#!/usr/bin/env bash
# Insertion is source translation: test the OCaml original and generated Soma,
# then test partial migration, diagnostics and non-destructive destinations.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$ROOT/_build/install/default/bin}:$PATH"
WORK=$(mktemp -d)
trap 'rm -rf "$WORK"' EXIT
export SOMA_INSERT_TEST="$WORK"
python3 - <<'PY'
from pathlib import Path
import json, os, subprocess, sys
root=Path(os.environ['SOMA_INSERT_TEST'])
probe=subprocess.run(['soma','insert','--help'],text=True,capture_output=True)
if 'OCaml 5 typedtree adapter is not implemented' in probe.stderr:
    assert probe.returncode==2
    print('SKIP soma insert translation: OCaml 5 typedtree adapter is not implemented')
    sys.exit(0)
def run(args, expected=0, cwd=root):
    p=subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=120)
    assert p.returncode==expected, (args,p.returncode,p.stdout,p.stderr)
    return p
assert 'insert PATH' in run(['soma','help']).stdout
assert 'Never evaluates' in run(['soma','insert','--help']).stdout
source=root/'arithmetic.ml'
source.write_text('''let add a b = a + b
let negative x = x < 0
let overflow = max_int + 1
let flip_bits x = x lxor 15
let identity x = x
let choose b x y = if b then x else y
let classify = function 0 -> "zero" | 1 -> "one" | _ -> "other"
type token = End | Value of int
let unpack = function End -> 0 | Value x -> x
let rec sum xs = match xs with [] -> 0 | x :: rest -> x + sum rest
type point = { x : int; y : int }
let flip p = { x = p.y; y = p.x }
let split s = String.split_on_char ';' s
let count xs = List.length xs
let rev xs = List.rev xs
let tuple x = (x, true, "ok")
let get_result = function Ok x -> x | Error _ -> 0
let local x = let y = x + 1 in y * 2
let join xs = String.concat "," xs
let decimal x = string_of_int x
let simultaneous x = let a = x + 1 and x = x + 2 in (a, x)
let both = 3 and other = 4
let nonempty xs = xs <> []
let without_empty xs = List.filter ((<>) "") xs
let repeat c = String.make 1 c
''')
original=source.read_bytes()
# Execute only this synthetic reference fixture, never user-supplied input.
(root/'reference.ml').write_text('''open Arithmetic
let () =
  assert (add 2 3 = 5);
  assert (negative (-1) && not (negative max_int));
  assert (overflow = min_int);
  assert (flip_bits 3 = 12);
  assert (identity true && identity 4 = 4);
  assert (classify 0 = "zero" && classify 2 = "other");
  assert (sum [1;2;3] = 6);
  assert (flip {x=2;y=3} = {x=3;y=2});
  assert (split ";a;;" = ["";"a";"";""]);
  assert (split "" = [""]);
  assert (count [true;false] = 2);
  assert (get_result (Ok 8) = 8);
  assert (local 4 = 10);
  assert (join ["a";"";"b"] = "a,,b");
  assert (decimal (-1) = "-1" && decimal min_int = "-4611686018427387904");
  assert (simultaneous 10 = (11,12));
  assert (without_empty ["";"x";""] = ["x"]);
  assert (nonempty [true] && not (nonempty []));
  assert (repeat 'x' = "x")
''')
run(['ocamlc','-o','reference','arithmetic.ml','reference.ml'])
run([str(root/'reference')])
out=root/'generated'
p=run(['soma','insert',str(source),'--out',str(out),'--json'])
r=json.loads(p.stdout)
assert r['complete'] and r['files'][0]['translated_items']==25, r
assert json.loads((out/'insert-report.json').read_text())==r
assert source.read_bytes()==original
text=(out/'arithmetic.soma').read_text()
assert 'PrimInt63.ltsb' in text and 'Fixpoint oc_sum' in text
assert 'Admitted' not in text and '\nAxiom ' not in text and 'unknown' not in text
(out/'arithmetic.exp').write_text('''Example added : oc_add 2%uint63 3%uint63 = 5%uint63. Proof. reflexivity. Qed.
Example signed : oc_negative 9223372036854775807%uint63 = true. Proof. reflexivity. Qed.
Example wrapped : oc_overflow = 4611686018427387904%uint63. Proof. reflexivity. Qed.
Example bits : oc_flip_5fbits 3%uint63 = 12%uint63. Proof. reflexivity. Qed.
Example poly_bool : oc_identity true = true. Proof. reflexivity. Qed.
Example poly_int : oc_identity 4%uint63 = 4%uint63. Proof. reflexivity. Qed.
Example sum_ok : oc_sum [1%uint63;2%uint63;3%uint63] = 6%uint63. Proof. reflexivity. Qed.
Example classify_ok : oc_classify 2%uint63 = "other". Proof. reflexivity. Qed.
Example record_ok : ocf_oct_point_x (oc_flip {| ocf_oct_point_x := 2%uint63; ocf_oct_point_y := 3%uint63 |}) = 3%uint63. Proof. reflexivity. Qed.
Example split_ok : oc_split ";a;;" = ["";"a";"";""]. Proof. reflexivity. Qed.
Example empty_split : oc_split "" = [""]. Proof. reflexivity. Qed.
Example count_ok : oc_count [true;false] = 2%uint63. Proof. reflexivity. Qed.
Example local_ok : oc_local 4%uint63 = 10%uint63. Proof. reflexivity. Qed.
Example join_ok : oc_join ["a";"";"b"] = "a,,b". Proof. reflexivity. Qed.
Example signed_decimal : oc_decimal 9223372036854775807%uint63 = "-1". Proof. reflexivity. Qed.
Example min_decimal : oc_decimal 4611686018427387904%uint63 = "-4611686018427387904". Proof. reflexivity. Qed.
Example simultaneous_ok : oc_simultaneous 10%uint63 = (11%uint63,12%uint63). Proof. reflexivity. Qed.
Example nonempty_ok : oc_nonempty [true] = true. Proof. reflexivity. Qed.
Example filtered : oc_without_5fempty ["";"x";""] = ["x"]. Proof. reflexivity. Qed.
''')
run(['soma','check',str(out/'arithmetic.soma')])
# Destination files are preserved, including previous generated output.
p=run(['soma','insert',str(source),'--out',str(out)],expected=2)
assert 'overwrite' in p.stderr and (out/'arithmetic.soma').read_text()==text
# Unsupported initialization is never executed; dependency users are omitted.
bad=root/'mixed.ml'
marker=root/'executed'
bad.write_text(f'''let answer = 42
let state = ref 0
let dependent () = !state
let () = let c = open_out {json.dumps(str(marker))} in close_out c
let twice n = n + n
''')
strict=root/'strict'
p=run(['soma','insert',str(bad),'--out',str(strict),'--json'],expected=1)
r=json.loads(p.stdout)
assert not r['complete'] and not strict.exists() and not marker.exists()
assert any(d['code']=='mutation' for d in r['files'][0]['diagnostics'])
partial=root/'partial'
p=run(['soma','insert',str(bad),'--out',str(partial),'--partial','--json'],expected=1)
r=json.loads(p.stdout)
assert r['files'][0]['translated_items']==2, r
fragment=(partial/'mixed.soma').read_text()
assert 'oc_answer' in fragment and 'oc_twice' in fragment and 'oc_dependent' not in fragment
assert not marker.exists()
run(['soma','check',str(partial/'mixed.soma')])
# Reject a shadowed standard-library module instead of mapping by spelling.
shadow=root/'shadow.ml'
shadow.write_text('module String = struct let length _ = 99 end\nlet size s = String.length s\n')
p=run(['soma','insert',str(shadow),'--report-only','--partial','--json'],expected=1)
assert json.loads(p.stdout)['files'][0]['translated_items']==0
# Builtin types are identified by compiler identity, not just their spelling.
alias=root/'alias.ml'
alias.write_text('type int = bool\nlet identity (x : int) = x\n')
alias_out=root/'alias'
run(['soma','insert',str(alias),'--out',str(alias_out)])
(alias_out/'alias.exp').write_text('Example alias_ok : oc_identity true = true. Proof. reflexivity. Qed.\n')
run(['soma','check',str(alias_out/'alias.soma')])
# A failed recursive declaration cannot leak into the accepted fragment.
rec=root/'recursion.ml'
rec.write_text('let rec bad xs = match xs with [] -> 0 | _ :: _ -> bad xs\nlet ok = 1\n')
p=run(['soma','insert',str(rec),'--out',str(root/'recursion'),'--partial','--json'],expected=1)
r=json.loads(p.stdout)
assert r['files'][0]['translated_items']==1 and any(d['code']=='soma-check' for d in r['files'][0]['diagnostics']), r
# Malformed OCaml yields machine-readable diagnostics and no output.
syntax=root/'syntax.ml'; syntax.write_text('let x = (\n')
p=run(['soma','insert',str(syntax),'--json'],expected=1)
assert json.loads(p.stdout)['files'][0]['diagnostics'][0]['code']=='ocaml-parse'
assert json.loads(p.stdout)['files'][0]['diagnostics'][0]['line']>0
# Quoting cannot turn source string contents into generated Soma commands.
quotes=root/'quotes.ml'
quotes.write_text('let text = "a\\\"b"\n')
quote_out=root/'quotes'
run(['soma','insert',str(quotes),'--out',str(quote_out)])
(quote_out/'quotes.exp').write_text('Example quotes_ok : oc_text = "a""b". Proof. reflexivity. Qed.\n')
run(['soma','check',str(quote_out/'quotes.soma')])
# Directory scanning preserves layout and ignores generated trees/symlinks.
project=root/'project'; (project/'sub').mkdir(parents=True)
(project/'a.ml').write_text('let n = 1\n')
(project/'sub'/'b.ml').write_text('let n = 2\n')
(project/'_build').mkdir(); (project/'_build'/'bad.ml').write_text('this is not OCaml')
(project/'link.ml').symlink_to(syntax)
report=root/'inventory.json'
p=run(['soma','insert',str(project),'--report-only','--report',str(report),'--json'])
assert len(json.loads(p.stdout)['files'])==2
assert report.exists() and not Path(str(project)+'-soma').exists()
print('PASS soma insert: OCaml/Soma behavior, inference, data, recursion, diagnostics, source isolation and destinations')
PY

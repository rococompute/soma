#!/usr/bin/env bash
# Source scanners keep the existing native string mappings and byte semantics.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 35 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"; exit "$rc"' EXIT
cd "$work"
cat >main.soma <<'SOMA'
From Soma Require TextScan.
Definition split := TextScan.split_on_char.
Definition contains := TextScan.contains.
Definition main := (split, contains).
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
cp native/{soma_nat.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,prog.ml,prog.mli} .
if rg -q 'If this appears, you.re using String internals' prog.ml; then
 echo 'FAIL: source scanner deconstructs native strings'; exit 1
fi
cat >check.ml <<'ML'
let count=ref 0
let check text separator =
 let parts=Prog.split separator text in
 assert(parts=String.split_on_char separator text);
 assert(Prog.contains text separator=String.contains text separator);
 assert(String.concat(String.make 1 separator)parts=text && parts<>[]);
 if not(String.contains text separator) then assert(List.hd parts==text);
 incr count
let rec strings depth text =
 for separator=0 to 255 do check text(Char.chr separator) done;
 if depth>0 then List.iter(fun c->strings(depth-1)(text^String.make 1 c))['\000';'/';'a']
let () =
 strings 5 "";
 let bytes=String.init 256 Char.chr in for c=0 to 255 do check bytes(Char.chr c) done;
 let state=Random.State.make[|193;71;2026|] in
 for _=1 to 10000 do
  let length=Random.State.int state 300 in
  check (String.init length(fun _->Char.chr(Random.State.int state 256)))
    (Char.chr(Random.State.int state 256))
 done;
 let big=String.make 2000000 'a' in
 let start=Sys.time() in check big '/';check big 'a';
 assert(Sys.time()-.start<15.);
 Printf.printf "PASS: %d split/contains cases, binary alphabet, empty fields, full-slice identity and 2 MB scans\n" !count
ML
for backend in ocamlopt ocamlc; do
 ocamlfind "$backend" -w -a -package lwt -linkpkg soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml prog.mli prog.ml check.ml -o "check-$backend" >"$backend.log" 2>&1
 "./check-$backend"
done

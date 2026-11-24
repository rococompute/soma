#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 60 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }
cat > "$work/storage.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native Algebraic graph := [
  data := ["Empty"; "Paired" Of [(PrimInt63.int * string)%type]; "Fields" Of [PrimInt63.int; string];
           "Inline" { mutable payload : string; owner : option node }];
  node := { mutable content : data; peers : Native.table string node }
] Exceptions ["Missing" Of [string]].
OCaml Native Get get_data : node -> data := "content".
OCaml Native Set set_data : node -> data -> unit := "content".
OCaml Native Build make : data -> Native.table string node -> node := "content" "peers".
OCaml Native Build make_lazily : (unit -> data) -> Native.table string node -> node :=
  "content" "peers" Evaluating "content".
OCaml Native Record Factory make_from_reference :
  Soma.Handles.reference data -> Native.table string node -> node :=
  "content" "peers" Reading "content".
OCaml Native Variant Dispatch project :
  forall (R : Type), (unit -> R) -> (data -> (PrimInt63.int * string) -> R) ->
    (PrimInt63.int -> string -> R) -> (string -> option node -> R) -> data -> R :=
  ["Empty" DiscardPayload; "Paired" KeepReceiver; "Fields"; "Inline" ReadFields ["payload"; "owner"]].
OCaml Native Constructor empty : unit -> data := "Empty" 0.
OCaml Native Constructor paired : (PrimInt63.int * string)%type -> data := "Paired" 1.
OCaml Native Constructor fields : PrimInt63.int -> string -> data := "Fields" 2.
OCaml Native Inline Build inline_value : string -> option node -> data := "Inline" "payload" "owner".
OCaml Native Inline Get inline_payload : data -> option string := "Inline" "payload".
OCaml Native Inline Set set_payload : data -> string -> bool := "Inline" "payload".
OCaml Native Constructor make_missing : string -> Soma.Handles.exception_value := "Missing" 1 In node.
OCaml Native Case read_missing : Soma.Handles.exception_value -> option string := "Missing" 1 In node.
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
Import storage.
Definition get node := Native.Export (Native.Call_callback get_data node).
Definition set node value := Native.Export (Native.Call_callback set_data (node,value)).
Definition create value peers := Native.Export (Native.Call_callback make (value,peers)).
Definition create_lazily value peers := Native.Export (Native.Call_callback make_lazily (value,peers)).
Definition create_from_reference := Native.Export (Native.Call_callback make_from_reference tt).
Definition dispatch := Native.Export (Native.Call_callback (project string) tt).
Definition make_empty (_ : unit) := Native.Export (Native.Call_callback empty tt).
Definition make_pair pair := Native.Export (Native.Call_callback paired pair).
Definition make_fields count message := Native.Export (Native.Call_callback fields (count,message)).
Definition make_inline message owner := Native.Export (Native.Call_callback inline_value (message,owner)).
Definition read_inline owner := Native.Export (Native.Call_callback inline_payload owner).
Definition write_inline owner message := Native.Export (Native.Call_callback set_payload (owner,message)).
Definition missing message := Native.Export (Native.Call_callback make_missing message).
Definition missing_message error := Native.Export (Native.Call_callback read_missing error).
Definition main := (get,set,create,create_lazily,create_from_reference,dispatch,make_empty,make_pair,make_fields,
  make_inline,read_inline,write_inline,missing,missing_message).
SOMA
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1
python3 - "$work/native" <<'PY'
import hashlib
import shlex
import sys
from pathlib import Path

out = Path(sys.argv[1])
version, line = (out/'native_algebraic.manifest').read_text().splitlines()
assert version == 'soma-native-algebraic-v1'
symbol, source, source_hash, module, product_hash = shlex.split(line)
assert symbol == 'storage.data'
assert source == 'storage.definition'
assert hashlib.sha256((out.parent/source).read_bytes()).hexdigest() == source_hash
assert hashlib.sha256((out/module).read_bytes()).hexdigest() == product_hash
probe = 'module Storage = '+ Path(module).stem.capitalize()[0] + Path(module).stem[1:] + '''
let check label actual = if not actual then failwith label
let () =
  let text = Bytes.to_string (Bytes.make 2048 'x') in
  let pair = (92,text) in
  let error = Prog.missing text in
  check "owned exception is throwable and borrows its payload"
    (match error with Storage.Missing payload -> payload == text | _ -> false);
  check "owned exception case reads the borrowed payload"
    (match Prog.missing_message error with Some payload -> payload == text | _ -> false);
  check "unrelated exception has no payload" (Prog.missing_message Exit = None);
  let peers = Hashtbl.create 1 in
  let evaluations = ref 0 in
  let deferred = Prog.create_lazily (fun () -> incr evaluations;Storage.Paired pair) peers in
  check "evaluate exactly once while building" (!evaluations = 1);
  check "evaluate leaves borrowed field and peers" (deferred.Storage.peers == peers &&
    match Prog.get deferred with Storage.Paired stored -> stored == pair | _ -> false);
  let live_content = ref Storage.Empty in
  let factory = Prog.create_from_reference live_content in
  live_content := Storage.Paired pair;
  let borrowed = factory peers in
  check "factory reads a live reference at full application"
    (borrowed.Storage.peers == peers &&
     match Prog.get borrowed with Storage.Paired stored -> stored == pair | _ -> false);
  let node = Prog.create (Prog.make_empty ()) peers in
  Hashtbl.add peers "root" node;
  check "native table alias and nullary tag" (node.Storage.peers == peers && Prog.get node == Storage.Empty);
  Prog.set node (Prog.make_pair pair);
  check "single boxed pair" (match node.content with Storage.Paired stored -> stored == pair | _ -> false);
  Prog.set node (Prog.make_fields 92 text);
  check "two fields" (match node.content with Storage.Fields(92,value) -> value == text | _ -> false);
  check "wrong constructor get" (Prog.read_inline (Prog.make_empty ()) = None);
  check "wrong constructor set" (not (Prog.write_inline (Prog.make_empty ()) text));
  let observed_pair = ref None in
  let paired = Storage.Paired pair in
  let print = Prog.dispatch
      (fun () -> "empty")
      (fun source ((_, value) as pair) ->
        check "dispatch keeps the original receiver on request" (source == paired);
        observed_pair := Some pair; value)
      (fun count value -> check "direct constructor count" (count = 92); value)
      (fun value owner ->
        check "dispatch borrows the recursive receiver's field" (Option.get owner == node);
        value) in
  check "dispatch a nullary constructor" (print Storage.Empty = "empty");
  check "dispatch preserves the borrowed tuple and text"
    (print paired == text && Option.get !observed_pair == pair);
  check "dispatch separates the raw constructor payloads"
    (print (Storage.Fields (92,text)) == text);
  let inline = Prog.make_inline text (Some node) in
  check "dispatch borrows an inline record field" (print inline == text);
  Prog.set node inline;
  (match Prog.get node with
   | Storage.Inline record ->
       check "inline record block" (Prog.get node == inline && record.payload == text);
       check "recursive node identity" (match record.owner with Some owner -> owner == node | _ -> false);
       check "selected field remains borrowed" (match Prog.read_inline inline with Some value -> value == text | _ -> false);
       check "inline setter used original block" (Prog.write_inline inline "changed")
   | _ -> failwith "missing inline constructor");
  check "inline mutation" (match inline with Storage.Inline record -> record.payload = "changed" | _ -> false);
  print_endline "PASS: native algebraic group retains mutable fields, inline blocks, boxed tuples and recursive aliases"
'''
(out/'probe.ml').write_text(probe)
modules = sorted(p.stem for p in out.glob('*.ml') if p.stem != 'soma_main')
(out/'dune').write_text('(executable (name probe) (modes exe byte) (modules '+
    ' '.join(modules)+') (libraries lwt) (flags (:standard -w -a)))\n')
PY
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

cp "$work/storage.definition" "$work/storage.original"
negative() {
  local name=$1 replacement=$2 expected=$3
  sed "s/$replacement/" "$work/storage.original" > "$work/storage.definition"
  if "$SOMA" extract "$work/main.soma" -o "$work/$name" > "$work/$name.log" 2>&1; then
    echo "accepted malformed algebraic group $name" >&2
    return 1
  fi
  grep -q "$expected" "$work/$name.log"
}
negative duplicate 'peers : Native.table string node/content : data' 'record field names must be distinct'
negative badtag '"Paired"/"Bad.Name"' 'constructor is a single name'
negative field 'mutable payload : string/mutable payload : forall (A : Type), A -> A' 'must be monomorphic'
negative unknown_exception '"Missing" 1 In node/"Unlisted" 1 In node' 'does not declare this exception'
negative unknown_evaluated 'Evaluating "content"/Evaluating "absent"' 'evaluated field must be part'
negative dispatch_duplicate '"Paired" KeepReceiver; "Fields"; "Inline" ReadFields/"Paired" KeepReceiver; "Paired"; "Inline" ReadFields' 'variant dispatch must cover every constructor once'
negative dispatch_unknown_field 'ReadFields \["payload"; "owner"\]/ReadFields ["absent"; "owner"]' 'variant dispatch field is absent'
negative dispatch_wrong_handler '(string -> option node -> R) -> data -> R/(bool -> option node -> R) -> data -> R' 'variant dispatch handler disagrees'
negative unknown_reference 'Reading "content"/Reading "absent"' 'a reference read must name a factory record field'
negative non_reference 'Soma.Handles.reference data -> Native.table string node/data -> Native.table string node' 'a record factory read needs a reference argument'
negative non_thunk 'make_lazily : (unit -> data)/make_lazily : data' 'evaluated field needs a unit thunk'
negative return_option 'inline_payload : data -> option string/inline_payload : data -> string' 'Inline Get result must be option'
negative return_bool 'set_payload : data -> string -> bool/set_payload : data -> string -> unit' 'Inline Set result must be bool'
negative repeated_inline '"Inline" "payload" "owner"/"Inline" "payload" "payload"' 'inline record fields must be distinct'
echo 'PASS: malformed algebraic groups and inline record bindings rejected'

cp "$work/storage.original" "$work/storage.definition"
printf '%s\n' 'Definition main := true.' > "$work/main.soma"
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/reextract.log" 2>&1
test ! -e "$work/native/native_algebraic.manifest"
test -z "$(find "$work/native" -maxdepth 1 -name 'soma_algebraic_*.ml' -print)"
test -f "$work/native/probe.ml"
echo 'PASS: obsolete algebraic products reclaimed while the host probe stays in place'

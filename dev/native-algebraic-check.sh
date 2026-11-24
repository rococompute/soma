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
].
OCaml Native Get get_data : node -> data := "content".
OCaml Native Set set_data : node -> data -> unit := "content".
OCaml Native Build make : data -> Native.table string node -> node := "content" "peers".
OCaml Native Constructor empty : unit -> data := "Empty" 0.
OCaml Native Constructor paired : (PrimInt63.int * string)%type -> data := "Paired" 1.
OCaml Native Constructor fields : PrimInt63.int -> string -> data := "Fields" 2.
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
Import storage.
Definition get node := Native.Export (Native.Call_callback get_data node).
Definition set node value := Native.Export (Native.Call_callback set_data (node,value)).
Definition create value peers := Native.Export (Native.Call_callback make (value,peers)).
Definition make_empty (_ : unit) := Native.Export (Native.Call_callback empty tt).
Definition make_pair pair := Native.Export (Native.Call_callback paired pair).
Definition make_fields count message := Native.Export (Native.Call_callback fields (count,message)).
Definition main := (get,set,create,make_empty,make_pair,make_fields).
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
  let peers = Hashtbl.create 1 in
  let node = Prog.create (Prog.make_empty ()) peers in
  Hashtbl.add peers "root" node;
  check "native table alias and nullary tag" (node.Storage.peers == peers && Prog.get node == Storage.Empty);
  Prog.set node (Prog.make_pair pair);
  check "single boxed pair" (match node.content with Storage.Paired stored -> stored == pair | _ -> false);
  Prog.set node (Prog.make_fields 92 text);
  check "two fields" (match node.content with Storage.Fields(92,value) -> value == text | _ -> false);
  let inline = Storage.Inline { payload=text; owner=Some node } in
  Prog.set node inline;
  (match Prog.get node with
   | Storage.Inline record ->
       check "inline record block" (Prog.get node == inline && record.payload == text);
       check "recursive node identity" (match record.owner with Some owner -> owner == node | _ -> false);
       record.payload <- "changed"
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
echo 'PASS: duplicate fields, qualified constructors and higher-ranked fields rejected'

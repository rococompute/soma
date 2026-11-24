#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
SOMA=${SOMA:-$root/_build/install/default/bin/soma}
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" != 0 ]; then tail -n 60 "$work"/*.log || true; fi; rm -rf "$work"' EXIT
host() { opam exec --switch="${SOMA_NATIVE_TEST_SWITCH:-kykeon}" -- "$@"; }

cat > "$work/literals.definition" <<'SOMA'
From Soma Require Native.
From Corelib Require Import PrimInt63.
From Stdlib Require Import Strings.String.
OCaml Native External Callback scan :
  string -> (PrimInt63.int -> PrimInt63.int -> PrimInt63.int) -> PrimInt63.int :=
  "Fixture.scan" With "%d %d" After 1.
OCaml Native External Callback prefix : string -> string -> string :=
  "Fixture.order" With "literal" After 0.
OCaml Native External Callback suffix : forall (first : string), string -> string :=
  "Fixture.labelled" With "literal" After 2.
SOMA
cat > "$work/main.soma" <<'SOMA'
From Soma Require Native.
Import literals.
Definition main := (scan, (prefix, suffix)).
SOMA
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/extract.log" 2>&1
grep -q 'external-literal-call .* after 1' "$work/native/native_abi.manifest"

cat > "$work/native/fixture.ml" <<'ML'
let callback = ref None
let text = ref None
let format = ref None
let key : int Lwt.key = Lwt.new_key ()
let context = ref None
let scan value fmt (body : int -> int -> int) =
  text := Some value;
  format := Some (Obj.repr fmt);
  callback := Some body;
  context := Lwt.get key;
  Scanf.sscanf value fmt body

let order first second last = String.concat "/" [first;second;last]
let labelled ~first second last = order first second last
ML
cat > "$work/native/probe.ml" <<'ML'
let check label ok = if not ok then failwith label

let () =
  let scan,(prefix,suffix) = Prog.soma_main () in
  let text = Bytes.to_string (Bytes.of_string "12 34") in
  let error = Failure (String.make 31 'x') in
  let callback x y = check "callback context" (Lwt.get Fixture.key = Some 7); x - y in
  let result = Lwt.with_value Fixture.key (Some 7) (fun () -> scan (text,callback)) in
  check "typed scanf result" (result = -22);
  check "caller input borrowed" (Option.get !(Fixture.text) == text);
  check "exact unwrapped callback" (Option.get !(Fixture.callback) == callback);
  check "raw provider context" (!(Fixture.context) = Some 7);
  let format = Option.get !(Fixture.format) in
  (match scan (text, fun _ _ -> raise error) with
   | exception got when got == error -> ()
   | _ -> failwith "raw callback exception identity");
  check "shared typed format" (Option.get !(Fixture.format) == format);
  check "first constant slot" (prefix ("one","two") = "literal/one/two");
  check "last constant slot and labels" (suffix ("one","two") = "one/two/literal");
  print_endline "PASS: typed later literals preserve raw scanf callback, format, context and exception identities"
ML

configure_probe() {
  python3 - "$work/native" <<'PY'
from pathlib import Path
import sys

root = Path(sys.argv[1])
assert 'Obj.' not in (root / 'soma_bindings.ml').read_text()
modules = sorted(path.stem for path in root.glob('*.ml') if path.stem != 'soma_main')
(root / 'dune').write_text(
    '(executable (name probe) (modes exe byte) (modules ' + ' '.join(modules)
    + ') (libraries lwt) (flags (:standard -w -a)))\n'
)
PY
}
configure_probe
(cd "$work/native" && host dune build --profile release -j2 probe.exe probe.bc) > "$work/build.log" 2>&1
"$work/native/_build/default/probe.exe"
host ocamlrun "$work/native/_build/default/probe.bc"

cp "$work/literals.definition" "$work/original.definition"
for position in -1 3; do
  sed "s/After 1/After $position/" "$work/original.definition" > "$work/literals.definition"
  if "$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/position-$position.log" 2>&1; then
    echo "accepted invalid literal position $position" >&2
    exit 1
  fi
done
grep -q 'literal insertion position' "$work/position-3.log"
sed 's/With "%d %d"/With "%d %s"/' "$work/original.definition" > "$work/literals.definition"
"$SOMA" extract "$work/main.soma" -o "$work/native" > "$work/bad-extract.log" 2>&1
configure_probe
if (cd "$work/native" && host dune build --profile release -j2) > "$work/bad-build.log" 2>&1; then
  echo "accepted a format with the wrong callback type" >&2
  exit 1
fi
grep -q 'soma_bindings.ml' "$work/bad-build.log"
grep -q 'string' "$work/bad-build.log"
echo 'PASS: invalid positions and incompatible native scanner callback types rejected'

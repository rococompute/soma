#!/usr/bin/env bash
# The actual generated Mirage adapter calls extracted Wire definitions.
# Exercise that adapter against binary frames, boundaries and trailing data.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache" SOMA_MIRAGE_DIR="$WORK/mirage"
unset SOMA_MIRAGE_SWITCH SOMA_MIRAGE_BUILD SOMA_MIRAGE_NO_IMAGE
cd "$WORK"
printf 'Require Import Sandbox.\nmain : io unit := print "wire".\n' > main.soma
soma build --no-image main.soma > build.log 2>&1 || { cat build.log; exit 1; }
project="$SOMA_MIRAGE_DIR/plain"
cp "$project"/{prog.ml,prog.mli,uint63.ml,float64.ml} .
# Use the generated adapter verbatim; exclude its networking interpreter.
sed -n '/^let take_line = Prog.soma_wire_take_line/,/^(\* What the network provides/p' "$project/soma_rt.ml" | sed '$d' > adapter.ml
cat > check.ml <<'OCAML'
let frame s =
  let n = String.length s in
  String.init 4 (fun i -> Char.chr ((n lsr (8 * (3-i))) land 255)) ^ s
let expect n s = match Adapter.take_frame s with
  | `Whole (data, rest) -> assert (String.length data = n && rest = "tail")
  | _ -> assert false
let () =
  let random = Random.State.make [|731|] in
  List.iter (fun n ->
    let s = String.init n (fun _ -> Char.chr (Random.State.int random 256)) in
    let encoded = frame s in
    expect n (encoded ^ "tail");
    if n > 0 then assert (Adapter.take_frame (String.sub encoded 0 (String.length encoded-1)) = `Need_more)
  ) [0; 1; 2; 255; 256; 65535; 65536; 1048576];
  for n = 0 to 3 do assert (Adapter.take_frame (String.make n '\000') = `Need_more) done;
  assert (Adapter.take_frame "\000\016\000\001" = `Oversized);
  assert (Adapter.take_frame "\255\255\255\255" = `Oversized);
  for byte = 0 to 255 do
    let s = String.make 1 (Char.chr byte) in
    if byte <> 10 then assert (Adapter.take_line (s ^ "\r\ntail") = Some (s, "tail"))
  done;
  assert (Adapter.take_line "\ntail" = Some ("", "tail"));
  assert (Adapter.take_line "unfinished" = None);
  print_endline "PASS generated Mirage adapter uses proved Wire decoders at byte and frame boundaries"
OCAML
ocamlc -w -a -c uint63.ml float64.ml prog.mli prog.ml adapter.ml check.ml > compile.log 2>&1
ocamlc -o check uint63.cmo float64.cmo prog.cmo adapter.cmo check.cmo
./check

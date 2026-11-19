#!/usr/bin/env bash
# Runtime-level E8: malformed index arity must produce a gradual error, not an
# OCaml bounds exception. The helper is the actual runtime embedded by extraction.
set -euo pipefail
export PATH="$BIN:$PATH"
SOURCE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cp "$SOURCE_ROOT/plugins/extraction/gradual_rt.ml" "$TMP/gradual_rt.ml"
cat > "$TMP/check.ml" <<'ML'
open Gradual_rt
let value = Obj.repr 7
let target data args = { name = "IndexTest"; data; args = Array.of_list args }
let checked_error thunk =
  try ignore (check (thunk ())); failwith "a bad index arity was accepted"
  with Cast_error _ -> ()
let () =
  let i = Val (Obj.repr 1) in
  let one = target false [i] in
  assert (check_indices one 0 [i] value == value);
  assert (check_indices one 0 [Unk] value == value);
  List.iter (fun (nparams, computed) ->
      checked_error (fun () -> check_indices one nparams computed value))
    [0, []; 0, [i; i]; -1, [i]; 2, []];
  let data = target true [i] in
  let failed = check_indices data 0 [i; i] value in
  assert (is_error failed);
  checked_error (fun () -> failed);
  let with_parameter = target false [Ty Erased; i] in
  assert (check_indices with_parameter 1 [i] value == value);
  print_endline "gradual index arity uses gradual errors, valid indices are preserved: ok"
ML
cd "$TMP"
ocamlc -w -a gradual_rt.ml check.ml -o check.exe
./check.exe

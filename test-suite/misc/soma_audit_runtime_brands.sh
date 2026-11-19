#!/usr/bin/env bash
# Actual runtime: names are diagnostics; exported physical brands determine
# semantic identity across module aliases and generative functor applications.
set -euo pipefail
export PATH="$BIN:$PATH"
SOURCE_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cp "$SOURCE_ROOT/plugins/extraction/gradual_rt.ml" "$TMP/gradual_rt.ml"
cat > "$TMP/check.ml" <<'ML'
open Gradual_rt
module Make () = struct let brand = object end end
module N = Make ()
module N2 = Make ()
module Alias = N
let ty name brand args = branded_ind name brand "variant" false args
let () =
  let n = ty "Make.box" N.brand [] in
  let alias = ty "Alias.box" Alias.brand [] in
  let n2 = ty "Make.box" N2.brand [] in
  assert (equal n alias);
  assert (not (equal n n2));
  let v = Obj.repr 7 in
  assert (cast n alias v == v);
  (try ignore (cast n n2 v); failwith "different applications were accepted"
   with Cast_error _ -> ());
  let calls_n = ref 0 and calls_n2 = ref 0 in
  let fn count _ _ value = incr count; value in
  let fs = branded_rcons "Make.box" N.brand "variant" (fn calls_n)
      (branded_rcons "Make.box" N2.brand "variant" (fn calls_n2) rnil) in
  let from brand = ty "Make.box" brand [Ty Unknown] in
  let into brand = ty "Outside.box" brand [Ty (Sort 1)] in
  ignore (cast_with fs (from N.brand) (into Alias.brand) v);
  ignore (cast_with fs (from N2.brand) (into N2.brand) v);
  assert (!calls_n = 1 && !calls_n2 = 1);
  (try ignore (cast n (branded_ind "Make.box" N.brand "native-int" false []) v);
       failwith "incompatible extraction representation was trusted"
   with Cast_error _ -> ());
  (try ignore (cast (ind "Make.box" false []) n v);
       failwith "unbranded legacy value was trusted as branded"
   with Cast_error _ -> ());
  print_endline "application brands, aliases, distinct constructor registries and mixed ABI refusal: ok"
ML
cd "$TMP"
ocamlc -w -a gradual_rt.ml check.ml -o check.exe
./check.exe

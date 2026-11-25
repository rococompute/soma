#!/usr/bin/env bash
# Share a checked nullary sum with an existing native variant, without conversion.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
export PATH="${BIN:-$root/_build/install/default/bin}:$PATH"
work=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then tail -n 50 "$work"/*.log 2>/dev/null || true; fi; rm -rf "$work"' EXIT
cd "$work"
cat > producer.soma <<'SOMA'
Inductive color := Red | Green | Blue.
Inductive payload := Payload (value : nat).
Inductive parameterized (A : Type) := Parameterized.
Inductive indexed : nat -> Type := Indexed : indexed O.
Inductive evidence : Prop := Evidence.
Definition main := Red.
SOMA
cat > target.definition <<'SOMA'
From Soma Require Import Native.
Import producer.
OCaml Native Enum color := producer.color As "Target.color".
Fail OCaml Native Enum conflicting := producer.color As "Other.color".
Fail OCaml Native Enum with_payload := producer.payload As "Target.payload".
Fail OCaml Native Enum with_parameter := producer.parameterized As "Target.parameterized".
Fail OCaml Native Enum with_index := producer.indexed As "Target.indexed".
Fail OCaml Native Enum with_proof := producer.evidence As "Target.evidence".
Fail OCaml Native Enum injected := producer.color As "Target.color; assert false".
SOMA
printf 'type color = Red | Green | Blue\n' >target.ml
cat > main.soma <<'SOMA'
Import target.
Definition rotate (value : color) : color :=
  match value with producer.Red => producer.Green | producer.Green => producer.Blue | producer.Blue => producer.Red end.
Definition main := rotate.
SOMA
soma extract main.soma -no-soma-prelude -o native >extract.log 2>&1
soma hash main.soma -no-soma-prelude >hash.log
if grep -q '  assumes ' hash.log; then echo 'enum reuse introduced assumptions' >&2; exit 1; fi
(cd native && dune build --profile release -j2) >build.log 2>&1
cp native/soma_enum_*.ml .
cp native/{target.ml,prog.ml,prog.mli,soma_bindings.ml,soma_effect.ml,soma_handles.ml,uint63.ml,soma_word64.ml,float64.ml,soma_nat.ml} .
cat > check.ml <<'OCAML'
let () =
  assert (Prog.rotate Target.Red = Target.Green);
  assert (Prog.rotate Target.Green = Target.Blue);
  assert (Prog.rotate Target.Blue = Target.Red);
  Gc.full_major ();
  let before = Gc.allocated_bytes () in
  for _ = 1 to 100000 do ignore (Prog.rotate Target.Red) done;
  assert (Gc.allocated_bytes () -. before < 1024.);
  print_endline "PASS: checked/native enum identity, exhaustive matching and allocation-free shared values."
OCAML
for compiler in ocamlc ocamlopt; do
  ocamlfind "$compiler" -package lwt -linkpkg -w -a -o "check-$compiler" \
    soma_nat.ml soma_effect.ml soma_handles.ml uint63.ml soma_word64.ml float64.ml \
    target.ml soma_enum_*.ml soma_bindings.ml prog.mli prog.ml check.ml
  "./check-$compiler"
done
# Discover the mapping through the logical inductive even when the alias
# constant is absent from the main definition's type and body.
cat > bare.soma <<'SOMA'
Import target.
Definition rotate (value : producer.color) : producer.color :=
  match value with producer.Red => producer.Blue | producer.Green => producer.Red | producer.Blue => producer.Green end.
Definition main := rotate.
SOMA
soma extract bare.soma -no-soma-prelude -o bare >bare.log 2>&1
(cd bare && dune build --profile release -j2) >>bare.log 2>&1
grep -q 'Soma_enum_' bare/prog.mli
grep -q 'type t = Target.color' bare/soma_enum_*.ml
# Even an identity client must reject extra native cases and payload changes.
cat > identity.soma <<'SOMA'
Import target.
Definition main (value : color) : color := value.
SOMA
printf 'type color = Red | Green | Blue | Extra\n' >target.ml
soma extract identity.soma -no-soma-prelude -o extra >extra.log 2>&1
if (cd extra && dune build --profile release -j2) >>extra.log 2>&1; then
  echo 'accepted a non-exhaustive native enum ABI' >&2; exit 1
fi
grep -Eq 'does not match|constructor.*Extra|Extra.*constructor' extra.log
printf 'type color = Red of int | Green | Blue\n' >target.ml
soma extract identity.soma -no-soma-prelude -o payload >payload.log 2>&1
if (cd payload && dune build --profile release -j2) >>payload.log 2>&1; then
  echo 'accepted a payload-bearing native enum constructor' >&2; exit 1
fi
grep -Eq 'expects|argument|constructor|arities' payload.log

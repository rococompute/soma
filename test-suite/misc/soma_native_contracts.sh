#!/usr/bin/env bash
# Check the real native extraction mappings at integer and byte boundaries.
# NativeSpec.v proves the signed-word refinement under explicit bounds;
# this test checks that the backend's realizers agree with that contract.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache"
cd "$WORK"
cat > driver.definition <<'SOMA'
check : (nat -> nat -> nat) -> (nat -> nat -> nat) ->
  (nat -> nat -> nat) -> (nat -> nat -> nat) -> (nat -> nat -> nat) ->
  (nat -> string -> option nat) ->
  (nat -> nat -> string -> string) -> (string -> string -> nat) -> string.
SOMA
cat > driver.ml <<'OCAML'
let check add mul sub div modulo get substring order =
  let cases = [0; 1; 2; 255; 256; 65535; 1048576; max_int / 2; max_int - 1; max_int] in
  List.iter (fun a -> List.iter (fun b ->
    if a <= max_int - b then
      assert (add a b = Int64.to_int (Int64.add (Int64.of_int a) (Int64.of_int b)));
    if b = 0 || a <= max_int / b then
      assert (mul a b = Int64.to_int (Int64.mul (Int64.of_int a) (Int64.of_int b)));
    assert (sub a b = (if a < b then 0 else a - b));
    assert (div a b = (if b = 0 then 0 else a / b));
    assert (modulo a b = (if b = 0 then a else a mod b))
  ) cases) cases;
  (* A deliberate counterexample to UNCONDITIONAL nat/int equivalence.
     Keep the negative result inside OCaml, outside any extracted nat match. *)
  assert (add max_int 1 = min_int);
  assert (mul max_int 2 = -2);
  let bytes = String.init 256 Char.chr in
  let strings = [""; "a"; "a\000"; "a\255"; "\128"; bytes] in
  let rec lex a b i =
    if i = String.length a then (if i = String.length b then 0 else 1)
    else if i = String.length b then 2
    else if Char.code a.[i] < Char.code b.[i] then 1
    else if Char.code b.[i] < Char.code a.[i] then 2
    else lex a b (i+1) in
  List.iter (fun s ->
    List.iter (fun n ->
      assert (get n s = if n < String.length s then Some (Char.code s.[n]) else None);
      List.iter (fun m ->
        let expected = List.init (min m (max 0 (String.length s - n)))
          (fun i -> s.[n+i]) |> List.to_seq |> String.of_seq in
        assert (substring n m s = expected)
      ) [0; 1; 255; 256; max_int]
    ) [0; 1; 255; 256; 257; max_int];
    List.iter (fun t -> assert (order s t = lex s t 0)) strings
  ) strings;
  "PASS bounded native arithmetic, explicit overflow counterexamples, and byte-string mappings"
OCAML
cat > main.soma <<'SOMA'
Import driver.
main := check Nat.add Nat.mul Nat.sub Nat.div Nat.modulo
  (fun n s => option_map Ascii.nat_of_ascii (String.get n s)) String.substring
  (fun a b => match String.compare a b with Eq => 0 | Lt => 1 | Gt => 2 end).
SOMA
soma run main.soma > run.log 2>&1 || { cat run.log; exit 1; }
cat run.log
grep -q '^PASS bounded native arithmetic' run.log

#!/usr/bin/env bash
# Exercise extracted casts for the type shapes and tag-dependent laws
# checked by CastSpec.v. Error kinds are checked, not arbitrary exceptions.
set -euo pipefail
export PATH="$BIN:$PATH"
WORK=$(mktemp -d)
trap 'rc=$?; if [ "$rc" -ne 0 ]; then cat "$WORK"/*.log >&2 || true; fi; rm -rf "$WORK"' EXIT
export XDG_CACHE_HOME="$WORK/cache"
cd "$WORK"
cat > driver.definition <<'SOMA'
check : (nat -> nat) -> (bool -> bool) -> (list nat -> list nat) ->
  (list (option (nat * string)) -> list (option (nat * string))) ->
  (nat -> nat) -> (nat -> nat) -> (nat -> bool) ->
  (unit -> nat) -> (unit -> nat) -> string.
SOMA
cat > driver.ml <<'OCAML'
let contains text word =
  let rec at i = i + String.length word <= String.length text &&
    (String.sub text i (String.length word) = word || at (i+1)) in at 0
let error kind f =
  match f () with
  | _ -> failwith ("expected " ^ kind)
  | exception e -> assert (contains (Printexc.exn_slot_name e) kind)
let check nat_rt bool_rt list_rt nested_rt function_rt unpack_nat unpack_bool unknown failed =
  List.iter (fun n -> assert (nat_rt n = n)) [0;1;2;255;65536;max_int];
  assert (bool_rt true && not (bool_rt false));
  let values = [0;1;31;255;65536;max_int] in
  assert (list_rt values = values);
  let nested = [None;Some (0, "");Some (max_int,"binary\000\255")] in
  assert (nested_rt nested = nested);
  for n = 0 to 2047 do
    assert (function_rt n = n + 3);
    if n mod 2 = 0 then begin
      assert (unpack_nat n = n); error "Cast_error" (fun () -> unpack_bool n)
    end else begin
      error "Cast_error" (fun () -> unpack_nat n); assert (unpack_bool n)
    end
  done;
  error "Unknown_term" unknown;
  error "Cast_error" failed;
  "PASS extracted cast round trips, higher-order wrappers, changing dynamic tags and precise failure kinds"
OCAML
cat > main.soma <<'SOMA'
Require Import Soma.CastSpec.
Import driver.
main := check
  (fun n : nat => cast Any nat (cast nat Any n))
  (fun b : bool => cast Any bool (cast bool Any b))
  (fun xs : list nat => cast Any (list nat) (cast (list nat) Any xs))
  (fun xs : list (option (nat * string)) =>
    cast Any (list (option (nat * string))) (cast (list (option (nat * string))) Any xs))
  (fun n : nat => cast Any (nat -> nat) (cast (nat -> nat) Any (fun x => x + 3)) n)
  unpack_nat unpack_bool
  (fun _ : unit => cast Any nat (unknown Any))
  (fun _ : unit => cast Any nat (err Any)).
SOMA
soma run main.soma > run.log 2>&1 || { cat run.log; exit 1; }
cat run.log
grep -q '^PASS extracted cast round trips' run.log

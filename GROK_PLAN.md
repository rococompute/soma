# Plan

As of `566c2b57a8` on branch `gradual` (Rocq 9.3.0). This replaces
`GROK_FOLLOWUP.md` as the work list. That file is the list as of
`75f40c8e88`; it is committed so the text stays in history if the file
is removed. The items it named have landed, including extraction of
`?` and `err` as values, `: Dyn` parameter defaulting, primitive
casts, `rocqchk -gradual-steps`, the recorded test-suite run, and the
summary cache.

`GRADUAL.md` is the spec. Do not start from the follow-up.

## Leave these alone

The encoding is the right cut. Do not reopen it.

- No cast term former. The kernel stays CIC. Rules live in reduction of the three retroknowledge axioms (`kernel/gradual.ml`).
- Do not implement the rules in the VM or the native compiler. Under Gradual Typing, `vm_compute`, `native_compute`, and `Compute` fall back to `cbv` (`tactics/redexpr.ml`).
- Do not rebuild the paper's germs. Germ-free injection keeps the original head. Change that only for a concrete observational counterexample.
- Do not add `Dyn@{i}`. One universe `gradual` still casts `list Type` and a universe-polymorphic record. A type above it already gets `Above_gradual` (`Set : Dyn`).
- Do not mechanize graduality or conservativity in this repo.
- Do not delete `Evar _, _ | _, Evar _ -> true` in `consistent` (`pretyping/gradualTyping.ml`). `unify_consistent` solves the positions that agree. The clause stayed after a search that found no bad elaboration. Delete it only for a term that shows a cast where the evar should have waited.
- Do not drop `leading_types` in `pretyping/pretyping.ml`. Delaying every argument broke `@Some Dyn false : option bool`.
- SProp stays out. The axioms quantify over `Type`.
- Haskell and Scheme stay an error (`MLraw`).
- Do not box types mapped by `Extract Inductive` (`bool => bool`, `nat => int`) so that `t_pair_bad` can be `(raise, raise)`. That changes the extracted ABI. The difference stays documented.
- Coinductive casts stay unsupported, for the reason in `GRADUAL.md`: the kernel would rebuild one constructor of a `cofix` without unfolding it again, and the runtime would have to keep that value lazy.
- The proof warning's two holes stay as the commit describes them. `check_gradual_proof` (`vernac/declare.ml`) does not force an asynchronous proof. `proof_uses_gradual` follows transparent bodies only.

## 1. Correct the stale comment

`pretyping/pretyping.ml`, in `pretype_app`, still says that
`cons 1 (cons true nil) : Dyn` fails. It succeeds.
`default_params_to_unknown` sets undetermined inductive parameters to
`Dyn`, and `GRADUAL.md` records that. Rewrite those sentences to say
so. No behavior change. The existing success and output tests are the
check.

## 2. Propagate `?` and `err` through an extracted match

This is the remaining gap between what Rocq computes and what the
extracted program computes.

The kernel rule (`GRADUAL.md`, reduction table) is: matching on
`unknown` or `err` at an inductive type yields `unknown` or `err` at
the match's return type. `Goal t_unk_elim tt = unk` in
`test-suite/misc/gradual_extraction/gradual_prog.v` is that rule for
`unk + 2`.

Extraction does not do this. `gradual_guard_cases` in
`plugins/extraction/extract_env.ml` wraps every non-custom match with
`Gradual_rt.check`, and `check` raises `Unknown_term` or `Cast_error`.
`main.ml` then treats that exception as the same result whenever the
kernel print is exactly `unk`:

```ocaml
| Unk m ->
  "unk (" ^ m ^ ")",
  if kernel = "unk" then `Same else ...
```

`t_unk_elim` prints `unk (Corelib.Init.Datatypes.nat)` and is counted
as agreement. The values are not the same. `2 + unk` agrees only
because `add` matches on its first argument, so the `unk` sits under
`S` and is never matched (`t_unk_plus`).

`MLcase`'s `ml_type` is the type of the scrutinee
(`plugins/extraction/miniml.mli`), not the return type. The return
type is `mlt` at the match in `plugins/extraction/extraction.ml`
(the standard case that builds `MLcase`, just after `extract_branch`).
Build the propagation there.

Add `Gradual_rt.eliminate` in `plugins/extraction/gradual_rt.ml`:

```ocaml
(* [eliminate ty v k] is [k v], unless [v] is [?] or [err].
   Then it is [?] or [err] at [ty], which raises when [ty] cannot
   hold that value (mapped, primitive, singleton, coinductive). *)
let eliminate (ty : ty) (v : 'a) (k : 'a -> 'b) : 'b =
  if is_exc (Obj.repr v) then
    Obj.magic (if is_unknown v then unknown_term ty else err_term ty)
  else k v
```

`unknown_term` and `err_term` already raise for a type that cannot
hold the block. Export `eliminate` next to `check` in
`pp_gradual_rt_sig` (`plugins/extraction/ocaml.ml`).

When the gradual primitives are registered, reify `mlt` with a
variant of `gradual_reify` that returns `None` instead of
`gradual_error` (a local type variable, a type stored in a
constructor, a partially applied inductive). On `Some ty`, emit

```ocaml
Gradual_rt.eliminate ty scrut (fun x -> match x with ...)
```

The later `gradual_guard_cases` pass still wraps the inner match
with `check`. That is what you want: `eliminate` returns before the
continuation when the scrutinee is `?` or `err`, and `check` still
stops a block from falling into an OCaml `match` (that match is
undefined behavior). On `None`, leave the match to `check`, so a
return type with no runtime description still extracts and still
raises on elimination.

The generated constructor cast (`MLcase` near the bottom of
`extract_gradual`) does not need this. `cast` in `gradual_rt.ml`
returns before calling that function when the value is already an
exception block and the target is an inductive that can hold it.

### Tests

`test-suite/misc/gradual_extraction.sh` is the check. After the
change:

- `t_unk_elim` prints `unk` as a value, through the `nat` printer,
  with no exception. Same for a match that returns `raise` at `nat`.
- `t_unk_plus`, `t_list_bad`, `t_list_bad_length`, and
  `t_list_bad_head` stay as they are. Length and head do not
  eliminate the `raise` in the tail.
- In `main.ml`, an `Unknown_term` exception is no longer `Same` when
  the kernel string is `unk`. A match that still raises where the
  kernel returned a `nat` value `unk` is a disagreement.
- Add one match whose return type cannot hold the block, for example
  `match unk with O => true | S _ => false`. The kernel result is
  `unk : bool`. Extraction raises, because `bool` is mapped. Mark it
  as a documented difference, next to `t_pair_bad`.
- `t_pair_bad` stays `(raise, raise)` in the kernel and an immediate
  `Cast_error` in OCaml. `t_poly_rec_bad` stays `[raise; raise]`
  against an immediate raise. Both are mapped `bool`. Do not try to
  make them values.

Update the "Eliminating `?` or `err` raises" paragraph in
`GRADUAL.md` to describe the new rule: elimination propagates when
the return type can hold the value, and raises when it cannot. Keep
the mapped-type, primitive, proof, universe, coinductive, and
array paragraphs.

### Still rejected at extraction time

A cast at a local `fun (A : Type) => …`, a type stored in a
constructor, or `@to_dyn` passed where `forall A, A -> Dyn` is
expected. `gradual_error` already names the constant-parameter
limit for a bare type variable. Leave the analysis in
`gradual_needed_params` until a program in this repo needs one of
those casts. Propositional casts stay unchecked because proofs are
erased. Universe levels stay erased. The runtime compares Prop, Set,
and Type.

## 3. Lock the array difference

Arrays of different element types are stuck in
`kernel/gradual.ml` (`HPrim` with equal heads, elements not visited)
and `Cast_error` in `gradual_rt.ml`. Do not make the kernel return
`err`, and do not make the runtime diverge. `success/gradual.v`
already checks the stuck kernel cast. Add a row to the three-way
test that records the `Cast_error`, marked as a documented
difference, if that row is not there yet.

## Check

Item 1 is a comment. Items 2 and 3 are extraction and the gradual
tests. Run:

```sh
dune build rocq-runtime.install
make -C test-suite success/gradual.v.log output/Gradual.v.log misc/gradual_extraction.sh
```

A full `make -C test-suite` is the conservativity check and is
already recorded at `935f6f8aad`. Run it again only if a change
touches the kernel, the elaborator, or a file the suite compiles
without importing `Gradual`.

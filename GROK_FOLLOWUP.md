# Follow-up

As of `75f40c8e88` on branch `gradual`. The previous note (`GROK_SUGGESTION.md`) is done. Those ten commits landed the list, with the exceptions below. This file is only what is still worth doing.

`plugins/extraction/` and `pretyping/gradualTyping.ml` were in the last commits. Check `git status` before editing them.

## What landed

| Suggestion | Commit |
|---|---|
| `Gradual Steps` budget, ordinary CIC not counted | `4fc9ffe223` |
| Sorts consistent only when cumulative; cast uses the universe graph | `564fcbb62e` |
| `rocqchk` installs `Register_gradual` for the rest of the module | `d3e0823656` |
| Annotated functions accepted at a less precise type | `338ca68f80` |
| One table: `lazy`, `cbv`, `cbn`, `simpl`, `vm_compute`, and extraction | `78a847265f` |
| Gradual reducts keep binders introduced by conversion | `78de1c48c8` |
| Indexed families (`vec`, `Fin`, `eq`); evars solved where the types agree | `800ab35894` |
| "Not consistent" names the first disagreeing heads | `85ff39f91b` |
| Above `Universe gradual`, the error says so (`Set : Dyn`) | `85173ea213` |
| `Qed` warns (`gradual-proof`) when the proof uses a primitive the statement does not | `75f40c8e88` |

`test-suite/success/gradual_vec.v` did not need a rule change. `list Type` and a universe-polymorphic record do cast to `Dyn`. A separate `Dyn@{i}` hierarchy is still not justified.

Leave the VM, native compilation, germ reconstruction, Haskell/Scheme, and a mechanization of the paper alone. Same reasons as before.

## 1. Make extraction compute the same values

The three-way test locks the disagreement instead of removing it. [GRADUAL.md](GRADUAL.md) still records:

| Term | Kernel | `plugins/extraction/gradual_rt.ml` |
|---|---|---|
| `cons raise nil` | a value | `Cast_error` at once |
| `2 + unk` | `S (S unk)` | `Unknown_term` |
| `unk : nat -> bool` | `fun _ => unk` | the same |

Represent error and unknown-at-an-inductive as data in `Gradual_rt`. Raise only when that value is eliminated (`match` that needs a constructor, a primitive operation, a projection). Then drop the "documented difference" marks in `test-suite/misc/gradual_extraction/main.out` for those two rows. Function `unk` is already the kernel's behavior.

Still rejected on purpose, and still later: a cast at a local `fun (A : Type) => …` or a type stored in a constructor, and a function that needs a runtime type parameter passed where `forall A, A -> Dyn` is expected (`gradual_needed_params` in `plugins/extraction/extraction.ml`). The runtime also compares only Prop, Set, and Type, while `sort_castable` in `kernel/gradual.ml` asks the universe graph. Levels are erased. Do not pretend those agree.

## 2. The evar clause is still there

`consistent` in `pretyping/gradualTyping.ml` still has `Evar _, _ | _, Evar _ -> true`. `unify_consistent` (the vector fix) solves the positions that match before the cast is inserted, which is why `vcons 1 (vcons true vnil) : vec Dyn unk` works. The clause remains the fallback: a leftover evar is treated as consistent with every type, so a cast can still be inserted where the evar should have stayed for unification.

Do not delete the clause until there is a failing term. Look for a goal whose evar is solved by a later argument, elaborated with `Gradual Typing` on, where today's output contains a `cast` and an unsolved or wrongly solved evar. If you find one, skip evars in `consistent` and in `inconsistency`, and let `unify_consistent` be the only place an evar is touched.

## 3. `cons 1 (cons true nil) : Dyn`

Checking at `list Dyn` works. Synthesis at `Dyn` still does not choose the parameters, and [GRADUAL.md](GRADUAL.md) says so on purpose. The ground choice, if you want it, is: when the expected type is `?` and the synthesized head is an inductive whose parameters are still evars, set those parameters to `Dyn` before checking the arguments. Explicit type arguments must keep winning (`leading_types` in `pretyping/pretyping.ml`, commit `154e4e6521`). Add a row to the graduality table in `test-suite/success/gradual.v` either way, so the choice stays a test and not a comment.

## 4. Holes the warning does not cover

`check_gradual_proof` in `vernac/declare.ml` runs only for `Decls.IsProof` with a `Default` body. It does not force an asynchronous proof, which the commit states. `proof_uses_gradual` does not follow opaque bodies. That is right only if every opaque proof was warned when it was saved. A `Defined` gradual lemma used inside a later proof is followed, because its body is transparent.

`uses_cache` in `pretyping/gradualTyping.ml` is a process-global `ref`, not a summary. A backtrack that replaces a constant can serve a stale list. Clear it where the retroknowledge or the constant table is reset, or key it so a changed body misses.

## 5. Fuel, checker, and the flag-off suite

`Gradual.step` is a pair of refs in `kernel/gradual.ml`, reset from `vernac/vernacinterp.ml` at each command. `rocqchk` runs with no limit, so a tampered `.vo` whose gradual reduction loops will hang the checker. A spent budget also sticks until the next reset: one overflowing command fails every later gradual step in that command. Both are acceptable if they are tested. Add a `rocqchk` case that a gradual loop inside one command does not need a `Timeout`, and that the next command still has its own budget.

Nobody has recorded `make -C test-suite` from this commit with `Gradual` not imported. That is the conservativity check. A failure there outranks the items above.

## 6. After the runtime values exist

Coinductive casts, and primitive `int`, `float`, `array`, and `string`, have no rule in `reduce_cast` and no case in `gradual_rt.ml`. Do the kernel rule and the runtime case in the same change, and add a row to the three-way test. Primitive integers matter once an extracted program should run on `int` rather than on `nat`.

`match` on `?` can still reduce to a term that lives above `Universe gradual` and would not re-typecheck. Leave it until a re-typecheck of a reduct fails on a program you care about. SProp stays out because the axioms quantify over `Type`.

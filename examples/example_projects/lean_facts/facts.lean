/-
  Theorems about series.soma's functions, proved in Lean. `Soma` is the
  module of Soma's definitions, which Soma translates to Lean
  (`Soma.series.sum_to`, `Soma.series.fib`); facts.definition says what
  Soma takes these theorems to be.
-/
import Soma
open Soma.series

theorem sum_to_formula : ∀ n, 2 * sum_to n = n * (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ m ih =>
    show 2 * ((m + 1) + sum_to m) = (m + 1) * (m + 1 + 1)
    grind

/-- each Fibonacci number and the next are at most the powers of 2 -/
theorem fib_le_pow_both : ∀ n, fib n ≤ 2 ^ n ∧ fib (n + 1) ≤ 2 ^ (n + 1) := by
  intro n
  induction n with
  | zero => decide
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    show fib m + fib (m + 1) ≤ 2 ^ (m + 1 + 1)
    have h1 := ih.1
    have h2 := ih.2
    have : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ 2 (m + 1)]
    omega

theorem fib_le_pow : ∀ n, fib n ≤ 2 ^ n := fun n => (fib_le_pow_both n).1

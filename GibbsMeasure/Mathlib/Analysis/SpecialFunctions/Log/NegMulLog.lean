/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy-type sums of `x log x`

* `Real.continuous_mul_log_div`: `x ↦ x log (x / c)` is continuous.
* `Real.neg_log_card_le_sum_mul_log`: **Gibbs' inequality**, the Shannon entropy `-∑ p log p` of a
  probability vector on a finite type `α` is at most `log |α|`.
-/

@[expose] public section

open Finset

namespace Real

/-- `x ↦ x log (x / c)` is continuous on `ℝ` (with Mathlib's conventions `log 0 = 0`,
`x / 0 = 0`). -/
lemma continuous_mul_log_div (c : ℝ) : Continuous fun x : ℝ ↦ x * log (x / c) := by
  by_cases hc : c = 0
  · simp only [hc, div_zero, Real.log_zero, mul_zero]
    exact continuous_const
  have : (fun x : ℝ ↦ x * log (x / c)) = fun x ↦ x * log x - x * log c := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hc, mul_sub]
  rw [this]
  exact Real.continuous_mul_log.sub (continuous_id.mul continuous_const)

/-- **Gibbs' inequality** on a finite type: the entropy `-∑ p log p` of a probability vector `p`
is at most `log |α|`, i.e. `-log |α| ≤ ∑ x, p x * log (p x)`. Summing `t - 1 ≤ t log t` at
`t = |α| p x` over `x`, the left-hand sides cancel. -/
theorem neg_log_card_le_sum_mul_log {α : Type*} [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x = 1) :
    -log (Fintype.card α) ≤ ∑ x, p x * log (p x) := by
  set c : ℝ := (Fintype.card α : ℝ) with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    exact_mod_cast Fintype.card_pos
  have h : ∀ x, (c * p x - 1) / c ≤ p x * log (c * p x) := fun x ↦ by
    have h1 := Real.self_sub_one_le_mul_log (mul_nonneg hc.le (hp0 x))
    rw [div_le_iff₀ hc]
    nlinarith [h1]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ h x
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hp, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_self, zero_div] at hsum
  have heq : ∑ x, p x * log (c * p x) = ∑ x, p x * log (p x) + log c := by
    rw [show ∑ x, p x * log (p x) + log c = ∑ x, (p x * log (p x) + p x * log c) by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : p x = 0
    · simp [hx]
    · rw [log_mul hc.ne' hx]
      ring
  linarith

end Real

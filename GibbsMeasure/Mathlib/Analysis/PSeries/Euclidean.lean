/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The Euclidean `p`-series on `ℤ²`

`∑_{x ∈ ℤ²} |x|^{-a} < ∞` for `a > 2`, where `|x|` is the Euclidean norm.  Mathlib proves this
for the sup norm, `EisensteinSeries.summable_one_div_norm_rpow`; the Euclidean statement follows
by comparison, since the sup norm is at most the Euclidean norm.

## Main results

* `summable_sum_sq_rpow_fin_two`: `Summable fun x : Fin 2 → ℤ ↦ (∑ c, (x c)²)^{-a/2}` for `a > 2`.
-/

@[expose] public section

/-- **The Euclidean `p`-series on `ℤ²` converges for `a > 2`:**
`∑_{x ∈ ℤ²} (x₀² + x₁²)^{-a/2} < ∞`.  (At `x = 0` the summand is `0^{-a/2} = 0`.)  Deduced from
the sup-norm statement `EisensteinSeries.summable_one_div_norm_rpow` by comparison. -/
theorem summable_sum_sq_rpow_fin_two {a : ℝ} (ha : 2 < a) :
    Summable fun x : Fin 2 → ℤ ↦ (∑ c, (x c : ℝ) ^ 2) ^ (-(a / 2)) := by
  refine Summable.of_norm_bounded_eventually (g := fun x : Fin 2 → ℤ ↦ ‖x‖ ^ (-a))
    (EisensteinSeries.summable_one_div_norm_rpow ha) ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : Fin 2 → ℤ)).subset fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hx ⊢
  by_contra hx0
  apply hx
  have hS : 0 ≤ ∑ c, (x c : ℝ) ^ 2 := Finset.sum_nonneg fun c _ ↦ sq_nonneg _
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hle : ‖x‖ ≤ Real.sqrt (∑ c, (x c : ℝ) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro c
    rw [Int.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun c ↦ (x c : ℝ) ^ 2)
      (fun c _ ↦ sq_nonneg _) (Finset.mem_univ c))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hS _)]
  calc (∑ c, (x c : ℝ) ^ 2) ^ (-(a / 2))
      = (Real.sqrt (∑ c, (x c : ℝ) ^ 2)) ^ (-a) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS]
        congr 1
        ring
    _ ≤ ‖x‖ ^ (-a) := Real.rpow_le_rpow_of_nonpos hxpos hle (by linarith)

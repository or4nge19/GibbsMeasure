/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian sums over a shifted lattice

For `ε > 0` and a period `r > 0`, `∑_{j ∈ ℤ} e^{-ε (y + r j)²} ≤ 2 + √(π / ε) / r` uniformly in the
offset `y` (`Real.tsum_exp_neg_mul_add_mul_intCast_sq_le`): the lattice-sum bound for radially
decreasing functions, `MeasureTheory.tsum_add_mul_intCast_le_lintegral`, with
`∫ e^{-ε t²} dt = √(π / ε)` (`integral_gaussian`). Being uniform in `y`, it bounds
`sup_y ∑_j e^{-ε (y + r j)²}`, the constant that controls a sum over integer fluxes at fixed real
background.
-/

@[expose] public section

open MeasureTheory Real

namespace ENNReal

/-- `∑_{j ∈ ℤ} e^{-ε (y + r j)²} ≤ 2 + √(π / ε) / r` in `ℝ≥0∞`, for `ε, r > 0` and every `y`. -/
theorem tsum_ofReal_exp_neg_mul_add_mul_intCast_sq_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (y : ℝ) :
    ∑' j : ℤ, ENNReal.ofReal (exp (-ε * (y + r * j) ^ 2)) ≤ ENNReal.ofReal (2 + √(π / ε) / r) := by
  refine (tsum_add_mul_intCast_le_lintegral (f := fun t ↦ ENNReal.ofReal (exp (-ε * t ^ 2)))
    (fun s t hst ↦ ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)) hr y).trans_eq ?_
  · have := sq_le_sq.2 hst
    nlinarith
  · rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq hε)
      (ae_of_all _ fun _ ↦ (exp_pos _).le), integral_gaussian,
      ENNReal.ofReal_add zero_le_two (by positivity), ENNReal.ofReal_div_of_pos hr]
    simp

end ENNReal

namespace Real

/-- The Gaussian weights over a shifted lattice are summable. -/
theorem summable_exp_neg_mul_add_mul_intCast_sq {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (y : ℝ) :
    Summable fun j : ℤ ↦ exp (-ε * (y + r * j) ^ 2) := by
  refine (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ENNReal.tsum_ofReal_exp_neg_mul_add_mul_intCast_sq_le hε hr y))).congr fun j ↦ ?_
  exact ENNReal.toReal_ofReal (exp_pos _).le

/-- **Gaussian sums over a shifted lattice**: `∑_{j ∈ ℤ} e^{-ε (y + r j)²} ≤ 2 + √(π / ε) / r`
for `ε, r > 0`, uniformly in `y`. -/
theorem tsum_exp_neg_mul_add_mul_intCast_sq_le {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (y : ℝ) :
    ∑' j : ℤ, exp (-ε * (y + r * j) ^ 2) ≤ 2 + √(π / ε) / r := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_tsum_of_nonneg
    (fun _ ↦ (exp_pos _).le) (summable_exp_neg_mul_add_mul_intCast_sq hε hr y)]
  exact ENNReal.tsum_ofReal_exp_neg_mul_add_mul_intCast_sq_le hε hr y

end Real

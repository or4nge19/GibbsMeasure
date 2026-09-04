/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Summability of the discrete Gaussian weights

The one-dimensional theta series `∑_{n ∈ ℤ} e^{-b n²}` converges for every `b > 0`, together with
the `ℝ≥0∞`-valued form used to integrate against counting measure on `ℤ`.

The bound is the crude comparison `e^{-b n²} ≤ (e^{-b})^{|n|}` with a geometric series; the exact
Jacobi theta identities of `Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation` are not
needed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Real

/-- `e^{-b n²} ≤ (e^{-b})^n` for `0 ≤ b` and `n : ℕ`. -/
theorem exp_neg_mul_sq_le_pow {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    exp (-b * (n : ℝ) ^ 2) ≤ exp (-b) ^ n := by
  rw [← exp_nat_mul]
  refine exp_le_exp.2 ?_
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · nlinarith [Nat.one_le_cast (α := ℝ) |>.2 hpos]
  nlinarith

/-- The discrete Gaussian weights are summable over `ℕ`. -/
theorem summable_exp_neg_mul_sq_nat {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℕ ↦ exp (-b * (n : ℝ) ^ 2) := by
  have hlt : exp (-b) < 1 := exp_lt_one_iff.2 (by linarith)
  exact Summable.of_nonneg_of_le (fun n ↦ (exp_pos _).le)
    (fun n ↦ exp_neg_mul_sq_le_pow hb.le n)
    (summable_geometric_of_lt_one (exp_pos _).le hlt)

/-- **The discrete Gaussian weights are summable over `ℤ`**: `∑_{n ∈ ℤ} e^{-b n²} < ∞` for
`b > 0`. -/
theorem summable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℤ ↦ exp (-b * (n : ℝ) ^ 2) := by
  refine Summable.of_nat_of_neg (summable_exp_neg_mul_sq_nat hb) ?_
  simpa using summable_exp_neg_mul_sq_nat hb

end Real

namespace ENNReal

/-- The `ℝ≥0∞`-valued discrete Gaussian sum is finite: `∑_{n ∈ ℤ} e^{-b n²} ≠ ∞` for `b > 0`. -/
theorem tsum_ofReal_exp_neg_mul_sq_ne_top {b : ℝ} (hb : 0 < b) :
    (∑' n : ℤ, ENNReal.ofReal (Real.exp (-b * (n : ℝ) ^ 2))) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ (Real.exp_pos _).le)
    (Real.summable_exp_neg_mul_sq hb)]
  exact ENNReal.ofReal_ne_top

/-- The counting-measure integral of the discrete Gaussian weight on `ℤ` is finite. -/
theorem lintegral_count_ofReal_exp_neg_mul_sq_ne_top {b : ℝ} (hb : 0 < b) :
    (∫⁻ n : ℤ, ENNReal.ofReal (Real.exp (-b * (n : ℝ) ^ 2)) ∂Measure.count) ≠ ⊤ := by
  rw [lintegral_count]
  exact tsum_ofReal_exp_neg_mul_sq_ne_top hb

end ENNReal

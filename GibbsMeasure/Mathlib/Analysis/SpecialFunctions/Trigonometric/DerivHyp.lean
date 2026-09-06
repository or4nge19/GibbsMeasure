/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A quadratic lower bound for `Real.cosh`

`1 + x²/2 ≤ cosh x`: the partial sum of order two of the hyperbolic cosine is a lower bound,
because every further term of its power series is nonnegative.  It is the counterpart of
Mathlib's upper bound `Real.cosh_le_exp_half_sq : cosh x ≤ exp (x ^ 2 / 2)`, which lives in
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.lean`.

The proof here is elementary — `x ≤ sinh x` for `x ≥ 0` (`Real.self_le_sinh_iff`) and the
identity `cosh x = 1 + 2 sinh(x/2)²` — so the lemma is stated in the file where `Real.one_le_cosh`
lives rather than with the power series.

## Main results

* `Real.one_add_sq_div_two_le_cosh`
* `Real.two_add_sq_le_exp_add_exp_neg`, the same inequality written out as
  `2 + x² ≤ e^x + e^{-x}`.
-/

@[expose] public section

namespace Real

/-- `x² ≤ sinh x ^ 2`: the hyperbolic sine moves away from the origin at least as fast as the
identity, in both directions. -/
theorem sq_le_sinh_sq (x : ℝ) : x ^ 2 ≤ sinh x ^ 2 := by
  rcases le_total 0 x with hx | hx
  · nlinarith [self_le_sinh_iff.2 hx]
  · have hx' : (0 : ℝ) ≤ -x := by linarith
    have h := self_le_sinh_iff.2 hx'
    rw [sinh_neg] at h
    nlinarith

/-- **`1 + x²/2 ≤ cosh x`**: the second-order Taylor polynomial of `cosh` is a lower bound.

Together with `Real.cosh_le_exp_half_sq` this pins `cosh` between `1 + x²/2` and `e^{x²/2}`. -/
theorem one_add_sq_div_two_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ cosh x := by
  have hd : cosh x = 1 + 2 * sinh (x / 2) ^ 2 := by
    have h := cosh_two_mul (x / 2)
    rw [show (2 : ℝ) * (x / 2) = x by ring, cosh_sq] at h
    linarith
  have hs := sq_le_sinh_sq (x / 2)
  rw [hd]
  nlinarith

/-- `2 + x² ≤ e^x + e^{-x}`, the form of `Real.one_add_sq_div_two_le_cosh` that turns a
Gaussian-domination bound into a second-moment bound. -/
theorem two_add_sq_le_exp_add_exp_neg (x : ℝ) : 2 + x ^ 2 ≤ exp x + exp (-x) := by
  have h := one_add_sq_div_two_le_cosh x
  rw [cosh_eq] at h
  linarith

end Real

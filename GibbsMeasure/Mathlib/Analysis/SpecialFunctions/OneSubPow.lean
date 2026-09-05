/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Exponential

/-!
# The bound `(1 - t)^n ≤ e^{-tn}`

The elementary estimate `(1 - t) ^ n ≤ exp (-(t * n))` for `t ≤ 1`: the survival probability of
`n` independent trials each failing with probability `t`. It is Mathlib's
`Real.one_sub_div_pow_le_exp_neg` in the form where the exponent carries the factor `n` instead
of the base carrying `1/n`.
-/

@[expose] public section

namespace Real

/-- `(1 - t)^n ≤ e^{-tn}` for `t ≤ 1`. -/
theorem one_sub_pow_le_exp_neg_mul {t : ℝ} (ht : t ≤ 1) (n : ℕ) :
    (1 - t) ^ n ≤ Real.exp (-(t * n)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Real.one_sub_div_pow_le_exp_neg (n := n) (t := t * n) (by nlinarith)
    rwa [mul_div_assoc, div_self hn'.ne', mul_one] at h

end Real

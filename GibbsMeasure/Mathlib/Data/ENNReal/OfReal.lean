/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.ENNReal.Real

/-!
# Small real scalars in `ℝ≥0∞`

`ENNReal.ofReal` turns a real scalar into an element of `ℝ≥0∞`. The lemma below records that
`t ↦ a + ENNReal.ofReal t * b` is small for small `t > 0` whenever `a < 1` and `b ≠ ∞`; it is the
`ℝ≥0∞` form of the statement that an open half-line condition survives a small perturbation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace ENNReal

/-- If `a < 1` and `b ≠ ∞`, then `a + t b < 1` for some real `t > 0`. -/
theorem exists_pos_add_ofReal_mul_lt_one {a b : ℝ≥0∞} (ha : a < 1) (hb : b ≠ ∞) :
    ∃ t : ℝ, 0 < t ∧ a + ENNReal.ofReal t * b < 1 := by
  have hatop : a ≠ ∞ := ha.ne_top
  have hA1 : a.toReal < 1 := by
    rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal by simp]
    exact (ENNReal.toReal_lt_toReal hatop one_ne_top).2 ha
  have hA0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have h1A : 0 < 1 - a.toReal := by linarith
  set t : ℝ := (1 - a.toReal) / (2 * (b.toReal + 1)) with ht
  have htpos : 0 < t := div_pos h1A (by positivity)
  have htB : t * b.toReal < 1 - a.toReal := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  refine ⟨t, htpos, ?_⟩
  have hmul : ENNReal.ofReal t * b = ENNReal.ofReal (t * b.toReal) := by
    rw [ENNReal.ofReal_mul htpos.le, ENNReal.ofReal_toReal hb]
  rw [hmul, ← ENNReal.ofReal_toReal hatop,
    ← ENNReal.ofReal_add hA0 (mul_nonneg htpos.le hB0),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)

end ENNReal

end

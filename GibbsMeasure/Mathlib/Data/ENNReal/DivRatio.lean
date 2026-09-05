/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.ENNReal.Inv

/-!
# Cross-multiplying an equality of real ratios of `ℝ≥0∞` quantities

An equality of the *real* ratios `a.toReal / b.toReal = c.toReal / d.toReal` of four finite,
non-zero extended non-negative reals is the same as the `ℝ≥0∞` identity `a * d = c * b`. This is
the standard way of turning the limit of a ratio (which only makes sense in `ℝ`, since `ℝ≥0∞`
division is badly behaved at `0` and `∞`) back into an identity in `ℝ≥0∞`.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Cross-multiplication: an equality of the real ratios of four finite `ℝ≥0∞` numbers with
non-zero denominators is the `ℝ≥0∞` identity `a * d = c * b`. -/
theorem mul_eq_mul_of_toReal_div_eq {a b c d : ℝ≥0∞} (ha : a ≠ ⊤) (hb₀ : b ≠ 0) (hb : b ≠ ⊤)
    (hc : c ≠ ⊤) (hd₀ : d ≠ 0) (hd : d ≠ ⊤)
    (h : a.toReal / b.toReal = c.toReal / d.toReal) : a * d = c * b := by
  have hb' : b.toReal ≠ 0 := (ENNReal.toReal_pos hb₀ hb).ne'
  have hd' : d.toReal ≠ 0 := (ENNReal.toReal_pos hd₀ hd).ne'
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top ha hd) (ENNReal.mul_ne_top hc hb),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  exact (div_eq_div_iff hb' hd').1 h

end ENNReal

end

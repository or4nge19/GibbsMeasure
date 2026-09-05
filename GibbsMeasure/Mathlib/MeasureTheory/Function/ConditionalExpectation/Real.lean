/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.Analysis.Normed.Group.Real

/-!
# The `L¹` contraction property of the conditional expectation, in `ℝ≥0∞` form
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- The `L¹`-contraction property of the conditional expectation, in `ℝ≥0∞` form. -/
theorem lintegral_ofReal_abs_condExp_le {Ω : Type*} {m m0 : MeasurableSpace Ω} {w : Measure Ω}
    (f : Ω → ℝ) :
    ∫⁻ x, ENNReal.ofReal |(w[f | m]) x| ∂w ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂w := by
  simpa only [eLpNorm_one_eq_lintegral_enorm, Real.enorm_eq_ofReal_abs] using
    eLpNorm_condExp_le_eLpNorm (m := m) (μ := w) f le_rfl

end MeasureTheory

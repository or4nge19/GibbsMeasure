/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiWithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilating an absolutely continuous measure

`MeasureTheory.Measure.map_addHaar_smul` computes the image of an additive Haar measure under a
dilation `x ↦ r • x`.  This file records the same for a measure with a density.

## Main results

* `MeasureTheory.Measure.map_addHaar_smul_withDensity`:
  `(μ.withDensity p).map (r • ·) = |r ^ dim|⁻¹ • μ.withDensity (p ∘ (r⁻¹ • ·))`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The dilation of an absolutely continuous measure.**  Rescaling by `r ≠ 0` rescales the
density by `r⁻¹` and its total mass by `|r ^ dim|`. -/
theorem map_addHaar_smul_withDensity {r : ℝ} (hr : r ≠ 0) {p : E → ℝ≥0∞} (hp : Measurable p) :
    (μ.withDensity p).map (r • ·)
      = ENNReal.ofReal |(r ^ Module.finrank ℝ E)⁻¹| • μ.withDensity fun x ↦ p (r⁻¹ • x) := by
  have hsmul : Measurable fun x : E ↦ r • x := measurable_const_smul r
  have hp' : Measurable fun x : E ↦ p (r⁻¹ • x) := hp.comp (measurable_const_smul r⁻¹)
  have key := map_withDensity_comp (J := fun x : E ↦ r • x) (G := fun y ↦ p (r⁻¹ • y)) μ hsmul hp'
  simp only [inv_smul_smul₀ hr] at key
  rw [key, map_addHaar_smul μ hr, withDensity_smul_measure]

end MeasureTheory.Measure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Pushing an exponentially tilted measure forward

If the tilt factors through a measurable map `φ`, tilting commutes with the pushforward along `φ`:
`(μ.tilted (g ∘ φ)).map φ = (μ.map φ).tilted g` (`MeasureTheory.map_tilted_comp`). The underlying
statement is the same one for densities, `(μ.withDensity (f ∘ φ)).map φ = (μ.map φ).withDensity f`
(`MeasureTheory.Measure.map_withDensity_comp`); the normalising integral of the tilt is the same on
both sides by the change-of-variables formula.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}

/-- Pushing forward a measure with a density that factors through the map: the density is
transported along. -/
theorem Measure.map_withDensity_comp {φ : α → β} (hφ : Measurable φ) {f : β → ℝ≥0∞}
    (hf : Measurable f) : (μ.withDensity (f ∘ φ)).map φ = (μ.map φ).withDensity f := by
  ext s hs
  rw [Measure.map_apply hφ hs, withDensity_apply _ (hφ hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hφ]
  rfl

/-- Tilting commutes with pushing forward along a map through which the tilt factors. -/
theorem map_tilted_comp {φ : α → β} (hφ : Measurable φ) {g : β → ℝ} (hg : Measurable g) :
    (μ.tilted (g ∘ φ)).map φ = (μ.map φ).tilted g := by
  have hint : ∫ x, Real.exp (g x) ∂(μ.map φ) = ∫ x, Real.exp (g (φ x)) ∂μ :=
    integral_map hφ.aemeasurable (Real.measurable_exp.comp hg).aestronglyMeasurable
  simp only [Measure.tilted, hint, Function.comp_apply]
  exact Measure.map_withDensity_comp hφ
    (f := fun x ↦ ENNReal.ofReal (Real.exp (g x) / ∫ x, Real.exp (g (φ x)) ∂μ))
    ((Real.measurable_exp.comp hg).div_const _).ennreal_ofReal

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Densities and the Giry monad
-/

@[expose] public section

open Set MeasureTheory ENNReal
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Binding into a density-modified family of measures is a density change of the bind. -/
lemma bind_withDensity (μ : Measure α) {κ : α → Measure β} (hκ : Measurable κ)
    {ρ : β → ℝ≥0∞} (hρ : Measurable ρ) :
    μ.bind (fun a ↦ (κ a).withDensity ρ) = (μ.bind κ).withDensity ρ := by
  have hmeas : Measurable fun a ↦ (κ a).withDensity ρ := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp_rw [withDensity_apply _ hs]
    exact (Measure.measurable_setLIntegral hρ hs).comp hκ
  ext A hA
  rw [Measure.bind_apply hA hmeas.aemeasurable, withDensity_apply _ hA, ← lintegral_indicator hA,
    Measure.lintegral_bind hκ.aemeasurable (hρ.indicator hA).aemeasurable]
  refine lintegral_congr fun a ↦ ?_
  rw [withDensity_apply _ hA, lintegral_indicator hA]

end MeasureTheory.Measure

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Inverting a positive finite density. -/
lemma withDensity_inv_of_eq {μ ν : Measure α} {ρ : α → ℝ≥0∞} (hρ : Measurable ρ)
    (h0 : ∀ x, ρ x ≠ 0) (htop : ∀ x, ρ x ≠ ⊤) (h : μ = ν.withDensity ρ) :
    ν = μ.withDensity ρ⁻¹ := by
  rw [h, ← withDensity_mul _ hρ hρ.inv]
  have : ρ * ρ⁻¹ = 1 := funext fun x ↦ ENNReal.mul_inv_cancel (h0 x) (htop x)
  rw [this, withDensity_one]

end MeasureTheory

/-! ### Transport of densities along a measurable equivalence -/

/-- The image of `μ.withDensity f` under a measurable equivalence `e` is `(μ.map e)` with
density `f ∘ e.symm`. -/
theorem MeasurableEquiv.map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity (f ∘ e.symm) := by
  refine Measure.ext fun s hs ↦ ?_
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs, e.restrict_map,
    lintegral_map_equiv]
  simp only [Function.comp_apply, e.symm_apply_apply]

/-! ### Georgii (5.6)(b): transport of `λ`-modifications -/


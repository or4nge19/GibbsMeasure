/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.UniformAverage
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration against a uniform average of measures

`∫ f d(|F|⁻¹ ∑_{i ∈ F} mᵢ) = |F|⁻¹ ∑_{i ∈ F} ∫ f dmᵢ`.

Intended home: next to `MeasureTheory.uniformAverage`.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace MeasureTheory

variable {ι Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
/-- The integral against a uniform average of measures is the average of the integrals. -/
theorem integral_uniformAverage (m : ι → Measure Ω) (s : Finset ι) {f : Ω → F}
    (hf : ∀ i ∈ s, Integrable f (m i)) :
    ∫ x, f x ∂(uniformAverage m s) = (s.card : ℝ)⁻¹ • ∑ i ∈ s, ∫ x, f x ∂(m i) := by
  rw [uniformAverage, integral_smul_measure, integral_finsetSum_measure hf]
  congr 1
  simp

/-- The uniform average of the Dirac measures at the points `g i`, `i ∈ s`. -/
theorem integral_uniformAverage_dirac (g : ι → Ω) (s : Finset ι)
    {f : Ω → F} (hf : StronglyMeasurable f) :
    ∫ x, f x ∂(uniformAverage (fun i ↦ Measure.dirac (g i)) s)
      = (s.card : ℝ)⁻¹ • ∑ i ∈ s, f (g i) := by
  have hint : ∀ i ∈ s, Integrable f (Measure.dirac (g i)) := fun i _ ↦
    ⟨hf.aestronglyMeasurable, by
      rw [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]
      exact enorm_lt_top⟩
  rw [integral_uniformAverage _ _ hint]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ integral_dirac' f (g i) hf

end MeasureTheory

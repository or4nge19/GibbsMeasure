/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Bochner integral against the composition of a kernel with a measure
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma integral_comp' [SFinite μ] [IsSFiniteKernel κ] {f : β → E}
    (hf : Integrable f (κ ∘ₘ μ)) :
    ∫ b, f b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ := by
  rw [← Measure.snd_compProd, Measure.snd] at hf ⊢
  rw [integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    Measure.integral_compProd]
  exact (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).1 hf

/-- `Measure.bind` form of `Measure.integral_comp'`. -/
lemma integral_bind [SFinite μ] [IsSFiniteKernel κ] {f : β → E}
    (hf : Integrable f (μ.bind κ)) :
    ∫ b, f b ∂(μ.bind κ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ :=
  integral_comp' hf

end MeasureTheory.Measure

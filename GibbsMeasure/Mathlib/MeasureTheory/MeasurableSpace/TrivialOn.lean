/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.Filter.CountableSeparatingOn
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Measurability for an infimum of σ-algebras, and zero-one laws

Two facts about a sub-σ-algebra `𝒜` of `m` that belong to Mathlib rather than to any particular
theory:

* `measurable_iInf_iff_forall`: a map is measurable for `⨅ i, 𝒜 i` exactly when it is measurable
  for every `𝒜 i`, because the infimum of σ-algebras is their intersection.
* `MeasureTheory.exists_ae_eq_const_of_forall_measure_eq_zero_or_one`: if a probability measure
  satisfies a zero-one law on `𝒜`, every `𝒜`-measurable map into a countably separated space is
  a.e. constant.
-/

@[expose] public section

open MeasureTheory

/-- A map is measurable for an infimum of σ-algebras exactly when it is measurable for each of
them: the infimum of σ-algebras is their intersection. -/
lemma measurable_iInf_iff_forall {Ω : Type*} {κ : Sort*} (mκ : κ → MeasurableSpace Ω)
    {X : Type*} [MeasurableSpace X] {f : Ω → X} :
    Measurable[⨅ i, mκ i] f ↔ ∀ i, Measurable[mκ i] f := by
  refine ⟨fun h i ↦ h.mono (iInf_le _ i) le_rfl, fun h U hU ↦ ?_⟩
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun i ↦ h i hU

namespace MeasureTheory

/-- If a probability measure `μ` satisfies the zero-one law on a sub-σ-algebra `𝒜` — every
`𝒜`-set is null or co-null — then every `𝒜`-measurable map into a countably separated space is
`μ`-a.e. constant. -/
lemma exists_ae_eq_const_of_forall_measure_eq_zero_or_one {Ω : Type*} {𝒜 m : MeasurableSpace Ω}
    (h𝒜 : 𝒜 ≤ m) {μ : Measure[m] Ω} [IsProbabilityMeasure μ]
    (htriv : ∀ A, MeasurableSet[𝒜] A → μ A = 0 ∨ μ A = 1)
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] [Nonempty X]
    {f : Ω → X} (hf : Measurable[𝒜] f) : ∃ c : X, f =ᵐ[μ] fun _ ↦ c := by
  refine Filter.exists_eventuallyEq_const_of_forall_separating (l := ae μ) (f := f)
    MeasurableSet fun U hU ↦ ?_
  have hpre : MeasurableSet[𝒜] (f ⁻¹' U) := hf hU
  rcases htriv _ hpre with h0 | h1
  · exact Or.inr (by rw [ae_iff]; simp only [not_not]; exact h0)
  · exact Or.inl (by rw [ae_iff]; exact (prob_compl_eq_zero_iff (h𝒜 _ hpre)).2 h1)

end MeasureTheory

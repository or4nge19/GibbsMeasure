/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Probability.ConditionalProbability

/-!
# The recurrent set of a measure-preserving map

For a self-map `f` of a measurable space, `{x | ∃ᶠ n in atTop, f^[n] x ∈ s}` is the set of
points whose forward orbit visits `s` infinitely often.  It is strictly `f`-invariant
(`preimage_setOf_frequently_iterate_mem`) and measurable
(`measurableSet_setOf_frequently_iterate_mem`).

Poincaré recurrence (`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`) says that
almost every point of `s` lies in that set.  Applying it to the conditional measure on its
complement — which is again invariant, the complement of an invariant set being invariant —
gives the sharper statement recorded here: *conditionally on not returning to `s` infinitely
often, `s` itself is null* (`MeasureTheory.cond_compl_setOf_frequently_iterate_apply_eq_zero`).
-/

@[expose] public section

open Filter Set
open scoped ENNReal ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α} {s : Set α}

/-- The set of points whose forward orbit visits `s` infinitely often is strictly invariant. -/
theorem preimage_setOf_frequently_iterate_mem (f : α → α) (s : Set α) :
    f ⁻¹' {x | ∃ᶠ n in atTop, f^[n] x ∈ s} = {x | ∃ᶠ n in atTop, f^[n] x ∈ s} := by
  ext x
  simp only [mem_preimage, Set.mem_ofPred_eq, frequently_atTop]
  constructor
  · intro h a
    obtain ⟨b, hb, hb'⟩ := h a
    exact ⟨b + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
  · intro h a
    obtain ⟨b, hb, hb'⟩ := h (a + 1)
    refine ⟨b - 1, by omega, ?_⟩
    rw [← Function.iterate_succ_apply]
    rwa [show (b - 1).succ = b by omega]

/-- The set of points whose forward orbit visits a measurable set infinitely often is
measurable. -/
theorem measurableSet_setOf_frequently_iterate_mem (hf : Measurable f) (hs : MeasurableSet s) :
    MeasurableSet {x | ∃ᶠ n in atTop, f^[n] x ∈ s} := by
  have hrw : {x | ∃ᶠ n in atTop, f^[n] x ∈ s} = ⋂ N : ℕ, ⋃ n ∈ Ici N, f^[n] ⁻¹' s := by
    ext x
    simp only [Set.mem_ofPred_eq, frequently_atTop, mem_iInter, mem_iUnion, mem_Ici,
      mem_preimage, exists_prop]
  rw [hrw]
  exact MeasurableSet.iInter fun _ ↦ MeasurableSet.biUnion (Set.to_countable _)
    fun n _ ↦ hs.preimage (hf.iterate n)

/-- Restricting a measure-preserving map to a strictly invariant set preserves the restricted
measure. -/
theorem MeasurePreserving.restrict_of_preimage_eq (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) :
    MeasurePreserving f (μ.restrict s) (μ.restrict s) := by
  refine ⟨hf.measurable, Measure.ext fun t ht ↦ ?_⟩
  rw [Measure.map_apply hf.measurable ht, Measure.restrict_apply (ht.preimage hf.measurable),
    Measure.restrict_apply ht,
    show f ⁻¹' t ∩ s = f ⁻¹' (t ∩ s) by rw [Set.preimage_inter, hfs],
    ← Measure.map_apply hf.measurable (ht.inter hs), hf.map_eq]

/-- Conditioning a measure-preserving map on a strictly invariant set preserves the conditional
measure. -/
theorem MeasurePreserving.cond_of_preimage_eq (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hfs : f ⁻¹' s = s) : MeasurePreserving f (μ[|s]) (μ[|s]) := by
  refine ⟨hf.measurable, ?_⟩
  rw [ProbabilityTheory.cond, Measure.map_smul _ hf.measurable.aemeasurable,
    (hf.restrict_of_preimage_eq hs hfs).map_eq]

/-- **Poincaré recurrence, sharp form.**  Conditionally on the complement of the set of points
whose orbit visits `s` infinitely often, the set `s` is null.  Consequently a measure-preserving
map of a probability space visits every non-null set infinitely often, unless conditioning on
never doing so already kills the set. -/
theorem cond_compl_setOf_frequently_iterate_apply_eq_zero [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hs : MeasurableSet s) :
    (μ[|{x | ∃ᶠ n in atTop, f^[n] x ∈ s}ᶜ]) s = 0 := by
  set R : Set α := {x | ∃ᶠ n in atTop, f^[n] x ∈ s} with hR
  have hRm : MeasurableSet R := measurableSet_setOf_frequently_iterate_mem hf.measurable hs
  have hRinv : f ⁻¹' Rᶜ = Rᶜ := by
    rw [Set.preimage_compl, preimage_setOf_frequently_iterate_mem]
  rcases eq_or_ne (μ Rᶜ) 0 with h0 | h0
  · rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 h0, smul_zero, Measure.coe_zero,
      Pi.zero_apply]
  haveI : IsProbabilityMeasure (μ[|Rᶜ]) := ProbabilityTheory.cond_isProbabilityMeasure h0
  have hcons : Conservative f (μ[|Rᶜ]) :=
    (hf.cond_of_preimage_eq hRm.compl hRinv).conservative
  have hbad : (μ[|Rᶜ]) {x | ¬ (x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s)} = 0 :=
    ae_iff.1 (hcons.ae_mem_imp_frequently_image_mem hs.nullMeasurableSet)
  have hzero : (μ[|Rᶜ]) R = 0 := by
    rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply hRm, smul_eq_mul,
      Set.inter_compl_self, measure_empty, mul_zero]
  have hsub : s ⊆ R ∪ {x | ¬ (x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s)} := by
    intro x hx
    by_cases hxR : x ∈ R
    · exact Or.inl hxR
    · exact Or.inr fun h ↦ hxR (h hx)
  refine nonpos_iff_eq_zero.1 ?_
  calc (μ[|Rᶜ]) s ≤ (μ[|Rᶜ]) (R ∪ {x | ¬ (x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s)}) :=
        measure_mono hsub
    _ ≤ (μ[|Rᶜ]) R + (μ[|Rᶜ]) {x | ¬ (x ∈ s → ∃ᶠ n in atTop, f^[n] x ∈ s)} :=
        measure_union_le _ _
    _ = 0 := by rw [hzero, hbad, add_zero]

end MeasureTheory

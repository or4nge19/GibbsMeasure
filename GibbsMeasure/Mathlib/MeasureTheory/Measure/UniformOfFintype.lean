/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Count

/-!
# The uniform measure on a finite type

`uniformOfFintype H` is counting measure on a finite type normalised by the cardinality. On a
finite group it is the Haar measure: it is a left-invariant probability measure, which is what
symmetrisation arguments over a finite group of symmetries need.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

variable (H) in
/-- The uniform probability measure on a finite type: counting measure normalised by the
cardinality.  On a finite group it is the Haar measure, and in particular left invariant
(`map_mul_left_uniformOfFintype`). -/
noncomputable def uniformOfFintype : Measure H := (Fintype.card H : ℝ≥0∞)⁻¹ • Measure.count

instance isProbabilityMeasure_uniformOfFintype [Nonempty H] :
    IsProbabilityMeasure (uniformOfFintype H) := by
  constructor
  have hcount : Measure.count (Set.univ : Set H) = (Fintype.card H : ℝ≥0∞) := by
    rw [Measure.count_apply_finite _ Set.finite_univ]
    simp [Set.Finite.toFinset_univ]
  rw [uniformOfFintype, Measure.smul_apply, smul_eq_mul, hcount,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp)]

/-- Counting measure is invariant under a bijection. -/
lemma count_preimage_of_bijective {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {f : α → β} (hf : Function.Bijective f) (s : Set β) :
    Measure.count (f ⁻¹' s) = Measure.count s := by
  calc Measure.count (f ⁻¹' s)
      = Measure.count (f '' (f ⁻¹' s)) := (Measure.count_injective_image hf.injective _).symm
    _ = Measure.count s := by rw [Set.image_preimage_eq s hf.surjective]

/-- The uniform measure on a finite group is left invariant. -/
lemma map_mul_left_uniformOfFintype [Group H] [MeasurableMul H] (g : H) :
    (uniformOfFintype H).map (g * ·) = uniformOfFintype H := by
  have hmeas : Measurable (g * · : H → H) := measurable_const_mul g
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply hmeas hs, uniformOfFintype, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul,
    count_preimage_of_bijective (Group.mulLeft_bijective g) s]

end MeasureTheory.Measure

end

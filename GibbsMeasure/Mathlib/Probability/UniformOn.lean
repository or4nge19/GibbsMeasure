/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.UniformOn

/-!
# The uniform measure on a finite group is left invariant

`ProbabilityTheory.uniformOn Set.univ` is the uniform probability measure on a finite type
(counting measure normalised by the cardinality). On a finite group it is the Haar measure: it is
left invariant, which is what symmetrisation arguments over a finite group of symmetries need.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

/-- Counting measure is invariant under a bijection. -/
lemma count_preimage_of_bijective {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {f : α → β} (hf : Function.Bijective f) (s : Set β) :
    Measure.count (f ⁻¹' s) = Measure.count s := by
  calc Measure.count (f ⁻¹' s)
      = Measure.count (f '' (f ⁻¹' s)) := (Measure.count_injective_image hf.injective _).symm
    _ = Measure.count s := by rw [Set.image_preimage_eq s hf.surjective]

variable {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- The uniform measure on a finite group is left invariant: it is the Haar measure. -/
lemma map_mul_left_uniformOn_univ [Group H] [MeasurableMul H] (g : H) :
    (uniformOn (Set.univ : Set H)).map (g * ·) = uniformOn Set.univ := by
  have hmeas : Measurable (g * · : H → H) := measurable_const_mul g
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.map_apply hmeas hs, uniformOn_univ, uniformOn_univ,
    count_preimage_of_bijective (Group.mulLeft_bijective g) s]

end ProbabilityTheory

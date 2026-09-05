/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Counting measure and measurable equivalences

A measurable equivalence pushes counting measure forward to counting measure. Mathlib has the
inequality `Function.Injective.map_count_le`; applying it to `e` and to `e.symm` turns it into an
equality, with no separability assumption on either space.
-/

@[expose] public section

open MeasureTheory

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A measurable equivalence maps counting measure to counting measure. -/
@[simp]
theorem map_count (e : α ≃ᵐ β) : (Measure.count : Measure α).map e = Measure.count := by
  refine le_antisymm (e.injective.map_count_le e.measurable) ?_
  have h := Measure.map_mono (e.symm.injective.map_count_le e.symm.measurable) e.measurable
  rwa [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id] at h

/-- A measurable equivalence preserves counting measure. -/
theorem measurePreserving_count (e : α ≃ᵐ β) :
    MeasurePreserving e (Measure.count : Measure α) Measure.count :=
  ⟨e.measurable, e.map_count⟩

end MeasurableEquiv

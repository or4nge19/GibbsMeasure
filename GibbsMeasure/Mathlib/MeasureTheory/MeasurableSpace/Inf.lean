/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Measurability for an infimum of σ-algebras

The infimum of a family of σ-algebras is their intersection, so a function is measurable for it
exactly when it is measurable for each member of the family. Only the direction that is used
downstream is recorded here.

Intended home: `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`.
-/

@[expose] public section

open MeasureTheory

/-- A function measurable for two σ-algebras is measurable for their infimum. -/
theorem Measurable.inf_measurableSpace {α β : Type*} {m₁ m₂ : MeasurableSpace α}
    [MeasurableSpace β] {f : α → β} (h₁ : Measurable[m₁] f) (h₂ : Measurable[m₂] f) :
    Measurable[m₁ ⊓ m₂] f :=
  fun _ hs ↦ MeasurableSpace.measurableSet_inf.2 ⟨h₁ hs, h₂ hs⟩

/-- A function measurable for every member of a family of σ-algebras is measurable for their
infimum. -/
theorem Measurable.iInf_measurableSpace {α β ι : Type*} {m : ι → MeasurableSpace α}
    [MeasurableSpace β] {f : α → β} (h : ∀ i, Measurable[m i] f) : Measurable[⨅ i, m i] f :=
  fun _ hs ↦ MeasurableSpace.measurableSet_iInf.2 fun i ↦ h i hs

end

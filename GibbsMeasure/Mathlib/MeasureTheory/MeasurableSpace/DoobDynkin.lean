/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
# A Doob–Dynkin lemma for `ℝ≥0∞`-valued functions
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

section DoobDynkin

variable {α β : Type*} {mβ : MeasurableSpace β}

/-- **Doob–Dynkin** for `ℝ≥0∞`-valued functions: a function measurable for the σ-algebra
`mβ.comap f` is a measurable function of `f`.
Intended home: `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`. -/
theorem _root_.Measurable.exists_eq_comp_of_comap {f : α → β} {g : α → ℝ≥0∞}
    (hg : Measurable[mβ.comap f] g) : ∃ g' : β → ℝ≥0∞, Measurable g' ∧ g = g' ∘ f := by
  let _ : MeasurableSpace α := mβ.comap f
  refine Measurable.ennreal_induction
    (motive := fun g : α → ℝ≥0∞ ↦ ∃ g' : β → ℝ≥0∞, Measurable g' ∧ g = g' ∘ f) ?_ ?_ ?_ hg
  · intro c s hs
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
    refine ⟨t.indicator fun _ ↦ c, measurable_const.indicator ht, ?_⟩
    ext x
    by_cases hx : f x ∈ t <;> simp [hx]
  · rintro g₁ g₂ - - - ⟨g₁', h₁, rfl⟩ ⟨g₂', h₂, rfl⟩
    exact ⟨g₁' + g₂', h₁.add h₂, rfl⟩
  · rintro gs - - h
    choose g' hg' hgs using h
    refine ⟨fun y ↦ ⨆ n, g' n y, Measurable.iSup hg', ?_⟩
    ext x
    simp [hgs]

end DoobDynkin

end MeasureTheory

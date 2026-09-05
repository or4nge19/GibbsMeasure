/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiWithDensity

/-!
# Measure-preserving maps and pushforwards

If `Ψ` intertwines `f` and `g`, in the sense that `g ∘ Ψ = Ψ ∘ f`, and `f` is measure preserving
from `μ` to `ν`, then `g` is measure preserving from `μ.map Ψ` to `ν.map Ψ'`.  This is how a
symmetry of a random field is transported to a coarse-grained or re-indexed copy of the field.

A measure-preserving map for `μ` also preserves `μ.withDensity ρ` when the density `ρ` is
invariant under it (`MeasurePreserving.withDensity_of_comp_eq`).
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.MeasurePreserving

variable {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace α']
  [MeasurableSpace β'] {μ : Measure α} {ν : Measure β}

/-- A measure-preserving map is pushed forward along maps intertwining it. -/
theorem map_of_comp_eq {f : α → β} (hf : MeasurePreserving f μ ν) {Ψ : α → α'} {Ψ' : β → β'}
    (hΨ : Measurable Ψ) (hΨ' : Measurable Ψ') {g : α' → β'} (hg : Measurable g)
    (h : g ∘ Ψ = Ψ' ∘ f) : MeasurePreserving g (μ.map Ψ) (ν.map Ψ') :=
  ⟨hg, by rw [Measure.map_map hg hΨ, h, ← Measure.map_map hΨ' hf.measurable, hf.map_eq]⟩

/-- A measure-preserving map preserves a density-modified measure when it leaves the density
invariant. -/
theorem withDensity_of_comp_eq {f : α → α} (hf : MeasurePreserving f μ μ) {ρ : α → ℝ≥0∞}
    (hρ : Measurable ρ) (h : ∀ x, ρ (f x) = ρ x) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) :=
  ⟨hf.measurable, by
    have := map_withDensity_comp μ hf.measurable hρ
    simp only [h, hf.map_eq] at this
    exact this⟩

end MeasureTheory.MeasurePreserving

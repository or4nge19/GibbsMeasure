/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Coordinatewise maps of product spaces

`Pi.map f : (∀ i, α i) → ∀ i, β i` applies a map `f i` in each coordinate. It is measurable when
each `f i` is, and it is a measurable embedding when each `f i` is and the index type is
countable: the range `∀ i, range (f i)` is then a measurable box. The countability cannot be
dropped in the embedding statement, since the range of `Pi.map f` is an uncountable intersection
of coordinate conditions otherwise.

Intended home: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`, next to
`MeasurableEmbedding.prodMap`.
-/

@[expose] public section

open Set

variable {ι : Type*} {α β : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  {f : ∀ i, α i → β i}

/-- A coordinatewise measurable map of product spaces is measurable. -/
theorem Measurable.piMap (hf : ∀ i, Measurable (f i)) : Measurable (Pi.map f) :=
  measurable_pi_lambda _ fun i ↦ (hf i).comp (measurable_pi_apply i)

/-- The pullback of the product σ-algebra along a coordinatewise map is the product of the
pullbacks. -/
theorem MeasurableSpace.comap_piMap (f : ∀ i, α i → β i) :
    MeasurableSpace.comap (Pi.map f) MeasurableSpace.pi =
      ⨆ i, MeasurableSpace.comap (fun x : ∀ i, α i ↦ x i)
        (MeasurableSpace.comap (f i) inferInstance) := by
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- `Pi.map` of a countable family of measurable embeddings is a measurable embedding. -/
theorem MeasurableEmbedding.piMap [Countable ι] (hf : ∀ i, MeasurableEmbedding (f i)) :
    MeasurableEmbedding (Pi.map f) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨Function.Injective.piMap fun i ↦ (hf i).injective, ?_, ?_⟩
  · rw [MeasurableSpace.comap_piMap]
    simp only [(hf _).comap_eq]
    rfl
  · rw [range_piMap]
    exact MeasurableSet.univ_pi fun i ↦ (hf i).measurableSet_range

end

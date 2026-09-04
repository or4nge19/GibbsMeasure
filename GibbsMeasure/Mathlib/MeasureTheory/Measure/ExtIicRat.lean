/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

/-!
# Probability measures are determined by the rational values of their CDF

`MeasureTheory.Measure.ext_of_forall_measure_Iic_rat`: two probability measures on `ℝ` agreeing
on the half-lines `Iic q`, `q` rational, are equal — the rational half-lines are a countable
π-system generating the Borel σ-algebra (`Real.borel_eq_generateFrom_Iic_rat`).

`MeasureTheory.Measure.ext_of_forall_measure_preimage_embeddingReal_Iic`: the same on a standard
Borel space `X`, through the Borel embedding `embeddingReal X : X → ℝ`. This is the pointwise
counterpart of `ProbabilityTheory.kernelOfMeasurableRat_eq`: a probability measure on `X` is
determined by the countably many numbers `μ (e⁻¹ (Iic q))`, `q : ℚ`.

Intended home: `Mathlib/MeasureTheory/Constructions/Polish/EmbeddingReal.lean`.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

/-- Two probability measures on `ℝ` which agree on the half-lines `Iic q`, `q` rational, are
equal. -/
theorem ext_of_forall_measure_Iic_rat {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ q : ℚ, μ (Iic (q : ℝ)) = ν (Iic (q : ℝ))) : μ = ν := by
  refine ext_of_generate_finite (⋃ q : ℚ, {Iic (q : ℝ)}) ?_ Real.isPiSystem_Iic_rat ?_ (by simp)
  · rw [← Real.borel_eq_generateFrom_Iic_rat]
    exact BorelSpace.measurable_eq
  · intro s hs
    simp only [mem_iUnion, mem_singleton_iff] at hs
    obtain ⟨q, rfl⟩ := hs
    exact h q

/-- Two probability measures on a standard Borel space which agree on the half-lines
`e⁻¹ (Iic q)`, `q` rational, of the Borel embedding `e = embeddingReal X`, are equal. -/
theorem ext_of_forall_measure_preimage_embeddingReal_Iic {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ q : ℚ, μ (embeddingReal X ⁻¹' Iic (q : ℝ)) = ν (embeddingReal X ⁻¹' Iic (q : ℝ))) :
    μ = ν := by
  have he := measurableEmbedding_embeddingReal X
  have hmap : μ.map (embeddingReal X) = ν.map (embeddingReal X) := by
    have : IsProbabilityMeasure (μ.map (embeddingReal X)) :=
      isProbabilityMeasure_map he.measurable.aemeasurable
    have : IsProbabilityMeasure (ν.map (embeddingReal X)) :=
      isProbabilityMeasure_map he.measurable.aemeasurable
    refine ext_of_forall_measure_Iic_rat fun q ↦ ?_
    rw [map_apply he.measurable measurableSet_Iic, map_apply he.measurable measurableSet_Iic]
    exact h q
  rw [← he.comap_map μ, ← he.comap_map ν, hmap]

end MeasureTheory.Measure

end

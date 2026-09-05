/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithSetwiseTopology
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.Metrizable.Basic

/-!
# Probability measures with the setwise topology as a subspace of a locally convex space

`WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)` carries the coarsest topology making `μ ↦ μ A`
continuous for `A ∈ 𝒞`. This file realises that space as a *subspace of a topological vector
space*: the evaluation map

`evalReal 𝒞 : μ ↦ fun A : 𝒞 ↦ μ.real A`

into the product `𝒞 → ℝ` is a topological embedding as soon as `𝒞` separates probability measures.
The product `𝒞 → ℝ` is a locally convex Hausdorff topological vector space (and, for countable
`𝒞`, a Polish space with its Borel σ-algebra), so all of convex analysis — Hahn-Banach separation,
barycentres, Choquet theory — becomes available for sets of probability measures.

This is the device behind Georgii's Comment (4.A10) and Step 3 of the proof of his Theorem
(15.45): a countable *core* `𝒞` of the σ-algebra turns the space of probability measures into a
compact metrizable set, and it is embedded here in `𝒞 → ℝ` so that convex analysis applies.

## Main statements

* `MeasureTheory.WithSetwiseTopology.isInducing_evalReal`: the setwise topology is exactly the
  topology induced from `𝒞 → ℝ`. (The `ℝ≥0∞`-valued evaluation `evalProb` is the composition of
  `evalReal` with the continuous `ENNReal.ofReal`, which gives one inclusion of neighbourhood
  filters; the other is continuity of `evalReal`.)
* `MeasureTheory.WithSetwiseTopology.isEmbedding_evalReal`: it is a topological embedding when `𝒞`
  separates probability measures.
* `MeasureTheory.WithSetwiseTopology.convex_image_evalReal`: the image of a set of probability
  measures stable under mixtures is convex.
* `MeasureTheory.WithSetwiseTopology.isCompact_image_evalReal`: the image of a compact set is
  compact.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace MeasureTheory

namespace WithSetwiseTopology

variable {Ω : Type*} [MeasurableSpace Ω] {𝒞 : Set (Set Ω)}

/-- Evaluation of probability measures on `𝒞`, with values in the real vector space `𝒞 → ℝ`.
This is the embedding through which convex analysis is applied to sets of probability measures. -/
def evalReal (𝒞 : Set (Set Ω)) : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) → (𝒞 → ℝ) :=
  fun μ A ↦ (μ.toMeasure : Measure Ω).real A.1

@[simp] lemma evalReal_apply (μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) (A : 𝒞) :
    evalReal 𝒞 μ A = (μ.toMeasure : Measure Ω).real A.1 := rfl

lemma continuous_evalReal : Continuous (evalReal (Ω := Ω) 𝒞) :=
  continuous_pi fun A ↦ continuous_apply_real A.2

/-- The `ℝ≥0∞`-valued evaluation is the real-valued one followed by `ENNReal.ofReal`. -/
lemma evalProb_eq_ofReal_comp_evalReal :
    evalProb (Ω := Ω) 𝒞 = (fun v : 𝒞 → ℝ ↦ fun A ↦ ENNReal.ofReal (v A)) ∘ evalReal 𝒞 := by
  funext μ A
  exact (ENNReal.ofReal_toReal (measure_ne_top (μ.toMeasure : Measure Ω) A.1)).symm

/-- **The setwise topology is induced from the product `𝒞 → ℝ`.** -/
lemma isInducing_evalReal : Topology.IsInducing (evalReal (Ω := Ω) 𝒞) := by
  refine Topology.isInducing_iff_nhds.2 fun μ ↦ le_antisymm ?_ ?_
  · exact Filter.map_le_iff_le_comap.1 continuous_evalReal.continuousAt
  · have hcont : Continuous (fun v : 𝒞 → ℝ ↦ fun A ↦ ENNReal.ofReal (v A)) :=
      continuous_pi fun A ↦ ENNReal.continuous_ofReal.comp (continuous_apply A)
    calc comap (evalReal (Ω := Ω) 𝒞) (𝓝 (evalReal 𝒞 μ))
        ≤ comap (evalReal (Ω := Ω) 𝒞)
            (comap (fun v : 𝒞 → ℝ ↦ fun A ↦ ENNReal.ofReal (v A))
              (𝓝 (fun A ↦ ENNReal.ofReal (evalReal 𝒞 μ A)))) :=
          comap_mono (Filter.map_le_iff_le_comap.1 hcont.continuousAt)
      _ = comap (evalProb (Ω := Ω) 𝒞) (𝓝 (evalProb 𝒞 μ)) := by
          rw [comap_comap, evalProb_eq_ofReal_comp_evalReal]; rfl
      _ = 𝓝 μ := (isInducing_evalProb.nhds_eq_comap μ).symm

lemma injective_evalReal (h𝒞 : SeparatesOn 𝒞 (fun μ ↦ IsProbabilityMeasure μ)) :
    Function.Injective (evalReal (Ω := Ω) 𝒞) := by
  rintro ⟨μ⟩ ⟨ν⟩ h
  have hreal : ∀ A ∈ 𝒞, (μ : Measure Ω) A = (ν : Measure Ω) A := by
    intro A hA
    have := congrFun h ⟨A, hA⟩
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ : Measure Ω) A),
      ← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure Ω) A)]
    exact congrArg ENNReal.ofReal this
  simp [ProbabilityMeasure.toMeasure_injective (h𝒞 μ.2 ν.2 hreal)]

/-- **The evaluation embedding.** When `𝒞` separates probability measures, the space of
probability measures with the setwise topology is a topological subspace of the locally convex
space `𝒞 → ℝ`. -/
lemma isEmbedding_evalReal (h𝒞 : SeparatesOn 𝒞 (fun μ ↦ IsProbabilityMeasure μ)) :
    Topology.IsEmbedding (evalReal (Ω := Ω) 𝒞) :=
  ⟨isInducing_evalReal, injective_evalReal h𝒞⟩

/-- The image of a compact set of probability measures is compact. -/
lemma isCompact_image_evalReal {P : Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω))}
    (hP : IsCompact P) : IsCompact (evalReal 𝒞 '' P) :=
  hP.image continuous_evalReal

/-- Evaluation turns a mixture of measures into the corresponding convex combination in
`𝒞 → ℝ`. -/
lemma evalReal_of_toMeasure_eq {μ ν ρ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hρ : (ρ.toMeasure : Measure Ω)
      = ENNReal.ofReal a • (μ.toMeasure : Measure Ω)
        + ENNReal.ofReal b • (ν.toMeasure : Measure Ω)) :
    evalReal 𝒞 ρ = a • evalReal 𝒞 μ + b • evalReal 𝒞 ν := by
  refine funext fun A ↦ ?_
  simp only [evalReal_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hρ, measureReal_def,
    Measure.coe_add, Measure.coe_smul]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

/-- **Convexity of the image.** If a set `P` of probability measures is stable under mixtures,
its image in `𝒞 → ℝ` is convex. The hypothesis is phrased on the underlying measures, since
`MeasureTheory.ProbabilityMeasure` carries no convex structure. -/
lemma convex_image_evalReal {P : Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω))}
    (hP : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure Ω)
        = ENNReal.ofReal a • (μ.toMeasure : Measure Ω)
          + ENNReal.ofReal b • (ν.toMeasure : Measure Ω)) :
    Convex ℝ (evalReal 𝒞 '' P) := by
  rintro _ ⟨μ, hμ, rfl⟩ _ ⟨ν, hν, rfl⟩ a b ha hb hab
  obtain ⟨ρ, hρP, hρ⟩ := hP μ hμ ν hν a b ha hb hab
  exact ⟨ρ, hρP, evalReal_of_toMeasure_eq ha hb hρ⟩

end WithSetwiseTopology

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import GibbsMeasure.Mathlib.Analysis.Convex.Extreme
public import GibbsMeasure.Mathlib.Analysis.Convex.ExtremeGDelta

/-!
# Weakly closed sets of probability measures: invariance and extreme points

* `MeasureTheory.ProbabilityMeasure.isClosed_setOf_measurePreserving`: the probability measures
  preserved by a continuous map form a closed set for the topology of convergence in distribution.
* `MeasureTheory.ProbabilityMeasure.isGδ_preimage_extremePoints`: on a compact metrizable space,
  the extreme points (with `ℝ≥0∞` scalars, in `Measure Ω`) of a weakly closed set of probability
  measures form a `Gδ` set of `ProbabilityMeasure Ω`. This is the classical Choquet-theory fact that
  the extreme boundary of a compact metrizable convex set is a `Gδ`
  (`IsCompact.isGδ_extremePoints`), transported along the embedding
  `ProbabilityMeasure Ω → FiniteMeasure Ω` into a topological `ℝ≥0`-module and along the injective
  `ℝ≥0`-linear map `FiniteMeasure Ω → Measure Ω`.
-/

@[expose] public section

open Set Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MeasureTheory.ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

/-- The probability measures preserved by a continuous map form a closed set for the topology of
convergence in distribution. (`HasOuterApproxClosed Ω`, automatic for pseudo-metrizable `Ω`, is
what makes `ProbabilityMeasure Ω` Hausdorff in Mathlib.) -/
theorem isClosed_setOf_measurePreserving [HasOuterApproxClosed Ω] [BorelSpace Ω] {f : Ω → Ω}
    (hf : Continuous f) : IsClosed {μ : ProbabilityMeasure Ω | MeasurePreserving f μ μ} := by
  convert isClosed_eq (continuous_map hf) continuous_id using 1
  ext μ
  simp only [mem_ofPred_eq, id_eq]
  rw [← toMeasure_injective.eq_iff, toMeasure_map]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨hf.measurable, h⟩⟩

/-- **The extreme points of a weakly closed set of probability measures on a compact metrizable
space form a `Gδ`.** Let `K` be a set of probability measures on `Ω` whose trace on
`ProbabilityMeasure Ω` is closed for the topology of convergence in distribution. Then the extreme
points of `K` (with `ℝ≥0∞` scalars, in `Measure Ω`) form a `Gδ` subset of `ProbabilityMeasure Ω`.
Since `ProbabilityMeasure Ω` is compact and metrizable, this is `IsCompact.isGδ_extremePoints`
transported along the embedding `toFiniteMeasure` into the topological `ℝ≥0`-module
`FiniteMeasure Ω` and along the injective `ℝ≥0`-linear map `FiniteMeasure Ω → Measure Ω`. -/
theorem isGδ_preimage_extremePoints [CompactSpace Ω] [MetrizableSpace Ω] [BorelSpace Ω]
    {K : Set (Measure Ω)} (hK : IsClosed ((↑) ⁻¹' K : Set (ProbabilityMeasure Ω)))
    (hKp : ∀ μ ∈ K, IsProbabilityMeasure μ) :
    IsGδ ((↑) ⁻¹' (K.extremePoints ℝ≥0∞) : Set (ProbabilityMeasure Ω)) := by
  set P : Set (ProbabilityMeasure Ω) := (↑) ⁻¹' K with hP
  have hKP : ((↑) : ProbabilityMeasure Ω → Measure Ω) '' P = K :=
    image_preimage_eq_of_subset fun μ hμ ↦ ⟨⟨μ, hKp μ hμ⟩, rfl⟩
  have e := toFiniteMeasure_isEmbedding Ω
  set K' : Set (FiniteMeasure Ω) := toFiniteMeasure '' P with hK'
  have hK'c : IsCompact K' := hK.isCompact.image e.continuous
  have : PseudoMetrizableSpace K' := (e.homeomorphImage P).symm.isInducing.pseudoMetrizableSpace
  have hσ : IsSigmaCompact (P \ toFiniteMeasure ⁻¹' (K'.extremePoints ℝ≥0)) := by
    rw [e.isSigmaCompact_iff, image_sdiff_preimage]
    exact hK'c.isSigmaCompact_diff_extremePoints
  have hid : toFiniteMeasure ⁻¹' (K'.extremePoints ℝ≥0) =
      ((↑) ⁻¹' (K.extremePoints ℝ≥0∞) : Set (ProbabilityMeasure Ω)) := by
    let L : FiniteMeasure Ω →ₗ[ℝ≥0] Measure Ω :=
      { FiniteMeasure.toMeasureAddMonoidHom with map_smul' := FiniteMeasure.toMeasure_smul }
    have hL : Function.Injective L := FiniteMeasure.toMeasure_injective
    have hLK : L '' K' = K := by
      rw [hK', image_image, ← hKP]
      rfl
    ext μ
    simp only [mem_preimage]
    rw [← hL.mem_set_image, LinearMapClass.image_extremePoints L hL, hLK, extremePoints_ennreal]
    exact Iff.rfl
  rw [← hid]
  have hsub : toFiniteMeasure ⁻¹' (K'.extremePoints ℝ≥0) ⊆ P := fun μ hμ ↦
    e.injective.mem_set_image.1 (extremePoints_subset hμ)
  rw [← sdiff_sdiff_cancel_left hsub]
  exact hK.isGδ_diff hσ

end MeasureTheory.ProbabilityMeasure

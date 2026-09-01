/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.UniformAverage
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Specification.Transformation

/-!
# Averaged Gibbs distributions

Georgii Proposition (5.18): every cluster point of the averages
`μ_α = |R_α|⁻¹ ∑_{Λ ∈ R_α} ν γ_Λ` is `τ`-invariant when `γ` and `ν` are and the index families
`R_α` are asymptotically invariant. The lattice instance (cubes on `ℤ^d`, Georgii (5.20)(1)) is
in `GibbsMeasure/Model/ShiftAverage.lean`.

`Specification.isGibbsMeasure_bind` is the continuous companion of these finite averages: a
mixture `∫ w(dx) μ^x` of a measurable family of Gibbs measures is a Gibbs measure.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology symmDiff

noncomputable section

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (5.18).** The average `|R|⁻¹ ∑_{Λ ∈ R} ν γ_Λ` of the finite-volume Gibbs
distributions of `ν` over a finite family `R` of volumes: `MeasureTheory.uniformAverage` of the
family `Λ ↦ ν γ_Λ`. -/
abbrev average (γ : Specification S E) (ν : Measure (S → E)) (R : Finset (Finset S)) :
    Measure (S → E) :=
  MeasureTheory.uniformAverage (fun Λ ↦ ν.bind (γ Λ)) R

lemma average_apply (γ : Specification S E) (ν : Measure (S → E)) (R : Finset (Finset S))
    (A : Set (S → E)) :
    γ.average ν R A = (R.card : ℝ≥0∞)⁻¹ * ∑ Λ ∈ R, ν.bind (γ Λ) A :=
  MeasureTheory.uniformAverage_apply _ R A

/-- The average of Georgii (5.18) over a nonempty family is a probability measure. -/
lemma isProbabilityMeasure_average (γ : Specification S E) (ν : Measure (S → E))
    [IsProbabilityMeasure ν] {R : Finset (Finset S)} (hR : R.Nonempty) :
    IsProbabilityMeasure (γ.average ν R) :=
  MeasureTheory.isProbabilityMeasure_uniformAverage _
    (fun Λ ↦ γ.isProbabilityMeasure_bind Λ ν) hR

/-- Real-valued form of `Specification.average_apply`. -/
lemma average_real_apply (γ : Specification S E) (ν : Measure (S → E))
    [IsProbabilityMeasure ν] (R : Finset (Finset S)) (A : Set (S → E)) :
    (γ.average ν R).real A = (R.card : ℝ)⁻¹ * ∑ Λ ∈ R, (ν.bind (γ Λ)).real A :=
  MeasureTheory.uniformAverage_real_apply _ (fun Λ ↦ γ.isProbabilityMeasure_bind Λ ν) R A

/-! ### Georgii (5.18): transport of averages under symmetries -/

variable {γ : Specification S E} {ν : Measure (S → E)}

/-- Georgii (5.18) via (5.5): for `τ`-invariant `γ` and `ν`, the `τ`-image of the average over `R`
is the average over `τ_* R = {τ_* Λ : Λ ∈ R}`. -/
lemma map_average {τ : Transformation S E} (hγ : IsInvariant τ γ)
    (hν : MeasurePreserving τ.toFun ν ν) (R : Finset (Finset S)) :
    (γ.average ν R).map τ.toFun =
      γ.average ν (R.map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding) := by
  have hterm : ∀ Λ : Finset S,
      (ν.bind (γ Λ)).map τ.toFun = ν.bind (γ (Λ.map τ.sites.toEmbedding)) := by
    intro Λ
    rw [Measure.map_bind (γ.measurable_kernel_toMeasure Λ) τ.measurable_toFun]
    have h : (fun ω ↦ (γ Λ ω).map τ.toFun) = ⇑(γ (Λ.map τ.sites.toEmbedding)) ∘ τ.toFun :=
      funext fun ω ↦ isInvariant_iff.1 hγ Λ ω
    rw [h, ← Measure.bind_map τ.measurable_toFun (γ.measurable_kernel_toMeasure _), hν.map_eq]
  unfold average MeasureTheory.uniformAverage
  rw [Measure.map_smul, Measure.map_finset_sum τ.measurable_toFun.aemeasurable, Finset.card_map,
    Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun Λ _ ↦ ?_
  rw [hterm]
  rfl

/-! ### Georgii (5.18): total-variation estimate between averages -/

variable [DecidableEq S]

/-- Two averages of Georgii (5.18) over nonempty families `R`, `R'` differ on every event by at
most `|R ∆ R'| / |R| + | |R'| / |R| - 1 |`. -/
lemma abs_average_real_sub_le [IsProbabilityMeasure ν] {R R' : Finset (Finset S)}
    (hR : R.Nonempty) (hR' : R'.Nonempty) (A : Set (S → E)) :
    |(γ.average ν R).real A - (γ.average ν R').real A| ≤
      ((R ∆ R').card : ℝ) / R.card + |(R'.card : ℝ) / R.card - 1| :=
  MeasureTheory.abs_uniformAverage_real_sub_le _
    (fun Λ ↦ γ.isProbabilityMeasure_bind Λ ν) hR hR' A

/-- Georgii (5.18), the estimate `|μ_α(f ∘ τ) - μ_α(f)| ≤ ‖f‖ |τ_* R ∆ R| / |R|` for events:
averages over families of the same cardinality differ by at most `|R ∆ R'| / |R|`. -/
lemma abs_average_real_sub_le_of_card_eq [IsProbabilityMeasure ν] {R R' : Finset (Finset S)}
    (hR : R.Nonempty) (hcard : R.card = R'.card) (A : Set (S → E)) :
    |(γ.average ν R).real A - (γ.average ν R').real A| ≤ ((R ∆ R').card : ℝ) / R.card :=
  MeasureTheory.abs_uniformAverage_real_sub_le_of_card_eq _
    (fun Λ ↦ γ.isProbabilityMeasure_bind Λ ν) hR hcard A

/-- Georgii (5.20)(1), the estimate for the modified sequence: the averages over `R' ⊆ R` differ
from those over `R` by at most `2 (1 - |R'| / |R|)`. -/
lemma abs_average_real_sub_le_of_subset [IsProbabilityMeasure ν] {R R' : Finset (Finset S)}
    (hR' : R'.Nonempty) (hsub : R' ⊆ R) (A : Set (S → E)) :
    |(γ.average ν R).real A - (γ.average ν R').real A| ≤ 2 * (1 - (R'.card : ℝ) / R.card) :=
  MeasureTheory.abs_uniformAverage_real_sub_le_of_subset _
    (fun Λ ↦ γ.isProbabilityMeasure_bind Λ ν) hR' hsub A

end Specification

namespace Specification

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {ν : Measure (S → E)}

/-- Georgii (4.18)/(5.20)(1): the average over a family `R` of volumes all containing `Λ` is
fixed by `γ_Λ`, i.e. `μ_α γ_Λ = μ_α` when `Λ ⊆ ⋂ R`, by consistency. -/
lemma bind_average_of_subset {Λ : Finset S} {R : Finset (Finset S)} (h : ∀ Λ' ∈ R, Λ ⊆ Λ') :
    (γ.average ν R).bind (γ Λ) = γ.average ν R := by
  unfold average MeasureTheory.uniformAverage
  rw [Measure.bind_smul, Measure.bind_finset_sum _ _ _ (γ.measurable_kernel_toMeasure Λ)]
  congr 1
  exact Finset.sum_congr rfl fun Λ' hΛ' ↦ γ.bind_bind_of_subset (h Λ' hΛ') ν

/-! ### Mixtures of Gibbs measures

The continuous analogue of the finite averages above: a measurable family `x ↦ μ^x` of Gibbs
measures and a probability weight `w` on the parameter space combine into the mixture
`∫ w(dx) μ^x = w.bind μ`, which is again Gibbs.
-/

variable {X : Type*} [MeasurableSpace X] {w : Measure X} {μ : X → Measure (S → E)}

/-- If `μ^x γ_Λ = μ^x` for `w`-almost every parameter `x`, the mixture `∫ w(dx) μ^x` is fixed by
`γ_Λ` as well. No finiteness of `w` or of the `μ^x` is needed. -/
lemma bind_bind_of_ae_bind_eq_self (γ : Specification S E) (hmeas : AEMeasurable μ w)
    (Λ : Finset S) (h : ∀ᵐ x ∂w, (μ x).bind (γ Λ) = μ x) :
    (w.bind μ).bind (γ Λ) = w.bind μ := by
  have hg : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) (w.bind μ) :=
    ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  rw [Measure.bind_bind hmeas hg]
  exact Measure.bind_congr_right h

/-- **A mixture of Gibbs measures is a Gibbs measure**: if `x ↦ μ^x` is a measurable family of
Gibbs measures for `γ` and `w` is a probability weight on the parameter space, then
`∫ w(dx) μ^x ∈ 𝒢(γ)`. This is the parametrised form of the convexity of `𝒢(γ)`. -/
theorem isGibbsMeasure_bind (γ : Specification S E) [IsProbabilityMeasure w]
    (hmeas : AEMeasurable μ w) (hprob : ∀ᵐ x ∂w, IsProbabilityMeasure (μ x))
    (hgibbs : ∀ᵐ x ∂w, γ.IsGibbsMeasure (μ x)) : γ.IsGibbsMeasure (w.bind μ) := by
  have : IsProbabilityMeasure (w.bind μ) := MeasureTheory.isProbabilityMeasure_bind hmeas hprob
  rw [isGibbsMeasure_iff_forall_bind_eq_of_prob]
  refine fun Λ ↦ γ.bind_bind_of_ae_bind_eq_self hmeas Λ ?_
  filter_upwards [hprob, hgibbs] with x hxprob hxgibbs
  exact (isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hxgibbs) Λ

end Specification

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S]

/-! ### Georgii Proposition (5.18) -/

/-- **Georgii Proposition (5.18)** (constant `τ`, `γ`, `ν`): if `|τ_* R_n ∆ R_n| / |R_n| → 0`, every
cluster point of the averages `μ_n = |R_n|⁻¹ ∑_{Λ ∈ R_n} ν γ_Λ` is `τ`-invariant. -/
theorem measurePreserving_of_mapClusterPt_average {τ : Transformation S E}
    {γ : Specification S E} {ν : Measure (S → E)} [IsProbabilityMeasure ν]
    (hγ : Specification.IsInvariant τ γ) (hν : MeasurePreserving τ.toFun ν ν)
    {R : ℕ → Finset (Finset S)} (hR : ∀ n, (R n).Nonempty)
    (hlim : Tendsto (fun n ↦
      (((R n).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding ∆ R n).card : ℝ) /
        (R n).card) atTop (𝓝 0))
    {μs : ℕ → ProbabilityMeasure (S → E)}
    (hμs : ∀ n, (μs n : Measure (S → E)) = γ.average ν (R n))
    {μ : ProbabilityMeasure (S → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
      fun n ↦ WithSetwiseTopology.ofMeasure (μs n)) :
    MeasurePreserving τ.toFun μ μ := by
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hμ
  refine ⟨τ.measurable_toFun, ?_⟩
  have hmap : IsProbabilityMeasure ((μ : Measure (S → E)).map τ.toFun) :=
    Measure.isProbabilityMeasure_map τ.measurable_toFun.aemeasurable
  refine separatesOn_localEvents hmap inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  rw [Measure.map_apply τ.measurable_toFun hAm]
  -- evaluations on the local events `A` and `τ⁻¹ A` converge along the ultrafilter `U`
  have h1 : Tendsto (fun n ↦ ((μs n : Measure (S → E)) A).toReal) U
      (𝓝 (((μ : Measure (S → E)) A).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hU A hA)
  have h2 : Tendsto (fun n ↦ ((μs n : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal) U
      (𝓝 (((μ : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hU _ (τ.preimage_mem_localEvents hA))
  -- `μ_n(τ⁻¹ A)` is the average over `τ_* R_n` evaluated at `A` (by `map_average`)
  have hn : ∀ n, ((μs n : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal =
      (γ.average ν ((R n).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding)).real A := by
    intro n
    rw [measureReal_def, ← Specification.map_average hγ hν,
      Measure.map_apply τ.measurable_toFun hAm, hμs]
  -- the difference `μ_n(τ⁻¹ A) - μ_n(A)` tends to `0`, by the estimate of (5.18)
  have hdiff : Tendsto (fun n ↦ ((μs n : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal -
      ((μs n : Measure (S → E)) A).toReal) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) hlim
    rw [Real.norm_eq_abs, hn n, ← measureReal_def, hμs n]
    have h := Specification.abs_average_real_sub_le_of_card_eq (γ := γ) (ν := ν)
      (R := (R n).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding) (R' := R n)
      (hR n).map (Finset.card_map _) A
    rwa [Finset.card_map] at h
  have h3 := tendsto_nhds_unique (h2.sub h1) (hdiff.mono_left hUle)
  rw [sub_eq_zero] at h3
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

/-! ### Cluster points of two nets that agree asymptotically on local events -/


lemma mapClusterPt_of_tendsto_real_sub {ι : Type*} {l : Filter ι}
    {μs μs' : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun i ↦ WithSetwiseTopology.ofMeasure (μs i))
    (h : ∀ A ∈ localEvents S E, Tendsto
      (fun i ↦ (μs i : Measure (S → E)).real A - (μs' i : Measure (S → E)).real A) l (𝓝 0)) :
    MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun i ↦ WithSetwiseTopology.ofMeasure (μs' i) := by
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hμ
  refine mapClusterPt_iff_ultrafilter.2 ⟨U, hUle, ?_⟩
  rw [tendsto_withLocalConvergence_iff] at hU ⊢
  intro A hA
  rw [← ENNReal.tendsto_toReal_iff (fun i ↦ measure_ne_top _ _) (measure_ne_top _ _)]
  have h1 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hU A hA)
  have h2 := h1.sub ((h A hA).mono_left hUle)
  simpa [measureReal_def, sub_sub_cancel, Function.comp_def] using h2

end MeasureTheory.GibbsMeasure

end

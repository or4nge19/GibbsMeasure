/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.DobrushinUniqueness
public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Topology.ClusterPoints

/-!
# Georgii (8.23)(ii): local convergence of the finite-volume Gibbs distributions

Under Dobrushin's condition of weak dependence, the finite-volume Gibbs distributions
`γ_Δ(·|η)` do not merely have a cluster point in the topology of local convergence — the whole
net *converges* to the unique Gibbs measure, from every boundary condition `η`. This is
Georgii's Theorem (8.23)(ii) in the case `V = S`, together with the speed-of-convergence
estimate `|γ_Δ(A|η) − μ(A)| ≤ ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_{ij}(γ)` (Georgii's comment following
(8.24)), uniform in `η`.

## Main declarations

* `MeasureTheory.GibbsMeasure.Dobrushin.tendsto_finiteVolumeDistributions_of_isDobrushin`:
  Georgii (8.23)(ii) for `V = S` — the net `Δ ↦ γ_Δ(·|η)` converges locally to the Gibbs
  measure, for every boundary condition `η`.
* `MeasureTheory.GibbsMeasure.Dobrushin.exists_mem_GP_forall_tendsto_of_isDobrushin`:
  the packaged form — Dobrushin's condition *constructs* the unique Gibbs measure as the local
  limit of the finite-volume distributions.
* `MeasureTheory.GibbsMeasure.Dobrushin.measure_le_add_interdepTail_of_mem_GP`,
  `le_measure_add_interdepTail_of_mem_GP`,
  `ofReal_abs_toReal_sub_le_interdepTail_of_mem_GP`: the quantitative estimate of the speed of
  this convergence, uniform in the boundary condition.

The ingredients — the Cauchy estimate `measure_le_add_interdepTail`, the tail bound
`tendsto_interdepTail`, local equicontinuity, and uniqueness (Georgii (8.7)) — live in
`GibbsMeasure.Specification.DobrushinUniqueness`; the compactness input
(`exists_tendsto_of_locallyEquicontinuous`, Georgii (4.9)) in
`GibbsMeasure.Topology.ClusterPoints`.
-/

@[expose] public section

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Dobrushin

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}

/-- **Georgii (8.23)(ii)** (the case `V = S`): under Dobrushin's condition the net of
finite-volume Gibbs distributions `γ_Δ(·|η)` converges, in the topology of local convergence,
to any — hence the unique — Gibbs measure of `γ`, from *every* boundary condition `η`. -/
theorem tendsto_finiteVolumeDistributions_of_isDobrushin [StandardBorelSpace E]
    (hd : IsDobrushin γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : μ ∈ GP (S := S) (E := E) γ) (η : S → E) :
    Tendsto (fun Δ : Finset S ↦
        (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ η Δ) :
          WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨ν, hν⟩ := exists_tendsto_of_locallyEquicontinuous
    (μs := fun Δ : Finset S ↦
      (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ η Δ) :
        WithLocalConvergence S E)) U hU
    (locallyEquicontinuous_finiteVolumeDistributions_of_isDobrushin hd.isQuasilocal hd η)
  have hltl : IsLocalThermodynamicLimit γ η ν.toMeasure :=
    mapClusterPt_iff_ultrafilter.2 ⟨U, hU, hν⟩
  have hνμ : ν.toMeasure = μ :=
    subsingleton_GP_of_isDobrushin hd.isQuasilocal hd (hltl.mem_GP hd.isQuasilocal) hμ
  have hνeq : ν = WithSetwiseTopology.ofMeasure μ := by rw [← hνμ]
  exact hνeq ▸ hν

/-- **Georgii (8.23)**: over a standard Borel state space Dobrushin's condition *constructs* the
Gibbs measure: there is exactly one, and it is the local limit of the finite-volume Gibbs
distributions from every boundary condition. -/
theorem exists_mem_GP_forall_tendsto_of_isDobrushin [Nonempty E] [StandardBorelSpace E]
    (hd : IsDobrushin γ) :
    ∃ μ ∈ GP (S := S) (E := E) γ, ∀ η : S → E,
      Tendsto (fun Δ : Finset S ↦
          (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ η Δ) :
            WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  obtain ⟨μ, hμ⟩ := GP_nonempty_of_isDobrushin hd.isQuasilocal hd
  exact ⟨μ, hμ, tendsto_finiteVolumeDistributions_of_isDobrushin hd hμ⟩

/-- **Georgii's comment after (8.24)**, one half: the unique Gibbs measure is approximated by
`γ_Δ(·|η)` with speed `∑_{i ∈ Λ} ∑_{j ∉ Δ} D_{ij}(γ)` on `Λ`-local events, uniformly in `η`:
`μ(A) ≤ γ_Δ(A|η) + ∑_{i ∈ Λ} interdepTail γ Δ i`. -/
theorem measure_le_add_interdepTail_of_mem_GP [DecidableEq S] [StandardBorelSpace E]
    (hd : IsDobrushin γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : μ ∈ GP (S := S) (E := E) γ) (Δ : Finset S) (η : S → E) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    (μ : Measure (S → E)) A ≤ γ Δ η A + ∑ i ∈ Λ, interdepTail γ Δ i := by
  have htend : Tendsto
      (fun Δ' : Finset S ↦
        ((finiteVolumeDistributions γ η Δ' : ProbabilityMeasure (S → E)) : Measure (S → E)) A)
      atTop (𝓝 ((μ : Measure (S → E)) A)) :=
    tendsto_withLocalConvergence_iff.1
      (tendsto_finiteVolumeDistributions_of_isDobrushin hd hμ η) A
      (mem_localEvents_of_cylinderEvents Λ hA)
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_ge_atTop Δ] with Δ' hΔ'
  exact measure_le_add_interdepTail hd.isQuasilocal hd hΔ' η hA

/-- **Georgii's comment after (8.24)**, the other half:
`γ_Δ(A|η) ≤ μ(A) + ∑_{i ∈ Λ} interdepTail γ Δ i` for `Λ`-local events `A`, uniformly in `η`. -/
theorem le_measure_add_interdepTail_of_mem_GP [DecidableEq S] [StandardBorelSpace E]
    (hd : IsDobrushin γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : μ ∈ GP (S := S) (E := E) γ) (Δ : Finset S) (η : S → E) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    γ Δ η A ≤ (μ : Measure (S → E)) A + ∑ i ∈ Λ, interdepTail γ Δ i := by
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have h := measure_le_add_interdepTail_of_mem_GP hd hμ Δ η hA.compl
  rw [prob_compl_eq_one_sub hAm, prob_compl_eq_one_sub hAm] at h
  set a := (μ : Measure (S → E)) A
  set b := γ Δ η A
  set T := ∑ i ∈ Λ, interdepTail γ Δ i
  have ha1 : a ≤ 1 := prob_le_one
  have hb1 : b ≤ 1 := prob_le_one
  have key : (1 : ℝ≥0∞) + b ≤ 1 + (a + T) := by
    calc (1 : ℝ≥0∞) + b = ((1 - a) + a) + b := by rw [tsub_add_cancel_of_le ha1]
      _ ≤ (((1 - b) + T) + a) + b := by gcongr
      _ = ((1 - b) + b) + (a + T) := by ring
      _ = 1 + (a + T) := by rw [tsub_add_cancel_of_le hb1]
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top).1 key

/-- **Georgii's comment after (8.24)**: the estimate of the speed of the convergence
`γ_Δ(·|η) → μ`, uniform in the boundary condition:
`|γ_Δ(A|η) − μ(A)| ≤ ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_{ij}(γ)` for every `Λ`-local event `A`. -/
theorem ofReal_abs_toReal_sub_le_interdepTail_of_mem_GP [DecidableEq S] [StandardBorelSpace E]
    (hd : IsDobrushin γ) {μ : ProbabilityMeasure (S → E)}
    (hμ : μ ∈ GP (S := S) (E := E) γ) (Δ : Finset S) (η : S → E) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    ENNReal.ofReal |(γ Δ η A).toReal - ((μ : Measure (S → E)) A).toReal|
      ≤ ∑ i ∈ Λ, interdepTail γ Δ i := by
  set T := ∑ i ∈ Λ, interdepTail γ Δ i with hTdef
  rcases eq_or_ne T ⊤ with hT | hT
  · simp [hT]
  have h1 : (μ : Measure (S → E)) A ≤ γ Δ η A + T :=
    measure_le_add_interdepTail_of_mem_GP hd hμ Δ η hA
  have h2 : γ Δ η A ≤ (μ : Measure (S → E)) A + T :=
    le_measure_add_interdepTail_of_mem_GP hd hμ Δ η hA
  have hr1 : ((μ : Measure (S → E)) A).toReal ≤ (γ Δ η A).toReal + T.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hT⟩) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hT] at h
  have hr2 : (γ Δ η A).toReal ≤ ((μ : Measure (S → E)) A).toReal + T.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hT⟩) h2
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hT] at h
  calc ENNReal.ofReal |(γ Δ η A).toReal - ((μ : Measure (S → E)) A).toReal|
      ≤ ENNReal.ofReal T.toReal :=
        ENNReal.ofReal_le_ofReal (abs_le.2 ⟨by linarith, by linarith⟩)
    _ = T := ENNReal.ofReal_toReal hT

end MeasureTheory.GibbsMeasure.Dobrushin

end

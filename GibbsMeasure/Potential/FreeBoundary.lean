/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Space
public import GibbsMeasure.Potential.UniformConvergence

/-!
# Free boundary conditions

**Georgii Example (4.20)(1)**. For an absolutely summable potential `Φ ∈ ℬ` and a finite volume
`Δ`, the truncated potential `Φ^Δ` (`Potential.truncation`) suppresses every interaction not
contained in `Δ`. The Hamiltonians of `Φ^Δ` converge to those of `Φ` uniformly in each volume
`Λ`, with explicit bound the tail `∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` of the interaction series, which
vanishes along `Δ ↑ S`. By Georgii (4.19) the Gibbsian specifications `γ^{Φ^Δ}` converge to
`γ^Φ` uniformly in the 𝓛-topology, so by the cluster-point form of (4.17) every cluster point of
the free-boundary net `Δ ↦ ν_Δ γ^{Φ^Δ}_Δ` is a Gibbs measure for `Φ`.

The net is moreover *unconditionally* locally equicontinuous (the density bound (4.14)(1) for
`Φ^Δ` at a fixed volume `Λ` is uniform in `Δ`, because `‖Φ^Δ‖ᵢ ≤ ‖Φ‖ᵢ`), so over a standard
Borel state space cluster points exist: the free-boundary existence theorem.
-/

@[expose] public section


open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} {Δ Λ : Finset S}

/-! ### (C1) The truncated potential `Φ^Δ` -/

open Classical in
/-- **Georgii (4.20)(1).** The truncation `Φ^Δ` of a potential to a finite volume `Δ`:
all interactions of spins in `Δ` with spins outside `Δ` are suppressed. -/
def truncation (Φ : Potential S E) (Δ : Finset S) : Potential S E :=
  fun A η ↦ if A ⊆ Δ then Φ A η else 0

lemma truncation_of_subset {B : Finset S} (h : B ⊆ Δ) : Φ.truncation Δ B = Φ B := by
  funext η; simp [truncation, h]

lemma truncation_of_not_subset {B : Finset S} (h : ¬ B ⊆ Δ) : Φ.truncation Δ B = 0 := by
  funext η; simp [truncation, h]

/-- Truncation preserves the absence of an `∅`-interaction. -/
lemma truncation_empty (h : Φ ∅ = 0) (Δ : Finset S) : Φ.truncation Δ ∅ = 0 := by
  rw [truncation_of_subset (Finset.empty_subset Δ), h]

/-- The truncation of a potential is a potential. -/
instance (Δ : Finset S) [IsPotential Φ] : IsPotential (Φ.truncation Δ) where
  measurable B := by
    by_cases h : B ⊆ Δ
    · rw [truncation_of_subset h]
      exact IsPotential.measurable (Φ := Φ) B
    · rw [truncation_of_not_subset h]
      exact @measurable_const ℝ (S → E) _ (cylinderEvents (B : Set S)) 0

/-- Termwise sup-norm bound: `‖Φ^Δ_B‖ ≤ ‖Φ_B‖`. -/
lemma iSup_enorm_truncation_le (Δ B : Finset S) :
    ⨆ η, ‖Φ.truncation Δ B η‖ₑ ≤ ⨆ η, ‖Φ B η‖ₑ := by
  refine iSup_le fun η ↦ ?_
  by_cases h : B ⊆ Δ
  · rw [truncation_of_subset h]
    exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) η
  · rw [truncation_of_not_subset h]
    simp

/-- The interaction norms of the truncation are dominated: `‖Φ^Δ‖ᵢ ≤ ‖Φ‖ᵢ`. -/
lemma normAt_truncation_le (Δ : Finset S) (i : S) :
    (Φ.truncation Δ).normAt i ≤ Φ.normAt i := by
  refine ENNReal.tsum_le_tsum fun B ↦ ?_
  by_cases hi : B ∈ {A : Finset S | i ∈ A}
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
    exact iSup_enorm_truncation_le Δ B
  · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]

/-- The truncation of an absolutely summable potential is absolutely summable
(`Φ ∈ ℬ ⇒ Φ^Δ ∈ ℬ`). -/
instance (Δ : Finset S) [IsAbsolutelySummable Φ] : IsAbsolutelySummable (Φ.truncation Δ) where
  normAt_ne_top i := ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
    (normAt_truncation_le Δ i)

/-- `∑_{i ∈ Λ} ‖Φ^Δ‖ᵢ ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ`: the Hamiltonian bound of the truncation is dominated,
uniformly in `Δ`. -/
lemma hamiltonianBound_truncation_le [IsAbsolutelySummable Φ] (Δ Λ : Finset S) :
    (Φ.truncation Δ).hamiltonianBound Λ ≤ Φ.hamiltonianBound Λ :=
  ENNReal.toReal_mono (sum_normAt_ne_top (Φ := Φ) Λ)
    (Finset.sum_le_sum fun i _ ↦ normAt_truncation_le Δ i)

/-! ### (C2) The tail of the interaction series and the Hamiltonian estimate -/

/-- Small API for `termNorm` (which is definitionally an indicator). -/
lemma termNorm_of_not_disjoint {B : Finset S} (h : ¬ Disjoint B Λ) :
    Φ.termNorm Λ B = ⨆ η, ‖Φ B η‖ₑ :=
  Set.indicator_of_mem h _

lemma termNorm_of_disjoint {B : Finset S} (h : Disjoint B Λ) :
    Φ.termNorm Λ B = 0 :=
  Set.indicator_of_notMem (by simpa using h) _

variable (Φ) in
/-- Georgii's tail `∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` of the interaction series in the volume `Λ`,
beyond the truncation volume `Δ` (`ℝ≥0∞`-valued). -/
def tailWeight (Δ Λ : Finset S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

variable (Φ) in
/-- The tail `∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` as a real number: the `D`-function of Georgii (4.19)
for the free-boundary net. -/
def tail (Δ Λ : Finset S) : ℝ := (Φ.tailWeight Δ Λ).toReal

lemma tail_nonneg (Δ Λ : Finset S) : 0 ≤ Φ.tail Δ Λ := ENNReal.toReal_nonneg

/-- The tail is dominated by the full interaction series in `Λ`. -/
lemma tailWeight_le_tsum_termNorm (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≤ ∑' A : Finset S, Φ.termNorm Λ A := by
  refine ENNReal.tsum_le_tsum fun B ↦ ?_
  by_cases hB : B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}
  · rw [Set.indicator_of_mem hB, termNorm_of_not_disjoint hB.1]
  · rw [Set.indicator_of_notMem hB]
    exact zero_le

lemma tailWeight_ne_top [IsAbsolutelySummable Φ] (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≠ ⊤ :=
  ne_top_of_le_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) (tailWeight_le_tsum_termNorm Δ Λ)

/-- The terms of `H^{Φ^Δ}_Λ − H^Φ_Λ` are dominated by the tail indicator family. -/
lemma enorm_hamiltonianTerms_truncation_sub_le (Δ Λ : Finset S) (η : S → E) (B : Finset S) :
    ‖(Φ.truncation Δ).hamiltonianTerms Λ η B - Φ.hamiltonianTerms Λ η B‖ₑ
      ≤ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ ζ, ‖Φ A ζ‖ₑ) B := by
  by_cases hd : Disjoint B Λ
  · rw [hamiltonianTerms_of_disjoint (Φ := Φ.truncation Δ) hd η,
      hamiltonianTerms_of_disjoint (Φ := Φ) hd η]
    simp
  · rw [hamiltonianTerms_of_not_disjoint (Φ := Φ.truncation Δ) hd η,
      hamiltonianTerms_of_not_disjoint (Φ := Φ) hd η]
    by_cases hsub : B ⊆ Δ
    · rw [truncation_of_subset hsub]
      simp
    · rw [truncation_of_not_subset hsub,
        Set.indicator_of_mem
          (show B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ} from ⟨hd, hsub⟩)]
      simp only [Pi.zero_apply, zero_sub, enorm_neg]
      exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) η

/-- **(C2), enorm form.** `‖H^{Φ^Δ}_Λ − H^Φ_Λ‖ₑ ≤ tailWeight Δ Λ`. -/
theorem enorm_hamiltonian_truncation_sub_le [IsAbsolutelySummable Φ]
    (Δ Λ : Finset S) (η : S → E) :
    ‖(Φ.truncation Δ).hamiltonian Λ η - Φ.hamiltonian Λ η‖ₑ ≤ Φ.tailWeight Δ Λ := by
  have hsT : Summable ((Φ.truncation Δ).hamiltonianTerms Λ η) :=
    summable_hamiltonianTerms (Φ := Φ.truncation Δ) Λ η
  have hsΦ : Summable (Φ.hamiltonianTerms Λ η) := summable_hamiltonianTerms (Φ := Φ) Λ η
  have hdiff : (Φ.truncation Δ).hamiltonian Λ η - Φ.hamiltonian Λ η
      = ∑' B : Finset S,
          ((Φ.truncation Δ).hamiltonianTerms Λ η B - Φ.hamiltonianTerms Λ η B) := by
    rw [hamiltonian_eq_tsum (Φ := Φ.truncation Δ) Λ η, hamiltonian_eq_tsum (Φ := Φ) Λ η]
    exact (hsT.tsum_sub hsΦ).symm
  rw [hdiff]
  exact le_trans enorm_tsum_le_tsum_enorm
    (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_truncation_sub_le Δ Λ η))

/-- **(C2), the Hamiltonian estimate of Georgii (4.20)(1).**
`|H^{Φ^Δ}_Λ η − H^Φ_Λ η| ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖ = tail Δ Λ`. -/
theorem abs_hamiltonian_truncation_sub_le [IsAbsolutelySummable Φ]
    (Δ Λ : Finset S) (η : S → E) :
    |(Φ.truncation Δ).hamiltonian Λ η - Φ.hamiltonian Λ η| ≤ Φ.tail Δ Λ := by
  have h := enorm_hamiltonian_truncation_sub_le (Φ := Φ) Δ Λ η
  rw [← ENNReal.toReal_le_toReal (by simp) (tailWeight_ne_top (Φ := Φ) Δ Λ)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), tail] using h

/-! ### (C3) The tail vanishes along `Δ ↑ S` -/

/-- The tail indicator family is the restriction of the interaction series `termNorm Λ` to the
supports outside the powerset of `Δ`. -/
lemma indicator_tail_eq (Δ Λ B : Finset S) :
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) B
      = {A : Finset S | A ∉ Δ.powerset}.indicator (Φ.termNorm Λ) B := by
  by_cases hsub : B ⊆ Δ
  · rw [Set.indicator_of_notMem (fun h ↦ h.2 hsub),
      Set.indicator_of_notMem
        (show B ∉ {A : Finset S | A ∉ Δ.powerset} from
          fun h ↦ h (Finset.mem_powerset.2 hsub))]
  · rw [Set.indicator_of_mem
      (show B ∈ {A : Finset S | A ∉ Δ.powerset} from fun h ↦ hsub (Finset.mem_powerset.1 h))]
    by_cases hd : Disjoint B Λ
    · rw [Set.indicator_of_notMem (fun h ↦ h.1 hd), termNorm_of_disjoint hd]
    · rw [Set.indicator_of_mem
        (show B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ} from ⟨hd, hsub⟩),
        termNorm_of_not_disjoint hd]

/-- The tail is the sum of the interaction series over the supports not contained in `Δ`. -/
lemma tailWeight_eq_tsum_compl (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ
      = ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
  calc Φ.tailWeight Δ Λ
      = ∑' B : Finset S, {A : Finset S | A ∉ Δ.powerset}.indicator (Φ.termNorm Λ) B :=
        tsum_congr fun B ↦ indicator_tail_eq Δ Λ B
    _ = ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
        (tsum_subtype {A : Finset S | A ∉ Δ.powerset} (Φ.termNorm Λ)).symm

/-- **(C3), enorm form.** The tail of an absolutely summable potential vanishes along `Δ ↑ S`:
tail-of-summable-series convergence, transported along `Δ ↦ Δ.powerset`. -/
theorem tendsto_tailWeight_atTop [IsAbsolutelySummable Φ] (Λ : Finset S) :
    Tendsto (fun Δ : Finset S ↦ Φ.tailWeight Δ Λ) atTop (𝓝 0) := by
  have hfun : (fun Δ : Finset S ↦ Φ.tailWeight Δ Λ)
      = fun Δ : Finset S ↦
          ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
    funext fun Δ ↦ tailWeight_eq_tsum_compl Δ Λ
  rw [hfun]
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero (f := Φ.termNorm Λ)
    (tsum_termNorm_ne_top (Φ := Φ) Λ)).comp
    (Filter.tendsto_finset_powerset_atTop_atTop (α := S))
  simpa [Function.comp_def] using h

/-- **(C3).** `lim_{Δ ↑ S} ∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖ = 0` for `Φ ∈ ℬ`
(Georgii (4.20)(1), the display before the conclusion). -/
theorem tendsto_tail_atTop [IsAbsolutelySummable Φ] (Λ : Finset S) :
    Tendsto (fun Δ : Finset S ↦ Φ.tail Δ Λ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp
    (tendsto_tailWeight_atTop (Φ := Φ) Λ)
  simpa [tail, Function.comp_def] using h

end Potential

/-! ### A `bindPM` version of the consistency bound (for the boundary-field net) -/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- A uniform bound on the kernels of a smaller volume passes to the finite-volume Gibbs
distribution `ν' γ_{Λ'}` of any larger volume and any boundary field, by consistency. -/
lemma bindPM_apply_le {γ : Specification S E} {Λ Λ' : Finset S} (h : Λ ⊆ Λ')
    (μ' : ProbabilityMeasure (S → E)) {A : Set (S → E)} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : ∀ ω, γ Λ ω A ≤ c) :
    (γ.bindPM Λ' μ' : Measure (S → E)) A ≤ c := by
  rw [Specification.coe_bindPM,
    Measure.bind_apply hA (γ.measurable_kernel_toMeasure Λ').aemeasurable]
  calc ∫⁻ ω, γ Λ' ω A ∂(μ' : Measure (S → E))
      ≤ ∫⁻ _, c ∂(μ' : Measure (S → E)) :=
        lintegral_mono fun ω ↦ finiteVolumeDistributions_apply_le h ω hA hc
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

end MeasureTheory.GibbsMeasure

/-! ### (C4) Georgii Example (4.20)(1): free boundary conditions -/

namespace Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (4.19) for the free-boundary truncations**: `γ^{Φ^Δ} → γ^Φ` uniformly in the
𝓛-topology along `Δ ↑ S` — verbatim the `hunif` hypothesis of Georgii (4.17)/(4.22), with
`D`-function the tail `Δ Λ ↦ Φ.tail Δ Λ` of (C2)/(C3). -/
theorem tendsto_dist_action_truncation :
    ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun Δ : Finset S ↦ dist
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).action Λ f)
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)) atTop (𝓝 0) :=
  tendsto_dist_action_gibbsSpecification_of_mem_localFunctions ν β
    (Φs := fun Δ : Finset S ↦ Φ.truncation Δ) (D := fun Δ Λ ↦ Φ.tail Δ Λ)
    (fun Δ Λ η ↦ abs_hamiltonian_truncation_sub_le Δ Λ η)
    (fun Λ ↦ tendsto_tail_atTop Λ)

/-- **Georgii Example (4.20)(1).** Every cluster point of the free-boundary net
`Δ ↦ ν_Δ γ^{Φ^Δ}_Δ` in the topology of local convergence is a Gibbs measure for `Φ`. -/
theorem mem_GP_of_mapClusterPt_truncation
    (νs : Finset S → ProbabilityMeasure (S → E)) {μ : ProbabilityMeasure (S → E)}
    (hcp : MapClusterPt
      (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
      fun Δ : Finset S ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ (νs Δ))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  mem_GP_of_mapClusterPt (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)
    (Λs := id) tendsto_id (tendsto_dist_action_truncation ν β) hcp

/-- **Georgii Example (4.20)(1)** for a configurational boundary condition: every cluster point
of `(γ^{Φ^Δ}_Δ(·|ω))_{Δ ∈ 𝒮}` belongs to `𝒢(Φ)`. -/
theorem mem_GP_of_mapClusterPt_truncation_finiteVolumeDistributions (ω : S → E)
    {μ : ProbabilityMeasure (S → E)}
    (hcp : MapClusterPt
      (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
      fun Δ : Finset S ↦ WithSetwiseTopology.ofMeasure
        (finiteVolumeDistributions
          (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β) ω Δ)) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) := by
  refine mem_GP_of_mapClusterPt_truncation ν β
    (fun _ ↦ ⟨Measure.dirac ω, inferInstance⟩) ?_
  have h : ∀ Δ : Finset S,
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ
          ⟨Measure.dirac ω, inferInstance⟩
        = finiteVolumeDistributions
            (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β) ω Δ :=
    fun Δ ↦ Subtype.ext (Measure.dirac_bind
      ((gibbsSpecificationOfAbsolutelySummable
        (Φ := Φ.truncation Δ) ν β).measurable_kernel_toMeasure Δ) ω)
  simpa only [h] using hcp

/-- The free-boundary net is locally equicontinuous, unconditionally: the density bound
Georgii (4.14)(1) for `γ^{Φ^Δ}` is uniform in `Δ`. -/
theorem locallyEquicontinuous_truncation_bindPM
    (νs : Finset S → ProbabilityMeasure (S → E)) :
    LocallyEquicontinuous atTop fun Δ : Finset S ↦
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ (νs Δ) := by
  refine locallyEquicontinuous_of_eventually_le (dominatingMeasure Φ ν β) fun Λ ↦ ?_
  filter_upwards [eventually_ge_atTop Λ] with Δ hΔ
  intro A hA
  refine bindPM_apply_le hΔ (νs Δ)
    (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) fun ω ↦ ?_
  calc gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β Λ ω A
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * (Φ.truncation Δ).hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A :=
        gibbsSpecificationOfAbsolutelySummable_apply_le (Φ := Φ.truncation Δ) ν β Λ ω hA
    _ ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A := by
        gcongr
        exact hamiltonianBound_truncation_le Δ Λ
    _ = dominatingMeasure Φ ν β Λ A := by
        rw [dominatingMeasure, Measure.smul_apply, smul_eq_mul]

/-- Free-boundary existence from local equicontinuity, over a standard Borel state space:
Georgii (4.20)(1) combined with Theorem (4.22). -/
theorem exists_mem_GP_mapClusterPt_truncation_of_locallyEquicontinuous [StandardBorelSpace E]
    (νs : Finset S → ProbabilityMeasure (S → E))
    (hle : LocallyEquicontinuous atTop fun Δ : Finset S ↦
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ (νs Δ)) :
    ∃ μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β),
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
        fun Δ : Finset S ↦ WithSetwiseTopology.ofMeasure
          ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ
            (νs Δ)) :=
  exists_mem_GP_mapClusterPt
    (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)
    (Λs := id) tendsto_id (tendsto_dist_action_truncation ν β) hle

/-- **Free-boundary existence.** Over a standard Borel state space, the free-boundary net of
any `Φ ∈ ℬ` has a cluster point in the topology of local convergence, and every such cluster
point is a Gibbs measure for `Φ`. -/
theorem exists_mem_GP_mapClusterPt_truncation [StandardBorelSpace E]
    (νs : Finset S → ProbabilityMeasure (S → E)) :
    ∃ μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β),
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
        fun Δ : Finset S ↦ WithSetwiseTopology.ofMeasure
          ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ.truncation Δ) ν β).bindPM Δ
            (νs Δ)) :=
  exists_mem_GP_mapClusterPt_truncation_of_locallyEquicontinuous ν β νs
    (locallyEquicontinuous_truncation_bindPM ν β νs)

end Potential

/-! ### The truncations converge in `ℬ` -/

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E}

/-- The interaction norm of `Φ − Φ^Δ` at `i` is the tail of the interaction series at `{i}`. -/
lemma normAt_sub_truncation (Δ : Finset S) (i : S) :
    (Φ - Φ.truncation Δ).normAt i = Φ.tailWeight Δ {i} := by
  classical
  unfold normAt tailWeight
  refine tsum_congr fun A ↦ ?_
  by_cases hi : i ∈ A
  · have hmem : A ∈ {A : Finset S | i ∈ A} := hi
    rw [Set.indicator_of_mem hmem]
    by_cases hAΔ : A ⊆ Δ
    · have hnot : A ∉ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} := fun h ↦ h.2 hAΔ
      rw [Set.indicator_of_notMem hnot]
      simp [sub_apply, truncation_of_subset hAΔ]
    · have hm : A ∈ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} :=
        ⟨by simpa [Finset.disjoint_singleton_right] using hi, hAΔ⟩
      rw [Set.indicator_of_mem hm]
      simp [sub_apply, truncation_of_not_subset hAΔ]
  · have hnm : A ∉ {A : Finset S | i ∈ A} := hi
    have hnm' : A ∉ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} := fun h ↦
      h.1 (by simpa [Finset.disjoint_singleton_right] using hi)
    rw [Set.indicator_of_notMem hnm, Set.indicator_of_notMem hnm']

/-- The truncations `Φ^Δ` of `Φ ∈ ℬ`, as elements of `ℬ`. -/
noncomputable def truncationB (Φ : absolutelySummable S E) (Δ : Finset S) :
    absolutelySummable S E :=
  ⟨(Φ : Potential S E).truncation Δ, inferInstance, truncation_empty (coe_apply_empty Φ) Δ,
    inferInstance⟩

@[simp] lemma coe_truncationB (Φ : absolutelySummable S E) (Δ : Finset S) :
    (truncationB Φ Δ : Potential S E) = (Φ : Potential S E).truncation Δ := rfl

/-- **Georgii (4.20)(1) in `ℬ`**: the free-boundary truncations of `Φ` converge to `Φ` in the
topology of `ℬ`. -/
theorem tendsto_truncationB (Φ : absolutelySummable S E) :
    Tendsto (truncationB Φ) atTop (𝓝 Φ) := by
  rw [tendsto_iff_tendsto_seminormAt]
  intro i
  refine (tendsto_tail_atTop (Φ := (Φ : Potential S E)) {i}).congr fun Δ ↦ ?_
  rw [seminormAt_apply, Submodule.coe_sub, coe_truncationB, ← normAt_neg, neg_sub,
    normAt_sub_truncation]
  rfl

end Potential

end

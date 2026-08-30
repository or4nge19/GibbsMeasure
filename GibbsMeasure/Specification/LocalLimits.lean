/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.GibbsKernel
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Topology.Metrizable

/-!
# Georgii, Theorem (7.12): extreme Gibbs measures as limits of finite-volume distributions

For an extreme Gibbs measure `μ ∈ ex G(γ)` (equivalently, by Theorem (7.7)(a), a tail-trivial
Gibbs measure) and the exhaustion `Λ_n = exhaustionVolumes n`:

* (a) `γ_{Λ_n}(A | ω) → μ(A)` for `μ`-a.e. `ω`, for every measurable `A`
  (`tendsto_ae_kernel_exhaustion_of_tailTrivial`,
  `tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G`): the DLR equation identifies
  `γ_{Λ_n}(A | ·)` with `μ(A | 𝓕_{Λ_nᶜ})`, Lévy's downward theorem gives a.e. convergence to
  `μ(A | 𝓣)`, and tail triviality makes the latter a.e. equal to `μ(A)`;
* (b)/(c) over a finite state space, where the local events are countable,
  `γ_{Λ_n}(· | ω) → μ` in the topology of local convergence for `μ`-a.e. `ω`
  (`ae_tendsto_finiteVolumeDistributions_exhaustion_of_mem_extremePoints_G`);
* Georgii's set `G_lim(γ)` of limiting Gibbs measures (`limitGibbs`, sequence form, as defined
  before Corollary (7.30)), with `ex G(γ) ⊆ G_lim(γ)` over a finite state space
  (`ofMeasure_mem_limitGibbs_of_mem_extremePoints_G`) and `G_lim(γ) ⊆ G(γ)` for a quasilocal `γ`
  (`limitGibbs_subset_GP`, Theorem (4.17)).

Only the local-convergence form of (7.12)(c) over a finite state space is proved here; the
uniform form of (c) and the weak-convergence statement (b) are not formalized.
-/

@[expose] public section


open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

section LimitGibbs

variable (γ : Specification S E)

/-- **Georgii's `G_lim(γ)`**: local limits of `γ_{Λ_n}(· | ω_n)` along volumes `Λ_n → S`. -/
def limitGibbs : Set (WithLocalConvergence S E) :=
  {μ | ∃ (Λ : ℕ → Finset S) (ω : ℕ → S → E), Tendsto Λ atTop atTop ∧
    Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ (ω n) (Λ n)) :
      WithLocalConvergence S E)) atTop (𝓝 μ)}

/-- **Georgii (4.17)**: for quasilocal `γ`, limiting Gibbs measures are Gibbs, `G_lim(γ) ⊆ G(γ)`. -/
theorem limitGibbs_subset_GP (hγ : γ.IsQuasilocal) :
    limitGibbs γ ⊆ WithSetwiseTopology.toMeasure ⁻¹' GP γ := by
  rintro ⟨ν⟩ ⟨Λ, ω, hΛ, hconv⟩
  have hdirac : ∀ n, γ.bindPM (Λ n) ⟨Measure.dirac (ω n), inferInstance⟩ =
      finiteVolumeDistributions γ (ω n) (Λ n) := fun n ↦
    Subtype.ext (Measure.dirac_bind (γ.measurable_kernel_toMeasure (Λ n)) (ω n))
  show ν ∈ GP γ
  refine mem_GP_of_tendsto_withLocalConvergence (l := (atTop : Filter ℕ)) hγ
    (γs := fun _ ↦ γ) (Λs := Λ) (νs := fun n ↦ ⟨Measure.dirac (ω n), inferInstance⟩) hΛ
    (fun Λ f _ ↦ by simp) ?_
  exact hconv.congr fun n ↦ by rw [hdirac n]

/-- **Georgii (4.17)**, pointwise form: a limiting Gibbs measure of a quasilocal `γ` is Gibbs. -/
theorem mem_GP_of_mem_limitGibbs (hγ : γ.IsQuasilocal) {μ : WithLocalConvergence S E}
    (hμ : μ ∈ limitGibbs γ) : μ.toMeasure ∈ GP γ :=
  limitGibbs_subset_GP γ hγ hμ

end LimitGibbs

section TailTrivial

variable {μ : Measure (S → E)} [IsProbabilityMeasure μ]

/-- Under a tail-trivial probability measure, `μ(A | 𝓣)` is a.e. the constant `μ(A)`. -/
lemma condExp_tail_ae_eq_measureReal_of_tailTrivial
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] =ᵐ[μ] fun _ ↦ μ.real A := by
  have htail' : IsTailTrivial (⟨μ, ‹_›⟩ : ProbabilityMeasure (S → E)) := htail
  obtain ⟨c, hc⟩ := htail'.ae_eq_const_of_measurable (X := ℝ)
    (f := μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _])
    stronglyMeasurable_condExp.measurable
  have hc' : μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] =ᵐ[μ] fun _ ↦ c := hc
  have h : ∫ x, (μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _]) x ∂μ = c := by
    rw [integral_congr_ae hc', integral_const, probReal_univ, one_smul]
  rw [integral_condExp tailSigmaAlgebra_le_pi, integral_indicator_const (1 : ℝ) hA, smul_eq_mul,
    mul_one] at h
  exact hc'.trans (Eventually.of_forall fun _ ↦ h.symm)

end TailTrivial

variable [Countable S]

/-- The exhaustion `exhaustionVolumes` tends to `S`: it is cofinal in the finite volumes. -/
lemma tendsto_exhaustionVolumes_atTop :
    Tendsto (exhaustionVolumes (S := S)) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun Λ ↦ ?_
  obtain ⟨n, hn⟩ := exhaustionVolumes_cofinal (S := S) Λ
  exact ⟨n, fun m hm ↦ hn.trans (exhaustionVolumes_monotone hm)⟩

section PartA

variable {γ : Specification S E} {μ : Measure (S → E)}

/-- **Georgii (7.12)(a)**: `γ_{Λ_n}(A | ·) → μ(A)` a.e. for a tail-trivial Gibbs measure `μ`. -/
theorem tendsto_ae_kernel_exhaustion_of_tailTrivial [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ)
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (γ (exhaustionVolumes n) ω A).toReal) atTop (𝓝 (μ.real A)) := by
  have hg : Integrable (A.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have h1 := hg.tendsto_ae_condExp_of_antitone (antitone_exhaustionFiltration (S := S) (E := E))
    exhaustionFiltration_le_pi
  rw [iInf_exhaustionFiltration] at h1
  have h2 : ∀ᵐ ω ∂μ, ∀ n, (μ[A.indicator (fun _ ↦ (1 : ℝ)) | exhaustionFiltration S E n]) ω
      = (γ (exhaustionVolumes n) ω A).toReal :=
    ae_all_iff.2 fun n ↦ condExp_exhaustionFiltration_ae_eq hμ hA n
  filter_upwards [h1, h2, condExp_tail_ae_eq_measureReal_of_tailTrivial htail hA]
    with ω h1ω h2ω h3ω
  rw [h3ω] at h1ω
  exact h1ω.congr h2ω

/-- **Georgii (7.12)(a)**: `γ_{Λ_n}(A | ·) → μ(A)` a.e. for an extreme Gibbs measure `μ`. -/
theorem tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) {A : Set (S → E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (γ (exhaustionVolumes n) ω A).toReal) atTop (𝓝 (μ.real A)) := by
  have : IsProbabilityMeasure μ := hμ.1.1
  exact tendsto_ae_kernel_exhaustion_of_tailTrivial hμ.1.2
    (tailTrivial_of_mem_extremePoints_G hμ) hA

/-- **Georgii (7.12)(a)**, `ℝ≥0∞`-valued form. -/
theorem tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G'
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) {A : Set (S → E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ γ (exhaustionVolumes n) ω A) atTop (𝓝 (μ A)) := by
  have : IsProbabilityMeasure μ := hμ.1.1
  filter_upwards [tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G hμ hA] with ω hω
  exact (ENNReal.tendsto_toReal_iff (fun n ↦ measure_ne_top _ _) (measure_ne_top _ _)).1 hω

end PartA

section PartC

variable (γ : Specification S E)

/-- **Georgii (7.12)(c)**, finite `E`: `γ_{Λ_n}(· | ω) → μ` locally, `μ`-a.e., for `μ` extreme. -/
theorem ae_tendsto_finiteVolumeDistributions_exhaustion_of_mem_extremePoints_G [Finite E]
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ (G γ).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure (S → E)),
      Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure
          (finiteVolumeDistributions γ ω (exhaustionVolumes n)) : WithLocalConvergence S E))
        atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  have h : ∀ᵐ ω ∂(μ : Measure (S → E)), ∀ A : localEvents S E,
      Tendsto (fun n ↦ γ (exhaustionVolumes n) ω A.1) atTop (𝓝 ((μ : Measure (S → E)) A.1)) :=
    ae_all_iff.2 fun A ↦ tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G' hμ
      (MeasurableSet.of_mem_measurableCylinders A.2)
  filter_upwards [h] with ω hω
  exact tendsto_withLocalConvergence_iff.2 fun A hA ↦ hω ⟨A, hA⟩

/-- **Georgii (7.12)(c)**, finite `E`: every extreme Gibbs measure is a limiting Gibbs measure. -/
theorem ofMeasure_mem_limitGibbs_of_mem_extremePoints_G [Finite E]
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ (G γ).extremePoints ℝ≥0∞) :
    (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ limitGibbs γ := by
  obtain ⟨ω, hω⟩ :=
    (ae_tendsto_finiteVolumeDistributions_exhaustion_of_mem_extremePoints_G γ hμ).exists
  exact ⟨exhaustionVolumes, fun _ ↦ ω, tendsto_exhaustionVolumes_atTop, hω⟩

end PartC

end MeasureTheory.GibbsMeasure

end

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
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Georgii, Theorem (7.12): extreme Gibbs measures as limits of finite-volume distributions

For an extreme Gibbs measure `μ ∈ ex G(γ)` (equivalently, by Theorem (7.7)(a), a tail-trivial
Gibbs measure) and an increasing cofinal sequence of volumes `(Λ_n)` — in particular the canonical
exhaustion `Λ_n = exhaustionVolumes n`:

* (a) `γ_{Λ_n}(A | ω) → μ(A)` for `μ`-a.e. `ω`, for every measurable `A`
  (`tendsto_ae_kernel_exhaustion_of_tailTrivial`,
  `tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G`): the DLR equation identifies
  `γ_{Λ_n}(A | ·)` with `μ(A | 𝓕_{Λ_nᶜ})`, Lévy's downward theorem gives a.e. convergence to
  `μ(A | 𝓣)`, and tail triviality makes the latter a.e. equal to `μ(A)`;
* (a) in functional form (`tendsto_ae_integral_kernel_of_tailTrivial`,
  `tendsto_ae_integral_kernel_of_mem_extremePoints_G`): `γ_{Λ_n}f → μ(f)` for `μ`-a.e. `ω`, for
  every `μ`-integrable `f` and along *any* increasing cofinal sequence of volumes;
* (b) over a compact metrizable state space `E` carrying its Borel `σ`-algebra,
  `γ_{Λ_n}(· | ω) → μ` **weakly** for `μ`-a.e. `ω`
  (`ae_tendsto_finiteVolumeDistributions_weakly_of_mem_extremePoints_G`): the configuration space
  `S → E` is then compact metrizable, hence `C(S → E, ℝ)` is separable, so (a) applied to a
  countable sup-norm dense set of bounded continuous functions produces a single `μ`-full set of
  boundary conditions on which all of them converge, and a `3ε` argument
  (`ProbabilityMeasure.tendsto_of_forall_mem_dense_tendsto_integral`) upgrades this to every
  bounded continuous function;
* (c) over a finite state space, where the local events are countable,
  `γ_{Λ_n}(· | ω) → μ` in the topology of local convergence for `μ`-a.e. `ω`
  (`ae_tendsto_finiteVolumeDistributions_exhaustion_of_mem_extremePoints_G`);
* Georgii's set `G_lim(γ)` of limiting Gibbs measures (`limitGibbs`, sequence form, as defined
  before Corollary (7.30)), with `ex G(γ) ⊆ G_lim(γ)` over a finite state space
  (`ofMeasure_mem_limitGibbs_of_mem_extremePoints_G`) and `G_lim(γ) ⊆ G(γ)` for a quasilocal `γ`
  (`limitGibbs_subset_GP`, Theorem (4.17)).

Of (7.12)(c) only the local-convergence form over a finite state space is proved here; the
uniform (total-variation on each finite volume) form of (c) is not formalized.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology BoundedContinuousFunction

namespace MeasureTheory

/-! ### Testing weak convergence on a dense set of bounded continuous functions

These three statements are general facts about weak convergence of probability measures and are
independent of Gibbs theory; they are what turns Theorem (7.12)(a) into Theorem (7.12)(b). -/

section WeakConvergenceViaDenseSet

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Two bounded continuous functions have integrals against a probability measure at distance at
most their sup-distance. -/
lemma abs_integral_sub_le_dist (ν : Measure Ω) [IsProbabilityMeasure ν] (f g : Ω →ᵇ ℝ) :
    |∫ ω, f ω ∂ν - ∫ ω, g ω ∂ν| ≤ dist f g := by
  rw [← integral_sub (f.integrable ν) (g.integrable ν), ← Real.norm_eq_abs]
  have h : ∀ᵐ ω ∂ν, ‖f ω - g ω‖ ≤ dist f g := ae_of_all _ fun ω ↦ by
    rw [Real.norm_eq_abs, ← Real.dist_eq]; exact f.dist_coe_le_dist ω
  simpa using norm_integral_le_of_norm_le_const h

/-- Weak convergence of probability measures may be tested on a **dense** set of bounded continuous
functions: this is the standard `3ε` argument, using that all the measures involved have total
mass one. -/
theorem ProbabilityMeasure.tendsto_of_forall_mem_dense_tendsto_integral {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} {D : Set (Ω →ᵇ ℝ)} (hD : Dense D)
    (h : ∀ f ∈ D, Tendsto (fun i ↦ ∫ ω, f ω ∂(νs i : Measure Ω)) l
      (𝓝 (∫ ω, f ω ∂(μ : Measure Ω)))) :
    Tendsto νs l (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, hgD, hfg⟩ := hD.exists_dist_lt f (ε := ε / 3) (by positivity)
  filter_upwards [Metric.tendsto_nhds.1 (h g hgD) (ε / 3) (by positivity)] with i hi
  have h1 := abs_integral_sub_le_dist (νs i : Measure Ω) f g
  have h2 := abs_integral_sub_le_dist (μ : Measure Ω) f g
  rw [Real.dist_eq] at hi ⊢
  have h3 : |∫ ω, f ω ∂(νs i : Measure Ω) - ∫ ω, f ω ∂(μ : Measure Ω)| ≤
      |∫ ω, f ω ∂(νs i : Measure Ω) - ∫ ω, g ω ∂(νs i : Measure Ω)| +
        (|∫ ω, g ω ∂(νs i : Measure Ω) - ∫ ω, g ω ∂(μ : Measure Ω)| +
          |∫ ω, g ω ∂(μ : Measure Ω) - ∫ ω, f ω ∂(μ : Measure Ω)|) := by
    have := abs_sub_le (∫ ω, f ω ∂(νs i : Measure Ω)) (∫ ω, g ω ∂(νs i : Measure Ω))
      (∫ ω, f ω ∂(μ : Measure Ω))
    have h' := abs_sub_le (∫ ω, g ω ∂(νs i : Measure Ω)) (∫ ω, g ω ∂(μ : Measure Ω))
      (∫ ω, f ω ∂(μ : Measure Ω))
    linarith
  rw [abs_sub_comm (∫ ω, g ω ∂(μ : Measure Ω))] at h3
  linarith

/-- On a compact, locally compact, second countable space the bounded continuous real functions
form a separable space: `C(X, ℝ)` is second countable, hence separable, and it is isometric to
`X →ᵇ ℝ`. -/
theorem separableSpace_boundedContinuousFunction {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [SecondCountableTopology X] [LocallyCompactSpace X] :
    TopologicalSpace.SeparableSpace (X →ᵇ ℝ) :=
  (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).toHomeomorph.surjective.denseRange.separableSpace
    (ContinuousMap.isometryEquivBoundedOfCompact X ℝ).toHomeomorph.continuous

end WeakConvergenceViaDenseSet

end MeasureTheory

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

section Cofinal

omit [Countable S] in
/-- Along an increasing sequence of volumes the outside-volume σ-algebras decrease. -/
lemma antitone_cylinderEvents_compl {Λ : ℕ → Finset S} (hmono : Monotone Λ) :
    Antitone fun n ↦ cylinderEvents (X := fun _ : S ↦ E) ((Λ n : Set S)ᶜ) := fun _ _ hmn ↦
  cylinderEvents_mono (X := fun _ : S ↦ E) (compl_subset_compl.2 (Finset.coe_subset.2 (hmono hmn)))

omit [Countable S] in
/-- **Georgii (2.19)**: the tail σ-field is the intersection of the outside-volume σ-algebras
along any cofinal sequence of volumes. -/
lemma tailSigmaAlgebra_eq_iInf_of_cofinal {Λ : ℕ → Finset S}
    (hcof : ∀ Δ : Finset S, ∃ n, Δ ⊆ Λ n) :
    (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E))
      = ⨅ n : ℕ, cylinderEvents (X := fun _ : S ↦ E) ((Λ n : Set S)ᶜ) := by
  refine le_antisymm (le_iInf fun n ↦ iInf_le _ (Λ n)) (le_iInf fun Δ ↦ ?_)
  obtain ⟨n, hn⟩ := hcof Δ
  exact (iInf_le _ n).trans (cylinderEvents_mono (X := fun _ : S ↦ E)
    (compl_subset_compl.2 (Finset.coe_subset.2 hn)))

end Cofinal

section PartAFun

variable {γ : Specification S E} {μ : Measure (S → E)}

omit [Countable S] in
/-- Under a tail-trivial probability measure, `μ(f | 𝓣)` is a.e. the constant `μ(f)`. -/
lemma condExp_tail_ae_eq_integral_of_tailTrivial [IsProbabilityMeasure μ]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    (f : (S → E) → ℝ) :
    μ[f | @tailSigmaAlgebra S E _] =ᵐ[μ] fun _ ↦ ∫ x, f x ∂μ := by
  have htail' : IsTailTrivial (⟨μ, ‹_›⟩ : ProbabilityMeasure (S → E)) := htail
  obtain ⟨c, hc⟩ := htail'.ae_eq_const_of_measurable (X := ℝ)
    (f := μ[f | @tailSigmaAlgebra S E _]) stronglyMeasurable_condExp.measurable
  have hc' : μ[f | @tailSigmaAlgebra S E _] =ᵐ[μ] fun _ ↦ c := hc
  have h : ∫ x, (μ[f | @tailSigmaAlgebra S E _]) x ∂μ = c := by
    rw [integral_congr_ae hc', integral_const, probReal_univ, one_smul]
  rw [integral_condExp tailSigmaAlgebra_le_pi] at h
  exact hc'.trans (Eventually.of_forall fun _ ↦ h.symm)

omit [Countable S] in
/-- **Georgii (7.12)(a)**, functional form: `γ_{Λ_n}f → μ(f)` `μ`-a.e. along any increasing
cofinal sequence of volumes, for every `μ`-integrable `f` and every tail-trivial Gibbs measure
`μ`. -/
theorem tendsto_ae_integral_kernel_of_tailTrivial [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ)
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Δ : Finset S, ∃ n, Δ ⊆ Λ n)
    {f : (S → E) → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have h1 := hf.tendsto_ae_condExp_of_antitone (antitone_cylinderEvents_compl (E := E) hmono)
    (fun _ ↦ cylinderEvents_le_pi)
  rw [← tailSigmaAlgebra_eq_iInf_of_cofinal (E := E) hcof] at h1
  have h2 : ∀ᵐ ω ∂μ, ∀ n,
      (μ[f | cylinderEvents (X := fun _ : S ↦ E) ((Λ n : Set S)ᶜ)]) ω = ∫ x, f x ∂(γ (Λ n) ω) := by
    refine ae_all_iff.2 fun n ↦ ?_
    have : (γ (Λ n)).IsCondExp μ := hμ _
    exact Kernel.condExp_ae_eq_integral (γ.isProper _) cylinderEvents_le_pi f hf
  filter_upwards [h1, h2, condExp_tail_ae_eq_integral_of_tailTrivial htail f] with ω h1ω h2ω h3ω
  rw [h3ω] at h1ω
  exact h1ω.congr h2ω

omit [Countable S] in
/-- **Georgii (7.12)(a)**, functional form, for an extreme Gibbs measure. -/
theorem tendsto_ae_integral_kernel_of_mem_extremePoints_G
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Δ : Finset S, ∃ n, Δ ⊆ Λ n)
    {f : (S → E) → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have : IsProbabilityMeasure μ := hμ.1.1
  exact tendsto_ae_integral_kernel_of_tailTrivial hμ.1.2
    (tailTrivial_of_mem_extremePoints_G hμ) hmono hcof hf

/-- **Georgii (7.12)(a)**, functional form along the canonical exhaustion. -/
theorem tendsto_ae_integral_kernel_exhaustion_of_mem_extremePoints_G
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) {f : (S → E) → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (exhaustionVolumes n) ω)) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_ae_integral_kernel_of_mem_extremePoints_G hμ exhaustionVolumes_monotone
    exhaustionVolumes_cofinal hf

end PartAFun

section PartB

variable [TopologicalSpace E] [CompactSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
  (γ : Specification S E)

/-- **Georgii (7.12)(b)**: for a compact metrizable state space `E` with its Borel σ-algebra, an
extreme Gibbs measure `μ ∈ ex G(γ)` and an increasing cofinal sequence of volumes `(Λ_n)`, one has
`γ_{Λ_n}(· | ω) → μ` **weakly** for `μ`-almost all `ω`.

Georgii's proof: the configuration space `S → E` is then compact metrizable, so the bounded
continuous functions on it contain a countable sup-norm dense set `C₀`; part (a) gives a single
`μ`-full set of boundary conditions `ω` on which `γ_{Λ_n}(f | ω) → μ(f)` for all `f ∈ C₀`
simultaneously, and density upgrades this to all bounded continuous `f`. -/
theorem ae_tendsto_finiteVolumeDistributions_weakly_of_mem_extremePoints_G
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ (G γ).extremePoints ℝ≥0∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Δ : Finset S, ∃ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂(μ : Measure (S → E)),
      Tendsto (fun n ↦ finiteVolumeDistributions γ ω (Λ n)) atTop (𝓝 μ) := by
  have : TopologicalSpace.SeparableSpace ((S → E) →ᵇ ℝ) :=
    separableSpace_boundedContinuousFunction
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ((S → E) →ᵇ ℝ)
  have : Countable D := hDc.to_subtype
  have h : ∀ᵐ ω ∂(μ : Measure (S → E)), ∀ f : D,
      Tendsto (fun n ↦ ∫ x, (f : (S → E) →ᵇ ℝ) x ∂(γ (Λ n) ω)) atTop
        (𝓝 (∫ x, (f : (S → E) →ᵇ ℝ) x ∂(μ : Measure (S → E)))) :=
    ae_all_iff.2 fun f ↦ tendsto_ae_integral_kernel_of_mem_extremePoints_G hμ hmono hcof
      ((f : (S → E) →ᵇ ℝ).integrable _)
  filter_upwards [h] with ω hω
  exact ProbabilityMeasure.tendsto_of_forall_mem_dense_tendsto_integral hDd fun f hf ↦ hω ⟨f, hf⟩

/-- **Georgii (7.12)(b)**, unfolded: for `μ`-almost all `ω`, `γ_{Λ_n}(f | ω) → μ(f)` for *every*
bounded continuous `f` simultaneously. -/
theorem ae_forall_tendsto_integral_boundedContinuous_of_mem_extremePoints_G
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ (G γ).extremePoints ℝ≥0∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Δ : Finset S, ∃ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂(μ : Measure (S → E)), ∀ f : (S → E) →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure (S → E)))) := by
  filter_upwards [ae_tendsto_finiteVolumeDistributions_weakly_of_mem_extremePoints_G
    γ hμ hmono hcof] with ω hω
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hω

/-- **Georgii (7.12)(b)** along the canonical exhaustion. -/
theorem ae_tendsto_finiteVolumeDistributions_exhaustion_weakly_of_mem_extremePoints_G
    {μ : ProbabilityMeasure (S → E)} (hμ : (μ : Measure (S → E)) ∈ (G γ).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure (S → E)),
      Tendsto (fun n ↦ finiteVolumeDistributions γ ω (exhaustionVolumes n)) atTop (𝓝 μ) :=
  ae_tendsto_finiteVolumeDistributions_weakly_of_mem_extremePoints_G γ hμ
    exhaustionVolumes_monotone exhaustionVolumes_cofinal

end PartB

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

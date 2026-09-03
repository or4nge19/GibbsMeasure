/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LocalContinuity
public import GibbsMeasure.Specification.Quasilocality
public import GibbsMeasure.Specification.Structure
public import GibbsMeasure.Specification.QuasilocalSpecification
public import GibbsMeasure.Topology.ClusterPoints
public import GibbsMeasure.Topology.LocalConvergence
public import GibbsMeasure.Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Existence of Gibbs measures (Georgii, Ch. 4)

The local-convergence backbone:

* `Specification.bindPM`: the finite-volume Gibbs distribution `ν γ_Λ` as a probability measure.
* `MeasureTheory.GibbsMeasure.mem_GP_of_tendsto_withLocalConvergence`: Georgii (4.17) — local
  limits of `ν_i γ^i_{Λ_i}` with `γ^i → γ` uniformly and `Λ_i ↑ S` are Gibbs for a quasilocal `γ`.
* `MeasureTheory.GibbsMeasure.IsLocalThermodynamicLimit.mem_GP`: Georgii (4.18) — thermodynamic
  limits of a quasilocal specification are Gibbs measures.
* `MeasureTheory.GibbsMeasure.exists_mem_GP_mapClusterPt`: Georgii (4.22) — a locally
  equicontinuous net of finite-volume Gibbs distributions has a cluster point in `GP γ`; in
  particular `GP γ ≠ ∅`.

The weak-topology results (Prokhorov/Feller) are kept separate and named `Weak`: weak compactness
is not silently identified with Georgii-local convergence.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

/-! ### Finite-volume Gibbs distributions as probability measures -/

namespace Specification

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}

-- kernels of a specification are measurable as functions into measures for the *full*
-- product σ-algebra (even though they are defined with `cylinderEvents (Λᶜ)` as source σ-algebra).
lemma measurable_kernel_toMeasure (γ : Specification S E) (Λ : Finset S) :
    @Measurable (S → E) (Measure (S → E)) MeasurableSpace.pi Measure.instMeasurableSpace (γ Λ) :=
  (Kernel.measurable (γ Λ)).mono
    (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl

/-- The kernel measurability `ω ↦ γ_Λ(B | ω)`, for the product σ-algebra. -/
lemma measurable_apply_kernel (γ : Specification S E) (Λ : Finset S) {B : Set (S → E)}
    (hB : MeasurableSet B) : Measurable fun ω ↦ γ Λ ω B :=
  (Measure.measurable_coe hB).comp (γ.measurable_kernel_toMeasure Λ)

lemma isProbabilityMeasure_bind (γ : Specification S E) (Λ : Finset S) (μ : Measure (S → E))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.bind (γ Λ)) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (γ.measurable_kernel_toMeasure Λ).aemeasurable]
  simp

/-- Bind a probability measure by a specification kernel (as a probability measure):
the finite-volume Gibbs distribution `ν γ_Λ`. -/
def bindPM (γ : Specification S E) (Λ : Finset S) (μ : ProbabilityMeasure (S → E)) :
    ProbabilityMeasure (S → E) :=
  ⟨(μ : Measure (S → E)).bind (γ Λ), γ.isProbabilityMeasure_bind Λ _⟩

@[simp] lemma coe_bindPM (γ : Specification S E) (Λ : Finset S)
    (μ : ProbabilityMeasure (S → E)) :
    (γ.bindPM Λ μ : Measure (S → E)) = (μ : Measure (S → E)).bind (γ Λ) :=
  rfl

/-- Consistency of the finite-volume Gibbs distributions: binding by a smaller volume is
absorbed (Georgii's `ν γ_Λ₂ γ_Λ₁ = ν γ_Λ₂` for `Λ₁ ⊆ Λ₂`). -/
lemma bind_bind_of_subset (γ : Specification S E) {Λ₁ Λ₂ : Finset S} (h : Λ₁ ⊆ Λ₂)
    (μ : Measure (S → E)) : (μ.bind (γ Λ₂)).bind (γ Λ₁) = μ.bind (γ Λ₂) := by
  rw [Measure.bind_bind (γ.measurable_kernel_toMeasure Λ₂).aemeasurable
    (γ.measurable_kernel_toMeasure Λ₁).aemeasurable]
  exact congrArg μ.bind (funext fun η ↦ Specification.bind (γ := γ) (hΛ := h) (η := η))

end Specification

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

variable (γ : Specification S E)

/-- The net of finite-volume Gibbs distributions with boundary condition `η`. -/
def finiteVolumeDistributions (η : S → E) :
    (Finset S) → ProbabilityMeasure (S → E) :=
  fun Λ ↦ ⟨γ Λ η, inferInstance⟩

/-- A probability measure is a *local thermodynamic limit* for boundary condition `η` if it is a
cluster point of the net `Λ ↦ γ Λ η` in the topology of local convergence — the notion of
Georgii's Comment (4.18), which proves every such limit Gibbs (`IsLocalThermodynamicLimit.mem_GP`).
-/
def IsLocalThermodynamicLimit (η : S → E) (μ : ProbabilityMeasure (S → E)) : Prop :=
  ClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E)
    (Filter.map (fun Λ ↦ (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ η Λ) :
      WithLocalConvergence S E)) Filter.atTop)

variable {γ}

/-- Fixed-point characterization of Gibbs probability measures, expressed using `bindPM`. -/
lemma mem_GP_iff_forall_bindPM_eq (μ : ProbabilityMeasure (S → E)) :
    μ ∈ GP (S := S) (E := E) γ ↔ ∀ Λ : Finset S, γ.bindPM Λ μ = μ := by
  constructor
  · intro hμ
    have hμ' : ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
      have hGibbs : γ.IsGibbsMeasure (μ : Measure (S → E)) := hμ
      simpa [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)] using hGibbs
    intro Λ
    exact Subtype.ext (by simpa [Specification.coe_bindPM] using hμ' Λ)
  · intro hfix
    have hfix' : ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) :=
      fun Λ ↦ by
        simpa [Specification.coe_bindPM] using
          congrArg (fun ν : ProbabilityMeasure (S → E) ↦ (ν : Measure (S → E))) (hfix Λ)
    exact show γ.IsGibbsMeasure (μ : Measure (S → E)) by
      simpa [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)] using hfix'

/-! ### Georgii (4.17): local limits of finite-volume Gibbs distributions are Gibbs -/

section LocalLimits

/-- Integrating the action of `γ'` on the indicator of `A` recovers the finite-volume Gibbs
distribution: `∫ γ'_Λ 1_A dμ = (μ γ'_Λ)(A)`. -/
lemma integral_action_indicatorLp (γ' : Specification S E) (Λ : Finset S)
    (μ : Measure (S → E)) [IsProbabilityMeasure μ] {A : Set (S → E)} (hA : MeasurableSet A) :
    ∫ η, (Specification.action γ' Λ (indicatorLp A) : (S → E) → ℝ) η ∂μ
      = ((μ.bind (γ' Λ)) A).toReal := by
  have hker : Measurable fun η ↦ (γ' Λ) η A :=
    ((γ' Λ).measurable_coe hA).mono
      (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ))) le_rfl
  have hptw : ∀ η, (Specification.action γ' Λ (indicatorLp A) : (S → E) → ℝ) η
      = ((γ' Λ) η A).toReal := by
    intro η
    rw [Specification.action_apply]
    rw [show ⇑(indicatorLp (S := S) (E := E) A) = A.indicator (fun _ ↦ (1 : ℝ)) from rfl,
      integral_indicator_const (1 : ℝ) hA]
    simp [measureReal_def]
  calc ∫ η, (Specification.action γ' Λ (indicatorLp A) : (S → E) → ℝ) η ∂μ
      = ∫ η, ((γ' Λ) η A).toReal ∂μ := by simp only [hptw]
    _ = (∫⁻ η, (γ' Λ) η A ∂μ).toReal :=
        integral_toReal hker.aemeasurable
          (.of_forall fun η ↦ lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)
    _ = ((μ.bind (γ' Λ)) A).toReal := by
        rw [Measure.bind_apply hA (γ'.measurable_kernel_toMeasure Λ).aemeasurable]

/-- Integrals of bounded measurable observables against a probability measure differ by at most
the uniform distance. -/
private lemma abs_integral_sub_integral_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {h h' : lp (fun _ : S → E ↦ ℝ) ∞} (hh : Measurable (⇑h)) (hh' : Measurable (⇑h')) :
    |(∫ x, (h : (S → E) → ℝ) x ∂μ) - ∫ x, (h' : (S → E) → ℝ) x ∂μ| ≤ dist h h' := by
  rw [← integral_sub (lp.integrable_of_measurable hh μ) (lp.integrable_of_measurable hh' μ),
    dist_eq_norm]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖h - h'‖)
    (f := fun x ↦ (h : (S → E) → ℝ) x - (h' : (S → E) → ℝ) x)
    (.of_forall fun x ↦ by
      have := lp.norm_apply_le_norm ENNReal.top_ne_zero (h - h') x
      rwa [lp.coeFn_sub, Pi.sub_apply] at this)
  simpa [Real.norm_eq_abs] using h

/-- **Georgii Theorem (4.17).** Let `γ` be a quasilocal specification, `(γ^i)` specifications
converging to `γ` uniformly on local observables, `(Λ_i)` volumes tending to `S`, and `(ν_i)`
arbitrary boundary fields. If the finite-volume Gibbs distributions `ν_i γ^i_{Λ_i}` converge
locally to `μ`, then `μ` is a Gibbs measure for `γ`. -/
theorem mem_GP_of_tendsto_withLocalConvergence {ι : Type*} {l : Filter ι} [l.NeBot]
    (hγ : γ.IsQuasilocal)
    {γs : ι → Specification S E} {Λs : ι → Finset S} {νs : ι → ProbabilityMeasure (S → E)}
    {μ : ProbabilityMeasure (S → E)} (hΛs : Tendsto Λs l atTop)
    (hunif : ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun i ↦ dist ((γs i).action Λ f) (γ.action Λ f)) l (𝓝 0))
    (hconv : Tendsto (fun i ↦ (WithSetwiseTopology.ofMeasure ((γs i).bindPM (Λs i) (νs i)) :
        WithLocalConvergence S E)) l
      (𝓝 (WithSetwiseTopology.ofMeasure μ))) :
    μ ∈ GP (S := S) (E := E) γ := by
  classical
  rw [mem_GP_iff_forall_bindPM_eq]
  intro Λ
  suffices key : (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) from
    Subtype.ext key
  haveI hbp : IsProbabilityMeasure ((μ : Measure (S → E)).bind (γ Λ)) :=
    γ.isProbabilityMeasure_bind Λ _
  refine separatesOn_localEvents hbp inferInstance fun A hA ↦ ?_
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  set P : ι → Measure (S → E) := fun i ↦ ((γs i).bindPM (Λs i) (νs i) : Measure (S → E))
    with hP
  haveI hPprob : ∀ i, IsProbabilityMeasure (P i) := fun i ↦
    ((γs i).bindPM (Λs i) (νs i)).2
  -- the quasilocal observable `γ_Λ 1_A`
  have hfloc : indicatorLp A ∈ localFunctions S E := indicatorLp_mem_localFunctions hA
  have hfmeas : Measurable (⇑(indicatorLp (S := S) (E := E) A)) := by
    rw [coeFn_indicatorLp]; exact measurable_const.indicator hAmeas
  set g : lp (fun _ : S → E ↦ ℝ) ∞ := Specification.action γ Λ (indicatorLp A) with hg
  have hgql : g ∈ quasilocalFunctions S E :=
    hγ Λ _ (localFunctions_le_quasilocalFunctions hfloc)
  have hgmeas : Measurable (⇑g) := Specification.measurable_action hfmeas
  -- convergence of `∫ γ_Λ 1_A` along the net, by `L`-continuity (Georgii (4.3)(2))
  have h1 : Tendsto (fun i ↦ ∫ x, (g : (S → E) → ℝ) x ∂(P i)) l
      (𝓝 (∫ x, (g : (S → E) → ℝ) x ∂(μ : Measure (S → E)))) :=
    ((lContinuous_of_mem_quasilocalFunctions hgql).tendsto _).comp hconv
  -- the `i`-th action differs from `γ_Λ 1_A` by at most the uniform distance
  have hdiff : Tendsto (fun i ↦ (∫ x, (g : (S → E) → ℝ) x ∂(P i))
      - ∫ x, ((γs i).action Λ (indicatorLp A) : (S → E) → ℝ) x ∂(P i)) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i ↦ ?_) (hunif Λ hfloc)
    have := abs_integral_sub_integral_le (μ := P i) (h := g)
      (h' := (γs i).action Λ (indicatorLp A)) hgmeas
      (Specification.measurable_action (γ := γs i) (Λ := Λ) hfmeas)
    rw [Real.norm_eq_abs]
    exact le_trans this (by rw [dist_comm])
  have h2 : Tendsto (fun i ↦ ∫ x, ((γs i).action Λ (indicatorLp A) : (S → E) → ℝ) x ∂(P i)) l
      (𝓝 (∫ x, (g : (S → E) → ℝ) x ∂(μ : Measure (S → E)))) := by
    have := h1.sub hdiff
    simpa using this
  -- eventually, the `i`-th action integrates to the measure of `A` (consistency)
  have hev : ∀ᶠ i in l, (∫ x, ((γs i).action Λ (indicatorLp A) : (S → E) → ℝ) x ∂(P i))
      = ((P i) A).toReal := by
    filter_upwards [hΛs.eventually (eventually_ge_atTop Λ)] with i hi
    rw [integral_action_indicatorLp (γs i) Λ (P i) hAmeas, hP]
    simp only [Specification.coe_bindPM]
    rw [(γs i).bind_bind_of_subset hi]
  -- evaluations on `A` converge
  have h3 : Tendsto (fun i ↦ ((P i) A).toReal) l (𝓝 (((μ : Measure (S → E)) A).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hconv A hA)
  -- identify the two limits
  have h4 : Tendsto (fun i ↦ ∫ x, ((γs i).action Λ (indicatorLp A) : (S → E) → ℝ) x ∂(P i)) l
      (𝓝 (((μ : Measure (S → E)) A).toReal)) :=
    h3.congr' (hev.mono fun i hi ↦ hi.symm)
  have hreal : ∫ x, (g : (S → E) → ℝ) x ∂(μ : Measure (S → E))
      = (((μ : Measure (S → E)) A)).toReal := tendsto_nhds_unique h2 h4
  have hbind : ∫ x, (g : (S → E) → ℝ) x ∂(μ : Measure (S → E))
      = (((μ : Measure (S → E)).bind (γ Λ)) A).toReal :=
    integral_action_indicatorLp γ Λ (μ : Measure (S → E)) hAmeas
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1
    (hbind.symm.trans hreal)

/-- **Georgii Theorem (4.17), cluster-point form.** Every cluster point of a net of finite-volume
Gibbs distributions `ν_i γ^i_{Λ_i}` with `γ^i → γ` uniformly and `Λ_i ↑ S` is a Gibbs measure for
a quasilocal `γ` (the form used in Georgii's (4.18), (4.20) and (4.23)(c)). -/
theorem mem_GP_of_mapClusterPt {ι : Type*} {l : Filter ι} [l.NeBot] (hγ : γ.IsQuasilocal)
    {γs : ι → Specification S E} {Λs : ι → Finset S} {νs : ι → ProbabilityMeasure (S → E)}
    {μ : ProbabilityMeasure (S → E)} (hΛs : Tendsto Λs l atTop)
    (hunif : ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun i ↦ dist ((γs i).action Λ f) (γ.action Λ f)) l (𝓝 0))
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      (fun i ↦ WithSetwiseTopology.ofMeasure ((γs i).bindPM (Λs i) (νs i)))) :
    μ ∈ GP (S := S) (E := E) γ := by
  obtain ⟨U, hUle, hUconv⟩ := mapClusterPt_iff_ultrafilter.1 hcp
  exact mem_GP_of_tendsto_withLocalConvergence (l := (U : Filter ι)) hγ
    (hΛs.mono_left hUle) (fun Λ f hf ↦ (hunif Λ hf).mono_left hUle) hUconv

/-- **Georgii Comment (4.18).** Every local thermodynamic limit of a quasilocal specification is a
Gibbs measure: the answer to problem (II) of Georgii's Chapter 4 introduction. -/
theorem IsLocalThermodynamicLimit.mem_GP (hγ : γ.IsQuasilocal) {η : S → E}
    {μ : ProbabilityMeasure (S → E)} (hμ : IsLocalThermodynamicLimit γ η μ) :
    μ ∈ GP (S := S) (E := E) γ := by
  have hdirac : ∀ Λ : Finset S,
      γ.bindPM Λ ⟨Measure.dirac η, inferInstance⟩ = finiteVolumeDistributions γ η Λ := by
    intro Λ
    exact Subtype.ext (Measure.dirac_bind (γ.measurable_kernel_toMeasure Λ) η)
  refine mem_GP_of_mapClusterPt (l := (atTop : Filter (Finset S))) hγ
    (γs := fun _ ↦ γ) (Λs := id) (νs := fun _ ↦ ⟨Measure.dirac η, inferInstance⟩)
    tendsto_id (fun Λ f _ ↦ by simpa using tendsto_const_nhds) ?_
  have hfun : (fun Λ : Finset S ↦
      (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ η Λ) :
        WithLocalConvergence S E))
      = fun Λ : Finset S ↦ (WithSetwiseTopology.ofMeasure
        (γ.bindPM (id Λ) ⟨Measure.dirac η, inferInstance⟩) : WithLocalConvergence S E) :=
    funext fun Λ ↦ by rw [id_eq, hdirac Λ]
  exact hfun ▸ hμ

/-! ### Georgii (4.22): existence of Gibbs measures -/

/-- **Georgii Theorem (4.22).** Over a standard Borel state space, if `γ` is quasilocal,
`γ^i → γ` uniformly on local observables, `Λ_i ↑ S`, and the net of finite-volume Gibbs
distributions `ν_i γ^i_{Λ_i}` is locally equicontinuous, then `GP γ` contains a cluster point of
the net, and is therefore non-empty. -/
theorem exists_mem_GP_mapClusterPt [StandardBorelSpace E] {ι : Type*} {l : Filter ι} [l.NeBot]
    (hγ : γ.IsQuasilocal)
    {γs : ι → Specification S E} {Λs : ι → Finset S} {νs : ι → ProbabilityMeasure (S → E)}
    (hΛs : Tendsto Λs l atTop)
    (hunif : ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun i ↦ dist ((γs i).action Λ f) (γ.action Λ f)) l (𝓝 0))
    (hle : LocallyEquicontinuous l fun i ↦ (γs i).bindPM (Λs i) (νs i)) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
        (fun i ↦ WithSetwiseTopology.ofMeasure ((γs i).bindPM (Λs i) (νs i))) := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le l
  obtain ⟨μlim, hμlim⟩ := exists_tendsto_of_locallyEquicontinuous
    (μs := fun i ↦ (WithSetwiseTopology.ofMeasure ((γs i).bindPM (Λs i) (νs i)) :
      WithLocalConvergence S E)) U hU hle
  refine ⟨μlim.toMeasure, ?_, ?_⟩
  · exact mem_GP_of_tendsto_withLocalConvergence (l := (U : Filter ι)) hγ
      (hΛs.mono_left hU) (fun Λ f hf ↦ (hunif Λ hf).mono_left hU) hμlim
  · exact mapClusterPt_iff_ultrafilter.2 ⟨U, hU, hμlim⟩

/-- **Georgii (4.22), single-specification form.** A quasilocal specification whose net of
finite-volume Gibbs distributions with boundary condition `η` is locally equicontinuous has a
Gibbs measure, obtained as a local thermodynamic limit. -/
theorem exists_isLocalThermodynamicLimit_mem_GP [StandardBorelSpace E]
    (hγ : γ.IsQuasilocal) (η : S → E)
    (hle : LocallyEquicontinuous atTop (finiteVolumeDistributions γ η)) :
    ∃ μ ∈ GP (S := S) (E := E) γ, IsLocalThermodynamicLimit γ η μ := by
  haveI : NeBot (Filter.atTop : Filter (Finset S)) := inferInstance
  have hdirac : ∀ Λ : Finset S,
      γ.bindPM Λ ⟨Measure.dirac η, inferInstance⟩ = finiteVolumeDistributions γ η Λ := by
    intro Λ
    exact Subtype.ext (Measure.dirac_bind (γ.measurable_kernel_toMeasure Λ) η)
  have hle' : LocallyEquicontinuous (atTop : Filter (Finset S))
      (fun Λ : Finset S ↦ γ.bindPM (id Λ) (⟨Measure.dirac η, inferInstance⟩ :
        ProbabilityMeasure (S → E))) := by
    have hfun : (fun Λ : Finset S ↦ γ.bindPM (id Λ) (⟨Measure.dirac η, inferInstance⟩ :
        ProbabilityMeasure (S → E))) = finiteVolumeDistributions γ η :=
      funext fun Λ ↦ hdirac Λ
    rw [hfun]; exact hle
  obtain ⟨μ, hμGP, hμcp⟩ := exists_mem_GP_mapClusterPt (l := (atTop : Filter (Finset S))) hγ
    (γs := fun _ ↦ γ) (Λs := id) (νs := fun _ ↦ ⟨Measure.dirac η, inferInstance⟩)
    tendsto_id (fun Λ f _ ↦ by simpa using tendsto_const_nhds) hle'
  refine ⟨μ, hμGP, ?_⟩
  have := hμcp
  simp only [id_eq, hdirac] at this
  exact this

/-- A uniform bound on the kernels of a smaller volume passes to every finite-volume Gibbs
distribution of a larger volume, by consistency. -/
lemma finiteVolumeDistributions_apply_le {Λ Λ' : Finset S} (h : Λ ⊆ Λ') (η : S → E)
    {A : Set (S → E)} (hA : MeasurableSet A) {c : ℝ≥0∞} (hc : ∀ ω, γ Λ ω A ≤ c) :
    (finiteVolumeDistributions γ η Λ' : Measure (S → E)) A ≤ c := by
  change (γ Λ' η) A ≤ c
  rw [← Specification.bind (γ := γ) (hΛ := h) (η := η),
    Measure.bind_apply hA (γ.measurable_kernel_toMeasure Λ).aemeasurable]
  calc ∫⁻ ω, γ Λ ω A ∂(γ Λ' η) ≤ ∫⁻ _, c ∂(γ Λ' η) := lintegral_mono hc
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

/-- A Gibbs measure inherits every uniform bound on its specification's kernels. -/
lemma apply_le_of_mem_GP {μ : ProbabilityMeasure (S → E)}
    (hμ : μ ∈ GP (S := S) (E := E) γ) (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : ∀ ω, γ Λ ω A ≤ c) : (μ : Measure (S → E)) A ≤ c := by
  have hfix : (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
    have := congrArg (fun ν : ProbabilityMeasure (S → E) ↦ (ν : Measure (S → E)))
      ((mem_GP_iff_forall_bindPM_eq μ).1 hμ Λ)
    simpa [Specification.coe_bindPM] using this
  rw [← hfix, Measure.bind_apply hA (γ.measurable_kernel_toMeasure Λ).aemeasurable]
  calc ∫⁻ ω, γ Λ ω A ∂(μ : Measure (S → E)) ≤ ∫⁻ _, c ∂(μ : Measure (S → E)) :=
      lintegral_mono hc
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

/-- For a quasilocal specification, the Gibbs measures form a closed set in the topology of local
convergence: the closedness in Georgii (4.23)(a), via Theorem (4.17) applied to the product net
`(ν, Λ) ↦ ν γ_Λ` (Georgii's directed set `D̄ = D × 𝒮`). -/
theorem isClosed_setOf_mem_GP (hγ : γ.IsQuasilocal) :
    IsClosed {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ} := by
  rw [isClosed_iff_clusterPt]
  intro μ hcp
  set G : Set (WithLocalConvergence S E) :=
    {ν : WithLocalConvergence S E | ν.toMeasure ∈ GP (S := S) (E := E) γ} with hG
  haveI hne : NeBot (𝓝 μ ⊓ 𝓟 G) := hcp
  haveI : NeBot ((𝓝 μ ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) :=
    Filter.prod_neBot.2 ⟨hne, inferInstance⟩
  change μ.toMeasure ∈ GP (S := S) (E := E) γ
  refine mem_GP_of_tendsto_withLocalConvergence
    (l := (𝓝 μ ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) hγ
    (γs := fun _ ↦ γ) (Λs := Prod.snd) (νs := fun p ↦ (p.1).toMeasure)
    tendsto_snd (fun Λ f _ ↦ by simpa using tendsto_const_nhds) ?_
  have hev : ∀ᶠ p : WithLocalConvergence S E × Finset S in
      (𝓝 μ ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S)),
      (WithSetwiseTopology.ofMeasure (γ.bindPM p.2 (p.1).toMeasure) :
        WithLocalConvergence S E) = p.1 := by
    have h1 : ∀ᶠ ν in 𝓝 μ ⊓ 𝓟 G, ν ∈ G :=
      (inf_le_right : 𝓝 μ ⊓ 𝓟 G ≤ 𝓟 G) (Filter.mem_principal_self G)
    filter_upwards [h1.prod_inl (atTop : Filter (Finset S))] with p hp
    rw [(mem_GP_iff_forall_bindPM_eq (γ := γ) (p.1).toMeasure).1 hp p.2]
  have hfst : Tendsto (fun p : WithLocalConvergence S E × Finset S ↦ p.1)
      ((𝓝 μ ⊓ 𝓟 G) ×ˢ (atTop : Filter (Finset S))) (𝓝 μ) :=
    tendsto_fst.mono_right inf_le_left
  exact hfst.congr' (hev.mono fun p hp ↦ hp.symm)

/-- **Georgii Example (4.11)(1).** The Gibbs measures of a modification of the independent
specification by uniformly bounded densities form a relatively compact set in the topology of
local convergence. -/
theorem isCompact_closure_setOf_mem_GP_modification [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (Specification.isssd ν).IsModifier ρ)
    {C : Finset S → ℝ≥0∞} (hC : ∀ Λ, C Λ ≠ ∞) (hbdd : ∀ Λ η, ρ Λ η ≤ C Λ) :
    IsCompact (closure {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E) ((Specification.isssd ν).modification ρ hρ)}) := by
  set νdom : Finset S → Measure (S → E) := fun Λ ↦ C Λ • Measure.infinitePi (fun _ : S ↦ ν)
    with hνdom
  have : ∀ Λ, IsFiniteMeasure (νdom Λ) := fun Λ ↦ ⟨by
    rw [hνdom, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact (hC Λ).lt_top⟩
  refine IsCompact.of_isClosed_subset (isCompact_dominatedBy νdom) isClosed_closure ?_
  refine closure_minimal ?_ (isClosed_dominatedBy νdom)
  intro μ hμ Λ A hA
  refine apply_le_of_mem_GP hμ Λ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) fun ω ↦ ?_
  rw [hνdom]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc ((Specification.isssd ν).modification ρ hρ) Λ ω A
      ≤ C Λ * Specification.isssd ν Λ ω A :=
        Specification.modification_apply_le _ ρ hρ Λ ω
          (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) (fun ω' ↦ hbdd Λ ω')
    _ = C Λ * Measure.infinitePi (fun _ : S ↦ ν) A := by
        rw [Specification.isssd_apply_of_mem_cylinderEvents ν Λ ω hA]

end LocalLimits

/-! ### Existence on compact spaces via Prokhorov + Feller continuity (weak topology) -/

section WeakCompact

open scoped Topology BoundedContinuousFunction
open BoundedContinuousFunction

variable {S E : Type*} [MeasurableSpace E] [TopologicalSpace E]

-- Weak topology on probability measures requires measurable open sets in configuration space.
variable [OpensMeasurableSpace (S → E)]

variable {γ : Specification S E}

/-- A weak-topology cluster point of the finite-volume net; not Georgii's local-convergence
notion. -/
def IsWeakThermodynamicLimit (γ : Specification S E) (η : S → E)
    (μ : ProbabilityMeasure (S → E)) : Prop :=
  ClusterPt μ (Filter.map (finiteVolumeDistributions γ η) Filter.atTop)

variable [γ.IsFeller]

-- Lean 4.34 does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`) during `isDefEq`.
set_option backward.isDefEq.respectTransparency false in
/-- Feller continuity: `μ ↦ μ γ_Λ` is continuous for the weak topology on probability
measures. -/
theorem _root_.Specification.continuous_bindPM (Λ : Finset S) :
    Continuous (γ.bindPM Λ : ProbabilityMeasure (S → E) → ProbabilityMeasure (S → E)) := by
  refine (MeasureTheory.ProbabilityMeasure.continuous_iff_forall_continuous_integral
    (μs := (γ.bindPM Λ))).2 ?_
  intro f
  let g : BoundedContinuousFunction (S → E) ℝ :=
    ProbabilityTheory.Kernel.continuousAction (κ := γ Λ) f
  have hg : Continuous fun μ : ProbabilityMeasure (S → E) => ∫ x, g x ∂(μ : Measure (S → E)) := by
    simpa using
      (MeasureTheory.ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f := g)
        (X := (S → E)))
  have hEq :
      (fun μ : ProbabilityMeasure (S → E) =>
          ∫ x, f x ∂((μ : Measure (S → E)).bind (γ Λ)))
        =
      (fun μ : ProbabilityMeasure (S → E) =>
          ∫ x, g x ∂(μ : Measure (S → E))) := by
    funext μ
    haveI : IsProbabilityMeasure ((μ : Measure (S → E)).bind (γ Λ)) :=
      γ.isProbabilityMeasure_bind Λ _
    have hf_int : Integrable (fun x : S → E => f x) ((μ : Measure (S → E)).bind (γ Λ)) := by
      simpa using (BoundedContinuousFunction.integrable (μ := (μ : Measure (S → E)).bind (γ Λ)) f)
    haveI : IsMarkovKernel ((γ Λ).comap id (MeasureTheory.cylinderEvents_le_pi
        (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))) :=
      Kernel.IsMarkovKernel.comap _ _
    have := Measure.integral_bind (κ := (γ Λ).comap id (MeasureTheory.cylinderEvents_le_pi
      (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))) (μ := (μ : Measure (S → E))) hf_int
    simpa [g, ProbabilityTheory.Kernel.continuousAction_apply] using this
  simpa [Specification.bindPM, Specification.coe_bindPM, hEq] using hg

variable [T2Space (ProbabilityMeasure (S → E))]

/-- Any **weak** thermodynamic limit of finite-volume distributions is a Gibbs measure. This is a
weak-topology closure theorem, not the full Georgii local/quasilocal existence theorem. -/
theorem isGibbsMeasure_of_isWeakThermodynamicLimit
    (η : S → E) {μ : ProbabilityMeasure (S → E)}
    (hμ : IsWeakThermodynamicLimit γ η μ) :
    μ ∈ GP (S := S) (E := E) γ := by
  rw [mem_GP_iff_forall_bindPM_eq]
  intro Λ
  -- Work with the cluster-point filter `𝓝 μ ⊓ F`.
  let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions γ η
  let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (Filter.atTop)
  have h_ne : NeBot (𝓝 μ ⊓ F) := hμ
  have hcont : Continuous (γ.bindPM Λ :
      ProbabilityMeasure (S → E) → ProbabilityMeasure (S → E)) :=
    Specification.continuous_bindPM (γ := γ) Λ
  have h_event_F : ∀ᶠ ν in F, γ.bindPM Λ ν = ν := by
    have h_event_atTop :
        ∀ᶠ Λ' in (Filter.atTop : Filter (Finset S)), γ.bindPM Λ (μs Λ') = μs Λ' := by
      refine Filter.eventually_atTop.2 ⟨Λ, fun Λ' hΛ ↦ ?_⟩
      apply Subtype.ext
      simpa [μs, finiteVolumeDistributions, Specification.bindPM, Specification.coe_bindPM] using
        (_root_.Specification.bind (γ := γ) (hΛ := hΛ) (η := η))
    simpa [F, μs] using h_event_atTop
  have h_event : ∀ᶠ ν in (𝓝 μ ⊓ F), γ.bindPM Λ ν = ν :=
    (inf_le_right : (𝓝 μ ⊓ F) ≤ F) h_event_F
  have hid : Tendsto id (𝓝 μ ⊓ F) (𝓝 μ) :=
    (tendsto_id'.2 (inf_le_left : (𝓝 μ ⊓ F) ≤ 𝓝 μ))
  have hbind_to_μ : Tendsto (γ.bindPM Λ) (𝓝 μ ⊓ F) (𝓝 μ) :=
    hid.congr' (h_event.mono fun ν hν => by simpa [id, Function.id_def] using hν.symm)
  have hbind_to_bindμ : Tendsto (γ.bindPM Λ) (𝓝 μ ⊓ F) (𝓝 (γ.bindPM Λ μ)) :=
    (hcont.tendsto μ).mono_left inf_le_left
  exact tendsto_nhds_unique hbind_to_bindμ hbind_to_μ

section Compact

variable [CompactSpace E] [BorelSpace E] [SecondCountableTopology E] [Countable S] [T2Space E]

/-- Existence of a Gibbs measure on a **compact** single-spin space, via weak compactness of
`ProbabilityMeasure (S → E)` and weak closure of the Gibbs fixed-point equations. This is a
weak-topology argument; it is not a replacement for Georgii's local/quasilocal theorem. -/
theorem existence_of_gibbsMeasure_compact_weak (η : S → E) :
    (GP (S := S) (E := E) γ).Nonempty := by
  classical
  haveI : CompactSpace (ProbabilityMeasure (S → E)) := by infer_instance
  let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions γ η
  let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (Filter.atTop)
  haveI : NeBot F := Filter.map_neBot
  obtain ⟨μ, hμ⟩ : ∃ μ : ProbabilityMeasure (S → E), ClusterPt μ F :=
    exists_clusterPt_of_compactSpace F
  exact ⟨μ, isGibbsMeasure_of_isWeakThermodynamicLimit (η := η) hμ⟩

end Compact

/-! ### Existence from tightness (Prokhorov, weak topology) -/

section Tight

variable [T2Space (S → E)] [BorelSpace (S → E)]

/-- Existence of a Gibbs measure from **tightness** of the finite-volume distributions, using weak
Prokhorov compactness of the closure of a tight set. This statement is explicitly formulated in
the weak topology. -/
theorem existence_of_gibbsMeasure_of_isTight_weak
    (η : S → E)
    (hT :
      IsTightMeasureSet
        {x : Measure (S → E) |
          ∃ μ ∈ Set.range (finiteVolumeDistributions γ η),
            (μ : Measure (S → E)) = x}) :
    (GP (S := S) (E := E) γ).Nonempty := by
  classical
  -- Apply Prokhorov: closure of a tight set of probability measures is compact.
  let μs : Finset S → ProbabilityMeasure (S → E) := finiteVolumeDistributions γ η
  let Sset : Set (ProbabilityMeasure (S → E)) := Set.range μs
  have hcompact : IsCompact (closure Sset) := by
    simpa [Sset] using
      (isCompact_closure_of_isTightMeasureSet (E := (S → E)) (S := Sset) (hS := hT))
  let F : Filter (ProbabilityMeasure (S → E)) := Filter.map μs (Filter.atTop)
  haveI : NeBot F := Filter.map_neBot
  have hF_le : F ≤ 𝓟 (closure Sset) := by
    have hF_range : F ≤ 𝓟 (Set.range μs) := by
      intro s hs
      have hsub : Set.range μs ⊆ s := hs
      have hpre : μs ⁻¹' s = (Set.univ : Set (Finset S)) := by
        ext Λ
        exact ⟨fun _ ↦ trivial, fun _ ↦ hsub ⟨Λ, rfl⟩⟩
      change s ∈ Filter.map μs Filter.atTop
      rw [Filter.mem_map, hpre]
      exact Filter.univ_mem
    exact hF_range.trans (Filter.principal_mono.2 subset_closure)
  obtain ⟨μ, _hμ_mem, hμ⟩ : ∃ μ ∈ closure Sset, ClusterPt μ F :=
    hcompact.exists_clusterPt (f := F) hF_le
  exact ⟨μ, isGibbsMeasure_of_isWeakThermodynamicLimit (η := η) hμ⟩

end Tight

/-! ### Topological properties of `GP(γ)` (weak topology) -/

section GPTopology

/-- `GP(γ)` is closed in the weak topology, provided `γ` is Feller. -/
theorem isClosed_GP : IsClosed (GP (S := S) (E := E) γ) := by
  classical
  have hGP : GP (S := S) (E := E) γ =
      ⋂ Λ : Finset S, {μ : ProbabilityMeasure (S → E) | γ.bindPM Λ μ = μ} := by
    ext μ
    simp [mem_GP_iff_forall_bindPM_eq (γ := γ) μ]
  have hclosed : ∀ Λ : Finset S,
      IsClosed {μ : ProbabilityMeasure (S → E) | γ.bindPM Λ μ = μ} := fun Λ ↦ by
    simpa using isClosed_eq (Specification.continuous_bindPM (γ := γ) Λ) continuous_id
  simpa [hGP] using isClosed_iInter hclosed

/-- If the ambient space of probability measures is compact, then `GP(γ)` is compact
(`GP(γ)` is closed by `isClosed_GP`). -/
theorem isCompact_GP [CompactSpace (ProbabilityMeasure (S → E))] :
    IsCompact (GP (S := S) (E := E) γ) :=
  (isClosed_GP (γ := γ)).isCompact

end GPTopology

end WeakCompact

end GibbsMeasure

end MeasureTheory

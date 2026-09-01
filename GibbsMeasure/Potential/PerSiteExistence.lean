/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Equivalence
public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Specification.InhomogeneousReference

/-!
# Existence over per-site a priori measures

Georgii Theorem (4.23)(a) with the single a priori measure `λ` replaced by a family `(λ_i)`, one
probability measure per site: the case needed for the existence half of Theorem (8.39), where the
self-energies `Φ_{i}` absorbed into the reference measure are site-dependent.

Georgii's proof carries over verbatim once the two inputs are stated at the right generality: the
reference specification only has to resample volumes (`Specification.IsResampling`, for
quasilocality) and to forget the boundary condition on inside-volume events
(`Specification.HasFreeMeasure`, for local equicontinuity).

## Main statements

* `Potential.gibbsSpecificationFamily`: Georgii Definition (2.9) over `Specification.isssdFamily`.
* `Potential.GP_gibbsSpecificationFamily_nonempty`: Georgii (4.23)(a).
* `Potential.isCompact_setOf_mem_GP_gibbsSpecificationFamily`: its compactness half.
* `Potential.selfEnergyWeight`, `Potential.lambdaSpecification_eq_gibbsSpecificationFamily`: the
  transport of Georgii's reduction — the λ-specification of `Φ` is the specification of the
  recentred many-body part of `Φ` over the per-site measures `e^{-β Φ_{i}} λ`, normalized.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Potential

section Family

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]
  (ν : S → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (β : ℝ)

variable (Φ) in
/-- **Georgii Definition (2.9) over a family of a priori measures.** The Gibbsian specification of
an absolutely summable potential relative to `Specification.isssdFamily ν`. -/
def gibbsSpecificationFamily : Specification S E :=
  Specification.premodification (Specification.isssdFamily ν) (Φ.boltzmannFactor β)
    (Specification.isResampling_isssdFamily ν) (isPremodifier_boltzmannFactor (Φ := Φ) β)
    (isRelAdmissible_boltzmannFactor (γ := Specification.isssdFamily ν) β)

lemma gibbsSpecificationFamily_apply (Λ : Finset S) (η : S → E) :
    gibbsSpecificationFamily Φ ν β Λ η
      = (Specification.isssdFamily ν Λ η).withDensity
          (Specification.relNorm (Specification.isssdFamily ν) (Φ.boltzmannFactor β) Λ) := rfl

lemma gibbsSpecificationFamily_const (lam : Measure E) [IsProbabilityMeasure lam] :
    gibbsSpecificationFamily Φ (fun _ ↦ lam) β
      = Φ.gibbsSpecificationOfAbsolutelySummable lam β := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun η ↦ ?_
  rw [gibbsSpecificationFamily_apply, show Specification.isssdFamily (S := S) (E := E)
    (fun _ ↦ lam) = Specification.isssd lam from Specification.isssdFamily_const lam]
  rfl

/-- **Georgii Example (2.25)(ii)** over a family of a priori measures. -/
theorem isQuasilocal_gibbsSpecificationFamily :
    (gibbsSpecificationFamily Φ ν β).IsQuasilocal := by
  rw [gibbsSpecificationFamily, Specification.premodification]
  simp only [boltzmannFactor_eq_ofReal_boltzmann (Φ := Φ) β]
  exact (Specification.isResampling_isssdFamily ν).isQuasilocal_modification_relNorm
    (H := fun Λ ↦ β • Φ.hamiltonianLp Λ)
    (fun Λ ↦ Subalgebra.smul_mem _ (hamiltonianLp_mem_quasilocalFunctions (Φ := Φ) Λ) β) _

/-- **Georgii (4.14)(1)** over a family of a priori measures: on `𝓕_Λ`-events the specification is
dominated by `e^{2|β| ‖Φ‖_Λ}` times the free measure `⨂ i, ν i`. -/
lemma gibbsSpecificationFamily_apply_le (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    gibbsSpecificationFamily Φ ν β Λ η A
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) * Measure.infinitePi ν A := by
  rw [gibbsSpecificationFamily_apply, withDensity_apply _ (cylinderEvents_le_pi _ hA),
    ← Specification.isssdFamily_apply_of_mem_cylinderEvents ν Λ η hA, ← setLIntegral_const]
  exact setLIntegral_mono_ae (by fun_prop)
    (.of_forall fun x _ ↦ relNorm_boltzmannFactor_le (Φ := Φ) β Λ x)

variable (Φ) in
/-- The dominating measures of Georgii (4.14)(1) for the per-site family. -/
def dominatingMeasureFamily (Λ : Finset S) : Measure (S → E) :=
  ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) • Measure.infinitePi ν

instance (Λ : Finset S) : IsFiniteMeasure (dominatingMeasureFamily Φ ν β Λ) := by
  constructor
  rw [dominatingMeasureFamily, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

/-- **Georgii Comment (4.14)(1)** over a family of a priori measures. -/
theorem locallyEquicontinuous_finiteVolumeDistributionsFamily (η : S → E) :
    LocallyEquicontinuous atTop
      (finiteVolumeDistributions (gibbsSpecificationFamily Φ ν β) η) := by
  refine locallyEquicontinuous_of_eventually_boundedOn
    (Specification.hasFreeMeasure_isssdFamily ν)
    (fun _ ↦ Specification.relNorm (Specification.isssdFamily ν) (Φ.boltzmannFactor β))
    (fun _ ↦ (isPremodifier_boltzmannFactor (Φ := Φ) β).isModifier_relNorm
      (Specification.isResampling_isssdFamily ν)
      (isRelAdmissible_boltzmannFactor (γ := Specification.isssdFamily ν) β))
    id tendsto_id (fun _ ↦ ⟨Measure.dirac η, inferInstance⟩) _ (fun Λ ↦ ?_) (fun Λ ε hε ↦ ?_)
  · exact (Subtype.ext (Measure.dirac_bind
      ((gibbsSpecificationFamily Φ ν β).measurable_kernel_toMeasure Λ) η)).symm
  · refine ⟨univ, ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)),
      MeasurableSet.univ, ENNReal.ofReal_ne_top,
      Eventually.of_forall fun a ω _ ↦ relNorm_boltzmannFactor_le (Φ := Φ) β Λ ω, ?_⟩
    have hzero : (fun Λ' : Finset S ↦
        (finiteVolumeDistributions (gibbsSpecificationFamily Φ ν β) η Λ' :
          Measure (S → E)) (univ : Set (S → E))ᶜ) = fun _ ↦ 0 := by
      funext Λ'; simp
    rw [hzero, limsup_const]
    exact hε.le

lemma setOf_mem_GP_gibbsSpecificationFamily_subset_dominatedBy :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (gibbsSpecificationFamily Φ ν β)}
      ⊆ dominatedBy S E (dominatingMeasureFamily Φ ν β) := by
  intro μ hμ Λ A hA
  refine apply_le_of_mem_GP hμ Λ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) fun ω ↦ ?_
  rw [dominatingMeasureFamily, Measure.smul_apply, smul_eq_mul]
  exact gibbsSpecificationFamily_apply_le ν β Λ ω hA

variable [StandardBorelSpace E]

/-- **Georgii Theorem (4.23)(a), existence, over per-site a priori measures.** -/
theorem GP_gibbsSpecificationFamily_nonempty :
    (GP (S := S) (E := E) (gibbsSpecificationFamily Φ ν β)).Nonempty := by
  obtain ⟨η⟩ : Nonempty (S → E) := by
    rcases isEmpty_or_nonempty S with hS | ⟨⟨i⟩⟩
    · exact ⟨fun i ↦ (hS.false i).elim⟩
    · have : Nonempty E := (ν i).nonempty_of_neZero
      exact ⟨fun _ ↦ Classical.arbitrary E⟩
  obtain ⟨μ, hμ, -⟩ := exists_isLocalThermodynamicLimit_mem_GP
    (isQuasilocal_gibbsSpecificationFamily (Φ := Φ) ν β) η
    (locallyEquicontinuous_finiteVolumeDistributionsFamily (Φ := Φ) ν β η)
  exact ⟨μ, hμ⟩

/-- **Georgii Theorem (4.23)(a), compactness, over per-site a priori measures.** -/
theorem isCompact_setOf_mem_GP_gibbsSpecificationFamily :
    IsCompact {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E) (gibbsSpecificationFamily Φ ν β)} :=
  (isCompact_dominatedBy (dominatingMeasureFamily Φ ν β)).of_isClosed_subset
    (isClosed_setOf_mem_GP (isQuasilocal_gibbsSpecificationFamily (Φ := Φ) ν β))
    (setOf_mem_GP_gibbsSpecificationFamily_subset_dominatedBy (Φ := Φ) ν β)

end Family

/-! ### Absorbing the self-energies into the a priori measure

Georgii's reduction in the proof of Theorem (8.39): the single-site terms `Φ_{i}` of a potential
are moved into the a priori measure, leaving the many-body part `Potential.manyBody`, which
`Potential.centre` normalizes so that condition (8.40) puts it in `ℬ`. -/

section SelfEnergy

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} [IsPotential Φ] {β : ℝ}
  {η₀ : S → E}

variable (Φ β η₀) in
/-- The single-site Boltzmann weight `e^{-β Φ_{i}}`, read off at the reference configuration `η₀`.
Since `Φ_{i}` is `𝓕_{i}`-measurable this does not depend on `η₀`
(`Potential.selfEnergyWeight_apply`). -/
noncomputable def selfEnergyWeight [DecidableEq S] (i : S) (x : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * Φ {i} (Function.update η₀ i x)))

variable [DecidableEq S]

lemma selfEnergyWeight_apply (i : S) (σ : S → E) :
    selfEnergyWeight Φ β η₀ i (σ i) = ENNReal.ofReal (Real.exp (-β * Φ {i} σ)) := by
  have h : Φ {i} (Function.update η₀ i (σ i)) = Φ {i} σ := by
    refine IsPotential.eq_of_eqOn (Φ := Φ) fun x hx ↦ ?_
    obtain rfl := Finset.mem_singleton.1 hx
    simp
  rw [selfEnergyWeight, h]

lemma measurable_selfEnergyWeight (i : S) : Measurable (selfEnergyWeight Φ β η₀ i) := by
  refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp ?_)
  exact measurable_const.mul
    (((IsPotential.measurable (Φ := Φ) {i}).mono cylinderEvents_le_pi le_rfl).comp
      (measurable_update η₀ (a := i)))

omit [IsPotential Φ] in
lemma selfEnergyWeight_ne_zero (i : S) (x : E) : selfEnergyWeight Φ β η₀ i x ≠ 0 := by
  simp [selfEnergyWeight, Real.exp_pos]

omit [IsPotential Φ] in
lemma selfEnergyWeight_ne_top (i : S) (x : E) : selfEnergyWeight Φ β η₀ i x ≠ ⊤ := by
  simp [selfEnergyWeight]

/-- **The factorization behind Georgii's reduction.** The Boltzmann factor of `Φ` splits into that
of the recentred many-body part, the product of the single-site weights, and a constant. -/
lemma boltzmannFactor_eq_mul_lambdaWeight [IsSummable Φ] (Λ : Finset S) (σ : S → E) :
    Φ.boltzmannFactor β Λ σ
      = ENNReal.ofReal (Real.exp (-β * (manyBody Φ).hamiltonian Λ η₀))
        * (((manyBody Φ).centre η₀).boltzmannFactor β Λ σ
            * Specification.lambdaWeight (selfEnergyWeight Φ β η₀) Λ σ) := by
  have hcentre : (manyBody Φ).hamiltonian Λ σ
      = ((manyBody Φ).centre η₀).hamiltonian Λ σ + (manyBody Φ).hamiltonian Λ η₀ := by
    have h := hamiltonian_sub' (Φ := manyBody Φ) (Ψ := (manyBody Φ).centre η₀) Λ σ
    rw [hamiltonian_sub_centre (Φ := manyBody Φ) η₀ Λ σ] at h
    linarith
  have hsplit : Φ.hamiltonian Λ σ
      = ((manyBody Φ).centre η₀).hamiltonian Λ σ + (manyBody Φ).hamiltonian Λ η₀
        + ∑ i ∈ Λ, Φ {i} σ := by
    rw [← hcentre, hamiltonian_manyBody (Φ := Φ) Λ σ]; ring
  have hweight : Specification.lambdaWeight (selfEnergyWeight Φ β η₀) Λ σ
      = ENNReal.ofReal (Real.exp (-β * ∑ i ∈ Λ, Φ {i} σ)) := by
    rw [Specification.lambdaWeight,
      Finset.prod_congr rfl fun i _ ↦ selfEnergyWeight_apply (Φ := Φ) (β := β) (η₀ := η₀) i σ,
      ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le, ← Real.exp_sum,
      Finset.mul_sum]
  rw [boltzmannFactor, boltzmannFactor, hweight, hsplit,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

/-! ### The transport -/

variable (Φ β η₀) in
/-- The a priori measure at site `i` in Georgii's reduction: `e^{-β Φ_{i}} λ`, normalized. -/
noncomputable def selfEnergyMeasure (lam : Measure E) (i : S) : Measure E :=
  (lam.withDensity (selfEnergyWeight Φ β η₀ i)).probNormalize

variable {lam : Measure E} [SigmaFinite lam] [NeZero lam]

lemma withDensity_selfEnergyWeight_univ (i : S) :
    lam.withDensity (selfEnergyWeight Φ β η₀ i) Set.univ
      = ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam := by
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]

lemma withDensity_selfEnergyWeight_univ_ne_zero (i : S) :
    lam.withDensity (selfEnergyWeight Φ β η₀ i) Set.univ ≠ 0 := by
  rw [withDensity_selfEnergyWeight_univ]
  intro h
  have hae := (lintegral_eq_zero_iff' (measurable_selfEnergyWeight (Φ := Φ) i).aemeasurable).1 h
  have hz : lam Set.univ = 0 :=
    measure_mono_null (fun x _ ↦ selfEnergyWeight_ne_zero (Φ := Φ) (β := β) (η₀ := η₀) i x) hae
  exact (NeZero.ne lam) (Measure.measure_univ_eq_zero.1 hz)

/-- The per-site measures are the densities `c_i⁻¹ e^{-β Φ_{i}}` against `λ`. -/
lemma selfEnergyMeasure_eq_withDensity (i : S) :
    selfEnergyMeasure Φ β η₀ lam i
      = lam.withDensity fun x ↦ (∫⁻ y, selfEnergyWeight Φ β η₀ i y ∂lam)⁻¹
          * selfEnergyWeight Φ β η₀ i x := by
  rw [selfEnergyMeasure, Measure.probNormalize_def, withDensity_selfEnergyWeight_univ,
    ← withDensity_smul _ (measurable_selfEnergyWeight (Φ := Φ) i)]
  rfl

lemma isProbabilityMeasure_selfEnergyMeasure
    (hfin : ∀ i, ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam ≠ ⊤) (i : S) :
    IsProbabilityMeasure (selfEnergyMeasure Φ β η₀ lam i) := by
  have : IsFiniteMeasure (lam.withDensity (selfEnergyWeight Φ β η₀ i)) :=
    ⟨by rw [withDensity_selfEnergyWeight_univ]; exact lt_top_iff_ne_top.2 (hfin i)⟩
  have : NeZero (lam.withDensity (selfEnergyWeight Φ β η₀ i)) :=
    ⟨fun h ↦ withDensity_selfEnergyWeight_univ_ne_zero (Φ := Φ) (β := β) (η₀ := η₀) (lam := lam) i
      (by rw [h]; simp)⟩
  exact Measure.isProbabilityMeasure_probNormalize _

/-- **Georgii (2.18)**, cf. (1.28)(3); used in the proof of Theorem (8.39). Moving the
self-energies `Φ_{i}` into
the a priori measure does not change the specification: over the per-site measures
`c_i⁻¹ e^{-β Φ_{i}} λ`, the recentred many-body part of `Φ` defines the λ-specification of `Φ`. -/
theorem lambdaSpecification_eq_gibbsSpecificationFamily [Countable S] [IsSummable Φ]
    [IsAbsolutelySummable ((manyBody Φ).centre η₀)]
    (ν : S → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    {c : S → ℝ≥0∞} (hc0 : ∀ i, c i ≠ 0) (hctop : ∀ i, c i ≠ ⊤)
    (hν : ∀ i, ν i = lam.withDensity fun x ↦ (c i)⁻¹ * selfEnergyWeight Φ β η₀ i x)
    {hρ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β)}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β)} :
    gibbsSpecificationFamily ((manyBody Φ).centre η₀) ν β
      = Specification.lambdaSpecification (S := S) (E := E) lam (Φ.boltzmannFactor β) hρ hZ := by
  classical
  set w : S → E → ℝ≥0∞ := fun i x ↦ (c i)⁻¹ * selfEnergyWeight Φ β η₀ i x with hw
  set Ψ : Potential S E := (manyBody Φ).centre η₀ with hΨ
  set κ : Finset S → ℝ≥0∞ := fun Λ ↦
    ENNReal.ofReal (Real.exp (-β * (manyBody Φ).hamiltonian Λ η₀)) * ∏ i ∈ Λ, c i with hκ
  have hwmeas : ∀ i, Measurable (w i) :=
    fun i ↦ measurable_const.mul (measurable_selfEnergyWeight (Φ := Φ) i)
  have hw0 : ∀ i x, w i x ≠ 0 := fun i x ↦
    mul_ne_zero (ENNReal.inv_ne_zero.2 (hctop i))
      (selfEnergyWeight_ne_zero (Φ := Φ) (β := β) (η₀ := η₀) i x)
  have hwtop : ∀ i x, w i x ≠ ⊤ := fun i x ↦
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (hc0 i))
      (selfEnergyWeight_ne_top (Φ := Φ) (β := β) (η₀ := η₀) i x)
  set W : Finset S → (S → E) → ℝ≥0∞ := Specification.lambdaWeight w with hW
  have hWmeas : ∀ Λ, Measurable (W Λ) := Specification.measurable_lambdaWeight hwmeas
  have hW0 : ∀ Λ ω, W Λ ω ≠ 0 := Specification.lambdaWeight_ne_zero hw0
  have hWtop : ∀ Λ ω, W Λ ω ≠ ⊤ := Specification.lambdaWeight_ne_top hwtop
  have href : ∀ (Λ : Finset S) (η : S → E),
      Specification.isssdFamily ν Λ η
        = (Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η).withDensity (W Λ) := by
    intro Λ η
    have hν' : ν = fun i ↦ lam.withDensity (w i) := funext hν
    subst hν'
    exact Specification.isssdFamilyFun_withDensity lam hwmeas Λ η
  have hfactor : ∀ (Λ : Finset S) (σ : S → E),
      Φ.boltzmannFactor β Λ σ = κ Λ * Ψ.boltzmannFactor β Λ σ * W Λ σ := by
    intro Λ σ
    have hprod : W Λ σ = (∏ i ∈ Λ, (c i)⁻¹)
        * Specification.lambdaWeight (selfEnergyWeight Φ β η₀) Λ σ := by
      rw [hW, Specification.lambdaWeight, Specification.lambdaWeight, ← Finset.prod_mul_distrib]
    have hcancel : (∏ i ∈ Λ, c i) * ∏ i ∈ Λ, (c i)⁻¹ = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ ↦ ENNReal.mul_inv_cancel (hc0 i) (hctop i)
    rw [boltzmannFactor_eq_mul_lambdaWeight (Φ := Φ) (β := β) (η₀ := η₀) Λ σ, hprod, hκ,
      show ENNReal.ofReal (Real.exp (-β * (manyBody Φ).hamiltonian Λ η₀)) * (∏ i ∈ Λ, c i)
          * Ψ.boltzmannFactor β Λ σ * ((∏ i ∈ Λ, (c i)⁻¹)
            * Specification.lambdaWeight (selfEnergyWeight Φ β η₀) Λ σ)
        = ENNReal.ofReal (Real.exp (-β * (manyBody Φ).hamiltonian Λ η₀))
          * (((∏ i ∈ Λ, c i) * ∏ i ∈ Λ, (c i)⁻¹) * (Ψ.boltzmannFactor β Λ σ
            * Specification.lambdaWeight (selfEnergyWeight Φ β η₀) Λ σ)) from by ring,
      hcancel, one_mul]
  have hdiv : (fun Λ ω ↦ Φ.boltzmannFactor β Λ ω / W Λ ω)
      = fun Λ ω ↦ κ Λ * Ψ.boltzmannFactor β Λ ω := by
    funext Λ ω
    rw [hfactor Λ ω, ENNReal.mul_div_cancel_right (hW0 Λ ω) (hWtop Λ ω)]
  have hκ0 : ∀ Λ, κ Λ ≠ 0 := fun Λ ↦ mul_ne_zero
    (by simp [Real.exp_pos]) (Finset.prod_ne_zero_iff.2 fun i _ ↦ hc0 i)
  have hκtop : ∀ Λ, κ Λ ≠ ⊤ := fun Λ ↦
    ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top fun i _ ↦ hctop i)
  refine Specification.ext fun Λ ↦ Kernel.ext fun η ↦ ?_
  have key := Specification.withDensity_relNorm_div_sigmaFiniteLambdaFun lam
    (γ' := Specification.isssdFamily ν) (ρ := Φ.boltzmannFactor β) (W := W)
    href hWmeas hW0 hWtop hρ.measurable Λ η
  rw [hdiv, Specification.relNorm_const_mul hκ0 hκtop] at key
  rw [gibbsSpecificationFamily, Specification.premodification, Specification.modification_apply]
  exact key

/-- **Georgii Theorem (4.23)(a) after the reduction.** A `λ`-admissible potential whose
self-energies are `λ`-integrable and whose recentred many-body part is absolutely summable has a
Gibbs measure. This is the existence half of Theorem (8.39), with condition (8.40) entering only
through `Potential.IsAbsolutelySummable ((manyBody Φ).centre η₀)`. -/
theorem GP_lambdaSpecification_nonempty_of_lintegral_selfEnergyWeight_ne_top
    [Countable S] [StandardBorelSpace E] [IsSummable Φ]
    [IsAbsolutelySummable ((manyBody Φ).centre η₀)]
    (hfin : ∀ i, ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam ≠ ⊤)
    {hρ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β)}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β)} :
    (GP (S := S) (E := E)
      (Specification.lambdaSpecification lam (Φ.boltzmannFactor β) hρ hZ)).Nonempty := by
  haveI : ∀ i, IsProbabilityMeasure (selfEnergyMeasure Φ β η₀ lam i) :=
    isProbabilityMeasure_selfEnergyMeasure hfin
  rw [← lambdaSpecification_eq_gibbsSpecificationFamily (Φ := Φ) (β := β) (η₀ := η₀)
    (selfEnergyMeasure Φ β η₀ lam)
    (c := fun i ↦ ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam)
    (fun i ↦ by
      rw [← withDensity_selfEnergyWeight_univ]
      exact withDensity_selfEnergyWeight_univ_ne_zero (Φ := Φ) i)
    hfin (fun i ↦ selfEnergyMeasure_eq_withDensity (Φ := Φ) i)]
  exact GP_gibbsSpecificationFamily_nonempty _ _

/-! ### λ-admissibility bounds the self-energies -/

lemma lintegral_sigmaFiniteLambdaFun_coord {i : S} (η : S → E) {f : E → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ σ, f (σ i)
        ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam ({i} : Finset S) η)
      = ∫⁻ x, f x ∂lam := by
  haveI : Unique (({i} : Finset S) : Type _) :=
    ⟨⟨⟨i, Finset.mem_singleton_self i⟩⟩, fun x ↦ Subtype.ext (Finset.mem_singleton.1 x.2)⟩
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map (f := fun σ : S → E ↦ f (σ i)) (hf.comp (measurable_pi_apply i))
      Measurable.juxt]
  have hcoord : ∀ ζ : ({i} : Finset S) → E,
      f (juxt ((({i} : Finset S) : Finset S) : Set S) η ζ i) = f (ζ default) := fun ζ ↦ by
    rw [juxt_apply_of_mem (Λ := ((({i} : Finset S) : Finset S) : Set S)) (by simp) ζ]
    congr 1
    exact congrArg ζ (Subsingleton.elim _ _)
  simp_rw [hcoord]
  have h := (MeasureTheory.measurePreserving_funUnique lam
    (({i} : Finset S) : Type _)).lintegral_comp hf
  refine Eq.trans ?_ h
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- **Georgii's finiteness input.** `λ`-admissibility at the single-site volumes bounds the
self-energy weights: once the recentred many-body part is absolutely summable, the many-body
contribution to `H_{i}` is bounded, so `λ(e^{-β Φ_{i}}) ≤ C · Z_{i} < ∞`. -/
theorem lintegral_selfEnergyWeight_ne_top [Countable S] [IsSummable Φ]
    [IsAbsolutelySummable ((manyBody Φ).centre η₀)]
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β))
    (i : S) : ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam ≠ ⊤ := by
  set Ψ : Potential S E := (manyBody Φ).centre η₀ with hΨ
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-β * (manyBody Φ).hamiltonian ({i} : Finset S) η₀))
    with hK
  set m : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (-(|β| * Ψ.hamiltonianBound ({i} : Finset S)))) with hm
  have hKm : K * m ≠ 0 := mul_ne_zero (by simp [hK, Real.exp_pos]) (by simp [hm, Real.exp_pos])
  -- the Boltzmann factor of `Φ` dominates a multiple of the self-energy weight
  have hle : ∀ σ : S → E,
      K * m * selfEnergyWeight Φ β η₀ i (σ i) ≤ Φ.boltzmannFactor β ({i} : Finset S) σ := by
    intro σ
    rw [boltzmannFactor_eq_mul_lambdaWeight (Φ := Φ) (β := β) (η₀ := η₀) ({i} : Finset S) σ,
      Specification.lambdaWeight, Finset.prod_singleton, mul_assoc]
    gcongr
    exact le_boltzmannFactor (Φ := Ψ) β _ σ
  -- integrate against the reference kernel at `Λ = {i}`
  have hint : K * m * ∫⁻ x, selfEnergyWeight Φ β η₀ i x ∂lam
      ≤ Specification.sigmaFiniteLambdaZ lam (Φ.boltzmannFactor β) ({i} : Finset S) η₀ := by
    rw [Specification.sigmaFiniteLambdaZ,
      ← lintegral_sigmaFiniteLambdaFun_coord (lam := lam) (i := i) η₀
        (measurable_selfEnergyWeight (Φ := Φ) i),
      ← lintegral_const_mul (f := fun σ : S → E ↦ selfEnergyWeight Φ β η₀ i (σ i)) _
        ((measurable_selfEnergyWeight (Φ := Φ) i).comp (measurable_pi_apply i))]
    exact lintegral_mono hle
  intro htop
  rw [htop, ENNReal.mul_top hKm] at hint
  exact (hZ ({i} : Finset S) η₀).2 (top_le_iff.1 hint)

/-- **The existence half of Georgii Theorem (8.39), in the form his proof establishes it.** A
`λ`-admissible potential whose recentred many-body part is absolutely summable has a Gibbs
measure. Only `Potential.IsAbsolutelySummable ((manyBody Φ).centre η₀)` remains to be supplied,
and on `ℤ` or `ℕ` condition (8.40) supplies it. -/
theorem GP_lambdaSpecification_nonempty [Countable S] [StandardBorelSpace E] [IsSummable Φ]
    [IsAbsolutelySummable ((manyBody Φ).centre η₀)]
    {hρ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β)}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Φ.boltzmannFactor β)} :
    (GP (S := S) (E := E)
      (Specification.lambdaSpecification lam (Φ.boltzmannFactor β) hρ hZ)).Nonempty :=
  GP_lambdaSpecification_nonempty_of_lintegral_selfEnergyWeight_ne_top (η₀ := η₀)
    (lintegral_selfEnergyWeight_ne_top (Φ := Φ) (β := β) (η₀ := η₀) hZ)

end SelfEnergy

end Potential

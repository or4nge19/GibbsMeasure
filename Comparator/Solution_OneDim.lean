import Comparator.Defs_OneDim
import GibbsMeasure

/-!
# Comparator solution: uniqueness in one dimension (Georgii, Section 8.3)

The solution file matching `Comparator/Challenge_OneDim.lean`.  The `Bridge` namespace identifies
the from-scratch definitions of `Comparator.Defs_OneDim` with those of the `GibbsMeasure` library
— in particular `Bridge.gibbsKernel_eq`, which identifies the finite-volume Gibbs distribution of
Definition (2.9) with the `Λ`-kernel of `Specification.lambdaSpecification` — and the theorems are
then discharged from
`MeasureTheory.GibbsMeasure.subsingleton_G_of_isUniformlyDominated`,
`…subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top`,
`…existsUnique_mem_GP_of_iSup_oscSpan_ne_top` and `…subsingleton_G_of_pair_rpow_le`.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Section 8.3
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace OneDimChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## The bridge to the `GibbsMeasure` library -/

namespace Bridge

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory

variable {S E : Type*} [MeasurableSpace E]

/-! ### The σ-algebras and the local events -/

theorem outside_eq_cylinderEvents (Λ : Finset S) :
    outside (S := S) (E := E) Λ = cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := rfl

theorem inside_eq_cylinderEvents (Λ : Finset S) :
    inside (S := S) (E := E) Λ = cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) := rfl

theorem isLocalEvent_iff {A : Set (Config S E)} : IsLocalEvent A ↔ A ∈ localEvents S E :=
  MeasureTheory.mem_localEvents_iff_cylinderEvents.symm

/-! ### The library `Specification` attached to a first-principles specification -/

variable {γ : Finset S → Config S E → Measure (Config S E)}

/-- The library's `Specification` bundling the kernels of a first-principles specification. -/
def spec (γ : Finset S → Config S E → Measure (Config S E)) (hγ : IsSpecification γ) :
    Specification S E where
  toFun Λ := @ProbabilityTheory.Kernel.mk (S → E) (S → E)
    (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) _ (γ Λ)
    (Measure.measurable_measure.2 fun A hA ↦ hγ.measurable_apply Λ A hA)
  isConsistent' := by
    intro Λ₁ Λ₂ h
    refine Kernel.ext fun ω ↦ Measure.ext fun A hA ↦ ?_
    rw [Kernel.comp_apply' _ _ _ hA]
    exact hγ.consistent Λ₁ Λ₂ h ω A hA
  isMarkovKernel' Λ := ⟨fun ω ↦ hγ.isProbabilityMeasure Λ ω⟩
  isProper' Λ := by
    rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
    intro A hA B hB ω
    show γ Λ ω (A ∩ B) = B.indicator 1 ω * γ Λ ω A
    rw [hγ.proper Λ A B hA hB ω]
    by_cases hω : ω ∈ B <;> simp [hω]

@[simp] theorem spec_apply (hγ : IsSpecification γ) (Λ : Finset S) (ω : Config S E) :
    spec γ hγ Λ ω = γ Λ ω := rfl

theorem comp_eq (hγ : IsSpecification γ) {μ : Measure (Config S E)} (hμ : IsGibbs γ μ)
    (Λ : Finset S) : ⇑(spec γ hγ Λ) ∘ₘ μ = μ := by
  have := hμ.1
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.bind_apply hA
    (((spec γ hγ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)]
  exact (hμ.2 Λ A hA).symm

theorem isGibbsMeasure (hγ : IsSpecification γ) {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    Specification.IsGibbsMeasure (spec γ hγ) μ := by
  have := hμ.1
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  exact fun Λ ↦ comp_eq hγ hμ Λ

theorem mem_G (hγ : IsSpecification γ) {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    μ ∈ G (γ := spec γ hγ) := ⟨hμ.1, isGibbsMeasure hγ hμ⟩

/-! ### Georgii (8.2): the two oscillations agree -/

omit [MeasurableSpace E] in
theorem osc_eq (f : Config S E → ℝ) : osc f = GibbsMeasure.Dobrushin.osc f :=
  le_antisymm (osc_le fun ζ η ↦ GibbsMeasure.Dobrushin.le_osc f ζ η)
    (GibbsMeasure.Dobrushin.osc_le fun ζ η ↦ le_osc f ζ η)

/-! ### Georgii (2.1)–(2.4): potentials and Hamiltonians

Georgii's Convention (2.1) is the library's `SummationFilter.volume`. -/

variable {Φ : Finset S → Config S E → ℝ}

theorem hamiltonianTerm_eq (Φ : Finset S → Config S E → ℝ) (Λ : Finset S) (ω : Config S E) :
    hamiltonianTerm Φ Λ ω = Potential.hamiltonianTerms (Φ : Potential S E) Λ ω := by
  have hset : {B : Finset S | ∃ i ∈ B, i ∈ Λ} = {B : Finset S | ¬ Disjoint B Λ} := by
    ext B; simp [Finset.not_disjoint_iff]
  funext A
  show {B : Finset S | ∃ i ∈ B, i ∈ Λ}.indicator (fun B ↦ Φ B ω) A = _
  rw [hset]
  rfl

theorem isPotentialLib (hΦ : IsPotential Φ) : Potential.IsPotential (Φ : Potential S E) :=
  ⟨fun A ↦ hΦ.measurable_inside A⟩

theorem isSummableLib (hΦ : IsPotential Φ) : Potential.IsSummable (Φ : Potential S E) := by
  refine ⟨fun Λ η ↦ ?_⟩
  obtain ⟨h, hh⟩ := hΦ.exists_hasHamiltonian Λ η
  refine ⟨h, SummationFilter.tendsto_volume_filter ?_⟩
  rw [← hamiltonianTerm_eq]
  exact hh

theorem hamiltonian_eq (hΦ : IsPotential Φ) (Λ : Finset S) (ω : Config S E) :
    hamiltonian Φ Λ ω = Potential.hamiltonian (Φ : Potential S E) Λ ω := by
  haveI := isSummableLib hΦ
  refine tendsto_nhds_unique (hasHamiltonian_hamiltonian hΦ Λ ω) ?_
  have h := Potential.hasSum_hamiltonian (Φ := (Φ : Potential S E)) Λ ω
  have h' : Tendsto (fun t : Finset (Finset S) ↦
      ∑ A ∈ t, Potential.hamiltonianTerms (Φ : Potential S E) Λ ω A)
      (Filter.map Finset.powerset Filter.atTop)
      (𝓝 (Potential.hamiltonian (Φ : Potential S E) Λ ω)) := h
  rw [hamiltonianTerm_eq]
  exact Filter.tendsto_map'_iff.2 h'

theorem boltzmannFactor_eq (hΦ : IsPotential Φ) (β : ℝ) (Λ : Finset S) :
    boltzmannFactor Φ β Λ = Potential.boltzmannFactor (Φ : Potential S E) β Λ := by
  funext ω
  rw [boltzmannFactor, Potential.boltzmannFactor, hamiltonian_eq hΦ]

/-! ### Georgii (1.26), (2.7): the reference kernels and the partition function -/

theorem freeMeasure_eq (lam : Measure E) [SigmaFinite lam] (Λ : Finset S) (ω : Config S E) :
    freeMeasure lam Λ ω = Specification.sigmaFiniteLambdaFun (S := S) (E := E) lam Λ ω := by
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map]
  show Measure.map (fun ζ : Λ → E ↦ extend Λ ζ ω) (Measure.pi fun _ : Λ ↦ lam)
      = Measure.map (juxt (Λ : Set S) ω) (Measure.pi fun _ : Λ ↦ lam)
  congr 1
  funext ζ i
  by_cases h : i ∈ Λ <;> simp [extend, juxt, h]

theorem freeMeasure_extend (lam : Measure E) (Λ : Finset S) (ω : Config S E) (ζ : Λ → E) :
    freeMeasure lam Λ (extend Λ ζ ω) = freeMeasure lam Λ ω := by
  rw [freeMeasure, freeMeasure]
  congr 1
  funext ζ' i
  by_cases h : i ∈ Λ <;> simp [extend, h]

theorem partitionFunction_extend (lam : Measure E) (β : ℝ) (Λ : Finset S) (ω : Config S E)
    (ζ : Λ → E) :
    partitionFunction Φ lam β Λ (extend Λ ζ ω) = partitionFunction Φ lam β Λ ω := by
  rw [partitionFunction, partitionFunction, freeMeasure_extend]

theorem partitionFunction_eq (hΦ : IsPotential Φ) (lam : Measure E) [SigmaFinite lam] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    partitionFunction Φ lam β Λ ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) lam
          (Potential.boltzmannFactor (Φ : Potential S E) β) Λ ω := by
  rw [partitionFunction, Specification.sigmaFiniteLambdaZ, boltzmannFactor_eq hΦ,
    freeMeasure_eq]

theorem isSigmaFiniteLambdaAdmissible (hΦ : IsPotential Φ) (lam : Measure E) [SigmaFinite lam]
    (β : ℝ) (hadm : IsAdmissible Φ lam β) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam
      (Potential.boltzmannFactor (Φ : Potential S E) β) := by
  intro Λ ω
  have h := hadm Λ ω
  rw [partitionFunction_eq hΦ lam β Λ ω] at h
  exact h

/-! ### Georgii (1.27), (2.9): the finite-volume Gibbs distribution -/

variable [Countable S]

/-- The finite-volume Gibbs distribution of Definition (2.9) is the `Λ`-kernel of the library's
λ-specification for the same σ-finite a priori measure. -/
theorem gibbsKernel_eq (hΦ : IsPotential Φ) (lam : Measure E) [SigmaFinite lam] [NeZero lam]
    (β : ℝ) (hadm : IsAdmissible Φ lam β) (Λ : Finset S) (ω : Config S E) :
    gibbsKernel Φ lam β Λ ω
      = Specification.lambdaSpecification (S := S) (E := E) lam
          (Potential.boltzmannFactor (Φ : Potential S E) β)
          (haveI := isPotentialLib hΦ; haveI := isSummableLib hΦ;
            Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β)
          (isSigmaFiniteLambdaAdmissible hΦ lam β hadm) Λ ω := by
  haveI := isPotentialLib hΦ
  haveI := isSummableLib hΦ
  have hbfmeas : Measurable (Potential.boltzmannFactor (Φ : Potential S E) β Λ) :=
    Potential.measurable_boltzmannFactor (Φ := (Φ : Potential S E)) β Λ
  rw [Specification.lambdaSpecification_apply, ← freeMeasure_eq lam Λ ω]
  refine Measure.ext fun A hA ↦ ?_
  rw [gibbsKernel, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA, withDensity_apply _ hA,
    ← lintegral_indicator hA, ← lintegral_indicator hA, freeMeasure,
    lintegral_map ?_ (measurable_extend Λ ω), lintegral_map ?_ (measurable_extend Λ ω),
    ← lintegral_const_mul _ ?_]
  · refine lintegral_congr fun ζ ↦ ?_
    by_cases hmem : extend Λ ζ ω ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Specification.sigmaFinitePremodifierNorm,
        ← partitionFunction_eq hΦ, partitionFunction_extend, boltzmannFactor_eq hΦ,
        partitionFunction_eq hΦ, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
  · rw [boltzmannFactor_eq hΦ]
    exact (hbfmeas.indicator hA).comp (measurable_extend Λ ω)
  · exact (Specification.sigmaFinitePremodifierNorm_measurable lam
      (Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β) Λ).indicator hA
  · rw [boltzmannFactor_eq hΦ]
    exact hbfmeas.indicator hA

theorem isSpecification_gibbsKernel (hΦ : IsPotential Φ) (lam : Measure E) [SigmaFinite lam]
    [NeZero lam] (β : ℝ) (hadm : IsAdmissible Φ lam β) :
    IsSpecification (gibbsKernel Φ lam β) := by
  refine ⟨fun Λ ω ↦ ?_, fun Λ A hA ↦ ?_, fun Λ ↦ ?_, fun Λ Δ hΛΔ ω A hA ↦ ?_⟩
  · rw [gibbsKernel_eq hΦ lam β hadm]; infer_instance
  · simp only [gibbsKernel_eq hΦ lam β hadm]
    exact ProbabilityTheory.Kernel.measurable_coe _ hA
  · intro A B hA hB ω
    rw [gibbsKernel_eq hΦ lam β hadm,
      (Specification.lambdaSpecification (S := S) (E := E) lam
        (Potential.boltzmannFactor (Φ : Potential S E) β)
        (haveI := isPotentialLib hΦ; haveI := isSummableLib hΦ;
          Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β)
        (isSigmaFiniteLambdaAdmissible hΦ lam β hadm)).isProper.inter_eq_indicator_mul Λ hA hB ω]
    by_cases hωB : ω ∈ B <;> simp [hωB]
  · simp only [gibbsKernel_eq hΦ lam β hadm]
    rw [← Measure.bind_apply hA
      ((Specification.lambdaSpecification (S := S) (E := E) lam
        (Potential.boltzmannFactor (Φ : Potential S E) β)
        (haveI := isPotentialLib hΦ; haveI := isSummableLib hΦ;
          Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β)
        (isSigmaFiniteLambdaAdmissible hΦ lam β hadm)).measurable_kernel_toMeasure Λ).aemeasurable,
      Specification.bind hΛΔ ω]

end Bridge

namespace Bridge

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory

variable {S E : Type*} [MeasurableSpace E] {Φ : Finset S → Config S E → ℝ}

/-! ### The DLR equations against a library specification -/

theorem isGibbs_iff_isGibbsMeasure {γ : Finset S → Config S E → Measure (Config S E)}
    {γlib : Specification S E} (hK : ∀ (Λ : Finset S) (ω : Config S E), γ Λ ω = γlib Λ ω)
    (μ : Measure (Config S E)) [IsProbabilityMeasure μ] :
    IsGibbs γ μ ↔ Specification.IsGibbsMeasure γlib μ := by
  have hmeas : ∀ Λ : Finset S, AEMeasurable (γlib Λ) μ := fun Λ ↦
    (γlib.measurable_kernel_toMeasure Λ).aemeasurable
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  constructor
  · rintro ⟨-, h⟩ Λ
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA (hmeas Λ), h Λ A hA]
    exact lintegral_congr fun ω ↦ by rw [hK]
  · refine fun h ↦ ⟨inferInstance, fun Λ A hA ↦ ?_⟩
    conv_lhs => rw [← h Λ]
    rw [Measure.bind_apply hA (hmeas Λ)]
    exact lintegral_congr fun ω ↦ by rw [hK]

/-! ### Georgii (8.40): the two spanning sums agree -/

theorem spans_iff [Preorder S] (A : Finset S) (i : S) :
    Spans A i ↔ MeasureTheory.GibbsMeasure.Spans A i := Iff.rfl

theorem oscSpan_eq [Preorder S] (Φ : Finset S → Config S E → ℝ) (i : S) :
    oscSpan Φ i = MeasureTheory.GibbsMeasure.oscSpan (Φ : Potential S E) i := by
  refine tsum_congr fun A ↦ ?_
  show {B : Finset S | Spans B i}.indicator (fun B ↦ osc (Φ B)) A
      = {B : Finset S | MeasureTheory.GibbsMeasure.Spans B i}.indicator
        (fun B ↦ MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential S E) B)) A
  by_cases h : Spans A i
  · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | Spans B i} from h),
      Set.indicator_of_mem
        (show A ∈ {B : Finset S | MeasureTheory.GibbsMeasure.Spans B i} from h), osc_eq]
  · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | Spans B i} from h),
      Set.indicator_of_notMem
        (show A ∉ {B : Finset S | MeasureTheory.GibbsMeasure.Spans B i} from h)]

theorem iSup_oscSpan_eq [Preorder S] (Φ : Finset S → Config S E → ℝ) :
    (⨆ i : S, oscSpan Φ i)
      = ⨆ i : S, MeasureTheory.GibbsMeasure.oscSpan (Φ : Potential S E) i :=
  iSup_congr fun i ↦ oscSpan_eq Φ i

theorem hasBoundedBoundary_iff [Preorder S] (m : ℕ) :
    HasBoundedBoundary S m ↔ MeasureTheory.GibbsMeasure.HasBoundedBoundary S m := Iff.rfl

/-! ### Georgii (8.41): translates on `ℤ` -/

theorem shiftFinset_eq (n : ℤ) (A : Finset ℤ) :
    shiftFinset n A = MeasureTheory.GibbsMeasure.shiftFinset n A := rfl

/-! ### Georgii (2.11): absolute summability -/

theorem potentialNormAt_eq (Φ : Finset S → Config S E → ℝ) (i : S) :
    potentialNormAt Φ i = Potential.normAt (Φ : Potential S E) i := by
  simp only [potentialNormAt, Potential.normAt, Real.enorm_eq_ofReal_abs]

theorem isAbsolutelySummableLib (habs : IsAbsolutelySummable Φ) :
    Potential.IsAbsolutelySummable (Φ : Potential S E) := by
  refine ⟨fun i ↦ ?_⟩
  rw [← potentialNormAt_eq]
  exact habs i

theorem isAdmissible_of_isAbsolutelySummable [Countable S] (hΦ : IsPotential Φ)
    (habs : IsAbsolutelySummable Φ) (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) :
    IsAdmissible Φ lam β := by
  haveI := isPotentialLib hΦ
  haveI := isAbsolutelySummableLib habs
  intro Λ ω
  have hZ := (Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible lam
    (Potential.boltzmannFactor (Φ : Potential S E) β)).1
      (Potential.isPremodifierAdmissible_boltzmannFactor (Φ := (Φ : Potential S E)) lam β)
  rw [partitionFunction_eq hΦ lam β Λ ω]
  exact hZ Λ ω

/-! ### The Gibbsian specification of an absolutely summable potential -/

variable {Ψ : Finset ℤ → Config ℤ E → ℝ}

theorem gibbsKernel_eq_gibbsSpec (hΨ : IsPotential Ψ) (habs : IsAbsolutelySummable Ψ)
    [Potential.IsPotential (Ψ : Potential ℤ E)]
    [Potential.IsAbsolutelySummable (Ψ : Potential ℤ E)]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ) (Λ : Finset ℤ) (ω : Config ℤ E) :
    gibbsKernel Ψ lam β Λ ω
      = Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Ψ : Potential ℤ E)) lam β Λ ω := by
  haveI := isPotentialLib hΨ
  haveI := isSummableLib hΨ
  haveI := isAbsolutelySummableLib habs
  have hadm := isAdmissible_of_isAbsolutelySummable hΨ habs lam β
  rw [gibbsKernel_eq hΨ lam β hadm,
    MeasureTheory.GibbsMeasure.gibbsSpecificationOfAbsolutelySummable_eq_lambdaSpecification
      (Φ := (Ψ : Potential ℤ E)) lam β (isSigmaFiniteLambdaAdmissible hΨ lam β hadm)]

/-- **Georgii, Theorem (8.39), second half**, transported to the from-first-principles
Gibbsian specification. -/
theorem existsUnique_isGibbs [StandardBorelSpace E] (hΨ : IsPotential Ψ)
    (habs : IsAbsolutelySummable Ψ)
    [Potential.IsPotential (Ψ : Potential ℤ E)]
    [Potential.IsAbsolutelySummable (Ψ : Potential ℤ E)]
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : (⨆ i : ℤ, MeasureTheory.GibbsMeasure.oscSpan (Ψ : Potential ℤ E) i) ≠ ⊤) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Ψ lam β) μ := by
  haveI := isPotentialLib hΨ
  haveI := isSummableLib hΨ
  haveI := isAbsolutelySummableLib habs
  have hK := gibbsKernel_eq_gibbsSpec hΨ habs lam β
  obtain ⟨P, hP, huniq⟩ :=
    MeasureTheory.GibbsMeasure.existsUnique_mem_GP_of_iSup_oscSpan_ne_top
      (Φ := (Ψ : Potential ℤ E)) lam β h840
  refine ⟨(P : Measure (Config ℤ E)), (isGibbs_iff_isGibbsMeasure hK _).2 hP, fun ν hν ↦ ?_⟩
  haveI := hν.1
  have hνP : (⟨ν, hν.1⟩ : ProbabilityMeasure (Config ℤ E)) = P :=
    huniq _ ((isGibbs_iff_isGibbsMeasure hK ν).1 hν)
  exact congrArg (fun x : ProbabilityMeasure (Config ℤ E) ↦ (x : Measure (Config ℤ E))) hνP

end Bridge

/-! ## The theorems -/

/-- **Georgii, Proposition (8.38)**: a specification `γ` for which every cylinder event `A` admits
a volume `Λ` with `γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all `ζ, η` and some `c > 0` has at most one Gibbs
measure.  Nothing beyond countability is assumed of the parameter set. -/
theorem subsingleton_isGibbs_of_isUniformlyDominated [Countable S]
    (γ : Finset S → Config S E → Measure (Config S E)) (hγ : IsSpecification γ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hdom : IsUniformlyDominated γ c) :
    {μ : Measure (Config S E) | IsGibbs γ μ}.Subsingleton := by
  intro μ hμ ν hν
  have hdom' : MeasureTheory.GibbsMeasure.IsUniformlyDominated (Bridge.spec γ hγ) c := by
    intro A hA
    obtain ⟨Λ, hΛ⟩ := hdom A (Bridge.isLocalEvent_iff.2 hA)
    exact ⟨Λ, hΛ⟩
  exact MeasureTheory.GibbsMeasure.subsingleton_G_of_isUniformlyDominated hc hdom'
    (Bridge.mem_G hγ hμ) (Bridge.mem_G hγ hν)

/-- Non-vacuity of Proposition (8.38): the independent specification is a genuine specification
satisfying its hypothesis with `c = 1`. -/
theorem exists_isSpecification_isUniformlyDominated (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    ∃ γ : Finset ℤ → Config ℤ E → Measure (Config ℤ E),
      IsSpecification γ ∧ IsUniformlyDominated γ 1 ∧
      ∀ (Λ : Finset ℤ) (ω : Config ℤ E), γ Λ ω = freeMeasure lam Λ ω := by
  refine ⟨gibbsKernel (fun (_ : Finset ℤ) (_ : Config ℤ E) ↦ (0 : ℝ)) lam β, ?_,
    isUniformlyDominated_gibbsKernel_zero lam β, fun Λ ω ↦ gibbsKernel_zero lam β Λ ω⟩
  exact Bridge.isSpecification_gibbsKernel isPotential_zero lam β (isAdmissible_zero lam β)

/-- The integers are exhausted by the intervals `]−n, n]`, each with the two boundary sites `−n`
and `n`. -/
theorem hasBoundedBoundary_int : HasBoundedBoundary ℤ 2 := by
  exact (Bridge.hasBoundedBoundary_iff 2).2 MeasureTheory.GibbsMeasure.hasBoundedBoundary_int

/-- The naturals are exhausted by the intervals `[0, n]`, each with the single boundary site
`n`. -/
theorem hasBoundedBoundary_nat : HasBoundedBoundary ℕ 1 := by
  exact (Bridge.hasBoundedBoundary_iff 1).2 MeasureTheory.GibbsMeasure.hasBoundedBoundary_nat

/-- **Georgii, Theorem (8.39), first half**: on a parameter set with a chain structure, a
potential in the sense of Definition (2.2) — merely summable in the sense of Convention (2.1) —
that is `λ`-admissible over a σ-finite non-zero `λ` and satisfies condition (8.40)
`sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞` has at most one Gibbs measure. -/
theorem subsingleton_isGibbs_of_iSup_oscSpan_ne_top [Countable S] [Preorder S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    (Φ : Finset S → Config S E → ℝ) (hΦ : IsPotential Φ)
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hadm : IsAdmissible Φ lam β) (h840 : (⨆ i : S, oscSpan Φ i) ≠ ⊤) :
    {μ : Measure (Config S E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  haveI := Bridge.isPotentialLib hΦ
  haveI := Bridge.isSummableLib hΦ
  intro μ hμ ν hν
  haveI := hμ.1
  haveI := hν.1
  have hZ := Bridge.isSigmaFiniteLambdaAdmissible hΦ lam β hadm
  have h840' : (⨆ i : S, MeasureTheory.GibbsMeasure.oscSpan (Φ : Potential S E) i) ≠ ⊤ := by
    rwa [← Bridge.iSup_oscSpan_eq]
  have hK : ∀ (Λ : Finset S) (ω : Config S E), gibbsKernel Φ lam β Λ ω
      = Specification.lambdaSpecification (S := S) (E := E) lam
          (Potential.boltzmannFactor (Φ : Potential S E) β)
          (Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β) hZ Λ ω :=
    fun Λ ω ↦ Bridge.gibbsKernel_eq hΦ lam β hadm Λ ω
  exact MeasureTheory.GibbsMeasure.subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top
    ((Bridge.hasBoundedBoundary_iff m).1 hexh) lam β hZ h840'
    ⟨hμ.1, (Bridge.isGibbs_iff_isGibbsMeasure hK μ).1 hμ⟩
    ⟨hν.1, (Bridge.isGibbs_iff_isGibbsMeasure hK ν).1 hν⟩

/-- **Georgii, Theorem (8.39), second half**: under condition (8.40) the potential has exactly one
Gibbs measure.  Existence rests on Theorem (4.23)(a), available only for an absolutely summable
potential over a finite a priori measure on a standard Borel state space, so the statement is made
at exactly those hypotheses and no weaker ones. -/
theorem existsUnique_isGibbs_of_iSup_oscSpan_ne_top [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : (⨆ i : ℤ, oscSpan Φ i) ≠ ⊤) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  haveI := Bridge.isPotentialLib hΦ
  haveI := Bridge.isSummableLib hΦ
  haveI := Bridge.isAbsolutelySummableLib habs
  exact Bridge.existsUnique_isGibbs hΦ habs lam β (by rwa [← Bridge.iSup_oscSpan_eq])

/-- **Georgii, Comment (8.41)(2)**: a shift-invariant pair potential on `ℤ` whose two-point
oscillations decay as `δ(Φ_{{0,n}}) ≤ c n^{-p}` with `p > 2` has at most one Gibbs measure.  The
hypotheses are conditions on the oscillations alone, so no relation between `Φ` and a particular
`φ` is presumed. -/
theorem subsingleton_isGibbs_of_pair_rpow_le
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    {μ : Measure (Config ℤ E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  haveI := Bridge.isPotentialLib hΦ
  haveI := Bridge.isSummableLib hΦ
  haveI := Bridge.isAbsolutelySummableLib habs
  have hshift' : ∀ (n : ℤ) (A : Finset ℤ),
      MeasureTheory.GibbsMeasure.Dobrushin.osc
          ((Φ : Potential ℤ E) (MeasureTheory.GibbsMeasure.shiftFinset n A))
        = MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) A) := by
    intro n A
    rw [← Bridge.shiftFinset_eq, ← Bridge.osc_eq, ← Bridge.osc_eq]
    exact hshift n A
  have hpair' : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) →
      MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) A) = 0 := by
    intro A hA
    rw [← Bridge.osc_eq]
    exact hpair A hA
  have hbd' : ∀ n : ℕ, 0 < n →
      MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) {0, (n : ℤ)})
        ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p)) := by
    intro n hn
    rw [← Bridge.osc_eq]
    exact hbd n hn
  intro μ hμ ν hν
  haveI := hμ.1
  haveI := hν.1
  have hK := Bridge.gibbsKernel_eq_gibbsSpec hΦ habs lam β
  exact MeasureTheory.GibbsMeasure.subsingleton_G_of_pair_rpow_le lam β hshift' hpair' hp hbd'
    ⟨hμ.1, (Bridge.isGibbs_iff_isGibbsMeasure hK μ).1 hμ⟩
    ⟨hν.1, (Bridge.isGibbs_iff_isGibbsMeasure hK ν).1 hν⟩

/-- **Georgii, Theorem (8.39) with Comment (8.41)(2)**: over a standard Borel state space, a
shift-invariant absolutely summable pair potential on `ℤ` with `δ(Φ_{{0,n}}) ≤ c n^{-p}` and
`p > 2` has exactly one Gibbs measure. -/
theorem existsUnique_isGibbs_of_pair_rpow_le [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  haveI := Bridge.isPotentialLib hΦ
  haveI := Bridge.isSummableLib hΦ
  haveI := Bridge.isAbsolutelySummableLib habs
  have hshift' : ∀ (n : ℤ) (A : Finset ℤ),
      MeasureTheory.GibbsMeasure.Dobrushin.osc
          ((Φ : Potential ℤ E) (MeasureTheory.GibbsMeasure.shiftFinset n A))
        = MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) A) := by
    intro n A
    rw [← Bridge.shiftFinset_eq, ← Bridge.osc_eq, ← Bridge.osc_eq]
    exact hshift n A
  have hpair' : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) →
      MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) A) = 0 := by
    intro A hA
    rw [← Bridge.osc_eq]
    exact hpair A hA
  have hbd' : ∀ n : ℕ, 0 < n →
      MeasureTheory.GibbsMeasure.Dobrushin.osc ((Φ : Potential ℤ E) {0, (n : ℤ)})
        ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p)) := by
    intro n hn
    rw [← Bridge.osc_eq]
    exact hbd n hn
  have h840' : (⨆ i : ℤ, MeasureTheory.GibbsMeasure.oscSpan (Φ : Potential ℤ E) i) ≠ ⊤ :=
    MeasureTheory.GibbsMeasure.iSup_oscSpan_ne_top_of_oscSpanDiam_ne_top hshift'
      (MeasureTheory.GibbsMeasure.oscSpanDiam_ne_top_of_pair_rpow_le hpair' hp hbd')
  exact Bridge.existsUnique_isGibbs hΦ habs lam β h840'

/-- Non-vacuity: the zero potential satisfies every hypothesis assembled above at once, and its
Gibbsian specification is the independent specification `λ_Λ(·|ω)`, not a degenerate one. -/
theorem exists_potential_of_forall_hypotheses (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    ∃ Φ : Finset ℤ → Config ℤ E → ℝ,
      IsPotential Φ ∧ IsAbsolutelySummable Φ ∧ IsAdmissible Φ lam β ∧
      (⨆ i : ℤ, oscSpan Φ i) ≠ ⊤ ∧
      (∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A)) ∧
      (∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0) ∧
      (∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (1 * (n : ℝ) ^ (-(3 : ℝ)))) ∧
      ∀ (Λ : Finset ℤ) (ω : Config ℤ E), gibbsKernel Φ lam β Λ ω = freeMeasure lam Λ ω := by
  refine ⟨fun (_ : Finset ℤ) (_ : Config ℤ E) ↦ (0 : ℝ), isPotential_zero,
    isAbsolutelySummable_zero, isAdmissible_zero lam β, iSup_oscSpan_zero_ne_top,
    fun n A ↦ rfl, fun A _ ↦ osc_const 0, fun n _ ↦ ?_, fun Λ ω ↦ gibbsKernel_zero lam β Λ ω⟩
  simp

end OneDimChallenge

end

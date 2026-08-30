import Comparator.Defs_Existence
import GibbsMeasure

/-!
# Comparator solution: existence and compactness of Gibbs measures (Georgii (4.22), (4.23))

This is the *solution* file matching `Comparator/Challenge_Existence.lean`.  Both files take their
definitions from the same modules `Comparator.Defs` and `Comparator.Defs_Existence`, which import
`Mathlib` and nothing else, so the statements of the theorems below are literally the challenge's
statements; the only differences are the extra `import GibbsMeasure`, this module docstring, an
auxiliary `namespace Bridge` block translating between those from-scratch definitions and the
`GibbsMeasure` library, and the proof terms.

## The bridge to the `GibbsMeasure` library

The `Bridge` namespace below is the only part of this file that is absent from
`Comparator/Challenge_Existence.lean`. It identifies, for every absolutely summable potential `Φ`,
the from-scratch objects of `Comparator.Defs` and `Comparator.Defs_Existence` with the
corresponding objects of the `GibbsMeasure` library:

* `Bridge.hamiltonian_eq`: `H_Λ` is `Potential.hamiltonian`;
* `Bridge.freeMeasure_eq`: `λ_Λ^ω` is `Specification.isssd`;
* `Bridge.gibbsKernel_eq`: **the finite-volume Gibbs distribution written out there is literally
  the `Λ`-kernel of `Potential.gibbsSpecificationOfAbsolutelySummable`**;
* `Bridge.isGibbs_iff`: consequently those DLR equations are the library's
  `Specification.IsGibbsMeasure`;
* `Bridge.continuous_coeMeasure`: the library's topology of local convergence on
  `ProbabilityMeasure` maps continuously onto the preamble's `localTopology`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Bridge

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Filter Topology
open scoped ENNReal Topology

variable {S E : Type*} [MeasurableSpace E]

/-! ### Potentials -/

theorem isPotential {Φ : Finset S → Config S E → ℝ} (hΦ : IsAbsolutelySummablePotential Φ) :
    Potential.IsPotential (Φ : Potential S E) :=
  ⟨fun A => hΦ.measurable_inside A⟩

theorem normAt_eq (Φ : Finset S → Config S E → ℝ) (i : S) :
    potentialNormAt Φ i = Potential.normAt (Φ : Potential S E) i := by
  simp only [potentialNormAt, Potential.normAt, Real.enorm_eq_ofReal_abs]

theorem isAbsolutelySummable {Φ : Finset S → Config S E → ℝ}
    (hΦ : IsAbsolutelySummablePotential Φ) :
    Potential.IsAbsolutelySummable (Φ : Potential S E) :=
  ⟨fun i => by rw [← normAt_eq]; exact hΦ.normAt_ne_top i⟩

variable (Φ : Finset S → Config S E → ℝ)

theorem hamiltonian_eq [Potential.IsAbsolutelySummable (Φ : Potential S E)]
    (Λ : Finset S) (ω : Config S E) :
    hamiltonian Φ Λ ω = Potential.hamiltonian (Φ : Potential S E) Λ ω := by
  rw [Potential.hamiltonian_eq_tsum, hamiltonian]
  congr 1
  funext A
  have hset : {A : Finset S | ∃ i ∈ A, i ∈ Λ} = {A : Finset S | ¬ Disjoint A Λ} := by
    ext B; simp [Finset.not_disjoint_iff]
  rw [hset]
  rfl

theorem boltzmannFactor_eq [Potential.IsAbsolutelySummable (Φ : Potential S E)] (β : ℝ)
    (Λ : Finset S) :
    boltzmannFactor Φ β Λ = Potential.boltzmannFactor (Φ : Potential S E) β Λ := by
  funext σ
  rw [boltzmannFactor, Potential.boltzmannFactor, hamiltonian_eq]

/-! ### The finite-volume kernels -/

theorem freeMeasure_eq (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S)
    (ω : Config S E) : freeMeasure ν Λ ω = Specification.isssd (S := S) (E := E) ν Λ ω := by
  rw [freeMeasure]
  show Measure.map (fun ζ : Λ → E => extend Λ ζ ω) (Measure.pi fun _ : Λ => ν)
      = Measure.map (juxt (Λ : Set S) ω) (Measure.pi fun _ : Λ ↦ ν)
  congr 1
  funext ζ i
  by_cases h : i ∈ Λ <;> simp [extend, juxt, h]

theorem freeMeasure_extend (ν : Measure E) (Λ : Finset S) (ω : Config S E) (ζ : Λ → E) :
    freeMeasure ν Λ (extend Λ ζ ω) = freeMeasure ν Λ ω := by
  rw [freeMeasure, freeMeasure]
  congr 1
  funext ζ' i
  by_cases h : i ∈ Λ <;> simp [extend, h]

theorem partitionFunction_extend (ν : Measure E) (β : ℝ) (Λ : Finset S) (ω : Config S E)
    (ζ : Λ → E) :
    partitionFunction Φ ν β Λ (extend Λ ζ ω) = partitionFunction Φ ν β Λ ω := by
  rw [partitionFunction, partitionFunction, freeMeasure_extend]

theorem partitionFunction_eq [Potential.IsAbsolutelySummable (Φ : Potential S E)]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    partitionFunction Φ ν β Λ ω
      = Specification.premodifierZ (S := S) (E := E) ν
          (Potential.boltzmannFactor (Φ : Potential S E) β) Λ ω := by
  rw [partitionFunction, Specification.premodifierZ, boltzmannFactor_eq, freeMeasure_eq]

variable [Countable S] [Potential.IsPotential (Φ : Potential S E)]
  [Potential.IsAbsolutelySummable (Φ : Potential S E)]

/-- The library's Gibbsian specification of `Φ`. -/
def libSpec (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) : Specification S E :=
  Potential.gibbsSpecificationOfAbsolutelySummable (Φ := (Φ : Potential S E)) ν β

/-- **The key identification.** The finite-volume Gibbs distribution written out from first
principles above is exactly the `Λ`-kernel of the library's Gibbsian specification. -/
theorem gibbsKernel_eq (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    gibbsKernel Φ ν β Λ ω = libSpec Φ ν β Λ ω := by
  have hbfmeas : Measurable (Potential.boltzmannFactor (Φ : Potential S E) β Λ) :=
    Potential.measurable_boltzmannFactor (Φ := (Φ : Potential S E)) β Λ
  show _ = (Specification.isssd (S := S) (E := E) ν Λ ω).withDensity
      (Specification.premodifierNorm (S := S) (E := E) ν
        (Potential.boltzmannFactor (Φ : Potential S E) β) Λ)
  rw [← freeMeasure_eq ν Λ ω]
  refine Measure.ext fun A hA => ?_
  rw [gibbsKernel, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA, withDensity_apply _ hA,
    ← lintegral_indicator hA, ← lintegral_indicator hA, freeMeasure,
    lintegral_map ?_ (measurable_extend Λ ω), lintegral_map ?_ (measurable_extend Λ ω),
    ← lintegral_const_mul _ ?_]
  · refine lintegral_congr fun ζ => ?_
    by_cases hmem : extend Λ ζ ω ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Specification.premodifierNorm,
        ← partitionFunction_eq, partitionFunction_extend, boltzmannFactor_eq,
        partitionFunction_eq, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
  · rw [boltzmannFactor_eq]
    exact (hbfmeas.indicator hA).comp (measurable_extend Λ ω)
  · exact (Specification.premodifierNorm_measurable ν
      (Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β) Λ).indicator hA
  · rw [boltzmannFactor_eq]
    exact hbfmeas.indicator hA

/-! ### The DLR equations -/

theorem isGibbs_iff (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (μ : Measure (Config S E)) [IsProbabilityMeasure μ] :
    IsGibbs (gibbsKernel Φ ν β) μ ↔ Specification.IsGibbsMeasure (libSpec Φ ν β) μ := by
  have hmeas : ∀ Λ : Finset S, AEMeasurable (libSpec Φ ν β Λ) μ := fun Λ =>
    ((libSpec Φ ν β).measurable_kernel_toMeasure Λ).aemeasurable
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  constructor
  · rintro ⟨-, h⟩ Λ
    refine Measure.ext fun A hA => ?_
    rw [Measure.bind_apply hA (hmeas Λ), h Λ A hA]
    exact lintegral_congr fun ω => by rw [gibbsKernel_eq]
  · refine fun h => ⟨inferInstance, fun Λ A hA => ?_⟩
    conv_lhs => rw [← h Λ]
    rw [Measure.bind_apply hA (hmeas Λ)]
    exact lintegral_congr fun ω => by rw [gibbsKernel_eq]

/-! ### The topology of local convergence -/

/-- The forgetful map from the library's space of probability measures with the topology of local
convergence to plain measures. -/
def coeMeasure (μ : WithLocalConvergence S E) : Measure (Config S E) :=
  (μ.toMeasure : Measure (S → E))

instance isProbabilityMeasure_coeMeasure (μ : WithLocalConvergence S E) :
    IsProbabilityMeasure (coeMeasure μ) := by
  show IsProbabilityMeasure ((μ.toMeasure : Measure (S → E)))
  infer_instance

omit [Countable S] [Potential.IsPotential (Φ : Potential S E)]
  [Potential.IsAbsolutelySummable (Φ : Potential S E)] in
theorem isLocalEvent_iff {A : Set (Config S E)} : IsLocalEvent A ↔ A ∈ localEvents S E :=
  MeasureTheory.mem_localEvents_iff_cylinderEvents.symm

omit [Countable S] [Potential.IsPotential (Φ : Potential S E)]
  [Potential.IsAbsolutelySummable (Φ : Potential S E)] in
theorem continuous_coeMeasure :
    @Continuous (WithLocalConvergence S E) (Measure (Config S E)) _ localTopology coeMeasure := by
  show @Continuous _ _ _ (⨅ A : {A : Set (Config S E) // IsLocalEvent A},
    TopologicalSpace.induced (fun μ : Measure (Config S E) => μ A.1) inferInstance) coeMeasure
  refine continuous_iInf_rng.2 fun A => ?_
  rw [continuous_induced_rng]
  exact (continuous_apply (⟨A.1, isLocalEvent_iff.1 A.2⟩ : localEvents S E)).comp
    WithSetwiseTopology.isInducing_evalProb.continuous

/-- The library's set of Gibbs measures for `Φ`, inside the space of probability measures carrying
the topology of local convergence. -/
def gibbsSet (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) : Set (WithLocalConvergence S E) :=
  {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) (libSpec Φ ν β)}

theorem setOf_isGibbs_eq_image (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    {μ : Measure (Config S E) | IsGibbs (gibbsKernel Φ ν β) μ}
      = coeMeasure '' gibbsSet Φ ν β := by
  ext μ
  constructor
  · rintro ⟨hp, h⟩
    haveI := hp
    exact ⟨WithSetwiseTopology.ofMeasure ⟨μ, hp⟩, (isGibbs_iff Φ ν β μ).1 ⟨hp, h⟩, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact (isGibbs_iff Φ ν β (coeMeasure P)).2 hP

theorem mem_image_of_isGibbs (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    {μ : Measure (Config S E)} (hμ : IsGibbs (gibbsKernel Φ ν β) μ) :
    μ ∈ coeMeasure '' gibbsSet Φ ν β := by
  rw [← setOf_isGibbs_eq_image]
  exact hμ

theorem isCompact_image_gibbsSet [StandardBorelSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology (coeMeasure '' gibbsSet Φ ν β) := by
  letI : TopologicalSpace (Measure (Config S E)) := localTopology
  exact (Potential.isCompact_setOf_mem_GP_gibbsSpecification
    (Φ := (Φ : Potential S E)) ν β).image continuous_coeMeasure

end Bridge

namespace Bridge

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Filter Topology
open scoped ENNReal Topology

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]

theorem isCompact_image_closure_iUnion_gibbsSet {ι : Type*}
    (Φs : ι → Finset S → Config S E → ℝ)
    [∀ i, Potential.IsPotential ((Φs i : Potential S E))]
    [∀ i, Potential.IsAbsolutelySummable ((Φs i : Potential S E))]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (hb : ∀ a : S, (⨆ i, Potential.normAt ((Φs i : Potential S E)) a) < ⊤) :
    @IsCompact (Measure (Config S E)) localTopology
      (coeMeasure '' closure (⋃ i, gibbsSet (Φs i) ν β)) := by
  letI : TopologicalSpace (Measure (Config S E)) := localTopology
  exact (Potential.isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top
    (fun i => (Φs i : Potential S E)) ν β hb).image continuous_coeMeasure

end Bridge

/-! ## The theorems -/

/-- **Georgii (2.9)/(2.10).** The Gibbsian specification of an absolutely summable potential really
is a specification in the sense of the preamble: a consistent family of proper probability kernels
from the exterior σ-algebra `𝓣_Λ`. -/
theorem isSpecification_gibbsKernel [Countable S] (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    IsSpecification (gibbsKernel Φ ν β) := by
  haveI := Bridge.isPotential hΦ
  haveI := Bridge.isAbsolutelySummable hΦ
  refine ⟨fun Λ ω => ?_, fun Λ A hA => ?_, fun Λ => ?_, fun Λ Δ hΛΔ ω A hA => ?_⟩
  · rw [Bridge.gibbsKernel_eq]
    infer_instance
  · simp only [Bridge.gibbsKernel_eq]
    exact ProbabilityTheory.Kernel.measurable_coe (Bridge.libSpec Φ ν β Λ) hA
  · intro A B hA hB ω
    rw [Bridge.gibbsKernel_eq, (Bridge.libSpec Φ ν β).isProper.inter_eq_indicator_mul Λ hA hB ω]
    by_cases hωB : ω ∈ B <;> simp [hωB]
  · simp only [Bridge.gibbsKernel_eq]
    rw [← Measure.bind_apply hA
      ((Bridge.libSpec Φ ν β).measurable_kernel_toMeasure Λ).aemeasurable,
      Specification.bind hΛΔ ω]

/-- **Georgii, Theorem (4.22).** Over a standard Borel state space, and for an absolutely summable
potential, the set of Gibbs measures of the Gibbsian specification is non-empty. -/
theorem exists_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    ∃ μ : Measure (Config S E), IsGibbs (gibbsKernel Φ ν β) μ := by
  haveI := Bridge.isPotential hΦ
  haveI := Bridge.isAbsolutelySummable hΦ
  obtain ⟨μ, hμ⟩ := Potential.GP_gibbsSpecification_nonempty (Φ := (Φ : Potential S E)) ν β
  exact ⟨(μ : Measure (Config S E)), (Bridge.isGibbs_iff Φ ν β _).2 hμ⟩

/-- **Georgii, Theorem (4.23)(a).** The set of Gibbs measures of an absolutely summable potential
is compact in the topology of local convergence. -/
theorem isCompact_setOf_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology {μ | IsGibbs (gibbsKernel Φ ν β) μ} := by
  haveI := Bridge.isPotential hΦ
  haveI := Bridge.isAbsolutelySummable hΦ
  rw [Bridge.setOf_isGibbs_eq_image Φ ν β]
  exact Bridge.isCompact_image_gibbsSet Φ ν β

/-- **Georgii, Theorem (4.23)(b).** If a family `(Φ_i)` of absolutely summable potentials is
bounded in `ℬ`, i.e. `sup_i ‖Φ_i‖_a < ∞` for every site `a`, then the union of the corresponding
sets of Gibbs measures is relatively compact in the topology of local convergence: it is contained
in a compact set of probability measures. -/
theorem exists_isCompact_superset_iUnion_setOf_isGibbs [Countable S] [StandardBorelSpace E]
    {ι : Type*} (Φs : ι → Finset S → Config S E → ℝ)
    (hΦs : ∀ i, IsAbsolutelySummablePotential (Φs i))
    (hbdd : ∀ a : S, (⨆ i, potentialNormAt (Φs i) a) < ⊤)
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    ∃ K : Set (Measure (Config S E)), @IsCompact (Measure (Config S E)) localTopology K ∧
      (∀ μ ∈ K, IsProbabilityMeasure μ) ∧
      (⋃ i, {μ : Measure (Config S E) | IsGibbs (gibbsKernel (Φs i) ν β) μ}) ⊆ K := by
  haveI : ∀ i, Potential.IsPotential ((Φs i : Potential S E)) :=
    fun i => Bridge.isPotential (hΦs i)
  haveI : ∀ i, Potential.IsAbsolutelySummable ((Φs i : Potential S E)) :=
    fun i => Bridge.isAbsolutelySummable (hΦs i)
  have hb : ∀ a : S, (⨆ i, Potential.normAt ((Φs i : Potential S E)) a) < ⊤ := by
    intro a
    simpa only [Bridge.normAt_eq] using hbdd a
  refine ⟨Bridge.coeMeasure '' closure (⋃ i, Bridge.gibbsSet (Φs i) ν β),
    Bridge.isCompact_image_closure_iUnion_gibbsSet Φs ν β hb, ?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    infer_instance
  rintro μ hμ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hμ
  obtain ⟨P, hP, rfl⟩ := Bridge.mem_image_of_isGibbs (Φs i) ν β hi
  exact ⟨P, subset_closure (Set.mem_iUnion.2 ⟨i, hP⟩), rfl⟩

end GibbsChallenge

end

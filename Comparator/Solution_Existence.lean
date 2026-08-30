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

## The a priori measure is an arbitrary finite `λ ∈ 𝓜(E, ℰ)`

Georgii's Theorem (4.23) is stated for a finite, non-zero, **un-normalized** a priori measure, and
by his (2.14) finiteness of `λ` is exactly `λ`-admissibility of a potential `Φ ∈ ℬ`.  The
`GibbsMeasure` library supports this generality directly, in
`GibbsMeasure/Potential/FiniteReference.lean`, which is built on Georgii's rescaling Remark
(1.28)(3) as formalized in `GibbsMeasure/Specification/Rescaling.lean`.  The bridge below therefore
identifies the challenge's `gibbsKernel` with `Potential.gibbsSpecificationOfFiniteReference`, and
the four theorems are discharged by

* `Potential.GP_gibbsSpecificationOfFiniteReference_nonempty` — (4.22)/(4.23)(a), existence;
* `Potential.isCompact_setOf_mem_GP_gibbsSpecificationOfFiniteReference` — (4.23)(a), compactness;
* `Potential.isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top_ofFiniteReference` —
  (4.23)(b).

## The bridge to the `GibbsMeasure` library

The `Bridge` namespace below is the only part of this file that is absent from
`Comparator/Challenge_Existence.lean`. It identifies, for every absolutely summable potential `Φ`,
the from-scratch objects of `Comparator.Defs` and `Comparator.Defs_Existence` with the
corresponding objects of the `GibbsMeasure` library:

* `Bridge.hamiltonian_eq`: `H_Λ` is `Potential.hamiltonian`;
* `Bridge.freeMeasure_eq`: `λ_Λ^ω` is `Specification.sigmaFiniteLambdaFun`, the kernel of Georgii's
  Notation (1.26) for a general — here finite — a priori measure;
* `Bridge.partitionFunction_eq`: `Z_Λ(ω)` is `Specification.sigmaFiniteLambdaZ`, Georgii (2.7);
* `Bridge.gibbsKernel_eq`: **the finite-volume Gibbs distribution written out there is literally
  the `Λ`-kernel of `Potential.gibbsSpecificationOfFiniteReference`**;
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


/-! ### Georgii's index set `𝒮` of non-empty volumes

Georgii's potentials are indexed by the *non-empty* finite volumes, and the library's space `ℬ`
records this by demanding `Φ ∅ = 0`.  The challenge imposes no such normalisation, so the bridge
truncates: `trunc Φ` is `Φ` with its value at `∅` replaced by `0`.  Nothing is lost, because the
value at `∅` enters neither the interaction norms `‖·‖ᵢ` nor the Hamiltonians, hence neither the
Gibbsian specification: `potentialNormAt_congr`, `gibbsKernel_congr` below. -/

open Classical in
/-- `Φ` with its value at the empty volume set to `0`. -/
def trunc (Φ : Finset S → Config S E → ℝ) : Finset S → Config S E → ℝ :=
  fun A ω ↦ if A = ∅ then 0 else Φ A ω

omit [MeasurableSpace E] in
theorem trunc_apply_of_ne {Φ : Finset S → Config S E → ℝ} {A : Finset S} (hA : A ≠ ∅) :
    trunc Φ A = Φ A := by
  funext ω; simp [trunc, hA]

omit [MeasurableSpace E] in
@[simp] theorem trunc_empty (Φ : Finset S → Config S E → ℝ) :
    trunc Φ (∅ : Finset S) = 0 := by
  funext ω; simp [trunc]

omit [MeasurableSpace E] in
/-- The interaction norms do not see the value at `∅`. -/
theorem potentialNormAt_congr {Φ Ψ : Finset S → Config S E → ℝ}
    (h : ∀ A : Finset S, A ≠ ∅ → Φ A = Ψ A) (i : S) :
    potentialNormAt Φ i = potentialNormAt Ψ i := by
  refine tsum_congr fun A ↦ ?_
  by_cases hA : A ∈ {A : Finset S | i ∈ A}
  · have hne : A ≠ ∅ := by
      rintro rfl
      simp at hA
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, h A hne]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

omit [MeasurableSpace E] in
/-- The Hamiltonians do not see the value at `∅`. -/
theorem hamiltonian_congr {Φ Ψ : Finset S → Config S E → ℝ}
    (h : ∀ A : Finset S, A ≠ ∅ → Φ A = Ψ A) (Λ : Finset S) (ω : Config S E) :
    hamiltonian Φ Λ ω = hamiltonian Ψ Λ ω := by
  refine tsum_congr fun A ↦ ?_
  by_cases hA : A ∈ {A : Finset S | ∃ i ∈ A, i ∈ Λ}
  · have hne : A ≠ ∅ := by
      obtain ⟨i, hiA, -⟩ := hA
      rintro rfl
      simp at hiA
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA, h A hne]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

/-- The Gibbsian specification does not see the value at `∅`. -/
theorem gibbsKernel_congr {Φ Ψ : Finset S → Config S E → ℝ}
    (h : ∀ A : Finset S, A ≠ ∅ → Φ A = Ψ A) (ν : Measure E) (β : ℝ) (Λ : Finset S)
    (ω : Config S E) : gibbsKernel Φ ν β Λ ω = gibbsKernel Ψ ν β Λ ω := by
  have hb : boltzmannFactor Φ β Λ = boltzmannFactor Ψ β Λ := by
    funext σ
    rw [boltzmannFactor, boltzmannFactor, hamiltonian_congr h]
  rw [gibbsKernel, gibbsKernel, partitionFunction, partitionFunction, hb]

/-! ### The finite-volume kernels

Georgii's Notation (1.26) attaches to *any* `λ ∈ 𝓜(E, ℰ)` the proper kernels
`λ_Λ(·|ω) = λ^Λ × δ_{ω_{S∖Λ}}`.  In the library these are `Specification.sigmaFiniteLambdaFun`;
`Specification.isssd` is their special case for a probability measure, which we do **not** use
here, since Theorem (4.23) allows an arbitrary finite `λ`. -/

theorem freeMeasure_eq (ν : Measure E) [SigmaFinite ν] (Λ : Finset S)
    (ω : Config S E) :
    freeMeasure ν Λ ω = Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω := by
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map]
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
    (ν : Measure E) [SigmaFinite ν] (β : ℝ) (Λ : Finset S) (ω : Config S E) :
    partitionFunction Φ ν β Λ ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
          (Potential.boltzmannFactor (Φ : Potential S E) β) Λ ω := by
  rw [partitionFunction, Specification.sigmaFiniteLambdaZ, boltzmannFactor_eq, freeMeasure_eq]

variable [Countable S] [Potential.IsPotential (Φ : Potential S E)]
  [Potential.IsAbsolutelySummable (Φ : Potential S E)]

/-- The library's Gibbsian specification of `Φ` over an arbitrary finite non-zero a priori
measure, Georgii Definition (2.9). -/
def libSpec (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) : Specification S E :=
  Potential.gibbsSpecificationOfFiniteReference (Φ := (Φ : Potential S E)) ν β

/-- **The key identification.** The finite-volume Gibbs distribution written out from first
principles above is exactly the `Λ`-kernel of the library's Gibbsian specification for the same
un-normalized a priori measure. -/
theorem gibbsKernel_eq (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (Λ : Finset S) (ω : Config S E) :
    gibbsKernel Φ ν β Λ ω = libSpec Φ ν β Λ ω := by
  have hbfmeas : Measurable (Potential.boltzmannFactor (Φ : Potential S E) β Λ) :=
    Potential.measurable_boltzmannFactor (Φ := (Φ : Potential S E)) β Λ
  show _ = (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω).withDensity
      (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
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
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
        Specification.sigmaFinitePremodifierNorm,
        ← partitionFunction_eq, partitionFunction_extend, boltzmannFactor_eq,
        partitionFunction_eq, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]
  · rw [boltzmannFactor_eq]
    exact (hbfmeas.indicator hA).comp (measurable_extend Λ ω)
  · exact (Specification.sigmaFinitePremodifierNorm_measurable ν
      (Potential.isPremodifier_boltzmannFactor (Φ := (Φ : Potential S E)) β) Λ).indicator hA
  · rw [boltzmannFactor_eq]
    exact hbfmeas.indicator hA

/-! ### The DLR equations -/

theorem isGibbs_iff (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
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
def gibbsSet (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    Set (WithLocalConvergence S E) :=
  {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) (libSpec Φ ν β)}

theorem setOf_isGibbs_eq_image (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    {μ : Measure (Config S E) | IsGibbs (gibbsKernel Φ ν β) μ}
      = coeMeasure '' gibbsSet Φ ν β := by
  ext μ
  constructor
  · rintro ⟨hp, h⟩
    haveI := hp
    exact ⟨WithSetwiseTopology.ofMeasure ⟨μ, hp⟩, (isGibbs_iff Φ ν β μ).1 ⟨hp, h⟩, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact (isGibbs_iff Φ ν β (coeMeasure P)).2 hP

theorem mem_image_of_isGibbs (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    {μ : Measure (Config S E)} (hμ : IsGibbs (gibbsKernel Φ ν β) μ) :
    μ ∈ coeMeasure '' gibbsSet Φ ν β := by
  rw [← setOf_isGibbs_eq_image]
  exact hμ

theorem isCompact_image_gibbsSet [StandardBorelSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology (coeMeasure '' gibbsSet Φ ν β) := by
  letI : TopologicalSpace (Measure (Config S E)) := localTopology
  exact (Potential.isCompact_setOf_mem_GP_gibbsSpecificationOfFiniteReference
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
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (hb : ∀ a : S, (⨆ i, Potential.normAt ((Φs i : Potential S E)) a) < ⊤) :
    @IsCompact (Measure (Config S E)) localTopology
      (coeMeasure '' closure (⋃ i, gibbsSet (Φs i) ν β)) := by
  letI : TopologicalSpace (Measure (Config S E)) := localTopology
  exact (Potential.isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top_ofFiniteReference
    (fun i => (Φs i : Potential S E)) ν β hb).image continuous_coeMeasure

end Bridge


namespace Bridge

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Filter Topology
open scoped ENNReal Topology

variable {S E : Type*} [MeasurableSpace E] [Countable S]

/-- Truncating at `∅` preserves absolute summability. -/
theorem isAbsolutelySummablePotential_trunc {Φ : Finset S → Config S E → ℝ}
    (hΦ : IsAbsolutelySummablePotential Φ) : IsAbsolutelySummablePotential (trunc Φ) where
  measurable_inside A := by
    by_cases hA : A = ∅
    · subst hA
      rw [trunc_empty]
      exact measurable_const
    · rw [trunc_apply_of_ne hA]
      exact hΦ.measurable_inside A
  normAt_ne_top i := by
    rw [potentialNormAt_congr (fun A hA ↦ trunc_apply_of_ne hA) i]
    exact hΦ.normAt_ne_top i

/-- An absolutely summable potential of the challenge, as an element of Georgii's Fréchet space
`ℬ` of (2.11).  Its value at the empty volume is discarded — Georgii's index set `𝒮` consists of
the non-empty finite volumes. -/
def toBSpace {Φ : Finset S → Config S E → ℝ} (hΦ : IsAbsolutelySummablePotential Φ) :
    Potential.BSpace S E :=
  ⟨(trunc Φ : Potential S E), isAbsolutelySummable (isAbsolutelySummablePotential_trunc hΦ),
    trunc_empty Φ, isPotential (isAbsolutelySummablePotential_trunc hΦ)⟩

@[simp] theorem coe_toBSpace {Φ : Finset S → Config S E → ℝ}
    (hΦ : IsAbsolutelySummablePotential Φ) :
    ((toBSpace hΦ : Potential.BSpace S E) : Potential S E) = trunc Φ := rfl

/-- The DLR equations of the challenge are membership in the library's `𝒢(Φ)`. -/
theorem isGibbs_iff_isGibbsMeasure {Φ : Finset S → Config S E → ℝ}
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (μ : Measure (Config S E)) [IsProbabilityMeasure μ] :
    IsGibbs (gibbsKernel Φ ν β) μ ↔
      Specification.IsGibbsMeasure
        (Potential.BSpace.gibbsSpecificationOfFiniteReference ν β (toBSpace hΦ)) μ := by
  haveI := isPotential (isAbsolutelySummablePotential_trunc hΦ)
  haveI := isAbsolutelySummable (isAbsolutelySummablePotential_trunc hΦ)
  have hk : gibbsKernel Φ ν β = gibbsKernel (trunc Φ) ν β :=
    funext fun Λ ↦ funext fun ω ↦
      (gibbsKernel_congr (fun A hA ↦ trunc_apply_of_ne hA) ν β Λ ω).symm
  rw [hk]
  exact isGibbs_iff (trunc Φ) ν β μ

/-- Convergence of the interaction norms is convergence in Georgii's Fréchet space `ℬ`. -/
theorem tendsto_toBSpace {ι : Type*} {l : Filter ι} {Φs : ι → Finset S → Config S E → ℝ}
    {Φ : Finset S → Config S E → ℝ} (hΦs : ∀ x, IsAbsolutelySummablePotential (Φs x))
    (hΦ : IsAbsolutelySummablePotential Φ)
    (hconv : ∀ a : S,
      Tendsto (fun x ↦ potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a) l (nhds 0)) :
    Tendsto (fun x ↦ toBSpace (hΦs x)) l (nhds (toBSpace hΦ)) := by
  rw [Potential.tendsto_iff_tendsto_seminormAt]
  intro a
  have heq : ∀ x, Potential.seminormAt S E a (toBSpace (hΦs x) - toBSpace hΦ)
      = (potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a).toReal := by
    intro x
    rw [Potential.seminormAt_apply, Submodule.coe_sub, coe_toBSpace, coe_toBSpace,
      ← normAt_eq]
    congr 1
    refine potentialNormAt_congr (fun A hA ↦ ?_) a
    funext ω
    show trunc (Φs x) A ω - trunc Φ A ω = Φs x A ω - Φ A ω
    rw [trunc_apply_of_ne hA, trunc_apply_of_ne hA]
  simp only [heq]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hconv a)

omit [Countable S] in
/-- Local convergence of probability measures is convergence in the library's space
`WithLocalConvergence`. -/
theorem tendsto_ofMeasure {ι : Type*} {l : Filter ι} (μs : ι → Measure (Config S E))
    (hμs : ∀ x, IsProbabilityMeasure (μs x)) (μ : Measure (Config S E))
    (hμ : IsProbabilityMeasure μ) (hloc : TendstoLocally μs l μ) :
    Tendsto (fun x ↦ (WithSetwiseTopology.ofMeasure ⟨μs x, hμs x⟩ : WithLocalConvergence S E)) l
      (nhds (WithSetwiseTopology.ofMeasure ⟨μ, hμ⟩ : WithLocalConvergence S E)) := by
  rw [tendsto_withLocalConvergence_iff]
  exact fun A hA ↦ hloc A (isLocalEvent_iff.2 hA)

end Bridge

/-! ## The theorems -/

/-- **Georgii (2.9)/(2.10).** The Gibbsian specification of an absolutely summable potential really
is a specification in the sense of the preamble: a consistent family of proper probability kernels
from the exterior σ-algebra `𝓣_Λ`.  The a priori measure is an arbitrary finite non-zero
`λ ∈ 𝓜(E, ℰ)`, as in Georgii's Definition (2.9); by (2.14) finiteness is exactly `λ`-admissibility
of `Φ ∈ ℬ`. -/
theorem isSpecification_gibbsKernel [Countable S] (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
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
potential and a finite non-zero a priori measure, the set of Gibbs measures of the Gibbsian
specification is non-empty. -/
theorem exists_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    ∃ μ : Measure (Config S E), IsGibbs (gibbsKernel Φ ν β) μ := by
  haveI := Bridge.isPotential hΦ
  haveI := Bridge.isAbsolutelySummable hΦ
  obtain ⟨μ, hμ⟩ :=
    Potential.GP_gibbsSpecificationOfFiniteReference_nonempty (Φ := (Φ : Potential S E)) ν β
  exact ⟨(μ : Measure (Config S E)), (Bridge.isGibbs_iff Φ ν β _).2 hμ⟩

/-- **Georgii, Theorem (4.23)(a).** For a standard Borel `(E, ℰ)` and a finite `λ ∈ 𝓜(E, ℰ)`, the
set of Gibbs measures of an absolutely summable potential is compact in the topology of local
convergence. -/
theorem isCompact_setOf_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology {μ | IsGibbs (gibbsKernel Φ ν β) μ} := by
  haveI := Bridge.isPotential hΦ
  haveI := Bridge.isAbsolutelySummable hΦ
  rw [Bridge.setOf_isGibbs_eq_image Φ ν β]
  exact Bridge.isCompact_image_gibbsSet Φ ν β

/-- **Georgii, Theorem (4.23)(b).** If a family `(Φ_i)` of absolutely summable potentials is
bounded in `ℬ`, i.e. `sup_i ‖Φ_i‖_a < ∞` for every site `a`, then the union of the corresponding
sets of Gibbs measures — taken with respect to one and the same finite `λ ∈ 𝓜(E, ℰ)` — is
relatively compact in the topology of local convergence: it is contained in a compact set of
probability measures. -/
theorem exists_isCompact_superset_iUnion_setOf_isGibbs [Countable S] [StandardBorelSpace E]
    {ι : Type*} (Φs : ι → Finset S → Config S E → ℝ)
    (hΦs : ∀ i, IsAbsolutelySummablePotential (Φs i))
    (hbdd : ∀ a : S, (⨆ i, potentialNormAt (Φs i) a) < ⊤)
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
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

/-- **Georgii, Theorem (4.23)(c): the graph of the Gibbs correspondence is closed.** Let `(Φ_x)` be
a net of absolutely summable potentials converging to `Φ` in Georgii's Fréchet space `ℬ`, i.e.
`‖Φ_x − Φ‖_a → 0` for every site `a`, and let `μ_x ∈ 𝒢(Φ_x)` converge to a probability measure `μ`
in the topology of local convergence.  Then `μ ∈ 𝒢(Φ)`.  (This is closedness of the graph
`{(Φ, μ) : μ ∈ 𝒢(Φ)} ⊆ ℬ × 𝒫(Ω, 𝓕)` in net form; as Georgii remarks, it does not need the state
space to be standard Borel.) -/
theorem isGibbs_of_tendsto_potentialNormAt_of_tendstoLocally [Countable S] {ι : Type*}
    {l : Filter ι} [l.NeBot] (Φs : ι → Finset S → Config S E → ℝ)
    (Φ : Finset S → Config S E → ℝ) (hΦs : ∀ x, IsAbsolutelySummablePotential (Φs x))
    (hΦ : IsAbsolutelySummablePotential Φ)
    (hconv : ∀ a : S,
      Tendsto (fun x ↦ potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a) l (nhds 0))
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (μs : ι → Measure (Config S E)) (hμs : ∀ x, IsGibbs (gibbsKernel (Φs x) ν β) (μs x))
    (μ : Measure (Config S E)) (hμ : IsProbabilityMeasure μ)
    (hloc : TendstoLocally μs l μ) :
    IsGibbs (gibbsKernel Φ ν β) μ := by
  haveI : ∀ x, IsProbabilityMeasure (μs x) := fun x ↦ (hμs x).1
  haveI := hμ
  set G : Set (Potential.BSpace S E × WithLocalConvergence S E) :=
    {p | p.2.toMeasure ∈ MeasureTheory.GibbsMeasure.GP (S := S) (E := E)
      (Potential.BSpace.gibbsSpecificationOfFiniteReference ν β p.1)} with hG
  have hclosed : IsClosed G := Potential.BSpace.isClosed_graph_GP_ofFiniteReference ν β
  have htend : Tendsto (fun x ↦ ((Bridge.toBSpace (hΦs x) : Potential.BSpace S E),
      (WithSetwiseTopology.ofMeasure ⟨μs x, inferInstance⟩ : WithLocalConvergence S E))) l
      (nhds ((Bridge.toBSpace hΦ : Potential.BSpace S E),
        (WithSetwiseTopology.ofMeasure ⟨μ, hμ⟩ : WithLocalConvergence S E))) :=
    (Bridge.tendsto_toBSpace hΦs hΦ hconv).prodMk_nhds
      (Bridge.tendsto_ofMeasure μs (fun x ↦ inferInstance) μ hμ hloc)
  have hmem : ∀ x, ((Bridge.toBSpace (hΦs x) : Potential.BSpace S E),
      (WithSetwiseTopology.ofMeasure ⟨μs x, inferInstance⟩ : WithLocalConvergence S E)) ∈ G :=
    fun x ↦ (Bridge.isGibbs_iff_isGibbsMeasure (hΦs x) ν β (μs x)).1 (hμs x)
  have hlim := hclosed.mem_of_tendsto htend (Filter.Eventually.of_forall hmem)
  exact (Bridge.isGibbs_iff_isGibbsMeasure hΦ ν β μ).2 hlim

/-- **Georgii, Theorem (4.23)(d): the Gibbs correspondence is upper semicontinuous.** Let `F` be a
set of measures which is closed in the topology of local convergence, and let `(Φ_x)` be a net of
absolutely summable potentials converging to `Φ` in `ℬ`.  If every `𝒢(Φ_x)` meets `F`, then so
does `𝒢(Φ)`.  This is Georgii's statement that `𝒢⁻¹(F) = {Φ : 𝒢(Φ) ∩ F ≠ ∅}` is closed. -/
theorem exists_mem_isGibbs_of_tendsto_potentialNormAt [Countable S] [StandardBorelSpace E]
    {ι : Type*} {l : Filter ι} [l.NeBot] (Φs : ι → Finset S → Config S E → ℝ)
    (Φ : Finset S → Config S E → ℝ) (hΦs : ∀ x, IsAbsolutelySummablePotential (Φs x))
    (hΦ : IsAbsolutelySummablePotential Φ)
    (hconv : ∀ a : S,
      Tendsto (fun x ↦ potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a) l (nhds 0))
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (F : Set (Measure (Config S E))) (hF : @IsClosed (Measure (Config S E)) localTopology F)
    (hmeet : ∀ x, ∃ ρ ∈ F, IsGibbs (gibbsKernel (Φs x) ν β) ρ) :
    ∃ ρ ∈ F, IsGibbs (gibbsKernel Φ ν β) ρ := by
  set F' : Set (WithLocalConvergence S E) := Bridge.coeMeasure ⁻¹' F with hF'
  have hF'closed : IsClosed F' := by
    letI : TopologicalSpace (Measure (Config S E)) := localTopology
    exact hF.preimage Bridge.continuous_coeMeasure
  set A : Set (Potential.BSpace S E) :=
    {Ψ | ∃ ρ ∈ F', ρ.toMeasure ∈ MeasureTheory.GibbsMeasure.GP (S := S) (E := E)
      (Potential.BSpace.gibbsSpecificationOfFiniteReference ν β Ψ)} with hA
  have hclosed : IsClosed A :=
    Potential.BSpace.isClosed_setOf_exists_mem_GP_ofFiniteReference ν β hF'closed
  have hmem : ∀ x, Bridge.toBSpace (hΦs x) ∈ A := by
    intro x
    obtain ⟨ρ, hρF, hρG⟩ := hmeet x
    haveI : IsProbabilityMeasure ρ := hρG.1
    exact ⟨WithSetwiseTopology.ofMeasure ⟨ρ, inferInstance⟩, hρF,
      (Bridge.isGibbs_iff_isGibbsMeasure (hΦs x) ν β ρ).1 hρG⟩
  have hlim := hclosed.mem_of_tendsto (Bridge.tendsto_toBSpace hΦs hΦ hconv)
    (Filter.Eventually.of_forall hmem)
  obtain ⟨ρ, hρF, hρG⟩ := hlim
  exact ⟨Bridge.coeMeasure ρ, hρF, (Bridge.isGibbs_iff_isGibbsMeasure hΦ ν β
    (Bridge.coeMeasure ρ)).2 hρG⟩

end GibbsChallenge

end

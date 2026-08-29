/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.QuasilocalSpecification
public import GibbsMeasure.Potential.Summable
public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Specification.NetEquicontinuity
public import GibbsMeasure.Topology.ClusterPoints

/-!
# Existence and compactness of Gibbs measures for absolutely summable potentials

**Georgii Theorem (4.23)(a)**: over a standard Borel state space, for every absolutely summable
potential `Φ` the set of Gibbs measures for the Gibbsian specification `γ^Φ` is non-empty and
compact in the topology of local convergence. The inputs are the uniform density bound
`ρ_Λ ≤ e^{2|β| ‖Φ‖_Λ}` (Georgii (4.14)(1), `gibbsSpecificationOfAbsolutelySummable_apply_le`),
the resulting local equicontinuity of the finite-volume Gibbs distributions (the bounded-density
case, Georgii Comment (4.14)(1), derived here from the general net Theorem (4.12) in
`GibbsMeasure/Specification/NetEquicontinuity.lean` with `B = univ`), the cluster-point
machinery of §4.2, and quasilocality (Example (2.25)).

The file also hosts the Gibbsian (Hamiltonian) form of Georgii Corollary (4.13),
`locallyEquicontinuous_of_confinement_hamiltonian`, via the density estimate
`premodifierNorm_le_of_abs_hamiltonian_le` (Georgii's `e^{2c(ℓ)} λ(K_ℓ)^{-|Λ|}`).
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

variable (Φ) in
/-- The dominating measures for the Gibbsian specification of `Φ`:
`e^{2|β| ‖Φ‖_Λ} • ν^S` on the volume `Λ` (Georgii (4.14)(1)). -/
def dominatingMeasure (Λ : Finset S) : Measure (S → E) :=
  ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) •
    Measure.infinitePi (fun _ : S ↦ ν)

instance (Λ : Finset S) : IsFiniteMeasure (dominatingMeasure Φ ν β Λ) := by
  constructor
  rw [dominatingMeasure, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

lemma gibbsSpecification_apply_le_dominatingMeasure (Λ : Finset S) (η : S → E)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η A
      ≤ dominatingMeasure Φ ν β Λ A := by
  rw [dominatingMeasure, Measure.smul_apply, smul_eq_mul]
  exact gibbsSpecificationOfAbsolutelySummable_apply_le (Φ := Φ) ν β Λ η hA

/-- **Georgii Comment (4.14)(1).** The net of finite-volume Gibbs distributions of an
absolutely summable potential is locally equicontinuous: the bounded-density case of the
general Theorem (4.12). -/
theorem locallyEquicontinuous_finiteVolumeDistributions (η : S → E) :
    LocallyEquicontinuous atTop
      (finiteVolumeDistributions (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) η) := by
  refine locallyEquicontinuous_of_eventually_boundedOn ν
    (fun _ ↦ Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (fun _ ↦ Specification.IsPremodifier.isModifier_premodifierNorm (ν := ν)
      (isPremodifier_boltzmannFactor (Φ := Φ) β)
      (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν β))
    id tendsto_id (fun _ ↦ ⟨Measure.dirac η, inferInstance⟩) _ (fun Λ ↦ ?_) (fun Λ ε hε ↦ ?_)
  · -- `δ_η γ_Λ = γ_Λ(η)`: the finite-volume distribution with deterministic boundary condition
    exact (Subtype.ext (Measure.dirac_bind
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).measurable_kernel_toMeasure Λ)
      η)).symm
  · -- global density bound: `B = univ`, `C = e^{2|β| ‖Φ‖_Λ}`
    refine ⟨univ, ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)),
      MeasurableSet.univ, ENNReal.ofReal_ne_top,
      Eventually.of_forall fun a ω _ ↦ premodifierNorm_boltzmannFactor_le (Φ := Φ) ν β Λ ω,
      ?_⟩
    have hzero : (fun Λ' : Finset S ↦
        (finiteVolumeDistributions (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) η Λ' :
          Measure (S → E)) (univ : Set (S → E))ᶜ) = fun _ ↦ 0 := by
      funext Λ'
      simp
    rw [hzero, limsup_const]
    exact hε.le

/-- Every Gibbs measure for `γ^Φ` is dominated by the free measures (Georgii (4.11)(1)). -/
lemma setOf_mem_GP_subset_dominatedBy :
    {μ : WithLocalConvergence S E |
        μ.toMeasure ∈ GP (S := S) (E := E) (gibbsSpecificationOfAbsolutelySummable
          (Φ := Φ) ν β)}
      ⊆ dominatedBy S E (dominatingMeasure Φ ν β) := by
  intro μ hμ Λ A hA
  exact apply_le_of_mem_GP hμ Λ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA)
    fun ω ↦ gibbsSpecification_apply_le_dominatingMeasure ν β Λ ω hA

variable [StandardBorelSpace E]

/-- **Georgii Theorem (4.23)(a), existence.** Over a standard Borel state space, every absolutely
summable potential admits a Gibbs measure, obtained as a local thermodynamic limit. -/
theorem GP_gibbsSpecification_nonempty :
    (GP (S := S) (E := E)
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)).Nonempty := by
  have hE : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨η⟩ : Nonempty (S → E) := ⟨fun _ ↦ Classical.arbitrary E⟩
  obtain ⟨μ, hμ, -⟩ := exists_isLocalThermodynamicLimit_mem_GP
    (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) η
    (locallyEquicontinuous_finiteVolumeDistributions ν β η)
  exact ⟨μ, hμ⟩

/-- **Georgii Theorem (4.23)(a), compactness.** Over a standard Borel state space, the set of
Gibbs measures of an absolutely summable potential is compact in the topology of local
convergence. -/
theorem isCompact_setOf_mem_GP_gibbsSpecification :
    IsCompact {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E)
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)} :=
  (isCompact_dominatedBy (dominatingMeasure Φ ν β)).of_isClosed_subset
    (isClosed_setOf_mem_GP
      (isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β))
    (setOf_mem_GP_subset_dominatedBy ν β)

/-- **Georgii Theorem (4.23)(b).** For a family of absolutely summable potentials whose
interaction norms are uniformly bounded on each finite volume, the union of the corresponding
Gibbs-measure sets is relatively compact in the topology of local convergence. -/
theorem isCompact_closure_iUnion_setOf_mem_GP {ι : Type*} (Φs : ι → Potential S E)
    [∀ i, IsPotential (Φs i)] [∀ i, IsAbsolutelySummable (Φs i)]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    {B : Finset S → ℝ} (hB : ∀ i Λ, (Φs i).hamiltonianBound Λ ≤ B Λ) :
    IsCompact (closure (⋃ i, {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E)
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β)})) := by
  set νdom : Finset S → Measure (S → E) := fun Λ ↦
    ENNReal.ofReal (Real.exp (2 * |β| * B Λ)) • Measure.infinitePi (fun _ : S ↦ ν) with hνdom
  have hfin : ∀ Λ, IsFiniteMeasure (νdom Λ) := fun Λ ↦ ⟨by
    rw [hνdom, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top⟩
  refine IsCompact.of_isClosed_subset (isCompact_dominatedBy νdom) isClosed_closure ?_
  refine closure_minimal (Set.iUnion_subset fun i μ hμ ↦ ?_) (isClosed_dominatedBy νdom)
  intro Λ A hA
  refine apply_le_of_mem_GP hμ Λ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) fun ω ↦ ?_
  rw [hνdom]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β Λ ω A
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * (Φs i).hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A :=
      gibbsSpecificationOfAbsolutelySummable_apply_le (Φ := Φs i) ν β Λ ω hA
    _ ≤ ENNReal.ofReal (Real.exp (2 * |β| * B Λ)) * Measure.infinitePi (fun _ : S ↦ ν) A := by
      gcongr
      exact hB i Λ

/-- **Georgii Theorem (4.23)(b), literal per-site form.** If `M = (Φs i)` is bounded in `ℬ` in
Georgii's sense — `sup_{Φ ∈ M} ‖Φ‖_a < ∞` for every site `a` — then `⋃ 𝒢(Φs i)` is relatively
compact in the topology of local convergence. -/
theorem isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top {ι : Type*}
    (Φs : ι → Potential S E)
    [∀ i, IsPotential (Φs i)] [∀ i, IsAbsolutelySummable (Φs i)]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (hb : ∀ a : S, (⨆ i, (Φs i).normAt a) < ⊤) :
    IsCompact (closure (⋃ i, {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E)
        (gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β)})) := by
  refine isCompact_closure_iUnion_setOf_mem_GP Φs ν β
    (B := fun Λ ↦ (∑ a ∈ Λ, ⨆ j, (Φs j).normAt a).toReal) fun i Λ ↦ ?_
  have hne : (∑ a ∈ Λ, ⨆ j, (Φs j).normAt a) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun a _ ↦ hb a).ne
  exact ENNReal.toReal_mono hne
    (Finset.sum_le_sum fun a _ ↦ le_iSup (fun j ↦ (Φs j).normAt a) i)

/-- Georgii's density estimate in the proof of (4.13): if `|H_Λ^Φ| ≤ c` on the confinement box
`K^Δ × E^{S∖Δ}`, then on the box the normalized Boltzmann density is at most
`e^{|β|c} / (e^{-|β|c} ν(K)^{|Λ|})`. -/
lemma premodifierNorm_le_of_abs_hamiltonian_le
    {S E : Type*} [MeasurableSpace E] (Φ : Potential S E)
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) {Kset : Set E} (hKset : MeasurableSet Kset)
    {c : ℝ} (hH : ∀ x ∈ {x : S → E | ∀ i ∈ Δ, x i ∈ Kset}, |Φ.hamiltonian Λ x| ≤ c)
    {ω : S → E} (hω : ω ∈ {x : S → E | ∀ i ∈ Δ, x i ∈ Kset}) :
    Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω
      ≤ ENNReal.ofReal (Real.exp (|β| * c))
        / (ENNReal.ofReal (Real.exp (-(|β| * c))) * ν Kset ^ Λ.card) := by
  classical
  set B : Set (S → E) := {x | ∀ i ∈ Δ, x i ∈ Kset} with hB
  -- bound for the numerator on `B`
  have hnum : Φ.boltzmannFactor β Λ ω ≤ ENNReal.ofReal (Real.exp (|β| * c)) := by
    rw [boltzmannFactor]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    calc -β * Φ.hamiltonian Λ ω ≤ |(-β) * Φ.hamiltonian Λ ω| := le_abs_self _
      _ = |β| * |Φ.hamiltonian Λ ω| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * c := mul_le_mul_of_nonneg_left (hH ω hω) (abs_nonneg β)
  -- pointwise lower bound for the Boltzmann factor on `B`
  have hlow : ∀ x ∈ B, ENNReal.ofReal (Real.exp (-(|β| * c))) ≤ Φ.boltzmannFactor β Λ x := by
    intro x hx
    rw [boltzmannFactor]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    calc -(|β| * c) ≤ -|(-β) * Φ.hamiltonian Λ x| := by
          rw [abs_mul, abs_neg]
          exact neg_le_neg (mul_le_mul_of_nonneg_left (hH x hx) (abs_nonneg β))
      _ ≤ -β * Φ.hamiltonian Λ x := neg_abs_le _
  -- decompose the box: `B = D ∩ Cout` with `D` inside `Λ` and `Cout` outside
  set D : Set (S → E) := {x | ∀ i ∈ Λ, x i ∈ Kset} with hD
  set Cout : Set (S → E) := {x | ∀ i ∈ Δ \ Λ, x i ∈ Kset} with hCout
  have hBDC : B = D ∩ Cout := by
    ext x
    constructor
    · exact fun hx ↦ ⟨fun i hi ↦ hx i (hΛΔ hi), fun i hi ↦ hx i (Finset.mem_sdiff.1 hi).1⟩
    · rintro ⟨hxD, hxC⟩ i hi
      by_cases hiΛ : i ∈ Λ
      · exact hxD i hiΛ
      · exact hxC i (Finset.mem_sdiff.2 ⟨hi, hiΛ⟩)
  have hDmeas : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] D := by
    have h : D = ⋂ i ∈ Λ, (fun x : S → E ↦ x i) ⁻¹' Kset := by ext x; simp [hD]
    rw [h]
    exact MeasurableSet.biInter Λ.countable_toSet fun i hi ↦
      measurable_cylinderEvent_apply (by simpa using hi) hKset
  have hDfull : MeasurableSet D := cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hDmeas
  have hCoutmeas : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Cout := by
    have h : Cout = ⋂ i ∈ Δ \ Λ, (fun x : S → E ↦ x i) ⁻¹' Kset := by ext x; simp [hCout]
    rw [h]
    exact MeasurableSet.biInter (Δ \ Λ).countable_toSet fun i hi ↦
      measurable_cylinderEvent_apply (by simpa using (Finset.mem_sdiff.1 hi).2) hKset
  -- the free measure of the inner box
  have hDval : Measure.infinitePi (fun _ : S ↦ ν) D = ν Kset ^ Λ.card := by
    have h : D = Set.pi (↑Λ : Set S) (fun _ ↦ Kset) := by
      ext x; simp [hD, Set.mem_pi]
    rw [h, Measure.infinitePi_pi (μ := fun _ : S ↦ ν) fun i _ ↦ hKset,
      Finset.prod_const]
  -- properness: for `ω ∈ B`, the kernel gives the box the mass of the inner box
  have hωCout : ω ∈ Cout := fun i hi ↦ hω i (Finset.mem_sdiff.1 hi).1
  have hkernel : Specification.isssd (S := S) (E := E) ν Λ ω B = ν Kset ^ Λ.card := by
    rw [hBDC, ((Specification.isssd (S := S) (E := E) ν).isProper Λ).inter_eq_indicator_mul
      cylinderEvents_le_pi hDfull hCoutmeas ω,
      indicator_of_mem hωCout, Pi.one_apply, one_mul,
      Specification.isssd_apply_of_mem_cylinderEvents ν Λ ω hDmeas, hDval]
  -- lower bound for the partition function
  have hZ : ENNReal.ofReal (Real.exp (-(|β| * c))) * ν Kset ^ Λ.card
      ≤ Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω := by
    have hBfull : MeasurableSet B := by
      rw [hBDC]
      exact hDfull.inter (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hCoutmeas)
    calc ENNReal.ofReal (Real.exp (-(|β| * c))) * ν Kset ^ Λ.card
        = ENNReal.ofReal (Real.exp (-(|β| * c)))
            * Specification.isssd (S := S) (E := E) ν Λ ω B := by rw [hkernel]
      _ = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-(|β| * c)))
            ∂(Specification.isssd (S := S) (E := E) ν Λ ω) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in B, Φ.boltzmannFactor β Λ x
            ∂(Specification.isssd (S := S) (E := E) ν Λ ω) :=
          setLIntegral_mono' hBfull hlow
      _ ≤ ∫⁻ x, Φ.boltzmannFactor β Λ x
            ∂(Specification.isssd (S := S) (E := E) ν Λ ω) :=
          setLIntegral_le_lintegral _ _
      _ = Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω := rfl
  rw [Specification.premodifierNorm]
  exact ENNReal.div_le_div hnum hZ

/-- **Georgii Corollary (4.13).** If `0 < ν (K ℓ)`, the mass escaping `K ℓ` at each site
vanishes along the net, and the Hamiltonians are eventually bounded on each confinement box,
then the finite-volume Gibbs distributions of the potentials `Φᵃ` are locally
equicontinuous. -/
theorem locallyEquicontinuous_of_confinement_hamiltonian
    {S E : Type*} [Countable S] [MeasurableSpace E] {ι : Type*} {l : Filter ι}
    (Φs : ι → Potential S E) [∀ a, IsPotential (Φs a)] [∀ a, IsAbsolutelySummable (Φs a)]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (Λs : ι → Finset S) (hΛs : Tendsto Λs l atTop)
    (νs μs : ι → ProbabilityMeasure (S → E))
    (hμs : ∀ a, μs a
      = (gibbsSpecificationOfAbsolutelySummable (Φ := Φs a) ν β).bindPM (Λs a) (νs a))
    (K : ℕ → Set E) (hK : ∀ ℓ, MeasurableSet (K ℓ))
    (hKpos : ∀ ℓ, 0 < ν (K ℓ))
    (hii : ∀ i : S, Tendsto
      (fun ℓ ↦ limsup (fun a ↦ (μs a : Measure (S → E)) {ω | ω i ∉ K ℓ}) l) atTop (𝓝 0))
    (hiii : ∀ Λ : Finset S, ∃ Δ : Finset S, Λ ⊆ Δ ∧ ∀ ℓ : ℕ, ∃ c : ℝ,
      ∀ᶠ a in l, ∀ ω ∈ {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ},
        |(Φs a).hamiltonian Λ ω| ≤ c) :
    LocallyEquicontinuous l μs := by
  refine locallyEquicontinuous_of_confinement ν
    (fun a ↦ Specification.premodifierNorm (S := S) (E := E) ν ((Φs a).boltzmannFactor β))
    (fun a ↦ Specification.IsPremodifier.isModifier_premodifierNorm (ν := ν)
      (isPremodifier_boltzmannFactor (Φ := Φs a) β)
      (isPremodifierAdmissible_boltzmannFactor (Φ := Φs a) ν β))
    Λs hΛs νs μs (fun a ↦ (hμs a).trans rfl) K hK hii ?_
  intro Λ
  obtain ⟨Δ, hΛΔ, hΔ⟩ := hiii Λ
  refine ⟨Δ, hΛΔ, fun ℓ ↦ ?_⟩
  obtain ⟨c, hc⟩ := hΔ ℓ
  refine ⟨ENNReal.ofReal (Real.exp (|β| * c))
      / (ENNReal.ofReal (Real.exp (-(|β| * c))) * ν (K ℓ) ^ Λ.card), ?_, ?_⟩
  · exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
        (pow_ne_zero _ (hKpos ℓ).ne'))
  · filter_upwards [hc] with a ha
    intro ω hω
    exact premodifierNorm_le_of_abs_hamiltonian_le (Φs a) ν β hΛΔ (hK ℓ) ha hω

end Potential

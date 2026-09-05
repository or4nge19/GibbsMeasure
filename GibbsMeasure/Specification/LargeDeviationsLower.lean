/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.BlockMcMillan
public import GibbsMeasure.Specification.LargeDeviations

/-!
# Inputs to Georgii's large deviation bounds (15.46), (15.47)

This file collects the finite-volume and topological inputs of Georgii's proofs of the two
inequalities of Theorem (15.45): the upper bound (15.46) and the lower bound (15.47).

## Main results

### A neighbourhood basis for the topology of local convergence

* `MeasureTheory.GibbsMeasure.exists_finset_localEvents_icc_subset_of_isOpen`, **Georgii (4.2)**:
  every open set of the topology of local convergence containing `μ` contains a finite
  intersection of local windows `{ν : ν(A) ∈ [μ(A) − ε, μ(A) + ε]}`, `A` a local event. The
  topology is by construction the initial topology of the evaluations at the local events
  (`WithSetwiseTopology.isInducing_evalProb`), and the library has no `HasBasis` lemma for it.

### Georgii (15.44) for an arbitrary open set

* `MeasureTheory.GibbsMeasure.periodicEmpiricalFieldL`: `°R^ω_Δ` read in the space of random
  fields with the topology of local convergence.
* `MeasureTheory.GibbsMeasure.tendsto_measure_setOf_periodicEmpiricalField_mem_isOpen`: for an
  ergodic `μ ∈ 𝓟_Θ` and an *open* `U ∋ μ`, `μ(°R_{Λ_n} ∈ U) → 1`. Georgii states (15.44) for the
  basic neighbourhoods only
  (`tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt`); this is the same for every
  open set, obtained from the neighbourhood basis above with the indicators of the local events
  as test observables. It is the first of the three ingredients that make Georgii's event `A_Λ`
  typical in the proof of (15.47).

### The finite-volume Gibbs distribution on a local event

* `MeasureTheory.GibbsMeasure.le_gibbsSpecificationOfAbsolutelySummable_apply`, the first
  inequality of the proof of (15.47): for a `𝓕_Λ`-event `A` on which the Hamiltonian is at most
  `b`, `γ^Φ_Λ(A | ω) ≥ e^{−b − log Z_Λ(ω)} λ^S(A)`. The `𝓕_Λ`-measurability is what turns the
  free part of the Gibbs kernel into the a priori product measure
  (`Specification.isssd_apply_of_mem_cylinderEvents`), so no boundary condition survives on the
  right.

### The Hamiltonian and the periodic empirical field

* `abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le`
  (in `MeasureTheory.GibbsMeasure`):
  **Georgii's estimate (15.25) in the form both proofs use it**,
  `|H_Λ(y) − |Λ| ⟨°R^y_Λ, Φ⟩| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`, uniformly in the configuration
  `y` — including the sites outside `Λ`, on which `H_Λ` does depend. By
  `Potential.tendsto_tail_div_card` the right-hand side is `o(|Λ|)` along boxes all of whose
  sides tend to infinity. This is the identity
  `|Δ|⁻¹ γ^C_{Δ|ω}(H^Φ_Δ) = ⟨γ^C_{Δ|ω} °R_Δ, Φ⟩ + o(1)` of Step 1 of the proof of (15.46), before
  integration, and the energy bound of the event `A_Λ` in the proof of (15.47).

## Not proved here

Theorem (15.45) itself — the two inequalities (15.46) and (15.47) — is **not** proved. What is
missing, precisely:

* For **(15.47)**: the McMillan input is complete and unconditional
  (`GibbsMeasure/Specification/BlockMcMillan.lean`), as are the three items above. What is not
  formalised is the assembly, and one combinatorial ingredient it needs: for an *arbitrary* cube
  `Λ`, the volume `Δ ⊇ Λ` made of the tiles of `Λ(m)` that meet `Λ` has `|Δ| / |Λ| → 1`, and its
  tile-index set is a box of `p ℤ^d`; only the *centred* instance of this is proved
  (`tileIdxImage_cubeUnion`, `tendsto_card_vadd_tileIdxImage_symmDiff_div_card`).
* For **(15.46)**: Step 2 forms the randomly shifted independent-block measure `γ̄^C_{Λ|ω}` whose
  *tile is the volume `Λ` itself*. The tiling API of this library
  (`isComplement_piFinset_Icc`, `specificEntropy_tileAverage`) is available only for the centred
  cubes `Λ(n) = [−n, n]^d` of odd side, so Proposition (15.52) is not yet available for the
  arbitrary cubes over which (15.46) takes its limit superior. Step 3 is available
  (`GibbsMeasure/Specification/InvariantFieldsBarycenter.lean`) but needs a **finite** state
  space, so (15.46) and hence (15.45) cannot be obtained at Georgii's standard Borel generality
  by that route; the lower bound (15.47), by contrast, needs no such restriction.
--/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Pointwise Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### A neighbourhood basis for the topology of local convergence -/

section LocalBasis

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (4.2): the basic neighbourhoods of the topology of local convergence.** Every open
set containing `μ` contains a finite intersection of local windows
`{ν : ν(A) ∈ [μ(A) − ε, μ(A) + ε]}`, `A` ranging over finitely many local events. The topology is
by construction the initial topology of the evaluations `ν ↦ ν(A)` at the local events
(`WithSetwiseTopology.isInducing_evalProb`), so this is `isOpen_pi_iff` together with the
`ℝ≥0∞` neighbourhood basis `Icc (x − ε) (x + ε)`. -/
theorem exists_finset_localEvents_icc_subset_of_isOpen
    {U : Set (WithLocalConvergence S E)} (hU : IsOpen U) {μ : WithLocalConvergence S E}
    (hμ : μ ∈ U) :
    ∃ (T : Finset (localEvents S E)) (ε : ℝ≥0∞), 0 < ε ∧ ε ≤ 1 ∧
      ∀ ν : WithLocalConvergence S E,
        (∀ A ∈ T, (ν.toMeasure : Measure (S → E)) (A : Set (S → E)) ∈
          Set.Icc ((μ.toMeasure : Measure (S → E)) (A : Set (S → E)) - ε)
            ((μ.toMeasure : Measure (S → E)) (A : Set (S → E)) + ε)) → ν ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := (WithSetwiseTopology.isInducing_evalProb (Ω := S → E)
    (𝒞 := localEvents S E)).isOpen_iff.1 hU
  have hμW : WithSetwiseTopology.evalProb (localEvents S E) μ ∈ W := by
    rw [← Set.mem_preimage, hWU]; exact hμ
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hW _ hμW
  -- a window inside each factor
  have hchoice : ∀ A : localEvents S E, ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ ≤ 1 ∧ (A ∈ I →
      Set.Icc ((μ.toMeasure : Measure (S → E)) (A : Set (S → E)) - δ)
        ((μ.toMeasure : Measure (S → E)) (A : Set (S → E)) + δ) ⊆ u A) := by
    intro A
    by_cases hA : A ∈ I
    · obtain ⟨δ, hδ0, hδ⟩ := ((ENNReal.hasBasis_nhds_of_ne_top' (x :=
        (μ.toMeasure : Measure (S → E)) (A : Set (S → E))) (measure_ne_top _ _)).mem_iff).1
          ((hu A hA).1.mem_nhds (hu A hA).2)
      refine ⟨min δ 1, (lt_min (pos_iff_ne_zero.2 hδ0) one_pos).ne', min_le_right _ _,
        fun _ x hx ↦ hδ ⟨le_trans (tsub_le_tsub_left (min_le_left δ 1) _) hx.1,
          hx.2.trans (by gcongr; exact min_le_left δ 1)⟩⟩
    · exact ⟨1, one_ne_zero, le_rfl, fun h ↦ absurd h hA⟩
  choose δ hδ0 hδ1 hδsub using hchoice
  -- a single window that works for all the finitely many factors
  have key : ∀ J : Finset (localEvents S E),
      ∃ ε : ℝ≥0∞, 0 < ε ∧ ε ≤ 1 ∧ ∀ A ∈ J, ε ≤ δ A := by
    intro J
    induction J using Finset.induction_on with
    | empty => exact ⟨1, one_pos, le_rfl, by simp⟩
    | insert A J _ ih =>
      obtain ⟨ε, hε0, hε1, hεle⟩ := ih
      refine ⟨min ε (δ A), lt_min hε0 (pos_iff_ne_zero.2 (hδ0 A)),
        (min_le_left _ _).trans hε1, fun B hB ↦ ?_⟩
      rcases Finset.mem_insert.1 hB with rfl | hB
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hεle B hB)
  obtain ⟨ε, hε0, hε1, hεle⟩ := key I
  refine ⟨I, ε, hε0, hε1, fun ν hν ↦ ?_⟩
  rw [← hWU, Set.mem_preimage]
  refine hsub fun A hA ↦ ?_
  refine hδsub A hA ⟨?_, ?_⟩
  · exact le_trans (tsub_le_tsub_left (hεle A hA) _) (hν A hA).1
  · exact (hν A hA).2.trans (by gcongr; exact hεle A hA)

end LocalBasis

/-! ### Georgii (15.44) for an arbitrary open set -/

section ErgodicOpen

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S]

/-- The periodic empirical field `°R^ω_Δ` read in the space of random fields with the topology of
local convergence. -/
def periodicEmpiricalFieldL (π : S → S) {Δ : Finset S} (hΔ : Δ.Nonempty) (ω : S → E) :
    WithLocalConvergence S E :=
  haveI : NeZero (#Δ) := ⟨hΔ.card_pos.ne'⟩
  WithSetwiseTopology.ofMeasure ⟨periodicEmpiricalField E π Δ ω, inferInstance⟩

@[simp] lemma toMeasure_periodicEmpiricalFieldL (π : S → S) {Δ : Finset S} (hΔ : Δ.Nonempty)
    (ω : S → E) :
    (((periodicEmpiricalFieldL π hΔ ω).toMeasure : ProbabilityMeasure (S → E)) :
      Measure (S → E)) = periodicEmpiricalField E π Δ ω := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ((ι → ℤ) → E)}

open scoped Classical in
/-- **Georgii (15.44) for an arbitrary open set.** For an ergodic shift-invariant random field
`μ` and an *open* set `U` of the topology of local convergence containing `μ`, the periodic
empirical fields eventually lie in `U` with probability tending to one:
`μ(°R_{Λ_n} ∈ U) → 1`. Georgii states (15.44) for the basic neighbourhoods
(`tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt`); this is the same statement
for every open set, obtained from the neighbourhood basis
`exists_finset_localEvents_icc_subset_of_isOpen` with the indicator functions of the local events
as the test observables. -/
theorem tendsto_measure_setOf_periodicEmpiricalField_mem_isOpen
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hmono : Monotone fun n ↦ Finset.Icc (m n) fun k ↦ m n k + s n)
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {U : Set (WithLocalConvergence (ι → ℤ) E)} (hU : IsOpen U)
    (hmemU : (WithSetwiseTopology.ofMeasure ⟨μ, hμ.1⟩ : WithLocalConvergence (ι → ℤ) E) ∈ U) :
    Tendsto (fun n ↦ μ {ω | periodicEmpiricalFieldL (π n) (hne n) ω ∈ U}) atTop (𝓝 1) := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  obtain ⟨T, ε, hε0, hε1, hTU⟩ := exists_finset_localEvents_icc_subset_of_isOpen hU hmemU
  have hεtop : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε1
  have hεR : 0 < ε.toReal := ENNReal.toReal_pos hε0.ne' hεtop
  -- the local events of `T`, with their volumes
  have hvol : ∀ A : T, ∃ Λ : Finset (ι → ℤ),
      MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Λ : Set (ι → ℤ))]
        ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E)) := fun A ↦
    mem_localEvents_iff_cylinderEvents.1 (A : localEvents (ι → ℤ) E).2
  choose Λ hΛ using hvol
  set f : T → ((ι → ℤ) → E) → ℝ := fun A ↦
    Set.indicator ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E)) 1 with hfdef
  have hAmeas : ∀ A : T, MeasurableSet ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E)) :=
    fun A ↦ cylinderEvents_le_pi _ (hΛ A)
  have hdep : ∀ A : T, DependsOn (f A) ((Λ A : Finset (ι → ℤ)) : Set (ι → ℤ)) := by
    intro A x y hxy
    have h := mem_congr_of_measurableSet_cylinderEvents (hΛ A) hxy
    simp only [hfdef, Set.indicator_apply, Pi.one_apply]
    by_cases hx : x ∈ ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E))
    · simp [hx, h.1 hx]
    · have hy : y ∉ ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E)) := fun hy ↦ hx (h.2 hy)
      simp [hx, hy]
  have hfm : ∀ A : T, StronglyMeasurable (f A) := fun A ↦
    (stronglyMeasurable_const (α := (ι → ℤ) → E) (b := (1 : ℝ))).indicator (hAmeas A)
  have hc : ∀ (A : T) (η : (ι → ℤ) → E), |f A η| ≤ 1 := by
    intro A η
    by_cases h : η ∈ ((A : localEvents (ι → ℤ) E) : Set ((ι → ℤ) → E)) <;>
      simp [hfdef, h]
  have hlim := tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt
    (μ := μ) hμ htriv hmono hs hπ (κ := T) (B := Λ) (f := f) hdep hfm (c := fun _ ↦ (1 : ℝ)) hc
    hεR
  -- the basic window is contained in the event that `°R_Λ ∈ U`
  have hsub : ∀ n : ℕ, {ω | ∀ A : T, |(∫ η, f A η ∂(periodicEmpiricalField E (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) - ∫ η, f A η ∂μ| < ε.toReal}
      ⊆ {ω | periodicEmpiricalFieldL (π n) (hne n) ω ∈ U} := by
    intro n ω hω
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))) := ⟨(hne n).card_pos.ne'⟩
    refine hTU _ fun A hA ↦ ?_
    have hωA := hω ⟨A, hA⟩
    rw [integral_indicator_one (hAmeas ⟨A, hA⟩), integral_indicator_one (hAmeas ⟨A, hA⟩)] at hωA
    set x : ℝ := (periodicEmpiricalField E (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) ω).real (A : Set ((ι → ℤ) → E)) with hx
    set y : ℝ := μ.real (A : Set ((ι → ℤ) → E)) with hy
    have hxnn : 0 ≤ x := measureReal_nonneg
    have hynn : 0 ≤ y := measureReal_nonneg
    have hxE : (periodicEmpiricalField E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) ω)
        (A : Set ((ι → ℤ) → E)) = ENNReal.ofReal x := by
      rw [hx, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hyE : ((WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩ :
        WithLocalConvergence (ι → ℤ) E).toMeasure : Measure ((ι → ℤ) → E))
        (A : Set ((ι → ℤ) → E)) = ENNReal.ofReal y := by
      rw [hy, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      rfl
    obtain ⟨h1, h2⟩ := abs_lt.1 hωA
    rw [toMeasure_periodicEmpiricalFieldL, hxE, hyE]
    constructor
    · rw [← ENNReal.ofReal_toReal hεtop, ← ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← ENNReal.ofReal_toReal hεtop, ← ENNReal.ofReal_add hynn ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (.of_forall fun n ↦ measure_mono (hsub n)) (.of_forall fun _ ↦ prob_le_one)

end ErgodicOpen

/-! ### The finite-volume Gibbs distribution on a local event -/

section GibbsLower

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **The finite-volume Gibbs distribution of a local event is bounded below by the free measure**,
Georgii's first inequality in the proof of the lower bound (15.47):
`γ^Φ_Λ(A | ω) ≥ e^{−b − log Z_Λ(ω)} λ^S(A)` for a `𝓕_Λ`-event `A` on which the Hamiltonian is at
most `b`. -/
theorem le_gibbsSpecificationOfAbsolutelySummable_apply (Λ : Finset S) (ω : S → E)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    {b : ℝ} (hb : ∀ y ∈ A, Φ.hamiltonian Λ y ≤ b) :
    ENNReal.ofReal (Real.exp (-b - Φ.logZ ν Λ ω)) * (Measure.infinitePi fun _ : S ↦ ν) A
      ≤ Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1 Λ ω A := by
  set Z := Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω with hZdef
  have hZpos : 0 < Z := Potential.premodifierZ_boltzmannFactor_pos ν 1 Λ ω
  have hZtop : Z ≠ ⊤ := Potential.premodifierZ_boltzmannFactor_ne_top ν 1 Λ ω
  have hZR : 0 < Z.toReal := ENNReal.toReal_pos hZpos.ne' hZtop
  rw [Potential.gibbsSpecificationOfAbsolutelySummable, Specification.modification_apply,
    Specification.withDensity_premodifierNorm_apply ν
      (Potential.isPremodifier_boltzmannFactor (Φ := Φ) 1) (cylinderEvents_le_pi _ hA) ω]
  -- the Boltzmann factor is at least `e^{-b}` on `A`
  have hint : ENNReal.ofReal (Real.exp (-b)) * (Measure.infinitePi fun _ : S ↦ ν) A
      ≤ ∫⁻ y in A, Φ.boltzmannFactor 1 Λ y ∂(Specification.isssd (S := S) (E := E) ν Λ ω) := by
    rw [← Specification.isssd_apply_of_mem_cylinderEvents ν Λ ω hA, ← setLIntegral_const]
    refine setLIntegral_mono' (cylinderEvents_le_pi _ hA) fun y hy ↦ ?_
    rw [Potential.boltzmannFactor]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by have := hb y hy; linarith))
  have hexp : Real.exp (-b - Φ.logZ ν Λ ω) = (Z.toReal)⁻¹ * Real.exp (-b) := by
    have hlog : Φ.logZ ν Λ ω = Real.log Z.toReal := rfl
    rw [hlog, sub_eq_neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hZR]
  have hfac : ENNReal.ofReal (Real.exp (-b - Φ.logZ ν Λ ω))
      = Z⁻¹ * ENNReal.ofReal (Real.exp (-b)) := by
    rw [hexp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hZR,
      ENNReal.ofReal_toReal hZtop]
  calc ENNReal.ofReal (Real.exp (-b - Φ.logZ ν Λ ω)) * (Measure.infinitePi fun _ : S ↦ ν) A
      = Z⁻¹ * (ENNReal.ofReal (Real.exp (-b)) * (Measure.infinitePi fun _ : S ↦ ν) A) := by
        rw [hfac, mul_assoc]
    _ ≤ Z⁻¹ * ∫⁻ y in A, Φ.boltzmannFactor 1 Λ y
          ∂(Specification.isssd (S := S) (E := E) ν Λ ω) := by gcongr

end GibbsLower

/-! ### The Hamiltonian and the periodic empirical field -/

section Energy

variable {S E : Type*} [Countable S] [DecidableEq S] [AddCommGroup S] [MeasurableSpace E]
  {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]

omit [DecidableEq S] in
/-- **Georgii's estimate (15.25) in the form Step 1 of (15.46) and the proof of (15.47) use it.**
For a torus reduction `π` of the box `Λ`, the Hamiltonian of *any* configuration `y` is the
specific energy of its periodic empirical field, up to the boundary term:
`|H_Λ(y) − |Λ| ⟨°R^y_Λ, Φ⟩| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`.
The bound is uniform in `y`, and `Potential.tendsto_tail_div_card` says it is `o(|Λ|)` along
boxes all of whose sides tend to infinity. The three terms are: Georgii (15.25) applied at the
periodic continuation `y^∘_Λ` (`Potential.abs_sum_energyDensity_shift_sub_hamiltonian_le`), and
the change of boundary condition from `y^∘_Λ` to `y`, which agree on `Λ`
(`Potential.abs_hamiltonian_sub_le_of_eqOn`). -/
theorem abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le
    (hΦ : Φ.IsShiftInvariant) {G : AddSubgroup S} {Λ : Finset S} {π : S → S}
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) (y : S → E) :
    |Φ.hamiltonian Λ y - (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ y)|
      ≤ 3 * Φ.tail Λ Λ := by
  classical
  have hcard : (0 : ℝ) < #Λ := by exact_mod_cast hΛ.card_pos
  set z : S → E := Potential.periodicExtend π y with hz
  -- `|Λ| ⟨°R^y_Λ, Φ⟩` is the spatial sum of the site energies of the periodic continuation
  have hsum : (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ y)
      = ∑ i ∈ Λ, Φ.energyDensity ((shift E (-i)).toFun z) := by
    rw [specificEnergy_periodicEmpiricalField hΦ π Λ y, ← mul_assoc,
      mul_inv_cancel₀ hcard.ne', one_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hΦ.siteEnergy_eq i z
  -- the two boundary estimates
  have h1 : |∑ i ∈ Λ, Φ.energyDensity ((shift E (-i)).toFun z) - Φ.hamiltonian Λ z|
      ≤ Φ.tail Λ Λ := Potential.abs_sum_energyDensity_shift_sub_hamiltonian_le hΦ Λ z
  have h2 : |Φ.hamiltonian Λ y - Φ.hamiltonian Λ z| ≤ 2 * Φ.tail Λ Λ :=
    Potential.abs_hamiltonian_sub_le_of_eqOn Λ fun i hi ↦ by
      simp only [hz, Potential.periodicExtend, hπ.eq_self i hi]
  rw [hsum]
  calc |Φ.hamiltonian Λ y - ∑ i ∈ Λ, Φ.energyDensity ((shift E (-i)).toFun z)|
      ≤ |Φ.hamiltonian Λ y - Φ.hamiltonian Λ z|
        + |Φ.hamiltonian Λ z - ∑ i ∈ Λ, Φ.energyDensity ((shift E (-i)).toFun z)| :=
        abs_sub_le _ _ _
    _ ≤ 2 * Φ.tail Λ Λ + Φ.tail Λ Λ := by
        refine add_le_add h2 ?_
        rw [abs_sub_comm]
        exact h1
    _ = 3 * Φ.tail Λ Λ := by ring

end Energy

end MeasureTheory.GibbsMeasure

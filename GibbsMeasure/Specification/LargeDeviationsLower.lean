/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import GibbsMeasure.Specification.BlockMcMillan
public import GibbsMeasure.Specification.LargeDeviations

/-!
# Georgii's large deviation lower bound (15.47), and the inputs of (15.46)

This file proves **the lower bound (15.47) of Georgii's Theorem (15.45)** — including its
"in particular" clause for the Gibbs measures — and collects the finite-volume and topological
inputs that the proof of the companion upper bound (15.46) shares with it.

Throughout, `S = ℤ^d` with `d ≥ 1` is spelled `Fin d → ℤ`, `λ` is an a priori *probability*
measure on an arbitrary measurable state space `E`, and `Φ` is a shift-invariant absolutely
summable potential, i.e. `Φ ∈ ℬ_Θ`. The volumes are Georgii's cubes: an arbitrary sequence
`Λ_n = ∏_k [m_n(k), m_n(k) + s_n]` with `s_n → ∞` — Georgii's `|Λ| → ∞`, with no monotonicity —
each equipped with an arbitrary torus reduction `π_n` (`Potential.IsTorusReduction`) so that the
periodic empirical field `°R_{Λ_n}` of Definition (15.41) is defined.

## Main results

All the names below live in the `MeasureTheory.GibbsMeasure` namespace.

### Georgii (15.47)

* `eventually_exists_ofReal_exp_le_gibbsSpecification`, **the estimate
  (15.55) that carries the lower bound**, in the form the two corollaries below consume: if
  `ν ∈ 𝓟_Θ` lies in Georgii's `C°` — the interior of `C` *in* `𝓟_Θ`, spelled
  `C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E] ν` — and `r < −𝒜(ν|Φ)`, then eventually there is a
  `𝓕_{Λ_n}`-measurable event `B ⊆ {°R_{Λ_n} ∈ C}` with `γ^Φ_{Λ_n}(B | ω) ≥ e^{|Λ_n| r}` for
  *every* boundary condition `ω`.
* `eventually_ofReal_exp_le_gibbsSpecification_setOf_periodicEmpiricalField_mem`,
  **Georgii (15.55)** as he states it, and
  `eventually_ofReal_exp_le_measure_setOf_periodicEmpiricalField_mem`,
  the same for a Gibbs measure `μ ∈ 𝒢(Φ)`, obtained by integrating the uniform bound over the
  boundary condition (this is why the measurable window `B` is exposed: the event
  `{°R_{Λ_n} ∈ C}` need not be measurable for an arbitrary `C`).
* `neg_iInf_specificRelativeEntropy_le_liminf_log_iInf_gibbsSpecification`,
  **(15.47)**:
  `liminf |Λ_n|⁻¹ log inf_ω γ^Φ_{Λ_n}(°R_{Λ_n} ∈ C | ω) ≥ − inf_{ν ∈ C°} 𝒜(ν|Φ)`, and
  `neg_iInf_specificRelativeEntropy_le_liminf_log_measure`, its
  **"in particular" clause**: the same with `γ^Φ_{Λ_n}(·|ω)` replaced by any `μ ∈ 𝒢(Φ)`.
  `invariantRandomFields` is `𝓟_Θ` read inside the space of random
  fields with the topology of local convergence, and
  `invariantInterior` is Georgii's `C°`.

The proof is Georgii's. Given `ν ∈ C°` with `𝒜(ν|Φ) < ∞` and `ε > 0`:

1. Proposition (15.52) supplies an *ergodic* `ν̃ = γ̃` in `C°` with `⟨ν̃, Φ⟩ < ⟨ν, Φ⟩ + ε`: the
   randomly shifted independent-block field (`tileAverage`) of the `Λ(i)`-marginal `γ` of `ν`,
   for a cube `Λ(i)` large enough. Its local convergence to `ν` is Theorem (14.12)
   (`tendsto_tileAverage`) and `⟨·, Φ⟩` is continuous
   (`Potential.continuous_specificEnergy`), so both requirements hold for large `i`. Georgii also
   asks for `𝒜(ν̃|Φ) < 𝒜(ν|Φ) + ε`; here nothing has to be said, because
   `𝓀(ν) ≤ |Λ(i)|⁻¹ 𝓗_{Λ(i)}(ν)` holds for *every* `i` — the specific entropy is an infimum over
   boxes (`specificEntropy_le_entropyIn_div_card`) — and `𝓀(ν̃) = |Λ(i)|⁻¹ 𝓗_{Λ(i)}(ν)`.
2. The event is Georgii's `A_Λ`: the window `W_n` of the *open* set
   `U ∩ {ρ : ⟨ρ, Φ⟩ < ⟨ν̃, Φ⟩ + ε}` given by (15.44)
   (`exists_measurableSet_subset_setOf_periodicEmpiricalField_mem`), intersected with the
   block-density event of the McMillan theorem for `γ̂`
   (`tendsto_tileProduct_setOf_blockDensity_le`).
   `U` is an open set with `U ∩ 𝓟_Θ ⊆ C`; since `°R^ω_{Λ_n} ∈ 𝓟_Θ` always, `W_n ⊆ {°R_{Λ_n} ∈ C}`.
3. The energy constraint turns into the Hamiltonian bound
   `H_{Λ_n} ≤ |Λ_n| (⟨ν̃, Φ⟩ + ε) + 3 ∑_{A ∩ Λ_n ≠ ∅, A ⊄ Λ_n} ‖Φ_A‖` on `W_n`
   (`abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le`), and then into the
   Gibbs lower bound `γ^Φ_{Λ_n}(W_n|ω) ≥ e^{−b − log Z_{Λ_n}(ω)} λ^S(W_n)`
   (`le_gibbsSpecificationOfAbsolutelySummable_apply`). The density event turns into
   `λ^S(W_n) ≥ e^{−c_n} γ̂(W_n ∩ D_n)` (`tileProduct_inter_le_mul_infinitePi`).
4. `γ̂(W_n ∩ D_n) ≥ 1/2` eventually: `γ̂(D_n) → 1` is the block McMillan theorem, and
   `γ̂(W_n) → 1` follows from `ν̃(W_n) → 1` because `γ̂(B) ≤ |Λ(i)| ν̃(B)`
   (`tileProduct_apply_le_card_mul_tileAverage_apply`) — this is how the shift structure of the
   average is used; the McMillan estimate itself is needed only for `γ̂`.
5. `|Λ_n|⁻¹ log Z_{Λ_n}(ω) → P(Φ)` uniformly in `ω` (via `logSupZ`, Georgii (15.31)) and
   `|Λ_n|⁻¹ c_n → |Λ(i)|⁻¹ 𝓗_{Λ(i)}(ν) + ε ≤ −𝓀(ν) + ε` finish the estimate.

Two remarks on the hypotheses.

* **No standard Borel hypothesis and no finiteness of `E` enters anywhere.** Georgii assumes
  `(E, ℰ)` standard Borel throughout §15.5, but that hypothesis is consumed only by the *upper*
  bound (15.46) — through the compactness of the level sets of `𝓀(·|Φ)` and through Step 3, the
  Choquet-theoretic passage from `cx̄ C` to `C̄`. The lower bound (15.47) needs neither: the
  McMillan input is the law of large numbers for an i.i.d. block field
  (`GibbsMeasure/Specification/BlockMcMillan.lean`), and everything else is finite-volume.
* Georgii's `C` is a subset of `𝓟_Θ` and his `C°` is the interior of `C` *in* `𝓟_Θ`. That is what
  is used here, not the interior in the ambient space of all random fields: only
  `U ∩ 𝓟_Θ ⊆ C` for an ambient open `U` is needed, since the periodic empirical fields are
  themselves shift invariant. The statement is therefore Georgii's, and is *stronger* than the
  ambient-interior version.

### A neighbourhood basis for the topology of local convergence

* `exists_finset_localEvents_icc_subset_of_isOpen`, **Georgii (4.2)**:
  every open set of the topology of local convergence containing `μ` contains a finite
  intersection of local windows `{ν : ν(A) ∈ [μ(A) − ε, μ(A) + ε]}`, `A` a local event. The
  topology is by construction the initial topology of the evaluations at the local events
  (`WithSetwiseTopology.isInducing_evalProb`), and the library has no `HasBasis` lemma for it.

### Georgii (15.44) for an arbitrary open set

* `periodicEmpiricalFieldL`: `°R^ω_Δ` read in the space of random
  fields with the topology of local convergence.
* `measurable_cylinderEvents_periodicExtend` and
  `measurable_cylinderEvents_integral_periodicEmpiricalField`:
  `°R^ω_Δ` depends on `ω` only through `ω_Δ`, so `ω ↦ °R^ω_Δ(f)` is `𝓕_Δ`-measurable.
* `exists_measurableSet_subset_setOf_periodicEmpiricalField_mem`: for
  an ergodic `μ ∈ 𝓟_Θ` and an *open* `U ∋ μ`, there are `𝓕_{Λ_n}`-measurable events
  `W_n ⊆ {°R_{Λ_n} ∈ U}` with `μ(W_n) → 1`; the `𝓕_{Λ_n}`-measurability is what lets `W_n` be fed
  to the Gibbs kernel of `Λ_n`.
  `tendsto_measure_setOf_periodicEmpiricalField_mem_isOpen` is the
  plain statement `μ(°R_{Λ_n} ∈ U) → 1`. Georgii states (15.44) for the basic neighbourhoods only
  (`tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt`); this is the same for every
  open set, obtained from the neighbourhood basis above with the indicators of the local events
  as test observables.

### The finite-volume Gibbs distribution on a local event

* `le_gibbsSpecificationOfAbsolutelySummable_apply`, the first
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

## The companion upper bound

The **upper bound (15.46)** is `limsup_log_iSup_gibbsSpecification_div_card_le` of
`GibbsMeasure/Specification/LargeDeviationsUpper.lean`, which imports this file. It is proved
over a **finite** state space: Step 2's cluster point extraction and Step 3 (the passage from
`cx̄ C` to `C̄`, which is `iInf_closedConvexHull_eq_iInf_closure_ereal` of
`GibbsMeasure/Specification/InvariantFieldsBarycenter.lean`, from the concavity of `𝓀(·|Φ)`)
both use the compactness of the space of random fields in the topology of local convergence, and
the event property of `{°R_Λ ∈ C}`. Georgii's standard Borel generality would need instead his
countable core of `𝓕` and the compact metrizable `𝒞`-topology, which this library does not have.
Proposition (15.52) is *not* an obstruction: `specificEntropy_tileAverage_Icc` of
`GibbsMeasure/Specification/BlockEntropy.lean` covers an arbitrary box, which is what Step 2 needs
for the cubes over which (15.46) takes its limit superior.

The lower bound below carries no such restriction: it holds over an arbitrary measurable state
space, and — since (15.44) is convergence in probability, hence a consequence of the *mean*
ergodic theorem (14.A5) — along an arbitrary sequence of cubes with `s_n → ∞`.
--/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function InformationTheory MeasureTheory ProbabilityTheory Set Topology
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

/-- **The periodic continuation is a `𝓕_Δ`-measurable function of the configuration**: `ω^∘_Δ`
reads `ω` only at the sites `π i`, all of which lie in `Δ`. -/
lemma measurable_cylinderEvents_periodicExtend {G : AddSubgroup S} {Δ : Finset S} {π : S → S}
    (hπ : Potential.IsTorusReduction G Δ π) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
      fun ω : S → E ↦ Potential.periodicExtend π ω := by
  simp only [measurable_pi_iff]
  exact fun i ↦ measurable_cylinderEvent_apply (Finset.mem_coe.2 (hπ.mapsTo i))

/-- **`ω ↦ °R^ω_Δ(f)` is `𝓕_Δ`-measurable.** The periodic empirical field is a spatial average of
observables of the periodic continuation `ω^∘_Δ`, which depends on `ω` only through `ω_Δ`. -/
lemma measurable_cylinderEvents_integral_periodicEmpiricalField {G : AddSubgroup S}
    {Δ : Finset S} {π : S → S} (hπ : Potential.IsTorusReduction G Δ π)
    {f : (S → E) → ℝ} (hf : StronglyMeasurable f) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
      fun ω : S → E ↦ ∫ η, f η ∂(periodicEmpiricalField E π Δ ω) := by
  have hrw : (fun ω : S → E ↦ ∫ η, f η ∂(periodicEmpiricalField E π Δ ω))
      = fun ω ↦ (#Δ : ℝ)⁻¹ * ∑ i ∈ Δ, f ((shift E (-i)).toFun (Potential.periodicExtend π ω)) :=
    funext fun ω ↦ integral_periodicEmpiricalField _ _ _ hf
  rw [hrw]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ ↦
    ((hf.measurable.comp (shift E (-i)).measurable_toFun).comp
      (measurable_cylinderEvents_periodicExtend hπ)))

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure ((ι → ℤ) → E)}

open scoped Classical in
/-- **Georgii (15.44) for an arbitrary open set, with a `𝓕_{Λ_n}`-measurable window.** For an
ergodic shift-invariant random field `μ` and an *open* set `U` of the topology of local
convergence containing `μ`, there are events `W_n ⊆ {ω : °R^ω_{Λ_n} ∈ U}`, measurable for the
cylinder σ-algebra `𝓕_{Λ_n}` of the volume itself, with `μ(W_n) → 1`.

Georgii states (15.44) for the basic neighbourhoods
(`tendsto_measure_setOf_abs_integral_periodicEmpiricalField_sub_lt`); `W_n` *is* Georgii's basic
window `{ω : |°R^ω_{Λ_n}(A) − μ(A)| < ε for the finitely many local events A}` of (4.2), obtained
from the neighbourhood basis `exists_finset_localEvents_icc_subset_of_isOpen` with the indicator
functions of the local events as the test observables. It is `𝓕_{Λ_n}`-measurable because
`°R^ω_{Λ_n}` depends on `ω` only through `ω_{Λ_n}`
(`measurable_cylinderEvents_integral_periodicEmpiricalField`), and that is what the proof of the
large deviation lower bound (15.47) needs: the event it feeds to the Gibbs kernel of the volume
`Λ_n` must be an event of that volume. -/
theorem exists_measurableSet_subset_setOf_periodicEmpiricalField_mem
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {U : Set (WithLocalConvergence (ι → ℤ) E)} (hU : IsOpen U)
    (hmemU : (WithSetwiseTopology.ofMeasure ⟨μ, hμ.1⟩ : WithLocalConvergence (ι → ℤ) E) ∈ U) :
    ∃ W : ℕ → Set ((ι → ℤ) → E),
      (∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
          ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))] (W n)) ∧
      (∀ n, W n ⊆ {ω | periodicEmpiricalFieldL (π n) (hne n) ω ∈ U}) ∧
      Tendsto (fun n ↦ μ (W n)) atTop (𝓝 1) := by
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
    (μ := μ) hμ htriv hs hπ (κ := T) (B := Λ) (f := f) hdep hfm (c := fun _ ↦ (1 : ℝ)) hc
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
  refine ⟨_, fun n ↦ ?_, hsub, hlim⟩
  have hrw : {ω : (ι → ℤ) → E | ∀ A : T, |(∫ η, f A η ∂(periodicEmpiricalField E (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) - ∫ η, f A η ∂μ| < ε.toReal}
      = ⋂ A : T, (fun ω ↦ ∫ η, f A η ∂(periodicEmpiricalField E (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) ω)) ⁻¹'
            Set.Ioo ((∫ η, f A η ∂μ) - ε.toReal) ((∫ η, f A η ∂μ) + ε.toReal) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Ioo, abs_lt]
    exact forall_congr' fun A ↦
      ⟨fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩, fun h ↦ ⟨by linarith [h.1], by
        linarith [h.2]⟩⟩
  rw [hrw]
  exact MeasurableSet.iInter fun A ↦
    (measurable_cylinderEvents_integral_periodicEmpiricalField (hπ n) (hfm A)) measurableSet_Ioo

open scoped Classical in
/-- **Georgii (15.44) for an arbitrary open set.** For an ergodic shift-invariant random field
`μ` and an *open* set `U` of the topology of local convergence containing `μ`, the periodic
empirical fields eventually lie in `U` with probability tending to one:
`μ(°R_{Λ_n} ∈ U) → 1`. -/
theorem tendsto_measure_setOf_periodicEmpiricalField_mem_isOpen
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (htriv : ∀ A, MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A → μ A = 0 ∨ μ A = 1)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {U : Set (WithLocalConvergence (ι → ℤ) E)} (hU : IsOpen U)
    (hmemU : (WithSetwiseTopology.ofMeasure ⟨μ, hμ.1⟩ : WithLocalConvergence (ι → ℤ) E) ∈ U) :
    Tendsto (fun n ↦ μ {ω | periodicEmpiricalFieldL (π n) (hne n) ω ∈ U}) atTop (𝓝 1) := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  obtain ⟨W, -, hWsub, hWlim⟩ := exists_measurableSet_subset_setOf_periodicEmpiricalField_mem
    hμ htriv hs hπ hne hU hmemU
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hWlim tendsto_const_nhds
    (.of_forall fun n ↦ measure_mono (hWsub n)) (.of_forall fun _ ↦ prob_le_one)

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


/-! ### Georgii (15.55): the large deviation lower bound at one random field -/

section LowerBound

section Ambient

variable (S E : Type*) [MeasurableSpace E] [AddCommGroup S]

/-- **Georgii's `𝓟_Θ(Ω, 𝓕)`** read inside the space of random fields with the topology of local
convergence: the shift-invariant random fields. Georgii's set `C` of Theorem (15.45) is a subset
of `𝓟_Θ` and his `C°` is the interior of `C` *in* `𝓟_Θ`; the hypothesis
`C ∈ 𝓝[invariantRandomFields S E] ν` of (15.55) below says exactly that `ν ∈ C°`. -/
abbrev invariantRandomFields : Set (WithLocalConvergence S E) :=
  {ρ | (ρ.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)}

end Ambient

/-- If `μ(W_n) → 1` then eventually `μ(W_nᶜ) ≤ c`, for any `0 < c ≤ 1`. -/
private lemma eventually_measure_compl_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {W : ℕ → Set α} (hW : ∀ n, MeasurableSet (W n))
    (h : Tendsto (fun n ↦ μ (W n)) atTop (𝓝 1)) {c : ℝ≥0∞} (hc : c ≠ 0) (hc1 : c ≤ 1) :
    ∀ᶠ n in atTop, μ (W n)ᶜ ≤ c := by
  have hlt : (1 : ℝ≥0∞) - c < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hc
  filter_upwards [h.eventually (Ici_mem_nhds hlt)] with n hn
  rw [prob_compl_eq_one_sub (hW n)]
  exact (tsub_le_tsub_left hn 1).trans_eq (ENNReal.sub_sub_cancel ENNReal.one_ne_top hc1)

private lemma mul_inv_four_mul (x : ℝ) (hx : x ≠ 0) : x * (1 / (4 * x)) = 1 / 4 := by
  field_simp

private lemma add_mul_div_self (k Q e : ℝ) (hQ : Q ≠ 0) : (k + Q * e) / Q = k / Q + e := by
  field_simp

private lemma mul_div_mul_add_div (a c Q k e : ℝ) (hQ : Q ≠ 0) (hc : c ≠ 0) :
    a * Q / c * (k / Q + e) = a * (k + Q * e) / c := by
  field_simp

private lemma neg_add_div_expand (c x t S k : ℝ) (hc : c ≠ 0) :
    -x - 3 * (t / c) - S / c + k = (-(c * x + 3 * t) - S + c * k) / c := by
  field_simp
  ring

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E]

open scoped Classical in
/-- **The window of Georgii's proof of (15.55), the common core of the two lower bounds.**

Let `ν ∈ 𝓟_Θ` have finite specific entropy and lie in Georgii's `C°` — the interior of `C` *in*
`𝓟_Θ`, spelled `C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E] ν` — and let `ε > 0`. Then, along any
sequence of cubes `Λ_n` of `ℤ^d` whose side tends to infinity, with arbitrary torus reductions
`π_n`, there is eventually an event `B` of the volume `Λ_n` itself, contained in `{°R_{Λ_n} ∈ C}`,
on which the specific energy of the periodic empirical field is below `⟨ν, Φ⟩ + ε`, and whose
a priori probability is at least `e^{|Λ_n| (𝓀(ν) − ε)}`.

This is Georgii's event `A_Λ` together with the estimate `λ^Λ(A_Λ) ≥ e^{−|Λ| (−𝓀(ν) + ε)}`
extracted from his proof; it does not depend on the boundary condition, and the two lower bounds
— for `γ^Φ_Λ(·|ω)` (`eventually_exists_ofReal_exp_le_gibbsSpecification`) and for the periodic
Gibbs distribution `°γ^Φ_Λ` — are obtained from it by bounding the Hamiltonian on `B`.

The proof is Georgii's and is sketched in the module documentation. `B` is his `A_Λ`: the
intersection of a basic window of the open set `U ∩ {⟨·, Φ⟩ < ⟨ν̃, Φ⟩ + ε/2}` around an ergodic
independent-block field `ν̃` close to `ν` (Proposition (15.52) and (15.44)) with the block-density
event of the McMillan theorem for the independent-block field `γ̂`; the density constraint bounds
`λ^S(B)` below by `e^{−c_n} γ̂(B)`, and `γ̂(B) ≥ 1/2` eventually. -/
theorem eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    {C : Set (WithLocalConvergence (Fin d → ℤ) E)}
    {ν : Measure ((Fin d → ℤ) → E)} (hν : ν ∈ invariantFields (shiftGroup (Fin d → ℤ) E))
    (hνC : C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E]
      (WithSetwiseTopology.ofMeasure ⟨ν, hν.1⟩ : WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    (hκ : specificEntropy lam ν ≠ ⊥) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ B : Set ((Fin d → ℤ) → E),
      MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] B ∧
      B ⊆ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} ∧
      (∀ y ∈ B, Φ.specificEnergy (periodicEmpiricalField E (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) y) < Φ.specificEnergy ν + ε) ∧
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ)
          * ((specificEntropy lam ν).toReal - ε)))
        ≤ (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) B := by
  classical
  have hprobν : IsProbabilityMeasure ν := hν.1
  -- ### Step 0. The specific entropy of `ν` is a finite number `-k₀`.
  have hκtop : specificEntropy lam ν ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (specificEntropy_nonpos lam (μ := ν))
  set k₀ : ℝ := -(specificEntropy lam ν).toReal with hk₀def
  have hκeq : specificEntropy lam ν = ((-k₀ : ℝ) : EReal) := by
    rw [hk₀def, neg_neg, EReal.coe_toReal hκtop hκ]
  have hk₀nn : 0 ≤ k₀ := by
    have h := specificEntropy_nonpos lam (μ := ν)
    rw [hκeq] at h
    have h' : (-k₀ : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  set ε' : ℝ := ε / 2 with hε'def
  have hε'pos : 0 < ε' := by rw [hε'def]; linarith
  -- ### Step 1. Georgii's `ν̃`: an ergodic independent-block field near `ν`.
  obtain ⟨U, hUopen, hUν, hUC⟩ := mem_nhdsWithin.1 hνC
  set ν' : ProbabilityMeasure ((Fin d → ℤ) → E) := ⟨ν, hprobν⟩ with hν'def
  have hconv : Tendsto (fun i ↦ (WithSetwiseTopology.ofMeasure
      (tileAveragePM (isComplement_piFinset_Icc (d := d) i) ν') :
        WithLocalConvergence (Fin d → ℤ) E)) atTop
      (𝓝 (WithSetwiseTopology.ofMeasure ν')) :=
    tendsto_tileAverage (isComplement_piFinset_Icc (d := d))
      tendsto_card_filter_sub_notMem_piFinset_Icc_div hν
  have henergy : Tendsto (fun i ↦ Φ.specificEnergy
      ((tileAveragePM (isComplement_piFinset_Icc (d := d) i) ν' :
        ProbabilityMeasure ((Fin d → ℤ) → E)) : Measure ((Fin d → ℤ) → E))) atTop
      (𝓝 (Φ.specificEnergy ν)) :=
    ((Potential.continuous_specificEnergy (Φ := Φ)).tendsto _).comp hconv
  obtain ⟨i, hiU, hie⟩ :=
    ((hconv.eventually (hUopen.mem_nhds hUν)).and
      (henergy.eventually (gt_mem_nhds (show Φ.specificEnergy ν < Φ.specificEnergy ν + ε' by
        linarith)))).exists
  -- ### Step 2. The block law on the tile `Λ(i)` and its relative entropy.
  set hCH := isComplement_piFinset_Icc (d := d) i with hCHdef
  set q : ℕ := (2 * i + 1) ^ d with hqdef
  have hqpos : 0 < q := by rw [hqdef]; positivity
  have hCtcard : #(Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i :
      Finset (Fin d → ℤ)) = q := card_piFinset_Icc i
  have hγprob : IsProbabilityMeasure ((ν : Measure ((Fin d → ℤ) → E)).map
      (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i :
        Finset (Fin d → ℤ)).restrict) :=
    Measure.isProbabilityMeasure_map (Finset.measurable_restrict _).aemeasurable
  set γb := (ν : Measure ((Fin d → ℤ) → E)).map
    (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i : Finset (Fin d → ℤ)).restrict
    with hγbdef
  set K : ℝ≥0∞ := klDiv γb (Measure.pi fun _ ↦ lam) with hKdef
  have hbox : (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i :
      Finset (Fin d → ℤ)).IsBox := by
    refine ⟨fun _ ↦ -(i : ℤ), fun _ ↦ (i : ℤ),
      fun _ ↦ show (-(i : ℤ)) ≤ (i : ℤ) by omega, ?_⟩
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_Icc, Pi.le_def]
    exact ⟨fun h ↦ ⟨fun k ↦ (h k).1, fun k ↦ (h k).2⟩, fun h k ↦ ⟨h.1 k, h.2 k⟩⟩
  have hKle : (K : EReal) ≤ ((k₀ * (q : ℝ) : ℝ) : EReal) := by
    have h := specificEntropy_le_entropyIn_div_card (lam := lam) (μ := ν) hbox
    have hent : entropyIn lam ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i :
        Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) ν = -(K : EReal) := by
      rw [entropyIn, relativeEntropyIn_coe_finset, Measure.infinitePi_map_restrict, hKdef, hγbdef]
    have hqE : ((q : ℕ) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_coe_eq_natCast]; exact EReal.coe_ne_top _
    rw [hκeq, hCtcard, hent, EReal.le_div_iff_mul_le (by exact_mod_cast hqpos) hqE] at h
    calc (K : EReal) ≤ -(((-k₀ : ℝ) : EReal) * ((q : ℕ) : EReal)) := EReal.le_neg.1 h
      _ = ((k₀ * (q : ℝ) : ℝ) : EReal) := by
          rw [← EReal.coe_coe_eq_natCast, ← EReal.coe_mul, ← EReal.coe_neg]
          congr 1
          ring
  have hKtop : K ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_ennreal_top, top_le_iff] at hKle
    exact EReal.coe_ne_top _ hKle
  have hKreal : K.toReal ≤ k₀ * q := by
    rw [← EReal.coe_ennreal_toReal hKtop] at hKle
    exact_mod_cast hKle
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 hKtop
  -- ### Step 3. The window `W_n` of the open set `U ∩ {⟨·, Φ⟩ < ⟨ν̃, Φ⟩ + ε'}`.
  set νt : Measure ((Fin d → ℤ) → E) := tileAverage hCH γb with hνtdef
  have hνtinv : νt ∈ invariantFields (shiftGroup (Fin d → ℤ) E) :=
    tileAverage_mem_invariantFields_shiftGroup hCH γb
  have hνtprob : IsProbabilityMeasure νt := hνtinv.1
  have hνttriv : ∀ B, MeasurableSet[invariantEvents (shiftGroup (Fin d → ℤ) E)] B →
      νt B = 0 ∨ νt B = 1 := tileAverage_mem_trivialOn_invariantEvents hCH γb
  set U' : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    U ∩ {ρ | Φ.specificEnergy (ρ.toMeasure : Measure ((Fin d → ℤ) → E))
      < Φ.specificEnergy νt + ε'} with hU'def
  have hU'open : IsOpen U' :=
    hUopen.inter (isOpen_lt (Potential.continuous_specificEnergy (Φ := Φ)) continuous_const)
  have hνte : Φ.specificEnergy νt < Φ.specificEnergy ν + ε' := hie
  have hU'mem : (WithSetwiseTopology.ofMeasure ⟨νt, hνtinv.1⟩ :
      WithLocalConvergence (Fin d → ℤ) E) ∈ U' :=
    ⟨hiU, show Φ.specificEnergy νt < Φ.specificEnergy νt + ε' by linarith⟩
  obtain ⟨W, hWmeas, hWsub, hWlim⟩ :=
    exists_measurableSet_subset_setOf_periodicEmpiricalField_mem hνtinv hνttriv hs hπ hne
      hU'open hU'mem
  have hWC : ∀ n, W n ⊆ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} := by
    intro n η hη
    refine hUC ⟨(hWsub n hη).1, ?_⟩
    change ((periodicEmpiricalFieldL (π n) (hne n) η).toMeasure : Measure ((Fin d → ℤ) → E))
      ∈ invariantFields (shiftGroup (Fin d → ℤ) E)
    rw [toMeasure_periodicEmpiricalFieldL]
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))) := ⟨(hne n).card_pos.ne'⟩
    exact periodicEmpiricalField_mem_invariantFields (hπ n) η
  have hWenergy : ∀ n, ∀ y ∈ W n, Φ.specificEnergy (periodicEmpiricalField E (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) y) < Φ.specificEnergy ν + ε := by
    intro n y hy
    have h1 : Φ.specificEnergy (periodicEmpiricalField E (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) y) < Φ.specificEnergy νt + ε' := by
      have := (hWsub n hy).2
      rwa [Set.mem_ofPred_eq, toMeasure_periodicEmpiricalFieldL] at this
    rw [hε'def] at *
    linarith
  -- ### Step 4. The volumes `Δ_n ⊇ Λ_n` made of tiles, and the block-density event.
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → Finset (Fin d → ℤ),
      ∀ n, Δ n = tileHull hCH (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : ℕ → ℝ,
      ∀ n, cc n = (#(tileIdxImage hCH (Δ n)) : ℝ) * (K.toReal + (q : ℝ) * ε') := ⟨_, fun _ ↦ rfl⟩
  have hΔtile : ∀ n, IsTileUnion hCH (Δ n) := fun n ↦ by
    rw [hΔ]; exact isTileUnion_tileHull hCH _
  have hΔsub : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) ⊆ Δ n := fun n ↦ by
    rw [hΔ]; exact subset_tileHull hCH _
  have hΔidx : ∀ n, tileIdxImage hCH (Δ n)
      = tileIdxImage hCH (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) := fun n ↦ by
    rw [hΔ, tileIdxImage_tileHull]
  have hΔcard : ∀ n, #(Δ n) = #(tileIdxImage hCH (Δ n)) * q := fun n ↦ by
    rw [card_of_isTileUnion hCH (hΔtile n), hCtcard]
  have hidxne : ∀ᶠ n in atTop, (tileIdxImage hCH (Δ n)).Nonempty :=
    .of_forall fun n ↦ by rw [hΔidx]; exact Finset.image_nonempty.2 (hne n)
  have hDlim : Tendsto (fun n ↦ tileProduct hCH γb
      {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}) atTop (𝓝 1) := by
    have h := tendsto_tileProduct_setOf_blockDensity_le hCH lam γb hac hint hidxne
      (fun h ↦ by
        refine (tendsto_card_vadd_tileIdxImage_Icc_symmDiff_div_card i m hs h).congr fun n ↦ ?_
        rw [hΔidx])
      (ε := (q : ℝ) * ε') (by positivity)
    refine h.congr fun n ↦ ?_
    rw [hcc, hKdef]
  -- ### Step 5. The good event has probability at least `1/2` eventually.
  have hWmeas' : ∀ n, MeasurableSet (W n) := fun n ↦ cylinderEvents_le_pi _ (hWmeas n)
  have hDmeas : ∀ n, MeasurableSet {ω : (Fin d → ℤ) → E |
      blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))} := fun n ↦
    (Finset.measurable_prod _ fun k _ ↦ (γb.measurable_rnDeriv _).comp
      ((measurable_pi_apply k).comp (tilingEquiv (E := E) hCH).symm.measurable))
      measurableSet_Iic
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqpos
  have hhalf : ∀ᶠ n in atTop, ENNReal.ofReal (1 / 2) ≤ tileProduct hCH γb
      (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}) := by
    have hc0 : ENNReal.ofReal (1 / (4 * (q : ℝ))) ≠ 0 := by
      simp only [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hc1 : ENNReal.ofReal (1 / (4 * (q : ℝ))) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by rw [div_le_one (by positivity)]; linarith)
    have hd0 : ENNReal.ofReal (1 / 4 : ℝ) ≠ 0 := by
      simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; norm_num
    have hd1 : ENNReal.ofReal (1 / 4 : ℝ) ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    filter_upwards [eventually_measure_compl_le hWmeas' hWlim hc0 hc1,
      eventually_measure_compl_le hDmeas hDlim hd0 hd1] with n hWn hDn
    have h1 : tileProduct hCH γb (W n)ᶜ ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      calc tileProduct hCH γb (W n)ᶜ
          ≤ (#(Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(i : ℤ)) i :
              Finset (Fin d → ℤ)) : ℝ≥0∞) * νt (W n)ᶜ :=
            tileProduct_apply_le_card_mul_tileAverage_apply hCH γb _
        _ ≤ (q : ℝ≥0∞) * ENNReal.ofReal (1 / (4 * (q : ℝ))) := by rw [hCtcard]; gcongr
        _ = ENNReal.ofReal (1 / 4 : ℝ) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            exact mul_inv_four_mul _ hqR.ne'
    have hcover : (Set.univ : Set ((Fin d → ℤ) → E)) ⊆
        (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}) ∪
          ((W n)ᶜ ∪ {ω : (Fin d → ℤ) → E |
            blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}ᶜ) := by
      intro x _
      by_cases hx : x ∈ W n
      · by_cases hy : x ∈ {ω : (Fin d → ℤ) → E |
            blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}
        · exact Or.inl ⟨hx, hy⟩
        · exact Or.inr (Or.inr hy)
      · exact Or.inr (Or.inl hx)
    have h4 : ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ)
        = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    have h5 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    have h3 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ)
        ≤ tileProduct hCH γb
            (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))})
          + ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [h5]
      calc (1 : ℝ≥0∞) = tileProduct hCH γb Set.univ := measure_univ.symm
        _ ≤ tileProduct hCH γb
              ((W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}) ∪
                ((W n)ᶜ ∪ {ω : (Fin d → ℤ) → E |
                  blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}ᶜ)) :=
            measure_mono hcover
        _ ≤ tileProduct hCH γb
              (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))})
            + tileProduct hCH γb ((W n)ᶜ ∪ {ω : (Fin d → ℤ) → E |
                blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}ᶜ) :=
            measure_union_le _ _
        _ ≤ tileProduct hCH γb
              (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))})
            + (ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ)) := by
            gcongr
            exact (measure_union_le _ _).trans (add_le_add h1 hDn)
        _ = _ := by rw [h4]
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h3
  -- ### Step 6. The change of measure from `γ̂` to `λ^S` on the window.
  have hkey : ∀ n, ENNReal.ofReal (1 / 2) ≤ tileProduct hCH γb
        (W n ∩ {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))}) →
      ENNReal.ofReal (Real.exp (-cc n - Real.log 2))
        ≤ (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) (W n) := by
    intro n hhalfn
    set Dn : Set ((Fin d → ℤ) → E) :=
      {ω | blockDensity hCH lam γb (Δ n) ω ≤ ENNReal.ofReal (Real.exp (cc n))} with hDn
    have hM0 : ENNReal.ofReal (Real.exp (cc n)) ≠ 0 := by
      simp only [Ne, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos _
    have hinv : (ENNReal.ofReal (Real.exp (cc n)))⁻¹ = ENNReal.ofReal (Real.exp (-cc n)) := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]
    have hA2 : (ENNReal.ofReal (Real.exp (cc n)))⁻¹ * tileProduct hCH γb (W n ∩ Dn)
        ≤ (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) (W n) := by
      have h := tileProduct_inter_le_mul_infinitePi hCH lam γb hac (hΔtile n)
        (A := W n) (cylinderEvents_mono (Finset.coe_subset.2 (hΔsub n)) _ (hWmeas n))
        (ENNReal.ofReal (Real.exp (cc n)))
      calc (ENNReal.ofReal (Real.exp (cc n)))⁻¹ * tileProduct hCH γb (W n ∩ Dn)
          ≤ (ENNReal.ofReal (Real.exp (cc n)))⁻¹ * (ENNReal.ofReal (Real.exp (cc n)) *
              (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) (W n)) := by gcongr
        _ = _ := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hM0 ENNReal.ofReal_ne_top, one_mul]
    have hexp : Real.exp (-cc n - Real.log 2) = Real.exp (-cc n) * (1 / 2) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log 2),
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    calc ENNReal.ofReal (Real.exp (-cc n - Real.log 2))
        = (ENNReal.ofReal (Real.exp (cc n)))⁻¹ * ENNReal.ofReal (1 / 2) := by
          rw [hexp, ENNReal.ofReal_mul (Real.exp_pos _).le, hinv]
      _ ≤ (ENNReal.ofReal (Real.exp (cc n)))⁻¹ * tileProduct hCH γb (W n ∩ Dn) := by gcongr
      _ ≤ _ := hA2
  -- ### Step 7. The exponent is eventually at least `|Λ_n| (𝓀(ν) − ε)`.
  have hcardpos : ∀ n, (0 : ℝ) < (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) := fun n ↦ by
    exact_mod_cast (hne n).card_pos
  have hhull : Tendsto (fun n ↦ (#(Δ n) : ℝ)
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_card_tileHull_div_card i m hs).congr fun n ↦ ?_
    rw [hΔ]
  have hcclim : Tendsto (fun n ↦ cc n
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop
      (𝓝 (K.toReal / q + ε')) := by
    have hqe : (K.toReal + (q : ℝ) * ε') / q = K.toReal / q + ε' :=
      add_mul_div_self _ _ _ hqR.ne'
    have h := hhull.mul_const ((K.toReal + (q : ℝ) * ε') / q)
    rw [one_mul, hqe] at h
    refine h.congr fun n ↦ ?_
    have hq : (#(Δ n) : ℝ) = (#(tileIdxImage hCH (Δ n)) : ℝ) * q := by exact_mod_cast hΔcard n
    rw [hcc, hq]
    exact mul_div_mul_add_div _ _ _ _ _ hqR.ne' (hcardpos n).ne'
  have hinvcard : Tendsto (fun n ↦ ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    have hpow : Tendsto (fun n ↦ (((s n + 1) ^ d : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_natCast_atTop_atTop.comp ?_
      exact (tendsto_pow_atTop (NeZero.ne d)).comp
        (tendsto_atTop_mono (fun n ↦ Nat.le_succ (s n)) hs)
    refine hpow.congr fun n ↦ ?_
    rw [← card_Icc_cube (m n) (s n)]
  set L : ℝ := -(K.toReal / q + ε') with hLdef
  have hFlim : Tendsto (fun n ↦ (-cc n - Real.log 2)
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 L) := by
    have h := (hcclim.neg).sub (hinvcard.const_mul (Real.log 2))
    simp only [mul_zero, sub_zero] at h
    refine h.congr fun n ↦ ?_
    ring
  have hrL : -k₀ - ε < L := by
    have h2 : K.toReal / q ≤ k₀ := by rw [div_le_iff₀ hqR]; exact hKreal
    rw [hLdef, hε'def] at *
    linarith
  filter_upwards [hhalf, hFlim.eventually (lt_mem_nhds hrL)] with n hhalfn hFn
  refine ⟨W n, hWmeas n, hWC n, hWenergy n, ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) (hkey n hhalfn)
  have hcardn := hcardpos n
  rw [lt_div_iff₀ hcardn] at hFn
  rw [hk₀def, neg_neg] at hFn
  nlinarith [hFn]

open scoped Classical in
/-- **Georgii (15.55)**, the estimate that carries the large deviation lower bound (15.47), in
the form both of its corollaries consume.

Let `Φ ∈ ℬ_Θ`, let `C` be a set of random fields, let `ν ∈ 𝓟_Θ` lie in Georgii's `C°` — the
interior of `C` *in* `𝓟_Θ`, spelled `C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E] ν` — and let
`r < −𝒜(ν|Φ)`. Then, along any sequence of cubes `Λ_n` of `ℤ^d` whose side tends to
infinity, with arbitrary torus reductions `π_n`, there is eventually an event `B` of the volume
`Λ_n` itself, contained in `{°R_{Λ_n} ∈ C}`, with `γ^Φ_{Λ_n}(B | ω) ≥ e^{|Λ_n| r}` for *every*
boundary condition `ω`. (The event `{°R_{Λ_n} ∈ C}` need not be measurable for an arbitrary `C`,
which is why the witness `B` is exposed: integrating over `ω` against a Gibbs measure needs a
measurable event.)

The event `B` is the window of
`eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem`, Georgii's `A_Λ`; the
energy constraint on `B` bounds the Hamiltonian through the estimate (15.25), so the Gibbs kernel
is bounded below by `e^{−b − log Z_{Λ_n}(ω)} λ^S(B)`
(`le_gibbsSpecificationOfAbsolutelySummable_apply`), and `|Λ_n|⁻¹ log Z_{Λ_n}(ω) → P(Φ)`
uniformly in `ω` (Georgii (15.31), via `logSupZ`). -/
theorem eventually_exists_ofReal_exp_le_gibbsSpecification
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    {C : Set (WithLocalConvergence (Fin d → ℤ) E)}
    {ν : Measure ((Fin d → ℤ) → E)} (hν : ν ∈ invariantFields (shiftGroup (Fin d → ℤ) E))
    (hνC : C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E]
      (WithSetwiseTopology.ofMeasure ⟨ν, hν.1⟩ : WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {r : ℝ} (hr : (r : EReal) < -Φ.specificRelativeEntropy lam ν) :
    ∀ᶠ n in atTop, ∃ B : Set ((Fin d → ℤ) → E),
      MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] B ∧
      B ⊆ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} ∧
      ∀ ω : (Fin d → ℤ) → E,
        ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ) * r))
          ≤ Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1
              (Finset.Icc (m n) fun k ↦ m n k + s n) ω B := by
  classical
  have hprobν : IsProbabilityMeasure ν := hν.1
  -- ### Step 0. The excess free energy of `ν` is a finite number `A`, and `r < -A`.
  have hAtop : Φ.specificRelativeEntropy lam ν ≠ ⊤ := by
    intro h; rw [h] at hr; simp at hr
  have hκtop : specificEntropy lam ν ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (specificEntropy_nonpos lam (μ := ν))
  have hκbot : specificEntropy lam ν ≠ ⊥ := by
    intro h
    exact hAtop (by rw [Potential.specificRelativeEntropy, h]; simp)
  set k₀ : ℝ := -(specificEntropy lam ν).toReal with hk₀def
  have hκeq : specificEntropy lam ν = ((-k₀ : ℝ) : EReal) := by
    rw [hk₀def, neg_neg, EReal.coe_toReal hκtop hκbot]
  set A : ℝ := Φ.pressure lam + Φ.specificEnergy ν + k₀ with hAdef
  have hAeq : Φ.specificRelativeEntropy lam ν = ((A : ℝ) : EReal) := by
    rw [Potential.specificRelativeEntropy, hκeq, ← EReal.coe_sub, hAdef]
    congr 1
    ring
  have hrA : r < -A := by
    rw [hAeq, ← EReal.coe_neg] at hr
    exact_mod_cast hr
  set ε : ℝ := (-A - r) / 3 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  -- ### Step 1. The window.
  have hwin := eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem lam
    (Φ := Φ) hν hνC hs hπ hne hκbot hεpos
  -- ### Step 2. The finite-volume chain of inequalities.
  have hkey : ∀ n (B : Set ((Fin d → ℤ) → E)),
      MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] B →
      (∀ y ∈ B, Φ.specificEnergy (periodicEmpiricalField E (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) y) < Φ.specificEnergy ν + ε) →
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ)
          * ((specificEntropy lam ν).toReal - ε)))
        ≤ (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) B →
      ∀ ω : (Fin d → ℤ) → E,
        ENNReal.ofReal (Real.exp
            (-((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (Φ.specificEnergy ν + ε)
                + 3 * Φ.tail (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
                    (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)))
              - Φ.logZ lam (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) ω
              + (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (-k₀ - ε)))
          ≤ Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1
              (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) ω B := by
    intro n B hBmeas hBenergy hBlam ω
    set Λn : Finset (Fin d → ℤ) := Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ) with hΛn
    set bn : ℝ := (#Λn : ℝ) * (Φ.specificEnergy ν + ε) + 3 * Φ.tail Λn Λn with hbn
    -- on the window the Hamiltonian is at most `bn`
    have hEnergy : ∀ y ∈ B, Φ.hamiltonian Λn y ≤ bn := by
      intro y hy
      have h1 := hBenergy y hy
      have h2 := (abs_le.1 (abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le
        hΦ (hπ n) (hne n) y)).2
      have hcard : (0 : ℝ) ≤ (#Λn : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hA1 := le_gibbsSpecificationOfAbsolutelySummable_apply (Φ := Φ) lam Λn ω hBmeas hEnergy
    have hexp : Real.exp (-bn - Φ.logZ lam Λn ω + (#Λn : ℝ) * (-k₀ - ε))
        = Real.exp (-bn - Φ.logZ lam Λn ω) * Real.exp ((#Λn : ℝ) * (-k₀ - ε)) := by
      rw [Real.exp_add]
    have hk₀ : (specificEntropy lam ν).toReal - ε = -k₀ - ε := by rw [hk₀def, neg_neg]
    calc ENNReal.ofReal (Real.exp (-bn - Φ.logZ lam Λn ω + (#Λn : ℝ) * (-k₀ - ε)))
        = ENNReal.ofReal (Real.exp (-bn - Φ.logZ lam Λn ω))
            * ENNReal.ofReal (Real.exp ((#Λn : ℝ) * (-k₀ - ε))) := by
          rw [hexp, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (-bn - Φ.logZ lam Λn ω))
            * (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) B := by
          gcongr
          rw [← hk₀]
          exact hBlam
      _ ≤ Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1 Λn ω B := hA1
  -- ### Step 3. The exponent is eventually at least `|Λ_n| r`.
  have hside : ∀ k, Tendsto (fun n ↦ (fun k' ↦ m n k' + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have hcardpos : ∀ n, (0 : ℝ) < (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) := fun n ↦ by
    exact_mod_cast (hne n).card_pos
  have htail : Tendsto (fun n ↦ Φ.tail (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
      (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 0) :=
    Potential.tendsto_tail_div_card hΦ hside
  have hsup : Tendsto (fun n ↦ Φ.logSupZ lam (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 (Φ.pressure lam)) := by
    have h := (Potential.tendsto_pressureTerm_div_card lam hΦ hside).sub htail
    rw [sub_zero] at h
    refine h.congr fun n ↦ ?_
    rw [Potential.pressureTerm]
    ring
  set L : ℝ := -(Φ.specificEnergy ν + ε) - Φ.pressure lam + (-k₀ - ε) with hLdef
  have hFlim : Tendsto (fun n ↦
      (-((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (Φ.specificEnergy ν + ε)
          + 3 * Φ.tail (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
              (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)))
        - Φ.logSupZ lam (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
        + (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (-k₀ - ε))
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 L) := by
    have h := (((tendsto_const_nhds (x := -(Φ.specificEnergy ν + ε)) (f := atTop (α := ℕ))).sub
      (htail.const_mul 3)).sub hsup).add (tendsto_const_nhds (x := -k₀ - ε))
    simp only [mul_zero, sub_zero] at h
    refine h.congr fun n ↦ ?_
    exact neg_add_div_expand _ _ _ _ _ (hcardpos n).ne'
  have hrL : r < L := by
    rw [hLdef, hAdef] at *
    linarith [hεdef]
  filter_upwards [hwin, hFlim.eventually (lt_mem_nhds hrL)] with n hn hFn
  obtain ⟨B, hBmeas, hBC, hBenergy, hBlam⟩ := hn
  refine ⟨B, hBmeas, hBC, fun ω ↦ ?_⟩
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (hkey n B hBmeas hBenergy hBlam ω)
  have hlogZ := Potential.logZ_le_logSupZ lam (Φ := Φ)
    (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) ω
  have hcardn := hcardpos n
  rw [lt_div_iff₀ hcardn] at hFn
  nlinarith [hFn, hlogZ]

/-- **Georgii (15.55) as he states it.** For `ν ∈ C°` with `𝒜(ν|Φ) < ∞` and every `r < −𝒜(ν|Φ)`,
the Gibbs distributions in the cubes `Λ_n` eventually give the event `{°R_{Λ_n} ∈ C}` probability
at least `e^{|Λ_n| r}`, *uniformly in the boundary condition*. -/
theorem eventually_ofReal_exp_le_gibbsSpecification_setOf_periodicEmpiricalField_mem
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    {C : Set (WithLocalConvergence (Fin d → ℤ) E)}
    {ν : Measure ((Fin d → ℤ) → E)} (hν : ν ∈ invariantFields (shiftGroup (Fin d → ℤ) E))
    (hνC : C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E]
      (WithSetwiseTopology.ofMeasure ⟨ν, hν.1⟩ : WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {r : ℝ} (hr : (r : EReal) < -Φ.specificRelativeEntropy lam ν) :
    ∀ᶠ n in atTop, ∀ ω : (Fin d → ℤ) → E,
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ) * r))
        ≤ Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1
            (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} := by
  filter_upwards [eventually_exists_ofReal_exp_le_gibbsSpecification lam hΦ hν hνC hs hπ
    hne hr] with n hn ω
  obtain ⟨B, -, hBsub, hB⟩ := hn
  exact (hB ω).trans (measure_mono hBsub)

/-- **Georgii (15.55) for a Gibbs measure**, the "in particular" clause of Theorem (15.45): the
same lower bound holds for every `μ ∈ 𝒢(Φ)`, obtained by integrating the uniform bound over the
boundary condition. -/
theorem eventually_ofReal_exp_le_measure_setOf_periodicEmpiricalField_mem
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    {C : Set (WithLocalConvergence (Fin d → ℤ) E)}
    {ν : Measure ((Fin d → ℤ) → E)} (hν : ν ∈ invariantFields (shiftGroup (Fin d → ℤ) E))
    (hνC : C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E]
      (WithSetwiseTopology.ofMeasure ⟨ν, hν.1⟩ : WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {r : ℝ} (hr : (r : EReal) < -Φ.specificRelativeEntropy lam ν)
    {μ : Measure ((Fin d → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : Specification.IsGibbsMeasure
      (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1) μ) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ) * r))
        ≤ μ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} := by
  filter_upwards [eventually_exists_ofReal_exp_le_gibbsSpecification lam hΦ hν hνC hs hπ
    hne hr] with n hn
  obtain ⟨B, hBmeas, hBsub, hB⟩ := hn
  set γ := Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1 with hγ
  set Λn : Finset (Fin d → ℤ) := Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ) with hΛn
  have hbind : μ.bind (γ Λn) = μ :=
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob).1 hμ Λn
  have hBmeas' : MeasurableSet B := cylinderEvents_le_pi _ hBmeas
  have hker : AEMeasurable (γ Λn : ((Fin d → ℤ) → E) → Measure ((Fin d → ℤ) → E)) μ :=
    (((γ Λn).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  calc ENNReal.ofReal (Real.exp ((#Λn : ℝ) * r))
      = ∫⁻ _, ENNReal.ofReal (Real.exp ((#Λn : ℝ) * r)) ∂μ := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ ω, γ Λn ω B ∂μ := lintegral_mono fun ω ↦ hB ω
    _ = (μ.bind (γ Λn)) B := (Measure.bind_apply hBmeas' hker).symm
    _ = μ B := by rw [hbind]
    _ ≤ μ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} := measure_mono hBsub

/-! ### Georgii (15.47) -/

section Ambient2

variable (S E : Type*) [MeasurableSpace E] [AddCommGroup S]

/-- **Georgii's `C°`**: the interior, in `𝓟_Θ`, of a set `C` of shift-invariant random fields
for the topology of local convergence. -/
abbrev invariantInterior (C : Set (WithLocalConvergence S E)) : Set (WithLocalConvergence S E) :=
  {ρ ∈ invariantRandomFields S E | C ∈ 𝓝[invariantRandomFields S E] ρ}

end Ambient2

/-- The `EReal` bookkeeping of (15.47): `log e^{|Λ| r} / |Λ| = r`. -/
private lemma coe_mul_div_natCast_eq (a : ℕ) (ha : a ≠ 0) (z : ℝ) :
    (((a : ℝ) * z : ℝ) : EReal) / ((a : ℕ) : EReal) = (z : EReal) := by
  rw [← EReal.coe_natCast, ← EReal.coe_div]
  congr 1
  field_simp

/-- **Georgii (15.47), the large deviation lower bound.** For `Φ ∈ ℬ_Θ` and any set `C` of random
fields,
`liminf |Λ|⁻¹ log inf_ω γ^Φ_Λ(°R_Λ ∈ C | ω) ≥ − inf_{ν ∈ C°} 𝒜(ν|Φ)`
along any sequence of cubes of `ℤ^d` whose side tends to infinity, with arbitrary
torus reductions. Here `C°` is Georgii's interior of `C` *in* `𝓟_Θ`
(`MeasureTheory.GibbsMeasure.invariantInterior`) and `𝒜(·|Φ)` is the excess free energy
`Potential.specificRelativeEntropy`. -/
theorem neg_iInf_specificRelativeEntropy_le_liminf_log_iInf_gibbsSpecification
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    (C : Set (WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty) :
    -(⨅ ρ ∈ invariantInterior (Fin d → ℤ) E C,
        Φ.specificRelativeEntropy lam (ρ.toMeasure : Measure ((Fin d → ℤ) → E)))
      ≤ liminf (fun n ↦ ENNReal.log (⨅ ω, Potential.gibbsSpecificationOfAbsolutelySummable
            (Φ := Φ) lam 1 (Finset.Icc (m n) fun k ↦ m n k + s n) ω
            {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n) : EReal)) atTop := by
  rw [EReal.neg_le]
  refine le_iInf₂ fun ρ hρ ↦ ?_
  rw [EReal.neg_le]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_
  have hev := eventually_ofReal_exp_le_gibbsSpecification_setOf_periodicEmpiricalField_mem
    lam hΦ hρ.1 hρ.2 hs hπ hne hz
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  have hcard : (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))) ≠ 0 := (hne n).card_pos.ne'
  have hlog : ENNReal.log (ENNReal.ofReal (Real.exp
      ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
      = (((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  calc (z : EReal)
      = ENNReal.log (ENNReal.ofReal (Real.exp
          ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
        / ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℕ) : EReal) := by
        rw [hlog, coe_mul_div_natCast_eq _ hcard]
    _ ≤ _ := by
        refine EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _) ?_
        exact ENNReal.log_le_log (le_iInf fun ω ↦ hn ω)

/-- **Georgii (15.47) for a Gibbs measure**, the "in particular" clause of Theorem (15.45): the
same lower bound holds when `γ^Φ_Λ(·|ω)` is replaced by any `μ ∈ 𝒢(Φ)`. -/
theorem neg_iInf_specificRelativeEntropy_le_liminf_log_measure
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    (C : Set (WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {μ : Measure ((Fin d → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : Specification.IsGibbsMeasure
      (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) lam 1) μ) :
    -(⨅ ρ ∈ invariantInterior (Fin d → ℤ) E C,
        Φ.specificRelativeEntropy lam (ρ.toMeasure : Measure ((Fin d → ℤ) → E)))
      ≤ liminf (fun n ↦ ENNReal.log (μ {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n) : EReal)) atTop := by
  rw [EReal.neg_le]
  refine le_iInf₂ fun ρ hρ ↦ ?_
  rw [EReal.neg_le]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_
  have hev := eventually_ofReal_exp_le_measure_setOf_periodicEmpiricalField_mem
    lam hΦ hρ.1 hρ.2 hs hπ hne hz hμ
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  have hcard : (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))) ≠ 0 := (hne n).card_pos.ne'
  have hlog : ENNReal.log (ENNReal.ofReal (Real.exp
      ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
      = (((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  calc (z : EReal)
      = ENNReal.log (ENNReal.ofReal (Real.exp
          ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
        / ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℕ) : EReal) := by
        rw [hlog, coe_mul_div_natCast_eq _ hcard]
    _ ≤ _ := by
        refine EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _) ?_
        exact ENNReal.log_le_log hn

end LowerBound

end MeasureTheory.GibbsMeasure

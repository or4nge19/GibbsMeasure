/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.EssSup
public import GibbsMeasure.Specification.PeriodicGibbs

/-!
# Georgii §18.1, (18.1)–(18.2) and (18.8)–(18.9): local ground states and the weight `t(G, Φ)`

Georgii, *Gibbs Measures and Phase Transitions*, §18.1.  Throughout, `Φ` is a `C`-potential
(17.18) on `ℤ^d`, so it is the single measurable function `Φ_C = φ` on the configurations
`E^C` of the unit cube `C = {0, 1}^d`, invariant under each reflection `r_k` of the cube and —
this is what hypothesis (17.18)(iv) delivers — bounded below.

* `MeasureTheory.GibbsMeasure.localGroundEnergy` is **(18.1)**, `m_Φ = λ`-inf `Φ_C`, and
  `localGroundEnergy_eq_sSup` is Georgii's formula `sup {c : λ^C(Φ_C ≤ c) = 0}` for it.
* `MeasureTheory.GibbsMeasure.localGroundStates` is **(18.2)**, `G_ε(Φ) = {Φ_C ≤ m_Φ + ε}`;
  `measure_localGroundStates_pos` is Georgii's remark that `λ^C(G_ε(Φ)) > 0` for `ε > 0`.
* `MeasureTheory.GibbsMeasure.IsRSymmetric` is Georgii's `r`-symmetry of a set `G ⊆ E^C`, and
  `IsRSymmetric.preimage_tauPow` upgrades invariance under the generating reflections `r_k` to
  invariance under all the iterated reflections `r^i` of (17.14).  The sets `G_ε(Φ)` are
  `r`-symmetric (`isRSymmetric_localGroundStates`), by condition (iii) of (17.18).
* `MeasureTheory.GibbsMeasure.patternWeight` is **(18.8)**, `t(G, Φ)`, with
  `patternWeightAt` its `δ`-th term and `patternWeight_eq_iInf` the identification.  Georgii's
  **Remarks (18.9)(1)–(4)** are `patternWeight_anti` (1), `groundStateCost_eq_iInf` (2),
  `patternWeight_le_of_abs_sub_le` (3, in the quantitative form `t(G, Ψ) ≤ e^{4η} t(G, Φ)`
  when `‖Ψ_C - Φ_C‖ ≤ η`, which implies Georgii's `ε`-form), and `patternWeight_smul_le`
  together with `tendsto_patternWeight_smul_atTop` (4).

## Normalisation

Georgii's `t(G, Φ)` is written with the normalised a priori measure `λ̃ = λ(E)⁻¹ λ`; we simply
take the a priori measure `ν` to be a probability measure.  This costs no generality: `m_Φ` and
`G_ε(Φ)` only depend on the null sets of `λ^C`, hence are unchanged by the normalisation, and
Georgii's reduction of an infinite `λ` to a finite one is his (2.18).

## Georgii's `λ-sup` in Remark (18.9)(2)

Georgii states (18.9)(2) with the essential supremum `λ-sup_M Φ_C = inf{c : λ^C(M ∩ {Φ_C ≥ c})
= 0}`, which is `+∞` when `Φ_C` is essentially unbounded on `M`; over `ℝ`, Mathlib's `essSup`
returns the junk value `sInf ∅ = 0` there instead, so transcribing (18.9)(2) with `essSup`
would be false as soon as some positive-measure `M` carries an essentially unbounded `Φ_C`.
`groundStateCost_eq_iInf_of_ae_le` therefore ranges over the *pairs* `(M, c)` with
`λ^C(M) > 0` and `Φ_C ≤ c` `λ^C`-a.e. on `M`, which is Georgii's infimum with the `λ-sup`
unfolded (the terms he writes with `λ-sup_M Φ_C = +∞` are `+∞` and do not affect an infimum).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-! ### The a priori measure on the unit cube -/

/-- **Georgii's `λ^C`**: the a priori measure on the configurations `E^C` of the unit cube
`C = {0, 1}^d`. -/
abbrev cubeMeasure (d : ℕ) {E : Type*} [MeasurableSpace E] (ν : Measure E) :
    Measure ((Fin d → Fin 2) → E) :=
  Measure.pi fun _ ↦ ν

instance (ν : Measure E) [IsProbabilityMeasure ν] : NeZero (cubeMeasure d ν) :=
  ⟨IsProbabilityMeasure.ne_zero _⟩

/-! ### Georgii (18.1): the local ground state energy `m_Φ` -/

variable (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)

/-- **Georgii (18.1).** `m_Φ`, the essential infimum of the cube interaction `Φ_C = φ` relative
to the a priori measure `λ^C` on `E^C`. -/
def localGroundEnergy : ℝ := essInf φ (cubeMeasure d ν)

variable {φ ν}

/-- Every pointwise lower bound for `Φ_C` is a lower bound for `m_Φ`. -/
theorem le_localGroundEnergy [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    M ≤ localGroundEnergy φ ν :=
  le_essInf_of_ae_le _ (Eventually.of_forall hM) (isCoboundedUnder_ge_ae φ)

/-- `Φ_C ≥ m_Φ` almost everywhere: `m_Φ` really is the essential infimum. -/
theorem ae_localGroundEnergy_le [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    ∀ᵐ ζ ∂cubeMeasure d ν, localGroundEnergy φ ν ≤ φ ζ :=
  ae_essInf_le (isBoundedUnder_ge_ae (Eventually.of_forall hM))

/-- The set of levels below which `Φ_C` almost never drops is bounded above, because `Φ_C` is
real valued and `λ^C` is a probability measure. -/
theorem bddAbove_setOf_measure_le_eq_zero [IsProbabilityMeasure ν] :
    BddAbove {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} := by
  by_contra hbdd
  -- otherwise `E^C` is a countable union of null sets
  have hnull : ∀ n : ℕ, cubeMeasure d ν {ζ | φ ζ ≤ (n : ℝ)} = 0 := by
    intro n
    obtain ⟨c, hc, hcn⟩ := not_bddAbove_iff.1 hbdd (n : ℝ)
    exact measure_mono_null (fun ζ hζ ↦ le_trans hζ hcn.le) hc
  have : cubeMeasure d ν (⋃ n : ℕ, {ζ | φ ζ ≤ (n : ℝ)}) = 0 := measure_iUnion_null hnull
  rw [show (⋃ n : ℕ, {ζ : (Fin d → Fin 2) → E | φ ζ ≤ (n : ℝ)}) = univ from
    eq_univ_of_forall fun ζ ↦ by
      obtain ⟨n, hn⟩ := exists_nat_ge (φ ζ)
      exact mem_iUnion.2 ⟨n, hn⟩, measure_univ] at this
  exact one_ne_zero this

/-- **Georgii (18.1) as stated**: `m_Φ = sup {c : λ^C(Φ_C ≤ c) = 0}`.  Mathlib's `essInf` is
the supremum of the levels `c` with `λ^C(Φ_C < c) = 0`; the two suprema agree because the sets
are downward closed and differ only at their top level. -/
theorem localGroundEnergy_eq_sSup [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    localGroundEnergy φ ν = sSup {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} := by
  have hBA : {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} ⊆
      {a : ℝ | cubeMeasure d ν {ζ | φ ζ < a} = 0} :=
    fun c hc ↦ measure_mono_null (fun ζ (hζ : φ ζ < c) ↦ hζ.le) hc
  have hBne : {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0}.Nonempty := by
    refine ⟨M - 1, ?_⟩
    have hempty : {ζ : (Fin d → Fin 2) → E | φ ζ ≤ M - 1} = ∅ := by
      ext ζ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [hM ζ]
    change cubeMeasure d ν {ζ | φ ζ ≤ M - 1} = 0
    rw [hempty, measure_empty]
  have hBbdd : BddAbove {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} :=
    bddAbove_setOf_measure_le_eq_zero
  have hlower : ∀ a ∈ {a : ℝ | cubeMeasure d ν {ζ | φ ζ < a} = 0}, ∀ c < a,
      c ∈ {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} :=
    fun a ha c hc ↦ measure_mono_null (fun ζ (hζ : φ ζ ≤ c) ↦ lt_of_le_of_lt hζ hc) ha
  have hAbdd : BddAbove {a : ℝ | cubeMeasure d ν {ζ | φ ζ < a} = 0} := by
    obtain ⟨u, hu⟩ := hBbdd
    refine ⟨u + 1, fun a ha ↦ ?_⟩
    have := hu (hlower a ha (a - 1) (by linarith))
    linarith
  rw [localGroundEnergy, essInf_eq_sSup]
  refine le_antisymm (csSup_le (Set.Nonempty.mono hBA hBne) fun a ha ↦ ?_)
    (csSup_le_csSup hAbdd hBne hBA)
  exact le_of_forall_lt_imp_le_of_dense fun c hc ↦ le_csSup hBbdd (hlower a ha c hc)

/-! ### Georgii (18.2): the local `ε`-ground states -/

variable (φ ν) in
/-- **Georgii (18.2).** `G_ε(Φ) = {ω ∈ E^C : Φ_C(ω) ≤ m_Φ + ε}`, the set of local
`ε`-ground states of the `C`-potential `Φ`. -/
def localGroundStates (ε : ℝ) : Set ((Fin d → Fin 2) → E) :=
  {ζ | φ ζ ≤ localGroundEnergy φ ν + ε}

@[simp] lemma mem_localGroundStates {ε : ℝ} {ζ : (Fin d → Fin 2) → E} :
    ζ ∈ localGroundStates φ ν ε ↔ φ ζ ≤ localGroundEnergy φ ν + ε := Iff.rfl

lemma measurableSet_localGroundStates (hφ : Measurable φ) (ε : ℝ) :
    MeasurableSet (localGroundStates φ ν ε) :=
  measurableSet_le hφ measurable_const

lemma localGroundStates_mono {ε ε' : ℝ} (h : ε ≤ ε') :
    localGroundStates φ ν ε ⊆ localGroundStates φ ν ε' := by
  intro ζ hζ
  rw [mem_localGroundStates] at hζ ⊢
  linarith

/-- **Georgii's remark after (18.2)**: the local `ε`-ground states have positive measure for
every `ε > 0`.  This is exactly what makes `m_Φ` the *essential* infimum. -/
theorem measure_localGroundStates_pos [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    {ε : ℝ} (hε : 0 < ε) : 0 < cubeMeasure d ν (localGroundStates φ ν ε) := by
  rw [pos_iff_ne_zero]
  intro h0
  have hmem : localGroundEnergy φ ν + ε ∈ {c : ℝ | cubeMeasure d ν {ζ | φ ζ ≤ c} = 0} := h0
  have := le_csSup (bddAbove_setOf_measure_le_eq_zero (φ := φ) (ν := ν)) hmem
  rw [← localGroundEnergy_eq_sSup hM] at this
  linarith

/-! ### `r`-symmetry -/

variable (E) in
/-- **Georgii, §18.1.** A set `G ⊆ E^C` of cube configurations is *`r`-symmetric* if it is
invariant under each of the reflections `r_k` of the unit cube (17.14).  By
`IsRSymmetric.preimage_tauPow` this is the same as Georgii's `r^i G = G` for all `i`. -/
def IsRSymmetric (G : Set ((Fin d → Fin 2) → E)) : Prop :=
  ∀ k : Fin d, cubeRefl E k ⁻¹' G = G

/-- Invariance of a set under a family of involutions passes to the iterated involutions
`τ^i` of Georgii (17.10). -/
lemma preimage_tauPow_eq_self {X : Type*} [MeasurableSpace X] {N : ℕ} :
    ∀ {n : ℕ} (τ : Fin n → X ≃ᵐ X) {s : Set X}, (∀ k, τ k ⁻¹' s = s) →
      ∀ i : Fin n → ZMod (2 * N), tauPow τ i ⁻¹' s = s
  | 0, τ, s, _, i => by ext x; simp [tauPow_zero]
  | n + 1, τ, s, hs, i => by
    ext x
    rw [mem_preimage, tauPow_succ]
    have hstep : spinIterate (τ 0) (i 0) x ∈ s ↔ x ∈ s := by
      unfold spinIterate
      split_ifs with h
      · exact Iff.rfl
      · exact Set.ext_iff.1 (hs 0) x
    have hrest := preimage_tauPow_eq_self (N := N) (fun k ↦ τ k.succ) (fun k ↦ hs k.succ)
      (Fin.tail i)
    rw [← hstep]
    exact Set.ext_iff.1 hrest (spinIterate (τ 0) (i 0) x)

/-- **Georgii's `r^i G = G`.** An `r`-symmetric set is invariant under every iterated
reflection `r^i` of the unit cube. -/
theorem IsRSymmetric.preimage_tauPow {G : Set ((Fin d → Fin 2) → E)} (hG : IsRSymmetric E G)
    {N : ℕ} (i : Fin d → ZMod (2 * N)) : tauPow (cubeRefl E) i ⁻¹' G = G :=
  preimage_tauPow_eq_self _ hG i

/-- **Condition (iii) of Georgii (17.18)** makes the local `ε`-ground states `r`-symmetric. -/
theorem isRSymmetric_localGroundStates (hφk : ∀ (k : Fin d) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (ε : ℝ) : IsRSymmetric E (localGroundStates φ ν ε) := by
  intro k
  ext ζ
  simp only [mem_preimage, mem_localGroundStates, hφk k ζ]

/-! ### Georgii (18.8): the weight `t(G, Φ)` -/

variable (φ ν) in
/-- **Georgii's `λ-inf_{E^C ∖ G} Φ_C`**: the essential infimum of the cube interaction off the
pattern set `G`, relative to `λ^C`. -/
def energyOutside (G : Set ((Fin d → Fin 2) → E)) : ℝ :=
  essInf φ ((cubeMeasure d ν).restrict Gᶜ)

variable (φ ν) in
/-- The third factor of Georgii (18.8), `inf_{δ > 0} e^δ / λ̃^C(G_δ(Φ))`: the price of confining
the configuration on a cube to the local `δ`-ground states. -/
def groundStateCost : ℝ≥0∞ :=
  ⨅ δ : {r : ℝ // 0 < r},
    ENNReal.ofReal (Real.exp δ.1) / cubeMeasure d ν (localGroundStates φ ν δ.1)

variable (φ ν) in
/-- The `δ`-th term of the infimum in Georgii (18.8):
`exp[-λ-inf_{E^C∖G}(Φ_C - m_Φ)] · λ̃^C(E^C∖G)^{1/|C|} · e^δ/λ̃^C(G_δ(Φ))`. -/
def patternWeightAt (G : Set ((Fin d → Fin 2) → E)) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G))
    * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
    * (ENNReal.ofReal (Real.exp δ) / cubeMeasure d ν (localGroundStates φ ν δ))

variable (φ ν) in
/-- **Georgii (18.8).**  The weight
`t(G, Φ) = exp[-λ-inf_{E^C∖G}(Φ_C - m_Φ)] · λ̃^C(E^C∖G)^{1/|C|} · inf_{δ>0} e^δ/λ̃^C(G_δ(Φ))`
measuring the extent to which the pattern `G` is favoured by `Φ` and the a priori measure. -/
def patternWeight (G : Set ((Fin d → Fin 2) → E)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G))
    * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
    * groundStateCost φ ν

/-! ### Georgii (18.9): elementary properties of `t(G, Φ)` -/

/-- Each term of `groundStateCost` is at least `1`: `e^δ ≥ 1` and `λ̃^C(G_δ) ≤ 1`. -/
lemma one_le_groundStateCost [IsProbabilityMeasure ν] : 1 ≤ groundStateCost φ ν := by
  refine le_iInf fun δ ↦ ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inr (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (Or.inl (measure_ne_top _ _)), one_mul]
  exact (prob_le_one).trans (ENNReal.one_le_ofReal.2 (Real.one_le_exp δ.2.le))

/-- `groundStateCost` is finite: the term at any `δ > 0` is, since `λ^C(G_δ(Φ)) > 0`. -/
lemma groundStateCost_lt_top [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) :
    groundStateCost φ ν < ∞ := by
  refine lt_of_le_of_lt (iInf_le _ ⟨1, one_pos⟩) ?_
  exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (measure_localGroundStates_pos hM one_pos).ne'

/-- **Georgii Remark (18.9)(1).** `t(·, Φ)` is decreasing: a larger pattern set is cheaper. -/
theorem patternWeight_anti [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    {G G' : Set ((Fin d → Fin 2) → E)} (h : G ⊆ G') :
    patternWeight φ ν G' ≤ patternWeight φ ν G := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  by_cases h0 : cubeMeasure d ν G'ᶜ = 0
  · have hz : patternWeight φ ν G' = 0 := by
      rw [patternWeight, h0, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    rw [hz]
    exact zero_le
  refine mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl
  · have hne : NeZero ((cubeMeasure d ν).restrict G'ᶜ) := by
      refine ⟨fun hc ↦ h0 ?_⟩
      rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
    have hle : energyOutside φ ν G ≤ energyOutside φ ν G' :=
      essInf_antitone_measure
        (Measure.absolutelyContinuous_of_le
          (Measure.restrict_mono (compl_subset_compl.2 h) le_rfl))
        (isBoundedUnder_ge_ae (Eventually.of_forall hM))
        (isCoboundedUnder_ge_ae φ)
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  · exact ENNReal.rpow_le_rpow (measure_mono (compl_subset_compl.2 h)) hp.le

/-- `t(G, Φ)` is the infimum over `δ > 0` of the terms `patternWeightAt`. -/
theorem patternWeight_eq_iInf [IsProbabilityMeasure ν] (G : Set ((Fin d → Fin 2) → E)) :
    patternWeight φ ν G = ⨅ δ : {r : ℝ // 0 < r}, patternWeightAt φ ν G δ.1 := by
  have hfin : ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G))
      * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹) ≠ ∞ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (ENNReal.rpow_le_one prob_le_one (by positivity))
  rw [patternWeight, groundStateCost,
    ENNReal.mul_iInf (fun h ↦ absurd h hfin)]
  rfl

/-! ### Georgii Remark (18.9)(4): the low temperature limit -/

/-- Scaling a `C`-potential scales its local ground state energy. -/
theorem localGroundEnergy_smul [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) {β : ℝ}
    (hβ : 0 < β) : localGroundEnergy (fun ζ ↦ β * φ ζ) ν = β * localGroundEnergy φ ν :=
  essInf_const_mul hβ (Eventually.of_forall hM)

/-- Scaling a `C`-potential scales the tolerance in the definition of the local ground states:
`G_{βδ}(βΦ) = G_δ(Φ)`. -/
theorem localGroundStates_smul [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ) {β : ℝ}
    (hβ : 0 < β) (δ : ℝ) :
    localGroundStates (fun ζ ↦ β * φ ζ) ν (β * δ) = localGroundStates φ ν δ := by
  ext ζ
  rw [mem_localGroundStates, mem_localGroundStates, localGroundEnergy_smul hM hβ, ← mul_add]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Off the local `ε`-ground states the interaction exceeds `m_Φ + ε`, hence so does its
essential infimum there. -/
theorem le_energyOutside_localGroundStates [IsProbabilityMeasure ν] (hφ : Measurable φ) {ε : ℝ}
    (hne : cubeMeasure d ν (localGroundStates φ ν ε)ᶜ ≠ 0) :
    localGroundEnergy φ ν + ε ≤ energyOutside φ ν (localGroundStates φ ν ε) := by
  have hz : NeZero ((cubeMeasure d ν).restrict (localGroundStates φ ν ε)ᶜ) := by
    refine ⟨fun hc ↦ hne ?_⟩
    rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
  refine le_essInf_of_ae_le _ (ae_restrict_of_forall_mem
    (measurableSet_localGroundStates hφ ε).compl fun ζ hζ ↦ ?_) (isCoboundedUnder_ge_ae φ)
  have hζ' : ¬ (φ ζ ≤ localGroundEnergy φ ν + ε) := hζ
  exact (not_le.1 hζ').le

/-- **Georgii Remark (18.9)(4), quantitative form.**  For `β > 0`,
`t(G_ε(Φ), βΦ) ≤ e^{-βε/2} / λ̃^C(G_{ε/2}(Φ))`. -/
theorem patternWeight_smul_le [IsProbabilityMeasure ν] (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) {ε : ℝ} (hε : 0 < ε) {β : ℝ} (hβ : 0 < β) :
    patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)
      ≤ ENNReal.ofReal (Real.exp (-(β * ε / 2)))
          / cubeMeasure d ν (localGroundStates φ ν (ε / 2)) := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  have hβM : ∀ ζ, β * M ≤ β * φ ζ := fun ζ ↦ by nlinarith [hM ζ]
  have hy0 : cubeMeasure d ν (localGroundStates φ ν (ε / 2)) ≠ 0 :=
    (measure_localGroundStates_pos hM (by linarith)).ne'
  by_cases hGc : cubeMeasure d ν (localGroundStates φ ν ε)ᶜ = 0
  · rw [patternWeight, hGc, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  -- the first factor
  have hfirst : ENNReal.ofReal (Real.exp (localGroundEnergy (fun ζ ↦ β * φ ζ) ν
        - energyOutside (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)))
      ≤ ENNReal.ofReal (Real.exp (-(β * ε))) := by
    have hz : NeZero ((cubeMeasure d ν).restrict (localGroundStates φ ν ε)ᶜ) := by
      refine ⟨fun hc ↦ hGc ?_⟩
      rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
    have hout : energyOutside (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)
        = β * energyOutside φ ν (localGroundStates φ ν ε) :=
      essInf_const_mul hβ (Eventually.of_forall hM)
    have hge := le_energyOutside_localGroundStates hφ hGc
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    rw [localGroundEnergy_smul hM hβ, hout]
    nlinarith
  -- the third factor
  have hthird : groundStateCost (fun ζ ↦ β * φ ζ) ν
      ≤ ENNReal.ofReal (Real.exp (β * (ε / 2)))
        / cubeMeasure d ν (localGroundStates φ ν (ε / 2)) := by
    have h := iInf_le (fun δ : {r : ℝ // 0 < r} ↦
      ENNReal.ofReal (Real.exp δ.1)
        / cubeMeasure d ν (localGroundStates (fun ζ ↦ β * φ ζ) ν δ.1))
      ⟨β * (ε / 2), by positivity⟩
    rwa [localGroundStates_smul hM hβ] at h
  calc patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)
      ≤ ENNReal.ofReal (Real.exp (-(β * ε))) * 1
        * (ENNReal.ofReal (Real.exp (β * (ε / 2)))
            / cubeMeasure d ν (localGroundStates φ ν (ε / 2))) :=
        mul_le_mul' (mul_le_mul' hfirst
          (ENNReal.rpow_le_one prob_le_one hp.le)) hthird
    _ = ENNReal.ofReal (Real.exp (-(β * ε / 2)))
        / cubeMeasure d ν (localGroundStates φ ν (ε / 2)) := by
        rw [mul_one, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        congr 3
        ring

/-- **Georgii Remark (18.9)(4).**  `t(G_ε(Φ), βΦ) → 0` as `β → ∞`, for every `ε > 0`. -/
theorem tendsto_patternWeight_smul_atTop [IsProbabilityMeasure ν] (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun β : ℝ ↦ patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
      Filter.atTop (nhds 0) := by
  have hy0 : cubeMeasure d ν (localGroundStates φ ν (ε / 2)) ≠ 0 :=
    (measure_localGroundStates_pos hM (by linarith)).ne'
  have h1 : Filter.Tendsto (fun β : ℝ ↦ β * ε / 2) Filter.atTop Filter.atTop := by
    have h := Filter.Tendsto.atTop_mul_const (show (0 : ℝ) < ε / 2 by linarith)
      (Filter.tendsto_id (α := ℝ))
    simpa [mul_div_assoc] using h
  have h2 : Filter.Tendsto (fun β : ℝ ↦ -(β * ε / 2)) Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_atTop_atBot.comp h1
  have hexp : Filter.Tendsto (fun β : ℝ ↦ ENNReal.ofReal (Real.exp (-(β * ε / 2))))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun β : ℝ ↦ Real.exp (-(β * ε / 2))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp h2
    have h' := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h'
    exact h'
  have hlim : Filter.Tendsto
      (fun β : ℝ ↦ ENNReal.ofReal (Real.exp (-(β * ε / 2)))
        / cubeMeasure d ν (localGroundStates φ ν (ε / 2))) Filter.atTop (nhds 0) := by
    simp only [div_eq_mul_inv]
    have h3 := ENNReal.Tendsto.mul_const hexp (Or.inr (ENNReal.inv_ne_top.2 hy0))
    rwa [zero_mul] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun β ↦ zero_le) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with β hβ
  exact patternWeight_smul_le hφ hM hε hβ

/-! ### Georgii Remark (18.9)(2) -/

/-- **Georgii Remark (18.9)(2).**  The third factor of `t(G, Φ)` can equally be computed as an
infimum over all sets `M` of positive `λ^C`-measure of `exp[λ-sup_M Φ_C - m_Φ]/λ̃^C(M)`.  We
range over the *pairs* `(M, c)` with `Φ_C ≤ c` almost everywhere on `M`, which is Georgii's
infimum with the essential supremum unfolded: an `M` on which `Φ_C` is essentially unbounded
contributes `+∞` to Georgii's infimum and no pair here, so the two infima agree. -/
theorem groundStateCost_eq_iInf [IsProbabilityMeasure ν] (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) :
    groundStateCost φ ν
      = ⨅ p : {p : Set ((Fin d → Fin 2) → E) × ℝ // MeasurableSet p.1 ∧
            0 < cubeMeasure d ν p.1 ∧ ∀ᵐ ζ ∂(cubeMeasure d ν).restrict p.1, φ ζ ≤ p.2},
          ENNReal.ofReal (Real.exp (p.1.2 - localGroundEnergy φ ν)) / cubeMeasure d ν p.1.1 := by
  refine le_antisymm ?_ (le_iInf fun δ ↦ ?_)
  · -- every admissible pair `(A, c)` dominates the infimum over `δ > 0`
    refine le_iInf fun p ↦ ?_
    obtain ⟨⟨A, c⟩, hAmeas, hApos, hAc⟩ := p
    simp only
    have hAz : NeZero ((cubeMeasure d ν).restrict A) := by
      refine ⟨fun hc ↦ hApos.ne' ?_⟩
      rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
    -- the essential upper bound `c` is at least `m_Φ`
    have hcm : localGroundEnergy φ ν ≤ c := by
      obtain ⟨ζ, hζ₁, hζ₂⟩ :=
        (hAc.and (ae_restrict_of_ae (ae_localGroundEnergy_le hM))).exists
      exact hζ₂.trans hζ₁
    -- the limit `δ ↓ c - m_Φ`
    have hlim : Filter.Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (Real.exp δ) / cubeMeasure d ν A)
        (nhdsWithin (c - localGroundEnergy φ ν) (Set.Ioi (c - localGroundEnergy φ ν)))
        (nhds (ENNReal.ofReal (Real.exp (c - localGroundEnergy φ ν)) / cubeMeasure d ν A)) := by
      simp only [div_eq_mul_inv]
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr (ENNReal.inv_ne_top.2 hApos.ne'))
      exact ((ENNReal.continuous_ofReal.comp Real.continuous_exp).tendsto _).mono_left
        nhdsWithin_le_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : c - localGroundEnergy φ ν < δ := hδ
    have hδpos : 0 < δ := lt_of_le_of_lt (by linarith) hδ'
    -- `A` is almost contained in `G_δ(Φ)`
    have hsub : cubeMeasure d ν A ≤ cubeMeasure d ν (localGroundStates φ ν δ) := by
      have hnull : cubeMeasure d ν (A \ localGroundStates φ ν δ) = 0 := by
        have h0 : (cubeMeasure d ν).restrict A (localGroundStates φ ν δ)ᶜ = 0 := by
          refine measure_mono_null (fun ζ hζ ↦ ?_) (ae_iff.1 hAc)
          have hζ' : ¬ (φ ζ ≤ localGroundEnergy φ ν + δ) := hζ
          intro hle
          exact hζ' (le_trans hle (by linarith))
        rw [Measure.restrict_apply' hAmeas] at h0
        rw [Set.sdiff_eq]
        rwa [Set.inter_comm] at h0
      calc cubeMeasure d ν A
          ≤ cubeMeasure d ν (A ∩ localGroundStates φ ν δ)
            + cubeMeasure d ν (A \ localGroundStates φ ν δ) :=
            measure_le_inter_add_sdiff _ _ _
        _ = cubeMeasure d ν (A ∩ localGroundStates φ ν δ) := by rw [hnull, add_zero]
        _ ≤ cubeMeasure d ν (localGroundStates φ ν δ) := measure_mono Set.inter_subset_right
    calc groundStateCost φ ν
        ≤ ENNReal.ofReal (Real.exp δ) / cubeMeasure d ν (localGroundStates φ ν δ) :=
          iInf_le (fun r : {r : ℝ // 0 < r} ↦
            ENNReal.ofReal (Real.exp r.1) / cubeMeasure d ν (localGroundStates φ ν r.1))
            ⟨δ, hδpos⟩
      _ ≤ ENNReal.ofReal (Real.exp δ) / cubeMeasure d ν A := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 hsub)
  · -- conversely `(G_δ(Φ), m_Φ + δ)` is admissible for every `δ > 0`
    refine le_trans (iInf_le _
      (⟨(localGroundStates φ ν δ.1, localGroundEnergy φ ν + δ.1),
        measurableSet_localGroundStates hφ _, measure_localGroundStates_pos hM δ.2,
        ae_restrict_of_forall_mem (measurableSet_localGroundStates hφ _) fun ζ hζ ↦ hζ⟩ :
        {p : Set ((Fin d → Fin 2) → E) × ℝ // MeasurableSet p.1 ∧
          0 < cubeMeasure d ν p.1 ∧ ∀ᵐ ζ ∂(cubeMeasure d ν).restrict p.1, φ ζ ≤ p.2}))
      (le_of_eq ?_)
    simp only [add_sub_cancel_left]

/-! ### Georgii Remark (18.9)(3): `t(G, ·)` is upper semicontinuous -/

section Perturbation

variable {ψ : ((Fin d → Fin 2) → E) → ℝ} {η : ℝ}

/-- A uniform perturbation of the cube interaction moves the local ground state energy by at
most the size of the perturbation. -/
theorem localGroundEnergy_le_add [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hd : ∀ ζ, |ψ ζ - φ ζ| ≤ η) :
    localGroundEnergy ψ ν ≤ localGroundEnergy φ ν + η :=
  essInf_le_essInf_add (M := M - η)
    (Eventually.of_forall fun ζ ↦ by linarith [hM ζ, abs_le.1 (hd ζ) |>.1])
    (Eventually.of_forall hM)
    (Eventually.of_forall fun ζ ↦ by linarith [abs_le.1 (hd ζ) |>.2])

/-- The essential infimum off a pattern set moves by at most the size of the perturbation. -/
theorem energyOutside_le_add [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hd : ∀ ζ, |ψ ζ - φ ζ| ≤ η) {G : Set ((Fin d → Fin 2) → E)}
    (hGc : cubeMeasure d ν Gᶜ ≠ 0) :
    energyOutside φ ν G ≤ energyOutside ψ ν G + η := by
  have hz : NeZero ((cubeMeasure d ν).restrict Gᶜ) := by
    refine ⟨fun hc ↦ hGc ?_⟩
    rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
  exact essInf_le_essInf_add (M := M) (M' := M - η)
    (Eventually.of_forall hM)
    (Eventually.of_forall fun ζ ↦ by linarith [hM ζ, abs_le.1 (hd ζ) |>.1])
    (Eventually.of_forall fun ζ ↦ by linarith [abs_le.1 (hd ζ) |>.1])

/-- **Georgii Remark (18.9)(3), quantitative form.**  A uniform perturbation of the cube
interaction of size `η` multiplies `t(G, Φ)` by at most `e^{4η}`; upper semicontinuity of
`t(G, ·)` follows by letting `η → 0`. -/
theorem patternWeight_le_of_abs_sub_le [IsProbabilityMeasure ν] {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hη : 0 ≤ η) (hd : ∀ ζ, |ψ ζ - φ ζ| ≤ η) (G : Set ((Fin d → Fin 2) → E)) :
    patternWeight ψ ν G ≤ ENNReal.ofReal (Real.exp (4 * η)) * patternWeight φ ν G := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  have hMψ : ∀ ζ, M - η ≤ ψ ζ := fun ζ ↦ by linarith [hM ζ, abs_le.1 (hd ζ) |>.1]
  by_cases hGc : cubeMeasure d ν Gᶜ = 0
  · rw [patternWeight, hGc, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  -- the exponential factor
  have hfirst : ENNReal.ofReal (Real.exp (localGroundEnergy ψ ν - energyOutside ψ ν G))
      ≤ ENNReal.ofReal (Real.exp (2 * η))
        * ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 := localGroundEnergy_le_add (ν := ν) hM hd
    have h2 := energyOutside_le_add (ν := ν) hM hd hGc
    linarith
  -- the ground state cost
  have hthird : groundStateCost ψ ν
      ≤ ENNReal.ofReal (Real.exp (2 * η)) * groundStateCost φ ν := by
    have hne : Nonempty {r : ℝ // 0 < r} := ⟨⟨1, one_pos⟩⟩
    simp only [groundStateCost]
    rw [ENNReal.mul_iInf (fun h ↦ absurd h ENNReal.ofReal_ne_top)]
    refine le_iInf fun δ ↦ ?_
    have hδ' : (0 : ℝ) < δ.1 + 2 * η := by have := δ.2; linarith
    have hsub : localGroundStates φ ν δ.1 ⊆ localGroundStates ψ ν (δ.1 + 2 * η) := by
      intro ζ hζ
      rw [mem_localGroundStates] at hζ ⊢
      have h1 := localGroundEnergy_le_add (ν := ν) (ψ := φ) (η := η) hMψ
        (fun ζ ↦ by rw [abs_sub_comm]; exact hd ζ)
      have h2 := abs_le.1 (hd ζ) |>.2
      linarith
    calc groundStateCost ψ ν
        ≤ ENNReal.ofReal (Real.exp (δ.1 + 2 * η))
            / cubeMeasure d ν (localGroundStates ψ ν (δ.1 + 2 * η)) :=
          iInf_le (fun r : {r : ℝ // 0 < r} ↦
            ENNReal.ofReal (Real.exp r.1) / cubeMeasure d ν (localGroundStates ψ ν r.1))
            ⟨δ.1 + 2 * η, hδ'⟩
      _ ≤ ENNReal.ofReal (Real.exp (2 * η))
            * (ENNReal.ofReal (Real.exp δ.1) / cubeMeasure d ν (localGroundStates φ ν δ.1)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
            ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith)))
            (ENNReal.inv_le_inv.2 (measure_mono hsub))
  calc patternWeight ψ ν G
      ≤ (ENNReal.ofReal (Real.exp (2 * η))
            * ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G)))
          * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
          * (ENNReal.ofReal (Real.exp (2 * η)) * groundStateCost φ ν) :=
        mul_le_mul' (mul_le_mul' hfirst le_rfl) hthird
    _ = ENNReal.ofReal (Real.exp (4 * η)) * patternWeight φ ν G := by
        rw [patternWeight, show ENNReal.ofReal (Real.exp (4 * η))
          = ENNReal.ofReal (Real.exp (2 * η)) * ENNReal.ofReal (Real.exp (2 * η)) by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            congr 2
            ring]
        ring_nf

end Perturbation

end MeasureTheory.GibbsMeasure

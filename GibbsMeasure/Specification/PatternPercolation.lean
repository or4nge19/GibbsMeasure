/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Data.ENNReal.Pow
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiBlocks
public import GibbsMeasure.Specification.LocalGroundStates

/-!
# Georgii §18.1, (18.3) and (18.10): the pattern set `V(G, ·)` and the chessboard estimate

Georgii, *Gibbs Measures and Phase Transitions*, §18.1.  For a measurable set `G ⊆ E^C` of
configurations on the unit cube `C = {0, 1}^d`, Georgii's (18.3) attaches to a configuration
`ω` the set

`V(G, ω) = {i : (θ_{-i} ω)_C ∈ r^i G}`

of elementary cubes on which `ω` shows the pattern `G`, read through the appropriate iterated
reflection `r^i` of (17.14).  This file works on the torus `Λ = (ℤ/2N)^d`, where the Gibbs
distribution `°γ_Λ^Φ` with periodic boundary condition lives, and proves the finite-volume form
of Georgii's key estimate:

**(18.10)** `°γ_Λ^Φ(D ∩ V(G, ·) = ∅) ≤ t(G, Φ)^{|D|}` for `r`-symmetric `G` and finite `D`.

## Main declarations

* `MeasureTheory.GibbsMeasure.torusPattern` — Georgii (18.3) on the torus.
* `MeasureTheory.GibbsMeasure.map_cubeView_pi` — the spins in one elementary cube are
  `λ^C`-distributed under `λ^Λ`; this is where `2N ≥ 2` enters.
* `MeasureTheory.GibbsMeasure.pi_forall_cubeView_evenSite` — the `N^d` elementary cubes based at
  the *even* sites tile the torus, so under `λ^Λ` their configurations are independent.  This is
  Georgii's `∏'` in the proof of (18.10), and the source of the exponent `1/|C|` in (18.8).
* `MeasureTheory.GibbsMeasure.pow_le_pi_forall_cubeView` — the chessboard estimate (17.17)
  applied to `λ^Λ`: `λ^C(B)^{|Λ|} ≤ λ^Λ(∀ i, ω_{C(i)} ∈ B)` for `r`-symmetric `B`.
* `MeasureTheory.GibbsMeasure.periodicGibbsDist_forall_notMem_torusPattern_le` and
  `MeasureTheory.GibbsMeasure.periodicGibbsDist_forall_notMem_torusPattern_le_patternWeight`
  — **Lemma (18.10)** on the torus, first at a fixed `δ > 0` and then with the infimum of
  (18.8).

## The passage to `𝒢₀(Φ)`

Georgii states (18.10) for `μ ∈ 𝒢₀(Φ)`, the set of `𝓛`-cluster points of the sequence
`(°γ_{Λ(N)}^Φ × δ_{ω_N})_N` of Example (5.20)(3).  The estimate above is the finite-volume
statement his proof establishes ("it is sufficient to prove that `°γ_Λ^Φ(D ∩ V(G, ·) = ∅) ≤
t(G, Φ)^{|D|}` whenever `Λ = Λ(N)` is so large a cube that `Λ ⊃ ⋃_{i ∈ D} C + i`").  The
transport of `°γ_Λ^Φ` from the torus `(ℤ/2N)^d` to a random field on `ℤ^d`, its identification
with the finite-volume Gibbs distribution of the periodic modification `Φ̃^{Λ(N)}` of Example
(4.20)(2), the set `𝒢₀(Φ)` itself, and the passage of the estimate to a cluster point are in
`GibbsMeasure.Specification.PeriodicGibbsLimits`
(`MeasureTheory.GibbsMeasure.forall_notMem_latticePattern_le_patternWeight`).

## What is *not* here

Georgii's **Comment (18.11)** — that (18.10) also holds with `t(G, Φ)` replaced by

`t̃(G, Φ) = exp[-λ-inf_{E^C∖G} Φ_C] λ^C(E^C∖G)^{1/|C|}
             inf_R exp[λ-sup_R Φ_C] / λ^C(R)^{1/|C|}`,

the infimum over the rectangles `R = ∏_{c ∈ C} R_c` with `λ(R_c) > 0` — is not proved.  Its
only new ingredient is the identity `λ^Λ(∏_{i ∈ Λ} 1_{r^i R} ∘ σ_{C(i)}) = λ^C(R)^{|Λ|/|C|}`,
which needs the description of the iterated reflection `r^i` of (17.14) as the permutation
`c ↦ (if i_k is even then c_k else 1 - c_k)_k` of the corners of the cube, together with the
observation that `r^{j-c}(c)` depends only on the parities of `j`; with that identity the
denominator estimate `le_periodicGibbs_univ` and the chain below it go through verbatim with
`G_δ(Φ)` replaced by `R`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {N d : ℕ} [NeZero N]

/-! ### Georgii (18.3): the pattern set of a configuration -/

variable (E) in
/-- **Georgii (18.3)** on the torus `Λ = (ℤ/2N)^d`.  `V(G, ω)` is the set of sites `i` such that
the spins of `ω` in the elementary cube `C(i)` show the pattern `G`, read through the iterated
reflection `r^i` of (17.14): `(θ_{-i}ω)_C ∈ r^i G`, equivalently `r^i (ω_{C(i)}) ∈ G` since
`r^i` is an involution. -/
def torusPattern (G : Set ((Fin d → Fin 2) → E)) (ω : (Fin d → ZMod (2 * N)) → E) :
    Set (Fin d → ZMod (2 * N)) :=
  {i | tauPow (cubeRefl E) i (cubeView ω i) ∈ G}

variable {G : Set ((Fin d → Fin 2) → E)}

omit [NeZero N] in
lemma mem_torusPattern {ω : (Fin d → ZMod (2 * N)) → E} {i : Fin d → ZMod (2 * N)} :
    i ∈ torusPattern E G ω ↔ tauPow (cubeRefl E) i (cubeView ω i) ∈ G := Iff.rfl

omit [NeZero N] in
/-- For an `r`-symmetric pattern the reflections drop out of (18.3). -/
lemma mem_torusPattern_of_isRSymmetric (hG : IsRSymmetric E G)
    (ω : (Fin d → ZMod (2 * N)) → E) (i : Fin d → ZMod (2 * N)) :
    i ∈ torusPattern E G ω ↔ cubeView ω i ∈ G :=
  Set.ext_iff.1 (hG.preimage_tauPow i) (cubeView ω i)

/-! ### The elementary cube at a site, and the even sublattice -/

lemma natCast_lt_two_mul {a : ℕ} (ha : a < 2 * N) : ((a : ZMod (2 * N))).val = a := by
  have : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  exact ZMod.val_cast_of_lt ha

/-- The `2^d` corners of an elementary cube of the torus are distinct: this is where `2N ≥ 2`
is used. -/
lemma injective_cubeCast : Function.Injective (cubeCast N (d := d)) := by
  intro c c' h
  funext k
  have hk := congrFun h k
  simp only [cubeCast] at hk
  have hb : (c k : ℕ) < 2 * N := lt_of_lt_of_le (c k).isLt (by have := NeZero.ne N; omega)
  have hb' : (c' k : ℕ) < 2 * N := lt_of_lt_of_le (c' k).isLt (by have := NeZero.ne N; omega)
  have := congrArg ZMod.val hk
  rw [natCast_lt_two_mul hb, natCast_lt_two_mul hb'] at this
  exact Fin.val_injective this

lemma injective_add_cubeCast (i : Fin d → ZMod (2 * N)) :
    Function.Injective fun c : Fin d → Fin 2 ↦ i + cubeCast N c :=
  fun _ _ h ↦ injective_cubeCast (add_right_injective i h)

/-- **The spins in one elementary cube are `λ^C`-distributed.**  The corners of `C(i)` are
`2^d` distinct sites of the torus, so `ω ↦ ω_{C(i)}` pushes `λ^Λ` forward to `λ^C`. -/
theorem map_cubeView_pi (ν : Measure E) [IsProbabilityMeasure ν] (i : Fin d → ZMod (2 * N)) :
    (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν).map (fun ω ↦ cubeView ω i)
      = cubeMeasure d ν :=
  map_comp_pi_of_injective ν (injective_add_cubeCast i)

/-- The doubling map `ℤ/N → ℤ/2N`, whose image is the even sublattice. -/
def evenCast (N : ℕ) (v : ZMod N) : ZMod (2 * N) := ((2 * v.val : ℕ) : ZMod (2 * N))

/-- The even sites `2j` of the torus: the elementary cubes based at them tile the torus. -/
def evenSite (N : ℕ) (j : Fin d → ZMod N) : Fin d → ZMod (2 * N) := fun k ↦ evenCast N (j k)

omit [NeZero N] in
lemma evenCast_add_natCast (v : ZMod N) (b : Fin 2) :
    evenCast N v + ((b : ℕ) : ZMod (2 * N)) = ((2 * v.val + (b : ℕ) : ℕ) : ZMod (2 * N)) := by
  rw [evenCast, Nat.cast_add]

/-- Every site of the torus is uniquely `2 v + b` with `v ∈ ℤ/N` and `b ∈ {0, 1}`. -/
lemma injective_evenCast_add :
    Function.Injective fun p : ZMod N × Fin 2 ↦ evenCast N p.1 + ((p.2 : ℕ) : ZMod (2 * N)) := by
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  simp only [evenCast_add_natCast] at h
  have hv : v.val < N := ZMod.val_lt v
  have hv' : v'.val < N := ZMod.val_lt v'
  have hb : (b : ℕ) < 2 := b.isLt
  have hb' : (b' : ℕ) < 2 := b'.isLt
  have h1 : 2 * v.val + (b : ℕ) < 2 * N := by omega
  have h2 : 2 * v'.val + (b' : ℕ) < 2 * N := by omega
  have := congrArg ZMod.val h
  rw [natCast_lt_two_mul h1, natCast_lt_two_mul h2] at this
  have hvv : v.val = v'.val := by omega
  have hbb : (b : ℕ) = (b' : ℕ) := by omega
  exact Prod.ext (ZMod.val_injective _ hvv) (Fin.val_injective hbb)

/-- The elementary cubes based at the even sites tile the torus. -/
lemma injective_evenSite_add_cubeCast :
    Function.Injective fun p : (Fin d → ZMod N) × (Fin d → Fin 2) ↦
      evenSite N p.1 + cubeCast N p.2 := by
  rintro ⟨j, c⟩ ⟨j', c'⟩ h
  have hk : ∀ k, (j k, c k) = (j' k, c' k) := by
    intro k
    refine injective_evenCast_add ?_
    exact congrFun h k
  exact Prod.ext (funext fun k ↦ (Prod.ext_iff.1 (hk k)).1)
    (funext fun k ↦ (Prod.ext_iff.1 (hk k)).2)

/-- **Georgii's `∏'` in the proof of (18.10).**  The configurations of the `N^d` elementary
cubes based at the even sites of the torus are independent copies of a `λ^C`-distributed
configuration, because those cubes tile the torus. -/
theorem pi_forall_cubeView_evenSite (ν : Measure E) [IsProbabilityMeasure ν]
    {B : Set ((Fin d → Fin 2) → E)} (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)
        {ω | ∀ j : Fin d → ZMod N, cubeView ω (evenSite N j) ∈ B}
      = cubeMeasure d ν B ^ (N ^ d) := by
  have h := pi_setOf_forall_comp_mem (κ := Fin d → ZMod (2 * N)) (J := Fin d → ZMod N)
    (ι := Fin d → Fin 2) ν (g := fun j c ↦ evenSite N j + cubeCast N c)
    injective_evenSite_add_cubeCast (B := fun _ ↦ B) fun _ ↦ hB
  have hset : {ω : (Fin d → ZMod (2 * N)) → E |
        ∀ j : Fin d → ZMod N, cubeView ω (evenSite N j) ∈ B}
      = {ω : (Fin d → ZMod (2 * N)) → E |
        ∀ j : Fin d → ZMod N, (fun c ↦ ω (evenSite N j + cubeCast N c)) ∈ B} := rfl
  rw [hset, h, Finset.prod_const, Finset.card_univ, Fintype.card_pi]
  simp [ZMod.card]

/-! ### Indicators of cube patterns -/

/-- The `{0, 1}`-valued indicator of a set of cube configurations: the function `f = 1_{E^C∖G}`
of Georgii's proof of (18.10). -/
def cubeInd (B : Set ((Fin d → Fin 2) → E)) : ((Fin d → Fin 2) → E) → ℝ := B.indicator 1

omit [MeasurableSpace E] in
open scoped Classical in
lemma cubeInd_apply (B : Set ((Fin d → Fin 2) → E)) (ζ : (Fin d → Fin 2) → E) :
    cubeInd B ζ = if ζ ∈ B then 1 else 0 := by
  classical
  rw [cubeInd, Set.indicator_apply]
  exact if_congr Iff.rfl rfl rfl

lemma measurable_cubeInd {B : Set ((Fin d → Fin 2) → E)} (hB : MeasurableSet B) :
    Measurable (cubeInd B) := measurable_one.indicator hB

omit [MeasurableSpace E] in
lemma abs_cubeInd_le_one (B : Set ((Fin d → Fin 2) → E)) (ζ : (Fin d → Fin 2) → E) :
    |cubeInd B ζ| ≤ 1 := by
  classical
  rw [cubeInd_apply]
  split_ifs <;> simp

omit [NeZero N] in
/-- An `r`-symmetric pattern is invisible to the iterated reflections `r^i`. -/
lemma cubeInd_tauPow (B : Set ((Fin d → Fin 2) → E)) (hBsym : IsRSymmetric E B)
    (i : Fin d → ZMod (2 * N)) (ζ : (Fin d → Fin 2) → E) :
    cubeInd B (tauPow (cubeRefl E) i ζ) = cubeInd B ζ := by
  classical
  have hmem : tauPow (cubeRefl E) i ζ ∈ B ↔ ζ ∈ B :=
    Set.ext_iff.1 (hBsym.preimage_tauPow (N := N) i) ζ
  rw [cubeInd_apply, cubeInd_apply]
  exact if_congr hmem rfl rfl

omit [NeZero N] [MeasurableSpace E] in
/-- The product of the indicators of a pattern over a finite set of cubes is the indicator of the
event that every one of those cubes shows the pattern. -/
lemma prod_cubeInd_cubeView (B : Set ((Fin d → Fin 2) → E))
    (s : Finset (Fin d → ZMod (2 * N))) (ω : (Fin d → ZMod (2 * N)) → E) :
    ∏ i ∈ s, cubeInd B (cubeView ω i)
      = Set.indicator {ω' | ∀ i ∈ s, cubeView ω' i ∈ B} (fun _ ↦ (1 : ℝ)) ω := by
  classical
  rw [Set.indicator_apply]
  simp only [cubeInd_apply]
  rw [Finset.prod_boole]
  exact if_congr Iff.rfl rfl rfl

omit [NeZero N] in
lemma measurableSet_forall_cubeView_mem {B : Set ((Fin d → Fin 2) → E)} (hB : MeasurableSet B)
    (s : Finset (Fin d → ZMod (2 * N))) :
    MeasurableSet {ω : (Fin d → ZMod (2 * N)) → E | ∀ i ∈ s, cubeView ω i ∈ B} := by
  have hrw : {ω : (Fin d → ZMod (2 * N)) → E | ∀ i ∈ s, cubeView ω i ∈ B}
      = ⋂ i ∈ s, (fun ω ↦ cubeView ω i) ⁻¹' B := by ext ω; simp
  rw [hrw]
  exact MeasurableSet.biInter s.countable_toSet fun i _ ↦
    hB.preimage ((measurable_pi_apply i).comp measurable_cubeView)

/-- The integral of the indicator of a measurable set is its measure. -/
lemma integral_indicator_one_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    ∫ ω, Set.indicator s (fun _ ↦ (1 : ℝ)) ω ∂μ = (μ s).toReal := by
  rw [integral_indicator_const _ hs, smul_eq_mul, mul_one]
  rfl

/-! ### The chessboard estimate for the product measure `λ^Λ` -/

lemma measurePreserving_shift_pi (ν : Measure E) [SigmaFinite ν] (j : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift E j).toFun (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
  rw [shift_eq_siteEquiv]
  exact measurePreserving_siteEquiv_pi (Equiv.addRight j) ν

lemma measurePreserving_hatReflection_pi (ν : Measure E) [SigmaFinite ν] (k : Fin d) :
    MeasurePreserving (hatReflection E N k).toFun (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) :=
  measurePreserving_siteEquiv_pi (hatReflAt N k) ν

/-- **Georgii, Corollary (17.17) applied to `λ^Λ`** — the last display of the proof of (18.10):
for an `r`-symmetric pattern `B`, the probability that *every* elementary cube of the torus shows
the pattern `B` is at least `λ^C(B)^{|Λ|}`. -/
theorem pow_le_pi_forall_cubeView (ν : Measure E) [IsProbabilityMeasure ν]
    {B : Set ((Fin (d + 1) → Fin 2) → E)} (hB : MeasurableSet B) (hBsym : IsRSymmetric E B) :
    cubeMeasure (d + 1) ν B ^ ((2 * N) ^ (d + 1))
      ≤ (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν)
          {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ B} := by
  classical
  set μ : Measure ((Fin (d + 1) → ZMod (2 * N)) → E) := Measure.pi fun _ ↦ ν with hμ
  have hμprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set f : (Fin (d + 1) → ZMod (2 * N)) → ((Fin (d + 1) → Fin 2) → E) → ℝ :=
    fun i ↦ if i = 0 then cubeInd B else fun _ ↦ 1 with hf
  have hf0 : f 0 = cubeInd B := by rw [hf]; simp
  have hfne : ∀ i ≠ (0 : Fin (d + 1) → ZMod (2 * N)), f i = fun _ ↦ 1 := by
    intro i hi
    rw [hf]
    simp [hi]
  have hfm : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : i = 0
    · rw [hi, hf0]; exact measurable_cubeInd hB
    · rw [hfne i hi]; exact measurable_const
  have hfC : ∀ i ζ, |f i ζ| ≤ 1 := by
    intro i ζ
    by_cases hi : i = 0
    · rw [hi, hf0]; exact abs_cubeInd_le_one B ζ
    · rw [hfne i hi]; simp
  have hcb := abs_integral_prod_cubeView_pow_le (μ := μ) (measurePreserving_shift_pi ν)
    (measurePreserving_hatReflection_pi ν)
    (fun k ↦ isReflectionPositive_hatReflection_pi ν k) hfm hfC
  have hmeas0 : Measurable fun ω : (Fin (d + 1) → ZMod (2 * N)) → E ↦ cubeView ω 0 :=
    (measurable_pi_apply 0).comp measurable_cubeView
  -- the left-hand side of the chessboard estimate is `λ^C(B)`
  have hL : ∫ ω, ∏ i, f i (cubeView ω i) ∂μ = (cubeMeasure (d + 1) ν B).toReal := by
    have hprod : (fun ω : (Fin (d + 1) → ZMod (2 * N)) → E ↦ ∏ i, f i (cubeView ω i))
        = Set.indicator ((fun ω' : (Fin (d + 1) → ZMod (2 * N)) → E ↦ cubeView ω' 0) ⁻¹' B)
            (fun _ ↦ (1 : ℝ)) := by
      funext ω
      rw [Finset.prod_eq_single 0 (fun i _ hi ↦ by rw [hfne i hi])
        (fun h ↦ absurd (Finset.mem_univ _) h), hf0]
      rfl
    rw [hprod, integral_indicator_one_eq μ (hB.preimage hmeas0),
      ← Measure.map_apply hmeas0 hB, hμ, map_cubeView_pi ν 0]
  -- the right-hand side is the probability that every cube shows `B`
  have hR : ∏ j, (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i)) ∂μ)
      = (μ {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))),
          cubeView ω i ∈ B}).toReal := by
    have hone : ∀ j ≠ (0 : Fin (d + 1) → ZMod (2 * N)),
        (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i)) ∂μ) = 1 := by
      intro j hj
      rw [hfne j hj]
      simp
    have hzero : (∫ ω, ∏ i, f 0 (tauPow (cubeRefl E) i (cubeView ω i)) ∂μ)
        = (μ {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))),
            cubeView ω i ∈ B}).toReal := by
      rw [hf0]
      simp only [cubeInd_tauPow B hBsym, prod_cubeInd_cubeView B Finset.univ]
      exact integral_indicator_one_eq μ (measurableSet_forall_cubeView_mem hB Finset.univ)
    rw [Finset.prod_eq_single 0 (fun j _ hj ↦ hone j hj)
      (fun h ↦ absurd (Finset.mem_univ _) h), hzero]
  rw [hL, hR, abs_of_nonneg ENNReal.toReal_nonneg] at hcb
  refine (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top (measure_ne_top _ _))
    (measure_ne_top _ _)).1 ?_
  rw [ENNReal.toReal_pow]
  exact hcb

/-! ### Georgii Lemma (18.10) on the torus -/

section Ten

variable {φ : ((Fin (d + 1) → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {G : Set ((Fin (d + 1) → Fin 2) → E)}

lemma isRSymmetric_compl (hGsym : IsRSymmetric E G) : IsRSymmetric E Gᶜ := by
  intro k
  rw [Set.preimage_compl, hGsym k]

lemma card_torus : Fintype.card (Fin (d + 1) → ZMod (2 * N)) = (2 * N) ^ (d + 1) := by
  have : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  simp [Fintype.card_pi, ZMod.card]

/-- Almost every configuration has energy at least `λ-inf_{E^C∖G} Φ_C` on every elementary cube
that does not show the pattern `G`. -/
lemma ae_energyOutside_le (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hG : MeasurableSet G) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν),
      ∀ i, cubeView ω i ∉ G → energyOutside φ ν G ≤ φ (cubeView ω i) := by
  set Bad : Set ((Fin (d + 1) → Fin 2) → E) := {ζ | φ ζ < energyOutside φ ν G} ∩ Gᶜ with hBad
  have hBadmeas : MeasurableSet Bad :=
    (measurableSet_lt hφ measurable_const).inter hG.compl
  have hBadnull : cubeMeasure (d + 1) ν Bad = 0 := by
    have hb := meas_lt_essInf (μ := (cubeMeasure (d + 1) ν).restrict Gᶜ) (f := φ)
      (isBoundedUnder_ge_ae (Filter.Eventually.of_forall hM))
    rwa [← energyOutside, Measure.restrict_apply' hG.compl] at hb
  have hnull : ∀ i : Fin (d + 1) → ZMod (2 * N),
      (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν) {ω | cubeView ω i ∈ Bad} = 0 := by
    intro i
    have hmeasi : Measurable fun ω : (Fin (d + 1) → ZMod (2 * N)) → E ↦ cubeView ω i :=
      (measurable_pi_apply i).comp measurable_cubeView
    rw [show {ω : (Fin (d + 1) → ZMod (2 * N)) → E | cubeView ω i ∈ Bad}
      = (fun ω ↦ cubeView ω i) ⁻¹' Bad from rfl, ← Measure.map_apply hmeasi hBadmeas,
      map_cubeView_pi ν i]
    exact hBadnull
  rw [ae_iff]
  refine measure_mono_null (fun ω hω ↦ ?_) (measure_iUnion_null (ι := Fin (d + 1) → ZMod (2 * N))
    fun i ↦ hnull i)
  simp only [Set.mem_ofPred_eq, not_forall] at hω
  obtain ⟨i, hi, hlt⟩ := hω
  exact Set.mem_iUnion.2 ⟨i, ⟨not_le.1 hlt, hi⟩⟩

/-- **The numerator estimate in Georgii's proof of (18.10).**  The unnormalised periodic Gibbs
measure of the event that no elementary cube shows the pattern `G` is at most
`exp[-|Λ| λ-inf_{E^C∖G} Φ_C] · λ^C(E^C∖G)^{N^d}`. -/
theorem periodicGibbs_forall_notMem_le (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hG : MeasurableSet G) :
    periodicGibbs E φ ν (N := N)
        {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ}
      ≤ ENNReal.ofReal
          (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * energyOutside φ ν G)))
        * cubeMeasure (d + 1) ν Gᶜ ^ (N ^ (d + 1)) := by
  classical
  set A : Set ((Fin (d + 1) → ZMod (2 * N)) → E) :=
    {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ} with hA
  have hAmeas : MeasurableSet A := measurableSet_forall_cubeView_mem hG.compl Finset.univ
  rw [periodicGibbs, withDensity_apply _ hAmeas]
  have hbound : ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-periodicHamiltonian E φ ω))
        ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν)
      ≤ ENNReal.ofReal (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * energyOutside φ ν G)))
        * (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν) A := by
    rw [← setLIntegral_const A
      (ENNReal.ofReal (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * energyOutside φ ν G))))]
    refine setLIntegral_mono_ae (by fun_prop) ?_
    filter_upwards [ae_energyOutside_le (N := N) hφ hM hG] with ω hω hωA
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
    have hsum : ((2 * N) ^ (d + 1) : ℕ) • energyOutside φ ν G
        ≤ ∑ i, φ (cubeView ω i) := by
      rw [← card_torus (N := N) (d := d), ← Finset.card_univ]
      exact Finset.card_nsmul_le_sum _ _ _ fun i _ ↦ hω i (hωA i (Finset.mem_univ i))
    rwa [nsmul_eq_mul] at hsum
  refine hbound.trans (mul_le_mul' le_rfl ?_)
  rw [← pi_forall_cubeView_evenSite (N := N) ν hG.compl]
  exact measure_mono fun ω hω j ↦ hω _ (Finset.mem_univ _)

/-- **The denominator estimate in Georgii's proof of (18.10).**  The normalisation constant
`°Z_Λ^Φ` is at least `exp[-|Λ|(m_Φ + δ)] λ^C(G_δ(Φ))^{|Λ|}`. -/
theorem le_periodicGibbs_univ (hφ : Measurable φ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ) {δ : ℝ} :
    ENNReal.ofReal
        (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * (localGroundEnergy φ ν + δ))))
      * cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1))
    ≤ periodicGibbs E φ ν (N := N) Set.univ := by
  classical
  set Gδ := localGroundStates φ ν δ with hGδ
  have hGδmeas : MeasurableSet Gδ := measurableSet_localGroundStates hφ δ
  set A : Set ((Fin (d + 1) → ZMod (2 * N)) → E) :=
    {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gδ} with hA
  have hAmeas : MeasurableSet A := measurableSet_forall_cubeView_mem hGδmeas Finset.univ
  rw [periodicGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine le_trans ?_ (setLIntegral_le_lintegral (μ := Measure.pi
    fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν) A _)
  refine le_trans (mul_le_mul' le_rfl (pow_le_pi_forall_cubeView (N := N) ν hGδmeas
    (isRSymmetric_localGroundStates hφk δ))) ?_
  rw [← setLIntegral_const A
    (ENNReal.ofReal (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * (localGroundEnergy φ ν + δ)))))]
  refine setLIntegral_mono_ae (measurable_periodicGibbsDensity hφ).aemeasurable
    (Filter.Eventually.of_forall fun ω hωA ↦ ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg ?_))
  have hsum : ∑ i, φ (cubeView ω i)
      ≤ ((2 * N) ^ (d + 1) : ℕ) • (localGroundEnergy φ ν + δ) := by
    rw [← card_torus (N := N) (d := d), ← Finset.card_univ]
    exact Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ hωA i (Finset.mem_univ i)
  rwa [nsmul_eq_mul] at hsum

omit [NeZero N] [IsProbabilityMeasure ν] in
/-- The `|Λ|`-th power of `t_δ(G, Φ)`, expanded. -/
theorem patternWeightAt_pow (δ : ℝ) :
    patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1))
      = ENNReal.ofReal (Real.exp (((2 * N) ^ (d + 1) : ℕ)
            * (localGroundEnergy φ ν - energyOutside φ ν G + δ)))
        * cubeMeasure (d + 1) ν Gᶜ ^ (N ^ (d + 1))
        * (cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1)))⁻¹ := by
  set n : ℕ := (2 * N) ^ (d + 1) with hn
  have hxp : (cubeMeasure (d + 1) ν Gᶜ ^ ((2 ^ (d + 1) : ℝ))⁻¹) ^ n
      = cubeMeasure (d + 1) ν Gᶜ ^ (N ^ (d + 1)) := by
    rw [← ENNReal.rpow_natCast (cubeMeasure (d + 1) ν Gᶜ ^ ((2 ^ (d + 1) : ℝ))⁻¹) n,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast (cubeMeasure (d + 1) ν Gᶜ) (N ^ (d + 1))]
    congr 1
    rw [hn]
    push_cast
    rw [mul_pow]
    field_simp
  have hexp : ENNReal.ofReal (Real.exp (localGroundEnergy φ ν - energyOutside φ ν G)) ^ n
        * ENNReal.ofReal (Real.exp δ) ^ n
      = ENNReal.ofReal (Real.exp ((n : ℕ) * (localGroundEnergy φ ν - energyOutside φ ν G + δ)))
      := by
    rw [← ENNReal.ofReal_pow (Real.exp_nonneg _), ← ENNReal.ofReal_pow (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _), ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    ring
  rw [patternWeightAt, div_eq_mul_inv, mul_pow, mul_pow, mul_pow, ENNReal.inv_pow, hxp]
  rw [← hexp]
  ring

/-- **Georgii's `t_Λ ≤ t(G, Φ)`.**  The Gibbs distribution with periodic boundary condition of
the event that *no* elementary cube of the torus shows the pattern `G` is at most
`t_δ(G, Φ)^{|Λ|}`, for every `δ > 0`. -/
theorem periodicGibbsDist_forall_mem_compl_le (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ) (hG : MeasurableSet G)
    {δ : ℝ} (hδ : 0 < δ) :
    periodicGibbsDist E φ ν (N := N)
        {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ}
      ≤ patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1)) := by
  have hfin := isFiniteMeasure_periodicGibbs (N := N) (d := d + 1) (ν := ν) hM
  have hy0 : 0 < cubeMeasure (d + 1) ν (localGroundStates φ ν δ) :=
    measure_localGroundStates_pos (ν := ν) hM hδ
  have hytop : cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ≠ ∞ := measure_ne_top _ _
  have hQ := le_periodicGibbs_univ (N := N) (ν := ν) hφ hφk (δ := δ)
  have hQpos : (0 : ℝ≥0∞) < ENNReal.ofReal
      (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * (localGroundEnergy φ ν + δ))))
      * cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1)) :=
    pos_iff_ne_zero.2 (mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (pow_ne_zero _ hy0.ne'))
  have hZ0 : periodicGibbs E φ ν (N := N) Set.univ ≠ 0 := (hQpos.trans_le hQ).ne'
  have hZtop : periodicGibbs E φ ν (N := N) Set.univ ≠ ∞ := measure_ne_top _ _
  -- the numerator/denominator identity
  have hYY : cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1))
      * (cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1)))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (pow_ne_zero _ hy0.ne') (ENNReal.pow_ne_top hytop)
  have key : ∀ A B X Y Yi : ℝ≥0∞, Y * Yi = 1 → (A * Y) * (B * X * Yi) = (A * B) * X := by
    intro A B X Y Yi h
    calc (A * Y) * (B * X * Yi) = (A * B) * X * (Y * Yi) := by ring
      _ = (A * B) * X := by rw [h, mul_one]
  have hid : ENNReal.ofReal
        (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * energyOutside φ ν G)))
      * cubeMeasure (d + 1) ν Gᶜ ^ (N ^ (d + 1))
      = (ENNReal.ofReal
            (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * (localGroundEnergy φ ν + δ))))
          * cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1)))
        * patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1)) := by
    rw [patternWeightAt_pow, key _ _ _ _ _ hYY]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    ring_nf
  -- assemble
  rw [periodicGibbsDist, Measure.smul_apply, smul_eq_mul]
  calc (periodicGibbs E φ ν (N := N) Set.univ)⁻¹ * periodicGibbs E φ ν (N := N)
        {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ}
      ≤ (periodicGibbs E φ ν (N := N) Set.univ)⁻¹
        * (ENNReal.ofReal
              (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * energyOutside φ ν G)))
            * cubeMeasure (d + 1) ν Gᶜ ^ (N ^ (d + 1))) :=
        mul_le_mul' le_rfl (periodicGibbs_forall_notMem_le hφ hM hG)
    _ = ((periodicGibbs E φ ν (N := N) Set.univ)⁻¹
          * (ENNReal.ofReal
              (Real.exp (-(((2 * N) ^ (d + 1) : ℕ) * (localGroundEnergy φ ν + δ))))
            * cubeMeasure (d + 1) ν (localGroundStates φ ν δ) ^ ((2 * N) ^ (d + 1))))
        * patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1)) := by rw [hid]; ring
    _ ≤ ((periodicGibbs E φ ν (N := N) Set.univ)⁻¹ * periodicGibbs E φ ν (N := N) Set.univ)
        * patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1)) :=
        mul_le_mul' (mul_le_mul' le_rfl hQ) le_rfl
    _ = patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1)) := by
        rw [ENNReal.inv_mul_cancel hZ0 hZtop, one_mul]

/-- **The chessboard step in Georgii's proof of (18.10).**  Corollary (17.17) applied to
`°γ_Λ^Φ` with the family `f_i = 1_{E^C∖G}` for `i ∈ D` and `f_i = 1` otherwise. -/
theorem periodicGibbsDist_pow_le_pow (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ) (hG : MeasurableSet G)
    (hGsym : IsRSymmetric E G) (D : Finset (Fin (d + 1) → ZMod (2 * N))) :
    periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ Gᶜ} ^ ((2 * N) ^ (d + 1))
      ≤ periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ}
            ^ D.card := by
  classical
  have hprob := isProbabilityMeasure_periodicGibbsDist (N := N) (d := d + 1) (ν := ν)
    (IsProbabilityMeasure.ne_zero ν) hφ hM
  set f : (Fin (d + 1) → ZMod (2 * N)) → ((Fin (d + 1) → Fin 2) → E) → ℝ :=
    fun i ↦ if i ∈ D then cubeInd Gᶜ else fun _ ↦ 1 with hf
  have hfD : ∀ i ∈ D, f i = cubeInd Gᶜ := fun i hi ↦ by rw [hf]; simp [hi]
  have hfout : ∀ i ∉ D, f i = fun _ ↦ 1 := fun i hi ↦ by rw [hf]; simp [hi]
  have hfm : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : i ∈ D
    · rw [hfD i hi]; exact measurable_cubeInd hG.compl
    · rw [hfout i hi]; exact measurable_const
  have hfC : ∀ i ζ, |f i ζ| ≤ 1 := by
    intro i ζ
    by_cases hi : i ∈ D
    · rw [hfD i hi]; exact abs_cubeInd_le_one _ ζ
    · rw [hfout i hi]; simp
  have hcb := abs_integral_prod_cubeView_pow_le_periodicGibbsDist (N := N) (d := d)
    (IsProbabilityMeasure.ne_zero ν) hφ hM hφk hfm hfC
  have hL : ∫ ω, ∏ i, f i (cubeView ω i) ∂(periodicGibbsDist E φ ν (N := N))
      = (periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ Gᶜ}).toReal := by
    have hprodeq : (fun ω : (Fin (d + 1) → ZMod (2 * N)) → E ↦ ∏ i, f i (cubeView ω i))
        = Set.indicator {ω | ∀ i ∈ D, cubeView ω i ∈ Gᶜ} (fun _ ↦ (1 : ℝ)) := by
      funext ω
      rw [← prod_cubeInd_cubeView Gᶜ D ω,
        ← Finset.prod_subset (Finset.subset_univ D) (fun i _ hi ↦ by rw [hfout i hi])]
      exact Finset.prod_congr rfl fun i hi ↦ by rw [hfD i hi]
    rw [hprodeq, integral_indicator_one_eq _ (measurableSet_forall_cubeView_mem hG.compl D)]
  have hR : ∏ j, (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
        ∂(periodicGibbsDist E φ ν (N := N)))
      = (periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))),
            cubeView ω i ∈ Gᶜ}).toReal ^ D.card := by
    have hin : ∀ j ∈ D, (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
          ∂(periodicGibbsDist E φ ν (N := N)))
        = (periodicGibbsDist E φ ν (N := N)
            {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))),
              cubeView ω i ∈ Gᶜ}).toReal := by
      intro j hj
      rw [hfD j hj]
      simp only [cubeInd_tauPow Gᶜ (isRSymmetric_compl hGsym),
        prod_cubeInd_cubeView Gᶜ Finset.univ]
      exact integral_indicator_one_eq _ (measurableSet_forall_cubeView_mem hG.compl Finset.univ)
    have hout : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), j ∉ D →
        (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
          ∂(periodicGibbsDist E φ ν (N := N))) = 1 := by
      intro j _ hj
      rw [hfout j hj]
      simp
    rw [← Finset.prod_subset (Finset.subset_univ D) hout, Finset.prod_congr rfl hin,
      Finset.prod_const]
  rw [hL, hR, abs_of_nonneg ENNReal.toReal_nonneg] at hcb
  refine (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top (measure_ne_top _ _))
    (ENNReal.pow_ne_top (measure_ne_top _ _))).1 ?_
  rw [ENNReal.toReal_pow, ENNReal.toReal_pow]
  exact hcb

/-- **Georgii, Lemma (18.10)** on the torus, at a fixed `δ > 0`: for an `r`-symmetric pattern
`G` and a finite set `D` of sites, the Gibbs distribution with periodic boundary condition of
the event `D ∩ V(G, ·) = ∅` is at most `t_δ(G, Φ)^{|D|}`. -/
theorem periodicGibbsDist_forall_notMem_torusPattern_le (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G) {δ : ℝ} (hδ : 0 < δ)
    (D : Finset (Fin (d + 1) → ZMod (2 * N))) :
    periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, i ∉ torusPattern E G ω}
      ≤ patternWeightAt φ ν G δ ^ D.card := by
  have hn : (2 * N) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by have := NeZero.ne N; omega)
  have hset : {ω : (Fin (d + 1) → ZMod (2 * N)) → E | ∀ i ∈ D, i ∉ torusPattern E G ω}
      = {ω | ∀ i ∈ D, cubeView ω i ∈ Gᶜ} := by
    ext ω
    exact forall_congr' fun i ↦ imp_congr_right fun _ ↦
      not_congr (mem_torusPattern_of_isRSymmetric hGsym ω i)
  rw [hset]
  refine ENNReal.le_of_pow_le_pow_left' hn ?_
  calc periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ Gᶜ} ^ ((2 * N) ^ (d + 1))
      ≤ periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), cubeView ω i ∈ Gᶜ}
            ^ D.card := periodicGibbsDist_pow_le_pow hφ hM hφk hG hGsym D
    _ ≤ (patternWeightAt φ ν G δ ^ ((2 * N) ^ (d + 1))) ^ D.card :=
        pow_le_pow_left' (periodicGibbsDist_forall_mem_compl_le hφ hM hφk hG hδ) _
    _ = (patternWeightAt φ ν G δ ^ D.card) ^ ((2 * N) ^ (d + 1)) := by
        rw [← pow_mul, ← pow_mul, mul_comm]

/-- **Georgii, Lemma (18.10)** on the torus:
`°γ_Λ^Φ(D ∩ V(G, ·) = ∅) ≤ t(G, Φ)^{|D|}` for every `r`-symmetric `G ∈ ℰ^C` and every finite set
`D` of sites of the torus. -/
theorem periodicGibbsDist_forall_notMem_torusPattern_le_patternWeight (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G)
    (D : Finset (Fin (d + 1) → ZMod (2 * N))) :
    periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, i ∉ torusPattern E G ω}
      ≤ patternWeight φ ν G ^ D.card := by
  have : Nonempty {r : ℝ // 0 < r} := ⟨⟨1, one_pos⟩⟩
  have hprob := isProbabilityMeasure_periodicGibbsDist (N := N) (d := d + 1) (ν := ν)
    (IsProbabilityMeasure.ne_zero ν) hφ hM
  rcases Nat.eq_zero_or_pos D.card with h0 | h0
  · rw [Finset.card_eq_zero.1 h0]
    simp
  rw [patternWeight_eq_iInf, ENNReal.iInf_pow _ h0.ne']
  exact le_iInf fun δ ↦
    periodicGibbsDist_forall_notMem_torusPattern_le hφ hM hφk hG hGsym δ.2 D

end Ten

end MeasureTheory.GibbsMeasure

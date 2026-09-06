/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.DiscreteSymmetryBreakingExamples

/-!
# Georgii 18.3.1 and 18.3.2: the Ising ferromagnet and antiferromagnet in the plane

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.1 and §18.3.2.  The state space is
`E = {-1, 1}`, realised as `Bool` with the observable `spin` of `GibbsMeasure/Model/Ising.lean`,
and the a priori measure is the uniform measure `uniformSpinMeasure` (Georgii's counting measure,
normalised — see the "Normalisation" section of
`GibbsMeasure/Specification/LocalGroundStates.lean`).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The uniform a priori spin measure charges every point -/

lemma uniformSpinMeasure_singleton (b : Bool) : uniformSpinMeasure {b} = 2⁻¹ := by
  rw [uniformSpinMeasure, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]

lemma uniformSpinMeasure_singleton_ne_zero (b : Bool) : uniformSpinMeasure {b} ≠ 0 := by
  rw [uniformSpinMeasure_singleton]
  simp

/-! ### Georgii (18.27): the Ising ferromagnet -/

section Ferromagnet

variable (d : ℕ)

/-- **Georgii (18.27)**: the `C`-potential of the Ising ferromagnet,
`Φ_C = -∑_{{i,j} ⊆ C, |i-j|=1} σ_i σ_j`, on the state space `E = {-1, 1}` read as `Bool` through
`spin`.  Up to a factor `2` this is the potential (6.8) of Georgii's §6.2, whose phase
transition is Theorem (6.9) (`GibbsMeasure/Model/PhaseTransition.lean`); the conclusion obtained
here through Theorem (18.25) is a slight refinement of it, in that the two Gibbs measures are
random perturbations of the two constant ground states and carry an ocean of `(++)` resp.
`(--)` cubes with probability one. -/
abbrev isingFerroCube : ((Fin d → Fin 2) → Bool) → ℝ :=
  cubeBondSum d fun x y ↦ -(spin x * spin y)

variable {d}

lemma measurable_isingFerroCube : Measurable (isingFerroCube d) := Measurable.of_discrete

/-- **Condition (iii) of Georgii (17.18)** for (18.27). -/
lemma isingFerroCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → Bool) :
    isingFerroCube d (cubeRefl Bool k ζ) = isingFerroCube d ζ :=
  cubeBondSum_cubeRefl _ k ζ

lemma neg_one_le_neg_spin_mul_spin (x y : Bool) : (-1 : ℝ) ≤ -(spin x * spin y) := by
  rw [spin_mul_spin]; split_ifs <;> norm_num

lemma neg_spin_mul_spin_le_one (x y : Bool) : -(spin x * spin y) ≤ 1 := by
  rw [spin_mul_spin]; split_ifs <;> norm_num

/-- **Georgii's `Φ_C ≥ -4`** for `d = 2`; in general `Φ_C ≥ -2^{d-1} d`. -/
lemma neg_four_le_isingFerroCube (ζ : (Fin 2 → Fin 2) → Bool) : -4 ≤ isingFerroCube 2 ζ := by
  have h := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ -(spin x * spin y)) (m := -1) (ζ := ζ)
    fun c c' ↦ neg_one_le_neg_spin_mul_spin _ _
  norm_num at h
  linarith

/-- **Georgii's `|Φ_C| ≤ 4`** for `d = 2`, the first alternative of condition (iv) of (17.18). -/
lemma abs_isingFerroCube_le_four (ζ : (Fin 2 → Fin 2) → Bool) : |isingFerroCube 2 ζ| ≤ 4 := by
  have h := cubeBondSum_le (d := 2) (ψ := fun x y ↦ -(spin x * spin y)) (M := 1) (ζ := ζ)
    fun c c' ↦ neg_spin_mul_spin_le_one _ _
  norm_num at h
  rw [abs_le]
  exact ⟨neg_four_le_isingFerroCube ζ, h⟩

/-- **The bond sum of the unit square** for (18.27), in Georgii's notation `ω = (w z / u v)`. -/
lemma isingFerroCube_two_apply (ζ : (Fin 2 → Fin 2) → Bool) :
    isingFerroCube 2 ζ =
      -(spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 1 0)))
        + -(spin (ζ (sqCorner 0 1)) * spin (ζ (sqCorner 1 1)))
        + -(spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 0 1)))
        + -(spin (ζ (sqCorner 1 0)) * spin (ζ (sqCorner 1 1))) :=
  cubeBondSum_two (fun x y ↦ by rw [mul_comm]) ζ

/-- **Georgii's "`Φ_C` only takes the three values `-4`, `0`, `4`"**: the unit square is an even
cycle, so the number of unsatisfied bonds is even. -/
lemma isingFerroCube_two_values (ζ : (Fin 2 → Fin 2) → Bool) :
    isingFerroCube 2 ζ = -4 ∨ isingFerroCube 2 ζ = 0 ∨ isingFerroCube 2 ζ = 4 := by
  rw [isingFerroCube_two_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin]

/-- **Georgii's local ground states of (18.27) are the two constant configurations `(++)` and
`(--)`.** -/
lemma isingFerroCube_two_eq_neg_four_iff (ζ : (Fin 2 → Fin 2) → Bool) :
    isingFerroCube 2 ζ = -4 ↔ ∃ b : Bool, ζ = fun _ ↦ b := by
  constructor
  · intro h
    refine ⟨ζ (sqCorner 0 0), ?_⟩
    rw [isingFerroCube_two_apply] at h
    have key : ζ (sqCorner 1 0) = ζ (sqCorner 0 0) ∧ ζ (sqCorner 0 1) = ζ (sqCorner 0 0)
        ∧ ζ (sqCorner 1 1) = ζ (sqCorner 0 0) := by
      revert h
      generalize ζ (sqCorner 0 0) = u
      generalize ζ (sqCorner 1 0) = v
      generalize ζ (sqCorner 0 1) = w
      generalize ζ (sqCorner 1 1) = z
      cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin]
    exact funext_sqCorner rfl key.1 key.2.1 key.2.2
  · rintro ⟨b, rfl⟩
    rw [isingFerroCube_two_apply]
    cases b <;> norm_num [spin]

/-- **Georgii's `m_Φ = -4`** for (18.27). -/
lemma localGroundEnergy_isingFerroCube :
    localGroundEnergy (isingFerroCube 2) uniformSpinMeasure = -4 :=
  localGroundEnergy_eq uniformSpinMeasure_singleton_ne_zero neg_four_le_isingFerroCube
    (ζ₀ := fun _ ↦ true) ((isingFerroCube_two_eq_neg_four_iff _).2 ⟨true, rfl⟩)

/-- **Georgii's `G_ε(Φ) = {(++), (--)}` for `0 < ε < 4`** in (18.27). -/
theorem localGroundStates_isingFerroCube {ε : ℝ} (hε : 0 < ε) (hε4 : ε < 4) :
    localGroundStates (isingFerroCube 2) uniformSpinMeasure ε
      = {ζ | ∃ b : Bool, ζ = fun _ ↦ b} := by
  rw [localGroundStates_eq_setOf_le uniformSpinMeasure_singleton_ne_zero
    neg_four_le_isingFerroCube (ζ₀ := fun _ ↦ true)
    ((isingFerroCube_two_eq_neg_four_iff _).2 ⟨true, rfl⟩)]
  ext ζ
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    refine (isingFerroCube_two_eq_neg_four_iff ζ).1 ?_
    rcases isingFerroCube_two_values ζ with h4 | h0 | h4 <;> [exact h4; linarith; linarith]
  · rintro ⟨b, rfl⟩
    rw [(isingFerroCube_two_eq_neg_four_iff _).2 ⟨b, rfl⟩]
    linarith


/-! #### Georgii's partition `{G_+, G_-}` and its symmetries -/

/-- **Georgii's partition of the local ground states of the Ising ferromagnet (18.27)**:
`G_0 = G_+ = {(++)}` and `G_1 = G_- = {(--)}`, the two constant cube configurations. -/
def isingFerroG (n : Fin 2) : Set ((Fin 2 → Fin 2) → Bool) := {fun _ ↦ ![true, false] n}

lemma isingFerroG_zero : isingFerroG 0 = {fun _ ↦ true} := rfl

lemma isingFerroG_one : isingFerroG 1 = {fun _ ↦ false} := rfl

lemma measurableSet_isingFerroG (n : Fin 2) : MeasurableSet (isingFerroG n) :=
  measurableSet_singleton _

lemma isRSymmetric_isingFerroG (n : Fin 2) : IsRSymmetric Bool (isingFerroG n) :=
  isRSymmetric_singleton_const _

/-- **Georgii's "this partition is evidently stable"** for (18.27): the two constant
configurations differ at every corner, in particular on every face of `C`; and `G_ε(Φ)` is
`G_+ ∪ G_-` for `0 < ε < 4`. -/
theorem pairwise_disjoint_faceRestrict_isingFerroG (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict Bool k a '' isingFerroG m)
      (faceRestrict Bool k a '' isingFerroG n) := by
  refine pairwise_disjoint_faceRestrict_singleton
    (ζ := fun n : Fin 2 ↦ fun _ : Fin 2 → Fin 2 ↦ ![true, false] n) fun m n hmn ↦ ?_
  refine ⟨fun _ ↦ a, rfl, ?_⟩
  fin_cases m <;> fin_cases n <;> simp_all

theorem isPStablePartition_isingFerroG :
    IsPStablePartition (isingFerroCube 2) uniformSpinMeasure Set.univ isingFerroG where
  exists_localGroundStates_subset := by
    refine ⟨1, one_pos, ?_⟩
    rw [localGroundStates_isingFerroCube one_pos (by norm_num)]
    rintro ζ ⟨b, rfl⟩
    exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_isingFerroG k a

/-- **Georgii's spin flip `τ : ω ↦ -ω`**, a pure spin transformation (18.21) of `T_{C,λ}`. -/
abbrev isingSpinFlip (d : ℕ) : CubeTransformation Bool d :=
  CubeTransformation.pureSpin fun _ ↦ boolNot

/-- The spin flip belongs to `I_{C,λ}(Φ)` for the Ising ferromagnet (18.27): it preserves the
uniform a priori measure and reverses both spins of every bond. -/
theorem isSymmetry_isingSpinFlip :
    (isingSpinFlip 2).IsSymmetry (isingFerroCube 2) uniformSpinMeasure :=
  CubeTransformation.IsSymmetry.of_apply_onCube isingFerroCube_cubeRefl
    (fun _ ↦ measurePreserving_boolNot_uniformSpinMeasure)
    fun ζ ↦ cubeBondSum_onCube _ (fun c c' _ x y ↦ by
      simp only [CubeTransformation.pureSpin, boolNot_apply, spin_not, neg_mul_neg]) ζ

lemma image_onCube_isingSpinFlip (b : Bool) :
    (isingSpinFlip 2).onCube.toFun '' {fun _ ↦ b} = {fun _ : Fin 2 → Fin 2 ↦ !b} := by
  rw [Set.image_singleton]
  congr 1

/-- **Georgii's "`{G_+, G_-}` is `Φ`-symmetric"** for (18.27): `G_+` and `G_-` are exchanged by
the spin flip `τ`, which belongs to `I_{C,λ}(Φ)`. -/
theorem isPhiSymmetric_isingFerroG :
    IsPhiSymmetric (isingFerroCube 2) uniformSpinMeasure isingFerroG := by
  refine isPhiSymmetric_of_ne isingFerroCube_cubeRefl fun m n hmn ↦
    ⟨isingSpinFlip 2, isSymmetry_isingSpinFlip, ?_⟩
  fin_cases m <;> fin_cases n <;> first
    | exact absurd rfl hmn
    | (change (isingSpinFlip 2).onCube.toFun '' {fun _ ↦ _} = _
       rw [image_onCube_isingSpinFlip]; rfl)

/-- Georgii's rotation `r_0` (18.20) and reflections `r_1, r_2` (17.5) belong to `I_{C,λ}(Φ)` for
every nearest-neighbour cube interaction, being purely spatial. -/
theorem isSymmetry_planeRot_isingFerroCube :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (isingFerroCube 2) uniformSpinMeasure :=
  CubeTransformation.isSymmetry_of_spin_refl isingFerroCube_cubeRefl (fun _ ↦ rfl)
    fun ζ ↦ cubeBondSum_onCube_of_spin_refl _ (fun _ ↦ rfl) ζ

/-- The rotation `r_0` and the reflections `r_k` fix each constant configuration, hence each
member of the partition. -/
lemma image_onCube_of_spin_refl_const {d : ℕ} (τ : CubeTransformation Bool d)
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl Bool) (b : Bool) :
    τ.onCube.toFun '' {fun _ ↦ b} = {fun _ : Fin d → Fin 2 ↦ b} := by
  rw [Set.image_singleton]
  congr 1
  funext c
  rw [CubeTransformation.onCube_toFun_apply, hτ c]
  rfl

lemma image_onCube_planeRot_isingFerroG (n : Fin 2) :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' isingFerroG n
      = isingFerroG n :=
  image_onCube_of_spin_refl_const _ (fun _ ↦ rfl) _

lemma image_onCube_refl_isingFerroG (k : Fin 2) (n : Fin 2) :
    (CubeTransformation.refl (E := Bool) k).onCube.toFun '' isingFerroG n = isingFerroG n :=
  image_onCube_of_spin_refl_const _ (fun _ ↦ rfl) _


lemma localGroundStates_subset_isingFerroG :
    localGroundStates (isingFerroCube 2) uniformSpinMeasure 1 ⊆ ⋃ n, isingFerroG n := by
  rw [localGroundStates_isingFerroCube one_pos (by norm_num)]
  rintro ζ ⟨b, rfl⟩
  exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩

/-! #### Georgii 18.3.1: the conclusion -/

open Peierls in
/-- **Georgii 18.3.1, the Ising ferromagnet (18.27).**  *For sufficiently large `β` there exist
two mutually singular Gibbs measures `μ_+, μ_- ∈ 𝒢_Θ(βΦ)` which are invariant under `r_0, r_1,
r_2` and satisfy `τ(μ_+) = μ_-`, `μ_+(ξ⁰(G_+, ·) ≠ ∅) = 1` and `μ_+(0 ∈ ξ⁰(G_+, ·)) → 1` as
`β → ∞`.*

Here `μ_+ = μ 0` and `μ_- = μ 1`, `G_+ = {(++)}` and `G_- = {(--)}` are `isingFerroG 0` and
`isingFerroG 1`, `τ` is the spin flip `isingSpinFlip`, `r_0` is `CubeTransformation.planeRot`
and `r_1, r_2` are `CubeTransformation.refl k`.  The last assertion is the explicit bound
`1 - 4 z(t(G_ε(Φ), βΦ)) ≤ μ_n(0 ∈ ξ⁰(G_n, ·))` of Comment (18.26)(1); its right-hand side tends
to `1` by Remark (18.9)(4), which is
`eventually_isingFerro_one_sub_le_measure_zero_mem_latticeOceanPart` below.

Everything is `eventually_exists_gibbsMeasure_family` — Theorem (18.25) — at the partition
`isingFerroG`, whose hypotheses are `isPStablePartition_isingFerroG` ("this partition is
evidently stable") and `isPhiSymmetric_isingFerroG` (the spin flip), with the confinement
condition (17.18)(iv) supplied by the bound `|Φ_C| ≤ 4`.

This is Georgii's "slight refinement of Theorem (6.9)"
(`GibbsMeasure/Model/PhaseTransition.lean`): (6.9) produces two distinct Gibbs measures for the
Ising potential (6.8) by the Peierls estimate, while here the two measures are moreover
mutually singular, are shift invariant, are exchanged by the spin flip and are supported on the
configurations carrying an infinite ocean of `(++)` resp. `(--)` unit squares. -/
theorem eventually_exists_isingFerro_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * isingFerroCube 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * isingFerroCube 2 ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → Bool),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec Bool
          (fun ζ ↦ β * isingFerroCube 2 ζ) uniformSpinMeasure hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ),
          MeasurePreserving (shift Bool a).toFun (μ n) (μ n)) ∧
        (∀ n : Fin 2, MeasurePreserving
          ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun (μ n) (μ n)) ∧
        (∀ (n : Fin 2) (k : Fin 2), MeasurePreserving
          ((CubeTransformation.refl (E := Bool) k).onLattice Bool).toFun (μ n) (μ n)) ∧
        (μ 0).map ((isingSpinFlip 2).onLattice Bool).toFun = μ 1 ∧
        (μ 1).map ((isingSpinFlip 2).onLattice Bool).toFun = μ 0 ∧
        (∀ n, μ n {ω | (latticeOceanPart Bool (isingFerroG n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - 4 * Peierls.crossingBound (patternWeight (fun ζ ↦ β * isingFerroCube 2 ζ)
            uniformSpinMeasure (localGroundStates (isingFerroCube 2) uniformSpinMeasure 1))
          ≤ μ n {ω | (0 : Site) ∈ latticeOceanPart Bool (isingFerroG n) ω}) := by
  filter_upwards [eventually_exists_gibbsMeasure_family (E := Bool)
    (φ := isingFerroCube 2) (ν := uniformSpinMeasure) (G := isingFerroG)
    measurable_isingFerroCube neg_four_le_isingFerroCube isingFerroCube_cubeRefl
    (isCubeConfining_univ ⟨4, abs_isingFerroCube_le_four⟩)
    isPStablePartition_isingFerroG isPhiSymmetric_isingFerroG measurableSet_isingFerroG
    one_pos localGroundStates_subset_isingFerroG] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, -, h5, h6, h7, h8, h9⟩ := hβ hφβ hMβ
  have hflip : (isingSpinFlip 2).IsSymmetry (fun ζ ↦ β * isingFerroCube 2 ζ) uniformSpinMeasure :=
    isSymmetry_isingSpinFlip.const_mul isingFerroCube_cubeRefl β
  refine ⟨ρ, h1, h2, h3 (by decide),
    fun n a ↦ h7 n a ((isRSymmetric_isingFerroG n).preimage_tauPow _),
    fun n ↦ h8 n _ (isSymmetry_planeRot_isingFerroCube.const_mul isingFerroCube_cubeRefl β)
      (image_onCube_planeRot_isingFerroG n),
    fun n k ↦ h8 n _ (CubeTransformation.isSymmetry_refl
      (ν := uniformSpinMeasure) (fun k ζ ↦ by rw [isingFerroCube_cubeRefl k ζ]) k)
      (image_onCube_refl_isingFerroG k n),
    h9 0 1 _ hflip ?_, h9 1 0 _ hflip ?_, h5, h6⟩
  · change (isingSpinFlip 2).onCube.toFun '' {fun _ ↦ true} = _
    rw [image_onCube_isingSpinFlip]
    rfl
  · change (isingSpinFlip 2).onCube.toFun '' {fun _ ↦ false} = _
    rw [image_onCube_isingSpinFlip]
    rfl

/-- **Georgii's `μ_+(0 ∈ ξ⁰(G_+, ·)) → 1` as `β → ∞`** for the Ising ferromagnet (18.27), in the
form appropriate to a `β`-dependent family: for every `δ > 0`, all sufficiently large `β` admit
the two Gibbs measures of `eventually_exists_isingFerro_gibbsMeasure_pair` with
`μ_n(0 ∈ ξ⁰(G_n, ·)) ≥ 1 - δ`.  This is Remark (18.9)(4), `t(G_ε(Φ), βΦ) → 0`. -/
theorem eventually_isingFerro_one_sub_le_measure_zero_mem_latticeOceanPart {δ : ℝ≥0∞}
    (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 4 * Peierls.crossingBound (patternWeight
      (fun ζ ↦ β * isingFerroCube 2 ζ) uniformSpinMeasure
      (localGroundStates (isingFerroCube 2) uniformSpinMeasure 1)) ≤ δ := by
  have h := tendsto_crossingBound_patternWeight_localGroundStates
    (ν := uniformSpinMeasure) measurable_isingFerroCube neg_four_le_isingFerroCube one_pos
  have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound (patternWeight
      (fun ζ ↦ β * isingFerroCube 2 ζ) uniformSpinMeasure
      (localGroundStates (isingFerroCube 2) uniformSpinMeasure 1))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
  exact (h4.eventually_lt_const hδ).mono fun β hβ ↦ hβ.le

/-- **Georgii's `|ex 𝒢_Θ(βΦ)| ≥ 2`** for the Ising ferromagnet (18.27) at large `β`: the two
measures of `eventually_exists_isingFerro_gibbsMeasure_pair` are shift invariant — the constant
configurations are `r`-symmetric, so Georgii's `Θ̃` is all of `Θ` — and mutually singular. -/
theorem eventually_two_le_encard_extremePoints_isingFerro :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * isingFerroCube 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * isingFerroCube 2 ζ),
      (2 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec Bool (fun ζ ↦ β * isingFerroCube 2 ζ)
        uniformSpinMeasure hφβ hMβ) (shiftGroup (Fin 2 → ℤ) Bool)).extremePoints ℝ≥0∞).encard :=
  eventually_le_encard_extremePoints (E := Bool) (φ := isingFerroCube 2)
    (ν := uniformSpinMeasure) (G := isingFerroG) measurable_isingFerroCube
    neg_four_le_isingFerroCube isingFerroCube_cubeRefl
    (isCubeConfining_univ ⟨4, abs_isingFerroCube_le_four⟩) isPStablePartition_isingFerroG
    isPhiSymmetric_isingFerroG measurableSet_isingFerroG isRSymmetric_isingFerroG one_pos
    localGroundStates_subset_isingFerroG

end Ferromagnet


/-! ### Georgii (18.28): the Ising antiferromagnet in an external field -/

section Antiferromagnet

variable {d : ℕ}

/-- **Georgii's staggered (chessboard) configurations of the unit cube**: `σ_i = b` when
`i_1 + ⋯ + i_d` is even and `!b` otherwise, i.e. Georgii's `ω^b = ((-1)^{i_1+i_2}b)_{i}` read on
`C`.  Its two values `b = ±1` are the two local ground states of the antiferromagnet (18.28). -/
def staggerCube (b : Bool) (c : Fin d → Fin 2) : Bool := if ∑ k, c k = 0 then b else !b

lemma staggerCube_apply (b : Bool) (c : Fin d → Fin 2) :
    staggerCube b c = if ∑ k, c k = 0 then b else !b := rfl

lemma staggerCube_ne (b : Bool) (c : Fin d → Fin 2) : staggerCube b c ≠ staggerCube (!b) c := by
  rw [staggerCube_apply, staggerCube_apply]
  split_ifs <;> cases b <;> simp

/-- The staggered configuration is exchanged with its partner by a reflection of the cube: the
reflection `r_k` changes the parity of the corner. -/
lemma staggerCube_add_single (b : Bool) (c : Fin d → Fin 2) (k : Fin d) :
    staggerCube b (c + Pi.single k 1) = staggerCube (!b) c := by
  rw [staggerCube_apply, staggerCube_apply, sum_add_single]
  rcases fin_two_eq_zero_or_one (∑ l, c l) with h | h <;> rw [h] <;> simp

/-- A translation of the corners by a corner of even parity fixes both staggered
configurations. -/
lemma staggerCube_add_of_sum_eq_zero {p : Fin d → Fin 2} (hp : ∑ k, p k = 0) (b : Bool)
    (c : Fin d → Fin 2) : staggerCube b (c + p) = staggerCube b c := by
  rw [staggerCube_apply, staggerCube_apply, sum_add, hp, add_zero]

lemma sum_sqCorner (a b : Fin 2) : ∑ k, sqCorner a b k = a + b := by
  simp [Fin.sum_univ_two]

lemma staggerCube_sqCorner (x : Bool) (a b : Fin 2) :
    staggerCube x (sqCorner a b) = if a + b = 0 then x else !x := by
  rw [staggerCube_apply, sum_sqCorner]

@[simp] lemma staggerCube_sqCorner_zero_zero (b : Bool) :
    staggerCube b (sqCorner 0 0) = b := by rw [staggerCube_sqCorner, if_pos (by decide)]

@[simp] lemma staggerCube_sqCorner_one_zero (b : Bool) :
    staggerCube b (sqCorner 1 0) = !b := by rw [staggerCube_sqCorner, if_neg (by decide)]

@[simp] lemma staggerCube_sqCorner_zero_one (b : Bool) :
    staggerCube b (sqCorner 0 1) = !b := by rw [staggerCube_sqCorner, if_neg (by decide)]

@[simp] lemma staggerCube_sqCorner_one_one (b : Bool) :
    staggerCube b (sqCorner 1 1) = b := by rw [staggerCube_sqCorner, if_pos (by decide)]

/-- A configuration of the unit square is staggered exactly when its four corner spins
alternate. -/
lemma exists_eq_staggerCube_iff (ζ : (Fin 2 → Fin 2) → Bool) :
    (∃ b, ζ = staggerCube b) ↔ ζ (sqCorner 1 0) = !ζ (sqCorner 0 0)
      ∧ ζ (sqCorner 0 1) = !ζ (sqCorner 0 0) ∧ ζ (sqCorner 1 1) = ζ (sqCorner 0 0) := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · rintro ⟨h10, h01, h11⟩
    exact ⟨ζ (sqCorner 0 0), funext_sqCorner (by simp) (by simp [h10]) (by simp [h01])
      (by simp [h11])⟩

variable (d) in
/-- **Georgii (18.28)**: the `C`-potential of the Ising antiferromagnet in an external field `h`,
`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} σ_i σ_j - h ∑_{i ∈ C} σ_i`.  Only the sign of the bond term
distinguishes it from the ferromagnet (18.27). -/
abbrev isingAntiCube (h : ℝ) : ((Fin d → Fin 2) → Bool) → ℝ :=
  fun ζ ↦ cubeBondSum d (fun x y ↦ spin x * spin y) ζ - h * cubeSiteSum d spin ζ

variable {h : ℝ}

lemma measurable_isingAntiCube : Measurable (isingAntiCube d h) := Measurable.of_discrete

/-- **Condition (iii) of Georgii (17.18)** for (18.28). -/
lemma isingAntiCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → Bool) :
    isingAntiCube d h (cubeRefl Bool k ζ) = isingAntiCube d h ζ := by
  simp only [isingAntiCube, cubeBondSum_cubeRefl, cubeSiteSum_cubeRefl]

/-- **The bond and field sums of the unit square** for (18.28), in Georgii's notation
`ω = (w z / u v)`. -/
lemma isingAntiCube_two_apply (ζ : (Fin 2 → Fin 2) → Bool) :
    isingAntiCube 2 h ζ =
      spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 1 0))
        + spin (ζ (sqCorner 0 1)) * spin (ζ (sqCorner 1 1))
        + spin (ζ (sqCorner 0 0)) * spin (ζ (sqCorner 0 1))
        + spin (ζ (sqCorner 1 0)) * spin (ζ (sqCorner 1 1))
        - h * (spin (ζ (sqCorner 0 0)) + spin (ζ (sqCorner 1 0))
          + spin (ζ (sqCorner 0 1)) + spin (ζ (sqCorner 1 1))) := by
  rw [isingAntiCube, cubeBondSum_two (fun x y ↦ by rw [mul_comm]) ζ, cubeSiteSum_def,
    sum_univ_cubeCorners]

/-- **Georgii's `Φ_C ≥ -4`** for (18.28) when `|h| < 2`. -/
lemma neg_four_le_isingAntiCube (hh : |h| < 2) (ζ : (Fin 2 → Fin 2) → Bool) :
    -4 ≤ isingAntiCube 2 h ζ := by
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  rw [isingAntiCube_two_apply]
  generalize ζ (sqCorner 0 0) = u
  generalize ζ (sqCorner 1 0) = v
  generalize ζ (sqCorner 0 1) = w
  generalize ζ (sqCorner 1 1) = z
  cases u <;> cases v <;> cases w <;> cases z <;> norm_num [spin] <;> linarith

/-- **Georgii's `Φ_C` attains its minimum `-4` exactly on the two staggered configurations** of
(18.28), when `|h| < 2`. -/
lemma isingAntiCube_two_staggerCube (b : Bool) : isingAntiCube 2 h (staggerCube b) = -4 := by
  rw [isingAntiCube_two_apply]
  simp only [staggerCube_sqCorner_zero_zero, staggerCube_sqCorner_one_zero,
    staggerCube_sqCorner_zero_one, staggerCube_sqCorner_one_one]
  cases b <;> norm_num [spin]

/-- **Georgii's "the next lowest value of `Φ_C` is `-2|h|`"** for (18.28). -/
lemma neg_two_mul_abs_le_isingAntiCube (hh : |h| < 2) {ζ : (Fin 2 → Fin 2) → Bool}
    (hζ : ¬ ∃ b, ζ = staggerCube b) : -2 * |h| ≤ isingAntiCube 2 h ζ := by
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  rw [exists_eq_staggerCube_iff] at hζ
  rw [isingAntiCube_two_apply]
  rcases abs_cases h with ⟨hah, _⟩ | ⟨hah, _⟩ <;> rw [hah] <;>
    revert hζ <;>
    generalize ζ (sqCorner 0 0) = u <;>
    generalize ζ (sqCorner 1 0) = v <;>
    generalize ζ (sqCorner 0 1) = w <;>
    generalize ζ (sqCorner 1 1) = z <;>
    cases u <;> cases v <;> cases w <;> cases z <;> intro hno <;>
    first
      | exact absurd ⟨rfl, rfl, rfl⟩ hno
      | (norm_num [spin]; linarith)
      | norm_num [spin]


lemma neg_one_le_spin_mul_spin (x y : Bool) : (-1 : ℝ) ≤ spin x * spin y := by
  rw [spin_mul_spin]; split_ifs <;> norm_num

lemma spin_mul_spin_le_one (x y : Bool) : spin x * spin y ≤ 1 := by
  rw [spin_mul_spin]; split_ifs <;> norm_num

lemma neg_one_le_spin (x : Bool) : (-1 : ℝ) ≤ spin x := by cases x <;> norm_num [spin]

lemma spin_le_one (x : Bool) : spin x ≤ 1 := by cases x <;> norm_num [spin]

/-- **`|Φ_C| ≤ 4 + 4|h|`** for (18.28), the first alternative of condition (iv) of (17.18). -/
lemma abs_isingAntiCube_le (ζ : (Fin 2 → Fin 2) → Bool) :
    |isingAntiCube 2 h ζ| ≤ 4 + 4 * |h| := by
  have hb1 := cubeBondSum_ge (d := 2) (ψ := fun x y ↦ spin x * spin y) (m := -1) (ζ := ζ)
    fun c c' ↦ neg_one_le_spin_mul_spin _ _
  have hb2 := cubeBondSum_le (d := 2) (ψ := fun x y ↦ spin x * spin y) (M := 1) (ζ := ζ)
    fun c c' ↦ spin_mul_spin_le_one _ _
  have hs1 := cubeSiteSum_ge (d := 2) (v := spin) (m := -1) (ζ := ζ) fun c ↦ neg_one_le_spin _
  have hs2 := cubeSiteSum_le (d := 2) (v := spin) (M := 1) (ζ := ζ) fun c ↦ spin_le_one _
  norm_num at hb1 hb2 hs1 hs2
  have hb : |cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ| ≤ 4 := abs_le.2 ⟨hb1, hb2⟩
  have hs : |cubeSiteSum 2 spin ζ| ≤ 4 := abs_le.2 ⟨hs1, hs2⟩
  have habs : |isingAntiCube 2 h ζ|
      ≤ |cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ| + |h * cubeSiteSum 2 spin ζ| := by
    simpa only [isingAntiCube, sub_eq_add_neg, abs_neg] using
      abs_add_le (cubeBondSum 2 (fun x y ↦ spin x * spin y) ζ) (-(h * cubeSiteSum 2 spin ζ))
  refine habs.trans ?_
  rw [abs_mul]
  have : |h| * |cubeSiteSum 2 spin ζ| ≤ |h| * 4 := by gcongr
  linarith

/-- **Georgii's `m_Φ = -4`** for (18.28) when `|h| < 2`. -/
lemma localGroundEnergy_isingAntiCube (hh : |h| < 2) :
    localGroundEnergy (isingAntiCube 2 h) uniformSpinMeasure = -4 :=
  localGroundEnergy_eq uniformSpinMeasure_singleton_ne_zero (neg_four_le_isingAntiCube hh)
    (ζ₀ := staggerCube true) (isingAntiCube_two_staggerCube true)

/-- **Georgii's `G_ε(Φ) = G_1 ∪ G_2` for `0 < ε < 4 - 2|h|`** in (18.28). -/
theorem localGroundStates_isingAntiCube (hh : |h| < 2) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 4 - 2 * |h|) :
    localGroundStates (isingAntiCube 2 h) uniformSpinMeasure ε
      = {ζ | ∃ b : Bool, ζ = staggerCube b} := by
  rw [localGroundStates_eq_setOf_le uniformSpinMeasure_singleton_ne_zero
    (neg_four_le_isingAntiCube hh) (ζ₀ := staggerCube true) (isingAntiCube_two_staggerCube true)]
  ext ζ
  simp only [Set.mem_ofPred_eq]
  refine ⟨fun hle ↦ ?_, ?_⟩
  · by_contra hno
    have := neg_two_mul_abs_le_isingAntiCube hh hno
    linarith
  · rintro ⟨b, rfl⟩
    rw [isingAntiCube_two_staggerCube]
    linarith

/-! #### Georgii's partition `{G_1, G_2}` of the staggered ground states -/

/-- **Georgii's partition of the local ground states of (18.28)**: the two staggered
configurations, `G_1` carrying `+` on the even sublattice of `C` and `G_2` on the odd one. -/
def isingAntiG (n : Fin 2) : Set ((Fin 2 → Fin 2) → Bool) := {staggerCube (![true, false] n)}

lemma measurableSet_isingAntiG (n : Fin 2) : MeasurableSet (isingAntiG n) :=
  measurableSet_singleton _

lemma localGroundStates_subset_isingAntiG (hh : |h| < 2) {ε : ℝ} (hε : 0 ≤ ε)
    (hε' : ε < 4 - 2 * |h|) :
    localGroundStates (isingAntiCube 2 h) uniformSpinMeasure ε ⊆ ⋃ n, isingAntiG n := by
  rw [localGroundStates_isingAntiCube hh hε hε']
  rintro ζ ⟨b, rfl⟩
  exact Set.mem_iUnion.2 ⟨if b then 0 else 1, by cases b <;> rfl⟩

/-- Georgii's admissible range for (18.28) is `0 < ε < 4 - 2|h|`; we fix the midpoint. -/
abbrev isingAntiEps (h : ℝ) : ℝ := (4 - 2 * |h|) / 2

lemma isingAntiEps_pos (hh : |h| < 2) : 0 < isingAntiEps h := by
  rw [isingAntiEps]; linarith

lemma isingAntiEps_lt (hh : |h| < 2) : isingAntiEps h < 4 - 2 * |h| := by
  rw [isingAntiEps]; linarith

/-- **Georgii's "the partition `{G_1, G_2}` clearly satisfies the stability condition
(18.23)(a)(ii)"**: the two staggered configurations differ at *every* corner of `C`, in
particular on each of the four faces. -/
theorem pairwise_disjoint_faceRestrict_isingAntiG (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict Bool k a '' isingAntiG m)
      (faceRestrict Bool k a '' isingAntiG n) := by
  refine pairwise_disjoint_faceRestrict_singleton
    (ζ := fun n : Fin 2 ↦ staggerCube (![true, false] n)) fun m n hmn ↦ ?_
  refine ⟨fun _ ↦ a, rfl, ?_⟩
  fin_cases m <;> fin_cases n <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] at hmn ⊢ <;>
    first
      | exact absurd rfl hmn
      | exact staggerCube_ne _ _

theorem isPStablePartition_isingAntiG (hh : |h| < 2) :
    IsPStablePartition (isingAntiCube 2 h) uniformSpinMeasure Set.univ isingAntiG where
  exists_localGroundStates_subset :=
    ⟨isingAntiEps h, isingAntiEps_pos hh,
      localGroundStates_subset_isingAntiG hh (isingAntiEps_pos hh).le (isingAntiEps_lt hh)⟩
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_isingAntiG k a


/-! #### The symmetries `r_0, r_1, r_2` exchange `G_1` and `G_2` -/

/-- Georgii's reflection `r_k` of the cube exchanges the two staggered configurations: it changes
the parity of every corner. -/
lemma onCube_refl_staggerCube (k : Fin d) (b : Bool) :
    (CubeTransformation.refl (E := Bool) k).onCube.toFun (staggerCube b)
      = (staggerCube (!b) : (Fin d → Fin 2) → Bool) := by
  rw [CubeTransformation.refl_onCube_toFun]
  funext c
  rw [cubeRefl_apply, cubeSiteRefl_eq_add_single, staggerCube_add_single]

/-- Georgii's rotation `r_0` (18.20) exchanges the two staggered configurations. -/
lemma onCube_planeRot_staggerCube (b : Bool) :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun (staggerCube b)
      = (staggerCube (!b) : (Fin 2 → Fin 2) → Bool) := by
  funext c
  rw [CubeTransformation.planeRot_onCube_toFun_apply, staggerCube_apply, staggerCube_apply]
  have hsum : ∑ l, (Function.update (Function.update c 0 (c 1)) 1 (c 0 + 1)) l
      = ∑ l, c l + 1 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Function.update_of_ne (by decide),
      Function.update_self, Function.update_self, add_comm (c 0) (c 1), add_assoc]
  rw [hsum]
  rcases fin_two_eq_zero_or_one (∑ l, c l) with hc | hc <;> rw [hc] <;> simp

/-- The reflection `r_k` of `E^C` exchanges the two staggered configurations, read as an equality
of preimages: this is what turns the last sentence of Georgii (18.25)(iii) into the assertion
that `θ_{(1,0)}` and `θ_{(0,1)}` exchange the two Gibbs measures of (18.28). -/
lemma preimage_cubeRefl_staggerCube (k : Fin d) (b : Bool) :
    cubeRefl Bool k ⁻¹' ({staggerCube b} : Set ((Fin d → Fin 2) → Bool))
      = {staggerCube (!b)} := by
  ext ζ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, cubeRefl_apply,
    cubeSiteRefl_eq_add_single]
  constructor
  · intro hζ c
    have hc := hζ (c + Pi.single k 1)
    rwa [add_assoc, corner_add_self, add_zero, staggerCube_add_single] at hc
  · intro hζ c
    rw [hζ, staggerCube_add_single, Bool.not_not]

/-- **Georgii's shift group `Θ̃ = {θ_i : i_1 + i_2 ≡ 0 mod 2}`** for (18.28): the iterated
reflection `r^a` fixes a staggered configuration exactly when `a_1 + a_2` is even. -/
lemma sum_latticeParity_two {a : Fin 2 → ℤ} (ha : Even (a 0 + a 1)) :
    ∑ k, latticeParity a k = 0 := by
  have hiff := Int.even_add.1 ha
  rw [Fin.sum_univ_two, latticeParity_apply, latticeParity_apply]
  split_ifs with h0 h1 h2
  · decide
  · exact absurd (hiff.1 h0) h1
  · exact absurd (hiff.2 h2) h0
  · decide

lemma preimage_tauPow_staggerCube {a : Fin 2 → ℤ} (ha : Even (a 0 + a 1)) (b : Bool) :
    tauPow (cubeRefl Bool) (latticeToTorus 0 a)
        ⁻¹' ({staggerCube b} : Set ((Fin 2 → Fin 2) → Bool)) = {staggerCube b} := by
  have hp : ∑ k, latticeParity a k = 0 := sum_latticeParity_two ha
  ext ζ
  simp only [Set.mem_preimage, Set.mem_singleton_iff, tauPow_cubeRefl_latticeToTorus_zero,
    funext_iff]
  constructor
  · intro hζ c
    have hc := hζ (c + latticeParity a)
    rwa [add_assoc, corner_add_self, add_zero, staggerCube_add_of_sum_eq_zero hp] at hc
  · intro hζ c
    rw [hζ, staggerCube_add_of_sum_eq_zero hp]

/-- Georgii's rotation `r_0` belongs to `I_{C,λ}(Φ)` for (18.28). -/
theorem isSymmetry_planeRot_isingAntiCube :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (isingAntiCube 2 h) uniformSpinMeasure :=
  CubeTransformation.isSymmetry_of_spin_refl isingAntiCube_cubeRefl (fun _ ↦ rfl) fun ζ ↦ by
    have hb := cubeBondSum_onCube_of_spin_refl (ψ := fun x y ↦ spin x * spin y)
      (CubeTransformation.planeRot (E := Bool) (d := 0)) (fun _ ↦ rfl) ζ
    have hs := cubeSiteSum_onCube_of_spin_refl (v := spin)
      (CubeTransformation.planeRot (E := Bool) (d := 0)) (fun _ ↦ rfl) ζ
    simp only [isingAntiCube]
    rw [hb, hs]

/-- **Georgii's "`G_1` and `G_2` are related to each other by each of the symmetries `r_0, r_1,
r_2 ∈ I_{C,λ}(Φ)`"** for (18.28). -/
theorem isPhiSymmetric_isingAntiG :
    IsPhiSymmetric (isingAntiCube 2 h) uniformSpinMeasure isingAntiG := by
  refine isPhiSymmetric_of_ne isingAntiCube_cubeRefl fun m n hmn ↦
    ⟨CubeTransformation.refl 0,
      CubeTransformation.isSymmetry_refl isingAntiCube_cubeRefl 0, ?_⟩
  have himg : ∀ b : Bool, (CubeTransformation.refl (E := Bool) (0 : Fin 2)).onCube.toFun ''
      ({staggerCube b} : Set ((Fin 2 → Fin 2) → Bool)) = {staggerCube (!b)} := fun b ↦ by
    rw [Set.image_singleton, onCube_refl_staggerCube]
  fin_cases m <;> fin_cases n <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] at hmn ⊢ <;>
    first
      | exact absurd rfl hmn
      | (rw [isingAntiG, isingAntiG]; exact himg _)


lemma isingAntiG_zero : isingAntiG 0 = ({staggerCube true} : Set ((Fin 2 → Fin 2) → Bool)) := rfl

lemma isingAntiG_one : isingAntiG 1 = ({staggerCube false} : Set ((Fin 2 → Fin 2) → Bool)) := rfl

lemma image_onCube_planeRot_isingAntiG_zero :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' isingAntiG 0
      = isingAntiG 1 := by
  rw [isingAntiG_zero, Set.image_singleton, onCube_planeRot_staggerCube, isingAntiG_one]
  rfl

lemma image_onCube_planeRot_isingAntiG_one :
    (CubeTransformation.planeRot (E := Bool) (d := 0)).onCube.toFun '' isingAntiG 1
      = isingAntiG 0 := by
  rw [isingAntiG_one, Set.image_singleton, onCube_planeRot_staggerCube, isingAntiG_zero]
  rfl

lemma image_onCube_refl_isingAntiG_zero (k : Fin 2) :
    (CubeTransformation.refl (E := Bool) k).onCube.toFun '' isingAntiG 0 = isingAntiG 1 := by
  rw [isingAntiG_zero, Set.image_singleton, onCube_refl_staggerCube, isingAntiG_one]
  rfl

lemma image_onCube_refl_isingAntiG_one (k : Fin 2) :
    (CubeTransformation.refl (E := Bool) k).onCube.toFun '' isingAntiG 1 = isingAntiG 0 := by
  rw [isingAntiG_one, Set.image_singleton, onCube_refl_staggerCube, isingAntiG_zero]
  rfl

lemma preimage_cubeRefl_isingAntiG_zero (k : Fin 2) :
    cubeRefl Bool k ⁻¹' isingAntiG 0 = isingAntiG 1 := by
  rw [isingAntiG_zero, preimage_cubeRefl_staggerCube, isingAntiG_one]
  rfl

lemma preimage_cubeRefl_isingAntiG_one (k : Fin 2) :
    cubeRefl Bool k ⁻¹' isingAntiG 1 = isingAntiG 0 := by
  rw [isingAntiG_one, preimage_cubeRefl_staggerCube, isingAntiG_zero]
  rfl

/-! #### Georgii 18.3.2: the conclusion -/

open Peierls in
/-- **Georgii 18.3.2, the Ising antiferromagnet in an external field (18.28), `|h| < 2`.**  *For
sufficiently large `β` there are two distinct Gibbs measures `μ_1, μ_2 ∈ 𝒢(βΦ)`: they are random
perturbations of the staggered ground states `ω¹ = ((-1)^{i_1+i_2+1})_i` and
`ω² = ((-1)^{i_1+i_2})_i`, are invariant under all translations `θ_i` with `i_1 + i_2 ≡ 0 mod 2`,
and are related to each other by the `Φ`-symmetries `r_0, r_1, r_2, θ_{(0,1)}, θ_{(1,0)}`.*

"Random perturbation of `ω^n`" is the pair of ocean assertions (18.25)(i): `μ_n` gives full mass
to the event that the staggered pattern `G_n` percolates in an ocean, and probability at least
`1 - 4 z(t(G_ε(Φ), βΦ))` — which tends to `1` as `β → ∞` — to the origin belonging to it.

`Φ_C` attains its minimum `-4` exactly on `G_1 ∪ G_2` and its next value is `-2|h|`
(`localGroundStates_isingAntiCube`), which is why `|h| < 2` and `0 < ε < 4 - 2|h|`; the partition
is stable because the two staggered configurations differ at *every* corner
(`isPStablePartition_isingAntiG`), and `Φ`-symmetric because each of `r_0, r_1, r_2` reverses the
parity of the corners (`isPhiSymmetric_isingAntiG`).  The last two symmetries `θ_{(1,0)}`,
`θ_{(0,1)}` come from the last sentence of (18.25)(iii). -/
theorem eventually_exists_isingAnti_gibbsMeasure_pair (hh : |h| < 2) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * isingAntiCube 2 h ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * isingAntiCube 2 h ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → Bool),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec Bool
          (fun ζ ↦ β * isingAntiCube 2 h ζ) uniformSpinMeasure hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart Bool (isingAntiG n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - 4 * Peierls.crossingBound (patternWeight
            (fun ζ ↦ β * isingAntiCube 2 h ζ) uniformSpinMeasure
            (localGroundStates (isingAntiCube 2 h) uniformSpinMeasure (isingAntiEps h)))
          ≤ μ n {ω | (0 : Site) ∈ latticeOceanPart Bool (isingAntiG n) ω}) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ), Even (a 0 + a 1) →
          MeasurePreserving (shift Bool a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 1 ∧
        (μ 1).map ((CubeTransformation.planeRot (E := Bool) (d := 0)).onLattice Bool).toFun
          = μ 0 ∧
        (∀ k : Fin 2,
          (μ 0).map ((CubeTransformation.refl (E := Bool) k).onLattice Bool).toFun = μ 1) ∧
        (∀ k : Fin 2,
          (μ 1).map ((CubeTransformation.refl (E := Bool) k).onLattice Bool).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 1).map (shift Bool (Pi.single k 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 0).map (shift Bool (Pi.single k 1)).toFun = μ 1) := by
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := Bool)
    (φ := isingAntiCube 2 h) (ν := uniformSpinMeasure) (G := isingAntiG)
    measurable_isingAntiCube (neg_four_le_isingAntiCube hh) isingAntiCube_cubeRefl
    (isCubeConfining_univ ⟨4 + 4 * |h|, abs_isingAntiCube_le⟩)
    (isPStablePartition_isingAntiG hh) isPhiSymmetric_isingAntiG measurableSet_isingAntiG
    (isingAntiEps_pos hh)
    (localGroundStates_subset_isingAntiG hh (isingAntiEps_pos hh).le (isingAntiEps_lt hh))]
    with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hβ hφβ hMβ
  have hrot : (CubeTransformation.planeRot (E := Bool) (d := 0)).IsSymmetry
      (fun ζ ↦ β * isingAntiCube 2 h ζ) uniformSpinMeasure :=
    isSymmetry_planeRot_isingAntiCube.const_mul isingAntiCube_cubeRefl β
  have hrefl : ∀ k : Fin 2, (CubeTransformation.refl (E := Bool) k).IsSymmetry
      (fun ζ ↦ β * isingAntiCube 2 h ζ) uniformSpinMeasure := fun k ↦
    CubeTransformation.isSymmetry_refl (ν := uniformSpinMeasure)
      (fun k ζ ↦ by rw [isingAntiCube_cubeRefl k ζ]) k
  exact ⟨ρ, h1, h2, h3 (by decide), h4, h5,
    fun n a ha ↦ h6 n a (preimage_tauPow_staggerCube ha _),
    h8 0 1 _ hrot image_onCube_planeRot_isingAntiG_zero,
    h8 1 0 _ hrot image_onCube_planeRot_isingAntiG_one,
    fun k ↦ h8 0 1 _ (hrefl k) (image_onCube_refl_isingAntiG_zero k),
    fun k ↦ h8 1 0 _ (hrefl k) (image_onCube_refl_isingAntiG_one k),
    fun k ↦ h9 0 1 k (preimage_cubeRefl_isingAntiG_zero k),
    fun k ↦ h9 1 0 k (preimage_cubeRefl_isingAntiG_one k)⟩

end Antiferromagnet

end MeasureTheory.GibbsMeasure

end

end

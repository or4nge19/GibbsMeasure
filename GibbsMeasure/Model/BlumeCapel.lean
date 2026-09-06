/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.PeriodicGibbsSymmetry
public import GibbsMeasure.Specification.ResolvingPerturbations

/-!
# Georgii, Example (19.8): the Blume–Capel model

Georgii, *Gibbs Measures and Phase Transitions*, Example (19.8).  On `S = ℤ²` with state space
`E = {-1, 0, 1}` and counting measure, the `C`-potential

`Φ_C = ∑_{{i,j} ⊆ C, |i - j| = 1} (σ_i - σ_j)²`

has exactly three local ground states, the three constant cube configurations, and only two of
them — the all-plus and the all-minus one — are related by a symmetry of `Φ`.  So the partition
`{G_1, G_{2,1}, G_{2,2}}` of the local ground states is stable but not `Φ`-symmetric, and
Theorem (18.25) does not apply.  Georgii's remedy is Comment (19.5)(1): the coarser partition
`{G_1, G_2}`, `G_2 = G_{2,1} ∪ G_{2,2}`, is *resolved* by the single bounded potential
`Φ^1_C = ∑_{i ∈ C} σ_i²`.

## Main results

* `blumeCapelEnergy_eq_zero_iff` — the local ground states of `Φ` are exactly the constant cube
  configurations; `localGroundEnergy_blumeCapel` is `m_Φ = 0` and
  `localGroundStates_blumeCapel_eq` is `G_ε(Φ) = {constant configurations}` for `0 < ε < 1`.
* `isPStablePartition_blumeCapelFine` — the fine partition `{G_1, G_{2,1}, G_{2,2}}` satisfies
  Definition (18.23)(a); `isPStablePartition_blumeCapel` is the same for the coarse partition
  `{G_1, G_2}`.
* `attainsGroundEnergy_blumeCapel` — assumption **(19.1)** for `G_1` and `G_2`: neither is at an
  energetic disadvantage.
* `resolves_blumeCapel` — **Example (19.8)**: `Φ^1_C = ∑_{i ∈ C} σ_i²` resolves `{G_1, G_2}` in
  the sense of Definition (19.4), by Comment (19.5)(1).

## What is *not* here

* Georgii's conclusion `|ex 𝒢_Θ(βΦ + βh(β)Φ^1)| ≥ 3` is Theorem (19.6) followed by Corollary
  (19.7).  (19.7) is `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_refinement`, but (19.6)
  rests on the Knaster–Kuratowski–Mazurkiewicz lemma (19.12), which Mathlib does not have — see
  the module docstring of `GibbsMeasure/Specification/ResolvingPerturbations.lean`.
* Georgii's remark that "there exist no `Φ`-symmetries which map these two configurations to the
  third one" — the reason the fine partition is not `Φ`-symmetric, so that Theorem (18.25) does
  not apply and the perturbation is needed.  He asserts it without proof, and it is not used by
  anything below: `resolves_blumeCapel` is what feeds Theorem (19.6).  (A `τ ∈ I_{C,λ}(Φ)`
  carrying the all-zero configuration to an all-`±1` one would have to have per-corner spin maps
  `τ_c` with `Φ_C ∘ τ_C = Φ_C`; ruling that out is a finite but genuinely separate check.)
* Bricmont and Slawny's theorem that the *unperturbed* `βΦ` has a unique shift-invariant Gibbs
  measure for all large `β`, which Georgii quotes but does not prove.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The model -/

/-- The three spin values `-1, 0, +1` of the Blume–Capel model, indexed by `Fin 3`. -/
def blumeCapelSpin : Fin 3 → ℤ := ![-1, 0, 1]

lemma blumeCapelSpin_injective : Function.Injective blumeCapelSpin := by decide

@[simp] lemma blumeCapelSpin_zero : blumeCapelSpin 0 = -1 := rfl
@[simp] lemma blumeCapelSpin_one : blumeCapelSpin 1 = 0 := rfl
@[simp] lemma blumeCapelSpin_two : blumeCapelSpin 2 = 1 := rfl

lemma blumeCapelSpin_sq_le_one (x : Fin 3) : blumeCapelSpin x ^ 2 ≤ 1 := by
  fin_cases x <;> decide

lemma blumeCapelSpin_sq_nonneg (x : Fin 3) : 0 ≤ blumeCapelSpin x ^ 2 := sq_nonneg _

/-- **Georgii's `Φ_C = ∑_{{i,j} ⊆ C, |i - j| = 1} (σ_i - σ_j)²`** for the Blume–Capel model,
as an integer.  The nearest-neighbour pairs of the unit square `C = {0,1}²` are the pairs
`{c, c + e_k}` with `c_k = 0`, each counted once. -/
def blumeCapelEnergy (ζ : (Fin 2 → Fin 2) → Fin 3) : ℤ :=
  ∑ c : Fin 2 → Fin 2, ∑ k : Fin 2,
    if c k = 0 then
      (blumeCapelSpin (ζ c) - blumeCapelSpin (ζ (Function.update c k 1))) ^ 2 else 0

/-- The Blume–Capel cube interaction. -/
def blumeCapelCube (ζ : (Fin 2 → Fin 2) → Fin 3) : ℝ := (blumeCapelEnergy ζ : ℝ)

/-- **Georgii's `Φ^1_C = ∑_{i ∈ C} σ_i²`**, the perturbing potential of Example (19.8). -/
def blumeCapelField (ζ : (Fin 2 → Fin 2) → Fin 3) : ℝ :=
  ((∑ c : Fin 2 → Fin 2, blumeCapelSpin (ζ c) ^ 2 : ℤ) : ℝ)

/-- The a priori measure: the normalised counting measure on `E = {-1, 0, 1}`. -/
def blumeCapelPrior : Measure (Fin 3) := ProbabilityTheory.uniformOn (Set.univ : Set (Fin 3))

instance : IsProbabilityMeasure blumeCapelPrior :=
  ProbabilityTheory.isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

lemma blumeCapelPrior_singleton (x : Fin 3) : blumeCapelPrior {x} = (3 : ℝ≥0∞)⁻¹ := by
  rw [blumeCapelPrior, ProbabilityTheory.uniformOn_univ, Measure.count_singleton]
  simp

/-! ### The local ground states -/

lemma blumeCapelEnergy_nonneg (ζ : (Fin 2 → Fin 2) → Fin 3) : 0 ≤ blumeCapelEnergy ζ :=
  Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun k _ ↦ by
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl

lemma blumeCapelCube_nonneg (ζ : (Fin 2 → Fin 2) → Fin 3) : 0 ≤ blumeCapelCube ζ := by
  simp only [blumeCapelCube]
  exact_mod_cast blumeCapelEnergy_nonneg ζ

/-- The energy vanishes exactly when neighbouring corners of the cube carry the same spin. -/
lemma blumeCapelEnergy_eq_zero_iff_bonds (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelEnergy ζ = 0 ↔
      ∀ c : Fin 2 → Fin 2, ∀ k : Fin 2, c k = 0 → ζ c = ζ (Function.update c k 1) := by
  rw [blumeCapelEnergy, Finset.sum_eq_zero_iff_of_nonneg
    (fun c _ ↦ Finset.sum_nonneg fun k _ ↦ by split_ifs; exacts [sq_nonneg _, le_rfl])]
  refine ⟨fun h c k hck ↦ ?_, fun h c _ ↦ Finset.sum_eq_zero fun k _ ↦ ?_⟩
  · have hc := h c (Finset.mem_univ c)
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ ↦ by split_ifs; exacts [sq_nonneg _, le_rfl])] at hc
    have hk := hc k (Finset.mem_univ k)
    split_ifs at hk with h'
    · rw [pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hk
      exact blumeCapelSpin_injective hk
    · exact absurd hck h'
  · split_ifs with hck
    · rw [h c k hck, sub_self]
      norm_num
    · rfl

/-- **The local ground states of the Blume–Capel potential are the constant cube
configurations.** -/
theorem blumeCapelEnergy_eq_zero_iff (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelEnergy ζ = 0 ↔ ∃ v : Fin 3, ζ = fun _ ↦ v := by
  rw [blumeCapelEnergy_eq_zero_iff_bonds]
  refine ⟨fun h ↦ ⟨ζ ![0, 0], ?_⟩, ?_⟩
  · have h10 : ζ ![1, 0] = ζ ![0, 0] := by
      have := h ![0, 0] 0 rfl
      rw [show Function.update (![0, 0] : Fin 2 → Fin 2) 0 1 = ![1, 0] from by
        funext i; fin_cases i <;> simp] at this
      exact this.symm
    have h01 : ζ ![0, 1] = ζ ![0, 0] := by
      have := h ![0, 0] 1 rfl
      rw [show Function.update (![0, 0] : Fin 2 → Fin 2) 1 1 = ![0, 1] from by
        funext i; fin_cases i <;> simp] at this
      exact this.symm
    have h11 : ζ ![1, 1] = ζ ![0, 0] := by
      have := h ![1, 0] 1 rfl
      rw [show Function.update (![1, 0] : Fin 2 → Fin 2) 1 1 = ![1, 1] from by
        funext i; fin_cases i <;> simp] at this
      rw [← this, h10]
    funext c
    have hc : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
    rcases fin_two_eq_zero_or_one (c 0) with h0 | h0 <;>
      rcases fin_two_eq_zero_or_one (c 1) with h1 | h1 <;>
        rw [hc, h0, h1] <;>
          assumption
  · rintro ⟨v, rfl⟩ c k _
    rfl

lemma blumeCapelCube_eq_zero_iff (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelCube ζ = 0 ↔ ∃ v : Fin 3, ζ = fun _ ↦ v := by
  rw [← blumeCapelEnergy_eq_zero_iff]
  simp only [blumeCapelCube, Int.cast_eq_zero]

@[simp] lemma blumeCapelCube_const (v : Fin 3) : blumeCapelCube (fun _ ↦ v) = 0 :=
  (blumeCapelCube_eq_zero_iff _).2 ⟨v, rfl⟩

/-- A non-constant cube configuration costs at least one unit of energy. -/
lemma one_le_blumeCapelCube (ζ : (Fin 2 → Fin 2) → Fin 3) (hζ : ¬ ∃ v : Fin 3, ζ = fun _ ↦ v) :
    1 ≤ blumeCapelCube ζ := by
  have h0 : blumeCapelEnergy ζ ≠ 0 := fun h ↦ hζ ((blumeCapelEnergy_eq_zero_iff ζ).1 h)
  have h1 : (1 : ℤ) ≤ blumeCapelEnergy ζ :=
    lt_of_le_of_ne (blumeCapelEnergy_nonneg ζ) (Ne.symm h0)
  simp only [blumeCapelCube]
  exact_mod_cast h1

/-! ### Measurability and the a priori measure of a single configuration -/

lemma measurable_blumeCapelCube : Measurable blumeCapelCube := Measurable.of_discrete

lemma measurable_blumeCapelField : Measurable blumeCapelField := Measurable.of_discrete

lemma cubeMeasure_blumeCapel_singleton (a : (Fin 2 → Fin 2) → Fin 3) :
    cubeMeasure 2 blumeCapelPrior {a} = ((3 : ℝ≥0∞)⁻¹) ^ 4 := by
  rw [← Set.univ_pi_singleton a, cubeMeasure, Measure.pi_pi]
  simp only [blumeCapelPrior_singleton, Finset.prod_const, Finset.card_univ]
  norm_num

lemma cubeMeasure_blumeCapel_singleton_ne_zero (a : (Fin 2 → Fin 2) → Fin 3) :
    cubeMeasure 2 blumeCapelPrior {a} ≠ 0 := by
  rw [cubeMeasure_blumeCapel_singleton]
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.2 (by norm_num))

lemma cubeMeasure_blumeCapel_pos {A : Set ((Fin 2 → Fin 2) → Fin 3)} (hA : A.Nonempty) :
    0 < cubeMeasure 2 blumeCapelPrior A := by
  obtain ⟨a, ha⟩ := hA
  exact lt_of_lt_of_le (pos_iff_ne_zero.2 (cubeMeasure_blumeCapel_singleton_ne_zero a))
    (measure_mono (Set.singleton_subset_iff.2 ha))

/-! ### Georgii's `m_Φ` and `G_ε(Φ)` -/

/-- The local ground state energy of the Blume–Capel potential is `0`. -/
theorem localGroundEnergy_blumeCapel : localGroundEnergy blumeCapelCube blumeCapelPrior = 0 := by
  refine le_antisymm ?_ (le_localGroundEnergy blumeCapelCube_nonneg)
  rw [← localGroundEnergyOn_univ]
  refine localGroundEnergyOn_le_of_measure_ne_zero measurable_blumeCapelCube
    blumeCapelCube_nonneg (c := 0) ?_
  refine (cubeMeasure_blumeCapel_pos ⟨fun _ ↦ 1, ?_⟩).ne'
  exact ⟨Set.mem_univ _, le_of_eq (blumeCapelCube_const 1)⟩

/-- **The local ground states of the Blume–Capel model**: for `0 < ε < 1` the set `G_ε(Φ)` is
exactly the set of the three constant cube configurations. -/
theorem localGroundStates_blumeCapel {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    localGroundStates blumeCapelCube blumeCapelPrior ε
      = {ζ : (Fin 2 → Fin 2) → Fin 3 | ∃ v : Fin 3, ζ = fun _ ↦ v} := by
  ext ζ
  rw [mem_localGroundStates, localGroundEnergy_blumeCapel, zero_add]
  refine ⟨fun hle ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · by_contra hcon
    exact absurd (le_trans (one_le_blumeCapelCube ζ hcon) hle) (not_le.2 hε1)
  · rw [hv, blumeCapelCube_const]
    exact hε0.le

/-- Every constant cube configuration is a local `ε`-ground state, for every `ε ≥ 0`. -/
lemma const_mem_localGroundStates_blumeCapel {ε : ℝ} (hε : 0 ≤ ε) (v : Fin 3) :
    (fun _ ↦ v) ∈ localGroundStates blumeCapelCube blumeCapelPrior ε := by
  rw [mem_localGroundStates, localGroundEnergy_blumeCapel, zero_add, blumeCapelCube_const]
  exact hε

/-! ### The partitions of Example (19.8) -/

/-- **Georgii's coarse partition `{G_1, G_2}`** of Example (19.8): `G_1` is the local ground
state with all spins `0`, and `G_2 = G_{2,1} ∪ G_{2,2}` collects the two ferromagnetic ones. -/
def blumeCapelPartition : Fin 2 → Set ((Fin 2 → Fin 2) → Fin 3)
  | 0 => {fun _ ↦ 1}
  | 1 => {fun _ ↦ 0, fun _ ↦ 2}

/-- **Georgii's fine partition `{G_1, G_{2,1}, G_{2,2}}`** of Example (19.8). -/
def blumeCapelFinePartition : Fin 3 → Set ((Fin 2 → Fin 2) → Fin 3)
  | 0 => {fun _ ↦ 1}
  | 1 => {fun _ ↦ 2}
  | 2 => {fun _ ↦ 0}

lemma blumeCapelPartition_nonempty (n : Fin 2) : (blumeCapelPartition n).Nonempty := by
  fin_cases n
  · exact ⟨fun _ ↦ 1, rfl⟩
  · exact ⟨fun _ ↦ 0, Or.inl rfl⟩

lemma blumeCapelFinePartition_nonempty (n : Fin 3) : (blumeCapelFinePartition n).Nonempty := by
  fin_cases n
  · exact ⟨fun _ ↦ 1, rfl⟩
  · exact ⟨fun _ ↦ 2, rfl⟩
  · exact ⟨fun _ ↦ 0, rfl⟩

lemma measurableSet_blumeCapelPartition (n : Fin 2) : MeasurableSet (blumeCapelPartition n) := by
  fin_cases n
  · exact measurableSet_singleton _
  · exact (measurableSet_singleton _).insert _

lemma measurableSet_blumeCapelFinePartition (n : Fin 3) :
    MeasurableSet (blumeCapelFinePartition n) := by
  fin_cases n <;> exact measurableSet_singleton _

lemma iUnion_blumeCapelPartition :
    (⋃ n, blumeCapelPartition n) = {ζ : (Fin 2 → Fin 2) → Fin 3 | ∃ v : Fin 3, ζ = fun _ ↦ v} := by
  ext ζ
  constructor
  · rintro hζ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hζ
    fin_cases n
    · exact ⟨1, hn⟩
    · rcases hn with hn | hn
      · exact ⟨0, hn⟩
      · exact ⟨2, hn⟩
  · rintro ⟨v, rfl⟩
    fin_cases v
    · exact Set.mem_iUnion.2 ⟨1, Or.inl rfl⟩
    · exact Set.mem_iUnion.2 ⟨0, rfl⟩
    · exact Set.mem_iUnion.2 ⟨1, Or.inr rfl⟩

lemma iUnion_blumeCapelFinePartition :
    (⋃ n, blumeCapelFinePartition n)
      = {ζ : (Fin 2 → Fin 2) → Fin 3 | ∃ v : Fin 3, ζ = fun _ ↦ v} := by
  ext ζ
  constructor
  · rintro hζ
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hζ
    fin_cases n
    · exact ⟨1, hn⟩
    · exact ⟨2, hn⟩
    · exact ⟨0, hn⟩
  · rintro ⟨v, rfl⟩
    fin_cases v
    · exact Set.mem_iUnion.2 ⟨2, rfl⟩
    · exact Set.mem_iUnion.2 ⟨0, rfl⟩
    · exact Set.mem_iUnion.2 ⟨1, rfl⟩

/-! ### Stability of the partitions, Georgii (18.23)(a) -/

/-- A `P`-face of the unit square is non-empty. -/
lemma nonempty_face (k a : Fin 2) : Nonempty {c : Fin 2 → Fin 2 // c k = a} :=
  ⟨⟨fun l ↦ if l = k then a else 0, by simp⟩⟩

/-- Distinct constant cube configurations already differ on a face. -/
lemma const_eq_of_faceRestrict_eq {k a : Fin 2} {v w : Fin 3}
    (h : faceRestrict (Fin 3) k a (fun _ ↦ v) = faceRestrict (Fin 3) k a (fun _ ↦ w)) : v = w := by
  obtain ⟨c⟩ := nonempty_face k a
  exact congrFun h c

lemma const_ne_const {v w : Fin 3} (h : v ≠ w) :
    (fun _ : Fin 2 → Fin 2 ↦ v) ≠ fun _ ↦ w := fun hc ↦ h (congrFun hc ![0, 0])

lemma faceRestrict_const_ne {k a : Fin 2} {v w : Fin 3} (hvw : v ≠ w) :
    faceRestrict (Fin 3) k a (fun _ ↦ v) ≠ faceRestrict (Fin 3) k a (fun _ ↦ w) :=
  fun h ↦ hvw (const_eq_of_faceRestrict_eq h)

lemma pairwise_disjoint_blumeCapelPartition :
    Pairwise (Function.onFun Disjoint blumeCapelPartition) := by
  intro m n hmn
  fin_cases m <;> fin_cases n
  · exact absurd rfl hmn
  · rw [Function.onFun, Set.disjoint_left]
    rintro x rfl (h | h)
    · exact const_ne_const (by decide) h
    · exact const_ne_const (by decide) h
  · rw [Function.onFun, Set.disjoint_left]
    rintro x (rfl | rfl) h
    · exact const_ne_const (by decide) h
    · exact const_ne_const (by decide) h
  · exact absurd rfl hmn

/-- **Georgii, Example (19.8)**: the coarse partition `{G_1, G_2}` satisfies Definition
(18.23)(a). -/
theorem isPStablePartition_blumeCapel :
    IsPStablePartition blumeCapelCube blumeCapelPrior Set.univ blumeCapelPartition where
  exists_localGroundStates_subset := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [localGroundStates_blumeCapel (by norm_num) (by norm_num), iUnion_blumeCapelPartition]
  pairwise_disjoint_faceRestrict := by
    intro k _ a m n hmn
    fin_cases m <;> fin_cases n
    · exact absurd rfl hmn
    · rw [Set.disjoint_left]
      rintro x ⟨ζ, rfl, rfl⟩ ⟨ζ', hζ', hx⟩
      rcases hζ' with rfl | rfl
      · exact faceRestrict_const_ne (by decide) hx
      · exact faceRestrict_const_ne (by decide) hx
    · rw [Set.disjoint_left]
      rintro x ⟨ζ, hζ, rfl⟩ ⟨ζ', rfl, hx⟩
      rcases hζ with rfl | rfl
      · exact faceRestrict_const_ne (by decide) hx
      · exact faceRestrict_const_ne (by decide) hx
    · exact absurd rfl hmn

/-- **Georgii, Example (19.8)**: the fine partition `{G_1, G_{2,1}, G_{2,2}}` of the local
ground states of `Φ` is stable, Definition (18.23)(a). -/
theorem isPStablePartition_blumeCapelFine :
    IsPStablePartition blumeCapelCube blumeCapelPrior Set.univ blumeCapelFinePartition where
  exists_localGroundStates_subset := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    rw [localGroundStates_blumeCapel (by norm_num) (by norm_num), iUnion_blumeCapelFinePartition]
  pairwise_disjoint_faceRestrict := by
    intro k _ a m n hmn
    fin_cases m <;> fin_cases n <;>
      first
      | exact absurd rfl hmn
      | · rw [Set.disjoint_left]
          rintro x ⟨ζ, rfl, rfl⟩ ⟨ζ', rfl, hx⟩
          exact faceRestrict_const_ne (by decide) hx

/-! ### Georgii (19.1) for the Blume–Capel partition -/

lemma blumeCapelPartition_subset_const (n : Fin 2) :
    blumeCapelPartition n ⊆ {ζ : (Fin 2 → Fin 2) → Fin 3 | ∃ v : Fin 3, ζ = fun _ ↦ v} := by
  rw [← iUnion_blumeCapelPartition]
  exact Set.subset_iUnion _ n

/-- **Georgii (19.1) for the Blume–Capel model**: neither `G_1` nor `G_2` is at an energetic
disadvantage — both consist of local ground states of `Φ`, and both have positive `λ^C`
measure. -/
theorem attainsGroundEnergy_blumeCapel (n : Fin 2) :
    AttainsGroundEnergy blumeCapelCube blumeCapelPrior (blumeCapelPartition n) := by
  intro ε hε
  obtain ⟨ζ, hζ⟩ := blumeCapelPartition_nonempty n
  obtain ⟨v, rfl⟩ := blumeCapelPartition_subset_const n hζ
  exact cubeMeasure_blumeCapel_pos ⟨_, hζ, const_mem_localGroundStates_blumeCapel hε.le v⟩

/-! ### Georgii's perturbing potential `Φ^1_C = ∑_{i ∈ C} σ_i²` -/

lemma blumeCapelField_const (v : Fin 3) :
    blumeCapelField (fun _ ↦ v) = 4 * ((blumeCapelSpin v ^ 2 : ℤ) : ℝ) := by
  rw [blumeCapelField]
  norm_cast
  simp [Finset.card_univ]

lemma abs_blumeCapelField_le (ζ : (Fin 2 → Fin 2) → Fin 3) : |blumeCapelField ζ| ≤ 4 := by
  have h0 : (0 : ℤ) ≤ ∑ c : Fin 2 → Fin 2, blumeCapelSpin (ζ c) ^ 2 :=
    Finset.sum_nonneg fun c _ ↦ sq_nonneg _
  have h4 : (∑ c : Fin 2 → Fin 2, blumeCapelSpin (ζ c) ^ 2) ≤ 4 := by
    calc (∑ c : Fin 2 → Fin 2, blumeCapelSpin (ζ c) ^ 2)
        ≤ ∑ _c : Fin 2 → Fin 2, (1 : ℤ) := Finset.sum_le_sum fun c _ ↦ blumeCapelSpin_sq_le_one _
      _ = 4 := by simp [Finset.card_univ]
  have hR0 : (0 : ℝ) ≤ blumeCapelField ζ := by
    rw [blumeCapelField]
    exact_mod_cast h0
  have hR4 : blumeCapelField ζ ≤ 4 := by
    rw [blumeCapelField]
    exact_mod_cast h4
  rw [abs_le]
  constructor <;> linarith

/-! ### Georgii, Example (19.8): the resolution -/

/-- **Georgii, Example (19.8).**  The bounded `C`-potential `Φ^1_C = ∑_{i ∈ C} σ_i²` *resolves*
the coarse partition `{G_1, G_2}` of the local ground states of the Blume–Capel potential, in
the sense of Definition (19.4).  Indeed `Φ^1_C = 0` on `G_1` and `Φ^1_C = 4` on
`G_2 = G ∖ G_1`, so Comment (19.5)(1) applies with `c_1 = 4` and `δ_1 = -4`. -/
theorem resolves_blumeCapel :
    Resolves blumeCapelCube blumeCapelPrior (fun _ : Fin 1 ↦ blumeCapelField)
      blumeCapelPartition := by
  refine resolves_of_const_on (M₀ := 0) (c := fun _ ↦ 4) (jump := fun _ ↦ -4) (b := fun _ ↦ 4)
    (ε := 1 / 2) measurable_blumeCapelCube blumeCapelCube_nonneg
    (fun _ ↦ measurable_blumeCapelField) (fun _ ζ ↦ abs_blumeCapelField_le ζ)
    measurableSet_blumeCapelPartition pairwise_disjoint_blumeCapelPartition ?_ ?_
    (fun _ ↦ by norm_num) attainsGroundEnergy_blumeCapel (by norm_num) ?_
  · intro k ζ hζ
    fin_cases k
    obtain ⟨v, rfl⟩ := blumeCapelPartition_subset_const _ hζ
    have hv : v = 1 := by
      have : (fun _ ↦ v) ∈ blumeCapelPartition 0 := hζ
      exact (congrFun this ![0, 0] : v = 1)
    subst hv
    rw [blumeCapelField_const]
    norm_num
  · intro k ζ hζ
    fin_cases k
    obtain ⟨hmem, hnot⟩ := hζ
    rw [iUnion_blumeCapelPartition] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have hv : v ≠ 1 := by
      rintro rfl
      exact hnot rfl
    have hsq : blumeCapelSpin v ^ 2 = 1 := by
      fin_cases v
      · decide
      · exact absurd rfl hv
      · decide
    rw [blumeCapelField_const, hsq]
    norm_num
  · rw [localGroundStates_blumeCapel (by norm_num) (by norm_num), iUnion_blumeCapelPartition]

end MeasureTheory.GibbsMeasure

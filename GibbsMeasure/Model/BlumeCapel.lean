/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.DiscreteSymmetryBreakingExamples
public import GibbsMeasure.Model.SpernerPhaseTransition
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
* `resolves_blumeCapel` — `Φ^1_C = ∑_{i ∈ C} σ_i²` resolves `{G_1, G_2}` in the sense of
  Definition (19.4), by Comment (19.5)(1).
* `blumeCapelCube_cubeRefl`, `blumeCapelField_cubeRefl` — condition (iii) of (17.18) for `Φ` and
  `Φ^1`: both are covered by the general bond-sum/site-sum API (`blumeCapelCube_eq_cubeBondSum`,
  `blumeCapelField_eq_cubeSiteSum`), so no enumeration of the `81` cube configurations is needed.
* `isRSymmetric_blumeCapelPartition` — the members of the partitions consist of *constant*
  configurations, which the reflections of the unit square fix (`isRSymmetric_of_const`).
* `blumeCapelSpinFlip` — Georgii's spin flip `σ ↦ -σ` as a cube transformation (18.21); it
  preserves the a priori measure, `Φ_C` and `Φ^1_C`, and exchanges `G_{2,1}` and `G_{2,2}`.
* `isPStablePartition_blumeCapelSplit` — the refinement `{G_{2,1}, G_{2,2}}` of `G_2` is stable.
* `eventually_exists_gibbsMeasure_family_blumeCapel` — **Example (19.8)**: for large `β` there is
  `h(β)` in an arbitrarily small neighbourhood of the origin such that `βΦ + βh(β)Φ^1` has three
  pairwise mutually singular shift-invariant Gibbs measures, one on each of `G_1`, `G_{2,1}`,
  `G_{2,2}`, and `|ex 𝒢_Θ(βΦ + βh(β)Φ^1)| ≥ 3`.
* `eventually_three_le_encard_extremePoints_blumeCapel` — **Georgii's displayed conclusion of
  (19.8)**, `|ex 𝒢_Θ(βΦ + βh(β)Φ^1)| ≥ 3`, with the crossing weight discharged at `t = 1/64`.

## Deviations from Georgii's statement

* Georgii's `h(β) → 0` and `μ_n(0 ∈ ξ⁰(G_n, ·)) → 1` appear as in Theorem (19.6): the
  neighbourhood `U₀` of the origin and the crossing weight `t` are parameters, and the conclusion
  holds eventually in `β` for each of them.
* Corollary (19.7) uses only condition (18.23)(a)(ii) of the refinement — Georgii says so
  explicitly ("the adjective stable will refer to property (18.23)(a)(ii)") — but
  `IsPStablePartition` bundles that with (18.23)(a)(i).  The refinement `{G_{2,1}, G_{2,2}}` is
  therefore recorded as a stable partition of the local ground states of the perturbed potential
  `Φ - Φ^1`, the member `h = -1` of Georgii's family (19.2), whose local ground states are exactly
  `G_2` (`blumeCapelSplitCube_eq_neg_four_iff`).

## What is *not* here

* Georgii's remark that "there exist no `Φ`-symmetries which map these two configurations to the
  third one" — the reason the fine partition is not `Φ`-symmetric, so that Theorem (18.25) does
  not apply and the perturbation is needed.  He asserts it without proof, and it is not used:
  `resolves_blumeCapel` is what feeds Theorem (19.6).  (A `τ ∈ I_{C,λ}(Φ)` carrying the all-zero
  configuration to an all-`±1` one would have to have per-corner spin maps `τ_c` with
  `Φ_C ∘ τ_C = Φ_C`; ruling that out is a finite but genuinely separate check.)
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


/-! ### The Blume–Capel interaction as a bond sum and a site sum

Georgii's `Φ_C` is a nearest-neighbour bond sum and `Φ^1_C` a site sum over the unit square, so
both are covered by the general API of `cubeBondSum` and `cubeSiteSum`; this is what gives the
reflection invariance (17.18)(iii) and the spin-flip invariance without any enumeration of the
`81` configurations of the square. -/

/-- The Blume–Capel bond interaction `u(x, y) = (σ_x - σ_y)²`. -/
def blumeCapelBond (x y : Fin 3) : ℝ := ((blumeCapelSpin x - blumeCapelSpin y : ℤ) : ℝ) ^ 2

lemma blumeCapelBond_comm (x y : Fin 3) : blumeCapelBond x y = blumeCapelBond y x := by
  simp only [blumeCapelBond]
  push_cast
  ring

/-- The Blume–Capel self-interaction `v(x) = σ_x²` of the perturbing potential `Φ^1`. -/
def blumeCapelSelf (x : Fin 3) : ℝ := ((blumeCapelSpin x ^ 2 : ℤ) : ℝ)

private lemma update_sqCorner :
    ∀ a b : Fin 2, Function.update (sqCorner a b) 0 1 = sqCorner 1 b ∧
      Function.update (sqCorner a b) 1 1 = sqCorner a 1 := by decide

/-- **The four bonds of the unit square** for the Blume–Capel energy, in Georgii's notation
`ω = (w z / u v)`: `Φ_C = (u - v)² + (w - z)² + (u - w)² + (v - z)²`. -/
lemma blumeCapelEnergy_apply (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelEnergy ζ =
      (blumeCapelSpin (ζ (sqCorner 0 0)) - blumeCapelSpin (ζ (sqCorner 1 0))) ^ 2
        + (blumeCapelSpin (ζ (sqCorner 0 1)) - blumeCapelSpin (ζ (sqCorner 1 1))) ^ 2
        + (blumeCapelSpin (ζ (sqCorner 0 0)) - blumeCapelSpin (ζ (sqCorner 0 1))) ^ 2
        + (blumeCapelSpin (ζ (sqCorner 1 0)) - blumeCapelSpin (ζ (sqCorner 1 1))) ^ 2 := by
  rw [blumeCapelEnergy, sum_univ_cubeCorners]
  simp only [Fin.sum_univ_two, (update_sqCorner _ _).1, (update_sqCorner _ _).2]
  norm_num
  ring

/-- **Georgii's `Φ_C` is the bond sum of `u(x, y) = (σ_x - σ_y)²` over the edges of the unit
square.** -/
lemma blumeCapelCube_eq_cubeBondSum (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelCube ζ = cubeBondSum 2 blumeCapelBond ζ := by
  rw [cubeBondSum_two blumeCapelBond_comm, blumeCapelCube, blumeCapelEnergy_apply]
  simp only [blumeCapelBond]
  push_cast
  ring

/-- **Georgii's `Φ^1_C = ∑_{i ∈ C} σ_i²` is the site sum of `v(x) = σ_x²`.** -/
lemma blumeCapelField_eq_cubeSiteSum (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelField ζ = cubeSiteSum 2 blumeCapelSelf ζ := by
  rw [blumeCapelField, cubeSiteSum_def]
  simp only [blumeCapelSelf]
  push_cast
  ring

/-! ### Condition (iii) of Georgii (17.18): the reflections of the unit square -/

/-- **Condition (iii) of Georgii (17.18)** for the Blume–Capel potential: `Φ_C` is a bond sum,
hence invariant under every reflection `r_k` of the unit square. -/
lemma blumeCapelCube_cubeRefl (k : Fin 2) (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelCube (cubeRefl (Fin 3) k ζ) = blumeCapelCube ζ := by
  rw [blumeCapelCube_eq_cubeBondSum, blumeCapelCube_eq_cubeBondSum, cubeBondSum_cubeRefl]

/-- **Condition (iii) of Georgii (17.18)** for the perturbing potential `Φ^1_C`: it is a site
sum, hence invariant under every reflection `r_k` of the unit square. -/
lemma blumeCapelField_cubeRefl (k : Fin 2) (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelField (cubeRefl (Fin 3) k ζ) = blumeCapelField ζ := by
  rw [blumeCapelField_eq_cubeSiteSum, blumeCapelField_eq_cubeSiteSum, cubeSiteSum_cubeRefl]

/-! ### Condition (iv) of Georgii (17.18) -/

/-- **Condition (iv) of Georgii (17.18)** for the Blume–Capel potential, in its first
alternative `‖Φ_C‖ < ∞`: the state space is finite. -/
theorem isCubeConfining_blumeCapelCube :
    IsCubeConfining blumeCapelCube blumeCapelPrior fun _ : ℕ ↦ (Set.univ : Set (Fin 3)) :=
  isCubeConfining_univ_of_finite _ _

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


/-! ### Georgii's spin flip `σ ↦ -σ`

The only symmetry of `Φ` relating two of the three local ground states: it exchanges the
all-plus and the all-minus configuration and fixes the all-zero one.  Georgii's remark that no
`Φ`-symmetry carries the ferromagnetic ground states to the paramagnetic one is what makes the
fine partition non-`Φ`-symmetric, so that Theorem (18.25) does not apply and the perturbation
`Φ^1` is needed. -/

/-- The spin flip `σ ↦ -σ` of `E = {-1, 0, 1}`: the transposition of `-1` and `1`, in the
encoding `blumeCapelSpin = ![-1, 0, 1]` the transposition of `0` and `2`. -/
def blumeCapelFlip : Fin 3 ≃ᵐ Fin 3 :=
  MeasurableEquiv.ofInvolutive ![2, 1, 0] (fun x ↦ by fin_cases x <;> rfl) Measurable.of_discrete

@[simp] lemma blumeCapelFlip_apply (x : Fin 3) : blumeCapelFlip x = ![2, 1, 0] x := rfl

lemma blumeCapelFlip_blumeCapelFlip (x : Fin 3) : blumeCapelFlip (blumeCapelFlip x) = x := by
  fin_cases x <;> rfl

lemma blumeCapelSpin_blumeCapelFlip (x : Fin 3) :
    blumeCapelSpin (blumeCapelFlip x) = -blumeCapelSpin x := by fin_cases x <;> rfl

lemma blumeCapelPrior_singleton_ne_zero (x : Fin 3) : blumeCapelPrior {x} ≠ 0 := by
  rw [blumeCapelPrior_singleton]
  exact ENNReal.inv_ne_zero.2 (by norm_num)

/-- The spin flip preserves the uniform a priori measure. -/
lemma measurePreserving_blumeCapelFlip :
    MeasurePreserving ⇑blumeCapelFlip blumeCapelPrior blumeCapelPrior := by
  refine ⟨blumeCapelFlip.measurable, Measure.ext_of_singleton fun x ↦ ?_⟩
  have hpre : (⇑blumeCapelFlip ⁻¹' {x}) = {blumeCapelFlip x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ by rw [← h, blumeCapelFlip_blumeCapelFlip],
      fun h ↦ by rw [h, blumeCapelFlip_blumeCapelFlip]⟩
  rw [Measure.map_apply blumeCapelFlip.measurable (measurableSet_singleton x), hpre,
    blumeCapelPrior_singleton, blumeCapelPrior_singleton]

/-- **Georgii's spin flip of Example (19.8)** as a cube transformation (18.21): the pure spin
transformation `σ ↦ -σ` at every corner of the unit square. -/
abbrev blumeCapelSpinFlip : CubeTransformation (Fin 3) 2 :=
  CubeTransformation.pureSpin fun _ ↦ blumeCapelFlip

lemma onCube_blumeCapelSpinFlip (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelSpinFlip.onCube.toFun ζ = fun c ↦ blumeCapelFlip (ζ c) := by
  funext c
  rw [CubeTransformation.pureSpin_onCube_toFun_apply]

lemma blumeCapelBond_blumeCapelFlip (x y : Fin 3) :
    blumeCapelBond (blumeCapelFlip x) (blumeCapelFlip y) = blumeCapelBond x y := by
  simp only [blumeCapelBond, blumeCapelSpin_blumeCapelFlip]
  push_cast
  ring

lemma blumeCapelSelf_blumeCapelFlip (x : Fin 3) :
    blumeCapelSelf (blumeCapelFlip x) = blumeCapelSelf x := by
  simp only [blumeCapelSelf, blumeCapelSpin_blumeCapelFlip]
  push_cast
  ring

/-- **The spin flip is a symmetry of `Φ`**: it reverses both spins of every bond, and
`(-σ_i + σ_j)² = (σ_i - σ_j)²`. -/
lemma blumeCapelCube_onCube_blumeCapelSpinFlip (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelCube (blumeCapelSpinFlip.onCube.toFun ζ) = blumeCapelCube ζ := by
  rw [onCube_blumeCapelSpinFlip, blumeCapelCube_eq_cubeBondSum, blumeCapelCube_eq_cubeBondSum]
  exact cubeBondSum_comp (Equiv.refl _) (fun _ _ ↦ Iff.rfl) (fun _ ↦ ⇑blumeCapelFlip)
    (fun _ _ _ x y ↦ blumeCapelBond_blumeCapelFlip x y) ζ

/-- **The spin flip is a symmetry of `Φ^1`**: `(-σ_i)² = σ_i²`. -/
lemma blumeCapelField_onCube_blumeCapelSpinFlip (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelField (blumeCapelSpinFlip.onCube.toFun ζ) = blumeCapelField ζ := by
  rw [onCube_blumeCapelSpinFlip, blumeCapelField_eq_cubeSiteSum, blumeCapelField_eq_cubeSiteSum,
    cubeSiteSum_def, cubeSiteSum_def]
  exact Finset.sum_congr rfl fun c _ ↦ blumeCapelSelf_blumeCapelFlip (ζ c)

lemma image_onCube_blumeCapelSpinFlip_const (v : Fin 3) :
    blumeCapelSpinFlip.onCube.toFun '' {fun _ ↦ v}
      = {fun _ : Fin 2 → Fin 2 ↦ blumeCapelFlip v} := by
  rw [Set.image_singleton, onCube_blumeCapelSpinFlip]

/-! ### `r`-symmetry of the ground state classes -/

/-- **The local ground state classes of the Blume–Capel model are `r`-symmetric.**  Each consists
of constant cube configurations, which the reflections of the unit square fix. -/
theorem isRSymmetric_blumeCapelPartition (n : Fin 2) :
    IsRSymmetric (Fin 3) (blumeCapelPartition n) :=
  isRSymmetric_of_const fun _ζ hζ ↦ blumeCapelPartition_subset_const n hζ

theorem isRSymmetric_blumeCapelFinePartition (n : Fin 3) :
    IsRSymmetric (Fin 3) (blumeCapelFinePartition n) := by
  refine isRSymmetric_of_const fun ζ hζ ↦ ?_
  have hmem : ζ ∈ {ζ : (Fin 2 → Fin 2) → Fin 3 | ∃ v : Fin 3, ζ = fun _ ↦ v} := by
    rw [← iUnion_blumeCapelFinePartition]
    exact Set.mem_iUnion.2 ⟨n, hζ⟩
  exact hmem

/-! ### Georgii's refinement `{G_{2,1}, G_{2,2}}` of `G_2` -/

/-- **Georgii's refinement of `G_2`** in Example (19.8): the all-plus and the all-minus local
ground state, exchanged by the spin flip. -/
def blumeCapelSplitPartition : Fin 2 → Set ((Fin 2 → Fin 2) → Fin 3)
  | 0 => {fun _ ↦ 2}
  | 1 => {fun _ ↦ 0}

lemma measurableSet_blumeCapelSplitPartition (ℓ : Fin 2) :
    MeasurableSet (blumeCapelSplitPartition ℓ) := by
  fin_cases ℓ <;> exact measurableSet_singleton _

lemma iUnion_blumeCapelSplitPartition :
    (⋃ ℓ, blumeCapelSplitPartition ℓ) = blumeCapelPartition 1 := by
  ext ζ
  constructor
  · rintro hζ
    obtain ⟨ℓ, hℓ⟩ := Set.mem_iUnion.1 hζ
    fin_cases ℓ
    · exact Or.inr hℓ
    · exact Or.inl hℓ
  · rintro (hζ | hζ)
    · exact Set.mem_iUnion.2 ⟨1, hζ⟩
    · exact Set.mem_iUnion.2 ⟨0, hζ⟩

theorem isRSymmetric_blumeCapelSplitPartition (ℓ : Fin 2) :
    IsRSymmetric (Fin 3) (blumeCapelSplitPartition ℓ) :=
  isRSymmetric_of_const fun _ζ hζ ↦ blumeCapelPartition_subset_const 1
    (iUnion_blumeCapelSplitPartition ▸ Set.mem_iUnion.2 ⟨ℓ, hζ⟩)

/-- **The spin flip exchanges `G_{2,1}` and `G_{2,2}`**, Georgii's "the first two of these local
ground states are related to each other by a symmetry of `Φ`, namely the spin flip". -/
lemma image_onCube_blumeCapelSpinFlip_split_zero :
    blumeCapelSpinFlip.onCube.toFun '' blumeCapelSplitPartition 0
      = blumeCapelSplitPartition 1 := by
  have h0 : blumeCapelSplitPartition 0 = {fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3)} := rfl
  have h1 : blumeCapelSplitPartition 1 = {fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3)} := rfl
  rw [h0, h1, image_onCube_blumeCapelSpinFlip_const]
  rfl

lemma image_onCube_blumeCapelSpinFlip_split_one :
    blumeCapelSpinFlip.onCube.toFun '' blumeCapelSplitPartition 1
      = blumeCapelSplitPartition 0 := by
  have h0 : blumeCapelSplitPartition 0 = {fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3)} := rfl
  have h1 : blumeCapelSplitPartition 1 = {fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3)} := rfl
  rw [h0, h1, image_onCube_blumeCapelSpinFlip_const]
  rfl

/-- The spin flip preserves `G_2 = G_{2,1} ∪ G_{2,2}`. -/
lemma image_onCube_blumeCapelSpinFlip_partition_one :
    blumeCapelSpinFlip.onCube.toFun '' blumeCapelPartition 1 = blumeCapelPartition 1 := by
  have h : blumeCapelPartition 1
      = {fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3), fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3)} := rfl
  have h0 : blumeCapelSpinFlip.onCube.toFun (fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3))
      = fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3) := by rw [onCube_blumeCapelSpinFlip]; rfl
  have h2 : blumeCapelSpinFlip.onCube.toFun (fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3))
      = fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3) := by rw [onCube_blumeCapelSpinFlip]; rfl
  rw [h, Set.image_insert_eq, Set.image_singleton, h0, h2, Set.pair_comm]


/-! ### Stability of Georgii's refinement, (18.23)(a)(ii)

Georgii calls `{G_{2,1}, G_{2,2}}` a *stable* partition of `G_2` and says explicitly that "the
adjective stable will refer to property (18.23)(a)(ii)" — the face-disjointness alone.
`IsPStablePartition` bundles that condition with (18.23)(a)(i), the covering of the local ground
states, and Corollary (19.7) (`exists_gibbsMeasure_refinement`) therefore asks for a `C`-potential
whose local ground states are covered by the refinement.  The perturbed potential `Φ - Φ^1` — the
member `h = -1` of Georgii's family (19.2) — is such a potential: `Φ_C - Φ^1_C ≥ -4` with equality
exactly on `G_2`. -/

lemma blumeCapelField_le_four (ζ : (Fin 2 → Fin 2) → Fin 3) : blumeCapelField ζ ≤ 4 :=
  (abs_le.1 (abs_blumeCapelField_le ζ)).2

/-- `Φ_C - Φ^1_C ≥ -4`: the bond energy is nonnegative and the four spins contribute at most `4`
to the field term. -/
lemma neg_four_le_blumeCapelSplitCube (ζ : (Fin 2 → Fin 2) → Fin 3) :
    -4 ≤ blumeCapelCube ζ - blumeCapelField ζ := by
  linarith [blumeCapelCube_nonneg ζ, blumeCapelField_le_four ζ]

/-- **The local ground states of `Φ - Φ^1` are exactly `G_2 = G_{2,1} ∪ G_{2,2}`**: equality in
`Φ_C - Φ^1_C ≥ -4` forces `Φ_C = 0`, so a constant configuration, and `Φ^1_C = 4`, so a nonzero
spin. -/
lemma blumeCapelSplitCube_eq_neg_four_iff (ζ : (Fin 2 → Fin 2) → Fin 3) :
    blumeCapelCube ζ - blumeCapelField ζ = -4 ↔ ζ ∈ ⋃ ℓ, blumeCapelSplitPartition ℓ := by
  rw [iUnion_blumeCapelSplitPartition]
  have hpart : blumeCapelPartition 1
      = {fun _ : Fin 2 → Fin 2 ↦ (0 : Fin 3), fun _ : Fin 2 → Fin 2 ↦ (2 : Fin 3)} := rfl
  rw [hpart]
  constructor
  · intro heq
    have hcube : blumeCapelCube ζ = 0 :=
      le_antisymm (by linarith [blumeCapelField_le_four ζ]) (blumeCapelCube_nonneg ζ)
    have hfield : blumeCapelField ζ = 4 := by linarith
    obtain ⟨v, rfl⟩ := (blumeCapelCube_eq_zero_iff ζ).1 hcube
    rw [blumeCapelField_const] at hfield
    have hsq : blumeCapelSpin v ^ 2 = 1 := by
      have hcast : ((blumeCapelSpin v ^ 2 : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
        push_cast at hfield ⊢
        linarith
      exact_mod_cast hcast
    fin_cases v
    · exact Or.inl rfl
    · exact absurd hsq (by decide)
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;>
      rw [blumeCapelCube_const, blumeCapelField_const] <;> norm_num

lemma exists_pos_localGroundStates_subset_blumeCapelSplit :
    ∃ ε > 0, localGroundStates (fun ζ ↦ blumeCapelCube ζ - blumeCapelField ζ) blumeCapelPrior ε
      ⊆ ⋃ ℓ, blumeCapelSplitPartition ℓ := by
  obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset
    (φ := fun ζ ↦ blumeCapelCube ζ - blumeCapelField ζ) (ν := blumeCapelPrior)
    blumeCapelPrior_singleton_ne_zero neg_four_le_blumeCapelSplitCube
    (ζ₀ := fun _ ↦ (0 : Fin 3))
    (by rw [blumeCapelCube_const, blumeCapelField_const]; norm_num)
  exact ⟨ε, hε, fun ζ hζ ↦ (blumeCapelSplitCube_eq_neg_four_iff ζ).1 (hsub hζ)⟩

/-- **Georgii, Example (19.8)**: the refinement `{G_{2,1}, G_{2,2}}` of `G_2` is stable in the
sense of (18.23)(a)(ii); it is recorded as a stable partition of the local ground states of the
perturbed potential `Φ - Φ^1`, whose local ground states it exactly covers. -/
theorem isPStablePartition_blumeCapelSplit :
    IsPStablePartition (fun ζ ↦ blumeCapelCube ζ - blumeCapelField ζ) blumeCapelPrior Set.univ
      blumeCapelSplitPartition where
  exists_localGroundStates_subset := exists_pos_localGroundStates_subset_blumeCapelSplit
  pairwise_disjoint_faceRestrict := by
    intro k _ a m n hmn
    fin_cases m <;> fin_cases n <;>
      first
      | exact absurd rfl hmn
      | · rw [Set.disjoint_left]
          rintro x ⟨ζ, rfl, rfl⟩ ⟨ζ', rfl, hx⟩
          exact faceRestrict_const_ne (by decide) hx

/-! ### The fine partition as the refinement of the coarse one -/

lemma blumeCapelFinePartition_zero :
    blumeCapelFinePartition 0 = blumeCapelPartition 0 := rfl

lemma blumeCapelFinePartition_succ (ℓ : Fin 2) :
    blumeCapelFinePartition ℓ.succ = blumeCapelSplitPartition ℓ := by
  fin_cases ℓ <;> rfl

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

/-! ### Georgii, Example (19.8): the conclusion -/

/-- **Georgii, Example (19.8).**  For all sufficiently large `β` there is a parameter `h(β)`,
lying in an arbitrarily prescribed neighbourhood `U₀` of the origin — Georgii's
`h(β) → 0` — such that the perturbed Blume–Capel potential `βΦ + βh(β)Φ^1` has *three* pairwise
mutually singular shift-invariant Gibbs measures, one for each of the three local ground states

`G_1 = {(00 / 00)}`,  `G_{2,1} = {(++ / ++)}`,  `G_{2,2} = {(-- / --)}`,

each living on the event that its own ground state percolates and containing the origin in that
ocean with probability at least `1 - 2·4z(t)`.  In particular

`|ex 𝒢_Θ(βΦ + βh(β)Φ^1)| ≥ 3`.

The proof is Georgii's: the coarse partition `{G_1, G_2}` is stable
(`isPStablePartition_blumeCapel`), its members are `r`-symmetric
(`isRSymmetric_blumeCapelPartition` — they consist of constant configurations) and satisfy
(19.1) (`attainsGroundEnergy_blumeCapel`), and `Φ^1_C = ∑_{i ∈ C} σ_i²` resolves it
(`resolves_blumeCapel`).  Theorem (19.6),
`eventually_exists_gibbsMeasure_family_of_resolvesOn`, therefore produces two phases `μ_1, μ_2`,
and the spin flip `σ ↦ -σ` exchanges `G_{2,1}` and `G_{2,2}` while preserving the a priori
measure, `Φ_C` and `Φ^1_C`, so Corollary (19.7), `exists_gibbsMeasure_refinement`, splits `μ_2`
into two.

Since `t` may be taken arbitrarily small and `U₀` arbitrarily small, this is exactly Georgii's
statement, with his `h(β) → 0` and `μ_n(0 ∈ ξ⁰(G_n, ·)) → 1` quantified over the neighbourhood
`U₀` and the weight `t`.

Bricmont and Slawny's theorem that the *unperturbed* `βΦ` has a unique shift-invariant Gibbs
measure for all large `β` — so that the perturbation is genuinely necessary — is quoted without
proof by Georgii and is not formalised. -/
theorem eventually_exists_gibbsMeasure_family_blumeCapel {U₀ : Set (Fin 1 → ℝ)}
    (hU₀ : U₀ ∈ 𝓝 (0 : Fin 1 → ℝ)) {t : ℝ≥0∞} (ht0 : 0 < t)
    (htz : (2 : ℝ≥0∞) * (4 * Peierls.crossingBound t) < 1) :
    ∀ᶠ β : ℝ in atTop, ∃ h ∈ U₀,
      ∀ (hmeas : Measurable fun ζ ↦
            β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
        (hM : ∃ M : ℝ, ∀ ζ,
            M ≤ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ),
      ∃ ρ : Fin 3 → Measure ((Fin 2 → ℤ) → Fin 3),
        (∀ n, IsProbabilityMeasure (ρ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (Fin 3)
          (fun ζ ↦ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
          blumeCapelPrior hmeas hM) (ρ n)) ∧
        (∀ (n : Fin 3) (a : Fin 2 → ℤ),
          MeasurePreserving (shift (Fin 3) a).toFun (ρ n) (ρ n)) ∧
        (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
        (∀ n, ρ n {ω | (latticeOceanPart (Fin 3) (blumeCapelFinePartition n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - (2 : ℝ≥0∞) * (4 * Peierls.crossingBound t)
          ≤ ρ n {ω | (0 : Peierls.Site) ∈
              latticeOceanPart (Fin 3) (blumeCapelFinePartition n) ω}) ∧
        (3 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec (Fin 3)
          (fun ζ ↦ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
          blumeCapelPrior hmeas hM)
          (shiftGroup (Fin 2 → ℤ) (Fin 3))).extremePoints ℝ≥0∞).encard := by
  classical
  obtain ⟨U, hres⟩ := resolves_blumeCapel
  have hN : ((1 : ℕ) : ℝ≥0∞) + 1 = 2 := by norm_num
  filter_upwards [eventually_exists_gibbsMeasure_family_of_resolvesOn
    (E := Fin 3) (ν := blumeCapelPrior) (N := 1) (φ := blumeCapelCube) (M₀ := 0)
    (Ψ := fun _ ↦ blumeCapelField) (b := fun _ ↦ 4) (G := blumeCapelPartition)
    (K := fun _ ↦ (Set.univ : Set (Fin 3))) (U := U) (U₀ := U₀)
    measurable_blumeCapelCube blumeCapelCube_nonneg blumeCapelCube_cubeRefl
    (fun _ ↦ measurable_blumeCapelField) (fun _ ζ ↦ abs_blumeCapelField_le ζ)
    (fun _ ↦ by norm_num) (fun _ k ζ ↦ blumeCapelField_cubeRefl k ζ)
    isCubeConfining_blumeCapelCube isPStablePartition_blumeCapel
    measurableSet_blumeCapelPartition isRSymmetric_blumeCapelPartition
    attainsGroundEnergy_blumeCapel hres hU₀ ht0 (by rw [hN]; exact htz)] with β hβ
  obtain ⟨h, hhU₀, hfam⟩ := hβ
  refine ⟨h, hhU₀, fun hmeas hM ↦ ?_⟩
  obtain ⟨ρ', hprob', hgibbs', hinv', -, -, hocean', horigin', hsym'⟩ := hfam hmeas hM
  have : IsProbabilityMeasure (ρ' 1) := hprob' 1
  have horigin'' : ∀ n : Fin 2, 1 - (2 : ℝ≥0∞) * (4 * Peierls.crossingBound t)
      ≤ ρ' n {ω | (0 : Peierls.Site) ∈
          latticeOceanPart (Fin 3) (blumeCapelPartition n) ω} := by
    intro n
    have hn := horigin' n
    rwa [hN] at hn
  -- Georgii's reflection `r_0`, and his spin flip `σ ↦ -σ`, preserve the second phase
  have hreflMP : MeasurePreserving
      ((CubeTransformation.refl (E := Fin 3) (d := 2) 0).onLattice (Fin 3)).toFun
        (ρ' 1) (ρ' 1) :=
    hsym' 1 (CubeTransformation.refl 0) (fun _ ↦ MeasurePreserving.id _)
      (fun ζ ↦ by rw [CubeTransformation.refl_onCube_toFun]; exact blumeCapelCube_cubeRefl 0 ζ)
      (fun _ ζ ↦ by
        rw [CubeTransformation.refl_onCube_toFun]; exact blumeCapelField_cubeRefl 0 ζ)
      (by
        rw [CubeTransformation.refl_onCube_toFun]
        exact (isRSymmetric_blumeCapelPartition 1).image_cubeRefl 0)
  have hflipMP : MeasurePreserving
      (blumeCapelSpinFlip.onLattice (Fin 3)).toFun (ρ' 1) (ρ' 1) :=
    hsym' 1 blumeCapelSpinFlip (fun _ ↦ measurePreserving_blumeCapelFlip)
      blumeCapelCube_onCube_blumeCapelSpinFlip
      (fun _ ζ ↦ blumeCapelField_onCube_blumeCapelSpinFlip ζ)
      image_onCube_blumeCapelSpinFlip_partition_one
  have htrans : ∀ ℓ ℓ' : Fin 2, ∃ τ : CubeTransformation (Fin 3) 2,
      MeasurePreserving (τ.onLattice (Fin 3)).toFun (ρ' 1) (ρ' 1) ∧
        τ.onCube.toFun '' blumeCapelSplitPartition ℓ = blumeCapelSplitPartition ℓ' := by
    intro ℓ ℓ'
    by_cases hll : ℓ = ℓ'
    · subst hll
      refine ⟨CubeTransformation.refl 0, hreflMP, ?_⟩
      rw [CubeTransformation.refl_onCube_toFun]
      exact (isRSymmetric_blumeCapelSplitPartition ℓ).image_cubeRefl 0
    · refine ⟨blumeCapelSpinFlip, hflipMP, ?_⟩
      fin_cases ℓ <;> fin_cases ℓ' <;>
        first
          | exact absurd rfl hll
          | exact image_onCube_blumeCapelSpinFlip_split_zero
          | exact image_onCube_blumeCapelSpinFlip_split_one
  have hμ1 : ρ' 1 {ω | (latticeOceanPart (Fin 3)
      (⋃ ℓ, blumeCapelSplitPartition ℓ) ω).Nonempty} = 1 := by
    rw [iUnion_blumeCapelSplitPartition]
    exact hocean' 1
  -- Georgii, Corollary (19.7): the second phase splits along the spin flip
  obtain ⟨σ, hσprob, hσgibbs, -, -, -, hσocean, hσorigin, hσshift, -⟩ :=
    exists_gibbsMeasure_refinement (E := Fin 3) (k := 2) (μ := ρ' 1)
      (φ₀ := fun ζ ↦ blumeCapelCube ζ - blumeCapelField ζ) (G := blumeCapelSplitPartition)
      hmeas hM isPStablePartition_blumeCapelSplit measurableSet_blumeCapelSplitPartition
      (hgibbs' 1) hμ1 htrans
  set ρ : Fin 3 → Measure ((Fin 2 → ℤ) → Fin 3) := Fin.cons (ρ' 0) σ with hρdef
  have hprob : ∀ n, IsProbabilityMeasure (ρ n) := by
    refine Fin.cases ?_ fun ℓ ↦ ?_
    · rw [hρdef, Fin.cons_zero]; exact hprob' 0
    · rw [hρdef, Fin.cons_succ]; exact hσprob ℓ
  have hgibbs : ∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (Fin 3)
      (fun ζ ↦ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
      blumeCapelPrior hmeas hM) (ρ n) := by
    refine Fin.cases ?_ fun ℓ ↦ ?_
    · rw [hρdef, Fin.cons_zero]; exact hgibbs' 0
    · rw [hρdef, Fin.cons_succ]; exact hσgibbs ℓ
  have hinv : ∀ (n : Fin 3) (a : Fin 2 → ℤ),
      MeasurePreserving (shift (Fin 3) a).toFun (ρ n) (ρ n) := by
    refine Fin.cases ?_ fun ℓ a ↦ ?_
    · intro a; rw [hρdef, Fin.cons_zero]; exact hinv' 0 a
    · rw [hρdef, Fin.cons_succ]
      exact hσshift ℓ a (hinv' 1 a)
        ((isRSymmetric_blumeCapelSplitPartition ℓ).preimage_tauPow _)
  have hself : ∀ n, ρ n
      {ω | (latticeOceanPart (Fin 3) (blumeCapelFinePartition n) ω).Nonempty} = 1 := by
    refine Fin.cases ?_ fun ℓ ↦ ?_
    · rw [hρdef, Fin.cons_zero, blumeCapelFinePartition_zero]; exact hocean' 0
    · rw [hρdef, Fin.cons_succ, blumeCapelFinePartition_succ]; exact hσocean ℓ
  have hzero : ∀ m n : Fin 3, m ≠ n →
      ρ n {ω | (latticeOceanPart (Fin 3) (blumeCapelFinePartition m) ω).Nonempty} = 0 := by
    intro m n hmn
    have := hprob n
    have hsub : {ω : (Fin 2 → ℤ) → Fin 3 |
          (latticeOceanPart (Fin 3) (blumeCapelFinePartition m) ω).Nonempty}
        ⊆ {ω : (Fin 2 → ℤ) → Fin 3 |
          (latticeOceanPart (Fin 3) (blumeCapelFinePartition n) ω).Nonempty}ᶜ :=
      Set.disjoint_left.1
        (isPStablePartition_blumeCapelFine.disjoint_setOf_latticeOceanPart_nonempty hmn)
    refine le_antisymm (le_trans (measure_mono hsub) (le_of_eq ?_)) zero_le
    rw [prob_compl_eq_one_sub (measurableSet_setOf_latticeOceanPart_nonempty
      (measurableSet_blumeCapelFinePartition n)), hself n, tsub_self]
  refine ⟨ρ, hprob, hgibbs, hinv, ?_, ?_, hself, ?_, ?_⟩
  · intro m n hmn
    have := hprob m
    refine ⟨{ω : (Fin 2 → ℤ) → Fin 3 |
        (latticeOceanPart (Fin 3) (blumeCapelFinePartition m) ω).Nonempty}ᶜ,
      (measurableSet_setOf_latticeOceanPart_nonempty
        (measurableSet_blumeCapelFinePartition m)).compl, ?_, ?_⟩
    · rw [prob_compl_eq_one_sub (measurableSet_setOf_latticeOceanPart_nonempty
        (measurableSet_blumeCapelFinePartition m)), hself m, tsub_self]
    · rw [compl_compl]
      exact hzero m n hmn
  · intro m n hmn
    by_contra hne
    have h1 := hself m
    rw [hmn, hzero m n hne] at h1
    exact zero_ne_one h1
  · refine Fin.cases ?_ fun ℓ ↦ ?_
    · rw [hρdef, Fin.cons_zero, blumeCapelFinePartition_zero]
      exact horigin'' 0
    · rw [hρdef, Fin.cons_succ, blumeCapelFinePartition_succ, hσorigin ℓ,
        iUnion_blumeCapelSplitPartition]
      exact horigin'' 1
  · have hcount := le_encard_extremePoints_of_latticeOceanPart (ν := blumeCapelPrior)
      (φ₀ := blumeCapelCube) isPStablePartition_blumeCapelFine
      measurableSet_blumeCapelFinePartition hprob hgibbs hinv hself
    exact_mod_cast hcount

/-- The crossing weight `t = 1/64` is small enough for Theorem (19.6) with `N + 1 = 2` members:
`z(t) ≤ 4t = 1/16` by `Peierls.crossingBound_le_four_mul`, so `2 · 4 z(t) ≤ 1/2 < 1`. -/
lemma blumeCapel_crossingBound_lt_one :
    (2 : ℝ≥0∞) * (4 * Peierls.crossingBound 64⁻¹) < 1 := by
  have h64 : (64 : ℝ≥0∞) ≠ 0 := by norm_num
  have h64t : (64 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hle : Peierls.crossingBound (64 : ℝ≥0∞)⁻¹ ≤ 4 * 64⁻¹ :=
    Peierls.crossingBound_le_four_mul (ENNReal.inv_le_inv.2 (by norm_num))
  calc (2 : ℝ≥0∞) * (4 * Peierls.crossingBound 64⁻¹) ≤ 2 * (4 * (4 * 64⁻¹)) := by gcongr
    _ = 64⁻¹ * 32 := by ring
    _ < 64⁻¹ * 64 :=
        ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 h64t) (ENNReal.inv_ne_top.2 h64)
          (by norm_num)
    _ = 1 := ENNReal.inv_mul_cancel h64 h64t

/-- **Georgii, Example (19.8), as he states it.**  For all sufficiently large `β` there is a
parameter `h(β)`, lying in an arbitrarily prescribed neighbourhood of the origin — Georgii's
`h(β) → 0` — with

`|ex 𝒢_Θ(βΦ + βh(β)Φ^1)| ≥ 3`.

This is `eventually_exists_gibbsMeasure_family_blumeCapel` at the crossing weight `t = 1/64`. -/
theorem eventually_three_le_encard_extremePoints_blumeCapel {U₀ : Set (Fin 1 → ℝ)}
    (hU₀ : U₀ ∈ 𝓝 (0 : Fin 1 → ℝ)) :
    ∀ᶠ β : ℝ in atTop, ∃ h ∈ U₀,
      ∀ (hmeas : Measurable fun ζ ↦
            β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
        (hM : ∃ M : ℝ, ∀ ζ,
            M ≤ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ),
        (3 : ℕ∞) ≤ ((invariantG (cubeGibbsSpec (Fin 3)
          (fun ζ ↦ β * perturb blumeCapelCube (fun _ : Fin 1 ↦ blumeCapelField) h ζ)
          blumeCapelPrior hmeas hM)
          (shiftGroup (Fin 2 → ℤ) (Fin 3))).extremePoints ℝ≥0∞).encard := by
  filter_upwards [eventually_exists_gibbsMeasure_family_blumeCapel hU₀ (t := 64⁻¹)
    (ENNReal.inv_pos.2 (by norm_num)) blumeCapel_crossingBound_lt_one] with β hβ
  obtain ⟨h, hhU₀, hfam⟩ := hβ
  refine ⟨h, hhU₀, fun hmeas hM ↦ ?_⟩
  obtain ⟨ρ, -, -, -, -, -, -, -, hcount⟩ := hfam hmeas hM
  exact hcount

end MeasureTheory.GibbsMeasure

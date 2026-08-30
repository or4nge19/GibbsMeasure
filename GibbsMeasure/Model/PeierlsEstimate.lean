/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Contours
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# The Peierls argument for the two-dimensional Ising model, topology-free half

Georgii, *Gibbs Measures and Phase Transitions*, Section 6.2, towards Theorem (6.9).

* `discordant_flip`, `bijOn_flip`: flipping the spins on `D` toggles exactly the boundary
  bonds `B*(τ_D ζ) ∆ B*(ζ) = ∂D`, a bijection between the configurations with no discordant
  boundary bond and those whose boundary bonds are all discordant (proof of (6.15)).
* `hamiltonian_eq`: the Ising energy identity `-H_Λ(ζ) = |B| - 2|B*(ζ)|`, the first display
  in the proof of (6.15), for the Ising potential with coupling `1` and no external field.
* `isingSpecification_edgeBoundary_subset_discordant_le`: the contour estimate (6.15) in
  edge-boundary form, `γ_Λ^{βΦ}({∂D ⊆ B*(·)} | ω) ≤ e^{-2β|∂D|}` for finite `D ⊆ Λ`.
* `finite_connectedBondSets`, `ncard_connectedBondSets_le_pow`: the counting bound (6.13)
  with plaquette adjacency — at most `4096^ℓ` connected (in `bondGraph`) sets of `ℓ` bonds
  contain a given bond, via a doubled spanning-walk encoding
  (`exists_spanning_closed_walk`, `support_mem_walkLists`).

The counting bound `ncard_connectedBondSets_le_pow` is `4096 ^ ℓ`, weaker than Georgii's
`ℓ · 3 ^ (ℓ - 1)`: only a constant to the `ℓ` is needed for (6.9), at the cost of a larger
threshold `β₀`. The estimate is indexed by `edgeBoundary D` while the counting is indexed by
`outerBoundary D`; `GibbsMeasure/Model/PhaseTransition.lean` bridges them through `interiorOf`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### Membership lemmas -/

lemma mem_discordant_mk {ζ : Site → Bool} {i j : Site} :
    s(i, j) ∈ discordant ζ ↔ (latticeGraph 2).Adj i j ∧ ζ i ≠ ζ j := by
  constructor
  · rintro ⟨hadj, i', j', hij, hne⟩
    refine ⟨by simpa using hadj, ?_⟩
    rcases Sym2.eq_iff.1 hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact hne.symm
  · rintro ⟨hadj, hne⟩
    exact ⟨by simpa using hadj, i, j, rfl, hne⟩

lemma mem_edgeBoundary_mk {D : Set Site} {i j : Site} :
    s(i, j) ∈ edgeBoundary D ↔
      (latticeGraph 2).Adj i j ∧ ((i ∈ D ∧ j ∉ D) ∨ (j ∈ D ∧ i ∉ D)) := by
  constructor
  · rintro ⟨i', hi', j', hj', hadj, hij⟩
    rcases Sym2.eq_iff.1 hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hadj, Or.inl ⟨hi', hj'⟩⟩
    · exact ⟨hadj.symm, Or.inr ⟨hi', hj'⟩⟩
  · rintro ⟨hadj, ⟨hi, hj⟩ | ⟨hj, hi⟩⟩
    · exact ⟨i, hi, j, hj, hadj, rfl⟩
    · exact ⟨j, hj, i, hi, hadj.symm, Sym2.eq_swap⟩

lemma edgeBoundary_subset_edgeSet (D : Set Site) :
    edgeBoundary D ⊆ (latticeGraph 2).edgeSet := by
  rintro e ⟨i, -, j, -, hadj, rfl⟩
  exact hadj

lemma discordant_subset_edgeSet (ζ : Site → Bool) :
    discordant ζ ⊆ (latticeGraph 2).edgeSet := fun _ he ↦ he.1

@[simp] lemma flip_apply_of_mem {D : Set Site} {ζ : Site → Bool} {i : Site} (hi : i ∈ D) :
    flip D ζ i = !ζ i := by simp [flip, hi]

@[simp] lemma flip_apply_of_notMem {D : Set Site} {ζ : Site → Bool} {i : Site} (hi : i ∉ D) :
    flip D ζ i = ζ i := by simp [flip, hi]

/-- Flipping twice is the identity. -/
@[simp] lemma flip_flip (D : Set Site) (ζ : Site → Bool) : flip D (flip D ζ) = ζ := by
  funext i
  by_cases hi : i ∈ D <;> simp [flip, hi]

lemma flip_involutive (D : Set Site) : Function.Involutive (flip D) := flip_flip D

/-- **Flipping `D` toggles exactly the boundary bonds** (Georgii, proof of (6.15):
`B*(τ_c ζ) ∆ B*(ζ) = c`). -/
theorem discordant_flip (D : Set Site) (ζ : Site → Bool) :
    discordant (flip D ζ) = discordant ζ ∆ edgeBoundary D := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    rw [mem_symmDiff, mem_discordant_mk, mem_discordant_mk, mem_edgeBoundary_mk]
    by_cases hi : i ∈ D <;> by_cases hj : j ∈ D <;> simp [hi, hj] <;> tauto


/-! ### M1: the flip bijection (Georgii, proof of (6.15)) -/

/-- `∂D ⊆ B*(τ_D ζ)` iff `∂D ∩ B*(ζ) = ∅`. -/
lemma edgeBoundary_subset_discordant_flip_iff (D : Set Site) (ζ : Site → Bool) :
    edgeBoundary D ⊆ discordant (flip D ζ) ↔ Disjoint (edgeBoundary D) (discordant ζ) := by
  rw [discordant_flip, Set.disjoint_left]
  constructor
  · intro h e he hed
    have := h he
    rw [Set.mem_symmDiff] at this
    rcases this with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2 he
    · exact h2 hed
  · intro h e he
    rw [Set.mem_symmDiff]
    exact Or.inr ⟨he, h he⟩

lemma flip_apply_of_notMem_of_subset {D Λ : Set Site} (hD : D ⊆ Λ) (ζ : Site → Bool) {i : Site}
    (hi : i ∉ Λ) : flip D ζ i = ζ i :=
  flip_apply_of_notMem fun h ↦ hi (hD h)

/-- **Georgii, proof of (6.15)**: `τ_D` is a bijection from `A₂` (no discordant bond on `∂D`) onto
`A₁` (all bonds of `∂D` discordant), within the configurations agreeing with `ω` off `Λ ⊇ D`. -/
theorem bijOn_flip {D Λ : Set Site} (hD : D ⊆ Λ) (ω : Site → Bool) :
    Set.BijOn (flip D)
      {ζ | Disjoint (edgeBoundary D) (discordant ζ) ∧ ∀ i ∉ Λ, ζ i = ω i}
      {ζ | edgeBoundary D ⊆ discordant ζ ∧ ∀ i ∉ Λ, ζ i = ω i} := by
  refine Set.InvOn.bijOn (f' := flip D) ⟨fun ζ _ ↦ flip_flip D ζ, fun ζ _ ↦ flip_flip D ζ⟩ ?_ ?_
  · rintro ζ ⟨h1, h2⟩
    exact ⟨(edgeBoundary_subset_discordant_flip_iff D ζ).2 h1,
      fun i hi ↦ (flip_apply_of_notMem_of_subset hD ζ hi).trans (h2 i hi)⟩
  · rintro ζ ⟨h1, h2⟩
    refine ⟨?_, fun i hi ↦ (flip_apply_of_notMem_of_subset hD ζ hi).trans (h2 i hi)⟩
    exact (edgeBoundary_subset_discordant_flip_iff D (flip D ζ)).1 (by rwa [flip_flip])

/-! ### M2: the Ising energy identity (Georgii, proof of (6.15), first display) -/

/-- Georgii (6.11): the nearest-neighbour bonds meeting `Λ`. -/
def bondsMeeting (Λ : Finset Site) : Finset (Sym2 Site) :=
  Λ.biUnion fun i ↦ (latticeGraph 2).incidenceFinset i

lemma mem_bondsMeeting {Λ : Finset Site} {e : Sym2 Site} :
    e ∈ bondsMeeting Λ ↔ e ∈ (latticeGraph 2).edgeSet ∧ ∃ i ∈ Λ, i ∈ e := by
  simp only [bondsMeeting, Finset.mem_biUnion, SimpleGraph.mem_incidenceFinset,
    SimpleGraph.incidenceSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, he, hie⟩
    exact ⟨he, i, hi, hie⟩
  · rintro ⟨he, i, hi, hie⟩
    exact ⟨i, hi, he, hie⟩

lemma mem_bondsMeeting_mk {Λ : Finset Site} {i j : Site} :
    s(i, j) ∈ bondsMeeting Λ ↔ (latticeGraph 2).Adj i j ∧ (i ∈ Λ ∨ j ∈ Λ) := by
  rw [mem_bondsMeeting, SimpleGraph.mem_edgeSet]
  simp only [Sym2.mem_iff]
  constructor
  · rintro ⟨h, k, hk, rfl | rfl⟩
    · exact ⟨h, Or.inl hk⟩
    · exact ⟨h, Or.inr hk⟩
  · rintro ⟨h, hk | hk⟩
    · exact ⟨h, i, hk, Or.inl rfl⟩
    · exact ⟨h, j, hk, Or.inr rfl⟩

lemma edgeBoundary_subset_bondsMeeting {D Λ : Finset Site} (hD : D ⊆ Λ) :
    edgeBoundary ↑D ⊆ ↑(bondsMeeting Λ) := by
  rintro e ⟨i, hi, j, -, hadj, rfl⟩
  exact Finset.mem_coe.2 (mem_bondsMeeting_mk.2 ⟨hadj, Or.inl (hD hi)⟩)

lemma edgeBoundary_finset_finite (D : Finset Site) : (edgeBoundary ↑D).Finite :=
  edgeBoundary_finite D.finite_toSet

lemma spin_mul_spin (a b : Bool) : spin a * spin b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [spin]

/-- The Ising interaction on a bond: `Φ_{i,j} = -σ_i σ_j` (Georgii (6.8)). -/
lemma isingPotential_pair {i j : Site} (hij : (latticeGraph 2).Adj i j) (ζ : Site → Bool) :
    isingPotential (latticeGraph 2) 1 0 {i, j} ζ = -(spin (ζ i) * spin (ζ j)) := by
  rw [isingPotential, Potential.nearestNeighbourPair_apply_pair
    ⟨Finset.card_pair hij.ne, i, by simp, j, by simp, hij⟩, Finset.prod_pair hij.ne]
  ring

/-- The Ising interaction vanishes off the bonds (Georgii (6.8)). -/
lemma isingPotential_eq_zero {A : Finset Site} (ζ : Site → Bool)
    (hA : ¬ ∃ i j, (latticeGraph 2).Adj i j ∧ A = {i, j}) :
    isingPotential (latticeGraph 2) 1 0 A ζ = 0 := by
  by_cases h1 : A.card = 1
  · rw [isingPotential, Potential.nearestNeighbourPair_apply_card_one h1]
    simp
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, (latticeGraph 2).Adj i j
    · exfalso
      obtain ⟨hcard, i, hi, j, hj, hij⟩ := h2
      refine hA ⟨i, j, hij, ?_⟩
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hi
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact hj
      · exact le_of_eq (by rw [hcard, Finset.card_pair hij.ne])
    · rw [isingPotential]
      exact Potential.nearestNeighbourPair_apply_eq_zero h1 h2 ζ

lemma hamiltonianTerms_eq_zero_of_notMem {Λ : Finset Site} (ζ : Site → Bool) {A : Finset Site}
    (hA : A ∉ (bondsMeeting Λ).image Sym2.toFinset) :
    (isingPotential (latticeGraph 2) 1 0).hamiltonianTerms Λ ζ A = 0 := by
  by_cases hdisj : Disjoint A Λ
  · exact Potential.hamiltonianTerms_of_disjoint hdisj ζ
  rw [Potential.hamiltonianTerms_of_not_disjoint hdisj]
  refine isingPotential_eq_zero ζ ?_
  rintro ⟨i, j, hij, rfl⟩
  refine hA (Finset.mem_image.2 ⟨s(i, j), ?_, Sym2.toFinset_mk_eq⟩)
  obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hdisj
  refine mem_bondsMeeting_mk.2 ⟨hij, ?_⟩
  rcases Finset.mem_insert.1 hxA with rfl | hx
  · exact Or.inl hxΛ
  · rw [Finset.mem_singleton] at hx
    subst hx
    exact Or.inr hxΛ

lemma toFinset_injOn_bondsMeeting (Λ : Finset Site) :
    Set.InjOn Sym2.toFinset ((bondsMeeting Λ : Finset (Sym2 Site)) : Set (Sym2 Site)) := by
  intro e he f hf hef
  induction e using Sym2.ind with
  | _ a b =>
  induction f using Sym2.ind with
  | _ c d =>
  have hab : a ≠ b := (mem_bondsMeeting_mk.1 (Finset.mem_coe.1 he)).1.ne
  have hcd : c ≠ d := (mem_bondsMeeting_mk.1 (Finset.mem_coe.1 hf)).1.ne
  rw [Sym2.toFinset_mk_eq, Sym2.toFinset_mk_eq] at hef
  have hc : c ∈ ({a, b} : Finset Site) := hef ▸ Finset.mem_insert_self c {d}
  have hd : d ∈ ({a, b} : Finset Site) :=
    hef ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self d)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact absurd rfl hcd
  · rfl
  · exact Sym2.eq_swap
  · exact absurd rfl hcd

open Classical in
lemma hamiltonianTerms_toFinset {Λ : Finset Site} (ζ : Site → Bool) {e : Sym2 Site}
    (he : e ∈ bondsMeeting Λ) :
    (isingPotential (latticeGraph 2) 1 0).hamiltonianTerms Λ ζ e.toFinset =
      -(1 - 2 * if e ∈ discordant ζ then 1 else 0) := by
  induction e using Sym2.ind with
  | _ i j =>
  obtain ⟨hij, hΛ⟩ := mem_bondsMeeting_mk.1 he
  have hnd : ¬ Disjoint s(i, j).toFinset Λ := by
    rw [Sym2.toFinset_mk_eq, Finset.not_disjoint_iff]
    rcases hΛ with h | h
    · exact ⟨i, by simp, h⟩
    · exact ⟨j, by simp, h⟩
  rw [Potential.hamiltonianTerms_of_not_disjoint hnd, Sym2.toFinset_mk_eq, isingPotential_pair hij,
    spin_mul_spin, mem_discordant_mk]
  rcases eq_or_ne (ζ i) (ζ j) with h | h
  · simp [h, hij]
  · simp [h, hij]
    norm_num


open Classical in
lemma hamiltonian_eq_card_filter (Λ : Finset Site) (ζ : Site → Bool) :
    (isingPotential (latticeGraph 2) 1 0).hamiltonian Λ ζ =
      -(((bondsMeeting Λ).card : ℝ) -
        2 * (((bondsMeeting Λ).filter (· ∈ discordant ζ)).card : ℝ)) := by
  rw [Potential.hamiltonian_eq_tsum, tsum_eq_sum (s := (bondsMeeting Λ).image Sym2.toFinset)
    (fun A hA ↦ hamiltonianTerms_eq_zero_of_notMem ζ hA),
    Finset.sum_image (toFinset_injOn_bondsMeeting Λ),
    Finset.sum_congr rfl (fun e he ↦ hamiltonianTerms_toFinset ζ he),
    Finset.sum_neg_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Georgii, proof of (6.15), first display**: `-H_Λ(ζ) = |B| - 2|B*(ζ)|` for the Ising potential
with coupling `1` and no field, where `B` is the set of bonds meeting `Λ`. -/
theorem hamiltonian_eq (Λ : Finset Site) (ζ : Site → Bool) :
    (isingPotential (latticeGraph 2) 1 0).hamiltonian Λ ζ =
      -(((bondsMeeting Λ).card : ℝ) - 2 * ((↑(bondsMeeting Λ) ∩ discordant ζ).ncard : ℝ)) := by
  classical
  rw [hamiltonian_eq_card_filter]
  have : (↑(bondsMeeting Λ) ∩ discordant ζ : Set (Sym2 Site)) =
      ↑((bondsMeeting Λ).filter (· ∈ discordant ζ)) := by
    ext e
    simp
  rw [this, Set.ncard_coe_finset]

/-! ### M3: the contour estimate, Georgii (6.15) in edge-boundary form -/

lemma ncard_inter_discordant_flip {Λ D : Finset Site} (hD : D ⊆ Λ) {ζ : Site → Bool}
    (hζ : Disjoint (edgeBoundary ↑D) (discordant ζ)) :
    (↑(bondsMeeting Λ) ∩ discordant (flip ↑D ζ)).ncard =
      (↑(bondsMeeting Λ) ∩ discordant ζ).ncard + (edgeBoundary ↑D).ncard := by
  have h1 : discordant (flip ↑D ζ) = discordant ζ ∪ edgeBoundary ↑D := by
    rw [discordant_flip]
    exact hζ.symm.symmDiff_eq_sup
  rw [h1, Set.inter_union_distrib_left,
    Set.inter_eq_right.2 (edgeBoundary_subset_bondsMeeting hD)]
  exact Set.ncard_union_eq (hζ.symm.mono_left Set.inter_subset_right)
    ((Finset.finite_toSet _).inter_of_left _) (edgeBoundary_finset_finite D)

/-- Flipping the spins in `D` raises the energy by exactly `2|∂D|` when no bond of `∂D` is
discordant (Georgii, proof of (6.15)). -/
lemma hamiltonian_flip {Λ D : Finset Site} (hD : D ⊆ Λ) {ζ : Site → Bool}
    (hζ : Disjoint (edgeBoundary ↑D) (discordant ζ)) :
    (isingPotential (latticeGraph 2) 1 0).hamiltonian Λ (flip ↑D ζ) =
      (isingPotential (latticeGraph 2) 1 0).hamiltonian Λ ζ + 2 * (edgeBoundary ↑D).ncard := by
  rw [hamiltonian_eq, hamiltonian_eq, ncard_inter_discordant_flip hD hζ]
  push_cast
  ring

lemma boltzmannFactor_flip (β : ℝ) {Λ D : Finset Site} (hD : D ⊆ Λ) {ζ : Site → Bool}
    (hζ : Disjoint (edgeBoundary ↑D) (discordant ζ)) :
    (isingPotential (latticeGraph 2) 1 0).boltzmannFactor β Λ (flip ↑D ζ) =
      ENNReal.ofReal (Real.exp (-2 * β * (edgeBoundary ↑D).ncard)) *
        (isingPotential (latticeGraph 2) 1 0).boltzmannFactor β Λ ζ := by
  rw [Potential.boltzmannFactor, Potential.boltzmannFactor, hamiltonian_flip hD hζ,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

lemma measurableSet_mem_discordant (e : Sym2 Site) :
    MeasurableSet {ζ : Site → Bool | e ∈ discordant ζ} := by
  induction e using Sym2.ind with
  | _ i j =>
  simp only [mem_discordant_mk]
  by_cases hij : (latticeGraph 2).Adj i j
  · simp only [hij, true_and]
    exact (measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)).compl
  · simp [hij]

lemma measurableSet_edgeBoundary_subset_discordant (D : Finset Site) :
    MeasurableSet {ζ : Site → Bool | edgeBoundary ↑D ⊆ discordant ζ} := by
  have : {ζ : Site → Bool | edgeBoundary ↑D ⊆ discordant ζ} =
      ⋂ e ∈ edgeBoundary ↑D, {ζ | e ∈ discordant ζ} := by
    ext ζ
    simp [Set.subset_def]
  rw [this]
  exact (edgeBoundary_finset_finite D).measurableSet_biInter fun e _ ↦ measurableSet_mem_discordant e

lemma measurableSet_disjoint_edgeBoundary_discordant (D : Finset Site) :
    MeasurableSet {ζ : Site → Bool | Disjoint (edgeBoundary ↑D) (discordant ζ)} := by
  have : {ζ : Site → Bool | Disjoint (edgeBoundary ↑D) (discordant ζ)} =
      ⋂ e ∈ edgeBoundary ↑D, {ζ | e ∈ discordant ζ}ᶜ := by
    ext ζ
    simp [Set.disjoint_left]
  rw [this]
  exact (edgeBoundary_finset_finite D).measurableSet_biInter
    fun e _ ↦ (measurableSet_mem_discordant e).compl

/-- The flip of the coordinates in `D` on the finite-volume configurations `Λ → Bool`. -/
def flipRestrict (Λ D : Finset Site) (x : ↥Λ → Bool) : ↥Λ → Bool :=
  fun i ↦ if (i : Site) ∈ D then !x i else x i

lemma flipRestrict_flipRestrict (Λ D : Finset Site) (x : ↥Λ → Bool) :
    flipRestrict Λ D (flipRestrict Λ D x) = x := by
  funext i
  by_cases h : (i : Site) ∈ D <;> simp [flipRestrict, h]

/-- `flipRestrict` as a permutation of `Λ → Bool`. -/
def flipEquiv (Λ D : Finset Site) : (↥Λ → Bool) ≃ (↥Λ → Bool) :=
  Function.Involutive.toPerm _ (flipRestrict_flipRestrict Λ D)

lemma juxt_flipRestrict {Λ D : Finset Site} (hD : D ⊆ Λ) (ω : Site → Bool) (x : ↥Λ → Bool) :
    juxt (↑Λ) ω (flipRestrict Λ D x) = flip ↑D (juxt (↑Λ) ω x) := by
  funext i
  by_cases hi : i ∈ Λ
  · simp [juxt, flip, flipRestrict, hi]
  · have hiD : i ∉ D := fun h ↦ hi (hD h)
    simp [juxt, flip, hi, hiD]

lemma pi_uniformSpinMeasure_singleton (Λ : Finset Site) (x : ↥Λ → Bool) :
    (Measure.pi fun _ : ↥Λ ↦ uniformSpinMeasure) {x} = (2⁻¹ : ℝ≥0∞) ^ Λ.card := by
  rw [Measure.pi_singleton]
  have h : ∀ b : Bool, uniformSpinMeasure {b} = 2⁻¹ := fun b ↦ by
    simp [uniformSpinMeasure]
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- The independent kernel with uniform spins, integrated against a measurable function, is a
finite sum over `Λ → Bool` with the uniform weight `2^{-|Λ|}`. -/
lemma lintegral_isssd_uniformSpinMeasure (Λ : Finset Site) (ω : Site → Bool)
    {f : (Site → Bool) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ζ, f ζ ∂(Specification.isssd uniformSpinMeasure Λ ω) =
      ∑ x : ↥Λ → Bool, f (juxt (↑Λ) ω x) * (2⁻¹ : ℝ≥0∞) ^ Λ.card := by
  change ∫⁻ ζ, f ζ ∂(Measure.map (juxt (↑Λ) ω) (Measure.pi fun _ : ↥Λ ↦ uniformSpinMeasure)) = _
  rw [lintegral_map hf Measurable.juxt, lintegral_fintype]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [pi_uniformSpinMeasure_singleton]

/-- **Georgii (6.15) in edge-boundary form.** For the two-dimensional Ising model with coupling `1`
and no field, at any inverse temperature `β`, and any `D ⊆ Λ`, the finite-volume Gibbs
distribution in `Λ` with boundary condition `ω` gives probability at most `e^{-2β|∂D|}` to the
event that all bonds of the edge boundary `∂D` are discordant. -/
theorem isingSpecification_edgeBoundary_subset_discordant_le (β : ℝ) {Λ D : Finset Site}
    (hD : D ⊆ Λ) (ω : Site → Bool) :
    isingSpecification (latticeGraph 2) 1 0 β Λ ω {ζ | edgeBoundary ↑D ⊆ discordant ζ} ≤
      ENNReal.ofReal (Real.exp (-2 * β * (edgeBoundary ↑D).ncard)) := by
  classical
  set Φ := isingPotential (latticeGraph 2) 1 0 with hΦ
  set ν := uniformSpinMeasure with hν
  set E := ENNReal.ofReal (Real.exp (-2 * β * (edgeBoundary ↑D).ncard)) with hE
  set A₁ := {ζ : Site → Bool | edgeBoundary ↑D ⊆ discordant ζ} with hA₁def
  set A₂ := {ζ : Site → Bool | Disjoint (edgeBoundary ↑D) (discordant ζ)} with hA₂def
  have hA₁ : MeasurableSet A₁ := measurableSet_edgeBoundary_subset_discordant D
  have hA₂ : MeasurableSet A₂ := measurableSet_disjoint_edgeBoundary_discordant D
  have hρ : Specification.IsPremodifier (Φ.boltzmannFactor β) :=
    Potential.isPremodifier_boltzmannFactor β
  have hZ := Potential.isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν β Λ ω
  have hmeas : Measurable (Φ.boltzmannFactor β Λ) := Potential.measurable_boltzmannFactor β Λ
  rw [isingSpecification, Potential.gibbsSpecificationOfAbsolutelySummable,
    Specification.modification_apply, Specification.withDensity_premodifierNorm_apply ν hρ hA₁ ω]
  have key : ∫⁻ y in A₁, Φ.boltzmannFactor β Λ y ∂(Specification.isssd ν Λ ω) =
      E * ∫⁻ y in A₂, Φ.boltzmannFactor β Λ y ∂(Specification.isssd ν Λ ω) := by
    rw [← lintegral_indicator hA₁, ← lintegral_indicator hA₂,
      lintegral_isssd_uniformSpinMeasure Λ ω (hmeas.indicator hA₁),
      lintegral_isssd_uniformSpinMeasure Λ ω (hmeas.indicator hA₂), Finset.mul_sum]
    refine (Fintype.sum_equiv (flipEquiv Λ D) _ _ fun x ↦ ?_).symm
    rw [show (flipEquiv Λ D) x = flipRestrict Λ D x from rfl, juxt_flipRestrict hD]
    set ζ := juxt (↑Λ) ω x with hζdef
    by_cases hζ : Disjoint (edgeBoundary ↑D) (discordant ζ)
    · rw [Set.indicator_of_mem (show ζ ∈ A₂ from hζ),
        Set.indicator_of_mem (show flip ↑D ζ ∈ A₁ from
          (edgeBoundary_subset_discordant_flip_iff _ _).2 hζ),
        boltzmannFactor_flip β hD hζ, mul_assoc]
    · rw [Set.indicator_of_notMem (show ζ ∉ A₂ from hζ),
        Set.indicator_of_notMem (show flip ↑D ζ ∉ A₁ from
          fun h ↦ hζ ((edgeBoundary_subset_discordant_flip_iff _ _).1 h))]
      simp
  rw [key]
  calc (Specification.premodifierZ ν (Φ.boltzmannFactor β) Λ ω)⁻¹ *
        (E * ∫⁻ y in A₂, Φ.boltzmannFactor β Λ y ∂(Specification.isssd ν Λ ω))
      ≤ (Specification.premodifierZ ν (Φ.boltzmannFactor β) Λ ω)⁻¹ *
        (E * Specification.premodifierZ ν (Φ.boltzmannFactor β) Λ ω) := by
        gcongr
        exact setLIntegral_le_lintegral _ _
    _ = E := by
        rw [mul_left_comm, ENNReal.inv_mul_cancel hZ.1 hZ.2, mul_one]


/-! ### M4: the counting bound (Georgii (6.13)) -/

/-- The candidate corners of the plaquettes containing a given bond. -/
def plaquetteCorners (e : Sym2 Site) : Finset Site :=
  e.toFinset.biUnion fun a ↦ {a, a - e0, a - e1, a - e0 - e1}

/-- The candidate plaquette-neighbours of a bond, one step of a walk in `bondGraph`. -/
def stepCands (e : Sym2 Site) : Finset (Sym2 Site) :=
  (plaquetteCorners e).biUnion plaquette

lemma card_plaquette_le (x : Site) : (plaquette x).card ≤ 4 := by
  have h1 := Finset.card_insert_le s(x, x + e0)
    ({s(x, x + e1), s(x + e0, x + e0 + e1), s(x + e1, x + e0 + e1)} : Finset (Sym2 Site))
  have h2 := Finset.card_insert_le s(x, x + e1)
    ({s(x + e0, x + e0 + e1), s(x + e1, x + e0 + e1)} : Finset (Sym2 Site))
  have h3 := Finset.card_insert_le s(x + e0, x + e0 + e1)
    ({s(x + e1, x + e0 + e1)} : Finset (Sym2 Site))
  have h4 : ({s(x + e1, x + e0 + e1)} : Finset (Sym2 Site)).card = 1 := Finset.card_singleton _
  rw [plaquette]
  omega

lemma card_plaquetteCorners_le (e : Sym2 Site) : (plaquetteCorners e).card ≤ 8 := by
  rw [plaquetteCorners]
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 fun a _ ↦ ?_) ?_
  · have h1 := Finset.card_insert_le a ({a - e0, a - e1, a - e0 - e1} : Finset Site)
    have h2 := Finset.card_insert_le (a - e0) ({a - e1, a - e0 - e1} : Finset Site)
    have h3 := Finset.card_insert_le (a - e1) ({a - e0 - e1} : Finset Site)
    have h4 : ({a - e0 - e1} : Finset Site).card = 1 := Finset.card_singleton _
    omega
  · have h : e.toFinset.card ≤ 2 := by
      induction e using Sym2.ind with
      | _ a b =>
        rw [Sym2.toFinset_mk_eq]
        exact le_trans (Finset.card_insert_le _ _) (by simp)
    omega

lemma card_stepCands_le (e : Sym2 Site) : (stepCands e).card ≤ 32 := by
  rw [stepCands]
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ 4 fun x _ ↦ card_plaquette_le x) ?_
  have := card_plaquetteCorners_le e
  omega

lemma corner_mem_plaquetteCorners {e : Sym2 Site} {x : Site} (he : e ∈ plaquette x) :
    x ∈ plaquetteCorners e := by
  simp only [plaquette, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Finset.mem_biUnion.2 ⟨x, by simp [Sym2.toFinset_mk_eq], by simp⟩
  · exact Finset.mem_biUnion.2 ⟨x, by simp [Sym2.toFinset_mk_eq], by simp⟩
  · exact Finset.mem_biUnion.2 ⟨x + e0, by simp [Sym2.toFinset_mk_eq], by simp⟩
  · exact Finset.mem_biUnion.2 ⟨x + e1, by simp [Sym2.toFinset_mk_eq], by simp⟩

/-- Every `bondGraph`-neighbour of `e` is among its (at most `32`) step candidates. -/
lemma mem_stepCands_of_adj {e f : Sym2 Site} (h : bondGraph.Adj e f) : f ∈ stepCands e := by
  obtain ⟨-, x, he, hf⟩ := h
  exact Finset.mem_biUnion.2 ⟨x, corner_mem_plaquetteCorners he, hf⟩

/-- The possible support lists of length-`n` walks in `bondGraph` ending at `e₀`. -/
def walkLists (e₀ : Sym2 Site) : ℕ → Finset (List (Sym2 Site))
  | 0 => {[e₀]}
  | n + 1 => (walkLists e₀ n).biUnion fun l ↦ (stepCands (l.headD e₀)).image fun f ↦ f :: l

lemma card_walkLists_le (e₀ : Sym2 Site) : ∀ n, (walkLists e₀ n).card ≤ 32 ^ n
  | 0 => by simp [walkLists]
  | n + 1 => by
    rw [walkLists]
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 32 fun l _ ↦
      le_trans Finset.card_image_le (card_stepCands_le _)) ?_
    rw [pow_succ]
    exact Nat.mul_le_mul (card_walkLists_le e₀ n) le_rfl

/-- The support of a walk to `e₀` of length `n` is one of the lists in `walkLists e₀ n`. -/
lemma support_mem_walkLists {e₀ a : Sym2 Site} (w : bondGraph.Walk a e₀) :
    w.support ∈ walkLists e₀ w.length := by
  induction w with
  | nil => simp [walkLists]
  | @cons a v e₀ h q ih =>
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.length_cons, walkLists]
    refine Finset.mem_biUnion.2 ⟨q.support, ih, Finset.mem_image.2 ⟨a, ?_, rfl⟩⟩
    have hhead : q.support.headD e₀ = v := by
      rw [← SimpleGraph.Walk.cons_tail_support, List.headD_cons]
    rw [hhead]
    exact mem_stepCands_of_adj h.symm

/-- The inclusion of an induced subgraph of `bondGraph` into `bondGraph`. -/
def induceIncl (s : Set (Sym2 Site)) : bondGraph.induce s →g bondGraph where
  toFun := Subtype.val
  map_rel' := fun h ↦ h

/-- A walk between two bonds of a connected set `c`, staying inside `c`. -/
lemma exists_walk_of_connected {c : Finset (Sym2 Site)}
    (hconn : (bondGraph.induce (↑c : Set (Sym2 Site))).Connected) {a b : Sym2 Site}
    (ha : a ∈ c) (hb : b ∈ c) :
    ∃ p : bondGraph.Walk a b, ∀ x ∈ p.support, x ∈ c := by
  obtain ⟨q⟩ := hconn.preconnected ⟨a, Finset.mem_coe.2 ha⟩ ⟨b, Finset.mem_coe.2 hb⟩
  have hA : (induceIncl (↑c : Set (Sym2 Site))) ⟨a, Finset.mem_coe.2 ha⟩ = a := rfl
  have hB : (induceIncl (↑c : Set (Sym2 Site))) ⟨b, Finset.mem_coe.2 hb⟩ = b := rfl
  refine ⟨(q.map (induceIncl (↑c : Set (Sym2 Site)))).copy hA hB, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

/-- A walk from inside `T` to outside `T` crosses the boundary of `T`. -/
lemma exists_exit {T : Finset (Sym2 Site)} {a b : Sym2 Site} (p : bondGraph.Walk a b) :
    a ∈ T → b ∉ T →
      ∃ t u, t ∈ T ∧ u ∉ T ∧ u ∈ p.support ∧ bondGraph.Adj t u := by
  induction p with
  | nil => exact fun ha hb ↦ absurd ha hb
  | @cons a v b h q ih =>
    intro ha hb
    by_cases hv : v ∈ T
    · obtain ⟨t, u, ht, hu, hus, hadj⟩ := ih hv hb
      exact ⟨t, u, ht, hu, by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hus, hadj⟩
    · exact ⟨a, v, ha, hv, by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ q.start_mem_support, h⟩

/-- **A doubled spanning walk.** A connected finite set `c` of bonds containing `e₀` is the
support of a closed walk at `e₀` in `bondGraph` of length at most `2(|c| - 1)`. -/
lemma exists_spanning_closed_walk {c : Finset (Sym2 Site)} {e₀ : Sym2 Site}
    (hconn : (bondGraph.induce (↑c : Set (Sym2 Site))).Connected) (he₀ : e₀ ∈ c) :
    ∃ w : bondGraph.Walk e₀ e₀, (∀ x, x ∈ w.support ↔ x ∈ c) ∧
      w.length ≤ 2 * (c.card - 1) := by
  classical
  suffices h : ∀ n (T : Finset (Sym2 Site)), T ⊆ c → e₀ ∈ T → c.card - T.card = n →
      (∃ w : bondGraph.Walk e₀ e₀, (∀ x, x ∈ w.support ↔ x ∈ T) ∧
        w.length ≤ 2 * (T.card - 1)) →
      ∃ w : bondGraph.Walk e₀ e₀, (∀ x, x ∈ w.support ↔ x ∈ c) ∧
        w.length ≤ 2 * (c.card - 1) by
    refine h (c.card - 1) {e₀} (Finset.singleton_subset_iff.2 he₀)
      (Finset.mem_singleton_self e₀) (by simp) ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  intro n
  induction n with
  | zero =>
    rintro T hTc he₀T hcard ⟨w, hwsupp, hwlen⟩
    have hle : T.card ≤ c.card := Finset.card_le_card hTc
    have hT : T = c := Finset.eq_of_subset_of_card_le hTc (by omega)
    subst hT
    exact ⟨w, hwsupp, hwlen⟩
  | succ n ih =>
    rintro T hTc he₀T hcard ⟨w, hwsupp, hwlen⟩
    have hle : T.card ≤ c.card := Finset.card_le_card hTc
    have hne : T ≠ c := by
      intro h
      subst h
      omega
    obtain ⟨u, huc, huT⟩ := Finset.exists_of_ssubset (hTc.ssubset_of_ne hne)
    obtain ⟨p, hp⟩ := exists_walk_of_connected hconn (hTc he₀T) huc
    obtain ⟨t, u', ht, hu', hu's, hadj⟩ := exists_exit p he₀T huT
    have htw : t ∈ w.support := (hwsupp t).2 ht
    refine ih (insert u' T) (Finset.insert_subset (hp u' hu's) hTc)
      (Finset.mem_insert_of_mem he₀T)
      (by rw [Finset.card_insert_of_notMem hu']; omega) ?_
    refine ⟨(w.takeUntil t htw).append
      (SimpleGraph.Walk.cons hadj (SimpleGraph.Walk.cons hadj.symm (w.dropUntil t htw))),
      ?_, ?_⟩
    · intro x
      have hx : (x ∈ (w.takeUntil t htw).support ∨ x ∈ (w.dropUntil t htw).support) ↔
          x ∈ T := by
        rw [← hwsupp x]
        conv_rhs => rw [← SimpleGraph.Walk.take_spec w htw]
        rw [SimpleGraph.Walk.mem_support_append_iff]
      have htend : t ∈ (w.takeUntil t htw).support := SimpleGraph.Walk.end_mem_support _
      rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_cons, List.mem_cons, List.mem_cons, Finset.mem_insert]
      constructor
      · rintro (h | rfl | rfl | h)
        · exact Or.inr (hx.1 (Or.inl h))
        · exact Or.inr ht
        · exact Or.inl rfl
        · exact Or.inr (hx.1 (Or.inr h))
      · rintro (rfl | hxT)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · rcases hx.2 hxT with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr h))
    · have hlen : (w.takeUntil t htw).length + (w.dropUntil t htw).length = w.length := by
        have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec w htw)
        rwa [SimpleGraph.Walk.length_append] at h
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_cons, Finset.card_insert_of_notMem hu']
      have hT1 : 1 ≤ T.card := Finset.card_pos.2 ⟨e₀, he₀T⟩
      omega

/-- Georgii's contour candidates: connected sets of `ℓ` bonds containing the bond `e₀`. -/
def connectedBondSets (e₀ : Sym2 Site) (ℓ : ℕ) : Set (Finset (Sym2 Site)) :=
  {c | (bondGraph.induce (↑c : Set (Sym2 Site))).Connected ∧ e₀ ∈ c ∧ c.card = ℓ}

/-- Every connected set of `ℓ` bonds containing `e₀` is the support set of an anchored walk
list of length less than `2ℓ - 1`. -/
lemma connectedBondSets_subset_image (e₀ : Sym2 Site) (ℓ : ℕ) :
    connectedBondSets e₀ ℓ ⊆
      ↑(((Finset.range (2 * ℓ - 1)).biUnion (walkLists e₀)).image List.toFinset) := by
  rintro c ⟨hconn, he₀, hcard⟩
  obtain ⟨w, hsupp, hlen⟩ := exists_spanning_closed_walk hconn he₀
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨w.support,
    Finset.mem_biUnion.2 ⟨w.length, Finset.mem_range.2 ?_, support_mem_walkLists w⟩, ?_⟩)
  · have hℓ : 1 ≤ ℓ := hcard ▸ Finset.card_pos.2 ⟨e₀, he₀⟩
    rw [hcard] at hlen
    omega
  · ext x
    rw [List.mem_toFinset]
    exact hsupp x

/-- **Georgii (6.13), finiteness**: there are finitely many connected sets of `ℓ` bonds
containing a given bond. -/
lemma finite_connectedBondSets (e₀ : Sym2 Site) (ℓ : ℕ) : (connectedBondSets e₀ ℓ).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (connectedBondSets_subset_image e₀ ℓ)

/-- **Georgii (6.13), counting**: at most `(2ℓ - 1)·32^(2ℓ - 2)` connected sets of `ℓ` bonds
contain a given bond. -/
theorem ncard_connectedBondSets_le (e₀ : Sym2 Site) (ℓ : ℕ) :
    (connectedBondSets e₀ ℓ).ncard ≤ (2 * ℓ - 1) * 32 ^ (2 * ℓ - 2) := by
  refine le_trans (Set.ncard_le_ncard (connectedBondSets_subset_image e₀ ℓ)
    (Finset.finite_toSet _)) ?_
  rw [Set.ncard_coe_finset]
  refine le_trans Finset.card_image_le ?_
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ (32 ^ (2 * ℓ - 2)) fun L hL ↦ ?_) ?_
  · refine le_trans (card_walkLists_le e₀ L) (Nat.pow_le_pow_right (by norm_num) ?_)
    have := Finset.mem_range.1 hL
    omega
  · rw [Finset.card_range]

/-- **Georgii (6.13) in exponential form**: at most `4096^ℓ` connected sets of `ℓ` bonds
contain a given bond. -/
theorem ncard_connectedBondSets_le_pow (e₀ : Sym2 Site) (ℓ : ℕ) :
    (connectedBondSets e₀ ℓ).ncard ≤ 4096 ^ ℓ := by
  refine le_trans (ncard_connectedBondSets_le e₀ ℓ) ?_
  have h0 : 2 * ℓ < 2 ^ (2 * ℓ) := Nat.lt_two_pow_self
  have h1 : 2 * ℓ - 1 ≤ 2 ^ (2 * ℓ) := by omega
  have h2 : (32 : ℕ) ^ (2 * ℓ - 2) ≤ 32 ^ (2 * ℓ) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (2 * ℓ - 1) * 32 ^ (2 * ℓ - 2) ≤ 2 ^ (2 * ℓ) * 32 ^ (2 * ℓ) := Nat.mul_le_mul h1 h2
    _ = 64 ^ (2 * ℓ) := by rw [← Nat.mul_pow]
    _ = 4096 ^ ℓ := by rw [pow_mul]; norm_num


end MeasureTheory.GibbsMeasure.Peierls

end

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
* `exists_dual_potential`: **planar duality on `ℤ²` mod two** — a bond labelling whose vertex
  sums all vanish (a mod-two cycle) is the coboundary of a labelling of the plaquettes, i.e. of
  the indicator of the "inside" of the cycle.  This is `exists_potential` transported
  to the dual lattice by the ninety-degree rotation `rot`.
* `no_crossing_diag`, `no_crossing_antidiag`: **Georgii's excluded case `n_c(u) = 4`**, proved
  *without* the Jordan curve theorem.  Two diagonally opposite corners of a unit square cannot
  lie in a finite connected `D ⊆ ℤ²` while the other two lie in the infinite component of `Dᶜ`:
  the lattice path inside `D` joining the two corners of `D`, closed up through one of the outer
  corners (`crossChain`), is a mod-two cycle, and its dual potential separates the two outer
  corners, contradicting `reachIn_of_mem_outside` (`GibbsMeasure/Model/Contours.lean`).
* `plaquetteDeg_outerBoundary_eq_two`: **Georgii Lemma (6.14), the circuit property.**  For a
  finite, nonempty, connected `D ⊆ ℤ²`, every plaquette met by the outer boundary of `D`
  contains exactly two of its bonds — Georgii's `n_c(u) = 2`.  `n_c(u) = 1` is excluded because
  all four corners of the plaquette would lie outside `D`, `n_c(u) = 3` by the parity of the
  number of changes of `1_D` around the four corners (both are `plaquette_count`), and
  `n_c(u) = 4` by `no_crossing_diag` / `no_crossing_antidiag`.

The counting bound `ncard_connectedBondSets_le_pow` is `4096 ^ ℓ`, weaker than Georgii's
`ℓ · 3 ^ (ℓ - 1)`: only a constant to the `ℓ` is needed for (6.9), at the cost of a larger
threshold `β₀`. The estimate is indexed by `edgeBoundary D` while the counting is indexed by
`outerBoundary D`; `GibbsMeasure/Model/PhaseTransition.lean` bridges them through `interiorOf`.

Together with `outerBoundary_connected`, `plaquetteDeg_outerBoundary_eq_two` says that
the outer boundary of a finite connected `D` is a *circuit* in Georgii's sense: it is connected
in the plaquette-adjacency graph and every dual site it meets lies on exactly two of its bonds.
`GibbsMeasure/Model/SharpContours.lean` completes the step to Georgii's `ℓ · 3 ^ (ℓ - 1)`
(`PeierlsSharp.ncard_anchored_circuits_le`): it traverses that circuit one plaquette at a time,
with at most three continuations per step, anchored on the horizontal half-line from `a` by
`exists_anchor_bond` (`GibbsMeasure/Model/Contours.lean`).
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
  exact (edgeBoundary_finset_finite D).measurableSet_biInter fun e _ ↦
      measurableSet_mem_discordant e

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
  rw [MeasureTheory.GibbsMeasure.lintegral_isssd_uniformSpinMeasure Λ ω hf, Finset.sum_mul,
    Fintype.card_coe]

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

/-- Finiteness for the surrogate of Georgii (6.13) used here: there are finitely many
`bondGraph`-connected sets of `ℓ` bonds containing a given bond.  Georgii counts circuits, not
arbitrary connected bond sets; that count is `PeierlsSharp.ncard_circuitSets_le`. -/
lemma finite_connectedBondSets (e₀ : Sym2 Site) (ℓ : ℕ) : (connectedBondSets e₀ ℓ).Finite :=
  Set.Finite.subset (Finset.finite_toSet _) (connectedBondSets_subset_image e₀ ℓ)

/-- A coarse surrogate for Georgii (6.13): at most `(2ℓ - 1)·32^(2ℓ - 2)` `bondGraph`-connected
sets of `ℓ` bonds contain a given bond.  Georgii's own count is over *circuits*, of which at most
`3 ^ (ℓ - 1)` of length `ℓ` contain a given bond (`PeierlsSharp.ncard_circuitSets_le`). -/
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

/-- The surrogate count in exponential form: at most `4096^ℓ` `bondGraph`-connected sets of `ℓ`
bonds contain a given bond.  Only a constant to the `ℓ` is needed for (6.9); Georgii's sharper
`3 ^ (ℓ - 1)` over circuits is `PeierlsSharp.ncard_circuitSets_le`. -/
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



/-! ### Coordinates -/

lemma mk_eq_mk {a b c d : ℤ} : mk a b = mk c d ↔ a = c ∧ b = d := by
  rw [site_ext_iff]; simp

lemma mk_sub_e0 (a b : ℤ) : mk a b - e0 = mk (a - 1) b := by
  rw [site_ext_iff]; simp

lemma mk_sub_e1 (a b : ℤ) : mk a b - e1 = mk a (b - 1) := by
  rw [site_ext_iff]; simp

/-- The horizontal bond with left endpoint `w`. -/
def hbond (w : Site) : Sym2 Site := s(w, w + e0)

/-- The vertical bond with lower endpoint `w`. -/
def vbond (w : Site) : Sym2 Site := s(w, w + e1)

lemma hbond_mk (a b : ℤ) : hbond (mk a b) = s(mk a b, mk (a + 1) b) := by
  rw [hbond, mk_add_e0]

lemma vbond_mk (a b : ℤ) : vbond (mk a b) = s(mk a b, mk a (b + 1)) := by
  rw [vbond, mk_add_e1]

lemma hbond_injective : Function.Injective hbond := by
  intro a b h
  rw [hbond, hbond, Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · rw [h1] at h2
    exact absurd (congrArg (fun z ↦ z 0) h2) (by simp; omega)

lemma vbond_injective : Function.Injective vbond := by
  intro a b h
  rw [vbond, vbond, Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · rw [h1] at h2
    exact absurd (congrArg (fun z ↦ z 1) h2) (by simp; omega)

lemma hbond_ne_vbond (a b : Site) : hbond a ≠ vbond b := by
  rw [hbond, vbond, Ne, Sym2.eq_iff]
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
  · exact absurd (congrArg (fun z ↦ z 0) h) (by simp)
  · exact absurd (congrArg (fun z ↦ z 0) h) (by simp)

lemma hbond_sub_e0 (v : Site) : hbond (v - e0) = s(v - e0, v) := by
  rw [hbond, sub_add_cancel]

lemma vbond_sub_e1 (v : Site) : vbond (v - e1) = s(v - e1, v) := by
  rw [vbond, sub_add_cancel]

/-! ### The dual (face) potential -/

/-- Coordinate swap on `ℤ²`; it turns the direction of a bond into the direction of its dual
bond. -/
def rot (x : Site) : Site := mk (x 1) (x 0)

@[simp] lemma rot_e0 : rot e0 = e1 := by rw [rot, site_ext_iff]; simp

@[simp] lemma rot_e1 : rot e1 = e0 := by rw [rot, site_ext_iff]; simp

/-- The transport of a bond labelling `Z` to the dual lattice: the dual bond joining the
plaquettes `x` and `y` (adjacent lower-left corners) is labelled by the value of `Z` on the
unique lattice bond shared by the two plaquettes. -/
def dualLab (Z : Sym2 Site → ZMod 2) : Sym2 Site → ZMod 2 :=
  Sym2.lift ⟨fun u v ↦ Z s(u ⊔ v, u ⊔ v + rot (u ⊔ v - u ⊓ v)),
    fun u v ↦ by dsimp only; rw [sup_comm u v, inf_comm u v]⟩

lemma dualLab_horiz (Z : Sym2 Site → ZMod 2) (t u : ℤ) :
    dualLab Z s(mk t u, mk (t + 1) u) = Z s(mk (t + 1) u, mk (t + 1) (u + 1)) := by
  have hsup : mk t u ⊔ mk (t + 1) u = mk (t + 1) u := by
    rw [site_ext_iff]; constructor <;> simp
  have hinf : mk t u ⊓ mk (t + 1) u = mk t u := by
    rw [site_ext_iff]; constructor <;> simp
  have hdiff : mk (t + 1) u - mk t u = e0 := by
    rw [site_ext_iff]; constructor <;> simp
  rw [dualLab, Sym2.lift_mk]
  dsimp only
  rw [hsup, hinf, hdiff, rot_e0, mk_add_e1]

lemma dualLab_vert (Z : Sym2 Site → ZMod 2) (t u : ℤ) :
    dualLab Z s(mk t u, mk t (u + 1)) = Z s(mk t (u + 1), mk (t + 1) (u + 1)) := by
  have hsup : mk t u ⊔ mk t (u + 1) = mk t (u + 1) := by
    rw [site_ext_iff]; constructor <;> simp
  have hinf : mk t u ⊓ mk t (u + 1) = mk t u := by
    rw [site_ext_iff]; constructor <;> simp
  have hdiff : mk t (u + 1) - mk t u = e1 := by
    rw [site_ext_iff]; constructor <;> simp
  rw [dualLab, Sym2.lift_mk]
  dsimp only
  rw [hsup, hinf, hdiff, rot_e1, mk_add_e0]

/-- The vertex sum (mod two) of a bond labelling: the four bonds meeting the site `v`. -/
def vertSum (Z : Sym2 Site → ZMod 2) (v : Site) : ZMod 2 :=
  Z (hbond v) + Z (hbond (v - e0)) + Z (vbond v) + Z (vbond (v - e1))

/-- **Planar duality on `ℤ²`, mod two.** A bond labelling all of whose vertex sums vanish — a
mod-two *cycle* — is the coboundary of a labelling of the plaquettes: `ψ` is the indicator of
the "inside" of the cycle. This is `exists_potential` transported to the dual lattice. -/
lemma exists_dual_potential (Z : Sym2 Site → ZMod 2) (hZ : ∀ v, vertSum Z v = 0) :
    ∃ ψ : Site → ZMod 2,
      (∀ a b : ℤ, Z s(mk a b, mk (a + 1) b) = ψ (mk a b) + ψ (mk a (b - 1))) ∧
      (∀ a b : ℤ, Z s(mk a b, mk a (b + 1)) = ψ (mk a b) + ψ (mk (a - 1) b)) := by
  have hP : ∀ t u : ℤ, dualLab Z s(mk t u, mk (t + 1) u) + dualLab Z s(mk t u, mk t (u + 1))
      + dualLab Z s(mk (t + 1) u, mk (t + 1) (u + 1))
      + dualLab Z s(mk t (u + 1), mk (t + 1) (u + 1)) = 0 := by
    intro t u
    have h := hZ (mk (t + 1) (u + 1))
    rw [vertSum, hbond_sub_e0, vbond_sub_e1, hbond, vbond, mk_add_e0, mk_add_e1,
      mk_sub_e0, mk_sub_e1] at h
    rw [show t + 1 + 1 = t + 2 from by ring, show u + 1 + 1 = u + 2 from by ring,
      show t + 1 - 1 = t from by ring, show u + 1 - 1 = u from by ring] at h
    rw [dualLab_horiz, dualLab_vert, dualLab_vert, dualLab_horiz,
      show t + 1 + 1 = t + 2 from by ring, show u + 1 + 1 = u + 2 from by ring]
    linear_combination h
  obtain ⟨φ, hφ⟩ := exists_potential (dualLab Z) hP
  refine ⟨φ, fun a b ↦ ?_, fun a b ↦ ?_⟩
  · have h := hφ (mk a (b - 1)) (mk a (b - 1 + 1)) (by rw [← mk_add_e1]; exact adj_add_e1 _)
    rw [dualLab_vert] at h
    rw [show b - 1 + 1 = b from by ring] at h
    rw [← h]
    exact add_comm _ _
  · have h := hφ (mk (a - 1) b) (mk (a - 1 + 1) b) (by rw [← mk_add_e0]; exact adj_add_e0 _)
    rw [dualLab_horiz] at h
    rw [show a - 1 + 1 = a from by ring] at h
    rw [← h]
    exact add_comm _ _
/-! ### Walks inside a prescribed set of sites -/

/-- The inclusion of an induced subgraph into the ambient graph. -/
def inclHom {V : Type*} (G : SimpleGraph V) (s : Set V) : G.induce s →g G where
  toFun := Subtype.val
  map_rel' := fun h ↦ h

/-- Reachability inside `s` is witnessed by an ambient walk staying in `s`. -/
lemma exists_walk_support_subset_of_reachIn {V : Type*} {G : SimpleGraph V} {s : Set V} {a b : V}
    (h : ReachIn G s a b) : ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ s := by
  obtain ⟨ha, hb, ⟨q⟩⟩ := h
  have hA : (inclHom G s) ⟨a, ha⟩ = a := rfl
  have hB : (inclHom G s) ⟨b, hb⟩ = b := rfl
  refine ⟨(q.map (inclHom G s)).copy hA hB, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact y.2

open Classical in
/-- **Trimming a walk after its last visit to its starting point**: a nontrivial walk from `a`
has a tail which starts at a neighbour of `a` and never returns to `a`. -/
lemma exists_avoiding_tail {V : Type*} {G : SimpleGraph V} {a : V} :
    ∀ (n : ℕ) {b : V} (p : G.Walk a b), p.length ≤ n → a ≠ b →
      ∃ (c : V) (q : G.Walk c b), G.Adj a c ∧ a ∉ q.support ∧
        ∀ z ∈ q.support, z ∈ p.support := by
  intro n
  induction n with
  | zero =>
    intro b p hlen hab
    exact absurd (SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.1 hlen)) hab
  | succ n ih =>
    intro b p hlen hab
    cases p with
    | nil => exact absurd rfl hab
    | cons h q =>
      rw [SimpleGraph.Walk.length_cons] at hlen
      have hqn : q.length ≤ n := by omega
      by_cases ha : a ∈ q.support
      · obtain ⟨c', q', hadj, hnot, hsub⟩ := ih (q.dropUntil a ha)
          (le_trans (SimpleGraph.Walk.length_dropUntil_le_length q ha) hqn) hab
        refine ⟨c', q', hadj, hnot, fun z hz ↦ ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _
          (SimpleGraph.Walk.support_dropUntil_subset_support q ha (hsub z hz))
      · refine ⟨_, q, h, ha, fun z hz ↦ ?_⟩
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ hz

/-! ### Mod-two bond chains of lattice walks -/

open Classical in
/-- The mod-two chain of a lattice walk: the parity of the number of traversals of each bond. -/
def bondChain : ∀ {a b : Site}, (latticeGraph 2).Walk a b → Sym2 Site → ZMod 2
  | _, _, SimpleGraph.Walk.nil => fun _ ↦ 0
  | a, _, SimpleGraph.Walk.cons (v := v) _ q => fun e ↦
      (if s(a, v) = e then 1 else 0) + bondChain q e

open Classical in
@[simp] lemma bondChain_nil {a : Site} :
    bondChain (SimpleGraph.Walk.nil : (latticeGraph 2).Walk a a) = fun _ ↦ 0 := rfl

open Classical in
lemma bondChain_cons {a v b : Site} (h : (latticeGraph 2).Adj a v)
    (q : (latticeGraph 2).Walk v b) (e : Sym2 Site) :
    bondChain (SimpleGraph.Walk.cons h q) e = (if s(a, v) = e then 1 else 0) + bondChain q e :=
  rfl

/-- A bond not traversed by the walk carries the label `0`. -/
lemma bondChain_eq_zero_of_notMem : ∀ {a b : Site} (w : (latticeGraph 2).Walk a b)
    {e : Sym2 Site}, e ∉ w.edges → bondChain w e = 0
  | _, _, SimpleGraph.Walk.nil, e, _ => rfl
  | a, _, SimpleGraph.Walk.cons (v := v) h q, e, he => by
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, not_or] at he
    rw [bondChain_cons, ite_eq_right (fun hc ↦ he.1 hc.symm),
      bondChain_eq_zero_of_notMem q he.2, add_zero]

lemma vertSum_add (Y Z : Sym2 Site → ZMod 2) (v : Site) :
    vertSum (fun e ↦ Y e + Z e) v = vertSum Y v + vertSum Z v := by
  simp only [vertSum]; ring

lemma vertSum_hbond (w v : Site) :
    vertSum (fun e ↦ if hbond w = e then (1 : ZMod 2) else 0) v
      = (if v = w then 1 else 0) + (if v = w + e0 then 1 else 0) := by
  have h1 : (hbond w = hbond v) ↔ (v = w) :=
    ⟨fun h ↦ (hbond_injective h).symm, fun h ↦ by rw [h]⟩
  have h2 : (hbond w = hbond (v - e0)) ↔ (v = w + e0) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [hbond_injective h]; abel
    · rw [h]; congr 1; abel
  simp only [vertSum, ite_eq_right (hbond_ne_vbond w v), ite_eq_right (hbond_ne_vbond w (v - e1)),
    h1, h2]
  ring

lemma vertSum_vbond (w v : Site) :
    vertSum (fun e ↦ if vbond w = e then (1 : ZMod 2) else 0) v
      = (if v = w then 1 else 0) + (if v = w + e1 then 1 else 0) := by
  have h1 : (vbond w = vbond v) ↔ (v = w) :=
    ⟨fun h ↦ (vbond_injective h).symm, fun h ↦ by rw [h]⟩
  have h2 : (vbond w = vbond (v - e1)) ↔ (v = w + e1) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [vbond_injective h]; abel
    · rw [h]; congr 1; abel
  simp only [vertSum, ite_eq_right (hbond_ne_vbond v w).symm,
    ite_eq_right (hbond_ne_vbond (v - e0) w).symm, h1, h2]
  ring

/-- The vertex sums of the chain of a single bond: its two endpoints. -/
lemma vertSum_single {p q : Site} (hpq : (latticeGraph 2).Adj p q) (v : Site) :
    vertSum (fun e ↦ if s(p, q) = e then (1 : ZMod 2) else 0) v
      = (if v = p then 1 else 0) + (if v = q then 1 else 0) := by
  rcases (latticeGraph_two_adj_iff' p q).1 hpq with rfl | rfl | rfl | rfl
  · rw [show s(p, p + e0) = hbond p from rfl, vertSum_hbond]
  · rw [Sym2.eq_swap, show s(q, q + e0) = hbond q from rfl, vertSum_hbond]
    exact add_comm _ _
  · rw [show s(p, p + e1) = vbond p from rfl, vertSum_vbond]
  · rw [Sym2.eq_swap, show s(q, q + e1) = vbond q from rfl, vertSum_vbond]
    exact add_comm _ _

/-- **The mod-two chain of a walk is a cycle away from its endpoints.** -/
lemma vertSum_bondChain : ∀ {a b : Site} (w : (latticeGraph 2).Walk a b) (v : Site),
    vertSum (bondChain w) v = (if v = a then 1 else 0) + (if v = b then 1 else 0)
  | a, _, SimpleGraph.Walk.nil, v => by
    have h0 : vertSum (bondChain (SimpleGraph.Walk.nil : (latticeGraph 2).Walk a a)) v = 0 := by
      simp [vertSum]
    rw [h0]
    by_cases h : v = a
    · rw [ite_eq_left h]; decide
    · rw [ite_eq_right h]; simp
  | a, b, SimpleGraph.Walk.cons (v := c) h q, v => by
    have hfun : bondChain (SimpleGraph.Walk.cons h q)
        = fun e ↦ (if s(a, c) = e then (1 : ZMod 2) else 0) + bondChain q e := by
      funext e; exact bondChain_cons h q e
    rw [hfun, vertSum_add, vertSum_single h, vertSum_bondChain q]
    exact (by decide : ∀ x y z : ZMod 2, x + y + (y + z) = x + z) _ _ _

/-! ### Excluding Georgii's fourth case: no alternating plaquette

Georgii excludes `n_c(u) = 4` — the case in which the two diagonal pairs of corners of the
plaquette are separated by the contour — by an appeal to the Jordan curve theorem.  The
substitute used here is planar duality mod two (`exists_dual_potential`): the lattice path
inside `D` joining the two corners of `D`, closed up through one of the two outer corners, is a
mod-two cycle; its dual potential `ψ` is the indicator of the inside of that cycle, and it
separates the two outer corners, contradicting the connectedness of `outside D`. -/

lemma bond_ne_of {w z p q : Site} (h1 : w ≠ p) (h2 : w ≠ q) : s(w, z) ≠ s(p, q) := by
  rw [Ne, Sym2.eq_iff]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact h1 h
  · exact h2 h

open Classical in
/-- The mod-two cycle obtained from a lattice walk `V` from `a` to `b` by closing it up through
the site `v₁` (Georgii's construction in the excluded case `n_c(u) = 4`). -/
def crossChain {a b : Site} (V : (latticeGraph 2).Walk a b) (v₁ : Site) : Sym2 Site → ZMod 2 :=
  fun e ↦ bondChain V e + ((if s(a, v₁) = e then 1 else 0) + (if s(v₁, b) = e then 1 else 0))

open Classical in
lemma crossChain_apply {a b : Site} (V : (latticeGraph 2).Walk a b) (v₁ : Site) (e : Sym2 Site) :
    crossChain V v₁ e
      = bondChain V e + ((if s(a, v₁) = e then 1 else 0) + (if s(v₁, b) = e then 1 else 0)) :=
  rfl

/-- The closed-up chain is a mod-two cycle: all its vertex sums vanish. -/
lemma vertSum_crossChain {a b v₁ : Site} (V : (latticeGraph 2).Walk a b)
    (ha : (latticeGraph 2).Adj a v₁) (hb : (latticeGraph 2).Adj v₁ b) (v : Site) :
    vertSum (crossChain V v₁) v = 0 := by
  classical
  have h1 : vertSum (crossChain V v₁) v
      = vertSum (bondChain V) v
        + (vertSum (fun e ↦ if s(a, v₁) = e then (1 : ZMod 2) else 0) v
          + vertSum (fun e ↦ if s(v₁, b) = e then (1 : ZMod 2) else 0) v) := by
    simp only [vertSum, crossChain_apply]
    ring
  rw [h1, vertSum_bondChain, vertSum_single ha, vertSum_single hb]
  exact (by decide : ∀ x y z : ZMod 2, x + y + (x + z + (z + y)) = 0) _ _ _

/-- **The dual potential of the closed-up path.**  Georgii's Jordan-curve step, replaced by
planar duality mod two. -/
lemma exists_crossing_potential {D : Set Site}
    (hconn : ∀ p q : Site, p ∈ D → q ∈ D → ReachIn (latticeGraph 2) D p q)
    {u₁ u₂ v₁ : Site} (hu₁ : u₁ ∈ D) (hu₂ : u₂ ∈ D) (hv₁ : v₁ ∉ D) (h12 : u₁ ≠ u₂)
    (ha₁ : (latticeGraph 2).Adj u₁ v₁) (ha₂ : (latticeGraph 2).Adj v₁ u₂) :
    ∃ (Z : Sym2 Site → ZMod 2) (ψ : Site → ZMod 2),
      (∀ a b : ℤ, Z s(mk a b, mk (a + 1) b) = ψ (mk a b) + ψ (mk a (b - 1))) ∧
      (∀ a b : ℤ, Z s(mk a b, mk a (b + 1)) = ψ (mk a b) + ψ (mk (a - 1) b)) ∧
      Z s(u₁, v₁) = 1 ∧ Z s(v₁, u₂) = 1 ∧
      (∀ w z : Site, w ∉ D → s(w, z) ≠ s(u₁, v₁) → s(w, z) ≠ s(v₁, u₂) → Z s(w, z) = 0) := by
  classical
  obtain ⟨V, hV⟩ := exists_walk_support_subset_of_reachIn (hconn u₁ u₂ hu₁ hu₂)
  obtain ⟨ψ, hh, hv⟩ := exists_dual_potential (crossChain V v₁) (vertSum_crossChain V ha₁ ha₂)
  have hVzero : ∀ w z : Site, w ∉ D → bondChain V s(w, z) = 0 := by
    intro w z hw
    refine bondChain_eq_zero_of_notMem V fun hmem ↦ hw ?_
    exact hV w (V.fst_mem_support_of_mem_edges hmem)
  have hspec : s(u₁, v₁) ≠ s(v₁, u₂) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hv₁ (h ▸ hu₁)
    · exact h12 h
  have hVzero' : ∀ w z : Site, z ∉ D → bondChain V s(w, z) = 0 := by
    intro w z hz
    rw [Sym2.eq_swap]
    exact hVzero z w hz
  refine ⟨crossChain V v₁, ψ, hh, hv, ?_, ?_, ?_⟩
  · rw [crossChain_apply, hVzero' u₁ v₁ hv₁, ite_eq_left rfl, ite_eq_right (Ne.symm hspec)]
    decide
  · rw [crossChain_apply, hVzero v₁ u₂ hv₁, ite_eq_right hspec, ite_eq_left rfl]
    decide
  · intro w z hw hne₁ hne₂
    rw [crossChain_apply, hVzero w z hw, ite_eq_right (Ne.symm hne₁),
      ite_eq_right (Ne.symm hne₂)]
    decide

/-- The four plaquettes meeting a site carry the same potential, as soon as none of the four
bonds at that site belongs to the cycle. -/
lemma psi_four_faces {Z : Sym2 Site → ZMod 2} {ψ : Site → ZMod 2}
    (hh : ∀ a b : ℤ, Z s(mk a b, mk (a + 1) b) = ψ (mk a b) + ψ (mk a (b - 1)))
    (hv : ∀ a b : ℤ, Z s(mk a b, mk a (b + 1)) = ψ (mk a b) + ψ (mk (a - 1) b))
    {w : Site} (hw0 : ∀ z : Site, Z s(w, z) = 0) :
    ψ w = ψ (w - e0) ∧ ψ w = ψ (w - e1) ∧ ψ w = ψ (w - e0 - e1) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℤ, w = mk a b := ⟨w 0, w 1, (mk_eta w).symm⟩
  have h1 : ψ (mk a b) = ψ (mk a (b - 1)) := by
    have h := hh a b
    rw [← mk_add_e0, hw0 (mk a b + e0)] at h
    exact (by decide : ∀ x y : ZMod 2, 0 = x + y → x = y) _ _ h
  have h2 : ψ (mk a b) = ψ (mk (a - 1) b) := by
    have h := hv a b
    rw [← mk_add_e1, hw0 (mk a b + e1)] at h
    exact (by decide : ∀ x y : ZMod 2, 0 = x + y → x = y) _ _ h
  have h3 : ψ (mk (a - 1) b) = ψ (mk (a - 1) (b - 1)) := by
    have hz : Z s(mk (a - 1) b, mk (a - 1 + 1) b) = 0 := by
      rw [show a - 1 + 1 = a from by ring, ← mk_sub_e0, Sym2.eq_swap]
      exact hw0 (mk a b - e0)
    have h := hh (a - 1) b
    rw [hz] at h
    exact (by decide : ∀ x y : ZMod 2, 0 = x + y → x = y) _ _ h
  refine ⟨by rw [mk_sub_e0]; exact h2, by rw [mk_sub_e1]; exact h1, ?_⟩
  rw [mk_sub_e0, mk_sub_e1]
  exact h2.trans h3

/-- The dual potential is constant along a lattice walk avoiding `D` and the site `v₁`. -/
lemma psi_invariant {D : Set Site} {v₁ : Site} {ψ : Site → ZMod 2}
    (hstep : ∀ w w' : Site, w ∉ D → w ≠ v₁ → w' ∉ D → w' ≠ v₁ →
      (latticeGraph 2).Adj w w' → ψ w = ψ w') :
    ∀ {a b : Site} (q : (latticeGraph 2).Walk a b),
      (∀ z ∈ q.support, z ∉ D ∧ z ≠ v₁) → ψ a = ψ b
  | _, _, SimpleGraph.Walk.nil, _ => rfl
  | a, _, SimpleGraph.Walk.cons (v := c) h q, hs => by
    have hac := hs a (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self)
    have hcc := hs c (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ q.start_mem_support)
    exact (hstep a c hac.1 hac.2 hcc.1 hcc.2 h).trans
      (psi_invariant hstep q fun z hz ↦ hs z (by
        rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz))

/-- **The contradiction in Georgii's excluded case.**  If the dual potential of the cycle is
locally constant off `D ∪ {v₁}` and takes different values at `v₂` and at every neighbour of
`v₁` off `D`, then `v₁` and `v₂` cannot both lie in the infinite component of `Dᶜ`. -/
lemma crossing_contradiction {D : Set Site} (hD : D.Finite) {ψ : Site → ZMod 2} {v₁ v₂ : Site}
    (hface : ∀ w : Site, w ∉ D → w ≠ v₁ →
      ψ w = ψ (w - e0) ∧ ψ w = ψ (w - e1) ∧ ψ w = ψ (w - e0 - e1))
    (hv₁ : v₁ ∈ outside D) (hv₂ : v₂ ∈ outside D) (hne : v₁ ≠ v₂)
    (hnbr : ∀ c : Site, (latticeGraph 2).Adj v₁ c → c ∉ D → c ≠ v₁ → ψ c ≠ ψ v₂) : False := by
  have hstep : ∀ w w' : Site, w ∉ D → w ≠ v₁ → w' ∉ D → w' ≠ v₁ →
      (latticeGraph 2).Adj w w' → ψ w = ψ w' := by
    intro w w' hw hwv hw' hw'v hadj
    rcases (latticeGraph_two_adj_iff' w w').1 hadj with rfl | rfl | rfl | rfl
    · rw [(hface _ hw' hw'v).1, add_sub_cancel_right]
    · rw [(hface _ hw hwv).1, add_sub_cancel_right]
    · rw [(hface _ hw' hw'v).2.1, add_sub_cancel_right]
    · rw [(hface _ hw hwv).2.1, add_sub_cancel_right]
  obtain ⟨W, hW⟩ := exists_walk_support_subset_of_reachIn (reachIn_of_mem_outside hD hv₁ hv₂)
  obtain ⟨c, q, hadj, hnot, hsub⟩ := exists_avoiding_tail W.length W le_rfl hne
  have hq : ∀ z ∈ q.support, z ∉ D ∧ z ≠ v₁ := by
    intro z hz
    exact ⟨hW z (hsub z hz), fun hzv ↦ hnot (hzv ▸ hz)⟩
  have hc := hq c q.start_mem_support
  exact hnbr c hadj hc.1 hc.2 (psi_invariant hstep q hq)

/-- **Georgii (6.14), the case `n_c(u) = 4`, main diagonal.**  Two diagonally opposite corners
of a plaquette cannot lie in a finite connected `D` while the other two lie in the infinite
component of `Dᶜ`. -/
theorem no_crossing_diag {D : Set Site} (hD : D.Finite)
    (hconn : ∀ p q : Site, p ∈ D → q ∈ D → ReachIn (latticeGraph 2) D p q) {t u : ℤ}
    (h00 : mk t u ∈ D) (h11 : mk (t + 1) (u + 1) ∈ D)
    (h10 : mk (t + 1) u ∈ outside D) (h01 : mk t (u + 1) ∈ outside D) : False := by
  have hv₁D : mk (t + 1) u ∉ D := notMem_of_mem_outside h10
  have hv₂D : mk t (u + 1) ∉ D := notMem_of_mem_outside h01
  have h12 : mk t u ≠ mk (t + 1) (u + 1) := by rw [Ne, mk_eq_mk]; omega
  have ha₁ : (latticeGraph 2).Adj (mk t u) (mk (t + 1) u) := adj_mk_horiz t u
  have ha₂ : (latticeGraph 2).Adj (mk (t + 1) u) (mk (t + 1) (u + 1)) := adj_mk_vert (t + 1) u
  obtain ⟨Z, ψ, hh, hv, hZ1, hZ2, hZ0⟩ :=
    exists_crossing_potential hconn h00 h11 hv₁D h12 ha₁ ha₂
  have hface : ∀ w : Site, w ∉ D → w ≠ mk (t + 1) u →
      ψ w = ψ (w - e0) ∧ ψ w = ψ (w - e1) ∧ ψ w = ψ (w - e0 - e1) := by
    intro w hw hwv
    refine psi_four_faces hh hv (fun z ↦ hZ0 w z hw ?_ ?_)
    · exact bond_ne_of (fun hc ↦ hw (by rw [hc]; exact h00)) hwv
    · exact bond_ne_of hwv (fun hc ↦ hw (by rw [hc]; exact h11))
  -- the potential jumps across the two bonds of the cycle at `mk (t + 1) u`
  have hα1 : ψ (mk (t + 1) u) = ψ (mk t u) + 1 := by
    have h := hv (t + 1) u
    rw [hZ2, show t + 1 - 1 = t from by ring] at h
    exact (by decide : ∀ x y : ZMod 2, 1 = x + y → x = y + 1) _ _ h
  have hα2 : ψ (mk (t + 1) (u - 1)) = ψ (mk t u) + 1 := by
    have hz : Z s(mk (t + 1) u, mk (t + 1 + 1) u) = 0 := by
      refine hZ0 (mk (t + 1) u) (mk (t + 1 + 1) u) hv₁D ?_ ?_
      · rw [Ne, Sym2.eq_iff, mk_eq_mk, mk_eq_mk, mk_eq_mk, mk_eq_mk]; omega
      · rw [Ne, Sym2.eq_iff, mk_eq_mk, mk_eq_mk, mk_eq_mk, mk_eq_mk]; omega
    have h := hh (t + 1) u
    rw [hz, hα1] at h
    exact (by decide : ∀ x y : ZMod 2, 0 = x + 1 + y → y = x + 1) _ _ h
  -- the potential at `mk t (u + 1)`
  have hψv₂ : ψ (mk t (u + 1)) = ψ (mk t u) := by
    have h := (hface (mk t (u + 1)) hv₂D (by rw [Ne, mk_eq_mk]; omega)).2.1
    rwa [mk_sub_e1, show u + 1 - 1 = u from by ring] at h
  refine crossing_contradiction hD hface h10 h01 (by rw [Ne, mk_eq_mk]; omega) ?_
  intro c hadj hcD hcv
  rw [hψv₂]
  rcases (latticeGraph_two_adj_iff' (mk (t + 1) u) c).1 hadj with h | h | h | h
  · have hc : c = mk (t + 2) u := by
      rw [h, mk_add_e0, show t + 1 + 1 = t + 2 from by ring]
    have hcf := (hface c hcD hcv).1
    rw [hc, mk_sub_e0, show t + 2 - 1 = t + 1 from by ring, hα1] at hcf
    rw [hc, hcf]
    exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _
  · exact absurd (by rw [show c = mk t u from by
      have hc : c = mk (t + 1) u - e0 := by rw [h]; abel
      rw [hc, mk_sub_e0, show t + 1 - 1 = t from by ring]]; exact h00) hcD
  · exact absurd (by rw [show c = mk (t + 1) (u + 1) from by rw [h, mk_add_e1]]; exact h11) hcD
  · have hc : c = mk (t + 1) (u - 1) := by
      have hc' : c = mk (t + 1) u - e1 := by rw [h]; abel
      rw [hc', mk_sub_e1]
    rw [hc, hα2]
    exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _

/-- **Georgii (6.14), the case `n_c(u) = 4`, anti-diagonal.** -/
theorem no_crossing_antidiag {D : Set Site} (hD : D.Finite)
    (hconn : ∀ p q : Site, p ∈ D → q ∈ D → ReachIn (latticeGraph 2) D p q) {t u : ℤ}
    (h10 : mk (t + 1) u ∈ D) (h01 : mk t (u + 1) ∈ D)
    (h00 : mk t u ∈ outside D) (h11 : mk (t + 1) (u + 1) ∈ outside D) : False := by
  have hv₁D : mk t u ∉ D := notMem_of_mem_outside h00
  have hv₂D : mk (t + 1) (u + 1) ∉ D := notMem_of_mem_outside h11
  have h12 : mk (t + 1) u ≠ mk t (u + 1) := by rw [Ne, mk_eq_mk]; omega
  have ha₁ : (latticeGraph 2).Adj (mk (t + 1) u) (mk t u) := (adj_mk_horiz t u).symm
  have ha₂ : (latticeGraph 2).Adj (mk t u) (mk t (u + 1)) := adj_mk_vert t u
  obtain ⟨Z, ψ, hh, hv, hZ1, hZ2, hZ0⟩ :=
    exists_crossing_potential hconn h10 h01 hv₁D h12 ha₁ ha₂
  have hface : ∀ w : Site, w ∉ D → w ≠ mk t u →
      ψ w = ψ (w - e0) ∧ ψ w = ψ (w - e1) ∧ ψ w = ψ (w - e0 - e1) := by
    intro w hw hwv
    refine psi_four_faces hh hv (fun z ↦ hZ0 w z hw ?_ ?_)
    · exact bond_ne_of (fun hc ↦ hw (by rw [hc]; exact h10)) hwv
    · exact bond_ne_of hwv (fun hc ↦ hw (by rw [hc]; exact h01))
  have hα1 : ψ (mk t (u - 1)) = ψ (mk t u) + 1 := by
    have h := hh t u
    rw [show s(mk t u, mk (t + 1) u) = s(mk (t + 1) u, mk t u) from Sym2.eq_swap, hZ1] at h
    exact (by decide : ∀ x y : ZMod 2, 1 = x + y → y = x + 1) _ _ h
  have hα2 : ψ (mk (t - 1) u) = ψ (mk t u) + 1 := by
    have h := hv t u
    rw [hZ2] at h
    exact (by decide : ∀ x y : ZMod 2, 1 = x + y → y = x + 1) _ _ h
  have hψv₂ : ψ (mk (t + 1) (u + 1)) = ψ (mk t u) := by
    have h := (hface (mk (t + 1) (u + 1)) hv₂D (by rw [Ne, mk_eq_mk]; omega)).2.2
    rwa [mk_sub_e0, mk_sub_e1, show t + 1 - 1 = t from by ring,
      show u + 1 - 1 = u from by ring] at h
  refine crossing_contradiction hD hface h00 h11 (by rw [Ne, mk_eq_mk]; omega) ?_
  intro c hadj hcD hcv
  rw [hψv₂]
  rcases (latticeGraph_two_adj_iff' (mk t u) c).1 hadj with h | h | h | h
  · exact absurd (by rw [show c = mk (t + 1) u from by rw [h, mk_add_e0]]; exact h10) hcD
  · have hc : c = mk (t - 1) u := by
      have hc' : c = mk t u - e0 := by rw [h]; abel
      rw [hc', mk_sub_e0]
    rw [hc, hα2]
    exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _
  · exact absurd (by rw [show c = mk t (u + 1) from by rw [h, mk_add_e1]]; exact h01) hcD
  · have hc : c = mk t (u - 1) := by
      have hc' : c = mk t u - e1 := by rw [h]; abel
      rw [hc', mk_sub_e1]
    rw [hc, hα1]
    exact (by decide : ∀ x : ZMod 2, x + 1 ≠ x) _

/-! ### M5: Georgii's degree-two property of the outer boundary (Lemma (6.14))

Georgii's Lemma (6.14) shows that the outer boundary `c` of a finite connected `D ⊆ ℤ²` is a
*circuit*: every dual site `u` met by `c` satisfies `n_c(u) = 2`, where
`n_c(u) = |{b* ∈ c : b* ∋ u}|`.  In the present encoding a dual site is a plaquette, indexed by
its lower-left corner `x`, and the four dual bonds at `u` are the four bonds of `plaquette x`. -/

open scoped Classical in
/-- Georgii's `n_c(u)`: the number of bonds of `c` in the plaquette with lower-left corner `x`
(the dual bonds of `c` meeting the dual site dual to that plaquette). -/
def plaquetteDeg (c : Set (Sym2 Site)) (x : Site) : ℕ :=
  ((plaquette x).filter (· ∈ c)).card

/-- A bond of the lattice lies in the outer boundary of `D` exactly when its two endpoints
disagree about membership in the infinite component of `Dᶜ`. -/
lemma mem_outerBoundary_iff_not_iff {D : Set Site} {a b : Site}
    (hab : (latticeGraph 2).Adj a b) :
    s(a, b) ∈ outerBoundary D ↔ ¬(a ∈ outside D ↔ b ∈ outside D) := by
  rw [mem_outerBoundary_iff hab]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩) hiff
    · exact notMem_of_mem_outside (hiff.2 hb) ha
    · exact notMem_of_mem_outside (hiff.1 ha) hb
  · intro hiff
    by_cases ha : a ∈ outside D
    · exact Or.inr ⟨mem_of_adj_outside (fun hb ↦ hiff ⟨fun _ ↦ hb, fun _ ↦ ha⟩) hab.symm ha, ha⟩
    · have hb : b ∈ outside D := by
        by_contra hb
        exact hiff ⟨fun h ↦ absurd h ha, fun h ↦ absurd h hb⟩
      exact Or.inl ⟨mem_of_adj_outside ha hab hb, hb⟩

/-- The count of the four sides of a square on which a two-valued function changes value is
`2`, unless it is `0` (constant) or the two diagonal pairs are separated. -/
lemma plaquette_count (P₁ P₂ P₃ P₄ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃]
    [Decidable P₄] (hno : ¬((P₁ ↔ P₄) ∧ (P₂ ↔ P₃) ∧ ¬(P₁ ↔ P₂)))
    (hne : ¬(P₁ ↔ P₂) ∨ ¬(P₁ ↔ P₃) ∨ ¬(P₂ ↔ P₄) ∨ ¬(P₃ ↔ P₄)) :
    (if ¬(P₁ ↔ P₂) then 1 else 0) + (if ¬(P₁ ↔ P₃) then 1 else 0)
      + (if ¬(P₂ ↔ P₄) then 1 else 0) + (if ¬(P₃ ↔ P₄) then 1 else 0) = 2 := by
  by_cases h₁ : P₁ <;> by_cases h₂ : P₂ <;> by_cases h₃ : P₃ <;> by_cases h₄ : P₄ <;> simp_all

open scoped Classical in
/-- `plaquetteDeg` as the sum of the four indicators of the sides of the plaquette. -/
lemma plaquetteDeg_eq (c : Set (Sym2 Site)) (t u : ℤ) :
    plaquetteDeg c (mk t u) = (if s(mk t u, mk (t + 1) u) ∈ c then 1 else 0)
      + (if s(mk t u, mk t (u + 1)) ∈ c then 1 else 0)
      + (if s(mk (t + 1) u, mk (t + 1) (u + 1)) ∈ c then 1 else 0)
      + (if s(mk t (u + 1), mk (t + 1) (u + 1)) ∈ c then 1 else 0) := by
  have h1 : s(mk t u, mk (t + 1) u) ∉ ({s(mk t u, mk t (u + 1)),
      s(mk (t + 1) u, mk (t + 1) (u + 1)), s(mk t (u + 1), mk (t + 1) (u + 1))} :
        Finset (Sym2 Site)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, mk_eq_mk, not_or]
    omega
  have h2 : s(mk t u, mk t (u + 1)) ∉ ({s(mk (t + 1) u, mk (t + 1) (u + 1)),
      s(mk t (u + 1), mk (t + 1) (u + 1))} : Finset (Sym2 Site)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, mk_eq_mk, not_or]
    omega
  have h3 : s(mk (t + 1) u, mk (t + 1) (u + 1)) ∉
      ({s(mk t (u + 1), mk (t + 1) (u + 1))} : Finset (Sym2 Site)) := by
    simp only [Finset.mem_singleton, Sym2.eq_iff, mk_eq_mk]
    omega
  simp only [plaquetteDeg, plaquette_mk]
  rw [Finset.card_filter, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  ring

/-- **Georgii Lemma (6.14), the circuit property.**  For a finite, nonempty, connected set of
sites `D ⊆ ℤ²`, every dual site met by the outer boundary of `D` is met by exactly two of its
bonds: `n_c(u) = 2`.  Together with `outerBoundary_connected` this says that the outer boundary
is a circuit in Georgii's sense.

Georgii excludes `n_c(u) = 1` because all four corners of the plaquette would then lie outside
`D`; `n_c(u) = 3` by the parity of the number of sign changes around the plaquette; and
`n_c(u) = 4` by the Jordan curve theorem.  Here the first two are the content of
`plaquette_count`, and the third is `no_crossing_diag` / `no_crossing_antidiag`, proved by
planar duality mod two instead of the Jordan curve theorem. -/
theorem plaquetteDeg_outerBoundary_eq_two {D : Set Site} (hD : D.Finite) (_hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) (x : Site)
    (hx : (↑(plaquette x) ∩ outerBoundary D).Nonempty) :
    plaquetteDeg (outerBoundary D) x = 2 := by
  classical
  obtain ⟨t, u, rfl⟩ : ∃ t u : ℤ, x = mk t u := ⟨x 0, x 1, (mk_eta x).symm⟩
  have hconn' : ∀ p q : Site, p ∈ D → q ∈ D → ReachIn (latticeGraph 2) D p q :=
    (induce_connected_iff.1 hconn).2
  have hb₁ := mem_outerBoundary_iff_not_iff (D := D) (adj_mk_horiz t u)
  have hb₂ := mem_outerBoundary_iff_not_iff (D := D) (adj_mk_vert t u)
  have hb₃ := mem_outerBoundary_iff_not_iff (D := D) (adj_mk_vert (t + 1) u)
  have hb₄ := mem_outerBoundary_iff_not_iff (D := D) (adj_mk_horiz t (u + 1))
  rw [plaquetteDeg_eq]
  simp only [hb₁, hb₂, hb₃, hb₄]
  refine plaquette_count _ _ _ _ ?_ ?_
  · -- Georgii's case `n_c(u) = 4`, excluded by planar duality
    rintro ⟨h14, h23, h12⟩
    by_cases hA : mk t u ∈ outside D
    · have hE : mk (t + 1) (u + 1) ∈ outside D := h14.1 hA
      have hB : mk (t + 1) u ∉ outside D := fun hB ↦ h12 ⟨fun _ ↦ hB, fun _ ↦ hA⟩
      have hC : mk t (u + 1) ∉ outside D := fun hC ↦ hB (h23.2 hC)
      exact no_crossing_antidiag hD hconn'
        (mem_of_adj_outside hB (adj_mk_horiz t u).symm hA)
        (mem_of_adj_outside hC (adj_mk_vert t u).symm hA) hA hE
    · have hE : mk (t + 1) (u + 1) ∉ outside D := fun hE ↦ hA (h14.2 hE)
      have hB : mk (t + 1) u ∈ outside D := by
        by_contra hB
        exact h12 ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩
      have hC : mk t (u + 1) ∈ outside D := h23.1 hB
      exact no_crossing_diag hD hconn'
        (mem_of_adj_outside hA (adj_mk_horiz t u) hB)
        (mem_of_adj_outside hE (adj_mk_vert (t + 1) u).symm hB) hB hC
  · -- Georgii's case `n_c(u) = 1`: some side of the plaquette is a boundary bond
    obtain ⟨e, hep, heb⟩ := hx
    rw [Finset.mem_coe, plaquette_mk, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hep
    rcases hep with rfl | rfl | rfl | rfl
    · exact Or.inl (hb₁.1 heb)
    · exact Or.inr (Or.inl (hb₂.1 heb))
    · exact Or.inr (Or.inr (Or.inl (hb₃.1 heb)))
    · exact Or.inr (Or.inr (Or.inr (hb₄.1 heb)))

/-! ### The two plaquettes of a bond, and `2`-regularity of the outer boundary

Georgii's counting Lemma (6.13) walks along a circuit: at each step the next dual bond is one
of the three bonds of the next plaquette other than the current one.  The input for that is
that the outer boundary is `2`-regular in `bondGraph`, which follows from
`plaquetteDeg_outerBoundary_eq_two` once one knows that each lattice bond lies in exactly two
plaquettes. -/

lemma plaquette_eq (x : Site) :
    plaquette x = {hbond x, vbond x, vbond (x + e0), hbond (x + e1)} := by
  have h1 : x + e1 + e0 = x + e0 + e1 := by abel
  simp only [plaquette, hbond, vbond, h1]

lemma hbond_mem_plaquette_iff (w x : Site) : hbond w ∈ plaquette x ↔ x = w ∨ x = w - e1 := by
  rw [plaquette_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (hbond_injective h).symm
    · exact absurd h (hbond_ne_vbond w x)
    · exact absurd h (hbond_ne_vbond w (x + e0))
    · refine Or.inr ?_
      rw [hbond_injective h]
      abel
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (by congr 1; abel)))

lemma vbond_mem_plaquette_iff (w x : Site) : vbond w ∈ plaquette x ↔ x = w ∨ x = w - e0 := by
  rw [plaquette_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h | h)
    · exact absurd h (Ne.symm (hbond_ne_vbond x w))
    · exact Or.inl (vbond_injective h).symm
    · refine Or.inr ?_
      rw [vbond_injective h]
      abel
    · exact absurd h (Ne.symm (hbond_ne_vbond (x + e1) w))
  · rintro (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl (by congr 1; abel)))

/-- The two plaquettes containing a bond, recognised by the sum of their lower-left corners. -/
lemma plaquette_sum {e : Sym2 Site} {x y : Site} (hex : e ∈ plaquette x) (hey : e ∈ plaquette y)
    (hxy : x ≠ y) :
    (∃ w, e = hbond w ∧ x + y = w + w - e1) ∨ (∃ w, e = vbond w ∧ x + y = w + w - e0) := by
  rw [plaquette_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
    Finset.mem_singleton] at hex
  rcases hex with rfl | rfl | rfl | rfl
  · rcases (hbond_mem_plaquette_iff x y).1 hey with h | h
    · exact absurd h.symm hxy
    · exact Or.inl ⟨x, rfl, by rw [h]; abel⟩
  · rcases (vbond_mem_plaquette_iff x y).1 hey with h | h
    · exact absurd h.symm hxy
    · exact Or.inr ⟨x, rfl, by rw [h]; abel⟩
  · rcases (vbond_mem_plaquette_iff (x + e0) y).1 hey with h | h
    · exact Or.inr ⟨x + e0, rfl, by rw [h]; abel⟩
    · exact absurd (h.trans (by abel : x + e0 - e0 = x)) hxy.symm
  · rcases (hbond_mem_plaquette_iff (x + e1) y).1 hey with h | h
    · exact Or.inl ⟨x + e1, rfl, by rw [h]; abel⟩
    · exact absurd (h.trans (by abel : x + e1 - e1 = x)) hxy.symm

/-- Two distinct plaquettes share at most one bond. -/
lemma eq_of_mem_plaquette₂ {x y : Site} (hxy : x ≠ y) {e f : Sym2 Site}
    (hex : e ∈ plaquette x) (hey : e ∈ plaquette y)
    (hfx : f ∈ plaquette x) (hfy : f ∈ plaquette y) : f = e := by
  rcases plaquette_sum hex hey hxy with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩ <;>
    rcases plaquette_sum hfx hfy hxy with ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩
  · have h := hw'.symm.trans hw
    rw [site_ext_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, e1_zero, e1_one] at h
    congr 1
    rw [site_ext_iff]
    omega
  · exfalso
    have h := hw'.symm.trans hw
    rw [site_ext_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, e0_zero, e0_one, e1_zero, e1_one] at h
    omega
  · exfalso
    have h := hw'.symm.trans hw
    rw [site_ext_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, e0_zero, e0_one, e1_zero, e1_one] at h
    omega
  · have h := hw'.symm.trans hw
    rw [site_ext_iff] at h
    simp only [Pi.add_apply, Pi.sub_apply, e0_zero, e0_one] at h
    congr 1
    rw [site_ext_iff]
    omega

lemma bondGraph_adj_iff {e f : Sym2 Site} :
    bondGraph.Adj e f ↔ e ≠ f ∧ ∃ x, e ∈ plaquette x ∧ f ∈ plaquette x := Iff.rfl

/-- Every bond of the outer boundary is a horizontal or a vertical lattice bond. -/
lemma exists_hbond_or_vbond {D : Set Site} {e : Sym2 Site} (he : e ∈ outerBoundary D) :
    (∃ w, e = hbond w) ∨ (∃ w, e = vbond w) := by
  obtain ⟨i, -, j, -, hij, rfl⟩ := he
  rcases (latticeGraph_two_adj_iff' i j).1 hij with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inl ⟨j, Sym2.eq_swap⟩
  · exact Or.inr ⟨i, rfl⟩
  · exact Or.inr ⟨j, Sym2.eq_swap⟩

open scoped Classical in
/-- In a plaquette carrying exactly two bonds of `c`, a bond of `c` has a unique partner. -/
lemma exists_partner {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (hx : plaquetteDeg c x = 2) (hex : e ∈ plaquette x) (hec : e ∈ c) :
    ∃ f, f ≠ e ∧ f ∈ plaquette x ∧ f ∈ c ∧
      ∀ g, g ∈ plaquette x → g ∈ c → g ≠ e → g = f := by
  simp only [plaquetteDeg] at hx
  obtain ⟨a, b, hab, hfil⟩ := Finset.card_eq_two.1 hx
  have hmem : ∀ g : Sym2 Site, (g ∈ plaquette x ∧ g ∈ c) ↔ (g = a ∨ g = b) := by
    intro g
    constructor
    · intro hg
      have : g ∈ (plaquette x).filter (· ∈ c) := Finset.mem_filter.2 hg
      rw [hfil] at this
      simpa using this
    · intro hg
      have : g ∈ (plaquette x).filter (· ∈ c) := by rw [hfil]; simpa using hg
      exact Finset.mem_filter.1 this
  have hea : e = a ∨ e = b := (hmem e).1 ⟨hex, hec⟩
  rcases hea with rfl | rfl
  · exact ⟨b, hab.symm, ((hmem b).2 (Or.inr rfl)).1, ((hmem b).2 (Or.inr rfl)).2,
      fun g hg hgc hge ↦ ((hmem g).1 ⟨hg, hgc⟩).resolve_left hge⟩
  · exact ⟨a, hab, ((hmem a).2 (Or.inl rfl)).1, ((hmem a).2 (Or.inl rfl)).2,
      fun g hg hgc hge ↦ ((hmem g).1 ⟨hg, hgc⟩).resolve_right hge⟩

/-- **The outer boundary is `2`-regular in the plaquette-adjacency graph** (Georgii's circuit
property, in the form needed for the counting Lemma (6.13)): every boundary bond is
plaquette-adjacent to exactly two other boundary bonds. -/
theorem outerBoundary_two_regular {D : Set Site} (hD : D.Finite) (hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) {e : Sym2 Site} (he : e ∈ outerBoundary D) :
    ∃ f g : Sym2 Site, f ≠ g ∧
      ∀ h : Sym2 Site, (h ∈ outerBoundary D ∧ bondGraph.Adj e h) ↔ (h = f ∨ h = g) := by
  classical
  -- the two plaquettes `x₁ ≠ x₂` of `e`
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁₂, hplaq⟩ :
      ∃ x₁ x₂ : Site, e ∈ plaquette x₁ ∧ e ∈ plaquette x₂ ∧ x₁ ≠ x₂ ∧
        ∀ x : Site, e ∈ plaquette x → x = x₁ ∨ x = x₂ := by
    rcases exists_hbond_or_vbond he with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · refine ⟨w, w - e1, (hbond_mem_plaquette_iff w w).2 (Or.inl rfl),
        (hbond_mem_plaquette_iff w (w - e1)).2 (Or.inr rfl), ?_,
        fun x hx ↦ (hbond_mem_plaquette_iff w x).1 hx⟩
      intro hc
      have := congrArg (fun z ↦ z 1) hc
      simp only [Pi.sub_apply, e1_one] at this
      omega
    · refine ⟨w, w - e0, (vbond_mem_plaquette_iff w w).2 (Or.inl rfl),
        (vbond_mem_plaquette_iff w (w - e0)).2 (Or.inr rfl), ?_,
        fun x hx ↦ (vbond_mem_plaquette_iff w x).1 hx⟩
      intro hc
      have := congrArg (fun z ↦ z 0) hc
      simp only [Pi.sub_apply, e0_zero] at this
      omega
  have hd₁ : plaquetteDeg (outerBoundary D) x₁ = 2 :=
    plaquetteDeg_outerBoundary_eq_two hD hne hconn x₁ ⟨e, Finset.mem_coe.2 hx₁, he⟩
  have hd₂ : plaquetteDeg (outerBoundary D) x₂ = 2 :=
    plaquetteDeg_outerBoundary_eq_two hD hne hconn x₂ ⟨e, Finset.mem_coe.2 hx₂, he⟩
  obtain ⟨f, hfe, hfx, hfc, hfu⟩ := exists_partner hd₁ hx₁ he
  obtain ⟨g, hge, hgx, hgc, hgu⟩ := exists_partner hd₂ hx₂ he
  refine ⟨f, g, ?_, ?_⟩
  · intro hfg
    exact hfe (eq_of_mem_plaquette₂ hx₁₂ hx₁ hx₂ hfx (hfg ▸ hgx))
  · intro h
    constructor
    · rintro ⟨hhb, hadj⟩
      rw [bondGraph_adj_iff] at hadj
      obtain ⟨hne', x, hex, hhx⟩ := hadj
      rcases hplaq x hex with rfl | rfl
      · exact Or.inl (hfu h hhx hhb (fun hc ↦ hne' hc.symm))
      · exact Or.inr (hgu h hhx hhb (fun hc ↦ hne' hc.symm))
    · rintro (rfl | rfl)
      · exact ⟨hfc, bondGraph_adj_iff.2 ⟨Ne.symm hfe, x₁, hx₁, hfx⟩⟩
      · exact ⟨hgc, bondGraph_adj_iff.2 ⟨Ne.symm hge, x₂, hx₂, hgx⟩⟩

end MeasureTheory.GibbsMeasure.Peierls

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Int.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Set.Infinite

/-!
# The Hasse graphs of `ℤ` and `ℕ`

`SimpleGraph.hasse ℤ` is the nearest-neighbour graph of `ℤ`: `i` and `j` are adjacent iff
`|i - j| = 1`. It is locally finite, with `∂i = {i - 1, i + 1}`; `SimpleGraph.hasseIntWalk a n` is
the walk `a → a + 1 → ⋯ → a + n`.

`SimpleGraph.hasse ℕ` is the half-line. In a subgraph `G ≤ hasse ℕ` (a bond configuration on the
half-line) the connected component of `v` is infinite iff every bond `{i, i + 1}` with `i ≥ v` is
present (`SimpleGraph.infinite_supp_connectedComponentMk_iff`), so `G` has an infinite connected
component iff all but finitely many bonds are present (`SimpleGraph.exists_infinite_supp_iff`),
and such a component is unique (`SimpleGraph.ConnectedComponent.eq_of_infinite_supp`).
-/

@[expose] public section

namespace SimpleGraph

lemma hasse_int_adj (i j : ℤ) : (hasse ℤ).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  rw [hasse_adj, Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]

lemma neighborSet_hasse_int (i : ℤ) : (hasse ℤ).neighborSet i = ({i - 1, i + 1} : Set ℤ) := by
  ext j
  simp only [mem_neighborSet, hasse_int_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- `ℤ` is a locally finite graph. -/
noncomputable instance instLocallyFiniteHasseInt : (hasse ℤ).LocallyFinite := fun i ↦
  (show ((hasse ℤ).neighborSet i).Finite by
    rw [neighborSet_hasse_int]
    exact Set.toFinite _).fintype

lemma neighborFinset_hasse_int (i : ℤ) : (hasse ℤ).neighborFinset i = {i - 1, i + 1} := by
  ext j
  simp only [mem_neighborFinset, hasse_int_adj, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `j ↦ s(j, j + 1)` is injective on `ℤ`: an edge of `hasse ℤ` determines its left endpoint. -/
lemma injective_mk_succ_int : Function.Injective fun j : ℤ ↦ s(j, j + 1) := by
  intro j k h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · omega

/-- The edges of `hasse ℤ` meeting `Λ` are the bonds `{j, j + 1}` with `j ∈ Λ` or `j + 1 ∈ Λ`. -/
lemma mem_bondsOf_hasse_int {Λ : Finset ℤ} {e : Sym2 ℤ} :
    e ∈ (hasse ℤ).bondsOf Λ ↔ ∃ j : ℤ, (j ∈ Λ ∨ j + 1 ∈ Λ) ∧ e = s(j, j + 1) := by
  constructor
  · induction e using Sym2.ind with
    | _ a b =>
      rw [mk_mem_bondsOf]
      rintro ⟨hadj, hab⟩
      rcases (hasse_int_adj a b).1 hadj with h | h
      · exact ⟨a, by rwa [h], by rw [h]⟩
      · exact ⟨b, by rw [h]; exact hab.symm, by rw [h, Sym2.eq_swap]⟩
  · rintro ⟨j, hj, rfl⟩
    exact mk_mem_bondsOf.2 ⟨(hasse_int_adj j (j + 1)).2 (Or.inl rfl), hj⟩

/-! ### Walks along `ℤ` -/

/-- The walk `a → a + 1 → ⋯ → a + n` in `hasse ℤ`. -/
def hasseIntWalk (a : ℤ) : (n : ℕ) → (hasse ℤ).Walk a (a + n)
  | 0 => (Walk.nil : (hasse ℤ).Walk a a).copy rfl (by simp)
  | n + 1 => (hasseIntWalk a n).concat
      ((hasse_int_adj (a + n) (a + (n + 1 : ℕ))).2 (Or.inl (by push_cast; omega)))

/-- The support of `hasseIntWalk a n` is the interval `[a, a + n]`. -/
lemma mem_support_hasseIntWalk {a x : ℤ} : ∀ {n : ℕ}, x ∈ (hasseIntWalk a n).support →
    a ≤ x ∧ x ≤ a + n
  | 0, hx => by
    rw [hasseIntWalk, Walk.support_copy, Walk.support_nil, List.mem_singleton] at hx
    omega
  | n + 1, hx => by
    rw [hasseIntWalk, Walk.support_concat, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · have := mem_support_hasseIntWalk hx
      push_cast
      omega
    · push_cast
      omega

/-! ### The Hasse graph of `ℕ` and its subgraphs -/

lemma hasse_nat_adj (i j : ℕ) : (hasse ℕ).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  rw [hasse_adj, Nat.covBy_iff_add_one_eq, Nat.covBy_iff_add_one_eq]

variable {G : SimpleGraph ℕ}

/-- In a subgraph of the half-line, a walk starting at or below `i` that cannot use the bond
`{i, i + 1}` stays at or below `i`. -/
lemma le_of_reachable_of_not_adj_succ (hG : G ≤ hasse ℕ) {i v w : ℕ}
    (hi : ¬ G.Adj i (i + 1)) (hv : v ≤ i) (h : G.Reachable v w) : w ≤ i := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hv
  | tail _ hadj ih =>
    rcases (hasse_nat_adj _ _).1 (hG hadj) with h1 | h1
    · rcases lt_or_eq_of_le ih with hlt | rfl
      · omega
      · exact absurd (h1 ▸ hadj) hi
    · omega

/-- In a subgraph of the half-line, `w ≥ v` is reachable from `v` as soon as all the bonds
between them are present. -/
lemma reachable_of_forall_adj_succ {v w : ℕ} (hvw : v ≤ w)
    (h : ∀ i, v ≤ i → i < w → G.Adj i (i + 1)) : G.Reachable v w := by
  induction w, hvw using Nat.le_induction with
  | base => exact Reachable.refl v
  | succ k hk ih =>
    exact (ih fun i hi hik ↦ h i hi (Nat.lt_succ_of_lt hik)).trans
      (h k hk (Nat.lt_succ_self k)).reachable

/-- In a subgraph `G` of the half-line `hasse ℕ`, the connected component of `v` is infinite iff
every bond `{i, i + 1}` with `i ≥ v` is present in `G`. -/
theorem infinite_supp_connectedComponentMk_iff (hG : G ≤ hasse ℕ) (v : ℕ) :
    (G.connectedComponentMk v).supp.Infinite ↔ ∀ i, v ≤ i → G.Adj i (i + 1) := by
  constructor
  · intro hinf i hvi
    by_contra hadj
    refine hinf ((Set.finite_Iic i).subset fun w hw ↦ ?_)
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hw
    exact le_of_reachable_of_not_adj_succ hG hadj hvi hw.symm
  · intro h
    refine (Set.Ici_infinite v).mono fun w hw ↦ ?_
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact (reachable_of_forall_adj_succ hw fun i hi _ ↦ h i hi).symm

/-- A subgraph of the half-line has an infinite connected component iff all but finitely many
bonds `{i, i + 1}` are present. -/
theorem exists_infinite_supp_iff (hG : G ≤ hasse ℕ) :
    (∃ C : G.ConnectedComponent, C.supp.Infinite) ↔ ∃ v, ∀ i, v ≤ i → G.Adj i (i + 1) := by
  constructor
  · rintro ⟨C, hC⟩
    induction C using ConnectedComponent.ind with
    | h v => exact ⟨v, (infinite_supp_connectedComponentMk_iff hG v).1 hC⟩
  · rintro ⟨v, hv⟩
    exact ⟨G.connectedComponentMk v, (infinite_supp_connectedComponentMk_iff hG v).2 hv⟩

/-- A subgraph of the half-line has at most one infinite connected component. -/
theorem ConnectedComponent.eq_of_infinite_supp (hG : G ≤ hasse ℕ) {C D : G.ConnectedComponent}
    (hC : C.supp.Infinite) (hD : D.supp.Infinite) : C = D := by
  induction C using ConnectedComponent.ind with
  | h v =>
  induction D using ConnectedComponent.ind with
  | h w =>
  rw [infinite_supp_connectedComponentMk_iff hG] at hC hD
  exact ConnectedComponent.sound
    ((reachable_of_forall_adj_succ (le_max_left v w) fun i hi _ ↦ hC i hi).trans
      (reachable_of_forall_adj_succ (le_max_right v w) fun i hi _ ↦ hD i hi).symm)

end SimpleGraph

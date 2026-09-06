/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.CayleyTree
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.RootedTree
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!
# Balls and spheres in a locally finite graph

`SimpleGraph.ballFinset G r n` is the ball of radius `n` around `r`, built by repeatedly adjoining
the outer boundary. In a connected graph it is `{i | d(r, i) ≤ n}` (`mem_ballFinset_iff`), it is
connected (`connected_induce_ballFinset`), and its outer boundary is the sphere of radius `n + 1`
(`mem_outerBoundary_ballFinset_iff`).

On a Cayley tree of degree `d + 1` every vertex of the sphere of radius `n + 1` has exactly one
neighbour inside the ball of radius `n` (its parent) and therefore `d` neighbours on the next
sphere; consequently the spheres grow, `card_lt_card_outerBoundary_ballFinset`: for `d ≥ 2` the
sphere of radius `n + 1` has more than `n` vertices, so the spheres are arbitrarily large.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] {d : ℕ}

/-! ### Adjoining the whole outer boundary -/

/-- Adjoining any set of outer-boundary vertices to a connected set keeps it connected. -/
lemma connected_induce_union_of_subset_outerBoundary {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) {Δ : Finset V} (hΔ : Δ ⊆ G.outerBoundary Λ) :
    (G.induce ((Λ ∪ Δ : Finset V) : Set V)).Connected := by
  induction Δ using Finset.induction_on with
  | empty => rw [Finset.union_empty]; exact hΛ
  | @insert x Δ hx ih =>
    have hxb : x ∈ G.outerBoundary Λ := hΔ (Finset.mem_insert_self x Δ)
    have hsub : Δ ⊆ G.outerBoundary Λ := fun y hy ↦ hΔ (Finset.mem_insert_of_mem hy)
    have hcon := ih hsub
    have hx' : x ∈ G.outerBoundary (Λ ∪ Δ) := by
      obtain ⟨hxΛ, j, hj, hxj⟩ := (G.mem_outerBoundary).1 hxb
      exact (G.mem_outerBoundary).2
        ⟨by simp only [Finset.mem_union, not_or]; exact ⟨hxΛ, hx⟩, j,
          Finset.mem_union_left _ hj, hxj⟩
    rw [Finset.union_insert]
    exact connected_induce_insert_of_mem_outerBoundary hcon hx'

/-! ### The ball of radius `n` -/

/-- The **ball** of radius `n` around `r`: `{i | d(r, i) ≤ n}` in a connected graph
(`mem_ballFinset_iff`), built by adjoining the outer boundary `n` times. -/
def ballFinset (G : SimpleGraph V) [G.LocallyFinite] (r : V) : ℕ → Finset V
  | 0 => {r}
  | n + 1 => G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n)

@[simp] lemma ballFinset_zero (r : V) : G.ballFinset r 0 = {r} := rfl

lemma ballFinset_succ (r : V) (n : ℕ) :
    G.ballFinset r (n + 1) = G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n) := rfl

lemma mem_ballFinset_self (r : V) (n : ℕ) : r ∈ G.ballFinset r n := by
  induction n with
  | zero => simp
  | succ n ih => exact Finset.mem_union_left _ ih

omit [DecidableEq V] [G.LocallyFinite] in
/-- The predecessor of a vertex at distance `m + 1`: some neighbour at distance `m`. -/
lemma exists_adj_dist_eq (hG : G.Connected) {r i : V} {m : ℕ} (h : G.dist r i = m + 1) :
    ∃ j, G.Adj j i ∧ G.dist r j = m := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist i r
  have hne : i ≠ r := by
    intro hcon
    rw [hcon, G.dist_self] at h
    omega
  obtain ⟨j, hij, q, rfl⟩ := p.exists_eq_cons_of_ne hne
  refine ⟨j, hij.symm, ?_⟩
  have hq : G.dist j r ≤ q.length := dist_le q
  have hlen : q.length + 1 = G.dist i r := by
    rw [← hp, Walk.length_cons]
  have htri : G.dist i r ≤ 1 + G.dist j r := by
    have := hG.dist_triangle (u := i) (v := j) (w := r)
    rwa [G.dist_eq_one_iff_adj.2 hij] at this
  rw [dist_comm] at h
  rw [dist_comm]
  omega

lemma dist_le_of_mem_ballFinset (hG : G.Connected) {r i : V} {n : ℕ}
    (h : i ∈ G.ballFinset r n) : G.dist r i ≤ n := by
  induction n generalizing i with
  | zero =>
    rw [ballFinset_zero, Finset.mem_singleton] at h
    simp [h]
  | succ n ih =>
    rw [ballFinset_succ, Finset.mem_union] at h
    rcases h with h | h
    · exact (ih h).trans (Nat.le_succ n)
    · obtain ⟨-, j, hj, hij⟩ := (G.mem_outerBoundary).1 h
      have h1 : G.dist r i ≤ G.dist r j + G.dist j i := hG.dist_triangle
      rw [G.dist_eq_one_iff_adj.2 hij.symm] at h1
      have := ih hj
      omega

lemma mem_ballFinset_of_dist_le (hG : G.Connected) {r i : V} {n : ℕ}
    (h : G.dist r i ≤ n) : i ∈ G.ballFinset r n := by
  induction n generalizing i with
  | zero =>
    rw [ballFinset_zero, Finset.mem_singleton]
    exact ((G.dist_eq_zero_iff_eq_or_not_reachable.1 (Nat.le_zero.1 h)).resolve_right
      (fun hcon ↦ hcon (hG.preconnected r i))).symm
  | succ n ih =>
    rcases Nat.lt_or_ge (G.dist r i) (n + 1) with hlt | hge
    · exact Finset.mem_union_left _ (ih (Nat.lt_succ_iff.1 hlt))
    · have heq : G.dist r i = n + 1 := le_antisymm h hge
      obtain ⟨j, hji, hj⟩ := exists_adj_dist_eq hG heq
      refine Finset.mem_union_right _ ((G.mem_outerBoundary).2 ⟨fun hcon ↦ ?_, j,
        ih hj.le, hji.symm⟩)
      have := dist_le_of_mem_ballFinset hG hcon
      omega

/-- **The ball is the metric ball.** -/
theorem mem_ballFinset_iff (hG : G.Connected) {r i : V} {n : ℕ} :
    i ∈ G.ballFinset r n ↔ G.dist r i ≤ n :=
  ⟨dist_le_of_mem_ballFinset hG, mem_ballFinset_of_dist_le hG⟩

/-- **The outer boundary of a ball is the next sphere.** -/
theorem mem_outerBoundary_ballFinset_iff (hG : G.Connected) {r k : V} {n : ℕ} :
    k ∈ G.outerBoundary (G.ballFinset r n) ↔ G.dist r k = n + 1 := by
  constructor
  · intro h
    obtain ⟨hk, j, hj, hkj⟩ := (G.mem_outerBoundary).1 h
    have h1 : G.dist r k ≤ G.dist r j + G.dist j k := hG.dist_triangle
    rw [G.dist_eq_one_iff_adj.2 hkj.symm] at h1
    have h2 := dist_le_of_mem_ballFinset hG hj
    have h3 : ¬ G.dist r k ≤ n := fun hcon ↦ hk (mem_ballFinset_of_dist_le hG hcon)
    omega
  · intro h
    obtain ⟨j, hjk, hj⟩ := exists_adj_dist_eq hG h
    refine (G.mem_outerBoundary).2 ⟨fun hcon ↦ ?_, j, mem_ballFinset_of_dist_le hG hj.le, hjk.symm⟩
    have := dist_le_of_mem_ballFinset hG hcon
    omega

/-- **A ball is connected.** -/
theorem connected_induce_ballFinset (r : V) (n : ℕ) :
    (G.induce ((G.ballFinset r n : Finset V) : Set V)).Connected := by
  induction n with
  | zero =>
    rw [ballFinset_zero, Finset.coe_singleton]
    rw [SimpleGraph.connected_induce_iff_forall_exists_walk]
    refine ⟨⟨r, rfl⟩, fun u hu v hv ↦ ?_⟩
    simp only [Set.mem_singleton_iff] at hu hv
    subst hu; subst hv
    exact ⟨SimpleGraph.Walk.nil, fun x hx ↦ by simpa using hx⟩
  | succ n ih => exact connected_induce_union_of_subset_outerBoundary ih subset_rfl

/-! ### Spheres in a Cayley tree grow -/

variable (hG : G.IsCayleyTree d)
include hG

/-- In a tree, a vertex at distance `n + 1` from `r` has exactly one neighbour in the ball of
radius `n`: its parent. -/
lemma card_neighborFinset_inter_ballFinset_le_one {r i : V} {n : ℕ}
    (hi : G.dist r i = n + 1) :
    (G.neighborFinset i ∩ G.ballFinset r n).card ≤ 1 := by
  refine Finset.card_le_one.2 fun j hj j' hj' ↦ ?_
  have key : ∀ k ∈ G.neighborFinset i ∩ G.ballFinset r n, G.Adj i k ∧ r ∈ G.past k i := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_inter.1 hk
    have hadj : G.Adj i k := (G.mem_neighborFinset i k).1 hk1
    have hle := dist_le_of_mem_ballFinset hG.connected hk2
    refine ⟨hadj, ?_⟩
    rw [mem_past]
    rcases hG.isTree.dist_eq_dist_add_one_of_adj r hadj with h | h <;> omega
  obtain ⟨hij, hjp⟩ := key j hj
  obtain ⟨hij', hj'p⟩ := key j' hj'
  exact hG.isTree.eq_of_mem_past_of_mem_past hij hij' hjp hj'p

/-- In a Cayley tree of degree `d + 1`, a vertex at distance `n + 1` from `r` has at least `d`
neighbours outside the ball of radius `n`. -/
lemma le_card_neighborFinset_sdiff_ballFinset {r i : V} {n : ℕ} (hi : G.dist r i = n + 1) :
    d ≤ (G.neighborFinset i \ G.ballFinset r n).card := by
  have hcard := Finset.card_sdiff_add_card_inter (G.neighborFinset i) (G.ballFinset r n)
  rw [hG.card_neighborFinset i] at hcard
  have := card_neighborFinset_inter_ballFinset_le_one hG hi
  omega

/-- **The spheres of a Cayley tree grow by a factor `d`.** -/
theorem mul_card_le_card_outerBoundary_ballFinset (r : V) (n : ℕ) :
    d * (G.outerBoundary (G.ballFinset r n)).card
      ≤ (G.outerBoundary (G.ballFinset r (n + 1))).card := by
  classical
  have hconn := hG.connected
  set f : V → V := fun k ↦ G.anchor (G.ballFinset r (n + 1)) k with hf
  have hmaps : ∀ k ∈ G.outerBoundary (G.ballFinset r (n + 1)), f k ∈
      G.outerBoundary (G.ballFinset r n) := by
    intro k hk
    have hkd : G.dist r k = n + 2 := mem_outerBoundary_ballFinset_iff hconn |>.1 hk
    have hadj : G.Adj k (f k) := G.adj_anchor hk
    have hmem : f k ∈ G.ballFinset r (n + 1) := G.anchor_mem hk
    have hle := dist_le_of_mem_ballFinset hconn hmem
    rw [mem_outerBoundary_ballFinset_iff hconn]
    rcases hG.isTree.dist_eq_dist_add_one_of_adj r hadj with h | h <;> omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc d * (G.outerBoundary (G.ballFinset r n)).card
      = ∑ _i ∈ G.outerBoundary (G.ballFinset r n), d := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ G.outerBoundary (G.ballFinset r n),
          ((G.outerBoundary (G.ballFinset r (n + 1))).filter fun k ↦ f k = i).card := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hid : G.dist r i = n + 1 := mem_outerBoundary_ballFinset_iff hconn |>.1 hi
        refine le_trans (le_card_neighborFinset_sdiff_ballFinset hG hid)
          (Finset.card_le_card fun k hk ↦ ?_)
        obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.1 hk
        have hadj : G.Adj i k := (G.mem_neighborFinset i k).1 hk1
        have hkd : G.dist r k = n + 2 := by
          have h2 : ¬ G.dist r k ≤ n := fun hcon ↦ hk2 (mem_ballFinset_of_dist_le hconn hcon)
          rcases hG.isTree.dist_eq_dist_add_one_of_adj r hadj with h | h <;> omega
        have hkb : k ∈ G.outerBoundary (G.ballFinset r (n + 1)) :=
          mem_outerBoundary_ballFinset_iff hconn |>.2 hkd
        refine Finset.mem_filter.2 ⟨hkb, ?_⟩
        exact hG.isAcyclic.anchor_eq (connected_induce_ballFinset r (n + 1)) hkb
          (mem_ballFinset_of_dist_le hconn hid.le) hadj.symm

/-- **The spheres of a Cayley tree of degree `d + 1 ≥ 3` are arbitrarily large.** -/
theorem lt_card_outerBoundary_ballFinset (hd : 2 ≤ d) (r : V) (n : ℕ) :
    n < (G.outerBoundary (G.ballFinset r n)).card := by
  induction n with
  | zero =>
    rw [ballFinset_zero, SimpleGraph.outerBoundary_singleton, hG.card_neighborFinset]
    omega
  | succ n ih =>
    have h := mul_card_le_card_outerBoundary_ballFinset hG r n
    have h2 : 2 * (G.outerBoundary (G.ballFinset r n)).card
        ≤ d * (G.outerBoundary (G.ballFinset r n)).card :=
      Nat.mul_le_mul_right _ hd
    omega

/-- Every `N` is exceeded by the size of some sphere of a Cayley tree of degree `d + 1 ≥ 3`. -/
theorem exists_le_card_outerBoundary_ballFinset (hd : 2 ≤ d) (r : V) (N : ℕ) :
    ∃ n, N ≤ (G.outerBoundary (G.ballFinset r n)).card :=
  ⟨N, (lt_card_outerBoundary_ballFinset hG hd r N).le⟩

end SimpleGraph

end

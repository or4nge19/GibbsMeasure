/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Self-avoiding paths of a given length from a vertex

* `SimpleGraph.finite_setOf_exists_walk_length_le`: in a locally finite graph only finitely many
  vertices are joined to a given vertex by a walk of length at most `n`.
* `SimpleGraph.exists_isPath_length_eq_of_infinite_supp`: in a locally finite graph, an infinite
  connected component of the induced subgraph `G.induce s` contains, from each of its vertices, a
  path of every length whose support lies in `s`.
* `SimpleGraph.pathLists G a n`: the self-avoiding paths of length `n` from `a`, recorded as
  vertex lists with the most recent vertex first; `SimpleGraph.mem_pathLists_iff` characterises
  them, `SimpleGraph.reverse_support_mem_pathLists` puts the support of every path there, and
  `SimpleGraph.card_pathLists_succ_le` is the classical bound `Δ (Δ - 1)^n` on the number of
  self-avoiding paths of length `n + 1` from a vertex of a graph of maximal degree `Δ` (each step
  after the first cannot return to the previous vertex).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Balls of a locally finite graph -/

/-- In a locally finite graph, finitely many vertices are joined to `a` by a walk of length at
most `n`. -/
theorem finite_setOf_exists_walk_length_le [G.LocallyFinite] (a : V) :
    ∀ n : ℕ, {x | ∃ p : G.Walk x a, p.length ≤ n}.Finite
  | 0 => by
    refine (Set.finite_singleton a).subset ?_
    rintro x ⟨p, hp⟩
    cases p with
    | nil => exact Set.mem_singleton a
    | cons h q => simp at hp
  | n + 1 => by
    have ih := finite_setOf_exists_walk_length_le a n
    refine (Set.Finite.union ih (Set.Finite.biUnion ih fun y _ ↦
      (G.neighborSet y).toFinite)).subset ?_
    rintro x ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl ⟨Walk.nil, Nat.zero_le _⟩
    | @cons _ y _ h q =>
      refine Or.inr (Set.mem_biUnion (x := y) ⟨q, ?_⟩ h.symm)
      rw [Walk.length_cons] at hp
      omega

/-- In a locally finite graph, an infinite connected component of `G.induce s` contains from each
of its vertices a path of every length, with support in `s`. -/
theorem exists_isPath_length_eq_of_infinite_supp [G.LocallyFinite] {s : Set V} {a : V}
    (ha : a ∈ s) (h : ((G.induce s).connectedComponentMk ⟨a, ha⟩).supp.Infinite) (n : ℕ) :
    ∃ (x : V) (p : G.Walk a x), p.IsPath ∧ p.length = n ∧ ∀ v ∈ p.support, v ∈ s := by
  classical
  have hfin := finite_setOf_exists_walk_length_le (G := G) a n
  obtain ⟨⟨v, hvs⟩, hvc, hvB⟩ : ∃ v ∈ ((G.induce s).connectedComponentMk ⟨a, ha⟩).supp,
      v.1 ∉ {x | ∃ p : G.Walk x a, p.length ≤ n} := by
    by_contra hcon
    push Not at hcon
    exact h ((hfin.preimage Subtype.val_injective.injOn).subset hcon)
  rw [ConnectedComponent.mem_supp_iff] at hvc
  obtain ⟨q⟩ := (ConnectedComponent.eq.1 hvc).symm
  obtain ⟨p, hpath, hsub⟩ : ∃ p : G.Walk a v, p.IsPath ∧
      p.support ⊆ (q.map (Embedding.induce s).toHom).support :=
    ⟨(q.map (Embedding.induce s).toHom).bypass, Walk.bypass_isPath _,
      Walk.support_bypass_subset_support _⟩
  have hpsupp : ∀ x ∈ p.support, x ∈ s := by
    intro x hx
    have hx' := hsub hx
    rw [Walk.support_map, List.mem_map] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact y.2
  have hlen : n < p.length := by
    by_contra hle
    exact hvB ⟨p.reverse, by rw [Walk.length_reverse]; exact not_lt.1 hle⟩
  refine ⟨p.getVert n, p.take n, hpath.take n, ?_, ?_⟩
  · rw [Walk.take_length]
    exact min_eq_left hlen.le
  · intro x hx
    rw [Walk.support_take] at hx
    exact hpsupp x (List.take_subset _ _ hx)

/-! ### The self-avoiding paths from a vertex, as vertex lists -/

variable (G) [DecidableEq V] [G.LocallyFinite]

/-- The self-avoiding paths of length `n` from `a`, as vertex lists with the most recent vertex
first: `[a]` for `n = 0`, and for `n + 1` every list `x :: l` with `l` a path of length `n` and
`x` a neighbour of the head of `l` not already visited. -/
def pathLists (a : V) : ℕ → Finset (List V)
  | 0 => {[a]}
  | n + 1 => (pathLists a n).biUnion fun l ↦
      ((G.neighborFinset (l.headD a)).filter fun x ↦ x ∉ l).image fun x ↦ x :: l

variable {G}

/-- The self-avoiding paths of length `n` from `a` are exactly the lists of `n + 1` distinct
vertices, consecutive ones adjacent, ending at `a`. -/
theorem mem_pathLists_iff {a : V} : ∀ {n : ℕ} {l : List V},
    l ∈ G.pathLists a n ↔
      l.length = n + 1 ∧ l.getLast? = some a ∧ l.IsChain G.Adj ∧ l.Nodup
  | 0, l => by
    rw [pathLists, Finset.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hlen, hlast, -, -⟩
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlen
      simpa using hlast
  | n + 1, l => by
    rw [pathLists, Finset.mem_biUnion]
    constructor
    · rintro ⟨l', hl', hl⟩
      rw [Finset.mem_image] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      rw [Finset.mem_filter, mem_neighborFinset] at hx
      obtain ⟨hlen, hlast, hchain, hnodup⟩ := mem_pathLists_iff.1 hl'
      obtain ⟨y, l'', rfl⟩ : ∃ y l'', l' = y :: l'' := by
        cases l' with
        | nil => simp at hlen
        | cons y l'' => exact ⟨y, l'', rfl⟩
      refine ⟨by simpa using hlen, by simpa using hlast, ?_, ?_⟩
      · exact List.IsChain.cons_cons (by simpa using hx.1.symm) hchain
      · exact List.nodup_cons.2 ⟨hx.2, hnodup⟩
    · rintro ⟨hlen, hlast, hchain, hnodup⟩
      obtain ⟨x, y, l'', rfl⟩ : ∃ x y l'', l = x :: y :: l'' := by
        match l, hlen with
        | x :: y :: l'', _ => exact ⟨x, y, l'', rfl⟩
      rw [List.isChain_cons_cons] at hchain
      rw [List.nodup_cons] at hnodup
      refine ⟨y :: l'', mem_pathLists_iff.2 ⟨by simpa using hlen, by simpa using hlast, hchain.2,
        hnodup.2⟩, ?_⟩
      rw [Finset.mem_image]
      exact ⟨x, Finset.mem_filter.2 ⟨(mem_neighborFinset _ _ _).2 hchain.1.symm, hnodup.1⟩, rfl⟩

/-- The (reversed) support of a path of length `n` from `a` is one of the lists of
`G.pathLists a n`. -/
theorem reverse_support_mem_pathLists {a x : V} {p : G.Walk a x} (hp : p.IsPath) :
    p.support.reverse ∈ G.pathLists a p.length := by
  refine mem_pathLists_iff.2 ⟨by simp [Walk.length_support], ?_, ?_, ?_⟩
  · rw [List.getLast?_reverse, ← Walk.cons_tail_support]
    rfl
  · rw [List.isChain_reverse]
    exact p.isChain_adj_support.imp fun _ _ h ↦ h.symm
  · exact List.nodup_reverse.2 hp.support_nodup

/-- Every element of a list of `G.pathLists a n` is a vertex; the first one is `a` and the head of
a list of `G.pathLists a (n + 1)` is a neighbour of the second vertex. -/
theorem exists_cons_cons_of_mem_pathLists_succ {a : V} {n : ℕ} {l : List V}
    (hl : l ∈ G.pathLists a (n + 1)) :
    ∃ x y l', l = x :: y :: l' ∧ G.Adj x y ∧ x ∉ y :: l' := by
  obtain ⟨hlen, -, hchain, hnodup⟩ := mem_pathLists_iff.1 hl
  obtain ⟨x, y, l'', rfl⟩ : ∃ x y l'', l = x :: y :: l'' := by
    match l, hlen with
    | x :: y :: l'', _ => exact ⟨x, y, l'', rfl⟩
  rw [List.isChain_cons_cons] at hchain
  rw [List.nodup_cons] at hnodup
  exact ⟨x, y, l'', rfl, hchain.1, hnodup.1⟩

/-- **The number of self-avoiding paths of length `n + 1` from a vertex of a graph of maximal
degree `Δ` is at most `Δ (Δ - 1)^n`**: the first step has at most `Δ` choices, and each further
step at most `Δ - 1`, since it cannot return to the previous vertex. -/
theorem card_pathLists_succ_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (a : V) :
    ∀ n : ℕ, (G.pathLists a (n + 1)).card ≤ Δ * (Δ - 1) ^ n
  | 0 => by
    rw [pathLists, pathLists, Finset.singleton_biUnion, pow_zero, mul_one]
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hΔ _))
  | n + 1 => by
    rw [pathLists]
    refine (Finset.card_biUnion_le_card_mul _ _ (Δ - 1) fun l hl ↦ ?_).trans ?_
    · obtain ⟨x, y, l', rfl, hxy, -⟩ := exists_cons_cons_of_mem_pathLists_succ hl
      refine Finset.card_image_le.trans ?_
      have hsub : ((G.neighborFinset ((x :: y :: l').headD a)).filter
          fun z ↦ z ∉ x :: y :: l') ⊆ (G.neighborFinset x).erase y := by
        intro z hz
        rw [Finset.mem_filter] at hz
        exact Finset.mem_erase.2 ⟨fun hzy ↦ hz.2 (by simp [hzy]), hz.1⟩
      refine (Finset.card_le_card hsub).trans ?_
      rw [Finset.card_erase_of_mem ((mem_neighborFinset _ _ _).2 hxy)]
      exact Nat.sub_le_sub_right (hΔ x) 1
    · rw [pow_succ, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (card_pathLists_succ_le hΔ a n)

end SimpleGraph

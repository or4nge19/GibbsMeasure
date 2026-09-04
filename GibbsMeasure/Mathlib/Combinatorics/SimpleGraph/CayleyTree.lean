/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Cayley trees

Georgii §12.2 works on `𝒞𝒯(d)`, "the unique connected tree with `|∂i| = d + 1` for all `i`".
`SimpleGraph.IsCayleyTree G d` is that property: `G` is a tree, regular of degree `d + 1`.

Georgii also uses that `𝒞𝒯(d)` is bipartite (for the alternating boundary laws of the
antiferromagnetic case). That is *not* proved here: it is Mathlib's `SimpleGraph.IsTree.isBipartite`
(a tree is `2`-colourable, `SimpleGraph.IsTree.coloringTwoOfVert`), which holds for every tree.

`SimpleGraph.hasse ℤ` is a Cayley tree of degree `1` (`SimpleGraph.isCayleyTree_hasse_int`); the
proof that it is acyclic goes through the general "cut" lemma
`SimpleGraph.Walk.mem_of_adj_closed`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reachability and cuts -/

/-- A set closed under the adjacency relation is closed under walks. -/
lemma Walk.mem_of_adj_closed {S : Set V} (hS : ∀ ⦃u v⦄, G.Adj u v → u ∈ S → v ∈ S) :
    ∀ {u v : V}, G.Walk u v → u ∈ S → v ∈ S
  | _, _, Walk.nil, hu => hu
  | _, _, Walk.cons h p, hu => Walk.mem_of_adj_closed hS p (hS h hu)

/-- If `S` is closed under adjacency, no vertex of `S` is reachable from outside `S`. -/
lemma not_reachable_of_adj_closed {S : Set V} (hS : ∀ ⦃u v⦄, G.Adj u v → u ∈ S → v ∈ S)
    {u v : V} (hu : u ∈ S) (hv : v ∉ S) : ¬ G.Reachable u v := by
  rintro ⟨p⟩
  exact hv (p.mem_of_adj_closed hS hu)

/-! ### Cayley trees -/

/-- **Georgii §12.2.** The Cayley tree `𝒞𝒯(d)`: a tree in which every vertex has exactly `d + 1`
neighbours. Georgii's `S = 𝒞𝒯(d)` is the (unique up to isomorphism) such graph; every statement
of §12.2 is a statement about an arbitrary graph with this property. -/
structure IsCayleyTree (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop where
  /-- A Cayley tree is a tree. -/
  isTree : G.IsTree
  /-- Every vertex of `𝒞𝒯(d)` has `d + 1` neighbours. -/
  isRegularOfDegree : G.IsRegularOfDegree (d + 1)

namespace IsCayleyTree

variable [G.LocallyFinite] {d : ℕ} (hG : G.IsCayleyTree d)
include hG

lemma isAcyclic : G.IsAcyclic := hG.isTree.isAcyclic

lemma connected : G.Connected := hG.isTree.connected

lemma nonempty : Nonempty V := hG.connected.nonempty

/-- A Cayley tree is bipartite (Mathlib's `SimpleGraph.IsTree.isBipartite`); this is Georgii's
decomposition `S = S₀ ∪ S₁` used for alternating boundary laws. -/
lemma isBipartite : G.IsBipartite := hG.isTree.isBipartite

lemma card_neighborFinset (i : V) : (G.neighborFinset i).card = d + 1 := by
  rw [G.card_neighborFinset_eq_degree, hG.isRegularOfDegree i]

/-- Along an oriented bond `ij` of `𝒞𝒯(d)` there are exactly `d` other neighbours of `i`: this is
the `d` in Georgii's equations (12.16), (12.21), (12.22). -/
lemma card_neighborFinset_erase [DecidableEq V] {i j : V} (hij : G.Adj i j) :
    ((G.neighborFinset i).erase j).card = d := by
  rw [Finset.card_erase_of_mem ((G.mem_neighborFinset i j).2 hij), hG.card_neighborFinset,
    Nat.add_sub_cancel]

/-- Every vertex of a Cayley tree has a neighbour. -/
lemma exists_adj_right (i : V) : ∃ j : V, G.Adj i j := by
  have hcard : (G.neighborFinset i).card = d + 1 := hG.card_neighborFinset i
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (by rw [hcard]; exact Nat.succ_pos d)
  exact ⟨j, (G.mem_neighborFinset i j).1 hj⟩

/-- A Cayley tree has at least one bond. -/
lemma exists_adj : ∃ i j : V, G.Adj i j := by
  obtain ⟨i⟩ := hG.nonempty
  obtain ⟨j, hj⟩ := hG.exists_adj_right i
  exact ⟨i, j, hj⟩

end IsCayleyTree

/-! ### `ℤ` is the Cayley tree of degree `1` -/

/-- `SimpleGraph.hasse ℤ` is acyclic: deleting the bond `{i, i+1}` separates `{k ≤ i}` from
`{k ≥ i + 1}`. -/
theorem isAcyclic_hasse_int : (hasse ℤ).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  have key : ∀ i : ℤ, (hasse ℤ).IsBridge s(i, i + 1) := by
    intro i
    rw [isBridge_iff]
    refine not_reachable_of_adj_closed (S := {k : ℤ | k ≤ i}) ?_ (Set.mem_ofPred.2 le_rfl)
      (by simp)
    rintro u v huv hu
    rw [deleteEdges_adj] at huv
    obtain ⟨hadj, hne⟩ := huv
    rcases (hasse_int_adj u v).1 hadj with h | h
    · by_cases hui : u = i
      · exact absurd (by rw [Set.mem_singleton_iff, hui, ← h, hui]) hne
      · have : u < i := lt_of_le_of_ne hu hui
        simp only [Set.mem_ofPred_eq] at hu ⊢
        omega
    · simp only [Set.mem_ofPred_eq] at hu ⊢
      omega
  intro u v huv
  rcases (hasse_int_adj u v).1 huv with h | h
  · rw [← h]; exact key u
  · rw [Sym2.eq_swap, ← h]; exact key v

theorem isTree_hasse_int : (hasse ℤ).IsTree where
  connected := by
    have : Nonempty ℤ := ⟨0⟩
    exact ⟨hasse_preconnected_of_succ ℤ⟩
  isAcyclic := isAcyclic_hasse_int

theorem isRegularOfDegree_hasse_int : (hasse ℤ).IsRegularOfDegree 2 := by
  intro i
  rw [← card_neighborFinset_eq_degree, neighborFinset_hasse_int]
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]

/-- **`ℤ` is Georgii's `𝒞𝒯(1)`**: the Cayley tree of degree `1`. -/
theorem isCayleyTree_hasse_int : (hasse ℤ).IsCayleyTree 1 where
  isTree := isTree_hasse_int
  isRegularOfDegree := isRegularOfDegree_hasse_int

end SimpleGraph

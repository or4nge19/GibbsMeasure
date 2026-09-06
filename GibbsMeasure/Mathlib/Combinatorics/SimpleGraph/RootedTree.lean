/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Rooting a tree: the parent of a vertex

Fix a tree `G` and a root `r`. Every vertex `i ≠ r` has exactly one neighbour that is closer to
`r` — its *parent* — and all its other neighbours are farther. Both halves are stated through
`SimpleGraph.past`: `r ∈ G.past j i` says `d(r, i) = d(r, j) + 1`, i.e. that `j` is closer to `r`
than `i` is, and `r ∈ G.past i k` says that `k` is farther.

* `SimpleGraph.IsTree.eq_of_mem_past_of_mem_past` — uniqueness of the parent: two neighbours of
  `i` that are both closer to `r` coincide. (Two geodesics `r → i` through them would be two
  distinct paths in a tree.)
* `SimpleGraph.IsTree.exists_adj_mem_past` — existence of the parent for `i ≠ r`.
* `SimpleGraph.IsTree.mem_past_of_ne` — every neighbour other than the parent is farther.
* `SimpleGraph.notMem_past_self_root` — no neighbour of the root is closer to it.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Uniqueness of the parent.** In a tree, two neighbours of `i` which are both closer to `r`
than `i` is are equal: concatenating a geodesic `r → j` (resp. `r → k`) with the edge to `i`
produces a path `r → i`, and a tree has at most one such path. -/
theorem IsTree.eq_of_mem_past_of_mem_past (hG : G.IsTree) {r i j k : V}
    (hij : G.Adj i j) (hik : G.Adj i k) (hj : r ∈ G.past j i) (hk : r ∈ G.past k i) : j = k := by
  obtain ⟨p, hp, hplen⟩ := hG.connected.exists_path_of_dist r j
  obtain ⟨q, hq, hqlen⟩ := hG.connected.exists_path_of_dist r k
  have hpath₁ : (p.concat hij.symm).IsPath :=
    (p.concat hij.symm).isPath_of_length_eq_dist (by
      rw [Walk.length_concat, hplen, ← mem_past.1 hj])
  have hpath₂ : (q.concat hik.symm).IsPath :=
    (q.concat hik.symm).isPath_of_length_eq_dist (by
      rw [Walk.length_concat, hqlen, ← mem_past.1 hk])
  have heq : p.concat hij.symm = q.concat hik.symm :=
    congrArg Subtype.val ((hG.isAcyclic.subsingleton_path r i).elim
      ⟨p.concat hij.symm, hpath₁⟩ ⟨q.concat hik.symm, hpath₂⟩)
  exact (Walk.concat_inj heq).1

/-- **Existence of the parent.** In a tree, every vertex other than the root has a neighbour
closer to the root: the first step of a geodesic from `i` to `r`. -/
theorem IsTree.exists_adj_mem_past (hG : G.IsTree) {r i : V} (hri : r ≠ i) :
    ∃ j, G.Adj i j ∧ r ∈ G.past j i := by
  obtain ⟨p, hp, hplen⟩ := hG.connected.exists_path_of_dist i r
  cases p with
  | nil => exact absurd rfl hri
  | @cons _ m _ hadj q =>
    refine ⟨m, hadj, ?_⟩
    rw [Walk.length_cons] at hplen
    have h1 : G.dist m r ≤ q.length := dist_le q
    have h2 : G.dist i r ≤ 1 + G.dist m r := by
      have := hG.connected.dist_triangle (u := i) (v := m) (w := r)
      rwa [G.dist_eq_one_iff_adj.2 hadj] at this
    rw [mem_past, dist_comm (u := r) (v := i), dist_comm (u := r) (v := m)]
    omega

/-- No neighbour of the root is closer to the root. -/
theorem notMem_past_self_root {r k : V} : r ∉ G.past k r := by
  rw [mem_past, dist_self]
  omega

/-- **Every neighbour other than the parent is farther from the root.** -/
theorem IsTree.mem_past_of_ne (hG : G.IsTree) {r i j k : V} (hij : G.Adj i j) (hik : G.Adj i k)
    (hj : r ∈ G.past j i) (hjk : j ≠ k) : r ∈ G.past i k :=
  (hG.mem_past_or_mem_past_swap hik r).resolve_right fun hcon ↦
    hjk (hG.eq_of_mem_past_of_mem_past hij hik hj hcon)

end SimpleGraph

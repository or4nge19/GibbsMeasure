/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Connectivity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Connected sets and their boundary in an acyclic graph

In an acyclic graph a vertex `k` of the outer boundary of a connected finite set `Λ` has exactly
one neighbour in `Λ` (`SimpleGraph.IsAcyclic.anchor_eq`), the outer boundary of `insert i Λ` is
`(∂Λ \ {i}) ∪ (∂i \ {i_Λ})`, and the bonds meeting `insert i Λ` are those meeting `Λ` together
with the bonds `{i, k}`, `k ∈ ∂i \ {i_Λ}`.

`SimpleGraph.past G i j` is the set of vertices on the `i`-side of an oriented bond `ij`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ### Boundary vertices of a connected set in a tree -/

section Tree

variable {G} [DecidableEq V] [G.LocallyFinite]

/-- In an acyclic graph, two distinct vertices of the outer boundary of a connected set are not
adjacent. -/
lemma IsAcyclic.not_adj_of_mem_outerBoundary (hG : G.IsAcyclic) {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) {k k' : V} (hk : k ∈ G.outerBoundary Λ)
    (hk' : k' ∈ G.outerBoundary Λ) (hkk' : k ≠ k') : ¬ G.Adj k k' := by
  intro hadj
  obtain ⟨hkΛ, m, hm, hkm⟩ := (G.mem_outerBoundary).1 hk
  obtain ⟨hk'Λ, m', hm', hk'm'⟩ := (G.mem_outerBoundary).1 hk'
  obtain ⟨q₀, hq₀⟩ := hΛ.exists_walk_of_induce (Finset.mem_coe.2 hm) (Finset.mem_coe.2 hm')
  have hq₀' : ∀ x ∈ q₀.bypass.support, x ∈ Λ := fun x hx ↦
    hq₀ x (q₀.support_bypass_subset_support hx)
  have hp : (hkm.symm.toWalk).IsPath := Walk.IsPath.of_adj _
  have hq : (q₀.bypass.concat hk'm'.symm).IsPath :=
    q₀.bypass_isPath.concat (fun h ↦ hk'Λ (hq₀' k' h)) hk'm'.symm
  have hkq : k ∉ (q₀.bypass.concat hk'm'.symm).support := by
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton]
    rintro (h | h)
    · exact hkΛ (hq₀' k h)
    · exact hkk' h
  have := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hadj hkq
  simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
    List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · exact hk'Λ hm
  · exact hkk' rfl

/-- In an acyclic graph, a vertex of the outer boundary of a connected set `Λ` has exactly one
neighbour in `Λ`: Georgii's `k_Λ`. -/
lemma IsAcyclic.eq_of_adj_of_mem_outerBoundary (hG : G.IsAcyclic) {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) {k j j' : V} (hk : k ∈ G.outerBoundary Λ)
    (hj : j ∈ Λ) (hj' : j' ∈ Λ) (hkj : G.Adj k j) (hkj' : G.Adj k j') : j = j' := by
  have hkΛ := G.notMem_of_mem_outerBoundary hk
  obtain ⟨q₀, hq₀⟩ := hΛ.exists_walk_of_induce (Finset.mem_coe.2 hj) (Finset.mem_coe.2 hj')
  have hq₀' : ∀ x ∈ q₀.bypass.support, x ∈ Λ := fun x hx ↦
    hq₀ x (q₀.support_bypass_subset_support hx)
  have hp : (Walk.cons hkj q₀.bypass).IsPath :=
    q₀.bypass_isPath.cons fun h ↦ hkΛ (hq₀' k h)
  have := hG.eq_snd_of_adj_start hp hkj' (Walk.end_mem_support _)
  simpa using this.symm

/-- In a tree, `k_Λ` is the unique neighbour of `k ∈ ∂Λ` in the connected set `Λ`. -/
lemma IsAcyclic.anchor_eq (hG : G.IsAcyclic) {Λ : Finset V} (hΛ : (G.induce (Λ : Set V)).Connected)
    {k j : V} (hk : k ∈ G.outerBoundary Λ) (hj : j ∈ Λ) (hkj : G.Adj k j) : G.anchor Λ k = j :=
  hG.eq_of_adj_of_mem_outerBoundary hΛ hk (G.anchor_mem hk) hj (G.adj_anchor hk) hkj

/-- In a tree, for `i ∈ ∂Λ` with `Λ` connected and `j = i_Λ`, the neighbours of `i` other than `j`
lie outside `Λ ∪ ∂Λ`. -/
lemma IsAcyclic.notMem_union_outerBoundary_of_adj (hG : G.IsAcyclic) {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) {i k : V} (hi : i ∈ G.outerBoundary Λ)
    (hik : G.Adj i k) (hk : k ≠ G.anchor Λ i) : k ∉ Λ ∪ G.outerBoundary Λ := by
  rw [Finset.mem_union, not_or]
  exact ⟨fun hkΛ ↦ hk (hG.anchor_eq hΛ hi hkΛ hik).symm,
    fun hk' ↦ hG.not_adj_of_mem_outerBoundary hΛ hi hk' hik.ne hik⟩

end Tree

/-! ### Growing a connected set by one boundary vertex

For a tree, `Λ` connected, `i ∈ ∂Λ` and `j = i_Λ`, the set `Δ = Λ ∪ {i}` is connected, its
boundary is `(∂Λ \ {i}) ∪ (∂i \ {j})` (a disjoint union), `Δ ∪ ∂Δ = (Λ ∪ ∂Λ) ⊔ (∂i \ {j})`, and
the bonds meeting `Δ` are those meeting `Λ` together with the bonds `{i, k}`, `k ∈ ∂i \ {j}`.
These are the combinatorial inputs of Georgii's consistency computation (12.14). -/

section Grow

variable {G} [DecidableEq V] [G.LocallyFinite] (hG : G.IsAcyclic) {Λ : Finset V}
  (hΛ : (G.induce (Λ : Set V)).Connected) {i : V} (hi : i ∈ G.outerBoundary Λ)
include hG hΛ hi

/-- The new boundary vertices `∂i \ {i_Λ}` lie outside `Λ ∪ ∂Λ`. -/
lemma IsAcyclic.disjoint_union_outerBoundary_erase :
    Disjoint (Λ ∪ G.outerBoundary Λ) ((G.neighborFinset i).erase (G.anchor Λ i)) := by
  rw [Finset.disjoint_right]
  intro k hk
  rw [Finset.mem_erase, mem_neighborFinset] at hk
  exact hG.notMem_union_outerBoundary_of_adj hΛ hi hk.2 hk.1

/-- The boundary of `Λ ∪ {i}` in a tree. -/
lemma IsAcyclic.outerBoundary_insert_eq :
    G.outerBoundary (insert i Λ)
      = (G.outerBoundary Λ).erase i ∪ (G.neighborFinset i).erase (G.anchor Λ i) := by
  rw [outerBoundary_insert]
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, not_or,
    mem_neighborFinset]
  constructor
  · rintro ⟨hik | hk, hki, hkΛ⟩
    · refine Or.inr ⟨fun h ↦ ?_, hik⟩
      exact hkΛ (h ▸ G.anchor_mem hi)
    · exact Or.inl ⟨hki, hk⟩
  · rintro (⟨hki, hk⟩ | ⟨hkj, hik⟩)
    · exact ⟨Or.inr hk, hki, G.notMem_of_mem_outerBoundary hk⟩
    · have := hG.notMem_union_outerBoundary_of_adj hΛ hi hik hkj
      rw [Finset.mem_union, not_or] at this
      exact ⟨Or.inl hik, hik.ne.symm, this.1⟩

lemma IsAcyclic.disjoint_outerBoundary_erase :
    Disjoint ((G.outerBoundary Λ).erase i) ((G.neighborFinset i).erase (G.anchor Λ i)) :=
  Finset.disjoint_of_subset_left (Finset.erase_subset_erase _ Finset.subset_union_right)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
      (hG.disjoint_union_outerBoundary_erase hΛ hi))

/-- `Δ ∪ ∂Δ = (Λ ∪ ∂Λ) ∪ (∂i \ {i_Λ})` for `Δ = Λ ∪ {i}`. -/
lemma IsAcyclic.insert_union_outerBoundary_eq :
    insert i Λ ∪ G.outerBoundary (insert i Λ)
      = (Λ ∪ G.outerBoundary Λ) ∪ (G.neighborFinset i).erase (G.anchor Λ i) := by
  rw [hG.outerBoundary_insert_eq hΛ hi]
  ext k
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ((rfl | hk) | ⟨-, hk⟩ | hk)
    · exact Or.inl (Or.inr hi)
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk
  · rintro ((hk | hk) | hk)
    · exact Or.inl (Or.inr hk)
    · by_cases hki : k = i
      · exact Or.inl (Or.inl hki)
      · exact Or.inr (Or.inl ⟨hki, hk⟩)
    · exact Or.inr (Or.inr hk)

/-- The anchor in `Λ ∪ {i}` of an old boundary vertex `k ≠ i` is its anchor in `Λ`. -/
lemma IsAcyclic.anchor_insert_of_mem_erase {k : V} (hk : k ∈ (G.outerBoundary Λ).erase i) :
    G.anchor (insert i Λ) k = G.anchor Λ k := by
  have hk' : k ∈ G.outerBoundary (insert i Λ) := by
    rw [hG.outerBoundary_insert_eq hΛ hi]
    exact Finset.mem_union_left _ hk
  exact hG.anchor_eq (connected_induce_insert_of_mem_outerBoundary hΛ hi) hk'
    (Finset.mem_insert_of_mem (G.anchor_mem (Finset.mem_of_mem_erase hk)))
    (G.adj_anchor (Finset.mem_of_mem_erase hk))

/-- The anchor in `Λ ∪ {i}` of a new boundary vertex `k ∈ ∂i \ {i_Λ}` is `i`. -/
lemma IsAcyclic.anchor_insert_of_adj {k : V} (hk : k ∈ (G.neighborFinset i).erase (G.anchor Λ i)) :
    G.anchor (insert i Λ) k = i := by
  have hk' : k ∈ G.outerBoundary (insert i Λ) := by
    rw [hG.outerBoundary_insert_eq hΛ hi]
    exact Finset.mem_union_right _ hk
  rw [Finset.mem_erase, mem_neighborFinset] at hk
  exact hG.anchor_eq (connected_induce_insert_of_mem_outerBoundary hΛ hi) hk'
      (Finset.mem_insert_self i Λ) hk.2.symm

omit hG hΛ in
/-- The bonds meeting `Λ ∪ {i}`: those meeting `Λ` and the new bonds `{i, k}`, `k ∈ ∂i \ {i_Λ}`. -/
lemma bondsOf_insert_eq_of_mem_outerBoundary :
    G.bondsOf (insert i Λ)
      = G.bondsOf Λ ∪ ((G.neighborFinset i).erase (G.anchor Λ i)).image fun k ↦ s(i, k) := by
  rw [bondsOf_insert, incidenceFinset_eq_image]
  ext e
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_erase, mem_neighborFinset]
  constructor
  · rintro (⟨k, hk, rfl⟩ | he)
    · by_cases hkj : k = G.anchor Λ i
      · subst hkj
        exact Or.inl (mk_mem_bondsOf.2 ⟨hk, Or.inr (G.anchor_mem hi)⟩)
      · exact Or.inr ⟨k, ⟨hkj, hk⟩, rfl⟩
    · exact Or.inl he
  · rintro (he | ⟨k, ⟨-, hk⟩, rfl⟩)
    · exact Or.inr he
    · exact Or.inl ⟨k, hk, rfl⟩

lemma IsAcyclic.disjoint_bondsOf_image :
    Disjoint (G.bondsOf Λ) (((G.neighborFinset i).erase (G.anchor Λ i)).image fun k ↦ s(i, k)) := by
  rw [Finset.disjoint_right]
  rintro e he
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_erase, mem_neighborFinset] at hk
  rw [mk_mem_bondsOf, not_and, not_or]
  intro _
  have := hG.notMem_union_outerBoundary_of_adj hΛ hi hk.2 hk.1
  rw [Finset.mem_union, not_or] at this
  exact ⟨G.notMem_of_mem_outerBoundary hi, this.1⟩

end Grow

/-! ### The two sides of an oriented bond in a tree -/

section Past

variable {G}

/-- Georgii's "past interval" `]-∞, ij[ = {k : d(k, j) = d(k, i) + 1}` of an oriented bond `ij`:
the vertices on the side of `i`. -/
def past (G : SimpleGraph V) (i j : V) : Set V := {k | G.dist k j = G.dist k i + 1}

lemma mem_past {i j k : V} : k ∈ G.past i j ↔ G.dist k j = G.dist k i + 1 := Iff.rfl

/-- In an acyclic graph every path realises the distance. -/
lemma IsAcyclic.length_eq_dist (hG : G.IsAcyclic) {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length = G.dist u v := by
  obtain ⟨q, hq, hq'⟩ := p.reachable.exists_path_of_dist
  have := (hG.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  rw [← hq']
  exact congrArg Walk.length (Subtype.ext_iff.1 this)

lemma mem_past_self_of_adj {i j : V} (hij : G.Adj i j) : i ∈ G.past i j := by
  change G.dist i j = G.dist i i + 1
  rw [dist_self, zero_add, dist_eq_one_iff_adj]
  exact hij

/-- In a tree, for `Λ` connected and `k ∈ ∂Λ`, every vertex of `Λ ∪ ∂Λ` other than `k` lies on
the side of `k_Λ` of the bond `k_Λ k`. -/
lemma IsAcyclic.mem_past_anchor (hG : G.IsAcyclic) [DecidableEq V] [G.LocallyFinite]
    {Λ : Finset V} (hΛ : (G.induce (Λ : Set V)).Connected) {k : V} (hk : k ∈ G.outerBoundary Λ)
    {x : V} (hx : x ∈ Λ ∪ G.outerBoundary Λ) (hxk : x ≠ k) : x ∈ G.past (G.anchor Λ k) k := by
  have hik : G.Adj (G.anchor Λ k) k := (G.adj_anchor hk).symm
  have hkΛ := G.notMem_of_mem_outerBoundary hk
  obtain ⟨p, hp, hpk⟩ : ∃ p : G.Walk x (G.anchor Λ k), p.IsPath ∧ k ∉ p.support := by
    rcases Finset.mem_union.1 hx with hxΛ | hxΛ
    · obtain ⟨q, hq⟩ := hΛ.exists_walk_of_induce (Finset.mem_coe.2 hxΛ)
        (Finset.mem_coe.2 (G.anchor_mem hk))
      exact ⟨q.bypass, q.bypass_isPath, fun h ↦ hkΛ (hq k (q.support_bypass_subset_support h))⟩
    · obtain ⟨q, hq⟩ := hΛ.exists_walk_of_induce (Finset.mem_coe.2 (G.anchor_mem hxΛ))
        (Finset.mem_coe.2 (G.anchor_mem hk))
      have hxΛ' := G.notMem_of_mem_outerBoundary hxΛ
      refine ⟨Walk.cons (G.adj_anchor hxΛ) q.bypass,
        q.bypass_isPath.cons fun h ↦ hxΛ' (hq x (q.support_bypass_subset_support h)), ?_⟩
      rw [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨hxk.symm, fun h ↦ hkΛ (hq k (q.support_bypass_subset_support h))⟩
  have hpath : (p.concat hik).IsPath := hp.concat hpk hik
  change G.dist x k = G.dist x (G.anchor Λ k) + 1
  rw [← hG.length_eq_dist hpath, ← hG.length_eq_dist hp, Walk.length_concat]

/-- On a tree, a path from `i` to a vertex on the side of `i` of the bond `ij` avoids `j`. -/
lemma IsAcyclic.notMem_support_of_mem_past (hG : G.IsAcyclic) {i j k : V} (hij : G.Adj i j)
    {p : G.Walk i k} (hp : p.IsPath) (hk : k ∈ G.past i j) : j ∉ p.support := by
  classical
  intro hj
  have hlen : p.length = G.dist i k := hG.length_eq_dist hp
  have h1 : (p.takeUntil j hj).length + (p.dropUntil j hj).length = p.length := by
    conv_rhs => rw [← p.take_spec hj]
    rw [Walk.length_append]
  have h2 : 0 < (p.takeUntil j hj).length := by
    rw [Nat.pos_iff_ne_zero]
    exact fun h0 ↦ hij.ne (Walk.eq_of_length_eq_zero h0)
  have h3 : G.dist j k ≤ (p.dropUntil j hj).length := dist_le _
  have hk' : G.dist j k = G.dist i k + 1 := by
    have := hk
    rw [mem_past] at this
    rwa [dist_comm, show G.dist k i = G.dist i k from dist_comm] at this
  omega

/-- On a tree, the endpoint of a path from `i` avoiding `j` lies on the side of `i` of `ij`. -/
lemma IsAcyclic.mem_past_of_notMem_support (hG : G.IsAcyclic) {i j k : V} (hij : G.Adj i j)
    {p : G.Walk i k} (hp : p.IsPath) (hj : j ∉ p.support) : k ∈ G.past i j := by
  rw [mem_past]
  rcases hG.dist_eq_dist_add_one_of_adj_of_reachable k hij p.reachable.symm with h | h
  · exfalso
    obtain ⟨q, -, hqlen⟩ := (p.reachable.symm.trans hij.reachable).exists_path_of_dist
    have hq' : (q.concat hij.symm).IsPath :=
      (q.concat hij.symm).isPath_of_length_eq_dist (by rw [Walk.length_concat, hqlen, h])
    have heq : p.reverse = q.concat hij.symm := congrArg Subtype.val
      ((hG.subsingleton_path k i).elim ⟨p.reverse, hp.reverse⟩ ⟨q.concat hij.symm, hq'⟩)
    have hj' : j ∈ (q.concat hij.symm).support :=
      q.support_subset_support_concat _ q.end_mem_support
    rw [← heq, Walk.support_reverse, List.mem_reverse] at hj'
    exact hj hj'
  · exact h

/-- On a tree, every vertex of a path from `i` to a vertex on the side of `i` of `ij` lies on that
side. -/
lemma IsAcyclic.mem_past_of_mem_support (hG : G.IsAcyclic) {i j k : V} (hij : G.Adj i j)
    {p : G.Walk i k} (hp : p.IsPath) (hk : k ∈ G.past i j) {v : V} (hv : v ∈ p.support) :
    v ∈ G.past i j := by
  classical
  exact hG.mem_past_of_notMem_support hij (hp.takeUntil hv) fun h ↦
    hG.notMem_support_of_mem_past hij hp hk (p.support_takeUntil_subset_support hv h)

lemma notMem_past_self (i j : V) : j ∉ G.past i j := by
  rw [mem_past, dist_self]
  omega

/-- On a tree, for `Λ` connected with `i ∈ Λ` on the side of `i` of `ij`, every vertex of
`Λ ∪ ∂Λ` other than `j` lies on that side. -/
lemma IsAcyclic.mem_past_of_mem_union_outerBoundary (hG : G.IsAcyclic) [DecidableEq V]
    [G.LocallyFinite] {i j : V} (hij : G.Adj i j) {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) (hiΛ : i ∈ Λ) (hΛp : ∀ x ∈ Λ, x ∈ G.past i j)
    {k : V} (hk : k ∈ Λ ∪ G.outerBoundary Λ) (hkj : k ≠ j) : k ∈ G.past i j := by
  rcases Finset.mem_union.1 hk with hkΛ | hkΛ
  · exact hΛp k hkΛ
  · obtain ⟨q, hq⟩ := hΛ.exists_walk_of_induce (Finset.mem_coe.2 hiΛ)
      (Finset.mem_coe.2 (G.anchor_mem hkΛ))
    have hkΛ' := G.notMem_of_mem_outerBoundary hkΛ
    have hjΛ : j ∉ Λ := fun hjΛ ↦ notMem_past_self i j (hΛp j hjΛ)
    have hp : (q.bypass.concat (G.adj_anchor hkΛ).symm).IsPath :=
      q.bypass_isPath.concat (fun h ↦ hkΛ' (hq k (q.support_bypass_subset_support h))) _
    refine hG.mem_past_of_notMem_support hij hp fun hjmem ↦ ?_
    simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hjmem
    rcases hjmem with h | h
    · exact hjΛ (hq j (q.support_bypass_subset_support h))
    · exact hkj h.symm

/-- On a tree, the hull rooted at `i` of a finite set on the side of `i` of `ij` lies on that
side. -/
lemma IsAcyclic.hull_subset_past (hG : G.IsAcyclic) [DecidableEq V] (hconn : G.Connected)
    {i j : V} (hij : G.Adj i j) {W : Finset V} (hW : ∀ k ∈ W, k ∈ G.past i j) :
    ∀ x ∈ hull hconn i W, x ∈ G.past i j := by
  intro x hx
  obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.1 hx
  have hkp : k ∈ G.past i j := by
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact mem_past_self_of_adj hij
    · exact hW k hk
  exact hG.mem_past_of_mem_support hij (Walk.bypass_isPath _) hkp (List.mem_toFinset.1 hx)

end Past

/-! ### Bonds inside a connected set and bonds to its boundary -/

section InnerBonds

variable {G} [DecidableEq V] [G.LocallyFinite]

lemma injOn_mk_anchor (Λ : Finset V) :
    Set.InjOn (fun k ↦ s(G.anchor Λ k, k)) (G.outerBoundary Λ : Set V) := by
  intro k hk k' hk' h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact h
  · exact absurd (h ▸ G.anchor_mem (Finset.mem_coe.1 hk')) (G.notMem_of_mem_outerBoundary
      (Finset.mem_coe.1 hk))

open Classical in
lemma disjoint_filter_bondsOf_image (Λ : Finset V) :
    Disjoint ((G.bondsOf Λ).filter fun b ↦ ∀ v ∈ b, v ∈ Λ)
      ((G.outerBoundary Λ).image fun k ↦ s(G.anchor Λ k, k)) := by
  rw [Finset.disjoint_right]
  intro e he
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter, not_and]
  intro _ h
  exact G.notMem_of_mem_outerBoundary hk (h k (Sym2.mem_mk_right _ _))

open Classical in
/-- In a tree, the bonds meeting a connected set `Λ` are the bonds inside `Λ` together with the
bonds `{k_Λ, k}`, `k ∈ ∂Λ`. -/
lemma IsAcyclic.bondsOf_eq_filter_union_image (hG : G.IsAcyclic) {Λ : Finset V}
    (hΛ : (G.induce (Λ : Set V)).Connected) :
    G.bondsOf Λ = ((G.bondsOf Λ).filter fun b ↦ ∀ v ∈ b, v ∈ Λ)
      ∪ (G.outerBoundary Λ).image fun k ↦ s(G.anchor Λ k, k) := by
  ext e
  constructor
  · intro he
    by_cases hin : ∀ v ∈ e, v ∈ Λ
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, hin⟩)
    · refine Finset.mem_union_right _ ?_
      revert he hin
      refine Sym2.inductionOn e fun u v he hin ↦ ?_
      obtain ⟨hadj, huv⟩ := mk_mem_bondsOf.1 he
      simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, not_and] at hin
      rw [Finset.mem_image]
      rcases huv with hu | hv
      · have hv : v ∉ Λ := hin hu
        have hvΛ : v ∈ G.outerBoundary Λ := (G.mem_outerBoundary).2 ⟨hv, u, hu, hadj.symm⟩
        exact ⟨v, hvΛ, by rw [hG.anchor_eq hΛ hvΛ hu hadj.symm]⟩
      · have hu : u ∉ Λ := fun hu ↦ hin hu hv
        have huΛ : u ∈ G.outerBoundary Λ := (G.mem_outerBoundary).2 ⟨hu, v, hv, hadj⟩
        exact ⟨u, huΛ, by rw [hG.anchor_eq hΛ huΛ hv hadj, Sym2.eq_swap]⟩
  · intro he
    rcases Finset.mem_union.1 he with he | he
    · exact (Finset.mem_filter.1 he).1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he
      exact mk_mem_bondsOf.2 ⟨(G.adj_anchor hk).symm, Or.inl (G.anchor_mem hk)⟩

end InnerBonds

end SimpleGraph

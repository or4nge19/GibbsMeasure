/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.InfiniteCluster
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
# Measurability of connectivity events of a random set of vertices

Let `G` be a graph on a countable vertex type `V` and `S : Ω → Set V` a random set of vertices
such that `{ω | v ∈ S ω}` is measurable for every vertex `v`.  Then

* `SimpleGraph.measurableSet_setOf_reachableIn`: reachability inside `S ω` between two given
  vertices is a measurable event — a countable union, over the finite chains of adjacent vertices
  joining them, of countable intersections;
* `SimpleGraph.measurableSet_setOf_mem_infiniteClusters`: membership of a given vertex in an
  infinite cluster of `S ω` is a measurable event — a countable intersection, over the finite
  subsets of `V`, of countable unions;
* `SimpleGraph.measurableSet_setOf_connected_induce` and
  `SimpleGraph.measurableSet_setOf_forall_finite_supp`: the two halves of `SimpleGraph.IsOceanIn`
  are measurable events.  Connectedness is a countable conjunction of reachability events; the
  finiteness of every component is `SimpleGraph.forall_finite_supp_iff_forall_exists_finset`, the
  statement that the vertices reachable from any given one are contained in some `Finset`, of
  which there are countably many.
* `SimpleGraph.measurableSet_setOf_isOceanIn` and
  `SimpleGraph.measurableSet_setOf_oceanPart_nonempty`: consequently, being an ocean in `R` and
  containing an ocean in `R` are measurable events.
-/

@[expose] public section

open MeasureTheory

namespace SimpleGraph

variable {Ω V : Type*} [MeasurableSpace Ω] [Countable V] (G : SimpleGraph V) {S : Ω → Set V}

/-- Reachability inside a random set of vertices, between two given vertices, is a measurable
event when membership of each vertex is. -/
lemma measurableSet_setOf_reachableIn (hS : ∀ v, MeasurableSet {ω | v ∈ S ω}) (u v : V) :
    MeasurableSet {ω | G.ReachableIn (S ω) u v} := by
  have hrw : {ω | G.ReachableIn (S ω) u v}
      = ⋃ n : ℕ, ⋃ f ∈ {f : Fin (n + 1) → V | f 0 = u ∧ f (Fin.last n) = v ∧
          ∀ k : Fin n, G.Adj (f k.castSucc) (f k.succ)}, ⋂ k, {ω | f k ∈ S ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    rw [reachableIn_iff_exists_chain]
    constructor
    · rintro ⟨n, f, h0, hn, hadj, hs⟩
      exact ⟨n, f, ⟨h0, hn, hadj⟩, hs⟩
    · rintro ⟨n, f, ⟨h0, hn, hadj⟩, hs⟩
      exact ⟨n, f, h0, hn, hadj, hs⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun n ↦ MeasurableSet.biUnion (Set.to_countable _)
    fun f _ ↦ MeasurableSet.iInter fun k ↦ hS (f k)

omit [Countable V] in
/-- A vertex lies in an infinite cluster of `s` exactly when it reaches, inside `s`, a vertex
outside any given finite set. -/
lemma mem_infiniteClusters_iff_forall_finset_exists {s : Set V} {u : V} :
    u ∈ G.infiniteClusters s ↔ ∀ F : Finset V, ∃ v ∉ F, G.ReachableIn s u v := by
  constructor
  · rintro ⟨hu, hinf⟩ F
    have himg := image_val_supp_connectedComponentMk_eq (G := G) hu
    have : {v | G.ReachableIn s u v}.Infinite := by
      rw [← himg]
      exact hinf.image Subtype.val_injective.injOn
    obtain ⟨v, hv, hvF⟩ := this.exists_notMem_finite F.finite_toSet
    exact ⟨v, hvF, hv⟩
  · intro h
    obtain ⟨v₀, -, hv₀⟩ := h ∅
    have hu : u ∈ s := hv₀.mem_left
    refine ⟨hu, ?_⟩
    rw [← Set.infinite_image_iff Subtype.val_injective.injOn,
      image_val_supp_connectedComponentMk_eq hu]
    intro hfin
    obtain ⟨v, hvF, hv⟩ := h hfin.toFinset
    exact hvF (hfin.mem_toFinset.2 hv)

/-- Membership of a given vertex in an infinite cluster of a random set of vertices is a
measurable event when membership of each vertex is. -/
lemma measurableSet_setOf_mem_infiniteClusters (hS : ∀ v, MeasurableSet {ω | v ∈ S ω}) (u : V) :
    MeasurableSet {ω | u ∈ G.infiniteClusters (S ω)} := by
  have hrw : {ω | u ∈ G.infiniteClusters (S ω)}
      = ⋂ F : Finset V, ⋃ v ∈ {v | v ∉ F}, {ω | G.ReachableIn (S ω) u v} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact mem_infiniteClusters_iff_forall_finset_exists G
  rw [hrw]
  exact MeasurableSet.iInter fun F ↦ MeasurableSet.biUnion (Set.to_countable _)
    fun v _ ↦ G.measurableSet_setOf_reachableIn hS u v

/-! ### Oceans of a random set of vertices

Georgii's event `{ξ⁰_P(G, ·) ≠ ∅}` is measurable because Definition (18.6) — connected, with
finite islands — is a *countable* condition on a countable vertex type: connectedness is a
countable conjunction of reachability events, and the finiteness of an island is witnessed by a
`Finset`, of which there are countably many. -/

omit [Countable V] in
/-- **Every component of `t` is finite** exactly when the set of vertices reachable inside `t`
from any given vertex of `t` is contained in some `Finset`.  This is the form of the island
condition of `SimpleGraph.IsOceanIn` that is visibly countable. -/
lemma forall_finite_supp_iff_forall_exists_finset {t : Set V} :
    (∀ c : (G.induce t).ConnectedComponent, c.supp.Finite) ↔
      ∀ u ∈ t, ∃ F : Finset V, ∀ v, G.ReachableIn t u v → v ∈ F := by
  classical
  constructor
  · intro h u hu
    have hfin : {v | G.ReachableIn t u v}.Finite := by
      rw [← image_val_supp_connectedComponentMk_eq hu]
      exact (h _).image _
    exact ⟨hfin.toFinset, fun v hv ↦ hfin.mem_toFinset.2 hv⟩
  · intro h c
    obtain ⟨⟨u, hu⟩, hmem⟩ := c.nonempty_supp
    rw [ConnectedComponent.mem_supp_iff] at hmem
    obtain ⟨F, hF⟩ := h u hu
    subst hmem
    refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
    rw [image_val_supp_connectedComponentMk_eq hu]
    exact F.finite_toSet.subset fun v hv ↦ hF v hv

/-- Finiteness of every island of a random set of vertices is a measurable event. -/
lemma measurableSet_setOf_forall_finite_supp {t : Ω → Set V}
    (ht : ∀ v, MeasurableSet {ω | v ∈ t ω}) :
    MeasurableSet {ω | ∀ c : (G.induce (t ω)).ConnectedComponent, c.supp.Finite} := by
  classical
  have hrw : {ω | ∀ c : (G.induce (t ω)).ConnectedComponent, c.supp.Finite}
      = ⋂ u : V, ({ω | u ∈ t ω}ᶜ ∪
          ⋃ F : Finset V, ⋂ v ∈ {v : V | v ∉ F}, {ω | G.ReachableIn (t ω) u v}ᶜ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_iUnion]
    rw [forall_finite_supp_iff_forall_exists_finset]
    constructor
    · intro h u
      by_cases hu : u ∈ t ω
      · obtain ⟨F, hF⟩ := h u hu
        exact Or.inr ⟨F, fun v hv hr ↦ hv (hF v hr)⟩
      · exact Or.inl hu
    · intro h u hu
      rcases h u with hne | ⟨F, hF⟩
      · exact absurd hu hne
      · exact ⟨F, fun v hr ↦ by by_contra hv; exact hF v hv hr⟩
  rw [hrw]
  refine MeasurableSet.iInter fun u ↦ (ht u).compl.union ?_
  exact MeasurableSet.iUnion fun F ↦ MeasurableSet.biInter (Set.to_countable _)
    fun v _ ↦ (G.measurableSet_setOf_reachableIn ht u v).compl

/-- Connectedness of the subgraph induced on a random set of vertices is a measurable event. -/
lemma measurableSet_setOf_connected_induce (hS : ∀ v, MeasurableSet {ω | v ∈ S ω}) :
    MeasurableSet {ω | (G.induce (S ω)).Connected} := by
  have hrw : {ω | (G.induce (S ω)).Connected}
      = (⋃ v : V, {ω | v ∈ S ω}) ∩
        ⋂ u : V, ⋂ v : V, ({ω | u ∈ S ω}ᶜ ∪ {ω | v ∈ S ω}ᶜ ∪ {ω | G.ReachableIn (S ω) u v}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    rw [connected_induce_iff_forall_reachableIn]
    constructor
    · rintro ⟨⟨v, hv⟩, h⟩
      refine ⟨⟨v, hv⟩, fun u v ↦ ?_⟩
      by_cases hu : u ∈ S ω
      · by_cases hv' : v ∈ S ω
        · exact Or.inr (h u hu v hv')
        · exact Or.inl (Or.inr hv')
      · exact Or.inl (Or.inl hu)
    · rintro ⟨⟨v, hv⟩, h⟩
      refine ⟨⟨v, hv⟩, fun u hu v hv' ↦ ?_⟩
      rcases h u v with (hne | hne) | hr
      · exact absurd hu hne
      · exact absurd hv' hne
      · exact hr
  rw [hrw]
  refine (MeasurableSet.iUnion fun v ↦ hS v).inter (MeasurableSet.iInter fun u ↦ ?_)
  exact MeasurableSet.iInter fun v ↦
    (((hS u).compl.union (hS v).compl).union (G.measurableSet_setOf_reachableIn hS u v))

/-- **Being an ocean in `R` is a measurable event** for a random set of vertices: Georgii's
Definition (18.6) is a countable condition. -/
lemma measurableSet_setOf_isOceanIn {H : SimpleGraph V} (R : Set V)
    (hS : ∀ v, MeasurableSet {ω | v ∈ S ω}) :
    MeasurableSet {ω | IsOceanIn G H R (S ω)} := by
  classical
  have hdiff : ∀ v : V, MeasurableSet {ω | v ∈ R \ S ω} := by
    intro v
    by_cases hv : v ∈ R
    · have hset : {ω | v ∈ R \ S ω} = {ω | v ∈ S ω}ᶜ := by ext ω; simp [hv]
      rw [hset]
      exact (hS v).compl
    · have hset : {ω | v ∈ R \ S ω} = (∅ : Set Ω) := by ext ω; simp [hv]
      rw [hset]
      exact MeasurableSet.empty
  have hrw : {ω | IsOceanIn G H R (S ω)}
      = (⋂ v : V, ({ω | v ∈ S ω}ᶜ ∪ {ω | v ∈ R})) ∩
        ({ω | (G.induce (S ω)).Connected} ∩
          {ω | ∀ c : (H.induce (R \ S ω)).ConnectedComponent, c.supp.Finite}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff]
    constructor
    · rintro ⟨hsub, hconn, hisl⟩
      refine ⟨fun v ↦ ?_, hconn, hisl⟩
      by_cases hv : v ∈ S ω
      · exact Or.inr (hsub hv)
      · exact Or.inl hv
    · rintro ⟨hsub, hconn, hisl⟩
      exact ⟨fun v hv ↦ (hsub v).resolve_left (not_not.2 hv), hconn, hisl⟩
  rw [hrw]
  refine (MeasurableSet.iInter fun v ↦ ?_).inter
    ((G.measurableSet_setOf_connected_induce hS).inter
      (measurableSet_setOf_forall_finite_supp (G := H) hdiff))
  by_cases hv : v ∈ R
  · simp [hv]
  · simpa [hv] using (hS v).compl

/-- **Georgii's event `{ξ⁰_R(G, ·) ≠ ∅}` is measurable**: the ocean part of a random set of
vertices is nonempty exactly when the union of its infinite clusters is an ocean. -/
lemma measurableSet_setOf_oceanPart_nonempty {H : SimpleGraph V} (R : Set V)
    (hS : ∀ v, MeasurableSet {ω | v ∈ S ω}) :
    MeasurableSet {ω | (oceanPart G H R (S ω)).Nonempty} := by
  have hrw : {ω | (oceanPart G H R (S ω)).Nonempty}
      = {ω | IsOceanIn G H R (G.infiniteClusters (S ω))} := by
    ext ω
    exact oceanPart_nonempty_iff_isOceanIn_infiniteClusters
  rw [hrw]
  exact G.measurableSet_setOf_isOceanIn R fun v ↦ G.measurableSet_setOf_mem_infiniteClusters hS v

end SimpleGraph

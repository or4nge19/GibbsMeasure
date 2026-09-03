/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Bonds and the outer boundary of a finite set of vertices

For a locally finite graph `G` and a finite set of vertices `Λ`:

* `SimpleGraph.bondsOf G Λ`: the edges of `G` meeting `Λ`.
* `SimpleGraph.outerBoundary G Λ`: the vertices outside `Λ` adjacent to `Λ`.
* `SimpleGraph.anchor G Λ k`: a neighbour of `k` inside `Λ`, chosen arbitrarily. It is unique when
  `Λ` is connected and `G` is acyclic (`SimpleGraph.IsAcyclic.anchor_eq`).
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section Bonds

variable [DecidableEq V] [G.LocallyFinite]

/-- The bonds (edges) of `G` meeting a finite set of vertices `Λ`: Georgii's `{b : b ∩ Λ ≠ ∅}`. -/
def bondsOf (Λ : Finset V) : Finset (Sym2 V) := Λ.biUnion fun i ↦ G.incidenceFinset i

variable {G}

lemma mem_bondsOf {Λ : Finset V} {e : Sym2 V} :
    e ∈ G.bondsOf Λ ↔ e ∈ G.edgeSet ∧ ∃ i ∈ Λ, i ∈ e := by
  simp only [bondsOf, Finset.mem_biUnion, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, he, hie⟩
    exact ⟨he, i, hi, hie⟩
  · rintro ⟨he, i, hi, hie⟩
    exact ⟨i, hi, he, hie⟩

lemma mk_mem_bondsOf {Λ : Finset V} {i j : V} :
    s(i, j) ∈ G.bondsOf Λ ↔ G.Adj i j ∧ (i ∈ Λ ∨ j ∈ Λ) := by
  rw [mem_bondsOf, mem_edgeSet]
  constructor
  · rintro ⟨h, k, hk, hke⟩
    rcases Sym2.mem_iff.1 hke with rfl | rfl
    · exact ⟨h, Or.inl hk⟩
    · exact ⟨h, Or.inr hk⟩
  · rintro ⟨h, hi | hj⟩
    · exact ⟨h, i, hi, Sym2.mem_mk_left i j⟩
    · exact ⟨h, j, hj, Sym2.mem_mk_right i j⟩

lemma bondsOf_mono {Λ₁ Λ₂ : Finset V} (h : Λ₁ ⊆ Λ₂) : G.bondsOf Λ₁ ⊆ G.bondsOf Λ₂ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

lemma bondsOf_insert (i : V) (Λ : Finset V) :
    G.bondsOf (insert i Λ) = G.incidenceFinset i ∪ G.bondsOf Λ :=
  Finset.biUnion_insert

lemma bondsOf_union (Λ₁ Λ₂ : Finset V) :
    G.bondsOf (Λ₁ ∪ Λ₂) = G.bondsOf Λ₁ ∪ G.bondsOf Λ₂ :=
  Finset.union_biUnion

lemma bondsOf_singleton (i : V) : G.bondsOf {i} = G.incidenceFinset i :=
  Finset.singleton_biUnion

/-- The edges at `i` are the edges `{i, k}`, `k` a neighbour of `i`. -/
lemma incidenceFinset_eq_image (i : V) :
    G.incidenceFinset i = (G.neighborFinset i).image fun k ↦ s(i, k) := by
  ext e
  simp only [mem_incidenceFinset, Finset.mem_image, mem_neighborFinset]
  constructor
  · intro he
    obtain ⟨k, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    exact ⟨k, G.mk'_mem_incidenceSet_left_iff.1 he, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact G.mk'_mem_incidenceSet_left_iff.2 hk

/-- Georgii's outer boundary `∂Λ = ⋃_{i ∈ Λ} ∂i \ Λ` of a finite set of vertices. -/
def outerBoundary (Λ : Finset V) : Finset V := (Λ.biUnion fun i ↦ G.neighborFinset i) \ Λ

variable (G)

lemma mem_outerBoundary {Λ : Finset V} {k : V} :
    k ∈ G.outerBoundary Λ ↔ k ∉ Λ ∧ ∃ j ∈ Λ, G.Adj k j := by
  simp only [outerBoundary, Finset.mem_sdiff, Finset.mem_biUnion, mem_neighborFinset]
  constructor
  · rintro ⟨⟨j, hj, hkj⟩, hk⟩
    exact ⟨hk, j, hj, hkj.symm⟩
  · rintro ⟨hk, j, hj, hkj⟩
    exact ⟨⟨j, hj, hkj.symm⟩, hk⟩

lemma disjoint_outerBoundary (Λ : Finset V) : Disjoint Λ (G.outerBoundary Λ) :=
  Finset.disjoint_sdiff

lemma notMem_of_mem_outerBoundary {Λ : Finset V} {k : V} (hk : k ∈ G.outerBoundary Λ) : k ∉ Λ :=
  ((G.mem_outerBoundary).1 hk).1

lemma mem_union_outerBoundary_of_adj {Λ : Finset V} {j k : V} (hj : j ∈ Λ) (hjk : G.Adj j k) :
    k ∈ Λ ∪ G.outerBoundary Λ := by
  by_cases hk : k ∈ Λ
  · exact Finset.mem_union_left _ hk
  · exact Finset.mem_union_right _ ((G.mem_outerBoundary).2 ⟨hk, j, hj, hjk.symm⟩)

/-- The outer boundary of `Λ ∪ {i}`, for any graph. -/
lemma outerBoundary_insert (i : V) (Λ : Finset V) :
    G.outerBoundary (insert i Λ) = (G.neighborFinset i ∪ G.outerBoundary Λ) \ insert i Λ := by
  ext k
  simp only [mem_outerBoundary, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_union,
    mem_neighborFinset, not_or]
  constructor
  · rintro ⟨⟨hki, hkΛ⟩, j, rfl | hj, hkj⟩
    · exact ⟨Or.inl hkj.symm, hki, hkΛ⟩
    · exact ⟨Or.inr ⟨hkΛ, j, hj, hkj⟩, hki, hkΛ⟩
  · rintro ⟨hik | ⟨-, j, hj, hkj⟩, hki, hkΛ⟩
    · exact ⟨⟨hki, hkΛ⟩, i, Or.inl rfl, hik.symm⟩
    · exact ⟨⟨hki, hkΛ⟩, j, Or.inr hj, hkj⟩

/-- The neighbours of a vertex of `Λ` lie in `Λ ∪ ∂Λ`. -/
lemma neighborFinset_subset_union_outerBoundary {Λ : Finset V} {i : V} (hi : i ∈ Λ) :
    G.neighborFinset i ⊆ Λ ∪ G.outerBoundary Λ := fun k hk ↦
  G.mem_union_outerBoundary_of_adj hi ((G.mem_neighborFinset i k).1 hk)

end Bonds

lemma injective_mk_left (i : V) : Function.Injective fun k : V ↦ s(i, k) := fun _ _ h ↦
  Sym2.congr_right.1 h

/-! ### The anchor of a boundary vertex -/

section Anchor

variable [DecidableEq V] [G.LocallyFinite]

open Classical in
/-- Georgii's `k_Λ`: the neighbour of a boundary vertex `k ∈ ∂Λ` inside `Λ`, unique when `Λ` is
connected and `G` is a tree (`IsAcyclic.eq_of_adj_of_mem_outerBoundary`); `k` itself otherwise. -/
noncomputable def anchor (Λ : Finset V) (k : V) : V :=
  if h : ∃ j ∈ Λ, G.Adj k j then h.choose else k

lemma anchor_mem_and_adj {Λ : Finset V} {k : V} (hk : k ∈ G.outerBoundary Λ) :
    G.anchor Λ k ∈ Λ ∧ G.Adj k (G.anchor Λ k) := by
  have h := ((G.mem_outerBoundary).1 hk).2
  rw [anchor, dite_eq_left h]
  exact h.choose_spec

lemma anchor_mem {Λ : Finset V} {k : V} (hk : k ∈ G.outerBoundary Λ) : G.anchor Λ k ∈ Λ :=
  (G.anchor_mem_and_adj hk).1

lemma adj_anchor {Λ : Finset V} {k : V} (hk : k ∈ G.outerBoundary Λ) : G.Adj k (G.anchor Λ k) :=
  (G.anchor_mem_and_adj hk).2

variable {G}

lemma outerBoundary_singleton (i : V) : G.outerBoundary {i} = G.neighborFinset i := by
  ext k
  simp only [mem_outerBoundary, Finset.mem_singleton, exists_eq_left, mem_neighborFinset]
  exact ⟨fun h ↦ h.2.symm, fun h ↦ ⟨h.ne.symm, h.symm⟩⟩

lemma anchor_singleton {i k : V} (hk : k ∈ G.outerBoundary {i}) : G.anchor {i} k = i :=
  Finset.mem_singleton.1 (G.anchor_mem hk)

lemma union_outerBoundary_mono {Λ Δ : Finset V} (h : Λ ⊆ Δ) :
    Λ ∪ G.outerBoundary Λ ⊆ Δ ∪ G.outerBoundary Δ := by
  intro k hk
  rcases Finset.mem_union.1 hk with hk | hk
  · exact Finset.mem_union_left _ (h hk)
  · obtain ⟨-, j, hj, hkj⟩ := (G.mem_outerBoundary).1 hk
    exact G.mem_union_outerBoundary_of_adj (h hj) hkj.symm

end Anchor

end SimpleGraph

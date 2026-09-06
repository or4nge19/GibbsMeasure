/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.InfiniteCluster

/-!
# Two oceans meet

* `SimpleGraph.Reachable.induce_apply_eq_of_forall_adj`: a function on the vertices which takes
  equal values on `G`-adjacent points of `s` is constant along reachability inside `s`.
* `SimpleGraph.Connected.subset_image_val_supp_of_disjoint`: a `G`-connected subset of `R`
  disjoint from a set `ξ` lies in a single `H`-component of `R \ ξ` (an island of `ξ`).
* `SimpleGraph.IsOceanIn.nonempty_inter`: **two oceans in `R` have a common point**, when `R`
  minus any finite set percolates in `H ≥ G` (so that oceans are infinite): an ocean disjoint
  from another would lie in one of its islands, which is finite.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {s R ξ η : Set V}

/-- A function taking equal values on adjacent points of `s` is constant along reachability
inside `s`. -/
lemma Reachable.induce_apply_eq_of_forall_adj {β : Sort*} {f : V → β}
    (hf : ∀ ⦃a b⦄, a ∈ s → b ∈ s → G.Adj a b → f a = f b) {u v : s}
    (h : (G.induce s).Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | @cons a b c hadj q ih => exact (hf a.2 b.2 (induce_adj.1 hadj)).trans ih

/-- A `G`-connected subset `η` of `R` disjoint from a set `ξ` lies in a single `H`-component of
`R \ ξ` — a single island of `ξ` — namely the one through any of its points. -/
lemma Connected.subset_image_val_supp_of_disjoint (hGH : G ≤ H)
    (hη : (G.induce η).Connected) (hηR : η ⊆ R) (hdisj : Disjoint η ξ) {x : V} (hx : x ∈ η) :
    η ⊆ Subtype.val ''
      ((H.induce (R \ ξ)).connectedComponentMk
        ⟨x, hηR hx, Set.disjoint_left.1 hdisj hx⟩).supp := by
  have hsub : η ⊆ R \ ξ := fun y hy ↦ ⟨hηR hy, Set.disjoint_left.1 hdisj hy⟩
  intro y hy
  refine ⟨⟨y, hsub hy⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff]
  exact ConnectedComponent.eq.2
    ((hη.preconnected ⟨y, hy⟩ ⟨x, hx⟩).induce_mono hGH hsub)

/-- **Two oceans in `R` meet.**  If `R` minus any finite set percolates in `H ≥ G`, so that
oceans in `R` are infinite, then two oceans in `R` have a common point: an ocean disjoint from
another would be contained in one of its islands, which is finite. -/
theorem IsOceanIn.nonempty_inter (hGH : G ≤ H)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty)
    (hξ : IsOceanIn G H R ξ) (hη : IsOceanIn G H R η) : (ξ ∩ η).Nonempty := by
  by_contra h
  have hdisj : Disjoint η ξ := by
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact Set.disjoint_iff_inter_eq_empty.2 (by rw [Set.inter_comm]; exact h)
  obtain ⟨x, hx⟩ := hη.nonempty
  refine hη.infinite hR (Set.Finite.subset ?_
    (hη.connected.subset_image_val_supp_of_disjoint hGH hη.subset hdisj hx))
  exact (hξ.finite_island _).image _

end SimpleGraph

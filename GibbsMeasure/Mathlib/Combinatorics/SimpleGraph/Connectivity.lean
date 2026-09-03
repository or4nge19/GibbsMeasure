/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Connected induced subgraphs

* `SimpleGraph.connected_induce_iff_forall_exists_walk`: the induced subgraph on `s` is connected
  iff `s` is nonempty and any two of its points are joined by a walk of `G` inside `s`.
* `SimpleGraph.hull`: a connected finite superset of a finite set in a connected graph.
* `SimpleGraph.connected_induction`: induction from a connected set to a connected superset,
  adding one outer-boundary vertex at a time.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ### Walks inside a set: connected induced subgraphs -/

section Connected

variable {G}

/-- A walk whose support lies in `s` is a walk of the induced subgraph on `s`. -/
lemma Walk.toSubgraph_le_induce_top {s : Set V} {u v : V} (p : G.Walk u v)
    (h : ∀ x ∈ p.support, x ∈ s) : p.toSubgraph ≤ (⊤ : G.Subgraph).induce s :=
  p.toSubgraph_le_induce_support.trans (Subgraph.induce_mono_right fun x hx ↦ h x hx)

/-- The induced subgraph on `s` is connected iff `s` is nonempty and any two points of `s` are
joined by a walk of `G` inside `s`. -/
lemma connected_induce_iff_forall_exists_walk {s : Set V} :
    (G.induce s).Connected ↔
      s.Nonempty ∧ ∀ u ∈ s, ∀ v ∈ s, ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ s := by
  rw [connected_induce_iff, Subgraph.connected_iff_forall_exists_walk_subgraph]
  simp only [Subgraph.induce_verts]
  refine and_congr_right fun _ ↦ ⟨fun h u hu v hv ↦ ?_, fun h u v hu hv ↦ ?_⟩
  · obtain ⟨p, hp⟩ := h hu hv
    exact ⟨p, fun x hx ↦ by simpa using (Subgraph.verts_mono hp) (p.mem_verts_toSubgraph.2 hx)⟩
  · obtain ⟨p, hp⟩ := h u hu v hv
    exact ⟨p, p.toSubgraph_le_induce_top hp⟩

lemma Connected.induce_nonempty {s : Set V} (h : (G.induce s).Connected) : s.Nonempty :=
  (connected_induce_iff_forall_exists_walk.1 h).1

lemma Connected.exists_walk_of_induce {s : Set V} (h : (G.induce s).Connected) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) : ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ s :=
  (connected_induce_iff_forall_exists_walk.1 h).2 u hu v hv

/-- The support of a walk is connected. -/
lemma connected_induce_support_finset [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (G.induce ((p.support.toFinset : Finset V) : Set V)).Connected := by
  have h : ((p.support.toFinset : Finset V) : Set V) = {v | v ∈ p.support} := by
    ext x
    simp
  rw [h]
  exact p.connected_induce_support

/-- Adding a boundary vertex to a connected set keeps it connected. -/
lemma connected_induce_insert_of_adj {s : Set V} (hs : (G.induce s).Connected) {i j : V}
    (hj : j ∈ s) (hij : G.Adj i j) : (G.induce (insert i s)).Connected := by
  rw [connected_induce_iff_forall_exists_walk]
  refine ⟨⟨i, Set.mem_insert i s⟩, fun u hu v hv ↦ ?_⟩
  have key : ∀ u ∈ insert i s, ∃ p : G.Walk u j, ∀ x ∈ p.support, x ∈ insert i s := by
    intro u hu
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · exact ⟨hij.toWalk, fun x hx ↦ by
        simp only [Adj.toWalk, Walk.support_cons, Walk.support_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ hj⟩
    · obtain ⟨p, hp⟩ := hs.exists_walk_of_induce hu hj
      exact ⟨p, fun x hx ↦ Set.mem_insert_of_mem _ (hp x hx)⟩
  obtain ⟨p, hp⟩ := key u hu
  obtain ⟨q, hq⟩ := key v hv
  refine ⟨p.append q.reverse, fun x hx ↦ ?_⟩
  rcases (Walk.mem_support_append_iff _ _).1 hx with hx | hx
  · exact hp x hx
  · rw [Walk.support_reverse, List.mem_reverse] at hx
    exact hq x hx

/-- A union of connected sets sharing a common point is connected. -/
lemma connected_induce_biUnion {ι : Type*} (t : Finset ι) (f : ι → Set V) (o : V)
    (ho : ∀ i ∈ t, o ∈ f i) (hf : ∀ i ∈ t, (G.induce (f i)).Connected) (ht : t.Nonempty) :
    (G.induce (⋃ i ∈ t, f i)).Connected := by
  rw [connected_induce_iff_forall_exists_walk]
  obtain ⟨i₀, hi₀⟩ := ht
  refine ⟨⟨o, Set.mem_biUnion hi₀ (ho i₀ hi₀)⟩, fun u hu v hv ↦ ?_⟩
  simp only [Set.mem_iUnion, exists_prop] at hu hv
  obtain ⟨i, hi, hu⟩ := hu
  obtain ⟨j, hj, hv⟩ := hv
  obtain ⟨p, hp⟩ := (hf i hi).exists_walk_of_induce hu (ho i hi)
  obtain ⟨q, hq⟩ := (hf j hj).exists_walk_of_induce (ho j hj) hv
  refine ⟨p.append q, fun x hx ↦ ?_⟩
  rcases (Walk.mem_support_append_iff _ _).1 hx with hx | hx
  · exact Set.mem_biUnion hi (hp x hx)
  · exact Set.mem_biUnion hj (hq x hx)

/-- A walk from outside `Λ` to inside `Λ` passes through the outer boundary of `Λ`. -/
lemma exists_mem_outerBoundary_of_walk [DecidableEq V] [G.LocallyFinite] {Λ : Finset V}
    {y x : V} (p : G.Walk y x) (hy : y ∉ Λ) (hx : x ∈ Λ) :
    ∃ k ∈ p.support, k ∈ G.outerBoundary Λ := by
  induction p with
  | nil => exact absurd hx hy
  | cons h p ih =>
    rename_i u v w
    by_cases hv : v ∈ Λ
    · exact ⟨u, Walk.start_mem_support _, (G.mem_outerBoundary).2 ⟨hy, v, hv, h⟩⟩
    · obtain ⟨k, hk, hkΛ⟩ := ih hv hx
      exact ⟨k, by rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hk, hkΛ⟩

/-- If `Λ ⊊ Δ` with `Λ` nonempty and `Δ` connected, some vertex of `Δ` lies on the boundary of
`Λ`. -/
lemma exists_mem_outerBoundary_of_ssubset [DecidableEq V] [G.LocallyFinite] {Λ Δ : Finset V}
    (hΔ : (G.induce (Δ : Set V)).Connected) (hΛ : Λ.Nonempty) (hΛΔ : Λ ⊆ Δ) (hne : Λ ≠ Δ) :
    ∃ k ∈ Δ, k ∈ G.outerBoundary Λ := by
  obtain ⟨x, hx⟩ := hΛ
  obtain ⟨y, hyΔ, hyΛ⟩ := Finset.exists_of_ssubset (hΛΔ.ssubset_of_ne hne)
  obtain ⟨p, hp⟩ := hΔ.exists_walk_of_induce (Finset.mem_coe.2 hyΔ) (Finset.mem_coe.2 (hΛΔ hx))
  obtain ⟨k, hk, hkΛ⟩ := G.exists_mem_outerBoundary_of_walk p hyΛ hx
  exact ⟨k, Finset.mem_coe.1 (hp k hk), hkΛ⟩

end Connected

/-! ### Adding one outer-boundary vertex -/

section Grow

variable {G} [DecidableEq V] [G.LocallyFinite] {Λ : Finset V}
  (hΛ : (G.induce (Λ : Set V)).Connected) {i : V} (hi : i ∈ G.outerBoundary Λ)
include hΛ hi

/-- Adjoining a vertex of the outer boundary to a connected set keeps it connected. -/
lemma connected_induce_insert_of_mem_outerBoundary :
    (G.induce ((insert i Λ : Finset V) : Set V)).Connected := by
  rw [Finset.coe_insert]
  exact connected_induce_insert_of_adj hΛ (Finset.mem_coe.2 (G.anchor_mem hi)) (G.adj_anchor hi)

end Grow

/-! ### A connected hull of a finite set in a connected graph -/

section Hull

variable {G} [DecidableEq V] (hG : G.Connected) (o : V)

/-- A connected finite set containing `Λ` and a root `o`: the union of the supports of walks from
`o` to the points of `Λ`. -/
noncomputable def hull (Λ : Finset V) : Finset V :=
  (insert o Λ).biUnion fun i ↦ (hG.preconnected o i).some.bypass.support.toFinset

lemma mem_hull_self (Λ : Finset V) : o ∈ hull hG o Λ :=
  Finset.mem_biUnion.2 ⟨o, Finset.mem_insert_self o Λ,
    List.mem_toFinset.2 (Walk.start_mem_support _)⟩

lemma subset_hull (Λ : Finset V) : Λ ⊆ hull hG o Λ := fun i hi ↦
  Finset.mem_biUnion.2 ⟨i, Finset.mem_insert_of_mem hi, List.mem_toFinset.2 (Walk.end_mem_support
      _)⟩

lemma hull_mono {Λ₁ Λ₂ : Finset V} (h : Λ₁ ⊆ Λ₂) : hull hG o Λ₁ ⊆ hull hG o Λ₂ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.insert_subset_insert o h)

lemma connected_induce_hull (Λ : Finset V) : (G.induce ((hull hG o Λ : Finset V) : Set
    V)).Connected := by
  have h : ((hull hG o Λ : Finset V) : Set V)
      = ⋃ i ∈ insert o Λ,
        (((hG.preconnected o i).some.bypass.support.toFinset : Finset V) : Set V) := by
    ext x
    simp [hull]
  rw [h]
  exact connected_induce_biUnion (insert o Λ) _ o (fun i _ ↦ by simp)
    (fun i _ ↦ connected_induce_support_finset _) ⟨o, Finset.mem_insert_self o Λ⟩

end Hull

/-! ### Induction along a connected set -/

section Induction

variable {G} [DecidableEq V] [G.LocallyFinite]

/-- Induction from a connected set `Λ₀` to a connected superset `Δ`, adding one boundary vertex
at a time. -/
theorem connected_induction {P : Finset V → Prop} {Λ₀ Δ : Finset V}
    (hΛ₀ : (G.induce (Λ₀ : Set V)).Connected) (hΔ : (G.induce (Δ : Set V)).Connected)
    (hΛ₀Δ : Λ₀ ⊆ Δ) (base : P Λ₀)
    (step : ∀ Λ : Finset V, (G.induce (Λ : Set V)).Connected → Λ₀ ⊆ Λ → Λ ⊆ Δ →
      ∀ i ∈ Δ, i ∈ G.outerBoundary Λ → P Λ → P (insert i Λ)) : P Δ := by
  suffices h : ∀ n, ∀ Λ : Finset V, (G.induce (Λ : Set V)).Connected → Λ₀ ⊆ Λ → Λ ⊆ Δ →
      (Δ \ Λ).card = n → P Λ → P Δ from h _ Λ₀ hΛ₀ subset_rfl hΛ₀Δ rfl base
  intro n
  induction n with
  | zero =>
    intro Λ _ _ hΛΔ hcard hP
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hcard
    rwa [hΛΔ.antisymm hcard] at hP
  | succ n ih =>
    intro Λ hΛ hΛ₀Λ hΛΔ hcard hP
    have hne : Λ ≠ Δ := fun h ↦ by simp [h] at hcard
    obtain ⟨i, hiΔ, hi⟩ := G.exists_mem_outerBoundary_of_ssubset hΔ
      (hΛ₀.induce_nonempty.mono (Finset.coe_subset.2 hΛ₀Λ) |> fun h ↦ by simpa using h) hΛΔ hne
    have hiΛ := G.notMem_of_mem_outerBoundary hi
    refine ih (insert i Λ) (connected_induce_insert_of_mem_outerBoundary hΛ hi)
      (hΛ₀Λ.trans (Finset.subset_insert i Λ)) (Finset.insert_subset hiΔ hΛΔ) ?_
      (step Λ hΛ hΛ₀Λ hΛΔ i hiΔ hi hP)
    have : Δ \ Λ = insert i (Δ \ insert i Λ) := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨hkΔ, hkΛ⟩
        by_cases hki : k = i
        · exact Or.inl hki
        · exact Or.inr ⟨hkΔ, hki, hkΛ⟩
      · rintro (rfl | ⟨hkΔ, -, hkΛ⟩)
        · exact ⟨hiΔ, hiΛ⟩
        · exact ⟨hkΔ, hkΛ⟩
    rw [this, Finset.card_insert_of_notMem (by simp)] at hcard
    exact Nat.succ_injective hcard


end Induction

end SimpleGraph

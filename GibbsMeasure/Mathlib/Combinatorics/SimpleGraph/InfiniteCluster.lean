/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Connectivity

/-!
# Infinite clusters and oceans

For a graph `G` on `V` and a set of vertices `s`, the *clusters* of `s` are the connected
components of the induced subgraph `G.induce s`.

* `SimpleGraph.infiniteClusters G s`: the union of the supports of the infinite clusters of `s`,
  as a subset of `V`; `s` *percolates* when this set is nonempty.
* `SimpleGraph.IsOceanIn G H R ξ`: `ξ ⊆ R` is `G`-connected and every `H`-component of `R \ ξ`
  (an *island* of `ξ` in `R`) is finite.  The intended reading has `G ≤ H`: `G` is the
  nearest-neighbour graph of a lattice and `H` its `*`-neighbour graph.
* `SimpleGraph.IsOceanIn.existsUnique_infinite_supp`,
  `SimpleGraph.IsOceanIn.isOceanIn_infiniteClusters`: a set `W ⊆ R` containing an infinite ocean
  has a unique infinite cluster, and that cluster is again an ocean.
* `SimpleGraph.oceanPart G H R W`: the union of the infinite clusters of `W` when that union is
  an ocean in `R`, and `∅` otherwise; it is nonempty iff `W` contains an ocean
  (`SimpleGraph.oceanPart_nonempty_iff`) and then it is the largest such ocean
  (`SimpleGraph.IsOceanIn.subset_oceanPart`).
* `SimpleGraph.IsOceanIn.finite_island_infiniteClusters_diff`,
  `SimpleGraph.IsOceanIn.isOceanIn_infiniteClusters_diff`,
  `SimpleGraph.oceanPart_nonempty_congr_of_finite_diff`: removing a finite set from an ocean.
  The islands of the union of the infinite clusters of `ξ \ F` are finite whenever `H` is locally
  finite; that union is again an ocean under the additional planarity hypothesis that a subset
  of `R` with only finite islands has at most one infinite cluster; and then whether a set
  contains an ocean is unchanged by a finite modification — Georgii's `{ξ⁰_P(G, ·) ≠ ∅} ∈ 𝒯`.
* `SimpleGraph.infiniteClusters_image`, `SimpleGraph.IsOceanIn.image`,
  `SimpleGraph.oceanPart_image`: all three are equivariant under an equivalence of the vertex
  type preserving the adjacency of both graphs and the set `R`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {s t R W ξ η : Set V} {u v : V}

/-! ### Reachability inside a set of vertices -/

/-- A walk of `G` whose support lies in `s` is a walk of the induced subgraph on `s`. -/
lemma reachable_induce_of_walk {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    (G.induce s).Reachable ⟨u, hp u p.start_mem_support⟩ ⟨v, hp v p.end_mem_support⟩ := by
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hadj q ih =>
    have hb : b ∈ s := hp b (by simp)
    have hq : ∀ x ∈ q.support, x ∈ s := fun x hx ↦ hp x (by simp [hx])
    exact (Adj.reachable (G := G.induce s) (u := ⟨a, hp a (by simp)⟩) (v := ⟨b, hb⟩) hadj).trans
      (ih hq)

/-- A walk of `G` whose support lies in `s` witnesses `G.ReachableIn s`. -/
lemma ReachableIn.of_walk {u v : V} (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    G.ReachableIn s u v :=
  ⟨hp u p.start_mem_support, hp v p.end_mem_support, reachable_induce_of_walk p hp⟩

/-- Reachability inside `s` is witnessed by a walk of `G` whose support lies in `s`. -/
lemma ReachableIn.exists_walk {u v : V} (h : G.ReachableIn s u v) :
    ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∈ s := by
  obtain ⟨hu, hv, ⟨q⟩⟩ := h
  refine ⟨q.map (Embedding.induce s).toHom, fun x hx ↦ ?_⟩
  have hx' : x ∈ (q.map (Embedding.induce s).toHom).support := hx
  rw [Walk.support_map, List.mem_map] at hx'
  obtain ⟨y, -, rfl⟩ := hx'
  exact y.2

/-- Reachability inside `s` for `G` implies reachability inside `t ⊇ s` for `H ≥ G`. -/
lemma Reachable.induce_mono (hGH : G ≤ H) (hst : s ⊆ t) {u v : s}
    (h : (G.induce s).Reachable u v) :
    (H.induce t).Reachable ⟨u, hst u.2⟩ ⟨v, hst v.2⟩ := by
  exact h.map (induceHom (Hom.ofLE hGH) (fun x hx ↦ hst hx))

/-- Every vertex on a walk of `G.induce s` starting in a component `c` lies in `c`. -/
lemma mem_supp_of_mem_support {c : (G.induce s).ConnectedComponent} {x y : s}
    (hx : x ∈ c.supp) (p : (G.induce s).Walk x y) {z : s} (hz : z ∈ p.support) : z ∈ c.supp := by
  obtain ⟨q, -, -⟩ := (Walk.mem_support_iff_exists_append.1 hz)
  rw [ConnectedComponent.mem_supp_iff] at hx ⊢
  exact (ConnectedComponent.eq.2 ⟨q⟩).symm.trans hx

/-- The (image in `V` of the) support of a component of `G.induce s` is contained in that of
the component of `H.induce t` through the same vertex, for `G ≤ H` and `s ⊆ t`. -/
lemma image_val_supp_connectedComponentMk_subset (hGH : G ≤ H) (hst : s ⊆ t) (x : s) :
    Subtype.val '' ((G.induce s).connectedComponentMk x).supp ⊆
      Subtype.val '' ((H.induce t).connectedComponentMk ⟨x, hst x.2⟩).supp := by
  rintro _ ⟨y, hy, rfl⟩
  rw [ConnectedComponent.mem_supp_iff] at hy
  refine ⟨⟨y, hst y.2⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff]
  exact ConnectedComponent.eq.2 ((ConnectedComponent.eq.1 hy).induce_mono hGH hst)

/-- A map sending adjacent vertices of `s` to equal or adjacent vertices carries reachability
inside `s` to reachability inside `f '' s`. -/
lemma Reachable.induce_image_of_forall_adj {W : Type*} {H : SimpleGraph W} {f : V → W}
    (hf : ∀ ⦃a b⦄, a ∈ s → b ∈ s → G.Adj a b → f a = f b ∨ H.Adj (f a) (f b)) {u v : s}
    (h : (G.induce s).Reachable u v) :
    (H.induce (f '' s)).Reachable ⟨f u, u, u.2, rfl⟩ ⟨f v, v, v.2, rfl⟩ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons a b c hadj q ih =>
    rcases hf a.2 b.2 (induce_adj.1 hadj) with heq | hadj'
    · have : (⟨f a, a, a.2, rfl⟩ : f '' s) = ⟨f b, b, b.2, rfl⟩ := Subtype.ext heq
      rw [this]
      exact ih
    · exact (Adj.reachable (G := H.induce (f '' s)) (u := ⟨f a, a, a.2, rfl⟩)
        (v := ⟨f b, b, b.2, rfl⟩) hadj').trans ih

/-- A map sending adjacent vertices of `s` to equal or adjacent vertices carries a connected
induced subgraph to a connected induced subgraph. -/
lemma Connected.induce_image_of_forall_adj {W : Type*} {H : SimpleGraph W} {f : V → W}
    (hf : ∀ ⦃a b⦄, a ∈ s → b ∈ s → G.Adj a b → f a = f b ∨ H.Adj (f a) (f b))
    (h : (G.induce s).Connected) :
    (H.induce (f '' s)).Connected := by
  obtain ⟨⟨x, hx⟩⟩ := h.nonempty
  have : Nonempty (f '' s) := ⟨⟨f x, x, hx, rfl⟩⟩
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨_, u, hu, rfl⟩ := a
  obtain ⟨_, v, hv, rfl⟩ := b
  exact (h.preconnected ⟨u, hu⟩ ⟨v, hv⟩).induce_image_of_forall_adj hf

/-- The induced subgraph on the support of a connected component of `G.induce s` is connected. -/
lemma connected_induce_image_val_supp (c : (G.induce s).ConnectedComponent) :
    (G.induce (Subtype.val '' c.supp)).Connected := by
  rw [connected_induce_iff_forall_exists_walk]
  refine ⟨c.nonempty_supp.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨p⟩ : (G.induce s).Reachable x y := by
    rw [ConnectedComponent.mem_supp_iff] at hx hy
    exact ConnectedComponent.eq.1 (hx.trans hy.symm)
  refine ⟨p.map (Embedding.induce s).toHom, fun z hz ↦ ?_⟩
  have hz' : z ∈ (p.map (Embedding.induce s).toHom).support := hz
  rw [Walk.support_map] at hz'
  obtain ⟨z', hz'', rfl⟩ := List.mem_map.1 hz'
  exact ⟨z', mem_supp_of_mem_support hx p hz'', rfl⟩

/-! ### Shortest walks have no shortcuts -/

variable (G) in
/-- No two vertices at distance two along the list are equal or adjacent: the list has no
shortcuts.  The support of a shortest walk has this property
(`noShortcut_support_of_forall_length_le`). -/
def NoShortcut : List V → Prop
  | a :: b :: c :: rest => ¬ (a = c ∨ G.Adj a c) ∧ NoShortcut (b :: c :: rest)
  | _ => True

@[simp] lemma noShortcut_nil : G.NoShortcut [] := trivial

@[simp] lemma noShortcut_singleton (a : V) : G.NoShortcut [a] := trivial

@[simp] lemma noShortcut_pair (a b : V) : G.NoShortcut [a, b] := trivial

@[simp] lemma noShortcut_cons_cons_cons {a b c : V} {rest : List V} :
    G.NoShortcut (a :: b :: c :: rest) ↔ ¬ (a = c ∨ G.Adj a c) ∧ G.NoShortcut (b :: c :: rest) :=
  Iff.rfl

/-- `NoShortcut` is transported along an injective map that reflects adjacency. -/
lemma noShortcut_map_of_injective {W : Type*} {H : SimpleGraph W} {f : V → W}
    (hf : Function.Injective f) (hadj : ∀ a b, H.Adj (f a) (f b) → G.Adj a b) :
    ∀ {L : List V}, G.NoShortcut L → H.NoShortcut (L.map f)
  | [], _ => trivial
  | [_], _ => trivial
  | [_, _], _ => trivial
  | a :: b :: c :: rest, h => by
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun h' ↦ h1 ?_, noShortcut_map_of_injective hf hadj h2⟩
    rcases h' with h' | h'
    · exact Or.inl (hf h')
    · exact Or.inr (hadj _ _ h')

/-- The support of a walk of minimal length between its endpoints has no shortcuts. -/
lemma noShortcut_support_of_forall_length_le {u v : V} (p : G.Walk u v)
    (hmin : ∀ q : G.Walk u v, p.length ≤ q.length) : G.NoShortcut p.support := by
  induction p with
  | nil => trivial
  | @cons a b c h₁ q ih =>
    have hq : ∀ q' : G.Walk b c, q.length ≤ q'.length := fun q' ↦ by
      have := hmin (Walk.cons h₁ q')
      simp only [Walk.length_cons] at this
      omega
    have ih' := ih hq
    cases q with
    | nil => trivial
    | @cons _ w _ h₂ r =>
      have hr : r.support = w :: r.support.tail := (Walk.cons_tail_support r).symm
      simp only [Walk.support_cons] at ih' ⊢
      rw [hr] at ih' ⊢
      refine ⟨?_, ih'⟩
      rintro (rfl | hac)
      · have := hmin r
        simp only [Walk.length_cons] at this
        omega
      · have := hmin (Walk.cons hac r)
        simp only [Walk.length_cons] at this
        omega

/-! ### The union of the infinite clusters -/

variable (G) in
/-- The union of the supports of the infinite connected components of `G.induce s`, as a subset
of `V`: the vertices of `s` lying in an infinite cluster of `s`.  `s` *percolates* when this set
is nonempty. -/
def infiniteClusters (s : Set V) : Set V :=
  {v | ∃ hv : v ∈ s, ((G.induce s).connectedComponentMk ⟨v, hv⟩).supp.Infinite}

lemma infiniteClusters_subset : G.infiniteClusters s ⊆ s := fun _ h ↦ h.1

lemma mem_infiniteClusters_iff_of_mem (hv : v ∈ s) :
    v ∈ G.infiniteClusters s ↔ ((G.induce s).connectedComponentMk ⟨v, hv⟩).supp.Infinite :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hv, h⟩⟩

lemma image_val_supp_subset_infiniteClusters {c : (G.induce s).ConnectedComponent}
    (hc : c.supp.Infinite) : Subtype.val '' c.supp ⊆ G.infiniteClusters s := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.2, ?_⟩
  rw [ConnectedComponent.mem_supp_iff] at hx
  rw [hx]
  exact hc

lemma mem_infiniteClusters_iff :
    v ∈ G.infiniteClusters s ↔
      ∃ c : (G.induce s).ConnectedComponent, c.supp.Infinite ∧ ∃ hv : v ∈ s, ⟨v, hv⟩ ∈ c.supp := by
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨_, h, hv, rfl⟩
  · rintro ⟨c, hc, hv, hvc⟩
    exact image_val_supp_subset_infiniteClusters hc ⟨_, hvc, rfl⟩

/-- `s` percolates iff some cluster of `s` is infinite. -/
lemma infiniteClusters_nonempty_iff :
    (G.infiniteClusters s).Nonempty ↔ ∃ c : (G.induce s).ConnectedComponent, c.supp.Infinite := by
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨_, h⟩
  · rintro ⟨c, hc⟩
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact ⟨x, image_val_supp_subset_infiniteClusters hc ⟨x, hx, rfl⟩⟩

/-- The union of the infinite clusters is closed under reachability inside `s`. -/
lemma mem_infiniteClusters_of_reachable {x y : s} (hx : x.1 ∈ G.infiniteClusters s)
    (h : (G.induce s).Reachable x y) : y.1 ∈ G.infiniteClusters s := by
  obtain ⟨c, hc, hxs, hxc⟩ := mem_infiniteClusters_iff.1 hx
  refine mem_infiniteClusters_iff.2 ⟨c, hc, y.2, ?_⟩
  rw [ConnectedComponent.mem_supp_iff] at hxc ⊢
  exact (ConnectedComponent.eq.2 h).symm.trans hxc

/-- From a point of an infinite cluster of `s`, reachability inside the union of the infinite
clusters of `s` is the same as reachability inside `s`. -/
lemma reachableIn_infiniteClusters_iff (hu : u ∈ G.infiniteClusters s) :
    G.ReachableIn (G.infiniteClusters s) u v ↔ G.ReachableIn s u v := by
  refine ⟨fun h ↦ h.mono infiniteClusters_subset, fun h ↦ ?_⟩
  refine h.induction (P := fun x ↦ G.ReachableIn (G.infiniteClusters s) u x)
    (ReachableIn.refl hu) fun a b ha hb hab hPa ↦ ?_
  have hb' : b ∈ G.infiniteClusters s :=
    mem_infiniteClusters_of_reachable (x := ⟨a, ha⟩) (y := ⟨b, hb⟩) hPa.mem_right
      (Adj.reachable (induce_adj.2 hab))
  exact hPa.trans (ReachableIn.of_adj hPa.mem_right hb' hab)

/-- Enlarging the graph and the set of vertices enlarges the union of the infinite clusters. -/
lemma infiniteClusters_mono (hGH : G ≤ H) (hst : s ⊆ t) :
    G.infiniteClusters s ⊆ H.infiniteClusters t := by
  rintro v ⟨hv, h⟩
  refine ⟨hst hv, ?_⟩
  have hsub := image_val_supp_connectedComponentMk_subset hGH hst ⟨v, hv⟩
  have : (Subtype.val '' ((G.induce s).connectedComponentMk ⟨v, hv⟩).supp).Infinite :=
    h.image Subtype.val_injective.injOn
  exact ((Set.infinite_image_iff Subtype.val_injective.injOn).1 (this.mono hsub))

/-! ### Oceans -/

variable (G H) in
/-- `ξ` is an *ocean* in `R` (Georgii (18.6) with `G` the nearest-neighbour graph and `H` the
`*`-neighbour graph of the plane `R`): `ξ ⊆ R` is connected in `G`, and every *island* of `ξ` in
`R`, i.e. every connected component of `H.induce (R \ ξ)`, is finite. -/
structure IsOceanIn (R ξ : Set V) : Prop where
  /-- An ocean in `R` lies in `R`. -/
  subset : ξ ⊆ R
  /-- An ocean is `G`-connected. -/
  connected : (G.induce ξ).Connected
  /-- Every island of an ocean is finite. -/
  finite_island : ∀ c : (H.induce (R \ ξ)).ConnectedComponent, c.supp.Finite

namespace IsOceanIn

lemma nonempty (h : IsOceanIn G H R ξ) : ξ.Nonempty := h.connected.induce_nonempty

/-- If `R` minus any finite set still percolates in `H`, then every ocean in `R` is infinite. -/
lemma infinite (h : IsOceanIn G H R ξ)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty) : ξ.Infinite := by
  intro hfin
  obtain ⟨v, hv⟩ := hR ξ hfin
  exact hv.2 (h.finite_island _)

/-- A connected set between an ocean and `R` is an ocean: its islands are contained in those
of the smaller ocean. -/
lemma of_subset_of_connected (h : IsOceanIn G H R ξ) (hξη : ξ ⊆ η) (hηR : η ⊆ R)
    (hη : (G.induce η).Connected) : IsOceanIn G H R η where
  subset := hηR
  connected := hη
  finite_island c := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    rw [ConnectedComponent.mem_supp_iff] at hx
    rw [← hx]
    have hsub : R \ η ⊆ R \ ξ := Set.sdiff_subset_sdiff_right hξη
    refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
    exact ((h.finite_island _).image Subtype.val).subset
      (image_val_supp_connectedComponentMk_subset le_rfl hsub x)

/-- Two points of an ocean `ξ ⊆ W` lie in the same cluster of `W`. -/
lemma mem_supp_connectedComponentMk (h : IsOceanIn G H R ξ) (hξW : ξ ⊆ W) {v w : V}
    (hv : v ∈ ξ) (hw : w ∈ ξ) :
    (⟨w, hξW hw⟩ : W) ∈ ((G.induce W).connectedComponentMk ⟨v, hξW hv⟩).supp := by
  rw [ConnectedComponent.mem_supp_iff]
  exact ConnectedComponent.eq.2
    ((h.connected.preconnected ⟨v, hv⟩ ⟨w, hw⟩).induce_mono le_rfl hξW).symm

/-- Every infinite cluster of a set `W ⊆ R` contains every ocean `ξ ⊆ W` in `R` (`G ≤ H`).  Such
a cluster meets `ξ`, since otherwise it would be contained in a single island of `ξ`. -/
lemma subset_image_val_supp (hGH : G ≤ H) (h : IsOceanIn G H R ξ) (hξW : ξ ⊆ W) (hWR : W ⊆ R)
    {c : (G.induce W).ConnectedComponent} (hc : c.supp.Infinite) :
    ξ ⊆ Subtype.val '' c.supp := by
  -- First, `c` meets `ξ`.
  have hmeet : ∃ (v : V) (hv : v ∈ ξ), (⟨v, hξW hv⟩ : W) ∈ c.supp := by
    by_contra hcon
    obtain ⟨x, hx⟩ := c.nonempty_supp
    have hdiff : ∀ y ∈ c.supp, y.1 ∈ R \ ξ := fun y hy ↦
      ⟨hWR y.2, fun hyξ ↦ hcon ⟨y.1, hyξ, by simpa using hy⟩⟩
    set c' := (H.induce (R \ ξ)).connectedComponentMk ⟨x, hdiff x hx⟩
    have hsub : Subtype.val '' c.supp ⊆ Subtype.val '' c'.supp := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p⟩ : (G.induce W).Reachable x y := by
        rw [ConnectedComponent.mem_supp_iff] at hx hy
        exact ConnectedComponent.eq.1 (hx.trans hy.symm)
      have hp : ∀ z ∈ ((p.map (Embedding.induce W).toHom).mapLe hGH).support, z ∈ R \ ξ := by
        intro z hz
        have hz' : z ∈ ((p.map (Embedding.induce W).toHom).mapLe hGH).support := hz
        rw [Walk.support_mapLe_eq_support, Walk.support_map] at hz'
        obtain ⟨z', hz'', rfl⟩ := List.mem_map.1 hz'
        exact hdiff z' (mem_supp_of_mem_support hx p hz'')
      refine ⟨⟨y, hdiff y hy⟩, ?_, rfl⟩
      rw [ConnectedComponent.mem_supp_iff]
      exact ConnectedComponent.eq.2 (reachable_induce_of_walk _ hp).symm
    exact hc (Set.Finite.of_finite_image (((h.finite_island c').image _).subset hsub)
      Subtype.val_injective.injOn)
  obtain ⟨v, hv, hvc⟩ := hmeet
  intro w hw
  refine ⟨⟨w, hξW hw⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff] at hvc ⊢
  rw [← hvc]
  exact ConnectedComponent.mem_supp_iff _ _ |>.1 (h.mem_supp_connectedComponentMk hξW hv hw)

/-- A set `W ⊆ R` containing an infinite ocean in `R` has exactly one infinite cluster. -/
theorem existsUnique_infinite_supp (hGH : G ≤ H) (h : IsOceanIn G H R ξ) (hinf : ξ.Infinite)
    (hξW : ξ ⊆ W) (hWR : W ⊆ R) :
    ∃! c : (G.induce W).ConnectedComponent, c.supp.Infinite := by
  obtain ⟨v, hv⟩ := h.nonempty
  refine ⟨(G.induce W).connectedComponentMk ⟨v, hξW hv⟩, ?_, fun c hc ↦ ?_⟩
  · refine Set.Infinite.mono (s := Subtype.val ⁻¹' ξ) ?_ (hinf.preimage (by simpa using hξW))
    rintro ⟨w, hwW⟩ hw
    exact h.mem_supp_connectedComponentMk hξW hv hw
  · have := h.subset_image_val_supp hGH hξW hWR hc hv
    obtain ⟨x, hx, hxv⟩ := this
    rw [ConnectedComponent.mem_supp_iff] at hx
    rw [← hx]
    congr 1
    exact Subtype.ext hxv

/-- The union of the infinite clusters of a set `W ⊆ R` containing an infinite ocean in `R` is
its unique infinite cluster. -/
theorem infiniteClusters_eq (hGH : G ≤ H) (h : IsOceanIn G H R ξ) (hinf : ξ.Infinite)
    (hξW : ξ ⊆ W) (hWR : W ⊆ R) {c : (G.induce W).ConnectedComponent} (hc : c.supp.Infinite) :
    G.infiniteClusters W = Subtype.val '' c.supp := by
  refine Set.Subset.antisymm ?_ (image_val_supp_subset_infiniteClusters hc)
  rintro v ⟨hv, hvinf⟩
  obtain ⟨c₀, -, huniq⟩ := h.existsUnique_infinite_supp hGH hinf hξW hWR
  have h1 := huniq _ hvinf
  have h2 := huniq _ hc
  refine ⟨⟨v, hv⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff, h1, h2]

/-- The union of the infinite clusters of a set `W ⊆ R` containing an infinite ocean in `R` is
itself an ocean in `R`. -/
theorem isOceanIn_infiniteClusters (hGH : G ≤ H) (h : IsOceanIn G H R ξ) (hinf : ξ.Infinite)
    (hξW : ξ ⊆ W) (hWR : W ⊆ R) : IsOceanIn G H R (G.infiniteClusters W) := by
  obtain ⟨c, hc, -⟩ := h.existsUnique_infinite_supp hGH hinf hξW hWR
  rw [h.infiniteClusters_eq hGH hinf hξW hWR hc]
  exact h.of_subset_of_connected (h.subset_image_val_supp hGH hξW hWR hc)
    (fun _ ⟨x, _, hx⟩ ↦ hx ▸ hWR x.2) (connected_induce_image_val_supp c)

end IsOceanIn

/-! ### The ocean part of a set -/

variable (G H) in
open Classical in
/-- Georgii (18.7): the union of the infinite clusters of `W` if it is an ocean in `R`, and `∅`
otherwise.  For `W ⊆ R` this is the unique maximal ocean of `W` in `R` whenever `W` contains an
ocean, and `∅` otherwise (`oceanPart_nonempty_iff`). -/
noncomputable def oceanPart (R W : Set V) : Set V :=
  if IsOceanIn G H R (G.infiniteClusters W) then G.infiniteClusters W else ∅

lemma oceanPart_subset : oceanPart G H R W ⊆ G.infiniteClusters W := by
  unfold oceanPart
  split_ifs <;> simp

lemma oceanPart_eq_of_isOceanIn (h : IsOceanIn G H R (G.infiniteClusters W)) :
    oceanPart G H R W = G.infiniteClusters W := by
  simp [oceanPart, h]

lemma oceanPart_eq_empty_of_not_isOceanIn (h : ¬ IsOceanIn G H R (G.infiniteClusters W)) :
    oceanPart G H R W = ∅ := by
  simp [oceanPart, h]

lemma isOceanIn_oceanPart_of_nonempty (h : (oceanPart G H R W).Nonempty) :
    IsOceanIn G H R (oceanPart G H R W) := by
  by_cases hW : IsOceanIn G H R (G.infiniteClusters W)
  · rwa [oceanPart_eq_of_isOceanIn hW]
  · rw [oceanPart_eq_empty_of_not_isOceanIn hW] at h
    exact absurd h Set.not_nonempty_empty

/-- Georgii, after (18.7): `ξ⁰_R(G, ·)` is the **maximal** ocean of `W` in `R`, in that every
ocean in `R` contained in `W` is contained in it. -/
theorem IsOceanIn.subset_oceanPart (hGH : G ≤ H)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty)
    (h : IsOceanIn G H R ξ) (hξW : ξ ⊆ W) (hWR : W ⊆ R) : ξ ⊆ oceanPart G H R W := by
  have hinf := h.infinite hR
  obtain ⟨c, hc, -⟩ := h.existsUnique_infinite_supp hGH hinf hξW hWR
  rw [oceanPart_eq_of_isOceanIn (h.isOceanIn_infiniteClusters hGH hinf hξW hWR),
    h.infiniteClusters_eq hGH hinf hξW hWR hc]
  exact h.subset_image_val_supp hGH hξW hWR hc

/-- Georgii, after (18.7): `{ξ⁰_R(G, ·) ≠ ∅} = {V_R(G, ·) contains an ocean}`, for a set `W ⊆ R`
when `R` minus any finite set percolates in `H ≥ G`. -/
theorem oceanPart_nonempty_iff (hGH : G ≤ H)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty) (hWR : W ⊆ R) :
    (oceanPart G H R W).Nonempty ↔ ∃ ξ, ξ ⊆ W ∧ IsOceanIn G H R ξ := by
  constructor
  · intro h
    exact ⟨_, oceanPart_subset.trans infiniteClusters_subset, isOceanIn_oceanPart_of_nonempty h⟩
  · rintro ⟨ξ, hξW, hξ⟩
    have hocean := hξ.isOceanIn_infiniteClusters hGH (hξ.infinite hR) hξW hWR
    rw [oceanPart_eq_of_isOceanIn hocean]
    obtain ⟨c, hc, -⟩ := hξ.existsUnique_infinite_supp hGH (hξ.infinite hR) hξW hWR
    exact hξ.nonempty.mono
      ((hξ.subset_image_val_supp hGH hξW hWR hc).trans (image_val_supp_subset_infiniteClusters hc))

/-! ### Removing a finite set from an ocean

Georgii asserts, in the proof of Theorem (18.17), that `{ξ⁰_P(G, ·) ≠ ∅}` is a tail event: that
whether a set of sites contains an ocean is unchanged by altering finitely many sites.  The
content is the following.  Let `ξ` be an ocean in `R` and `F` a finite set.  Then

* every island of the union of the infinite clusters of `ξ \ F` is finite
  (`IsOceanIn.finite_island_infiniteClusters_diff`) — this holds for any `G ≤ H` with `H`
  locally finite;
* `ξ \ F` has exactly one infinite cluster, so that this union is again an ocean
  (`IsOceanIn.isOceanIn_infiniteClusters_diff`).  This is **not** true in general: on the line
  `ℤ` with `G = H` the ocean `ℤ` minus the origin has two infinite clusters, and `ℤ \ {0}`
  contains no ocean.  What the plane `ℤ²` has, and the line does not, is the property `hR₁`
  below: a subset of `R` all of whose islands are finite has at most one infinite cluster.  For
  `ℤ²` it is proved in `GibbsMeasure/Model/UniqueInfiniteCluster.lean`.

`oceanPart_nonempty_congr_of_finite_diff` is the resulting tail property: two subsets of `R`
with finite symmetric difference either both contain an ocean or neither does. -/

section Removal

variable {S T K : Set V}

/-- When a connected set `S` meets `T`, every cluster of `S \ T` has a vertex adjacent to a
vertex of `S ∩ T`. -/
lemma exists_adj_of_connected_diff (hS : (G.induce S).Connected) (hST : (S ∩ T).Nonempty)
    (c : (G.induce (S \ T)).ConnectedComponent) :
    ∃ x ∈ c.supp, ∃ y ∈ S ∩ T, G.Adj x.1 y := by
  obtain ⟨⟨x, hxS, hxT⟩, hx⟩ := c.nonempty_supp
  obtain ⟨y, hyS, hyT⟩ := hST
  obtain ⟨p, hp⟩ := hS.exists_walk_of_induce hxS hyS
  obtain ⟨w, z, q, hq, hwz, hz, hzp⟩ :=
    exists_walk_until_exit (s := S \ T) p ⟨hxS, hxT⟩ fun h ↦ h.2 hyT
  have hqS : ∀ a ∈ q.support, a ∈ S \ T := fun a ha ↦ (hq a ha).1
  refine ⟨⟨w, hqS w q.end_mem_support⟩, ?_, z, ⟨hp z hzp, ?_⟩, hwz⟩
  · rw [ConnectedComponent.mem_supp_iff] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.eq.2 (reachable_induce_of_walk q hqS)).symm
  · by_contra hzT
    exact hz ⟨hp z hzp, hzT⟩

/-- If every cluster of `S` has a vertex adjacent to a finite set `K` at whose vertices `G` is
locally finite, then `S` has finitely many clusters. -/
lemma finite_connectedComponent_induce_of_forall_exists_adj (hK : K.Finite)
    (hG : ∀ k ∈ K, (G.neighborSet k).Finite)
    (h : ∀ c : (G.induce S).ConnectedComponent, ∃ x ∈ c.supp, ∃ k ∈ K, G.Adj x.1 k) :
    Finite (G.induce S).ConnectedComponent := by
  choose x hx k hk hadj using h
  have hN : (⋃ k ∈ K, G.neighborSet k).Finite := hK.biUnion hG
  have := hN.to_subtype
  refine Finite.of_injective (fun c ↦ (⟨(x c).1, Set.mem_biUnion (hk c)
    ((mem_neighborSet _ _ _).2 (hadj c).symm)⟩ : ↥(⋃ k ∈ K, G.neighborSet k))) fun c c' hcc' ↦ ?_
  have hval : x c = x c' := Subtype.ext (congrArg Subtype.val hcc' :)
  exact ConnectedComponent.eq_of_common_vertex (hx c) (hval ▸ hx c')

/-- Removing a finite set from a connected set leaves finitely many clusters, in a locally finite
graph. -/
lemma finite_connectedComponent_induce_diff (hS : (G.induce S).Connected) (hT : T.Finite)
    (hG : ∀ v, (G.neighborSet v).Finite) : Finite (G.induce (S \ T)).ConnectedComponent := by
  rcases (S ∩ T).eq_empty_or_nonempty with h | h
  · have hST : S \ T = S := sdiff_eq_left.2 (Set.disjoint_iff_inter_eq_empty.2 h)
    rw [hST]
    have := hS.preconnected.subsingleton_connectedComponent
    infer_instance
  · exact finite_connectedComponent_induce_of_forall_exists_adj (hT.inter_of_right S)
      (fun k _ ↦ hG k) (exists_adj_of_connected_diff hS h)

/-- An infinite set with finitely many clusters has an infinite cluster. -/
lemma exists_infinite_supp_of_infinite [Finite (G.induce S).ConnectedComponent]
    (hS : S.Infinite) : ∃ c : (G.induce S).ConnectedComponent, c.supp.Infinite := by
  by_contra h
  simp only [not_exists, Set.not_infinite] at h
  refine hS (Set.finite_coe_iff.1 (Set.finite_univ_iff.1 ?_))
  rw [← (G.induce S).iUnion_connectedComponentSupp]
  exact Set.finite_iUnion h

/-- With finitely many clusters, the vertices of `S` outside its infinite clusters form a finite
set. -/
lemma finite_diff_infiniteClusters [Finite (G.induce S).ConnectedComponent] :
    (S \ G.infiniteClusters S).Finite := by
  refine ((Set.toFinite {c : (G.induce S).ConnectedComponent | c.supp.Finite}).biUnion
    fun c hc ↦ hc.image Subtype.val).subset ?_
  intro x ⟨hxS, hx⟩
  refine Set.mem_biUnion (x := (G.induce S).connectedComponentMk ⟨x, hxS⟩) ?_
    ⟨⟨x, hxS⟩, ConnectedComponent.connectedComponentMk_mem, rfl⟩
  exact Set.not_infinite.1 fun hinf ↦ hx ⟨hxS, hinf⟩

/-- A subset of `R \ ξ` which is `H`-reachable from one of its points lies in a single island of
the ocean `ξ`, hence is finite. -/
lemma IsOceanIn.finite_of_subset_diff (h : IsOceanIn G H R ξ) (hS : S ⊆ R \ ξ) {x : V}
    (hx : x ∈ S) (hreach : ∀ y ∈ S, H.ReachableIn S x y) : S.Finite := by
  refine ((h.finite_island ((H.induce (R \ ξ)).connectedComponentMk ⟨x, hS hx⟩)).image
    Subtype.val).subset fun y hy ↦ ?_
  obtain ⟨hx', hy', hr⟩ := hreach y hy
  refine ⟨⟨y, hS hy⟩, ?_, rfl⟩
  rw [ConnectedComponent.mem_supp_iff]
  exact (ConnectedComponent.eq.2 (hr.induce_mono le_rfl hS)).symm

/-- **Removing a finite set from an ocean: the islands.**  Let `ξ` be an ocean in `R` for
`G ≤ H` with `H` locally finite, and let `F` be finite.  Every island in `R` of the union of the
infinite clusters of `ξ \ F` is finite.

Such an island `D` consists of points of `R \ ξ`, of `ξ ∩ F`, and of the finitely many finite
clusters of `ξ \ F`.  The `H`-clusters of `D` outside the finite set `K` of the latter two kinds
of points are `H`-connected subsets of `R \ ξ`, hence lie in islands of `ξ` and are finite, and
each is adjacent to `K`; local finiteness leaves room for only finitely many of them. -/
theorem IsOceanIn.finite_island_infiniteClusters_diff (hGH : G ≤ H)
    (hH : ∀ v, (H.neighborSet v).Finite) (h : IsOceanIn G H R ξ) {F : Set V} (hF : F.Finite)
    (c : (H.induce (R \ G.infiniteClusters (ξ \ F))).ConnectedComponent) : c.supp.Finite := by
  have hG : ∀ v, (G.neighborSet v).Finite := fun v ↦ (hH v).subset fun _ hw ↦ hGH hw
  have : Finite (G.induce (ξ \ F)).ConnectedComponent :=
    finite_connectedComponent_induce_diff h.connected hF hG
  have hKfin : ((ξ ∩ F) ∪ ((ξ \ F) \ G.infiniteClusters (ξ \ F))).Finite :=
    (hF.inter_of_right ξ).union finite_diff_infiniteClusters
  generalize hξ' : G.infiniteClusters (ξ \ F) = ξ' at c hKfin ⊢
  set K : Set V := (ξ ∩ F) ∪ ((ξ \ F) \ ξ') with hK
  suffices hDfin : (Subtype.val '' c.supp).Finite from
    Set.Finite.of_finite_image hDfin Subtype.val_injective.injOn
  have hcover : R \ ξ' ⊆ (R \ ξ) ∪ K := by
    intro y ⟨hyR, hyξ'⟩
    by_cases hyξ : y ∈ ξ
    · by_cases hyF : y ∈ F
      · exact Or.inr (Or.inl ⟨hyξ, hyF⟩)
      · exact Or.inr (Or.inr ⟨⟨hyξ, hyF⟩, hyξ'⟩)
    · exact Or.inl ⟨hyR, hyξ⟩
  set D : Set V := Subtype.val '' c.supp with hD
  have hDsub : D ⊆ R \ ξ' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hDconn : (H.induce D).Connected := connected_induce_image_val_supp c
  have hDreach : ∀ u ∈ D, ∀ v ∈ D, H.ReachableIn D u v :=
    (connected_induce_iff_forall_reachableIn.1 hDconn).2
  rcases (D ∩ K).eq_empty_or_nonempty with hDK | hDK
  · obtain ⟨x, hx⟩ := hDconn.induce_nonempty
    refine h.finite_of_subset_diff (fun y hy ↦ ?_) hx (hDreach x hx)
    rcases hcover (hDsub hy) with hyξ | hyK
    · exact hyξ
    · exact absurd ⟨hy, hyK⟩ (Set.eq_empty_iff_forall_notMem.1 hDK y)
  · have : Finite (H.induce (D \ K)).ConnectedComponent :=
      finite_connectedComponent_induce_of_forall_exists_adj (hKfin.inter_of_right D)
        (fun k _ ↦ hH k) (exists_adj_of_connected_diff hDconn hDK)
    have hDK' : (D \ K).Finite := by
      have hunion : D \ K
          = ⋃ c' : (H.induce (D \ K)).ConnectedComponent, Subtype.val '' c'.supp := by
        ext y
        constructor
        · intro hy
          exact Set.mem_iUnion.2 ⟨(H.induce (D \ K)).connectedComponentMk ⟨y, hy⟩,
            ⟨y, hy⟩, ConnectedComponent.connectedComponentMk_mem, rfl⟩
        · intro hy
          obtain ⟨c', hc'⟩ := Set.mem_iUnion.1 hy
          obtain ⟨z, -, rfl⟩ := hc'
          exact z.2
      rw [hunion]
      refine Set.finite_iUnion fun c' ↦ ?_
      obtain ⟨x, hx⟩ := c'.nonempty_supp
      refine h.finite_of_subset_diff (S := Subtype.val '' c'.supp) ?_ ⟨x, hx, rfl⟩ ?_
      · rintro _ ⟨y, -, rfl⟩
        rcases hcover (hDsub y.2.1) with h1 | h1
        · exact h1
        · exact absurd h1 y.2.2
      · exact fun y hy ↦ (connected_induce_iff_forall_reachableIn.1
          (connected_induce_image_val_supp c')).2 _ ⟨x, hx, rfl⟩ y hy
    rw [← Set.sdiff_union_inter D K]
    exact hDK'.union (hKfin.inter_of_right D)

/-- **Removing a finite set from an ocean.**  Let `ξ` be an infinite ocean in `R` for `G ≤ H`
with `H` locally finite, and let `F` be finite.  Suppose that every subset of `R` all of whose
islands are finite has at most one infinite cluster (`hR₁`; true in the plane `ℤ²`, false on the
line `ℤ`).  Then the union of the infinite clusters of `ξ \ F` is again an ocean in `R`: it is
nonempty and connected because it has exactly one infinite cluster, and its islands are finite by
`IsOceanIn.finite_island_infiniteClusters_diff`. -/
theorem IsOceanIn.isOceanIn_infiniteClusters_diff (hGH : G ≤ H)
    (hH : ∀ v, (H.neighborSet v).Finite)
    (hR₁ : ∀ X ⊆ R, (∀ c : (H.induce (R \ X)).ConnectedComponent, c.supp.Finite) →
      ∀ c₁ c₂ : (G.induce X).ConnectedComponent, c₁.supp.Infinite → c₂.supp.Infinite → c₁ = c₂)
    (h : IsOceanIn G H R ξ) (hξ : ξ.Infinite) {F : Set V} (hF : F.Finite) :
    IsOceanIn G H R (G.infiniteClusters (ξ \ F)) := by
  have hG : ∀ v, (G.neighborSet v).Finite := fun v ↦ (hH v).subset fun _ hw ↦ hGH hw
  have : Finite (G.induce (ξ \ F)).ConnectedComponent :=
    finite_connectedComponent_induce_diff h.connected hF hG
  set ξ' := G.infiniteClusters (ξ \ F) with hξ'
  have hsub : ξ' ⊆ R := infiniteClusters_subset.trans (Set.sdiff_subset.trans h.subset)
  have hisl := h.finite_island_infiniteClusters_diff hGH hH hF
  have huniq := hR₁ ξ' hsub hisl
  -- every point of `ξ'` lies in an infinite cluster of `ξ'`: its cluster in `ξ \ F`
  have hinf : ∀ (u : V) (hu : u ∈ ξ'),
      ((G.induce ξ').connectedComponentMk ⟨u, hu⟩).supp.Infinite := by
    intro u hu
    obtain ⟨huF, hucomp⟩ := hu
    set c := (G.induce (ξ \ F)).connectedComponentMk ⟨u, huF⟩ with hc
    have himg : Subtype.val '' c.supp ⊆ ξ' := image_val_supp_subset_infiniteClusters hucomp
    have hconn := connected_induce_image_val_supp c
    refine Set.Infinite.mono (s := Subtype.val ⁻¹' (Subtype.val '' c.supp)) ?_
      ((hucomp.image Subtype.val_injective.injOn).preimage (by simpa using himg))
    rintro ⟨w, hw⟩ hw'
    have hr := hconn.preconnected ⟨u, ⟨u, huF⟩, ConnectedComponent.connectedComponentMk_mem, rfl⟩
      ⟨w, hw'⟩
    rw [ConnectedComponent.mem_supp_iff]
    exact (ConnectedComponent.eq.2 (hr.induce_mono le_rfl himg)).symm
  refine ⟨hsub, ?_, hisl⟩
  rw [connected_induce_iff_forall_reachableIn]
  refine ⟨?_, fun u hu v hv ↦ ⟨hu, hv, ConnectedComponent.eq.1 (huniq _ _ (hinf u hu) (hinf v hv))⟩⟩
  obtain ⟨c, hc⟩ := exists_infinite_supp_of_infinite (G := G) (hξ.sdiff hF)
  obtain ⟨x, hx⟩ := c.nonempty_supp
  exact ⟨x, image_val_supp_subset_infiniteClusters hc ⟨x, hx, rfl⟩⟩

/-- `ξ⁰_R` of a set is nonempty exactly when the union of its infinite clusters is an ocean. -/
lemma oceanPart_nonempty_iff_isOceanIn_infiniteClusters :
    (oceanPart G H R W).Nonempty ↔ IsOceanIn G H R (G.infiniteClusters W) := by
  constructor
  · intro h
    by_contra hnot
    rw [oceanPart_eq_empty_of_not_isOceanIn hnot] at h
    exact Set.not_nonempty_empty h
  · intro h
    rw [oceanPart_eq_of_isOceanIn h]
    exact h.nonempty

/-- **Containing an ocean is a tail property.**  Two subsets `W`, `W'` of `R` with finite
symmetric difference either both contain an ocean in `R` or neither does, under the hypotheses of
`IsOceanIn.isOceanIn_infiniteClusters_diff` and `oceanPart_nonempty_iff`: an ocean `ξ ⊆ W`
yields the ocean `infiniteClusters (ξ \ (W \ W')) ⊆ W'`.  With Georgii (18.3) this is
`{ξ⁰_P(G, ·) ≠ ∅} ∈ 𝒯`, used in the proof of his Theorem (18.17). -/
theorem oceanPart_nonempty_congr_of_finite_diff (hGH : G ≤ H)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty)
    (hH : ∀ v, (H.neighborSet v).Finite)
    (hR₁ : ∀ X ⊆ R, (∀ c : (H.induce (R \ X)).ConnectedComponent, c.supp.Finite) →
      ∀ c₁ c₂ : (G.induce X).ConnectedComponent, c₁.supp.Infinite → c₂.supp.Infinite → c₁ = c₂)
    {W W' : Set V} (hW : W ⊆ R) (hW' : W' ⊆ R) (h₁ : (W \ W').Finite) (h₂ : (W' \ W).Finite) :
    (oceanPart G H R W).Nonempty ↔ (oceanPart G H R W').Nonempty := by
  have key : ∀ {W W' : Set V}, W ⊆ R → W' ⊆ R → (W \ W').Finite →
      (oceanPart G H R W).Nonempty → (oceanPart G H R W').Nonempty := by
    intro W W' hW hW' h₁ hne
    obtain ⟨ξ, hξW, hξ⟩ := (oceanPart_nonempty_iff hGH hR hW).1 hne
    refine (oceanPart_nonempty_iff hGH hR hW').2 ⟨_, fun x hx ↦ ?_,
      hξ.isOceanIn_infiniteClusters_diff hGH hH hR₁ (hξ.infinite hR) h₁⟩
    have hx' := infiniteClusters_subset hx
    by_contra hxW'
    exact hx'.2 ⟨hξW hx'.1, hxW'⟩
  exact ⟨key hW hW' h₁, key hW' hW h₂⟩

end Removal

/-! ### Transport along a symmetry of the graph -/

section Symmetry

variable {e : V ≃ V}

/-- The cluster of `e x` in `e '' s` is the `e`-image of the cluster of `x` in `s`, for an
equivalence `e` of the vertex type preserving adjacency. -/
lemma image_val_supp_connectedComponentMk_image (he : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    {x : V} (hx : x ∈ s) :
    Subtype.val '' ((G.induce (e '' s)).connectedComponentMk ⟨e x, x, hx, rfl⟩).supp
      = e '' (Subtype.val '' ((G.induce s).connectedComponentMk ⟨x, hx⟩).supp) := by
  let φ : G.induce s ≃g G.induce (e '' s) :=
    Iso.induce (⟨e, he _ _⟩ : G ≃g G) e.injective.injOn.bijOn_image
  ext y
  constructor
  · rintro ⟨⟨w, hw⟩, hwsupp, rfl⟩
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hwsupp
    obtain ⟨u, hu, rfl⟩ := hw
    refine ⟨u, ⟨⟨u, hu⟩, ?_, rfl⟩, rfl⟩
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact (Iso.reachable_iff (φ := φ) (u := ⟨u, hu⟩) (v := ⟨x, hx⟩)).1 hwsupp
  · rintro ⟨_, ⟨⟨u, hu⟩, husupp, rfl⟩, rfl⟩
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at husupp
    refine ⟨⟨e u, u, hu, rfl⟩, ?_, rfl⟩
    rw [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
    exact (Iso.reachable_iff (φ := φ) (u := ⟨u, hu⟩) (v := ⟨x, hx⟩)).2 husupp

/-- The cluster of `e x` in `e '' s` is infinite iff the cluster of `x` in `s` is. -/
lemma infinite_supp_connectedComponentMk_image_iff
    (he : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b) {x : V} (hx : x ∈ s) :
    ((G.induce (e '' s)).connectedComponentMk ⟨e x, x, hx, rfl⟩).supp.Infinite ↔
      ((G.induce s).connectedComponentMk ⟨x, hx⟩).supp.Infinite := by
  rw [← Set.infinite_image_iff (f := Subtype.val) Subtype.val_injective.injOn,
    ← Set.infinite_image_iff (f := Subtype.val) (s := ((G.induce s).connectedComponentMk
      ⟨x, hx⟩).supp) Subtype.val_injective.injOn,
    image_val_supp_connectedComponentMk_image he hx,
    Set.infinite_image_iff e.injective.injOn]

/-- Every cluster of `e '' s` is finite as soon as every cluster of `s` is. -/
lemma finite_supp_of_finite_supp_image (he : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (hfin : ∀ c : (G.induce s).ConnectedComponent, c.supp.Finite)
    (c : (G.induce (e '' s)).ConnectedComponent) : c.supp.Finite := by
  obtain ⟨y, hy⟩ := c.nonempty_supp
  rw [ConnectedComponent.mem_supp_iff] at hy
  obtain ⟨x, hx, hxy⟩ := y.2
  obtain rfl : y = ⟨e x, x, hx, rfl⟩ := Subtype.ext hxy.symm
  rw [← hy, ← Set.not_infinite, infinite_supp_connectedComponentMk_image_iff he hx,
    Set.not_infinite]
  exact hfin _

/-- **The union of the infinite clusters is equivariant** under an adjacency-preserving
equivalence of the vertex type. -/
lemma infiniteClusters_image (he : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b) (s : Set V) :
    G.infiniteClusters (e '' s) = e '' G.infiniteClusters s := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hinf⟩
    exact ⟨x, ⟨hx, (infinite_supp_connectedComponentMk_image_iff he hx).1 hinf⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hinf⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (infinite_supp_connectedComponentMk_image_iff he hx).2 hinf⟩

/-- **An ocean is carried to an ocean** by a symmetry of both graphs preserving the plane `R`. -/
lemma IsOceanIn.image (hG : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (hH : ∀ a b, H.Adj (e a) (e b) ↔ H.Adj a b) (hR : e '' R = R) (h : IsOceanIn G H R ξ) :
    IsOceanIn G H R (e '' ξ) where
  subset := by rw [← hR]; exact Set.image_mono h.subset
  connected :=
    h.connected.induce_image_of_forall_adj fun a b _ _ hab ↦ Or.inr ((hG a b).2 hab)
  finite_island := by
    have hdiff : R \ e '' ξ = e '' (R \ ξ) := by rw [Set.image_sdiff e.injective, hR]
    rw [hdiff]
    exact fun c ↦ finite_supp_of_finite_supp_image hH h.finite_island c

/-- Being an ocean is invariant under a symmetry of both graphs preserving the plane `R`. -/
lemma isOceanIn_image_iff (hG : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (hH : ∀ a b, H.Adj (e a) (e b) ↔ H.Adj a b) (hR : e '' R = R) :
    IsOceanIn G H R (e '' ξ) ↔ IsOceanIn G H R ξ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.image hG hH hR⟩
  have hG' : ∀ a b, G.Adj (e.symm a) (e.symm b) ↔ G.Adj a b := fun a b ↦ by
    rw [← hG (e.symm a) (e.symm b), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hH' : ∀ a b, H.Adj (e.symm a) (e.symm b) ↔ H.Adj a b := fun a b ↦ by
    rw [← hH (e.symm a) (e.symm b), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hR' : e.symm '' R = R := by
    conv_lhs => rw [← hR]
    exact Equiv.symm_image_image e R
  have hsymm := h.image hG' hH' hR'
  rwa [Equiv.symm_image_image] at hsymm

/-- **Georgii's `ξ⁰_R(G, ·)` is equivariant**: the ocean part of `e '' W` is the `e`-image of the
ocean part of `W`, for a symmetry `e` of both graphs which preserves `R`.  This is the invariance
used in Georgii (18.17). -/
lemma oceanPart_image (hG : ∀ a b, G.Adj (e a) (e b) ↔ G.Adj a b)
    (hH : ∀ a b, H.Adj (e a) (e b) ↔ H.Adj a b) (hR : e '' R = R) (W : Set V) :
    oceanPart G H R (e '' W) = e '' oceanPart G H R W := by
  by_cases hocean : IsOceanIn G H R (G.infiniteClusters W)
  · have h1 : IsOceanIn G H R (G.infiniteClusters (e '' W)) := by
      rw [infiniteClusters_image hG W]
      exact hocean.image hG hH hR
    rw [oceanPart_eq_of_isOceanIn h1, oceanPart_eq_of_isOceanIn hocean,
      infiniteClusters_image hG W]
  · have h1 : ¬ IsOceanIn G H R (G.infiniteClusters (e '' W)) := by
      rw [infiniteClusters_image hG W]
      exact fun h ↦ hocean ((isOceanIn_image_iff hG hH hR).1 h)
    rw [oceanPart_eq_empty_of_not_isOceanIn h1, oceanPart_eq_empty_of_not_isOceanIn hocean,
      Set.image_empty]

end Symmetry

end SimpleGraph

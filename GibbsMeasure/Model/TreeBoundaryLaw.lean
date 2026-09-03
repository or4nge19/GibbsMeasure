/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLaw
public import GibbsMeasure.Specification.MarkovInt
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Georgii §12.1: Markov chains and boundary laws on trees

Sites `S` are the vertices of a locally finite tree `G : SimpleGraph S` (`G.IsTree`,
`G.LocallyFinite`), the state space `E` is countable with the discrete σ-algebra
(`Countable E`, `MeasurableSingletonClass E`), and the a priori measure is counting measure.
Georgii assumes `E` finite throughout Chapter 12; the two places where countability is not enough
are made explicit hypotheses (`IsTransferFamily.sigmaFiniteLambdaZ_ne_top`,
`IsBoundaryLaw.mass_ne_top`), both automatic for finite `E` (`isTransferFamily_of_finite`,
`IsBoundaryLaw.of_finite`).

## Main declarations

* `SimpleGraph.bondsOf`, `SimpleGraph.outerBoundary`, `SimpleGraph.anchor`: the bonds meeting a
  finite volume `Λ`, its outer boundary `∂Λ`, and Georgii's `k_Λ` (the unique neighbour in a
  connected `Λ` of `k ∈ ∂Λ`, `IsAcyclic.anchor_eq`); `SimpleGraph.past` is the side `]-∞, ij[` of
  an oriented bond; `SimpleGraph.hull` a connected hull; `SimpleGraph.connected_induction` grows a
  connected set one boundary vertex at a time.
* `IsMarkovSpecification` — **Definition (12.1)**; `isMarkovSpecification_transferSpecification`.
* `IsMarkovChain` — **Definition (12.2)** (via conditional expectations);
  `IsMarkovChain.measure_preimage_inter_cyl` is its finite-volume content, and
  `IsMarkovChain.measure_cyl_union_eq_mul_prod` the consequence of **(12.4)** used in (12.12)(b).
* `transferWeight`, `IsTransferFamily`, `transferSpecification` — the positive Markov
  specification **(12.8)** of a family of transfer matrices **(12.9)**, as the λ-specification of
  counting measure; `transferSpecification_apply_cyl` is (12.8).
* `IsBoundaryLaw` — **Definition (12.10)**; `IsBoundaryLaw.eq_prod_div_of_normalized` is
  **(12.15)** and `isBoundaryLaw_const_iff` is **(12.16)** on the Cayley tree (the boundary-law
  side of **Corollary (12.17)**).
* `Markov.IsBoundaryLaw.isBoundaryLaw_hasse_int` — **Example (12.11)**: a boundary law of
  Definition (11.8) on `ℤ = SimpleGraph.hasse ℤ` is one of Definition (12.10).
* `boundaryLawWeight`, `volumeLaw`, `normalizedVolumeLaw`, `boundaryLawFDD`,
  `boundaryLawMeasure` — the measure **(12.13)** by Kolmogorov extension; the consistency
  **(12.14)** is `IsBoundaryLaw.exists_lintegral_boundaryLawWeight_insert` /
  `IsBoundaryLaw.normalizedVolumeLaw_map_restrict_eq`; `IsBoundaryLaw.boundaryLawMeasure_cyl` is
  (12.13) and `IsBoundaryLaw.eq_boundaryLawMeasure_of_forall_cyl` its uniqueness.
* **Theorem (12.12)(a)**: `IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure`
  (`μ ∈ 𝒢(γ^Q)`) and `IsBoundaryLaw.isMarkovChain_boundaryLawMeasure` (`μ` is a Markov chain,
  with transition matrices `boundaryLawTransition`).
* **Theorem (12.12)(b)**: `IsMarkovChain.isBoundaryLaw_chainBoundaryLaw` and
  `IsMarkovChain.eq_boundaryLawMeasure` — every Markov chain in `𝒢(γ^Q)` is the measure (12.13) of
  the boundary law `chainBoundaryLaw`, `ℓ_{ij}(x) = P_{ji}(a, x) / Q_{ji}(a, x)`.

Not formalised here: Theorem (12.6) (extreme Gibbs measures of Markov specifications are Markov
chains, which needs the backward martingale convergence theorem), the uniqueness up to a factor
in (12.12)(b), Comments (12.3), and Corollary (12.18).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ## General lemmas on graphs and trees

Intended Mathlib home: `Mathlib/Combinatorics/SimpleGraph/Finite.lean` (bonds and outer
boundary of a finite vertex set), `Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean`
(walk characterisation of connected induced subgraphs) and
`Mathlib/Combinatorics/SimpleGraph/Acyclic.lean` (boundary vertices of a connected set in a tree).
-/

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

variable (G)

open Classical in
/-- Georgii's `k_Λ`: the neighbour of a boundary vertex `k ∈ ∂Λ` inside `Λ`, unique when `Λ` is
connected and `G` is a tree (`IsAcyclic.eq_of_adj_of_mem_outerBoundary`); `k` itself otherwise. -/
def anchor (Λ : Finset V) (k : V) : V :=
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

omit hG in
lemma connected_induce_insert_of_mem_outerBoundary :
    (G.induce ((insert i Λ : Finset V) : Set V)).Connected := by
  rw [Finset.coe_insert]
  exact connected_induce_insert_of_adj hΛ (Finset.mem_coe.2 (G.anchor_mem hi)) (G.adj_anchor hi)

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

lemma injective_mk_left (i : V) : Function.Injective fun k : V ↦ s(i, k) := fun _ _ h ↦
  Sym2.congr_right.1 h

/-! ### A connected hull of a finite set in a connected graph -/

section Hull

variable {G} [DecidableEq V] (hG : G.Connected) (o : V)

/-- A connected finite set containing `Λ` and a root `o`: the union of the supports of walks from
`o` to the points of `Λ`. -/
def hull (Λ : Finset V) : Finset V :=
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

/-! ### Singletons, monotonicity, and induction along a connected set -/

section Extra

variable {G} [DecidableEq V] [G.LocallyFinite]

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

end Extra

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

/-! ## The counting-measure reference kernel and cylinders on an arbitrary site space

These generalise the `ℤ`-specific lemmas of `GibbsMeasure/Model/BoundaryLaw.lean`
(`lintegral_lambdaCount`, `lintegral_lambdaCount_insert`, `setLIntegral_lambdaCount_cyl'`,
`map_restrict_withDensity_insert`, `map_restrict_eq_of_subset`) and of
`GibbsMeasure/Model/MarkovChain.lean` (`cyl`, `insertPiEquiv`, `ext_of_forall_cyl`) to an
arbitrary site space `S`; the `ℤ` versions should become instances. Intended home:
`GibbsMeasure/Prereqs/`. -/

namespace MeasureTheory.GibbsMeasure.Tree

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

local notation "λ₀" => Specification.sigmaFiniteLambdaFun (S := S) (E := E) Measure.count

/-! ### Cylinders `{σ_Λ = η_Λ}` -/

section Cyl

/-- The cylinder `{σ_Λ = η_Λ}`: Mathlib's `cylinder Λ` over the singleton `{η_Λ}`. -/
abbrev cyl (Λ : Finset S) (η : S → E) : Set (S → E) := cylinder Λ {Λ.restrict η}

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma mem_cyl {Λ : Finset S} {η σ : S → E} : σ ∈ cyl Λ η ↔ ∀ k ∈ Λ, σ k = η k := by
  simp only [cyl, mem_cylinder, Set.mem_singleton_iff, funext_iff]
  exact ⟨fun h k hk ↦ h ⟨k, hk⟩, fun h k ↦ h k.1 k.2⟩

omit [DecidableEq S] [Countable E] in
lemma measurableSet_cyl (Λ : Finset S) (η : S → E) : MeasurableSet (cyl Λ η) :=
  MeasurableSet.cylinder _ (measurableSet_singleton _)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_congr {Λ : Finset S} {η η' : S → E} (h : ∀ k ∈ Λ, η k = η' k) :
    cyl Λ η = cyl Λ η' := by
  ext σ
  simp only [mem_cyl]
  exact ⟨fun h' k hk ↦ (h' k hk).trans (h k hk), fun h' k hk ↦ (h' k hk).trans (h k hk).symm⟩

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_update_of_notMem {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) (y : E) :
    cyl Λ (Function.update η j y) = cyl Λ η :=
  cyl_congr fun _ hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hj) _ _

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_mono {Λ Δ : Finset S} (h : Λ ⊆ Δ) (η : S → E) : cyl Δ η ⊆ cyl Λ η := fun _ hσ ↦
  mem_cyl.2 fun k hk ↦ mem_cyl.1 hσ k (h hk)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma mem_cyl_self (Λ : Finset S) (η : S → E) : η ∈ cyl Λ η := mem_cyl.2 fun _ _ ↦ rfl

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_insert_eq_inter (Λ : Finset S) (j : S) (η : S → E) :
    cyl (insert j Λ) η = {σ | σ j = η j} ∩ cyl Λ η := by
  ext σ
  simp only [mem_cyl, Finset.mem_insert, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_eq_or_imp]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- A cylinder over `Λ` is the disjoint union of the cylinders over `Λ ∪ {j}`, `j ∉ Λ`, obtained
by filling in the free coordinate `j`. -/
lemma cyl_eq_iUnion_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) :
    cyl Λ η = ⋃ y : E, cyl (insert j Λ) (Function.update η j y) := by
  ext σ
  simp only [Set.mem_iUnion, cyl_insert_eq_inter, cyl_update_of_notMem hj, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Function.update_self]
  exact ⟨fun h ↦ ⟨σ j, rfl, h⟩, fun ⟨_, _, h⟩ ↦ h⟩

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pairwise_disjoint_cyl_insert_update (Λ : Finset S) (j : S) (η : S → E) :
    Pairwise (Function.onFun Disjoint fun y : E ↦ cyl (insert j Λ) (Function.update η j y)) := by
  intro y y' hyy'
  rw [Function.onFun, Set.disjoint_left]
  intro σ hσ hσ'
  have h1 := mem_cyl.1 hσ j (Finset.mem_insert_self j Λ)
  have h2 := mem_cyl.1 hσ' j (Finset.mem_insert_self j Λ)
  rw [Function.update_self] at h1 h2
  exact hyy' (h1.symm.trans h2)

/-- The measure of a cylinder is the sum over a free coordinate of the measures of the finer
cylinders. -/
lemma measure_cyl_eq_tsum_insert (μ : Measure (S → E)) {Λ : Finset S} {j : S} (hj : j ∉ Λ)
    (η : S → E) :
    μ (cyl Λ η) = ∑' y : E, μ (cyl (insert j Λ) (Function.update η j y)) := by
  rw [cyl_eq_iUnion_insert hj η, measure_iUnion (pairwise_disjoint_cyl_insert_update Λ j η)
    fun _ ↦ measurableSet_cyl _ _]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma preimage_singleton_eq_cyl (i : S) (x : E) (η : S → E) :
    (fun σ : S → E ↦ σ i) ⁻¹' {x} = cyl {i} (Function.update η i x) := by
  ext σ
  rw [Set.mem_preimage, Set.mem_singleton_iff, mem_cyl]
  simp

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma preimage_inter_preimage_eq_cyl {i j : S} (hij : i ≠ j) (x y : E) (η : S → E) :
    (fun σ : S → E ↦ σ i) ⁻¹' {x} ∩ (fun σ ↦ σ j) ⁻¹' {y}
      = cyl {i, j} (Function.update (Function.update η i x) j y) := by
  ext σ
  simp only [mem_cyl, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Function.update_of_ne hij,
    Function.update_self]

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma cyl_empty (η : S → E) : cyl (∅ : Finset S) η = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_cyl.2 fun _ h ↦ absurd h (Finset.notMem_empty _)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma restrict_preimage_singleton (Λ : Finset S) (η : S → E) :
    Λ.restrict ⁻¹' ({Λ.restrict η} : Set (Λ → E)) = cyl Λ η := rfl

omit [DecidableEq S] [Countable E] in
/-- A cylinder over `Δ ⊆ V` is measurable for the cylinder σ-algebra of `V`. -/
lemma measurableSet_cylinderEvents_cyl {V : Set S} {Δ : Finset S} (h : (Δ : Set S) ⊆ V)
    (ζ : S → E) : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) V] (cyl Δ ζ) := by
  have : cyl Δ ζ = ⋂ k ∈ Δ, (fun σ : S → E ↦ σ k) ⁻¹' {ζ k} := by
    ext σ
    rw [mem_cyl]
    simp
  rw [this]
  exact MeasurableSet.biInter Δ.countable_toSet fun k hk ↦
    measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (h (Finset.mem_coe.2 hk))
      (measurableSet_singleton _)

omit [DecidableEq S] in
lemma measurable_measure_cyl (μ : Measure (S → E)) (Δ : Finset S) :
    Measurable fun ξ : S → E ↦ μ (cyl Δ ξ) := by
  have : (fun ξ : S → E ↦ μ (cyl Δ ξ)) = (fun x : Δ → E ↦ μ (Δ.restrict ⁻¹' {x})) ∘ Δ.restrict :=
    rfl
  rw [this]
  exact (measurable_of_countable _).comp (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ)

/-- The cylinders over finite subsets of `V`: a π-system generating `cylinderEvents V`. -/
def cylindersIn (V : Set S) : Set (Set (S → E)) :=
  {A | ∃ (W : Finset S) (ω : S → E), (W : Set S) ⊆ V ∧ A = cyl W ω}

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma isPiSystem_cylindersIn (V : Set S) : IsPiSystem (cylindersIn (E := E) V) := by
  classical
  rintro _ ⟨W₁, ω₁, hW₁, rfl⟩ _ ⟨W₂, ω₂, hW₂, rfl⟩ ⟨σ, hσ₁, hσ₂⟩
  refine ⟨W₁ ∪ W₂, σ, by rw [Finset.coe_union]; exact Set.union_subset hW₁ hW₂, ?_⟩
  ext τ
  simp only [Set.mem_inter_iff, mem_cyl, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    rcases hk with hk | hk
    · exact (h1 k hk).trans (mem_cyl.1 hσ₁ k hk).symm
    · exact (h2 k hk).trans (mem_cyl.1 hσ₂ k hk).symm
  · intro h
    exact ⟨fun k hk ↦ (h k (Or.inl hk)).trans (mem_cyl.1 hσ₁ k hk),
      fun k hk ↦ (h k (Or.inr hk)).trans (mem_cyl.1 hσ₂ k hk)⟩

omit [DecidableEq S] in
/-- For a countable state space, `cylinderEvents V` is generated by the cylinders over finite
subsets of `V`. -/
lemma cylinderEvents_eq_generateFrom_cylindersIn [Nonempty E] (V : Set S) :
    cylinderEvents (X := fun _ : S ↦ E) V = MeasurableSpace.generateFrom (cylindersIn V) := by
  classical
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup₂_le fun k hk s hs ↦ ?_
    obtain ⟨t, -, rfl⟩ := hs
    have : (fun σ : S → E ↦ σ k) ⁻¹' t
        = ⋃ x ∈ t, cyl {k} (Function.update (fun _ ↦ Classical.arbitrary E) k x) := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
      constructor
      · intro h
        exact ⟨σ k, h, mem_cyl.2 fun m hm ↦ by
          rw [Finset.mem_singleton.1 hm, Function.update_self]⟩
      · rintro ⟨x, hx, h⟩
        have := mem_cyl.1 h k (Finset.mem_singleton_self k)
        rw [Function.update_self] at this
        rw [this]
        exact hx
    rw [this]
    exact MeasurableSet.biUnion t.to_countable fun x _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨{k}, _, by simpa using hk, rfl⟩
  · rintro _ ⟨W, ω, hW, rfl⟩
    exact measurableSet_cylinderEvents_cyl hW ω

end Cyl

/-! ### Marginals -/

section Marginals

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
lemma map_restrict_eq_of_subset {μ ν : Measure (S → E)} {Λ Δ : Finset S} (h : Λ ⊆ Δ)
    (hμν : μ.map Δ.restrict = ν.map Δ.restrict) : μ.map Λ.restrict = ν.map Λ.restrict := by
  rw [← Finset.restrict₂_comp_restrict (π := fun _ : S ↦ E) h,
    ← Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) h)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ),
    ← Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) h)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) Δ), hμν]

omit [DecidableEq S] in
/-- Two measures with the same cylinder probabilities over `Λ` have the same marginal on `Λ`. -/
lemma map_restrict_eq_of_forall_cyl [Nonempty E] {μ ν : Measure (S → E)} (Λ : Finset S)
    (h : ∀ η, μ (cyl Λ η) = ν (cyl Λ η)) : μ.map Λ.restrict = ν.map Λ.restrict := by
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ)
    (measurableSet_singleton _), Measure.map_apply
    (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) (measurableSet_singleton _)]
  have hx : x = Λ.restrict (juxt (Λ : Set S) (Classical.arbitrary (S → E)) x) := by
    · funext k
      exact (juxt_apply_of_mem k.2 x).symm
  rw [hx, restrict_preimage_singleton]
  exact h _

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
/-- A finite measure is determined by its finite-dimensional marginals (`IsProjectiveLimit.unique`
for the family of its own marginals). -/
lemma ext_of_forall_map_restrict {μ ν : Measure (S → E)} [IsFiniteMeasure μ]
    (h : ∀ Λ : Finset S, μ.map Λ.restrict = ν.map Λ.restrict) : μ = ν :=
  IsProjectiveLimit.unique (P := fun Λ : Finset S ↦ μ.map Λ.restrict) (fun _ ↦ rfl)
    fun Λ ↦ (h Λ).symm

omit [DecidableEq S] in
/-- Two finite measures agreeing on the cylinders over a cofinal family of volumes are equal. -/
lemma ext_of_forall_exists_cyl_eq [Nonempty E] {μ ν : Measure (S → E)} [IsFiniteMeasure μ]
    (h : ∀ Λ : Finset S, ∃ H : Finset S, Λ ⊆ H ∧ ∀ η, μ (cyl H η) = ν (cyl H η)) : μ = ν :=
  ext_of_forall_map_restrict fun Λ ↦ by
    obtain ⟨H, hΛH, hH⟩ := h Λ
    exact map_restrict_eq_of_subset hΛH (map_restrict_eq_of_forall_cyl H hH)

end Marginals

/-! ### The counting reference kernel `λ_Λ` -/

section LambdaCount

omit [DecidableEq S] in
lemma measurable_pair (g : E → E → ℝ≥0∞) (k l : S) :
    Measurable fun σ : S → E ↦ g (σ k) (σ l) :=
  (measurable_of_countable fun p : E × E ↦ g p.1 p.2).comp
    (f := fun σ : S → E ↦ (σ k, σ l)) ((measurable_pi_apply k).prodMk (measurable_pi_apply l))

omit [DecidableEq S] in
lemma measurable_coord (g : E → ℝ≥0∞) (k : S) : Measurable fun σ : S → E ↦ g (σ k) :=
  (measurable_of_countable g).comp (measurable_pi_apply k)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma juxt_restrict (Λ : Finset S) (η : S → E) : juxt (Λ : Set S) η (Λ.restrict η) = η := by
  funext k
  by_cases hk : k ∈ Λ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hk)]; rfl
  · rw [juxt_apply_of_not_mem (by simpa using hk)]

/-- Splitting off the coordinate `j` of a product over `insert j Λ`. -/
def insertPiEquiv (Λ : Finset S) (j : S) (hj : j ∉ Λ) :
    (Π _k : (insert j Λ : Finset S), E) ≃ (Π _k : Λ, E) × E where
  toFun x := (fun k ↦ x ⟨↑k, Finset.mem_insert_of_mem k.2⟩, x ⟨j, Finset.mem_insert_self j Λ⟩)
  invFun p := fun k ↦ if h : (k : S) ∈ Λ then p.1 ⟨↑k, h⟩ else p.2
  left_inv x := by
    funext k
    obtain ⟨k, hk⟩ := k
    by_cases h : k ∈ Λ
    · simp only [dite_eq_left h]
    · have hkj : k = j := by
        rcases Finset.mem_insert.1 hk with h' | h'
        · exact h'
        · exact absurd h' h
      subst hkj
      simp only [dite_eq_right h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext k
      exact dite_eq_left k.2
    · exact dite_eq_right hj

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma juxt_insertPiEquiv_symm {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E) (x : Λ → E)
    (y : E) :
    juxt ((insert j Λ : Finset S) : Set S) η ((insertPiEquiv Λ j hj).symm (x, y))
      = Function.update (juxt (Λ : Set S) η x) j y := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_insert_self i Λ))]
    exact dite_eq_right hj
  · rw [Function.update_of_ne hij]
    by_cases hiΛ : i ∈ Λ
    · rw [juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_insert_of_mem hiΛ)),
        juxt_apply_of_mem (Finset.mem_coe.2 hiΛ)]
      exact dite_eq_left hiΛ
    · rw [juxt_apply_of_not_mem (show i ∉ ((insert j Λ : Finset S) : Set S) by simp [hij, hiΛ]),
        juxt_apply_of_not_mem (show i ∉ (Λ : Set S) by simpa using hiΛ)]

omit [DecidableEq S] in
/-- For counting measure, integrating against `λ_Λ(·|η)` sums over the configurations on `Λ`. -/
lemma lintegral_lambdaCount (Λ : Finset S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ Λ η) = ∑' x : Λ → E, F (juxt (Λ : Set S) η x) := by
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map, lintegral_map hF Measurable.juxt]
  erw [Measure.pi_count (X := fun _ : ((Λ : Set S) : Type _) ↦ E)]
  rw [lintegral_count]
  rfl

omit [DecidableEq S] in
lemma lintegral_lambdaCount_congr (Λ : Finset S) (η : S → E) {F G : (S → E) → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (h : ∀ ζ, (∀ k ∉ Λ, ζ k = η k) → F ζ = G ζ) :
    ∫⁻ ζ, F ζ ∂(λ₀ Λ η) = ∫⁻ ζ, G ζ ∂(λ₀ Λ η) := by
  rw [lintegral_lambdaCount Λ η hF, lintegral_lambdaCount Λ η hG]
  exact tsum_congr fun x ↦ h _ (juxt_agree_on_compl Λ η x)

omit [DecidableEq S] in
lemma lintegral_lambdaCount_empty (η : S → E) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ ∅ η) = F η := by
  rw [lintegral_lambdaCount ∅ η hF]
  have : IsEmpty ((∅ : Finset S) : Type _) := ⟨fun k ↦ absurd k.2 (Finset.notMem_empty _)⟩
  have hj : ∀ x : ((∅ : Finset S) : Type _) → E, juxt ((∅ : Finset S) : Set S) η x = η :=
    fun x ↦ funext fun k ↦ juxt_apply_of_not_mem (show k ∉ ((∅ : Finset S) : Set S) by simp) x
  simp_rw [hj]
  rw [tsum_fintype, Fintype.sum_unique]

omit [Countable E] [MeasurableSingletonClass E] in
lemma measurable_update_left' (j : S) (y : E) :
    Measurable fun σ : S → E ↦ Function.update σ j y :=
  measurable_update_left

/-- Integrating against `λ_{Λ ∪ {j}}(·|η)` for counting measure: sum over the free coordinate
`j`, then integrate against `λ_Λ(·|η)`. -/
lemma lintegral_lambdaCount_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ (insert j Λ) η) = ∫⁻ ζ, ∑' y, F (Function.update ζ j y) ∂(λ₀ Λ η) := by
  have hG : Measurable fun ζ : S → E ↦ ∑' y, F (Function.update ζ j y) :=
    Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y)
  rw [lintegral_lambdaCount _ _ hF, lintegral_lambdaCount _ _ hG]
  calc ∑' x : ↥(insert j Λ) → E, F (juxt ((insert j Λ : Finset S) : Set S) η x)
      = ∑' p : (Λ → E) × E, F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm p)) := (Equiv.tsum_eq _ _).symm
    _ = ∑' (x : Λ → E) (y : E), F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm (x, y))) :=
        ENNReal.tsum_prod (f := fun x y ↦ F (juxt ((insert j Λ : Finset S) : Set S) η
          ((insertPiEquiv Λ j hj).symm (x, y))))
    _ = ∑' (x : Λ → E) (y : E), F (Function.update (juxt (Λ : Set S) η x) j y) := by
        simp_rw [juxt_insertPiEquiv_symm hj η]

lemma lintegral_lambdaCount_singleton (j : S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ {j} η) = ∑' y, F (Function.update η j y) := by
  rw [← Finset.insert_empty, lintegral_lambdaCount_insert (Finset.notMem_empty j) η hF,
    lintegral_lambdaCount_empty (F := fun ζ ↦ ∑' y, F (Function.update ζ j y)) _
      (Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y))]

omit [DecidableEq S] in
/-- Integrating over the cylinder `{σ_Λ = σ_Λ}` against `λ_Λ(·|η)` evaluates at the configuration
`σ_Λ η_{Λᶜ}`. -/
lemma setLIntegral_lambdaCount_cyl' (Λ : Finset S) (η σ : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ in cyl Λ σ, F ζ ∂(λ₀ Λ η) = F (juxt (Λ : Set S) η (Λ.restrict σ)) := by
  rw [← lintegral_indicator (measurableSet_cyl Λ σ), lintegral_lambdaCount Λ η
    (hF.indicator (measurableSet_cyl Λ σ))]
  rw [tsum_eq_single (Λ.restrict σ) fun x hx ↦ ?_]
  · exact Set.indicator_of_mem (show juxt (Λ : Set S) η (Λ.restrict σ) ∈ cyl Λ σ from
      mem_cyl.2 fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _) _
  · refine Set.indicator_of_notMem (fun h ↦ hx (funext fun k ↦ ?_)) _
    have := mem_cyl.1 h k k.2
    rwa [juxt_apply_of_mem (Finset.mem_coe.2 k.2)] at this

omit [DecidableEq S] in
lemma setLIntegral_lambdaCount_cyl (Λ : Finset S) (η : S → E) {F : (S → E) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ζ in cyl Λ η, F ζ ∂(λ₀ Λ η) = F η := by
  rw [setLIntegral_lambdaCount_cyl' Λ η η hF, juxt_restrict]

/-- Integrating over the cylinder `{σ_H = ζ_H}`, `Λ ⊆ H`, against `λ_Λ(·|ω)`: the value at
`ζ_Λ ω_{Λᶜ}` if `ω` agrees with `ζ` on `H \ Λ`, and `0` otherwise. -/
lemma setLIntegral_lambdaCount_cyl_of_subset {Λ H : Finset S} (hΛH : Λ ⊆ H) (ω ζ : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ξ in cyl H ζ, F ξ ∂(λ₀ Λ ω)
      = (cyl (H \ Λ) ζ).indicator (fun ω ↦ F (juxt (Λ : Set S) ω (Λ.restrict ζ))) ω := by
  rw [← lintegral_indicator (measurableSet_cyl H ζ),
    lintegral_lambdaCount Λ ω (hF.indicator (measurableSet_cyl H ζ))]
  by_cases hω : ω ∈ cyl (H \ Λ) ζ
  · rw [Set.indicator_of_mem hω, tsum_eq_single (Λ.restrict ζ) fun x hx ↦ ?_]
    · refine Set.indicator_of_mem (mem_cyl.2 fun k hk ↦ ?_) _
      by_cases hkΛ : k ∈ Λ
      · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]; rfl
      · rw [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hkΛ)]
        exact mem_cyl.1 hω k (Finset.mem_sdiff.2 ⟨hk, hkΛ⟩)
    · refine Set.indicator_of_notMem (fun h ↦ hx (funext fun k ↦ ?_)) _
      have := mem_cyl.1 h k (hΛH k.2)
      rwa [juxt_apply_of_mem (Finset.mem_coe.2 k.2)] at this
  · rw [Set.indicator_of_notMem hω]
    refine ENNReal.tsum_eq_zero.2 fun x ↦ Set.indicator_of_notMem (fun h ↦ hω (mem_cyl.2
      fun k hk ↦ ?_)) _
    have hk' := Finset.mem_sdiff.1 hk
    have := mem_cyl.1 h k hk'.1
    rwa [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hk'.2)] at this

omit [DecidableEq S] in
/-- The partition function of a pre-modification for counting measure dominates the weight of the
boundary condition itself. -/
lemma sigmaFiniteLambdaZ_count_ne_zero {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier ρ) {Λ : Finset S} {ω : S → E} (h : ρ Λ ω ≠ 0) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count ρ Λ ω ≠ 0 := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount Λ ω (hρ.measurable Λ)]
  refine ne_of_gt ((pos_iff_ne_zero.2 h).trans_le ?_)
  have := ENNReal.le_tsum (f := fun x : Λ → E ↦ ρ Λ (juxt (Λ : Set S) ω x)) (Λ.restrict ω)
  rwa [juxt_restrict] at this

omit [DecidableEq S] in
/-- On a finite state space the partition functions of a finite weight are finite. -/
lemma sigmaFiniteLambdaZ_count_ne_top_of_finite [Finite E] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier ρ) (htop : ∀ Λ ω, ρ Λ ω ≠ ⊤) (Λ : Finset S) (ω : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count ρ Λ ω ≠ ⊤ := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount Λ ω (hρ.measurable Λ)]
  have : Fintype (Λ → E) := Fintype.ofFinite _
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun _ _ ↦ htop _ _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma restrict_update_of_notMem {Λ : Finset S} {j : S} (h : j ∉ Λ) (σ : S → E) (z : E) :
    Λ.restrict (Function.update σ j z) = Λ.restrict σ := by
  funext k
  exact Function.update_of_ne (ne_of_mem_of_not_mem k.2 h) z σ

/-- Marginalising a density on `Λ ∪ {j}` to `Λ` sums the free coordinate. -/
lemma map_restrict_withDensity_insert {Λ : Finset S} {j : S} (hj : j ∉ Λ) (η : S → E)
    {w w' : (S → E) → ℝ≥0∞} (hw : Measurable w)
    (h : ∀ ζ, ∑' y, w (Function.update ζ j y) = w' ζ) :
    ((λ₀ (insert j Λ) η).withDensity w).map Λ.restrict
      = ((λ₀ Λ η).withDensity w').map Λ.restrict := by
  ext A hA
  have hA' : MeasurableSet (Λ.restrict ⁻¹' A : Set (S → E)) :=
    Finset.measurable_restrict (X := fun _ : S ↦ E) Λ hA
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) hA,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ) hA,
    withDensity_apply _ hA', withDensity_apply _ hA', ← lintegral_indicator hA',
    ← lintegral_indicator hA', lintegral_lambdaCount_insert hj η (hw.indicator hA')]
  refine lintegral_congr fun ζ ↦ ?_
  by_cases hζ : ζ ∈ Λ.restrict ⁻¹' A
  · have hmem : ∀ y, Function.update ζ j y ∈ Λ.restrict ⁻¹' A := fun y ↦ by
      change Λ.restrict (Function.update ζ j y) ∈ A
      rwa [restrict_update_of_notMem hj]
    simp_rw [Set.indicator_of_mem (hmem _), Set.indicator_of_mem hζ, h]
  · have hmem : ∀ y, Function.update ζ j y ∉ Λ.restrict ⁻¹' A := fun y hy ↦ by
      change Λ.restrict (Function.update ζ j y) ∈ A at hy
      rw [restrict_update_of_notMem hj] at hy
      exact hζ hy
    simp_rw [Set.indicator_of_notMem (hmem _), Set.indicator_of_notMem hζ, tsum_zero]

/-- Integrating against `λ_{Λ₁ ∪ Λ₂}` for disjoint volumes: integrate over `Λ₂`, then over `Λ₁`
(counting measure; Georgii's Notation (1.26) `λ_{Λ₁} λ_{Λ₂} = λ_{Λ₁ ∪ Λ₂}`). -/
lemma lintegral_lambdaCount_union {Λ₁ Λ₂ : Finset S} (h : Disjoint Λ₁ Λ₂) (η : S → E)
    {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ (Λ₁ ∪ Λ₂) η) = ∫⁻ ζ, ∫⁻ ξ, F ξ ∂(λ₀ Λ₂ ζ) ∂(λ₀ Λ₁ η) := by
  induction Λ₂ using Finset.induction_on generalizing F with
  | empty =>
    simp_rw [lintegral_lambdaCount_empty _ hF]
    rw [Finset.union_empty]
  | insert j Λ₂ hj ih =>
    rw [Finset.disjoint_insert_right] at h
    have hG : Measurable fun ζ : S → E ↦ ∑' y, F (Function.update ζ j y) :=
      Measurable.tsum fun y ↦ hF.comp (measurable_update_left' j y)
    rw [Finset.union_insert, lintegral_lambdaCount_insert (by simp [h.1, hj]) η hF, ih h.2 hG]
    exact lintegral_congr fun ζ ↦ (lintegral_lambdaCount_insert hj ζ hF).symm

omit [DecidableEq S] in
lemma measurable_lintegral_lambdaCount (Λ : Finset S) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun ζ : S → E ↦ ∫⁻ ξ, F ξ ∂(λ₀ Λ ζ) :=
  hF.lintegral_kernel.mono cylinderEvents_le_pi le_rfl

omit [DecidableEq S] in
/-- Integrating a product of one-site functions over `λ_V` factorises. -/
lemma lintegral_lambdaCount_prod (V : Finset S) (ζ : S → E) (f : S → E → ℝ≥0∞) :
    ∫⁻ ξ, ∏ k ∈ V, f k (ξ k) ∂(λ₀ V ζ) = ∏ k ∈ V, ∑' y, f k y := by
  classical
  induction V using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [lintegral_lambdaCount_empty _ measurable_const]
  | insert j V hj ih =>
    have hF : Measurable fun ξ : S → E ↦ ∏ k ∈ insert j V, f k (ξ k) :=
      Finset.measurable_prod _ fun k _ ↦ measurable_coord (f k) k
    rw [lintegral_lambdaCount_insert hj ζ hF, Finset.prod_insert hj, ← ih,
      ← lintegral_const_mul _ (Finset.measurable_prod _ fun k _ ↦ measurable_coord (f k) k)]
    refine lintegral_congr fun ξ ↦ ?_
    simp_rw [Finset.prod_insert hj, Function.update_self]
    have hprod : ∀ y, ∏ k ∈ V, f k (Function.update ξ j y k) = ∏ k ∈ V, f k (ξ k) := fun y ↦
      Finset.prod_congr rfl fun k hk ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
    simp_rw [hprod]
    rw [ENNReal.tsum_mul_right]

/-- Marginalising a density on `H ∪ V` to `H` integrates out the coordinates in `V`. -/
lemma map_restrict_withDensity_union {H V : Finset S} (hHV : Disjoint H V) (η : S → E)
    {w : (S → E) → ℝ≥0∞} (hw : Measurable w) :
    ((λ₀ (H ∪ V) η).withDensity w).map H.restrict
      = ((λ₀ H η).withDensity fun ζ ↦ ∫⁻ ξ, w ξ ∂(λ₀ V ζ)).map H.restrict := by
  ext A hA
  have hA' : MeasurableSet (H.restrict ⁻¹' A : Set (S → E)) :=
    Finset.measurable_restrict (X := fun _ : S ↦ E) H hA
  rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) H) hA,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) H) hA,
    withDensity_apply _ hA', withDensity_apply _ hA', ← lintegral_indicator hA',
    ← lintegral_indicator hA', lintegral_lambdaCount_union hHV η (hw.indicator hA')]
  refine lintegral_congr fun ζ ↦ ?_
  have hres : ∀ ξ : S → E, (∀ k ∉ V, ξ k = ζ k) → H.restrict ξ = H.restrict ζ := fun ξ hξ ↦
    funext fun k ↦ hξ k (Finset.disjoint_left.1 hHV k.2)
  by_cases hζ : ζ ∈ H.restrict ⁻¹' A
  · rw [Set.indicator_of_mem hζ]
    exact lintegral_lambdaCount_congr V ζ (hw.indicator hA') hw fun ξ hξ ↦
      Set.indicator_of_mem (show ξ ∈ H.restrict ⁻¹' A by
        change H.restrict ξ ∈ A; rwa [hres ξ hξ]) _
  · rw [Set.indicator_of_notMem hζ]
    rw [lintegral_lambdaCount_congr V ζ (hw.indicator hA') measurable_const
      (G := fun _ ↦ 0) fun ξ hξ ↦ Set.indicator_of_notMem (fun h ↦ hζ (by
        change H.restrict ξ ∈ A at h; rwa [hres ξ hξ] at h)) _]
    simp

/-- The measure of a cylinder over `H` is the sum over the spins in a disjoint finite `V` of the
measures of the cylinders over `H ∪ V`. -/
lemma measure_cyl_eq_lintegral_lambdaCount (μ : Measure (S → E)) {H V : Finset S}
    (hHV : Disjoint H V) (ζ : S → E) :
    μ (cyl H ζ) = ∫⁻ ξ, μ (cyl (H ∪ V) ξ) ∂(λ₀ V ζ) := by
  induction V using Finset.induction_on generalizing ζ with
  | empty => rw [Finset.union_empty, lintegral_lambdaCount_empty _ (measurable_measure_cyl μ H)]
  | insert j V hj ih =>
    rw [Finset.disjoint_insert_right] at hHV
    rw [ih hHV.2, lintegral_lambdaCount_insert hj ζ (measurable_measure_cyl μ _)]
    refine lintegral_congr fun ξ ↦ ?_
    rw [Finset.union_insert, measure_cyl_eq_tsum_insert μ (Λ := H ∪ V) (j := j)
      (by simp [hHV.1, hj]) ξ]

end LambdaCount


/-! ## Georgii's `γ^Q` on a locally finite graph: transfer matrices along the bonds

A family `Q_{ij}` of matrices on `E` indexed by the oriented bonds `ij` of a locally finite graph
`G`, with `Q_{ij}(x, y) = Q_{ji}(y, x)` (Georgii (12.9)); the bond function `Q_b(σ) = Q_{ij}(σ_i,
    σ_j)`
for `b = {i, j}`, and the weight `∏_{b ∩ Λ ≠ ∅} Q_b(σ)` of (12.8). Nothing in this section uses the
tree property. -/

section TransferFamily

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- Georgii (12.9): a family of matrices indexed by oriented bonds with `Q_{ij}(x,y) = Q_{ji}(y,x)`
is a function `Q_b` of the unoriented bond `b = {i, j}` and the two spins on it. -/
def bondWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (σ : S → E) : Sym2 S → ℝ≥0∞ :=
  Sym2.lift ⟨fun i j ↦ Q i j (σ i) (σ j), fun i j ↦ hQ i j _ _⟩

omit [DecidableEq S] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
@[simp] lemma bondWeight_mk (hQ : ∀ i j x y, Q i j x y = Q j i y x) (σ : S → E) (i j : S) :
    bondWeight Q hQ σ s(i, j) = Q i j (σ i) (σ j) := rfl

omit [DecidableEq S] in
lemma measurable_bondWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (b : Sym2 S) :
    Measurable fun σ : S → E ↦ bondWeight Q hQ σ b :=
  Sym2.inductionOn b fun i j ↦ measurable_pair (Q i j) i j

/-- **Georgii (12.8) before normalisation.** The weight `∏_{b ∩ Λ ≠ ∅} Q_b(σ)` of the bonds
meeting `Λ`; for `Q_b = e^{-Φ_b}` this is the Boltzmann factor of a nearest-neighbour potential. -/
def transferWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) (Λ : Finset S) (σ : S → E) : ℝ≥0∞ :=
  ∏ b ∈ G.bondsOf Λ, bondWeight Q hQ σ b

variable {Q} (hQ : ∀ i j x y, Q i j x y = Q j i y x)

lemma measurable_transferWeight (Λ : Finset S) : Measurable (transferWeight G Q hQ Λ) :=
  Finset.measurable_prod _ fun b _ ↦ measurable_bondWeight Q hQ b

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

lemma transferWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (Λ : Finset S)
    (σ : S → E) : 0 < transferWeight G Q hQ Λ σ := by
  refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b hb ↦ ?_)
  have he := (SimpleGraph.mem_bondsOf.1 hb).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact (hpos (G.mem_edgeSet.1 he) _ _).ne'

lemma transferWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) (Λ : Finset S)
    (σ : S → E) : transferWeight G Q hQ Λ σ ≠ ⊤ := by
  refine ENNReal.prod_ne_top fun b hb ↦ ?_
  have he := (SimpleGraph.mem_bondsOf.1 hb).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact htop (G.mem_edgeSet.1 he) _ _

omit [DecidableEq S] in
/-- The bond weight of a bond depends only on the spins at its endpoints. -/
lemma bondWeight_congr {σ τ : S → E} {b : Sym2 S} (h : ∀ k ∈ b, σ k = τ k) :
    bondWeight Q hQ σ b = bondWeight Q hQ τ b := by
  revert h
  refine Sym2.inductionOn b fun i j h ↦ ?_
  rw [bondWeight_mk, bondWeight_mk, h i (Sym2.mem_mk_left i j), h j (Sym2.mem_mk_right i j)]

/-- The endpoints of a bond meeting `Λ` lie in `Λ ∪ ∂Λ`. -/
lemma mem_union_outerBoundary_of_mem_bondsOf {Λ : Finset S} {b : Sym2 S} (hb : b ∈ G.bondsOf Λ)
    {k : S} (hk : k ∈ b) : k ∈ Λ ∪ G.outerBoundary Λ := by
  obtain ⟨he, i, hi, hib⟩ := SimpleGraph.mem_bondsOf.1 hb
  by_cases hki : k = i
  · exact hki ▸ Finset.mem_union_left _ hi
  · have : b = s(i, k) := (Sym2.mem_and_mem_iff (Ne.symm hki)).1 ⟨hib, hk⟩
    rw [this, SimpleGraph.mem_edgeSet] at he
    exact G.mem_union_outerBoundary_of_adj hi he

/-- The transfer weight of `Λ` depends only on the spins in `Λ ∪ ∂Λ`. -/
lemma transferWeight_congr {Λ : Finset S} {σ τ : S → E}
    (h : ∀ k ∈ Λ ∪ G.outerBoundary Λ, σ k = τ k) :
    transferWeight G Q hQ Λ σ = transferWeight G Q hQ Λ τ :=
  Finset.prod_congr rfl fun _ hb ↦ bondWeight_congr hQ fun k hk ↦
    h k (mem_union_outerBoundary_of_mem_bondsOf G hb hk)

/-- The transfer weights form a pre-modification (Georgii (1.28)(5)): the weights of the bonds
not meeting `Λ₁` factor out. -/
lemma transferWeight_mul_comm_of_subset {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : S → E}
    (h : ∀ s ∉ Λ₁, ζ s = η s) :
    transferWeight G Q hQ Λ₂ ζ * transferWeight G Q hQ Λ₁ η
      = transferWeight G Q hQ Λ₁ ζ * transferWeight G Q hQ Λ₂ η := by
  have hsplit : ∀ ω : S → E, transferWeight G Q hQ Λ₂ ω
      = (∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ ω b)
        * transferWeight G Q hQ Λ₁ ω := fun ω ↦
    (Finset.prod_sdiff (SimpleGraph.bondsOf_mono hΛ)).symm
  have hdiff : (∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ ζ b)
      = ∏ b ∈ G.bondsOf Λ₂ \ G.bondsOf Λ₁, bondWeight Q hQ η b := by
    refine Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hQ fun k hk ↦ h k fun hkΛ ↦ ?_
    have hb' := Finset.mem_sdiff.1 hb
    exact hb'.2 (SimpleGraph.mem_bondsOf.2 ⟨(SimpleGraph.mem_bondsOf.1 hb'.1).1, k, hkΛ, hk⟩)
  rw [hsplit ζ, hsplit η, hdiff]
  ring

/-- The transfer weight of a singleton: the product over the neighbours. -/
lemma transferWeight_singleton (i : S) (σ : S → E) :
    transferWeight G Q hQ {i} σ = ∏ k ∈ G.neighborFinset i, Q i k (σ i) (σ k) := by
  rw [transferWeight, SimpleGraph.bondsOf_singleton, SimpleGraph.incidenceFinset_eq_image,
    Finset.prod_image fun _ _ _ _ h ↦ SimpleGraph.injective_mk_left i h]
  rfl

/-- The bonds at `i ∈ Λ` split off from the bonds meeting `Λ`: the remaining factor does not
depend on the spin at `i`. -/
lemma transferWeight_eq_mul_of_mem {Λ : Finset S} {i : S} (hi : i ∈ Λ) (σ : S → E) :
    transferWeight G Q hQ Λ σ
      = (∏ k ∈ G.neighborFinset i, Q i k (σ i) (σ k))
        * ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ σ b := by
  have hsub : G.incidenceFinset i ⊆ G.bondsOf Λ := by
    rw [← SimpleGraph.bondsOf_singleton (G := G)]
    exact SimpleGraph.bondsOf_mono (Finset.singleton_subset_iff.2 hi)
  rw [transferWeight, ← Finset.prod_sdiff hsub, mul_comm, ← transferWeight_singleton G hQ,
    transferWeight, SimpleGraph.bondsOf_singleton]

lemma prod_bondsOf_sdiff_incidenceFinset_update {Λ : Finset S} (i : S) (σ : S → E) (y : E) :
    ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ (Function.update σ i y) b
      = ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ σ b := by
  refine Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hQ fun k hk ↦
    Function.update_of_ne (fun hki ↦ ?_) _ _
  subst hki
  have hb' := Finset.mem_sdiff.1 hb
  exact hb'.2 ((G.mem_incidenceFinset _ _).2 ⟨(SimpleGraph.mem_bondsOf.1 hb'.1).1, hk⟩)

end TransferFamily

/-! ### Transfer families: positivity, finiteness and admissibility -/

section IsTransferFamily

variable (G : SimpleGraph S) [G.LocallyFinite]

/-- **Georgii's hypotheses on the transfer matrices of §12.1.** A family `Q_{ij}` of matrices on
the countable state space `E` indexed by the ordered pairs of sites which is symmetric in the sense
of (12.9), positive with finite entries along the bonds of `G`, and whose partition functions
`Z_Λ(ω) = ∑_{σ_Λ} ∏_{b ∩ Λ ≠ ∅} Q_b(σ_Λ ω_{Λᶜ})` are finite (λ-admissibility for counting measure).
On a finite state space the last condition is automatic (`isTransferFamily_of_finite`); Georgii
assumes `E` finite throughout Chapter 12. -/
structure IsTransferFamily (Q : S → S → E → E → ℝ≥0∞) : Prop where
  symm : ∀ i j x y, Q i j x y = Q j i y x
  pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y
  ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤
  sigmaFiniteLambdaZ_ne_top : ∀ (Λ : Finset S) (ω : S → E),
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q symm)
      Λ ω ≠ ⊤

variable {G} {Q : S → S → E → E → ℝ≥0∞}

lemma isPremodifier_transferWeight (hQ : ∀ i j x y, Q i j x y = Q j i y x) :
    Specification.IsPremodifier (transferWeight G Q hQ) where
  measurable := measurable_transferWeight G hQ
  comm_of_subset _ _ _ _ hΛ h := transferWeight_mul_comm_of_subset G hQ hΛ h

/-- On a finite state space every symmetric family of positive finite matrices is a transfer
family. -/
lemma isTransferFamily_of_finite [Finite E] (symm : ∀ i j x y, Q i j x y = Q j i y x)
    (pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) : IsTransferFamily G Q where
  symm := symm
  pos := pos
  ne_top := ne_top
  sigmaFiniteLambdaZ_ne_top := sigmaFiniteLambdaZ_count_ne_top_of_finite
    (isPremodifier_transferWeight symm) (transferWeight_ne_top G symm ne_top)

namespace IsTransferFamily

variable (hQ : IsTransferFamily G Q)
include hQ

lemma transferWeight_pos (Λ : Finset S) (σ : S → E) : 0 < transferWeight G Q hQ.symm Λ σ :=
  Tree.transferWeight_pos G hQ.symm hQ.pos Λ σ

lemma transferWeight_ne_top (Λ : Finset S) (σ : S → E) : transferWeight G Q hQ.symm Λ σ ≠ ⊤ :=
  Tree.transferWeight_ne_top G hQ.symm hQ.ne_top Λ σ

/-- A transfer family is admissible for counting measure. -/
theorem isSigmaFiniteLambdaAdmissible :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) Measure.count
      (transferWeight G Q hQ.symm) := fun Λ ω ↦
  ⟨sigmaFiniteLambdaZ_count_ne_zero (isPremodifier_transferWeight hQ.symm)
    (hQ.transferWeight_pos Λ ω).ne', hQ.sigmaFiniteLambdaZ_ne_top Λ ω⟩

end IsTransferFamily

end IsTransferFamily

/-! ### The specification `γ^Q`: Georgii (12.8) -/

section TransferSpecification

variable [Nonempty E] (G : SimpleGraph S) [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q)

/-- **Georgii's positive Markov specification (12.8).** The λ-specification, for counting measure
on the countable state space `E`, of the transfer weights `∏_{b ∩ Λ ≠ ∅} Q_b` of a transfer
family `Q` on the locally finite graph `G`. -/
def transferSpecification : Specification S E :=
  Specification.lambdaSpecification (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
    (isPremodifier_transferWeight hQ.symm) hQ.isSigmaFiniteLambdaAdmissible

lemma transferSpecification_apply (Λ : Finset S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    transferSpecification G hQ Λ ω A
      = (Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) Λ ω)⁻¹ * ∫⁻ ζ in A, transferWeight G Q hQ.symm Λ ζ ∂(λ₀ Λ
              ω) := by
  rw [transferSpecification, Specification.lambdaSpecification_apply]
  exact Specification.withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E)
    Measure.count (isPremodifier_transferWeight hQ.symm) hA ω

/-- **Georgii (12.8).** `γ_Λ(σ_Λ = ω_Λ | ω) = Z_Λ(ω)⁻¹ ∏_{b ∩ Λ ≠ ∅} Q_b(ω_b)`. -/
lemma transferSpecification_apply_cyl (Λ : Finset S) (ω : S → E) :
    transferSpecification G hQ Λ ω (cyl Λ ω)
      = transferWeight G Q hQ.symm Λ ω / Specification.sigmaFiniteLambdaZ (S := S) (E := E)
          Measure.count (transferWeight G Q hQ.symm) Λ ω := by
  rw [transferSpecification_apply G hQ Λ ω (measurableSet_cyl Λ ω),
    setLIntegral_lambdaCount_cyl Λ ω (measurable_transferWeight G hQ.symm Λ),
        ENNReal.div_eq_inv_mul]

omit [Nonempty E] in
/-- The partition function of a singleton: `Z_{i}(ω) = ∑_x ∏_{k ∈ ∂i} Q_{ik}(x, ω_k)`. -/
lemma sigmaFiniteLambdaZ_transferWeight_singleton (i : S) (ω : S → E) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        {i} ω
      = ∑' x, ∏ k ∈ G.neighborFinset i, Q i k x (ω k) := by
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount_singleton i ω
    (measurable_transferWeight G hQ.symm {i})]
  refine tsum_congr fun x ↦ ?_
  rw [transferWeight_singleton]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [Function.update_self, Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1
      hk)).symm]

omit [Nonempty E] in
/-- The singleton partition function depends only on the spins at the neighbours. -/
lemma sigmaFiniteLambdaZ_transferWeight_singleton_congr (i : S) {ω ζ : S → E}
    (h : ∀ k ∈ G.neighborFinset i, ω k = ζ k) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        {i} ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) {i} ζ := by
  rw [sigmaFiniteLambdaZ_transferWeight_singleton G hQ,
    sigmaFiniteLambdaZ_transferWeight_singleton G hQ]
  exact tsum_congr fun x ↦ Finset.prod_congr rfl fun k hk ↦ by rw [h k hk]

omit [Nonempty E] in
/-- The partition function `Z_Λ(ω)` depends only on the spins on `∂Λ`. -/
lemma sigmaFiniteLambdaZ_transferWeight_congr (Λ : Finset S) {ω ω' : S → E}
    (h : ∀ k ∈ G.outerBoundary Λ, ω k = ω' k) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count (transferWeight G Q hQ.symm)
        Λ ω
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
          (transferWeight G Q hQ.symm) Λ ω' := by
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ,
    lintegral_lambdaCount _ _ (measurable_transferWeight G hQ.symm Λ),
    lintegral_lambdaCount _ _ (measurable_transferWeight G hQ.symm Λ)]
  refine tsum_congr fun x ↦ transferWeight_congr G hQ.symm fun k hk ↦ ?_
  rcases Finset.mem_union.1 hk with hkΛ | hkΛ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ), juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]
  · have hkΛ' : k ∉ (Λ : Set S) := by simpa using G.notMem_of_mem_outerBoundary hkΛ
    rw [juxt_apply_of_not_mem hkΛ', juxt_apply_of_not_mem hkΛ', h k hkΛ]

/-- **Georgii (12.8) on the cylinder `{σ_{Λ ∪ ∂Λ} = ζ}`.** `γ_Λ(σ_{Λ ∪ ∂Λ} = ζ | ω)` is
`∏_{b ∩ Λ ≠ ∅} Q_b(ζ) / Z_Λ(ζ)` if `ω` agrees with `ζ` on `∂Λ` and `0` otherwise. -/
theorem transferSpecification_apply_cyl_union_outerBoundary (Λ : Finset S) (ζ ω : S → E) :
    transferSpecification G hQ Λ ω (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (cyl (G.outerBoundary Λ) ζ).indicator
          (fun _ ↦ transferWeight G Q hQ.symm Λ ζ
            / Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
                (transferWeight G Q hQ.symm) Λ ζ) ω := by
  rw [transferSpecification_apply G hQ Λ ω (measurableSet_cyl _ _),
    setLIntegral_lambdaCount_cyl_of_subset Finset.subset_union_left ω ζ
      (measurable_transferWeight G hQ.symm Λ),
    Finset.union_sdiff_cancel_left (G.disjoint_outerBoundary Λ)]
  by_cases hω : ω ∈ cyl (G.outerBoundary Λ) ζ
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, ENNReal.div_eq_inv_mul,
      sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ (ω' := ζ) (mem_cyl.1 hω),
      transferWeight_congr G hQ.symm (τ := ζ) fun k hk ↦ ?_]
    rcases Finset.mem_union.1 hk with hkΛ | hkΛ
    · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]; rfl
    · rw [juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by
        simpa using G.notMem_of_mem_outerBoundary hkΛ)]
      exact mem_cyl.1 hω k hkΛ
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, mul_zero]

/-- The singleton kernel of `γ^Q` on a cylinder containing the site `i` and its neighbours:
`γ_{i}(σ_H = ζ_H | ω)` is `∏_{k ∈ ∂i} Q_{ik}(ζ_i, ζ_k) / Z_{i}(ζ)` if `ω` agrees with `ζ` on
`H \ {i}` and `0` otherwise. -/
theorem transferSpecification_singleton_apply_cyl {H : Finset S} {i : S} (hi : i ∈ H)
    (hH : G.neighborFinset i ⊆ H) (ζ ω : S → E) :
    transferSpecification G hQ {i} ω (cyl H ζ)
      = (cyl (H.erase i) ζ).indicator
          (fun _ ↦ (∏ k ∈ G.neighborFinset i, Q i k (ζ i) (ζ k))
            / Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
                (transferWeight G Q hQ.symm) {i} ζ) ω := by
  rw [transferSpecification_apply G hQ {i} ω (measurableSet_cyl H ζ),
    ← lintegral_indicator (measurableSet_cyl H ζ),
    lintegral_lambdaCount_singleton i ω
      ((measurable_transferWeight G hQ.symm {i}).indicator (measurableSet_cyl H ζ))]
  by_cases hω : ω ∈ cyl (H.erase i) ζ
  · have hωζ : ∀ k ∈ G.neighborFinset i, ω k = ζ k := fun k hk ↦
      mem_cyl.1 hω k (Finset.mem_erase.2 ⟨G.ne_of_adj ((G.mem_neighborFinset i k).1 hk) |>.symm,
        hH hk⟩)
    rw [Set.indicator_of_mem hω, tsum_eq_single (ζ i) fun y hy ↦ ?_,
      sigmaFiniteLambdaZ_transferWeight_singleton_congr G hQ i hωζ]
    · have hmem : Function.update ω i (ζ i) ∈ cyl H ζ := by
        refine mem_cyl.2 fun k hk ↦ ?_
        by_cases hki : k = i
        · subst hki; exact Function.update_self ..
        · rw [Function.update_of_ne hki]
          exact mem_cyl.1 hω k (Finset.mem_erase.2 ⟨hki, hk⟩)
      rw [Set.indicator_of_mem hmem, transferWeight_singleton, ENNReal.div_eq_inv_mul]
      congr 1
      refine Finset.prod_congr rfl fun k hk ↦ ?_
      rw [Function.update_self,
        Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1 hk)).symm, hωζ k hk]
    · refine Set.indicator_of_notMem (fun h ↦ hy ?_) _
      have := mem_cyl.1 h i hi
      rwa [Function.update_self] at this
  · rw [Set.indicator_of_notMem hω]
    have : ∀ y, (cyl H ζ).indicator (transferWeight G Q hQ.symm {i}) (Function.update ω i y) = 0 :=
      fun y ↦ Set.indicator_of_notMem (fun h ↦ hω (mem_cyl.2 fun k hk ↦ by
        have hki := (Finset.mem_erase.1 hk).1
        have := mem_cyl.1 h k (Finset.mem_erase.1 hk).2
        rwa [Function.update_of_ne hki] at this)) _
    simp [this]

end TransferSpecification


/-! ## Boundary laws: Georgii Definition (12.10) -/

section BoundaryLaw

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (ℓ : S → S → E → ℝ≥0∞)

/-- **Georgii Definition (12.10).** A family `ℓ_{ij}`, indexed by the oriented bonds `ij` of `G`, of
positive finite row vectors on `E` such that for every oriented bond `ij` there is a constant
`c_{ij} > 0` with `ℓ_{ij}(x) = c_{ij} ∏_{k ∈ ∂i \ {j}} (ℓ_{ki} Q_{ki})(x)`, where
`(ℓ_{ki} Q_{ki})(x) = ∑_y ℓ_{ki}(y) Q_{ki}(y, x)` (the row vector `ℓ_{ki}` times the matrix
`Q_{ki}`, i.e. `(ℓ_{ki} · count).bind (ofMatrix Q_{ki})` evaluated at `{x}`).

The last field, finiteness of the total masses `∑_x ∏_{k ∈ ∂i} (ℓ_{ki} Q_{ki})(x)` of the singleton
volumes, is automatic for a finite state space (`IsBoundaryLaw.of_finite`), which is Georgii's
standing assumption in Chapter 12; for a countable `E` it is the normalisability of the measure
(12.13), the tree analogue of `ℓ_i r_i = 1` in Definition (11.8). -/
structure IsBoundaryLaw : Prop where
  pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x
  ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤
  consistent : ∀ ⦃i j⦄, G.Adj i j → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x,
    ℓ i j x = c * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x
  mass_ne_top : ∀ i, ∑' x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x ≠ ⊤

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a finite state space the mass condition of `IsBoundaryLaw` is automatic. -/
lemma IsBoundaryLaw.of_finite [Finite E] (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤)
    (pos : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x)
    (ne_top : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤)
    (consistent : ∀ ⦃i j⦄, G.Adj i j → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x,
      ℓ i j x = c * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) :
    IsBoundaryLaw G Q ℓ where
  pos := pos
  ne_top := ne_top
  consistent := consistent
  mass_ne_top i := by
    cases nonempty_fintype E
    simp only [tsum_fintype]
    refine ENNReal.sum_ne_top.2 fun x _ ↦ ENNReal.prod_ne_top fun k hk ↦ ?_
    have hik := (G.mem_neighborFinset i k).1 hk
    exact ENNReal.sum_ne_top.2 fun y _ ↦ ENNReal.mul_ne_top (ne_top hik.symm y) (hQ hik.symm y x)

omit [DecidableEq S] in
/-- `ℓ_{ki} Q_{ki}` as a `Measure.bind`: the row vector `ℓ_{ki}` acting on the kernel of the
matrix `Q_{ki}`. -/
lemma bind_ofMatrix_apply_singleton (k i : S) (x : E) :
    ((Measure.count.withDensity (ℓ k i)).bind (Kernel.ofMatrix (Q k i))) {x}
      = ∑' y, ℓ k i y * Q k i y x := by
  rw [Kernel.bind_ofMatrix_apply_singleton]
  simp_rw [Measure.count_withDensity_apply_singleton]

namespace IsBoundaryLaw

variable {G Q ℓ} (hℓ : IsBoundaryLaw G Q ℓ)
include hℓ

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The row-vector products `ℓ_{ki} Q_{ki}` along a bond are positive. -/
lemma tsum_mul_pos (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {k i : S} (hki : G.Adj k i)
    (x : E) : 0 < ∑' y, ℓ k i y * Q k i y x :=
  (ENNReal.mul_pos (hℓ.pos hki x).ne' (hQ hki x x).ne').trans_le (ENNReal.le_tsum x)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The row-vector products `ℓ_{ki} Q_{ki}` along a bond are finite: they are factors of the
finite `ℓ_{ij}`, `j` any other neighbour... or, if `i` has no other neighbour, of `ℓ_{ij}` for
`j = k` read through the bond `ki`. -/
lemma tsum_mul_ne_top (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {k i : S}
    (hki : G.Adj k i) (x : E) : ∑' y, ℓ k i y * Q k i y x ≠ ⊤ := by
  classical
  -- `ℓ_{ki} Q_{ki}` is one of the positive factors in the consistency equation for the
  -- oriented bond `i j` with `j = ` any neighbour of `i` other than `k`; if `k` is the only
  -- neighbour of `i`, use the bond `i k`... whose product is empty. In that case use the mass
  -- condition at `i` instead.
  by_cases hex : ∃ j ∈ G.neighborFinset i, j ≠ k
  · obtain ⟨j, hj, hjk⟩ := hex
    have hij := (G.mem_neighborFinset i j).1 hj
    obtain ⟨c, hc0, -, hc⟩ := hℓ.consistent hij
    have hfin : c * ∏ m ∈ (G.neighborFinset i).erase j, ∑' y, ℓ m i y * Q m i y x ≠ ⊤ :=
      hc x ▸ hℓ.ne_top hij x
    have hprod : ∏ m ∈ (G.neighborFinset i).erase j, ∑' y, ℓ m i y * Q m i y x ≠ ⊤ :=
      fun h ↦ hfin (by rw [h, ENNReal.mul_top hc0])
    have hk : k ∈ (G.neighborFinset i).erase j :=
      Finset.mem_erase.2 ⟨hjk.symm, (G.mem_neighborFinset i k).2 hki.symm⟩
    intro htop
    apply hprod
    rw [← Finset.mul_prod_erase _ _ hk, htop, ENNReal.top_mul]
    exact Finset.prod_ne_zero_iff.2 fun m hm ↦ (hℓ.tsum_mul_pos hQ
      (((G.mem_neighborFinset i m).1
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))).symm) x).ne'
  · push Not at hex
    have hnb : G.neighborFinset i = {k} := by
      ext m
      simp only [Finset.mem_singleton]
      exact ⟨fun hm ↦ hex m hm, fun hm ↦ hm ▸ (G.mem_neighborFinset i k).2 hki.symm⟩
    have := hℓ.mass_ne_top i
    rw [hnb] at this
    simp only [Finset.prod_singleton] at this
    exact ne_top_of_le_ne_top this (ENNReal.le_tsum x)

end IsBoundaryLaw

end BoundaryLaw


/-! ## The weights (12.13) and their consistency (12.14) -/

section BoundaryLawWeight

variable (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (hs : ∀ i j x y, Q i j x y = Q j i y x) (ℓ : S → S → E → ℝ≥0∞)

/-- The right-hand side of Georgii (12.13) before normalisation: the weight
`∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b)` of a configuration on `Λ ∪ ∂Λ`. -/
def boundaryLawWeight (Λ : Finset S) (ζ : S → E) : ℝ≥0∞ :=
  (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k)) * transferWeight G Q hs Λ ζ

lemma measurable_boundaryLawWeight (Λ : Finset S) : Measurable (boundaryLawWeight G Q hs ℓ Λ) :=
  (Finset.measurable_prod _ fun k _ ↦ measurable_coord (ℓ k (G.anchor Λ k)) k).mul
    (measurable_transferWeight G hs Λ)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The weight of `Λ` depends only on the spins in `Λ ∪ ∂Λ`. -/
lemma boundaryLawWeight_congr {Λ : Finset S} {ζ ζ' : S → E}
    (h : ∀ k ∈ Λ ∪ G.outerBoundary Λ, ζ k = ζ' k) :
    boundaryLawWeight G Q hs ℓ Λ ζ = boundaryLawWeight G Q hs ℓ Λ ζ' := by
  rw [boundaryLawWeight, boundaryLawWeight, transferWeight_congr G hs h]
  congr 1
  exact Finset.prod_congr rfl fun k hk ↦ by rw [h k (Finset.mem_union_right _ hk)]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundaryLawWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x) (Λ : Finset S) (ζ : S → E) :
    0 < boundaryLawWeight G Q hs ℓ Λ ζ :=
  ENNReal.mul_pos (Finset.prod_ne_zero_iff.2 fun _ hk ↦ (hℓ (G.adj_anchor hk) _).ne')
    (transferWeight_pos G hs hpos Λ ζ).ne'

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundaryLawWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x ≠ ⊤) (Λ : Finset S) (ζ : S → E) :
    boundaryLawWeight G Q hs ℓ Λ ζ ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ hk ↦ hℓ (G.adj_anchor hk) _)
    (transferWeight_ne_top G hs htop Λ ζ)

variable {G Q ℓ}

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The algebra of Georgii's consistency computation (12.14): for a tree, `Λ` connected,
`i ∈ ∂Λ`, `j = i_Λ` and `V = ∂i \ {j}`, the weight of `Λ ∪ {i}` at a configuration agreeing with
`ζ` off `V` is `∏_{k ∈ ∂Λ \ {i}} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ) ∏_{k ∈ V} ℓ_{ki}(ξ_k)
    Q_{ki}(ξ_k, ζ_i)`. -/
lemma boundaryLawWeight_insert_eq (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) {ζ ξ : S → E}
    (hξ : ∀ k ∉ (G.neighborFinset i).erase (G.anchor Λ i), ξ k = ζ k) :
    boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
      = ((∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
          * transferWeight G Q hs Λ ζ)
        * ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ℓ k i (ξ k) * Q k i (ξ k) (ζ i) := by
  set V := (G.neighborFinset i).erase (G.anchor Λ i) with hV
  have hdisj := hG.disjoint_union_outerBoundary_erase hΛ hi
  have hξH : ∀ k ∈ Λ ∪ G.outerBoundary Λ, ξ k = ζ k := fun k hk ↦
    hξ k (Finset.disjoint_left.1 hdisj hk)
  have hξi : ξ i = ζ i := hξH i (Finset.mem_union_right _ hi)
  rw [boundaryLawWeight, hG.outerBoundary_insert_eq hΛ hi,
    Finset.prod_union (hG.disjoint_outerBoundary_erase hΛ hi), transferWeight,
    SimpleGraph.bondsOf_insert_eq_of_mem_outerBoundary hi,
    Finset.prod_union (hG.disjoint_bondsOf_image hΛ hi),
    Finset.prod_image fun _ _ _ _ h ↦ SimpleGraph.injective_mk_left i h]
  have h1 : ∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor (insert i Λ) k) (ξ k)
      = ∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [hG.anchor_insert_of_mem_erase hΛ hi hk,
        hξH k (Finset.mem_union_right _ (Finset.mem_of_mem_erase hk))]
  have h2 : ∏ k ∈ V, ℓ k (G.anchor (insert i Λ) k) (ξ k) = ∏ k ∈ V, ℓ k i (ξ k) :=
    Finset.prod_congr rfl fun k hk ↦ by rw [hG.anchor_insert_of_adj hΛ hi hk]
  have h3 : ∏ b ∈ G.bondsOf Λ, bondWeight Q hs ξ b = transferWeight G Q hs Λ ζ :=
    transferWeight_congr G hs hξH
  have h4 : ∏ k ∈ V, bondWeight Q hs ξ s(i, k) = ∏ k ∈ V, Q k i (ξ k) (ζ i) :=
    Finset.prod_congr rfl fun k _ ↦ by rw [bondWeight_mk, hs, hξi]
  rw [h1, h2, h3, h4, Finset.prod_mul_distrib]
  ring

/-- Integrating the weight of `Λ ∪ {i}` over the spins in `∂i \ {i_Λ}`, before using the
boundary-law equation: the row-vector products `ℓ_{ki} Q_{ki}` appear. -/
lemma lintegral_boundaryLawWeight_insert (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) (ζ : S → E) :
    ∫⁻ ξ, boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
        ∂(λ₀ ((G.neighborFinset i).erase (G.anchor Λ i)) ζ)
      = ((∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
          * transferWeight G Q hs Λ ζ)
        * ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ∑' y, ℓ k i y * Q k i y (ζ i) := by
  set V := (G.neighborFinset i).erase (G.anchor Λ i) with hV
  set A := (∏ k ∈ (G.outerBoundary Λ).erase i, ℓ k (G.anchor Λ k) (ζ k))
    * transferWeight G Q hs Λ ζ with hA
  rw [lintegral_lambdaCount_congr V ζ (measurable_boundaryLawWeight G Q hs ℓ _)
    (measurable_const.mul (Finset.measurable_prod _ fun k _ ↦
      measurable_coord (fun y ↦ ℓ k i y * Q k i y (ζ i)) k))
    (G := fun ξ ↦ A * ∏ k ∈ V, ℓ k i (ξ k) * Q k i (ξ k) (ζ i))
    fun ξ hξ ↦ boundaryLawWeight_insert_eq hs hG hΛ hi hξ,
    lintegral_const_mul _ (Finset.measurable_prod _ fun k _ ↦
      measurable_coord (fun y ↦ ℓ k i y * Q k i y (ζ i)) k),
    lintegral_lambdaCount_prod V ζ (fun k y ↦ ℓ k i y * Q k i y (ζ i))]

/-- **Georgii (12.14), one step.** For a tree, `Λ` connected and `i ∈ ∂Λ` with `j = i_Λ`,
integrating the weight of `Λ ∪ {i}` over the spins in `∂i \ {j}` gives `c_{ij}⁻¹` times the
weight of `Λ`. -/
lemma IsBoundaryLaw.exists_lintegral_boundaryLawWeight_insert (hℓ : IsBoundaryLaw G Q ℓ)
    (hG : G.IsAcyclic) {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S}
    (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ ζ : S → E,
      ∫⁻ ξ, boundaryLawWeight G Q hs ℓ (insert i Λ) ξ
          ∂(λ₀ ((G.neighborFinset i).erase (G.anchor Λ i)) ζ)
        = c⁻¹ * boundaryLawWeight G Q hs ℓ Λ ζ := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent (G.adj_anchor hi)
  refine ⟨c, hc0, hct, fun ζ ↦ ?_⟩
  rw [lintegral_boundaryLawWeight_insert hs hG hΛ hi ζ]
  have hℓi : ∏ k ∈ (G.neighborFinset i).erase (G.anchor Λ i), ∑' y, ℓ k i y * Q k i y (ζ i)
      = c⁻¹ * ℓ i (G.anchor Λ i) (ζ i) := by
    rw [hc (ζ i), ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hℓi, boundaryLawWeight, ← Finset.mul_prod_erase _ _ hi]
  ring

end BoundaryLawWeight


/-! ## The measure (12.13) of a boundary law -/

section VolumeLaw

variable [Nonempty E] (G : SimpleGraph S) [G.LocallyFinite] (Q : S → S → E → E → ℝ≥0∞)
  (hs : ∀ i j x y, Q i j x y = Q j i y x) (ℓ : S → S → E → ℝ≥0∞)

/-- A fixed configuration, the boundary condition of the reference kernel `λ_{Λ ∪ ∂Λ}`; the
marginals of `volumeLaw` on `Λ ∪ ∂Λ` do not depend on it. -/
def baseConfig : S → E := fun _ ↦ Classical.arbitrary E

/-- The measure `ρ_Λ λ_{Λ ∪ ∂Λ}(·|ω₀)` on `S → E` with the density (12.13) on `Λ ∪ ∂Λ` with
respect to counting measure, before normalisation. -/
def volumeLaw (Λ : Finset S) : Measure (S → E) :=
  (λ₀ (Λ ∪ G.outerBoundary Λ) (baseConfig (S := S) (E := E))).withDensity
    (boundaryLawWeight G Q hs ℓ Λ)

/-- The normalised measure `z_Λ ρ_Λ λ_{Λ ∪ ∂Λ}` of (12.13). -/
def normalizedVolumeLaw (Λ : Finset S) : Measure (S → E) :=
  (volumeLaw G Q hs ℓ Λ Set.univ)⁻¹ • volumeLaw G Q hs ℓ Λ

lemma volumeLaw_univ_eq_lintegral (Λ : Finset S) :
    volumeLaw G Q hs ℓ Λ Set.univ
      = ∫⁻ ζ, boundaryLawWeight G Q hs ℓ Λ ζ
          ∂(λ₀ (Λ ∪ G.outerBoundary Λ) (baseConfig (S := S) (E := E))) := by
  rw [volumeLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The total mass of `volumeLaw Λ` is positive. -/
lemma volumeLaw_univ_ne_zero (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y)
    (hℓ : ∀ ⦃i j⦄, G.Adj i j → ∀ x, 0 < ℓ i j x) (Λ : Finset S) :
    volumeLaw G Q hs ℓ Λ Set.univ ≠ 0 := by
  rw [volumeLaw_univ_eq_lintegral, lintegral_lambdaCount _ _ (measurable_boundaryLawWeight G Q hs
      ℓ Λ)]
  refine ne_of_gt ((boundaryLawWeight_pos G Q hs ℓ hpos hℓ Λ
    (juxt ((Λ ∪ G.outerBoundary Λ : Finset S) : Set S) (baseConfig (S := S) (E := E))
      (fun _ ↦ Classical.arbitrary E))).trans_le (ENNReal.le_tsum _))

/-- The cylinder probabilities of `volumeLaw Λ`: the weight (12.13) before normalisation. -/
lemma volumeLaw_cyl (Λ : Finset S) (ζ : S → E) :
    volumeLaw G Q hs ℓ Λ (cyl (Λ ∪ G.outerBoundary Λ) ζ) = boundaryLawWeight G Q hs ℓ Λ ζ := by
  rw [volumeLaw, withDensity_apply _ (measurableSet_cyl _ _),
    setLIntegral_lambdaCount_cyl' _ _ _ (measurable_boundaryLawWeight G Q hs ℓ Λ)]
  exact boundaryLawWeight_congr G Q hs ℓ fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _

lemma normalizedVolumeLaw_cyl (Λ : Finset S) (ζ : S → E) :
    normalizedVolumeLaw G Q hs ℓ Λ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (volumeLaw G Q hs ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hs ℓ Λ ζ := by
  rw [normalizedVolumeLaw, Measure.smul_apply, smul_eq_mul, volumeLaw_cyl]

lemma normalizedVolumeLaw_univ {Λ : Finset S} (h0 : volumeLaw G Q hs ℓ Λ Set.univ ≠ 0)
    (htop : volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤) :
    normalizedVolumeLaw G Q hs ℓ Λ Set.univ = 1 := by
  rw [normalizedVolumeLaw, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The mass of a singleton volume, in terms of the row-vector products `ℓ_{ki} Q_{ki}`. -/
lemma volumeLaw_singleton_univ (i : S) :
    volumeLaw G Q hs ℓ {i} Set.univ
      = ∑' x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x := by
  have hdisj : Disjoint ({i} : Finset S) (G.outerBoundary {i}) := G.disjoint_outerBoundary _
  rw [volumeLaw_univ_eq_lintegral, lintegral_lambdaCount_union hdisj _
    (measurable_boundaryLawWeight G Q hs ℓ {i}),
    lintegral_lambdaCount_singleton i _ (measurable_lintegral_lambdaCount _
      (measurable_boundaryLawWeight G Q hs ℓ {i}))]
  refine tsum_congr fun x ↦ ?_
  rw [SimpleGraph.outerBoundary_singleton, ← lintegral_lambdaCount_prod (G.neighborFinset i) _
    (fun k y ↦ ℓ k i y * Q k i y x)]
  refine lintegral_lambdaCount_congr _ _ (measurable_boundaryLawWeight G Q hs ℓ {i})
    (Finset.measurable_prod _ fun k _ ↦ measurable_coord (fun y ↦ ℓ k i y * Q k i y x) k)
    fun ξ hξ ↦ ?_
  have hξi : ξ i = x := by
    rw [hξ i (fun h ↦ G.irrefl ((G.mem_neighborFinset i i).1 h)), Function.update_self]
  rw [boundaryLawWeight, transferWeight_singleton, SimpleGraph.outerBoundary_singleton,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k hk ↦ ?_
  rw [SimpleGraph.anchor_singleton (SimpleGraph.outerBoundary_singleton (G := G) i ▸ hk), hs, hξi]

variable {G Q ℓ}

/-- The mass of a singleton volume is finite for a boundary law. -/
lemma IsBoundaryLaw.volumeLaw_singleton_univ_ne_top (hℓ : IsBoundaryLaw G Q ℓ) (i : S) :
    volumeLaw G Q hs ℓ {i} Set.univ ≠ ⊤ := by
  rw [volumeLaw_singleton_univ]
  exact hℓ.mass_ne_top i

/-- **Georgii (12.14), one step, in measure form.** For a tree, `Λ` connected and `i ∈ ∂Λ`, the
marginal of `volumeLaw (Λ ∪ {i})` on `Λ ∪ ∂Λ` is `c_{ij}⁻¹` times `volumeLaw Λ`. -/
lemma IsBoundaryLaw.exists_volumeLaw_insert_map_restrict (hℓ : IsBoundaryLaw G Q ℓ)
    (hG : G.IsAcyclic) {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S}
    (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (volumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
        = c⁻¹ • (volumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.exists_lintegral_boundaryLawWeight_insert hs hG hΛ hi
  refine ⟨c, hc0, hct, ?_⟩
  rw [volumeLaw, volumeLaw, hG.insert_union_outerBoundary_eq hΛ hi,
    map_restrict_withDensity_union (hG.disjoint_union_outerBoundary_erase hΛ hi) _
      (measurable_boundaryLawWeight G Q hs ℓ _)]
  simp_rw [hc]
  rw [← Measure.map_smul, ← withDensity_smul _ (measurable_boundaryLawWeight G Q hs ℓ Λ)]
  rfl

lemma IsBoundaryLaw.exists_volumeLaw_insert_univ (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      volumeLaw G Q hs ℓ (insert i Λ) Set.univ = c⁻¹ * volumeLaw G Q hs ℓ Λ Set.univ ∧
      (volumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
        = c⁻¹ • (volumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.exists_volumeLaw_insert_map_restrict hs hG hΛ hi
  refine ⟨c, hc0, hct, ?_, hc⟩
  have := congrArg (fun μ : Measure ((Λ ∪ G.outerBoundary Λ : Finset S) → E) ↦ μ Set.univ) hc
  simpa only [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
    MeasurableSet.univ, Set.preimage_univ, Measure.smul_apply, smul_eq_mul] using this

/-- The normalised measures (12.13) are consistent under adding a boundary vertex. -/
lemma IsBoundaryLaw.normalizedVolumeLaw_insert_map_restrict (hℓ : IsBoundaryLaw G Q ℓ)
    (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {i : S} (hi : i ∈ G.outerBoundary Λ) :
    (normalizedVolumeLaw G Q hs ℓ (insert i Λ)).map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  obtain ⟨c, hc0, hct, hmass, hmap⟩ := hℓ.exists_volumeLaw_insert_univ hs hG hΛ hi
  have h0 := volumeLaw_univ_ne_zero G Q hs ℓ hQ hℓ.pos Λ
  rw [normalizedVolumeLaw, normalizedVolumeLaw, Measure.map_smul, Measure.map_smul, hmap, hmass,
    smul_smul, ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hct)) (Or.inl (ENNReal.inv_ne_top.2
        hc0)),
    inv_inv, mul_right_comm, ENNReal.mul_inv_cancel hc0 hct, one_mul]

omit [DecidableEq S] [G.LocallyFinite] [Nonempty E] in
lemma connected_induce_singleton (i : S) : (G.induce (({i} : Finset S) : Set S)).Connected := by
  rw [SimpleGraph.connected_induce_iff_forall_exists_walk]
  refine ⟨⟨i, by simp⟩, fun u hu v hv ↦ ?_⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hv
  subst hu; subst hv
  exact ⟨SimpleGraph.Walk.nil, fun x hx ↦ by simpa using hx⟩

/-- The mass of a connected volume is finite for a boundary law on a tree. -/
lemma IsBoundaryLaw.volumeLaw_univ_ne_top (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) :
    volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤ := by
  obtain ⟨o, ho⟩ := hΛ.induce_nonempty
  refine SimpleGraph.connected_induction (P := fun Λ ↦ volumeLaw G Q hs ℓ Λ Set.univ ≠ ⊤)
    (connected_induce_singleton o) hΛ (Finset.singleton_subset_iff.2 (Finset.mem_coe.1 ho))
    (hℓ.volumeLaw_singleton_univ_ne_top hs o) fun Λ' hΛ' _ _ i _ hi hP ↦ ?_
  obtain ⟨c, hc0, -, hmass, -⟩ := hℓ.exists_volumeLaw_insert_univ hs hG hΛ' hi
  rw [hmass]
  exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hc0) hP

/-- **Georgii (12.14).** For connected `Λ ⊆ Δ` in a tree, the marginals on `Λ ∪ ∂Λ` of the
normalised measures (12.13) of `Δ` and of `Λ` coincide. -/
theorem IsBoundaryLaw.normalizedVolumeLaw_map_restrict_eq (hℓ : IsBoundaryLaw G Q ℓ)
    (hQ : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (hG : G.IsAcyclic) {Λ Δ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (hΔ : (G.induce (Δ : Set S)).Connected)
    (hΛΔ : Λ ⊆ Δ) :
    (normalizedVolumeLaw G Q hs ℓ Δ).map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict := by
  refine SimpleGraph.connected_induction (P := fun Λ' ↦
    (normalizedVolumeLaw G Q hs ℓ Λ').map (Λ ∪ G.outerBoundary Λ).restrict
      = (normalizedVolumeLaw G Q hs ℓ Λ).map (Λ ∪ G.outerBoundary Λ).restrict)
    hΛ hΔ hΛΔ rfl fun Λ' hΛ' hΛΛ' _ i _ hi hP ↦ ?_
  rw [← hP]
  exact map_restrict_eq_of_subset (SimpleGraph.union_outerBoundary_mono hΛΛ')
    (hℓ.normalizedVolumeLaw_insert_map_restrict hs hQ hG hΛ' hi)

end VolumeLaw

/-! ### Kolmogorov extension: the measure of a boundary law -/

section BoundaryLawMeasure

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {ℓ : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

/-- A root of the tree, used to build connected hulls of finite volumes. -/
def root (hG : G.IsTree) : S := hG.connected.nonempty.some

variable (ℓ) in
/-- The finite-dimensional distributions of a boundary law: the marginal on `Λ` of the normalised
measure (12.13) of the connected hull of `Λ`. -/
def boundaryLawFDD (Λ : Finset S) : Measure (Λ → E) :=
  (normalizedVolumeLaw G Q hQ.symm ℓ (SimpleGraph.hull hG.connected (root hG) Λ)).map Λ.restrict

include hℓ

/-- The marginal on `Λ` of the normalised measure of any connected `Δ` with `Λ ⊆ Δ ∪ ∂Δ` is the
finite-dimensional distribution on `Λ`. -/
lemma IsBoundaryLaw.boundaryLawFDD_eq {Λ Δ : Finset S} (hΔ : (G.induce (Δ : Set S)).Connected)
    (hΛΔ : Λ ⊆ Δ ∪ G.outerBoundary Δ) :
    boundaryLawFDD hQ ℓ hG Λ = (normalizedVolumeLaw G Q hQ.symm ℓ Δ).map Λ.restrict := by
  set H₁ := SimpleGraph.hull hG.connected (root hG) Λ with hH₁
  set H₂ := SimpleGraph.hull hG.connected (root hG) (Λ ∪ Δ) with hH₂
  have h1 := hℓ.normalizedVolumeLaw_map_restrict_eq hQ.symm hQ.pos hG.isAcyclic
    (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ)
    (SimpleGraph.connected_induce_hull hG.connected (root hG) (Λ ∪ Δ))
    (SimpleGraph.hull_mono _ _ Finset.subset_union_left)
  have h2 := hℓ.normalizedVolumeLaw_map_restrict_eq hQ.symm hQ.pos hG.isAcyclic hΔ
    (SimpleGraph.connected_induce_hull hG.connected (root hG) (Λ ∪ Δ))
    (Finset.subset_union_right.trans (SimpleGraph.subset_hull _ _ _))
  rw [boundaryLawFDD, ← map_restrict_eq_of_subset
    ((SimpleGraph.subset_hull hG.connected (root hG) Λ).trans Finset.subset_union_left) h1,
    map_restrict_eq_of_subset hΛΔ h2]

lemma IsBoundaryLaw.isProjectiveMeasureFamily_boundaryLawFDD :
    IsProjectiveMeasureFamily (α := fun _ : S ↦ E) (boundaryLawFDD hQ ℓ hG) := by
  intro I J hJI
  rw [hℓ.boundaryLawFDD_eq hQ hG (SimpleGraph.connected_induce_hull hG.connected (root hG) I)
    ((hJI.trans (SimpleGraph.subset_hull _ _ I)).trans Finset.subset_union_left),
    boundaryLawFDD, Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : S ↦ E) hJI)
      (Finset.measurable_restrict (X := fun _ : S ↦ E) I), Finset.restrict₂_comp_restrict]

lemma IsBoundaryLaw.isProbabilityMeasure_boundaryLawFDD (Λ : Finset S) :
    IsProbabilityMeasure (boundaryLawFDD hQ ℓ hG Λ) := by
  constructor
  rw [boundaryLawFDD, Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) Λ)
    MeasurableSet.univ, Set.preimage_univ]
  exact normalizedVolumeLaw_univ G Q hQ.symm ℓ (volumeLaw_univ_ne_zero G Q hQ.symm ℓ hQ.pos
      hℓ.pos _)
    (hℓ.volumeLaw_univ_ne_top hQ.symm hG.isAcyclic
      (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ))

lemma IsBoundaryLaw.exists_isProjectiveLimit_boundaryLawFDD :
    ∃ μ : Measure (S → E), IsProjectiveLimit μ (boundaryLawFDD hQ ℓ hG) := by
  have : ∀ Λ, IsFiniteMeasure (boundaryLawFDD hQ ℓ hG Λ) := fun Λ ↦ by
    have := hℓ.isProbabilityMeasure_boundaryLawFDD hQ hG Λ
    infer_instance
  exact exists_isProjectiveLimit_of_standardBorel (hℓ.isProjectiveMeasureFamily_boundaryLawFDD hQ
      hG)

/-- **Georgii (12.12)(a), the measure.** The probability measure `μ` on `E^S` with the cylinder
probabilities (12.13), obtained from a boundary law on a tree by Kolmogorov's extension theorem. -/
def boundaryLawMeasure : Measure (S → E) :=
  (hℓ.exists_isProjectiveLimit_boundaryLawFDD hQ hG).choose

lemma IsBoundaryLaw.isProjectiveLimit_boundaryLawMeasure :
    IsProjectiveLimit (boundaryLawMeasure hQ hℓ hG) (boundaryLawFDD hQ ℓ hG) :=
  (hℓ.exists_isProjectiveLimit_boundaryLawFDD hQ hG).choose_spec

instance isProbabilityMeasure_boundaryLawMeasure :
    IsProbabilityMeasure (boundaryLawMeasure hQ hℓ hG) := by
  constructor
  have h := hℓ.isProjectiveLimit_boundaryLawMeasure hQ hG (∅ : Finset S)
  have := hℓ.isProbabilityMeasure_boundaryLawFDD hQ hG (∅ : Finset S)
  calc boundaryLawMeasure hQ hℓ hG Set.univ
      = ((boundaryLawMeasure hQ hℓ hG).map (∅ : Finset S).restrict) Set.univ := by
        rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
          MeasurableSet.univ, Set.preimage_univ]
    _ = boundaryLawFDD hQ ℓ hG ∅ Set.univ := by rw [h]
    _ = 1 := measure_univ

/-- **Georgii (12.13).** For a connected volume `Λ`,
`μ(σ_{Λ ∪ ∂Λ} = ζ) = z_Λ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b)`, with the normalising
constant `z_Λ = (∑_ζ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_b))⁻¹`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_cyl {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected)
    (ζ : S → E) :
    boundaryLawMeasure hQ hℓ hG (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (volumeLaw G Q hQ.symm ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hQ.symm ℓ Λ ζ := by
  rw [← restrict_preimage_singleton, ← Measure.map_apply
    (Finset.measurable_restrict (X := fun _ : S ↦ E) _) (measurableSet_singleton _),
    hℓ.isProjectiveLimit_boundaryLawMeasure hQ hG, hℓ.boundaryLawFDD_eq hQ hG hΛ subset_rfl,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : S ↦ E) _)
      (measurableSet_singleton _), restrict_preimage_singleton, normalizedVolumeLaw_cyl]

/-- **Georgii (12.12)(a), uniqueness of the measure.** A probability measure with the cylinder
probabilities (12.13) on all connected volumes is `boundaryLawMeasure`. -/
theorem IsBoundaryLaw.eq_boundaryLawMeasure_of_forall_cyl {μ : Measure (S → E)}
    [IsProbabilityMeasure μ]
    (h : ∀ Λ : Finset S, (G.induce (Λ : Set S)).Connected → ∀ ζ : S → E,
      μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
        = (volumeLaw G Q hQ.symm ℓ Λ Set.univ)⁻¹ * boundaryLawWeight G Q hQ.symm ℓ Λ ζ) :
    μ = boundaryLawMeasure hQ hℓ hG :=
  ext_of_forall_exists_cyl_eq fun Λ ↦
    ⟨SimpleGraph.hull hG.connected (root hG) Λ ∪ G.outerBoundary _,
      (SimpleGraph.subset_hull _ _ Λ).trans Finset.subset_union_left, fun ζ ↦ by
        rw [h _ (SimpleGraph.connected_induce_hull hG.connected (root hG) Λ),
          hℓ.boundaryLawMeasure_cyl hQ hG (SimpleGraph.connected_induce_hull hG.connected (root
              hG) Λ)]⟩

end BoundaryLawMeasure


/-! ## Georgii Theorem (12.12)(a): the measure of a boundary law is a Gibbs measure for `γ^Q` -/

section Gibbs

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {ℓ : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

omit [Nonempty E] in
/-- The weight (12.13) after resampling the spin at an interior site `i ∈ Λ`: the bonds at `i`
split off, the rest does not depend on the new spin. -/
lemma boundaryLawWeight_update_of_mem {Λ : Finset S} {i : S} (hi : i ∈ Λ) (ζ : S → E) (x : E) :
    boundaryLawWeight G Q hQ.symm ℓ Λ (Function.update ζ i x)
      = (∏ k ∈ G.neighborFinset i, Q i k x (ζ k))
        * ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k))
          * ∏ b ∈ G.bondsOf Λ \ G.incidenceFinset i, bondWeight Q hQ.symm ζ b) := by
  rw [boundaryLawWeight, transferWeight_eq_mul_of_mem G hQ.symm hi,
    prod_bondsOf_sdiff_incidenceFinset_update G hQ.symm, Function.update_self]
  have h1 : ∏ k ∈ G.neighborFinset i, Q i k x (Function.update ζ i x k)
      = ∏ k ∈ G.neighborFinset i, Q i k x (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset i k).1 hk)).symm]
  have h2 : ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (Function.update ζ i x k)
      = ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ k) :=
    Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hi (G.notMem_of_mem_outerBoundary hk)).symm]
  rw [h1, h2]
  ring

/-- **Georgii Theorem (12.12)(a).** The probability measure (12.13) of a boundary law for a
transfer family `Q` on a locally finite tree is a Gibbs measure for the Markov specification `γ^Q`
of (12.8). -/
theorem IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure :
    (transferSpecification G hQ).IsGibbsMeasure (boundaryLawMeasure hQ hℓ hG) := by
  refine (Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq
    (S := S) (E := E) Measure.count (isPremodifier_transferWeight hQ.symm)
    (fun Λ ω ↦ (hQ.transferWeight_pos Λ ω).ne') (fun Λ ω ↦ hQ.transferWeight_ne_top Λ ω)
    hQ.isSigmaFiniteLambdaAdmissible).2 fun i ↦ ?_
  change (boundaryLawMeasure hQ hℓ hG).bind (transferSpecification G hQ {i})
    = boundaryLawMeasure hQ hℓ hG
  have hmeas : Measurable (transferSpecification G hQ {i}) :=
    (transferSpecification G hQ {i}).measurable.mono cylinderEvents_le_pi le_rfl
  have hprob : IsProbabilityMeasure
      ((boundaryLawMeasure hQ hℓ hG).bind (transferSpecification G hQ {i})) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
    simp
  refine ext_of_forall_exists_cyl_eq fun Λ ↦ ?_
  set Λ' := SimpleGraph.hull hG.connected (root hG) (insert i Λ) with hΛ'def
  have hΛ' : (G.induce (Λ' : Set S)).Connected :=
    SimpleGraph.connected_induce_hull hG.connected (root hG) _
  have hiΛ' : i ∈ Λ' := SimpleGraph.subset_hull _ _ _ (Finset.mem_insert_self i Λ)
  refine ⟨Λ' ∪ G.outerBoundary Λ', ((Finset.subset_insert i Λ).trans
    (SimpleGraph.subset_hull _ _ _)).trans Finset.subset_union_left, fun ζ ↦ ?_⟩
  have hiH : i ∈ Λ' ∪ G.outerBoundary Λ' := Finset.mem_union_left _ hiΛ'
  have hnb : G.neighborFinset i ⊆ Λ' ∪ G.outerBoundary Λ' :=
    G.neighborFinset_subset_union_outerBoundary hiΛ'
  obtain ⟨hZ0, hZt⟩ := hQ.isSigmaFiniteLambdaAdmissible {i} ζ
  rw [Measure.bind_apply (measurableSet_cyl _ ζ) hmeas.aemeasurable]
  simp_rw [transferSpecification_singleton_apply_cyl G hQ hiH hnb ζ]
  rw [lintegral_indicator (measurableSet_cyl _ _), setLIntegral_const,
    measure_cyl_eq_tsum_insert _ (Finset.notMem_erase i _) ζ, Finset.insert_erase hiH]
  simp_rw [hℓ.boundaryLawMeasure_cyl hQ hG hΛ', boundaryLawWeight_update_of_mem hQ hiΛ']
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
    ← sigmaFiniteLambdaZ_transferWeight_singleton G hQ i ζ, boundaryLawWeight,
    transferWeight_eq_mul_of_mem G hQ.symm hiΛ', div_eq_mul_inv]
  set Z := Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
    (transferWeight G Q hQ.symm) {i} ζ with hZ
  rw [show ∀ a b c : ℝ≥0∞, a * Z⁻¹ * (b * (Z * c)) = (Z⁻¹ * Z) * (b * (a * c)) from
    fun a b c ↦ by ring, ENNReal.inv_mul_cancel hZ0 hZt, one_mul]
  ring

end Gibbs


/-! ## Markov chains on a tree: Georgii Definition (12.2) -/

section MarkovChain

variable (G : SimpleGraph S)

/-- Georgii's transition matrix `P_{ij}(x, y) = μ(σ_j = y | σ_i = x)` of a probability measure
(the conditional probability given the spin at `i`, as a ratio of cylinder probabilities). -/
def transitionProb (μ : Measure (S → E)) (i j : S) (x y : E) : ℝ≥0∞ :=
  μ ((fun σ ↦ σ i) ⁻¹' {x} ∩ (fun σ ↦ σ j) ⁻¹' {y}) / μ ((fun σ ↦ σ i) ⁻¹' {x})

/-- **Georgii Definition (12.2).** A probability measure `μ` on `E^S` is a *Markov chain* on the
tree `G` if for every oriented bond `ij` and `y ∈ E`,
`μ(σ_j = y | 𝓕_{]-∞, ij[}) = μ(σ_j = y | 𝓕_{i})` `μ`-a.s., where `]-∞, ij[` is the side of `i`. -/
structure IsMarkovChain (μ : Measure (S → E)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  condExp : ∀ ⦃i j⦄, G.Adj i j → ∀ y : E,
    μ[((fun σ : S → E ↦ σ j) ⁻¹' {y}).indicator (1 : (S → E) → ℝ) | cylinderEvents (G.past i j)]
      =ᵐ[μ] μ[((fun σ : S → E ↦ σ j) ⁻¹' {y}).indicator (1 : (S → E) → ℝ)
        | cylinderEvents ({i} : Set S)]

variable {G} {μ : Measure (S → E)}

omit [DecidableEq S] [Countable E] in
/-- The finite-dimensional content of Definition (12.2): for a finite `Δ` on the side of `i` with
`i ∈ Δ`, `μ(σ_j = y, σ_Δ = ω_Δ) = P_{ij}(ω_i, y) μ(σ_Δ = ω_Δ)`. -/
theorem IsMarkovChain.measure_preimage_inter_cyl (hμ : IsMarkovChain G μ) {i j : S}
    (hij : G.Adj i j) {Δ : Finset S} (hΔ : (Δ : Set S) ⊆ G.past i j) (hi : i ∈ Δ) (ω : S → E)
    (y : E) :
    μ ((fun σ ↦ σ j) ⁻¹' {y} ∩ cyl Δ ω) = transitionProb μ i j (ω i) y * μ (cyl Δ ω) := by
  have := hμ.isProbabilityMeasure
  set A := (fun σ : S → E ↦ σ j) ⁻¹' {y} with hA
  have hAm : MeasurableSet A := measurable_pi_apply j (measurableSet_singleton y)
  have hm' : cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S) ≤ cylinderEvents (G.past i j) :=
    cylinderEvents_mono (Set.singleton_subset_iff.2 (hΔ (Finset.mem_coe.2 hi)))
  have hm₀ : cylinderEvents (X := fun _ : S ↦ E) (G.past i j) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have key := (condExp_indicator_ae_eq_iff_forall_setIntegral hm' hm₀ hAm).1 (hμ.condExp hij y)
  set f := μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents ({i} : Set S)] with hf
  have hfm : Measurable[cylinderEvents ({i} : Set S)] f := stronglyMeasurable_condExp.measurable
  have hdep : DependsOn f {i} := hfm.dependsOn_of_cylinderEvents
  set D₁ := cyl Δ ω with hD₁def
  set D₂ := (fun σ : S → E ↦ σ i) ⁻¹' {ω i} with hD₂def
  have hD₁ : MeasurableSet[cylinderEvents (G.past i j)] D₁ := measurableSet_cylinderEvents_cyl hΔ ω
  have hD₂ : MeasurableSet[cylinderEvents (G.past i j)] D₂ :=
    measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (hΔ (Finset.mem_coe.2 hi))
      (measurableSet_singleton _)
  have hD₁m : MeasurableSet D₁ := measurableSet_cyl Δ ω
  have hD₂m : MeasurableSet D₂ := measurable_pi_apply i (measurableSet_singleton _)
  have hD₁₂ : D₁ ⊆ D₂ := fun σ hσ ↦ mem_cyl.1 hσ i hi
  have h1 : μ.real (A ∩ D₁) = μ.real D₁ * f ω := by
    rw [← key D₁ hD₁, setIntegral_congr_fun hD₁m (g := fun _ ↦ f ω) fun σ hσ ↦ hdep fun k hk ↦ by
      rw [Set.mem_singleton_iff.1 hk]; exact mem_cyl.1 hσ i hi, setIntegral_const, smul_eq_mul]
  have h2 : μ.real (A ∩ D₂) = μ.real D₂ * f ω := by
    rw [← key D₂ hD₂, setIntegral_congr_fun hD₂m (g := fun _ ↦ f ω) fun σ hσ ↦ hdep fun k hk ↦ by
      rw [Set.mem_singleton_iff.1 hk]; exact hσ, setIntegral_const, smul_eq_mul]
  have hE : μ (A ∩ D₁) * μ D₂ = μ (A ∩ D₂) * μ D₁ := by
    have : (μ (A ∩ D₁) * μ D₂).toReal = (μ (A ∩ D₂) * μ D₁).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def,
        ← measureReal_def, ← measureReal_def, h1, h2]
      ring
    exact (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (measure_ne_top _ _)
      (measure_ne_top _ _)) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1 this
  by_cases h0 : μ D₂ = 0
  · have hA₁ : μ (A ∩ D₁) = 0 := measure_mono_null (Set.inter_subset_right.trans hD₁₂) h0
    have hA₂ : μ (D₂ ∩ A) = 0 := measure_mono_null Set.inter_subset_left h0
    rw [hA₁, transitionProb, hA₂, ENNReal.zero_div, zero_mul]
  · rw [transitionProb, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
      ENNReal.eq_div_iff h0 (measure_ne_top _ _), Set.inter_comm D₂ A, mul_comm]
    exact hE

end MarkovChain


/-! ## Gibbs measures for `γ^Q`: cylinder identities and positivity -/

section GibbsCylinder

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) {μ : Measure (S → E)} [IsProbabilityMeasure μ]

lemma measurable_transferSpecification (Λ : Finset S) :
    Measurable (transferSpecification G hQ Λ) :=
  (transferSpecification G hQ Λ).measurable.mono cylinderEvents_le_pi le_rfl

variable (hμ : (transferSpecification G hQ).IsGibbsMeasure μ)
include hμ

/-- For `μ ∈ 𝒢(γ^Q)`, `μ(σ_{Λ ∪ ∂Λ} = ζ) = γ_Λ(σ_Λ = ζ_Λ | ζ) μ(σ_{∂Λ} = ζ_{∂Λ})` (the Markov
    property
of `γ^Q`). -/
theorem measure_cyl_union_outerBoundary_of_isGibbsMeasure (Λ : Finset S) (ζ : S → E) :
    μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = transferWeight G Q hQ.symm Λ ζ / Specification.sigmaFiniteLambdaZ (S := S) (E := E)
          Measure.count (transferWeight G Q hQ.symm) Λ ζ * μ (cyl (G.outerBoundary Λ) ζ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) Λ
  calc μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = (μ.bind (transferSpecification G hQ Λ)) (cyl (Λ ∪ G.outerBoundary Λ) ζ) := by rw [hbind]
    _ = _ := by
      rw [Measure.bind_apply (measurableSet_cyl _ _)
        (measurable_transferSpecification hQ Λ).aemeasurable]
      simp_rw [transferSpecification_apply_cyl_union_outerBoundary G hQ Λ ζ]
      rw [lintegral_indicator (measurableSet_cyl _ _), setLIntegral_const, mul_comm]

/-- A Gibbs measure for the positive specification `γ^Q` is positive on cylinder events. -/
theorem measure_cyl_pos_of_isGibbsMeasure (H : Finset S) (ζ : S → E) : 0 < μ (cyl H ζ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) H
  have hpos : ∀ ω, 0 < transferSpecification G hQ H ω (cyl H ζ) := fun ω ↦ by
    rw [transferSpecification_apply G hQ H ω (measurableSet_cyl _ _),
      setLIntegral_lambdaCount_cyl' H ω ζ (measurable_transferWeight G hQ.symm H)]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (hQ.sigmaFiniteLambdaZ_ne_top H ω))
      (hQ.transferWeight_pos _ _).ne'
  calc 0 < (μ.bind (transferSpecification G hQ H)) (cyl H ζ) := by
        rw [Measure.bind_apply (measurableSet_cyl _ _)
          (measurable_transferSpecification hQ H).aemeasurable,
          lintegral_pos_iff_support ((Kernel.measurable_coe _ (measurableSet_cyl _ _)).mono
            cylinderEvents_le_pi le_rfl),
          Set.eq_univ_of_forall (s := Function.support fun ω ↦
            transferSpecification G hQ H ω (cyl H ζ)) fun ω ↦ (hpos ω).ne', measure_univ]
        exact one_pos
    _ = μ (cyl H ζ) := by rw [hbind]

end GibbsCylinder

/-! ## Georgii Theorem (12.12)(b): Markov chains in `𝒢(γ^Q)` come from boundary laws -/

section Representation

variable {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}

omit [Countable E] in
/-- The Markov chain property along the whole boundary of a connected set: for `Λ` connected and
`B ⊆ ∂Λ`, `μ(σ_Λ ≡ a, σ_B = ζ_B) = μ(σ_Λ ≡ a) ∏_{k ∈ B} P_{k_Λ k}(a, ζ_k)`. This is Georgii's
`μ(B | A) = ∏_{k ∈ ∂Λ} P_{k_Λ k}(a, ζ_k)` in the proof of (12.12)(b), a consequence of (12.4). -/
theorem IsMarkovChain.measure_cyl_union_eq_mul_prod {μ : Measure (S → E)}
    (hμ : IsMarkovChain G μ) (hG : G.IsAcyclic)
    {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) (a : E) (ζ : S → E) {B : Finset S}
    (hB : B ⊆ G.outerBoundary Λ) :
    μ (cyl (Λ ∪ B) (juxt (Λ : Set S) ζ fun _ ↦ a))
      = μ (cyl Λ fun _ ↦ a) * ∏ k ∈ B, transitionProb μ (G.anchor Λ k) k a (ζ k) := by
  induction B using Finset.induction_on with
  | empty =>
    rw [Finset.union_empty, Finset.prod_empty, mul_one]
    exact congrArg μ (cyl_congr fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _)
  | insert k B hk ih =>
    have hB' : B ⊆ G.outerBoundary Λ := (Finset.subset_insert k B).trans hB
    have hkΛ : k ∈ G.outerBoundary Λ := hB (Finset.mem_insert_self k B)
    have hkΛ' : k ∉ Λ := G.notMem_of_mem_outerBoundary hkΛ
    have hpast : ((Λ ∪ B : Finset S) : Set S) ⊆ G.past (G.anchor Λ k) k := fun x hx ↦ by
      rw [Finset.mem_coe, Finset.mem_union] at hx
      refine hG.mem_past_anchor hΛ hkΛ ?_ ?_
      · rcases hx with hx | hx
        · exact Finset.mem_union_left _ hx
        · exact Finset.mem_union_right _ (hB' hx)
      · rintro rfl
        rcases hx with hx | hx
        · exact hkΛ' hx
        · exact hk hx
    have key := hμ.measure_preimage_inter_cyl (G.adj_anchor hkΛ).symm hpast
      (Finset.mem_union_left _ (G.anchor_mem hkΛ)) (juxt (Λ : Set S) ζ fun _ ↦ a) (ζ k)
    rw [juxt_apply_of_mem (Finset.mem_coe.2 (G.anchor_mem hkΛ))] at key
    rw [Finset.union_insert, cyl_insert_eq_inter, Finset.prod_insert hk, mul_left_comm, ← ih hB',
      juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using hkΛ')]
    exact key

variable (G) (Q) (hs : ∀ i j x y, Q i j x y = Q j i y x)

open Classical in
/-- The weight `∏_{b ⊆ Λ} Q_b(a a)` of the bonds inside `Λ` at the constant configuration `a`. -/
def innerWeight (a : E) (Λ : Finset S) : ℝ≥0∞ :=
  ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs (fun _ ↦ a) b

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma innerWeight_pos (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) (a : E) (Λ : Finset S) :
    0 < innerWeight G Q hs a Λ := by
  classical
  refine pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun b hb ↦ ?_)
  have he := (SimpleGraph.mem_bondsOf.1 (Finset.mem_filter.1 hb).1).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact (hpos (G.mem_edgeSet.1 he) _ _).ne'

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma innerWeight_ne_top (htop : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, Q i j x y ≠ ⊤) (a : E)
    (Λ : Finset S) : innerWeight G Q hs a Λ ≠ ⊤ := by
  classical
  refine ENNReal.prod_ne_top fun b hb ↦ ?_
  have he := (SimpleGraph.mem_bondsOf.1 (Finset.mem_filter.1 hb).1).1
  revert he
  refine Sym2.inductionOn b fun i j he ↦ ?_
  exact htop (G.mem_edgeSet.1 he) _ _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a tree, the transfer weight of a connected `Λ` at the configuration which is `a` on `Λ`
and `ζ` outside factorises as `∏_{b ⊆ Λ} Q_b(aa) ∏_{k ∈ ∂Λ} Q_{k_Λ k}(a, ζ_k)`. -/
lemma transferWeight_juxt_const (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (ζ : S → E) (a : E) :
    transferWeight G Q hs Λ (juxt (Λ : Set S) ζ fun _ ↦ a)
      = innerWeight G Q hs a Λ * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) := by
  classical
  rw [transferWeight, hG.bondsOf_eq_filter_union_image hΛ,
    Finset.prod_union (SimpleGraph.disjoint_filter_bondsOf_image Λ),
    Finset.prod_image fun x hx y hy h ↦
      SimpleGraph.injOn_mk_anchor Λ (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h, innerWeight]
  congr 1
  · exact Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hs fun v hv ↦
      juxt_apply_of_mem (Finset.mem_coe.2 ((Finset.mem_filter.1 hb).2 v hv)) _
  · exact Finset.prod_congr rfl fun k hk ↦ by
      rw [bondWeight_mk, juxt_apply_of_mem (Finset.mem_coe.2 (G.anchor_mem hk)),
        juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by
          simpa using G.notMem_of_mem_outerBoundary hk)]


open Classical in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- On a tree, the transfer weight of a connected `Λ` factorises into the bonds inside `Λ` and the
bonds `{k_Λ, k}` to the boundary. -/
lemma transferWeight_eq_filter_mul_prod (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (σ : S → E) :
    transferWeight G Q hs Λ σ
      = (∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs σ b)
        * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k (σ (G.anchor Λ k)) (σ k) := by
  conv_lhs => rw [transferWeight, hG.bondsOf_eq_filter_union_image hΛ]
  rw [Finset.prod_union (SimpleGraph.disjoint_filter_bondsOf_image Λ),
    Finset.prod_image fun x hx y hy h ↦
      SimpleGraph.injOn_mk_anchor Λ (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) h]
  rfl

variable (ℓ : S → S → E → ℝ≥0∞)

open Classical in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The weight (12.13) after resampling the spin at a boundary site `k ∈ ∂Λ`: only the factor
`ℓ_{k k_Λ}(y) Q_{k_Λ k}(ζ_{k_Λ}, y)` depends on the new spin `y`. -/
lemma boundaryLawWeight_update_of_mem_outerBoundary (hG : G.IsAcyclic) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {k : S} (hk : k ∈ G.outerBoundary Λ) (ζ : S → E)
    (y : E) :
    boundaryLawWeight G Q hs ℓ Λ (Function.update ζ k y)
      = (ℓ k (G.anchor Λ k) y * Q (G.anchor Λ k) k (ζ (G.anchor Λ k)) y)
        * ((∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (ζ k'))
          * ((∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs ζ b)
            * ∏ k' ∈ (G.outerBoundary Λ).erase k,
                Q (G.anchor Λ k') k' (ζ (G.anchor Λ k')) (ζ k'))) := by
  have hkΛ := G.notMem_of_mem_outerBoundary hk
  rw [boundaryLawWeight, transferWeight_eq_filter_mul_prod G Q hs hG hΛ,
    ← Finset.mul_prod_erase _ _ hk,
    ← Finset.mul_prod_erase _ (fun k' ↦ Q (G.anchor Λ k') k' (Function.update ζ k y (G.anchor Λ k'))
      (Function.update ζ k y k')) hk,
    Function.update_self, Function.update_of_ne (ne_of_mem_of_not_mem (G.anchor_mem hk) hkΛ)]
  have h1 : ∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (Function.update ζ k y k')
      = ∏ k' ∈ (G.outerBoundary Λ).erase k, ℓ k' (G.anchor Λ k') (ζ k') :=
    Finset.prod_congr rfl fun k' hk' ↦ by rw [Function.update_of_ne (Finset.mem_erase.1 hk').1]
  have h2 : ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ),
        bondWeight Q hs (Function.update ζ k y) b
      = ∏ b ∈ (G.bondsOf Λ).filter (fun b ↦ ∀ v ∈ b, v ∈ Λ), bondWeight Q hs ζ b :=
    Finset.prod_congr rfl fun b hb ↦ bondWeight_congr hs fun v hv ↦
      Function.update_of_ne (ne_of_mem_of_not_mem ((Finset.mem_filter.1 hb).2 v hv) hkΛ) _ _
  have h3 : ∏ k' ∈ (G.outerBoundary Λ).erase k, Q (G.anchor Λ k') k'
        (Function.update ζ k y (G.anchor Λ k')) (Function.update ζ k y k')
      = ∏ k' ∈ (G.outerBoundary Λ).erase k, Q (G.anchor Λ k') k' (ζ (G.anchor Λ k')) (ζ k') :=
    Finset.prod_congr rfl fun k' hk' ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.1 hk').1, Function.update_of_ne
        (ne_of_mem_of_not_mem (G.anchor_mem (Finset.mem_of_mem_erase hk')) hkΛ)]
  rw [h1, h2, h3]
  ring

variable {ℓ}

variable {G Q hs} [Nonempty E] (hQ : IsTransferFamily G Q) {μ : Measure (S → E)}
  [IsProbabilityMeasure μ]

variable (Q) in
/-- Georgii's boundary law of a Markov chain in `𝒢(γ^Q)`, normalised through the reference state
`a`: `ℓ_{ij}(x) = P_{ji}(a, x) / Q_{ji}(a, x)`. -/
def chainBoundaryLaw (μ : Measure (S → E)) (a : E) : S → S → E → ℝ≥0∞ := fun i j x ↦
  transitionProb μ j i a x / Q j i a x

/-- Georgii's normalising constant `z_Λ = μ(σ_Λ ≡ a) / ∏_{b ⊆ Λ} Q_b(aa)` in the proof of
(12.12)(b). -/
def chainNormalizer (μ : Measure (S → E)) (a : E) (Λ : Finset S) : ℝ≥0∞ :=
  μ (cyl Λ fun _ ↦ a) / innerWeight G Q hQ.symm a Λ

variable (hGibbs : (transferSpecification G hQ).IsGibbsMeasure μ)
include hGibbs

lemma transitionProb_pos_of_isGibbsMeasure {i j : S} (hij : i ≠ j) (x y : E) :
    0 < transitionProb μ i j x y :=
  ENNReal.div_pos (by
    rw [preimage_inter_preimage_eq_cyl hij x y (baseConfig (S := S) (E := E))]
    exact (measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne') (measure_ne_top _ _)

lemma transitionProb_ne_top_of_isGibbsMeasure (i j : S) (x y : E) :
    transitionProb μ i j x y ≠ ⊤ :=
  ENNReal.div_ne_top (measure_ne_top _ _) (by
    rw [preimage_singleton_eq_cyl i x (baseConfig (S := S) (E := E))]
    exact (measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne')

lemma chainBoundaryLaw_pos (a : E) {i j : S} (hij : G.Adj i j) (x : E) :
    0 < chainBoundaryLaw Q μ a i j x :=
  ENNReal.div_pos (transitionProb_pos_of_isGibbsMeasure hQ hGibbs hij.ne.symm a x).ne'
    (hQ.ne_top hij.symm a x)

lemma chainBoundaryLaw_ne_top (a : E) {i j : S} (hij : G.Adj i j) (x : E) :
    chainBoundaryLaw Q μ a i j x ≠ ⊤ :=
  ENNReal.div_ne_top (transitionProb_ne_top_of_isGibbsMeasure hQ hGibbs j i a x)
    (hQ.pos hij.symm a x).ne'

lemma chainNormalizer_ne_zero (a : E) (Λ : Finset S) : chainNormalizer hQ μ a Λ ≠ 0 :=
  ENNReal.div_ne_zero.2 ⟨(measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _).ne',
    innerWeight_ne_top G Q hQ.symm hQ.ne_top a Λ⟩

omit [Nonempty E] hGibbs in
lemma chainNormalizer_ne_top (a : E) (Λ : Finset S) : chainNormalizer hQ μ a Λ ≠ ⊤ :=
  ENNReal.div_ne_top (measure_ne_top _ _) (innerWeight_pos G Q hQ.symm hQ.pos a Λ).ne'

variable (hμ : IsMarkovChain G μ) (hG : G.IsTree)
include hμ hG

/-- **Georgii (12.12)(b), the representation (12.13).** A Markov chain `μ ∈ 𝒢(γ^Q)` on a tree
satisfies `μ(σ_{Λ ∪ ∂Λ} = ζ) = z_Λ ∏_{k ∈ ∂Λ} ℓ_{k k_Λ}(ζ_k) ∏_{b ∩ Λ ≠ ∅} Q_b(ζ)` for every
connected `Λ`, with `ℓ_{ij}(x) = P_{ji}(a, x)/Q_{ji}(a, x)` and `z_Λ = μ(σ_Λ ≡ a)/∏_{b ⊆ Λ}
    Q_b(aa)`. -/
theorem IsMarkovChain.measure_cyl_union_outerBoundary_eq (a : E) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) (ζ : S → E) :
    μ (cyl (Λ ∪ G.outerBoundary Λ) ζ)
      = chainNormalizer hQ μ a Λ * boundaryLawWeight G Q hQ.symm (chainBoundaryLaw Q μ a) Λ ζ := by
  have hζ'B : ∀ k ∈ G.outerBoundary Λ, (juxt (Λ : Set S) ζ fun _ ↦ a) k = ζ k := fun k hk ↦
    juxt_apply_of_not_mem (show k ∉ (Λ : Set S) by simpa using G.notMem_of_mem_outerBoundary hk) _
  obtain ⟨hZ0, hZt⟩ := hQ.isSigmaFiniteLambdaAdmissible Λ ζ
  have hIa0 := (innerWeight_pos G Q hQ.symm hQ.pos a Λ).ne'
  have hIat := innerWeight_ne_top G Q hQ.symm hQ.ne_top a Λ
  have hQb0 : ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk ↦ (hQ.pos (G.adj_anchor hk).symm a (ζ k)).ne'
  have hQbt : ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) ≠ ⊤ :=
    ENNReal.prod_ne_top fun k hk ↦ hQ.ne_top (G.adj_anchor hk).symm a (ζ k)
  have hG1 := measure_cyl_union_outerBoundary_of_isGibbsMeasure hQ hGibbs Λ ζ
  have hG2 := measure_cyl_union_outerBoundary_of_isGibbsMeasure hQ hGibbs Λ
    (juxt (Λ : Set S) ζ fun _ ↦ a)
  have hM := hμ.measure_cyl_union_eq_mul_prod hG.isAcyclic hΛ a ζ subset_rfl
  rw [transferWeight_juxt_const G Q hQ.symm hG.isAcyclic hΛ ζ a,
    sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ hζ'B, cyl_congr hζ'B] at hG2
  have hPb : ∏ k ∈ G.outerBoundary Λ, transitionProb μ (G.anchor Λ k) k a (ζ k)
      = (∏ k ∈ G.outerBoundary Λ, chainBoundaryLaw Q μ a k (G.anchor Λ k) (ζ k))
        * ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk ↦ ?_
    rw [chainBoundaryLaw, ENNReal.div_mul_cancel (hQ.pos (G.adj_anchor hk).symm a (ζ k)).ne'
      (hQ.ne_top (G.adj_anchor hk).symm a (ζ k))]
  rw [hPb] at hM
  have hG2M := hG2.symm.trans hM
  set Y := μ (cyl (G.outerBoundary Λ) ζ) with hY
  set m := μ (cyl Λ fun _ ↦ a) with hm
  set L := ∏ k ∈ G.outerBoundary Λ, chainBoundaryLaw Q μ a k (G.anchor Λ k) (ζ k) with hL
  set Qb := ∏ k ∈ G.outerBoundary Λ, Q (G.anchor Λ k) k a (ζ k) with hQb
  set Z := Specification.sigmaFiniteLambdaZ (S := S) (E := E) Measure.count
    (transferWeight G Q hQ.symm) Λ ζ with hZ
  set Ia := innerWeight G Q hQ.symm a Λ with hIa
  have hYeq : Y = m * L * Z * Ia⁻¹ := by
    calc Y = (Ia * Ia⁻¹) * (Qb * Qb⁻¹) * (Z⁻¹ * Z) * Y := by
          rw [ENNReal.mul_inv_cancel hIa0 hIat, ENNReal.mul_inv_cancel hQb0 hQbt,
            ENNReal.inv_mul_cancel hZ0 hZt]
          ring
      _ = (Ia * Qb / Z * Y) * (Ia⁻¹ * Qb⁻¹ * Z) := by rw [div_eq_mul_inv]; ring
      _ = (m * (L * Qb)) * (Ia⁻¹ * Qb⁻¹ * Z) := by rw [hG2M]
      _ = m * L * Z * Ia⁻¹ * (Qb * Qb⁻¹) := by ring
      _ = m * L * Z * Ia⁻¹ := by rw [ENNReal.mul_inv_cancel hQb0 hQbt, mul_one]
  rw [hG1, hYeq, chainNormalizer, boundaryLawWeight, div_eq_mul_inv, div_eq_mul_inv]
  calc transferWeight G Q hQ.symm Λ ζ * Z⁻¹ * (m * L * Z * Ia⁻¹)
      = (Z⁻¹ * Z) * (m * Ia⁻¹ * (L * transferWeight G Q hQ.symm Λ ζ)) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hZ0 hZt, one_mul]

/-- The normalising constants of (12.13) are the inverse total masses: `z_Λ ∑_ζ (…) = 1`. -/
theorem IsMarkovChain.chainNormalizer_mul_volumeLaw_univ (a : E) {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) :
    chainNormalizer hQ μ a Λ
      * volumeLaw G Q hQ.symm (chainBoundaryLaw Q μ a) Λ Set.univ = 1 := by
  have h := measure_cyl_eq_lintegral_lambdaCount μ (H := ∅) (V := Λ ∪ G.outerBoundary Λ)
    (Finset.disjoint_empty_left _) (baseConfig (S := S) (E := E))
  rw [cyl_empty, measure_univ, Finset.empty_union] at h
  simp_rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ] at h
  rw [lintegral_const_mul _ (measurable_boundaryLawWeight G Q hQ.symm _ Λ),
    ← volumeLaw_univ_eq_lintegral] at h
  exact h.symm

/-- **Georgii (12.12)(b), the boundary law.** The family `ℓ_{ij}(x) = P_{ji}(a, x)/Q_{ji}(a, x)`
of a Markov chain `μ ∈ 𝒢(γ^Q)` on a tree is a boundary law for `Q`. -/
theorem IsMarkovChain.isBoundaryLaw_chainBoundaryLaw (a : E) :
    IsBoundaryLaw G Q (chainBoundaryLaw Q μ a) where
  pos _ _ hij x := chainBoundaryLaw_pos hQ hGibbs a hij x
  ne_top _ _ hij x := chainBoundaryLaw_ne_top hQ hGibbs a hij x
  consistent i j hij := by
    have hi : i ∈ G.outerBoundary {j} := by
      rw [SimpleGraph.outerBoundary_singleton, SimpleGraph.mem_neighborFinset]
      exact hij.symm
    have hanc : G.anchor {j} i = j := SimpleGraph.anchor_singleton hi
    have hΛ := connected_induce_singleton (G := G) j
    have hzΛ0 := chainNormalizer_ne_zero hQ hGibbs a {j}
    have hzΛt := chainNormalizer_ne_top hQ (μ := μ) a {j}
    have hzΔ0 := chainNormalizer_ne_zero hQ hGibbs a (insert i {j})
    have hzΔt := chainNormalizer_ne_top hQ (μ := μ) a (insert i {j})
    refine ⟨chainNormalizer hQ μ a (insert i {j}) / chainNormalizer hQ μ a {j},
      ENNReal.div_ne_zero.2 ⟨hzΔ0, hzΛt⟩, ENNReal.div_ne_top hzΔt hzΛ0, fun x ↦ ?_⟩
    set ζ : S → E := fun _ ↦ x with hζ
    -- the two representations of `μ(σ_{Λ ∪ ∂Λ} = ζ)`, `Λ = {j}`, through `Λ` and through `Δ`
    have h1 := hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ ζ
    have h2 := measure_cyl_eq_lintegral_lambdaCount μ
      (hG.isAcyclic.disjoint_union_outerBoundary_erase hΛ hi) ζ
    rw [← hG.isAcyclic.insert_union_outerBoundary_eq hΛ hi] at h2
    simp_rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a
        (SimpleGraph.connected_induce_insert_of_mem_outerBoundary hΛ hi)] at h2
    rw [lintegral_const_mul _ (measurable_boundaryLawWeight G Q hQ.symm _ _),
      lintegral_boundaryLawWeight_insert hQ.symm hG.isAcyclic hΛ hi ζ, h1,
      boundaryLawWeight, ← Finset.mul_prod_erase _ _ hi, hanc,
      mul_assoc (chainBoundaryLaw Q μ a i j (ζ i))] at h2
    have hζi : ζ i = x := rfl
    rw [hζi] at h2
    set A := (∏ k ∈ (G.outerBoundary {j}).erase i,
        chainBoundaryLaw Q μ a k (G.anchor {j} k) (ζ k)) * transferWeight G Q hQ.symm {j} ζ
      with hA
    have hA0 : A ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k hk ↦
      (chainBoundaryLaw_pos hQ hGibbs a (G.adj_anchor (Finset.mem_of_mem_erase hk)) _).ne')
      (hQ.transferWeight_pos _ _).ne'
    have hAt : A ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.prod_ne_top fun k hk ↦
      chainBoundaryLaw_ne_top hQ hGibbs a (G.adj_anchor (Finset.mem_of_mem_erase hk)) _)
      (hQ.transferWeight_ne_top _ _)
    calc chainBoundaryLaw Q μ a i j x
        = (chainNormalizer hQ μ a {j})⁻¹ * chainNormalizer hQ μ a {j}
          * (chainBoundaryLaw Q μ a i j x * A) * A⁻¹ := by
          rw [ENNReal.inv_mul_cancel hzΛ0 hzΛt, one_mul, mul_assoc,
            ENNReal.mul_inv_cancel hA0 hAt, mul_one]
      _ = (chainNormalizer hQ μ a {j})⁻¹
          * (chainNormalizer hQ μ a {j} * (chainBoundaryLaw Q μ a i j x * A)) * A⁻¹ := by ring
      _ = (chainNormalizer hQ μ a {j})⁻¹ * (chainNormalizer hQ μ a (insert i {j})
          * (A * ∏ k ∈ (G.neighborFinset i).erase j, ∑' y,
              chainBoundaryLaw Q μ a k i y * Q k i y x)) * A⁻¹ := by rw [h2]
      _ = chainNormalizer hQ μ a (insert i {j}) / chainNormalizer hQ μ a {j}
          * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, chainBoundaryLaw Q μ a k i y * Q k i y x)
          * (A * A⁻¹) := by rw [div_eq_mul_inv]; ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]
  mass_ne_top i := by
    have h := hμ.chainNormalizer_mul_volumeLaw_univ hQ hGibbs hG a (connected_induce_singleton i)
    rw [volumeLaw_singleton_univ] at h
    intro htop
    rw [htop, ENNReal.mul_top (chainNormalizer_ne_zero hQ hGibbs a {i})] at h
    exact ENNReal.top_ne_one h

/-- **Georgii Theorem (12.12)(b).** Every Markov chain `μ ∈ 𝒢(γ^Q)` on a locally finite tree is
the measure (12.13) of a boundary law for `Q`. -/
theorem IsMarkovChain.eq_boundaryLawMeasure (a : E) :
    μ = boundaryLawMeasure hQ (hμ.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a) hG :=
  (hμ.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a).eq_boundaryLawMeasure_of_forall_cyl hQ hG
    fun Λ hΛ ζ ↦ by
      rw [hμ.measure_cyl_union_outerBoundary_eq hQ hGibbs hG a hΛ ζ,
        ENNReal.eq_inv_of_mul_eq_one_left (hμ.chainNormalizer_mul_volumeLaw_univ hQ hGibbs hG a hΛ)]

theorem IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure :
    ∃ ℓ : S → S → E → ℝ≥0∞, ∃ hℓ : IsBoundaryLaw G Q ℓ, μ = boundaryLawMeasure hQ hℓ hG :=
  ⟨_, _, hμ.eq_boundaryLawMeasure hQ hGibbs hG (Classical.arbitrary E)⟩

end Representation


/-! ## Georgii Definition (12.1): Markov specifications -/

section MarkovSpecification

variable (G : SimpleGraph S) [G.LocallyFinite]

/-- **Georgii Definition (12.1).** A specification `γ` is *Markov* (for the graph `G`) if
`γ_Λ(σ_Λ = ζ | ·)` is `𝓕_{∂Λ}`-measurable for every finite `Λ` and every `ζ`. -/
def IsMarkovSpecification (γ : Specification S E) : Prop :=
  ∀ (Λ : Finset S) (ζ : S → E),
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (G.outerBoundary Λ : Set S)]
      fun ω ↦ γ Λ ω (cyl Λ ζ)

variable {G} [Nonempty E] {Q : S → S → E → E → ℝ≥0∞} (hQ : IsTransferFamily G Q)

/-- `γ^Q` is a Markov specification: `γ_Λ(σ_Λ = ζ_Λ | ω) = ∏_{b ∩ Λ ≠ ∅} Q_b(ζ_Λ ω_{Λᶜ}) / Z_Λ(ω)`
depends on `ω` through `ω_{∂Λ}` only. -/
theorem isMarkovSpecification_transferSpecification :
    IsMarkovSpecification G (transferSpecification G hQ) := by
  intro Λ ζ
  refine (measurable_cylinderEvents_iff_dependsOn (X := fun _ : S ↦ E)).2
    ⟨(Kernel.measurable_coe _ (measurableSet_cyl _ _)).mono cylinderEvents_le_pi le_rfl,
      fun ω ω' h ↦ ?_⟩
  simp only [transferSpecification_apply G hQ Λ _ (measurableSet_cyl Λ ζ),
    setLIntegral_lambdaCount_cyl' Λ _ ζ (measurable_transferWeight G hQ.symm Λ)]
  rw [sigmaFiniteLambdaZ_transferWeight_congr G hQ Λ h,
    transferWeight_congr G hQ.symm (τ := juxt (Λ : Set S) ω' (Λ.restrict ζ)) fun k hk ↦ ?_]
  rcases Finset.mem_union.1 hk with hkΛ | hkΛ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hkΛ), juxt_apply_of_mem (Finset.mem_coe.2 hkΛ)]
  · have hkΛ' : k ∉ (Λ : Set S) := by simpa using G.notMem_of_mem_outerBoundary hkΛ
    rw [juxt_apply_of_not_mem hkΛ', juxt_apply_of_not_mem hkΛ', h k hkΛ]

end MarkovSpecification

/-! ## Normalised boundary laws: Georgii (12.15), (12.16) and Corollary (12.17)

A boundary law is determined up to a positive factor on each oriented bond; normalising at a
reference state `a ∈ E` (`ℓ_{ij}(a) = 1`) turns the consistency equation into (12.15). On the
Cayley tree `CT(d)` (every vertex of degree `d + 1`) a *completely homogeneous* family `ℓ_{ij} = ℓ`
for a single symmetric matrix `Q` is a boundary law iff `ℓ` solves (12.16),
`ℓ(x) = (ℓQ(x) / ℓQ(a))^d`. This is the boundary-law side of Corollary (12.17); the
correspondence with completely homogeneous Markov chains is Theorem (12.12). -/

section Normalized

variable {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  {ℓ : S → S → E → ℝ≥0∞}

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii (12.15).** For a boundary law normalised at `a` (`ℓ_{ij}(a) = 1`), the constants are
determined: `ℓ_{ij}(x) = ∏_{k ∈ ∂i \ {j}} (ℓ_{ki} Q_{ki})(x) / (ℓ_{ki} Q_{ki})(a)`. -/
theorem IsBoundaryLaw.eq_prod_div_of_normalized (hℓ : IsBoundaryLaw G Q ℓ)
    (hpos : ∀ ⦃i j⦄, G.Adj i j → ∀ x y, 0 < Q i j x y) {a : E}
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j a = 1) ⦃i j : S⦄ (hij : G.Adj i j) (x : E) :
    ℓ i j x = ∏ k ∈ (G.neighborFinset i).erase j,
      (∑' y, ℓ k i y * Q k i y x) / ∑' y, ℓ k i y * Q k i y a := by
  obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent hij
  have hprod : ∀ z, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y z ≠ 0 := fun z ↦
    Finset.prod_ne_zero_iff.2 fun k hk ↦ (hℓ.tsum_mul_pos hpos
      (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm) z).ne'
  have hprodt : ∀ z, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y z ≠ ⊤ := fun z ↦
    ENNReal.prod_ne_top fun k hk ↦ hℓ.tsum_mul_ne_top hpos
      (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm) z
  have hca : c = (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y a)⁻¹ := by
    have := hc a
    rw [ha hij] at this
    exact ENNReal.eq_inv_of_mul_eq_one_left this.symm
  rw [hc x, hca, ENNReal.prod_div_distrib, div_eq_mul_inv, mul_comm]
  exact fun k hk _ _ _ ↦ Or.inl (hℓ.tsum_mul_pos hpos
    (((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hk))).symm) a).ne'

variable (G Q)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii (12.16) ⇔ (12.10) for completely homogeneous families on the Cayley tree.** On a
graph regular of degree `d + 1`, with a single matrix `Q` along every bond (the transfer family
`Q_{ij} = Q` of a completely homogeneous Markov specification is necessarily symmetric, but the
boundary-law equation does not use this), a constant family `ℓ_{ij} = ℓ` of positive finite
vectors with `ℓ(a) = 1` is a boundary law iff `ℓ` solves `ℓ(x) = (ℓQ(x) / ℓQ(a))^d` (and, for
countable `E`, `∑_x (ℓQ(x))^{d+1} < ∞`). -/
theorem isBoundaryLaw_const_iff {d : ℕ} (hreg : G.IsRegularOfDegree (d + 1))
    {Q₀ : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < Q₀ x y)
    {ℓ₀ : E → ℝ≥0∞} (hℓpos : ∀ x, 0 < ℓ₀ x) (hℓt : ∀ x, ℓ₀ x ≠ ⊤)
    {a : E} (ha : ℓ₀ a = 1) (hne : ∃ i j : S, G.Adj i j) :
    IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ₀) ↔
      (∀ x, ℓ₀ x = ((∑' y, ℓ₀ y * Q₀ y x) / ∑' y, ℓ₀ y * Q₀ y a) ^ d)
        ∧ ∑' x, (∑' y, ℓ₀ y * Q₀ y x) ^ (d + 1) ≠ ⊤ := by
  have hcard : ∀ ⦃i j : S⦄, G.Adj i j → ((G.neighborFinset i).erase j).card = d := fun i j hij ↦ by
    rw [Finset.card_erase_of_mem ((G.mem_neighborFinset i j).2 hij),
        G.card_neighborFinset_eq_degree,
      hreg i, Nat.add_sub_cancel]
  constructor
  · intro hℓ
    refine ⟨fun x ↦ ?_, ?_⟩
    · have := hℓ.eq_prod_div_of_normalized (fun _ _ _ x y ↦ hpos x y) (fun _ _ _ ↦ ha)
        hne.choose_spec.choose_spec x
      rwa [Finset.prod_const, hcard hne.choose_spec.choose_spec] at this
    · have := hℓ.mass_ne_top hne.choose
      simp only [Finset.prod_const, G.card_neighborFinset_eq_degree, hreg.degree_eq] at this
      exact this
  · rintro ⟨h16, hm⟩
    refine ⟨fun _ _ _ x ↦ hℓpos x, fun _ _ _ x ↦ hℓt x, fun i j hij ↦ ?_, fun i ↦ ?_⟩
    · have hQa0 : ∑' y, ℓ₀ y * Q₀ y a ≠ 0 :=
        (ENNReal.mul_pos (hℓpos a).ne' (hpos a a).ne').trans_le (ENNReal.le_tsum a) |>.ne'
      have hQat : ∑' y, ℓ₀ y * Q₀ y a ≠ ⊤ := by
        intro h
        apply hm
        refine ENNReal.tsum_eq_top_of_eq_top ⟨a, ?_⟩
        rw [h, ENNReal.top_pow (Nat.succ_ne_zero d)]
      refine ⟨((∑' y, ℓ₀ y * Q₀ y a) ^ d)⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top hQat),
        ENNReal.inv_ne_top.2 (pow_ne_zero d hQa0), fun x ↦ ?_⟩
      rw [Finset.prod_const, hcard hij, h16 x, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow,
        mul_comm]
    · simp only [Finset.prod_const, G.card_neighborFinset_eq_degree, hreg.degree_eq]
      exact hm

end Normalized


/-! ## Georgii Example (12.11): the boundary laws of Chapter 11 on `ℤ`

`ℤ` with its usual graph structure is Mathlib's `SimpleGraph.hasse ℤ` (adjacency `i ⋖ j ∨ j ⋖ i`,
i.e. `|i - j| = 1`). A matrix `Q` on `E` defines the transfer family `Q_{(i,i+1)} = Q`,
`Q_{(i,i-1)} = Qᵀ`, and a boundary law `{ℓ_i, r_i}` for `Q` in the sense of Definition (11.8)
(`GibbsMeasure/Model/BoundaryLaw.lean`) defines the boundary law `ℓ_{(i,i+1)} = ℓ_i`,
`ℓ_{(i,i-1)} = r_iᵀ` in the sense of Definition (12.10). -/

section IntExample

open SimpleGraph

lemma hasse_int_adj (i j : ℤ) : (hasse ℤ).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  rw [hasse_adj, Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]

lemma neighborSet_hasse_int (i : ℤ) : (hasse ℤ).neighborSet i = ({i - 1, i + 1} : Set ℤ) := by
  ext j
  simp only [mem_neighborSet, hasse_int_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- `ℤ` is a locally finite graph. -/
noncomputable instance instLocallyFiniteHasseInt : (hasse ℤ).LocallyFinite := fun i ↦
  (show ((hasse ℤ).neighborSet i).Finite by
    rw [neighborSet_hasse_int]
    exact Set.toFinite _).fintype

lemma neighborFinset_hasse_int (i : ℤ) : (hasse ℤ).neighborFinset i = {i - 1, i + 1} := by
  ext j
  simp only [mem_neighborFinset, hasse_int_adj, Finset.mem_insert, Finset.mem_singleton]
  omega

variable (Q : E → E → ℝ≥0∞) (ℓ r : ℤ → E → ℝ≥0∞)

/-- The transfer family on `ℤ` of a matrix `Q`: `Q_{(i,i+1)} = Q`, `Q_{(i,i-1)} = Qᵀ` (and `1` on
non-adjacent pairs, so that the family is symmetric). -/
def intTransferFamily : ℤ → ℤ → E → E → ℝ≥0∞ := fun i j x y ↦
  if j = i + 1 then Q x y else if i = j + 1 then Q y x else 1

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_of_succ {i j : ℤ} (h : j = i + 1) (x y : E) :
    intTransferFamily Q i j x y = Q x y := by
  rw [intTransferFamily, ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_of_pred {i j : ℤ} (h : i = j + 1) (x y : E) :
    intTransferFamily Q i j x y = Q y x := by
  rw [intTransferFamily, ite_eq_right (by omega), ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intTransferFamily_symm (i j : ℤ) (x y : E) :
    intTransferFamily Q i j x y = intTransferFamily Q j i y x := by
  by_cases h1 : j = i + 1
  · rw [intTransferFamily_of_succ Q h1, intTransferFamily_of_pred Q h1]
  · by_cases h2 : i = j + 1
    · rw [intTransferFamily_of_pred Q h2, intTransferFamily_of_succ Q h2]
    · simp [intTransferFamily, h1, h2]

/-- The family `ℓ_{(i,i+1)} = ℓ_i`, `ℓ_{(i,i-1)} = r_i` of Example (12.11). -/
def intBoundaryLaw : ℤ → ℤ → E → ℝ≥0∞ := fun i j x ↦ if j = i + 1 then ℓ i x else r i x

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intBoundaryLaw_of_succ {i j : ℤ} (h : j = i + 1) (x : E) :
    intBoundaryLaw ℓ r i j x = ℓ i x := by
  rw [intBoundaryLaw, ite_eq_left h]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intBoundaryLaw_of_pred {i j : ℤ} (h : i = j + 1) (x : E) :
    intBoundaryLaw ℓ r i j x = r i x := by
  rw [intBoundaryLaw, ite_eq_right (by omega)]

variable {Q ℓ r}

/-- **Georgii Example (12.11).** A boundary law `{ℓ_i, r_i}` for `Q` in the sense of Definition
(11.8) is a boundary law for the transfer family `Q_{(i,i+1)} = Q`, `Q_{(i,i-1)} = Qᵀ` on `ℤ` in the
sense of Definition (12.10), with all constants `c_{ij} = 1`. -/
theorem Markov.IsBoundaryLaw.isBoundaryLaw_hasse_int (h : Markov.IsBoundaryLaw Q ℓ r) :
    IsBoundaryLaw (hasse ℤ) (intTransferFamily Q) (intBoundaryLaw ℓ r) where
  pos i j hij x := by
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · rw [intBoundaryLaw_of_succ ℓ r h1.symm]; exact h.left_pos i x
    · rw [intBoundaryLaw_of_pred ℓ r h1.symm]; exact h.right_pos i x
  ne_top i j hij x := by
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · rw [intBoundaryLaw_of_succ ℓ r h1.symm]; exact h.left_ne_top i x
    · rw [intBoundaryLaw_of_pred ℓ r h1.symm]; exact h.right_ne_top i x
  consistent i j hij := by
    refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun x ↦ ?_⟩
    rw [one_mul]
    rcases (hasse_int_adj i j).1 hij with h1 | h1
    · have e : ((hasse ℤ).neighborFinset i).erase j = {i - 1} := by
        rw [neighborFinset_hasse_int]
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [e, Finset.prod_singleton, intBoundaryLaw_of_succ ℓ r h1.symm]
      simp_rw [intBoundaryLaw_of_succ ℓ r (show i = i - 1 + 1 by omega),
        intTransferFamily_of_succ Q (show i = i - 1 + 1 by omega)]
      exact (h.tsum_left_mul_pred i x).symm
    · have e : ((hasse ℤ).neighborFinset i).erase j = {i + 1} := by
        rw [neighborFinset_hasse_int]
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [e, Finset.prod_singleton, intBoundaryLaw_of_pred ℓ r h1.symm]
      simp_rw [intBoundaryLaw_of_pred ℓ r (show i + 1 = i + 1 by rfl),
        intTransferFamily_of_pred Q (show i + 1 = i + 1 by rfl), mul_comm]
      exact (h.tsum_mul_right_succ i x).symm
  mass_ne_top i := by
    rw [neighborFinset_hasse_int]
    simp_rw [Finset.prod_pair (show i - 1 ≠ i + 1 by omega),
      intBoundaryLaw_of_succ ℓ r (show i = i - 1 + 1 by omega),
      intTransferFamily_of_succ Q (show i = i - 1 + 1 by omega),
      intBoundaryLaw_of_pred ℓ r (show i + 1 = i + 1 by rfl),
      intTransferFamily_of_pred Q (show i + 1 = i + 1 by rfl), h.tsum_left_mul_pred]
    have : ∀ x, ∑' y, r (i + 1) y * Q x y = r i x := fun x ↦ by
      simp_rw [mul_comm]
      exact h.tsum_mul_right_succ i x
    simp_rw [this]
    rw [h.tsum_left_mul_right i]
    exact ENNReal.one_ne_top

end IntExample


/-! ## Georgii Theorem (12.12)(a): the measure of a boundary law is a Markov chain -/

section MarkovChainOfBoundaryLaw

variable (Q : S → S → E → E → ℝ≥0∞) (ℓ : S → S → E → ℝ≥0∞)

/-- The transition matrix `P_{ij}(x, y) = ℓ_{ji}(y) Q_{ji}(y, x) / (ℓ_{ji} Q_{ji})(x)` of the Markov
chain of a boundary law (Georgii, proof of (12.12)(a)). -/
def boundaryLawTransition (i j : S) (x y : E) : ℝ≥0∞ :=
  ℓ j i y * Q i j x y / ∑' y', ℓ j i y' * Q i j x y'

variable {Q ℓ} [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] (hQ : IsTransferFamily G Q)
  (hℓ : IsBoundaryLaw G Q ℓ) (hG : G.IsTree)

include hQ hℓ in
omit [Nonempty E] in
lemma tsum_boundaryLawTransition_ne_zero {i j : S} (hij : G.Adj i j) (x : E) :
    ∑' y', ℓ j i y' * Q i j x y' ≠ 0 :=
  ((ENNReal.mul_pos (hℓ.pos hij.symm x).ne' (hQ.pos hij x x).ne').trans_le (ENNReal.le_tsum x)).ne'

include hQ hℓ in
omit [Nonempty E] in
lemma tsum_boundaryLawTransition_ne_top {i j : S} (hij : G.Adj i j) (x : E) :
    ∑' y', ℓ j i y' * Q i j x y' ≠ ⊤ := by
  simp_rw [hQ.symm i j]
  exact hℓ.tsum_mul_ne_top hQ.pos hij.symm x

include hQ hℓ in
omit [Nonempty E] in
lemma boundaryLawTransition_ne_top {i j : S} (hij : G.Adj i j) (x y : E) :
    boundaryLawTransition Q ℓ i j x y ≠ ⊤ :=
  ENNReal.div_ne_top (ENNReal.mul_ne_top (hℓ.ne_top hij.symm y) (hQ.ne_top hij x y))
    (tsum_boundaryLawTransition_ne_zero hQ hℓ hij x)

/-- The one-step Markov property of the measure (12.13) in finite volume: for `Λ` connected and
`j ∈ ∂Λ` with `i = j_Λ`, `μ(σ_j = y, σ_Δ = ξ_Δ) = P_{ij}(ξ_i, y) μ(σ_Δ = ξ_Δ)` for
`Δ = (Λ ∪ ∂Λ) \ {j}`. -/
theorem IsBoundaryLaw.measure_preimage_inter_cyl_erase {Λ : Finset S}
    (hΛ : (G.induce (Λ : Set S)).Connected) {j : S} (hj : j ∈ G.outerBoundary Λ) (ξ : S → E)
    (y : E) :
    boundaryLawMeasure hQ hℓ hG ((fun σ ↦ σ j) ⁻¹' {y} ∩ cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ)
      = boundaryLawTransition Q ℓ (G.anchor Λ j) j (ξ (G.anchor Λ j)) y
        * boundaryLawMeasure hQ hℓ hG (cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ) := by
  classical
  have hjH : j ∈ Λ ∪ G.outerBoundary Λ := Finset.mem_union_right _ hj
  have hjD : j ∉ (Λ ∪ G.outerBoundary Λ).erase j := Finset.notMem_erase j _
  have hinter : (fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl ((Λ ∪ G.outerBoundary Λ).erase j) ξ
      = cyl (Λ ∪ G.outerBoundary Λ) (Function.update ξ j y) := by
    conv_rhs => rw [← Finset.insert_erase hjH]
    rw [cyl_insert_eq_inter, Function.update_self, cyl_update_of_notMem hjD]
    rfl
  rw [hinter, hℓ.boundaryLawMeasure_cyl hQ hG hΛ, measure_cyl_eq_tsum_insert _ hjD ξ,
    Finset.insert_erase hjH]
  simp_rw [hℓ.boundaryLawMeasure_cyl hQ hG hΛ,
    boundaryLawWeight_update_of_mem_outerBoundary G Q hQ.symm ℓ hG.isAcyclic hΛ hj ξ]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, boundaryLawTransition, div_eq_mul_inv]
  set T := ∑' y', ℓ j (G.anchor Λ j) y' * Q (G.anchor Λ j) j (ξ (G.anchor Λ j)) y' with hT
  have hT0 : T ≠ 0 := tsum_boundaryLawTransition_ne_zero hQ hℓ (G.adj_anchor hj).symm _
  have hTt : T ≠ ⊤ := tsum_boundaryLawTransition_ne_top hQ hℓ (G.adj_anchor hj).symm _
  rw [show ∀ a b c : ℝ≥0∞, a * T⁻¹ * (b * (T * c)) = (T⁻¹ * T) * (b * (a * c)) from
    fun a b c ↦ by ring, ENNReal.inv_mul_cancel hT0 hTt, one_mul]

/-- **Georgii Theorem (12.12)(a), the Markov property.** The measure (12.13) of a boundary law on
a tree is a Markov chain in the sense of Definition (12.2), with transition matrices
`P_{ij}(x, y) = ℓ_{ji}(y) Q_{ji}(y, x) / (ℓ_{ji} Q_{ji})(x)`. -/
theorem IsBoundaryLaw.isMarkovChain_boundaryLawMeasure :
    IsMarkovChain G (boundaryLawMeasure hQ hℓ hG) where
  isProbabilityMeasure := inferInstance
  condExp i j hij y := by
    classical
    set B := (fun σ : S → E ↦ σ j) ⁻¹' {y} with hB
    have hBm : MeasurableSet B := measurable_pi_apply j (measurableSet_singleton y)
    let g : E → ℝ≥0∞ := fun x ↦ boundaryLawTransition Q ℓ i j x y
    have hgt : ∀ x, g x ≠ ⊤ := fun x ↦ boundaryLawTransition_ne_top hQ hℓ hij x y
    have hgm : Measurable[cylinderEvents ({i} : Set S)] fun σ : S → E ↦ g (σ i) :=
      (measurable_of_countable g).comp
        (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Set.mem_singleton i))
    have hm' : cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)
        ≤ cylinderEvents (G.past i j) :=
      cylinderEvents_mono (Set.singleton_subset_iff.2 (SimpleGraph.mem_past_self_of_adj hij))
    have hm₀ : cylinderEvents (X := fun _ : S ↦ E) (G.past i j) ≤ MeasurableSpace.pi :=
      cylinderEvents_le_pi
    -- the two set functions agree on the cylinders over finite subsets of the past
    have hcyl : ∀ (W : Finset S) (ω : S → E), (W : Set S) ⊆ G.past i j →
        (boundaryLawMeasure hQ hℓ hG).restrict B (cyl W ω)
          = (boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i)) (cyl W ω) := by
      intro W ω hW
      set Λ := SimpleGraph.hull hG.connected i W with hΛdef
      have hΛ : (G.induce (Λ : Set S)).Connected :=
        SimpleGraph.connected_induce_hull hG.connected i W
      have hiΛ : i ∈ Λ := SimpleGraph.mem_hull_self hG.connected i W
      have hΛp : ∀ x ∈ Λ, x ∈ G.past i j :=
        hG.isAcyclic.hull_subset_past hG.connected hij fun k hk ↦ hW (Finset.mem_coe.2 hk)
      have hjΛ : j ∉ Λ := fun h ↦ SimpleGraph.notMem_past_self i j (hΛp j h)
      have hjB : j ∈ G.outerBoundary Λ := (G.mem_outerBoundary).2 ⟨hjΛ, i, hiΛ, hij.symm⟩
      have hanc : G.anchor Λ j = i := hG.isAcyclic.anchor_eq hΛ hjB hiΛ hij.symm
      set Δ := (Λ ∪ G.outerBoundary Λ).erase j with hΔdef
      have hWΔ : W ⊆ Δ := fun k hk ↦ Finset.mem_erase.2
        ⟨fun h ↦ SimpleGraph.notMem_past_self i j (h ▸ hW (Finset.mem_coe.2 hk)),
          Finset.mem_union_left _ (SimpleGraph.subset_hull _ _ _ hk)⟩
      have hiΔ : i ∈ Δ := Finset.mem_erase.2 ⟨hij.ne, Finset.mem_union_left _ hiΛ⟩
      rw [measure_cyl_eq_lintegral_lambdaCount _ (Finset.disjoint_sdiff (s := W) (t := Δ)) ω,
        measure_cyl_eq_lintegral_lambdaCount _ (Finset.disjoint_sdiff (s := W) (t := Δ)) ω,
        Finset.union_sdiff_of_subset hWΔ]
      refine lintegral_congr fun ξ ↦ ?_
      rw [Measure.restrict_apply (measurableSet_cyl _ _), Set.inter_comm,
        withDensity_apply _ (measurableSet_cyl _ _),
        setLIntegral_congr_fun (measurableSet_cyl _ _) (g := fun _ ↦ g (ξ i))
          (fun σ hσ ↦ by simp only [mem_cyl.1 hσ i hiΔ]),
        setLIntegral_const]
      have := hℓ.measure_preimage_inter_cyl_erase hQ hG hΛ hjB ξ y
      rw [hanc] at this
      exact this
    have htrim : ((boundaryLawMeasure hQ hℓ hG).restrict B).trim hm₀
        = ((boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i))).trim hm₀ := by
      refine ext_of_generate_finite (cylindersIn (G.past i j))
        (cylinderEvents_eq_generateFrom_cylindersIn _) (isPiSystem_cylindersIn _) ?_ ?_
      · rintro _ ⟨W, ω, hW, rfl⟩
        rw [trim_measurableSet_eq hm₀ (measurableSet_cylinderEvents_cyl hW ω),
          trim_measurableSet_eq hm₀ (measurableSet_cylinderEvents_cyl hW ω)]
        exact hcyl W ω hW
      · have h := hcyl ∅ (fun _ ↦ y) (by simp)
        rw [cyl_empty] at h
        rw [trim_measurableSet_eq hm₀ MeasurableSet.univ,
          trim_measurableSet_eq hm₀ MeasurableSet.univ]
        exact h
    have key : ∀ t, MeasurableSet[cylinderEvents (G.past i j)] t →
        boundaryLawMeasure hQ hℓ hG (B ∩ t) = ∫⁻ σ in t, g (σ i) ∂(boundaryLawMeasure hQ hℓ hG)
            := by
      intro t ht
      have h1 : ((boundaryLawMeasure hQ hℓ hG).restrict B).trim hm₀ t
          = ((boundaryLawMeasure hQ hℓ hG).withDensity (fun σ ↦ g (σ i))).trim hm₀ t := by
        rw [htrim]
      rw [trim_measurableSet_eq hm₀ ht, trim_measurableSet_eq hm₀ ht,
        Measure.restrict_apply (hm₀ _ ht), withDensity_apply _ (hm₀ _ ht), Set.inter_comm] at h1
      exact h1
    have h_past := (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq hm₀ hBm
      (measure_ne_top _ _) (hgm.mono hm' le_rfl).stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun σ ↦ hgt (σ i))).2 key
    have h_i := (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm'.trans hm₀) hBm
      (measure_ne_top _ _) hgm.stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun σ ↦ hgt (σ i))).2 fun t ht ↦ key t (hm' _ ht)
    exact h_past.symm.trans h_i

end MarkovChainOfBoundaryLaw

end MeasureTheory.GibbsMeasure.Tree

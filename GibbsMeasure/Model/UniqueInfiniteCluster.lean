/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.OceanNetwork

/-!
# Uniqueness of the infinite cluster in the plane, and the tail property of oceans

Georgii, in the proof of Theorem (18.17), uses that `{ξ⁰_P(G, ·) ≠ ∅}` is a tail event: that
whether a subset of the plane contains an ocean (Definition (18.6)) is unchanged when finitely
many sites are added or removed.  The general reduction, in
`GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/InfiniteCluster.lean`
(`SimpleGraph.oceanPart_nonempty_congr_of_finite_diff`), leaves one genuinely planar statement:

**a subset of `ℤ²` all of whose `*`-islands are finite has at most one infinite
nearest-neighbour cluster** (`Peierls.eq_of_infinite_supp_of_forall_finite_island`).

This is false on the line `ℤ`, where `ℤ \ {0}` has finite islands and two infinite clusters, and
it is the reason that the tail property is a two-dimensional fact.

## Timár's boundary connectivity, for an arbitrary connected set

The proof is Timár's argument (Proc. AMS 141 (2013)) in the generality he states it: for a
connected set `D ⊆ ℤ²` — finite or not — and a connected component `Z` of `Dᶜ`, the bonds
between `D` and `Z` are connected in the plaquette-adjacency graph (`edgesBetween_connected`),
and the sites of `Z` adjacent to `D` are `*`-connected (`boundary_starConnected`).  The proof is
the one of `Peierls.outerEdgeBoundary_connected` in `GibbsMeasure/Model/Contours.lean`, which is
the special case of a finite `D` and `Z = outside D`; only the mod-two coboundary identity
`edgesBetween_chi` and the connectivity of `D` and `Z` are used, and neither needs finiteness.

Given two distinct infinite clusters `C₁`, `C₂` of `ℤ² \ Y`, the sites of the component of `C₂`
in `C₁ᶜ` adjacent to `C₁` lie in `Y` and form a `*`-connected set, hence a finite one; but every
lattice walk from `C₂` to `C₁` must pass through it, and two sites far outside a box containing
it are joined by a walk outside that box (`Peierls.reachIn_compl_box`).

## Main declarations

* `Peierls.edgesBetween_connected`, `Peierls.boundary_starConnected`: Timár's theorem.
* `Peierls.eq_of_infinite_supp_of_forall_finite_island`: uniqueness of the infinite cluster.
* `Peierls.oceanPart_nonempty_congr_of_finite_diff`: **the tail property of oceans in the
  plane**, `{ξ⁰_P ≠ ∅}` is unchanged by a finite modification of `V_P(G, ·)`.
* `Peierls.isOceanIn_univ_iff`: being an ocean in the plane as a countable condition, the form
  in which `{ξ⁰_P(G, ·) ≠ ∅}` is seen to be measurable.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure Set

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### Timár's boundary connectivity for an arbitrary connected set -/

section Timar

variable {D Z : Set Site}

/-- When `Z` is closed under adjacency off `D`, a bond lies between `D` and `Z` exactly when one
endpoint lies in `Z` and the other does not. -/
lemma mk_mem_edgesBetween_iff_of_closed (hDZ : Disjoint D Z)
    (hclosed : ∀ z ∈ Z, ∀ w, (latticeGraph 2).Adj z w → w ∉ Z → w ∈ D) {u v : Site}
    (huv : (latticeGraph 2).Adj u v) :
    s(u, v) ∈ (latticeGraph 2).edgesBetween D Z ↔ (u ∈ Z ∧ v ∉ Z) ∨ (v ∈ Z ∧ u ∉ Z) := by
  rw [SimpleGraph.mk_mem_edgesBetween, and_iff_right huv]
  constructor
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact Or.inr ⟨hv, Set.disjoint_left.1 hDZ hu⟩
    · exact Or.inl ⟨hu, Set.disjoint_left.1 hDZ hv⟩
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact Or.inr ⟨hclosed u hu v huv hv, hu⟩
    · exact Or.inl ⟨hclosed v hv u huv.symm hu, hv⟩

open Classical in
/-- The `ZMod 2` indicator of the bonds between `D` and `Z` is the coboundary of the indicator of
`Z`, when `Z` is closed under adjacency off `D`. -/
lemma edgesBetween_chi (hDZ : Disjoint D Z)
    (hclosed : ∀ z ∈ Z, ∀ w, (latticeGraph 2).Adj z w → w ∉ Z → w ∈ D) {u v : Site}
    (huv : (latticeGraph 2).Adj u v) :
    (if s(u, v) ∈ (latticeGraph 2).edgesBetween D Z then (1 : ZMod 2) else 0)
      = (if u ∈ Z then (1 : ZMod 2) else 0) + (if v ∈ Z then (1 : ZMod 2) else 0) := by
  by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z
  · have hOB : s(u, v) ∉ (latticeGraph 2).edgesBetween D Z := by
      rw [mk_mem_edgesBetween_iff_of_closed hDZ hclosed huv]
      rintro (⟨-, h⟩ | ⟨-, h⟩) <;> contradiction
    rw [ite_eq_right hOB, ite_eq_left hu, ite_eq_left hv]
    decide
  · have hOB : s(u, v) ∈ (latticeGraph 2).edgesBetween D Z :=
      (mk_mem_edgesBetween_iff_of_closed hDZ hclosed huv).2 (Or.inl ⟨hu, hv⟩)
    rw [ite_eq_left hOB, ite_eq_left hu, ite_eq_right hv]
    decide
  · have hOB : s(u, v) ∈ (latticeGraph 2).edgesBetween D Z :=
      (mk_mem_edgesBetween_iff_of_closed hDZ hclosed huv).2 (Or.inr ⟨hv, hu⟩)
    rw [ite_eq_left hOB, ite_eq_right hu, ite_eq_left hv]
    decide
  · have hOB : s(u, v) ∉ (latticeGraph 2).edgesBetween D Z := by
      rw [mk_mem_edgesBetween_iff_of_closed hDZ hclosed huv]
      rintro (⟨h, -⟩ | ⟨h, -⟩) <;> contradiction
    rw [ite_eq_right hOB, ite_eq_right hu, ite_eq_right hv]
    decide

/-- **Timár's boundary connectivity**, for an arbitrary connected set of sites.  Let `D ⊆ ℤ²` be
connected and let `Z` be a connected set disjoint from `D` and closed under adjacency off `D`
(a connected component of `Dᶜ`).  Then the bonds between `D` and `Z`, if there are any, are
connected in the plaquette-adjacency graph.

The `ZMod 2` indicator `κ` of the bonds reachable from a given boundary bond has vanishing
plaquette sums, hence is the coboundary of a site labelling `φ`; `φ` is constant on `D` and on
`Z`, so `κ` takes the same value on every bond between them. -/
theorem edgesBetween_connected (hD : ∀ u ∈ D, ∀ v ∈ D, ReachIn (latticeGraph 2) D u v)
    (hZ : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (latticeGraph 2) Z u v) (hDZ : Disjoint D Z)
    (hclosed : ∀ z ∈ Z, ∀ w, (latticeGraph 2).Adj z w → w ∉ Z → w ∈ D)
    (hne : ((latticeGraph 2).edgesBetween D Z).Nonempty) :
    (bondGraph.induce ((latticeGraph 2).edgesBetween D Z)).Connected := by
  classical
  rw [induce_connected_iff]
  refine ⟨hne, ?_⟩
  intro e₀ f he₀ hf
  by_contra hcon
  set B := (latticeGraph 2).edgesBetween D Z with hB
  set A : Set (Sym2 Site) := {e | ReachIn bondGraph B e₀ e} with hA
  have he₀A : e₀ ∈ A := ReachIn.refl he₀
  have hfA : f ∉ A := hcon
  have hAsub : A ⊆ B := fun e he ↦ he.mem_right
  have hclosedA : ∀ {e g : Sym2 Site} {x : Site}, e ∈ A → g ∈ B →
      e ∈ plaquette x → g ∈ plaquette x → g ∈ A := by
    intro e g x he hg hex hgx
    by_cases heg : e = g
    · exact heg ▸ he
    · exact SimpleGraph.ReachableIn.trans he (ReachIn.of_adj (hAsub he) hg ⟨heg, x, hex, hgx⟩)
  set κ : Sym2 Site → ZMod 2 := fun e ↦ if e ∈ A then 1 else 0 with hκ
  have hP : ∀ t u : ℤ, κ s(mk t u, mk (t + 1) u) + κ s(mk t u, mk t (u + 1))
      + κ s(mk (t + 1) u, mk (t + 1) (u + 1)) + κ s(mk t (u + 1), mk (t + 1) (u + 1)) = 0 := by
    intro t u
    by_cases hA1 : s(mk t u, mk (t + 1) u) ∈ A ∨ s(mk t u, mk t (u + 1)) ∈ A
        ∨ s(mk (t + 1) u, mk (t + 1) (u + 1)) ∈ A ∨ s(mk t (u + 1), mk (t + 1) (u + 1)) ∈ A
    · have hkOB : ∀ g, g ∈ plaquette (mk t u) → κ g = if g ∈ B then (1 : ZMod 2) else 0 := by
        intro g hg
        by_cases hgOB : g ∈ B
        · rw [ite_eq_left hgOB]
          have hgA : g ∈ A := by
            rcases hA1 with h | h | h | h
            · exact hclosedA h hgOB (mem_plaquette₁ t u) hg
            · exact hclosedA h hgOB (mem_plaquette₂ t u) hg
            · exact hclosedA h hgOB (mem_plaquette₃ t u) hg
            · exact hclosedA h hgOB (mem_plaquette₄ t u) hg
          simp [hκ, hgA]
        · rw [ite_eq_right hgOB]
          have hgA : g ∉ A := fun h' ↦ hgOB (hAsub h')
          simp [hκ, hgA]
      rw [hkOB _ (mem_plaquette₁ t u), hkOB _ (mem_plaquette₂ t u),
        hkOB _ (mem_plaquette₃ t u), hkOB _ (mem_plaquette₄ t u),
        edgesBetween_chi hDZ hclosed (adj_mk_horiz t u),
        edgesBetween_chi hDZ hclosed (adj_mk_vert t u),
        edgesBetween_chi hDZ hclosed (adj_mk_vert (t + 1) u),
        edgesBetween_chi hDZ hclosed (adj_mk_horiz t (u + 1))]
      exact (by decide : ∀ a b c d : ZMod 2, (a + b) + (a + c) + (b + d) + (c + d) = 0) _ _ _ _
    · push Not at hA1
      obtain ⟨h1, h2, h3, h4⟩ := hA1
      simp only [hκ, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
      decide
  obtain ⟨φ, hφ⟩ := exists_potential κ hP
  -- `φ` is constant along walks inside `D` and inside `Z`
  have hφD : ∀ {p q : Site}, ReachIn (latticeGraph 2) D p q → φ p = φ q := by
    intro p q h
    refine h.invariant φ ?_
    intro a b ha hb hab
    have hOB : s(a, b) ∉ B := by
      rw [hB, mk_mem_edgesBetween_iff_of_closed hDZ hclosed hab]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Set.disjoint_left.1 hDZ ha h1
      · exact Set.disjoint_left.1 hDZ hb h1
    have hAe : s(a, b) ∉ A := fun h' ↦ hOB (hAsub h')
    have hsum := hφ a b hab
    simp only [hκ, ite_eq_right hAe] at hsum
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hsum
  have hφZ : ∀ {p q : Site}, ReachIn (latticeGraph 2) Z p q → φ p = φ q := by
    intro p q h
    refine h.invariant φ ?_
    intro a b ha hb hab
    have hOB : s(a, b) ∉ B := by
      rw [hB, mk_mem_edgesBetween_iff_of_closed hDZ hclosed hab]
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact h2 hb
      · exact h2 ha
    have hAe : s(a, b) ∉ A := fun h' ↦ hOB (hAsub h')
    have hsum := hφ a b hab
    simp only [hκ, ite_eq_right hAe] at hsum
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hsum
  -- endpoints of `e₀` and `f`
  obtain ⟨c₁, hc₁, d₁, hd₁, hadj₁, he₀eq⟩ := he₀
  obtain ⟨c₂, hc₂, d₂, hd₂, hadj₂, hfeq⟩ := hf
  have h1 : φ c₁ = φ c₂ := hφD (hD c₁ hc₁ c₂ hc₂)
  have h2 : φ d₁ = φ d₂ := hφZ (hZ d₁ hd₁ d₂ hd₂)
  have h3 : φ c₁ + φ d₁ = 1 := by
    have hsum := hφ c₁ d₁ hadj₁
    rw [← he₀eq] at hsum
    have hκe : κ e₀ = 1 := by simp [hκ, he₀A]
    rw [hκe] at hsum
    exact hsum
  have h4 : φ c₂ + φ d₂ = 0 := by
    have hsum := hφ c₂ d₂ hadj₂
    rw [← hfeq] at hsum
    have hκf : κ f = 0 := by simp [hκ, hfA]
    rw [hκf] at hsum
    exact hsum
  rw [h1, h2, h4] at h3
  exact absurd h3 (by decide)

open Classical in
/-- The endpoint of a bond lying in `Z` (junk if there is none). -/
noncomputable def endIn (Z : Set Site) (e : Sym2 Site) : Site :=
  if h : ∃ j ∈ Z, j ∈ e then h.choose else 0

lemma endIn_eq (hDZ : Disjoint D Z) {i j : Site} (hi : i ∈ D) (hj : j ∈ Z) :
    endIn Z s(i, j) = j := by
  unfold endIn
  split_ifs with h
  · obtain ⟨hZ, hmem⟩ := h.choose_spec
    rcases Sym2.mem_iff.1 hmem with h' | h'
    · exact absurd (h' ▸ hZ) (Set.disjoint_left.1 hDZ hi)
    · exact h'
  · exact absurd ⟨j, hj, Sym2.mem_mk_right i j⟩ h

lemma image_endIn_edgesBetween (hDZ : Disjoint D Z) :
    endIn Z '' (latticeGraph 2).edgesBetween D Z
      = {j | j ∈ Z ∧ ∃ i ∈ D, (latticeGraph 2).Adj i j} := by
  ext j
  constructor
  · rintro ⟨e, ⟨i, hi, j', hj', hij, rfl⟩, rfl⟩
    rw [endIn_eq hDZ hi hj']
    exact ⟨hj', i, hi, hij⟩
  · rintro ⟨hj, i, hi, hij⟩
    exact ⟨s(i, j), ⟨i, hi, j, hj, hij, rfl⟩, endIn_eq hDZ hi hj⟩

lemma endIn_mem {e : Sym2 Site} (hDZ : Disjoint D Z) (he : e ∈ (latticeGraph 2).edgesBetween D Z) :
    endIn Z e ∈ e ∧ endIn Z e ∈ Z := by
  obtain ⟨i, hi, j, hj, -, rfl⟩ := he
  rw [endIn_eq hDZ hi hj]
  exact ⟨Sym2.mem_mk_right i j, hj⟩

/-- **Timár's boundary connectivity, vertex form.**  For a connected set `D ⊆ ℤ²` and a connected
component `Z` of `Dᶜ`, the sites of `Z` adjacent to `D` form a `*`-connected set. -/
theorem boundary_starConnected (hD : ∀ u ∈ D, ∀ v ∈ D, ReachIn (latticeGraph 2) D u v)
    (hZ : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (latticeGraph 2) Z u v) (hDZ : Disjoint D Z)
    (hclosed : ∀ z ∈ Z, ∀ w, (latticeGraph 2).Adj z w → w ∉ Z → w ∈ D)
    (hne : ((latticeGraph 2).edgesBetween D Z).Nonempty) :
    ((starLatticeGraph 2).induce {j | j ∈ Z ∧ ∃ i ∈ D, (latticeGraph 2).Adj i j}).Connected := by
  rw [← image_endIn_edgesBetween hDZ]
  refine (edgesBetween_connected hD hZ hDZ hclosed hne).induce_image_of_forall_adj ?_
  intro e f he hf hef
  obtain ⟨-, x, hex, hfx⟩ := hef
  by_cases heq : endIn Z e = endIn Z f
  · exact Or.inl heq
  · refine Or.inr ⟨heq, ?_⟩
    rw [Fin.forall_fin_two]
    exact abs_sub_le_one_of_mem_plaquette hex hfx (endIn_mem hDZ he).1 (endIn_mem hDZ hf).1

end Timar

/-! ### Uniqueness of the infinite cluster -/

/-- **Uniqueness of the infinite cluster.**  If every `*`-island of `X ⊆ ℤ²` is finite, then
`X` has at most one infinite cluster.

Two distinct infinite clusters `C₁`, `C₂` would have the following: the sites adjacent to `C₁`
in the component `Z` of `C₂` in `C₁ᶜ` lie outside `X`, are `*`-connected by Timár's theorem,
hence lie in a single island and form a finite set `B`; but a lattice walk outside a box
containing `B` joins a far site of `C₂ ⊆ Z` to a far site of `C₁`, and its first exit from `Z`
is a site of `B`. -/
theorem eq_of_infinite_supp_of_forall_finite_island {X : Set Site}
    (hX : ∀ c : ((starLatticeGraph 2).induce (Set.univ \ X)).ConnectedComponent, c.supp.Finite)
    (c₁ c₂ : ((latticeGraph 2).induce X).ConnectedComponent) (h₁ : c₁.supp.Infinite)
    (h₂ : c₂.supp.Infinite) : c₁ = c₂ := by
  classical
  by_contra hne
  set C₁ : Set Site := Subtype.val '' c₁.supp with hC₁
  set C₂ : Set Site := Subtype.val '' c₂.supp with hC₂
  have hC₁X : C₁ ⊆ X := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hC₂X : C₂ ⊆ X := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hC₁conn : ∀ u ∈ C₁, ∀ v ∈ C₁, ReachIn (latticeGraph 2) C₁ u v :=
    (SimpleGraph.connected_induce_iff_forall_reachableIn.1
      (SimpleGraph.connected_induce_image_val_supp c₁)).2
  have hC₂conn : ∀ u ∈ C₂, ∀ v ∈ C₂, ReachIn (latticeGraph 2) C₂ u v :=
    (SimpleGraph.connected_induce_iff_forall_reachableIn.1
      (SimpleGraph.connected_induce_image_val_supp c₂)).2
  -- a site of `X` adjacent to `C₁` lies in `C₁`
  have hC₁adj : ∀ d ∈ C₁, ∀ z ∈ X, (latticeGraph 2).Adj d z → z ∈ C₁ := by
    rintro _ ⟨d, hd, rfl⟩ z hz hadj
    exact ⟨⟨z, hz⟩, SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c₁ hd
      (SimpleGraph.induce_adj.2 hadj), rfl⟩
  -- `C₂` is disjoint from `C₁`
  have hdisj : ∀ z ∈ C₂, z ∉ C₁ := by
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', hzz'⟩
    obtain rfl : z' = z := Subtype.ext hzz'
    exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hz' hz)
  obtain ⟨⟨q₀, hq₀X⟩, hq₀⟩ := c₂.nonempty_supp
  have hq₀C₂ : q₀ ∈ C₂ := ⟨_, hq₀, rfl⟩
  -- the component `Z` of `C₂` in `C₁ᶜ`
  set Z : Set Site := {z | ReachIn (latticeGraph 2) C₁ᶜ q₀ z} with hZ
  have hZC₁ : Disjoint C₁ Z := Set.disjoint_left.2 fun d hd hdZ ↦ hdZ.mem_right hd
  have hZconn : ∀ u ∈ Z, ∀ v ∈ Z, ReachIn (latticeGraph 2) Z u v := fun u hu v hv ↦
    (reachIn_setOf_reachIn hu).symm.trans (reachIn_setOf_reachIn hv)
  have hclosed : ∀ z ∈ Z, ∀ w, (latticeGraph 2).Adj z w → w ∉ Z → w ∈ C₁ := by
    intro z hz w hzw hw
    by_contra hwC₁
    exact hw (hz.trans (ReachIn.of_adj hz.mem_right hwC₁ hzw))
  have hC₂Z : C₂ ⊆ Z := fun z hz ↦ (hC₂conn q₀ hq₀C₂ z hz).mono fun y hy ↦ hdisj y hy
  -- the boundary `B` of `Z` towards `C₁`
  set B : Set Site := {j | j ∈ Z ∧ ∃ i ∈ C₁, (latticeGraph 2).Adj i j} with hB
  -- every walk from `Z` to `C₁` passes through `B`
  have hexit : ∀ {a b : Site} (p : (latticeGraph 2).Walk a b), a ∈ Z → b ∈ C₁ →
      ∃ w ∈ p.support, w ∈ B := by
    intro a b p ha hb
    obtain ⟨w, x, q, hq, hwx, hx, hxp⟩ :=
      SimpleGraph.exists_walk_until_exit (s := Z) p ha (Set.disjoint_left.1 hZC₁ hb)
    refine ⟨w, (hq w q.end_mem_support).2, (hq w q.end_mem_support).1, x, ?_, hwx.symm⟩
    exact hclosed w (hq w q.end_mem_support).1 x hwx hx
  -- `B` is nonempty
  obtain ⟨⟨p₀, hp₀X⟩, hp₀⟩ := c₁.nonempty_supp
  have hp₀C₁ : p₀ ∈ C₁ := ⟨_, hp₀, rfl⟩
  have hq₀Z : q₀ ∈ Z := ReachIn.refl (hdisj q₀ hq₀C₂)
  obtain ⟨b₀, hb₀⟩ : ∃ b, b ∈ B := by
    obtain ⟨p, -⟩ := (reachIn_univ q₀ p₀).exists_walk
    obtain ⟨w, -, hw⟩ := hexit p hq₀Z hp₀C₁
    exact ⟨w, hw⟩
  -- `B ⊆ univ \ X`
  have hBX : B ⊆ Set.univ \ X := by
    rintro j ⟨hjZ, i, hi, hij⟩
    refine ⟨trivial, fun hjX ↦ ?_⟩
    exact Set.disjoint_left.1 hZC₁ (hC₁adj i hi j hjX hij) hjZ
  -- `B` is `*`-connected, hence finite
  obtain ⟨hb₀Z, i₀, hi₀, hi₀b₀⟩ := id hb₀
  have hBconn := boundary_starConnected hC₁conn hZconn hZC₁ hclosed
    ⟨s(i₀, b₀), i₀, hi₀, b₀, hb₀Z, hi₀b₀, rfl⟩
  have hBfin : B.Finite := by
    refine ((hX (((starLatticeGraph 2).induce (Set.univ \ X)).connectedComponentMk
      ⟨b₀, hBX hb₀⟩)).image Subtype.val).subset fun j hj ↦ ?_
    refine ⟨⟨j, hBX hj⟩, ?_, rfl⟩
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.eq.2
      ((hBconn.preconnected ⟨b₀, hb₀⟩ ⟨j, hj⟩).induce_mono le_rfl hBX)).symm
  -- far sites of `C₁` and `C₂` are joined outside a box containing `B`
  obtain ⟨N, hBN⟩ := exists_subset_box hBfin
  obtain ⟨p, hpC₁, hpN⟩ := (h₁.image Subtype.val_injective.injOn).exists_notMem_finite
    (box_finite N)
  obtain ⟨q, hqC₂, hqN⟩ := (h₂.image Subtype.val_injective.injOn).exists_notMem_finite
    (box_finite N)
  obtain ⟨r, hr⟩ := (reachIn_compl_box hqN hpN).exists_walk
  obtain ⟨w, hw, hwB⟩ := hexit r (hC₂Z hqC₂) hpC₁
  exact hr w hw (hBN hwB)

/-- The property `hR₁` of `SimpleGraph.IsOceanIn.isOceanIn_infiniteClusters_diff` holds in the
plane: a subset of `ℤ²` with only finite `*`-islands has at most one infinite cluster. -/
theorem forall_finite_island_imp_eq_of_infinite_supp :
    ∀ X ⊆ (Set.univ : Set Site),
      (∀ c : ((starLatticeGraph 2).induce (Set.univ \ X)).ConnectedComponent, c.supp.Finite) →
      ∀ c₁ c₂ : ((latticeGraph 2).induce X).ConnectedComponent,
        c₁.supp.Infinite → c₂.supp.Infinite → c₁ = c₂ :=
  fun _ _ hX c₁ c₂ h₁ h₂ ↦ eq_of_infinite_supp_of_forall_finite_island hX c₁ c₂ h₁ h₂

/-- The `*`-neighbour graph of the plane is locally finite. -/
lemma starLatticeGraph_neighborSet_finite (v : Site) :
    ((starLatticeGraph 2).neighborSet v).Finite := by
  refine ((box_finite 1).image (· + v)).subset fun w hw ↦ ?_
  refine ⟨w - v, fun i ↦ ?_, sub_add_cancel w v⟩
  have h := (starLatticeGraph_two_adj_iff v w).1 hw
  rw [Pi.sub_apply, abs_sub_comm]
  fin_cases i
  · exact_mod_cast h.2.1
  · exact_mod_cast h.2.2

/-! ### The tail property of oceans in the plane -/

/-- **Containing an ocean is a tail property of a subset of the plane**: if `W` and `W'` differ
by finitely many sites, then `W` contains an ocean iff `W'` does.  With Georgii (18.3) this is
`{ξ⁰_P(G, ·) ≠ ∅} ∈ 𝒯`, the fact his proof of Theorem (18.17) invokes without proof. -/
theorem oceanPart_nonempty_congr_of_finite_diff {W W' : Set Site} (h₁ : (W \ W').Finite)
    (h₂ : (W' \ W).Finite) :
    (SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ W).Nonempty ↔
      (SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ W').Nonempty :=
  SimpleGraph.oceanPart_nonempty_congr_of_finite_diff (latticeGraph_le_starLatticeGraph 2)
    (fun _ hF ↦ nonempty_infiniteClusters_univ_diff (latticeGraph_le_starLatticeGraph 2) hF)
    starLatticeGraph_neighborSet_finite forall_finite_island_imp_eq_of_infinite_supp
    (Set.subset_univ W) (Set.subset_univ W') h₁ h₂

/-! ### Being an ocean in the plane as a countable condition -/

/-- **Georgii (18.6) in the plane, as a countable condition**: `X` is an ocean in `ℤ²` iff it is
nonempty, any two of its sites are joined inside it, and the `*`-cluster in `Xᶜ` of every site
off `X` lies in some box. -/
theorem isOceanIn_univ_iff {X : Set Site} :
    SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ X ↔
      X.Nonempty ∧ (∀ u ∈ X, ∀ v ∈ X, ReachIn (latticeGraph 2) X u v) ∧
        ∀ y, y ∈ X ∨ ∃ n : ℕ, ∀ z, ReachIn (starLatticeGraph 2) (Set.univ \ X) y z → z ∈ box n := by
  constructor
  · intro h
    refine ⟨h.nonempty,
      (SimpleGraph.connected_induce_iff_forall_reachableIn.1 h.connected).2, fun y ↦ ?_⟩
    by_cases hy : y ∈ X
    · exact Or.inl hy
    · refine Or.inr ?_
      have hyX : y ∈ Set.univ \ X := ⟨trivial, hy⟩
      have hfin := (h.finite_island (((starLatticeGraph 2).induce
        (Set.univ \ X)).connectedComponentMk ⟨y, hyX⟩)).image Subtype.val
      rw [image_val_supp_connectedComponentMk_eq hyX] at hfin
      obtain ⟨n, hn⟩ := exists_subset_box hfin
      exact ⟨n, fun z hz ↦ hn hz⟩
  · rintro ⟨hne, hconn, hisl⟩
    refine ⟨Set.subset_univ X, SimpleGraph.connected_induce_iff_forall_reachableIn.2 ⟨hne, hconn⟩,
      fun c ↦ ?_⟩
    obtain ⟨⟨y, hyX⟩, hy⟩ := c.nonempty_supp
    rcases hisl y with hyX' | ⟨n, hn⟩
    · exact absurd hyX' hyX.2
    · refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hy
      rw [← hy, image_val_supp_connectedComponentMk_eq hyX]
      exact (box_finite n).subset fun z hz ↦ hn z hz

end MeasureTheory.GibbsMeasure.Peierls

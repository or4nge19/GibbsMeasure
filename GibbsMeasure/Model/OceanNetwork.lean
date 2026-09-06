/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PlanarCrossing

/-!
# Georgii Lemma (18.16), Steps 2 and 3: barriers, crossings and the ocean

Planar combinatorics on `ℤ²` for Georgii's Lemma (18.16).  Throughout, `W` is a subset of `ℤ²`
— in the application `W = V(G, ω)` of Georgii (18.3) — and `Peierls.IsCrossCentre W i` is
Georgii's event `X` at the site `i`: `i` lies in an infinite cluster of `W` in each of the four
closed quadrants with vertex `i`.

## Step 2

`reachIn_upper_of_infiniteClusters_of_barrier` is Georgii's "`π_n^+` is bound to intersect
`π_{n+1}^-`": if `(k, 0)` and `(k', 0)` (`-N < k < k' < N`) carry infinite clusters of `W` in the
quarter planes `{i₁ ≥ k, i₂ ≥ 0}` resp. `{i₁ ≤ k', i₂ ≥ 0}`, and the barrier row `[-N, N] × {h}`
misses `W`, then `(k, 0)` and `(k', 0)` are joined inside `W` in the closed upper half-plane.  The
barrier forces both clusters to leave the box `[-N, N] × [0, h-1]` sideways, and the two
crossings so obtained meet by the planar crossing lemma
`Peierls.inter_nonempty_of_crossings` of `GibbsMeasure/Model/PlanarCrossing.lean`.

`motion` and `reachIn_of_motion` transport that statement along the isometries of `ℤ²`, giving
`reachIn_up`, `reachIn_down`, `reachIn_right`, `reachIn_left` at an arbitrary line, and
`reachIn_up_of_crossCentres` etc. their form at two cross centres.

## Step 3

`finite_reachIn_star_of_circuit` is the separation statement Georgii replaces by Figure 18.2:
four lattice walks closing into a circuit — above the row `t`, right of the column `b`, below the
row `s`, left of the column `a` — trap the `*`-cluster of any site of the open box
`(a, b) × (s, t)` in the complement of the circuit.  Its proof is the mod-two side function
`Peierls.exists_side_fun` of the circuit together with the crossing parity
`sum_bondChain_hbond`: only the top piece of the circuit can cross the vertical ray above `p`,
and it does so an odd number of times because it runs from the column `a` to the column `b`.

`exists_isOceanIn_of_crossCentres` assembles Steps 2 and 3: given barriers in all four
directions and a set `R` of cross centres containing the origin, meeting the vertical axis
arbitrarily far up and down, and containing for any two of its heights `s`, `t` on that axis
points `(k, s)` and `(k, t)` with `k` arbitrarily large positive and negative, the cluster of the
origin in `W` is an **ocean** (`SimpleGraph.IsOceanIn`).  The circuit around a site `p` off the
cluster is built from four Step-2 connections at the cross centres `(a, s)`, `(a, t)`, `(b, s)`,
`(b, t)` surrounding `p`, and all four lie in the cluster of the origin because each is linked to
it through the axis cross centres.

`isOceanIn_univ` is the degenerate case `λ^C(G) = 1` of Georgii's proof: the whole plane is an
ocean.

## Auxiliary results

* `exists_exit_rect`, `exists_connected_right`, `exists_connected_left` — escaping a rectangle
  inside an infinite cluster, and the two crossings of Step 2.
* `sum_ite_hbond_eq`, `sum_bondChain_hbond`, `psi_sum_Ioc`, `psi_const_outside_box`,
  `reachIn_star_subset_box_of_psi` — the mod-two crossing number of a lattice walk and the
  trapping argument.
* `mem_infiniteClusters_iff_forall_exists` — membership in an infinite cluster as a countable
  condition; this is what makes Georgii's event `X` measurable.
* `isCrossCentre_add` — cross centres translate with the pattern.
* `reachIn_univ`, `mem_infiniteClusters_univ` — the plane is connected and percolates.

Everything in this file is about subsets of `ℤ²`; nothing here mentions a random field.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### Segments of the lattice -/

/-- The horizontal segment `[a, b] × {y}` of `ℤ²`: the degenerate rectangle of height zero. -/
abbrev hseg (a b y : ℤ) : Set Site := rect a b y y

/-- The vertical segment `{t} × [c, e]` of `ℤ²`: the degenerate rectangle of width zero. -/
abbrev vseg (t c e : ℤ) : Set Site := rect t t c e

/-- Any two sites of a horizontal segment are joined inside it. -/
lemma reachIn_hseg {a b y s r : ℤ} (hs : a ≤ s) (hs' : s ≤ b) (hr : a ≤ r) (hr' : r ≤ b) :
    ReachIn (latticeGraph 2) (hseg a b y) (mk s y) (mk r y) := by
  have key : ∀ u v : ℤ, a ≤ u → u ≤ v → v ≤ b →
      ReachIn (latticeGraph 2) (hseg a b y) (mk u y) (mk v y) := by
    intro u v hu huv hv
    obtain ⟨p, hp⟩ := exists_walk_horiz y huv
    refine SimpleGraph.ReachableIn.of_walk p fun z hz ↦ ?_
    obtain ⟨h1, h2, h3⟩ := hp z hz
    exact ⟨le_trans hu h2, le_trans h3 hv, h1.ge, h1.le⟩
  rcases le_total s r with h | h
  · exact key s r hs h hr'
  · exact (key r s hr h hs').symm

/-- Any two sites of a vertical segment are joined inside it. -/
lemma reachIn_vseg {t c e s r : ℤ} (hs : c ≤ s) (hs' : s ≤ e) (hr : c ≤ r) (hr' : r ≤ e) :
    ReachIn (latticeGraph 2) (vseg t c e) (mk t s) (mk t r) := by
  have key : ∀ u v : ℤ, c ≤ u → u ≤ v → v ≤ e →
      ReachIn (latticeGraph 2) (vseg t c e) (mk t u) (mk t v) := by
    intro u v hu huv hv
    obtain ⟨p, hp⟩ := exists_walk_vert t huv
    refine SimpleGraph.ReachableIn.of_walk p fun z hz ↦ ?_
    obtain ⟨h1, h2, h3⟩ := hp z hz
    exact ⟨h1.ge, h1.le, le_trans hu h2, le_trans h3 hv⟩
  rcases le_total s r with h | h
  · exact key s r hs h hr'
  · exact (key r s hr h hs').symm

/-! ### The half-plane clusters of Georgii's Step 2 -/

/-- The closed right half-plane `{i₁ ≥ k}` intersected with the upper half-plane. -/
def upperRight (k : ℤ) : Set Site := {x | k ≤ x 0 ∧ 0 ≤ x 1}

/-- The closed left half-plane `{i₁ ≤ k}` intersected with the upper half-plane. -/
def upperLeft (k : ℤ) : Set Site := {x | x 0 ≤ k ∧ 0 ≤ x 1}

lemma mem_upperRight {k : ℤ} {x : Site} : x ∈ upperRight k ↔ k ≤ x 0 ∧ 0 ≤ x 1 := Iff.rfl

lemma mem_upperLeft {k : ℤ} {x : Site} : x ∈ upperLeft k ↔ x 0 ≤ k ∧ 0 ≤ x 1 := Iff.rfl

/-- Sites of `ℤ²` in a bounded rectangle form a finite set. -/
lemma finite_rect (a b c e : ℤ) : (rect a b c e).Finite := by
  refine Set.Finite.subset (Set.Finite.image (fun p : ℤ × ℤ ↦ mk p.1 p.2)
    ((Set.finite_Icc a b).prod (Set.finite_Icc c e))) ?_
  rintro x ⟨h1, h2, h3, h4⟩
  exact ⟨(x 0, x 1), ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, by simp⟩

/-- **Escaping a rectangle inside an infinite cluster.**  If `o` lies in an infinite cluster of
`U` then some walk inside `U` starting at `o` stays in the rectangle until it steps out of it;
both the walk and the exit site lie in `U`. -/
lemma exists_exit_rect {U : Set Site} {o : Site} (ho : o ∈ (latticeGraph 2).infiniteClusters U)
    {a b c e : ℤ} (hoR : o ∈ rect a b c e) :
    ∃ (w x : Site) (q : (latticeGraph 2).Walk o w),
      (∀ z ∈ q.support, z ∈ U ∩ rect a b c e) ∧ (latticeGraph 2).Adj w x ∧
        x ∈ U ∧ x ∉ rect a b c e := by
  obtain ⟨hoU, hinf⟩ := ho
  have hsupp : (Subtype.val '' (((latticeGraph 2).induce U).connectedComponentMk
      ⟨o, hoU⟩).supp).Infinite := hinf.image Subtype.val_injective.injOn
  obtain ⟨v, hv, hvR⟩ := hsupp.exists_notMem_finite (finite_rect a b c e)
  rw [SimpleGraph.image_val_supp_connectedComponentMk_eq hoU] at hv
  obtain ⟨p, hp⟩ := exists_walk_support_subset_of_reachIn hv
  obtain ⟨w, x, q, hq, hwx, hx, hxp⟩ :=
    SimpleGraph.exists_walk_until_exit (s := U ∩ rect a b c e) p ⟨hoU, hoR⟩
      (fun hc ↦ hvR hc.2)
  have hxU : x ∈ U := hp x hxp
  exact ⟨w, x, q, fun z hz ↦ (hq z hz).1, hwx, hxU, fun hc ↦ hx ⟨hxU, hc⟩⟩

/-- **Georgii, Step 2: the crossing to the right edge.**  Suppose `(k, 0)` lies in an infinite
cluster of `W` inside the quarter plane `{i₁ ≥ k, i₂ ≥ 0}`, and the row `[-N, N] × {h}` misses
`W`.  Then `W` contains a connected set inside the rectangle `[k, N] × [0, h-1]` joining `(k, 0)`
to the right edge `{i₁ = N}`: the cluster cannot escape upwards through the barrier row, so it
escapes sideways. -/
lemma exists_connected_right {W : Set Site} {k N h : ℤ} (hkN : k < N) (hNk : -N ≤ k) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    (hclu : mk k 0 ∈ (latticeGraph 2).infiniteClusters (W ∩ upperRight k)) :
    ∃ (S : Set Site) (y : ℤ), S ⊆ W ∩ upperRight k ∧ S ⊆ rect k N 0 (h - 1) ∧
      mk k 0 ∈ S ∧ mk N y ∈ S ∧ 0 ≤ y ∧ y ≤ h - 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, ReachIn (latticeGraph 2) S u v := by
  obtain ⟨w, x, q, hq, hwx, hxU, hxR⟩ :=
    exists_exit_rect hclu (a := k) (b := N - 1) (c := 0) (e := h - 1)
      (by rw [mk_mem_rect]; omega)
  have hwR : w ∈ rect k (N - 1) 0 (h - 1) := (hq w q.end_mem_support).2
  obtain ⟨-, ha0, ha1⟩ := (starLatticeGraph_two_adj_iff w x).1
    (latticeGraph_le_starLatticeGraph 2 hwx)
  obtain ⟨-, hw1, -, hw3⟩ := mem_rect.1 hwR
  rw [abs_le] at ha0 ha1
  have hxW : x ∈ W := hxU.1
  have hxk : k ≤ x 0 := hxU.2.1
  have hx1 : 0 ≤ x 1 := hxU.2.2
  have hxN : x 0 ≤ N := by omega
  have hcase : x 1 ≤ h - 1 := by
    by_contra hc
    have hx1h : mk (x 0) h = x := by
      have : x 1 = h := by omega
      rw [← this, mk_eta]
    exact hbar (x 0) (by omega) hxN (hx1h ▸ hxW)
  have hx0N : x 0 = N := by
    rcases mem_rect.not.1 hxR |> not_and_or.1 with h' | h'
    · exact absurd hxk h'
    · rcases not_and_or.1 h' with h'' | h''
      · omega
      · rcases not_and_or.1 h'' with h₃ | h₃
        · exact absurd hx1 h₃
        · exact absurd hcase h₃
  refine ⟨{z | z ∈ (q.concat hwx).support}, x 1, ?_, ?_, ?_, ?_, hx1, hcase, ?_⟩
  · intro z hz
    rcases (SimpleGraph.Walk.mem_support_concat q hwx).1 hz with hz | rfl
    · exact (hq z hz).1
    · exact hxU
  · intro z hz
    rcases (SimpleGraph.Walk.mem_support_concat q hwx).1 hz with hz | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := mem_rect.1 (hq z hz).2
      exact ⟨h1, by omega, h3, h4⟩
    · exact ⟨hxk, hxN, hx1, hcase⟩
  · exact (SimpleGraph.Walk.mem_support_concat q hwx).2 (Or.inl q.start_mem_support)
  · refine (SimpleGraph.Walk.mem_support_concat q hwx).2 (Or.inr ?_)
    rw [← hx0N, mk_eta]
  · exact fun u hu v hv ↦ SimpleGraph.reachableIn_support (q.concat hwx) hu hv

/-- **Georgii, Step 2: the crossing to the left edge**, the mirror image of
`exists_connected_right`. -/
lemma exists_connected_left {W : Set Site} {k N h : ℤ} (hkN : -N < k) (hNk : k ≤ N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    (hclu : mk k 0 ∈ (latticeGraph 2).infiniteClusters (W ∩ upperLeft k)) :
    ∃ (S : Set Site) (y : ℤ), S ⊆ W ∩ upperLeft k ∧ S ⊆ rect (-N) k 0 (h - 1) ∧
      mk k 0 ∈ S ∧ mk (-N) y ∈ S ∧ 0 ≤ y ∧ y ≤ h - 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, ReachIn (latticeGraph 2) S u v := by
  obtain ⟨w, x, q, hq, hwx, hxU, hxR⟩ :=
    exists_exit_rect hclu (a := -(N - 1)) (b := k) (c := 0) (e := h - 1)
      (by rw [mk_mem_rect]; omega)
  have hwR : w ∈ rect (-(N - 1)) k 0 (h - 1) := (hq w q.end_mem_support).2
  obtain ⟨-, ha0, ha1⟩ := (starLatticeGraph_two_adj_iff w x).1
    (latticeGraph_le_starLatticeGraph 2 hwx)
  obtain ⟨hw0, -, -, hw3⟩ := mem_rect.1 hwR
  rw [abs_le] at ha0 ha1
  have hxW : x ∈ W := hxU.1
  have hxk : x 0 ≤ k := hxU.2.1
  have hx1 : 0 ≤ x 1 := hxU.2.2
  have hxN : -N ≤ x 0 := by omega
  have hcase : x 1 ≤ h - 1 := by
    by_contra hc
    have hx1h : mk (x 0) h = x := by
      have : x 1 = h := by omega
      rw [← this, mk_eta]
    exact hbar (x 0) hxN (by omega) (hx1h ▸ hxW)
  have hx0N : x 0 = -N := by
    rcases not_and_or.1 (mem_rect.not.1 hxR) with h' | h'
    · omega
    · rcases not_and_or.1 h' with h'' | h''
      · exact absurd hxk h''
      · rcases not_and_or.1 h'' with h₃ | h₃
        · exact absurd hx1 h₃
        · exact absurd hcase h₃
  refine ⟨{z | z ∈ (q.concat hwx).support}, x 1, ?_, ?_, ?_, ?_, hx1, hcase, ?_⟩
  · intro z hz
    rcases (SimpleGraph.Walk.mem_support_concat q hwx).1 hz with hz | rfl
    · exact (hq z hz).1
    · exact hxU
  · intro z hz
    rcases (SimpleGraph.Walk.mem_support_concat q hwx).1 hz with hz | rfl
    · obtain ⟨h1, h2, h3, h4⟩ := mem_rect.1 (hq z hz).2
      exact ⟨by omega, h2, h3, h4⟩
    · exact ⟨hxN, hxk, hx1, hcase⟩
  · exact (SimpleGraph.Walk.mem_support_concat q hwx).2 (Or.inl q.start_mem_support)
  · refine (SimpleGraph.Walk.mem_support_concat q hwx).2 (Or.inr ?_)
    rw [← hx0N, mk_eta]
  · exact fun u hu v hv ↦ SimpleGraph.reachableIn_support (q.concat hwx) hu hv

/-- **Georgii, Lemma (18.16), Step 2: "`π_n^+` is bound to intersect `π_{n+1}^-`".**  Let `W` be
a subset of `ℤ²` (in the application, `W = V(G, ω)`).  Suppose that `(k, 0)` lies in an infinite
cluster of `W` inside `{i₁ ≥ k, i₂ ≥ 0}`, that `(k', 0)` lies in an infinite cluster of `W`
inside `{i₁ ≤ k', i₂ ≥ 0}`, with `-N < k < k' < N`, and that the barrier row `[-N, N] × {h}`,
`h ≥ 1`, misses `W`.  Then `(k, 0)` and `(k', 0)` are joined by a path of `W` in the closed
upper half-plane.

The barrier forces both clusters to leave the box `[-N, N] × [0, h-1]` sideways, so `W` contains
a left-to-right crossing of `[-N, N] × [-1, h-1]` through `(k, 0)` and a bottom-to-top crossing
through `(k', 0)` (both completed by straight segments off `W` which the two crossings cannot
share); the planar crossing lemma
`MeasureTheory.GibbsMeasure.Peierls.inter_nonempty_of_crossings` makes them meet. -/
theorem reachIn_upper_of_infiniteClusters_of_barrier {W : Set Site} {k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    (h₁ : mk k 0 ∈ (latticeGraph 2).infiniteClusters (W ∩ upperRight k))
    (h₂ : mk k' 0 ∈ (latticeGraph 2).infiniteClusters (W ∩ upperLeft k')) :
    ReachIn (latticeGraph 2) (W ∩ {x : Site | 0 ≤ x 1}) (mk k 0) (mk k' 0) := by
  obtain ⟨S₁, y, hS₁U, hS₁R, hS₁0, hS₁N, hy0, hy1, hS₁c⟩ :=
    exists_connected_right (W := W) (k := k) (N := N) (by omega) (by omega) hh hbar h₁
  obtain ⟨S₂, y', hS₂U, hS₂R, hS₂0, hS₂N, hy'0, hy'1, hS₂c⟩ :=
    exists_connected_left (W := W) (k := k') (N := N) (by omega) (by omega) hh hbar h₂
  set Sstar : Set Site := S₁ ∪ hseg (-N) k (-1) with hSs
  set Tstar : Set Site := S₂ ∪ ({mk k' (-1)} ∪ vseg (-N) y' (h - 1)) with hTs
  -- `Sstar` is a left-to-right crossing of the rectangle
  have hSsub : Sstar ⊆ rect (-N) N (-1) (h - 1) := by
    rintro z (hz | hz)
    · obtain ⟨g1, g2, g3, g4⟩ := mem_rect.1 (hS₁R hz)
      exact ⟨by omega, by omega, by omega, g4⟩
    · obtain ⟨g1, g2, g3, g4⟩ := hz
      exact ⟨g1, by omega, by omega, by omega⟩
  have hkey₁ : ∀ u ∈ Sstar, ReachIn (latticeGraph 2) Sstar (mk k 0) u := by
    rintro u (hu | hu)
    · exact (hS₁c _ hS₁0 u hu).mono Set.subset_union_left
    · have hkm : mk k (-1) ∈ hseg (-N) k (-1) := by rw [mk_mem_rect]; omega
      have hadj : (latticeGraph 2).Adj (mk k 0) (mk k (-1)) := by
        have hv := adj_mk_vert k (-1)
        norm_num at hv
        exact hv.symm
      have g1 : ReachIn (latticeGraph 2) Sstar (mk k 0) (mk k (-1)) :=
        ReachIn.of_adj (Set.mem_union_left _ hS₁0) (Set.mem_union_right _ hkm) hadj
      obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
      have g2 : ReachIn (latticeGraph 2) (hseg (-N) k (-1)) (mk k (-1)) u := by
        have hr := reachIn_hseg (a := -N) (b := k) (y := -1) (s := k) (r := u 0)
          (by omega) le_rfl hu1 hu2
        rwa [show mk (u 0) (-1) = u by rw [show (-1 : ℤ) = u 1 by omega, mk_eta]] at hr
      exact g1.trans (g2.mono Set.subset_union_right)
  have hSconn : ∀ u ∈ Sstar, ∀ v ∈ Sstar, ReachIn (latticeGraph 2) Sstar u v :=
    fun u hu v hv ↦ (hkey₁ u hu).symm.trans (hkey₁ v hv)
  have hSa : ∃ u ∈ Sstar, u 0 = -N :=
    ⟨mk (-N) (-1), Set.mem_union_right _ (by rw [mk_mem_rect]; omega), by simp⟩
  have hSb : ∃ v ∈ Sstar, v 0 = N := ⟨mk N y, Set.mem_union_left _ hS₁N, by simp⟩
  -- `Tstar` is a bottom-to-top crossing of the rectangle
  have hTsub : Tstar ⊆ rect (-N) N (-1) (h - 1) := by
    rintro z (hz | hz | hz)
    · obtain ⟨g1, g2, g3, g4⟩ := mem_rect.1 (hS₂R hz)
      exact ⟨g1, by omega, by omega, g4⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [mk_mem_rect]
      omega
    · obtain ⟨g1, g2, g3, g4⟩ := hz
      exact ⟨by omega, by omega, by omega, g4⟩
  have hkey₂ : ∀ u ∈ Tstar, ReachIn (latticeGraph 2) Tstar (mk k' 0) u := by
    have hadj : (latticeGraph 2).Adj (mk k' 0) (mk k' (-1)) := by
      have hv := adj_mk_vert k' (-1)
      norm_num at hv
      exact hv.symm
    rintro u (hu | hu | hu)
    · exact (hS₂c _ hS₂0 u hu).mono Set.subset_union_left
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ReachIn.of_adj (Set.mem_union_left _ hS₂0)
        (Set.mem_union_right _ (Set.mem_union_left _ rfl)) hadj
    · have g1 : ReachIn (latticeGraph 2) Tstar (mk k' 0) (mk (-N) y') :=
        (hS₂c _ hS₂0 _ hS₂N).mono Set.subset_union_left
      obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
      have g2 : ReachIn (latticeGraph 2) (vseg (-N) y' (h - 1)) (mk (-N) y') u := by
        have hr := reachIn_vseg (t := -N) (c := y') (e := h - 1) (s := y') (r := u 1)
          le_rfl hy'1 hu3 hu4
        rwa [show mk (-N) (u 1) = u by rw [show (-N : ℤ) = u 0 by omega, mk_eta]] at hr
      exact g1.trans (g2.mono (Set.subset_union_right.trans Set.subset_union_right))
  have hTconn : ∀ u ∈ Tstar, ∀ v ∈ Tstar, ReachIn (latticeGraph 2) Tstar u v :=
    fun u hu v hv ↦ (hkey₂ u hu).symm.trans (hkey₂ v hv)
  have hTc : ∃ w ∈ Tstar, w 1 = -1 :=
    ⟨mk k' (-1), Set.mem_union_right _ (Set.mem_union_left _ rfl), by simp⟩
  have hTe : ∃ z ∈ Tstar, z 1 = h - 1 :=
    ⟨mk (-N) (h - 1), Set.mem_union_right _ (Set.mem_union_right _
      (by rw [mk_mem_rect]; omega)), by simp⟩
  obtain ⟨z, hzS, hzT⟩ :=
    inter_nonempty_of_crossings hSsub hSconn hSa hSb hTsub hTconn hTc hTe
  -- the two crossings can only meet inside `W`
  have hzS₁ : z ∈ S₁ := by
    rcases hzS with hz | hz
    · exact hz
    · exfalso
      obtain ⟨g1, g2, g3, g4⟩ := hz
      rcases hzT with hw | hw | hw
      · have := (hS₂U hw).2.2
        omega
      · rw [Set.mem_singleton_iff] at hw
        subst hw
        simp only [mk_zero] at g2
        omega
      · obtain ⟨w1, w2, w3, w4⟩ := hw
        omega
  have hzS₂ : z ∈ S₂ := by
    rcases hzT with hz | hz | hz
    · exact hz
    · exfalso
      rw [Set.mem_singleton_iff] at hz
      have := (hS₁U hzS₁).2.2
      rw [hz] at this
      simp only [mk_one] at this
      omega
    · exfalso
      obtain ⟨w1, w2, w3, w4⟩ := hz
      have := (hS₁U hzS₁).2.1
      omega
  have hsub₁ : S₁ ⊆ W ∩ {x : Site | 0 ≤ x 1} := fun u hu ↦ ⟨(hS₁U hu).1, (hS₁U hu).2.2⟩
  have hsub₂ : S₂ ⊆ W ∩ {x : Site | 0 ≤ x 1} := fun u hu ↦ ⟨(hS₂U hu).1, (hS₂U hu).2.2⟩
  exact ((hS₁c _ hS₁0 z hzS₁).mono hsub₁).trans (((hS₂c _ hS₂0 z hzS₂).mono hsub₂).symm)

/-! ### Lattice motions of the plane

The four orientations of Georgii's Step 2 (a horizontal line seen from above or below, a
vertical line seen from the right or the left, at an arbitrary level) are transported from the
single statement `reachIn_upper_of_infiniteClusters_of_barrier` along the isometries of `ℤ²`
generated by the coordinate transposition, the reflections and the translations. -/

/-- The lattice motion `x ↦ (ε₁ x_{σ 0} + c₁, ε₂ x_{σ 1} + c₂)` of `ℤ²`, where `σ` is the
transposition if `τ` and the identity otherwise, and `ε₁, ε₂ ∈ {1, -1}`. -/
def motion (τ : Bool) (ε₁ ε₂ c₁ c₂ : ℤ) : Site → Site := fun x ↦
  if τ then mk (ε₁ * x 1 + c₁) (ε₂ * x 0 + c₂) else mk (ε₁ * x 0 + c₁) (ε₂ * x 1 + c₂)

@[simp] lemma motion_false (ε₁ ε₂ c₁ c₂ : ℤ) (x : Site) :
    motion false ε₁ ε₂ c₁ c₂ x = mk (ε₁ * x 0 + c₁) (ε₂ * x 1 + c₂) := rfl

@[simp] lemma motion_true (ε₁ ε₂ c₁ c₂ : ℤ) (x : Site) :
    motion true ε₁ ε₂ c₁ c₂ x = mk (ε₁ * x 1 + c₁) (ε₂ * x 0 + c₂) := rfl

variable {τ : Bool} {ε₁ ε₂ c₁ c₂ : ℤ}

/-- A lattice motion is injective. -/
lemma motion_injective (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) :
    Function.Injective (motion τ ε₁ ε₂ c₁ c₂) := by
  intro x y hxy
  cases τ <;>
    · simp only [motion_false, motion_true, site_ext_iff, mk_zero, mk_one] at hxy
      rw [site_ext_iff]
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> omega

/-- A lattice motion is surjective. -/
lemma motion_surjective (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) :
    Function.Surjective (motion τ ε₁ ε₂ c₁ c₂) := by
  intro y
  cases τ
  · exact ⟨mk (ε₁ * (y 0 - c₁)) (ε₂ * (y 1 - c₂)), by
      rw [site_ext_iff]
      simp only [motion_false, mk_zero, mk_one]
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> constructor <;> ring⟩
  · exact ⟨mk (ε₂ * (y 1 - c₂)) (ε₁ * (y 0 - c₁)), by
      rw [site_ext_iff]
      simp only [motion_true, mk_zero, mk_one]
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> constructor <;> ring⟩

/-- A lattice motion, as an equivalence of the sites. -/
noncomputable def motionEquiv (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) : Site ≃ Site :=
  Equiv.ofBijective (motion τ ε₁ ε₂ c₁ c₂) ⟨motion_injective h₁ h₂, motion_surjective h₁ h₂⟩

@[simp] lemma motionEquiv_apply (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) (x : Site) :
    motionEquiv (τ := τ) (c₁ := c₁) (c₂ := c₂) h₁ h₂ x = motion τ ε₁ ε₂ c₁ c₂ x := rfl

/-- A lattice motion preserves the nearest-neighbour graph. -/
lemma motion_latticeGraph_adj_iff (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) (x y : Site) :
    (latticeGraph 2).Adj (motion τ ε₁ ε₂ c₁ c₂ x) (motion τ ε₁ ε₂ c₁ c₂ y) ↔
      (latticeGraph 2).Adj x y := by
  rw [latticeGraph_two_adj_iff, latticeGraph_two_adj_iff]
  cases τ <;>
    · simp only [motion_false, motion_true, mk_zero, mk_one]
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> omega

/-- A lattice motion preserves the `*`-neighbour graph. -/
lemma motion_starLatticeGraph_adj_iff (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1)
    (x y : Site) :
    (starLatticeGraph 2).Adj (motion τ ε₁ ε₂ c₁ c₂ x) (motion τ ε₁ ε₂ c₁ c₂ y) ↔
      (starLatticeGraph 2).Adj x y := by
  have hinj : motion τ ε₁ ε₂ c₁ c₂ x = motion τ ε₁ ε₂ c₁ c₂ y ↔ x = y :=
    ⟨fun h ↦ motion_injective h₁ h₂ h, fun h ↦ by rw [h]⟩
  rw [starLatticeGraph_two_adj_iff, starLatticeGraph_two_adj_iff, ne_eq, ne_eq, hinj]
  refine and_congr_right fun _ ↦ ?_
  cases τ <;>
    · simp only [motion_false, motion_true, mk_zero, mk_one, abs_le]
      rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> omega

/-! ### Transport of reachability and of infinite clusters along a symmetry -/

variable {G : SimpleGraph Site}

/-- Reachability inside a set is transported along a symmetry of the graph. -/
lemma reachIn_image_iff {e : Site ≃ Site} (he : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
    {s : Set Site} {u v : Site} : ReachIn G (e '' s) (e u) (e v) ↔ ReachIn G s u v := by
  have key : ∀ (f : Site ≃ Site), (∀ x y, G.Adj (f x) (f y) ↔ G.Adj x y) →
      ∀ {t : Set Site} {p q : Site}, ReachIn G t p q → ReachIn G (f '' t) (f p) (f q) := by
    intro f hf t p q h
    obtain ⟨hp, hq, hr⟩ := h
    exact ⟨⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩,
      SimpleGraph.Reachable.induce_image_of_forall_adj (G := G) (H := G) (s := t) (f := ⇑f)
        (fun a b _ _ hab ↦ Or.inr ((hf a b).2 hab)) (u := ⟨p, hp⟩) (v := ⟨q, hq⟩) hr⟩
  refine ⟨fun h ↦ ?_, key e he⟩
  have he' : ∀ x y, G.Adj (e.symm x) (e.symm y) ↔ G.Adj x y := fun x y ↦ by
    rw [← he (e.symm x) (e.symm y), Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h' := key e.symm he' h
  rwa [Equiv.symm_image_image, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h'

/-- Membership in the union of the infinite clusters is transported along a symmetry. -/
lemma mem_infiniteClusters_image_iff {e : Site ≃ Site} (he : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
    {s : Set Site} {u : Site} :
    e u ∈ G.infiniteClusters (e '' s) ↔ u ∈ G.infiniteClusters s := by
  rw [SimpleGraph.infiniteClusters_image he s]
  exact ⟨fun ⟨v, hv, hvu⟩ ↦ e.injective hvu ▸ hv, fun h ↦ ⟨u, h, rfl⟩⟩

/-! ### Georgii's Step 2 in the four orientations -/

/-- Georgii's Step 2 transported along a lattice motion. -/
theorem reachIn_of_motion (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1)
    {W Q Q' P : Set Site} {k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hQ : motion τ ε₁ ε₂ c₁ c₂ ⁻¹' Q = upperRight k)
    (hQ' : motion τ ε₁ ε₂ c₁ c₂ ⁻¹' Q' = upperLeft k')
    (hP : motion τ ε₁ ε₂ c₁ c₂ ⁻¹' P = {x : Site | 0 ≤ x 1})
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → motion τ ε₁ ε₂ c₁ c₂ (mk x h) ∉ W)
    (hc₁ : motion τ ε₁ ε₂ c₁ c₂ (mk k 0) ∈ (latticeGraph 2).infiniteClusters (W ∩ Q))
    (hc₂ : motion τ ε₁ ε₂ c₁ c₂ (mk k' 0) ∈ (latticeGraph 2).infiniteClusters (W ∩ Q')) :
    ReachIn (latticeGraph 2) (W ∩ P) (motion τ ε₁ ε₂ c₁ c₂ (mk k 0))
      (motion τ ε₁ ε₂ c₁ c₂ (mk k' 0)) := by
  set e : Site ≃ Site := motionEquiv (τ := τ) (c₁ := c₁) (c₂ := c₂) h₁ h₂ with hedef
  have hea : ∀ x, e x = motion τ ε₁ ε₂ c₁ c₂ x := fun x ↦ rfl
  have he : ∀ x y, (latticeGraph 2).Adj (e x) (e y) ↔ (latticeGraph 2).Adj x y := fun x y ↦ by
    rw [hea, hea]; exact motion_latticeGraph_adj_iff h₁ h₂ x y
  set W' : Set Site := e ⁻¹' W with hW'
  have himg : ∀ A B : Set Site, e ⁻¹' A = B → e '' (W' ∩ B) = W ∩ A := by
    intro A B hAB
    rw [← hAB, ← Set.preimage_inter, Equiv.image_preimage]
  have hb₁ : mk k 0 ∈ (latticeGraph 2).infiniteClusters (W' ∩ upperRight k) := by
    rw [← mem_infiniteClusters_image_iff he, himg Q (upperRight k) (by rw [← hQ]; rfl)]
    exact hc₁
  have hb₂ : mk k' 0 ∈ (latticeGraph 2).infiniteClusters (W' ∩ upperLeft k') := by
    rw [← mem_infiniteClusters_image_iff he, himg Q' (upperLeft k') (by rw [← hQ']; rfl)]
    exact hc₂
  have hbar' : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W' := fun x hx hx' hmem ↦
    hbar x hx hx' hmem
  have hbase := reachIn_upper_of_infiniteClusters_of_barrier (W := W') hNk hkk' hk'N hh hbar'
    hb₁ hb₂
  have := (reachIn_image_iff (G := latticeGraph 2) he
    (s := W' ∩ {x : Site | 0 ≤ x 1}) (u := mk k 0) (v := mk k' 0)).2 hbase
  rwa [himg P {x : Site | 0 ≤ x 1} (by rw [← hP]; rfl)] at this

/-- **Georgii, Step 2, upward.**  Two cross centres `(k, t)` and `(k', t)` on the horizontal line
at height `t`, whose clusters in the two upper quadrants there are infinite, are joined by a path
of `W` in the closed half-plane above that line, provided a barrier row `[-N, N] × {t + h}`
above them misses `W`. -/
theorem reachIn_up {W : Set Site} {t k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x (h + t) ∉ W)
    (hc₁ : mk k t ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | k ≤ y 0 ∧ t ≤ y 1}))
    (hc₂ : mk k' t ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | y 0 ≤ k' ∧ t ≤ y 1})) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | t ≤ y 1}) (mk k t) (mk k' t) := by
  have key := reachIn_of_motion (τ := false) (ε₁ := 1) (ε₂ := 1) (c₁ := 0) (c₂ := t)
    (Or.inl rfl) (Or.inl rfl) (W := W) (Q := {y : Site | k ≤ y 0 ∧ t ≤ y 1})
    (Q' := {y : Site | y 0 ≤ k' ∧ t ≤ y 1}) (P := {y : Site | t ≤ y 1})
    hNk hkk' hk'N hh
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperRight]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperLeft]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_one, Set.mem_ofPred_eq]
      omega)
    (by intro x hx hx'; simpa using hbar x hx hx')
    (by simpa using hc₁) (by simpa using hc₂)
  simpa using key

/-- **Georgii, Step 2, downward**: the mirror image of `reachIn_up` in the line at height `t`. -/
theorem reachIn_down {W : Set Site} {t k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x (t - h) ∉ W)
    (hc₁ : mk k t ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | k ≤ y 0 ∧ y 1 ≤ t}))
    (hc₂ : mk k' t ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | y 0 ≤ k' ∧ y 1 ≤ t})) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | y 1 ≤ t}) (mk k t) (mk k' t) := by
  have key := reachIn_of_motion (τ := false) (ε₁ := 1) (ε₂ := -1) (c₁ := 0) (c₂ := t)
    (Or.inl rfl) (Or.inr rfl) (W := W) (Q := {y : Site | k ≤ y 0 ∧ y 1 ≤ t})
    (Q' := {y : Site | y 0 ≤ k' ∧ y 1 ≤ t}) (P := {y : Site | y 1 ≤ t})
    hNk hkk' hk'N hh
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperRight]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperLeft]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_false, mk_one, Set.mem_ofPred_eq]
      omega)
    (by
      intro x hx hx'
      have heq : motion false 1 (-1) 0 t (mk x h) = mk x (t - h) := by
        rw [motion_false, site_ext_iff]
        simp only [mk_zero, mk_one]
        omega
      rw [heq]
      exact hbar x hx hx')
    (by simpa using hc₁) (by simpa using hc₂)
  simpa using key

/-- **Georgii, Step 2, to the right**: two cross centres `(m, k)` and `(m, k')` on the vertical
line at column `m` are joined by a path of `W` in the closed half-plane to the right of it,
provided a barrier column `{m + h} × [-N, N]` misses `W`. -/
theorem reachIn_right {W : Set Site} {m k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk (h + m) x ∉ W)
    (hc₁ : mk m k ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | k ≤ y 1 ∧ m ≤ y 0}))
    (hc₂ : mk m k' ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | y 1 ≤ k' ∧ m ≤ y 0})) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | m ≤ y 0}) (mk m k) (mk m k') := by
  have key := reachIn_of_motion (τ := true) (ε₁ := 1) (ε₂ := 1) (c₁ := m) (c₂ := 0)
    (Or.inl rfl) (Or.inl rfl) (W := W) (Q := {y : Site | k ≤ y 1 ∧ m ≤ y 0})
    (Q' := {y : Site | y 1 ≤ k' ∧ m ≤ y 0}) (P := {y : Site | m ≤ y 0})
    hNk hkk' hk'N hh
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperRight]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperLeft]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, Set.mem_ofPred_eq]
      omega)
    (by intro x hx hx'; simpa using hbar x hx hx')
    (by simpa using hc₁) (by simpa using hc₂)
  simpa using key

/-- **Georgii, Step 2, to the left**: the mirror image of `reachIn_right`. -/
theorem reachIn_left {W : Set Site} {m k k' N h : ℤ}
    (hNk : -N < k) (hkk' : k < k') (hk'N : k' < N) (hh : 1 ≤ h)
    (hbar : ∀ x : ℤ, -N ≤ x → x ≤ N → mk (m - h) x ∉ W)
    (hc₁ : mk m k ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | k ≤ y 1 ∧ y 0 ≤ m}))
    (hc₂ : mk m k' ∈ (latticeGraph 2).infiniteClusters (W ∩ {y : Site | y 1 ≤ k' ∧ y 0 ≤ m})) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | y 0 ≤ m}) (mk m k) (mk m k') := by
  have key := reachIn_of_motion (τ := true) (ε₁ := -1) (ε₂ := 1) (c₁ := m) (c₂ := 0)
    (Or.inr rfl) (Or.inl rfl) (W := W) (Q := {y : Site | k ≤ y 1 ∧ y 0 ≤ m})
    (Q' := {y : Site | y 1 ≤ k' ∧ y 0 ≤ m}) (P := {y : Site | y 0 ≤ m})
    hNk hkk' hk'N hh
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperRight]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, mk_one, Set.mem_ofPred_eq, mem_upperLeft]
      omega)
    (by
      ext x
      simp only [Set.mem_preimage, motion_true, mk_zero, Set.mem_ofPred_eq]
      omega)
    (by
      intro x hx hx'
      have heq : motion true (-1) 1 m 0 (mk x h) = mk (m - h) x := by
        rw [motion_true, site_ext_iff]
        simp only [mk_zero, mk_one]
        omega
      rw [heq]
      exact hbar x hx hx')
    (by simpa using hc₁) (by simpa using hc₂)
  simpa using key

/-! ### The mod-two crossing number of a lattice walk

A closed lattice walk carries a side function `ψ` (`exists_side_fun`) whose increment up a column
is the parity of the horizontal bonds of the walk crossed.  Summing that increment along a
vertical ray turns the question "is `p` inside the circuit?" into the parity of the number of
times the circuit crosses the ray, which is computed by `sum_bondChain_hbond`. -/

/-- One step of a lattice walk crosses the dual vertical line at horizontal position `t + 1/2`
exactly when exactly one of its two ends lies weakly left of the column `t`. -/
lemma sum_ite_hbond_eq {u w : Site} (hadj : (latticeGraph 2).Adj u w) (t : ℤ) (Y : Finset ℤ)
    (hY : ∀ y : ℤ, s(u, w) = hbond (mk t y) → y ∈ Y) :
    ∑ y ∈ Y, (if s(u, w) = hbond (mk t y) then (1 : ZMod 2) else 0)
      = (if u 0 ≤ t then 1 else 0) + (if w 0 ≤ t then 1 else 0) := by
  classical
  by_cases hcase : ∃ y : ℤ, s(u, w) = hbond (mk t y)
  · obtain ⟨y₀, hy₀⟩ := hcase
    have huniq : ∀ y ∈ Y, y ≠ y₀ → (if s(u, w) = hbond (mk t y) then (1 : ZMod 2) else 0) = 0 := by
      intro y _ hne
      refine if_neg fun hy ↦ hne ?_
      have hbb : hbond (mk t y) = hbond (mk t y₀) := by rw [← hy, hy₀]
      have := hbond_injective hbb
      rw [site_ext_iff] at this
      simpa using this.2
    rw [Finset.sum_eq_single y₀ huniq (fun h ↦ absurd (hY y₀ hy₀) h), if_pos hy₀]
    rw [hbond_mk] at hy₀
    rcases Sym2.eq_iff.1 hy₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      simp only [mk_zero]
      rw [if_pos le_rfl, if_neg (by omega)]
      decide
    · rw [h1, h2]
      simp only [mk_zero]
      rw [if_pos le_rfl, if_neg (by omega)]
      decide
  · have hzero : ∀ y ∈ Y, (if s(u, w) = hbond (mk t y) then (1 : ZMod 2) else 0) = 0 :=
      fun y _ ↦ if_neg fun h ↦ hcase ⟨y, h⟩
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    have hsame : (u 0 ≤ t) ↔ (w 0 ≤ t) := by
      by_contra hcon
      have hne : u 0 ≠ w 0 := by
        intro h
        rw [h] at hcon
        exact hcon Iff.rfl
      have h1 : (u 0 - w 0).natAbs + (u 1 - w 1).natAbs = 1 := (latticeGraph_two_adj_iff u w).1 hadj
      have h2 : u 1 = w 1 := by omega
      rcases le_or_gt (u 0) t with hu | hu
      · have hw : t < w 0 := by
          by_contra hc
          exact hcon (iff_of_true hu (by omega))
        have hcoord : u 0 = t ∧ w 0 = t + 1 := by omega
        have hu' : u = mk t (u 1) := by
          rw [site_ext_iff]
          exact ⟨by rw [mk_zero]; exact hcoord.1, by rw [mk_one]⟩
        have hw' : w = mk (t + 1) (u 1) := by
          rw [site_ext_iff]
          exact ⟨by rw [mk_zero]; exact hcoord.2, by rw [mk_one]; exact h2.symm⟩
        refine hcase ⟨u 1, ?_⟩
        rw [hbond_mk, ← hu', ← hw']
      · have hw : w 0 ≤ t := by
          by_contra hc
          exact hcon (iff_of_false (by omega) (by omega))
        have hcoord : w 0 = t ∧ u 0 = t + 1 := by omega
        have hu' : u = mk (t + 1) (u 1) := by
          rw [site_ext_iff]
          exact ⟨by rw [mk_zero]; exact hcoord.2, by rw [mk_one]⟩
        have hw' : w = mk t (u 1) := by
          rw [site_ext_iff]
          exact ⟨by rw [mk_zero]; exact hcoord.1, by rw [mk_one]; exact h2.symm⟩
        refine hcase ⟨u 1, ?_⟩
        rw [hbond_mk, ← hw', ← hu']
        exact Sym2.eq_swap
    by_cases hu : u 0 ≤ t
    · rw [if_pos hu, if_pos (hsame.1 hu)]
      decide
    · rw [if_neg hu, if_neg (fun h ↦ hu (hsame.2 h))]
      decide

/-- **The mod-two crossing number of a lattice walk.**  The parity of the number of horizontal
bonds of the walk in the column strip between the columns `t` and `t + 1` equals the parity of
the number of endpoints of the walk lying weakly left of the column `t`.  The finite set `Y` must
contain every height at which such a bond occurs. -/
lemma sum_bondChain_hbond (t : ℤ) :
    ∀ {u v : Site} (γ : (latticeGraph 2).Walk u v) (Y : Finset ℤ),
      (∀ y : ℤ, hbond (mk t y) ∈ γ.edges → y ∈ Y) →
      ∑ y ∈ Y, bondChain γ (hbond (mk t y))
        = (if u 0 ≤ t then 1 else 0) + (if v 0 ≤ t then 1 else 0)
  | u, _, .nil, Y, _ => by
      simp only [bondChain_nil, Finset.sum_const_zero]
      by_cases h : u 0 ≤ t
      · rw [if_pos h]; decide
      · rw [if_neg h]; decide
  | u, v, .cons (v := w) hadj q, Y, hY => by
      have hq : ∀ y : ℤ, hbond (mk t y) ∈ q.edges → y ∈ Y := fun y hy ↦
        hY y (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ hy)
      have hsplit : ∑ y ∈ Y, bondChain (SimpleGraph.Walk.cons hadj q) (hbond (mk t y))
          = (∑ y ∈ Y, (if s(u, w) = hbond (mk t y) then (1 : ZMod 2) else 0))
            + ∑ y ∈ Y, bondChain q (hbond (mk t y)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun y _ ↦ bondChain_cons hadj q _
      rw [hsplit, sum_bondChain_hbond t q Y hq,
        sum_ite_hbond_eq hadj t Y (fun y hy ↦ hY y (by
          rw [SimpleGraph.Walk.edges_cons, ← hy]; exact List.mem_cons_self))]
      generalize (if u 0 ≤ t then (1 : ZMod 2) else 0) = A
      generalize (if w 0 ≤ t then (1 : ZMod 2) else 0) = B
      generalize (if v 0 ≤ t then (1 : ZMod 2) else 0) = D
      have : B + B = 0 := zmodTwo_add_self B
      rw [add_assoc, ← add_assoc B B D, this, zero_add]

/-- Telescoping the side function up a column: `ψ` at the bottom and at the top of a segment of a
column differ by the parity of the horizontal bonds of the circuit crossed in between. -/
lemma psi_sum_Ioc {o : Site} {C : (latticeGraph 2).Walk o o} {ψ : Site → ZMod 2}
    (hψ : ∀ t y : ℤ, ψ (mk t y) + ψ (mk t (y + 1)) = bondChain C (hbond (mk t (y + 1))))
    (t : ℤ) {y₀ y₁ : ℤ} (h : y₀ ≤ y₁) :
    ψ (mk t y₀) + ψ (mk t y₁) = ∑ y ∈ Finset.Ioc y₀ y₁, bondChain C (hbond (mk t y)) := by
  induction y₁, h using Int.leInduction with
  | base =>
      rw [show Finset.Ioc y₀ y₀ = (∅ : Finset ℤ) by simp]
      simp only [Finset.sum_empty]
      exact zmodTwo_add_self _
  | succ n hn ih =>
      have hins : Finset.Ioc y₀ (n + 1) = insert (n + 1) (Finset.Ioc y₀ n) := by
        ext z
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        omega
      have hnot : (n + 1) ∉ Finset.Ioc y₀ n := by simp
      rw [hins, Finset.sum_insert hnot, ← ih, ← hψ t n]
      generalize ψ (mk t y₀) = A
      generalize ψ (mk t n) = B
      generalize ψ (mk t (n + 1)) = D
      have : B + B = 0 := zmodTwo_add_self B
      rw [add_comm (B + D) (A + B), add_assoc, ← add_assoc B B D, this, zero_add]

/-! ### A lattice circuit traps the `*`-cluster of any point inside it -/

/-- The side function of a lattice circuit is constant outside any box containing the circuit:
the complement of a box is connected and misses the circuit. -/
lemma psi_const_outside_box {o : Site} {C : (latticeGraph 2).Walk o o} {ψ : Site → ZMod 2}
    (hstar : ∀ z z' : Site, z ∉ C.support → z' ∉ C.support →
      (starLatticeGraph 2).Adj z z' → ψ z = ψ z')
    {N : ℕ} (hN : ∀ z ∈ C.support, z ∈ box N) {x y : Site} (hx : x ∉ box N) (hy : y ∉ box N) :
    ψ x = ψ y := by
  set D : Set Site := {z | z ∈ C.support} with hD
  have hDN : D ⊆ box N := fun z hz ↦ hN z hz
  have hDfin : D.Finite := List.finite_toSet C.support
  have hxo : x ∈ outside D := mem_outside_of_notMem_box hDN hx
  have hyo : y ∈ outside D := mem_outside_of_notMem_box hDN hy
  refine SimpleGraph.ReachableIn.invariant ψ (fun z z' hz hz' hzz' ↦
    hstar z z' hz hz' (latticeGraph_le_starLatticeGraph 2 hzz')) ?_
  exact reachIn_of_mem_outside hDfin hxo hyo

/-- **A lattice circuit traps the `*`-cluster of a point at which its side function differs from
its value at infinity.**  Every site `*`-connected to `p` off the circuit lies in the box. -/
lemma reachIn_star_subset_box_of_psi {o : Site} {C : (latticeGraph 2).Walk o o}
    {ψ : Site → ZMod 2}
    (hstar : ∀ z z' : Site, z ∉ C.support → z' ∉ C.support →
      (starLatticeGraph 2).Adj z z' → ψ z = ψ z')
    {N : ℕ} (hN : ∀ z ∈ C.support, z ∈ box N) {p x : Site} (hx : x ∉ box N) (hne : ψ p ≠ ψ x)
    {S : Set Site} (hS : ∀ z ∈ C.support, z ∈ S) :
    {q | ReachIn (starLatticeGraph 2) Sᶜ p q} ⊆ box N := by
  intro q hq
  have hoff : ∀ z ∈ (Sᶜ : Set Site), z ∉ C.support := fun z hz hzC ↦ hz (hS z hzC)
  have hpsi : ψ p = ψ q :=
    SimpleGraph.ReachableIn.invariant ψ (fun z z' hz hz' hzz' ↦ hstar z z' (hoff z hz)
      (hoff z' hz') hzz') hq
  by_contra hqN
  exact hne (hpsi.trans (psi_const_outside_box hstar hN hqN hx))

/-- **Georgii, Step 3: a circuit of `W` around `p`.**  Four lattice walks that close up into a
circuit — one running above the row `t`, one right of the column `b`, one below the row `s`, one
left of the column `a` — trap every site `*`-connected off the circuit to a point `p` of the open
box `(a, b) × (s, t)`: that `*`-cluster is finite.

The circuit crosses the vertical ray above `p` an odd number of times (only its top piece can
cross it, and that piece runs from the column `a` to the column `b`), so the mod-two side
function of `exists_side_fun` separates `p` from infinity. -/
theorem finite_reachIn_star_of_circuit {a b s t : ℤ}
    (Pu : (latticeGraph 2).Walk (mk a t) (mk b t))
    (Pr : (latticeGraph 2).Walk (mk b t) (mk b s))
    (Pd : (latticeGraph 2).Walk (mk b s) (mk a s))
    (Pl : (latticeGraph 2).Walk (mk a s) (mk a t))
    (hPu : ∀ z ∈ Pu.support, t ≤ z 1) (hPr : ∀ z ∈ Pr.support, b ≤ z 0)
    (hPd : ∀ z ∈ Pd.support, z 1 ≤ s) (hPl : ∀ z ∈ Pl.support, z 0 ≤ a)
    {p : Site} (hpa : a < p 0) (hpb : p 0 < b) (hps : s < p 1) (hpt : p 1 < t)
    {S : Set Site}
    (hS : ∀ z, (z ∈ Pu.support ∨ z ∈ Pr.support ∨ z ∈ Pd.support ∨ z ∈ Pl.support) → z ∈ S) :
    {q | ReachIn (starLatticeGraph 2) Sᶜ p q}.Finite := by
  classical
  set C : (latticeGraph 2).Walk (mk a t) (mk a t) := Pu.append (Pr.append (Pd.append Pl)) with hC
  have hsupp : ∀ z : Site, z ∈ C.support ↔
      (z ∈ Pu.support ∨ z ∈ Pr.support ∨ z ∈ Pd.support ∨ z ∈ Pl.support) := by
    intro z
    simp only [hC, SimpleGraph.Walk.mem_support_append_iff]
  obtain ⟨ψ, hψ, hstar⟩ := exists_side_fun C
  obtain ⟨N, hN⟩ : ∃ N : ℕ, {z : Site | z ∈ C.support} ⊆ box N :=
    exists_subset_box (List.finite_toSet C.support)
  have hNsupp : ∀ z ∈ C.support, z ∈ box N := fun z hz ↦ hN hz
  -- the four corners of the circuit lie in the box, hence so does `p`
  have hcorner : ∀ z ∈ C.support, -(N : ℤ) ≤ z 0 ∧ z 0 ≤ (N : ℤ) ∧ -(N : ℤ) ≤ z 1 ∧
      z 1 ≤ (N : ℤ) := by
    intro z hz
    have := hNsupp z hz
    simp only [box, Set.mem_ofPred_eq, Fin.forall_fin_two, abs_le] at this
    exact ⟨this.1.1, this.1.2, this.2.1, this.2.2⟩
  have hat := hcorner (mk a t) ((hsupp _).2 (Or.inl Pu.start_mem_support))
  have hbs := hcorner (mk b s) ((hsupp _).2 (Or.inr (Or.inl Pr.end_mem_support)))
  simp only [mk_zero, mk_one] at hat hbs
  have hpN : -(N : ℤ) ≤ p 0 ∧ p 0 ≤ (N : ℤ) ∧ -(N : ℤ) ≤ p 1 ∧ p 1 ≤ (N : ℤ) := by
    omega
  -- the parity of the crossings of the vertical ray above `p`
  set Y : ℤ := (N : ℤ) + 1 with hY
  have hpY : p 1 ≤ Y := by rw [hY]; omega
  have hsum := psi_sum_Ioc hψ (p 0) hpY
  have hzeroPr : ∀ y ∈ Finset.Ioc (p 1) Y, bondChain Pr (hbond (mk (p 0) y)) = 0 := by
    intro y _
    rw [hbond_mk]
    refine bondChain_eq_zero_of_fst_notMem Pr fun hmem ↦ ?_
    have := hPr _ hmem
    simp only [mk_zero] at this
    omega
  have hzeroPd : ∀ y ∈ Finset.Ioc (p 1) Y, bondChain Pd (hbond (mk (p 0) y)) = 0 := by
    intro y hy
    rw [Finset.mem_Ioc] at hy
    rw [hbond_mk]
    refine bondChain_eq_zero_of_fst_notMem Pd fun hmem ↦ ?_
    have := hPd _ hmem
    simp only [mk_one] at this
    omega
  have hzeroPl : ∀ y ∈ Finset.Ioc (p 1) Y, bondChain Pl (hbond (mk (p 0) y)) = 0 := by
    intro y _
    rw [hbond_mk]
    refine bondChain_eq_zero_of_snd_notMem Pl fun hmem ↦ ?_
    have := hPl _ hmem
    simp only [mk_zero] at this
    omega
  have hPuY : ∀ y : ℤ, hbond (mk (p 0) y) ∈ Pu.edges → y ∈ Finset.Ioc (p 1) Y := by
    intro y hy
    have hy' : s(mk (p 0) y, mk (p 0 + 1) y) ∈ Pu.edges := by rwa [hbond_mk] at hy
    have hmem : mk (p 0) y ∈ Pu.support := Pu.fst_mem_support_of_mem_edges hy'
    have h1 := hPu _ hmem
    have h2 := hcorner _ ((hsupp _).2 (Or.inl hmem))
    simp only [mk_one] at h1
    simp only [mk_one] at h2
    rw [Finset.mem_Ioc, hY]
    omega
  have hone : ∑ y ∈ Finset.Ioc (p 1) Y, bondChain C (hbond (mk (p 0) y)) = 1 := by
    have hsplit : ∀ y : ℤ, bondChain C (hbond (mk (p 0) y))
        = bondChain Pu (hbond (mk (p 0) y)) + bondChain Pr (hbond (mk (p 0) y))
          + bondChain Pd (hbond (mk (p 0) y)) + bondChain Pl (hbond (mk (p 0) y)) := by
      intro y
      rw [hC, bondChain_append, bondChain_append, bondChain_append]
      ring
    rw [Finset.sum_congr rfl fun y hy ↦ by
      rw [hsplit y, hzeroPr y hy, hzeroPd y hy, hzeroPl y hy, add_zero, add_zero, add_zero]]
    rw [sum_bondChain_hbond (p 0) Pu (Finset.Ioc (p 1) Y) hPuY]
    simp only [mk_zero]
    rw [if_pos (by omega), if_neg (by omega)]
    decide
  rw [hone] at hsum
  have hne : ψ p ≠ ψ (mk (p 0) Y) := by
    rw [mk_eta] at hsum
    intro hcon
    rw [hcon] at hsum
    exact absurd (hsum.symm.trans (zmodTwo_add_self _)) (by decide)
  have hYbox : mk (p 0) Y ∉ box N := by
    rw [notMem_box_iff]
    refine Or.inr ?_
    simp only [mk_one, hY]
    rw [abs_of_nonneg (by positivity)]
    omega
  exact (box_finite N).subset
    (reachIn_star_subset_box_of_psi hstar hNsupp hYbox hne
      (fun z hz ↦ hS z ((hsupp z).1 hz)))

/-! ### Cross centres and the four connections of Step 2 -/

/-- The closed quadrant with vertex `i` and signs `s₁, s₂`, a translate of `quadrant s₁ s₂`. -/
def quadrantAt (s₁ s₂ : ℤ) (i : Site) : Set Site := (· + i) '' quadrant s₁ s₂

lemma mem_quadrantAt {s₁ s₂ : ℤ} {i x : Site} :
    x ∈ quadrantAt s₁ s₂ i ↔ 0 ≤ s₁ * (x 0 - i 0) ∧ 0 ≤ s₂ * (x 1 - i 1) := by
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    simpa using ⟨hy1, hy2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x - i, ⟨by simpa using h1, by simpa using h2⟩, by abel⟩

/-- **Georgii's event `X`, at the site `i`.**  `i` is a *cross centre* of `W` if it lies in an
infinite cluster of `W` inside each of the four closed quadrants with vertex `i`: the origin of
an infinite "cross" of `W`. -/
def IsCrossCentre (W : Set Site) (i : Site) : Prop :=
  ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
    i ∈ (latticeGraph 2).infiniteClusters (W ∩ quadrantAt s₁ s₂ i)

lemma IsCrossCentre.mem {W : Set Site} {i : Site} (h : IsCrossCentre W i) : i ∈ W :=
  (SimpleGraph.infiniteClusters_subset (h 1 1 (Or.inl rfl) (Or.inl rfl))).1

lemma IsCrossCentre.mem_infiniteClusters {W : Set Site} {i : Site} (h : IsCrossCentre W i) :
    i ∈ (latticeGraph 2).infiniteClusters W :=
  SimpleGraph.infiniteClusters_mono le_rfl Set.inter_subset_left
    (h 1 1 (Or.inl rfl) (Or.inl rfl))

lemma IsCrossCentre.quadrant_eq {W : Set Site} {i : Site} (h : IsCrossCentre W i)
    {s₁ s₂ : ℤ} (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) {Q : Set Site}
    (hQ : Q = quadrantAt s₁ s₂ i) :
    i ∈ (latticeGraph 2).infiniteClusters (W ∩ Q) := hQ ▸ h s₁ s₂ h₁ h₂

variable {W : Set Site}

/-- **Georgii, Step 2, upward, at two cross centres.** -/
theorem reachIn_up_of_crossCentres
    (hbarU : ∀ N y₀ : ℤ, ∃ h : ℤ, y₀ < h ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    {t k k' : ℤ} (hkk' : k < k')
    (h₁ : IsCrossCentre W (mk k t)) (h₂ : IsCrossCentre W (mk k' t)) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | t ≤ y 1}) (mk k t) (mk k' t) := by
  set N : ℤ := (k.natAbs : ℤ) + (k'.natAbs : ℤ) + 1 with hN
  obtain ⟨h, hht, hbar⟩ := hbarU N t
  have hbar' : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x (h - t + t) ∉ W := by
    intro x hx hx'
    rw [show h - t + t = h by ring]
    exact hbar x hx hx'
  have hc₁ := h₁.quadrant_eq (Or.inl rfl) (Or.inl rfl) (Q := {y : Site | k ≤ y 0 ∧ t ≤ y 1})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  have hc₂ := h₂.quadrant_eq (Or.inr rfl) (Or.inl rfl) (Q := {y : Site | y 0 ≤ k' ∧ t ≤ y 1})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  exact reachIn_up (N := N) (h := h - t) (by simp only [hN]; omega) hkk'
    (by simp only [hN]; omega) (by omega) hbar' hc₁ hc₂

/-- **Georgii, Step 2, downward, at two cross centres.** -/
theorem reachIn_down_of_crossCentres
    (hbarD : ∀ N y₀ : ℤ, ∃ h : ℤ, h < y₀ ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    {t k k' : ℤ} (hkk' : k < k')
    (h₁ : IsCrossCentre W (mk k t)) (h₂ : IsCrossCentre W (mk k' t)) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | y 1 ≤ t}) (mk k t) (mk k' t) := by
  set N : ℤ := (k.natAbs : ℤ) + (k'.natAbs : ℤ) + 1 with hN
  obtain ⟨h, hht, hbar⟩ := hbarD N t
  have hbar' : ∀ x : ℤ, -N ≤ x → x ≤ N → mk x (t - (t - h)) ∉ W := by
    intro x hx hx'
    rw [show t - (t - h) = h by ring]
    exact hbar x hx hx'
  have hc₁ := h₁.quadrant_eq (Or.inl rfl) (Or.inr rfl) (Q := {y : Site | k ≤ y 0 ∧ y 1 ≤ t})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  have hc₂ := h₂.quadrant_eq (Or.inr rfl) (Or.inr rfl) (Q := {y : Site | y 0 ≤ k' ∧ y 1 ≤ t})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  exact reachIn_down (N := N) (h := t - h) (by simp only [hN]; omega) hkk'
    (by simp only [hN]; omega) (by omega) hbar' hc₁ hc₂

/-- **Georgii, Step 2, to the right, at two cross centres.** -/
theorem reachIn_right_of_crossCentres
    (hbarR : ∀ N x₀ : ℤ, ∃ h : ℤ, x₀ < h ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ W)
    {m k k' : ℤ} (hkk' : k < k')
    (h₁ : IsCrossCentre W (mk m k)) (h₂ : IsCrossCentre W (mk m k')) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | m ≤ y 0}) (mk m k) (mk m k') := by
  set N : ℤ := (k.natAbs : ℤ) + (k'.natAbs : ℤ) + 1 with hN
  obtain ⟨h, hhm, hbar⟩ := hbarR N m
  have hbar' : ∀ x : ℤ, -N ≤ x → x ≤ N → mk (h - m + m) x ∉ W := by
    intro x hx hx'
    rw [show h - m + m = h by ring]
    exact hbar x hx hx'
  have hc₁ := h₁.quadrant_eq (Or.inl rfl) (Or.inl rfl) (Q := {y : Site | k ≤ y 1 ∧ m ≤ y 0})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  have hc₂ := h₂.quadrant_eq (Or.inl rfl) (Or.inr rfl) (Q := {y : Site | y 1 ≤ k' ∧ m ≤ y 0})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  exact reachIn_right (N := N) (h := h - m) (by simp only [hN]; omega) hkk'
    (by simp only [hN]; omega) (by omega) hbar' hc₁ hc₂

/-- **Georgii, Step 2, to the left, at two cross centres.** -/
theorem reachIn_left_of_crossCentres
    (hbarL : ∀ N x₀ : ℤ, ∃ h : ℤ, h < x₀ ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ W)
    {m k k' : ℤ} (hkk' : k < k')
    (h₁ : IsCrossCentre W (mk m k)) (h₂ : IsCrossCentre W (mk m k')) :
    ReachIn (latticeGraph 2) (W ∩ {y : Site | y 0 ≤ m}) (mk m k) (mk m k') := by
  set N : ℤ := (k.natAbs : ℤ) + (k'.natAbs : ℤ) + 1 with hN
  obtain ⟨h, hhm, hbar⟩ := hbarL N m
  have hbar' : ∀ x : ℤ, -N ≤ x → x ≤ N → mk (m - (m - h)) x ∉ W := by
    intro x hx hx'
    rw [show m - (m - h) = h by ring]
    exact hbar x hx hx'
  have hc₁ := h₁.quadrant_eq (Or.inr rfl) (Or.inl rfl) (Q := {y : Site | k ≤ y 1 ∧ y 0 ≤ m})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  have hc₂ := h₂.quadrant_eq (Or.inr rfl) (Or.inr rfl) (Q := {y : Site | y 1 ≤ k' ∧ y 0 ≤ m})
    (by ext y; rw [mem_quadrantAt]; simp only [mk_zero, mk_one, Set.mem_ofPred_eq]; omega)
  exact reachIn_left (N := N) (h := m - h) (by simp only [hN]; omega) hkk'
    (by simp only [hN]; omega) (by omega) hbar' hc₁ hc₂

/-! ### Infinite clusters through arbitrarily distant sites, and translations -/

@[simp] lemma mk_zero_zero : mk 0 0 = (0 : Site) := by rw [site_ext_iff]; simp

lemma quadrantAt_zero (s₁ s₂ : ℤ) : quadrantAt s₁ s₂ 0 = quadrant s₁ s₂ := by
  rw [quadrantAt]
  ext y
  simp

/-- A site lies in an infinite cluster of `s` exactly when arbitrarily distant sites are joined
to it inside `s`.  This exhibits the event `{ω | o ∈ infiniteClusters (W ω)}` as a countable
intersection of countable unions, hence measurable. -/
lemma mem_infiniteClusters_iff_forall_exists {s : Set Site} {o : Site} :
    o ∈ (latticeGraph 2).infiniteClusters s ↔
      ∀ n : ℕ, ∃ x : Site, x ∉ box n ∧ ReachIn (latticeGraph 2) s o x := by
  constructor
  · rintro ⟨ho, hinf⟩ n
    have himg : Subtype.val '' (((latticeGraph 2).induce s).connectedComponentMk ⟨o, ho⟩).supp
        = {x | ReachIn (latticeGraph 2) s o x} :=
      SimpleGraph.image_val_supp_connectedComponentMk_eq ho
    have hTinf : {x : Site | ReachIn (latticeGraph 2) s o x}.Infinite := by
      rw [← himg]
      exact hinf.image Subtype.val_injective.injOn
    obtain ⟨x, hx, hxn⟩ := hTinf.exists_notMem_finite (box_finite n)
    exact ⟨x, hxn, hx⟩
  · intro h
    obtain ⟨x₀, -, hx₀⟩ := h 0
    have ho : o ∈ s := hx₀.mem_left
    refine ⟨ho, ?_⟩
    rw [← Set.infinite_image_iff Subtype.val_injective.injOn,
      SimpleGraph.image_val_supp_connectedComponentMk_eq ho]
    intro hfin
    obtain ⟨n, hn⟩ := exists_subset_box hfin
    obtain ⟨x, hxn, hx⟩ := h n
    exact hxn (hn hx)

/-- **Cross centres translate with the pattern.**  This is the equivariance behind Georgii's
"`θ_{-i} ω ∈ X` iff `i` is a cross centre of `V(G, ω)`". -/
lemma isCrossCentre_add {W : Set Site} (i a : Site) :
    IsCrossCentre ((· + a) '' W) (i + a) ↔ IsCrossCentre W i := by
  have he : ∀ x y : Site, (latticeGraph 2).Adj ((Equiv.addRight a) x) ((Equiv.addRight a) y)
      ↔ (latticeGraph 2).Adj x y := fun x y ↦ latticeGraph_adj_add_right a x y
  have hq : ∀ s₁ s₂ : ℤ, quadrantAt s₁ s₂ (i + a) = (· + a) '' quadrantAt s₁ s₂ i := by
    intro s₁ s₂
    rw [quadrantAt, quadrantAt, ← Set.image_comp]
    congr 1
    funext x
    simp only [Function.comp_apply]
    abel
  constructor
  · intro h s₁ s₂ h₁ h₂
    have hh := h s₁ s₂ h₁ h₂
    rw [hq s₁ s₂, ← Set.image_inter (add_left_injective a)] at hh
    exact (mem_infiniteClusters_image_iff (e := Equiv.addRight a) he).1 hh
  · intro h s₁ s₂ h₁ h₂
    rw [hq s₁ s₂, ← Set.image_inter (add_left_injective a)]
    exact (mem_infiniteClusters_image_iff (e := Equiv.addRight a) he).2 (h s₁ s₂ h₁ h₂)

/-! ### The whole plane is an ocean -/

/-- The plane is connected. -/
lemma reachIn_univ (u v : Site) : ReachIn (latticeGraph 2) Set.univ u v := by
  have h1 : ReachIn (latticeGraph 2) Set.univ (mk (u 0) (u 1)) (mk (v 0) (u 1)) :=
    (reachIn_hseg (a := min (u 0) (v 0)) (b := max (u 0) (v 0)) (y := u 1)
      (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _)).mono
      (Set.subset_univ _)
  have h2 : ReachIn (latticeGraph 2) Set.univ (mk (v 0) (u 1)) (mk (v 0) (v 1)) :=
    (reachIn_vseg (t := v 0) (c := min (u 1) (v 1)) (e := max (u 1) (v 1))
      (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _)).mono
      (Set.subset_univ _)
  rw [mk_eta u] at h1
  rw [mk_eta v] at h2
  exact h1.trans h2

lemma mem_infiniteClusters_univ (x : Site) :
    x ∈ (latticeGraph 2).infiniteClusters (Set.univ : Set Site) := by
  rw [mem_infiniteClusters_iff_forall_exists]
  intro n
  refine ⟨mk ((n : ℤ) + 1) 0, ?_, reachIn_univ x _⟩
  rw [notMem_box_iff]
  refine Or.inl ?_
  simp only [mk_zero]
  rw [abs_of_nonneg (by positivity)]
  omega

/-- **The whole plane is an ocean**, Georgii's degenerate case `λ^C(G) = 1` in the proof of
(18.16). -/
theorem isOceanIn_univ :
    SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ Set.univ where
  subset := Set.Subset.rfl
  connected := by
    rw [SimpleGraph.connected_induce_iff_forall_reachableIn]
    exact ⟨⟨0, trivial⟩, fun u _ v _ ↦ reachIn_univ u v⟩
  finite_island := by
    intro c
    obtain ⟨x, -⟩ := c.nonempty_supp
    exact absurd x.2 (by simp)

/-! ### Georgii, Lemma (18.16), Steps 2 and 3: the ocean -/

/-- **Georgii, Lemma (18.16), Steps 2 and 3.**  Suppose that `W ⊆ ℤ²` admits barriers in all four
directions (Step 1) and that `R` is a set of cross centres of `W` containing the origin, meeting
the vertical axis arbitrarily far up and down, and containing, for any two of its heights `s` and
`t` on that axis, points `(k, s)` and `(k, t)` with `k` arbitrarily large positive and negative.

Then the cluster of the origin in `W` is an **ocean**: the four Step-2 connections through the
cross centres `(a, s), (a, t), (b, s), (b, t)` surrounding any site `p` off the cluster close up
into a lattice circuit inside the cluster, and `finite_reachIn_star_of_circuit` makes the
`*`-cluster of `p` in the complement finite. -/
theorem exists_isOceanIn_of_crossCentres {W R : Set Site}
    (hbarU : ∀ N y₀ : ℤ, ∃ h : ℤ, y₀ < h ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    (hbarD : ∀ N y₀ : ℤ, ∃ h : ℤ, h < y₀ ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ W)
    (hbarR : ∀ N x₀ : ℤ, ∃ h : ℤ, x₀ < h ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ W)
    (hbarL : ∀ N x₀ : ℤ, ∃ h : ℤ, h < x₀ ∧ ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ W)
    (hR : ∀ i ∈ R, IsCrossCentre W i) (h0 : mk 0 0 ∈ R)
    (hKvUp : ∀ M : ℤ, ∃ n : ℤ, M < n ∧ mk 0 n ∈ R)
    (hKvDown : ∀ M : ℤ, ∃ n : ℤ, n < M ∧ mk 0 n ∈ R)
    (hGridR : ∀ s t M : ℤ, mk 0 s ∈ R → mk 0 t ∈ R → ∃ k : ℤ, M < k ∧ mk k s ∈ R ∧ mk k t ∈ R)
    (hGridL : ∀ s t M : ℤ, mk 0 s ∈ R → mk 0 t ∈ R → ∃ k : ℤ, k < M ∧ mk k s ∈ R ∧ mk k t ∈ R) :
    ∃ ξ : Set Site, ξ ⊆ W ∧
      SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ ξ := by
  classical
  have h0W : mk 0 0 ∈ W := (hR _ h0).mem
  set ξ : Set Site :=
    Subtype.val '' (((latticeGraph 2).induce W).connectedComponentMk ⟨mk 0 0, h0W⟩).supp with hξ
  have hξeq : ξ = {x | ReachIn (latticeGraph 2) W (mk 0 0) x} :=
    SimpleGraph.image_val_supp_connectedComponentMk_eq h0W
  have hξW : ξ ⊆ W := by
    rw [hξeq]; exact fun x hx ↦ hx.mem_right
  refine ⟨ξ, hξW, Set.subset_univ _, SimpleGraph.connected_induce_image_val_supp _, ?_⟩
  -- the islands of the cluster of the origin are finite
  intro c
  obtain ⟨⟨p, hp⟩, hpc⟩ := c.nonempty_supp
  have hcp : c = ((starLatticeGraph 2).induce (Set.univ \ ξ)).connectedComponentMk ⟨p, hp⟩ :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _ |>.1 hpc).symm
  have himg : Subtype.val '' c.supp
      = {q | ReachIn (starLatticeGraph 2) (Set.univ \ ξ) p q} := by
    rw [hcp]
    exact SimpleGraph.image_val_supp_connectedComponentMk_eq hp
  refine Set.Finite.of_finite_image ?_ Subtype.val_injective.injOn
  rw [himg]
  -- the four cross centres around `p`
  obtain ⟨t, ht, htR⟩ := hKvUp ((p 1).natAbs : ℤ)
  obtain ⟨s, hs, hsR⟩ := hKvDown (-((p 1).natAbs : ℤ))
  obtain ⟨b, hb, hbsR, hbtR⟩ := hGridR s t ((p 0).natAbs : ℤ) hsR htR
  obtain ⟨a, ha, hasR, hatR⟩ := hGridL s t (-((p 0).natAbs : ℤ)) hsR htR
  have hst : s < t := by omega
  have hab : a < b := by omega
  have ha0 : a < 0 := by omega
  have h0b : (0 : ℤ) < b := by omega
  have hs0 : s < 0 := by omega
  have h0t : (0 : ℤ) < t := by omega
  have hpa : a < p 0 := by omega
  have hpb : p 0 < b := by omega
  have hps : s < p 1 := by omega
  have hpt : p 1 < t := by omega
  -- the origin reaches the four corners inside `W`
  have hmono : ∀ {A : Set Site} {u v : Site}, ReachIn (latticeGraph 2) (W ∩ A) u v →
      ReachIn (latticeGraph 2) W u v := fun h ↦ h.mono Set.inter_subset_left
  have hO0t : ReachIn (latticeGraph 2) W (mk 0 0) (mk 0 t) :=
    hmono (reachIn_right_of_crossCentres hbarR h0t (hR _ h0) (hR _ htR))
  have hO0s : ReachIn (latticeGraph 2) W (mk 0 0) (mk 0 s) :=
    (hmono (reachIn_left_of_crossCentres hbarL hs0 (hR _ hsR) (hR _ h0))).symm
  have hOat : ReachIn (latticeGraph 2) W (mk 0 0) (mk a t) :=
    hO0t.trans (hmono (reachIn_up_of_crossCentres hbarU ha0 (hR _ hatR) (hR _ htR))).symm
  have hObt : ReachIn (latticeGraph 2) W (mk 0 0) (mk b t) :=
    hO0t.trans (hmono (reachIn_up_of_crossCentres hbarU h0b (hR _ htR) (hR _ hbtR)))
  have hOas : ReachIn (latticeGraph 2) W (mk 0 0) (mk a s) :=
    hO0s.trans (hmono (reachIn_down_of_crossCentres hbarD ha0 (hR _ hasR) (hR _ hsR))).symm
  have hObs : ReachIn (latticeGraph 2) W (mk 0 0) (mk b s) :=
    hO0s.trans (hmono (reachIn_down_of_crossCentres hbarD h0b (hR _ hsR) (hR _ hbsR)))
  -- the four pieces of the circuit
  obtain ⟨Pu, hPu⟩ := exists_walk_support_subset_of_reachIn
    (reachIn_up_of_crossCentres hbarU hab (hR _ hatR) (hR _ hbtR))
  obtain ⟨Pr, hPr⟩ := exists_walk_support_subset_of_reachIn
    (reachIn_right_of_crossCentres hbarR hst (hR _ hbsR) (hR _ hbtR)).symm
  obtain ⟨Pd, hPd⟩ := exists_walk_support_subset_of_reachIn
    (reachIn_down_of_crossCentres hbarD hab (hR _ hasR) (hR _ hbsR)).symm
  obtain ⟨Pl, hPl⟩ := exists_walk_support_subset_of_reachIn
    (reachIn_left_of_crossCentres hbarL hst (hR _ hasR) (hR _ hatR))
  -- every site of the circuit lies in the cluster of the origin
  have hpiece : ∀ {u v : Site} (P : (latticeGraph 2).Walk u v) {A : Set Site},
      (∀ z ∈ P.support, z ∈ W ∩ A) → ReachIn (latticeGraph 2) W (mk 0 0) u →
      ∀ z ∈ P.support, z ∈ ξ := by
    intro u v P A hPsub hOu z hz
    rw [hξeq]
    exact hOu.trans (((SimpleGraph.reachableIn_support P P.start_mem_support hz).mono
      (fun w hw ↦ (hPsub w hw).1)))
  refine (finite_reachIn_star_of_circuit Pu Pr Pd Pl (fun z hz ↦ (hPu z hz).2)
    (fun z hz ↦ (hPr z hz).2) (fun z hz ↦ (hPd z hz).2) (fun z hz ↦ (hPl z hz).2)
    hpa hpb hps hpt (S := ξ) ?_).subset ?_
  · rintro z (hz | hz | hz | hz)
    · exact hpiece Pu hPu hOat z hz
    · exact hpiece Pr hPr hObt z hz
    · exact hpiece Pd hPd hObs z hz
    · exact hpiece Pl hPl hOas z hz
  · have hcompl : (Set.univ \ ξ : Set Site) = ξᶜ := by ext z; simp
    rw [hcompl]

end MeasureTheory.GibbsMeasure.Peierls

end

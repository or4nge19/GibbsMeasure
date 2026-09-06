/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Geodesics in a tree and the two sides of their bonds

A walk `p` of length `G.dist u v` visits `p.getVert l` at distance exactly `l` from `u`
(`SimpleGraph.dist_getVert`). In a tree this pins down which side of the bond
`(p.getVert l, p.getVert (l + 1))` a vertex lies on: everything within distance `l` of `u` lies on
the near side (`SimpleGraph.IsAcyclic.mem_past_getVert`), because the path from `p.getVert l` back
to `u` and on to that vertex never reaches `p.getVert (l + 1)`.

Iterating this along a geodesic between two far apart centres `r`, `r'` produces a *separating
chain*: a sequence of `n + 2` consecutive vertices such that a ball of radius `R` around `r` sits
strictly on the near side of its first bond and a ball of radius `R` around `r'` strictly beyond
every one of its bonds (`SimpleGraph.IsTree.exists_chain_separating`). This is the geometric input
of the two-block mixing estimate for Markov chains on trees (Georgii, proof of Theorem (12.31),
step 5).

## Main results

* `SimpleGraph.dist_getVert`
* `SimpleGraph.IsAcyclic.mem_past_getVert`
* `SimpleGraph.IsTree.exists_chain_separating`
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Distances along a geodesic -/

/-- Every vertex of a walk is within the length of the walk from its source. -/
lemma dist_le_length_of_mem_support {u v z : V} {p : G.Walk u v} (hz : z ∈ p.support) :
    G.dist u z ≤ p.length := by
  classical
  exact (SimpleGraph.dist_le (p.takeUntil z hz)).trans (p.length_takeUntil_le_length hz)

/-- **A geodesic reaches its `l`-th vertex in exactly `l` steps.** -/
lemma dist_getVert (hconn : G.Connected) {u v : V} {p : G.Walk u v}
    (hp : p.length = G.dist u v) {l : ℕ} (hl : l ≤ p.length) :
    G.dist u (p.getVert l) = l := by
  have hle : G.dist u (p.getVert l) ≤ l := by
    have := SimpleGraph.dist_le (p.take l)
    rwa [p.take_length l, min_eq_left hl] at this
  have hge : G.dist (p.getVert l) v ≤ p.length - l := by
    have := SimpleGraph.dist_le (p.drop l)
    rwa [p.drop_length l] at this
  have htri : G.dist u v ≤ G.dist u (p.getVert l) + G.dist (p.getVert l) v :=
    hconn.dist_triangle
  omega

/-! ### The two sides of a bond of a geodesic -/

/-- **The near side of a bond of a geodesic.** In a tree, if `p` is a geodesic from `u` and
`l < p.length`, then every vertex within distance `l` of `u` lies on the `p.getVert l` side of the
bond `(p.getVert l, p.getVert (l + 1))`: the path from `p.getVert l` back along `p` to `u` and
then on to `x` never meets `p.getVert (l + 1)`, which is at distance `l + 1` from `u`. -/
lemma IsAcyclic.mem_past_getVert (hG : G.IsAcyclic) (hconn : G.Connected) {u v : V}
    {p : G.Walk u v} (hp : p.length = G.dist u v) {l : ℕ} (hl : l < p.length) {x : V}
    (hx : G.dist u x ≤ l) : x ∈ G.past (p.getVert l) (p.getVert (l + 1)) := by
  classical
  have hadj : G.Adj (p.getVert l) (p.getVert (l + 1)) := p.adj_getVert_succ hl
  have hdl : G.dist u (p.getVert (l + 1)) = l + 1 := dist_getVert hconn hp hl
  obtain ⟨q₁, hq₁⟩ := (hconn.preconnected u x).exists_walk_length_eq_dist
  set q : G.Walk (p.getVert l) x := ((p.take l).reverse).append q₁ with hqdef
  have hnot : p.getVert (l + 1) ∉ q.support := by
    intro hmem
    rw [hqdef, Walk.support_append] at hmem
    rcases List.mem_append.1 hmem with hmem | hmem
    · rw [Walk.support_reverse, List.mem_reverse] at hmem
      have h1 : G.dist u (p.getVert (l + 1)) ≤ (p.take l).length :=
        dist_le_length_of_mem_support hmem
      rw [p.take_length l, min_eq_left hl.le] at h1
      omega
    · have h1 : G.dist u (p.getVert (l + 1)) ≤ q₁.length :=
        dist_le_length_of_mem_support (List.mem_of_mem_tail hmem)
      omega
  exact hG.mem_past_of_notMem_support hadj q.bypass_isPath fun hmem ↦
    hnot (q.support_bypass_subset_support hmem)

/-- The far side of a bond of a geodesic, read off the reversed geodesic: everything within
distance `l` of the *endpoint* `v` lies beyond the bond `(p.getVert m, p.getVert (m - 1))` as soon
as `m ≤ p.length - l`. -/
lemma IsAcyclic.mem_past_getVert_reverse (hG : G.IsAcyclic) (hconn : G.Connected) {u v : V}
    {p : G.Walk u v} (hp : p.length = G.dist u v) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ p.length)
    {l : ℕ} (hlm : l + m ≤ p.length) {x : V} (hx : G.dist v x ≤ l) :
    x ∈ G.past (p.getVert m) (p.getVert (m - 1)) := by
  have hrevlen : p.reverse.length = G.dist v u := by
    rw [Walk.length_reverse, hp, G.dist_comm]
  have hidx : p.length - m < p.reverse.length := by rw [Walk.length_reverse]; omega
  have hxle : G.dist v x ≤ p.length - m := by omega
  have h := hG.mem_past_getVert hconn hrevlen hidx hxle
  rwa [Walk.getVert_reverse, Walk.getVert_reverse,
    show p.length - (p.length - m) = m by omega,
    show p.length - (p.length - m + 1) = m - 1 by omega] at h

/-! ### Separating chains -/

/-- **A chain of bonds separating two far apart balls of a tree.** If `d(r, r') ≥ 2R + n + 1`,
there are `n + 2` consecutive vertices `w 0, …, w (n + 1)` on the geodesic from `r` to `r'` such
that

* the ball of radius `R` around `r` lies on the `w 0` side of the bond `(w 0, w 1)`;
* the ball of radius `R` around `r'` lies beyond the bond `(w l, w (l + 1))` for every `l ≤ n`;
* the chain never backtracks: `w l` lies on the `w (l + 1)` side of `(w (l + 1), w (l + 2))`.

This is the geometric content of Georgii's `I(B, n)` in the proof of Theorem (12.31), step 5. -/
theorem IsTree.exists_chain_separating (hG : G.IsTree) {r r' : V} {R n : ℕ}
    (hd : 2 * R + n + 1 ≤ G.dist r r') :
    ∃ w : ℕ → V, (∀ l ≤ n, G.Adj (w l) (w (l + 1))) ∧
      (∀ l < n, w l ∈ G.past (w (l + 1)) (w (l + 2))) ∧
      (∀ x, G.dist r x ≤ R → x ∈ G.past (w 0) (w 1)) ∧
      (∀ l ≤ n, ∀ x, G.dist r' x ≤ R → x ∈ G.past (w (l + 1)) (w l)) := by
  obtain ⟨p, hp⟩ := (hG.connected.preconnected r r').exists_walk_length_eq_dist
  have hlen : 2 * R + n + 1 ≤ p.length := by omega
  refine ⟨fun l ↦ p.getVert (R + l), fun l hl ↦ ?_, fun l hl ↦ ?_, fun x hx ↦ ?_,
    fun l hl x hx ↦ ?_⟩
  · have : R + l < p.length := by omega
    simpa [Nat.add_assoc] using p.adj_getVert_succ this
  · have hlt : R + l + 1 < p.length := by omega
    have hxle : G.dist r (p.getVert (R + l)) ≤ R + l + 1 := by
      rw [dist_getVert hG.connected hp (by omega)]; omega
    exact hG.isAcyclic.mem_past_getVert hG.connected hp hlt hxle
  · have hlt : R < p.length := by omega
    exact hG.isAcyclic.mem_past_getVert hG.connected hp hlt hx
  · exact hG.isAcyclic.mem_past_getVert_reverse hG.connected hp (m := R + l + 1)
      (by omega) (by omega) (l := R) (by omega) hx

end SimpleGraph

end

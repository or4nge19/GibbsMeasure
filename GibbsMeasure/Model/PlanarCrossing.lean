/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.StarCrossing
public import GibbsMeasure.Model.PeierlsEstimate

/-!
# The two-dimensional crossing lemma

The combinatorial heart of planar percolation duality on `ℤ²`: in an axis-parallel rectangle,
a *nearest-neighbour* left-to-right crossing meets every `*`-connected top-to-bottom crossing
(Kesten; Grimmett, *Percolation*, Prop. 11.2).  The asymmetry is essential: with both crossings
only `*`-connected the statement is false, as `S = {(0,0), (1,1)}`, `T = {(1,0), (0,1)}` in
`[0,1]²` shows.

The proof is planar duality mod two rather than the Jordan curve theorem, in the same style as
Timár's argument in `GibbsMeasure/Model/Contours.lean` and Georgii's excluded case `n_c(u) = 4`
in `GibbsMeasure/Model/PeierlsEstimate.lean`.

Given a nearest-neighbour walk inside `S` from the left edge of the rectangle to its right edge,
`exists_encircling_walk` closes it into a lattice *circuit* by a detour through the row `e + 2`
above the rectangle and the columns `a - 1`, `b + 1` beside it.  Because the walk ends exactly on
the two vertical edges of the rectangle, the detour meets the rectangle only in `S`.  The
mod-two chain `bondChain` of a circuit is a mod-two cycle (`vertSum_bondChain`), so
`exists_dual_potential` produces a `ZMod 2` labelling `ψ` of the *sites* — the indicator of the
inside of the circuit.  Two facts about `ψ` are all that is needed (`exists_side_fun`):

* `ψ` is constant along every `*`-step both of whose endpoints avoid the circuit — the diagonal
  step is handled by going round a corner, both of whose bonds meet the far endpoint;
* going up a column, `ψ` changes exactly at the horizontal bonds of the circuit.

Below the rectangle and above it `ψ` is therefore constant, while up the column `b` it changes
exactly once — at the single detour bond leaving the right edge of the rectangle.  A `*`-crossing
`T` disjoint from `S` avoids the circuit, so `ψ` would be constant on `T` together with the sites
just below and just above it: contradiction.

## Main declarations

* `rect`: the rectangle `[a, b] × [c, e]` of sites.
* `exists_encircling_walk`: the circuit around a left-to-right crossing.
* `exists_side_fun`: the mod-two side function of a lattice circuit.
* `inter_nonempty_of_crossing_of_starCrossing`: **the crossing lemma**.
* `inter_nonempty_of_crossings`: two nearest-neighbour crossings in the two directions meet.

`bondChain_append` is an addendum to the `bondChain` API of
`GibbsMeasure/Model/PeierlsEstimate.lean` and belongs there.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory.GibbsMeasure.Peierls

/-! ### Arithmetic in `ZMod 2` -/

/-- In characteristic two a sum vanishes exactly when the summands agree. -/
lemma zmodTwo_eq_of_add_eq_zero : ∀ A B : ZMod 2, A + B = 0 → A = B := by decide

/-- In characteristic two every element is its own negative. -/
lemma zmodTwo_add_self : ∀ A : ZMod 2, A + A = 0 := by decide

/-! ### Rectangles of sites -/

/-- The axis-parallel rectangle `[a, b] × [c, e]` of sites of `ℤ²`. -/
def rect (a b c e : ℤ) : Set Site := {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ e}

lemma mem_rect {a b c e : ℤ} {x : Site} :
    x ∈ rect a b c e ↔ a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ e := Iff.rfl

@[simp] lemma mk_mem_rect {a b c e s t : ℤ} :
    mk s t ∈ rect a b c e ↔ a ≤ s ∧ s ≤ b ∧ c ≤ t ∧ t ≤ e := by
  simp [mem_rect]

/-- `*`-adjacency of two sites given in coordinates. -/
lemma starAdj_mk {s r s' r' : ℤ} (hne : ¬(s = s' ∧ r = r')) (h0 : -1 ≤ s - s') (h0' : s - s' ≤ 1)
    (h1 : -1 ≤ r - r') (h1' : r - r' ≤ 1) : (starLatticeGraph 2).Adj (mk s r) (mk s' r') := by
  rw [starLatticeGraph_two_adj_iff]
  refine ⟨fun hc ↦ hne ?_, ?_, ?_⟩
  · rw [site_ext_iff] at hc
    simpa using hc
  · simp only [mk_zero, abs_le]
    omega
  · simp only [mk_one, abs_le]
    omega

/-! ### Straight lattice walks -/

/-- A horizontal lattice walk along the row `y` from the column `x` to the column `x'`. -/
lemma exists_walk_horiz (y : ℤ) {x x' : ℤ} (h : x ≤ x') :
    ∃ p : (latticeGraph 2).Walk (mk x y) (mk x' y),
      ∀ w ∈ p.support, w 1 = y ∧ x ≤ w 0 ∧ w 0 ≤ x' := by
  induction x', h using Int.leInduction with
  | base => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ n hn ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat (adj_mk_horiz n y), fun w hw ↦ ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · obtain ⟨h1, h2, h3⟩ := hp w hw
      exact ⟨h1, h2, by omega⟩
    · simp only [mk_zero, mk_one]
      exact ⟨trivial, by omega, by omega⟩

/-- A vertical lattice walk along the column `x` from the row `y` to the row `y'`. -/
lemma exists_walk_vert (x : ℤ) {y y' : ℤ} (h : y ≤ y') :
    ∃ p : (latticeGraph 2).Walk (mk x y) (mk x y'),
      ∀ w ∈ p.support, w 0 = x ∧ y ≤ w 1 ∧ w 1 ≤ y' := by
  induction y', h using Int.leInduction with
  | base => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ n hn ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.concat (adj_mk_vert x n), fun w hw ↦ ?_⟩
    rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · obtain ⟨h1, h2, h3⟩ := hp w hw
      exact ⟨h1, h2, by omega⟩
    · simp only [mk_zero, mk_one]
      exact ⟨trivial, by omega, by omega⟩

/-! ### Mod-two chains of concatenated walks -/

/-- The mod-two chain of a concatenation is the sum of the chains. -/
lemma bondChain_append {a b c : Site} (p : (latticeGraph 2).Walk a b)
    (q : (latticeGraph 2).Walk b c) (ee : Sym2 Site) :
    bondChain (p.append q) ee = bondChain p ee + bondChain q ee := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [SimpleGraph.Walk.cons_append, bondChain_cons, bondChain_cons, ih]
    ring

/-- A bond one of whose endpoints is off the walk carries the label `0`. -/
lemma bondChain_eq_zero_of_fst_notMem {a b : Site} (p : (latticeGraph 2).Walk a b) {x z : Site}
    (hx : x ∉ p.support) : bondChain p s(x, z) = 0 :=
  bondChain_eq_zero_of_notMem p fun hmem ↦ hx (p.fst_mem_support_of_mem_edges hmem)

/-- A bond one of whose endpoints is off the walk carries the label `0`. -/
lemma bondChain_eq_zero_of_snd_notMem {a b : Site} (p : (latticeGraph 2).Walk a b) {x z : Site}
    (hz : z ∉ p.support) : bondChain p s(x, z) = 0 :=
  bondChain_eq_zero_of_notMem p fun hmem ↦ hz (p.snd_mem_support_of_mem_edges hmem)

/-! ### The circuit around a left-to-right crossing -/

/-- **The circuit around a nearest-neighbour crossing.**  A nearest-neighbour walk inside `S` from
the left edge `{x₀ = a}` of the rectangle `[a, b] × [c, e]` to its right edge `{x₀ = b}` is closed
into a lattice circuit by a detour: one step right, up the column `b + 1`, left along the row
`e + 2`, down the column `a - 1`, one step right.  The resulting circuit meets the rectangle only
in `S`, stays weakly above the row `c`, meets the row `e + 1` only in the columns `a - 1` and
`b + 1`, and crosses the vertical line between the columns `b` and `b + 1` exactly once below the
row `e + 2` — at the single detour bond leaving the right edge. -/
lemma exists_encircling_walk {a b c e yu yv : ℤ} {S : Set Site} (hS : S ⊆ rect a b c e)
    (hSconn : ∀ p ∈ S, ∀ q ∈ S, ReachIn (latticeGraph 2) S p q)
    (hu : mk a yu ∈ S) (hv : mk b yv ∈ S) :
    ∃ C : (latticeGraph 2).Walk (mk a yu) (mk a yu),
      (∀ w ∈ C.support, c ≤ w 1) ∧
      (∀ w ∈ C.support, w ∈ rect a b c e → w ∈ S) ∧
      (∀ w ∈ C.support, w 1 = e + 1 → w 0 = a - 1 ∨ w 0 = b + 1) ∧
      (∀ y : ℤ, y ≤ e + 1 → bondChain C (hbond (mk b y)) = if y = yv then 1 else 0) := by
  classical
  obtain ⟨-, hab, hcu, hue⟩ := mk_mem_rect.1 (hS hu)
  obtain ⟨-, -, hcv, hve⟩ := mk_mem_rect.1 (hS hv)
  obtain ⟨Pw, hPw⟩ := exists_walk_support_subset_of_reachIn (hSconn _ hu _ hv)
  -- the five pieces of the detour
  have hadjR : (latticeGraph 2).Adj (mk b yv) (mk (b + 1) yv) := adj_mk_horiz b yv
  have hadjL : (latticeGraph 2).Adj (mk (a - 1) yu) (mk a yu) := by
    have h := adj_mk_horiz (a - 1) yu
    rwa [show a - 1 + 1 = a from by ring] at h
  obtain ⟨Uw, hUw⟩ := exists_walk_vert (b + 1) (show yv ≤ e + 2 by omega)
  obtain ⟨Tw₀, hTw₀⟩ := exists_walk_horiz (e + 2) (show a - 1 ≤ b + 1 by omega)
  obtain ⟨Dw₀, hDw₀⟩ := exists_walk_vert (a - 1) (show yu ≤ e + 2 by omega)
  refine ⟨Pw.append ((SimpleGraph.Walk.cons hadjR SimpleGraph.Walk.nil).append
    (Uw.append (Tw₀.reverse.append (Dw₀.reverse.append
      (SimpleGraph.Walk.cons hadjL SimpleGraph.Walk.nil))))), ?_, ?_, ?_, ?_⟩
  all_goals
    have hTw : ∀ w ∈ Tw₀.reverse.support, w 1 = e + 2 := by
      intro w hw
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
      exact (hTw₀ w hw).1
    have hDw : ∀ w ∈ Dw₀.reverse.support, w 0 = a - 1 ∧ yu ≤ w 1 := by
      intro w hw
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
      exact ⟨(hDw₀ w hw).1, (hDw₀ w hw).2.1⟩
  · -- the circuit stays weakly above the row `c`
    intro w hw
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hw
    rcases hw with hw | (rfl | rfl) | hw | hw | hw | (rfl | rfl)
    · exact (mem_rect.1 (hS (hPw w hw))).2.2.1
    · simpa using hcv
    · simpa using hcv
    · exact le_trans hcv (hUw w hw).2.1
    · rw [hTw w hw]; omega
    · exact le_trans hcu (hDw w hw).2
    · simpa using hcu
    · simpa using hcu
  · -- the circuit meets the rectangle only in `S`
    intro w hw hwr
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hw
    obtain ⟨hr0, hr1, -, hr3⟩ := mem_rect.1 hwr
    rcases hw with hw | (rfl | rfl) | hw | hw | hw | (rfl | rfl)
    · exact hPw w hw
    · exact hv
    · simp only [mk_zero] at hr1; omega
    · have := (hUw w hw).1; omega
    · have := hTw w hw; omega
    · have := (hDw w hw).1; omega
    · simp only [mk_zero] at hr0; omega
    · exact hu
  · -- the circuit meets the row `e + 1` only beside the rectangle
    intro w hw hw1
    simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hw
    rcases hw with hw | (rfl | rfl) | hw | hw | hw | (rfl | rfl)
    · have := (mem_rect.1 (hS (hPw w hw))).2.2.2; omega
    · simp only [mk_one] at hw1; omega
    · simp only [mk_one] at hw1; omega
    · exact Or.inr (hUw w hw).1
    · have := hTw w hw; omega
    · exact Or.inl (hDw w hw).1
    · simp only [mk_one] at hw1; omega
    · simp only [mk_one] at hw1; omega
  · -- the circuit crosses the line between the columns `b` and `b + 1` exactly once
    intro y hy
    rw [bondChain_append, bondChain_append, bondChain_append, bondChain_append,
      bondChain_append, hbond_mk]
    have hP0 : bondChain Pw s(mk b y, mk (b + 1) y) = 0 := by
      refine bondChain_eq_zero_of_snd_notMem Pw fun hc ↦ ?_
      have := (mem_rect.1 (hS (hPw _ hc))).2.1
      simp only [mk_zero] at this
      omega
    have hU0 : bondChain Uw s(mk b y, mk (b + 1) y) = 0 := by
      refine bondChain_eq_zero_of_fst_notMem Uw fun hc ↦ ?_
      have := (hUw _ hc).1
      simp only [mk_zero] at this
      omega
    have hT0 : bondChain Tw₀.reverse s(mk b y, mk (b + 1) y) = 0 := by
      refine bondChain_eq_zero_of_fst_notMem _ fun hc ↦ ?_
      have := hTw _ hc
      simp only [mk_one] at this
      omega
    have hD0 : bondChain Dw₀.reverse s(mk b y, mk (b + 1) y) = 0 := by
      refine bondChain_eq_zero_of_fst_notMem _ fun hc ↦ ?_
      have := (hDw _ hc).1
      simp only [mk_zero] at this
      omega
    have hL0 : bondChain (SimpleGraph.Walk.cons hadjL SimpleGraph.Walk.nil)
        s(mk b y, mk (b + 1) y) = 0 := by
      refine bondChain_eq_zero_of_snd_notMem _ fun hc ↦ ?_
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;>
        · have := congrArg (fun w : Site ↦ w 0) hc
          simp only [mk_zero] at this
          omega
    have hR0 : bondChain (SimpleGraph.Walk.cons hadjR SimpleGraph.Walk.nil)
        s(mk b y, mk (b + 1) y) = (if y = yv then 1 else 0) := by
      rw [bondChain_cons]
      simp only [bondChain_nil, add_zero]
      by_cases hyy : y = yv
      · subst hyy
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hyy, if_neg]
        intro hc
        rcases Sym2.eq_iff.1 hc with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hyy (congrArg (fun w : Site ↦ w 1) h1).symm
        · have := congrArg (fun w : Site ↦ w 0) h1
          simp only [mk_zero] at this
          omega
    rw [hP0, hR0, hU0, hT0, hD0, hL0]
    ring

/-! ### The mod-two side function of a lattice circuit -/

/-- **The mod-two side function of a lattice circuit.**  A closed lattice walk `C` carries a
`ZMod 2` labelling `ψ` of the sites — the indicator of the inside of `C` — whose increments up a
column are the parities of the horizontal bonds of `C` crossed, and which is constant along every
`*`-step both of whose endpoints avoid `C`.

Only the second statement needs the graph `starLatticeGraph 2`; it holds because for a diagonal
step `z ↝ z'` both bonds of the corner route from `z` to `z'` contain the far endpoint `z'`. -/
lemma exists_side_fun {o : Site} (C : (latticeGraph 2).Walk o o) :
    ∃ ψ : Site → ZMod 2,
      (∀ t y : ℤ, ψ (mk t y) + ψ (mk t (y + 1)) = bondChain C (hbond (mk t (y + 1)))) ∧
      (∀ z z' : Site, z ∉ C.support → z' ∉ C.support →
        (starLatticeGraph 2).Adj z z' → ψ z = ψ z') := by
  classical
  obtain ⟨ψ, hh, hvv⟩ := exists_dual_potential (bondChain C) fun x ↦ by
    rw [vertSum_bondChain]; split_ifs <;> decide
  have key1 : ∀ t y : ℤ, ψ (mk t y) + ψ (mk t (y + 1)) = bondChain C (hbond (mk t (y + 1))) := by
    intro t y
    rw [hbond_mk, hh t (y + 1), show y + 1 - 1 = y from by ring]
    exact add_comm _ _
  have key0 : ∀ t y : ℤ, ψ (mk t y) + ψ (mk (t + 1) y) = bondChain C (vbond (mk (t + 1) y)) := by
    intro t y
    rw [vbond_mk, hvv (t + 1) y, show t + 1 - 1 = t from by ring]
    exact add_comm _ _
  refine ⟨ψ, key1, ?_⟩
  -- one vertical step, needing either endpoint of the bond above to avoid `C`
  have stepV : ∀ s r r' : ℤ, r' = r + 1 →
      (mk s r' ∉ C.support ∨ mk (s + 1) r' ∉ C.support) → ψ (mk s r) = ψ (mk s r') := by
    intro s r r' hr h
    subst hr
    refine zmodTwo_eq_of_add_eq_zero _ _ ?_
    rw [key1 s r, hbond_mk]
    rcases h with h | h
    · exact bondChain_eq_zero_of_fst_notMem C h
    · exact bondChain_eq_zero_of_snd_notMem C h
  -- one horizontal step, needing the right endpoint to avoid `C`
  have stepH : ∀ s s' r : ℤ, s' = s + 1 → mk s' r ∉ C.support →
      ψ (mk s r) = ψ (mk s' r) := by
    intro s s' r hs h
    subst hs
    refine zmodTwo_eq_of_add_eq_zero _ _ ?_
    rw [key0 s r, vbond_mk]
    exact bondChain_eq_zero_of_fst_notMem C h
  have hdiag : ∀ s r s' r' : ℤ, s' = s + 1 → r' = r + 1 → mk s' r' ∉ C.support →
      ψ (mk s r) = ψ (mk s' r') := by
    intro s r s' r' hs hr hoff
    subst hs; subst hr
    rw [stepV s r (r + 1) rfl (Or.inr hoff), stepH s (s + 1) (r + 1) rfl hoff]
  have hanti : ∀ s r s' r' : ℤ, s' = s + 1 → r' = r - 1 → mk s r ∉ C.support →
      mk s' r' ∉ C.support → ψ (mk s r) = ψ (mk s' r') := by
    intro s r s' r' hs hr h h'
    subst hs; subst hr
    rw [← stepV s (r - 1) r (by ring) (Or.inl h), stepH s (s + 1) (r - 1) rfl h']
  intro z z' hz hz' hadj
  obtain ⟨t, y, rfl⟩ : ∃ t y, z = mk t y := ⟨z 0, z 1, (mk_eta z).symm⟩
  obtain ⟨t', y', rfl⟩ : ∃ t y, z' = mk t y := ⟨z' 0, z' 1, (mk_eta z').symm⟩
  obtain ⟨hne, h0, h1⟩ := (starLatticeGraph_two_adj_iff _ _).1 hadj
  simp only [mk_zero, mk_one, abs_le] at h0 h1
  have hne' : ¬(t = t' ∧ y = y') := by
    rintro ⟨rfl, rfl⟩
    exact hne rfl
  have ht : t' = t - 1 ∨ t = t' ∨ t' = t + 1 := by omega
  have hy : y' = y - 1 ∨ y = y' ∨ y' = y + 1 := by omega
  rcases ht with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · exact (hdiag (t - 1) (y - 1) t y (by ring) (by ring) hz).symm
  · exact (stepH (t - 1) t y (by ring) hz).symm
  · exact (hanti (t - 1) (y + 1) t y (by ring) (by ring) hz' hz).symm
  · exact (stepV t (y - 1) y (by ring) (Or.inl hz)).symm
  · exact absurd ⟨rfl, rfl⟩ hne'
  · exact stepV t y (y + 1) rfl (Or.inl hz')
  · exact hanti t y (t + 1) (y - 1) (by ring) (by ring) hz hz'
  · exact stepH t (t + 1) y rfl hz'
  · exact hdiag t y (t + 1) (y + 1) rfl rfl hz'

/-! ### The crossing lemma -/

/-- **The crossing lemma.**  In a rectangle of `ℤ²`, a nearest-neighbour left-to-right crossing
meets every `*`-connected top-to-bottom crossing.

This is the "hard direction" of planar duality for site percolation on the square lattice.  The
asymmetry between the two connectivities is essential: in `[0,1]²` the `*`-connected sets
`{(0,0), (1,1)}` and `{(1,0), (0,1)}` cross in the two directions and are disjoint. -/
theorem inter_nonempty_of_crossing_of_starCrossing {a b c e : ℤ} {S T : Set Site}
    (hS : S ⊆ rect a b c e) (hSconn : ∀ u ∈ S, ∀ v ∈ S, ReachIn (latticeGraph 2) S u v)
    (hSa : ∃ u ∈ S, u 0 = a) (hSb : ∃ v ∈ S, v 0 = b)
    (hT : T ⊆ rect a b c e) (hTconn : ∀ u ∈ T, ∀ v ∈ T, ReachIn (starLatticeGraph 2) T u v)
    (hTc : ∃ w ∈ T, w 1 = c) (hTe : ∃ z ∈ T, z 1 = e) :
    (S ∩ T).Nonempty := by
  classical
  by_contra hST
  have hdisj : ∀ x, x ∈ S → x ∉ T := fun x hx hx' ↦ hST ⟨x, hx, hx'⟩
  obtain ⟨u, huS, hu0⟩ := hSa
  obtain ⟨v, hvS, hv0⟩ := hSb
  obtain ⟨w, hwT, hw1⟩ := hTc
  obtain ⟨z, hzT, hz1⟩ := hTe
  obtain ⟨yu, rfl⟩ : ∃ y : ℤ, u = mk a y := ⟨u 1, by rw [site_ext_iff]; simp [hu0]⟩
  obtain ⟨yv, rfl⟩ : ∃ y : ℤ, v = mk b y := ⟨v 1, by rw [site_ext_iff]; simp [hv0]⟩
  obtain ⟨xw, rfl⟩ : ∃ x : ℤ, w = mk x c := ⟨w 0, by rw [site_ext_iff]; simp [hw1]⟩
  obtain ⟨xz, rfl⟩ : ∃ x : ℤ, z = mk x e := ⟨z 0, by rw [site_ext_iff]; simp [hz1]⟩
  obtain ⟨hab_le, -, hcv, hve⟩ := mk_mem_rect.1 (hS hvS)
  obtain ⟨hwa, hwb, hce, -⟩ := mk_mem_rect.1 (hT hwT)
  obtain ⟨hza, hzb, -, -⟩ := mk_mem_rect.1 (hT hzT)
  obtain ⟨C, hC1, hC2, hC3, hC4⟩ := exists_encircling_walk hS hSconn huS hvS
  obtain ⟨ψ, hkey, hstar⟩ := exists_side_fun C
  -- `T` and the rows just below and just above the rectangle avoid the circuit
  have hToff : ∀ x ∈ T, x ∉ C.support := fun x hx hc ↦ hdisj x (hC2 x hc (hT hx)) hx
  have hoffC : ∀ x : ℤ, mk x (c - 1) ∉ C.support := by
    intro x hc
    have := hC1 _ hc
    simp only [mk_one] at this
    omega
  have hoffE : ∀ x : ℤ, a ≤ x → x ≤ b → mk x (e + 1) ∉ C.support := by
    intro x hx hx' hc
    rcases hC3 _ hc (by simp) with h | h <;> · simp only [mk_zero] at h; omega
  -- `ψ` is constant along the row below the rectangle
  have hrowC0 : ∀ x : ℤ, ψ (mk x (c - 1)) = ψ (mk 0 (c - 1)) := by
    intro x
    induction x using Int.induction_on with
    | zero => rfl
    | succ n ih =>
      rw [← ih]
      exact (hstar _ _ (hoffC (n : ℤ)) (hoffC ((n : ℤ) + 1))
        (starAdj_mk (by omega) (by omega) (by omega) (by omega) (by omega))).symm
    | pred n ih =>
      rw [← ih]
      exact hstar _ _ (hoffC (-(n : ℤ) - 1)) (hoffC (-(n : ℤ)))
        (starAdj_mk (by omega) (by omega) (by omega) (by omega) (by omega))
  have hrowC : ∀ x x' : ℤ, ψ (mk x (c - 1)) = ψ (mk x' (c - 1)) := fun x x' ↦
    (hrowC0 x).trans (hrowC0 x').symm
  -- `ψ` is constant along the row above the rectangle, between its two vertical edges
  have hrowE : ∀ x : ℤ, a ≤ x → x ≤ b → ψ (mk x (e + 1)) = ψ (mk a (e + 1)) := by
    intro x hx
    induction x, hx using Int.leInduction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hle
      rw [← hstar _ _ (hoffE n (by omega) (by omega)) (hoffE (n + 1) (by omega) (by omega))
        (starAdj_mk (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact ih (by omega)
  -- `ψ` takes the same value below and above the rectangle, through `T`
  have hbelow : ψ (mk xw (c - 1)) = ψ (mk xw c) :=
    hstar _ _ (hoffC xw) (hToff _ hwT)
      (starAdj_mk (by omega) (by omega) (by omega) (by omega) (by omega))
  have habove : ψ (mk xz e) = ψ (mk xz (e + 1)) :=
    hstar _ _ (hToff _ hzT) (hoffE xz hza hzb)
      (starAdj_mk (by omega) (by omega) (by omega) (by omega) (by omega))
  have hthrough : ψ (mk xw c) = ψ (mk xz e) :=
    SimpleGraph.ReachableIn.invariant ψ
      (fun p q hp hq hpq ↦ hstar p q (hToff p hp) (hToff q hq) hpq) (hTconn _ hwT _ hzT)
  have hsame : ψ (mk b (c - 1)) = ψ (mk b (e + 1)) :=
    (hrowC b xw).trans (hbelow.trans (hthrough.trans (habove.trans
      ((hrowE xz hza hzb).trans (hrowE b hab_le le_rfl).symm))))
  -- but going up the column `b` the value changes exactly once
  have hstepcol : ∀ y : ℤ, y + 1 ≤ e + 1 → y + 1 ≠ yv → ψ (mk b y) = ψ (mk b (y + 1)) := by
    intro y h1 h2
    refine zmodTwo_eq_of_add_eq_zero _ _ ?_
    rw [hkey b y, hC4 (y + 1) h1, if_neg h2]
  have hA : ∀ y : ℤ, c - 1 ≤ y → y ≤ yv - 1 → ψ (mk b y) = ψ (mk b (c - 1)) := by
    intro y hy
    induction y, hy using Int.leInduction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hle
      rw [← hstepcol n (by omega) (by omega)]
      exact ih (by omega)
  have hB : ∀ y : ℤ, yv ≤ y → y ≤ e + 1 → ψ (mk b y) = ψ (mk b yv) := by
    intro y hy
    induction y, hy using Int.leInduction with
    | base => intro _; rfl
    | succ n hn ih =>
      intro hle
      rw [← hstepcol n (by omega) (by omega)]
      exact ih (by omega)
  have hjump : ψ (mk b (yv - 1)) + ψ (mk b yv) = 1 := by
    have h := hkey b (yv - 1)
    rw [show yv - 1 + 1 = yv from by ring] at h
    rw [h, hC4 yv (by omega), if_pos rfl]
  have hfin : ψ (mk b (c - 1)) + ψ (mk b (e + 1)) = 1 := by
    rw [← hA (yv - 1) (by omega) (by omega), hB (e + 1) (by omega) le_rfl]
    exact hjump
  rw [hsame, zmodTwo_add_self] at hfin
  exact absurd hfin (by decide)

/-- Two nearest-neighbour crossings of a rectangle in the two directions meet. -/
theorem inter_nonempty_of_crossings {a b c e : ℤ} {S T : Set Site}
    (hS : S ⊆ rect a b c e) (hSconn : ∀ u ∈ S, ∀ v ∈ S, ReachIn (latticeGraph 2) S u v)
    (hSa : ∃ u ∈ S, u 0 = a) (hSb : ∃ v ∈ S, v 0 = b)
    (hT : T ⊆ rect a b c e) (hTconn : ∀ u ∈ T, ∀ v ∈ T, ReachIn (latticeGraph 2) T u v)
    (hTc : ∃ w ∈ T, w 1 = c) (hTe : ∃ z ∈ T, z 1 = e) :
    (S ∩ T).Nonempty :=
  inter_nonempty_of_crossing_of_starCrossing hS hSconn hSa hSb hT
    (fun p hp q hq ↦ (hTconn p hp q hq).induction
      (SimpleGraph.ReachableIn.refl hp)
      fun x y hx hy hxy hrec ↦ hrec.trans
        (SimpleGraph.ReachableIn.of_adj hx hy (latticeGraph_le_starLatticeGraph 2 hxy)))
    hTc hTe

end MeasureTheory.GibbsMeasure.Peierls

end

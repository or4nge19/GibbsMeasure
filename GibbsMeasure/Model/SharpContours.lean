/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PhaseTransition

/-!
# Georgii (6.13)/(6.14) sharpened: circuits, the degree-two property, and `ℓ · 3^(ℓ-1)`

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Section 6.2.

`GibbsMeasure/Model/PeierlsEstimate.lean` bounds the number of contours of length `ℓ` through a
fixed bond by `4096 ^ ℓ`, because it counts arbitrary `bondGraph`-connected bond sets.  Georgii
instead counts *circuits*: closed cycles of dual bonds in which every dual vertex meets exactly
two bonds, whence `ℓ · 3 ^ (ℓ - 1)`.  This file develops that circuit structure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false


open MeasureTheory MeasureTheory.GibbsMeasure MeasureTheory.GibbsMeasure.Peierls Set
open SimpleGraph
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.PeierlsSharp

/-! ### Bonds in coordinates -/

/-- The horizontal bond from `(t, u)` to `(t + 1, u)`. -/
def hBond (t u : ℤ) : Sym2 Site := s(mk t u, mk (t + 1) u)

/-- The vertical bond from `(t, u)` to `(t, u + 1)`. -/
def vBond (t u : ℤ) : Sym2 Site := s(mk t u, mk t (u + 1))

lemma mk_inj {a b c d : ℤ} : mk a b = mk c d ↔ a = c ∧ b = d := by
  rw [site_ext_iff]; simp

@[simp] lemma hBond_inj {t u t' u' : ℤ} : hBond t u = hBond t' u' ↔ t = t' ∧ u = u' := by
  simp only [hBond, Sym2.eq_iff, mk_inj]; omega

@[simp] lemma vBond_inj {t u t' u' : ℤ} : vBond t u = vBond t' u' ↔ t = t' ∧ u = u' := by
  simp only [vBond, Sym2.eq_iff, mk_inj]; omega

@[simp] lemma hBond_ne_vBond (t u t' u' : ℤ) : hBond t u ≠ vBond t' u' := by
  intro h
  rw [hBond, vBond, Sym2.eq_iff, mk_inj, mk_inj, mk_inj, mk_inj] at h
  omega

@[simp] lemma vBond_ne_hBond (t u t' u' : ℤ) : vBond t u ≠ hBond t' u' :=
  fun h ↦ hBond_ne_vBond t' u' t u h.symm

lemma plaquette_mk_eq (t u : ℤ) :
    plaquette (mk t u) = {hBond t u, vBond t u, vBond (t + 1) u, hBond t (u + 1)} := by
  rw [plaquette_mk]; rfl

lemma plaquette_eq' (x : Site) :
    plaquette x = {hBond (x 0) (x 1), vBond (x 0) (x 1), vBond (x 0 + 1) (x 1),
      hBond (x 0) (x 1 + 1)} := by
  rw [← mk_eta x, plaquette_mk_eq]; simp

/-- Each plaquette carries exactly four bonds: the dual lattice is `4`-regular. -/
lemma card_plaquette (x : Site) : (plaquette x).card = 4 := by
  rw [plaquette_eq', Finset.card_insert_of_notMem (by simp),
    Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]

lemma mem_plaquette_hBond {t u : ℤ} {x : Site} :
    hBond t u ∈ plaquette x ↔ x 0 = t ∧ (x 1 = u ∨ x 1 = u - 1) := by
  rw [plaquette_eq']
  simp only [Finset.mem_insert, Finset.mem_singleton, hBond_inj, hBond_ne_vBond, false_or]
  omega

lemma mem_plaquette_vBond {t u : ℤ} {x : Site} :
    vBond t u ∈ plaquette x ↔ x 1 = u ∧ (x 0 = t ∨ x 0 = t - 1) := by
  rw [plaquette_eq']
  simp only [Finset.mem_insert, Finset.mem_singleton, vBond_inj, vBond_ne_hBond, false_or,
    or_false]
  omega

/-! ### `ZMod 2` sums along a lattice walk -/

/-- The `ZMod 2` sum of a step weight along a lattice walk. -/
def stepSum (f : Site → Site → ZMod 2) {p q : Site} (w : (latticeGraph 2).Walk p q) : ZMod 2 :=
  (w.darts.map fun d ↦ f d.fst d.snd).sum

@[simp] lemma stepSum_nil (f : Site → Site → ZMod 2) (p : Site) :
    stepSum f (SimpleGraph.Walk.nil : (latticeGraph 2).Walk p p) = 0 := by
  simp [stepSum]

@[simp] lemma stepSum_cons (f : Site → Site → ZMod 2) {p v q : Site}
    (h : (latticeGraph 2).Adj p v) (w : (latticeGraph 2).Walk v q) :
    stepSum f (SimpleGraph.Walk.cons h w) = f p v + stepSum f w := by
  simp [stepSum]

/-- Telescoping: the sum of a coboundary along a walk sees only the endpoints. -/
lemma stepSum_coboundary (g : Site → ZMod 2) {p q : Site} (w : (latticeGraph 2).Walk p q) :
    stepSum (fun a b ↦ g a + g b) w = g p + g q := by
  induction w with
  | nil => simp; exact (by decide : ∀ z : ZMod 2, (0 : ZMod 2) = z + z) _
  | cons h w ih =>
    rw [stepSum_cons, ih]
    exact (by decide : ∀ a b c : ZMod 2, a + b + (b + c) = a + c) _ _ _

lemma stepSum_add (f₁ f₂ : Site → Site → ZMod 2) {p q : Site} (w : (latticeGraph 2).Walk p q) :
    stepSum (fun a b ↦ f₁ a b + f₂ a b) w = stepSum f₁ w + stepSum f₂ w := by
  induction w with
  | nil => simp
  | cons h w ih => rw [stepSum_cons, stepSum_cons, stepSum_cons, ih]; ring

lemma stepSum_congr {f₁ f₂ : Site → Site → ZMod 2}
    (h : ∀ a b : Site, (latticeGraph 2).Adj a b → f₁ a b = f₂ a b)
    {p q : Site} (w : (latticeGraph 2).Walk p q) : stepSum f₁ w = stepSum f₂ w := by
  induction w with
  | nil => simp
  | cons hadj w ih => rw [stepSum_cons, stepSum_cons, ih, h _ _ hadj]

lemma stepSum_eq_zero_of_support {f : Site → Site → ZMod 2} {A : Set Site}
    (hf : ∀ a b : Site, a ∈ A → b ∈ A → f a b = 0)
    {p q : Site} (w : (latticeGraph 2).Walk p q) (hw : ∀ z ∈ w.support, z ∈ A) :
    stepSum f w = 0 := by
  induction w with
  | nil => simp
  | @cons a b c hadj w ih =>
    rw [stepSum_cons, hf a b (hw a (by simp)) (hw b (by simp)),
      ih (fun z hz ↦ hw z (by simp [hz]))]
    ring

/-! ### The three step indicators -/

/-- Indicator that the step `a → b` crosses the horizontal ray running to the right from the
dual vertex at the centre of the plaquette with lower-left corner `y`. -/
def rayInd (y a b : Site) : ZMod 2 :=
  if a 0 = b 0 ∧ y 0 < a 0 ∧ min (a 1) (b 1) = y 1 then 1 else 0

/-- Indicator that the step `a → b` traverses the bond `e`. -/
def bondInd (e : Sym2 Site) (a b : Site) : ZMod 2 := if s(a, b) = e then 1 else 0

/-- Indicator of the half-row `{z : t < z 0, z 1 = u + 1}`. -/
def chiR (t u : ℤ) (z : Site) : ZMod 2 := if t < z 0 ∧ z 1 = u + 1 then 1 else 0

/-- Two horizontally neighbouring rays differ by one vertical bond. -/
lemma rayInd_step_vert (t u : ℤ) {a b : Site} (hab : (latticeGraph 2).Adj a b) :
    rayInd (mk t u) a b + rayInd (mk (t + 1) u) a b = bondInd (vBond (t + 1) u) a b := by
  unfold rayInd bondInd vBond
  rcases (latticeGraph_two_adj_iff' a b).1 hab with rfl | rfl | rfl | rfl <;>
    simp only [Pi.add_apply, e0_zero, e0_one, e1_zero, e1_one, mk_zero, mk_one, Sym2.eq_iff,
      site_ext_iff] <;>
    split_ifs <;> first | rfl | omega

/-- Two vertically neighbouring rays, together with the horizontal bond joining their feet,
form the edge boundary of a half-row. -/
lemma rayInd_step_horiz (t u : ℤ) {a b : Site} (hab : (latticeGraph 2).Adj a b) :
    rayInd (mk t u) a b + rayInd (mk t (u + 1)) a b + bondInd (hBond t (u + 1)) a b
      = chiR t u a + chiR t u b := by
  unfold rayInd bondInd chiR hBond
  rcases (latticeGraph_two_adj_iff' a b).1 hab with rfl | rfl | rfl | rfl <;>
    simp only [Pi.add_apply, e0_zero, e0_one, e1_zero, e1_one, mk_zero, mk_one, Sym2.eq_iff,
      site_ext_iff] <;>
    split_ifs <;> first | rfl | omega


/-! ### Walks inside a set -/

lemma exists_walk_support_of_reachIn {V : Type*} {G : SimpleGraph V} {s : Set V} {u v : V}
    (h : ReachIn G s u v) : ∃ w : G.Walk u v, ∀ z ∈ w.support, z ∈ s := by
  obtain ⟨hu, hv, ⟨p⟩⟩ := h
  suffices H : ∀ (a b : ↥s) (p : (G.induce s).Walk a b),
      ∃ w : G.Walk a.1 b.1, ∀ z ∈ w.support, z ∈ s by
    obtain ⟨w, hw⟩ := H ⟨u, hu⟩ ⟨v, hv⟩ p
    exact ⟨w, hw⟩
  intro a b p
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | @cons a b c hadj p ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨SimpleGraph.Walk.cons (show G.Adj a.1 b.1 from hadj) w, ?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact a.2
    · exact hw z hz

/-- A walk staying in `A` never traverses a bond with an endpoint in a set `B` disjoint
from `A`. -/
lemma stepSum_bondInd_eq_zero {A B : Set Site} (hAB : ∀ z, z ∈ A → z ∈ B → False)
    {c d : Site} (hc : c ∈ B) {p q : Site} (W : (latticeGraph 2).Walk p q)
    (hW : ∀ z ∈ W.support, z ∈ A) : stepSum (bondInd s(c, d)) W = 0 := by
  refine stepSum_eq_zero_of_support (A := A) (fun a b ha hb ↦ ?_) W hW
  unfold bondInd
  refine ite_eq_right (fun h ↦ ?_)
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hAB a ha (by rw [h1]; exact hc)
  · exact hAB b hb (by rw [h2]; exact hc)

lemma stepSum_bondInd_vBond_eq_zero {A B : Set Site} (hAB : ∀ z, z ∈ A → z ∈ B → False)
    {t u : ℤ} (hc : mk t u ∈ B) {p q : Site} (W : (latticeGraph 2).Walk p q)
    (hW : ∀ z ∈ W.support, z ∈ A) : stepSum (bondInd (vBond t u)) W = 0 :=
  stepSum_bondInd_eq_zero hAB hc W hW

lemma stepSum_bondInd_hBond_eq_zero {A B : Set Site} (hAB : ∀ z, z ∈ A → z ∈ B → False)
    {t u : ℤ} (hc : mk t u ∈ B) {p q : Site} (W : (latticeGraph 2).Walk p q)
    (hW : ∀ z ∈ W.support, z ∈ A) : stepSum (bondInd (hBond t u)) W = 0 :=
  stepSum_bondInd_eq_zero hAB hc W hW

/-! ### The plaquette potential of a lattice walk -/

/-- The correction accounting for the two closing bonds `s(x, x + e₀)` and
`s(x + e₀, x + e₀ + e₁)` which turn the walk into a closed cycle. -/
def psi0 (x y : Site) : ZMod 2 := if y 1 = x 1 ∧ y 0 ≤ x 0 then 1 else 0

/-- Georgii's "interior" function for the cycle obtained by closing a walk from `x` to
`x + e₀ + e₁` through `x + e₀`: the value at the plaquette with lower-left corner `y` is the
parity of the number of crossings of the horizontal ray to the right of `y`'s centre. -/
def psi (x : Site) (W : (latticeGraph 2).Walk x (x + e0 + e1)) (y : Site) : ZMod 2 :=
  stepSum (rayInd y) W + psi0 x y

lemma psi_vert (x : Site) (W : (latticeGraph 2).Walk x (x + e0 + e1)) (t u : ℤ) :
    psi x W (mk t u) + psi x W (mk (t + 1) u)
      = stepSum (bondInd (vBond (t + 1) u)) W + (if t = x 0 ∧ u = x 1 then 1 else 0) := by
  have hstep : stepSum (rayInd (mk t u)) W + stepSum (rayInd (mk (t + 1) u)) W
      = stepSum (bondInd (vBond (t + 1) u)) W := by
    rw [← stepSum_add]
    exact stepSum_congr (fun a b hab ↦ rayInd_step_vert t u hab) W
  have hcorr : psi0 x (mk t u) + psi0 x (mk (t + 1) u)
      = (if t = x 0 ∧ u = x 1 then (1 : ZMod 2) else 0) := by
    unfold psi0
    simp only [mk_zero, mk_one]
    split_ifs <;> first | rfl | omega
  unfold psi
  rw [show stepSum (rayInd (mk t u)) W + psi0 x (mk t u)
        + (stepSum (rayInd (mk (t + 1) u)) W + psi0 x (mk (t + 1) u))
      = (stepSum (rayInd (mk t u)) W + stepSum (rayInd (mk (t + 1) u)) W)
        + (psi0 x (mk t u) + psi0 x (mk (t + 1) u)) from by ring, hstep, hcorr]

lemma psi_horiz (x : Site) (W : (latticeGraph 2).Walk x (x + e0 + e1)) (t u : ℤ) :
    psi x W (mk t u) + psi x W (mk t (u + 1))
      = stepSum (bondInd (hBond t (u + 1))) W + (if t = x 0 ∧ u + 1 = x 1 then 1 else 0) := by
  have hstep : stepSum (rayInd (mk t u)) W + stepSum (rayInd (mk t (u + 1))) W
      = (chiR t u x + chiR t u (x + e0 + e1)) + stepSum (bondInd (hBond t (u + 1))) W := by
    rw [← stepSum_add,
      stepSum_congr (f₂ := fun a b ↦ (chiR t u a + chiR t u b) + bondInd (hBond t (u + 1)) a b)
        (fun a b hab ↦ (by
          have h := rayInd_step_horiz t u hab
          exact (by decide : ∀ p q r c : ZMod 2, p + q + r = c → p + q = c + r) _ _ _ _ h)) W,
      stepSum_add, stepSum_coboundary]
  have hcorr : (chiR t u x + chiR t u (x + e0 + e1))
      + (psi0 x (mk t u) + psi0 x (mk t (u + 1)))
      = (if t = x 0 ∧ u + 1 = x 1 then (1 : ZMod 2) else 0) := by
    unfold psi0 chiR
    simp only [mk_zero, mk_one, Pi.add_apply, e0_zero, e0_one, e1_zero, e1_one]
    split_ifs <;> first | rfl | omega
  unfold psi
  rw [show stepSum (rayInd (mk t u)) W + psi0 x (mk t u)
        + (stepSum (rayInd (mk t (u + 1))) W + psi0 x (mk t (u + 1)))
      = (stepSum (rayInd (mk t u)) W + stepSum (rayInd (mk t (u + 1))) W)
        + (psi0 x (mk t u) + psi0 x (mk t (u + 1))) from by ring, hstep]
  rw [show chiR t u x + chiR t u (x + e0 + e1) + stepSum (bondInd (hBond t (u + 1))) W
        + (psi0 x (mk t u) + psi0 x (mk t (u + 1)))
      = stepSum (bondInd (hBond t (u + 1))) W
        + ((chiR t u x + chiR t u (x + e0 + e1)) + (psi0 x (mk t u) + psi0 x (mk t (u + 1))))
      from by ring, hcorr]


/-! ### Georgii (6.14), the case `n_c(u) = 4`: no alternating plaquette -/

/-- Two adjacent sites of `B` carry the same value of the potential. -/
lemma psi_eq_of_adj {A B : Set Site} (hAB : ∀ z, z ∈ A → z ∈ B → False)
    {x : Site} (hx : x ∈ A) (W : (latticeGraph 2).Walk x (x + e0 + e1))
    (hW : ∀ z ∈ W.support, z ∈ A)
    {a b : Site} (ha : a ∈ B) (hb : b ∈ B) (hab : (latticeGraph 2).Adj a b) :
    psi x W a = psi x W b := by
  have key : ∀ c : Site, c ∈ B → ∀ d : Site, d ∈ B → (d = c + e0 ∨ d = c + e1) →
      psi x W c + psi x W d = 0 := by
    intro c hc d hd hcd
    have hc0 : mk (c 0) (c 1) = c := mk_eta c
    rcases hcd with rfl | rfl
    · have hc1 : mk (c 0 + 1) (c 1) = c + e0 := by rw [← mk_add_e0, hc0]
      have h := psi_vert x W (c 0) (c 1)
      rw [hc0, hc1] at h
      rw [h, stepSum_bondInd_vBond_eq_zero (A := A) hAB (t := c 0 + 1) (u := c 1)
        (by rw [hc1]; exact hd) W hW, ite_eq_right (fun hcx ↦ ?_)]
      · ring
      · exact hAB c (by rw [← hc0, hcx.1, hcx.2, mk_eta]; exact hx) hc
    · have hc2 : mk (c 0) (c 1 + 1) = c + e1 := by rw [← mk_add_e1, hc0]
      have h := psi_horiz x W (c 0) (c 1)
      rw [hc0, hc2] at h
      rw [h, stepSum_bondInd_hBond_eq_zero (A := A) hAB (t := c 0) (u := c 1 + 1)
        (by rw [hc2]; exact hd) W hW, ite_eq_right (fun hcx ↦ ?_)]
      · ring
      · exact hAB (c + e1) (by rw [← hc2, hcx.1, hcx.2, mk_eta]; exact hx) hd
  have hsum : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  rcases (latticeGraph_two_adj_iff' a b).1 hab with rfl | rfl | rfl | rfl
  · exact hsum _ _ (key a ha _ hb (Or.inl rfl))
  · exact (hsum _ _ (key b hb _ ha (Or.inl rfl))).symm
  · exact hsum _ _ (key a ha _ hb (Or.inr rfl))
  · exact (hsum _ _ (key b hb _ ha (Or.inr rfl))).symm

/-- **Georgii (6.14), the case `n_c(u) = 4`.**  If `A` and `B` are disjoint sets of sites, each
connected in `ℤ²`, then the four corners of a unit square cannot alternate between them: the two
diagonal corners `x`, `x + e₀ + e₁` cannot lie in `A` while `x + e₀`, `x + e₁` lie in `B`.

This replaces Georgii's appeal to the Jordan curve theorem.  The proof is the mod-two crossing
argument: a walk in `A` from `x` to `x + e₀ + e₁`, closed up through `x + e₀`, defines a
`ZMod 2` potential `psi` on plaquettes whose coboundary is supported on the cycle; the two
plaquettes `x + e₀` and `x + e₁` get different values, yet `psi` is constant along `B`. -/
theorem no_alternating_plaquette {A B : Set Site}
    (hAB : ∀ z, z ∈ A → z ∈ B → False)
    (hA : ∀ p ∈ A, ∀ q ∈ A, ReachIn (latticeGraph 2) A p q)
    (hB : ∀ p ∈ B, ∀ q ∈ B, ReachIn (latticeGraph 2) B p q)
    {x : Site} (hx : x ∈ A) (hx' : x + e0 + e1 ∈ A) (hy : x + e0 ∈ B) (hy' : x + e1 ∈ B) :
    False := by
  obtain ⟨W, hW⟩ := exists_walk_support_of_reachIn (hA x hx _ hx')
  have hx0 : mk (x 0) (x 1) = x := mk_eta x
  have hx1 : mk (x 0 + 1) (x 1) = x + e0 := by rw [← mk_add_e0, hx0]
  have hx2 : mk (x 0) (x 1 + 1) = x + e1 := by rw [← mk_add_e1, hx0]
  -- the two plaquettes `x + e₀` and `x + e₁` have different potentials
  have hV : psi x W x + psi x W (x + e0) = 1 := by
    have h := psi_vert x W (x 0) (x 1)
    rw [hx0, hx1] at h
    rw [h, stepSum_bondInd_vBond_eq_zero (A := A) hAB (t := x 0 + 1) (u := x 1)
      (by rw [hx1]; exact hy) W hW, ite_eq_left ⟨rfl, rfl⟩]
    ring
  have hH : psi x W x = psi x W (x + e1) := by
    have h := psi_horiz x W (x 0) (x 1)
    rw [hx0, hx2] at h
    have h0 : psi x W x + psi x W (x + e1) = 0 := by
      rw [h, stepSum_bondInd_hBond_eq_zero (A := A) hAB (t := x 0) (u := x 1 + 1)
        (by rw [hx2]; exact hy') W hW, ite_eq_right (fun hcx ↦ by omega)]
      ring
    exact (by decide : ∀ p q : ZMod 2, p + q = 0 → p = q) _ _ h0
  -- but the potential is constant along `B`
  have hconst : psi x W (x + e0) = psi x W (x + e1) :=
    ReachIn.invariant (psi x W)
      (fun a b haB hbB hab ↦ psi_eq_of_adj hAB hx W hW haB hbB hab) (hB _ hy _ hy')
  rw [hconst, ← hH] at hV
  exact (by decide : ∀ p : ZMod 2, p + p ≠ (1 : ZMod 2)) _ hV


/-! ### Georgii (6.14): every dual vertex of the outer boundary has degree two -/

/-- A bond lies in the outer boundary iff its two endpoints are separated by the infinite
outside. -/
lemma mem_outerBoundary_iff_xor {D : Set Site} {u v : Site} (huv : (latticeGraph 2).Adj u v) :
    s(u, v) ∈ outerBoundary D ↔ ¬ (u ∈ outside D ↔ v ∈ outside D) := by
  rw [mem_outerBoundary_iff huv]
  constructor
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩) hiff
    · exact notMem_of_mem_outside (hiff.2 hv) hu
    · exact notMem_of_mem_outside (hiff.1 hu) hv
  · intro h
    by_cases hu : u ∈ outside D
    · have hv : v ∉ outside D := fun hv ↦ h ⟨fun _ ↦ hv, fun _ ↦ hu⟩
      exact Or.inr ⟨mem_of_adj_outside hv huv.symm hu, hu⟩
    · have hv : v ∈ outside D := by
        by_contra hv
        exact h ⟨fun h' ↦ absurd h' hu, fun h' ↦ absurd h' hv⟩
      exact Or.inl ⟨mem_of_adj_outside hu huv hv, hv⟩

/-- The infinite outside is connected *within itself*. -/
lemma reachIn_outside {D : Set Site} (hD : D.Finite) {j k : Site}
    (hj : j ∈ outside D) (hk : k ∈ outside D) :
    ReachIn (latticeGraph 2) (outside D) j k := by
  refine (reachIn_of_mem_outside hD hj hk).induction
    (P := fun v ↦ ReachIn (latticeGraph 2) (outside D) j v) (ReachIn.refl hj) ?_
  intro a b ha hb hab hja
  exact hja.trans (ReachIn.of_adj hja.mem_right (mem_outside_of_adj hb hab.symm hja.mem_right) hab)

open Classical in
/-- Georgii's `n_c(u)`: the number of bonds of `c` meeting the dual vertex at the centre of the
plaquette whose lower-left corner is `x`. -/
def dualDeg (c : Set (Sym2 Site)) (x : Site) : ℕ := ((plaquette x).filter (· ∈ c)).card

open Classical in
lemma dualDeg_eq (c : Set (Sym2 Site)) (x : Site) :
    dualDeg c x = (if hBond (x 0) (x 1) ∈ c then 1 else 0)
      + ((if vBond (x 0) (x 1) ∈ c then 1 else 0)
        + ((if vBond (x 0 + 1) (x 1) ∈ c then 1 else 0)
          + (if hBond (x 0) (x 1 + 1) ∈ c then 1 else 0))) := by
  rw [dualDeg, Finset.card_filter, plaquette_eq', Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]

open Classical in
lemma dualDeg_le_four (c : Set (Sym2 Site)) (x : Site) : dualDeg c x ≤ 4 := by
  rw [dualDeg, ← card_plaquette x]
  exact Finset.card_filter_le _ _

open Classical in
lemma dualDeg_pos {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site} (he : e ∈ plaquette x)
    (hec : e ∈ c) : 0 < dualDeg c x :=
  Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hec⟩⟩

open Classical in
lemma forall_mem_of_dualDeg_eq_four {c : Set (Sym2 Site)} {x : Site} (h : dualDeg c x = 4)
    {e : Sym2 Site} (he : e ∈ plaquette x) : e ∈ c := by
  rw [dualDeg] at h
  have hEq : (plaquette x).filter (· ∈ c) = plaquette x :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [card_plaquette, h])
  exact (Finset.mem_filter.1 (hEq ▸ he)).2

/-- **Georgii Lemma (6.14), the degree-two property.**  For a finite, nonempty, connected set of
sites `D ⊆ ℤ²`, every dual vertex met by the outer boundary of `D` meets exactly two of its
bonds: the outer boundary is a *circuit*, `n_c(u) = 2`. -/
theorem outerBoundary_dualDeg_eq_two {D : Set Site} (hD : D.Finite) (_hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) {x : Site}
    (hx : ∃ e ∈ plaquette x, e ∈ outerBoundary D) :
    dualDeg (outerBoundary D) x = 2 := by
  classical
  obtain ⟨e, hep, hec⟩ := hx
  -- the four corners of the plaquette
  set p1 : Site := mk (x 0) (x 1) with hp1
  set p2 : Site := mk (x 0 + 1) (x 1) with hp2
  set p3 : Site := mk (x 0) (x 1 + 1) with hp3
  set p4 : Site := mk (x 0 + 1) (x 1 + 1) with hp4
  have hadj12 : (latticeGraph 2).Adj p1 p2 := adj_mk_horiz _ _
  have hadj13 : (latticeGraph 2).Adj p1 p3 := adj_mk_vert _ _
  have hadj24 : (latticeGraph 2).Adj p2 p4 := adj_mk_vert _ _
  have hadj34 : (latticeGraph 2).Adj p3 p4 := adj_mk_horiz _ _
  have hb1 : hBond (x 0) (x 1) ∈ outerBoundary D ↔ ¬ (p1 ∈ outside D ↔ p2 ∈ outside D) :=
    mem_outerBoundary_iff_xor hadj12
  have hb2 : vBond (x 0) (x 1) ∈ outerBoundary D ↔ ¬ (p1 ∈ outside D ↔ p3 ∈ outside D) :=
    mem_outerBoundary_iff_xor hadj13
  have hb3 : vBond (x 0 + 1) (x 1) ∈ outerBoundary D ↔ ¬ (p2 ∈ outside D ↔ p4 ∈ outside D) :=
    mem_outerBoundary_iff_xor hadj24
  have hb4 : hBond (x 0) (x 1 + 1) ∈ outerBoundary D ↔ ¬ (p3 ∈ outside D ↔ p4 ∈ outside D) :=
    mem_outerBoundary_iff_xor hadj34
  -- parity: `n_c(u)` is even (Georgii excludes `n_c(u) ∈ {1, 3}`)
  have hpar : dualDeg (outerBoundary D) x % 2 = 0 := by
    rw [dualDeg_eq]
    by_cases h1 : p1 ∈ outside D <;> by_cases h2 : p2 ∈ outside D <;>
      by_cases h3 : p3 ∈ outside D <;> by_cases h4 : p4 ∈ outside D <;>
      simp only [hb1, hb2, hb3, hb4, h1, h2, h3, h4, iff_true, iff_false, not_true, not_false_iff,
        ite_true, ite_false]
  -- `n_c(u) ≠ 0`
  have hpos : 0 < dualDeg (outerBoundary D) x := dualDeg_pos hep hec
  -- `n_c(u) ≠ 4`
  have hne4 : dualDeg (outerBoundary D) x ≠ 4 := by
    intro h4
    have hall := fun {f : Sym2 Site} (hf : f ∈ plaquette x) ↦ forall_mem_of_dualDeg_eq_four h4 hf
    have hp : plaquette x = {hBond (x 0) (x 1), vBond (x 0) (x 1), vBond (x 0 + 1) (x 1),
        hBond (x 0) (x 1 + 1)} := plaquette_eq' x
    have hc1 := hb1.1 (hall (by rw [hp]; simp))
    have hc2 := hb2.1 (hall (by rw [hp]; simp))
    have hc3 := hb3.1 (hall (by rw [hp]; simp))
    have hc4 := hb4.1 (hall (by rw [hp]; simp))
    -- connectivity data
    have hDreach : ∀ p ∈ D, ∀ q ∈ D, ReachIn (latticeGraph 2) D p q := by
      rw [induce_connected_iff] at hconn
      exact fun p hp q hq ↦ hconn.2 p q hp hq
    have hOreach : ∀ p ∈ outside D, ∀ q ∈ outside D,
        ReachIn (latticeGraph 2) (outside D) p q := fun p hp q hq ↦ reachIn_outside hD hp hq
    have hdisj1 : ∀ z, z ∈ outside D → z ∈ D → False := fun z hz hzD ↦ notMem_of_mem_outside hz hzD
    have hdisj2 : ∀ z, z ∈ D → z ∈ outside D → False := fun z hzD hz ↦ notMem_of_mem_outside hz hzD
    have hsq1 : p1 + e0 = p2 := by rw [hp1, hp2, mk_add_e0]
    have hsq2 : p1 + e1 = p3 := by rw [hp1, hp3, mk_add_e1]
    have hsq3 : p1 + e0 + e1 = p4 := by rw [hp1, hp4, mk_add_e0, mk_add_e1]
    by_cases h1 : p1 ∈ outside D
    · -- `p1, p4` outside, `p2, p3` in `D`
      have h2 : p2 ∉ outside D := fun h ↦ hc1 ⟨fun _ ↦ h, fun _ ↦ h1⟩
      have h3 : p3 ∉ outside D := fun h ↦ hc2 ⟨fun _ ↦ h, fun _ ↦ h1⟩
      have h4' : p4 ∈ outside D := by
        by_contra h4'
        exact hc3 ⟨fun h ↦ absurd h h2, fun h ↦ absurd h h4'⟩
      refine no_alternating_plaquette hdisj1 hOreach hDreach (x := p1) h1 ?_ ?_ ?_
      · rw [hsq3]; exact h4'
      · rw [hsq1]; exact mem_of_adj_outside h2 hadj12.symm h1
      · rw [hsq2]; exact mem_of_adj_outside h3 hadj13.symm h1
    · -- `p2, p3` outside, `p1, p4` in `D`
      have h2 : p2 ∈ outside D := by
        by_contra h2
        exact hc1 ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h2⟩
      have h3 : p3 ∈ outside D := by
        by_contra h3
        exact hc2 ⟨fun h ↦ absurd h h1, fun h ↦ absurd h h3⟩
      have h4' : p4 ∉ outside D := fun h ↦ hc3 ⟨fun _ ↦ h, fun _ ↦ h2⟩
      refine no_alternating_plaquette hdisj2 hDreach hOreach (x := p1)
        (mem_of_adj_outside h1 hadj12 h2) ?_ ?_ ?_
      · rw [hsq3]; exact mem_of_adj_outside h4' hadj34.symm h3
      · rw [hsq1]; exact h2
      · rw [hsq2]; exact h3
  have hle := dualDeg_le_four (outerBoundary D) x
  omega


/-! ### M2: the circuit structure and Georgii's counting Lemma (6.13)

A bond lies in exactly two plaquettes; `otherPlaq e x` is the plaquette of `e` other than `x`. -/

lemma mem_plaquette_iff {e : Sym2 Site} {x : Site} :
    e ∈ plaquette x ↔ e = hBond (x 0) (x 1) ∨ e = vBond (x 0) (x 1) ∨
      e = vBond (x 0 + 1) (x 1) ∨ e = hBond (x 0) (x 1 + 1) := by
  rw [plaquette_eq']
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- The dual vertex on the other side of the bond `e` from the dual vertex `x`. -/
def otherPlaq (e : Sym2 Site) (x : Site) : Site :=
  if e = hBond (x 0) (x 1) then mk (x 0) (x 1 - 1)
  else if e = hBond (x 0) (x 1 + 1) then mk (x 0) (x 1 + 1)
  else if e = vBond (x 0) (x 1) then mk (x 0 - 1) (x 1)
  else mk (x 0 + 1) (x 1)

@[simp] lemma otherPlaq_hBond_bot (x : Site) :
    otherPlaq (hBond (x 0) (x 1)) x = mk (x 0) (x 1 - 1) := by
  rw [otherPlaq, ite_eq_left rfl]

@[simp] lemma otherPlaq_hBond_top (x : Site) :
    otherPlaq (hBond (x 0) (x 1 + 1)) x = mk (x 0) (x 1 + 1) := by
  rw [otherPlaq, ite_eq_right (by simp), ite_eq_left rfl]

@[simp] lemma otherPlaq_vBond_left (x : Site) :
    otherPlaq (vBond (x 0) (x 1)) x = mk (x 0 - 1) (x 1) := by
  rw [otherPlaq, ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_left rfl]

@[simp] lemma otherPlaq_vBond_right (x : Site) :
    otherPlaq (vBond (x 0 + 1) (x 1)) x = mk (x 0 + 1) (x 1) := by
  rw [otherPlaq, ite_eq_right (by simp), ite_eq_right (by simp), ite_eq_right (by simp)]

lemma otherPlaq_ne {e : Sym2 Site} {x : Site} (he : e ∈ plaquette x) : otherPlaq e x ≠ x := by
  rw [mem_plaquette_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [otherPlaq_hBond_bot, otherPlaq_vBond_left, otherPlaq_vBond_right,
      otherPlaq_hBond_top] <;>
    · intro h
      have h0 := congrArg (fun z : Site ↦ z 0) h
      have h1 := congrArg (fun z : Site ↦ z 1) h
      simp only [mk_zero, mk_one] at h0 h1
      omega

lemma otherPlaq_mem {e : Sym2 Site} {x : Site} (he : e ∈ plaquette x) :
    e ∈ plaquette (otherPlaq e x) := by
  rw [mem_plaquette_iff] at he
  rcases he with rfl | rfl | rfl | rfl <;>
    simp only [otherPlaq_hBond_bot, otherPlaq_vBond_left, otherPlaq_vBond_right,
      otherPlaq_hBond_top, mem_plaquette_iff, mk_zero, mk_one, hBond_inj, vBond_inj,
      hBond_ne_vBond, vBond_ne_hBond, false_or, or_false, true_and, and_true, true_or,
      or_true] <;> omega

lemma otherPlaq_otherPlaq {e : Sym2 Site} {x : Site} (he : e ∈ plaquette x) :
    otherPlaq e (otherPlaq e x) = x := by
  rw [mem_plaquette_iff] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [otherPlaq_hBond_bot]
    rw [show hBond (x 0) (x 1)
        = hBond ((mk (x 0) (x 1 - 1)) 0) ((mk (x 0) (x 1 - 1)) 1 + 1) from by simp,
      otherPlaq_hBond_top]
    simp
  · rw [otherPlaq_vBond_left]
    rw [show vBond (x 0) (x 1)
        = vBond ((mk (x 0 - 1) (x 1)) 0 + 1) ((mk (x 0 - 1) (x 1)) 1) from by simp,
      otherPlaq_vBond_right]
    simp
  · rw [otherPlaq_vBond_right]
    rw [show vBond (x 0 + 1) (x 1)
        = vBond ((mk (x 0 + 1) (x 1)) 0) ((mk (x 0 + 1) (x 1)) 1) from by simp,
      otherPlaq_vBond_left]
    simp
  · rw [otherPlaq_hBond_top]
    rw [show hBond (x 0) (x 1 + 1)
        = hBond ((mk (x 0) (x 1 + 1)) 0) ((mk (x 0) (x 1 + 1)) 1) from by simp,
      otherPlaq_hBond_bot]
    simp

/-- The two dual vertices of a bond. -/
lemma eq_or_eq_otherPlaq {e : Sym2 Site} {x y : Site} (hx : e ∈ plaquette x)
    (hy : e ∈ plaquette y) : y = x ∨ y = otherPlaq e x := by
  rw [mem_plaquette_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rw [mem_plaquette_hBond] at hy
    rw [otherPlaq_hBond_bot]
    rcases hy.2 with h | h
    · exact Or.inl (by rw [← mk_eta y, ← mk_eta x, mk_inj]; exact ⟨hy.1, h⟩)
    · exact Or.inr (by rw [← mk_eta y, mk_inj]; exact ⟨hy.1, h⟩)
  · rw [mem_plaquette_vBond] at hy
    rw [otherPlaq_vBond_left]
    rcases hy.2 with h | h
    · exact Or.inl (by rw [← mk_eta y, ← mk_eta x, mk_inj]; exact ⟨h, hy.1⟩)
    · exact Or.inr (by rw [← mk_eta y, mk_inj]; exact ⟨h, hy.1⟩)
  · rw [mem_plaquette_vBond] at hy
    rw [otherPlaq_vBond_right]
    rcases hy.2 with h | h
    · exact Or.inr (by rw [← mk_eta y, mk_inj]; exact ⟨h, hy.1⟩)
    · exact Or.inl (by rw [← mk_eta y, ← mk_eta x, mk_inj]; exact ⟨by omega, hy.1⟩)
  · rw [mem_plaquette_hBond] at hy
    rw [otherPlaq_hBond_top]
    rcases hy.2 with h | h
    · exact Or.inr (by rw [← mk_eta y, mk_inj]; exact ⟨hy.1, h⟩)
    · exact Or.inl (by rw [← mk_eta y, ← mk_eta x, mk_inj]; exact ⟨hy.1, by omega⟩)


/-! ### Circuits and the traversal step -/

open Classical in
/-- The bonds of `c` meeting the dual vertex `x`. -/
def bondsAt (c : Set (Sym2 Site)) (x : Site) : Finset (Sym2 Site) := (plaquette x).filter (· ∈ c)

open Classical in
@[simp] lemma mem_bondsAt {c : Set (Sym2 Site)} {x : Site} {f : Sym2 Site} :
    f ∈ bondsAt c x ↔ f ∈ plaquette x ∧ f ∈ c := by
  rw [bondsAt, Finset.mem_filter]

lemma dualDeg_eq_card_bondsAt (c : Set (Sym2 Site)) (x : Site) :
    dualDeg c x = (bondsAt c x).card := rfl

/-- **Georgii's circuits.**  A finite set of bonds, connected in the plaquette-adjacency graph,
in which every dual vertex met by the set meets exactly two of its bonds (`n_c(u) = 2`). -/
structure IsCircuit (c : Finset (Sym2 Site)) : Prop where
  connected : (bondGraph.induce (↑c : Set (Sym2 Site))).Connected
  degree_two : ∀ {x : Site} {e : Sym2 Site}, e ∈ plaquette x → e ∈ c →
    dualDeg (↑c : Set (Sym2 Site)) x = 2

open Classical in
/-- The partner of `e` at the dual vertex `x`: the other bond of `c` meeting `x`. -/
def partner (c : Set (Sym2 Site)) (x : Site) (e : Sym2 Site) : Sym2 Site :=
  if h : ((bondsAt c x).erase e).Nonempty then h.choose else e

lemma card_bondsAt_erase {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) : ((bondsAt c x).erase e).card = 1 := by
  rw [Finset.card_erase_of_mem he, ← dualDeg_eq_card_bondsAt, h2]

open Classical in
lemma partner_mem_erase {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) :
    partner c x e ∈ (bondsAt c x).erase e := by
  have hne : ((bondsAt c x).erase e).Nonempty :=
    Finset.card_pos.1 (by rw [card_bondsAt_erase h2 he]; norm_num)
  rw [partner, dite_eq_left hne]
  exact hne.choose_spec

lemma partner_mem {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) : partner c x e ∈ bondsAt c x :=
  (Finset.mem_erase.1 (partner_mem_erase h2 he)).2

lemma partner_ne {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) : partner c x e ≠ e :=
  (Finset.mem_erase.1 (partner_mem_erase h2 he)).1

/-- At a dual vertex of degree two, the partner is the *only* other bond. -/
lemma partner_unique {c : Set (Sym2 Site)} {x : Site} {e f : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) (hf : f ∈ bondsAt c x) (hfe : f ≠ e) :
    f = partner c x e := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.1 (card_bondsAt_erase h2 he)
  have h1 : f ∈ (bondsAt c x).erase e := Finset.mem_erase.2 ⟨hfe, hf⟩
  have h3 := partner_mem_erase h2 he
  rw [hg, Finset.mem_singleton] at h1 h3
  rw [h1, h3]

lemma partner_partner {c : Set (Sym2 Site)} {x : Site} {e : Sym2 Site}
    (h2 : dualDeg c x = 2) (he : e ∈ bondsAt c x) : partner c x (partner c x e) = e :=
  (partner_unique h2 (partner_mem h2 he) he (Ne.symm (partner_ne h2 he))).symm

/-- The traversal state: a bond of `c` together with a dual vertex it meets. -/
def DualState (c : Set (Sym2 Site)) (p : Sym2 Site × Site) : Prop := p.1 ∈ bondsAt c p.2

/-- One step of Georgii's traversal of a circuit: from the bond `p.1` seen at the dual vertex
`p.2`, move to the other bond of `c` at `p.2` and on to its far dual vertex. -/
def dualStep (c : Set (Sym2 Site)) (p : Sym2 Site × Site) : Sym2 Site × Site :=
  (partner c p.2 p.1, otherPlaq (partner c p.2 p.1) p.2)

/-- Reversing the direction of the traversal at a bond. -/
def dualRev (p : Sym2 Site × Site) : Sym2 Site × Site := (p.1, otherPlaq p.1 p.2)

lemma dualState_dualRev {c : Set (Sym2 Site)} {p : Sym2 Site × Site} (hp : DualState c p) :
    DualState c (dualRev p) := by
  obtain ⟨h1, h2⟩ := mem_bondsAt.1 hp
  exact mem_bondsAt.2 ⟨otherPlaq_mem h1, h2⟩

lemma dualRev_ne {c : Set (Sym2 Site)} {p : Sym2 Site × Site} (hp : DualState c p) :
    dualRev p ≠ p := fun h ↦ otherPlaq_ne (mem_bondsAt.1 hp).1 (congrArg Prod.snd h)

lemma dualRev_dualRev {c : Set (Sym2 Site)} {p : Sym2 Site × Site} (hp : DualState c p) :
    dualRev (dualRev p) = p := by
  have h := otherPlaq_otherPlaq (mem_bondsAt.1 hp).1
  simp only [dualRev, h]

section Irreducible
-- `partner` is a `dite` on `Finset.Nonempty` for a `Finset (Sym2 Site)` cut out of a `Set` by
-- classical decidability, and `otherPlaq` a four-way `if` on `Sym2 Site` equalities. Unfolding
-- either during `whnf`/`isDefEq` is what made this file need a five-fold `maxHeartbeats` bump:
-- the traversal lemmas below need only their API, so both are sealed here.
attribute [local irreducible] partner otherPlaq

@[simp] lemma dualStep_fst (c : Set (Sym2 Site)) (p : Sym2 Site × Site) :
    (dualStep c p).1 = partner c p.2 p.1 := rfl

@[simp] lemma dualStep_snd (c : Set (Sym2 Site)) (p : Sym2 Site × Site) :
    (dualStep c p).2 = otherPlaq (partner c p.2 p.1) p.2 := rfl

@[simp] lemma dualRev_fst (p : Sym2 Site × Site) : (dualRev p).1 = p.1 := rfl

@[simp] lemma dualRev_snd (p : Sym2 Site × Site) : (dualRev p).2 = otherPlaq p.1 p.2 := rfl

lemma dualState_dualStep {c : Set (Sym2 Site)} {p : Sym2 Site × Site}
    (h2 : dualDeg c p.2 = 2) (hp : DualState c p) : DualState c (dualStep c p) := by
  obtain ⟨h1, h3⟩ := mem_bondsAt.1 (partner_mem h2 hp)
  show (dualStep c p).1 ∈ bondsAt c (dualStep c p).2
  rw [dualStep_fst, dualStep_snd]
  exact mem_bondsAt.2 ⟨otherPlaq_mem h1, h3⟩

lemma dualStep_fst_ne {c : Set (Sym2 Site)} {p : Sym2 Site × Site}
    (h2 : dualDeg c p.2 = 2) (hp : DualState c p) : (dualStep c p).1 ≠ p.1 := partner_ne h2 hp

/-- Reversing after a step and stepping again reverses: `step ∘ rev ∘ step = rev`. -/
lemma dualStep_dualRev_dualStep {c : Set (Sym2 Site)} {p : Sym2 Site × Site}
    (h2 : dualDeg c p.2 = 2) (hp : DualState c p) :
    dualStep c (dualRev (dualStep c p)) = dualRev p := by
  have hfm : partner c p.2 p.1 ∈ bondsAt c p.2 := partner_mem h2 hp
  have hrev : dualRev (dualStep c p) = (partner c p.2 p.1, p.2) := by
    refine Prod.ext ?_ ?_
    · rw [dualRev_fst, dualStep_fst]
    · rw [dualRev_snd, dualStep_fst, dualStep_snd,
        otherPlaq_otherPlaq (mem_bondsAt.1 hfm).1]
  rw [hrev]
  refine Prod.ext ?_ ?_
  · rw [dualStep_fst, dualRev_fst, partner_partner h2 hp]
  · rw [dualStep_snd, dualRev_snd, partner_partner h2 hp]

/-- The traversal step is injective on states. -/
lemma dualStep_inj {c : Set (Sym2 Site)} {p q : Sym2 Site × Site}
    (h2p : dualDeg c p.2 = 2) (h2q : dualDeg c q.2 = 2)
    (hp : DualState c p) (hq : DualState c q) (h : dualStep c p = dualStep c q) : p = q := by
  have hfg : partner c p.2 p.1 = partner c q.2 q.1 := congrArg Prod.fst h
  have hy : otherPlaq (partner c p.2 p.1) p.2 = otherPlaq (partner c q.2 q.1) q.2 :=
    congrArg Prod.snd h
  have hfp := mem_bondsAt.1 (partner_mem h2p hp)
  have hgq := mem_bondsAt.1 (partner_mem h2q hq)
  have hx : p.2 = q.2 :=
    calc p.2 = otherPlaq (partner c p.2 p.1) (otherPlaq (partner c p.2 p.1) p.2) :=
          (otherPlaq_otherPlaq hfp.1).symm
      _ = otherPlaq (partner c q.2 q.1) (otherPlaq (partner c q.2 q.1) q.2) := by
          rw [hy, hfg]
      _ = q.2 := otherPlaq_otherPlaq hgq.1
  have hfg' := hfg
  rw [hx] at hfg'
  have h1 : p.1 = q.1 :=
    calc p.1 = partner c p.2 (partner c p.2 p.1) := (partner_partner h2p hp).symm
      _ = partner c q.2 (partner c q.2 p.1) := by rw [hx]
      _ = partner c q.2 (partner c q.2 q.1) := by rw [hfg']
      _ = q.1 := partner_partner h2q hq
  exact Prod.ext h1 hx

end Irreducible


/-! ### The traversal of a circuit -/

/-- Georgii's traversal of a circuit, started at the state `p₀`. -/
def dualTrace (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) : ℕ → Sym2 Site × Site
  | 0 => p₀
  | n + 1 => dualStep c (dualTrace c p₀ n)

@[simp] lemma dualTrace_zero (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) :
    dualTrace c p₀ 0 = p₀ := rfl

@[simp] lemma dualTrace_succ (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) (n : ℕ) :
    dualTrace c p₀ (n + 1) = dualStep c (dualTrace c p₀ n) := rfl

variable {C : Finset (Sym2 Site)}

lemma dualDeg_of_state (hc : IsCircuit C) {p : Sym2 Site × Site}
    (hp : DualState (↑C : Set (Sym2 Site)) p) : dualDeg (↑C : Set (Sym2 Site)) p.2 = 2 :=
  hc.degree_two (mem_bondsAt.1 hp).1 (Finset.mem_coe.1 (mem_bondsAt.1 hp).2)

lemma dualState_trace (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) :
    ∀ n, DualState (↑C : Set (Sym2 Site)) (dualTrace (↑C : Set (Sym2 Site)) p₀ n)
  | 0 => hp₀
  | n + 1 =>
    dualState_dualStep (dualDeg_of_state hc (dualState_trace hc hp₀ n))
      (dualState_trace hc hp₀ n)

lemma dualTrace_fst_mem (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) (n : ℕ) :
    (dualTrace (↑C : Set (Sym2 Site)) p₀ n).1 ∈ C :=
  Finset.mem_coe.1 (mem_bondsAt.1 (dualState_trace hc hp₀ n)).2

/-- If the traversal reverses direction somewhere, it does so all along. -/
lemma dualRev_trace_aux (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) {i j : ℕ} (hij : i < j)
    (h : dualRev (dualTrace (↑C : Set (Sym2 Site)) p₀ i) = dualTrace (↑C : Set (Sym2 Site)) p₀ j) :
    ∀ k ≤ j - i, dualRev (dualTrace (↑C : Set (Sym2 Site)) p₀ (i + k))
      = dualTrace (↑C : Set (Sym2 Site)) p₀ (j - k) := by
  set c : Set (Sym2 Site) := (↑C : Set (Sym2 Site)) with hcdef
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    have hk' : k ≤ j - i := by omega
    have hjk : 1 ≤ j - k := by omega
    have hstep : dualStep c (dualRev (dualTrace c p₀ (i + k + 1))) = dualTrace c p₀ (j - k) := by
      rw [← ih hk']
      exact dualStep_dualRev_dualStep (dualDeg_of_state hc (dualState_trace hc hp₀ (i + k)))
        (dualState_trace hc hp₀ (i + k))
    have hjk' : j - k = (j - (k + 1)) + 1 := by omega
    rw [hjk', dualTrace_succ] at hstep
    have h1 : DualState c (dualRev (dualTrace c p₀ (i + k + 1))) :=
      dualState_dualRev (dualState_trace hc hp₀ (i + k + 1))
    have h2 : DualState c (dualTrace c p₀ (j - (k + 1))) := dualState_trace hc hp₀ (j - (k + 1))
    have := dualStep_inj (dualDeg_of_state hc h1) (dualDeg_of_state hc h2) h1 h2 hstep
    rw [show i + (k + 1) = i + k + 1 from by omega]
    exact this

/-- The traversal never repeats a bond except by repeating the whole state. -/
lemma dualTrace_fst_inj (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) {i j : ℕ} (hij : i < j)
    (h : (dualTrace (↑C : Set (Sym2 Site)) p₀ i).1
      = (dualTrace (↑C : Set (Sym2 Site)) p₀ j).1) :
    dualTrace (↑C : Set (Sym2 Site)) p₀ i = dualTrace (↑C : Set (Sym2 Site)) p₀ j := by
  set c : Set (Sym2 Site) := (↑C : Set (Sym2 Site)) with hcdef
  by_contra hne
  have hPi := dualState_trace hc hp₀ i
  have hPj := dualState_trace hc hp₀ j
  have hmem : (dualTrace c p₀ i).1 ∈ plaquette (dualTrace c p₀ j).2 := by
    rw [h]; exact (mem_bondsAt.1 hPj).1
  have hrev : dualRev (dualTrace c p₀ i) = dualTrace c p₀ j := by
    rcases eq_or_eq_otherPlaq (mem_bondsAt.1 hPi).1 hmem with h' | h'
    · exact absurd (Prod.ext h h'.symm) hne
    · exact Prod.ext h h'.symm
  have key := dualRev_trace_aux hc hp₀ hij hrev
  rcases Nat.even_or_odd (j - i) with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hle : k ≤ j - i := by omega
    have := key k hle
    rw [show j - k = i + k from by omega] at this
    exact dualRev_ne (dualState_trace hc hp₀ (i + k)) this
  · have hle : k ≤ j - i := by omega
    have := key k hle
    rw [show j - k = i + k + 1 from by omega] at this
    have hfst : (dualRev (dualTrace c p₀ (i + k))).1 = (dualTrace c p₀ (i + k + 1)).1 :=
      congrArg Prod.fst this
    exact dualStep_fst_ne (dualDeg_of_state hc (dualState_trace hc hp₀ (i + k)))
      (dualState_trace hc hp₀ (i + k)) hfst.symm

lemma dualTrace_shift (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) :
    ∀ (i d : ℕ), dualTrace (↑C : Set (Sym2 Site)) p₀ i
        = dualTrace (↑C : Set (Sym2 Site)) p₀ (i + d) →
      dualTrace (↑C : Set (Sym2 Site)) p₀ d = p₀ := by
  set c : Set (Sym2 Site) := (↑C : Set (Sym2 Site)) with hcdef
  intro i
  induction i with
  | zero => intro d h; simpa using h.symm
  | succ i ih =>
    intro d h
    refine ih d ?_
    have h' : dualStep c (dualTrace c p₀ i) = dualStep c (dualTrace c p₀ (i + d)) := by
      rw [← dualTrace_succ, ← dualTrace_succ, show i + d + 1 = i + 1 + d from by omega]
      exact h
    exact dualStep_inj (dualDeg_of_state hc (dualState_trace hc hp₀ i))
      (dualDeg_of_state hc (dualState_trace hc hp₀ (i + d))) (dualState_trace hc hp₀ i)
      (dualState_trace hc hp₀ (i + d)) h'

lemma dualTrace_periodic {c : Set (Sym2 Site)} {p₀ : Sym2 Site × Site} {m : ℕ}
    (hm : dualTrace c p₀ m = p₀) : ∀ k, dualTrace c p₀ (k + m) = dualTrace c p₀ k := by
  intro k
  induction k with
  | zero => simpa using hm
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 from by omega, dualTrace_succ, dualTrace_succ, ih]

/-- **The traversal closes up after at most `|c|` steps.** -/
lemma exists_dualTrace_period (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) :
    ∃ m, 0 < m ∧ m ≤ C.card ∧ dualTrace (↑C : Set (Sym2 Site)) p₀ m = p₀ := by
  set c : Set (Sym2 Site) := (↑C : Set (Sym2 Site)) with hcdef
  obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (C.card + 1)) (t := C)
      (by simp) (fun k _ ↦ dualTrace_fst_mem hc hp₀ k)
  rw [Finset.mem_range] at hi hj
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, by omega, ?_⟩
    have := dualTrace_fst_inj hc hp₀ hlt hfij
    exact dualTrace_shift hc hp₀ i (j - i) (by rwa [show i + (j - i) = j from by omega])
  · refine ⟨i - j, by omega, by omega, ?_⟩
    have := dualTrace_fst_inj hc hp₀ hlt hfij.symm
    exact dualTrace_shift hc hp₀ j (i - j) (by rwa [show j + (i - j) = i from by omega])


/-! ### The traversal covers the circuit -/

/-- **Closure**: a bond of `c` sharing a dual vertex with a bond visited by the traversal is
itself visited. -/
lemma trace_closure (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) {m : ℕ} (hm : 0 < m)
    (hper : dualTrace (↑C : Set (Sym2 Site)) p₀ m = p₀) {k : ℕ} {g : Sym2 Site} (hg : g ∈ C)
    (hadj : bondGraph.Adj (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 g) :
    ∃ k', (dualTrace (↑C : Set (Sym2 Site)) p₀ k').1 = g := by
  set c : Set (Sym2 Site) := (↑C : Set (Sym2 Site)) with hcdef
  obtain ⟨n, hn⟩ : ∃ n, dualTrace c p₀ (n + 1) = dualTrace c p₀ k :=
    ⟨k + m - 1, by
      rw [show k + m - 1 + 1 = k + m from by omega]
      exact dualTrace_periodic hper k⟩
  rw [← hn] at hadj
  obtain ⟨hne, y, hey, hgy⟩ := hadj
  have hstn : DualState c (dualTrace c p₀ n) := dualState_trace hc hp₀ n
  have h2n : dualDeg c (dualTrace c p₀ n).2 = 2 := dualDeg_of_state hc hstn
  have hfm : partner c (dualTrace c p₀ n).2 (dualTrace c p₀ n).1
      ∈ bondsAt c (dualTrace c p₀ n).2 := partner_mem h2n hstn
  have hfst : (dualTrace c p₀ (n + 1)).1
      = partner c (dualTrace c p₀ n).2 (dualTrace c p₀ n).1 := by
    simp only [dualTrace_succ, dualStep]
  have hsnd : (dualTrace c p₀ (n + 1)).2
      = otherPlaq (partner c (dualTrace c p₀ n).2 (dualTrace c p₀ n).1)
          (dualTrace c p₀ n).2 := by
    simp only [dualTrace_succ, dualStep]
  have hst1 : DualState c (dualTrace c p₀ (n + 1)) := dualState_trace hc hp₀ (n + 1)
  have h21 : dualDeg c (dualTrace c p₀ (n + 1)).2 = 2 := dualDeg_of_state hc hst1
  rcases eq_or_eq_otherPlaq (mem_bondsAt.1 hst1).1 hey with hy | hy
  · refine ⟨n + 2, ?_⟩
    have hgm : g ∈ bondsAt c (dualTrace c p₀ (n + 1)).2 :=
      mem_bondsAt.2 ⟨hy ▸ hgy, Finset.mem_coe.2 hg⟩
    have hgp := partner_unique h21 hst1 hgm (Ne.symm hne)
    have h2eq : (dualTrace c p₀ (n + 2)).1
        = partner c (dualTrace c p₀ (n + 1)).2 (dualTrace c p₀ (n + 1)).1 := by
      rw [show n + 2 = (n + 1) + 1 from by omega]
      simp only [dualTrace_succ, dualStep]
    rw [h2eq, ← hgp]
  · refine ⟨n, ?_⟩
    rw [hfst, hsnd, otherPlaq_otherPlaq (mem_bondsAt.1 hfm).1] at hy
    have hgm : g ∈ bondsAt c (dualTrace c p₀ n).2 :=
      mem_bondsAt.2 ⟨hy ▸ hgy, Finset.mem_coe.2 hg⟩
    have hgf : g ≠ partner c (dualTrace c p₀ n).2 (dualTrace c p₀ n).1 := by
      intro hcon
      exact hne (by rw [hfst, hcon])
    have hgp := partner_unique h2n hfm hgm hgf
    rw [partner_partner h2n hstn] at hgp
    exact hgp.symm

/-- **The traversal visits every bond of the circuit.** -/
lemma trace_covers (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) {m : ℕ} (hm : 0 < m)
    (hper : dualTrace (↑C : Set (Sym2 Site)) p₀ m = p₀) :
    ∀ g ∈ C, ∃ k, (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 = g := by
  intro g hg
  have he₀ : p₀.1 ∈ C := Finset.mem_coe.1 (mem_bondsAt.1 hp₀).2
  obtain ⟨w, hw⟩ := exists_walk_of_connected hc.connected he₀ hg
  suffices H : ∀ (a b : Sym2 Site) (w : bondGraph.Walk a b), (∀ z ∈ w.support, z ∈ C) →
      (∃ k, (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 = a) →
      ∃ k, (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 = b by
    exact H _ _ w hw ⟨0, rfl⟩
  intro a b w
  induction w with
  | nil => exact fun _ h ↦ h
  | @cons a v b hadj w ih =>
    rintro hsup ⟨k, hk⟩
    have hvC : v ∈ C := hsup v (by
      rw [SimpleGraph.Walk.support_cons]
      exact List.mem_cons_of_mem _ w.start_mem_support)
    have hadj' : bondGraph.Adj (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 v := by
      rw [hk]; exact hadj
    obtain ⟨k', hk'⟩ := trace_closure hc hp₀ hm hper hvC hadj'
    refine ih (fun z hz ↦ hsup z ?_) ⟨k', hk'⟩
    rw [SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem _ hz

lemma dualTrace_mod {c : Set (Sym2 Site)} {p₀ : Sym2 Site × Site} {m : ℕ} (hm : 0 < m)
    (hper : dualTrace c p₀ m = p₀) : ∀ k, dualTrace c p₀ k = dualTrace c p₀ (k % m) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < m
    · rw [Nat.mod_eq_of_lt hk]
    · have hkm : k - m < k := by omega
      have h1 : dualTrace c p₀ k = dualTrace c p₀ (k - m) := by
        have h := dualTrace_periodic (c := c) (p₀ := p₀) hper (k - m)
        rwa [show k - m + m = k from by omega] at h
      rw [h1, ih (k - m) hkm, ← Nat.mod_eq_sub_mod (by omega)]

/-- Every bond of the circuit is visited within the first `|c|` steps. -/
lemma trace_covers_lt (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) {m : ℕ} (hm : 0 < m) (hmle : m ≤ C.card)
    (hper : dualTrace (↑C : Set (Sym2 Site)) p₀ m = p₀) :
    ∀ g ∈ C, ∃ k < C.card, (dualTrace (↑C : Set (Sym2 Site)) p₀ k).1 = g := by
  intro g hg
  obtain ⟨k, hk⟩ := trace_covers hc hp₀ hm hper g hg
  refine ⟨k % m, lt_of_lt_of_le (Nat.mod_lt _ hm) hmle, ?_⟩
  rw [← dualTrace_mod hm hper k]
  exact hk


/-! ### Georgii Lemma (6.13): at most `3 ^ (ℓ - 1)` circuits of length `ℓ` through a bond -/

/-- The at most three continuations of the traversal from a state: the other three bonds of the
current plaquette (Georgii: "at each step there are at most three possible choices"). -/
def dualStepCands (p : Sym2 Site × Site) : Finset (Sym2 Site × Site) :=
  if p.1 ∈ plaquette p.2 then ((plaquette p.2).erase p.1).image fun f ↦ (f, otherPlaq f p.2)
  else ∅

lemma card_dualStepCands_le (p : Sym2 Site × Site) : (dualStepCands p).card ≤ 3 := by
  rw [dualStepCands]
  split_ifs with h
  · refine le_trans Finset.card_image_le ?_
    rw [Finset.card_erase_of_mem h, card_plaquette]
  · simp

/-- The candidate traversal records of length `n + 1`, most recent state first. -/
def dualWalkLists (p₀ : Sym2 Site × Site) : ℕ → Finset (List (Sym2 Site × Site))
  | 0 => {[p₀]}
  | n + 1 => (dualWalkLists p₀ n).biUnion fun l ↦
      (dualStepCands (l.headD p₀)).image fun q ↦ q :: l

lemma card_dualWalkLists_le (p₀ : Sym2 Site × Site) : ∀ n, (dualWalkLists p₀ n).card ≤ 3 ^ n
  | 0 => by simp [dualWalkLists]
  | n + 1 => by
    rw [dualWalkLists]
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ 3 fun l _ ↦
      le_trans Finset.card_image_le (card_dualStepCands_le _)) ?_
    rw [pow_succ]
    exact Nat.mul_le_mul (card_dualWalkLists_le p₀ n) le_rfl

/-- The record of the first `n + 1` states of the traversal, most recent state first. -/
def traceList (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) : ℕ → List (Sym2 Site × Site)
  | 0 => [p₀]
  | n + 1 => dualTrace c p₀ (n + 1) :: traceList c p₀ n

lemma traceList_headD (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) :
    ∀ n, (traceList c p₀ n).headD p₀ = dualTrace c p₀ n
  | 0 => rfl
  | _ + 1 => rfl

lemma traceList_mem_dualWalkLists (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) :
    ∀ n, traceList (↑C : Set (Sym2 Site)) p₀ n ∈ dualWalkLists p₀ n
  | 0 => by simp [traceList, dualWalkLists]
  | n + 1 => by
    rw [traceList, dualWalkLists]
    refine Finset.mem_biUnion.2 ⟨traceList (↑C : Set (Sym2 Site)) p₀ n,
      traceList_mem_dualWalkLists hc hp₀ n, ?_⟩
    rw [traceList_headD]
    refine Finset.mem_image.2 ⟨dualTrace (↑C : Set (Sym2 Site)) p₀ (n + 1), ?_, rfl⟩
    have hst := dualState_trace hc hp₀ n
    have h2 := dualDeg_of_state hc hst
    rw [dualStepCands, ite_eq_left (mem_bondsAt.1 hst).1]
    exact Finset.mem_image.2
      ⟨partner (↑C : Set (Sym2 Site)) (dualTrace (↑C : Set (Sym2 Site)) p₀ n).2
          (dualTrace (↑C : Set (Sym2 Site)) p₀ n).1,
        Finset.mem_erase.2 ⟨partner_ne h2 hst, (mem_bondsAt.1 (partner_mem h2 hst)).1⟩, rfl⟩

lemma mem_traceList_map (c : Set (Sym2 Site)) (p₀ : Sym2 Site × Site) (g : Sym2 Site) :
    ∀ n, g ∈ (traceList c p₀ n).map Prod.fst ↔ ∃ k ≤ n, (dualTrace c p₀ k).1 = g
  | 0 => by
    simp only [traceList, List.map_cons, List.map_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_rfl, h.symm⟩
    · rintro ⟨k, hk, rfl⟩; rw [Nat.le_zero.1 hk, dualTrace_zero]
  | n + 1 => by
    rw [traceList, List.map_cons, List.mem_cons, mem_traceList_map c p₀ g n]
    constructor
    · rintro (rfl | ⟨k, hk, hk'⟩)
      · exact ⟨n + 1, le_rfl, rfl⟩
      · exact ⟨k, by omega, hk'⟩
    · rintro ⟨k, hk, hk'⟩
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · exact Or.inr ⟨k, by omega, hk'⟩
      · exact Or.inl (by rw [show n + 1 = k from by omega]; exact hk'.symm)

/-- **The circuit is recovered from its traversal record.** -/
theorem circuit_eq_traceList_toFinset (hc : IsCircuit C) {p₀ : Sym2 Site × Site}
    (hp₀ : DualState (↑C : Set (Sym2 Site)) p₀) :
    ((traceList (↑C : Set (Sym2 Site)) p₀ (C.card - 1)).map Prod.fst).toFinset = C := by
  classical
  obtain ⟨m, hm, hmle, hper⟩ := exists_dualTrace_period hc hp₀
  ext g
  rw [List.mem_toFinset, mem_traceList_map]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact dualTrace_fst_mem hc hp₀ k
  · intro hg
    obtain ⟨k, hk, hk'⟩ := trace_covers_lt hc hp₀ hm hmle hper g hg
    exact ⟨k, by omega, hk'⟩

/-- Georgii's set of circuits of length `ℓ` through the bond `e₀`. -/
def circuitSets (e₀ : Sym2 Site) (ℓ : ℕ) : Set (Finset (Sym2 Site)) :=
  {c | IsCircuit c ∧ e₀ ∈ c ∧ c.card = ℓ}

theorem circuitSets_subset_image (e₀ : Sym2 Site) (x₀ : Site) (hx₀ : e₀ ∈ plaquette x₀)
    (ℓ : ℕ) :
    circuitSets e₀ ℓ ⊆ (fun L : List (Sym2 Site × Site) ↦ (L.map Prod.fst).toFinset) ''
      ↑(dualWalkLists (e₀, x₀) (ℓ - 1)) := by
  rintro C ⟨hc, he₀, hcard⟩
  have hp₀ : DualState (↑C : Set (Sym2 Site)) (e₀, x₀) :=
    mem_bondsAt.2 ⟨hx₀, Finset.mem_coe.2 he₀⟩
  refine ⟨traceList (↑C : Set (Sym2 Site)) (e₀, x₀) (ℓ - 1), ?_, ?_⟩
  · rw [Finset.mem_coe, ← hcard]
    exact traceList_mem_dualWalkLists hc hp₀ (C.card - 1)
  · rw [← hcard]
    exact circuit_eq_traceList_toFinset hc hp₀

/-- **Georgii Lemma (6.13), the sharp count**: at most `3 ^ (ℓ - 1)` circuits of length `ℓ`
contain a given bond. -/
theorem ncard_circuitSets_le (e₀ : Sym2 Site) (x₀ : Site) (hx₀ : e₀ ∈ plaquette x₀) (ℓ : ℕ) :
    (circuitSets e₀ ℓ).ncard ≤ 3 ^ (ℓ - 1) := by
  have himg : ((fun L : List (Sym2 Site × Site) ↦ (L.map Prod.fst).toFinset) ''
      ↑(dualWalkLists (e₀, x₀) (ℓ - 1))).ncard ≤ 3 ^ (ℓ - 1) := by
    refine le_trans (Set.ncard_image_le (Finset.finite_toSet _)) ?_
    rw [Set.ncard_coe_finset]
    exact card_dualWalkLists_le _ _
  exact le_trans (Set.ncard_le_ncard (circuitSets_subset_image e₀ x₀ hx₀ ℓ)
    ((Finset.finite_toSet _).image _)) himg

lemma finite_circuitSets (e₀ : Sym2 Site) (x₀ : Site) (hx₀ : e₀ ∈ plaquette x₀) (ℓ : ℕ) :
    (circuitSets e₀ ℓ).Finite :=
  Set.Finite.subset ((Finset.finite_toSet (dualWalkLists (e₀, x₀) (ℓ - 1))).image _)
    (circuitSets_subset_image e₀ x₀ hx₀ ℓ)


/-! ### The outer boundary of a connected set is a circuit -/

/-- **Georgii Lemma (6.14), the circuit property of the outer boundary.**  For a finite,
nonempty, connected set of sites `D ⊆ ℤ²`, the outer boundary of `D` is a circuit: it is
connected in the plaquette-adjacency graph and every dual vertex it meets meets exactly two of
its bonds.  Georgii's own statement of (6.14) — the existence of a contour *surrounding* `a` —
is `exists_circuit_contour`. -/
theorem isCircuit_outerBoundary {D : Set Site} (hD : D.Finite) (hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) :
    IsCircuit (outerBoundary_finite hD).toFinset := by
  have hcoe : (↑((outerBoundary_finite hD).toFinset) : Set (Sym2 Site)) = outerBoundary D :=
    Set.Finite.coe_toFinset _
  refine ⟨by rw [hcoe]; exact outerBoundary_connected hD hne hconn, ?_⟩
  intro x e hep hec
  rw [hcoe]
  exact outerBoundary_dualDeg_eq_two hD hne hconn
    ⟨e, hep, (Set.Finite.mem_toFinset _).1 hec⟩

/-! ### Georgii Lemma (6.13): `ℓ · 3^(ℓ-1)` circuits of length `ℓ` around a site -/

lemma add_nsmul_e0_eq (a : Site) (k : ℕ) : a + k • e0 = mk (a 0 + k) (a 1) := by
  rw [site_ext_iff]; simp

lemma hBond_mem_plaquette_mk (t u : ℤ) : hBond t u ∈ plaquette (mk t u) :=
  mem_plaquette_hBond.2 ⟨by simp, Or.inl (by simp)⟩

lemma anchor_bond_eq (a : Site) (k : ℕ) :
    s(a + k • e0, a + (k + 1) • e0) = hBond (a 0 + k) (a 1) := by
  have h2 : a + (k + 1) • e0 = mk (a 0 + k + 1) (a 1) := by
    rw [add_nsmul_e0_eq, mk_inj]
    exact ⟨by push_cast; ring, rfl⟩
  rw [add_nsmul_e0_eq, h2, hBond]

/-- **Georgii Lemma (6.13), in anchored form**: at most `ℓ · 3^(ℓ-1)` circuits of length `ℓ`
cross the horizontal half-line to the right of `a` at one of its first `ℓ` bonds.  Georgii
derives his count for the circuits *surrounding* `a` from this, using that such a circuit must
cross that half-line; here the contour comes out of `exists_circuit_contour` already anchored
(`exists_anchor_bond`), so the anchored form is the one the Peierls sum needs.  Compare the
`4096 ^ ℓ` bound of `GibbsMeasure/Model/PeierlsEstimate.lean`. -/
theorem ncard_anchored_circuits_le (a : Site) (ℓ : ℕ) :
    {C : Finset (Sym2 Site) | IsCircuit C ∧ C.card = ℓ ∧
        ∃ k < ℓ, s(a + k • e0, a + (k + 1) • e0) ∈ C}.ncard ≤ ℓ * 3 ^ (ℓ - 1) := by
  classical
  set T : Finset (Finset (Sym2 Site)) := (Finset.range ℓ).biUnion (fun k ↦
    (finite_circuitSets (hBond (a 0 + k) (a 1)) (mk (a 0 + k) (a 1))
      (hBond_mem_plaquette_mk _ _) ℓ).toFinset) with hT
  have hsub : {C : Finset (Sym2 Site) | IsCircuit C ∧ C.card = ℓ ∧
      ∃ k < ℓ, s(a + k • e0, a + (k + 1) • e0) ∈ C} ⊆ (↑T : Set (Finset (Sym2 Site))) := by
    rintro C ⟨hc, hcard, k, hk, hmem⟩
    rw [Finset.mem_coe, hT]
    refine Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨hc, by rwa [anchor_bond_eq] at hmem, hcard⟩
  have hcardT : T.card ≤ ℓ * 3 ^ (ℓ - 1) := by
    rw [hT]
    refine le_trans (Finset.card_biUnion_le_card_mul _ _ (3 ^ (ℓ - 1)) fun k _ ↦ ?_) ?_
    · have hcast : ((finite_circuitSets (hBond (a 0 + k) (a 1)) (mk (a 0 + k) (a 1))
            (hBond_mem_plaquette_mk _ _) ℓ).toFinset).card
          = (circuitSets (hBond (a 0 + k) (a 1)) ℓ).ncard := by
        rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
      rw [hcast]
      exact ncard_circuitSets_le _ _ (hBond_mem_plaquette_mk _ _) ℓ
    · rw [Finset.card_range]
  calc {C : Finset (Sym2 Site) | IsCircuit C ∧ C.card = ℓ ∧
        ∃ k < ℓ, s(a + k • e0, a + (k + 1) • e0) ∈ C}.ncard
      ≤ (↑T : Set (Finset (Sym2 Site))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ ℓ * 3 ^ (ℓ - 1) := hcardT


/-! ### M3: the sharpened Peierls series and the improved threshold -/

/-- The geometric-derivative sum `∑_{l ≥ 0} (l+1) z^l = (1-z)^{-2}` in `ℝ≥0∞`. -/
lemma tsum_succ_mul_pow (z : ℝ≥0∞) :
    ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * z ^ l = (1 - z)⁻¹ * (1 - z)⁻¹ := by
  classical
  have hfiber : ∀ l : ℕ, ((fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {l})
      = (↑(Finset.antidiagonal l) : Set (ℕ × ℕ)) := by
    intro l; ext p; simp [Finset.mem_antidiagonal]
  have hinner : ∀ l : ℕ,
      ∑' p : ((fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {l}), z ^ ((p : ℕ × ℕ).1 + (p : ℕ × ℕ).2)
        = ((l : ℝ≥0∞) + 1) * z ^ l := by
    intro l
    rw [hfiber l, Finset.tsum_subtype' (Finset.antidiagonal l)
      (fun p : ℕ × ℕ ↦ z ^ (p.1 + p.2))]
    have hc : ∑ p ∈ Finset.antidiagonal l, z ^ (p.1 + p.2)
        = ∑ _p ∈ Finset.antidiagonal l, z ^ l := by
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [hp]
    rw [hc, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
    push_cast
    ring
  have hprod : ∑' p : ℕ × ℕ, z ^ (p.1 + p.2) = (1 - z)⁻¹ * (1 - z)⁻¹ := by
    rw [ENNReal.tsum_prod']
    calc ∑' (a : ℕ) (b : ℕ), z ^ (a + b) = ∑' a : ℕ, z ^ a * ∑' b : ℕ, z ^ b := by
          refine tsum_congr fun a ↦ ?_
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun b ↦ pow_add z a b
      _ = (∑' a : ℕ, z ^ a) * (∑' b : ℕ, z ^ b) := ENNReal.tsum_mul_right
      _ = (1 - z)⁻¹ * (1 - z)⁻¹ := by rw [ENNReal.tsum_geometric]
  calc ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * z ^ l
      = ∑' (l : ℕ) (p : ((fun p : ℕ × ℕ ↦ p.1 + p.2) ⁻¹' {l})),
          z ^ ((p : ℕ × ℕ).1 + (p : ℕ × ℕ).2) := (tsum_congr hinner).symm
    _ = ∑' p : ℕ × ℕ, z ^ (p.1 + p.2) :=
        ENNReal.tsum_fiberwise (fun p : ℕ × ℕ ↦ z ^ (p.1 + p.2)) (fun p ↦ p.1 + p.2)
    _ = (1 - z)⁻¹ * (1 - z)⁻¹ := hprod

/-- **Georgii's Peierls series with his own contour count** (6.13):
`r'(β) = ∑_{ℓ ≥ 1} ℓ · 3^(ℓ-1) · e^{-2βℓ}`.  The series `Peierls.r` of
`GibbsMeasure/Model/PhaseTransition.lean` uses `4096 ^ ℓ` in place of `3 ^ (ℓ - 1)`. -/
def r' (b : ℝ) : ℝ≥0∞ :=
  ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * 3 ^ l * ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1)))

/-- **Georgii's series in closed form**: `r'(β) = e^{-2β} (1 - 3 e^{-2β})^{-2}`. -/
theorem r'_eq (b : ℝ) :
    r' b = ENNReal.ofReal (Real.exp (-2 * b))
      * ((1 - 3 * ENNReal.ofReal (Real.exp (-2 * b)))⁻¹
        * (1 - 3 * ENNReal.ofReal (Real.exp (-2 * b)))⁻¹) := by
  set y := ENNReal.ofReal (Real.exp (-2 * b)) with hy
  have hterm : ∀ l : ℕ,
      ((l : ℝ≥0∞) + 1) * 3 ^ l * ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1)))
        = y * (((l : ℝ≥0∞) + 1) * (3 * y) ^ l) := by
    intro l
    have hexpl : ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) = y ^ (l + 1) := by
      rw [hy, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexpl, mul_pow, pow_succ]
    ring
  rw [r', tsum_congr hterm, ENNReal.tsum_mul_left, tsum_succ_mul_pow]

/-- **The sharpened Peierls bound.**  With Georgii's own contour count `ℓ · 3^(ℓ-1)`, the
Peierls series is at most `1/4` as soon as `β ≥ log 3 ≈ 1.0986`.  The threshold of
`Peierls.r_le_quarter` in `GibbsMeasure/Model/PhaseTransition.lean`, forced by the crude count
`4096 ^ ℓ`, is `8 log 2 ≈ 5.5452`. -/
theorem r'_le_quarter {b : ℝ} (hb : Real.log 9 ≤ 2 * b) : r' b ≤ 4⁻¹ := by
  set y := ENNReal.ofReal (Real.exp (-2 * b)) with hy
  have hexp : Real.exp (-2 * b) ≤ 1 / 9 := by
    have h1 : Real.exp (-2 * b) ≤ Real.exp (-Real.log 9) := Real.exp_le_exp.2 (by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 9), ← one_div] at h1
  have hy9 : y ≤ ENNReal.ofReal (1 / 9) := ENNReal.ofReal_le_ofReal hexp
  have h3y : 3 * y ≤ ENNReal.ofReal (1 / 3) := by
    calc 3 * y ≤ 3 * ENNReal.ofReal (1 / 9) := by gcongr
      _ = ENNReal.ofReal (1 / 3) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          norm_num
  have hsubl : ENNReal.ofReal (2 / 3) ≤ 1 - 3 * y := by
    refine le_trans (le_of_eq ?_) (tsub_le_tsub_left h3y 1)
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub _ (by norm_num : (0:ℝ) ≤ 1 / 3)]
    norm_num
  have hinv : (1 - 3 * y)⁻¹ ≤ ENNReal.ofReal (3 / 2) := by
    refine le_trans (ENNReal.inv_le_inv.2 hsubl) (le_of_eq ?_)
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2 / 3)]
    norm_num
  rw [r'_eq]
  calc y * ((1 - 3 * y)⁻¹ * (1 - 3 * y)⁻¹)
      ≤ ENNReal.ofReal (1 / 9) * (ENNReal.ofReal (3 / 2) * ENNReal.ofReal (3 / 2)) :=
        mul_le_mul' hy9 (mul_le_mul' hinv hinv)
    _ = 4⁻¹ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3 / 2),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 9),
          show (1 / 9 : ℝ) * (3 / 2 * (3 / 2)) = (4 : ℝ)⁻¹ from by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num

/-- The analogue, for the sharpened series `r'`, of Georgii's requirement `r(β) < 1/2` in the
proof of (6.9): `r' β < 1/2` as soon as `β ≥ (1/2) log (20/3) ≈ 0.9486`.  (Georgii's own
`r(β) = 1 ∧ ∑_{ℓ ≥ 1} ℓ (3 e^{-2β})^ℓ` equals `1 ∧ 3 r'(β)`, hence is still `1` at that `β`;
the exact analytic threshold for `r'` itself is `(1/2) log (9/(4-√7)) ≈ 0.9470`.) -/
theorem r'_lt_half {b : ℝ} (hb : Real.log (20 / 3) ≤ 2 * b) : r' b < 2⁻¹ := by
  set y := ENNReal.ofReal (Real.exp (-2 * b)) with hy
  have hexp : Real.exp (-2 * b) ≤ 3 / 20 := by
    have h1 : Real.exp (-2 * b) ≤ Real.exp (-Real.log (20 / 3)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 20 / 3)] at h1
    rw [show (3 : ℝ) / 20 = ((20 : ℝ) / 3)⁻¹ from by norm_num]
    exact h1
  have hy20 : y ≤ ENNReal.ofReal (3 / 20) := ENNReal.ofReal_le_ofReal hexp
  have h3y : 3 * y ≤ ENNReal.ofReal (9 / 20) := by
    calc 3 * y ≤ 3 * ENNReal.ofReal (3 / 20) := by gcongr
      _ = ENNReal.ofReal (9 / 20) := by
          rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
          norm_num
  have hsubl : ENNReal.ofReal (11 / 20) ≤ 1 - 3 * y := by
    refine le_trans (le_of_eq ?_) (tsub_le_tsub_left h3y 1)
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub _ (by norm_num : (0:ℝ) ≤ 9 / 20)]
    norm_num
  have hinv : (1 - 3 * y)⁻¹ ≤ ENNReal.ofReal (20 / 11) := by
    refine le_trans (ENNReal.inv_le_inv.2 hsubl) (le_of_eq ?_)
    rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 11 / 20)]
    norm_num
  rw [r'_eq]
  refine lt_of_le_of_lt (mul_le_mul' hy20 (mul_le_mul' hinv hinv)) ?_
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 20 / 11),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3 / 20),
    show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) from by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]
      norm_num]
  rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- The sharpened threshold really is much smaller than the landed one:
`log 3 < 8 log 2`, i.e. `1.0986… < 5.5452…`. -/
theorem sharpened_threshold_lt : Real.log 9 / 2 < 8 * Real.log 2 := by
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 3 < 2 * Real.log 2 := by
    rw [← h4]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [h9]
  linarith


/-! ### The Peierls input, sharpened: contours of a configuration are circuits -/

/-- **Georgii (6.14) and (6.13), packaged.**  If `ζ` is `+1` outside the box `Λ_N` and `-1` at
`a`, then `a` is surrounded by a *circuit* of discordant bonds, anchored at one of the first
`|c|` bonds of the horizontal half-line from `a`.  Together with `ncard_anchored_circuits_le`
this replaces the crude count `4096 ^ ℓ` by Georgii's `ℓ · 3^(ℓ-1)` in the Peierls sum. -/
theorem exists_circuit_contour (N : ℕ) (a : Site) {ζ : Site → Bool}
    (ha : ζ a = false) (hout : ∀ i ∉ cube 2 N, ζ i = true) :
    ∃ C : Finset (Sym2 Site), IsCircuit C ∧ 0 < C.card ∧
      (↑C : Set (Sym2 Site)) ⊆ discordant ζ ∧
      ∃ k < C.card, s(a + k • e0, a + (k + 1) • e0) ∈ C := by
  set D : Set Site := minusCluster a ζ with hDdef
  have haD : a ∈ D := mem_minusCluster_self ha
  have hDsub : D ⊆ ((cube 2 N : Finset Site) : Set Site) :=
    minusCluster_subset_of_forall_eq_true (fun i hi ↦ hout i (by simpa using hi))
  have hDbox : D ⊆ box N := by rw [← coe_cube_eq_box N]; exact hDsub
  have hDfin : D.Finite := (box_finite N).subset hDbox
  have hOBfin : (outerBoundary D).Finite := outerBoundary_finite hDfin
  have hcard : hOBfin.toFinset.card = (outerBoundary D).ncard := by
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  refine ⟨hOBfin.toFinset, isCircuit_outerBoundary hDfin ⟨a, haD⟩ (minusCluster_connected ha),
    ?_, ?_, ?_⟩
  · rw [Finset.card_pos, Set.Finite.toFinset_nonempty]
    exact outerBoundary_nonempty hDfin ⟨a, haD⟩
  · rw [Set.Finite.coe_toFinset]
    exact outerBoundary_minusCluster_subset_discordant a ζ
  · obtain ⟨k, hk, hbond⟩ := exists_anchor_bond hDfin haD
    exact ⟨k, by rw [hcard]; exact hk, (Set.Finite.mem_toFinset _).2 hbond⟩

end MeasureTheory.GibbsMeasure.PeierlsSharp

end

end

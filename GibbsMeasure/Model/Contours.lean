/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ZMod.Basic

/-!
# The Peierls argument for the two-dimensional Ising model: boundary connectivity

Georgii, Section 6.2, Lemma (6.14) in its topology-free, combinatorial form. For a finite
connected set of sites `D ⊆ ℤ²`, the complement `Dᶜ` has exactly one infinite connected
component (`outside D`), and the *outer boundary* of `D` — the bonds joining `D` to `outside D` —
is connected in the plaquette-adjacency graph on bonds (Georgii's dual bonds sharing a dual site).
This replaces Georgii's appeal to the Jordan curve theorem by Timár's boundary-connectivity
argument (Proc. AMS 141 (2013)): a `ZMod 2`-valued potential built from L-shaped lattice paths.
Also: the "last exit" bond of a walk leaving `D`, and the anchor bond on the horizontal half-line
used in the counting Lemma (6.13).
-/

@[expose] public section


open MeasureTheory MeasureTheory.GibbsMeasure Set

noncomputable section

namespace MeasureTheory.GibbsMeasure.Peierls

/-- The sites of the square lattice `ℤ²`. -/
abbrev Site := Fin 2 → ℤ

/-- The first unit vector of `ℤ²`. -/
def e0 : Site := Pi.single 0 1

/-- The second unit vector of `ℤ²`. -/
def e1 : Site := Pi.single 1 1

/-- The four bonds of the unit square (plaquette) with lower-left corner `x`. -/
def plaquette (x : Site) : Finset (Sym2 Site) :=
  {s(x, x + e0), s(x, x + e1), s(x + e0, x + e0 + e1), s(x + e1, x + e0 + e1)}

/-- Two bonds are plaquette-adjacent if they are distinct and lie in a common plaquette
(Georgii: their dual bonds share a dual site). -/
def bondAdj (e f : Sym2 Site) : Prop := e ≠ f ∧ ∃ x, e ∈ plaquette x ∧ f ∈ plaquette x

/-- The plaquette-adjacency graph on bonds (Georgii's dual lattice, seen from the bonds). -/
def bondGraph : SimpleGraph (Sym2 Site) where
  Adj := bondAdj
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.imp fun _ hx ↦ hx.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The `Λ`-independent version of Georgii's `B*(ζ)`: every lattice bond whose endpoints carry
different spins, so that `B*(ζ) = bondsMeeting Λ ∩ discordant ζ`. -/
def discordant (ζ : Site → Bool) : Set (Sym2 Site) :=
  {e ∈ (latticeGraph 2).edgeSet | ∃ i j, e = s(i, j) ∧ ζ i ≠ ζ j}

/-- The edge boundary of a set of sites: the lattice bonds with exactly one endpoint in `D`. -/
def edgeBoundary (D : Set Site) : Set (Sym2 Site) :=
  {e | ∃ i ∈ D, ∃ j ∉ D, (latticeGraph 2).Adj i j ∧ e = s(i, j)}

open Classical in
/-- Georgii's `τ_c`: flip the spins on `D`. -/
def flip (D : Set Site) (ζ : Site → Bool) : Site → Bool := fun i ↦ if i ∈ D then !ζ i else ζ i

/-! ### Reachability inside a set of vertices -/

/-- `ReachIn G s u v`: `u, v ∈ s` are joined by a walk of the induced graph `G.induce s`. -/
def ReachIn {V : Type*} (G : SimpleGraph V) (s : Set V) (u v : V) : Prop :=
  ∃ (hu : u ∈ s) (hv : v ∈ s), (G.induce s).Reachable ⟨u, hu⟩ ⟨v, hv⟩

section ReachIn
variable {V : Type*} {G : SimpleGraph V} {s t : Set V} {u v w : V}

lemma ReachIn.mem_left (h : ReachIn G s u v) : u ∈ s := h.1

lemma ReachIn.mem_right (h : ReachIn G s u v) : v ∈ s := h.2.1

lemma ReachIn.refl (hu : u ∈ s) : ReachIn G s u u := ⟨hu, hu, SimpleGraph.Reachable.refl _⟩

lemma ReachIn.symm (h : ReachIn G s u v) : ReachIn G s v u := by
  obtain ⟨hu, hv, h⟩ := h
  exact ⟨hv, hu, h.symm⟩

lemma ReachIn.trans (h₁ : ReachIn G s u v) (h₂ : ReachIn G s v w) : ReachIn G s u w := by
  obtain ⟨hu, hv, h₁'⟩ := h₁
  obtain ⟨hv', hw, h₂'⟩ := h₂
  exact ⟨hu, hw, h₁'.trans h₂'⟩

lemma ReachIn.of_adj (hu : u ∈ s) (hv : v ∈ s) (h : G.Adj u v) : ReachIn G s u v :=
  ⟨hu, hv, SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.2 h)⟩

/-- Induction along a walk inside `s`. -/
lemma ReachIn.induction {P : V → Prop} (hu : P u)
    (hstep : ∀ a b, a ∈ s → b ∈ s → G.Adj a b → P a → P b) (h : ReachIn G s u v) : P v := by
  obtain ⟨hu', hv, ⟨p⟩⟩ := h
  suffices H : ∀ (x y : s) (_ : (G.induce s).Walk x y), P x.1 → P y.1 from H _ _ p hu
  intro x y p
  induction p with
  | nil => exact id
  | cons hadj _ ih => exact fun hx ↦ ih (hstep _ _ (by simp) (by simp) hadj hx)

lemma ReachIn.mono (hst : s ⊆ t) (h : ReachIn G s u v) : ReachIn G t u v :=
  h.induction (ReachIn.refl (hst h.mem_left))
    fun _ _ ha hb hab hab' ↦ hab'.trans (ReachIn.of_adj (hst ha) (hst hb) hab)

/-- A function constant along edges inside `s` is constant along walks inside `s`. -/
lemma ReachIn.invariant {α : Type*} (f : V → α)
    (hf : ∀ a b : V, a ∈ s → b ∈ s → G.Adj a b → f a = f b) (h : ReachIn G s u v) :
    f u = f v :=
  ReachIn.induction (P := fun x ↦ f u = f x) rfl
    (fun a b ha hb hab hfa ↦ hfa.trans (hf a b ha hb hab)) h

/-- A chain of adjacent vertices inside `s` yields reachability inside `s`. -/
lemma reachIn_chain (p : ℕ → V) (hadj : ∀ k, G.Adj (p k) (p (k + 1))) :
    ∀ n : ℕ, (∀ k ≤ n, p k ∈ s) → ReachIn G s (p 0) (p n)
  | 0, hp => ReachIn.refl (hp 0 le_rfl)
  | n + 1, hp =>
    (reachIn_chain p hadj n fun k hk ↦ hp k (by omega)).trans
      (ReachIn.of_adj (hp n (by omega)) (hp (n + 1) le_rfl) (hadj n))

end ReachIn

/-! ### Coordinates on `ℤ²` and nearest-neighbour adjacency -/

/-- The site with coordinates `(a, b)`. -/
def mk (a b : ℤ) : Site := ![a, b]

@[simp] lemma mk_zero (a b : ℤ) : mk a b 0 = a := by simp [mk]

@[simp] lemma mk_one (a b : ℤ) : mk a b 1 = b := by simp [mk]

@[simp] lemma e0_zero : e0 0 = 1 := by simp [e0]

@[simp] lemma e0_one : e0 1 = 0 := by simp [e0]

@[simp] lemma e1_zero : e1 0 = 0 := by simp [e1]

@[simp] lemma e1_one : e1 1 = 1 := by simp [e1]

lemma site_ext_iff (x y : Site) : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  rw [funext_iff, Fin.forall_fin_two]

@[simp] lemma mk_eta (x : Site) : mk (x 0) (x 1) = x := by
  rw [site_ext_iff]; simp

lemma mk_add_e0 (a b : ℤ) : mk a b + e0 = mk (a + 1) b := by
  rw [site_ext_iff]; simp

lemma mk_add_e1 (a b : ℤ) : mk a b + e1 = mk a (b + 1) := by
  rw [site_ext_iff]; simp

@[simp] lemma nsmul_e0_zero (k : ℕ) : (k • e0) 0 = k := by simp

@[simp] lemma nsmul_e0_one (k : ℕ) : (k • e0) 1 = 0 := by simp

@[simp] lemma nsmul_e1_zero (k : ℕ) : (k • e1) 0 = 0 := by simp

@[simp] lemma nsmul_e1_one (k : ℕ) : (k • e1) 1 = k := by simp

/-- Adjacency in `ℤ²` in terms of coordinates. -/
lemma latticeGraph_two_adj_iff (x y : Site) :
    (latticeGraph 2).Adj x y ↔ (x 0 - y 0).natAbs + (x 1 - y 1).natAbs = 1 := by
  show (∑ i, (x i - y i).natAbs = 1) ↔ _
  rw [Fin.sum_univ_two]

/-- A neighbour of `x` in `ℤ²` is `x ± e0` or `x ± e1`. -/
lemma latticeGraph_two_adj_iff' (x y : Site) :
    (latticeGraph 2).Adj x y ↔ y = x + e0 ∨ x = y + e0 ∨ y = x + e1 ∨ x = y + e1 := by
  rw [latticeGraph_two_adj_iff]
  constructor
  · intro h
    simp only [site_ext_iff, Pi.add_apply, e0_zero, e0_one, e1_zero, e1_one]
    omega
  · rintro (rfl | rfl | rfl | rfl) <;>
      simp only [Pi.add_apply, e0_zero, e0_one, e1_zero, e1_one] <;> omega

lemma adj_add_e0 (x : Site) : (latticeGraph 2).Adj x (x + e0) :=
  (latticeGraph_two_adj_iff' _ _).2 (Or.inl rfl)

lemma adj_add_e1 (x : Site) : (latticeGraph 2).Adj x (x + e1) :=
  (latticeGraph_two_adj_iff' _ _).2 (Or.inr (Or.inr (Or.inl rfl)))

lemma adj_nsmul_e0 (a : Site) (k : ℕ) : (latticeGraph 2).Adj (a + k • e0) (a + (k + 1) • e0) := by
  rw [succ_nsmul, ← add_assoc]; exact adj_add_e0 _

lemma adj_nsmul_e1 (a : Site) (k : ℕ) : (latticeGraph 2).Adj (a + k • e1) (a + (k + 1) • e1) := by
  rw [succ_nsmul, ← add_assoc]; exact adj_add_e1 _

/-- Horizontal segments: reachability along a row inside `s`. -/
lemma reachIn_horizontal (s : Set Site) (a b y : ℤ)
    (h : ∀ t, min a b ≤ t → t ≤ max a b → mk t y ∈ s) :
    ReachIn (latticeGraph 2) s (mk a y) (mk b y) := by
  have key : ∀ (a : ℤ) (n : ℕ), (∀ k : ℕ, k ≤ n → mk (a + k) y ∈ s) →
      ReachIn (latticeGraph 2) s (mk a y) (mk (a + n) y) := by
    intro a n hn
    have := reachIn_chain (G := latticeGraph 2) (s := s) (fun k : ℕ ↦ mk (a + k) y)
      (fun k ↦ by
        have : mk (a + ((k + 1 : ℕ) : ℤ)) y = mk (a + k) y + e0 := by
          rw [mk_add_e0]; congr 1; push_cast; ring
        rw [this]; exact adj_add_e0 _) n hn
    simpa using this
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    exact key a n fun k hk ↦ h _ (by omega) (by omega)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = b + n := ⟨(a - b).toNat, by omega⟩
    exact (key b n fun k hk ↦ h _ (by omega) (by omega)).symm

/-- Vertical segments: reachability along a column inside `s`. -/
lemma reachIn_vertical (s : Set Site) (x a b : ℤ)
    (h : ∀ t, min a b ≤ t → t ≤ max a b → mk x t ∈ s) :
    ReachIn (latticeGraph 2) s (mk x a) (mk x b) := by
  have key : ∀ (a : ℤ) (n : ℕ), (∀ k : ℕ, k ≤ n → mk x (a + k) ∈ s) →
      ReachIn (latticeGraph 2) s (mk x a) (mk x (a + n)) := by
    intro a n hn
    have := reachIn_chain (G := latticeGraph 2) (s := s) (fun k : ℕ ↦ mk x (a + k))
      (fun k ↦ by
        have : mk x (a + ((k + 1 : ℕ) : ℤ)) = mk x (a + k) + e1 := by
          rw [mk_add_e1]; congr 1; push_cast; ring
        rw [this]; exact adj_add_e1 _) n hn
    simpa using this
  rcases le_total a b with hab | hab
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    exact key a n fun k hk ↦ h _ (by omega) (by omega)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = b + n := ⟨(a - b).toNat, by omega⟩
    exact (key b n fun k hk ↦ h _ (by omega) (by omega)).symm

/-! ### Boxes and far points -/

/-- The box `[-N, N]²`. -/
def box (N : ℕ) : Set Site := {x | ∀ i, |x i| ≤ N}

lemma notMem_box_iff {N : ℕ} {x : Site} : x ∉ box N ↔ (N : ℤ) < |x 0| ∨ (N : ℤ) < |x 1| := by
  simp only [box, Set.mem_ofPred_eq, Fin.forall_fin_two, not_and_or, not_le]

lemma box_finite (N : ℕ) : (box N).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin 2 ↦ Set.Icc (-(N : ℤ)) N)
    fun _ ↦ Set.finite_Icc _ _).subset ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  exact fun i ↦ abs_le.1 (hx i)

lemma exists_subset_box {D : Set Site} (hD : D.Finite) : ∃ N : ℕ, D ⊆ box N := by
  obtain ⟨M, hM⟩ := (hD.image fun x ↦ max |x 0| |x 1|).bddAbove
  refine ⟨M.toNat, fun x hx ↦ ?_⟩
  have h := hM (Set.mem_image_of_mem _ hx)
  have h' := Int.self_le_toNat M
  simp only [box, Set.mem_ofPred_eq, Fin.forall_fin_two]
  exact ⟨(le_max_left _ _).trans (h.trans h'), (le_max_right _ _).trans (h.trans h')⟩

lemma lt_of_notMem_box {N : ℕ} {x : Site} (hx : x ∉ box N) : (N : ℤ) < max |x 0| |x 1| := by
  rw [notMem_box_iff] at hx
  rcases hx with h | h
  · exact h.trans_le (le_max_left _ _)
  · exact h.trans_le (le_max_right _ _)

lemma corner_notMem_box {N : ℕ} {K : ℤ} (hK : (N : ℤ) < K) : mk K K ∉ box N := by
  rw [notMem_box_iff]
  exact Or.inl (by simpa using hK.trans_le (le_abs_self K))

lemma reachIn_corner_succ {N : ℕ} {K : ℤ} (hK : (N : ℤ) < K) :
    ReachIn (latticeGraph 2) (box N)ᶜ (mk K K) (mk (K + 1) (K + 1)) := by
  have h1 : mk K K ∉ box N := corner_notMem_box hK
  have h2 : mk (K + 1) K ∉ box N := by
    rw [notMem_box_iff]
    exact Or.inr (by simpa using hK.trans_le (le_abs_self K))
  have h3 : mk (K + 1) (K + 1) ∉ box N := corner_notMem_box (by omega)
  exact (ReachIn.of_adj h1 h2 (by rw [← mk_add_e0]; exact adj_add_e0 _)).trans
    (ReachIn.of_adj h2 h3 (by rw [← mk_add_e1]; exact adj_add_e1 _))

lemma reachIn_corner {N : ℕ} {K : ℤ} (hK : (N : ℤ) < K) (n : ℕ) :
    ReachIn (latticeGraph 2) (box N)ᶜ (mk K K) (mk (K + n) (K + n)) := by
  induction n with
  | zero => simpa using ReachIn.refl (s := (box N)ᶜ) (corner_notMem_box hK)
  | succ n ih =>
    have := reachIn_corner_succ (N := N) (K := K + n) (by omega)
    rw [show K + ((n + 1 : ℕ) : ℤ) = K + n + 1 by push_cast; ring]
    exact ih.trans this

/-- Every point outside the box reaches the diagonal corner of its `ℓ∞`-sphere, outside the box. -/
lemma reachIn_corner_of_notMem_box {N : ℕ} {x : Site} (hx : x ∉ box N) :
    ReachIn (latticeGraph 2) (box N)ᶜ x (mk (max |x 0| |x 1|) (max |x 0| |x 1|)) := by
  have hNK := lt_of_notMem_box hx
  have hcorner : ∀ t, mk (max |x 0| |x 1|) t ∉ box N := fun t ↦ by
    rw [notMem_box_iff]
    exact Or.inl (by simpa using hNK.trans_le (le_abs_self _))
  have hcorner' : ∀ t, mk t (max |x 0| |x 1|) ∉ box N := fun t ↦ by
    rw [notMem_box_iff]
    exact Or.inr (by simpa using hNK.trans_le (le_abs_self _))
  rcases max_choice |x 0| |x 1| with h | h
  · -- `|x 0|` is the largest coordinate: go vertically to `(x 0, K)`, then horizontally.
    have hcol : ∀ t, mk (x 0) t ∉ box N := fun t ↦ by
      rw [notMem_box_iff]; exact Or.inl (by simpa using h ▸ hNK)
    have step1 : ReachIn (latticeGraph 2) (box N)ᶜ (mk (x 0) (x 1)) (mk (x 0) (max |x 0| |x 1|)) :=
      reachIn_vertical _ _ _ _ fun t _ _ ↦ hcol t
    have step2 := reachIn_horizontal (box N)ᶜ (x 0)
      (max |x 0| |x 1|) (max |x 0| |x 1|) fun t _ _ ↦ hcorner' t
    rw [mk_eta] at step1
    exact step1.trans step2
  · -- `|x 1|` is the largest coordinate: go horizontally to `(K, x 1)`, then vertically.
    have hrow : ∀ t, mk t (x 1) ∉ box N := fun t ↦ by
      rw [notMem_box_iff]; exact Or.inr (by simpa using h ▸ hNK)
    have step1 : ReachIn (latticeGraph 2) (box N)ᶜ (mk (x 0) (x 1)) (mk (max |x 0| |x 1|) (x 1)) :=
      reachIn_horizontal _ _ _ _ fun t _ _ ↦ hrow t
    have step2 := reachIn_vertical (box N)ᶜ (max |x 0| |x 1|) (x 1) (max |x 0| |x 1|)
      fun t _ _ ↦ hcorner t
    rw [mk_eta] at step1
    exact step1.trans step2

/-- Any two points outside the box are connected outside the box. -/
lemma reachIn_compl_box {N : ℕ} {x y : Site} (hx : x ∉ box N) (hy : y ∉ box N) :
    ReachIn (latticeGraph 2) (box N)ᶜ x y := by
  have hx' := reachIn_corner_of_notMem_box hx
  have hy' := reachIn_corner_of_notMem_box hy
  have hNx := lt_of_notMem_box hx
  have hNy := lt_of_notMem_box hy
  rcases le_total (max |x 0| |x 1|) (max |y 0| |y 1|) with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, max |y 0| |y 1| = max |x 0| |x 1| + n :=
      ⟨(max |y 0| |y 1| - max |x 0| |x 1|).toNat, by omega⟩
    have := reachIn_corner hNx n
    rw [← hn] at this
    exact hx'.trans (this.trans hy'.symm)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, max |x 0| |x 1| = max |y 0| |y 1| + n :=
      ⟨(max |x 0| |x 1| - max |y 0| |y 1|).toNat, by omega⟩
    have := reachIn_corner hNy n
    rw [← hn] at this
    exact hx'.trans (this.symm.trans hy'.symm)

/-! ### The infinite component of the complement -/

/-- The infinite "outside" of `D`: the sites off `D` whose connected component in the graph
induced on `Dᶜ` is infinite. -/
def outside (D : Set Site) : Set Site :=
  {j | ∃ hj : j ∈ Dᶜ, (((latticeGraph 2).induce Dᶜ).connectedComponentMk ⟨j, hj⟩).supp.Infinite}

lemma outside_subset_compl (D : Set Site) : outside D ⊆ Dᶜ := fun _ h ↦ h.1

lemma notMem_of_mem_outside {D : Set Site} {j : Site} (h : j ∈ outside D) : j ∉ D := h.1

/-- The support of the component of `j` in `Dᶜ`, seen in `ℤ²`, is the set of sites reachable
from `j` within `Dᶜ`. -/
lemma image_val_supp_connectedComponentMk (D : Set Site) (j : Site) (hj : j ∈ Dᶜ) :
    Subtype.val '' (((latticeGraph 2).induce Dᶜ).connectedComponentMk ⟨j, hj⟩).supp
      = {k | ReachIn (latticeGraph 2) Dᶜ j k} := by
  ext k
  constructor
  · rintro ⟨⟨k', hk'⟩, hsupp, rfl⟩
    exact ⟨hj, hk', (SimpleGraph.ConnectedComponent.eq.1 hsupp).symm⟩
  · rintro ⟨hj', hk, hr⟩
    exact ⟨⟨k, hk⟩, SimpleGraph.ConnectedComponent.eq.2 hr.symm, rfl⟩

/-- Membership in the infinite outside, via reachability within `Dᶜ`. -/
lemma mem_outside_iff {D : Set Site} {j : Site} :
    j ∈ outside D ↔ j ∉ D ∧ {k | ReachIn (latticeGraph 2) Dᶜ j k}.Infinite := by
  constructor
  · rintro ⟨hj, hinf⟩
    exact ⟨hj, image_val_supp_connectedComponentMk D j hj ▸
      hinf.image Subtype.val_injective.injOn⟩
  · rintro ⟨hj, hinf⟩
    refine ⟨hj, ?_⟩
    rw [← Set.infinite_image_iff Subtype.val_injective.injOn,
      image_val_supp_connectedComponentMk D j hj]
    exact hinf

/-- Reaching within `Dᶜ` preserves membership in the infinite outside. -/
lemma ReachIn.mem_outside {D : Set Site} {j k : Site} (hj : j ∈ outside D)
    (h : ReachIn (latticeGraph 2) Dᶜ j k) : k ∈ outside D := by
  rw [mem_outside_iff] at hj ⊢
  exact ⟨h.mem_right, hj.2.mono fun r hr ↦ h.symm.trans hr⟩

/-- The infinite outside of `D` is closed under adjacency off `D`. -/
lemma mem_outside_of_adj {D : Set Site} {i j : Site} (hi : i ∉ D)
    (hij : (latticeGraph 2).Adj i j) (hj : j ∈ outside D) : i ∈ outside D :=
  ReachIn.mem_outside hj (ReachIn.of_adj (outside_subset_compl D hj) hi hij.symm)

/-- A neighbour of the infinite outside which is not itself outside lies in `D`
(Georgii's "bond of the last exit from `D`"). -/
lemma mem_of_adj_outside {D : Set Site} {i j : Site} (hi : i ∉ outside D)
    (hij : (latticeGraph 2).Adj i j) (hj : j ∈ outside D) : i ∈ D := by
  by_contra hiD
  exact hi (mem_outside_of_adj hiD hij hj)

/-- Every site outside a box containing `D` belongs to the infinite outside of `D`. -/
lemma mem_outside_of_notMem_box {D : Set Site} {N : ℕ} (hDN : D ⊆ box N) {x : Site}
    (hx : x ∉ box N) : x ∈ outside D := by
  rw [mem_outside_iff]
  have hDc : (box N)ᶜ ⊆ Dᶜ := Set.compl_subset_compl.2 hDN
  refine ⟨fun hxD ↦ hx (hDN hxD), ?_⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ mk (max |x 0| |x 1| + n) (max |x 0| |x 1| + n)) ?_ ?_
  · intro m n hmn
    have h0 : max |x 0| |x 1| + (m : ℤ) = max |x 0| |x 1| + n := by
      simpa using congrArg (fun z ↦ z 0) hmn
    omega
  · exact fun n ↦ ((reachIn_corner_of_notMem_box hx).trans
      (reachIn_corner (lt_of_notMem_box hx) n)).mono hDc

/-- Any two sites of the infinite outside are connected within `Dᶜ`: uniqueness of the
infinite component of `Dᶜ`. -/
lemma reachIn_of_mem_outside {D : Set Site} (hD : D.Finite) {j k : Site}
    (hj : j ∈ outside D) (hk : k ∈ outside D) : ReachIn (latticeGraph 2) Dᶜ j k := by
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  have hDc : (box N)ᶜ ⊆ Dᶜ := Set.compl_subset_compl.2 hDN
  obtain ⟨p, hp, hpN⟩ := ((mem_outside_iff.1 hj).2).exists_notMem_finite (box_finite N)
  obtain ⟨q, hq, hqN⟩ := ((mem_outside_iff.1 hk).2).exists_notMem_finite (box_finite N)
  exact (hp.trans ((reachIn_compl_box hpN hqN).mono hDc)).trans hq.symm

/-- **The complement of a finite `D ⊆ ℤ²` has exactly one infinite connected component.** -/
theorem existsUnique_infinite_connectedComponent {D : Set Site} (hD : D.Finite) :
    ∃! C : ((latticeGraph 2).induce Dᶜ).ConnectedComponent, C.supp.Infinite := by
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  have hc : mk ((N : ℤ) + 1) ((N : ℤ) + 1) ∉ box N := by
    rw [notMem_box_iff, mk_zero]
    exact Or.inl (by rw [abs_of_nonneg (by omega)]; omega)
  obtain ⟨hmem, hinf⟩ := mem_outside_of_notMem_box hDN hc
  refine ⟨_, hinf, ?_⟩
  intro C hC
  obtain ⟨⟨v, hv⟩, hvC⟩ := C.nonempty_supp
  have hCv : ((latticeGraph 2).induce Dᶜ).connectedComponentMk ⟨v, hv⟩ = C := hvC
  have hvout : v ∈ outside D := ⟨hv, by rw [hCv]; exact hC⟩
  obtain ⟨hv', hc', hr⟩ :=
    reachIn_of_mem_outside hD hvout (mem_outside_of_notMem_box hDN hc)
  rw [← hCv]
  exact SimpleGraph.ConnectedComponent.eq.2 hr

/-! ### The outer boundary -/

/-- The outer boundary of `D`: the bonds joining `D` to the infinite component of `Dᶜ`
(Georgii's circuit `c` in Lemma (6.14)). -/
def outerBoundary (D : Set Site) : Set (Sym2 Site) :=
  {e | ∃ i ∈ D, ∃ j ∈ outside D, (latticeGraph 2).Adj i j ∧ e = s(i, j)}

lemma outerBoundary_subset_edgeBoundary (D : Set Site) :
    outerBoundary D ⊆ edgeBoundary D := by
  rintro e ⟨i, hi, j, hj, hij, rfl⟩
  exact ⟨i, hi, j, notMem_of_mem_outside hj, hij, rfl⟩

/-- The edge boundary of a finite set of sites is finite. -/
lemma edgeBoundary_finite {D : Set Site} (hD : D.Finite) : (edgeBoundary D).Finite := by
  have hsub : edgeBoundary D ⊆ ⋃ i ∈ D,
      ({s(i, i + e0), s(i, i + e1), s(i, i - e0), s(i, i - e1)} : Set (Sym2 Site)) := by
    rintro e ⟨i, hi, j, hj, hij, rfl⟩
    refine Set.mem_biUnion hi ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (latticeGraph_two_adj_iff' i j).1 hij with h | h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inr (Or.inl (by rw [h, add_sub_cancel_right])))
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, add_sub_cancel_right])))
  exact (hD.biUnion fun i _ ↦ (Set.finite_singleton _).insert _ |>.insert _ |>.insert _).subset
    hsub

/-- The outer boundary of a finite set of sites is finite. -/
lemma outerBoundary_finite {D : Set Site} (hD : D.Finite) : (outerBoundary D).Finite :=
  (edgeBoundary_finite hD).subset (outerBoundary_subset_edgeBoundary D)

/-- A bond lies in the outer boundary iff one endpoint is in `D` and the other in the
infinite outside. -/
lemma mem_outerBoundary_iff {D : Set Site} {u v : Site} (huv : (latticeGraph 2).Adj u v) :
    s(u, v) ∈ outerBoundary D ↔
      (u ∈ D ∧ v ∈ outside D) ∨ (v ∈ D ∧ u ∈ outside D) := by
  constructor
  · rintro ⟨i, hi, j, hj, hij, hs⟩
    rw [Sym2.eq_iff] at hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi, hj⟩
    · exact Or.inr ⟨hi, hj⟩
  · rintro (⟨hu, hv⟩ | ⟨hv, hu⟩)
    · exact ⟨u, hu, v, hv, huv, rfl⟩
    · exact ⟨v, hv, u, hu, huv.symm, Sym2.eq_swap⟩

/-! ### Crossing the outer boundary: last exit and the anchor bond -/

/-- A chain starting off the infinite outside and ending in it crosses the outer boundary
at its first entrance. -/
lemma chain_exists_outerBoundary_bond {D : Set Site} (p : ℕ → Site)
    (hadj : ∀ k, (latticeGraph 2).Adj (p k) (p (k + 1))) (h0 : p 0 ∉ outside D) :
    ∀ n, p n ∈ outside D →
      ∃ k < n, p k ∈ D ∧ p (k + 1) ∈ outside D ∧ s(p k, p (k + 1)) ∈ outerBoundary D := by
  intro n
  induction n with
  | zero => exact fun hn ↦ absurd hn h0
  | succ n ih =>
    intro hn
    by_cases hpn : p n ∈ outside D
    · obtain ⟨k, hk, h⟩ := ih hpn
      exact ⟨k, by omega, h⟩
    · exact ⟨n, by omega, mem_of_adj_outside hpn (hadj n) hn, hn,
        ⟨p n, mem_of_adj_outside hpn (hadj n) hn, p (n + 1), hn, hadj n, rfl⟩⟩

/-- Walking right from `a ∈ D` along the horizontal half-line, some bond lies in the outer
boundary. -/
lemma exists_horizontal_outerBoundary_bond {D : Set Site} (hD : D.Finite) {a : Site}
    (ha : a ∈ D) : ∃ k : ℕ, s(a + k • e0, a + (k + 1) • e0) ∈ outerBoundary D := by
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  have haN : |a 0| ≤ (N : ℤ) := (hDN ha) 0
  have h0 : a + (0 : ℕ) • e0 ∉ outside D := by
    have h : a + (0 : ℕ) • e0 = a := by simp
    rw [h]
    exact fun h' ↦ notMem_of_mem_outside h' ha
  set n : ℕ := ((N : ℤ) + 1 - a 0).toNat with hn
  have hcast : ((N : ℤ) + 1 - a 0) ≤ (n : ℤ) := Int.self_le_toNat _
  have hpnbox : a + n • e0 ∉ box N := by
    rw [notMem_box_iff]
    refine Or.inl ?_
    have h1 : (a + n • e0) 0 = a 0 + n := by simp
    rw [h1, abs_of_nonneg (by omega)]
    omega
  obtain ⟨k, -, -, -, hbond⟩ := chain_exists_outerBoundary_bond (fun k ↦ a + k • e0)
    (fun k ↦ adj_nsmul_e0 a k) h0 n (mem_outside_of_notMem_box hDN hpnbox)
  exact ⟨k, hbond⟩

/-- The outer boundary of a finite nonempty set of sites is nonempty. -/
lemma outerBoundary_nonempty {D : Set Site} (hD : D.Finite) (hne : D.Nonempty) :
    (outerBoundary D).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨k, hk⟩ := exists_horizontal_outerBoundary_bond hD ha
  exact ⟨_, hk⟩

/-- **Georgii (6.14), "surrounding"**: every lattice walk from a site not in the infinite
outside — in particular from a site of `D` — to the infinite outside uses a bond of the outer
boundary (the bond of the last exit from `D`). -/
theorem exists_outerBoundary_bond_of_walk {D : Set Site} :
    ∀ {a b : Site} (w : (latticeGraph 2).Walk a b), a ∉ outside D → b ∈ outside D →
      ∃ e ∈ w.edges, e ∈ outerBoundary D
  | _, _, .nil, ha, hb => absurd hb ha
  | a, b, .cons (v := v) huv p, ha, hb => by
    classical
    by_cases hv : v ∈ outside D
    · exact ⟨s(a, v), by simp, a, mem_of_adj_outside ha huv hv, v, hv, huv, rfl⟩
    · obtain ⟨e, he, heOB⟩ := exists_outerBoundary_bond_of_walk p hv hb
      exact ⟨e, by simp [he], heOB⟩

/-- Every lattice walk from a site of `D` to the infinite outside crosses the outer boundary. -/
theorem exists_outerBoundary_bond_of_walk_of_mem {D : Set Site} {a b : Site}
    (w : (latticeGraph 2).Walk a b) (ha : a ∈ D) (hb : b ∈ outside D) :
    ∃ e ∈ w.edges, e ∈ outerBoundary D :=
  exists_outerBoundary_bond_of_walk w (fun h ↦ notMem_of_mem_outside h ha) hb

/-- **The anchor bond** (for the counting Lemma (6.13)): for `a ∈ D` some bond
`s(a + k•e0, a + (k+1)•e0)` of the horizontal half-line from `a` lies in the outer boundary
with `k < |outerBoundary D|`. -/
theorem exists_anchor_bond {D : Set Site} (hD : D.Finite) {a : Site} (ha : a ∈ D) :
    ∃ k : ℕ, k < (outerBoundary D).ncard ∧
      s(a + k • e0, a + (k + 1) • e0) ∈ outerBoundary D := by
  classical
  obtain ⟨N, hDN⟩ := exists_subset_box hD
  have hex := exists_horizontal_outerBoundary_bond hD ha
  set k := Nat.find hex with hk
  refine ⟨k, ?_, Nat.find_spec hex⟩
  -- no site of the half-line up to `k` lies in the infinite outside
  have hray : ∀ m, m ≤ k → a + m • e0 ∉ outside D := by
    intro m
    induction m with
    | zero =>
      intro _ hout
      have h : a + (0 : ℕ) • e0 = a := by simp
      rw [h] at hout
      exact notMem_of_mem_outside hout ha
    | succ m ih =>
      intro hm hout
      have hm' : a + m • e0 ∉ outside D := ih (by omega)
      have hmD : a + m • e0 ∈ D := mem_of_adj_outside hm' (adj_nsmul_e0 a m) hout
      exact Nat.find_min hex (show m < Nat.find hex by omega)
        ⟨_, hmD, _, hout, adj_nsmul_e0 a m, rfl⟩
  -- for each `m ≤ k`, walking upwards from `a + m • e0` yields a vertical outer-boundary
  -- bond in the column `a 0 + m`
  have hvert : ∀ m : ℕ, m ≤ k → ∃ y : ℤ,
      s(mk (a 0 + (m : ℤ)) y, mk (a 0 + (m : ℤ)) (y + 1)) ∈ outerBoundary D := by
    intro m hm
    set q : ℕ → Site := fun t ↦ a + m • e0 + t • e1 with hq
    have hqc : ∀ t : ℕ, q t = mk (a 0 + (m : ℤ)) (a 1 + (t : ℤ)) := by
      intro t
      rw [site_ext_iff]
      constructor <;> simp [hq]
    have h0 : q 0 ∉ outside D := by
      have h : q 0 = a + m • e0 := by simp [hq]
      rw [h]
      exact hray m hm
    set T : ℕ := ((N : ℤ) + 1 - a 1).toNat with hT
    have hcast : ((N : ℤ) + 1 - a 1) ≤ (T : ℤ) := Int.self_le_toNat _
    have hqbox : q T ∉ box N := by
      rw [notMem_box_iff]
      refine Or.inr ?_
      rw [hqc T, mk_one, abs_of_nonneg (by omega)]
      omega
    obtain ⟨t, -, -, -, hbond⟩ := chain_exists_outerBoundary_bond q
      (fun t ↦ adj_nsmul_e1 _ t) h0 T (mem_outside_of_notMem_box hDN hqbox)
    refine ⟨a 1 + t, ?_⟩
    have h2 : q (t + 1) = mk (a 0 + (m : ℤ)) (a 1 + (t : ℤ) + 1) := by
      rw [hqc (t + 1)]
      congr 1
      push_cast
      ring
    rw [hqc t, h2] at hbond
    exact hbond
  -- inject the columns `a 0 + m`, `m ≤ k`, into the outer boundary
  choose y hy using hvert
  set F : Fin (k + 1) → Sym2 Site := fun m ↦
    s(mk (a 0 + ((m : ℕ) : ℤ)) (y (m : ℕ) (Nat.lt_succ_iff.mp m.isLt)),
      mk (a 0 + ((m : ℕ) : ℤ)) (y (m : ℕ) (Nat.lt_succ_iff.mp m.isLt) + 1)) with hF
  have hinj : Function.Injective F := by
    intro m₁ m₂ h
    simp only [hF, Sym2.eq_iff] at h
    have h0 : (a 0 : ℤ) + (m₁ : ℕ) = a 0 + (m₂ : ℕ) := by
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simpa using congrArg (fun z ↦ z 0) h1
    exact Fin.val_injective (by omega)
  have hsub : Set.range F ⊆ outerBoundary D := by
    rintro e ⟨m, rfl⟩
    exact hy (m : ℕ) (Nat.lt_succ_iff.mp m.isLt)
  have h1 : (Set.range F).ncard = k + 1 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    simp
  have h2 : (Set.range F).ncard ≤ (outerBoundary D).ncard :=
    Set.ncard_le_ncard hsub (outerBoundary_finite hD)
  omega

/-! ### A `ZMod 2` antiderivative on `ℤ`, and the potential of an even bond labelling -/

/-- A `ZMod 2` antiderivative: `intSum g t` sums `g` between `0` and `t` (signs are immaterial
in characteristic two). -/
def intSum (g : ℤ → ZMod 2) (t : ℤ) : ZMod 2 := ∑ i ∈ Finset.Ico (min 0 t) (max 0 t), g i

@[simp] lemma intSum_zero (g : ℤ → ZMod 2) : intSum g 0 = 0 := by simp [intSum]

/-- The defining recurrence of the antiderivative. -/
lemma intSum_add_one (g : ℤ → ZMod 2) (t : ℤ) : intSum g (t + 1) = intSum g t + g t := by
  rcases (by omega : 0 ≤ t ∨ t < 0) with ht | ht
  · have h1 : min 0 (t + 1) = 0 := by omega
    have h2 : max 0 (t + 1) = t + 1 := by omega
    have h3 : min 0 t = 0 := by omega
    have h4 : max 0 t = t := by omega
    have h5 : Finset.Ico (0 : ℤ) (t + 1) = insert t (Finset.Ico (0 : ℤ) t) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    simp only [intSum, h1, h2, h3, h4, h5]
    rw [Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
    exact add_comm _ _
  · have h1 : min 0 (t + 1) = t + 1 := by omega
    have h2 : max 0 (t + 1) = 0 := by omega
    have h3 : min 0 t = t := by omega
    have h4 : max 0 t = 0 := by omega
    have h5 : Finset.Ico t (0 : ℤ) = insert t (Finset.Ico (t + 1) (0 : ℤ)) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    simp only [intSum, h1, h2, h3, h4, h5]
    rw [Finset.sum_insert (by simp only [Finset.mem_Ico]; omega)]
    exact (by decide : ∀ a b : ZMod 2, b = a + b + a) _ _

/-- The downward recurrence of the antiderivative. -/
lemma intSum_sub_one (g : ℤ → ZMod 2) (t : ℤ) : intSum g (t - 1) = intSum g t + g (t - 1) := by
  have h := intSum_add_one g (t - 1)
  rw [show t - 1 + 1 = t from by ring] at h
  rw [h]
  exact (by decide : ∀ a b : ZMod 2, a = a + b + b) _ _

/-- **Plaquettes generate the cycle space of `ℤ²`**: a `ZMod 2`-valued bond labelling `κ` whose
four-term plaquette sums vanish is a coboundary `κ s(u, v) = φ u + φ v` (Timár's cycle-space
step, made explicit by integrating `κ` along L-shaped lattice paths). -/
lemma exists_potential (κ : Sym2 Site → ZMod 2)
    (hP : ∀ t u : ℤ, κ s(mk t u, mk (t + 1) u) + κ s(mk t u, mk t (u + 1))
      + κ s(mk (t + 1) u, mk (t + 1) (u + 1)) + κ s(mk t (u + 1), mk (t + 1) (u + 1)) = 0) :
    ∃ φ : Site → ZMod 2,
      ∀ u v : Site, (latticeGraph 2).Adj u v → φ u + φ v = κ s(u, v) := by
  have hkey : ∀ t u : ℤ,
      intSum (fun w ↦ κ s(mk t w, mk t (w + 1))) u
        + intSum (fun w ↦ κ s(mk (t + 1) w, mk (t + 1) (w + 1))) u
      = κ s(mk t u, mk (t + 1) u) + κ s(mk t 0, mk (t + 1) 0) := by
    intro t u
    induction u using Int.induction_on with
    | zero =>
      simp only [intSum_zero]
      exact (by decide : ∀ x : ZMod 2, (0 : ZMod 2) + 0 = x + x) _
    | succ n ih =>
      rw [intSum_add_one, intSum_add_one]
      exact (by decide : ∀ A₁ A₂ a b X X' Y : ZMod 2,
        A₁ + A₂ = X + Y → X + a + b + X' = 0 → A₁ + a + (A₂ + b) = X' + Y)
        _ _ _ _ _ _ _ ih (hP t n)
    | pred n ih =>
      have hco : (-(n : ℤ) - 1) + 1 = -(n : ℤ) := by ring
      have hP' := hP t (-(n : ℤ) - 1)
      rw [hco] at hP'
      rw [intSum_sub_one, intSum_sub_one]
      rw [hco]
      exact (by decide : ∀ B₁ B₂ a b W X Y : ZMod 2,
        B₁ + B₂ = X + Y → W + a + b + X = 0 → B₁ + a + (B₂ + b) = W + Y)
        _ _ _ _ _ _ _ ih hP'
  have hvert : ∀ t b : ℤ,
      (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) t
          + intSum (fun w ↦ κ s(mk t w, mk t (w + 1))) b)
        + (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) t
          + intSum (fun w ↦ κ s(mk t w, mk t (w + 1))) (b + 1))
      = κ s(mk t b, mk t (b + 1)) := by
    intro t b
    rw [intSum_add_one]
    exact (by decide : ∀ A B c : ZMod 2, A + B + (A + (B + c)) = c) _ _ _
  have hhor : ∀ t b : ℤ,
      (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) t
          + intSum (fun w ↦ κ s(mk t w, mk t (w + 1))) b)
        + (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) (t + 1)
          + intSum (fun w ↦ κ s(mk (t + 1) w, mk (t + 1) (w + 1))) b)
      = κ s(mk t b, mk (t + 1) b) := by
    intro t b
    rw [intSum_add_one]
    exact (by decide : ∀ A B₁ B₂ X Y : ZMod 2,
      B₁ + B₂ = X + Y → A + B₁ + (A + Y + B₂) = X) _ _ _ _ _ (hkey t b)
  refine ⟨fun x ↦ intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) (x 0)
      + intSum (fun w ↦ κ s(mk (x 0) w, mk (x 0) (w + 1))) (x 1), ?_⟩
  have main : ∀ x y : Site, y = x + e0 ∨ y = x + e1 →
      (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) (x 0)
          + intSum (fun w ↦ κ s(mk (x 0) w, mk (x 0) (w + 1))) (x 1))
        + (intSum (fun r ↦ κ s(mk r 0, mk (r + 1) 0)) (y 0)
          + intSum (fun w ↦ κ s(mk (y 0) w, mk (y 0) (w + 1))) (y 1))
      = κ s(x, y) := by
    rintro x y (rfl | rfl)
    · obtain ⟨t, b, rfl⟩ : ∃ t b : ℤ, x = mk t b := ⟨x 0, x 1, (mk_eta x).symm⟩
      rw [mk_add_e0]
      simp only [mk_zero, mk_one]
      exact hhor t b
    · obtain ⟨t, b, rfl⟩ : ∃ t b : ℤ, x = mk t b := ⟨x 0, x 1, (mk_eta x).symm⟩
      rw [mk_add_e1]
      simp only [mk_zero, mk_one]
      exact hvert t b
  intro u v huv
  rcases (latticeGraph_two_adj_iff' u v).1 huv with h | h | h | h
  · exact main u v (Or.inl h)
  · have hk := main v u (Or.inl h)
    rw [Sym2.eq_swap] at hk
    exact (by decide : ∀ x y z : ZMod 2, x + y = z → y + x = z) _ _ _ hk
  · exact main u v (Or.inr h)
  · have hk := main v u (Or.inr h)
    rw [Sym2.eq_swap] at hk
    exact (by decide : ∀ x y z : ZMod 2, x + y = z → y + x = z) _ _ _ hk

/-! ### Georgii Lemma (6.14): connectivity of the outer boundary -/

/-- The plaquette at `mk t u`, in coordinates. -/
lemma plaquette_mk (t u : ℤ) :
    plaquette (mk t u) = {s(mk t u, mk (t + 1) u), s(mk t u, mk t (u + 1)),
      s(mk (t + 1) u, mk (t + 1) (u + 1)), s(mk t (u + 1), mk (t + 1) (u + 1))} := by
  simp only [plaquette, mk_add_e0, mk_add_e1]

lemma mem_plaquette₁ (t u : ℤ) : s(mk t u, mk (t + 1) u) ∈ plaquette (mk t u) := by
  rw [plaquette_mk]; simp

lemma mem_plaquette₂ (t u : ℤ) : s(mk t u, mk t (u + 1)) ∈ plaquette (mk t u) := by
  rw [plaquette_mk]; simp

lemma mem_plaquette₃ (t u : ℤ) : s(mk (t + 1) u, mk (t + 1) (u + 1)) ∈ plaquette (mk t u) := by
  rw [plaquette_mk]; simp

lemma mem_plaquette₄ (t u : ℤ) : s(mk t (u + 1), mk (t + 1) (u + 1)) ∈ plaquette (mk t u) := by
  rw [plaquette_mk]; simp

lemma adj_mk_horiz (t u : ℤ) : (latticeGraph 2).Adj (mk t u) (mk (t + 1) u) := by
  rw [← mk_add_e0]; exact adj_add_e0 _

lemma adj_mk_vert (t u : ℤ) : (latticeGraph 2).Adj (mk t u) (mk t (u + 1)) := by
  rw [← mk_add_e1]; exact adj_add_e1 _

open Classical in
/-- The `ZMod 2` indicator of the outer boundary is the coboundary of the indicator of the
infinite outside. -/
lemma outerBoundary_chi {D : Set Site} {u v : Site} (huv : (latticeGraph 2).Adj u v) :
    (if s(u, v) ∈ outerBoundary D then (1 : ZMod 2) else 0)
      = (if u ∈ outside D then (1 : ZMod 2) else 0)
        + (if v ∈ outside D then (1 : ZMod 2) else 0) := by
  by_cases hu : u ∈ outside D <;> by_cases hv : v ∈ outside D
  · have hOB : s(u, v) ∉ outerBoundary D := by
      rw [mem_outerBoundary_iff huv]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact notMem_of_mem_outside hu h1
      · exact notMem_of_mem_outside hv h1
    rw [ite_eq_right hOB, ite_eq_left hu, ite_eq_left hv]
    decide
  · have hvD : v ∈ D := mem_of_adj_outside hv huv.symm hu
    have hOB : s(u, v) ∈ outerBoundary D := (mem_outerBoundary_iff huv).2 (Or.inr ⟨hvD, hu⟩)
    rw [ite_eq_left hOB, ite_eq_left hu, ite_eq_right hv]
    decide
  · have huD : u ∈ D := mem_of_adj_outside hu huv hv
    have hOB : s(u, v) ∈ outerBoundary D := (mem_outerBoundary_iff huv).2 (Or.inl ⟨huD, hv⟩)
    rw [ite_eq_left hOB, ite_eq_right hu, ite_eq_left hv]
    decide
  · have hOB : s(u, v) ∉ outerBoundary D := by
      rw [mem_outerBoundary_iff huv]
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact hv h2
      · exact hu h2
    rw [ite_eq_right hOB, ite_eq_right hu, ite_eq_right hv]
    decide

/-- A graph induced on a set of vertices is connected iff the set is nonempty and any two of
its elements are joined by a walk inside it. -/
lemma induce_connected_iff {V : Type*} {G : SimpleGraph V} {s : Set V} :
    (G.induce s).Connected ↔ s.Nonempty ∧ ∀ u v, u ∈ s → v ∈ s → ReachIn G s u v := by
  constructor
  · intro h
    obtain ⟨⟨x, hx⟩⟩ := h.nonempty
    exact ⟨⟨x, hx⟩, fun u v hu hv ↦ ⟨hu, hv, h.preconnected _ _⟩⟩
  · rintro ⟨⟨x, hx⟩, h⟩
    have : Nonempty s := ⟨⟨x, hx⟩⟩
    refine ⟨fun u v ↦ ?_⟩
    obtain ⟨hu, hv, hr⟩ := h u.1 v.1 u.2 v.2
    exact hr

/-- **Georgii Lemma (6.14), combinatorial core (after Timár)**: for a finite, nonempty,
connected set of sites `D ⊆ ℤ²`, the outer boundary of `D` — the bonds joining `D` to the
infinite component of `Dᶜ` — is connected in the plaquette-adjacency graph on bonds. -/
theorem outerBoundary_connected {D : Set Site} (hD : D.Finite) (hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) :
    (bondGraph.induce (outerBoundary D)).Connected := by
  classical
  rw [induce_connected_iff] at hconn ⊢
  obtain ⟨-, hDreach⟩ := hconn
  refine ⟨outerBoundary_nonempty hD hne, ?_⟩
  intro e₀ f he₀ hf
  by_contra hcon
  -- `A` is the set of boundary bonds reachable from `e₀`; `κ` its `ZMod 2` indicator.
  set A : Set (Sym2 Site) := {e | ReachIn bondGraph (outerBoundary D) e₀ e} with hA
  have he₀A : e₀ ∈ A := ReachIn.refl he₀
  have hfA : f ∉ A := hcon
  have hAsub : A ⊆ outerBoundary D := fun e he ↦ he.mem_right
  have hclosed : ∀ {e g : Sym2 Site} {x : Site}, e ∈ A → g ∈ outerBoundary D →
      e ∈ plaquette x → g ∈ plaquette x → g ∈ A := by
    intro e g x he hg hex hgx
    by_cases heg : e = g
    · exact heg ▸ he
    · exact ReachIn.trans he (ReachIn.of_adj (hAsub he) hg ⟨heg, x, hex, hgx⟩)
  set κ : Sym2 Site → ZMod 2 := fun e ↦ if e ∈ A then 1 else 0 with hκ
  -- the plaquette sums of `κ` vanish: either no bond of the plaquette is in `A`, or all its
  -- boundary bonds are, and then `κ` agrees on it with the coboundary of the outside indicator
  have hP : ∀ t u : ℤ, κ s(mk t u, mk (t + 1) u) + κ s(mk t u, mk t (u + 1))
      + κ s(mk (t + 1) u, mk (t + 1) (u + 1)) + κ s(mk t (u + 1), mk (t + 1) (u + 1)) = 0 := by
    intro t u
    by_cases hA1 : s(mk t u, mk (t + 1) u) ∈ A ∨ s(mk t u, mk t (u + 1)) ∈ A
        ∨ s(mk (t + 1) u, mk (t + 1) (u + 1)) ∈ A ∨ s(mk t (u + 1), mk (t + 1) (u + 1)) ∈ A
    · have hkOB : ∀ g, g ∈ plaquette (mk t u) →
          κ g = if g ∈ outerBoundary D then (1 : ZMod 2) else 0 := by
        intro g hg
        by_cases hgOB : g ∈ outerBoundary D
        · rw [ite_eq_left hgOB]
          have hgA : g ∈ A := by
            rcases hA1 with h | h | h | h
            · exact hclosed h hgOB (mem_plaquette₁ t u) hg
            · exact hclosed h hgOB (mem_plaquette₂ t u) hg
            · exact hclosed h hgOB (mem_plaquette₃ t u) hg
            · exact hclosed h hgOB (mem_plaquette₄ t u) hg
          simp [hκ, hgA]
        · rw [ite_eq_right hgOB]
          have hgA : g ∉ A := fun h' ↦ hgOB (hAsub h')
          simp [hκ, hgA]
      rw [hkOB _ (mem_plaquette₁ t u), hkOB _ (mem_plaquette₂ t u),
        hkOB _ (mem_plaquette₃ t u), hkOB _ (mem_plaquette₄ t u),
        outerBoundary_chi (adj_mk_horiz t u), outerBoundary_chi (adj_mk_vert t u),
        outerBoundary_chi (adj_mk_vert (t + 1) u), outerBoundary_chi (adj_mk_horiz t (u + 1))]
      exact (by decide : ∀ a b c d : ZMod 2,
        (a + b) + (a + c) + (b + d) + (c + d) = 0) _ _ _ _
    · push Not at hA1
      obtain ⟨h1, h2, h3, h4⟩ := hA1
      simp only [hκ, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
      decide
  obtain ⟨φ, hφ⟩ := exists_potential κ hP
  -- the potential is constant along walks inside `D` and inside `Dᶜ`
  have hφD : ∀ {p q : Site}, ReachIn (latticeGraph 2) D p q → φ p = φ q := by
    intro p q h
    refine h.invariant φ ?_
    intro a b ha hb hab
    have hOB : s(a, b) ∉ outerBoundary D := by
      rw [mem_outerBoundary_iff hab]
      rintro (⟨-, h2⟩ | ⟨-, h2⟩)
      · exact notMem_of_mem_outside h2 hb
      · exact notMem_of_mem_outside h2 ha
    have hAe : s(a, b) ∉ A := fun h' ↦ hOB (hAsub h')
    have hsum := hφ a b hab
    simp only [hκ, ite_eq_right hAe] at hsum
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hsum
  have hφDc : ∀ {p q : Site}, ReachIn (latticeGraph 2) Dᶜ p q → φ p = φ q := by
    intro p q h
    refine h.invariant φ ?_
    intro a b ha hb hab
    have hOB : s(a, b) ∉ outerBoundary D := by
      rw [mem_outerBoundary_iff hab]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact ha h1
      · exact hb h1
    have hAe : s(a, b) ∉ A := fun h' ↦ hOB (hAsub h')
    have hsum := hφ a b hab
    simp only [hκ, ite_eq_right hAe] at hsum
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ hsum
  -- endpoints of `e₀` and `f`
  obtain ⟨c₁, hc₁, d₁, hd₁, hadj₁, he₀eq⟩ := he₀
  obtain ⟨c₂, hc₂, d₂, hd₂, hadj₂, hfeq⟩ := hf
  have h1 : φ c₁ = φ c₂ := hφD (hDreach c₁ c₂ hc₁ hc₂)
  have h2 : φ d₁ = φ d₂ := hφDc (reachIn_of_mem_outside hD hd₁ hd₂)
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

end MeasureTheory.GibbsMeasure.Peierls

end

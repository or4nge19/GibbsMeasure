/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.InfiniteCluster
public import GibbsMeasure.Model.Contours

/-!
# Georgii Lemma (18.14): percolation of a spin pattern in a quadrant of `ℤ²`

Georgii, *Gibbs Measures and Phase Transitions*, §18.1.  Let `W` be a random subset of the plane
`ℤ²` such that every finite set `D` is disjoint from `W` with probability at most `t ^ |D|` (for
`W = V(G, ·)` this is Lemma (18.10), the chessboard estimate).  Lemma (18.14) says that the
origin then belongs to an infinite cluster of `W ∩ Q` with probability at least `1 - z(t)`, for
each of the four quadrants `Q` of the plane with vertex `0`, where
`z(t) = 1 ∧ ∑_{ℓ ≥ 1} ℓ (5t)^ℓ / 5` is (18.13).

Georgii's proof is planar duality plus a count.  If the origin is *not* in an infinite cluster
of `W ∩ Q`, there is a finite set `D ⊆ Q \ W` which is the vertex set of a self-avoiding
`*`-path joining the two half-axes bounding `Q`, "a suitable subset of the outer boundary of the
finite cluster of `V ∩ Q` containing the origin; cf. the proof of Lemma (6.14)".  The outer
boundary of a finite connected set of sites is connected in the plaquette graph on bonds
(`Peierls.outerBoundary_connected`, Timár's argument, `GibbsMeasure/Model/Contours.lean`), so its
outside endpoints are `*`-connected.  To confine the crossing to the quadrant one reflects:
`W' = fold⁻¹ W` is the four-fold reflection of `W ∩ Q`, the cluster of `0` in `W'` is finite, and
folding its `*`-connected outer vertex boundary back into `Q` produces the crossing.  There are
at most `ℓ · 5^{ℓ-1}` crossings of length `ℓ`, and each avoids `W` with probability at most
`t^ℓ`; countable subadditivity finishes the proof.

The file also records Georgii's remarks after (18.6) and (18.7) for the plane `P = ℤ²`: an ocean
is infinite, a set containing an ocean has a unique infinite cluster, `ξ⁰_P(G, ω) ≠ ∅` iff
`V_P(G, ω)` contains an ocean, and `ξ⁰_P` is equivariant under the translations and the
reflections of `ℤ²` (the invariance used in Georgii (18.17)).  The general theory of oceans is
in `GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/InfiniteCluster.lean`.

## Main declarations

* `starLatticeGraph d`: the `*`-neighbour graph on `ℤ^d` (sup-distance `1`).
* `quadrant s₁ s₂`: the quadrant `{0 ≤ s₁ x₁, 0 ≤ s₂ x₂}` of `ℤ²`, `s₁, s₂ ∈ {1, -1}`.
* `IsStarCrossing s₁ s₂ L`: the list `L` is a self-avoiding `*`-path in `quadrant s₁ s₂` from the
  vertical to the horizontal half-axis without shortcuts (Georgii's (i)–(iii)).
* `exists_isStarCrossing_of_notMem_infiniteClusters`: the crossing exists in `Q \ W` whenever the
  origin is not in an infinite cluster of `W ∩ Q`.
* `starCrossings s₁ s₂ ℓ`, `card_starCrossings_le`: the crossings of length `ℓ` form a finite
  set of at most `ℓ · 5 ^ (ℓ - 1)` lists.
* `crossingBound`: Georgii's `z` of (18.13); `crossingBound_le_four_mul` is `z(t) ≤ 4t` for
  `t ≤ 1/20`, the quantitative form of `z(t) → 0` as `t → 0`.
* `le_measure_mem_infiniteClusters`: **Lemma (18.14)**, and
  `le_measure_forall_mem_infiniteClusters` the four-quadrant union bound `μ(X) ≥ 1 - 4 z(t)`
  which opens the proof of (18.16).
* `nonempty_infiniteClusters_compl`, `infinite_of_isOceanIn`,
  `oceanPart_nonempty_iff_exists_isOceanIn`, `oceanPart_image_add_right`,
  `oceanPart_image_refl`: (18.6)/(18.7) in the plane.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure.Peierls Set

namespace MeasureTheory.GibbsMeasure

/-! ### The `*`-neighbour graph -/

/-- The `*`-neighbour graph on `ℤ^d`: two points are adjacent iff they are distinct and at
sup-distance `1`, i.e. `|i - j| = 1` or `√2` in `ℤ²`. -/
def starLatticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj x y := x ≠ y ∧ ∀ i, |x i - y i| ≤ 1
  symm := ⟨fun _ _ ⟨hne, h⟩ ↦ ⟨hne.symm, fun i ↦ by rw [abs_sub_comm]; exact h i⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

lemma starLatticeGraph_adj {d : ℕ} {x y : Fin d → ℤ} :
    (starLatticeGraph d).Adj x y ↔ x ≠ y ∧ ∀ i, |x i - y i| ≤ 1 := Iff.rfl

/-- Nearest neighbours are `*`-neighbours. -/
lemma latticeGraph_le_starLatticeGraph (d : ℕ) : latticeGraph d ≤ starLatticeGraph d := by
  intro x y hxy
  have h1 : ∑ i, (x i - y i).natAbs = 1 := hxy
  refine ⟨fun hxy' ↦ by simp [hxy'] at h1, fun i ↦ ?_⟩
  have := Finset.single_le_sum (f := fun i ↦ (x i - y i).natAbs) (fun i _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)
  rw [h1] at this
  rw [Int.abs_eq_natAbs]
  omega

namespace Peierls

lemma starLatticeGraph_two_adj_iff (x y : Site) :
    (starLatticeGraph 2).Adj x y ↔ x ≠ y ∧ |x 0 - y 0| ≤ 1 ∧ |x 1 - y 1| ≤ 1 := by
  rw [starLatticeGraph_adj, Fin.forall_fin_two]

/-! ### Quadrants, reflections and the fold -/

/-- The quadrant `{x : 0 ≤ s₁ x₀, 0 ≤ s₂ x₁}` of `ℤ²` with vertex `0`; `s₁, s₂ ∈ {1, -1}`. -/
def quadrant (s₁ s₂ : ℤ) : Set Site := {x | 0 ≤ s₁ * x 0 ∧ 0 ≤ s₂ * x 1}

lemma mem_quadrant {s₁ s₂ : ℤ} {x : Site} : x ∈ quadrant s₁ s₂ ↔ 0 ≤ s₁ * x 0 ∧ 0 ≤ s₂ * x 1 :=
  Iff.rfl

lemma zero_mem_quadrant (s₁ s₂ : ℤ) : (0 : Site) ∈ quadrant s₁ s₂ := by simp [mem_quadrant]

/-- The coordinate reflection `x ↦ (ε₁ x₀, ε₂ x₁)`, `ε₁, ε₂ ∈ {1, -1}`. -/
def refl (ε₁ ε₂ : ℤ) (x : Site) : Site := mk (ε₁ * x 0) (ε₂ * x 1)

@[simp] lemma refl_zero (ε₁ ε₂ : ℤ) (x : Site) : refl ε₁ ε₂ x 0 = ε₁ * x 0 := by simp [refl]

@[simp] lemma refl_one (ε₁ ε₂ : ℤ) (x : Site) : refl ε₁ ε₂ x 1 = ε₂ * x 1 := by simp [refl]

/-- The fold `x ↦ (s₁ |x₀|, s₂ |x₁|)` of `ℤ²` onto `quadrant s₁ s₂`. -/
def fold (s₁ s₂ : ℤ) (x : Site) : Site := mk (s₁ * |x 0|) (s₂ * |x 1|)

@[simp] lemma fold_zero' (s₁ s₂ : ℤ) (x : Site) : fold s₁ s₂ x 0 = s₁ * |x 0| := by simp [fold]

@[simp] lemma fold_one' (s₁ s₂ : ℤ) (x : Site) : fold s₁ s₂ x 1 = s₂ * |x 1| := by simp [fold]

@[simp] lemma fold_zero (s₁ s₂ : ℤ) : fold s₁ s₂ 0 = 0 := by
  rw [site_ext_iff]; simp

/-- The sign `foldSign s a ∈ {1, -1}` with `s |a| = foldSign s a * a`. -/
def foldSign (s a : ℤ) : ℤ := if 0 ≤ a then s else -s

lemma foldSign_mul (s a : ℤ) : foldSign s a * a = s * |a| := by
  unfold foldSign
  split_ifs with h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (not_le.1 h)]; ring

lemma foldSign_eq {s : ℤ} (hs : s = 1 ∨ s = -1) (a : ℤ) : foldSign s a = 1 ∨ foldSign s a = -1 := by
  unfold foldSign
  split_ifs <;> rcases hs with rfl | rfl <;> simp

/-- The fold is the reflection by the coordinate signs. -/
lemma fold_eq_refl (s₁ s₂ : ℤ) (x : Site) :
    fold s₁ s₂ x = refl (foldSign s₁ (x 0)) (foldSign s₂ (x 1)) x := by
  rw [site_ext_iff]; simp [foldSign_mul]

lemma refl_refl {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) (x : Site) :
    refl ε₁ ε₂ (refl ε₁ ε₂ x) = x := by
  rw [site_ext_iff]
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

lemma fold_refl {s₁ s₂ ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) (x : Site) :
    fold s₁ s₂ (refl ε₁ ε₂ x) = fold s₁ s₂ x := by
  rw [site_ext_iff]
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

lemma fold_mem_quadrant {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (x : Site) : fold s₁ s₂ x ∈ quadrant s₁ s₂ := by
  rw [mem_quadrant]
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> simp [abs_nonneg]

lemma fold_eq_self_of_mem_quadrant {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) {x : Site} (hx : x ∈ quadrant s₁ s₂) : fold s₁ s₂ x = x := by
  rw [mem_quadrant] at hx
  rw [site_ext_iff]
  rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;>
    simp only [fold_zero', fold_one', one_mul, neg_mul] at hx ⊢ <;>
    constructor <;> first
      | exact abs_of_nonneg (by omega)
      | (rw [abs_of_nonpos (by omega)]; ring)

lemma refl_fold_eq_self {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (x : Site) : refl (foldSign s₁ (x 0)) (foldSign s₂ (x 1)) (fold s₁ s₂ x) = x := by
  rw [fold_eq_refl]
  exact refl_refl (foldSign_eq hs₁ _) (foldSign_eq hs₂ _) x

/-! ### Reflections are automorphisms of both graphs; the fold is a weak homomorphism -/

lemma natAbs_mul_sign {ε a b : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (ε * a - ε * b).natAbs = (a - b).natAbs := by
  rcases hε with rfl | rfl
  · simp
  · rw [show -1 * a - -1 * b = -(a - b) by ring, Int.natAbs_neg]

lemma latticeGraph_adj_refl_iff {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1)
    (x y : Site) :
    (latticeGraph 2).Adj (refl ε₁ ε₂ x) (refl ε₁ ε₂ y) ↔ (latticeGraph 2).Adj x y := by
  rw [latticeGraph_two_adj_iff, latticeGraph_two_adj_iff, refl_zero, refl_zero, refl_one,
    refl_one, natAbs_mul_sign h₁, natAbs_mul_sign h₂]

lemma starLatticeGraph_adj_refl_iff {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 1 ∨ ε₂ = -1) (x y : Site) :
    (starLatticeGraph 2).Adj (refl ε₁ ε₂ x) (refl ε₁ ε₂ y) ↔ (starLatticeGraph 2).Adj x y := by
  rw [starLatticeGraph_two_adj_iff, starLatticeGraph_two_adj_iff, refl_zero, refl_zero, refl_one,
    refl_one, ← mul_sub, ← mul_sub, abs_mul, abs_mul]
  have e₁ : |ε₁| = 1 := by rcases h₁ with rfl | rfl <;> simp
  have e₂ : |ε₂| = 1 := by rcases h₂ with rfl | rfl <;> simp
  rw [e₁, e₂, one_mul, one_mul]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro h hxy; exact h (by rw [hxy])
  · intro h hxy
    apply h
    have := congrArg (refl ε₁ ε₂) hxy
    rwa [refl_refl h₁ h₂, refl_refl h₁ h₂] at this

lemma natAbs_fold_le {s : ℤ} (hs : s = 1 ∨ s = -1) (a b : ℤ) :
    (s * |a| - s * |b|).natAbs ≤ (a - b).natAbs := by
  rw [natAbs_mul_sign hs]
  rcases abs_cases a with ⟨ha, ha'⟩ | ⟨ha, ha'⟩ <;>
    rcases abs_cases b with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
    rw [ha, hb] <;> omega

/-- The fold sends nearest neighbours to equal or nearest-neighbour points. -/
lemma fold_adj_or_eq {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    {x y : Site} (h : (latticeGraph 2).Adj x y) :
    fold s₁ s₂ x = fold s₁ s₂ y ∨ (latticeGraph 2).Adj (fold s₁ s₂ x) (fold s₁ s₂ y) := by
  rw [latticeGraph_two_adj_iff] at h ⊢
  have h0 := natAbs_fold_le hs₁ (x 0) (y 0)
  have h1 := natAbs_fold_le hs₂ (x 1) (y 1)
  simp only [fold_zero', fold_one']
  by_cases heq : (s₁ * |x 0| - s₁ * |y 0|).natAbs + (s₂ * |x 1| - s₂ * |y 1|).natAbs = 0
  · left
    rw [site_ext_iff]
    simp only [fold_zero', fold_one']
    omega
  · right
    omega

/-- The fold sends `*`-neighbours to equal or `*`-neighbouring points. -/
lemma fold_star_adj_or_eq {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    {x y : Site} (h : (starLatticeGraph 2).Adj x y) :
    fold s₁ s₂ x = fold s₁ s₂ y ∨ (starLatticeGraph 2).Adj (fold s₁ s₂ x) (fold s₁ s₂ y) := by
  rw [starLatticeGraph_two_adj_iff] at h ⊢
  by_cases heq : fold s₁ s₂ x = fold s₁ s₂ y
  · exact Or.inl heq
  refine Or.inr ⟨heq, ?_, ?_⟩
  · simp only [fold_zero']
    have := natAbs_fold_le hs₁ (x 0) (y 0)
    have h' := h.2.1
    rw [Int.abs_eq_natAbs] at h' ⊢
    omega
  · simp only [fold_one']
    have := natAbs_fold_le hs₂ (x 1) (y 1)
    have h' := h.2.2
    rw [Int.abs_eq_natAbs] at h' ⊢
    omega

/-! ### The cluster of the origin in the four-fold reflection of `V ∩ Q` -/

/-- The image of the support of the component of `j` in `G.induce s` is the set of points
reachable from `j` inside `s`. -/
lemma image_val_supp_connectedComponentMk_eq {V : Type*} {G : SimpleGraph V} {s : Set V}
    {j : V} (hj : j ∈ s) :
    Subtype.val '' ((G.induce s).connectedComponentMk ⟨j, hj⟩).supp = {k | ReachIn G s j k} := by
  ext k
  constructor
  · rintro ⟨⟨k', hk'⟩, hsupp, rfl⟩
    exact ⟨hj, hk', (SimpleGraph.ConnectedComponent.eq.1 hsupp).symm⟩
  · rintro ⟨hj', hk, hr⟩
    exact ⟨⟨k, hk⟩, SimpleGraph.ConnectedComponent.eq.2 hr.symm, rfl⟩

/-- Reachability from the origin inside `s` is reachability inside the cluster of the origin. -/
lemma reachIn_setOf_reachIn {V : Type*} {G : SimpleGraph V} {s : Set V} {o p : V}
    (h : ReachIn G s o p) : ReachIn G {q | ReachIn G s o q} o p := by
  refine h.induction (P := fun q ↦ ReachIn G {q | ReachIn G s o q} o q)
    (ReachIn.refl (ReachIn.refl h.mem_left)) ?_
  intro a b ha hb hab hPa
  have hb' : b ∈ {q | ReachIn G s o q} :=
    (hPa.mono fun _ hq ↦ hq.mem_right).trans (ReachIn.of_adj ha hb hab)
  exact hPa.trans (ReachIn.of_adj hPa.mem_right hb' hab)

variable {s₁ s₂ : ℤ} {V : Set Site}

/-- Folding a walk from the origin inside `fold⁻¹ V` gives a walk inside `V ∩ Q`. -/
lemma reachIn_fold_of_reachIn_preimage (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    {p : Site} (h : ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p) :
    ReachIn (latticeGraph 2) (V ∩ quadrant s₁ s₂) 0 (fold s₁ s₂ p) := by
  have h0 : (0 : Site) ∈ V ∩ quadrant s₁ s₂ :=
    ⟨by simpa using h.mem_left, zero_mem_quadrant _ _⟩
  refine h.induction
    (P := fun q ↦ ReachIn (latticeGraph 2) (V ∩ quadrant s₁ s₂) 0 (fold s₁ s₂ q))
    (by rw [fold_zero]; exact ReachIn.refl h0) ?_
  intro a b _ hb hab hPa
  have hb' : fold s₁ s₂ b ∈ V ∩ quadrant s₁ s₂ := ⟨hb, fold_mem_quadrant hs₁ hs₂ b⟩
  rcases fold_adj_or_eq hs₁ hs₂ hab with heq | hadj
  · rwa [← heq]
  · exact hPa.trans (ReachIn.of_adj hPa.mem_right hb' hadj)

/-- Reflections preserve reachability from the origin inside `fold⁻¹ V`. -/
lemma reachIn_refl_of_reachIn_preimage {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 1 ∨ ε₂ = -1) {p : Site} (h : ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p) :
    ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 (refl ε₁ ε₂ p) := by
  refine h.induction
    (P := fun q ↦ ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 (refl ε₁ ε₂ q)) ?_ ?_
  · have : refl ε₁ ε₂ 0 = 0 := by rw [site_ext_iff]; simp
    rw [this]
    exact ReachIn.refl h.mem_left
  · intro a b _ hb hab hPa
    have hb' : refl ε₁ ε₂ b ∈ fold s₁ s₂ ⁻¹' V := by
      show fold s₁ s₂ (refl ε₁ ε₂ b) ∈ V
      rw [fold_refl h₁ h₂]
      exact hb
    exact hPa.trans
      (ReachIn.of_adj hPa.mem_right hb' ((latticeGraph_adj_refl_iff h₁ h₂ a b).2 hab))

/-- If the origin is not in an infinite cluster of `V ∩ Q`, then its cluster in the four-fold
reflection `fold⁻¹ V` of `V ∩ Q` is finite. -/
lemma finite_setOf_reachIn_preimage (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (h0 : (0 : Site) ∉ (latticeGraph 2).infiniteClusters (V ∩ quadrant s₁ s₂)) :
    {p | ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p}.Finite := by
  by_cases hV : (0 : Site) ∈ V
  · have h0' : (0 : Site) ∈ V ∩ quadrant s₁ s₂ := ⟨hV, zero_mem_quadrant _ _⟩
    have hfin : {q | ReachIn (latticeGraph 2) (V ∩ quadrant s₁ s₂) 0 q}.Finite := by
      rw [← image_val_supp_connectedComponentMk_eq h0']
      refine Set.Finite.image _ ?_
      rw [SimpleGraph.mem_infiniteClusters_iff_of_mem h0'] at h0
      exact Set.not_infinite.1 h0
    have hsub : {p | ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p} ⊆
        ⋃ ε₁ ∈ ({1, -1} : Set ℤ), ⋃ ε₂ ∈ ({1, -1} : Set ℤ),
          refl ε₁ ε₂ '' {q | ReachIn (latticeGraph 2) (V ∩ quadrant s₁ s₂) 0 q} := by
      intro p hp
      simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff, exists_prop]
      exact ⟨foldSign s₁ (p 0), foldSign_eq hs₁ _, foldSign s₂ (p 1), foldSign_eq hs₂ _,
        fold s₁ s₂ p, reachIn_fold_of_reachIn_preimage hs₁ hs₂ hp, refl_fold_eq_self hs₁ hs₂ p⟩
    refine Set.Finite.subset ?_ hsub
    exact Set.Finite.biUnion (Set.toFinite _) fun ε₁ _ ↦
      Set.Finite.biUnion (Set.toFinite _) fun ε₂ _ ↦ hfin.image _
  · have : {p | ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hp
      exact hV (by simpa using hp.mem_left)
    rw [this]
    exact Set.finite_empty

/-! ### The outer vertex boundary is `*`-connected -/

/-- The outer vertex boundary of `D`: the sites of the infinite outside of `D` adjacent to `D`
(the outside endpoints of the bonds of `outerBoundary D`). -/
def outerVertexBoundary (D : Set Site) : Set Site :=
  {j | j ∈ outside D ∧ ∃ i ∈ D, (latticeGraph 2).Adj i j}

open Classical in
/-- The endpoint of a bond lying in the infinite outside of `D` (junk if there is none). -/
noncomputable def outEnd (D : Set Site) (e : Sym2 Site) : Site :=
  if h : ∃ j ∈ outside D, j ∈ e then h.choose else 0

lemma outEnd_eq {D : Set Site} {i j : Site} (hi : i ∈ D) (hj : j ∈ outside D) :
    outEnd D s(i, j) = j := by
  unfold outEnd
  split_ifs with h
  · obtain ⟨hout, hmem⟩ := h.choose_spec
    rcases Sym2.mem_iff.1 hmem with h' | h'
    · exact absurd hi (notMem_of_mem_outside (h' ▸ hout))
    · exact h'
  · exact absurd ⟨j, hj, Sym2.mem_mk_right i j⟩ h

lemma outEnd_mem {D : Set Site} {e : Sym2 Site} (he : e ∈ outerBoundary D) :
    outEnd D e ∈ e ∧ outEnd D e ∈ outside D := by
  obtain ⟨i, hi, j, hj, -, rfl⟩ := he
  rw [outEnd_eq hi hj]
  exact ⟨Sym2.mem_mk_right i j, hj⟩

lemma image_outEnd_outerBoundary (D : Set Site) :
    outEnd D '' outerBoundary D = outerVertexBoundary D := by
  ext j
  constructor
  · rintro ⟨e, ⟨i, hi, j', hj', hij, rfl⟩, rfl⟩
    rw [outEnd_eq hi hj']
    exact ⟨hj', i, hi, hij⟩
  · rintro ⟨hj, i, hi, hij⟩
    exact ⟨s(i, j), ⟨i, hi, j, hj, hij, rfl⟩, outEnd_eq hi hj⟩

/-- The endpoints of the bonds of the plaquette with lower-left corner `x` are its corners. -/
lemma corner_of_mem_plaquette {x : Site} {e : Sym2 Site} (he : e ∈ plaquette x) {c : Site}
    (hc : c ∈ e) : (c 0 = x 0 ∨ c 0 = x 0 + 1) ∧ (c 1 = x 1 ∨ c 1 = x 1 + 1) := by
  simp only [plaquette, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.1 hc with rfl | rfl <;> simp

/-- Two corners of a plaquette are at sup-distance at most `1`. -/
lemma abs_sub_le_one_of_mem_plaquette {x : Site} {e f : Sym2 Site} (he : e ∈ plaquette x)
    (hf : f ∈ plaquette x) {y z : Site} (hy : y ∈ e) (hz : z ∈ f) :
    |y 0 - z 0| ≤ 1 ∧ |y 1 - z 1| ≤ 1 := by
  obtain ⟨hy0, hy1⟩ := corner_of_mem_plaquette he hy
  obtain ⟨hz0, hz1⟩ := corner_of_mem_plaquette hf hz
  constructor <;> rw [abs_le] <;> omega

/-- **The outer vertex boundary of a finite connected set of sites is `*`-connected**: the
vertex form of Georgii's Lemma (6.14) (`Peierls.outerBoundary_connected`). -/
theorem outerVertexBoundary_connected {D : Set Site} (hD : D.Finite) (hne : D.Nonempty)
    (hconn : ((latticeGraph 2).induce D).Connected) :
    ((starLatticeGraph 2).induce (outerVertexBoundary D)).Connected := by
  rw [← image_outEnd_outerBoundary]
  refine (outerBoundary_connected hD hne hconn).induce_image_of_forall_adj ?_
  intro e f he hf hef
  obtain ⟨-, x, hex, hfx⟩ := hef
  by_cases heq : outEnd D e = outEnd D f
  · exact Or.inl heq
  · refine Or.inr ⟨heq, ?_⟩
    rw [Fin.forall_fin_two]
    exact abs_sub_le_one_of_mem_plaquette hex hfx (outEnd_mem he).1 (outEnd_mem hf).1

/-! ### Boundary points on the two axes -/

/-- A finite set of sites containing the origin has an outer-boundary point on the vertical
axis: the point just above the highest point of `D` on that axis. -/
lemma exists_mem_outerVertexBoundary_vertical {D : Set Site} (hD : D.Finite)
    (h0 : (0 : Site) ∈ D) : ∃ a ∈ outerVertexBoundary D, a 0 = 0 := by
  classical
  set T : Finset ℤ := (hD.toFinset.filter fun x ↦ x 0 = 0).image fun x ↦ x 1 with hT
  have hT0 : (0 : ℤ) ∈ T := by
    rw [hT, Finset.mem_image]
    exact ⟨0, by simp [h0], rfl⟩
  have hTne : T.Nonempty := ⟨0, hT0⟩
  set y := T.max' hTne with hy
  have hyD : mk 0 y ∈ D := by
    have := Finset.max'_mem T hTne
    rw [← hy, hT, Finset.mem_image] at this
    obtain ⟨x, hx, hxy⟩ := this
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hx
    rw [← hx.2, ← hxy, mk_eta]
    exact hx.1
  have hnot : ∀ t, y < t → mk 0 t ∉ D := by
    intro t ht htD
    have : t ∈ T := by
      rw [hT, Finset.mem_image]
      exact ⟨mk 0 t, by simp [htD], by simp⟩
    exact absurd (Finset.le_max' T t this) (not_le.2 ht)
  refine ⟨mk 0 (y + 1), ⟨?_, mk 0 y, hyD, adj_mk_vert 0 y⟩, by simp⟩
  rw [mem_outside_iff]
  refine ⟨hnot _ (by omega), ?_⟩
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ mk 0 (y + 1 + n)) ?_ ?_
  · intro m n hmn
    have := congrArg (fun z ↦ z 1) hmn
    simp only [mk_one] at this
    omega
  · intro n
    refine reachIn_vertical Dᶜ 0 (y + 1) (y + 1 + n) fun t ht₁ ht₂ ↦ hnot t ?_
    simp only [min_le_iff] at ht₁
    omega

/-- A finite set of sites containing the origin has an outer-boundary point on the horizontal
axis: the point just to the right of the rightmost point of `D` on that axis. -/
lemma exists_mem_outerVertexBoundary_horizontal {D : Set Site} (hD : D.Finite)
    (h0 : (0 : Site) ∈ D) : ∃ b ∈ outerVertexBoundary D, b 1 = 0 := by
  classical
  set T : Finset ℤ := (hD.toFinset.filter fun x ↦ x 1 = 0).image fun x ↦ x 0 with hT
  have hT0 : (0 : ℤ) ∈ T := by
    rw [hT, Finset.mem_image]
    exact ⟨0, by simp [h0], rfl⟩
  have hTne : T.Nonempty := ⟨0, hT0⟩
  set y := T.max' hTne with hy
  have hyD : mk y 0 ∈ D := by
    have := Finset.max'_mem T hTne
    rw [← hy, hT, Finset.mem_image] at this
    obtain ⟨x, hx, hxy⟩ := this
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hx
    rw [← hx.2, ← hxy, mk_eta]
    exact hx.1
  have hnot : ∀ t, y < t → mk t 0 ∉ D := by
    intro t ht htD
    have : t ∈ T := by
      rw [hT, Finset.mem_image]
      exact ⟨mk t 0, by simp [htD], by simp⟩
    exact absurd (Finset.le_max' T t this) (not_le.2 ht)
  refine ⟨mk (y + 1) 0, ⟨?_, mk y 0, hyD, adj_mk_horiz y 0⟩, by simp⟩
  rw [mem_outside_iff]
  refine ⟨hnot _ (by omega), ?_⟩
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ mk (y + 1 + n) 0) ?_ ?_
  · intro m n hmn
    have := congrArg (fun z ↦ z 0) hmn
    simp only [mk_zero] at this
    omega
  · intro n
    refine reachIn_horizontal Dᶜ (y + 1) (y + 1 + n) 0 fun t ht₁ ht₂ ↦ hnot t ?_
    simp only [min_le_iff] at ht₁
    omega

/-! ### The `*`-crossing of a quadrant -/

/-- Georgii, proof of (18.14), properties (i)–(iii): `L` is the vertex list of a self-avoiding
`*`-path in `quadrant s₁ s₂` starting on the vertical half-axis `{x₀ = 0}`, ending on the
horizontal half-axis `{x₁ = 0}`, and without shortcuts (`|u⁽ᵏ⁾ - u⁽ᵏ⁺²⁾| > √2`). -/
structure IsStarCrossing (s₁ s₂ : ℤ) (L : List Site) : Prop where
  /-- The crossing is nonempty. -/
  ne_nil : L ≠ []
  /-- The crossing lies in the quadrant. -/
  mem_quadrant : ∀ x ∈ L, x ∈ quadrant s₁ s₂
  /-- The crossing starts on the vertical half-axis. -/
  head_zero : ∀ h : L ≠ [], L.head h 0 = 0
  /-- The crossing ends on the horizontal half-axis. -/
  getLast_one : ∀ h : L ≠ [], L.getLast h 1 = 0
  /-- Consecutive points are `*`-neighbours. -/
  isChain : L.IsChain (starLatticeGraph 2).Adj
  /-- No shortcuts: points two apart are neither equal nor `*`-neighbours. -/
  noShortcut : (starLatticeGraph 2).NoShortcut L
  /-- The crossing is self-avoiding. -/
  nodup : L.Nodup

/-- The folded outer vertex boundary of the cluster of the origin in `fold⁻¹ V` avoids `V`. -/
lemma fold_notMem_of_mem_outerVertexBoundary (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) {j : Site}
    (hj : j ∈ outerVertexBoundary {p | ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p}) :
    fold s₁ s₂ j ∉ V := by
  obtain ⟨hout, i, hi, hij⟩ := hj
  intro hjV
  apply notMem_of_mem_outside hout
  have hε₁ := foldSign_eq hs₁ (j 0)
  have hε₂ := foldSign_eq hs₂ (j 1)
  have hfold : fold s₁ s₂ j ∈ fold s₁ s₂ ⁻¹' V := by
    show fold s₁ s₂ (fold s₁ s₂ j) ∈ V
    rwa [fold_eq_self_of_mem_quadrant hs₁ hs₂ (fold_mem_quadrant hs₁ hs₂ j)]
  have hi' := reachIn_refl_of_reachIn_preimage hε₁ hε₂ hi
  have hadj : (latticeGraph 2).Adj (refl (foldSign s₁ (j 0)) (foldSign s₂ (j 1)) i)
      (fold s₁ s₂ j) := by
    rw [fold_eq_refl]
    exact (latticeGraph_adj_refl_iff hε₁ hε₂ i j).2 hij
  have hfj : ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 (fold s₁ s₂ j) :=
    hi'.trans (ReachIn.of_adj hi'.mem_right hfold hadj)
  have := reachIn_refl_of_reachIn_preimage hε₁ hε₂ hfj
  rwa [refl_fold_eq_self hs₁ hs₂] at this

/-- **Planar duality in a quadrant** (Georgii, proof of (18.14)): if the origin is not in an
infinite cluster of `V ∩ Q`, then some `*`-crossing of the quadrant `Q` avoids `V`. -/
theorem exists_isStarCrossing_of_notMem_infiniteClusters (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) (V : Set Site)
    (h0 : (0 : Site) ∉ (latticeGraph 2).infiniteClusters (V ∩ quadrant s₁ s₂)) :
    ∃ L : List Site, IsStarCrossing s₁ s₂ L ∧ ∀ x ∈ L, x ∉ V := by
  by_cases hV : (0 : Site) ∈ V
  swap
  · exact ⟨[0], ⟨by simp, by simpa using zero_mem_quadrant s₁ s₂, by simp, by simp, by simp,
      by simp, by simp⟩, by simpa using hV⟩
  set ξ := {p | ReachIn (latticeGraph 2) (fold s₁ s₂ ⁻¹' V) 0 p} with hξ
  have h0ξ : (0 : Site) ∈ ξ := ReachIn.refl (by simpa using hV)
  have hξfin : ξ.Finite := finite_setOf_reachIn_preimage hs₁ hs₂ h0
  have hξconn : ((latticeGraph 2).induce ξ).Connected := by
    rw [induce_connected_iff]
    exact ⟨⟨0, h0ξ⟩, fun u v hu hv ↦ (reachIn_setOf_reachIn hu).symm.trans
      (reachIn_setOf_reachIn hv)⟩
  set O := outerVertexBoundary ξ with hO
  have hOconn := outerVertexBoundary_connected hξfin ⟨0, h0ξ⟩ hξconn
  obtain ⟨a, ha, ha0⟩ := exists_mem_outerVertexBoundary_vertical hξfin h0ξ
  obtain ⟨b, hb, hb1⟩ := exists_mem_outerVertexBoundary_horizontal hξfin h0ξ
  -- fold the boundary into the quadrant
  have hfold : ((starLatticeGraph 2).induce (fold s₁ s₂ '' O)).Connected :=
    hOconn.induce_image_of_forall_adj fun x y _ _ hxy ↦ fold_star_adj_or_eq hs₁ hs₂ hxy
  have hreach := hfold.preconnected ⟨fold s₁ s₂ a, a, ha, rfl⟩ ⟨fold s₁ s₂ b, b, hb, rfl⟩
  obtain ⟨p, hp, hplen⟩ := hreach.exists_path_of_dist
  have hmin : ∀ q : ((starLatticeGraph 2).induce (fold s₁ s₂ '' O)).Walk
      ⟨fold s₁ s₂ a, a, ha, rfl⟩ ⟨fold s₁ s₂ b, b, hb, rfl⟩, p.length ≤ q.length :=
    fun q ↦ hplen ▸ SimpleGraph.dist_le q
  refine ⟨p.support.map Subtype.val, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨⟨_, y, -, rfl⟩, -, rfl⟩ := hx
    exact fold_mem_quadrant hs₁ hs₂ y
  · intro h
    rw [List.head_map, SimpleGraph.Walk.head_support]
    simp [ha0]
  · intro h
    rw [List.getLast_map, SimpleGraph.Walk.getLast_support]
    simp [hb1]
  · exact List.isChain_map_of_isChain (S := (starLatticeGraph 2).Adj) Subtype.val
      (fun _ _ h ↦ h) p.isChain_adj_support
  · exact SimpleGraph.noShortcut_map_of_injective Subtype.val_injective (fun _ _ h ↦ h)
      (SimpleGraph.noShortcut_support_of_forall_length_le p hmin)
  · exact hp.support_nodup.map Subtype.val_injective
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨⟨_, y, hy, rfl⟩, -, rfl⟩ := hx
    exact fold_notMem_of_mem_outerVertexBoundary hs₁ hs₂ hy

/-! ### Counting the crossings: at most `ℓ · 5 ^ (ℓ - 1)` of length `ℓ` -/

/-- The eight `*`-offsets in `ℤ²`. -/
def starOffsets : Finset (ℤ × ℤ) :=
  (({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ)).erase (0, 0)

/-- The offset `δ` shifts `x` to `x + δ`. -/
def shiftBy (x : Site) (δ : ℤ × ℤ) : Site := mk (x 0 + δ.1) (x 1 + δ.2)

@[simp] lemma shiftBy_zero (x : Site) (δ : ℤ × ℤ) : shiftBy x δ 0 = x 0 + δ.1 := by simp [shiftBy]

@[simp] lemma shiftBy_one (x : Site) (δ : ℤ × ℤ) : shiftBy x δ 1 = x 1 + δ.2 := by simp [shiftBy]

/-- The `*`-neighbours of `x`. -/
def starNbrs (x : Site) : Finset Site := starOffsets.image (shiftBy x)

lemma mem_starOffsets {δ : ℤ × ℤ} :
    δ ∈ starOffsets ↔ δ ≠ (0, 0) ∧ (δ.1 = -1 ∨ δ.1 = 0 ∨ δ.1 = 1) ∧
      (δ.2 = -1 ∨ δ.2 = 0 ∨ δ.2 = 1) := by
  simp [starOffsets]

lemma mem_starNbrs_iff_adj {x y : Site} : y ∈ starNbrs x ↔ (starLatticeGraph 2).Adj y x := by
  rw [starLatticeGraph_two_adj_iff, starNbrs, Finset.mem_image]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    rw [mem_starOffsets] at hδ
    obtain ⟨hne, h1, h2⟩ := hδ
    refine ⟨fun h ↦ hne ?_, ?_, ?_⟩
    · have h0 := congrArg (fun z ↦ z 0) h
      have h1' := congrArg (fun z ↦ z 1) h
      simp only [shiftBy_zero, shiftBy_one] at h0 h1'
      exact Prod.ext (by omega) (by omega)
    · simp only [shiftBy_zero, abs_le]; omega
    · simp only [shiftBy_one, abs_le]; omega
  · rintro ⟨hne, h0, h1⟩
    refine ⟨(y 0 - x 0, y 1 - x 1), ?_, by rw [site_ext_iff]; simp⟩
    rw [mem_starOffsets]
    refine ⟨fun h ↦ hne ?_, ?_, ?_⟩
    · rw [Prod.mk.injEq] at h
      rw [site_ext_iff]; omega
    · rw [abs_le] at h0; omega
    · rw [abs_le] at h1; omega

instance decidableMemQuadrant (s₁ s₂ : ℤ) : DecidablePred (· ∈ quadrant s₁ s₂) := fun x ↦
  inferInstanceAs (Decidable (0 ≤ s₁ * x 0 ∧ 0 ≤ s₂ * x 1))

/-- The `*`-neighbours of `b` in the quadrant which are not within sup-distance `1` of `c`: the
candidates for the predecessor of `b` in a crossing `… , w, b, c, …` without shortcuts. -/
def prevCandidates (s₁ s₂ : ℤ) (b c : Site) : Finset Site :=
  ((starNbrs b).filter (· ∈ quadrant s₁ s₂)).filter fun w ↦ ¬ (|w 0 - c 0| ≤ 1 ∧ |w 1 - c 1| ≤ 1)

/-- The candidates for the point preceding a partial crossing `L`. -/
def prevSet (s₁ s₂ : ℤ) : List Site → Finset Site
  | [] => ∅
  | [b] => (starNbrs b).filter (· ∈ quadrant s₁ s₂)
  | b :: c :: _ => prevCandidates s₁ s₂ b c

/-- The possible end points `(s₁ a, 0)`, `0 ≤ a < ℓ`, of a crossing of length `ℓ`. -/
def endPoints (s₁ : ℤ) (ℓ : ℕ) : Finset Site := (Finset.range ℓ).image fun a : ℕ ↦ mk (s₁ * a) 0

/-- The partial crossings of length `k` of a crossing of length `ℓ`, built backwards from the
end point on the horizontal half-axis. -/
def starCrossingsAux (s₁ s₂ : ℤ) (ℓ : ℕ) : ℕ → Finset (List Site)
  | 0 => ∅
  | 1 => (endPoints s₁ ℓ).image fun b ↦ [b]
  | k + 2 => (starCrossingsAux s₁ s₂ ℓ (k + 1)).biUnion fun L ↦ (prevSet s₁ s₂ L).image (· :: L)

/-- A finite set of lists containing every `*`-crossing of length `ℓ`
(`mem_starCrossings_of_isStarCrossing`), of cardinality at most `ℓ · 5 ^ (ℓ - 1)`
(`card_starCrossings_le`): Georgii's count in the proof of (18.14). -/
def starCrossings (s₁ s₂ : ℤ) (ℓ : ℕ) : Finset (List Site) := starCrossingsAux s₁ s₂ ℓ ℓ

lemma card_filter_starNbrs_le (hs₂ : s₂ = 1 ∨ s₂ = -1) {b : Site} (hb : b 1 = 0) :
    ((starNbrs b).filter (· ∈ quadrant s₁ s₂)).card ≤ 5 := by
  have hsub : (starNbrs b).filter (· ∈ quadrant s₁ s₂) ⊆
      (starOffsets.filter fun δ ↦ 0 ≤ s₂ * δ.2).image (shiftBy b) := by
    intro w hw
    rw [Finset.mem_filter, starNbrs, Finset.mem_image] at hw
    obtain ⟨⟨δ, hδ, rfl⟩, hQ⟩ := hw
    refine Finset.mem_image.2 ⟨δ, Finset.mem_filter.2 ⟨hδ, ?_⟩, rfl⟩
    have := hQ.2
    rw [shiftBy_one, hb, zero_add] at this
    exact this
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rcases hs₂ with rfl | rfl <;> decide

/-- Of the eight `*`-offsets, at most five are at sup-distance at least `2` from a given
`*`-offset `ε`. -/
lemma card_filter_starOffsets_le : ∀ ε ∈ starOffsets,
    (starOffsets.filter fun δ ↦ ¬ (|δ.1 - ε.1| ≤ 1 ∧ |δ.2 - ε.2| ≤ 1)).card ≤ 5 := by
  decide

lemma sub_mem_starOffsets_of_adj {b c : Site} (hbc : (starLatticeGraph 2).Adj b c) :
    (c 0 - b 0, c 1 - b 1) ∈ starOffsets := by
  rw [starLatticeGraph_two_adj_iff] at hbc
  obtain ⟨hne, h0, h1⟩ := hbc
  rw [mem_starOffsets]
  refine ⟨fun h ↦ hne ?_, ?_, ?_⟩
  · rw [Prod.mk.injEq] at h
    rw [site_ext_iff]
    omega
  · rw [abs_le] at h0
    omega
  · rw [abs_le] at h1
    omega

lemma prevCandidates_subset (s₁ s₂ : ℤ) (b c : Site) :
    prevCandidates s₁ s₂ b c ⊆
      (starOffsets.filter fun δ ↦
        ¬ (|δ.1 - (c 0 - b 0)| ≤ 1 ∧ |δ.2 - (c 1 - b 1)| ≤ 1)).image (shiftBy b) := by
  intro w hw
  rw [prevCandidates, Finset.mem_filter, Finset.mem_filter, starNbrs, Finset.mem_image] at hw
  obtain ⟨⟨⟨δ, hδ, rfl⟩, -⟩, hfar⟩ := hw
  refine Finset.mem_image.2 ⟨δ, Finset.mem_filter.2 ⟨hδ, ?_⟩, rfl⟩
  rw [shiftBy_zero, shiftBy_one] at hfar
  have e1 : δ.1 - (c 0 - b 0) = b 0 + δ.1 - c 0 := by ring
  have e2 : δ.2 - (c 1 - b 1) = b 1 + δ.2 - c 1 := by ring
  rw [e1, e2]
  exact hfar

/-- At most five `*`-offsets can precede `b` in a crossing `…, w, b, c, …` without shortcuts.

The pair `ε` is passed explicitly: leaving it to unification forces the elaborator to solve
`?ε.1 =?= c 0 - b 0`, which it postpones and then attempts by unfolding `starOffsets`. -/
lemma card_prevCandidates_le (s₁ s₂ : ℤ) {b c : Site} (hbc : (starLatticeGraph 2).Adj b c) :
    (prevCandidates s₁ s₂ b c).card ≤ 5 :=
  (Finset.card_le_card (prevCandidates_subset s₁ s₂ b c)).trans
    (Finset.card_image_le.trans
      (card_filter_starOffsets_le (c 0 - b 0, c 1 - b 1) (sub_mem_starOffsets_of_adj hbc)))

/-- The invariant of the partial crossings: nonempty, with the end point on the horizontal
half-axis and consecutive points `*`-adjacent. -/
def AuxInv : List Site → Prop
  | [] => False
  | [b] => b 1 = 0
  | b :: c :: _ => (starLatticeGraph 2).Adj b c

lemma auxInv_of_mem_starCrossingsAux (s₁ s₂ : ℤ) (ℓ : ℕ) :
    ∀ k, ∀ L ∈ starCrossingsAux s₁ s₂ ℓ (k + 1), AuxInv L
  | 0, L, hL => by
    simp only [starCrossingsAux, Finset.mem_image] at hL
    obtain ⟨b, hb, rfl⟩ := hL
    simp only [endPoints, Finset.mem_image] at hb
    obtain ⟨a, -, rfl⟩ := hb
    simp [AuxInv]
  | k + 1, L, hL => by
    simp only [starCrossingsAux, Finset.mem_biUnion, Finset.mem_image] at hL
    obtain ⟨L', hL', a, ha, rfl⟩ := hL
    have hinv := auxInv_of_mem_starCrossingsAux s₁ s₂ ℓ k L' hL'
    match L', ha, hinv with
    | [], _, hinv => exact hinv.elim
    | [b], ha, _ =>
      simp only [prevSet, Finset.mem_filter] at ha
      exact mem_starNbrs_iff_adj.1 ha.1
    | b :: c :: rest, ha, _ =>
      simp only [prevSet, prevCandidates, Finset.mem_filter] at ha
      exact mem_starNbrs_iff_adj.1 ha.1.1

lemma card_prevSet_le (hs₂ : s₂ = 1 ∨ s₂ = -1) {L : List Site} (hL : AuxInv L) :
    (prevSet s₁ s₂ L).card ≤ 5 := by
  match L, hL with
  | [], hL => exact hL.elim
  | [b], hL => exact card_filter_starNbrs_le hs₂ hL
  | b :: c :: rest, hL => exact card_prevCandidates_le s₁ s₂ hL

/-- There are at most `ℓ · 5 ^ k` partial crossings of length `k + 1`. -/
lemma card_starCrossingsAux_le (hs₂ : s₂ = 1 ∨ s₂ = -1) (ℓ : ℕ) :
    ∀ k, (starCrossingsAux s₁ s₂ ℓ (k + 1)).card ≤ ℓ * 5 ^ k
  | 0 => by
    simp only [starCrossingsAux, pow_zero, mul_one]
    exact Finset.card_image_le.trans (Finset.card_image_le.trans (by simp))
  | k + 1 => by
    simp only [starCrossingsAux]
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ L ∈ starCrossingsAux s₁ s₂ ℓ (k + 1), ((prevSet s₁ s₂ L).image (· :: L)).card
        ≤ ∑ L ∈ starCrossingsAux s₁ s₂ ℓ (k + 1), 5 := by
          refine Finset.sum_le_sum fun L hL ↦ Finset.card_image_le.trans ?_
          exact card_prevSet_le hs₂ (auxInv_of_mem_starCrossingsAux s₁ s₂ ℓ k L hL)
      _ = (starCrossingsAux s₁ s₂ ℓ (k + 1)).card * 5 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ℓ * 5 ^ k * 5 := by
          exact Nat.mul_le_mul_right 5 (card_starCrossingsAux_le hs₂ ℓ k)
      _ = ℓ * 5 ^ (k + 1) := by ring

/-- **Georgii's count in the proof of (18.14)**: at most `ℓ · 5 ^ (ℓ - 1)` crossings of length
`ℓ ≥ 1`. -/
theorem card_starCrossings_le (hs₂ : s₂ = 1 ∨ s₂ = -1) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (starCrossings s₁ s₂ ℓ).card ≤ ℓ * 5 ^ (ℓ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simpa [starCrossings] using card_starCrossingsAux_le hs₂ (k + 1) k

/-- Along a `*`-chain, coordinates move by at most `1` per step. -/
lemma abs_sub_head_le_of_isChain (i : Fin 2) :
    ∀ (L : List Site) (h : L ≠ []), L.IsChain (starLatticeGraph 2).Adj →
      ∀ x ∈ L, |x i - L.head h i| ≤ L.length - 1
  | [], h, _, _, _ => absurd rfl h
  | [a], _, _, x, hx => by
    simp only [List.mem_singleton] at hx
    subst hx
    simp
  | a :: b :: rest, _, hchain, x, hx => by
    rw [List.isChain_cons_cons] at hchain
    obtain ⟨hab, hchain⟩ := hchain
    have hab' : |a i - b i| ≤ 1 := (starLatticeGraph_adj.1 hab).2 i
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have : (0 : ℤ) ≤ (rest.length : ℤ) := Int.natCast_nonneg _
      simp only [List.head_cons, sub_self, abs_zero, List.length_cons]
      push_cast
      linarith
    · have := abs_sub_head_le_of_isChain i (b :: rest) (by simp) hchain x (by simpa using hx)
      simp only [List.head_cons, List.length_cons] at this ⊢
      have h3 := abs_sub_le (x i) (b i) (a i)
      rw [abs_sub_comm (b i)] at h3
      push_cast at this ⊢
      linarith

/-- Every `*`-crossing of length `ℓ` lies in the finite set `starCrossings s₁ s₂ ℓ`. -/
theorem mem_starCrossings_of_isStarCrossing (hs₁ : s₁ = 1 ∨ s₁ = -1) {L : List Site}
    (hL : IsStarCrossing s₁ s₂ L) : L ∈ starCrossings s₁ s₂ L.length := by
  have hlast : ∀ h : L ≠ [], |L.getLast h 0| < L.length := by
    intro h
    have := abs_sub_head_le_of_isChain 0 L h hL.isChain (L.getLast h) (List.getLast_mem h)
    rw [hL.head_zero h, sub_zero] at this
    have hpos : 0 < L.length := List.length_pos_of_ne_nil h
    have : (|L.getLast h 0| : ℤ) ≤ (L.length : ℤ) - 1 := by exact_mod_cast this
    omega
  suffices key : ∀ (M : List Site) (hM : M ≠ []), (∀ x ∈ M, x ∈ quadrant s₁ s₂) →
      M.IsChain (starLatticeGraph 2).Adj → (starLatticeGraph 2).NoShortcut M →
      M.getLast hM 1 = 0 → |M.getLast hM 0| < L.length →
      M ∈ starCrossingsAux s₁ s₂ L.length M.length from
    key L hL.ne_nil hL.mem_quadrant hL.isChain hL.noShortcut (hL.getLast_one _) (hlast _)
  intro M
  induction M with
  | nil => exact fun h ↦ absurd rfl h
  | cons a M ih =>
    intro hM hQ hchain hns hlast1 hlast0
    cases M with
    | nil =>
      simp only [List.getLast_singleton] at hlast1 hlast0
      rw [List.length_singleton]
      simp only [starCrossingsAux]
      have haQ := hQ a (List.mem_singleton_self a)
      rw [mem_quadrant] at haQ
      refine Finset.mem_image.2 ⟨a, ?_, rfl⟩
      refine Finset.mem_image.2 ⟨(s₁ * a 0).toNat, Finset.mem_range.2 ?_, ?_⟩
      · rw [abs_lt] at hlast0
        obtain ⟨hl₁, hl₂⟩ := hlast0
        obtain ⟨hq₁, -⟩ := haQ
        rcases hs₁ with rfl | rfl <;> omega
      · rw [site_ext_iff, mk_zero, mk_one, hlast1]
        refine ⟨?_, rfl⟩
        rw [Int.toNat_of_nonneg haQ.1]
        rcases hs₁ with rfl | rfl <;> ring
    | cons b M =>
      have hM' : b :: M ≠ [] := by simp
      have ih' := ih hM' (fun x hx ↦ hQ x (List.mem_cons_of_mem a hx))
        (List.isChain_cons_cons.1 hchain).2 ?_
        (by rw [← List.getLast_cons hM']; exact hlast1)
        (by rw [← List.getLast_cons hM']; exact hlast0)
      · simp only [List.length_cons, starCrossingsAux]
        refine Finset.mem_biUnion.2 ⟨b :: M, ih', Finset.mem_image.2 ⟨a, ?_, rfl⟩⟩
        have hab : (starLatticeGraph 2).Adj a b := (List.isChain_cons_cons.1 hchain).1
        have haQ := hQ a (List.mem_cons_self ..)
        cases M with
        | nil =>
          simp only [prevSet, Finset.mem_filter]
          exact ⟨mem_starNbrs_iff_adj.2 hab, haQ⟩
        | cons c M =>
          simp only [prevSet, prevCandidates, Finset.mem_filter]
          refine ⟨⟨mem_starNbrs_iff_adj.2 hab, haQ⟩, fun hnear ↦ ?_⟩
          have hns' := (SimpleGraph.noShortcut_cons_cons_cons.1 hns).1
          apply hns'
          by_cases hac : a = c
          · exact Or.inl hac
          · exact Or.inr ((starLatticeGraph_two_adj_iff a c).2 ⟨hac, hnear.1, hnear.2⟩)
      · match M, hns with
        | [], _ => trivial
        | c :: M, hns => exact (SimpleGraph.noShortcut_cons_cons_cons.1 hns).2

/-! ### Georgii (18.13), (18.14): the origin percolates in every quadrant -/

open scoped ENNReal

/-- **Georgii (18.13)**: `z(t) = 1 ∧ ∑_{ℓ ≥ 1} ℓ (5t)^ℓ / 5`.

The `ℓ`-th summand `ℓ · 5^{ℓ-1} · t^ℓ` is the bound `card_starCrossings_le` for the number of
`*`-crossings of a quadrant of length `ℓ` times the bound `t^ℓ` for the probability that a
given one of them avoids the pattern.  The summand vanishes at `ℓ = 0`, so the sum below is
Georgii's sum over `ℓ ≥ 1`. -/
noncomputable def crossingBound (t : ℝ≥0∞) : ℝ≥0∞ :=
  1 ⊓ ∑' ℓ : ℕ, ((ℓ * 5 ^ (ℓ - 1) : ℕ) : ℝ≥0∞) * t ^ ℓ

lemma crossingBound_le_one (t : ℝ≥0∞) : crossingBound t ≤ 1 := inf_le_left

lemma crossingBound_le_tsum (t : ℝ≥0∞) :
    crossingBound t ≤ ∑' ℓ : ℕ, ((ℓ * 5 ^ (ℓ - 1) : ℕ) : ℝ≥0∞) * t ^ ℓ := inf_le_right

lemma succ_mul_five_pow_le (k : ℕ) : (k + 1) * 5 ^ k ≤ 2 * 10 ^ k := by
  have h1 : k + 1 ≤ 2 * 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    omega
  calc (k + 1) * 5 ^ k ≤ 2 * 2 ^ k * 5 ^ k := Nat.mul_le_mul_right _ h1
    _ = 2 * (2 * 5) ^ k := by rw [mul_pow]; ring
    _ = 2 * 10 ^ k := by norm_num

/-- Georgii's `z(t) → 0` as `t → 0`, quantitatively: `z(t) ≤ 4t` for `t ≤ 1/20`. -/
lemma crossingBound_le_four_mul {t : ℝ≥0∞} (ht : t ≤ 20⁻¹) : crossingBound t ≤ 4 * t := by
  have h10 : 10 * t ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le]
    have h : (10 : ℝ≥0∞) * t * 2 = 20 * t := by ring
    rw [h]
    calc (20 : ℝ≥0∞) * t ≤ 20 * 20⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hterm : ∀ k : ℕ, (((k + 1) * 5 ^ (k + 1 - 1) : ℕ) : ℝ≥0∞) * t ^ (k + 1)
      ≤ 2 * t * ((2 : ℝ≥0∞)⁻¹) ^ k := by
    intro k
    have hcast : (((k + 1) * 5 ^ (k + 1 - 1) : ℕ) : ℝ≥0∞) ≤ ((2 * 10 ^ k : ℕ) : ℝ≥0∞) := by
      rw [Nat.add_sub_cancel]
      exact Nat.cast_le.2 (succ_mul_five_pow_le k)
    calc (((k + 1) * 5 ^ (k + 1 - 1) : ℕ) : ℝ≥0∞) * t ^ (k + 1)
        ≤ ((2 * 10 ^ k : ℕ) : ℝ≥0∞) * t ^ (k + 1) := mul_le_mul_left hcast _
      _ = 2 * t * ((10 : ℝ≥0∞) * t) ^ k := by push_cast; rw [mul_pow]; ring
      _ ≤ 2 * t * ((2 : ℝ≥0∞)⁻¹) ^ k := mul_le_mul_right (pow_le_pow_left' h10 k) _
  have hsum : ∑' k : ℕ, 2 * t * ((2 : ℝ≥0∞)⁻¹) ^ k = 4 * t := by
    have h1 : ∑' k : ℕ, 2 * t * ((2 : ℝ≥0∞)⁻¹) ^ k
        = 2 * t * ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ k := ENNReal.tsum_mul_left
    rw [h1, ENNReal.tsum_geometric_two]
    ring
  refine (crossingBound_le_tsum t).trans ?_
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hzero : ((0 * 5 ^ (0 - 1) : ℕ) : ℝ≥0∞) * t ^ 0 = 0 := by simp
  rw [hzero, zero_add, ← hsum]
  exact ENNReal.tsum_le_tsum hterm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Georgii, Lemma (18.14)**, the estimate behind it.  Let `W : Ω → Set Site` be a random
subset of the plane such that a finite set `D` is disjoint from `W` with probability at most
`t ^ |D|`.  Then the origin fails to lie in an infinite cluster of `W ∩ Q`, for `Q` a quadrant
with vertex `0`, with probability at most `∑_{ℓ ≥ 1} ℓ 5^{ℓ-1} t^ℓ`.

No measurability of `W` is used: the bound is countable subadditivity over the `*`-crossings of
`Q` (`exists_isStarCrossing_of_notMem_infiniteClusters`, `mem_starCrossings_of_isStarCrossing`,
`card_starCrossings_le`). -/
theorem measure_notMem_infiniteClusters_le (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (μ : Measure Ω) (W : Ω → Set Site) {t : ℝ≥0∞}
    (ht : ∀ D : Finset Site, μ {ω | ∀ i ∈ D, i ∉ W ω} ≤ t ^ D.card) :
    μ {ω | (0 : Site) ∉ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)}
      ≤ ∑' ℓ : ℕ, ((ℓ * 5 ^ (ℓ - 1) : ℕ) : ℝ≥0∞) * t ^ ℓ := by
  classical
  set C : ℕ → Finset (List Site) := fun ℓ ↦
    (starCrossings s₁ s₂ ℓ).filter fun L ↦ L.Nodup ∧ L.length = ℓ with hCdef
  have hcover : {ω | (0 : Site) ∉ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)} ⊆
      ⋃ ℓ : ℕ, ⋃ L ∈ C ℓ, {ω | ∀ i ∈ L, i ∉ W ω} := by
    intro ω hω
    obtain ⟨L, hL, hLW⟩ := exists_isStarCrossing_of_notMem_infiniteClusters hs₁ hs₂ (W ω) hω
    refine Set.mem_iUnion.2 ⟨L.length, Set.mem_iUnion₂.2 ⟨L, ?_, hLW⟩⟩
    exact Finset.mem_filter.2 ⟨mem_starCrossings_of_isStarCrossing hs₁ hL, hL.nodup, rfl⟩
  refine (measure_mono hcover).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum ?_))
  intro ℓ
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ L ∈ C ℓ, μ {ω | ∀ i ∈ L, i ∉ W ω} ≤ t ^ ℓ := by
    intro L hL
    obtain ⟨-, hnodup, hlen⟩ := Finset.mem_filter.1 hL
    have h := ht L.toFinset
    rw [List.toFinset_card_of_nodup hnodup, hlen] at h
    refine le_trans (le_of_eq ?_) h
    congr 1
    ext ω
    simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  gcongr
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · simp [hCdef, starCrossings, starCrossingsAux]
  · exact_mod_cast (Finset.card_filter_le _ _).trans (card_starCrossings_le hs₂ hℓ)

/-- **Georgii, Lemma (18.14)**: if a finite set `D` is disjoint from the random set `W` with
probability at most `t ^ |D|`, then the origin lies in an infinite cluster of `W ∩ Q` with
probability at least `1 - z(t)`, for each of the four quadrants `Q` with vertex `0`. -/
theorem le_measure_mem_infiniteClusters (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Set Site) {t : ℝ≥0∞}
    (ht : ∀ D : Finset Site, μ {ω | ∀ i ∈ D, i ∉ W ω} ≤ t ^ D.card) :
    1 - crossingBound t
      ≤ μ {ω | (0 : Site) ∈ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)} := by
  set good := {ω | (0 : Site) ∈ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)}
  set bad := {ω | (0 : Site) ∉ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)}
  have hbad : μ bad ≤ crossingBound t :=
    le_inf prob_le_one (measure_notMem_infiniteClusters_le hs₁ hs₂ μ W ht)
  have hcov : (Set.univ : Set Ω) ⊆ good ∪ bad := fun ω _ ↦ by
    by_cases h : (0 : Site) ∈ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)
    · exact Or.inl h
    · exact Or.inr h
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
    _ ≤ μ (good ∪ bad) := measure_mono hcov
    _ ≤ μ good + μ bad := measure_union_le _ _
    _ ≤ μ good + crossingBound t := by gcongr

/-- **Georgii, proof of Lemma (18.16), first step**: `μ(X) ≥ 1 - 4z(t)`, where `X` is the event
that the origin is the centre of an infinite cross, i.e. lies in an infinite cluster of `W ∩ Q`
for each of the four quadrants `Q` with vertex `0`. -/
theorem le_measure_forall_mem_infiniteClusters (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Set Site) {t : ℝ≥0∞}
    (ht : ∀ D : Finset Site, μ {ω | ∀ i ∈ D, i ∉ W ω} ≤ t ^ D.card) :
    1 - 4 * crossingBound t ≤
      μ {ω | ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
        (0 : Site) ∈ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)} := by
  classical
  set good := {ω | ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
    (0 : Site) ∈ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant s₁ s₂)} with hgood
  set P : ℤ × ℤ → Set Ω := fun p ↦
    {ω | (0 : Site) ∉ (latticeGraph 2).infiniteClusters (W ω ∩ quadrant p.1 p.2)} with hP
  set Signs : Finset (ℤ × ℤ) := ({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ) with hSigns
  have hbad : μ (⋃ p ∈ Signs, P p) ≤ 4 * crossingBound t := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ p ∈ Signs, μ (P p) ≤ crossingBound t := by
      intro p hp
      rw [hSigns, Finset.mem_product] at hp
      have h1 : p.1 = 1 ∨ p.1 = -1 := by simpa using hp.1
      have h2 : p.2 = 1 ∨ p.2 = -1 := by simpa using hp.2
      exact le_inf prob_le_one (measure_notMem_infiniteClusters_le h1 h2 μ W ht)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : Signs.card = 4 := by rw [hSigns]; decide
    rw [hcard]
    norm_num
  have hcov : (Set.univ : Set Ω) ⊆ good ∪ ⋃ p ∈ Signs, P p := by
    intro ω _
    by_cases h : ω ∈ good
    · exact Or.inl h
    · rw [hgood, Set.mem_ofPred_eq] at h
      push Not at h
      obtain ⟨s₁, s₂, h1, h2, hno⟩ := h
      refine Or.inr (Set.mem_iUnion₂.2 ⟨(s₁, s₂), ?_, hno⟩)
      rw [hSigns, Finset.mem_product]
      exact ⟨by rcases h1 with rfl | rfl <;> simp, by rcases h2 with rfl | rfl <;> simp⟩
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
    _ ≤ μ (good ∪ ⋃ p ∈ Signs, P p) := measure_mono hcov
    _ ≤ μ good + μ (⋃ p ∈ Signs, P p) := measure_union_le _ _
    _ ≤ μ good + 4 * crossingBound t := by gcongr

/-! ### Georgii (18.6), (18.7) in the plane `ℤ²` -/

/-- Georgii's infinite outside of `D` *is* the union of the infinite clusters of the complement:
`Peierls.outside` and `SimpleGraph.infiniteClusters` are the same object. -/
lemma outside_eq_infiniteClusters (D : Set Site) :
    outside D = (latticeGraph 2).infiniteClusters Dᶜ := rfl

/-- **The plane minus a finite set percolates.** -/
theorem nonempty_infiniteClusters_compl {F : Set Site} (hF : F.Finite) :
    ((latticeGraph 2).infiniteClusters Fᶜ).Nonempty := by
  obtain ⟨N, hFN⟩ := exists_subset_box hF
  have hc : mk ((N : ℤ) + 1) ((N : ℤ) + 1) ∉ box N := by
    rw [notMem_box_iff, mk_zero]
    exact Or.inl (by rw [abs_of_nonneg (by omega)]; omega)
  exact ⟨_, (outside_eq_infiniteClusters F) ▸ mem_outside_of_notMem_box hFN hc⟩

/-- The plane minus a finite set percolates for any graph above the nearest-neighbour graph;
this is the hypothesis of `SimpleGraph.IsOceanIn.infinite` and
`SimpleGraph.oceanPart_nonempty_iff` for the plane `R = ℤ²`. -/
theorem nonempty_infiniteClusters_univ_diff {G : SimpleGraph Site} (hG : latticeGraph 2 ≤ G)
    {F : Set Site} (hF : F.Finite) : (G.infiniteClusters (Set.univ \ F)).Nonempty :=
  (nonempty_infiniteClusters_compl hF).mono
    (SimpleGraph.infiniteClusters_mono hG (Set.compl_eq_univ_sdiff F).subset)

/-- **Georgii's remark after (18.6)**: an ocean in the plane is always infinite. -/
theorem infinite_of_isOceanIn {ξ : Set Site}
    (h : SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ ξ) : ξ.Infinite :=
  h.infinite fun _ hF ↦ nonempty_infiniteClusters_univ_diff
    (latticeGraph_le_starLatticeGraph 2) hF

/-- **Georgii's remark after (18.6)**: a subset of the plane containing an ocean has exactly one
infinite cluster. -/
theorem existsUnique_infinite_supp_of_isOceanIn {ξ W : Set Site}
    (h : SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ ξ) (hξW : ξ ⊆ W) :
    ∃! c : ((latticeGraph 2).induce W).ConnectedComponent, c.supp.Infinite :=
  h.existsUnique_infinite_supp (latticeGraph_le_starLatticeGraph 2) (infinite_of_isOceanIn h)
    hξW (Set.subset_univ W)

/-- **Georgii, after (18.7)**, in the plane: `ξ⁰_P(G, ω) ≠ ∅` iff `V_P(G, ω)` contains an
ocean. -/
theorem oceanPart_nonempty_iff_exists_isOceanIn (W : Set Site) :
    (SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ W).Nonempty ↔
      ∃ ξ, ξ ⊆ W ∧ SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ ξ :=
  SimpleGraph.oceanPart_nonempty_iff (latticeGraph_le_starLatticeGraph 2)
    (fun _ hF ↦ nonempty_infiniteClusters_univ_diff (latticeGraph_le_starLatticeGraph 2) hF)
    (Set.subset_univ W)

/-! ### The symmetries of the plane: translations and reflections -/

/-- Translations are automorphisms of the nearest-neighbour graph. -/
lemma latticeGraph_adj_add_right {d : ℕ} (a x y : Fin d → ℤ) :
    (latticeGraph d).Adj (x + a) (y + a) ↔ (latticeGraph d).Adj x y := by
  have h : ∑ i, ((x + a) i - (y + a) i).natAbs = ∑ i, (x i - y i).natAbs :=
    Finset.sum_congr rfl fun i _ ↦ by simp only [Pi.add_apply]; congr 1; ring
  constructor
  · intro hxy
    have h1 : ∑ i, ((x + a) i - (y + a) i).natAbs = 1 := hxy
    exact h.symm.trans h1
  · intro hxy
    have h1 : ∑ i, (x i - y i).natAbs = 1 := hxy
    exact h.trans h1

/-- Translations are automorphisms of the `*`-neighbour graph. -/
lemma starLatticeGraph_adj_add_right {d : ℕ} (a x y : Fin d → ℤ) :
    (starLatticeGraph d).Adj (x + a) (y + a) ↔ (starLatticeGraph d).Adj x y := by
  rw [starLatticeGraph_adj, starLatticeGraph_adj]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun hxy ↦ hne (by rw [hxy]), fun i ↦ by
      have := h i; simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using this⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun hxy ↦ hne (add_right_cancel hxy), fun i ↦ by
      simpa only [Pi.add_apply, add_sub_add_right_eq_sub] using h i⟩

/-- The reflection `refl ε₁ ε₂` as an involutive permutation of the plane. -/
def reflEquiv {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) : Site ≃ Site :=
  Function.Involutive.toPerm (refl ε₁ ε₂) (refl_refl h₁ h₂)

@[simp] lemma coe_reflEquiv {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1) :
    ⇑(reflEquiv h₁ h₂) = refl ε₁ ε₂ := rfl

/-- **The ocean part of the plane is translation-equivariant.**  With (18.3) this is the
invariance of `{ξ⁰_P(G, ·) ≠ ∅}` under the shift group used in Georgii (18.17). -/
theorem oceanPart_image_add_right (a : Site) (W : Set Site) :
    SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ ((· + a) '' W)
      = (· + a) '' SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ W := by
  have h := SimpleGraph.oceanPart_image (G := latticeGraph 2) (H := starLatticeGraph 2)
    (R := Set.univ) (e := Equiv.addRight a) (fun x y ↦ latticeGraph_adj_add_right a x y)
    (fun x y ↦ starLatticeGraph_adj_add_right a x y)
    (by rw [Set.image_univ]; exact (Equiv.addRight a).surjective.range_eq) W
  simpa using h

/-- **The ocean part of the plane is reflection-equivariant**, the second invariance used in
Georgii (18.17). -/
theorem oceanPart_image_refl {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1) (h₂ : ε₂ = 1 ∨ ε₂ = -1)
    (W : Set Site) :
    SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ (refl ε₁ ε₂ '' W)
      = refl ε₁ ε₂ '' SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ W := by
  have h := SimpleGraph.oceanPart_image (G := latticeGraph 2) (H := starLatticeGraph 2)
    (R := Set.univ) (e := reflEquiv h₁ h₂)
    (fun x y ↦ latticeGraph_adj_refl_iff h₁ h₂ x y)
    (fun x y ↦ starLatticeGraph_adj_refl_iff h₁ h₂ x y)
    (by rw [Set.image_univ]; exact (reflEquiv h₁ h₂).surjective.range_eq) W
  simpa using h

end Peierls

end MeasureTheory.GibbsMeasure

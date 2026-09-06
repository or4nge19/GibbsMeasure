/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Group.Finset
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Sperner's lemma

Sperner's lemma: for the standard (Freudenthal–Kuhn) triangulation of the `N`-th dilate of the
standard `(N-1)`-simplex, every *admissible* colouring of the lattice points — one that paints a
point with an index of its support — has an **odd** number of panchromatic cells, in particular
at least one.

## The combinatorial model

Write `N = d + 1` for the number of colours and `ℓ ≥ 1` for the mesh, so that the object being
triangulated is `ℓ·Δ^d = {x ∈ ℕ^{d+1} : ∑ x = ℓ}`.  Instead of the barycentric coordinates `x`
we use the *staircase* coordinates
`y_m = x_0 + ⋯ + x_m` (`0 ≤ m < d`), which identify `ℓ·Δ^d` with the order simplex
`{y ∈ ℤ^d : 0 ≤ y_0 ≤ ⋯ ≤ y_{d-1} ≤ ℓ}`; the barycentric coordinates are recovered as the
successive differences of `profile ℓ y : ℕ → ℤ`, which is `0`, then `y_0, …, y_{d-1}`, then `ℓ`.
In these coordinates the standard triangulation is *Kuhn's*: a top-dimensional cell is a pair
`(y, σ)` consisting of a base point `y` and a permutation `σ` of `Fin d`, with vertices

`vertex y σ k = y + 1_{ {i : σ i < k} }`,  `k = 0, …, d`,

so that the cell is the chain `y = v_0 < v_1 < ⋯ < v_d = y + 1` inside the unit cube at `y`, the
order of the unit steps being prescribed by `σ`.  `IsCell` is the (elementary, purely
order-theoretic) characterisation of the pairs `(y, σ)` all of whose vertices lie in the order
simplex, `IsCell_iff_forall_isGridPt`.

## Main results

* `Sperner.odd_card_panchromaticCells` — **Sperner's lemma**: relative to an admissible
  colouring `φ`, the number of panchromatic cells of mesh `ℓ ≥ 1` is odd.
* `Sperner.exists_isPanchromatic` — the consequence that is actually used: some cell shows all
  `d + 1` colours.
* `Sperner.exists_forall_mem_stdSimplex` — the same statement transported to the simplex
  `stdSimplex ℝ (Fin (d+1))`: there are `d + 1` points of the simplex, pairwise within `2/ℓ` in
  every coordinate, the `n`-th of which is coloured `n` and therefore has `n`-th coordinate
  positive.  This is what feeds the Knaster–Kuratowski–Mazurkiewicz lemma.

## The proof

Georgii's induction on the number of colours (his Appendix 19.A), organised as a
door-to-door parity argument so that no classification of the cells containing a given facet is
needed.  A *door* is a pair (cell, omitted vertex) whose remaining `d` vertices show exactly the
colours `0, …, d-1` (`Sperner.IsDoor`).  Then

* `Sperner.card_doors_mod_two` — the number of doors is congruent mod `2` to the number of
  panchromatic cells: a panchromatic cell has exactly one door, a cell showing exactly
  `{0, …, d-1}` has exactly two, and any other cell has none.  This is pure counting for a map
  `Fin (d+1) → Fin (d+1)` (`Sperner.odd_card_filter_iff_surjective`).
* `Sperner.pivot` — the *pivot* involution on doors: keep the facet and replace the omitted
  vertex by the only other vertex completing it to a cell of the (unbounded) Kuhn triangulation
  of `ℤ^d`.  `Sperner.pivot_pivot` is `pivot ∘ pivot = id`.
* `Sperner.isFixed_pivot_iff` — a door is fixed by the pivot exactly when the pivoted cell falls
  out of the order simplex, and — this is where admissibility enters — that happens only for
  doors on the face `α_d = 0`, i.e. `y_{d-1} = ℓ`, with the omitted vertex the smallest one.
* `Sperner.fixedDoorEquiv` — those are in bijection with the panchromatic cells of the
  `(d-1)`-dimensional problem for the restricted colouring, which closes the induction.

## Georgii's statement is false as it stands

Georgii states Sperner's lemma (19.A1) for the *cliques* of the graph on the `ℓ⁻¹`-grid
`𝒫_{N,ℓ}` in which two points are adjacent when they differ by `±ℓ⁻¹` in exactly two
coordinates, asserting parenthetically that an `n`-clique is the vertex set of an
`(n-1)`-simplex of the induced simplicial decomposition of `𝒫_N`.  The cliques are easy to
classify: an `N`-clique is either `{y + e_m : m}` for some `y ∈ ℕ^N` with `∑ y = ℓ - 1`, or
`{z - e_m : m}` for some `z ∈ ℕ^N` with `∑ z = ℓ + 1` and every `z_m ≥ 1`.  For `N ≤ 3` these
are exactly the top-dimensional simplices, but for `N ≥ 4` they are far fewer, and the double
count (19.A2) — which needs every `(N-1)`-clique to lie in one or two `N`-cliques — breaks down.

Concretely, take `N = 4` and `ℓ = 2`.  There is no `z ∈ ℕ^4` with `∑ z = 3` and all `z_m ≥ 1`,
so the only `4`-cliques are `U_j = {e_j + e_m : m}`, `j = 1, …, 4`.  An admissible colouring must
paint `2e_j` with `j`, and may paint `e_j + e_k` (`j ≠ k`) with either `j` or `k`; `U_j` is
panchromatic exactly when `e_j + e_k` is painted `k` for every `k ≠ j`.  The admissible colouring

`φ(e_1+e_2) = φ(e_1+e_3) = 1`, `φ(e_1+e_4) = 4`, `φ(e_2+e_3) = φ(e_2+e_4) = 2`,
`φ(e_3+e_4) = 3`, `φ(2e_j) = j`,

therefore has **no** panchromatic `4`-clique at all: `U_1` fails at `{1,2}`, `U_2` at `{2,3}`,
`U_3` at `{3,4}` and `U_4` at `{1,4}`.  So (19.A1) fails for `N = 4`, `ℓ = 2` (and likewise for
`N = 4, ℓ = 3` and `N = 5, ℓ = 2`); the `3`-clique `{(1,1,0,0), (1,0,1,0), (0,1,1,0)}` (in the
coordinates `ℓα`) lies in *no* `4`-clique at all, which is where the double count (19.A2) breaks.

The statement proved here is the classical one, on the standard triangulation, and it is what
Georgii's Appendix 19.A4 uses: it delivers `N` grid points, pairwise `O(ℓ⁻¹)`-close, showing all
`N` colours.
-/

@[expose] public section

open Finset

namespace Sperner

variable {d ℓ : ℕ}

/-! ### A parity lemma for involutions -/

/-- A fixed-point-free involution of a finite set has even cardinality. -/
theorem even_card_of_involutive_of_fixedPointFree {α : Type*} (s : Finset α)
    (g : α → α) (hmaps : ∀ x ∈ s, g x ∈ s) (hinv : ∀ x ∈ s, g (g x) = x)
    (hfree : ∀ x ∈ s, g x ≠ x) : Even s.card := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    subst hn
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hgx : g x ∈ s := hmaps x hx
      have hne : g x ≠ x := hfree x hx
      set t := (s.erase x).erase (g x) with ht
      have h2 : g x ∈ s.erase x := Finset.mem_erase.2 ⟨hne, hgx⟩
      have hcard : t.card + 2 = s.card := by
        have h1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have h3 : t.card = (s.erase x).card - 1 := Finset.card_erase_of_mem h2
        have hpos : 1 ≤ s.card := Finset.card_pos.2 ⟨x, hx⟩
        have hpos2 : 1 ≤ (s.erase x).card := Finset.card_pos.2 ⟨g x, h2⟩
        omega
      have hsub : t ⊆ s := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hmaps' : ∀ z ∈ t, g z ∈ t := by
        intro z hz
        have hz' : z ∈ s := hsub hz
        have hzx : z ≠ x := (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).1
        have hzgx : z ≠ g x := (Finset.mem_erase.1 hz).1
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmaps z hz'⟩⟩
        · intro h
          exact hzx (by rw [← hinv x hx, ← h, hinv z hz'])
        · intro h
          exact hzgx (by rw [← h, hinv z hz'])
      obtain ⟨m, hm⟩ := ih t.card (by omega) t hmaps' (fun z hz ↦ hinv z (hsub hz))
        (fun z hz ↦ hfree z (hsub hz)) rfl
      exact ⟨m + 1, by omega⟩

/-- The cardinality of a finite set carrying an involution is congruent mod `2` to the number of
its fixed points. -/
theorem card_mod_two_eq_card_filter_fixed {α : Type*} [DecidableEq α] (s : Finset α) (g : α → α)
    (hmaps : ∀ x ∈ s, g x ∈ s) (hinv : ∀ x ∈ s, g (g x) = x) :
    s.card % 2 = (s.filter fun x ↦ g x = x).card % 2 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (p := fun x ↦ g x = x)
  have heven : Even (s.filter fun x ↦ ¬ g x = x).card := by
    refine even_card_of_involutive_of_fixedPointFree _ g ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨hmaps x hx.1, ?_⟩
      intro h
      exact hx.2 (by rw [← hinv x hx.1, h, h])
    · exact fun x hx ↦ hinv x (Finset.mem_filter.1 hx).1
    · exact fun x hx ↦ (Finset.mem_filter.1 hx).2
  obtain ⟨m, hm⟩ := heven
  omega

/-! ### Staircase coordinates -/

/-- The *profile* of a staircase point `y`: `profile ℓ y n` is the `n`-th partial sum
`x_0 + ⋯ + x_{n-1}` of the barycentric coordinates, so it runs `0, y_0, …, y_{d-1}, ℓ, ℓ, …`.
The barycentric coordinate `x_n` is the increment `profile ℓ y (n+1) - profile ℓ y n`. -/
def profile (ℓ : ℕ) {d : ℕ} (y : Fin d → ℤ) : ℕ → ℤ
  | 0 => 0
  | (n + 1) => if h : n < d then y ⟨n, h⟩ else (ℓ : ℤ)

@[simp] lemma profile_zero (y : Fin d → ℤ) : profile ℓ y 0 = 0 := rfl

lemma profile_succ_of_lt {n : ℕ} (y : Fin d → ℤ) (h : n < d) :
    profile ℓ y (n + 1) = y ⟨n, h⟩ := by
  simp [profile, h]

lemma profile_succ_of_le {n : ℕ} (y : Fin d → ℤ) (h : d ≤ n) :
    profile ℓ y (n + 1) = (ℓ : ℤ) := by
  simp [profile, Nat.not_lt.2 h]

@[simp] lemma profile_apply_coe (y : Fin d → ℤ) (i : Fin d) :
    profile ℓ y ((i : ℕ) + 1) = y i := by
  rw [profile_succ_of_lt y i.isLt]

/-- A *grid point* of mesh `ℓ`: a monotone staircase between `0` and `ℓ`, i.e. a lattice point of
the order simplex. -/
def IsGridPt (ℓ : ℕ) {d : ℕ} (y : Fin d → ℤ) : Prop :=
  (∀ i j : Fin d, i ≤ j → y i ≤ y j) ∧ (∀ i, 0 ≤ y i) ∧ ∀ i, y i ≤ (ℓ : ℤ)

lemma IsGridPt.mono {y : Fin d → ℤ} (hy : IsGridPt ℓ y) {i j : Fin d} (h : i ≤ j) :
    y i ≤ y j := hy.1 i j h

lemma IsGridPt.nonneg {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (i : Fin d) : 0 ≤ y i := hy.2.1 i

lemma IsGridPt.le {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (i : Fin d) : y i ≤ (ℓ : ℤ) := hy.2.2 i

lemma IsGridPt.profile_nonneg {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (n : ℕ) :
    0 ≤ profile ℓ y n := by
  cases n with
  | zero => simp
  | succ m =>
    by_cases h : m < d
    · rw [profile_succ_of_lt y h]; exact hy.nonneg _
    · rw [profile_succ_of_le y (not_lt.1 h)]; exact_mod_cast Nat.zero_le ℓ

lemma IsGridPt.profile_le {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (n : ℕ) :
    profile ℓ y n ≤ (ℓ : ℤ) := by
  cases n with
  | zero => simp only [profile_zero]; exact_mod_cast Nat.zero_le ℓ
  | succ m =>
    by_cases h : m < d
    · rw [profile_succ_of_lt y h]; exact hy.le _
    · rw [profile_succ_of_le y (not_lt.1 h)]

lemma IsGridPt.profile_le_succ {y : Fin d → ℤ} (hy : IsGridPt ℓ y) (n : ℕ) :
    profile ℓ y n ≤ profile ℓ y (n + 1) := by
  cases n with
  | zero => simpa using hy.profile_nonneg 1
  | succ m =>
    by_cases h : m + 1 < d
    · rw [profile_succ_of_lt y h, profile_succ_of_lt y (Nat.lt_of_succ_lt h)]
      exact hy.mono (by simp [Fin.le_def])
    · rw [profile_succ_of_le y (Nat.not_lt.1 h)]
      exact hy.profile_le _

lemma IsGridPt.profile_mono {y : Fin d → ℤ} (hy : IsGridPt ℓ y) {m n : ℕ} (h : m ≤ n) :
    profile ℓ y m ≤ profile ℓ y n :=
  monotone_nat_of_le_succ hy.profile_le_succ h

/-- An admissible colour at `y` is an index of the support of the barycentric coordinates, i.e.
one at which the profile strictly increases. -/
def IsAdmissibleAt (ℓ : ℕ) {d : ℕ} (y : Fin d → ℤ) (n : ℕ) : Prop :=
  profile ℓ y n < profile ℓ y (n + 1)

/-- An admissible colour is one of the `d + 1` available ones. -/
lemma IsAdmissibleAt.le {y : Fin d → ℤ} {n : ℕ} (h : IsAdmissibleAt ℓ y n) : n ≤ d := by
  by_contra hn
  rw [Nat.not_le] at hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [IsAdmissibleAt, profile_succ_of_le y (by omega), profile_succ_of_le y (by omega)] at h
  exact absurd h (lt_irrefl _)

/-- A colouring is *admissible* if every grid point is painted with an index of its support. -/
def IsAdmissible (ℓ : ℕ) {d : ℕ} (φ : (Fin d → ℤ) → ℕ) : Prop :=
  ∀ y, IsGridPt ℓ y → IsAdmissibleAt ℓ y (φ y)

/-! ### Cells of Kuhn's triangulation -/

/-- The `k`-th vertex of the Kuhn cell with base point `y` and step order `σ`: the base point
raised by one in the coordinates whose step comes among the first `k`. -/
def vertex {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : ℕ) : Fin d → ℤ :=
  fun i ↦ y i + if (σ i : ℕ) < k then 1 else 0

@[simp] lemma vertex_zero (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) : vertex y σ 0 = y := by
  funext i; simp [vertex]

lemma vertex_of_le {k : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (hk : d ≤ k) :
    vertex y σ k = fun i ↦ y i + 1 := by
  funext i
  have : (σ i : ℕ) < k := lt_of_lt_of_le (σ i).isLt hk
  simp [vertex, this]

lemma vertex_apply_of_le {k : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (hk : d ≤ k)
    (i : Fin d) : vertex y σ k i = y i + 1 := by
  have : ((σ i : Fin d) : ℕ) < k := lt_of_lt_of_le (σ i).isLt hk
  simp [vertex, this]

lemma vertex_le_vertex {k k' : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (h : k ≤ k')
    (i : Fin d) : vertex y σ k i ≤ vertex y σ k' i := by
  simp only [vertex]
  split_ifs with h1 h2 h2 <;> omega

lemma le_vertex (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : ℕ) (i : Fin d) :
    y i ≤ vertex y σ k i := by
  simpa using vertex_le_vertex (k := 0) (k' := k) y σ (Nat.zero_le _) i

lemma vertex_le_succ (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : ℕ) (i : Fin d) :
    vertex y σ k i ≤ y i + 1 := by
  simp only [vertex]; split_ifs <;> omega

/-- A pair `(y, σ)` spans a cell of the triangulated order simplex of mesh `ℓ` when the base
point is nonnegative, the top point `y + 1` stays below `ℓ`, and the steps are taken in the
reverse order of any coordinate tie: `y i = y j` with `i < j` forces the step at `j` to come
first.  `isCell_iff_forall_isGridPt` is the equivalence with "all vertices are grid points". -/
def IsCell (ℓ : ℕ) {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) : Prop :=
  (∀ i j : Fin d, i ≤ j → y i ≤ y j) ∧ (∀ i, 0 ≤ y i) ∧ (∀ i, y i < (ℓ : ℤ)) ∧
    ∀ i j : Fin d, i < j → y i = y j → σ j ≤ σ i

lemma IsCell.isGridPt_vertex {y : Fin d → ℤ} {σ : Equiv.Perm (Fin d)} (h : IsCell ℓ y σ)
    (k : ℕ) : IsGridPt ℓ (vertex y σ k) := by
  obtain ⟨hmono, hnn, hlt, hord⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    rcases eq_or_lt_of_le hij with rfl | hlt'
    · exact le_rfl
    rcases eq_or_lt_of_le (hmono i j hij) with heq | hgt
    · have hle : (σ j : ℕ) ≤ (σ i : ℕ) := hord i j hlt' heq
      simp only [vertex, ← heq]
      split_ifs <;> omega
    · have h1 := vertex_le_succ y σ k i
      have h2 := le_vertex y σ k j
      omega
  · intro i; exact le_trans (hnn i) (le_vertex y σ k i)
  · intro i
    have := vertex_le_succ y σ k i
    have := hlt i
    omega

lemma IsCell.isGridPt {y : Fin d → ℤ} {σ : Equiv.Perm (Fin d)} (h : IsCell ℓ y σ) :
    IsGridPt ℓ y := by simpa using h.isGridPt_vertex (ℓ := ℓ) 0

/-- The vertices of a cell are pairwise distinct: `vertex y σ` is injective on `{0, …, d}`. -/
lemma vertex_injOn {y : Fin d → ℤ} {σ : Equiv.Perm (Fin d)} {k k' : ℕ} (hk : k ≤ d) (hk' : k' ≤ d)
    (h : vertex y σ k = vertex y σ k') : k = k' := by
  by_contra hne
  wlog hlt : k < k' generalizing k k'
  · exact this hk' hk h.symm (Ne.symm hne) (by omega)
  have hk'pos : 0 < k' := by omega
  obtain ⟨i, hi⟩ : ∃ i : Fin d, (σ i : ℕ) = k' - 1 := by
    refine ⟨σ.symm ⟨k' - 1, by omega⟩, ?_⟩
    simp
  have hcon := congrFun h i
  simp only [vertex, hi] at hcon
  split_ifs at hcon <;> omega


/-! ### Counting the doors of a single cell

A cell has `d + 1` vertices and there are `d + 1` colours.  A *door* of the cell is a vertex
whose `d` companions already show the `d` colours `0, …, d - 1`.  A panchromatic cell has exactly
one door, a cell whose vertices show exactly the colours `0, …, d - 1` has exactly two, and every
other cell has none. -/

/-- The number of doors of a cell whose vertex colours are `f`, modulo `2`: it is `1` when the
cell is panchromatic and `0` otherwise. -/
lemma card_filter_mod_two {d : ℕ} (f : Fin (d + 1) → ℕ) (hf : ∀ j, f j ≤ d) :
    (univ.filter fun k ↦ ∀ c < d, ∃ j, j ≠ k ∧ f j = c).card % 2
      = if ∀ c ≤ d, ∃ j, f j = c then 1 else 0 := by
  classical
  split_ifs with hs
  · -- Surjective, hence injective: the unique door omits the vertex coloured `d`.
    have himg : univ.image f = Finset.range (d + 1) := by
      refine Finset.Subset.antisymm ?_ ?_
      · intro c hc
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
        obtain ⟨j, rfl⟩ := hc
        simpa using Nat.lt_succ_of_le (hf j)
      · intro c hc
        simp only [Finset.mem_range] at hc
        obtain ⟨j, hj⟩ := hs c (Nat.lt_succ_iff.1 hc)
        exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
    have hcard : (univ.image f).card = (univ : Finset (Fin (d + 1))).card := by
      rw [himg]; simp
    have hinj : Set.InjOn f (univ : Finset (Fin (d + 1))) := Finset.injOn_of_card_image_eq hcard
    obtain ⟨k₀, hk₀⟩ := hs d le_rfl
    have hK : (univ.filter fun k ↦ ∀ c < d, ∃ j, j ≠ k ∧ f j = c) = {k₀} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        by_contra hne
        have hlt : f k < d := by
          rcases Nat.lt_or_ge (f k) d with h | h
          · exact h
          · have hfk : f k = d := le_antisymm (hf k) h
            exact absurd (hinj (Finset.mem_coe.2 (Finset.mem_univ k))
              (Finset.mem_coe.2 (Finset.mem_univ k₀)) (by rw [hfk, hk₀])) hne
        obtain ⟨j, hjk, hj⟩ := hk _ hlt
        exact hjk (hinj (Finset.mem_coe.2 (Finset.mem_univ j))
          (Finset.mem_coe.2 (Finset.mem_univ k)) hj)
      · rintro rfl
        intro c hc
        obtain ⟨j, hj⟩ := hs c (le_of_lt hc)
        exact ⟨j, fun h ↦ by rw [h, hk₀] at hj; omega, hj⟩
    rw [hK]; simp
  · by_cases hcov : ∀ c, c < d → ∃ j, f j = c
    · -- All colours below `d` occur, `d` does not: exactly two doors.
      have hd : ∀ j, f j ≠ d := by
        intro j hj
        refine hs fun c hc ↦ ?_
        rcases Nat.lt_or_ge c d with h | h
        · exact hcov c h
        · exact ⟨j, by omega⟩
      have hmapsto : ∀ a : Fin (d + 1), a ∈ (univ : Finset (Fin (d + 1))) → f a ∈ Finset.range d :=
        fun a _ ↦ Finset.mem_range.2 (lt_of_le_of_ne (hf a) (hd a))
      obtain ⟨a, -, b, -, hab, hfab⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := (univ : Finset (Fin (d + 1))))
          (t := Finset.range d) (by simp) hmapsto
      have hberase : (univ.erase b).card = d := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ b)]; simp
      have himg : (univ.erase b).image f = Finset.range d := by
        refine Finset.Subset.antisymm ?_ ?_
        · intro c hc
          simp only [Finset.mem_image] at hc
          obtain ⟨j, -, rfl⟩ := hc
          exact hmapsto j (Finset.mem_univ _)
        · intro c hc
          simp only [Finset.mem_range] at hc
          obtain ⟨j, hj⟩ := hcov c hc
          by_cases hjb : j = b
          · exact Finset.mem_image.2 ⟨a, Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩,
              by rw [hfab, ← hjb]; exact hj⟩
          · exact Finset.mem_image.2 ⟨j, Finset.mem_erase.2 ⟨hjb, Finset.mem_univ _⟩, hj⟩
      have hinj : Set.InjOn f (univ.erase b : Finset (Fin (d + 1))) :=
        Finset.injOn_of_card_image_eq (by rw [himg, hberase]; simp)
      have hmem : ∀ {x : Fin (d + 1)}, x ≠ b → x ∈ (univ.erase b : Finset (Fin (d + 1))) :=
        fun {x} hx ↦ Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩)
      have hK : (univ.filter fun k ↦ ∀ c < d, ∃ j, j ≠ k ∧ f j = c) = {a, b} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hk
          by_contra hne
          have hka : k ≠ a := fun h ↦ hne (Or.inl h)
          have hkb : k ≠ b := fun h ↦ hne (Or.inr h)
          obtain ⟨j, hjk, hj⟩ := hk (f k) (Finset.mem_range.1 (hmapsto k (Finset.mem_univ _)))
          by_cases hjb : j = b
          · subst hjb
            exact hka (hinj (hmem hkb) (hmem hab) (hj.symm.trans hfab.symm))
          · exact hjk (hinj (hmem hjb) (hmem hkb) hj)
        · intro hk c hc
          obtain ⟨j, hj⟩ := hcov c hc
          rcases hk with rfl | rfl
          · by_cases hjk : j = k
            · exact ⟨b, Ne.symm hab, by rw [← hfab, ← hjk]; exact hj⟩
            · exact ⟨j, hjk, hj⟩
          · by_cases hjk : j = k
            · exact ⟨a, hab, by rw [hfab, ← hjk]; exact hj⟩
            · exact ⟨j, hjk, hj⟩
      rw [hK, Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
    · -- Some colour below `d` is missing: no doors at all.
      simp only [not_forall, not_exists] at hcov
      obtain ⟨c, hcd, hcnone⟩ := hcov
      have hK : (univ.filter fun k ↦ ∀ c' < d, ∃ j, j ≠ k ∧ f j = c') = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun k hk ↦ ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        obtain ⟨j, -, hj⟩ := hk c hcd
        exact hcnone j hj
      rw [hK]; simp

/-! ### The pivot

Deleting one vertex from a cell of the Kuhn triangulation of `ℤ^d` leaves a facet which is
contained in exactly one other cell; passing to it is the *pivot*.  Deleting an intermediate
vertex transposes two consecutive steps; deleting the bottom (resp. top) vertex moves the base
point up (resp. down) and rotates the step order. -/

/-- The cyclic predecessor of a natural number modulo `d`, and its inverse, cancel. -/
lemma rotDown_rotUp_val {d a : ℕ} (h : a < d) :
    (if (if a = 0 then d - 1 else a - 1) + 1 = d then 0
      else (if a = 0 then d - 1 else a - 1) + 1) = a := by
  split_ifs <;> omega

/-- The cyclic successor of a natural number modulo `d`, and its inverse, cancel. -/
lemma rotUp_rotDown_val {d a : ℕ} :
    (if (if a + 1 = d then 0 else a + 1) = 0 then d - 1
      else (if a + 1 = d then 0 else a + 1) - 1) = a := by
  by_cases h1 : a + 1 = d
  · rw [if_pos h1, if_pos (rfl : (0 : ℕ) = 0)]
    omega
  · rw [if_neg h1, if_neg (by omega : ¬ (a + 1 = 0))]
    omega

/-- The cyclic predecessor permutation of `Fin d`. -/
def rotDown (d : ℕ) : Equiv.Perm (Fin d) where
  toFun i := ⟨if (i : ℕ) = 0 then d - 1 else (i : ℕ) - 1, by have := i.isLt; split <;> omega⟩
  invFun i := ⟨if (i : ℕ) + 1 = d then 0 else (i : ℕ) + 1, by have := i.isLt; split <;> omega⟩
  left_inv i := Fin.ext (rotDown_rotUp_val i.isLt)
  right_inv i := Fin.ext rotUp_rotDown_val

@[simp] lemma coe_rotDown_apply {d : ℕ} (i : Fin d) :
    ((rotDown d i : Fin d) : ℕ) = if (i : ℕ) = 0 then d - 1 else (i : ℕ) - 1 := rfl

@[simp] lemma coe_rotDown_symm_apply {d : ℕ} (i : Fin d) :
    (((rotDown d).symm i : Fin d) : ℕ) = if (i : ℕ) + 1 = d then 0 else (i : ℕ) + 1 := rfl

/-- The pivot of a door `(y, σ, k)`: the unique other cell of the Kuhn triangulation of `ℤ^d`
containing the facet obtained by deleting the `k`-th vertex, together with the index of the new
vertex in it. -/
def pivot {d : ℕ} (p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :
    ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1) :=
  if h : 0 < (p.2 : ℕ) ∧ (p.2 : ℕ) < d then
    ((p.1.1, p.1.2.trans (Equiv.swap ⟨(p.2 : ℕ) - 1, by omega⟩ ⟨(p.2 : ℕ), h.2⟩)), p.2)
  else if (p.2 : ℕ) = 0 then
    ((vertex p.1.1 p.1.2 1, p.1.2.trans (rotDown d)), Fin.last d)
  else
    ((fun i ↦ p.1.1 i - (if (p.1.2 i : ℕ) + 1 = d then 1 else 0),
      p.1.2.trans (rotDown d).symm), 0)

lemma pivot_interior {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : Fin (d + 1))
    (h : 0 < (k : ℕ) ∧ (k : ℕ) < d) :
    pivot ((y, σ), k)
      = ((y, σ.trans (Equiv.swap ⟨(k : ℕ) - 1, by omega⟩ ⟨(k : ℕ), h.2⟩)), k) := by
  unfold pivot
  split_ifs <;> rfl

lemma pivot_bot {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : Fin (d + 1))
    (h : (k : ℕ) = 0) :
    pivot ((y, σ), k) = ((vertex y σ 1, σ.trans (rotDown d)), Fin.last d) := by
  unfold pivot
  dsimp only
  split_ifs <;> first | rfl | (exfalso; omega)

lemma pivot_top {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) (k : Fin (d + 1))
    (hd : 0 < d) (h : (k : ℕ) = d) :
    pivot ((y, σ), k)
      = ((fun i ↦ y i - (if (σ i : ℕ) + 1 = d then 1 else 0), σ.trans (rotDown d).symm), 0) := by
  unfold pivot
  dsimp only
  split_ifs <;> first | rfl | (exfalso; omega)

/-! #### The facet is preserved -/

/-- Transposing two consecutive steps changes only the vertex between them. -/
lemma vertex_swap {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) {k : ℕ} (hk0 : 0 < k)
    (hkd : k < d) {j : ℕ} (hj : j ≠ k) :
    vertex y (σ.trans (Equiv.swap (⟨k - 1, by omega⟩ : Fin d) ⟨k, hkd⟩)) j = vertex y σ j := by
  set A : Fin d := ⟨k - 1, by omega⟩ with hA
  set B : Fin d := ⟨k, hkd⟩ with hB
  have hAv : (A : ℕ) = k - 1 := by rw [hA]
  have hBv : (B : ℕ) = k := by rw [hB]
  funext i
  simp only [vertex, Equiv.trans_apply]
  have key : ((Equiv.swap A B (σ i) : Fin d) : ℕ) < j ↔ ((σ i : Fin d) : ℕ) < j := by
    rcases eq_or_ne (σ i) A with h | h1
    · rw [h, Equiv.swap_apply_left, hAv, hBv]; omega
    · rcases eq_or_ne (σ i) B with h | h2
      · rw [h, Equiv.swap_apply_right, hAv, hBv]; omega
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  simp only [key]

/-- Moving the base point up and rotating the step order down shifts the vertex indices by one:
the pivoted cell at `k = 0` has the same facet. -/
lemma vertex_rotDown {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) {j : ℕ} (hj : j < d) :
    vertex (vertex y σ 1) (σ.trans (rotDown d)) j = vertex y σ (j + 1) := by
  funext i
  have hlt := (σ i).isLt
  simp only [vertex, Equiv.trans_apply, coe_rotDown_apply]
  split_ifs <;> omega

/-- Moving the base point down and rotating the step order up shifts the vertex indices back by
one: the pivoted cell at `k = d` has the same facet. -/
lemma vertex_rotUp {d : ℕ} (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) {j : ℕ} (hj : 0 < j)
    (hj' : j ≤ d) :
    vertex (fun i ↦ y i - (if (σ i : ℕ) + 1 = d then 1 else 0)) (σ.trans (rotDown d).symm) j
      = vertex y σ (j - 1) := by
  funext i
  have hlt := (σ i).isLt
  simp only [vertex, Equiv.trans_apply, coe_rotDown_symm_apply]
  split_ifs <;> omega


/-! ### Cells, doors and panchromatic cells as finite sets -/

instance decidableIsCell (ℓ : ℕ) (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) :
    Decidable (IsCell ℓ y σ) := by unfold IsCell; infer_instance

/-- A cell is *panchromatic* when its `d + 1` vertices show all `d + 1` colours. -/
def IsPanchromatic (φ : (Fin d → ℤ) → ℕ) (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d)) : Prop :=
  ∀ c ≤ d, ∃ j : Fin (d + 1), φ (vertex y σ (j : ℕ)) = c

instance decidableIsPanchromatic (φ : (Fin d → ℤ) → ℕ) (y : Fin d → ℤ)
    (σ : Equiv.Perm (Fin d)) : Decidable (IsPanchromatic φ y σ) := by
  unfold IsPanchromatic; infer_instance

/-- A *door* of the coloured complex: a cell together with the index of a vertex whose `d`
companions show exactly the colours `0, …, d - 1`. -/
def IsDoor (ℓ : ℕ) (φ : (Fin d → ℤ) → ℕ) (y : Fin d → ℤ) (σ : Equiv.Perm (Fin d))
    (k : Fin (d + 1)) : Prop :=
  IsCell ℓ y σ ∧ ∀ c < d, ∃ j : Fin (d + 1), j ≠ k ∧ φ (vertex y σ (j : ℕ)) = c

instance decidableIsDoor (ℓ : ℕ) (φ : (Fin d → ℤ) → ℕ) (y : Fin d → ℤ)
    (σ : Equiv.Perm (Fin d)) (k : Fin (d + 1)) : Decidable (IsDoor ℓ φ y σ k) := by
  unfold IsDoor; infer_instance

/-- The possible base points of a cell of mesh `ℓ`. -/
def basePts (ℓ d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Ico (0 : ℤ) (ℓ : ℤ)

lemma mem_basePts {y : Fin d → ℤ} : y ∈ basePts ℓ d ↔ ∀ i, 0 ≤ y i ∧ y i < (ℓ : ℤ) := by
  simp [basePts, Finset.mem_Ico]

/-- The cells of the triangulated order simplex of mesh `ℓ` in dimension `d`. -/
def cells (ℓ d : ℕ) : Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) :=
  ((basePts ℓ d) ×ˢ univ).filter fun p ↦ IsCell ℓ p.1 p.2

@[simp] lemma mem_cells {p : (Fin d → ℤ) × Equiv.Perm (Fin d)} :
    p ∈ cells ℓ d ↔ IsCell ℓ p.1 p.2 := by
  simp only [cells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, mem_basePts]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun i ↦ ⟨h.2.1 i, h.2.2.1 i⟩, h⟩⟩

/-- The panchromatic cells. -/
def panchromaticCells (ℓ d : ℕ) (φ : (Fin d → ℤ) → ℕ) :
    Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) :=
  (cells ℓ d).filter fun p ↦ IsPanchromatic φ p.1 p.2

@[simp] lemma mem_panchromaticCells {φ : (Fin d → ℤ) → ℕ}
    {p : (Fin d → ℤ) × Equiv.Perm (Fin d)} :
    p ∈ panchromaticCells ℓ d φ ↔ IsCell ℓ p.1 p.2 ∧ IsPanchromatic φ p.1 p.2 := by
  simp [panchromaticCells]

/-- The doors. -/
def doors (ℓ d : ℕ) (φ : (Fin d → ℤ) → ℕ) :
    Finset (((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :=
  ((cells ℓ d) ×ˢ univ).filter fun p ↦ IsDoor ℓ φ p.1.1 p.1.2 p.2

@[simp] lemma mem_doors {φ : (Fin d → ℤ) → ℕ}
    {p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)} :
    p ∈ doors ℓ d φ ↔ IsDoor ℓ φ p.1.1 p.1.2 p.2 := by
  simp only [doors, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, mem_cells]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1, h⟩⟩

/-- **The doors count the panchromatic cells modulo `2`.** -/
lemma card_doors_mod_two {φ : (Fin d → ℤ) → ℕ} (hφ : IsAdmissible ℓ φ) :
    (doors ℓ d φ).card % 2 = (panchromaticCells ℓ d φ).card % 2 := by
  classical
  have hsum : (doors ℓ d φ).card
      = ∑ p ∈ cells ℓ d, ((univ : Finset (Fin (d + 1))).filter
          fun k ↦ ∀ c < d, ∃ j : Fin (d + 1), j ≠ k ∧ φ (vertex p.1 p.2 (j : ℕ)) = c).card := by
    rw [doors, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hiff : IsDoor ℓ φ p.1 p.2 k ↔
        ∀ c < d, ∃ j : Fin (d + 1), j ≠ k ∧ φ (vertex p.1 p.2 (j : ℕ)) = c :=
      ⟨fun h ↦ h.2, fun h ↦ ⟨mem_cells.1 hp, h⟩⟩
    simp only [hiff]
  have key : ∀ p ∈ cells ℓ d, ((univ : Finset (Fin (d + 1))).filter
      fun k ↦ ∀ c < d, ∃ j : Fin (d + 1), j ≠ k ∧ φ (vertex p.1 p.2 (j : ℕ)) = c).card % 2
        = if IsPanchromatic φ p.1 p.2 then 1 else 0 := by
    intro p hp
    have hcell := mem_cells.1 hp
    exact card_filter_mod_two (fun j ↦ φ (vertex p.1 p.2 (j : ℕ)))
      fun j ↦ (hφ _ (hcell.isGridPt_vertex (j : ℕ))).le
  rw [hsum, Finset.sum_nat_mod, Finset.sum_congr rfl key, ← Finset.card_filter,
    panchromaticCells]

/-! ### The pivot is an involution -/

lemma pivot_pivot (p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :
    pivot (pivot p) = p := by
  obtain ⟨⟨y, σ⟩, k⟩ := p
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · refine Prod.ext (Prod.ext (funext fun i ↦ i.elim0) (Equiv.ext fun i ↦ i.elim0)) ?_
    apply Fin.ext
    have h1 := (pivot (pivot ((y, σ), k))).2.isLt
    have h2 := k.isLt
    omega
  · have hkle : (k : ℕ) ≤ d := Nat.lt_succ_iff.1 k.isLt
    rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
    · rw [pivot_bot y σ k h0, pivot_top _ _ _ hd (by simp)]
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · funext i
        have hlt := (σ i).isLt
        simp only [vertex, Equiv.trans_apply, coe_rotDown_apply]
        split_ifs <;> omega
      · simp only
        rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl]
      · exact (Fin.ext h0).symm
    · rcases eq_or_lt_of_le hkle with hlast | hint
      · rw [pivot_top y σ k hd hlast, pivot_bot _ _ _ (by simp)]
        refine Prod.ext (Prod.ext ?_ ?_) ?_
        · funext i
          have hlt := (σ i).isLt
          simp only [vertex, Equiv.trans_apply, coe_rotDown_symm_apply]
          split_ifs <;> omega
        · simp only
          rw [Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.trans_refl]
        · exact (Fin.ext (by simp [hlast])).symm
      · rw [pivot_interior y σ k ⟨h0, hint⟩, pivot_interior _ _ k ⟨h0, hint⟩]
        refine Prod.ext (Prod.ext rfl ?_) rfl
        simp only
        rw [Equiv.trans_assoc]
        rw [show (Equiv.swap (⟨(k : ℕ) - 1, by omega⟩ : Fin d) ⟨(k : ℕ), hint⟩).trans
              (Equiv.swap (⟨(k : ℕ) - 1, by omega⟩ : Fin d) ⟨(k : ℕ), hint⟩)
            = Equiv.refl (Fin d) by
          rw [← Equiv.symm_swap (⟨(k : ℕ) - 1, by omega⟩ : Fin d) ⟨(k : ℕ), hint⟩]
          exact Equiv.self_trans_symm _]
        exact Equiv.trans_refl _


/-! ### When does the pivoted pair span a cell?

A pair spans a cell exactly when all its vertices are grid points (`isCell_iff`).  Since the
pivot keeps the facet, only the *new* vertex has to be checked. -/

variable {y : Fin d → ℤ} {σ : Equiv.Perm (Fin d)}

theorem isCell_iff : IsCell ℓ y σ ↔ ∀ k ≤ d, IsGridPt ℓ (vertex y σ k) := by
  refine ⟨fun h k _ ↦ h.isGridPt_vertex k, fun H ↦ ?_⟩
  have h0 := H 0 (Nat.zero_le _)
  have hd := H d le_rfl
  rw [vertex_zero] at h0
  refine ⟨h0.1, h0.2.1, fun i ↦ ?_, fun i j hij hyij ↦ ?_⟩
  · have h1 : y i + 1 ≤ (ℓ : ℤ) := by
      have := hd.le i
      rwa [vertex_apply_of_le y σ le_rfl i] at this
    omega
  · by_contra hcon
    rw [not_le, Fin.lt_def] at hcon
    have hk : ((σ j : Fin d) : ℕ) ≤ d := le_of_lt (σ j).isLt
    have hmono := (H ((σ j : Fin d) : ℕ) hk).mono (le_of_lt hij)
    simp only [vertex] at hmono
    rw [if_pos hcon, if_neg (lt_irrefl _)] at hmono
    omega

/-- Raising every coordinate of a grid point by one gives a grid point exactly when the point is
everywhere below `ℓ`. -/
lemma isGridPt_add_one {v : Fin d → ℤ} (hv : IsGridPt ℓ v) :
    IsGridPt ℓ (fun i ↦ v i + 1) ↔ ∀ i, v i < (ℓ : ℤ) := by
  constructor
  · intro h i
    have h1 : v i + 1 ≤ (ℓ : ℤ) := h.le i
    omega
  · intro h
    refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
    · have h2 : v i ≤ v j := hv.mono hij
      change v i + 1 ≤ v j + 1
      omega
    · have h2 : 0 ≤ v i := hv.nonneg i
      change (0 : ℤ) ≤ v i + 1
      omega
    · have h2 := h i
      change v i + 1 ≤ (ℓ : ℤ)
      omega

/-- Lowering every coordinate of a grid point by one gives a grid point exactly when the point is
everywhere positive. -/
lemma isGridPt_sub_one {v : Fin d → ℤ} (hv : IsGridPt ℓ v) :
    IsGridPt ℓ (fun i ↦ v i - 1) ↔ ∀ i, 1 ≤ v i := by
  constructor
  · intro h i
    have h1 : (0 : ℤ) ≤ v i - 1 := h.nonneg i
    omega
  · intro h
    refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
    · have h2 : v i ≤ v j := hv.mono hij
      change v i - 1 ≤ v j - 1
      omega
    · have h2 := h i
      change (0 : ℤ) ≤ v i - 1
      omega
    · have h2 : v i ≤ (ℓ : ℤ) := hv.le i
      change v i - 1 ≤ (ℓ : ℤ)
      omega

/-- The cell pivoted at the bottom vertex: its vertices are those of the facet, together with
`vertex y σ 1 + 1`. -/
theorem isCell_pivot_bot (h : IsCell ℓ y σ) :
    IsCell ℓ (vertex y σ 1) (σ.trans (rotDown d)) ↔ ∀ i, vertex y σ 1 i < (ℓ : ℤ) := by
  rw [isCell_iff]
  constructor
  · intro H
    have := (isGridPt_add_one (h.isGridPt_vertex 1)).1 ?_
    · exact this
    · have := H d le_rfl
      rwa [vertex_of_le _ _ le_rfl] at this
  · intro H k hk
    rcases Nat.lt_or_ge k d with hkd | hkd
    · rw [vertex_rotDown y σ hkd]
      exact h.isGridPt_vertex _
    · rw [vertex_of_le _ _ hkd]
      exact (isGridPt_add_one (h.isGridPt_vertex 1)).2 H

/-- The base point of the cell pivoted at the top vertex is `vertex y σ (d-1)` lowered by one. -/
lemma pivot_top_base :
    (fun i ↦ y i - (if ((σ i : Fin d) : ℕ) + 1 = d then (1 : ℤ) else 0))
      = fun i ↦ vertex y σ (d - 1) i - 1 := by
  funext i
  have := (σ i).isLt
  simp only [vertex]
  split_ifs <;> omega

/-- The cell pivoted at the top vertex: its vertices are those of the facet, together with
`vertex y σ (d-1) - 1`. -/
theorem isCell_pivot_top (h : IsCell ℓ y σ) :
    IsCell ℓ (fun i ↦ y i - (if ((σ i : Fin d) : ℕ) + 1 = d then (1 : ℤ) else 0))
        (σ.trans (rotDown d).symm)
      ↔ ∀ i, 1 ≤ vertex y σ (d - 1) i := by
  rw [isCell_iff]
  constructor
  · intro H
    have h0 := H 0 (Nat.zero_le _)
    rw [vertex_zero, pivot_top_base] at h0
    exact (isGridPt_sub_one (h.isGridPt_vertex (d - 1))).1 h0
  · intro H k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [vertex_zero, pivot_top_base]
      exact (isGridPt_sub_one (h.isGridPt_vertex (d - 1))).2 H
    · rw [vertex_rotUp y σ hk0 hk]
      exact h.isGridPt_vertex _

/-- The cell pivoted at an intermediate vertex has the same base point, so only the order
condition can fail; and it fails exactly at a coordinate tie between the two transposed steps. -/
theorem exists_of_not_isCell_pivot_interior (h : IsCell ℓ y σ) {k : ℕ} (hk0 : 0 < k)
    (hkd : k < d)
    (hn : ¬ IsCell ℓ y (σ.trans (Equiv.swap (⟨k - 1, by omega⟩ : Fin d) ⟨k, hkd⟩))) :
    ∃ a b : Fin d, b < a ∧ ((σ a : Fin d) : ℕ) = k - 1 ∧ ((σ b : Fin d) : ℕ) = k ∧ y a = y b := by
  classical
  set A : Fin d := ⟨k - 1, by omega⟩ with hA
  set B : Fin d := ⟨k, hkd⟩ with hB
  have hAv : (A : ℕ) = k - 1 := by rw [hA]
  have hBv : (B : ℕ) = k := by rw [hB]
  have hval : ∀ t : Fin d, ((Equiv.swap A B (σ t) : Fin d) : ℕ)
      = if ((σ t : Fin d) : ℕ) = k - 1 then k else
          if ((σ t : Fin d) : ℕ) = k then k - 1 else ((σ t : Fin d) : ℕ) := by
    intro t
    rcases eq_or_ne (σ t) A with hA' | hA'
    · rw [hA', Equiv.swap_apply_left, hAv, hBv]
      simp
    · rcases eq_or_ne (σ t) B with hB' | hB'
      · rw [hB', Equiv.swap_apply_right, hAv, hBv]
        have hkk : ¬ (k = k - 1) := by omega
        simp [hkk]
      · rw [Equiv.swap_apply_of_ne_of_ne hA' hB']
        have h1 : ((σ t : Fin d) : ℕ) ≠ k - 1 := fun hc ↦ hA' (Fin.ext (by rw [hc, hAv]))
        have h2 : ((σ t : Fin d) : ℕ) ≠ k := fun hc ↦ hB' (Fin.ext (by rw [hc, hBv]))
        simp [h1, h2]
  by_contra hcon
  refine hn ⟨h.1, h.2.1, h.2.2.1, fun i j hij hyij ↦ ?_⟩
  rw [Fin.le_def]
  simp only [Equiv.trans_apply, hval]
  have hbase : ((σ j : Fin d) : ℕ) ≤ ((σ i : Fin d) : ℕ) := Fin.le_def.1 (h.2.2.2 i j hij hyij)
  have hne : ¬ (((σ j : Fin d) : ℕ) = k - 1 ∧ ((σ i : Fin d) : ℕ) = k) := by
    rintro ⟨h1, h2⟩
    exact hcon ⟨j, i, hij, h1, h2, hyij.symm⟩
  split_ifs <;> omega


/-! ### The doors that the pivot fixes

A door whose omitted vertex is not the bottom one always pivots to a cell: otherwise the whole
facet would sit inside a face `α_n = 0` with `n < d`, and no vertex of it could carry the colour
`n`, contradicting the door condition.  So the fixed doors are the bottom ones for which the
pivoted base point leaves the simplex, and those sit on the top face `α_d = 0`. -/

variable {φ : (Fin d → ℤ) → ℕ}

/-- A door with an intermediate omitted vertex pivots to a cell. -/
theorem isCell_pivot_of_isDoor_interior (hφ : IsAdmissible ℓ φ) {k : Fin (d + 1)}
    (hk : 0 < (k : ℕ) ∧ (k : ℕ) < d) (hdoor : IsDoor ℓ φ y σ k) :
    IsCell ℓ y (σ.trans (Equiv.swap (⟨(k : ℕ) - 1, by omega⟩ : Fin d) ⟨(k : ℕ), hk.2⟩)) := by
  by_contra hn
  obtain ⟨a, b, hba, hsa, hsb, hyab⟩ :=
    exists_of_not_isCell_pivot_interior hdoor.1 hk.1 hk.2 hn
  have hbd : ((b : Fin d) : ℕ) + 1 < d := lt_of_le_of_lt (by exact_mod_cast Fin.lt_def.1 hba) a.isLt
  obtain ⟨j, hjk, hj⟩ := hdoor.2 (((b : Fin d) : ℕ) + 1) hbd
  set v := vertex y σ ((j : Fin (d + 1)) : ℕ) with hv
  have hgrid : IsGridPt ℓ v := hdoor.1.isGridPt_vertex _
  have hjne : ((j : Fin (d + 1)) : ℕ) ≠ (k : ℕ) := fun hc ↦ hjk (Fin.ext hc)
  have hvab : v a = v b := by
    simp only [hv, vertex, hsa, hsb, hyab]
    have : (((k : ℕ) - 1 < ((j : Fin (d + 1)) : ℕ)) ↔ ((k : ℕ) < ((j : Fin (d + 1)) : ℕ))) := by
      omega
    simp only [this]
  have hstep : v b = v ⟨((b : Fin d) : ℕ) + 1, hbd⟩ := by
    have h1 : v b ≤ v ⟨((b : Fin d) : ℕ) + 1, hbd⟩ :=
      hgrid.mono (by simp [Fin.le_def])
    have h2 : v ⟨((b : Fin d) : ℕ) + 1, hbd⟩ ≤ v a :=
      hgrid.mono (by simp only [Fin.le_def]; exact_mod_cast Fin.lt_def.1 hba)
    omega
  have hadm := hφ v hgrid
  rw [hj] at hadm
  rw [IsAdmissibleAt, profile_apply_coe, profile_succ_of_lt v hbd] at hadm
  exact absurd hstep (by omega)

/-- A door whose omitted vertex is the top one pivots to a cell. -/
theorem isCell_pivot_of_isDoor_top (hd : 0 < d) (hφ : IsAdmissible ℓ φ) {k : Fin (d + 1)}
    (hk : (k : ℕ) = d) (hdoor : IsDoor ℓ φ y σ k) :
    IsCell ℓ (fun i ↦ y i - (if ((σ i : Fin d) : ℕ) + 1 = d then (1 : ℤ) else 0))
      (σ.trans (rotDown d).symm) := by
  rw [isCell_pivot_top hdoor.1]
  intro i
  by_contra hcon
  have hnn : 0 ≤ vertex y σ (d - 1) i := (hdoor.1.isGridPt_vertex _).nonneg i
  have hzero : vertex y σ (d - 1) (⟨0, hd⟩ : Fin d) = 0 := by
    have h1 : vertex y σ (d - 1) (⟨0, hd⟩ : Fin d) ≤ vertex y σ (d - 1) i :=
      (hdoor.1.isGridPt_vertex _).mono (by simp [Fin.le_def])
    have h2 : 0 ≤ vertex y σ (d - 1) (⟨0, hd⟩ : Fin d) := (hdoor.1.isGridPt_vertex _).nonneg _
    omega
  obtain ⟨j, hjk, hj⟩ := hdoor.2 0 hd
  have hjd : ((j : Fin (d + 1)) : ℕ) ≤ d - 1 := by
    have h4 := Nat.lt_succ_iff.1 (j : Fin (d + 1)).isLt
    have hne : ((j : Fin (d + 1)) : ℕ) ≠ d := fun hc ↦ hjk (Fin.ext (by omega))
    omega
  have hgrid : IsGridPt ℓ (vertex y σ ((j : Fin (d + 1)) : ℕ)) := hdoor.1.isGridPt_vertex _
  have hle : vertex y σ ((j : Fin (d + 1)) : ℕ) (⟨0, hd⟩ : Fin d) ≤ 0 := by
    have h3 := vertex_le_vertex (k := ((j : Fin (d + 1)) : ℕ)) (k' := d - 1) y σ hjd
      (⟨0, hd⟩ : Fin d)
    omega
  have hnn0 : 0 ≤ vertex y σ ((j : Fin (d + 1)) : ℕ) (⟨0, hd⟩ : Fin d) := hgrid.nonneg _
  have hadm := hφ _ hgrid
  rw [hj, IsAdmissibleAt, profile_zero, profile_succ_of_lt _ hd] at hadm
  omega

/-- A door with an intermediate omitted vertex pivots to a door. -/
theorem isDoor_pivot_interior (hφ : IsAdmissible ℓ φ) {k : Fin (d + 1)}
    (hk : 0 < (k : ℕ) ∧ (k : ℕ) < d) (hdoor : IsDoor ℓ φ y σ k) :
    IsDoor ℓ φ y (σ.trans (Equiv.swap (⟨(k : ℕ) - 1, by omega⟩ : Fin d) ⟨(k : ℕ), hk.2⟩)) k := by
  refine ⟨isCell_pivot_of_isDoor_interior hφ hk hdoor, fun c hc ↦ ?_⟩
  obtain ⟨j, hjk, hj⟩ := hdoor.2 c hc
  exact ⟨j, hjk, by rw [vertex_swap y σ hk.1 hk.2 (fun hcon ↦ hjk (Fin.ext hcon))]; exact hj⟩

/-- A door whose omitted vertex is the top one pivots to a door. -/
theorem isDoor_pivot_top (hd : 0 < d) (hφ : IsAdmissible ℓ φ) {k : Fin (d + 1)}
    (hk : (k : ℕ) = d) (hdoor : IsDoor ℓ φ y σ k) :
    IsDoor ℓ φ (fun i ↦ y i - (if ((σ i : Fin d) : ℕ) + 1 = d then (1 : ℤ) else 0))
      (σ.trans (rotDown d).symm) 0 := by
  refine ⟨isCell_pivot_of_isDoor_top hd hφ hk hdoor, fun c hc ↦ ?_⟩
  obtain ⟨j, hjk, hj⟩ := hdoor.2 c hc
  have hjd : ((j : Fin (d + 1)) : ℕ) < d := by
    have h4 := Nat.lt_succ_iff.1 (j : Fin (d + 1)).isLt
    have hne : ((j : Fin (d + 1)) : ℕ) ≠ d := fun hcon ↦ hjk (Fin.ext (by omega))
    omega
  refine ⟨⟨((j : Fin (d + 1)) : ℕ) + 1, by omega⟩, ?_, ?_⟩
  · intro hcon
    have h5 : ((j : Fin (d + 1)) : ℕ) + 1 = 0 := by
      have := congrArg Fin.val hcon
      simpa using this
    omega
  · rw [show (((⟨((j : Fin (d + 1)) : ℕ) + 1, by omega⟩ : Fin (d + 1)) : ℕ))
        = ((j : Fin (d + 1)) : ℕ) + 1 from rfl,
      vertex_rotUp y σ (Nat.succ_pos _) (by omega)]
    simpa using hj

/-- A door whose omitted vertex is the bottom one pivots to a door, as soon as the pivoted pair
spans a cell. -/
theorem isDoor_pivot_bot {k : Fin (d + 1)} (hk : (k : ℕ) = 0) (hdoor : IsDoor ℓ φ y σ k)
    (hcell : IsCell ℓ (vertex y σ 1) (σ.trans (rotDown d))) :
    IsDoor ℓ φ (vertex y σ 1) (σ.trans (rotDown d)) (Fin.last d) := by
  refine ⟨hcell, fun c hc ↦ ?_⟩
  obtain ⟨j, hjk, hj⟩ := hdoor.2 c hc
  have hj0 : 0 < ((j : Fin (d + 1)) : ℕ) := by
    have hne : ((j : Fin (d + 1)) : ℕ) ≠ 0 := fun hcon ↦ hjk (Fin.ext (by omega))
    omega
  have hjd : ((j : Fin (d + 1)) : ℕ) ≤ d := Nat.lt_succ_iff.1 (j : Fin (d + 1)).isLt
  refine ⟨⟨((j : Fin (d + 1)) : ℕ) - 1, by omega⟩, ?_, ?_⟩
  · simp only [ne_eq, Fin.ext_iff, Fin.val_last]
    omega
  · rw [show (((⟨((j : Fin (d + 1)) : ℕ) - 1, by omega⟩ : Fin (d + 1)) : ℕ))
        = ((j : Fin (d + 1)) : ℕ) - 1 from rfl,
      vertex_rotDown y σ (by omega : ((j : Fin (d + 1)) : ℕ) - 1 < d)]
    rw [show ((j : Fin (d + 1)) : ℕ) - 1 + 1 = ((j : Fin (d + 1)) : ℕ) by omega]
    exact hj


/-! ### The pivot as an involution of the set of doors -/

/-- The pivot as a self-map of the set of doors: a door whose pivot is again a door is sent to
it, a door whose pivot leaves the simplex is fixed. -/
def doorPivot (ℓ d : ℕ) (φ : (Fin d → ℤ) → ℕ)
    (p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :
    ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1) :=
  if pivot p ∈ doors ℓ d φ then pivot p else p

lemma doorPivot_mem {p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)}
    (hp : p ∈ doors ℓ d φ) : doorPivot ℓ d φ p ∈ doors ℓ d φ := by
  unfold doorPivot
  split_ifs with h
  · exact h
  · exact hp

lemma doorPivot_doorPivot {p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)}
    (hp : p ∈ doors ℓ d φ) : doorPivot ℓ d φ (doorPivot ℓ d φ p) = p := by
  by_cases h1 : pivot p ∈ doors ℓ d φ
  · have e1 : doorPivot ℓ d φ p = pivot p := by unfold doorPivot; rw [if_pos h1]
    have h2 : pivot (pivot p) ∈ doors ℓ d φ := by rw [pivot_pivot]; exact hp
    rw [e1]
    unfold doorPivot
    rw [if_pos h2, pivot_pivot]
  · have e1 : doorPivot ℓ d φ p = p := by unfold doorPivot; rw [if_neg h1]
    rw [e1, e1]

/-- The pivot never returns the same door. -/
lemma pivot_ne (hd : 0 < d) (p : ((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :
    pivot p ≠ p := by
  obtain ⟨⟨y, σ⟩, k⟩ := p
  have hkle : (k : ℕ) ≤ d := Nat.lt_succ_iff.1 k.isLt
  rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
  · rw [pivot_bot y σ k h0]
    intro hcon
    have := congrArg (fun q ↦ ((q.2 : Fin (d + 1)) : ℕ)) hcon
    simp only [Fin.val_last] at this
    omega
  · rcases eq_or_lt_of_le hkle with hlast | hint
    · rw [pivot_top y σ k hd hlast]
      intro hcon
      have := congrArg (fun q ↦ ((q.2 : Fin (d + 1)) : ℕ)) hcon
      simp only [Fin.val_zero] at this
      omega
    · rw [pivot_interior y σ k ⟨h0, hint⟩]
      intro hcon
      have h2 := congrArg (fun q ↦ q.1.2) hcon
      simp only at h2
      set A : Fin d := ⟨(k : ℕ) - 1, by omega⟩ with hA
      set B : Fin d := ⟨(k : ℕ), hint⟩ with hB
      have hAB : A ≠ B := by
        simp only [ne_eq, hA, hB, Fin.mk.injEq]
        omega
      have := congrArg (fun e ↦ e (σ.symm A)) h2
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_left] at this
      exact hAB this.symm

/-- The doors fixed by the pivot. -/
def fixedDoors (ℓ d : ℕ) (φ : (Fin d → ℤ) → ℕ) :
    Finset (((Fin d → ℤ) × Equiv.Perm (Fin d)) × Fin (d + 1)) :=
  (doors ℓ d φ).filter fun p ↦ doorPivot ℓ d φ p = p

/-- **The fixed doors count the doors modulo `2`.** -/
lemma card_doors_mod_two_fixed :
    (doors ℓ d φ).card % 2 = (fixedDoors ℓ d φ).card % 2 :=
  card_mod_two_eq_card_filter_fixed _ _ (fun _ hx ↦ doorPivot_mem hx)
    (fun _ hx ↦ doorPivot_doorPivot hx)

/-- If the pivot of a door leaves the simplex, the omitted vertex was the bottom one, and the
base point of the pivoted cell reaches the top of the simplex. -/
lemma exists_of_not_isCell_pivot_bot (h : IsCell ℓ y σ)
    (hn : ¬ IsCell ℓ (vertex y σ 1) (σ.trans (rotDown d))) :
    ∃ i, ((σ i : Fin d) : ℕ) = 0 ∧ y i + 1 = (ℓ : ℤ) := by
  rw [isCell_pivot_bot h] at hn
  simp only [not_forall, not_lt] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ?_, ?_⟩
  · by_contra hcon
    have h1 : vertex y σ 1 i = y i := by simp [vertex, Nat.lt_one_iff, hcon]
    have := h.2.2.1 i
    omega
  · have h1 : vertex y σ 1 i ≤ y i + 1 := vertex_le_succ y σ 1 i
    have h2 := h.2.2.1 i
    omega

/-- The coordinate at which a fixed bottom door reaches the top of the simplex is the last
one. -/
lemma eq_last_of_isCell_of_sigma_zero (hd : 0 < d) (h : IsCell ℓ y σ) {i : Fin d}
    (hσ : ((σ i : Fin d) : ℕ) = 0) (hy : y i + 1 = (ℓ : ℤ)) : ((i : Fin d) : ℕ) = d - 1 := by
  by_contra hcon
  have hid := i.isLt
  have hjlt : d - 1 < d := by omega
  have hij : i < (⟨d - 1, hjlt⟩ : Fin d) := by
    rw [Fin.lt_def]
    change (i : ℕ) < d - 1
    omega
  have hy1 : y i ≤ y ⟨d - 1, hjlt⟩ := h.1 i _ (le_of_lt hij)
  have hy2 : y ⟨d - 1, hjlt⟩ < (ℓ : ℤ) := h.2.2.1 _
  have hyij : y i = y ⟨d - 1, hjlt⟩ := by omega
  have hle : ((σ ⟨d - 1, hjlt⟩ : Fin d) : ℕ) ≤ ((σ i : Fin d) : ℕ) :=
    Fin.le_def.1 (h.2.2.2 i _ hij hyij)
  have heq : σ ⟨d - 1, hjlt⟩ = σ i := Fin.ext (by omega)
  exact absurd (σ.injective heq).symm (ne_of_lt hij)


/-! ### The top face

The fixed doors are exactly the cells of the top face `α_d = 0`, read in one dimension less. -/

lemma snoc_apply {e : ℕ} (y : Fin e → ℤ) (L : ℤ) (i : Fin (e + 1)) :
    Fin.snoc (α := fun _ ↦ ℤ) y L i = if h : (i : ℕ) < e then y ⟨(i : ℕ), h⟩ else L := by
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro m; simp

/-- The colouring induced on the top face `α_d = 0` of the simplex. -/
def faceColour (ℓ e : ℕ) (φ : (Fin (e + 1) → ℤ) → ℕ) : (Fin e → ℤ) → ℕ :=
  fun y ↦ φ (Fin.snoc y (ℓ : ℤ))

lemma profile_snoc {e : ℕ} (y : Fin e → ℤ) :
    profile ℓ (Fin.snoc y (ℓ : ℤ)) = profile ℓ y := by
  funext n
  cases n with
  | zero => rfl
  | succ m =>
    by_cases h : m < e
    · rw [profile_succ_of_lt _ (by omega : m < e + 1), profile_succ_of_lt _ h, snoc_apply]
      simp [h]
    · by_cases h' : m = e
      · subst h'
        rw [profile_succ_of_lt _ (by omega : m < m + 1), profile_succ_of_le _ le_rfl, snoc_apply]
        simp
      · rw [profile_succ_of_le _ (by omega : e + 1 ≤ m), profile_succ_of_le _ (by omega : e ≤ m)]

lemma isGridPt_snoc {e : ℕ} {y : Fin e → ℤ} (hℓ : 0 ≤ (ℓ : ℤ)) (h : IsGridPt ℓ y) :
    IsGridPt ℓ (Fin.snoc y (ℓ : ℤ)) := by
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩ <;> simp only [snoc_apply]
  · have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.1 hij
    split_ifs with h1 h2 h2
    · exact h.mono (Fin.mk_le_mk.2 hij')
    · exact h.le _
    · omega
    · exact le_rfl
  · split_ifs with h1
    · exact h.nonneg _
    · exact hℓ
  · split_ifs with h1
    · exact h.le _
    · exact le_rfl

lemma isAdmissible_faceColour {e : ℕ} {φ : (Fin (e + 1) → ℤ) → ℕ} (hℓ : 0 ≤ (ℓ : ℤ))
    (hφ : IsAdmissible ℓ φ) : IsAdmissible ℓ (faceColour ℓ e φ) := by
  intro y hy
  have := hφ (Fin.snoc y (ℓ : ℤ)) (isGridPt_snoc hℓ hy)
  rwa [IsAdmissibleAt, profile_snoc] at this

/-- The permutation of `Fin (e+1)` that sends the last coordinate to `0` and `castSucc m` to
`succ (τ m)`: the step order of a cell of the top face, read as a cell of the whole simplex whose
very first step is the last coordinate. -/
def liftPerm {e : ℕ} (τ : Equiv.Perm (Fin e)) : Equiv.Perm (Fin (e + 1)) where
  toFun := Fin.lastCases 0 fun m ↦ (τ m).succ
  invFun := Fin.cases (Fin.last e) fun t ↦ (τ.symm t).castSucc
  left_inv i := by
    refine Fin.lastCases ?_ ?_ i <;> simp
  right_inv i := by
    refine Fin.cases ?_ ?_ i <;> simp

@[simp] lemma liftPerm_last {e : ℕ} (τ : Equiv.Perm (Fin e)) : liftPerm τ (Fin.last e) = 0 := by
  simp [liftPerm]

@[simp] lemma liftPerm_castSucc {e : ℕ} (τ : Equiv.Perm (Fin e)) (m : Fin e) :
    liftPerm τ m.castSucc = (τ m).succ := by
  simp [liftPerm]

lemma coe_liftPerm_apply {e : ℕ} (τ : Equiv.Perm (Fin e)) (i : Fin (e + 1)) :
    ((liftPerm τ i : Fin (e + 1)) : ℕ)
      = if h : (i : ℕ) < e then ((τ ⟨(i : ℕ), h⟩ : Fin e) : ℕ) + 1 else 0 := by
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro m; simp

lemma vertex_liftPerm {e : ℕ} (y : Fin e → ℤ) (τ : Equiv.Perm (Fin e)) (L : ℤ) (j : ℕ) :
    vertex (Fin.snoc y L) (liftPerm τ) (j + 1) = Fin.snoc (vertex y τ j) (L + 1) := by
  funext i
  simp only [vertex, snoc_apply, coe_liftPerm_apply]
  split_ifs <;> omega

/-- A cell of the top face lifts to a cell of the simplex whose bottom vertex sits on that
face. -/
lemma isCell_liftPerm {e : ℕ} (hℓ : 1 ≤ ℓ) {y : Fin e → ℤ} {τ : Equiv.Perm (Fin e)}
    (h : IsCell ℓ y τ) : IsCell ℓ (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ) := by
  have hℓ' : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, fun i j hij hyij ↦ ?_⟩
  · simp only [snoc_apply]
    have hij' : (i : ℕ) ≤ (j : ℕ) := Fin.le_def.1 hij
    split_ifs with h1 h2 h2
    · exact h.1 _ _ (Fin.mk_le_mk.2 hij')
    · have := h.2.2.1 (⟨(i : ℕ), h1⟩ : Fin e); omega
    · omega
    · exact le_rfl
  · simp only [snoc_apply]
    split_ifs with h1
    · exact h.2.1 _
    · omega
  · simp only [snoc_apply]
    split_ifs with h1
    · exact h.2.2.1 _
    · omega
  · rw [Fin.le_def, coe_liftPerm_apply, coe_liftPerm_apply]
    have hij' : (i : ℕ) < (j : ℕ) := Fin.lt_def.1 hij
    have hjle : (j : ℕ) ≤ e := Nat.lt_succ_iff.1 j.isLt
    by_cases h2 : (j : ℕ) < e
    · have h1 : (i : ℕ) < e := by omega
      rw [dif_pos h1, dif_pos h2]
      simp only [snoc_apply, dif_pos h1, dif_pos h2] at hyij
      have h3 := Fin.le_def.1 (h.2.2.2 ⟨(i : ℕ), h1⟩ ⟨(j : ℕ), h2⟩ (Fin.mk_lt_mk.2 hij') hyij)
      omega
    · rw [dif_neg h2]
      exact Nat.zero_le _

/-- The fixed door attached to a cell of the top face. -/
def liftCell (ℓ e : ℕ) (q : (Fin e → ℤ) × Equiv.Perm (Fin e)) :
    ((Fin (e + 1) → ℤ) × Equiv.Perm (Fin (e + 1))) × Fin (e + 2) :=
  ((Fin.snoc q.1 ((ℓ : ℤ) - 1), liftPerm q.2), 0)


/-- **The fixed doors are exactly the panchromatic cells of the top face.** -/
theorem card_panchromaticCells_face {e : ℕ} (hℓ : 1 ≤ ℓ) {φ : (Fin (e + 1) → ℤ) → ℕ}
    (hφ : IsAdmissible ℓ φ) :
    (panchromaticCells ℓ e (faceColour ℓ e φ)).card = (fixedDoors ℓ (e + 1) φ).card := by
  classical
  have hℓ' : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  refine Finset.card_bij (fun q _ ↦ liftCell ℓ e q) ?_ ?_ ?_
  · rintro ⟨y, τ⟩ hq
    rw [mem_panchromaticCells] at hq
    obtain ⟨hcell, hpan⟩ := hq
    simp only at hcell hpan
    have hLcell : IsCell ℓ (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ) := isCell_liftPerm hℓ hcell
    have hdoor : IsDoor ℓ φ (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ) 0 := by
      refine ⟨hLcell, fun c hc ↦ ?_⟩
      obtain ⟨j', hj'⟩ := hpan c (Nat.lt_succ_iff.1 hc)
      have hj'lt := (j' : Fin (e + 1)).isLt
      refine ⟨⟨((j' : Fin (e + 1)) : ℕ) + 1, by omega⟩, ?_, ?_⟩
      · intro hcon
        have h2 := congrArg Fin.val hcon
        simp only [Fin.val_zero] at h2
        omega
      · show φ (vertex (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ)
          (((j' : Fin (e + 1)) : ℕ) + 1)) = c
        rw [vertex_liftPerm y τ ((ℓ : ℤ) - 1) ((j' : Fin (e + 1)) : ℕ),
          show (ℓ : ℤ) - 1 + 1 = (ℓ : ℤ) by omega]
        exact hj'
    have hval : vertex (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ) 1 (Fin.last e) = (ℓ : ℤ) := by
      simp [vertex]
    have hnotmem : pivot (liftCell ℓ e (y, τ)) ∉ doors ℓ (e + 1) φ := by
      intro hmem
      rw [liftCell, pivot_bot (Fin.snoc y ((ℓ : ℤ) - 1)) (liftPerm τ) 0 rfl] at hmem
      have hc2 := (mem_doors.1 hmem).1
      rw [isCell_pivot_bot hLcell] at hc2
      have h3 := hc2 (Fin.last e)
      rw [hval] at h3
      omega
    rw [fixedDoors, Finset.mem_filter]
    refine ⟨mem_doors.2 hdoor, ?_⟩
    unfold doorPivot
    rw [if_neg hnotmem]
  · rintro ⟨y₁, τ₁⟩ - ⟨y₂, τ₂⟩ - heq
    rw [liftCell, liftCell, Prod.mk.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2⟩, -⟩ := heq
    refine Prod.ext ?_ ?_
    · funext m
      have h3 := congrFun h1 m.castSucc
      simp only [Fin.snoc_castSucc] at h3
      exact h3
    · refine Equiv.ext fun m ↦ ?_
      have h3 := congrArg (fun E : Equiv.Perm (Fin (e + 1)) ↦ E m.castSucc) h2
      simp only [liftPerm_castSucc] at h3
      exact Fin.succ_injective _ h3
  · rintro ⟨⟨y, σ⟩, k⟩ hb
    rw [fixedDoors, Finset.mem_filter] at hb
    obtain ⟨hmem, hfix⟩ := hb
    have hdoor := mem_doors.1 hmem
    simp only at hdoor
    have hpivot_not : pivot ((y, σ), k) ∉ doors ℓ (e + 1) φ := by
      intro hcon
      have heq : doorPivot ℓ (e + 1) φ ((y, σ), k) = pivot ((y, σ), k) := by
        unfold doorPivot; rw [if_pos hcon]
      rw [heq] at hfix
      exact pivot_ne (by omega) _ hfix
    have hk0 : ((k : Fin (e + 2)) : ℕ) = 0 := by
      by_contra hk
      have hkle : ((k : Fin (e + 2)) : ℕ) ≤ e + 1 := Nat.lt_succ_iff.1 k.isLt
      rcases eq_or_lt_of_le hkle with hlast | hint
      · refine hpivot_not ?_
        rw [pivot_top y σ k (by omega) hlast]
        exact mem_doors.2 (isDoor_pivot_top (by omega) hφ hlast hdoor)
      · refine hpivot_not ?_
        rw [pivot_interior y σ k ⟨by omega, hint⟩]
        exact mem_doors.2 (isDoor_pivot_interior hφ ⟨by omega, hint⟩ hdoor)
    have hnotcell : ¬ IsCell ℓ (vertex y σ 1) (σ.trans (rotDown (e + 1))) := by
      intro hcell
      refine hpivot_not ?_
      rw [pivot_bot y σ k hk0]
      exact mem_doors.2 (isDoor_pivot_bot hk0 hdoor hcell)
    obtain ⟨i, hσi, hyi⟩ := exists_of_not_isCell_pivot_bot hdoor.1 hnotcell
    have hie : ((i : Fin (e + 1)) : ℕ) = e := by
      have := eq_last_of_isCell_of_sigma_zero (by omega) hdoor.1 hσi hyi
      omega
    have hilast : i = Fin.last e := Fin.ext (by simpa using hie)
    have hσlast : σ (Fin.last e) = 0 := by rw [← hilast]; exact Fin.ext hσi
    have hylast : y (Fin.last e) = (ℓ : ℤ) - 1 := by rw [← hilast]; omega
    have hne : ∀ m : Fin e, ((σ m.castSucc : Fin (e + 1)) : ℕ) ≠ 0 := by
      intro m hcon
      have h1 : σ m.castSucc = σ (Fin.last e) := by rw [hσlast]; exact Fin.ext hcon
      have h3 := congrArg Fin.val (σ.injective h1)
      simp only [Fin.val_castSucc, Fin.val_last] at h3
      exact absurd h3 (Nat.ne_of_lt m.isLt)
    have hbound : ∀ m : Fin e, ((σ m.castSucc : Fin (e + 1)) : ℕ) - 1 < e := by
      intro m
      have h1 := Nat.lt_succ_iff.1 (σ m.castSucc).isLt
      have h2 := hne m
      have h3 := m.isLt
      omega
    set f : Fin e → Fin e := fun m ↦ ⟨((σ m.castSucc : Fin (e + 1)) : ℕ) - 1, hbound m⟩ with hf
    have hfval : ∀ m, ((f m : Fin e) : ℕ) = ((σ m.castSucc : Fin (e + 1)) : ℕ) - 1 :=
      fun m ↦ rfl
    have hfinj : Function.Injective f := by
      intro m m' hmm
      have h1 := hne m
      have h2 := hne m'
      have h3 : ((f m : Fin e) : ℕ) = ((f m' : Fin e) : ℕ) := congrArg Fin.val hmm
      rw [hfval, hfval] at h3
      have h4 : σ m.castSucc = σ m'.castSucc := Fin.ext (by omega)
      exact Fin.castSucc_injective _ (σ.injective h4)
    set τ : Equiv.Perm (Fin e) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
      with hτdef
    have hτval : ∀ m, ((τ m : Fin e) : ℕ) = ((σ m.castSucc : Fin (e + 1)) : ℕ) - 1 := fun m ↦ rfl
    have hlift : liftPerm τ = σ := by
      refine Equiv.ext fun t ↦ ?_
      refine Fin.lastCases ?_ ?_ t
      · rw [liftPerm_last, hσlast]
      · intro m
        rw [liftPerm_castSucc]
        refine Fin.ext ?_
        rw [Fin.val_succ, hτval]
        have := hne m
        omega
    have hsnoc : Fin.snoc (Fin.init y) ((ℓ : ℤ) - 1) = y := by
      rw [← hylast]; exact Fin.snoc_init_self y
    have hinitcell : IsCell ℓ (Fin.init y) τ := by
      refine ⟨fun m m' hmm ↦ hdoor.1.1 _ _ (Fin.castSucc_le_castSucc_iff.2 hmm),
        fun m ↦ hdoor.1.2.1 _, fun m ↦ hdoor.1.2.2.1 _, fun m m' hmm hyy ↦ ?_⟩
      rw [Fin.le_def, hτval, hτval]
      have h1 := hne m
      have h2 := hne m'
      have h3 := Fin.le_def.1 (hdoor.1.2.2.2 m.castSucc m'.castSucc
        (Fin.castSucc_lt_castSucc_iff.2 hmm) hyy)
      omega
    have hpan : IsPanchromatic (faceColour ℓ e φ) (Fin.init y) τ := by
      intro c hc
      obtain ⟨j, hjk, hj⟩ := hdoor.2 c (by omega)
      have hj0 : ((j : Fin (e + 2)) : ℕ) ≠ 0 := fun hcon ↦ hjk (Fin.ext (by omega))
      have hjle : ((j : Fin (e + 2)) : ℕ) ≤ e + 1 := Nat.lt_succ_iff.1 j.isLt
      refine ⟨⟨((j : Fin (e + 2)) : ℕ) - 1, by omega⟩, ?_⟩
      change φ (Fin.snoc (vertex (Fin.init y) τ (((j : Fin (e + 2)) : ℕ) - 1)) (ℓ : ℤ)) = c
      rw [show (ℓ : ℤ) = ((ℓ : ℤ) - 1) + 1 by omega,
        ← vertex_liftPerm (Fin.init y) τ ((ℓ : ℤ) - 1) (((j : Fin (e + 2)) : ℕ) - 1), hlift,
        hsnoc, show ((j : Fin (e + 2)) : ℕ) - 1 + 1 = ((j : Fin (e + 2)) : ℕ) by omega]
      exact hj
    refine ⟨(Fin.init y, τ), mem_panchromaticCells.2 ⟨hinitcell, hpan⟩, ?_⟩
    rw [liftCell]
    simp only
    rw [hlift, hsnoc]
    exact Prod.ext rfl (Fin.ext hk0.symm)

/-- **Sperner's lemma.**  Relative to an admissible colouring of the grid of mesh `ℓ ≥ 1`, the
number of panchromatic cells of the standard triangulation of `ℓ·Δ^d` is odd. -/
theorem odd_card_panchromaticCells (hℓ : 1 ≤ ℓ) (d : ℕ) (φ : (Fin d → ℤ) → ℕ)
    (hφ : IsAdmissible ℓ φ) : Odd (panchromaticCells ℓ d φ).card := by
  induction d with
  | zero =>
    have h1 : panchromaticCells ℓ 0 φ = cells ℓ 0 := by
      refine Finset.filter_true_of_mem fun p hp ↦ ?_
      intro c hc
      refine ⟨0, ?_⟩
      have h2 := (hφ p.1 (mem_cells.1 hp).isGridPt).le
      have h3 : φ (vertex p.1 p.2 ((0 : Fin 1) : ℕ)) = φ p.1 := by
        rw [show (((0 : Fin 1)) : ℕ) = 0 from rfl, vertex_zero]
      omega
    have h4 : cells ℓ 0 = {((fun _ ↦ (0 : ℤ)), Equiv.refl (Fin 0))} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨mem_cells.2 ?_, fun x _ ↦ ?_⟩
      · exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
      · exact Prod.ext (funext fun i ↦ i.elim0) (Equiv.ext fun i ↦ i.elim0)
    rw [h1, h4, Finset.card_singleton]
    exact ⟨0, rfl⟩
  | succ e ih =>
    have h1 := card_doors_mod_two (φ := φ) hφ
    have h2 : (doors ℓ (e + 1) φ).card % 2 = (fixedDoors ℓ (e + 1) φ).card % 2 :=
      card_doors_mod_two_fixed
    have h3 := card_panchromaticCells_face hℓ hφ
    have h4 := ih (faceColour ℓ e φ)
      (isAdmissible_faceColour (by exact_mod_cast Nat.zero_le ℓ) hφ)
    rw [Nat.odd_iff] at h4 ⊢
    omega

/-- **Sperner's lemma**, in the form used to prove the Knaster–Kuratowski–Mazurkiewicz lemma:
some cell of the triangulation shows all `d + 1` colours. -/
theorem exists_isPanchromatic (hℓ : 1 ≤ ℓ) (d : ℕ) (φ : (Fin d → ℤ) → ℕ)
    (hφ : IsAdmissible ℓ φ) : ∃ y σ, IsCell ℓ y σ ∧ IsPanchromatic φ y σ := by
  obtain ⟨m, hm⟩ := odd_card_panchromaticCells hℓ d φ hφ
  have hne : (panchromaticCells ℓ d φ).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p, hp⟩ := hne
  exact ⟨p.1, p.2, (mem_panchromaticCells.1 hp).1, (mem_panchromaticCells.1 hp).2⟩

end Sperner

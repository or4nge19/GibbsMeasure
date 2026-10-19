/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Order.Filter.AtTopBot.Finset
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The Neumann series of a nonnegative matrix over `ℝ≥0∞`

A function `C : α → α → ℝ≥0∞` on an arbitrary type `α` acts on vectors `a : α → ℝ≥0∞` by
`(C a)_i = ∑' j, C i j * a j`. Because `ℝ≥0∞` is a complete linearly ordered semiring in which
every family is summable, this action needs no finiteness or measurability assumption on `α`,
and its iterates and Neumann series `D = ∑_{n ≥ 0} C^n` are always defined.

If the row sums of `C` are at most `c` then `∑_j (C^n)_{ij} ≤ c^n`, so for `c < 1` the series
`D` has row sums at most `(1 - c)⁻¹` and the weight it puts far away from a finite set is small.
These estimates are the engine behind the convergence of Dobrushin-type iterations.

## Main definitions

* `ENNReal.matIter C n a`: the `n`-fold action `C^n a`.
* `ENNReal.matSeries C a`: the Neumann series `D a = ∑_{n ≥ 0} C^n a`.
* `ENNReal.matEntry C i j`: the entry `D_ij`, so that `(D a)_i = ∑_j D_ij a_j`
  (`ENNReal.matSeries_eq_tsum_matEntry`).
* `ENNReal.matTail C Δ i = ∑_{j ∉ Δ} D_ij`: the weight `D` puts outside a finite set.

## Main results

* `ENNReal.matIter_le`, `ENNReal.matSeries_le`, `ENNReal.tsum_matEntry_le`: the row-sum bounds
  `C^n a ≤ (sup a) c^n`, `D a ≤ (sup a)/(1 - c)` and `∑_j D_ij ≤ (1 - c)⁻¹`.
* `ENNReal.matIter_add`, `ENNReal.matIter_const_mul`, `ENNReal.matIter_tsum` and their
  `matSeries` counterparts: the action is additive, homogeneous and commutes with countable sums.
* `ENNReal.tsum_tsum_matSeries_mul`: the Neumann series of a countable sum of vectors,
  tested against a weight, may be summed term by term.
* `ENNReal.matIter_eq_zero_of_lt`, `ENNReal.matSeries_le_pow_of_le`: locality — if one step of
  `C` lowers a "distance to the support of `b`" `ρ : α → ℕ∞` by at most one, then `C^n b`
  vanishes where `ρ > n`, and `(D b)_i ≤ (sup b) c^k/(1 − c)` for `k ≤ ρ i`.
* `ENNReal.matEntry_le_pow_of_le_edist`, `ENNReal.matEntry_le_pow_dist`: **graph-distance decay of
  the Neumann series** — if `C` vanishes off the edges and the diagonal of a simple graph `G`,
  then `D_ij ≤ c^{d_G(i,j)}/(1 − c)`.
* `ENNReal.tendsto_matTail`: for `c < 1` the tail weight `∑_{j ∉ Δ} D_ij` vanishes as `Δ ↑ α`.
* `ENNReal.tsum_matSeries_mul_ne_top`: finiteness of `∑_i (D v)_i w_i` for a bounded `v` and a
  summable `w`.
* `ENNReal.tendsto_tsum_matSeries_mul`, `ENNReal.tendsto_tsum_matTail_mul`: the two forms of
  dominated convergence for `∑_i (D v)_i w_i` used in applications.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ENNReal Topology

namespace ENNReal

variable {α : Type*}

section MatIter


variable {C C' : α → α → ℝ≥0∞} {c : ℝ≥0∞}

/-- `C^n a`, the `n`-fold action of a nonnegative matrix `C` on a vector `a`. -/
noncomputable def matIter (C : α → α → ℝ≥0∞) : ℕ → (α → ℝ≥0∞) → α → ℝ≥0∞
  | 0, a => a
  | (n + 1), a => fun i ↦ ∑' j, C i j * matIter C n a j

@[simp] lemma matIter_zero (C : α → α → ℝ≥0∞) (a : α → ℝ≥0∞) : matIter C 0 a = a := rfl

lemma matIter_succ (C : α → α → ℝ≥0∞) (n : ℕ) (a : α → ℝ≥0∞) (i : α) :
    matIter C (n + 1) a i = ∑' j, C i j * matIter C n a j := rfl

/-- If the row sums of `C` are at most `c` and `a ≤ M` pointwise, then `C^n a ≤ M c^n`. -/
lemma matIter_le (hc : ∀ i, ∑' j, C i j ≤ c) {a : α → ℝ≥0∞} {M : ℝ≥0∞} (ha : ∀ j, a j ≤ M)
    (n : ℕ) (i : α) : matIter C n a i ≤ M * c ^ n := by
  induction n generalizing i with
  | zero => simpa using ha i
  | succ n ih =>
      calc matIter C (n + 1) a i = ∑' j, C i j * matIter C n a j := rfl
        _ ≤ ∑' j, C i j * (M * c ^ n) :=
            ENNReal.tsum_le_tsum fun j ↦ by gcongr; exact ih j
        _ = (∑' j, C i j) * (M * c ^ n) := ENNReal.tsum_mul_right
        _ ≤ c * (M * c ^ n) := by gcongr; exact hc i
        _ = M * c ^ (n + 1) := by ring

/-- `C^n` is monotone in the matrix. -/
lemma matIter_mono_matrix (h : ∀ i j, C' i j ≤ C i j) (n : ℕ) (a : α → ℝ≥0∞) (i : α) :
    matIter C' n a i ≤ matIter C n a i := by
  induction n generalizing i with
  | zero => exact le_rfl
  | succ n ih => exact ENNReal.tsum_le_tsum fun j ↦ mul_le_mul' (h i j) (ih j)

/-- `C^n` is monotone in the vector. -/
lemma matIter_mono_vec (C : α → α → ℝ≥0∞) {a b : α → ℝ≥0∞} (hab : ∀ j, a j ≤ b j) (n : ℕ)
    (i : α) : matIter C n a i ≤ matIter C n b i := by
  induction n generalizing i with
  | zero => exact hab i
  | succ n ih => exact ENNReal.tsum_le_tsum fun j ↦ mul_le_mul' le_rfl (ih j)

/-- `C^n` is additive in the vector. -/
lemma matIter_add (C : α → α → ℝ≥0∞) (a b : α → ℝ≥0∞) (n : ℕ) (i : α) :
    matIter C n (a + b) i = matIter C n a i + matIter C n b i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp only [matIter_succ]
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun j ↦ by rw [ih j, mul_add]

/-- `C^n` is homogeneous: `C^n (c a) = c (C^n a)`. -/
lemma matIter_const_mul (C : α → α → ℝ≥0∞) (c : ℝ≥0∞) (a : α → ℝ≥0∞) (n : ℕ) (i : α) :
    matIter C n (fun j ↦ c * a j) i = c * matIter C n a i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      calc matIter C (n + 1) (fun j ↦ c * a j) i
          = ∑' j, C i j * matIter C n (fun j ↦ c * a j) j := rfl
        _ = ∑' j, c * (C i j * matIter C n a j) := by
            exact tsum_congr fun j ↦ by rw [ih j]; ring
        _ = c * matIter C (n + 1) a i := by
            rw [ENNReal.tsum_mul_left]; rfl

/-- `C^n` commutes with countable sums of vectors (Tonelli). -/
lemma matIter_tsum {ι : Type*} (C : α → α → ℝ≥0∞) (a : ι → α → ℝ≥0∞) (n : ℕ) (i : α) :
    matIter C n (fun j ↦ ∑' k, a k j) i = ∑' k, matIter C n (a k) i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      calc matIter C (n + 1) (fun j ↦ ∑' k, a k j) i
          = ∑' j, C i j * ∑' k, matIter C n (a k) j := by
            simp only [matIter_succ]
            exact tsum_congr fun j ↦ by rw [ih j]
        _ = ∑' j, ∑' k, C i j * matIter C n (a k) j := by
            exact tsum_congr fun j ↦ ENNReal.tsum_mul_left.symm
        _ = ∑' k, ∑' j, C i j * matIter C n (a k) j := ENNReal.tsum_comm
        _ = ∑' k, matIter C (n + 1) (a k) i := rfl

/-- The Neumann series `D b = ∑_{n ≥ 0} C^n b`. -/
noncomputable def matSeries (C : α → α → ℝ≥0∞) (bt : α → ℝ≥0∞) (i : α) : ℝ≥0∞ :=
  ∑' n : ℕ, matIter C n bt i

/-- The `n = 0` term of the Neumann series: `b ≤ D b`. -/
lemma le_matSeries (C : α → α → ℝ≥0∞) (bt : α → ℝ≥0∞) (i : α) : bt i ≤ matSeries C bt i :=
  le_trans (le_of_eq rfl) (ENNReal.le_tsum (f := fun n ↦ matIter C n bt i) 0)

/-- **The row-sum bound for the Neumann series** of a matrix with row sums at most `c < 1`:
`∑_j D_ij b_j ≤ (sup_j b_j)/(1 − c)`. -/
lemma matSeries_le (hc : ∀ i, ∑' j, C i j ≤ c) {b : α → ℝ≥0∞} {B : ℝ≥0∞} (hb : ∀ j, b j ≤ B)
    (i : α) : matSeries C b i ≤ B / (1 - c) :=
  calc matSeries C b i = ∑' n : ℕ, matIter C n b i := rfl
    _ ≤ ∑' n : ℕ, B * c ^ n := ENNReal.tsum_le_tsum fun n ↦ matIter_le hc hb n i
    _ = B * ∑' n : ℕ, c ^ n := ENNReal.tsum_mul_left
    _ = B * (1 - c)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ = B / (1 - c) := (div_eq_mul_inv _ _).symm

lemma matSeries_mono_matrix (h : ∀ i j, C' i j ≤ C i j) (a : α → ℝ≥0∞) (i : α) :
    matSeries C' a i ≤ matSeries C a i :=
  ENNReal.tsum_le_tsum fun n ↦ matIter_mono_matrix h n a i

lemma matSeries_mono_vec (C : α → α → ℝ≥0∞) {a b : α → ℝ≥0∞} (hab : ∀ j, a j ≤ b j) (i : α) :
    matSeries C a i ≤ matSeries C b i :=
  ENNReal.tsum_le_tsum fun n ↦ matIter_mono_vec C hab n i

lemma matSeries_add (C : α → α → ℝ≥0∞) (a b : α → ℝ≥0∞) (i : α) :
    matSeries C (a + b) i = matSeries C a i + matSeries C b i := by
  rw [matSeries, matSeries, matSeries, ← ENNReal.tsum_add]
  exact tsum_congr fun n ↦ matIter_add C a b n i

/-- The Neumann series is homogeneous: `D (c b) = c (D b)`. -/
lemma matSeries_const_mul (C : α → α → ℝ≥0∞) (c : ℝ≥0∞) (a : α → ℝ≥0∞) (i : α) :
    matSeries C (fun j ↦ c * a j) i = c * matSeries C a i := by
  rw [matSeries, matSeries, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n ↦ matIter_const_mul C c a n i

/-- The Neumann series commutes with countable sums of vectors (Tonelli). -/
lemma matSeries_tsum {ι : Type*} (C : α → α → ℝ≥0∞) (a : ι → α → ℝ≥0∞) (i : α) :
    matSeries C (fun j ↦ ∑' k, a k j) i = ∑' k, matSeries C (a k) i := by
  simp only [matSeries]
  rw [tsum_congr fun n ↦ matIter_tsum C a n i]
  exact ENNReal.tsum_comm

/-- Testing the Neumann series of a countable sum of vectors against a weight `w` may be done
term by term. -/
lemma tsum_tsum_matSeries_mul {ι : Type*} (C : α → α → ℝ≥0∞) (a : ι → α → ℝ≥0∞)
    (w : α → ℝ≥0∞) :
    ∑' k, ∑' i, matSeries C (a k) i * w i
      = ∑' i, matSeries C (fun j ↦ ∑' k, a k j) i * w i := by
  calc ∑' k, ∑' i, matSeries C (a k) i * w i
      = ∑' i, ∑' k, matSeries C (a k) i * w i := ENNReal.tsum_comm
    _ = ∑' i, (∑' k, matSeries C (a k) i) * w i := tsum_congr fun i ↦ ENNReal.tsum_mul_right
    _ = ∑' i, matSeries C (fun j ↦ ∑' k, a k j) i * w i :=
        tsum_congr fun i ↦ by rw [matSeries_tsum]

variable (C) in
/-- The matrix `D = ∑_{n ≥ 0} C^n`, entrywise: `D_ij` is the value at `i` of the Neumann series
applied to the indicator of `j`. -/
noncomputable def matEntry (i j : α) : ℝ≥0∞ :=
  matSeries C (({j} : Set α).indicator fun _ ↦ 1) i

/-- The Neumann series acts on vectors as the matrix `D`: `(D b)_i = ∑_j D_ij b_j`. -/
lemma matSeries_eq_tsum_matEntry (C : α → α → ℝ≥0∞) (v : α → ℝ≥0∞) (i : α) :
    matSeries C v i = ∑' j, matEntry C i j * v j := by
  have hv : v = fun k ↦ ∑' j, v j * ({j} : Set α).indicator (fun _ ↦ (1 : ℝ≥0∞)) k := by
    funext k
    rw [tsum_eq_single k fun j hj ↦ by
      rw [Set.indicator_of_notMem (by simpa using Ne.symm hj), mul_zero]]
    rw [Set.indicator_of_mem (Set.mem_singleton k), mul_one]
  conv_lhs => rw [hv]
  rw [matSeries_tsum C (fun j k ↦ v j * ({j} : Set α).indicator (fun _ ↦ (1 : ℝ≥0∞)) k) i]
  exact tsum_congr fun j ↦ by
    rw [matSeries_const_mul C (v j) (({j} : Set α).indicator fun _ ↦ 1) i, matEntry, mul_comm]

/-- **The row sums of `D`**: `∑_j D_ij ≤ (1 − c)⁻¹` when the row sums of `C` are
at most `c`. -/
lemma tsum_matEntry_le (hc : ∀ i, ∑' j, C i j ≤ c) (i : α) :
    ∑' j, matEntry C i j ≤ 1 / (1 - c) := by
  have h := matSeries_le (C := C) hc (b := fun _ ↦ (1 : ℝ≥0∞)) (B := 1) (fun _ ↦ le_rfl) i
  rw [matSeries_eq_tsum_matEntry] at h
  simpa using h

/-! ### Locality: the Neumann series decays with the distance -/

/-- **Locality of `C^n`.** If one step of `C` moves at most one unit of `ρ` — `C i k ≠ 0` implies
`ρ i ≤ ρ k + 1` — and `b` is supported where `ρ = 0`, then `(C^n b)_i = 0` whenever `n < ρ i`. -/
lemma matIter_eq_zero_of_lt {ρ : α → ℕ∞} (hC : ∀ i k, C i k ≠ 0 → ρ i ≤ ρ k + 1)
    {b : α → ℝ≥0∞} (hb : ∀ j, b j ≠ 0 → ρ j = 0) (n : ℕ) {i : α} (hi : (n : ℕ∞) < ρ i) :
    matIter C n b i = 0 := by
  induction n generalizing i with
  | zero =>
      by_contra h
      rw [hb i h] at hi
      exact lt_irrefl _ hi
  | succ n ih =>
      refine ENNReal.tsum_eq_zero.2 fun k ↦ ?_
      by_cases hik : C i k = 0
      · rw [hik, zero_mul]
      · refine mul_eq_zero_of_right _ (ih ?_)
        by_contra hk
        have h1 : ρ i ≤ (n : ℕ∞) + 1 := (hC i k hik).trans (add_le_add_left (not_lt.1 hk) 1)
        exact absurd hi (not_lt.2 (by exact_mod_cast h1))

/-- **The Neumann series decays with the distance.** Under the hypotheses of
`matIter_eq_zero_of_lt`, if the row sums of `C` are at most `c` and `b ≤ B`, then
`(D b)_i ≤ B c^k/(1 − c)` for every `k ≤ ρ i`: the first `k` terms of `∑_n C^n b` vanish at `i`. -/
lemma matSeries_le_pow_of_le {ρ : α → ℕ∞} (hC : ∀ i k, C i k ≠ 0 → ρ i ≤ ρ k + 1)
    {b : α → ℝ≥0∞} (hb : ∀ j, b j ≠ 0 → ρ j = 0) (hc : ∀ i, ∑' j, C i j ≤ c) {B : ℝ≥0∞}
    (hB : ∀ j, b j ≤ B) {k : ℕ} {i : α} (hk : (k : ℕ∞) ≤ ρ i) :
    matSeries C b i ≤ B * c ^ k / (1 - c) := by
  have hzero : ∑ n ∈ Finset.range k, matIter C n b i = 0 :=
    Finset.sum_eq_zero fun n hn ↦ matIter_eq_zero_of_lt hC hb n
      ((Nat.cast_lt.2 (Finset.mem_range.1 hn)).trans_le hk)
  have hsplit : matSeries C b i = ∑' n, matIter C (n + k) b i := by
    rw [matSeries, (ENNReal.summable.hasSum.sum_range_add (f := fun n ↦ matIter C n b i)).tsum_eq,
      hzero, zero_add]
  calc matSeries C b i = ∑' n, matIter C (n + k) b i := hsplit
    _ ≤ ∑' n : ℕ, B * c ^ k * c ^ n :=
        ENNReal.tsum_le_tsum fun n ↦ (matIter_le hc hB (n + k) i).trans_eq (by ring)
    _ = B * c ^ k / (1 - c) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv]

/-- **Graph-distance decay of the Neumann series.** If `C` vanishes off the edges and the
diagonal of a simple graph `G` and its row sums are at most `c`, then `D_ij ≤ c^k/(1 − c)` for
every `k` at most the graph distance `d_G(i,j)` (`D_ij = 0` when `j` is not reachable from `i` and
`c < 1`). -/
theorem matEntry_le_pow_of_le_edist (G : SimpleGraph α)
    (hCG : ∀ i k, i ≠ k → ¬ G.Adj i k → C i k = 0) (hc : ∀ i, ∑' j, C i j ≤ c) {i j : α}
    {k : ℕ} (hk : (k : ℕ∞) ≤ G.edist i j) : matEntry C i j ≤ c ^ k / (1 - c) := by
  have hstep : ∀ i' k', C i' k' ≠ 0 → G.edist i' j ≤ G.edist k' j + 1 := by
    intro i' k' h
    rcases eq_or_ne i' k' with rfl | hne
    · exact le_self_add
    · have hadj : G.Adj i' k' := by
        by_contra hadj
        exact h (hCG i' k' hne hadj)
      rw [add_comm, ← SimpleGraph.edist_eq_one_iff_adj.2 hadj]
      exact SimpleGraph.edist_triangle
  have hb : ∀ j', ({j} : Set α).indicator (fun _ ↦ (1 : ℝ≥0∞)) j' ≠ 0 → G.edist j' j = 0 := by
    intro j' h
    by_cases hj : j' = j
    · rw [hj, SimpleGraph.edist_self]
    · exact absurd (Set.indicator_of_notMem (by simpa using hj) _) h
  simpa [matEntry] using matSeries_le_pow_of_le (ρ := fun i' ↦ G.edist i' j) hstep hb hc
    (B := 1) (fun j' ↦ by by_cases hj : j' = j <;> simp [hj]) hk

/-- `matEntry_le_pow_of_le_edist` at the graph distance `G.dist i j` (whose junk value `0` between
unreachable vertices gives the row-sum bound `D_ij ≤ (1 − c)⁻¹`). -/
theorem matEntry_le_pow_dist (G : SimpleGraph α) (hCG : ∀ i k, i ≠ k → ¬ G.Adj i k → C i k = 0)
    (hc : ∀ i, ∑' j, C i j ≤ c) (i j : α) : matEntry C i j ≤ c ^ G.dist i j / (1 - c) :=
  matEntry_le_pow_of_le_edist G hCG hc (ENat.natCast_toNat_le_self _)

variable [DecidableEq α]

/-- `∑_{j ∉ Δ} D_{ij}`: the total weight the Neumann series `D = ∑_n C^n` puts outside the
finite set `Δ`. -/
noncomputable def matTail (C : α → α → ℝ≥0∞) (Δ : Finset α) (i : α) : ℝ≥0∞ :=
  matSeries C (fun j ↦ if j ∈ Δ then 0 else 1) i

lemma matTail_antitone (C : α → α → ℝ≥0∞) {Δ Δ' : Finset α} (h : Δ ⊆ Δ') (i : α) :
    matTail C Δ' i ≤ matTail C Δ i :=
  matSeries_mono_vec C (fun j ↦ by
    by_cases hj : j ∈ Δ
    · simp [hj, h hj]
    · by_cases hj' : j ∈ Δ' <;> simp [hj, hj']) i

lemma matTail_mono_matrix (h : ∀ i j, C' i j ≤ C i j) (Δ : Finset α) (i : α) :
    matTail C' Δ i ≤ matTail C Δ i :=
  matSeries_mono_matrix h _ i

/-- For each fixed number of steps, `C^n 1_{α∖Δ}` can be made arbitrarily small by taking `Δ`
large, when the row sums of `C` are at most `c < 1`. -/
theorem exists_matIter_compl_le (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c) (n : ℕ) (i : α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ Δ : Finset α, matIter C n (fun j ↦ if j ∈ Δ then 0 else 1) i ≤ ε := by
  have hcne : c ≠ ⊤ := ne_top_of_lt hc1
  have hle1 : ∀ i j, C i j ≤ 1 := fun i j ↦
    ((ENNReal.le_tsum j).trans (hc i)).trans hc1.le
  have hbdd : ∀ (Δ : Finset α) (m : ℕ) (j : α),
      matIter C m (fun k ↦ if k ∈ Δ then 0 else 1) j ≤ 1 := by
    intro Δ m j
    refine (matIter_le hc (M := 1) (fun k ↦ by split <;> simp) m j).trans ?_
    simpa using pow_le_one₀ (by simp : (0 : ℝ≥0∞) ≤ c) hc1.le
  have hfin : ∀ i : α, ∑' j, C i j ≠ ⊤ := fun i ↦ ne_top_of_le_ne_top hcne (hc i)
  suffices H : ∀ (n : ℕ) (i : α) (ε : ℝ≥0∞), 0 < ε →
      ∃ Δ : Finset α, matIter C n (fun j ↦ if j ∈ Δ then 0 else 1) i ≤ ε from H n i ε hε
  intro n
  induction n with
  | zero => exact fun i ε _ ↦ ⟨{i}, by simp⟩
  | succ n ih =>
    intro i ε hε
    obtain ⟨J, hJ⟩ := exists_tsum_ite_compl_le (hfin i) (ENNReal.half_pos hε.ne')
    set δ : ℝ≥0∞ := (ε / 2) / (J.card + 1) with hδ
    have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp)
    choose Δf hΔf using fun j : α ↦ ih j δ hδpos
    refine ⟨J.sup Δf, ?_⟩
    have hsub : ∀ j ∈ J, Δf j ⊆ J.sup Δf := fun j hj ↦ Finset.le_sup hj
    have hmono : ∀ j ∈ J,
        matIter C n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j ≤ δ := by
      intro j hj
      refine le_trans (matIter_mono_vec C (fun k ↦ ?_) n j) (hΔf j)
      by_cases hk : k ∈ Δf j
      · simp [hk, hsub j hj hk]
      · by_cases hk' : k ∈ J.sup Δf <;> simp [hk, hk']
    have hstep := tsum_le_card_mul_add
      (g := fun j ↦ C i j * matIter C n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j)
      (h := fun j ↦ C i j) J δ
      (fun j hj ↦ le_trans (mul_le_mul' (hle1 i j) (hmono j hj)) (by simp))
      (fun j _ ↦ by
        refine le_trans (mul_le_mul' le_rfl (hbdd _ n j)) (by simp))
    have hcard : (J.card : ℝ≥0∞) * δ ≤ ε / 2 := by
      calc (J.card : ℝ≥0∞) * δ ≤ ((J.card : ℝ≥0∞) + 1) * δ := by gcongr; exact le_self_add
        _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp)
    calc matIter C (n + 1) (fun k ↦ if k ∈ J.sup Δf then 0 else 1) i
        = ∑' j, C i j * matIter C n (fun k ↦ if k ∈ J.sup Δf then 0 else 1) j := rfl
      _ ≤ (J.card : ℝ≥0∞) * δ + ∑' j, (if j ∈ J then 0 else C i j) := hstep
      _ ≤ ε / 2 + ε / 2 := add_le_add hcard hJ
      _ = ε := ENNReal.add_halves ε

/-- For a matrix with row sums at most `c < 1` the tail weight vanishes:
`∑_{j ∉ Δ} D_{ij} → 0` as `Δ ↑ α`. -/
theorem tendsto_matTail (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c) (i : α) :
    Tendsto (fun Δ : Finset α ↦ matTail C Δ i) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hgeom : ∑' n : ℕ, c ^ n ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hc1).ne'
  obtain ⟨J, hJ⟩ := exists_tsum_ite_compl_le (f := fun n : ℕ ↦ c ^ n) hgeom
    (ENNReal.half_pos hε.ne')
  set δ : ℝ≥0∞ := (ε / 2) / (J.card + 1) with hδ
  have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp)
  choose Δf hΔf using fun n : ℕ ↦ exists_matIter_compl_le hc1 hc n i hδpos
  set Δ₀ : Finset α := J.sup Δf with hΔ₀
  have hsub : ∀ n ∈ J, Δf n ⊆ Δ₀ := fun n hn ↦ Finset.le_sup hn
  have hmono : ∀ n ∈ J, matIter C n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i ≤ δ := by
    intro n hn
    refine le_trans (matIter_mono_vec C (fun k ↦ ?_) n i) (hΔf n)
    by_cases hk : k ∈ Δf n
    · simp [hk, hsub n hn hk]
    · by_cases hk' : k ∈ Δ₀ <;> simp [hk, hk']
  have hbound : matTail C Δ₀ i ≤ ε := by
    have hstep := tsum_le_card_mul_add
      (g := fun n : ℕ ↦ matIter C n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i)
      (h := fun n : ℕ ↦ c ^ n) J δ hmono
      (fun n _ ↦ by
        simpa using matIter_le hc (M := 1) (fun k ↦ by split <;> simp) n i)
    have hcard : (J.card : ℝ≥0∞) * δ ≤ ε / 2 := by
      calc (J.card : ℝ≥0∞) * δ ≤ ((J.card : ℝ≥0∞) + 1) * δ := by gcongr; exact le_self_add
        _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp)
    calc matTail C Δ₀ i
        = ∑' n : ℕ, matIter C n (fun k ↦ if k ∈ Δ₀ then 0 else 1) i := rfl
      _ ≤ (J.card : ℝ≥0∞) * δ + ∑' n : ℕ, (if n ∈ J then 0 else c ^ n) := hstep
      _ ≤ ε / 2 + ε / 2 := add_le_add hcard hJ
      _ = ε := ENNReal.add_halves ε
  filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ
  exact (matTail_antitone C hΔ i).trans hbound

/-- Testing a bounded vector through the Neumann series against a summable weight gives a finite
number, when the row sums of `C` are at most `c < 1`. -/
lemma tsum_matSeries_mul_ne_top (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c) {v : α → ℝ≥0∞}
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hv : ∀ j, v j ≤ M) {w : α → ℝ≥0∞} (hw : ∑' i, w i ≠ ⊤) :
    ∑' i, matSeries C v i * w i ≠ ⊤ := by
  have hinv : (1 - c) ≠ 0 := (tsub_pos_of_lt hc1).ne'
  have hle : ∑' i, matSeries C v i * w i ≤ M / (1 - c) * ∑' i, w i :=
    calc ∑' i, matSeries C v i * w i ≤ ∑' i, M / (1 - c) * w i :=
          ENNReal.tsum_le_tsum fun i ↦ mul_le_mul' (matSeries_le hc hv i) le_rfl
      _ = M / (1 - c) * ∑' i, w i := ENNReal.tsum_mul_left
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ?_ hw) hle
  rw [div_eq_mul_inv]
  exact ENNReal.mul_ne_top hM (ENNReal.inv_ne_top.2 hinv)

omit [DecidableEq α] in
/-- **Dominated convergence through the Neumann series.** If the vectors `v_k` are bounded by a
finite `M` and tend to `0` at every index, and `∑_i w_i < ∞`, then `∑_i (D v_k)_i w_i → 0`, where
`D = ∑_{n ≥ 0} C^n` has row sums at most `(1 − c)⁻¹`. -/
theorem tendsto_tsum_matSeries_mul (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c)
    {κ : Type*} {l : Filter κ} {v : κ → α → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hv : ∀ k j, v k j ≤ M) (hv0 : ∀ j, Tendsto (fun k ↦ v k j) l (𝓝 0))
    {w : α → ℝ≥0∞} (hw : ∑' i, w i ≠ ⊤) :
    Tendsto (fun k ↦ ∑' i, matSeries C (v k) i * w i) l (𝓝 0) := by
  have hinv : (1 - c) ≠ 0 := (tsub_pos_of_lt hc1).ne'
  have hDfin : ∀ i, ∑' j, matEntry C i j ≠ ⊤ := fun i ↦
    ne_top_of_le_ne_top (by rw [one_div]; exact ENNReal.inv_ne_top.2 hinv)
      (tsum_matEntry_le hc i)
  have hinner : ∀ i, Tendsto (fun k ↦ matSeries C (v k) i) l (𝓝 0) := by
    intro i
    have h := tendsto_tsum_mul_of_tendsto (A := v) (w := fun j ↦ matEntry C i j) hM hv hv0
      (hDfin i)
    refine h.congr fun k ↦ ?_
    rw [matSeries_eq_tsum_matEntry]
    exact tsum_congr fun j ↦ mul_comm _ _
  have hbound : ∀ (k : κ) (i : α), matSeries C (v k) i ≤ M / (1 - c) := fun k i ↦
    matSeries_le hc (fun j ↦ hv k j) i
  exact tendsto_tsum_mul_of_tendsto (A := fun k i ↦ matSeries C (v k) i) (w := w)
    (by rw [div_eq_mul_inv]; exact ENNReal.mul_ne_top hM (ENNReal.inv_ne_top.2 hinv))
    hbound hinner hw

/-- The tail weights `∑_{j ∉ Δ} D_ij` tested against a summable weight are finite. -/
lemma tsum_matTail_mul_ne_top (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c) (Δ : Finset α)
    {w : α → ℝ≥0∞} (hw : ∑' i, w i ≠ ⊤) : ∑' i, matTail C Δ i * w i ≠ ⊤ :=
  tsum_matSeries_mul_ne_top hc1 hc (M := 1) one_ne_top (fun j ↦ by split <;> simp) hw

/-- For a summable weight `w`, the tail weights `∑_{j ∉ Λ} D_ij` tested against `w` vanish as
`Λ ↑ α`. -/
theorem tendsto_tsum_matTail_mul (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c)
    {w : α → ℝ≥0∞} (hw : ∑' j, w j ≠ ⊤) :
    Tendsto (fun Λ : Finset α ↦ ∑' j, matTail C Λ j * w j) atTop (𝓝 0) := by
  have hinv : (1 - c) ≠ 0 := (tsub_pos_of_lt hc1).ne'
  refine tendsto_tsum_mul_of_tendsto (A := fun Λ j ↦ matTail C Λ j) (w := w)
    (M := 1 / (1 - c)) (by rw [one_div]; exact ENNReal.inv_ne_top.2 hinv) (fun Λ j ↦ ?_)
    (fun j ↦ tendsto_matTail hc1 hc j) hw
  exact matSeries_le hc (b := fun k ↦ if k ∈ Λ then 0 else 1) (B := 1)
    (fun k ↦ by split <;> simp) j

end MatIter

end ENNReal

end

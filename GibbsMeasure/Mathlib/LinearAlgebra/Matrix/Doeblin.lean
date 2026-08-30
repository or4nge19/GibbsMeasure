/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Doeblin's ergodic theorem for positive stochastic matrices

Georgii, *Gibbs Measures and Phase Transitions*, Appendix 3.A. For a row-stochastic matrix `P`
with strictly positive entries, left multiplication by `P` contracts the `ℓ¹`-norm of sum-zero
vectors by the factor `1 - card n * ε`, where `ε` is the smallest entry of `P`. Consequently
`P` has a unique stationary distribution `α`, and `μ ᵥ* P ^ k → α` geometrically for every
probability vector `μ`; in particular every row of `P ^ k` converges to `α`.

The contraction factor is the Dobrushin coefficient bound of
[or4nge19/MCMC](https://github.com/or4nge19/MCMC) (`MCMC/Finite/TotalVariation.lean`,
`MCMC/Finite/Convergence.lean`), specialised to strictly positive matrices.
-/

@[expose] public section

open Filter Topology Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)

/-- Left multiplication by a row-stochastic matrix preserves the sum of a vector. -/
lemma sum_vecMul_of_mem_rowStochastic (hP : P ∈ rowStochastic ℝ n) (d : n → ℝ) :
    ∑ j, (d ᵥ* P) j = ∑ i, d i := by
  simp only [vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_row_of_mem_rowStochastic hP, mul_one]

/-- `ℓ¹`-contraction (Georgii, Appendix 3.A): if every entry of the row-stochastic matrix `P` is
at least `ε`, then `d ↦ d ᵥ* P` contracts sum-zero vectors by the factor `1 - card n * ε`. -/
lemma sum_abs_vecMul_le_of_sum_eq_zero (hP : P ∈ rowStochastic ℝ n) {ε : ℝ}
    (hε : ∀ i j, ε ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) :
    ∑ j, |(d ᵥ* P) j| ≤ (1 - Fintype.card n * ε) * ∑ i, |d i| := by
  have key : ∀ j, (d ᵥ* P) j = ∑ i, d i * (P i j - ε) := by
    intro j
    simp only [vecMul, dotProduct, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd,
      zero_mul, sub_zero]
  calc ∑ j, |(d ᵥ* P) j| = ∑ j, |∑ i, d i * (P i j - ε)| := by simp_rw [key]
    _ ≤ ∑ j, ∑ i, |d i| * (P i j - ε) := by
        refine Finset.sum_le_sum fun j _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hε i j))]
    _ = ∑ i, |d i| * ∑ j, (P i j - ε) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ i, |d i| * (1 - Fintype.card n * ε) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic hP, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
    _ = (1 - Fintype.card n * ε) * ∑ i, |d i| := by rw [← Finset.sum_mul, mul_comm]

/-- The standard simplex is stable under left multiplication by a row-stochastic matrix. -/
lemma vecMul_mem_stdSimplex (hP : P ∈ rowStochastic ℝ n) {μ : n → ℝ}
    (hμ : μ ∈ stdSimplex ℝ n) : μ ᵥ* P ∈ stdSimplex ℝ n :=
  ⟨nonneg_vecMul_of_mem_rowStochastic hP hμ.1,
    by rw [sum_vecMul_of_mem_rowStochastic P hP, hμ.2]⟩

/-- A stationary vector of `P` is stationary for every power of `P`. -/
lemma vecMul_pow_eq_self {α : n → ℝ} (hα : α ᵥ* P = α) (k : ℕ) : α ᵥ* P ^ k = α := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← vecMul_vecMul, ih, hα]

omit [DecidableEq n] in
/-- The `ℓ¹`-distance of two points of the standard simplex is at most `2`. -/
lemma sum_abs_sub_le_two_of_mem_stdSimplex {μ ν : n → ℝ} (hμ : μ ∈ stdSimplex ℝ n)
    (hν : ν ∈ stdSimplex ℝ n) : ∑ i, |μ i - ν i| ≤ 2 := by
  calc ∑ i, |μ i - ν i| ≤ ∑ i, (μ i + ν i) := by
        refine Finset.sum_le_sum fun i _ => (abs_sub _ _).trans ?_
        rw [abs_of_nonneg (hμ.1 i), abs_of_nonneg (hν.1 i)]
    _ = 2 := by rw [Finset.sum_add_distrib, hμ.2, hν.2]; norm_num

variable [Nonempty n]

omit [DecidableEq n] in
/-- A matrix with positive entries has a positive lower bound on its entries. -/
lemma exists_pos_le_of_pos (hpos : ∀ i j, 0 < P i j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, ε ≤ P i j := by
  obtain ⟨⟨i₀, j₀⟩, -, hmin⟩ :=
    Finset.exists_min_image (univ : Finset (n × n)) (fun p => P p.1 p.2) univ_nonempty
  exact ⟨P i₀ j₀, hpos i₀ j₀, fun i j => hmin (i, j) (mem_univ _)⟩

/-- The contraction factor `1 - card n * ε` is nonnegative. -/
lemma one_sub_card_mul_nonneg (hP : P ∈ rowStochastic ℝ n) {ε : ℝ} (hε : ∀ i j, ε ≤ P i j) :
    0 ≤ 1 - Fintype.card n * ε := by
  obtain ⟨i⟩ := ‹Nonempty n›
  have : ∑ j, (P i j - ε) = 1 - Fintype.card n * ε := by
    rw [Finset.sum_sub_distrib, sum_row_of_mem_rowStochastic hP, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  rw [← this]
  exact Finset.sum_nonneg fun j _ => sub_nonneg.2 (hε i j)

omit [DecidableEq n] in
/-- The contraction factor `1 - card n * ε` is strictly less than `1` when `ε > 0`. -/
lemma one_sub_card_mul_lt_one {ε : ℝ} (hε0 : 0 < ε) : 1 - Fintype.card n * ε < 1 := by
  have : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  linarith [mul_pos this hε0]

/-- Iterated `ℓ¹`-contraction for the powers of `P`. -/
lemma sum_abs_vecMul_pow_le_of_sum_eq_zero (hP : P ∈ rowStochastic ℝ n) {ε : ℝ}
    (hε : ∀ i j, ε ≤ P i j) {d : n → ℝ} (hd : ∑ i, d i = 0) (k : ℕ) :
    ∑ j, |(d ᵥ* P ^ k) j| ≤ (1 - Fintype.card n * ε) ^ k * ∑ i, |d i| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsum : ∑ j, (d ᵥ* P ^ k) j = 0 := by
      rw [sum_vecMul_of_mem_rowStochastic _ (pow_mem hP k), hd]
    calc ∑ j, |(d ᵥ* P ^ (k + 1)) j| = ∑ j, |((d ᵥ* P ^ k) ᵥ* P) j| := by
          rw [pow_succ, ← vecMul_vecMul]
      _ ≤ (1 - Fintype.card n * ε) * ∑ j, |(d ᵥ* P ^ k) j| :=
          sum_abs_vecMul_le_of_sum_eq_zero P hP hε hsum
      _ ≤ (1 - Fintype.card n * ε) * ((1 - Fintype.card n * ε) ^ k * ∑ i, |d i|) :=
          mul_le_mul_of_nonneg_left ih (one_sub_card_mul_nonneg P hP hε)
      _ = (1 - Fintype.card n * ε) ^ (k + 1) * ∑ i, |d i| := by ring

/-- Uniqueness: two vectors with the same coordinate sum that are both fixed by `ᵥ* P`
coincide. -/
lemma eq_of_vecMul_eq_of_sum_eq (hP : P ∈ rowStochastic ℝ n) (hpos : ∀ i j, 0 < P i j)
    {α β : n → ℝ} (hα : α ᵥ* P = α) (hβ : β ᵥ* P = β) (hs : ∑ i, α i = ∑ i, β i) : α = β := by
  obtain ⟨ε, hε0, hε⟩ := exists_pos_le_of_pos P hpos
  have hd : ∑ i, (α - β) i = 0 := by simp [Finset.sum_sub_distrib, hs]
  have h := sum_abs_vecMul_le_of_sum_eq_zero P hP hε hd
  rw [sub_vecMul, hα, hβ] at h
  have hS : 0 ≤ ∑ i, |(α - β) i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hS0 : ∑ i, |(α - β) i| = 0 := by
    by_contra hne
    have hSpos : 0 < ∑ i, |(α - β) i| := lt_of_le_of_ne hS (Ne.symm hne)
    exact absurd ((le_mul_iff_one_le_left hSpos).1 h) (not_le.2 (one_sub_card_mul_lt_one hε0))
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg ((α - β) i)).1 hS0
  ext i
  exact sub_eq_zero.1 (abs_eq_zero.1 (this i (mem_univ i)))

/-- Geometric `ℓ¹`-convergence of `μ ᵥ* P ^ k` to a stationary distribution `α`
(Georgii, Appendix 3.A). -/
theorem sum_abs_vecMul_pow_sub_le (hP : P ∈ rowStochastic ℝ n) {ε : ℝ} (hε : ∀ i j, ε ≤ P i j)
    {α μ : n → ℝ} (hα : α ∈ stdSimplex ℝ n) (hαP : α ᵥ* P = α) (hμ : μ ∈ stdSimplex ℝ n)
    (k : ℕ) : ∑ j, |(μ ᵥ* P ^ k) j - α j| ≤ (1 - Fintype.card n * ε) ^ k * 2 := by
  have hd : ∑ i, (μ - α) i = 0 := by simp [Finset.sum_sub_distrib, hμ.2, hα.2]
  have h := sum_abs_vecMul_pow_le_of_sum_eq_zero P hP hε hd k
  rw [sub_vecMul, vecMul_pow_eq_self P hαP] at h
  simp only [Pi.sub_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sum_abs_sub_le_two_of_mem_stdSimplex hμ hα)
    (pow_nonneg (one_sub_card_mul_nonneg P hP hε) k))

/-- Entrywise geometric rate: `|(P ^ k) x y - α y| ≤ (1 - card n * ε) ^ k * 2`. -/
theorem abs_pow_apply_sub_le (hP : P ∈ rowStochastic ℝ n) {ε : ℝ} (hε : ∀ i j, ε ≤ P i j)
    {α : n → ℝ} (hα : α ∈ stdSimplex ℝ n) (hαP : α ᵥ* P = α) (x y : n) (k : ℕ) :
    |(P ^ k) x y - α y| ≤ (1 - Fintype.card n * ε) ^ k * 2 := by
  have h := sum_abs_vecMul_pow_sub_le P hP hε hα hαP
    (single_mem_stdSimplex (𝕜 := ℝ) (ι := n) x) k
  simp only [single_vecMul, one_smul, row_apply] at h
  exact (Finset.single_le_sum (f := fun j => |(P ^ k) x j - α j|) (fun j _ => abs_nonneg _)
    (mem_univ y)).trans h

/-- Existence of a stationary distribution for a positive row-stochastic matrix. -/
theorem exists_stationary (hP : P ∈ rowStochastic ℝ n) (hpos : ∀ i j, 0 < P i j) :
    ∃ α ∈ stdSimplex ℝ n, α ᵥ* P = α := by
  obtain ⟨ε, hε0, hε⟩ := exists_pos_le_of_pos P hpos
  have hκ0 : 0 ≤ 1 - Fintype.card n * ε := one_sub_card_mul_nonneg P hP hε
  have hκ1 : 1 - Fintype.card n * ε < 1 := one_sub_card_mul_lt_one hε0
  obtain ⟨i₀⟩ := ‹Nonempty n›
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : n → ℝ, μ₀ ∈ stdSimplex ℝ n :=
    ⟨_, single_mem_stdSimplex (𝕜 := ℝ) (ι := n) i₀⟩
  have hmem : ∀ k, μ₀ ᵥ* P ^ k ∈ stdSimplex ℝ n := fun k =>
    vecMul_mem_stdSimplex _ (pow_mem hP k) hμ₀
  have hdist : ∀ k, dist (μ₀ ᵥ* P ^ k) (μ₀ ᵥ* P ^ (k + 1)) ≤
      2 * (1 - Fintype.card n * ε) ^ k := by
    intro k
    have hd : ∑ i, (μ₀ ᵥ* P - μ₀) i = 0 := by
      simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_vecMul_of_mem_rowStochastic P hP,
        sub_self]
    have h := sum_abs_vecMul_pow_le_of_sum_eq_zero P hP hε hd k
    rw [sub_vecMul, vecMul_vecMul, ← pow_succ'] at h
    refine (dist_pi_le_iff (mul_nonneg zero_le_two (pow_nonneg hκ0 k))).2 fun j => ?_
    rw [Real.dist_eq, abs_sub_comm]
    calc |(μ₀ ᵥ* P ^ (k + 1)) j - (μ₀ ᵥ* P ^ k) j|
        ≤ ∑ j, |(μ₀ ᵥ* P ^ (k + 1) - μ₀ ᵥ* P ^ k) j| :=
          Finset.single_le_sum (f := fun j => |(μ₀ ᵥ* P ^ (k + 1) - μ₀ ᵥ* P ^ k) j|)
            (fun j _ => abs_nonneg _) (mem_univ j)
      _ ≤ (1 - Fintype.card n * ε) ^ k * ∑ i, |(μ₀ ᵥ* P - μ₀) i| := h
      _ ≤ (1 - Fintype.card n * ε) ^ k * 2 :=
          mul_le_mul_of_nonneg_left (sum_abs_sub_le_two_of_mem_stdSimplex
            (vecMul_mem_stdSimplex P hP hμ₀) hμ₀) (pow_nonneg hκ0 k)
      _ = 2 * (1 - Fintype.card n * ε) ^ k := mul_comm _ _
  obtain ⟨α, hα⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (f := fun k => μ₀ ᵥ* P ^ k) _ 2 hκ1 hdist)
  refine ⟨α, (isClosed_stdSimplex ℝ n).mem_of_tendsto hα (Eventually.of_forall hmem), ?_⟩
  have hcont : Continuous fun x : n → ℝ => x ᵥ* P := by fun_prop
  have h1 : Tendsto (fun k => μ₀ ᵥ* P ^ k ᵥ* P) atTop (𝓝 (α ᵥ* P)) :=
    (hcont.tendsto α).comp hα
  have h2 : Tendsto (fun k => μ₀ ᵥ* P ^ k ᵥ* P) atTop (𝓝 α) := by
    have : (fun k => μ₀ ᵥ* P ^ k ᵥ* P) = fun k => μ₀ ᵥ* P ^ (k + 1) := by
      funext k; rw [vecMul_vecMul, ← pow_succ]
    rw [this]
    exact hα.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h2

/-- Doeblin's ergodic theorem: `μ ᵥ* P ^ k` converges to the stationary distribution `α`
for every probability vector `μ`. -/
theorem tendsto_vecMul_pow (hP : P ∈ rowStochastic ℝ n) (hpos : ∀ i j, 0 < P i j)
    {α μ : n → ℝ} (hα : α ∈ stdSimplex ℝ n) (hαP : α ᵥ* P = α) (hμ : μ ∈ stdSimplex ℝ n) :
    Tendsto (fun k => μ ᵥ* P ^ k) atTop (𝓝 α) := by
  obtain ⟨ε, hε0, hε⟩ := exists_pos_le_of_pos P hpos
  have hκ0 : 0 ≤ 1 - Fintype.card n * ε := one_sub_card_mul_nonneg P hP hε
  have hκ1 : 1 - Fintype.card n * ε < 1 := one_sub_card_mul_lt_one hε0
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => (1 - Fintype.card n * ε) ^ k * 2) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const 2
  refine squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hlim
  refine (dist_pi_le_iff (mul_nonneg (pow_nonneg hκ0 k) zero_le_two)).2 fun j => ?_
  rw [Real.dist_eq]
  exact (Finset.single_le_sum (f := fun j => |(μ ᵥ* P ^ k) j - α j|) (fun j _ => abs_nonneg _)
    (mem_univ j)).trans (sum_abs_vecMul_pow_sub_le P hP hε hα hαP hμ k)

/-- A positive row-stochastic matrix has a unique stationary distribution. -/
theorem exists_unique_stationary (hP : P ∈ rowStochastic ℝ n) (hpos : ∀ i j, 0 < P i j) :
    ∃! α : n → ℝ, α ∈ stdSimplex ℝ n ∧ α ᵥ* P = α := by
  obtain ⟨α, hα, hαP⟩ := exists_stationary P hP hpos
  exact ⟨α, ⟨hα, hαP⟩, fun β ⟨hβ, hβP⟩ =>
    eq_of_vecMul_eq_of_sum_eq P hP hpos hβP hαP (hβ.2.trans hα.2.symm)⟩

/-- Doeblin's ergodic theorem, entrywise: every row of `P ^ k` converges to the stationary
distribution `α`. -/
theorem tendsto_pow_apply (hP : P ∈ rowStochastic ℝ n) (hpos : ∀ i j, 0 < P i j)
    {α : n → ℝ} (hα : α ∈ stdSimplex ℝ n) (hαP : α ᵥ* P = α) (x y : n) :
    Tendsto (fun k => (P ^ k) x y) atTop (𝓝 (α y)) := by
  have h := tendsto_pi_nhds.1
    (tendsto_vecMul_pow P hP hpos hα hαP (single_mem_stdSimplex (𝕜 := ℝ) (ι := n) x)) y
  simpa [single_vecMul, row_apply] using h

/-- The stationary distribution of a positive stochastic matrix is strictly positive
(Georgii (3.3): `α_P ∈ ]0, 1[^E`). -/
lemma pos_of_vecMul_eq_self (hpos : ∀ i j, 0 < P i j) {α : n → ℝ} (hα : α ∈ stdSimplex ℝ n)
    (hαP : α ᵥ* P = α) (j : n) : 0 < α j := by
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    have := hα.2
    simp [h] at this
  rw [← hαP]
  simp only [vecMul, dotProduct]
  exact Finset.sum_pos' (fun k _ ↦ mul_nonneg (hα.1 k) (hpos k j).le)
    ⟨i, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hα.1 i) (Ne.symm hi)) (hpos i j)⟩

end Matrix

end

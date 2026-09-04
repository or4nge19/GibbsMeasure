/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PerronFrobenius
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# The stochastic matrix of a positive matrix

A strictly positive matrix `A` with Perron root `r` and positive Perron eigenvector `v` is
conjugate to `r` times the row-stochastic matrix
`P(x, y) = A(x, y) v(y) / (r v(x))`
(`perronStochastic`): `A = r · D P D⁻¹` with `D = diagonal v`, so that
`A^k(x, y) = r^k P^k(x, y) v(x) / v(y)` (`pow_apply_eq_perronRoot_pow_mul`). This is Georgii's
passage from a positive transfer matrix `Q` to a transition matrix (Theorem (3.17), and the
Perron–Frobenius normalisation of Comment (3.8)(2)). Conversely, a positive row-stochastic matrix
has Perron root `1` (`perronRoot_eq_one_of_mem_rowStochastic`).
-/

@[expose] public section

namespace Matrix

open Finset

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (A : Matrix n n ℝ)
  (hA : ∀ i j, 0 < A i j)

/-- The row-stochastic matrix `P(x, y) = A(x, y) v(y) / (r v(x))` of a positive matrix `A` with
Perron root `r` and Perron eigenvector `v`. -/
noncomputable def perronStochastic : Matrix n n ℝ :=
  of fun x y ↦ A x y * perronVector A hA y / (perronRoot A hA * perronVector A hA x)

omit [DecidableEq n] in
lemma perronStochastic_apply (x y : n) :
    perronStochastic A hA x y
      = A x y * perronVector A hA y / (perronRoot A hA * perronVector A hA x) := rfl

omit [DecidableEq n] in
lemma perronStochastic_pos (x y : n) : 0 < perronStochastic A hA x y :=
  div_pos (mul_pos (hA x y) (perronVector_pos A hA y))
    (mul_pos (perronRoot_pos A hA) (perronVector_pos A hA x))

lemma perronStochastic_mem_rowStochastic : perronStochastic A hA ∈ rowStochastic ℝ n := by
  refine mem_rowStochastic_iff_sum.2 ⟨fun x y ↦ (perronStochastic_pos A hA x y).le, fun x ↦ ?_⟩
  have hv := congrFun (mulVec_perronVector A hA) x
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv
  simp only [perronStochastic_apply, ← sum_div, hv]
  exact div_self (mul_pos (perronRoot_pos A hA) (perronVector_pos A hA x)).ne'

omit [DecidableEq n] in
/-- `A = r · D P D⁻¹` entrywise: `A(x, y) = r P(x, y) v(x) / v(y)`. -/
lemma apply_eq_perronRoot_mul (x y : n) :
    A x y = perronRoot A hA * perronStochastic A hA x y * perronVector A hA x
      / perronVector A hA y := by
  rw [perronStochastic_apply]
  field_simp [(perronRoot_pos A hA).ne', (perronVector_pos A hA x).ne',
    (perronVector_pos A hA y).ne']

/-- **Powers of a positive matrix through its stochastic matrix.**
`A^k(x, y) = r^k P^k(x, y) v(x) / v(y)`, with `r` the Perron root, `v` the Perron eigenvector
and `P = perronStochastic A`. -/
theorem pow_apply_eq_perronRoot_pow_mul (k : ℕ) (x y : n) :
    (A ^ k) x y = perronRoot A hA ^ k * (perronStochastic A hA ^ k) x y * perronVector A hA x
      / perronVector A hA y := by
  induction k generalizing y with
  | zero =>
    simp only [pow_zero, one_apply]
    split_ifs with h
    · subst h
      rw [mul_one, one_mul, div_self (perronVector_pos A hA x).ne']
    · simp
  | succ k ih =>
    rw [pow_succ A, mul_apply, pow_succ (perronStochastic A hA), mul_apply, mul_sum, sum_mul,
      sum_div]
    refine sum_congr rfl fun z _ ↦ ?_
    rw [ih z, apply_eq_perronRoot_mul A hA z y]
    field_simp [(perronVector_pos A hA z).ne', (perronVector_pos A hA y).ne']
    ring

/-- `A^k(x, x) = r^k P^k(x, x)`. -/
theorem pow_apply_self_eq_perronRoot_pow_mul (k : ℕ) (x : n) :
    (A ^ k) x x = perronRoot A hA ^ k * (perronStochastic A hA ^ k) x x := by
  rw [pow_apply_eq_perronRoot_pow_mul A hA k x x, mul_div_assoc,
    div_self (perronVector_pos A hA x).ne', mul_one]

/-- A positive row-stochastic matrix has Perron root `1`: the all-ones vector is a positive
eigenvector with eigenvalue `1`. -/
theorem perronRoot_eq_one_of_mem_rowStochastic (hM : A ∈ rowStochastic ℝ n) :
    perronRoot A hA = 1 :=
  (eq_perronRoot_of_pos_eigenvector A hA (v := 1) (r := 1) (fun _ ↦ zero_lt_one)
    (by rw [one_vecMul_of_mem_rowStochastic hM, one_smul])).symm

end Matrix

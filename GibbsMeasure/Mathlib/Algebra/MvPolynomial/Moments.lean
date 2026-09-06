/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Ring.Basic

/-!
# Moments determine a finitely supported weight

A weight `g` carried by a finite set of *distinct* points `x i ∈ σ → R` of an ordered field is
determined by its moments `∑ i, g i ∏_ℓ (x i ℓ) ^ n ℓ`, `n : σ → ℕ`: if all of them vanish, then
`g` vanishes on the finite set. This is the multivariate Vandermonde argument, run through
Lagrange interpolation: the moment hypothesis says that the linear functional
`p ↦ ∑ i, g i * eval (x i) p` kills every monomial, hence every polynomial, and the multivariate
Lagrange basis polynomial

  `p = ∏_{i ≠ i₀} (∑_ℓ (X ℓ - x i ℓ)²) / (∑_ℓ (x i₀ ℓ - x i ℓ)²)`

is `1` at `x i₀` and `0` at every other `x i`. Over an ordered field a sum of squares vanishes
only when all its terms do, so the denominators are non-zero; this is what replaces the choice of
a separating coordinate for each `i`.

## Main results

* `MvPolynomial.eval_sumSqDist_pos`: the separating polynomial `∑_ℓ (X ℓ - x ℓ) ^ 2` is positive
  away from `x`.
* `MvPolynomial.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`: the statement above, for an indexed
  family of points.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype σ]

/-- The squared distance to a point `x`, as a polynomial: `∑_ℓ (X ℓ - x ℓ) ^ 2`. It vanishes at
`x` and is positive everywhere else, so it is the building block of a multivariate Lagrange
basis over an ordered field. -/
noncomputable def sumSqDist (x : σ → R) : MvPolynomial σ R := ∑ ℓ, (X ℓ - C (x ℓ)) ^ 2

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] lemma eval_sumSqDist (x y : σ → R) : eval y (sumSqDist x) = ∑ ℓ, (y ℓ - x ℓ) ^ 2 := by
  simp [sumSqDist]

omit [LinearOrder R] [IsStrictOrderedRing R] in
@[simp] lemma eval_sumSqDist_self (x : σ → R) : eval x (sumSqDist x) = 0 := by simp

/-- `∑_ℓ (y ℓ - x ℓ) ^ 2 > 0` as soon as `y ≠ x`: over an ordered field a sum of squares vanishes
only when every term does. -/
lemma eval_sumSqDist_pos {x y : σ → R} (h : y ≠ x) : 0 < eval y (sumSqDist x) := by
  obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.1 h
  rw [eval_sumSqDist]
  refine Finset.sum_pos' (fun k _ ↦ sq_nonneg _) ⟨ℓ, Finset.mem_univ ℓ, ?_⟩
  exact sq_pos_of_ne_zero (sub_ne_zero.2 hℓ)

/-- **Moments determine a finitely supported weight.** If the moments
`∑_{i ∈ F} g i ∏_ℓ (x i ℓ) ^ n ℓ` all vanish, `n` ranging over the multi-indices `σ → ℕ`, and the
points `x i`, `i ∈ F`, are distinct, then `g` vanishes on `F`. -/
theorem eq_zero_of_forall_sum_mul_prod_pow_eq_zero {ι : Type*} (F : Finset ι) (x : ι → σ → R)
    (hx : Set.InjOn x F) (g : ι → R)
    (hg : ∀ n : σ → ℕ, ∑ i ∈ F, g i * ∏ ℓ, x i ℓ ^ n ℓ = 0) {i₀ : ι} (hi₀ : i₀ ∈ F) :
    g i₀ = 0 := by
  classical
  -- The moment hypothesis says that `p ↦ ∑ i, g i * eval (x i) p` kills every polynomial.
  have key : ∀ p : MvPolynomial σ R, ∑ i ∈ F, g i * eval (x i) p = 0 := by
    intro p
    have hexp : ∀ i : ι, g i * eval (x i) p
        = ∑ n ∈ p.support, p.coeff n * (g i * ∏ ℓ, x i ℓ ^ n ℓ) := by
      intro i
      rw [eval_eq', Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ ↦ (mul_left_comm _ _ _)
    simp_rw [hexp]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    rw [← Finset.mul_sum, hg n, mul_zero]
  -- The multivariate Lagrange basis polynomial at `x i₀`.
  set p : MvPolynomial σ R :=
    ∏ i ∈ F.erase i₀, C (eval (x i₀) (sumSqDist (x i)))⁻¹ * sumSqDist (x i) with hp
  have hne : ∀ i ∈ F.erase i₀, eval (x i₀) (sumSqDist (x i)) ≠ 0 := fun i hi ↦
    ne_of_gt (eval_sumSqDist_pos fun hcon ↦
      (Finset.ne_of_mem_erase hi)
        (hx (Finset.mem_coe.2 hi₀) (Finset.mem_coe.2 (Finset.mem_of_mem_erase hi)) hcon).symm)
  have h₀ : eval (x i₀) p = 1 := by
    rw [hp, map_prod]
    refine Finset.prod_eq_one fun i hi ↦ ?_
    rw [map_mul, eval_C, inv_mul_cancel₀ (hne i hi)]
  have hother : ∀ i ∈ F.erase i₀, eval (x i) p = 0 := by
    intro i hi
    rw [hp, map_prod]
    refine Finset.prod_eq_zero hi ?_
    rw [map_mul, eval_sumSqDist_self, mul_zero]
  have hsum := key p
  rw [← Finset.add_sum_erase F _ hi₀, h₀, mul_one,
    Finset.sum_eq_zero (fun i hi ↦ by rw [hother i hi, mul_zero]), add_zero] at hsum
  exact hsum

end MvPolynomial

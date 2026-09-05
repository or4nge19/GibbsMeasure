/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fin.VecNotation

/-!
# Cauchy–Schwarz for a nonnegative bilinear form: symmetry is not automatic

`LinearMap.BilinMap.sq_apply_le_of_symm_of_nonneg` proves the Cauchy–Schwarz inequality
`B x y ^ 2 ≤ B x x * B y y` for a bilinear form that is nonnegative definite *and symmetric*.
This file records what happens without the second hypothesis.

* `LinearMap.BilinMap.sq_add_swap_apply_le_of_nonneg`: nonnegativity alone bounds exactly the
  *symmetric part* of the form, `(B x y + B y x) ^ 2 ≤ 4 * (B x x * B y y)`.  This is the sharp
  statement: the quadratic `t ↦ B (x + t • y) (x + t • y)` only ever sees `B x y + B y x`.
* `LinearMap.BilinMap.notSymm`, `LinearMap.BilinMap.nonneg_notSymm` and
  `LinearMap.BilinMap.mul_notSymm_lt_sq_notSymm`: the bilinear form on `ℝ²` with matrix
  `!![1, 2; 0, 1]` is nonnegative definite, and `B e₀ e₁ ^ 2 = 4 > 1 = B e₀ e₀ * B e₁ e₁`.
  So Cauchy–Schwarz genuinely fails for a nonnegative form that is not symmetric, and the
  symmetry hypothesis of `sq_apply_le_of_symm_of_nonneg` cannot be dropped.

Georgii, *Gibbs Measures and Phase Transitions*, (17.8), asserts Cauchy–Schwarz for the real
bilinear form `(f, g) ↦ μ(f g^*)` of a reflection positive measure with the words "of course";
the reflection invariance of `μ` that makes it symmetric is used silently.  See
`GibbsMeasure/Specification/ReflectionPositivity.lean` for the measure-theoretic form of this
counterexample.
-/

@[expose] public section

universe u

namespace LinearMap.BilinMap

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **What nonnegativity of a bilinear form gives without symmetry.**  If `0 ≤ B z z` for every
`z`, then Cauchy–Schwarz holds for the *symmetric part* of `B`:
`(B x y + B y x) ^ 2 ≤ 4 * (B x x * B y y)`.  For a symmetric `B` this is
`sq_apply_le_of_symm_of_nonneg`; in general nothing more is true, see
`mul_notSymm_lt_sq_notSymm`. -/
theorem sq_add_swap_apply_le_of_nonneg {V : Type*} [AddCommGroup V] [Module K V]
    {B : V →ₗ[K] V →ₗ[K] K} (hnonneg : ∀ x, 0 ≤ B x x) (x y : V) :
    (B x y + B y x) ^ 2 ≤ 4 * (B x x * B y y) := by
  have key : ((B x y + B y x) / 2) ^ 2 ≤ B x x * B y y := by
    refine sq_le_mul_of_forall_quadratic_nonneg fun t ↦ ?_
    have h := hnonneg (x + t • y)
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    field_simp
    nlinarith [h]
  have h2 : (0 : K) < 2 := two_pos
  nlinarith [key]

/-- The bilinear form on `K²` with matrix `!![1, 2; 0, 1]`, i.e.
`B x y = x₀ y₀ + 2 x₀ y₁ + x₁ y₁`.  It is nonnegative definite but not symmetric. -/
def notSymm : (Fin 2 → K) →ₗ[K] (Fin 2 → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun x y ↦ x 0 * y 0 + 2 * (x 0 * y 1) + x 1 * y 1)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ ↦ by simp only [Pi.add_apply]; ring)
    (fun _ _ _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring)

omit [LinearOrder K] [IsStrictOrderedRing K] in
@[simp] lemma notSymm_apply (x y : Fin 2 → K) :
    notSymm x y = x 0 * y 0 + 2 * (x 0 * y 1) + x 1 * y 1 :=
  LinearMap.mk₂_apply _ _ _ _

/-- `notSymm` is nonnegative definite: `B z z = (z₀ + z₁) ^ 2`. -/
theorem nonneg_notSymm (z : Fin 2 → K) : 0 ≤ (notSymm (K := K)) z z := by
  have h : (notSymm (K := K)) z z = (z 0 + z 1) ^ 2 := by simp only [notSymm_apply]; ring
  rw [h]
  exact sq_nonneg _

/-- **Cauchy–Schwarz fails for `notSymm`**: at the two standard basis vectors,
`B x y ^ 2 = 4` while `B x x * B y y = 1`. -/
theorem mul_notSymm_lt_sq_notSymm :
    (notSymm (K := K)) ![1, 0] ![1, 0] * (notSymm (K := K)) ![0, 1] ![0, 1]
      < ((notSymm (K := K)) ![1, 0] ![0, 1]) ^ 2 := by
  simp only [notSymm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  norm_num

/-- **A nonnegative definite bilinear form need not satisfy Cauchy–Schwarz.**  The symmetry
hypothesis in `LinearMap.BilinMap.sq_apply_le_of_symm_of_nonneg` is not redundant. -/
theorem exists_nonneg_not_sq_apply_le :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (B : V →ₗ[K] V →ₗ[K] K) (x y : V),
      (∀ z, 0 ≤ B z z) ∧ B x x * B y y < B x y ^ 2 :=
  ⟨Fin 2 → K, inferInstance, inferInstance, notSymm, ![1, 0], ![0, 1],
    nonneg_notSymm, mul_notSymm_lt_sq_notSymm⟩

end LinearMap.BilinMap

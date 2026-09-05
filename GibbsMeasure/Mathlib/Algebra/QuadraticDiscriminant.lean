/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Cauchy–Schwarz from a nonnegative quadratic

The Cauchy–Schwarz inequality for a symmetric bilinear form that is merely *nonnegative
definite* (no definiteness, hence no inner product space): if `B` is symmetric and
`0 ≤ B x x` for all `x`, then `B x y ^ 2 ≤ B x x * B y y`.

The whole content is the discriminant of the quadratic `t ↦ B (x + t • y) (x + t • y)`, which
is isolated as `sq_le_mul_of_forall_quadratic_nonneg`: over a linearly ordered field, if
`a + 2 t b + t ^ 2 c ≥ 0` for every `t`, then `b ^ 2 ≤ a * c`.  This scalar form is what a
nonnegative form gives when it is not attached to a module, e.g. the form
`(f, g) ↦ ∫ f · (g ∘ r) dμ` of a reflection-positive measure `μ`, which is defined only on a
set of bounded measurable functions.
-/

@[expose] public section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **Cauchy–Schwarz, scalar form.** If the quadratic `t ↦ a + 2 t b + t ^ 2 c` is nonnegative
for every `t`, then `b ^ 2 ≤ a * c`. -/
theorem sq_le_mul_of_forall_quadratic_nonneg {a b c : K}
    (h : ∀ t : K, 0 ≤ a + 2 * t * b + t ^ 2 * c) : b ^ 2 ≤ a * c := by
  have hd : discrim c (2 * b) a ≤ 0 :=
    discrim_le_zero fun t ↦ by have := h t; nlinarith [h t]
  rw [discrim] at hd
  nlinarith [hd]

/-- **Cauchy–Schwarz for a nonnegative definite symmetric bilinear form.** -/
theorem LinearMap.BilinMap.sq_apply_le_of_symm_of_nonneg {V : Type*} [AddCommGroup V]
    [Module K V] {B : V →ₗ[K] V →ₗ[K] K} (hsymm : ∀ x y, B x y = B y x)
    (hnonneg : ∀ x, 0 ≤ B x x) (x y : V) : B x y ^ 2 ≤ B x x * B y y := by
  refine sq_le_mul_of_forall_quadratic_nonneg fun t ↦ ?_
  have h := hnonneg (x + t • y)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  rw [hsymm y x] at h
  nlinarith [h]

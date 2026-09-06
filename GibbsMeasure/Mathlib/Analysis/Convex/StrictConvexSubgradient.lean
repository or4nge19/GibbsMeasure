/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.TangentFunctional

/-!
# The subdifferential of a strictly convex function is injective

A linear functional `L` is a subgradient of `f` at `x` when `L y ≤ f (x + y) − f x` for all `y`
(`subgradientAt`), equivalently when `x` minimises `f − L`. If `f` is strictly convex, the
minimiser of `f − L` is unique, so `L` can be a subgradient of `f` at one point at most:

* `StrictConvexOn.eq_of_mem_subgradientAt`.

This is the elementary half of the Legendre correspondence between the subdifferential of a
convex function and that of its conjugate (Rockafellar, *Convex Analysis*, Theorem 26.3): a
convex function whose conjugate is strictly convex has at most one subgradient at each point,
because a subgradient of the function at `x` is a point at which the conjugate is supported by
`x`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} {x y : E}

/-- **A strictly convex function is supported by a given linear functional at one point at
most.** If `L` is a subgradient of a strictly convex `f` both at `x` and at `y`, then `x = y`:
both points minimise `f − L`, so `f − L` takes the same value at them, and the midpoint would
give a strictly smaller value. -/
theorem StrictConvexOn.eq_of_mem_subgradientAt (hf : StrictConvexOn ℝ univ f)
    {L : E →ₗ[ℝ] ℝ} (hx : L ∈ subgradientAt f x) (hy : L ∈ subgradientAt f y) : x = y := by
  by_contra hne
  have hx' := mem_subgradientAt_iff.1 hx
  have hy' := mem_subgradientAt_iff.1 hy
  have hxy : f x - L x = f y - L y := le_antisymm (hx' y) (hy' x)
  set c : ℝ := 1 / 2 with hc
  have hstrict : f (c • x + c • y) < c • f x + c • f y :=
    hf.2 (mem_univ x) (mem_univ y) hne (by norm_num) (by norm_num) (by norm_num)
  rw [smul_eq_mul, smul_eq_mul] at hstrict
  have hlin : L (c • x + c • y) = c * L x + c * L y := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hmin := hx' (c • x + c • y)
  rw [hlin] at hmin
  rw [hc] at hstrict hmin
  linarith

/-- The subgradients of a strictly convex function at two different points are different. -/
theorem StrictConvexOn.subgradientAt_disjoint (hf : StrictConvexOn ℝ univ f) (hne : x ≠ y) :
    Disjoint (subgradientAt f x) (subgradientAt f y) :=
  Set.disjoint_left.2 fun _ hLx hLy ↦ hne (hf.eq_of_mem_subgradientAt hLx hLy)

end

end

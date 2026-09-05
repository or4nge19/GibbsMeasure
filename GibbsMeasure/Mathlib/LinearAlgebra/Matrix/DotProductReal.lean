/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Elementary inequalities for the real scalar product

The two inequalities `0 ≤ x ⬝ᵥ x` and `2 |x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y` on `ι → ℝ`.  The second is
the polarisation bound; it is weaker than Cauchy–Schwarz but suffices wherever a bilinear energy
has to be dominated by a sum of one-site energies.

## Main results

* `Matrix.dotProduct_self_nonneg`
* `Matrix.two_mul_abs_dotProduct_le`
-/

@[expose] public section

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- The real scalar product is positive semidefinite. -/
lemma dotProduct_self_nonneg (x : ι → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- **The polarisation bound** `2 |x · y| ≤ |x|² + |y|²`, from `0 ≤ |x ± y|²`. -/
lemma two_mul_abs_dotProduct_le (x y : ι → ℝ) : 2 * |x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y := by
  have h1 : 0 ≤ (x - y) ⬝ᵥ (x - y) := dotProduct_self_nonneg _
  have h2 : 0 ≤ (x + y) ⬝ᵥ (x + y) := dotProduct_self_nonneg _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm y x] at h1
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x] at h2
  rcases abs_cases (x ⬝ᵥ y) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith

/-- The scalar product of two vectors is bounded by the half-sum of their square lengths. -/
lemma dotProduct_le_half_add (x y : ι → ℝ) : x ⬝ᵥ y ≤ (x ⬝ᵥ x + y ⬝ᵥ y) / 2 := by
  have := two_mul_abs_dotProduct_le x y
  have h := le_abs_self (x ⬝ᵥ y)
  linarith

end Matrix

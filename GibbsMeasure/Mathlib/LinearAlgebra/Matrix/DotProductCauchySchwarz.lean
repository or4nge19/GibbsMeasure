/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.DotProductReal
public import Mathlib.Analysis.Real.Sqrt

/-!
# Cauchy–Schwarz for the real dot product

`Matrix.dotProduct` on `ι → ℝ` is the standard inner product; this file records the
Cauchy–Schwarz inequality for it in the form `|x ⬝ᵥ y| ≤ √(x ⬝ᵥ x) * √(y ⬝ᵥ y)`, which is what
one needs when the two factors are controlled separately.  It is the sharpening of
`Matrix.two_mul_abs_dotProduct_le` (`2|x ⬝ᵥ y| ≤ x ⬝ᵥ x + y ⬝ᵥ y`), whose right-hand side is a
*sum* and therefore useless when the two sites carry different weights.

Its natural home is next to `Matrix.two_mul_abs_dotProduct_le` in
`GibbsMeasure.Mathlib.LinearAlgebra.Matrix.DotProductReal`.
-/

@[expose] public section

open Finset

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- **Cauchy–Schwarz for the real dot product.** -/
lemma abs_dotProduct_le_sqrt_mul_sqrt (x y : ι → ℝ) :
    |x ⬝ᵥ y| ≤ Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by
  have hsq : ∀ z : ι → ℝ, z ⬝ᵥ z = ∑ i, z i ^ 2 := fun z ↦ by
    simp [dotProduct, sq]
  have key : ∀ z : ι → ℝ, z ⬝ᵥ y ≤ Real.sqrt (z ⬝ᵥ z) * Real.sqrt (y ⬝ᵥ y) := by
    intro z
    rw [hsq z, hsq y]
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ z y
  rcases abs_cases (x ⬝ᵥ y) with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; exact key x
  · rw [h, ← neg_dotProduct]
    have hneg : (-x) ⬝ᵥ (-x) = x ⬝ᵥ x := by simp [dotProduct]
    simpa [hneg] using key (-x)

end Matrix

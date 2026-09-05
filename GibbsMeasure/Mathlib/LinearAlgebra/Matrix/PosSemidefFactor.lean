/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Gram factorisation of a positive semidefinite matrix

`Matrix.PosSemidef.exists_conjTranspose_mul_self`: a positive semidefinite matrix over `ℝ` or `ℂ`
is `Bᴴ * B`, i.e. it is the Gram matrix of a family of vectors.  Mathlib has the converse
(`Matrix.posSemidef_conjTranspose_mul_self`) but not this direction.  The witness is
`B = diagonal (√ eigenvalues) * Uᴴ` for the unitary `U` of the spectral theorem.

`Matrix.PosSemidef.exists_sum_mul` is the entrywise form `M i j = ∑ a, B a i * B a j` over `ℝ`,
which is how a positive semidefinite interaction matrix is turned into a sum of squares.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

/-- **Every positive semidefinite matrix is a Gram matrix.**  If `M` is positive semidefinite
then `M = Bᴴ * B` for `B = diagonal (√ eigenvalues) * Uᴴ`, with `U` the unitary diagonalising
`M`. -/
theorem PosSemidef.exists_conjTranspose_mul_self {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    ∃ B : Matrix n n 𝕜, M = Bᴴ * B := by
  classical
  have hherm : M.IsHermitian := hM.1
  set V : Matrix n n 𝕜 := (hherm.eigenvectorUnitary : Matrix n n 𝕜) with hV
  set D : Matrix n n 𝕜 :=
    Matrix.diagonal fun i ↦ (RCLike.ofReal (Real.sqrt (hherm.eigenvalues i)) : 𝕜) with hD
  have hspec : M = V * Matrix.diagonal (RCLike.ofReal ∘ hherm.eigenvalues) * Vᴴ := by
    have h := hherm.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa only [hV, Unitary.coe_star, Matrix.star_eq_conjTranspose] using h
  have hDherm : Dᴴ = D := by
    rw [hD, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have hDD : D * D = Matrix.diagonal (RCLike.ofReal ∘ hherm.eigenvalues) := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    rw [Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
  refine ⟨D * Vᴴ, ?_⟩
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDherm]
  rw [hspec, ← hDD]
  simp [Matrix.mul_assoc]

/-- **A real positive semidefinite matrix is a sum of squares**, entrywise:
`M i j = ∑ a, B a i * B a j`.  This is `PosSemidef.exists_conjTranspose_mul_self` read off in
coordinates. -/
theorem PosSemidef.exists_sum_mul {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    ∃ B : Matrix n n ℝ, ∀ i j, M i j = ∑ a, B a i * B a j := by
  classical
  obtain ⟨B, hB⟩ := hM.exists_conjTranspose_mul_self
  refine ⟨B, fun i j ↦ ?_⟩
  rw [hB]
  simp [Matrix.mul_apply]

end Matrix

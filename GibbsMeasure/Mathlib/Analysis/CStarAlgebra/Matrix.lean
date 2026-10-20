/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The `L²` operator norm of matrices: eigenvalues and determinants

For the `L²` operator norm on `Matrix n n 𝕜` (scope `Matrix.Norms.L2Operator`):

* `l2_opNorm_one_le`: `‖1‖ ≤ 1`.
* `abs_eigenvalues_le_l2_opNorm`: the eigenvalues of a Hermitian matrix are bounded by its norm.
* `norm_det_le_l2_opNorm_pow`: `‖det A‖ ≤ ‖A‖ ^ card n` (`|det A|² = det (Aᴴ A)` is the product of
  the eigenvalues of `Aᴴ A`, each at most `‖Aᴴ A‖ = ‖A‖²`).

Searched (pin `d13f23b7`): `Mathlib/Analysis/CStarAlgebra/Matrix.lean` (`l2_opNorm_*`: diagonal,
conjugate transpose, C⋆-identity, `mulVec`), `Mathlib/Analysis/Matrix/Spectrum.lean`
(`IsHermitian.det_eq_prod_eigenvalues`, `mulVec_eigenvectorBasis`), `rg "det.*‖|norm_det"`: no
norm bound for eigenvalues or determinants; `Matrix.det_le` bounds by the entries only.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem l2_opNorm_one_le : ‖(1 : Matrix n n 𝕜)‖ ≤ 1 := by
  rw [← diagonal_one, l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ ↦ by simp

/-- **The eigenvalues of a Hermitian matrix are bounded by its `L²` operator norm.** -/
theorem abs_eigenvalues_le_l2_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  have hv : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h := (toEuclideanCLM (n := n) (𝕜 := 𝕜) A).le_opNorm (hA.eigenvectorBasis i)
  rw [l2_opNorm_toEuclideanCLM, hv, mul_one] at h
  have he : toEuclideanCLM (n := n) (𝕜 := 𝕜) A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : 𝕜) • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    rw [ofLp_toEuclideanCLM, WithLp.ofLp_smul, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    exact hA.mulVec_eigenvectorBasis i
  rwa [he, norm_smul, hv, mul_one, RCLike.norm_ofReal] at h

/-- **Determinant bound**: `‖det A‖ ≤ ‖A‖ ^ card n` in the `L²` operator norm. -/
theorem norm_det_le_l2_opNorm_pow (A : Matrix n n 𝕜) : ‖A.det‖ ≤ ‖A‖ ^ Fintype.card n := by
  have hH := isHermitian_conjTranspose_mul_self A
  have h1 : ‖A.det‖ ^ 2 = ∏ i, |hH.eigenvalues i| := by
    have := hH.det_eq_prod_eigenvalues
    rw [det_mul, det_conjTranspose] at this
    rw [sq]
    nth_rewrite 1 [← norm_star]
    rw [← norm_mul, this, norm_prod]
    simp
  have h2 : ∏ i, |hH.eigenvalues i| ≤ (‖A‖ ^ Fintype.card n) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, sq, ← l2_opNorm_conjTranspose_mul_self]
    calc _ ≤ ∏ _i : n, ‖Aᴴ * A‖ :=
          Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ abs_eigenvalues_le_l2_opNorm hH i
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (h1 ▸ h2)

end Matrix

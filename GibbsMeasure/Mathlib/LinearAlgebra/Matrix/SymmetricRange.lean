/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Matrix.Spectrum

/-!
# The range of a real symmetric matrix is the orthogonal of its kernel

`Matrix.IsHermitian.exists_mulVec_eq_of_forall_dotProduct_eq_zero`: for a real symmetric matrix
`A`, a vector `c` orthogonal to the kernel of `A` lies in the range of `A`. Proved by expanding
`c` in an orthonormal eigenbasis of `A` (`Matrix.IsHermitian.eigenvectorBasis`) and dividing by
the nonzero eigenvalues; the eigenvectors with eigenvalue `0` lie in the kernel, so they carry no
component of `c`.

This is the linear-algebraic input for Gaussian regression (`ProbabilityTheory.IsGaussianProcess.
exists_condExp_eq_affine`): it solves `Cov(Y) v = Cov(X, Y)` for `v` without assuming that the
covariance matrix `Cov(Y)` is invertible.
-/

@[expose] public section

open Matrix
open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- For a real symmetric matrix `A`, a vector orthogonal to `ker A` is in the range of `A`. -/
theorem exists_mulVec_eq_of_forall_dotProduct_eq_zero (hA : A.IsHermitian) {c : n → ℝ}
    (hc : ∀ a, A *ᵥ a = 0 → a ⬝ᵥ c = 0) : ∃ v, A *ᵥ v = c := by
  classical
  set e := hA.eigenvectorBasis with he
  set lam := hA.eigenvalues with hlam
  refine ⟨∑ j, (if lam j = 0 then 0 else (⇑(e j) ⬝ᵥ c) / lam j) • ⇑(e j), ?_⟩
  have hAv : A *ᵥ (∑ j, (if lam j = 0 then 0 else (⇑(e j) ⬝ᵥ c) / lam j) • ⇑(e j)) =
      ∑ j, (⇑(e j) ⬝ᵥ c) • ⇑(e j) := by
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Matrix.mulVec_smul, hA.mulVec_eigenvectorBasis]
    by_cases hj : lam j = 0
    · have h0 : A *ᵥ ⇑(e j) = 0 := by
        rw [hA.mulVec_eigenvectorBasis]
        change lam j • ⇑(e j) = 0
        rw [hj, zero_smul]
      rw [ite_eq_left hj, hc _ h0, zero_smul, zero_smul]
    · rw [ite_eq_right hj, smul_smul]
      change ((⇑(e j) ⬝ᵥ c) / lam j * lam j) • ⇑(e j) = _
      rw [div_mul_cancel₀ _ hj]
  rw [hAv]
  have hsum := e.sum_repr' (WithLp.toLp 2 c)
  have hcoe := congrArg WithLp.ofLp hsum
  rw [WithLp.ofLp_sum] at hcoe
  simp only [WithLp.ofLp_smul] at hcoe
  refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) hcoe
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

end Matrix.IsHermitian

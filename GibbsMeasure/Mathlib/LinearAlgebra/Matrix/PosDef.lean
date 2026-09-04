/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive definiteness over an arbitrary index type via finite principal submatrices

Besides the bridge `Matrix.posDef_iff_forall_finset_submatrix` between the finitely-supported
notion of positive definiteness and the finite principal submatrices, this file proves the
variational characterisation of the quadratic form of `A⁻¹`,

`t ⬝ᵥ A⁻¹ *ᵥ t = sup_x (2 (t ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x)`,

and its consequence `Matrix.PosDef.dotProduct_mulVec_inv_submatrix_le`: the quadratic form of the
inverse of a principal submatrix is dominated by the quadratic form of the inverse, i.e.
`(A_{II})⁻¹ ≤ (A⁻¹)_{II}` in the positive semidefinite order.
-/

@[expose] public section

open scoped Matrix

/-- A real matrix over an arbitrary index type is positive definite (in the finitely supported
sense of `Matrix.PosDef`) iff every finite principal submatrix is positive definite. This is the
bridge between Georgii's (13.3) and the finite-volume matrices `𝒥_Λ` of (13.12). -/
theorem Matrix.posDef_iff_forall_finset_submatrix {ι : Type*} {A : Matrix ι ι ℝ} :
    A.PosDef ↔ ∀ Λ : Finset ι, (A.submatrix (Subtype.val : Λ → ι) Subtype.val).PosDef := by
  classical
  refine ⟨fun hA Λ ↦ hA.submatrix Subtype.val_injective, fun h ↦ ⟨?_, fun x hx ↦ ?_⟩⟩
  · refine Matrix.IsHermitian.ext fun i j ↦ ?_
    have := (h {i, j}).1.apply ⟨i, by simp⟩ ⟨j, by simp⟩
    simpa using this
  · set Λ := x.support with hΛ
    set y : Λ → ℝ := fun i ↦ x i with hy
    have hy0 : y ≠ 0 := by
      intro hy0
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 hx
      have := congrFun hy0 ⟨i, hi⟩
      simp only [hy, Pi.zero_apply] at this
      exact (Finsupp.mem_support_iff.1 hi) this
    have hpos := ((Matrix.posDef_iff_dotProduct_mulVec).1 (h Λ)).2 hy0
    simp only [star_trivial] at hpos
    refine lt_of_lt_of_eq hpos ?_
    simp only [Finsupp.sum, star_trivial, dotProduct, Matrix.mulVec, Matrix.submatrix_apply, hy,
      Finset.mul_sum]
    rw [← Finset.sum_coe_sort Λ]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_coe_sort Λ]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring


open Finset in
/-- If `f : n → ℝ` vanishes off the range of an injective `e : m → n`, its total sum is the sum of
`f ∘ e`. -/
private theorem Fintype.sum_eq_sum_comp_of_eq_zero_of_notMem_range
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] {e : m → n}
    (he : Function.Injective e) (f : n → ℝ) (hf : ∀ j, (∀ i, e i ≠ j) → f j = 0) :
    ∑ j, f j = ∑ i, f (e i) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := e) (f := f)
    fun x _ y _ hxy ↦ he hxy]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_).symm
  exact hf j fun i hij ↦ hj (Finset.mem_image.2 ⟨i, Finset.mem_univ i, hij⟩)

namespace Matrix.PosDef

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] in
/-- A real positive definite matrix is symmetric. -/
theorem transpose_eq (hA : A.PosDef) : Aᵀ = A := by
  have hh : Aᴴ = A := hA.isHermitian
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at hh

omit [DecidableEq n] in
/-- For a real positive definite (hence symmetric) matrix, `u ᵥ* A = A *ᵥ u`. -/
theorem vecMul_eq_mulVec (hA : A.PosDef) (u : n → ℝ) : u ᵥ* A = A *ᵥ u := by
  conv_lhs => rw [← hA.transpose_eq]
  exact Matrix.vecMul_transpose A u

/-- **The variational characterisation of the quadratic form of `A⁻¹`.** For a positive definite
real matrix `A`, the concave quadratic `x ↦ 2 (t ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x` is bounded above by
`t ⬝ᵥ A⁻¹ *ᵥ t`, with equality at `x = A⁻¹ *ᵥ t`
(`Matrix.PosDef.two_mul_dotProduct_sub_dotProduct_mulVec_inv`). -/
theorem two_mul_dotProduct_sub_dotProduct_mulVec_le (hA : A.PosDef) (t x : n → ℝ) :
    2 * (t ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x ≤ t ⬝ᵥ A⁻¹ *ᵥ t := by
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.PosDef.det_pos hA).ne'.isUnit
  set z : n → ℝ := A⁻¹ *ᵥ t with hz
  have hAz : A *ᵥ z = t := by rw [hz, Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
  have hnonneg : 0 ≤ (x - z) ⬝ᵥ A *ᵥ (x - z) := by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (x - z)
  have hzAx : z ⬝ᵥ A *ᵥ x = t ⬝ᵥ x := by
    rw [dotProduct_mulVec, hA.vecMul_eq_mulVec, hAz]
  have hexp : (x - z) ⬝ᵥ A *ᵥ (x - z)
      = x ⬝ᵥ A *ᵥ x - 2 * (t ⬝ᵥ x) + t ⬝ᵥ A⁻¹ *ᵥ t := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hAz, hzAx,
      dotProduct_comm x t, dotProduct_comm z t, ← hz]
    ring
  rw [hexp] at hnonneg
  linarith

/-- Equality in `Matrix.PosDef.two_mul_dotProduct_sub_dotProduct_mulVec_le` at `x = A⁻¹ *ᵥ t`. -/
theorem two_mul_dotProduct_sub_dotProduct_mulVec_inv (hA : A.PosDef) (t : n → ℝ) :
    2 * (t ⬝ᵥ (A⁻¹ *ᵥ t)) - (A⁻¹ *ᵥ t) ⬝ᵥ A *ᵥ (A⁻¹ *ᵥ t) = t ⬝ᵥ A⁻¹ *ᵥ t := by
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Matrix.PosDef.det_pos hA).ne'.isUnit
  have hAz : A *ᵥ (A⁻¹ *ᵥ t) = t := by
    rw [Matrix.mulVec_mulVec, hAinv, Matrix.one_mulVec]
  rw [hAz, dotProduct_comm (A⁻¹ *ᵥ t) t]
  ring

/-- **The quadratic form of the inverse of a principal submatrix is dominated by the quadratic
form of the inverse.** For `A` positive definite, `e : m → n` injective, and any `t' : n → ℝ`
extending `t : m → ℝ` along `e`,

`t ⬝ᵥ (A.submatrix e e)⁻¹ *ᵥ t ≤ t' ⬝ᵥ A⁻¹ *ᵥ t'`.

Taking `t'` to be the extension of `t` by zero, this is `(A_{II})⁻¹ ≤ (A⁻¹)_{II}` in the positive
semidefinite order for a principal submatrix `A_{II}`. It is the linear algebra underlying
Georgii's monotonicity display in the proof of Theorem (13.26):
`∑_{i,j ∈ Λ} 𝒥_Λ⁻¹(i,j) t_i t_j ≤ ∑_{i,j ∈ Λ} 𝒥_Δ⁻¹(i,j) t_i t_j` for `Λ ⊆ Δ`. Both sides are, by
`Matrix.PosDef.two_mul_dotProduct_sub_dotProduct_mulVec_le`, suprema of one and the same concave
quadratic — on the left over the vectors supported in the range of `e`, on the right over all
vectors. -/
theorem dotProduct_mulVec_inv_submatrix_le {m : Type*} [Fintype m] [DecidableEq m]
    (hA : A.PosDef) {e : m → n} (he : Function.Injective e) (t : m → ℝ) (t' : n → ℝ)
    (ht : ∀ i, t' (e i) = t i) :
    t ⬝ᵥ (A.submatrix e e)⁻¹ *ᵥ t ≤ t' ⬝ᵥ A⁻¹ *ᵥ t' := by
  classical
  set B : Matrix m m ℝ := A.submatrix e e with hB
  have hBpd : B.PosDef := hA.submatrix he
  set y : m → ℝ := B⁻¹ *ᵥ t with hy
  obtain ⟨x, hxe, hx0⟩ : ∃ x : n → ℝ, (∀ i, x (e i) = y i) ∧
      ∀ j, (∀ i, e i ≠ j) → x j = 0 := by
    refine ⟨Function.extend e y 0, fun i ↦ he.extend_apply _ _ i, fun j hj ↦ ?_⟩
    rw [Function.extend_apply' _ _ _ (by rintro ⟨i, rfl⟩; exact hj i rfl)]
    rfl
  have hBy : B *ᵥ y = t := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Matrix.PosDef.det_pos hBpd).ne'.isUnit,
      Matrix.one_mulVec]
  have hlin : t' ⬝ᵥ x = t ⬝ᵥ y := by
    show ∑ j, t' j * x j = ∑ i, t i * y i
    rw [Fintype.sum_eq_sum_comp_of_eq_zero_of_notMem_range he (fun j ↦ t' j * x j)
      fun j hj ↦ by rw [hx0 j hj, mul_zero]]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [ht i, hxe i]
  have hquad : x ⬝ᵥ A *ᵥ x = y ⬝ᵥ B *ᵥ y := by
    have hinner : ∀ i : m, (A *ᵥ x) (e i) = (B *ᵥ y) i := by
      intro i
      show ∑ k, A (e i) k * x k = ∑ i', B i i' * y i'
      rw [Fintype.sum_eq_sum_comp_of_eq_zero_of_notMem_range he (fun k ↦ A (e i) k * x k)
        fun j hj ↦ by rw [hx0 j hj, mul_zero]]
      exact Finset.sum_congr rfl fun i' _ ↦ by rw [hxe i']; rfl
    show ∑ j, x j * (A *ᵥ x) j = ∑ i, y i * (B *ᵥ y) i
    rw [Fintype.sum_eq_sum_comp_of_eq_zero_of_notMem_range he (fun j ↦ x j * (A *ᵥ x) j)
      fun j hj ↦ by rw [hx0 j hj, zero_mul]]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hxe i, hinner i]
  have hmain := hA.two_mul_dotProduct_sub_dotProduct_mulVec_le t' x
  rw [hlin, hquad, hBy, dotProduct_comm y t] at hmain
  show t ⬝ᵥ y ≤ t' ⬝ᵥ A⁻¹ *ᵥ t'
  linarith

end Matrix.PosDef

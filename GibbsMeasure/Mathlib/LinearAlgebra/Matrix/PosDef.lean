/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definiteness is preserved by positive scalars
-/

@[expose] public section

theorem Matrix.PosDef.smul_of_pos {ι : Type*} [Finite ι] {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  have := Fintype.ofFinite ι
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (hA.isHermitian.smul (IsSelfAdjoint.all c))
    fun x hx ↦ ?_
  have hpos := hA.dotProduct_mulVec_pos hx
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact mul_pos hc hpos

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

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

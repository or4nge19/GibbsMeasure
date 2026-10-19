/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# The Pauli matrices

The Pauli matrices `σ₁ = !![0, 1; 1, 0]`, `σ₂ = !![0, -i; i, 0]`, `σ₃ = !![1, 0; 0, -1]`, indexed
by `Fin 3`, form a Hermitian Clifford triple: they are Hermitian (`isHermitian_pauli`) and
`σ_μ σ_ν + σ_ν σ_μ = 2 δ_{μν}` (`pauli_mul_add_pauli_mul`).

Searched (pin `d13f23b7`): `rg -i pauli Mathlib` finds only tactic documentation; Physlib has
Pauli matrices, but it is not a dependency of this library.
-/

@[expose] public section

namespace Matrix

/-- The **Pauli matrices** `σ₁ = !![0, 1; 1, 0]`, `σ₂ = !![0, -i; i, 0]`, `σ₃ = !![1, 0; 0, -1]`,
indexed by `Fin 3`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

theorem isHermitian_pauli (μ : Fin 3) : (pauli μ).IsHermitian := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, conjTranspose_apply]

/-- **The Clifford relations** `σ_μ σ_ν + σ_ν σ_μ = 2 δ_{μν}`. -/
theorem pauli_mul_add_pauli_mul (μ ν : Fin 3) :
    pauli μ * pauli ν + pauli ν * pauli μ = if μ = ν then 2 else 0 := by
  fin_cases μ <;> fin_cases ν <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, ofNat_apply] <;> ring_nf

end Matrix

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
# The Pauli matrices and Clifford families

The Pauli matrices `σ₁ = !![0, 1; 1, 0]`, `σ₂ = !![0, -i; i, 0]`, `σ₃ = !![1, 0; 0, -1]`, indexed
by `Fin 3`, form a Hermitian Clifford triple: they are Hermitian (`isHermitian_pauli`) and
`σ_μ σ_ν + σ_ν σ_μ = 2 δ_{μν}` (`pauli_mul_add_pauli_mul`). For any family with these Clifford
relations, `(∑ a_μ γ_μ)² = (∑ a_μ²) 1` (`sum_smul_mul_sum_smul_of_anticomm`), so `γ_v` is an
involution for a unit vector `v`; the doubled family `diag(σ_μ, -σ_μ)` again satisfies them
(`fromBlocks_neg_anticomm`).

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

/-- **A Clifford family squares to the quadratic form**: if `γ_μ γ_ν + γ_ν γ_μ = 2 δ_{μν}`, then
`(∑ a_μ γ_μ)² = (∑ a_μ²) 1`. -/
theorem sum_smul_mul_sum_smul_of_anticomm {ι n 𝕜 : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] [DecidableEq n] [Field 𝕜] [CharZero 𝕜] {γ : ι → Matrix n n 𝕜}
    (hγ : ∀ μ ν, γ μ * γ ν + γ ν * γ μ = if μ = ν then 2 else 0) (a : ι → 𝕜) :
    (∑ μ, a μ • γ μ) * (∑ μ, a μ • γ μ) = (∑ μ, a μ * a μ) • 1 := by
  have hS : (∑ μ, a μ • γ μ) * (∑ μ, a μ • γ μ) = ∑ μ, ∑ ν, (a μ * a ν) • (γ μ * γ ν) := by
    rw [Finset.sum_mul_sum]
    simp only [smul_mul_smul_comm]
  have hS' : (∑ μ, a μ • γ μ) * (∑ μ, a μ • γ μ) = ∑ μ, ∑ ν, (a μ * a ν) • (γ ν * γ μ) := by
    rw [hS, Finset.sum_comm]
    exact Finset.sum_congr rfl fun μ _ ↦ Finset.sum_congr rfl fun ν _ ↦ by rw [mul_comm]
  refine smul_right_injective (Matrix n n 𝕜) (two_ne_zero (α := 𝕜)) ?_
  simp only
  rw [two_smul]
  nth_rewrite 1 [hS]
  rw [hS', ← Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib, ← smul_add, hγ, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  rw [smul_comm, two_smul, one_add_one_eq_two]

/-- **The doubled family `diag(σ_μ, -σ_μ)` of a Clifford family is a Clifford family.** -/
theorem fromBlocks_neg_anticomm {ι n 𝕜 : Type*} [DecidableEq ι] [Fintype n] [DecidableEq n]
    [CommRing 𝕜]
    {σ : ι → Matrix n n 𝕜} (hσ : ∀ μ ν, σ μ * σ ν + σ ν * σ μ = if μ = ν then 2 else 0)
    (μ ν : ι) :
    fromBlocks (σ μ) 0 0 (-σ μ) * fromBlocks (σ ν) 0 0 (-σ ν) +
        fromBlocks (σ ν) 0 0 (-σ ν) * fromBlocks (σ μ) 0 0 (-σ μ) =
      if μ = ν then 2 else 0 := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add]
  simp only [mul_zero, zero_mul, add_zero, zero_add, neg_mul_neg, hσ μ ν]
  split_ifs
  · ext (i | i) (j | j) <;> simp [ofNat_apply]
  · simp

end Matrix

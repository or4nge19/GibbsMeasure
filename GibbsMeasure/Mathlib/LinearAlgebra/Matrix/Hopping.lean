/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Hopping matrices

For a map `N : S → S` of sites and blocks `B : S → Matrix s s R`, the **hopping matrix**
`hoppingMatrix N B : Matrix (S × s) (S × s) R` is the matrix of `ψ ↦ (x ↦ B x (ψ (N x)))` on
`S × s`-indexed vectors: entry `((x, α), (y, β))` is `B x α β` if `N x = y` and `0` otherwise.
A nearest-neighbour lattice operator with one bond of each type at each site is a sum of these,
one for each type (the chamber Dirac matrix, `Model/ChamberDirac`).

## Main results

* `conjTranspose_hoppingMatrix`: for an involution `N`, the adjoint hops back along the same
  bonds with the adjoint blocks of the far ends, `(hop N B)ᴴ = hop N (fun x ↦ (B (N x))ᴴ)`.
* `reindex_hoppingMatrix_fromBlocks`: block-diagonal blocks give a block-diagonal hopping matrix
  in the splitting `S × (s ⊕ t) ≃ S × s ⊕ S × t`.
* `diagonal_mul_hoppingMatrix_mul_diagonal`: conjugation by site-diagonal matrices (gauge
  transformations) rescales the blocks by the values at the two ends.
* `hoppingMatrix_mul_hoppingMatrix`, `hoppingMatrix_id_one`, `hoppingMatrix_add`,
  `sum_hoppingMatrix`, `smul_hoppingMatrix`: the algebra of hopping matrices (hopping twice is
  hopping along the composite).

Searched (pin `d13f23b7`): `Mathlib/Data/Matrix/Composition.lean` (`Matrix.comp`, block matrices
`Matrix I J (Matrix K L R)`; no `conjTranspose` lemma), `SimpleGraph.adjMatrix` (scalar
weights only), `Matrix.blockDiagonal'`; no matrix-weighted adjacency of a functional graph.
-/

@[expose] public section

open Equiv

namespace Matrix

variable {S s t R : Type*}

section Basic

variable [DecidableEq S] [Zero R]

/-- The **hopping matrix** of `N : S → S` with blocks `B : S → Matrix s s R`: the matrix of
`ψ ↦ (x ↦ B x (ψ (N x)))`, with entry `B x α β` at `((x, α), (N x, β))` and `0` elsewhere. -/
def hoppingMatrix (N : S → S) (B : S → Matrix s s R) : Matrix (S × s) (S × s) R :=
  of fun a b ↦ if N a.1 = b.1 then B a.1 a.2 b.2 else 0

theorem hoppingMatrix_apply (N : S → S) (B : S → Matrix s s R) (a b : S × s) :
    hoppingMatrix N B a b = if N a.1 = b.1 then B a.1 a.2 b.2 else 0 :=
  rfl

/-- **Block-diagonal blocks give a block-diagonal hopping matrix** in the splitting
`S × (s ⊕ t) ≃ S × s ⊕ S × t`. -/
theorem reindex_hoppingMatrix_fromBlocks (N : S → S) (P : S → Matrix s s R)
    (Q : S → Matrix t t R) :
    reindex (prodSumDistrib S s t) (prodSumDistrib S s t)
        (hoppingMatrix N fun x ↦ fromBlocks (P x) 0 0 (Q x)) =
      fromBlocks (hoppingMatrix N P) 0 0 (hoppingMatrix N Q) := by
  ext (⟨x, α⟩ | ⟨x, α⟩) (⟨y, β⟩ | ⟨y, β⟩) <;> simp [hoppingMatrix_apply]

theorem hoppingMatrix_id_one [DecidableEq s] [One R] :
    hoppingMatrix id (fun _ : S ↦ (1 : Matrix s s R)) = 1 := by
  ext ⟨x, α⟩ ⟨y, β⟩
  by_cases h : x = y
  · subst h
    simp [hoppingMatrix_apply, one_apply]
  · simp [hoppingMatrix_apply, h]

end Basic

theorem hoppingMatrix_add [DecidableEq S] [AddZeroClass R] (N : S → S)
    (B B' : S → Matrix s s R) :
    hoppingMatrix N B + hoppingMatrix N B' = hoppingMatrix N fun x ↦ B x + B' x := by
  ext a b
  simp only [add_apply, hoppingMatrix_apply]
  split_ifs <;> simp

theorem sum_hoppingMatrix [DecidableEq S] [AddCommMonoid R] {ι : Type*} (t : Finset ι)
    (N : S → S) (B : ι → S → Matrix s s R) :
    ∑ i ∈ t, hoppingMatrix N (B i) = hoppingMatrix N fun x ↦ ∑ i ∈ t, B i x := by
  ext a b
  by_cases h : N a.1 = b.1 <;> simp [hoppingMatrix_apply, Matrix.sum_apply, h]

theorem smul_hoppingMatrix [DecidableEq S] {α : Type*} [Zero R] [SMulZeroClass α R] (c : α)
    (N : S → S) (B : S → Matrix s s R) :
    c • hoppingMatrix N B = hoppingMatrix N fun x ↦ c • B x := by
  ext a b
  simp only [smul_apply, hoppingMatrix_apply]
  split_ifs <;> simp

/-- **Hopping twice**: the product of two hopping matrices hops along the composite map, with
the product of the blocks along the way. -/
theorem hoppingMatrix_mul_hoppingMatrix [Fintype S] [DecidableEq S] [Fintype s]
    [NonUnitalNonAssocSemiring R] (N N' : S → S) (B B' : S → Matrix s s R) :
    hoppingMatrix N B * hoppingMatrix N' B' = hoppingMatrix (N' ∘ N) fun x ↦ B x * B' (N x) := by
  ext a b
  rw [mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (N a.1)]
  · simp only [hoppingMatrix_apply, ite_true, Function.comp_apply, mul_apply]
    split_ifs <;> simp
  · intro y _ hy
    simp [hoppingMatrix_apply, Ne.symm hy]
  · simp

/-- **The adjoint of a hopping matrix along an involution** hops back along the same bonds with
the adjoint blocks of the far ends. -/
theorem conjTranspose_hoppingMatrix [DecidableEq S] [AddMonoid R] [StarAddMonoid R]
    {N : S → S} (hN : Function.Involutive N) (B : S → Matrix s s R) :
    (hoppingMatrix N B)ᴴ = hoppingMatrix N fun x ↦ (B (N x))ᴴ := by
  ext a b
  have h : N b.1 = a.1 ↔ N a.1 = b.1 := ⟨fun h ↦ h ▸ hN b.1, fun h ↦ h ▸ hN a.1⟩
  rw [conjTranspose_apply, hoppingMatrix_apply, hoppingMatrix_apply]
  by_cases hab : N a.1 = b.1
  · rw [ite_eq_left (h.2 hab), ite_eq_left hab, conjTranspose_apply, ← hab]
  · rw [ite_eq_right (mt h.1 hab), ite_eq_right hab, star_zero]

/-- **Conjugation by site-diagonal matrices** rescales each block by the values at its two
ends. -/
theorem diagonal_mul_hoppingMatrix_mul_diagonal [Fintype S] [DecidableEq S] [Fintype s]
    [DecidableEq s] [CommSemiring R] (c c' : S → R) (N : S → S) (B : S → Matrix s s R) :
    diagonal (fun a : S × s ↦ c a.1) * hoppingMatrix N B * diagonal (fun b : S × s ↦ c' b.1) =
      hoppingMatrix N fun x ↦ (c x * c' (N x)) • B x := by
  ext a b
  rw [mul_diagonal, diagonal_mul, hoppingMatrix_apply, hoppingMatrix_apply]
  split_ifs with h
  · rw [smul_apply, smul_eq_mul, ← h]
    ring
  · rw [mul_zero, zero_mul]

end Matrix

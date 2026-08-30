/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Hom.Basic

/-!
# Mapping finsets along an equivalence
-/

@[expose] public section

namespace Finset

variable {α β : Type*} (e : α ≃ β) (s : Finset α)

lemma map_symm_toEmbedding_map_toEmbedding :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  ext; simp

lemma map_toEmbedding_map_symm_toEmbedding (t : Finset β) :
    (t.map e.symm.toEmbedding).map e.toEmbedding = t := by
  ext; simp

end Finset

namespace Equiv

variable {α β : Type*}

@[simp] lemma _root_.Finset.map_symm_map (σ : α ≃ β) (A : Finset α) :
    (A.map σ.toEmbedding).map σ.symm.toEmbedding = A := by
  ext; simp [Finset.mem_map_equiv]

@[simp] lemma _root_.Finset.map_map_symm (σ : α ≃ β) (B : Finset β) :
    (B.map σ.symm.toEmbedding).map σ.toEmbedding = B := by
  ext; simp [Finset.mem_map_equiv]

/-- A bijection of `α` acts on `Finset α` as an order isomorphism. -/
def finsetOrderIso (σ : α ≃ β) : Finset α ≃o Finset β where
  toFun A := A.map σ.toEmbedding
  invFun B := B.map σ.symm.toEmbedding
  left_inv := Finset.map_symm_map σ
  right_inv := Finset.map_map_symm σ
  map_rel_iff' := Finset.map_subset_map

@[simp] lemma finsetOrderIso_apply (σ : α ≃ β) (A : Finset α) :
    σ.finsetOrderIso A = A.map σ.toEmbedding := rfl

@[simp] lemma finsetOrderIso_symm_apply (σ : α ≃ β) (B : Finset β) :
    σ.finsetOrderIso.symm B = B.map σ.symm.toEmbedding := rfl

end Equiv

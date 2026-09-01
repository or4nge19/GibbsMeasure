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

namespace Equiv

variable {α β : Type*}

@[simp] lemma _root_.Finset.map_symm_map (σ : α ≃ β) (A : Finset α) :
    (A.map σ.toEmbedding).map σ.symm.toEmbedding = A := by
  ext; simp [Finset.mem_map_equiv]

@[simp] lemma _root_.Finset.map_map_symm (σ : α ≃ β) (B : Finset β) :
    (B.map σ.symm.toEmbedding).map σ.toEmbedding = B := by
  ext; simp [Finset.mem_map_equiv]

/-- A bijection of `α` acts on `Finset α` as an order isomorphism: `Equiv.Finset.congr` together
with `Finset.map_subset_map`. -/
def finsetOrderIso (σ : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := Equiv.Finset.congr σ
  map_rel_iff' := Finset.map_subset_map

@[simp] lemma finsetOrderIso_apply (σ : α ≃ β) (A : Finset α) :
    σ.finsetOrderIso A = A.map σ.toEmbedding := rfl

@[simp] lemma finsetOrderIso_symm_apply (σ : α ≃ β) (B : Finset β) :
    σ.finsetOrderIso.symm B = B.map σ.symm.toEmbedding := rfl

end Equiv

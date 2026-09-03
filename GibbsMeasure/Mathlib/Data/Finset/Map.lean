/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Data.Finset.Image
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

section Translate

variable {G : Type*} [AddCommGroup G]

/-- Translating a finite set twice is translating it by the sum.
(Intended home: `Mathlib/Data/Finset/Image.lean`.) -/
lemma Finset.map_addRightEmbedding_map (s : Finset G) (a b : G) :
    (s.map (addRightEmbedding a)).map (addRightEmbedding b)
      = s.map (addRightEmbedding (a + b)) := by
  rw [Finset.map_map]
  congr 1
  exact Function.Embedding.ext fun x ↦ by simp [addRightEmbedding]

/-- Translating a finite set by `a` and then by `-a` gives it back.
(Intended home: `Mathlib/Data/Finset/Image.lean`.) -/
lemma Finset.map_addRightEmbedding_neg (s : Finset G) (a : G) :
    (s.map (addRightEmbedding a)).map (addRightEmbedding (-a)) = s := by
  rw [Finset.map_addRightEmbedding_map, add_neg_cancel]
  have : addRightEmbedding (0 : G) = Function.Embedding.refl G :=
    Function.Embedding.ext fun x ↦ by simp [addRightEmbedding]
  rw [this, Finset.map_refl]

end Translate

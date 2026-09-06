/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Precomposing a bounded function

`lp (fun _ : β ↦ B) ∞` is the space of bounded functions `β → B`. Precomposition with an arbitrary
map `φ : α → β` sends a bounded function to a bounded function, and does so linearly and
multiplicatively.

## Main declarations

* `lp.precomp φ g`: the bounded function `g ∘ φ`.
* `lp.precompₐ 𝕜 φ`: the same as an algebra homomorphism, for `B` a normed `𝕜`-algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace lp

variable {α β B : Type*} [NormedAddCommGroup B]

/-- Precomposition of a bounded function `g : β → B` with a map `φ : α → β`, again a bounded
function. -/
def precomp (φ : α → β) (g : lp (fun _ : β ↦ B) ∞) : lp (fun _ : α ↦ B) ∞ :=
  ⟨⇑g ∘ φ, memℓp_infty ⟨‖g‖, by
    rintro _ ⟨a, rfl⟩
    exact norm_apply_le_norm ENNReal.top_ne_zero g (φ a)⟩⟩

@[simp] lemma coeFn_precomp (φ : α → β) (g : lp (fun _ : β ↦ B) ∞) :
    ⇑(precomp φ g) = ⇑g ∘ φ := rfl

@[simp] lemma precomp_apply (φ : α → β) (g : lp (fun _ : β ↦ B) ∞) (a : α) :
    ⇑(precomp φ g) a = ⇑g (φ a) := rfl

@[simp] lemma precomp_zero (φ : α → β) : precomp φ (0 : lp (fun _ : β ↦ B) ∞) = 0 := rfl

@[simp] lemma precomp_add (φ : α → β) (g h : lp (fun _ : β ↦ B) ∞) :
    precomp φ (g + h) = precomp φ g + precomp φ h := rfl

@[simp] lemma precomp_neg (φ : α → β) (g : lp (fun _ : β ↦ B) ∞) :
    precomp φ (-g) = -precomp φ g := rfl

@[simp] lemma precomp_sub (φ : α → β) (g h : lp (fun _ : β ↦ B) ∞) :
    precomp φ (g - h) = precomp φ g - precomp φ h := rfl

lemma norm_precomp_le (φ : α → β) (g : lp (fun _ : β ↦ B) ∞) : ‖precomp φ g‖ ≤ ‖g‖ :=
  norm_le_of_forall_le (norm_nonneg g) fun a ↦ norm_apply_le_norm ENNReal.top_ne_zero g (φ a)

section Module

variable {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 B] [IsBoundedSMul 𝕜 B]

@[simp] lemma precomp_smul (φ : α → β) (c : 𝕜) (g : lp (fun _ : β ↦ B) ∞) :
    precomp φ (c • g) = c • precomp φ g := rfl

end Module

section Ring

variable {C : Type*} [NonUnitalNormedRing C]

@[simp] lemma precomp_mul (φ : α → β) (g h : lp (fun _ : β ↦ C) ∞) :
    precomp φ (g * h) = precomp φ g * precomp φ h := rfl

end Ring

section Algebra

variable (𝕜 : Type*) {B : Type*} [NormedField 𝕜] [NormedRing B] [NormedAlgebra 𝕜 B]
  [NormOneClass B]

/-- Precomposition with `φ : α → β`, as an algebra homomorphism on the bounded functions. -/
def precompₐ (φ : α → β) : lp (fun _ : β ↦ B) ∞ →ₐ[𝕜] lp (fun _ : α ↦ B) ∞ where
  toFun := precomp φ
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] lemma coe_precompₐ (φ : α → β) :
    ⇑(precompₐ (B := B) 𝕜 φ) = precomp (B := B) φ := rfl

end Algebra

end lp

end

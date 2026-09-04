/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Lp.LpEquiv

/-!
# Bounded continuous functions as elements of `lp _ ∞`

`Mathlib.Analysis.Normed.Lp.LpEquiv` identifies `α →ᵇ E` with `lp (fun _ : α ↦ E) ∞` when `α` is
discrete. For an arbitrary topology on `α` only one direction survives: every bounded continuous
function is a bounded function, `BoundedContinuousFunction.toLpInfty`, and this map is a linear
isometry (it is `AddEquiv.lpBCF.symm` when `α` is discrete).
-/

@[expose] public section

open scoped BoundedContinuousFunction ENNReal

namespace BoundedContinuousFunction

variable {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]

/-- A bounded continuous function `α →ᵇ E`, viewed as an element of `lp (fun _ : α ↦ E) ∞`. -/
def toLpInfty (f : α →ᵇ E) : lp (fun _ : α ↦ E) ∞ :=
  ⟨⇑f, memℓp_infty f.bddAbove_range_norm_comp⟩

@[simp] theorem coe_toLpInfty (f : α →ᵇ E) : ⇑(toLpInfty f) = ⇑f := rfl

theorem norm_toLpInfty (f : α →ᵇ E) : ‖toLpInfty f‖ = ‖f‖ := by
  simp only [norm_eq_iSup_norm, lp.norm_eq_ciSup]; rfl

theorem toLpInfty_injective : Function.Injective (toLpInfty : (α →ᵇ E) → lp (fun _ : α ↦ E) ∞) :=
  fun _ _ h ↦ BoundedContinuousFunction.ext fun x ↦ congrFun (congrArg Subtype.val h) x

end BoundedContinuousFunction

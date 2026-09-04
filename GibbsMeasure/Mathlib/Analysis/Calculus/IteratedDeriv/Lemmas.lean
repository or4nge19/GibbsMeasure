/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Iterated derivatives of compositions with continuous linear maps

`iteratedDeriv n (g ∘ f) x = g (iteratedDeriv n f x)` for a continuous linear map `g`, and its
instance for the inner product with a fixed vector.
-/

@[expose] public section

open scoped RealInnerProductSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F G : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The iterated derivative of the composition with a continuous linear map on the left.
Intended home: `Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean`. -/
theorem ContinuousLinearMap.iteratedDeriv_comp_left {f : 𝕜 → F} (g : F →L[𝕜] G) {x : 𝕜} {n : ℕ}
    (hf : ContDiffAt 𝕜 n f x) :
    iteratedDeriv n (g ∘ f) x = g (iteratedDeriv n f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    g.iteratedFDeriv_comp_left hf le_rfl]
  rfl

/-- The iterated derivative of `t ↦ ⟪x, f t⟫` is `⟪x, f⁽ⁿ⁾ t⟫`. Intended home:
`Mathlib/Analysis/InnerProductSpace/Calculus.lean`. -/
theorem iteratedDeriv_inner_const_left {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : ℝ → V} {t : ℝ} {n : ℕ} (hf : ContDiffAt ℝ n f t) (x : V) :
    iteratedDeriv n (fun u ↦ ⟪x, f u⟫) t = ⟪x, iteratedDeriv n f t⟫ :=
  (innerSL ℝ x).iteratedDeriv_comp_left hf

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Comparing two integrals against a product measure through one marginal

`MeasureTheory.lintegral_le_of_lmarginal_le` compares `∫⁻ f ∂(⨂ᵢ μᵢ)` with `∫⁻ g ∂(⨂ᵢ μᵢ)` from a
pointwise comparison of the marginals `∫⋯∫⁻_s, f` and `∫⋯∫⁻_s, g` over a *finite* block `s` of
coordinates.  In applications the two marginals are not comparable on the nose but only after
rescaling — the block carries a density which is bounded above on one side and below on the other,
by constants which do not depend on the coordinates outside the block.  This file records that
rescaled form.

## Main result

* `MeasureTheory.const_mul_lintegral_le_of_lmarginal`: if
  `c · (∫⋯∫⁻_s, f) x ≤ m · (∫⋯∫⁻_s, g) x` for every `x`, then
  `c · ∫⁻ f ∂(⨂ᵢ μᵢ) ≤ m · ∫⁻ g ∂(⨂ᵢ μᵢ)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function
open scoped ENNReal

namespace MeasureTheory

variable {δ : Type*} [Fintype δ] [DecidableEq δ] {X : δ → Type*} [∀ i, MeasurableSpace (X i)]

omit [Fintype δ] in
/-- Scaling a function by a finite constant scales its marginal. -/
theorem lmarginal_const_mul (μ : ∀ i, Measure (X i)) (s : Finset δ)
    (f : (∀ i, X i) → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    (∫⋯∫⁻_s, (fun x ↦ c * f x) ∂μ) = fun x ↦ c * (∫⋯∫⁻_s, f ∂μ) x := by
  funext x
  simpa [lmarginal] using lintegral_const_mul' (μ := Measure.pi fun i : s ↦ μ i)
    (f := fun u ↦ f (updateFinset x s u)) c hc

/-- **A rescaled comparison of two integrals against a product measure, through one block of
coordinates.**  If a finite block `s` of coordinates witnesses `c · (∫⋯∫⁻_s, f) ≤ m · (∫⋯∫⁻_s, g)`
pointwise, then `c · ∫⁻ f ≤ m · ∫⁻ g` against the whole product measure.

This is `MeasureTheory.lintegral_le_of_lmarginal_le` with the two constants carried along; the
constants have to be finite because that is what makes `∫⁻ c * f = c * ∫⁻ f` unconditional. -/
theorem const_mul_lintegral_le_of_lmarginal (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (s : Finset δ) {f g : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {c m : ℝ≥0∞} (hc : c ≠ ∞) (hm : m ≠ ∞)
    (h : ∀ x, c * (∫⋯∫⁻_s, f ∂μ) x ≤ m * (∫⋯∫⁻_s, g ∂μ) x) :
    c * ∫⁻ x, f x ∂Measure.pi μ ≤ m * ∫⁻ x, g x ∂Measure.pi μ := by
  rw [← lintegral_const_mul' _ _ hc, ← lintegral_const_mul' _ _ hm]
  refine lintegral_le_of_lmarginal_le (μ := μ) s (hf.const_mul c) (hg.const_mul m) ?_
  rw [lmarginal_const_mul μ s f hc, lmarginal_const_mul μ s g hm]
  exact h

end MeasureTheory

end

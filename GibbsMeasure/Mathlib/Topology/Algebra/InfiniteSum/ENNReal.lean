/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Real.ENatENNReal

/-!
# Fibrewise summation, subtraction, and summability via `ENNReal.ofReal` in `ℝ≥0∞`
-/

@[expose] public section

open scoped ENNReal

/-- Summing `g ∘ f` fiberwise: `∑' a, g (f a) = ∑' b, |f⁻¹{b}| g b` in `ℝ≥0∞`. Intended home:
`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`. -/
theorem ENNReal.tsum_comp_eq_tsum_encard_preimage_mul {α β : Type*} (f : α → β) (g : β → ℝ≥0∞) :
    ∑' a, g (f a) = ∑' b, ((f ⁻¹' {b}).encard : ℝ≥0∞) * g b := by
  rw [← (Equiv.sigmaFiberEquiv f).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun b ↦ ?_
  rw [← ENNReal.tsum_set_const]
  exact tsum_congr fun x ↦ by simp [Equiv.sigmaFiberEquiv, x.2]

/-- Subtraction of `ℝ≥0∞`-valued sums, general index (Mathlib's `ENNReal.tsum_sub` is stated for
`ℕ`): if `g ≤ f` pointwise and `∑ g < ∞`, then `∑ (f - g) = ∑ f - ∑ g`. -/
lemma ENNReal.tsum_tsub {ι : Type*} {f g : ι → ℝ≥0∞} (hfg : ∀ i, g i ≤ f i)
    (hg : ∑' i, g i ≠ ⊤) : ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i := by
  refine ENNReal.eq_sub_of_add_eq hg ?_
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun i ↦ tsub_add_cancel_of_le (hfg i)

/-- A nonnegative real family is summable iff its `ENNReal.ofReal`-series is finite: the converse
of `Summable.tsum_ofReal_ne_top`, which needs no sign condition. -/
theorem ENNReal.tsum_ofReal_ne_top_iff_summable {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑' a, ENNReal.ofReal (f a) ≠ ∞ ↔ Summable f := by
  refine ⟨fun h ↦ ?_, Summable.tsum_ofReal_ne_top⟩
  refine (summable_congr fun a ↦ ?_).1 (ENNReal.summable_toReal h)
  exact ENNReal.toReal_ofReal (hf a)

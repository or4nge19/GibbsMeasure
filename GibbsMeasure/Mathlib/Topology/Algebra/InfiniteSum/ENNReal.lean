/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Data.Real.ENatENNReal
public import GibbsMeasure.Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fibrewise summation, subtraction, `ENNReal.ofReal`-summability, and Tannery's theorem in `ℝ≥0∞`
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

/-! ### Tannery's theorem for sums over a growing family of finite sets, in `ℝ≥0∞` -/

section Tannery

open Filter Finset
open scoped Topology

variable {α β : Type*} {l : Filter α}

/-- **Tannery's theorem for finite sums of growing length**, in `ℝ≥0∞`: if the finite sets `s a`
eventually contain every index, `f a b → g b` for every `b`, and `f a b ≤ bound b` for `b ∈ s a`
with `∑' b, bound b < ∞`, then `∑ b ∈ s a, f a b → ∑' b, g b`. -/
theorem ENNReal.tendsto_finsetSum_of_dominated_convergence {s : α → Finset β}
    {f : α → β → ℝ≥0∞} {g : β → ℝ≥0∞} {bound : β → ℝ≥0∞} (h_sum : ∑' b, bound b ≠ ∞)
    (hs : ∀ b, ∀ᶠ a in l, b ∈ s a) (hab : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (h_bound : ∀ᶠ a in l, ∀ b ∈ s a, f a b ≤ bound b) :
    Tendsto (fun a ↦ ∑ b ∈ s a, f a b) l (𝓝 (∑' b, g b)) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hbt : ∀ b, bound b ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top h_sum
  have hgb : ∀ b, g b ≤ bound b := fun b ↦
    le_of_tendsto (hab b) <| by filter_upwards [hs b, h_bound] with a ha hb using hb b ha
  have hgt : ∀ b, g b ≠ ∞ := fun b ↦ ne_top_of_le_ne_top (hbt b) (hgb b)
  have hgs : ∑' b, g b ≠ ∞ := ne_top_of_le_ne_top h_sum (ENNReal.tsum_le_tsum hgb)
  have hreal : Tendsto (fun a ↦ ∑ b ∈ s a, (f a b).toReal) l (𝓝 (∑' b, (g b).toReal)) := by
    refine _root_.tendsto_finsetSum_of_dominated_convergence (bound := fun b ↦ (bound b).toReal)
      (ENNReal.summable_toReal h_sum) hs
      (fun b ↦ (ENNReal.tendsto_toReal (hgt b)).comp (hab b)) ?_
    filter_upwards [h_bound] with a ha b hb
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hbt b) (ha b hb)
  rw [← ENNReal.ofReal_toReal hgs, ENNReal.tsum_toReal_eq hgt]
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [h_bound] with a ha
  rw [← ENNReal.toReal_sum fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb),
    ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb))]

/-- Tannery's theorem for `∑ k ∈ range n, f n k` in `ℝ≥0∞`: if `f n k → g k` for every `k` and
`f n k ≤ bound k` for `k < n` with `∑' k, bound k < ∞`, then `∑ k < n, f n k → ∑' k, g k`. -/
theorem ENNReal.tendsto_sum_range_of_dominated_convergence {f : ℕ → ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞}
    {bound : ℕ → ℝ≥0∞} (h_sum : ∑' k, bound k ≠ ∞) (hab : ∀ k, Tendsto (f · k) atTop (𝓝 (g k)))
    (h_bound : ∀ᶠ n in atTop, ∀ k < n, f n k ≤ bound k) :
    Tendsto (fun n ↦ ∑ k ∈ range n, f n k) atTop (𝓝 (∑' k, g k)) :=
  ENNReal.tendsto_finsetSum_of_dominated_convergence h_sum (fun k ↦ by
    simpa using eventually_gt_atTop k) hab (by simpa using h_bound)

end Tannery

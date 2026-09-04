/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Log.Summable
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Tanh
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite products of `tanh`

For a sequence `J : ι → ℝ`, the product `∏' i, tanh (J i)` converges to a positive limit exactly
when `∑ i, exp (-2 * J i) < ∞` (and `J i > 0`), because `1 - tanh x` is comparable to
`exp (-2 * x)` for `x ≥ 0`. We prove:

* `Real.summable_one_sub_tanh_iff`: `∑ (1 - tanh (J i)) < ∞ ↔ ∑ exp (-2 * J i) < ∞`, with no
  sign hypothesis on `J`;
* `Real.multipliable_tanh`, `Real.tprod_tanh_pos`: multipliability and positivity of the product;
* `Real.one_sub_tprod_tanh_le`: the quantitative bound
  `1 - ∏' i, tanh (J i) ≤ 2 * ∑' i, exp (-2 * J i)`;
* `Real.tendsto_prod_Ico_tanh_nhds_zero`: if `∑ i, exp (-2 * J i) = ∞` the partial products
  tend to `0`.

The general facts about infinite products behind them live where Mathlib keeps their
neighbours: `Real.tprod_pos_of_summable_log`, `Real.tprod_one_add_pos_of_summable` and
`Real.tendsto_prod_Ico_nhds_zero_of_not_summable_one_sub` in
`GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Log.Summable`, `tprod_le_one₀` and
`one_sub_tsum_le_tprod_one_sub` in `GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.Order`.
-/

@[expose] public section

open Filter Finset Topology

variable {ι : Type*}

namespace Real

/-! ### Products of `tanh` -/

variable {J : ι → ℝ}

/-- `∑ i, (1 - tanh (J i)) < ∞` if and only if `∑ i, exp (-2 * J i) < ∞`. No sign condition on
`J` is needed: either summability forces `J i > 0` for all but finitely many `i`. -/
theorem summable_one_sub_tanh_iff :
    (Summable fun i ↦ 1 - tanh (J i)) ↔ Summable fun i ↦ exp (-2 * J i) := by
  constructor
  · intro h
    refine .of_norm_bounded_eventually h ?_
    filter_upwards [h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)] with i hi
    have hJ : 0 ≤ J i := (tanh_pos_iff.1 (by linarith)).le
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_sub_tanh hJ
  · intro h
    exact .of_nonneg_of_le (fun i ↦ sub_nonneg.2 (tanh_lt_one _).le)
      (fun i ↦ one_sub_tanh_le_two_mul_exp _) (h.mul_left 2)

/-- If `∑ i, exp (-2 * J i) < ∞` then `∏ i, tanh (J i)` converges. -/
theorem multipliable_tanh (h : Summable fun i ↦ exp (-2 * J i)) :
    Multipliable fun i ↦ tanh (J i) := by
  have := Real.multipliable_one_add_of_summable (summable_one_sub_tanh_iff.2 h).neg
  simpa using this

/-- If `J i > 0` for all `i` and `∑ i, exp (-2 * J i) < ∞`, then `∏' i, tanh (J i) > 0`. -/
theorem tprod_tanh_pos (hJ : ∀ i, 0 < J i) (h : Summable fun i ↦ exp (-2 * J i)) :
    0 < ∏' i, tanh (J i) := by
  have := tprod_one_add_pos_of_summable (f := fun i ↦ -(1 - tanh (J i)))
    (fun i ↦ by simpa using tanh_pos (hJ i)) (summable_one_sub_tanh_iff.2 h).neg
  simpa using this

/-- If `J i ≥ 0` for all `i` and `∑ i, exp (-2 * J i) < ∞`, then
`1 - ∏' i, tanh (J i) ≤ 2 * ∑' i, exp (-2 * J i)`. -/
theorem one_sub_tprod_tanh_le (hJ : ∀ i, 0 ≤ J i) (h : Summable fun i ↦ exp (-2 * J i)) :
    1 - ∏' i, tanh (J i) ≤ 2 * ∑' i, exp (-2 * J i) := by
  have hs : Summable fun i ↦ 1 - tanh (J i) := summable_one_sub_tanh_iff.2 h
  have hm : Multipliable fun i ↦ 1 - (1 - tanh (J i)) := by simpa using multipliable_tanh h
  have h1 := one_sub_tsum_le_tprod_one_sub (fun i ↦ sub_nonneg.2 (tanh_lt_one _).le)
    (fun i ↦ by linarith [tanh_nonneg (hJ i)]) hs hm
  simp only [sub_sub_cancel] at h1
  calc 1 - ∏' i, tanh (J i) ≤ ∑' i, (1 - tanh (J i)) := by linarith
    _ ≤ ∑' i, 2 * exp (-2 * J i) :=
        hs.tsum_le_tsum (fun i ↦ one_sub_tanh_le_two_mul_exp _) (h.mul_left 2)
    _ = 2 * ∑' i, exp (-2 * J i) := tsum_mul_left

/-- If `J i ≥ 0` for all `i` and `∑ i, exp (-2 * J i) = ∞`, then the partial products
`∏ i ∈ Ico n N, tanh (J i)` tend to `0` as `N → ∞`, for every `n`. -/
theorem tendsto_prod_Ico_tanh_nhds_zero {J : ℕ → ℝ} (hJ : ∀ i, 0 ≤ J i)
    (h : ¬ Summable fun i ↦ exp (-2 * J i)) (n : ℕ) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, tanh (J i)) atTop (𝓝 0) :=
  tendsto_prod_Ico_nhds_zero_of_not_summable_one_sub (fun i ↦ tanh_nonneg (hJ i))
    (fun _ ↦ (tanh_lt_one _).le) (fun hs ↦ h (summable_one_sub_tanh_iff.1 hs)) n

end Real

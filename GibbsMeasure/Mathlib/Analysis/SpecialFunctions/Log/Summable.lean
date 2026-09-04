/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Positivity and divergence of real infinite products

* `Real.tprod_pos_of_summable_log`: `∏' i, f i > 0` for `f i > 0` with summable logarithms;
* `Real.tprod_one_add_pos_of_summable`: `∏' i, (1 + f i) > 0` for summable `f` with
  `1 + f i > 0` (the positivity counterpart of `Real.multipliable_one_add_of_summable`);
* `Real.tendsto_prod_Ico_nhds_zero_of_not_summable_one_sub`: if `0 ≤ f i ≤ 1` and
  `∑ (1 - f i) = ∞`, the partial products `∏ i ∈ Ico n N, f i` tend to `0`.
-/

@[expose] public section

open Filter Finset Topology

variable {ι : Type*}

namespace Real

/-- **Divergence of a product of factors in `[0, 1]`.** If `0 ≤ f i ≤ 1` and
`∑ i, (1 - f i) = ∞`, then the partial products `∏ i ∈ Ico n N, f i` tend to `0` as `N → ∞`,
for every `n`, since `∏ i ∈ Ico n N, f i ≤ exp (-∑ i ∈ Ico n N, (1 - f i))`. -/
theorem tendsto_prod_Ico_nhds_zero_of_not_summable_one_sub {f : ℕ → ℝ} (h0 : ∀ i, 0 ≤ f i)
    (h1 : ∀ i, f i ≤ 1) (hs : ¬ Summable fun i ↦ 1 - f i) (n : ℕ) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, f i) atTop (𝓝 0) := by
  have hS : Tendsto (fun N ↦ ∑ i ∈ range N, (1 - f i)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun i ↦ sub_nonneg.2 (h1 i)).1 hs
  have hbound : ∀ N, n ≤ N → ∏ i ∈ Ico n N, f i
      ≤ exp (∑ i ∈ range n, (1 - f i) - ∑ i ∈ range N, (1 - f i)) := by
    intro N hN
    calc ∏ i ∈ Ico n N, f i ≤ ∏ i ∈ Ico n N, exp (f i - 1) :=
          prod_le_prod (fun i _ ↦ h0 i) fun i _ ↦ by linarith [add_one_le_exp (f i - 1)]
      _ = exp (∑ i ∈ range n, (1 - f i) - ∑ i ∈ range N, (1 - f i)) := by
          rw [← exp_sum, ← sum_range_add_sum_Ico _ hN, sub_add_cancel_left, ← sum_neg_distrib]
          simp only [neg_sub]
  have hSneg : Tendsto (fun N ↦ ∑ i ∈ range n, (1 - f i) - ∑ i ∈ range N, (1 - f i)) atTop
      atBot := tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp hS)
  refine squeeze_zero' (Eventually.of_forall fun N ↦ prod_nonneg fun i _ ↦ h0 i) ?_
    (tendsto_exp_atBot.comp hSneg)
  filter_upwards [eventually_ge_atTop n] with N hN using hbound N hN

/-- An infinite product of positive reals with summable logarithms is positive. -/
theorem tprod_pos_of_summable_log {f : ι → ℝ} (hfn : ∀ i, 0 < f i)
    (hf : Summable fun i ↦ log (f i)) : 0 < ∏' i, f i := by
  rw [← rexp_tsum_eq_tprod hfn hf]
  exact exp_pos _

/-- If `f` is summable and `1 + f i > 0` for all `i`, then `∏' i, (1 + f i) > 0`.
Compare `Real.multipliable_one_add_of_summable`. -/
theorem tprod_one_add_pos_of_summable {f : ι → ℝ} (hfn : ∀ i, 0 < 1 + f i) (hf : Summable f) :
    0 < ∏' i, (1 + f i) :=
  tprod_pos_of_summable_log hfn (summable_log_one_add_of_summable hf)

end Real

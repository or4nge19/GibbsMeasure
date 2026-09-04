/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Tanh
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order

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

The general facts about infinite products behind them — positivity of `∏' i, f i` for
`0 < f i` with summable logarithms, the bound `∏' i, f i ≤ 1` for `0 ≤ f i ≤ 1`, the infinite
form `1 - ∑' i, f i ≤ ∏' i, (1 - f i)` of Weierstrass' product inequality, the convergence
of the partial products `∏ i ∈ Ico n N, f i` to the tail product `∏' i, f (i + n)`, and the
divergence of `∏ i ∈ Ico n N, f i` to `0` when `0 ≤ f i ≤ 1` and `∑ (1 - f i) = ∞` — are
stated first, in the generality in which they hold.
-/

@[expose] public section

open Filter Finset Topology

variable {ι : Type*}

/-! ### General infinite products -/

section Monoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M]

/-- If the tail `fun i ↦ f (i + n)` has product `m`, then the partial products
`∏ i ∈ Ico n N, f i` converge to `m` as `N → ∞`. -/
@[to_additive /-- If the tail `fun i ↦ f (i + n)` has sum `m`, then the partial sums
`∑ i ∈ Ico n N, f i` converge to `m` as `N → ∞`. -/]
theorem HasProd.tendsto_prod_Ico_nat {f : ℕ → M} {m : M} {n : ℕ}
    (h : HasProd (fun i ↦ f (i + n)) m) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, f i) atTop (𝓝 m) := by
  refine (h.tendsto_prod_nat.comp (tendsto_sub_atTop_nat n)).congr fun N ↦ ?_
  simp only [Function.comp_def, prod_Ico_eq_prod_range]
  exact prod_congr rfl fun k _ ↦ by rw [add_comm]

/-- If the tail `fun i ↦ f (i + n)` is multipliable, then the partial products
`∏ i ∈ Ico n N, f i` converge to the tail product `∏' i, f (i + n)` as `N → ∞`. -/
@[to_additive /-- If the tail `fun i ↦ f (i + n)` is summable, then the partial sums
`∑ i ∈ Ico n N, f i` converge to the tail sum `∑' i, f (i + n)` as `N → ∞`. -/]
theorem Multipliable.tendsto_prod_Ico_nat {f : ℕ → M} {n : ℕ}
    (h : Multipliable fun i ↦ f (i + n)) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, f i) atTop (𝓝 (∏' i, f (i + n))) :=
  h.hasProd.tendsto_prod_Ico_nat

end Monoid

section WithZero

variable {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R] [Preorder R] [ZeroLEOneClass R]
  [PosMulMono R] [ClosedIicTopology R]

/-- An infinite product of factors in `[0, 1]` is at most `1`. No multipliability is assumed: a
non-multipliable product is `1` by convention. See `tprod_le_one` for ordered monoids. -/
theorem tprod_le_one₀ {f : ι → R} (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) : ∏' i, f i ≤ 1 := by
  by_cases hf : Multipliable f
  · exact hasProd_le_of_prod_le hf.hasProd fun s ↦ prod_le_one (fun i _ ↦ h0 i) fun i _ ↦ h1 i
  · rw [tprod_eq_one_of_not_multipliable hf]

end WithZero

section OrderedRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [TopologicalSpace R]
  [OrderClosedTopology R]

/-- **Weierstrass' product inequality**, infinite form: `1 - ∑' i, f i ≤ ∏' i, (1 - f i)` for
`0 ≤ f i ≤ 1`, provided `f` is summable and `1 - f` is multipliable. -/
theorem one_sub_tsum_le_tprod_one_sub {f : ι → R} (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1)
    (hs : Summable f) (hm : Multipliable fun i ↦ 1 - f i) :
    1 - ∑' i, f i ≤ ∏' i, (1 - f i) := by
  refine le_hasProd_of_le_prod hm.hasProd fun s ↦ ?_
  calc 1 - ∑' i, f i ≤ 1 - ∑ i ∈ s, f i := by
        gcongr
        exact hs.sum_le_tsum s fun i _ ↦ h0 i
    _ ≤ ∏ i ∈ s, (1 - f i) := one_sub_sum_le_prod_one_sub (fun i _ ↦ h0 i) fun i _ ↦ h1 i

end OrderedRing

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

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Infinite products of factors in `[0, 1]`

* `tprod_le_one₀`: an infinite product of factors in `[0, 1]` in an ordered monoid with zero is
  at most `1` (the counterpart of `tprod_le_one`, which needs an ordered monoid);
* `one_sub_tsum_le_tprod_one_sub`: **Weierstrass' product inequality** in infinite form,
  `1 - ∑' i, f i ≤ ∏' i, (1 - f i)` for `0 ≤ f i ≤ 1`.
-/

@[expose] public section

open Finset

variable {ι : Type*}

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

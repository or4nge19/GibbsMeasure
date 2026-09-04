/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Weierstrass' product inequality

`1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i)` whenever `0 ≤ f i ≤ 1` on `s`. This is the lower bound
complementing `Finset.prod_le_one`; it is the finite form of the classical criterion for an
infinite product `∏ (1 - a_i)` with `a_i ∈ [0, 1]` to be positive when `∑ a_i < 1`.
-/

@[expose] public section

namespace Finset

variable {ι R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}

/-- **Weierstrass' product inequality**: `1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i)` when
`0 ≤ f i ≤ 1` for all `i ∈ s`. -/
theorem one_sub_sum_le_prod_one_sub (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    have h0a := h0 a (mem_insert_self a s)
    have h1a := h1 a (mem_insert_self a s)
    have ih' := ih (fun i hi ↦ h0 i (mem_insert_of_mem hi)) fun i hi ↦ h1 i (mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, f i := sum_nonneg fun i hi ↦ h0 i (mem_insert_of_mem hi)
    calc 1 - (f a + ∑ i ∈ s, f i)
        = (1 - f a) * (1 - ∑ i ∈ s, f i) - f a * ∑ i ∈ s, f i := by ring
      _ ≤ (1 - f a) * (1 - ∑ i ∈ s, f i) := sub_le_self _ (mul_nonneg h0a hsum)
      _ ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) := mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 h1a)

end Finset

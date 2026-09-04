/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Double sums of a symmetric function over a finset

`∑ i ∈ s, ∑ j ∈ s, f i j` for a symmetric `f` is the diagonal sum plus twice the strictly
upper-triangular sum.
-/

@[expose] public section

namespace Finset

variable {ι M : Type*} [AddCommMonoid M]

/-- A double sum over `s × s` of a symmetric function is the sum over the diagonal plus twice the
sum over the pairs `i < j`. -/
theorem sum_sum_eq_sum_diag_add_two_nsmul_sum_lt [LinearOrder ι] (s : Finset ι) {f : ι → ι → M}
    (hf : ∀ i j, f i j = f j i) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = ∑ i ∈ s, f i i + 2 • ∑ i ∈ s, ∑ j ∈ s with i < j, f i j := by
  classical
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if i = j then f i j else 0) +
      (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [hlt, hlt.ne, lt_asymm hlt]
    · simp
    · simp [hgt, hgt.ne', lt_asymm hgt]
  have hdiag : ∀ i ∈ s, ∑ j ∈ s, (if i = j then f i j else 0) = f i i := fun i hi ↦ by
    rw [sum_ite_eq]
    exact ite_eq_left hi
  have hlast : ∑ i ∈ s, ∑ j ∈ s, (if j < i then f i j else 0) =
      ∑ i ∈ s, ∑ j ∈ s, (if i < j then f i j else 0) := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ by rw [hf]
  calc ∑ i ∈ s, ∑ j ∈ s, f i j
      = ∑ i ∈ s, ((∑ j ∈ s, if i < j then f i j else 0) + f i i +
          ∑ j ∈ s, if j < i then f i j else 0) := by
        refine sum_congr rfl fun i hi ↦ ?_
        rw [← hdiag i hi, ← sum_add_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ hsplit i j
    _ = ∑ i ∈ s, f i i + 2 • ∑ i ∈ s, ∑ j ∈ s with i < j, f i j := by
        rw [sum_add_distrib, sum_add_distrib, hlast, two_nsmul]
        simp only [sum_filter]
        rw [add_right_comm, add_comm]

end Finset

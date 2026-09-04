/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Gibbs' inequality for finite sums

For nonnegative weights `p` and positive weights `q` on a finite set with the same total mass,
the relative entropy `∑ i, p i * log (p i / q i)` is nonnegative, and it vanishes if and only if
`p = q`. This is the finite-sum form of the fact that `klFun x = x log x - x + 1` is nonnegative
on `[0, ∞)` with `1` as its only zero:
`p i * log (p i / q i) = q i * klFun (p i / q i) + p i - q i`.
-/

@[expose] public section

open Finset Real

namespace InformationTheory

variable {ι : Type*} {s : Finset ι} {p q : ι → ℝ}

/-- `x log (x / y) = y klFun (x / y) + x - y` for `y ≠ 0`. -/
lemma mul_log_div_eq_mul_klFun_div_add_sub {x y : ℝ} (hy : y ≠ 0) :
    x * log (x / y) = y * klFun (x / y) + x - y := by
  rw [klFun_apply]
  field_simp
  ring

/-- Under the hypotheses of Gibbs' inequality, `∑ i ∈ s, p i * log (p i / q i)` is the sum of
the nonnegative terms `q i * klFun (p i / q i)`. -/
lemma sum_mul_log_div_eq_sum_mul_klFun_div (hq : ∀ i ∈ s, 0 < q i)
    (hpq : ∑ i ∈ s, p i = ∑ i ∈ s, q i) :
    ∑ i ∈ s, p i * log (p i / q i) = ∑ i ∈ s, q i * klFun (p i / q i) := by
  calc ∑ i ∈ s, p i * log (p i / q i)
      = ∑ i ∈ s, (q i * klFun (p i / q i) + p i - q i) :=
        sum_congr rfl fun i hi ↦ mul_log_div_eq_mul_klFun_div_add_sub (hq i hi).ne'
    _ = ∑ i ∈ s, q i * klFun (p i / q i) := by
        rw [sum_sub_distrib, sum_add_distrib, hpq, add_sub_cancel_right]

/-- **Gibbs' inequality.** For nonnegative `p` and positive `q` with the same total mass on `s`,
`0 ≤ ∑ i ∈ s, p i * log (p i / q i)`. -/
theorem sum_mul_log_div_nonneg (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hpq : ∑ i ∈ s, p i = ∑ i ∈ s, q i) :
    0 ≤ ∑ i ∈ s, p i * log (p i / q i) := by
  rw [sum_mul_log_div_eq_sum_mul_klFun_div hq hpq]
  exact sum_nonneg fun i hi ↦
    mul_nonneg (hq i hi).le (klFun_nonneg (div_nonneg (hp i hi) (hq i hi).le))

/-- **Equality in Gibbs' inequality.** For nonnegative `p` and positive `q` with the same total
mass on `s`, `∑ i ∈ s, p i * log (p i / q i) = 0` if and only if `p = q` on `s`. -/
theorem sum_mul_log_div_eq_zero_iff (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hpq : ∑ i ∈ s, p i = ∑ i ∈ s, q i) :
    ∑ i ∈ s, p i * log (p i / q i) = 0 ↔ ∀ i ∈ s, p i = q i := by
  rw [sum_mul_log_div_eq_sum_mul_klFun_div hq hpq, sum_eq_zero_iff_of_nonneg fun i hi ↦
    mul_nonneg (hq i hi).le (klFun_nonneg (div_nonneg (hp i hi) (hq i hi).le))]
  refine forall₂_congr fun i hi ↦ ?_
  rw [mul_eq_zero, or_iff_right (hq i hi).ne',
    klFun_eq_zero_iff (div_nonneg (hp i hi) (hq i hi).le), div_eq_one_iff_eq (hq i hi).ne']

end InformationTheory

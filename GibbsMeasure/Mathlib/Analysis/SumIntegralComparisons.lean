/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lattice sums of a radially decreasing function

Let `f : ℝ → ℝ≥0∞` be radially decreasing, `f t ≤ f s` whenever `|s| ≤ |t|`. For every period
`r > 0` and offset `y`, the sum of `f` over the shifted lattice `y + r ℤ` is at most two values at
the origin plus the mean of `f` per period:
`∑_{j ∈ ℤ} f (y + r j) ≤ 2 f 0 + (∫ f) / r` (`tsum_add_mul_intCast_le_lintegral`).

Translating `y` by a multiple of `r` reduces to `y ∈ [0, r)`. The two lattice points `y`,
`y - r` nearest the origin are bounded by `f 0`. Every other point `y + r j`, `j ≥ 1`, is the
right end of `(y + r (j - 1), y + r j] ⊆ (0, ∞)`, and every `y + r j`, `j ≤ -2`, the left end of
`[y + r j, y + r (j + 1)) ⊆ (-∞, 0)`; there `f` is at least its value at that end. These intervals
of length `r` are pairwise disjoint, so `r` times the sum of the remaining values is at most
`∫ f`. No integrability or measurability of `f` is needed.

## Searches

Mathlib `d13f23b7` has the one-sided integral test for real antitone functions with unit step
(`AntitoneOn.tsum_add_one_le_integral`, `AntitoneOn.tsum_le_integral`, in
`Mathlib.Analysis.SumIntegralComparisons`) but no two-sided bound over a shifted lattice
`y + r ℤ` (`rg "tsum.*lintegral|lintegral.*tsum" Mathlib/Analysis`: none of this shape).
-/

@[expose] public section

open Set Function
open scoped ENNReal

namespace MeasureTheory

/-- **Lattice sums of a radially decreasing function**: for `f t ≤ f s` whenever `|s| ≤ |t|`,
`∑_{j ∈ ℤ} f (y + r j) ≤ 2 f 0 + (∫ f) / r` for every `y` and every period `r > 0`. -/
theorem tsum_add_mul_intCast_le_lintegral {f : ℝ → ℝ≥0∞} (hf : ∀ s t, |s| ≤ |t| → f t ≤ f s)
    {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ∑' j : ℤ, f (y + r * j) ≤ 2 * f 0 + (∫⁻ t, f t) / ENNReal.ofReal r := by
  obtain ⟨m, hm, -⟩ := existsUnique_add_zsmul_mem_Ico hr y 0
  rw [zero_add, zsmul_eq_mul] at hm
  set s := y + m * r with hs
  obtain ⟨hs0, hsr⟩ := hm
  have hshift : ∑' j : ℤ, f (y + r * j) = ∑' j : ℤ, f (s + r * j) := by
    rw [← (Equiv.addRight m).tsum_eq]
    congr 1
    ext j
    simp only [Equiv.coe_addRight, Int.cast_add, hs]
    ring_nf
  -- the intervals to the right and to the left of the origin
  set I : ℕ → Set ℝ := fun n ↦ Ioc (s + n * r) (s + (n + 1) * r) with hI
  set J : ℕ → Set ℝ := fun n ↦ Ico (s - (n + 2) * r) (s - (n + 1) * r) with hJ
  have hIdisj : Pairwise (Disjoint on I) := by
    intro a b hab
    wlog h : a < b generalizing a b
    · exact (this hab.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)).symm
    refine Set.disjoint_left.2 fun t hta htb ↦ ?_
    have hab' : ((a : ℝ) + 1) * r ≤ b * r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast h) hr.le
    simp only [hI, mem_Ioc] at hta htb
    linarith [hta.2, htb.1]
  have hJdisj : Pairwise (Disjoint on J) := by
    intro a b hab
    wlog h : a < b generalizing a b
    · exact (this hab.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)).symm
    refine Set.disjoint_left.2 fun t hta htb ↦ ?_
    have hab' : ((a : ℝ) + 2) * r ≤ (b + 1) * r :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : a + 2 ≤ b + 1)) hr.le
    simp only [hJ, mem_Ico] at hta htb
    linarith [hta.1, htb.2]
  have hpos : ENNReal.ofReal r * ∑' n : ℕ, f (s + (n + 1) * r) ≤ ∫⁻ t in Ioi 0, f t := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' n : ℕ, ENNReal.ofReal r * f (s + (n + 1) * r)
        ≤ ∑' n : ℕ, ∫⁻ t in I n, f t := by
          refine ENNReal.tsum_le_tsum fun n ↦ ?_
          calc ENNReal.ofReal r * f (s + (n + 1) * r)
              = ∫⁻ _ in I n, f (s + (n + 1) * r) := by
                rw [setLIntegral_const, hI, Real.volume_Ioc, mul_comm]
                congr 2
                ring
            _ ≤ ∫⁻ t in I n, f t := setLIntegral_mono' measurableSet_Ioc fun t ht ↦ by
                have hn : (0 : ℝ) ≤ n * r := by positivity
                exact hf _ _ (abs_le_abs (by linarith [ht.2]) (by linarith [ht.1]))
      _ = ∫⁻ t in ⋃ n, I n, f t := (lintegral_iUnion (fun _ ↦ measurableSet_Ioc) hIdisj f).symm
      _ ≤ ∫⁻ t in Ioi 0, f t := lintegral_mono_set (iUnion_subset fun n t ht ↦ by
          have hn : (0 : ℝ) ≤ n * r := by positivity
          exact mem_Ioi.2 (by linarith [ht.1]))
  have hneg : ENNReal.ofReal r * ∑' n : ℕ, f (s - (n + 2) * r) ≤ ∫⁻ t in Iio 0, f t := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' n : ℕ, ENNReal.ofReal r * f (s - (n + 2) * r)
        ≤ ∑' n : ℕ, ∫⁻ t in J n, f t := by
          refine ENNReal.tsum_le_tsum fun n ↦ ?_
          calc ENNReal.ofReal r * f (s - (n + 2) * r)
              = ∫⁻ _ in J n, f (s - (n + 2) * r) := by
                rw [setLIntegral_const, hJ, Real.volume_Ico, mul_comm]
                congr 2
                ring
            _ ≤ ∫⁻ t in J n, f t := setLIntegral_mono' measurableSet_Ico fun t ht ↦ by
                have hn : (0 : ℝ) ≤ n * r := by positivity
                refine hf _ _ ((abs_le_abs (b := (n + 2) * r - s) (by linarith [ht.2])
                  (by linarith [ht.1])).trans_eq ?_)
                rw [abs_sub_comm]
      _ = ∫⁻ t in ⋃ n, J n, f t := (lintegral_iUnion (fun _ ↦ measurableSet_Ico) hJdisj f).symm
      _ ≤ ∫⁻ t in Iio 0, f t := lintegral_mono_set (iUnion_subset fun n t ht ↦ by
          have hn : (0 : ℝ) ≤ n * r := by positivity
          exact mem_Iio.2 (by linarith [ht.2]))
  have hsum : ∑' n : ℕ, f (s + (n + 1) * r) + ∑' n : ℕ, f (s - (n + 2) * r) ≤
      (∫⁻ t, f t) / ENNReal.ofReal r := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hr)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm, mul_add]
    calc ENNReal.ofReal r * ∑' n : ℕ, f (s + (n + 1) * r) +
          ENNReal.ofReal r * ∑' n : ℕ, f (s - (n + 2) * r)
        ≤ (∫⁻ t in Ioi 0, f t) + ∫⁻ t in Iio 0, f t := add_le_add hpos hneg
      _ = ∫⁻ t in Ioi 0 ∪ Iio 0, f t :=
          (lintegral_union measurableSet_Iio (Ioi_disjoint_Iio_same (a := (0 : ℝ)))).symm
      _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _
  rw [hshift, tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable,
    tsum_eq_zero_add' (f := fun n : ℕ ↦ f (s + r * ((-((n : ℤ) + 1) : ℤ) : ℝ))) ENNReal.summable]
  have h0 : f (s + r * (((0 : ℕ) : ℤ) : ℝ)) ≤ f 0 := hf _ _ (by simp)
  have h1 : f (s + r * ((-(((0 : ℕ) : ℤ) + 1) : ℤ) : ℝ)) ≤ f 0 :=
    hf _ _ (by simp only [abs_zero]; exact abs_nonneg _)
  have hp : ∑' n : ℕ, f (s + r * (((n + 1 : ℕ) : ℤ) : ℝ)) = ∑' n : ℕ, f (s + (n + 1) * r) := by
    congr 1; ext n; push_cast; ring_nf
  have hn : ∑' n : ℕ, f (s + r * ((-(((n + 1 : ℕ) : ℤ) + 1) : ℤ) : ℝ)) =
      ∑' n : ℕ, f (s - (n + 2) * r) := by
    congr 1; ext n; push_cast; ring_nf
  rw [hp, hn, two_mul]
  calc f (s + r * (((0 : ℕ) : ℤ) : ℝ)) + ∑' n : ℕ, f (s + (n + 1) * r) +
        (f (s + r * ((-(((0 : ℕ) : ℤ) + 1) : ℤ) : ℝ)) + ∑' n : ℕ, f (s - (n + 2) * r))
      = (f (s + r * (((0 : ℕ) : ℤ) : ℝ)) + f (s + r * ((-(((0 : ℕ) : ℤ) + 1) : ℤ) : ℝ))) +
          (∑' n : ℕ, f (s + (n + 1) * r) + ∑' n : ℕ, f (s - (n + 2) * r)) := by
        ring
    _ ≤ f 0 + f 0 + (∫⁻ t, f t) / ENNReal.ofReal r := add_le_add (add_le_add h0 h1) hsum

end MeasureTheory

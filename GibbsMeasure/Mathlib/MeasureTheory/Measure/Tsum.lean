/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Measurability of `ℝ≥0∞`-valued series, and of real-valued ones on their summability set

`measurable_ennreal_tsum` is Mathlib's `Measurable.ennreal_tsum`, restated because the Mathlib
version carries a dangling deprecation.

A real-valued `tsum` is *not* measurable in general (it is defined to be `0` off the summability
set, and that set need not be measurable for an uncountable index type), but on the set where the
family is summable it agrees with the difference of the `toReal`s of the `ℝ≥0∞`-series of its
positive and negative parts (`Summable.tsum_eq_toReal_tsum_ofReal_sub`), which *is* measurable
(`measurable_toReal_tsum_ofReal`). This is the standard way to see that a parametrized absolutely
convergent series is a measurable function of its parameter.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

theorem measurable_ennreal_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) : Measurable fun x ↦ ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s ↦ s.measurable_fun_sum fun i _ ↦ hf i

/-- **A summable real series as a difference of two `ℝ≥0∞`-series.** For a summable family of
reals, `∑' i, f i` is the difference of the `ℝ≥0∞`-sums of its positive and negative parts, read
back in `ℝ` — both sums being finite. Intended home:
`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`. -/
theorem _root_.Summable.tsum_eq_toReal_tsum_ofReal_sub {ι : Type*} {f : ι → ℝ}
    (hf : Summable f) :
    ∑' i, f i =
      (∑' i, ENNReal.ofReal (f i)).toReal - (∑' i, ENNReal.ofReal (-f i)).toReal := by
  have habs : Summable fun i ↦ |f i| := summable_abs_iff.2 hf
  have hp : Summable fun i ↦ max (f i) 0 :=
    Summable.of_nonneg_of_le (fun i ↦ le_max_right _ _)
      (fun i ↦ max_le (le_abs_self _) (abs_nonneg _)) habs
  have hn : Summable fun i ↦ max (-f i) 0 :=
    Summable.of_nonneg_of_le (fun i ↦ le_max_right _ _)
      (fun i ↦ max_le (neg_le_abs _) (abs_nonneg _)) habs
  have hofReal : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
    intro x
    rcases le_or_gt x 0 with hx | hx
    · rw [max_eq_right hx, ENNReal.ofReal_eq_zero.2 hx, ENNReal.ofReal_zero]
    · rw [max_eq_left hx.le]
  have hpos : (∑' i, ENNReal.ofReal (f i)).toReal = ∑' i, max (f i) 0 := by
    rw [show (fun i ↦ ENNReal.ofReal (f i)) = fun i ↦ ENNReal.ofReal (max (f i) 0) from
        funext fun i ↦ hofReal (f i),
      ← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ le_max_right _ _) hp,
      ENNReal.toReal_ofReal (tsum_nonneg fun i ↦ le_max_right _ _)]
  have hneg : (∑' i, ENNReal.ofReal (-f i)).toReal = ∑' i, max (-f i) 0 := by
    rw [show (fun i ↦ ENNReal.ofReal (-f i)) = fun i ↦ ENNReal.ofReal (max (-f i) 0) from
        funext fun i ↦ hofReal (-f i),
      ← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ le_max_right _ _) hn,
      ENNReal.toReal_ofReal (tsum_nonneg fun i ↦ le_max_right _ _)]
  rw [hpos, hneg, ← hp.tsum_sub hn]
  refine tsum_congr fun i ↦ ?_
  rcases le_or_gt 0 (f i) with hx | hx
  · rw [max_eq_left hx, max_eq_right (by linarith : -f i ≤ 0)]; ring
  · rw [max_eq_right hx.le, max_eq_left (by linarith : (0 : ℝ) ≤ -f i)]; ring

/-- The `toReal` of an `ℝ≥0∞`-series of `ENNReal.ofReal`s of measurable functions is measurable.
Together with `Summable.tsum_eq_toReal_tsum_ofReal_sub`, this exhibits a measurable function
agreeing with `x ↦ ∑' i, f i x` on the set where the family is summable. -/
theorem measurable_toReal_tsum_ofReal {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x ↦ (∑' i, ENNReal.ofReal (f i x)).toReal :=
  (measurable_ennreal_tsum fun i ↦ (hf i).ennreal_ofReal).ennreal_toReal

end MeasureTheory

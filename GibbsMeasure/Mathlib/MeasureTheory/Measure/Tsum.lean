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
# Measurability of `ℝ≥0∞`-valued series, and absolute summability through `ENNReal.ofReal`
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

theorem measurable_ennreal_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) : Measurable fun x ↦ ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s ↦ s.measurable_fun_sum fun i _ ↦ hf i

end MeasureTheory

theorem summable_abs_iff_tsum_ofReal_ne_top {ι : Type*} (F : ι → ℝ) (hF : ∀ j, 0 ≤ F j) :
    Summable F ↔ (∑' j, ENNReal.ofReal (F j)) ≠ ⊤ := by
  have hFg : F = fun j ↦ ((F j).toNNReal : ℝ) := funext fun j ↦ (Real.coe_toNNReal _ (hF j)).symm
  conv_lhs => rw [hFg]
  rw [NNReal.summable_coe, ← ENNReal.tsum_coe_ne_top_iff_summable]
  simp [ENNReal.ofReal]

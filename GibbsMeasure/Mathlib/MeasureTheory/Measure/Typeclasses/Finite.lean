/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Real-valued bounds from two-sided `ℝ≥0∞` bounds for finite measures
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- A pair of two-sided `ℝ≥0∞` bounds `μ (A ∩ C) ≤ μ A * μ C + D` and `μ A * μ C ≤ μ (A ∩ C) + D`
(with `D` finite) gives the real absolute-value bound `|μ.real (A ∩ C) - μ.real A * μ.real C| ≤
D.toReal`. The two-sided form is what a truncated-subtraction estimate naturally produces; this
converts it to the form used by a covariance/mixing bound. -/
theorem abs_measureReal_inter_sub_mul_le {X : Type*} {mX : MeasurableSpace X} {w : Measure X}
    [IsFiniteMeasure w] {A C : Set X} {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (h1 : w (A ∩ C) ≤ w A * w C + D) (h2 : w A * w C ≤ w (A ∩ C) + D) :
    |w.real (A ∩ C) - w.real A * w.real C| ≤ D.toReal := by
  have hmul : w.real A * w.real C = (w A * w C).toReal := (ENNReal.toReal_mul).symm
  rw [Measure.real, hmul]
  have hxtop : w (A ∩ C) ≠ ⊤ := measure_ne_top _ _
  have hytop : w A * w C ≠ ⊤ := ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  have hb1 : w (A ∩ C) - w A * w C ≤ D := tsub_le_iff_left.2 h1
  have hb2 : w A * w C - w (A ∩ C) ≤ D := tsub_le_iff_left.2 h2
  rcases le_total (w (A ∩ C)) (w A * w C) with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.2 ((ENNReal.toReal_le_toReal hxtop hytop).2 hle)),
      neg_sub, ← ENNReal.toReal_sub_of_le hle hytop]
    exact ENNReal.toReal_mono hD hb2
  · rw [abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal hytop hxtop).2 hle)),
      ← ENNReal.toReal_sub_of_le hle hxtop]
    exact ENNReal.toReal_mono hD hb1

end MeasureTheory

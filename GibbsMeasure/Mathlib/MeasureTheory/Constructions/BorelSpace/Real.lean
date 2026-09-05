/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Analysis.Normed.Group.Real

/-!
# Measurability of `ENNReal.ofReal |·|`
-/

@[expose] public section

namespace MeasureTheory

/-- Measurability of `x ↦ ENNReal.ofReal |u x|`. -/
theorem measurable_ofReal_abs {X : Type*} [MeasurableSpace X] {u : X → ℝ} (hu : Measurable u) :
    Measurable fun x ↦ ENNReal.ofReal |u x| :=
  ENNReal.measurable_ofReal.comp (by simpa only [Real.norm_eq_abs] using hu.norm)

/-- Measurability of `x ↦ ENNReal.ofReal |u x - w x|`. -/
theorem measurable_ofReal_abs_sub {X : Type*} [MeasurableSpace X] {u w : X → ℝ}
    (hu : Measurable u) (hw : Measurable w) :
    Measurable fun x ↦ ENNReal.ofReal |u x - w x| :=
  ENNReal.measurable_ofReal.comp (by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hu.sub hw).norm)

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Restriction of a measure to a sub-σ-algebra: scaling and probability measures
-/

@[expose] public section

open scoped NNReal

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

lemma Measure.trim_smul (hm : m ≤ m0) (c : ℝ≥0) : (c • μ).trim hm = c • μ.trim hm :=
  @Measure.ext _ m _ _ fun s hs ↦ by
    rw [trim_measurableSet_eq hm hs, Measure.smul_apply, Measure.smul_apply,
      trim_measurableSet_eq hm hs]

instance isProbabilityMeasure_trim (hm : m ≤ m0) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.trim hm) :=
  ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]⟩

end MeasureTheory

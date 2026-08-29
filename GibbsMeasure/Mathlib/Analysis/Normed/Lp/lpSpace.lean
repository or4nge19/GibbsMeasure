/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of bounded observables

An element of `lp _ ∞` is integrable against any finite measure.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace lp

variable {α : Type*} [MeasurableSpace α] {V : Type*} [NormedAddCommGroup V]

/-- A bounded observable is integrable against any finite measure. -/
lemma integrable_of_aestronglyMeasurable {f : lp (fun _ : α ↦ V) ∞} (μ : Measure α)
    [IsFiniteMeasure μ] (hf : AEStronglyMeasurable (⇑f) μ) : Integrable (⇑f) μ :=
  Integrable.mono' (integrable_const ‖f‖) hf
    (.of_forall fun x ↦ norm_apply_le_norm ENNReal.top_ne_zero f x)

/-- A bounded measurable observable is integrable against any finite measure. -/
lemma integrable_of_measurable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {f : lp (fun _ : α ↦ V) ∞} (hf : Measurable (⇑f)) (μ : Measure α) [IsFiniteMeasure μ] :
    Integrable (⇑f) μ :=
  integrable_of_aestronglyMeasurable μ hf.aestronglyMeasurable

end lp

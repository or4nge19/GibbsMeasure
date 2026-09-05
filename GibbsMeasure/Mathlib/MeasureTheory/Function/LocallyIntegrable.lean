/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability with respect to a measure carried by a compact set

Mathlib's `ContinuousOn.integrableOn_of_subset_isCompact` shows that a function which is continuous
on a compact set `s` is integrable *on* `s`. If moreover the measure is finite and gives no mass to
the complement of `s`, then the function is integrable on the whole space: no growth assumption
outside `s` is needed, because the measure does not see it.

## Main statements

* `ContinuousOn.integrable_of_ae_mem_isCompact`
* `Continuous.integrable_of_ae_mem_isCompact`
-/

@[expose] public section

open Filter MeasureTheory Set

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  [NormedAddCommGroup E] {f : X → E} {s : Set X} {μ : Measure X}

/-- A function continuous on a compact measurable set `s` is integrable with respect to any finite
measure which is carried by `s`, i.e. for which almost every point lies in `s`. -/
theorem ContinuousOn.integrable_of_ae_mem_isCompact [IsFiniteMeasure μ] (hf : ContinuousOn f s)
    (hs : IsCompact s) (hsm : MeasurableSet s) (hμ : ∀ᵐ x ∂μ, x ∈ s) : Integrable f μ := by
  have h := hf.integrableOn_of_subset_isCompact hs hsm Subset.rfl (measure_ne_top μ s)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

/-- A continuous function is integrable with respect to any finite measure which is carried by a
compact measurable set. -/
theorem Continuous.integrable_of_ae_mem_isCompact [IsFiniteMeasure μ] (hf : Continuous f)
    (hs : IsCompact s) (hsm : MeasurableSet s) (hμ : ∀ᵐ x ∂μ, x ∈ s) : Integrable f μ :=
  hf.continuousOn.integrable_of_ae_mem_isCompact hs hsm hμ

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.Recurrence

/-!
# Transporting a conditional measure along a measure-preserving map

`MeasureTheory.MeasurePreserving.cond_of_preimage_eq` in
`GibbsMeasure.Mathlib.Dynamics.Ergodic.Recurrence` says that conditioning on a *strictly
invariant* set preserves the invariance of a measure-preserving map.  The same computation gives
the two-set version: a measure-preserving `f` carrying `s` back to `t` carries `μ(· | t)` to
`μ(· | s)`, provided the two events have the same mass — which they do when `f` is invertible,
and in particular when `s = t`.  Its natural home is next to `cond_of_preimage_eq`.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → α} {s t : Set α}

/-- A measure-preserving map carrying `s` back to `t` carries `μ(· | t)` to `μ(· | s)`, provided
the two events have the same mass.  `MeasurePreserving.cond_of_preimage_eq` is the case
`s = t`. -/
theorem MeasurePreserving.map_cond_of_preimage_eq (hf : MeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hfs : f ⁻¹' s = t) (hst : μ t = μ s) : (μ[|t]).map f = μ[|s] := by
  have hres : (μ.restrict t).map f = μ.restrict s := by
    rw [← hfs, ← Measure.restrict_map hf.measurable hs, hf.map_eq]
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond,
    Measure.map_smul _ hf.measurable.aemeasurable, hres, hst]

end MeasureTheory

end

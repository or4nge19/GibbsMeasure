/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.ConditionalProbability

/-!
# Rescaling a conditional measure
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {s : Set Ω}

/-- Rescaling `μ[|s]` by `μ s` recovers the restriction of `μ` to `s`. -/
lemma measure_smul_cond (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) : μ s • μ[|s] = μ.restrict s := by
  rw [cond, smul_smul, ENNReal.mul_inv_cancel hs₀ hs, one_smul]

end ProbabilityTheory

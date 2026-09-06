/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measures separated by a family of events are linearly independent

A finite family of measures `ρ i` for which some family of events `A i` satisfies
`ρ i (A i) = 1` and `ρ j (A i) = 0` for `j ≠ i` is linearly independent over `ℝ≥0∞`: evaluating a
linear combination on `A i` reads off its `i`-th coefficient.  Mutually singular probability
measures are the typical example.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [Finite ι]

/-- **Measures separated by a family of events are linearly independent over `ℝ≥0∞`**: the
value of `∑ l, c l • ρ l` on `A i` is `c i`. -/
theorem linearIndependent_of_measure_eq_one_of_measure_eq_zero {ρ : ι → Measure Ω}
    {A : ι → Set Ω} (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    LinearIndependent ℝ≥0∞ ρ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iffₛ]
  intro c d hcd i
  have key : ∀ e : ι → ℝ≥0∞, (∑ l, e l • ρ l) (A i) = e i := by
    intro e
    rw [Measure.finsetSum_apply,
      Finset.sum_eq_single i (fun l _ hl ↦ ?_) fun h ↦ absurd (Finset.mem_univ i) h]
    · rw [Measure.smul_apply, hself i, smul_eq_mul, mul_one]
    · rw [Measure.smul_apply, hother i l (Ne.symm hl), smul_eq_mul, mul_zero]
  have h2 : (∑ l, c l • ρ l) (A i) = (∑ l, d l • ρ l) (A i) :=
    congrArg (fun r : Measure Ω ↦ r (A i)) hcd
  rwa [key c, key d] at h2

end MeasureTheory

end

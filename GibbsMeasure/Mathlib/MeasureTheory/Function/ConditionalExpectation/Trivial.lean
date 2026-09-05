/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The conditional expectation given a σ-algebra on which a zero-one law holds

If every set of a sub-σ-algebra `m` is `μ`-null or `μ`-co-null, then `μ[f | m]` is almost surely
the constant `∫ f dμ`. This is the form in which ergodicity (a zero-one law on the invariant
σ-algebra of an action) or tail triviality is consumed.
-/

@[expose] public section

namespace MeasureTheory

/-- If a probability measure satisfies the zero-one law on a sub-σ-algebra `m` — every `m`-set is
null or co-null — then the conditional expectation given `m` is almost surely the mean. -/
theorem condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one {Ω : Type*}
    {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀) {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]
    (htriv : ∀ A, MeasurableSet[m] A → μ A = 0 ∨ μ A = 1) (f : Ω → ℝ) :
    μ[f | m] =ᵐ[μ] fun _ ↦ ∫ x, f x ∂μ := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one hm htriv
    (f := μ[f | m]) stronglyMeasurable_condExp.measurable
  have hc' : μ[f | m] =ᵐ[μ] fun _ ↦ c := hc
  have h : ∫ x, (μ[f | m]) x ∂μ = c := by
    rw [integral_congr_ae hc', integral_const, probReal_univ, one_smul]
  rw [integral_condExp hm] at h
  exact hc'.trans (Filter.Eventually.of_forall fun _ ↦ h.symm)

end MeasureTheory

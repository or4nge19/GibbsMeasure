/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional probabilities take values in `[0, 1]`, and `p log p` is integrable

`μ[s.indicator 1 | m]` is a version of the conditional probability of `s` given `m`. It takes
values in `[0, 1]` almost surely, so `p log p` is bounded by `1` and integrable for a finite
measure: the integrand of a conditional Shannon entropy is always integrable.
-/

@[expose] public section

open Real

namespace MeasureTheory

variable {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α}

/-- `t ↦ t log t` is integrable for every finite measure along a strongly measurable function
with values in `[0, 1]`: it is bounded by `1` there. -/
lemma integrable_mul_log_of_ae_mem_Icc [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf01 : ∀ᵐ x ∂μ, f x ∈ Set.Icc 0 1) :
    Integrable (fun x ↦ f x * log (f x)) μ := by
  refine Integrable.of_bound (hf.mul (hf.aemeasurable.log.aestronglyMeasurable)) 1 ?_
  filter_upwards [hf01] with x hx
  rw [Real.norm_eq_abs]
  rcases hx.1.eq_or_lt with h | h
  · simp [← h]
  · rw [mul_comm]
    exact (abs_log_mul_self_lt _ h hx.2).le

/-- A conditional probability is nonnegative almost surely. -/
lemma condExp_indicator_one_nonneg (s : Set α) :
    0 ≤ᵐ[μ] μ[s.indicator (fun _ ↦ (1 : ℝ)) | m] :=
  condExp_nonneg (.of_forall fun x ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x)

/-- A conditional probability is at most `1` almost surely. -/
lemma condExp_indicator_one_le_one [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet[m₀] s) :
    μ[s.indicator (fun _ ↦ (1 : ℝ)) | m] ≤ᵐ[μ] fun _ ↦ (1 : ℝ) := by
  by_cases hm : m ≤ m₀
  · have h := condExp_mono (m := m) (μ := μ) (f := s.indicator fun _ ↦ (1 : ℝ))
      (g := fun _ ↦ (1 : ℝ)) ((integrable_const _).indicator hs) (integrable_const _)
      (.of_forall fun x ↦ Set.indicator_le_self' (fun _ _ ↦ zero_le_one) x)
    rwa [condExp_const hm] at h
  · rw [condExp_of_not_le hm]
    exact .of_forall fun _ ↦ zero_le_one

/-- A conditional probability lies in `[0, 1]` almost surely. -/
lemma condExp_indicator_one_mem_Icc [IsFiniteMeasure μ] {s : Set α}
    (hs : MeasurableSet[m₀] s) :
    ∀ᵐ x ∂μ, (μ[s.indicator (fun _ ↦ (1 : ℝ)) | m]) x ∈ Set.Icc 0 1 := by
  filter_upwards [condExp_indicator_one_nonneg (m := m) (μ := μ) s,
    condExp_indicator_one_le_one (m := m) (μ := μ) hs] with x h₀ h₁
  exact ⟨h₀, h₁⟩

/-- For a conditional probability `p = μ[1_s | m]`, `p log p` is integrable. -/
lemma integrable_condExp_indicator_one_mul_log [IsFiniteMeasure μ] {s : Set α}
    (hs : MeasurableSet[m₀] s) :
    Integrable (fun x ↦ (μ[s.indicator (fun _ ↦ (1 : ℝ)) | m]) x
      * log ((μ[s.indicator (fun _ ↦ (1 : ℝ)) | m]) x)) μ :=
  integrable_mul_log_of_ae_mem_Icc integrable_condExp.aestronglyMeasurable
    (condExp_indicator_one_mem_Icc hs)

end MeasureTheory

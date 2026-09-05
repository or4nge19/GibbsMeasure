/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Measure.Real
public import GibbsMeasure.Mathlib.Analysis.Normed.Group.Tannery

/-!
# Finite measures on a countable space as sums of their real point masses

For a finite measure `μ` on a countable space with measurable singletons, `μ.real s` is the sum
of the real point masses `μ.real {b}`, `b ∈ s` (`MeasureTheory.tsum_indicator_apply_singleton`
transported along `ENNReal.toReal`). Consequently the difference of two such measures on any set
is bounded by their `ℓ¹` distance on singletons, and Scheffé's lemma for series gives: finite
measures converging on every singleton and in total mass converge in total variation.

Intended home: `Mathlib/MeasureTheory/Measure/Dirac.lean`, next to
`MeasureTheory.Measure.tsum_indicator_apply_singleton`.
-/

@[expose] public section

open Filter Set
open scoped Topology ENNReal

variable {α β : Type*} {l : Filter α}

/-- A finite measure on a countable space with measurable singletons is the sum of its point
masses: `HasSum (fun b ↦ μ.real {b}) (μ.real univ)`. -/
lemma MeasureTheory.hasSum_measureReal_singleton [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ] :
    HasSum (fun b ↦ μ.real {b}) (μ.real univ) := by
  have h := μ.tsum_indicator_apply_singleton univ MeasurableSet.univ
  simp only [indicator_univ] at h
  have hne : ∑' b, μ {b} ≠ ∞ := by rw [h]; exact MeasureTheory.measure_ne_top μ _
  have := (ENNReal.summable_toReal hne).hasSum
  rwa [← ENNReal.tsum_toReal_eq (fun b ↦ MeasureTheory.measure_ne_top μ _), h] at this

/-- The real mass of any set of a finite measure on a countable space with measurable singletons
is the sum of the point masses it contains. -/
lemma MeasureTheory.measureReal_eq_tsum_indicator [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ]
    (s : Set β) : μ.real s = ∑' b, s.indicator (fun b ↦ μ.real {b}) b := by
  have h := μ.tsum_indicator_apply_singleton s s.to_countable.measurableSet
  have hne : ∀ b, s.indicator (fun b ↦ μ {b}) b ≠ ∞ := fun b ↦
    ne_top_of_le_ne_top (MeasureTheory.measure_ne_top μ {b}) (indicator_le_self _ _ b)
  rw [MeasureTheory.measureReal_def, ← h, ENNReal.tsum_toReal_eq hne]
  refine tsum_congr fun b ↦ ?_
  simp only [MeasureTheory.measureReal_def]
  by_cases hb : b ∈ s
  · rw [indicator_of_mem hb, indicator_of_mem hb]
  · rw [indicator_of_notMem hb, indicator_of_notMem hb, ENNReal.toReal_zero]

/-- The difference of two finite measures on any set is bounded by their `ℓ¹` distance on
singletons. -/
lemma MeasureTheory.abs_measureReal_sub_le_tsum_abs [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ ν : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ]
    [MeasureTheory.IsFiniteMeasure ν] (s : Set β) :
    |μ.real s - ν.real s| ≤ ∑' b, |μ.real {b} - ν.real {b}| := by
  have hμ := (MeasureTheory.hasSum_measureReal_singleton μ).summable
  have hν := (MeasureTheory.hasSum_measureReal_singleton ν).summable
  have hd : Summable fun b ↦
      s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b :=
    (hμ.indicator s).sub (hν.indicator s)
  rw [MeasureTheory.measureReal_eq_tsum_indicator μ, MeasureTheory.measureReal_eq_tsum_indicator ν,
    ← (hμ.indicator s).tsum_sub (hν.indicator s)]
  calc |∑' b, (s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b)|
      ≤ ∑' b, |s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b| := by
        have := norm_tsum_le_tsum_norm (f := fun b ↦
          s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b)
          (by simpa only [Real.norm_eq_abs] using hd.abs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' b, |μ.real {b} - ν.real {b}| :=
        hd.abs.tsum_le_tsum (fun b ↦ by by_cases hb : b ∈ s <;> simp [hb]) (hμ.sub hν).abs

/-- **Scheffé's lemma for finite measures on a countable space.** If finite measures `μ a`
converge to a finite measure `ν` on every singleton and in total mass, then they converge in total
variation: `∑' b, |(μ a).real {b} - ν.real {b}| → 0`. For probability measures the total-mass
hypothesis is automatic; see `tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto'`. -/
theorem MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {μ : α → MeasureTheory.Measure β}
    {ν : MeasureTheory.Measure β} [∀ a, MeasureTheory.IsFiniteMeasure (μ a)]
    [MeasureTheory.IsFiniteMeasure ν]
    (h : ∀ b, Tendsto (fun a ↦ (μ a).real {b}) l (𝓝 (ν.real {b})))
    (huniv : Tendsto (fun a ↦ (μ a).real univ) l (𝓝 (ν.real univ))) :
    Tendsto (fun a ↦ ∑' b, |(μ a).real {b} - ν.real {b}|) l (𝓝 0) := by
  refine tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum (Eventually.of_forall fun a b ↦
    MeasureTheory.measureReal_nonneg) (fun b ↦ MeasureTheory.measureReal_nonneg)
    (Eventually.of_forall fun a ↦ (MeasureTheory.hasSum_measureReal_singleton (μ a)).summable)
    (MeasureTheory.hasSum_measureReal_singleton ν).summable h ?_
  simp_rw [(MeasureTheory.hasSum_measureReal_singleton _).tsum_eq]
  exact huniv

/-- **Scheffé's lemma for probability measures on a countable space.** Probability measures
converging on every singleton converge in total variation. -/
theorem MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto' [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {μ : α → MeasureTheory.Measure β}
    {ν : MeasureTheory.Measure β} [∀ a, MeasureTheory.IsProbabilityMeasure (μ a)]
    [MeasureTheory.IsProbabilityMeasure ν]
    (h : ∀ b, Tendsto (fun a ↦ (μ a).real {b}) l (𝓝 (ν.real {b}))) :
    Tendsto (fun a ↦ ∑' b, |(μ a).real {b} - ν.real {b}|) l (𝓝 0) :=
  MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto h
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 : ℝ)) l (𝓝 1)))

end

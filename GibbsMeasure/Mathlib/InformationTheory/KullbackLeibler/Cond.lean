/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# The Kullback–Leibler divergence of a conditional measure

Conditioning a probability measure on an event costs exactly `−log` of the probability of that
event: `𝓗(μ(· | s) | μ) = −log μ(s)`. Equivalently, `μ(· | s)` is the minimiser of
`ρ ↦ 𝓗(ρ | μ)` over the probability measures carried by `s`, and the minimum is `−log μ(s)`.

## Main statements

* `InformationTheory.klDiv_cond_self`: `𝓗(μ[|s] | μ) = −log μ(s)`.
* `InformationTheory.klDiv_trim_cond_self`: the same on a sub-σ-algebra `m` for which `s` is
  measurable, `𝓗_m(μ[|s] | μ) = −log μ(s)`: conditioning on an `m`-measurable event uses no
  information outside `m`. The ingredient is `MeasureTheory.Measure.trim_cond`, that conditioning
  commutes with trimming at an `m`-measurable event.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} {m mα : MeasurableSpace α}

/-- Conditioning commutes with trimming to a sub-σ-algebra for which the conditioning event is
measurable. -/
lemma trim_cond (hm : m ≤ mα) (μ : Measure α) {s : Set α} (hs : MeasurableSet[m] s) :
    (μ[|s]).trim hm = (μ.trim hm)[|s] := by
  have hs0 : MeasurableSet s := hm _ hs
  refine @Measure.ext _ m _ _ fun t ht ↦ ?_
  rw [trim_measurableSet_eq hm ht, cond_apply hs0, cond_apply hs,
    trim_measurableSet_eq hm hs, trim_measurableSet_eq hm (hs.inter ht)]

end MeasureTheory.Measure

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- **The relative entropy of a conditional measure**: conditioning on an event `s` of positive
probability costs `−log μ(s)`, i.e. `𝓗(μ(· | s) | μ) = −log μ(s)`. -/
theorem klDiv_cond_self [IsProbabilityMeasure μ] (hs : MeasurableSet s) (hμs : μ s ≠ 0) :
    klDiv (μ[|s]) μ = ENNReal.ofReal (-Real.log (μ.real s)) := by
  have hprob : IsProbabilityMeasure (μ[|s]) := cond_isProbabilityMeasure hμs
  have hac : μ[|s] ≪ μ := cond_absolutelyContinuous
  set g : α → ℝ≥0∞ := (μ s)⁻¹ • Set.indicator s (1 : α → ℝ≥0∞) with hg
  have hind : Measurable (Set.indicator s (1 : α → ℝ≥0∞)) := measurable_one.indicator hs
  have hgm : Measurable g := by rw [hg]; exact hind.const_smul _
  have hdens : μ[|s] = μ.withDensity g := by
    rw [hg, withDensity_smul _ hind, withDensity_indicator_one hs]
    rfl
  have hrn : (μ[|s]).rnDeriv μ =ᵐ[μ] g := by
    rw [hdens]; exact Measure.rnDeriv_withDensity μ hgm
  have hsreal : (0 : ℝ) < μ.real s := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hμs (measure_ne_top μ s)
  -- the log-likelihood ratio is `-log μ(s)` almost everywhere under the conditional measure
  have hllr : llr (μ[|s]) μ =ᵐ[μ[|s]] fun _ ↦ -Real.log (μ.real s) := by
    have h0 : μ[|s] sᶜ = 0 := by
      rw [cond_apply hs, Set.inter_compl_self, measure_empty, mul_zero]
    have hs1 : ∀ᵐ x ∂(μ[|s]), x ∈ s := by rw [ae_iff]; exact h0
    filter_upwards [hac.ae_le hrn, hs1] with x hx hxs
    simp only [llr_def, hx, hg, Pi.smul_apply, Set.indicator_of_mem hxs, Pi.one_apply,
      smul_eq_mul, mul_one, ENNReal.toReal_inv]
    rw [Real.log_inv, ← measureReal_def]
  have hint : Integrable (llr (μ[|s]) μ) (μ[|s]) :=
    (integrable_const (-Real.log (μ.real s))).congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr]
  simp

/-- **The relative entropy of a conditional measure on a sub-σ-algebra.** If the conditioning
event `s` is measurable for the sub-σ-algebra `m`, then the relative entropy of `μ(· | s)` with
respect to `μ` computed on `m` is again `−log μ(s)`: conditioning on an `m`-measurable event uses
no information outside `m`. -/
theorem klDiv_trim_cond_self {m mα : MeasurableSpace α} (hm : m ≤ mα) {μ : Measure α}
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet[m] s) (hμs : μ s ≠ 0) :
    klDiv ((μ[|s]).trim hm) (μ.trim hm) = ENNReal.ofReal (-Real.log (μ.real s)) := by
  have hprob : IsProbabilityMeasure (μ.trim hm) :=
    ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ]; exact measure_univ⟩
  have hts : (μ.trim hm) s = μ s := trim_measurableSet_eq hm hs
  rw [Measure.trim_cond hm μ hs,
    klDiv_cond_self (μ := μ.trim hm) hs (by rw [hts]; exact hμs), measureReal_def, hts,
    measureReal_def]

end InformationTheory

end

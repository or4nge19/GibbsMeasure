/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Kullback–Leibler divergence of a measure with a bounded density

For a probability measure `ν` and a measurable density `g` bounded away from `0` and `∞` with
`ν(g) = 1`, the tilted law `g·ν` is a probability measure and

`𝓗(g·ν | ν) = ∫ g log g dν`.

Intended home: `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Real
open scoped ENNReal NNReal

namespace InformationTheory

variable {X : Type*} {mX : MeasurableSpace X} {ν : Measure X} [IsProbabilityMeasure ν]
  {g : X → ℝ} {c C : ℝ}

/-- A bounded nonnegative density of total mass one gives a probability measure. -/
theorem isProbabilityMeasure_withDensity_ofReal (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgC : ∀ x, g x ≤ C) (hint : ∫ x, g x ∂ν = 1) :
    IsProbabilityMeasure (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
  have hgint : Integrable g ν :=
    (integrable_const C).mono' hg.aestronglyMeasurable (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hgC x)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hgint (.of_forall hg0), hint, ENNReal.ofReal_one]

/-- **The Kullback–Leibler divergence of a tilted law with a bounded density.**
If `c ≤ g ≤ C` with `c > 0` and `ν(g) = 1`, then `𝓗(g·ν | ν) = ∫ g log g dν`. -/
theorem klDiv_withDensity_ofReal (hg : Measurable g) (hc : 0 < c) (hgc : ∀ x, c ≤ g x)
    (hgC : ∀ x, g x ≤ C) (hint : ∫ x, g x ∂ν = 1) :
    klDiv (ν.withDensity fun x ↦ ENNReal.ofReal (g x)) ν
      = ENNReal.ofReal (∫ x, g x * Real.log (g x) ∂ν) := by
  set α : Measure X := ν.withDensity fun x ↦ ENNReal.ofReal (g x) with hα
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ hc.le.trans (hgc x)
  have hprob : IsProbabilityMeasure α :=
    isProbabilityMeasure_withDensity_ofReal hg hg0 hgC hint
  have hac : α ≪ ν := withDensity_absolutelyContinuous _ _
  -- the log-likelihood ratio is `log g`
  have hrn : α.rnDeriv ν =ᵐ[ν] fun x ↦ ENNReal.ofReal (g x) :=
    Measure.rnDeriv_withDensity ν (hg.ennreal_ofReal)
  have hllr : llr α ν =ᵐ[ν] fun x ↦ Real.log (g x) := by
    filter_upwards [hrn] with x hx
    rw [llr, hx, ENNReal.toReal_ofReal (hg0 x)]
  have hllr' : llr α ν =ᵐ[α] fun x ↦ Real.log (g x) := hac.ae_le hllr
  -- `log g` is bounded, hence integrable for the probability measure `α`
  have hbound : ∀ x, |Real.log (g x)| ≤ |Real.log c| + |Real.log C| := by
    intro x
    have hCpos : 0 < C := lt_of_lt_of_le hc ((hgc x).trans (hgC x))
    have h1 : Real.log c ≤ Real.log (g x) := Real.log_le_log hc (hgc x)
    have h2 : Real.log (g x) ≤ Real.log C := Real.log_le_log (hc.trans_le (hgc x)) (hgC x)
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log c); linarith [abs_nonneg (Real.log C)]
    · have := le_abs_self (Real.log C); linarith [abs_nonneg (Real.log c)]
  have hlogmeas : Measurable fun x ↦ Real.log (g x) := Real.measurable_log.comp hg
  have hintlog : Integrable (llr α ν) α := by
    refine (integrable_congr hllr').2 ?_
    exact (integrable_const (|Real.log c| + |Real.log C|)).mono'
      hlogmeas.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hbound x)
  -- the change of measure
  have hchange : ∫ x, Real.log (g x) ∂α = ∫ x, g x * Real.log (g x) ∂ν := by
    rw [hα, integral_withDensity_eq_integral_toReal_smul hg.ennreal_ofReal
      (.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
    exact integral_congr_ae (.of_forall fun x ↦ by
      simp only [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul])
  rw [klDiv_of_ac_of_integrable hac hintlog, integral_congr_ae hllr', hchange]
  simp

end InformationTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Existence
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.CondExp

/-!
# Translates of Gaussian fields

A Gaussian field on `ι → ℝ` translated by a fixed configuration `c` is again a Gaussian field,
with mean shifted by `c` and the same covariance function; and conversely every Gaussian field
with covariance `C` and mean `m` is the translate by `m` of `ProbabilityTheory.gaussianField C`.

This is the "`μ = μ_C * δ_m`" step in the proof of Georgii's Theorem (13.24).

## Main results

* `ProbabilityTheory.isGaussianProcess_map_add_const`,
  `ProbabilityTheory.integral_eval_map_add_const`,
  `ProbabilityTheory.covariance_eval_map_add_const`.
* `ProbabilityTheory.eq_map_add_gaussianField`: a Gaussian field with covariance `C` and mean `m`
  is `(gaussianField C hC).map (· + m)`, i.e. the convolution `μ_C * δ_m`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

namespace ProbabilityTheory

variable {ι : Type*} {μ : Measure (ι → ℝ)}

/-- A translate of a Gaussian field is a Gaussian field. -/
theorem isGaussianProcess_map_add_const
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ) (c : ι → ℝ) :
    IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) (μ.map fun x ↦ x + c) := by
  refine ⟨fun I ↦ ⟨(Finset.measurable_restrict I).aemeasurable, ?_⟩⟩
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact ((hμ.hasGaussianLaw I).add_const (I.restrict c)).isGaussian_map

/-- The mean of a translated Gaussian field. -/
theorem integral_eval_map_add_const [IsProbabilityMeasure μ]
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ) (c : ι → ℝ) (i : ι) :
    ∫ ω, ω i ∂(μ.map fun x ↦ x + c) = (∫ ω, ω i ∂μ) + c i := by
  have hint : Integrable (fun ω : ι → ℝ ↦ ω i) μ := (hμ.hasGaussianLaw_eval i).integrable
  rw [integral_map (measurable_add_const c).aemeasurable
    (measurable_pi_apply i).aestronglyMeasurable]
  simp only [Pi.add_apply]
  rw [integral_add hint (integrable_const _), integral_const]
  simp

/-- The covariance function of a translated Gaussian field. -/
theorem covariance_eval_map_add_const [IsProbabilityMeasure μ]
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ) (c : ι → ℝ) (i j : ι) :
    cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ.map fun x ↦ x + c]
      = cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] := by
  rw [covariance, covariance, integral_eval_map_add_const hμ c i,
    integral_eval_map_add_const hμ c j,
    integral_map (measurable_add_const c).aemeasurable (by fun_prop)]
  congr 1 with ω
  simp only [Pi.add_apply]
  ring_nf

/-- **Georgii's `μ = μ_C * δ_m`.** A Gaussian field on `ι → ℝ` with covariance function `C` and
mean `m` is the translate by `m` of the centred Gaussian field with covariance `C`. -/
theorem eq_map_add_gaussianField [DecidableEq ι] [IsProbabilityMeasure μ] {C : ι → ι → ℝ}
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef)
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ)
    (hcov : ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = C i j)
    {m : ι → ℝ} (hm : ∀ i, ∫ ω, ω i ∂μ = m i) :
    μ = (gaussianField C hC).map fun x ↦ x + m := by
  have hprob : IsProbabilityMeasure (μ.map fun x ↦ x + (-m)) :=
    inferInstance
  have hν : μ.map (fun x ↦ x + (-m)) = gaussianField C hC := by
    refine eq_gaussianField hC (isGaussianProcess_map_add_const hμ (-m)) (fun i ↦ ?_)
      (fun i j ↦ ?_)
    · rw [integral_eval_map_add_const hμ (-m) i, hm i]
      simp
    · rw [covariance_eval_map_add_const hμ (-m) i j]
      exact hcov i j
  rw [← hν, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun x : ι → ℝ ↦ x + m) ∘ fun x : ι → ℝ ↦ x + (-m)) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

end ProbabilityTheory

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Topology.LocalConvergenceIntegral
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.WeakLimit

/-!
# Georgii Proposition (13.A5): a local limit of Gaussian fields is Gaussian

Georgii's Proposition (13.A5) says that a limit in distribution of `ℝⁿ`-valued Gaussian random
vectors is Gaussian, with the limiting mean and covariance. The general statement lives in
`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/WeakLimit.lean`. Here it is transported
to random fields on a configuration space `Ω = S → ℝ` and to Georgii's topology of local
convergence (4.2), in the form in which Theorem (13.24) uses it: if `μ_n → μ` locally and every
`μ_n` is a Gauss field (Definition (13.1)), then `μ` is a Gauss field, its mean is the limit of
the means and its covariance function is the limit of the covariance functions.

Local convergence is *stronger* than convergence in distribution — it is setwise convergence on
the local events — so no topological assumption on the state space is used; the bridge is
`MeasureTheory.tendsto_integral_of_tendsto_withLocalConvergence`.

## Main results

* `MeasureTheory.GibbsMeasure.tendstoFddCharFun_of_tendsto_withLocalConvergence`: local
  convergence implies convergence of all finite-dimensional characteristic functions.
* `MeasureTheory.GibbsMeasure.isGaussianProcess_of_tendsto_withLocalConvergence`: **Georgii
  (13.A5)** — a local limit of Gauss fields is a Gauss field.
* `MeasureTheory.GibbsMeasure.tendsto_integral_eval_of_tendsto_withLocalConvergence` and
  `MeasureTheory.GibbsMeasure.tendsto_covariance_of_tendsto_withLocalConvergence`: the means
  `μ_n(σ_i)` and the covariances `cov_{μ_n}(σ_i, σ_j)` converge to those of `μ`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} {μs : ℕ → WithLocalConvergence S ℝ} {μ : WithLocalConvergence S ℝ}

/-- Local convergence implies the convergence of all finite-dimensional characteristic functions
of the coordinate process. -/
theorem tendstoFddCharFun_of_tendsto_withLocalConvergence (h : Tendsto μs atTop (𝓝 μ)) :
    ProbabilityTheory.TendstoFddCharFun (fun (i : S) (ω : S → ℝ) ↦ ω i)
      (fun n ↦ ((μs n).toMeasure : Measure (S → ℝ))) (μ.toMeasure : Measure (S → ℝ)) := by
  intro A L r
  have hrestrict : Measurable[cylinderEvents (X := fun _ : S ↦ ℝ) (A : Set S)]
      fun ω : S → ℝ ↦ A.restrict ω := by
    rw [measurable_iff_comap_le, cylinderEvents_eq_comap_finsetRestrict]
  have hfm : Measurable[cylinderEvents (X := fun _ : S ↦ ℝ) (A : Set S)]
      fun ω : S → ℝ ↦ Complex.exp ((r * L (A.restrict fun i ↦ ω i) : ℝ) * Complex.I) := by
    refine Complex.measurable_exp.comp (Measurable.mul_const ?_ _)
    exact Complex.measurable_ofReal.comp
      ((L.continuous.measurable.comp hrestrict).const_mul r)
  have hC : ∀ ω : S → ℝ,
      ‖Complex.exp ((r * L (A.restrict fun i ↦ ω i) : ℝ) * Complex.I)‖ ≤ 1 := fun ω ↦
    le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  exact tendsto_integral_of_tendsto_withLocalConvergence h A hfm hC

/-- **Georgii, Proposition (13.A5)** for random fields: a limit, in the topology of local
convergence, of Gauss fields is a Gauss field. -/
theorem isGaussianProcess_of_tendsto_withLocalConvergence (h : Tendsto μs atTop (𝓝 μ))
    (hg : ∀ n, IsGaussianProcess (fun (i : S) (ω : S → ℝ) ↦ ω i)
      ((μs n).toMeasure : Measure (S → ℝ))) :
    IsGaussianProcess (fun (i : S) (ω : S → ℝ) ↦ ω i) (μ.toMeasure : Measure (S → ℝ)) :=
  (tendstoFddCharFun_of_tendsto_withLocalConvergence h).isGaussianProcess
    (fun i ↦ measurable_pi_apply i) hg

/-- **Georgii, Proposition (13.A5)**: the means converge. -/
theorem tendsto_integral_eval_of_tendsto_withLocalConvergence (h : Tendsto μs atTop (𝓝 μ))
    (hg : ∀ n, IsGaussianProcess (fun (i : S) (ω : S → ℝ) ↦ ω i)
      ((μs n).toMeasure : Measure (S → ℝ))) (i : S) :
    Tendsto (fun n ↦ ((μs n).toMeasure : Measure (S → ℝ))[fun ω : S → ℝ ↦ ω i]) atTop
      (𝓝 ((μ.toMeasure : Measure (S → ℝ))[fun ω : S → ℝ ↦ ω i])) :=
  (tendstoFddCharFun_of_tendsto_withLocalConvergence h).tendsto_integral_eval
    (fun i ↦ measurable_pi_apply i) hg i

/-- **Georgii, Proposition (13.A5)**: the covariance functions converge. -/
theorem tendsto_covariance_of_tendsto_withLocalConvergence (h : Tendsto μs atTop (𝓝 μ))
    (hg : ∀ n, IsGaussianProcess (fun (i : S) (ω : S → ℝ) ↦ ω i)
      ((μs n).toMeasure : Measure (S → ℝ))) (i j : S) :
    Tendsto (fun n ↦ cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j;
        ((μs n).toMeasure : Measure (S → ℝ))]) atTop
      (𝓝 (cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j;
        (μ.toMeasure : Measure (S → ℝ))])) :=
  (tendstoFddCharFun_of_tendsto_withLocalConvergence h).tendsto_covariance
    (fun i ↦ measurable_pi_apply i) hg i j

end MeasureTheory.GibbsMeasure

end

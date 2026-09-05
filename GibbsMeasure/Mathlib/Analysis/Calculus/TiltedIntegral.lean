/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Differentiating an expectation along an exponential tilt

For a probability measure `μ` and bounded measurable `u v g`, the expectation of `g` under the
exponentially tilted measure `μ.tilted (u + t v)` is differentiable in `t`, with derivative the
covariance of `g` and `v` under the tilted measure:

`∂/∂t ∫ g d(μ.tilted (u + t v)) = ∫ g v dν_t − (∫ g dν_t) (∫ v dν_t)`, `ν_t = μ.tilted (u + t v)`.

This is the elementary fact behind the differentiation of finite-volume Gibbs expectations in the
potential (Georgii, proof of Corollary (8.37)): differentiate numerator and denominator of
`∫ g e^{u + tv} dμ / ∫ e^{u + tv} dμ` under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) and apply the quotient rule.

Intended home: `Mathlib/Probability/Moments/Tilted.lean`.
-/

@[expose] public section

open Filter Real
open scoped Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The expectation under an exponential tilt as a quotient of two integrals against the base
measure. -/
lemma integral_tilted_eq_div (f g : α → ℝ) :
    ∫ x, g x ∂(μ.tilted f) = (∫ x, g x * exp (f x) ∂μ) / ∫ x, exp (f x) ∂μ := by
  rw [integral_tilted, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul]
  ring

section Line

variable [IsProbabilityMeasure μ] {u v g : α → ℝ} {Cu Cv Cg : ℝ}

/-- A bounded measurable function is integrable against a probability measure. -/
lemma integrable_of_forall_abs_le {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := C)
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)⟩

omit [MeasurableSpace α] [IsProbabilityMeasure μ] in
/-- The line `t ↦ u x + t v x` is bounded on a ball around `t`. -/
lemma abs_add_mul_le_of_mem_ball (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv) (t : ℝ)
    {s : ℝ} (hs : s ∈ Metric.ball t 1) (x : α) :
    |u x + s * v x| ≤ Cu + (|t| + 1) * Cv := by
  have hs' : |s| ≤ |t| + 1 := by
    have := Metric.mem_ball.1 hs
    rw [Real.dist_eq] at this
    calc |s| = |t + (s - t)| := by ring_nf
      _ ≤ |t| + |s - t| := abs_add_le _ _
      _ ≤ |t| + 1 := by linarith
  have hv0 : 0 ≤ Cv := le_trans (abs_nonneg _) (hvb x)
  calc |u x + s * v x| ≤ |u x| + |s * v x| := abs_add_le _ _
    _ = |u x| + |s| * |v x| := by rw [abs_mul]
    _ ≤ Cu + (|t| + 1) * Cv :=
        add_le_add (hub x) (mul_le_mul hs' (hvb x) (abs_nonneg _) (by positivity))

/-- Differentiating `t ↦ ∫ g e^{u + t v} dμ` under the integral sign. -/
lemma hasDerivAt_integral_mul_exp_add_mul (hu : Measurable u) (hv : Measurable v)
    (hg : Measurable g) (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv) (hgb : ∀ x, |g x| ≤ Cg)
    (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, g x * exp (u x + t * v x) ∂μ)
      (∫ x, g x * v x * exp (u x + t * v x) ∂μ) t := by
  set B : ℝ := Cu + (|t| + 1) * Cv with hB
  have hFm : ∀ s : ℝ, Measurable fun x ↦ g x * exp (u x + s * v x) := fun s ↦
    hg.mul ((hu.add (measurable_const.mul hv)).exp)
  have hF'm : Measurable fun x ↦ g x * v x * exp (u x + t * v x) :=
    (hg.mul hv).mul ((hu.add (measurable_const.mul hv)).exp)
  have hbound : ∀ x, ∀ s ∈ Metric.ball t 1,
      ‖g x * v x * exp (u x + s * v x)‖ ≤ Cg * Cv * exp B := by
    intro x s hs
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_exp]
    have hv0 : 0 ≤ Cv := le_trans (abs_nonneg _) (hvb x)
    have hg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb x)
    refine mul_le_mul (mul_le_mul (hgb x) (hvb x) (abs_nonneg _) hg0)
      (Real.exp_le_exp.2 ((le_abs_self _).trans (abs_add_mul_le_of_mem_ball hub hvb t hs x)))
      (Real.exp_pos _).le (by positivity)
  have hint : Integrable (fun x ↦ g x * exp (u x + t * v x)) μ :=
    integrable_of_forall_abs_le (hFm t) (C := Cg * exp B) fun x ↦ by
      rw [abs_mul, abs_exp]
      have hg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgb x)
      exact mul_le_mul (hgb x) (Real.exp_le_exp.2 ((le_abs_self _).trans
        (abs_add_mul_le_of_mem_ball hub hvb t (Metric.mem_ball_self (by norm_num)) x)))
        (Real.exp_pos _).le hg0
  have hdiff : ∀ x, ∀ s ∈ Metric.ball t 1,
      HasDerivAt (fun s ↦ g x * exp (u x + s * v x)) (g x * v x * exp (u x + s * v x)) s := by
    intro x s _
    have h1 : HasDerivAt (fun s ↦ u x + s * v x) (v x) s := by
      simpa using ((hasDerivAt_id s).mul_const (v x)).const_add (u x)
    exact (h1.exp.const_mul (g x)).congr_deriv (by ring)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s ↦ (hFm s).aestronglyMeasurable) hint hF'm.aestronglyMeasurable
    (Eventually.of_forall hbound) (integrable_const _) (Eventually.of_forall hdiff)).2

/-- The partition function of a bounded tilt is positive. -/
lemma integral_exp_pos_of_forall_abs_le {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : 0 < ∫ x, exp (f x) ∂μ := by
  have hint : Integrable (fun x ↦ exp (f x)) μ :=
    integrable_of_forall_abs_le hf.exp (C := exp C) fun x ↦ by
      rw [abs_exp]; exact Real.exp_le_exp.2 ((le_abs_self _).trans (hC x))
  have hlow : ∀ x, exp (-C) ≤ exp (f x) := fun x ↦
    Real.exp_le_exp.2 (by linarith [(abs_le.1 (hC x)).1])
  calc (0 : ℝ) < exp (-C) := Real.exp_pos _
    _ = ∫ _x, exp (-C) ∂μ := by simp
    _ ≤ ∫ x, exp (f x) ∂μ := integral_mono (integrable_const _) hint hlow

/-- **Differentiating an expectation along an exponential tilt.** For a probability measure `μ`
and bounded measurable `u v g`, with `ν_t = μ.tilted (u + t v)`,
`∂/∂t ν_t(g) = ν_t(g v) − ν_t(g) ν_t(v)`. -/
theorem hasDerivAt_integral_tilted_add_mul (hu : Measurable u) (hv : Measurable v)
    (hg : Measurable g) (hub : ∀ x, |u x| ≤ Cu) (hvb : ∀ x, |v x| ≤ Cv) (hgb : ∀ x, |g x| ≤ Cg)
    (t : ℝ) :
    HasDerivAt (fun t ↦ ∫ x, g x ∂(μ.tilted fun x ↦ u x + t * v x))
      ((∫ x, g x * v x ∂(μ.tilted fun x ↦ u x + t * v x))
        - (∫ x, g x ∂(μ.tilted fun x ↦ u x + t * v x))
          * ∫ x, v x ∂(μ.tilted fun x ↦ u x + t * v x)) t := by
  have hfun : (fun t ↦ ∫ x, g x ∂(μ.tilted fun x ↦ u x + t * v x))
      = fun t ↦ (∫ x, g x * exp (u x + t * v x) ∂μ) / ∫ x, exp (u x + t * v x) ∂μ := by
    funext t; exact integral_tilted_eq_div _ _
  have hN : HasDerivAt (fun t ↦ ∫ x, g x * exp (u x + t * v x) ∂μ)
      (∫ x, g x * v x * exp (u x + t * v x) ∂μ) t :=
    hasDerivAt_integral_mul_exp_add_mul (μ := μ) hu hv hg hub hvb hgb t
  have hZ : HasDerivAt (fun t ↦ ∫ x, exp (u x + t * v x) ∂μ)
      (∫ x, v x * exp (u x + t * v x) ∂μ) t := by
    have h := hasDerivAt_integral_mul_exp_add_mul (μ := μ) (g := fun _ ↦ (1 : ℝ)) (Cg := 1) hu hv
      measurable_const hub hvb (fun _ ↦ by simp) t
    simpa only [one_mul] using h
  have hZpos : 0 < ∫ x, exp (u x + t * v x) ∂μ :=
    integral_exp_pos_of_forall_abs_le (hu.add (measurable_const.mul hv))
      (C := Cu + (|t| + 1) * Cv) fun x ↦
        abs_add_mul_le_of_mem_ball hub hvb t (Metric.mem_ball_self (by norm_num)) x
  rw [hfun]
  refine (hN.div hZ hZpos.ne').congr_deriv ?_
  have key : ∀ N N' Z Z' : ℝ, Z ≠ 0 → (N' * Z - N * Z') / Z ^ 2 = N' / Z - N / Z * (Z' / Z) := by
    intro N N' Z Z' hZ
    field_simp
  rw [integral_tilted_eq_div, integral_tilted_eq_div, integral_tilted_eq_div]
  exact key _ _ _ _ hZpos.ne'

end Line

end MeasureTheory

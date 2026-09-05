/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Orthogonality of the circle characters, in the angle parametrisation

The characters of the circle group are `z ↦ z ^ m` for `m : ℤ`; in the angle parametrisation
`z = e^{iθ}` they become `θ ↦ e^{imθ}`, and the Haar probability measure of the circle becomes
the normalised Lebesgue measure `dθ / (2π)` on one period of the angle.

This file introduces that measure as a probability measure `MeasureTheory.angleProbability` on
`ℝ` carried by `Ioc 0 (2π)`, and proves the orthogonality relations
`∫ e^{imθ} dθ/(2π) = δ_{m,0}` in one variable and on a finite-dimensional torus.

## Main results

* `MeasureTheory.angleProbability`: the measure `(2π)⁻¹ · Leb|_{Ioc 0 (2π)}` on `ℝ`, together
  with its `IsProbabilityMeasure` instance.
* `Complex.norm_exp_int_mul_ofReal_mul_I`: `‖e^{imθ}‖ = 1` for `m : ℤ` and `θ : ℝ`.
* `MeasureTheory.integrable_exp_int_mul_I`: `θ ↦ e^{imθ}` is `angleProbability`-integrable.
* `MeasureTheory.integral_exp_int_mul_I`: **orthogonality of the circle characters**,
  `∫ e^{imθ} ∂angleProbability = if m = 0 then 1 else 0`.
* `MeasureTheory.integral_cos_mul_exp_int_mul_I`: the same integral against the weight
  `2 cos θ = e^{iθ} + e^{-iθ}`, which is `1` exactly for `m = ±1`.
* `MeasureTheory.integral_exp_sum_int_mul_I`: **orthogonality of the characters of a
  finite-dimensional torus**, `∫ e^{i ∑_{c ∈ s} m_c θ_c} ∂(⨂ angleProbability)` is `1` if
  `m` vanishes on `s` and `0` otherwise.

## Implementation notes

The measure is defined on `ℝ`, not on `Circle` or `AddCircle (2 * π)`, because the intended
consumers integrate functions of a *real* angle variable and take finite products over a site
set.  It is the pullback of the Haar probability measure of `AddCircle (2 * π)`: by
`AddCircle.measurePreserving_mk (2 * π) 0` the quotient map pushes `volume.restrict
(Ioc 0 (2 * π))` forward to `volume` on `AddCircle (2 * π)`, whose total mass is `2 * π`.
The corresponding statement on the quotient is Mathlib's `orthonormal_fourier`; the proofs
below instead go directly through `integral_exp_mul_complex`.
-/

@[expose] public section

open Set

namespace Complex

/-- The circle characters have unit modulus: `‖e^{imθ}‖ = 1` for an integer `m` and a real
angle `θ`. -/
@[simp]
theorem norm_exp_int_mul_ofReal_mul_I (m : ℤ) (θ : ℝ) : ‖exp (m * θ * I)‖ = 1 := by
  have h : (m : ℂ) * (θ : ℂ) * I = ((m * θ : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, norm_exp_ofReal_mul_I]

end Complex

namespace MeasureTheory

/-- The normalised Lebesgue measure on one period of the angle: a probability measure on `ℝ`
carried by `Ioc 0 (2π)`, the image of the Haar probability measure of the unit circle under a
branch of the argument. -/
noncomputable def angleProbability : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Set.Ioc 0 (2 * Real.pi))

instance : IsProbabilityMeasure angleProbability := by
  constructor
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [angleProbability, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
    sub_zero, smul_eq_mul]
  refine ENNReal.inv_mul_cancel ?_ ENNReal.ofReal_ne_top
  simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hpos

/-- A circle character is integrable for `angleProbability`: it is continuous and bounded, and
the measure is finite. -/
theorem integrable_exp_int_mul_I (m : ℤ) :
    Integrable (fun θ : ℝ ↦ Complex.exp (m * θ * Complex.I)) angleProbability := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · simp

/-- **Orthogonality of the circle characters.** The average of `e^{imθ}` over one period of the
angle is `1` for the trivial character `m = 0` and `0` otherwise: the primitive
`e^{imθ}/(im)` is `2π`-periodic. -/
theorem integral_exp_int_mul_I (m : ℤ) :
    ∫ θ, Complex.exp (m * θ * Complex.I) ∂angleProbability = if m = 0 then 1 else 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [ite_eq_right hm]
    have h0 : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hc : (m : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hm) Complex.I_ne_zero
    have heq : ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), Complex.exp (m * θ * Complex.I)
        = ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp ((m : ℂ) * Complex.I * θ) := by
      rw [intervalIntegral.integral_of_le h0]
      refine setIntegral_congr_fun measurableSet_Ioc fun θ _ ↦ ?_
      congr 1
      ring
    have hI : ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), Complex.exp (m * θ * Complex.I) = 0 := by
      rw [heq, integral_exp_mul_complex hc]
      have h1 : (m : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h1, Complex.exp_int_mul_two_pi_mul_I]
      simp
    rw [angleProbability, integral_smul_measure, hI, smul_zero]

/-- The average of `2 cos θ · e^{imθ}` over one period of the angle is `1` for `m = ±1` and `0`
otherwise: `2 cos θ = e^{iθ} + e^{-iθ}` splits the integrand into the characters `m + 1` and
`m - 1`. -/
theorem integral_cos_mul_exp_int_mul_I (m : ℤ) :
    ∫ θ, (2 * Real.cos θ : ℂ) * Complex.exp (m * θ * Complex.I) ∂angleProbability
      = if m = 1 ∨ m = -1 then 1 else 0 := by
  have key : ∀ θ : ℝ, (2 * Real.cos θ : ℂ) * Complex.exp (m * θ * Complex.I)
      = Complex.exp (((m + 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)
        + Complex.exp (((m - 1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
    intro θ
    have h2 : (2 * Real.cos θ : ℂ)
        = Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I) := by
      rw [Complex.ofReal_cos]
      exact Complex.two_cos _
    rw [h2, add_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  simp_rw [key]
  rw [integral_add (integrable_exp_int_mul_I (m + 1)) (integrable_exp_int_mul_I (m - 1)),
    integral_exp_int_mul_I, integral_exp_int_mul_I]
  by_cases h1 : m = 1
  · subst h1; norm_num
  by_cases h2 : m = -1
  · subst h2; norm_num
  rw [ite_eq_right (show m + 1 ≠ 0 by omega), ite_eq_right (show m - 1 ≠ 0 by omega),
    ite_eq_right (show ¬(m = 1 ∨ m = -1) by tauto)]
  ring

/-- **Orthogonality of the characters of a finite-dimensional torus.** The average of
`e^{i ∑_{c ∈ s} m_c θ_c}` over the product of one period of each angle is `1` if `m` vanishes on
`s` and `0` otherwise: by Fubini the integral factorises into one-dimensional character
integrals, one of which vanishes as soon as some `m_c`, `c ∈ s`, is nonzero. -/
theorem integral_exp_sum_int_mul_I {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (m : ι → ℤ) :
    (∫ θ : ι → ℝ, Complex.exp (Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ))
        ∂(Measure.pi fun _ : ι ↦ angleProbability))
      = if ∀ c ∈ s, m c = 0 then 1 else 0 := by
  classical
  -- extend `m` by zero outside `s`, so that the sum runs over all of `ι`
  set m' : ι → ℤ := fun c ↦ if c ∈ s then m c else 0 with hm'
  have hrw : ∀ θ : ι → ℝ, Complex.exp (Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ))
      = ∏ c : ι, Complex.exp ((m' c : ℂ) * (θ c : ℂ) * Complex.I) := by
    intro θ
    have hsub : ∑ c ∈ s, ((m' c : ℂ) * (θ c : ℂ) * Complex.I)
        = ∑ c : ι, ((m' c : ℂ) * (θ c : ℂ) * Complex.I) :=
      Finset.sum_subset (Finset.subset_univ s) fun c _ hcs ↦ by simp [hm', hcs]
    have hs : ∑ c ∈ s, ((m' c : ℂ) * (θ c : ℂ) * Complex.I)
        = Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      simp only [hm', ite_eq_left hc]
      ring
    rw [← Complex.exp_sum, ← hsub, hs]
  simp_rw [hrw]
  rw [integral_fintype_prod_eq_prod
    (fun (c : ι) (x : ℝ) ↦ Complex.exp ((m' c : ℂ) * (x : ℂ) * Complex.I))]
  simp_rw [integral_exp_int_mul_I]
  by_cases h : ∀ c ∈ s, m c = 0
  · rw [ite_eq_left h]
    refine Finset.prod_eq_one fun c _ ↦ ?_
    have hc : m' c = 0 := by
      by_cases hcs : c ∈ s
      · simp [hm', hcs, h c hcs]
      · simp [hm', hcs]
    simp [hc]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨c, hcs, hc⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
    have hc' : m' c ≠ 0 := by simp [hm', hcs, hc]
    simp [hc']

end MeasureTheory

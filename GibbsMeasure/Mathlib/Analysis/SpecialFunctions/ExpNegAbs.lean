/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Fourier transform of the two-sided exponential, and the Cauchy kernel

The two-sided exponential `x ↦ e^{-a|x|}` (`a > 0`) has Fourier transform the Cauchy–Poisson
kernel `b ↦ 2a/(a² + b²)`:

`∫_ℝ e^{ibx} e^{-a|x|} dx = 2a/(a² + b²)`,  equivalently  `∫_ℝ cos(bx) e^{-a|x|} dx = 2a/(a²+b²)`.

Read from right to left this exhibits the Cauchy kernel `b ↦ a/(a² + b²)` as `½` times the
integral of the characters `x ↦ e^{ibx}` against the *finite positive* measure `e^{-a|x|} dx`.

## Main results

* `MeasureTheory.integrable_exp_neg_mul_abs`, `MeasureTheory.integrable_cos_mul_exp_neg_mul_abs`,
  `MeasureTheory.integrable_exp_mul_I_mul_exp_neg_mul_abs`: integrability.
* `MeasureTheory.integral_exp_mul_I_mul_exp_neg_mul_abs`: the complex form.
* `MeasureTheory.integral_cos_mul_exp_neg_mul_abs`: the real (cosine) form.
* `MeasureTheory.integral_exp_neg_mul_abs`: the total mass `∫_ℝ e^{-a|x|} dx = 2/a`.

## Implementation notes

The proof splits `ℝ` at the origin and uses Mathlib's `integral_exp_mul_complex_Ioi` and
`integral_exp_mul_complex_Iic`; on each half the integrand is a genuine complex exponential
`e^{(∓a + ib)x}`.  Neither contour integration nor Fourier inversion is needed in this direction.

The *converse* — the Fourier transform of the Cauchy density,
`∫_ℝ cos(tx)/(1+x²) dx = π e^{-|t|}` — is not proved here; it would follow from the statements
below by Fourier inversion (`Continuous.fourierInv_fourier_eq`), at the cost of the `2π`
bookkeeping in Mathlib's normalisation of `𝓕`, for which Mathlib currently has no dilation lemma.
-/

@[expose] public section

open Set Complex MeasureTheory

namespace MeasureTheory

variable {a b : ℝ}

/-- On the positive half-line the integrand `e^{ibx} e^{-a|x|}` is the complex exponential
`e^{(ib - a)x}`. -/
private lemma eqOn_exp_neg_mul_abs_Ioi (a b : ℝ) :
    EqOn (fun x : ℝ ↦ Complex.exp ((b * Complex.I - a) * x))
      (fun x : ℝ ↦ Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) (Ioi 0) := by
  intro x hx
  simp only [abs_of_pos (mem_Ioi.1 hx), Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- On the negative half-line the integrand `e^{ibx} e^{-a|x|}` is the complex exponential
`e^{(ib + a)x}`. -/
private lemma eqOn_exp_neg_mul_abs_Iic (a b : ℝ) :
    EqOn (fun x : ℝ ↦ Complex.exp ((b * Complex.I + a) * x))
      (fun x : ℝ ↦ Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) (Iic 0) := by
  intro x hx
  simp only [abs_of_nonpos (mem_Iic.1 hx), Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma integrableOn_exp_neg_mul_abs_Ioi (ha : 0 < a) (b : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦ Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) (Ioi 0) := by
  refine (integrableOn_exp_mul_complex_Ioi (a := (b * Complex.I - a)) ?_ 0).congr_fun
    (eqOn_exp_neg_mul_abs_Ioi a b) measurableSet_Ioi
  simpa [Complex.sub_re, Complex.mul_re] using ha

private lemma integrableOn_exp_neg_mul_abs_Iic (ha : 0 < a) (b : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦ Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)) (Iic 0) := by
  refine (integrableOn_exp_mul_complex_Iic (a := (b * Complex.I + a)) ?_ 0).congr_fun
    (eqOn_exp_neg_mul_abs_Iic a b) measurableSet_Iic
  simpa [Complex.add_re, Complex.mul_re] using ha

/-- The two-sided exponential `x ↦ e^{-a|x|}` is integrable for `a > 0`. -/
theorem integrable_exp_neg_mul_abs (ha : 0 < a) :
    Integrable fun x : ℝ ↦ Real.exp (-(a * |x|)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    simp only [abs_of_nonpos (mem_Iic.1 hx)]
    ring_nf
  · refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [abs_of_pos (mem_Ioi.1 hx)]
    ring_nf

/-- `x ↦ e^{ibx} e^{-a|x|}` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    Integrable fun x : ℝ ↦ Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_exp_neg_mul_abs_Iic ha b).union (integrableOn_exp_neg_mul_abs_Ioi ha b)

/-- The real part of `e^{ibx} e^{-a|x|}`. -/
private lemma re_exp_mul_I_mul_exp_neg_mul_abs (a b x : ℝ) :
    (Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)).re
      = Real.cos (b * x) * Real.exp (-(a * |x|)) := by
  rw [show (b : ℂ) * x * Complex.I = ((b * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- **The Fourier transform of the two-sided exponential is the Cauchy–Poisson kernel.**
For `a > 0`,

`∫_ℝ e^{ibx} e^{-a|x|} dx = 2a/(a² + b²)`.

Read from right to left: the Cauchy kernel `b ↦ a/(a² + b²)` is `½` times a superposition of the
characters `x ↦ e^{ibx}` against the finite positive measure `e^{-a|x|} dx`. -/
theorem integral_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    ∫ x : ℝ, Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hAre : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hBre : ((a : ℂ) - b * Complex.I).re = a := by simp
  have hA : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hAre
    exact absurd hAre.symm (ne_of_gt ha)
  have hB : (a : ℂ) - b * Complex.I ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hBre
    exact absurd hBre.symm (ne_of_gt ha)
  have hIic : ∫ x : ℝ in Iic (0 : ℝ),
      Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)
      = 1 / ((a : ℂ) + b * Complex.I) := by
    rw [← setIntegral_congr_fun measurableSet_Iic (eqOn_exp_neg_mul_abs_Iic a b),
      integral_exp_mul_complex_Iic (a := (b * Complex.I + a))
        (by simpa [Complex.add_re, Complex.mul_re] using ha)]
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_comm]
  have hIoi : ∫ x : ℝ in Ioi (0 : ℝ),
      Complex.exp (b * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ)
      = 1 / ((a : ℂ) - b * Complex.I) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi (eqOn_exp_neg_mul_abs_Ioi a b),
      integral_exp_mul_complex_Ioi (a := (b * Complex.I - a))
        (by simpa [Complex.sub_re, Complex.mul_re] using ha)]
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (b : ℂ) * Complex.I - a = -((a : ℂ) - b * Complex.I) by ring, neg_div_neg_eq]
  have hnum : ((a : ℂ) + b * Complex.I) * ((a : ℂ) - b * Complex.I)
      = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-(b : ℂ) ^ 2) * Complex.I_sq
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_exp_neg_mul_abs_Iic ha b)
    (integrableOn_exp_neg_mul_abs_Ioi ha b), hIic, hIoi, div_add_div _ _ hA hB, hnum,
    Complex.ofReal_div]
  congr 1
  push_cast
  ring

/-- `x ↦ cos(bx) e^{-a|x|}` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_cos_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    Integrable fun x : ℝ ↦ Real.cos (b * x) * Real.exp (-(a * |x|)) := by
  refine (integrable_exp_neg_mul_abs ha).mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (Real.exp_nonneg _) (Real.abs_cos_le_one _)

/-- **The Fourier transform of the two-sided exponential, real form.**  For `a > 0`,

`∫_ℝ cos(bx) e^{-a|x|} dx = 2a/(a² + b²)`.

This is the identity Georgii uses in Example (17.32) to write the Cauchy kernel
`(k, ℓ) ↦ sk/(ℓ² + s²k²)` as the integral of the characters `ℓ ↦ e^{iuℓ}` against the finite
positive measure `e^{-sk|u|} du`. -/
theorem integral_cos_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    ∫ x : ℝ, Real.cos (b * x) * Real.exp (-(a * |x|)) = 2 * a / (a ^ 2 + b ^ 2) := by
  have hre := integral_re (integrable_exp_mul_I_mul_exp_neg_mul_abs ha b)
  simp only [RCLike.re_to_complex] at hre
  rw [integral_exp_mul_I_mul_exp_neg_mul_abs ha b, Complex.ofReal_re] at hre
  rw [← hre]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x ↦ (re_exp_mul_I_mul_exp_neg_mul_abs a b x).symm)

/-- The total mass of the two-sided exponential: `∫_ℝ e^{-a|x|} dx = 2/a` for `a > 0`.  This is
the case `b = 0` of `integral_cos_mul_exp_neg_mul_abs`. -/
theorem integral_exp_neg_mul_abs (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * |x|)) = 2 / a := by
  have h := integral_cos_mul_exp_neg_mul_abs ha 0
  simp only [zero_mul, Real.cos_zero, one_mul, sq, add_zero] at h
  rw [h]
  field_simp

end MeasureTheory

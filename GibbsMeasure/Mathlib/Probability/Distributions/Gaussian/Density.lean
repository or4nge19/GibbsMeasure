/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Gaussian.Multivariate
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiWithDensity
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The multivariate Gaussian density measure on `ι → ℝ`

For a positive definite real matrix `A` indexed by a finite type `ι` and `m : ι → ℝ`, this file
defines the measure on `ι → ℝ` with Lebesgue density
```
x ↦ √(A.det / (2 * π) ^ card ι) * exp (-(1/2) * ((x - m) ⬝ᵥ A *ᵥ (x - m)))
```
and shows it is a probability measure. `A` plays the role of the *precision* matrix (the inverse
of the covariance matrix): `Mathlib.Analysis.SpecialFunctions.Gaussian.Multivariate` already
proves the normalizing-constant integral identity that makes this a probability density, in
`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct`.

Mathlib's `ProbabilityTheory.multivariateGaussian` (`Mathlib.Probability.Distributions.Gaussian.
Multivariate`) constructs the multivariate Gaussian on `EuclideanSpace ℝ ι` as a pushforward of
`stdGaussian` along `CFC.sqrt` of a *covariance* matrix, rather than by its Lebesgue density on
`ι → ℝ`; this file is the density-side construction, complementing it.

## Main definitions

* `ProbabilityTheory.multivariateGaussianPDFReal`: the real-valued density function.
* `ProbabilityTheory.multivariateGaussianPDF`: the `ℝ≥0∞`-valued density function.
* `ProbabilityTheory.multivariateGaussianPi`: the measure `volume.withDensity
  multivariateGaussianPDF` on `ι → ℝ`.

## Main statements

* `ProbabilityTheory.isProbabilityMeasure_multivariateGaussianPi`: for `A` positive definite,
  `multivariateGaussianPi A m` is a probability measure.
* `ProbabilityTheory.integral_eval_multivariateGaussianPi`: its mean is `m`.
* `ProbabilityTheory.integral_sub_mul_sub_multivariateGaussianPi`: its covariance is `A⁻¹`.

## Not done in this file

The characteristic function of `multivariateGaussianPi A m`, and its identification with
`ProbabilityTheory.multivariateGaussian m A⁻¹` on `EuclideanSpace ℝ ι`, are not proved here: see
the module docstring of the `Covariance` section below (in the source) for exactly what closed
form the real-parameter moment generating function `integral_exp_neg_half_add_mul_dotProduct`
identity does *not*, by itself, extend to. Computing the characteristic function needs a genuinely
new complex-exponent analogue of
`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct` (the real-`b` normalizing
identity in `GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Gaussian.Multivariate`), obtained by
re-running its spectral-decomposition (`hA.isHermitian.spectral_theorem`) plus Fubini argument with
a complex phase `I * (t ⬝ᵥ x)` in place of the real `b ⬝ᵥ x`, diagonalized against the complex
one-dimensional Gaussian Fourier transform `fourierIntegral_gaussian`
(`Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform`) coordinate by coordinate. That is a
second construction of comparable size to the real-`b` one and is not a corollary of the mean and
covariance results proved here; it has not been attempted.
-/

@[expose] public section

open MeasureTheory Measure Matrix Real
open scoped ENNReal

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Def

/-- The density, with respect to Lebesgue measure on `ι → ℝ`, of the multivariate Gaussian
distribution with mean `m` and *precision* matrix `A` (the inverse of the covariance matrix).
Well-defined for every `A : Matrix ι ι ℝ`; it integrates to `1` when `A` is positive definite,
see `isProbabilityMeasure_multivariateGaussianPi`. -/
noncomputable def multivariateGaussianPDFReal (A : Matrix ι ι ℝ) (m x : ι → ℝ) : ℝ :=
  Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
    Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m)))

lemma multivariateGaussianPDFReal_def (A : Matrix ι ι ℝ) (m : ι → ℝ) :
    multivariateGaussianPDFReal A m =
      fun x ↦ Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) := rfl

lemma multivariateGaussianPDFReal_nonneg (A : Matrix ι ι ℝ) (m x : ι → ℝ) :
    0 ≤ multivariateGaussianPDFReal A m x :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

@[fun_prop]
lemma measurable_multivariateGaussianPDFReal (A : Matrix ι ι ℝ) (m : ι → ℝ) :
    Measurable (multivariateGaussianPDFReal A m) := by
  unfold multivariateGaussianPDFReal; fun_prop

/-- The `ℝ≥0∞`-valued density of the multivariate Gaussian distribution with mean `m` and
precision matrix `A`. -/
noncomputable def multivariateGaussianPDF (A : Matrix ι ι ℝ) (m x : ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (multivariateGaussianPDFReal A m x)

lemma multivariateGaussianPDF_def (A : Matrix ι ι ℝ) (m : ι → ℝ) :
    multivariateGaussianPDF A m = fun x ↦ ENNReal.ofReal (multivariateGaussianPDFReal A m x) :=
  rfl

@[simp]
lemma toReal_multivariateGaussianPDF (A : Matrix ι ι ℝ) (m x : ι → ℝ) :
    (multivariateGaussianPDF A m x).toReal = multivariateGaussianPDFReal A m x :=
  ENNReal.toReal_ofReal (multivariateGaussianPDFReal_nonneg A m x)

lemma multivariateGaussianPDF_lt_top (A : Matrix ι ι ℝ) (m x : ι → ℝ) :
    multivariateGaussianPDF A m x < ∞ := by
  rw [multivariateGaussianPDF]; exact ENNReal.ofReal_lt_top

@[fun_prop]
lemma measurable_multivariateGaussianPDF (A : Matrix ι ι ℝ) (m : ι → ℝ) :
    Measurable (multivariateGaussianPDF A m) :=
  (measurable_multivariateGaussianPDFReal A m).ennreal_ofReal

/-- The multivariate Gaussian distribution on `ι → ℝ` with mean `m` and *precision* matrix `A`
(the inverse of the covariance matrix), as the measure with Lebesgue density
`multivariateGaussianPDF A m`. -/
noncomputable def multivariateGaussianPi (A : Matrix ι ι ℝ) (m : ι → ℝ) : Measure (ι → ℝ) :=
  volume.withDensity (multivariateGaussianPDF A m)

end Def

section ProbabilityMeasure

/-- The normalizing constant of `multivariateGaussianPDFReal` and of
`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec` are reciprocal: this identity recurs
throughout the file (probability mass, mean, covariance). -/
private lemma sqrt_det_div_mul_sqrt_div_det_eq_one {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) = 1 := by
  have hdetpos := hA.det_pos
  rw [← Real.sqrt_mul (div_nonneg hdetpos.le (by positivity))]
  rw [show A.det / (2 * π) ^ Fintype.card ι * ((2 * π) ^ Fintype.card ι / A.det) = 1 by
    field_simp]
  exact Real.sqrt_one

/-- The density `multivariateGaussianPDFReal A m` is integrable when `A` is positive definite:
translate the `b = 0` case of
`Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct` by `m` and scale by the
normalizing constant. -/
lemma integrable_multivariateGaussianPDFReal {A : Matrix ι ι ℝ} (hA : A.PosDef) (m : ι → ℝ) :
    Integrable (multivariateGaussianPDFReal A m) := by
  have hf : Integrable (fun y : ι → ℝ ↦ Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := by
    simpa using
      Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA (0 : ι → ℝ)
  exact (hf.comp_sub_right m).const_mul (Real.sqrt (A.det / (2 * π) ^ Fintype.card ι))

/-- The density `multivariateGaussianPDFReal A m` integrates to `1` when `A` is positive
definite: this is exactly the normalizing-constant identity
`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec`, after translating by `m`
(`MeasureTheory.integral_sub_right_eq_self`). -/
lemma integral_multivariateGaussianPDFReal {A : Matrix ι ι ℝ} (hA : A.PosDef) (m : ι → ℝ) :
    ∫ x, multivariateGaussianPDFReal A m x = 1 := by
  simp only [multivariateGaussianPDFReal]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : ι → ℝ ↦ Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) m,
    Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec hA]
  exact sqrt_det_div_mul_sqrt_div_det_eq_one hA

/-- **The multivariate Gaussian distribution is a probability measure.** For `A` positive
definite, `multivariateGaussianPi A m` (mean `m`, precision matrix `A`) is a probability
measure on `ι → ℝ`. -/
theorem isProbabilityMeasure_multivariateGaussianPi {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (m : ι → ℝ) : IsProbabilityMeasure (multivariateGaussianPi A m) where
  measure_univ := by
    rw [multivariateGaussianPi, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      MeasureTheory.setLIntegral_univ, multivariateGaussianPDF_def,
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrable_multivariateGaussianPDFReal hA m)
        (ae_of_all _ (multivariateGaussianPDFReal_nonneg A m)),
      integral_multivariateGaussianPDFReal hA m, ENNReal.ofReal_one]

end ProbabilityMeasure

section TailBounds

/-- Elementary real-analysis fact used to dominate a polynomial by an exponential: for every
real `x`, `|x| ≤ exp x + exp (-x)`. -/
lemma abs_le_exp_add_exp (x : ℝ) : |x| ≤ Real.exp x + Real.exp (-x) := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · nlinarith [Real.add_one_le_exp (-x), Real.exp_pos x]
  · nlinarith [Real.add_one_le_exp x, Real.exp_pos (-x)]

omit [DecidableEq ι] in
/-- The odd moment `y ↦ (v ⬝ᵥ y) * exp (-(1/2) * (y ⬝ᵥ A *ᵥ y))` is integrable for every
`v : ι → ℝ`, by comparison with the (already integrable, by
`Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct`) functions at `b = v`
and `b = -v`, using `abs_le_exp_add_exp`. -/
lemma integrable_dotProduct_mul_exp_neg_half_dotProduct_mulVec {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (v : ι → ℝ) :
    Integrable
      (fun y : ι → ℝ ↦ (v ⬝ᵥ y) * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := by
  classical
  have hbound : Integrable (fun y : ι → ℝ ↦
      Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y) + v ⬝ᵥ y) +
        Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y) + (-v) ⬝ᵥ y)) :=
    (Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA v).add
      (Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA (-v))
  refine hbound.mono' (by fun_prop) (ae_of_all _ fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), neg_dotProduct,
    Real.exp_add, Real.exp_add]
  calc |v ⬝ᵥ y| * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))
      ≤ (Real.exp (v ⬝ᵥ y) + Real.exp (-(v ⬝ᵥ y))) * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) :=
        mul_le_mul_of_nonneg_right (abs_le_exp_add_exp _) (Real.exp_pos _).le
    _ = Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * Real.exp (v ⬝ᵥ y) +
        Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * Real.exp (-(v ⬝ᵥ y)) := by ring

end TailBounds

section Mean

/-- **The mean of the multivariate Gaussian density measure.** For `A` positive definite, the
`i`-th coordinate of a `multivariateGaussianPi A m`-distributed vector has mean `m i`: translate
by `m` and use that the centred integrand `y ↦ y i * exp (-(1/2) * (y ⬝ᵥ A *ᵥ y))` is odd, hence
integrates to `0` (`Measure.measurePreserving_neg`, negation-invariance of Lebesgue measure). -/
theorem integral_eval_multivariateGaussianPi {A : Matrix ι ι ℝ} (hA : A.PosDef) (m : ι → ℝ)
    (i : ι) : ∫ x, x i ∂(multivariateGaussianPi A m) = m i := by
  have hdetpos := hA.det_pos
  -- The odd moment `∫ y, exp (-(1/2) y ⬝ A ⬝ y) * y i` is integrable and vanishes.
  have hint_odd : Integrable
      (fun y : ι → ℝ ↦ Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i) := by
    have h := integrable_dotProduct_mul_exp_neg_half_dotProduct_mulVec hA (Pi.single i (1 : ℝ))
    simpa [single_dotProduct, mul_comm] using h
  have hodd : ∫ y : ι → ℝ, Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i = 0 := by
    have hnegPreserving : MeasurePreserving (Neg.neg : (ι → ℝ) → (ι → ℝ)) volume volume :=
      Measure.measurePreserving_neg volume
    have hcomp :
        ∫ y : ι → ℝ, Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i =
          ∫ y : ι → ℝ, Real.exp (-(1 / 2) * ((-y) ⬝ᵥ A *ᵥ (-y))) * (-y) i :=
      (MeasurePreserving.integral_comp hnegPreserving
        (Homeomorph.neg (ι → ℝ)).measurableEmbedding
        (fun y ↦ Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i)).symm
    have heven : ∀ y : ι → ℝ,
        Real.exp (-(1 / 2) * ((-y) ⬝ᵥ A *ᵥ (-y))) * (-y) i =
          -(Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i) := by
      intro y
      rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, Pi.neg_apply]; ring
    simp only [heven] at hcomp
    rw [MeasureTheory.integral_neg] at hcomp
    linarith
  -- The `0`-th moment is the normalizing-constant integral.
  have hf_integral :
      ∫ y : ι → ℝ, Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) =
        Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) :=
    Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec hA
  have hf_integrable : Integrable (fun y : ι → ℝ ↦ Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := by
    simpa using
      Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA (0 : ι → ℝ)
  -- Convert the goal to a Lebesgue integral of the real-valued density.
  rw [multivariateGaussianPi,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_multivariateGaussianPDF A m)
      (ae_of_all _ (multivariateGaussianPDF_lt_top A m))]
  simp only [toReal_multivariateGaussianPDF, smul_eq_mul, multivariateGaussianPDFReal]
  -- Centre by `m`, splitting the integrand into the odd part (vanishes) and the constant part.
  have heq : (fun x : ι → ℝ ↦
      Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * x i)
      = (fun x : ι → ℝ ↦
          (fun y : ι → ℝ ↦
              Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
                (Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i +
                  Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * m i)) (x - m)) := by
    funext x
    change Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * x i
        = Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
            (Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * (x - m) i +
              Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * m i)
    rw [Pi.sub_apply]; ring
  rw [heq,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : ι → ℝ ↦ Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        (Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * y i +
          Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) * m i)) m,
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hint_odd (hf_integrable.mul_const (m i)),
    MeasureTheory.integral_mul_const, hodd, hf_integral, zero_add, ← mul_assoc,
    sqrt_det_div_mul_sqrt_div_det_eq_one hA, one_mul]

end Mean

section Covariance

/-- **Domination for the first derivative in `t`.** For `t` ranging over `[c₁, c₂]`, `|u| * exp
(t * u)` is bounded, uniformly in `t`, by a fixed sum of two exponentials in `u`. -/
lemma abs_mul_exp_le {c₁ c₂ t u : ℝ} (h1 : c₁ ≤ t) (h2 : t ≤ c₂) :
    |u| * Real.exp (t * u) ≤ Real.exp ((c₂ + 1) * u) + Real.exp ((c₁ - 1) * u) := by
  rcases le_total 0 u with hu | hu
  · have hexp1 : Real.exp (t * u) ≤ Real.exp (c₂ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hu)
    have hexp2 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hle : |u| * Real.exp (t * u) ≤ Real.exp u * Real.exp (c₂ * u) := by
      rw [abs_of_nonneg hu]
      exact mul_le_mul hexp2 hexp1 (Real.exp_pos _).le (Real.exp_pos _).le
    rw [← Real.exp_add, show u + c₂ * u = (c₂ + 1) * u by ring] at hle
    linarith [Real.exp_pos ((c₁ - 1) * u)]
  · have hexp1 : Real.exp (t * u) ≤ Real.exp (c₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hexp2 : -u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have hle : |u| * Real.exp (t * u) ≤ Real.exp (-u) * Real.exp (c₁ * u) := by
      rw [abs_of_nonpos hu]
      exact mul_le_mul hexp2 hexp1 (Real.exp_pos _).le (Real.exp_pos _).le
    rw [← Real.exp_add, show -u + c₁ * u = (c₁ - 1) * u by ring] at hle
    linarith [Real.exp_pos ((c₂ + 1) * u)]

/-- **Domination for the second derivative in `t`.** Quadratic analogue of `abs_mul_exp_le`. -/
lemma sq_mul_exp_le {c₁ c₂ t u : ℝ} (h1 : c₁ ≤ t) (h2 : t ≤ c₂) :
    u ^ 2 * Real.exp (t * u) ≤ Real.exp ((c₂ + 2) * u) + Real.exp ((c₁ - 2) * u) := by
  rcases le_total 0 u with hu | hu
  · have hexp1 : Real.exp (t * u) ≤ Real.exp (c₂ * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hu)
    have hexp2 : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hsq : u ^ 2 ≤ Real.exp u * Real.exp u := by
      rw [sq]; exact mul_le_mul hexp2 hexp2 hu (Real.exp_pos _).le
    have hle : u ^ 2 * Real.exp (t * u) ≤ Real.exp u * Real.exp u * Real.exp (c₂ * u) :=
      mul_le_mul hsq hexp1 (Real.exp_pos _).le (by positivity)
    rw [← Real.exp_add, ← Real.exp_add, show u + u + c₂ * u = (c₂ + 2) * u by ring] at hle
    linarith [Real.exp_pos ((c₁ - 2) * u)]
  · have hexp1 : Real.exp (t * u) ≤ Real.exp (c₁ * u) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hexp2 : -u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have hsq : u ^ 2 ≤ Real.exp (-u) * Real.exp (-u) := by
      have hsq' : (-u) ^ 2 ≤ Real.exp (-u) * Real.exp (-u) := by
        rw [sq]; exact mul_le_mul hexp2 hexp2 (by linarith) (Real.exp_pos _).le
      simpa using hsq'
    have hle : u ^ 2 * Real.exp (t * u) ≤ Real.exp (-u) * Real.exp (-u) * Real.exp (c₁ * u) :=
      mul_le_mul hsq hexp1 (Real.exp_pos _).le (by positivity)
    rw [← Real.exp_add, ← Real.exp_add, show -u + -u + c₁ * u = (c₁ - 2) * u by ring] at hle
    linarith [Real.exp_pos ((c₂ + 2) * u)]

/-- The moment generating function of the centred Gaussian kernel along a direction `v`, in
closed form: specialise
`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct` to `b = t • v`. -/
private lemma integral_exp_neg_half_add_mul_dotProduct {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (v : ι → ℝ) (t : ℝ) :
    ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) *
        Real.exp ((1 / 2) * (t ^ 2 * (v ⬝ᵥ A⁻¹ *ᵥ v))) := by
  have h := Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct hA (t • v)
  simp only [smul_dotProduct, mulVec_smul, dotProduct_smul, smul_eq_mul] at h
  rwa [show t * (t * (v ⬝ᵥ A⁻¹ *ᵥ v)) = t ^ 2 * (v ⬝ᵥ A⁻¹ *ᵥ v) by ring] at h

omit [DecidableEq ι] in
/-- Differentiating `integral_exp_neg_half_add_mul_dotProduct` under the integral sign, at any
basepoint `t₀`: **Leibniz's rule**, via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and
the domination bound `abs_mul_exp_le`. -/
private lemma hasDerivAt_integral_exp_neg_half_add_mul_dotProduct {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (v : ι → ℝ) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
      (∫ x : ι → ℝ, (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x))) t₀ := by
  classical
  have hs : Set.Ioo (t₀ - 1) (t₀ + 1) ∈ nhds t₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ t in nhds t₀,
      AEStronglyMeasurable
        (fun x : ι → ℝ ↦ Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))) volume :=
    Filter.Eventually.of_forall fun t ↦
      Measurable.aestronglyMeasurable (by fun_prop)
  have hF_int : Integrable
      (fun x : ι → ℝ ↦ Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x))) := by
    have h := Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA (t₀ • v)
    simpa [smul_dotProduct] using h
  have hF'_meas : AEStronglyMeasurable
      (fun x : ι → ℝ ↦ (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x))) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have h_bound : ∀ᵐ x ∂volume, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1),
      ‖(v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))‖ ≤
        Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (t₀ + 2) * (v ⬝ᵥ x)) +
          Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (t₀ - 2) * (v ⬝ᵥ x)) := by
    refine ae_of_all _ fun x t ht ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_add, Real.exp_add,
      Real.exp_add]
    calc |v ⬝ᵥ x| * (Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp (t * (v ⬝ᵥ x)))
        = Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * (|v ⬝ᵥ x| * Real.exp (t * (v ⬝ᵥ x))) := by ring
      _ ≤ Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) *
            (Real.exp ((t₀ + 2) * (v ⬝ᵥ x)) + Real.exp ((t₀ - 2) * (v ⬝ᵥ x))) := by
          have hb := abs_mul_exp_le ht.1.le ht.2.le (u := v ⬝ᵥ x)
          rw [show t₀ + 1 + 1 = t₀ + 2 by ring, show t₀ - 1 - 1 = t₀ - 2 by ring] at hb
          exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp ((t₀ + 2) * (v ⬝ᵥ x)) +
            Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp ((t₀ - 2) * (v ⬝ᵥ x)) := by ring
  have hbound_integrable : Integrable (fun x : ι → ℝ ↦
      Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (t₀ + 2) * (v ⬝ᵥ x)) +
        Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (t₀ - 2) * (v ⬝ᵥ x))) := by
    have h1 := Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA
      ((t₀ + 2) • v)
    have h2 := Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA
      ((t₀ - 2) • v)
    simp only [smul_dotProduct] at h1 h2
    exact h1.add h2
  have h_diff : ∀ᵐ x ∂volume, ∀ t ∈ Set.Ioo (t₀ - 1) (t₀ + 1),
      HasDerivAt (fun t : ℝ ↦ Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
        ((v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))) t := by
    refine ae_of_all _ fun x t _ ↦ ?_
    have hlin : HasDerivAt (fun t : ℝ ↦ -(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)) (v ⬝ᵥ x) t := by
      have h0 : HasDerivAt (fun t : ℝ ↦ -(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))
          (1 * (v ⬝ᵥ x)) t :=
        ((hasDerivAt_id t).mul_const (v ⬝ᵥ x)).const_add (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))
      rwa [one_mul] at h0
    simpa [mul_comm] using hlin.exp
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    hbound_integrable h_diff).2

/-- **The moment generating function of the odd moment**, in closed form: for every `t₀`,
`∫ x, (v ⬝ᵥ x) * exp (-(1/2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x))
  = √((2π)^n / A.det) * exp ((1/2) * (t₀^2 * (v ⬝ᵥ A⁻¹ *ᵥ v))) * (t₀ * (v ⬝ᵥ A⁻¹ *ᵥ v))`,
obtained by matching the Leibniz derivative
`hasDerivAt_integral_exp_neg_half_add_mul_dotProduct` against the elementary derivative of the
closed form `integral_exp_neg_half_add_mul_dotProduct` (`HasDerivAt.unique`). -/
private lemma integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (v : ι → ℝ) (t₀ : ℝ) :
    ∫ x : ι → ℝ, (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x)) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) *
        (Real.exp ((1 / 2) * (t₀ ^ 2 * (v ⬝ᵥ A⁻¹ *ᵥ v))) * (t₀ * (v ⬝ᵥ A⁻¹ *ᵥ v))) := by
  set C : ℝ := Real.sqrt ((2 * π) ^ Fintype.card ι / A.det)
  set κ : ℝ := v ⬝ᵥ A⁻¹ *ᵥ v
  have hclosed : HasDerivAt (fun t : ℝ ↦ C * Real.exp ((1 / 2) * (t ^ 2 * κ)))
      (C * (Real.exp ((1 / 2) * (t₀ ^ 2 * κ)) * (t₀ * κ))) t₀ := by
    have h1 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * (t ^ 2 * κ)) (t₀ * κ) t₀ := by
      have h0 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * (t ^ 2 * κ))
          ((1 / 2 : ℝ) * ((2 : ℝ) * t₀ ^ (2 - 1) * κ)) t₀ :=
        ((hasDerivAt_pow 2 t₀).mul_const κ).const_mul (1 / 2 : ℝ)
      have hv : (1 / 2 : ℝ) * ((2 : ℝ) * t₀ ^ (2 - 1) * κ) = t₀ * κ := by norm_num; ring
      rwa [hv] at h0
    simpa [mul_comm] using h1.exp.const_mul C
  have hleft :
      HasDerivAt (fun t : ℝ ↦ ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
        (∫ x : ι → ℝ, (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t₀ * (v ⬝ᵥ x))) t₀ :=
    hasDerivAt_integral_exp_neg_half_add_mul_dotProduct hA v t₀
  have hfun : (fun t : ℝ ↦ ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
      = (fun t : ℝ ↦ C * Real.exp ((1 / 2) * (t ^ 2 * κ))) :=
    funext fun t ↦ integral_exp_neg_half_add_mul_dotProduct hA v t
  rw [hfun] at hleft
  exact hleft.unique hclosed

omit [DecidableEq ι] in
/-- Differentiating `integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct` under the integral
sign, at `t₀ = 0`: the second application of Leibniz's rule, via the quadratic domination bound
`sq_mul_exp_le`. -/
private lemma hasDerivAt_integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (v : ι → ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ x : ι → ℝ, (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
      (∫ x : ι → ℝ, (v ⬝ᵥ x) ^ 2 * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))) 0 := by
  classical
  have hs : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hF_meas : ∀ᶠ t in nhds (0 : ℝ),
      AEStronglyMeasurable
        (fun x : ι → ℝ ↦ (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))) volume :=
    Filter.Eventually.of_forall fun t ↦ Measurable.aestronglyMeasurable (by fun_prop)
  have hF_int : Integrable
      (fun x : ι → ℝ ↦ (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (0 : ℝ) * (v ⬝ᵥ x))) := by
    simpa using integrable_dotProduct_mul_exp_neg_half_dotProduct_mulVec hA v
  have hF'_meas : AEStronglyMeasurable
      (fun x : ι → ℝ ↦
        (v ⬝ᵥ x) ^ 2 * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (0 : ℝ) * (v ⬝ᵥ x))) volume :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have h_bound : ∀ᵐ x ∂volume, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      ‖(v ⬝ᵥ x) ^ 2 * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))‖ ≤
        Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (3 : ℝ) * (v ⬝ᵥ x)) +
          Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (-3 : ℝ) * (v ⬝ᵥ x)) := by
    refine ae_of_all _ fun x t ht ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _),
      Real.exp_add, Real.exp_add, Real.exp_add]
    calc (v ⬝ᵥ x) ^ 2 * (Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp (t * (v ⬝ᵥ x)))
        = Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * ((v ⬝ᵥ x) ^ 2 * Real.exp (t * (v ⬝ᵥ x))) := by
          ring
      _ ≤ Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) *
            (Real.exp ((3 : ℝ) * (v ⬝ᵥ x)) + Real.exp ((-3 : ℝ) * (v ⬝ᵥ x))) := by
          have hb := sq_mul_exp_le ht.1.le ht.2.le (u := v ⬝ᵥ x)
          rw [show (1 : ℝ) + 2 = 3 by norm_num, show (-1 : ℝ) - 2 = -3 by norm_num] at hb
          exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp ((3 : ℝ) * (v ⬝ᵥ x)) +
            Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) * Real.exp ((-3 : ℝ) * (v ⬝ᵥ x)) := by ring
  have hbound_integrable : Integrable (fun x : ι → ℝ ↦
      Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (3 : ℝ) * (v ⬝ᵥ x)) +
        Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + (-3 : ℝ) * (v ⬝ᵥ x))) := by
    have h1 := Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA
      ((3 : ℝ) • v)
    have h2 := Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA
      ((-3 : ℝ) • v)
    simp only [smul_dotProduct] at h1 h2
    exact h1.add h2
  have h_diff : ∀ᵐ x ∂volume, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
        ((v ⬝ᵥ x) ^ 2 * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))) t := by
    refine ae_of_all _ fun x t _ ↦ ?_
    have hlin : HasDerivAt (fun t : ℝ ↦ -(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)) (v ⬝ᵥ x) t := by
      have h0 : HasDerivAt (fun t : ℝ ↦ -(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x))
          (1 * (v ⬝ᵥ x)) t :=
        ((hasDerivAt_id t).mul_const (v ⬝ᵥ x)).const_add (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))
      rwa [one_mul] at h0
    have hexp := hlin.exp
    have hmul := hexp.const_mul (v ⬝ᵥ x)
    have heq : (v ⬝ᵥ x) *
        (Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)) * (v ⬝ᵥ x)) =
        (v ⬝ᵥ x) ^ 2 * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)) := by ring
    rwa [heq] at hmul
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    hbound_integrable h_diff
  simpa using h.2

/-- **The general second moment of the centred Gaussian kernel.** For `A` positive definite and
any `v : ι → ℝ`,
`∫ y, (v ⬝ᵥ y) ^ 2 * exp (-(1/2) * (y ⬝ᵥ A *ᵥ y)) = √((2π)^n / A.det) * (v ⬝ᵥ A⁻¹ *ᵥ v)`,
obtained by matching the Leibniz derivative
`hasDerivAt_integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct` against the elementary
derivative, at `t = 0`, of the closed form
`integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct`. -/
theorem integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (v : ι → ℝ) :
    ∫ y : ι → ℝ, (v ⬝ᵥ y) ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) * (v ⬝ᵥ A⁻¹ *ᵥ v) := by
  set C : ℝ := Real.sqrt ((2 * π) ^ Fintype.card ι / A.det)
  set κ : ℝ := v ⬝ᵥ A⁻¹ *ᵥ v
  have hp0 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * (t ^ 2 * κ)) (0 : ℝ) 0 := by
    have h0 : HasDerivAt (fun t : ℝ ↦ (1 / 2 : ℝ) * (t ^ 2 * κ))
        ((1 / 2 : ℝ) * ((2 : ℝ) * (0 : ℝ) ^ (2 - 1) * κ)) 0 :=
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const κ).const_mul (1 / 2 : ℝ)
    norm_num at h0
    exact h0
  have hf0 : HasDerivAt (fun t : ℝ ↦ Real.exp ((1 / 2 : ℝ) * (t ^ 2 * κ))) (0 : ℝ) 0 := by
    have := hp0.exp
    simpa using this
  have hg0 : HasDerivAt (fun t : ℝ ↦ t * κ) κ (0 : ℝ) := by
    have h0 := (hasDerivAt_id (0 : ℝ)).mul_const κ
    simpa using h0
  have hfg0 : HasDerivAt
      (fun t : ℝ ↦ Real.exp ((1 / 2 : ℝ) * (t ^ 2 * κ)) * (t * κ)) κ (0 : ℝ) := by
    have hmul := hf0.mul hg0
    convert hmul using 1 <;> first | rfl | norm_num
  have hclosed0 : HasDerivAt
      (fun t : ℝ ↦ C * (Real.exp ((1 / 2 : ℝ) * (t ^ 2 * κ)) * (t * κ))) (C * κ) (0 : ℝ) :=
    hfg0.const_mul C
  have hfun : (fun t : ℝ ↦
      ∫ x : ι → ℝ, (v ⬝ᵥ x) * Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + t * (v ⬝ᵥ x)))
      = (fun t : ℝ ↦ C * (Real.exp ((1 / 2 : ℝ) * (t ^ 2 * κ)) * (t * κ))) :=
    funext fun t ↦ integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct hA v t
  have hleft := hasDerivAt_integral_dotProduct_mul_exp_neg_half_add_mul_dotProduct hA v
  rw [hfun] at hleft
  exact hleft.unique hclosed0

/-- The integrand of `integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec` is integrable: a
nonnegative function whose Bochner integral is nonzero must be integrable. For `v = 0` the
integrand is identically `0`. -/
lemma integrable_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (v : ι → ℝ) :
    Integrable (fun y : ι → ℝ ↦ (v ⬝ᵥ y) ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := by
  rcases eq_or_ne v 0 with hv | hv
  · simp [hv]
  · by_contra h
    have hz := MeasureTheory.integral_undef h
    rw [integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA v] at hz
    have hApos : 0 < A.det := hA.det_pos
    have hcard : 0 < (2 * π) ^ Fintype.card ι := by positivity
    have hκpos : 0 < v ⬝ᵥ A⁻¹ *ᵥ v := by simpa using hA.inv.dotProduct_mulVec_pos hv
    have : 0 < Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) * (v ⬝ᵥ A⁻¹ *ᵥ v) := by
      have : 0 < Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) := Real.sqrt_pos.mpr (by positivity)
      positivity
    exact absurd hz this.ne'

/-- Positive definite real matrices are symmetric, and so are their inverses: `A⁻¹ i j = A⁻¹ j i`.
-/
private lemma inv_apply_symm {A : Matrix ι ι ℝ} (hA : A.PosDef) (i j : ι) :
    A⁻¹ i j = A⁻¹ j i := by
  have hh : (A⁻¹)ᴴ = A⁻¹ := hA.inv.isHermitian
  have h : (A⁻¹)ᵀ = A⁻¹ := by rwa [conjTranspose_eq_transpose_of_trivial] at hh
  exact congrFun (congrFun h j) i

/-- **Polarization**: the general second moment `integral_dotProduct_sq_mul_exp_neg_half_
dotProduct_mulVec` at `v = e_i + e_j`, `v = e_i` and `v = e_j` combine (via
`(y i + y j) ^ 2 - y i ^ 2 - y j ^ 2 = 2 * y i * y j`) to give the cross moment. -/
theorem integral_eval_mul_eval_exp_neg_half_dotProduct_mulVec {A : Matrix ι ι ℝ}
    (hA : A.PosDef) (i j : ι) :
    ∫ y : ι → ℝ, y i * y j * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) * A⁻¹ i j := by
  set C : ℝ := Real.sqrt ((2 * π) ^ Fintype.card ι / A.det)
  have hMi := integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA (Pi.single i (1 : ℝ))
  have hMj := integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA (Pi.single j (1 : ℝ))
  have hMij := integral_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA
    (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  have hIi := integrable_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA
    (Pi.single i (1 : ℝ))
  have hIj := integrable_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA
    (Pi.single j (1 : ℝ))
  have hIij := integrable_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec hA
    (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
  simp only [single_dotProduct, add_dotProduct, one_mul] at hMi hMj hMij hIi hIj hIij
  simp only [mulVec_single_one, Matrix.col_apply] at hMi hMj
  have hbil : (A⁻¹ *ᵥ (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))) i +
      (A⁻¹ *ᵥ (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))) j =
        A⁻¹ i i + 2 * A⁻¹ i j + A⁻¹ j j := by
    simp only [mulVec_add, Pi.add_apply, mulVec_single_one, Matrix.col_apply]
    rw [inv_apply_symm hA j i]
    ring
  rw [hbil] at hMij
  have heq : (fun y : ι → ℝ ↦ y i * y j * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)))
      = (fun y : ι → ℝ ↦ (1 / 2 : ℝ) *
          (((y i + y j) ^ 2 - y i ^ 2 - y j ^ 2) * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)))) := by
    funext y; ring
  rw [heq, MeasureTheory.integral_const_mul]
  have heq2 : (fun y : ι → ℝ ↦
      ((y i + y j) ^ 2 - y i ^ 2 - y j ^ 2) * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)))
      = (fun y : ι → ℝ ↦
          (y i + y j) ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) -
            y i ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) -
              y j ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := by
    funext y; ring
  have hIijMinusI : Integrable (fun y : ι → ℝ ↦
      (y i + y j) ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)) -
        y i ^ 2 * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y))) := hIij.sub hIi
  rw [heq2, MeasureTheory.integral_sub hIijMinusI hIj, MeasureTheory.integral_sub hIij hIi,
    hMij, hMi, hMj]
  ring

/-- **The covariance of the multivariate Gaussian density measure.** For `A` positive definite,
the pair `(i, j)` of coordinates of a `multivariateGaussianPi A m`-distributed vector has
covariance `A⁻¹ i j`: translate by `m` (as in `integral_eval_multivariateGaussianPi`) and use
`integral_eval_mul_eval_exp_neg_half_dotProduct_mulVec`. -/
theorem integral_sub_mul_sub_multivariateGaussianPi {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (m : ι → ℝ) (i j : ι) :
    ∫ x, (x i - m i) * (x j - m j) ∂(multivariateGaussianPi A m) = A⁻¹ i j := by
  rw [multivariateGaussianPi,
    integral_withDensity_eq_integral_toReal_smul
      (measurable_multivariateGaussianPDF A m)
      (ae_of_all _ (multivariateGaussianPDF_lt_top A m))]
  simp only [toReal_multivariateGaussianPDF, smul_eq_mul, multivariateGaussianPDFReal]
  have heq : (fun x : ι → ℝ ↦
      Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * ((x i - m i) * (x j - m j)))
      = (fun x : ι → ℝ ↦
          (fun y : ι → ℝ ↦
              Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
                (y i * y j * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)))) (x - m)) := by
    funext x
    change Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))) * ((x i - m i) * (x j - m j))
        = Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
            ((x - m) i * (x - m) j * Real.exp (-(1 / 2) * ((x - m) ⬝ᵥ A *ᵥ (x - m))))
    rw [Pi.sub_apply, Pi.sub_apply]; ring
  rw [heq,
    MeasureTheory.integral_sub_right_eq_self
      (fun y : ι → ℝ ↦ Real.sqrt (A.det / (2 * π) ^ Fintype.card ι) *
        (y i * y j * Real.exp (-(1 / 2) * (y ⬝ᵥ A *ᵥ y)))) m,
    MeasureTheory.integral_const_mul,
    integral_eval_mul_eval_exp_neg_half_dotProduct_mulVec hA i j, ← mul_assoc,
    sqrt_det_div_mul_sqrt_div_det_eq_one hA, one_mul]

end Covariance

section Unique

/-- **The one-dimensional multivariate Gaussian is `gaussianReal`.** For a singleton index type
`ι`, `multivariateGaussianPi A m` (precision `A`, mean `m`) is the image of
`gaussianReal (m default) (A default default)⁻¹` under `x ↦ (fun _ ↦ x)`, provided
`0 < A default default`. -/
theorem multivariateGaussianPi_unique {ι : Type*} [Fintype ι] [DecidableEq ι] [Unique ι]
    {A : Matrix ι ι ℝ} (hA : 0 < A default default) (m : ι → ℝ) :
    multivariateGaussianPi A m =
      (gaussianReal (m default) (Real.toNNReal (A default default)⁻¹)).map
        (MeasurableEquiv.funUnique ι ℝ).symm := by
  have hv : Real.toNNReal (A default default)⁻¹ ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact inv_pos.2 hA
  have hpdf : gaussianPDF (m default) (Real.toNNReal (A default default)⁻¹) =
      fun x ↦ multivariateGaussianPDF A m ((MeasurableEquiv.funUnique ι ℝ).symm x) := by
    funext x
    rw [gaussianPDF, multivariateGaussianPDF, gaussianPDFReal, multivariateGaussianPDFReal]
    congr 1
    simp only [Matrix.det_unique, Fintype.card_unique, pow_one, dotProduct, Matrix.mulVec,
      Fintype.sum_unique, Pi.sub_apply, MeasurableEquiv.funUnique_symm_apply, uniqueElim_default,
      Real.coe_toNNReal _ (inv_pos.2 hA).le]
    have hA0 : A default default ≠ 0 := hA.ne'
    rw [show (2 * Real.pi * (A default default)⁻¹) = (A default default / (2 * Real.pi))⁻¹ by
        field_simp, Real.sqrt_inv, inv_inv]
    congr 1
    field_simp
  rw [gaussianReal_of_var_ne_zero _ hv, multivariateGaussianPi, hpdf,
    map_withDensity_comp volume (MeasurableEquiv.funUnique ι ℝ).symm.measurable
      (measurable_multivariateGaussianPDF A m),
    ((volume_preserving_funUnique ι ℝ).symm (MeasurableEquiv.funUnique ι ℝ)).map_eq]
  congr
  exact Subsingleton.elim _ _

end Unique

end ProbabilityTheory

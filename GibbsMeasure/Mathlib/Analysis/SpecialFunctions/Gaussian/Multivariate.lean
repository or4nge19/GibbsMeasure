/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The `n`-dimensional Gaussian integral

For a positive definite real matrix `A` indexed by a finite type `ι` and `b : ι → ℝ`, this file
proves
```
∫ x, exp (-(1/2) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x) ∂volume
    = √((2 * π) ^ card ι / A.det) * exp ((1/2) * (b ⬝ᵥ A⁻¹ *ᵥ b))
```
on `ι → ℝ` with the product Lebesgue measure. Mathlib has the one-dimensional case
(`integral_gaussian` in `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`) and the
multivariate Gaussian *measure* `ProbabilityTheory.multivariateGaussian`
(`Mathlib.Probability.Distributions.Gaussian.Multivariate`), the latter defined as a pushforward
of the standard Gaussian rather than by its Lebesgue density; neither of those files contains the
density-side integral identity proved here.

## Main results

* `Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec`: the case `b = 0`.
* `Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct`: the general formula.
* `Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct`: the integrand is
  integrable (a corollary of the value formula: a nonneg function whose Bochner integral is
  nonzero is integrable, since a non-integrable function's Bochner integral is `0` by
  convention).

## Proof outline

`A` is Hermitian (being positive definite), so the spectral theorem
(`Matrix.IsHermitian.spectral_theorem`) diagonalizes it as `A = U * D * star U` with `U` in the
unitary group and `D` the diagonal matrix of eigenvalues. Since real matrices have trivial star,
`star U = Uᵀ` and unitarity reads `Uᵀ * U = 1`, i.e. `U` is orthogonal. Multiplication by an
orthogonal matrix has determinant `±1`, hence preserves the Lebesgue measure on `ι → ℝ`
(`map_linearMap_addHaar_eq_smul_addHaar`); changing variables along it turns the quadratic form
into `y ↦ y ⬝ᵥ D *ᵥ y = ∑ i, d i * y i ^ 2`, and Fubini
(`MeasureTheory.integral_fintype_prod_eq_prod`) reduces the integral to a product of
one-dimensional Gaussian integrals, computed by `integral_gaussian`. The case `b ≠ 0` follows by
completing the square and using translation invariance of Lebesgue measure
(`MeasureTheory.integral_sub_right_eq_self`).
-/

@[expose] public section

open MeasureTheory Measure Matrix Real

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication by a matrix in the unitary group (for `ℝ`: the orthogonal group) preserves
the product Lebesgue measure on `ι → ℝ`, since its determinant has absolute value `1`. -/
theorem Matrix.measurePreserving_toLin'_of_mem_unitaryGroup {U : Matrix ι ι ℝ}
    (hU : U ∈ Matrix.unitaryGroup ι ℝ) :
    MeasurePreserving (Matrix.toLin' U) (volume : Measure (ι → ℝ)) volume := by
  have hstar : (star U).det = U.det := by
    rw [star_eq_conjTranspose, det_conjTranspose]; simp
  have hdet1 : U.det * U.det = 1 := by
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff.mp hU)
    rwa [Matrix.det_mul, hstar, Matrix.det_one] at this
  have hdetne : LinearMap.det (Matrix.toLin' U) ≠ 0 := by
    rw [LinearMap.det_toLin']; intro h; rw [h] at hdet1; norm_num at hdet1
  have habs : |LinearMap.det (Matrix.toLin' U)| = 1 := by
    rw [LinearMap.det_toLin', abs_eq (by norm_num : (0 : ℝ) ≤ 1)]
    exact mul_self_eq_one_iff.mp hdet1
  refine ⟨(Matrix.toLin' U).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [map_linearMap_addHaar_eq_smul_addHaar volume hdetne, abs_inv, habs]; simp

/-- Multiplication by a matrix in the unitary group is a measurable embedding of `ι → ℝ`. -/
theorem Matrix.measurableEmbedding_toLin'_of_mem_unitaryGroup (U : Matrix.unitaryGroup ι ℝ) :
    MeasurableEmbedding (Matrix.toLin' (U : Matrix ι ι ℝ)) := by
  have hcont : Continuous (Matrix.UnitaryGroup.toLinearEquiv U) :=
    (Matrix.toLin' (U : Matrix ι ι ℝ)).continuous_of_finiteDimensional
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
    (Matrix.UnitaryGroup.toLinearEquiv U).toContinuousLinearEquivOfContinuous hcont
  have he : (e : (ι → ℝ) → (ι → ℝ)) = Matrix.toLin' (U : Matrix ι ι ℝ) := rfl
  rw [← he]
  exact e.toHomeomorph.toMeasurableEquiv.measurableEmbedding

namespace Matrix.PosDef

variable {A : Matrix ι ι ℝ}

/-- **The `n`-dimensional Gaussian integral**, homogeneous case. For a positive definite real
matrix `A`,
`∫ x, exp (-(1/2) * (x ⬝ᵥ A *ᵥ x)) ∂volume = √((2 * π) ^ card ι / A.det)`
on `ι → ℝ` with the product Lebesgue measure. -/
theorem integral_exp_neg_half_dotProduct_mulVec (hA : A.PosDef) :
    ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x)) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) := by
  set d := hA.isHermitian.eigenvalues with hd
  set Uu := hA.isHermitian.eigenvectorUnitary with hUu
  set U := (Uu : Matrix ι ι ℝ) with hUdef
  have hUmem : U ∈ Matrix.unitaryGroup ι ℝ := Uu.2
  have hUtr : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hUU : Uᵀ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hUmem
    rwa [hUtr] at this
  have hAeq : A = U * diagonal d * Uᵀ := by
    have hspec := hA.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, hUtr] at hspec
    simpa [Function.comp] using hspec
  have hdet : A.det = ∏ i, d i := by
    have := hA.isHermitian.det_eq_prod_eigenvalues (𝕜 := ℝ)
    simpa using this
  have hmp : MeasurePreserving (Matrix.toLin' U) (volume : Measure (ι → ℝ)) volume :=
    Matrix.measurePreserving_toLin'_of_mem_unitaryGroup hUmem
  have hme : MeasurableEmbedding (Matrix.toLin' U) :=
    Matrix.measurableEmbedding_toLin'_of_mem_unitaryGroup Uu
  rw [← hmp.integral_comp hme]
  have hquad : ∀ y : ι → ℝ,
      (Matrix.toLin' U y) ⬝ᵥ A *ᵥ (Matrix.toLin' U y) = y ⬝ᵥ (diagonal d *ᵥ y) := by
    intro y
    show (U *ᵥ y) ⬝ᵥ A *ᵥ (U *ᵥ y) = y ⬝ᵥ (diagonal d *ᵥ y)
    rw [hAeq, mulVec_mulVec, Matrix.mul_assoc (U * diagonal d) Uᵀ U, hUU, Matrix.mul_one,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_mulVec, hUU, vecMul_one]
  simp_rw [hquad]
  have hdiag : ∀ y : ι → ℝ, y ⬝ᵥ (diagonal d *ᵥ y) = ∑ i, d i * (y i) ^ 2 := by
    intro y
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mulVec_diagonal]; ring
  simp_rw [hdiag]
  have hstep : ∀ y : ι → ℝ, Real.exp (-(1 / 2) * ∑ i, d i * (y i) ^ 2) =
      ∏ i, Real.exp (-(1 / 2) * d i * (y i) ^ 2) := by
    intro y
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => by ring_nf
  simp_rw [hstep]
  rw [show (volume : Measure (ι → ℝ)) = Measure.pi (fun _ : ι => (volume : Measure ℝ)) from rfl,
    MeasureTheory.integral_fintype_prod_eq_prod
      (fun i (t : ℝ) => Real.exp (-(1 / 2) * d i * t ^ 2))]
  have hind : ∀ i, ∫ t : ℝ, Real.exp (-(1 / 2) * d i * t ^ 2) = Real.sqrt (2 * π / d i) := by
    intro i
    have hg := integral_gaussian (d i / 2)
    have heq : ∀ t : ℝ, -(d i / 2) * t ^ 2 = -(1 / 2) * d i * t ^ 2 := by intro t; ring
    simp_rw [heq] at hg
    rw [hg]; congr 1; field_simp
  simp_rw [hind]
  have hdpos : ∀ i, 0 < d i := fun i => hA.eigenvalues_pos i
  rw [← Real.sqrt_prod Finset.univ (fun i _ => (div_nonneg (by positivity) (hdpos i).le))]
  congr 1
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hdet]

/-- Completing the square: for `A` positive definite (in particular symmetric and invertible),
`-(1/2) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x`
`  = -(1/2) * ((x - A⁻¹*ᵥb) ⬝ᵥ A *ᵥ (x - A⁻¹*ᵥb)) + (1/2)*(b⬝ᵥA⁻¹*ᵥb)`. -/
theorem neg_half_dotProduct_mulVec_add_dotProduct_eq (hA : A.PosDef) (b x : ι → ℝ) :
    -(1 / 2 : ℝ) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x =
      -(1 / 2 : ℝ) * ((x - A⁻¹ *ᵥ b) ⬝ᵥ A *ᵥ (x - A⁻¹ *ᵥ b)) + (1 / 2 : ℝ) * (b ⬝ᵥ A⁻¹ *ᵥ b) := by
  have hAsym : Aᵀ = A := by
    have hh : Aᴴ = A := hA.isHermitian
    rwa [conjTranspose_eq_transpose_of_trivial] at hh
  have hAinv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (hA.det_pos.ne').isUnit
  set c := A⁻¹ *ᵥ b with hc
  have hAc : A *ᵥ c = b := by rw [hc, mulVec_mulVec, hAinv, one_mulVec]
  have hsymm : ∀ u v : ι → ℝ, u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
    intro u v
    have := dotProduct_transpose_mulVec A u v
    rwa [hAsym] at this
  have hexp : (x - c) ⬝ᵥ A *ᵥ (x - c) = x ⬝ᵥ A *ᵥ x - b ⬝ᵥ x - b ⬝ᵥ x + b ⬝ᵥ c := by
    simp only [mulVec_sub, sub_dotProduct, dotProduct_sub]
    have h1 : x ⬝ᵥ (A *ᵥ c) = b ⬝ᵥ x := by rw [hAc, dotProduct_comm]
    have h2 : c ⬝ᵥ (A *ᵥ x) = b ⬝ᵥ x := by rw [hsymm]; exact h1
    have h3 : c ⬝ᵥ (A *ᵥ c) = b ⬝ᵥ c := by rw [hAc, dotProduct_comm]
    rw [h1, h2, h3]; ring
  rw [hexp, hc]; ring

/-- **The `n`-dimensional Gaussian integral**. For a positive definite real matrix `A` and
`b : ι → ℝ`,
`∫ x, exp (-(1/2) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x) ∂volume
    = √((2 * π) ^ card ι / A.det) * exp ((1/2) * (b ⬝ᵥ A⁻¹ *ᵥ b))`
on `ι → ℝ` with the product Lebesgue measure. -/
theorem integral_exp_neg_half_dotProduct_mulVec_add_dotProduct (hA : A.PosDef) (b : ι → ℝ) :
    ∫ x : ι → ℝ, Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x) =
      Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) * Real.exp ((1 / 2) * (b ⬝ᵥ A⁻¹ *ᵥ b)) := by
  simp_rw [neg_half_dotProduct_mulVec_add_dotProduct_eq hA b]
  simp_rw [Real.exp_add]
  rw [MeasureTheory.integral_mul_const,
    MeasureTheory.integral_sub_right_eq_self
      (fun x : ι → ℝ => Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x))) (A⁻¹ *ᵥ b),
    integral_exp_neg_half_dotProduct_mulVec hA]

/-- The integrand of `integral_exp_neg_half_dotProduct_mulVec_add_dotProduct` is integrable: a
nonnegative function whose Bochner integral is nonzero must be integrable, since a
non-integrable function's Bochner integral is `0` by convention. -/
theorem integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct (hA : A.PosDef) (b : ι → ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (-(1 / 2) * (x ⬝ᵥ A *ᵥ x) + b ⬝ᵥ x)) := by
  by_contra h
  have hz := MeasureTheory.integral_undef h
  rw [integral_exp_neg_half_dotProduct_mulVec_add_dotProduct hA b] at hz
  have hApos : 0 < A.det := hA.det_pos
  have hcard : 0 < (2 * π) ^ Fintype.card ι := by positivity
  have hpos :
      0 < Real.sqrt ((2 * π) ^ Fintype.card ι / A.det) * Real.exp ((1 / 2) * (b ⬝ᵥ A⁻¹ *ᵥ b)) := by
    have : 0 < (2 * π) ^ Fintype.card ι / A.det := div_pos hcard hApos
    positivity
  exact absurd hz hpos.ne'

end Matrix.PosDef

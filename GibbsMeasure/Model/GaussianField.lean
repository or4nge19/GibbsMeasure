/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Potential.Pair
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import GibbsMeasure.Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Georgii §13.1: Gauss fields as Gibbs measures

`E = ℝ`, `λ` = Lebesgue measure, `S` an arbitrary countable set. This file identifies Georgii's
Definition (13.1) with Mathlib's `ProbabilityTheory.IsGaussianProcess`, records that the
covariance function of a Gaussian field is always nonnegative definite (13.3), proves the
Fourier-analytic restatement (13.2) of (13.1), and formalizes the Gaussian pair potential
`Φ^{J,h}` of (13.11)/(13.12) as a `Potential S ℝ`.

## General lemma missing from Mathlib

* `ProbabilityTheory.covariance_sum_smul_sum_smul`: the bilinear expansion
  `cov[∑ᵢ aᵢ • Xᵢ, ∑ⱼ bⱼ • Xⱼ] = ∑ᵢ∑ⱼ aᵢ bⱼ cov[Xᵢ, Xⱼ]` of the covariance of two finite linear
  combinations of an `L²` family. Intended home: `Mathlib/Probability/Moments/Covariance.lean`,
  next to `covariance_sum_left'`/`covariance_sum_right'`.
* `Matrix.posSemidef_covariance`: the covariance "matrix" `(i, j) ↦ cov[Xᵢ, Xⱼ; μ]` of an
  arbitrary (possibly infinite) `L²` family is `Matrix.PosSemidef`. Intended home: the same file,
  or a new `Mathlib/Probability/Moments/CovarianceMatrix.lean`. `Matrix.PosSemidef`/`Matrix.PosDef`
  are already stated over `n →₀ R` (finitely supported coefficients), so no `Fintype`/`Finset`
  bookkeeping is needed to match Georgii's (13.3), which is exactly the finitely-supported
  condition.

## Main definitions

* Georgii Definition (13.1) is **not** re-defined: a Gaussian field on `(S → ℝ, ℰ^S)` is
  `ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ`, i.e. all finite-dimensional
  marginals `σ_Λ(μ)` are Gaussian (`ProbabilityTheory.IsGaussianProcess.hasGaussianLaw`). The mean
  `m` and covariance function `C` of (13.1) are literally `μ[fun ω ↦ ω i]` and
  `cov[fun ω ↦ ω i, fun ω ↦ ω j; μ]`.
* `Potential.site`: the single-site half of a potential, `Φ_{\{i\}} = f i (η i)`, `Φ_A = 0`
  otherwise — the counterpart of `Potential.pairTerms` for singletons, needed because Georgii's
  (13.11) is a one-body term plus the pair term `Potential.pair`.
* `Potential.gaussianPotential J h`: **Georgii (13.11)**, the potential
  `Φ^{J,h}_{\{i\}} = J(i,i)/2 · σ_i² + h_i σ_i`, `Φ^{J,h}_{\{i,j\}} = J(i,j) σ_i σ_j` (`i ≠ j`),
  `Φ^{J,h}_A = 0` otherwise.
* `Potential.gaussianCovMatrix J Λ`: **Georgii (13.12)**, the matrix `𝒥_Λ = (J(i,j))_{i,j ∈ Λ}`.

## Main results

* `MeasureTheory.GibbsMeasure.posSemidef_covar_of_isGaussianProcess`: **Georgii (13.3)** (the
  "well-known and easily seen" fact preceding Proposition (13.7)) — the covariance function of a
  Gaussian field is nonnegative definite.
* `MeasureTheory.GibbsMeasure.integral_cexp_I_sum_eq_of_isGaussianProcess`: **Georgii (13.2)** —
  the characteristic function of a Gaussian field factors through its mean and covariance
  function, for every finite `Λ ⊆ S` and every `t : S → ℝ`. Proved from Mathlib's
  `HasGaussianLaw.charFunDual_map_eq_fun` applied to the joint law of `(σ_i)_{i ∈ Λ}` and the
  linear functional `ζ ↦ ∑_{i ∈ Λ} t_i ζ_i`, together with
  `ProbabilityTheory.covariance_sum_smul_sum_smul` above for the variance term.
* `Potential.isPotential_gaussianPotential`: `Φ^{J,h}` satisfies Georgii (2.2)(i) unconditionally
  (each `Φ_A` is a polynomial in finitely many coordinates, hence measurable), for *arbitrary*
  `J : S → S → ℝ` and `h : S → ℝ`, including infinite range.

## What is not in this file, and why

* **Propositions (13.7) and Lemma (13.10)**, i.e. items (13.4)–(13.10), identify the conditional
  expectation `ξ_i^μ = μ(σ_i | 𝒯_{\{i\}})` and show it is affine in finitely many coordinates. This
  needs regular conditional distributions / conditional expectation machinery for the tail
  σ-algebra `𝒯_{\{i\}}` (`cylinderEvents ({i} : Set S)ᶜ`) that is not built anywhere in this tree
  (`GibbsMeasure/Topology/LocalConvergence.lean` has the σ-algebra but no conditional expectation
  theory over it). This is a genuine gap, not a missing tail-gluing step.
* **Proposition (13.13)**'s two-sided conclusion (`Z_Λ^{J,h}(ω) < ∞ ↔ 𝒥_Λ` positive definite, and
  in that case `γ_Λ^{J,h}(·|ω)` **is** `multivariateGaussian` with the stated mean and covariance
  `𝒥_Λ⁻¹`) needs a genuine *n*-dimensional Gaussian integral fact that Mathlib does not yet have:
  `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean` only proves the
  **one-dimensional** `∫ x, exp (-b x^2) = √(π/b)`, and
  `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` defines `multivariateGaussian` by
  pushing `stdGaussian` forward along `CFC.sqrt S`, with no Lebesgue density formula. Proving
  (13.13) honestly requires first proving, for a positive definite `Matrix.PosDef` quadratic form,
  either (a) the Lebesgue density of `multivariateGaussian` on `EuclideanSpace ℝ ι`, or (b) the
  finiteness/value of `∫ x, exp (-⟪x, A x⟫/2 - ⟪b, x⟫) dvolume` directly (diagonalize `A` by an
  orthogonal change of variables — Lebesgue-measure-preserving via
  `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`/`Matrix.IsHermitian` spectral data —
  then apply the one-dimensional Gaussian integral in each eigen-coordinate via Fubini). Neither is
  in Mathlib. This is the blocking general lemma for (13.13)–(13.22); (13.18)'s tail-event gluing
  (`Ω_J` is `𝒯`-measurable, `GibbsMeasure/Specification/GluedFamily.lean`) is a *further*, separate
  step needed only after (13.13) is available, to handle infinite-range `J` (`Ω_J ≠ Ω`).
  `Potential.gaussianPotential` and `Potential.gaussianCovMatrix` are exactly the ingredients
  (13.13) would be stated with once that integral fact exists.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal NNReal

noncomputable section

/-! ### Georgii (13.1): a Gauss field is `IsGaussianProcess` for the coordinate process -/

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} {mΩ : MeasurableSpace (S → ℝ)} {μ : Measure (S → ℝ)}

/-- **Georgii (13.3)**, specialized to a Gaussian field: the covariance function
`C(i, j) = cov[σ_i, σ_j; μ]` of a Gaussian field is nonnegative definite. This is the "well-known
and easily seen" fact preceding Proposition (13.7), obtained from
`Matrix.posSemidef_covariance` and the fact that a Gaussian random variable is in `L²`
(`ProbabilityTheory.HasGaussianLaw.memLp_two`). -/
theorem posSemidef_covar_of_isGaussianProcess
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ) :
    Matrix.PosSemidef
      (fun i j ↦ cov[fun ω ↦ ω i, fun ω ↦ ω j; μ] : Matrix S S ℝ) :=
  haveI := hμ.isProbabilityMeasure
  Matrix.posSemidef_covariance fun i ↦ (hμ.hasGaussianLaw_eval i).memLp_two

/-- **Georgii (13.2)**, the Fourier-analytic restatement of Definition (13.1): for a Gaussian
field `μ` with mean `m i = μ[σ_i]` and covariance function `C(i, j) = cov[σ_i, σ_j; μ]`,
`μ(exp[i ∑_{i ∈ Λ} t_i σ_i]) = exp[-1/2 ∑_{i,j ∈ Λ} t_i C(i, j) t_j + i ∑_{i ∈ Λ} t_i m_i]`
for every finite `Λ ⊆ S` and every `t : S → ℝ` (Georgii's "finitely supported real sequence
`(t_i)_{i ∈ S}`" is realized here, without loss of generality, as an arbitrary `t : S → ℝ`
together with a finite `Λ` containing its support). The proof reduces to Mathlib's
`ProbabilityTheory.HasGaussianLaw.charFunDual_map_eq_fun`, applied to the joint law of
`(σ_i)_{i ∈ Λ}` (`IsGaussianProcess.hasGaussianLaw`) and the linear functional
`ζ ↦ ∑_{i ∈ Λ} t_i ζ_i`; the variance of `∑_{i ∈ Λ} t_i σ_i` is expanded via
`ProbabilityTheory.covariance_sum_smul_sum_smul` above. -/
theorem integral_cexp_I_sum_eq_of_isGaussianProcess
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
    (Λ : Finset S) (t : S → ℝ) :
    ∫ ω, Complex.exp (Complex.I * ∑ i ∈ Λ, (t i : ℂ) * ω i) ∂μ =
      Complex.exp (-(1 / 2 : ℂ) * ∑ i ∈ Λ, ∑ j ∈ Λ, (t i : ℂ) *
          ((cov[fun ω ↦ ω i, fun ω ↦ ω j; μ] : ℝ) : ℂ) * (t j : ℂ) +
        Complex.I * ∑ i ∈ Λ, (t i : ℂ) * ((μ[fun ω ↦ ω i] : ℝ) : ℂ)) := by
  classical
  have := hμ.isProbabilityMeasure
  set X : (S → ℝ) → (Λ → ℝ) := fun ω ↦ Λ.restrict ω with hXdef
  have hgauss : ProbabilityTheory.HasGaussianLaw X μ := hμ.hasGaussianLaw Λ
  set L : StrongDual ℝ (Λ → ℝ) :=
    ∑ i : Λ, t i.1 • ContinuousLinearMap.proj (R := ℝ) i with hLdef
  have hcf := hgauss.charFunDual_map_eq_fun L
  have hLapp : ∀ ζ : Λ → ℝ, L ζ = ∑ i : Λ, t i.1 * ζ i := by
    intro ζ
    simp [hLdef]
  have hLX : ∀ ω : S → ℝ, L (X ω) = ∑ i ∈ Λ, t i * ω i := by
    intro ω
    rw [hLapp]
    exact Finset.sum_coe_sort Λ (fun i ↦ t i * ω i)
  have hLHS : charFunDual (Measure.map X μ) L =
      ∫ ω, Complex.exp (Complex.I * ∑ i ∈ Λ, (t i : ℂ) * ω i) ∂μ := by
    rw [charFunDual_apply, integral_map hgauss.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp only [hLX]
    congr 1
    push_cast
    ring
  have hLX2 : ProbabilityTheory.HasGaussianLaw (fun ω ↦ L (X ω)) μ :=
    hgauss.map_of_measurable L L.continuous.measurable
  have hmean : ∫ ω, L (X ω) ∂μ = ∑ i ∈ Λ, t i * μ[fun ω ↦ ω i] := by
    have hint : ∀ i ∈ Λ, Integrable (fun ω : S → ℝ ↦ t i * ω i) μ :=
      fun i _ ↦ ((hμ.hasGaussianLaw_eval i).memLp_two.integrable (by norm_num)).const_mul _
    calc ∫ ω, L (X ω) ∂μ = ∫ ω, ∑ i ∈ Λ, t i * ω i ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall hLX)
      _ = ∑ i ∈ Λ, ∫ ω, t i * ω i ∂μ := integral_finsetSum Λ hint
      _ = ∑ i ∈ Λ, t i * μ[fun ω ↦ ω i] := by
          simp [integral_const_mul]
  have hVar : Var[fun ω ↦ L (X ω); μ] =
      ∑ i ∈ Λ, ∑ j ∈ Λ, t i * t j * cov[fun ω ↦ ω i, fun ω ↦ ω j; μ] := by
    rw [(covariance_self hLX2.memLp_two.aestronglyMeasurable.aemeasurable).symm]
    have hcongr : (fun ω ↦ L (X ω)) = ∑ i ∈ Λ, t i • (fun ω : S → ℝ ↦ ω i) := by
      funext ω
      simp [hLX ω, smul_eq_mul]
    rw [hcongr]
    exact covariance_sum_smul_sum_smul (fun i _ ↦ (hμ.hasGaussianLaw_eval i).memLp_two) t t
  rw [← hLHS, hcf, hmean, hVar]
  have hBeq : ∑ i ∈ Λ, ∑ j ∈ Λ, t i * t j * cov[fun ω ↦ ω i, fun ω ↦ ω j; μ] =
      ∑ i ∈ Λ, ∑ j ∈ Λ, t i * cov[fun ω ↦ ω i, fun ω ↦ ω j; μ] * t j :=
    Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hBeq]
  congr 1
  push_cast
  ring

end MeasureTheory.GibbsMeasure

/-! ### Georgii (13.11)/(13.12): the Gaussian pair potential `Φ^{J,h}` -/

namespace Potential

variable {S E : Type*} [MeasurableSpace E] [LinearOrder S]

section SiteTerms

variable {α : Type*} [AddCommMonoid α]

/-- The family `A ↦ f i` if `A = {i}`, and `0` otherwise, written as a `Finset.sum` so that it is
manifestly measurable in any parameters of `f`. The single-site counterpart of
`Potential.pairTerms`. -/
def siteTerms (f : S → α) (A : Finset S) : α :=
  ∑ i ∈ A, if A = {i} then f i else 0

variable {f g : S → α}

lemma siteTerms_singleton (i : S) : siteTerms f {i} = f i := by simp [siteTerms]

lemma siteTerms_eq_zero {A : Finset S} (hA : ∀ i, A ≠ {i}) : siteTerms f A = 0 :=
  Finset.sum_eq_zero fun i _ ↦ ite_eq_right (hA i)

end SiteTerms

/-- **The single-site half of a potential**: `Φ_{\{i\}} = f i (η i)`, and `Φ_A = 0` for every
other `A`. The counterpart of `Potential.pair` for singletons, needed because Georgii's (13.11)
is a one-body term (site) plus a pair term. -/
def site (f : S → E → ℝ) : Potential S E := fun A η ↦ siteTerms (fun i ↦ f i (η i)) A

variable {f : S → E → ℝ}

lemma site_apply (A : Finset S) (η : S → E) : site f A η = siteTerms (fun i ↦ f i (η i)) A := rfl

lemma site_singleton (i : S) (η : S → E) : site f {i} η = f i (η i) :=
  siteTerms_singleton i

lemma site_eq_zero {A : Finset S} (hA : ∀ i, A ≠ {i}) : site f A = 0 :=
  funext fun _ ↦ siteTerms_eq_zero hA

/-- A single-site potential with measurable `f i` is a potential in the sense of Georgii
(2.2)(i). -/
lemma isPotential_site (hf : ∀ i, Measurable (f i)) : IsPotential (site f) where
  measurable A := by
    unfold site siteTerms
    refine Finset.measurable_sum _ fun i hi ↦ ?_
    by_cases hA : A = {i}
    · simp only [ite_eq_left hA]
      exact (hf i).comp (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Finset.mem_coe.2 hi))
    · simp only [ite_eq_right hA]
      exact measurable_const

variable (J : S → S → ℝ) (h : S → ℝ)

/-- **Georgii (13.11).** The Gaussian pair potential
`Φ^{J,h}_{\{i\}} = J(i,i)/2 · σ_i² + h_i σ_i`, `Φ^{J,h}_{\{i,j\}} = J(i,j) σ_i σ_j` (`i ≠ j`), and
`Φ^{J,h}_A = 0` for every other `A`. No positive-definiteness or finite-range hypothesis on `J` is
needed for the definition; `J` positive definite is needed only to make `Φ^{J,h}` λ-admissible
(Proposition (13.13)). -/
def gaussianPotential : Potential S ℝ :=
  site (fun i x ↦ J i i / 2 * x ^ 2 + h i * x) + pair (fun i j x y ↦ J i j * x * y)

/-- A singleton and a pair are never equal, by cardinality. -/
private lemma singleton_ne_pair {i j k : S} (hij : i ≠ j) : ({k} : Finset S) ≠ {i, j} := by
  intro hEq
  have h1 : ({k} : Finset S).card = 1 := Finset.card_singleton k
  have h2 : ({i, j} : Finset S).card = 2 := Finset.card_pair hij
  rw [hEq, h2] at h1
  omega

lemma gaussianPotential_apply_singleton (i : S) (η : S → ℝ) :
    gaussianPotential J h {i} η = J i i / 2 * η i ^ 2 + h i * η i := by
  have hpair : (pair (fun i j x y ↦ J i j * x * y) : Potential S ℝ) {i} η = 0 :=
    congrFun (pair_eq_zero (φ := fun i j x y ↦ J i j * x * y)
      fun a b hab ↦ singleton_ne_pair hab.ne) η
  simp [gaussianPotential, add_apply, site_singleton, hpair]

lemma gaussianPotential_apply_pair {i j : S} (hij : i < j) (η : S → ℝ) :
    gaussianPotential J h {i, j} η = J i j * η i * η j := by
  have hsite : (site (fun i x ↦ J i i / 2 * x ^ 2 + h i * x) : Potential S ℝ) {i, j} η = 0 :=
    congrFun (site_eq_zero fun k ↦ (singleton_ne_pair hij.ne).symm) η
  simp [gaussianPotential, add_apply, hsite, pair_pair (fun i j x y ↦ J i j * x * y) hij]

lemma gaussianPotential_eq_zero {A : Finset S} (hA1 : ∀ i, A ≠ {i})
    (hA2 : ∀ i j, i < j → A ≠ {i, j}) (η : S → ℝ) :
    gaussianPotential J h A η = 0 := by
  simp [gaussianPotential, add_apply, congrFun (site_eq_zero hA1) η,
    congrFun (pair_eq_zero (φ := fun i j x y ↦ J i j * x * y) hA2) η]

/-- **Georgii (2.2)(i) for `Φ^{J,h}`, unconditionally.** Every interaction term of `Φ^{J,h}` is a
polynomial in finitely many coordinates, hence measurable, for *arbitrary* `J : S → S → ℝ` and
`h : S → ℝ`, including infinite range. (Only λ-admissibility, Proposition (13.13), needs `J`
positive definite.) -/
theorem isPotential_gaussianPotential : IsPotential (gaussianPotential J h) := by
  have hsite : IsPotential (site (fun i x ↦ J i i / 2 * x ^ 2 + h i * x) : Potential S ℝ) :=
    isPotential_site fun i ↦ by fun_prop
  have hpair : IsPotential (pair (fun i j x y ↦ J i j * x * y) : Potential S ℝ) :=
    isPotential_pair (φ := fun i j x y ↦ J i j * x * y) fun i j ↦ by fun_prop
  have := hsite
  have := hpair
  rw [gaussianPotential]
  infer_instance

omit [LinearOrder S] in
/-- **Georgii (13.12).** The finite-volume interaction matrix `𝒥_Λ = (J(i,j))_{i,j ∈ Λ}`. -/
def gaussianCovMatrix (Λ : Finset S) : Matrix Λ Λ ℝ := fun i j ↦ J i.1 j.1

omit [LinearOrder S] in
lemma gaussianCovMatrix_apply (Λ : Finset S) (i j : Λ) :
    gaussianCovMatrix J Λ i j = J i.1 j.1 := rfl

end Potential

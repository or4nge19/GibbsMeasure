/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Potential.Pair
public import GibbsMeasure.Potential.Site
public import GibbsMeasure.Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import GibbsMeasure.Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Density
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.CondExp
public import Mathlib.Analysis.Matrix.Order

/-!
# Georgii §13.1: Gauss fields as Gibbs measures

`E = ℝ`, `λ` = Lebesgue measure, `S` an arbitrary countable set. This file identifies Georgii's
Definition (13.1) with Mathlib's `ProbabilityTheory.IsGaussianProcess`, records that the
covariance function of a Gaussian field is always nonnegative definite (13.3), proves the
Fourier-analytic restatement (13.2) of (13.1), formalizes the Gaussian pair potential `Φ^{J,h}` of
(13.11)/(13.12) as a `Potential S ℝ`, computes its finite-volume Hamiltonian as a quadratic form,
proves λ-admissibility, and identifies the resulting finite-volume Gibbs specification with the
multivariate Gaussian distribution (13.13) — for `J` symmetric with finite row support (Georgii's
finite-range case (2.15); his Chapter 13 also allows a genuinely infinite-range `J` under a
convergence condition, not treated here).

## General lemmas used here, proved in the Mathlib layer

* `ProbabilityTheory.covariance_sum_smul_sum_smul` and `Matrix.posSemidef_covariance`
  (`GibbsMeasure/Mathlib/Probability/Moments/Covariance.lean`): the bilinear expansion
  `cov[∑ᵢ aᵢ • Xᵢ, ∑ⱼ bⱼ • Xⱼ] = ∑ᵢ∑ⱼ aᵢ bⱼ cov[Xᵢ, Xⱼ]`, and the fact that the covariance
  "matrix" `(i, j) ↦ cov[Xᵢ, Xⱼ; μ]` of an arbitrary (possibly infinite) `L²` family is
  `Matrix.PosSemidef`. `Matrix.PosSemidef`/`Matrix.PosDef` are stated over `n →₀ R` (finitely
  supported coefficients), which is exactly Georgii's (13.3).
* `Finset.sum_sum_eq_sum_diag_add_two_nsmul_sum_lt`
  (`GibbsMeasure/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean`): the diagonal/off-diagonal
  expansion `∑_{i,j ∈ s} f i j = ∑_{i ∈ s} f i i + 2 ∑_{i < j} f i j` of a symmetric `f`.
* `Potential.site` and its API (`GibbsMeasure/Potential/Site.lean`): the one-body half of a
  potential.

## General lemma missing from `GibbsMeasure/Specification.lean`

* `Specification.sigmaFiniteLambdaFun_juxt_eq`: the σ-finite reference kernel `λ_Λ(·|η)` depends
  on the boundary condition `η` only through `η|_{Λᶜ}` — resampling inside `Λ` first does not
  change it (`GibbsMeasure/Specification.lean`).

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
* `Potential.gaussianBoundaryField J hFin Λ ω i`: `(J_{Λ,Λᶜ} ω)_i = ∑_{j ∉ Λ} J(i,j) ω(j)`.
* `Potential.gaussianMean J h hFin Λ ω`: **the mean of (13.13)**, literally Georgii's display
  `m_Λ(ω) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})`; see its docstring for the derivation by completing
  the square in the Boltzmann factor against `Potential.gaussianPotential`'s `+ h i * x` site term.
* `Potential.gaussianSpecification J h hSymm hFin hPD β hβ`: **Georgii Definition (2.9) for
  `Φ^{J,h}`**, the Gibbsian specification over Lebesgue measure, given `J` symmetric with finite
  row support, every `𝒥_Λ` positive definite, and `β > 0`.

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
* `Potential.isFiniteRange_gaussianPotential`: Georgii (2.15), given `J` symmetric with finite row
  support.
* `Potential.hamiltonian_gaussianPotential_eq`/`hamiltonian_gaussianPotential_juxt_eq`: **the
  finite-volume Hamiltonian as a quadratic form**,
  `H_Λ(ζ_Λ ω_{Λᶜ}) = (1/2)(ζ ⬝ᵥ 𝒥_Λ *ᵥ ζ) + (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ}) ⬝ᵥ ζ`. Every interaction term
  entering `H_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` is a singleton in `Λ`, a pair inside `Λ`, or a pair crossing
  `Λ`'s boundary; there is no further additive constant depending only on `ω|_{Λᶜ}`.
* `Potential.isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor`: **Georgii
  Proposition (13.13), λ-admissibility**, from the *n*-dimensional Gaussian integral
  (`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct`) applied to the rescaled
  precision `β • 𝒥_Λ`.
* `Potential.gaussianSpecification_apply`: **Georgii Proposition (13.13), the main identification**
  — `γ_Λ^{J,h}(·|ω)` is the `juxt`-pushforward of `ProbabilityTheory.multivariateGaussianPi
  (β • 𝒥_Λ) (gaussianMean J h hFin Λ ω)`. Consequently (by
  `ProbabilityTheory.integral_eval_multivariateGaussianPi`/
  `integral_sub_mul_sub_multivariateGaussianPi`), under `γ_Λ^{J,h}(·|ω)` the mean of `σ_i` is
  `(gaussianMean J h hFin Λ ω) i` and the covariance of `(σ_i, σ_j)` is `(β • 𝒥_Λ)⁻¹ i j`.

## Georgii (13.4)–(13.7): conditional expectations given the other spins

* `MeasureTheory.GibbsMeasure.condExpOutside μ i`: **Georgii (13.4)**, `ξ_i^μ = μ(σ_i | 𝒯_{\{i\}})`,
  literally Mathlib's `μ[σ_i | cylinderEvents {i}ᶜ]`.
* `MeasureTheory.GibbsMeasure.condCovariance μ i j`: **Georgii (13.6)**, the conditional
  covariance function `Γ(i, j) = μ((σ_i - ξ_i^μ)(σ_j - ξ_j^μ))`; `condCoupling` and
  `condExternalField` are the `J` and `h` of Proposition (13.7).
* `MeasureTheory.GibbsMeasure.exists_condExp_cylinderEvents_eq_affine`: **Georgii (13.A4)** for a
  Gaussian field — the conditional expectation of `σ_i` given finitely many spins is affine in
  them (Gaussian regression, `ProbabilityTheory.IsGaussianProcess.exists_condExp_eq_affine` in
  `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/CondExp.lean`).
* `MeasureTheory.GibbsMeasure.georgii_13_7`: **Georgii Proposition (13.7)**, with its hypotheses
  (i) `Γ(i, i) > 0` and (ii) the Markov property — `ξ_i^μ` has an `𝓕_{∂i}`-measurable version for
  a finite `∂i ∌ i` — exactly as stated: `J` has finite range, `J` is positive definite
  (`Matrix.PosDef (Matrix.of J)`, Georgii's finitely-supported sense (13.3)), and (13.5) holds.
  The tower of lemmas follows Georgii's proof: `condCovariance_eq_zero_of_notMem` (finite range),
  `exists_condExpOutside_ae_eq_affine` (his (13.8)), `sub_condExpOutside_ae_eq_condCoupling`
  ((13.5)), and `posDef_gaussianCovMatrix_condCoupling` (`Γ_Λ` is a right inverse of `𝒥_Λ`).
* **Lemma (13.10)** lives in `GibbsMeasure/Model/GaussianSpecification.lean`
  (`MeasureTheory.GibbsMeasure.georgii_13_10`), next to `Ω_J` (13.9), which its hypothesis (i)
  mentions.

## What is not in this file, and why

* **Proposition (13.13)'s converse direction** (`𝒥_Λ` *not* positive definite `⟹` `Z_Λ^{J,h}(ω) = ∞`
  or the density is not Gaussian) is not proved: only the "if `𝒥_Λ` positive definite, then
  admissible and Gaussian" direction is formalized (matching what a genuinely infinite-range `J`
  under Georgii's convergence condition could still need); the strict biconditional of (13.13) is a
  further step.
* **Infinite range.** `hamiltonian_gaussianPotential_eq` and everything built on it assume `J`
  symmetric with finite row support (Georgii's (2.15) finite-range case), not Georgii's fully
  general Chapter 13 convergence condition on an infinite-range `J`. (13.18)'s tail-event gluing
  (`Ω_J` is `𝒯`-measurable, `GibbsMeasure/Specification/GluedFamily.lean`) is a further, separate
  step needed to handle that generality (`Ω_J ≠ Ω`), independent of what is proved here.
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

/-! ### Georgii §13.1: the finite-volume Hamiltonian as a quadratic form

Georgii's Chapter 13 allows `J` of infinite range subject to a convergence condition; what is
formalized here is the case enough for (13.13): `J` symmetric (`hSymm`, implicit in `𝒥_Λ` being
the matrix entering a *positive definite quadratic form* — `Matrix.PosDef` bundles `IsHermitian`,
i.e. for a real matrix, symmetry) with finite row support (`hFin`, Georgii's finite-range case
(2.15)). -/

section HamiltonianQuadraticForm

variable (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)

/-- **Finite range for `Φ^{J,h}`** (Georgii (2.15)): if `J` is symmetric with finite row support,
every site `i` interacts with only the finitely many `j` with `J i j ≠ 0`. -/
theorem isFiniteRange_gaussianPotential (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) : IsFiniteRange (gaussianPotential J h) where
  exists_finset i := by
    classical
    refine ⟨insert i (hFin i).toFinset, fun A hiA hΦ ↦ ?_⟩
    by_cases h1 : A.card = 1
    · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.mem_singleton] at hiA
      subst hiA
      exact Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)
    · by_cases h2 : ∃ a b : S, a < b ∧ A = ({a, b} : Finset S)
      · obtain ⟨a, b, hab, rfl⟩ := h2
        have hJab : J a b ≠ 0 := fun h0 ↦ hΦ (funext fun η ↦ by
          simp [gaussianPotential_apply_pair J h hab η, h0])
        rw [Finset.mem_insert, Finset.mem_singleton] at hiA
        rw [Finset.insert_subset_iff]
        rcases hiA with rfl | rfl
        · refine ⟨Finset.mem_insert_self _ _, Finset.singleton_subset_iff.2 ?_⟩
          exact Finset.mem_insert_of_mem ((hFin i).mem_toFinset.2 hJab)
        · refine ⟨Finset.mem_insert_of_mem ((hFin i).mem_toFinset.2 ?_),
            Finset.singleton_subset_iff.2 (Finset.mem_insert_self _ _)⟩
          change J i a ≠ 0
          rw [hSymm i a]; exact hJab
      · refine absurd (funext fun η ↦ gaussianPotential_eq_zero J h
          (fun k hk ↦ h1 (by rw [hk]; exact Finset.card_singleton k))
          (fun a b hab hAab ↦ h2 ⟨a, b, hab, hAab⟩) η) hΦ

/-- The contribution to `Φ^{J,h}` of the subsets of `Λ`: the site terms plus the pairwise terms
`J(i,j)η_iη_j` for `i < j` both in `Λ`. -/
private lemma sum_powerset_gaussianPotential (Λ : Finset S) (η : S → ℝ) :
    ∑ A ∈ Λ.powerset, gaussianPotential J h A η =
      ∑ i ∈ Λ, (J i i / 2 * η i ^ 2 + h i * η i) +
        ∑ i ∈ Λ, ∑ j ∈ Λ, (if i < j then J i j * η i * η j else 0) := by
  have hsplit : ∀ A ∈ Λ.powerset, gaussianPotential J h A η =
      siteTerms (fun i ↦ J i i / 2 * η i ^ 2 + h i * η i) A +
        pairTerms (fun i j ↦ J i j * η i * η j) A := fun A _ ↦ by
    simp [gaussianPotential, add_apply, site_apply, pair_apply]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_powerset_siteTerms Λ (fun i ↦ J i i / 2 * η i ^ 2 + h i * η i),
    sum_powerset_pairTerms Λ (fun i j ↦ J i j * η i * η j)]

/-- The finite set of boundary-crossing pairs `{i, j}` with `i ∈ Λ` and `j ∉ Λ` that could carry
a nonzero interaction: `j` ranges over the (finite, by `hFin`) row support of `i`. Each such pair
is counted through its unique element `i ∈ Λ`, so the buckets over `i ∈ Λ` are disjoint. -/
private def gaussianBoundaryPairs (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) :
    Finset (Finset S) :=
  Λ.biUnion (fun i ↦ ((hFin i).toFinset \ Λ).image (fun j ↦ ({i, j} : Finset S)))

private lemma pairwiseDisjoint_gaussianBoundaryPairs
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) :
    (Λ : Set S).PairwiseDisjoint
      (fun i ↦ ((hFin i).toFinset \ Λ).image (fun j ↦ ({i, j} : Finset S))) := by
  intro i hiΛ i' _ hne
  have hiΛ' : i ∈ Λ := Finset.mem_coe.1 hiΛ
  refine Finset.disjoint_left.2 fun Δ hΔ hΔ' ↦ ?_
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hΔ
  obtain ⟨j', hj', hΔ'⟩ := Finset.mem_image.1 hΔ'
  have hj'Λ : j' ∉ Λ := (Finset.mem_sdiff.1 hj').2
  have hii' : i ∈ ({i', j'} : Finset S) := by rw [hΔ']; exact Finset.mem_insert_self i {j}
  rcases Finset.mem_insert.1 hii' with h | h
  · exact hne h
  · exact hj'Λ (Finset.mem_singleton.1 h ▸ hiΛ')

/-- The value of the boundary-crossing sum: `∑_{i ∈ Λ} ∑_{j ∈ (hFin i).toFinset \ Λ} J(i,j) η_i
η_j`. -/
private lemma sum_gaussianBoundaryPairs (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (η : S → ℝ) :
    ∑ Δ ∈ gaussianBoundaryPairs J hFin Λ, gaussianPotential J h Δ η =
      ∑ i ∈ Λ, ∑ j ∈ (hFin i).toFinset \ Λ, J i j * η i * η j := by
  rw [gaussianBoundaryPairs, Finset.sum_biUnion (pairwiseDisjoint_gaussianBoundaryPairs J hFin Λ)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hinj : Set.InjOn (fun j ↦ ({i, j} : Finset S)) ((hFin i).toFinset \ Λ : Finset S) := by
    intro j hj j' hj' hEq
    dsimp only at hEq
    have hjΛ : j ∉ Λ := (Finset.mem_sdiff.1 hj).2
    have hmem : j ∈ ({i, j'} : Finset S) := by
      rw [← hEq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    rcases Finset.mem_insert.1 hmem with hji | hjj'
    · exact absurd (hji ▸ hi) hjΛ
    · exact Finset.mem_singleton.1 hjj'
  rw [Finset.sum_image fun a ha b hb ↦ hinj ha hb]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjΛ : j ∉ Λ := (Finset.mem_sdiff.1 hj).2
  have hij : i ≠ j := fun heq ↦ hjΛ (heq ▸ hi)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [gaussianPotential_apply_pair J h hlt η]
  · rw [show ({i, j} : Finset S) = ({j, i} : Finset S) from Finset.pair_comm i j,
      gaussianPotential_apply_pair J h hgt η, hSymm j i]
    ring

/-- **The finite-volume Hamiltonian of the Gaussian potential as a quadratic form.** For `J`
symmetric with finite row support,
`H_Λ(η) = ∑_{i ∈ Λ} (J(i,i)/2 η_i² + h_i η_i) + ∑_{i < j, i,j ∈ Λ} J(i,j) η_i η_j
  + ∑_{i ∈ Λ} ∑_{j ∉ Λ} J(i,j) η_i η_j`
(the last sum a finite sum over `j` with `J(i,j) ≠ 0`). Every interaction term entering `H_Λ =
∑_{A ∩ Λ ≠ ∅} Φ_A` is a singleton in `Λ`, a pair inside `Λ`, or a pair crossing `Λ`'s boundary —
there is no further additive term depending only on `η|_{Λᶜ}`, since terms disjoint from `Λ` are
not part of `H_Λ` at all (Georgii's Definition (2.3)). -/
theorem hamiltonian_gaussianPotential_eq (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (η : S → ℝ) :
    (gaussianPotential J h).hamiltonian Λ η =
      ∑ i ∈ Λ, (J i i / 2 * η i ^ 2 + h i * η i) +
        (∑ i ∈ Λ, ∑ j ∈ Λ, if i < j then J i j * η i * η j else 0) +
        ∑ i ∈ Λ, ∑ j ∈ (hFin i).toFinset \ Λ, J i j * η i * η j := by
  have := isFiniteRange_gaussianPotential J h hSymm hFin
  have hsubset : interactingSupport (Φ := gaussianPotential J h) Λ ⊆
      Λ.powerset ∪ gaussianBoundaryPairs J hFin Λ := by
    intro Δ hΔ
    obtain ⟨⟨x, hx⟩, hΦ⟩ := (mem_interactingSupport (Φ := gaussianPotential J h)).1 hΔ
    have hxΔ : x ∈ Δ := Finset.mem_coe.1 hx.1
    have hxΛ : x ∈ Λ := Finset.mem_coe.1 hx.2
    by_cases h1 : Δ.card = 1
    · obtain ⟨k, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.mem_singleton] at hxΔ
      subst hxΔ
      exact Finset.mem_union_left _ (Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hxΛ))
    · by_cases h2 : ∃ a b : S, a < b ∧ Δ = ({a, b} : Finset S)
      · obtain ⟨a, b, hab, rfl⟩ := h2
        have hJab : J a b ≠ 0 := fun h0 ↦ hΦ (funext fun ζ ↦ by
          simp [gaussianPotential_apply_pair J h hab ζ, h0])
        rw [Finset.mem_insert, Finset.mem_singleton] at hxΔ
        by_cases haΛ : a ∈ Λ
        · by_cases hbΛ : b ∈ Λ
          · exact Finset.mem_union_left _ (Finset.mem_powerset.2
              (Finset.insert_subset_iff.2 ⟨haΛ, Finset.singleton_subset_iff.2 hbΛ⟩))
          · refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨a, haΛ, ?_⟩)
            exact Finset.mem_image.2 ⟨b, Finset.mem_sdiff.2
              ⟨(hFin a).mem_toFinset.2 hJab, hbΛ⟩, rfl⟩
        · have hbΛ : b ∈ Λ := by
            rcases hxΔ with rfl | rfl
            · exact absurd hxΛ haΛ
            · exact hxΛ
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, hbΛ, ?_⟩)
          refine Finset.mem_image.2 ⟨a, Finset.mem_sdiff.2 ⟨(hFin b).mem_toFinset.2 ?_, haΛ⟩,
            Finset.pair_comm b a⟩
          change J b a ≠ 0
          rwa [hSymm b a]
      · exact absurd (funext fun ζ ↦ gaussianPotential_eq_zero J h
          (fun k hk ↦ h1 (by rw [hk]; exact Finset.card_singleton k))
          (fun a b hab hAab ↦ h2 ⟨a, b, hab, hAab⟩) ζ) hΦ
  have hzero : ∀ Δ ∈ Λ.powerset ∪ gaussianBoundaryPairs J hFin Λ,
      Δ ∉ interactingSupport (Φ := gaussianPotential J h) Λ →
        gaussianPotential J h Δ η = 0 := by
    intro Δ hΔT hΔ
    rcases Finset.mem_union.1 hΔT with hΔp | hΔb
    · rcases Δ.eq_empty_or_nonempty with rfl | hΔne
      · exact gaussianPotential_eq_zero J h
          (fun i hi ↦ absurd hi.symm (Finset.singleton_ne_empty i))
          (fun i j _ hij ↦ absurd hij.symm (Finset.insert_ne_empty i {j})) η
      · have hΔΛ : ((Δ : Set S) ∩ (Λ : Set S)).Nonempty := by
          obtain ⟨x, hxΔ⟩ := hΔne
          exact ⟨x, Finset.mem_coe.2 hxΔ, Finset.mem_coe.2 (Finset.mem_powerset.1 hΔp hxΔ)⟩
        by_contra hne
        exact hΔ ((mem_interactingSupport (Φ := gaussianPotential J h)).2
          ⟨hΔΛ, fun hΦ0 ↦ hne (congrFun hΦ0 η)⟩)
    · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.1 hΔb
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hj
      have hΔΛ : ((({i, j} : Finset S) : Set S) ∩ (Λ : Set S)).Nonempty :=
        ⟨i, Finset.mem_coe.2 (Finset.mem_insert_self i {j}), Finset.mem_coe.2 hi⟩
      by_contra hne
      exact hΔ ((mem_interactingSupport (Φ := gaussianPotential J h)).2
        ⟨hΔΛ, fun hΦ0 ↦ hne (congrFun hΦ0 η)⟩)
  have hdisjoint : Disjoint (Λ.powerset) (gaussianBoundaryPairs J hFin Λ) := by
    refine Finset.disjoint_left.2 fun Δ hΔp hΔb ↦ ?_
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.1 hΔb
    obtain ⟨j, hj', rfl⟩ := Finset.mem_image.1 hj
    have hjΛ : j ∉ Λ := (Finset.mem_sdiff.1 hj').2
    exact hjΛ (Finset.mem_powerset.1 hΔp (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)))
  rw [hamiltonian_eq_interactingHamiltonian]
  change ∑ Δ ∈ interactingSupport (Φ := gaussianPotential J h) Λ, gaussianPotential J h Δ η = _
  rw [Finset.sum_subset hsubset hzero, Finset.sum_union hdisjoint,
    sum_powerset_gaussianPotential J h Λ η, sum_gaussianBoundaryPairs J h hSymm hFin Λ η]

/-- **Georgii's boundary field** `(J_{Λ,Λᶜ} ω)_i = ∑_{j ∉ Λ} J(i,j) ω(j)`: the coupling of the
site `i` to the boundary condition `ω` outside `Λ`. A finite sum, since `J` has finite row
support (`hFin`). -/
def gaussianBoundaryField (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ)
    (i : S) : ℝ :=
  ∑ j ∈ (hFin i).toFinset \ Λ, J i j * ω j

/-- **Georgii's mean (13.13)**, literally: `m_Λ(ω) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})` for
`Φ^{J,h}`'s finite-volume Gibbs distribution. The overall `-` sign is exactly Georgii's display and
is confirmed independently by completing the square in the Boltzmann factor `exp(-β H_Λ)` against
`hamiltonian_gaussianPotential_juxt_eq`'s
`H_Λ(ζ_Λ ω_{Λᶜ}) = (1/2)(ζ ⬝ᵥ 𝒥_Λ *ᵥ ζ) + (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ}) ⬝ᵥ ζ`: the *linear* term of
`-β H_Λ` in `ζ` is `-β (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})`, and matching
`Matrix.PosDef.neg_half_dotProduct_mulVec_add_dotProduct_eq` (`b = A m`, `A = β 𝒥_Λ`) gives
`m = (β 𝒥_Λ)⁻¹ (-β (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})`, independent of
`β`. -/
def gaussianMean (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ) : Λ → ℝ :=
  -((gaussianCovMatrix J Λ)⁻¹ *ᵥ (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1))

/-- **Diagonal/off-diagonal expansion of the quadratic form of `J`.** For `J` symmetric,
`∑_{i,j ∈ Λ} J(i,j) η_i η_j = ∑_{i ∈ Λ} J(i,i) η_i² + 2 ∑_{i < j, i,j ∈ Λ} J(i,j) η_i η_j`:
`Finset.sum_sum_eq_sum_diag_add_two_nsmul_sum_lt` at `f i j = J(i,j) η_i η_j`. -/
private lemma sum_sum_eq_sum_diag_add_two_mul_sum_lt (hSymm : ∀ i j, J i j = J j i)
    (Λ : Finset S) (η : S → ℝ) :
    ∑ i ∈ Λ, ∑ j ∈ Λ, J i j * η i * η j =
      ∑ i ∈ Λ, J i i * η i ^ 2 +
        2 * ∑ i ∈ Λ, ∑ j ∈ Λ, (if i < j then J i j * η i * η j else 0) := by
  have h := Finset.sum_sum_eq_sum_diag_add_two_nsmul_sum_lt (M := ℝ) Λ
    (f := fun i j ↦ J i j * η i * η j) fun i j ↦ by rw [hSymm i j]; ring
  simpa [Finset.sum_filter, nsmul_eq_mul, pow_two, mul_assoc] using h

omit [LinearOrder S] in
/-- The quadratic form `ζ ⬝ᵥ 𝒥_Λ *ᵥ ζ` evaluated at the `Λ`-restriction of a juxtaposition
`juxt Λ ω ζ`, as the corresponding `S`-indexed double sum. -/
private lemma dotProduct_mulVec_gaussianCovMatrix_eq_sum (Λ : Finset S) (ω : S → ℝ) (ζ : Λ → ℝ) :
    ζ ⬝ᵥ (gaussianCovMatrix J Λ) *ᵥ ζ =
      ∑ i ∈ Λ, ∑ j ∈ Λ, J i j * (juxt (Λ : Set S) ω ζ i) * (juxt (Λ : Set S) ω ζ j) := by
  set G : S → ℝ := juxt (Λ : Set S) ω ζ with hG
  have hζ : ∀ i : Λ, ζ i = G i.1 := fun i ↦
    (juxt_apply_of_mem (Finset.mem_coe.2 i.2) ζ).symm
  have hLHS : ζ ⬝ᵥ (gaussianCovMatrix J Λ) *ᵥ ζ =
      ∑ i : Λ, ∑ j ∈ Λ, J i.1 j * G i.1 * G j := by
    change ∑ i : Λ, ζ i * ∑ j : Λ, gaussianCovMatrix J Λ i j * ζ j = _
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hζ i, Finset.mul_sum, ← Finset.sum_coe_sort Λ (fun j ↦ J i.1 j * G i.1 * G j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [gaussianCovMatrix_apply, hζ j]
    ring
  rw [hLHS]
  exact Finset.sum_coe_sort Λ (fun i : S ↦ ∑ j ∈ Λ, J i j * G i * G j)

/-- **Georgii §13.1, the finite-volume Hamiltonian as a quadratic form on `Λ`.** With the
boundary condition `ω` juxtaposed against a free configuration `ζ : Λ → ℝ`,
`H_Λ(ζ_Λ ω_{Λᶜ}) = (1/2) (ζ ⬝ᵥ 𝒥_Λ *ᵥ ζ) + (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ}) ⬝ᵥ ζ`.
This is exactly Georgii's display preceding (13.13), read off `hamiltonian_gaussianPotential_eq`
by matching the site and inside-`Λ` pair terms against `dotProduct_mulVec_gaussianCovMatrix_eq_sum`
(via `sum_sum_eq_sum_diag_add_two_mul_sum_lt`) and the boundary-crossing term against
`gaussianBoundaryField`. -/
theorem hamiltonian_gaussianPotential_juxt_eq (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ) (ζ : Λ → ℝ) :
    (gaussianPotential J h).hamiltonian Λ (juxt (Λ : Set S) ω ζ) =
      (1 / 2) * (ζ ⬝ᵥ (gaussianCovMatrix J Λ) *ᵥ ζ) +
        (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1) ⬝ᵥ ζ := by
  set G : S → ℝ := juxt (Λ : Set S) ω ζ with hG
  have hζ : ∀ i : Λ, ζ i = G i.1 := fun i ↦
    (juxt_apply_of_mem (Finset.mem_coe.2 i.2) ζ).symm
  rw [hamiltonian_gaussianPotential_eq J h hSymm hFin Λ G,
    dotProduct_mulVec_gaussianCovMatrix_eq_sum J Λ ω ζ,
    sum_sum_eq_sum_diag_add_two_mul_sum_lt J hSymm Λ G]
  have hbf : (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1) ⬝ᵥ ζ =
      ∑ i ∈ Λ, (h i + gaussianBoundaryField J hFin Λ ω i) * G i := by
    change ∑ i : Λ, (h i.1 + gaussianBoundaryField J hFin Λ ω i.1) * ζ i = _
    rw [← Finset.sum_coe_sort Λ
      (fun i ↦ (h i + gaussianBoundaryField J hFin Λ ω i) * G i)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hζ i]
  have hthird : ∑ i ∈ Λ, ∑ j ∈ (hFin i).toFinset \ Λ, J i j * G i * G j =
      ∑ i ∈ Λ, gaussianBoundaryField J hFin Λ ω i * G i := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [gaussianBoundaryField, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjΛ : j ∉ Λ := (Finset.mem_sdiff.1 hj).2
    rw [hG, juxt_apply_of_not_mem hjΛ]
    ring
  have hexpand1 : ∑ i ∈ Λ, (J i i / 2 * G i ^ 2 + h i * G i) =
      ∑ i ∈ Λ, J i i / 2 * G i ^ 2 + ∑ i ∈ Λ, h i * G i := Finset.sum_add_distrib
  have hexpand2 : ∑ i ∈ Λ, (h i + gaussianBoundaryField J hFin Λ ω i) * G i =
      ∑ i ∈ Λ, h i * G i + ∑ i ∈ Λ, gaussianBoundaryField J hFin Λ ω i * G i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hexpand3 : ∑ i ∈ Λ, J i i / 2 * G i ^ 2 = 1 / 2 * ∑ i ∈ Λ, J i i * G i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hbf, hthird, hexpand1, hexpand2, hexpand3]
  ring

end HamiltonianQuadraticForm

/-! ### Georgii Proposition (13.13): λ-admissibility -/

section LambdaAdmissibility

variable [Countable S] (J : S → S → ℝ) (h : S → ℝ)

/-- The finite-volume partition function of the Gaussian potential, in closed form: the
*n*-dimensional Gaussian integral
(`Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct`) applied to the quadratic
form of `hamiltonian_gaussianPotential_juxt_eq`, at the rescaled precision `β • 𝒥_Λ` and boundary
vector `-β • (h|_Λ + J_{Λ,Λᶜ} η|_{Λᶜ})`. -/
private lemma sigmaFiniteLambdaZ_gaussianPotential_boltzmannFactor_eq
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β) (Λ : Finset S)
    (η : S → ℝ) :
    Specification.sigmaFiniteLambdaZ (S := S) (E := ℝ) volume
        ((gaussianPotential J h).boltzmannFactor β) Λ η =
      ENNReal.ofReal (Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / (β • gaussianCovMatrix J Λ).det) *
        Real.exp ((1 / 2) * ((-β • fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ η i.1) ⬝ᵥ
          (β • gaussianCovMatrix J Λ)⁻¹ *ᵥ
            (-β • fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ η i.1)))) := by
  have := isFiniteRange_gaussianPotential J h hSymm hFin
  have := isPotential_gaussianPotential J h
  set A : Matrix Λ Λ ℝ := β • gaussianCovMatrix J Λ with hAdef
  have hA : A.PosDef := (hPD Λ).smul hβ
  set b : Λ → ℝ := -β • (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ η i.1) with hbdef
  have hmeas : Measurable ((gaussianPotential J h).boltzmannFactor β Λ) :=
    measurable_boltzmannFactor β Λ
  have hZeq : Specification.sigmaFiniteLambdaZ (S := S) (E := ℝ) volume
      ((gaussianPotential J h).boltzmannFactor β) Λ η =
      ∫⁻ ζ : Λ → ℝ, ENNReal.ofReal
        (Real.exp (-(1 / 2) * (ζ ⬝ᵥ A *ᵥ ζ) + b ⬝ᵥ ζ)) ∂volume := by
    rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaFun_apply_eq_map,
      show (Measure.pi fun _ : Λ ↦ (volume : Measure ℝ)) = (volume : Measure (Λ → ℝ)) from
        volume_pi.symm,
      lintegral_map hmeas (Measurable.juxt (Λ := (Λ : Set S)) (η := η))]
    refine lintegral_congr fun ζ ↦ ?_
    change ENNReal.ofReal (Real.exp (-β * (gaussianPotential J h).hamiltonian Λ
        (juxt (Λ : Set S) η ζ))) = _
    rw [hamiltonian_gaussianPotential_juxt_eq J h hSymm hFin Λ η ζ]
    congr 2
    rw [hAdef, hbdef]
    simp only [Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_smul,
      neg_dotProduct]
    ring
  rw [hZeq, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (Matrix.PosDef.integrable_exp_neg_half_dotProduct_mulVec_add_dotProduct hA b)
    (Filter.Eventually.of_forall fun ζ ↦ (Real.exp_pos _).le),
    Matrix.PosDef.integral_exp_neg_half_dotProduct_mulVec_add_dotProduct hA b]

/-- **Georgii Proposition (13.13), λ-admissibility.** For `J` symmetric with finite row support,
`β > 0`, and every finite-volume interaction matrix `𝒥_Λ` positive definite, the Gaussian
potential's Boltzmann factor is admissible for Lebesgue measure: every finite-volume partition
function `Z_Λ^{J,h}(η)` is finite and nonzero. -/
theorem isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := ℝ) volume
      ((gaussianPotential J h).boltzmannFactor β) := by
  intro Λ η
  rw [sigmaFiniteLambdaZ_gaussianPotential_boltzmannFactor_eq J h hSymm hFin hPD β hβ Λ η]
  have hdetpos : 0 < (β • gaussianCovMatrix J Λ).det := ((hPD Λ).smul hβ).det_pos
  have hposval : 0 < Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / (β • gaussianCovMatrix J Λ).det) *
      Real.exp ((1 / 2) * ((-β • fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ η i.1) ⬝ᵥ
        (β • gaussianCovMatrix J Λ)⁻¹ *ᵥ
          (-β • fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ η i.1))) :=
    mul_pos (Real.sqrt_pos.2 (div_pos (by positivity) hdetpos)) (Real.exp_pos _)
  exact ⟨(ENNReal.ofReal_pos.2 hposval).ne', ENNReal.ofReal_ne_top⟩

/-- **The Gaussian specification, Georgii §13.1.** The finite-volume Gibbs specification of the
Gaussian potential `Φ^{J,h}` over Lebesgue measure, for `J` symmetric with finite row support,
`β > 0`, and every `𝒥_Λ` positive definite. -/
noncomputable def gaussianSpecification (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef)
    (β : ℝ) (hβ : 0 < β) : Specification S ℝ :=
  have := isFiniteRange_gaussianPotential J h hSymm hFin
  have := isPotential_gaussianPotential J h
  gibbsSpecificationOfSigmaFiniteAdmissible (gaussianPotential J h) volume β
    (isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor J h hSymm hFin hPD β hβ)

/-! ### Georgii Proposition (13.13): the finite-volume Gibbs distribution is Gaussian

## General lemma missing from `GibbsMeasure/Specification.lean`

* `Specification.sigmaFiniteLambdaFun_juxt_eq`: the σ-finite reference kernel `λ_Λ(·|η)` depends
  on the boundary condition `η` only through `η|_{Λᶜ}`: resampling inside `Λ` first does not
  change it (`GibbsMeasure/Specification.lean`).
-/

/-- **Georgii Proposition (13.13).** The finite-volume Gibbs distribution `γ_Λ^{J,h}(·|ω)` is the
`juxt`-pushforward of the multivariate Gaussian measure on `Λ → ℝ` with precision matrix `β • 𝒥_Λ`
and mean `gaussianMean J h hFin Λ ω`. Consequently, by
`ProbabilityTheory.integral_eval_multivariateGaussianPi` and
`ProbabilityTheory.integral_sub_mul_sub_multivariateGaussianPi`, under `γ_Λ^{J,h}(·|ω)` the mean of
`σ_i` (`i ∈ Λ`) is `(gaussianMean J h hFin Λ ω) i` and the covariance of `(σ_i, σ_j)` is
`(β • 𝒥_Λ)⁻¹ i j`. -/
theorem gaussianSpecification_apply (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef)
    (β : ℝ) (hβ : 0 < β) (Λ : Finset S) (ω : S → ℝ) :
    gaussianSpecification J h hSymm hFin hPD β hβ Λ ω =
      (ProbabilityTheory.multivariateGaussianPi (β • gaussianCovMatrix J Λ)
        (gaussianMean J h hFin Λ ω)).map (juxt (Λ : Set S) ω) := by
  have := isFiniteRange_gaussianPotential J h hSymm hFin
  have := isPotential_gaussianPotential J h
  set A : Matrix Λ Λ ℝ := β • gaussianCovMatrix J Λ with hAdef
  have hA : A.PosDef := (hPD Λ).smul hβ
  set b : Λ → ℝ := -β • (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1) with hbdef
  have hJdet : (gaussianCovMatrix J Λ).det ≠ 0 := (hPD Λ).det_pos.ne'
  have hJinv : gaussianCovMatrix J Λ * (gaussianCovMatrix J Λ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hJdet.isUnit
  have hAdet : A.det ≠ 0 := hA.det_pos.ne'
  have hAm : A *ᵥ gaussianMean J h hFin Λ ω = b := by
    rw [hAdef, gaussianMean, hbdef, Matrix.smul_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
      hJinv, Matrix.one_mulVec, smul_neg, neg_smul]
  have hm : A⁻¹ *ᵥ b = gaussianMean J h hFin Λ ω := by
    rw [← hAm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAdet.isUnit, Matrix.one_mulVec]
  have hdetpos : 0 < A.det := hA.det_pos
  have hsqrt1 : Real.sqrt (A.det / (2 * Real.pi) ^ Fintype.card Λ) *
      Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / A.det) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show A.det / (2 * Real.pi) ^ Fintype.card Λ * ((2 * Real.pi) ^ Fintype.card Λ / A.det) = 1
      by field_simp]
    exact Real.sqrt_one
  have hρmeas : Measurable
      (Specification.sigmaFinitePremodifierNorm (S := S) (E := ℝ) volume
        ((gaussianPotential J h).boltzmannFactor β) Λ) :=
    Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := ℝ) volume
      (isPremodifier_boltzmannFactor β) Λ
  rw [gaussianSpecification, gibbsSpecificationOfSigmaFiniteAdmissible,
    Specification.lambdaSpecification_apply, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    show (Measure.pi fun _ : Λ ↦ (volume : Measure ℝ)) = (volume : Measure (Λ → ℝ)) from
      volume_pi.symm,
    ← MeasureTheory.map_withDensity_comp volume (Measurable.juxt (Λ := (Λ : Set S)) (η := ω))
      hρmeas,
    ProbabilityTheory.multivariateGaussianPi]
  congr 1
  congr 1
  funext ζ
  rw [Specification.sigmaFinitePremodifierNorm, Specification.sigmaFiniteLambdaZ_juxt_eq,
    sigmaFiniteLambdaZ_gaussianPotential_boltzmannFactor_eq J h hSymm hFin hPD β hβ Λ ω]
  have hboltz : (gaussianPotential J h).boltzmannFactor β Λ (juxt (Λ : Set S) ω ζ) =
      ENNReal.ofReal (Real.exp (-(1 / 2) * (ζ ⬝ᵥ A *ᵥ ζ) + b ⬝ᵥ ζ)) := by
    change ENNReal.ofReal (Real.exp (-β * (gaussianPotential J h).hamiltonian Λ
        (juxt (Λ : Set S) ω ζ))) = _
    rw [hamiltonian_gaussianPotential_juxt_eq J h hSymm hFin Λ ω ζ]
    congr 2
    rw [hAdef, hbdef]
    simp only [Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, smul_eq_mul, neg_smul,
      neg_dotProduct]
    ring
  rw [hboltz, ProbabilityTheory.multivariateGaussianPDF,
    ProbabilityTheory.multivariateGaussianPDFReal]
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  rw [div_eq_iff (by positivity :
    Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / A.det) * Real.exp ((1 / 2) * (b ⬝ᵥ A⁻¹ *ᵥ b)) ≠ 0)]
  rw [Matrix.PosDef.neg_half_dotProduct_mulVec_add_dotProduct_eq hA b ζ, hm, Real.exp_add]
  rw [show Real.sqrt (A.det / (2 * Real.pi) ^ Fintype.card Λ) *
      Real.exp (-(1 / 2) * ((ζ - gaussianMean J h hFin Λ ω) ⬝ᵥ A *ᵥ
        (ζ - gaussianMean J h hFin Λ ω))) *
      (Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / A.det) *
        Real.exp (1 / 2 * (b ⬝ᵥ gaussianMean J h hFin Λ ω))) =
      (Real.sqrt (A.det / (2 * Real.pi) ^ Fintype.card Λ) *
        Real.sqrt ((2 * Real.pi) ^ Fintype.card Λ / A.det)) *
      (Real.exp (-(1 / 2) * ((ζ - gaussianMean J h hFin Λ ω) ⬝ᵥ A *ᵥ
        (ζ - gaussianMean J h hFin Λ ω))) * Real.exp (1 / 2 * (b ⬝ᵥ gaussianMean J h hFin Λ ω)))
      from by ring, hsqrt1, one_mul]

end LambdaAdmissibility

end Potential

/-! ### Georgii (13.4)–(13.7): conditional expectations given the other spins

`ξ_i^μ = μ(σ_i | 𝒯_{\{i\}})` (13.4), the conditional covariance function
`Γ(i, j) = μ((σ_i - ξ_i^μ)(σ_j - ξ_j^μ))` (13.6), and Proposition (13.7): for a Markovian Gaussian
field with `Γ(i, i) > 0`, the coupling `J(i, j) = Γ(i, j) / (Γ(i, i) Γ(j, j))` has finite range,
is positive definite, and `σ_i - ξ_i^μ = J(i, i)⁻¹ (h_i + ∑_j J(i, j) σ_j)` (13.5). -/

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} (μ : Measure (S → ℝ))

/-- **Georgii (13.4).** `ξ_i^μ = μ(σ_i | 𝒯_{\{i\}})`: the conditional expectation of the spin at
`i` given all the other spins. `𝒯_{\{i\}}` is Georgii's `𝓕_{S ∖ \{i\}}`, i.e.
`cylinderEvents ({i}ᶜ)`. -/
noncomputable abbrev condExpOutside (i : S) : (S → ℝ) → ℝ :=
  μ[(fun ω ↦ ω i) | cylinderEvents ({i}ᶜ : Set S)]

/-- **Georgii (13.6).** The conditional covariance function
`Γ(i, j) = μ((σ_i - ξ_i^μ)(σ_j - ξ_j^μ))`; `Γ(i, i)` is the mean square interpolation error. -/
noncomputable def condCovariance (i j : S) : ℝ :=
  ∫ ω, (ω i - condExpOutside μ i ω) * (ω j - condExpOutside μ j ω) ∂μ

/-- **The coupling of Proposition (13.7)**: `J(i, j) = Γ(i, j) / (Γ(i, i) Γ(j, j))`. -/
noncomputable def condCoupling (i j : S) : ℝ :=
  condCovariance μ i j / (condCovariance μ i i * condCovariance μ j j)

/-- **The external field of Proposition (13.7)**: `h_i = -∑_{j ∈ S} J(i, j) m_j`, with `m` the
mean of `μ`. -/
noncomputable def condExternalField (i : S) : ℝ :=
  -∑' j, condCoupling μ i j * ∫ ω, ω j ∂μ

variable {μ}

lemma condCovariance_comm (i j : S) : condCovariance μ i j = condCovariance μ j i := by
  unfold condCovariance
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

lemma condCoupling_comm (i j : S) : condCoupling μ i j = condCoupling μ j i := by
  unfold condCoupling
  rw [condCovariance_comm, mul_comm]

lemma condCoupling_self {i : S} (h : condCovariance μ i i ≠ 0) :
    condCoupling μ i i = (condCovariance μ i i)⁻¹ := by
  unfold condCoupling
  field_simp

section Orthogonality

variable [IsProbabilityMeasure μ]

lemma cylinderEvents_compl_singleton_le (i : S) :
    cylinderEvents (X := fun _ : S ↦ ℝ) ({i}ᶜ : Set S) ≤ MeasurableSpace.pi :=
  cylinderEvents_le_pi

/-- `σ_i - ξ_i^μ` is centered. -/
lemma integral_sub_condExpOutside (i : S) (hi : Integrable (fun ω : S → ℝ ↦ ω i) μ) :
    ∫ ω, (ω i - condExpOutside μ i ω) ∂μ = 0 := by
  rw [integral_sub hi integrable_condExp, integral_condExp cylinderEvents_le_pi, sub_self]

/-- **Orthogonality of the interpolation residual**: for `f` measurable given the spins off `i`
and square integrable, `μ(f (σ_i - ξ_i^μ)) = 0`. -/
lemma integral_mul_sub_condExpOutside_eq_zero {i : S} {f : (S → ℝ) → ℝ}
    (hf : AEStronglyMeasurable[cylinderEvents ({i}ᶜ : Set S)] f μ) (hf2 : MemLp f 2 μ)
    (hi : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ) :
    ∫ ω, f ω * (ω i - condExpOutside μ i ω) ∂μ = 0 :=
  integral_mul_sub_condExp_eq_zero cylinderEvents_le_pi hf (hi.integrable one_le_two)
    (hf2.integrable_mul hi) (hf2.integrable_mul (hi.condExp one_le_two))

/-- The residual `σ_i - ξ_i^μ` is orthogonal to every other spin `σ_k`, `k ≠ i`. -/
lemma integral_eval_mul_sub_condExpOutside_eq_zero {i k : S} (hki : k ≠ i)
    (hi : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ) (hk : MemLp (fun ω : S → ℝ ↦ ω k) 2 μ) :
    ∫ ω, ω k * (ω i - condExpOutside μ i ω) ∂μ = 0 :=
  integral_mul_sub_condExpOutside_eq_zero
    (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({i}ᶜ : Set S))
      (by simpa using hki)).aestronglyMeasurable hk hi

/-- The residual `σ_i - ξ_i^μ` is orthogonal to `ξ_i^μ` itself. -/
lemma integral_condExpOutside_mul_sub_condExpOutside_eq_zero {i : S}
    (hi : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ) :
    ∫ ω, condExpOutside μ i ω * (ω i - condExpOutside μ i ω) ∂μ = 0 :=
  integral_mul_sub_condExpOutside_eq_zero stronglyMeasurable_condExp.aestronglyMeasurable
    (hi.condExp one_le_two) hi

/-- `Γ(i, i) = μ(σ_i (σ_i - ξ_i^μ))`. -/
lemma condCovariance_self_eq_integral_eval_mul {i : S}
    (hi : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ) :
    condCovariance μ i i = ∫ ω, ω i * (ω i - condExpOutside μ i ω) ∂μ := by
  have h0 := integral_condExpOutside_mul_sub_condExpOutside_eq_zero hi
  have hint1 : Integrable (fun ω ↦ ω i * (ω i - condExpOutside μ i ω)) μ :=
    hi.integrable_mul (hi.sub (hi.condExp one_le_two))
  have hint2 : Integrable (fun ω ↦ condExpOutside μ i ω * (ω i - condExpOutside μ i ω)) μ :=
    (hi.condExp one_le_two).integrable_mul (hi.sub (hi.condExp one_le_two))
  unfold condCovariance
  rw [show (fun ω ↦ (ω i - condExpOutside μ i ω) * (ω i - condExpOutside μ i ω)) =
      fun ω ↦ ω i * (ω i - condExpOutside μ i ω) -
        condExpOutside μ i ω * (ω i - condExpOutside μ i ω) from funext fun ω ↦ by ring,
    integral_sub hint1 hint2, h0, sub_zero]

end Orthogonality

section Markov

variable [IsProbabilityMeasure μ]

/-- **Georgii (13.7), first step**: under the Markov hypothesis (ii) — `ξ_i^μ` has an
`𝓕_{Δi}`-measurable version, `i ∉ Δi` — one has `ξ_i^μ = μ(σ_i | 𝓕_{Δi})` a.s. (tower
property). -/
lemma condExpOutside_ae_eq_condExp_of_aestronglyMeasurable {i : S} {Δ : Finset S} (hΔ : i ∉ Δ)
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ) :
    condExpOutside μ i =ᵐ[μ] μ[(fun ω ↦ ω i) | cylinderEvents (Δ : Set S)] := by
  have hle : cylinderEvents (X := fun _ : S ↦ ℝ) (Δ : Set S) ≤ cylinderEvents ({i}ᶜ : Set S) :=
    cylinderEvents_mono fun j hj ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hΔ (Finset.mem_coe.1 hj)
  have h1 : μ[condExpOutside μ i | cylinderEvents (Δ : Set S)] =ᵐ[μ]
      μ[(fun ω ↦ ω i) | cylinderEvents (Δ : Set S)] :=
    condExp_condExp_of_le hle cylinderEvents_le_pi
  have h2 : μ[condExpOutside μ i | cylinderEvents (Δ : Set S)] =ᵐ[μ] condExpOutside μ i :=
    condExp_of_aestronglyMeasurable' cylinderEvents_le_pi hMarkov integrable_condExp
  exact h2.symm.trans h1

/-- **Georgii (13.7), `Γ(i, j) = 0` unless `j ∈ {i} ∪ Δi`**: if `ξ_i^μ` is `𝓕_{Δi}`-measurable and
`j ∉ {i} ∪ Δi`, then `σ_i - ξ_i^μ` is measurable given the spins off `j`, hence orthogonal to
`σ_j - ξ_j^μ`. -/
lemma condCovariance_eq_zero_of_notMem {i j : S} {Δ : Finset S}
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ)
    (hji : j ≠ i) (hjΔ : j ∉ Δ) (hi : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ)
    (hj2 : MemLp (fun ω : S → ℝ ↦ ω j) 2 μ) :
    condCovariance μ i j = 0 := by
  have hij : i ≠ j := hji.symm
  have hle : cylinderEvents (X := fun _ : S ↦ ℝ) (Δ : Set S) ≤ cylinderEvents ({j}ᶜ : Set S) :=
    cylinderEvents_mono fun k hk ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hjΔ (Finset.mem_coe.1 hk)
  have hξ : AEStronglyMeasurable[cylinderEvents ({j}ᶜ : Set S)] (condExpOutside μ i) μ := by
    obtain ⟨g, hg, hfg⟩ := hMarkov
    exact ⟨g, hg.mono hle, hfg⟩
  have hσ : AEStronglyMeasurable[cylinderEvents ({j}ᶜ : Set S)] (fun ω : S → ℝ ↦ ω i) μ :=
    (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({j}ᶜ : Set S))
      (by simpa using hij)).aestronglyMeasurable
  exact integral_mul_sub_condExpOutside_eq_zero (hσ.sub hξ) (hi.sub (hi.condExp one_le_two)) hj2

omit [IsProbabilityMeasure μ] in
/-- **Georgii (13.A4) for a Gaussian field**: the conditional expectation of `σ_i` given the spins
in a finite `Δ` is an affine function of `σ_Δ`. -/
lemma exists_condExp_cylinderEvents_eq_affine
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ) (i : S)
    (Δ : Finset S) :
    ∃ (u : ℝ) (v : Δ → ℝ), μ[(fun ω ↦ ω i) | cylinderEvents (Δ : Set S)] =ᵐ[μ]
      fun ω ↦ u + ∑ j, v j * ω j := by
  have hjoint : ProbabilityTheory.IsGaussianProcess
      (fun o : Option Δ ↦ o.elim (fun ω : S → ℝ ↦ ω i) fun j ω ↦ ω j) μ := by
    have := hμ.comp_right fun o : Option Δ ↦ o.elim i Subtype.val
    refine this.congr fun o ↦ ?_
    cases o <;> rfl
  obtain ⟨u, v, huv⟩ := hjoint.exists_condExp_eq_affine (measurable_pi_apply i)
    fun j ↦ measurable_pi_apply (j : S)
  refine ⟨u, v, ?_⟩
  rw [cylinderEvents_eq_comap_finsetRestrict]
  exact huv

end Markov

section Proposition13_7

variable (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
include hμ

/-- Every spin of a Gaussian field is square integrable. -/
lemma memLp_two_eval (i : S) : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ :=
  (hμ.hasGaussianLaw_eval i).memLp_two

/-- **Georgii (13.7), identification of the regression coefficients** (his (13.8) together with
the computation of `v_{ij}`): under the Markov hypothesis,
`ξ_i^μ = u - ∑_{j ∈ ∂i} Γ(i,j)/Γ(j,j) σ_j` a.s. for some constant `u`. -/
lemma exists_condExpOutside_ae_eq_affine {i : S} {Δ : Finset S} (hiΔ : i ∉ Δ)
    (hΓ : ∀ j, 0 < condCovariance μ j j)
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ) :
    ∃ u : ℝ, condExpOutside μ i =ᵐ[μ]
      fun ω ↦ u - ∑ j ∈ Δ, condCovariance μ i j / condCovariance μ j j * ω j := by
  have hP := hμ.isProbabilityMeasure
  obtain ⟨u, v, huv⟩ := exists_condExp_cylinderEvents_eq_affine hμ i Δ
  have hξ : condExpOutside μ i =ᵐ[μ] fun ω ↦ u + ∑ j : Δ, v j * ω j :=
    (condExpOutside_ae_eq_condExp_of_aestronglyMeasurable hiΔ hMarkov).trans huv
  have hL2 := memLp_two_eval hμ
  have hv : ∀ k : Δ, v k = -(condCovariance μ i k / condCovariance μ k k) := by
    intro k
    have hik : i ≠ k := fun h ↦ hiΔ (h ▸ k.2)
    set R : (S → ℝ) → ℝ := fun ω ↦ ω k - condExpOutside μ k ω with hR_def
    have hR2 : MemLp R 2 μ := (hL2 k).sub ((hL2 k).condExp one_le_two)
    have hcongr : (fun ω ↦ (ω i - condExpOutside μ i ω) * (ω k - condExpOutside μ k ω)) =ᵐ[μ]
        fun ω ↦ (ω i * R ω - u * R ω) - ∑ j : Δ, v j * (ω j * R ω) := by
      filter_upwards [hξ] with ω hω
      rw [hω]
      simp only [hR_def, sub_mul, Finset.sum_mul, mul_assoc, sub_add_eq_sub_sub]
    have hΓ_eq : condCovariance μ i k = -(v k * condCovariance μ k k) := by
      have hint1 : Integrable (fun ω ↦ ω i * R ω) μ := (hL2 i).integrable_mul hR2
      have hint2 : Integrable (fun ω ↦ u * R ω) μ := (hR2.integrable one_le_two).const_mul u
      have hint3 : ∀ j : Δ, Integrable (fun ω ↦ v j * (ω j * R ω)) μ := fun j ↦
        ((hL2 j).integrable_mul hR2).const_mul _
      have hRHS : ∫ a, a k * R a ∂μ = condCovariance μ k k :=
        (condCovariance_self_eq_integral_eval_mul (hL2 k)).symm
      rw [show condCovariance μ i k =
          ∫ ω, (ω i - condExpOutside μ i ω) * (ω k - condExpOutside μ k ω) ∂μ from rfl,
        integral_congr_ae hcongr,
        integral_sub (f := fun ω ↦ ω i * R ω - u * R ω) (g := fun ω ↦ ∑ j : Δ, v j * (ω j * R ω))
          (hint1.sub hint2) (integrable_finsetSum _ fun j _ ↦ hint3 j),
        integral_sub hint1 hint2, integral_finsetSum _ fun j _ ↦ hint3 j]
      simp only [integral_const_mul]
      rw [show ∫ ω, ω i * R ω ∂μ = 0 from
          integral_eval_mul_sub_condExpOutside_eq_zero hik (hL2 k) (hL2 i),
        show ∫ ω, R ω ∂μ = 0 from
          integral_sub_condExpOutside (k : S) ((hL2 k).integrable one_le_two),
        Finset.sum_eq_single k]
      · rw [hRHS]
        ring
      · intro j _ hjk
        have hjk' : (j : S) ≠ k := fun h ↦ hjk (Subtype.ext h)
        rw [integral_eval_mul_sub_condExpOutside_eq_zero hjk' (hL2 k) (hL2 j), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ k) h
    have hkk : condCovariance μ k k ≠ 0 := (hΓ k).ne'
    rw [hΓ_eq]
    field_simp
  refine ⟨u, hξ.trans (Filter.Eventually.of_forall fun ω ↦ ?_)⟩
  simp only [hv, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  exact (Finset.sum_coe_sort Δ fun j ↦ condCovariance μ i j / condCovariance μ j j * ω j).symm ▸
    rfl

/-- **Georgii (13.7), finite range**: `J(i, j) = 0` unless `j ∈ {i} ∪ ∂i`. -/
lemma condCoupling_eq_zero_of_notMem {i j : S} {Δ : Finset S}
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ)
    (hji : j ≠ i) (hjΔ : j ∉ Δ) : condCoupling μ i j = 0 := by
  have hP := hμ.isProbabilityMeasure
  unfold condCoupling
  rw [condCovariance_eq_zero_of_notMem hMarkov hji hjΔ (memLp_two_eval hμ i) (memLp_two_eval hμ j),
    zero_div]

/-- The mean of a Gaussian field, `m_i = μ(σ_i)`, against the coupling: for a Markovian field,
`h_i = -∑_{j ∈ S} J(i, j) m_j` is the finite sum over `{i} ∪ ∂i`. -/
lemma condExternalField_eq_sum [DecidableEq S] {i : S} {Δ : Finset S}
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ) :
    condExternalField μ i = -∑ j ∈ insert i Δ, condCoupling μ i j * ∫ ω, ω j ∂μ := by
  unfold condExternalField
  congr 1
  refine tsum_eq_sum fun j hj ↦ ?_
  rw [Finset.mem_insert, not_or] at hj
  rw [condCoupling_eq_zero_of_notMem hμ hMarkov hj.1 hj.2, zero_mul]

/-- **Georgii (13.5) for the coupling and field of Proposition (13.7)**, with the sum written over
the finite set `{i} ∪ ∂i` carrying the coupling:
`σ_i - ξ_i^μ = J(i, i)⁻¹ (h_i + ∑_{j ∈ {i} ∪ ∂i} J(i, j) σ_j)` a.s. -/
theorem sub_condExpOutside_ae_eq_condCoupling [DecidableEq S] {i : S} {Δ : Finset S} (hiΔ : i ∉ Δ)
    (hΓ : ∀ j, 0 < condCovariance μ j j)
    (hMarkov : AEStronglyMeasurable[cylinderEvents (Δ : Set S)] (condExpOutside μ i) μ) :
    ∀ᵐ ω ∂μ, ω i - condExpOutside μ i ω = (condCoupling μ i i)⁻¹ *
      (condExternalField μ i + ∑ j ∈ insert i Δ, condCoupling μ i j * ω j) := by
  have hP := hμ.isProbabilityMeasure
  obtain ⟨u, hξ⟩ := exists_condExpOutside_ae_eq_affine hμ hiΔ hΓ hMarkov
  set c : S → ℝ := fun j ↦ condCovariance μ i j / condCovariance μ j j with hc_def
  have hcJ : ∀ j, condCovariance μ i i * condCoupling μ i j = c j := by
    intro j
    simp only [hc_def, condCoupling]
    field_simp [(hΓ i).ne', (hΓ j).ne']
  have hci : c i = 1 := div_self (hΓ i).ne'
  have hJii : (condCoupling μ i i)⁻¹ = condCovariance μ i i := by
    rw [condCoupling_self (hΓ i).ne', inv_inv]
  -- The constant `u` from the mean of the residual.
  have hu : u = ∑ j ∈ insert i Δ, c j * ∫ ω, ω j ∂μ := by
    have h0 := integral_sub_condExpOutside (μ := μ) i ((memLp_two_eval hμ i).integrable one_le_two)
    have hcongr : (fun ω ↦ ω i - condExpOutside μ i ω) =ᵐ[μ]
        fun ω ↦ (ω i - u) + ∑ j ∈ Δ, c j * ω j := by
      filter_upwards [hξ] with ω hω
      rw [hω]
      ring
    have hint : ∀ j ∈ Δ, Integrable (fun ω : S → ℝ ↦ c j * ω j) μ := fun j _ ↦
      ((memLp_two_eval hμ j).integrable one_le_two).const_mul _
    rw [integral_congr_ae hcongr, integral_add (f := fun ω : S → ℝ ↦ ω i - u)
      (g := fun ω ↦ ∑ j ∈ Δ, c j * ω j) (((memLp_two_eval hμ i).integrable one_le_two).sub
      (integrable_const u)) (integrable_finsetSum _ hint), integral_sub
      ((memLp_two_eval hμ i).integrable one_le_two) (integrable_const u), integral_finsetSum _ hint,
      integral_const, probReal_univ, one_smul] at h0
    simp only [integral_const_mul] at h0
    rw [Finset.sum_insert hiΔ, hci, one_mul]
    linarith
  filter_upwards [hξ] with ω hω
  rw [hω, hJii, condExternalField_eq_sum hμ hMarkov, hu, mul_add, mul_neg, Finset.mul_sum,
    Finset.mul_sum]
  simp only [← mul_assoc, hcJ]
  rw [Finset.sum_insert hiΔ, Finset.sum_insert hiΔ, hci, one_mul, one_mul]
  ring

/-- **`𝒥_Λ` is nonnegative definite**: `J(i, j) = Γ(i, j) / (Γ(i, i) Γ(j, j))` is the covariance
of the normalized residuals `(σ_i - ξ_i^μ) / Γ(i, i)`. -/
lemma posSemidef_gaussianCovMatrix_condCoupling (hΓ : ∀ j, 0 < condCovariance μ j j)
    (Λ : Finset S) : (Potential.gaussianCovMatrix (condCoupling μ) Λ).PosSemidef := by
  have hP := hμ.isProbabilityMeasure
  set Z : S → (S → ℝ) → ℝ :=
    fun i ω ↦ (condCovariance μ i i)⁻¹ * (ω i - condExpOutside μ i ω) with hZ_def
  have hZ2 : ∀ i, MemLp (Z i) 2 μ := fun i ↦
    ((memLp_two_eval hμ i).sub ((memLp_two_eval hμ i).condExp one_le_two)).const_mul _
  have hZmean : ∀ i, ∫ ω, Z i ω ∂μ = 0 := fun i ↦ by
    simp only [hZ_def]
    rw [integral_const_mul,
      integral_sub_condExpOutside i ((memLp_two_eval hμ i).integrable one_le_two), mul_zero]
  have hcov : ∀ i j : Λ, cov[Z i, Z j; μ] = condCoupling μ i j := by
    intro i j
    unfold ProbabilityTheory.covariance
    rw [hZmean, hZmean]
    simp only [sub_zero, hZ_def]
    have hii := (hΓ i).ne'
    have hjj := (hΓ j).ne'
    unfold condCoupling
    rw [eq_div_iff (mul_ne_zero hii hjj), ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
    field_simp
  have := Matrix.posSemidef_covariance (X := fun i : Λ ↦ Z i) fun i ↦ hZ2 i
  have hmat : (Potential.gaussianCovMatrix (condCoupling μ) Λ) =
      (fun i j ↦ cov[Z i, Z j; μ] : Matrix Λ Λ ℝ) := by
    ext i j
    exact (hcov i j).symm
  rw [hmat]
  exact this

/-- **Georgii (13.7), positive definiteness of `J`**, in the finite-volume form of (13.12): for a
Markovian Gaussian field with `Γ(i, i) > 0`, every `𝒥_Λ = (J(i, j))_{i, j ∈ Λ}` is positive
definite. Georgii's proof: `𝒥_Λ` is nonnegative definite, and `Γ_Λ(j, k) = μ(σ_j (σ_k - η_k^Λ))`,
`η_k^Λ = μ(σ_k | 𝒯_Λ)`, is a right inverse of `𝒥_Λ`. -/
theorem posDef_gaussianCovMatrix_condCoupling [DecidableEq S]
    (hΓ : ∀ j, 0 < condCovariance μ j j) (N : S → Finset S) (hN : ∀ i, i ∉ N i)
    (hMarkov : ∀ i, AEStronglyMeasurable[cylinderEvents (N i : Set S)] (condExpOutside μ i) μ)
    (Λ : Finset S) : (Potential.gaussianCovMatrix (condCoupling μ) Λ).PosDef := by
  have hP := hμ.isProbabilityMeasure
  have hL2 := memLp_two_eval hμ
  refine (posSemidef_gaussianCovMatrix_condCoupling hμ hΓ Λ).posDef_iff_det_ne_zero.2 ?_
  set J := condCoupling μ with hJ_def
  set η : S → (S → ℝ) → ℝ := fun k ↦ μ[(fun ω ↦ ω k) | cylinderEvents ((Λ : Set S)ᶜ)] with hη_def
  set R : S → (S → ℝ) → ℝ := fun k ω ↦ ω k - η k ω with hR_def
  have hR2 : ∀ k, MemLp (R k) 2 μ := fun k ↦ (hL2 k).sub ((hL2 k).condExp one_le_two)
  have hΛle : ∀ i ∈ Λ, cylinderEvents (X := fun _ : S ↦ ℝ) ((Λ : Set S)ᶜ) ≤
      cylinderEvents ({i}ᶜ : Set S) := fun i hi ↦
    cylinderEvents_mono
      (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 (Finset.mem_coe.2 hi)))
  -- `Γ_Λ`, Georgii's right inverse.
  set G : Matrix Λ Λ ℝ := fun j k ↦ ∫ ω, ω j * R k ω ∂μ with hG_def
  -- Off-`Λ` spins are orthogonal to the residuals `R k`.
  have hoff : ∀ j, j ∉ Λ → ∀ k : Λ, ∫ ω, ω j * R k ω ∂μ = 0 := by
    intro j hj k
    refine integral_mul_sub_condExp_eq_zero cylinderEvents_le_pi
      (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ((Λ : Set S)ᶜ))
        (by simpa using hj)).aestronglyMeasurable ((hL2 k).integrable one_le_two)
      ((hL2 j).integrable_mul (hL2 k)) ((hL2 j).integrable_mul ((hL2 k).condExp one_le_two))
  -- The key identity `∑_{j ∈ Λ} J(i, j) Γ_Λ(j, k) = δ_{ik}`.
  have hJG : Potential.gaussianCovMatrix J Λ * G = 1 := by
    ext i k
    set T : Finset S := Λ ∪ insert (i : S) (N i) with hT_def
    have hΛT : Λ ⊆ T := Finset.subset_union_left
    have hiT : insert (i : S) (N i) ⊆ T := Finset.subset_union_right
    have hJzero : ∀ j, j ∉ insert (i : S) (N i) → J i j = 0 := fun j hj ↦ by
      rw [Finset.mem_insert, not_or] at hj
      exact condCoupling_eq_zero_of_notMem hμ (hMarkov i) hj.1 hj.2
    -- Rewrite the matrix product as one integral.
    have hprod : (Potential.gaussianCovMatrix J Λ * G) i k =
        ∫ ω, (∑ j ∈ T, J i j * ω j) * R k ω ∂μ := by
      rw [Matrix.mul_apply]
      simp only [Potential.gaussianCovMatrix_apply, hG_def]
      rw [Finset.sum_coe_sort Λ (fun j ↦ J i j * ∫ ω, ω j * R k ω ∂μ)]
      rw [Finset.sum_subset hΛT fun j _ hj ↦ by rw [hoff j hj k, mul_zero]]
      symm
      calc ∫ ω, (∑ j ∈ T, J i j * ω j) * R k ω ∂μ
          = ∫ ω, ∑ j ∈ T, J i j * (ω j * R k ω) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
            simp only [Finset.sum_mul, mul_assoc]
        _ = ∑ j ∈ T, J i j * ∫ ω, ω j * R k ω ∂μ := by
            rw [integral_finsetSum (f := fun j ω ↦ J i j * (ω j * R k ω)) _
              fun j _ ↦ ((hL2 j).integrable_mul (hR2 k)).const_mul _]
            simp only [integral_const_mul]
    -- (13.5) turns the sum into `J(i,i) (σ_i - ξ_i) - h_i`.
    have h135 := sub_condExpOutside_ae_eq_condCoupling hμ (hN i) hΓ (hMarkov i)
    have hsumT : ∀ ω : S → ℝ,
        ∑ j ∈ T, J i j * ω j = ∑ j ∈ insert (i : S) (N i), J i j * ω j := fun ω ↦
      (Finset.sum_subset hiT fun j _ hj ↦ by rw [hJzero j hj, zero_mul]).symm
    have hJii : J i i ≠ 0 := by
      rw [hJ_def, condCoupling_self (hΓ i).ne']
      exact inv_ne_zero (hΓ i).ne'
    have hcongr : (fun ω ↦ (∑ j ∈ T, J i j * ω j) * R k ω) =ᵐ[μ]
        fun ω ↦ J i i * ((ω i - condExpOutside μ i ω) * R k ω) -
          condExternalField μ i * R k ω := by
      filter_upwards [h135] with ω hω
      rw [hsumT]
      have : ∑ j ∈ insert (i : S) (N i), J i j * ω j =
          J i i * (ω i - condExpOutside μ i ω) - condExternalField μ i := by
        rw [hω, ← mul_assoc, mul_inv_cancel₀ hJii, one_mul, add_sub_cancel_left]
      rw [this]
      ring
    have hint1 : Integrable (fun ω ↦ (ω i - condExpOutside μ i ω) * R k ω) μ :=
      ((hL2 i).sub ((hL2 i).condExp one_le_two)).integrable_mul (hR2 k)
    rw [hprod, integral_congr_ae hcongr, integral_sub (hint1.const_mul _)
      (((hR2 k).integrable one_le_two).const_mul _), integral_const_mul, integral_const_mul,
      show ∫ ω, R k ω ∂μ = 0 from by
        simp only [hR_def, hη_def]
        rw [integral_sub ((hL2 k).integrable one_le_two) integrable_condExp,
          integral_condExp cylinderEvents_le_pi, sub_self],
      mul_zero, sub_zero]
    -- `η_k^Λ` is measurable given the spins off `i`, for every `i ∈ Λ`.
    have hηi : AEStronglyMeasurable[cylinderEvents ({(i : S)}ᶜ : Set S)] (η k) μ :=
      (stronglyMeasurable_condExp.mono (hΛle i i.2)).aestronglyMeasurable
    by_cases hik : i = k
    · subst hik
      rw [Matrix.one_apply_eq]
      have hsplit : (fun ω ↦ (ω i - condExpOutside μ i ω) * R i ω) =
          fun ω ↦ ω i * (ω i - condExpOutside μ i ω) -
            η i ω * (ω i - condExpOutside μ i ω) := by
        funext ω; simp only [hR_def]; ring
      rw [hsplit, integral_sub (f := fun ω ↦ ω i * (ω i - condExpOutside μ i ω))
        (g := fun ω ↦ η i ω * (ω i - condExpOutside μ i ω))
        ((hL2 i).integrable_mul ((hL2 i).sub ((hL2 i).condExp one_le_two)))
        (((hL2 i).condExp one_le_two).integrable_mul ((hL2 i).sub ((hL2 i).condExp one_le_two))),
        integral_mul_sub_condExpOutside_eq_zero hηi ((hL2 i).condExp one_le_two) (hL2 i),
        ← condCovariance_self_eq_integral_eval_mul (hL2 i), sub_zero, hJ_def,
        condCoupling_self (hΓ i).ne', inv_mul_cancel₀ (hΓ i).ne']
    · rw [Matrix.one_apply_ne hik]
      have hki : (k : S) ≠ i := fun h ↦ hik (Subtype.ext h.symm)
      have hRk : AEStronglyMeasurable[cylinderEvents ({(i : S)}ᶜ : Set S)] (R k) μ :=
        (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({(i : S)}ᶜ : Set S))
          (by simpa using hki)).aestronglyMeasurable.sub hηi
      rw [show (fun ω ↦ (ω i - condExpOutside μ i ω) * R k ω) =
          fun ω ↦ R k ω * (ω i - condExpOutside μ i ω) from funext fun ω ↦ mul_comm _ _,
        integral_mul_sub_condExpOutside_eq_zero hRk (hR2 k) (hL2 i), mul_zero]
  intro hdet
  have := congrArg Matrix.det hJG
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- **Georgii Proposition (13.7).** Let `μ` be a Gaussian field with mean `m`. Suppose
(i) `Γ(i, i) > 0` for all `i`, and (ii) `μ` is Markovian: for each `i` there is a finite `∂i ∌ i`
such that `ξ_i^μ` has an `𝓕_{∂i}`-measurable version. Define
`J(i, j) = Γ(i, j) / (Γ(i, i) Γ(j, j))` (`condCoupling`) and `h_i = -∑_j J(i, j) m_j`
(`condExternalField`). Then `J(i, j) = 0` unless `j ∈ {i} ∪ ∂i`, `J` is positive definite (in
Georgii's finitely-supported sense (13.3)), and (13.5) holds for all `i`:
`σ_i - ξ_i^μ = J(i, i)⁻¹ (h_i + ∑_j J(i, j) σ_j)` a.s., the sum over `S` being the (absolutely
convergent) `tsum`, which reduces to the finite sum over `{i} ∪ ∂i`. -/
theorem georgii_13_7 [DecidableEq S] (hΓ : ∀ j, 0 < condCovariance μ j j) (N : S → Finset S)
    (hN : ∀ i, i ∉ N i)
    (hMarkov : ∀ i, AEStronglyMeasurable[cylinderEvents (N i : Set S)] (condExpOutside μ i) μ) :
    (∀ i j, j ≠ i → j ∉ N i → condCoupling μ i j = 0) ∧
      Matrix.PosDef (Matrix.of (condCoupling μ)) ∧
      ∀ i, ∀ᵐ ω ∂μ, ω i - condExpOutside μ i ω = (condCoupling μ i i)⁻¹ *
        (condExternalField μ i + ∑' j, condCoupling μ i j * ω j) := by
  refine ⟨fun i j hji hjN ↦ condCoupling_eq_zero_of_notMem hμ (hMarkov i) hji hjN, ?_, fun i ↦ ?_⟩
  · exact Matrix.posDef_iff_forall_finset_submatrix.2 fun Λ ↦
      posDef_gaussianCovMatrix_condCoupling hμ hΓ N hN hMarkov Λ
  · filter_upwards [sub_condExpOutside_ae_eq_condCoupling hμ (hN i) hΓ (hMarkov i)] with ω hω
    rw [hω]
    congr 2
    refine (tsum_eq_sum fun j hj ↦ ?_).symm
    rw [Finset.mem_insert, not_or] at hj
    rw [condCoupling_eq_zero_of_notMem hμ (hMarkov i) hj.1 hj.2, zero_mul]

end Proposition13_7

end MeasureTheory.GibbsMeasure

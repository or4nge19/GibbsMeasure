/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Potential.Pair
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import GibbsMeasure.Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Density

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
* `Matrix.PosDef.smul`: a positive definite real matrix scaled by a positive real is positive
  definite. Intended home: `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.

## General lemma missing from `GibbsMeasure/Specification.lean`

* `Specification.sigmaFiniteLambdaFun_juxt_eq`: the σ-finite reference kernel `λ_Λ(·|η)` depends
  on the boundary condition `η` only through `η|_{Λᶜ}` — resampling inside `Λ` first does not
  change it. Intended home: next to `Specification.sigmaFiniteLambdaFun_apply_eq_map`.

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
* `Potential.gaussianMean J h hFin Λ ω`: **the mean of (13.13)**,
  `m_Λ(ω) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})` — see its docstring for why the overall sign is `-`,
  not Georgii's naive-looking `𝒥_Λ⁻¹(h - J_{Λ,Λᶜ}ω)`: it is forced by completing the square against
  the actual sign convention already fixed by `Potential.gaussianPotential`'s `+ h i * x` term.
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

## What is not in this file, and why

* **Propositions (13.7) and Lemma (13.10)**, i.e. items (13.4)–(13.10), identify the conditional
  expectation `ξ_i^μ = μ(σ_i | 𝒯_{\{i\}})` and show it is affine in finitely many coordinates. This
  needs regular conditional distributions / conditional expectation machinery for the tail
  σ-algebra `𝒯_{\{i\}}` (`cylinderEvents ({i} : Set S)ᶜ`) that is not built anywhere in this tree
  (`GibbsMeasure/Topology/LocalConvergence.lean` has the σ-algebra but no conditional expectation
  theory over it). This is a genuine gap, not a missing tail-gluing step.
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

/-- Summing `siteTerms f` over the powerset of `Δ` is summing `f` over `Δ`: only the singletons
`{i}`, `i ∈ Δ`, are both in `Δ.powerset` and possibly nonzero. The site-term counterpart of
`Potential.sum_powerset_pairTerms`. -/
lemma sum_powerset_siteTerms (Δ : Finset S) (f : S → α) :
    ∑ A ∈ Δ.powerset, siteTerms f A = ∑ i ∈ Δ, f i := by
  classical
  have hsub : Δ.image (fun i ↦ ({i} : Finset S)) ⊆ Δ.powerset := by
    intro A hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
    simpa using hi
  have hzero : ∀ A ∈ Δ.powerset, A ∉ Δ.image (fun i ↦ ({i} : Finset S)) → siteTerms f A = 0 := by
    intro A hA hAim
    refine siteTerms_eq_zero fun k hk ↦ hAim ?_
    have hkΔ : k ∈ Δ := Finset.mem_powerset.1 hA (hk ▸ Finset.mem_singleton_self k)
    exact Finset.mem_image.2 ⟨k, hkΔ, hk.symm⟩
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun a _ b _ hab ↦ Finset.singleton_injective hab)]
  exact Finset.sum_congr rfl fun i _ ↦ siteTerms_singleton i

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

/-- A single-site potential has finite range unconditionally: each site interacts only with
itself. (Intended home: next to `Potential.site`, if `site` is ever generalized out of this
file.) -/
lemma isFiniteRange_site : IsFiniteRange (site f) where
  exists_finset i := ⟨{i}, fun A hiA hΦ ↦ by
    by_cases hA : A = {i}
    · rw [hA]
    · exact absurd (site_eq_zero fun k hk ↦ hA (by
        have hik : i = k := Finset.mem_singleton.1 (hk ▸ hiA)
        rw [hik, hk])) hΦ⟩

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
      · exact gaussianPotential_eq_zero J h (fun i hi ↦ absurd hi.symm (Finset.singleton_ne_empty i))
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

/-- **Georgii's mean** `m_Λ(ω) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})` for `Φ^{J,h}`'s finite-volume
Gibbs distribution. The overall `-` sign is forced by completing the square in the Boltzmann
factor `exp(-β H_Λ)` against `hamiltonian_gaussianPotential_juxt_eq`'s
`H_Λ(ζ_Λ ω_{Λᶜ}) = (1/2)(ζ ⬝ᵥ 𝒥_Λ *ᵥ ζ) + (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ}) ⬝ᵥ ζ`: the *linear* term of
`-β H_Λ` in `ζ` is `-β (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})`, and matching
`Matrix.PosDef.neg_half_dotProduct_mulVec_add_dotProduct_eq` (`b = A m`, `A = β 𝒥_Λ`) gives
`m = (β 𝒥_Λ)⁻¹ (-β (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})) = -𝒥_Λ⁻¹ (h|_Λ + J_{Λ,Λᶜ} ω|_{Λᶜ})`, independent of
`β`. This is the sign that is actually forced by `Potential.gaussianPotential`'s `+ h i * x` site
term (see this file's module docstring): the naive expectation `m = 𝒥_Λ⁻¹(h - J_{Λ,Λᶜ}ω)` would
hold only for a potential with a `- h i * x` site term, which is *not* what is coded here. -/
def gaussianMean (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ) : Λ → ℝ :=
  -((gaussianCovMatrix J Λ)⁻¹ *ᵥ (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1))

/-- **Diagonal/off-diagonal expansion of a symmetric bilinear form.** For `J` symmetric,
`∑_{i,j ∈ Λ} J(i,j) η_i η_j = ∑_{i ∈ Λ} J(i,i) η_i² + 2 ∑_{i < j, i,j ∈ Λ} J(i,j) η_i η_j`.
(Intended home, if generalized past `J`: a `Finset`-sum lemma for symmetric `f : S → S → α` next
to `Potential.pairTerms`.) -/
private lemma sum_sum_eq_sum_diag_add_two_mul_sum_lt (hSymm : ∀ i j, J i j = J j i)
    (Λ : Finset S) (η : S → ℝ) :
    ∑ i ∈ Λ, ∑ j ∈ Λ, J i j * η i * η j =
      ∑ i ∈ Λ, J i i * η i ^ 2 +
        2 * ∑ i ∈ Λ, ∑ j ∈ Λ, (if i < j then J i j * η i * η j else 0) := by
  classical
  set f : S → S → ℝ := fun i j ↦ J i j * η i * η j with hf
  have hsplit : ∀ i j : S, f i j =
      (if i < j then f i j else 0) + (if i = j then f i j else 0) +
        (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · rw [ite_eq_left hlt, ite_eq_right hlt.ne, ite_eq_right (not_lt.2 hlt.le)]
      ring
    · subst heq
      rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl]
      ring
    · rw [ite_eq_right (not_lt.2 hgt.le), ite_eq_right hgt.ne', ite_eq_left hgt]
      ring
  have hstep : ∑ i ∈ Λ, ∑ j ∈ Λ, f i j =
      (∑ i ∈ Λ, ∑ j ∈ Λ, (if i < j then f i j else 0)) +
        (∑ i ∈ Λ, ∑ j ∈ Λ, (if i = j then f i j else 0)) +
        ∑ i ∈ Λ, ∑ j ∈ Λ, (if j < i then f i j else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hsplit i j
  have hdiag : ∑ i ∈ Λ, ∑ j ∈ Λ, (if i = j then f i j else 0) = ∑ i ∈ Λ, J i i * η i ^ 2 := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.sum_ite_eq Λ i (fun j ↦ f i j), ite_eq_left hi]
    simp only [hf]
    ring
  have hlast : ∑ i ∈ Λ, ∑ j ∈ Λ, (if j < i then f i j else 0) =
      ∑ i ∈ Λ, ∑ j ∈ Λ, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hij : j < i
    · rw [ite_eq_left hij, ite_eq_left hij]
      simp only [hf]
      rw [hSymm i j]
      ring
    · rw [ite_eq_right hij, ite_eq_right hij]
  rw [hstep, hdiag, hlast]
  ring

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

/-! ### Georgii Proposition (13.13): λ-admissibility

## General lemma missing from Mathlib

* `Matrix.PosDef.smul`: a positive definite real matrix scaled by a positive real scalar is
  positive definite. Intended home: `Mathlib/LinearAlgebra/Matrix/PosDef.lean`, next to
  `Matrix.PosDef.posSemidef`.
-/

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
  have hA : A.PosDef := Matrix.PosDef.smul_of_pos (hPD Λ) hβ
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
  have hdetpos : 0 < (β • gaussianCovMatrix J Λ).det := (Matrix.PosDef.smul_of_pos (hPD Λ) hβ).det_pos
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
  change it. Intended home: next to `Specification.sigmaFiniteLambdaFun_apply_eq_map`.
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
  have hA : A.PosDef := Matrix.PosDef.smul_of_pos (hPD Λ) hβ
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

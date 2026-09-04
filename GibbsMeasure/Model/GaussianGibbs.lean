/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianSpecification
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Existence
public import GibbsMeasure.Specification.Transformation

/-!
# Georgii §13.2: Gibbs measures for Gaussian specifications

`GibbsMeasure/Model/GaussianField.lean` (§13.1, (13.1)–(13.13)) and
`GibbsMeasure/Model/GaussianSpecification.lean` ((13.9), (13.10), (13.18), (13.20), (13.21))
start from a Gaussian field `μ` and produce a Gaussian specification `γ^{J,h}` with
`μ ∈ 𝒢(γ^{J,h})`. This file takes Georgii's opposite point of view: for a given `γ^{J,h}` it
studies `𝒢(γ^{J,h})`.

Throughout, `J : S × S → ℝ` is symmetric with **finite row support** — Georgii's finite range
`{j : J(i,j) ≠ 0} ∈ 𝒮`, the standing hypothesis of Theorems (13.26) and (13.28) — and every
`𝒥_Λ = (J(i,j))_{i,j ∈ Λ}` is positive definite. Then `Ω_J = Ω`
(`Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport`), Georgii's "otherwise" branch in
Definition (13.18) is vacuous, and `γ^{J,h}` is `Potential.gaussianSpecification`.

## Main definitions

Georgii's `τ^m` (the display opening §13.2), `τ^m ω = ω + m`, is
`MeasureTheory.GibbsMeasure.spinTranslation m : Transformation S ℝ` (5.1) — the sites are fixed
and the spin at `i` is translated by `m_i` — defined in general in
`GibbsMeasure/Prereqs/Transformation.lean`. `Specification.map` (5.4) and Georgii (5.10)
(`Specification.map_mem_G_map`) then apply verbatim.

* `Potential.gaussianRowForm J hFin i`: **Georgii's `X_i = ∑_{j ∈ S} J(i,j) σ_j`** in the proof of
  Theorem (13.22); a finite sum, since `J` has finite row support.

## Main results

* **Georgii Remark (13.23)(a)**, `Potential.gaussianSpecification_map_spinTranslation`: for
  `m ∈ M_{J,h}`, `τ^m(γ^{J,h'}) = γ^{J,h+h'}`, i.e.
  `γ^{J,h+h'}_Λ(·|τ^m ω) = τ^m(γ^{J,h'}_Λ(·|ω))` for all `Λ` and `ω`. Both sides are Gaussian with
  the same covariance `𝒥_Λ⁻¹` (Proposition (13.13)); the means differ by exactly `m|_Λ`, which is
  the content of `Potential.gaussianMean_add_eq_add` and, underneath it,
  `Potential.gaussianCovMatrix_mulVec_add_gaussianBoundaryField`: for `m ∈ M_{J,h}` the equation
  `h_i + ∑_{j ∈ S} J(i,j) m_j = 0` of (13.21) splits at `Λ` into `𝒥_Λ m|_Λ + J_{Λ,Λᶜ} m = -h|_Λ`.
* **Georgii Remark (13.23)(b)**,
  `Potential.gaussianSpecification_G_eq_image_of_mem_gaussianMeanSet`: for `m ∈ M_{J,h}`,
  `𝒢(γ^{J,h}) = {τ^m(μ) : μ ∈ 𝒢(γ^{J,0})}`. Both inclusions are (13.23)(a) followed by Georgii
  (5.10); the reverse one uses `-m ∈ M_{J,-h}` (`Potential.neg_mem_gaussianMeanSet`).
* **Georgii Remark (13.23)(c)**,
  `Potential.isInvariant_spinTranslation_gaussianSpecification` and
  `Potential.map_add_isGibbsMeasure_of_mem_gaussianMeanSubmodule`: for `m ∈ M_{J,0}` the
  translation `τ^m` is a symmetry of `γ^{J,h}`, so `𝒢(γ^{J,h})` is preserved by it.
* **Georgii Theorem (13.22), (b) ⟹ (a)**,
  `MeasureTheory.GibbsMeasure.georgii_13_22_of_finiteRowSupport`: a Gaussian field `μ` with mean
  `m ∈ M_{J,h}` and covariance `C` satisfying `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}` is a Gibbs
  measure for `γ^{J,h}`. (Georgii's third condition `μ(Ω_J) = 1` is automatic for finite range.)
  The proof is his: the residual `σ_i - ξ_i = J(i,i)⁻¹ (h_i + X_i)` is centred, uncorrelated with
  every `σ_k`, `k ≠ i`, and jointly Gaussian with them
  (`isGaussianProcess_sum_elim_gaussianRowForm`), hence independent of `𝒯_{\{i\}}`
  (`indep_comap_gaussianRowForm_cylinderEvents`); therefore `ξ_i^μ = ξ_i` a.s.
  (`condExpOutside_ae_eq_gaussianCondMean`, Georgii's (13.5)) and `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`
  (`integral_sq_sub_condExpOutside_eq_inv`), which are the hypotheses of Lemma (13.10); Theorem
  (1.33), in the conditional-probability form
  `Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq`
  (`GibbsMeasure/Specification/CondExpGibbs.lean`), concludes. Because `J` has finite range, all
  the sums are finite and Georgii's Corollary (13.A6) — a.s. convergence implies `L²` convergence
  for a Gaussian family, which he needs for infinite range — is not used.
* **Georgii Theorem (13.22), the implication (a) ⟹ (b)**, and hence the full equivalence
  `MeasureTheory.GibbsMeasure.georgii_13_22_iff`: for `J` of finite range, a Gaussian field `μ`
  with mean `m` and covariance `C` is in `𝒢(γ^{J,h})` iff `m ∈ M_{J,h}` and
  `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}`. The necessity is Georgii's proof: Proposition (13.13) at the
  one-point volume gives the first two moments of `γ^{J,h}_{\{i\}}(·|ω)`
  (`integral_eval_gaussianSpecification_singleton`,
  `integral_eval_sq_gaussianSpecification_singleton`), which
  `ProbabilityTheory.Kernel.condExp_ae_eq_integral_kernel` turns into (13.5)
  (`condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure`) and into
  `μ(σ_i² | 𝒯_{\{i\}}) = ξ_i² + J(i,i)⁻¹` (`condExp_sq_ae_eq_of_isGibbsMeasure`); hence
  `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`
  (`integral_sq_sub_condExpOutside_eq_inv_of_isGibbsMeasure`), the residual `σ_i - ξ_i` is
  orthogonal to `L²(𝒯_{\{i\}})` (`integral_mul_sub_gaussianCondMean_eq_zero`), and Georgii's
  computation of `μ((X_i - μ(X_i))(σ_k - m_k))` gives `m ∈ M_{J,h}`
  (`mem_gaussianMeanSet_of_isGibbsMeasure`) and `∑_j J(i,j)C(j,k) = δ_{ik}`
  (`isInverse_covariance_of_isGibbsMeasure`).
* **The last step of Georgii's proofs of Theorems (13.26) and (13.31)**,
  `MeasureTheory.GibbsMeasure.isGibbsMeasure_map_add_of_centered_of_isInverse` and
  `nonempty_G_gaussianSpecification_of_centered_of_isInverse`: if a *centred* Gaussian field
  `μ_C` whose covariance `C` inverts `J` exists, then `τ^m(μ_C) ∈ 𝒢(γ^{J,h})` for every
  `m ∈ M_{J,h}`, so `𝒢(γ^{J,h}) ≠ ∅` whenever `M_{J,h} ≠ ∅`. This is (13.22)(b) ⟹ (a) at `h = 0`
  followed by (13.23)(b), exactly as Georgii closes both proofs.
* **Georgii Theorem (13.26), the sufficiency half, in full**,
  `MeasureTheory.GibbsMeasure.nonempty_G_gaussianSpecification_of_bddAbove`: for `J` symmetric of
  finite range with every `𝒥_Λ` positive definite, `M_{J,h} ≠ ∅` together with Georgii's condition
  (13.27), `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`, implies `𝒢(γ^{J,h}) ≠ ∅`. The chain is Georgii's:
  `MeasureTheory.GibbsMeasure.dotProduct_mulVec_inv_gaussianCovMatrix_mono` (his monotonicity
  display), `inv_gaussianCovMatrix_diag_mono` and `inv_gaussianCovMatrix_pair_mono` (his two
  monotone functions of `Λ`), `two_mul_inv_gaussianCovMatrix_le` (his Cauchy–Schwarz step),
  `exists_tendsto_invGaussianCovEntry` (the limits (13.25) exist),
  `posSemidef_covMatrix_of_tendsto` and `isInverse_of_tendsto_invGaussianCovEntry` (the limit `C`
  is nonnegative definite and inverts `J`), then the item below.
* **Georgii Theorem (13.26), the existence half, granted the limit (13.25)**,
  `MeasureTheory.GibbsMeasure.nonempty_G_gaussianSpecification_of_posSemidef_of_isInverse`: if
  `C : S × S → ℝ` is nonnegative definite and inverts `J`, then `𝒢(γ^{J,h}) ≠ ∅` for every `h`
  with `M_{J,h} ≠ ∅`. The centred Gauss field `μ_C` of Proposition (13.A7) is now available as
  `ProbabilityTheory.gaussianField`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Existence.lean`), so this is the
  previous item with its hypothesis discharged.

## What is *not* proved here, and why

* **Georgii Remark (13.23)(d)** (`M_{J,0} ≠ {0}` implies `𝒢(γ^{J,h}) = ∅` or `ex 𝒢(γ^{J,h})`
  uncountable) needs, besides (c): `ex 𝒢 ≠ ∅` when `𝒢 ≠ ∅` (Theorem (7.26)), which *is* in the
  tree as `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_G_of_isGibbsMeasure`; that `τ^m`
  maps `ex 𝒢` into itself (Remark (7.2)), which is not, though
  `mem_extremePoints_G_iff_isTailTrivial` reduces it to the invariance of the tail σ-algebra under
  `τ^m`; and the injectivity of `t ↦ τ^{t m}(μ)`, which amounts to the fact that no probability
  measure on `ℝ` is invariant under a non-zero translation, also not in the tree.
* **Georgii Theorems (13.24) and (13.31).** (13.24) — the description of `ex 𝒢(γ^{J,h})` as the
  Gaussian fields with covariance `C` of (13.25) and mean in `M_{J,h}`, and hence the necessity
  half of (13.26) — needs Theorem (7.12) (every extreme Gibbs measure is a local limit
  `lim_n γ_{Λ_n}(·|ω)`) together with Proposition (13.A5) (a local limit of Gaussian fields is
  Gaussian, of which `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Limit.lean` has the
  `L¹` version); neither step is attempted here. (13.31) needs the matrices
  `P_V(i,j) = -J(i,j)/J(i,i)` and the Neumann series `C_V = ∑_n P_V^n / J(j,j)`, i.e. a genuinely
  infinite-range development. The potential-theoretic identity of Comment (13.28) is not attempted
  either.

## General lemmas proved in the Mathlib layer for this file

* `ProbabilityTheory.multivariateGaussianPi_map_add_right`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Density.lean`): the pushforward of
  `multivariateGaussianPi A m` along `x ↦ x + v` is `multivariateGaussianPi A (m + v)`.
* `ProbabilityTheory.integral_eval_sq_multivariateGaussianPi` and the integrability lemmas
  `integrable_eval_multivariateGaussianPi`, `integrable_sub_mul_sub_multivariateGaussianPi`,
  `integrable_eval_sq_multivariateGaussianPi` (same file): the second moment
  `∫ x_i² d(multivariateGaussianPi A m) = A⁻¹(i,i) + m_i²`, needed for the conditional variance in
  Theorem (13.22).
* `Matrix.PosDef.two_mul_dotProduct_sub_dotProduct_mulVec_le` and
  `Matrix.PosDef.dotProduct_mulVec_inv_submatrix_le`
  (`GibbsMeasure/Mathlib/LinearAlgebra/Matrix/PosDef.lean`): the variational characterisation
  `t ⬝ᵥ A⁻¹ *ᵥ t = sup_x (2 (t ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x)` of the quadratic form of the inverse of a
  positive definite matrix, and the resulting positive semidefinite inequality
  `(A_{II})⁻¹ ≤ (A⁻¹)_{II}` for a principal submatrix — Georgii's monotonicity display in the
  proof of Theorem (13.26).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal NNReal

noncomputable section

/-! ## The mean of `γ^{J,h}_Λ` under a spin translation -/

namespace Potential

variable {S : Type*} [LinearOrder S] (J : S → S → ℝ)

/-- The boundary field `(J_{Λ,Λᶜ} ω)_i = ∑_{j ∉ Λ} J(i,j) ω_j` is linear in the boundary
condition. -/
lemma gaussianBoundaryField_sub (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S)
    (ω m : S → ℝ) (i : S) :
    gaussianBoundaryField J hFin Λ (ω - m) i =
      gaussianBoundaryField J hFin Λ ω i - gaussianBoundaryField J hFin Λ m i := by
  simp only [gaussianBoundaryField, Pi.sub_apply, mul_sub]
  rw [Finset.sum_sub_distrib]

/-- **The defining property of `M_{J,h}` (13.21), split at `Λ`.** For `m ∈ M_{J,h}` and `J` of
finite row support, `∑_{j ∈ S} J(i,j) m_j = 0 - h_i` decomposes as the inside-`Λ` matrix-vector
product `𝒥_Λ m|_Λ` plus the boundary field `(J_{Λ,Λᶜ} m)_i`. -/
lemma gaussianCovMatrix_mulVec_add_gaussianBoundaryField
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) {h m : S → ℝ} (hm : m ∈ gaussianMeanSet J h)
    (Λ : Finset S) (i : Λ) :
    (gaussianCovMatrix J Λ *ᵥ fun k : Λ ↦ m k.1) i + gaussianBoundaryField J hFin Λ m i.1
      = -h i.1 := by
  classical
  set T : Finset S := (hFin i.1).toFinset with hT
  have hmemT : ∀ j : S, j ∉ T → J i.1 j = 0 := by
    intro j hj
    by_contra hne
    exact hj (by rw [hT, Set.Finite.mem_toFinset]; exact hne)
  have hsum : ∑' j, J i.1 j * m j = ∑ j ∈ T, J i.1 j * m j :=
    tsum_eq_sum fun j hj ↦ by rw [hmemT j hj, zero_mul]
  have hmul : (gaussianCovMatrix J Λ *ᵥ fun k : Λ ↦ m k.1) i = ∑ k ∈ Λ, J i.1 k * m k := by
    change ∑ k : Λ, gaussianCovMatrix J Λ i k * m k.1 = _
    rw [← Finset.sum_coe_sort Λ fun k ↦ J i.1 k * m k]
    rfl
  have h1 : ∑ k ∈ Λ, J i.1 k * m k = ∑ k ∈ T ∩ Λ, J i.1 k * m k := by
    refine (Finset.sum_subset Finset.inter_subset_right fun x hx hxn ↦ ?_).symm
    rw [hmemT x fun hxT ↦ hxn (Finset.mem_inter.2 ⟨hxT, hx⟩), zero_mul]
  have h2 : ∑ k ∈ T \ Λ, J i.1 k * m k + ∑ k ∈ T ∩ Λ, J i.1 k * m k = ∑ k ∈ T, J i.1 k * m k := by
    have := Finset.sum_sdiff (f := fun k ↦ J i.1 k * m k) (Finset.inter_subset_left (s₁ := T)
      (s₂ := Λ))
    rwa [Finset.sdiff_inter_self_left] at this
  have h3 : h i.1 + ∑' j, J i.1 j * m j = 0 := hm.2 i.1
  rw [hmul, h1, gaussianBoundaryField, ← hT]
  linarith

/-- **The mean of `γ^{J,h+h'}_Λ(·|ω)` is the mean of `γ^{J,h'}_Λ(·|ω - m)` shifted by `m`**, for
`m ∈ M_{J,h}`. This is the computation behind Georgii Remark (13.23)(a): the two Gaussian fields
have the same covariance `𝒥_Λ⁻¹` by Proposition (13.13), and their means differ by `m|_Λ`. -/
lemma gaussianMean_add_eq_add (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) {h m : S → ℝ}
    (hm : m ∈ gaussianMeanSet J h) (h' : S → ℝ) (Λ : Finset S) (ω : S → ℝ) :
    gaussianMean J (h + h') hFin Λ ω
      = gaussianMean J h' hFin Λ (ω - m) + fun k : Λ ↦ m k.1 := by
  classical
  set A : Matrix Λ Λ ℝ := gaussianCovMatrix J Λ with hA
  set mv : Λ → ℝ := fun k : Λ ↦ m k.1 with hmv
  have hdet : A.det ≠ 0 := (hPD Λ).det_pos.ne'
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hdet.isUnit
  have key : (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ m i.1) = -(A *ᵥ mv) := by
    funext i
    have := gaussianCovMatrix_mulVec_add_gaussianBoundaryField J hFin hm Λ i
    simp only [Pi.neg_apply]
    linarith
  have hsplit : (fun i : Λ ↦ (h + h') i.1 + gaussianBoundaryField J hFin Λ ω i.1)
      = (fun i : Λ ↦ h' i.1 + gaussianBoundaryField J hFin Λ (ω - m) i.1)
        + (fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ m i.1) := by
    funext i
    simp only [Pi.add_apply]
    rw [gaussianBoundaryField_sub]
    ring
  rw [gaussianMean, gaussianMean, hsplit, key, Matrix.mulVec_add, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  abel


/-! ## Georgii Remark (13.23)(a): the spin translation acts on Gaussian specifications -/

/-- **Georgii Remark (13.23)(a).** For `m ∈ M_{J,h}`,
`γ^{J,h+h'}_Λ(·|τ^m ω) = τ^m(γ^{J,h'}_Λ(·|ω))` for all `Λ` and all `ω` — equivalently, in the
notation of Georgii (5.4), `τ^m(γ^{J,h'}) = γ^{J,h+h'}`. Both sides are, by Proposition (13.13),
Gaussian fields with the same covariance `𝒥_Λ⁻¹`; their means differ by exactly `m|_Λ`
(`Potential.gaussianMean_add_eq_add`), which is Georgii's "immediately checked, using the
explicit expression for these mean values". Stated for `J` of finite row support, where
`Ω_J = Ω` and Georgii's restriction `ω ∈ Ω_J` is vacuous. -/
theorem gaussianSpecification_map_spinTranslation [Countable S]
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β)
    {h m : S → ℝ} (hm : m ∈ gaussianMeanSet J h) (h' : S → ℝ) :
    (gaussianSpecification J h' hSymm hFin hPD β hβ).map
        (MeasureTheory.GibbsMeasure.spinTranslation m)
      = gaussianSpecification J (h + h') hSymm hFin hPD β hβ := by
  classical
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  set A : Matrix Λ Λ ℝ := β • gaussianCovMatrix J Λ with hAdef
  set M : Λ → ℝ := gaussianMean J h' hFin Λ (ω - m) with hMdef
  set mv : Λ → ℝ := fun k : Λ ↦ m k.1 with hmvdef
  have hΛ : Λ.map (MeasureTheory.GibbsMeasure.spinTranslation m).sites.symm.toEmbedding = Λ := by
    simp [MeasureTheory.GibbsMeasure.spinTranslation]
  have hτ : (MeasureTheory.GibbsMeasure.spinTranslation m).toFun = fun x : S → ℝ ↦ x + m :=
    funext (MeasureTheory.GibbsMeasure.spinTranslation_toFun m)
  have hcomp : (fun x : S → ℝ ↦ x + m) ∘ juxt (Λ : Set S) (ω - m)
      = juxt (Λ : Set S) ω ∘ fun ζ : Λ → ℝ ↦ ζ + mv := by
    funext ζ i
    by_cases hi : i ∈ (Λ : Set S)
    · simp [juxt_apply_of_mem hi, hmvdef]
    · simp [juxt_apply_of_not_mem hi]
  rw [Specification.map_apply, hΛ, MeasureTheory.GibbsMeasure.spinTranslation_inv_toFun, hτ,
    gaussianSpecification_apply, gaussianSpecification_apply,
    Measure.map_map (measurable_add_const m) Measurable.juxt,
    gaussianMean_add_eq_add J hFin hPD hm h' Λ ω, ← hMdef, ← hmvdef,
    ← multivariateGaussianPi_map_add_right A M mv,
    Measure.map_map Measurable.juxt (measurable_add_const mv), hcomp]


omit [LinearOrder S] in
/-- `M_{J,-h} = -M_{J,h}`: the affine system (13.21) is linear in `(h, m)`. -/
lemma neg_mem_gaussianMeanSet {h m : S → ℝ} (hm : m ∈ gaussianMeanSet J h) :
    -m ∈ gaussianMeanSet J (-h) := by
  refine ⟨(gaussianConvergenceSubmodule J).neg_mem hm.1, fun i ↦ ?_⟩
  have hsplit : (fun j ↦ J i j * (-m) j) = fun j ↦ -(J i j * m j) := by
    funext j; simp
  rw [Pi.neg_apply, hsplit, tsum_neg]
  have := hm.2 i
  linarith

/-- **Georgii Remark (13.23)(c), the symmetry.** For `m ∈ M_{J,0}` the spin translation `τ^m` is a
symmetry of `γ^{J,h}`, for every external field `h`: this is (13.23)(a) with `h := 0`. -/
theorem isInvariant_spinTranslation_gaussianSpecification [Countable S]
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β) (h : S → ℝ)
    {m : S → ℝ} (hm : m ∈ gaussianMeanSet J 0) :
    Specification.IsInvariant (MeasureTheory.GibbsMeasure.spinTranslation m)
      (gaussianSpecification J h hSymm hFin hPD β hβ) := by
  have := gaussianSpecification_map_spinTranslation J hSymm hFin hPD β hβ hm h
  rwa [zero_add] at this

/-- **Georgii Remark (13.23)(c).** `𝒢(γ^{J,h})` is preserved by the spin translations `τ^m` with
`m ∈ M_{J,0}`. -/
theorem map_add_isGibbsMeasure_of_mem_gaussianMeanSubmodule [Countable S]
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β) (h : S → ℝ)
    {m : S → ℝ} (hm : m ∈ gaussianMeanSet J 0) {μ : Measure (S → ℝ)} [IsProbabilityMeasure μ]
    (hμ : (gaussianSpecification J h hSymm hFin hPD β hβ).IsGibbsMeasure μ) :
    (gaussianSpecification J h hSymm hFin hPD β hβ).IsGibbsMeasure (μ.map fun x ↦ x + m) := by
  have hinv := isInvariant_spinTranslation_gaussianSpecification J hSymm hFin hPD β hβ h hm
  have := hinv.map_isGibbsMeasure hμ
  rwa [funext (MeasureTheory.GibbsMeasure.spinTranslation_toFun m)] at this

/-- **Georgii Remark (13.23)(b).** For each `m ∈ M_{J,h}`,
`𝒢(γ^{J,h}) = {τ^m(μ) : μ ∈ 𝒢(γ^{J,0})}`. -/
theorem gaussianSpecification_G_eq_image_of_mem_gaussianMeanSet [Countable S]
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β)
    {h m : S → ℝ} (hm : m ∈ gaussianMeanSet J h) :
    MeasureTheory.GibbsMeasure.G (gaussianSpecification J h hSymm hFin hPD β hβ)
      = (fun μ : Measure (S → ℝ) ↦ μ.map fun x ↦ x + m) ''
          MeasureTheory.GibbsMeasure.G (gaussianSpecification J 0 hSymm hFin hPD β hβ) := by
  have hmap0 : (gaussianSpecification J 0 hSymm hFin hPD β hβ).map
      (MeasureTheory.GibbsMeasure.spinTranslation m)
      = gaussianSpecification J h hSymm hFin hPD β hβ := by
    have := gaussianSpecification_map_spinTranslation J hSymm hFin hPD β hβ hm 0
    rwa [add_zero] at this
  have hmaph : (gaussianSpecification J h hSymm hFin hPD β hβ).map
      (MeasureTheory.GibbsMeasure.spinTranslation (-m))
      = gaussianSpecification J 0 hSymm hFin hPD β hβ := by
    have := gaussianSpecification_map_spinTranslation J hSymm hFin hPD β hβ
      (neg_mem_gaussianMeanSet J hm) h
    rwa [neg_add_cancel] at this
  have hτ : ∀ v : S → ℝ, (MeasureTheory.GibbsMeasure.spinTranslation v).toFun
      = fun x : S → ℝ ↦ x + v := fun v ↦
    funext (MeasureTheory.GibbsMeasure.spinTranslation_toFun v)
  refine Set.Subset.antisymm (fun ν hν ↦ ?_) (fun ν hν ↦ ?_)
  · refine ⟨ν.map fun x ↦ x + -m, ?_, ?_⟩
    · have := Specification.map_mem_G_map (MeasureTheory.GibbsMeasure.spinTranslation (-m)) hν
      rwa [hmaph, hτ] at this
    · show Measure.map (fun x : S → ℝ ↦ x + m) (Measure.map (fun x : S → ℝ ↦ x + -m) ν) = ν
      rw [Measure.map_map (measurable_add_const m) (measurable_add_const (-m)),
        show ((fun x : S → ℝ ↦ x + m) ∘ fun x : S → ℝ ↦ x + -m) = id from by funext x; simp,
        Measure.map_id]
  · obtain ⟨μ, hμ, rfl⟩ := hν
    show Measure.map (fun x : S → ℝ ↦ x + m) μ ∈ _
    have := Specification.map_mem_G_map (MeasureTheory.GibbsMeasure.spinTranslation m) hμ
    rwa [hmap0, hτ] at this


/-! ## Georgii's row form `X_i = ∑_j J(i,j) σ_j` (proof of (13.22)) -/

omit [LinearOrder S] in
/-- **Georgii's `X_i` in the proof of Theorem (13.22)**: the linear form
`X_i(ω) = ∑_{j ∈ S} J(i,j) ω_j`. For `J` of finite row support this is the finite sum over the
support of the `i`-th row, so no convergence hypothesis on `ω` is needed. -/
def gaussianRowForm (J : S → S → ℝ) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (i : S)
    (ω : S → ℝ) : ℝ :=
  ∑ j ∈ (hFin i).toFinset, J i j * ω j

omit [LinearOrder S] in
lemma gaussianRowForm_eq_tsum (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (i : S) (ω : S → ℝ) :
    gaussianRowForm J hFin i ω = ∑' j, J i j * ω j := by
  refine (tsum_eq_sum fun j hj ↦ ?_).symm
  rw [show J i j = 0 from by
    by_contra hne
    exact hj ((hFin i).mem_toFinset.2 hne), zero_mul]

/-- The row form is the boundary field of `GaussianField.lean` at `Λ = ∅`: `X_i = (J_{∅,S} ω)_i`.
Recorded so that the two finite-sum objects of this development are visibly the same function;
`gaussianRowForm` exists under its own name because it is Georgii's `X_i`, a full row sum and not
a boundary term. -/
lemma gaussianRowForm_eq_gaussianBoundaryField_empty
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (i : S) (ω : S → ℝ) :
    gaussianRowForm J hFin i ω = gaussianBoundaryField J hFin ∅ ω i := by
  rw [gaussianRowForm, gaussianBoundaryField, Finset.sdiff_empty]

omit [LinearOrder S] in
lemma measurable_gaussianRowForm (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (i : S) :
    Measurable (gaussianRowForm J hFin i) :=
  Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).const_mul _

end Potential

/-! ## Georgii Theorem (13.22), (b) ⟹ (a), for `J` of finite range

Georgii's proof: for `m ∈ M_{J,h}` and `C` an inverse of `J`, the residual
`σ_i - ξ_i = J(i,i)⁻¹ (h_i + X_i)`, `X_i = ∑_j J(i,j) σ_j`, is centred, uncorrelated with every
`σ_k`, `k ≠ i`, hence — being jointly Gaussian with them — independent of `𝒯_{\{i\}}`; therefore
`ξ_i^μ = ξ_i` a.s. ((13.5)) and `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`. Lemma (13.10) and Theorem (1.33)
then give `μ ∈ 𝒢(γ^{J,h})`. For `J` of finite range the sums are finite, so Corollary (13.A6)
(a.s. convergence implies `L²` convergence for a Gaussian family), which Georgii needs for
infinite range, is not used. -/

namespace MeasureTheory.GibbsMeasure

section Theorem13_22

variable {S : Type*} [Countable S] [DecidableEq S] {μ : Measure (S → ℝ)} {J : S → S → ℝ}
  {h : S → ℝ} (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
  (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)

include hFin hμ

omit [Countable S] [DecidableEq S] in
/-- The row form `X_i = ∑_j J(i,j) σ_j` of a Gaussian field is square integrable. -/
lemma memLp_two_gaussianRowForm (i : S) : MemLp (Potential.gaussianRowForm J hFin i) 2 μ := by
  have hfun : Potential.gaussianRowForm J hFin i
      = ∑ j ∈ (hFin i).toFinset, fun ω : S → ℝ ↦ J i j * ω j := by
    funext ω
    simp [Potential.gaussianRowForm, Finset.sum_apply]
  rw [hfun]
  exact memLp_finsetSum' _ fun j _ ↦ (memLp_two_eval hμ j).const_mul _

omit [Countable S] [DecidableEq S] in
/-- `μ(X_i) = ∑_j J(i,j) m_j`, the mean of the row form. -/
lemma integral_gaussianRowForm (i : S) :
    ∫ ω, Potential.gaussianRowForm J hFin i ω ∂μ
      = Potential.gaussianRowForm J hFin i fun j ↦ ∫ ω, ω j ∂μ := by
  have hP := hμ.isProbabilityMeasure
  simp only [Potential.gaussianRowForm]
  rw [integral_finsetSum _ fun j _ ↦
    ((memLp_two_eval hμ j).integrable one_le_two).const_mul _]
  exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _

omit [Countable S] [DecidableEq S] in
/-- `cov(X_i, σ_k) = ∑_j J(i,j) C(j,k)`, the covariance of the row form with a single spin. -/
lemma covariance_gaussianRowForm_eval (i k : S) :
    cov[Potential.gaussianRowForm J hFin i, fun ω : S → ℝ ↦ ω k; μ]
      = ∑' j, J i j * cov[fun ω : S → ℝ ↦ ω j, fun ω : S → ℝ ↦ ω k; μ] := by
  have hP := hμ.isProbabilityMeasure
  have hstep : cov[Potential.gaussianRowForm J hFin i, fun ω : S → ℝ ↦ ω k; μ]
      = ∑ j ∈ (hFin i).toFinset, J i j * cov[fun ω : S → ℝ ↦ ω j, fun ω : S → ℝ ↦ ω k; μ] := by
    rw [show Potential.gaussianRowForm J hFin i
        = fun ω : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset, J i j * ω j from rfl,
      covariance_fun_sum_left' (X := fun j (ω : S → ℝ) ↦ J i j * ω j)
        (fun j _ ↦ (memLp_two_eval hμ j).const_mul _) (memLp_two_eval hμ k)]
    exact Finset.sum_congr rfl fun j _ ↦ covariance_const_mul_left _
  rw [hstep]
  refine (tsum_eq_sum fun j hj ↦ ?_).symm
  rw [show J i j = 0 from by
    by_contra hne
    exact hj ((hFin i).mem_toFinset.2 hne), zero_mul]

omit [Countable S] [DecidableEq S] in
/-- **The row form is jointly Gaussian with the spins off `i`**: both are continuous linear images
of finitely many coordinates of the Gaussian process `(σ_j)_{j ∈ S}`. -/
lemma isGaussianProcess_sum_elim_gaussianRowForm (i : S) :
    ProbabilityTheory.IsGaussianProcess
      (Sum.elim (fun (_ : Unit) ↦ Potential.gaussianRowForm J hFin i)
        fun (k : ({i}ᶜ : Set S)) (ω : S → ℝ) ↦ ω k) μ := by
  refine hμ.of_isGaussianProcess fun r ↦ ?_
  cases r with
  | inl _ =>
    refine ⟨(hFin i).toFinset,
      { toFun x := ∑ j : ((hFin i).toFinset : Finset S), J i j.1 * x j
        map_add' x y := by
          simp only [Pi.add_apply, mul_add]
          exact Finset.sum_add_distrib
        map_smul' c x := by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring }, fun ω ↦ ?_⟩
    change Potential.gaussianRowForm J hFin i ω = ∑ j : ((hFin i).toFinset : Finset S),
      J i j.1 * ω j.1
    rw [Potential.gaussianRowForm, ← Finset.sum_coe_sort (hFin i).toFinset
      fun j ↦ J i j * ω j]
  | inr k =>
    exact ⟨{(k : S)}, { toFun x := x ⟨(k : S), Finset.mem_singleton_self _⟩
                        map_add' x y := by simp
                        map_smul' c x := by simp }, fun ω ↦ rfl⟩


omit [Countable S] hμ in
/-- Georgii's `ξ_i` as a finite linear combination of the spins `σ_j`, `j ≠ i`, for `J` of finite
row support. -/
lemma gaussianCondMean_eq_sum (i : S) (ω : S → ℝ) :
    gaussianCondMean J h i ω
      = -(J i i)⁻¹ * (h i + ∑ j ∈ (hFin i).toFinset.erase i, J i j * ω j) := by
  have hts : ∑' j, (if j = i then (0 : ℝ) else J i j * ω j)
      = ∑ j ∈ (hFin i).toFinset.erase i, J i j * ω j := by
    rw [tsum_eq_sum (s := (hFin i).toFinset.erase i) fun j hj ↦ ?_]
    · exact Finset.sum_congr rfl fun j hj ↦ by simp [(Finset.mem_erase.1 hj).1]
    · by_cases hji : j = i
      · simp [hji]
      · have hJ0 : J i j = 0 := by
          by_contra hne
          exact hj (Finset.mem_erase.2 ⟨hji, (hFin i).mem_toFinset.2 hne⟩)
        simp [hji, hJ0]
  rw [gaussianCondMean, hts]

omit [Countable S] hμ in
/-- Georgii's `ξ_i` is `𝒯_{\{i\}}`-measurable. -/
lemma measurable_cylinderEvents_gaussianCondMean (i : S) :
    Measurable[cylinderEvents ({i}ᶜ : Set S)] (gaussianCondMean J h i) := by
  rw [funext (gaussianCondMean_eq_sum hFin i)]
  refine Measurable.const_mul (Measurable.const_add ?_ _) _
  refine Finset.measurable_sum _ fun j hj ↦ ?_
  exact (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({i}ᶜ : Set S))
    (by simpa using (Finset.mem_erase.1 hj).1)).const_mul _

variable (hC : ∀ i k, ∑' j, J i j * cov[fun ω : S → ℝ ↦ ω j, fun ω : S → ℝ ↦ ω k; μ]
    = if i = k then 1 else 0)

include hC

omit [Countable S] in
/-- **The row form `X_i` is independent of `𝒯_{\{i\}}`** when `C` is an inverse of `J`: it is
uncorrelated with every `σ_k`, `k ≠ i`, and jointly Gaussian with them. -/
lemma indep_comap_gaussianRowForm_cylinderEvents (i : S) :
    ProbabilityTheory.Indep
      (MeasurableSpace.comap (Potential.gaussianRowForm J hFin i) inferInstance)
      (cylinderEvents ({i}ᶜ : Set S)) μ := by
  have hP := hμ.isProbabilityMeasure
  have hcov : ∀ (_ : Unit) (k : ({i}ᶜ : Set S)),
      cov[Potential.gaussianRowForm J hFin i, fun ω : S → ℝ ↦ ω k; μ] = 0 := by
    intro _ k
    have hki : (k : S) ≠ i := k.2
    have hik : i ≠ (k : S) := fun hh ↦ hki hh.symm
    rw [covariance_gaussianRowForm_eval hFin hμ i (k : S), hC i (k : S)]
    simp [hik]
  have h1 := (isGaussianProcess_sum_elim_gaussianRowForm hFin hμ i).indepFun_of_covariance_eq_zero
    (fun _ ↦ (Potential.measurable_gaussianRowForm J hFin i).aemeasurable)
    (fun k ↦ (measurable_pi_apply (k : S)).aemeasurable) hcov
  have h2 := h1.comp (measurable_pi_apply ()) measurable_id
  rw [IndepFun_iff_Indep] at h2
  rw [cylinderEvents_eq_comap_restrict]
  exact h2

omit [Countable S] in
/-- `cov(X_i, X_i) = J(i,i)` when `C` is an inverse of `J`. -/
lemma covariance_gaussianRowForm_self (i : S) (hJii : J i i ≠ 0) :
    cov[Potential.gaussianRowForm J hFin i, Potential.gaussianRowForm J hFin i; μ] = J i i := by
  have hP := hμ.isProbabilityMeasure
  have hstep : cov[Potential.gaussianRowForm J hFin i, Potential.gaussianRowForm J hFin i; μ]
      = ∑ j ∈ (hFin i).toFinset,
          J i j * cov[fun ω : S → ℝ ↦ ω j, Potential.gaussianRowForm J hFin i; μ] := by
    rw [show Potential.gaussianRowForm J hFin i
        = fun ω : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset, J i j * ω j from rfl]
    rw [covariance_fun_sum_left' (X := fun j (ω : S → ℝ) ↦ J i j * ω j)
      (fun j _ ↦ (memLp_two_eval hμ j).const_mul _)
      (show MemLp (fun ω : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset, J i j * ω j) 2 μ from
        memLp_two_gaussianRowForm hFin hμ i)]
    exact Finset.sum_congr rfl fun j _ ↦ covariance_const_mul_left _
  rw [hstep]
  have hterm : ∀ j : S, J i j * cov[fun ω : S → ℝ ↦ ω j,
      Potential.gaussianRowForm J hFin i; μ] = if j = i then J i i else 0 := by
    intro j
    rw [covariance_comm, covariance_gaussianRowForm_eval hFin hμ i j, hC i j]
    by_cases hji : j = i
    · subst hji; simp
    · have hij : i ≠ j := fun hh ↦ hji hh.symm
      simp [hij, hji]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_ite_eq' ((hFin i).toFinset) i
    (fun _ ↦ J i i)]
  simp [(hFin i).mem_toFinset.2 hJii]

/-- **Georgii's equation (13.5), derived from (13.22)(b).** For a Gaussian field with mean
`m ∈ M_{J,h}` and covariance `C` an inverse of `J`, the conditional expectation `ξ_i^μ` is the
explicit affine function `ξ_i = -J(i,i)⁻¹ (h_i + ∑_{j ≠ i} J(i,j) σ_j)`. -/
lemma condExpOutside_ae_eq_gaussianCondMean
    (hm : (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h) (i : S) (hJii : J i i ≠ 0) :
    condExpOutside μ i =ᵐ[μ] gaussianCondMean J h i := by
  have hP := hμ.isProbabilityMeasure
  set X := Potential.gaussianRowForm J hFin i with hXdef
  set W : (S → ℝ) → ℝ := fun ω ↦ (J i i)⁻¹ * (h i + X ω) with hWdef
  have hXmeas : Measurable X := Potential.measurable_gaussianRowForm J hFin i
  have hXL2 : MemLp X 2 μ := memLp_two_gaussianRowForm hFin hμ i
  have hXint : ∫ ω, X ω ∂μ = -h i := by
    rw [hXdef, integral_gaussianRowForm hFin hμ i, Potential.gaussianRowForm_eq_tsum J hFin i]
    have := hm.2 i
    linarith
  have hWL2 : MemLp W 2 μ := ((memLp_const (h i)).add hXL2).const_mul _
  have hWmean : ∫ ω, W ω ∂μ = 0 := by
    rw [hWdef]
    rw [integral_const_mul, integral_add (integrable_const _) (hXL2.integrable one_le_two),
      hXint, integral_const]
    simp
  have hdec : (fun ω : S → ℝ ↦ ω i) = gaussianCondMean J h i + W := by
    funext ω
    have hω : ω ∈ Potential.gaussianConvergenceSet J := by
      rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]
      trivial
    simp only [Pi.add_apply, hWdef, hXdef, Potential.gaussianRowForm_eq_tsum J hFin i,
      gaussianCondMean_eq_of_mem hJii hω]
    ring
  have hξmeas : Measurable[cylinderEvents ({i}ᶜ : Set S)] (gaussianCondMean J h i) :=
    measurable_cylinderEvents_gaussianCondMean hFin i
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := by
    have : gaussianCondMean J h i = (fun ω : S → ℝ ↦ ω i) - W := by
      rw [hdec]; abel
    rw [this]
    exact (memLp_two_eval hμ i).sub hWL2
  have hcondW : μ[W | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] fun _ ↦ (0 : ℝ) := by
    have hWsm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] W :=
      ((measurable_const_mul (J i i)⁻¹).comp
        ((measurable_const_add (h i)).comp (measurable_iff_comap_le.2 le_rfl))).stronglyMeasurable
    have := MeasureTheory.condExp_indep_eq (μ := μ) (f := W) hXmeas.comap_le cylinderEvents_le_pi
      hWsm (indep_comap_gaussianRowForm_cylinderEvents hFin hμ hC i)
    rwa [hWmean] at this
  have hcondξ : μ[gaussianCondMean J h i | cylinderEvents ({i}ᶜ : Set S)]
      = gaussianCondMean J h i :=
    condExp_of_stronglyMeasurable cylinderEvents_le_pi hξmeas.stronglyMeasurable
      (hξL2.integrable one_le_two)
  have hsplit : condExpOutside μ i
      =ᵐ[μ] μ[gaussianCondMean J h i | cylinderEvents ({i}ᶜ : Set S)]
        + μ[W | cylinderEvents ({i}ᶜ : Set S)] := by
    unfold condExpOutside
    rw [hdec]
    exact condExp_add (hξL2.integrable one_le_two) (hWL2.integrable one_le_two) _
  filter_upwards [hsplit, hcondW] with ω h1 h3
  rw [h1, Pi.add_apply, hcondξ, h3, add_zero]

/-- **The conditional variance of a single spin is `J(i,i)⁻¹`**, the second hypothesis of
Lemma (13.10), derived from (13.22)(b). -/
lemma integral_sq_sub_condExpOutside_eq_inv
    (hm : (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h) (i : S) (hJii : J i i ≠ 0) :
    ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹ := by
  have hP := hμ.isProbabilityMeasure
  set X := Potential.gaussianRowForm J hFin i with hXdef
  set W : (S → ℝ) → ℝ := fun ω ↦ (J i i)⁻¹ * (h i + X ω) with hWdef
  have hXL2 : MemLp X 2 μ := memLp_two_gaussianRowForm hFin hμ i
  have hXint : ∫ ω, X ω ∂μ = -h i := by
    rw [hXdef, integral_gaussianRowForm hFin hμ i, Potential.gaussianRowForm_eq_tsum J hFin i]
    have := hm.2 i
    linarith
  have hWL2 : MemLp W 2 μ := ((memLp_const (h i)).add hXL2).const_mul _
  have hWmean : ∫ ω, W ω ∂μ = 0 := by
    rw [hWdef, integral_const_mul,
      integral_add (integrable_const _) (hXL2.integrable one_le_two), hXint, integral_const]
    simp
  have hdec : ∀ ω : S → ℝ, ω i - gaussianCondMean J h i ω = W ω := by
    intro ω
    have hω : ω ∈ Potential.gaussianConvergenceSet J := by
      rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]
      trivial
    simp only [hWdef, hXdef, Potential.gaussianRowForm_eq_tsum J hFin i,
      gaussianCondMean_eq_of_mem hJii hω]
    ring
  have hcovWW : cov[W, W; μ] = (J i i)⁻¹ := by
    rw [hWdef, covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_add_left (hXL2.integrable one_le_two),
      covariance_const_add_right (hXL2.integrable one_le_two), hXdef,
      covariance_gaussianRowForm_self hFin hμ hC i hJii]
    field_simp
  have hae : ∀ᵐ ω ∂μ, (ω i - condExpOutside μ i ω) ^ 2 = W ω * W ω := by
    filter_upwards [condExpOutside_ae_eq_gaussianCondMean hFin hμ hC hm i hJii] with ω hω
    rw [hω, hdec ω, sq]
  rw [integral_congr_ae hae, ← hcovWW, covariance_eq_sub hWL2 hWL2, hWmean]
  simp [Pi.mul_apply]


/-- **Georgii Theorem (13.22), the implication (b) ⟹ (a), for `J` of finite range.** Let `μ` be a
Gaussian field with mean `m` and covariance function `C`, let `J` be symmetric with every `𝒥_Λ`
positive definite (Georgii's positive definiteness) and of finite row support, and let `h ∈ Ω`.
If `m ∈ M_{J,h}` and `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}` for all `i, k`, then `μ ∈ 𝒢(γ^{J,h})`.
(Georgii's remaining hypothesis `μ(Ω_J) = 1` is automatic here: `Ω_J = Ω` for finite range.)

The proof is Georgii's: `σ_i - ξ_i = J(i,i)⁻¹ (h_i + X_i)` is centred
(`integral_gaussianRowForm`), uncorrelated with every `σ_k`, `k ≠ i`, and jointly Gaussian with
them, hence independent of `𝒯_{\{i\}}` (`indep_comap_gaussianRowForm_cylinderEvents`); therefore
`ξ_i^μ = ξ_i` a.s. (`condExpOutside_ae_eq_gaussianCondMean`, Georgii's (13.5)) and
`μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹` (`integral_sq_sub_condExpOutside_eq_inv`). Lemma (13.10) —
in the form `condExp_indicator_ae_eq_gaussianSpecification_singleton` — and Theorem (1.33) —
in the form `Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq` — conclude. -/
theorem georgii_13_22_of_finiteRowSupport [LinearOrder S] (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (hm : (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h) :
    (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ := by
  classical
  have hP := hμ.isProbabilityMeasure
  have hJii : ∀ i : S, J i i ≠ 0 := fun i ↦ by
    have := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
    exact ne_of_gt this
  have hvar : ∀ i, ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹ :=
    fun i ↦ integral_sq_sub_condExpOutside_eq_inv hFin hμ hC hm i (hJii i)
  have h135 : ∀ i, ∀ᵐ ω ∂μ,
      ω i - condExpOutside μ i ω = (J i i)⁻¹ * (h i + ∑' j, J i j * ω j) := by
    intro i
    filter_upwards [condExpOutside_ae_eq_gaussianCondMean hFin hμ hC hm i (hJii i)] with ω hω
    have hωΩ : ω ∈ Potential.gaussianConvergenceSet J := by
      rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]
      trivial
    rw [hω, gaussianCondMean_eq_of_mem (hJii i) hωΩ]
    ring
  have := Potential.isPotential_gaussianPotential J h
  have := Potential.isFiniteRange_gaussianPotential J h hSymm hFin
  have hadm := Potential.isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor J h
    hSymm hFin hPD 1 one_pos
  have hEq : Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos =
      Specification.lambdaSpecification (S := S) (E := ℝ) volume
        ((Potential.gaussianPotential J h).boltzmannFactor 1)
        (Potential.isPremodifier_boltzmannFactor 1) hadm := rfl
  rw [hEq]
  refine Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq volume _
    (fun Λ ω ↦ (Potential.boltzmannFactor_pos 1 Λ ω).ne')
    (fun Λ ω ↦ Potential.boltzmannFactor_ne_top 1 Λ ω) hadm ?_
  intro i A hA
  rw [← hEq]
  exact condExp_indicator_ae_eq_gaussianSpecification_singleton hSymm hFin hPD hμ hvar h135 i hA


/-- **The last step of Georgii's proofs of Theorems (13.26) and (13.31).** Let `J` be symmetric of
finite range with every `𝒥_Λ` positive definite, and suppose a *centred* Gaussian field `μ_C` with
covariance `C` an inverse of `J` exists (this is what Georgii gets from (13.A7) once the limits
(13.25) are shown to exist and to invert `J`). Then for every `h` and every `m ∈ M_{J,h}` the
translate `τ^m(μ_C)` is a Gibbs measure for `γ^{J,h}`; in particular `𝒢(γ^{J,h}) ≠ ∅` as soon as
`M_{J,h} ≠ ∅`.

Georgii: "`μ_C` satisfies condition (b) of Theorem (13.22) with `h = 0`. Thus
`μ_C ∈ 𝒢(γ^{J,0})`, and Remark (13.23)(b) implies that `τ^m(μ_C) ∈ 𝒢(γ^{J,h})` for each
`m ∈ M_{J,h}`." -/
theorem isGibbsMeasure_map_add_of_centered_of_isInverse [LinearOrder S]
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (hcentred : ∀ j, ∫ ω, ω j ∂μ = 0) {m : S → ℝ} (hm : m ∈ Potential.gaussianMeanSet J h) :
    (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure
      (μ.map fun x ↦ x + m) := by
  have hP := hμ.isProbabilityMeasure
  have hzero : (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J (0 : S → ℝ) := by
    refine ⟨?_, fun i ↦ ?_⟩
    · have : (fun j ↦ ∫ ω, ω j ∂μ) = (0 : S → ℝ) := funext hcentred
      rw [this]
      exact (Potential.gaussianConvergenceSubmodule J).zero_mem
    · simp [hcentred]
  have h0 : (Potential.gaussianSpecification J (0 : S → ℝ) hSymm hFin hPD 1
      one_pos).IsGibbsMeasure μ :=
    georgii_13_22_of_finiteRowSupport hFin hμ hC hSymm hPD hzero
  have hmem : μ.map (fun x ↦ x + m)
      ∈ MeasureTheory.GibbsMeasure.G (Potential.gaussianSpecification J h hSymm hFin hPD 1
        one_pos) := by
    rw [Potential.gaussianSpecification_G_eq_image_of_mem_gaussianMeanSet J hSymm hFin hPD 1
      one_pos hm]
    exact ⟨μ, ⟨inferInstance, h0⟩, rfl⟩
  exact hmem.2

/-- **`𝒢(γ^{J,h}) ≠ ∅`** under the hypotheses of
`isGibbsMeasure_map_add_of_centered_of_isInverse`: the existence half of Georgii's Theorems
(13.26) and (13.31), granted the centred Gauss field `μ_C` of (13.A7). -/
theorem nonempty_G_gaussianSpecification_of_centered_of_isInverse [LinearOrder S]
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (hcentred : ∀ j, ∫ ω, ω j ∂μ = 0) {m : S → ℝ} (hm : m ∈ Potential.gaussianMeanSet J h) :
    (MeasureTheory.GibbsMeasure.G
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty := by
  have hP := hμ.isProbabilityMeasure
  refine ⟨μ.map fun x ↦ x + m, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map (measurable_add_const m).aemeasurable
  · exact isGibbsMeasure_map_add_of_centered_of_isInverse hFin hμ hC hSymm hPD hcentred hm

end Theorem13_22

section Theorem13_26

variable {S : Type*} [Countable S] [DecidableEq S] [LinearOrder S] {J : S → S → ℝ} {h : S → ℝ}

/-- **Georgii Theorem (13.26), the existence half, with the limit (13.25) supplied.** Let `J` be
symmetric of finite range with every `𝒥_Λ` positive definite, and let `C : S × S → ℝ` be a
nonnegative definite symmetric function (every finite submatrix `(C(i,j))_{i,j ∈ I}` is positive
semidefinite) which is an inverse of `J` in the sense of Theorem (13.22),
`∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}`. Then `𝒢(γ^{J,h}) ≠ ∅` for every `h` with `M_{J,h} ≠ ∅`.

This is Georgii's closing paragraph of the proof of (13.26): the centred Gauss field `μ_C` with
covariance `C` exists by Proposition (13.A7)
(`ProbabilityTheory.gaussianField`, `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/
Existence.lean`), it satisfies condition (b) of Theorem (13.22) with `h = 0`, and Remark (13.23)(b)
transports it to `τ^m(μ_C) ∈ 𝒢(γ^{J,h})`.

What is *not* supplied here is the earlier half of Georgii's proof, namely that his hypothesis
(13.27), `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`, produces such a `C` as the limit (13.25): that is the
monotonicity argument `∑_{i,j ∈ Λ} 𝒥_Λ⁻¹(i,j) t_i t_j ≤ ∑_{i,j ∈ Λ} 𝒥_Δ⁻¹(i,j) t_i t_j` for
`Λ ⊆ Δ`, which is a statement about the specification `γ^{J,h}` and not about Gauss fields. -/
theorem nonempty_G_gaussianSpecification_of_posSemidef_of_isInverse
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (C : S → S → ℝ) (hCpsd : ∀ I : Finset S, (ProbabilityTheory.covMatrix C I).PosSemidef)
    (hCinv : ∀ i k, ∑' j, J i j * C j k = if i = k then 1 else 0)
    {m : S → ℝ} (hm : m ∈ Potential.gaussianMeanSet J h) :
    (MeasureTheory.GibbsMeasure.G
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty := by
  refine nonempty_G_gaussianSpecification_of_centered_of_isInverse
    (μ := ProbabilityTheory.gaussianField C hCpsd) hFin
    (ProbabilityTheory.isGaussianProcess_gaussianField hCpsd) ?_ hSymm hPD
    (ProbabilityTheory.integral_eval_gaussianField hCpsd) hm
  intro i k
  simpa only [ProbabilityTheory.covariance_eval_gaussianField hCpsd] using hCinv i k

end Theorem13_26

/-! ## Georgii Theorem (13.22), (a) ⟹ (b), for `J` of finite range

The two ingredients Georgii uses are the first two moments of `γ^{J,h}_{\{i\}}(·|ω)`, read off
Proposition (13.13) at the one-point volume `Λ = {i}`: the mean is `ξ_i(ω)` and the variance is
`J(i,i)⁻¹`. Fed into `ProbabilityTheory.Kernel.condExp_ae_eq_integral_kernel` they turn
`μ ∈ 𝒢(γ^{J,h})` into Georgii's (13.5), `ξ_i^μ = ξ_i` a.s., and into
`μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`. -/

section Theorem13_22Converse

variable {S : Type*} [Countable S] [LinearOrder S] {μ : Measure (S → ℝ)}
  {J : S → S → ℝ} {h : S → ℝ}
  (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)

omit [Countable S] in
/-- On the one-point volume `Λ = {i}` the coupling matrix `𝒥_{\{i\}}` is the `1 × 1` matrix
`J(i,i)`, so `𝒥_{\{i\}}⁻¹ = J(i,i)⁻¹`. This is the variance of `γ^{J,h}_{\{i\}}(·|ω)` in
Proposition (13.13). -/
lemma inv_gaussianCovMatrix_singleton_apply (J : S → S → ℝ) (i : S) :
    (Potential.gaussianCovMatrix J {i})⁻¹ ⟨i, Finset.mem_singleton_self i⟩
        ⟨i, Finset.mem_singleton_self i⟩ = (J i i)⁻¹ := by
  have hinv : (Potential.gaussianCovMatrix J {i})⁻¹ = (J i i)⁻¹ • (1 : Matrix _ _ ℝ) := by
    rw [Matrix.inv_def, Matrix.adjugate_subsingleton, Matrix.det_unique, Ring.inverse_eq_inv']
    rfl
  rw [hinv]
  simp

include hSymm hFin hPD in
/-- **The mean of `γ^{J,h}_{\{i\}}(·|ω)`** (Proposition (13.13) at `Λ = {i}`): Georgii's
`ξ_i(ω) = -J(i,i)⁻¹(h_i + ∑_{j ≠ i} J(i,j) ω_j)`. -/
lemma integral_eval_gaussianSpecification_singleton (i : S) (ω : S → ℝ) :
    ∫ x, x i ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω)
      = gaussianCondMean J h i ω := by
  have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
  rw [Potential.gaussianSpecification_apply, one_smul,
    integral_map Measurable.juxt.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
  simp only [juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_singleton_self i))]
  refine Eq.trans ?_ (gaussianCondMean_eq_gaussianMean h hFin hJii.ne' ω).symm
  exact integral_eval_multivariateGaussianPi (ι := ({i} : Finset S)) (hPD {i})
    (Potential.gaussianMean J h hFin {i} ω) ⟨i, Finset.mem_singleton_self i⟩

include hSymm hFin hPD in
/-- **The second moment of `γ^{J,h}_{\{i\}}(·|ω)`** (Proposition (13.13) at `Λ = {i}`):
`ξ_i(ω)² + J(i,i)⁻¹`. -/
lemma integral_eval_sq_gaussianSpecification_singleton (i : S) (ω : S → ℝ) :
    ∫ x, x i ^ 2 ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω)
      = gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹ := by
  have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
  rw [Potential.gaussianSpecification_apply, one_smul,
    integral_map Measurable.juxt.aemeasurable
      ((measurable_pi_apply i).pow_const 2).aestronglyMeasurable]
  simp only [juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_singleton_self i))]
  refine Eq.trans (integral_eval_sq_multivariateGaussianPi (ι := ({i} : Finset S)) (hPD {i})
    (Potential.gaussianMean J h hFin {i} ω) ⟨i, Finset.mem_singleton_self i⟩) ?_
  rw [inv_gaussianCovMatrix_singleton_apply J i, gaussianCondMean_eq_gaussianMean h hFin hJii.ne']
  ring

variable (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)

omit [Countable S] in
include hFin hμ in
/-- Georgii's `ξ_i` is square integrable under a Gaussian field: for `J` of finite row support it
is a finite affine combination of the spins `σ_j`, `j ≠ i`. -/
lemma memLp_two_gaussianCondMean (i : S) : MemLp (gaussianCondMean J h i) 2 μ := by
  have hP := hμ.isProbabilityMeasure
  have hfun : (fun ω : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset.erase i, J i j * ω j)
      = ∑ j ∈ (hFin i).toFinset.erase i, fun ω : S → ℝ ↦ J i j * ω j := by
    funext ω
    simp [Finset.sum_apply]
  have hsum : MemLp
      (fun ω : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset.erase i, J i j * ω j) 2 μ := by
    rw [hfun]
    exact memLp_finsetSum' _ fun j _ ↦ (memLp_two_eval hμ j).const_mul (J i j)
  have hadd : MemLp
      (fun ω : S → ℝ ↦ h i + ∑ j ∈ (hFin i).toFinset.erase i, J i j * ω j) 2 μ :=
    (memLp_const (μ := μ) (p := 2) (h i)).add hsum
  rw [funext (gaussianCondMean_eq_sum hFin i)]
  exact hadd.const_mul (-(J i i)⁻¹)

omit [Countable S] [LinearOrder S] in
private lemma coe_singleton_compl (i : S) :
    ((({i} : Finset S) : Set S))ᶜ = ({i}ᶜ : Set S) := by rw [Finset.coe_singleton]

include hSymm hPD hμ in
/-- **Georgii's equation (13.5), derived from `μ ∈ 𝒢(γ^{J,h})`.** This is the first step of the
implication (a) ⟹ (b) of Theorem (13.22): by Proposition (13.13) the mean of
`γ^{J,h}_{\{i\}}(·|ω)` is `ξ_i(ω)`, and `γ^{J,h}_{\{i\}}` is a conditional expectation kernel for
`μ`, so `ξ_i^μ = ξ_i` `μ`-a.s. -/
lemma condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i : S) : condExpOutside μ i =ᵐ[μ] gaussianCondMean J h i := by
  have hP := hμ.isProbabilityMeasure
  have hcond := hGibbs {i}
  have hpt : ∀ ω : S → ℝ,
      ∫ x, x i ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω)
        = gaussianCondMean J h i ω :=
    fun ω ↦ integral_eval_gaussianSpecification_singleton hSymm hFin hPD i ω
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := memLp_two_gaussianCondMean hFin hμ i
  have hgm : AEStronglyMeasurable[cylinderEvents ((({i} : Finset S) : Set S))ᶜ]
      (fun ω ↦ ∫ x, x i ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω))
      μ := by
    rw [funext hpt, coe_singleton_compl i]
    exact ((measurable_cylinderEvents_gaussianCondMean (h := h) hFin
      i).stronglyMeasurable).aestronglyMeasurable
  have key : μ[fun ω : S → ℝ ↦ ω i | cylinderEvents ((({i} : Finset S) : Set S))ᶜ]
      =ᵐ[μ] gaussianCondMean J h i :=
    (Kernel.condExp_ae_eq_integral_kernel μ
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i}) cylinderEvents_le_pi
      (fun ω : S → ℝ ↦ ω i) ((memLp_two_eval hμ i).integrable one_le_two)
      (by rw [funext hpt]; exact hξL2.integrable one_le_two) hgm).trans
    (Filter.Eventually.of_forall hpt)
  rw [coe_singleton_compl i] at key
  exact key

include hSymm hPD hμ in
/-- **The conditional second moment of a single spin, derived from `μ ∈ 𝒢(γ^{J,h})`**: by
Proposition (13.13) the law of `σ_i` under `γ^{J,h}_{\{i\}}(·|ω)` is `𝒩(ξ_i(ω), J(i,i)⁻¹)`, so
`μ(σ_i² | 𝒯_{\{i\}}) = ξ_i² + J(i,i)⁻¹` `μ`-a.s. -/
lemma condExp_sq_ae_eq_of_isGibbsMeasure
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i : S) :
    μ[fun ω : S → ℝ ↦ ω i ^ 2 | cylinderEvents ({i}ᶜ : Set S)]
      =ᵐ[μ] fun ω ↦ gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹ := by
  have hP := hμ.isProbabilityMeasure
  have hcond := hGibbs {i}
  have hpt : ∀ ω : S → ℝ,
      ∫ x, x i ^ 2 ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω)
        = gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹ :=
    fun ω ↦ integral_eval_sq_gaussianSpecification_singleton hSymm hFin hPD i ω
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := memLp_two_gaussianCondMean hFin hμ i
  have hgint : Integrable (fun ω ↦ gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹) μ :=
    hξL2.integrable_sq.add (integrable_const _)
  have hgm : AEStronglyMeasurable[cylinderEvents ((({i} : Finset S) : Set S))ᶜ]
      (fun ω ↦ ∫ x, x i ^ 2
        ∂(Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω)) μ := by
    rw [funext hpt, coe_singleton_compl i]
    exact ((((measurable_cylinderEvents_gaussianCondMean (h := h) hFin i).pow_const
      2).add_const _).stronglyMeasurable).aestronglyMeasurable
  have key : μ[fun ω : S → ℝ ↦ ω i ^ 2 | cylinderEvents ((({i} : Finset S) : Set S))ᶜ]
      =ᵐ[μ] fun ω ↦ gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹ :=
    (Kernel.condExp_ae_eq_integral_kernel μ
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i}) cylinderEvents_le_pi
      (fun ω : S → ℝ ↦ ω i ^ 2) (memLp_two_eval hμ i).integrable_sq
      (by rw [funext hpt]; exact hgint) hgm).trans (Filter.Eventually.of_forall hpt)
  rw [coe_singleton_compl i] at key
  exact key

include hSymm hPD hμ in
/-- **The conditional variance of a single spin is `J(i,i)⁻¹`, derived from `μ ∈ 𝒢(γ^{J,h})`.**
Combining the conditional first moment (`condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure`)
with the conditional second moment (`condExp_sq_ae_eq_of_isGibbsMeasure`) and the pull-out
property of the conditional expectation, `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`. -/
lemma integral_sq_sub_condExpOutside_eq_inv_of_isGibbsMeasure
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i : S) : ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹ := by
  have hP := hμ.isProbabilityMeasure
  have h5 := condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure hSymm hFin hPD hμ hGibbs i
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := memLp_two_gaussianCondMean hFin hμ i
  have hσL2 : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ := memLp_two_eval hμ i
  have hi1 : Integrable (fun ω : S → ℝ ↦ ω i ^ 2) μ := hσL2.integrable_sq
  have hi3 : Integrable (fun ω : S → ℝ ↦ gaussianCondMean J h i ω ^ 2) μ := hξL2.integrable_sq
  have hmul : Integrable (fun ω : S → ℝ ↦ gaussianCondMean J h i ω * ω i) μ :=
    hξL2.integrable_mul hσL2
  have hi2 : Integrable (fun ω : S → ℝ ↦ 2 * (gaussianCondMean J h i ω * ω i)) μ :=
    hmul.const_mul 2
  -- The second moment of `σ_i`, from the conditional second moment.
  have e1 : ∫ ω, ω i ^ 2 ∂μ = ∫ ω, (gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹) ∂μ := by
    rw [← integral_condExp (m := cylinderEvents ({i}ᶜ : Set S)) cylinderEvents_le_pi
      (f := fun ω : S → ℝ ↦ ω i ^ 2)]
    exact integral_congr_ae (condExp_sq_ae_eq_of_isGibbsMeasure hSymm hFin hPD hμ hGibbs i)
  -- The mixed moment `μ(ξ_i σ_i)`, by pulling `ξ_i` out of the conditional expectation.
  have e2 : ∫ ω, gaussianCondMean J h i ω * ω i ∂μ
      = ∫ ω, gaussianCondMean J h i ω ^ 2 ∂μ := by
    rw [← integral_condExp (m := cylinderEvents ({i}ᶜ : Set S)) cylinderEvents_le_pi
      (f := fun ω : S → ℝ ↦ gaussianCondMean J h i ω * ω i)]
    refine integral_congr_ae ?_
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (m := cylinderEvents ({i}ᶜ : Set S)) (μ := μ)
      (measurable_cylinderEvents_gaussianCondMean (h := h) hFin i).stronglyMeasurable
      hmul (hσL2.integrable one_le_two)
    filter_upwards [hpull, h5] with ω hω1 hω2
    have hfun : (μ[gaussianCondMean J h i * fun ω : S → ℝ ↦ ω i |
          cylinderEvents ({i}ᶜ : Set S)]) ω
        = (μ[fun ω : S → ℝ ↦ gaussianCondMean J h i ω * ω i |
          cylinderEvents ({i}ᶜ : Set S)]) ω := rfl
    rw [← hfun, hω1, Pi.mul_apply]
    change gaussianCondMean J h i ω * condExpOutside μ i ω = _
    rw [hω2, sq]
  have hae : ∀ᵐ ω ∂μ, (ω i - condExpOutside μ i ω) ^ 2
      = ω i ^ 2 - 2 * (gaussianCondMean J h i ω * ω i) + gaussianCondMean J h i ω ^ 2 := by
    filter_upwards [h5] with ω hω
    rw [hω]
    ring
  have hsplit1 : ∫ ω, (ω i ^ 2 - 2 * (gaussianCondMean J h i ω * ω i)
        + gaussianCondMean J h i ω ^ 2) ∂μ
      = (∫ ω, (ω i ^ 2 - 2 * (gaussianCondMean J h i ω * ω i)) ∂μ)
        + ∫ ω, gaussianCondMean J h i ω ^ 2 ∂μ := integral_add (hi1.sub hi2) hi3
  have hsplit2 : ∫ ω, (ω i ^ 2 - 2 * (gaussianCondMean J h i ω * ω i)) ∂μ
      = (∫ ω, ω i ^ 2 ∂μ) - ∫ ω, 2 * (gaussianCondMean J h i ω * ω i) ∂μ :=
    integral_sub hi1 hi2
  have hsplit3 : ∫ ω, (gaussianCondMean J h i ω ^ 2 + (J i i)⁻¹) ∂μ
      = (∫ ω, gaussianCondMean J h i ω ^ 2 ∂μ) + ∫ _ω : S → ℝ, (J i i)⁻¹ ∂μ :=
    integral_add hi3 (integrable_const _)
  rw [integral_congr_ae hae, hsplit1, hsplit2, integral_const_mul, e1, hsplit3, e2,
    integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

include hSymm hPD hμ in
/-- **The residual `σ_i - ξ_i` is centred and orthogonal to `L²(𝒯_{\{i\}})`.** For `μ ∈ 𝒢(γ^{J,h})`
the conditional expectation of `σ_i - ξ_i` given `𝒯_{\{i\}}` vanishes
(`condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure`); hence its integral against any
square-integrable `𝒯_{\{i\}}`-measurable `g` is `0`. -/
lemma integral_mul_sub_gaussianCondMean_eq_zero
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i : S) {g : (S → ℝ) → ℝ} (hgm : Measurable[cylinderEvents ({i}ᶜ : Set S)] g)
    (hgL2 : MemLp g 2 μ) :
    ∫ ω, g ω * (ω i - gaussianCondMean J h i ω) ∂μ = 0 := by
  have hP := hμ.isProbabilityMeasure
  have h5 := condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure hSymm hFin hPD hμ hGibbs i
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := memLp_two_gaussianCondMean hFin hμ i
  have hσL2 : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ := memLp_two_eval hμ i
  have hres : MemLp (fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω) 2 μ := hσL2.sub hξL2
  have hint : Integrable (fun ω : S → ℝ ↦ g ω * (ω i - gaussianCondMean J h i ω)) μ :=
    hgL2.integrable_mul hres
  have hzero : μ[fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω |
      cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] 0 := by
    have hsub := condExp_sub (μ := μ) (hσL2.integrable one_le_two)
      (hξL2.integrable one_le_two) (cylinderEvents ({i}ᶜ : Set S))
    have hξc : μ[gaussianCondMean J h i | cylinderEvents ({i}ᶜ : Set S)]
        = gaussianCondMean J h i :=
      condExp_of_stronglyMeasurable cylinderEvents_le_pi
        (measurable_cylinderEvents_gaussianCondMean (h := h) hFin i).stronglyMeasurable
        (hξL2.integrable one_le_two)
    filter_upwards [hsub, h5] with ω hω1 hω2
    have hfun : (μ[(fun ω : S → ℝ ↦ ω i) - gaussianCondMean J h i |
          cylinderEvents ({i}ᶜ : Set S)]) ω
        = (μ[fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω |
          cylinderEvents ({i}ᶜ : Set S)]) ω := rfl
    rw [← hfun, hω1, Pi.sub_apply, hξc]
    change condExpOutside μ i ω - gaussianCondMean J h i ω = (0 : (S → ℝ) → ℝ) ω
    rw [hω2, sub_self, Pi.zero_apply]
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := cylinderEvents ({i}ᶜ : Set S))
    (μ := μ) hgm.stronglyMeasurable hint (hres.integrable one_le_two)
  have hae : μ[fun ω : S → ℝ ↦ g ω * (ω i - gaussianCondMean J h i ω) |
      cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hzero] with ω hω1 hω2
    have hfun : (μ[g * fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω |
          cylinderEvents ({i}ᶜ : Set S)]) ω
        = (μ[fun ω : S → ℝ ↦ g ω * (ω i - gaussianCondMean J h i ω) |
          cylinderEvents ({i}ᶜ : Set S)]) ω := rfl
    rw [← hfun, hω1, Pi.mul_apply, hω2]
    simp
  rw [← integral_condExp (m := cylinderEvents ({i}ᶜ : Set S)) cylinderEvents_le_pi
    (f := fun ω : S → ℝ ↦ g ω * (ω i - gaussianCondMean J h i ω)), integral_congr_ae hae]
  simp

include hSymm hPD hμ in
/-- **The mean of the residual vanishes**: `μ(σ_i - ξ_i) = 0`, for `μ ∈ 𝒢(γ^{J,h})`. -/
lemma integral_sub_gaussianCondMean_eq_zero
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i : S) : ∫ ω, (ω i - gaussianCondMean J h i ω) ∂μ = 0 := by
  have hP := hμ.isProbabilityMeasure
  have := integral_mul_sub_gaussianCondMean_eq_zero hSymm hFin hPD hμ hGibbs i
    (g := fun _ ↦ (1 : ℝ)) (measurable_const) (memLp_const 1)
  simpa using this

include hSymm hPD hμ in
/-- **Georgii's covariance identity in the proof of (13.22)(a) ⟹ (b)**:
`cov(σ_i - ξ_i, σ_k) = δ_{ik} J(i,i)⁻¹`. For `k ≠ i` the spin `σ_k` is `𝒯_{\{i\}}`-measurable and
the residual is conditionally centred; for `k = i` one splits `σ_i = ξ_i + (σ_i - ξ_i)` and uses
`μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`. -/
lemma covariance_sub_gaussianCondMean_eval
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i k : S) :
    cov[fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω, fun ω : S → ℝ ↦ ω k; μ]
      = if i = k then (J i i)⁻¹ else 0 := by
  have hP := hμ.isProbabilityMeasure
  have h5 := condExpOutside_ae_eq_gaussianCondMean_of_isGibbsMeasure hSymm hFin hPD hμ hGibbs i
  have hξL2 : MemLp (gaussianCondMean J h i) 2 μ := memLp_two_gaussianCondMean hFin hμ i
  have hσL2 : ∀ j : S, MemLp (fun ω : S → ℝ ↦ ω j) 2 μ := fun j ↦ memLp_two_eval hμ j
  have hres : MemLp (fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω) 2 μ := (hσL2 i).sub hξL2
  have hmean0 := integral_sub_gaussianCondMean_eq_zero hSymm hFin hPD hμ hGibbs i
  have hcovsub : cov[fun ω : S → ℝ ↦ ω i - gaussianCondMean J h i ω, fun ω : S → ℝ ↦ ω k; μ]
      = ∫ ω, (ω i - gaussianCondMean J h i ω) * ω k ∂μ := by
    rw [covariance_eq_sub hres (hσL2 k), hmean0]
    simp
  rw [hcovsub]
  by_cases hik : i = k
  · subst hik
    have hsplit : ∀ ω : S → ℝ, (ω i - gaussianCondMean J h i ω) * ω i
        = gaussianCondMean J h i ω * (ω i - gaussianCondMean J h i ω)
          + (ω i - gaussianCondMean J h i ω) ^ 2 := by
      intro ω; ring
    have hi1 : Integrable (fun ω : S → ℝ ↦
        gaussianCondMean J h i ω * (ω i - gaussianCondMean J h i ω)) μ :=
      hξL2.integrable_mul hres
    have hi2 : Integrable (fun ω : S → ℝ ↦ (ω i - gaussianCondMean J h i ω) ^ 2) μ :=
      hres.integrable_sq
    have hvar := integral_sq_sub_condExpOutside_eq_inv_of_isGibbsMeasure hSymm hFin hPD hμ
      hGibbs i
    have hvar' : ∫ ω, (ω i - gaussianCondMean J h i ω) ^ 2 ∂μ = (J i i)⁻¹ := by
      rw [← hvar]
      refine integral_congr_ae ?_
      filter_upwards [h5] with ω hω
      rw [hω]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add hi1 hi2,
      integral_mul_sub_gaussianCondMean_eq_zero hSymm hFin hPD hμ hGibbs i
        (measurable_cylinderEvents_gaussianCondMean (h := h) hFin i) hξL2, hvar']
    simp
  · have hki : (k : S) ≠ i := fun hh ↦ hik hh.symm
    have hgm : Measurable[cylinderEvents ({i}ᶜ : Set S)] (fun ω : S → ℝ ↦ ω k) :=
      measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({i}ᶜ : Set S))
        (by simpa using hki)
    have := integral_mul_sub_gaussianCondMean_eq_zero hSymm hFin hPD hμ hGibbs i hgm (hσL2 k)
    rw [show (fun ω : S → ℝ ↦ (ω i - gaussianCondMean J h i ω) * ω k)
      = fun ω : S → ℝ ↦ ω k * (ω i - gaussianCondMean J h i ω) from funext fun ω ↦ mul_comm _ _,
      this]
    simp [hik]

omit [Countable S] in
include hPD in
/-- Georgii's decomposition `σ_i - ξ_i = J(i,i)⁻¹ (h_i + X_i)`, i.e.
`X_i = -h_i + J(i,i)(σ_i - ξ_i)`, for `J` of finite row support (where `Ω_J = Ω`). -/
lemma gaussianRowForm_eq_sub_gaussianCondMean (i : S) :
    Potential.gaussianRowForm J hFin i
      = fun ω : S → ℝ ↦ -h i + J i i * (ω i - gaussianCondMean J h i ω) := by
  have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
  funext ω
  have hω : ω ∈ Potential.gaussianConvergenceSet J := by
    rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]
    trivial
  rw [Potential.gaussianRowForm_eq_tsum J hFin i, gaussianCondMean_eq_of_mem hJii.ne' hω]
  field_simp
  ring

include hSymm hPD hμ in
/-- **Georgii Theorem (13.22), (a) ⟹ (b), the mean condition.** If `μ ∈ 𝒢(γ^{J,h})` is a Gaussian
field then its mean `m` lies in `M_{J,h}`: integrating `σ_i - ξ_i^μ = J(i,i)⁻¹(h_i + X_i)` gives
`h_i + ∑_{j ∈ S} J(i,j) m_j = 0`. (Georgii's condition `m ∈ Ω_J` is automatic here, `J` having
finite range.) -/
theorem mem_gaussianMeanSet_of_isGibbsMeasure
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ) :
    (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h := by
  have hP := hμ.isProbabilityMeasure
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]
    trivial
  · have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
    have hXint : ∫ ω, Potential.gaussianRowForm J hFin i ω ∂μ
        = ∑' j, J i j * ∫ ω, ω j ∂μ := by
      rw [integral_gaussianRowForm hFin hμ i, Potential.gaussianRowForm_eq_tsum J hFin i]
    have hzero := integral_sub_gaussianCondMean_eq_zero hSymm hFin hPD hμ hGibbs i
    have hXL2 : MemLp (Potential.gaussianRowForm J hFin i) 2 μ :=
      memLp_two_gaussianRowForm hFin hμ i
    have hres : ∫ ω, Potential.gaussianRowForm J hFin i ω ∂μ
        = -h i + J i i * ∫ ω, (ω i - gaussianCondMean J h i ω) ∂μ := by
      rw [gaussianRowForm_eq_sub_gaussianCondMean hFin hPD i]
      have hi : Integrable (fun ω : S → ℝ ↦ J i i * (ω i - gaussianCondMean J h i ω)) μ := by
        have hσL2 : MemLp (fun ω : S → ℝ ↦ ω i) 2 μ := memLp_two_eval hμ i
        exact ((hσL2.sub (memLp_two_gaussianCondMean hFin hμ i)).integrable
          one_le_two).const_mul _
      have hsum : ∫ ω, (-h i + J i i * (ω i - gaussianCondMean J h i ω)) ∂μ
          = (∫ _ω : S → ℝ, -h i ∂μ) +
            ∫ ω, J i i * (ω i - gaussianCondMean J h i ω) ∂μ :=
        integral_add (integrable_const _) hi
      rw [hsum, integral_const, integral_const_mul]
      simp
    rw [hzero] at hres
    rw [← hXint, hres]
    ring

include hSymm hPD hμ in
/-- **Georgii Theorem (13.22), (a) ⟹ (b), the covariance condition.** If `μ ∈ 𝒢(γ^{J,h})` is a
Gaussian field with covariance function `C`, then `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}`. Georgii's
computation: `∑_j J(i,j) C(j,k) = cov(X_i, σ_k) = J(i,i) cov(σ_i - ξ_i, σ_k) = δ_{ik}`. -/
theorem isInverse_covariance_of_isGibbsMeasure
    (hGibbs : (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ)
    (i k : S) :
    ∑' j, J i j * cov[fun ω : S → ℝ ↦ ω j, fun ω : S → ℝ ↦ ω k; μ] = if i = k then 1 else 0 := by
  have hP := hμ.isProbabilityMeasure
  have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
  have hres : Integrable (fun ω : S → ℝ ↦ J i i * (ω i - gaussianCondMean J h i ω)) μ :=
    (((memLp_two_eval hμ i).sub (memLp_two_gaussianCondMean hFin hμ i)).integrable
      one_le_two).const_mul _
  rw [← covariance_gaussianRowForm_eval hFin hμ i k,
    gaussianRowForm_eq_sub_gaussianCondMean hFin hPD i,
    covariance_const_add_left hres, covariance_const_mul_left,
    covariance_sub_gaussianCondMean_eval hSymm hFin hPD hμ hGibbs i k]
  by_cases hik : i = k
  · subst hik
    simp [mul_inv_cancel₀ hJii.ne']
  · simp [hik]

include hSymm hPD hμ in
/-- **Georgii Theorem (13.22) for `J` of finite range.** Let `μ` be a Gaussian field with mean `m`
and covariance function `C`, let `J : S × S → ℝ` be symmetric with finite row support and every
`𝒥_Λ` positive definite, and let `h ∈ Ω`. Then

`μ ∈ 𝒢(γ^{J,h})` ⟺ `m ∈ M_{J,h}` and `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}` for all `i, k ∈ S`.

Georgii's third condition, `μ(Ω_J) = 1`, is automatic here: `Ω_J = Ω` for finite range
(`Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport`), which is also why Corollary
(13.A6) — a.s. convergence implies `L²` convergence for a Gaussian family — is not needed.

(a) ⟹ (b) is `mem_gaussianMeanSet_of_isGibbsMeasure` and
`isInverse_covariance_of_isGibbsMeasure`, both read off the first two moments of
`γ^{J,h}_{\{i\}}(·|ω)` through `ProbabilityTheory.Kernel.condExp_ae_eq_integral_kernel`;
(b) ⟹ (a) is `georgii_13_22_of_finiteRowSupport`. -/
theorem georgii_13_22_iff :
    (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure μ
      ↔ (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h ∧
        ∀ i k, ∑' j, J i j * cov[fun ω : S → ℝ ↦ ω j, fun ω : S → ℝ ↦ ω k; μ]
          = if i = k then 1 else 0 := by
  refine ⟨fun hG ↦ ⟨mem_gaussianMeanSet_of_isGibbsMeasure hSymm hFin hPD hμ hG,
    fun i k ↦ isInverse_covariance_of_isGibbsMeasure hSymm hFin hPD hμ hG i k⟩, ?_⟩
  rintro ⟨hm, hC⟩
  exact georgii_13_22_of_finiteRowSupport hFin hμ hC hSymm hPD hm

end Theorem13_22Converse

/-! ## Georgii Theorem (13.26): the limits (13.25) exist under (13.27)

Georgii's monotonicity display,
`∑_{i,j ∈ Λ} 𝒥_Λ⁻¹(i,j) t_i t_j ≤ ∑_{i,j ∈ Λ} 𝒥_Δ⁻¹(i,j) t_i t_j` for `Λ ⊆ Δ`, which he derives
from Proposition (13.13) and Jensen's inequality, is the linear-algebra statement
`(A_{ΛΛ})⁻¹ ≤ (A⁻¹)_{ΛΛ}` for a principal submatrix of a positive definite matrix; it is proved
in `GibbsMeasure/Mathlib/LinearAlgebra/Matrix/PosDef.lean` as
`Matrix.PosDef.dotProduct_mulVec_inv_submatrix_le`, by the variational characterisation
`t ⬝ᵥ A⁻¹ *ᵥ t = sup_x (2 (t ⬝ᵥ x) - x ⬝ᵥ A *ᵥ x)` (the left-hand side is the supremum of the same
quadratic over the vectors supported in `Λ`). -/

section Theorem13_26Limits

variable {S : Type*} [LinearOrder S] {J : S → S → ℝ}

/-- **Georgii's monotonicity display in the proof of Theorem (13.26)**, in the coordinate-free
form `t ⬝ᵥ 𝒥_Λ⁻¹ *ᵥ t ≤ t' ⬝ᵥ 𝒥_Δ⁻¹ *ᵥ t'` for `Λ ⊆ Δ` and `t'` any extension of `t` to `Δ`.
Georgii derives it from Proposition (13.13) and Jensen's inequality; the underlying fact is the
positive semidefinite inequality `(A_{ΛΛ})⁻¹ ≤ (A⁻¹)_{ΛΛ}`,
`Matrix.PosDef.dotProduct_mulVec_inv_submatrix_le`. -/
theorem dotProduct_mulVec_inv_gaussianCovMatrix_mono
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) (t : Λ → ℝ) (t' : Δ → ℝ) (ht : ∀ a : Λ, t' ⟨a.1, hΛΔ a.2⟩ = t a) :
    t ⬝ᵥ (Potential.gaussianCovMatrix J Λ)⁻¹ *ᵥ t
      ≤ t' ⬝ᵥ (Potential.gaussianCovMatrix J Δ)⁻¹ *ᵥ t' := by
  have he : Function.Injective (fun a : Λ ↦ (⟨a.1, hΛΔ a.2⟩ : Δ)) :=
    fun a b hab ↦ Subtype.ext (by
      have hval := congrArg (fun z : Δ ↦ (z : S)) hab
      simpa using hval)
  have hsub : (Potential.gaussianCovMatrix J Δ).submatrix
      (fun a : Λ ↦ (⟨a.1, hΛΔ a.2⟩ : Δ)) (fun a : Λ ↦ (⟨a.1, hΛΔ a.2⟩ : Δ))
      = Potential.gaussianCovMatrix J Λ := rfl
  have := (hPD Δ).dotProduct_mulVec_inv_submatrix_le he t t' ht
  rwa [hsub] at this

omit [LinearOrder S] in
/-- `Pi.single a 1 ⬝ᵥ M *ᵥ Pi.single b 1 = M a b`. -/
private lemma single_dotProduct_mulVec_single {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (a b : n) :
    Pi.single a (1 : ℝ) ⬝ᵥ M *ᵥ Pi.single b (1 : ℝ) = M a b := by
  simp [single_dotProduct, Matrix.mulVec_single]

/-- **Georgii's first conclusion in the proof of (13.26)**: `𝒥_Λ⁻¹(i,i)` is an increasing function
of `Λ`. -/
theorem inv_gaussianCovMatrix_diag_mono
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) {i : S} (hi : i ∈ Λ) :
    (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨i, hi⟩ ⟨i, hi⟩
      ≤ (Potential.gaussianCovMatrix J Δ)⁻¹ ⟨i, hΛΔ hi⟩ ⟨i, hΛΔ hi⟩ := by
  classical
  have hext : ∀ a : Λ,
      ((Pi.single (⟨i, hΛΔ hi⟩ : Δ) (1 : ℝ) : Δ → ℝ)) (⟨a.1, hΛΔ a.2⟩ : Δ)
      = ((Pi.single (⟨i, hi⟩ : Λ) (1 : ℝ) : Λ → ℝ)) a := by
    intro a
    by_cases hai : a = ⟨i, hi⟩
    · subst hai
      simp
    · have h1 : (⟨a.1, hΛΔ a.2⟩ : Δ) ≠ ⟨i, hΛΔ hi⟩ := fun hh ↦
        hai (Subtype.ext (show (a : S) = i from congrArg Subtype.val hh))
      rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne hai]
  have := dotProduct_mulVec_inv_gaussianCovMatrix_mono hPD hΛΔ
    (Pi.single (⟨i, hi⟩ : Λ) (1 : ℝ)) (Pi.single (⟨i, hΛΔ hi⟩ : Δ) (1 : ℝ)) hext
  rwa [single_dotProduct_mulVec_single, single_dotProduct_mulVec_single] at this

omit [LinearOrder S] in
/-- `(u + v) ⬝ᵥ M *ᵥ (u + v)` for `u = e_a`, `v = e_b`. -/
private lemma add_single_dotProduct_mulVec_add_single {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (a b : n) :
    (Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ)) ⬝ᵥ M *ᵥ
        (Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ))
      = M a a + M a b + (M b a + M b b) := by
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    single_dotProduct_mulVec_single, single_dotProduct_mulVec_single]

/-- **Georgii's second conclusion in the proof of (13.26)**: for `i ≠ j`,
`𝒥_Λ⁻¹(i,i) + 𝒥_Λ⁻¹(i,j) + 𝒥_Λ⁻¹(j,i) + 𝒥_Λ⁻¹(j,j)` is an increasing function of `Λ`. -/
theorem inv_gaussianCovMatrix_pair_mono
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) {i j : S} (hi : i ∈ Λ) (hj : j ∈ Λ) :
    (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨i, hi⟩ ⟨i, hi⟩
        + (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨i, hi⟩ ⟨j, hj⟩
        + ((Potential.gaussianCovMatrix J Λ)⁻¹ ⟨j, hj⟩ ⟨i, hi⟩
          + (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨j, hj⟩ ⟨j, hj⟩)
      ≤ (Potential.gaussianCovMatrix J Δ)⁻¹ ⟨i, hΛΔ hi⟩ ⟨i, hΛΔ hi⟩
        + (Potential.gaussianCovMatrix J Δ)⁻¹ ⟨i, hΛΔ hi⟩ ⟨j, hΛΔ hj⟩
        + ((Potential.gaussianCovMatrix J Δ)⁻¹ ⟨j, hΛΔ hj⟩ ⟨i, hΛΔ hi⟩
          + (Potential.gaussianCovMatrix J Δ)⁻¹ ⟨j, hΛΔ hj⟩ ⟨j, hΛΔ hj⟩) := by
  classical
  have hsingle : ∀ (k : S) (hk : k ∈ Λ) (a : Λ),
      ((Pi.single (⟨k, hΛΔ hk⟩ : Δ) (1 : ℝ) : Δ → ℝ)) (⟨a.1, hΛΔ a.2⟩ : Δ)
        = ((Pi.single (⟨k, hk⟩ : Λ) (1 : ℝ) : Λ → ℝ)) a := by
    intro k hk a
    by_cases hak : a = ⟨k, hk⟩
    · subst hak
      simp
    · have h1 : (⟨a.1, hΛΔ a.2⟩ : Δ) ≠ ⟨k, hΛΔ hk⟩ := fun hh ↦
        hak (Subtype.ext (by
          have hval := congrArg (fun z : Δ ↦ (z : S)) hh
          simpa using hval))
      rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne hak]
  have hext : ∀ a : Λ,
      ((Pi.single (⟨i, hΛΔ hi⟩ : Δ) (1 : ℝ) : Δ → ℝ)
        + (Pi.single (⟨j, hΛΔ hj⟩ : Δ) (1 : ℝ) : Δ → ℝ)) (⟨a.1, hΛΔ a.2⟩ : Δ)
      = ((Pi.single (⟨i, hi⟩ : Λ) (1 : ℝ) : Λ → ℝ)
        + (Pi.single (⟨j, hj⟩ : Λ) (1 : ℝ) : Λ → ℝ)) a := by
    intro a
    rw [Pi.add_apply, Pi.add_apply, hsingle i hi a, hsingle j hj a]
  have := dotProduct_mulVec_inv_gaussianCovMatrix_mono hPD hΛΔ
    ((Pi.single (⟨i, hi⟩ : Λ) (1 : ℝ) : Λ → ℝ) + (Pi.single (⟨j, hj⟩ : Λ) (1 : ℝ) : Λ → ℝ))
    ((Pi.single (⟨i, hΛΔ hi⟩ : Δ) (1 : ℝ) : Δ → ℝ)
      + (Pi.single (⟨j, hΛΔ hj⟩ : Δ) (1 : ℝ) : Δ → ℝ)) hext
  rwa [add_single_dotProduct_mulVec_add_single, add_single_dotProduct_mulVec_add_single] at this

/-- The inverse of `𝒥_Λ` is symmetric. -/
theorem inv_gaussianCovMatrix_symm
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (a b : Λ) :
    (Potential.gaussianCovMatrix J Λ)⁻¹ a b = (Potential.gaussianCovMatrix J Λ)⁻¹ b a := by
  have h := (hPD Λ).inv.transpose_eq
  exact congrFun (congrFun h b) a

/-- The inverse of `𝒥_Λ` is positive semidefinite as a quadratic form. -/
theorem dotProduct_mulVec_inv_gaussianCovMatrix_nonneg
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (t : Λ → ℝ) :
    0 ≤ t ⬝ᵥ (Potential.gaussianCovMatrix J Λ)⁻¹ *ᵥ t := by
  simpa using (hPD Λ).inv.posSemidef.dotProduct_mulVec_nonneg t

/-- The diagonal of `𝒥_Λ⁻¹` is nonnegative. -/
theorem inv_gaussianCovMatrix_diag_nonneg
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (a : Λ) :
    0 ≤ (Potential.gaussianCovMatrix J Λ)⁻¹ a a := by
  classical
  have := dotProduct_mulVec_inv_gaussianCovMatrix_nonneg hPD Λ (Pi.single a (1 : ℝ))
  rwa [single_dotProduct_mulVec_single] at this

/-- The sum of the four entries of `𝒥_Λ⁻¹` at `(i, j)` is nonnegative. -/
theorem inv_gaussianCovMatrix_pair_nonneg
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (a b : Λ) :
    0 ≤ (Potential.gaussianCovMatrix J Λ)⁻¹ a a + (Potential.gaussianCovMatrix J Λ)⁻¹ a b
      + ((Potential.gaussianCovMatrix J Λ)⁻¹ b a
        + (Potential.gaussianCovMatrix J Λ)⁻¹ b b) := by
  classical
  have := dotProduct_mulVec_inv_gaussianCovMatrix_nonneg hPD Λ
    (Pi.single a (1 : ℝ) + Pi.single b (1 : ℝ))
  rwa [add_single_dotProduct_mulVec_add_single] at this

/-- **Georgii's Cauchy–Schwarz step in the proof of (13.26)**, in the form he only needs:
`2 𝒥_Λ⁻¹(i,j) ≤ 𝒥_Λ⁻¹(i,i) + 𝒥_Λ⁻¹(j,j)`, from the positive semidefiniteness of `𝒥_Λ⁻¹` applied
to `e_i - e_j`. -/
theorem two_mul_inv_gaussianCovMatrix_le
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (a b : Λ) :
    2 * (Potential.gaussianCovMatrix J Λ)⁻¹ a b
      ≤ (Potential.gaussianCovMatrix J Λ)⁻¹ a a + (Potential.gaussianCovMatrix J Λ)⁻¹ b b := by
  classical
  have hneg := dotProduct_mulVec_inv_gaussianCovMatrix_nonneg hPD Λ
    (Pi.single a (1 : ℝ) + Pi.single b (-1 : ℝ))
  have hexp : (Pi.single a (1 : ℝ) + Pi.single b (-1 : ℝ)) ⬝ᵥ
      (Potential.gaussianCovMatrix J Λ)⁻¹ *ᵥ (Pi.single a (1 : ℝ) + Pi.single b (-1 : ℝ))
      = (Potential.gaussianCovMatrix J Λ)⁻¹ a a - (Potential.gaussianCovMatrix J Λ)⁻¹ a b
        - ((Potential.gaussianCovMatrix J Λ)⁻¹ b a
          - (Potential.gaussianCovMatrix J Λ)⁻¹ b b) := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    simp [single_dotProduct, Matrix.mulVec_single]
    ring
  rw [hexp] at hneg
  have hsym := inv_gaussianCovMatrix_symm hPD Λ a b
  linarith

/-- **Georgii's `𝒥_Λ⁻¹(i,j)` of (13.25)**, extended by `0` when `i` or `j` lies outside `Λ`, so
that it is a function of `Λ` on the whole net `Finset S` of finite volumes. Georgii's limits
(13.25) are the limits of this function along `Filter.atTop`. -/
noncomputable def invGaussianCovEntry (J : S → S → ℝ) (Λ : Finset S) (i j : S) : ℝ :=
  if h : i ∈ Λ ∧ j ∈ Λ then (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

@[simp] lemma invGaussianCovEntry_of_mem {Λ : Finset S} {i j : S} (hi : i ∈ Λ) (hj : j ∈ Λ) :
    invGaussianCovEntry J Λ i j = (Potential.gaussianCovMatrix J Λ)⁻¹ ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp only [invGaussianCovEntry]
  split_ifs with hh
  · rfl
  · exact absurd ⟨hi, hj⟩ hh

lemma invGaussianCovEntry_of_notMem_left {Λ : Finset S} {i j : S} (hi : i ∉ Λ) :
    invGaussianCovEntry J Λ i j = 0 := by
  simp only [invGaussianCovEntry]
  split_ifs with hh
  · exact absurd hh.1 hi
  · rfl

lemma invGaussianCovEntry_of_notMem_right {Λ : Finset S} {i j : S} (hj : j ∉ Λ) :
    invGaussianCovEntry J Λ i j = 0 := by
  simp only [invGaussianCovEntry]
  split_ifs with hh
  · exact absurd hh.2 hj
  · rfl

lemma invGaussianCovEntry_symm
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (i j : S) :
    invGaussianCovEntry J Λ i j = invGaussianCovEntry J Λ j i := by
  by_cases hi : i ∈ Λ
  · by_cases hj : j ∈ Λ
    · rw [invGaussianCovEntry_of_mem hi hj, invGaussianCovEntry_of_mem hj hi,
        inv_gaussianCovMatrix_symm hPD]
    · rw [invGaussianCovEntry_of_notMem_right hj, invGaussianCovEntry_of_notMem_left hj]
  · rw [invGaussianCovEntry_of_notMem_left hi, invGaussianCovEntry_of_notMem_right hi]

lemma invGaussianCovEntry_diag_nonneg
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (i : S) :
    0 ≤ invGaussianCovEntry J Λ i i := by
  by_cases hi : i ∈ Λ
  · rw [invGaussianCovEntry_of_mem hi hi]
    exact inv_gaussianCovMatrix_diag_nonneg hPD Λ ⟨i, hi⟩
  · rw [invGaussianCovEntry_of_notMem_left hi]

/-- **Georgii's first conclusion in the proof of (13.26)**: `Λ ↦ 𝒥_Λ⁻¹(i,i)` is increasing. -/
theorem monotone_invGaussianCovEntry_diag
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (i : S) :
    Monotone fun Λ : Finset S ↦ invGaussianCovEntry J Λ i i := by
  intro Λ Δ hΛΔ
  show invGaussianCovEntry J Λ i i ≤ invGaussianCovEntry J Δ i i
  by_cases hi : i ∈ Λ
  · rw [invGaussianCovEntry_of_mem hi hi, invGaussianCovEntry_of_mem (hΛΔ hi) (hΛΔ hi)]
    exact inv_gaussianCovMatrix_diag_mono hPD hΛΔ hi
  · rw [invGaussianCovEntry_of_notMem_left hi]
    exact invGaussianCovEntry_diag_nonneg hPD Δ i

/-- The four-entry sum `𝒥_Λ⁻¹(i,i) + 𝒥_Λ⁻¹(i,j) + 𝒥_Λ⁻¹(j,i) + 𝒥_Λ⁻¹(j,j)` of Georgii's second
conclusion, extended by `0` unless both `i` and `j` lie in `Λ`. -/
noncomputable def invGaussianCovPair (J : S → S → ℝ) (Λ : Finset S) (i j : S) : ℝ :=
  if i ∈ Λ ∧ j ∈ Λ then
    invGaussianCovEntry J Λ i i + invGaussianCovEntry J Λ i j
      + (invGaussianCovEntry J Λ j i + invGaussianCovEntry J Λ j j)
  else 0

lemma invGaussianCovPair_of_mem {Λ : Finset S} {i j : S} (hi : i ∈ Λ) (hj : j ∈ Λ) :
    invGaussianCovPair J Λ i j = invGaussianCovEntry J Λ i i + invGaussianCovEntry J Λ i j
      + (invGaussianCovEntry J Λ j i + invGaussianCovEntry J Λ j j) := by
  simp only [invGaussianCovPair]
  split_ifs with hh
  · rfl
  · exact absurd ⟨hi, hj⟩ hh

lemma invGaussianCovPair_nonneg
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (Λ : Finset S) (i j : S) :
    0 ≤ invGaussianCovPair J Λ i j := by
  rw [invGaussianCovPair]
  split_ifs with hij
  · rw [invGaussianCovEntry_of_mem hij.1 hij.1, invGaussianCovEntry_of_mem hij.1 hij.2,
      invGaussianCovEntry_of_mem hij.2 hij.1, invGaussianCovEntry_of_mem hij.2 hij.2]
    exact inv_gaussianCovMatrix_pair_nonneg hPD Λ ⟨i, hij.1⟩ ⟨j, hij.2⟩
  · exact le_rfl

/-- **Georgii's second conclusion in the proof of (13.26)**: the four-entry sum is increasing. -/
theorem monotone_invGaussianCovPair
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) (i j : S) :
    Monotone fun Λ : Finset S ↦ invGaussianCovPair J Λ i j := by
  intro Λ Δ hΛΔ
  show invGaussianCovPair J Λ i j ≤ invGaussianCovPair J Δ i j
  by_cases hij : i ∈ Λ ∧ j ∈ Λ
  · rw [invGaussianCovPair_of_mem hij.1 hij.2,
      invGaussianCovPair_of_mem (hΛΔ hij.1) (hΛΔ hij.2),
      invGaussianCovEntry_of_mem hij.1 hij.1, invGaussianCovEntry_of_mem hij.1 hij.2,
      invGaussianCovEntry_of_mem hij.2 hij.1, invGaussianCovEntry_of_mem hij.2 hij.2,
      invGaussianCovEntry_of_mem (hΛΔ hij.1) (hΛΔ hij.1),
      invGaussianCovEntry_of_mem (hΛΔ hij.1) (hΛΔ hij.2),
      invGaussianCovEntry_of_mem (hΛΔ hij.2) (hΛΔ hij.1),
      invGaussianCovEntry_of_mem (hΛΔ hij.2) (hΛΔ hij.2)]
    exact inv_gaussianCovMatrix_pair_mono hPD hΛΔ hij.1 hij.2
  · rw [show invGaussianCovPair J Λ i j = 0 from by simp [invGaussianCovPair, hij]]
    exact invGaussianCovPair_nonneg hPD Δ i j

/-- **Georgii Theorem (13.26): condition (13.27) forces the limits (13.25) to exist.** If
`sup_Λ 𝒥_Λ⁻¹(i,i) < ∞` for every `i` — here: the net `Λ ↦ 𝒥_Λ⁻¹(i,i)` is bounded above — then
`C(i,j) = lim_Λ 𝒥_Λ⁻¹(i,j)` exists for all `i, j`.

Georgii's proof: `Λ ↦ 𝒥_Λ⁻¹(i,i)` is increasing (`monotone_invGaussianCovEntry_diag`), hence
convergent; `Λ ↦ 𝒥_Λ⁻¹(i,i) + 𝒥_Λ⁻¹(i,j) + 𝒥_Λ⁻¹(j,i) + 𝒥_Λ⁻¹(j,j)` is increasing
(`monotone_invGaussianCovPair`) and bounded above by `2 (sup_Λ 𝒥_Λ⁻¹(i,i) + sup_Λ 𝒥_Λ⁻¹(j,j))`,
because `2 𝒥_Λ⁻¹(i,j) ≤ 𝒥_Λ⁻¹(i,i) + 𝒥_Λ⁻¹(j,j)` (Georgii's Cauchy–Schwarz step,
`two_mul_inv_gaussianCovMatrix_le`); the off-diagonal limit is then the half-difference. -/
theorem exists_tendsto_invGaussianCovEntry
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (h27 : ∀ i : S, BddAbove (Set.range fun Λ : Finset S ↦ invGaussianCovEntry J Λ i i))
    (i j : S) :
    ∃ c : ℝ, Filter.Tendsto (fun Λ : Finset S ↦ invGaussianCovEntry J Λ i j)
      Filter.atTop (nhds c) := by
  classical
  obtain ⟨Mi, hMi⟩ := h27 i
  obtain ⟨Mj, hMj⟩ := h27 j
  have hMi' : ∀ Λ : Finset S, invGaussianCovEntry J Λ i i ≤ Mi :=
    fun Λ ↦ hMi ⟨Λ, rfl⟩
  have hMj' : ∀ Λ : Finset S, invGaussianCovEntry J Λ j j ≤ Mj :=
    fun Λ ↦ hMj ⟨Λ, rfl⟩
  have hMi0 : 0 ≤ Mi := le_trans (invGaussianCovEntry_diag_nonneg hPD ∅ i) (hMi' ∅)
  have hMj0 : 0 ≤ Mj := le_trans (invGaussianCovEntry_diag_nonneg hPD ∅ j) (hMj' ∅)
  have hci := tendsto_atTop_ciSup (monotone_invGaussianCovEntry_diag hPD i) (h27 i)
  have hcj := tendsto_atTop_ciSup (monotone_invGaussianCovEntry_diag hPD j) (h27 j)
  -- The four-entry sum is bounded above.
  have hpairbdd : BddAbove (Set.range fun Λ : Finset S ↦ invGaussianCovPair J Λ i j) := by
    refine ⟨2 * (Mi + Mj), ?_⟩
    rintro _ ⟨Λ, rfl⟩
    show invGaussianCovPair J Λ i j ≤ 2 * (Mi + Mj)
    by_cases hij : i ∈ Λ ∧ j ∈ Λ
    · rw [invGaussianCovPair_of_mem hij.1 hij.2]
      have hb := two_mul_inv_gaussianCovMatrix_le hPD Λ ⟨i, hij.1⟩ ⟨j, hij.2⟩
      have hsym := inv_gaussianCovMatrix_symm hPD Λ (⟨j, hij.2⟩ : Λ) ⟨i, hij.1⟩
      have ha := hMi' Λ
      have hd := hMj' Λ
      rw [invGaussianCovEntry_of_mem hij.1 hij.1] at ha
      rw [invGaussianCovEntry_of_mem hij.2 hij.2] at hd
      rw [invGaussianCovEntry_of_mem hij.1 hij.1, invGaussianCovEntry_of_mem hij.1 hij.2,
        invGaussianCovEntry_of_mem hij.2 hij.1, invGaussianCovEntry_of_mem hij.2 hij.2]
      linarith
    · rw [show invGaussianCovPair J Λ i j = 0 from by simp [invGaussianCovPair, hij]]
      linarith
  have hcp := tendsto_atTop_ciSup (monotone_invGaussianCovPair hPD i j) hpairbdd
  refine ⟨((⨆ Λ : Finset S, invGaussianCovPair J Λ i j)
      - (⨆ Λ : Finset S, invGaussianCovEntry J Λ i i)
      - ⨆ Λ : Finset S, invGaussianCovEntry J Λ j j) / 2, ?_⟩
  refine Filter.Tendsto.congr' ?_ (((hcp.sub hci).sub hcj).div_const 2)
  refine Filter.eventually_atTop.2 ⟨{i, j}, fun Λ hΛ ↦ ?_⟩
  have hi : i ∈ Λ := hΛ (by simp)
  have hj : j ∈ Λ := hΛ (by simp)
  have hsym := inv_gaussianCovMatrix_symm hPD Λ (⟨j, hj⟩ : Λ) ⟨i, hi⟩
  show (invGaussianCovPair J Λ i j - invGaussianCovEntry J Λ i i
    - invGaussianCovEntry J Λ j j) / 2 = invGaussianCovEntry J Λ i j
  rw [invGaussianCovPair_of_mem hi hj, invGaussianCovEntry_of_mem hi hi,
    invGaussianCovEntry_of_mem hi hj, invGaussianCovEntry_of_mem hj hi,
    invGaussianCovEntry_of_mem hj hj, hsym]
  ring

/-- For `I ⊆ Λ` the `I`-block of `𝒥_Λ⁻¹` is `ProbabilityTheory.covMatrix` of the extended entry
function. -/
lemma covMatrix_invGaussianCovEntry_eq_submatrix {I Λ : Finset S} (hIΛ : I ⊆ Λ) :
    ProbabilityTheory.covMatrix (invGaussianCovEntry J Λ) I
      = (Potential.gaussianCovMatrix J Λ)⁻¹.submatrix
          (fun a : I ↦ (⟨a.1, hIΛ a.2⟩ : Λ)) (fun a : I ↦ (⟨a.1, hIΛ a.2⟩ : Λ)) := by
  funext a b
  exact invGaussianCovEntry_of_mem (hIΛ a.2) (hIΛ b.2)

/-- For `I ⊆ Λ` the `I`-block of `𝒥_Λ⁻¹` is positive semidefinite. -/
lemma posSemidef_covMatrix_invGaussianCovEntry
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {I Λ : Finset S}
    (hIΛ : I ⊆ Λ) : (ProbabilityTheory.covMatrix (invGaussianCovEntry J Λ) I).PosSemidef := by
  rw [covMatrix_invGaussianCovEntry_eq_submatrix hIΛ]
  exact (hPD Λ).inv.posSemidef.submatrix _

/-- **The limiting covariance function `C` of Georgii (13.25) is nonnegative definite.** -/
theorem posSemidef_covMatrix_of_tendsto
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {C : S → S → ℝ}
    (hC : ∀ i j, Filter.Tendsto (fun Λ : Finset S ↦ invGaussianCovEntry J Λ i j)
      Filter.atTop (nhds (C i j))) (I : Finset S) :
    (ProbabilityTheory.covMatrix C I).PosSemidef := by
  have hsymm : ∀ i j : S, C i j = C j i := by
    intro i j
    refine tendsto_nhds_unique (hC i j) ?_
    have : (fun Λ : Finset S ↦ invGaussianCovEntry J Λ j i)
        = fun Λ : Finset S ↦ invGaussianCovEntry J Λ i j :=
      funext fun Λ ↦ (invGaussianCovEntry_symm hPD Λ i j).symm
    rw [← this]
    exact hC j i
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · refine Matrix.IsHermitian.ext fun a b ↦ ?_
    simpa using hsymm b.1 a.1
  · have hlim : Filter.Tendsto
        (fun Λ : Finset S ↦ x ⬝ᵥ (ProbabilityTheory.covMatrix (invGaussianCovEntry J Λ) I) *ᵥ x)
        Filter.atTop (nhds (x ⬝ᵥ (ProbabilityTheory.covMatrix C I) *ᵥ x)) := by
      show Filter.Tendsto
        (fun Λ : Finset S ↦ ∑ a : I, x a * ∑ b : I, invGaussianCovEntry J Λ a b * x b)
        Filter.atTop (nhds (∑ a : I, x a * ∑ b : I, C a b * x b))
      refine tendsto_finsetSum _ fun a _ ↦ Filter.Tendsto.const_mul _ ?_
      exact tendsto_finsetSum _ fun b _ ↦ (hC a.1 b.1).mul_const _
    have hev : ∀ᶠ Λ : Finset S in Filter.atTop,
        (0 : ℝ) ≤ x ⬝ᵥ (ProbabilityTheory.covMatrix (invGaussianCovEntry J Λ) I) *ᵥ x := by
      refine Filter.eventually_atTop.2 ⟨I, fun Λ hΛ ↦ ?_⟩
      simpa using (posSemidef_covMatrix_invGaussianCovEntry hPD hΛ).dotProduct_mulVec_nonneg x
    simpa using ge_of_tendsto hlim hev

/-- **The limiting covariance function `C` of Georgii (13.25) is an inverse of `J`**, for `J` of
finite row support: `∑_{j ∈ S} J(i,j) C(j,k) = δ_{ik}`. Georgii's computation
`∑_{j ∈ S} J(i,j) C(j,k) = lim_Λ ∑_{j ∈ Λ} J(i,j) 𝒥_Λ⁻¹(j,k) = δ_{ik}`, where for `Λ` containing
`i`, `k` and the (finite) support of the `i`-th row of `J` the inner sum is exactly the `(i,k)`
entry of `𝒥_Λ 𝒥_Λ⁻¹ = 1`. -/
theorem isInverse_of_tendsto_invGaussianCovEntry
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef) {C : S → S → ℝ}
    (hC : ∀ i j, Filter.Tendsto (fun Λ : Finset S ↦ invGaussianCovEntry J Λ i j)
      Filter.atTop (nhds (C i j))) (i k : S) :
    ∑' j, J i j * C j k = if i = k then 1 else 0 := by
  classical
  set T : Finset S := (hFin i).toFinset with hT
  have hT0 : ∀ j : S, j ∉ T → J i j = 0 := fun j hj ↦ by
    by_contra hne
    exact hj ((hFin i).mem_toFinset.2 hne)
  have hts : ∑' j, J i j * C j k = ∑ j ∈ T, J i j * C j k :=
    tsum_eq_sum fun j hj ↦ by rw [hT0 j hj, zero_mul]
  have hlim : Filter.Tendsto (fun Λ : Finset S ↦ ∑ j ∈ T, J i j * invGaussianCovEntry J Λ j k)
      Filter.atTop (nhds (∑ j ∈ T, J i j * C j k)) :=
    tendsto_finsetSum _ fun j _ ↦ Filter.Tendsto.const_mul _ (hC j k)
  have hev : ∀ᶠ Λ : Finset S in Filter.atTop,
      ∑ j ∈ T, J i j * invGaussianCovEntry J Λ j k = if i = k then 1 else 0 := by
    refine Filter.eventually_atTop.2 ⟨T ∪ {i, k}, fun Λ hΛ ↦ ?_⟩
    have hTΛ : T ⊆ Λ := (Finset.subset_union_left).trans hΛ
    have hiΛ : i ∈ Λ := hΛ (Finset.mem_union_right _ (by simp))
    have hkΛ : k ∈ Λ := hΛ (Finset.mem_union_right _ (by simp))
    have hmul : (Potential.gaussianCovMatrix J Λ * (Potential.gaussianCovMatrix J Λ)⁻¹)
        ⟨i, hiΛ⟩ ⟨k, hkΛ⟩ = if i = k then 1 else 0 := by
      rw [Matrix.mul_nonsing_inv _ (Matrix.PosDef.det_pos (hPD Λ)).ne'.isUnit, Matrix.one_apply]
      by_cases hik : i = k
      · subst hik
        simp
      · have hne : (⟨i, hiΛ⟩ : Λ) ≠ ⟨k, hkΛ⟩ := fun hh ↦ hik (by
          have hval := congrArg (fun z : Λ ↦ (z : S)) hh
          simpa using hval)
        simp [hne, hik]
    have hsumΛ : ∑ j : Λ, Potential.gaussianCovMatrix J Λ ⟨i, hiΛ⟩ j
        * (Potential.gaussianCovMatrix J Λ)⁻¹ j ⟨k, hkΛ⟩ = if i = k then 1 else 0 := by
      rw [← hmul, Matrix.mul_apply]
    have hcoe : ∑ j : Λ, Potential.gaussianCovMatrix J Λ ⟨i, hiΛ⟩ j
        * (Potential.gaussianCovMatrix J Λ)⁻¹ j ⟨k, hkΛ⟩
        = ∑ j ∈ Λ, J i j * invGaussianCovEntry J Λ j k := by
      rw [← Finset.sum_coe_sort Λ fun j ↦ J i j * invGaussianCovEntry J Λ j k]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [invGaussianCovEntry_of_mem j.2 hkΛ]
      rfl
    have hrestrict : ∑ j ∈ Λ, J i j * invGaussianCovEntry J Λ j k
        = ∑ j ∈ T, J i j * invGaussianCovEntry J Λ j k := by
      refine (Finset.sum_subset hTΛ fun j _ hj ↦ ?_).symm
      rw [hT0 j hj, zero_mul]
    rw [← hrestrict, ← hcoe, hsumΛ]
  rw [hts]
  exact tendsto_nhds_unique hlim
    (Filter.Tendsto.congr' (hev.mono fun _ hΛ ↦ hΛ.symm) tendsto_const_nhds)

/-- **Georgii Theorem (13.26), the sufficiency half.** Let `J : S × S → ℝ` be symmetric with
finite row support (`{j : J(i,j) ≠ 0} ∈ 𝒮`) and every `𝒥_Λ` positive definite, and let `h ∈ Ω`.
If `M_{J,h} ≠ ∅` and Georgii's condition (13.27) holds — `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞` for every
`i ∈ S`, stated here as boundedness above of the net `Λ ↦ 𝒥_Λ⁻¹(i,i)` — then
`𝒢(γ^{J,h}) ≠ ∅`.

The proof is Georgii's: (13.27) and the monotonicity
`∑_{i,j ∈ Λ} 𝒥_Λ⁻¹(i,j) t_i t_j ≤ ∑_{i,j ∈ Λ} 𝒥_Δ⁻¹(i,j) t_i t_j` produce the limits (13.25)
(`exists_tendsto_invGaussianCovEntry`); the limit function `C` is nonnegative definite
(`posSemidef_covMatrix_of_tendsto`) and inverts `J`
(`isInverse_of_tendsto_invGaussianCovEntry`, using the finite range); Proposition (13.A7)
(`ProbabilityTheory.gaussianField`) produces the centred Gauss field `μ_C`, which satisfies
condition (b) of Theorem (13.22) at `h = 0`, and Remark (13.23)(b) transports it to
`τ^m(μ_C) ∈ 𝒢(γ^{J,h})` for every `m ∈ M_{J,h}`. -/
theorem nonempty_G_gaussianSpecification_of_bddAbove [Countable S]
    (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCovMatrix J Λ).PosDef)
    (h27 : ∀ i : S, BddAbove (Set.range fun Λ : Finset S ↦ invGaussianCovEntry J Λ i i))
    {h : S → ℝ} (hM : (Potential.gaussianMeanSet J h).Nonempty) :
    (MeasureTheory.GibbsMeasure.G
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty := by
  classical
  obtain ⟨m, hm⟩ := hM
  choose C hC using exists_tendsto_invGaussianCovEntry hPD h27
  exact nonempty_G_gaussianSpecification_of_posSemidef_of_isInverse hFin hSymm hPD C
    (posSemidef_covMatrix_of_tendsto hPD hC)
    (isInverse_of_tendsto_invGaussianCovEntry hFin hPD hC) hm

end Theorem13_26Limits

end MeasureTheory.GibbsMeasure

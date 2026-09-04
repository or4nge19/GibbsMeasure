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

* `MeasureTheory.GibbsMeasure.spinTranslation m`: **Georgii's `τ^m`** (the display opening §13.2),
  `τ^m ω = ω + m`, as a `Transformation S ℝ` (5.1) — the sites are fixed and the spin at `i` is
  translated by `m_i`. `Specification.map` (5.4) and Georgii (5.10)
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
* **The last step of Georgii's proofs of Theorems (13.26) and (13.31)**,
  `MeasureTheory.GibbsMeasure.isGibbsMeasure_map_add_of_centered_of_isInverse` and
  `nonempty_G_gaussianSpecification_of_centered_of_isInverse`: if a *centred* Gaussian field
  `μ_C` whose covariance `C` inverts `J` exists, then `τ^m(μ_C) ∈ 𝒢(γ^{J,h})` for every
  `m ∈ M_{J,h}`, so `𝒢(γ^{J,h}) ≠ ∅` whenever `M_{J,h} ≠ ∅`. This is (13.22)(b) ⟹ (a) at `h = 0`
  followed by (13.23)(b), exactly as Georgii closes both proofs.
* **Georgii Theorem (13.26), the existence half, granted the limit (13.25)**,
  `MeasureTheory.GibbsMeasure.nonempty_G_gaussianSpecification_of_posSemidef_of_isInverse`: if
  `C : S × S → ℝ` is nonnegative definite and inverts `J`, then `𝒢(γ^{J,h}) ≠ ∅` for every `h`
  with `M_{J,h} ≠ ∅`. The centred Gauss field `μ_C` of Proposition (13.A7) is now available as
  `ProbabilityTheory.gaussianField`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Existence.lean`), so this is the
  previous item with its hypothesis discharged.

## What is *not* proved here, and why

* **Georgii Theorem (13.22), (a) ⟹ (b)** is not proved. For finite range it does not need
  (13.A6) either. The missing steps are: the identification of `∫ x_i dγ^{J,h}_{\{i\}}(x|ω)`
  and `∫ x_i² dγ^{J,h}_{\{i\}}(x|ω)` with `ξ_i(ω)` and `ξ_i(ω)² + J(i,i)⁻¹` (Proposition
  (13.13) at `Λ = {i}`, i.e. `Potential.gaussianSpecification_apply` together with
  `ProbabilityTheory.integral_eval_multivariateGaussianPi` and
  `integral_sub_mul_sub_multivariateGaussianPi` — the second moment additionally needs
  `Integrable (fun ζ ↦ ζ i ^ 2) (multivariateGaussianPi A m)`, which
  `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Density.lean` proves only in its
  density-weighted form `integrable_dotProduct_sq_mul_exp_neg_half_dotProduct_mulVec`); these fed
  into `ProbabilityTheory.Kernel.condExp_ae_eq_integral_kernel`
  (`GibbsMeasure/Prereqs/Kernel/CondExpBind.lean`) turn `μ ∈ 𝒢(γ^{J,h})` into `ξ_i^μ = ξ_i` a.s.
  and `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`; from there Georgii's computation of
  `μ((X_i - μ(X_i))(σ_k - m_k))` uses only `integral_sub_condExpOutside`,
  `integral_eval_mul_sub_condExpOutside_eq_zero` (`GaussianField.lean`) and
  `covariance_gaussianRowForm_eval` below. This is a self-contained further step and is simply
  not attempted.
* **Georgii Remark (13.23)(d)** (`M_{J,0} ≠ {0}` implies `𝒢(γ^{J,h}) = ∅` or `ex 𝒢(γ^{J,h})`
  uncountable) needs, besides (c): `ex 𝒢 ≠ ∅` when `𝒢 ≠ ∅` (Theorem (7.26)), which *is* in the
  tree as `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_G_of_isGibbsMeasure`; that `τ^m`
  maps `ex 𝒢` into itself (Remark (7.2)), which is not, though
  `mem_extremePoints_G_iff_isTailTrivial` reduces it to the invariance of the tail σ-algebra under
  `τ^m`; and the injectivity of `t ↦ τ^{t m}(μ)`, which amounts to the fact that no probability
  measure on `ℝ` is invariant under a non-zero translation, also not in the tree.
* **Georgii Theorems (13.24) and (13.26)/(13.31) proper.** (13.24) needs Theorem (7.12) (every
  extreme Gibbs measure is a local limit `lim_n γ_{Λ_n}(·|ω)`) together with Proposition (13.A5)
  (a local limit of Gaussian fields is Gaussian). Proposition (13.A7) — the existence of a centred
  Gaussian field with a prescribed nonnegative definite covariance function — is no longer
  missing: it is `ProbabilityTheory.gaussianField` in
  `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Existence.lean`, a Kolmogorov extension
  of the projective family of (possibly degenerate) multivariate Gaussians
  `ProbabilityTheory.multivariateGaussian`. What is still missing for (13.26) is the *first* half
  of its proof: that hypothesis (13.27), `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`, forces the limits (13.25) to
  exist, via the monotonicity `∑_{i,j ∈ Λ} 𝒥_Λ⁻¹(i,j) t_i t_j ≤ ∑_{i,j ∈ Λ} 𝒥_Δ⁻¹(i,j) t_i t_j`
  for `Λ ⊆ Δ` (a statement about `γ^{J,h}`, proved from Proposition (13.13) and Jensen). Likewise
  (13.31) needs the Fourier-analytic input (13.A8)/(13.A9). The potential-theoretic identity of
  Comment (13.28) is not attempted either.

## General lemmas proved in the Mathlib layer for this file

* `ProbabilityTheory.multivariateGaussianPi_map_add_right`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Density.lean`): the pushforward of
  `multivariateGaussianPi A m` along `x ↦ x + v` is `multivariateGaussianPi A (m + v)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ## Georgii's spin translation `τ^m` -/

variable {S : Type*}

/-- **Georgii's spin translation `τ^m`** (the display opening §13.2): `τ^m ω = ω + m`, as a
transformation (5.1) of the configuration space acting trivially on the sites and by the
translation `x ↦ x + m_i` on the spin at site `i`. -/
def spinTranslation (m : S → ℝ) : Transformation S ℝ where
  sites := Equiv.refl S
  spin i := MeasurableEquiv.addRight (m i)

@[simp] lemma spinTranslation_toFun (m ω : S → ℝ) : (spinTranslation m).toFun ω = ω + m := by
  funext i
  simp [Transformation.toFun, spinTranslation]

@[simp] lemma spinTranslation_inv_toFun (m ω : S → ℝ) :
    (spinTranslation m).inv.toFun ω = ω - m := by
  funext i
  simp [Transformation.toFun, Transformation.inv, spinTranslation, sub_eq_add_neg]

@[simp] lemma spinTranslation_sites (m : S → ℝ) : (spinTranslation m).sites = Equiv.refl S := rfl

end MeasureTheory.GibbsMeasure

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

end MeasureTheory.GibbsMeasure

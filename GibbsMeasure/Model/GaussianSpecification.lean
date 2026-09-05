/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianField
public import GibbsMeasure.Specification.GluedFamily
public import GibbsMeasure.Specification.ZeroDirac
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Tsum
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import GibbsMeasure.Specification.CondExpGibbs

/-!
# Georgii §13.2: Gibbs measures for Gaussian specifications

This file continues `GibbsMeasure/Model/GaussianField.lean` (Georgii §13.1: (13.1)–(13.8),
(13.11)–(13.13)) into the remainder of §13.1 and the start of §13.2. The book's actual numbering
(read from `.axiomatic/reference_docs/.../13.1 Gauss fields as Gibbs measures.md` and
`13.2 Gibbs measures for Gaussian specifications.md`) is: (13.9) the convergence set `Ω_J`,
(13.10) the conditional distribution of a single spin, (13.11)–(13.13) already in
`GaussianField.lean`, (13.18) Definition of `γ^{J,h}` by gluing the Gibbsian part on `Ω_J` to a
Dirac reference off it, (13.21) the affine set `M_{J,h}`, (13.22) the theorem characterizing
`𝒢(γ^{J,h})` for a *given* Gaussian field by its mean and covariance. §13.2 proper starts only at
Remark (13.23).

## What is proved here

* **Georgii Lemma (13.10)**, `MeasureTheory.GibbsMeasure.georgii_13_10`, with Georgii's exact
  hypotheses: `J` symmetric positive definite (`Matrix.PosDef (Matrix.of J)`), `h ∈ Ω`, `μ` a
  Gaussian field with (i) `μ(Ω_J) = 1`, (ii) `μ((σ_i - ξ_i^μ)²) = J(i,i)⁻¹`, (iii) (13.5). The
  conclusion is that the conditional distribution of `σ_i` given `𝒯_{\{i\}}` is Gaussian with
  mean `ξ_i = -J(i,i)⁻¹(h_i + ∑_{j ≠ i} J(i,j)σ_j)` (`gaussianCondMean`) and variance `J(i,i)⁻¹`:
  `μ(A | 𝒯_{\{i\}})(ω) = 𝒩(ξ_i(ω), J(i,i)⁻¹)({x : ω with ω_i := x ∈ A})` a.s. The core of the
  proof, valid for *every* Gaussian field, is
  `MeasureTheory.GibbsMeasure.condExp_indicator_ae_eq_gaussianReal_map_update` (mean `ξ_i^μ`,
  variance `Γ(i,i)`), built from the independence of the residual `σ_i - ξ_i^μ` from `𝒯_{\{i\}}`
  (`indep_cylinderEvents_compl_comap_sub_condExpOutside`) and the general "conditional law of a
  function of an independent input" `ProbabilityTheory.condExp_indicator_ae_eq_map_of_indep`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/CondExp.lean`). Georgii's
  restatement "the conditional distribution is Gibbsian for `Φ^{J,h}`" is
  `condExp_indicator_ae_eq_gaussianSpecification_singleton` for `J` of finite row support:
  `μ(A | 𝒯_{\{i\}}) = γ^{J,h}_{\{i\}}(A | ·)` a.s., via the one-dimensional identification
  `ProbabilityTheory.multivariateGaussianPi_unique` of `multivariateGaussianPi` with
  `gaussianReal`.

* **Georgii (13.9), general `J`.** `Potential.gaussianConvergenceSet J` (`Ω_J`) and
  `Potential.gaussianConvergenceSubmodule J`: `Ω_J` is a linear subspace of `Ω = S → ℝ`, and (given
  `[Countable S]`) it is tail-measurable
  (`Potential.measurableSet_tail_gaussianConvergenceSet`), matching the book's unproved-but-used
  remark "`Ω_J ∈ 𝒯`". For `J` of finite row support, `Ω_J = Ω`
  (`Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport`), Georgii's "trivial" case
  preceding Theorem (13.26).
* **Georgii (13.21).** `Potential.gaussianMeanSet J h` (`M_{J,h}`) and
  `Potential.gaussianMeanSubmodule J` (`M_{J,0}`, a linear subspace); `M_{J,h}` is a coset of
  `M_{J,0}` (`Potential.gaussianMeanSet_iff_sub_mem_gaussianMeanSubmodule`), Georgii's remark right
  after (13.21).
* **Georgii Theorem (13.20)**, `MeasureTheory.GibbsMeasure.georgii_13_20`: a Gaussian field `μ`
  with (i) `Γ(i,i) > 0` for all `i` and (ii) the Markov property of Proposition (13.7) is a Gibbs
  measure for the specification `γ^{J,h}` built from its own conditional covariances,
  `J = condCoupling μ` and `h = condExternalField μ`. The specification is well defined because
  `J` is symmetric, of finite row support (`finite_setOf_condCoupling_ne_zero`) and has every
  `𝒥_Λ` positive definite (`posDef_gaussianCouplingMatrix_condCoupling`). Georgii's proof, verbatim:
  (13.7), (13.10), (13.13) and (1.33), the last in the conditional-probability form
  `Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq`
  (`GibbsMeasure/Specification/CondExpGibbs.lean`).
* **Georgii (13.18), finite range.** `Specification.zeroDirac S E`, a general reference
  specification (the Dirac mass at the configuration vanishing on `Λ` and agreeing with the
  boundary condition off `Λ`), used for Georgii's "otherwise" branch. Georgii's gluing itself is
  `Specification.glued` (Remark (2.26), `GibbsMeasure/Specification/GluedFamily.lean`) applied to
  the two-valued family `Potential.gaussianSpecificationBranch` along the tail-measurable indicator
  of `Ω_J`: `Potential.gaussianGluedSpecification`. For `J` of finite row support this coincides
  with `Potential.gaussianSpecification`
  (`Potential.gaussianGluedSpecification_eq_gaussianSpecification`), because `Ω_J = Ω` makes the
  "otherwise" branch vacuous.

## What is not proved here, and why

* **Genuinely infinite-range `J` in (13.18).** Constructing the "on `Ω_J`" branch for an infinite
  range `J` needs a version of `Potential.hamiltonian_gaussianPotential_eq` and
  `Potential.isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor`
  (`GaussianField.lean`) with the boundary field `∑_{j ∉ Λ} J(i,j)ω_j` interpreted as the absolutely
  convergent series guaranteed by `ω ∈ Ω_J`, rather than the finite sum `hFin` provides. This is a
  further, self-contained development (already flagged as missing in `GaussianField.lean`'s module
  doc) and is not attempted here; `Potential.gaussianGluedSpecification` below is stated and proved
  only for finite row support.
* **Georgii (13.22)**, the theorem characterizing which Gauss fields (given their mean and
  covariance) are Gibbs for `γ^{J,h}`, is *not* proved here. Its direction (b) ⟹ (a) for `J` of
  finite range is `MeasureTheory.GibbsMeasure.georgii_13_22_of_finiteRowSupport` in
  `GibbsMeasure/Model/GaussianGibbs.lean`, built on Lemma (13.10) below and on Theorem (1.33) in
  the conditional-probability form
  `Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq`
  (`GibbsMeasure/Specification/CondExpGibbs.lean`); its direction (a) ⟹ (b) is still open — for
  infinite range it needs Corollary (13.A6) (a.s. convergence of `∑_j J(i,j)σ_j` implies `L²`
  convergence for a Gaussian family), which is not in this tree, and the missing steps in the
  finite-range case are listed in `GaussianGibbs.lean`'s module doc.
  `Potential.gaussianMeanSet`/`gaussianMeanSubmodule` above are (13.21) exactly as Georgii states
  them.

## General lemmas (Mathlib-bound)

* `MeasureTheory.measurable_ennreal_tsum`: `Measurable (fun x ↦ ∑' i, f i x)` for a countable
  family of measurable `ℝ≥0∞`-valued functions. Mathlib already proves exactly this as
  `Measurable.ennreal_tsum`, but that lemma is `deprecated` (since 2026-04-30) in favour of
  `Measurable.tsum` from `Mathlib.MeasureTheory.Constructions.Polish.Basic`, and that replacement
  does not exist in this checkout's pinned mathlib (only a differently-typed `Measurable.tsum` for
  `SummationFilter`s does). Restated here under a fresh name to avoid the deprecation warning;
  intended eventual home is wherever the dangling deprecation gets fixed.
* `ENNReal.tsum_ofReal_ne_top_iff_summable`
  (`GibbsMeasure/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`, next to
  `ENNReal.tsum_coe_ne_top_iff_summable`): for `F : ι → ℝ` nonnegative, `∑' i, ENNReal.ofReal (F i)
  ≠ ⊤` iff `Summable F` — the converse of Mathlib's `Summable.tsum_ofReal_ne_top`.
* `ProbabilityTheory.multivariateGaussianPi_unique`
  (`GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Density.lean`): on a singleton index
  type, the multivariate Gaussian with precision `A` and mean `m` is
  `gaussianReal (m default) (A default default)⁻¹` pushed forward along `x ↦ (fun _ ↦ x)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal NNReal

noncomputable section

/-! ## Georgii (13.9): the convergence set `Ω_J` -/

namespace Potential

variable {S : Type*} (J : S → S → ℝ)

/-- **Georgii (13.9).** The set of configurations against which every row of `J` sums absolutely:
`Ω_J = {ω : ∑_{j ∈ S} |J(i,j)ω_j| < ∞ for all i ∈ S}`. No hypothesis on `J` (symmetry, positive
definiteness, finite range) is needed for the definition. -/
def gaussianConvergenceSet (J : S → S → ℝ) : Set (S → ℝ) :=
  {ω | ∀ i, Summable (fun j ↦ |J i j * ω j|)}

lemma mem_gaussianConvergenceSet_iff {ω : S → ℝ} :
    ω ∈ gaussianConvergenceSet J ↔ ∀ i, Summable (fun j ↦ |J i j * ω j|) := Iff.rfl

/-- Georgii's remark preceding Theorem (13.26): "if `J` has finite range, the condition
`μ_C(Ω_J) = 1` is trivial", i.e. `Ω_J = Ω`. Every row sum is then a finite sum. -/
theorem gaussianConvergenceSet_eq_univ_of_finiteRowSupport
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) : gaussianConvergenceSet J = Set.univ := by
  refine Set.eq_univ_of_forall fun ω i ↦ ?_
  have hsub : {j : S | ¬ |J i j * ω j| = (0 : S → ℝ) j} ⊆ {j | J i j ≠ 0} := by
    intro j hj hJ0
    exact hj (by simp [hJ0])
  have hfin : {j : S | ¬ |J i j * ω j| = (0 : S → ℝ) j}.Finite := (hFin i).subset hsub
  have hcof : (fun j ↦ |J i j * ω j|) =ᶠ[Filter.cofinite] (0 : S → ℝ) :=
    Filter.eventuallyEq_of_mem hfin.compl_mem_cofinite fun j hj ↦ not_not.mp hj
  exact (summable_congr_cofinite hcof).2 summable_zero

section Submodule

/-- **`Ω_J` is a linear subspace of `Ω = S → ℝ`.** Georgii does not name this fact explicitly for
`Ω_J` (only for `M_{J,0}` after (13.21)), but it is used implicitly (e.g. Theorem (13.24)'s
`μ_C * v`, `v` a law on `Ω_J`) and the proof is identical to the one for `M_{J,0}` below. -/
def gaussianConvergenceSubmodule (J : S → S → ℝ) : Submodule ℝ (S → ℝ) where
  carrier := gaussianConvergenceSet J
  zero_mem' := fun i ↦ by simp
  add_mem' {ω ω'} hω hω' := fun i ↦ by
    refine Summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) (fun j ↦ ?_)
      ((hω i).add (hω' i))
    calc |J i j * (ω j + ω' j)| = |J i j * ω j + J i j * ω' j| := by ring_nf
      _ ≤ |J i j * ω j| + |J i j * ω' j| := abs_add_le _ _
  smul_mem' c {ω} hω := fun i ↦ by
    have : (fun j ↦ |J i j * (c • ω) j|) = fun j ↦ |c| * |J i j * ω j| := by
      funext j; rw [Pi.smul_apply, smul_eq_mul]; rw [← abs_mul]; ring_nf
    rw [this]
    exact (hω i).mul_left _

@[simp] lemma mem_gaussianConvergenceSubmodule_iff {ω : S → ℝ} :
    ω ∈ gaussianConvergenceSubmodule J ↔ ω ∈ gaussianConvergenceSet J := Iff.rfl

end Submodule

section TailMeasurable

variable [Countable S]

/-- `Ω_J` is measurable in the ordinary (product) σ-algebra: writing "`∑_j |J(i,j)ω_j| < ∞`" as
"`∑'_j ENNReal.ofReal |J(i,j)ω_j| ≠ ⊤`" turns it into a countable intersection, over `i`, of
preimages of `{⊤}ᶜ` under the (by `MeasureTheory.measurable_ennreal_tsum`) measurable function
`ω ↦ ∑'_j ENNReal.ofReal |J(i,j)ω_j|`. -/
theorem measurableSet_gaussianConvergenceSet : MeasurableSet (gaussianConvergenceSet J) := by
  have hset : gaussianConvergenceSet J =
      ⋂ i, {ω : S → ℝ | (∑' j, ENNReal.ofReal |J i j * ω j|) ≠ ⊤} := by
    ext ω
    simp only [gaussianConvergenceSet, Set.mem_iInter, Set.mem_ofPred_eq]
    exact forall_congr' fun i ↦
      (ENNReal.tsum_ofReal_ne_top_iff_summable fun j ↦ abs_nonneg (J i j * ω j)).symm
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hmeas : Measurable fun ω : S → ℝ ↦ ∑' j, ENNReal.ofReal |J i j * ω j| :=
    MeasureTheory.measurable_ennreal_tsum fun j ↦
      (show Measurable fun ω : S → ℝ ↦ |J i j * ω j| by fun_prop).ennreal_ofReal
  exact hmeas (measurableSet_singleton ⊤).compl

omit [Countable S] in
/-- **`Ω_J` is invariant under changing the configuration on any finite set `Λ`**: absolute
convergence of a series does not depend on finitely many of its terms
(`summable_congr_cofinite`). This is the content behind Georgii's unproved remark that `Ω_J` is
tail-measurable ("`Ω_J ∈ 𝒯`", preceding (13.18)). -/
theorem gaussianConvergenceSet_congr {Λ : Finset S} {ω ω' : S → ℝ}
    (h : ∀ i ∈ (Λ : Set S)ᶜ, ω i = ω' i) :
    ω ∈ gaussianConvergenceSet J ↔ ω' ∈ gaussianConvergenceSet J := by
  simp only [mem_gaussianConvergenceSet_iff]
  refine forall_congr' fun i ↦ summable_congr_cofinite ?_
  have hfin : {j : S | ¬ (fun j ↦ |J i j * ω j|) j = (fun j ↦ |J i j * ω' j|) j} ⊆ (Λ : Set S) := by
    intro j hj
    by_contra hjΛ
    exact hj (by simp only [h j (by simpa using hjΛ)])
  exact Filter.eventuallyEq_of_mem ((Λ.finite_toSet.subset hfin).compl_mem_cofinite)
    fun j hj ↦ not_not.mp hj

omit [Countable S] in
theorem dependsOn_indicator_gaussianConvergenceSet (Λ : Finset S) :
    DependsOn ((gaussianConvergenceSet J).indicator (1 : (S → ℝ) → ℝ)) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  by_cases h : ω ∈ gaussianConvergenceSet J
  · have h' : ω' ∈ gaussianConvergenceSet J := (gaussianConvergenceSet_congr J hωω').1 h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    rfl
  · have h' : ω' ∉ gaussianConvergenceSet J :=
      fun hc ↦ h ((gaussianConvergenceSet_congr J hωω').2 hc)
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

/-- **Georgii, `Ω_J ∈ 𝒯`.** `Ω_J` is tail-measurable, given `S` countable. -/
theorem measurableSet_tail_gaussianConvergenceSet :
    MeasurableSet[MeasureTheory.GibbsMeasure.tailSigmaAlgebra S ℝ] (gaussianConvergenceSet J) := by
  rw [MeasureTheory.GibbsMeasure.tailSigmaAlgebra, MeasurableSpace.measurableSet_iInf]
  intro Λ
  have hmeas : Measurable ((gaussianConvergenceSet J).indicator (1 : (S → ℝ) → ℝ)) :=
    measurable_one.indicator (measurableSet_gaussianConvergenceSet J)
  have hcyl : Measurable[cylinderEvents ((Λ : Set S)ᶜ)]
      ((gaussianConvergenceSet J).indicator (1 : (S → ℝ) → ℝ)) :=
    hmeas.cylinderEvents_of_dependsOn (dependsOn_indicator_gaussianConvergenceSet J Λ)
  have hpre : ((gaussianConvergenceSet J).indicator (1 : (S → ℝ) → ℝ)) ⁻¹' {(1 : ℝ)} =
      gaussianConvergenceSet J := by
    ext ω
    by_cases h : ω ∈ gaussianConvergenceSet J
    · simp [h]
    · simp [h]
  exact hpre ▸ hcyl (measurableSet_singleton (1 : ℝ))

end TailMeasurable

/-! ## Georgii (13.21): the affine set `M_{J,h}` -/

section GaussianMeanSet

/-- A row of `J` sums *signedly* against any `m ∈ Ω_J` (not merely absolutely): this is what lets
`∑_{j ∈ S} J(i,j)m_j` in (13.21) make sense as an honest converging sum. -/
theorem summable_gaussianConvergenceSet {m : S → ℝ} (hm : m ∈ gaussianConvergenceSet J) (i : S) :
    Summable (fun j ↦ J i j * m j) :=
  Summable.of_norm (by simpa [Real.norm_eq_abs] using hm i)

/-- **Georgii (13.21).** `M_{J,h} = {m ∈ Ω_J : h_i + ∑_{j ∈ S} J(i,j)m_j = 0 for all i ∈ S}`. -/
def gaussianMeanSet (J : S → S → ℝ) (h : S → ℝ) : Set (S → ℝ) :=
  {m | m ∈ gaussianConvergenceSet J ∧ ∀ i, h i + ∑' j, J i j * m j = 0}

lemma mem_gaussianMeanSet_iff {h : S → ℝ} {m : S → ℝ} :
    m ∈ gaussianMeanSet J h ↔ m ∈ gaussianConvergenceSet J ∧ ∀ i, h i + ∑' j, J i j * m j = 0 :=
  Iff.rfl

/-- **`M_{J,0}` is a linear subspace of `Ω`**, Georgii's remark right after (13.21). -/
def gaussianMeanSubmodule (J : S → S → ℝ) : Submodule ℝ (S → ℝ) where
  carrier := gaussianMeanSet J 0
  zero_mem' := ⟨(gaussianConvergenceSubmodule J).zero_mem, fun i ↦ by simp⟩
  add_mem' {m m'} hm hm' := by
    obtain ⟨hmΩ, hmeq⟩ := hm
    obtain ⟨hm'Ω, hm'eq⟩ := hm'
    refine ⟨(gaussianConvergenceSubmodule J).add_mem hmΩ hm'Ω, fun i ↦ ?_⟩
    have hsplit : (fun j ↦ J i j * (m + m') j) = fun j ↦ J i j * m j + J i j * m' j := by
      funext j; simp [mul_add]
    have e1 : ∑' j, J i j * m j = 0 := by simpa using hmeq i
    have e2 : ∑' j, J i j * m' j = 0 := by simpa using hm'eq i
    rw [hsplit, Summable.tsum_add (summable_gaussianConvergenceSet J hmΩ i)
      (summable_gaussianConvergenceSet J hm'Ω i), e1, e2]
    simp
  smul_mem' c {m} hm := by
    obtain ⟨hmΩ, hmeq⟩ := hm
    refine ⟨(gaussianConvergenceSubmodule J).smul_mem c hmΩ, fun i ↦ ?_⟩
    have hsplit : (fun j ↦ J i j * (c • m) j) = fun j ↦ c * (J i j * m j) := by
      funext j; simp [smul_eq_mul]; ring
    have e1 : ∑' j, J i j * m j = 0 := by simpa using hmeq i
    rw [hsplit, tsum_mul_left, e1]
    simp

@[simp] lemma mem_gaussianMeanSubmodule_iff {m : S → ℝ} :
    m ∈ gaussianMeanSubmodule J ↔ m ∈ gaussianMeanSet J 0 := Iff.rfl

/-- **Georgii's remark right after (13.21): `M_{J,h}` is a coset of `M_{J,0}`.** Given one solution
`m₀` of the affine system, `m` is another solution iff `m - m₀` solves the homogeneous system. -/
theorem gaussianMeanSet_iff_sub_mem_gaussianMeanSubmodule {h : S → ℝ} {m₀ : S → ℝ}
    (hm₀ : m₀ ∈ gaussianMeanSet J h) {m : S → ℝ} :
    m ∈ gaussianMeanSet J h ↔ m - m₀ ∈ gaussianMeanSubmodule J := by
  obtain ⟨hm₀Ω, hm₀eq⟩ := hm₀
  constructor
  · rintro ⟨hmΩ, hmeq⟩
    refine ⟨(gaussianConvergenceSubmodule J).sub_mem hmΩ hm₀Ω, fun i ↦ ?_⟩
    have hsplit : (fun j ↦ J i j * (m - m₀) j) = fun j ↦ J i j * m j - J i j * m₀ j := by
      funext j; simp [mul_sub]
    rw [hsplit, Summable.tsum_sub (summable_gaussianConvergenceSet J hmΩ i)
      (summable_gaussianConvergenceSet J hm₀Ω i)]
    have e1 : h i + ∑' j, J i j * m j = 0 := hmeq i
    have e2 : h i + ∑' j, J i j * m₀ j = 0 := hm₀eq i
    simp only [Pi.zero_apply]
    linarith
  · rintro ⟨hsubΩ, hsubeq⟩
    have hmΩ : m ∈ gaussianConvergenceSet J := by
      have hadd := (gaussianConvergenceSubmodule J).add_mem hsubΩ hm₀Ω
      rwa [sub_add_cancel] at hadd
    refine ⟨hmΩ, fun i ↦ ?_⟩
    have hsplit : (fun j ↦ J i j * (m - m₀) j) = fun j ↦ J i j * m j - J i j * m₀ j := by
      funext j; simp [mul_sub]
    have e0 : ∑' j, J i j * (m - m₀) j = 0 := by simpa using hsubeq i
    rw [hsplit, Summable.tsum_sub (summable_gaussianConvergenceSet J hmΩ i)
      (summable_gaussianConvergenceSet J hm₀Ω i)] at e0
    have e2 : h i + ∑' j, J i j * m₀ j = 0 := hm₀eq i
    linarith

/-- **Georgii's conclusion in Remark (13.39).** `M_{J,0}` is a linear subspace of `Ω`, so as soon
as it contains one non-zero element `m` it contains the whole line `ℝ m` and is uncountable. -/
theorem not_countable_gaussianMeanSet_zero {m : S → ℝ} (hm : m ∈ gaussianMeanSet J 0)
    (hm0 : m ≠ 0) : ¬ (gaussianMeanSet J 0).Countable := by
  intro hcount
  have hinj : Function.Injective fun t : ℝ ↦ t • m := fun a b hab ↦ by
    have hab' : a • m = b • m := hab
    by_contra hne
    have hzero : (a - b) • m = 0 := by rw [sub_smul, hab', sub_self]
    rcases smul_eq_zero.1 hzero with h | h
    · exact hne (sub_eq_zero.1 h)
    · exact hm0 h
  have hsub : Set.range (fun t : ℝ ↦ t • m) ⊆ gaussianMeanSet J 0 := by
    rintro _ ⟨t, rfl⟩
    exact (gaussianMeanSubmodule J).smul_mem t hm
  have : Countable ℝ := (Equiv.ofInjective _ hinj).countable_iff.2 (hcount.mono hsub).to_subtype
  exact Cardinal.not_countable_real Set.countable_univ

/-- **Georgii's conclusion in Remark (13.39).** `M_{J,h} = m₀ + M_{J,0}` is a coset of `M_{J,0}`,
so it is uncountable as soon as it is non-empty and `M_{J,0} ≠ {0}`. -/
theorem not_countable_gaussianMeanSet {h : S → ℝ} {m₀ : S → ℝ} (hm₀ : m₀ ∈ gaussianMeanSet J h)
    {m : S → ℝ} (hm : m ∈ gaussianMeanSet J 0) (hm0 : m ≠ 0) :
    ¬ (gaussianMeanSet J h).Countable := by
  intro hcount
  refine not_countable_gaussianMeanSet_zero J hm hm0 ((hcount.image fun x ↦ x - m₀).mono ?_)
  intro x hx
  refine ⟨x + m₀, ?_, by abel⟩
  rw [gaussianMeanSet_iff_sub_mem_gaussianMeanSubmodule J hm₀]
  simpa using hx

end GaussianMeanSet

end Potential

/-! ## A general reference specification: the Dirac mass vanishing on `Λ`

This is Georgii's "otherwise" branch of Definition (13.18): `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`. It is
completely general (any `S`, any `E` with a `Zero`), and lives at the level of `Specification`
(`GibbsMeasure/Specification/ZeroDirac.lean`), with no `Potential` or Gaussian import. -/

/-! ## Georgii, Definition (13.18): the glued specification, finite range

Georgii's Definition (13.18) glues the Gibbsian part of `γ^{J,h}` (defined only on `Ω_J`, where the
boundary field converges) to the Dirac reference `Specification.zeroDirac` off `Ω_J`. The gluing
itself is `Specification.glued` (Remark (2.26)): apply it to the two-valued family
`Potential.gaussianSpecificationBranch : Bool → Specification S ℝ` along the tail-measurable
indicator `Potential.gaussianConvergenceIndicator J` of `Ω_J`. For `J` of finite row support,
`Ω_J = Ω` (`gaussianConvergenceSet_eq_univ_of_finiteRowSupport`), so the indicator is constantly
`true` and the glued specification reduces to `gaussianSpecification` — the "otherwise" branch is
vacuous, exactly matching Georgii's remark that finite range makes the distinction moot. -/

namespace Potential

variable {S : Type*} [Countable S] [LinearOrder S] (J : S → S → ℝ) (h : S → ℝ)

section GluedSpecification

variable (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset S, (gaussianCouplingMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β)

/-- **Georgii (13.18), the two branches.** `true` is the Gibbsian Gaussian specification (used on
`Ω_J`); `false` is the Dirac reference (used off `Ω_J`). -/
noncomputable def gaussianSpecificationBranch : Bool → Specification S ℝ :=
  fun b ↦ if b then gaussianSpecification J h hSymm hFin hPD β hβ else Specification.zeroDirac S ℝ

@[simp] lemma gaussianSpecificationBranch_true :
    gaussianSpecificationBranch J h hSymm hFin hPD β hβ true =
      gaussianSpecification J h hSymm hFin hPD β hβ := rfl

@[simp] lemma gaussianSpecificationBranch_false :
    gaussianSpecificationBranch J h hSymm hFin hPD β hβ false = Specification.zeroDirac S ℝ := rfl

lemma isMeasurableFamily_gaussianSpecificationBranch :
    Specification.IsMeasurableFamily (gaussianSpecificationBranch J h hSymm hFin hPD β hβ) := by
  classical
  intro Λ A hA
  have hg : Measurable[cylinderEvents ((Λ : Set S)ᶜ)]
      (fun ω ↦ gaussianSpecification J h hSymm hFin hPD β hβ Λ ω A) := Kernel.measurable_coe _ hA
  have hz : Measurable[cylinderEvents ((Λ : Set S)ᶜ)]
      (fun ω ↦ Specification.zeroDirac S ℝ Λ ω A) := Kernel.measurable_coe _ hA
  have hset : @MeasurableSet (Bool × (S → ℝ))
      (@Prod.instMeasurableSpace Bool (S → ℝ) _ (cylinderEvents ((Λ : Set S)ᶜ)))
      (Prod.fst ⁻¹' ({true} : Set Bool)) :=
    measurable_fst MeasurableSpace.measurableSet_top
  have hfn : (fun p : Bool × (S → ℝ) ↦
      gaussianSpecificationBranch J h hSymm hFin hPD β hβ p.1 Λ p.2 A) =
      (Prod.fst ⁻¹' ({true} : Set Bool)).piecewise
        (fun p ↦ gaussianSpecification J h hSymm hFin hPD β hβ Λ p.2 A)
        (fun p ↦ Specification.zeroDirac S ℝ Λ p.2 A) := by
    funext p
    rcases p with ⟨b, ω⟩
    cases b <;> simp
  rw [hfn]
  exact Measurable.piecewise hset (hg.comp measurable_snd) (hz.comp measurable_snd)

/-- The indicator (as `Bool`, to serve as a two-valued parameter for `Specification.glued`) of the
tail event `Ω_J`. -/
noncomputable def gaussianConvergenceIndicator : (S → ℝ) → Bool :=
  open Classical in fun ω ↦ decide (ω ∈ gaussianConvergenceSet J)

omit [Countable S] [LinearOrder S] in
lemma gaussianConvergenceIndicator_eq_true_iff {ω : S → ℝ} :
    gaussianConvergenceIndicator J ω = true ↔ ω ∈ gaussianConvergenceSet J := by
  classical simp [gaussianConvergenceIndicator]

omit [LinearOrder S] in
theorem measurable_tail_gaussianConvergenceIndicator :
    Measurable[MeasureTheory.GibbsMeasure.tailSigmaAlgebra S ℝ]
      (gaussianConvergenceIndicator J) := by
  refine @measurable_to_countable' Bool (S → ℝ) _ _
    (MeasureTheory.GibbsMeasure.tailSigmaAlgebra S ℝ) (gaussianConvergenceIndicator J) fun x ↦ ?_
  cases x with
  | true =>
    have hpre : gaussianConvergenceIndicator J ⁻¹' {true} = gaussianConvergenceSet J := by
      ext ω; exact gaussianConvergenceIndicator_eq_true_iff J
    rw [hpre]; exact measurableSet_tail_gaussianConvergenceSet J
  | false =>
    have hpre : gaussianConvergenceIndicator J ⁻¹' {false} = (gaussianConvergenceSet J)ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff,
        ← gaussianConvergenceIndicator_eq_true_iff J]
      cases gaussianConvergenceIndicator J ω <;> simp
    rw [hpre]; exact (measurableSet_tail_gaussianConvergenceSet J).compl

/-- **Georgii, Definition (13.18), finite range.** The glued Gaussian specification, obtained from
`Specification.glued` applied to `gaussianSpecificationBranch` along the indicator of `Ω_J`. -/
noncomputable def gaussianGluedSpecification : Specification S ℝ :=
  Specification.glued (gaussianSpecificationBranch J h hSymm hFin hPD β hβ)
    (gaussianConvergenceIndicator J) (isMeasurableFamily_gaussianSpecificationBranch J h hSymm hFin
      hPD β hβ) (measurable_tail_gaussianConvergenceIndicator J)

/-- **For finite range `J`, Georgii's (13.18) coincides with `gaussianSpecification`.** `Ω_J = Ω`
makes the "otherwise" branch of the gluing vacuous. -/
theorem gaussianGluedSpecification_eq_gaussianSpecification :
    gaussianGluedSpecification J h hSymm hFin hPD β hβ =
      gaussianSpecification J h hSymm hFin hPD β hβ := by
  ext Λ ω
  have hω : ω ∈ gaussianConvergenceSet J := by
    rw [gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin]; trivial
  have hind : gaussianConvergenceIndicator J ω = true :=
    (gaussianConvergenceIndicator_eq_true_iff J).2 hω
  rw [gaussianGluedSpecification, Specification.glued_apply, hind]
  rfl

end GluedSpecification

end Potential

/-! ## Georgii Lemma (13.10): the conditional distribution of a single spin

For every Gaussian field `μ` (`S` countable) and every site `i`, the residual `σ_i - ξ_i^μ` is
jointly Gaussian with the spins off `i` (`isGaussianProcess_sum_elim_sub_condExpOutside`),
uncorrelated with them, hence independent of `𝒯_{\{i\}}`
(`indep_cylinderEvents_compl_comap_sub_condExpOutside`), with law `𝒩(0, Γ(i,i))`
(`map_sub_condExpOutside_eq_gaussianReal`). Consequently the conditional distribution of `σ_i`
given `𝒯_{\{i\}}` is Gaussian with mean `ξ_i^μ` and variance `Γ(i, i)`
(`condExp_indicator_ae_eq_gaussianReal_map_update`); this is the content of Georgii's proof of
(13.10) before he substitutes (13.5). Lemma (13.10) itself (`georgii_13_10`) then replaces `ξ_i^μ`
by the explicit affine function `ξ_i = -J(i,i)⁻¹ (h_i + ∑_{j ≠ i} J(i,j) σ_j)` on `Ω_J` and
`Γ(i, i)` by `J(i, i)⁻¹`, using its hypotheses (i)–(iii). -/

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} {μ : Measure (S → ℝ)}

/-- **Georgii's `ξ_i` in the proof of (13.10)**: the affine function
`ξ_i = -J(i, i)⁻¹ (h_i + ∑_{j ≠ i} J(i, j) σ_j)`, which agrees with `ξ_i^μ` on `Ω_J` under (13.5).
For `J` of finite row support this is `Potential.gaussianMean J h hFin {i}`. -/
noncomputable def gaussianCondMean [DecidableEq S] (J : S → S → ℝ) (h : S → ℝ) (i : S)
    (ω : S → ℝ) : ℝ :=
  -(J i i)⁻¹ * (h i + ∑' j, if j = i then 0 else J i j * ω j)

/-- On `Ω_J`, Georgii's `ξ_i` is (13.5) solved for `ξ_i^μ`. -/
lemma gaussianCondMean_eq_of_mem [DecidableEq S] {J : S → S → ℝ} {h : S → ℝ} {i : S}
    (hJ : J i i ≠ 0) {ω : S → ℝ} (hω : ω ∈ Potential.gaussianConvergenceSet J) :
    gaussianCondMean J h i ω = ω i - (J i i)⁻¹ * (h i + ∑' j, J i j * ω j) := by
  have hs : Summable fun j ↦ J i j * ω j := Potential.summable_gaussianConvergenceSet J hω i
  rw [gaussianCondMean, hs.tsum_eq_add_tsum_ite i]
  field_simp
  ring

section Residual

variable [Countable S] (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
include hμ

/-- **The residual `σ_i - ξ_i^μ` is jointly Gaussian with the spins off `i`.** Georgii's proof
of (13.10) obtains this from (13.5) and the closure of Gaussian vectors under a.s. limits
(his (13.A1), (13.A5)); here it is instead the closure of a Gaussian process under conditioning
(`ProbabilityTheory.IsGaussianProcess.sum_elim_condExp`), which needs no hypothesis on `μ`. -/
lemma isGaussianProcess_sum_elim_sub_condExpOutside (i : S) :
    ProbabilityTheory.IsGaussianProcess
      (Sum.elim (fun (_ : Unit) (ω : S → ℝ) ↦ ω i - condExpOutside μ i ω)
        fun (j : ({i}ᶜ : Set S)) (ω : S → ℝ) ↦ ω j) μ := by
  classical
  have hext := hμ.sum_elim_condExp (fun t ↦ measurable_pi_apply t)
    (Set.to_countable ({i}ᶜ : Set S))
  refine hext.of_isGaussianProcess fun r ↦ ?_
  cases r with
  | inl _ =>
    exact ⟨({Sum.inl i, Sum.inr i} : Finset (S ⊕ S)),
      { toFun x := x ⟨(Sum.inl i : S ⊕ S), by simp⟩ - x ⟨(Sum.inr i : S ⊕ S), by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; abel
        map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
      fun ω ↦ rfl⟩
  | inr j =>
    exact ⟨{Sum.inl (j : S)},
      { toFun x := x ⟨Sum.inl (j : S), by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp },
      fun ω ↦ rfl⟩

/-- **The residual `σ_i - ξ_i^μ` is independent of `𝒯_{\{i\}}`** (Georgii's proof of (13.10)):
it is uncorrelated with every `σ_j`, `j ≠ i`, and jointly Gaussian with them
(`ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero`, his Remark (13.A3)). -/
lemma indep_cylinderEvents_compl_comap_sub_condExpOutside (i : S) :
    ProbabilityTheory.Indep (cylinderEvents ({i}ᶜ : Set S))
      (MeasurableSpace.comap (fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω) inferInstance) μ := by
  have hP := hμ.isProbabilityMeasure
  have hL2 := memLp_two_eval hμ
  have hW : Measurable fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω :=
    (measurable_pi_apply i).sub (stronglyMeasurable_condExp.measurable.mono cylinderEvents_le_pi
      le_rfl)
  have hW2 : MemLp (fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω) 2 μ :=
    (hL2 i).sub ((hL2 i).condExp one_le_two)
  have hWmean : ∫ ω, (ω i - condExpOutside μ i ω) ∂μ = 0 :=
    integral_sub_condExpOutside i ((hL2 i).integrable one_le_two)
  have hcov : ∀ (_ : Unit) (j : ({i}ᶜ : Set S)),
      cov[fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω, fun ω ↦ ω j; μ] = 0 := by
    intro _ j
    have hji : (j : S) ≠ i := j.2
    rw [covariance_eq_sub hW2 (hL2 j), hWmean, zero_mul, sub_zero]
    rw [show ((fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω) * fun ω ↦ ω j) =
        fun ω ↦ ω j * (ω i - condExpOutside μ i ω) from funext fun ω ↦ mul_comm _ _]
    exact integral_eval_mul_sub_condExpOutside_eq_zero hji (hL2 i) (hL2 j)
  have h1 := (isGaussianProcess_sum_elim_sub_condExpOutside hμ i).indepFun_of_covariance_eq_zero
    (fun _ ↦ hW.aemeasurable) (fun j ↦ (measurable_pi_apply (j : S)).aemeasurable) hcov
  have h2 := h1.comp (measurable_pi_apply ()) measurable_id
  rw [IndepFun_iff_Indep] at h2
  refine Indep.symm ?_
  rw [cylinderEvents_eq_comap_restrict]
  exact h2

/-- **The law of the residual**: `σ_i - ξ_i^μ ∼ 𝒩(0, Γ(i, i))`. -/
lemma map_sub_condExpOutside_eq_gaussianReal (i : S) :
    μ.map (fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω) =
      gaussianReal 0 (condCovariance μ i i).toNNReal := by
  have hP := hμ.isProbabilityMeasure
  have hL2 := memLp_two_eval hμ
  have hW : Measurable fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω :=
    (measurable_pi_apply i).sub (stronglyMeasurable_condExp.measurable.mono cylinderEvents_le_pi
      le_rfl)
  have hWmean : ∫ ω, (ω i - condExpOutside μ i ω) ∂μ = 0 :=
    integral_sub_condExpOutside i ((hL2 i).integrable one_le_two)
  have hg : ProbabilityTheory.HasGaussianLaw (fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω) μ :=
    (isGaussianProcess_sum_elim_sub_condExpOutside hμ i).hasGaussianLaw_eval (Sum.inl ())
  rw [hg.map_eq_gaussianReal, hWmean, variance_eq_integral hW.aemeasurable, hWmean]
  congr 2
  unfold condCovariance
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by simp [pow_two])

/-- **The conditional distribution of `σ_i` given the other spins of a Gaussian field is Gaussian
with mean `ξ_i^μ` and variance `Γ(i, i)`** (the core of Georgii's proof of Lemma (13.10)): for every
measurable `A`,
`μ(A | 𝒯_{\{i\}})(ω) = ∫ 1_A(ω with ω_i := x) 𝒩(ξ_i^μ(ω), Γ(i,i))(dx)` a.s.
The residual `σ_i - ξ_i^μ` is independent of `𝒯_{\{i\}}`
(`indep_cylinderEvents_compl_comap_sub_condExpOutside`) with law `𝒩(0, Γ(i,i))`; conditionally on
`𝒯_{\{i\}}` the configuration is therefore `ω` with `ω_i` replaced by `ξ_i^μ(ω) + W`, `W` an
independent copy of the residual (`ProbabilityTheory.condExp_indicator_ae_eq_map_of_indep`). -/
theorem condExp_indicator_ae_eq_gaussianReal_map_update [DecidableEq S] (i : S)
    {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    μ[A.indicator 1 | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] fun ω ↦
      ((gaussianReal (condExpOutside μ i ω) (condCovariance μ i i).toNNReal).map
        (Function.update ω i) A).toReal := by
  have hP := hμ.isProbabilityMeasure
  have hξm : Measurable[cylinderEvents ({i}ᶜ : Set S)] (condExpOutside μ i) :=
    stronglyMeasurable_condExp.measurable
  have hW : Measurable fun ω : S → ℝ ↦ ω i - condExpOutside μ i ω :=
    (measurable_pi_apply i).sub (hξm.mono cylinderEvents_le_pi le_rfl)
  set G : (S → ℝ) × ℝ → (S → ℝ) :=
    fun p ↦ Function.update p.1 i (condExpOutside μ i p.1 + p.2) with hG_def
  have hG : Measurable[(cylinderEvents ({i}ᶜ : Set S)).prod inferInstance, MeasurableSpace.pi]
      G := by
    refine (@measurable_pi_iff _ _ _ ((cylinderEvents ({i}ᶜ : Set S)).prod inferInstance) _ _).2
      fun j ↦ ?_
    by_cases hj : j = i
    · simp only [hG_def, hj, Function.update_self]
      exact (hξm.comp (@measurable_fst _ _ (cylinderEvents ({i}ᶜ : Set S)) _)).add
        (@measurable_snd _ _ (cylinderEvents ({i}ᶜ : Set S)) _)
    · simp only [hG_def, Function.update_of_ne hj]
      exact (measurable_cylinderEvent_apply (X := fun _ : S ↦ ℝ) (Δ := ({i}ᶜ : Set S))
        (by simpa using hj)).comp (@measurable_fst _ _ (cylinderEvents ({i}ᶜ : Set S)) _)
  have hGW : ∀ ω, G (ω, ω i - condExpOutside μ i ω) = ω := fun ω ↦ by
    simp [hG_def]
  have hmain := ProbabilityTheory.condExp_indicator_ae_eq_map_of_indep cylinderEvents_le_pi hW
    (indep_cylinderEvents_compl_comap_sub_condExpOutside hμ i) hG hGW hA
  refine hmain.trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  beta_reduce
  rw [map_sub_condExpOutside_eq_gaussianReal hμ i]
  congr 1
  rw [show gaussianReal (condExpOutside μ i ω) (condCovariance μ i i).toNNReal =
      (gaussianReal 0 (condCovariance μ i i).toNNReal).map (condExpOutside μ i ω + ·) by
        rw [gaussianReal_map_const_add, zero_add],
    Measure.map_map (measurable_update ω) (measurable_const_add _),
    Measure.map_apply ((measurable_update ω).comp (measurable_const_add _)) hA]
  rfl

end Residual

/-- **Georgii Lemma (13.10).** Let `J : S × S → ℝ` be symmetric and positive definite
(`Matrix.PosDef`, in Georgii's finitely-supported sense (13.3)), `h ∈ Ω`, and `μ` a Gaussian field
with (i) `μ(Ω_J) = 1`, (ii) `μ((σ_i - ξ_i^μ)²) = J(i, i)⁻¹` for all `i`, and (iii) (13.5) for all
`i`. Then for each `i`, the conditional distribution of `σ_i` given `𝒯_{\{i\}}` is Gaussian with
expectation `ξ_i^μ` — which on `Ω_J` is the explicit affine function
`ξ_i = -J(i, i)⁻¹ (h_i + ∑_{j ≠ i} J(i, j) σ_j)` (`gaussianCondMean`) — and variance `J(i, i)⁻¹`:
for every `A ∈ 𝓕`,
`μ(A | 𝒯_{\{i\}})(ω) = ∫ 1_A(ω with ω_i := x) 𝒩(ξ_i(ω), J(i, i)⁻¹)(dx)` for `μ`-a.e. `ω`.
Georgii's density `ρ_{\{i\}}` is the Lebesgue density of `𝒩(ξ_i(ω), J(i, i)⁻¹)`. -/
theorem georgii_13_10 [Countable S] [DecidableEq S] {J : S → S → ℝ} {h : S → ℝ}
    (hJ : (Matrix.of J).PosDef)
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
    (hΩ : μ (Potential.gaussianConvergenceSet J) = 1)
    (hvar : ∀ i, ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹)
    (h135 : ∀ i, ∀ᵐ ω ∂μ, ω i - condExpOutside μ i ω = (J i i)⁻¹ * (h i + ∑' j, J i j * ω j))
    (i : S) {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    μ[A.indicator 1 | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] fun ω ↦
      ((gaussianReal (gaussianCondMean J h i ω) (Real.toNNReal (J i i)⁻¹)).map
        (Function.update ω i) A).toReal := by
  have hP := hμ.isProbabilityMeasure
  have hJii : J i i ≠ 0 := by
    have := hJ.diag_pos (i := i)
    rw [Matrix.of_apply] at this
    exact this.ne'
  have hae : ∀ᵐ ω ∂μ, ω ∈ Potential.gaussianConvergenceSet J :=
    (ae_iff_measure_eq (Potential.measurableSet_gaussianConvergenceSet J).nullMeasurableSet).2
      (hΩ.trans measure_univ.symm)
  have hvar' : (condCovariance μ i i).toNNReal = Real.toNNReal (J i i)⁻¹ := by
    rw [← hvar i]
    unfold condCovariance
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  refine (condExp_indicator_ae_eq_gaussianReal_map_update hμ i hA).trans ?_
  filter_upwards [hae, h135 i] with ω hω h5
  rw [hvar', gaussianCondMean_eq_of_mem hJii hω, ← h5, sub_sub_cancel]

/-- For `J` of finite row support, Georgii's `ξ_i` of (13.10) is the mean `m_{\{i\}}(ω)` of
Proposition (13.13) at the singleton `{i}`: `-J(i,i)⁻¹ (h_i + ∑_{j ∉ \{i\}} J(i,j) ω_j)`. -/
lemma gaussianCondMean_eq_gaussianMean [LinearOrder S] {J : S → S → ℝ} (h : S → ℝ)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) {i : S} (hJ : J i i ≠ 0) (ω : S → ℝ) :
    gaussianCondMean J h i ω =
      Potential.gaussianMean J h hFin {i} ω ⟨i, Finset.mem_singleton_self i⟩ := by
  classical
  have hinv : (Potential.gaussianCouplingMatrix J {i})⁻¹ = (J i i)⁻¹ • (1 : Matrix _ _ ℝ) := by
    rw [Matrix.inv_def, Matrix.adjugate_subsingleton, Matrix.det_unique, Ring.inverse_eq_inv']
    rfl
  have hsum : ∑' j, (if j = i then 0 else J i j * ω j) =
      Potential.gaussianBoundaryField J hFin {i} ω i := by
    rw [Potential.gaussianBoundaryField, tsum_eq_sum (s := (hFin i).toFinset \ {i}) ?_]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
      rw [ite_eq_right hj.2]
    · intro j hj
      rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton,
        not_and_or, not_not, not_not] at hj
      rcases hj with hj | rfl
      · simp [hj]
      · simp
  rw [gaussianCondMean, Potential.gaussianMean, hinv, hsum]
  simp [Matrix.smul_mulVec]

/-- **Georgii's restatement of Lemma (13.10)** (the paragraph following it): for `J` symmetric of
finite row support with every `𝒥_Λ` positive definite, the conditional distribution of `σ_i`
given `𝒯_{\{i\}}` under a Gaussian field `μ` satisfying (13.10)(ii)–(iii) is *Gibbsian for
`Φ^{J,h}`*: `μ(A | 𝒯_{\{i\}}) = γ^{J,h}_{\{i\}}(A | ·)` `μ`-a.s., with `γ^{J,h}` the Gaussian
specification of Definition (2.9)/(13.18) at inverse temperature `1`. (Hypothesis (13.10)(i),
`μ(Ω_J) = 1`, is automatic: `Ω_J = Ω` for finite range.) This is the input Theorem (1.33) needs
for (13.20). -/
theorem condExp_indicator_ae_eq_gaussianSpecification_singleton [Countable S] [LinearOrder S]
    {J : S → S → ℝ} {h : S → ℝ} (hSymm : ∀ i j, J i j = J j i)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset S, (Potential.gaussianCouplingMatrix J Λ).PosDef)
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
    (hvar : ∀ i, ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹)
    (h135 : ∀ i, ∀ᵐ ω ∂μ, ω i - condExpOutside μ i ω = (J i i)⁻¹ * (h i + ∑' j, J i j * ω j))
    (i : S) {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    μ[A.indicator 1 | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] fun ω ↦
      (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos {i} ω A).toReal := by
  have hP := hμ.isProbabilityMeasure
  have hJ : (Matrix.of J).PosDef := Matrix.posDef_iff_forall_finset_submatrix.2 fun Λ ↦ hPD Λ
  have hΩ : μ (Potential.gaussianConvergenceSet J) = 1 := by
    rw [Potential.gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin, measure_univ]
  have hJii : 0 < J i i := (hPD {i}).diag_pos (i := ⟨i, Finset.mem_singleton_self i⟩)
  refine (georgii_13_10 hJ hμ hΩ hvar h135 i hA).trans (Filter.Eventually.of_forall fun ω ↦ ?_)
  beta_reduce
  rw [Potential.gaussianSpecification_apply, one_smul,
    multivariateGaussianPi_unique (ι := ({i} : Finset S)) hJii,
    Measure.map_map Measurable.juxt (MeasurableEquiv.measurable _),
    gaussianCondMean_eq_gaussianMean h hFin hJii.ne']
  have hfun : Function.update ω i = juxt (({i} : Finset S) : Set S) ω ∘
      (MeasurableEquiv.funUnique ({i} : Finset S) ℝ).symm := by
    funext x j
    simp only [Function.comp_apply, MeasurableEquiv.funUnique_symm_apply]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self,
        juxt_apply_of_mem (Finset.mem_coe.2 (Finset.mem_singleton_self j))]
      rfl
    · rw [Function.update_of_ne hj, juxt_apply_of_not_mem (by simpa using hj)]
  rw [hfun]
  rfl

/-! ## Georgii Theorem (13.20): a Markovian Gauss field is a Gibbs measure

Georgii's proof is "combine Proposition (13.7), Lemma (13.10), Proposition (13.13), and
Theorem (1.33)": (13.7) produces `J` and `h` out of the conditional covariances and the mean of
`μ`, together with its finite range, its positive definiteness and (13.5); (13.10) plus (13.13)
identify `μ(A | 𝒯_{\{i\}})` with `γ^{J,h}_{\{i\}}(A | ·)`
(`condExp_indicator_ae_eq_gaussianSpecification_singleton`); and (1.33)
(`Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq`, the conditional-probability
form of `Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq` proved in
`GibbsMeasure/Specification/CondExpGibbs.lean`) upgrades the single-site identities to the full
DLR equations. -/

section Theorem13_20

/-- For a Markovian Gaussian field — Georgii (13.20)(ii): `ξ_i^μ` has an `𝓕_{∂i}`-measurable
version for a finite `∂i` — the coupling `J = condCoupling μ` of Proposition (13.7) has finite row
support, `{j : J(i,j) ≠ 0} ⊆ ∂i ∪ {i}`. This is Georgii's finite range (2.15) for `Φ^{J,h}`, and
the hypothesis `hFin` of `Potential.gaussianSpecification`. -/
theorem finite_setOf_condCoupling_ne_zero [DecidableEq S]
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
    {N : S → Finset S}
    (hMarkov : ∀ i, AEStronglyMeasurable[cylinderEvents (N i : Set S)] (condExpOutside μ i) μ)
    (i : S) : {j : S | condCoupling μ i j ≠ 0}.Finite := by
  refine Set.Finite.subset (insert i (N i) : Finset S).finite_toSet fun j hj ↦ ?_
  by_contra hjmem
  rw [Finset.mem_coe, Finset.mem_insert, not_or] at hjmem
  exact hj (condCoupling_eq_zero_of_notMem hμ (hMarkov i) hjmem.1 hjmem.2)

/-- **Georgii Theorem (13.20).** Let `μ` be a Gaussian field such that

* (i) `Γ(i, i) = μ((σ_i - μ(σ_i | 𝒯_{\{i\}}))²) > 0` for all `i` — Georgii's
  `μ(σ_i ≠ μ(σ_i|𝒯_{\{i\}})) > 0`, i.e. the spin at `i` is not a.s. determined by the others; and
* (ii) for each `i` there is a finite `∂i ∌ i` with `μ(σ_i | 𝒯_{\{i\}}) = μ(σ_i | 𝓕_{∂i})` a.s.

Define `J = condCoupling μ` and `h = condExternalField μ` from the conditional covariances and the
mean of `μ` as in Proposition (13.7). Then `γ^{J,h}` is well defined — `J` is symmetric
(`condCoupling_comm`), of finite range (`finite_setOf_condCoupling_ne_zero`) and every `𝒥_Λ` is
positive definite (`posDef_gaussianCouplingMatrix_condCoupling`), which is exactly what
`Potential.gaussianSpecification` consumes — and `μ ∈ 𝒢(γ^{J,h})`. -/
theorem georgii_13_20 [Countable S] [LinearOrder S] [DecidableEq S]
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ)
    (hΓ : ∀ j, 0 < condCovariance μ j j) (N : S → Finset S) (hN : ∀ i, i ∉ N i)
    (hMarkov : ∀ i, AEStronglyMeasurable[cylinderEvents (N i : Set S)] (condExpOutside μ i) μ) :
    (Potential.gaussianSpecification (condCoupling μ) (condExternalField μ)
      (fun i j ↦ condCoupling_comm i j)
      (finite_setOf_condCoupling_ne_zero hμ hMarkov)
      (fun Λ ↦ posDef_gaussianCouplingMatrix_condCoupling hμ hΓ N hN hMarkov Λ) 1
      one_pos).IsGibbsMeasure μ := by
  classical
  have hP := hμ.isProbabilityMeasure
  set J := condCoupling μ with hJdef
  set hh := condExternalField μ with hhdef
  have hSymm : ∀ i j, J i j = J j i := fun i j ↦ condCoupling_comm i j
  have hFin : ∀ i, {j : S | J i j ≠ 0}.Finite := finite_setOf_condCoupling_ne_zero hμ hMarkov
  have hPD : ∀ Λ : Finset S, (Potential.gaussianCouplingMatrix J Λ).PosDef :=
    fun Λ ↦ posDef_gaussianCouplingMatrix_condCoupling hμ hΓ N hN hMarkov Λ
  have hvar : ∀ i, ∫ ω, (ω i - condExpOutside μ i ω) ^ 2 ∂μ = (J i i)⁻¹ := by
    intro i
    rw [hJdef, condCoupling_self (hΓ i).ne', inv_inv]
    unfold condCovariance
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ sq _)
  have h135 := (georgii_13_7 hμ hΓ N hN hMarkov).2.2
  have := Potential.isPotential_gaussianPotential J hh
  have := Potential.isFiniteRange_gaussianPotential J hh hSymm hFin
  have hadm := Potential.isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor J hh
    hSymm hFin hPD 1 one_pos
  have hEq : Potential.gaussianSpecification J hh hSymm hFin hPD 1 one_pos =
      Specification.lambdaSpecification (S := S) (E := ℝ) volume
        ((Potential.gaussianPotential J hh).boltzmannFactor 1)
        (Potential.isPremodifier_boltzmannFactor 1) hadm := rfl
  rw [hEq]
  refine Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq volume _
    (fun Λ ω ↦ (Potential.boltzmannFactor_pos 1 Λ ω).ne')
    (fun Λ ω ↦ Potential.boltzmannFactor_ne_top 1 Λ ω) hadm ?_
  intro i A hA
  rw [← hEq]
  exact condExp_indicator_ae_eq_gaussianSpecification_singleton hSymm hFin hPD hμ hvar h135 i hA

end Theorem13_20

end MeasureTheory.GibbsMeasure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianField
public import GibbsMeasure.Specification.GluedFamily

/-!
# Georgii §13.2: Gibbs measures for Gaussian specifications

This file continues `GibbsMeasure/Model/GaussianField.lean` (Georgii §13.1, up to Proposition
(13.13)) into the remainder of §13.1 and the start of §13.2. The book's actual numbering (read
from `.axiomatic/reference_docs/.../13.1 Gauss fields as Gibbs measures.md` and
`13.2 Gibbs measures for Gaussian specifications.md`) is: (13.9) the convergence set `Ω_J`,
(13.11)–(13.13) already in `GaussianField.lean`, (13.18) Definition of `γ^{J,h}` by gluing the
Gibbsian part on `Ω_J` to a Dirac reference off it, (13.21) the affine set `M_{J,h}`, (13.22) the
theorem characterizing `𝒢(γ^{J,h})` for a *given* Gaussian field by its mean and covariance.
§13.2 proper starts only at Remark (13.23).

## What is proved here

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
  covariance) are Gibbs for `γ^{J,h}`. Tracing through the book's proof: direction (a) ⟹ (b) uses
  Corollary (13.A6) (a.s. convergence of `∑_j J(i,j)σ_j` implies `L²` convergence for a Gaussian
  family), which is not in this tree. Direction (b) ⟹ (a) reduces, via Lemma (13.10) and Theorem
  (1.33) (already in `GibbsMeasure/Specification/Singleton.lean` as
  `Specification.isGibbsMeasure_iff_forall_singleton_bind_eq`, if `gaussianSpecification` is
  exhibited as a `Specification.lambdaSpecification`), to a *single* fact: for `μ` Gaussian with
  mean `m ∈ M_{J,h}` and covariance `C` an inverse of `J`, `σ_i - ξ_i^μ` (an explicit finite linear
  combination of `(σ_j - m_j)_j`, given finite range) is mean-zero, variance `J(i,i)⁻¹`, and
  uncorrelated with — hence, by
  `ProbabilityTheory.IsGaussianProcess.indepFun_of_covariance_eq_zero` (which *is* in Mathlib),
  independent of — every `σ_k`, `k ≠ i`. What remains beyond that computation is a "reconstruct the
  joint law from an independent factorization compatible with `juxt`" lemma: if `ξ` depends only on
  coordinates `≠ i` and `Y := σ_i - ξ` is independent of them with law `ν`, then
  `μ.bind (fun ω ↦ (ν.map (ξ ω + ·)).map (fun x ↦ juxt {i} ω x)) = μ`. This reconstruction lemma is
  not built anywhere in this tree; formalizing Theorem (13.22) is future work gated on it, not on
  any further mathematical gap. `Potential.gaussianMeanSet`/`gaussianMeanSubmodule` above are (13.21)
  exactly as Georgii states them, ready for that theorem's statement.

## General lemmas (Mathlib-bound)

* `MeasureTheory.measurable_ennreal_tsum`: `Measurable (fun x ↦ ∑' i, f i x)` for a countable
  family of measurable `ℝ≥0∞`-valued functions. Mathlib already proves exactly this as
  `Measurable.ennreal_tsum`, but that lemma is `deprecated` (since 2026-04-30) in favour of
  `Measurable.tsum` from `Mathlib.MeasureTheory.Constructions.Polish.Basic`, and that replacement
  does not exist in this checkout's pinned mathlib (only a differently-typed `Measurable.tsum` for
  `SummationFilter`s does). Restated here under a fresh name to avoid the deprecation warning;
  intended eventual home is wherever the dangling deprecation gets fixed.
* `summable_abs_iff_tsum_ofReal_ne_top`: for `F : ι → ℝ` nonnegative, `Summable F` iff
  `∑' i, ENNReal.ofReal (F i) ≠ ⊤`. Intended home: `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`,
  next to `ENNReal.tsum_coe_ne_top_iff_summable`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal NNReal

noncomputable section

/-! ## General lemmas -/

namespace MeasureTheory

theorem measurable_ennreal_tsum {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {f : ι → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) : Measurable fun x ↦ ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact Measurable.iSup fun s ↦ s.measurable_fun_sum fun i _ ↦ hf i

end MeasureTheory

theorem summable_abs_iff_tsum_ofReal_ne_top {ι : Type*} (F : ι → ℝ) (hF : ∀ j, 0 ≤ F j) :
    Summable F ↔ (∑' j, ENNReal.ofReal (F j)) ≠ ⊤ := by
  have hFg : F = fun j ↦ ((F j).toNNReal : ℝ) := funext fun j ↦ (Real.coe_toNNReal _ (hF j)).symm
  conv_lhs => rw [hFg]
  rw [NNReal.summable_coe, ← ENNReal.tsum_coe_ne_top_iff_summable]
  simp [ENNReal.ofReal]

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
    exact forall_congr' fun i ↦ summable_abs_iff_tsum_ofReal_ne_top _ fun j ↦ abs_nonneg _
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

end GaussianMeanSet

end Potential

/-! ## A general reference specification: the Dirac mass vanishing on `Λ`

This is Georgii's "otherwise" branch of Definition (13.18): `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`. It is
completely general (any `S`, any `E` with a `Zero`), not specific to the Gaussian setting, so it
belongs at the level of `Specification`, not `Potential`. Intended home: `GibbsMeasure/Specification/`
(e.g. next to `Specification.isssd` in `GibbsMeasure/Specification.lean`), no `Potential`/Gaussian
import needed. -/

namespace Specification

variable (S E : Type*) [MeasurableSpace E] [Zero E]

/-- The raw kernel `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`: the Dirac mass at the configuration agreeing
with `ω` off `Λ` and vanishing on `Λ`. -/
noncomputable def zeroDiracFun (Λ : Finset S) :
    Kernel[cylinderEvents ((Λ : Set S)ᶜ)] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _ (fun ω ↦ Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)))
    (Measure.measurable_dirac.comp (measurable_cylinderEvents_juxt_boundary (0 : Λ → E)))

@[simp] lemma zeroDiracFun_apply (Λ : Finset S) (ω : S → E) :
    zeroDiracFun S E Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) := rfl

variable {S E}

lemma isMarkovKernel_zeroDiracFun (Λ : Finset S) : IsMarkovKernel (zeroDiracFun S E Λ) :=
  ⟨fun ω ↦ by rw [zeroDiracFun_apply]; infer_instance⟩

lemma isProper_zeroDiracFun (Λ : Finset S) : (zeroDiracFun S E Λ).IsProper :=
  Kernel.IsProper.of_inter_eq_indicator_mul cylinderEvents_le_pi fun A hA B hB ω ↦ by
    have hBmeas : MeasurableSet B := cylinderEvents_le_pi _ hB
    have hcongr : juxt (Λ : Set S) ω (0 : Λ → E) ∈ B ↔ ω ∈ B :=
      mem_congr_of_measurableSet_cylinderEvents hB fun i hi ↦ juxt_apply_of_not_mem hi 0
    rw [zeroDiracFun_apply, Measure.dirac_apply' _ (hA.inter hBmeas), Measure.dirac_apply' _ hA]
    by_cases hωB : ω ∈ B
    · have hjB : juxt (Λ : Set S) ω 0 ∈ B := hcongr.2 hωB
      by_cases hjA : juxt (Λ : Set S) ω 0 ∈ A
      · simp [Set.indicator_of_mem (Set.mem_inter hjA hjB), Set.indicator_of_mem hωB,
          Set.indicator_of_mem hjA]
      · simp [Set.indicator_of_notMem
          (fun hmem : juxt (Λ : Set S) ω 0 ∈ A ∩ B ↦ hjA hmem.1),
          Set.indicator_of_mem hωB, Set.indicator_of_notMem hjA]
    · have hjB : juxt (Λ : Set S) ω 0 ∉ B := fun hc ↦ hωB (hcongr.1 hc)
      simp [Set.indicator_of_notMem
        (fun hmem : juxt (Λ : Set S) ω 0 ∈ A ∩ B ↦ hjB hmem.2),
        Set.indicator_of_notMem hωB]

omit [MeasurableSpace E] in
/-- The identity `juxt Λ₁ (juxt Λ₂ ω 0) 0 = juxt Λ₂ ω 0` for `Λ₁ ⊆ Λ₂`: resampling to `0` on `Λ₂`
and then again on the smaller `Λ₁` changes nothing further. -/
lemma juxt_juxt_zero_of_subset {Λ₁ Λ₂ : Finset S} (h : Λ₁ ⊆ Λ₂) (ω : S → E) :
    juxt (Λ₁ : Set S) (juxt (Λ₂ : Set S) ω (0 : Λ₂ → E)) (0 : Λ₁ → E) =
      juxt (Λ₂ : Set S) ω (0 : Λ₂ → E) := by
  funext x
  by_cases hx1 : x ∈ (Λ₁ : Set S)
  · have hx2 : x ∈ (Λ₂ : Set S) := h hx1
    rw [juxt_apply_of_mem hx1, juxt_apply_of_mem hx2]
    rfl
  · rw [juxt_apply_of_not_mem hx1]

lemma isConsistent_zeroDiracFun : IsConsistent (zeroDiracFun S E) := by
  intro Λ₁ Λ₂ hΛ
  ext ω A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  have h1 : ∀ ζ : S → E, ((zeroDiracFun S E Λ₁).comap id cylinderEvents_le_pi) ζ A =
      zeroDiracFun S E Λ₁ ζ A := fun _ ↦ rfl
  simp only [h1]
  rw [zeroDiracFun_apply]
  have hfmeas : Measurable (fun ζ : S → E ↦ zeroDiracFun S E Λ₁ ζ A) :=
    (Kernel.measurable_coe (zeroDiracFun S E Λ₁) hA).mono cylinderEvents_le_pi le_rfl
  rw [lintegral_dirac' _ hfmeas, zeroDiracFun_apply, juxt_juxt_zero_of_subset hΛ]

variable (S E) in
/-- The raw family before bundling the Markov and properness hypotheses. -/
noncomputable def zeroDiracPre : PreSpecification S E where
  toFun := zeroDiracFun S E
  isConsistent' := isConsistent_zeroDiracFun

variable (S E) in
/-- **The Dirac reference specification**: `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`. Georgii's "otherwise"
branch of Definition (13.18). -/
noncomputable def zeroDirac : Specification S E where
  toPreSpecification := zeroDiracPre S E
  isMarkovKernel' := isMarkovKernel_zeroDiracFun
  isProper' := isProper_zeroDiracFun

@[simp] lemma zeroDirac_apply (Λ : Finset S) (ω : S → E) :
    zeroDirac S E Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) := rfl

end Specification

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
  (hPD : ∀ Λ : Finset S, (gaussianCovMatrix J Λ).PosDef) (β : ℝ) (hβ : 0 < β)

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

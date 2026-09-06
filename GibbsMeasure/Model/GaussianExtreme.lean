/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianGibbs
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Translate
public import GibbsMeasure.Topology.GaussianLocalLimit
public import GibbsMeasure.Specification.ExtremeCorollaries

/-!
# Georgii Theorem (13.24): the extreme Gibbs measures of a Gaussian specification

Georgii's Theorem (13.24). For a symmetric `J : S × S → ℝ` of finite range with every `𝒥_Λ`
positive definite, if `𝒢(γ^{J,h}) ≠ ∅` then the limits

  `C(i,j) = lim_{Λ ∈ 𝒮} 𝒥_Λ⁻¹(i,j)`   (13.25)

exist, and a random field belongs to `ex 𝒢(γ^{J,h})` if and only if it is a Gauss field with
covariance function `C` and a mean `m ∈ M_{J,h}`.

The proof is Georgii's. Theorem (7.26) gives `ex 𝒢(γ^{J,h}) ≠ ∅`; Theorem (7.12)(c) — available
here as
`MeasureTheory.GibbsMeasure.ae_tendsto_finiteVolumeDistributions_exhaustion_lambdaSpecification`,
since `γ^{J,h}` is a λ-specification over Lebesgue measure — writes an extreme `μ` as a local
limit `lim_n γ^{J,h}_{Λ_n}(·|ω)` along the canonical exhaustion; Proposition (13.13) says each
`γ^{J,h}_{Λ_n}(·|ω)` is a Gauss field with covariance `𝒥_{Λ_n}⁻¹`; and Proposition (13.A5) — here
`MeasureTheory.GibbsMeasure.isGaussianProcess_of_tendsto_withLocalConvergence` — makes the limit
a Gauss field whose covariance is the limit of the `𝒥_{Λ_n}⁻¹`. The monotonicity of
`Λ ↦ 𝒥_Λ⁻¹(i,i)` then upgrades convergence along the exhaustion to convergence along the whole
net of finite volumes, which is Georgii's (13.25) and, at the same time, his condition (13.27);
Theorem (13.22) identifies the mean as an element of `M_{J,h}`; and `μ = μ_C * δ_m` because two
Gauss fields with the same mean and covariance coincide (`ProbabilityTheory.eq_gaussianField`).

## Main results

* `MeasureTheory.GibbsMeasure.isGaussianProcess_of_mem_extremePoints_G`: **(13.24)**, every
  extreme Gibbs measure for `γ^{J,h}` is a Gauss field.
* `MeasureTheory.GibbsMeasure.tendsto_gaussianCovEntry_covariance_of_mem_extremePoints_G`:
  **(13.25)** — the covariance function of an extreme Gibbs measure is the limit
  `lim_Λ 𝒥_Λ⁻¹(i,j)`, and in particular that limit exists.
* `MeasureTheory.GibbsMeasure.bddAbove_gaussianCovEntry_of_nonempty_G`: **Georgii's condition
  (13.27) is necessary**, `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`, as soon as `𝒢(γ^{J,h}) ≠ ∅`.
* `MeasureTheory.GibbsMeasure.nonempty_gaussianMeanSet_of_nonempty_G`: `M_{J,h} ≠ ∅` is
  necessary too.
* `MeasureTheory.GibbsMeasure.nonempty_G_gaussianSpecification_iff`: **Georgii Theorem (13.26)**
  in full, `𝒢(γ^{J,h}) ≠ ∅ ↔ M_{J,h} ≠ ∅ ∧ sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`.
* `MeasureTheory.GibbsMeasure.eq_map_add_gaussianField_of_mem_extremePoints_G`: **(13.24)**,
  `μ = μ_C * δ_m` for an extreme `μ`, where `μ_C` is the centred Gauss field with covariance `C`
  and `m ∈ M_{J,h}` is the mean of `μ`.
* `MeasureTheory.GibbsMeasure.isGibbsMeasure_of_isGaussianProcess_covariance_eq`: the converse
  inclusion of (13.24) at the level of `𝒢`: every Gauss field with covariance `C` and mean in
  `M_{J,h}` is a Gibbs measure for `γ^{J,h}`.
* `MeasureTheory.GibbsMeasure.map_add_mem_extremePoints_G`: **Georgii Remark (7.2) for spin
  translations** — `τ^m` maps `ex 𝒢(γ^{J,h'})` into `ex 𝒢(γ^{J,h+h'})` for `m ∈ M_{J,h}`. Both
  halves are available: `τ^m(μ) ∈ 𝒢(γ^{J,h+h'})` is Remark (13.23)(b), and extremality is
  tail-triviality (Georgii (7.7)), which `τ^m` preserves because it acts coordinatewise and
  therefore preserves every `𝓕_{Λᶜ}`
  (`MeasureTheory.GibbsMeasure.measurableSet_tail_preimage_add_const`,
  `MeasureTheory.GibbsMeasure.tailTrivial_map_add_const`).
* `MeasureTheory.GibbsMeasure.mem_extremePoints_G_gaussianField` and
  `MeasureTheory.GibbsMeasure.extremePoints_G_eq_image_gaussianField`: **Georgii Theorem (13.24)
  as he states it** — `ex 𝒢(γ^{J,h}) = {μ_C * δ_m : m ∈ M_{J,h}}`; and
  `MeasureTheory.GibbsMeasure.bijOn_map_add_gaussianField_extremePoints_G`, the bijection
  `M_{J,h} ≃ ex 𝒢(γ^{J,h})`.
* `MeasureTheory.GibbsMeasure.not_countable_extremePoints_G`: **Georgii Remark (13.23)(d)** — if
  `M_{J,0} ≠ {0}` then `𝒢(γ^{J,h})` is empty or `ex 𝒢(γ^{J,h})` is uncountable.

## What is *not* proved here

Georgii's final sentence, `𝒢(γ^{J,h}) = {μ_C * ν : ν ∈ 𝒫(Ω), ν(M_{J,h}) = 1}`, is Theorem (7.26)
(the extreme decomposition, in the tree as
`MeasureTheory.GibbsMeasure.exists_unique_weight_extremePoints`) transported along the bijection
`M_{J,h} ≃ ex 𝒢(γ^{J,h})` of `bijOn_map_add_gaussianField_extremePoints_G`. What is missing for
that transport is measure-theoretic bookkeeping that the tree does not have: the bijection has to
be shown *bimeasurable* between `M_{J,h}` with its trace σ-algebra and `ex 𝒢(γ^{J,h})` with the
σ-algebra of `𝒫(Ω, 𝓕)`, so that a weight `w` on `ex 𝒢` and a `ν` on `M_{J,h}` correspond and
`∫ τ^m(μ_C) ν(dm) = μ_C * ν`. The statement of (13.24) about `ex 𝒢` itself is complete above.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} [Countable S] [LinearOrder S] {J : S → S → ℝ} {h : S → ℝ}
  {μ : Measure (S → ℝ)}

/-! ### Georgii Remark (7.2) for spin translations, and `ex 𝒢(γ^{J,h}) = {μ_C * δ_m}` -/

section Translation

variable {E : Type*} [MeasurableSpace E] [Add E] [MeasurableAdd E]

omit [Countable S] [LinearOrder S] in
/-- **A spin translation preserves the tail σ-algebra.** `ω ↦ ω + m` acts coordinatewise, so it is
`𝓕_{Λᶜ}`-measurable for every finite volume `Λ`, hence `𝓣`-measurable. -/
theorem measurableSet_tail_preimage_add_const (m : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[tailSigmaAlgebra S E] A) :
    MeasurableSet[tailSigmaAlgebra S E] ((fun x : S → E ↦ x + m) ⁻¹' A) := by
  simp only [MeasurableSpace.measurableSet_iInf] at hA ⊢
  intro Λ
  have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ),
      cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] fun x : S → E ↦ x + m := by
    rw [measurable_cylinderEvents_iff]
    intro i hi
    have h1 : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
        fun a : S → E ↦ a i := measurable_cylinderEvent_apply hi
    exact h1.add_const (m i)
  exact hmeas (hA Λ)

omit [Countable S] [LinearOrder S] in
/-- **Tail-triviality is preserved by spin translations.** -/
theorem tailTrivial_map_add_const {ν : Measure (S → E)} [IsProbabilityMeasure ν] (m : S → E)
    (hν : ∀ A, MeasurableSet[tailSigmaAlgebra S E] A → ν A = 0 ∨ ν A = 1) (A : Set (S → E))
    (hA : MeasurableSet[tailSigmaAlgebra S E] A) :
    (ν.map fun x : S → E ↦ x + m) A = 0 ∨ (ν.map fun x : S → E ↦ x + m) A = 1 := by
  have hle : tailSigmaAlgebra S E ≤ MeasurableSpace.pi :=
    iInf_le_of_le ∅ cylinderEvents_le_pi
  rw [Measure.map_apply (measurable_add_const m) (hle _ hA)]
  exact hν _ (measurableSet_tail_preimage_add_const m hA)

end Translation

omit [Countable S] [LinearOrder S] in
/-- Distinct means give distinct translates of the centred Gauss field: the mean of
`μ_C * δ_m` at the site `i` is `m i`. -/
theorem injective_map_add_gaussianField [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ I : Finset S, (ProbabilityTheory.covMatrix C I).PosSemidef) :
    Function.Injective fun m : S → ℝ ↦
      (ProbabilityTheory.gaussianField C hC).map fun x ↦ x + m := by
  have hi : ∀ (v : S → ℝ) (i : S),
      ∫ ω, ω i ∂((ProbabilityTheory.gaussianField C hC).map fun x ↦ x + v) = v i := by
    intro v i
    rw [ProbabilityTheory.integral_eval_map_add_const
      (ProbabilityTheory.isGaussianProcess_gaussianField hC) v i,
      ProbabilityTheory.integral_eval_gaussianField hC i, zero_add]
  intro m m' hmm'
  funext i
  have hcong := congrArg (fun ρ : Measure (S → ℝ) ↦ ∫ ω, ω i ∂ρ) hmm'
  simpa only [hi] using hcong

section Extreme

variable (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset S, (Potential.gaussianCouplingMatrix J Λ).PosDef)

include hSymm hFin hPD

/-- **Georgii Theorem (7.12)(c) and Proposition (13.A5) for `γ^{J,h}`.** An extreme Gibbs measure
of a Gaussian specification is a Gauss field, and its covariance function is the limit of the
finite-volume covariances `𝒥_{Λ_n}⁻¹` along the canonical exhaustion.

Theorem (7.12)(c) applies because `γ^{J,h}` *is* the λ-specification of the normalized
pre-modification `(Φ^{J,h}).boltzmannFactor 1` over Lebesgue measure (the identification is
definitional). -/
theorem isGaussianProcess_and_tendsto_gaussianCovEntry_of_mem_extremePoints_G
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) :
    IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ ∧
      ∀ i j, Tendsto (fun n : ℕ ↦ gaussianCovEntry J (exhaustionVolumes n) i j) atTop
        (𝓝 (cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ])) := by
  have hpot := Potential.isPotential_gaussianPotential J h
  have hfr := Potential.isFiniteRange_gaussianPotential J h hSymm hFin
  have hadm := Potential.isSigmaFiniteLambdaAdmissible_gaussianPotential_boltzmannFactor J h
    hSymm hFin hPD 1 one_pos
  have hp : IsProbabilityMeasure μ := hμ.1.1
  set μP : ProbabilityMeasure (S → ℝ) := ⟨μ, hp⟩ with hμP
  have : IsProbabilityMeasure ((μP : ProbabilityMeasure (S → ℝ)) : Measure (S → ℝ)) := hp
  have hEq : Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos =
      Specification.lambdaSpecification (S := S) (E := ℝ) volume
        ((Potential.gaussianPotential J h).boltzmannFactor 1)
        (Potential.isPremodifier_boltzmannFactor 1) hadm := rfl
  have hμ' : (μP : Measure (S → ℝ)) ∈
      (G (Specification.lambdaSpecification (S := S) (E := ℝ) volume
        ((Potential.gaussianPotential J h).boltzmannFactor 1)
        (Potential.isPremodifier_boltzmannFactor 1) hadm)).extremePoints ℝ≥0∞ := by
    rw [← hEq]; exact hμ
  obtain ⟨ω, hω⟩ := (ae_tendsto_finiteVolumeDistributions_exhaustion_lambdaSpecification
    (Potential.isPremodifier_boltzmannFactor 1) hadm hμ').exists
  rw [← hEq] at hω
  -- the finite-volume Gibbs distributions are Gauss fields
  have hg : ∀ n : ℕ, IsGaussianProcess (fun i (σ : S → ℝ) ↦ σ i)
      (((WithSetwiseTopology.ofMeasure (finiteVolumeDistributions
        (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos) ω
        (exhaustionVolumes n)) : WithLocalConvergence S ℝ)).toMeasure : Measure (S → ℝ)) :=
    fun n ↦ Potential.isGaussianProcess_gaussianSpecification J h hSymm hFin hPD 1 one_pos _ ω
  refine ⟨isGaussianProcess_of_tendsto_withLocalConvergence hω hg, fun i j ↦ ?_⟩
  have hcov := tendsto_covariance_of_tendsto_withLocalConvergence hω hg i j
  refine hcov.congr fun n ↦ ?_
  have hval : cov[fun σ : S → ℝ ↦ σ i, fun σ : S → ℝ ↦ σ j;
      (((WithSetwiseTopology.ofMeasure (finiteVolumeDistributions
        (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos) ω
        (exhaustionVolumes n)) : WithLocalConvergence S ℝ)).toMeasure : Measure (S → ℝ))]
      = cov[fun σ : S → ℝ ↦ σ i, fun σ : S → ℝ ↦ σ j;
        Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos (exhaustionVolumes n) ω] :=
    rfl
  rw [hval, Potential.covariance_eval_gaussianSpecification, gaussianCovEntry]
  split_ifs with hij
  · rw [one_smul]
  · rfl

/-- **Georgii Proposition (13.A5), the field form**: an extreme Gibbs measure of a Gaussian
specification is a Gauss field. -/
theorem isGaussianProcess_of_mem_extremePoints_G
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) :
    IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ :=
  (isGaussianProcess_and_tendsto_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD hμ).1

/-- **Georgii's condition (13.27) is necessary**: if `𝒢(γ^{J,h})` contains an extreme element then
`sup_Λ 𝒥_Λ⁻¹(i,i) < ∞` for every `i`.

The diagonal `Λ ↦ 𝒥_Λ⁻¹(i,i)` is increasing (`monotone_gaussianCovEntry_diag`), so it is bounded
above by the limit of its values along the cofinal exhaustion, which exists by (13.A5) and equals
the variance of `σ_i` under the extreme Gibbs measure. -/
theorem bddAbove_gaussianCovEntry_of_mem_extremePoints_G
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) (i : S) :
    BddAbove (Set.range fun Λ : Finset S ↦ gaussianCovEntry J Λ i i) := by
  obtain ⟨-, hlim⟩ :=
    isGaussianProcess_and_tendsto_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD hμ
  have hmono : Monotone fun n : ℕ ↦ gaussianCovEntry J (exhaustionVolumes (S := S) n) i i :=
    (monotone_gaussianCovEntry_diag hPD i).comp exhaustionVolumes_monotone
  refine ⟨cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω i; μ], ?_⟩
  rintro _ ⟨Λ, rfl⟩
  obtain ⟨n, hn⟩ := exhaustionVolumes_cofinal (S := S) Λ
  exact le_trans (monotone_gaussianCovEntry_diag hPD i hn) (hmono.ge_of_tendsto (hlim i i) n)

/-- **Georgii (13.25)**: if `𝒢(γ^{J,h})` has an extreme element, the limits
`C(i,j) = lim_{Λ ∈ 𝒮} 𝒥_Λ⁻¹(i,j)` exist along the whole net of finite volumes, and they are the
covariance function of that extreme element. -/
theorem tendsto_gaussianCovEntry_of_mem_extremePoints_G
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) (i j : S) :
    Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop
      (𝓝 (cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ])) := by
  obtain ⟨-, hlim⟩ :=
    isGaussianProcess_and_tendsto_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD hμ
  obtain ⟨c, hc⟩ := exists_tendsto_gaussianCovEntry hPD
    (bddAbove_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD hμ) i j
  have hseq := hc.comp (tendsto_exhaustionVolumes_atTop (S := S))
  rwa [tendsto_nhds_unique hseq (hlim i j)] at hc

/-- **Georgii Theorem (13.24), the covariance**: the covariance function of an extreme Gibbs
measure for `γ^{J,h}` is `C(i,j) = lim_{Λ ∈ 𝒮} 𝒥_Λ⁻¹(i,j)` — in particular it does not depend on
the extreme element chosen. -/
theorem covariance_eq_of_mem_extremePoints_G {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) (i j : S) :
    cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ] = C i j :=
  tendsto_nhds_unique (tendsto_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD hμ i j)
    (hC i j)

/-- **Georgii Theorem (13.24), the mean**: the mean of an extreme Gibbs measure for `γ^{J,h}`
lies in `M_{J,h}`. (By Theorem (13.22) this holds for every *Gaussian* Gibbs measure; extremality
enters only through the Gaussianity.) -/
theorem mem_gaussianMeanSet_of_mem_extremePoints_G
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) :
    (fun j ↦ ∫ ω, ω j ∂μ) ∈ Potential.gaussianMeanSet J h :=
  mem_gaussianMeanSet_of_isGibbsMeasure hSymm hFin hPD
    (isGaussianProcess_of_mem_extremePoints_G hSymm hFin hPD hμ) hμ.1.2

/-- **Georgii Theorem (13.24), `μ = μ_C * δ_m`**: an extreme Gibbs measure for `γ^{J,h}` is the
translate, by its own mean `m ∈ M_{J,h}`, of the centred Gauss field `μ_C` with the covariance
function `C` of (13.25). -/
theorem eq_map_add_gaussianField_of_mem_extremePoints_G [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) :
    μ = (ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC)).map
      fun x ↦ x + fun j ↦ ∫ ω, ω j ∂μ := by
  have hp : IsProbabilityMeasure μ := hμ.1.1
  exact ProbabilityTheory.eq_map_add_gaussianField _
    (isGaussianProcess_of_mem_extremePoints_G hSymm hFin hPD hμ)
    (covariance_eq_of_mem_extremePoints_G hSymm hFin hPD hC hμ) fun _ ↦ rfl

/-! ### Georgii Theorem (13.26) in full -/

/-- **Georgii's condition (13.27) is necessary**, in terms of `𝒢(γ^{J,h})` itself. -/
theorem bddAbove_gaussianCovEntry_of_nonempty_G
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) (i : S) :
    BddAbove (Set.range fun Λ : Finset S ↦ gaussianCovEntry J Λ i i) :=
  bddAbove_gaussianCovEntry_of_mem_extremePoints_G hSymm hFin hPD
    (nonempty_extremePoints_G hG).some_mem i

/-- **`M_{J,h} ≠ ∅` is necessary for `𝒢(γ^{J,h}) ≠ ∅`** (Georgii's Theorem (13.24), used in
Theorems (13.26) and (13.36)). -/
theorem nonempty_gaussianMeanSet_of_nonempty_G
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    (Potential.gaussianMeanSet J h).Nonempty :=
  ⟨_, mem_gaussianMeanSet_of_mem_extremePoints_G hSymm hFin hPD
    (nonempty_extremePoints_G hG).some_mem⟩

/-- **Georgii Theorem (13.26)**, both halves: for `J` symmetric of finite range with every `𝒥_Λ`
positive definite, `𝒢(γ^{J,h}) ≠ ∅` **iff** `M_{J,h} ≠ ∅` and `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞` for every
`i ∈ S`.

Sufficiency is `nonempty_G_gaussianSpecification_of_bddAbove`; necessity is Theorem (13.24), i.e.
`bddAbove_gaussianCovEntry_of_nonempty_G` and `nonempty_gaussianMeanSet_of_nonempty_G`. -/
theorem nonempty_G_gaussianSpecification_iff :
    (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty ↔
      (Potential.gaussianMeanSet J h).Nonempty ∧
        ∀ i : S, BddAbove (Set.range fun Λ : Finset S ↦ gaussianCovEntry J Λ i i) :=
  ⟨fun hG ↦ ⟨nonempty_gaussianMeanSet_of_nonempty_G hSymm hFin hPD hG,
      bddAbove_gaussianCovEntry_of_nonempty_G hSymm hFin hPD hG⟩,
    fun ⟨hM, h27⟩ ↦ by
      classical
      exact nonempty_G_gaussianSpecification_of_bddAbove hSymm hFin hPD h27 hM⟩

/-- **The converse inclusion of Georgii Theorem (13.24)**, at the level of `𝒢`: every Gauss field
with covariance function `C` of (13.25) and mean in `M_{J,h}` is a Gibbs measure for `γ^{J,h}`.
This is Theorem (13.22)(b) ⟹ (a), `C` inverting `J` by
`isInverse_of_tendsto_gaussianCovEntry`. -/
theorem isGibbsMeasure_of_isGaussianProcess_covariance_eq {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    {ν : Measure (S → ℝ)} (hν : IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) ν)
    (hνcov : ∀ i j, cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; ν] = C i j)
    (hνm : (fun j ↦ ∫ ω, ω j ∂ν) ∈ Potential.gaussianMeanSet J h) :
    (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos).IsGibbsMeasure ν := by
  classical
  refine georgii_13_22_of_finiteRowSupport hFin hν (fun i k ↦ ?_) hSymm hPD hνm
  have hinv := isInverse_of_tendsto_gaussianCovEntry hFin hPD hC i k
  simp only [hνcov]
  convert hinv using 2


/-- **Georgii Remark (7.2) for the spin translations of a Gaussian specification.** If `μ` is an
extreme Gibbs measure for `γ^{J,h'}` and `m ∈ M_{J,h}`, then `τ^m(μ)` is an extreme Gibbs measure
for `γ^{J,h+h'}`.

Both halves are already available: `τ^m(μ) ∈ 𝒢(γ^{J,h+h'})` is Remark (13.23)(b)
(`Potential.gaussianSpecification_map_spinTranslation`), and extremality is tail-triviality
(Georgii (7.7), `mem_extremePoints_G_iff_isTailTrivial`), which is preserved because `τ^m`
preserves the tail σ-algebra. -/
theorem map_add_mem_extremePoints_G {h' m : S → ℝ} (hm : m ∈ Potential.gaussianMeanSet J h)
    (hμ : μ ∈ (G (Potential.gaussianSpecification J h' hSymm hFin hPD 1 one_pos)).extremePoints
      ℝ≥0∞) :
    μ.map (fun x ↦ x + m) ∈
      (G (Potential.gaussianSpecification J (h + h') hSymm hFin hPD 1 one_pos)).extremePoints
        ℝ≥0∞ := by
  have hp : IsProbabilityMeasure μ := hμ.1.1
  have hmapG : μ.map (fun x ↦ x + m) ∈
      G (Potential.gaussianSpecification J (h + h') hSymm hFin hPD 1 one_pos) := by
    have hinv := Potential.gaussianSpecification_map_spinTranslation J hSymm hFin hPD 1 one_pos
      hm h'
    have := Specification.map_mem_G_map (spinTranslation m) hμ.1
    rwa [hinv, funext (spinTranslation_toFun m)] at this
  refine mem_extremePoints_G_of_isTailTrivial hmapG ?_
  intro A hA
  simpa using tailTrivial_map_add_const m (tailTrivial_of_mem_extremePoints_G hμ) A hA

/-- **Georgii Theorem (13.24), the centred Gauss field is extreme.** If `𝒢(γ^{J,h}) ≠ ∅` then the
centred Gauss field `μ_C` with the covariance function `C` of (13.25) is an *extreme* Gibbs
measure for `γ^{J,0}`.

Georgii: an extreme `μ ∈ 𝒢(γ^{J,h})` is `τ^m(μ_C)` for `m ∈ M_{J,h}`, so `μ_C = τ^{-m}(μ)` is
extreme by Remarks (13.23)(b) and (7.2). -/
theorem mem_extremePoints_G_gaussianField [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) ∈
      (G (Potential.gaussianSpecification J (0 : S → ℝ) hSymm hFin hPD 1
        one_pos)).extremePoints ℝ≥0∞ := by
  obtain ⟨μ, hμ⟩ := nonempty_extremePoints_G hG
  set m : S → ℝ := fun j ↦ ∫ ω, ω j ∂μ with hm_def
  have hμeq := eq_map_add_gaussianField_of_mem_extremePoints_G hSymm hFin hPD hC hμ
  have hm : m ∈ Potential.gaussianMeanSet J h :=
    mem_gaussianMeanSet_of_mem_extremePoints_G hSymm hFin hPD hμ
  have hneg : -m ∈ Potential.gaussianMeanSet J (-h) := Potential.neg_mem_gaussianMeanSet J hm
  have hshift := map_add_mem_extremePoints_G hSymm hFin hPD (h := -h) (h' := h) hneg hμ
  rw [neg_add_cancel] at hshift
  have hcomp : μ.map (fun x ↦ x + -m)
      = ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) := by
    rw [hμeq, Measure.map_map (measurable_add_const _) (measurable_add_const _)]
    rw [show ((fun x : S → ℝ ↦ x + -m) ∘ fun x : S → ℝ ↦ x + m) = id from by funext x; simp,
      Measure.map_id]
  rwa [hcomp] at hshift

/-- **Georgii Theorem (13.24)**: `ex 𝒢(γ^{J,h}) = {μ_C * δ_m : m ∈ M_{J,h}}`.

`⊆` is `eq_map_add_gaussianField_of_mem_extremePoints_G` together with
`mem_gaussianMeanSet_of_mem_extremePoints_G`; `⊇` is `mem_extremePoints_G_gaussianField`
followed by Remark (7.2) for spin translations, `map_add_mem_extremePoints_G`. -/
theorem extremePoints_G_eq_image_gaussianField [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints ℝ≥0∞
      = (fun m : S → ℝ ↦ (ProbabilityTheory.gaussianField C
          (posSemidef_covMatrix_of_tendsto hPD hC)).map fun x ↦ x + m) ''
        Potential.gaussianMeanSet J h := by
  refine Set.Subset.antisymm (fun ν hν ↦ ?_) ?_
  · exact ⟨fun j ↦ ∫ ω, ω j ∂ν, mem_gaussianMeanSet_of_mem_extremePoints_G hSymm hFin hPD hν,
      (eq_map_add_gaussianField_of_mem_extremePoints_G hSymm hFin hPD hC hν).symm⟩
  · rintro _ ⟨m, hm, rfl⟩
    have := map_add_mem_extremePoints_G hSymm hFin hPD (h := h) (h' := (0 : S → ℝ)) hm
      (mem_extremePoints_G_gaussianField hSymm hFin hPD hC hG)
    rwa [add_zero] at this

/-- **Georgii Theorem (13.24)**: if `𝒢(γ^{J,h}) ≠ ∅` then `ex 𝒢(γ^{J,h})` is in bijection with
`M_{J,h}`, the bijection being `m ↦ μ_C * δ_m`. -/
theorem bijOn_map_add_gaussianField_extremePoints_G [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)))
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    Set.BijOn (fun m : S → ℝ ↦ (ProbabilityTheory.gaussianField C
        (posSemidef_covMatrix_of_tendsto hPD hC)).map fun x ↦ x + m)
      (Potential.gaussianMeanSet J h)
      ((G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).extremePoints ℝ≥0∞) := by
  rw [extremePoints_G_eq_image_gaussianField hSymm hFin hPD hC hG]
  exact (Function.Injective.injOn
    (injective_map_add_gaussianField (posSemidef_covMatrix_of_tendsto hPD hC))).bijOn_image

/-- **Georgii Remark (13.23)(d)**: if `M_{J,0}` contains a non-zero element then either
`𝒢(γ^{J,h}) = ∅` or `ex 𝒢(γ^{J,h})` is uncountable.

Georgii derives this from the continuous symmetry `(τ^{t m})_{t ∈ ℝ}` of `γ^{J,h}` together with
Theorem (7.26) and Remark (7.2); here it is read off Theorem (13.24), which puts `ex 𝒢(γ^{J,h})`
in bijection with the uncountable coset `M_{J,h} = m₀ + M_{J,0}`. -/
theorem not_countable_extremePoints_G {m : S → ℝ}
    (hm : m ∈ Potential.gaussianMeanSet J 0) (hm0 : m ≠ 0)
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    ¬ ((G (Potential.gaussianSpecification J h hSymm hFin hPD 1
      one_pos)).extremePoints ℝ≥0∞).Countable := by
  classical
  obtain ⟨m₀, hm₀⟩ := nonempty_gaussianMeanSet_of_nonempty_G hSymm hFin hPD hG
  obtain ⟨C, hC⟩ : ∃ C : S → S → ℝ, ∀ i j,
      Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) atTop (𝓝 (C i j)) := by
    choose C hC using exists_tendsto_gaussianCovEntry hPD
      (bddAbove_gaussianCovEntry_of_nonempty_G hSymm hFin hPD hG)
    exact ⟨C, hC⟩
  intro hcount
  refine Potential.not_countable_gaussianMeanSet J hm₀ hm hm0 ?_
  have hbij := bijOn_map_add_gaussianField_extremePoints_G hSymm hFin hPD hC hG
  exact (hcount.preimage (injective_map_add_gaussianField
    (posSemidef_covMatrix_of_tendsto hPD hC))).mono fun x hx ↦ hbij.mapsTo hx

end Extreme

end MeasureTheory.GibbsMeasure

end

end

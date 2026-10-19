/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianExtreme
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Georgii Theorem (13.24), final statement: `𝒢(γ^{J,h}) = {μ_C * ν : ν(M_{J,h}) = 1}`

Georgii closes Theorem (13.24) with the description of the whole Gibbs simplex: a random field
`μ` belongs to `𝒢(γ^{J,h})` if and only if it is a *random translation* of the centred Gauss
field `μ_C` with the covariance function `C` of (13.25),

  `μ = ∫ ν(dm) τ^m(μ_C) = μ_C * ν`,

for a probability measure `ν` on `Ω` carried by `M_{J,h}`. Here `*` is Mathlib's
`MeasureTheory.Measure.conv`, the image of `μ_C ⊗ ν` under `(ζ, η) ↦ ζ + η`, which is exactly
Georgii's `μ_1 * μ_2(f) = ∫ μ_1(dζ) ∫ μ_2(dη) f(ζ + η)`.

## The two halves

`⊇` is a general fact about specifications, not about Gaussians: a mixture of translates of a
Gibbs measure is a Gibbs measure. Writing `A` for a measurable set and using Tonelli in the form
that integrates `ν` last,

  `(μ * ν).bind(γ_Λ)(A) = ∫ ν(dm) ∫ μ(dx) γ_Λ(A | x + m) = ∫ ν(dm) τ^m(μ).bind(γ_Λ)(A)
                        = ∫ ν(dm) τ^m(μ)(A) = (μ * ν)(A).`

`⊆` is Georgii's: Theorem (7.26) writes `μ = ∫ w(dρ) ρ` with `w` carried by `ex 𝒢(γ^{J,h})`, and
Theorem (13.24) identifies `ex 𝒢(γ^{J,h})` with `{τ^m(μ_C) : m ∈ M_{J,h}}`, the correspondence
being `ρ ↦ mean ρ`. The transport of `w` to `ν` is `ν = mean_*(w)`, and the measurability of
`ρ ↦ mean ρ` — the step the earlier files recorded as missing — is
`MeasureTheory.GibbsMeasure.measurable_meanOf` below: the mean is written as a difference of two
`lintegral`s of the positive and negative parts of the coordinate, and
`Measure.measurable_lintegral` makes each of them measurable in the measure.

## Main results

* `MeasureTheory.GibbsMeasure.isGibbsMeasure_conv`: **a mixture of translates of a Gibbs measure
  is a Gibbs measure** (any specification on an additive group of spins).
* `MeasureTheory.GibbsMeasure.meanOf` and `MeasureTheory.GibbsMeasure.measurable_meanOf`: the
  mean of a measure on `S → ℝ`, as a measurable function of the measure.
* `Potential.measurableSet_gaussianMeanSet`: `M_{J,h}` is measurable when `J` has finite row
  support. *Intended home:* `GibbsMeasure/Model/GaussianSpecification.lean`, next to
  `Potential.gaussianMeanSet`.
* `MeasureTheory.GibbsMeasure.G_eq_conv_gaussianField`: **Georgii Theorem (13.24), final
  statement.**
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### A mixture of translates of a Gibbs measure is a Gibbs measure -/

section Mixture

variable {S E : Type*} [MeasurableSpace E] [AddCommMonoid E] [MeasurableAdd₂ E]

/-- **A mixture of translates of a Gibbs measure is a Gibbs measure.** If `τ^m(μ) ∈ 𝒢(γ)` for
`ν`-almost every `m`, then the convolution `μ * ν = ∫ ν(dm) τ^m(μ)` lies in `𝒢(γ)`.

Nothing Gaussian is involved: this is Tonelli plus the DLR equation for each translate. -/
theorem isGibbsMeasure_conv (γ : Specification S E) {μ ν : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmem : ∀ᵐ m ∂ν, γ.IsGibbsMeasure (μ.map fun x ↦ x + m)) :
    γ.IsGibbsMeasure (μ ∗ ν) := by
  have hadd : Measurable fun p : (S → E) × (S → E) ↦ p.1 + p.2 := measurable_add
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  ext A hA
  have hγA : Measurable fun ω : S → E ↦ γ Λ ω A :=
    (Kernel.measurable_coe (γ Λ) hA).mono cylinderEvents_le_pi le_rfl
  have hAprod : MeasurableSet ((fun p : (S → E) × (S → E) ↦ p.1 + p.2) ⁻¹' A) := hadd hA
  -- The right-hand side, `ν` integrated last.
  have hrhs : (μ ∗ ν) A = ∫⁻ m, (μ.map fun x ↦ x + m) A ∂ν := by
    rw [Measure.conv, Measure.map_apply hadd hA, Measure.prod_apply_symm hAprod]
    refine lintegral_congr fun m ↦ ?_
    rw [Measure.map_apply (measurable_add_const m) hA]
    rfl
  -- The left-hand side, by Tonelli.
  have hlhs : (μ ∗ ν).bind (γ Λ) A = ∫⁻ m, ((μ.map fun x ↦ x + m).bind (γ Λ)) A ∂ν := by
    rw [Measure.bind_apply hA (γ.measurable_kernel_toMeasure Λ).aemeasurable, Measure.conv,
      lintegral_map hγA hadd,
      lintegral_prod_symm' (fun p : (S → E) × (S → E) ↦ γ Λ (p.1 + p.2) A) (hγA.comp hadd)]
    refine lintegral_congr fun m ↦ ?_
    rw [Measure.bind_apply hA (γ.measurable_kernel_toMeasure Λ).aemeasurable,
      lintegral_map hγA (measurable_add_const m)]
  rw [hlhs, hrhs]
  refine lintegral_congr_ae ?_
  filter_upwards [hmem] with m hm
  have : IsProbabilityMeasure (μ.map fun x ↦ x + m) :=
    Measure.isProbabilityMeasure_map (measurable_add_const m).aemeasurable
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hm Λ]

/-- The version of `MeasureTheory.GibbsMeasure.isGibbsMeasure_conv` with Georgii's hypothesis
`ν(T) = 1` on a measurable carrier `T`. -/
theorem isGibbsMeasure_conv_of_measure_eq_one (γ : Specification S E) {μ ν : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {T : Set (S → E)} (hT : MeasurableSet T)
    (hνT : ν T = 1) (hmem : ∀ m ∈ T, γ.IsGibbsMeasure (μ.map fun x ↦ x + m)) :
    γ.IsGibbsMeasure (μ ∗ ν) := by
  refine isGibbsMeasure_conv γ ?_
  have hcompl : ν Tᶜ = 0 := by
    rw [measure_compl hT (measure_ne_top ν T), hνT, measure_univ, tsub_self]
  filter_upwards [(ae_iff.2 hcompl : ∀ᵐ m ∂ν, m ∈ T)] with m hm using hmem m hm

/-- The measure of a set under a translate is a measurable function of the translation. -/
theorem measurable_map_add_apply {μ : Measure (S → E)} [SFinite μ] {A : Set (S → E)}
    (hA : MeasurableSet A) : Measurable fun m : S → E ↦ (μ.map fun x ↦ x + m) A := by
  have hind : Measurable fun p : (S → E) × (S → E) ↦
      A.indicator (1 : (S → E) → ℝ≥0∞) (p.2 + p.1) :=
    (measurable_one.indicator hA).comp (measurable_snd.add measurable_fst)
  have heq : ∀ m : S → E, (μ.map fun x ↦ x + m) A
      = ∫⁻ x, A.indicator (1 : (S → E) → ℝ≥0∞) (x + m) ∂μ := by
    intro m
    have hfun : (fun x : S → E ↦ A.indicator (1 : (S → E) → ℝ≥0∞) (x + m))
        = ((fun x ↦ x + m) ⁻¹' A).indicator 1 := by
      funext x
      rfl
    rw [Measure.map_apply (measurable_add_const m) hA, hfun,
      lintegral_indicator_one (measurable_add_const m hA)]
  simp_rw [heq]
  exact hind.lintegral_prod_right'

end Mixture

/-! ### The mean of a measure, as a measurable function of the measure -/

section MeanOf

variable {S : Type*}

/-- **The mean of a measure on `S → ℝ`**, written as the difference of the integrals of the
positive and negative parts of the coordinate so that it is defined — and measurable — for every
measure, and agrees with `i ↦ ∫ ω_i dρ` whenever the coordinates are integrable. -/
def meanOf (ρ : Measure (S → ℝ)) (i : S) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (ω i) ∂ρ).toReal - (∫⁻ ω, ENNReal.ofReal (-ω i) ∂ρ).toReal

/-- `meanOf` is a measurable function of the measure. -/
theorem measurable_meanOf : Measurable (meanOf (S := S)) := by
  refine Measurable.of_eval fun i ↦ ?_
  refine Measurable.sub ?_ ?_
  · exact (Measure.measurable_lintegral
      ((measurable_pi_apply i).ennreal_ofReal)).ennreal_toReal
  · exact (Measure.measurable_lintegral
      ((measurable_pi_apply i).neg.ennreal_ofReal)).ennreal_toReal

/-- On a measure for which the coordinates are integrable, `meanOf` is the vector of means. -/
theorem meanOf_eq_integral {ρ : Measure (S → ℝ)}
    (hint : ∀ i, Integrable (fun ω : S → ℝ ↦ ω i) ρ) (i : S) :
    meanOf ρ i = ∫ ω, ω i ∂ρ :=
  (integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint i)).symm

end MeanOf

end MeasureTheory.GibbsMeasure

/-! ### `M_{J,h}` is a measurable set -/

namespace Potential

variable {S : Type*} [Countable S] {J : S → S → ℝ} {h : S → ℝ}

/-- **`M_{J,h}` is a measurable subset of `Ω`** when `J` has finite row support: each row sum
`∑_j J(i,j) m_j` is then a finite sum, hence a measurable function of `m`, and `M_{J,h}` is the
countable intersection of the level sets `{m : h_i + ∑_j J(i,j) m_j = 0}`.

*Intended home:* `GibbsMeasure/Model/GaussianSpecification.lean`, next to
`Potential.gaussianMeanSet`. -/
theorem measurableSet_gaussianMeanSet (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) :
    MeasurableSet (gaussianMeanSet J h) := by
  classical
  have hrow : ∀ i : S, Measurable fun m : S → ℝ ↦ ∑' j, J i j * m j := by
    intro i
    have heq : (fun m : S → ℝ ↦ ∑' j, J i j * m j)
        = fun m : S → ℝ ↦ ∑ j ∈ (hFin i).toFinset, J i j * m j := by
      funext m
      refine tsum_eq_sum fun j hj ↦ ?_
      have : J i j = 0 := by
        by_contra hcon
        exact hj ((hFin i).mem_toFinset.2 hcon)
      simp [this]
    rw [heq]
    exact Finset.measurable_sum _ fun j _ ↦ (measurable_pi_apply j).const_mul _
  have hset : gaussianMeanSet J h = ⋂ i : S, {m : S → ℝ | h i + ∑' j, J i j * m j = 0} := by
    ext m
    rw [mem_gaussianMeanSet_iff]
    refine ⟨fun hm ↦ Set.mem_iInter.2 fun i ↦ hm.2 i, fun hm ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩⟩
    · have := (gaussianConvergenceSet_eq_univ_of_finiteRowSupport J hFin) ▸
        (Set.mem_univ m : m ∈ (Set.univ : Set (S → ℝ)))
      exact this i
    · exact Set.mem_iInter.1 hm i
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact measurableSet_eq_fun ((hrow i).const_add (h i)) measurable_const

end Potential

/-! ### Georgii Theorem (13.24), final statement -/

namespace MeasureTheory.GibbsMeasure

section Georgii1324

variable {S : Type*} [Countable S] [LinearOrder S] {J : S → S → ℝ} {h : S → ℝ}
  (hSymm : ∀ i j, J i j = J j i) (hFin : ∀ i, {j | J i j ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset S, (Potential.gaussianCouplingMatrix J Λ).PosDef)

include hSymm hFin hPD

/-- **Georgii Theorem (13.24), final statement.** If `𝒢(γ^{J,h}) ≠ ∅` then

  `𝒢(γ^{J,h}) = {μ_C * ν : ν ∈ 𝒫(Ω, 𝓕), ν(M_{J,h}) = 1}`,

`μ_C` being the centred Gauss field with the covariance function `C` of (13.25). -/
theorem G_eq_conv_gaussianField [DecidableEq S] {C : S → S → ℝ}
    (hC : ∀ i j, Filter.Tendsto (fun Λ : Finset S ↦ gaussianCovEntry J Λ i j) Filter.atTop
      (nhds (C i j)))
    (hG : (G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)).Nonempty) :
    G (Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos)
      = {μ | ∃ ν : Measure (S → ℝ), IsProbabilityMeasure ν ∧
          ν (Potential.gaussianMeanSet J h) = 1 ∧
          μ = ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) ∗ ν} := by
  classical
  set μC := ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) with hμC
  set γ := Potential.gaussianSpecification J h hSymm hFin hPD 1 one_pos with hγ
  have hM : MeasurableSet (Potential.gaussianMeanSet J h) :=
    Potential.measurableSet_gaussianMeanSet hFin
  have hext := extremePoints_G_eq_image_gaussianField hSymm hFin hPD hC hG
  -- every translate of `μ_C` by an element of `M_{J,h}` is a Gibbs measure
  have htrans : ∀ m ∈ Potential.gaussianMeanSet J h, γ.IsGibbsMeasure (μC.map fun x ↦ x + m) := by
    intro m hm
    have : (μC.map fun x ↦ x + m) ∈ (G γ).extremePoints ℝ≥0∞ := by
      rw [hext]
      exact ⟨m, hm, rfl⟩
    exact this.1.2
  refine Set.Subset.antisymm (fun μ hμ ↦ ?_) ?_
  · -- Georgii's direction: the extreme decomposition, transported by the mean map.
    have hprob : IsProbabilityMeasure μ := hμ.1
    set w := weightOf hG μ with hw
    have hwprob : IsProbabilityMeasure w := isProbabilityMeasure_weightOf hG μ
    have hwex : w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0 := weightOf_extremePoints_compl hG hμ
    have hjoin : Measure.join w = μ := join_weightOf hG hμ
    -- the mean of an extreme Gibbs measure
    have hmean : ∀ ρ ∈ (G γ).extremePoints ℝ≥0∞, meanOf ρ = fun j ↦ ∫ ω, ω j ∂ρ := by
      intro ρ hρ
      have hp : IsProbabilityMeasure ρ := hρ.1.1
      have hgp := isGaussianProcess_of_mem_extremePoints_G hSymm hFin hPD hρ
      funext i
      exact meanOf_eq_integral
        (fun i ↦ ((hgp.hasGaussianLaw_eval i).memLp_two.integrable (by norm_num))) i
    refine ⟨w.map meanOf, Measure.isProbabilityMeasure_map measurable_meanOf.aemeasurable, ?_, ?_⟩
    · -- `ν(M_{J,h}) = 1`
      rw [Measure.map_apply measurable_meanOf hM]
      refine (prob_compl_eq_zero_iff (measurable_meanOf hM)).1 (measure_mono_null ?_ hwex)
      intro ρ hρ hcon
      refine hρ ?_
      rw [Set.mem_preimage, hmean ρ hcon]
      exact mem_gaussianMeanSet_of_mem_extremePoints_G hSymm hFin hPD hcon
    · -- `μ = μ_C * ν`
      ext A hA
      rw [← hjoin, Measure.join_apply hA, Measure.conv, Measure.map_apply measurable_add hA,
        Measure.prod_apply_symm (measurable_add hA)]
      have hpt : ∀ y : S → ℝ,
          μC ((fun x ↦ (x, y)) ⁻¹' ((fun p : (S → ℝ) × (S → ℝ) ↦ p.1 + p.2) ⁻¹' A))
            = (μC.map fun x ↦ x + y) A := by
        intro y
        rw [Measure.map_apply (measurable_add_const y) hA]
        rfl
      simp_rw [hpt]
      rw [lintegral_map (measurable_map_add_apply (μ := μC) hA) measurable_meanOf]
      refine lintegral_congr_ae ?_
      filter_upwards [(ae_iff.2 hwex : ∀ᵐ ρ ∂w, ρ ∈ (G γ).extremePoints ℝ≥0∞)] with ρ hρ
      have hρeq : ρ = μC.map (fun x ↦ x + fun j ↦ ∫ ω, ω j ∂ρ) := by
        rw [hμC]
        exact eq_map_add_gaussianField_of_mem_extremePoints_G hSymm hFin hPD hC hρ
      rw [hmean ρ hρ]
      conv_lhs => rw [hρeq]
  · rintro μ ⟨ν, hνprob, hνM, rfl⟩
    exact ⟨inferInstance, isGibbsMeasure_conv_of_measure_eq_one γ hM hνM htrans⟩

end Georgii1324

end MeasureTheory.GibbsMeasure

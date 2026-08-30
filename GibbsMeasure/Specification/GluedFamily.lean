/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Structure

/-!
# Georgii, Remark (2.26): gluing a measurable family of specifications along a tail function

Let `(X, 𝓧)` be a measurable space, `ξ : Ω → X` a *tail measurable* function and `(γˣ)ₓ` a family
of specifications whose kernels depend measurably on the parameter. Georgii's Remark (2.26) says
that

`γ_Λ(A | ω) = γ^{ξ ω}_Λ(A | ω)`

is again a specification, and that every `μ` which is Gibbs for `γˣ` and satisfies `μ(ξ = x) = 1`
is Gibbs for `γ`.

Properness and the Markov property are pointwise. Consistency is the whole content: `ξ` is
tail measurable, hence `𝓕_{Λᶜ}`-measurable for every finite `Λ`, so properness of `γ^{ξ ω}_Λ`
forces `γ^{ξ ω}_Λ(· | ω)` to be carried by `{σ : ξ σ = ξ ω}` (`Specification.ae_eq_of_tail`). On
that set the inner kernel `γ^{ξ σ}_{Λ₁}` is the *fixed* kernel `γ^{ξ ω}_{Λ₁}`, and consistency of
`γ^{ξ ω}` applies.

The hypothesis `[MeasurableSingletonClass X]` is not a strengthening of Georgii's: his condition
(2.26)(i) is stated in terms of the events `{ξ = x}`, which presupposes that singletons of `X` are
measurable.

## Main declarations

* `Specification.IsMeasurableFamily`: Georgii (2.26)(ii), joint measurability of the family.
* `Specification.glued`: the specification of Georgii (2.26).
* `Specification.isGibbsMeasure_glued`: Georgii (2.26), `μ(ξ = x) = 1` and `μ ∈ 𝒢(γˣ)` imply
  `μ ∈ 𝒢(γ)`.
-/

@[expose] public section

-- Lean 4.34's module system does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`)
-- during `isDefEq`. Several proofs below rely on that unfolding.
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

namespace Specification

variable {S E X : Type*} [MeasurableSpace E] [MeasurableSpace X]

/-- Georgii (2.26)(ii): the kernels of a family `(γˣ)ₓ` of specifications depend measurably on the
parameter `x`, jointly with the boundary condition `ω`. -/
def IsMeasurableFamily (γ : X → Specification S E) : Prop :=
  ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄, MeasurableSet A →
    @Measurable (X × (S → E)) ℝ≥0∞
      (@Prod.instMeasurableSpace X (S → E) _ (cylinderEvents ((Λ : Set S)ᶜ))) _
      fun p ↦ γ p.1 Λ p.2 A

variable {γ : X → Specification S E} {ξ : (S → E) → X}

/-- A tail measurable function is measurable for every boundary σ-algebra. -/
lemma measurable_cylinderEvents_compl_of_tail (hξ : Measurable[tailSigmaAlgebra S E] ξ)
    (Λ : Finset S) : Measurable[cylinderEvents ((Λ : Set S)ᶜ)] ξ :=
  hξ.mono (iInf_le _ Λ) le_rfl

/-- The kernels of the glued family are measurable. -/
lemma measurable_gluedFun (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) (Λ : Finset S) :
    Measurable[cylinderEvents ((Λ : Set S)ᶜ)] fun ω ↦ γ (ξ ω) Λ ω := by
  refine @Measure.measurable_of_measurable_coe (S → E) (S → E) _
    (cylinderEvents ((Λ : Set S)ᶜ)) _ fun A hA ↦ ?_
  have hpair : @Measurable (S → E) (X × (S → E)) (cylinderEvents ((Λ : Set S)ᶜ))
      (@Prod.instMeasurableSpace X (S → E) _ (cylinderEvents ((Λ : Set S)ᶜ)))
      fun ω ↦ (ξ ω, ω) :=
    Measurable.prodMk (measurable_cylinderEvents_compl_of_tail hξ Λ) measurable_id
  exact (hγ Λ hA).comp hpair

variable (γ ξ) in
/-- Georgii (2.26): the glued family of kernels `γ_Λ(· | ω) = γ^{ξ ω}_Λ(· | ω)`. -/
noncomputable def gluedFun (hγ : IsMeasurableFamily γ) (hξ : Measurable[tailSigmaAlgebra S E] ξ)
    (Λ : Finset S) : Kernel[cylinderEvents ((Λ : Set S)ᶜ)] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _ (fun ω ↦ γ (ξ ω) Λ ω) (measurable_gluedFun hγ hξ Λ)

@[simp] lemma gluedFun_apply (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) (Λ : Finset S) (ω : S → E) :
    gluedFun γ ξ hγ hξ Λ ω = γ (ξ ω) Λ ω := rfl

lemma isMarkovKernel_gluedFun (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) (Λ : Finset S) :
    IsMarkovKernel (gluedFun γ ξ hγ hξ Λ) :=
  ⟨fun ω ↦ by rw [gluedFun_apply]; infer_instance⟩

lemma isProper_gluedFun (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) (Λ : Finset S) :
    (gluedFun γ ξ hγ hξ Λ).IsProper := by
  constructor
  intro B hB ω
  have h := ((γ (ξ ω)).isProper Λ).restrict_eq_indicator_smul' hB ω
  rw [Kernel.restrict_apply] at h ⊢
  rw [gluedFun_apply]
  exact h

variable [MeasurableSingletonClass X]

/-- The heart of Georgii (2.26): since `ξ` is tail measurable, it is constant on the fibres that
`γ^x_Λ(· | ω)` charges. -/
lemma ae_eq_of_tail (hξ : Measurable[tailSigmaAlgebra S E] ξ) (x : X) (Λ : Finset S) (ω : S → E) :
    ∀ᵐ σ ∂(γ x Λ ω), ξ σ = ξ ω := by
  set B : Set (S → E) := ξ ⁻¹' {ξ ω} with hBdef
  have hB : MeasurableSet[cylinderEvents ((Λ : Set S)ᶜ)] B :=
    measurable_cylinderEvents_compl_of_tail hξ Λ (measurableSet_singleton _)
  have hprop := ((γ x).isProper Λ).inter_eq_indicator_mul cylinderEvents_le_pi
    MeasurableSet.univ hB ω
  have hωB : ω ∈ B := by simp [hBdef]
  have hmass : γ x Λ ω B = 1 := by
    have h1 : γ x Λ ω (Set.univ ∩ B) = B.indicator 1 ω * γ x Λ ω Set.univ := hprop
    rwa [Set.univ_inter, Set.indicator_of_mem hωB, Pi.one_apply, one_mul, measure_univ] at h1
  have hBmeas : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hzero : γ x Λ ω Bᶜ = 0 := by
    have := measure_compl (μ := γ x Λ ω) hBmeas (by simp [hmass])
    simpa [hmass] using this
  rw [MeasureTheory.ae_iff]
  have hcompl : {a : S → E | ¬ ξ a = ξ ω} = Bᶜ := by ext a; simp [hBdef]
  rw [hcompl]
  exact hzero

/-- Georgii (2.26): the glued family is consistent. -/
lemma isConsistent_gluedFun (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) : IsConsistent (gluedFun γ ξ hγ hξ) := by
  intro Λ₁ Λ₂ hΛ
  ext ω A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  have h1 : ∀ σ : S → E,
      ((gluedFun γ ξ hγ hξ Λ₁).comap id cylinderEvents_le_pi) σ A = γ (ξ σ) Λ₁ σ A := fun _ ↦ rfl
  simp only [h1, gluedFun_apply]
  have hae : ∀ᵐ σ ∂(γ (ξ ω) Λ₂ ω), γ (ξ σ) Λ₁ σ A = γ (ξ ω) Λ₁ σ A := by
    filter_upwards [ae_eq_of_tail hξ (ξ ω) Λ₂ ω] with σ hσ
    rw [hσ]
  rw [lintegral_congr_ae hae]
  have hbind := congrArg (fun μ : Measure (S → E) ↦ μ A)
    (Specification.bind (γ := γ (ξ ω)) hΛ ω)
  simpa [Measure.bind_apply hA
    (((γ (ξ ω) Λ₁).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)] using hbind

variable (γ ξ) in
/-- The raw glued family, before bundling the Markov and properness hypotheses. -/
noncomputable def gluedPre (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) : PreSpecification S E where
  toFun := gluedFun γ ξ hγ hξ
  isConsistent' := isConsistent_gluedFun hγ hξ

variable (γ ξ) in
/-- **Georgii, Remark (2.26).** Gluing a measurable family `(γˣ)ₓ` of specifications along a tail
measurable function `ξ` produces a specification. -/
noncomputable def glued (hγ : IsMeasurableFamily γ) (hξ : Measurable[tailSigmaAlgebra S E] ξ) :
    Specification S E where
  toPreSpecification := gluedPre γ ξ hγ hξ
  isMarkovKernel' := isMarkovKernel_gluedFun hγ hξ
  isProper' := isProper_gluedFun hγ hξ

@[simp] lemma glued_apply (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) (Λ : Finset S) (ω : S → E) :
    glued γ ξ hγ hξ Λ ω = γ (ξ ω) Λ ω := rfl

/-- **Georgii, Remark (2.26).** If `μ` is concentrated on `{ξ = x}` and is a Gibbs measure for
`γˣ`, then it is a Gibbs measure for the glued specification. -/
theorem isGibbsMeasure_glued (hγ : IsMeasurableFamily γ)
    (hξ : Measurable[tailSigmaAlgebra S E] ξ) {x : X} {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμξ : μ {ω | ξ ω = x} = 1)
    (hμ : (γ x).IsGibbsMeasure μ) : (glued γ ξ hγ hξ).IsGibbsMeasure μ := by
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob] at hμ ⊢
  intro Λ
  have hae : ∀ᵐ ω ∂μ, ξ ω = x := by
    rw [MeasureTheory.ae_iff]
    have hmeas : MeasurableSet {ω : S → E | ξ ω = x} :=
      cylinderEvents_le_pi _
        (measurable_cylinderEvents_compl_of_tail hξ ∅ (measurableSet_singleton x))
    have := measure_compl (μ := μ) hmeas (by simp [hμξ])
    simpa [hμξ, Set.compl_ofPred] using this
  ext A hA
  rw [Measure.bind_apply hA
    (((glued γ ξ hγ hξ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)]
  have hae' : ∀ᵐ ω ∂μ, glued γ ξ hγ hξ Λ ω A = γ x Λ ω A := by
    filter_upwards [hae] with ω hω
    rw [glued_apply, hω]
  rw [lintegral_congr_ae hae']
  have h := congrArg (fun ν : Measure (S → E) ↦ ν A) (hμ Λ)
  simpa [Measure.bind_apply hA
    (((γ x Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)] using h

end Specification

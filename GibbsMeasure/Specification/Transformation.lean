/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Prereqs.Transformation
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import GibbsMeasure.Mathlib.Probability.Kernel.Composition.MapComap
public import GibbsMeasure.Mathlib.Data.Finset.Map

/-!
# Transformations of specifications

Georgii §5.1–5.2: the image `τ(γ)` of a specification under a transformation ((5.4), (5.5)),
`τ`-invariant specifications ((5.7)(b)), the transport of Gibbs measures ((5.10), (5.11)) and
the invariance of the independent specification under `λ`-preserving transformations ((5.6)(a)).
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

-- Lean 4.34's module system does not unfold non-exposed Mathlib defs (e.g. `Kernel.comap`) during
-- `isDefEq`; the consistency proof relies on that unfolding, as in `Specification.lean`.
set_option backward.isDefEq.respectTransparency false in
/-- **Georgii (5.4).** The image `τ(γ)` of a specification under a transformation:
`τ(γ)_Λ(A | ω) = γ_{τ_*⁻¹ Λ}(τ⁻¹ A | τ⁻¹ ω)`. -/
def map (τ : Transformation S E) (γ : Specification S E) : Specification S E where
  toFun Λ := ((γ (Λ.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
    (τ.measurable_inv_toFun_cylinderEvents_compl Λ)).map τ.toFun
  isConsistent' := by
    intro Λ₁ Λ₂ h
    refine Kernel.ext fun ω ↦ ?_
    rw [Kernel.comp_apply]
    show ⇑((((γ (Λ₁.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
        (τ.measurable_inv_toFun_cylinderEvents_compl Λ₁)).map τ.toFun).comap id
        cylinderEvents_le_pi) ∘ₘ
      ((((γ (Λ₂.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
        (τ.measurable_inv_toFun_cylinderEvents_compl Λ₂)).map τ.toFun) ω) =
      (((γ (Λ₂.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
        (τ.measurable_inv_toFun_cylinderEvents_compl Λ₂)).map τ.toFun) ω
    rw [Kernel.coe_comap, Kernel.coe_map_comap _ _ τ.measurable_toFun,
      Kernel.coe_map_comap _ _ τ.measurable_toFun, Function.comp_id]
    dsimp only
    have hf : Measurable fun c ↦
        ((γ (Λ₁.map τ.sites.symm.toEmbedding)) (τ.inv.toFun c)).map τ.toFun :=
      (Measure.measurable_map _ τ.measurable_toFun).comp
        ((γ.measurable_kernel_toMeasure _).comp τ.inv.measurable_toFun)
    rw [Measure.bind_map τ.measurable_toFun hf]
    simp only [Function.comp_def, τ.inv_toFun_toFun]
    rw [← Measure.map_bind (γ.measurable_kernel_toMeasure (Λ₁.map τ.sites.symm.toEmbedding))
      τ.measurable_toFun, Specification.bind (γ := γ) (Finset.map_subset_map.2 h)]
  isMarkovKernel' Λ := Kernel.IsMarkovKernel.map _ τ.measurable_toFun
  isProper' Λ := by
    rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
    intro A hA B hB x
    have hB' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E)
        ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S)ᶜ] (τ.toFun ⁻¹' B) :=
      τ.measurable_toFun_cylinderEvents_compl Λ hB
    show ((γ (Λ.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
        (τ.measurable_inv_toFun_cylinderEvents_compl Λ)).map τ.toFun x (A ∩ B) =
      B.indicator 1 x * ((γ (Λ.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
        (τ.measurable_inv_toFun_cylinderEvents_compl Λ)).map τ.toFun x A
    rw [Kernel.map_apply' _ τ.measurable_toFun _ (hA.inter (cylinderEvents_le_pi _ hB)),
      Kernel.map_apply' _ τ.measurable_toFun _ hA, Kernel.comap_apply', Kernel.comap_apply',
      preimage_inter, (γ.isProper _).inter_eq_indicator_mul cylinderEvents_le_pi
        (τ.measurable_toFun hA) hB']
    congr 1
    classical
    rw [indicator_apply, indicator_apply, mem_preimage, τ.toFun_inv_toFun, Pi.one_apply,
      Pi.one_apply]

@[simp] lemma map_apply (τ : Transformation S E) (γ : Specification S E) (Λ : Finset S)
    (ω : S → E) :
    (γ.map τ) Λ ω = ((γ (Λ.map τ.sites.symm.toEmbedding)) (τ.inv.toFun ω)).map τ.toFun := by
  show ((γ (Λ.map τ.sites.symm.toEmbedding)).comap τ.inv.toFun
    (τ.measurable_inv_toFun_cylinderEvents_compl Λ)).map τ.toFun ω = _
  rw [Kernel.map_apply _ τ.measurable_toFun, Kernel.comap_apply]

/-- **Georgii (5.4)** on sets: `τ(γ)_Λ(A | ω) = γ_{τ_*⁻¹ Λ}(τ⁻¹ A | τ⁻¹ ω)`. -/
lemma map_apply' (τ : Transformation S E) (γ : Specification S E) (Λ : Finset S) (ω : S → E)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    (γ.map τ) Λ ω A = γ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω) (τ.toFun ⁻¹' A) := by
  rw [map_apply, Measure.map_apply τ.measurable_toFun hA]

/-- **Georgii (5.4)**, equivalent form: `τ(γ)_{τ_* Λ}(τ A | τ ω) = γ_Λ(A | ω)`. -/
lemma map_apply_image (τ : Transformation S E) (γ : Specification S E) (Λ : Finset S)
    (ω : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    (γ.map τ) (Λ.map τ.sites.toEmbedding) (τ.toFun ω) (τ.toFun '' A) = γ Λ ω A := by
  have hA' : MeasurableSet (τ.toFun '' A) := τ.toMeasurableEquiv.measurableSet_image.2 hA
  rw [map_apply' _ _ _ _ hA', Finset.map_symm_toEmbedding_map_toEmbedding, τ.inv_toFun_toFun,
    (Function.LeftInverse.injective τ.inv_toFun_toFun).preimage_image]

/-- **Georgii (5.5).** `(τ(γ)_{τ_* Λ} f) ∘ τ = γ_Λ (f ∘ τ)` for the Lebesgue integral. -/
lemma lintegral_map_comp (τ : Transformation S E) (γ : Specification S E) (Λ : Finset S)
    (ω : S → E) (f : (S → E) → ℝ≥0∞) :
    ∫⁻ x, f x ∂(γ.map τ) (Λ.map τ.sites.toEmbedding) (τ.toFun ω) =
      ∫⁻ x, f (τ.toFun x) ∂γ Λ ω := by
  rw [map_apply, Finset.map_symm_toEmbedding_map_toEmbedding, τ.inv_toFun_toFun]
  exact lintegral_map_equiv f τ.toMeasurableEquiv

/-- **Georgii (5.5)**, Bochner form: `(τ(γ)_{τ_* Λ} f) ∘ τ = γ_Λ (f ∘ τ)`. -/
lemma integral_map_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (τ : Transformation S E) (γ : Specification S E) (Λ : Finset S) (ω : S → E)
    (f : (S → E) → F) :
    ∫ x, f x ∂(γ.map τ) (Λ.map τ.sites.toEmbedding) (τ.toFun ω) = ∫ x, f (τ.toFun x) ∂γ Λ ω := by
  rw [map_apply, Finset.map_symm_toEmbedding_map_toEmbedding, τ.inv_toFun_toFun]
  exact integral_map_equiv τ.toMeasurableEquiv f

lemma map_id (γ : Specification S E) : γ.map Transformation.id = γ := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  have hΛ : Λ.map (Transformation.id : Transformation S E).sites.symm.toEmbedding = Λ := by
    ext; simp [Transformation.id]
  have h : (Transformation.id : Transformation S E).toFun = _root_.id :=
    funext Transformation.id_toFun
  rw [map_apply, Transformation.id_inv_toFun, h, Measure.map_id, hΛ]

/-- Georgii (5.4) is a left action: `(τ ∘ σ)(γ) = τ(σ(γ))`. -/
lemma map_comp (τ σ : Transformation S E) (γ : Specification S E) :
    γ.map (τ.comp σ) = (γ.map σ).map τ := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  have hΛ : Λ.map (τ.comp σ).sites.symm.toEmbedding =
      (Λ.map τ.sites.symm.toEmbedding).map σ.sites.symm.toEmbedding := by
    ext x
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Transformation.comp, Equiv.trans_apply]
  have hτσ : (τ.comp σ).toFun = τ.toFun ∘ σ.toFun := funext (Transformation.comp_toFun τ σ)
  rw [map_apply, map_apply, map_apply, hΛ, Transformation.comp_inv_toFun, hτσ,
    Measure.map_map τ.measurable_toFun σ.measurable_toFun]

/-- **Georgii (5.7)(b).** A specification `γ` is `τ`-invariant, and `τ` is a symmetry of `γ`,
if `τ(γ) = γ`. -/
def IsInvariant (τ : Transformation S E) (γ : Specification S E) : Prop := γ.map τ = γ

/-- **Georgii (5.7)(b)** in the displayed form `γ_{τ_* Λ}(· | τ ω) = τ(γ_Λ(· | ω))`. -/
lemma isInvariant_iff {τ : Transformation S E} {γ : Specification S E} :
    IsInvariant τ γ ↔
      ∀ Λ ω, (γ Λ ω).map τ.toFun = γ (Λ.map τ.sites.toEmbedding) (τ.toFun ω) := by
  constructor
  · intro h Λ ω
    have h' : γ.map τ = γ := h
    have := DFunLike.congr_fun (DFunLike.congr_fun h' (Λ.map τ.sites.toEmbedding)) (τ.toFun ω)
    rwa [map_apply, Finset.map_symm_toEmbedding_map_toEmbedding, τ.inv_toFun_toFun] at this
  · intro h
    refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
    rw [map_apply, h, Finset.map_toEmbedding_map_symm_toEmbedding, τ.toFun_inv_toFun]

/-- **Georgii (5.10).** If `μ ∈ 𝒢(γ)` then `τ(μ) ∈ 𝒢(τ(γ))`. -/
theorem map_mem_GP {γ : Specification S E} (τ : Transformation S E)
    {μ : ProbabilityMeasure (S → E)} (hμ : μ ∈ GP γ) :
    μ.map τ.measurable_toFun.aemeasurable ∈ GP (γ.map τ) := by
  rw [mem_GP_iff_forall_bindPM_eq] at hμ ⊢
  intro Λ
  refine ProbabilityMeasure.toMeasure_injective ?_
  have h := congrArg ProbabilityMeasure.toMeasure (hμ (Λ.map τ.sites.symm.toEmbedding))
  rw [Specification.coe_bindPM] at h
  rw [Specification.coe_bindPM, ProbabilityMeasure.toMeasure_map,
    Measure.bind_map τ.measurable_toFun ((γ.map τ).measurable_kernel_toMeasure Λ)]
  have hfun : ⇑((γ.map τ) Λ) ∘ τ.toFun =
      fun ω ↦ ((γ (Λ.map τ.sites.symm.toEmbedding)) ω).map τ.toFun := by
    funext ω
    rw [Function.comp_apply, map_apply, τ.inv_toFun_toFun]
  rw [hfun, ← Measure.map_bind (γ.measurable_kernel_toMeasure (Λ.map τ.sites.symm.toEmbedding))
    τ.measurable_toFun, h]

/-- **Georgii (5.10).** `𝒢(γ)` is invariant under every symmetry of `γ`. -/
theorem IsInvariant.map_mem_GP {τ : Transformation S E} {γ : Specification S E}
    (hγ : IsInvariant τ γ) {μ : ProbabilityMeasure (S → E)} (hμ : μ ∈ GP γ) :
    μ.map τ.measurable_toFun.aemeasurable ∈ GP γ := by
  have h := Specification.map_mem_GP τ hμ
  rwa [show γ.map τ = γ from hγ] at h

/-- **Georgii (5.11).** If `𝒢(γ) = {μ}` then `μ` is preserved by every symmetry of `γ`. -/
theorem IsInvariant.measurePreserving_of_GP_eq_singleton {τ : Transformation S E}
    {γ : Specification S E} (hγ : IsInvariant τ γ) {μ : ProbabilityMeasure (S → E)}
    (hGP : GP γ = {μ}) : MeasurePreserving τ.toFun μ μ := by
  have hμ : μ ∈ GP γ := hGP ▸ mem_singleton μ
  have h := hγ.map_mem_GP hμ
  rw [hGP, mem_singleton_iff] at h
  exact ⟨τ.measurable_toFun, congrArg ProbabilityMeasure.toMeasure h⟩

lemma isInvariant_id (γ : Specification S E) : IsInvariant Transformation.id γ := map_id γ

/-- Georgii (5.7)(d): symmetries of `γ` are closed under composition. -/
lemma IsInvariant.comp {τ σ : Transformation S E} {γ : Specification S E}
    (hτ : IsInvariant τ γ) (hσ : IsInvariant σ γ) : IsInvariant (τ.comp σ) γ := by
  unfold IsInvariant at *
  rw [map_comp, hσ, hτ]

end Specification

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (5.6)(a).** The independent specification `λ.` is invariant under a `λ`-preserving
transformation: `τ(λ.)_Λ(· | ω) = λ_{τ_*⁻¹ Λ}(τ⁻¹ · | τ⁻¹ ω) = λ_Λ(· | ω)`, cf. (5.4). -/
theorem isssdFun_map_toFun (ν : Measure E) [IsProbabilityMeasure ν] (τ : Transformation S E)
    (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S) (ω : S → E) :
    (isssdFun ν (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω)).map τ.toFun =
      isssdFun ν Λ ω := by
  simp only [isssdFun_apply]
  rw [Measure.map_map τ.measurable_toFun Measurable.juxt, τ.toFun_comp_juxt,
    ← Measure.map_map Measurable.juxt (τ.measurePreserving_spin_piCongrLeft hτ Λ).measurable,
    (τ.measurePreserving_spin_piCongrLeft hτ Λ).map_eq]

end Specification

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Reindex
public import GibbsMeasure.Potential.GibbsTransformation
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Mathlib.Analysis.Convex.Extreme

/-!
# Reindexing the sites of a specification along a bijection

Georgii's results on `ℤ` (Chapter 3) and on `ℤ^d` (Chapters 14–15) are identified in Example
(15.40) by reading `ℤ` as `ℤ^1`. This file transports the objects of Chapters 1, 5, 7 and 14 along
an arbitrary bijection `e : S ≃ S'` of site sets, the spin space `E` being fixed. Configurations
are reindexed by `MeasurableEquiv.arrowCongr' e (.refl E) : (S → E) ≃ᵐ (S' → E)`, `ω ↦ ω ∘ e.symm`.

## Main definitions

* `Specification.reindex e γ`: the specification on `S'` with kernels
  `γ'_Λ(A | ω) = γ_{e⁻¹ Λ}((ω ↦ ω ∘ e.symm)⁻¹ A | ω ∘ e)`, i.e. the kernels of `γ` conjugated by the
  configuration equivalence. This is Georgii (5.4) for the site bijection `e`, between different
  site sets; `Specification.map (siteEquiv E e) γ = γ.reindex e` definitionally when `S' = S`
  (`Specification.map_siteEquiv`).

## Main results

* `Specification.isssd_reindex`: the independent specification is reindexed to itself.
* `Potential.gibbsSpecificationOfAbsolutelySummable_reindex`: `γ^{Φ.reindex e} = (γ^Φ).reindex e`,
  Georgii (5.6)(c) for a reindexing.
* `Specification.isGibbsMeasure_reindex_iff`, `MeasureTheory.GibbsMeasure.image_G_reindex`,
  `image_GP_reindex`, `image_extremePoints_G_reindex`: `μ ↦ μ ∘ (ω ↦ ω ∘ e.symm)⁻¹` maps `𝒢(γ)`
  bijectively onto `𝒢(γ.reindex e)`, and its extreme points onto the extreme points.
* `MeasureTheory.GibbsMeasure.image_invariantFields_reindex`, `image_invariantG_reindex`,
  `map_shiftGroup_reindexMulEquiv`: `𝓟_Θ`, `𝒢_Θ(γ)` and the shift group are transported along the
  group isomorphism `Transformation.reindexMulEquiv`, the shift group along an additive bijection
  going to the shift group.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ### Cylinder measurability of the configuration equivalence on finite volumes -/

namespace MeasureTheory

variable {S S' E : Type*} [MeasurableSpace E] (e : S ≃ S')

/-- The image under `e` of the exterior of `e⁻¹ Λ` is the exterior of `Λ`. -/
lemma image_compl_coe_map_symm (Λ : Finset S') :
    e '' ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ = (Λ : Set S')ᶜ := by
  rw [Equiv.image_compl, Potential.coe_map_symm_image]

/-- `ω ↦ ω ∘ e` is measurable from `𝓕_{Λᶜ}` to `𝓕_{(e⁻¹ Λ)ᶜ}`. -/
lemma measurable_arrowCongr'_refl_symm_cylinderEvents_compl (Λ : Finset S') :
    Measurable[cylinderEvents (X := fun _ : S' ↦ E) (Λ : Set S')ᶜ,
      cylinderEvents (X := fun _ : S ↦ E) ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ]
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm := by
  have h := measurable_arrowCongr'_refl_symm_cylinderEvents (E := E) e
    ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ
  rwa [image_compl_coe_map_symm] at h

/-- `ω ↦ ω ∘ e.symm` is measurable from `𝓕_{(e⁻¹ Λ)ᶜ}` to `𝓕_{Λᶜ}`. -/
lemma measurable_arrowCongr'_refl_cylinderEvents_compl (Λ : Finset S') :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ,
      cylinderEvents (X := fun _ : S' ↦ E) (Λ : Set S')ᶜ]
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) := by
  have h := measurable_arrowCongr'_refl_cylinderEvents (E := E) e
    ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ
  rwa [image_compl_coe_map_symm] at h

end MeasureTheory

namespace Specification

variable {S S' E : Type*} [MeasurableSpace E]

-- Lean 4.34's module system does not unfold non-exposed Mathlib defs (e.g. `Kernel.comap`) during
-- `isDefEq`; the consistency proof relies on that unfolding, as in `Specification.lean`.
set_option backward.isDefEq.respectTransparency false in
/-- **Georgii (5.4) for a bijection `e : S ≃ S'` of site sets.** The specification on `S'` whose
kernels are those of `γ` conjugated by the configuration equivalence `ω ↦ ω ∘ e.symm`:
`(γ.reindex e)_Λ(A | ω) = γ_{e⁻¹ Λ}((· ∘ e.symm)⁻¹ A | ω ∘ e)`. -/
def reindex (e : S ≃ S') (γ : Specification S E) : Specification S' E where
  toFun Λ := ((γ (Λ.map e.symm.toEmbedding)).comap
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
    (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ)).map
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))
  isConsistent' := by
    intro Λ₁ Λ₂ h
    refine Kernel.ext fun ω ↦ ?_
    rw [Kernel.comp_apply]
    change ⇑((((γ (Λ₁.map e.symm.toEmbedding)).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
        (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ₁)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))).comap id
        cylinderEvents_le_pi) ∘ₘ
      ((((γ (Λ₂.map e.symm.toEmbedding)).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
        (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ₂)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) ω) =
      (((γ (Λ₂.map e.symm.toEmbedding)).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
        (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ₂)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) ω
    rw [Kernel.coe_comap, Kernel.coe_map_comap _ _ (MeasurableEquiv.measurable _),
      Kernel.coe_map_comap _ _ (MeasurableEquiv.measurable _), Function.comp_id]
    dsimp only
    have hf : Measurable fun c ↦
        ((γ (Λ₁.map e.symm.toEmbedding))
          ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm c)).map
            (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) :=
      (Measure.measurable_map _ (MeasurableEquiv.measurable _)).comp
        ((γ.measurable_kernel_toMeasure _).comp (MeasurableEquiv.measurable _))
    rw [Measure.bind_map (MeasurableEquiv.measurable _) hf]
    simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
    rw [← Measure.map_bind (γ.measurable_kernel_toMeasure (Λ₁.map e.symm.toEmbedding))
      (MeasurableEquiv.measurable _), Specification.bind (γ := γ) (Finset.map_subset_map.2 h)]
  isMarkovKernel' Λ := Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)
  isProper' Λ := by
    rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
    intro A hA B hB x
    have hB' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E)
        ((Λ.map e.symm.toEmbedding : Finset S) : Set S)ᶜ]
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ⁻¹' B) :=
      measurable_arrowCongr'_refl_cylinderEvents_compl e Λ hB
    change ((γ (Λ.map e.symm.toEmbedding)).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
        (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) x (A ∩ B) =
      B.indicator 1 x * ((γ (Λ.map e.symm.toEmbedding)).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
        (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) x A
    rw [Kernel.map_apply' _ (MeasurableEquiv.measurable _) _ (hA.inter (cylinderEvents_le_pi _ hB)),
      Kernel.map_apply' _ (MeasurableEquiv.measurable _) _ hA, Kernel.comap_apply',
      Kernel.comap_apply', preimage_inter,
      (γ.isProper _).inter_eq_indicator_mul cylinderEvents_le_pi
        (MeasurableEquiv.measurable _ hA) hB']
    congr 1
    classical
    rw [indicator_apply, indicator_apply, mem_preimage, MeasurableEquiv.apply_symm_apply,
      Pi.one_apply, Pi.one_apply]

variable (e : S ≃ S') (γ : Specification S E)

@[simp] lemma reindex_apply (Λ : Finset S') (ω : S' → E) :
    (γ.reindex e) Λ ω = ((γ (Λ.map e.symm.toEmbedding))
      ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω)).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) := by
  change ((γ (Λ.map e.symm.toEmbedding)).comap
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
    (measurable_arrowCongr'_refl_symm_cylinderEvents_compl e Λ)).map
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) ω = _
  rw [Kernel.map_apply _ (MeasurableEquiv.measurable _), Kernel.comap_apply]

/-- **Georgii (5.4)** on sets: `(γ.reindex e)_Λ(A | ω) = γ_{e⁻¹ Λ}((· ∘ e.symm)⁻¹ A | ω ∘ e)`. -/
lemma reindex_apply' (Λ : Finset S') (ω : S' → E) {A : Set (S' → E)} (hA : MeasurableSet A) :
    (γ.reindex e) Λ ω A = γ (Λ.map e.symm.toEmbedding)
      ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω)
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ⁻¹' A) := by
  rw [reindex_apply, Measure.map_apply (MeasurableEquiv.measurable _) hA]

/-- **Georgii (5.4)**, equivalent form: `(γ.reindex e)_{e Λ}((· ∘ e.symm) '' A | ω ∘ e.symm) =
γ_Λ(A | ω)`. -/
lemma reindex_apply_image (Λ : Finset S) (ω : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    (γ.reindex e) (Λ.map e.toEmbedding) (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω)
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) '' A) = γ Λ ω A := by
  rw [reindex_apply' _ _ _ _ ((MeasurableEquiv.arrowCongr' e
    (MeasurableEquiv.refl E)).measurableSet_image.2 hA), Finset.map_symm_map,
    MeasurableEquiv.symm_apply_apply, (MeasurableEquiv.injective _).preimage_image]

/-- **Georgii (5.5)** for a reindexing:
`((γ.reindex e)_{e Λ} f)(ω ∘ e.symm) = γ_Λ(f ∘ (· ∘ e.symm))` for the Lebesgue integral. -/
lemma lintegral_reindex_comp (Λ : Finset S) (ω : S → E) (f : (S' → E) → ℝ≥0∞) :
    ∫⁻ x, f x ∂(γ.reindex e) (Λ.map e.toEmbedding)
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) =
      ∫⁻ x, f (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) x) ∂γ Λ ω := by
  rw [reindex_apply, Finset.map_symm_map, MeasurableEquiv.symm_apply_apply]
  exact lintegral_map_equiv f _

/-- **Georgii (5.5)**, Bochner form. -/
lemma integral_reindex_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (Λ : Finset S)
    (ω : S → E) (f : (S' → E) → F) :
    ∫ x, f x ∂(γ.reindex e) (Λ.map e.toEmbedding)
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) =
      ∫ x, f (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) x) ∂γ Λ ω := by
  rw [reindex_apply, Finset.map_symm_map, MeasurableEquiv.symm_apply_apply]
  exact integral_map_equiv _ f

/-- `Specification.map` along the site bijection `siteEquiv E e` of Georgii (5.2)(2) is
`Specification.reindex e`: the two notions agree definitionally when the site sets coincide. -/
lemma map_siteEquiv (e : S ≃ S) : γ.map (siteEquiv E e) = γ.reindex e := rfl

@[simp] lemma reindex_refl : γ.reindex (Equiv.refl S) = γ := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  have hΛ : Λ.map (Equiv.refl S).symm.toEmbedding = Λ := by ext; simp
  rw [reindex_apply, hΛ]
  exact Measure.map_id

lemma reindex_reindex {S'' : Type*} (f : S' ≃ S'') :
    (γ.reindex e).reindex f = γ.reindex (e.trans f) := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  simp only [reindex_apply]
  rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
    Finset.map_map]
  rfl

@[simp] lemma reindex_symm_reindex : (γ.reindex e).reindex e.symm = γ := by
  rw [reindex_reindex, Equiv.self_trans_symm, reindex_refl]

@[simp] lemma reindex_reindex_symm (γ' : Specification S' E) :
    (γ'.reindex e.symm).reindex e = γ' := by
  rw [reindex_reindex, Equiv.symm_trans_self, reindex_refl]

lemma reindex_injective : Function.Injective (reindex (E := E) e) := fun γ γ' h ↦ by
  rw [← reindex_symm_reindex e γ, h, reindex_symm_reindex]

/-- Reindexing commutes with Georgii's action (5.4) of the transformation group:
`(τ γ).reindex e = (τ.reindex e) (γ.reindex e)`. -/
lemma map_reindex (τ : Transformation S E) :
    (γ.reindex e).map (τ.reindex e) = (γ.map τ).reindex e := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  simp only [Specification.map_apply, reindex_apply]
  rw [Measure.map_map (τ.reindex e).measurable_toFun (MeasurableEquiv.measurable _),
    Measure.map_map (MeasurableEquiv.measurable _) τ.measurable_toFun]
  have hΛ : (Λ.map (τ.reindex e).sites.symm.toEmbedding).map e.symm.toEmbedding =
      (Λ.map e.symm.toEmbedding).map τ.sites.symm.toEmbedding := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Transformation.reindex_sites,
      Equiv.trans_apply, Equiv.symm_apply_apply]
  have hω : (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
      ((τ.reindex e).inv.toFun ω) =
      τ.inv.toFun ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω) := by
    rw [← Transformation.reindex_inv]
    funext i
    simp [Transformation.toFun]
  rw [hΛ, hω]
  congr 1
  funext ω
  exact Transformation.reindex_toFun_arrowCongr' e τ ω

/-- Georgii (5.7)(b) is transported: `τ` is a symmetry of `γ` iff `τ.reindex e` is a symmetry of
`γ.reindex e`. -/
lemma isInvariant_reindex_iff (τ : Transformation S E) :
    IsInvariant (τ.reindex e) (γ.reindex e) ↔ IsInvariant τ γ := by
  unfold IsInvariant
  rw [map_reindex]
  exact (reindex_injective e).eq_iff

end Specification

/-! ### The independent specification (Georgii (5.6)(a)) -/

namespace Specification

variable {S S' E : Type*} [MeasurableSpace E] (e : S ≃ S')

/-- The bijection `e⁻¹ Λ ≃ Λ` induced by `e`. -/
def sitesEquiv (Λ : Finset S') : (Λ.map e.symm.toEmbedding : Finset S) ≃ Λ :=
  e.subtypeEquiv fun _ ↦ by simp [Finset.mem_map_equiv]

@[simp] lemma coe_sitesEquiv_apply (Λ : Finset S') (j : (Λ.map e.symm.toEmbedding : Finset S)) :
    (sitesEquiv e Λ j : S') = e j := rfl

@[simp] lemma coe_sitesEquiv_symm_apply (Λ : Finset S') (i : Λ) :
    ((sitesEquiv e Λ).symm i : S) = e.symm i := rfl

/-- The configuration equivalence intertwines the juxtaposition maps:
`(· ∘ e.symm) ∘ juxt_{e⁻¹ Λ}(ω ∘ e) = juxt_Λ(ω) ∘ piCongrLeft`. -/
lemma arrowCongr'_comp_juxt (Λ : Finset S') (ω : S' → E) :
    MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ∘
      juxt ((Λ.map e.symm.toEmbedding : Finset S) : Set S)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω) =
      juxt (Λ : Set S') ω ∘ MeasurableEquiv.piCongrLeft (fun _ : Λ ↦ E) (sitesEquiv e Λ) := by
  funext ζ i
  simp only [Function.comp_apply, MeasurableEquiv.arrowCongr'_refl_apply]
  by_cases hi : i ∈ Λ
  · have hi' : e.symm i ∈ Λ.map e.symm.toEmbedding := by simp [hi]
    rw [juxt_apply_of_mem (Finset.mem_coe.2 hi), juxt_apply_of_mem (Finset.mem_coe.2 hi')]
    have hij : (⟨i, hi⟩ : Λ) = sitesEquiv e Λ ⟨e.symm i, hi'⟩ := Subtype.ext (by simp)
    rw [hij, MeasurableEquiv.piCongrLeft_apply_apply]
  · have hi' : e.symm i ∉ Λ.map e.symm.toEmbedding := by simp [hi]
    rw [juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi),
      juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi')]
    simp

/-- **Georgii (5.6)(a)** for a reindexing: the independent specification `λ.` is carried to
itself, `(λ._{e⁻¹ Λ}(· | ω ∘ e)) ∘ (· ∘ e.symm)⁻¹ = λ._Λ(· | ω)`. -/
theorem isssdFun_reindex (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S') (ω : S' → E) :
    (isssdFun ν (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω)).map
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) = isssdFun ν Λ ω := by
  simp only [isssdFun_apply]
  rw [Measure.map_map (MeasurableEquiv.measurable _) Measurable.juxt, arrowCongr'_comp_juxt,
    ← Measure.map_map Measurable.juxt (MeasurableEquiv.measurable _),
    (measurePreserving_piCongrLeft (fun _ : Λ ↦ ν) (sitesEquiv e Λ)).map_eq]

/-- **Georgii (5.6)(a)** for `isssd`. -/
theorem isssd_reindex_apply (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S')
    (ω : S' → E) :
    (isssd ν (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω)).map
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) = isssd ν Λ ω :=
  isssdFun_reindex e ν Λ ω

/-- **Georgii (5.6)(a)** for a reindexing: `(λ.).reindex e = λ.`. -/
theorem isssd_reindex (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd (S := S) ν).reindex e = isssd (S := S') ν :=
  Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ by
    rw [reindex_apply, isssd_reindex_apply]

/-- **Georgii (5.5)** for `λ.` and a reindexing. -/
lemma lintegral_isssd_comp_arrowCongr'_symm (ν : Measure E) [IsProbabilityMeasure ν]
    (Λ : Finset S') (ω : S' → E) (f : (S → E) → ℝ≥0∞) :
    ∫⁻ x, f ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm x) ∂isssd ν Λ ω =
      ∫⁻ x, f x ∂isssd ν (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω) := by
  rw [← isssd_reindex e ν, reindex_apply, lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

/-! #### Modifications and the Gibbsian specification (Georgii (5.6)(b),(c)) -/

/-- The reindexing of a density family: `(ρ.reindex e)_Λ(η) = ρ_{e⁻¹ Λ}(η ∘ e)`, Georgii (5.3). -/
lemma premodifierZ_reindex (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S') (η : S' → E) :
    premodifierZ (S := S') (E := E) ν
        (fun Λ η ↦ ρ (Λ.map e.symm.toEmbedding)
          ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η)) Λ η =
      premodifierZ (S := S) (E := E) ν ρ (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) :=
  lintegral_isssd_comp_arrowCongr'_symm e ν Λ η _

lemma premodifierNorm_reindex (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S') (η : S' → E) :
    premodifierNorm (S := S') (E := E) ν
        (fun Λ η ↦ ρ (Λ.map e.symm.toEmbedding)
          ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η)) Λ η =
      premodifierNorm (S := S) (E := E) ν ρ (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) := by
  simp only [premodifierNorm, Specification.relNorm, premodifierZ_reindex e ν]

/-- The kernels of `(ρλ.).reindex e` are the `λ.`-kernels with the reindexed densities. -/
lemma coe_modification_isssd_reindex (ν : Measure E) [IsProbabilityMeasure ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    ⇑(((isssd (S := S) (E := E) ν).modification ρ hρ).reindex e) =
      modificationKer (isssd (S := S') (E := E) ν)
        (fun Λ η ↦ ρ (Λ.map e.symm.toEmbedding)
          ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η))
        (fun Λ ↦ (hρ.measurable (Λ.map e.symm.toEmbedding)).comp
          (MeasurableEquiv.measurable _)) := by
  funext Λ
  refine Kernel.ext fun ω ↦ ?_
  rw [reindex_apply, modification_apply, modificationKer_apply, MeasurableEquiv.map_withDensity,
    isssd_reindex_apply e ν]
  rfl

/-- **Georgii (5.6)(b)** for a reindexing: the reindexed densities form a `λ`-modification. -/
theorem IsModifier.reindex_isssd (ν : Measure E) [IsProbabilityMeasure ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    (isssd (S := S') (E := E) ν).IsModifier
      fun Λ η ↦ ρ (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) where
  measurable Λ := (hρ.measurable (Λ.map e.symm.toEmbedding)).comp (MeasurableEquiv.measurable _)
  isMarkovKernel Λ := by
    rw [← congrFun (coe_modification_isssd_reindex e ν hρ) Λ]
    infer_instance
  isConsistent := by
    rw [← coe_modification_isssd_reindex e ν hρ]
    exact (((isssd ν).modification ρ hρ).reindex e).isConsistent

/-- **Georgii (5.6)(b)** for a reindexing: `(ρλ.).reindex e = (ρ.reindex e)λ.`. -/
theorem modification_isssd_reindex (ν : Measure E) [IsProbabilityMeasure ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    ((isssd (S := S) (E := E) ν).modification ρ hρ).reindex e =
      (isssd (S := S') (E := E) ν).modification
        (fun Λ η ↦ ρ (Λ.map e.symm.toEmbedding)
          ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η))
        (hρ.reindex_isssd e ν) :=
  Specification.ext fun Λ ↦ congrFun (coe_modification_isssd_reindex e ν hρ) Λ

end Specification

namespace Potential

variable {S S' E : Type*} [MeasurableSpace E] (e : S ≃ S') (Φ : Potential S E) (ν : Measure E)
  [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (5.6)(c)** for a reindexing, the partition function (2.7):
`Z^{Φ.reindex e}_Λ(η) = Z^Φ_{e⁻¹ Λ}(η ∘ e)`. -/
theorem premodifierZ_boltzmannFactor_reindex (Λ : Finset S') (η : S' → E) :
    Specification.premodifierZ (S := S') (E := E) ν ((Φ.reindex e).boltzmannFactor β) Λ η =
      Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β)
        (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) := by
  have h : (Φ.reindex e).boltzmannFactor β =
      fun Λ η ↦ Φ.boltzmannFactor β (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) :=
    funext fun Λ ↦ funext fun η ↦ boltzmannFactor_reindex' e Φ β Λ η
  rw [h, Specification.premodifierZ_reindex e ν]

/-- **Georgii (5.6)(c)** for a reindexing: `ρ^{Φ.reindex e} = (ρ^Φ).reindex e`. -/
theorem premodifierNorm_boltzmannFactor_reindex :
    Specification.premodifierNorm (S := S') (E := E) ν ((Φ.reindex e).boltzmannFactor β) =
      fun Λ η ↦ Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β)
        (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) := by
  have h : (Φ.reindex e).boltzmannFactor β =
      fun Λ η ↦ Φ.boltzmannFactor β (Λ.map e.symm.toEmbedding)
        ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) :=
    funext fun Λ ↦ funext fun η ↦ boltzmannFactor_reindex' e Φ β Λ η
  funext Λ η
  rw [h, Specification.premodifierNorm_reindex e ν]

/-- **Georgii (5.6)(c) at the specification level, for a reindexing.** The Gibbsian specification
of the reindexed potential is the reindexed Gibbsian specification:
`γ^{Φ.reindex e} = (γ^Φ).reindex e` for `Φ ∈ ℬ`. -/
theorem gibbsSpecificationOfAbsolutelySummable_reindex [Countable S] [Countable S']
    [IsPotential Φ] [IsAbsolutelySummable Φ] :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ.reindex e) ν β =
      (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).reindex e := by
  unfold gibbsSpecificationOfAbsolutelySummable
  rw [Specification.modification_isssd_reindex e ν]
  exact Specification.modification_congr (premodifierNorm_boltzmannFactor_reindex e Φ ν β) _ _

end Potential

/-! ### Transport of Gibbs measures (Georgii (5.10)) -/

namespace Specification

variable {S S' E : Type*} [MeasurableSpace E] (e : S ≃ S') {γ : Specification S E}

/-- **Georgii (5.10)** for a reindexing: if `μ ∈ 𝒢(γ)` then
`μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝒢(γ.reindex e)`. -/
theorem IsGibbsMeasure.reindex {μ : Measure (S → E)} [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) :
    (γ.reindex e).IsGibbsMeasure
      (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) := by
  rw [isGibbsMeasure_iff_forall_bind_eq] at hμ ⊢
  intro Λ
  rw [Measure.bind_map (MeasurableEquiv.measurable _)
    ((γ.reindex e).measurable_kernel_toMeasure Λ)]
  have hfun : ⇑((γ.reindex e) Λ) ∘ MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) =
      fun ω ↦ ((γ (Λ.map e.symm.toEmbedding)) ω).map
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) := by
    funext ω
    rw [Function.comp_apply, reindex_apply, MeasurableEquiv.symm_apply_apply]
  rw [hfun, ← Measure.map_bind (γ.measurable_kernel_toMeasure (Λ.map e.symm.toEmbedding))
    (MeasurableEquiv.measurable _), hμ]

/-- **Georgii (5.10)** for a reindexing is an equivalence: `μ ∈ 𝒢(γ)` iff
`μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝒢(γ.reindex e)`. -/
theorem isGibbsMeasure_reindex_iff {μ : Measure (S → E)} [IsFiniteMeasure μ] :
    (γ.reindex e).IsGibbsMeasure
      (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) ↔ γ.IsGibbsMeasure μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reindex e⟩
  have := h.reindex e.symm
  rwa [reindex_symm_reindex, ← MeasurableEquiv.arrowCongr'_refl_symm, MeasurableEquiv.map_symm_map]
    at this

/-- Every Gibbs measure of `γ.reindex e` is the reindexing of a Gibbs measure of `γ`. -/
theorem isGibbsMeasure_reindex_iff' {μ : Measure (S' → E)} [IsFiniteMeasure μ] :
    (γ.reindex e).IsGibbsMeasure μ ↔ γ.IsGibbsMeasure
      (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm) := by
  conv_lhs => rw [← MeasurableEquiv.map_map_symm
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) (ν := μ)]
  exact isGibbsMeasure_reindex_iff e

end Specification

namespace MeasureTheory.GibbsMeasure

variable {S S' E : Type*} [MeasurableSpace E] (e : S ≃ S') {γ : Specification S E}

/-- `μ ∈ 𝒢(γ)` iff `μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝒢(γ.reindex e)`. -/
lemma map_mem_G_reindex_iff {μ : Measure (S → E)} :
    μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) ∈ G (γ.reindex e) ↔ μ ∈ G γ := by
  rw [G.mem_iff, G.mem_iff,
    Measure.isProbabilityMeasure_map_iff (MeasurableEquiv.measurable _).aemeasurable]
  refine and_congr_right fun h ↦ ?_
  exact Specification.isGibbsMeasure_reindex_iff e

/-- **`μ ↦ μ ∘ (· ∘ e.symm)⁻¹` maps `𝒢(γ)` bijectively onto `𝒢(γ.reindex e)`.** -/
theorem image_G_reindex :
    Measure.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) '' G γ =
      G (γ.reindex e) := by
  ext μ
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact (map_mem_G_reindex_iff e).2 hμ
  · intro hμ
    refine ⟨μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm, ?_,
      MeasurableEquiv.map_map_symm _⟩
    rw [← map_mem_G_reindex_iff e, MeasurableEquiv.map_map_symm]
    exact hμ

/-- The extreme points of `𝒢(γ)` (Georgii §7.1) are carried onto those of `𝒢(γ.reindex e)`. -/
theorem image_extremePoints_G_reindex :
    Measure.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) ''
        (G γ).extremePoints ℝ≥0∞ =
      (G (γ.reindex e)).extremePoints ℝ≥0∞ := by
  have hlin : ⇑(Measure.mapₗ (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) =
      Measure.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) :=
    funext (Measure.mapₗ_apply_of_measurable (MeasurableEquiv.measurable _))
  rw [← image_G_reindex, ← hlin]
  exact LinearMapClass.image_extremePoints _
    (hlin ▸ MeasurableEquiv.map_measurableEquiv_injective _) _

/-- `μ ∈ ex 𝒢(γ)` iff `μ ∘ (· ∘ e.symm)⁻¹ ∈ ex 𝒢(γ.reindex e)`. -/
lemma map_mem_extremePoints_G_reindex_iff {μ : Measure (S → E)} :
    μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) ∈
        (G (γ.reindex e)).extremePoints ℝ≥0∞ ↔
      μ ∈ (G γ).extremePoints ℝ≥0∞ := by
  rw [← image_extremePoints_G_reindex]
  exact (MeasurableEquiv.map_measurableEquiv_injective _).mem_set_image

/-- `μ ∈ 𝒢(γ)` iff `μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝒢(γ.reindex e)`, for probability measures. -/
lemma map_mem_GP_reindex_iff {μ : ProbabilityMeasure (S → E)} :
    μ.map (MeasurableEquiv.measurable (MeasurableEquiv.arrowCongr' e
      (MeasurableEquiv.refl E))).aemeasurable ∈ GP (γ.reindex e) ↔ μ ∈ GP γ := by
  change (γ.reindex e).IsGibbsMeasure _ ↔ γ.IsGibbsMeasure _
  rw [ProbabilityMeasure.toMeasure_map]
  exact Specification.isGibbsMeasure_reindex_iff e

/-- **`μ ↦ μ ∘ (· ∘ e.symm)⁻¹` maps `𝒢(γ)` bijectively onto `𝒢(γ.reindex e)`**, for probability
measures. -/
theorem image_GP_reindex :
    (fun μ : ProbabilityMeasure (S → E) ↦ μ.map (MeasurableEquiv.measurable
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))).aemeasurable) '' GP γ =
      GP (γ.reindex e) := by
  ext μ
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact (map_mem_GP_reindex_iff e).2 hμ
  · intro hμ
    refine ⟨μ.map (MeasurableEquiv.measurable (MeasurableEquiv.arrowCongr' e
      (MeasurableEquiv.refl E)).symm).aemeasurable, ?_, ?_⟩
    · rw [← map_mem_GP_reindex_iff e]
      convert hμ using 1
      refine ProbabilityMeasure.toMeasure_injective ?_
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        MeasurableEquiv.map_map_symm]
    · refine ProbabilityMeasure.toMeasure_injective ?_
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        MeasurableEquiv.map_map_symm]

/-! ### Transport of invariant fields and the shift group (Georgii (14.1), (5.2)(1)) -/

/-- A transformation `τ` preserves `μ` iff `τ.reindex e` preserves `μ ∘ (· ∘ e.symm)⁻¹`. -/
lemma measurePreserving_reindex_toFun_map_iff (τ : Transformation S E) {μ : Measure (S → E)} :
    MeasurePreserving (τ.reindex e).toFun
        (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)))
        (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) ↔
      MeasurePreserving τ.toFun μ μ := by
  have hc : MeasurePreserving (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) μ
      (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) :=
    ⟨MeasurableEquiv.measurable _, rfl⟩
  have hc' : MeasurePreserving (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
      (μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))) μ :=
    ⟨MeasurableEquiv.measurable _, MeasurableEquiv.map_symm_map _⟩
  constructor
  · intro h
    have := (hc'.comp h).comp hc
    convert this using 1
    funext ω
    simp only [Function.comp_apply, Transformation.reindex_toFun, MeasurableEquiv.symm_apply_apply]
  · intro h
    rw [Transformation.reindex_toFun]
    exact (hc.comp h).comp hc'

/-- **Georgii (14.1)** is transported: `μ ∈ 𝓟_Θ` iff `μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝓟_{Θ.reindex e}`. -/
lemma map_mem_invariantFields_reindex_iff (Θ : Subgroup (Transformation S E))
    {μ : Measure (S → E)} :
    μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) ∈
        invariantFields (Θ.map (Transformation.reindexMulEquiv E e).toMonoidHom) ↔
      μ ∈ invariantFields Θ := by
  rw [mem_invariantFields_iff, mem_invariantFields_iff,
    Measure.isProbabilityMeasure_map_iff (MeasurableEquiv.measurable _).aemeasurable]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h τ hτ
    exact (measurePreserving_reindex_toFun_map_iff e τ).1
      (h _ (Subgroup.mem_map.2 ⟨τ, hτ, rfl⟩))
  · rintro h _ hτ'
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hτ'
    exact (measurePreserving_reindex_toFun_map_iff e τ).2 (h τ hτ)

/-- **`μ ↦ μ ∘ (· ∘ e.symm)⁻¹` maps `𝓟_Θ` bijectively onto `𝓟_{Θ.reindex e}`.** -/
theorem image_invariantFields_reindex (Θ : Subgroup (Transformation S E)) :
    Measure.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) '' invariantFields Θ =
      invariantFields (Θ.map (Transformation.reindexMulEquiv E e).toMonoidHom) := by
  ext μ
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact (map_mem_invariantFields_reindex_iff e Θ).2 hμ
  · intro hμ
    refine ⟨μ.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm, ?_,
      MeasurableEquiv.map_map_symm _⟩
    rw [← map_mem_invariantFields_reindex_iff e, MeasurableEquiv.map_map_symm]
    exact hμ

/-- **`μ ↦ μ ∘ (· ∘ e.symm)⁻¹` maps `𝒢_Θ(γ)` bijectively onto `𝒢_{Θ.reindex e}(γ.reindex e)`**
(Georgii (14.14)). -/
theorem image_invariantG_reindex (Θ : Subgroup (Transformation S E)) :
    Measure.map (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) '' invariantG γ Θ =
      invariantG (γ.reindex e) (Θ.map (Transformation.reindexMulEquiv E e).toMonoidHom) := by
  rw [invariantG, invariantG,
    Set.image_inter (MeasurableEquiv.map_measurableEquiv_injective _), image_G_reindex,
    image_invariantFields_reindex]

/-- Reindexing along an additive bijection carries Georgii's shift group `Θ` (5.2)(1) to the shift
group. -/
theorem map_shiftGroup_reindexMulEquiv [AddGroup S] [AddGroup S'] (e : S ≃+ S') :
    (shiftGroup S E).map (Transformation.reindexMulEquiv E (e : S ≃ S')).toMonoidHom =
      shiftGroup S' E := by
  ext τ
  rw [Subgroup.mem_map, mem_shiftGroup]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨e j, (Transformation.reindex_shift e j).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨shift E (e.symm j), shift_mem_shiftGroup _, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, Transformation.reindexMulEquiv_apply,
      Transformation.reindex_shift, AddEquiv.apply_symm_apply]

/-- **Georgii (14.1)** for the shift group, along an additive bijection: `μ ∈ 𝓟_Θ` iff
`μ ∘ (· ∘ e.symm)⁻¹ ∈ 𝓟_Θ`. -/
lemma map_mem_invariantFields_shiftGroup_iff [AddGroup S] [AddGroup S'] (e : S ≃+ S')
    {μ : Measure (S → E)} :
    μ.map (MeasurableEquiv.arrowCongr' (e : S ≃ S') (MeasurableEquiv.refl E)) ∈
        invariantFields (shiftGroup S' E) ↔ μ ∈ invariantFields (shiftGroup S E) := by
  rw [← map_shiftGroup_reindexMulEquiv e, map_mem_invariantFields_reindex_iff]

/-- **Georgii (14.14)** for the shift group, along an additive bijection: `𝒢_Θ(γ)` is carried
bijectively onto `𝒢_Θ(γ.reindex e)`. -/
theorem image_invariantG_shiftGroup_reindex [AddGroup S] [AddGroup S'] (e : S ≃+ S') :
    Measure.map (MeasurableEquiv.arrowCongr' (e : S ≃ S') (MeasurableEquiv.refl E)) ''
        invariantG γ (shiftGroup S E) =
      invariantG (γ.reindex (e : S ≃ S')) (shiftGroup S' E) := by
  rw [image_invariantG_reindex, map_shiftGroup_reindexMulEquiv]

end MeasureTheory.GibbsMeasure

end

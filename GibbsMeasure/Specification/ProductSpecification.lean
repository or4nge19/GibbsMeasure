/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LocalLimits
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Georgii, Example (7.18)-(7.19): product specifications
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Lean 4.34's module system does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`)
-- during `isDefEq`. Several proofs below rely on that unfolding.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace
open scoped ENNReal

/-! ### The measurable equivalence `E^{S₁ ⊕ S₂} ≃ E^{S₁} × E^{S₂}` -/

namespace MeasurableEquiv

/-- `Equiv.sumArrowEquivProdArrow` as a measurable equivalence: a configuration on a disjoint
union of two site sets is the same thing as a pair of configurations. -/
noncomputable def sumArrowEquivProdArrow (α β γ : Type*) [MeasurableSpace γ] :
    (α ⊕ β → γ) ≃ᵐ (α → γ) × (β → γ) :=
  MeasurableEquiv.sumPiEquivProdPi fun _ : α ⊕ β ↦ γ

@[simp] lemma coe_sumArrowEquivProdArrow (α β γ : Type*) [MeasurableSpace γ] :
    ⇑(sumArrowEquivProdArrow α β γ) = fun f ↦ (fun a ↦ f (.inl a), fun b ↦ f (.inr b)) := rfl

@[simp] lemma sumArrowEquivProdArrow_symm_apply {α β γ : Type*} [MeasurableSpace γ]
    (p : (α → γ) × (β → γ)) : (sumArrowEquivProdArrow α β γ).symm p = Sum.elim p.1 p.2 := by
  funext i; cases i <;> rfl

end MeasurableEquiv

namespace MeasureTheory

variable {S₁ S₂ E : Type*} [MeasurableSpace E]

/-- The cylinder σ-algebra of `Δ ⊆ S₁ ⊕ S₂` is, under the identification
`E^{S₁ ⊕ S₂} ≃ E^{S₁} × E^{S₂}`, the product of the cylinder σ-algebras of the two traces
of `Δ`. -/
lemma cylinderEvents_sum (Δ : Set (S₁ ⊕ S₂)) :
    cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) Δ =
      MeasurableSpace.comap (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E)
        ((cylinderEvents (X := fun _ : S₁ ↦ E) (Sum.inl ⁻¹' Δ)).prod
          (cylinderEvents (X := fun _ : S₂ ↦ E) (Sum.inr ⁻¹' Δ))) := by
  have h1 : (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E :
        ((S₁ ⊕ S₂) → E) → (S₁ → E) × (S₂ → E)) =
      fun η ↦ ((fun i ↦ η (Sum.inl i)), (fun i ↦ η (Sum.inr i))) := rfl
  rw [h1, MeasurableSpace.comap_prodMk]
  simp only [cylinderEvents, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rw [iSup_sum]
  rfl

/-- Splitting a configuration on `S₁ ⊕ S₂` is measurable from the cylinder σ-algebra of `Δ` to
the product of the cylinder σ-algebras of the traces of `Δ`. -/
lemma measurable_sumArrowEquivProdArrow (Δ : Set (S₁ ⊕ S₂)) :
    Measurable[cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) Δ,
        (cylinderEvents (X := fun _ : S₁ ↦ E) (Sum.inl ⁻¹' Δ)).prod
          (cylinderEvents (X := fun _ : S₂ ↦ E) (Sum.inr ⁻¹' Δ))]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) :=
  Measurable.of_comap_le (cylinderEvents_sum (E := E) Δ).ge

/-- Glueing a pair of configurations is measurable from the product of the cylinder σ-algebras of
the traces of `Δ` to the cylinder σ-algebra of `Δ`. -/
lemma measurable_sumArrowEquivProdArrow_symm (Δ : Set (S₁ ⊕ S₂)) :
    Measurable[(cylinderEvents (X := fun _ : S₁ ↦ E) (Sum.inl ⁻¹' Δ)).prod
        (cylinderEvents (X := fun _ : S₂ ↦ E) (Sum.inr ⁻¹' Δ)),
      cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) Δ]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm := by
  rw [measurable_iff_comap_le, cylinderEvents_sum (E := E) Δ, MeasurableSpace.comap_comp]
  have : (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) ∘
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm = id :=
    funext fun p ↦ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).apply_symm_apply p
  rw [this]
  simp

end MeasureTheory

/-! ### Missing `Mathlib` API: properness, monotonicity of product σ-algebras, parallel binds -/

namespace MeasurableSpace

variable {α β : Type*}

/-- The product of measurable spaces is monotone in both arguments. -/
lemma prod_le_prod {m₁ m₁' : MeasurableSpace α} {m₂ m₂' : MeasurableSpace β} (h₁ : m₁ ≤ m₁')
    (h₂ : m₂ ≤ m₂') : m₁.prod m₂ ≤ m₁'.prod m₂' :=
  sup_le_sup (comap_mono h₁) (comap_mono h₂)

end MeasurableSpace

namespace ProbabilityTheory.Kernel

section IsProper
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X}

/-- A kernel that charges a boundary event exactly when its argument belongs to it is proper.

This is the "Dirac on `𝓑`" characterization of properness, and it is how properness is checked in
practice: no integration is involved. -/
lemma isProper_of_apply_eq_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (h : ∀ ⦃B : Set X⦄, MeasurableSet[𝓑] B → ∀ x, π x B = B.indicator 1 x) : π.IsProper := by
  refine IsProper.of_inter_eq_indicator_mul h𝓑𝓧 fun A hA B hB x ↦ ?_
  have hBm : MeasurableSet[𝓧] B := h𝓑𝓧 _ hB
  by_cases hx : x ∈ B
  · have hBc : π x Bᶜ = 0 := by simpa [hx] using h hB.compl x
    have h1 : π x (A \ B) = 0 := measure_mono_null (fun _ hy ↦ hy.2) hBc
    have h2 : π x (A ∩ B) + π x (A \ B) = π x A := measure_inter_add_sdiff A hBm
    simp only [hx, indicator_of_mem, Pi.one_apply, one_mul]
    simpa [h1] using h2
  · have hB0 : π x B = 0 := by simpa [hx] using h hB x
    have h1 : π x (A ∩ B) = 0 := measure_mono_null inter_subset_right hB0
    simp [hx, h1]

/-- A proper Markov kernel is the Dirac kernel on boundary events. -/
lemma IsProper.apply_eq_indicator [IsMarkovKernel π] (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    {B : Set X} (hB : MeasurableSet[𝓑] B) (x : X) : π x B = B.indicator 1 x := by
  simpa using hπ.inter_eq_indicator_mul h𝓑𝓧 (MeasurableSet.univ (m := 𝓧) (α := X)) hB x

end IsProper

section ParallelComp
variable {X Y : Type*} {𝓑X 𝓧X : MeasurableSpace X} {𝓑Y 𝓧Y : MeasurableSpace Y}

/-- **Properness is stable under parallel composition.** If `π` is proper for `𝓑X ≤ 𝓧X` and `ρ` is
proper for `𝓑Y ≤ 𝓧Y`, then `π ∥ₖ ρ` is proper for the product σ-algebras. -/
theorem IsProper.parallelComp {π : Kernel[𝓑X, 𝓧X] X X} {ρ : Kernel[𝓑Y, 𝓧Y] Y Y}
    [IsMarkovKernel π] [IsMarkovKernel ρ]
    (h𝓑X : 𝓑X ≤ 𝓧X) (h𝓑Y : 𝓑Y ≤ 𝓧Y) (hπ : π.IsProper) (hρ : ρ.IsProper) :
    (π ∥ₖ ρ).IsProper := by
  have hle : 𝓑X.prod 𝓑Y ≤ 𝓧X.prod 𝓧Y := MeasurableSpace.prod_le_prod h𝓑X h𝓑Y
  refine isProper_of_apply_eq_indicator hle ?_
  set C : Set (Set (X × Y)) :=
    Set.image2 (· ×ˢ ·) {s : Set X | MeasurableSet[𝓑X] s} {t : Set Y | MeasurableSet[𝓑Y] t}
    with hC
  have hgen : (𝓑X.prod 𝓑Y) = MeasurableSpace.generateFrom C :=
    (@generateFrom_prod X Y 𝓑X 𝓑Y).symm
  have hpi : IsPiSystem C := @isPiSystem_prod X Y 𝓑X 𝓑Y
  have key : ∀ B : Set (X × Y), MeasurableSet[𝓑X.prod 𝓑Y] B →
      ∀ z : X × Y, (π ∥ₖ ρ) z B = Measure.dirac z B := by
    refine MeasurableSpace.induction_on_inter (m := 𝓑X.prod 𝓑Y) hgen hpi ?_ ?_ ?_ ?_
    · intro z; simp
    · rintro _ ⟨s, hs, t, ht, rfl⟩ z
      rw [parallelComp_apply_prod,
        Measure.dirac_apply' _ (hle _ (hs.prod ht : MeasurableSet[𝓑X.prod 𝓑Y] (s ×ˢ t))),
        hπ.apply_eq_indicator h𝓑X hs, hρ.apply_eq_indicator h𝓑Y ht, Set.indicator_prod_one]
    · intro s hs ih z
      rw [prob_compl_eq_one_sub (hle _ hs), prob_compl_eq_one_sub (hle _ hs), ih z]
    · intro f hdisj hmeas ih z
      rw [measure_iUnion hdisj fun i ↦ hle _ (hmeas i),
        measure_iUnion hdisj fun i ↦ hle _ (hmeas i)]
      exact tsum_congr fun i ↦ ih i z
  intro B hB z
  rw [key B hB z, Measure.dirac_apply' _ (hle _ hB)]

end ParallelComp

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {X₁ X₂ Y₁ Y₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁]
  [MeasurableSpace Y₂]

/-- **Fubini for parallel binds**: binding a product measure along a pair of kernels acting on the
two coordinates separately produces the product of the two binds. -/
lemma bind_prod_parallelComp (μ₁ : Measure X₁) (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂]
    (κ₁ : Kernel X₁ Y₁) (κ₂ : Kernel X₂ Y₂) [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] :
    (μ₁.prod μ₂).bind (fun p ↦ (κ₁ p.1).prod (κ₂ p.2)) = (μ₁.bind κ₁).prod (μ₂.bind κ₂) := by
  have h := DFunLike.congr_fun
    (Kernel.parallelComp_comp_parallelComp (κ := Kernel.const Unit μ₁) (η := κ₁)
      (κ' := Kernel.const Unit μ₂) (η' := κ₂)) ((), ())
  rw [Kernel.comp_apply, Kernel.parallelComp_apply, Kernel.const_apply, Kernel.const_apply,
    Kernel.parallelComp_apply, Kernel.comp_apply, Kernel.comp_apply, Kernel.const_apply,
    Kernel.const_apply] at h
  refine .trans ?_ h
  refine Measure.bind_congr_right ?_
  exact ae_of_all _ fun p ↦ (Kernel.parallelComp_apply κ₁ κ₂ p).symm

end MeasureTheory.Measure

/-! ### The product specification -/

namespace Specification

variable {S₁ S₂ E : Type*} [MeasurableSpace E]

section Prod

variable (γ₁ : Specification S₁ E) (γ₂ : Specification S₂ E)

open MeasureTheory

@[simp] lemma preimage_inl_compl_coe (Λ : Finset (S₁ ⊕ S₂)) :
    Sum.inl ⁻¹' ((Λ : Set (S₁ ⊕ S₂))ᶜ) = ((Λ.toLeft : Set S₁))ᶜ := by
  ext i; simp

@[simp] lemma preimage_inr_compl_coe (Λ : Finset (S₁ ⊕ S₂)) :
    Sum.inr ⁻¹' ((Λ : Set (S₁ ⊕ S₂))ᶜ) = ((Λ.toRight : Set S₂))ᶜ := by
  ext i; simp

/-- Splitting a configuration is measurable from the boundary events of `Λ` to the product of the
boundary events of the two traces of `Λ`. -/
lemma measurable_split (Λ : Finset (S₁ ⊕ S₂)) :
    Measurable[cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) ((Λ : Set (S₁ ⊕ S₂))ᶜ),
        (cylinderEvents (X := fun _ : S₁ ↦ E) ((Λ.toLeft : Set S₁)ᶜ)).prod
          (cylinderEvents (X := fun _ : S₂ ↦ E) ((Λ.toRight : Set S₂)ᶜ))]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) := by
  have h := measurable_sumArrowEquivProdArrow (E := E) ((Λ : Set (S₁ ⊕ S₂))ᶜ)
  rwa [preimage_inl_compl_coe, preimage_inr_compl_coe] at h

/-- Glueing a pair of configurations is measurable from the product of the boundary events of the
two traces of `Λ` to the boundary events of `Λ`. -/
lemma measurable_glue (Λ : Finset (S₁ ⊕ S₂)) :
    Measurable[(cylinderEvents (X := fun _ : S₁ ↦ E) ((Λ.toLeft : Set S₁)ᶜ)).prod
        (cylinderEvents (X := fun _ : S₂ ↦ E) ((Λ.toRight : Set S₂)ᶜ)),
      cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) ((Λ : Set (S₁ ⊕ S₂))ᶜ)]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm := by
  have h := measurable_sumArrowEquivProdArrow_symm (E := E) ((Λ : Set (S₁ ⊕ S₂))ᶜ)
  rwa [preimage_inl_compl_coe, preimage_inr_compl_coe] at h

/-- **Georgii (7.18)**: the boundary-condition kernels of the product specification
`γ¹ × γ²`, namely `γ_{Λ}(· | ω¹ω²) = γ¹_{Λ ∩ S₁}(· | ω¹) × γ²_{Λ ∩ S₂}(· | ω²)`. -/
noncomputable def prodKernel (Λ : Finset (S₁ ⊕ S₂)) :
    Kernel[cylinderEvents (X := fun _ : S₁ ⊕ S₂ ↦ E) ((Λ : Set (S₁ ⊕ S₂))ᶜ)]
      ((S₁ ⊕ S₂) → E) ((S₁ ⊕ S₂) → E) :=
  Kernel.map
    (Kernel.comap (γ₁ Λ.toLeft ∥ₖ γ₂ Λ.toRight)
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) (measurable_split (E := E) Λ))
    (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm

lemma prodKernel_apply (Λ : Finset (S₁ ⊕ S₂)) (η : (S₁ ⊕ S₂) → E) :
    prodKernel γ₁ γ₂ Λ η =
      Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
        ((γ₁ Λ.toLeft fun i ↦ η (.inl i)).prod (γ₂ Λ.toRight fun i ↦ η (.inr i))) := by
  rw [prodKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _), Kernel.comap_apply,
    Kernel.parallelComp_apply]
  rfl

instance instIsMarkovKernelProdKernel (Λ : Finset (S₁ ⊕ S₂)) :
    IsMarkovKernel (prodKernel γ₁ γ₂ Λ) := by
  rw [prodKernel]
  exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.measurable _)

/-- Measurability, in the pair of boundary conditions, of the product of the two finite-volume
kernels. -/
lemma measurable_prodMeasure (L : Finset S₁) (R : Finset S₂) :
    Measurable fun p : (S₁ → E) × (S₂ → E) ↦ (γ₁ L p.1).prod (γ₂ R p.2) := by
  have hfun : (fun p : (S₁ → E) × (S₂ → E) ↦ (γ₁ L p.1).prod (γ₂ R p.2))
      = fun p ↦ (γ₁ L ∥ₖ γ₂ R) p := funext fun p ↦ (Kernel.parallelComp_apply _ _ p).symm
  rw [hfun]
  exact (γ₁ L ∥ₖ γ₂ R).measurable.mono
    (MeasurableSpace.prod_le_prod cylinderEvents_le_pi cylinderEvents_le_pi) le_rfl

lemma measurable_prodKernel (Λ : Finset (S₁ ⊕ S₂)) :
    Measurable fun η : (S₁ ⊕ S₂) → E ↦ prodKernel γ₁ γ₂ Λ η :=
  (prodKernel γ₁ γ₂ Λ).measurable.mono cylinderEvents_le_pi le_rfl

/-- Properness of the product kernels: Georgii's "routine argument" for (7.18). -/
lemma isProper_prodKernel (Λ : Finset (S₁ ⊕ S₂)) : (prodKernel γ₁ γ₂ Λ).IsProper := by
  have hpar : (γ₁ Λ.toLeft ∥ₖ γ₂ Λ.toRight).IsProper :=
    Kernel.IsProper.parallelComp cylinderEvents_le_pi cylinderEvents_le_pi
      (γ₁.isProper _) (γ₂.isProper _)
  refine Kernel.isProper_of_apply_eq_indicator cylinderEvents_le_pi fun B hB η ↦ ?_
  have hB' : MeasurableSet[(cylinderEvents (X := fun _ : S₁ ↦ E) ((Λ.toLeft : Set S₁)ᶜ)).prod
      (cylinderEvents (X := fun _ : S₂ ↦ E) ((Λ.toRight : Set S₂)ᶜ))]
      ((MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm ⁻¹' B) :=
    measurable_glue (E := E) Λ hB
  have h := hpar.apply_eq_indicator
    (MeasurableSpace.prod_le_prod cylinderEvents_le_pi cylinderEvents_le_pi) hB'
    (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E η)
  rw [prodKernel, Kernel.map_apply _ (MeasurableEquiv.measurable _),
    Measure.map_apply (MeasurableEquiv.measurable _) (cylinderEvents_le_pi _ hB),
    Kernel.comap_apply, h]
  have hmem : ((MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) η ∈
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm ⁻¹' B) ↔ η ∈ B := by
    rw [Set.mem_preimage, (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm_apply_apply]
  by_cases hη : η ∈ B
  · rw [Set.indicator_of_mem (hmem.2 hη), Set.indicator_of_mem hη]
    simp
  · rw [Set.indicator_of_notMem fun hc ↦ hη (hmem.1 hc), Set.indicator_of_notMem hη]

/-- **Fubini for the product specification**: pushing a product measure through the product
kernel over `Λ` binds the two factors separately, along `γ¹` over `Λ ∩ S₁` and `γ²` over
`Λ ∩ S₂`. -/
lemma bind_prodKernel_map_prod (Λ : Finset (S₁ ⊕ S₂)) (μ₁ : Measure (S₁ → E))
    (μ₂ : Measure (S₂ → E)) [SFinite μ₁] [SFinite μ₂] :
    (Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
        (μ₁.prod μ₂)).bind (prodKernel γ₁ γ₂ Λ)
      = Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
          ((μ₁.bind (γ₁ Λ.toLeft)).prod (μ₂.bind (γ₂ Λ.toRight))) := by
  set φ := (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm with hφ
  have hcongr : (fun ζ ↦ prodKernel γ₁ γ₂ Λ ζ) ∘ φ
      = fun p : (S₁ → E) × (S₂ → E) ↦
          Measure.map φ ((γ₁ Λ.toLeft p.1).prod (γ₂ Λ.toRight p.2)) :=
    funext fun p ↦ prodKernel_apply γ₁ γ₂ Λ _
  have hc₁ : ∀ ω : S₁ → E,
      ((γ₁ Λ.toLeft).comap id cylinderEvents_le_pi) ω = γ₁ Λ.toLeft ω :=
    fun ω ↦ Kernel.comap_apply _ _ _
  have hc₂ : ∀ ω : S₂ → E,
      ((γ₂ Λ.toRight).comap id cylinderEvents_le_pi) ω = γ₂ Λ.toRight ω :=
    fun ω ↦ Kernel.comap_apply _ _ _
  have hfub := Measure.bind_prod_parallelComp (μ₁ := μ₁) (μ₂ := μ₂)
    (κ₁ := (γ₁ Λ.toLeft).comap id cylinderEvents_le_pi)
    (κ₂ := (γ₂ Λ.toRight).comap id cylinderEvents_le_pi)
  rw [Measure.bind_congr_right (ae_of_all _ hc₁),
    Measure.bind_congr_right (ae_of_all _ hc₂)] at hfub
  simp only [hc₁, hc₂] at hfub
  calc (Measure.map φ (μ₁.prod μ₂)).bind (prodKernel γ₁ γ₂ Λ)
      = (μ₁.prod μ₂).bind ((fun ζ ↦ prodKernel γ₁ γ₂ Λ ζ) ∘ φ) :=
        Measure.bind_map (MeasurableEquiv.measurable _) (measurable_prodKernel γ₁ γ₂ Λ)
    _ = (μ₁.prod μ₂).bind (fun p ↦ Measure.map φ ((γ₁ Λ.toLeft p.1).prod (γ₂ Λ.toRight p.2))) := by
        rw [hcongr]
    _ = Measure.map φ ((μ₁.prod μ₂).bind fun p ↦ (γ₁ Λ.toLeft p.1).prod (γ₂ Λ.toRight p.2)) :=
        (Measure.map_bind (measurable_prodMeasure γ₁ γ₂ Λ.toLeft Λ.toRight)
          (MeasurableEquiv.measurable _)).symm
    _ = Measure.map φ ((μ₁.bind (γ₁ Λ.toLeft)).prod (μ₂.bind (γ₂ Λ.toRight))) := by rw [hfub]

/-- Consistency of the product kernels, pointwise form. -/
lemma bind_prodKernel {Λ Λ' : Finset (S₁ ⊕ S₂)} (hΛ : Λ ⊆ Λ') (η : (S₁ ⊕ S₂) → E) :
    (prodKernel γ₁ γ₂ Λ' η).bind (prodKernel γ₁ γ₂ Λ) = prodKernel γ₁ γ₂ Λ' η := by
  rw [prodKernel_apply γ₁ γ₂ Λ', bind_prodKernel_map_prod, γ₁.bind (Finset.toLeft_subset_toLeft hΛ),
    γ₂.bind (Finset.toRight_subset_toRight hΛ), ← prodKernel_apply γ₁ γ₂ Λ' η]

lemma isConsistent_prodKernel : IsConsistent (prodKernel γ₁ γ₂) := by
  intro Λ Λ' hΛ
  refine Kernel.ext fun η ↦ ?_
  rw [Kernel.comp_apply]
  have : ((prodKernel γ₁ γ₂ Λ).comap id cylinderEvents_le_pi : _ → Measure ((S₁ ⊕ S₂) → E))
      = fun ζ ↦ prodKernel γ₁ γ₂ Λ ζ := funext fun ζ ↦ Kernel.comap_apply _ _ _
  rw [this]
  exact bind_prodKernel γ₁ γ₂ hΛ η

/-- **Georgii, Example (7.18)**: the product `γ¹ × γ²` of two specifications, on the disjoint
union `S₁ ⊕ S₂` of their parameter sets, is a specification. -/
noncomputable def prod : Specification (S₁ ⊕ S₂) E where
  toFun := prodKernel γ₁ γ₂
  isConsistent' := isConsistent_prodKernel γ₁ γ₂
  isMarkovKernel' Λ := instIsMarkovKernelProdKernel γ₁ γ₂ Λ
  isProper' Λ := isProper_prodKernel γ₁ γ₂ Λ

@[simp] lemma prod_apply' (Λ : Finset (S₁ ⊕ S₂)) : (γ₁.prod γ₂) Λ = prodKernel γ₁ γ₂ Λ := rfl

/-- **Georgii (7.18)**, the defining identity:
`(γ¹ × γ²)_Λ(· | ω¹ω²) = γ¹_{Λ ∩ S₁}(· | ω¹) × γ²_{Λ ∩ S₂}(· | ω²)`. -/
lemma prod_apply (Λ : Finset (S₁ ⊕ S₂)) (η : (S₁ ⊕ S₂) → E) :
    (γ₁.prod γ₂) Λ η =
      Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
        ((γ₁ Λ.toLeft fun i ↦ η (.inl i)).prod (γ₂ Λ.toRight fun i ↦ η (.inr i))) :=
  prodKernel_apply γ₁ γ₂ Λ η

/-- **Georgii (7.18)**: a product of Gibbs measures is a Gibbs measure for the product
specification, `{μ¹ × μ² : μᵏ ∈ 𝒢(γᵏ)} ⊆ 𝒢(γ¹ × γ²)`.

The inclusion is strict as soon as both factors have more than one Gibbs measure: for
`νᵏ ∈ 𝒢(γᵏ) \ {μᵏ}` the average `(μ¹ × μ² + ν¹ × ν²)/2` is Gibbs for the product but is not a
product measure. -/
theorem isGibbsMeasure_prod_map {μ₁ : Measure (S₁ → E)} {μ₂ : Measure (S₂ → E)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : γ₁.IsGibbsMeasure μ₁) (h₂ : γ₂.IsGibbsMeasure μ₂) :
    (γ₁.prod γ₂).IsGibbsMeasure
      (Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)) := by
  have hprob : IsProbabilityMeasure
      (Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable
  refine (isGibbsMeasure_iff_forall_bind_eq (γ := γ₁.prod γ₂)).2 fun Λ ↦ ?_
  rw [prod_apply']
  rw [bind_prodKernel_map_prod,
    (isGibbsMeasure_iff_forall_bind_eq (γ := γ₁) (μ := μ₁)).1 h₁ Λ.toLeft,
    (isGibbsMeasure_iff_forall_bind_eq (γ := γ₂) (μ := μ₂)).1 h₂ Λ.toRight]

end Prod

end Specification

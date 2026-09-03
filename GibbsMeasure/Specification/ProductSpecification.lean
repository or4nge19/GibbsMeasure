/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.ProdZeroOne
public import GibbsMeasure.Specification.LocalLimits
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Georgii, Example (7.18)-(7.19): product specifications

Let `γ¹` and `γ²` be specifications with the same state space `E` and parameter sets `S₁` and `S₂`.
Georgii's product specification `γ = γ¹ × γ²` on the disjoint union `S₁ ⊕ S₂` is
`γ_Λ(· | ω¹ω²) = γ¹_{Λ ∩ S₁}(· | ω¹) × γ²_{Λ ∩ S₂}(· | ω²)`, read through the measurable
equivalence `E^{S₁ ⊕ S₂} ≃ E^{S₁} × E^{S₂}` (`MeasurableEquiv.sumArrowEquivProdArrow`).

* `Specification.prod`, `Specification.prod_apply`: **Example (7.18)**, the product specification
  and its defining identity. Consistency comes from Fubini for parallel binds
  (`Specification.bind_prodKernel_map_prod`), properness from
  `ProbabilityTheory.Kernel.IsProper.parallelComp`.
* `Specification.isGibbsMeasure_prod_map`: `{μ¹ × μ² : μᵏ ∈ 𝒢(γᵏ)} ⊆ 𝒢(γ)`, an inclusion that is
  strict as soon as both factors have more than one Gibbs measure.
* `MeasureTheory.GibbsMeasure.extremePoints_G_prod`: **Equation (7.19)**,
  `ex 𝒢(γ) = {μ¹ × μ² : μᵏ ∈ ex 𝒢(γᵏ)}`. Both inclusions go through Theorem (7.7), extremality
  `↔` tail triviality. Forwards: a product of tail-trivial measures is tail-trivial
  (`MeasureTheory.GibbsMeasure.isTailTrivial_map_symm_prod`, from the zero-one law
  `MeasureTheory.Measure.prod_apply_eq_zero_or_one_iInf`). Backwards: Theorem (7.12)(a) turns the
  product structure of `γ_Λ` into independence of the two blocks of coordinates
  (`MeasureTheory.GibbsMeasure.measure_preimage_prod_eq_mul_of_mem_extremePoints_G_prod`), so an
  extreme `μ` is the product of its two marginals, each of which is Gibbs and tail-trivial. The
  factorwise converse Georgii states — if `μ¹ × μ²` is extreme then so is each `μᵏ` — is
  `MeasureTheory.GibbsMeasure.mem_extremePoints_G_of_mem_extremePoints_G_prod_map`.
* `MeasureTheory.GibbsMeasure.extremePointsGProdEquiv`,
  `MeasureTheory.GibbsMeasure.card_extremePoints_G_prod`,
  `MeasureTheory.GibbsMeasure.mk_extremePoints_G_prod`: the bijection
  `ex 𝒢(γ¹) × ex 𝒢(γ²) ≃ ex 𝒢(γ)` and the resulting
  `|ex 𝒢(γ)| = |ex 𝒢(γ¹)| |ex 𝒢(γ²)|`, Georgii's recipe for a specification with a prescribed
  number of phases.
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

/-! ### Missing `Mathlib` API: properness under parallel composition, parallel binds

Monotonicity of the product of σ-algebras (`MeasurableSpace.prod_le_prod`) and the section lemmas
it is used with live in `GibbsMeasure/Mathlib/MeasureTheory/Measure/ProdZeroOne.lean`. -/

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

/-! ### Georgii (7.19): the extreme points of `𝒢(γ¹ × γ²)` -/

namespace MeasureTheory.GibbsMeasure

open scoped Topology

universe u₁ u₂ u₃

variable {S₁ : Type u₁} {S₂ : Type u₂} {E : Type u₃} [MeasurableSpace E]

/-! #### Tail events of `E^{S₁ ⊕ S₂}` and of the two factors -/

/-- Splitting a configuration undoes glueing, on preimages. -/
lemma preimage_symm_preimage_sumArrow (u : Set ((S₁ → E) × (S₂ → E))) :
    (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm ⁻¹'
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' u) = u := by
  ext p
  simp only [Set.mem_preimage, MeasurableEquiv.apply_symm_apply]

/-- A tail event `A¹ ∈ 𝓣¹` of the first factor, read as the event `A¹ × Ω²` of the disjoint union,
is a tail event: for every finite `Λ ⊆ S₁ ⊕ S₂` it only depends on the sites outside `Λ`. -/
lemma measurableSet_tail_preimage_prod_univ {A₁ : Set (S₁ → E)}
    (hA₁ : MeasurableSet[@tailSigmaAlgebra S₁ E _] A₁) :
    MeasurableSet[@tailSigmaAlgebra (S₁ ⊕ S₂) E _]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (A₁ ×ˢ (univ : Set (S₂ → E)))) := by
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ Specification.measurable_split (E := E) Λ ?_
  exact @MeasurableSet.prod _ _ (cylinderEvents (X := fun _ : S₁ ↦ E) ((Λ.toLeft : Set S₁)ᶜ))
    (cylinderEvents (X := fun _ : S₂ ↦ E) ((Λ.toRight : Set S₂)ᶜ)) A₁ univ
    (MeasurableSpace.measurableSet_iInf.1 hA₁ Λ.toLeft) MeasurableSet.univ

/-- A tail event `A² ∈ 𝓣²` of the second factor, read as the event `Ω¹ × A²` of the disjoint
union, is a tail event. -/
lemma measurableSet_tail_preimage_univ_prod {A₂ : Set (S₂ → E)}
    (hA₂ : MeasurableSet[@tailSigmaAlgebra S₂ E _] A₂) :
    MeasurableSet[@tailSigmaAlgebra (S₁ ⊕ S₂) E _]
      (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' ((univ : Set (S₁ → E)) ×ˢ A₂)) := by
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ Specification.measurable_split (E := E) Λ ?_
  exact @MeasurableSet.prod _ _ (cylinderEvents (X := fun _ : S₁ ↦ E) ((Λ.toLeft : Set S₁)ᶜ))
    (cylinderEvents (X := fun _ : S₂ ↦ E) ((Λ.toRight : Set S₂)ᶜ)) univ A₂
    MeasurableSet.univ (MeasurableSpace.measurableSet_iInf.1 hA₂ Λ.toRight)

/-- Georgii's `𝓣 = ⋂_Λ 𝓕¹_{S₁∖Λ} × 𝓕²_{S₂∖Λ}`, in the direction that carries the proof of (7.19):
a tail event of the disjoint union is, for *every* pair of finite volumes `L ⊆ S₁` and `R ⊆ S₂`,
an event of `𝓕¹_{S₁∖L} ⊗ 𝓕²_{S₂∖R}` on the pair space.

Note that this is genuinely weaker than membership of `𝓣¹ ⊗ 𝓣²`: an infimum of product
σ-algebras is bigger than the product of the infima. That is why the zero-one law used below,
`MeasureTheory.Measure.prod_apply_eq_zero_or_one_iInf`, is stated for families. -/
lemma measurableSet_prod_preimage_symm_of_measurableSet_tail {A : Set ((S₁ ⊕ S₂) → E)}
    (hA : MeasurableSet[@tailSigmaAlgebra (S₁ ⊕ S₂) E _] A) (L : Finset S₁) (R : Finset S₂) :
    MeasurableSet[(cylinderEvents (X := fun _ : S₁ ↦ E) ((L : Set S₁)ᶜ)).prod
        (cylinderEvents (X := fun _ : S₂ ↦ E) ((R : Set S₂)ᶜ))]
      ((MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm ⁻¹' A) := by
  have h := Specification.measurable_glue (E := E) (L.disjSum R)
    (MeasurableSpace.measurableSet_iInf.1 hA (L.disjSum R))
  rwa [Finset.toLeft_disjSum, Finset.toRight_disjSum] at h

/-- **Georgii (7.19), the tail-triviality half**: a product `μ¹ × μ²` of two tail-trivial
probability measures is trivial on the tail σ-algebra of the disjoint union.

Georgii's argument: for `A ∈ 𝓣` the section `A(ω¹)` lies in `𝓣²` and `ω¹ ↦ μ²(A(ω¹))` is
`𝓣¹`-measurable, so `μ²(A(ω¹)) ∈ {0,1}` for all `ω¹` and
`μ(A) = ∫ μ¹(dω¹) μ²(A(ω¹)) ∈ {0,1}`. -/
theorem isTailTrivial_map_symm_prod {μ₁ : Measure (S₁ → E)} {μ₂ : Measure (S₂ → E)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : ∀ A, MeasurableSet[@tailSigmaAlgebra S₁ E _] A → μ₁ A = 0 ∨ μ₁ A = 1)
    (h₂ : ∀ B, MeasurableSet[@tailSigmaAlgebra S₂ E _] B → μ₂ B = 0 ∨ μ₂ B = 1)
    (A : Set ((S₁ ⊕ S₂) → E)) (hA : MeasurableSet[@tailSigmaAlgebra (S₁ ⊕ S₂) E _] A) :
    Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂) A = 0 ∨
      Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂) A = 1 := by
  rw [MeasurableEquiv.map_apply]
  refine Measure.prod_apply_eq_zero_or_one_iInf
    (m₁ := fun L : Finset S₁ ↦ cylinderEvents (X := fun _ : S₁ ↦ E) ((L : Set S₁)ᶜ))
    (m₂ := fun R : Finset S₂ ↦ cylinderEvents (X := fun _ : S₂ ↦ E) ((R : Set S₂)ᶜ))
    (fun _ ↦ cylinderEvents_le_pi) (fun _ ↦ cylinderEvents_le_pi) h₁ h₂ ?_
  exact MeasurableSpace.measurableSet_iInf.2 fun L ↦ MeasurableSpace.measurableSet_iInf.2 fun R ↦
    measurableSet_prod_preimage_symm_of_measurableSet_tail hA L R

/-- Two products of probability measures agree only if their factors do: the factors are the
marginals. -/
lemma map_symm_prod_inj {μ₁ ν₁ : Measure (S₁ → E)} {μ₂ ν₂ : Measure (S₂ → E)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)
      = Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (ν₁.prod ν₂)) :
    μ₁ = ν₁ ∧ μ₂ = ν₂ := by
  have h' : μ₁.prod μ₂ = ν₁.prod ν₂ := MeasurableEquiv.map_measurableEquiv_injective _ h
  refine ⟨?_, ?_⟩
  · have hf := congrArg Measure.fst h'
    rwa [Measure.fst_prod, Measure.fst_prod] at hf
  · have hs := congrArg Measure.snd h'
    rwa [Measure.snd_prod, Measure.snd_prod] at hs

/-! #### The two inclusions of (7.19) -/

variable (γ₁ : Specification S₁ E) (γ₂ : Specification S₂ E)

/-- The product specification on a rectangle:
`(γ¹ × γ²)_Λ(A¹ × A² | ω) = γ¹_{Λ ∩ S₁}(A¹ | ω¹) γ²_{Λ ∩ S₂}(A² | ω²)`. -/
lemma prod_apply_preimage_prod (Λ : Finset (S₁ ⊕ S₂)) (η : (S₁ ⊕ S₂) → E)
    (s : Set (S₁ → E)) (t : Set (S₂ → E)) :
    (γ₁.prod γ₂) Λ η (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (s ×ˢ t))
      = (γ₁ Λ.toLeft fun i ↦ η (.inl i)) s * (γ₂ Λ.toRight fun i ↦ η (.inr i)) t := by
  rw [Specification.prod_apply, MeasurableEquiv.map_apply, preimage_symm_preimage_sumArrow,
    Measure.prod_prod]

/-- **Georgii (7.19), the inclusion `⊇`**: a product of extreme Gibbs measures is an extreme Gibbs
measure of the product specification.

By Theorem (7.7) both `μᵏ` are tail-trivial, hence so is `μ¹ × μ²`, which is Gibbs for `γ¹ × γ²`
by (7.18); Theorem (7.7) again makes it extreme. -/
theorem mem_extremePoints_G_prod_map [Countable S₁] [Countable S₂]
    {μ₁ : Measure (S₁ → E)} {μ₂ : Measure (S₂ → E)}
    (h₁ : μ₁ ∈ (G (γ := γ₁)).extremePoints ℝ≥0∞)
    (h₂ : μ₂ ∈ (G (γ := γ₂)).extremePoints ℝ≥0∞) :
    Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)
      ∈ (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞ := by
  have hp₁ : IsProbabilityMeasure μ₁ := h₁.1.1
  have hp₂ : IsProbabilityMeasure μ₂ := h₂.1.1
  have hG : Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)
      ∈ G (γ := γ₁.prod γ₂) :=
    ⟨Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable,
      Specification.isGibbsMeasure_prod_map γ₁ γ₂ h₁.1.2 h₂.1.2⟩
  exact mem_extremePoints_G_of_isTailTrivial hG fun A hA ↦
    isTailTrivial_map_symm_prod (tailTrivial_of_mem_extremePoints_G h₁)
      (tailTrivial_of_mem_extremePoints_G h₂) A hA

/-- **The key step of the converse of (7.19)**: under an extreme Gibbs measure `μ` of a product
specification the two blocks of coordinates are independent,
`μ(A¹ × A²) = μ(A¹ × Ω²) μ(Ω¹ × A²)`.

This is Georgii's computation: by Theorem (7.12)(a) the three probabilities are the `μ`-a.e.
limits of `γ_{Λ_n}(· | ω)` along the exhaustion, and the product structure of `γ` makes the
finite-volume quantities *exactly* multiplicative at every `n`. -/
theorem measure_preimage_prod_eq_mul_of_mem_extremePoints_G_prod
    [Countable S₁] [Countable S₂] {μ : Measure ((S₁ ⊕ S₂) → E)}
    (hμ : μ ∈ (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞)
    {s : Set (S₁ → E)} {t : Set (S₂ → E)} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (s ×ˢ t))
      = μ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (s ×ˢ univ))
        * μ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (univ ×ˢ t)) := by
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have hm : ∀ u : Set ((S₁ → E) × (S₂ → E)), MeasurableSet u →
      MeasurableSet (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' u) :=
    fun _ hu ↦ (MeasurableEquiv.measurable _) hu
  set A := MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (s ×ˢ t) with hAdef
  set A₁ := MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' (s ×ˢ (univ : Set (S₂ → E)))
    with hA₁def
  set A₂ := MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹' ((univ : Set (S₁ → E)) ×ˢ t)
    with hA₂def
  have h1 := tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G hμ (hm _ (hs.prod ht))
  have h2 := tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G hμ
    (hm _ (hs.prod MeasurableSet.univ))
  have h3 := tendsto_ae_kernel_exhaustion_of_mem_extremePoints_G hμ
    (hm _ (MeasurableSet.univ.prod ht))
  obtain ⟨ω, hω1, hω2, hω3⟩ := (h1.and (h2.and h3)).exists
  have hpt : ∀ n : ℕ, ((γ₁.prod γ₂) (exhaustionVolumes n) ω A).toReal
      = ((γ₁.prod γ₂) (exhaustionVolumes n) ω A₁).toReal
        * ((γ₁.prod γ₂) (exhaustionVolumes n) ω A₂).toReal := by
    intro n
    rw [hAdef, hA₁def, hA₂def, prod_apply_preimage_prod, prod_apply_preimage_prod,
      prod_apply_preimage_prod, measure_univ, measure_univ, mul_one, one_mul, ENNReal.toReal_mul]
  have hlim : Tendsto (fun n ↦ ((γ₁.prod γ₂) (exhaustionVolumes n) ω A).toReal) atTop
      (𝓝 (μ.real A₁ * μ.real A₂)) := by
    simpa only [hpt] using hω2.mul hω3
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A)
    (ENNReal.mul_ne_top (measure_ne_top μ A₁) (measure_ne_top μ A₂))).1 ?_
  rw [ENNReal.toReal_mul]
  exact tendsto_nhds_unique hω1 hlim

/-- **Georgii (7.19), the inclusion `⊆`**: an extreme Gibbs measure of a product specification is
the product of two extreme Gibbs measures of the factors.

Independence of the two blocks identifies `μ` with the product of its marginals `μ¹` and `μ²`;
Fubini for the product specification (`Specification.bind_prodKernel_map_prod`) plus injectivity
of `μ ↦ μ ∘ φ⁻¹` turns the DLR equation for `μ` into `μ¹ γ¹_{Λ₁} = μ¹` and `μ² γ²_{Λ₂} = μ²`; and
a tail event of a factor is a tail event of the disjoint union, so both marginals are tail-trivial
and hence extreme by Theorem (7.7). -/
theorem exists_eq_map_prod_of_mem_extremePoints_G_prod [Countable S₁] [Countable S₂]
    {μ : Measure ((S₁ ⊕ S₂) → E)} (hμ : μ ∈ (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞) :
    ∃ μ₁ ∈ (G (γ := γ₁)).extremePoints ℝ≥0∞, ∃ μ₂ ∈ (G (γ := γ₂)).extremePoints ℝ≥0∞,
      μ = Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂) := by
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have hρprob : IsProbabilityMeasure
      (Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) μ) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable
  set ρ := Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E) μ with hρ
  -- Independence of the two blocks identifies `ρ` with the product of its marginals.
  have hsplit : ρ = ρ.fst.prod ρ.snd := by
    refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
    rw [Measure.fst_apply hs, Measure.snd_apply ht, ← Set.prod_univ, ← Set.univ_prod, hρ,
      MeasurableEquiv.map_apply, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
    exact measure_preimage_prod_eq_mul_of_mem_extremePoints_G_prod γ₁ γ₂ hμ hs ht
  have hμeq : μ = Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
      (ρ.fst.prod ρ.snd) := by
    rw [← hsplit, hρ, MeasurableEquiv.map_symm_map]
  -- The DLR equation for `μ` splits into the DLR equations for the two marginals.
  have hprod : ∀ (L : Finset S₁) (R : Finset S₂),
      (ρ.fst.bind (γ₁ L)).prod (ρ.snd.bind (γ₂ R)) = ρ.fst.prod ρ.snd := by
    intro L R
    have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ₁.prod γ₂)
      (μ := μ)).1 hμ.1.2 (L.disjSum R)
    rw [hμeq, Specification.prod_apply', Specification.bind_prodKernel_map_prod,
      Finset.toLeft_disjSum, Finset.toRight_disjSum] at hbind
    exact MeasurableEquiv.map_measurableEquiv_injective _ hbind
  have hfix₁ : ∀ L : Finset S₁, ρ.fst.bind (γ₁ L) = ρ.fst := by
    intro L
    have hpb : IsProbabilityMeasure (ρ.snd.bind (γ₂ ∅)) := γ₂.isProbabilityMeasure_bind ∅ ρ.snd
    have hpb' : IsProbabilityMeasure (ρ.fst.bind (γ₁ L)) := γ₁.isProbabilityMeasure_bind L ρ.fst
    have h := congrArg Measure.fst (hprod L ∅)
    rwa [Measure.fst_prod, Measure.fst_prod] at h
  have hfix₂ : ∀ R : Finset S₂, ρ.snd.bind (γ₂ R) = ρ.snd := by
    intro R
    have hpb : IsProbabilityMeasure (ρ.fst.bind (γ₁ ∅)) := γ₁.isProbabilityMeasure_bind ∅ ρ.fst
    have hpb' : IsProbabilityMeasure (ρ.snd.bind (γ₂ R)) := γ₂.isProbabilityMeasure_bind R ρ.snd
    have h := congrArg Measure.snd (hprod ∅ R)
    rwa [Measure.snd_prod, Measure.snd_prod] at h
  have hG₁ : ρ.fst ∈ G (γ := γ₁) :=
    ⟨inferInstance, Specification.isGibbsMeasure_iff_forall_bind_eq.2 hfix₁⟩
  have hG₂ : ρ.snd ∈ G (γ := γ₂) :=
    ⟨inferInstance, Specification.isGibbsMeasure_iff_forall_bind_eq.2 hfix₂⟩
  -- Both marginals are tail-trivial, because a tail event of a factor is a tail event.
  have htail₁ :
      IsTailTrivial (S := S₁) (E := E) (⟨ρ.fst, hG₁.1⟩ : ProbabilityMeasure (S₁ → E)) := by
    intro A₁ hA₁
    have hval : ρ.fst A₁ = μ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹'
        (A₁ ×ˢ (univ : Set (S₂ → E)))) := by
      rw [Measure.fst_apply (tailSigmaAlgebra_le_pi _ hA₁), ← Set.prod_univ, hρ,
        MeasurableEquiv.map_apply]
    change ρ.fst A₁ = 0 ∨ ρ.fst A₁ = 1
    rw [hval]
    exact tailTrivial_of_mem_extremePoints_G hμ _ (measurableSet_tail_preimage_prod_univ hA₁)
  have htail₂ :
      IsTailTrivial (S := S₂) (E := E) (⟨ρ.snd, hG₂.1⟩ : ProbabilityMeasure (S₂ → E)) := by
    intro A₂ hA₂
    have hval : ρ.snd A₂ = μ (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E ⁻¹'
        ((univ : Set (S₁ → E)) ×ˢ A₂)) := by
      rw [Measure.snd_apply (tailSigmaAlgebra_le_pi _ hA₂), ← Set.univ_prod, hρ,
        MeasurableEquiv.map_apply]
    change ρ.snd A₂ = 0 ∨ ρ.snd A₂ = 1
    rw [hval]
    exact tailTrivial_of_mem_extremePoints_G hμ _ (measurableSet_tail_preimage_univ_prod hA₂)
  exact ⟨ρ.fst, mem_extremePoints_G_of_isTailTrivial hG₁ htail₁, ρ.snd,
    mem_extremePoints_G_of_isTailTrivial hG₂ htail₂, hμeq⟩

/-- **Georgii (7.19), the converse for the factors**: if a product `μ¹ × μ²` of probability
measures is extreme in `𝒢(γ¹ × γ²)`, then each factor is extreme in `𝒢(γᵏ)`.

Georgii argues directly — a nontrivial splitting `μ¹ = s ν + (1-s) ν'` inside `𝒢(γ¹)` produces the
splitting `μ = s (ν × μ²) + (1-s) (ν' × μ²)` inside `𝒢(γ)` — but the same conclusion falls out of
the inclusion `⊆` above, since the two factors of a product of probability measures are its
marginals. -/
theorem mem_extremePoints_G_of_mem_extremePoints_G_prod_map [Countable S₁] [Countable S₂]
    {μ₁ : Measure (S₁ → E)} {μ₂ : Measure (S₂ → E)}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h : Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (μ₁.prod μ₂)
      ∈ (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞) :
    μ₁ ∈ (G (γ := γ₁)).extremePoints ℝ≥0∞ ∧ μ₂ ∈ (G (γ := γ₂)).extremePoints ℝ≥0∞ := by
  obtain ⟨ν₁, hν₁, ν₂, hν₂, heq⟩ := exists_eq_map_prod_of_mem_extremePoints_G_prod γ₁ γ₂ h
  have hp₁ : IsProbabilityMeasure ν₁ := hν₁.1.1
  have hp₂ : IsProbabilityMeasure ν₂ := hν₂.1.1
  obtain ⟨e₁, e₂⟩ := map_symm_prod_inj heq
  exact ⟨by rw [e₁]; exact hν₁, by rw [e₂]; exact hν₂⟩

/-! #### (7.19) and the number of phases -/

/-- **Georgii, equation (7.19)**:
`ex 𝒢(γ¹ × γ²) = {μ¹ × μ² : μᵏ ∈ ex 𝒢(γᵏ), k = 1, 2}`. -/
theorem extremePoints_G_prod [Countable S₁] [Countable S₂] :
    (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞ =
      (fun p : Measure (S₁ → E) × Measure (S₂ → E) ↦
          Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm (p.1.prod p.2)) ''
        ((G (γ := γ₁)).extremePoints ℝ≥0∞ ×ˢ (G (γ := γ₂)).extremePoints ℝ≥0∞) := by
  ext μ
  constructor
  · intro hμ
    obtain ⟨μ₁, h₁, μ₂, h₂, rfl⟩ := exists_eq_map_prod_of_mem_extremePoints_G_prod γ₁ γ₂ hμ
    exact ⟨(μ₁, μ₂), ⟨h₁, h₂⟩, rfl⟩
  · rintro ⟨⟨μ₁, μ₂⟩, ⟨h₁, h₂⟩, rfl⟩
    exact mem_extremePoints_G_prod_map γ₁ γ₂ h₁ h₂

/-- `(μ¹, μ²) ↦ μ¹ × μ²` is a bijection from `ex 𝒢(γ¹) × ex 𝒢(γ²)` onto `ex 𝒢(γ¹ × γ²)`. -/
theorem bijective_prod_extremePoints_G [Countable S₁] [Countable S₂] :
    Function.Bijective
      (fun p : (G (γ := γ₁)).extremePoints ℝ≥0∞ × (G (γ := γ₂)).extremePoints ℝ≥0∞ ↦
        (⟨Measure.map (MeasurableEquiv.sumArrowEquivProdArrow S₁ S₂ E).symm
            ((p.1 : Measure (S₁ → E)).prod (p.2 : Measure (S₂ → E))),
          mem_extremePoints_G_prod_map γ₁ γ₂ p.1.2 p.2.2⟩ :
          (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞)) := by
  constructor
  · rintro ⟨⟨μ₁, hμ₁⟩, ⟨μ₂, hμ₂⟩⟩ ⟨⟨ν₁, hν₁⟩, ⟨ν₂, hν₂⟩⟩ h
    have h₁ : IsProbabilityMeasure μ₁ := hμ₁.1.1
    have h₂ : IsProbabilityMeasure μ₂ := hμ₂.1.1
    have h₃ : IsProbabilityMeasure ν₁ := hν₁.1.1
    have h₄ : IsProbabilityMeasure ν₂ := hν₂.1.1
    obtain ⟨e₁, e₂⟩ := map_symm_prod_inj (Subtype.ext_iff.1 h)
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨e₁, e₂⟩
  · rintro ⟨μ, hμ⟩
    obtain ⟨μ₁, h₁, μ₂, h₂, rfl⟩ := exists_eq_map_prod_of_mem_extremePoints_G_prod γ₁ γ₂ hμ
    exact ⟨(⟨μ₁, h₁⟩, ⟨μ₂, h₂⟩), rfl⟩

/-- **Georgii (7.19)** as the explicit bijection `ex 𝒢(γ¹) × ex 𝒢(γ²) ≃ ex 𝒢(γ¹ × γ²)`,
`(μ¹, μ²) ↦ μ¹ × μ²`. This is the statement behind `|ex 𝒢(γ)| = |ex 𝒢(γ¹)| |ex 𝒢(γ²)|`. -/
noncomputable def extremePointsGProdEquiv [Countable S₁] [Countable S₂] :
    ((G (γ := γ₁)).extremePoints ℝ≥0∞ × (G (γ := γ₂)).extremePoints ℝ≥0∞) ≃
      (G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞ :=
  Equiv.ofBijective _ (bijective_prod_extremePoints_G γ₁ γ₂)

/-- **Georgii (7.19)**: `|ex 𝒢(γ¹ × γ²)| = |ex 𝒢(γ¹)| |ex 𝒢(γ²)|`, the number of phases of a
product specification. Iterating this over the potentials of Section 6.1 produces specifications
whose number of phases is any prescribed power of two. -/
theorem card_extremePoints_G_prod [Countable S₁] [Countable S₂] :
    Nat.card ((G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞)
      = Nat.card ((G (γ := γ₁)).extremePoints ℝ≥0∞) *
        Nat.card ((G (γ := γ₂)).extremePoints ℝ≥0∞) := by
  rw [← Nat.card_congr (extremePointsGProdEquiv γ₁ γ₂), Nat.card_prod]

/-- **Georgii (7.19)**, the cardinal identity `|ex 𝒢(γ¹ × γ²)| = |ex 𝒢(γ¹)| |ex 𝒢(γ²)|`, with no
finiteness assumption on the number of phases. -/
theorem mk_extremePoints_G_prod [Countable S₁] [Countable S₂] :
    Cardinal.mk ((G (γ := γ₁.prod γ₂)).extremePoints ℝ≥0∞)
      = Cardinal.lift.{max u₂ u₃} (Cardinal.mk ((G (γ := γ₁)).extremePoints ℝ≥0∞)) *
        Cardinal.lift.{max u₁ u₃} (Cardinal.mk ((G (γ := γ₂)).extremePoints ℝ≥0∞)) := by
  rw [← Cardinal.mk_congr (extremePointsGProdEquiv γ₁ γ₂), Cardinal.mk_prod]

end MeasureTheory.GibbsMeasure

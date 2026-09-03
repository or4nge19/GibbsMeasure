/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithDensity
public import GibbsMeasure.Potential.Pair
public import GibbsMeasure.Potential.Summable
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.ProductSpecification

/-!
# Potentials pulled back along a map of the state space, and layered Gibbs measures

A potential on `E^S` may only depend on the configuration through a map `f : E' → E` of the single
spin space; the standard example is a *layered* model, where the spin space is a product
`E₁ × E₂` and the interaction reads only the first layer (`f = Prod.fst`). Georgii's Example
(9.15) is of this shape at `K = 0`.

This file defines the pullback `Potential.comap f Φ`, `(f^*Φ)_A(η) = Φ_A(f ∘ η)`, and — for
`f = Prod.fst` and a **product** a priori measure `ν₁ ⊗ ν₂` — identifies the Gibbsian
specification of `f^*Φ` and its Gibbs measures with those of `Φ`.

## Main definitions

* `Potential.comap f Φ`: the pullback of a potential along `f : E' → E`. It is a potential
  (`Potential.isPotential_comap`, for measurable `f`), summable and absolutely summable whenever
  `Φ` is (`Potential.normAt_comap_le` is the exact estimate `‖f^*Φ‖ᵢ ≤ ‖Φ‖ᵢ`), and its
  Hamiltonians and Boltzmann factors are those of `Φ` read through `f`.

## Main results

* `Specification.map_isssd_prod`: under `(E₁ × E₂)^S ≃ E₁^S × E₂^S`
  (`MeasurableEquiv.arrowProdEquivProdArrow`), the independent specification of `ν₁ ⊗ ν₂` is the
  product `λ¹_Λ(·|η¹) ⊗ λ²_Λ(·|η²)`; `Specification.map_fst_isssd_prod` is its first marginal.
* `Specification.relZ_isssd_prod_boltzmannFactor_comap_fst`: the second layer integrates out of the
  partition function, `Z^{f^*Φ}_Λ(η) = Z^Φ_Λ(η¹)`.
* `Specification.map_gibbsSpecificationOfAbsolutelySummable_comap_fst`: **the Gibbs kernels of a
  layered potential factor**, `γ^{f^*Φ}_Λ(·|η) = γ^Φ_Λ(·|η¹) ⊗ λ²_Λ(·|η²)`; its first marginal is
  `Specification.map_fst_gibbsSpecificationOfAbsolutelySummable_comap_fst`.
* `Specification.isGibbsMeasure_map_symm_prod_comap_fst` and
  `MeasureTheory.GibbsMeasure.mem_G_map_symm_prod_infinitePi_comap_fst`: **the lift**, `μ₁ ⊗ ν₂^S`
  is a Gibbs measure for `f^*Φ` whenever `μ₁` is one for `Φ`; its first-layer marginal is `μ₁`
  (`MeasureTheory.GibbsMeasure.map_fst_map_arrowProdEquivProdArrow_symm_prod`).
* `Specification.isGibbsMeasure_map_fst_comap_fst` and
  `MeasureTheory.GibbsMeasure.mem_G_map_fst_comap_fst`: **the marginal**, the first layer of a
  Gibbs measure for `f^*Φ` is a Gibbs measure for `Φ`.

The two directions together say that `μ ↦ μ¹` maps `𝒢(f^*Φ)` onto `𝒢(Φ)`; it is not injective
(the second layer of `μ` is unconstrained on the tail), which is exactly why the layered model of
Georgii (9.15) has more phases than its first layer.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Potential

variable {S E E' : Type*} [MeasurableSpace E] [MeasurableSpace E'] {f : E' → E}

/-- The pullback `(f^*Φ)_A(η) = Φ_A(f ∘ η)` of a potential along a map `f : E' → E` of the single
spin space: the interaction of the configuration `η` is the interaction of the configuration
`f ∘ η` obtained by reading each spin through `f`. -/
def comap (f : E' → E) (Φ : Potential S E) : Potential S E' := fun A η ↦ Φ A (f ∘ η)

@[simp] lemma comap_apply (f : E' → E) (Φ : Potential S E) (A : Finset S) (η : S → E') :
    Φ.comap f A η = Φ A (f ∘ η) := rfl

variable {Φ : Potential S E}

lemma isPotential_comap (hf : Measurable f) [IsPotential Φ] : IsPotential (Φ.comap f) where
  measurable A := by
    refine Measurable.cylinderEvents_of_dependsOn ?_ fun η ζ h ↦ ?_
    · exact ((IsPotential.measurable (Φ := Φ) A).mono cylinderEvents_le_pi le_rfl).comp
        (measurable_pi_lambda _ fun i ↦ hf.comp (measurable_pi_apply i))
    · exact IsPotential.dependsOn (Φ := Φ) A fun i hi ↦ congrArg f (h i hi)

@[simp] lemma hamiltonianTerms_comap (f : E' → E) (Φ : Potential S E) (Λ : Finset S) (η : S → E') :
    (Φ.comap f).hamiltonianTerms Λ η = Φ.hamiltonianTerms Λ (f ∘ η) := rfl

@[simp] lemma hamiltonian_comap (f : E' → E) (Φ : Potential S E) (Λ : Finset S) (η : S → E') :
    (Φ.comap f).hamiltonian Λ η = Φ.hamiltonian Λ (f ∘ η) := rfl

instance isSummable_comap (f : E' → E) (Φ : Potential S E) [IsSummable Φ] :
    IsSummable (Φ.comap f) :=
  ⟨fun Λ η ↦ IsSummable.summable (Φ := Φ) Λ (f ∘ η)⟩

/-- Pulling back a pair potential is reading the pair interaction through `f`. -/
lemma comap_pair [LinearOrder S] (f : E' → E) (φ : S → S → E → E → ℝ) :
    (pair φ).comap f = pair fun i j x y ↦ φ i j (f x) (f y) := rfl

@[simp] lemma boltzmannFactor_comap (f : E' → E) (Φ : Potential S E) (β : ℝ) (Λ : Finset S)
    (η : S → E') : (Φ.comap f).boltzmannFactor β Λ η = Φ.boltzmannFactor β Λ (f ∘ η) := rfl

/-- Reading the spins through `f` can only shrink Georgii's norm `‖·‖ᵢ` of (2.12); it preserves it
as soon as `f` is surjective. -/
lemma normAt_comap_le (f : E' → E) (Φ : Potential S E) (i : S) :
    (Φ.comap f).normAt i ≤ Φ.normAt i := by
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h : A ∈ {A : Finset S | i ∈ A}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact iSup_le fun η ↦ le_iSup (fun ζ ↦ ‖Φ A ζ‖ₑ) (f ∘ η)
  · simp [Set.indicator_of_notMem h]

instance isAbsolutelySummable_comap (f : E' → E) (Φ : Potential S E) [IsAbsolutelySummable Φ] :
    IsAbsolutelySummable (Φ.comap f) :=
  ⟨fun i ↦ ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top i) (normAt_comap_le f Φ i)⟩

/-- Reading only the first spin layer is a measurable pullback, so the pullback of an interaction
potential along `Prod.fst` is again an interaction potential. -/
instance isPotential_comap_fst {E₂ : Type*} [MeasurableSpace E₂] (Φ : Potential S E)
    [IsPotential Φ] : IsPotential (Φ.comap (Prod.fst : E × E₂ → E)) :=
  isPotential_comap measurable_fst

end Potential

/-! ### The independent specification of a product a priori measure -/

namespace Specification

variable {S E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]

/-- Resampling a finite volume commutes with the identification `(E₁ × E₂)^S ≃ E₁^S × E₂^S`:
juxtaposing on `S` is juxtaposing separately in the two layers. -/
lemma arrowProdEquivProdArrow_comp_juxt (Λ : Finset S) (η : S → E₁ × E₂) :
    ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S) ∘ juxt (Λ : Set S) η
      = Prod.map (juxt (Λ : Set S) fun i ↦ (η i).1) (juxt (Λ : Set S) fun i ↦ (η i).2) ∘
          ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ Λ) := by
  funext ζ
  refine Prod.ext ?_ ?_ <;> funext i <;> by_cases hi : i ∈ (Λ : Set S) <;>
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow, hi]

/-- **The independent specification of a product single-spin distribution is the product of the
independent specifications of the factors.** Under `(E₁ × E₂)^S ≃ E₁^S × E₂^S`,
`λ_Λ(·|η) = λ¹_Λ(·|η¹) ⊗ λ²_Λ(·|η²)`. -/
theorem map_isssd_prod (ν₁ : Measure E₁) (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (Λ : Finset S) (η : S → E₁ × E₂) :
    (isssd (ν₁.prod ν₂) Λ η).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S)
      = (isssd ν₁ Λ fun i ↦ (η i).1).prod (isssd ν₂ Λ fun i ↦ (η i).2) := by
  have hpi := (measurePreserving_arrowProdEquivProdArrow E₁ E₂ Λ
    (fun _ ↦ ν₁) (fun _ ↦ ν₂)).map_eq
  calc (isssd (ν₁.prod ν₂) Λ η).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S)
      = ((Measure.pi fun _ : Λ ↦ ν₁.prod ν₂).map (juxt (Λ : Set S) η)).map
          (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S) := rfl
    _ = (Measure.pi fun _ : Λ ↦ ν₁.prod ν₂).map
          (⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S) ∘ juxt (Λ : Set S) η) :=
        Measure.map_map (MeasurableEquiv.measurable _) Measurable.juxt
    _ = (Measure.pi fun _ : Λ ↦ ν₁.prod ν₂).map
          (Prod.map (juxt (Λ : Set S) fun i ↦ (η i).1) (juxt (Λ : Set S) fun i ↦ (η i).2) ∘
            ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ Λ)) := by
        rw [arrowProdEquivProdArrow_comp_juxt]
    _ = ((Measure.pi fun _ : Λ ↦ ν₁).prod (Measure.pi fun _ : Λ ↦ ν₂)).map
          (Prod.map (juxt (Λ : Set S) fun i ↦ (η i).1)
            (juxt (Λ : Set S) fun i ↦ (η i).2)) := by
        rw [← Measure.map_map (Measurable.juxt.prodMap Measurable.juxt)
          (MeasurableEquiv.measurable _), hpi]
    _ = (isssd ν₁ Λ fun i ↦ (η i).1).prod (isssd ν₂ Λ fun i ↦ (η i).2) :=
        (Measure.map_prod_map _ _ Measurable.juxt Measurable.juxt).symm

end Specification

/-! ### The Gibbsian specification of a pulled-back potential -/

namespace Specification

variable {S E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]

/-- The first-layer marginal of the independent specification of `ν₁ ⊗ ν₂` is the independent
specification of `ν₁`. -/
theorem map_fst_isssd_prod (ν₁ : Measure E₁) (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (Λ : Finset S) (η : S → E₁ × E₂) :
    (isssd (ν₁.prod ν₂) Λ η).map (fun ω i ↦ (ω i).1) = isssd ν₁ Λ fun i ↦ (η i).1 := by
  have h : (fun ω : S → E₁ × E₂ ↦ fun i ↦ (ω i).1)
      = Prod.fst ∘ ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S) := rfl
  rw [h, ← Measure.map_map measurable_fst (MeasurableEquiv.measurable _),
    map_isssd_prod ν₁ ν₂ Λ η]
  exact Measure.fst_prod (μ := isssd ν₁ Λ fun i ↦ (η i).1)
    (ν := isssd ν₂ Λ fun i ↦ (η i).2)

open Potential

variable (Φ : Potential S E₁) [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- The partition function of a pulled-back potential over `ν₁ ⊗ ν₂` is the partition function of
the potential over `ν₁` at the first-layer boundary condition: the second layer integrates out. -/
theorem relZ_isssd_prod_boltzmannFactor_comap_fst [Countable S] (ν₁ : Measure E₁)
    (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) (Λ : Finset S)
    (η : S → E₁ × E₂) :
    relZ (isssd (ν₁.prod ν₂)) ((Φ.comap (Prod.fst : E₁ × E₂ → E₁)).boltzmannFactor β) Λ η
      = relZ (isssd ν₁) (Φ.boltzmannFactor β) Λ fun i ↦ (η i).1 := by
  rw [relZ, relZ, ← map_fst_isssd_prod ν₁ ν₂ Λ η,
    lintegral_map (measurable_boltzmannFactor (Φ := Φ) β Λ)
      (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).fst)]
  rfl

/-- **The Gibbs kernels of a potential that reads only the first spin layer.** Under the
identification `(E₁ × E₂)^S ≃ E₁^S × E₂^S` and for a product a priori measure `ν₁ ⊗ ν₂`,
`γ^{f^*Φ}_Λ(·|η) = γ^Φ_Λ(·|η¹) ⊗ λ²_Λ(·|η²)`: the first layer is Gibbsian for `Φ` and the second
layer is resampled independently. -/
theorem map_gibbsSpecificationOfAbsolutelySummable_comap_fst [Countable S] (ν₁ : Measure E₁)
    (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) (Λ : Finset S)
    (η : S → E₁ × E₂) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
        (ν₁.prod ν₂) β Λ η).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S)
      = (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β Λ fun i ↦ (η i).1).prod
          (isssd ν₂ Λ fun i ↦ (η i).2) := by
  have hdens : (premodifierNorm (S := S) (ν₁.prod ν₂)
        ((Φ.comap (Prod.fst : E₁ × E₂ → E₁)).boltzmannFactor β) Λ) ∘
        ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S).symm
      = fun p ↦ premodifierNorm (S := S) ν₁ (Φ.boltzmannFactor β) Λ p.1 := by
    funext p
    rw [Function.comp_apply, premodifierNorm, premodifierNorm, relNorm, relNorm,
      relZ_isssd_prod_boltzmannFactor_comap_fst Φ ν₁ ν₂ β Λ _]
    rfl
  rw [gibbsSpecificationOfAbsolutelySummable, gibbsSpecificationOfAbsolutelySummable,
    modification_apply, modification_apply, MeasurableEquiv.map_withDensity, hdens,
    map_isssd_prod ν₁ ν₂ Λ η,
    ← prod_withDensity_left (measurable_relNorm (γ := isssd ν₁) (ρ := Φ.boltzmannFactor β)
      (fun Λ' ↦ measurable_boltzmannFactor (Φ := Φ) β Λ') Λ)]

end Specification

/-! ### Gibbs measures of a layered model -/

namespace Specification

variable {S E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]

open Potential

variable (Φ : Potential S E₁) [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- **Lifting a Gibbs measure along the layering.** If the potential reads only the first spin
layer and the a priori measure is a product `ν₁ ⊗ ν₂`, then the product of a Gibbs measure `μ₁`
for `Φ` with an independent second layer `μ₂ ∈ 𝒢(λ²)` is a Gibbs measure for the pullback. -/
theorem isGibbsMeasure_map_symm_prod_comap_fst [Countable S] (ν₁ : Measure E₁) (ν₂ : Measure E₂)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ)
    {μ₁ : Measure (S → E₁)} {μ₂ : Measure (S → E₂)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (hμ₁ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β).IsGibbsMeasure μ₁)
    (hμ₂ : (isssd (S := S) ν₂).IsGibbsMeasure μ₂) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
        (ν₁.prod ν₂) β).IsGibbsMeasure
      ((μ₁.prod μ₂).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S).symm) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S with he
  set γ₁ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β with hγ₁
  set γ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
    (ν₁.prod ν₂) β with hγ
  have hb₁ := (isGibbsMeasure_iff_forall_bind_eq (γ := γ₁) (μ := μ₁)).1 hμ₁
  have hb₂ := (isGibbsMeasure_iff_forall_bind_eq (γ := isssd (S := S) ν₂) (μ := μ₂)).1 hμ₂
  have : IsProbabilityMeasure ((μ₁.prod μ₂).map e.symm) :=
    Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable
  rw [isGibbsMeasure_iff_forall_bind_eq]
  intro Λ
  set κ₁ : Kernel (S → E₁) (S → E₁) :=
    (γ₁ Λ).comap id (measurable_id'' cylinderEvents_le_pi) with hκ₁
  set κ₂ : Kernel (S → E₂) (S → E₂) :=
    (isssd (S := S) ν₂ Λ).comap id (measurable_id'' cylinderEvents_le_pi) with hκ₂
  have hc₁ : ∀ x : S → E₁, κ₁ x = γ₁ Λ x := fun x ↦ by rw [hκ₁]; exact Kernel.comap_apply _ _ _
  have hc₂ : ∀ x : S → E₂, κ₂ x = isssd (S := S) ν₂ Λ x := fun x ↦ by
    rw [hκ₂]; exact Kernel.comap_apply _ _ _
  have hmeasγ : Measurable ⇑(γ Λ) := (γ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  have hker : ∀ p : (S → E₁) × (S → E₂),
      γ Λ (e.symm p) = ((γ₁ Λ p.1).prod (isssd (S := S) ν₂ Λ p.2)).map e.symm := fun p ↦ by
    have h : (γ Λ (e.symm p)).map e = (γ₁ Λ p.1).prod (isssd (S := S) ν₂ Λ p.2) :=
      map_gibbsSpecificationOfAbsolutelySummable_comap_fst Φ ν₁ ν₂ β Λ (e.symm p)
    rw [← h, MeasurableEquiv.map_symm_map]
  calc ((μ₁.prod μ₂).map e.symm).bind (γ Λ)
      = (μ₁.prod μ₂).bind (⇑(γ Λ) ∘ ⇑e.symm) :=
        Measure.bind_map (MeasurableEquiv.measurable _) hmeasγ
    _ = (μ₁.prod μ₂).bind (fun p ↦ ((κ₁ p.1).prod (κ₂ p.2)).map e.symm) := by
        refine Measure.bind_congr_right (.of_forall fun p ↦ ?_)
        change γ Λ (e.symm p) = ((κ₁ p.1).prod (κ₂ p.2)).map e.symm
        rw [hc₁, hc₂]
        exact hker p
    _ = ((μ₁.prod μ₂).bind (fun p ↦ (κ₁ p.1).prod (κ₂ p.2))).map e.symm := by
        refine (Measure.map_bind ?_ (MeasurableEquiv.measurable _)).symm
        have hmp : (fun p : (S → E₁) × (S → E₂) ↦ (κ₁ p.1).prod (κ₂ p.2)) = ⇑(κ₁ ∥ₖ κ₂) :=
          funext fun p ↦ (Kernel.parallelComp_apply κ₁ κ₂ p).symm
        rw [hmp]
        exact (κ₁ ∥ₖ κ₂).measurable
    _ = ((μ₁.bind κ₁).prod (μ₂.bind κ₂)).map e.symm := by
        rw [Measure.bind_prod_parallelComp]
    _ = (μ₁.prod μ₂).map e.symm := by
        rw [show ⇑κ₁ = ⇑(γ₁ Λ) from funext hc₁,
          show ⇑κ₂ = ⇑(isssd (S := S) ν₂ Λ) from funext hc₂, hb₁ Λ, hb₂ Λ]

/-- The first-layer marginal of the Gibbs kernel of a pulled-back potential is the Gibbs kernel of
the potential itself. -/
theorem map_fst_gibbsSpecificationOfAbsolutelySummable_comap_fst [Countable S] (ν₁ : Measure E₁)
    (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) (Λ : Finset S)
    (η : S → E₁ × E₂) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
        (ν₁.prod ν₂) β Λ η).map (fun ω i ↦ (ω i).1)
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β Λ fun i ↦ (η i).1 := by
  have h : (fun ω : S → E₁ × E₂ ↦ fun i ↦ (ω i).1)
      = Prod.fst ∘ ⇑(MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S) := rfl
  rw [h, ← Measure.map_map measurable_fst (MeasurableEquiv.measurable _),
    map_gibbsSpecificationOfAbsolutelySummable_comap_fst Φ ν₁ ν₂ β Λ η]
  exact Measure.fst_prod
    (μ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β Λ fun i ↦ (η i).1)
    (ν := isssd ν₂ Λ fun i ↦ (η i).2)

/-- **The first-layer marginal of a Gibbs measure of the layered model.** If the potential reads
only the first spin layer and the a priori measure is a product, the image of a Gibbs measure
under `ω ↦ (ω_·)₁` is a Gibbs measure for the potential itself. -/
theorem isGibbsMeasure_map_fst_comap_fst [Countable S] (ν₁ : Measure E₁) (ν₂ : Measure E₂)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) {μ : Measure (S → E₁ × E₂)}
    [IsProbabilityMeasure μ]
    (hμ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
      (ν₁.prod ν₂) β).IsGibbsMeasure μ) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β).IsGibbsMeasure
      (μ.map fun ω i ↦ (ω i).1) := by
  set γ₁ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β with hγ₁
  set γ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁))
    (ν₁.prod ν₂) β with hγ
  have hb := (isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ)).1 hμ
  have hq : Measurable (fun ω : S → E₁ × E₂ ↦ fun i ↦ (ω i).1) :=
    measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).fst
  have : IsProbabilityMeasure (μ.map fun ω i ↦ (ω i).1) :=
    Measure.isProbabilityMeasure_map hq.aemeasurable
  rw [isGibbsMeasure_iff_forall_bind_eq]
  intro Λ
  have hmeasγ : Measurable ⇑(γ Λ) := (γ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  have hmeasγ₁ : Measurable ⇑(γ₁ Λ) := (γ₁ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  calc (μ.map fun ω i ↦ (ω i).1).bind (γ₁ Λ)
      = μ.bind (⇑(γ₁ Λ) ∘ fun ω i ↦ (ω i).1) := Measure.bind_map hq hmeasγ₁
    _ = μ.bind (fun ω ↦ (γ Λ ω).map fun ω i ↦ (ω i).1) :=
        Measure.bind_congr_right (.of_forall fun ω ↦
          (map_fst_gibbsSpecificationOfAbsolutelySummable_comap_fst Φ ν₁ ν₂ β Λ ω).symm)
    _ = (μ.bind (γ Λ)).map fun ω i ↦ (ω i).1 := (Measure.map_bind hmeasγ hq).symm
    _ = μ.map fun ω i ↦ (ω i).1 := by rw [hb Λ]

end Specification

namespace MeasureTheory.GibbsMeasure

open Potential Specification

variable {S E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
  (Φ : Potential S E₁) [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- The first layer of the layered configuration `ω ↦ ((ω_·)₁, (ω_·)₂)` recovers the first
factor. -/
lemma map_fst_map_arrowProdEquivProdArrow_symm_prod (μ₁ : Measure (S → E₁))
    (μ₂ : Measure (S → E₂)) [SFinite μ₁] [IsProbabilityMeasure μ₂] :
    ((μ₁.prod μ₂).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S).symm).map
        (fun ω i ↦ (ω i).1) = μ₁ := by
  rw [Measure.map_map (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).fst)
    (MeasurableEquiv.measurable _)]
  exact Measure.fst_prod (μ := μ₁) (ν := μ₂)

/-- **Lifting a Gibbs measure along the layering, `𝒢`-level.** -/
theorem mem_G_map_symm_prod_comap_fst [Countable S] (ν₁ : Measure E₁) (ν₂ : Measure E₂)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) {μ₁ : Measure (S → E₁)}
    {μ₂ : Measure (S → E₂)}
    (hμ₁ : μ₁ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β))
    (hμ₂ : μ₂ ∈ G (isssd (S := S) ν₂)) :
    (μ₁.prod μ₂).map (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S).symm
      ∈ G (gibbsSpecificationOfAbsolutelySummable
          (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁)) (ν₁.prod ν₂) β) := by
  have h₁ := hμ₁.1
  have h₂ := hμ₂.1
  exact ⟨Measure.isProbabilityMeasure_map (MeasurableEquiv.measurable _).aemeasurable,
    isGibbsMeasure_map_symm_prod_comap_fst Φ ν₁ ν₂ β hμ₁.2 hμ₂.2⟩

/-- **Lifting a Gibbs measure along the layering, with the free second layer `ν₂^S`.** Georgii's
`𝒢(Φ) ≠ ∅` transfers from the first layer to the layered model: `μ₁ ⊗ ν₂^S ∈ 𝒢(f^*Φ)`, and its
first-layer marginal is `μ₁` (`map_fst_map_arrowProdEquivProdArrow_symm_prod`). -/
theorem mem_G_map_symm_prod_infinitePi_comap_fst [Countable S] (ν₁ : Measure E₁)
    (ν₂ : Measure E₂) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ)
    {μ₁ : Measure (S → E₁)}
    (hμ₁ : μ₁ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β)) :
    (μ₁.prod (Measure.infinitePi fun _ : S ↦ ν₂)).map
        (MeasurableEquiv.arrowProdEquivProdArrow E₁ E₂ S).symm
      ∈ G (gibbsSpecificationOfAbsolutelySummable
          (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁)) (ν₁.prod ν₂) β) :=
  mem_G_map_symm_prod_comap_fst Φ ν₁ ν₂ β hμ₁
    ⟨inferInstance, Specification.isGibbsMeasure_isssd_infinitePi ν₂⟩

/-- **The first-layer marginal of a Gibbs measure of the layered model, `𝒢`-level.** -/
theorem mem_G_map_fst_comap_fst [Countable S] (ν₁ : Measure E₁) (ν₂ : Measure E₂)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] (β : ℝ) {μ : Measure (S → E₁ × E₂)}
    (hμ : μ ∈ G (gibbsSpecificationOfAbsolutelySummable
      (Φ := Φ.comap (Prod.fst : E₁ × E₂ → E₁)) (ν₁.prod ν₂) β)) :
    (μ.map fun ω i ↦ (ω i).1) ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν₁ β) := by
  have h := hμ.1
  exact ⟨Measure.isProbabilityMeasure_map
      (measurable_pi_lambda _ fun i ↦ (measurable_pi_apply i).fst).aemeasurable,
    isGibbsMeasure_map_fst_comap_fst Φ ν₁ ν₂ β hμ.2⟩

end MeasureTheory.GibbsMeasure

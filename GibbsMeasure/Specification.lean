/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import GibbsMeasure.Prereqs.CylinderEvents
public import GibbsMeasure.Prereqs.Filtration.Consistent
public import GibbsMeasure.Prereqs.Juxt
public import GibbsMeasure.Prereqs.MeasureExt
public import GibbsMeasure.Prereqs.Kernel.CondExp
public import GibbsMeasure.Mathlib.Probability.Kernel.Proper
public import GibbsMeasure.Prereqs.SquareCylinders
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.ProductMeasure

/-!
# Gibbs measures

This file develops specifications in the sense of Georgii, Definition (1.23), the Gibbs measures
they specify, and the λ-specification machinery of Georgii §1.3.

## Main definitions

* `Specification`: a consistent family of proper probability kernels, Georgii (1.23).
* `Specification.IsGibbsMeasure`: `μ ∈ 𝒢(γ)`, i.e. every `γ Λ` is a conditional expectation
  kernel for `μ`.
* `Specification.isssd`: the independent specification with single-spin distribution `ν`,
  Georgii, Remark (1.25).
* `Specification.juxtMapKernel` and `Specification.sigmaFiniteLambdaFun`: the reference kernels
  `λ_Λ(· | η) = λ^Λ × δ_{η_{S∖Λ}}` of Georgii, Notation (1.26), the latter for σ-finite `λ`.
* `Specification.IsModifier` and `Specification.modification`: modifiers and the specification
  `ρ γ` they produce, generalizing Georgii's λ-modifications, Definition (1.27), to an arbitrary
  base specification.
* `Specification.IsPremodifier`: pre-modifications, Georgii, Definition (1.31).
* `Specification.premodifierZ`, `Specification.premodifierNorm`, `Specification.relZ` and
  `Specification.relNorm`: the partition function `λ_Λ h_Λ` and the normalized density
  `h_Λ / λ_Λ h_Λ`, over `isssd` and over an arbitrary reference specification.
* `Specification.IsResampling`: the shape of Georgii's `λ_Λ` -- resample `Λ`, freeze the exterior.

## Main results

* `Specification.isGibbsMeasure_iff_forall_bind_eq` and
  `Specification.isGibbsMeasure_iff_frequently_bind_eq`: Georgii, Remark (1.24), (a) ↔ (b) ↔ (c).
* `Specification.isGibbsMeasure_isssd_iff`: `𝒢(λ_·) = {λ^S}`, Georgii, Remark (1.25).
* `Specification.isModifier_iff_ae_eq` and `Specification.isModifier_iff_ae_comm`: Georgii,
  Proposition (1.30), (a) ↔ (b) ↔ (c).
* `Specification.IsPremodifier.isModifier_relNorm`: Georgii, Remark (1.32) -- normalizing a
  pre-modification against a resampling reference gives a modification.
-/

@[expose] public section

-- Lean 4.34's module system does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`)
-- during `isDefEq`. Several existing proofs rely on that unfolding.
set_option backward.isDefEq.respectTransparency false

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

variable {S E : Type*} {mE : MeasurableSpace E} {Λ₁ Λ₂ : Finset S}

/-- A family of boundary-condition kernels is consistent if
`γ Λ₁ ∘ₖ γ Λ₂ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.

This is Georgii's condition `γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ`, written in Mathlib's kernel-composition
order and with the harmless `comap` needed because the source σ-algebras are nested boundary
σ-algebras. -/
def IsConsistent (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂

/-- A family of boundary-condition kernels is *strongly consistent* if `γ Λ₁ ∘ₖ γ Λ₂ = γ (Λ₁ ∪ Λ₂)`
for all `Λ₁, Λ₂`, i.e. `Λ ↦ γ Λ` is a join-semilattice homomorphism into the kernels under
composition.

This is Georgii's identity `λ_Δ λ_Λ = λ_{Δ ∪ Λ}` (1.25). It implies `IsConsistent` and is strictly
stronger. -/
def IsStronglyConsistent [DecidableEq S]
    (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ Λ₁ Λ₂ : Finset S, (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ =
    (γ (Λ₁ ∪ Λ₂)).comap id
      (measurable_id'' <| by
        gcongr
        exact Finset.subset_union_right)

/-- Strong consistency implies consistency. -/
lemma IsStronglyConsistent.isConsistent [DecidableEq S]
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    (hγ : IsStronglyConsistent γ) : IsConsistent γ := by
  intro Λ₁ Λ₂ hΛ
  rw [hγ Λ₁ Λ₂]
  ext a s _
  simp only [Kernel.comap_apply, id_eq]
  rw [Finset.union_eq_right.2 hΛ]

/-- Georgii (1.26): `γ Λ₁ ∘ₖ γ Λ₂ = γ (Λ₁ ∪ Λ₂)` for *disjoint* volumes. This is what Georgii's
Proposition (1.30) (b) ↔ (c) uses. -/
def IsDisjointlyConsistent [DecidableEq S]
    (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂ : Finset S⦄, Disjoint Λ₁ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ =
    (γ (Λ₁ ∪ Λ₂)).comap id
      (measurable_id'' <| by
        gcongr
        exact Finset.subset_union_right)

lemma IsStronglyConsistent.isDisjointlyConsistent [DecidableEq S]
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    (hγ : IsStronglyConsistent γ) : IsDisjointlyConsistent γ := fun Λ₁ Λ₂ _ ↦ hγ Λ₁ Λ₂

/-- Disjoint consistency, evaluated at a boundary condition. -/
lemma IsDisjointlyConsistent.bind_eq [DecidableEq S]
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    (hγ : IsDisjointlyConsistent γ) {Λ₁ Λ₂ : Finset S} (h : Disjoint Λ₁ Λ₂) (η : S → E) :
    (γ Λ₂ η).bind (γ Λ₁) = γ (Λ₁ ∪ Λ₂) η := by
  simpa [Kernel.comp_apply, Kernel.comap_apply] using DFunLike.congr_fun (hγ h) η

/-- Strong consistency, evaluated at a boundary condition. -/
lemma IsStronglyConsistent.bind_eq [DecidableEq S]
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    (hγ : IsStronglyConsistent γ) (Λ₁ Λ₂ : Finset S) (η : S → E) :
    (γ Λ₂ η).bind (γ Λ₁) = γ (Λ₁ ∪ Λ₂) η := by
  have := DFunLike.congr_fun (hγ Λ₁ Λ₂) η
  simpa [Kernel.comp_apply, Kernel.comap_apply] using this

lemma isConsistentKernel_cylinderEventsCompl
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)} :
    Filtration.cylinderEventsCompl.IsConsistentKernel (fun Λ ↦ γ (OrderDual.ofDual Λ)) ↔
      IsConsistent γ := forall_comm

variable (S E) in
/-- A raw family of boundary-condition kernels, before imposing the proper/probability-kernel
requirements in Georgii's definition of a specification.

This lower-level object is useful for constructing specifications by density changes. The public
`Specification` structure below bundles the extra hypotheses required by Georgii: proper Markov
kernels. We index by all `Finset S`; the empty volume is a totalized endpoint of Georgii's nonempty
finite-volume directed set. -/
structure PreSpecification [MeasurableSpace E] where
  /-- The boundary condition kernels of a specification.

  DO NOT USE. Instead use the coercion to function `⇑γ`. Lean should insert it automatically in
  most cases. -/
  toFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
  /-- The boundary condition kernels of a specification are consistent.

  DO NOT USE. Instead use `PreSpecification.isConsistent`. -/
  isConsistent' : IsConsistent toFun

namespace PreSpecification

instance instDFunLike :
    DFunLike (PreSpecification S E) (Finset S)
      fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E) where
  coe := toFun
  coe_injective γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

/-- The boundary condition kernels of a raw specification are consistent. -/
lemma isConsistent (γ : PreSpecification S E) : IsConsistent γ := γ.isConsistent'

initialize_simps_projections PreSpecification (toFun → apply)

variable {γ γ₁ γ₂ : PreSpecification S E} {Λ Λ₁ Λ₂ : Finset S}

@[ext] lemma ext : (∀ Λ, γ₁ Λ = γ₂ Λ) → γ₁ = γ₂ := DFunLike.ext _ _

protected lemma bind (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) : (γ Λ₂ η).bind (γ Λ₁) = γ Λ₂ η :=
  DFunLike.congr_fun (γ.isConsistent hΛ) η

end PreSpecification

variable (S E) in
/-- A specification in Georgii's sense: a consistent family of proper probability kernels from the
outside-volume σ-algebra to the full configuration σ-algebra. -/
structure Specification [MeasurableSpace E] extends PreSpecification S E where
  /-- Each finite-volume kernel is a probability kernel. -/
  isMarkovKernel' : ∀ Λ, IsMarkovKernel (toPreSpecification Λ)
  /-- Each finite-volume kernel is proper with respect to its boundary σ-algebra. -/
  isProper' : ∀ Λ, (toPreSpecification Λ).IsProper

namespace Specification

instance instDFunLike :
    DFunLike (Specification S E) (Finset S) fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
    where
  coe γ := γ.toPreSpecification
  coe_injective γ₁ γ₂ h := by
    have hpre : γ₁.toPreSpecification = γ₂.toPreSpecification :=
      PreSpecification.ext fun Λ => congrFun h Λ
    cases γ₁
    cases γ₂
    cases hpre
    congr

/-- The boundary condition kernels of a specification are consistent. -/
lemma isConsistent (γ : Specification S E) : IsConsistent γ := γ.toPreSpecification.isConsistent

initialize_simps_projections Specification (toPreSpecification_toFun → apply)

variable {γ γ₁ γ₂ : Specification S E} {Λ Λ₁ Λ₂ : Finset S}

@[ext] lemma ext : (∀ Λ, γ₁ Λ = γ₂ Λ) → γ₁ = γ₂ := DFunLike.ext _ _

protected lemma bind (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) : (γ Λ₂ η).bind (γ Λ₁) = γ Λ₂ η :=
  DFunLike.congr_fun (γ.isConsistent hΛ) η

instance instIsMarkovKernel (γ : Specification S E) {Λ : Finset S} : IsMarkovKernel (γ Λ) :=
  γ.isMarkovKernel' Λ

section IsProper

/-- A specification is proper if all its boundary condition kernels are. -/
def IsProper (γ : Specification S E) : Prop := ∀ Λ : Finset S, (γ Λ).IsProper

/-- Specifications are proper by definition. -/
lemma isProper (γ : Specification S E) : γ.IsProper := γ.isProper'

lemma isProper_iff_restrict_eq_indicator_smul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃B : Set (S → E)⦄ (hB : MeasurableSet[cylinderEvents Λᶜ] B) (x : S → E),
      (γ Λ).restrict (cylinderEvents_le_pi _ hB) x = B.indicator (1 : (S → E) → ℝ≥0∞) x • γ Λ x :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_restrict_eq_indicator_smul _

lemma isProper_iff_inter_eq_indicator_mul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄ (_hA : MeasurableSet A) ⦃B : Set (S → E)⦄
        (_hB : MeasurableSet[cylinderEvents Λᶜ] B) (η : S → E),
      γ Λ η (A ∩ B) = B.indicator 1 η * γ Λ η A :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul

variable {A B : Set (S → E)} {f g : (S → E) → ℝ≥0∞} {η₀ : S → E}

lemma setLIntegral_eq_indicator_mul_lintegral (γ : Specification S E) (Λ : Finset S)
    (hf : Measurable f) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (γ.isProper Λ).setLIntegral_eq_indicator_mul_lintegral cylinderEvents_le_pi hf hB _

lemma setLIntegral_inter_eq_indicator_mul_setLIntegral (γ : Specification S E) (Λ : Finset S)
    (hf : Measurable f) (hA : MeasurableSet A) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in A ∩ B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x in A, f x ∂(γ Λ η₀) :=
  (γ.isProper Λ).setLIntegral_inter_eq_indicator_mul_setLIntegral cylinderEvents_le_pi hf hA hB _

lemma lintegral_mul (γ : Specification S E) (Λ : Finset S) (hf : Measurable f)
    (hg : Measurable[cylinderEvents Λᶜ] g) :
    ∫⁻ x, g x * f x ∂(γ Λ η₀) = g η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (γ.isProper _).lintegral_mul cylinderEvents_le_pi hf hg _

end IsProper

section IsGibbsMeasure
variable {μ : Measure (S → E)}

/-- For a specification `γ`, a Gibbs measure is a measure whose conditional expectation kernels
conditionally on configurations exterior to finite sets agree with the boundary condition kernels
of the specification `γ`. -/
def IsGibbsMeasure (γ : Specification S E) (μ : Measure (S → E)) : Prop := ∀ Λ, (γ Λ).IsCondExp μ

-- The following two lemmas should generalise to a family of kernels indexed by a filtration.
lemma isGibbsMeasure_iff_forall_bind_eq [IsFiniteMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∀ Λ, μ.bind (γ Λ) = μ :=
  forall_congr' fun Λ ↦ Kernel.isCondExp_iff_bind_eq_left (γ.isProper Λ) cylinderEvents_le_pi

/-!
### Probability-measure restatements

`IsProbabilityMeasure μ` yields `IsFiniteMeasure μ` by instance resolution, so
`Specification.isGibbsMeasure_iff_forall_bind_eq` and
`Specification.isGibbsMeasure_iff_frequently_bind_eq` already apply verbatim to a probability
measure. The `_of_prob` restatements below add no hypothesis, and exist only as the names the
downstream files call.
-/

lemma isGibbsMeasure_iff_forall_bind_eq_of_prob [IsProbabilityMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∀ Λ, μ.bind (γ Λ) = μ := by
  haveI : IsFiniteMeasure μ := by infer_instance
  simpa using (isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ))

lemma isGibbsMeasure_iff_frequently_bind_eq [IsFiniteMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∃ᶠ Λ in .atTop, μ.bind (γ Λ) = μ := by
  rw [isGibbsMeasure_iff_forall_bind_eq]
  refine ⟨Filter.Frequently.of_forall, fun h Λ ↦ ?_⟩
  obtain ⟨Λ', h, hΛ'⟩ := h.forall_exists_of_atTop Λ
  rw [← hΛ', Measure.bind_bind, funext (γ.bind h)] <;>
    exact ((γ _).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable

lemma isGibbsMeasure_iff_frequently_bind_eq_of_prob [IsProbabilityMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∃ᶠ Λ in .atTop, μ.bind (γ Λ) = μ := by
  haveI : IsFiniteMeasure μ := by infer_instance
  simpa using (isGibbsMeasure_iff_frequently_bind_eq (γ := γ) (μ := μ))

end IsGibbsMeasure

noncomputable section ISSSD
variable (ν : Measure E) [IsProbabilityMeasure ν] (η : S → E)

/-- The outside-volume constraint of a finite square cylinder is measurable with respect to the
outside-volume cylinder σ-algebra. -/
lemma measurableSet_forall_mem_not_mem
    (Λ s : Finset S) {t : S → Set E} (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      {η : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i} := by
  classical
  have hset :
      {η : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i} =
        ⋂ i ∈ s, if i ∈ (Λ : Set S) then Set.univ else (fun η : S → E => η i) ⁻¹' t i := by
    ext η
    simp [Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  refine Finset.measurableSet_biInter s (fun i hi => ?_)
  by_cases hiΛ : i ∈ (Λ : Set S)
  · simp [hiΛ]
  · have hiΛc : i ∈ (Λ : Set S)ᶜ := by simpa [Set.mem_compl_iff] using hiΛ
    have hproj : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
        (fun η : S → E => η i) :=
      measurable_cylinderEvent_apply (i := i) (X := fun _ : S ↦ E) hiΛc
    simpa [hiΛ] using (ht i).preimage hproj

/-- If the boundary satisfies all outside-volume constraints, the pullback of a square cylinder
under `juxt` is the corresponding finite-coordinate box. -/
lemma preimage_juxt_squareCylinder_eq_univ_pi_of_forall
    [DecidableEq S] {Λ s : Finset S} {t : S → Set E} {η : S → E}
    (hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) :
    (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) =
      Set.univ.pi (fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
  ext ζ
  constructor
  · intro hζ
    have hcond : ∀ i, i ∈ (s : Set S) → juxt (Λ : Set S) η ζ i ∈ t i := by
      simpa [Set.mem_preimage, Set.mem_pi] using hζ
    refine Set.mem_univ_pi.2 (fun j => ?_)
    by_cases hjs : (j : S) ∈ (s : Set S)
    · have : juxt (Λ : Set S) η ζ (j : S) ∈ t (j : S) := hcond (j : S) hjs
      simpa [hjs, juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) j.property]
        using this
    · simp [hjs]
  · intro hζ
    have hζ' : ∀ j : Λ, ζ j ∈ (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
      simpa [Set.mem_univ_pi] using hζ
    refine Set.mem_pi.2 (fun i hi => ?_)
    by_cases hiΛ : i ∈ (Λ : Set S)
    · let j : Λ := ⟨i, hiΛ⟩
      have hjs : (j : S) ∈ (s : Set S) := by simpa using hi
      simpa [j, hjs, juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hiΛ]
        using hζ' j
    · simpa [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hiΛ]
        using hP i hi hiΛ

/-- If the boundary violates an outside-volume constraint, the pullback of a square cylinder under
`juxt` is empty. -/
lemma preimage_juxt_squareCylinder_eq_empty_of_not_forall
    {Λ s : Finset S} {t : S → Set E} {η : S → E}
    (hP : ¬ ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) :
    (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) = (∅ : Set (Λ → E)) := by
  ext ζ
  constructor
  · intro hζ
    simp only [not_forall] at hP
    rcases hP with ⟨i, hi_s, hi_Λ, hi_not⟩
    have hcond : ∀ j, j ∈ (s : Set S) → juxt (Λ : Set S) η ζ j ∈ t j := by
      simpa [Set.mem_preimage, Set.mem_pi] using hζ
    have : η i ∈ t i := by
      simpa [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η) (ζ := ζ) hi_Λ]
        using hcond i hi_s
    exact (hi_not this).elim
  · intro hζ
    simp at hζ

/-- Raw evaluation of a `juxt`-mapped finite-coordinate measure on a finite square cylinder. -/
lemma map_juxt_apply_squareCylinder_of_measure
    [DecidableEq S] {Λ s : Finset S} (μΛ : Measure (Λ → E)) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    (Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ) ((s : Set S).pi t) =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i)
          (μΛ (Set.univ.pi (fun j : Λ =>
            if (j : S) ∈ (s : Set S) then t j else Set.univ)))
          0) := by
  classical
  have hmeas_rect : MeasurableSet ((s : Set S).pi t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)) hmeas_rect]
  by_cases hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  · rw [preimage_juxt_squareCylinder_eq_univ_pi_of_forall (S := S) (E := E) hP]
    rw [if_pos hP]
    rfl
  · rw [preimage_juxt_squareCylinder_eq_empty_of_not_forall (S := S) (E := E) hP]
    have hP' : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := by
      intro h
      exact hP (fun i hi hiΛ => h i (by simpa using hi) (by simpa using hiΛ))
    simp [hP']
    exact measure_empty

omit [IsProbabilityMeasure ν] in
/-- Raw evaluation of a `juxt`-mapped product measure on a finite square cylinder. -/
lemma map_juxt_apply_squareCylinder
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    (Measure.map (juxt (Λ := (Λ : Set S)) η) (Measure.pi fun _ : Λ ↦ ν))
        ((s : Set S).pi t) =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i)
          ((Measure.pi fun _ : Λ ↦ ν)
            (Set.univ.pi (fun j : Λ =>
              if (j : S) ∈ (s : Set S) then t j else Set.univ)))
          0) := by
  exact map_juxt_apply_squareCylinder_of_measure
    (S := S) (E := E) (Λ := Λ) (s := s) (Measure.pi fun _ : Λ => ν) t ht η

/-- Measurability, as a function of the boundary condition, of a `juxt`-mapped finite-coordinate
measure applied to a finite square cylinder. -/
lemma measurable_map_juxt_apply_squareCylinder_of_measure
    {Λ s : Finset S} (μΛ : Measure (Λ → E)) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      fun η : S → E =>
        (Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ) ((s : Set S).pi t) := by
  classical
  let P : (S → E) → Prop := fun η =>
    ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  let c : ℝ≥0∞ :=
    μΛ (Set.univ.pi (fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ))
  have h_eval :
      (fun η : S → E =>
          (Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ) ((s : Set S).pi t)) =
        fun η => ite (P η) c 0 := by
    funext η
    simpa [P, c] using map_juxt_apply_squareCylinder_of_measure
      (S := S) (E := E) (Λ := Λ) (s := s) μΛ t ht η
  have hP : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ] {η | P η} := by
    simpa [P] using measurableSet_forall_mem_not_mem (S := S) (E := E) Λ s ht
  letI : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ
  haveI : DecidablePred P := fun η => Classical.propDecidable (P η)
  simpa [h_eval] using
    (Measurable.ite (p := P) (hp := by simpa using hP) measurable_const measurable_const)

omit [IsProbabilityMeasure ν] in
/-- Measurability, as a function of the boundary condition, of a `juxt`-mapped product measure
applied to a finite square cylinder. -/
lemma measurable_map_juxt_apply_squareCylinder
    (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      fun η : S → E =>
        (Measure.map (juxt (Λ := (Λ : Set S)) η) (Measure.pi fun _ : Λ ↦ ν))
          ((s : Set S).pi t) := by
  exact measurable_map_juxt_apply_squareCylinder_of_measure
    (S := S) (E := E) (Λ := Λ) (s := s) (Measure.pi fun _ : Λ => ν) t ht

/-- Measurability of a `juxt`-mapped finite-coordinate finite measure as a function of the boundary
condition. -/
lemma measurable_map_juxt_of_isFiniteMeasure
    {Λ : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ] :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      fun η : S → E => Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ := by
  classical
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  let μ' : (S → E) → Measure (S → E) :=
    fun η ↦ Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ
  haveI : ∀ η, IsFiniteMeasure (μ' η) := by
    intro η
    refine ⟨?_⟩
    have hjuxt : Measurable (juxt (Λ := (Λ : Set S)) (η := η)) :=
      Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)
    rw [show μ' η = Measure.map (juxt (Λ := (Λ : Set S)) (η := η)) μΛ by rfl]
    rw [Measure.map_apply hjuxt MeasurableSet.univ]
    simp
  refine (Measurable.measure_of_isPiSystem (μ := μ') (S := C)
    (hgen := hgen) (hpi := hC_pi) ?_ ?_)
  · intro A hA
    rcases hA with ⟨s, t, ht, rfl⟩
    have ht_meas : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    exact measurable_map_juxt_apply_squareCylinder_of_measure
      (S := S) (E := E) (Λ := Λ) (s := s) μΛ t ht_meas
  · have h_eval_univ : (fun η : S → E => μ' η Set.univ) = fun _ => μΛ Set.univ := by
      funext η
      have hjuxt : Measurable (juxt (Λ := (Λ : Set S)) (η := η)) :=
        Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)
      simp [μ', Measure.map_apply hjuxt MeasurableSet.univ]
    rw [h_eval_univ]
    exact measurable_const

/-- Kernel obtained by pushing a finite measure on the finite-coordinate space through `juxt`. -/
@[simps -fullyApplied]
def juxtMapKernel {Λ : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ] :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η => Measure.map (juxt (Λ := (Λ : Set S)) η) μΛ)
    (measurable_map_juxt_of_isFiniteMeasure (S := S) (E := E) (Λ := Λ) μΛ)

/-- Evaluation of `juxtMapKernel` on a finite square cylinder. -/
lemma juxtMapKernel_apply_squareCylinder
    [DecidableEq S] {Λ s : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ]
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    juxtMapKernel (S := S) (E := E) μΛ η ((s : Set S).pi t) =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i)
          (μΛ (Set.univ.pi (fun j : Λ =>
            if (j : S) ∈ (s : Set S) then t j else Set.univ)))
          0) := by
  rw [juxtMapKernel_apply]
  exact map_juxt_apply_squareCylinder_of_measure
    (S := S) (E := E) (Λ := Λ) (s := s) μΛ t ht η

/-- The total mass of `juxtMapKernel` is the mass of its finite-coordinate input measure. -/
lemma juxtMapKernel_apply_univ {Λ : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ]
    (η : S → E) :
    juxtMapKernel (S := S) (E := E) μΛ η Set.univ = μΛ Set.univ := by
  rw [juxtMapKernel_apply]
  rw [Measure.map_apply
    (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)) MeasurableSet.univ]
  simp

instance juxtMapKernel.instIsFiniteKernel
    {Λ : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ] :
    IsFiniteKernel (juxtMapKernel (S := S) (E := E) μΛ) := by
  refine ⟨⟨μΛ Set.univ, measure_lt_top _ _, fun η => ?_⟩⟩
  rw [juxtMapKernel_apply_univ]

/-- The σ-finite reference kernel from Georgii's Notation 1.26, constructed as an s-finite kernel.

For a σ-finite reference measure `ν`, the finite-volume product measure is s-finite. We decompose
that product measure into finite measures and push each finite piece through `juxt`, then sum the
resulting finite kernels. -/
noncomputable def sigmaFiniteLambdaFun (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  Kernel.sum fun n : ℕ =>
    juxtMapKernel (S := S) (E := E) (Λ := Λ) (sfiniteSeq (Measure.pi fun _ : Λ => ν) n)

instance sigmaFiniteLambdaFun.instIsSFiniteKernel
    (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) :
    IsSFiniteKernel (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ) := by
  rw [sigmaFiniteLambdaFun]
  refine ProbabilityTheory.Kernel.isSFiniteKernel_sum_of_denumerable ?_
  intro n
  haveI : IsFiniteKernel
      (juxtMapKernel (S := S) (E := E) (Λ := Λ)
        (sfiniteSeq (Measure.pi fun _ : Λ => ν) n)) := by
    infer_instance
  infer_instance

/-- The s-finite construction of `sigmaFiniteLambdaFun` evaluates to the expected pushed-forward
finite-volume product measure. -/
lemma sigmaFiniteLambdaFun_apply_eq_map
    (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η =
      Measure.map (juxt (Λ := (Λ : Set S)) η) (Measure.pi fun _ : Λ => ν) := by
  let μΛ : Measure (Λ → E) := Measure.pi fun _ : Λ => ν
  let J : (Λ → E) → (S → E) := juxt (Λ := (Λ : Set S)) η
  have hJ : Measurable J := Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)
  calc
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η =
        Measure.sum fun n : ℕ => Measure.map J (sfiniteSeq μΛ n) := by
          rw [sigmaFiniteLambdaFun, Kernel.sum_apply]
          rfl
    _ = Measure.map J (Measure.sum (sfiniteSeq μΛ)) := by
          exact (Measure.map_sum (m := sfiniteSeq μΛ) (f := J) hJ.aemeasurable).symm
    _ = Measure.map J μΛ := by
          rw [sum_sfiniteSeq μΛ]

/-- Evaluation of the σ-finite reference kernel on a finite square cylinder. -/
lemma sigmaFiniteLambdaFun_apply_squareCylinder
    [DecidableEq S] (ν : Measure E) [SigmaFinite ν] (Λ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η ((s : Set S).pi t) =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i)
          ((Measure.pi fun _ : Λ ↦ ν)
            (Set.univ.pi (fun j : Λ =>
              if (j : S) ∈ (s : Set S) then t j else Set.univ)))
          0) := by
  rw [sigmaFiniteLambdaFun_apply_eq_map]
  exact map_juxt_apply_squareCylinder (S := S) (E := E) ν Λ s t ht η

/-- The total mass of the σ-finite reference kernel is the finite-volume product mass of `ν`. -/
lemma sigmaFiniteLambdaFun_apply_univ
    (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η Set.univ =
      (Measure.pi fun _ : Λ ↦ ν) Set.univ := by
  rw [sigmaFiniteLambdaFun_apply_eq_map]
  rw [Measure.map_apply
    (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)) MeasurableSet.univ]
  simp

/-- The finite-reference version of Georgii's `λ_Λ` kernel: `Specification.juxtMapKernel` of the
finite product `ν^Λ`.

This kernel resamples the coordinates in `Λ` using the finite measure `ν` and leaves the exterior
configuration fixed. It is generally not Markov; the probability independent specification
`isssdFun` is the special case where `ν` is a probability measure. -/
abbrev finiteLambdaFun (ν : Measure E) [IsFiniteMeasure ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  juxtMapKernel (S := S) (E := E) (Λ := Λ) (Measure.pi fun _ : Λ => ν)

/-- For finite reference measures, the s-finite λ-kernel agrees with the finite λ-kernel. -/
lemma sigmaFiniteLambdaFun_eq_finiteLambdaFun
    (ν : Measure E) [IsFiniteMeasure ν] (Λ : Finset S) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ =
      finiteLambdaFun (S := S) (E := E) ν Λ := by
  ext η A hA
  rw [sigmaFiniteLambdaFun_apply_eq_map]
  rfl

/-- Auxiliary definition for `Specification.isssd`: the independent resampling kernel with a
probability spin distribution `ν`, i.e. `Specification.juxtMapKernel` of the finite product
`ν^Λ`. -/
abbrev isssdFun (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  juxtMapKernel (S := S) (E := E) (Λ := Λ) (Measure.pi fun _ : Λ ↦ ν)

@[simp] lemma isssdFun_apply (Λ : Finset S) :
    ⇑(isssdFun (S := S) (E := E) ν Λ)
      = fun η : S → E ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν) := rfl

/-- The probability independent kernel is the finite-reference kernel for a probability reference
measure. -/
lemma finiteLambdaFun_eq_isssdFun (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    finiteLambdaFun (S := S) (E := E) ν Λ = isssdFun (S := S) (E := E) ν Λ := rfl

/-!
### Evaluating `isssdFun` on square cylinders

For a measurable rectangle `(s : Set S).pi t`, the ISSSD kernel either gives `0` (if the
boundary condition violates an outside-`Λ` constraint) or a finite product of the single-site
masses `ν (t i)` over the coordinates in `s ∩ Λ`.
-/

/-- Product measure of a coordinate box on a finite subtype, with unconstrained coordinates
contributing mass `1`. -/
lemma measure_pi_univ_pi_if_mem_eq_prod_inter
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E) :
    (Measure.pi fun _ : Λ ↦ ν)
        (Set.univ.pi fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ) =
      ∏ i ∈ s ∩ Λ, ν (t i) := by
  haveI : SigmaFinite ν := by infer_instance
  have hpi :
      (Measure.pi fun _ : Λ ↦ ν)
          (Set.univ.pi fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ) =
        ∏ j : Λ, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
    simp
  have hnu : ν (Set.univ : Set E) = 1 := by simp
  have hattach :
      (∏ j : Λ, ν (if (j : S) ∈ (s : Set S) then t j else Set.univ)) =
        ∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ) := by
    simpa [Finset.univ_eq_attach, Finset.prod_attach, Finset.mem_coe] using
      (Finset.prod_attach (s := Λ) (f := fun i : S => ν (if i ∈ s then t i else Set.univ)))
  have hdrop :
      (∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ)) =
        ∏ i ∈ s ∩ Λ, ν (t i) := by
    have h' :
        (∏ i ∈ Λ, ν (if i ∈ s then t i else Set.univ)) =
          ∏ i ∈ Λ, (if i ∈ s then ν (t i) else 1) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      by_cases his : i ∈ s <;> simp [his, hnu]
    simp [h', Finset.prod_ite_mem, Finset.inter_comm]
  exact hpi.trans (hattach.trans hdrop)

lemma isssdFun_apply_squareCylinder
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ η ((s : Set S).pi t) =
      (by
        classical -- needed
        exact ite (∀ i ∈ s, i ∉ Λ → η i ∈ t i)
          (∏ i ∈ s ∩ Λ, ν (t i)) 0) := by
  rw [isssdFun_apply]
  rw [map_juxt_apply_squareCylinder (S := S) (E := E) ν Λ s t ht η]
  rw [measure_pi_univ_pi_if_mem_eq_prod_inter (S := S) (E := E) ν Λ s t]
  have hP_iff :
      (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) ↔
        ∀ i ∈ s, i ∉ Λ → η i ∈ t i := by
    simp
  by_cases hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  · have hP' : ∀ i ∈ s, i ∉ Λ → η i ∈ t i := hP_iff.mp hP
    rw [if_pos hP, if_pos hP']
  · have hP' : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := fun h => hP (hP_iff.mpr h)
    rw [if_neg hP, if_neg hP']

/-- A square-cylinder event depending only outside `Λ` can be written as a coordinate box with
unconstrained coordinates on `Λ`. -/
lemma setOf_forall_not_mem_eq_pi_if_univ [DecidableEq S]
    (Λ s : Finset S) (t : S → Set E) :
    {ω : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → ω i ∈ t i} =
      ((s : Set S).pi fun i => if i ∈ (Λ : Set S) then Set.univ else t i) := by
  ext ω
  simp [Set.mem_pi]

/-- Measurability of the outside-`Λ` part of a finite square-cylinder event. -/
lemma measurableSet_forall_not_mem
    (Λ s : Finset S) {t : S → Set E} (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet {ω : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → ω i ∈ t i} := by
  classical
  rw [setOf_forall_not_mem_eq_pi_if_univ (S := S) (E := E) Λ s t]
  refine MeasurableSet.pi s.countable_toSet ?_
  intro i hi
  by_cases hiΛ : i ∈ (Λ : Set S)
  · simp [hiΛ]
  · simpa [hiΛ] using ht i

/-- Outside both finite volumes is the same as outside their finite union. -/
lemma forall_mem_not_mem_union_iff
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E) (η : S → E) :
    (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i) ↔
      ∀ i ∈ s, i ∉ Λ₁ → i ∉ Λ₂ → η i ∈ t i := by
  constructor
  · intro h i hi hi1 hi2
    exact h i (by simpa using hi) (fun hiU =>
      (Finset.mem_union.1 hiU).elim hi1 hi2)
  · intro h i hi hiU
    exact h i (by simpa using hi)
      (fun hi1 => hiU (Finset.mem_union.2 (Or.inl hi1)))
      (fun hi2 => hiU (Finset.mem_union.2 (Or.inr hi2)))

/-- Splitting a product over `s ∩ Λ₂` by removing the coordinates already in `Λ₁`. -/
lemma prod_inter_if_mem_eq_prod_inter_sdiff
    [DecidableEq S] {M : Type*} [CommMonoid M] (s Λ₁ Λ₂ : Finset S) (f : S → M) :
    (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then 1 else f i)) =
      ∏ i ∈ s ∩ (Λ₂ \ Λ₁), f i := by
  have hite :
      (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then 1 else f i)) =
        ∏ i ∈ s ∩ Λ₂, (if i ∈ (s ∩ Λ₂) \ Λ₁ then f i else 1) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    by_cases hiΛ1 : i ∈ Λ₁
    · have : i ∉ (s ∩ Λ₂) \ Λ₁ := fun hi' => (Finset.mem_sdiff.1 hi').2 hiΛ1
      simp [hiΛ1, this]
    · have : i ∈ (s ∩ Λ₂) \ Λ₁ := Finset.mem_sdiff.2 ⟨hi, hiΛ1⟩
      simp [hiΛ1, this]
  have hsub : (s ∩ Λ₂) \ Λ₁ ⊆ s ∩ Λ₂ := fun _ hi => (Finset.mem_sdiff.1 hi).1
  calc
    (∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then 1 else f i)) =
        ∏ i ∈ s ∩ Λ₂, (if i ∈ (s ∩ Λ₂) \ Λ₁ then f i else 1) := hite
    _ = ∏ i ∈ (s ∩ Λ₂) ∩ ((s ∩ Λ₂) \ Λ₁), f i := by
          simpa using Finset.prod_ite_mem (s ∩ Λ₂) ((s ∩ Λ₂) \ Λ₁) f
    _ = ∏ i ∈ (s ∩ Λ₂) \ Λ₁, f i := by
          simp [Finset.inter_eq_right.2 hsub]
    _ = ∏ i ∈ s ∩ (Λ₂ \ Λ₁), f i := by
          congr 1
          ext i
          constructor
          · intro hi
            rcases Finset.mem_sdiff.1 hi with ⟨hi12, hi1⟩
            exact Finset.mem_inter.2
              ⟨(Finset.mem_inter.1 hi12).1,
                Finset.mem_sdiff.2 ⟨(Finset.mem_inter.1 hi12).2, hi1⟩⟩
          · intro hi
            rcases Finset.mem_inter.1 hi with ⟨his, hi21⟩
            exact Finset.mem_sdiff.2
              ⟨Finset.mem_inter.2 ⟨his, (Finset.mem_sdiff.1 hi21).1⟩,
                (Finset.mem_sdiff.1 hi21).2⟩

/-- Product decomposition for the disjoint split `Λ₁` and `Λ₂ \ Λ₁` inside `s`. -/
lemma prod_inter_mul_prod_inter_sdiff_eq_prod_inter_union
    [DecidableEq S] {M : Type*} [CommMonoid M] (s Λ₁ Λ₂ : Finset S) (f : S → M) :
    (∏ i ∈ s ∩ Λ₁, f i) * (∏ i ∈ s ∩ (Λ₂ \ Λ₁), f i) =
      ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), f i := by
  have hdisj : Disjoint (s ∩ Λ₁) (s ∩ (Λ₂ \ Λ₁)) := by
    refine Finset.disjoint_left.2 ?_
    intro i hi1 hi2
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hi2).2).2 (Finset.mem_inter.1 hi1).2
  have hunion : (s ∩ Λ₁) ∪ (s ∩ (Λ₂ \ Λ₁)) = s ∩ (Λ₁ ∪ Λ₂) := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.1 hi with hi | hi
      · exact Finset.mem_inter.2
          ⟨(Finset.mem_inter.1 hi).1, Finset.mem_union.2 (Or.inl (Finset.mem_inter.1 hi).2)⟩
      · exact Finset.mem_inter.2
          ⟨(Finset.mem_inter.1 hi).1,
            Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.1 (Finset.mem_inter.1 hi).2).1)⟩
    · intro hi
      rcases Finset.mem_inter.1 hi with ⟨his, hiU⟩
      rcases Finset.mem_union.1 hiU with hi1 | hi2
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨his, hi1⟩))
      · by_cases hi1 : i ∈ Λ₁
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2 ⟨his, hi1⟩))
        · exact Finset.mem_union.2
            (Or.inr (Finset.mem_inter.2 ⟨his, Finset.mem_sdiff.2 ⟨hi2, hi1⟩⟩))
  simpa [hunion] using
    (Finset.prod_union (s₁ := s ∩ Λ₁) (s₂ := s ∩ (Λ₂ \ Λ₁)) (f := f) hdisj).symm

/-- Single-site factors with unconstrained coordinates on `Λ₁` collapse to the coordinates in
`Λ₂ \ Λ₁`. -/
lemma prod_measure_if_mem_univ_eq_prod_inter_sdiff
    [DecidableEq S] (s Λ₁ Λ₂ : Finset S) (t : S → Set E) :
    (∏ i ∈ s ∩ Λ₂, ν (if i ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t i)) =
      ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by
  have hrewrite :
      (∏ i ∈ s ∩ Λ₂, ν (if i ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t i)) =
        ∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν (t i)) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    by_cases hiΛ1 : i ∈ Λ₁
    · simp [hiΛ1]
    · simp [hiΛ1]
  rw [hrewrite]
  exact prod_inter_if_mem_eq_prod_inter_sdiff (s := s) (Λ₁ := Λ₁)
    (Λ₂ := Λ₂) (f := fun i => ν (t i))

/-- Evaluation of `isssdFun` on a finite cylinder that constrains only the sites outside another
finite volume. -/
lemma isssdFun_apply_forall_not_mem
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ₂ η
        {ω : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → ω i ∈ t i} =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
          (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) 0) := by
  classical
  rw [setOf_forall_not_mem_eq_pi_if_univ (S := S) (E := E) Λ₁ s t]
  have hbase := isssdFun_apply_squareCylinder (ν := ν) (mE := mE) Λ₂ s
    (fun i => if i ∈ (Λ₁ : Set S) then Set.univ else t i)
    (fun i => by by_cases hiΛ : i ∈ (Λ₁ : Set S) <;> simp [hiΛ, ht i]) η
  have hpred :
      (∀ i ∈ s, i ∉ Λ₂ → η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) ↔
        ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i := by
    constructor
    · intro h i hi hiU
      have hi1 : i ∉ Λ₁ := fun hi1 => hiU (Finset.mem_union.2 (Or.inl hi1))
      simpa [hi1] using
        h i (by simpa using hi) (fun hi2 => hiU (Finset.mem_union.2 (Or.inr hi2)))
    · intro h i hi hi2
      by_cases hi1 : i ∈ Λ₁
      · simp [hi1]
      · simp [hi1, h i (by simpa using hi)
          (fun hiU => (Finset.mem_union.1 hiU).elim hi1 hi2)]
  have hprod :
      (∏ x ∈ s ∩ Λ₂, ν (if x ∈ Λ₁ then (Set.univ : Set E) else t x)) =
        ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by
    simpa using prod_measure_if_mem_univ_eq_prod_inter_sdiff (ν := ν) s Λ₁ Λ₂ t
  have hprodSet :
      (∏ x ∈ s ∩ Λ₂, ν (if x ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t x)) =
        ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by
    simpa using hprod
  calc
    (isssdFun ν Λ₂ η)
        (((s : Set S).pi fun i => if i ∈ (Λ₁ : Set S) then Set.univ else t i)) =
        ite (∀ i ∈ s, i ∉ Λ₂ → η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i))
          (∏ i ∈ s ∩ Λ₂, ν (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) 0 := hbase
    _ = ite (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
        (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) 0 := by
          by_cases hU :
              ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i
          · have hleft := hpred.mpr hU
            rw [if_pos hleft, if_pos hU, hprodSet]
          · have hleft : ¬
                (∀ i ∈ s, i ∉ Λ₂ →
                  η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) :=
              fun h => hU (hpred.mp h)
            rw [if_neg hleft, if_neg hU]

/-- Integral of a constant on a measurable predicate, written with an `if`. -/
lemma lintegral_ite_const_eq_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (p : α → Prop) [DecidablePred p]
    (hp : MeasurableSet {x | p x}) (c : ℝ≥0∞) :
    ∫⁻ x, (if p x then c else 0) ∂μ = c * μ {x | p x} := by
  have hite : (fun x => if p x then c else 0) = ({x | p x}).indicator (fun _ => c) := by
    funext x
    by_cases hx : p x <;> simp [hx]
  rw [hite]
  exact MeasureTheory.lintegral_indicator_const hp c

/-- Integrating a finite-volume ISSSD square-cylinder evaluation leaves the mass of the outside
constraints under the outer ISSSD kernel. -/
lemma lintegral_isssdFun_apply_squareCylinder
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
      (∏ i ∈ s ∩ Λ₁, ν (t i)) *
        (isssdFun ν Λ₂ η)
          {b : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i} := by
  classical
  let P : (S → E) → Prop := fun b =>
    ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i
  have hp : MeasurableSet {b : S → E | P b} := by
    simpa [P] using
      (measurableSet_forall_not_mem (S := S) (E := E) Λ₁ s (t := t) ht)
  have h_eval :
      (fun b : S → E => isssdFun ν Λ₁ b ((s : Set S).pi t)) =
        fun b => ite (P b) (∏ i ∈ s ∩ Λ₁, ν (t i)) 0 := by
    funext b
    simpa [P] using
      (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) Λ₁ s t ht b)
  rw [h_eval]
  simpa [P] using
    (lintegral_ite_const_eq_mul (μ := isssdFun ν Λ₂ η) (p := P) hp
      (∏ i ∈ s ∩ Λ₁, ν (t i)))

/-- Positive square-cylinder case for composing two ISSSD kernels. -/
lemma lintegral_isssdFun_apply_squareCylinder_of_forall
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E)
    (hU : ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i) :
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
      ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), ν (t i) := by
  let P : (S → E) → Prop := fun b =>
    ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i
  have h_outer :
      (isssdFun ν Λ₂ η) {b : S → E | P b} = ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i) := by
    have h := isssdFun_apply_forall_not_mem (ν := ν) (mE := mE) Λ₁ Λ₂ s t ht η
    rw [h, if_pos hU]
  calc
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
        (∏ i ∈ s ∩ Λ₁, ν (t i)) * (isssdFun ν Λ₂ η) {b : S → E | P b} := by
          simpa [P] using
            (lintegral_isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
              Λ₁ Λ₂ s t ht η)
    _ = (∏ i ∈ s ∩ Λ₁, ν (t i)) * (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) := by
          rw [h_outer]
    _ = ∏ i ∈ s ∩ (Λ₁ ∪ Λ₂), ν (t i) := by
          exact prod_inter_mul_prod_inter_sdiff_eq_prod_inter_union
            (s := s) (Λ₁ := Λ₁) (Λ₂ := Λ₂) (f := fun i : S => ν (t i))

/-- Zero square-cylinder case for composing two ISSD kernels. -/
lemma lintegral_isssdFun_apply_squareCylinder_of_not_forall
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E)
    (hU : ¬ ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i) :
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η = 0 := by
  let P : (S → E) → Prop := fun b =>
    ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i
  have h_outer : (isssdFun ν Λ₂ η) {b : S → E | P b} = 0 := by
    have h := isssdFun_apply_forall_not_mem (ν := ν) (mE := mE) Λ₁ Λ₂ s t ht η
    rw [h, if_neg hU]
  calc
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
        (∏ i ∈ s ∩ Λ₁, ν (t i)) * (isssdFun ν Λ₂ η) {b : S → E | P b} := by
          simpa [P] using
            (lintegral_isssdFun_apply_squareCylinder (ν := ν) (mE := mE)
              Λ₁ Λ₂ s t ht η)
    _ = 0 := by
          rw [h_outer]
          simp

/-- Composition of two ISSSD kernels evaluated on a finite square cylinder. -/
lemma lintegral_isssdFun_apply_squareCylinder_eq_union
    [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
      isssdFun ν (Λ₁ ∪ Λ₂) η ((s : Set S).pi t) := by
  by_cases hU : ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i
  · have hU' : ∀ i ∈ s, i ∉ Λ₁ ∪ Λ₂ → η i ∈ t i := by
      intro i hi hiU
      exact hU i (by simpa using hi) hiU
    rw [lintegral_isssdFun_apply_squareCylinder_of_forall
      (ν := ν) (mE := mE) Λ₁ Λ₂ s t ht η hU]
    simpa [if_pos hU'] using
      (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) (Λ₁ ∪ Λ₂) s t ht η).symm
  · have hU' : ¬ ∀ i ∈ s, i ∉ Λ₁ ∪ Λ₂ → η i ∈ t i := by
      intro h
      exact hU (fun i hi hiU => h i (by simpa using hi) hiU)
    rw [lintegral_isssdFun_apply_squareCylinder_of_not_forall
      (ν := ν) (mE := mE) Λ₁ Λ₂ s t ht η hU]
    simpa [if_neg hU'] using
      (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) (Λ₁ ∪ Λ₂) s t ht η).symm

/-- Each `isssdFun` value is a probability measure. -/
lemma isProbabilityMeasure_isssdFun_apply (Λ : Finset S) (η : S → E) :
    IsProbabilityMeasure (isssdFun (S := S) (E := E) ν Λ η) := by
  haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ ↦ ν)) := by infer_instance
  simpa [isssdFun_apply] using
    Measure.isProbabilityMeasure_map
      (μ := Measure.pi (fun _ : Λ ↦ ν))
      (f := juxt (Λ := (Λ : Set S)) (η := η))
      (hf := (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)).aemeasurable)

/-- Every independent finite-volume kernel has total mass one. -/
lemma isssdFun_apply_univ (Λ : Finset S) (η : S → E) :
    isssdFun (S := S) (E := E) ν Λ η Set.univ = 1 := by
  haveI : IsProbabilityMeasure (isssdFun (S := S) (E := E) ν Λ η) :=
    isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η
  simpa using (IsProbabilityMeasure.measure_univ (μ := isssdFun ν Λ η))

/-- The composition of two ISSSD kernels has total mass one. -/
lemma isssdFun_comp_isssdFun_apply_univ (Λ₁ Λ₂ : Finset S) (η : S → E) :
    (((isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η) Set.univ = 1 := by
  have huniv_meas : MeasurableSet (Set.univ : Set (S → E)) := MeasurableSet.univ
  haveI : IsProbabilityMeasure (isssdFun ν Λ₂ η) :=
    isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ₂ η
  haveI :
      IsProbabilityMeasure
        (Measure.map (juxt (Λ := (Λ₂ : Set S)) (η := η)) (Measure.pi fun _ : Λ₂ ↦ ν)) := by
    simpa [isssdFun_apply] using
      (isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ₂ η)
  have h_integrand :
      (fun b : S → E =>
          (Measure.map (juxt (Λ := (Λ₁ : Set S)) (η := b)) (Measure.pi fun _ : Λ₁ ↦ ν))
            Set.univ) =
        fun _ => (1 : ℝ≥0∞) := by
    funext b
    simpa [isssdFun_apply] using
      (isssdFun_apply_univ (S := S) (E := E) ν Λ₁ b)
  simp [Kernel.comp_apply' _ _ _ huniv_meas, Kernel.comap_apply, h_integrand,
    MeasureTheory.lintegral_const]

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by
          gcongr
          exact Finset.subset_union_right) := by
  classical
  -- We prove equality of kernels by showing that, for every boundary condition `η`, the resulting
  -- measures agree on the π-system of square cylinders generating the product σ-algebra.
  ext η
  -- Let `C` be the generating π-system of measurable rectangles.
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  have huniv : (Set.univ : Set (S → E)) ∈ C := by
    simpa [C] using (univ_mem_squareCylindersMeas S E)
  have hL_univ :
      (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η) Set.univ ≠ ∞ := by
    rw [isssdFun_comp_isssdFun_apply_univ (ν := ν) (mE := mE) Λ₁ Λ₂ η]
    simp
  have hmeas_eq :
      (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η)
        =
        ((isssdFun ν (Λ₁ ∪ Λ₂)).comap id
            (measurable_id'' <| by gcongr) η) := by
    refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
      (μ := (( (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂) η))
      (ν := ((isssdFun ν (Λ₁ ∪ Λ₂)).comap id (measurable_id'' <| by gcongr) η))
      (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hL_univ) ?_
    intro A hA
    rcases hA with ⟨s, t, ht, rfl⟩
    have ht_meas : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    have h_rect_meas : MeasurableSet ((s : Set S).pi t) :=
      MeasurableSet.pi s.countable_toSet (fun i _ => ht_meas i)
    simpa [Kernel.comp_apply' _ _ _ h_rect_meas, Kernel.comap_apply, isssdFun_apply] using
      (lintegral_isssdFun_apply_squareCylinder_eq_union
        (ν := ν) (mE := mE) Λ₁ Λ₂ s t ht_meas η)
  simp [hmeas_eq]

/-- The independent finite-volume kernels are Markov kernels. -/
lemma isMarkovKernel_isssdFun (Λ : Finset S) :
    IsMarkovKernel (isssdFun (S := S) (E := E) ν Λ) := by
  refine ⟨?_⟩
  intro η
  exact isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η

/-- Juxtaposing a finite-volume configuration leaves the outside-volume restriction unchanged. -/
lemma restrict_compl_juxt (Λ : Finset S) (x : S → E) (ζ : Λ → E) :
    Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)
        (juxt (Λ := (Λ : Set S)) x ζ) =
      Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ) x := by
  ext i
  have hi : (i : S) ∉ (Λ : Set S) := i.property
  simp [Set.restrict, juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := x) (x := (i : S)) hi]

/-- Outside-volume events pull back under `juxt` to either `univ` or `∅`. -/
lemma preimage_juxt_restrict_compl
    (Λ : Finset S) (x : S → E) {C : Set (((Λ : Set S)ᶜ : Set S) → E)} :
    (juxt (Λ := (Λ : Set S)) x) ⁻¹'
        ((Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C) =
      (by
        classical
        exact if x ∈ (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C
          then Set.univ
          else ∅) := by
  classical
  ext ζ
  by_cases hx : x ∈ (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C
  · have hx' : Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ) x ∈ C := by
      simpa [Set.mem_preimage] using hx
    have : Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)
        (juxt (Λ := (Λ : Set S)) x ζ) ∈ C := by
      simpa [restrict_compl_juxt (S := S) (E := E) Λ x ζ] using hx'
    simp [hx, Set.mem_preimage, this]
  · have hx' : Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ) x ∉ C := by
      simpa [Set.mem_preimage] using hx
    have : Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)
        (juxt (Λ := (Λ : Set S)) x ζ) ∉ C := by
      simpa [restrict_compl_juxt (S := S) (E := E) Λ x ζ] using hx'
    simp [hx, Set.mem_preimage, this]

/-- A `juxt`-mapped finite-coordinate measure factors outside-volume events as an indicator of the
boundary condition. -/
lemma map_juxt_inter_restrict_compl_preimage_of_measure
    {Λ : Finset S} (μΛ : Measure (Λ → E)) {A : Set (S → E)} (hA : MeasurableSet A)
    {C : Set (((Λ : Set S)ᶜ : Set S) → E)} (hC : MeasurableSet C) (x : S → E) :
    (Measure.map (juxt (Λ := (Λ : Set S)) x) μΛ)
        (A ∩ (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C) =
      ((Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C).indicator 1 x *
        (Measure.map (juxt (Λ := (Λ : Set S)) x) μΛ) A := by
  let J : (Λ → E) → (S → E) := juxt (Λ := (Λ : Set S)) x
  let B : Set (S → E) := (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C
  have hB : MeasurableSet B := hC.preimage (Set.measurable_restrict _)
  have hAB : MeasurableSet (A ∩ B) := hA.inter hB
  have hpreB : J ⁻¹' B = (by classical exact if x ∈ B then Set.univ else ∅) := by
    simpa [J, B] using preimage_juxt_restrict_compl (S := S) (E := E) Λ x (C := C)
  by_cases hx : x ∈ B
  · have hpreB' : J ⁻¹' B = Set.univ := by simpa [hx] using hpreB
    simp [J, B, hx, Set.indicator, hpreB',
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hAB,
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hA,
      preimage_inter, Set.inter_univ]
  · have hpreB' : J ⁻¹' B = (∅ : Set (Λ → E)) := by simpa [hx] using hpreB
    simp [J, B, hx, Set.indicator, hpreB',
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hAB,
      Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := x) (𝓔 := mE)) hA,
      preimage_inter]
    exact measure_empty

omit [IsProbabilityMeasure ν] in
/-- A product-measure map by `juxt` factors outside-volume events as an indicator of the boundary
condition. -/
lemma map_juxt_inter_restrict_compl_preimage
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet A)
    {C : Set (((Λ : Set S)ᶜ : Set S) → E)} (hC : MeasurableSet C) (x : S → E) :
    (Measure.map (juxt (Λ := (Λ : Set S)) x) (Measure.pi fun _ : Λ ↦ ν))
        (A ∩ (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C) =
      ((Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C).indicator 1 x *
        (Measure.map (juxt (Λ := (Λ : Set S)) x) (Measure.pi fun _ : Λ ↦ ν)) A := by
  exact map_juxt_inter_restrict_compl_preimage_of_measure
    (S := S) (E := E) (Λ := Λ) (Measure.pi fun _ : Λ => ν) hA hC x

/-- `juxtMapKernel` is proper with respect to the outside-volume σ-algebra. -/
lemma isProper_juxtMapKernel {Λ : Finset S} (μΛ : Measure (Λ → E)) [IsFiniteMeasure μΛ] :
    (juxtMapKernel (S := S) (E := E) μΛ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB x
  rw [juxtMapKernel_apply]
  let Δ : Set S := (Λ : Set S)ᶜ
  have hBcomap :
      MeasurableSet[
          MeasurableSpace.comap (Set.domRestrict Δ)
            (inferInstance : MeasurableSpace (Δ → E))] B := by
    rw [← MeasureTheory.cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := Δ)]
    exact hB
  rcases hBcomap with ⟨C, hC, rfl⟩
  exact map_juxt_inter_restrict_compl_preimage_of_measure
    (S := S) (E := E) (Λ := Λ) μΛ hA hC x

/-- The σ-finite reference λ-kernel is proper with respect to the outside-volume σ-algebra. -/
lemma isProper_sigmaFiniteLambdaFun
    (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) :
    (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB x
  rw [sigmaFiniteLambdaFun_apply_eq_map]
  let Δ : Set S := (Λ : Set S)ᶜ
  have hBcomap :
      MeasurableSet[
          MeasurableSpace.comap (Set.domRestrict Δ)
            (inferInstance : MeasurableSpace (Δ → E))] B := by
    rw [← MeasureTheory.cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := Δ)]
    exact hB
  rcases hBcomap with ⟨C, hC, rfl⟩
  exact map_juxt_inter_restrict_compl_preimage_of_measure
    (S := S) (E := E) (Λ := Λ) (Measure.pi fun _ : Λ => ν) hA hC x

/-- The independent finite-volume kernels are proper. -/
lemma isProper_isssdFun (Λ : Finset S) : (isssdFun (S := S) (E := E) ν Λ).IsProper :=
  isProper_juxtMapKernel (S := S) (E := E) (Measure.pi fun _ : Λ ↦ ν)

/-- The independent finite-volume kernels are consistent. -/
lemma isConsistent_isssdFun : IsConsistent (isssdFun (S := S) (E := E) ν) := by
  intro Λ₁ Λ₂ hΛ
  classical
  rw [isssdFun_comp_isssdFun]
  ext a s _
  simp only [Kernel.comap_apply, id_eq, isssdFun_apply, Finset.coe_sort_coe]
  rw [Finset.union_eq_right.2 hΛ]

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corresponding to the product measure. -/
@[simps]
def isssd (ν : Measure E) [IsProbabilityMeasure ν] : Specification S E where
  toPreSpecification := {
    toFun := isssdFun ν
    isConsistent' := isConsistent_isssdFun (S := S) (E := E) ν }
  isMarkovKernel' := isMarkovKernel_isssdFun (S := S) (E := E) ν
  isProper' := isProper_isssdFun (S := S) (E := E) ν

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssd_comp_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssd ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssd ν Λ₂ =
      (isssd ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by
          gcongr
          exact Finset.subset_union_right) := isssdFun_comp_isssdFun ..

/-- Georgii (1.25): the independent specification is strongly consistent. -/
lemma isStronglyConsistent_isssdFun [DecidableEq S] :
    IsStronglyConsistent (isssdFun (S := S) (E := E) ν) :=
  fun Λ₁ Λ₂ ↦ isssdFun_comp_isssdFun (ν := ν) Λ₁ Λ₂

lemma isStronglyConsistent_isssd [DecidableEq S] :
    IsStronglyConsistent (isssd (S := S) (E := E) ν) :=
  isStronglyConsistent_isssdFun (S := S) (E := E) ν

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  exact (isssd (S := S) (E := E) ν).isProper

end ISSSD

/-!
### Finite / σ-finite λ-kernels and base consistency

The σ-finite reference kernel `sigmaFiniteLambdaFun` evaluates to `Measure.map (juxt η) ν^Λ`
(`sigmaFiniteLambdaFun_apply_eq_map`). For a finite reference measure (including a probability spin
distribution), its finite-volume kernels agree pointwise with the independent kernels `isssdFun`, so
the ISSSD consistency proof applies verbatim.
-/

/-- For ISSSD-compatible spin distributions (probability spin law),
σ-finite λ-kernels coincide with ISSSD kernels. -/
lemma sigmaFiniteLambdaFun_eq_isssdFun {ν : Measure E}
    [IsProbabilityMeasure ν] (Λ : Finset S) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ = isssdFun (S := S) (E := E) ν Λ :=
  (sigmaFiniteLambdaFun_eq_finiteLambdaFun ν Λ).trans (finiteLambdaFun_eq_isssdFun ν Λ)

lemma isConsistent_sigmaFiniteLambdaFun {ν : Measure E}
    [IsProbabilityMeasure ν] :
    IsConsistent (sigmaFiniteLambdaFun (S := S) (E := E) ν) := fun Λ₁ Λ₂ hΛ₁₂ => by
  classical
  simp_rw [sigmaFiniteLambdaFun_eq_isssdFun Λ₁, sigmaFiniteLambdaFun_eq_isssdFun Λ₂]
  exact isConsistent_isssdFun (S := S) (E := E) ν hΛ₁₂

section InfinitePi

/-- The ISSSD kernel is a.e. measurable for any ambient measure on configurations. -/
lemma aemeasurable_isssd
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) (μ : Measure (S → E)) :
    AEMeasurable (fun η : S → E => isssd (S := S) (E := E) ν Λ η) μ :=
  ((isssd (S := S) (E := E) ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable

/-- The infinite product measure of a finite square cylinder. -/
lemma infinitePi_apply_squareCylinder
    (ν : Measure E) [IsProbabilityMeasure ν] (s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    Measure.infinitePi (fun _ : S ↦ ν) ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
  simpa using
    (Measure.infinitePi_pi (μ := fun _ : S ↦ ν) (s := s) (t := t)
      (fun i _ => ht i))

/-- The outside-`Λ` part of a finite square cylinder as a finite-coordinate box. -/
lemma setOf_forall_finset_not_mem_eq_pi_sdiff
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E) :
    {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ((s \ Λ : Finset S) : Set S).pi t := by
  ext η
  simp [Set.mem_pi]

/-- The infinite product measure of the outside-`Λ` constraints from a finite square cylinder. -/
lemma infinitePi_apply_forall_finset_not_mem
    [DecidableEq S] (ν : Measure E) [IsProbabilityMeasure ν] (Λ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    Measure.infinitePi (fun _ : S ↦ ν) {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ∏ i ∈ s \ Λ, ν (t i) := by
  rw [setOf_forall_finset_not_mem_eq_pi_sdiff (S := S) (E := E) Λ s t]
  exact infinitePi_apply_squareCylinder (S := S) (E := E) ν (s \ Λ) t ht

/-- Integrating one ISSSD square-cylinder kernel against the infinite product measure leaves the
same square-cylinder mass. -/
lemma lintegral_isssd_infinitePi_apply_squareCylinder
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    ∫⁻ η, isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)
        ∂Measure.infinitePi (fun _ : S ↦ ν) =
      Measure.infinitePi (fun _ : S ↦ ν) ((s : Set S).pi t) := by
  classical
  let P : (S → E) → Prop := fun η => ∀ i ∈ s, i ∉ Λ → η i ∈ t i
  have h_eval :
      (fun η : S → E => isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)) =
        fun η => ite (P η) (∏ i ∈ s ∩ Λ, ν (t i)) 0 := by
    funext η
    simpa [P, isssd_apply, isssdFun_apply, Finset.coe_sort_coe] using
      (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) Λ s t ht η)
  have hP :
      Measure.infinitePi (fun _ : S ↦ ν) {η : S → E | P η} = ∏ i ∈ s \ Λ, ν (t i) := by
    simpa [P] using
      (infinitePi_apply_forall_finset_not_mem (S := S) (E := E) ν Λ s t ht)
  calc
    ∫⁻ η, isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)
          ∂Measure.infinitePi (fun _ : S ↦ ν) =
        (∏ i ∈ s ∩ Λ, ν (t i)) *
          Measure.infinitePi (fun _ : S ↦ ν) {η : S → E | P η} := by
          rw [h_eval]
          exact lintegral_ite_const_eq_mul (μ := Measure.infinitePi (fun _ : S ↦ ν))
            (p := P) (measurableSet_forall_not_mem (S := S) (E := E) Λ s (t := t) ht) _
    _ = (∏ i ∈ s ∩ Λ, ν (t i)) * (∏ i ∈ s \ Λ, ν (t i)) := by rw [hP]
    _ = ∏ i ∈ s, ν (t i) := by
          exact Finset.prod_inter_mul_prod_diff s Λ fun i => ν (t i)
    _ = Measure.infinitePi (fun _ : S ↦ ν) ((s : Set S).pi t) := by
          rw [infinitePi_apply_squareCylinder (S := S) (E := E) ν s t ht]

/-- The infinite product measure has total mass one after binding an ISSSD kernel. -/
lemma infinitePi_bind_isssd_apply_univ
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    ((Measure.infinitePi (fun _ : S ↦ ν)).bind (isssd (S := S) (E := E) ν Λ)) Set.univ = 1 := by
  have huniv_meas : MeasurableSet (Set.univ : Set (S → E)) := MeasurableSet.univ
  have hκ := aemeasurable_isssd (S := S) (E := E) ν Λ (Measure.infinitePi (fun _ : S ↦ ν))
  have h1 : ∀ η : S → E, isssd (S := S) (E := E) ν Λ η Set.univ = 1 := by
    intro η
    simpa [isssd_apply] using isssdFun_apply_univ (S := S) (E := E) ν Λ η
  have h_integrand :
      (fun η : S → E =>
          (Measure.map (juxt (Λ := (Λ : Set S)) (η := η)) (Measure.pi fun _ : Λ ↦ ν))
            Set.univ) =
        fun _ => (1 : ℝ≥0∞) := by
    funext η
    simpa [isssd_apply, isssdFun_apply] using h1 η
  rw [Measure.bind_apply (s := Set.univ) huniv_meas hκ]
  simp [h_integrand, MeasureTheory.lintegral_const]

/-- The ISSSD resampling kernel preserves finite square-cylinder probabilities of the infinite
product measure. -/
lemma infinitePi_bind_isssd_apply_squareCylinder
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    ((Measure.infinitePi (fun _ : S ↦ ν)).bind (isssd (S := S) (E := E) ν Λ))
        ((s : Set S).pi t) =
      Measure.infinitePi (fun _ : S ↦ ν) ((s : Set S).pi t) := by
  let μ : Measure (S → E) := Measure.infinitePi (fun _ : S ↦ ν)
  have hκ := aemeasurable_isssd (S := S) (E := E) ν Λ μ
  rw [Measure.bind_apply (m := μ) (f := isssd (S := S) (E := E) ν Λ)
    (s := (s : Set S).pi t) (MeasureTheory.measurableSet_finset_pi (S := S) s t ht) hκ]
  simpa [μ] using lintegral_isssd_infinitePi_apply_squareCylinder
    (S := S) (E := E) ν Λ s t ht

/-- The infinite product measure is invariant under resampling any finite volume from the ISSSD
kernel. -/
lemma infinitePi_bind_isssd
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    (Measure.infinitePi (fun _ : S ↦ ν)).bind (isssd (S := S) (E := E) ν Λ) =
      Measure.infinitePi (fun _ : S ↦ ν) := by
  let μ : Measure (S → E) := Measure.infinitePi (fun _ : S ↦ ν)
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by simpa [C] using isPiSystem_squareCylindersMeas S E
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using generateFrom_squareCylindersMeas S E
  have huniv : (Set.univ : Set (S → E)) ∈ C := by simpa [C] using univ_mem_squareCylindersMeas S E
  have hμ_univ : (μ.bind (isssd (S := S) (E := E) ν Λ)) Set.univ ≠ ∞ := by
    rw [show μ = Measure.infinitePi (fun _ : S ↦ ν) from rfl]
    rw [infinitePi_bind_isssd_apply_univ (S := S) (E := E) ν Λ]
    simp
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
    (μ := μ.bind (isssd (S := S) (E := E) ν Λ)) (ν := μ)
    (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hμ_univ) ?_
  intro A hA
  rcases hA with ⟨s, t, ht, rfl⟩
  have ht_meas : ∀ i : S, MeasurableSet (t i) := by
    simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
  simpa [μ] using infinitePi_bind_isssd_apply_squareCylinder
    (S := S) (E := E) ν Λ s t ht_meas

/-- The infinite product measure `ν ^ S` is an `isssd ν`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_infinitePi (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsGibbsMeasure (Measure.infinitePi fun _ : S ↦ ν) := by
  classical
  intro Λ
  let μ : Measure (S → E) := Measure.infinitePi (fun _ : S ↦ ν)
  haveI : IsFiniteMeasure μ := inferInstance
  have hproper : (isssd (S := S) (E := E) ν).IsProper :=
    Specification.IsProper.isssd (S := S) (E := E) (mE := mE) (ν := ν)
  have hπ : (isssd (S := S) (E := E) ν Λ).IsProper := hproper Λ
  haveI : IsMarkovKernel (isssd (S := S) (E := E) ν Λ) := by
    infer_instance
  haveI : SigmaFinite (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))) := by
    infer_instance
  have h_bind : μ.bind (isssd (S := S) (E := E) ν Λ) = μ := by
    simpa [μ] using infinitePi_bind_isssd (S := S) (E := E) ν Λ
  have : Kernel.IsCondExp (isssd (S := S) (E := E) ν Λ) μ := by
    exact (Kernel.isCondExp_iff_bind_eq_left (μ := μ) (π := isssd (S := S) (E := E) ν Λ)
      hπ (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))).2 h_bind
  simpa [μ] using this

/-- On a square cylinder supported in `Λ`, the independent kernel does not depend on the boundary
condition. -/
lemma isssd_apply_squareCylinder_of_subset (ν : Measure E) [IsProbabilityMeasure ν]
    {Λ s : Finset S} (hs : s ⊆ Λ)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssd ν Λ η ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
  classical
  have hcond : ∀ i ∈ s, i ∉ Λ → η i ∈ t i := fun i hi hiΛ ↦ absurd (hs hi) hiΛ
  have hinter : s ∩ Λ = s := Finset.inter_eq_left.2 hs
  have h := isssdFun_apply_squareCylinder (ν := ν) (mE := mE) Λ s t ht η
  rw [hinter] at h
  rw [show (isssd ν Λ) η = isssdFun ν Λ η from rfl, h]
  exact if_pos hcond

variable (γ) in
/-- `γ` has *free measure* `μ₀` if on the events inside the volume it forgets the boundary
condition and reproduces `μ₀`: Georgii's `λ_Λ(A | η) = λ^S(A)` for `A ∈ 𝓕_Λ`. The independent
specifications, homogeneous (`Specification.hasFreeMeasure_isssd`) or not
(`Specification.hasFreeMeasure_isssdFamily`), are the examples. -/
def HasFreeMeasure (μ₀ : Measure (S → E)) : Prop :=
  ∀ (Λ : Finset S) (η : S → E) ⦃A : Set (S → E)⦄,
    MeasurableSet[cylinderEvents (Λ : Set S)] A → γ Λ η A = μ₀ A

/-! #### What a free measure determines

A free measure pins down the Gibbs measures of `γ` completely, and by an argument that uses
nothing but properness: the value `γ_Λ(A | η) = μ₀(A)` for `A ∈ 𝓕_Λ` turns the DLR equation over
`Λ` into `μ(A) = μ(Ω)\,μ₀(A)` on the local events, which generate. So `|𝒢(γ)| ≤ 1`, with equality
exactly when `μ₀` makes the inside and the outside of every finite volume independent
(`Specification.isGibbsMeasure_iff_indep_of_hasFreeMeasure`). Georgii's Remark (1.25) and
Example (7.14) are the two instances of this at `γ = ISSSD(λ)` and at its inhomogeneous form.
-/

section HasFreeMeasureTheorems
variable {μ₀ : Measure (S → E)}

/-- A square cylinder all of whose sites lie in `Δ` is `𝓕_Δ`-measurable. -/
lemma measurableSet_cylinderEvents_finset_pi {Δ : Set S} {s : Finset S} (hs : (s : Set S) ⊆ Δ)
    {t : S → Set E} (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Δ] ((s : Set S).pi t) := by
  have hpi : ((s : Set S).pi t) = ⋂ i ∈ s, (fun σ : S → E ↦ σ i) ⁻¹' t i := by
    ext σ; simp [Set.mem_pi]
  rw [hpi]
  exact MeasurableSet.biInter s.countable_toSet fun i hi ↦
    (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (hs hi)) (ht i)

/-- Every local event is `𝓕_Λ`-measurable for some finite volume `Λ`. -/
lemma exists_measurableSet_cylinderEvents_of_mem_measurableCylinders
    {A : Set (S → E)} (hA : A ∈ measurableCylinders fun _ : S ↦ E) :
    ∃ Λ : Finset S, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A := by
  obtain ⟨Λ, B, hB, rfl⟩ := (mem_measurableCylinders _).1 hA
  refine ⟨Λ, ?_⟩
  rw [cylinderEvents_eq_comap_finsetRestrict]
  exact ⟨B, hB, rfl⟩

/-- **A specification with a free measure has at most one Gibbs measure, up to total mass.**  If
`γ_Λ(A | η) = μ₀(A)` for all `A ∈ 𝓕_Λ` and all boundary conditions, then every finite Gibbs
measure for `γ` is the multiple `μ(Ω)\,μ₀` of `μ₀`.  Beyond the properness that every
specification has, no hypothesis on `γ`, on `E` or on `S` is used, and `μ₀` need not itself be a
Gibbs measure. -/
theorem eq_smul_of_hasFreeMeasure (h₀ : γ.HasFreeMeasure μ₀) [IsProbabilityMeasure μ₀]
    {μ : Measure (S → E)} [IsFiniteMeasure μ] (hμ : γ.IsGibbsMeasure μ) :
    μ = μ Set.univ • μ₀ := by
  have hbind : ∀ Λ : Finset S, μ.bind (γ Λ) = μ :=
    (isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ)).1 hμ
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : S ↦ E)
    (generateFrom_measurableCylinders (α := fun _ : S ↦ E)).symm
    isPiSystem_measurableCylinders (fun A hA ↦ ?_) (by simp)
  obtain ⟨Λ, hΛ⟩ := exists_measurableSet_cylinderEvents_of_mem_measurableCylinders hA
  have hmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  have hker : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  calc μ A = (μ.bind (γ Λ)) A := by rw [hbind Λ]
    _ = ∫⁻ _, μ₀ A ∂μ := by
        rw [Measure.bind_apply hmeas hker]
        exact lintegral_congr fun η ↦ h₀ Λ η hΛ
    _ = (μ Set.univ • μ₀) A := by
        rw [lintegral_const, Measure.smul_apply, smul_eq_mul, mul_comm]

/-- **A specification with a free measure has at most one Gibbs probability measure**, namely the
free measure itself. -/
theorem eq_of_hasFreeMeasure (h₀ : γ.HasFreeMeasure μ₀) [IsProbabilityMeasure μ₀]
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ) : μ = μ₀ := by
  simpa using eq_smul_of_hasFreeMeasure h₀ hμ

/-- **A free measure is a Gibbs measure exactly when it makes the inside and the outside of every
finite volume independent.**

Properness turns the DLR equation over `Λ` into the product rule
`μ₀(A ∩ B) = μ₀(A)\,μ₀(B)` for `A ∈ 𝓕_Λ` and `B ∈ 𝓕_{Λᶜ}`, and conversely: on a square cylinder,
splitting the sites into those inside and those outside `Λ` reduces the fixed-point equation to
that product rule. With `Specification.eq_of_hasFreeMeasure` this determines `𝒢(γ)` for a
specification with a free measure: it is `{μ₀}` when the independence holds, and `∅` otherwise. -/
theorem isGibbsMeasure_iff_indep_of_hasFreeMeasure [IsProbabilityMeasure μ₀]
    (h₀ : γ.HasFreeMeasure μ₀) :
    γ.IsGibbsMeasure μ₀ ↔ ∀ Λ : Finset S,
      ProbabilityTheory.Indep (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))
        (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) μ₀ := by
  classical
  rw [isGibbsMeasure_iff_forall_bind_eq]
  constructor
  · intro hbind Λ
    rw [ProbabilityTheory.Indep_iff]
    intro A B hA hB
    have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
    have hB' : MeasurableSet B := cylinderEvents_le_pi _ hB
    have hker : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ₀ :=
      (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
    calc μ₀ (A ∩ B) = (μ₀.bind (γ Λ)) (A ∩ B) := by rw [hbind Λ]
      _ = ∫⁻ η, B.indicator 1 η * μ₀ A ∂μ₀ := by
          rw [Measure.bind_apply (hA'.inter hB') hker]
          refine lintegral_congr fun η ↦ ?_
          rw [γ.isProper.inter_eq_indicator_mul Λ hA' hB η, h₀ Λ η hA]
      _ = μ₀ A * μ₀ B := by
          rw [lintegral_mul_const' _ _ (by simp), lintegral_indicator_one hB']
          ring
  · intro hindep Λ
    have hker : AEMeasurable (γ Λ : (S → E) → Measure (S → E)) μ₀ :=
      (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
    have hprob : IsProbabilityMeasure (μ₀.bind (γ Λ)) := by
      constructor
      rw [Measure.bind_apply MeasurableSet.univ hker]
      simp
    refine MeasureTheory.ext_of_generate_finite (squareCylindersMeas S E)
      (generateFrom_squareCylindersMeas S E) (isPiSystem_squareCylindersMeas S E)
      (fun A hA ↦ ?_) (by simp)
    obtain ⟨s, t, ht, rfl⟩ := hA
    have ht' : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    set A₁ : Set (S → E) := ((s ∩ Λ : Finset S) : Set S).pi t with hA₁
    set A₂ : Set (S → E) := ((s \ Λ : Finset S) : Set S).pi t with hA₂
    have hsplit : ((s : Set S).pi t) = A₁ ∩ A₂ := by
      ext σ
      simp only [hA₁, hA₂, Set.mem_pi, Set.mem_inter_iff, Finset.coe_inter, Finset.coe_sdiff,
        Set.mem_inter_iff, Set.mem_sdiff]
      refine ⟨fun h ↦ ⟨fun i hi ↦ h i hi.1, fun i hi ↦ h i hi.1⟩, ?_⟩
      rintro ⟨h1, h2⟩ i hi
      by_cases hiΛ : i ∈ Λ
      · exact h1 i ⟨hi, hiΛ⟩
      · exact h2 i ⟨hi, hiΛ⟩
    have hm₁ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A₁ :=
      measurableSet_cylinderEvents_finset_pi (Finset.coe_subset.2 Finset.inter_subset_right) ht'
    have hm₂ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] A₂ :=
      measurableSet_cylinderEvents_finset_pi
        (fun i hi ↦ by simp only [Finset.coe_sdiff, Set.mem_sdiff] at hi; exact hi.2) ht'
    have h₁' : MeasurableSet A₁ := cylinderEvents_le_pi _ hm₁
    have h₂' : MeasurableSet A₂ := cylinderEvents_le_pi _ hm₂
    rw [hsplit, Measure.bind_apply (h₁'.inter h₂') hker]
    calc ∫⁻ η, γ Λ η (A₁ ∩ A₂) ∂μ₀
        = ∫⁻ η, A₂.indicator 1 η * μ₀ A₁ ∂μ₀ := by
          refine lintegral_congr fun η ↦ ?_
          rw [γ.isProper.inter_eq_indicator_mul Λ h₁' hm₂ η, h₀ Λ η hm₁]
      _ = μ₀ A₁ * μ₀ A₂ := by
          rw [lintegral_mul_const' _ _ (by simp), lintegral_indicator_one h₂']
          ring
      _ = μ₀ (A₁ ∩ A₂) :=
          ((ProbabilityTheory.Indep_iff _ _ _).1 (hindep Λ) A₁ A₂ hm₁ hm₂).symm

end HasFreeMeasureTheorems

/-- On events measurable inside the finite volume `Λ`, the independent kernel with any boundary
condition `η` gives the same mass as the infinite product measure `ν^S`. -/
lemma isssd_apply_of_mem_cylinderEvents (ν : Measure E) [IsProbabilityMeasure ν]
    (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (Λ : Set S)] A) :
    isssd (S := S) (E := E) ν Λ η A = Measure.infinitePi (fun _ : S ↦ ν) A := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hmeasA : MeasurableSet (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B) :=
    Λ.measurable_restrict hB
  have hcomp : ∀ ζ : Π _ : Λ, E,
      Λ.restrict (π := fun _ : S ↦ E) (juxt (Λ : Set S) η ζ) = ζ := by
    intro ζ
    funext i
    exact juxt_apply_of_mem (by simp) ζ
  have h1 : isssd (S := S) (E := E) ν Λ η (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B)
      = Measure.pi (fun _ : Λ ↦ ν) B := by
    rw [show (isssd (S := S) (E := E) ν Λ) η
        = Measure.map (juxt (Λ : Set S) η) (Measure.pi fun _ : Λ ↦ ν) from rfl]
    rw [Measure.map_apply Measurable.juxt hmeasA]
    congr 1
    ext ζ
    simp [Set.mem_preimage, hcomp ζ]
  have h2 : Measure.infinitePi (fun _ : S ↦ ν) (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B) =
      Measure.pi (fun _ : Λ ↦ ν) B := by
    rw [← Measure.infinitePi_map_restrict (μ := fun _ : S ↦ ν) (I := Λ),
      Measure.map_apply Λ.measurable_restrict hB]
  rw [h1, h2]

lemma hasFreeMeasure_isssd (ν : Measure E) [IsProbabilityMeasure ν] :
    HasFreeMeasure (isssd (S := S) (E := E) ν) (Measure.infinitePi fun _ : S ↦ ν) :=
  isssd_apply_of_mem_cylinderEvents ν

/-- Any probability measure pushed through the independent kernel on `Λ` agrees with the product
measure on square cylinders supported in `Λ`. -/
lemma bind_isssd_apply_squareCylinder_of_subset (ν : Measure E)
    [IsProbabilityMeasure ν] (μ : Measure (S → E))
    {Λ s : Finset S} (hs : s ⊆ Λ)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    (μ.bind (isssd ν Λ)) ((s : Set S).pi t) = μ Set.univ * ∏ i ∈ s, ν (t i) := by
  classical
  have hmeas : MeasurableSet ((s : Set S).pi t) :=
    MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i
  have hker : AEMeasurable (isssd ν Λ : (S → E) → Measure (S → E)) μ :=
    (((isssd ν Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  rw [Measure.bind_apply hmeas hker,
    lintegral_congr fun a ↦ isssd_apply_squareCylinder_of_subset (ν := ν) hs t ht a,
    lintegral_const, mul_comm]

/-- The finite-measure form of Georgii Remark (1.25). -/
theorem isGibbsMeasure_isssd_iff_of_isFiniteMeasure (ν : Measure E) [IsProbabilityMeasure ν]
    (μ : Measure (S → E)) [IsFiniteMeasure μ] :
    (isssd ν).IsGibbsMeasure μ ↔ μ = μ Set.univ • Measure.infinitePi fun _ : S ↦ ν := by
  classical
  constructor
  · intro hμ
    have hbind : ∀ Λ : Finset S, μ.bind (isssd ν Λ) = μ :=
      (isGibbsMeasure_iff_forall_bind_eq (γ := isssd ν) (μ := μ)).1 hμ
    refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ
      (C := squareCylindersMeas S E) (hA := generateFrom_squareCylindersMeas S E)
      (hC := isPiSystem_squareCylindersMeas S E) (huniv := univ_mem_squareCylindersMeas S E)
      (hμ_univ := measure_ne_top _ _) ?_
    rintro A ⟨s, t, ht, rfl⟩
    have ht' : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    calc μ ((s : Set S).pi t)
        = (μ.bind (isssd ν s)) ((s : Set S).pi t) := by rw [hbind s]
      _ = μ Set.univ * ∏ i ∈ s, ν (t i) :=
          bind_isssd_apply_squareCylinder_of_subset ν μ (le_refl s) t ht'
      _ = (μ Set.univ • Measure.infinitePi (fun _ : S ↦ ν)) ((s : Set S).pi t) := by
          rw [Measure.smul_apply, smul_eq_mul,
            infinitePi_apply_squareCylinder (S := S) (E := E) ν s t ht']
  · intro h
    refine (isGibbsMeasure_iff_forall_bind_eq (γ := isssd ν) (μ := μ)).2 fun Λ ↦ ?_
    conv_lhs => rw [h]
    rw [Measure.bind_smul, infinitePi_bind_isssd (S := S) (E := E) ν Λ, ← h]

/-- **Georgii, Remark (1.25).** `G(λ_·) = {λ^S}`. -/
theorem isGibbsMeasure_isssd_iff (ν : Measure E) [IsProbabilityMeasure ν]
    (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    (isssd ν).IsGibbsMeasure μ ↔ μ = Measure.infinitePi fun _ : S ↦ ν := by
  rw [isGibbsMeasure_isssd_iff_of_isFiniteMeasure ν μ, measure_univ, one_smul]

end InfinitePi

section Modifier
variable {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- The kernel of a modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

This is an auxiliary definition for `Specification.modification`, which you should generally use
instead of `Specification.modificationKer`. -/
@[simps]
noncomputable def modificationKer (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E))
    (ρ : Finset S → (S → E) → ℝ≥0∞) (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ (γ Λ η).withDensity (ρ Λ))
    (@Measure.measurable_of_measurable_coe _ _ _ (_) _ fun s hs ↦ by
      simp_rw [MeasureTheory.withDensity_apply _ hs]
      exact (Measure.measurable_setLIntegral (hρ _) hs).comp (γ Λ).measurable)

@[simp] lemma modificationKer_one' (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ (fun _Λ _η ↦ 1) (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma modificationKer_one (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ 1 (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

lemma isProper_modificationKer_of_isProper
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    (hγ : ∀ Λ, (γ Λ).IsProper) (hρ : ∀ Λ, Measurable (ρ Λ)) :
    ∀ Λ, (modificationKer γ ρ hρ Λ).IsProper := by
  intro Λ
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB η
  rw [modificationKer_apply, withDensity_apply _ hA,
    withDensity_apply _ (hA.inter <| cylinderEvents_le_pi _ hB),
    (hγ Λ).setLIntegral_inter_eq_indicator_mul_setLIntegral cylinderEvents_le_pi (hρ _) hA hB]

/-- **Georgii, Remark (1.28)(1), first sentence.** A density change of the kernels of a
specification is proper, because the kernels of the specification are. -/
lemma isProper_modificationKer {γ : Specification S E}
    (hρ : ∀ Λ, Measurable (ρ Λ)) :
    ∀ Λ, (modificationKer γ ρ hρ Λ).IsProper :=
  isProper_modificationKer_of_isProper (fun Λ => γ.isProper' Λ) hρ

/-- A modifier of a specification `γ` is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `γ.modificationKer ρ` (informally, `ρ * γ`) is consistent.
* The modified kernels are still probability kernels, so they again form a genuine specification.

Properness of the modified kernels is not a condition: by Georgii, Remark (1.28)(1), it is
inherited from `γ` (`Specification.isProper_modificationKer`); see
`Specification.IsModifier.isProper`. -/
@[mk_iff]
structure IsModifier (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  isMarkovKernel Λ : IsMarkovKernel (modificationKer γ ρ measurable Λ)
  isConsistent : IsConsistent (modificationKer γ ρ measurable)

/-- **Georgii, Remark (1.28)(1).** The kernels modified by a modifier are proper: this is
automatic, not a condition of `Specification.IsModifier`. -/
protected lemma IsModifier.isProper (h : γ.IsModifier ρ) :
    ∀ Λ, (modificationKer γ ρ h.measurable Λ).IsProper :=
  isProper_modificationKer h.measurable

@[simp] lemma IsModifier.one' : γ.IsModifier (fun _Λ _η ↦ 1) where
  measurable _ := measurable_const
  isConsistent := by simpa using γ.isConsistent
  isMarkovKernel Λ := by
    simp only [modificationKer_one']
    infer_instance

@[simp] lemma IsModifier.one : γ.IsModifier 1 := .one'

lemma IsModifier.comp_eq (hρ : γ.IsModifier ρ) ⦃Λ₁ Λ₂⦄ (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    (fun ξ ↦ (γ Λ₁ ξ).withDensity (ρ Λ₁)) ∘ₘ (γ Λ₂ η).withDensity (ρ Λ₂)
      = (γ Λ₂ η).withDensity (ρ Λ₂) := by
  simpa [IsConsistent, modificationKer, Kernel.ext_iff, Kernel.comp_apply, Measure.ext_iff]
    using DFunLike.congr_fun (hρ.isConsistent hΛ) η

/-- Evaluate the composition of two density-modified kernels on a measurable set.

`γ` is only a dependent family of kernels; probability-kernel hypotheses are irrelevant for this
Fubini calculation. -/
lemma modificationKer_comp_apply_eq_lintegral_mul
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)}
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : ∀ Λ, Measurable (ρ Λ))
    {Λ₁ Λ₂ : Finset S} {η : S → E} {A : Set (S → E)} (hA : MeasurableSet A) :
    (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
          cylinderEvents_le_pi ∘ₖ modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂) η) A =
      ∫⁻ x, ρ Λ₂ x * ((γ Λ₁ x).withDensity (ρ Λ₁)) A ∂(γ Λ₂ η) := by
  let kA : (S → E) → ℝ≥0∞ := fun x => ((γ Λ₁ x).withDensity (ρ Λ₁)) A
  have hkA_meas : Measurable kA := by
    let K₁ : Kernel[cylinderEvents (Λ₁ : Set S)ᶜ] (S → E) (S → E) :=
      modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁
    have hmeas_dom : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] (fun x : S → E => (K₁ x) A) :=
      Kernel.measurable_coe K₁ hA
    simpa [kA, K₁, modificationKer] using hmeas_dom.mono cylinderEvents_le_pi le_rfl
  have hcomp :
      (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
            cylinderEvents_le_pi ∘ₖ modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂) η) A =
        ∫⁻ x, (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
            cylinderEvents_le_pi) x) A ∂(modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂ η) := by
    simpa using
      (Kernel.comp_apply' ((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
          cylinderEvents_le_pi) (modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂) η hA)
  have h_integrand :
      (fun x : S → E => (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
          cylinderEvents_le_pi) x) A) = kA := by
    funext x
    simp [kA, modificationKer, Kernel.comap_apply]
  calc
    (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
          cylinderEvents_le_pi ∘ₖ modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂) η) A
        = ∫⁻ x, (((modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₁).comap id
            cylinderEvents_le_pi) x) A ∂(modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂ η) := hcomp
    _ = ∫⁻ x, kA x ∂(modificationKer (γ := γ) (ρ := ρ) (hρ := hρ) Λ₂ η) := by
          rw [h_integrand]
    _ = ∫⁻ x, ρ Λ₂ x * kA x ∂(γ Λ₂ η) := by
          simpa [kA, modificationKer] using
            (lintegral_withDensity_eq_lintegral_mul (μ := γ Λ₂ η) (f := ρ Λ₂)
              (h_mf := hρ Λ₂) (g := kA) hkA_meas)

/-! ### Georgii's Proposition (1.30)

`Λ₁` is Georgii's `Λ` and `Λ₂` his `Δ`, with `Λ₁ ⊆ Λ₂`. Condition (a) ↔ (b) needs only properness
and
consistency of the base specification; (b) ↔ (c) needs only *disjoint* consistency
(`IsDisjointlyConsistent`: `λ_Δ λ_Λ = λ_{Δ ∪ Λ}` for `Λ ∩ Δ = ∅`, Georgii's Notation (1.26)),
which is what `ae_eq_iff_ae_ae_eq` and `isModifier_iff_ae_comm` assume.
-/

/-- Composing two density-modified kernels is again a density change of the base specification, with
density `ρ Λ₁ * γ_{Λ₁} ρ Λ₂`. Georgii (1.30), step 1. -/
lemma comp_modificationKer_apply (hρ : ∀ Λ, Measurable (ρ Λ))
    (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    ((modificationKer (γ := ⇑γ) ρ hρ Λ₁).comap id cylinderEvents_le_pi
        ∘ₖ modificationKer (γ := ⇑γ) ρ hρ Λ₂) η
      = (γ Λ₂ η).withDensity (fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)) := by
  classical
  set G : (S → E) → ℝ≥0∞ := fun ω ↦ ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω) with hGdef
  have hGmeas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] G := (hρ Λ₂).lintegral_kernel
  have hGmeas' : Measurable G := hGmeas.mono cylinderEvents_le_pi le_rfl
  -- Consistency of `γ`, in integral form.
  have hbind : ∀ f : (S → E) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(γ Λ₂ η) = ∫⁻ ζ, (∫⁻ x, f x ∂(γ Λ₁ ζ)) ∂(γ Λ₂ η) := by
    intro f hf
    conv_lhs => rw [← Specification.bind (γ := γ) hΛ η]
    exact Measure.lintegral_bind
      ((Kernel.measurable (γ Λ₁)).mono cylinderEvents_le_pi le_rfl).aemeasurable hf.aemeasurable
  ext A hA
  set F : (S → E) → ℝ≥0∞ := fun ζ ↦ ∫⁻ ω in A, ρ Λ₁ ω ∂(γ Λ₁ ζ) with hFdef
  have hFmeas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] F := (hρ Λ₁).setLIntegral_kernel hA
  have hFmeas' : Measurable F := hFmeas.mono cylinderEvents_le_pi le_rfl
  -- The left-hand side is `∫⁻ ζ, F ζ * ρ Λ₂ ζ ∂(γ Λ₂ η)`.
  have hL : ((modificationKer (γ := ⇑γ) ρ hρ Λ₁).comap id cylinderEvents_le_pi
        ∘ₖ modificationKer (γ := ⇑γ) ρ hρ Λ₂) η A = ∫⁻ ζ, F ζ * ρ Λ₂ ζ ∂(γ Λ₂ η) := by
    rw [modificationKer_comp_apply_eq_lintegral_mul hρ hA]
    exact lintegral_congr fun ζ ↦ by rw [withDensity_apply _ hA, mul_comm]
  -- The right-hand side is `∫⁻ ζ, G ζ * F ζ ∂(γ Λ₂ η)`, by properness of `γ Λ₁`.
  have hR : ((γ Λ₂ η).withDensity (fun ω ↦ ρ Λ₁ ω * G ω)) A
      = ∫⁻ ζ, G ζ * F ζ ∂(γ Λ₂ η) := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    have hrw : (A.indicator fun ω ↦ ρ Λ₁ ω * G ω) = fun ω ↦ G ω * A.indicator (ρ Λ₁) ω := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω, mul_comm]
    rw [hrw, hbind (fun ω ↦ G ω * A.indicator (ρ Λ₁) ω)
      (hGmeas'.fun_mul ((hρ Λ₁).indicator hA))]
    refine lintegral_congr fun ζ ↦ ?_
    rw [(γ.isProper Λ₁).lintegral_mul cylinderEvents_le_pi ((hρ Λ₁).indicator hA) hGmeas ζ,
      lintegral_indicator hA]
  -- Both sides equal `∫⁻ ζ, F ζ * G ζ ∂(γ Λ₂ η)`, again by properness of `γ Λ₁`.
  rw [hL, hR, hbind (fun ζ ↦ F ζ * ρ Λ₂ ζ) (hFmeas'.fun_mul (hρ Λ₂))]
  refine lintegral_congr fun ζ ↦ ?_
  rw [(γ.isProper Λ₁).lintegral_mul cylinderEvents_le_pi (hρ Λ₂) hFmeas ζ, mul_comm]

/-- **Georgii, Proposition (1.30), (a) ↔ (b).** -/
lemma isModifier_iff_ae_eq :
    γ.IsModifier ρ ↔
      (∀ Λ, Measurable (ρ Λ)) ∧
      (∀ (Λ : Finset S) (η : S → E), ∫⁻ ζ, ρ Λ ζ ∂(γ Λ η) = 1) ∧
      ∀ ⦃Λ₁ Λ₂ : Finset S⦄, Λ₁ ⊆ Λ₂ → ∀ η : S → E,
        ρ Λ₂ =ᵐ[γ Λ₂ η] fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω) := by
  constructor
  · rintro h
    have hnorm : ∀ (Λ : Finset S) (η : S → E), ∫⁻ ζ, ρ Λ ζ ∂(γ Λ η) = 1 := by
      intro Λ η
      have := h.isMarkovKernel Λ
      have huniv := measure_univ (μ := modificationKer (⇑γ) ρ h.measurable Λ η)
      rwa [modificationKer_apply, withDensity_apply _ MeasurableSet.univ,
        setLIntegral_univ] at huniv
    refine ⟨h.measurable, hnorm, fun Λ₁ Λ₂ hΛ η ↦ ?_⟩
    have hcomp := DFunLike.congr_fun (h.isConsistent hΛ) η
    rw [comp_modificationKer_apply h.measurable hΛ η, modificationKer_apply] at hcomp
    exact (withDensity_eq_iff_of_sigmaFinite (h.measurable Λ₂).aemeasurable
      ((h.measurable Λ₁).fun_mul
        ((h.measurable Λ₂).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)).aemeasurable).1
      hcomp.symm
  · rintro ⟨hmeas, hnorm, hb⟩
    have hmk : ∀ Λ, IsMarkovKernel (modificationKer (⇑γ) ρ hmeas Λ) := by
      intro Λ
      refine ⟨fun η ↦ ⟨?_⟩⟩
      rw [modificationKer_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      exact hnorm Λ η
    refine ⟨hmeas, hmk, fun Λ₁ Λ₂ hΛ ↦ Kernel.ext fun η ↦ ?_⟩
    rw [comp_modificationKer_apply hmeas hΛ η, modificationKer_apply]
    exact (withDensity_congr_ae (hb hΛ η)).symm

/-- Georgii (1.30), (b) ↔ (c) on a single fibre. -/
lemma ae_eq_iff_ae_comm (hmeas : ∀ Λ, Measurable (ρ Λ))
    (η₂ : S → E) (hnorm : ∫⁻ ζ, ρ Λ₁ ζ ∂(γ Λ₁ η₂) = 1) :
    (ρ Λ₂ =ᵐ[γ Λ₁ η₂] fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω))
      ↔ ∀ᵐ z ∂((γ Λ₁ η₂).prod (γ Λ₁ η₂)),
          ρ Λ₂ z.1 * ρ Λ₁ z.2 = ρ Λ₂ z.2 * ρ Λ₁ z.1 := by
  classical
  have hGmeas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ]
      (fun ω ↦ ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)) := (hmeas Λ₂).lintegral_kernel
  -- Properness freezes the boundary observable `ω ↦ γ_{Λ₁} ρ_{Λ₂} (ω)` on the fibre.
  have hGconst : ∀ᵐ ω ∂(γ Λ₁ η₂),
      (∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)) = ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η₂) :=
    (γ.isProper Λ₁).ae_eq_const cylinderEvents_le_pi hGmeas η₂
  constructor
  · intro h
    have h' : ρ Λ₂ =ᵐ[γ Λ₁ η₂] fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η₂) := by
      filter_upwards [h, hGconst] with ω hω hGω using hω.trans (by rw [hGω])
    have h1 : ∀ᵐ z ∂((γ Λ₁ η₂).prod (γ Λ₁ η₂)),
        ρ Λ₂ z.1 = ρ Λ₁ z.1 * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η₂) :=
      Measure.quasiMeasurePreserving_fst.ae h'
    have h2 : ∀ᵐ z ∂((γ Λ₁ η₂).prod (γ Λ₁ η₂)),
        ρ Λ₂ z.2 = ρ Λ₁ z.2 * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η₂) :=
      Measure.quasiMeasurePreserving_snd.ae h'
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]; ring
  · intro h
    have h' : ∀ᵐ ζ ∂(γ Λ₁ η₂), ∀ᵐ ξ ∂(γ Λ₁ η₂), ρ Λ₂ ζ * ρ Λ₁ ξ = ρ Λ₂ ξ * ρ Λ₁ ζ :=
      Measure.ae_ae_of_ae_prod h
    filter_upwards [h', hGconst] with ζ hζ hGζ
    have hint : ∫⁻ ξ, ρ Λ₂ ζ * ρ Λ₁ ξ ∂(γ Λ₁ η₂) = ∫⁻ ξ, ρ Λ₂ ξ * ρ Λ₁ ζ ∂(γ Λ₁ η₂) :=
      lintegral_congr_ae hζ
    rw [lintegral_const_mul _ (hmeas Λ₁), lintegral_mul_const _ (hmeas Λ₂), hnorm, mul_one] at hint
    rw [hint, hGζ, mul_comm]

/-- Georgii's condition (b) for `Λ₂` splits along `Λ₂ \ Λ₁`. -/
lemma ae_eq_iff_ae_ae_eq [DecidableEq S] (hγ : IsDisjointlyConsistent ⇑γ)
    (hmeas : ∀ Λ, Measurable (ρ Λ)) (hΛ : Λ₁ ⊆ Λ₂) (η₁ : S → E) :
    (ρ Λ₂ =ᵐ[γ Λ₂ η₁] fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω))
      ↔ ∀ᵐ η₂ ∂γ (Λ₂ \ Λ₁) η₁,
          ρ Λ₂ =ᵐ[γ Λ₁ η₂] fun ω ↦ ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω) := by
  classical
  have hbind : (γ (Λ₂ \ Λ₁) η₁).bind (γ Λ₁) = γ Λ₂ η₁ := by
    rw [hγ.bind_eq disjoint_sdiff_self_right η₁, Finset.union_sdiff_of_subset hΛ]
  have hGmeas : Measurable (fun ω : S → E ↦ ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)) :=
    ((hmeas Λ₂).lintegral_kernel).mono cylinderEvents_le_pi le_rfl
  have hset : MeasurableSet {ω : S → E | ρ Λ₂ ω = ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)} :=
    measurableSet_eq_fun (hmeas Λ₂) ((hmeas Λ₁).mul hGmeas)
  have hcomp : (γ (Λ₂ \ Λ₁) η₁).bind (γ Λ₁)
      = ((γ Λ₁).comap id cylinderEvents_le_pi) ∘ₘ (γ (Λ₂ \ Λ₁) η₁) := rfl
  rw [← hbind, hcomp]
  exact Measure.ae_comp_iff hset

/-- **Georgii, Proposition (1.30), (a) ↔ (c).** Compare `Specification.IsPremodifier`, the
everywhere-version of the same symmetry (Georgii (1.31)). -/
lemma isModifier_iff_ae_comm [DecidableEq S] (hγ : IsDisjointlyConsistent ⇑γ) :
    γ.IsModifier ρ ↔
      (∀ Λ, Measurable (ρ Λ)) ∧
      (∀ (Λ : Finset S) (η : S → E), ∫⁻ ζ, ρ Λ ζ ∂(γ Λ η) = 1) ∧
      ∀ ⦃Λ₁ Λ₂ : Finset S⦄, Λ₁ ⊆ Λ₂ → ∀ η₁ : S → E,
        ∀ᵐ η₂ ∂γ (Λ₂ \ Λ₁) η₁, ∀ᵐ z ∂((γ Λ₁ η₂).prod (γ Λ₁ η₂)),
          ρ Λ₂ z.1 * ρ Λ₁ z.2 = ρ Λ₂ z.2 * ρ Λ₁ z.1 := by
  rw [isModifier_iff_ae_eq]
  refine and_congr_right fun hmeas ↦ and_congr_right fun hnorm ↦ ?_
  refine forall_congr' fun Λ₁ ↦ forall_congr' fun Λ₂ ↦ forall_congr' fun hΛ ↦
    forall_congr' fun η₁ ↦ ?_
  rw [ae_eq_iff_ae_ae_eq hγ hmeas hΛ η₁]
  exact Filter.eventually_congr (.of_forall fun η₂ ↦ ae_eq_iff_ae_comm hmeas η₂ (hnorm Λ₁ η₂))

/-- The empty-volume kernel of any specification is the identity: properness and the Markov
property force `γ ∅ x = δ_x`. -/
@[simp] lemma apply_empty (γ : Specification S E) (x : S → E) : γ ∅ x = Measure.dirac x := by
  refine Measure.ext fun A hA ↦ ?_
  have hA' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((∅ : Finset S) : Set S)ᶜ] A := by
    rw [Finset.coe_empty, Set.compl_empty, cylinderEvents_univ]; exact hA
  rw [Measure.dirac_apply' _ hA,
    (γ.isProper ∅).apply_eq_indicator_mul_univ cylinderEvents_le_pi hA', measure_univ, mul_one]

/-- Modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

When the family of densities `ρ` is a modifier (`Specification.IsModifier`), modifying a
specification results in a specification `γ.modification ρ _`. -/
noncomputable def modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : Specification S E where
  toPreSpecification := {
    toFun := modificationKer γ ρ hρ.measurable
    isConsistent' := hρ.isConsistent }
  isMarkovKernel' := hρ.isMarkovKernel
  isProper' := hρ.isProper

-- This is not simp as we want to keep `modificationKer` an implementation detail
lemma coe_modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : γ.modification ρ hρ = modificationKer γ ρ hρ.measurable := rfl

@[simp]
lemma modification_apply (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) (Λ : Finset S) (η : S → E) :
    γ.modification ρ hρ Λ η = (γ Λ η).withDensity (ρ Λ) := rfl

/-- Set-restricted version of `Specification.modification_apply_le`: a pointwise bound on the
density **on `B` only** bounds the modified kernel on `A ∩ B` against the base kernel on `A`.
This is the estimate `∫_{A ∩ B} ρ_Λ dγ_Λ ≤ C · γ_Λ(A)` in Georgii's proof of (4.12). -/
lemma modification_apply_inter_le (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) (Λ : Finset S) (η : S → E) {A B : Set (S → E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {c : ℝ≥0∞}
    (hc : ∀ ω ∈ B, ρ Λ ω ≤ c) :
    γ.modification ρ hρ Λ η (A ∩ B) ≤ c * γ Λ η A := by
  rw [modification_apply, withDensity_apply _ (hA.inter hB)]
  calc ∫⁻ x in A ∩ B, ρ Λ x ∂(γ Λ η)
      ≤ ∫⁻ _ in A ∩ B, c ∂(γ Λ η) :=
        setLIntegral_mono' (hA.inter hB) fun x hx ↦ hc x hx.2
    _ = c * γ Λ η (A ∩ B) := setLIntegral_const _ _
    _ ≤ c * γ Λ η A := mul_le_mul' le_rfl (measure_mono inter_subset_left)

/-- A pointwise bound on the densities bounds the modified kernel against the base kernel. -/
lemma modification_apply_le (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) (Λ : Finset S) (η : S → E) {A : Set (S → E)} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (hc : ∀ ω, ρ Λ ω ≤ c) :
    γ.modification ρ hρ Λ η A ≤ c * γ Λ η A := by
  simpa [Set.inter_univ] using modification_apply_inter_le γ ρ hρ Λ η hA MeasurableSet.univ
    (fun ω _ ↦ hc ω)

@[simp] lemma IsModifier.mul {ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞}
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    γ.IsModifier (ρ₁ * ρ₂) where
  measurable Λ := (hρ₁.measurable _).mul (hρ₂.measurable _)
  isConsistent Λ₁ Λ₂ hΛ := by
    simpa [modificationKer, modification_apply, Pi.mul_apply, MeasureTheory.withDensity_mul,
      hρ₁.measurable, hρ₂.measurable]
      using (hρ₂.isConsistent (Λ₁ := Λ₁) (Λ₂ := Λ₂) hΛ)
  isMarkovKernel Λ := by
    simpa [modificationKer, modification_apply, Pi.mul_apply, MeasureTheory.withDensity_mul,
      hρ₁.measurable, hρ₂.measurable]
      using hρ₂.isMarkovKernel Λ

@[simp] lemma modification_one' (γ : Specification S E) :
    γ.modification (fun _Λ _η ↦ 1) .one' = γ := by ext; simp

@[simp] lemma modification_one (γ : Specification S E) : γ.modification 1 .one = γ := by ext; simp

@[simp] lemma modification_modification (γ : Specification S E) (ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞)
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    (γ.modification ρ₁ hρ₁).modification ρ₂ hρ₂ = γ.modification (ρ₁ * ρ₂) (hρ₁.mul hρ₂) := by
  ext Λ σ s hs
  simp only [modification_apply, Pi.mul_apply]
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (hρ₁.measurable Λ) (hρ₂.1 Λ) hs]

lemma isProper_modification {hρ} : (γ.modification ρ hρ).IsProper := by
  refine IsProper.of_inter_eq_indicator_mul fun Λ A hA B hB η ↦ ?_
  rw [modification_apply, withDensity_apply _ hA,
    withDensity_apply _ (hA.inter <| cylinderEvents_le_pi _ hB),
    setLIntegral_inter_eq_indicator_mul_setLIntegral γ _ (hρ.measurable _) hA hB]

/-- A premodifier is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η` for all `Λ₁ Λ₂ : Finset S` and `ζ η : S → E` such that
  `Λ₁ ⊆ Λ₂` and `∀ (s : Λ₁ᶜ), ζ s = η s`. -/
structure IsPremodifier [MeasurableSpace E] (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  comm_of_subset ⦃Λ₁ Λ₂ : Finset S⦄ ⦃ζ η : S → E⦄ (hΛ : Λ₁ ⊆ Λ₂)
    (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) : ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η

/-- For a premodifier `ρ`, the normalized density relative to the σ-finite reference kernel
`sigmaFiniteLambdaFun` is measurable. -/
lemma IsPremodifier.measurable_div_sigmaFiniteLambda
    (hρ : IsPremodifier ρ) (ν : Measure E) [SigmaFinite ν] :
    ∀ Λ, Measurable
      (fun σ : S → E =>
        ρ Λ σ / ∫⁻ x, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ σ)) := by
  intro Λ
  exact (hρ.measurable Λ).div
    ((hρ.measurable Λ).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)

/-!
### Resampling specifications

Georgii's Notation (1.26) writes the reference kernel as `λ_Λ(dω | η) = λ^Λ(dω_Λ) δ_{η_{S∖Λ}}`:
the volume `Λ` is resampled, the exterior is frozen. `Specification.IsResampling` records exactly
this shape, and is all that the normalization of a premodifier (Georgii, Remark (1.32)) uses
about the reference kernels. Both `Specification.isssd` and, for the second half of Georgii
(8.39), the inhomogeneous `Specification.isssdFamily` are resampling specifications.
-/

variable (γ) in
/-- A specification *resamples volumes* if each finite-volume kernel is the image, under
juxtaposition with the boundary condition, of a measure on the configurations of that volume.

This is the shape of Georgii's reference kernels `λ_Λ` in Notation (1.26). -/
def IsResampling : Prop :=
  ∀ Λ : Finset S, ∃ μ : Measure (Λ → E), ∀ η : S → E, γ Λ η = μ.map (juxt (Λ : Set S) η)

lemma isResampling_isssd (ν : Measure E) [IsProbabilityMeasure ν] :
    IsResampling (isssd (S := S) (E := E) ν) :=
  fun Λ ↦ ⟨Measure.pi fun _ : Λ ↦ ν, fun _ ↦ rfl⟩

/-- Under a resampling kernel, integrands that agree with each other on the configurations
matching the boundary condition off `Λ` have the same integral. -/
lemma IsResampling.lintegral_congr (hγ : IsResampling γ) {Λ : Finset S} {η : S → E}
    {F G : (S → E) → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (h : ∀ ζ : S → E, (∀ s ∉ Λ, ζ s = η s) → F ζ = G ζ) :
    ∫⁻ ζ, F ζ ∂(γ Λ η) = ∫⁻ ζ, G ζ ∂(γ Λ η) := by
  obtain ⟨μ, hμ⟩ := hγ Λ
  rw [hμ η, lintegral_map hF Measurable.juxt, lintegral_map hG Measurable.juxt]
  refine MeasureTheory.lintegral_congr fun ζ ↦ ?_
  exact h _ (juxt_agree_on_compl Λ η ζ)

/-! ### Normalizing a premodifier against a reference specification

**Georgii, Remark (1.32).** If `h` is a pre-modification and `0 < λ_Λ h_Λ < ∞` for all `Λ`, then
`ρ_Λ = h_Λ / λ_Λ h_Λ` is a λ-modification, so `ρ λ_·` is a specification. The partition function
`relZ`, the normalized density `relNorm` and the admissibility predicate `IsRelAdmissible` are
stated for an arbitrary reference specification `γ`; Georgii's λ-versions over the independent
reference `Specification.isssd ν` are the abbreviations `Specification.premodifierZ`,
`Specification.premodifierNorm` and `Specification.IsPremodifierAdmissible` below.
-/

variable (γ ρ) in
/-- The partition function of a density family `ρ` relative to a reference specification `γ`:
`Z_Λ(η) = γ_Λ(ρ_Λ | η)`. `Specification.premodifierZ` is this at `γ = Specification.isssd ν`. -/
noncomputable def relZ (Λ : Finset S) (η : S → E) : ℝ≥0∞ := ∫⁻ x, ρ Λ x ∂(γ Λ η)

variable (γ ρ) in
/-- The normalized density `ρ'_Λ = ρ_Λ / Z_Λ` relative to a reference specification `γ`.
`Specification.premodifierNorm` is this at `γ = Specification.isssd ν`. -/
noncomputable def relNorm (Λ : Finset S) (η : S → E) : ℝ≥0∞ := ρ Λ η / relZ γ ρ Λ η

variable (γ ρ) in
/-- Georgii's λ-admissibility relative to a reference specification: every finite-volume
partition function is nonzero and finite. -/
def IsRelAdmissible : Prop := ∀ (Λ : Finset S) (η : S → E), relZ γ ρ Λ η ≠ 0 ∧ relZ γ ρ Λ η ≠ ⊤

lemma measurable_relZ (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Measurable[cylinderEvents (Λ : Set S)ᶜ] (relZ γ ρ Λ) :=
  Measurable.lintegral_kernel (κ := γ Λ) (f := ρ Λ) (hρ Λ)

lemma measurable_relNorm (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Measurable (relNorm γ ρ Λ) :=
  (hρ Λ).div ((measurable_relZ (γ := γ) hρ Λ).mono cylinderEvents_le_pi le_rfl)

/-- The partition function is constant on the fibres of the reference kernel. -/
lemma relZ_ae_eq (hρ : ∀ Λ, Measurable (ρ Λ)) {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    ∀ᵐ ζ ∂(γ Λ₁ η), relZ γ ρ Λ₂ ζ = relZ γ ρ Λ₂ η := by
  refine (γ.isProper Λ₁).ae_eq_const cylinderEvents_le_pi ?_ η
  refine (measurable_relZ (γ := γ) hρ Λ₂).mono (cylinderEvents_mono ?_) le_rfl
  exact Set.compl_subset_compl.2 (by exact_mod_cast hΛ)

/-- Normalizing against the reference kernel gives total mass one. -/
lemma lintegral_relNorm (hρ : ∀ Λ, Measurable (ρ Λ)) (hZ : IsRelAdmissible γ ρ)
    (Λ : Finset S) (η : S → E) : ∫⁻ ζ, relNorm γ ρ Λ ζ ∂(γ Λ η) = 1 := by
  have hae : ∀ᵐ ζ ∂(γ Λ η), relNorm γ ρ Λ ζ = (relZ γ ρ Λ η)⁻¹ * ρ Λ ζ := by
    filter_upwards [relZ_ae_eq (γ := γ) hρ (Finset.Subset.refl Λ) η] with ζ hζ
    rw [relNorm, hζ, ENNReal.div_eq_inv_mul]
  rw [lintegral_congr_ae hae, lintegral_const_mul _ (hρ Λ)]
  exact ENNReal.inv_mul_cancel (hZ Λ η).1 (hZ Λ η).2

/-- Evaluating the normalized modification `relNorm γ ρ · γ_·` on a measurable set factors the
partition function out of the set integral:
`(ρ'_Λ γ_Λ)(A | η) = Z_Λ(η)⁻¹ ∫_A ρ_Λ dγ_Λ(· | η)`. Only properness of `γ` is used. -/
lemma withDensity_relNorm_apply (hρ : ∀ Λ, Measurable (ρ Λ)) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ((γ Λ η).withDensity (relNorm γ ρ Λ)) A
      = (relZ γ ρ Λ η)⁻¹ * ∫⁻ y in A, ρ Λ y ∂(γ Λ η) := by
  have hZmeas : Measurable[cylinderEvents (Λ : Set S)ᶜ] (relZ γ ρ Λ) :=
    measurable_relZ (γ := γ) hρ Λ
  have hpull :
      ∫⁻ y, (fun y : S → E ↦ (relZ γ ρ Λ y)⁻¹) y *
          (A.indicator fun y : S → E ↦ ρ Λ y) y ∂(γ Λ η) =
        (relZ γ ρ Λ η)⁻¹ *
          ∫⁻ y, (A.indicator fun y : S → E ↦ ρ Λ y) y ∂(γ Λ η) :=
    Specification.lintegral_mul γ Λ
      (f := A.indicator fun y : S → E ↦ ρ Λ y) (g := fun y : S → E ↦ (relZ γ ρ Λ y)⁻¹)
      (Measurable.indicator (hρ Λ) hA) hZmeas.inv
  calc
    ((γ Λ η).withDensity (relNorm γ ρ Λ)) A =
        ∫⁻ y in A, ρ Λ y * (relZ γ ρ Λ y)⁻¹ ∂(γ Λ η) := by
          simp [withDensity_apply _ hA, relNorm, div_eq_mul_inv]
    _ = ∫⁻ y, (relZ γ ρ Λ y)⁻¹ * (A.indicator fun y : S → E ↦ ρ Λ y) y ∂(γ Λ η) := by
          rw [← lintegral_indicator hA]
          simp [Set.indicator_mul_left, mul_comm]
    _ = (relZ γ ρ Λ η)⁻¹ * ∫⁻ y, (A.indicator fun y : S → E ↦ ρ Λ y) y ∂(γ Λ η) := hpull
    _ = (relZ γ ρ Λ η)⁻¹ * ∫⁻ y in A, ρ Λ y ∂(γ Λ η) := by
          simp [lintegral_indicator hA]

/-- Georgii's cocycle (1.31) integrated against the reference kernel: the premodifier identity
holds with one argument averaged over the resampled volume. -/
lemma IsPremodifier.mul_relZ (hγ : IsResampling γ) (hρ : IsPremodifier ρ) {Λ₁ Λ₂ : Finset S}
    (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    ρ Λ₂ η * relZ γ ρ Λ₁ η = ρ Λ₁ η * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η) := by
  rw [relZ, ← lintegral_const_mul _ (hρ.measurable Λ₁), ← lintegral_const_mul _ (hρ.measurable Λ₂)]
  refine hγ.lintegral_congr (measurable_const.mul (hρ.measurable Λ₁))
    (measurable_const.mul (hρ.measurable Λ₂)) fun ζ hζ ↦ ?_
  have := hρ.comm_of_subset (Λ₁ := Λ₁) (Λ₂ := Λ₂) (ζ := ζ) (η := η) hΛ hζ
  rw [mul_comm (ρ Λ₂ η), mul_comm (ρ Λ₁ η)]
  exact this.symm

/-- **Georgii, Remark (1.32).** Normalizing a premodifier against a resampling reference
specification produces a modifier, hence a specification: the normalized family still satisfies
the symmetry of Definition (1.31), hence condition (c) of Proposition (1.30), hence (a).

Specialized to `γ = Specification.isssd ν` this is
`Specification.IsPremodifier.isModifier_premodifierNorm`; it applies just as well to the
inhomogeneous `Specification.isssdFamily`. -/
theorem IsPremodifier.isModifier_relNorm (hγ : IsResampling γ) (hρ : IsPremodifier ρ)
    (hZ : IsRelAdmissible γ ρ) : γ.IsModifier (relNorm γ ρ) := by
  refine (isModifier_iff_ae_eq (γ := γ)).2
    ⟨measurable_relNorm (γ := γ) hρ.measurable,
      lintegral_relNorm (γ := γ) hρ.measurable hZ, fun Λ₁ Λ₂ hΛ η ↦ .of_forall fun ω ↦ ?_⟩
  have hinner : ∫⁻ ζ, relNorm γ ρ Λ₂ ζ ∂(γ Λ₁ ω)
      = (relZ γ ρ Λ₂ ω)⁻¹ * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω) := by
    have hae : ∀ᵐ ζ ∂(γ Λ₁ ω), relNorm γ ρ Λ₂ ζ = (relZ γ ρ Λ₂ ω)⁻¹ * ρ Λ₂ ζ := by
      filter_upwards [relZ_ae_eq (γ := γ) hρ.measurable hΛ ω] with ζ hζ
      rw [relNorm, hζ, ENNReal.div_eq_inv_mul]
    rw [lintegral_congr_ae hae, lintegral_const_mul _ (hρ.measurable Λ₂)]
  change relNorm γ ρ Λ₂ ω = relNorm γ ρ Λ₁ ω * ∫⁻ ζ, relNorm γ ρ Λ₂ ζ ∂(γ Λ₁ ω)
  rw [hinner, relNorm, relNorm, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  have hcancel : (relZ γ ρ Λ₁ ω)⁻¹ * relZ γ ρ Λ₁ ω = 1 :=
    ENNReal.inv_mul_cancel (hZ Λ₁ ω).1 (hZ Λ₁ ω).2
  calc (relZ γ ρ Λ₂ ω)⁻¹ * ρ Λ₂ ω
      = (relZ γ ρ Λ₂ ω)⁻¹ * (ρ Λ₂ ω * ((relZ γ ρ Λ₁ ω)⁻¹ * relZ γ ρ Λ₁ ω)) := by
        rw [hcancel, mul_one]
    _ = (relZ γ ρ Λ₁ ω)⁻¹ * ((relZ γ ρ Λ₂ ω)⁻¹ * (ρ Λ₂ ω * relZ γ ρ Λ₁ ω)) := by ring
    _ = (relZ γ ρ Λ₁ ω)⁻¹ * ((relZ γ ρ Λ₂ ω)⁻¹ * (ρ Λ₁ ω * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω))) := by
        rw [hρ.mul_relZ hγ hΛ ω]
    _ = (relZ γ ρ Λ₁ ω)⁻¹ * ρ Λ₁ ω * ((relZ γ ρ Λ₂ ω)⁻¹ * ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ ω)) := by ring

variable (γ ρ) in
/-- The specification obtained by normalizing a premodifier against a resampling reference
specification: Georgii's `γ = ρ' γ₀` with `ρ'_Λ = ρ_Λ / γ₀_Λ(ρ_Λ)`. -/
noncomputable def premodification (hγ : IsResampling γ) (hρ : IsPremodifier ρ)
    (hZ : IsRelAdmissible γ ρ) : Specification S E :=
  γ.modification (relNorm γ ρ) (hρ.isModifier_relNorm hγ hZ)

lemma premodification_apply (hγ : IsResampling γ) (hρ : IsPremodifier ρ)
    (hZ : IsRelAdmissible γ ρ) (Λ : Finset S) (η : S → E) :
    premodification γ ρ hγ hρ hZ Λ η = (γ Λ η).withDensity (relNorm γ ρ Λ) := rfl

/-!
### Georgii's λ-modification machinery over `isssd`

The Georgii-named layer at the independent reference with a probability spin distribution:
`premodifierZ`, `premodifierNorm` and `IsPremodifierAdmissible` are abbreviations for `relZ`,
`relNorm` and `IsRelAdmissible` at `γ = Specification.isssd ν`, so the whole `rel*` API applies
to them directly.
-/

/-- The *partition function* (normalizing factor) `λ_Λ h_Λ` associated to a density `ρ Λ` and the
independent specification `isssd ν`: `Specification.relZ` at the independent reference. -/
noncomputable abbrev premodifierZ (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  relZ (isssd (S := S) (E := E) ν) ρ Λ η

/-- The normalized density `h_Λ / λ_Λ h_Λ` associated to a premodifier `ρ` and the independent
specification `isssd ν`: `Specification.relNorm` at the independent reference. -/
noncomputable abbrev premodifierNorm (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  relNorm (isssd (S := S) (E := E) ν) ρ Λ η

/-- Georgii's λ-admissibility `0 < λ_Λ h_Λ < ∞` over the independent reference:
`Specification.IsRelAdmissible` at `γ = Specification.isssd ν`. -/
abbrev IsPremodifierAdmissible (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop :=
  IsRelAdmissible (isssd (S := S) (E := E) ν) ρ

/-- Evaluating the normalized premodifier modification on a measurable set factors the boundary
normalization outside the set integral. -/
lemma withDensity_premodifierNorm_apply (ν : Measure E) [IsProbabilityMeasure ν]
    (hρ : IsPremodifier ρ) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ((isssd (S := S) (E := E) ν Λ η).withDensity
        (premodifierNorm (S := S) (E := E) ν ρ Λ)) A =
      (premodifierZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ y in A, ρ Λ y ∂(isssd (S := S) (E := E) ν Λ η) :=
  withDensity_relNorm_apply (γ := isssd (S := S) (E := E) ν) hρ.measurable hA η

/-!
### The σ-finite λ-layer

Georgii's reference measures range over the σ-finite `𝓜(E, ℰ)`. `sigmaFiniteLambdaZ`,
`sigmaFinitePremodifierNorm` and `IsSigmaFiniteLambdaAdmissible` are the partition function,
normalized density and admissibility over the σ-finite reference kernels
`sigmaFiniteLambdaFun ν`, which do not form a `Specification` (they are not Markov unless
`ν univ = 1`), so the `rel*` API does not apply to them; for a probability spin law the two
layers agree (`premodifierZ_eq_sigmaFiniteLambdaZ`,
`premodifierNorm_eq_sigmaFinitePremodifierNorm`,
`isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible`).
-/

/-- The σ-finite-reference partition function associated to `sigmaFiniteLambdaFun`.

This is Georgii's `λ_Λ h_Λ(η)` for a σ-finite reference measure. -/
noncomputable def sigmaFiniteLambdaZ
    (ν : Measure E) [SigmaFinite ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ∫⁻ x, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η)

/-- The normalized density associated to a premodifier and a σ-finite reference measure:
`ρ' Λ η = ρ Λ η / Z_Λ(η)`. -/
noncomputable def sigmaFinitePremodifierNorm
    (ν : Measure E) [SigmaFinite ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ρ Λ η / sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η

/-- Measurability of the normalized σ-finite premodifier density. -/
lemma sigmaFinitePremodifierNorm_measurable
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) :
    ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ) := by
  intro Λ
  have h :
      sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ =
        fun σ ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ σ) := by
    funext σ
    simp [sigmaFinitePremodifierNorm, sigmaFiniteLambdaZ]
  rw [h]
  exact hρ.measurable_div_sigmaFiniteLambda (S := S) (E := E) (ρ := ρ) ν Λ

/-- σ-finite-reference admissibility: all finite-volume partition functions are nonzero and finite.

This is the formal version of Georgii's λ-admissibility condition for the normalized density. -/
def IsSigmaFiniteLambdaAdmissible
    (ν : Measure E) [SigmaFinite ν] (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop :=
  ∀ (Λ : Finset S) (η : S → E),
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η ≠ ⊤

namespace IsSigmaFiniteLambdaAdmissible

lemma ne_zero {ν : Measure E} [SigmaFinite ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η ≠ 0 :=
  (hZ Λ η).1

lemma ne_top {ν : Measure E} [SigmaFinite ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η ≠ ⊤ :=
  (hZ Λ η).2

end IsSigmaFiniteLambdaAdmissible

/-- For probability reference measures, `premodifierZ` is the σ-finite-reference partition
function. -/
lemma premodifierZ_eq_sigmaFiniteLambdaZ (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) :
    premodifierZ (S := S) (E := E) ν ρ Λ η =
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η := by
  rw [sigmaFiniteLambdaZ,
    show sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η = isssd (S := S) (E := E) ν Λ η from
      by rw [sigmaFiniteLambdaFun_eq_isssdFun (ν := ν) Λ]; rfl]
  rfl

/-- For probability reference measures, normalized premodifier admissibility is exactly
σ-finite-reference admissibility specialized to a probability measure. -/
lemma isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible
    (ν : Measure E) [IsProbabilityMeasure ν] (ρ : Finset S → (S → E) → ℝ≥0∞) :
    IsPremodifierAdmissible (S := S) (E := E) ν ρ ↔
      IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ := by
  simp only [IsPremodifierAdmissible, IsRelAdmissible, IsSigmaFiniteLambdaAdmissible,
    premodifierZ_eq_sigmaFiniteLambdaZ (S := S) (E := E) ν ρ]

/-- For probability reference measures, `premodifierNorm` is the σ-finite normalized
premodifier. -/
lemma premodifierNorm_eq_sigmaFinitePremodifierNorm (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) :
    premodifierNorm (S := S) (E := E) ν ρ =
      sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ := by
  funext Λ η
  simp only [premodifierNorm, relNorm, sigmaFinitePremodifierNorm,
    premodifierZ_eq_sigmaFiniteLambdaZ (S := S) (E := E) ν ρ]

/-- The σ-finite-reference partition function depends only on the exterior boundary condition. -/
lemma sigmaFiniteLambdaZ_congr_of_eqOn_compl
    (ν : Measure E) [SigmaFinite ν] {Λ : Finset S} (hρΛ : Measurable (ρ Λ))
    {η₁ η₂ : S → E} (h : ∀ s ∉ Λ, η₁ s = η₂ s) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η₁ =
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η₂ := by
  classical
  have hjuxt : juxt (Λ := (Λ : Set S)) η₁ = juxt (Λ := (Λ : Set S)) η₂ := by
    funext ζ x
    by_cases hx : x ∈ (Λ : Set S)
    · simp [juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η₁) (ζ := ζ) hx,
        juxt_apply_of_mem (Λ := (Λ : Set S)) (η := η₂) (ζ := ζ) hx]
    · have hx' : x ∉ Λ := by
        simpa [Finset.mem_coe] using hx
      simp [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η₁) (ζ := ζ) hx,
        juxt_apply_of_not_mem (Λ := (Λ : Set S)) (η := η₂) (ζ := ζ) hx, h x hx']
  simp only [sigmaFiniteLambdaZ]
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map]
  rw [lintegral_map hρΛ (Measurable.juxt (Λ := (Λ : Set S)) (η := η₁) (𝓔 := mE))]
  simpa [hjuxt] using
    (lintegral_map hρΛ
      (Measurable.juxt (Λ := (Λ : Set S)) (η := η₂) (𝓔 := mE))).symm

/-- Pull the boundary normalization of a σ-finite normalized premodifier outside an integral. -/
lemma lintegral_sigmaFinitePremodifierNorm_mul_eq
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) {Λ : Finset S}
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) (η : S → E) :
    ∫⁻ x, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x * f x
        ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) =
      (sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ x, ρ Λ x * f x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  let Z : Finset S → (S → E) → ℝ≥0∞ :=
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ
  have hZmeas : Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := by
    have h :
        Z Λ = fun a ↦ ∫⁻ b, ρ Λ b ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ a) := by
      funext a
      simp [Z, sigmaFiniteLambdaZ]
    rw [h]
    exact Measurable.lintegral_kernel (κ := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
      (f := ρ Λ) (hρ.measurable Λ)
  have hpull :=
    (isProper_sigmaFiniteLambdaFun (S := S) (E := E) ν Λ).lintegral_mul cylinderEvents_le_pi
      (hf := (hρ.measurable Λ).mul hf) (hg := hZmeas.inv) η
  simpa [sigmaFinitePremodifierNorm, Z, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hpull

/-- Pull the boundary normalization of a σ-finite normalized premodifier outside a set integral. -/
lemma setLIntegral_sigmaFinitePremodifierNorm_eq
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ x in A, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x
        ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) =
      (sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ x in A, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  have h := lintegral_sigmaFinitePremodifierNorm_mul_eq
    (S := S) (E := E) (ρ := ρ) ν hρ (Λ := Λ)
    (f := A.indicator fun _ : S → E => 1) (Measurable.indicator measurable_const hA) η
  let μ : Measure (S → E) := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η
  have hlhs :
      ∫⁻ x, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x *
          A.indicator (fun _ : S → E => 1) x ∂μ =
        ∫⁻ x in A, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x ∂μ := by
    rw [← lintegral_indicator hA]
    congr with x
    by_cases hx : x ∈ A <;> simp [hx]
  have hrhs :
      ∫⁻ x, ρ Λ x * A.indicator (fun _ : S → E => 1) x ∂μ =
        ∫⁻ x in A, ρ Λ x ∂μ := by
    rw [← lintegral_indicator hA]
    congr with x
    by_cases hx : x ∈ A <;> simp [hx]
  simpa [μ, hlhs, hrhs] using h

/-- Evaluating the σ-finite normalized premodifier kernel on a measurable set factors the boundary
normalization outside the set integral. -/
lemma withDensity_sigmaFinitePremodifierNorm_apply
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ((sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity
        (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ)) A =
      (sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ x in A, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  rw [withDensity_apply _ hA]
  exact setLIntegral_sigmaFinitePremodifierNorm_eq
    (S := S) (E := E) (ρ := ρ) ν hρ hA η

/-- The σ-finite normalized premodifier has partition function `1` in every finite volume. -/
lemma lintegral_sigmaFinitePremodifierNorm_eq_one
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (Λ : Finset S) (ξ : S → E) :
    ∫⁻ x, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x
      ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ξ) = 1 := by
  let Z : Finset S → (S → E) → ℝ≥0∞ :=
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ
  have hmul := lintegral_sigmaFinitePremodifierNorm_mul_eq
    (S := S) (E := E) (ρ := ρ) ν hρ (Λ := Λ)
    (f := fun _ : S → E => 1) measurable_const ξ
  have hZξ : Z Λ ξ ≠ 0 ∧ Z Λ ξ ≠ ⊤ := hZ Λ ξ
  calc
    ∫⁻ x, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ x
        ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ξ) =
        (Z Λ ξ)⁻¹ * ∫⁻ x, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ξ) := by
          simpa [Z] using hmul
    _ = (Z Λ ξ)⁻¹ * Z Λ ξ := by simp [Z, sigmaFiniteLambdaZ]
    _ = 1 := ENNReal.inv_mul_cancel hZξ.1 hZξ.2

/-- The normalized finite-volume kernel obtained from a σ-finite reference measure and a
premodifier. It is the density modification of
`sigmaFiniteLambdaFun ν Λ η` with density `sigmaFinitePremodifierNorm ν ρ Λ`.

These kernels are proper because the σ-finite reference λ-kernels are proper and properness is
preserved by density changes. Under `IsSigmaFiniteLambdaAdmissible`, they are also Markov; under a
probability spin law `[IsProbabilityMeasure ν]` (so `sigmaFiniteLambdaFun ν` composes via
`isConsistent_sigmaFiniteLambdaFun`),
**`IsPremodifier.isConsistent_modificationKer_sigmaFinitePremodifierNorm`** gives full DLR
consistency of the normalized modification. -/
noncomputable def sigmaFinitePremodifierKernel
    (ν : Measure E) [SigmaFinite ν] (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : IsPremodifier ρ) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
    (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
    (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ) Λ

/-- Evaluation of `sigmaFinitePremodifierKernel`. -/
lemma sigmaFinitePremodifierKernel_apply
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ)
    (Λ : Finset S) (η : S → E) :
    sigmaFinitePremodifierKernel (S := S) (E := E) ν ρ hρ Λ η =
      (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity
        (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ) := rfl

/-- Under admissibility, each normalized σ-finite premodifier kernel is a probability kernel. -/
lemma isMarkovKernel_sigmaFinitePremodifierKernel
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (Λ : Finset S) :
    IsMarkovKernel (sigmaFinitePremodifierKernel (S := S) (E := E) ν ρ hρ Λ) := by
  refine ⟨?_⟩
  intro ξ
  constructor
  simpa [sigmaFinitePremodifierKernel, modificationKer, withDensity_apply] using
    lintegral_sigmaFinitePremodifierNorm_eq_one
      (S := S) (E := E) (ρ := ρ) ν hρ hZ Λ ξ

/-- Each normalized σ-finite premodifier kernel is proper with respect to the outside-volume
σ-algebra. -/
lemma isProper_sigmaFinitePremodifierKernel
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) (Λ : Finset S) :
    (sigmaFinitePremodifierKernel (S := S) (E := E) ν ρ hρ Λ).IsProper := by
  exact isProper_modificationKer_of_isProper
    (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
    (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
    (fun Λ => isProper_sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
    (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ) Λ

/-!
### Change of variables along `juxt`

Integrating against a reference kernel `λ_Λ(· | η)` is integrating along `juxt Λ η` against the
finite product `ν^Λ` — one application of `MeasureTheory.setLIntegral_map`. The σ-finite form is
the root; the `isssd` form is its specialization to a probability spin law. -/

/-- Rewrite a set integral against the σ-finite reference kernel as an integral over the finite
resampling coordinates. -/
lemma setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt
    (ν : Measure E) [SigmaFinite ν] {Λ₀ : Finset S}
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) {A : Set (S → E)}
    (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ x in A, f x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ₀ η) =
      ∫⁻ ζ : Λ₀ → E in (juxt (Λ := (Λ₀ : Set S)) (η := η)) ⁻¹' A,
        f (juxt (Λ := (Λ₀ : Set S)) (η := η) ζ) ∂(Measure.pi fun _ : Λ₀ => ν) := by
  rw [sigmaFiniteLambdaFun_apply_eq_map ν Λ₀ η]
  simpa using
    (setLIntegral_map (μ := Measure.pi (fun _ : Λ₀ => ν)) (s := A) (f := f)
      (g := juxt (Λ := (Λ₀ : Set S)) (η := η)) hA hf
      (Measurable.juxt (Λ := (Λ₀ : Set S)) (η := η) (𝓔 := mE)))

/-- Rewrite a set integral against `isssd` as an integral over the finite resampling
coordinates. -/
lemma setLIntegral_isssd_eq_setLIntegral_juxt
    (ν : Measure E) [IsProbabilityMeasure ν] {Λ₀ : Finset S}
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) {A : Set (S → E)}
    (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ x in A, f x ∂(isssd (S := S) (E := E) ν Λ₀ η) =
      ∫⁻ ζ : Λ₀ → E in (juxt (Λ := (Λ₀ : Set S)) (η := η)) ⁻¹' A,
        f (juxt (Λ := (Λ₀ : Set S)) (η := η) ζ) ∂(Measure.pi fun _ : Λ₀ => ν) := by
  rw [show (isssd (S := S) (E := E) ν Λ₀) η = sigmaFiniteLambdaFun (S := S) (E := E) ν Λ₀ η from
    by rw [sigmaFiniteLambdaFun_eq_isssdFun (ν := ν) Λ₀]; rfl]
  exact setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt ν hf hA η

/-- Integrating against `isssd ν Δ (· | τ)` is integrating along `juxt Δ τ` against `ν^Δ`:
the full-integral change of variables. -/
lemma lintegral_isssd_eq {ν : Measure E} [IsProbabilityMeasure ν] (Δ : Finset S) (τ : S → E)
    {g : (S → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ σ, g σ ∂(isssd ν Δ τ) =
      ∫⁻ ζ, g (juxt (Δ : Set S) τ ζ) ∂(Measure.pi fun _ : Δ ↦ ν) := by
  simpa using setLIntegral_isssd_eq_setLIntegral_juxt (S := S) (E := E) ν hg .univ τ

/-- Premodifier cocycle identity integrated over a σ-finite finite-volume resampling. -/
lemma IsPremodifier.mul_setLIntegral_sigmaFiniteLambdaFun_eq
    (ν : Measure E) [SigmaFinite ν] (hρ : IsPremodifier ρ) {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂)
    {A : Set (S → E)} (hA : MeasurableSet A) (ξ : S → E) :
    ρ Λ₂ ξ * ∫⁻ ζ in A, ρ Λ₁ ζ ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ₁ ξ) =
      ρ Λ₁ ξ * ∫⁻ ζ in A, ρ Λ₂ ζ ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ₁ ξ) := by
  let J : (Λ₁ → E) → (S → E) := juxt (Λ := (Λ₁ : Set S)) (η := ξ)
  let s : Set (Λ₁ → E) := J ⁻¹' A
  let μ : Measure (Λ₁ → E) := Measure.pi fun _ : Λ₁ => ν
  have hI := setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt
    (S := S) (E := E) ν (Λ₀ := Λ₁) (hρ.measurable Λ₁) hA ξ
  have hH := setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt
    (S := S) (E := E) ν (Λ₀ := Λ₁) (hρ.measurable Λ₂) hA ξ
  have hpoint (ζ : Λ₁ → E) : ρ Λ₂ ξ * ρ Λ₁ (J ζ) = ρ Λ₁ ξ * ρ Λ₂ (J ζ) := by
    have hrestrict : ∀ s ∉ Λ₁, J ζ s = ξ s := by
      intro s hs
      simpa [J] using (juxt_agree_on_compl (Λ := Λ₁) (η := ξ) (ζ := ζ) s hs)
    simpa [J, mul_comm, mul_left_comm, mul_assoc] using
      (hρ.comm_of_subset (Λ₁ := Λ₁) (Λ₂ := Λ₂) (ζ := J ζ) (η := ξ) hΛ hrestrict).symm
  have hf₁ : Measurable fun ζ : Λ₁ → E => ρ Λ₁ (J ζ) :=
    (hρ.measurable Λ₁).comp (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))
  have hf₂ : Measurable fun ζ : Λ₁ → E => ρ Λ₂ (J ζ) :=
    (hρ.measurable Λ₂).comp (Measurable.juxt (Λ := (Λ₁ : Set S)) (η := ξ) (𝓔 := mE))
  rw [hI, hH]
  calc
    ρ Λ₂ ξ * ∫⁻ ζ in s, ρ Λ₁ (J ζ) ∂μ =
        ∫⁻ ζ in s, ρ Λ₂ ξ * ρ Λ₁ (J ζ) ∂μ := by
          simpa [s, μ] using (lintegral_const_mul (μ := μ.restrict s) (ρ Λ₂ ξ) hf₁).symm
    _ = ∫⁻ ζ in s, ρ Λ₁ ξ * ρ Λ₂ (J ζ) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards with ζ
          exact hpoint ζ
    _ = ρ Λ₁ ξ * ∫⁻ ζ in s, ρ Λ₂ (J ζ) ∂μ := by
          simpa [s, μ] using lintegral_const_mul (μ := μ.restrict s) (ρ Λ₁ ξ) hf₂

/-- Set integrals against the σ-finite reference kernel over `Λ` are measurable with respect to
the outside of `Λ`. -/
lemma measurable_setLIntegral_sigmaFiniteLambdaFun
    (ν : Measure E) [SigmaFinite ν] {Λ : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet A) {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    Measurable[cylinderEvents (Λ : Set S)ᶜ]
      (fun η : S → E => ∫⁻ ζ in A, f ζ ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η)) := by
  simpa [lintegral_indicator hA] using
    (Measurable.lintegral_kernel (κ := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
      (f := A.indicator f) (Measurable.indicator hf hA))

/-!
### Georgii, Remark (1.32), headline statements

The single proof is `Specification.IsPremodifier.isModifier_relNorm` over an arbitrary
resampling reference; the statements below are its specializations to the independent reference
`Specification.isssd ν` and, through the bridge lemmas, to the σ-finite presentation
`sigmaFiniteLambdaFun ν` of the same kernels at a probability spin law. The genuinely σ-finite
non-zero case is `Specification.isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero`
in `GibbsMeasure/Specification/Rescaling.lean`, obtained by the rescaling of Georgii,
Remark (1.28)(3). -/

/-- **Georgii, Remark (1.32) over `isssd`.** The normalized premodifier density is a modifier of
the independent specification. -/
lemma IsPremodifier.isModifier_premodifierNorm (ν : Measure E) [IsProbabilityMeasure ν]
    (hρ : IsPremodifier ρ) (hZ : IsPremodifierAdmissible (S := S) (E := E) ν ρ) :
    (isssd (S := S) (E := E) ν).IsModifier (premodifierNorm (S := S) (E := E) ν ρ) :=
  hρ.isModifier_relNorm (isResampling_isssd ν) hZ

/-- **Georgii, Remark (1.32) over `isssd`,** consistency form: the normalized premodifier density
gives a consistent modification of the independent specification. -/
lemma IsPremodifier.isConsistent_modificationKer_premodifierNorm
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hρ : IsPremodifier ρ) (hZ : IsPremodifierAdmissible (S := S) (E := E) ν ρ) :
    IsConsistent
      (modificationKer (γ := isssd (S := S) (E := E) ν)
        (ρ := premodifierNorm (S := S) (E := E) ν ρ)
        (measurable_relNorm (γ := isssd (S := S) (E := E) ν) hρ.measurable)) :=
  (hρ.isModifier_relNorm (isResampling_isssd ν) hZ).isConsistent

/-- **Georgii, Remark (1.32) for the σ-finite presentation of a probability spin law.** DLR
consistency of the normalized modification of `sigmaFiniteLambdaFun ν`, from
`Specification.IsPremodifier.isModifier_relNorm` through the bridge lemmas. -/
lemma IsPremodifier.isConsistent_modificationKer_sigmaFinitePremodifierNorm
    {ν : Measure E} [IsProbabilityMeasure ν] (hρ : IsPremodifier ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    IsConsistent
      (modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
        (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)) := by
  have hZ' : IsPremodifierAdmissible (S := S) (E := E) ν ρ :=
    (isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ).2 hZ
  have hcons := (hρ.isModifier_relNorm (γ := isssd (S := S) (E := E) ν)
    (isResampling_isssd ν) hZ').isConsistent
  have hkey : modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
        (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)
      = modificationKer (γ := ⇑(isssd (S := S) (E := E) ν))
        (ρ := relNorm (isssd (S := S) (E := E) ν) ρ)
        (measurable_relNorm (γ := isssd (S := S) (E := E) ν) hρ.measurable) := by
    funext Λ
    refine Kernel.ext fun η ↦ ?_
    rw [modificationKer_apply, modificationKer_apply,
      show sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η = isssd (S := S) (E := E) ν Λ η from
        by rw [sigmaFiniteLambdaFun_eq_isssdFun (ν := ν) Λ]; rfl,
      show sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ
        = relNorm (isssd (S := S) (E := E) ν) ρ Λ from
        congrFun (premodifierNorm_eq_sigmaFinitePremodifierNorm
          (S := S) (E := E) ν ρ).symm Λ]
  rw [hkey]
  exact hcons

end Modifier

/-- The independent kernel on a singleton resamples the single coordinate: `λ_{i}(·|ω)` is the
image of `ν` under `x ↦ update ω i x`. -/
lemma isssd_singleton_eq_map {S E : Type*} [DecidableEq S] [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (i : S) (ω : S → E) :
    isssd (S := S) ν {i} ω = ν.map (Function.update ω i) := by
  have hpi : (Measure.pi fun _ : (({i} : Finset S) : Type _) ↦ ν) =
      ν.map (MeasurableEquiv.funUnique (({i} : Finset S) : Type _) E).symm :=
    ((measurePreserving_funUnique ν _).symm _).map_eq.symm
  change Measure.map (juxt (({i} : Finset S) : Set S) ω)
    (Measure.pi fun _ : (({i} : Finset S) : Type _) ↦ ν) = _
  rw [hpi, Measure.map_map Measurable.juxt
    (MeasurableEquiv.funUnique (({i} : Finset S) : Type _) E).symm.measurable]
  congr 1
  funext y j
  by_cases hj : j = i
  · subst hj
    rw [Function.comp_apply, juxt_apply_of_mem (by simp), Function.update_self]
    rfl
  · rw [Function.comp_apply, juxt_apply_of_not_mem (by simpa using hj), Function.update_of_ne hj]

section IsssdBind

variable {S E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {μ : Measure (S → E)}

lemma measurable_isssd_coe (Λ : Finset S) : Measurable (isssd (S := S) ν Λ) :=
  (isssd ν Λ).measurable.mono cylinderEvents_le_pi le_rfl
/-- Resampling `Λ₂` and then `Λ₁` is resampling `Λ₁ ∪ Λ₂` (strong consistency of `isssd`, as an
identity of measures). -/
lemma isssd_bind_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) (η : S → E) :
    (isssd ν Λ₂ η).bind (isssd ν Λ₁) = isssd ν (Λ₁ ∪ Λ₂) η := by
  have := DFunLike.congr_fun (isssd_comp_isssd (S := S) (ν := ν) Λ₁ Λ₂) η
  simp only [Kernel.comp_apply, Kernel.comap_apply, id_eq] at this
  rw [← this]
  congr 1
instance isProbabilityMeasure_bind_isssd [IsProbabilityMeasure μ] (Λ : Finset S) :
    IsProbabilityMeasure (μ.bind (isssd ν Λ)) :=
  ⟨by rw [Measure.bind_apply MeasurableSet.univ (measurable_isssd_coe Λ).aemeasurable,
    lintegral_congr fun η ↦ measure_univ (μ := isssd ν Λ η), lintegral_one, measure_univ]⟩

end IsssdBind

end Specification

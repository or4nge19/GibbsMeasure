module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import GibbsMeasure.KolmogorovExtension4.ProductMeasure
public import GibbsMeasure.Prereqs.CylinderEvents
public import GibbsMeasure.Prereqs.Filtration.Consistent
public import GibbsMeasure.Prereqs.Juxt
public import GibbsMeasure.Prereqs.MeasureExt
public import GibbsMeasure.Prereqs.Kernel.CondExp
public import GibbsMeasure.Mathlib.Probability.Kernel.Proper
public import GibbsMeasure.Prereqs.SquareCylinders


/-!
# Gibbs measures

This file defines Gibbs measures.
-/

@[expose] public section

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

variable {S E : Type*} {mE : MeasurableSpace E} {Λ₁ Λ₂ : Finset S}

/-- A family of boundary-condition kernels is consistent if
`γ Λ₁ ∘ₖ γ Λ₂ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.

This is Georgii's condition `γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ`, written in Mathlib's kernel-composition
order and with the harmless `comap` needed because the source σ-algebras are nested boundary
σ-algebras. -/
def IsConsistent (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂

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
  coe_injective' γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

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
  coe_injective' γ₁ γ₂ h := by
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

section IsIndep

/-- An independent specification is a specification `γ` where `γ Λ₁ ∘ₖ γ Λ₂ = γ (Λ₁ ∪ Λ₂)` for all
`Λ₁ Λ₂`. -/
def IsIndep (γ : Specification S E) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄ [DecidableEq S], (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = (γ (Λ₁ ∪ Λ₂)).comap id
      (measurable_id'' <| by
        gcongr
        exact Finset.subset_union_right)

end IsIndep

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
### Probability-measure specializations

In the Vol. II / infinite-volume development, Gibbs measures are probability measures.
These lemmas avoid threading `[IsFiniteMeasure μ]` explicitly.
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
  classical
  have hmeas_rect : MeasurableSet ((s : Set S).pi t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  rw [Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)) hmeas_rect]
  by_cases hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  · rw [preimage_juxt_squareCylinder_eq_univ_pi_of_forall (S := S) (E := E) hP]
    rw [if_pos hP]
  · rw [preimage_juxt_squareCylinder_eq_empty_of_not_forall (S := S) (E := E) hP]
    have hP' : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := by
      intro h
      exact hP (fun i hi hiΛ => h i (by simpa using hi) (by simpa using hiΛ))
    simp [hP']

/-- Measurability, as a function of the boundary condition, of a `juxt`-mapped product measure
applied to a finite square cylinder. -/
lemma measurable_map_juxt_apply_squareCylinder
    (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      fun η : S → E =>
        (Measure.map (juxt (Λ := (Λ : Set S)) η) (Measure.pi fun _ : Λ ↦ ν))
          ((s : Set S).pi t) := by
  classical
  let P : (S → E) → Prop := fun η =>
    ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  let c : ℝ≥0∞ :=
    (Measure.pi fun _ : Λ ↦ ν)
      (Set.univ.pi (fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ))
  have h_eval :
      (fun η : S → E =>
          (Measure.map (juxt (Λ := (Λ : Set S)) η) (Measure.pi fun _ : Λ ↦ ν))
            ((s : Set S).pi t)) =
        fun η => ite (P η) c 0 := by
    funext η
    simpa [P, c] using map_juxt_apply_squareCylinder (S := S) (E := E) ν Λ s t ht η
  have hP : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ] {η | P η} := by
    simpa [P] using measurableSet_forall_mem_not_mem (S := S) (E := E) Λ s ht
  letI : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ
  haveI : DecidablePred P := fun η => Classical.propDecidable (P η)
  simpa [h_eval] using
    (Measurable.ite (p := P) (hp := by simpa using hP) measurable_const measurable_const)

lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) := by
  classical -- needed for decidability
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  let μ' : (S → E) → Measure (S → E) := fun η ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η)
  haveI : ∀ η, IsProbabilityMeasure (μ' η) := by
    intro η
    haveI : IsProbabilityMeasure (Measure.pi (fun _ : Λ ↦ ν)) := by infer_instance
    exact Measure.isProbabilityMeasure_map
      (μ := Measure.pi (fun _ : Λ ↦ ν))
      (f := juxt (Λ := (Λ : Set S)) (η := η))
      (hf := (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)).aemeasurable)
  refine (Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (μ := μ') (S := C)
    (hgen := hgen) (hpi := hC_pi) ?_)
  intro A hA
  rcases hA with ⟨s, t, ht, rfl⟩
  have ht_meas : ∀ i : S, MeasurableSet (t i) := by
    simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
  simpa [μ'] using
    measurable_map_juxt_apply_squareCylinder (S := S) (E := E) ν Λ s t ht_meas

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps -fullyApplied]
def isssdFun (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

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

/-- If the boundary condition satisfies all outside-volume constraints, the pullback of a square
cylinder under `juxt` is the corresponding coordinate box on the resampled volume. -/
lemma preimage_juxt_squareCylinder_of_forall
    [DecidableEq S] {Λ s : Finset S} {t : S → Set E} {η : S → E}
    (hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) :
    (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) =
      Set.univ.pi (fun j : Λ => if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
  exact preimage_juxt_squareCylinder_eq_univ_pi_of_forall (S := S) (E := E) hP

/-- If the boundary condition violates an outside-volume constraint, the pullback of the square
cylinder under `juxt` is empty. -/
lemma preimage_juxt_squareCylinder_of_not_forall
    {Λ s : Finset S} {t : S → Set E} {η : S → E}
    (hP : ¬ ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) :
    (juxt (Λ : Set S) η) ⁻¹' ((s : Set S).pi t) = (∅ : Set (Λ → E)) := by
  exact preimage_juxt_squareCylinder_eq_empty_of_not_forall (S := S) (E := E) hP

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

/-- The coordinate restriction to any set of sites is measurable. -/
lemma measurable_restrict_sites (Δ : Set S) :
    Measurable (Set.restrict (π := fun _ : S ↦ E) Δ) := by
  rw [measurable_pi_iff]
  intro i
  simpa [Set.restrict] using (measurable_pi_apply (i : S))

omit [IsProbabilityMeasure ν] in
/-- A map by `juxt` factors outside-volume events as an indicator of the boundary condition. -/
lemma map_juxt_inter_restrict_compl_preimage
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet A)
    {C : Set (((Λ : Set S)ᶜ : Set S) → E)} (hC : MeasurableSet C) (x : S → E) :
    (Measure.map (juxt (Λ := (Λ : Set S)) x) (Measure.pi fun _ : Λ ↦ ν))
        (A ∩ (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C) =
      ((Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C).indicator 1 x *
        (Measure.map (juxt (Λ := (Λ : Set S)) x) (Measure.pi fun _ : Λ ↦ ν)) A := by
  let J : (Λ → E) → (S → E) := juxt (Λ := (Λ : Set S)) x
  let B : Set (S → E) := (Set.restrict (π := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) ⁻¹' C
  have hB : MeasurableSet B := hC.preimage (measurable_restrict_sites (S := S) (E := E) _)
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

/-- The independent finite-volume kernels are proper. -/
lemma isProper_isssdFun (Λ : Finset S) : (isssdFun (S := S) (E := E) ν Λ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB x
  change (Measure.map (juxt Λ x) (Measure.pi fun _ : Λ ↦ ν)) (A ∩ B) =
    B.indicator 1 x * (Measure.map (juxt Λ x) (Measure.pi fun _ : Λ ↦ ν)) A
  let Δ : Set S := (Λ : Set S)ᶜ
  have hBcomap :
      MeasurableSet[
          MeasurableSpace.comap (Set.restrict (π := fun _ : S ↦ E) Δ)
            (inferInstance : MeasurableSpace (Δ → E))] B := by
    rw [← MeasureTheory.cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := Δ)]
    exact hB
  rcases hBcomap with ⟨C, hC, rfl⟩
  exact map_juxt_inter_restrict_compl_preimage (S := S) (E := E) ν Λ hA hC x

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

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  exact (isssd (S := S) (E := E) ν).isProper

end ISSSD

section ProductMeasure

/-- Product measure of a finite square cylinder. -/
lemma productMeasure_apply_squareCylinder
    (ν : Measure E) [IsProbabilityMeasure ν] (s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    productMeasure (fun _ : S ↦ ν) ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
  simpa using
    (MeasureTheory.productMeasure_boxes (μ := fun _ : S ↦ ν) (s := s) (t := t)
      (mt := fun i _ => ht i))

/-- The outside-`Λ` part of a finite square cylinder as a finite-coordinate box. -/
lemma setOf_forall_finset_not_mem_eq_pi_sdiff
    [DecidableEq S] (Λ s : Finset S) (t : S → Set E) :
    {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ((s \ Λ : Finset S) : Set S).pi t := by
  ext η
  simp [Set.mem_pi]

/-- Product-measure mass of the outside-`Λ` constraints from a finite square cylinder. -/
lemma productMeasure_apply_forall_finset_not_mem
    [DecidableEq S] (ν : Measure E) [IsProbabilityMeasure ν] (Λ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    productMeasure (fun _ : S ↦ ν) {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ∏ i ∈ s \ Λ, ν (t i) := by
  rw [setOf_forall_finset_not_mem_eq_pi_sdiff (S := S) (E := E) Λ s t]
  exact productMeasure_apply_squareCylinder (S := S) (E := E) ν (s \ Λ) t ht

/-- Integrating one ISSSD square-cylinder kernel against the product law reproduces the product
law on that square cylinder. -/
lemma lintegral_isssd_productMeasure_apply_squareCylinder
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    ∫⁻ η, isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)
        ∂productMeasure (fun _ : S ↦ ν) =
      productMeasure (fun _ : S ↦ ν) ((s : Set S).pi t) := by
  classical
  let P : (S → E) → Prop := fun η => ∀ i ∈ s, i ∉ Λ → η i ∈ t i
  have h_eval :
      (fun η : S → E => isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)) =
        fun η => ite (P η) (∏ i ∈ s ∩ Λ, ν (t i)) 0 := by
    funext η
    simpa [P, isssd_apply, isssdFun_apply, Finset.coe_sort_coe] using
      (isssdFun_apply_squareCylinder (ν := ν) (mE := mE) Λ s t ht η)
  have hP :
      productMeasure (fun _ : S ↦ ν) {η : S → E | P η} = ∏ i ∈ s \ Λ, ν (t i) := by
    simpa [P] using
      (productMeasure_apply_forall_finset_not_mem (S := S) (E := E) ν Λ s t ht)
  calc
    ∫⁻ η, isssd (S := S) (E := E) ν Λ η ((s : Set S).pi t)
          ∂productMeasure (fun _ : S ↦ ν) =
        (∏ i ∈ s ∩ Λ, ν (t i)) *
          productMeasure (fun _ : S ↦ ν) {η : S → E | P η} := by
          rw [h_eval]
          exact lintegral_ite_const_eq_mul (μ := productMeasure (fun _ : S ↦ ν))
            (p := P) (measurableSet_forall_not_mem (S := S) (E := E) Λ s (t := t) ht) _
    _ = (∏ i ∈ s ∩ Λ, ν (t i)) * (∏ i ∈ s \ Λ, ν (t i)) := by rw [hP]
    _ = ∏ i ∈ s, ν (t i) := by
          exact Finset.prod_inter_mul_prod_diff s Λ fun i => ν (t i)
    _ = productMeasure (fun _ : S ↦ ν) ((s : Set S).pi t) := by
          rw [productMeasure_apply_squareCylinder (S := S) (E := E) ν s t ht]

/-- The product law has total mass one after binding an ISSSD kernel. -/
lemma productMeasure_bind_isssd_apply_univ
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    ((productMeasure (fun _ : S ↦ ν)).bind (isssd (S := S) (E := E) ν Λ)) Set.univ = 1 := by
  have huniv_meas : MeasurableSet (Set.univ : Set (S → E)) := MeasurableSet.univ
  have hκ :
      AEMeasurable (fun η : S → E => isssd (S := S) (E := E) ν Λ η)
        (productMeasure (fun _ : S ↦ ν)) :=
    ((isssd (S := S) (E := E) ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
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
  simp [isssdFun_apply, h_integrand, MeasureTheory.lintegral_const]

/-- The product law is invariant under resampling any finite volume from the ISSSD kernel. -/
lemma productMeasure_bind_isssd
    (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    (productMeasure (fun _ : S ↦ ν)).bind (isssd (S := S) (E := E) ν Λ) =
      productMeasure (fun _ : S ↦ ν) := by
  let μ : Measure (S → E) := productMeasure (fun _ : S ↦ ν)
  have hκ :
      AEMeasurable (fun η : S → E => isssd (S := S) (E := E) ν Λ η) μ :=
    ((isssd (S := S) (E := E) ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by simpa [C] using isPiSystem_squareCylindersMeas S E
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using generateFrom_squareCylindersMeas S E
  have huniv : (Set.univ : Set (S → E)) ∈ C := by simpa [C] using univ_mem_squareCylindersMeas S E
  have hμ_univ : (μ.bind (isssd (S := S) (E := E) ν Λ)) Set.univ ≠ ∞ := by
    rw [show μ = productMeasure (fun _ : S ↦ ν) from rfl]
    rw [productMeasure_bind_isssd_apply_univ (S := S) (E := E) ν Λ]
    simp
  refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
    (μ := μ.bind (isssd (S := S) (E := E) ν Λ)) (ν := μ)
    (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hμ_univ) ?_
  intro A hA
  rcases hA with ⟨s, t, ht, rfl⟩
  have ht_meas : ∀ i : S, MeasurableSet (t i) := by
    simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
  have h_rect_meas : MeasurableSet ((s : Set S).pi t) :=
    MeasurableSet.pi s.countable_toSet (fun i _ => ht_meas i)
  rw [Measure.bind_apply (m := μ) (f := isssd (S := S) (E := E) ν Λ)
    (s := (s : Set S).pi t) h_rect_meas hκ]
  simpa [μ] using lintegral_isssd_productMeasure_apply_squareCylinder
    (S := S) (E := E) ν Λ s t ht_meas

/-- The product measure `ν ^ S` is a `isssd μ`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_productMeasure (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsGibbsMeasure (productMeasure fun _ : S ↦  ν) := by
  classical
  intro Λ
  let μ : Measure (S → E) := productMeasure (fun _ : S ↦ ν)
  haveI : IsFiniteMeasure μ := inferInstance
  have hproper : (isssd (S := S) (E := E) ν).IsProper :=
    Specification.IsProper.isssd (S := S) (E := E) (mE := mE) (ν := ν)
  have hπ : (isssd (S := S) (E := E) ν Λ).IsProper := hproper Λ
  haveI : IsMarkovKernel (isssd (S := S) (E := E) ν Λ) := by
    infer_instance
  haveI : SigmaFinite (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))) := by
    infer_instance
  have h_bind : μ.bind (isssd (S := S) (E := E) ν Λ) = μ := by
    simpa [μ] using productMeasure_bind_isssd (S := S) (E := E) ν Λ
  have : Kernel.IsCondExp (isssd (S := S) (E := E) ν Λ) μ := by
    exact (Kernel.isCondExp_iff_bind_eq_left (μ := μ) (π := isssd (S := S) (E := E) ν Λ)
      hπ (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)ᶜ))).2 h_bind
  simpa [μ] using this

end ProductMeasure

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

@[simp] lemma modificationKer_one (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ 1 (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

lemma isProper_modificationKer {γ : Specification S E}
    (hρ : ∀ Λ, Measurable (ρ Λ)) :
    ∀ Λ, (modificationKer γ ρ hρ Λ).IsProper := by
  intro Λ
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB η
  rw [modificationKer_apply, withDensity_apply _ hA,
    withDensity_apply _ (hA.inter <| cylinderEvents_le_pi _ hB),
    Specification.setLIntegral_inter_eq_indicator_mul_setLIntegral γ _ (hρ _) hA hB]

/-- A modifier of a specification `γ` is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `γ.modificationKer ρ` (informally, `ρ * γ`) is consistent.
* The modified kernels are still probability kernels and proper, so they again form a genuine
  specification. -/
@[mk_iff]
structure IsModifier (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  isMarkovKernel Λ : IsMarkovKernel (modificationKer γ ρ measurable Λ)
  isProper Λ : (modificationKer γ ρ measurable Λ).IsProper
  isConsistent : IsConsistent (modificationKer γ ρ measurable)

@[simp] lemma IsModifier.one' : γ.IsModifier (fun _Λ _η ↦ 1) where
  measurable _ := measurable_const
  isConsistent := by simpa using γ.isConsistent
  isMarkovKernel Λ := by
    have hker : modificationKer γ (fun _Λ _η ↦ 1) (fun _Λ ↦ measurable_const) Λ = γ Λ := by
      ext η A hA
      simp [modificationKer]
    simpa [hker] using γ.isMarkovKernel' Λ
  isProper Λ := by
    have hker : modificationKer γ (fun _Λ _η ↦ 1) (fun _Λ ↦ measurable_const) Λ = γ Λ := by
      ext η A hA
      simp [modificationKer]
    simpa [hker] using γ.isProper' Λ

@[simp] lemma IsModifier.one : γ.IsModifier 1 := .one'

lemma IsModifier.comp_eq (hρ : γ.IsModifier ρ) ⦃Λ₁ Λ₂⦄ (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    (fun ξ ↦ (γ Λ₁ ξ).withDensity (ρ Λ₁)) ∘ₘ (γ Λ₂ η).withDensity (ρ Λ₂)
      = (γ Λ₂ η).withDensity (ρ Λ₂) := by
  simpa [IsConsistent, modificationKer, Kernel.ext_iff, Kernel.comp_apply, Measure.ext_iff]
    using DFunLike.congr_fun (hρ.isConsistent hΛ) η

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
  isProper Λ := by
    simpa [modificationKer, modification_apply, Pi.mul_apply, MeasureTheory.withDensity_mul,
      hρ₁.measurable, hρ₂.measurable]
      using hρ₂.isProper Λ

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

/-- For a premodifier `ρ`, the normalized density
`σ ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)` is measurable. -/
lemma IsPremodifier.measurable_div_isssd
    (hρ : IsPremodifier ρ) (ν : Measure E) [IsProbabilityMeasure ν] :
    ∀ Λ, Measurable (fun σ : S → E ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)) := by
  intro Λ
  -- `σ ↦ ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ)` is measurable by the kernel measurability API.
  exact (hρ.measurable Λ).div ((hρ.measurable Λ).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)

/-! ### Normalization of a premodifier (Georgii 4.6 ⇒ DLR consistency) -/

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- The *partition function* (normalizing factor) associated to a density `ρ Λ` and the independent
specification `isssd ν`. -/
noncomputable def premodifierZ
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ∫⁻ x, ρ Λ x ∂(isssd (S := S) (E := E) ν Λ η)

/-- The normalized density associated to a premodifier `ρ`:
`ρ' Λ η = ρ Λ η / Z_Λ(η)` where `Z_Λ(η) = ∫ ρ Λ x d(isssd ν Λ η)`. -/
noncomputable def premodifierNorm
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ρ Λ η / premodifierZ (S := S) (E := E) ν ρ Λ η

lemma premodifierNorm_measurable (hρ : IsPremodifier ρ) :
    ∀ Λ, Measurable (premodifierNorm (S := S) (E := E) ν ρ Λ) := by
  intro Λ
  simpa [premodifierNorm, premodifierZ] using
    (hρ.measurable_div_isssd (S := S) (E := E) (ρ := ρ) ν Λ)

lemma premodifierZ_congr_of_eqOn_compl
    {Λ : Finset S} (hρΛ : Measurable (ρ Λ)) {η₁ η₂ : S → E} (h : ∀ s ∉ Λ, η₁ s = η₂ s) :
    premodifierZ (S := S) (E := E) ν ρ Λ η₁ = premodifierZ (S := S) (E := E) ν ρ Λ η₂ := by
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
  simp [premodifierZ, isssdFun_apply]
  rw [lintegral_map hρΛ (Measurable.juxt (Λ := (Λ : Set S)) (η := η₁) (𝓔 := mE))]
  simpa [hjuxt] using
    (lintegral_map hρΛ (Measurable.juxt (Λ := (Λ : Set S)) (η := η₂) (𝓔 := mE))).symm

/-- Rewrite a set integral against `isssd` as an integral over the finite resampling coordinates. -/
lemma setLIntegral_isssd_eq_setLIntegral_juxt
    {Λ₀ Λ : Finset S} (hρΛ : Measurable (ρ Λ)) {A : Set (S → E)}
    (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ x in A, ρ Λ x ∂(isssd (S := S) (E := E) ν Λ₀ η) =
      ∫⁻ ζ : Λ₀ → E in (juxt (Λ := (Λ₀ : Set S)) (η := η)) ⁻¹' A,
        ρ Λ (juxt (Λ := (Λ₀ : Set S)) (η := η) ζ) ∂(Measure.pi fun _ : Λ₀ => ν) := by
  simp [isssdFun_apply]
  simpa using
    (setLIntegral_map (μ := Measure.pi (fun _ : Λ₀ => ν)) (s := A) (f := ρ Λ)
      (g := juxt (Λ := (Λ₀ : Set S)) (η := η)) hA hρΛ
      (Measurable.juxt (Λ := (Λ₀ : Set S)) (η := η) (𝓔 := mE)))

/-- Premodifier cocycle identity integrated over an independent finite-volume resampling. -/
lemma IsPremodifier.mul_setLIntegral_isssd_eq
    (hρ : IsPremodifier ρ) {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂)
    {A : Set (S → E)} (hA : MeasurableSet A) (ξ : S → E) :
    ρ Λ₂ ξ * ∫⁻ ζ in A, ρ Λ₁ ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ) =
      ρ Λ₁ ξ * ∫⁻ ζ in A, ρ Λ₂ ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ) := by
  let J : (Λ₁ → E) → (S → E) := juxt (Λ := (Λ₁ : Set S)) (η := ξ)
  let s : Set (Λ₁ → E) := J ⁻¹' A
  let μ : Measure (Λ₁ → E) := Measure.pi fun _ : Λ₁ => ν
  have hI := setLIntegral_isssd_eq_setLIntegral_juxt
    (S := S) (E := E) (ρ := ρ) ν (Λ₀ := Λ₁) (Λ := Λ₁) (hρ.measurable Λ₁) hA ξ
  have hH := setLIntegral_isssd_eq_setLIntegral_juxt
    (S := S) (E := E) (ρ := ρ) ν (Λ₀ := Λ₁) (Λ := Λ₂) (hρ.measurable Λ₂) hA ξ
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

/-- The normalized premodifier has partition function `1` in every finite volume. -/
lemma lintegral_premodifierNorm_eq_one (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤)
    (Λ : Finset S) (ξ : S → E) :
    ∫⁻ x, premodifierNorm (S := S) (E := E) ν ρ Λ x
      ∂(isssd (S := S) (E := E) ν Λ ξ) = 1 := by
  let Z : Finset S → (S → E) → ℝ≥0∞ := premodifierZ (S := S) (E := E) ν ρ
  have hZmeasΛ : Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := by
    simpa [Z, premodifierZ] using
      (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ))
        (f := ρ Λ) (hρ.measurable Λ))
  have hpull :=
    Specification.lintegral_mul (isssd (S := S) (E := E) ν)
      (Λ := Λ) (η₀ := ξ) (f := ρ Λ) (g := fun x : S → E => (Z Λ x)⁻¹)
      (hf := hρ.measurable Λ) (hg := hZmeasΛ.inv)
  have hZξ : Z Λ ξ ≠ 0 ∧ Z Λ ξ ≠ ⊤ := hZ Λ ξ
  calc
    ∫⁻ x, premodifierNorm (S := S) (E := E) ν ρ Λ x ∂(isssd (S := S) (E := E) ν Λ ξ)
        = (Z Λ ξ)⁻¹ * ∫⁻ x, ρ Λ x ∂(isssd (S := S) (E := E) ν Λ ξ) := by
            simpa [premodifierNorm, Z, div_eq_mul_inv, mul_assoc, mul_left_comm,
              mul_comm] using hpull
    _ = (Z Λ ξ)⁻¹ * Z Λ ξ := by simp [Z, premodifierZ]
    _ = 1 := ENNReal.inv_mul_cancel hZξ.1 hZξ.2

/-- Evaluating the normalized premodifier modification on a measurable set factors the boundary
normalization outside the set integral. -/
lemma withDensity_premodifierNorm_apply (hρ : IsPremodifier ρ) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ((isssd (S := S) (E := E) ν Λ η).withDensity
        (premodifierNorm (S := S) (E := E) ν ρ Λ)) A =
      (premodifierZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ y in A, ρ Λ y ∂(isssd (S := S) (E := E) ν Λ η) := by
  let Z : Finset S → (S → E) → ℝ≥0∞ := premodifierZ (S := S) (E := E) ν ρ
  have hZmeas : Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := by
    simpa [Z, premodifierZ] using
      (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ))
        (f := ρ Λ) (hρ.measurable Λ))
  have hpull :
      ∫⁻ y, (fun y : S → E => (Z Λ y)⁻¹) y *
          (A.indicator fun y : S → E => ρ Λ y) y
        ∂(isssd (S := S) (E := E) ν Λ η) =
        (Z Λ η)⁻¹ *
          ∫⁻ y, (A.indicator fun y : S → E => ρ Λ y) y
            ∂(isssd (S := S) (E := E) ν Λ η) :=
    Specification.lintegral_mul (isssd (S := S) (E := E) ν)
      (Λ := Λ) (η₀ := η) (f := A.indicator fun y : S → E => ρ Λ y)
      (g := fun y : S → E => (Z Λ y)⁻¹)
      (hf := Measurable.indicator (hρ.measurable Λ) hA) (hg := hZmeas.inv)
  calc
    ((isssd (S := S) (E := E) ν Λ η).withDensity
        (premodifierNorm (S := S) (E := E) ν ρ Λ)) A =
        ∫⁻ y in A, ρ Λ y * (Z Λ y)⁻¹ ∂(isssd (S := S) (E := E) ν Λ η) := by
          simp [withDensity_apply _ hA, premodifierNorm, Z, div_eq_mul_inv]
    _ = ∫⁻ y, (Z Λ y)⁻¹ * (A.indicator fun y : S → E => ρ Λ y) y
          ∂(isssd (S := S) (E := E) ν Λ η) := by
          rw [← lintegral_indicator hA]
          simp [Set.indicator_mul_left, mul_comm]
    _ = (Z Λ η)⁻¹ * ∫⁻ y, (A.indicator fun y : S → E => ρ Λ y) y
          ∂(isssd (S := S) (E := E) ν Λ η) := hpull
    _ = (Z Λ η)⁻¹ * ∫⁻ y in A, ρ Λ y ∂(isssd (S := S) (E := E) ν Λ η) := by
          simp [lintegral_indicator hA]

/-- Pull the boundary normalization of a normalized premodifier outside an integral. -/
lemma lintegral_premodifierNorm_mul_eq (hρ : IsPremodifier ρ) {Λ : Finset S}
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) (η : S → E) :
    ∫⁻ x, premodifierNorm (S := S) (E := E) ν ρ Λ x * f x
        ∂(isssd (S := S) (E := E) ν Λ η) =
      (premodifierZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ x, ρ Λ x * f x ∂(isssd (S := S) (E := E) ν Λ η) := by
  let Z : Finset S → (S → E) → ℝ≥0∞ := premodifierZ (S := S) (E := E) ν ρ
  have hZmeas : Measurable[cylinderEvents (Λ : Set S)ᶜ] (Z Λ) := by
    simpa [Z, premodifierZ] using
      (Measurable.lintegral_kernel (κ := (isssd (S := S) (E := E) ν Λ))
        (f := ρ Λ) (hρ.measurable Λ))
  have hpull :=
    Specification.lintegral_mul (isssd (S := S) (E := E) ν)
      (Λ := Λ) (η₀ := η) (f := fun x : S → E => ρ Λ x * f x)
      (g := fun x : S → E => (Z Λ x)⁻¹)
      (hf := (hρ.measurable Λ).mul hf) (hg := hZmeas.inv)
  simpa [premodifierNorm, Z, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpull

/-- Pull the boundary normalization of a normalized premodifier outside a set integral. -/
lemma setLIntegral_premodifierNorm_eq (hρ : IsPremodifier ρ) {Λ : Finset S}
    {A : Set (S → E)} (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ x in A, premodifierNorm (S := S) (E := E) ν ρ Λ x
        ∂(isssd (S := S) (E := E) ν Λ η) =
      (premodifierZ (S := S) (E := E) ν ρ Λ η)⁻¹ *
        ∫⁻ x in A, ρ Λ x ∂(isssd (S := S) (E := E) ν Λ η) := by
  simpa [withDensity_apply _ hA] using
    withDensity_premodifierNorm_apply (S := S) (E := E) (ρ := ρ) ν hρ hA η

/-- Consistency of `isssd` collapses an iterated finite-volume integral. -/
lemma lintegral_lintegral_isssd_eq_of_subset {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) (η : S → E) :
    ∫⁻ x, ∫⁻ y, f y ∂(isssd (S := S) (E := E) ν Λ₁ x)
        ∂(isssd (S := S) (E := E) ν Λ₂ η) =
      ∫⁻ y, f y ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
  have hcons : ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
      (isssd (S := S) (E := E) ν Λ₂)) = (isssd (S := S) (E := E) ν Λ₂) :=
    (isssd (S := S) (E := E) ν).isConsistent hΛ
  have hcons_eta :
      (((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
          (isssd (S := S) (E := E) ν Λ₂)) η) =
        (isssd (S := S) (E := E) ν Λ₂ η) := by
    simpa using congrArg (fun κ => κ η) hcons
  calc
    ∫⁻ x, ∫⁻ y, f y ∂(isssd (S := S) (E := E) ν Λ₁ x)
        ∂(isssd (S := S) (E := E) ν Λ₂ η)
        = ∫⁻ y, f y
            ∂(((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ
                (isssd (S := S) (E := E) ν Λ₂)) η) := by
          simpa [Kernel.comap_apply, measurable_id''] using
            (Kernel.lintegral_comp ((isssd (S := S) (E := E) ν Λ₁).comap id cylinderEvents_le_pi)
              (isssd (S := S) (E := E) ν Λ₂) η hf).symm
    _ = ∫⁻ y, f y ∂(isssd (S := S) (E := E) ν Λ₂ η) := by rw [hcons_eta]

/-- Set integrals against `isssd Λ₁` are measurable with respect to the outside of `Λ₁`. -/
lemma measurable_setLIntegral_isssd {Λ : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet A) {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    Measurable[cylinderEvents (Λ : Set S)ᶜ]
      (fun η : S → E => ∫⁻ ζ in A, f ζ ∂(isssd (S := S) (E := E) ν Λ η)) := by
  simpa [lintegral_indicator hA] using
    (Measurable.lintegral_kernel (κ := isssd (S := S) (E := E) ν Λ)
      (f := A.indicator f) (Measurable.indicator hf hA))

/-- Consistency of `isssd` collapses an outer integral of an inner set integral. -/
lemma lintegral_setLIntegral_isssd_eq_setLIntegral_of_subset {Λ₁ Λ₂ : Finset S}
    (hΛ : Λ₁ ⊆ Λ₂) {A : Set (S → E)} (hA : MeasurableSet A)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) (η : S → E) :
    ∫⁻ ξ, (∫⁻ ζ in A, f ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ))
        ∂(isssd (S := S) (E := E) ν Λ₂ η) =
      ∫⁻ ζ in A, f ζ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
  let gA : (S → E) → ℝ≥0∞ := A.indicator f
  have hgA : Measurable gA := Measurable.indicator hf hA
  calc
    ∫⁻ ξ, (∫⁻ ζ in A, f ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ))
        ∂(isssd (S := S) (E := E) ν Λ₂ η)
        = ∫⁻ ξ, ∫⁻ ζ, gA ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ)
            ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          simp [gA, lintegral_indicator hA]
    _ = ∫⁻ ζ, gA ζ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          exact lintegral_lintegral_isssd_eq_of_subset (S := S) (E := E) ν hΛ hgA η
    _ = ∫⁻ ζ in A, f ζ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          simp [gA, lintegral_indicator hA]

/-- A normalized premodifier integrates out against off-volume measurable functions. -/
lemma lintegral_premodifierNorm_mul_boundary_eq (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤)
    {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {H : (S → E) → ℝ≥0∞}
    (hHc : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] H) (hH : Measurable H) (η : S → E) :
    ∫⁻ ξ, premodifierNorm (S := S) (E := E) ν ρ Λ₁ ξ * H ξ
        ∂(isssd (S := S) (E := E) ν Λ₂ η) =
      ∫⁻ ξ, H ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) :=
    premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ
  have hprod : Measurable fun ξ : S → E => ρ' Λ₁ ξ * H ξ := (hρ'meas Λ₁).mul hH
  calc
    ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(isssd (S := S) (E := E) ν Λ₂ η)
        = ∫⁻ x, ∫⁻ ξ, ρ' Λ₁ ξ * H ξ
            ∂(isssd (S := S) (E := E) ν Λ₁ x)
            ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          exact (lintegral_lintegral_isssd_eq_of_subset (S := S) (E := E) ν hΛ hprod η).symm
    _ = ∫⁻ x, H x ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          refine lintegral_congr_ae ?_
          filter_upwards with x
          have hpull := Specification.lintegral_mul (isssd (S := S) (E := E) ν)
            (Λ := Λ₁) (η₀ := x) (f := ρ' Λ₁) (g := H)
            (hf := hρ'meas Λ₁) (hg := hHc)
          have hnormx : ∫⁻ ξ, ρ' Λ₁ ξ ∂(isssd (S := S) (E := E) ν Λ₁ x) = 1 := by
            simpa [ρ'] using lintegral_premodifierNorm_eq_one
              (S := S) (E := E) (ρ := ρ) ν hρ hZ Λ₁ x
          calc
            ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(isssd (S := S) (E := E) ν Λ₁ x)
                = H x * ∫⁻ ξ, ρ' Λ₁ ξ ∂(isssd (S := S) (E := E) ν Λ₁ x) := by
                  simpa [mul_comm] using hpull
            _ = H x * 1 := by rw [hnormx]
            _ = H x := by simp

/-- Pointwise rearrangement behind consistency of a normalized premodifier modification. -/
lemma premodifierNorm_withDensity_rearrange (hρ : IsPremodifier ρ)
    {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {A : Set (S → E)}
    (hA : MeasurableSet A) (ξ : S → E) :
    ρ Λ₂ ξ * ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity
        (premodifierNorm (S := S) (E := E) ν ρ Λ₁)) A =
      premodifierNorm (S := S) (E := E) ν ρ Λ₁ ξ *
        ∫⁻ ζ in A, ρ Λ₂ ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ) := by
  let Z : Finset S → (S → E) → ℝ≥0∞ := premodifierZ (S := S) (E := E) ν ρ
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  let I₁ : (S → E) → ℝ≥0∞ := fun η => ∫⁻ ζ in A, ρ Λ₁ ζ ∂(isssd (S := S) (E := E) ν Λ₁ η)
  let H : (S → E) → ℝ≥0∞ := fun η => ∫⁻ ζ in A, ρ Λ₂ ζ ∂(isssd (S := S) (E := E) ν Λ₁ η)
  have hkA : ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity (ρ' Λ₁)) A =
      (Z Λ₁ ξ)⁻¹ * I₁ ξ := by
    simpa [ρ', Z, I₁] using
      withDensity_premodifierNorm_apply (S := S) (E := E) (ρ := ρ) ν hρ
        (Λ := Λ₁) hA ξ
  have hcocycle : ρ Λ₂ ξ * I₁ ξ = ρ Λ₁ ξ * H ξ := by
    simpa [I₁, H] using
      IsPremodifier.mul_setLIntegral_isssd_eq (S := S) (E := E) (ρ := ρ) ν hρ hΛ hA ξ
  have hkA' :
      ((Measure.map (juxt (Λ := (Λ₁ : Set S)) (η := ξ)) (Measure.pi fun _ : Λ₁ => ν)).withDensity
          (ρ' Λ₁)) A = (Z Λ₁ ξ)⁻¹ * I₁ ξ := by
    simpa [isssdFun_apply] using hkA
  calc
    ρ Λ₂ ξ * ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity (ρ' Λ₁)) A
        = ρ Λ₂ ξ * ((Z Λ₁ ξ)⁻¹ * I₁ ξ) := by
            simpa [isssdFun_apply] using congrArg (fun t => ρ Λ₂ ξ * t) hkA'
    _ = (Z Λ₁ ξ)⁻¹ * (ρ Λ₂ ξ * I₁ ξ) := by simp [mul_left_comm]
    _ = (Z Λ₁ ξ)⁻¹ * (ρ Λ₁ ξ * H ξ) := by simp [hcocycle]
    _ = ρ' Λ₁ ξ * H ξ := by simp [ρ', premodifierNorm, Z, div_eq_mul_inv, mul_assoc, mul_left_comm]

/-- Evaluate the composition of two density-modified kernels on a measurable set. -/
lemma modificationKer_comp_apply_eq_lintegral_mul (γ : Specification S E)
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

/-- The unnormalized cocycle integral left after expanding the outer normalized density. -/
lemma lintegral_mul_premodifierNorm_withDensity_eq_setLIntegral (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤)
    {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {A : Set (S → E)}
    (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ ξ, ρ Λ₂ ξ * ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity
        (premodifierNorm (S := S) (E := E) ν ρ Λ₁)) A
        ∂(isssd (S := S) (E := E) ν Λ₂ η) =
      ∫⁻ ξ in A, ρ Λ₂ ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  let H : (S → E) → ℝ≥0∞ := fun ξ => ∫⁻ ζ in A, ρ Λ₂ ζ ∂(isssd (S := S) (E := E) ν Λ₁ ξ)
  have hH_meas_Λ₁c : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] H := by
    simpa [H] using measurable_setLIntegral_isssd
      (S := S) (E := E) ν (Λ := Λ₁) hA (hρ.measurable Λ₂)
  have hH_meas : Measurable H := hH_meas_Λ₁c.mono cylinderEvents_le_pi le_rfl
  have h_rearrange (ξ : S → E) :
      ρ Λ₂ ξ * ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity (ρ' Λ₁)) A = ρ' Λ₁ ξ * H ξ := by
    simpa [ρ', H] using
      premodifierNorm_withDensity_rearrange (S := S) (E := E) (ρ := ρ) ν hρ hΛ hA ξ
  have hH_integral : (∫⁻ ξ, H ξ ∂(isssd (S := S) (E := E) ν Λ₂ η)) =
      ∫⁻ ξ in A, ρ Λ₂ ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
    simpa [H] using
      lintegral_setLIntegral_isssd_eq_setLIntegral_of_subset
        (S := S) (E := E) ν hΛ hA (hρ.measurable Λ₂) η
  calc
    ∫⁻ ξ, ρ Λ₂ ξ * ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity (ρ' Λ₁)) A
        ∂(isssd (S := S) (E := E) ν Λ₂ η)
        = ∫⁻ ξ, ρ' Λ₁ ξ * H ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          refine lintegral_congr_ae ?_
          filter_upwards with ξ
          exact h_rearrange ξ
    _ = ∫⁻ ξ, H ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          exact lintegral_premodifierNorm_mul_boundary_eq
            (S := S) (E := E) (ρ := ρ) ν hρ hZ hΛ hH_meas_Λ₁c hH_meas η
    _ = ∫⁻ ξ in A, ρ Λ₂ ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := hH_integral

/-- Consistency integral for the normalized premodifier density. -/
lemma lintegral_premodifierNorm_withDensity_eq_setLIntegral (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤)
    {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {A : Set (S → E)}
    (hA : MeasurableSet A) (η : S → E) :
    ∫⁻ ξ, premodifierNorm (S := S) (E := E) ν ρ Λ₂ ξ *
        ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity
          (premodifierNorm (S := S) (E := E) ν ρ Λ₁)) A
        ∂(isssd (S := S) (E := E) ν Λ₂ η) =
      ∫⁻ ξ in A, premodifierNorm (S := S) (E := E) ν ρ Λ₂ ξ
        ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
  let kA : (S → E) → ℝ≥0∞ := fun ξ =>
    ((isssd (S := S) (E := E) ν Λ₁ ξ).withDensity
      (premodifierNorm (S := S) (E := E) ν ρ Λ₁)) A
  have hkA_meas : Measurable kA := by
    let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
    have hρ'meas : ∀ Λ, Measurable (ρ' Λ) :=
      premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ
    let K₁ : Kernel[cylinderEvents (Λ₁ : Set S)ᶜ] (S → E) (S → E) :=
      modificationKer (γ := isssd (S := S) (E := E) ν)
        (ρ := ρ') (hρ := hρ'meas) Λ₁
    have hmeas_dom : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] (fun ξ : S → E => (K₁ ξ) A) :=
      Kernel.measurable_coe K₁ hA
    simpa [kA, ρ', K₁, modificationKer] using hmeas_dom.mono cylinderEvents_le_pi le_rfl
  calc
    ∫⁻ ξ, premodifierNorm (S := S) (E := E) ν ρ Λ₂ ξ * kA ξ
        ∂(isssd (S := S) (E := E) ν Λ₂ η)
        = (premodifierZ (S := S) (E := E) ν ρ Λ₂ η)⁻¹ *
            ∫⁻ ξ, ρ Λ₂ ξ * kA ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          exact lintegral_premodifierNorm_mul_eq
            (S := S) (E := E) (ρ := ρ) ν hρ hkA_meas η
    _ = (premodifierZ (S := S) (E := E) ν ρ Λ₂ η)⁻¹ *
          ∫⁻ ξ in A, ρ Λ₂ ξ ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          rw [lintegral_mul_premodifierNorm_withDensity_eq_setLIntegral
            (S := S) (E := E) (ρ := ρ) ν hρ hZ hΛ hA η]
    _ = ∫⁻ ξ in A, premodifierNorm (S := S) (E := E) ν ρ Λ₂ ξ
          ∂(isssd (S := S) (E := E) ν Λ₂ η) := by
          rw [setLIntegral_premodifierNorm_eq (S := S) (E := E) (ρ := ρ) ν hρ hA η]

/-- The normalized premodifier density gives a consistent modification of `isssd`. -/
lemma IsPremodifier.isConsistent_modificationKer_premodifierNorm (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤) :
    IsConsistent
      (modificationKer (γ := isssd (S := S) (E := E) ν)
        (ρ := premodifierNorm (S := S) (E := E) ν ρ)
        (premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)) := by
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) :=
    premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ
  let γ : Finset S → (S → E) → Measure (S → E) := fun Λ ξ => (isssd (S := S) (E := E) ν Λ) ξ
  intro Λ₁ Λ₂ hΛ
  ext η A hA
  let kA : (S → E) → ℝ≥0∞ := fun ξ => ((γ Λ₁ ξ).withDensity (ρ' Λ₁)) A
  have h_goal :
      (∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η)) = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := by
    simpa [ρ', γ, kA] using
      lintegral_premodifierNorm_withDensity_eq_setLIntegral
        (S := S) (E := E) (ρ := ρ) ν hρ hZ hΛ hA η
  have hLHS :
      (((modificationKer (γ := isssd (S := S) (E := E) ν) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
            cylinderEvents_le_pi ∘ₖ
          modificationKer (γ := isssd (S := S) (E := E) ν) (ρ := ρ') (hρ := hρ'meas) Λ₂)
        η) A = ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := by
    simpa [γ, kA] using modificationKer_comp_apply_eq_lintegral_mul
      (γ := isssd (S := S) (E := E) ν) (ρ := ρ') hρ'meas
      (Λ₁ := Λ₁) (Λ₂ := Λ₂) (η := η) (A := A) hA
  calc
    (((modificationKer (γ := isssd (S := S) (E := E) ν) (ρ := ρ') (hρ := hρ'meas) Λ₁).comap id
          cylinderEvents_le_pi ∘ₖ
        modificationKer (γ := isssd (S := S) (E := E) ν) (ρ := ρ') (hρ := hρ'meas) Λ₂) η) A
        = ∫⁻ ξ, ρ' Λ₂ ξ * kA ξ ∂(γ Λ₂ η) := hLHS
    _ = ∫⁻ ξ in A, ρ' Λ₂ ξ ∂(γ Λ₂ η) := h_goal
    _ = (modificationKer (γ := isssd (S := S) (E := E) ν) (ρ := ρ') (hρ := hρ'meas) Λ₂ η) A := by
          simp only [modificationKer_apply]
          exact Eq.symm (withDensity_apply' (ρ' Λ₂) A)

lemma IsPremodifier.isModifier_premodifierNorm (hρ : IsPremodifier ρ)
    (hZ : ∀ (Λ : Finset S) (η : S → E),
      premodifierZ (S := S) (E := E) ν ρ Λ η ≠ 0 ∧
        premodifierZ (S := S) (E := E) ν ρ Λ η ≠ ⊤) :
    (isssd (S := S) (E := E) ν).IsModifier (premodifierNorm (S := S) (E := E) ν ρ) := by
  classical
  let ρ' : Finset S → (S → E) → ℝ≥0∞ := premodifierNorm (S := S) (E := E) ν ρ
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) :=
    premodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ
  let γ : Finset S → (S → E) → Measure (S → E) := fun Λ ξ => (isssd (S := S) (E := E) ν Λ) ξ
  have hNorm :
      ∀ (Λ : Finset S) (ξ : S → E), ∫⁻ x, ρ' Λ x ∂(γ Λ ξ) = 1 := by
    intro Λ ξ
    simpa [ρ', γ] using
      lintegral_premodifierNorm_eq_one (S := S) (E := E) (ρ := ρ) ν hρ hZ Λ ξ
  refine
    { measurable := hρ'meas
      isMarkovKernel := ?_
      isProper := ?_
      isConsistent := ?_ }
  · intro Λ
    refine ⟨?_⟩
    intro ξ
    constructor
    simpa [modificationKer, γ, withDensity_apply] using hNorm Λ ξ
  · exact isProper_modificationKer (γ := isssd (S := S) (E := E) ν) hρ'meas
  · simpa [ρ'] using
      IsPremodifier.isConsistent_modificationKer_premodifierNorm
        (S := S) (E := E) (ρ := ρ) ν hρ hZ

end Modifier
end Specification

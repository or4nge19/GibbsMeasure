module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory Set

variable {S E : Type*} {mE : MeasurableSpace E}

public lemma mem_congr_of_measurableSet_cylinderEvents {Δ : Set S} {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents Δ] B) {f₁ f₂ : S → E} (h : ∀ i ∈ Δ, f₁ i = f₂ i) :
    f₁ ∈ B ↔ f₂ ∈ B := by
  unfold cylinderEvents at hB
  rw [MeasurableSpace.measurableSet_iSup] at hB
  refine hB.recOn (fun s ⟨i,hi⟩ ↦ ?_) (by simp) (fun _ _ ih => ih.not) (fun _ _ ih ↦ by simp [ih])
  by_cases hiΔ : i ∈ Δ
  · rw [iSup_pos hiΔ, MeasurableSpace.measurableSet_comap] at hi
    obtain ⟨_ , _, rfl⟩ := hi
    simp only [mem_preimage, h i hiΔ]
  · rw [iSup_neg hiΔ, MeasurableSpace.measurableSet_bot_iff] at hi
    rcases hi with rfl | rfl <;> exact iff_of_eq rfl

namespace MeasureTheory

section CylinderEventsUnion

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The cylinder σ-algebra of a union is the supremum of the cylinder σ-algebras. -/
public lemma cylinderEvents_union (Δ₁ Δ₂ : Set ι) :
    cylinderEvents (X := X) (Δ₁ ∪ Δ₂) = cylinderEvents (X := X) Δ₁ ⊔ cylinderEvents (X := X) Δ₂
        := by
  simp only [cylinderEvents]
  exact _root_.iSup_union

/-- The cylinder σ-algebra of a union is the supremum of the cylinder σ-algebras. -/
public lemma cylinderEvents_iUnion {κ : Sort*} (Δ : κ → Set ι) :
    cylinderEvents (X := X) (⋃ k, Δ k) = ⨆ k, cylinderEvents (X := X) (Δ k) := by
  simp only [cylinderEvents]
  exact iSup_iUnion Δ _

@[simp] public lemma cylinderEvents_empty : cylinderEvents (X := X) (∅ : Set ι) = ⊥ := by
  simp [cylinderEvents]

variable {ι' E : Type*} [MeasurableSpace E]

/-- Precomposing configurations with a map of sites `σ : ι → ι'` pulls the cylinder σ-algebra of
`Δ ⊆ ι` back to the cylinder σ-algebra of the image `σ '' Δ ⊆ ι'`. -/
public lemma cylinderEvents_comap_precomp (σ : ι → ι') (Δ : Set ι) :
    (cylinderEvents (X := fun _ : ι ↦ E) Δ).comap (fun ω : ι' → E ↦ fun i ↦ ω (σ i))
      = cylinderEvents (X := fun _ : ι' ↦ E) (σ '' Δ) := by
  rw [cylinderEvents, cylinderEvents, _root_.iSup_image, MeasurableSpace.comap_iSup]
  refine iSup_congr fun i ↦ ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [MeasurableSpace.comap_comp]
  rfl

end CylinderEventsUnion

/-! ### Reindexing the sites along an equivalence

For `e : ι ≃ ι'`, the measurable equivalence `MeasurableEquiv.arrowCongr' e (.refl E)` sends a
configuration `ω : ι → E` to `ω ∘ e.symm : ι' → E`. It carries the cylinder σ-algebra of `Δ` to
the cylinder σ-algebra of `e '' Δ`. -/

section ArrowCongr

variable {ι ι' E : Type*} [MeasurableSpace E]

@[simp] public lemma _root_.MeasurableEquiv.arrowCongr'_refl_apply (e : ι ≃ ι') (ω : ι → E)
    (i : ι') : MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω i = ω (e.symm i) := rfl

@[simp] public lemma _root_.MeasurableEquiv.arrowCongr'_refl_symm_apply (e : ι ≃ ι') (ω : ι' → E)
    (i : ι) : (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm ω i = ω (e i) := rfl

/-- The inverse of `arrowCongr' e (.refl E)` is `arrowCongr' e.symm (.refl E)`. -/
public lemma _root_.MeasurableEquiv.arrowCongr'_refl_symm (e : ι ≃ ι') :
    (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm =
      MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl E) := rfl

/-- For a constant family, `arrowCongr' e (.refl E)` is Mathlib's `piCongrLeft`. -/
public lemma _root_.MeasurableEquiv.arrowCongr'_refl_eq_piCongrLeft (e : ι ≃ ι') :
    MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) =
      MeasurableEquiv.piCongrLeft (fun _ : ι' ↦ E) e := by
  refine MeasurableEquiv.ext (funext fun ω ↦ funext fun i ↦ ?_)
  obtain ⟨a, rfl⟩ := e.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply, MeasurableEquiv.arrowCongr'_refl_apply,
    Equiv.symm_apply_apply]

/-- Pulling back the cylinder σ-algebra of `Δ` along `ω ↦ ω ∘ e` gives the cylinder σ-algebra of
`e '' Δ`. -/
public lemma cylinderEvents_comap_arrowCongr'_symm (e : ι ≃ ι') (Δ : Set ι) :
    (cylinderEvents (X := fun _ : ι ↦ E) Δ).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm
      = cylinderEvents (X := fun _ : ι' ↦ E) (e '' Δ) :=
  cylinderEvents_comap_precomp (E := E) e Δ

/-- Pulling back the cylinder σ-algebra of `Δ` along `ω ↦ ω ∘ e.symm` gives the cylinder σ-algebra
of `e.symm '' Δ`. -/
public lemma cylinderEvents_comap_arrowCongr' (e : ι ≃ ι') (Δ : Set ι') :
    (cylinderEvents (X := fun _ : ι' ↦ E) Δ).comap
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E))
      = cylinderEvents (X := fun _ : ι ↦ E) (e.symm '' Δ) :=
  cylinderEvents_comap_precomp (E := E) e.symm Δ

/-- `ω ↦ ω ∘ e.symm` is measurable from `cylinderEvents Δ` to `cylinderEvents (e '' Δ)`. -/
public lemma measurable_arrowCongr'_refl_cylinderEvents (e : ι ≃ ι') (Δ : Set ι) :
    Measurable[cylinderEvents (X := fun _ : ι ↦ E) Δ,
      cylinderEvents (X := fun _ : ι' ↦ E) (e '' Δ)]
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)) := by
  rw [measurable_iff_comap_le, cylinderEvents_comap_arrowCongr', Equiv.symm_image_image]

/-- `ω ↦ ω ∘ e` is measurable from `cylinderEvents (e '' Δ)` to `cylinderEvents Δ`. -/
public lemma measurable_arrowCongr'_refl_symm_cylinderEvents (e : ι ≃ ι') (Δ : Set ι) :
    Measurable[cylinderEvents (X := fun _ : ι' ↦ E) (e '' Δ),
      cylinderEvents (X := fun _ : ι ↦ E) Δ]
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm := by
  rw [measurable_iff_comap_le, cylinderEvents_comap_arrowCongr'_symm]

end ArrowCongr


/-! ### `cylinderEvents` as a pullback σ-algebra, and cylinder measurability versus dependence on
coordinates

`measurable_cylinderEvents_iff_dependsOn`: a function is `cylinderEvents Δ`-measurable iff it is
measurable and depends only on the coordinates in `Δ`. Mathlib's `Measurable.dependsOn_of_piFinset`
is the `Finset`-indexed, one-directional case. -/

section DependsOn

open Function

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {Δ : Set ι}

/-! ### `cylinderEvents` as a pullback σ-algebra -/

/-- `cylinderEvents Δ` is the pullback of the product σ-algebra along restriction to `Δ`. -/
public lemma cylinderEvents_eq_comap_domRestrict (Δ : Set ι) :
    cylinderEvents (X := X) Δ =
      MeasurableSpace.comap Δ.domRestrict (inferInstance : MeasurableSpace (∀ i : Δ, X i)) := by
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_)
    (measurable_restrict_cylinderEvents (X := X) Δ).comap_le
  exact MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ∀ i : Δ, X i ↦ x ⟨i, hi⟩)
    (measurable_pi_apply _) rfl

/-- Non-dependent restatement of `cylinderEvents_eq_comap_domRestrict`. -/
public lemma cylinderEvents_eq_comap_restrict {S E : Type*} [MeasurableSpace E] (Δ : Set S) :
    cylinderEvents (X := fun _ : S ↦ E) Δ =
      MeasurableSpace.comap (Set.domRestrict Δ)
        (inferInstance : MeasurableSpace (Δ → E)) :=
  cylinderEvents_eq_comap_domRestrict (X := fun _ : S ↦ E) Δ

/-- The finite-volume σ-algebra is the pullback of the product σ-algebra along
`Finset.restrict`. `Finset` analogue of `cylinderEvents_eq_comap_domRestrict`. -/
public lemma cylinderEvents_eq_comap_finsetRestrict (Λ : Finset ι) :
    cylinderEvents (X := X) (Λ : Set ι) =
      MeasurableSpace.comap (Λ.restrict (π := X))
        (inferInstance : MeasurableSpace (Π i : Λ, X i)) := by
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_) ?_
  · exact MeasurableSpace.comap_le_comap_of_eq_comp (fun x : Π i : Λ, X i ↦ x ⟨i, hi⟩)
      (measurable_pi_apply _) rfl
  · refine Measurable.comap_le ?_
    rw [@measurable_pi_iff]
    exact fun j ↦ measurable_cylinderEvent_apply j.2

/-! ### Cylinder measurability versus dependence on coordinates -/

variable {Z : Type*} [MeasurableSpace Z] {f : (∀ i, X i) → Z}

/-- A function measurable for the cylinder σ-algebra of `Δ` depends only on the coordinates in `Δ`.

Requires measurable singletons in the codomain. -/
public theorem _root_.Measurable.dependsOn_of_cylinderEvents [MeasurableSingletonClass Z]
    (hf : Measurable[cylinderEvents Δ] f) : DependsOn f Δ :=
  dependsOn_iff_factorsThrough.2 <| by
    rw [cylinderEvents_eq_comap_domRestrict] at hf; exact hf.factorsThrough

/-- A measurable function depending only on the coordinates in `Δ` is measurable for the cylinder
σ-algebra of `Δ`. -/
public theorem _root_.Measurable.cylinderEvents_of_dependsOn
    (hf : Measurable f) (hdep : DependsOn f Δ) : Measurable[cylinderEvents Δ] f := by
  classical
  by_cases hne : Nonempty (∀ i, X i)
  swap
  · have : IsEmpty (∀ i, X i) := not_nonempty_iff.1 hne
    intro s _
    have hempty : f ⁻¹' s = ∅ := Set.eq_empty_of_isEmpty _
    simp [hempty]
  obtain ⟨x₀⟩ := hne
  set e : (∀ i : Δ, X i) → ∀ i, X i :=
    fun y i ↦ if h : i ∈ Δ then y ⟨i, h⟩ else x₀ i with he
  have hemeas : Measurable e := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    by_cases h : i ∈ Δ
    · simpa only [he, h, dite_true] using measurable_pi_apply (⟨i, h⟩ : Δ)
    · simpa only [he, h, dite_false] using measurable_const (a := x₀ i)
  have hfe : f = (f ∘ e) ∘ Δ.domRestrict := by
    funext x
    refine (hdep fun i hi ↦ ?_).symm
    simp [he, hi, Set.domRestrict]
  rw [cylinderEvents_eq_comap_domRestrict, hfe]
  exact (hf.comp hemeas).comp (Measurable.of_comap_le le_rfl)

/-- **A function is `cylinderEvents Δ`-measurable exactly when it is measurable and depends only on
the coordinates in `Δ`.**

This characterization of `𝓕_Δ`-measurability (for codomains with measurable singletons) is what
underlies Georgii's notion of a local function, Definition (2.20)(a). Mathlib's
`Measurable.dependsOn_of_piFinset` is the `Finset`-indexed, one-directional special case. -/
public theorem measurable_cylinderEvents_iff_dependsOn [MeasurableSingletonClass Z] :
    Measurable[cylinderEvents Δ] f ↔ Measurable f ∧ DependsOn f Δ :=
  ⟨fun h ↦ ⟨h.mono cylinderEvents_le_pi le_rfl, h.dependsOn_of_cylinderEvents⟩,
    fun h ↦ h.1.cylinderEvents_of_dependsOn h.2⟩

end DependsOn

end MeasureTheory

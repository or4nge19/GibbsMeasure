module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

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

end MeasureTheory

module

public import Mathlib.MeasureTheory.Constructions.Cylinders

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

@[simp] public lemma cylinderEvents_empty : cylinderEvents (X := X) (∅ : Set ι) = ⊥ := by
  simp [cylinderEvents]

variable {E : Type*} [MeasurableSpace E]

/-- Precomposing configurations with a map of sites pulls the cylinder σ-algebra of `Δ` back to
the cylinder σ-algebra of the image of `Δ`. -/
public lemma cylinderEvents_comap_precomp (σ : ι → ι) (Δ : Set ι) :
    (cylinderEvents (X := fun _ : ι ↦ E) Δ).comap (fun ω : ι → E ↦ fun i ↦ ω (σ i))
      = cylinderEvents (X := fun _ : ι ↦ E) (σ '' Δ) := by
  rw [cylinderEvents, cylinderEvents, _root_.iSup_image, MeasurableSpace.comap_iSup]
  refine iSup_congr fun i ↦ ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun _ ↦ ?_
  rw [MeasurableSpace.comap_comp]
  rfl

end CylinderEventsUnion

end MeasureTheory

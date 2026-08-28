module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Function.FactorsThrough

@[expose] public section

/-!
# Cylinder σ-algebras and dependence on coordinates

`MeasureTheory.measurable_cylinderEvents_iff_dependsOn`: a function is `cylinderEvents Δ`-measurable
iff it is measurable and depends only on the coordinates in `Δ`.

Mathlib's `Measurable.dependsOn_of_piFinset` is the `Finset`-indexed, one-directional case.
-/

open Set Function

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {Δ : Set ι}

/-! ### `cylinderEvents` as a pullback σ-algebra -/

/-- `cylinderEvents Δ` is the pullback of the product σ-algebra along restriction to `Δ`. -/
lemma cylinderEvents_eq_comap_domRestrict (Δ : Set ι) :
    cylinderEvents (X := X) Δ =
      MeasurableSpace.comap Δ.domRestrict (inferInstance : MeasurableSpace (∀ i : Δ, X i)) := by
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_)
    (measurable_restrict_cylinderEvents (X := X) Δ).comap_le
  exact MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ∀ i : Δ, X i ↦ x ⟨i, hi⟩)
    (measurable_pi_apply _) rfl

/-- Non-dependent restatement of `cylinderEvents_eq_comap_domRestrict`. -/
lemma cylinderEvents_eq_comap_restrict {S E : Type*} [MeasurableSpace E] (Δ : Set S) :
    cylinderEvents (X := fun _ : S ↦ E) Δ =
      MeasurableSpace.comap (Set.domRestrict Δ)
        (inferInstance : MeasurableSpace (Δ → E)) :=
  cylinderEvents_eq_comap_domRestrict (X := fun _ : S ↦ E) Δ

/-! ### Cylinder measurability versus dependence on coordinates -/

variable {Z : Type*} [MeasurableSpace Z] {f : (∀ i, X i) → Z}

/-- A function measurable for the cylinder σ-algebra of `Δ` depends only on the coordinates in `Δ`.

This is one half of Georgii's Definition (2.20)(a). -/
theorem _root_.Measurable.dependsOn_of_cylinderEvents [MeasurableSingletonClass Z]
    (hf : Measurable[cylinderEvents Δ] f) : DependsOn f Δ :=
  dependsOn_iff_factorsThrough.2 <| by
    rw [cylinderEvents_eq_comap_domRestrict] at hf; exact hf.factorsThrough

/-- A measurable function depending only on the coordinates in `Δ` is measurable for the cylinder
σ-algebra of `Δ`. -/
theorem _root_.Measurable.cylinderEvents_of_dependsOn
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

This is the general form of Georgii's Definition (2.20)(a); Mathlib's
`Measurable.dependsOn_of_piFinset` is the `Finset`-indexed, one-directional special case. -/
theorem measurable_cylinderEvents_iff_dependsOn [MeasurableSingletonClass Z] :
    Measurable[cylinderEvents Δ] f ↔ Measurable f ∧ DependsOn f Δ :=
  ⟨fun h ↦ ⟨h.mono cylinderEvents_le_pi le_rfl, h.dependsOn_of_cylinderEvents⟩,
    fun h ↦ h.1.cylinderEvents_of_dependsOn h.2⟩

end MeasureTheory

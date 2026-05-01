module

public import Mathlib.MeasureTheory.Constructions.Cylinders

public section

open MeasureTheory

section juxt

variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

open Classical in
noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E :=
  if h : x ∈ Λ then ζ ⟨x, h⟩ else η x

@[simp] lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by simp [juxt, hx]
@[simp] lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by simp [juxt, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

protected lemma Measurable.juxt : Measurable (juxt Λ η) := by
  rw [measurable_pi_iff]
  rintro x
  by_cases hx : x ∈ Λ <;> simp [juxt, hx, measurable_pi_apply]

lemma juxt_agree_on_compl (Λ : Finset S) (η : S → E) (ζ : Λ → E) :
    ∀ x ∉ Λ, juxt (Λ : Set S) η ζ x = η x := fun x hx ↦
  juxt_apply_of_not_mem (x := x) (Λ := (Λ : Set S)) (η := η) (ζ := ζ) (Finset.mem_coe.not.mpr hx)

end juxt

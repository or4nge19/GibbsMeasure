module

public import GibbsMeasure.Prereqs.CylinderEvents
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Juxtaposition of configurations

`juxt Λ η ζ` glues a configuration `ζ` on `Λ` to a boundary condition `η` off `Λ`. This is the
resampling operation underlying independent specifications and the finite-volume kernels of a
specification.
-/

@[expose] public section

open MeasureTheory

section juxt

variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

open Classical in
/-- `juxt Λ η ζ` is the configuration agreeing with `ζ` on `Λ` and with `η` off `Λ`.

This is Georgii's juxtaposition (Section 1.1): "if `ω ∈ E^Λ` and `ζ ∈ E^{Δ∖Λ}` then the
juxtaposition `ωζ ∈ E^Δ` is defined by the properties `σ_Λ(ωζ) = ω` and `σ_{Δ∖Λ}(ωζ) = ζ`",
taken with `Δ = S`, in the order `ζ_Λ η_{S∖Λ}`. -/
noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E :=
  if h : x ∈ Λ then ζ ⟨x, h⟩ else η x

@[simp] lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by
  simp [juxt, hx]
@[simp] lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by
  simp [juxt, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

/-- Updating the boundary configuration at a site inside `Λ` does not change the resampled
configuration off that site; updating it outside `Λ` commutes with `juxt`. -/
lemma juxt_update_of_notMem [DecidableEq S] {i : S} (hi : i ∉ Λ) (η : S → E) (y : E)
    (ζ : Λ → E) :
    juxt Λ (Function.update η i y) ζ = Function.update (juxt Λ η ζ) i y := by
  funext x
  by_cases hx : x ∈ Λ
  · have hxi : x ≠ i := fun h ↦ hi (h ▸ hx)
    rw [juxt_apply_of_mem hx, Function.update_of_ne hxi, juxt_apply_of_mem hx]
  · by_cases hxi : x = i
    · subst hxi
      rw [juxt_apply_of_not_mem hx, Function.update_self, Function.update_self]
    · rw [juxt_apply_of_not_mem hx, Function.update_of_ne hxi, Function.update_of_ne hxi,
        juxt_apply_of_not_mem hx]

/-- `η ↦ juxt Λ η ζ` fixes `ζ` on `Λ` and copies `η` off `Λ`, so it is measurable for the
exterior cylinder σ-algebra — the strongest measurability the map has. -/
lemma measurable_cylinderEvents_juxt_boundary (ζ : Λ → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) Λᶜ] fun η : S → E ↦ juxt Λ η ζ := by
  have hmeas : Measurable fun η : S → E ↦ juxt Λ η ζ := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    by_cases hi : i ∈ Λ
    · simp only [juxt_apply_of_mem hi]
      exact measurable_const
    · simp only [juxt_apply_of_not_mem hi]
      exact measurable_pi_apply i
  refine hmeas.cylinderEvents_of_dependsOn fun η η' h ↦ ?_
  funext i
  by_cases hi : i ∈ Λ
  · simp only [juxt_apply_of_mem hi]
  · simp only [juxt_apply_of_not_mem hi]
    exact h i hi

/-- `η ↦ juxt Λ η ζ` is measurable. -/
lemma measurable_juxt_boundary (ζ : Λ → E) :
    Measurable fun η : S → E ↦ juxt Λ η ζ :=
  (measurable_cylinderEvents_juxt_boundary ζ).mono cylinderEvents_le_pi le_rfl

protected lemma Measurable.juxt : Measurable (juxt Λ η) := by
  rw [measurable_pi_iff]
  rintro x
  by_cases hx : x ∈ Λ <;> simp [juxt, hx, measurable_pi_apply]

lemma juxt_agree_on_compl (Λ : Finset S) (η : S → E) (ζ : Λ → E) :
    ∀ x ∉ Λ, juxt (Λ : Set S) η ζ x = η x := fun x hx ↦
  juxt_apply_of_not_mem (x := x) (Λ := (Λ : Set S)) (η := η) (ζ := ζ) (Finset.mem_coe.not.mpr hx)

end juxt

/-! ### Lattice and order identities

Resampling on `Λ` absorbs previous resamplings on `Λ`, commutes with the pointwise lattice
operations, and is monotone in both the boundary condition and the inner configuration. -/

section order

variable {S E : Type*} {Λ : Set S}

lemma juxt_juxt (Λ : Set S) (ω : S → E) (ζ ξ : Λ → E) :
    juxt Λ (juxt Λ ω ζ) ξ = juxt Λ ω ξ := by
  funext x
  by_cases hx : x ∈ Λ <;> simp [hx]

lemma juxt_inf_juxt [SemilatticeInf E] {ω ω' : S → E} (hω : ω ≤ ω') (ζ ξ : Λ → E) :
    juxt Λ ω (ζ ⊓ ξ) = juxt Λ ω ζ ⊓ juxt Λ ω' ξ := by
  funext x
  by_cases hx : x ∈ Λ
  · simp [hx]
  · simp only [juxt_apply_of_not_mem hx, Pi.inf_apply]
    exact (inf_eq_left.2 (hω x)).symm

lemma juxt_sup_juxt [SemilatticeSup E] {ω ω' : S → E} (hω : ω ≤ ω') (ζ ξ : Λ → E) :
    juxt Λ ω' (ζ ⊔ ξ) = juxt Λ ω ζ ⊔ juxt Λ ω' ξ := by
  funext x
  by_cases hx : x ∈ Λ
  · simp [hx]
  · simp only [juxt_apply_of_not_mem hx, Pi.sup_apply]
    exact (sup_eq_right.2 (hω x)).symm

lemma juxt_le_juxt [Preorder E] {ω ω' : S → E} (hω : ω ≤ ω') (ζ : Λ → E) :
    juxt Λ ω ζ ≤ juxt Λ ω' ζ := by
  intro x
  by_cases hx : x ∈ Λ
  · simp [hx]
  · simpa [hx] using hω x

lemma monotone_juxt [Preorder E] (ω : S → E) : Monotone (juxt Λ ω) := by
  intro ζ ξ hζξ x
  by_cases hx : x ∈ Λ
  · simpa [hx] using hζξ ⟨x, hx⟩
  · simp [hx]

end order

section Restrict

variable {S E : Type*} [MeasurableSpace E]

/-- `σ ↦ σ_Λ ω_{S∖Λ}` is measurable for the cylinder σ-algebra `𝓕_Λ`: it only reads the
coordinates in `Λ`. (Intended home: `GibbsMeasure/Prereqs/Juxt.lean`.) -/
lemma measurable_cylinderEvents_juxt_restrict (Λ : Set S) (ω : S → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) Λ]
      fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i := by
  have hmeas : Measurable fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    by_cases hi : i ∈ Λ
    · simpa only [juxt_apply_of_mem hi] using measurable_pi_apply i
    · simpa only [juxt_apply_of_not_mem hi] using measurable_const
  refine hmeas.cylinderEvents_of_dependsOn fun σ σ' h ↦ ?_
  funext i
  by_cases hi : i ∈ Λ
  · simp only [juxt_apply_of_mem hi]
    exact h i hi
  · simp only [juxt_apply_of_not_mem hi]

/-- Resampling inside `Λ` does not change membership in an `𝓕_Λ`-event.
(Intended home: `GibbsMeasure/Prereqs/Juxt.lean`.) -/
lemma preimage_juxt_restrict_eq (Λ : Set S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Λ] A) :
    (fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i) ⁻¹' A = A := by
  ext σ
  exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ juxt_apply_of_mem hi _

end Restrict

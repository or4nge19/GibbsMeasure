module

public import GibbsMeasure.Mathlib.Data.Finset.Update
public import GibbsMeasure.Prereqs.CylinderEvents
public import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Juxtaposition of configurations

`juxt Λ η ζ` glues a configuration `ζ` on `Λ` to a boundary condition `η` off `Λ`. This is the
resampling operation underlying independent specifications and the finite-volume kernels of a
specification.

Juxtaposition *is* `Function.updateSet` (the `Set` version of Mathlib's `Function.updateFinset`,
see `GibbsMeasure/Mathlib/Data/Finset/Update.lean`) with the arguments in Georgii's order:
`juxt Λ η ζ = Function.updateSet η Λ ζ`. It is an `abbrev`, so the two are interchangeable and the
general lemmas are proved once, upstream; only the statements that mention `cylinderEvents` or
Georgii's order structure live here.
-/

@[expose] public section

open MeasureTheory

section juxt

variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

/-- `juxt Λ η ζ` is the configuration agreeing with `ζ` on `Λ` and with `η` off `Λ`.

This is Georgii's juxtaposition (Section 1.1): "if `ω ∈ E^Λ` and `ζ ∈ E^{Δ∖Λ}` then the
juxtaposition `ωζ ∈ E^Δ` is defined by the properties `σ_Λ(ωζ) = ω` and `σ_{Δ∖Λ}(ωζ) = ζ`",
taken with `Δ = S`, in the order `ζ_Λ η_{S∖Λ}`.

It is `Function.updateSet η Λ ζ`, i.e. `Function.updateFinset` for an arbitrary set of sites,
with the arguments permuted to Georgii's order. -/
noncomputable abbrev juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) : S → E := Function.updateSet η Λ ζ

@[simp] lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ :=
  Function.updateSet_apply_of_mem (x := η) hx ζ

@[simp] lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x :=
  Function.updateSet_apply_of_notMem (x := η) h ζ

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

/-- Updating the boundary configuration at a site inside `Λ` does not change the resampled
configuration off that site; updating it outside `Λ` commutes with `juxt`. -/
lemma juxt_update_of_notMem [DecidableEq S] {i : S} (hi : i ∉ Λ) (η : S → E) (y : E)
    (ζ : Λ → E) :
    juxt Λ (Function.update η i y) ζ = Function.update (juxt Λ η ζ) i y :=
  Function.updateSet_update_of_notMem hi η y ζ

/-- `η ↦ juxt Λ η ζ` fixes `ζ` on `Λ` and copies `η` off `Λ`, so it is measurable for the
exterior cylinder σ-algebra — the strongest measurability the map has. -/
lemma measurable_cylinderEvents_juxt_boundary (ζ : Λ → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) Λᶜ] fun η : S → E ↦ juxt Λ η ζ := by
  refine Function.measurable_updateSet_left.cylinderEvents_of_dependsOn fun η η' h ↦ ?_
  funext i
  by_cases hi : i ∈ Λ
  · simp only [juxt_apply_of_mem hi]
  · simp only [juxt_apply_of_not_mem hi]
    exact h i hi

/-- `η ↦ juxt Λ η ζ` is measurable. -/
lemma measurable_juxt_boundary (ζ : Λ → E) :
    Measurable fun η : S → E ↦ juxt Λ η ζ :=
  Function.measurable_updateSet_left

protected lemma Measurable.juxt : Measurable (juxt Λ η) :=
  Function.measurable_updateSet

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
    juxt Λ (juxt Λ ω ζ) ξ = juxt Λ ω ξ :=
  Function.updateSet_updateSet ω ζ ξ

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
    juxt Λ ω ζ ≤ juxt Λ ω' ζ :=
  Function.updateSet_le_updateSet hω ζ

lemma monotone_juxt [Preorder E] (ω : S → E) : Monotone (juxt Λ ω) :=
  Function.monotone_updateSet ω Λ

end order

section Restrict

variable {S E : Type*} [MeasurableSpace E]

/-- `σ ↦ σ_Λ ω_{S∖Λ}` is measurable for the cylinder σ-algebra `𝓕_Λ`: it only reads the
coordinates in `Λ`. -/
lemma measurable_cylinderEvents_juxt_restrict (Λ : Set S) (ω : S → E) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) Λ]
      fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i := by
  have hmeas : Measurable fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i :=
    Function.measurable_updateSet.comp (measurable_pi_lambda _ fun i ↦ measurable_pi_apply i.1)
  refine hmeas.cylinderEvents_of_dependsOn fun σ σ' h ↦ ?_
  funext i
  by_cases hi : i ∈ Λ
  · simp only [juxt_apply_of_mem hi]
    exact h i hi
  · simp only [juxt_apply_of_not_mem hi]

/-- Resampling inside `Λ` does not change membership in an `𝓕_Λ`-event. -/
lemma preimage_juxt_restrict_eq (Λ : Set S) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Λ] A) :
    (fun σ : S → E ↦ juxt Λ ω fun i ↦ σ i) ⁻¹' A = A := by
  ext σ
  exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ juxt_apply_of_mem hi _

end Restrict

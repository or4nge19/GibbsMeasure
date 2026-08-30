/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification

/-!
# Inhomogeneous independent specifications

Georgii's independent specification `Specification.isssd ν` (Example (1.28)(1)) resamples every
site of a finite volume from one and the same a priori measure `ν`. In the second half of the
proof of Georgii Theorem (8.39) one needs the version in which each site `i` carries its own a
priori measure `ν i`:

> "its proof extends without difficulties to the case when the single a priori measure `λ` is
> replaced by a family `(λ̃_i)` of separate finite a priori measures for each site."

## Main definitions

* `Specification.isssdFamilyFun`: the finite-volume kernel resampling the sites of `Λ`
  independently, site `i` from `ν i`, and keeping the boundary condition outside `Λ`.
* `Specification.isssdFamily`: the resulting specification.

## Main statements

* `Specification.isssdFamily_const`: a constant family recovers `Specification.isssd`.
* `Specification.isStronglyConsistent_isssdFamilyFun`: Georgii (1.25) for the inhomogeneous
  family.
* `Specification.isssdFamily_apply_of_mem_cylinderEvents`: on inside-volume events the kernel is
  the infinite product measure `⨂ i, ν i`.
-/

@[expose] public section

-- Lean 4.34's module system does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`)
-- during `isDefEq`; the `isssd` development in `GibbsMeasure/Specification.lean` relies on it.
set_option backward.isDefEq.respectTransparency false

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} (ν : S → Measure E)
  [∀ i, IsProbabilityMeasure (ν i)]

/-! ### The inhomogeneous independent kernel -/

/-- Auxiliary definition for `Specification.isssdFamily`: the kernel resampling the sites of the
finite volume `Λ` independently, site `i` from the a priori measure `ν i`, and keeping the
boundary condition outside `Λ`.

`Specification.isssdFun` is the special case of a constant family
(`Specification.isssdFamilyFun_const`). -/
noncomputable def isssdFamilyFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  juxtMapKernel (S := S) (E := E) (Λ := Λ) (Measure.pi fun i : Λ ↦ ν i)

lemma isssdFamilyFun_apply (Λ : Finset S) (η : S → E) :
    isssdFamilyFun ν Λ η = Measure.map (juxt (Λ : Set S) η) (Measure.pi fun i : Λ ↦ ν i) := rfl

/-- A constant family of a priori measures gives back Georgii's independent kernel. -/
lemma isssdFamilyFun_const (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    isssdFamilyFun (S := S) (E := E) (fun _ ↦ ν) Λ = isssdFun (S := S) (E := E) ν Λ := by
  ext η A hA
  rfl

/-! ### Evaluation on square cylinders -/

variable {ν}

/-- Product measure of a coordinate box on a finite volume for a family of a priori measures. -/
lemma measure_piFamily_univ_pi_if_mem_eq_prod_inter [DecidableEq S] (Λ s : Finset S)
    (t : S → Set E) :
    (Measure.pi fun j : Λ ↦ ν j)
        (Set.univ.pi fun j : Λ ↦ if (j : S) ∈ (s : Set S) then t j else Set.univ) =
      ∏ i ∈ s ∩ Λ, ν i (t i) := by
  classical
  have hpi :
      (Measure.pi fun j : Λ ↦ ν j)
          (Set.univ.pi fun j : Λ ↦ if (j : S) ∈ (s : Set S) then t j else Set.univ) =
        ∏ j : Λ, ν j (if (j : S) ∈ (s : Set S) then t j else Set.univ) := by
    simp
  have hattach :
      (∏ j : Λ, ν j (if (j : S) ∈ (s : Set S) then t j else Set.univ)) =
        ∏ i ∈ Λ, ν i (if i ∈ s then t i else Set.univ) := by
    simpa [Finset.univ_eq_attach, Finset.prod_attach, Finset.mem_coe] using
      (Finset.prod_attach (s := Λ) (f := fun i : S ↦ ν i (if i ∈ s then t i else Set.univ)))
  have hdrop :
      (∏ i ∈ Λ, ν i (if i ∈ s then t i else Set.univ)) = ∏ i ∈ s ∩ Λ, ν i (t i) := by
    have h' :
        (∏ i ∈ Λ, ν i (if i ∈ s then t i else Set.univ)) =
          ∏ i ∈ Λ, (if i ∈ s then ν i (t i) else 1) := by
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      by_cases his : i ∈ s <;> simp [his]
    simp [h', Finset.prod_ite_mem, Finset.inter_comm]
  exact hpi.trans (hattach.trans hdrop)

lemma isssdFamilyFun_apply_squareCylinder [DecidableEq S] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFamilyFun ν Λ η ((s : Set S).pi t) =
      (by
        classical
        exact ite (∀ i ∈ s, i ∉ Λ → η i ∈ t i) (∏ i ∈ s ∩ Λ, ν i (t i)) 0) := by
  classical
  rw [isssdFamilyFun_apply,
    map_juxt_apply_squareCylinder_of_measure (S := S) (E := E) (Λ := Λ) (s := s)
      (Measure.pi fun i : Λ ↦ ν i) t ht η,
    measure_piFamily_univ_pi_if_mem_eq_prod_inter (ν := ν) Λ s t]
  have hP_iff :
      (∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i) ↔ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := by simp
  by_cases hP : ∀ i ∈ (s : Set S), i ∉ (Λ : Set S) → η i ∈ t i
  · have hP' : ∀ i ∈ s, i ∉ Λ → η i ∈ t i := hP_iff.mp hP
    simp only [eq_true hP, eq_true hP', ↓reduceIte]
  · have hP' : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i := fun h ↦ hP (hP_iff.mpr h)
    simp only [hP, hP', ↓reduceIte]

/-- Single-site factors with unconstrained coordinates on `Λ₁` collapse to the coordinates in
`Λ₂ \ Λ₁`. -/
lemma prod_measure_family_if_mem_univ_eq_prod_inter_sdiff [DecidableEq S] (s Λ₁ Λ₂ : Finset S)
    (t : S → Set E) :
    (∏ i ∈ s ∩ Λ₂, ν i (if i ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t i)) =
      ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν i (t i) := by
  have hrewrite :
      (∏ i ∈ s ∩ Λ₂, ν i (if i ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t i)) =
        ∏ i ∈ s ∩ Λ₂, (if i ∈ Λ₁ then (1 : ℝ≥0∞) else ν i (t i)) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hiΛ1 : i ∈ Λ₁ <;> simp [hiΛ1]
  rw [hrewrite]
  exact prod_inter_if_mem_eq_prod_inter_sdiff (s := s) (Λ₁ := Λ₁) (Λ₂ := Λ₂)
    (f := fun i ↦ ν i (t i))

/-- Evaluation on a finite cylinder that constrains only the sites outside another volume. -/
lemma isssdFamilyFun_apply_forall_not_mem [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFamilyFun ν Λ₂ η {ω : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → ω i ∈ t i} =
      (by
        classical
        exact ite (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
          (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν i (t i)) 0) := by
  classical
  rw [setOf_forall_not_mem_eq_pi_if_univ (S := S) (E := E) Λ₁ s t]
  have hbase := isssdFamilyFun_apply_squareCylinder (ν := ν) Λ₂ s
    (fun i ↦ if i ∈ (Λ₁ : Set S) then Set.univ else t i)
    (fun i ↦ by by_cases hiΛ : i ∈ (Λ₁ : Set S) <;> simp [hiΛ, ht i]) η
  have hpred :
      (∀ i ∈ s, i ∉ Λ₂ → η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) ↔
        ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i := by
    constructor
    · intro h i hi hiU
      have hi1 : i ∉ Λ₁ := fun hi1 ↦ hiU (Finset.mem_union.2 (Or.inl hi1))
      simpa [hi1] using
        h i (by simpa using hi) (fun hi2 ↦ hiU (Finset.mem_union.2 (Or.inr hi2)))
    · intro h i hi hi2
      by_cases hi1 : i ∈ Λ₁
      · simp [hi1]
      · simp [hi1, h i (by simpa using hi)
          (fun hiU ↦ (Finset.mem_union.1 hiU).elim hi1 hi2)]
  have hprodSet :
      (∏ x ∈ s ∩ Λ₂, ν x (if x ∈ (Λ₁ : Set S) then (Set.univ : Set E) else t x)) =
        ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν i (t i) := by
    simpa using prod_measure_family_if_mem_univ_eq_prod_inter_sdiff (ν := ν) s Λ₁ Λ₂ t
  calc
    isssdFamilyFun ν Λ₂ η ((s : Set S).pi fun i ↦ if i ∈ (Λ₁ : Set S) then Set.univ else t i) =
        ite (∀ i ∈ s, i ∉ Λ₂ → η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i))
          (∏ i ∈ s ∩ Λ₂, ν i (if i ∈ (Λ₁ : Set S) then Set.univ else t i)) 0 := hbase
    _ = ite (∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i)
        (∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν i (t i)) 0 := by
          by_cases hU : ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i
          · have hL := hpred.mpr hU
            simp only [eq_true hU, eq_true hL, ↓reduceIte, hprodSet]
          · have hL : ¬ ∀ i ∈ s, i ∉ Λ₂ →
                η i ∈ (if i ∈ (Λ₁ : Set S) then Set.univ else t i) := fun h ↦ hU (hpred.mp h)
            simp only [eq_false hU, eq_false hL, ↓reduceIte]

/-! ### Strong consistency -/

lemma lintegral_isssdFamilyFun_apply_squareCylinder [DecidableEq S] (Λ₁ Λ₂ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    ∫⁻ b, isssdFamilyFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFamilyFun ν Λ₂ η =
      (∏ i ∈ s ∩ Λ₁, ν i (t i)) *
        isssdFamilyFun ν Λ₂ η {b : S → E | ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i} := by
  classical
  let P : (S → E) → Prop := fun b ↦ ∀ i ∈ (s : Set S), i ∉ (Λ₁ : Set S) → b i ∈ t i
  have hp : MeasurableSet {b : S → E | P b} := by
    simpa [P] using measurableSet_forall_not_mem (S := S) (E := E) Λ₁ s (t := t) ht
  have h_eval :
      (fun b : S → E ↦ isssdFamilyFun ν Λ₁ b ((s : Set S).pi t)) =
        fun b ↦ ite (P b) (∏ i ∈ s ∩ Λ₁, ν i (t i)) 0 := by
    funext b
    simpa [P] using isssdFamilyFun_apply_squareCylinder (ν := ν) Λ₁ s t ht b
  rw [h_eval]
  simpa [P] using
    lintegral_ite_const_eq_mul (μ := isssdFamilyFun ν Λ₂ η) (p := P) hp
      (∏ i ∈ s ∩ Λ₁, ν i (t i))

lemma lintegral_isssdFamilyFun_apply_squareCylinder_eq_union [DecidableEq S] (Λ₁ Λ₂ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    ∫⁻ b, isssdFamilyFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFamilyFun ν Λ₂ η =
      isssdFamilyFun ν (Λ₁ ∪ Λ₂) η ((s : Set S).pi t) := by
  classical
  have hmain := lintegral_isssdFamilyFun_apply_squareCylinder (ν := ν) Λ₁ Λ₂ s t ht η
  have houter := isssdFamilyFun_apply_forall_not_mem (ν := ν) Λ₁ Λ₂ s t ht η
  rw [hmain, houter, isssdFamilyFun_apply_squareCylinder (ν := ν) (Λ₁ ∪ Λ₂) s t ht η]
  by_cases hU : ∀ i ∈ (s : Set S), i ∉ (Λ₁ ∪ Λ₂ : Finset S) → η i ∈ t i
  · have hU' : ∀ i ∈ s, i ∉ Λ₁ ∪ Λ₂ → η i ∈ t i := fun i hi hiU ↦ hU i (by simpa using hi) hiU
    simp only [eq_true hU, eq_true hU', ↓reduceIte]
    exact prod_inter_mul_prod_inter_sdiff_eq_prod_inter_union (s := s) (Λ₁ := Λ₁) (Λ₂ := Λ₂)
      (f := fun i : S ↦ ν i (t i))
  · have hU' : ¬ ∀ i ∈ s, i ∉ Λ₁ ∪ Λ₂ → η i ∈ t i := fun h ↦
      hU fun i hi hiU ↦ h i (by simpa using hi) hiU
    simp only [eq_false hU, eq_false hU', ↓reduceIte, mul_zero]

/-! ### Markov, proper, consistent -/

lemma isProbabilityMeasure_isssdFamilyFun_apply (Λ : Finset S) (η : S → E) :
    IsProbabilityMeasure (isssdFamilyFun ν Λ η) := by
  rw [isssdFamilyFun_apply]
  exact Measure.isProbabilityMeasure_map
    (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE)).aemeasurable

lemma isssdFamilyFun_apply_univ (Λ : Finset S) (η : S → E) :
    isssdFamilyFun ν Λ η Set.univ = 1 := by
  have := isProbabilityMeasure_isssdFamilyFun_apply (ν := ν) Λ η
  simp

lemma isMarkovKernel_isssdFamilyFun (Λ : Finset S) : IsMarkovKernel (isssdFamilyFun ν Λ) :=
  ⟨fun η ↦ isProbabilityMeasure_isssdFamilyFun_apply (ν := ν) Λ η⟩

lemma isProper_isssdFamilyFun (Λ : Finset S) : (isssdFamilyFun ν Λ).IsProper :=
  isProper_juxtMapKernel (S := S) (E := E) (Measure.pi fun i : Λ ↦ ν i)

lemma isssdFamilyFun_comp_isssdFamilyFun_apply_univ (Λ₁ Λ₂ : Finset S) (η : S → E) :
    (((isssdFamilyFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFamilyFun ν Λ₂) η) Set.univ
      = 1 := by
  have h_integrand : (fun b : S → E ↦ isssdFamilyFun ν Λ₁ b Set.univ) = fun _ ↦ (1 : ℝ≥0∞) := by
    funext b
    exact isssdFamilyFun_apply_univ (ν := ν) Λ₁ b
  have := isProbabilityMeasure_isssdFamilyFun_apply (ν := ν) Λ₂ η
  simp [Kernel.comp_apply' _ _ _ MeasurableSet.univ, Kernel.comap_apply, h_integrand]

/-- Georgii (1.25) for the inhomogeneous independent kernels. -/
lemma isssdFamilyFun_comp_isssdFamilyFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFamilyFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFamilyFun ν Λ₂ =
      (isssdFamilyFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by gcongr; exact Finset.subset_union_right) := by
  classical
  ext η
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by simpa [C] using isPiSystem_squareCylindersMeas S E
  have hgen : (inferInstance : MeasurableSpace (S → E)) = .generateFrom C := by
    simpa [C] using generateFrom_squareCylindersMeas S E
  have huniv : (Set.univ : Set (S → E)) ∈ C := by simpa [C] using univ_mem_squareCylindersMeas S E
  have hL_univ :
      (((isssdFamilyFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFamilyFun ν Λ₂) η)
        Set.univ ≠ ∞ := by
    rw [isssdFamilyFun_comp_isssdFamilyFun_apply_univ (ν := ν) Λ₁ Λ₂ η]; simp
  have hmeas_eq :
      (((isssdFamilyFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFamilyFun ν Λ₂) η) =
        ((isssdFamilyFun ν (Λ₁ ∪ Λ₂)).comap id (measurable_id'' <| by gcongr) η) := by
    refine MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (C := C)
      (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hL_univ) ?_
    rintro A ⟨s, t, ht, rfl⟩
    have ht_meas : ∀ i : S, MeasurableSet (t i) := by
      simpa [Set.mem_pi, Set.mem_univ, true_implies] using ht
    have h_rect_meas : MeasurableSet ((s : Set S).pi t) :=
      MeasurableSet.pi s.countable_toSet fun i _ ↦ ht_meas i
    simpa [Kernel.comp_apply' _ _ _ h_rect_meas, Kernel.comap_apply] using
      lintegral_isssdFamilyFun_apply_squareCylinder_eq_union (ν := ν) Λ₁ Λ₂ s t ht_meas η
  simp [hmeas_eq]

lemma isStronglyConsistent_isssdFamilyFun [DecidableEq S] :
    IsStronglyConsistent (isssdFamilyFun ν) :=
  fun Λ₁ Λ₂ ↦ isssdFamilyFun_comp_isssdFamilyFun (ν := ν) Λ₁ Λ₂

lemma isConsistent_isssdFamilyFun : IsConsistent (isssdFamilyFun ν) := by
  classical
  exact (isStronglyConsistent_isssdFamilyFun (ν := ν)).isConsistent

variable (ν)

/-- The **inhomogeneous independent specification**: the sites of a finite volume are resampled
independently, site `i` from the a priori measure `ν i`.

This is Georgii's `Specification.isssd` with a separate a priori measure at each site, the
generalisation used in the second half of the proof of Theorem (8.39). -/
@[simps]
noncomputable def isssdFamily : Specification S E where
  toPreSpecification :=
    { toFun := isssdFamilyFun ν
      isConsistent' := isConsistent_isssdFamilyFun (ν := ν) }
  isMarkovKernel' := isMarkovKernel_isssdFamilyFun (ν := ν)
  isProper' := isProper_isssdFamilyFun (ν := ν)

/-- A constant family of a priori measures recovers Georgii's independent specification. -/
@[simp] lemma isssdFamily_const (ν : Measure E) [IsProbabilityMeasure ν] :
    isssdFamily (S := S) (E := E) (fun _ ↦ ν) = isssd (S := S) (E := E) ν :=
  Specification.ext fun Λ ↦ isssdFamilyFun_const (S := S) (E := E) ν Λ

lemma isStronglyConsistent_isssdFamily [DecidableEq S] :
    IsStronglyConsistent (isssdFamily (S := S) (E := E) ν) :=
  isStronglyConsistent_isssdFamilyFun (ν := ν)

protected lemma IsProper.isssdFamily : (isssdFamily (S := S) (E := E) ν).IsProper :=
  (isssdFamily ν).isProper

/-- On events measurable inside the finite volume `Λ`, the inhomogeneous independent kernel with
any boundary condition gives the same mass as the infinite product measure `⨂ i, ν i`. -/
lemma isssdFamily_apply_of_mem_cylinderEvents (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (Λ : Set S)] A) :
    isssdFamily (S := S) (E := E) ν Λ η A = Measure.infinitePi ν A := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  have hmeasA : MeasurableSet (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B) := Λ.measurable_restrict hB
  have hcomp : ∀ ζ : Π _ : Λ, E, Λ.restrict (π := fun _ : S ↦ E) (juxt (Λ : Set S) η ζ) = ζ := by
    intro ζ
    funext i
    exact juxt_apply_of_mem (by simp) ζ
  have h1 : isssdFamily (S := S) (E := E) ν Λ η (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B)
      = Measure.pi (fun i : Λ ↦ ν i) B := by
    rw [show (isssdFamily (S := S) (E := E) ν Λ) η
        = Measure.map (juxt (Λ : Set S) η) (Measure.pi fun i : Λ ↦ ν i) from rfl,
      Measure.map_apply Measurable.juxt hmeasA]
    congr 1
    ext ζ
    simp [Set.mem_preimage, hcomp ζ]
  have h2 : Measure.infinitePi ν (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B) =
      Measure.pi (fun i : Λ ↦ ν i) B := by
    rw [← Measure.infinitePi_map_restrict (μ := ν) (I := Λ),
      Measure.map_apply Λ.measurable_restrict hB]
  rw [h1, h2]

/-!
### Resampling specifications

Georgii's Notation (1.26) writes the reference kernel as `λ_Λ(dω | η) = λ^Λ(dω_Λ) δ_{η_{S∖Λ}}`:
the volume `Λ` is resampled, the exterior is frozen. `Specification.IsResampling` records exactly
this shape, and is all that the normalization of a premodifier (Georgii (1.31) ⇒ (1.30)) uses
about the reference kernels. Both `Specification.isssd` and `Specification.isssdFamily` are
resampling specifications.
-/

section Resampling

variable {S E : Type*} {mE : MeasurableSpace E} {γ : Specification S E}
  {ρ : Finset S → (S → E) → ℝ≥0∞}

variable (γ) in
/-- A specification *resamples volumes* if each finite-volume kernel is the image, under
juxtaposition with the boundary condition, of a measure on the configurations of that volume.

This is the shape of Georgii's reference kernels `λ_Λ` in Notation (1.26). -/
def IsResampling : Prop :=
  ∀ Λ : Finset S, ∃ μ : Measure (Λ → E), ∀ η : S → E, γ Λ η = μ.map (juxt (Λ : Set S) η)

lemma isResampling_isssdFamily (ν : S → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    IsResampling (isssdFamily (S := S) (E := E) ν) :=
  fun Λ ↦ ⟨Measure.pi fun i : Λ ↦ ν i, fun _ ↦ rfl⟩

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

/-! ### Normalizing a premodifier against an arbitrary reference specification -/

variable (γ ρ) in
/-- The partition function of a density family `ρ` relative to a reference specification `γ`:
`Z_Λ(η) = γ_Λ(ρ_Λ | η)`. For `γ = Specification.isssd ν` this is
`Specification.premodifierZ`. -/
noncomputable def relZ (Λ : Finset S) (η : S → E) : ℝ≥0∞ := ∫⁻ x, ρ Λ x ∂(γ Λ η)

variable (γ ρ) in
/-- The normalized density `ρ'_Λ = ρ_Λ / Z_Λ` relative to a reference specification `γ`.
For `γ = Specification.isssd ν` this is `Specification.premodifierNorm`. -/
noncomputable def relNorm (Λ : Finset S) (η : S → E) : ℝ≥0∞ := ρ Λ η / relZ γ ρ Λ η

variable (γ ρ) in
/-- Georgii's λ-admissibility relative to a reference specification: every finite-volume
partition function is nonzero and finite. -/
def IsRelAdmissible : Prop := ∀ (Λ : Finset S) (η : S → E), relZ γ ρ Λ η ≠ 0 ∧ relZ γ ρ Λ η ≠ ⊤

lemma relZ_isssd (ν : Measure E) [IsProbabilityMeasure ν] :
    relZ (isssd (S := S) (E := E) ν) ρ = premodifierZ (S := S) (E := E) ν ρ := rfl

lemma relNorm_isssd (ν : Measure E) [IsProbabilityMeasure ν] :
    relNorm (isssd (S := S) (E := E) ν) ρ = premodifierNorm (S := S) (E := E) ν ρ := rfl

lemma isRelAdmissible_isssd_iff (ν : Measure E) [IsProbabilityMeasure ν] :
    IsRelAdmissible (isssd (S := S) (E := E) ν) ρ ↔
      IsPremodifierAdmissible (S := S) (E := E) ν ρ := Iff.rfl

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

/-- **Georgii (1.31) ⇒ (1.30).** Normalizing a premodifier against a resampling reference
specification produces a modifier, hence a specification.

This is `Specification.IsPremodifier.isModifier_premodifierNorm` with the independent
specification `Specification.isssd ν` replaced by an arbitrary resampling reference — in
particular by the inhomogeneous `Specification.isssdFamily ν`. -/
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

end Resampling

end Specification

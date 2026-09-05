/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Logic.Function.DependsOn

/-!
# Reflection positivity of product measures

Let `ν` be a family of finite measures on `E` indexed by a finite type `ι`, and let `r` be a
permutation of `ι` with `ν (r i) = ν i`.  Suppose `P ⊆ ι` is a set such that every site which
is not fixed by `r` lies in exactly one of `P` and `r P`.  Then for every bounded measurable `f`
depending only on the coordinates in `P`,

  `∫ f ω · f (ω ∘ r) d(⨂ᵢ ν i) ≥ 0`.

This is the "trivial example" of reflection positivity in Georgii, *Gibbs Measures and Phase
Transitions*, §17.2: the product measure is positive both for reflections in a plane between
the sites (no fixed points, `integral_mul_comp_nonneg_of_disjoint`) and for reflections in a
plane through the sites (`integral_mul_comp_nonneg`).  The proof is Fubini: conditionally on
the fixed coordinates, `f` and `f ∘ r` are independent copies of the same function, so the
integral is the integral of a square.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E] {ν : ι → Measure E}
  [∀ i, IsFiniteMeasure (ν i)]

/-- A bounded measurable real function is integrable against a finite measure. -/
theorem Integrable.of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa using hC x)

/-- **Reflection positivity of a product measure, for a reflection without fixed points.**
If the permutation `r` of the sites exchanges `P` and its complement and preserves the marginals,
then `∫ f · f∘r ≥ 0` for every bounded measurable `f` depending only on the coordinates in `P`:
under `ν^ι = ν^P ⊗ ν^{Pᶜ}` the two factors are independent copies of the same function of the
`P`-coordinates, so the integral is a square. -/
theorem integral_mul_comp_nonneg_of_disjoint (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    {P : Set ι} (hP : ∀ i, i ∈ P ↔ r i ∉ P) {f : (ι → E) → ℝ} (hf : Measurable f)
    (hdep : DependsOn f P) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    0 ≤ ∫ ω, f ω * f (ω ∘ r) ∂(Measure.pi ν) := by
  classical
  set Ψ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι ↦ E) (· ∈ P) with hΨdef
  have hΨ : MeasurePreserving Ψ (Measure.pi ν)
      ((Measure.pi fun i : {i // i ∈ P} ↦ ν i).prod (Measure.pi fun i : {i // i ∉ P} ↦ ν i)) :=
    measurePreserving_piEquivPiSubtypeProd ν (· ∈ P)
  -- the bijection `P ≃ Pᶜ` induced by `r`
  let e : {i // i ∈ P} ≃ {i // i ∉ P} := r.subtypeEquiv hP
  have he : ∀ i : {i // i ∈ P}, (e i : ι) = r i := fun _ ↦ rfl
  have he' : ∀ j : {i // i ∉ P}, (e.symm j : ι) = r.symm j := fun _ ↦ rfl
  have hΨsymm : ∀ (x : {i // i ∈ P} → E) (y : {i // i ∉ P} → E) (i : ι),
      Ψ.symm (x, y) i = if h : i ∈ P then x ⟨i, h⟩ else y ⟨i, h⟩ := fun _ _ _ ↦ rfl
  -- the function of the `P`-coordinates
  set g : ({i // i ∈ P} → E) → ℝ := fun x ↦ f (Ψ.symm (x, x ∘ e.symm)) with hg
  have h1 : ∀ (x : {i // i ∈ P} → E) (y : {i // i ∉ P} → E), f (Ψ.symm (x, y)) = g x := by
    intro x y
    refine hdep fun i hi ↦ ?_
    simp only [hΨsymm, hi, dite_true]
  have h2 : ∀ (x : {i // i ∈ P} → E) (y : {i // i ∉ P} → E),
      f (Ψ.symm (x, y) ∘ r) = g (y ∘ e) := by
    intro x y
    refine hdep fun i hi ↦ ?_
    have hri : r i ∉ P := (hP i).1 hi
    simp only [Function.comp_apply, hΨsymm, hri, dite_false, hi, dite_true]
    rfl
  have hgm : Measurable g :=
    hf.comp (Ψ.symm.measurable.comp (measurable_id.prodMk
      (measurable_pi_lambda _ fun j ↦ measurable_pi_apply (e.symm j))))
  have hgC : ∀ x, |g x| ≤ C := fun x ↦ hC _
  -- transport along `Ψ` and factorize
  have hint : ∫ ω, f ω * f (ω ∘ r) ∂(Measure.pi ν)
      = ∫ p, g p.1 * g (p.2 ∘ e)
          ∂((Measure.pi fun i : {i // i ∈ P} ↦ ν i).prod
            (Measure.pi fun i : {i // i ∉ P} ↦ ν i)) := by
    rw [← hΨ.symm.integral_comp' fun ω ↦ f ω * f (ω ∘ r)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    obtain ⟨x, y⟩ := p
    simp only [h1, h2]
  -- the reflected factor has the same integral as the unreflected one
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ P} ↦ E) e.symm)
      (Measure.pi fun j : {i // i ∉ P} ↦ ν j) (Measure.pi fun i : {i // i ∈ P} ↦ ν i) := by
    have h := measurePreserving_piCongrLeft (α := fun _ ↦ E) (fun i : {i // i ∈ P} ↦ ν i) e.symm
    have hν' : (fun j : {i // i ∉ P} ↦ ν (e.symm j)) = fun j : {i // i ∉ P} ↦ ν j := by
      funext j
      rw [he', ← hν (r.symm j), Equiv.apply_symm_apply]
    rwa [hν'] at h
  have hcomp : ∀ y : {i // i ∉ P} → E,
      MeasurableEquiv.piCongrLeft (fun _ : {i // i ∈ P} ↦ E) e.symm y = y ∘ e := by
    intro y
    funext i
    obtain ⟨j, rfl⟩ := e.symm.surjective i
    rw [MeasurableEquiv.piCongrLeft_apply_apply, Function.comp_apply, Equiv.apply_symm_apply]
  have hrefl : ∫ y, g (y ∘ e) ∂(Measure.pi fun j : {i // i ∉ P} ↦ ν j)
      = ∫ x, g x ∂(Measure.pi fun i : {i // i ∈ P} ↦ ν i) := by
    rw [← hmp.integral_comp' g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by simp only [hcomp])
  rw [hint, integral_prod_mul (fun x ↦ g x) (fun y ↦ g (y ∘ e)), hrefl]
  exact mul_self_nonneg _

/-- **Reflection positivity of a product measure.** Let `r` be a permutation of the sites
preserving the marginals, and `P` a set of sites such that every site not fixed by `r` lies in
exactly one of `P` and `r P`.  Then `∫ f · f∘r ≥ 0` for every bounded measurable `f` depending
only on the coordinates in `P`.  Conditionally on the coordinates fixed by `r`, this is the
fixed-point-free case `integral_mul_comp_nonneg_of_disjoint`. -/
theorem integral_mul_comp_nonneg (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i) {P : Set ι}
    (hP : ∀ i, r i ≠ i → (i ∈ P ↔ r i ∉ P)) {f : (ι → E) → ℝ} (hf : Measurable f)
    (hdep : DependsOn f P) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    0 ≤ ∫ ω, f ω * f (ω ∘ r) ∂(Measure.pi ν) := by
  classical
  set L : Set ι := {i | r i = i} with hL
  set Ψ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι ↦ E) (· ∈ L) with hΨdef
  have hΨ : MeasurePreserving Ψ (Measure.pi ν)
      ((Measure.pi fun i : {i // i ∈ L} ↦ ν i).prod (Measure.pi fun i : {i // i ∉ L} ↦ ν i)) :=
    measurePreserving_piEquivPiSubtypeProd ν (· ∈ L)
  have hΨsymm : ∀ (x : {i // i ∈ L} → E) (y : {i // i ∉ L} → E) (i : ι),
      Ψ.symm (x, y) i = if h : i ∈ L then x ⟨i, h⟩ else y ⟨i, h⟩ := fun _ _ _ ↦ rfl
  -- `r` restricted to the sites it moves
  have hrL : ∀ i, i ∉ L ↔ r i ∉ L := by
    intro i
    simp only [hL, mem_ofPred_eq, not_iff_not]
    exact ⟨fun h ↦ by simp [h], fun h ↦ r.injective h⟩
  let r' : {i // i ∉ L} ≃ {i // i ∉ L} := r.subtypeEquiv hrL
  have hr' : ∀ j : {i // i ∉ L}, (r' j : ι) = r j := fun _ ↦ rfl
  -- `f` with the fixed coordinates frozen
  set F : ({i // i ∈ L} → E) → ({i // i ∉ L} → E) → ℝ := fun a y ↦ f (Ψ.symm (a, y)) with hF
  have hFr : ∀ a y, f (Ψ.symm (a, y) ∘ r) = F a (y ∘ r') := by
    intro a y
    have : Ψ.symm (a, y) ∘ r = Ψ.symm (a, y ∘ r') := by
      funext i
      simp only [Function.comp_apply, hΨsymm]
      by_cases hi : i ∈ L
      · have hi' : r i = i := hi
        have hri : r i ∈ L := by rw [hi']; exact hi
        simp only [hri, hi, dite_true]
        congr 1
        exact Subtype.ext hi'
      · have hri : r i ∉ L := (hrL i).1 hi
        simp only [hri, hi, dite_false]
        rfl
    rw [this]
  have hFm : ∀ a, Measurable (F a) := fun a ↦
    hf.comp (Ψ.symm.measurable.comp measurable_prodMk_left)
  have hFC : ∀ a y, |F a y| ≤ C := fun a y ↦ hC _
  have hFdep : ∀ a, DependsOn (F a) {j : {i // i ∉ L} | (j : ι) ∈ P} := by
    intro a y y' hyy'
    refine hdep fun i hi ↦ ?_
    simp only [hΨsymm]
    by_cases hiL : i ∈ L
    · simp only [hiL, dite_true]
    · simp only [hiL, dite_false]
      exact hyy' ⟨i, hiL⟩ hi
  have hP' : ∀ j : {i // i ∉ L}, j ∈ {j : {i // i ∉ L} | (j : ι) ∈ P}
      ↔ r' j ∉ {j : {i // i ∉ L} | (j : ι) ∈ P} := by
    intro j
    simp only [mem_ofPred_eq, hr']
    exact hP j j.2
  have hν' : ∀ j : {i // i ∉ L}, (fun j : {i // i ∉ L} ↦ ν j) (r' j) = ν j := fun j ↦ by
    simp only [hr']
    exact hν j
  have hinner : ∀ a, 0 ≤ ∫ y, F a y * F a (y ∘ r') ∂(Measure.pi fun j : {i // i ∉ L} ↦ ν j) :=
    fun a ↦ integral_mul_comp_nonneg_of_disjoint (ν := fun j : {i // i ∉ L} ↦ ν j) r' hν' hP'
      (hFm a) (hFdep a) (hFC a)
  -- Fubini
  have hI : Integrable (fun p : ({i // i ∈ L} → E) × ({i // i ∉ L} → E) ↦
      f (Ψ.symm p) * f (Ψ.symm p ∘ r))
      ((Measure.pi fun i : {i // i ∈ L} ↦ ν i).prod (Measure.pi fun i : {i // i ∉ L} ↦ ν i)) := by
    refine Integrable.of_abs_le ((hf.comp Ψ.symm.measurable).mul (hf.comp
      ((measurable_pi_lambda _ fun i ↦ measurable_pi_apply (r i)).comp Ψ.symm.measurable)))
      (C := |C| * |C|) fun p ↦ ?_
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self _)) ((hC _).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hint : ∫ ω, f ω * f (ω ∘ r) ∂(Measure.pi ν)
      = ∫ a, ∫ y, F a y * F a (y ∘ r') ∂(Measure.pi fun j : {i // i ∉ L} ↦ ν j)
          ∂(Measure.pi fun i : {i // i ∈ L} ↦ ν i) := by
    rw [← hΨ.symm.integral_comp' fun ω ↦ f ω * f (ω ∘ r),
      integral_prod (fun p ↦ f (Ψ.symm p) * f (Ψ.symm p ∘ r)) hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a ↦ ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    simp only [hFr]
    rfl
  rw [hint]
  exact integral_nonneg hinner

end MeasureTheory

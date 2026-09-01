/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite products and densities

Three general-purpose measure-theoretic facts used to rescale the a priori measure of a
`λ`-specification (Georgii, *Gibbs Measures and Phase Transitions*, Remark (1.28)(3)).

## Main results

* `MeasureTheory.lintegral_pi_prod`: Tonelli's theorem for a product of one-variable functions on a
  finite product measure, `∫⁻ x, ∏ i, g i (x i) = ∏ i, ∫⁻ y, g i y`.
* `MeasureTheory.Measure.pi_withDensity`: a finite product of density-modified measures is the
  product measure with the product density,
  `∏ᵢ (μ i).withDensity (r i) = (∏ᵢ μ i).withDensity (fun x ↦ ∏ i, r i (x i))`.
* `MeasureTheory.map_withDensity_comp`: pushing a density forward along a measurable map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function
open scoped ENNReal

namespace MeasureTheory

/-- **Tonelli's theorem for a product of single-variable functions.** The `ℝ≥0∞`-valued companion
of `MeasureTheory.integral_fintype_prod_eq_prod`. -/
theorem lintegral_pi_prod {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {g : ∀ i, α i → ℝ≥0∞} (hg : ∀ i, Measurable (g i)) :
    ∫⁻ x, ∏ i, g i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ y, g i y ∂(μ i) := by
  classical
  set f : (∀ i, α i) → ℝ≥0∞ := fun x ↦ ∏ i, g i (x i) with hf_def
  have hf : Measurable f :=
    Finset.measurable_prod _ fun i _ ↦ (hg i).comp (measurable_pi_apply i)
  rcases isEmpty_or_nonempty (∀ i, α i) with hE | hE
  · have h0 : Measure.pi μ = 0 := by
      have huniv : (Set.univ : Set (∀ i, α i)) = ∅ := Set.univ_eq_empty_iff.2 hE
      refine Measure.measure_univ_eq_zero.mp ?_
      rw [huniv]; simp
    have hex : ∃ i : ι, IsEmpty (α i) := by
      by_contra hcon
      push Not at hcon
      exact hE.elim fun i ↦ (hcon i).some
    obtain ⟨i, hi⟩ := hex
    have hμi : (μ i) = 0 := by
      refine Measure.measure_univ_eq_zero.mp ?_
      have huniv : (Set.univ : Set (α i)) = ∅ := Set.univ_eq_empty_iff.2 hi
      rw [huniv]; simp
    rw [h0]
    simp only [lintegral_zero_measure]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hμi])).symm
  obtain ⟨x₀⟩ := hE
  have key : ∀ (s : Finset ι) (x : ∀ i, α i),
      (∫⋯∫⁻_s, f ∂μ) x = (∏ i ∈ s, ∫⁻ y, g i y ∂(μ i)) * ∏ i ∈ sᶜ, g i (x i) := by
    intro s
    induction s using Finset.induction with
    | empty => intro x; simp [f]
    | insert j s hj ih =>
        intro x
        rw [lmarginal_insert f hf hj x]
        have hstep : ∀ y : α j,
            (∫⋯∫⁻_s, f ∂μ) (Function.update x j y) =
              (∏ i ∈ s, ∫⁻ z, g i z ∂(μ i)) *
                (g j y * ∏ i ∈ (insert j s)ᶜ, g i (x i)) := by
          intro y
          rw [ih (Function.update x j y)]
          congr 1
          have hjs : j ∈ sᶜ := by simpa using hj
          rw [← Finset.mul_prod_erase _ _ hjs, Finset.compl_insert]
          simp only [Function.update_self]
          congr 1
          refine Finset.prod_congr rfl fun i hi ↦ ?_
          have hij : i ≠ j := Finset.ne_of_mem_erase hi
          simp [Function.update_of_ne hij]
        calc ∫⁻ y, (∫⋯∫⁻_s, f ∂μ) (Function.update x j y) ∂(μ j)
            = ∫⁻ y, ((∏ i ∈ s, ∫⁻ z, g i z ∂(μ i)) * ∏ i ∈ (insert j s)ᶜ, g i (x i))
                * g j y ∂(μ j) := by
              refine lintegral_congr fun y ↦ ?_
              rw [hstep y]; ring
          _ = ((∏ i ∈ s, ∫⁻ z, g i z ∂(μ i)) * ∏ i ∈ (insert j s)ᶜ, g i (x i))
                * ∫⁻ y, g j y ∂(μ j) := lintegral_const_mul _ (hg j)
          _ = (∏ i ∈ insert j s, ∫⁻ y, g i y ∂(μ i)) * ∏ i ∈ (insert j s)ᶜ, g i (x i) := by
              rw [Finset.prod_insert hj]; ring
  have h := key Finset.univ x₀
  rw [lintegral_eq_lmarginal_univ (μ := μ) (f := f) x₀]
  simpa using h

/-- **A finite product of density-modified measures.** Georgii's rescaling `λ̃ = r · λ` turns the
finite-volume product measure `λ̃^Λ` into `λ^Λ` with the density `ζ ↦ ∏_{i ∈ Λ} r(ζ i)`. -/
theorem Measure.pi_withDensity {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {r : ∀ i, α i → ℝ≥0∞} (hr : ∀ i, Measurable (r i))
    [∀ i, SigmaFinite ((μ i).withDensity (r i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (r i))
      = (Measure.pi μ).withDensity (fun x ↦ ∏ i, r i (x i)) := by
  classical
  refine Measure.pi_eq ?_
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.univ.pi s).indicator (fun x : ∀ i, α i ↦ ∏ i, r i (x i))
      = fun x ↦ ∏ i, (s i).indicator (r i) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ ↦
        (Set.indicator_of_mem (hx i (Set.mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, forall_const, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind, lintegral_pi_prod μ (g := fun i ↦ (s i).indicator (r i))
    (fun i ↦ (hr i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]

/-- Pushing a density forward along a measurable map. -/
theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : Measure α) {J : α → β} (hJ : Measurable J) {G : β → ℝ≥0∞} (hG : Measurable G) :
    (m.withDensity (fun x ↦ G (J x))).map J = (m.map J).withDensity G := by
  ext A hA
  rw [Measure.map_apply hJ hA, withDensity_apply _ (hJ hA), withDensity_apply _ hA,
    ← lintegral_indicator (hJ hA), ← lintegral_indicator hA,
    lintegral_map (hG.indicator hA) hJ]
  refine lintegral_congr fun x ↦ ?_
  by_cases hx : J x ∈ A
  · rw [Set.indicator_of_mem (show x ∈ J ⁻¹' A from hx), Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem (show x ∉ J ⁻¹' A from hx), Set.indicator_of_notMem hx]

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiSeries
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Finite measures on the torus and their Fourier–Stieltjes transforms

For a finite measure `α` on `UnitAddTorus d = d → ℝ/ℤ` the *Fourier–Stieltjes coefficients*
`n ↦ ∫ z, mFourier n z ∂α` determine `α`: the monomials span a dense subalgebra of
`C(UnitAddTorus d, ℂ)` (`UnitAddTorus.exists_norm_sub_sum_mul_mFourier_le`), and a finite Borel
measure on a metric space is determined by the integrals of bounded continuous functions
(`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`).

## Main statements

* `UnitAddTorus.integrable_mFourier`: the monomials are integrable against a finite measure.
* `UnitAddTorus.ext_of_integral_mFourier_eq`: two finite measures with the same
  Fourier–Stieltjes coefficients are equal.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

open Set MeasureTheory

/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The monomial `z ↦ z^n` is integrable against any finite measure on the torus. -/
lemma integrable_mFourier (α : Measure (UnitAddTorus d)) [IsFiniteMeasure α] (n : d → ℤ) :
    Integrable (fun z ↦ mFourier n z) α :=
  Integrable.mono' (integrable_const (1 : ℝ)) (mFourier n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ by simp)

/-- The real part of a monomial is integrable against any finite measure on the torus. -/
lemma integrable_re_mFourier (α : Measure (UnitAddTorus d)) [IsFiniteMeasure α] (n : d → ℤ) :
    Integrable (fun z ↦ (mFourier n z).re) α :=
  (integrable_mFourier α n).re

/-- **Finite measures on the torus are determined by their Fourier–Stieltjes coefficients.** -/
theorem ext_of_integral_mFourier_eq {α β : Measure (UnitAddTorus d)}
    [IsFiniteMeasure α] [IsFiniteMeasure β]
    (h : ∀ n : d → ℤ, ∫ z, mFourier n z ∂α = ∫ z, mFourier n z ∂β) : α = β := by
  refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
  set A : ℝ := (α univ).toReal with hA
  set B : ℝ := (β univ).toReal with hB
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  -- The key estimate: the two integrals differ by at most `ε (A + B)` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → |∫ z, f z ∂α - ∫ z, f z ∂β| ≤ ε * (A + B) := by
    intro ε hε
    obtain ⟨I, c, hc⟩ := exists_norm_sub_sum_mul_mFourier_le
      (⟨fun z ↦ ((f z : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
        C(UnitAddTorus d, ℂ)) hε
    simp only [ContinuousMap.coe_mk] at hc
    -- Both measures integrate the trigonometric polynomial to the same value.
    have hpolyint : ∀ (γ : Measure (UnitAddTorus d)) (_ : IsFiniteMeasure γ),
        Integrable (fun z ↦ ∑ j ∈ I, c j * mFourier j z) γ := fun γ _ ↦
      integrable_finsetSum _ fun j _ ↦ (integrable_mFourier γ j).const_mul _
    have hpoly : ∀ (γ : Measure (UnitAddTorus d)) (_ : IsFiniteMeasure γ),
        ∫ z, (∑ j ∈ I, c j * mFourier j z) ∂γ = ∑ j ∈ I, c j * ∫ z, mFourier j z ∂γ := by
      intro γ _
      rw [integral_finsetSum _ fun j _ ↦ (integrable_mFourier γ j).const_mul _]
      exact Finset.sum_congr rfl fun j _ ↦ integral_const_mul _ _
    have hfint : ∀ (γ : Measure (UnitAddTorus d)) (_ : IsFiniteMeasure γ),
        Integrable (fun z ↦ ((f z : ℝ) : ℂ)) γ := fun γ _ ↦
      (f.integrable γ).ofReal
    -- The error made by replacing `f` by the polynomial.
    have hbound : ∀ (γ : Measure (UnitAddTorus d)) (_ : IsFiniteMeasure γ),
        ‖((∫ z, f z ∂γ : ℝ) : ℂ) - ∑ j ∈ I, c j * ∫ z, mFourier j z ∂γ‖
          ≤ ε * (γ univ).toReal := by
      intro γ hγ
      have hsub : ((∫ z, f z ∂γ : ℝ) : ℂ) - ∑ j ∈ I, c j * ∫ z, mFourier j z ∂γ
          = ∫ z, (((f z : ℝ) : ℂ) - ∑ j ∈ I, c j * mFourier j z) ∂γ := by
        rw [integral_sub (hfint γ hγ) (hpolyint γ hγ), hpoly γ hγ, integral_complex_ofReal]
      rw [hsub]
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hc)
    have hα := hbound α inferInstance
    have hβ := hbound β inferInstance
    have hsame : ∑ j ∈ I, c j * ∫ z, mFourier j z ∂α = ∑ j ∈ I, c j * ∫ z, mFourier j z ∂β :=
      Finset.sum_congr rfl fun j _ ↦ by rw [h j]
    have : ‖((∫ z, f z ∂α : ℝ) : ℂ) - ((∫ z, f z ∂β : ℝ) : ℂ)‖ ≤ ε * A + ε * B := by
      calc ‖((∫ z, f z ∂α : ℝ) : ℂ) - ((∫ z, f z ∂β : ℝ) : ℂ)‖
          = ‖(((∫ z, f z ∂α : ℝ) : ℂ) - ∑ j ∈ I, c j * ∫ z, mFourier j z ∂α)
              - (((∫ z, f z ∂β : ℝ) : ℂ) - ∑ j ∈ I, c j * ∫ z, mFourier j z ∂β)‖ := by
            rw [hsame]; ring_nf
        _ ≤ _ := norm_sub_le _ _
        _ ≤ ε * A + ε * B := add_le_add hα hβ
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  -- Let `ε → 0`.
  refine sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm ?_ (abs_nonneg _)))
  by_contra hc
  rw [not_le] at hc
  set X : ℝ := |∫ z, f z ∂α - ∫ z, f z ∂β| with hX
  have hD : (0 : ℝ) < A + B + 1 := by linarith
  have h1 := key (X / (2 * (A + B + 1))) (by positivity)
  have hEq : X / (2 * (A + B + 1)) * (A + B + 1) = X / 2 := by field_simp
  have h2 : X / (2 * (A + B + 1)) * (A + B) ≤ X / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hEq.le
  linarith

end UnitAddTorus

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential moments from an exponential tail bound

A nonnegative random variable whose tail is dominated by `B e^{-b t}` has a finite exponential
moment of every order `a < b`, with the explicit bound

`∫ e^{a f} dμ ≤ 1 + a B / (b - a)`.

The proof is the layer cake formula `∫ (∫_0^{f} g) dμ = ∫_{t > 0} μ{f ≥ t} g(t) dt`
(`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`) for `g(t) = a e^{a t}`.

## Main results

* `MeasureTheory.lintegral_exp_le_of_measure_le`
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `∫_0^y a e^{a t} dt = e^{a y} - 1`. -/
private lemma intervalIntegral_exp_mul (a y : ℝ) :
    ∫ t in (0 : ℝ)..y, a * Real.exp (a * t) = Real.exp (a * y) - 1 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) y,
      HasDerivAt (fun s : ℝ ↦ Real.exp (a * s)) (a * Real.exp (a * t)) t := by
    intro t _
    have h : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
      simpa using (hasDerivAt_id t).const_mul a
    simpa [mul_comm] using h.exp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)]
  simp

/-- **An exponential tail bound gives an exponential moment.**

If `f ≥ 0` and `μ {f ≥ t} ≤ B e^{-b t}` for every `t ≥ 0`, then for every `0 < a < b`

`∫ e^{a f} dμ ≤ 1 + a B / (b - a)`.

Taking `b = 2a` gives Georgii's bound `1 + B`. -/
theorem lintegral_exp_le_of_measure_le [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : AEMeasurable f μ) (hf0 : 0 ≤ᵐ[μ] f) {a b B : ℝ} (ha : 0 < a) (hab : a < b)
    (hB : ∀ t, 0 ≤ t → μ {x | t ≤ f x} ≤ ENNReal.ofReal (B * Real.exp (-(b * t)))) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (a * f x)) ∂μ ≤ 1 + ENNReal.ofReal (a * B / (b - a)) := by
  have hba : 0 < b - a := by linarith
  have hf0' : ∀ᵐ x ∂μ, (0 : ℝ) ≤ f x := hf0
  -- The set where `f ≥ 0` carries all the mass.
  have hone : (1 : ℝ≥0∞) ≤ μ {x | (0 : ℝ) ≤ f x} := by
    have hnull : μ {x | ¬ ((0 : ℝ) ≤ f x)} = 0 := ae_iff.1 hf0'
    have hcover : (Set.univ : Set α) ⊆ {x | (0 : ℝ) ≤ f x} ∪ {x | ¬ ((0 : ℝ) ≤ f x)} := by
      intro x _
      by_cases h : (0 : ℝ) ≤ f x
      · exact Or.inl h
      · exact Or.inr h
    calc (1 : ℝ≥0∞) = μ Set.univ := measure_univ.symm
      _ ≤ μ ({x | (0 : ℝ) ≤ f x} ∪ {x | ¬ ((0 : ℝ) ≤ f x)}) := measure_mono hcover
      _ ≤ μ {x | (0 : ℝ) ≤ f x} + μ {x | ¬ ((0 : ℝ) ≤ f x)} := measure_union_le _ _
      _ = μ {x | (0 : ℝ) ≤ f x} := by rw [hnull, add_zero]
  -- The tail bound at `t = 0` therefore forces `B ≥ 0`.
  have hB0 : 0 ≤ B := by
    by_contra h
    have h0 := hB 0 le_rfl
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at h0
    rw [ENNReal.ofReal_of_nonpos (le_of_not_ge h)] at h0
    exact absurd (hone.trans h0) (by simp)
  set g : ℝ → ℝ := fun t ↦ a * Real.exp (a * t) with hg
  have hgnn : ∀ t, 0 ≤ g t := fun t ↦ by positivity
  have hgint : ∀ t > (0 : ℝ), IntervalIntegrable g volume 0 t := fun t _ ↦
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _
  -- Step 1: the layer cake formula.
  have hlayer : ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..(f x), g t) ∂μ
      = ∫⁻ t in Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t) :=
    lintegral_comp_eq_lintegral_meas_le_mul μ hf0 hf hgint
      (Filter.Eventually.of_forall fun t ↦ hgnn t)
  -- Step 2: rewrite the exponential moment through the layer cake integrand.
  have hsplit : ∫⁻ x, ENNReal.ofReal (Real.exp (a * f x)) ∂μ
      = 1 + ∫⁻ x, ENNReal.ofReal (∫ t in (0 : ℝ)..(f x), g t) ∂μ := by
    have h1 : ∫⁻ x, ENNReal.ofReal (Real.exp (a * f x)) ∂μ
        = ∫⁻ x, (1 + ENNReal.ofReal (∫ t in (0 : ℝ)..(f x), g t)) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hf0'] with x hx
      have hnn : (0 : ℝ) ≤ Real.exp (a * f x) - 1 := by
        have : (1 : ℝ) ≤ Real.exp (a * f x) := Real.one_le_exp (by positivity)
        linarith
      rw [hg]
      simp only
      rw [intervalIntegral_exp_mul, ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one hnn]
      congr 1
      ring
    rw [h1, lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  -- Step 3: bound the layer cake integral.
  have hbound : ∫⁻ t in Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t)
      ≤ ENNReal.ofReal (a * B / (b - a)) := by
    have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {x | t ≤ f x} * ENNReal.ofReal (g t)
        ≤ ENNReal.ofReal (a * B * Real.exp (-(b - a) * t)) := by
      intro t ht
      have hreal : B * Real.exp (-(b * t)) * (a * Real.exp (a * t))
          = a * B * Real.exp (-(b - a) * t) := by
        rw [show -(b - a) * t = -(b * t) + a * t by ring, Real.exp_add]
        ring
      refine le_trans (mul_le_mul' (hB t (le_of_lt ht)) le_rfl) (le_of_eq ?_)
      rw [hg]
      simp only
      rw [← ENNReal.ofReal_mul (by positivity), hreal]
    have hintegrable : IntegrableOn (fun t : ℝ ↦ a * B * Real.exp (-(b - a) * t)) (Ioi 0) :=
      (integrableOn_exp_mul_Ioi (a := -(b - a)) (by linarith) 0).const_mul (a * B)
    have hI : ∫ t in Ioi (0 : ℝ), Real.exp (-(b - a) * t) = 1 / (b - a) := by
      rw [integral_exp_mul_Ioi (a := -(b - a)) (by linarith) 0, mul_zero, Real.exp_zero,
        neg_div_neg_eq]
    calc ∫⁻ t in Ioi 0, μ {x | t ≤ f x} * ENNReal.ofReal (g t)
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (a * B * Real.exp (-(b - a) * t)) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = ENNReal.ofReal (∫ t in Ioi 0, a * B * Real.exp (-(b - a) * t)) :=
          (ofReal_integral_eq_lintegral_ofReal hintegrable
            (Filter.Eventually.of_forall fun t ↦ by positivity)).symm
      _ = ENNReal.ofReal (a * B / (b - a)) := by
          congr 1
          rw [integral_const_mul, hI]
          field_simp
  rw [hsplit, hlayer]
  exact add_le_add le_rfl hbound

end MeasureTheory

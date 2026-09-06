/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Comparing two exponentially tilted probability measures

Two energies `H₁`, `H₂` on a finite measure space `(X, m)` give two normalised laws

`K_i(A) = (∫_A e^{-H_i} dm) / (∫ e^{-H_i} dm)`.

If both energies are dominated by a nonnegative `Q` with an integrable exponential moment, and the
two energies differ by at most `δ Q`, then the two laws differ by at most a multiple of `δ`,
*uniformly in the event* `A`.  This is the elementary core of Georgii's continuity result for
Gibbsian specifications (*Gibbs Measures and Phase Transitions*, Proposition (4.19)); the
quantitative form below is what a comparison of two finite-volume Gibbs kernels in the same volume,
with the same boundary condition and the same a priori measure, needs.

## Main results

* `Real.abs_exp_neg_sub_one_le`: `|e^{-v} - 1| ≤ |v| e^{|v|}`, from `1 - u ≤ e^{-u}`.
* `MeasureTheory.abs_expTilt_sub_le`: if `|H₂| ≤ c Q`, `|H₁ - H₂| ≤ δ Q` with `0 ≤ δ ≤ 1` and
  `Q ≥ 0`, and `Γ = ∫ e^{(c+2)Q} dm < ∞`, `β = ∫ e^{-cQ} dm > 0` satisfy `δ Γ ≤ β / 2`, then
  `|K₁(A) - K₂(A)| ≤ 4 Γ δ / β` for every measurable `A`.

The two constants are the ones dictated by the proof: `β` bounds the partition functions from
below and `Γ` bounds `∫ |e^{-H₁} - e^{-H₂}| / δ` from above.  Nothing is assumed about the
relation between `A` and `Q`, and no dominated convergence is used: the only analytic inputs are
`e^u - 1 ≤ u e^u` and `u ≤ e^u`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Real

/-- `|e^{-v} - 1| ≤ |v| e^{|v|}`.  Both halves come from `1 - u ≤ e^{-u}`: for `v ≥ 0` it gives
`1 - e^{-v} ≤ v ≤ v e^{v}`, and multiplying it by `e^{v}` gives `e^{v} - 1 ≤ v e^{v}`. -/
theorem abs_exp_neg_sub_one_le (v : ℝ) : |Real.exp (-v) - 1| ≤ |v| * Real.exp |v| := by
  have habs : 0 ≤ |v| := abs_nonneg v
  have hexp1 : (1 : ℝ) ≤ Real.exp |v| := Real.one_le_exp habs
  -- `1 - u ≤ e^{-u}` for `u = |v|`
  have hlow : 1 - |v| ≤ Real.exp (-|v|) := by
    have := Real.add_one_le_exp (-|v|)
    linarith
  -- `e^{u} - 1 ≤ u e^{u}`, obtained from `hlow` by multiplying with `e^{u} > 0`
  have hhigh : Real.exp |v| - 1 ≤ |v| * Real.exp |v| := by
    have hpos : (0 : ℝ) < Real.exp |v| := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hlow hpos.le
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
    linarith
  have hle : Real.exp (-v) ≤ Real.exp |v| := Real.exp_le_exp.2 (neg_le_abs v)
  have hge : Real.exp (-|v|) ≤ Real.exp (-v) := Real.exp_le_exp.2 (neg_le_neg (le_abs_self v))
  rw [abs_le]
  constructor
  · have : 1 - |v| ≤ Real.exp (-v) := hlow.trans hge
    nlinarith
  · linarith [hle, hhigh]

end Real

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {m : Measure X} {H₁ H₂ Q : X → ℝ} {c δ : ℝ}

section Pointwise

/-- The pointwise comparison behind `MeasureTheory.abs_expTilt_sub_le`: if `H₂ ≤ c Q` and
`|H₁ - H₂| ≤ δ Q` with `0 ≤ δ ≤ 1` and `0 ≤ Q`, then
`|e^{-H₁} - e^{-H₂}| ≤ δ e^{(c+2)Q}`.  The three steps are `e^{-H₂} ≤ e^{cQ}`,
`|e^{-(H₁-H₂)} - 1| ≤ δQ e^{δQ}` and `Q e^{Q} ≤ e^{2Q}`. -/
theorem abs_exp_neg_sub_exp_neg_le {a b q : ℝ} (hq : 0 ≤ q) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hb : -b ≤ c * q) (hab : |a - b| ≤ δ * q) :
    |Real.exp (-a) - Real.exp (-b)| ≤ δ * Real.exp ((c + 2) * q) := by
  have hδq : 0 ≤ δ * q := mul_nonneg hδ0 hq
  -- `e^{-a} - e^{-b} = e^{-b} (e^{-(a-b)} - 1)`
  have hfac : Real.exp (-a) - Real.exp (-b)
      = Real.exp (-b) * (Real.exp (-(a - b)) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  have h1 : |Real.exp (-(a - b)) - 1| ≤ |a - b| * Real.exp |a - b| :=
    Real.abs_exp_neg_sub_one_le (a - b)
  have h2 : |a - b| * Real.exp |a - b| ≤ (δ * q) * Real.exp (δ * q) := by
    refine mul_le_mul hab (Real.exp_le_exp.2 hab) (Real.exp_pos _).le hδq
  have h3 : (δ * q) * Real.exp (δ * q) ≤ δ * (q * Real.exp q) := by
    have hq1 : Real.exp (δ * q) ≤ Real.exp q :=
      Real.exp_le_exp.2 (by nlinarith)
    calc (δ * q) * Real.exp (δ * q) ≤ (δ * q) * Real.exp q :=
          mul_le_mul_of_nonneg_left hq1 hδq
      _ = δ * (q * Real.exp q) := by ring
  have h4 : q * Real.exp q ≤ Real.exp (2 * q) := by
    have hle : q ≤ Real.exp q := (Real.add_one_le_exp q).trans' (by linarith)
    calc q * Real.exp q ≤ Real.exp q * Real.exp q :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ = Real.exp (2 * q) := by rw [← Real.exp_add]; ring_nf
  have hexpb : Real.exp (-b) ≤ Real.exp (c * q) := Real.exp_le_exp.2 hb
  calc |Real.exp (-a) - Real.exp (-b)|
      = Real.exp (-b) * |Real.exp (-(a - b)) - 1| := by
        rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (c * q) * (δ * Real.exp (2 * q)) := by
        refine mul_le_mul hexpb ?_ (abs_nonneg _) (Real.exp_pos _).le
        calc |Real.exp (-(a - b)) - 1| ≤ (δ * q) * Real.exp (δ * q) := h1.trans h2
          _ ≤ δ * (q * Real.exp q) := h3
          _ ≤ δ * Real.exp (2 * q) := mul_le_mul_of_nonneg_left h4 hδ0
    _ = δ * Real.exp ((c + 2) * q) := by
        rw [show (c + 2) * q = c * q + 2 * q by ring, Real.exp_add]; ring

end Pointwise

section Comparison

variable [IsFiniteMeasure m]

/-- **Georgii, Proposition (4.19), elementary two-kernel form.**  Let `H₁`, `H₂` be two energies on
a finite measure space `(X, m)` and `Q ≥ 0` a control function with

`|H₂| ≤ c Q`  and  `|H₁ - H₂| ≤ δ Q`,  `0 ≤ δ ≤ 1`.

Write `β = ∫ e^{-cQ} dm` and `Γ = ∫ e^{(c+2)Q} dm`, and assume `Γ < ∞`, `β > 0` and `δ Γ ≤ β/2`.
Then the two normalised laws `K_i(A) = (∫_A e^{-H_i})/(∫ e^{-H_i})` satisfy

`|K₁(A) - K₂(A)| ≤ 4 Γ δ / β`

for **every** measurable `A`.

The proof is Georgii's: `∫|e^{-H₁} - e^{-H₂}| ≤ δ Γ` by the pointwise bound
`abs_exp_neg_sub_exp_neg_le`, the partition functions are at least `β` resp. `β/2`, and the
difference of two ratios is expanded as `(N₁-N₂)Z₂ + N₂(Z₂-Z₁)` over `Z₁Z₂`. -/
theorem abs_expTilt_sub_le (hH₁ : Measurable H₁) (hH₂ : Measurable H₂) (hQ : Measurable Q)
    (hc : 0 ≤ c) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hQ0 : ∀ x, 0 ≤ Q x)
    (hH₂le : ∀ x, |H₂ x| ≤ c * Q x) (hdiff : ∀ x, |H₁ x - H₂ x| ≤ δ * Q x)
    (hΓ : Integrable (fun x ↦ Real.exp ((c + 2) * Q x)) m)
    (hβ : 0 < ∫ x, Real.exp (-(c * Q x)) ∂m)
    (hsmall : δ * (∫ x, Real.exp ((c + 2) * Q x) ∂m) ≤ (∫ x, Real.exp (-(c * Q x)) ∂m) / 2)
    {A : Set X} (hA : MeasurableSet A) :
    |(∫ x in A, Real.exp (-(H₁ x)) ∂m) / (∫ x, Real.exp (-(H₁ x)) ∂m)
        - (∫ x in A, Real.exp (-(H₂ x)) ∂m) / (∫ x, Real.exp (-(H₂ x)) ∂m)|
      ≤ 4 * (∫ x, Real.exp ((c + 2) * Q x) ∂m) * δ
        / (∫ x, Real.exp (-(c * Q x)) ∂m) := by
  set g : X → ℝ := fun x ↦ Real.exp ((c + 2) * Q x) with hg
  set h : X → ℝ := fun x ↦ Real.exp (-(c * Q x)) with hh
  set f₁ : X → ℝ := fun x ↦ Real.exp (-(H₁ x)) with hf₁
  set f₂ : X → ℝ := fun x ↦ Real.exp (-(H₂ x)) with hf₂
  set Γ : ℝ := ∫ x, g x ∂m with hΓdef
  set β : ℝ := ∫ x, h x ∂m with hβdef
  have hgmeas : Measurable g := (hQ.const_mul _).exp
  have hhmeas : Measurable h := ((hQ.const_mul _).neg).exp
  have hf₁meas : Measurable f₁ := hH₁.neg.exp
  have hf₂meas : Measurable f₂ := hH₂.neg.exp
  -- pointwise comparisons
  have hf₂g : ∀ x, f₂ x ≤ g x := fun x ↦ by
    have h1 := (abs_le.1 (hH₂le x)).1
    have h2 := hQ0 x
    exact Real.exp_le_exp.2 (by nlinarith)
  have hf₁g : ∀ x, f₁ x ≤ g x := fun x ↦ by
    have h1 := (abs_le.1 (hH₂le x)).1
    have h2 := (abs_le.1 (hdiff x)).1
    have h3 := hQ0 x
    have h4 : δ * Q x ≤ Q x := by nlinarith
    exact Real.exp_le_exp.2 (by nlinarith)
  have hhf₂ : ∀ x, h x ≤ f₂ x := fun x ↦
    Real.exp_le_exp.2 (neg_le_neg ((le_abs_self _).trans (hH₂le x)))
  have hptw : ∀ x, |f₁ x - f₂ x| ≤ δ * g x := fun x ↦
    abs_exp_neg_sub_exp_neg_le (hQ0 x) hδ0 hδ1
      ((neg_le_abs _).trans (hH₂le x)) (hdiff x)
  -- integrability
  have hf₁int : Integrable f₁ m :=
    Integrable.mono' hΓ hf₁meas.aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hf₁g x)
  have hf₂int : Integrable f₂ m :=
    Integrable.mono' hΓ hf₂meas.aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hf₂g x)
  have hhint : Integrable h m :=
    Integrable.mono' (integrable_const (1 : ℝ)) hhmeas.aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by nlinarith [hQ0 x]))
  set Z₁ : ℝ := ∫ x, f₁ x ∂m with hZ₁
  set Z₂ : ℝ := ∫ x, f₂ x ∂m with hZ₂
  set N₁ : ℝ := ∫ x in A, f₁ x ∂m with hN₁
  set N₂ : ℝ := ∫ x in A, f₂ x ∂m with hN₂
  -- the `L¹` distance of the two densities
  have hdiffint : Integrable (fun x ↦ f₁ x - f₂ x) m := hf₁int.sub hf₂int
  have hZdiff : |Z₁ - Z₂| ≤ δ * Γ := by
    rw [hZ₁, hZ₂, ← integral_sub hf₁int hf₂int]
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hΓdef, ← integral_const_mul]
    exact integral_mono hdiffint.abs (hΓ.const_mul δ) hptw
  have hNdiff : |N₁ - N₂| ≤ δ * Γ := by
    rw [hN₁, hN₂, ← integral_sub hf₁int.restrict hf₂int.restrict]
    refine (abs_integral_le_integral_abs).trans ?_
    refine le_trans (integral_mono hdiffint.abs.restrict ((hΓ.const_mul δ).restrict) hptw) ?_
    rw [hΓdef, ← integral_const_mul]
    exact setIntegral_le_integral (hΓ.const_mul δ)
      (.of_forall fun x ↦ mul_nonneg hδ0 (Real.exp_pos _).le)
  -- lower bounds on the two partition functions
  have hβZ₂ : β ≤ Z₂ := integral_mono hhint hf₂int hhf₂
  have hΓ0 : 0 ≤ Γ := integral_nonneg fun x ↦ (Real.exp_pos _).le
  have hδΓ : 0 ≤ δ * Γ := mul_nonneg hδ0 hΓ0
  have hZ₂pos : 0 < Z₂ := lt_of_lt_of_le hβ hβZ₂
  have hZ₁pos : β / 2 ≤ Z₁ := by
    have h1 : Z₂ - Z₁ ≤ δ * Γ := by
      have := (abs_le.1 hZdiff).1; linarith
    linarith
  have hZ₁pos' : 0 < Z₁ := lt_of_lt_of_le (by linarith) hZ₁pos
  -- `0 ≤ N₂ ≤ Z₂`
  have hN₂0 : 0 ≤ N₂ := setIntegral_nonneg hA fun x _ ↦ (Real.exp_pos _).le
  have hN₂Z₂ : N₂ ≤ Z₂ := setIntegral_le_integral hf₂int (.of_forall fun x ↦ (Real.exp_pos _).le)
  -- expand the difference of the two ratios
  have hexpand : N₁ / Z₁ - N₂ / Z₂ = ((N₁ - N₂) * Z₂ + N₂ * (Z₂ - Z₁)) / (Z₁ * Z₂) := by
    field_simp
    ring
  have hnum : |(N₁ - N₂) * Z₂ + N₂ * (Z₂ - Z₁)| ≤ 2 * (δ * Γ) * Z₂ := by
    have h1 : |(N₁ - N₂) * Z₂| ≤ (δ * Γ) * Z₂ := by
      rw [abs_mul, abs_of_pos hZ₂pos]
      exact mul_le_mul_of_nonneg_right hNdiff hZ₂pos.le
    have h2 : |N₂ * (Z₂ - Z₁)| ≤ Z₂ * (δ * Γ) := by
      rw [abs_mul, abs_of_nonneg hN₂0]
      exact mul_le_mul hN₂Z₂ (by rwa [abs_sub_comm]) (abs_nonneg _) hZ₂pos.le
    calc |(N₁ - N₂) * Z₂ + N₂ * (Z₂ - Z₁)| ≤ |(N₁ - N₂) * Z₂| + |N₂ * (Z₂ - Z₁)| :=
          abs_add_le _ _
      _ ≤ (δ * Γ) * Z₂ + Z₂ * (δ * Γ) := add_le_add h1 h2
      _ = 2 * (δ * Γ) * Z₂ := by ring
  rw [hexpand, abs_div, abs_of_pos (mul_pos hZ₁pos' hZ₂pos), div_le_div_iff₀
    (mul_pos hZ₁pos' hZ₂pos) hβ]
  -- `|num| (Z₁ Z₂)⁻¹ ≤ 2 δ Γ / Z₁ ≤ 4 Γ δ / β`
  have hkey : |(N₁ - N₂) * Z₂ + N₂ * (Z₂ - Z₁)| * β ≤ 4 * Γ * δ * (Z₁ * Z₂) := by
    have hstep : 2 * (δ * Γ) * Z₂ * β ≤ 4 * Γ * δ * (Z₁ * Z₂) := by
      have h1 : 2 * (δ * Γ) * β ≤ 4 * Γ * δ * Z₁ := by nlinarith
      nlinarith [hZ₂pos.le]
    exact le_trans (mul_le_mul_of_nonneg_right hnum hβ.le) hstep
  exact hkey

end Comparison

end MeasureTheory

end

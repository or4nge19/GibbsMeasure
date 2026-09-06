/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential moments from an exponential tail bound

A nonnegative random variable whose tail is dominated by `B e^{-b t}` has a finite exponential
moment of every order `a < b`, with the explicit bound

`∫ e^{a f} dμ ≤ 1 + a B / (b - a)`.

The proof is the layer cake formula `∫ (∫_0^{f} g) dμ = ∫_{t > 0} μ{f ≥ t} g(t) dt`
(`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`) for `g(t) = a e^{a t}`.

A converse-flavoured companion: a *two-sided* exponential bound `∫ e^{t f} dμ ≤ e^{t² B}`, valid
for every real `t`, forces `f ∈ L²(μ)` and `∫ f² dμ ≤ 2B`.  (Mathlib's bundled form of the
hypothesis is `ProbabilityTheory.HasSubgaussianMGF`, which carries `MemLp` but no second-moment
bound.)

## Main results

* `MeasureTheory.lintegral_exp_le_of_measure_le`
* `MeasureTheory.integrable_sq_of_lintegral_exp_le`
* `MeasureTheory.integral_sq_le_two_mul_of_lintegral_exp_le`
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

/-! ### A sub-Gaussian bound gives a second-moment bound -/

section SubGaussian

/-- `e^y (1 - y) ≤ 1`, the multiplicative form of `1 + x ≤ e^x`. -/
private lemma exp_mul_one_sub_le_one (y : ℝ) : Real.exp y * (1 - y) ≤ 1 := by
  have h := Real.add_one_le_exp (-y)
  have hmul : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp y * (1 - y) = (-y + 1) * Real.exp y := by ring
    _ ≤ Real.exp (-y) * Real.exp y := mul_le_mul_of_nonneg_right h (Real.exp_pos y).le
    _ = 1 := hmul

/-- **`1 + x c ≤ e^{x B}` for every `x ≥ 0` forces `c ≤ B`.**  The elementary replacement for
"the derivative of `x ↦ e^{xB} - 1 - xc` at `0` is nonnegative". -/
private lemma le_of_forall_one_add_mul_le_exp {c B : ℝ}
    (h : ∀ x : ℝ, 0 ≤ x → 1 + x * c ≤ Real.exp (x * B)) : c ≤ B := by
  have key : ∀ x : ℝ, 0 < x → x * B < 1 → c - B ≤ x * (c * B) := by
    intro x hx hxB
    have h1 := h x hx.le
    have h2 := exp_mul_one_sub_le_one (x * B)
    have h3 : (1 + x * c) * (1 - x * B) ≤ Real.exp (x * B) * (1 - x * B) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h4 : (1 + x * c) * (1 - x * B) ≤ 1 := h3.trans h2
    have h5 : x * (c - B) ≤ x * (x * (c * B)) := by nlinarith [h4]
    exact le_of_mul_le_mul_left h5 hx
  have htend : Filter.Tendsto (fun x : ℝ ↦ x * (c * B))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h0 : Filter.Tendsto (fun x : ℝ ↦ x * (c * B)) (nhds 0) (nhds (0 * (c * B))) :=
      (continuous_id.mul continuous_const).tendsto 0
    simpa using h0.mono_left nhdsWithin_le_nhds
  have hxpos : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < x := self_mem_nhdsWithin
  have hopen : IsOpen {x : ℝ | x * B < 1} :=
    isOpen_lt (continuous_id.mul continuous_const) continuous_const
  have hxB : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x * B < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hopen.mem_nhds (by simp))
  have hle : c - B ≤ 0 := ge_of_tendsto htend ((hxpos.and hxB).mono fun x hx ↦ key x hx.1 hx.2)
  linarith

section Core

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
  {B : ℝ}

/-- The second-order expansion of the sub-Gaussian bound at the parameter `t`. -/
private lemma two_add_mul_lintegral_sq_le (hf : Measurable f)
    (h : ∀ t : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * B))) (t : ℝ) :
    2 + ENNReal.ofReal (t ^ 2) * (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ)
      ≤ 2 * ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by
  have hsqm : Measurable fun x ↦ ENNReal.ofReal (f x ^ 2) := (hf.pow_const 2).ennreal_ofReal
  have hexpm : ∀ s : ℝ, Measurable fun x ↦ ENNReal.ofReal (Real.exp (s * f x)) := fun s ↦
    (Real.continuous_exp.measurable.comp (hf.const_mul s)).ennreal_ofReal
  have hptwise : ∀ x, ENNReal.ofReal (2 + t ^ 2 * f x ^ 2)
      ≤ ENNReal.ofReal (Real.exp (t * f x)) + ENNReal.ofReal (Real.exp ((-t) * f x)) := by
    intro x
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := Real.two_add_sq_le_exp_add_exp_neg (t * f x)
    have hsq : (t * f x) ^ 2 = t ^ 2 * f x ^ 2 := by ring
    have hneg : -(t * f x) = (-t) * f x := by ring
    rw [hsq, hneg] at hb
    exact hb
  have hLHS : (∫⁻ x, ENNReal.ofReal (2 + t ^ 2 * f x ^ 2) ∂μ)
      = 2 + ENNReal.ofReal (t ^ 2) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ := by
    have hsplit : ∀ x, ENNReal.ofReal (2 + t ^ 2 * f x ^ 2)
        = 2 + ENNReal.ofReal (t ^ 2) * ENNReal.ofReal (f x ^ 2) := by
      intro x
      rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (sq_nonneg t)]
      norm_num
    rw [lintegral_congr hsplit, lintegral_add_left measurable_const,
      lintegral_const_mul _ hsqm, lintegral_const, measure_univ, mul_one]
  have hRHS : (∫⁻ x, (ENNReal.ofReal (Real.exp (t * f x))
        + ENNReal.ofReal (Real.exp ((-t) * f x))) ∂μ)
      ≤ 2 * ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by
    rw [lintegral_add_left (hexpm t)]
    have h2 : (∫⁻ x, ENNReal.ofReal (Real.exp ((-t) * f x)) ∂μ)
        ≤ ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by
      have := h (-t)
      rwa [show (-t) ^ 2 = t ^ 2 from by ring] at this
    calc (∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ)
          + ∫⁻ x, ENNReal.ofReal (Real.exp ((-t) * f x)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (t ^ 2 * B)) + ENNReal.ofReal (Real.exp (t ^ 2 * B)) :=
          add_le_add (h t) h2
      _ = 2 * ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by rw [two_mul]
  calc 2 + ENNReal.ofReal (t ^ 2) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
      = ∫⁻ x, ENNReal.ofReal (2 + t ^ 2 * f x ^ 2) ∂μ := hLHS.symm
    _ ≤ ∫⁻ x, (ENNReal.ofReal (Real.exp (t * f x))
          + ENNReal.ofReal (Real.exp ((-t) * f x))) ∂μ := lintegral_mono hptwise
    _ ≤ 2 * ENNReal.ofReal (Real.exp (t ^ 2 * B)) := hRHS

/-- **A sub-Gaussian bound makes the square integrable.**  If `μ` is a probability measure and
`μ(e^{t f}) ≤ e^{t² B}` for every `t ∈ ℝ`, then `f ∈ L²(μ)`. -/
theorem integrable_sq_of_lintegral_exp_le (hf : Measurable f)
    (h : ∀ t : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * B))) :
    Integrable (fun x ↦ f x ^ 2) μ := by
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦ sq_nonneg _)]
  rw [lt_top_iff_ne_top]
  intro htop
  have h1 := two_add_mul_lintegral_sq_le hf h 1
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at h1
  rw [htop] at h1
  simp only [add_top, top_le_iff] at h1
  exact (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) h1

/-- **A sub-Gaussian bound gives a second-moment bound.**  If `μ` is a probability measure and
`μ(e^{t f}) ≤ e^{t² B}` for every `t ∈ ℝ`, then `μ(f²) ≤ 2B` (so in particular `B ≥ 0`).

Mathlib's bundled form of the hypothesis is `ProbabilityTheory.HasSubgaussianMGF f (2 * B) μ`;
that class carries `MemLp` but no bound on the second moment. -/
theorem integral_sq_le_two_mul_of_lintegral_exp_le (hf : Measurable f)
    (h : ∀ t : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (t * f x)) ∂μ)
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * B))) :
    (∫ x, f x ^ 2 ∂μ) ≤ 2 * B := by
  have hInt := integrable_sq_of_lintegral_exp_le hf h
  set S := ∫ x, f x ^ 2 ∂μ with hS
  have hSnn : 0 ≤ S := integral_nonneg fun x ↦ sq_nonneg _
  have hIeq : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) = ENNReal.ofReal S := by
    rw [hS, integral_eq_lintegral_of_nonneg_ae (.of_forall fun x ↦ sq_nonneg _)
      (hf.pow_const 2).aestronglyMeasurable, ENNReal.ofReal_toReal]
    rw [← lt_top_iff_ne_top, ← hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦ sq_nonneg _)]
    exact hInt.hasFiniteIntegral
  have hreal : ∀ x : ℝ, 0 ≤ x → 1 + x * (S / 2) ≤ Real.exp (x * B) := by
    intro x hx
    have hx' := two_add_mul_lintegral_sq_le hf h (Real.sqrt x)
    rw [Real.sq_sqrt hx, hIeq, ← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_mul (by norm_num)] at hx'
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hx'
    linarith
  have := le_of_forall_one_add_mul_le_exp hreal
  linarith

end Core

end SubGaussian

end MeasureTheory

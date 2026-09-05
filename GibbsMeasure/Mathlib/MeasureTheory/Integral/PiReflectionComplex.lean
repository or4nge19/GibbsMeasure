/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Reflection positivity of product measures: complex functions and exponential densities

This file continues `GibbsMeasure.Mathlib.MeasureTheory.Integral.Pi`, where the real statement
`0 ≤ ∫ f · f∘r d(⨂ᵢ ν i)` is proved for a permutation `r` of a finite index set exchanging `P`
and `Pᶜ`.  Here `f` is allowed to be complex, the reflection being combined with complex
conjugation as in Georgii, *Gibbs Measures and Phase Transitions*, (17.26)(iii):

  `F⋆ ω = conj (F (ω ∘ r))`.

## Main results

* `MeasureTheory.re_integral_mul_conj_comp_nonneg`: `0 ≤ (∫ F · F⋆)ᵣₑ` for bounded measurable
  complex `F` depending only on the coordinates in `P`.  Splitting `F` into real and imaginary
  parts reduces this to two instances of the real statement.
* `MeasureTheory.re_integral_mul_conj_comp_pow_nonneg`: the same with an extra factor `H ^ ℓ`,
  where `H` is itself of the form `∫_W h_w · h_w⋆ dm`; the `ℓ`-fold Fubini turns `H ^ ℓ` into an
  integral over `W ^ ℓ` of `G · G⋆` with `G = ∏ⱼ h_{wⱼ}`.
* `MeasureTheory.re_integral_mul_conj_comp_exp_nonneg`: the analytic core, `0 ≤ (∫ F · F⋆ ·
  exp H)ᵣₑ`, obtained from the previous item by expanding the exponential and interchanging the
  sum with the integral.
* `MeasureTheory.integral_mul_comp_mul_exp_nonneg`: **Georgii, Lemma (17.26)**.  A real
  integrable density `ρ = exp(h + h⋆ + ∫_W h_w · h_w⋆ dm)` relative to the product measure, with
  `h` and the `h_w` complex functions of the coordinates in `P` dominated by one measurable
  function `φ` of those coordinates, satisfies `∫ f · f∘r · ρ ≥ 0` for every bounded measurable
  real `f` depending only on the coordinates in `P`.
  `integral_mul_comp_mul_exp_nonneg_of_bounded` is the case of a uniform bound, to which the
  general case is reduced by Georgii's truncation `f ↦ f · 1_{φ ≤ c}` (applied here to `h` and
  the `h_w` as well; the truncated density agrees with `ρ` wherever the truncated test function
  is nonzero).

-/

@[expose] public section

open MeasureTheory Set Finset
open scoped ComplexConjugate ENNReal

namespace MeasureTheory

variable {ι E : Type*} [Fintype ι] [MeasurableSpace E] {ν : ι → Measure E}
  [∀ i, IsFiniteMeasure (ν i)]

section Complex

variable {r : ι ≃ ι} {P : Set ι}

omit [Fintype ι] [∀ i, IsFiniteMeasure (ν i)] in
/-- Composition with a permutation of the coordinates is measurable. -/
theorem measurable_comp_equiv (r : ι ≃ ι) :
    Measurable fun ω : ι → E ↦ ω ∘ r :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply (r i)

/-- **Reflection positivity of a product measure, for complex functions.** If the permutation
`r` of the sites exchanges `P` and its complement and preserves the marginals, then
`(∫ F ω · conj (F (ω ∘ r)))ᵣₑ ≥ 0` for every bounded measurable `F : (ι → E) → ℂ` depending only
on the coordinates in `P`.  Writing `F = F₁ + i F₂`, the real part of the integrand is
`F₁ · F₁∘r + F₂ · F₂∘r`, and each summand integrates to a nonnegative number by
`integral_mul_comp_nonneg_of_disjoint`. -/
theorem re_integral_mul_conj_comp_nonneg (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P) {F : (ι → E) → ℂ} (hF : Measurable F)
    (hdep : DependsOn F P) {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) :
    0 ≤ (∫ ω, F ω * conj (F (ω ∘ r)) ∂(Measure.pi ν)).re := by
  have hFr : Measurable fun ω : ι → E ↦ F (ω ∘ r) := hF.comp (measurable_comp_equiv r)
  have hre : Measurable fun ω : ι → E ↦ (F ω).re := Complex.measurable_re.comp hF
  have him : Measurable fun ω : ι → E ↦ (F ω).im := Complex.measurable_im.comp hF
  have hCre : ∀ ω, |(F ω).re| ≤ C := fun ω ↦ (Complex.abs_re_le_norm _).trans (hC ω)
  have hCim : ∀ ω, |(F ω).im| ≤ C := fun ω ↦ (Complex.abs_im_le_norm _).trans (hC ω)
  have hdre : DependsOn (fun ω ↦ (F ω).re) P := fun _ _ h ↦ congrArg Complex.re (hdep h)
  have hdim : DependsOn (fun ω ↦ (F ω).im) P := fun _ _ h ↦ congrArg Complex.im (hdep h)
  -- the integrand is integrable, so the real part commutes with the integral
  have hint : Integrable (fun ω ↦ F ω * conj (F (ω ∘ r))) (Measure.pi ν) := by
    refine (integrable_const (C * C)).mono'
      (hF.mul (Complex.continuous_conj.measurable.comp hFr)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    have h₀ : (0 : ℝ) ≤ C := (norm_nonneg _).trans (hC ω)
    simpa [norm_mul, RCLike.norm_conj] using mul_le_mul (hC ω) (hC _) (norm_nonneg _) h₀
  have hRe := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hRe
  rw [← hRe]
  -- `Re (z * conj w) = z.re * w.re + z.im * w.im`
  have hpt : ∀ ω : ι → E, (F ω * conj (F (ω ∘ r))).re
      = (F ω).re * (F (ω ∘ r)).re + (F ω).im * (F (ω ∘ r)).im :=
    fun ω ↦ by simp [Complex.mul_re]
  simp only [hpt]
  have hmul : ∀ (G : (ι → E) → ℝ), Measurable G → (∀ ω, |G ω| ≤ C) →
      Integrable (fun ω ↦ G ω * G (ω ∘ r)) (Measure.pi ν) := by
    intro G hG hGC
    refine Integrable.of_abs_le (hG.mul (hG.comp (measurable_comp_equiv r))) (C := C * C) ?_
    intro ω
    simpa [abs_mul] using
      mul_le_mul (hGC ω) (hGC _) (abs_nonneg _) ((abs_nonneg _).trans (hGC ω))
  rw [integral_add (hmul _ hre hCre) (hmul _ him hCim)]
  exact add_nonneg
    (integral_mul_comp_nonneg_of_disjoint r hν hP hre hdre hCre)
    (integral_mul_comp_nonneg_of_disjoint r hν hP him hdim hCim)


/-- A complex integral with nonnegative real part on the integrand has nonnegative real part. -/
theorem re_integral_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) (h : ∀ a, 0 ≤ (f a).re) : 0 ≤ (∫ a, f a ∂μ).re := by
  have := Complex.reCLM.integral_comp_comm hf
  simp only [Complex.reCLM_apply] at this
  rw [← this]
  exact integral_nonneg h

variable {W : Type*} [MeasurableSpace W]

/-- **Reflection positivity of a product measure against a power of a positive kernel.** With `H`
the function `ω ↦ ∫_W h_w ω · conj (h_w (ω ∘ r)) dm`, the `ℓ`-th power `H ^ ℓ` is, by the `ℓ`-fold
Fubini theorem, the integral over `W ^ ℓ` of `G_v · G_v⋆` with `G_v = ∏ⱼ h_{vⱼ}`.  Multiplying by
`F · F⋆` and swapping the two integrals therefore reduces to
`re_integral_mul_conj_comp_nonneg`.  This is the step of Georgii's Lemma (17.26) that expands the
`ℓ`-th term of the exponential series. -/
theorem re_integral_mul_conj_comp_pow_nonneg (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P) {F : (ι → E) → ℂ} (hF : Measurable F) (hdep : DependsOn F P)
    {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) {m : Measure W} [IsFiniteMeasure m]
    {h : W → (ι → E) → ℂ} (hh : Measurable (Function.uncurry h))
    (hhdep : ∀ w, DependsOn (h w) P) {Ch : ℝ} (hhC : ∀ w ω, ‖h w ω‖ ≤ Ch) (ℓ : ℕ) :
    0 ≤ (∫ ω, F ω * conj (F (ω ∘ r)) * (∫ w, h w ω * conj (h w (ω ∘ r)) ∂m) ^ ℓ
      ∂(Measure.pi ν)).re := by
  classical
  -- `h` is measurable in the two arguments jointly, hence along any measurable pair of maps
  have hpair : ∀ {a : (ι → E) × (Fin ℓ → W) → W} {b : (ι → E) × (Fin ℓ → W) → ι → E},
      Measurable a → Measurable b → Measurable fun x ↦ h (a x) (b x) :=
    fun ha hb ↦ hh.comp (ha.prodMk hb)
  have hhw : ∀ w, Measurable (h w) := fun _ ↦ hh.of_uncurry_left
  -- `G v ω = F ω * ∏ⱼ h (v j) ω`
  set G : (Fin ℓ → W) → (ι → E) → ℂ := fun v ω ↦ F ω * ∏ j, h (v j) ω with hG
  have hGm : ∀ v, Measurable (G v) := fun v ↦
    hF.mul (Finset.measurable_prod _ fun j _ ↦ hhw (v j))
  have hGdep : ∀ v, DependsOn (G v) P := fun v x y hxy ↦ by
    simp only [hG, hdep hxy]
    exact congrArg _ (Finset.prod_congr rfl fun j _ ↦ hhdep (v j) hxy)
  have hGC : ∀ v ω, ‖G v ω‖ ≤ C * Ch ^ ℓ := by
    intro v ω
    have hC0 : (0 : ℝ) ≤ C := (norm_nonneg _).trans (hC ω)
    rw [hG, norm_mul]
    refine mul_le_mul (hC ω) ?_ (norm_nonneg _) hC0
    calc ‖∏ j, h (v j) ω‖ = ∏ j, ‖h (v j) ω‖ := norm_prod _ _
      _ ≤ ∏ _j : Fin ℓ, Ch := Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
          fun j _ ↦ hhC (v j) ω
      _ = Ch ^ ℓ := by simp
  -- Step 1: `H ^ ℓ` as an integral over `W ^ ℓ`
  have hpow : ∀ ω : ι → E, F ω * conj (F (ω ∘ r)) * (∫ w, h w ω * conj (h w (ω ∘ r)) ∂m) ^ ℓ
      = ∫ v : Fin ℓ → W, G v ω * conj (G v (ω ∘ r)) ∂(Measure.pi fun _ : Fin ℓ ↦ m) := by
    intro ω
    have hfub := integral_fintype_prod_eq_pow (ι := Fin ℓ)
      (fun w ↦ h w ω * conj (h w (ω ∘ r))) (μ := m)
    rw [Fintype.card_fin] at hfub
    rw [← hfub, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only [hG, map_mul, map_prod, Finset.prod_mul_distrib]
    ring
  simp only [hpow]
  -- Step 2: swap the two integrals
  have hjoint : Integrable
      (Function.uncurry fun (ω : ι → E) (v : Fin ℓ → W) ↦ G v ω * conj (G v (ω ∘ r)))
      ((Measure.pi ν).prod (Measure.pi fun _ : Fin ℓ ↦ m)) := by
    have hmeas : Measurable
        (Function.uncurry fun (ω : ι → E) (v : Fin ℓ → W) ↦ G v ω * conj (G v (ω ∘ r))) := by
      have h₁ : Measurable fun p : (ι → E) × (Fin ℓ → W) ↦ G p.2 p.1 :=
        (hF.comp measurable_fst).mul (Finset.measurable_prod _ fun j _ ↦
          hpair ((measurable_pi_apply j).comp measurable_snd) measurable_fst)
      have h₂ : Measurable fun p : (ι → E) × (Fin ℓ → W) ↦ G p.2 (p.1 ∘ r) :=
        (hF.comp ((measurable_comp_equiv r).comp measurable_fst)).mul
          (Finset.measurable_prod _ fun j _ ↦
            hpair ((measurable_pi_apply j).comp measurable_snd)
              ((measurable_comp_equiv r).comp measurable_fst))
      exact h₁.mul (Complex.continuous_conj.measurable.comp h₂)
    refine (integrable_const ((C * Ch ^ ℓ) * (C * Ch ^ ℓ))).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ ?_)
    have h₀ : (0 : ℝ) ≤ C * Ch ^ ℓ := (norm_nonneg _).trans (hGC p.2 p.1)
    simpa [Function.uncurry, norm_mul, RCLike.norm_conj] using
      mul_le_mul (hGC p.2 p.1) (hGC p.2 _) (norm_nonneg _) h₀
  rw [integral_integral_swap hjoint]
  -- Step 3: each inner integral has nonnegative real part
  refine re_integral_nonneg (MeasureTheory.Integrable.integral_prod_right hjoint) fun v ↦
    re_integral_mul_conj_comp_nonneg r hν hP (hGm v) (hGdep v) (hGC v)


/-- **Georgii, Lemma (17.26), analytic core.** Let `H ω = ∫_W h_w ω · conj (h_w (ω ∘ r)) dm` with
`h` jointly measurable, uniformly bounded, and depending only on the coordinates in `P`.  Then
`(∫ F · F⋆ · exp H)ᵣₑ ≥ 0` for every bounded measurable `F` depending only on the coordinates in
`P`.  Expanding the exponential turns the integral into the sum `∑_ℓ (1/ℓ!) ∫ F · F⋆ · H^ℓ` of
the nonnegative terms of `re_integral_mul_conj_comp_pow_nonneg`. -/
theorem re_integral_mul_conj_comp_exp_nonneg (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P) {F : (ι → E) → ℂ} (hF : Measurable F) (hdep : DependsOn F P)
    {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) {m : Measure W} [IsFiniteMeasure m]
    {h : W → (ι → E) → ℂ} (hh : Measurable (Function.uncurry h))
    (hhdep : ∀ w, DependsOn (h w) P) {Ch : ℝ} (hhC : ∀ w ω, ‖h w ω‖ ≤ Ch) :
    0 ≤ (∫ ω, F ω * conj (F (ω ∘ r)) *
      Complex.exp (∫ w, h w ω * conj (h w (ω ∘ r)) ∂m) ∂(Measure.pi ν)).re := by
  classical
  set H : (ι → E) → ℂ := fun ω ↦ ∫ w, h w ω * conj (h w (ω ∘ r)) ∂m with hHdef
  -- `H` is measurable, being a parametric integral of a jointly measurable function
  have hgm : Measurable fun p : (ι → E) × W ↦ h p.2 p.1 * conj (h p.2 (p.1 ∘ r)) :=
    (hh.comp (measurable_snd.prodMk measurable_fst)).mul
      (Complex.continuous_conj.measurable.comp
        (hh.comp (measurable_snd.prodMk ((measurable_comp_equiv r).comp measurable_fst))))
  have hHm : Measurable H := (hgm.stronglyMeasurable.integral_prod_right').measurable
  -- `H` is bounded
  set K : ℝ := Ch * Ch * (m Set.univ).toReal with hKdef
  have hHC : ∀ ω, ‖H ω‖ ≤ K := fun ω ↦
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun w ↦ by
      simpa [norm_mul, RCLike.norm_conj] using
        mul_le_mul (hhC w ω) (hhC w _) (norm_nonneg _) ((norm_nonneg _).trans (hhC w ω)))
  have hK0 : (0 : ℝ) ≤ K := mul_nonneg (mul_self_nonneg Ch) ENNReal.toReal_nonneg
  -- the terms of the exponential series
  set T : ℕ → (ι → E) → ℂ :=
    fun ℓ ω ↦ (((Nat.factorial ℓ : ℝ)⁻¹ : ℝ) : ℂ) * (F ω * conj (F (ω ∘ r)) * H ω ^ ℓ)
    with hTdef
  set B : ℕ → ℝ := fun ℓ ↦ (Nat.factorial ℓ : ℝ)⁻¹ * (C * C * K ^ ℓ) with hBdef
  have hGℓm : ∀ ℓ, Measurable fun ω : ι → E ↦ F ω * conj (F (ω ∘ r)) * H ω ^ ℓ := fun ℓ ↦
    (hF.mul (Complex.continuous_conj.measurable.comp
      (hF.comp (measurable_comp_equiv r)))).mul (hHm.pow_const ℓ)
  have hTm : ∀ ℓ, Measurable (T ℓ) := fun ℓ ↦ (hGℓm ℓ).const_mul _
  have hTC : ∀ ℓ ω, ‖T ℓ ω‖ ≤ B ℓ := by
    intro ℓ ω
    have hC0 : (0 : ℝ) ≤ C := (norm_nonneg _).trans (hC ω)
    have h₁ : ‖F ω * conj (F (ω ∘ r))‖ ≤ C * C := by
      simpa [norm_mul, RCLike.norm_conj] using mul_le_mul (hC ω) (hC _) (norm_nonneg _) hC0
    have h₂ : ‖H ω ^ ℓ‖ ≤ K ^ ℓ := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hHC ω) ℓ
    rw [hTdef, hBdef, norm_mul, Complex.norm_real, norm_inv, Real.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖F ω * conj (F (ω ∘ r)) * H ω ^ ℓ‖
        ≤ (C * C) * K ^ ℓ := by
          rw [norm_mul]
          exact mul_le_mul h₁ h₂ (norm_nonneg _) (mul_nonneg hC0 hC0)
      _ = C * C * K ^ ℓ := rfl
  have hTint : ∀ ℓ, Integrable (T ℓ) (Measure.pi ν) := fun ℓ ↦
    (integrable_const (B ℓ)).mono' (hTm ℓ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ by simpa using hTC ℓ ω)
  -- the norms of the terms are summable
  have hTsum : Summable fun ℓ ↦ ∫ ω, ‖T ℓ ω‖ ∂(Measure.pi ν) := by
    refine Summable.of_nonneg_of_le (fun ℓ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun ℓ ↦ ?_) (((Real.summable_pow_div_factorial K).mul_left
        (C * C * (Measure.pi ν Set.univ).toReal)))
    calc ∫ ω, ‖T ℓ ω‖ ∂(Measure.pi ν)
        ≤ ∫ _ω, B ℓ ∂(Measure.pi ν) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall (hTC ℓ))
      _ = (Measure.pi ν Set.univ).toReal • B ℓ := integral_const _
      _ = C * C * (Measure.pi ν Set.univ).toReal * (K ^ ℓ / Nat.factorial ℓ) := by
          simp only [hBdef, smul_eq_mul]; field_simp
  have hHasSum := hasSum_integral_of_summable_integral_norm hTint hTsum
  -- the pointwise sum of the series is the integrand
  have hpt : ∀ ω, ∑' ℓ, T ℓ ω = F ω * conj (F (ω ∘ r)) * Complex.exp (H ω) := by
    intro ω
    calc ∑' ℓ, T ℓ ω = ∑' ℓ, F ω * conj (F (ω ∘ r)) * (H ω ^ ℓ / (Nat.factorial ℓ : ℂ)) := by
          refine tsum_congr fun ℓ ↦ ?_
          simp only [hTdef, Complex.ofReal_inv, Complex.ofReal_natCast]
          rw [div_eq_mul_inv]
          ring
      _ = F ω * conj (F (ω ∘ r)) * ∑' ℓ, H ω ^ ℓ / (Nat.factorial ℓ : ℂ) := tsum_mul_left
      _ = F ω * conj (F (ω ∘ r)) * Complex.exp (H ω) := by
          rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  simp only [hpt] at hHasSum
  -- each term has nonnegative real part
  refine hasSum_le (fun ℓ ↦ ?_) hasSum_zero (Complex.reCLM.hasSum hHasSum)
  have hint : ∫ ω, T ℓ ω ∂(Measure.pi ν)
      = (((Nat.factorial ℓ : ℝ)⁻¹ : ℝ) : ℂ)
        * ∫ ω, F ω * conj (F (ω ∘ r)) * H ω ^ ℓ ∂(Measure.pi ν) := by
    rw [hTdef, integral_const_mul]
  simp only [Complex.reCLM_apply, hint, Complex.re_ofReal_mul]
  exact mul_nonneg (by positivity)
    (re_integral_mul_conj_comp_pow_nonneg r hν hP hF hdep hC hh hhdep hhC ℓ)


/-- **Georgii, Lemma (17.26), for uniformly bounded `h` and `h_w`.**  Let `ρ` be a real density
relative to the product measure of the form `ρ = exp(h + h⋆ + ∫_W h_w · h_w⋆ dm)`, where `h` and
the `h_w` are bounded measurable complex functions of the coordinates in `P` and `⋆` is the
reflection `r` combined with complex conjugation.  Then `∫ f · f∘r · ρ ≥ 0` for every bounded
measurable real `f` depending only on the coordinates in `P`; that is, the measure with density
`ρ` is reflection positive.  Absorbing `exp h` into the test function turns this into
`re_integral_mul_conj_comp_exp_nonneg`. -/
theorem integral_mul_comp_mul_exp_nonneg_of_bounded (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P) {h : (ι → E) → ℂ} (hhm : Measurable h) (hhdep : DependsOn h P)
    {m : Measure W} [IsFiniteMeasure m] {hw : W → (ι → E) → ℂ}
    (hwm : Measurable (Function.uncurry hw)) (hwdep : ∀ w, DependsOn (hw w) P)
    {Ch : ℝ} (hhC : ∀ ω, ‖h ω‖ ≤ Ch) (hwC : ∀ w ω, ‖hw w ω‖ ≤ Ch)
    {ρ : (ι → E) → ℝ} (hρ : ∀ ω, (ρ ω : ℂ) = Complex.exp (h ω + conj (h (ω ∘ r))
      + ∫ w, hw w ω * conj (hw w (ω ∘ r)) ∂m))
    {f : (ι → E) → ℝ} (hf : Measurable f) (hfdep : DependsOn f P) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    0 ≤ ∫ ω, f ω * f (ω ∘ r) * ρ ω ∂(Measure.pi ν) := by
  classical
  set F : (ι → E) → ℂ := fun ω ↦ ((f ω : ℝ) : ℂ) * Complex.exp (h ω) with hFdef
  have hFm : Measurable F :=
    (Complex.measurable_ofReal.comp hf).mul (Complex.continuous_exp.measurable.comp hhm)
  have hFdep : DependsOn F P := fun x y hxy ↦ by
    simp only [hFdef, hfdep hxy, hhdep hxy]
  have hFC : ∀ ω, ‖F ω‖ ≤ C * Real.exp Ch := by
    intro ω
    have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hC ω)
    rw [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    exact mul_le_mul (hC ω) (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hhC ω)))
      (Real.exp_pos _).le hC0
  -- the real integrand is the real part of the complex one
  have hpt : ∀ ω : ι → E, ((f ω * f (ω ∘ r) * ρ ω : ℝ) : ℂ)
      = F ω * conj (F (ω ∘ r)) * Complex.exp (∫ w, hw w ω * conj (hw w (ω ∘ r)) ∂m) := by
    intro ω
    rw [hFdef]
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.ofReal_mul, hρ ω,
      Complex.exp_add]
    ring
  have hcast : ∫ ω, ((f ω * f (ω ∘ r) * ρ ω : ℝ) : ℂ) ∂(Measure.pi ν)
      = ((∫ ω, f ω * f (ω ∘ r) * ρ ω ∂(Measure.pi ν) : ℝ) : ℂ) := integral_complex_ofReal
  have hgoal : ∫ ω, f ω * f (ω ∘ r) * ρ ω ∂(Measure.pi ν)
      = (∫ ω, F ω * conj (F (ω ∘ r)) *
          Complex.exp (∫ w, hw w ω * conj (hw w (ω ∘ r)) ∂m) ∂(Measure.pi ν)).re := by
    simp only [← hpt, hcast, Complex.ofReal_re]
  rw [hgoal]
  exact re_integral_mul_conj_comp_exp_nonneg r hν hP hFm hFdep hFC hwm hwdep hwC

/-- **Georgii, Lemma (17.26).**  Let `ρ` be an integrable real density relative to the product
measure of the form `ρ = exp(h + h⋆ + ∫_W h_w · h_w⋆ dm)`, where `h` and the `h_w` are measurable
complex functions of the coordinates in `P` dominated by one measurable function `φ` of those
coordinates, and `⋆` is the reflection `r` combined with complex conjugation.  Then
`∫ f · f∘r · ρ ≥ 0` for every bounded measurable real `f` depending only on the coordinates in
`P`.  Georgii's truncation `f_c = f · 1_{φ ≤ c}` is carried out here on `h` and the `h_w`
simultaneously, which is what makes the bounded case
`integral_mul_comp_mul_exp_nonneg_of_bounded` applicable; the truncated density agrees with `ρ`
wherever the truncated test function is nonzero. -/
theorem integral_mul_comp_mul_exp_nonneg (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P) {φ : (ι → E) → ℝ} (hφm : Measurable φ) (hφdep : DependsOn φ P)
    {h : (ι → E) → ℂ} (hhm : Measurable h) (hhdep : DependsOn h P) (hhφ : ∀ ω, ‖h ω‖ ≤ φ ω)
    {m : Measure W} [IsFiniteMeasure m] {hw : W → (ι → E) → ℂ}
    (hwm : Measurable (Function.uncurry hw)) (hwdep : ∀ w, DependsOn (hw w) P)
    (hwφ : ∀ w ω, ‖hw w ω‖ ≤ φ ω)
    {ρ : (ι → E) → ℝ} (hρm : Measurable ρ) (hρint : Integrable ρ (Measure.pi ν))
    (hρ : ∀ ω, (ρ ω : ℂ) = Complex.exp (h ω + conj (h (ω ∘ r))
      + ∫ w, hw w ω * conj (hw w (ω ∘ r)) ∂m))
    {f : (ι → E) → ℝ} (hf : Measurable f) (hfdep : DependsOn f P) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    0 ≤ ∫ ω, f ω * f (ω ∘ r) * ρ ω ∂(Measure.pi ν) := by
  classical
  -- Georgii's truncation `1_{φ ≤ n}`, a bounded function of the coordinates in `P`
  set u : ℕ → (ι → E) → ℝ := fun n ω ↦ if φ ω ≤ n then 1 else 0 with hudef
  have hum : ∀ n, Measurable (u n) := fun n ↦
    Measurable.ite (measurableSet_le hφm measurable_const) measurable_const measurable_const
  have hudep : ∀ n, DependsOn (u n) P := fun n _ _ hxy ↦ by simp only [hudef, hφdep hxy]
  have huabs : ∀ n ω, |u n ω| ≤ 1 := fun n ω ↦ by
    simp only [hudef]; split <;> simp
  have hu1 : ∀ (n : ℕ) (ω : ι → E), φ ω ≤ (n : ℝ) → u n ω = 1 := fun n ω hc ↦ by
    simp [hudef, hc]
  have hu0 : ∀ (n : ℕ) (ω : ι → E), ¬ (φ ω ≤ (n : ℝ)) → u n ω = 0 := fun n ω hc ↦ by
    simp [hudef, hc]
  -- for each truncation level the truncated test function has a nonnegative integral
  have step : ∀ n : ℕ,
      0 ≤ ∫ ω, f ω * u n ω * (f (ω ∘ r) * u n (ω ∘ r)) * ρ ω ∂(Measure.pi ν) := by
    intro n
    set hwn : W → (ι → E) → ℂ := fun w ω ↦ ((u n ω : ℝ) : ℂ) * hw w ω with hwndef
    set F : (ι → E) → ℂ :=
      fun ω ↦ ((f ω * u n ω : ℝ) : ℂ) * Complex.exp (((u n ω : ℝ) : ℂ) * h ω) with hFdef
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    -- the truncated data is bounded by `n`
    have htrunc : ∀ (g : (ι → E) → ℂ), (∀ ω, ‖g ω‖ ≤ φ ω) →
        ∀ ω, ‖((u n ω : ℝ) : ℂ) * g ω‖ ≤ n := by
      intro g hg ω
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hc : φ ω ≤ (n : ℝ)
      · rw [hu1 n ω hc]; simpa using (hg ω).trans hc
      · rw [hu0 n ω hc]; simp [hn0]
    have hwnC : ∀ w ω, ‖hwn w ω‖ ≤ (n : ℝ) := fun w ↦ htrunc _ (hwφ w)
    have hhnC : ∀ ω, ‖((u n ω : ℝ) : ℂ) * h ω‖ ≤ (n : ℝ) := htrunc _ hhφ
    have hwnm : Measurable (Function.uncurry hwn) :=
      (Complex.measurable_ofReal.comp ((hum n).comp measurable_snd)).mul hwm
    have hwndep : ∀ w, DependsOn (hwn w) P := fun w _ _ hxy ↦ by
      simp only [hwndef, hudep n hxy, hwdep w hxy]
    have hFm : Measurable F :=
      (Complex.measurable_ofReal.comp (hf.mul (hum n))).mul
        (Complex.continuous_exp.measurable.comp
          ((Complex.measurable_ofReal.comp (hum n)).mul hhm))
    have hFdep : DependsOn F P := fun x y hxy ↦ by
      simp only [hFdef, hfdep hxy, hudep n hxy, hhdep hxy]
    have hFC : ∀ ω, ‖F ω‖ ≤ C * Real.exp n := by
      intro ω
      have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hC ω)
      rw [hFdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, abs_mul]
      refine mul_le_mul ?_ (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hhnC ω)))
        (Real.exp_pos _).le hC0
      simpa using mul_le_mul (hC ω) (huabs n ω) (abs_nonneg _) hC0
    -- the truncated integrand is the real part of the complex one
    have hpt : ∀ ω : ι → E, ((f ω * u n ω * (f (ω ∘ r) * u n (ω ∘ r)) * ρ ω : ℝ) : ℂ)
        = F ω * conj (F (ω ∘ r)) * Complex.exp (∫ w, hwn w ω * conj (hwn w (ω ∘ r)) ∂m) := by
      intro ω
      by_cases hc : φ ω ≤ (n : ℝ)
      · by_cases hc' : φ (ω ∘ r) ≤ (n : ℝ)
        · simp only [hFdef, hwndef, hu1 n ω hc, hu1 n _ hc', Complex.ofReal_one, one_mul,
            mul_one, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.ofReal_mul,
            hρ ω, Complex.exp_add]
          ring
        · simp [hFdef, hu0 n _ hc']
      · simp [hFdef, hu0 n ω hc]
    have hgoal : ∫ ω, f ω * u n ω * (f (ω ∘ r) * u n (ω ∘ r)) * ρ ω ∂(Measure.pi ν)
        = (∫ ω, F ω * conj (F (ω ∘ r)) *
            Complex.exp (∫ w, hwn w ω * conj (hwn w (ω ∘ r)) ∂m) ∂(Measure.pi ν)).re := by
      simp only [← hpt, integral_complex_ofReal, Complex.ofReal_re]
    rw [hgoal]
    exact re_integral_mul_conj_comp_exp_nonneg r hν hP hFm hFdep hFC hwnm hwndep hwnC
  -- pass to the limit `n → ∞`
  have hrm : Measurable fun ω : ι → E ↦ f (ω ∘ r) := hf.comp (measurable_comp_equiv r)
  have hlim : Filter.Tendsto
      (fun n ↦ ∫ ω, f ω * u n ω * (f (ω ∘ r) * u n (ω ∘ r)) * ρ ω ∂(Measure.pi ν))
      Filter.atTop (nhds (∫ ω, f ω * f (ω ∘ r) * ρ ω ∂(Measure.pi ν))) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ C * C * |ρ ω|)
      (fun n ↦ (((hf.mul (hum n)).mul (hrm.mul ((hum n).comp
        (measurable_comp_equiv r)))).mul hρm).aestronglyMeasurable)
      (hρint.abs.const_mul _) (fun n ↦ Filter.Eventually.of_forall fun ω ↦ ?_)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    · have hC0 : (0 : ℝ) ≤ C := (abs_nonneg _).trans (hC ω)
      have h₁ : |f ω * u n ω| ≤ C := by
        simpa using mul_le_mul (hC ω) (huabs n ω) (abs_nonneg _) hC0
      have h₂ : |f (ω ∘ r) * u n (ω ∘ r)| ≤ C := by
        simpa using mul_le_mul (hC _) (huabs n _) (abs_nonneg _) hC0
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul h₁ h₂ (abs_nonneg _) hC0) le_rfl (abs_nonneg _)
        (mul_nonneg hC0 hC0)
    · refine tendsto_atTop_of_eventually_const
        (i₀ := ⌈max (φ ω) (φ (ω ∘ r))⌉₊) fun i hi ↦ ?_
      have h₁ : φ ω ≤ i := (le_max_left _ _).trans ((Nat.le_ceil _).trans (Nat.cast_le.2 hi))
      have h₂ : φ (ω ∘ r) ≤ i := (le_max_right _ _).trans ((Nat.le_ceil _).trans (Nat.cast_le.2 hi))
      simp [hudef, h₁, h₂]
  exact ge_of_tendsto' hlim step


/-- **Georgii, Lemma (17.26), for a finite sum of squares.**  The density
`exp(h + h∘r + ∑_a g_a · g_a∘r)` relative to the product measure, with `h` and the `g_a`
measurable *real* functions of the coordinates in `P` dominated by one measurable function `φ` of
those coordinates and `a` ranging over a finite type, defines a reflection positive measure.
This is (17.26) with `m` the counting measure; it is the form in which reflection positivity is
checked for a lattice model whose interaction across the plane of `r` is a nonnegative quadratic
form in observables of the positive half.  The integrability hypothesis is the finiteness of the
partition function; when `φ` is constant it is automatic. -/
theorem integral_mul_comp_mul_exp_sum_nonneg {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (r : ι ≃ ι) (hν : ∀ i, ν (r i) = ν i)
    (hP : ∀ i, i ∈ P ↔ r i ∉ P)
    {φ : (ι → E) → ℝ} (hφm : Measurable φ) (hφdep : DependsOn φ P)
    {h : (ι → E) → ℝ} (hhm : Measurable h) (hhdep : DependsOn h P) (hhφ : ∀ ω, |h ω| ≤ φ ω)
    {g : A → (ι → E) → ℝ} (hgm : ∀ a, Measurable (g a)) (hgdep : ∀ a, DependsOn (g a) P)
    (hgφ : ∀ a ω, |g a ω| ≤ φ ω)
    (hρint : Integrable (fun ω ↦ Real.exp (h ω + h (ω ∘ r) + ∑ a, g a ω * g a (ω ∘ r)))
      (Measure.pi ν))
    {f : (ι → E) → ℝ} (hf : Measurable f) (hfdep : DependsOn f P) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    0 ≤ ∫ ω, f ω * f (ω ∘ r) *
      Real.exp (h ω + h (ω ∘ r) + ∑ a, g a ω * g a (ω ∘ r)) ∂(Measure.pi ν) := by
  classical
  have hrm : Measurable fun ω : ι → E ↦ ω ∘ r := measurable_comp_equiv r
  have hρm : Measurable fun ω : ι → E ↦
      Real.exp (h ω + h (ω ∘ r) + ∑ a, g a ω * g a (ω ∘ r)) :=
    Real.continuous_exp.measurable.comp ((hhm.add (hhm.comp hrm)).add
      (Finset.measurable_sum _ fun a _ ↦ (hgm a).mul ((hgm a).comp hrm)))
  refine integral_mul_comp_mul_exp_nonneg (W := A) (m := Measure.count)
    (h := fun ω ↦ ((h ω : ℝ) : ℂ)) (hw := fun a ω ↦ ((g a ω : ℝ) : ℂ))
    r hν hP hφm hφdep (Complex.measurable_ofReal.comp hhm)
    (fun _ _ hxy ↦ congrArg _ (hhdep hxy)) (fun ω ↦ by simpa using hhφ ω)
    (measurable_from_prod_countable_right fun a ↦ Complex.measurable_ofReal.comp (hgm a))
    (fun a _ _ hxy ↦ congrArg _ (hgdep a hxy)) (fun a ω ↦ by simpa using hgφ a ω)
    hρm hρint ?_ hf hfdep hC
  intro ω
  rw [Complex.ofReal_exp, integral_count]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
  push_cast
  ring_nf

end Complex

end MeasureTheory

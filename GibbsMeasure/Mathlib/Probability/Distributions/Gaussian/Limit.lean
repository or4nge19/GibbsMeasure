/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# `L¹`-limits of Gaussian random variables are Gaussian

If real random variables `X n` with Gaussian laws converge to `Y` in `L¹`, then `Y` has a
Gaussian law (`ProbabilityTheory.HasGaussianLaw.of_tendsto_eLpNorm_one`). The proof goes through
characteristic functions: `L¹`-convergence gives pointwise convergence of the characteristic
functions (`tendsto_charFun_map_of_tendsto_eLpNorm_one`), the means converge, and the variances
converge because the modulus `exp (-v n * s ^ 2 / 2)` of the Gaussian characteristic function
converges to the modulus of the (continuous, equal to `1` at `0`) limit characteristic function,
which is positive at some `s ≠ 0`.

The process version `ProbabilityTheory.IsGaussianProcess.of_tendsto_eLpNorm_one` says that a
pointwise-in-time `L¹`-limit of Gaussian processes is a Gaussian process.
-/

@[expose] public section

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- `L¹`-convergence of real random variables implies pointwise convergence of the
characteristic functions of their laws. -/
theorem tendsto_charFun_map_of_tendsto_eLpNorm_one [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    {Y : Ω → ℝ} (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (h : Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop (𝓝 (charFun (P.map Y) t)) := by
  have hbound : ∀ n, ‖charFun (P.map (X n)) t - charFun (P.map Y) t‖ₑ ≤
      ‖t‖ₑ * eLpNorm (X n - Y) 1 P := by
    intro n
    rw [charFun_apply_real, charFun_apply_real, integral_map (hX n) (by fun_prop),
      integral_map hY (by fun_prop), ← integral_sub]
    · refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [eLpNorm_one_eq_lintegral_enorm, ← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_mono fun ω ↦ ?_
      have hfac : exp (t * X n ω * I) - exp (t * Y ω * I) =
          exp (t * Y ω * I) * (exp (I * ((t * (X n ω - Y ω) : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      rw [hfac, enorm_mul,
        show (t : ℂ) * (Y ω : ℂ) * I = ((t * Y ω : ℝ) : ℂ) * I by push_cast; ring,
        enorm_exp_ofReal_mul_I, one_mul, ← enorm_mul, Pi.sub_apply]
      exact Real.enorm_exp_I_mul_ofReal_sub_one_le
    · refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
      · exact ((Complex.continuous_exp.comp
          (by fun_prop : Continuous fun x : ℝ ↦ (t * x * I : ℂ))).measurable.comp_aemeasurable
            (hX n)).aestronglyMeasurable
      · rw [show (t : ℂ) * (X n ω : ℂ) * I = ((t * X n ω : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
    · refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
      · exact ((Complex.continuous_exp.comp
          (by fun_prop : Continuous fun x : ℝ ↦ (t * x * I : ℂ))).measurable.comp_aemeasurable
            hY).aestronglyMeasurable
      · rw [show (t : ℂ) * (Y ω : ℂ) * I = ((t * Y ω : ℝ) : ℂ) * I by push_cast; ring,
          norm_exp_ofReal_mul_I]
  rw [tendsto_iff_enorm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n ↦ bot_le) hbound
  simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)

/-- **An `L¹`-limit of real Gaussian random variables is Gaussian.** If `X n` has a Gaussian law
for every `n` and `X n → Y` in `L¹(P)`, then `Y` has a Gaussian law. -/
theorem HasGaussianLaw.of_tendsto_eLpNorm_one {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, HasGaussianLaw (X n) P) (hY : AEMeasurable Y P)
    (h : Tendsto (fun n ↦ eLpNorm (X n - Y) 1 P) atTop (𝓝 0)) : HasGaussianLaw Y P := by
  have hP : IsProbabilityMeasure P := (hX 0).isProbabilityMeasure
  have hPY : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  set m : ℕ → ℝ := fun n ↦ P[X n] with hm_def
  set v : ℕ → ℝ := fun n ↦ Var[X n; P] with hv_def
  have hv0 : ∀ n, 0 ≤ v n := fun n ↦ variance_nonneg _ _
  have hφ : ∀ n t, charFun (P.map (X n)) t = exp (t * m n * I - v n * t ^ 2 / 2) := by
    intro n t
    rw [(hX n).map_eq_gaussianReal, charFun_gaussianReal]
    simp [m, v, Real.coe_toNNReal _ (hv0 n)]
  have hlim : ∀ t, Tendsto (fun n ↦ charFun (P.map (X n)) t) atTop (𝓝 (charFun (P.map Y) t)) :=
    tendsto_charFun_map_of_tendsto_eLpNorm_one (fun n ↦ (hX n).aemeasurable) hY h
  -- `Y` is integrable, and the means converge.
  have hYint : Integrable Y P := by
    obtain ⟨n, hn⟩ : ∃ n, eLpNorm (X n - Y) 1 P < ⊤ :=
      (h.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
    have hXY : Integrable (X n - Y) P :=
      memLp_one_iff_integrable.1 ⟨((hX n).aemeasurable.sub hY).aestronglyMeasurable, hn⟩
    simpa using (hX n).integrable.sub hXY
  have hm : Tendsto m atTop (𝓝 P[Y]) := by
    rw [tendsto_iff_enorm_sub_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n ↦ bot_le)
      fun n ↦ ?_
    rw [hm_def, ← integral_sub (hX n).integrable hYint, eLpNorm_one_eq_lintegral_enorm]
    exact enorm_integral_le_lintegral_enorm _
  -- The modulus of the limit characteristic function is positive at some `s ≠ 0`.
  have hnorm : ∀ n s, ‖charFun (P.map (X n)) s‖ = Real.exp (-(v n * s ^ 2 / 2)) := by
    intro n s
    rw [hφ, Complex.norm_exp]
    congr 1
    simp [pow_two]
  obtain ⟨s, hs, hg⟩ : ∃ s : ℝ, s ≠ 0 ∧ 0 < ‖charFun (P.map Y) s‖ := by
    have hc : Continuous fun s : ℝ ↦ ‖charFun (P.map Y) s‖ := continuous_charFun.norm
    have h0 : (1 / 2 : ℝ) < ‖charFun (P.map Y) 0‖ := by
      rw [charFun_zero, probReal_univ]
      norm_num
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (continuousAt_const.eventually_lt hc.continuousAt h0)
    refine ⟨ε / 2, by positivity, lt_trans (by norm_num) (hball ?_)⟩
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  -- The variances converge.
  set g : ℝ := ‖charFun (P.map Y) s‖ with hg_def
  have hexp : Tendsto (fun n ↦ Real.exp (-(v n * s ^ 2 / 2))) atTop (𝓝 g) := by
    simpa only [hnorm] using (hlim s).norm
  have hlog : Tendsto (fun n ↦ -(v n * s ^ 2 / 2)) atTop (𝓝 (Real.log g)) := by
    have := ((Real.continuousAt_log hg.ne').tendsto).comp hexp
    simpa only [Function.comp_def, Real.log_exp] using this
  set v₀ : ℝ := Real.log g * (-2 / s ^ 2) with hv₀_def
  have hv : Tendsto v atTop (𝓝 v₀) := by
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    have := hlog.mul_const (-2 / s ^ 2)
    refine this.congr fun n ↦ ?_
    field_simp
  have hv₀ : 0 ≤ v₀ := ge_of_tendsto' hv hv0
  -- Identify the limit characteristic function.
  set m₀ : ℝ := P[Y] with hm₀_def
  have hchar : ∀ t, charFun (P.map Y) t = exp (t * m₀ * I - v₀ * t ^ 2 / 2) := by
    intro t
    refine tendsto_nhds_unique (hlim t) ?_
    simp_rw [hφ]
    have hmC : Tendsto (fun n ↦ (m n : ℂ)) atTop (𝓝 (m₀ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hm
    have hvC : Tendsto (fun n ↦ (v n : ℂ)) atTop (𝓝 (v₀ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hv
    exact (Complex.continuous_exp.tendsto _).comp
      (((tendsto_const_nhds.mul hmC).mul tendsto_const_nhds).sub
        ((hvC.mul tendsto_const_nhds).div_const _))
  have hmap : P.map Y = gaussianReal m₀ v₀.toNNReal := by
    refine Measure.ext_of_charFun (funext fun t ↦ ?_)
    rw [hchar, charFun_gaussianReal, Real.coe_toNNReal _ hv₀]
  exact ⟨by rw [hmap]; infer_instance⟩

/-- Composing with a continuous linear map contracts the `L¹` seminorm by the operator norm. -/
theorem _root_.MeasureTheory.eLpNorm_one_clm_comp_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F] (M : E →L[ℝ] F) (g : Ω → E) :
    eLpNorm (fun ω ↦ M (g ω)) 1 P ≤ ‖M‖ₑ * eLpNorm g 1 P := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    ← lintegral_const_mul' _ _ enorm_ne_top]
  exact lintegral_mono fun ω ↦ M.le_opENorm (g ω)

/-- **A pointwise `L¹`-limit of Gaussian processes is a Gaussian process.** If `X n` is a Gaussian
process for every `n` and `X n t → Y t` in `L¹(P)` for every `t`, then `Y` is a Gaussian
process. -/
theorem IsGaussianProcess.of_tendsto_eLpNorm_one {T : Type*} {X : ℕ → T → Ω → ℝ} {Y : T → Ω → ℝ}
    (hX : ∀ n, IsGaussianProcess (X n) P) (hY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ t, Tendsto (fun n ↦ eLpNorm (X n t - Y t) 1 P) atTop (𝓝 0)) :
    IsGaussianProcess Y P := by
  classical
  have hP : IsProbabilityMeasure P := (hX 0).isProbabilityMeasure
  refine ⟨fun I ↦ ?_⟩
  have hYI : AEMeasurable (fun ω ↦ I.restrict (Y · ω)) P :=
    aemeasurable_pi_lambda _ fun i ↦ hY i
  refine ⟨isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hYI]
  have hXn : ∀ n, HasGaussianLaw (fun ω ↦ L (I.restrict (X n · ω))) P :=
    fun n ↦ ((hX n).hasGaussianLaw I).map_fun L
  have hdecomp : ∀ n, ((fun ω ↦ L (I.restrict (X n · ω))) - fun ω ↦ L (I.restrict (Y · ω))) =
      ∑ k : I, fun ω ↦ (L.comp (.single ℝ _ k)) (X n k ω - Y k ω) := by
    intro n
    funext ω
    simp only [Pi.sub_apply, Finset.sum_apply, map_sub]
    rw [Finset.sum_sub_distrib, L.sum_comp_single, L.sum_comp_single]
    rfl
  have hlim : Tendsto (fun n ↦ eLpNorm ((fun ω ↦ L (I.restrict (X n · ω))) -
      fun ω ↦ L (I.restrict (Y · ω))) 1 P) atTop (𝓝 0) := by
    have hbound : ∀ n, eLpNorm ((fun ω ↦ L (I.restrict (X n · ω))) -
        fun ω ↦ L (I.restrict (Y · ω))) 1 P ≤
        ∑ k : I, ‖L.comp (.single ℝ _ k)‖ₑ * eLpNorm (X n k - Y k) 1 P := by
      intro n
      rw [hdecomp n]
      refine (eLpNorm_sum_le (fun k _ ↦ ?_) le_rfl).trans (Finset.sum_le_sum fun k _ ↦ ?_)
      · exact ((L.comp (.single ℝ _ k)).continuous.measurable.comp_aemeasurable
          (((hX n).aemeasurable k).sub (hY k))).aestronglyMeasurable
      · exact MeasureTheory.eLpNorm_one_clm_comp_le _ _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n ↦ bot_le) hbound
    have := tendsto_finsetSum (Finset.univ : Finset I) fun k _ ↦
      ENNReal.Tendsto.const_mul (a := ‖L.comp (.single ℝ (fun _ : I ↦ ℝ) k)‖ₑ) (h k)
        (Or.inr enorm_ne_top)
    simpa using this
  exact (HasGaussianLaw.of_tendsto_eLpNorm_one hXn
    (L.continuous.measurable.comp_aemeasurable hYI) hlim).isGaussian_map

end ProbabilityTheory

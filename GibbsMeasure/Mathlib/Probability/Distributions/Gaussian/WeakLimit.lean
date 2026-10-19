/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Sequences

/-!
# Limits in distribution of Gaussian measures are Gaussian

A limit in distribution of Gaussian measures on `ℝ` is Gaussian, and the means and variances
converge to the mean and the variance of the limit. This is the "convergence in distribution"
counterpart of `GibbsMeasure/Mathlib/Probability/Distributions/Gaussian/Limit.lean`, which treats
`L¹` limits.

Convergence in distribution enters through the characteristic functions: the hypothesis used
throughout is the pointwise convergence `charFun (ρ n) t → charFun ν t`, which is implied by weak
convergence but also — and this is the form needed for Gibbs measures — by setwise convergence on
a σ-algebra making the relevant coordinates measurable.

## Main results

* `ProbabilityTheory.exists_eq_gaussianReal_of_tendsto_charFun`: if `ρ n` is a Gaussian measure on
  `ℝ` for every `n` and `charFun (ρ n) → charFun ν` pointwise for a probability measure `ν`, then
  the means `(ρ n)[id]` and the variances `Var[id; ρ n]` converge and `ν` is the Gaussian measure
  with the limiting mean and variance.
* `ProbabilityTheory.isGaussian_of_tendsto_charFun`, and the two limit statements
  `tendsto_integral_id_of_tendsto_charFun`, `tendsto_variance_id_of_tendsto_charFun`.
* `ProbabilityTheory.IsGaussianProcess.of_tendsto_integral_cexp`: a limit in distribution of
  Gaussian processes is a Gaussian process, the hypothesis being the convergence of the integrals
  of `ω ↦ exp (i s ∑_{i ∈ I} c i * X i ω)` for every finite `I`, every `c` and every `s`.
* `ProbabilityTheory.tendsto_integral_of_tendsto_integral_cexp` and
  `ProbabilityTheory.tendsto_covariance_of_tendsto_integral_cexp`: under the same hypothesis the
  means `(P n)[X i]` and the covariances `cov[X i, X j; P n]` converge to those of the limit.

## Implementation notes

The delicate point of the argument (Georgii's Proposition (13.A5)) is that the *means* converge:
the moduli of the characteristic functions give the convergence of the variances at once, but the
phases `exp (i t m_n)` only converge pointwise to a continuous limit, and one has to see that this
forces `m_n` to converge. `ProbabilityTheory.exists_tendsto_of_tendsto_cexp_mul_I` isolates this:
integrating `exp (i t m_n)` over a small interval `[0, δ]` on which the limit has real part `≥ 1/2`
gives `2 / |m_n| ≥ δ / 4` eventually (Riemann–Lebesgue in its most elementary form), hence a
bounded sequence; a convergent subsequence identifies the limit phase as `exp (i t m₀)`; and
`|sin θ| ≥ 2 |θ| / π` on `[-π/2, π/2]` turns the convergence of the phases at a single small `t`
into the convergence of `m_n` to `m₀`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-! ## Pointwise limits of characters of `ℝ` -/

/-- If the characters `t ↦ exp (i t m n)` of `ℝ` converge pointwise to a function `ψ` which is
continuous at `0` with `ψ 0 = 1`, then the sequence `m` is eventually bounded.

This is the elementary Riemann–Lebesgue argument: `∫_0^δ exp (i t m) dt` has modulus at most
`2 / |m|`, while the limit `∫_0^δ ψ` has real part at least `δ / 2` if `δ` is small enough. -/
theorem eventually_abs_le_of_tendsto_cexp_mul_I {m : ℕ → ℝ} {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ψ 0 = 1)
    (h : ∀ t : ℝ, Tendsto (fun n ↦ cexp ((t * m n : ℝ) * I)) atTop (𝓝 (ψ t))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, |m n| ≤ M := by
  -- a `δ > 0` on which `Re ψ ≥ 1/2`
  obtain ⟨δ, hδ, hre⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) δ, (1 : ℝ) / 2 ≤ (ψ t).re := by
    have hcre : ContinuousAt (fun t : ℝ ↦ (ψ t).re) 0 :=
      (Complex.continuous_re.comp hψc).continuousAt
    have h1 : (1 : ℝ) / 2 < (ψ 0).re := by rw [hψ0]; norm_num
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcre.eventually_const_lt h1)
    refine ⟨ε / 2, by positivity, fun t ht ↦ le_of_lt (hball ?_)⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact lt_of_le_of_lt ht.2 (by linarith)
  -- the limit of the integrals over `[0, δ]`
  set L : ℂ := ∫ t in (0 : ℝ)..δ, ψ t with hL
  have hLre : δ / 2 ≤ L.re := by
    have hintψ : IntegrableOn ψ (Ioc (0 : ℝ) δ) volume := hψc.integrableOn_Ioc
    have hintre : IntegrableOn (fun t : ℝ ↦ (ψ t).re) (Ioc (0 : ℝ) δ) volume :=
      (Complex.continuous_re.comp hψc).integrableOn_Ioc
    have hre' : (∫ t in Ioc (0 : ℝ) δ, (ψ t).re) = L.re := by
      rw [hL, intervalIntegral.integral_of_le hδ.le]
      simpa using ContinuousLinearMap.integral_comp_comm Complex.reCLM hintψ
    have hmono : (1 : ℝ) / 2 * (volume.real (Ioc (0 : ℝ) δ)) ≤
        ∫ t in Ioc (0 : ℝ) δ, (ψ t).re :=
      setIntegral_ge_of_const_le_real measurableSet_Ioc (by simp [Real.volume_Ioc])
        (fun t ht ↦ hre t ⟨ht.1.le, ht.2⟩) hintre
    have hvol : volume.real (Ioc (0 : ℝ) δ) = δ := by
      simp [Measure.real, Real.volume_Ioc, hδ.le]
    rw [hvol] at hmono
    rw [← hre']
    linarith
  have hLnorm : δ / 2 ≤ ‖L‖ := le_trans hLre (Complex.re_le_norm L)
  -- dominated convergence for the integrals
  have hA : Tendsto (fun n ↦ ∫ t in (0 : ℝ)..δ, cexp ((t * m n : ℝ) * I)) atTop (𝓝 L) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
      (.of_forall fun n ↦ (Continuous.aestronglyMeasurable (by fun_prop))) (.of_forall fun n ↦ ?_)
      intervalIntegrable_const (.of_forall fun t _ ↦ h t)
    filter_upwards with t _
    rw [Complex.norm_exp_ofReal_mul_I]
  -- the explicit value of the integral
  have hbound : ∀ n, m n ≠ 0 → ‖∫ t in (0 : ℝ)..δ, cexp ((t * m n : ℝ) * I)‖ ≤ 2 / |m n| := by
    intro n hn
    have hc : ((m n : ℂ) * I) ≠ 0 := by
      simpa [Complex.ext_iff] using mul_ne_zero (Complex.ofReal_ne_zero.2 hn) Complex.I_ne_zero
    have hrw : (fun t : ℝ ↦ cexp ((t * m n : ℝ) * I)) = fun t : ℝ ↦ cexp (((m n : ℂ) * I) * t) := by
      funext t; congr 1; push_cast; ring
    rw [hrw, integral_exp_mul_complex hc]
    have h1 : ‖cexp (((m n : ℂ) * I) * (0 : ℝ))‖ = 1 := by simp
    have h2 : ‖cexp (((m n : ℂ) * I) * (δ : ℝ))‖ = 1 := by
      rw [show ((m n : ℂ) * I) * (δ : ℝ) = ((δ * m n : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_div]
    have hnc : ‖(m n : ℂ) * I‖ = |m n| := by simp
    rw [hnc]
    gcongr
    calc ‖cexp (((m n : ℂ) * I) * (δ : ℝ)) - cexp (((m n : ℂ) * I) * (0 : ℝ))‖
        ≤ ‖cexp (((m n : ℂ) * I) * (δ : ℝ))‖ + ‖cexp (((m n : ℂ) * I) * (0 : ℝ))‖ :=
          norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  -- eventually `‖A n‖ ≥ δ / 4`, hence `|m n| ≤ 8 / δ`
  refine ⟨8 / δ, by positivity, ?_⟩
  have hev : ∀ᶠ n in atTop, δ / 4 < ‖∫ t in (0 : ℝ)..δ, cexp ((t * m n : ℝ) * I)‖ := by
    have hlt : δ / 4 < ‖L‖ := lt_of_lt_of_le (by linarith) hLnorm
    exact (hA.norm).eventually (eventually_gt_nhds hlt)
  filter_upwards [hev] with n hn
  rcases eq_or_ne (m n) 0 with h0 | h0
  · rw [h0, abs_zero]; positivity
  · have hlt := lt_of_lt_of_le hn (hbound n h0)
    have hpos : 0 < |m n| := abs_pos.2 h0
    have h2 : δ / 4 * |m n| < 2 :=
      calc δ / 4 * |m n| < 2 / |m n| * |m n| := by
            exact mul_lt_mul_of_pos_right hlt hpos
        _ = 2 := by field_simp
    rw [le_div_iff₀ hδ]
    nlinarith

/-- **Georgii, the key step of Proposition (13.A5)**: if the characters `t ↦ exp (i t m n)` of `ℝ`
converge pointwise to a continuous `ψ` with `ψ 0 = 1`, then `m n` converges to some `m₀` and
`ψ t = exp (i t m₀)`. -/
theorem exists_tendsto_of_tendsto_cexp_mul_I {m : ℕ → ℝ} {ψ : ℝ → ℂ} (hψc : Continuous ψ)
    (hψ0 : ψ 0 = 1)
    (h : ∀ t : ℝ, Tendsto (fun n ↦ cexp ((t * m n : ℝ) * I)) atTop (𝓝 (ψ t))) :
    ∃ m₀ : ℝ, Tendsto m atTop (𝓝 m₀) ∧ ∀ t : ℝ, ψ t = cexp ((t * m₀ : ℝ) * I) := by
  obtain ⟨M, hM0, hM⟩ := eventually_abs_le_of_tendsto_cexp_mul_I hψc hψ0 h
  -- a convergent subsequence
  obtain ⟨m₀, hm₀mem, φ, hφ, hφlim⟩ :
      ∃ a ∈ Icc (-M) M, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (m ∘ φ) atTop (𝓝 a) := by
    refine isCompact_Icc.tendsto_subseq' (Filter.Eventually.frequently ?_)
    filter_upwards [hM] with n hn
    exact Set.mem_Icc.2 ⟨by linarith [(abs_le.1 hn).1], (abs_le.1 hn).2⟩
  -- the limit phase
  have hψeq : ∀ t : ℝ, ψ t = cexp ((t * m₀ : ℝ) * I) := by
    intro t
    refine tendsto_nhds_unique ((h t).comp hφ.tendsto_atTop) ?_
    have : Continuous fun x : ℝ ↦ cexp ((t * x : ℝ) * I) := by fun_prop
    exact (this.tendsto m₀).comp hφlim
  refine ⟨m₀, ?_, hψeq⟩
  -- quantitative convergence at a single small `t₀`
  set t₀ : ℝ := Real.pi / (4 * (M + 1)) with ht₀
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have ht₀pos : 0 < t₀ := by
    rw [ht₀]; positivity
  have hkey : ∀ n, |m n| ≤ M →
      |m n - m₀| ≤ Real.pi / (2 * t₀) * ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖ := by
    intro n hn
    have hm₀ : |m₀| ≤ M := abs_le.2 ⟨hm₀mem.1, hm₀mem.2⟩
    set θ : ℝ := t₀ * (m n - m₀) with hθ
    have hθabs : |θ| ≤ Real.pi / 2 := by
      have h1 : |m n - m₀| ≤ 2 * M := by
        calc |m n - m₀| ≤ |m n| + |m₀| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      rw [hθ, abs_mul, abs_of_pos ht₀pos]
      calc t₀ * |m n - m₀| ≤ t₀ * (2 * M) := by nlinarith
        _ ≤ Real.pi / 2 := by
            rw [ht₀]
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [Real.pi_pos]
    -- `‖exp (i t₀ m n) - exp (i t₀ m₀)‖ = ‖exp (i θ) - 1‖ ≥ |sin θ| ≥ (2/π) |θ|`
    have hfac : cexp ((t₀ * m n : ℝ) * I) - ψ t₀
        = cexp ((t₀ * m₀ : ℝ) * I) * (cexp ((θ : ℝ) * I) - 1) := by
      rw [hψeq t₀, mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      rw [hθ]; push_cast; ring
    have hnormfac : ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖ = ‖cexp ((θ : ℝ) * I) - 1‖ := by
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hsin : |Real.sin θ| ≤ ‖cexp ((θ : ℝ) * I) - 1‖ := by
      have him : (cexp ((θ : ℝ) * I) - 1).im = Real.sin θ := by
        simp [Complex.exp_mul_I, ← Complex.ofReal_sin]
      calc |Real.sin θ| = |(cexp ((θ : ℝ) * I) - 1).im| := by rw [him]
        _ ≤ ‖cexp ((θ : ℝ) * I) - 1‖ := Complex.abs_im_le_norm _
    have hjordan : 2 / Real.pi * |θ| ≤ |Real.sin θ| := by
      rcases le_total 0 θ with hpos | hneg
      · calc 2 / Real.pi * |θ| = 2 / Real.pi * θ := by rw [abs_of_nonneg hpos]
          _ ≤ Real.sin θ := Real.mul_le_sin hpos (by rw [abs_of_nonneg hpos] at hθabs; exact hθabs)
          _ ≤ |Real.sin θ| := le_abs_self _
      · have hθ' : 0 ≤ -θ := by linarith
        have hθ'' : -θ ≤ Real.pi / 2 := by
          rw [abs_of_nonpos hneg] at hθabs; exact hθabs
        calc 2 / Real.pi * |θ| = 2 / Real.pi * (-θ) := by rw [abs_of_nonpos hneg]
          _ ≤ Real.sin (-θ) := Real.mul_le_sin hθ' hθ''
          _ ≤ |Real.sin (-θ)| := le_abs_self _
          _ = |Real.sin θ| := by rw [Real.sin_neg, abs_neg]
    have hchain : 2 / Real.pi * (t₀ * |m n - m₀|) ≤ ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖ := by
      rw [hnormfac]
      calc 2 / Real.pi * (t₀ * |m n - m₀|) = 2 / Real.pi * |θ| := by
            rw [hθ, abs_mul, abs_of_pos ht₀pos]
        _ ≤ |Real.sin θ| := hjordan
        _ ≤ _ := hsin
    have hcoef : (0 : ℝ) ≤ Real.pi / (2 * t₀) := by positivity
    calc |m n - m₀|
        = Real.pi / (2 * t₀) * (2 / Real.pi * (t₀ * |m n - m₀|)) := by
          have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
          field_simp
      _ ≤ Real.pi / (2 * t₀) * ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖ :=
          mul_le_mul_of_nonneg_left hchain hcoef
  have hto : Tendsto (fun n ↦ |m n - m₀|) atTop (𝓝 0) := by
    have hz : Tendsto (fun n ↦ Real.pi / (2 * t₀) * ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖) atTop
        (𝓝 0) := by
      have hsub : Tendsto (fun n ↦ cexp ((t₀ * m n : ℝ) * I) - ψ t₀) atTop (𝓝 (0 : ℂ)) := by
        simpa using (h t₀).sub (tendsto_const_nhds (x := ψ t₀) (f := (atTop : Filter ℕ)))
      have hnorm0 : Tendsto (fun n ↦ ‖cexp ((t₀ * m n : ℝ) * I) - ψ t₀‖) atTop (𝓝 (0 : ℝ)) := by
        simpa using hsub.norm
      simpa using hnorm0.const_mul (Real.pi / (2 * t₀))
    refine squeeze_zero' (.of_forall fun n ↦ abs_nonneg _) ?_ hz
    filter_upwards [hM] with n hn using hkey n hn
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.dist_eq] using hto

/-! ## Limits in distribution of real Gaussian measures -/

variable {ρ : ℕ → Measure ℝ} {ν : Measure ℝ}

/-- **Georgii, Proposition (13.A5)** in dimension one. If `ρ n` is a Gaussian measure on `ℝ` for
every `n` and the characteristic functions converge pointwise to that of a probability measure `ν`,
then the means and the variances converge, and `ν` is the Gaussian measure with the limiting mean
and variance. -/
theorem exists_eq_gaussianReal_of_tendsto_charFun (hρ : ∀ n, IsGaussian (ρ n))
    [IsProbabilityMeasure ν]
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (ρ n) t) atTop (𝓝 (charFun ν t))) :
    ∃ m v : ℝ, 0 ≤ v ∧ Tendsto (fun n ↦ (ρ n)[id]) atTop (𝓝 m) ∧
      Tendsto (fun n ↦ Var[id; ρ n]) atTop (𝓝 v) ∧ ν = gaussianReal m v.toNNReal := by
  set m : ℕ → ℝ := fun n ↦ (ρ n)[id] with hm_def
  set v : ℕ → ℝ := fun n ↦ Var[id; ρ n] with hv_def
  have hv0 : ∀ n, 0 ≤ v n := fun n ↦ variance_nonneg _ _
  have hφ : ∀ n t, charFun (ρ n) t = cexp (t * m n * I - v n * t ^ 2 / 2) := by
    intro n t
    rw [(hρ n).eq_gaussianReal, charFun_gaussianReal]
    simp [m, v, Real.coe_toNNReal _ (hv0 n)]
  have hnorm : ∀ n s, ‖charFun (ρ n) s‖ = Real.exp (-(v n * s ^ 2 / 2)) := by
    intro n s
    rw [hφ, Complex.norm_exp]
    congr 1
    simp [pow_two]
  -- the modulus of the limit is positive somewhere
  obtain ⟨s, hs, hg⟩ : ∃ s : ℝ, s ≠ 0 ∧ 0 < ‖charFun ν s‖ := by
    have hc : Continuous fun s : ℝ ↦ ‖charFun ν s‖ := continuous_charFun.norm
    have h0 : (1 / 2 : ℝ) < ‖charFun ν 0‖ := by
      rw [charFun_zero, probReal_univ]
      norm_num
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (continuousAt_const.eventually_lt hc.continuousAt h0)
    refine ⟨ε / 2, by positivity, lt_trans (by norm_num) (hball ?_)⟩
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  -- the variances converge
  set g : ℝ := ‖charFun ν s‖ with hg_def
  have hexp : Tendsto (fun n ↦ Real.exp (-(v n * s ^ 2 / 2))) atTop (𝓝 g) := by
    simpa only [hnorm] using (h s).norm
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
  -- the phases converge to a continuous limit
  set ψ : ℝ → ℂ := fun t ↦ charFun ν t * cexp ((v₀ * t ^ 2 / 2 : ℝ)) with hψ_def
  have hψc : Continuous ψ := by
    refine continuous_charFun.mul ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  have hψ0 : ψ 0 = 1 := by simp [hψ_def, charFun_zero, probReal_univ]
  have hphase : ∀ t : ℝ, Tendsto (fun n ↦ cexp ((t * m n : ℝ) * I)) atTop (𝓝 (ψ t)) := by
    intro t
    have hrw : ∀ n, cexp ((t * m n : ℝ) * I)
        = charFun (ρ n) t * cexp ((v n * t ^ 2 / 2 : ℝ)) := by
      intro n
      rw [hφ n t, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [hrw]
    refine (h t).mul ?_
    exact (Complex.continuous_exp.comp Complex.continuous_ofReal).continuousAt.tendsto.comp
      (by simpa using (hv.mul_const (t ^ 2)).div_const 2)
  obtain ⟨m₀, hmlim, hψeq⟩ := exists_tendsto_of_tendsto_cexp_mul_I hψc hψ0 hphase
  refine ⟨m₀, v₀, hv₀, hmlim, hv, ?_⟩
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [charFun_gaussianReal, Real.coe_toNNReal _ hv₀]
  have h1 : charFun ν t = ψ t * cexp ((-(v₀ * t ^ 2 / 2) : ℝ)) := by
    rw [hψ_def]
    simp only
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  rw [h1, hψeq t, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Georgii, Proposition (13.A5)** in dimension one: a limit in distribution of real Gaussian
measures is Gaussian. -/
theorem isGaussian_of_tendsto_charFun (hρ : ∀ n, IsGaussian (ρ n)) [IsProbabilityMeasure ν]
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (ρ n) t) atTop (𝓝 (charFun ν t))) : IsGaussian ν := by
  obtain ⟨m, v, hv, -, -, hν⟩ := exists_eq_gaussianReal_of_tendsto_charFun hρ h
  rw [hν]
  infer_instance

/-- **Georgii, Proposition (13.A5)**: the means converge. -/
theorem tendsto_integral_id_of_tendsto_charFun (hρ : ∀ n, IsGaussian (ρ n))
    [IsProbabilityMeasure ν]
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (ρ n) t) atTop (𝓝 (charFun ν t))) :
    Tendsto (fun n ↦ (ρ n)[id]) atTop (𝓝 (ν[id])) := by
  obtain ⟨m, v, hv, hm, -, hν⟩ := exists_eq_gaussianReal_of_tendsto_charFun hρ h
  have : (gaussianReal m v.toNNReal)[id] = m := by
    simp
  rwa [hν, this]

/-- **Georgii, Proposition (13.A5)**: the variances converge. -/
theorem tendsto_variance_id_of_tendsto_charFun (hρ : ∀ n, IsGaussian (ρ n))
    [IsProbabilityMeasure ν]
    (h : ∀ t : ℝ, Tendsto (fun n ↦ charFun (ρ n) t) atTop (𝓝 (charFun ν t))) :
    Tendsto (fun n ↦ Var[id; ρ n]) atTop (𝓝 (Var[id; ν])) := by
  obtain ⟨m, v, hv, -, hvlim, hν⟩ := exists_eq_gaussianReal_of_tendsto_charFun hρ h
  rwa [hν, variance_id_gaussianReal, Real.coe_toNNReal _ hv]


/-! ## Limits in distribution of Gaussian processes -/

section Process

variable {Ω T : Type*} {mΩ : MeasurableSpace Ω} {X : T → Ω → ℝ} {P : ℕ → Measure Ω}
  {Q : Measure Ω}

/-- Convergence in distribution of all finite-dimensional distributions of a process, expressed
through characteristic functions: for every finite `A ⊆ T` and every continuous linear form `L` on
`ℝ^A`, the laws of `ω ↦ L ((X i ω)_{i ∈ A})` converge in distribution.

This is exactly what the topology of local convergence gives for the coordinate process on a
configuration space, since `ω ↦ exp (i r L ((X i ω)_{i ∈ A}))` is bounded and measurable with
respect to the σ-algebra generated by the coordinates in `A`. -/
def TendstoFddCharFun (X : T → Ω → ℝ) (P : ℕ → Measure Ω) (Q : Measure Ω) : Prop :=
  ∀ (A : Finset T) (L : (∀ _ : A, ℝ) →L[ℝ] ℝ) (r : ℝ),
    Tendsto (fun n ↦ ∫ ω, cexp ((r * L (A.restrict (X · ω)) : ℝ) * I) ∂(P n)) atTop
      (𝓝 (∫ ω, cexp ((r * L (A.restrict (X · ω)) : ℝ) * I) ∂Q))

namespace TendstoFddCharFun

variable (hX : ∀ i, Measurable (X i)) (hP : ∀ n, IsGaussianProcess X (P n))

include hX

/-- Reading `TendstoFddCharFun` as convergence of the characteristic functions of the laws of
`ω ↦ L ((X i ω)_{i ∈ A})`. -/
theorem tendsto_charFun (h : TendstoFddCharFun X P Q) (A : Finset T)
    (L : (∀ _ : A, ℝ) →L[ℝ] ℝ) :
    ∀ r : ℝ, Tendsto (fun n ↦ charFun ((P n).map fun ω ↦ L (A.restrict (X · ω))) r) atTop
      (𝓝 (charFun (Q.map fun ω ↦ L (A.restrict (X · ω))) r)) := by
  intro r
  have hf : Measurable fun ω ↦ L (A.restrict (X · ω)) :=
    L.continuous.measurable.comp (Measurable.of_eval fun i ↦ hX i)
  have hrw : ∀ μ : Measure Ω, charFun (μ.map fun ω ↦ L (A.restrict (X · ω))) r
      = ∫ ω, cexp ((r * L (A.restrict (X · ω)) : ℝ) * I) ∂μ := by
    intro μ
    have hint : AEStronglyMeasurable (fun x : ℝ ↦ cexp ((r : ℂ) * (x : ℂ) * I))
        (μ.map fun ω ↦ L (A.restrict (X · ω))) := by fun_prop
    rw [charFun_apply_real, integral_map hf.aemeasurable hint]
    simp only [Complex.ofReal_mul]
  simp only [hrw]
  exact h A L r

include hP

/-- **Georgii, Proposition (13.A5)**: a limit in distribution of Gaussian processes is a Gaussian
process. -/
theorem isGaussianProcess [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) :
    IsGaussianProcess X Q := by
  refine ⟨fun A ↦ ?_⟩
  have hmeas : Measurable fun ω ↦ A.restrict (X · ω) := Measurable.of_eval fun i ↦ hX i
  refine ⟨hmeas.aemeasurable, isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  rw [Measure.map_map (by fun_prop) hmeas]
  have hf : Measurable fun ω ↦ L (A.restrict (X · ω)) := L.continuous.measurable.comp hmeas
  have hQprob : IsProbabilityMeasure (Q.map fun ω ↦ L (A.restrict (X · ω))) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hcomp : ((fun x ↦ L x) ∘ fun ω ↦ A.restrict (X · ω))
      = fun ω ↦ L (A.restrict (X · ω)) := rfl
  rw [hcomp]
  refine isGaussian_of_tendsto_charFun (fun n ↦ ?_) (h.tendsto_charFun hX A L)
  exact (((hP n).hasGaussianLaw A).map_fun L).isGaussian_map

/-- **Georgii, Proposition (13.A5)**: the mean of every finite-dimensional linear functional of
the process converges. -/
theorem tendsto_integral [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (A : Finset T)
    (L : (∀ _ : A, ℝ) →L[ℝ] ℝ) :
    Tendsto (fun n ↦ (P n)[fun ω ↦ L (A.restrict (X · ω))]) atTop
      (𝓝 (Q[fun ω ↦ L (A.restrict (X · ω))])) := by
  have hmeas : Measurable fun ω ↦ A.restrict (X · ω) := Measurable.of_eval fun i ↦ hX i
  have hf : Measurable fun ω ↦ L (A.restrict (X · ω)) := L.continuous.measurable.comp hmeas
  have hQprob : IsProbabilityMeasure (Q.map fun ω ↦ L (A.restrict (X · ω))) :=
    inferInstance
  have hgauss : ∀ n, IsGaussian ((P n).map fun ω ↦ L (A.restrict (X · ω))) := fun n ↦
    (((hP n).hasGaussianLaw A).map_fun L).isGaussian_map
  have hlim := tendsto_integral_id_of_tendsto_charFun hgauss (h.tendsto_charFun hX A L)
  have hmap : ∀ μ : Measure Ω, (μ.map fun ω ↦ L (A.restrict (X · ω)))[id]
      = μ[fun ω ↦ L (A.restrict (X · ω))] := fun μ ↦
    integral_map hf.aemeasurable aestronglyMeasurable_id
  simpa only [hmap] using hlim

/-- **Georgii, Proposition (13.A5)**: the variance of every finite-dimensional linear functional
of the process converges. -/
theorem tendsto_variance [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (A : Finset T)
    (L : (∀ _ : A, ℝ) →L[ℝ] ℝ) :
    Tendsto (fun n ↦ Var[fun ω ↦ L (A.restrict (X · ω)); P n]) atTop
      (𝓝 (Var[fun ω ↦ L (A.restrict (X · ω)); Q])) := by
  have hmeas : Measurable fun ω ↦ A.restrict (X · ω) := Measurable.of_eval fun i ↦ hX i
  have hf : Measurable fun ω ↦ L (A.restrict (X · ω)) := L.continuous.measurable.comp hmeas
  have hQprob : IsProbabilityMeasure (Q.map fun ω ↦ L (A.restrict (X · ω))) :=
    inferInstance
  have hgauss : ∀ n, IsGaussian ((P n).map fun ω ↦ L (A.restrict (X · ω))) := fun n ↦
    (((hP n).hasGaussianLaw A).map_fun L).isGaussian_map
  have hlim := tendsto_variance_id_of_tendsto_charFun hgauss (h.tendsto_charFun hX A L)
  simpa only [variance_id_map hf.aemeasurable] using hlim

/-- **Georgii, Proposition (13.A5)**: the means of the process converge. -/
theorem tendsto_integral_eval [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (i : T) :
    Tendsto (fun n ↦ (P n)[X i]) atTop (𝓝 (Q[X i])) := by
  classical
  have hi : i ∈ ({i} : Finset T) := Finset.mem_singleton_self i
  have := h.tendsto_integral hX hP {i}
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({i} : Finset T) ↦ ℝ) ⟨i, hi⟩)
  exact this

/-- **Georgii, Proposition (13.A5)**: the variances of the process converge. -/
theorem tendsto_variance_eval [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (i : T) :
    Tendsto (fun n ↦ Var[X i; P n]) atTop (𝓝 (Var[X i; Q])) := by
  classical
  have hi : i ∈ ({i} : Finset T) := Finset.mem_singleton_self i
  exact h.tendsto_variance hX hP {i}
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({i} : Finset T) ↦ ℝ) ⟨i, hi⟩)

/-- **Georgii, Proposition (13.A5)**: the variances of the sums `X i + X j` converge. -/
theorem tendsto_variance_add [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (i j : T) :
    Tendsto (fun n ↦ Var[fun ω ↦ X i ω + X j ω; P n]) atTop
      (𝓝 (Var[fun ω ↦ X i ω + X j ω; Q])) := by
  classical
  have hi : i ∈ ({i, j} : Finset T) := by simp
  have hj : j ∈ ({i, j} : Finset T) := by simp
  exact h.tendsto_variance hX hP {i, j}
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({i, j} : Finset T) ↦ ℝ) ⟨i, hi⟩ +
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ({i, j} : Finset T) ↦ ℝ) ⟨j, hj⟩)

/-- **Georgii, Proposition (13.A5)**: the covariances of the process converge. -/
theorem tendsto_covariance [IsProbabilityMeasure Q] (h : TendstoFddCharFun X P Q) (i j : T) :
    Tendsto (fun n ↦ cov[X i, X j; P n]) atTop (𝓝 (cov[X i, X j; Q])) := by
  have hQ : IsGaussianProcess X Q := h.isGaussianProcess hX hP
  have hPprob : ∀ n, IsProbabilityMeasure (P n) := fun n ↦ (hP n).isProbabilityMeasure
  have hmemP : ∀ (n : ℕ) (k : T), MemLp (X k) 2 (P n) := fun n k ↦
    ((hP n).hasGaussianLaw_eval k).memLp_two
  have hmemQ : ∀ k : T, MemLp (X k) 2 Q := fun k ↦ (hQ.hasGaussianLaw_eval k).memLp_two
  have hcov : ∀ (μ : Measure Ω) [IsFiniteMeasure μ], MemLp (X i) 2 μ → MemLp (X j) 2 μ →
      cov[X i, X j; μ] = (Var[fun ω ↦ X i ω + X j ω; μ] - Var[X i; μ] - Var[X j; μ]) / 2 := by
    intro μ _ hi hj
    have := variance_add (X := X i) (Y := X j) (μ := μ) hi hj
    have hadd : Var[X i + X j; μ] = Var[fun ω ↦ X i ω + X j ω; μ] := rfl
    rw [hadd] at this
    linarith
  simp only [hcov _ (hmemQ i) (hmemQ j), fun n ↦ hcov (P n) (hmemP n i) (hmemP n j)]
  exact (((h.tendsto_variance_add hX hP i j).sub (h.tendsto_variance_eval hX hP i)).sub
    (h.tendsto_variance_eval hX hP j)).div_const 2

end TendstoFddCharFun

end Process

end ProbabilityTheory

end

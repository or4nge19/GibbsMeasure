/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.PSeries

/-!
# Divergence of `∫ ‖y‖^{-k}` over a ball of `ℝ^n` when `k ≥ n`

Mathlib has the convergent half of the borderline: `integrableOn_ball_of_norm_le_rpow` says that
`‖y‖^{-α}` is integrable over a ball of an `n`-dimensional space when `α < n`. This file supplies
the divergent half in the form needed for lower bounds on Lebesgue integrals: for `k ≥ n` the
lower integral of `(c ‖y‖ ^ k)⁻¹` over any ball of `ℝ^n = ι → ℝ` is `∞`.

The proof is the dyadic one: on the annulus `A_m = B(0, R/2^m) ∖ B(0, R/2^{m+1})` the integrand is
at least `(c (R/2^m)^k)⁻¹` while the annulus has volume `(2^n - 1)(R/2^m)^n`, so each annulus
contributes at least `(2^n - 1) R^{n-k}/c > 0`, a quantity that does not depend on `m`; summing
over the countably many disjoint annuli gives `∞`.

The same dyadic decomposition gives the logarithmic refinement
`∫_{‖y‖ < R} (c ‖y‖^k log ‖y‖⁻¹)⁻¹ dy = ∞` for `k ≥ n`, which is what Georgii's Corollary (13.41)
needs: on the `m`-th annulus the logarithm is at most `(m+1) log(2/R)`, so the annuli now
contribute a constant multiple of the *harmonic* series instead of a constant.

## Main results

* `MeasureTheory.setLIntegral_inv_mul_norm_pow_ball_eq_top`
* `MeasureTheory.setLIntegral_inv_mul_norm_pow_mul_log_inv_ball_eq_top`
-/

@[expose] public section

open Function Metric Set

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **`∫ (c ‖y‖^k)⁻¹` over a ball of `ℝ^n` diverges when `k ≥ n`.** The dyadic annuli
`B(0, R/2^m) ∖ B(0, R/2^{m+1})` each contribute at least the constant `(2^n - 1) R^{n-k}/c`. -/
theorem setLIntegral_inv_mul_norm_pow_ball_eq_top {k : ℕ} (hk : Fintype.card ι ≤ k) {c R : ℝ}
    (hc : 0 < c) (hR : 0 < R) :
    ∫⁻ y in Metric.ball (0 : ι → ℝ) R, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ = ∞ := by
  classical
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := Fintype.card_pos
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn0
  -- the dyadic radii
  set t : ℕ → ℝ := fun m ↦ R / 2 ^ m with ht
  have htpos : ∀ m, 0 < t m := fun m ↦ by rw [ht]; positivity
  have htle : ∀ m, t m ≤ R := fun m ↦ div_le_self hR.le (one_le_pow₀ one_le_two)
  have htsucc : ∀ m, t (m + 1) = t m / 2 := by
    intro m
    rw [ht]
    simp only
    rw [pow_succ, div_div]
  have htanti : ∀ m m' : ℕ, m ≤ m' → t m' ≤ t m := by
    intro m m' hmm'
    rw [ht]
    exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ one_le_two hmm')
  -- the dyadic annuli
  set A : ℕ → Set (ι → ℝ) := fun m ↦ Metric.ball (0 : ι → ℝ) (t m) \ Metric.ball 0 (t (m + 1))
    with hA
  have hAmeas : ∀ m, MeasurableSet (A m) := fun m ↦ measurableSet_ball.diff measurableSet_ball
  have hAsub : ∀ m, A m ⊆ Metric.ball (0 : ι → ℝ) R := fun m y hy ↦
    Metric.ball_subset_ball (htle m) hy.1
  have hAdisj : Pairwise (Disjoint on A) := by
    have key : ∀ a b : ℕ, a < b → Disjoint (A a) (A b) := by
      intro a b hab
      rw [Set.disjoint_left]
      rintro y ⟨-, hy2⟩ hy3
      exact hy2 (Metric.ball_subset_ball (htanti (a + 1) b hab) hy3.1)
    intro m m' hmm'
    rcases lt_or_gt_of_ne hmm' with hlt | hgt
    · exact key m m' hlt
    · exact (key m' m hgt).symm
  -- the volume of an annulus
  have hvol : ∀ m, volume (A m) = ENNReal.ofReal ((2 ^ n - 1) * t m ^ n) := by
    intro m
    have hsubm : Metric.ball (0 : ι → ℝ) (t (m + 1)) ⊆ Metric.ball 0 (t m) :=
      Metric.ball_subset_ball (htanti m (m + 1) (Nat.le_succ m))
    have hfin : volume (Metric.ball (0 : ι → ℝ) (t (m + 1))) ≠ ∞ := by
      rw [Real.volume_pi_ball _ (htpos (m + 1))]
      exact ENNReal.ofReal_ne_top
    rw [hA, measure_sdiff hsubm measurableSet_ball.nullMeasurableSet hfin,
      Real.volume_pi_ball _ (htpos m), Real.volume_pi_ball _ (htpos (m + 1)), htsucc m,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    have h2 : (2 : ℝ) * (t m / 2) = t m := by ring
    rw [h2, mul_pow]
    ring
  -- each annulus contributes at least a fixed positive amount
  set c₀ : ℝ≥0∞ := ENNReal.ofReal ((2 ^ n - 1) * R ^ n / (c * R ^ k)) with hc₀
  have hc₀pos : c₀ ≠ 0 := by
    rw [hc₀, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have hB : (0 : ℝ) < 2 ^ n - 1 := by linarith
    positivity
  have hlower : ∀ m, c₀ ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ := by
    intro m
    have hstep : ∀ y ∈ A m,
        (ENNReal.ofReal (c * t m ^ k))⁻¹ ≤ (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ := by
      intro y hy
      have hy1 : ‖y‖ < t m := by simpa [Metric.mem_ball, dist_zero_right] using hy.1
      exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) hy1.le k) hc.le))
    have hconst : (ENNReal.ofReal (c * t m ^ k))⁻¹ * volume (A m)
        ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ := by
      calc (ENNReal.ofReal (c * t m ^ k))⁻¹ * volume (A m)
          = ∫⁻ _ in A m, (ENNReal.ofReal (c * t m ^ k))⁻¹ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem (hAmeas m)] with y hy using hstep y hy
    refine le_trans ?_ hconst
    rw [hvol m, hc₀, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    have hB : (0 : ℝ) ≤ 2 ^ n - 1 := by linarith
    have htm := htpos m
    have hjle : t m ^ j ≤ R ^ j := pow_le_pow_left₀ htm.le (htle m) j
    have hLHS : (2 ^ n - 1) * R ^ n / (c * R ^ (n + j)) = (2 ^ n - 1) / (c * R ^ j) := by
      rw [pow_add]
      field_simp
    have hRHS : (c * t m ^ (n + j))⁻¹ * ((2 ^ n - 1) * t m ^ n)
        = (2 ^ n - 1) / (c * t m ^ j) := by
      rw [pow_add]
      field_simp
    rw [hLHS, hRHS]
    exact div_le_div_of_nonneg_left hB (by positivity) (by nlinarith)
  -- summing over the annuli
  have hUnion : ∫⁻ y in ⋃ m, A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹
      = ∑' m, ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ :=
    lintegral_iUnion hAmeas hAdisj _
  have hmono : ∫⁻ y in ⋃ m, A m, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹
      ≤ ∫⁻ y in Metric.ball (0 : ι → ℝ) R, (ENNReal.ofReal (c * ‖y‖ ^ k))⁻¹ :=
    lintegral_mono' (Measure.restrict_mono (Set.iUnion_subset hAsub) le_rfl) le_rfl
  refine top_le_iff.1 (le_trans ?_ hmono)
  rw [hUnion, ← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hc₀pos]
  exact ENNReal.tsum_le_tsum hlower

/-- The harmonic series diverges, in `ℝ≥0∞`. -/
private lemma tsum_ofReal_div_natCast_succ_eq_top {b : ℝ} (hb : 0 < b) :
    ∑' m : ℕ, ENNReal.ofReal (b / (m + 1)) = ∞ := by
  by_contra hcon
  have hsum : Summable fun m : ℕ ↦ (ENNReal.ofReal (b / (m + 1))).toReal :=
    ENNReal.summable_toReal hcon
  have heq : (fun m : ℕ ↦ (ENNReal.ofReal (b / ((m : ℝ) + 1))).toReal)
      = fun m : ℕ ↦ b / ((m : ℝ) + 1) := by
    funext m
    exact ENNReal.toReal_ofReal (by positivity)
  rw [heq] at hsum
  have h2 : Summable fun m : ℕ ↦ 1 / (((m + 1 : ℕ) : ℝ)) := by
    refine (hsum.mul_left b⁻¹).congr fun m ↦ ?_
    push_cast
    field_simp
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

/-- **`∫ (c ‖y‖^k log ‖y‖⁻¹)⁻¹` over a ball of `ℝ^n` diverges when `k ≥ n`.** This is the
logarithmic refinement of `MeasureTheory.setLIntegral_inv_mul_norm_pow_ball_eq_top`: the extra
factor `log ‖y‖⁻¹` is *not* enough to make the integral converge, because on the dyadic annulus
`B(0, R/2^m) ∖ B(0, R/2^{m+1})` the logarithm is at most `(m+1) log(2/R)`, so the annuli
contribute a constant multiple of the harmonic series `∑_m 1/(m+1)`.

This is exactly the divergence at the end of Georgii's proof of Corollary (13.41),
`∫_0^δ (r log r^{-1})^{-1} dr = [-log log r^{-1}]_0^δ = ∞` in polar coordinates. -/
theorem setLIntegral_inv_mul_norm_pow_mul_log_inv_ball_eq_top {k : ℕ} (hk : Fintype.card ι ≤ k)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hR1 : R ≤ 1) :
    ∫⁻ y in Metric.ball (0 : ι → ℝ) R,
      (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ = ∞ := by
  classical
  set n := Fintype.card ι with hn
  have hn0 : 0 < n := Fintype.card_pos
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hn0
  -- the dyadic radii
  set t : ℕ → ℝ := fun m ↦ R / 2 ^ m with ht
  have htpos : ∀ m, 0 < t m := fun m ↦ by rw [ht]; positivity
  have htle : ∀ m, t m ≤ R := fun m ↦ div_le_self hR.le (one_le_pow₀ one_le_two)
  have htle1 : ∀ m, t m ≤ 1 := fun m ↦ (htle m).trans hR1
  have htsucc : ∀ m, t (m + 1) = t m / 2 := by
    intro m
    rw [ht]
    simp only
    rw [pow_succ, div_div]
  have htanti : ∀ m m' : ℕ, m ≤ m' → t m' ≤ t m := by
    intro m m' hmm'
    rw [ht]
    exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ one_le_two hmm')
  -- the dyadic annuli
  set A : ℕ → Set (ι → ℝ) := fun m ↦ Metric.ball (0 : ι → ℝ) (t m) \ Metric.ball 0 (t (m + 1))
    with hA
  have hAmeas : ∀ m, MeasurableSet (A m) := fun m ↦ measurableSet_ball.diff measurableSet_ball
  have hAsub : ∀ m, A m ⊆ Metric.ball (0 : ι → ℝ) R := fun m y hy ↦
    Metric.ball_subset_ball (htle m) hy.1
  have hAdisj : Pairwise (Disjoint on A) := by
    have key : ∀ a b : ℕ, a < b → Disjoint (A a) (A b) := by
      intro a b hab
      rw [Set.disjoint_left]
      rintro y ⟨-, hy2⟩ hy3
      exact hy2 (Metric.ball_subset_ball (htanti (a + 1) b hab) hy3.1)
    intro m m' hmm'
    rcases lt_or_gt_of_ne hmm' with hlt | hgt
    · exact key m m' hlt
    · exact (key m' m hgt).symm
  -- the volume of an annulus
  have hvol : ∀ m, volume (A m) = ENNReal.ofReal ((2 ^ n - 1) * t m ^ n) := by
    intro m
    have hsubm : Metric.ball (0 : ι → ℝ) (t (m + 1)) ⊆ Metric.ball 0 (t m) :=
      Metric.ball_subset_ball (htanti m (m + 1) (Nat.le_succ m))
    have hfin : volume (Metric.ball (0 : ι → ℝ) (t (m + 1))) ≠ ∞ := by
      rw [Real.volume_pi_ball _ (htpos (m + 1))]
      exact ENNReal.ofReal_ne_top
    rw [hA, measure_sdiff hsubm measurableSet_ball.nullMeasurableSet hfin,
      Real.volume_pi_ball _ (htpos m), Real.volume_pi_ball _ (htpos (m + 1)), htsucc m,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    have h2 : (2 : ℝ) * (t m / 2) = t m := by ring
    rw [h2, mul_pow]
    ring
  -- the logarithmic weight on the `m`-th annulus, and its comparison with `(m + 1) log (2/R)`
  set K : ℝ := Real.log (2 / R) with hK
  have hKpos : 0 < K := Real.log_pos (by rw [lt_div_iff₀ hR]; linarith)
  have hlogbound : ∀ m : ℕ, Real.log (t (m + 1))⁻¹ ≤ (m + 1) * K := by
    intro m
    have h1 : Real.log (t (m + 1))⁻¹ = (m + 1) * Real.log 2 + Real.log R⁻¹ := by
      rw [ht]
      simp only
      rw [Real.log_inv, Real.log_div hR.ne' (by positivity), Real.log_pow, Real.log_inv]
      push_cast
      ring
    have hlogR : 0 ≤ Real.log R⁻¹ := by
      rw [Real.log_inv, neg_nonneg]
      exact Real.log_nonpos hR.le hR1
    have hK' : K = Real.log 2 + Real.log R⁻¹ := by
      rw [hK, Real.log_div two_ne_zero hR.ne', Real.log_inv]
      ring
    have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [h1, hK']
    nlinarith [Real.log_pos one_lt_two]
  -- each annulus contributes at least a constant multiple of `1/(m+1)`
  have hlower : ∀ m : ℕ, ENNReal.ofReal ((2 ^ n - 1) / (c * K) / (m + 1))
      ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ := by
    intro m
    set D : ℝ := c * t m ^ k * ((m + 1) * K) with hD
    have hDpos : 0 < D := by rw [hD]; positivity
    have hstep : ∀ y ∈ A m,
        (ENNReal.ofReal D)⁻¹ ≤ (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ := by
      intro y hy
      have hy1 : ‖y‖ < t m := by simpa [Metric.mem_ball, dist_zero_right] using hy.1
      have hy2 : t (m + 1) ≤ ‖y‖ := by
        by_contra hcon
        exact hy.2 (by simpa [Metric.mem_ball, dist_zero_right] using not_le.1 hcon)
      have hypos : 0 < ‖y‖ := lt_of_lt_of_le (htpos (m + 1)) hy2
      have hlog : Real.log ‖y‖⁻¹ ≤ (m + 1) * K :=
        le_trans (by
          rw [Real.log_inv, Real.log_inv, neg_le_neg_iff]
          exact Real.log_le_log (htpos (m + 1)) hy2) (hlogbound m)
      have hlognn : 0 ≤ Real.log ‖y‖⁻¹ := by
        rw [Real.log_inv, neg_nonneg]
        exact Real.log_nonpos hypos.le (hy1.le.trans (htle1 m))
      refine ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal ?_)
      have hpow : ‖y‖ ^ k ≤ t m ^ k := pow_le_pow_left₀ (norm_nonneg y) hy1.le k
      have h1 : c * ‖y‖ ^ k * Real.log ‖y‖⁻¹ ≤ c * t m ^ k * Real.log ‖y‖⁻¹ := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) hlognn
      have h2 : c * t m ^ k * Real.log ‖y‖⁻¹ ≤ D := by
        rw [hD]
        exact mul_le_mul_of_nonneg_left hlog (by positivity)
      linarith
    have hconst : (ENNReal.ofReal D)⁻¹ * volume (A m)
        ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ := by
      calc (ENNReal.ofReal D)⁻¹ * volume (A m)
          = ∫⁻ _ in A m, (ENNReal.ofReal D)⁻¹ := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem (hAmeas m)] with y hy using hstep y hy
    refine le_trans ?_ hconst
    rw [hvol m, ← ENNReal.ofReal_inv_of_pos hDpos, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
    have hB : (0 : ℝ) ≤ 2 ^ n - 1 := by linarith
    have htm := htpos m
    have hjle : t m ^ j ≤ 1 := pow_le_one₀ htm.le (htle1 m)
    have hRHS : D⁻¹ * ((2 ^ n - 1) * t m ^ n)
        = (2 ^ n - 1) / (c * t m ^ j * ((m + 1) * K)) := by
      rw [hD, pow_add]
      field_simp
    have hLHS : (2 ^ n - 1) / (c * K) / ((m : ℝ) + 1) = (2 ^ n - 1) / (c * ((m + 1) * K)) := by
      field_simp
    rw [hRHS, hLHS]
    refine div_le_div_of_nonneg_left hB (by positivity) ?_
    have hfac : (0 : ℝ) ≤ ((m : ℝ) + 1) * K := by positivity
    have hstep2 : c * t m ^ j * (((m : ℝ) + 1) * K) ≤ c * 1 * (((m : ℝ) + 1) * K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjle hc.le) hfac
    linarith
  -- summing over the annuli
  have hUnion : ∫⁻ y in ⋃ m, A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹
      = ∑' m, ∫⁻ y in A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ :=
    lintegral_iUnion hAmeas hAdisj _
  have hmono : ∫⁻ y in ⋃ m, A m, (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹
      ≤ ∫⁻ y in Metric.ball (0 : ι → ℝ) R,
          (ENNReal.ofReal (c * ‖y‖ ^ k * Real.log ‖y‖⁻¹))⁻¹ :=
    lintegral_mono' (Measure.restrict_mono (Set.iUnion_subset hAsub) le_rfl) le_rfl
  refine top_le_iff.1 (le_trans ?_ hmono)
  rw [hUnion, ← tsum_ofReal_div_natCast_succ_eq_top (b := (2 ^ n - 1) / (c * K))
    (by have : (0:ℝ) < 2 ^ n - 1 := by linarith
        positivity)]
  exact ENNReal.tsum_le_tsum hlower

end MeasureTheory

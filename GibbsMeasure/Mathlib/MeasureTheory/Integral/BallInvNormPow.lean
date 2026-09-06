/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

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

## Main results

* `MeasureTheory.setLIntegral_inv_mul_norm_pow_ball_eq_top`
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

end MeasureTheory

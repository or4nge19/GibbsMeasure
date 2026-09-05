/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Beta-type improper integrals `∫_0^∞ w^s (1 + w)^t dw`

The integral `∫_0^∞ w^s (1 + w)^t dw` converges when `-1 < s` and `s + t < -1`: the exponent
`s` governs the singularity at `0`, the exponent `s + t` the decay at `∞`.  We prove this
convergence, the positivity of `∫_0^∞ w^s/(1 + w) dw`, and the homogeneity
`∫_0^∞ w^s/(κ + w) dw = κ^s ∫_0^∞ w^s/(1 + w) dw` (`κ > 0`) under the dilation `w ↦ κ w`.

## Main results

* `integrableOn_rpow_mul_one_add_rpow_Ioi`: `w ↦ w^s (1 + w)^t` is integrable on `(0, ∞)` when
  `-1 < s` and `s + t < -1`.
* `integrableOn_rpow_div_one_add_Ioi`: the case `t = -1`, for `-1 < s < 0`.
* `integral_rpow_div_one_add_Ioi_pos`: `0 < ∫_0^∞ w^s/(1 + w) dw` for `-1 < s < 0`.
* `integral_rpow_div_add_Ioi`: **homogeneity**, `∫_0^∞ w^s/(κ + w) dw = κ^s ∫_0^∞ w^s/(1+w) dw`
  for `κ > 0`.

## Implementation notes

`∫_0^∞ w^s/(1 + w) dw` is the Mellin transform of `w ↦ (1 + w)⁻¹` at `s + 1`, and the
homogeneity is `mellin_comp_mul_left`; the real-variable statement is proved directly from
`integral_comp_mul_left_Ioi`.  Its value `π / sin(π (s + 1))` is not needed here and not proved.
-/

@[expose] public section

open Set MeasureTheory

namespace MeasureTheory

/-- **Convergence of the Beta-type integral.**  `w ↦ w^s (1 + w)^t` is integrable on `(0, ∞)`
when `-1 < s` (integrability at `0`) and `s + t < -1` (integrability at `∞`). -/
theorem integrableOn_rpow_mul_one_add_rpow_Ioi {s t : ℝ} (hs : -1 < s) (hst : s + t < -1) :
    IntegrableOn (fun w : ℝ ↦ w ^ s * (1 + w) ^ t) (Ioi 0) := by
  have ht : t < 0 := by linarith
  have hmeas : Measurable fun w : ℝ ↦ w ^ s * (1 + w) ^ t := by fun_prop
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  refine IntegrableOn.union ?_ ?_
  · refine ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hs).mono'
      hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun w hw ↦ ?_
    have hw0 : 0 < w := hw.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hw0.le _)
      (Real.rpow_nonneg (by linarith) _))]
    calc w ^ s * (1 + w) ^ t ≤ w ^ s * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) ht.le)
            (Real.rpow_nonneg hw0.le _)
      _ = w ^ s := mul_one _
  · rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine (integrableOn_Ioi_rpow_of_lt hst zero_lt_one).mono' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun w hw ↦ ?_
    have hw1 : 1 < w := mem_Ioi.1 hw
    have hw0 : 0 < w := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hw0.le _)
      (Real.rpow_nonneg (by linarith) _))]
    calc w ^ s * (1 + w) ^ t ≤ w ^ s * w ^ t :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hw0 (by linarith) ht.le)
            (Real.rpow_nonneg hw0.le _)
      _ = w ^ (s + t) := (Real.rpow_add hw0 s t).symm

/-- `w ↦ w^s/(1 + w)` is integrable on `(0, ∞)` for `-1 < s < 0`. -/
theorem integrableOn_rpow_div_one_add_Ioi {s : ℝ} (hs₁ : -1 < s) (hs₂ : s < 0) :
    IntegrableOn (fun w : ℝ ↦ w ^ s / (1 + w)) (Ioi 0) := by
  refine (integrableOn_rpow_mul_one_add_rpow_Ioi hs₁ (t := -1) (by linarith)).congr_fun
    (fun w _ ↦ ?_) measurableSet_Ioi
  simp [Real.rpow_neg_one, div_eq_mul_inv]

/-- `∫_0^∞ w^s/(1 + w) dw > 0` for `-1 < s < 0`. -/
theorem integral_rpow_div_one_add_Ioi_pos {s : ℝ} (hs₁ : -1 < s) (hs₂ : s < 0) :
    0 < ∫ w in Ioi (0 : ℝ), w ^ s / (1 + w) := by
  have hint := integrableOn_rpow_div_one_add_Ioi hs₁ hs₂
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun w : ℝ ↦ w ^ s / (1 + w) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun w hw ↦
      div_nonneg (Real.rpow_nonneg (le_of_lt hw) _) (by linarith [mem_Ioi.1 hw])
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : Function.support (fun w : ℝ ↦ w ^ s / (1 + w)) ∩ Ioi 0 = Ioi 0 := by
    ext w
    simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
    intro hw
    exact (div_pos (Real.rpow_pos_of_pos hw _) (by linarith)).ne'
  rw [hsupp, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- **Homogeneity of `∫_0^∞ w^s/(κ + w) dw`.**  For `κ > 0`, the dilation `w ↦ κ w` gives
`∫_0^∞ w^s/(κ + w) dw = κ^s ∫_0^∞ w^s/(1 + w) dw`. -/
theorem integral_rpow_div_add_Ioi {s κ : ℝ} (hκ : 0 < κ) :
    ∫ w in Ioi (0 : ℝ), w ^ s / (κ + w) = κ ^ s * ∫ w in Ioi (0 : ℝ), w ^ s / (1 + w) := by
  have h := integral_comp_mul_left_Ioi (fun w : ℝ ↦ w ^ s / (κ + w)) 0 hκ
  rw [mul_zero] at h
  have hpt : EqOn (fun w : ℝ ↦ (κ * w) ^ s / (κ + κ * w))
      (fun w : ℝ ↦ (κ ^ s / κ) * (w ^ s / (1 + w))) (Ioi 0) := by
    intro w hw
    have hw0 : 0 < w := hw
    simp only
    rw [Real.mul_rpow hκ.le hw0.le, show κ + κ * w = κ * (1 + w) by ring]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, smul_eq_mul] at h
  have hκ' : κ ≠ 0 := hκ.ne'
  field_simp at h
  linarith

end MeasureTheory

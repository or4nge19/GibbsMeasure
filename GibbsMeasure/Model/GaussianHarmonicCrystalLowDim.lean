/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianHomogeneousExtreme
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.BallInvNormPow

/-!
# Georgii Example (13.43) for `d ≤ 2`: the harmonic crystal has no Gibbs measure

Georgii's Example (13.43) reads: "If `d ≤ 2` then `𝒢(γ^{J,0}) = ∅`, because of Corollary (13.41)."
For the harmonic crystal the analytic content of Corollary (13.41) — that the root `z = 1` of `Ĵ`
forces `∫_G Ĵ(z)⁻¹ dz = ∞` in dimensions `d ≤ 2` — is elementary: the *upper* bound
`Ĵ(z_p) ≤ 2π²β ‖p‖²` matches the lower bound `Ĵ(z_p) ≥ (8β/d)‖p‖²` already recorded in
`GibbsMeasure/Model/GaussianHomogeneous.lean`, and `‖p‖^{-2}` fails to be integrable near the
origin of `ℝ^d` exactly when `d ≤ 2`
(`MeasureTheory.setLIntegral_inv_mul_norm_pow_ball_eq_top`). The step from `∫_G Ĵ⁻¹ dz = ∞` to
`𝒢(γ^{J,0}) = ∅` is the necessity half of Theorem (13.36),
`Potential.nonempty_G_homogeneousCoupling_iff`.

This closes the `d ≤ 2` half of Example (13.43); Corollary (13.41) itself — for a general
absolutely summable `J` satisfying `∑_{0 < |i| ≤ n} |i|^d |J(i)| ≤ L log n` — is not proved here.
What (13.41) needs beyond the present file is Georgii's estimate
`Ĵ(p) ≤ M |p - q|^d log |p - q|^{-1}` near a root `q` (in `d = 2` through `grad Ĵ(q) = 0`, which
uses `∑_i |i| |J(i)| < ∞`), together with the corresponding logarithmic refinement of the
divergence lemma. The harmonic crystal has finite range, so the quadratic bound suffices for it.

## Main results

* `Potential.re_fourierHomogeneousCoupling_harmonicCrystalCoupling_le`: `Ĵ(z_p) ≤ 2π²β ‖p‖²`.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_eq_top`:
  `∫_G Ĵ(z)⁻¹ dz = ∞` for `d ≤ 2`.
* `Potential.not_nonempty_G_harmonicCrystalCoupling`: **Georgii Example (13.43) for `d ≤ 2`** —
  `𝒢(γ^{J,h}) = ∅` for every constant external field `h`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Set

open scoped ENNReal

noncomputable section

namespace Potential

open UnitAddTorus

/-- Normalised Haar measure on `ℝ/ℤ`, as in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`. -/
local instance instMeasureSpaceUnitAddCircleLowDim : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolumeLowDim :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolumeLowDim :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq d] {β : ℝ}

/-- **The upper bound matching Georgii's estimate in Example (13.43)**:
`Ĵ(z_p) ≤ 2π²β ‖p‖²` on all of `ℝ^d`, from `1 - cos t ≤ t²/2`. -/
lemma re_fourierHomogeneousCoupling_harmonicCrystalCoupling_le [Nonempty d] (hβ : 0 < β)
    (x : d → ℝ) :
    (fourierHomogeneousCoupling (harmonicCrystalCoupling d β)
        (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re
      ≤ 2 * Real.pi ^ 2 * β * ‖x‖ ^ 2 := by
  rw [re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe]
  have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ ℓ : d, 1 - Real.cos (2 * Real.pi * x ℓ) ≤ 2 * Real.pi ^ 2 * ‖x‖ ^ 2 := by
    intro ℓ
    have hcos : 1 - (2 * Real.pi * x ℓ) ^ 2 / 2 ≤ Real.cos (2 * Real.pi * x ℓ) :=
      Real.one_sub_sq_div_two_le_cos
    have hx : |x ℓ| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x ℓ
    have hsq : x ℓ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [← sq_abs (x ℓ)]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  calc β / Fintype.card d * ∑ ℓ, (1 - Real.cos (2 * Real.pi * x ℓ))
      ≤ β / Fintype.card d * ∑ _ℓ : d, 2 * Real.pi ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ ↦ hterm ℓ) (by positivity)
    _ = 2 * Real.pi ^ 2 * β * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **Georgii Example (13.43) for `d ≤ 2`, the analytic half**: `∫_G Ĵ(z)⁻¹ dz = ∞`. -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_eq_top [Nonempty d]
    (hβ : 0 < β) (hd : Fintype.card d ≤ 2) :
    ∫⁻ z, (ENNReal.ofReal
      (fourierHomogeneousCoupling (harmonicCrystalCoupling d β) z).re)⁻¹ = ∞ := by
  rw [UnitAddTorus.lintegral_preimage _ fun _ : d ↦ (-(1 : ℝ) / 2)]
  -- the open ball of radius `1/2` for the supremum norm sits inside the fundamental cube
  have hball : Metric.ball (0 : d → ℝ) (1 / 2)
      ⊆ {y : d → ℝ | ∀ i, y i ∈ Set.Ioc ((fun _ : d ↦ -(1 : ℝ) / 2) i)
        ((fun _ : d ↦ -(1 : ℝ) / 2) i + 1)} := by
    intro y hy i
    have hyi : |y i| < 1 / 2 := by
      have := norm_le_pi_norm y i
      have hy' : ‖y‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
      simpa [Real.norm_eq_abs] using lt_of_le_of_lt this hy'
    rw [abs_lt] at hyi
    constructor <;> simp <;> linarith [hyi.1, hyi.2]
  refine top_le_iff.1 (le_trans ?_ (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl))
  -- on that ball, `Ĵ⁻¹ ≥ (2π²β ‖y‖²)⁻¹`, whose integral diverges when `d ≤ 2`
  rw [← setLIntegral_inv_mul_norm_pow_ball_eq_top (ι := d) (k := 2) (c := 2 * Real.pi ^ 2 * β)
    (R := 1 / 2) hd (by positivity) (by norm_num)]
  refine lintegral_mono fun y ↦ ?_
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal
    (re_fourierHomogeneousCoupling_harmonicCrystalCoupling_le hβ y))

variable [LinearOrder (d → ℤ)]

/-- **Georgii Example (13.43) for `d ≤ 2`**: the harmonic crystal has *no* Gibbs measure in
dimensions `d ≤ 2`, for every constant external field. -/
theorem not_nonempty_G_harmonicCrystalCoupling [Nonempty d] (hβ : 0 < β)
    (hd : Fintype.card d ≤ 2) (h : ℝ) :
    ¬ (MeasureTheory.GibbsMeasure.G (gaussianSpecification
      (homogeneousCoupling (harmonicCrystalCoupling d β)) (fun _ ↦ h)
      (symm_homogeneousCoupling harmonicCrystalCoupling_neg)
      (finite_setOf_homogeneousCoupling_ne_zero finite_setOf_harmonicCrystalCoupling_ne_zero)
      (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ) 1 one_pos)).Nonempty := by
  intro hG
  have hne := (nonempty_G_homogeneousCoupling_iff summable_abs_harmonicCrystalCoupling
    harmonicCrystalCoupling_neg finite_setOf_harmonicCrystalCoupling_ne_zero
    (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ)
    (re_fourierHomogeneousCoupling_harmonicCrystalCoupling_nonneg hβ)).1 hG
  exact hne.2 (lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_eq_top hβ hd)

/-- **Georgii Example (13.43)** in full, as a dichotomy in the dimension: the harmonic crystal has
Gibbs measures if and only if `d ≥ 3`. -/
theorem nonempty_G_harmonicCrystalCoupling_iff [Nonempty d] (hβ : 0 < β) :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification
      (homogeneousCoupling (harmonicCrystalCoupling d β)) (fun _ ↦ (0 : ℝ))
      (symm_homogeneousCoupling harmonicCrystalCoupling_neg)
      (finite_setOf_homogeneousCoupling_ne_zero finite_setOf_harmonicCrystalCoupling_ne_zero)
      (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ) 1 one_pos)).Nonempty
      ↔ 3 ≤ Fintype.card d := by
  refine ⟨fun hG ↦ ?_, fun hd ↦ nonempty_G_harmonicCrystalCoupling hβ hd⟩
  by_contra hd
  exact not_nonempty_G_harmonicCrystalCoupling hβ (by omega) 0 hG

end Potential

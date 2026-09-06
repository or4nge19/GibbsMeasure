/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import GibbsMeasure.Specification.GaussianDomination
public import GibbsMeasure.Specification.InfraredBoundCorrelation

/-!
# Georgii (20.14) and Proposition (20.12): the infrared bound

Georgii's Proposition (20.12) is the *infrared bound*

`0 ≤ C_Λ^Φ(z) ≤ N (Ĵ(1) - Ĵ(z))⁻¹`   for `z ∈ G_Λ` with `Ĵ(z) ≠ Ĵ(1)`,

for the Fourier transform (20.11) of the correlation function of the Gibbs distribution in the
cube `Λ` with periodic boundary condition.  The lower bound is `correlationFourier_nonneg` in
`GibbsMeasure.Specification.InfraredBoundCorrelation`; the upper bound is proved here from
Lemma (20.13) (`GibbsMeasure.Specification.GaussianDomination`).

## Main results

* `integral_sq_le_two_mul_of_lintegral_exp_le` (and `integrable_sq_of_lintegral_exp_le`) — the
  analytic core: a probability measure with the sub-Gaussian bound `μ(e^{t f}) ≤ e^{t² B}` for
  every real `t` has `f ∈ L²(μ)` and `μ(f²) ≤ 2B`.  Intended home:
  `GibbsMeasure/Mathlib/MeasureTheory/Integral/ExponentialMoment.lean`.
* `integral_sq_heisenbergShiftPairing_le` — **Georgii (20.14) for a real shift**:
  `°γ_Λ^Φ(A(ζ,·)²) ≤ 2 B(ζ)`, with `A(ζ, ω) = ½ ∑_{i,j} J_Λ(i-j)(ω_i - ω_j)·(ζ_i - ζ_j)`
  (`heisenbergShiftPairing`) and `B(ζ) = ¼ ∑_{i,j} J_Λ(i-j)|ζ_i - ζ_j|²`
  (`heisenbergShiftEnergy`).
* `sum_periodizedCoupling_mul_sub_mul_sub_mFourier` and `sq_add_sq_heisenbergShiftPairing` —
  Georgii's identity for the left-hand side of (20.14) at `ζ = (Re(z^i)e_ℓ)`, `η = (Im(z^i)e_ℓ)`:
  `A(ζ,ω)² + A(η,ω)² = (Ĵ(1) - Ĵ(z))² |∑_i σ_{i,ℓ} z^i|²`.
* `sum_periodizedCoupling_mul_norm_sq_sub` and `heisenbergShiftEnergy_fourierShift_add` — his
  identity for the right-hand side: `2B(ζ) + 2B(η) = |Λ|(Ĵ(1) - Ĵ(z))`.
* `sq_mul_correlationFourier_le` — **Proposition (20.12)** in the division-free form
  `(Ĵ(1) - Ĵ(z))² C_Λ^Φ(z) ≤ N(Ĵ(1) - Ĵ(z))`, `correlationFourier_le` — its stated form
  `C_Λ^Φ(z) ≤ N(Ĵ(1) - Ĵ(z))⁻¹`, and `couplingFourier_le_couplingFourier_zero` — the by-product
  `Ĵ(z) ≤ Ĵ(1)` on `G_Λ`, which Georgii instead reads off from `J ≥ 0` in Comment (20.17)(1).

## What is not proved: Theorem (20.15)

Beyond (20.12), Georgii's spontaneous-magnetisation theorem needs: the orthogonality of the
characters on the *finite* dual group `G_Λ` (the `2N`-torsion of `(ℝ/ℤ)^d`), which is not yet
available — `G_Λ` is not carried as a `Finset` anywhere in this development, so neither is the
inversion `|Λ|⁻¹ ∑_{z ∈ G_Λ}(1 - z^{-j}) C_Λ^Φ(z) = °γ_Λ^Φ(|σ_0|²) - °γ_Λ^Φ(σ_0·σ_j)`; the
Riemann-sum hypothesis (20.19) resp. the transience condition (20.16); Lemma (20.8)
(`exists_le_lintegral_dotProduct_self_heisenbergPeriodicGibbsDist`, available) and Proposition
(20.7) (`heisenbergGZero_nonempty_and_subset`, available); and the ergodic input — the `L²`
ergodic theorem (14.A3) or the random ergodic theorem (20.23), together with (14.10) and
(14.17).

## Deviation from Georgii

Georgii deduces (20.14) from `φ''(0) ≤ 0` for `φ(t) = °γ_Λ^Φ(f_Λ^Φ(tζ, ·))`, differentiating
twice under the integral sign and justifying the interchange by Lemma (20.6)(i).  Here the same
conclusion is obtained from Lemma (20.13) alone, by the elementary inequalities
`2 + u² ≤ e^u + e^{-u}` and "`1 + x c ≤ e^{x B}` for all `x ≥ 0` implies `c ≤ B`".  Lemma
(20.6)(i) is not needed, and neither is any differentiability statement.

All the results below take Georgii's Lemma (20.13) in the form `IsGaussianDominating` as a
hypothesis; see the module documentation of `GibbsMeasure.Specification.GaussianDomination` for
what is and is not proved about that hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The analytic core: a sub-Gaussian bound gives a second-moment bound -/

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

/-- `2 + u² ≤ e^u + e^{-u}`: the second-order expansion of the hyperbolic cosine, in the form
used to turn Gaussian domination into a second-moment bound.  Intended home:
`Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean` (as
`Real.one_add_sq_div_two_le_cosh`). -/
private lemma two_add_sq_le_exp_add_exp_neg (u : ℝ) :
    2 + u ^ 2 ≤ Real.exp u + Real.exp (-u) := by
  have h1 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (u / 2) * Real.exp (-(u / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hsinh : Real.exp (u / 2) - Real.exp (-(u / 2)) = 2 * Real.sinh (u / 2) := by
    rw [Real.sinh_eq]; ring
  have hs : (2 * Real.sinh (u / 2)) ^ 2 = Real.exp u + Real.exp (-u) - 2 := by
    rw [← hsinh]
    have hexp : (Real.exp (u / 2) - Real.exp (-(u / 2))) ^ 2
        = Real.exp (u / 2) * Real.exp (u / 2)
          - 2 * (Real.exp (u / 2) * Real.exp (-(u / 2)))
          + Real.exp (-(u / 2)) * Real.exp (-(u / 2)) := by ring
    rw [hexp, h1, h2, h3]; ring
  have hv : (u / 2) ^ 2 ≤ Real.sinh (u / 2) ^ 2 := by
    rcases le_total 0 (u / 2) with hu | hu
    · have := Real.self_le_sinh_iff.2 hu
      nlinarith
    · have hu' : (0 : ℝ) ≤ -(u / 2) := by linarith
      have := Real.self_le_sinh_iff.2 hu'
      rw [Real.sinh_neg] at this
      nlinarith
  nlinarith [hs, hv]

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
    have hb := two_add_sq_le_exp_add_exp_neg (t * f x)
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
`μ(e^{t f}) ≤ e^{t² B}` for every `t ∈ ℝ`, then `f ∈ L²(μ)`.  Intended home:
`GibbsMeasure/Mathlib/MeasureTheory/Integral/ExponentialMoment.lean`. -/
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
Intended home: `GibbsMeasure/Mathlib/MeasureTheory/Integral/ExponentialMoment.lean`. -/
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

/-! ### Georgii (20.14) for a real shift -/

section Georgii2014

variable {d N n : ℕ} [NeZero N] {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}
  [IsFiniteMeasure ν]

/-- **Lemma (20.13) along the ray `t ζ` is a sub-Gaussian bound for Georgii's linear form**:
`°γ_Λ^Φ(e^{t A(ζ,·)}) ≤ e^{t² B(ζ)}` for every `t ∈ ℝ`. -/
theorem lintegral_exp_heisenbergShiftPairing_le (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) (t : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t * heisenbergShiftPairing N n J ζ ω))
        ∂(heisenbergPeriodicGibbsDist N n J ν))
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * heisenbergShiftEnergy N n J ζ)) := by
  set B := heisenbergShiftEnergy N n J ζ with hB
  have hmeas : Measurable fun ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (t * heisenbergShiftPairing N n J ζ ω)) :=
    (Real.continuous_exp.measurable.comp
      ((measurable_heisenbergShiftPairing ζ).const_mul t)).ennreal_ofReal
  set X := ∫⁻ ω, ENNReal.ofReal (Real.exp (t * heisenbergShiftPairing N n J ζ ω))
    ∂(heisenbergPeriodicGibbsDist N n J ν) with hX
  have hdom' : ENNReal.ofReal (Real.exp (-(t ^ 2 * B))) * X ≤ 1 := by
    have h := lintegral_heisenbergShiftFactor_le_one hν hexp hsum hdom (t • ζ)
    rw [hX, ← lintegral_const_mul _ hmeas]
    refine le_trans (le_of_eq (lintegral_congr fun ω ↦ ?_)) h
    rw [heisenbergShiftFactor, heisenbergShiftExponent_smul,
      show t * heisenbergShiftPairing N n J ζ ω - t ^ 2 * B
        = -(t ^ 2 * B) + t * heisenbergShiftPairing N n J ζ ω from by ring,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hc0 : ENNReal.ofReal (Real.exp (-(t ^ 2 * B))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hctop : ENNReal.ofReal (Real.exp (-(t ^ 2 * B))) ≠ ∞ := ENNReal.ofReal_ne_top
  have hinv : (ENNReal.ofReal (Real.exp (-(t ^ 2 * B))))⁻¹
      = ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by
    rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos _), inv_inv]
  calc X = (ENNReal.ofReal (Real.exp (-(t ^ 2 * B))))⁻¹
        * (ENNReal.ofReal (Real.exp (-(t ^ 2 * B))) * X) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (-(t ^ 2 * B))))⁻¹ * 1 := mul_le_mul' le_rfl hdom'
    _ = ENNReal.ofReal (Real.exp (t ^ 2 * B)) := by rw [mul_one, hinv]

/-- **Georgii (20.14), for a real shift `ζ`.**

`°γ_Λ^Φ(A(ζ, ·)²) ≤ 2 B(ζ)`, where `A(ζ, ω) = ½ ∑_{i,j ∈ Λ} J_Λ(i-j)(ω_i - ω_j)·(ζ_i - ζ_j)` is
`heisenbergShiftPairing` and `B(ζ) = ¼ ∑_{i,j ∈ Λ} J_Λ(i-j)|ζ_i - ζ_j|²` is
`heisenbergShiftEnergy`.

Lemma (20.13) applied along the ray `t ζ` reads `°γ_Λ^Φ(e^{t A(ζ,·)}) ≤ e^{t² B(ζ)}` for every
real `t`, i.e. `A(ζ, ·)` is sub-Gaussian with variance proxy `2 B(ζ)`; the conclusion is then
`integral_sq_le_two_mul_of_lintegral_exp_le`.  Georgii instead differentiates twice under the
integral sign at `t = 0`, using Lemma (20.6)(i) to justify the interchange; that step is not
needed here. -/
theorem integral_sq_heisenbergShiftPairing_le (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫ ω, heisenbergShiftPairing N n J ζ ω ^ 2 ∂(heisenbergPeriodicGibbsDist N n J ν))
      ≤ 2 * heisenbergShiftEnergy N n J ζ := by
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d + 1) (J := J) hexp hsum
  have hprob : IsProbabilityMeasure (heisenbergPeriodicGibbsDist N n J ν) :=
    isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
  exact integral_sq_le_two_mul_of_lintegral_exp_le (measurable_heisenbergShiftPairing ζ)
    (lintegral_exp_heisenbergShiftPairing_le hν hexp hsum hdom ζ)

/-- **Square integrability of Georgii's linear form**, contained in (20.14). -/
theorem integrable_sq_heisenbergShiftPairing (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) :
    Integrable (fun ω ↦ heisenbergShiftPairing N n J ζ ω ^ 2)
      (heisenbergPeriodicGibbsDist N n J ν) := by
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d + 1) (J := J) hexp hsum
  have hprob : IsProbabilityMeasure (heisenbergPeriodicGibbsDist N n J ν) :=
    isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
  exact integrable_sq_of_lintegral_exp_le (measurable_heisenbergShiftPairing ζ)
    (lintegral_exp_heisenbergShiftPairing_le hν hexp hsum hdom ζ)

/-- **The quadratic form of (20.13) is nonnegative** — a by-product of (20.14): it dominates a
second moment. -/
theorem heisenbergShiftEnergy_nonneg (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) :
    0 ≤ heisenbergShiftEnergy N n J ζ := by
  have h := integral_sq_heisenbergShiftPairing_le hν hexp hsum hdom ζ
  have h0 : (0 : ℝ) ≤ ∫ ω, heisenbergShiftPairing N n J ζ ω ^ 2
      ∂(heisenbergPeriodicGibbsDist N n J ν) := integral_nonneg fun ω ↦ sq_nonneg _
  linarith

end Georgii2014

/-! ### Georgii's two identities in the proof of Proposition (20.12) -/

section Identities

variable {d L n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {x : UnitAddTorus (Fin (d + 1))}

/-- A character of the torus has modulus one at every point.  Intended home:
`Mathlib/Analysis/Fourier/AddCircleMulti.lean` (the sup-norm version `mFourier_norm` is there). -/
private lemma norm_mFourier_apply (m : Fin (d + 1) → ℤ) (y : UnitAddTorus (Fin (d + 1))) :
    ‖mFourier m y‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply, Circle.norm_coe,
    Finset.prod_const_one]

private lemma mFourier_mul_conj_self (m : Fin (d + 1) → ℤ) :
    mFourier m x * conj (mFourier m x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mFourier_apply]
  norm_num

/-- The column sum of the periodised coupling, the transpose of `sum_periodizedCoupling_sub`. -/
theorem sum_periodizedCoupling_sub_right (hsum : Summable J)
    (j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J (i - j)) = ∑' m, J m := by
  have h : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J (i - j))
      = ∑ z : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J z :=
    Fintype.sum_equiv (Equiv.subRight j) _ _ fun i ↦ by simp
  rw [h]
  exact sum_periodizedCoupling hsum

/-- **Georgii (20.10) with the real part carried out**: on `G_Λ`,
`Ĵ(z) = ∑_{v ∈ Λ} J_Λ(v) Re(z^v)`. -/
theorem couplingFourier_eq_sum_periodizedCoupling_re (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0) :
    couplingFourier J x = ∑ v : Fin (d + 1) → ZMod (2 * (L + 1)),
      periodizedCoupling (L + 1) J v * (mFourier (torusToLattice L v) x).re := by
  have h := ofReal_couplingFourier heven x
  rw [tsum_mul_mFourier_eq_sum_periodizedCoupling hsum L hx] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re, Complex.re_sum] at hre
  rw [hre]
  exact Finset.sum_congr rfl fun v _ ↦ Complex.re_ofReal_mul _ _

/-- **Georgii's `Ĵ(1) = ∑_{v ∈ Λ} J_Λ(v)`**, the value at the neutral element of `G`. -/
theorem couplingFourier_zero_eq_sum_periodizedCoupling (hsum : Summable J) :
    couplingFourier J (0 : UnitAddTorus (Fin (d + 1)))
      = ∑ v : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J v := by
  rw [couplingFourier_zero, sum_periodizedCoupling hsum]

/-- **Georgii's `∑_{j ∈ Λ} J_Λ(i-j) z^{j-i} = Ĵ(z)`** for `z ∈ G_Λ`: the evenness of `J` turns
the reflected sum into the transform itself. -/
theorem sum_periodizedCoupling_mul_mFourier_sub_left (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), (periodizedCoupling (L + 1) J (i - j) : ℂ)
        * mFourier (torusToLattice L (j - i)) x)
      = ((couplingFourier J x : ℝ) : ℂ) := by
  rw [ofReal_couplingFourier heven, tsum_mul_mFourier_eq_sum_periodizedCoupling hsum L hx]
  refine Fintype.sum_equiv (Equiv.subRight i) _ _ fun j ↦ ?_
  change (periodizedCoupling (L + 1) J (i - j) : ℂ) * mFourier (torusToLattice L (j - i)) x
      = (periodizedCoupling (L + 1) J (j - i) : ℂ) * mFourier (torusToLattice L (j - i)) x
  rw [show i - j = -(j - i) from by abel, periodizedCoupling_neg heven]

/-- **Georgii's `∑_{i ∈ Λ} J_Λ(i-j) z^{i-j} = Ĵ(z)`** for `z ∈ G_Λ`. -/
theorem sum_periodizedCoupling_mul_mFourier_sub_right (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), (periodizedCoupling (L + 1) J (i - j) : ℂ)
        * mFourier (torusToLattice L (i - j)) x)
      = ((couplingFourier J x : ℝ) : ℂ) := by
  rw [ofReal_couplingFourier heven, tsum_mul_mFourier_eq_sum_periodizedCoupling hsum L hx]
  exact Fintype.sum_equiv (Equiv.subRight j) _ _ fun i ↦ rfl

/-- **Georgii's second identity in the proof of (20.12)**:

`½ ∑_{i,j ∈ Λ} J_Λ(i-j)(a_i - a_j)(z^i - z^j) = (Ĵ(1) - Ĵ(z)) ∑_{i ∈ Λ} a_i z^i`

for every `a : Λ → ℂ` and every `z ∈ G_Λ`.  Georgii states it for `a_i = σ_{i,ℓ}`. -/
theorem sum_periodizedCoupling_mul_sub_mul_sub_mFourier (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (a : (Fin (d + 1) → ZMod (2 * (L + 1))) → ℂ) :
    (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ) * ((a i - a j)
          * (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x))) / 2
      = (((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x : ℝ)) : ℂ)
        * ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), a i * mFourier (torusToLattice L i) x := by
  classical
  have hKsum : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
      (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), (periodizedCoupling (L + 1) J (i - j) : ℂ))
        = ((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) : ℝ) : ℂ) := by
    intro i
    rw [← Complex.ofReal_sum, sum_periodizedCoupling_sub hsum i, couplingFourier_zero]
  have hKsum' : ∀ j : Fin (d + 1) → ZMod (2 * (L + 1)),
      (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), (periodizedCoupling (L + 1) J (i - j) : ℂ))
        = ((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) : ℝ) : ℂ) := by
    intro j
    rw [← Complex.ofReal_sum, sum_periodizedCoupling_sub_right hsum j, couplingFourier_zero]
  -- the four blocks of the expanded double sum
  have hT1 : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ)
          * (a i * mFourier (torusToLattice L i) x))
      = ((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) : ℝ) : ℂ)
        * ∑ i, a i * mFourier (torusToLattice L i) x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_mul, hKsum i]
  have hT4 : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ)
          * (a j * mFourier (torusToLattice L j) x))
      = ((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) : ℝ) : ℂ)
        * ∑ i, a i * mFourier (torusToLattice L i) x := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.sum_mul, hKsum' j]
  have hT2 : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ)
          * (a i * mFourier (torusToLattice L j) x))
      = ((couplingFourier J x : ℝ) : ℂ) * ∑ i, a i * mFourier (torusToLattice L i) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hstep : ∀ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ) * (a i * mFourier (torusToLattice L j) x)
          = a i * mFourier (torusToLattice L i) x * ((periodizedCoupling (L + 1) J (i - j) : ℂ)
            * mFourier (torusToLattice L (j - i)) x) := by
      intro j
      have hmul : mFourier (torusToLattice L j) x
          = mFourier (torusToLattice L i) x * mFourier (torusToLattice L (j - i)) x := by
        have h := mFourier_torusToLattice_add hx i (j - i)
        rw [show i + (j - i) = j from by abel] at h
        exact h
      rw [hmul]; ring
    rw [Finset.sum_congr rfl fun j _ ↦ hstep j, ← Finset.mul_sum,
      sum_periodizedCoupling_mul_mFourier_sub_left hsum heven hx i]
    exact mul_comm _ _
  have hT3 : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ)
          * (a j * mFourier (torusToLattice L i) x))
      = ((couplingFourier J x : ℝ) : ℂ) * ∑ i, a i * mFourier (torusToLattice L i) x := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hstep : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ) * (a j * mFourier (torusToLattice L i) x)
          = a j * mFourier (torusToLattice L j) x * ((periodizedCoupling (L + 1) J (i - j) : ℂ)
            * mFourier (torusToLattice L (i - j)) x) := by
      intro i
      have hmul : mFourier (torusToLattice L i) x
          = mFourier (torusToLattice L j) x * mFourier (torusToLattice L (i - j)) x := by
        have h := mFourier_torusToLattice_add hx j (i - j)
        rw [show j + (i - j) = i from by abel] at h
        exact h
      rw [hmul]; ring
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i, ← Finset.mul_sum,
      sum_periodizedCoupling_mul_mFourier_sub_right hsum heven hx j]
    exact mul_comm _ _
  -- expand and assemble
  have hexpand : (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        (periodizedCoupling (L + 1) J (i - j) : ℂ) * ((a i - a j)
          * (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x)))
      = ((∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (periodizedCoupling (L + 1) J (i - j) : ℂ)
              * (a i * mFourier (torusToLattice L i) x))
          - ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (periodizedCoupling (L + 1) J (i - j) : ℂ)
              * (a i * mFourier (torusToLattice L j) x))
        - ((∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (periodizedCoupling (L + 1) J (i - j) : ℂ)
              * (a j * mFourier (torusToLattice L i) x))
          - ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (periodizedCoupling (L + 1) J (i - j) : ℂ)
              * (a j * mFourier (torusToLattice L j) x)) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hexpand, hT1, hT2, hT3, hT4]
  push_cast
  ring

end Identities

/-! ### Proposition (20.12): the infrared bound -/

section Georgii2012

variable {d L n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}
  {x : UnitAddTorus (Fin (d + 1))}

variable (L n) in
/-- **Georgii's `ζ = (Re(z^i) e_ℓ)_{i ∈ Λ}`** in the proof of Proposition (20.12). -/
def fourierShiftRe (l : Fin n) (x : UnitAddTorus (Fin (d + 1)))
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) : Fin n → ℝ :=
  (mFourier (torusToLattice L i) x).re • Pi.single l (1 : ℝ)

variable (L n) in
/-- **Georgii's `η = (Im(z^i) e_ℓ)_{i ∈ Λ}`** in the proof of Proposition (20.12). -/
def fourierShiftIm (l : Fin n) (x : UnitAddTorus (Fin (d + 1)))
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) : Fin n → ℝ :=
  (mFourier (torusToLattice L i) x).im • Pi.single l (1 : ℝ)

variable (L n J) in
/-- **The complex left-hand side of Georgii (20.14)**,
`½ ∑_{i,j ∈ Λ} J_Λ(i-j)(σ_{i,ℓ} - σ_{j,ℓ})(z^i - z^j)`.  Its real and imaginary parts are the
linear forms of (20.13) at `fourierShiftRe` and `fourierShiftIm`. -/
def fourierPairing (l : Fin n) (x : UnitAddTorus (Fin (d + 1)))
    (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)) : ℂ :=
  (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
    (periodizedCoupling (L + 1) J (i - j) : ℂ)
      * ((((ω i l : ℝ) : ℂ) - ((ω j l : ℝ) : ℂ))
        * (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x))) / 2

/-- The dot product against a shift of the form `c • e_ℓ`. -/
private lemma dotProduct_smul_single (u : Fin n → ℝ) (c : ℝ) (l : Fin n) :
    u ⬝ᵥ (c • Pi.single l (1 : ℝ)) = c * u l := by
  rw [dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]

private lemma fourierShift_sub_re (l : Fin n) (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    fourierShiftRe L n l x i - fourierShiftRe L n l x j
      = (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x).re
        • Pi.single l (1 : ℝ) := by
  rw [fourierShiftRe, fourierShiftRe, ← sub_smul, Complex.sub_re]

private lemma fourierShift_sub_im (l : Fin n) (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    fourierShiftIm L n l x i - fourierShiftIm L n l x j
      = (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x).im
        • Pi.single l (1 : ℝ) := by
  rw [fourierShiftIm, fourierShiftIm, ← sub_smul, Complex.sub_im]

/-- The real part of `fourierPairing` is Georgii's linear form at `ζ = (Re(z^i) e_ℓ)`. -/
theorem fourierPairing_re (l : Fin n)
    (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :
    (fourierPairing L n J l x ω).re
      = heisenbergShiftPairing (L + 1) n J (fourierShiftRe L n l x) ω := by
  rw [fourierPairing, heisenbergShiftPairing, Complex.div_ofNat_re, Complex.re_sum]
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.re_ofReal_mul, fourierShift_sub_re, dotProduct_smul_single, Complex.mul_re]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    Pi.sub_apply]
  ring

/-- The imaginary part of `fourierPairing` is Georgii's linear form at `η = (Im(z^i) e_ℓ)`. -/
theorem fourierPairing_im (l : Fin n)
    (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :
    (fourierPairing L n J l x ω).im
      = heisenbergShiftPairing (L + 1) n J (fourierShiftIm L n l x) ω := by
  rw [fourierPairing, heisenbergShiftPairing, Complex.div_ofNat_im, Complex.im_sum]
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Complex.im_ofReal_mul, fourierShift_sub_im, dotProduct_smul_single, Complex.mul_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    Pi.sub_apply]
  ring

/-- **Georgii's identity for the left-hand side of (20.14)**:
`½ ∑_{i,j} J_Λ(i-j)(σ_{i,ℓ} - σ_{j,ℓ})(z^i - z^j) = (Ĵ(1) - Ĵ(z)) ∑_i σ_{i,ℓ} z^i`. -/
theorem fourierPairing_eq (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hx : Potential.intBoxLen L • x = 0) (l : Fin n)
    (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :
    fourierPairing L n J l x ω
      = ((couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x : ℝ) : ℂ)
        * ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x :=
  sum_periodizedCoupling_mul_sub_mul_sub_mFourier hsum heven hx fun i ↦ ((ω i l : ℝ) : ℂ)

/-- **The left-hand side of Georgii (20.14), summed over the real and imaginary shifts**:
`A(ζ,ω)² + A(η,ω)² = (Ĵ(1) - Ĵ(z))² |∑_i σ_{i,ℓ} z^i|²`. -/
theorem sq_add_sq_heisenbergShiftPairing (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hx : Potential.intBoxLen L • x = 0) (l : Fin n)
    (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :
    heisenbergShiftPairing (L + 1) n J (fourierShiftRe L n l x) ω ^ 2
        + heisenbergShiftPairing (L + 1) n J (fourierShiftIm L n l x) ω ^ 2
      = (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) ^ 2
        * ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2 := by
  have hnormsq : ∀ w : ℂ, w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    intro w
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [← fourierPairing_re, ← fourierPairing_im, hnormsq, fourierPairing_eq hsum heven hx,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! #### The right-hand side of (20.14) at the Fourier shifts -/

/-- `∑_{j ∈ Λ} J_Λ(i-j) z^{i-j} = Ĵ(z)` for `z ∈ G_Λ`. -/
theorem sum_periodizedCoupling_mul_mFourier_sub_self (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), (periodizedCoupling (L + 1) J (i - j) : ℂ)
        * mFourier (torusToLattice L (i - j)) x)
      = ((couplingFourier J x : ℝ) : ℂ) := by
  rw [ofReal_couplingFourier heven, tsum_mul_mFourier_eq_sum_periodizedCoupling hsum L hx]
  exact Fintype.sum_equiv (Equiv.subLeft i) _ _ fun j ↦ rfl

/-- Real-part form of `sum_periodizedCoupling_mul_mFourier_sub_self`. -/
theorem sum_periodizedCoupling_mul_re_mFourier_sub_self (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J (i - j)
        * (mFourier (torusToLattice L (i - j)) x).re)
      = couplingFourier J x := by
  have h := congrArg Complex.re (sum_periodizedCoupling_mul_mFourier_sub_self hsum heven hx i)
  rw [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ ↦ (Complex.re_ofReal_mul _ _).symm

/-- Real-part form of `sum_periodizedCoupling_mul_mFourier_sub_left`. -/
theorem sum_periodizedCoupling_mul_re_mFourier_sub_left (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hx : Potential.intBoxLen L • x = 0)
    (i : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J (i - j)
        * (mFourier (torusToLattice L (j - i)) x).re)
      = couplingFourier J x := by
  have h := congrArg Complex.re (sum_periodizedCoupling_mul_mFourier_sub_left hsum heven hx i)
  rw [Complex.re_sum, Complex.ofReal_re] at h
  rw [← h]
  exact Finset.sum_congr rfl fun j _ ↦ (Complex.re_ofReal_mul _ _).symm

/-- `|z^i - z^j|² = 2 - Re(z^{i-j}) - Re(z^{j-i})` for `z ∈ G_Λ`. -/
private lemma norm_sq_mFourier_sub (hx : Potential.intBoxLen L • x = 0)
    (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    ‖mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x‖ ^ 2
      = 2 - (mFourier (torusToLattice L (i - j)) x).re
        - (mFourier (torusToLattice L (j - i)) x).re := by
  have hexp : (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x)
      * conj (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x)
      = 2 - mFourier (torusToLattice L (i - j)) x - mFourier (torusToLattice L (j - i)) x := by
    rw [map_sub, show (mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x)
          * (conj (mFourier (torusToLattice L i) x) - conj (mFourier (torusToLattice L j) x))
        = mFourier (torusToLattice L i) x * conj (mFourier (torusToLattice L i) x)
          + mFourier (torusToLattice L j) x * conj (mFourier (torusToLattice L j) x)
          - mFourier (torusToLattice L i) x * conj (mFourier (torusToLattice L j) x)
          - mFourier (torusToLattice L j) x * conj (mFourier (torusToLattice L i) x) from by ring,
      mFourier_mul_conj_self, mFourier_mul_conj_self,
      mFourier_torusToLattice_mul_conj hx i j, mFourier_torusToLattice_mul_conj hx j i]
    ring
  have hre := congrArg Complex.re hexp
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at hre
  rw [hre]
  simp

/-- **Georgii's identity for the right-hand side of (20.14)**:
`½ ∑_{i,j ∈ Λ} J_Λ(i-j)|z^i - z^j|² = |Λ|(Ĵ(1) - Ĵ(z))`. -/
theorem sum_periodizedCoupling_mul_norm_sq_sub (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hx : Potential.intBoxLen L • x = 0) :
    (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        periodizedCoupling (L + 1) J (i - j)
          * ‖mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x‖ ^ 2)
      = 2 * (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ)
        * (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) := by
  classical
  have hrow : ∀ i : Fin (d + 1) → ZMod (2 * (L + 1)),
      (∑ j : Fin (d + 1) → ZMod (2 * (L + 1)), periodizedCoupling (L + 1) J (i - j)
          * ‖mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x‖ ^ 2)
        = 2 * (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) := by
    intro i
    have hpt : ∀ j : Fin (d + 1) → ZMod (2 * (L + 1)),
        periodizedCoupling (L + 1) J (i - j)
            * ‖mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x‖ ^ 2
          = 2 * periodizedCoupling (L + 1) J (i - j)
            - periodizedCoupling (L + 1) J (i - j)
              * (mFourier (torusToLattice L (i - j)) x).re
            - periodizedCoupling (L + 1) J (i - j)
              * (mFourier (torusToLattice L (j - i)) x).re := by
      intro j
      rw [norm_sq_mFourier_sub hx]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, sum_periodizedCoupling_sub hsum i,
      sum_periodizedCoupling_mul_re_mFourier_sub_self hsum heven hx i,
      sum_periodizedCoupling_mul_re_mFourier_sub_left hsum heven hx i, ← couplingFourier_zero]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

private lemma dotProduct_self_smul_single (c : ℝ) (l : Fin n) :
    (c • Pi.single l (1 : ℝ)) ⬝ᵥ (c • Pi.single l (1 : ℝ)) = c ^ 2 := by
  rw [dotProduct_smul_single, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  ring

/-- **The right-hand side of Georgii (20.14), summed over the real and imaginary shifts**:
`2 B(ζ) + 2 B(η) = |Λ|(Ĵ(1) - Ĵ(z))`. -/
theorem heisenbergShiftEnergy_fourierShift_add (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hx : Potential.intBoxLen L • x = 0) (l : Fin n) :
    heisenbergShiftEnergy (L + 1) n J (fourierShiftRe L n l x)
        + heisenbergShiftEnergy (L + 1) n J (fourierShiftIm L n l x)
      = (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ)
        * (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) / 2 := by
  classical
  have hcombine : heisenbergShiftEnergy (L + 1) n J (fourierShiftRe L n l x)
        + heisenbergShiftEnergy (L + 1) n J (fourierShiftIm L n l x)
      = (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
          periodizedCoupling (L + 1) J (i - j)
            * ‖mFourier (torusToLattice L i) x - mFourier (torusToLattice L j) x‖ ^ 2) / 4 := by
    rw [heisenbergShiftEnergy, heisenbergShiftEnergy, ← add_div]
    refine congrArg (· / 4) ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [fourierShift_sub_re, fourierShift_sub_im, dotProduct_self_smul_single,
      dotProduct_self_smul_single, ← mul_add, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [hcombine, sum_periodizedCoupling_mul_norm_sq_sub hsum heven hx]
  ring

/-! #### Proposition (20.12) -/

variable [IsFiniteMeasure ν]

/-- **Georgii, Proposition (20.12), in the division-free form**:

`(Ĵ(1) - Ĵ(z))² C_Λ^Φ(z) ≤ N (Ĵ(1) - Ĵ(z))`  for `z ∈ G_Λ`.

Georgii's (20.14) at the real and imaginary shifts `ζ = (Re(z^i)e_ℓ)`, `η = (Im(z^i)e_ℓ)`,
summed over `ℓ`, together with `|Λ| C_Λ^Φ(z) = ∑_ℓ °γ_Λ^Φ(|∑_i σ_{i,ℓ} z^i|²)`
(`card_mul_correlationFourier_eq_sum_integral`) and the two identities
`sq_add_sq_heisenbergShiftPairing` and `heisenbergShiftEnergy_fourierShift_add`. -/
theorem sq_mul_correlationFourier_le (hν : ν ≠ 0) (hexp : HasExpSqMoments ν) (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (hdom : IsGaussianDominating (L + 1) n J ν) (hx : Potential.intBoxLen L • x = 0) :
    (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) ^ 2
        * correlationFourier L n J ν x
      ≤ (n : ℝ) * (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) := by
  classical
  set D := couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x with hD
  set M := (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact_mod_cast Fintype.card_pos_iff.2 ⟨0⟩
  set μ := heisenbergPeriodicGibbsDist (L + 1) n J ν with hμ
  -- the bound for a single coordinate `ℓ`
  have hkey : ∀ l : Fin n, D ^ 2 * (∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2 ∂μ) ≤ M * D := by
    intro l
    have h1 := integral_sq_heisenbergShiftPairing_le (N := L + 1) hν hexp hsum hdom
      (fourierShiftRe L n l x)
    have h2 := integral_sq_heisenbergShiftPairing_le (N := L + 1) hν hexp hsum hdom
      (fourierShiftIm L n l x)
    have hi1 := integrable_sq_heisenbergShiftPairing (N := L + 1) hν hexp hsum hdom
      (fourierShiftRe L n l x)
    have hi2 := integrable_sq_heisenbergShiftPairing (N := L + 1) hν hexp hsum hdom
      (fourierShiftIm L n l x)
    have hE := heisenbergShiftEnergy_fourierShift_add (J := J) hsum heven hx l
    calc D ^ 2 * (∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
              ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2 ∂μ)
        = ∫ ω, (heisenbergShiftPairing (L + 1) n J (fourierShiftRe L n l x) ω ^ 2
            + heisenbergShiftPairing (L + 1) n J (fourierShiftIm L n l x) ω ^ 2) ∂μ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (.of_forall fun ω ↦
            (sq_add_sq_heisenbergShiftPairing hsum heven hx l ω).symm)
      _ = (∫ ω, heisenbergShiftPairing (L + 1) n J (fourierShiftRe L n l x) ω ^ 2 ∂μ)
            + ∫ ω, heisenbergShiftPairing (L + 1) n J (fourierShiftIm L n l x) ω ^ 2 ∂μ :=
          integral_add hi1 hi2
      _ ≤ 2 * heisenbergShiftEnergy (L + 1) n J (fourierShiftRe L n l x)
            + 2 * heisenbergShiftEnergy (L + 1) n J (fourierShiftIm L n l x) := add_le_add h1 h2
      _ = M * D := by rw [← mul_add, hE]; ring
  -- sum over the coordinates
  have hCM := card_mul_correlationFourier_eq_sum_integral (L := L) (n := n) (J := J) (ν := ν)
    hν hexp hsum heven hnd hx
  have hsumℓ : D ^ 2 * (M * correlationFourier L n J ν x) ≤ (n : ℝ) * (M * D) := by
    rw [← hM] at hCM
    rw [hCM, Finset.mul_sum]
    calc (∑ l : Fin n, D ^ 2 * ∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2 ∂μ)
        ≤ ∑ _l : Fin n, M * D := Finset.sum_le_sum fun l _ ↦ hkey l
      _ = (n : ℝ) * (M * D) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcancel : M * (D ^ 2 * correlationFourier L n J ν x) ≤ M * ((n : ℝ) * D) := by
    calc M * (D ^ 2 * correlationFourier L n J ν x)
        = D ^ 2 * (M * correlationFourier L n J ν x) := by ring
      _ ≤ (n : ℝ) * (M * D) := hsumℓ
      _ = M * ((n : ℝ) * D) := by ring
  exact le_of_mul_le_mul_left hcancel hMpos

/-- **A by-product of the infrared bound**: on `G_Λ` the transform of the coupling is maximal at
the neutral element, `Ĵ(z) ≤ Ĵ(1)`.  Georgii derives this from the nonnegativity and
irreducibility of `J` in Comment (20.17)(1); here it follows from (20.12) itself. -/
theorem couplingFourier_le_couplingFourier_zero (hn : 0 < n) (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) (hdom : IsGaussianDominating (L + 1) n J ν)
    (hx : Potential.intBoxLen L • x = 0) :
    couplingFourier J x ≤ couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) := by
  by_contra hlt
  push Not at hlt
  set D := couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x with hD
  have hDneg : D < 0 := by rw [hD]; linarith
  have hkey := sq_mul_correlationFourier_le hν hexp hsum heven hnd hdom hx
  have hC : 0 ≤ correlationFourier L n J ν x := correlationFourier_nonneg hν hexp hsum heven hnd hx
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  nlinarith [hkey, hC, hDneg, hn', sq_nonneg D]

/-- **Georgii, Proposition (20.12): the infrared bound.**

`0 ≤ C_Λ^Φ(z) ≤ N (Ĵ(1) - Ĵ(z))⁻¹`  for every `z ∈ G_Λ` with `Ĵ(z) ≠ Ĵ(1)`.

The lower bound is `correlationFourier_nonneg`; the upper bound is proved here from Lemma (20.13)
through (20.14). -/
theorem correlationFourier_le (hn : 0 < n) (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (hdom : IsGaussianDominating (L + 1) n J ν) (hx : Potential.intBoxLen L • x = 0)
    (hne : couplingFourier J x ≠ couplingFourier J (0 : UnitAddTorus (Fin (d + 1)))) :
    correlationFourier L n J ν x
      ≤ (n : ℝ) / (couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x) := by
  have hle := couplingFourier_le_couplingFourier_zero hn hν hexp hsum heven hnd hdom hx
  have hDpos : 0 < couplingFourier J (0 : UnitAddTorus (Fin (d + 1))) - couplingFourier J x :=
    sub_pos.2 (lt_of_le_of_ne hle hne)
  have hkey := sq_mul_correlationFourier_le hν hexp hsum heven hnd hdom hx
  rw [le_div_iff₀ hDpos]
  nlinarith [hkey, hDpos]

end Georgii2012

end MeasureTheory.GibbsMeasure

end

end

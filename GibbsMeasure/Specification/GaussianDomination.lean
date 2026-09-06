/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.InfraredBound

/-!
# Georgii, Lemma (20.13): Gaussian domination

Georgii's Lemma (20.13) is the inequality

`°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) ≤ °γ_Λ^Φ(f_Λ^Φ(0, ·)) = 1`,   `ζ ∈ (ℝ^N)^Λ`,

for the function

`f_Λ^Φ(ζ, ω) = exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j)(ω_i - ω_j)·(ζ_i - ζ_j)
                    - ¼ ∑_{i,j ∈ Λ} J_Λ(i-j)|ζ_i - ζ_j|²]`.

It is the only place in Chapter 20 where reflection positivity is used in an essential way, and
it is the analytic input to the infrared bound (20.12).

## Georgii's proof, and how it is organised here

Write `W(ω) = -¼ ∑_{i,j ∈ Λ} J_Λ(i-j)|ω_i - ω_j|²` (`heisenbergDiffExponent`) for the exponent of
Georgii's `g`, and `λ̃(dx) = exp[|x|² Ĵ(1)/2] λ(dx)` (`expSqTilted`) for his tilted a priori
measure, where `Ĵ(1) = ∑_{m ∈ Λ} J_Λ(m)`.  Then:

* **the algebra.**  `heisenbergExponent_eq_diffExponent_add` is the identity
  `½ ∑_{i,j} J_Λ(i-j) σ_i·σ_j = W(σ) + ½ Ĵ(1) ∑_i |σ_i|²`, whence
  `heisenbergPeriodicGibbs_eq_withDensity` : `°γ_Λ^Φ` (unnormalised) is `λ̃^Λ` with the density
  `e^W`.  `heisenbergDiffExponent_sub` is `W(ω - ζ) = W(ω) + log f_Λ^Φ(ζ, ω)` — the "short
  calculation" at the beginning of Georgii's proof — and
  `heisenbergShiftExponent_of_const` is `f_Λ^Φ(ζ, ·) = 1` for a *constant* `ζ`.
* **the reduction.**  `lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs` :
  `°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) = λ̃^Λ(e^{W(· - ζ)}) / λ̃^Λ(e^W)`.  Georgii's `λ̃^Λ(g ∘ τ_ζ)/λ̃^Λ(g)`.  So
  (20.13) *is* the statement `λ̃^Λ(e^{W(· - ζ)}) ≤ λ̃^Λ(e^W)`, an inequality about the a priori
  measure alone; that is `IsGaussianDominating`.
* **the chessboard step.**  `isGaussianDominating_of_withDensity` proves it when `λ` — hence
  `λ̃` — has an everywhere positive, finite density relative to Lebesgue measure.  This is
  Georgii's first case: the translate of `λ̃^Λ` then has the *product* density
  `∏_{i ∈ Λ} r(σ_i + ζ_i)/r(σ_i)` relative to `λ̃^Λ`, Theorem (17.29)
  (`isReflectionPositive_heisenbergPeriodicGibbsDist_of_isNonnegDefiniteAt`) and the chessboard
  estimate (17.11) (`abs_integral_prod_pow_le_pi`) bound its `°γ_Λ^Φ`-average by
  `∏_{j ∈ Λ} °γ_Λ^Φ(∏_i r(σ_i + ζ_j)/r(σ_i))^{1/|Λ|}`, and each factor is `1` because it is the
  average of `f_Λ^Φ(ζ^j, ·)` at the constant configuration `ζ^j`.  The ratios are not bounded, so
  the chessboard estimate is applied to the truncations `min(·, M)` and `M ↑ ∞` afterwards by
  monotone convergence — Georgii's statement of (17.11) carries no boundedness hypothesis, ours
  does.
* **(20.13)** `lintegral_heisenbergShiftFactor_le_one` and
  `integral_heisenbergShiftFactor_le_one` are the conclusion, for any `λ` for which
  `IsGaussianDominating` holds.

## What is *not* proved here

Georgii's remaining three approximation steps, which remove the hypothesis that `λ` be
absolutely continuous: `λ` absolutely continuous on a compact ball, then an arbitrary finite
measure on a ball (a weak limit of absolutely continuous ones), then the ball increasing to
`ℝ^N`.  What is missing is exactly `IsGaussianDominating` for a general finite `λ` satisfying
(20.3); everything downstream of (20.13) in this file and in
`GibbsMeasure.Specification.InfraredBoundTheorem` takes `IsGaussianDominating` as its hypothesis
and therefore generalises for free.  In particular the surface measure on a sphere — the
Heisenberg model proper — is *not* covered, while Georgii's other running example
`λ(dx) = exp[-c|x|^{2+ε}] dx` is.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d N n : ℕ} [NeZero N] {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-! ### The exponent of Georgii's `g`, and the shift factor `f_Λ^Φ` -/

section Algebra

variable (N n J) in
/-- **The exponent of Georgii's `g` in the proof of Lemma (20.13)**,

`W(ω) = -¼ ∑_{i, j ∈ Λ} J_Λ(i - j) |ω_i - ω_j|²`.

Together with the one-site Gaussian weights `exp[|σ_i|² Ĵ(1)/2]` it makes up the exponent
(17.24) of the Gibbs distribution with periodic boundary condition
(`heisenbergExponent_eq_diffExponent_add`).  Unlike (17.24) it is invariant under a *global*
shift of the configuration (`heisenbergDiffExponent_sub_const`), which is what makes the
right-hand sides of the chessboard estimate equal to `1`. -/
def heisenbergDiffExponent (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  -(∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ω i - ω j))) / 4

variable (N n J) in
/-- **The linear form in Georgii's `f_Λ^Φ(ζ, ·)` of (20.13)**,

`½ ∑_{i,j ∈ Λ} J_Λ(i-j)(ω_i - ω_j)·(ζ_i - ζ_j)`.

It is linear in `ζ` (`heisenbergShiftPairing_smul`); its second moment under `°γ_Λ^Φ` is what
(20.14) bounds. -/
def heisenbergShiftPairing (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  (∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ζ i - ζ j))) / 2

variable (N n J) in
/-- **The quadratic form in Georgii's `f_Λ^Φ(ζ, ·)` of (20.13)**,

`¼ ∑_{i,j ∈ Λ} J_Λ(i-j)|ζ_i - ζ_j|²`.

It is quadratic in `ζ` (`heisenbergShiftEnergy_smul`) and is the bound in (20.14). -/
def heisenbergShiftEnergy (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  (∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ζ i - ζ j) ⬝ᵥ (ζ i - ζ j))) / 4

variable (N n J) in
/-- **The exponent of Georgii's `f_Λ^Φ(ζ, ·)` of (20.13)**,

`½ ∑_{i,j ∈ Λ} J_Λ(i-j)(ω_i - ω_j)·(ζ_i - ζ_j) - ¼ ∑_{i,j ∈ Λ} J_Λ(i-j)|ζ_i - ζ_j|²`. -/
def heisenbergShiftExponent (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  heisenbergShiftPairing N n J ζ ω - heisenbergShiftEnergy N n J ζ

/-- **`f_Λ^Φ(tζ, ω) = exp[t A(ζ, ω) - t² B(ζ)]`**: the shift factor along a ray through `ζ`.
This is what turns Lemma (20.13) into a sub-Gaussian bound for `A(ζ, ·)`, and thereby into
(20.14). -/
theorem heisenbergShiftPairing_smul (t : ℝ) (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftPairing N n J (t • ζ) ω = t * heisenbergShiftPairing N n J ζ ω := by
  have h : (∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ ((t • ζ) i - (t • ζ) j)))
      = t * ∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ζ i - ζ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (t • ζ) i - (t • ζ) j = t • (ζ i - ζ j) from by simp [smul_sub],
      dotProduct_smul, smul_eq_mul]
    ring
  rw [heisenbergShiftPairing, heisenbergShiftPairing, h, mul_div_assoc]

theorem heisenbergShiftEnergy_smul (t : ℝ) (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftEnergy N n J (t • ζ) = t ^ 2 * heisenbergShiftEnergy N n J ζ := by
  have h : (∑ i, ∑ j, periodizedCoupling N J (i - j)
        * (((t • ζ) i - (t • ζ) j) ⬝ᵥ ((t • ζ) i - (t • ζ) j)))
      = t ^ 2 * ∑ i, ∑ j, periodizedCoupling N J (i - j) * ((ζ i - ζ j) ⬝ᵥ (ζ i - ζ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [show (t • ζ) i - (t • ζ) j = t • (ζ i - ζ j) from by simp [smul_sub],
      dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  rw [heisenbergShiftEnergy, heisenbergShiftEnergy, h, mul_div_assoc]

theorem heisenbergShiftExponent_smul (t : ℝ) (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftExponent N n J (t • ζ) ω
      = t * heisenbergShiftPairing N n J ζ ω - t ^ 2 * heisenbergShiftEnergy N n J ζ := by
  rw [heisenbergShiftExponent, heisenbergShiftPairing_smul, heisenbergShiftEnergy_smul]

variable (N n J) in
/-- **Georgii's `f_Λ^Φ(ζ, ω)` of (20.13).** -/
def heisenbergShiftFactor (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  Real.exp (heisenbergShiftExponent N n J ζ ω)

@[simp] lemma heisenbergShiftFactor_pos (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    0 < heisenbergShiftFactor N n J ζ ω := Real.exp_pos _

/-- `|u - v|² = |u|² - 2 u·v + |v|²` for the dot product on `ℝ^n`.  Intended home:
`GibbsMeasure/Mathlib/LinearAlgebra/Matrix/DotProductReal.lean` (as `Matrix.sub_dotProduct_sub`).
-/
private lemma dotProduct_sub_sub (u v : Fin n → ℝ) :
    (u - v) ⬝ᵥ (u - v) = u ⬝ᵥ u - 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v u]
  ring

/-- **The exponent (17.24) split off from `W`.**  `½ ∑_{i,j} J_Λ(i-j) σ_i·σ_j
= W(σ) + ½ (∑_{m ∈ Λ} J_Λ(m)) ∑_i |σ_i|²`; the coefficient is Georgii's `Ĵ(1)`, cf.
`sum_periodizedCoupling`. -/
theorem heisenbergExponent_eq_diffExponent_add (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergExponent N n J ω
      = heisenbergDiffExponent N n J ω
        + (∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) / 2 * ∑ i, (ω i ⬝ᵥ ω i) := by
  classical
  have hrow : ∀ i : Fin d → ZMod (2 * N),
      (∑ j : Fin d → ZMod (2 * N), periodizedCoupling N J (i - j))
        = ∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m :=
    fun i ↦ Equiv.sum_comp (Equiv.subLeft i) fun m ↦ periodizedCoupling N J m
  have hcol : ∀ j : Fin d → ZMod (2 * N),
      (∑ i : Fin d → ZMod (2 * N), periodizedCoupling N J (i - j))
        = ∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m :=
    fun j ↦ Equiv.sum_comp (Equiv.subRight j) fun m ↦ periodizedCoupling N J m
  have hexpand : ∀ i j : Fin d → ZMod (2 * N),
      periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ω i - ω j))
        = periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω i)
          + periodizedCoupling N J (i - j) * (ω j ⬝ᵥ ω j)
          - 2 * (periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)) := by
    intro i j
    rw [dotProduct_sub_sub]
    ring
  -- the three pieces of the expanded double sum
  have hA : (∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
        periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω i))
      = (∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) * ∑ i, (ω i ⬝ᵥ ω i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Finset.sum_mul, hrow i]
  have hB : (∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
        periodizedCoupling N J (i - j) * (ω j ⬝ᵥ ω j))
      = (∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) * ∑ j, (ω j ⬝ᵥ ω j) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [← Finset.sum_mul, hcol j]
  rw [heisenbergDiffExponent, heisenbergExponent]
  rw [show (∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
      periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ω i - ω j)))
      = ((∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω i))
          + ∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            periodizedCoupling N J (i - j) * (ω j ⬝ᵥ ω j))
        - 2 * ∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            (periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)) from ?_]
  · rw [hA, hB]; ring
  · rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hexpand i j

/-- **`W` is invariant under a global shift of the configuration**: it only sees the differences
`ω_i - ω_j`.  This is why the right-hand side of the chessboard estimate in Georgii's proof of
(20.13) consists of `1`s. -/
theorem heisenbergDiffExponent_sub_const (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ))
    (c : Fin n → ℝ) :
    heisenbergDiffExponent N n J (fun i ↦ ω i - c) = heisenbergDiffExponent N n J ω := by
  refine congrArg (fun x ↦ -x / 4)
    (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  simp only [sub_sub_sub_cancel_right]

/-- **Georgii's "short calculation"**: `W(ω - ζ) = W(ω) + log f_Λ^Φ(ζ, ω)`, equivalently
`g(τ_ζ ω) = g(ω) f_Λ^Φ(ζ, ω)`. -/
theorem heisenbergDiffExponent_sub (ζ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergDiffExponent N n J (ω - ζ)
      = heisenbergDiffExponent N n J ω + heisenbergShiftExponent N n J ζ ω := by
  classical
  have hexpand : ∀ i j : Fin d → ZMod (2 * N),
      periodizedCoupling N J (i - j) * (((ω - ζ) i - (ω - ζ) j) ⬝ᵥ ((ω - ζ) i - (ω - ζ) j))
        = periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ω i - ω j))
          - 2 * (periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ζ i - ζ j)))
          + periodizedCoupling N J (i - j) * ((ζ i - ζ j) ⬝ᵥ (ζ i - ζ j)) := by
    intro i j
    have hij : (ω - ζ) i - (ω - ζ) j = (ω i - ω j) - (ζ i - ζ j) := by
      simp only [Pi.sub_apply]; abel
    rw [hij, dotProduct_sub_sub]
    ring
  rw [heisenbergDiffExponent, heisenbergDiffExponent, heisenbergShiftExponent,
    heisenbergShiftPairing, heisenbergShiftEnergy]
  rw [show (∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
      periodizedCoupling N J (i - j) * (((ω - ζ) i - (ω - ζ) j) ⬝ᵥ ((ω - ζ) i - (ω - ζ) j)))
      = ((∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ω i - ω j)))
          - 2 * ∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            (periodizedCoupling N J (i - j) * ((ω i - ω j) ⬝ᵥ (ζ i - ζ j))))
        + ∑ i : Fin d → ZMod (2 * N), ∑ j : Fin d → ZMod (2 * N),
            periodizedCoupling N J (i - j) * ((ζ i - ζ j) ⬝ᵥ (ζ i - ζ j)) from ?_]
  · ring
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hexpand i j

/-- **`f_Λ^Φ(ζ^j, ·) = 1` for a constant `ζ^j`**, the last step of Georgii's proof of (20.13). -/
@[simp] theorem heisenbergShiftExponent_of_const (c : Fin n → ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftExponent N n J (fun _ ↦ c) ω = 0 := by
  simp [heisenbergShiftExponent, heisenbergShiftPairing, heisenbergShiftEnergy]

@[simp] theorem heisenbergShiftFactor_of_const (c : Fin n → ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftFactor N n J (fun _ ↦ c) ω = 1 := by
  simp [heisenbergShiftFactor]

lemma measurable_heisenbergDiffExponent :
    Measurable (heisenbergDiffExponent N n J (d := d)) := by
  refine Measurable.div_const (Measurable.neg ?_) _
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    Measurable.const_mul (((measurable_pi_apply i).sub (measurable_pi_apply j)).dotProduct
      ((measurable_pi_apply i).sub (measurable_pi_apply j))) _

lemma measurable_heisenbergShiftPairing (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Measurable (heisenbergShiftPairing N n J ζ) := by
  refine Measurable.div_const ?_ _
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    Measurable.const_mul (((measurable_pi_apply i).sub (measurable_pi_apply j)).dotProduct
      measurable_const) _

lemma measurable_heisenbergShiftExponent (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Measurable (heisenbergShiftExponent N n J ζ) :=
  (measurable_heisenbergShiftPairing ζ).sub_const _

lemma measurable_heisenbergShiftFactor (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Measurable (heisenbergShiftFactor N n J ζ) :=
  (measurable_heisenbergShiftExponent ζ).exp

end Algebra

/-! ### Georgii's `λ̃`, and `°γ_Λ^Φ` as `λ̃^Λ` with the density `e^W` -/

section Tilt

/-- **Georgii's tilted a priori measure `λ̃(dx) = exp[a |x|²] λ(dx)`** from the proof of Lemma
(20.13), at a general tilt `a`; Georgii uses `a = Ĵ(1)/2`. -/
def expSqTilted (a : ℝ) (ν : Measure (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  ν.withDensity fun x ↦ ENNReal.ofReal (Real.exp (a * (x ⬝ᵥ x)))

lemma measurable_expSqDensity (a : ℝ) :
    Measurable fun x : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (a * (x ⬝ᵥ x))) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.measurable.comp ((measurable_id.dotProduct measurable_id).const_mul _))

/-- `λ̃` is finite: this is exactly Georgii's (20.3) at the single exponent `a`. -/
lemma isFiniteMeasure_expSqTilted {a : ℝ} [IsFiniteMeasure ν] (hexp : HasExpSqMoments ν) :
    IsFiniteMeasure (expSqTilted a ν) := by
  refine isFiniteMeasure_withDensity ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hexp a)
    (Filter.Eventually.of_forall fun _ ↦ (Real.exp_nonneg _))]
  exact ENNReal.ofReal_ne_top

/-- The tilt that turns the exponent (17.24) into `W`: Georgii's `Ĵ(1)/2`, with `Ĵ(1)` the sum
`∑_{m ∈ Λ} J_Λ(m)` of the periodised coupling (equal to `∑_{i ∈ ℤ^d} J(i)` when `J` is summable,
`sum_periodizedCoupling`). -/
def heisenbergTilt (N : ℕ) [NeZero N] (J : (Fin d → ℤ) → ℝ) : ℝ :=
  (∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) / 2

/-- **Georgii's `°γ_Λ^Φ = g · λ̃^Λ`.**  The unnormalised Gibbs distribution (17.24) is the product
of the tilted a priori measures with the density `g = e^W`. -/
theorem heisenbergPeriodicGibbs_eq_withDensity [IsFiniteMeasure ν] (hexp : HasExpSqMoments ν) :
    heisenbergPeriodicGibbs N n J ν
      = (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν).withDensity
          (fun ω ↦ ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))) := by
  classical
  have _hfin : IsFiniteMeasure (ν.withDensity fun x ↦
      ENNReal.ofReal (Real.exp (heisenbergTilt N J * (x ⬝ᵥ x)))) :=
    isFiniteMeasure_expSqTilted (a := heisenbergTilt N J) hexp
  have hprod : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ∏ i, ENNReal.ofReal (Real.exp (heisenbergTilt N J * (ω i ⬝ᵥ ω i))) :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_expSqDensity _).comp (measurable_pi_apply i)
  have hW : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω)) :=
    measurable_heisenbergDiffExponent.exp.ennreal_ofReal
  have hpi : (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν)
      = (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν).withDensity
          (fun ω ↦ ∏ i, ENNReal.ofReal (Real.exp (heisenbergTilt N J * (ω i ⬝ᵥ ω i)))) :=
    Measure.pi_withDensity (fun _ : Fin d → ZMod (2 * N) ↦ ν)
      (r := fun _ ↦ fun x ↦ ENNReal.ofReal (Real.exp (heisenbergTilt N J * (x ⬝ᵥ x))))
      (fun _ ↦ measurable_expSqDensity _)
  have hdens : (fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
        ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω)))
      = (fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
          ∏ i, ENNReal.ofReal (Real.exp (heisenbergTilt N J * (ω i ⬝ᵥ ω i))))
        * fun ω ↦ ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω)) := by
    funext ω
    rw [Pi.mul_apply, ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_nonneg _)),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ ↦ (Real.exp_nonneg _)),
      ← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
    have hsplit := heisenbergExponent_eq_diffExponent_add (N := N) (n := n) (J := J) ω
    simp only [heisenbergTilt]
    exact congrArg _ (congrArg _ (by linarith [hsplit]))
  rw [hpi, ← withDensity_mul _ hprod hW, ← hdens]
  rfl

end Tilt

/-! ### The reduction: `°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) = λ̃^Λ(e^{W(· - ζ)}) / λ̃^Λ(e^W)` -/

section Reduction

variable [IsFiniteMeasure ν]

/-- **Georgii's `°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) = λ̃^Λ(g ∘ τ_ζ)`** (before dividing by `λ̃^Λ(g)`): the "short
calculation" at the beginning of the proof of Lemma (20.13). -/
theorem lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs (hexp : HasExpSqMoments ν)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫⁻ ω, ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω) ∂(heisenbergPeriodicGibbs N n J ν))
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν) := by
  have hW : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω)) :=
    measurable_heisenbergDiffExponent.exp.ennreal_ofReal
  have hF : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω) :=
    (measurable_heisenbergShiftFactor ζ).ennreal_ofReal
  rw [heisenbergPeriodicGibbs_eq_withDensity hexp,
    lintegral_withDensity_eq_lintegral_mul _ hW hF]
  refine lintegral_congr fun ω ↦ ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _), heisenbergShiftFactor,
    ← Real.exp_add, ← heisenbergDiffExponent_sub]

/-- The mass of `°γ_Λ^Φ` is Georgii's `λ̃^Λ(g)`. -/
theorem heisenbergPeriodicGibbs_univ_eq_lintegral (hexp : HasExpSqMoments ν) :
    heisenbergPeriodicGibbs N n J ν univ
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν) := by
  have h := lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs (J := J) (ν := ν) hexp
    (fun _ : Fin d → ZMod (2 * N) ↦ (0 : Fin n → ℝ))
  simp only [heisenbergShiftFactor_of_const, ENNReal.ofReal_one, lintegral_one] at h
  rw [h]
  refine lintegral_congr fun ω ↦ ?_
  rw [show ω - (fun _ : Fin d → ZMod (2 * N) ↦ (0 : Fin n → ℝ)) = ω from by funext i; simp]

variable (N n J ν) in
/-- **Georgii's Lemma (20.13), as an inequality about the a priori measure alone**:

`λ̃^Λ(g ∘ τ_ζ) ≤ λ̃^Λ(g)` for every `ζ ∈ (ℝ^N)^Λ`,

where `λ̃(dx) = exp[|x|² Ĵ(1)/2] λ(dx)` and `g = exp W`.  By
`lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs` this is *equivalent* to Georgii's
`°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) ≤ 1`, and it no longer mentions the Gibbs distribution.  It is what
`isGaussianDominating_of_withDensity` proves for an absolutely continuous `λ`, and what Georgii's
three approximation steps extend to a general `λ`. -/
def IsGaussianDominating : Prop :=
  ∀ ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
    (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν))
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν)

/-- **Georgii, Lemma (20.13).**  `°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) ≤ °γ_Λ^Φ(f_Λ^Φ(0, ·)) = 1`. -/
theorem lintegral_heisenbergShiftFactor_le_one (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫⁻ ω, ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω)
        ∂(heisenbergPeriodicGibbsDist N n J ν)) ≤ 1 := by
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d) (J := J) hexp hsum
  have hfin : IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hZ0 : heisenbergPeriodicGibbs N n J ν univ ≠ 0 := (heisenbergPeriodicGibbs_univ_pos hν).ne'
  have hZtop : heisenbergPeriodicGibbs N n J ν univ ≠ ∞ := measure_ne_top _ _
  rw [heisenbergPeriodicGibbsDist, lintegral_smul_measure,
    lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs hexp ζ]
  calc (heisenbergPeriodicGibbs N n J ν univ)⁻¹
        * ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
            ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν)
      ≤ (heisenbergPeriodicGibbs N n J ν univ)⁻¹
          * ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
            ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν) :=
        mul_le_mul' le_rfl (hdom ζ)
    _ = 1 := by
        rw [← heisenbergPeriodicGibbs_univ_eq_lintegral hexp]
        exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- **Georgii, Lemma (20.13)** in Bochner form, together with the integrability that makes it
meaningful. -/
theorem integrable_heisenbergShiftFactor (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Integrable (heisenbergShiftFactor N n J ζ) (heisenbergPeriodicGibbsDist N n J ν) := by
  refine ⟨(measurable_heisenbergShiftFactor ζ).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun _ ↦ (heisenbergShiftFactor_pos _ _).le)]
  exact lt_of_le_of_lt (lintegral_heisenbergShiftFactor_le_one hν hexp hsum hdom ζ)
    ENNReal.one_lt_top

/-- **Georgii, Lemma (20.13).** -/
theorem integral_heisenbergShiftFactor_le_one (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (hdom : IsGaussianDominating N n J ν)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫ ω, heisenbergShiftFactor N n J ζ ω ∂(heisenbergPeriodicGibbsDist N n J ν)) ≤ 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (.of_forall fun _ ↦ (heisenbergShiftFactor_pos _ _).le)
    (measurable_heisenbergShiftFactor ζ).aestronglyMeasurable]
  have h := lintegral_heisenbergShiftFactor_le_one hν hexp hsum hdom ζ
  calc (∫⁻ ω, ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω)
        ∂(heisenbergPeriodicGibbsDist N n J ν)).toReal
      ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h
    _ = 1 := ENNReal.toReal_one

/-- **`IsGaussianDominating` is exactly Georgii's Lemma (20.13).**  Both are the same inequality
divided, or not, by the partition function `°Z_Λ^Φ = λ̃^Λ(g)`. -/
theorem isGaussianDominating_iff (hν : ν ≠ 0) (hexp : HasExpSqMoments ν) (hsum : Summable J) :
    IsGaussianDominating N n J ν
      ↔ ∀ ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
          (∫⁻ ω, ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω)
            ∂(heisenbergPeriodicGibbsDist N n J ν)) ≤ 1 := by
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d) (J := J) hexp hsum
  have hfin : IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hZ0 : heisenbergPeriodicGibbs N n J ν univ ≠ 0 := (heisenbergPeriodicGibbs_univ_pos hν).ne'
  have hZtop : heisenbergPeriodicGibbs N n J ν univ ≠ ∞ := measure_ne_top _ _
  refine ⟨fun hdom ζ ↦ lintegral_heisenbergShiftFactor_le_one hν hexp hsum hdom ζ, fun h ζ ↦ ?_⟩
  have hζ := h ζ
  rw [heisenbergPeriodicGibbsDist, lintegral_smul_measure,
    lintegral_heisenbergShiftFactor_heisenbergPeriodicGibbs hexp ζ] at hζ
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν))
      = heisenbergPeriodicGibbs N n J ν univ * ((heisenbergPeriodicGibbs N n J ν univ)⁻¹
          * ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
            ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]
    _ ≤ heisenbergPeriodicGibbs N n J ν univ * 1 := mul_le_mul' le_rfl hζ
    _ = heisenbergPeriodicGibbs N n J ν univ := mul_one _
    _ = _ := heisenbergPeriodicGibbs_univ_eq_lintegral hexp

end Reduction

/-! ### Georgii's first case: an absolutely continuous a priori measure -/

section Chessboard

/-- **Georgii, Theorem (17.11) for the reflections `r_k` of (17.5)**, for bounded functions:
`|μ(∏_i f_i ∘ σ_i)|^{|Λ|} ≤ ∏_j μ(∏_i f_j ∘ σ_i)`.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbs.lean`, next to `measure_apply_pow_card_le_siteEquiv`,
of which this is the function form (the involutions `τ^i` of (17.10) are trivial here). -/
theorem abs_integral_prod_pow_le_pi_siteEquiv {E : Type*} [MeasurableSpace E] {d N : ℕ}
    [NeZero N] {μ : Measure ((Fin (d + 1) → ZMod (2 * N)) → E)} [IsFiniteMeasure μ]
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ)
    (hrefl : ∀ k, MeasurePreserving (siteEquiv E (torusReflAt N k)).toFun μ μ)
    (hpos : ∀ k, IsReflectionPositive (torusPosAt N k) (siteEquiv E (torusReflAt N k)) μ)
    {f : (Fin (d + 1) → ZMod (2 * N)) → E → ℝ} (hf : ∀ i, Measurable (f i)) {C : ℝ}
    (hC : ∀ i x, |f i x| ≤ C) :
    |∫ ω, ∏ i, f i (ω i) ∂μ| ^ ((2 * N) ^ (d + 1)) ≤ ∏ j, ∫ ω, ∏ i, f j (ω i) ∂μ := by
  have h := abs_integral_prod_pow_le_pi (μ := μ) (τ := fun _ ↦ MeasurableEquiv.refl E)
    (fun _ _ ↦ rfl) hper (by simpa only [genReflectionAt_refl] using hrefl)
    (by simpa only [genReflectionAt_refl] using hpos) hf hC
  simpa only [tauPow_refl] using h

/-- **The `°γ_Λ^Φ`-average of the density of the translated `λ̃^Λ` is `λ̃^Λ(g ∘ τ_ζ)`.**

If `λ̃ = R · dx` with `0 < R < ∞`, the translate `τ_ζ(λ̃^Λ)` has the density
`∏_{i ∈ Λ} R(σ_i + ζ_i)/R(σ_i)` relative to `λ̃^Λ` (translation invariance of Lebesgue measure),
and Georgii's identity `°γ_Λ^Φ(f_Λ^Φ(ζ,·)) = λ̃^Λ(g ∘ τ_ζ)/λ̃^Λ(g)` then reads: the
(unnormalised) `°γ_Λ^Φ`-average of that density is `λ̃^Λ(g ∘ τ_ζ)`. -/
theorem lintegral_prod_div_heisenbergPeriodicGibbs {d N n : ℕ} [NeZero N]
    {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]
    (hexp : HasExpSqMoments ν) {R : (Fin n → ℝ) → ℝ≥0∞} (hRm : Measurable R)
    (hR0 : ∀ x, R x ≠ 0) (hRtop : ∀ x, R x ≠ ∞)
    (hνR : expSqTilted (heisenbergTilt N J) ν = volume.withDensity R)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫⁻ ω, ∏ i, R (ω i + ζ i) / R (ω i) ∂(heisenbergPeriodicGibbs N n J ν))
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν) := by
  classical
  have hfin : IsFiniteMeasure (expSqTilted (heisenbergTilt N J) ν) :=
    isFiniteMeasure_expSqTilted hexp
  have hfinR : IsFiniteMeasure ((volume : Measure (Fin n → ℝ)).withDensity R) := hνR ▸ hfin
  -- measurability of the pieces
  have hW : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω)) :=
    measurable_heisenbergDiffExponent.exp.ennreal_ofReal
  have hWζ : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ))) :=
    (measurable_heisenbergDiffExponent.comp (measurable_id.sub_const ζ)).exp.ennreal_ofReal
  have hshift : ∀ i : Fin d → ZMod (2 * N),
      Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ R (ω i + ζ i) := by
    intro i
    have h : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ ω i + ζ i := by
      fun_prop
    exact hRm.comp h
  have hplain : ∀ i : Fin d → ZMod (2 * N),
      Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ R (ω i) :=
    fun i ↦ hRm.comp (measurable_pi_apply i)
  have hratio : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ∏ i, R (ω i + ζ i) / R (ω i) :=
    Finset.measurable_prod _ fun i _ ↦ (hshift i).div (hplain i)
  have hRprod : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ ∏ i, R (ω i) :=
    Finset.measurable_prod _ fun i _ ↦ hplain i
  -- `λ̃^Λ` is Lebesgue measure on `(ℝ^N)^Λ` with the product density
  have hpi : (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν)
      = (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ (volume : Measure (Fin n → ℝ))).withDensity
          (fun ω ↦ ∏ i, R (ω i)) := by
    simp only [hνR]
    exact Measure.pi_withDensity (fun _ : Fin d → ZMod (2 * N) ↦ (volume : Measure (Fin n → ℝ)))
      (r := fun _ ↦ R) (fun _ ↦ hRm)
  -- the cancellation `R(x) · (R(y)/R(x)) = R(y)`
  have hcancel : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
      (∏ i, R (ω i)) * ((fun ω ↦ ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))) ω
          * ∏ i, R (ω i + ζ i) / R (ω i))
        = ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω)) * ∏ i, R (ω i + ζ i) := by
    intro ω
    rw [← mul_assoc, mul_comm (∏ i, R (ω i)), mul_assoc, ← Finset.prod_mul_distrib]
    exact congrArg _ (Finset.prod_congr rfl fun i _ ↦
      ENNReal.mul_div_cancel (hR0 (ω i)) (hRtop (ω i)))
  -- translation invariance of Lebesgue measure on `(ℝ^N)^Λ`
  have htrans : (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
          * ∏ i, R (ω i + ζ i)
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ (volume : Measure (Fin n → ℝ))))
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ))) * ∏ i, R (ω i)
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ (volume : Measure (Fin n → ℝ))) := by
    have h := lintegral_sub_right_eq_self
      (μ := (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ (volume : Measure (Fin n → ℝ))))
      (f := fun ω ↦ ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
        * ∏ i, R (ω i + ζ i)) ζ
    rw [← h]
    refine lintegral_congr fun ω ↦ ?_
    refine congrArg₂ _ rfl (Finset.prod_congr rfl fun i _ ↦ ?_)
    exact congrArg R (by simp)
  rw [heisenbergPeriodicGibbs_eq_withDensity hexp,
    lintegral_withDensity_eq_lintegral_mul _ hW hratio, hpi,
    lintegral_withDensity_eq_lintegral_mul _ hRprod (hW.mul hratio),
    lintegral_withDensity_eq_lintegral_mul _ hRprod hWζ]
  simp only [Pi.mul_apply]
  rw [lintegral_congr hcancel, htrans]
  exact lintegral_congr fun ω ↦ mul_comm _ _

/-- The `°γ_Λ^Φ`-average of the density belonging to a **constant** `ζ` is `1`: this is Georgii's
`f_Λ^Φ(ζ^j, ·) = 1`, the right-hand side of the chessboard estimate in the proof of (20.13). -/
theorem lintegral_prod_div_heisenbergPeriodicGibbsDist_const {d N n : ℕ} [NeZero N]
    {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) {R : (Fin n → ℝ) → ℝ≥0∞} (hRm : Measurable R)
    (hR0 : ∀ x, R x ≠ 0) (hRtop : ∀ x, R x ≠ ∞)
    (hνR : expSqTilted (heisenbergTilt N J) ν = volume.withDensity R) (c : Fin n → ℝ) :
    (∫⁻ ω, ∏ i, R (ω i + c) / R (ω i) ∂(heisenbergPeriodicGibbsDist N n J ν)) = 1 := by
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d) (J := J) hexp hsum
  have hfin : IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hZ0 : heisenbergPeriodicGibbs N n J ν univ ≠ 0 := (heisenbergPeriodicGibbs_univ_pos hν).ne'
  have hZtop : heisenbergPeriodicGibbs N n J ν univ ≠ ∞ := measure_ne_top _ _
  have hkey := lintegral_prod_div_heisenbergPeriodicGibbs hexp hRm hR0 hRtop hνR
    (fun _ : Fin d → ZMod (2 * N) ↦ c)
  rw [heisenbergPeriodicGibbsDist, lintegral_smul_measure, hkey]
  have hconst : (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J
        (ω - fun _ : Fin d → ZMod (2 * N) ↦ c)))
      ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν))
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν) := by
    refine lintegral_congr fun ω ↦ ?_
    exact congrArg _ (congrArg _ (heisenbergDiffExponent_sub_const ω c))
  rw [hconst, ← heisenbergPeriodicGibbs_univ_eq_lintegral hexp]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- **Georgii, Lemma (20.13), first case**: the Gaussian domination inequality holds whenever the
a priori measure `λ` is equivalent to Lebesgue measure, i.e. `λ = r · dx` with `0 < r < ∞`.

This is the only place in Chapter 20 where reflection positivity is used essentially.  The
translate of `λ̃^Λ` has the product density `∏_{i ∈ Λ} R(σ_i + ζ_i)/R(σ_i)` relative to `λ̃^Λ`
(`lintegral_prod_div_heisenbergPeriodicGibbs`), Theorem (17.29) makes `°γ_Λ^Φ` `r_k`-positive in
every direction, and the chessboard estimate (17.11) bounds the `°γ_Λ^Φ`-average of that product
by the geometric mean of the averages of the products belonging to the *constant* configurations
`ζ^j`, each of which is `1` (`lintegral_prod_div_heisenbergPeriodicGibbsDist_const`).  Since the
ratios are unbounded, (17.11) is applied to the truncations `min(·, M)` and `M ↑ ∞` afterwards by
monotone convergence. -/
theorem isGaussianDominating_of_withDensity {d N n : ℕ} [NeZero N]
    {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {R : (Fin n → ℝ) → ℝ≥0∞} (hRm : Measurable R)
    (hR0 : ∀ x, R x ≠ 0) (hRtop : ∀ x, R x ≠ ∞)
    (hνR : expSqTilted (heisenbergTilt N J) ν = volume.withDensity R) :
    IsGaussianDominating N n J ν := by
  classical
  intro ζ
  have hint := integrable_exp_heisenbergExponent (N := N) (d := d + 1) (J := J) hexp hsum
  have hprob : IsProbabilityMeasure (heisenbergPeriodicGibbsDist N n J ν) :=
    isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
  have hfin : IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hZ0 : heisenbergPeriodicGibbs N n J ν univ ≠ 0 := (heisenbergPeriodicGibbs_univ_pos hν).ne'
  have hZtop : heisenbergPeriodicGibbs N n J ν univ ≠ ∞ := measure_ne_top _ _
  set μ := heisenbergPeriodicGibbsDist N n J ν with hμ
  -- the one-site ratios and their truncations
  set F : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) → ℝ≥0∞ :=
    fun i x ↦ R (x + ζ i) / R x with hF
  have hFm : ∀ i, Measurable (F i) := by
    intro i
    have hadd : Measurable fun x : Fin n → ℝ ↦ x + ζ i := by fun_prop
    exact (hRm.comp hadd).div hRm
  have hFtop : ∀ i x, F i x ≠ ∞ := fun i x ↦ (ENNReal.div_lt_top (hRtop _) (hR0 _)).ne
  -- the right-hand sides of the chessboard estimate are `1`
  have hone : ∀ j : Fin (d + 1) → ZMod (2 * N), (∫⁻ ω, ∏ i, F j (ω i) ∂μ) = 1 := fun j ↦
    lintegral_prod_div_heisenbergPeriodicGibbsDist_const hν hexp hsum hRm hR0 hRtop hνR (ζ j)
  -- the truncated products
  set G : ℕ → ((Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ≥0∞ :=
    fun M ω ↦ ∏ i, min (F i (ω i)) (M : ℝ≥0∞) with hG
  have hGm : ∀ M, Measurable (G M) := fun M ↦
    Finset.measurable_prod _ fun i _ ↦ ((hFm i).comp (measurable_pi_apply i)).min measurable_const
  have hGmono : Monotone G := by
    intro M M' hMM' ω
    exact Finset.prod_le_prod' fun i _ ↦
      min_le_min le_rfl (by exact_mod_cast hMM')
  -- the Bochner and Lebesgue integrals of a product of nonnegative functions agree
  have hBL : ∀ h : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) → ℝ, (∀ i, Measurable (h i)) →
      (∀ i x, 0 ≤ h i x) → (∫ ω, ∏ i, h i (ω i) ∂μ)
        = (∫⁻ ω, ∏ i, ENNReal.ofReal (h i (ω i)) ∂μ).toReal := by
    intro h hhm hhnn
    have hmeas : Measurable fun ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) ↦
        ∏ i, h i (ω i) :=
      Finset.measurable_prod _ fun i _ ↦ (hhm i).comp (measurable_pi_apply i)
    rw [integral_eq_lintegral_of_nonneg_ae
      (.of_forall fun ω ↦ Finset.prod_nonneg fun i _ ↦ hhnn i (ω i)) hmeas.aestronglyMeasurable]
    exact congrArg ENNReal.toReal (lintegral_congr fun ω ↦
      ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hhnn i (ω i))
  -- each truncated integral is at most `1`, by the chessboard estimate
  have hGle : ∀ M : ℕ, (∫⁻ ω, G M ω ∂μ) ≤ 1 := by
    intro M
    set g : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) → ℝ :=
      fun i x ↦ (min (F i x) (M : ℝ≥0∞)).toReal with hg
    have hminlt : ∀ (i) (x : Fin n → ℝ), min (F i x) (M : ℝ≥0∞) ≠ ∞ := fun i x ↦
      ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by simp))
    have hgm : ∀ i, Measurable (g i) := fun i ↦ ((hFm i).min measurable_const).ennreal_toReal
    have hgnn : ∀ i x, 0 ≤ g i x := fun i x ↦ ENNReal.toReal_nonneg
    have hofReal : ∀ (i) (x : Fin n → ℝ), ENNReal.ofReal (g i x) = min (F i x) (M : ℝ≥0∞) :=
      fun i x ↦ ENNReal.ofReal_toReal (hminlt i x)
    have hgC : ∀ i x, |g i x| ≤ (M : ℝ) := by
      intro i x
      rw [abs_of_nonneg (hgnn i x), hg]
      refine ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg M) ?_
      simp
    -- the chessboard estimate
    have hchess := abs_integral_prod_pow_le_pi_siteEquiv (μ := μ)
      (fun j ↦ measurePreserving_shift_heisenbergPeriodicGibbsDist ν j)
      (fun k ↦ measurePreserving_siteEquiv_torusReflAt_heisenbergPeriodicGibbsDist
        ((hnd k).flipCoord_eq heven) ν)
      (fun k ↦ isReflectionPositive_heisenbergPeriodicGibbsDist_of_isNonnegDefiniteAt hsum heven
        (hnd k) ν hint) hgm hgC
    -- the right-hand side factors are at most `1`, and nonnegative
    have hRHSnn : ∀ j : Fin (d + 1) → ZMod (2 * N), 0 ≤ ∫ ω, ∏ i, g j (ω i) ∂μ := by
      intro j
      rw [hBL (fun _ ↦ g j) (fun _ ↦ hgm j) (fun _ ↦ hgnn j)]
      exact ENNReal.toReal_nonneg
    have hRHS : ∀ j : Fin (d + 1) → ZMod (2 * N), (∫ ω, ∏ i, g j (ω i) ∂μ) ≤ 1 := by
      intro j
      rw [hBL (fun _ ↦ g j) (fun _ ↦ hgm j) (fun _ ↦ hgnn j)]
      have hmono : (∫⁻ ω, ∏ i, ENNReal.ofReal (g j (ω i)) ∂μ) ≤ ∫⁻ ω, ∏ i, F j (ω i) ∂μ :=
        lintegral_mono fun ω ↦ Finset.prod_le_prod' fun i _ ↦ by
          rw [hofReal]; exact min_le_left _ _
      rw [hone j] at hmono
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmono
    -- the left-hand side is at most `1`
    have hK : 0 < (2 * N) ^ (d + 1) := Nat.pow_pos (by have := NeZero.ne N; omega)
    have hpow : |∫ ω, ∏ i, g i (ω i) ∂μ| ^ ((2 * N) ^ (d + 1)) ≤ (1 : ℝ) ^ ((2 * N) ^ (d + 1)) := by
      refine le_trans (hchess.trans (Finset.prod_le_one (fun j _ ↦ hRHSnn j)
        fun j _ ↦ hRHS j)) ?_
      rw [one_pow]
    have hLHS : (∫ ω, ∏ i, g i (ω i) ∂μ) ≤ 1 :=
      (le_abs_self _).trans (le_of_pow_le_pow_left₀ hK.ne' zero_le_one hpow)
    rw [hBL g hgm hgnn] at hLHS
    -- the truncated integral is finite, so the bound transfers to `ℝ≥0∞`
    have hne : (∫⁻ ω, ∏ i, ENNReal.ofReal (g i (ω i)) ∂μ) ≠ ∞ := by
      have hb : (∫⁻ ω, ∏ i, ENNReal.ofReal (g i (ω i)) ∂μ)
          ≤ ∫⁻ _ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ),
              (M : ℝ≥0∞) ^ Fintype.card (Fin (d + 1) → ZMod (2 * N)) ∂μ := by
        refine lintegral_mono fun ω ↦ ?_
        calc ∏ i, ENNReal.ofReal (g i (ω i))
            ≤ ∏ _i : Fin (d + 1) → ZMod (2 * N), (M : ℝ≥0∞) :=
              Finset.prod_le_prod' fun i _ ↦ by rw [hofReal]; exact min_le_right _ _
          _ = (M : ℝ≥0∞) ^ Fintype.card (Fin (d + 1) → ZMod (2 * N)) := by
              rw [Finset.prod_const, Finset.card_univ]
      refine ne_of_lt (lt_of_le_of_lt hb ?_)
      rw [lintegral_const, measure_univ, mul_one]
      simp [lt_top_iff_ne_top, ENNReal.pow_eq_top_iff]
    have hle1 : (∫⁻ ω, ∏ i, ENNReal.ofReal (g i (ω i)) ∂μ) ≤ 1 := by
      rw [← ENNReal.ofReal_toReal hne]
      simpa using ENNReal.ofReal_le_ofReal hLHS
    refine le_trans (le_of_eq ?_) hle1
    exact lintegral_congr fun ω ↦ Finset.prod_congr rfl fun i _ ↦ (hofReal i (ω i)).symm
  -- monotone convergence `M ↑ ∞`
  have hsup : ∀ ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ),
      ⨆ M : ℕ, G M ω = ∏ i, F i (ω i) := by
    intro ω
    refine le_antisymm (iSup_le fun M ↦ Finset.prod_le_prod' fun i _ ↦ min_le_left _ _) ?_
    obtain ⟨M, hM⟩ := exists_nat_ge (∑ i, (F i (ω i)).toReal)
    refine le_iSup_of_le M (le_of_eq (Finset.prod_congr rfl fun i _ ↦ ?_).symm)
    refine min_eq_left ?_
    have hle : (F i (ω i)).toReal ≤ (M : ℝ) :=
      le_trans (Finset.single_le_sum (f := fun i ↦ (F i (ω i)).toReal)
        (fun i _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ i)) hM
    calc F i (ω i) = ENNReal.ofReal ((F i (ω i)).toReal) :=
          (ENNReal.ofReal_toReal (hFtop i (ω i))).symm
      _ ≤ ENNReal.ofReal (M : ℝ) := ENNReal.ofReal_le_ofReal hle
      _ = (M : ℝ≥0∞) := by simp
  have hfinal : (∫⁻ ω, ∏ i, F i (ω i) ∂μ) ≤ 1 := by
    rw [show (fun ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) ↦ ∏ i, F i (ω i))
        = fun ω ↦ ⨆ M : ℕ, G M ω from funext fun ω ↦ (hsup ω).symm,
      lintegral_iSup hGm hGmono]
    exact iSup_le hGle
  -- back to the a priori measure
  have hkey := lintegral_prod_div_heisenbergPeriodicGibbs hexp hRm hR0 hRtop hνR ζ
  rw [hμ, heisenbergPeriodicGibbsDist, lintegral_smul_measure, hkey] at hfinal
  rw [← heisenbergPeriodicGibbs_univ_eq_lintegral hexp]
  calc (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
        ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ν))
      = heisenbergPeriodicGibbs N n J ν univ * ((heisenbergPeriodicGibbs N n J ν univ)⁻¹
          * ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
            ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦
              expSqTilted (heisenbergTilt N J) ν)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]
    _ ≤ heisenbergPeriodicGibbs N n J ν univ * 1 := mul_le_mul' le_rfl hfinal
    _ = heisenbergPeriodicGibbs N n J ν univ := mul_one _

/-- **Georgii, Lemma (20.13), first case, stated for the a priori measure**: Gaussian domination
holds whenever `λ` is equivalent to Lebesgue measure, `λ = r · dx` with `0 < r(x) < ∞` for every
`x`.  Georgii's running example `E = ℝ^N`, `λ(dx) = exp[-c|x|^{2+ε}] dx` is of this form; the
surface measure on a sphere is not, and needs his three further approximation steps. -/
theorem isGaussianDominating_of_eq_withDensity {d N n : ℕ} [NeZero N]
    {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J) {r : (Fin n → ℝ) → ℝ≥0∞} (hrm : Measurable r)
    (hr0 : ∀ x, r x ≠ 0) (hrtop : ∀ x, r x ≠ ∞) (hνr : ν = volume.withDensity r) :
    IsGaussianDominating N n J ν := by
  refine isGaussianDominating_of_withDensity hν hexp hsum heven hnd
    (R := fun x ↦ r x * ENNReal.ofReal (Real.exp (heisenbergTilt N J * (x ⬝ᵥ x))))
    (hrm.mul (measurable_expSqDensity _))
    (fun x ↦ mul_ne_zero (hr0 x) (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (fun x ↦ ENNReal.mul_ne_top (hrtop x) ENNReal.ofReal_ne_top) ?_
  rw [expSqTilted, hνr, ← withDensity_mul _ hrm (measurable_expSqDensity _)]
  rfl

end Chessboard

end MeasureTheory.GibbsMeasure

end

end

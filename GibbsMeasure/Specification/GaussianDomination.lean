/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
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
* **the approximation.**  `isGaussianDominating` removes the absolute continuity: for *every*
  finite `λ ≠ 0` satisfying (20.3) the mollifications `λ ∗ ψ_ε` — `ψ = e^{-|y|⁴} dy`,
  `ψ_ε` its image under `y ↦ ε y` — are equivalent to Lebesgue measure
  (`exists_withDensity_conv_map_smul_quarticMollifier`) and satisfy (20.3)
  (`hasExpSqMoments_conv_map_smul_quarticMollifier`), so the first case applies to them, and the
  inequality survives `ε ↓ 0` by dominated convergence
  (`tendsto_lintegral_pi_heisenbergShiftedDensity_conv`).  In particular the surface measure of a
  sphere — the Heisenberg model proper of Theorem (20.15) — is covered, as is Georgii's other
  running example `λ(dx) = exp[-c|x|^{2+ε}] dx`.
* **(20.13)** `lintegral_heisenbergShiftFactor_le_one` and
  `integral_heisenbergShiftFactor_le_one` are the conclusion for any `λ` for which
  `IsGaussianDominating` holds;
  `lintegral_heisenbergShiftFactor_le_one_of_isNonnegDefiniteAt` and
  `integral_heisenbergShiftFactor_le_one_of_isNonnegDefiniteAt` are Georgii's Lemma (20.13) as
  stated, with that hypothesis discharged.

## A deviation from Georgii

Georgii's approximation is a three-step limit: `λ` absolutely continuous and carried by a compact
ball; an arbitrary finite measure on a ball, as a *weak* limit of absolutely continuous ones; the
ball increasing to `ℝ^N`.  One mollification does all three at once, and does so with dominated
convergence against (20.3) instead of weak convergence on a ball, which is why no compactness and
no boundedness of `f_Λ^Φ(ζ, ·)` are needed here.  The mollifier is *not* a Gaussian: (20.3) for
`λ ∗ ψ_ε` requires `∫ e^{a|y|²} dψ < ∞` for every `a`, which a Gaussian fails; `e^{-|y|⁴} dy` has
that and an everywhere positive density, which is what the first case needs.
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
    rw [sub_dotProduct_sub]
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
    rw [hij, sub_dotProduct_sub]
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

/-- **`W` is continuous**: it is a quadratic polynomial in the configuration.  This is what makes
the mollification limit `ε ↓ 0` a pointwise limit. -/
lemma continuous_heisenbergDiffExponent :
    Continuous (heisenbergDiffExponent N n J (d := d)) := by
  refine Continuous.div_const (Continuous.neg ?_) _
  exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    Continuous.const_mul (((continuous_apply i).sub (continuous_apply j)).dotProduct
      ((continuous_apply i).sub (continuous_apply j))) _

/-- **`|W(ω)| ≤ ‖J‖₀ ∑_i |ω_i|²`.**  Georgii's estimate `abs_heisenbergExponent_le` at the start
of the proof of (20.6), transported through `heisenbergExponent_eq_diffExponent_add`: the tilt
`Ĵ(1)/2` is itself bounded by `‖J‖₀/2` (`sum_abs_periodizedCoupling_le`).  It is the domination
that makes every integral of `e^W` in this file converge against (20.3). -/
theorem abs_heisenbergDiffExponent_le (hsum : Summable J)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    |heisenbergDiffExponent N n J ω| ≤ (∑' m, |J m|) * ∑ i, (ω i ⬝ᵥ ω i) := by
  have hS : 0 ≤ ∑ i, (ω i ⬝ᵥ ω i) :=
    Finset.sum_nonneg fun i _ ↦ Matrix.dotProduct_self_nonneg _
  have hsplit := heisenbergExponent_eq_diffExponent_add (N := N) (n := n) (J := J) ω
  have h1 : |heisenbergExponent N n J ω| ≤ (∑' m, |J m|) / 2 * ∑ i, (ω i ⬝ᵥ ω i) :=
    abs_heisenbergExponent_le hsum ω
  have h2 : |∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m| ≤ ∑' m, |J m| :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (sum_abs_periodizedCoupling_le hsum)
  have hW : heisenbergDiffExponent N n J ω
      = heisenbergExponent N n J ω
        - (∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) / 2 * ∑ i, (ω i ⬝ᵥ ω i) := by
    linarith [hsplit]
  have hb : |(∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) / 2 * ∑ i, (ω i ⬝ᵥ ω i)|
      ≤ (∑' m, |J m|) / 2 * ∑ i, (ω i ⬝ᵥ ω i) := by
    rw [abs_mul, abs_of_nonneg hS]
    refine mul_le_mul_of_nonneg_right ?_ hS
    rw [abs_div, abs_two]
    linarith
  rw [hW]
  have := abs_sub (heisenbergExponent N n J ω)
    ((∑ m : Fin d → ZMod (2 * N), periodizedCoupling N J m) / 2 * ∑ i, (ω i ⬝ᵥ ω i))
  linarith

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

/-! ### Georgii's approximation steps: an arbitrary finite a priori measure

Georgii removes the absolute continuity of `λ` from the first case in three steps: `λ` absolutely
continuous and carried by a compact ball, then an arbitrary finite measure on a ball (a weak limit
of absolutely continuous ones), then the ball increasing to `ℝ^N`.  All three are subsumed here by
a single mollification.  For a fixed auxiliary finite measure `ψ` on `ℝ^N` and `ε > 0` put
`ψ_ε = ` the image of `ψ` under `y ↦ ε y`; then `λ ∗ ψ_ε` is absolutely continuous with an
everywhere positive finite Lebesgue density for *every* finite `λ ≠ 0`, so the first case applies
to it, and `ε ↓ 0` returns `λ` by dominated convergence, the domination being exactly (20.3).

The auxiliary `ψ` has to satisfy two requirements at once: its density must be everywhere positive
(a compactly supported bump would leave the density of `λ ∗ ψ_ε` vanishing somewhere, and Georgii's
first case needs `0 < r < ∞`), and it must have *all* Gaussian exponential moments (20.3), which a
Gaussian does not.  The measure `e^{-|y|⁴} dy` has both. -/

section Approximation

open Filter Topology

/-! #### The mollifying measure `e^{-|y|⁴} dy` -/

/-- **The mollifying density `e^{-|y|⁴}`.**  Everywhere positive, bounded by `1`, and with all
Gaussian exponential moments (`lintegral_exp_quarticMollifier_ne_top`). -/
def quarticDensity (y : Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(y ⬝ᵥ y) ^ 2))

/-- **The mollifying measure `e^{-|y|⁴} dy` on `ℝ^n`.**  It is not normalised: the total mass
enters both sides of the Gaussian domination inequality and cancels. -/
def quarticMollifier (n : ℕ) : Measure (Fin n → ℝ) := volume.withDensity quarticDensity

lemma measurable_quarticDensity : Measurable (quarticDensity (n := n)) :=
  ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
    (((measurable_id.dotProduct measurable_id).pow_const 2).neg))

@[simp] lemma quarticDensity_pos (y : Fin n → ℝ) : 0 < quarticDensity y :=
  ENNReal.ofReal_pos.2 (Real.exp_pos _)

@[simp] lemma quarticDensity_ne_top (y : Fin n → ℝ) : quarticDensity y ≠ ∞ := ENNReal.ofReal_ne_top

lemma quarticDensity_le_one (y : Fin n → ℝ) : quarticDensity y ≤ 1 := by
  rw [quarticDensity, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg _)))

/-- The one-dimensional Gaussian integral, in `ℝ≥0∞` form. -/
private lemma lintegral_exp_neg_sq_ne_top :
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (-(t * t)))) ≠ ∞ := by
  have hint : Integrable fun t : ℝ ↦ Real.exp (-(t * t)) := by
    have h := integrable_exp_neg_mul_sq (b := 1) one_pos
    refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
    norm_num [sq]
  have := hint.2
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun t ↦ (Real.exp_nonneg _))] at this
  exact this.ne

/-- The `n`-dimensional Gaussian integral `∫ e^{-|y|²} dy < ∞`, in `ℝ≥0∞` form. -/
private lemma lintegral_exp_neg_dotProduct_ne_top :
    (∫⁻ y : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(y ⬝ᵥ y)))) ≠ ∞ := by
  have hsplit : ∀ y : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(y ⬝ᵥ y)))
      = ∏ i, ENNReal.ofReal (Real.exp (-(y i * y i))) := by
    intro y
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_nonneg _), ← Real.exp_sum]
    exact congrArg _ (congrArg _ (by rw [dotProduct, ← Finset.sum_neg_distrib]))
  have hmeas : Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-(t * t))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_id.mul measurable_id).neg)
  rw [volume_pi, lintegral_congr hsplit,
    lintegral_pi_prod (fun _ : Fin n ↦ (volume : Measure ℝ))
      (g := fun _ t ↦ ENNReal.ofReal (Real.exp (-(t * t)))) fun _ ↦ hmeas]
  exact ENNReal.prod_ne_top fun i _ ↦ lintegral_exp_neg_sq_ne_top

/-- **Georgii's (20.3) for the mollifier**: `∫ e^{a|y|²} e^{-|y|⁴} dy < ∞` for *every* `a`, since
the quartic in the exponent beats the quadratic.  This is what a Gaussian mollifier fails. -/
lemma lintegral_exp_quarticMollifier_ne_top (a : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (a * (y ⬝ᵥ y))) ∂(quarticMollifier n)) ≠ ∞ := by
  have hmeas : Measurable fun y : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (a * (y ⬝ᵥ y))) :=
    measurable_expSqDensity a
  have hpt : ∀ y : Fin n → ℝ,
      quarticDensity y * ENNReal.ofReal (Real.exp (a * (y ⬝ᵥ y)))
        ≤ ENNReal.ofReal (Real.exp ((a + 1) ^ 2 / 4)) * ENNReal.ofReal (Real.exp (-(y ⬝ᵥ y))) := by
    intro y
    rw [quarticDensity, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith [sq_nonneg (y ⬝ᵥ y - (a + 1) / 2)]
  rw [quarticMollifier, lintegral_withDensity_eq_lintegral_mul _ measurable_quarticDensity hmeas]
  simp only [Pi.mul_apply]
  have hm2 : Measurable fun y : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (-(y ⬝ᵥ y))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_id.dotProduct measurable_id).neg)
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_const_mul _ hm2]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_exp_neg_dotProduct_ne_top

instance isFiniteMeasure_quarticMollifier : IsFiniteMeasure (quarticMollifier n) := by
  refine ⟨lt_of_le_of_ne le_top ?_⟩
  have h := lintegral_exp_quarticMollifier_ne_top (n := n) 0
  simpa using h

lemma quarticMollifier_univ_pos : 0 < (quarticMollifier n) univ := by
  have hsupp : Function.support (quarticDensity (n := n)) = univ :=
    Set.eq_univ_of_forall fun y ↦ (quarticDensity_pos y).ne'
  rw [quarticMollifier, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_pos_iff_support measurable_quarticDensity, hsupp]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

lemma quarticMollifier_univ_ne_zero : (quarticMollifier n) univ ≠ 0 := quarticMollifier_univ_pos.ne'

/-! #### The mollified a priori measure `λ ∗ ψ_ε` -/

/-- **Georgii's (20.3) in `ℝ≥0∞` form.**  Intended home: next to `HasExpSqMoments` in
`GibbsMeasure.Specification.InfraredBound`. -/
lemma hasExpSqMoments_iff_lintegral_ne_top {μ : Measure (Fin n → ℝ)} :
    HasExpSqMoments μ ↔ ∀ a : ℝ, (∫⁻ x, ENNReal.ofReal (Real.exp (a * (x ⬝ᵥ x))) ∂μ) ≠ ∞ := by
  have hmeas : ∀ a : ℝ, Measurable fun x : Fin n → ℝ ↦ Real.exp (a * (x ⬝ᵥ x)) := fun a ↦
    Real.continuous_exp.measurable.comp ((measurable_id.dotProduct measurable_id).const_mul a)
  refine ⟨fun h a ↦ ?_, fun h a ↦ ⟨(hmeas a).aestronglyMeasurable, ?_⟩⟩
  · have h2 := (h a).2
    rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦ (Real.exp_nonneg _))] at h2
    exact h2.ne
  · rw [hasFiniteIntegral_iff_ofReal (.of_forall fun x ↦ (Real.exp_nonneg _))]
    exact lt_of_le_of_ne le_top (h a)

lemma hasExpSqMoments_quarticMollifier : HasExpSqMoments (quarticMollifier n) :=
  hasExpSqMoments_iff_lintegral_ne_top.2 fun a ↦ lintegral_exp_quarticMollifier_ne_top a

/-- **The mollified measure is equivalent to Lebesgue measure.**  For every finite `λ ≠ 0` and
every `ε ≠ 0`, `λ ∗ ψ_ε = r · dx` with `0 < r(x) < ∞` everywhere: the density is
`r(x) = |ε^n|⁻¹ ∫ λ(dw) e^{-|(x - w)/ε|⁴}`, positive because the mollifying density is, and finite
because it is bounded.  This is what makes Georgii's first case
(`isGaussianDominating_of_eq_withDensity`) applicable to `λ ∗ ψ_ε` for an *arbitrary* finite
`λ`. -/
lemma exists_withDensity_conv_map_smul_quarticMollifier {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) {ε : ℝ} (hε : ε ≠ 0) :
    ∃ r : (Fin n → ℝ) → ℝ≥0∞, Measurable r ∧ (∀ x, r x ≠ 0) ∧ (∀ x, r x ≠ ∞) ∧
      μ ∗ ((quarticMollifier n).map (ε • ·)) = volume.withDensity r := by
  set c : ℝ≥0∞ := ENNReal.ofReal |(ε ^ Module.finrank ℝ (Fin n → ℝ))⁻¹| with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.2 (inv_ne_zero (pow_ne_zero _ hε))
  set q : (Fin n → ℝ) → ℝ≥0∞ := fun y ↦ quarticDensity (ε⁻¹ • y) with hq
  have hqm : Measurable q := measurable_quarticDensity.comp (measurable_const_smul _)
  have hconv : Measurable (Function.uncurry fun w x : Fin n → ℝ ↦ q (-w + x)) :=
    hqm.comp (measurable_fst.neg.add measurable_snd)
  have hint : Measurable fun x ↦ ∫⁻ w, q (-w + x) ∂μ := hconv.lintegral_prod_left
  have hψ : (quarticMollifier n).map (ε • ·) = c • volume.withDensity q := by
    rw [quarticMollifier, Measure.map_addHaar_smul_withDensity _ hε measurable_quarticDensity]
  refine ⟨c • fun x ↦ ∫⁻ w, q (-w + x) ∂μ, hint.const_mul c, fun x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, Ne, mul_eq_zero]
    push Not
    refine ⟨hc0, ?_⟩
    have hsupp : Function.support (fun w : Fin n → ℝ ↦ q (-w + x)) = univ :=
      Set.eq_univ_of_forall fun w ↦ (quarticDensity_pos _).ne'
    have hqx : Measurable fun w : Fin n → ℝ ↦ q (-w + x) :=
      hqm.comp (measurable_neg.add_const x)
    have : 0 < ∫⁻ w, q (-w + x) ∂μ := by
      rw [lintegral_pos_iff_support hqx, hsupp]
      exact Measure.measure_univ_pos.2 hμ
    exact this.ne'
  · rw [Pi.smul_apply, smul_eq_mul]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top ?_
      (lintegral_mono fun w ↦ quarticDensity_le_one (ε⁻¹ • (-w + x))))
    rw [lintegral_one]
    exact measure_ne_top μ univ
  · rw [hψ, Measure.conv_smul_right, Measure.conv_withDensity _ _ hqm,
      withDensity_smul c hint]

/-- The scaled mollifier `ψ_ε` is finite. -/
instance isFiniteMeasure_map_smul_quarticMollifier (ε : ℝ) :
    IsFiniteMeasure ((quarticMollifier n).map (ε • ·)) :=
  Measure.isFiniteMeasure_map _ _

/-- **The `a`-th Gaussian exponential moment of the scaled mollifier** is the `aε²`-th moment of
the mollifier. -/
lemma lintegral_exp_map_smul_quarticMollifier (a ε : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (a * (y ⬝ᵥ y))) ∂((quarticMollifier n).map (ε • ·)))
      = ∫⁻ u, ENNReal.ofReal (Real.exp ((a * ε ^ 2) * (u ⬝ᵥ u))) ∂(quarticMollifier n) := by
  rw [lintegral_map (measurable_expSqDensity a) (measurable_const_smul ε)]
  refine lintegral_congr fun u ↦ ?_
  refine congrArg _ (congrArg _ ?_)
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Georgii's (20.3) is stable under mollification.**  `∫ e^{a|x|²} d(λ ∗ ψ_ε) < ∞` for every
`a`, by `|x + y|² ≤ 2|x|² + 2|y|²` and the exponential square moments of `λ` and of `ψ`.  The
second is the reason the mollifier cannot be a Gaussian: a Gaussian has `∫ e^{a|y|²} dψ = ∞` for
all large `a`, and (20.3) for `λ ∗ ψ_ε` would fail. -/
lemma hasExpSqMoments_conv_map_smul_quarticMollifier {μ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure μ] (hexp : HasExpSqMoments μ) (ε : ℝ) :
    HasExpSqMoments (μ ∗ ((quarticMollifier n).map (ε • ·))) := by
  rw [hasExpSqMoments_iff_lintegral_ne_top]
  intro a
  have hb : Measurable fun x : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (2 * |a| * (x ⬝ᵥ x))) :=
    measurable_expSqDensity _
  have hpt : ∀ x y : Fin n → ℝ, ENNReal.ofReal (Real.exp (a * ((x + y) ⬝ᵥ (x + y))))
      ≤ ENNReal.ofReal (Real.exp (2 * |a| * (x ⬝ᵥ x)))
        * ENNReal.ofReal (Real.exp (2 * |a| * (y ⬝ᵥ y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : (x + y) ⬝ᵥ (x + y) ≤ 2 * (x ⬝ᵥ x) + 2 * (y ⬝ᵥ y) := add_dotProduct_add_le x y
    have h2 : a * ((x + y) ⬝ᵥ (x + y)) ≤ |a| * ((x + y) ⬝ᵥ (x + y)) :=
      mul_le_mul_of_nonneg_right (le_abs_self a) (Matrix.dotProduct_self_nonneg _)
    nlinarith [abs_nonneg a]
  have hstep : ∀ x : Fin n → ℝ,
      (∫⁻ y, ENNReal.ofReal (Real.exp (a * ((x + y) ⬝ᵥ (x + y))))
          ∂((quarticMollifier n).map (ε • ·)))
        ≤ ENNReal.ofReal (Real.exp (2 * |a| * (x ⬝ᵥ x)))
          * ∫⁻ y, ENNReal.ofReal (Real.exp (2 * |a| * (y ⬝ᵥ y)))
              ∂((quarticMollifier n).map (ε • ·)) := by
    intro x
    rw [← lintegral_const_mul _ hb]
    exact lintegral_mono fun y ↦ hpt x y
  rw [Measure.lintegral_conv (measurable_expSqDensity a)]
  refine ne_top_of_le_ne_top ?_ ((lintegral_mono hstep).trans (le_of_eq (lintegral_mul_const _ hb)))
  refine ENNReal.mul_ne_top (hasExpSqMoments_iff_lintegral_ne_top.1 hexp _) ?_
  rw [lintegral_exp_map_smul_quarticMollifier]
  exact lintegral_exp_quarticMollifier_ne_top _

/-! #### The integrand of Georgii's `λ̃^Λ(g ∘ τ_ζ)` over the untilted product measure -/

variable (N n J) in
/-- **The `λ^Λ`-density of the shifted `°γ_Λ^Φ`**,

`exp[Ĵ(1)/2 ∑_i |σ_i|² + W(σ - ζ)] = exp[½ ∑_{i,j} J_Λ(i-j) σ_i·σ_j] f_Λ^Φ(ζ, σ)`,

that is, the integrand of Georgii's `λ̃^Λ(g ∘ τ_ζ)` written over the *untilted* product measure
`λ^Λ` (`lintegral_expSqTilted_eq_lintegral_shiftedDensity`).  Mollification is carried out
against it, because — unlike the tilted measure `λ̃` — the a priori measure `λ` itself is what is
being convolved. -/
def heisenbergShiftedDensity (ζ x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (heisenbergTilt N J * ∑ i, (x i ⬝ᵥ x i)
    + heisenbergDiffExponent N n J (x - ζ)))

lemma continuous_heisenbergShiftedDensity (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Continuous (heisenbergShiftedDensity N n J ζ) := by
  have h1 : Continuous fun x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      heisenbergTilt N J * ∑ i, (x i ⬝ᵥ x i) :=
    continuous_const.mul (continuous_finsetSum _ fun i _ ↦
      (continuous_apply i).dotProduct (continuous_apply i))
  have h2 : Continuous fun x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      heisenbergDiffExponent N n J (x - ζ) :=
    continuous_heisenbergDiffExponent.comp (continuous_id.sub continuous_const)
  exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (h1.add h2))

lemma measurable_heisenbergShiftedDensity (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    Measurable (heisenbergShiftedDensity N n J ζ) :=
  (continuous_heisenbergShiftedDensity ζ).measurable

/-- **Georgii's `λ̃^Λ(g ∘ τ_ζ)` over the untilted product measure.**  The tilt
`λ̃ = e^{|x|² Ĵ(1)/2} λ` is a one-site density, so `λ̃^Λ` is `λ^Λ` with the product density and the
integral of `e^{W(· - ζ)}` against `λ̃^Λ` is the integral of `heisenbergShiftedDensity` against
`λ^Λ`. -/
theorem lintegral_expSqTilted_eq_lintegral_shiftedDensity {ρ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ρ] (hexp : HasExpSqMoments ρ)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ)))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ρ))
      = ∫⁻ ω, heisenbergShiftedDensity N n J ζ ω
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ) := by
  have _hfin : IsFiniteMeasure (ρ.withDensity fun x ↦
      ENNReal.ofReal (Real.exp (heisenbergTilt N J * (x ⬝ᵥ x)))) :=
    isFiniteMeasure_expSqTilted (a := heisenbergTilt N J) hexp
  have hprod : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ∏ i, ENNReal.ofReal (Real.exp (heisenbergTilt N J * (ω i ⬝ᵥ ω i))) :=
    Finset.measurable_prod _ fun i _ ↦ (measurable_expSqDensity _).comp (measurable_pi_apply i)
  have hWζ : Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J (ω - ζ))) :=
    (measurable_heisenbergDiffExponent.comp (measurable_id.sub_const ζ)).exp.ennreal_ofReal
  have hpi : (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ρ)
      = (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ).withDensity
          (fun ω ↦ ∏ i, ENNReal.ofReal (Real.exp (heisenbergTilt N J * (ω i ⬝ᵥ ω i)))) :=
    Measure.pi_withDensity (fun _ : Fin d → ZMod (2 * N) ↦ ρ)
      (r := fun _ ↦ fun x ↦ ENNReal.ofReal (Real.exp (heisenbergTilt N J * (x ⬝ᵥ x))))
      (fun _ ↦ measurable_expSqDensity _)
  rw [hpi, lintegral_withDensity_eq_lintegral_mul _ hprod hWζ]
  refine lintegral_congr fun ω ↦ ?_
  rw [Pi.mul_apply, ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_nonneg _)),
    ← Real.exp_sum, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Finset.mul_sum]
  rfl

/-! #### `(λ ∗ ψ_ε)^Λ` as the image of `λ^Λ ⊗ ψ^Λ` -/

/-- **A product of convolutions is the convolution of the products**, in integrated form:
`(λ ∗ ψ_ε)^Λ` is the image of `λ^Λ ⊗ ψ^Λ` under `(ω, y) ↦ ω + ε y`.  This is
`MeasureTheory.Measure.pi_conv` together with `MeasureTheory.Measure.pi_map_pi`; it is what turns
the mollification limit into an application of dominated convergence over the *fixed* measure
`λ^Λ ⊗ ψ^Λ`. -/
theorem lintegral_pi_conv_map_smul {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] (ε : ℝ)
    {F : ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦
        μ ∗ ((quarticMollifier n).map (ε • ·))))
      = ∫⁻ z, F (z.1 + ε • z.2)
          ∂((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ).prod
              (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)) := by
  have hsmul : Measurable fun y : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ ε • y :=
    measurable_const_smul ε
  have hmap : (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ (quarticMollifier n).map (ε • ·))
      = (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n).map (ε • ·) :=
    (Measure.pi_map_pi (μ := fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)
      (f := fun _ (x : Fin n → ℝ) ↦ ε • x) fun _ ↦ (measurable_const_smul ε).aemeasurable).symm
  have hinner : ∀ x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
      (∫⁻ y, F (x + y) ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦
          (quarticMollifier n).map (ε • ·)))
        = ∫⁻ y, F (x + ε • y)
            ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n) := by
    intro x
    have hFx : Measurable fun y : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ F (x + y) :=
      hF.comp (measurable_const_add x)
    rw [hmap, lintegral_map hFx hsmul]
  have hjoint : AEMeasurable (fun z : (((Fin d → ZMod (2 * N)) → (Fin n → ℝ))
      × ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))) ↦ F (z.1 + ε • z.2))
      ((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ).prod
        (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)) :=
    (hF.comp (measurable_fst.add (hsmul.comp measurable_snd))).aemeasurable
  rw [Measure.pi_conv, Measure.lintegral_conv hF]
  simp only [hinner]
  exact (lintegral_prod _ hjoint).symm

/-! #### The domination, and the limit `ε ↓ 0` -/

/-- **A Gaussian exponential moment of the product measure.**  `∫ e^{b ∑_i |x_i|²} dλ^Λ < ∞` for
every `b`, by (20.3) at each site. -/
lemma lintegral_pi_exp_dotProduct_ne_top {ρ : Measure (Fin n → ℝ)} [SigmaFinite ρ]
    (hexp : HasExpSqMoments ρ) (b : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (b * ∑ i, (x i ⬝ᵥ x i)))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ)) ≠ ∞ := by
  have hsplit : ∀ x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
      ENNReal.ofReal (Real.exp (b * ∑ i, (x i ⬝ᵥ x i)))
        = ∏ i, ENNReal.ofReal (Real.exp (b * (x i ⬝ᵥ x i))) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ (Real.exp_nonneg _)), ← Real.exp_sum,
      Finset.mul_sum]
  rw [lintegral_congr hsplit,
    lintegral_pi_prod (fun _ : Fin d → ZMod (2 * N) ↦ ρ)
      (g := fun _ x ↦ ENNReal.ofReal (Real.exp (b * (x ⬝ᵥ x)))) fun _ ↦ measurable_expSqDensity b]
  exact ENNReal.prod_ne_top fun i _ ↦ hasExpSqMoments_iff_lintegral_ne_top.1 hexp b

/-- **The domination for the mollification limit.**  For `|ε| ≤ 1`,

`exp[Ĵ(1)/2 ∑_i |ω_i + ε y_i|² + W(ω + ε y - ζ)]
  ≤ exp[2‖J‖₀ ∑_i |ζ_i|²] exp[b ∑_i |ω_i|²] exp[b ∑_i |y_i|²]`,   `b = 4‖J‖₀ + 2|Ĵ(1)/2|`,

by `|W| ≤ ‖J‖₀ ∑_i |·_i|²` (`abs_heisenbergDiffExponent_le`) and the parallelogram bound.  The
right-hand side is `λ^Λ ⊗ ψ^Λ`-integrable by (20.3) for `λ` and for `ψ`, which is exactly what
dominated convergence needs. -/
lemma heisenbergShiftedDensity_add_smul_le (hsum : Summable J)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) {ε : ℝ} (hε : |ε| ≤ 1)
    (ω y : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergShiftedDensity N n J ζ (ω + ε • y)
      ≤ ENNReal.ofReal (Real.exp (2 * (∑' m, |J m|) * ∑ i, (ζ i ⬝ᵥ ζ i)
          + (4 * (∑' m, |J m|) + 2 * |heisenbergTilt N J|) * ∑ i, (ω i ⬝ᵥ ω i)
          + (4 * (∑' m, |J m|) + 2 * |heisenbergTilt N J|) * ∑ i, (y i ⬝ᵥ y i))) := by
  have hK0 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith [abs_nonneg ε, sq_abs ε]
  have hnn : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ x := fun x ↦ Matrix.dotProduct_self_nonneg x
  have hSnn : ∀ x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ), 0 ≤ ∑ i, (x i ⬝ᵥ x i) :=
    fun x ↦ Finset.sum_nonneg fun i _ ↦ hnn _
  -- the two pointwise square bounds
  have hx : ∀ i, ((ω + ε • y) i ⬝ᵥ (ω + ε • y) i)
      ≤ 2 * (ω i ⬝ᵥ ω i) + 2 * (y i ⬝ᵥ y i) := by
    intro i
    have h2 := add_dotProduct_add_le (ω i) (ε • y i)
    have h3 : (ε • y i) ⬝ᵥ (ε • y i) = ε ^ 2 * (y i ⬝ᵥ y i) := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [h3] at h2
    have h4 : ε ^ 2 * (y i ⬝ᵥ y i) ≤ y i ⬝ᵥ y i := by nlinarith [hnn (y i)]
    have h1 : (ω + ε • y) i = ω i + ε • y i := rfl
    rw [h1]
    linarith
  have hz : ∀ i, ((ω + ε • y - ζ) i ⬝ᵥ (ω + ε • y - ζ) i)
      ≤ 4 * (ω i ⬝ᵥ ω i) + 4 * (y i ⬝ᵥ y i) + 2 * (ζ i ⬝ᵥ ζ i) := by
    intro i
    have h1 : (ω + ε • y - ζ) i = (ω + ε • y) i + (-ζ i) := by
      simp only [Pi.sub_apply, sub_eq_add_neg]
    have h2 := add_dotProduct_add_le ((ω + ε • y) i) (-ζ i)
    have h3 : (-ζ i) ⬝ᵥ (-ζ i) = ζ i ⬝ᵥ ζ i := by
      rw [neg_dotProduct, dotProduct_neg, neg_neg]
    rw [h3] at h2
    rw [h1]
    linarith [hx i]
  -- the two summed bounds
  have hSx : ∑ i, ((ω + ε • y) i ⬝ᵥ (ω + ε • y) i)
      ≤ 2 * (∑ i, (ω i ⬝ᵥ ω i)) + 2 * ∑ i, (y i ⬝ᵥ y i) := by
    calc ∑ i, ((ω + ε • y) i ⬝ᵥ (ω + ε • y) i)
        ≤ ∑ i, (2 * (ω i ⬝ᵥ ω i) + 2 * (y i ⬝ᵥ y i)) := Finset.sum_le_sum fun i _ ↦ hx i
      _ = 2 * (∑ i, (ω i ⬝ᵥ ω i)) + 2 * ∑ i, (y i ⬝ᵥ y i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hSz : ∑ i, ((ω + ε • y - ζ) i ⬝ᵥ (ω + ε • y - ζ) i)
      ≤ 4 * (∑ i, (ω i ⬝ᵥ ω i)) + 4 * (∑ i, (y i ⬝ᵥ y i)) + 2 * ∑ i, (ζ i ⬝ᵥ ζ i) := by
    calc ∑ i, ((ω + ε • y - ζ) i ⬝ᵥ (ω + ε • y - ζ) i)
        ≤ ∑ i, (4 * (ω i ⬝ᵥ ω i) + 4 * (y i ⬝ᵥ y i) + 2 * (ζ i ⬝ᵥ ζ i)) :=
          Finset.sum_le_sum fun i _ ↦ hz i
      _ = 4 * (∑ i, (ω i ⬝ᵥ ω i)) + 4 * (∑ i, (y i ⬝ᵥ y i)) + 2 * ∑ i, (ζ i ⬝ᵥ ζ i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum]
  -- the tilt and the exponent `W`
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have e1 : heisenbergTilt N J * ∑ i, ((ω + ε • y) i ⬝ᵥ (ω + ε • y) i)
      ≤ |heisenbergTilt N J| * (2 * (∑ i, (ω i ⬝ᵥ ω i)) + 2 * ∑ i, (y i ⬝ᵥ y i)) := by
    refine le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hSnn _)) ?_
    exact mul_le_mul_of_nonneg_left hSx (abs_nonneg _)
  have e2 : heisenbergDiffExponent N n J (ω + ε • y - ζ)
      ≤ (∑' m, |J m|) * (4 * (∑ i, (ω i ⬝ᵥ ω i)) + 4 * (∑ i, (y i ⬝ᵥ y i))
          + 2 * ∑ i, (ζ i ⬝ᵥ ζ i)) := by
    refine le_trans (le_trans (le_abs_self _) (abs_heisenbergDiffExponent_le hsum _)) ?_
    exact mul_le_mul_of_nonneg_left hSz hK0
  nlinarith [e1, e2]

/-- **The mollification limit**, and with it Georgii's three approximation steps at one stroke:

`∫ S d(λ ∗ ψ_ε)^Λ ⟶ ψ^Λ(1) ∫ S dλ^Λ`   as `ε → 0`,

for the integrand `S = heisenbergShiftedDensity` of Georgii's `λ̃^Λ(g ∘ τ_ζ)`.  The identity
`lintegral_pi_conv_map_smul` moves the `ε`-dependence into the integrand over the *fixed* measure
`λ^Λ ⊗ ψ^Λ`, `heisenbergShiftedDensity_add_smul_le` dominates it, and `S` is continuous. -/
theorem tendsto_lintegral_pi_heisenbergShiftedDensity_conv (hsum : Summable J)
    {μ : Measure (Fin n → ℝ)} [IsFiniteMeasure μ] (hexp : HasExpSqMoments μ)
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) {ε : ℕ → ℝ} (hε1 : ∀ k, |ε k| ≤ 1)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫⁻ x, heisenbergShiftedDensity N n J ζ x
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ ∗ ((quarticMollifier n).map (ε k • ·))))
      atTop (𝓝 ((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n) univ
        * ∫⁻ x, heisenbergShiftedDensity N n J ζ x
            ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ))) := by
  set S := heisenbergShiftedDensity N n J ζ with hS
  have hSm : Measurable S := measurable_heisenbergShiftedDensity ζ
  set b : ℝ := 4 * (∑' m, |J m|) + 2 * |heisenbergTilt N J| with hb
  set c : ℝ := 2 * (∑' m, |J m|) * ∑ i, (ζ i ⬝ᵥ ζ i) with hcdef
  set B : (((Fin d → ZMod (2 * N)) → (Fin n → ℝ))
      × ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))) → ℝ≥0∞ :=
    fun z ↦ ENNReal.ofReal (Real.exp (c + b * ∑ i, (z.1 i ⬝ᵥ z.1 i)
      + b * ∑ i, (z.2 i ⬝ᵥ z.2 i))) with hB
  have hexpb : Measurable fun x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (b * ∑ i, (x i ⬝ᵥ x i))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((Finset.measurable_sum _ fun i _ ↦
        (measurable_pi_apply i).dotProduct (measurable_pi_apply i)).const_mul b))
  have hrw : ∀ k, (∫⁻ x, S x ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦
        μ ∗ ((quarticMollifier n).map (ε k • ·))))
      = ∫⁻ z, S (z.1 + ε k • z.2)
          ∂((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ).prod
              (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)) :=
    fun k ↦ lintegral_pi_conv_map_smul (ε k) hSm
  have hconst : (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n) univ
      * ∫⁻ x, S x ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ)
      = ∫⁻ z, S z.1
          ∂((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ).prod
              (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)) := by
    have hfst : AEMeasurable (fun z : (((Fin d → ZMod (2 * N)) → (Fin n → ℝ))
        × ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))) ↦ S z.1)
        ((Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ).prod
          (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ quarticMollifier n)) :=
      (hSm.comp measurable_fst).aemeasurable
    rw [lintegral_prod _ hfst]
    simp only [lintegral_const]
    rw [lintegral_mul_const _ hSm, mul_comm]
  simp only [hrw]
  rw [hconst]
  refine tendsto_lintegral_of_dominated_convergence B
    (fun k ↦ hSm.comp (measurable_fst.add ((measurable_const_smul (ε k)).comp measurable_snd)))
    (fun k ↦ Filter.Eventually.of_forall fun z ↦
      heisenbergShiftedDensity_add_smul_le hsum ζ (hε1 k) z.1 z.2) ?_ ?_
  · have hBsplit : ∀ z : (((Fin d → ZMod (2 * N)) → (Fin n → ℝ))
        × ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))),
        B z = (ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp (b * ∑ i, (z.1 i ⬝ᵥ z.1 i))))
          * ENNReal.ofReal (Real.exp (b * ∑ i, (z.2 i ⬝ᵥ z.2 i))) := by
      intro z
      change ENNReal.ofReal (Real.exp (c + b * ∑ i, (z.1 i ⬝ᵥ z.1 i)
        + b * ∑ i, (z.2 i ⬝ᵥ z.2 i))) = _
      rw [Real.exp_add, Real.exp_add, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity)]
    have hf1 : AEMeasurable (fun x : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
        ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp (b * ∑ i, (x i ⬝ᵥ x i))))
        (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ μ) := (hexpb.const_mul _).aemeasurable
    rw [lintegral_congr hBsplit, lintegral_prod_mul hf1 hexpb.aemeasurable]
    refine ENNReal.mul_ne_top ?_ (lintegral_pi_exp_dotProduct_ne_top
      hasExpSqMoments_quarticMollifier b)
    rw [lintegral_const_mul _ hexpb]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_pi_exp_dotProduct_ne_top hexp b)
  · refine Filter.Eventually.of_forall fun z ↦ ?_
    have h1 : Tendsto (fun k ↦ z.1 + ε k • z.2) atTop (𝓝 z.1) := by
      have h2 : Tendsto (fun k ↦ ε k • z.2) atTop (𝓝 ((0 : ℝ) • z.2)) := hε.smul_const z.2
      rw [zero_smul] at h2
      simpa using (tendsto_const_nhds (x := z.1) (f := atTop)).add h2
    exact ((continuous_heisenbergShiftedDensity ζ).tendsto z.1).comp h1

/-! #### Georgii's Lemma (20.13) for an arbitrary finite a priori measure -/

/-- The right-hand side of `IsGaussianDominating`, in terms of `heisenbergShiftedDensity`. -/
theorem lintegral_expSqTilted_eq_lintegral_shiftedDensity_zero {ρ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ρ] (hexp : HasExpSqMoments ρ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergDiffExponent N n J ω))
        ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ expSqTilted (heisenbergTilt N J) ρ))
      = ∫⁻ ω, heisenbergShiftedDensity N n J 0 ω
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ) := by
  rw [← lintegral_expSqTilted_eq_lintegral_shiftedDensity hexp 0]
  exact lintegral_congr fun ω ↦ by rw [sub_zero]

/-- **Gaussian domination over the untilted product measure.**  `IsGaussianDominating` says
exactly that the `λ^Λ`-integral of the shifted density is maximal at `ζ = 0`. -/
theorem isGaussianDominating_iff_lintegral_shiftedDensity {ρ : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ρ] (hexp : HasExpSqMoments ρ) :
    IsGaussianDominating N n J ρ
      ↔ ∀ ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
          (∫⁻ x, heisenbergShiftedDensity N n J ζ x
              ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ))
            ≤ ∫⁻ x, heisenbergShiftedDensity N n J 0 x
                ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ρ) := by
  refine forall_congr' fun ζ ↦ ?_
  rw [lintegral_expSqTilted_eq_lintegral_shiftedDensity hexp ζ,
    lintegral_expSqTilted_eq_lintegral_shiftedDensity_zero hexp]

/-- The mollified measure is nonzero. -/
lemma conv_map_smul_quarticMollifier_ne_zero {μ : Measure (Fin n → ℝ)} (hμ : μ ≠ 0) (ε : ℝ) :
    μ ∗ ((quarticMollifier n).map (ε • ·)) ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, Measure.conv_apply_univ,
    Measure.map_apply (measurable_const_smul ε) MeasurableSet.univ, Set.preimage_univ]
  exact mul_ne_zero (Measure.measure_univ_ne_zero.2 hμ) quarticMollifier_univ_ne_zero

/-- **Georgii, Lemma (20.13), for an arbitrary finite a priori measure.**

`λ̃^Λ(g ∘ τ_ζ) ≤ λ̃^Λ(g)` for every finite `λ ≠ 0` satisfying (20.3) — no absolute continuity is
assumed, so the surface measure of a sphere (the Heisenberg model proper, which is what (20.15)
needs) is covered.

Georgii's first case (`isGaussianDominating_of_eq_withDensity`, the chessboard estimate) is
applied to the mollifications `λ ∗ ψ_ε`, which are equivalent to Lebesgue measure
(`exists_withDensity_conv_map_smul_quarticMollifier`) and inherit (20.3)
(`hasExpSqMoments_conv_map_smul_quarticMollifier`), and the resulting inequalities pass to the
limit `ε ↓ 0` (`tendsto_lintegral_pi_heisenbergShiftedDensity_conv`), where the common factor
`ψ^Λ(1)` cancels.  This replaces Georgii's three approximation steps (absolutely continuous on a
ball, arbitrary on a ball, ball `↑ ℝ^N`) by a single mollification. -/
theorem isGaussianDominating {d N n : ℕ} [NeZero N] {J : (Fin (d + 1) → ℤ) → ℝ}
    {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J) :
    IsGaussianDominating N n J ν := by
  set ε : ℕ → ℝ := fun k ↦ ((k : ℝ) + 1)⁻¹ with hεdef
  have hεpos : ∀ k, 0 < ε k := by
    intro k
    simp only [hεdef]
    positivity
  have hε1 : ∀ k, |ε k| ≤ 1 := by
    intro k
    rw [abs_of_pos (hεpos k)]
    simp only [hεdef]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.congr fun k ↦ one_div _
  -- the mollified a priori measures satisfy Georgii's first case
  have hfin : ∀ k, IsFiniteMeasure (ν ∗ ((quarticMollifier n).map (ε k • ·))) := fun k ↦
    inferInstance
  have hexpk : ∀ k, HasExpSqMoments (ν ∗ ((quarticMollifier n).map (ε k • ·))) := fun k ↦
    hasExpSqMoments_conv_map_smul_quarticMollifier hexp (ε k)
  have hdom : ∀ k, IsGaussianDominating N n J (ν ∗ ((quarticMollifier n).map (ε k • ·))) := by
    intro k
    obtain ⟨r, hrm, hr0, hrtop, hrν⟩ :=
      exists_withDensity_conv_map_smul_quarticMollifier hν (hεpos k).ne'
    exact isGaussianDominating_of_eq_withDensity
      (conv_map_smul_quarticMollifier_ne_zero hν (ε k)) (hexpk k) hsum heven hnd hrm hr0 hrtop hrν
  -- pass to the limit
  rw [isGaussianDominating_iff_lintegral_shiftedDensity hexp]
  intro ζ
  have hk : ∀ k, (∫⁻ x, heisenbergShiftedDensity N n J ζ x
        ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦
          ν ∗ ((quarticMollifier n).map (ε k • ·))))
      ≤ ∫⁻ x, heisenbergShiftedDensity N n J 0 x
        ∂(Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦
          ν ∗ ((quarticMollifier n).map (ε k • ·))) := fun k ↦
    (isGaussianDominating_iff_lintegral_shiftedDensity (hexpk k)).1 (hdom k) ζ
  have hA := tendsto_lintegral_pi_heisenbergShiftedDensity_conv (μ := ν) hsum hexp ζ hε1 hε0
  have hB := tendsto_lintegral_pi_heisenbergShiftedDensity_conv (μ := ν) hsum hexp
    (0 : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) hε1 hε0
  have hC0 : (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ quarticMollifier n) univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun i _ ↦ quarticMollifier_univ_ne_zero
  have hCtop : (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ quarticMollifier n) univ ≠ ∞ :=
    measure_ne_top _ _
  exact (ENNReal.mul_le_mul_iff_right hC0 hCtop).1 (le_of_tendsto_of_tendsto' hA hB hk)

/-- **Georgii, Lemma (20.13)**, with no hypothesis on `λ` beyond (20.3):

`°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) ≤ °γ_Λ^Φ(f_Λ^Φ(0, ·)) = 1`,   `ζ ∈ (ℝ^N)^Λ`.

This is `lintegral_heisenbergShiftFactor_le_one` with the Gaussian domination hypothesis
discharged by `isGaussianDominating`. -/
theorem lintegral_heisenbergShiftFactor_le_one_of_isNonnegDefiniteAt {d N n : ℕ} [NeZero N]
    {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫⁻ ω, ENNReal.ofReal (heisenbergShiftFactor N n J ζ ω)
        ∂(heisenbergPeriodicGibbsDist N n J ν)) ≤ 1 :=
  lintegral_heisenbergShiftFactor_le_one hν hexp hsum
    (isGaussianDominating hν hexp hsum heven hnd) ζ

/-- **Georgii, Lemma (20.13)** in Bochner form, with no hypothesis on `λ` beyond (20.3). -/
theorem integral_heisenbergShiftFactor_le_one_of_isNonnegDefiniteAt {d N n : ℕ} [NeZero N]
    {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (ζ : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)) :
    (∫ ω, heisenbergShiftFactor N n J ζ ω ∂(heisenbergPeriodicGibbsDist N n J ν)) ≤ 1 :=
  integral_heisenbergShiftFactor_le_one hν hexp hsum
    (isGaussianDominating hν hexp hsum heven hnd) ζ

end Approximation









end MeasureTheory.GibbsMeasure

end

end

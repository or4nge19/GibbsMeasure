/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.PSeries.Lattice
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.ExponentialMoment
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.PositiveDotProduct
public import GibbsMeasure.Specification.HeisenbergPeriodic

/-!
# Georgii §20.1: the a priori estimates for `N`-vector models, (20.1)–(20.8)

The chapter's parameter set is `S = ℤ^d` (`d ≥ 1`, so `Fin (d+1) → ℤ` here), the state space is
`ℝ^N` (`Fin n → ℝ` here) or a rotationally invariant Borel subset of it — encoded as the a priori
measure `λ = ν` being carried by that subset, which is strictly more general — and the
interaction is the isotropic pair potential of (20.1).

## The objects

* **(20.1)** the Heisenberg pair potential `Φ_{{i,j}} = -J(i-j) σ_i·σ_j` is
  `MeasureTheory.GibbsMeasure.heisenbergPotential`, defined in
  `GibbsMeasure.Specification.HeisenbergPeriodic`: (20.1) is verbatim (17.22), and there is no
  second definition.
* **(20.2)** Georgii's `‖J‖₀ = ∑_k |J(k)| < ∞` is `Summable J`, and the number `‖J‖₀` is
  `∑' m, |J m|`.  `sum_abs_periodizedCoupling_le` and `abs_heisenbergExponent_le`
  (`HeisenbergPeriodic`) are the two estimates it is used for.
* **(20.3)** `MeasureTheory.GibbsMeasure.HasExpSqMoments`: `∫ λ(dx) e^{a|x|²} < ∞` for all `a`.
  Georgii asks it for `a ≥ 0` only; for a finite `λ` the two are equivalent, since the integrand
  is bounded by `1` when `a ≤ 0` (`HasExpSqMoments.of_nonneg`).
* **(20.4)** `MeasureTheory.GibbsMeasure.slowGrowth` is Georgii's `α(i) = (1 ∨ log|i|)^{1/2}` and
  `MeasureTheory.GibbsMeasure.IsSlowlySummable` is `∑_i |J(i)| α(i) < ∞`;
  `IsSlowlySummable.summable` is Georgii's remark that (20.4) is stronger than (20.2).
  The norm `|i|` is the sup norm of `ℤ^d`, not the Euclidean norm; the two differ by a factor
  `≤ √d`, so `log|i|` changes by `O(1)`, `α` by a bounded factor, `IsSlowlySummable` not at all,
  and the sets `Ω_t` below only by a rescaling of `t`, which is immaterial in (20.6)(iii).

## What is proved

* `measure_apply_le_toReal_div` is the workhorse: the chessboard estimate (17.11) for the
  reflections `r_k` (`measure_apply_pow_card_le_siteEquiv`) applied to a single-site event, with
  the resulting `|Λ|`-fold event and the partition function `°Z_Λ^Φ` both bounded by `|Λ|`-th
  powers, so that the powers cancel: `°γ_Λ^Φ(σ_{i₀} ∈ A) ≤ P/Q`.
* `heisenbergPeriodicGibbsDist_apply_le_div`: its uniform-bound form.  If the spins of `A` have
  pairwise scalar products at most `v`, those of `U` at least `u ≥ v`, and `J ≥ 0`, then
  `°γ_Λ^Φ(σ_{i₀} ∈ A) ≤ λ(A)/λ(U)`, with no dependence on the cube, on `J` or on the temperature.
* `exists_le_lintegral_dotProduct_self_heisenbergPeriodicGibbsDist`: **Lemma (20.8)**.  There is a
  `δ > 0` depending only on the a priori measure such that `°γ_Λ^Φ(|σ_i|²) ≥ δ` for every cube,
  every dimension, every site, and every nonnegative `J` which is nonnegative definite relative to
  all the reflections.  See the docstring for two errata to Georgii's proof.
* `heisenbergPeriodicGibbsDist_tail_le`: **the tail estimate of the proof of (20.6)**,
  `°γ_Λ^Φ(|σ_i|² ≥ t) ≤ b(a) e^{-a t}` for every `a > 0` and every `t`, uniformly in the cube,
  with `b(a) = (∫ λ(dx) e^{(a + ½‖J‖₀)|x|²}) / (∫ λ(dx) e^{-½‖J‖₀|x|²})` — Georgii's `b(a)`, with
  the sharper constant `½‖J‖₀` in place of his `‖J‖₀` (`abs_heisenbergExponent_le`).
* `lintegral_exp_dotProduct_self_le_of_tail`, `lintegral_indicator_abs_dotProduct_le` and
  `measure_compl_slowGrowthSet_le`: **(20.6)(i), (ii) and (iii)**.  Georgii derives all three from
  the tail estimate alone, so they are stated here for *any* probability measure on a
  configuration space satisfying it; `Ω_t` is `slowGrowthSet`.  (ii) replaces his Cauchy–Schwarz
  step by `uv ≤ u² + v²`, which needs no integrability and costs a factor `2` in his `b₂(a)`;
  (iii) needs the lattice `p`-series `summable_max_exp_norm_rpow`.

**Not transferred to `ℤ^d`.**  Georgii states (20.6) for the fields `μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0` on
`Ω = (ℝ^N)^{ℤ^d}` and for the cluster points `𝒢₀(Φ)`, and gets it from the torus estimate "by
continuity", the tail bound being a bound on a local event.  The three consequences above are
stated in exactly that generality (any probability measure on a configuration space with the tail
bound), but the *tail bound itself* is proved here only for the torus measure `°γ_Λ^Φ`: pushing it
forward to `ℤ^d` needs the embedding `°γ_Λ^Φ ↦ °γ_Λ^Φ × δ_ω` for the Heisenberg family, which the
tree has only for `C`-potentials (`MeasureTheory.GibbsMeasure.periodicGibbsField` in
`GibbsMeasure.Specification.PeriodicGibbsLimits`).  That embedding is the same missing layer as
the one (20.5) and (20.7) need; see below.

## What is *not* proved, and why

* **(20.5)**, the Gibbsian specification `γ^Φ` for an *unbounded* state space, and **(20.7)**,
  `∅ ≠ 𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`.  For an unbounded `E` and an infinite-range `J` the potential (20.1)
  violates Georgii's (2.2)(ii): the Hamiltonians `H_Λ^Φ` are defined only on the tail-measurable
  set `Ω_* = {sup_i |σ_i|/α(i) < ∞}`, and (20.5) is the resulting *modified* specification
  (Dirac at `0_Λ ω_{S∖Λ}` off `Ω_*`), in the style of (13.18).  The tree has no specification
  whose Hamiltonians are defined only on a tail set — `Potential.gibbsSpecification` requires a
  `λ`-admissible potential — so (20.5) cannot be stated here without first building that layer,
  and (20.7), whose proof compares `γ^{Φ^n}` with `γ^Φ` through Theorems (4.12), (4.17) and
  Proposition (4.19), cannot be stated without (20.5).  Note that Georgii himself flags
  (20.3)–(20.7) as needed *only* for an unbounded state space; over a bounded one, (20.7) is
  Comment (4.14)(1) with Example (4.20)(2) and Example (5.20)(3), which for `C`-potentials is
  `MeasureTheory.GibbsMeasure.GZero_nonempty` and `mem_GP_of_mem_GZero` in
  `GibbsMeasure.Specification.PeriodicGibbsLimits`.  A Heisenberg potential over a *bounded*
  state space is not expressible in the present setting either, because the spin space of
  `heisenbergPotential` is the whole of `ℝ^n`: `‖Φ_{{i,j}}‖` of (2.12) is a supremum over all of
  `(ℝ^n)^{ℤ^d}` and is infinite as soon as `J(i-j) ≠ 0`, whatever `λ` is.  Re-basing the
  Heisenberg objects on a general rotationally invariant spin space is the prerequisite for both.
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii (20.3) and (20.4): the hypotheses on `λ` and on `J` -/

section Hypotheses

variable {n : ℕ}

/-- **Georgii (20.3).**  The a priori measure has Gaussian exponential moments of every order:
`∫ λ(dx) e^{a|x|²} < ∞` for every `a`.  Georgii states it for `a ≥ 0`; for a finite measure the
two forms agree (`HasExpSqMoments.of_nonneg`). -/
def HasExpSqMoments (ν : Measure (Fin n → ℝ)) : Prop :=
  ∀ a : ℝ, Integrable (fun x ↦ Real.exp (a * (x ⬝ᵥ x))) ν

/-- For a finite measure, Georgii's (20.3) for `a ≥ 0` gives it for every `a`: the integrand is
bounded by `1` when `a ≤ 0`. -/
lemma HasExpSqMoments.of_nonneg {ν : Measure (Fin n → ℝ)} [IsFiniteMeasure ν]
    (h : ∀ a : ℝ, 0 ≤ a → Integrable (fun x ↦ Real.exp (a * (x ⬝ᵥ x))) ν) :
    HasExpSqMoments ν := by
  intro a
  rcases le_or_gt 0 a with ha | ha
  · exact h a ha
  · refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact (Real.continuous_exp.measurable.comp
        ((Finset.measurable_sum _ fun c _ ↦
          (measurable_pi_apply c).mul (measurable_pi_apply c)).const_mul _)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ha.le
        (Matrix.dotProduct_self_nonneg x))

variable {D : ℕ}

/-- **Georgii's `α(i) = (1 ∨ log|i|)^{1/2}`** of §20.1, with `|i|` the sup norm of `ℤ^d`. -/
def slowGrowth (i : Fin D → ℤ) : ℝ := Real.sqrt (max 1 (Real.log ‖i‖))

lemma one_le_slowGrowth (i : Fin D → ℤ) : 1 ≤ slowGrowth i :=
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (max 1 (Real.log ‖i‖)) := Real.sqrt_le_sqrt (le_max_left _ _)

lemma slowGrowth_pos (i : Fin D → ℤ) : 0 < slowGrowth i :=
  lt_of_lt_of_le zero_lt_one (one_le_slowGrowth i)

/-- `α(i)² = log(e ∨ |i|)`, the form in which `α` enters the proof of (20.6)(iii). -/
lemma slowGrowth_sq (i : Fin D → ℤ) :
    slowGrowth i ^ 2 = Real.log (max (Real.exp 1) ‖i‖) := by
  have hlog : max 1 (Real.log ‖i‖) = Real.log (max (Real.exp 1) ‖i‖) := by
    rcases le_or_gt ‖i‖ (Real.exp 1) with h | h
    · have hle : Real.log ‖i‖ ≤ 1 := by
        rcases eq_or_lt_of_le (norm_nonneg i) with h0 | h0
        · rw [← h0, Real.log_zero]; norm_num
        · rw [← Real.log_exp 1]
          exact Real.log_le_log h0 h
      rw [max_eq_left hle, max_eq_left h, Real.log_exp]
    · have hlog1 : 1 ≤ Real.log ‖i‖ :=
        (Real.le_log_iff_exp_le (lt_trans (Real.exp_pos 1) h)).2 h.le
      rw [max_eq_right hlog1, max_eq_right h.le]
  rw [slowGrowth, Real.sq_sqrt (le_trans zero_le_one (le_max_left _ _)), hlog]

/-- **Georgii (20.4).**  `∑_i |J(i)| α(i) < ∞`. -/
def IsSlowlySummable (J : (Fin D → ℤ) → ℝ) : Prop :=
  Summable fun i ↦ |J i| * slowGrowth i

/-- **Georgii's remark that (20.4) is stronger than (20.2)**: `α ≥ 1`. -/
lemma IsSlowlySummable.summable {J : (Fin D → ℤ) → ℝ} (h : IsSlowlySummable J) : Summable J := by
  refine Summable.of_norm_bounded h fun i ↦ ?_
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (J i), one_le_slowGrowth i]

end Hypotheses

/-! ### The chessboard estimate for `°γ_Λ^Φ`, in the form used throughout §20.1 -/

section Chessboard

variable {d n N : ℕ} [NeZero N] {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **The workhorse of §20.1.**  Georgii applies the chessboard estimate (17.11) to the
single-site event `{σ_{i₀} ∈ A}` and then bounds the resulting `|Λ|`-fold event and the partition
function `°Z_Λ^Φ` by `|Λ|`-th powers of one-site quantities.  Whenever

`°Z_Λ^Φ °γ_Λ^Φ(A^Λ) ≤ P^{|Λ|}`  and  `Q^{|Λ|} ≤ °Z_Λ^Φ`,

the two powers cancel and `°γ_Λ^Φ(σ_{i₀} ∈ A) ≤ P/Q`. -/
theorem measure_apply_le_toReal_div [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν))
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) {P Q : ℝ≥0∞} (hPtop : P ≠ ∞)
    (hQ0 : Q ≠ 0) (hQtop : Q ≠ ∞)
    (hP : heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A} ≤ P ^ ((2 * N) ^ (d + 1)))
    (hQ : Q ^ ((2 * N) ^ (d + 1)) ≤ heisenbergPeriodicGibbs N n J ν Set.univ)
    (i₀ : Fin (d + 1) → ZMod (2 * N)) :
    (heisenbergPeriodicGibbsDist N n J ν {ω | ω i₀ ∈ A}).toReal ≤ P.toReal / Q.toReal := by
  classical
  have hGfin : IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hprob : IsProbabilityMeasure (heisenbergPeriodicGibbsDist N n J ν) :=
    isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
  have hZpos : 0 < heisenbergPeriodicGibbs N n J ν Set.univ :=
    heisenbergPeriodicGibbs_univ_pos hν
  have hZtop : heisenbergPeriodicGibbs N n J ν Set.univ ≠ ∞ := measure_ne_top _ _
  have hKpos : 0 < (2 * N) ^ (d + 1) :=
    Nat.pow_pos (by have := NeZero.ne N; omega)
  have hchess := measure_apply_pow_card_le_siteEquiv
    (μ := heisenbergPeriodicGibbsDist N n J ν)
    (fun j ↦ measurePreserving_shift_heisenbergPeriodicGibbsDist ν j)
    (fun k ↦ measurePreserving_siteEquiv_torusReflAt_heisenbergPeriodicGibbsDist
      ((hnd k).flipCoord_eq heven) ν)
    (fun k ↦ isReflectionPositive_heisenbergPeriodicGibbsDist_of_isNonnegDefiniteAt hsum heven
      (hnd k) ν hint) hA i₀
  have hratio : ∀ S : Set ((Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)),
      (heisenbergPeriodicGibbsDist N n J ν S).toReal
        = (heisenbergPeriodicGibbs N n J ν S).toReal
          / (heisenbergPeriodicGibbs N n J ν Set.univ).toReal := by
    intro S
    rw [heisenbergPeriodicGibbsDist, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, inv_mul_eq_div]
  have hPtop' : P ^ ((2 * N) ^ (d + 1)) ≠ ∞ := by
    simp [ENNReal.pow_eq_top_iff, hPtop]
  have h1 : (heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A}).toReal
      ≤ P.toReal ^ ((2 * N) ^ (d + 1)) := by
    have h := ENNReal.toReal_mono hPtop' hP
    rwa [ENNReal.toReal_pow] at h
  have h2 : Q.toReal ^ ((2 * N) ^ (d + 1))
      ≤ (heisenbergPeriodicGibbs N n J ν Set.univ).toReal := by
    have h := ENNReal.toReal_mono hZtop hQ
    rwa [ENNReal.toReal_pow] at h
  have hQR : 0 < Q.toReal := ENNReal.toReal_pos hQ0 hQtop
  refine le_of_pow_le_pow_left₀ hKpos.ne' (div_nonneg ENNReal.toReal_nonneg hQR.le) ?_
  calc (heisenbergPeriodicGibbsDist N n J ν {ω | ω i₀ ∈ A}).toReal ^ ((2 * N) ^ (d + 1))
      ≤ (heisenbergPeriodicGibbsDist N n J ν {ω | ∀ i, ω i ∈ A}).toReal := hchess
    _ = (heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A}).toReal
          / (heisenbergPeriodicGibbs N n J ν Set.univ).toReal := hratio _
    _ ≤ P.toReal ^ ((2 * N) ^ (d + 1)) / Q.toReal ^ ((2 * N) ^ (d + 1)) :=
        div_le_div₀ (pow_nonneg ENNReal.toReal_nonneg _) h1 (pow_pos hQR _) h2
    _ = (P.toReal / Q.toReal) ^ ((2 * N) ^ (d + 1)) := (div_pow _ _ _).symm

/-- **The chessboard estimate with uniform bounds on the pair energies.**  If the spins of `A`
have pairwise scalar products at most `v` and those of `U` at least `u ≥ v`, and `J ≥ 0`, then
`°γ_Λ^Φ(σ_{i₀} ∈ A) ≤ λ(A)/λ(U)` — no dependence on the cube, on `J`, or on the temperature.
This is the estimate behind Georgii's Lemma (20.8). -/
theorem heisenbergPeriodicGibbsDist_apply_le_div [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hJ : ∀ m, 0 ≤ J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν))
    {A U : Set (Fin n → ℝ)} (hA : MeasurableSet A) (hU : MeasurableSet U) (hUne : ν U ≠ 0)
    {u v : ℝ} (huv : v ≤ u)
    (hAv : ∀ x ∈ A, ∀ y ∈ A, x ⬝ᵥ y ≤ v) (hUu : ∀ x ∈ U, ∀ y ∈ U, u ≤ x ⬝ᵥ y)
    (i₀ : Fin (d + 1) → ZMod (2 * N)) :
    (heisenbergPeriodicGibbsDist N n J ν {ω | ω i₀ ∈ A}).toReal
      ≤ (ν A).toReal / (ν U).toReal := by
  classical
  set S : ℝ := ∑' m, J m with hS
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg hJ
  set P : ℝ≥0∞ := ENNReal.ofReal (Real.exp (v * S / 2)) * ν A with hPdef
  set Q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (u * S / 2)) * ν U with hQdef
  have hpow : ∀ (c : ℝ) (B : Set (Fin n → ℝ)),
      (ENNReal.ofReal (Real.exp (c * S / 2)) * ν B) ^ ((2 * N) ^ (d + 1))
        = ENNReal.ofReal (Real.exp (((2 * N) ^ (d + 1) : ℕ) * (c * S) / 2))
          * ν B ^ ((2 * N) ^ (d + 1)) := by
    intro c B
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
    congr 2
    ring
  have hPle : heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A} ≤ P ^ ((2 * N) ^ (d + 1)) := by
    rw [hPdef, hpow]
    exact heisenbergPeriodicGibbs_forall_mem_le hA fun ω hω ↦
      heisenbergExponent_le_of_le hsum hJ fun i j ↦ hAv _ (hω i) _ (hω j)
  have hQle : Q ^ ((2 * N) ^ (d + 1)) ≤ heisenbergPeriodicGibbs N n J ν Set.univ := by
    rw [hQdef, hpow]
    exact le_heisenbergPeriodicGibbs_univ hU fun ω hω ↦
      le_heisenbergExponent_of_le hsum hJ fun i j ↦ hUu _ (hω i) _ (hω j)
  have hPtop : P ≠ ∞ := by
    rw [hPdef]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hQtop : Q ≠ ∞ := by
    rw [hQdef]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hQ0 : Q ≠ 0 := by
    rw [hQdef]
    exact mul_ne_zero (by simp [Real.exp_pos]) hUne
  refine (measure_apply_le_toReal_div hν hsum heven hnd hint hA hPtop hQ0 hQtop hPle hQle
    i₀).trans ?_
  rw [hPdef, hQdef, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (Real.exp_nonneg _), ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hUR : 0 < (ν U).toReal := ENNReal.toReal_pos hUne (measure_ne_top _ _)
  have hexp : Real.exp (v * S / 2) ≤ Real.exp (u * S / 2) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hEu : (0 : ℝ) < Real.exp (u * S / 2) := Real.exp_pos _
  calc Real.exp (v * S / 2) * (ν A).toReal / (Real.exp (u * S / 2) * (ν U).toReal)
      ≤ Real.exp (u * S / 2) * (ν A).toReal / (Real.exp (u * S / 2) * (ν U).toReal) := by
        gcongr
    _ = (ν A).toReal / (ν U).toReal := by
        field_simp

end Chessboard

/-! ### Georgii, Lemma (20.8) -/

section LowerBound

variable {n : ℕ}

/-- **Georgii, Lemma (20.8).**  There is a `δ > 0` depending only on the a priori measure `λ`
such that `°γ_Λ^Φ(|σ_i|²) ≥ δ` for *every* cube `Λ`, every dimension, every site and every
potential of the form (20.1) whose coupling `J` is nonnegative and nonnegative definite relative
to all the reflections `r_1, …, r_d`.

The only hypothesis on `λ` is Georgii's non-degeneracy `λ(E ∖ {0}) > 0`; his rotational
invariance is not needed, since a set `U` of positive measure on which the scalar products are
bounded below by some `u > 0` exists for *any* measure charging the complement of the origin
(`MeasureTheory.exists_forall_le_dotProduct_of_measure_ne_zero`).

**Erratum to the proof of (20.8).**  Georgii asks that `ε ≤ u`; what the estimate needs is
`ε² ≤ u`, which is what is used here (the parameter `s` below is his `ε²`).  For `u > 1` his
condition is strictly weaker than what the proof requires; since `ε` is chosen as small as one
likes, the lemma itself is unaffected.  Georgii's second estimate `°γ_Λ^Φ(|σ_0| = 0) ≤ a` with
`a = λ({0})/λ({0} ∪ U)` also needs the lower bound `°Z_Λ^Φ ≥ λ({0} ∪ U)^{|Λ|}`, not the bound
`°Z_Λ^Φ ≥ (λ(U) e^{u‖J‖₀/2})^{|Λ|}` he uses for the first one; both are instances of
`le_heisenbergPeriodicGibbs_univ`, the second with the set `{0} ∪ U` and the constant `0`. -/
theorem exists_le_lintegral_dotProduct_self_heisenbergPeriodicGibbsDist
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν] (hν : ν {x : Fin n → ℝ | x ≠ 0} ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d N : ℕ) [NeZero N] (J : (Fin (d + 1) → ℤ) → ℝ),
      Summable J → (∀ m, J (-m) = J m) → (∀ m, 0 ≤ J m) → (∀ k, IsNonnegDefiniteAt k J) →
      Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
        (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν) →
      ∀ i₀ : Fin (d + 1) → ZMod (2 * N),
        ENNReal.ofReal δ ≤ ∫⁻ ω, ENNReal.ofReal (ω i₀ ⬝ᵥ ω i₀)
          ∂(heisenbergPeriodicGibbsDist N n J ν) := by
  classical
  obtain ⟨U, u, hUmeas, hUne, hupos, hUdot⟩ :=
    exists_forall_le_dotProduct_of_measure_ne_zero hν
  have hν0 : ν ≠ 0 := fun h ↦ hν (by simp [h])
  have hzero : (0 : Fin n → ℝ) ∉ U := fun h ↦ by
    have := hUdot 0 h 0 h
    simp only [dotProduct, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at this
    linarith
  -- `U' = {0} ∪ U`, on which the scalar products are still nonnegative.
  have hU'meas : MeasurableSet (insert (0 : Fin n → ℝ) U) := hUmeas.insert 0
  have hU'split : ν (insert (0 : Fin n → ℝ) U) = ν {(0 : Fin n → ℝ)} + ν U := by
    rw [Set.insert_eq, measure_union (by simpa using hzero) hUmeas]
  have hU'ne : ν (insert (0 : Fin n → ℝ) U) ≠ 0 := fun h ↦ hUne (by
    refine measure_mono_null (Set.subset_insert _ _) h)
  have hU'dot : ∀ x ∈ insert (0 : Fin n → ℝ) U, ∀ y ∈ insert (0 : Fin n → ℝ) U,
      (0 : ℝ) ≤ x ⬝ᵥ y := by
    intro x hx y hy
    rcases hx with hx | hx
    · subst hx; simp [dotProduct]
    · rcases hy with hy | hy
      · subst hy; simp [dotProduct]
      · linarith [hUdot x hx y hy]
  have hUR : 0 < (ν U).toReal := ENNReal.toReal_pos hUne (measure_ne_top _ _)
  have hU'R : 0 < (ν (insert (0 : Fin n → ℝ) U)).toReal :=
    ENNReal.toReal_pos hU'ne (measure_ne_top _ _)
  set a : ℝ := (ν {(0 : Fin n → ℝ)}).toReal / (ν (insert (0 : Fin n → ℝ) U)).toReal with ha
  have halt : a < 1 := by
    rw [ha, div_lt_one hU'R, hU'split, ENNReal.toReal_add (measure_ne_top _ _)
      (measure_ne_top _ _)]
    linarith
  have ha0 : 0 ≤ a := div_nonneg ENNReal.toReal_nonneg hU'R.le
  -- Georgii's `ε`, in the form `s = ε²`.
  have hAmeas : ∀ s : ℝ, MeasurableSet {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s} := fun s ↦ by
    have h1 : MeasurableSet {x : Fin n → ℝ | x ≠ 0} :=
      (measurableSet_singleton (0 : Fin n → ℝ)).compl
    have h2 : MeasurableSet {x : Fin n → ℝ | x ⬝ᵥ x < s} :=
      measurableSet_lt (Finset.measurable_sum _ fun c _ ↦
        (measurable_pi_apply c).mul (measurable_pi_apply c)) measurable_const
    exact h1.inter h2
  obtain ⟨s, hs0, hsu, hsb⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ u ∧
      (ν {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}).toReal / (ν U).toReal < 1 - a := by
    have hsqpos : ∀ m : ℕ, 0 < min u (1 / (m + 1 : ℝ)) := fun m ↦ lt_min hupos (by positivity)
    have hanti : Antitone
        fun m : ℕ ↦ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < min u (1 / (m + 1 : ℝ))} := by
      intro m m' hmm x hx
      refine ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_min le_rfl ?_)⟩
      have : (m : ℝ) + 1 ≤ (m' : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmm
      exact one_div_le_one_div_of_le (by positivity) this
    have hinter : (⋂ m : ℕ, {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < min u (1 / (m + 1 : ℝ))}) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hx
      have hx0 : x ≠ 0 := (hx 0).1
      have hxpos : 0 < x ⬝ᵥ x :=
        lt_of_le_of_ne (Matrix.dotProduct_self_nonneg x) fun h ↦ hx0
          (dotProduct_self_eq_zero.1 h.symm)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hxpos
      exact absurd ((hx m).2.trans_le (min_le_right _ _)) (not_lt.2 hm.le)
    have htend := tendsto_measure_iInter_atTop
      (μ := ν) (s := fun m : ℕ ↦ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < min u (1 / (m + 1 : ℝ))})
      (fun m ↦ (hAmeas _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at htend
    have h1 : Filter.Tendsto
        (fun m : ℕ ↦ (ν {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < min u (1 / (m + 1 : ℝ))}).toReal)
        Filter.atTop (nhds 0) := by
      have := (ENNReal.tendsto_toReal (by simp)).comp htend
      simpa [Function.comp_def] using this
    have h2 := (h1.div_const ((ν U).toReal))
    rw [zero_div] at h2
    obtain ⟨m, hm⟩ := (h2.eventually_lt_const (by linarith : (0 : ℝ) < 1 - a)).exists
    exact ⟨min u (1 / (m + 1 : ℝ)), hsqpos m, min_le_left _ _, hm⟩
  set b : ℝ := (ν {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}).toReal / (ν U).toReal with hb
  have hb0 : 0 ≤ b := div_nonneg ENNReal.toReal_nonneg hUR.le
  refine ⟨s * (1 - a - b), by nlinarith, ?_⟩
  intro d N _ J hsum heven hJ hnd hint i₀
  have hprob := isProbabilityMeasure_heisenbergPeriodicGibbsDist hν0 hint
  -- The three estimates of Georgii's proof.
  have h1 : (heisenbergPeriodicGibbsDist N n J ν
      {ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}).toReal ≤ a := by
    refine heisenbergPeriodicGibbsDist_apply_le_div hν0 hsum heven hJ hnd hint
      (measurableSet_singleton (0 : Fin n → ℝ)) hU'meas hU'ne (le_refl (0 : ℝ)) ?_ hU'dot i₀
    intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst hx; subst hy
    simp [dotProduct]
  have h2 : (heisenbergPeriodicGibbsDist N n J ν
      {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}}).toReal ≤ b := by
    refine heisenbergPeriodicGibbsDist_apply_le_div hν0 hsum heven hJ hnd hint
      (hAmeas s) hUmeas hUne hsu ?_ hUdot i₀
    intro x hx y hy
    have := Matrix.dotProduct_le_half_add x y
    linarith [hx.2, hy.2]
  -- The three events cover the configuration space.
  have hcover : (Set.univ : Set ((Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)))
      ⊆ ({ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}
        ∪ {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}})
        ∪ {ω | s ≤ ω i₀ ⬝ᵥ ω i₀} := by
    intro ω _
    by_cases hω : ω i₀ = 0
    · exact Or.inl (Or.inl hω)
    · rcases lt_or_ge (ω i₀ ⬝ᵥ ω i₀) s with h | h
      · exact Or.inl (Or.inr ⟨hω, h⟩)
      · exact Or.inr h
  have hfin : ∀ S : Set ((Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ)),
      heisenbergPeriodicGibbsDist N n J ν S ≠ ∞ := fun S ↦ measure_ne_top _ _
  have hle : (1 : ℝ) ≤ (heisenbergPeriodicGibbsDist N n J ν
        {ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}).toReal
      + (heisenbergPeriodicGibbsDist N n J ν
        {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}}).toReal
      + (heisenbergPeriodicGibbsDist N n J ν {ω | s ≤ ω i₀ ⬝ᵥ ω i₀}).toReal := by
    have h₁ : (1 : ℝ≥0∞)
        ≤ heisenbergPeriodicGibbsDist N n J ν {ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}
          + heisenbergPeriodicGibbsDist N n J ν
            {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}}
          + heisenbergPeriodicGibbsDist N n J ν {ω | s ≤ ω i₀ ⬝ᵥ ω i₀} := by
      calc (1 : ℝ≥0∞) = heisenbergPeriodicGibbsDist N n J ν Set.univ := measure_univ.symm
        _ ≤ heisenbergPeriodicGibbsDist N n J ν (({ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}
              ∪ {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}})
              ∪ {ω | s ≤ ω i₀ ⬝ᵥ ω i₀}) := measure_mono hcover
        _ ≤ heisenbergPeriodicGibbsDist N n J ν ({ω | ω i₀ ∈ ({0} : Set (Fin n → ℝ))}
              ∪ {ω | ω i₀ ∈ {x : Fin n → ℝ | x ≠ 0 ∧ x ⬝ᵥ x < s}})
              + heisenbergPeriodicGibbsDist N n J ν {ω | s ≤ ω i₀ ⬝ᵥ ω i₀} :=
            measure_union_le _ _
        _ ≤ _ := by gcongr; exact measure_union_le _ _
    have h₂ := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩, hfin _⟩) h₁
    rw [ENNReal.toReal_one, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) (hfin _),
      ENNReal.toReal_add (hfin _) (hfin _)] at h₂
    linarith
  have h3 : (1 : ℝ) - a - b
      ≤ (heisenbergPeriodicGibbsDist N n J ν {ω | s ≤ ω i₀ ⬝ᵥ ω i₀}).toReal := by
    linarith
  -- Conclusion.
  have hEmeas : MeasurableSet {ω : (Fin (d + 1) → ZMod (2 * N)) → (Fin n → ℝ) |
      s ≤ ω i₀ ⬝ᵥ ω i₀} :=
    measurableSet_le measurable_const (measurable_dotProduct_apply i₀ i₀)
  calc ENNReal.ofReal (s * (1 - a - b))
      = ENNReal.ofReal s * ENNReal.ofReal (1 - a - b) := ENNReal.ofReal_mul hs0.le
    _ ≤ ENNReal.ofReal s
          * heisenbergPeriodicGibbsDist N n J ν {ω | s ≤ ω i₀ ⬝ᵥ ω i₀} := by
        gcongr
        exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 h3
    _ = ∫⁻ _ in {ω | s ≤ ω i₀ ⬝ᵥ ω i₀}, ENNReal.ofReal s
          ∂(heisenbergPeriodicGibbsDist N n J ν) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ ω in {ω | s ≤ ω i₀ ⬝ᵥ ω i₀}, ENNReal.ofReal (ω i₀ ⬝ᵥ ω i₀)
          ∂(heisenbergPeriodicGibbsDist N n J ν) :=
        setLIntegral_mono' hEmeas fun ω hω ↦ ENNReal.ofReal_le_ofReal hω
    _ ≤ ∫⁻ ω, ENNReal.ofReal (ω i₀ ⬝ᵥ ω i₀) ∂(heisenbergPeriodicGibbsDist N n J ν) :=
        setLIntegral_le_lintegral _ _

end LowerBound

/-! ### Georgii, Lemma (20.6): the tail estimate and its three consequences -/

section Tail

variable {d n N : ℕ} [NeZero N] {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **The tail estimate of Georgii's proof of Lemma (20.6).**  For every `a > 0` and every `t`,

`°γ_Λ^Φ(|σ_i|² ≥ t) ≤ b(a) e^{-a t}`, where
`b(a) = (∫ λ(dx) e^{(a + ½‖J‖₀)|x|²}) / (∫ λ(dx) e^{-½‖J‖₀|x|²})`,

uniformly in the cube `Λ`, in the site `i` and in the dimension.  This is Georgii's estimate with
his `‖J‖₀` replaced by the sharper `½‖J‖₀` of `abs_heisenbergExponent_le`; his restriction
`t ≥ 0` is not needed. -/
theorem heisenbergPeriodicGibbsDist_tail_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hnd : ∀ k, IsNonnegDefiniteAt k J)
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin (d + 1) → ZMod (2 * N) ↦ ν))
    {a : ℝ} (ha : 0 < a) (t : ℝ) (i₀ : Fin (d + 1) → ZMod (2 * N)) :
    (heisenbergPeriodicGibbsDist N n J ν {ω | t ≤ ω i₀ ⬝ᵥ ω i₀}).toReal
      ≤ (∫ x, Real.exp ((a + (∑' m, |J m|) / 2) * (x ⬝ᵥ x)) ∂ν)
          / (∫ x, Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) ∂ν) * Real.exp (-(a * t)) := by
  classical
  set c : ℝ := (∑' m, |J m|) / 2 with hc
  set A : Set (Fin n → ℝ) := {x | t ≤ x ⬝ᵥ x} with hA
  have hAmeas : MeasurableSet A :=
    measurableSet_le measurable_const (Finset.measurable_sum _ fun cc _ ↦
      (measurable_pi_apply cc).mul (measurable_pi_apply cc))
  set P : ℝ≥0∞ := ∫⁻ x in A, ENNReal.ofReal (Real.exp (c * (x ⬝ᵥ x))) ∂ν with hP
  set Q : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (-(c * (x ⬝ᵥ x)))) ∂ν with hQ
  -- The two one-site integrals as ordinary integrals.
  have hIup : ∫⁻ x, ENNReal.ofReal (Real.exp ((a + c) * (x ⬝ᵥ x))) ∂ν
      = ENNReal.ofReal (∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal (hexp (a + c))
      (Filter.Eventually.of_forall fun x ↦ (Real.exp_nonneg _))).symm
  have hQeq : Q = ENNReal.ofReal (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) := by
    have hcongr : (fun x : Fin n → ℝ ↦ Real.exp (-c * (x ⬝ᵥ x)))
        = fun x ↦ Real.exp (-(c * (x ⬝ᵥ x))) := by
      funext x; ring_nf
    rw [hQ, ← ofReal_integral_eq_lintegral_ofReal (by simpa [hcongr] using hexp (-c))
      (Filter.Eventually.of_forall fun x ↦ (Real.exp_nonneg _))]
  -- `Q > 0` and `Q < ∞`.
  have hQ0 : Q ≠ 0 := by
    rw [hQ, ← pos_iff_ne_zero, lintegral_pos_iff_support]
    · have hsupp : Function.support
          (fun x : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (-(c * (x ⬝ᵥ x))))) = Set.univ :=
        Set.eq_univ_of_forall fun x ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      rw [hsupp]
      exact pos_iff_ne_zero.2 (by simpa using hν)
    · exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((Finset.measurable_sum _ fun cc _ ↦
          (measurable_pi_apply cc).mul (measurable_pi_apply cc)).const_mul _).neg)
  have hQtop : Q ≠ ∞ := by rw [hQeq]; exact ENNReal.ofReal_ne_top
  -- `P` is bounded by `e^{-a t}` times the upper one-site integral.
  have hPle : P ≤ ENNReal.ofReal (Real.exp (-(a * t)))
      * ENNReal.ofReal (∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν) := by
    have hstep : P ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-(a * t)) * Real.exp ((a + c) * (x ⬝ᵥ x)))
        ∂ν := by
      refine le_trans (setLIntegral_mono' hAmeas fun x hx ↦ ?_)
        (setLIntegral_le_lintegral _ _)
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have hxt : t ≤ x ⬝ᵥ x := hx
      nlinarith
    refine hstep.trans (le_of_eq ?_)
    rw [← hIup]
    simp_rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp ((Finset.measurable_sum _ fun cc _ ↦
        (measurable_pi_apply cc).mul (measurable_pi_apply cc)).const_mul _)))
  have hPtop : P ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hPle
  -- The chessboard estimate.
  have hmain := measure_apply_le_toReal_div hν hsum heven hnd hint hAmeas hPtop hQ0 hQtop
    (heisenbergPeriodicGibbs_forall_mem_le_pow hsum hAmeas)
    (le_heisenbergPeriodicGibbs_univ_pow hsum) i₀
  refine hmain.trans ?_
  have hQR : 0 < Q.toReal := ENNReal.toReal_pos hQ0 hQtop
  have hPR : P.toReal ≤ Real.exp (-(a * t)) * ∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hPle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun x ↦ (Real.exp_nonneg _))] at h
  have hQtoReal : Q.toReal = ∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν := by
    rw [hQeq, ENNReal.toReal_ofReal (integral_nonneg fun x ↦ (Real.exp_nonneg _))]
  rw [hQtoReal] at hQR ⊢
  rw [div_le_iff₀ hQR]
  have hcancel : (∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν)
        / (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν) * Real.exp (-(a * t))
        * (∫ x, Real.exp (-(c * (x ⬝ᵥ x))) ∂ν)
      = Real.exp (-(a * t)) * ∫ x, Real.exp ((a + c) * (x ⬝ᵥ x)) ∂ν := by
    field_simp
  rw [hcancel]
  exact hPR

end Tail

/-! ### The three assertions of Lemma (20.6)

Georgii deduces (i), (ii) and (iii) from the tail estimate alone.  They are therefore stated here
for an arbitrary probability measure on a configuration space satisfying that estimate; that
covers `°γ_Λ^Φ` (`heisenbergPeriodicGibbsDist_tail_le`), Georgii's fields
`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0`, and every cluster point of them — the tail bound being a bound on a
*local event*, and therefore preserved under local convergence. -/

section TailConsequences

variable {S : Type*} {n : ℕ} {μ : Measure (S → (Fin n → ℝ))}

/-- **Georgii, Lemma (20.6)(i).**  A tail bound `μ(|σ_i|² ≥ t) ≤ b e^{-2a t}` gives
`μ(e^{a|σ_i|²}) ≤ 1 + b`. -/
theorem lintegral_exp_dotProduct_self_le_of_tail [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a)
    (i : S) (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | t ≤ ω i ⬝ᵥ ω i} ≤ ENNReal.ofReal (b * Real.exp (-(2 * a * t)))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (a * (ω i ⬝ᵥ ω i))) ∂μ ≤ 1 + ENNReal.ofReal b := by
  have hmeas : Measurable fun ω : S → (Fin n → ℝ) ↦ (ω i ⬝ᵥ ω i) :=
    (measurable_pi_apply i).dotProduct (measurable_pi_apply i)
  have h := lintegral_exp_le_of_measure_le (μ := μ) (f := fun ω ↦ ω i ⬝ᵥ ω i)
    hmeas.aemeasurable
    (Filter.Eventually.of_forall fun ω ↦ Matrix.dotProduct_self_nonneg (ω i))
    ha (by linarith : a < 2 * a) htail
  have hconst : a * b / (2 * a - a) = b := by
    field_simp
    ring
  rwa [hconst] at h

/-- **Georgii, Lemma (20.6)(ii).**  The truncated first moment of the pair energy is dominated by
`e^{-a t}` times the exponential moments of order `2a + 1` at the two sites.  Combined with
(20.6)(i) this is Georgii's `μ(|σ_i·σ_j| 1_{|σ_i·σ_j| ≥ t}) ≤ b₂(a) e^{-a t}` with
`b₂(a) = 2 b₁(2a+1)`; Georgii's `b₂(a) = b₁(2a+1)` drops the factor `2` coming from the two
sites.

The proof replaces Georgii's Cauchy–Schwarz step by the elementary `uv ≤ u² + v²`, which needs no
integrability. -/
theorem lintegral_indicator_abs_dotProduct_le {a : ℝ} (ha : 0 < a) (i j : S) (t : ℝ) :
    ∫⁻ ω, Set.indicator {ω : S → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
        (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω ∂μ
      ≤ ENNReal.ofReal (Real.exp (-(a * t)))
        * ((∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i))) ∂μ)
          + ∫⁻ ω, ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j))) ∂μ) := by
  classical
  have hEi : Measurable fun ω : S → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_pi_apply i).dotProduct (measurable_pi_apply i)).const_mul _))
  have hEj : Measurable fun ω : S → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_pi_apply j).dotProduct (measurable_pi_apply j)).const_mul _))
  have hpt : ∀ ω : S → (Fin n → ℝ),
      Set.indicator {ω : S → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
        (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω
        ≤ ENNReal.ofReal (Real.exp (-(a * t))
            * (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i))
              + Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j)))) := by
    intro ω
    by_cases hω : t ≤ |ω i ⬝ᵥ ω j|
    · rw [Set.indicator_of_mem
        (show ω ∈ {ω : S → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|} from hω)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hp : (0 : ℝ) ≤ ω i ⬝ᵥ ω i := Matrix.dotProduct_self_nonneg _
      have hq : (0 : ℝ) ≤ ω j ⬝ᵥ ω j := Matrix.dotProduct_self_nonneg _
      have hxy : 2 * |ω i ⬝ᵥ ω j| ≤ (ω i ⬝ᵥ ω i) + (ω j ⬝ᵥ ω j) :=
        Matrix.two_mul_abs_dotProduct_le _ _
      have hsplit : |ω i ⬝ᵥ ω j|
          = Real.exp (-(a * t)) * (Real.exp (a * t) * |ω i ⬝ᵥ ω j|) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
      have hkey : ∀ r : ℝ, 0 ≤ r → |ω i ⬝ᵥ ω j| ≤ r →
          Real.exp (a * t) * |ω i ⬝ᵥ ω j| ≤ Real.exp ((2 * a + 1) * r) := by
        intro r hr hle
        have h1 : Real.exp (a * t) ≤ Real.exp (a * r) :=
          Real.exp_le_exp.2 (by nlinarith [le_trans hω hle])
        have h2 : |ω i ⬝ᵥ ω j| ≤ Real.exp r := le_trans hle (by linarith [Real.add_one_le_exp r])
        have h3 : Real.exp (a * r) * Real.exp r = Real.exp ((a + 1) * r) := by
          rw [← Real.exp_add]; ring_nf
        calc Real.exp (a * t) * |ω i ⬝ᵥ ω j| ≤ Real.exp (a * r) * Real.exp r := by
              exact mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_nonneg _)
          _ = Real.exp ((a + 1) * r) := h3
          _ ≤ Real.exp ((2 * a + 1) * r) := Real.exp_le_exp.2 (by nlinarith)
      rw [hsplit]
      rcases le_total (ω i ⬝ᵥ ω i) (ω j ⬝ᵥ ω j) with hpq | hpq
      · have := hkey (ω j ⬝ᵥ ω j) hq (by linarith)
        nlinarith [Real.exp_pos (-(a * t)), Real.exp_pos ((2 * a + 1) * (ω i ⬝ᵥ ω i))]
      · have := hkey (ω i ⬝ᵥ ω i) hp (by linarith)
        nlinarith [Real.exp_pos (-(a * t)), Real.exp_pos ((2 * a + 1) * (ω j ⬝ᵥ ω j))]
    · rw [Set.indicator_of_notMem
        (show ω ∉ {ω : S → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|} from hω)]
      exact bot_le
  calc ∫⁻ ω, Set.indicator {ω : S → (Fin n → ℝ) | t ≤ |ω i ⬝ᵥ ω j|}
          (fun ω ↦ ENNReal.ofReal |ω i ⬝ᵥ ω j|) ω ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-(a * t))) *
          (ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i)))
            + ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j)))) ∂μ := by
        refine lintegral_mono fun ω ↦ (hpt ω).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _),
          ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
    _ = ENNReal.ofReal (Real.exp (-(a * t)))
          * ∫⁻ ω, (ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω i ⬝ᵥ ω i)))
            + ENNReal.ofReal (Real.exp ((2 * a + 1) * (ω j ⬝ᵥ ω j)))) ∂μ :=
        lintegral_const_mul _ (hEi.add hEj)
    _ = _ := by rw [lintegral_add_left hEi]

end TailConsequences

/-! #### Georgii's `Ω_t` and (20.6)(iii) -/

section SlowGrowth

variable {D n : ℕ}

variable (D n) in
/-- **Georgii's `Ω_t = {|σ_i| ≤ t α(i) for all i ∈ S}`** of §20.1, written with the squares. -/
def slowGrowthSet (t : ℝ) : Set ((Fin D → ℤ) → (Fin n → ℝ)) :=
  {ω | ∀ i, ω i ⬝ᵥ ω i ≤ t ^ 2 * slowGrowth i ^ 2}

/-- **Georgii, Lemma (20.6)(iii).**  From the tail estimate at the rate `c ≥ a + d + 1`,

`μ(Ω_t^c) ≤ b · C_d · e^{-a t²}`  for `t ≥ 1`,  `C_d = ∑_{i ∈ ℤ^d} (e ∨ |i|)^{-(d+1)} < ∞`.

Georgii's `b₃(a)` is `b(a+d+1) C_d`.  The series is `summable_max_exp_norm_rpow`. -/
theorem measure_compl_slowGrowthSet_le {μ : Measure ((Fin D → ℤ) → (Fin n → ℝ))}
    {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : (D : ℝ) + 1 + a ≤ c)
    (htail : ∀ (i : Fin D → ℤ) (r : ℝ),
      μ {ω | r ≤ ω i ⬝ᵥ ω i} ≤ ENNReal.ofReal (b * Real.exp (-(c * r))))
    {t : ℝ} (ht : 1 ≤ t) :
    μ (slowGrowthSet D n t)ᶜ
      ≤ ENNReal.ofReal (b * (∑' i : Fin D → ℤ, (max (Real.exp 1) ‖i‖) ^ (-((D : ℝ) + 1)))
          * Real.exp (-(a * t ^ 2))) := by
  classical
  have hsum := summable_max_exp_norm_rpow (D := D) (p := (D : ℝ) + 1) (by linarith)
  have hnn : ∀ i : Fin D → ℤ, (0 : ℝ) ≤ (max (Real.exp 1) ‖i‖) ^ (-((D : ℝ) + 1)) := fun i ↦
    Real.rpow_nonneg (le_trans (Real.exp_pos 1).le (le_max_left _ _)) _
  have ht2 : (1 : ℝ) ≤ t ^ 2 := by nlinarith
  -- the termwise estimate
  have hterm : ∀ i : Fin D → ℤ, μ {ω | t ^ 2 * slowGrowth i ^ 2 ≤ ω i ⬝ᵥ ω i}
      ≤ ENNReal.ofReal (b * Real.exp (-(a * t ^ 2))
        * (max (Real.exp 1) ‖i‖) ^ (-((D : ℝ) + 1))) := by
    intro i
    refine (htail i _).trans (ENNReal.ofReal_le_ofReal ?_)
    set M : ℝ := max (Real.exp 1) ‖i‖ with hM
    have hMe : Real.exp 1 ≤ M := le_max_left _ _
    have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos 1) hMe
    have hM1 : (1 : ℝ) ≤ M := le_trans (Real.one_le_exp zero_le_one) hMe
    have hrew : Real.exp (-(c * (t ^ 2 * slowGrowth i ^ 2))) = M ^ (-(c * t ^ 2)) := by
      rw [Real.rpow_def_of_pos hMpos, slowGrowth_sq, ← hM]
      congr 1
      ring
    have hfac : M ^ (-(c * t ^ 2))
        = M ^ (-(a * t ^ 2)) * M ^ (-((c - a) * t ^ 2)) := by
      rw [← Real.rpow_add hMpos]
      congr 1
      ring
    have h1 : M ^ (-(a * t ^ 2)) ≤ Real.exp (-(a * t ^ 2)) := by
      have := Real.rpow_le_rpow_of_nonpos (Real.exp_pos 1) hMe
        (by nlinarith : -(a * t ^ 2) ≤ 0)
      rwa [Real.exp_one_rpow] at this
    have h2 : M ^ (-((c - a) * t ^ 2)) ≤ M ^ (-((D : ℝ) + 1)) := by
      refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
      nlinarith
    have h3 : (0 : ℝ) ≤ M ^ (-((c - a) * t ^ 2)) := Real.rpow_nonneg hMpos.le _
    have h4 : (0 : ℝ) ≤ M ^ (-(a * t ^ 2)) := Real.rpow_nonneg hMpos.le _
    rw [hrew, hfac]
    have hprod : M ^ (-(a * t ^ 2)) * M ^ (-((c - a) * t ^ 2))
        ≤ Real.exp (-(a * t ^ 2)) * M ^ (-((D : ℝ) + 1)) := by
      exact mul_le_mul h1 h2 h3 (Real.exp_nonneg _)
    nlinarith
  -- sum over the sites
  have hcover : (slowGrowthSet D n t)ᶜ
      ⊆ ⋃ i : Fin D → ℤ, {ω | t ^ 2 * slowGrowth i ^ 2 ≤ ω i ⬝ᵥ ω i} := by
    intro ω hω
    simp only [slowGrowthSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi⟩ := hω
    exact Set.mem_iUnion.2 ⟨i, hi.le⟩
  refine le_trans (measure_mono hcover) (le_trans (measure_iUnion_le _)
    (le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i ↦ by positivity)
    ((hsum.mul_left (b * Real.exp (-(a * t ^ 2)))))]
  congr 1
  rw [tsum_mul_left]
  ring

end SlowGrowth

end MeasureTheory.GibbsMeasure

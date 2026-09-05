/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.RealSingleton
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Poisson convergence for binomial distributions with a varying number of trials

Mathlib's Poisson limit theorem `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`
lets the number of trials be the sequence index itself: `n.choose k * p n ^ k * (1 - p n) ^ (n - k)`
converges to `exp (-r) * r ^ k / k!` when `n * p n → r`. Applications (the law of rare events along
an arbitrary sequence of trial numbers, e.g. Georgii, *Gibbs Measures and Phase Transitions*,
§11.2 and §11.4, where the number of trials is `x n` and the success probability `p ^ n`) need the
number of trials `x a : ℕ` and the success probability `p a` to be independent functions of the
index `a`, along an arbitrary filter. Here the hypothesis `x a * p a → r` no longer forces
`p a → 0` (take `x a = 1`), so it is assumed separately.

The pointwise convergence of the weights is upgraded to convergence of the binomial measures in
total variation, by Scheffé's lemma for series.

## Main results

* `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul`: the **Poisson limit theorem**,
  `(x a).choose k * p a ^ k * (1 - p a) ^ (x a - k) → exp (-r) * r ^ k / k!` when `x a * p a → r`
  and `p a → 0`.
* `ProbabilityTheory.tendsto_binomial_singleton_of_tendsto_mul`,
  `ProbabilityTheory.tendsto_binomial_real_singleton_of_tendsto_mul`: the same for the masses
  `Bin(x a, p a) {k} → Po(r) {k}`.
* `ProbabilityTheory.tendsto_tsum_abs_binomial_real_sub_of_tendsto_mul`: convergence in total
  variation, `∑' k, |Bin(x a, p a).real {k} - Po(r).real {k}| → 0`, and its setwise and uniform
  consequences `ProbabilityTheory.tendsto_binomial_of_tendsto_mul`,
  `ProbabilityTheory.tendsto_iSup_abs_binomial_real_sub_of_tendsto_mul`.

The general ingredients live where Mathlib keeps their relatives:
`Real.tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero`
(`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`), Scheffé's lemma for
series and Tannery's theorem for sums of growing length
(`GibbsMeasure/Mathlib/Analysis/Normed/Group/Tannery.lean`,
`GibbsMeasure/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`), and the real point-mass
decomposition of a finite measure on a countable space
(`GibbsMeasure/Mathlib/MeasureTheory/Measure/RealSingleton.lean`).
-/

@[expose] public section

open Filter Finset Set
open scoped Topology ENNReal NNReal

variable {α β : Type*} {l : Filter α}

/-! ### The Poisson limit theorem along an arbitrary sequence of trial numbers -/

/-- If `x a * p a → r` and `p a → 0`, then `(x a - i) * p a → r` as well, for every fixed `i`. The
subtraction is truncated in `ℕ`, so no relation between `x a` and `i` is needed. -/
lemma tendsto_natCast_sub_mul_of_tendsto_mul {x : α → ℕ} {p : α → ℝ} {r : ℝ}
    (hr : Tendsto (fun a ↦ (x a : ℝ) * p a) l (𝓝 r)) (hp : Tendsto p l (𝓝 0)) (i : ℕ) :
    Tendsto (fun a ↦ ((x a - i : ℕ) : ℝ) * p a) l (𝓝 r) := by
  have h0 : Tendsto (fun a ↦ ((x a - (x a - i) : ℕ) : ℝ) * p a) l (𝓝 0) := by
    refine squeeze_zero_norm (a := fun a ↦ (i : ℝ) * |p a|) (fun a ↦ ?_)
      (by simpa using hp.abs.const_mul (i : ℝ))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast]
    gcongr
    exact_mod_cast (show x a - (x a - i) ≤ i by omega)
  have : (fun a ↦ ((x a - i : ℕ) : ℝ) * p a)
      = fun a ↦ (x a : ℝ) * p a - ((x a - (x a - i) : ℕ) : ℝ) * p a := by
    ext a
    rw [Nat.cast_sub (Nat.sub_le _ _)]
    ring
  rw [this]
  simpa using hr.sub h0

namespace ProbabilityTheory

variable {x : α → ℕ} {r : ℝ}

/-- `x.choose k * p ^ k = (∏_{i < k} (x - i) p) / k!`, the form in which the Poisson limit of the
binomial coefficient is read off factor by factor. -/
lemma choose_mul_pow_eq_prod_div_factorial (x k : ℕ) (p : ℝ) :
    (x.choose k : ℝ) * p ^ k = (∏ i ∈ range k, ((x - i : ℕ) : ℝ) * p) / k.factorial := by
  have h : (k.factorial : ℝ) * x.choose k = ∏ i ∈ range k, ((x - i : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  rw [prod_mul_distrib, prod_const, card_range, ← h, eq_div_iff (by positivity)]
  ring

/-- If `x a * p a → r` and `p a → 0`, then `(x a).choose k * p a ^ k → r ^ k / k!`. -/
lemma tendsto_choose_mul_pow_of_tendsto_mul_of_tendsto_zero {p : α → ℝ}
    (hr : Tendsto (fun a ↦ (x a : ℝ) * p a) l (𝓝 r)) (hp : Tendsto p l (𝓝 0)) (k : ℕ) :
    Tendsto (fun a ↦ (x a).choose k * p a ^ k) l (𝓝 (r ^ k / k.factorial)) := by
  simp_rw [choose_mul_pow_eq_prod_div_factorial]
  have : Tendsto (fun a ↦ ∏ i ∈ range k, ((x a - i : ℕ) : ℝ) * p a) l
      (𝓝 (∏ i ∈ range k, r)) :=
    tendsto_finsetProd _ fun i _ ↦ tendsto_natCast_sub_mul_of_tendsto_mul hr hp i
  simpa using this.div_const (k.factorial : ℝ)

/-- **Poisson limit theorem** (law of rare events) along an arbitrary sequence of trial numbers:
if `x a * p a → r` and `p a → 0`, then the binomial weights
`(x a).choose k * p a ^ k * (1 - p a) ^ (x a - k)` converge to the Poisson weight
`exp (-r) * r ^ k / k!`.

`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop` is the special case `x n = n`,
where `p n → 0` follows from `n * p n → r`. -/
theorem tendsto_choose_mul_pow_of_tendsto_mul {p : α → ℝ}
    (hr : Tendsto (fun a ↦ (x a : ℝ) * p a) l (𝓝 r)) (hp : Tendsto p l (𝓝 0)) (k : ℕ) :
    Tendsto (fun a ↦ (x a).choose k * p a ^ k * (1 - p a) ^ (x a - k)) l
      (𝓝 (Real.exp (-r) * r ^ k / k.factorial)) := by
  have h1 := tendsto_choose_mul_pow_of_tendsto_mul_of_tendsto_zero hr hp k
  have h2 : Tendsto (fun a ↦ (1 - p a) ^ (x a - k)) l (𝓝 (Real.exp (-r))) := by
    have hx' : Tendsto (fun a ↦ ((x a - k : ℕ) : ℝ) * -p a) l (𝓝 (-r)) := by
      simpa only [mul_neg] using (tendsto_natCast_sub_mul_of_tendsto_mul hr hp k).neg
    simpa only [sub_eq_add_neg] using
      Real.tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero hx' (by simpa using hp.neg)
  have := h1.mul h2
  rwa [show r ^ k / k.factorial * Real.exp (-r) = Real.exp (-r) * r ^ k / k.factorial by ring]
    at this

open scoped unitInterval in
/-- The Poisson limit theorem for the masses of the binomial distributions: if `x a * p a → r` and
`p a → 0`, then `Bin(x a, p a).real {k} → Po(r).real {k}`. -/
theorem tendsto_binomial_real_singleton_of_tendsto_mul {p : α → I} {r : ℝ≥0}
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) (k : ℕ) :
    Tendsto (fun a ↦ Bin(x a, p a).real {k}) l (𝓝 (Po(r).real {k})) := by
  simp_rw [binomial_real_singleton, poissonMeasure_real_singleton]
  exact tendsto_choose_mul_pow_of_tendsto_mul hr hp k

open scoped unitInterval in
/-- The Poisson limit theorem for the masses of the binomial distributions, in `ℝ≥0∞`: if
`x a * p a → r` and `p a → 0`, then `Bin(x a, p a) {k} → Po(r) {k}`. -/
theorem tendsto_binomial_singleton_of_tendsto_mul {p : α → I} {r : ℝ≥0}
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) (k : ℕ) :
    Tendsto (fun a ↦ Bin(x a, p a) {k}) l (𝓝 (Po(r) {k})) := by
  simp_rw [binomial_singleton, poissonMeasure_singleton]
  exact ENNReal.tendsto_ofReal (tendsto_choose_mul_pow_of_tendsto_mul hr hp k)

end ProbabilityTheory

/-! ### Total variation convergence of the binomial distributions to the Poisson distribution -/

namespace ProbabilityTheory

open scoped unitInterval

variable {x : α → ℕ} {p : α → I} {r : ℝ≥0}

/-- **Poisson convergence in total variation.** If `x a * p a → r` and `p a → 0`, then
`Bin(x a, p a) → Po(r)` in total variation: `∑' k, |Bin(x a, p a).real {k} - Po(r).real {k}| → 0`.
This is the Poisson limit theorem upgraded by Scheffé's lemma. -/
theorem tendsto_tsum_abs_binomial_real_sub_of_tendsto_mul
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) :
    Tendsto (fun a ↦ ∑' k, |Bin(x a, p a).real {k} - Po(r).real {k}|) l (𝓝 0) :=
  MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto'
    (tendsto_binomial_real_singleton_of_tendsto_mul hr hp)

/-- **Poisson convergence, uniformly over sets.** If `x a * p a → r` and `p a → 0`, then
`sup_s |Bin(x a, p a).real s - Po(r).real s| → 0`. -/
theorem tendsto_iSup_abs_binomial_real_sub_of_tendsto_mul
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) :
    Tendsto (fun a ↦ ⨆ s : Set ℕ, |Bin(x a, p a).real s - Po(r).real s|) l (𝓝 0) := by
  refine squeeze_zero (fun a ↦ Real.iSup_nonneg fun s ↦ abs_nonneg _) (fun a ↦ ciSup_le fun s ↦ ?_)
    (tendsto_tsum_abs_binomial_real_sub_of_tendsto_mul hr hp)
  exact MeasureTheory.abs_measureReal_sub_le_tsum_abs _ _ s

/-- **Poisson convergence, setwise.** If `x a * p a → r` and `p a → 0`, then
`Bin(x a, p a).real s → Po(r).real s` for every set `s` of natural numbers. -/
theorem tendsto_binomial_real_of_tendsto_mul
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) (s : Set ℕ) :
    Tendsto (fun a ↦ Bin(x a, p a).real s) l (𝓝 (Po(r).real s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun a ↦ norm_nonneg _) (fun a ↦ ?_)
    (tendsto_tsum_abs_binomial_real_sub_of_tendsto_mul hr hp)
  exact MeasureTheory.abs_measureReal_sub_le_tsum_abs _ _ s

/-- **Poisson convergence, setwise**, in `ℝ≥0∞`: if `x a * p a → r` and `p a → 0`, then
`Bin(x a, p a) s → Po(r) s` for every set `s` of natural numbers. -/
theorem tendsto_binomial_of_tendsto_mul
    (hr : Tendsto (fun a ↦ (x a : ℝ) * (p a : ℝ)) l (𝓝 r))
    (hp : Tendsto (fun a ↦ (p a : ℝ)) l (𝓝 0)) (s : Set ℕ) :
    Tendsto (fun a ↦ Bin(x a, p a) s) l (𝓝 (Po(r) s)) := by
  have h := ENNReal.tendsto_ofReal (tendsto_binomial_real_of_tendsto_mul hr hp s)
  simpa only [MeasureTheory.measureReal_def,
    ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top _ _)] using h

end ProbabilityTheory

end

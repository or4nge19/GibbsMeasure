/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
total variation, by Scheffé's lemma for series (a consequence of Tannery's theorem).

## Main results

* `Real.tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero`:
  `(1 + g a) ^ x a → exp t` when `x a * g a → t` and `g a → 0`; the version of
  `Real.tendsto_one_add_pow_exp_of_tendsto` with an arbitrary natural exponent.
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
* `tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum`: **Scheffé's lemma for series**: pointwise
  convergence of nonnegative summable families together with convergence of their sums gives
  convergence in `ℓ¹`; `MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto` is
  the version for finite measures on a countable space.
* `tendsto_finsetSum_of_dominated_convergence`,
  `ENNReal.tendsto_finsetSum_of_dominated_convergence`: Tannery's theorem for finite sums over a
  growing family of finite sets, the form of dominated convergence needed for renewal series
  `∑_{k < n} f n k` whose length grows with the index (`tendsto_sum_range_of_dominated_convergence`,
  `ENNReal.tendsto_sum_range_of_dominated_convergence`).
-/

@[expose] public section

open Filter Finset Set
open scoped Topology ENNReal NNReal

variable {α β : Type*} {l : Filter α}

/-! ### `(1 + g a) ^ x a → exp t` -/

namespace Real

/-- The limit of `(1 + g a) ^ x a` is `exp t` when `x a * g a → t` and `g a → 0`. This is
`Real.tendsto_one_add_pow_exp_of_tendsto` with an arbitrary natural exponent `x a` in place of
the index `n`; since `x` need not tend to infinity, `g → 0` is assumed rather than derived. -/
lemma tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero {x : α → ℕ} {g : α → ℝ} {t : ℝ}
    (hx : Tendsto (fun a ↦ (x a : ℝ) * g a) l (𝓝 t)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun a ↦ (1 + g a) ^ x a) l (𝓝 (exp t)) := by
  have hsmall : ∀ᶠ a in l, g a ∈ Ioo (-1 / 2 : ℝ) (1 / 2) :=
    hg.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  -- `x a * log (1 + g a) → t`: the error `x a * (log (1 + g a) - g a)` is `O(|x a g a| |g a|)`.
  have hlog : Tendsto (fun a ↦ (x a : ℝ) * log (1 + g a)) l (𝓝 t) := by
    have herr : Tendsto (fun a ↦ (x a : ℝ) * (log (1 + g a) - g a)) l (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun a ↦ |(x a : ℝ) * g a| * (|g a| / (1 - |g a|))) ?_ ?_
      · filter_upwards [hsmall] with a ha
        have hg1 : |g a| < 1 := by rw [abs_lt]; constructor <;> linarith [ha.1, ha.2]
        have hbound := abs_log_sub_add_sum_range_le (x := -g a) (by rwa [abs_neg]) 1
        simp only [sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, sub_neg_eq_add,
          abs_neg] at hbound
        have hb : |log (1 + g a) - g a| ≤ |g a| ^ 2 / (1 - |g a|) := by
          rw [← neg_add_eq_sub]; simpa using hbound
        calc ‖(x a : ℝ) * (log (1 + g a) - g a)‖ = |(x a : ℝ)| * |log (1 + g a) - g a| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ |(x a : ℝ)| * (|g a| ^ 2 / (1 - |g a|)) :=
              mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = |(x a : ℝ) * g a| * (|g a| / (1 - |g a|)) := by rw [abs_mul]; ring
      · have h1 : Tendsto (fun a ↦ 1 - |g a|) l (𝓝 (1 - |(0 : ℝ)|)) :=
          tendsto_const_nhds.sub hg.abs
        have h0 : Tendsto (fun a ↦ |g a| / (1 - |g a|)) l (𝓝 (|(0 : ℝ)| / (1 - |(0 : ℝ)|))) :=
          hg.abs.div h1 (by simp)
        simpa using hx.abs.mul h0
    have : (fun a ↦ (x a : ℝ) * log (1 + g a))
        = fun a ↦ (x a : ℝ) * g a + (x a : ℝ) * (log (1 + g a) - g a) := by
      ext a; ring
    rw [this]
    simpa using hx.add herr
  refine ((continuous_exp.tendsto t).comp hlog).congr' ?_
  filter_upwards [hsmall] with a ha
  have h1 : 0 < 1 + g a := by linarith [ha.1]
  simp only [Function.comp_apply]
  rw [← log_pow, exp_log (pow_pos h1 _)]

end Real

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

/-! ### Scheffé's lemma for series -/

/-- **Scheffé's lemma for series.** If nonnegative summable families `f a` converge pointwise to a
nonnegative summable `g`, and their sums converge to the sum of `g`, then `f a → g` in `ℓ¹`:
`∑' b, |f a b - g b| → 0`.

This is Scheffé's lemma for the counting measure; like Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`), from which it is deduced, it holds along an arbitrary
filter. The proof writes `|f - g| = 2 (g - f)⁺ + (f - g)`: the first term is dominated by `g`. -/
theorem tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum {f : α → β → ℝ} {g : β → ℝ}
    (hf : ∀ᶠ a in l, ∀ b, 0 ≤ f a b) (hg : ∀ b, 0 ≤ g b)
    (hfs : ∀ᶠ a in l, Summable (f a)) (hgs : Summable g)
    (h : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (hsum : Tendsto (fun a ↦ ∑' b, f a b) l (𝓝 (∑' b, g b))) :
    Tendsto (fun a ↦ ∑' b, |f a b - g b|) l (𝓝 0) := by
  -- the positive parts `(g - f a)⁺` are dominated by `g` and tend to `0` pointwise
  have hpos : Tendsto (fun a ↦ ∑' b, max (g b - f a b) 0) l (𝓝 0) := by
    have hb : ∀ b, Tendsto (fun a ↦ max (g b - f a b) 0) l (𝓝 0) := fun b ↦ by
      simpa using ((tendsto_const_nhds (x := g b)).sub (h b)).max
        (tendsto_const_nhds (x := (0 : ℝ)))
    have := tendsto_tsum_of_dominated_convergence (𝓕 := l) (f := fun a b ↦ max (g b - f a b) 0)
      (g := fun _ ↦ 0) (bound := g) hgs hb ?_
    · simpa using this
    · filter_upwards [hf] with a ha b
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [ha b]) (hg b)
  have hid : ∀ a, (∀ b, 0 ≤ f a b) → Summable (f a) →
      ∑' b, |f a b - g b| = 2 * ∑' b, max (g b - f a b) 0 + (∑' b, f a b - ∑' b, g b) := by
    intro a ha hs
    have hmax : Summable fun b ↦ max (g b - f a b) 0 :=
      hgs.of_nonneg_of_le (fun b ↦ le_max_right _ _) fun b ↦ max_le (by linarith [ha b]) (hg b)
    rw [← tsum_mul_left, ← hs.tsum_sub hgs, ← (hmax.mul_left 2).tsum_add (hs.sub hgs)]
    refine tsum_congr fun b ↦ ?_
    rcases le_total (g b) (f a b) with hle | hle
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
  have : Tendsto (fun a ↦ 2 * ∑' b, max (g b - f a b) 0 + (∑' b, f a b - ∑' b, g b)) l (𝓝 0) := by
    simpa using (hpos.const_mul 2).add (hsum.sub_const (∑' b, g b))
  refine this.congr' ?_
  filter_upwards [hf, hfs] with a ha hs
  exact (hid a ha hs).symm

/-- A finite measure on a countable space with measurable singletons is the sum of its point
masses: `HasSum (fun b ↦ μ.real {b}) (μ.real univ)`. -/
lemma MeasureTheory.hasSum_measureReal_singleton [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ] :
    HasSum (fun b ↦ μ.real {b}) (μ.real univ) := by
  have h := μ.tsum_indicator_apply_singleton univ MeasurableSet.univ
  simp only [indicator_univ] at h
  have hne : ∑' b, μ {b} ≠ ∞ := by rw [h]; exact MeasureTheory.measure_ne_top μ _
  have := (ENNReal.summable_toReal hne).hasSum
  rwa [← ENNReal.tsum_toReal_eq (fun b ↦ MeasureTheory.measure_ne_top μ _), h] at this

/-- The real mass of any set of a finite measure on a countable space with measurable singletons
is the sum of the point masses it contains. -/
lemma MeasureTheory.measureReal_eq_tsum_indicator [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ]
    (s : Set β) : μ.real s = ∑' b, s.indicator (fun b ↦ μ.real {b}) b := by
  have h := μ.tsum_indicator_apply_singleton s s.to_countable.measurableSet
  have hne : ∀ b, s.indicator (fun b ↦ μ {b}) b ≠ ∞ := fun b ↦
    ne_top_of_le_ne_top (MeasureTheory.measure_ne_top μ {b}) (indicator_le_self _ _ b)
  rw [MeasureTheory.measureReal_def, ← h, ENNReal.tsum_toReal_eq hne]
  refine tsum_congr fun b ↦ ?_
  simp only [MeasureTheory.measureReal_def]
  by_cases hb : b ∈ s
  · rw [indicator_of_mem hb, indicator_of_mem hb]
  · rw [indicator_of_notMem hb, indicator_of_notMem hb, ENNReal.toReal_zero]

/-- The difference of two finite measures on any set is bounded by their `ℓ¹` distance on
singletons. -/
lemma MeasureTheory.abs_measureReal_sub_le_tsum_abs [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] (μ ν : MeasureTheory.Measure β) [MeasureTheory.IsFiniteMeasure μ]
    [MeasureTheory.IsFiniteMeasure ν] (s : Set β) :
    |μ.real s - ν.real s| ≤ ∑' b, |μ.real {b} - ν.real {b}| := by
  have hμ := (MeasureTheory.hasSum_measureReal_singleton μ).summable
  have hν := (MeasureTheory.hasSum_measureReal_singleton ν).summable
  have hd : Summable fun b ↦
      s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b :=
    (hμ.indicator s).sub (hν.indicator s)
  rw [MeasureTheory.measureReal_eq_tsum_indicator μ, MeasureTheory.measureReal_eq_tsum_indicator ν,
    ← (hμ.indicator s).tsum_sub (hν.indicator s)]
  calc |∑' b, (s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b)|
      ≤ ∑' b, |s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b| := by
        have := norm_tsum_le_tsum_norm (f := fun b ↦
          s.indicator (fun b ↦ μ.real {b}) b - s.indicator (fun b ↦ ν.real {b}) b)
          (by simpa only [Real.norm_eq_abs] using hd.abs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' b, |μ.real {b} - ν.real {b}| :=
        hd.abs.tsum_le_tsum (fun b ↦ by by_cases hb : b ∈ s <;> simp [hb]) (hμ.sub hν).abs

/-- **Scheffé's lemma for finite measures on a countable space.** If finite measures `μ a`
converge to a finite measure `ν` on every singleton and in total mass, then they converge in total
variation: `∑' b, |(μ a).real {b} - ν.real {b}| → 0`. For probability measures the total-mass
hypothesis is automatic; see `tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto'`. -/
theorem MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {μ : α → MeasureTheory.Measure β}
    {ν : MeasureTheory.Measure β} [∀ a, MeasureTheory.IsFiniteMeasure (μ a)]
    [MeasureTheory.IsFiniteMeasure ν]
    (h : ∀ b, Tendsto (fun a ↦ (μ a).real {b}) l (𝓝 (ν.real {b})))
    (huniv : Tendsto (fun a ↦ (μ a).real univ) l (𝓝 (ν.real univ))) :
    Tendsto (fun a ↦ ∑' b, |(μ a).real {b} - ν.real {b}|) l (𝓝 0) := by
  refine tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum (Eventually.of_forall fun a b ↦
    MeasureTheory.measureReal_nonneg) (fun b ↦ MeasureTheory.measureReal_nonneg)
    (Eventually.of_forall fun a ↦ (MeasureTheory.hasSum_measureReal_singleton (μ a)).summable)
    (MeasureTheory.hasSum_measureReal_singleton ν).summable h ?_
  simp_rw [(MeasureTheory.hasSum_measureReal_singleton _).tsum_eq]
  exact huniv

/-- **Scheffé's lemma for probability measures on a countable space.** Probability measures
converging on every singleton converge in total variation. -/
theorem MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto' [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] {μ : α → MeasureTheory.Measure β}
    {ν : MeasureTheory.Measure β} [∀ a, MeasureTheory.IsProbabilityMeasure (μ a)]
    [MeasureTheory.IsProbabilityMeasure ν]
    (h : ∀ b, Tendsto (fun a ↦ (μ a).real {b}) l (𝓝 (ν.real {b}))) :
    Tendsto (fun a ↦ ∑' b, |(μ a).real {b} - ν.real {b}|) l (𝓝 0) :=
  MeasureTheory.tendsto_tsum_abs_measureReal_singleton_sub_of_tendsto h
    (by simpa using (tendsto_const_nhds : Tendsto (fun _ : α ↦ (1 : ℝ)) l (𝓝 1)))

/-! ### Tannery's theorem for sums over a growing family of finite sets -/

/-- **Tannery's theorem for finite sums of growing length.** If the finite sets `s a` eventually
contain every index, `f a b → g b` for every `b`, and `‖f a b‖ ≤ bound b` for `b ∈ s a` with `bound`
summable, then `∑ b ∈ s a, f a b → ∑' b, g b`. This is the dominated convergence theorem for
renewal-type series `∑_{k < n} f n k` whose length grows with the index. -/
theorem tendsto_finsetSum_of_dominated_convergence {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] {s : α → Finset β} {f : α → β → G} {g : β → G} {bound : β → ℝ}
    (h_sum : Summable bound) (hs : ∀ b, ∀ᶠ a in l, b ∈ s a)
    (hab : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (h_bound : ∀ᶠ a in l, ∀ b ∈ s a, ‖f a b‖ ≤ bound b) :
    Tendsto (fun a ↦ ∑ b ∈ s a, f a b) l (𝓝 (∑' b, g b)) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hbound0 : ∀ b, 0 ≤ bound b := fun b ↦ by
    obtain ⟨a, ha, hb⟩ := ((hs b).and h_bound).exists
    exact (norm_nonneg _).trans (hb b ha)
  rw [show (fun a ↦ ∑ b ∈ s a, f a b) = fun a ↦ ∑' b, (↑(s a) : Set β).indicator (f a) b from
    funext fun a ↦ sum_eq_tsum_indicator _ _]
  refine tendsto_tsum_of_dominated_convergence h_sum (fun b ↦ (hab b).congr' ?_) ?_
  · filter_upwards [hs b] with a ha
    exact (indicator_of_mem (Finset.mem_coe.2 ha) _).symm
  · filter_upwards [h_bound] with a ha b
    by_cases hb : b ∈ s a
    · rw [indicator_of_mem (Finset.mem_coe.2 hb)]; exact ha b hb
    · rw [indicator_of_notMem (Finset.mem_coe.not.2 hb), norm_zero]; exact hbound0 b

/-- **Tannery's theorem for finite sums of growing length**, in `ℝ≥0∞`: if the finite sets `s a`
eventually contain every index, `f a b → g b` for every `b`, and `f a b ≤ bound b` for `b ∈ s a`
with `∑' b, bound b < ∞`, then `∑ b ∈ s a, f a b → ∑' b, g b`. -/
theorem ENNReal.tendsto_finsetSum_of_dominated_convergence {s : α → Finset β}
    {f : α → β → ℝ≥0∞} {g : β → ℝ≥0∞} {bound : β → ℝ≥0∞} (h_sum : ∑' b, bound b ≠ ∞)
    (hs : ∀ b, ∀ᶠ a in l, b ∈ s a) (hab : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (h_bound : ∀ᶠ a in l, ∀ b ∈ s a, f a b ≤ bound b) :
    Tendsto (fun a ↦ ∑ b ∈ s a, f a b) l (𝓝 (∑' b, g b)) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hbt : ∀ b, bound b ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top h_sum
  have hgb : ∀ b, g b ≤ bound b := fun b ↦
    le_of_tendsto (hab b) <| by filter_upwards [hs b, h_bound] with a ha hb using hb b ha
  have hgt : ∀ b, g b ≠ ∞ := fun b ↦ ne_top_of_le_ne_top (hbt b) (hgb b)
  have hgs : ∑' b, g b ≠ ∞ := ne_top_of_le_ne_top h_sum (ENNReal.tsum_le_tsum hgb)
  have hreal : Tendsto (fun a ↦ ∑ b ∈ s a, (f a b).toReal) l (𝓝 (∑' b, (g b).toReal)) := by
    refine _root_.tendsto_finsetSum_of_dominated_convergence (bound := fun b ↦ (bound b).toReal)
      (ENNReal.summable_toReal h_sum) hs
      (fun b ↦ (ENNReal.tendsto_toReal (hgt b)).comp (hab b)) ?_
    filter_upwards [h_bound] with a ha b hb
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hbt b) (ha b hb)
  rw [← ENNReal.ofReal_toReal hgs, ENNReal.tsum_toReal_eq hgt]
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [h_bound] with a ha
  rw [← ENNReal.toReal_sum fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb),
    ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb))]

/-- Tannery's theorem for `∑ k ∈ range n, f n k`: if `f n k → g k` for every `k` and
`‖f n k‖ ≤ bound k` for `k < n` with `bound` summable, then `∑ k < n, f n k → ∑' k, g k`. -/
theorem tendsto_sum_range_of_dominated_convergence {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] {f : ℕ → ℕ → G} {g : ℕ → G} {bound : ℕ → ℝ} (h_sum : Summable bound)
    (hab : ∀ k, Tendsto (f · k) atTop (𝓝 (g k)))
    (h_bound : ∀ᶠ n in atTop, ∀ k < n, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∑ k ∈ range n, f n k) atTop (𝓝 (∑' k, g k)) :=
  tendsto_finsetSum_of_dominated_convergence h_sum (fun k ↦ by
    simpa using eventually_gt_atTop k) hab (by simpa using h_bound)

/-- Tannery's theorem for `∑ k ∈ range n, f n k` in `ℝ≥0∞`: if `f n k → g k` for every `k` and
`f n k ≤ bound k` for `k < n` with `∑' k, bound k < ∞`, then `∑ k < n, f n k → ∑' k, g k`. -/
theorem ENNReal.tendsto_sum_range_of_dominated_convergence {f : ℕ → ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞}
    {bound : ℕ → ℝ≥0∞} (h_sum : ∑' k, bound k ≠ ∞) (hab : ∀ k, Tendsto (f · k) atTop (𝓝 (g k)))
    (h_bound : ∀ᶠ n in atTop, ∀ k < n, f n k ≤ bound k) :
    Tendsto (fun n ↦ ∑ k ∈ range n, f n k) atTop (𝓝 (∑' k, g k)) :=
  ENNReal.tendsto_finsetSum_of_dominated_convergence h_sum (fun k ↦ by
    simpa using eventually_gt_atTop k) hab (by simpa using h_bound)

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

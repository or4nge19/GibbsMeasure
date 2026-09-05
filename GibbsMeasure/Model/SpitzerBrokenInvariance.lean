/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SpitzerCox
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix.FirstPassage
public import GibbsMeasure.Mathlib.Probability.Distributions.Poisson.Convergence
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Georgii §11.4: Spitzer's example of totally broken shift-invariance

State space `E = ℤ₊ = ℕ`, sites `ℤ`. Fix `0 < p < 1` and a strictly positive probability vector
`α` on `ℕ`, and let (Georgii (11.43))

`P(x, y) = ℓ(x, p, y)` for `x ≥ 1`,  `P(0, y) = α(y)`,

the population in which each inhabitant survives with probability `p` and, at the time of
extinction, a new population of size distribution `α` immigrates. `P` is not positive, so Georgii
works with `Q = P²`, which is: `Q(x, y) ≥ P(x, 0) P(0, y) > 0`.

**Georgii Theorem (11.46).** If `α` is chosen so that `P` (hence `Q`) is null recurrent, then
`|ex 𝒢(Q)| = ∞` while `θ_j(μ) ≠ μ` for every `j ≠ 0` and every `μ ∈ 𝒢(Q)`.

## What is here, and what is not

**Theorem (11.46) is proved in full**, at the level of generality at which Georgii states it:
`matrix_pos`, `tsum_matrix` and `isTransferMatrix` put Spitzer's `Q = P²` into the framework of
§11.1, and `map_shift_ne`, `infinite_extremePoints_G` are Georgii's two conclusions, deduced from
Corollary (11.14) through the general theorems
`MeasureTheory.GibbsMeasure.Markov.map_shift_ne_of_not_exists_isPositiveRecurrent` and
`…infinite_extremePoints_G_of_nonempty_of_not_exists_isPositiveRecurrent`
(`GibbsMeasure/Model/BoundaryLawPhaseTransition.lean`).

Georgii's *hypothesis* on `α` — "`α` is chosen in such a way that `P` is null recurrent" — is
carried by the two theorems in the explicit form `μ_P^0(τ) = ∞`,

`∑ₙ ∑_y Tⁿ(0, y) = ∞`  for the taboo matrix `T` of `P` at the state `0`,

and `exists_null_recurrent` shows that it is satisfiable: it builds a strictly positive
probability vector `α` for which it holds, by Georgii's argument (a sparse sequence of test
states `x_k` with `μ_P^{x_k}(τ) ≥ 4^k` carrying mass `α(x_k) ≥ 2^{-k-2}`). The hypothesis is
*not* removable: for a positive recurrent `Q` the conclusions of (11.46) are false, as Georgii
notes at the end of §11.4.

The four steps of Georgii's proof:

* **Step 1** (recurrence, and null recurrence for a suitable `α`). The pure-survival matrix `P̃`
  of (11.44) and its powers (11.45) `P̃^n(x, y) = ℓ(x, p^n, y)`; the extinction-time law
  `μ_P^x(τ = m+1) = (1 - p^{m+1})^x - (1 - p^m)^x`, `μ_P^x(τ ≤ n) = (1 - p^n)^x` for `x ≥ 1`
  (`firstPassage_step_add`, `sum_firstPassage_step`), hence `μ_P^0(τ < ∞) = 1`
  (`tsum_firstPassage_step_zero`) and the recurrence of `P` and of `Q = P²`
  (`potential_step_eq_top`, `isRecurrent_matrix`). Null recurrence rules out an invariant
  probability vector through **Kac's inequality**
  (`ProbabilityTheory.Kernel.mul_tsum_tsum_taboo_pow_le_of_invariant`, applied to the invariant
  vector `v + vP` of `P` obtained from one of `Q = P²`): `not_isPositiveRecurrent_matrix`.
  Georgii's Remark (11.7) then gives `not_exists_isPositiveRecurrent`, i.e. `𝒢_Θ(Q) = ∅`.
* **Step 2** (the limit rows). The renewal decomposition (11.47) — in the general form
  `ProbabilityTheory.Kernel.ofMatrix_pow_apply_singleton_eq_taboo_add`
  (`GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix/FirstPassage.lean`), specialised to
  `P` in `step_pow_apply_singleton` and `step_pow_apply_singleton_of_ne_zero` — combined with the
  Poisson convergence theorem
  (`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul`,
  `GibbsMeasure/Mathlib/Probability/Distributions/Poisson/Convergence.lean`) and dominated
  convergence for the renewal series gives `P^n(x_n, ·) → α_c` whenever `x_n p^n → c > 0` from
  above (`tendsto_step_pow_apply_singleton`).
* **Steps 3–4** (the entrance law). Fatou plus `isEntranceLaw_of_forall_tsum_le` gives
  `isEntranceLaw_step` and `isEntranceLaw_matrix`, and Theorem (11.9)(a) turns the entrance law
  into a Gibbs measure: `nonempty_G`, which needs no hypothesis on `α` beyond positivity.

What is **not** here: Georgii's closing remarks of §11.4 — that `θ_j(μ^c) = μ^{c p^{-2j}}`, that
`μ^c(lim_{i → -∞} σ_i p^{-2i} = c) = 1`, and hence that `ex 𝒢(Q)` is *uncountable*. Those need
the Borel–Cantelli argument of Step 3 of Theorem (11.31), which is not formalised (see
`GibbsMeasure/Model/SpitzerCox.lean`). `infinite_extremePoints_G` is Georgii's stated
`|ex 𝒢(Q)| = ∞`.

The `ℓ(x, p, ·)` weights, Georgii (11.20), and the identities (11.22)–(11.25) live in
`GibbsMeasure/Model/SpitzerCox.lean`.

## Main declarations

* `stepReal`, `step` — **Georgii (11.43)**; `noImmigration` — **Georgii (11.44)**;
  `noImmigration_pow_apply_singleton` — **Georgii (11.45)**.
* `taboo_step_pow_apply_singleton`, `taboo_noImmigration_pow_apply_singleton`,
  `step_pow_apply_singleton` — **Georgii (11.47)** for `P`.
* `firstPassage_step_add`, `sum_firstPassage_step` — the extinction-time law of §11.4, Step 2.
* `matrix`, `matrix_pos`, `tsum_matrix`, `isTransferMatrix` — Spitzer's `Q = P²` as a transfer
  matrix.
* `tsum_firstPassage_step`, `tsum_firstPassage_step_zero`, `potential_step_eq_top`,
  `isRecurrent_matrix` — `P` and `Q = P²` are recurrent.
* `not_isPositiveRecurrent_matrix`, `not_exists_isPositiveRecurrent` — null recurrence of `Q`
  through Kac's inequality, and **Georgii Remark (11.7)** for Spitzer's `Q`.
* `tsum_taboo_step_pow_add`, `half_le_tsum_taboo_step_pow`, `le_tsum_tsum_taboo_step_pow`,
  `extinctionSeq`, `immigrationWeight`, `exists_null_recurrent` — **Georgii §11.4, Step 1**:
  `μ_P^x(τ) → ∞` and a strictly positive probability vector `α` making `P` null recurrent.
* `map_shift_ne`, `infinite_extremePoints_G` — **Georgii Theorem (11.46)**.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov.Spitzer

open SpitzerCox

/-- **Georgii (11.43).** `P(x, y) = ℓ(x, p, y)` for `x ≥ 1` and `P(0, y) = α(y)`. -/
def stepReal (p : ℝ) (α : ℕ → ℝ) (x y : ℕ) : ℝ :=
  if x = 0 then α y else binomialWeight x p y

/-- **Georgii (11.43)** as an `ℝ≥0∞`-valued matrix on `E = ℤ₊ = ℕ`. -/
def step (p : ℝ) (α : ℕ → ℝ) (x y : ℕ) : ℝ≥0∞ := ENNReal.ofReal (stepReal p α x y)

/-- **Georgii's `Q = P²`.** `P` itself is not positive (it is `0` off the "survivors" range),
so §11.1 is applied to its square. -/
def matrix (p : ℝ) (α : ℕ → ℝ) (x y : ℕ) : ℝ≥0∞ :=
  (Kernel.ofMatrix (step p α) ^ 2) x {y}

/-- Georgii's limiting extinction weights (§11.4, Step 2):
`g_k(c) = e^{-c p^{-k}} - e^{-c p^{-k-1}}`. Along a sequence `(x_n)` in `E` with `x_n p^n → c`
these are the limits `lim_n μ_P^{x_n}(τ = n - k)` of the extinction-time law. -/
def entranceWeight (p c : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(c / p ^ k)) - Real.exp (-(c / p ^ (k + 1))))

/-- **Georgii §11.4, Step 2.** The entrance vector

`α_c = 𝔭(c, ·) 1_{· ≠ 0} + ∑_{k ≥ 0} g_k(c) P^k(0, ·)`,

the limit of the rows `P^n(x_n, ·)` along any sequence with `x_n p^n → c` and `x_n p^n ≥ c`
(`tendsto_step_pow_apply_singleton`): the surviving part of the initial population becomes a
`Poisson(c)` population (unless it dies out), and the population that has already died out
restarts with the immigration row `α`, `k` steps before the end. -/
def entranceVector (p : ℝ) (α : ℕ → ℝ) (c : ℝ) (y : ℕ) : ℝ≥0∞ :=
  (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y))
    + ∑' k : ℕ, entranceWeight p c k * (Kernel.ofMatrix (step p α) ^ k) 0 {y}

/-- Georgii's choice of the sequence `(x_n)` in §11.4, Step 2: `x_n = ⌈c p^{-n}⌉`, the smallest
state with `x_n p^n ≥ c`; then also `x_n p^n → c`. -/
def entranceSeq (p c : ℝ) (n : ℕ) : ℕ := ⌈c / p ^ n⌉₊

variable {p : ℝ} {α : ℕ → ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hα : ∀ y, 0 < α y)
  (hαs : Summable α) (hα1 : ∑' y, α y = 1)

include hp0 hp1 hα

/-- **Georgii (11.44).** The pure-survival matrix `P̃(x, y) = ℓ(x, p, y)`: the same population
as `P`, with every inhabitant surviving independently with probability `p`, but with no
immigration at the time of extinction. It agrees with `P` off the state `0`
(`step_eq_noImmigration`). -/
def noImmigration (p : ℝ) (x y : ℕ) : ℝ≥0∞ := ENNReal.ofReal (binomialWeight x p y)

omit hp0 hp1 hα in
/-- `P` and `P̃` differ only in the row of the state `0`. -/
lemma step_eq_noImmigration {x : ℕ} (hx : x ≠ 0) (y : ℕ) :
    step p α x y = noImmigration p x y := by
  simp [step, stepReal, noImmigration, hx]

omit hα in
lemma tsum_noImmigration (x : ℕ) : ∑' y : ℕ, noImmigration p x y = 1 := by
  simp only [noImmigration]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ binomialWeight_nonneg hp0.le hp1.le x y)
    (summable_binomialWeight p x), (hasSum_binomialWeight p x).tsum_eq, ENNReal.ofReal_one]

omit hα in
/-- **Georgii (11.45).** `P̃^n(x, y) = ℓ(x, p^n, y)`: surviving `n` time units independently with
probability `p` each is surviving with probability `p^n`. This is Georgii (11.23) iterated; it
also holds for `n = 0`, where `ℓ(x, 1, ·) = δ_x`. -/
theorem noImmigration_pow_apply_singleton (n x y : ℕ) :
    (Kernel.ofMatrix (noImmigration p) ^ n) x {y}
      = ENNReal.ofReal (binomialWeight x (p ^ n) y) := by
  induction n generalizing y with
  | zero =>
      rw [Kernel.pow_zero_apply_singleton, pow_zero]
      rcases eq_or_ne x y with rfl | hxy
      · simp [binomialWeight]
      · rw [Set.indicator_of_notMem (by simpa using hxy)]
        rcases lt_or_ge x y with h | h
        · rw [binomialWeight_eq_zero h, ENNReal.ofReal_zero]
        · have hlt : y < x := lt_of_le_of_ne h (Ne.symm hxy)
          have : x - y ≠ 0 := by omega
          simp [binomialWeight, zero_pow this]
  | succ n ih =>
      have hpn0 : (0 : ℝ) ≤ p ^ n := pow_nonneg hp0.le n
      have hpn1 : p ^ n ≤ 1 := pow_le_one₀ hp0.le hp1.le
      have hmul : ∀ z : ℕ, (Kernel.ofMatrix (noImmigration p) ^ n) x {z} * noImmigration p z y
          = ENNReal.ofReal (binomialWeight x (p ^ n) z * binomialWeight z p y) := fun z ↦ by
        rw [ih, noImmigration, ← ENNReal.ofReal_mul (binomialWeight_nonneg hpn0 hpn1 x z)]
      rw [Kernel.ofMatrix_pow_succ'_apply_singleton]
      simp only [hmul]
      rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun z ↦ mul_nonneg (binomialWeight_nonneg hpn0 hpn1 x z)
            (binomialWeight_nonneg hp0.le hp1.le z y))
          (hasSum_binomialWeight_mul_binomialWeight (p ^ n) p x y).summable,
        (hasSum_binomialWeight_mul_binomialWeight (p ^ n) p x y).tsum_eq, ← pow_succ]

omit hα in
/-- The extinction probability of the pure-survival chain within `n` steps:
`P̃^n(x, 0) = (1 - p^n)^x`, Georgii's `μ_P^x(τ ≤ n)`. -/
theorem noImmigration_pow_apply_zero (n x : ℕ) :
    (Kernel.ofMatrix (noImmigration p) ^ n) x {0} = ENNReal.ofReal ((1 - p ^ n) ^ x) := by
  rw [noImmigration_pow_apply_singleton hp0 hp1 n x 0]
  simp [binomialWeight]

omit hα in
/-- Under `P̃` the state `0` is absorbing, so `P̃^n(0, y) = 0` for `y ≥ 1`. -/
lemma noImmigration_pow_apply_zero_row {y : ℕ} (hy : y ≠ 0) (n : ℕ) :
    (Kernel.ofMatrix (noImmigration p) ^ n) 0 {y} = 0 := by
  rw [noImmigration_pow_apply_singleton hp0 hp1 n 0 y,
    binomialWeight_eq_zero (Nat.pos_of_ne_zero hy), ENNReal.ofReal_zero]

omit hα in
/-- The `P̃`-paths avoiding the state `0` are exactly the `P̃`-paths ending away from `0`, since
`0` is absorbing for `P̃`. -/
lemma taboo_noImmigration_pow_apply_singleton {y : ℕ} (hy : y ≠ 0) (n x : ℕ) :
    (Kernel.ofMatrix (Kernel.tabooMatrix (noImmigration p) 0) ^ n) x {y}
      = (Kernel.ofMatrix (noImmigration p) ^ n) x {y} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Kernel.ofMatrix_pow_succ_apply_singleton, Kernel.ofMatrix_pow_succ_apply_singleton]
      refine tsum_congr fun w ↦ ?_
      rcases eq_or_ne w 0 with rfl | hw
      · rw [Kernel.tabooMatrix_apply_self, zero_mul,
          noImmigration_pow_apply_zero_row hp0 hp1 hy n, mul_zero]
      · rw [Kernel.tabooMatrix_apply_of_ne hw, ih w]

omit hp0 hp1 hα in
/-- `P` and `P̃` have the same taboo powers away from the state `0`: a path that never returns to
`0` never uses the immigration row of `P`. -/
lemma taboo_step_pow_apply_singleton (n : ℕ) : ∀ x, x ≠ 0 → ∀ y,
    (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y}
      = (Kernel.ofMatrix (Kernel.tabooMatrix (noImmigration p) 0) ^ n) x {y} := by
  induction n with
  | zero => intro x _ y; simp
  | succ n ih =>
      intro x hx y
      rw [Kernel.ofMatrix_pow_succ_apply_singleton, Kernel.ofMatrix_pow_succ_apply_singleton]
      refine tsum_congr fun w ↦ ?_
      rcases eq_or_ne w 0 with rfl | hw
      · rw [Kernel.tabooMatrix_apply_self, Kernel.tabooMatrix_apply_self, zero_mul, zero_mul]
      · rw [Kernel.tabooMatrix_apply_of_ne hw, Kernel.tabooMatrix_apply_of_ne hw,
          step_eq_noImmigration hx w, ih w hw y]

omit hα in
/-- **Georgii (11.47) for Spitzer's `P`.** For `x ≥ 1` and `y ≥ 1`,

`P^n(x, y) = ℓ(x, p^n, y) + ∑_{m < n} μ_P^x(τ = m+1) P^{n-1-m}(0, y)`,

where `τ` is the extinction time: the paths that never visit `0` are exactly the paths of the
pure-survival chain `P̃` (Georgii's first display, with `μ_P^x(σ_n = y, τ > n) = ℓ(x, p^n, y)`
for `y ≥ 1`), and every other path is decomposed at its first visit to `0`. -/
theorem step_pow_apply_singleton {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℕ) :
    (Kernel.ofMatrix (step p α) ^ n) x {y}
      = ENNReal.ofReal (binomialWeight x (p ^ n) y)
        + ∑ m ∈ Finset.range n, Kernel.firstPassage (step p α) 0 m x
            * (Kernel.ofMatrix (step p α) ^ (n - 1 - m)) 0 {y} := by
  rw [Kernel.ofMatrix_pow_apply_singleton_eq_taboo_add (step p α) 0 n x y,
    taboo_step_pow_apply_singleton n x hx y,
    taboo_noImmigration_pow_apply_singleton hp0 hp1 hy n x,
    noImmigration_pow_apply_singleton hp0 hp1 n x y]

omit hp0 hp1 hα in
/-- `P(w, 0) = (1 - p)^w` for `w ≥ 1`: the whole population dies out in a single step. -/
lemma step_apply_zero {w : ℕ} (hw : w ≠ 0) : step p α w 0 = ENNReal.ofReal ((1 - p) ^ w) := by
  simp [step, stepReal, hw, binomialWeight]

omit hα in
/-- **Georgii's extinction-time law for Spitzer's `P`** (§11.4, Step 2). For `x ≥ 1` the first
passage to `0` satisfies `μ_P^x(τ = m + 1) = (1 - p^{m+1})^x - (1 - p^m)^x`; stated without
subtraction, since the ambient order is `ℝ≥0∞`. Summing over `m < n` telescopes to Georgii's
`μ_P^x(τ ≤ n) = (1 - p^n)^x`. -/
theorem firstPassage_step_add {x : ℕ} (hx : x ≠ 0) (m : ℕ) :
    Kernel.firstPassage (step p α) 0 m x + ENNReal.ofReal ((1 - p ^ m) ^ x)
      = ENNReal.ofReal ((1 - p ^ (m + 1)) ^ x) := by
  have hz : (0 : ℝ) ≤ 1 - p := by linarith
  have hpm0 : (0 : ℝ) ≤ p ^ m := pow_nonneg hp0.le m
  have hpm1 : p ^ m ≤ 1 := pow_le_one₀ hp0.le hp1.le
  set f : ℕ → ℝ := fun w ↦ binomialWeight x (p ^ m) w * (1 - p) ^ w with hf
  have hnn : ∀ w, 0 ≤ f w := fun w ↦
    mul_nonneg (binomialWeight_nonneg hpm0 hpm1 x w) (pow_nonneg hz w)
  have hsum : HasSum f ((1 - p ^ m + p ^ m * (1 - p)) ^ x) :=
    hasSum_binomialWeight_mul_pow (p ^ m) (1 - p) x
  have hf0 : f 0 = (1 - p ^ m) ^ x := by simp [hf, binomialWeight]
  have htotal : (1 - p ^ m + p ^ m * (1 - p)) ^ x = (1 - p ^ (m + 1)) ^ x := by
    congr 1; rw [pow_succ]; ring
  have hgnn : ∀ w : ℕ, 0 ≤ (if w = 0 then (0 : ℝ) else f w) := by
    intro w; split_ifs with h
    · exact le_rfl
    · exact hnn w
  have hgle : ∀ w : ℕ, (if w = 0 then (0 : ℝ) else f w) ≤ f w := by
    intro w; split_ifs with h
    · exact hnn w
    · exact le_rfl
  have hg : Summable fun w : ℕ ↦ (if w = 0 then (0 : ℝ) else f w) :=
    Summable.of_nonneg_of_le hgnn hgle hsum.summable
  have hind : HasSum (fun w : ℕ ↦ if w = 0 then f 0 else 0) (f 0) := by
    simpa using hasSum_single (f := fun w : ℕ ↦ if w = 0 then f 0 else 0) 0
      fun w hw ↦ by simp [hw]
  have hsplit : ∀ w : ℕ, f w
      = (if w = 0 then (0 : ℝ) else f w) + (if w = 0 then f 0 else 0) := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · simp [hw]
  have hgsum : (∑' w : ℕ, (if w = 0 then (0 : ℝ) else f w)) + f 0
      = (1 - p ^ (m + 1)) ^ x := by
    rw [← htotal, ← hsum.tsum_eq, tsum_congr hsplit, hg.tsum_add hind.summable,
      hind.tsum_eq]
  have hterm : ∀ w : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ m) x {w}
      * step p α w 0 = ENNReal.ofReal (if w = 0 then (0 : ℝ) else f w) := by
    intro w
    rcases eq_or_ne w 0 with rfl | hw
    · rw [Kernel.tabooMatrix_pow_apply_self hx m, zero_mul]
      simp
    · rw [taboo_step_pow_apply_singleton m x hx w,
        taboo_noImmigration_pow_apply_singleton hp0 hp1 hw m x,
        noImmigration_pow_apply_singleton hp0 hp1 m x w, step_apply_zero hw,
        ← ENNReal.ofReal_mul (binomialWeight_nonneg hpm0 hpm1 x w)]
      simp only [hw, ite_false, hf]
  rw [Kernel.firstPassage]
  simp only [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hgnn hg, ← hf0,
    ← ENNReal.ofReal_add (tsum_nonneg hgnn) (hnn 0), hgsum]

omit hα in
/-- **Georgii's extinction probability** `μ_P^x(τ ≤ n) = (1 - p^n)^x` for `x ≥ 1`: the telescoping
sum of `firstPassage_step_add`. In particular `μ_P^x(τ < ∞) = 1`, since `(1 - p^n)^x → 1`. -/
theorem sum_firstPassage_step {x : ℕ} (hx : x ≠ 0) (n : ℕ) :
    ∑ m ∈ Finset.range n, Kernel.firstPassage (step p α) 0 m x
      = ENNReal.ofReal ((1 - p ^ n) ^ x) := by
  induction n with
  | zero => simp [zero_pow hx]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, add_comm, firstPassage_step_add hp0 hp1 hx n]

omit hp0 hp1 in
lemma step_pos_of_zero (y : ℕ) : 0 < step p α 0 y :=
  ENNReal.ofReal_pos.2 (by simpa [stepReal] using hα y)

omit hp0 in
lemma step_pos_apply_zero (x : ℕ) : 0 < step p α x 0 := by
  refine ENNReal.ofReal_pos.2 ?_
  simp only [stepReal]
  split_ifs with h
  · exact hα 0
  · exact binomialWeight_zero_pos hp1 x

include hαs hα1 in
lemma tsum_step (x : ℕ) : ∑' y : ℕ, step p α x y = 1 := by
  simp only [step, stepReal]
  split_ifs with h
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ (hα y).le) hαs, hα1, ENNReal.ofReal_one]
  · rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun y ↦ binomialWeight_nonneg hp0.le hp1.le x y) (summable_binomialWeight p x),
      (hasSum_binomialWeight p x).tsum_eq, ENNReal.ofReal_one]

omit hp0 hp1 hα in
lemma matrix_eq_tsum (x y : ℕ) : matrix p α x y = ∑' z : ℕ, step p α x z * step p α z y :=
  Kernel.ofMatrix_pow_two_apply_singleton _ x y

omit hp0 in
/-- `Q = P²` is a positive matrix: `Q(x, y) ≥ P(x, 0) P(0, y) > 0`. -/
lemma matrix_pos (x y : ℕ) : 0 < matrix p α x y := by
  rw [matrix_eq_tsum]
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 0)
  exact ENNReal.mul_pos (step_pos_apply_zero hp1 hα x).ne' (step_pos_of_zero hα y).ne'

include hαs hα1 in
/-- `Q = P²` is stochastic. -/
lemma tsum_matrix (x : ℕ) : ∑' y : ℕ, matrix p α x y = 1 := by
  simp only [matrix_eq_tsum]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, tsum_step hp0 hp1 hα hαs hα1, mul_one]
  exact tsum_step hp0 hp1 hα hαs hα1 x

include hαs hα1 in
/-- Spitzer's `Q = P²` is a transfer matrix in the sense of Georgii (11.1). -/
lemma isTransferMatrix : IsTransferMatrix (matrix p α) :=
  isTransferMatrix_of_stochastic (matrix_pos hp1 hα) (tsum_matrix hp0 hp1 hα hαs hα1)

/-! ## Georgii §11.4, Steps 2–4: the entrance law, and `𝒢(Q) ≠ ∅` -/

section EntranceLaw

open Filter
open scoped Topology

omit hα in
/-- The extinction-time law of §11.4 in closed form: for `x ≥ 1`,
`μ_P^x(τ = m + 1) = (1 - p^{m+1})^x - (1 - p^m)^x`. -/
lemma firstPassage_step_eq {x : ℕ} (hx : x ≠ 0) (m : ℕ) :
    Kernel.firstPassage (step p α) 0 m x
      = ENNReal.ofReal ((1 - p ^ (m + 1)) ^ x - (1 - p ^ m) ^ x) := by
  have h0 : (0 : ℝ) ≤ 1 - p ^ m := by
    have := pow_le_one₀ hp0.le hp1.le (n := m); linarith
  rw [ENNReal.ofReal_sub _ (pow_nonneg h0 x)]
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top (firstPassage_step_add hp0 hp1 hx m)

omit hα in
/-- The taboo powers of `P` at the state `0`: a path that avoids `0` is a pure-survival path, and
it never ends at `0`. -/
lemma taboo_step_pow_eq {x : ℕ} (hx : x ≠ 0) (n y : ℕ) :
    (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y}
      = if y = 0 then 0 else ENNReal.ofReal (binomialWeight x (p ^ n) y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [ite_eq_left rfl, Kernel.tabooMatrix_pow_apply_self hx n]
  · rw [ite_eq_right hy, taboo_step_pow_apply_singleton n x hx y,
      taboo_noImmigration_pow_apply_singleton hp0 hp1 hy n x,
      noImmigration_pow_apply_singleton hp0 hp1 n x y]

omit hα in
/-- **Georgii (11.47) for Spitzer's `P`, at every state `y`,** with the renewal sum indexed by the
number `k` of steps *after* the extinction:

`P^n(x, y) = ℓ(x, p^n, y) 1_{y ≠ 0} + ∑_{k < n} μ_P^x(τ = n - k) P^k(0, y)`  (`x ≥ 1`).

The extra clause at `y = 0` is that a path avoiding `0` cannot end at `0`. -/
theorem step_pow_apply_singleton_of_ne_zero {x : ℕ} (hx : x ≠ 0) (n y : ℕ) :
    (Kernel.ofMatrix (step p α) ^ n) x {y}
      = (if y = 0 then 0 else ENNReal.ofReal (binomialWeight x (p ^ n) y))
        + ∑ k ∈ Finset.range n, Kernel.firstPassage (step p α) 0 (n - 1 - k) x
            * (Kernel.ofMatrix (step p α) ^ k) 0 {y} := by
  rw [Kernel.ofMatrix_pow_apply_singleton_eq_taboo_add (step p α) 0 n x y,
    taboo_step_pow_eq hp0 hp1 hx n y]
  congr 1
  refine (Finset.sum_range_reflect _ n).symm.trans (Finset.sum_congr rfl fun k hk ↦ ?_)
  simp only [Finset.mem_range] at hk
  rw [show n - 1 - (n - 1 - k) = k from by omega]

omit hα in
/-- The dominating series of Georgii's Step 2: `∑_k e^{-c p^{-k}} < ∞`, because `p^{-k}` grows
geometrically, so `c p^{-k} ≥ c(1 + k(p^{-1} - 1))`. -/
lemma summable_exp_neg_div_pow {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ ↦ Real.exp (-(c / p ^ k)) := by
  have hinv : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpinv : (0 : ℝ) < p⁻¹ := inv_pos.2 hp0
  have ha0 : (0 : ℝ) < p⁻¹ - 1 := by nlinarith
  set a : ℝ := p⁻¹ - 1 with ha
  set r : ℝ := Real.exp (-(c * a)) with hr
  have hr1 : r < 1 := by
    have hlt : Real.exp (-(c * a)) < Real.exp 0 := Real.exp_lt_exp.2 (by nlinarith)
    rwa [Real.exp_zero] at hlt
  refine Summable.of_nonneg_of_le (fun k ↦ (Real.exp_pos _).le) (fun k ↦ ?_)
    ((summable_geometric_of_lt_one (Real.exp_nonneg _) hr1).mul_left (Real.exp (-c)))
  have hpk0 : (0 : ℝ) < p ^ k := pow_pos hp0 k
  have hbern : 1 + (k : ℝ) * a ≤ (1 + a) ^ k := one_add_mul_le_pow (by linarith) k
  have hpow : (1 + a) ^ k = (p ^ k)⁻¹ := by
    rw [show (1 : ℝ) + a = p⁻¹ by rw [ha]; ring, ← inv_pow]
  have hle : c * (1 + (k : ℝ) * a) ≤ c / p ^ k := by
    rw [div_eq_mul_inv, ← hpow]
    exact mul_le_mul_of_nonneg_left hbern hc.le
  calc Real.exp (-(c / p ^ k)) ≤ Real.exp (-(c * (1 + (k : ℝ) * a))) :=
        Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (-c) * r ^ k := by
        rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

omit hα in
/-- Georgii's telescoping identity for the limiting extinction weights:
`∑_{k ≥ 0} [e^{-c p^{-k}} - e^{-c p^{-k-1}}] = e^{-c}`, the total mass that the entrance vector
receives from the extinct part of the population. -/
lemma tsum_entranceWeight {c : ℝ} (hc : 0 < c) :
    ∑' k : ℕ, entranceWeight p c k = ENNReal.ofReal (Real.exp (-c)) := by
  set A : ℕ → ℝ := fun k ↦ Real.exp (-(c / p ^ k)) with hA
  have hmono : ∀ k, A (k + 1) ≤ A k := by
    intro k
    have hpk : (0 : ℝ) < p ^ k := pow_pos hp0 k
    have hpk1 : (0 : ℝ) < p ^ (k + 1) := pow_pos hp0 (k + 1)
    have hpp : p ^ (k + 1) ≤ p ^ k := pow_le_pow_of_le_one hp0.le hp1.le (Nat.le_succ k)
    have hdiv : c / p ^ k ≤ c / p ^ (k + 1) := by
      rw [div_le_div_iff₀ hpk hpk1]
      nlinarith
    exact Real.exp_le_exp.2 (by linarith)
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, (A k - A (k + 1)) = A 0 - A n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hpartial : ∀ n : ℕ, ∑ k ∈ Finset.range n, entranceWeight p c k
      = ENNReal.ofReal (A 0 - A n) := by
    intro n
    have h1 : ∀ k ∈ Finset.range n, entranceWeight p c k = ENNReal.ofReal (A k - A (k + 1)) :=
      fun k _ ↦ rfl
    rw [Finset.sum_congr rfl h1,
      ← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ sub_nonneg.2 (hmono k)), htel n]
  have hA0 : Tendsto A atTop (𝓝 0) := (summable_exp_neg_div_pow hp0 hp1 hc).tendsto_atTop_zero
  refine ((ENNReal.hasSum_iff_tendsto_nat _).2 ?_).tsum_eq
  simp only [hpartial]
  have hsub : Tendsto (fun n ↦ A 0 - A n) atTop (𝓝 (A 0 - 0)) := tendsto_const_nhds.sub hA0
  have := ENNReal.tendsto_ofReal hsub
  simpa [hA] using this

omit hα in
/-- A pointwise limit `(1 - p^{n-j})^{x_n} → e^{-c p^{-j}}` behind Georgii's Step 2: the
probability that a population of `x_n` individuals is extinct after `n - j` time units. -/
private lemma tendsto_one_sub_pow_sub {c : ℝ} {x : ℕ → ℕ}
    (hlim : Tendsto (fun n ↦ (x n : ℝ) * p ^ n) atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n ↦ (1 - p ^ (n - j)) ^ x n) atTop (𝓝 (Real.exp (-(c / p ^ j)))) := by
  have hpj : (0 : ℝ) < p ^ j := pow_pos hp0 j
  have heq : ∀ᶠ n in atTop, p ^ (n - j) = p ^ n / p ^ j := by
    filter_upwards [eventually_ge_atTop j] with n hn
    rw [eq_div_iff hpj.ne', ← pow_add]
    congr 1
    omega
  have h1 : Tendsto (fun n ↦ (x n : ℝ) * -p ^ (n - j)) atTop (𝓝 (-(c / p ^ j))) := by
    refine ((hlim.div_const (p ^ j)).neg).congr' ?_
    filter_upwards [heq] with n hn
    rw [hn]
    ring
  have h2 : Tendsto (fun n : ℕ ↦ -p ^ (n - j)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ ↦ p ^ n / p ^ j) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1).div_const (p ^ j)
    have hpneg : Tendsto (fun n : ℕ ↦ -(p ^ n / p ^ j)) atTop (𝓝 0) := by simpa using hp.neg
    refine hpneg.congr' ?_
    filter_upwards [heq] with n hn
    rw [hn]
  exact (Real.tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero h1 h2).congr fun n ↦ by
    rw [← sub_eq_add_neg]

include hαs hα1 in
omit hα in
lemma isMarkovKernel_ofMatrix_step (hα' : ∀ y, 0 < α y) :
    IsMarkovKernel (Kernel.ofMatrix (step p α)) :=
  Kernel.isMarkovKernel_ofMatrix _ (tsum_step hp0 hp1 hα' hαs hα1)

include hαs hα1 in
/-- **Georgii §11.4, Step 2.** Along any sequence `(x_n)` in `E` with `x_n p^n → c > 0` and
`x_n p^n ≥ c` eventually, the rows of the powers of `P` converge, `P^n(x_n, y) → α_c(y)`.

The binomial term of the renewal decomposition (11.47) converges by the Poisson limit theorem,
`ℓ(x_n, p^n, ·) → 𝔭(c, ·)`; the renewal series converges by dominated convergence, the
extinction weights `μ_P^{x_n}(τ = n - k)` being dominated by `e^{-c p^{-k}}`, which is summable
in `k`. -/
theorem tendsto_step_pow_apply_singleton {c : ℝ} (hc : 0 < c) {x : ℕ → ℕ}
    (hge : ∀ᶠ n in atTop, c ≤ (x n : ℝ) * p ^ n)
    (hlim : Tendsto (fun n ↦ (x n : ℝ) * p ^ n) atTop (𝓝 c)) (y : ℕ) :
    Tendsto (fun n ↦ (Kernel.ofMatrix (step p α) ^ n) (x n) {y}) atTop
      (𝓝 (entranceVector p α c y)) := by
  have hMarkov : IsMarkovKernel (Kernel.ofMatrix (step p α)) :=
    isMarkovKernel_ofMatrix_step hp0 hp1 hαs hα1 hα
  have hpn0 : Tendsto (fun n : ℕ ↦ p ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1
  have hx0 : ∀ᶠ n in atTop, x n ≠ 0 := by
    filter_upwards [hge] with n hn hxn
    rw [hxn] at hn
    simp only [Nat.cast_zero, zero_mul] at hn
    linarith
  -- the binomial term of (11.47)
  have hbin : Tendsto
      (fun n ↦ if y = 0 then 0 else ENNReal.ofReal (binomialWeight (x n) (p ^ n) y)) atTop
      (𝓝 (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y))) := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · simp only [ite_eq_right hy]
      refine ENNReal.tendsto_ofReal ?_
      exact ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul hlim hpn0 y
  -- the renewal series of (11.47)
  have hfp : ∀ k : ℕ, Tendsto (fun n ↦ Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)) atTop
      (𝓝 (entranceWeight p c k)) := by
    intro k
    have heq : ∀ᶠ n in atTop, ENNReal.ofReal
        ((1 - p ^ (n - k)) ^ x n - (1 - p ^ (n - (k + 1))) ^ x n)
        = Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n) := by
      filter_upwards [hx0, eventually_ge_atTop (k + 1)] with n hn hnk
      rw [firstPassage_step_eq hp0 hp1 hn (n - 1 - k),
        show n - 1 - k + 1 = n - k from by omega, show n - 1 - k = n - (k + 1) from by omega]
    refine Tendsto.congr' heq ?_
    exact ENNReal.tendsto_ofReal
      ((tendsto_one_sub_pow_sub hp0 hp1 hlim k).sub (tendsto_one_sub_pow_sub hp0 hp1 hlim (k + 1)))
  have hren : Tendsto (fun n ↦ ∑ k ∈ Finset.range n,
      Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)
        * (Kernel.ofMatrix (step p α) ^ k) 0 {y}) atTop
      (𝓝 (∑' k : ℕ, entranceWeight p c k * (Kernel.ofMatrix (step p α) ^ k) 0 {y})) := by
    refine ENNReal.tendsto_sum_range_of_dominated_convergence
      (bound := fun k ↦ ENNReal.ofReal (Real.exp (-(c / p ^ k))))
      ((summable_exp_neg_div_pow hp0 hp1 hc).tsum_ofReal_ne_top)
      (fun k ↦ ENNReal.Tendsto.mul_const (hfp k) (Or.inr (measure_ne_top _ _))) ?_
    filter_upwards [hx0, hge] with n hn hgen k hk
    have hpnk : (0 : ℝ) < p ^ (n - k) := pow_pos hp0 (n - k)
    have hpk : (0 : ℝ) < p ^ k := pow_pos hp0 k
    have hsplit : p ^ (n - k) * p ^ k = p ^ n := by rw [← pow_add]; congr 1; omega
    have hfle : Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)
        ≤ ENNReal.ofReal (Real.exp (-(c / p ^ k))) := by
      have h1 : Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)
          ≤ ENNReal.ofReal ((1 - p ^ (n - 1 - k + 1)) ^ x n) := by
        rw [← firstPassage_step_add hp0 hp1 hn (n - 1 - k)]
        exact self_le_add_right _ _
      refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [show n - 1 - k + 1 = n - k from by omega]
      refine (Real.one_sub_pow_le_exp_neg_mul (pow_le_one₀ hp0.le hp1.le) (x n)).trans
        (Real.exp_le_exp.2 ?_)
      have hge' : c / p ^ k ≤ p ^ (n - k) * (x n : ℝ) := by
        rw [div_le_iff₀ hpk]
        calc c ≤ (x n : ℝ) * p ^ n := hgen
          _ = p ^ (n - k) * (x n : ℝ) * p ^ k := by rw [← hsplit]; ring
      linarith
    calc Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)
          * (Kernel.ofMatrix (step p α) ^ k) 0 {y}
        ≤ ENNReal.ofReal (Real.exp (-(c / p ^ k))) * 1 := by
          gcongr
          exact prob_le_one
      _ = ENNReal.ofReal (Real.exp (-(c / p ^ k))) := mul_one _
  have hdec : ∀ᶠ n in atTop,
      (if y = 0 then 0 else ENNReal.ofReal (binomialWeight (x n) (p ^ n) y))
        + ∑ k ∈ Finset.range n, Kernel.firstPassage (step p α) 0 (n - 1 - k) (x n)
            * (Kernel.ofMatrix (step p α) ^ k) 0 {y}
        = (Kernel.ofMatrix (step p α) ^ n) (x n) {y} := by
    filter_upwards [hx0] with n hn
    exact (step_pow_apply_singleton_of_ne_zero hp0 hp1 hn n y).symm
  exact Tendsto.congr' hdec (hbin.add hren)

omit hα in
lemma entranceWeight_pos {c : ℝ} (hc : 0 < c) (k : ℕ) : 0 < entranceWeight p c k := by
  have hpk : (0 : ℝ) < p ^ k := pow_pos hp0 k
  have hpk1 : (0 : ℝ) < p ^ (k + 1) := pow_pos hp0 (k + 1)
  have hpp : p ^ (k + 1) < p ^ k := by
    calc p ^ (k + 1) = p ^ k * p := by ring
      _ < p ^ k * 1 := by nlinarith
      _ = p ^ k := mul_one _
  have hdiv : c / p ^ k < c / p ^ (k + 1) := by
    rw [div_lt_div_iff₀ hpk hpk1]
    nlinarith
  refine ENNReal.ofReal_pos.2 ?_
  have := Real.exp_lt_exp.2 (show -(c / p ^ (k + 1)) < -(c / p ^ k) from by linarith)
  linarith

omit hα in
/-- Every entry of the entrance vector is strictly positive: for `y ≠ 0` already the Poisson
term is, and at `y = 0` the term `k = 0` of the renewal series is `g_0(c) > 0`. -/
lemma entranceVector_pos {c : ℝ} (hc : 0 < c) (y : ℕ) : 0 < entranceVector p α c y := by
  rcases eq_or_ne y 0 with rfl | hy
  · refine lt_of_lt_of_le ?_ (le_add_self (a :=
      ∑' k : ℕ, entranceWeight p c k * (Kernel.ofMatrix (step p α) ^ k) 0 {0}) (b := _))
    refine lt_of_lt_of_le ?_ (ENNReal.le_tsum 0)
    have hind : ({0} : Set ℕ).indicator (1 : ℕ → ℝ≥0∞) 0 = 1 := by simp
    rw [Kernel.pow_zero_apply_singleton, hind, mul_one]
    exact entranceWeight_pos hp0 hp1 hc 0
  · refine lt_of_lt_of_le ?_ (le_self_add)
    rw [ite_eq_right hy]
    exact ENNReal.ofReal_pos.2 (poissonWeight_pos hc y)

include hαs hα1 in
/-- The entrance vector is a probability vector: the Poisson part contributes `1 - e^{-c}` and
the renewal series contributes `∑_k g_k(c) = e^{-c}`, since every `P^k(0, ·)` is a probability
vector. -/
lemma tsum_entranceVector {c : ℝ} (hc : 0 < c) : ∑' y : ℕ, entranceVector p α c y = 1 := by
  have hMarkov : IsMarkovKernel (Kernel.ofMatrix (step p α)) :=
    isMarkovKernel_ofMatrix_step hp0 hp1 hαs hα1 hα
  have hsplit : ∀ y : ℕ, entranceVector p α c y
      = (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y))
        + ∑' k : ℕ, entranceWeight p c k * (Kernel.ofMatrix (step p α) ^ k) 0 {y} := fun _ ↦ rfl
  have hP : ∀ k : ℕ, ∑' y : ℕ, (Kernel.ofMatrix (step p α) ^ k) 0 {y} = 1 := fun k ↦ by
    rw [MeasureTheory.Measure.tsum_apply_singleton]
    exact measure_univ
  have h2 : (∑' y : ℕ, ∑' k : ℕ,
      entranceWeight p c k * (Kernel.ofMatrix (step p α) ^ k) 0 {y})
      = ENNReal.ofReal (Real.exp (-c)) := by
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, hP, mul_one]
    exact tsum_entranceWeight hp0 hp1 hc
  have h1 : ENNReal.ofReal (Real.exp (-c))
      + ∑' y : ℕ, (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y)) = 1 := by
    have hall : ∑' y : ℕ, ENNReal.ofReal (poissonWeight c y) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ poissonWeight_nonneg hc.le y)
        (summable_poissonWeight hc.le), tsum_poissonWeight hc.le, ENNReal.ofReal_one]
    have hsplit0 : ∀ y : ℕ, ENNReal.ofReal (poissonWeight c y)
        = (if y = 0 then ENNReal.ofReal (Real.exp (-c)) else 0)
          + (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y)) := by
      intro y
      rcases eq_or_ne y 0 with rfl | hy
      · simp [poissonWeight_zero]
      · simp [hy]
    have hone : (∑' y : ℕ, (if y = 0 then ENNReal.ofReal (Real.exp (-c)) else 0))
        = ENNReal.ofReal (Real.exp (-c)) := by
      rw [tsum_eq_single 0 fun b hb ↦ by simp [hb]]
      simp
    calc ENNReal.ofReal (Real.exp (-c))
          + ∑' y : ℕ, (if y = 0 then 0 else ENNReal.ofReal (poissonWeight c y))
        = ∑' y : ℕ, ENNReal.ofReal (poissonWeight c y) := by
          rw [tsum_congr hsplit0, ENNReal.tsum_add, hone]
      _ = 1 := hall
  rw [tsum_congr hsplit, ENNReal.tsum_add, h2, add_comm]
  exact h1

include hαs hα1 in
lemma entranceVector_ne_top {c : ℝ} (hc : 0 < c) (y : ℕ) : entranceVector p α c y ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top
    (by rw [tsum_entranceVector hp0 hp1 hα hαs hα1 hc]; exact ENNReal.one_ne_top) y

omit hp1 hα in
lemma le_entranceSeq_mul_pow {c : ℝ} (n : ℕ) : c ≤ (entranceSeq p c n : ℝ) * p ^ n :=
  (div_le_iff₀ (pow_pos hp0 n)).1 (Nat.le_ceil (c / p ^ n))

omit hα in
lemma tendsto_entranceSeq_mul_pow {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n ↦ (entranceSeq p c n : ℝ) * p ^ n) atTop (𝓝 c) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ ↦ c)
    (h := fun n : ℕ ↦ c + p ^ n) tendsto_const_nhds ?_
    (fun n ↦ le_entranceSeq_mul_pow hp0 n) (fun n ↦ ?_)
  · simpa using tendsto_const_nhds.add (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1)
  · have hpn : (0 : ℝ) < p ^ n := pow_pos hp0 n
    have h := Nat.ceil_lt_add_one (a := c / p ^ n) (by positivity)
    have hmul : (entranceSeq p c n : ℝ) * p ^ n ≤ (c / p ^ n + 1) * p ^ n :=
      mul_le_mul_of_nonneg_right h.le hpn.le
    rwa [add_mul, div_mul_cancel₀ _ hpn.ne', one_mul] at hmul

include hαs hα1 in
/-- **Georgii §11.4, Step 3.** `{α_{c p^i} : i ∈ ℤ}` is an entrance law for `P`. Fatou's lemma
gives `α_{c p^i} P ≤ α_{c p^{i+1}}` — the left side is a limit of the rows `P^n(x_n, ·)` and the
right side the corresponding limit of `P^{n+1}(x_n, ·)` — and since both sides are probability
vectors the inequality cannot be strict anywhere (`isEntranceLaw_of_forall_tsum_le`). -/
theorem isEntranceLaw_step {c : ℝ} (hc : 0 < c) :
    IsEntranceLaw (step p α) (fun i : ℤ ↦ entranceVector p α (c * p ^ i)) := by
  have hci : ∀ i : ℤ, 0 < c * p ^ i := fun i ↦ mul_pos hc (zpow_pos hp0 i)
  refine isEntranceLaw_of_forall_tsum_le (tsum_step hp0 hp1 hα hαs hα1)
    (fun i x ↦ entranceVector_pos hp0 hp1 (hci i) x)
    (fun i ↦ tsum_entranceVector hp0 hp1 hα hαs hα1 (hci i)) fun i y ↦ ?_
  set d : ℝ := c * p ^ i with hd
  have hd0 : 0 < d := hci i
  set x : ℕ → ℕ := entranceSeq p d with hx
  have hge : ∀ᶠ n in atTop, d ≤ (x n : ℝ) * p ^ n :=
    Eventually.of_forall fun n ↦ le_entranceSeq_mul_pow hp0 n
  have hlim : Tendsto (fun n ↦ (x n : ℝ) * p ^ n) atTop (𝓝 d) :=
    tendsto_entranceSeq_mul_pow hp0 hp1 hd0
  have h1 : ∀ z : ℕ, Tendsto (fun n ↦ (Kernel.ofMatrix (step p α) ^ n) (x n) {z}) atTop
      (𝓝 (entranceVector p α d z)) := fun z ↦
    tendsto_step_pow_apply_singleton hp0 hp1 hα hαs hα1 hd0 hge hlim z
  -- the shifted sequence: `P^{n+1}(x_n, ·) → α_{d p}`
  have hshift : Tendsto (fun n ↦ (Kernel.ofMatrix (step p α) ^ (n + 1)) (x n) {y}) atTop
      (𝓝 (entranceVector p α (d * p) y)) := by
    set w : ℕ → ℕ := fun m ↦ x (m - 1) with hw
    have hwge : ∀ᶠ m in atTop, d * p ≤ (w m : ℝ) * p ^ m := by
      filter_upwards [eventually_ge_atTop 1] with m hm
      have hpm : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ]; congr 1; omega
      have := le_entranceSeq_mul_pow (p := p) (c := d) hp0 (m - 1)
      rw [hw, hpm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right this hp0.le
    have hwlim : Tendsto (fun m ↦ (w m : ℝ) * p ^ m) atTop (𝓝 (d * p)) := by
      have hcomp : Tendsto (fun m : ℕ ↦ (x (m - 1) : ℝ) * p ^ (m - 1)) atTop (𝓝 d) :=
        hlim.comp (tendsto_sub_atTop_nat 1)
      refine (hcomp.mul_const p).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with m hm
      rw [hw, show p ^ m = p ^ (m - 1) * p from by rw [← pow_succ]; congr 1; omega]
      ring
    have hwconv : Tendsto (fun m ↦ (Kernel.ofMatrix (step p α) ^ m) (w m) {y}) atTop
        (𝓝 (entranceVector p α (d * p) y)) :=
      tendsto_step_pow_apply_singleton hp0 hp1 hα hαs hα1 (mul_pos hd0 hp0) hwge hwlim y
    have hcomp := hwconv.comp (tendsto_add_atTop_nat 1)
    simpa [hw, Function.comp_def, Nat.add_sub_cancel] using hcomp
  have hrate : d * p = c * p ^ (i + 1) := by
    rw [hd, zpow_add_one₀ hp0.ne', mul_assoc]
  rw [← hrate]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hfin : Tendsto (fun n ↦ ∑ z ∈ s, (Kernel.ofMatrix (step p α) ^ n) (x n) {z}
      * step p α z y) atTop
      (𝓝 (∑ z ∈ s, entranceVector p α d z * step p α z y)) :=
    tendsto_finsetSum _ fun z _ ↦
      ENNReal.Tendsto.mul_const (h1 z) (Or.inr ENNReal.ofReal_ne_top)
  refine le_of_tendsto_of_tendsto' hfin hshift fun n ↦ ?_
  calc ∑ z ∈ s, (Kernel.ofMatrix (step p α) ^ n) (x n) {z} * step p α z y
      ≤ ∑' z : ℕ, (Kernel.ofMatrix (step p α) ^ n) (x n) {z} * step p α z y :=
        ENNReal.sum_le_tsum s
    _ = (Kernel.ofMatrix (step p α) ^ (n + 1)) (x n) {y} :=
        (Kernel.ofMatrix_pow_succ'_apply_singleton _ n _ y).symm

include hαs hα1 in
/-- **Georgii §11.4, Step 4.** `{α_{c p^{2i}} : i ∈ ℤ}` is an entrance law for `Q = P²`: apply
`isEntranceLaw_step` twice. -/
theorem isEntranceLaw_matrix {c : ℝ} (hc : 0 < c) :
    IsEntranceLaw (matrix p α) (fun i : ℤ ↦ entranceVector p α (c * p ^ (2 * i))) where
  pos i x := entranceVector_pos hp0 hp1 (mul_pos hc (zpow_pos hp0 _)) x
  tsum_eq_one i := tsum_entranceVector hp0 hp1 hα hαs hα1 (mul_pos hc (zpow_pos hp0 _))
  step i y := by
    have hP := isEntranceLaw_step hp0 hp1 hα hαs hα1 hc
    have hswap : (∑' x : ℕ, entranceVector p α (c * p ^ (2 * i)) x * matrix p α x y)
        = ∑' z : ℕ, (∑' x : ℕ, entranceVector p α (c * p ^ (2 * i)) x * step p α x z)
            * step p α z y := by
      have hterm : ∀ x : ℕ, entranceVector p α (c * p ^ (2 * i)) x * matrix p α x y
          = ∑' z : ℕ, entranceVector p α (c * p ^ (2 * i)) x * step p α x z * step p α z y := by
        intro x
        rw [matrix_eq_tsum, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun z ↦ (mul_assoc _ _ _).symm
      rw [tsum_congr hterm, ENNReal.tsum_comm]
      exact tsum_congr fun z ↦ ENNReal.tsum_mul_right
    calc (∑' x : ℕ, entranceVector p α (c * p ^ (2 * i)) x * matrix p α x y)
        = ∑' z : ℕ, entranceVector p α (c * p ^ (2 * i + 1)) z * step p α z y := by
          rw [hswap]
          exact tsum_congr fun z ↦ by rw [hP.step (2 * i) z]
      _ = entranceVector p α (c * p ^ (2 * i + 1 + 1)) y := hP.step (2 * i + 1) y
      _ = entranceVector p α (c * p ^ (2 * (i + 1))) y := by
          rw [show 2 * i + 1 + 1 = 2 * (i + 1) from by ring]

include hαs hα1 in
/-- **Georgii §11.4, Steps 2–4: `𝒢(Q) ≠ ∅` for Spitzer's `Q = P²`.** The entrance law
`{α_{p^{2i}}}` of `isEntranceLaw_matrix` is a boundary law with `r_i ≡ 1`, and Theorem
(11.9)(a) turns it into a Gibbs measure for `γ^Q`. This is the half of Theorem (11.46) that
Georgii calls "the main point of this example". -/
theorem nonempty_G :
    (G (transferSpecification (matrix p α) (isTransferMatrix hp0 hp1 hα hαs hα1))).Nonempty := by
  have hbl := (isEntranceLaw_matrix hp0 hp1 hα hαs hα1 (c := 1) one_pos).isBoundaryLaw
    (tsum_matrix hp0 hp1 hα hαs hα1)
  exact ⟨boundaryLawMeasure hbl, inferInstance,
    isGibbsMeasure_transferSpecification_boundaryLawMeasure _ hbl⟩

end EntranceLaw

/-! ## Georgii §11.4, Step 1: recurrence, and null recurrence for a suitable `α` -/

section NullRecurrence

open Filter
open scoped Topology

omit hα in
/-- **Georgii §11.4, Step 1.** Started at `x ≥ 1`, the population dies out almost surely:
`μ_P^x(τ < ∞) = lim_n (1 - p^n)^x = 1`. -/
theorem tsum_firstPassage_step {x : ℕ} (hx : x ≠ 0) :
    ∑' m : ℕ, Kernel.firstPassage (step p α) 0 m x = 1 := by
  refine ((ENNReal.hasSum_iff_tendsto_nat _).2 ?_).tsum_eq
  simp only [sum_firstPassage_step hp0 hp1 hx]
  have hbase : Tendsto (fun n : ℕ ↦ 1 - p ^ n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1)
  have hlim : Tendsto (fun n : ℕ ↦ (1 - p ^ n) ^ x) atTop (𝓝 1) := by simpa using hbase.pow x
  simpa only [ENNReal.ofReal_one] using ENNReal.tendsto_ofReal hlim

include hαs hα1 in
/-- **Georgii §11.4, Step 1.** `μ_P^0(τ < ∞) = α(0) + ∑_{x ≥ 1} α(x) μ_P^x(τ < ∞) = 1`: the
immigrating population dies out again almost surely. -/
theorem tsum_firstPassage_step_zero : ∑' m : ℕ, Kernel.firstPassage (step p α) 0 m 0 = 1 :=
  Kernel.tsum_firstPassage_self_eq_one (tsum_step hp0 hp1 hα hαs hα1 0)
    fun _ hw ↦ tsum_firstPassage_step hp0 hp1 hw

include hαs hα1 in
/-- **Georgii §11.4, Step 1.** `P` is recurrent: `∑ₙ Pⁿ(0, 0) = ∞`, by the renewal criterion
applied to `tsum_firstPassage_step_zero`. -/
theorem potential_step_eq_top : Kernel.potential (Kernel.ofMatrix (step p α)) 0 {0} = ∞ := by
  rw [Kernel.potential_apply_singleton]
  exact Kernel.tsum_pow_apply_singleton_self_eq_top_of_tsum_firstPassage
    (tsum_firstPassage_step_zero hp0 hp1 hα hαs hα1)

omit hp0 hp1 hα in
/-- Spitzer's `Q = P²` is the square of the kernel of `P`. -/
lemma ofMatrix_matrix : Kernel.ofMatrix (matrix p α) = Kernel.ofMatrix (step p α) ^ 2 :=
  Kernel.ofMatrix_entries _

omit hp0 in
lemma isIrreducible_matrix :
    Kernel.IsIrreducible (Measure.count : Measure ℕ) (Kernel.ofMatrix (matrix p α)) :=
  Kernel.isIrreducible_count_ofMatrix_of_forall_pos (matrix_pos hp1 hα)

include hαs hα1 in
lemma isMarkovKernel_ofMatrix_matrix : IsMarkovKernel (Kernel.ofMatrix (matrix p α)) :=
  Kernel.isMarkovKernel_ofMatrix _ (tsum_matrix hp0 hp1 hα hαs hα1)

include hαs hα1 in
/-- **Georgii §11.4, Step 1.** `Q = P²` is recurrent: `Q^n(0,0) = P^{2n}(0,0)` and the even part
of a divergent Green series still diverges, because `P(0, 0) = α(0) > 0`
(`ProbabilityTheory.Kernel.potential_pow_two_apply_singleton_self_eq_top`). -/
theorem isRecurrent_matrix : Kernel.IsRecurrent (Kernel.ofMatrix (matrix p α)) := by
  have := isIrreducible_matrix hp1 hα
  refine Kernel.isRecurrent_of_potential_eq_top (x := 0) (y := 0) ?_
  rw [ofMatrix_matrix]
  refine Kernel.potential_pow_two_apply_singleton_self_eq_top ?_
    (potential_step_eq_top hp0 hp1 hα hαs hα1)
  rw [Kernel.ofMatrix_apply_singleton]
  exact (step_pos_of_zero hα 0).ne'

include hαs hα1 in
/-- **Georgii §11.4, Step 1, the null-recurrence half, through Kac's inequality.** If the mean
extinction time of `P` started at `0` is infinite — Georgii's `μ_P^0(τ) = ∞`, written here as the
divergence of `∑ₙ μ_P^0(τ > n) = ∑ₙ ∑_y Tⁿ(0, y)` for the taboo matrix `T` of `P` at `0` — then
`Q = P²` has no invariant probability vector, hence is null recurrent.

Kac's inequality (`ProbabilityTheory.Kernel.mul_tsum_tsum_taboo_pow_le_of_invariant`) bounds
`v(0) μ_P^0(τ)` by the total mass of an invariant vector `v` of `P`; the invariant probability
vector of `Q = P²` is turned into an invariant vector `v + vP` of `P` of total mass `2` by
`ProbabilityTheory.Kernel.tsum_mul_add_tsum_mul_eq_of_tsum_mul_pow_two`. -/
theorem not_isPositiveRecurrent_matrix
    (hnull : ∑' n : ℕ, ∑' y : ℕ,
        (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) 0 {y} = ∞) :
    ¬ Kernel.IsPositiveRecurrent (Kernel.ofMatrix (matrix p α)) := by
  rintro ⟨-, μ, hμprob, hμinv⟩
  have hμ2 : ∀ y, ∑' x : ℕ, μ {x} * (Kernel.ofMatrix (step p α) ^ 2) x {y} = μ {y} := by
    intro y
    conv_rhs => rw [hμinv.apply_singleton_eq_tsum y]
    exact tsum_congr fun x ↦ by rw [mul_comm, ofMatrix_matrix]
  have hvinv := fun y ↦ Kernel.tsum_mul_add_tsum_mul_eq_of_tsum_mul_pow_two hμ2 y
  have hv0 : μ {0} + ∑' w : ℕ, μ {w} * step p α w 0 ≠ 0 := by
    intro h0
    have hall : ∀ w : ℕ, μ {w} = 0 := fun w ↦ by
      have h2 : ∑' w : ℕ, μ {w} * step p α w 0 = 0 := (add_eq_zero.1 h0).2
      rcases mul_eq_zero.1 (ENNReal.tsum_eq_zero.1 h2 w) with h | h
      · exact h
      · exact absurd h (step_pos_apply_zero hp1 hα w).ne'
    have huniv : μ Set.univ = 0 := by
      rw [← MeasureTheory.Measure.tsum_apply_singleton]
      simp [hall]
    rw [measure_univ] at huniv
    exact one_ne_zero huniv
  have hvt : (∑' y : ℕ, (μ {y} + ∑' w : ℕ, μ {w} * step p α w y)) ≠ ∞ := by
    have hrow : (∑' y : ℕ, ∑' w : ℕ, μ {w} * step p α w y) = 1 := by
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left, tsum_step hp0 hp1 hα hαs hα1, mul_one]
      rw [MeasureTheory.Measure.tsum_apply_singleton, measure_univ]
    rw [ENNReal.tsum_add, hrow, MeasureTheory.Measure.tsum_apply_singleton, measure_univ]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.one_ne_top⟩
  exact Kernel.tsum_tsum_taboo_pow_ne_top_of_invariant hvinv hv0 hvt hnull

include hαs hα1 in
/-- **Georgii Remark (11.7) for Spitzer's `Q`.** A null recurrent `Q` is not equivalent, in the
sense of Georgii (11.5), to any positive recurrent stochastic matrix: an equivalence
`P(x, y) = Q(x, y) r(y)/(c r(x))` with `P` stochastic and positive recurrent forces `c = 1` and
`r` constant, hence `P = Q`, so that `Q` itself would be positive recurrent
(`ProbabilityTheory.Kernel.isPositiveRecurrent_of_apply_eq_mul_div`). -/
theorem not_exists_isPositiveRecurrent
    (hnull : ∑' n : ℕ, ∑' y : ℕ,
        (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) 0 {y} = ∞) :
    ¬ ∃ (P : ℕ → ℕ → ℝ≥0∞) (c : ℝ≥0∞) (r : ℕ → ℝ≥0∞), 0 < c ∧ c ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = matrix p α x y * r y / (c * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P) := by
  rintro ⟨P, c, r, hc0, hct, hr0, hrt, hPeq, hPst, hPpr⟩
  refine not_isPositiveRecurrent_matrix hp0 hp1 hα hαs hα1 hnull ?_
  have := isMarkovKernel_ofMatrix_matrix hp0 hp1 hα hαs hα1
  have : IsMarkovKernel (Kernel.ofMatrix P) := Kernel.isMarkovKernel_ofMatrix _ hPst
  have : Kernel.IsIrreducible (Measure.count : Measure ℕ) (Kernel.ofMatrix P) :=
    Kernel.isIrreducible_count_ofMatrix_of_forall_pos fun x y ↦ by
      rw [hPeq]
      exact ENNReal.div_pos (mul_ne_zero (matrix_pos hp1 hα x y).ne' (hr0 y).ne')
        (ENNReal.mul_ne_top hct (hrt x))
  exact Kernel.isPositiveRecurrent_of_apply_eq_mul_div (x := 0) hc0.ne' hct
    (fun x ↦ (hr0 x).ne') hrt
    (fun x y ↦ by rw [Kernel.ofMatrix_apply_singleton, Kernel.ofMatrix_apply_singleton, hPeq])
    ((isRecurrent_matrix hp0 hp1 hα hαs hα1).convergenceNorm_eq_one 0) hPpr

end NullRecurrence

/-! ## Georgii §11.4, Step 1: a null recurrent immigration law exists -/

section NullRecurrentExists

open Filter
open scoped Topology

omit hα in
/-- The mass of the `n`-step paths of `P` from `x ≥ 1` that have not yet visited `0`:
`μ_P^x(τ > n) = 1 - (1 - p^n)^x`, stated without subtraction because the ambient order is
`ℝ≥0∞`. -/
lemma tsum_taboo_step_pow_add {x : ℕ} (hx : x ≠ 0) (n : ℕ) :
    (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y})
      + ENNReal.ofReal ((1 - p ^ n) ^ x) = 1 := by
  have hpn0 : (0 : ℝ) ≤ p ^ n := pow_nonneg hp0.le n
  have hpn1 : p ^ n ≤ 1 := pow_le_one₀ hp0.le hp1.le
  have hb : ∀ y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y}
      + (if y = 0 then ENNReal.ofReal ((1 - p ^ n) ^ x) else 0)
      = ENNReal.ofReal (binomialWeight x (p ^ n) y) := fun y ↦ by
    rw [taboo_step_pow_eq hp0 hp1 hx n y]
    rcases eq_or_ne y 0 with rfl | hy
    · simp [binomialWeight]
    · simp [hy]
  have hite : (∑' y : ℕ, (if y = 0 then ENNReal.ofReal ((1 - p ^ n) ^ x) else 0))
      = ENNReal.ofReal ((1 - p ^ n) ^ x) := tsum_ite_eq 0 _
  calc (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y})
        + ENNReal.ofReal ((1 - p ^ n) ^ x)
      = (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y})
          + ∑' y : ℕ, (if y = 0 then ENNReal.ofReal ((1 - p ^ n) ^ x) else 0) := by rw [hite]
    _ = ∑' y : ℕ, ((Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y}
          + (if y = 0 then ENNReal.ofReal ((1 - p ^ n) ^ x) else 0)) := (ENNReal.tsum_add).symm
    _ = ∑' y : ℕ, ENNReal.ofReal (binomialWeight x (p ^ n) y) := tsum_congr hb
    _ = 1 := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ binomialWeight_nonneg hpn0 hpn1 x y)
            (summable_binomialWeight (p ^ n) x),
          (hasSum_binomialWeight (p ^ n) x).tsum_eq, ENNReal.ofReal_one]

omit hα in
/-- **Georgii §11.4, Step 1.** If `p^n x ≥ 1` then the population started at `x` is still alive
at time `n` with probability at least `1/2`, because `(1 - p^n)^x ≤ e^{-p^n x} ≤ e^{-1} < 1/2`. -/
lemma half_le_tsum_taboo_step_pow {x n : ℕ} (h : 1 ≤ p ^ n * x) :
    (1 : ℝ≥0∞) / 2 ≤ ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y} := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, mul_zero] at h
    linarith
  have hpn1 : p ^ n ≤ 1 := pow_le_one₀ hp0.le hp1.le
  have hle : (1 - p ^ n) ^ x ≤ 1 / 2 := by
    have h1 : (1 - p ^ n) ^ x ≤ Real.exp (-(p ^ n * x)) := Real.one_sub_pow_le_exp_neg_mul hpn1 x
    have h2 : Real.exp (-(p ^ n * x)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      have he : (2 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
        linarith
      exact one_div_lt_one_div_of_lt (by norm_num) he
    linarith
  have hofhalf : ENNReal.ofReal ((1 : ℝ) / 2) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  have hhalf : ENNReal.ofReal ((1 - p ^ n) ^ x) ≤ 1 / 2 := by
    rw [← hofhalf]
    exact ENNReal.ofReal_le_ofReal hle
  have h1 : (1 : ℝ≥0∞) / 2 + 1 / 2
      ≤ (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y}) + 1 / 2 := by
    rw [ENNReal.add_halves]
    calc (1 : ℝ≥0∞)
        = (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y})
            + ENNReal.ofReal ((1 - p ^ n) ^ x) := (tsum_taboo_step_pow_add hp0 hp1 hx n).symm
      _ ≤ _ := add_le_add le_rfl hhalf
  exact ENNReal.le_of_add_le_add_right (by simp) h1

omit hα in
/-- **Georgii's Fatou step, quantified** (§11.4, Step 1). If `p^N x ≥ 1` then the mean extinction
time from `x` is at least `(N + 1)/2`: at each of the `N + 1` times `n ≤ N` the population is
still alive with probability at least `1/2`. In particular `μ_P^x(τ) → ∞` as `x → ∞`, which is
Georgii's `liminf_{x → ∞} μ_P^x(τ) = ∞`. -/
lemma le_tsum_tsum_taboo_step_pow {x N : ℕ} (h : 1 ≤ p ^ N * x) :
    ((N : ℝ≥0∞) + 1) / 2
      ≤ ∑' n : ℕ, ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y} := by
  have hterm : ∀ n ∈ Finset.range (N + 1), (1 : ℝ≥0∞) / 2
      ≤ ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y} := by
    intro n hn
    refine half_le_tsum_taboo_step_pow hp0 hp1 (h.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hp0.le hp1.le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)))
      (Nat.cast_nonneg x)
  have hconst : (∑ _n ∈ Finset.range (N + 1), (1 : ℝ≥0∞) / 2) = ((N : ℝ≥0∞) + 1) / 2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      mul_one_div]
  calc ((N : ℝ≥0∞) + 1) / 2 = ∑ _n ∈ Finset.range (N + 1), (1 : ℝ≥0∞) / 2 := hconst.symm
    _ ≤ ∑ n ∈ Finset.range (N + 1),
          ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) x {y} :=
        Finset.sum_le_sum hterm
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Georgii's test states, §11.4 Step 1: `x_k = ⌈p^{-2·4^k}⌉ + k`. The bound `p^{2·4^k} x_k ≥ 1`
makes the mean extinction time from `x_k` at least `4^k`, and the summand `k` makes the sequence
strictly increasing, hence injective. -/
def extinctionSeq (p : ℝ) (k : ℕ) : ℕ := ⌈(p ^ (2 * 4 ^ k))⁻¹⌉₊ + k

omit hp1 hα in
lemma one_le_pow_mul_extinctionSeq (k : ℕ) :
    1 ≤ p ^ (2 * 4 ^ k) * (extinctionSeq p k : ℝ) := by
  have hpk : (0 : ℝ) < p ^ (2 * 4 ^ k) := pow_pos hp0 _
  have hceil : (p ^ (2 * 4 ^ k))⁻¹ ≤ (extinctionSeq p k : ℝ) := by
    refine (Nat.le_ceil _).trans ?_
    have hle : ⌈(p ^ (2 * 4 ^ k))⁻¹⌉₊ ≤ extinctionSeq p k := Nat.le_add_right _ k
    exact_mod_cast hle
  calc (1 : ℝ) = p ^ (2 * 4 ^ k) * (p ^ (2 * 4 ^ k))⁻¹ := by field_simp
    _ ≤ p ^ (2 * 4 ^ k) * (extinctionSeq p k : ℝ) := by nlinarith

omit hp1 hα in
lemma extinctionSeq_ne_zero (k : ℕ) : extinctionSeq p k ≠ 0 := by
  have h1 : 0 < ⌈(p ^ (2 * 4 ^ k))⁻¹⌉₊ := Nat.ceil_pos.2 (inv_pos.2 (pow_pos hp0 _))
  simp only [extinctionSeq]
  omega

omit hα in
lemma strictMono_extinctionSeq : StrictMono (extinctionSeq p) := by
  intro k l hkl
  have hexp : 2 * 4 ^ k ≤ 2 * 4 ^ l := by
    have h4 : (4 : ℕ) ^ k ≤ 4 ^ l := Nat.pow_le_pow_right (by norm_num) hkl.le
    omega
  have hp : p ^ (2 * 4 ^ l) ≤ p ^ (2 * 4 ^ k) := pow_le_pow_of_le_one hp0.le hp1.le hexp
  have hinv : (p ^ (2 * 4 ^ k))⁻¹ ≤ (p ^ (2 * 4 ^ l))⁻¹ :=
    (inv_le_inv₀ (pow_pos hp0 _) (pow_pos hp0 _)).2 hp
  have hceil : ⌈(p ^ (2 * 4 ^ k))⁻¹⌉₊ ≤ ⌈(p ^ (2 * 4 ^ l))⁻¹⌉₊ := Nat.ceil_mono hinv
  simp only [extinctionSeq]
  omega

/-- The sparse part of Georgii's immigration law: mass `2^{-k-1}` at the state `x_k`. -/
noncomputable def immigrationTail (p : ℝ) (y : ℕ) : ℝ :=
  Set.indicator (Set.range (extinctionSeq p))
    (fun z ↦ (1 / 2 : ℝ) ^ (Function.invFun (extinctionSeq p) z + 1)) y

/-- **Georgii's null recurrent immigration law**, §11.4 Step 1, before normalisation:

`β(y) = 2^{-y-1} + 2^{-k-1} 1_{y = x_k}`,

with `x_k = extinctionSeq p k`. It is strictly positive, summable with `∑_y β(y) = 2`, and puts
mass `2^{-k-1}` on the state `x_k`, where the mean extinction time exceeds `4^k`. -/
noncomputable def immigrationWeight (p : ℝ) (y : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (y + 1) + immigrationTail p y

section Weight

omit hp0 hp1 hα in
private lemma summable_half_pow_succ : Summable fun y : ℕ ↦ ((1 : ℝ) / 2) ^ (y + 1) := by
  have h : Summable fun y : ℕ ↦ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ y :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact h.congr fun y ↦ by rw [pow_succ]; ring

omit hp0 hp1 hα in
private lemma tsum_half_pow_succ : (∑' y : ℕ, ((1 : ℝ) / 2) ^ (y + 1)) = 1 := by
  rw [tsum_congr fun y : ℕ ↦ (by rw [pow_succ]; ring :
      ((1 : ℝ) / 2) ^ (y + 1) = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ y),
    tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

omit hp0 hp1 hα in
private lemma immigrationTail_nonneg (y : ℕ) : 0 ≤ immigrationTail p y :=
  Set.indicator_apply_nonneg fun _ ↦ by positivity

omit hp0 hp1 hα in
private lemma immigrationTail_eq_zero {y : ℕ} (hy : y ∉ Set.range (extinctionSeq p)) :
    immigrationTail p y = 0 := Set.indicator_of_notMem hy _

omit hα in
private lemma immigrationTail_extinctionSeq (k : ℕ) :
    immigrationTail p (extinctionSeq p k) = (1 / 2 : ℝ) ^ (k + 1) := by
  rw [immigrationTail, Set.indicator_of_mem (Set.mem_range_self k),
    Function.leftInverse_invFun (strictMono_extinctionSeq hp0 hp1).injective k]

omit hα in
private lemma summable_immigrationTail : Summable (immigrationTail p) := by
  refine ((strictMono_extinctionSeq hp0 hp1).injective.summable_iff
    fun y hy ↦ immigrationTail_eq_zero hy).1 ?_
  exact Summable.congr summable_half_pow_succ fun k ↦
    (immigrationTail_extinctionSeq hp0 hp1 k).symm

omit hα in
private lemma tsum_immigrationTail : (∑' y : ℕ, immigrationTail p y) = 1 := by
  rw [← (strictMono_extinctionSeq hp0 hp1).injective.tsum_eq
      (Function.support_subset_iff'.2 fun y hy ↦ immigrationTail_eq_zero hy),
    tsum_congr fun k ↦ immigrationTail_extinctionSeq hp0 hp1 k, tsum_half_pow_succ]

omit hp0 hp1 hα in
lemma immigrationWeight_pos (y : ℕ) : 0 < immigrationWeight p y :=
  lt_of_lt_of_le (by positivity) (le_add_of_nonneg_right (immigrationTail_nonneg y))

omit hα in
lemma summable_immigrationWeight : Summable (immigrationWeight p) :=
  summable_half_pow_succ.add (summable_immigrationTail hp0 hp1)

omit hα in
lemma tsum_immigrationWeight : (∑' y : ℕ, immigrationWeight p y) = 2 := by
  simp only [immigrationWeight]
  rw [summable_half_pow_succ.tsum_add (summable_immigrationTail hp0 hp1), tsum_half_pow_succ,
    tsum_immigrationTail hp0 hp1]
  norm_num

omit hα in
lemma le_immigrationWeight_extinctionSeq (k : ℕ) :
    (1 / 2 : ℝ) ^ (k + 1) ≤ immigrationWeight p (extinctionSeq p k) := by
  have hsplit : immigrationWeight p (extinctionSeq p k)
      = (1 / 2 : ℝ) ^ (extinctionSeq p k + 1) + immigrationTail p (extinctionSeq p k) := rfl
  rw [hsplit, immigrationTail_extinctionSeq hp0 hp1 k]
  exact le_add_of_nonneg_left (by positivity)

end Weight

omit hα in
/-- **Georgii §11.4, Step 1: `α` can be chosen so that `P` is null recurrent.** For the
immigration law `α = β/2` built from `immigrationWeight` the mean extinction time
`μ_P^0(τ) = ∑ₙ μ_P^0(τ > n)` is infinite, because for Georgii's test states
`x_k = extinctionSeq p k`

`μ_P^0(τ) ≥ α(x_k) μ_P^{x_k}(τ) ≥ 2^{-k-2} · 4^k = 2^{k-2} → ∞`.

This is exactly the hypothesis of Theorem (11.46) (`map_shift_ne`,
`infinite_extremePoints_G`): Georgii's "`α` can be chosen in such a way that `P` is null
recurrent". Note that `α` is strictly positive, so the conclusions of §11.4 that do *not* need
null recurrence — `nonempty_G` in particular — hold for every `α`. -/
theorem exists_null_recurrent :
    ∃ α : ℕ → ℝ, (∀ y, 0 < α y) ∧ Summable α ∧ (∑' y, α y = 1) ∧
      ∑' n : ℕ, ∑' y : ℕ,
        (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) 0 {y} = ∞ := by
  classical
  set a : ℕ → ℝ := fun y ↦ immigrationWeight p y / 2 with hadef
  have hapos : ∀ y, 0 < a y := fun y ↦ div_pos (immigrationWeight_pos y) two_pos
  have hasum : Summable a := (summable_immigrationWeight hp0 hp1).div_const 2
  have hatot : (∑' y : ℕ, a y) = 1 := by
    rw [hadef, tsum_div_const, tsum_immigrationWeight hp0 hp1]
    norm_num
  refine ⟨a, hapos, hasum, hatot, ?_⟩
  set Tot : ℝ≥0∞ := ∑' n : ℕ, ∑' y : ℕ,
    (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ n) 0 {y} with hTot
  have hkey : ∀ k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ k / 4) ≤ Tot := by
    intro k
    have hx₀0 : extinctionSeq p k ≠ 0 := extinctionSeq_ne_zero hp0 k
    have hT0 : Kernel.tabooMatrix (step p a) 0 0 (extinctionSeq p k)
        = ENNReal.ofReal (a (extinctionSeq p k)) := by
      rw [Kernel.tabooMatrix_apply_of_ne hx₀0]
      simp [step, stepReal]
    -- the mass that the immigration row puts on `x_k`
    have hmass : ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2))
        ≤ Kernel.tabooMatrix (step p a) 0 0 (extinctionSeq p k) := by
      rw [hT0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := le_immigrationWeight_extinctionSeq hp0 hp1 k
      have hid : (1 / 2 : ℝ) ^ (k + 2) = (1 / 2 : ℝ) ^ (k + 1) / 2 := by rw [pow_succ]; ring
      rw [hid, hadef]
      dsimp only
      linarith
    -- the mean extinction time from `x_k`
    have hmean : (4 : ℝ≥0∞) ^ k ≤ ∑' n : ℕ, ∑' y : ℕ,
        (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ n) (extinctionSeq p k) {y} := by
      refine le_trans ?_ (le_tsum_tsum_taboo_step_pow (α := a) hp0 hp1
        (one_le_pow_mul_extinctionSeq hp0 k))
      rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]
      push_cast
      calc (4 : ℝ≥0∞) ^ k * 2 = 2 * 4 ^ k := by ring
        _ ≤ 2 * 4 ^ k + 1 := le_self_add
    have hstep : ∀ n : ℕ, Kernel.tabooMatrix (step p a) 0 0 (extinctionSeq p k)
          * (∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ n)
              (extinctionSeq p k) {y})
        ≤ ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ (n + 1)) 0 {y} := by
      intro n
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun y ↦ ?_
      rw [Kernel.ofMatrix_pow_succ_apply_singleton]
      exact ENNReal.le_tsum (extinctionSeq p k)
    have hreal : (2 : ℝ) ^ k / 4 = (1 / 2 : ℝ) ^ (k + 2) * (4 : ℝ) ^ k := by
      have h2 : (0 : ℝ) < 2 ^ k := by positivity
      rw [div_pow, one_pow, pow_add,
        show ((4 : ℝ) ^ k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k by rw [← mul_pow]; norm_num]
      field_simp
      ring
    have hprod : ENNReal.ofReal ((2 : ℝ) ^ k / 4)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) * (4 : ℝ≥0∞) ^ k := by
      rw [show ((4 : ℝ≥0∞) ^ k) = ENNReal.ofReal ((4 : ℝ) ^ k) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
    calc ENNReal.ofReal ((2 : ℝ) ^ k / 4)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) * (4 : ℝ≥0∞) ^ k := hprod
      _ ≤ Kernel.tabooMatrix (step p a) 0 0 (extinctionSeq p k)
            * ∑' n : ℕ, ∑' y : ℕ,
                (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ n) (extinctionSeq p k) {y} :=
          mul_le_mul' hmass hmean
      _ = ∑' n : ℕ, Kernel.tabooMatrix (step p a) 0 0 (extinctionSeq p k)
            * ∑' y : ℕ, (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ n)
                (extinctionSeq p k) {y} := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' n : ℕ, ∑' y : ℕ,
            (Kernel.ofMatrix (Kernel.tabooMatrix (step p a) 0) ^ (n + 1)) 0 {y} :=
          ENNReal.tsum_le_tsum hstep
      _ ≤ Tot := ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ ↦ n + 1)
          (fun u v huv ↦ by simpa using huv) _
  by_contra hfin
  have hpow : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k, hk⟩ := (hpow.eventually_gt_atTop (4 * Tot.toReal)).exists
  have hle : (2 : ℝ) ^ k / 4 ≤ Tot.toReal := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hkey k)
  have : (2 : ℝ) ^ k ≤ 4 * Tot.toReal := by linarith
  linarith

end NullRecurrentExists

include hαs hα1 in
/-- **Georgii Theorem (11.46), the broken-invariance clause.** If `α` is chosen so that `P` is
null recurrent — Georgii's hypothesis, here in the form `μ_P^0(τ) = ∞`, which
`exists_null_recurrent` shows to be satisfiable — then no Gibbs measure for `γ^Q` is invariant
under any non-trivial shift.

Georgii's Remark (11.7) is `not_exists_isPositiveRecurrent`: a null recurrent `Q` is not
equivalent, in the sense of (11.5), to a positive recurrent stochastic matrix, so
`𝒢_Θ(Q) = ∅`. -/
theorem map_shift_ne
    (hnull : ∑' n : ℕ, ∑' y : ℕ,
      (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) 0 {y} = ∞)
    {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p α) (isTransferMatrix hp0 hp1 hα hαs hα1)))
    {j : ℤ} (hj : j ≠ 0) :
    μ.map (shift ℕ j).toFun ≠ μ :=
  map_shift_ne_of_not_exists_isPositiveRecurrent _
    (not_exists_isPositiveRecurrent hp0 hp1 hα hαs hα1 hnull) hμ hj

include hαs hα1 in
/-- **Georgii Theorem (11.46), the cardinality clause.** With the same null-recurrence hypothesis,
the set `ex 𝒢(Q)` is infinite: the existence of *some* Gibbs measure is Georgii's entrance law
`α_i = lim_n P^n(x_{n-i}, ·)`, which is `nonempty_G`. -/
theorem infinite_extremePoints_G
    (hnull : ∑' n : ℕ, ∑' y : ℕ,
      (Kernel.ofMatrix (Kernel.tabooMatrix (step p α) 0) ^ n) 0 {y} = ∞) :
    ((G (transferSpecification (matrix p α)
      (isTransferMatrix hp0 hp1 hα hαs hα1))).extremePoints ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_of_nonempty_of_not_exists_isPositiveRecurrent _
    (not_exists_isPositiveRecurrent hp0 hp1 hα hαs hα1 hnull) (nonempty_G hp0 hp1 hα hαs hα1)

end MeasureTheory.GibbsMeasure.Markov.Spitzer

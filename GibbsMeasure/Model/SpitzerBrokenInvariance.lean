/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SpitzerCox
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix.FirstPassage

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

The *structural* half of Theorem (11.46) is proved here, at the level of generality at which
Georgii proves it: `matrix_pos`, `tsum_matrix` and `isTransferMatrix` put Spitzer's `Q = P²` into
the framework of §11.1, and `map_shift_ne`, `infinite_extremePoints_G` are Georgii's two
conclusions, deduced from Corollary (11.14) through the general theorems
`MeasureTheory.GibbsMeasure.Markov.map_shift_ne_of_not_exists_isPositiveRecurrent` and
`…infinite_extremePoints_G_of_nonempty_of_not_exists_isPositiveRecurrent`
(`GibbsMeasure/Model/BoundaryLawPhaseTransition.lean`).

The *analytic* preliminaries of §11.4 are now proved: the pure-survival matrix `P̃` of (11.44),
its powers (11.45) `P̃^n(x, y) = ℓ(x, p^n, y)` (Georgii (11.23) iterated), the renewal
decomposition (11.47) — in the general form
`ProbabilityTheory.Kernel.ofMatrix_pow_apply_singleton_eq_taboo_add`
(`GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix/FirstPassage.lean`), specialised to `P`
in `step_pow_apply_singleton` — and the extinction-time law
`μ_P^x(τ = m+1) = (1 - p^{m+1})^x - (1 - p^m)^x`, `μ_P^x(τ ≤ n) = (1 - p^n)^x` for `x ≥ 1`
(`firstPassage_step_add`, `sum_firstPassage_step`).

Two inputs of Theorem (11.46) are still **hypotheses** of the theorems below rather than lemmas,
and this is the honest state of the formalisation:

* `hnotequiv`, that `Q` is not equivalent in the sense of (11.5) to a positive recurrent
  stochastic matrix. Georgii gets this from Remark (11.7) once `Q` is null recurrent. What is
  missing is the passage from `sum_firstPassage_step` at the state `0` — where the immigration
  row `α` enters and `μ_P^0(τ) = 1 + ∑_{x ≥ 1} α(x) μ_P^x(τ) = ∞` for a suitable `α` — to null
  recurrence of `P` and then of `Q = P²`, i.e. Vere-Jones' criterion in the form of Remark
  (11.7); `GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix/Recurrence.lean` has the
  convergence norm and the recurrence/transience dichotomy but not the mean-return-time
  characterisation of positive recurrence.
* `hne`, that `𝒢(Q) ≠ ∅`. This is *the* point of §11.4: Georgii builds an entrance law
  `α_i = lim_n P^n(x_{n-i}, ·)` along a sequence with `x_n p^n → c`. With (11.45) and (11.47) in
  place the remaining inputs are the **Poisson convergence theorem** `ℓ(x_n, p^n, ·) → 𝔭(c, ·)`
  when `x_n p^n → c` (not in Mathlib, and not proved here) and dominated convergence for the
  renewal series; the final step is available, namely the Fatou upgrade
  `α_i P ≤ α_{i+1} ⟹ α_i P = α_{i+1}`
  (`MeasureTheory.GibbsMeasure.Markov.isEntranceLaw_of_forall_tsum_le`), after which
  `IsEntranceLaw.isBoundaryLaw` and Theorem (11.9)(a) produce a Gibbs measure for `Q = P²`.

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
* `map_shift_ne`, `infinite_extremePoints_G` — **Georgii Theorem (11.46)**, modulo the two
  hypotheses above.
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

include hαs hα1 in
/-- **Georgii Theorem (11.46), the broken-invariance clause.** If Spitzer's `Q = P²` is not
equivalent, in the sense of (11.5), to a positive recurrent stochastic matrix — which is what
Georgii's choice of a null recurrent `α` achieves, through Remark (11.7) — then no Gibbs measure
for `γ^Q` is invariant under any non-trivial shift. -/
theorem map_shift_ne
    (hnotequiv : ¬ ∃ (P : ℕ → ℕ → ℝ≥0∞) (c : ℝ≥0∞) (r : ℕ → ℝ≥0∞), 0 < c ∧ c ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = matrix p α x y * r y / (c * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P))
    {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ G (transferSpecification (matrix p α) (isTransferMatrix hp0 hp1 hα hαs hα1)))
    {j : ℤ} (hj : j ≠ 0) :
    μ.map (shift ℕ j).toFun ≠ μ :=
  map_shift_ne_of_not_exists_isPositiveRecurrent _ hnotequiv hμ hj

include hαs hα1 in
/-- **Georgii Theorem (11.46), the cardinality clause.** With the same hypothesis on `Q` and the
existence of *some* Gibbs measure — Georgii's entrance law `α_i = lim_n P^n(x_{n-i}, ·)` — the set
`ex 𝒢(Q)` is infinite. -/
theorem infinite_extremePoints_G
    (hnotequiv : ¬ ∃ (P : ℕ → ℕ → ℝ≥0∞) (c : ℝ≥0∞) (r : ℕ → ℝ≥0∞), 0 < c ∧ c ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = matrix p α x y * r y / (c * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P))
    (hne : (G (transferSpecification (matrix p α)
      (isTransferMatrix hp0 hp1 hα hαs hα1))).Nonempty) :
    ((G (transferSpecification (matrix p α)
      (isTransferMatrix hp0 hp1 hα hαs hα1))).extremePoints ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_of_nonempty_of_not_exists_isPositiveRecurrent _ hnotequiv hne

end MeasureTheory.GibbsMeasure.Markov.Spitzer

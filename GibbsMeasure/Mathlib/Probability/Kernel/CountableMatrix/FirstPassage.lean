/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix

/-!
# First-passage decomposition of the powers of a matrix on a countable space

For a nonnegative matrix `Q` on a countable space and a fixed state `z`, deleting the column of
`z` gives the *taboo matrix* `tabooMatrix Q z`, whose `n`-th power counts the `n`-step paths that
avoid `z` at every positive time. The *first-passage weights* `firstPassage Q z n x` count the
paths from `x` that reach `z` for the first time at time `n + 1`. Decomposing a path according to
the first time it visits `z` gives

`Qⁿ(x, y) = Tⁿ(x, y) + ∑_{m < n} f_m(x) Q^{n-1-m}(z, y)`,

which for a stochastic `Q` is the renewal equation of a Markov chain broken at its first passage
time; it is the identity used by Georgii, *Gibbs Measures and Phase Transitions*, (11.47).

## Main definitions

* `ProbabilityTheory.Kernel.tabooMatrix Q z`: `Q` with the column of `z` set to `0`.
* `ProbabilityTheory.Kernel.firstPassage Q z n x`: the weight of the paths from `x` whose first
  visit to `z` happens at time `n + 1`.

## Main results

* `ProbabilityTheory.Kernel.firstPassage_succ`: the recursion `f_{n+1} = T f_n`.
* `ProbabilityTheory.Kernel.ofMatrix_pow_apply_singleton_eq_taboo_add`: the first-passage
  decomposition above.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} [Countable α] [MeasurableSingletonClass α]

/-- The **taboo matrix** of `Q` at the state `z`: `Q` with the column of `z` deleted. Its `n`-th
power `Tⁿ(x, y)` is the total weight of the `n`-step paths from `x` to `y` that avoid `z` at
every time `1, …, n`. -/
def tabooMatrix (Q : α → α → ℝ≥0∞) (z : α) (x y : α) : ℝ≥0∞ :=
  ({z}ᶜ : Set α).indicator (Q x) y

/-- The **first-passage weights** of `Q` at the state `z`: `firstPassage Q z n x` is the total
weight of the paths starting at `x` that visit `z` for the first time at time `n + 1`. -/
def firstPassage (Q : α → α → ℝ≥0∞) (z : α) (n : ℕ) (x : α) : ℝ≥0∞ :=
  ∑' w, (ofMatrix (tabooMatrix Q z) ^ n) x {w} * Q w z

variable {Q : α → α → ℝ≥0∞} {z : α}

omit [Countable α] in
@[simp] lemma tabooMatrix_apply_self (x : α) : tabooMatrix Q z x z = 0 :=
  Set.indicator_of_notMem (by simp) _

omit [Countable α] in
lemma tabooMatrix_apply_of_ne {y : α} (hy : y ≠ z) (x : α) : tabooMatrix Q z x y = Q x y :=
  Set.indicator_of_mem (by simpa using hy) _

omit [Countable α] in
lemma tabooMatrix_le (x y : α) : tabooMatrix Q z x y ≤ Q x y := by
  rcases eq_or_ne y z with rfl | hy
  · simp
  · rw [tabooMatrix_apply_of_ne hy]

/-- A path counted by a power of the taboo matrix never ends at `z`, unless it starts there and
has length `0`. -/
lemma tabooMatrix_pow_apply_self {x : α} (hx : x ≠ z) (n : ℕ) :
    (ofMatrix (tabooMatrix Q z) ^ n) x {z} = 0 := by
  cases n with
  | zero => rw [pow_zero_apply_singleton, Set.indicator_of_notMem (by simpa using hx)]
  | succ n =>
      rw [ofMatrix_pow_succ'_apply_singleton]
      simp only [tabooMatrix_apply_self, mul_zero, tsum_zero]

/-- A first hit of `z` at time `1` is a single step. -/
@[simp] lemma firstPassage_zero (x : α) : firstPassage Q z 0 x = Q x z := by
  rw [firstPassage, tsum_eq_single x fun w hw ↦ by
    rw [pow_zero_apply_singleton, Set.indicator_of_notMem (by simpa using Ne.symm hw), zero_mul]]
  rw [pow_zero_apply_singleton, Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply,
    one_mul]

/-- Splitting off the first step: `f_{n+1}(x) = ∑_w T(x, w) f_n(w)`. -/
lemma firstPassage_succ (n : ℕ) (x : α) :
    firstPassage Q z (n + 1) x = ∑' w, tabooMatrix Q z x w * firstPassage Q z n w := by
  simp only [firstPassage]
  have h1 : ∀ w : α, (ofMatrix (tabooMatrix Q z) ^ (n + 1)) x {w} * Q w z
      = ∑' v, tabooMatrix Q z x v * (ofMatrix (tabooMatrix Q z) ^ n) v {w} * Q w z := fun w ↦ by
    rw [ofMatrix_pow_succ_apply_singleton, ENNReal.tsum_mul_right]
  rw [tsum_congr h1, ENNReal.tsum_comm]
  refine tsum_congr fun v ↦ ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun w ↦ mul_assoc _ _ _

omit [Countable α] in
/-- Splitting off the first step of an arbitrary path: the step into `z` is separated from the
steps that avoid `z`. -/
lemma tsum_mul_eq_add_tsum_tabooMatrix_mul (x : α) (g : α → ℝ≥0∞) :
    ∑' w, Q x w * g w = Q x z * g z + ∑' w, tabooMatrix Q z x w * g w := by
  classical
  have hdec : ∀ w : α, Q x w * g w
      = (if w = z then Q x z * g z else 0) + tabooMatrix Q z x w * g w := by
    intro w
    rcases eq_or_ne w z with rfl | hw
    · simp
    · simp [tabooMatrix_apply_of_ne hw, hw]
  have hsingle : ∑' w : α, (if w = z then Q x z * g z else 0) = Q x z * g z := by
    rw [tsum_eq_single z fun w hw ↦ by simp [hw]]
    simp
  rw [tsum_congr hdec, ENNReal.tsum_add, hsingle]

/-- **The first-passage decomposition of the powers of `Q`** (Georgii (11.47)). A path of length
`n` from `x` to `y` either avoids `z` at every positive time — the taboo term — or visits `z` for
the first time at some time `m + 1 ≤ n`, after which it is an arbitrary path from `z` of length
`n - 1 - m`. -/
theorem ofMatrix_pow_apply_singleton_eq_taboo_add (Q : α → α → ℝ≥0∞) (z : α) (n : ℕ) (x y : α) :
    (ofMatrix Q ^ n) x {y} = (ofMatrix (tabooMatrix Q z) ^ n) x {y}
      + ∑ m ∈ Finset.range n, firstPassage Q z m x * (ofMatrix Q ^ (n - 1 - m)) z {y} := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      have hih : ∀ w : α, tabooMatrix Q z x w * (ofMatrix Q ^ n) w {y}
          = tabooMatrix Q z x w * (ofMatrix (tabooMatrix Q z) ^ n) w {y}
            + ∑ m ∈ Finset.range n, tabooMatrix Q z x w * firstPassage Q z m w
                * (ofMatrix Q ^ (n - 1 - m)) z {y} := fun w ↦ by
        rw [ih w, mul_add, Finset.mul_sum]
        exact congrArg _ (Finset.sum_congr rfl fun m _ ↦ (mul_assoc _ _ _).symm)
      have hswap : (∑' w, ∑ m ∈ Finset.range n, tabooMatrix Q z x w * firstPassage Q z m w
            * (ofMatrix Q ^ (n - 1 - m)) z {y})
          = ∑ m ∈ Finset.range n, firstPassage Q z (m + 1) x
              * (ofMatrix Q ^ (n - 1 - m)) z {y} := by
        rw [Summable.tsum_finsetSum fun m _ ↦ ENNReal.summable]
        exact Finset.sum_congr rfl fun m _ ↦ by
          rw [ENNReal.tsum_mul_right, firstPassage_succ]
      have hterms : ∀ m ∈ Finset.range n, firstPassage Q z (m + 1) x
          * (ofMatrix Q ^ (n + 1 - 1 - (m + 1))) z {y}
          = firstPassage Q z (m + 1) x * (ofMatrix Q ^ (n - 1 - m)) z {y} := fun m _ ↦ by
        rw [show n + 1 - 1 - (m + 1) = n - 1 - m from by omega]
      calc (ofMatrix Q ^ (n + 1)) x {y}
          = ∑' w, Q x w * (ofMatrix Q ^ n) w {y} := ofMatrix_pow_succ_apply_singleton _ n x y
        _ = Q x z * (ofMatrix Q ^ n) z {y}
              + ∑' w, tabooMatrix Q z x w * (ofMatrix Q ^ n) w {y} :=
            tsum_mul_eq_add_tsum_tabooMatrix_mul x _
        _ = Q x z * (ofMatrix Q ^ n) z {y}
              + ((ofMatrix (tabooMatrix Q z) ^ (n + 1)) x {y}
                + ∑ m ∈ Finset.range n, firstPassage Q z (m + 1) x
                    * (ofMatrix Q ^ (n - 1 - m)) z {y}) := by
            rw [tsum_congr hih, ENNReal.tsum_add, hswap,
              ← ofMatrix_pow_succ_apply_singleton (tabooMatrix Q z) n x y]
        _ = (ofMatrix (tabooMatrix Q z) ^ (n + 1)) x {y}
              + ∑ m ∈ Finset.range (n + 1), firstPassage Q z m x
                  * (ofMatrix Q ^ (n + 1 - 1 - m)) z {y} := by
            rw [Finset.sum_range_succ' (fun m ↦ firstPassage Q z m x
                * (ofMatrix Q ^ (n + 1 - 1 - m)) z {y}) n,
              Finset.sum_congr rfl hterms, show n + 1 - 1 - 0 = n from by omega,
              firstPassage_zero]
            ring

end ProbabilityTheory.Kernel

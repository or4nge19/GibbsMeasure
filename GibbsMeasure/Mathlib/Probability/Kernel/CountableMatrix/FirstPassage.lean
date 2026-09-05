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

/-- A path counted by a positive power of the taboo matrix never *ends* at `z`, whatever its
starting point: its last step avoids the deleted column. -/
lemma tabooMatrix_pow_succ_apply_self (x : α) (n : ℕ) :
    (ofMatrix (tabooMatrix Q z) ^ (n + 1)) x {z} = 0 := by
  rw [ofMatrix_pow_succ'_apply_singleton]
  simp only [tabooMatrix_apply_self, mul_zero, tsum_zero]

/-- **The renewal equation** at the state `z`: `Q^{n+1}(z, z) = ∑_{m ≤ n} f_m(z) Q^{n-m}(z, z)`,
the first-passage decomposition of a path from `z` back to `z`. -/
theorem pow_succ_apply_singleton_self_eq_sum (n : ℕ) :
    (ofMatrix Q ^ (n + 1)) z {z}
      = ∑ m ∈ Finset.range (n + 1), firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z} := by
  rw [ofMatrix_pow_apply_singleton_eq_taboo_add Q z (n + 1) z z,
    tabooMatrix_pow_succ_apply_self z n, zero_add]
  exact Finset.sum_congr rfl fun m _ ↦ by rw [show n + 1 - 1 - m = n - m from by omega]

/-- **Recurrence from a sure first passage** (the renewal criterion). If the first-passage
weights of `Q` at `z` sum to `1` — for a stochastic `Q` this says that the chain started at `z`
returns to `z` almost surely — then the Green function of `Q` at `z` is infinite,
`∑ₙ Qⁿ(z, z) = ∞`. Indeed the renewal equation gives `U = 1 + (∑ₘ f_m) U = 1 + U` for
`U = ∑ₙ Qⁿ(z, z)`, which is impossible for a finite `U`. -/
theorem tsum_pow_apply_singleton_self_eq_top_of_tsum_firstPassage
    (h : ∑' m, firstPassage Q z m z = 1) :
    ∑' n, (ofMatrix Q ^ n) z {z} = ∞ := by
  by_contra hfin
  have hu0 : (ofMatrix Q ^ 0) z {z} = 1 := by
    rw [pow_zero_apply_singleton]
    simp
  have hite : ∀ n : ℕ, (ofMatrix Q ^ (n + 1)) z {z}
      = ∑' m : ℕ, (if m ≤ n then firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z} else 0) := by
    intro n
    rw [pow_succ_apply_singleton_self_eq_sum n,
      tsum_eq_sum (s := Finset.range (n + 1)) fun m hm ↦
        ite_eq_right (by simpa [Nat.lt_succ_iff] using hm)]
    exact (Finset.sum_congr rfl fun m hm ↦
      ite_eq_left (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))).symm
  have hshift : ∀ m : ℕ,
      (∑' n : ℕ, (if m ≤ n then firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z} else 0))
      = firstPassage Q z m z * ∑' j : ℕ, (ofMatrix Q ^ j) z {z} := by
    intro m
    have hz : ∀ i ∈ Finset.range m,
        (if m ≤ i then firstPassage Q z m z * (ofMatrix Q ^ (i - m)) z {z} else 0) = 0 :=
      fun i hi ↦ ite_eq_right (by simpa using Nat.not_le.2 (Finset.mem_range.1 hi))
    have hb := Summable.sum_add_tsum_nat_add'
      (f := fun n : ℕ ↦ (if m ≤ n then firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z}
        else 0)) (k := m) ENNReal.summable
    rw [Finset.sum_eq_zero hz, zero_add] at hb
    rw [← hb, ← ENNReal.tsum_mul_left]
    exact tsum_congr fun j ↦ by rw [ite_eq_left (Nat.le_add_left m j), Nat.add_sub_cancel]
  have hdouble : (∑' n : ℕ, (ofMatrix Q ^ (n + 1)) z {z})
      = ∑' n : ℕ, (ofMatrix Q ^ n) z {z} := by
    calc (∑' n : ℕ, (ofMatrix Q ^ (n + 1)) z {z})
        = ∑' n : ℕ, ∑' m : ℕ,
            (if m ≤ n then firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z} else 0) :=
          tsum_congr hite
      _ = ∑' m : ℕ, ∑' n : ℕ,
            (if m ≤ n then firstPassage Q z m z * (ofMatrix Q ^ (n - m)) z {z} else 0) :=
          ENNReal.tsum_comm
      _ = ∑' m : ℕ, firstPassage Q z m z * ∑' j : ℕ, (ofMatrix Q ^ j) z {z} :=
          tsum_congr hshift
      _ = (∑' m : ℕ, firstPassage Q z m z) * ∑' j : ℕ, (ofMatrix Q ^ j) z {z} :=
          ENNReal.tsum_mul_right
      _ = ∑' n : ℕ, (ofMatrix Q ^ n) z {z} := by rw [h, one_mul]
  have hsplit : (∑' n : ℕ, (ofMatrix Q ^ n) z {z})
      = 1 + ∑' n : ℕ, (ofMatrix Q ^ n) z {z} := by
    conv_lhs => rw [tsum_eq_zero_add' ENNReal.summable]
    rw [hu0, hdouble]
  have h2 : (∑' n : ℕ, (ofMatrix Q ^ n) z {z}) + 1
      = (∑' n : ℕ, (ofMatrix Q ^ n) z {z}) + 0 := by
    rw [add_zero, add_comm _ (1 : ℝ≥0∞), ← hsplit]
  exact one_ne_zero ((ENNReal.add_right_inj hfin).1 h2)

/-! ### Kac's inequality -/

/-- **Kac's inequality, pointwise.** If `v` is an invariant vector of the matrix `Q`, then
`v z ∑_{n < N} Tⁿ(z, y) ≤ v y` for the taboo matrix `T` at `z`: the paths that leave `z` and
have not yet returned carry at most the mass that `v` puts on their current position. -/
theorem mul_sum_taboo_pow_le_of_invariant {v : α → ℝ≥0∞}
    (hv : ∀ y, ∑' x, v x * Q x y = v y) (N : ℕ) (y : α) :
    v z * ∑ n ∈ Finset.range N, (ofMatrix (tabooMatrix Q z) ^ n) z {y} ≤ v y := by
  induction N generalizing y with
  | zero => simp
  | succ N ih =>
      have hterm : ∀ n : ℕ, (ofMatrix (tabooMatrix Q z) ^ (n + 1)) z {y}
          = ∑' w, (ofMatrix (tabooMatrix Q z) ^ n) z {w} * tabooMatrix Q z w y := fun n ↦
        ofMatrix_pow_succ'_apply_singleton _ n z y
      have hhead : v z * ∑ n ∈ Finset.range (N + 1), (ofMatrix (tabooMatrix Q z) ^ n) z {y}
          = v z * (ofMatrix (tabooMatrix Q z) ^ 0) z {y}
            + ∑' w, (v z * ∑ n ∈ Finset.range N, (ofMatrix (tabooMatrix Q z) ^ n) z {w})
                * tabooMatrix Q z w y := by
        rw [Finset.sum_range_succ' _ N, mul_add, add_comm]
        congr 1
        rw [Finset.sum_congr rfl fun n _ ↦ hterm n,
          ← Summable.tsum_finsetSum fun n (_ : n ∈ Finset.range N) ↦ ENNReal.summable,
          ← ENNReal.tsum_mul_left]
        exact tsum_congr fun w ↦ by
          simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [hhead]
      have htail : (∑' w, (v z * ∑ n ∈ Finset.range N, (ofMatrix (tabooMatrix Q z) ^ n) z {w})
          * tabooMatrix Q z w y) ≤ ∑' w, v w * tabooMatrix Q z w y :=
        ENNReal.tsum_le_tsum fun w ↦ mul_le_mul' (ih w) le_rfl
      rcases eq_or_ne y z with hyz | hy
      · have hz : ∀ w, tabooMatrix Q z w y = 0 := fun w ↦ by
          rw [hyz]; exact tabooMatrix_apply_self w
        simp only [hz, mul_zero, tsum_zero, add_zero]
        rw [pow_zero_apply_singleton, Set.indicator_of_mem (by simpa using hyz.symm),
          Pi.one_apply, mul_one, hyz]
      · rw [pow_zero_apply_singleton, Set.indicator_of_notMem (by simpa using Ne.symm hy),
          mul_zero, zero_add]
        refine htail.trans (le_of_eq ?_)
        rw [← hv y]
        exact tsum_congr fun w ↦ by rw [tabooMatrix_apply_of_ne hy]

/-- **Kac's inequality.** If `v` is an invariant vector of `Q`, then `v z ∑ₙ Tⁿ(z, y) ≤ v y`,
`T` the taboo matrix at `z`. -/
theorem mul_tsum_taboo_pow_le_of_invariant {v : α → ℝ≥0∞}
    (hv : ∀ y, ∑' x, v x * Q x y = v y) (y : α) :
    v z * ∑' n : ℕ, (ofMatrix (tabooMatrix Q z) ^ n) z {y} ≤ v y := by
  rw [ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
  exact iSup_le fun N ↦ mul_sum_taboo_pow_le_of_invariant hv N y

/-- **Kac's inequality, in total mass**: `v z` times the expected time the chain spends away from
`z` before returning — `∑ₙ ∑_y Tⁿ(z, y) = E_z[τ_z]` for a stochastic `Q` — is at most the total
mass of `v`. So an invariant vector of finite total mass forces a finite mean return time: a
null recurrent matrix has no invariant probability vector. -/
theorem mul_tsum_tsum_taboo_pow_le_of_invariant {v : α → ℝ≥0∞}
    (hv : ∀ y, ∑' x, v x * Q x y = v y) :
    v z * ∑' n : ℕ, ∑' y : α, (ofMatrix (tabooMatrix Q z) ^ n) z {y} ≤ ∑' y, v y := by
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun y ↦ mul_tsum_taboo_pow_le_of_invariant hv y

/-- **Kac's theorem, the negative half.** If `Q` has an invariant vector `v` of finite total mass
which does not vanish at `z`, then the mean return time to `z` is finite. Contrapositively: a
matrix whose mean return time `∑ₙ ∑_y Tⁿ(z, y)` to `z` is infinite admits no invariant vector of
finite total mass that is positive at `z` — in particular no invariant probability vector, so a
null recurrent stochastic matrix is never positive recurrent. -/
theorem tsum_tsum_taboo_pow_ne_top_of_invariant {v : α → ℝ≥0∞}
    (hv : ∀ y, ∑' x, v x * Q x y = v y) (hv0 : v z ≠ 0) (hvt : ∑' y, v y ≠ ∞) :
    ∑' n : ℕ, ∑' y : α, (ofMatrix (tabooMatrix Q z) ^ n) z {y} ≠ ∞ := by
  intro h
  have hle := mul_tsum_tsum_taboo_pow_le_of_invariant (z := z) hv
  rw [h, ENNReal.mul_top hv0] at hle
  exact hvt (top_le_iff.1 hle)

/-! ### A sure first passage -/

/-- **A sure first passage propagates along a stochastic row.** If from every state `w ≠ z` the
chain reaches `z` almost surely — `∑ₘ f_m(w) = 1` — and the row of `z` is stochastic, then the
chain started at `z` returns to `z` almost surely. Splitting the first step gives
`∑ₘ f_m(z) = Q(z, z) + ∑_{w ≠ z} Q(z, w) ∑ₘ f_m(w) = ∑_w Q(z, w) = 1`. -/
theorem tsum_firstPassage_self_eq_one (hQ : ∑' y, Q z y = 1)
    (h : ∀ w, w ≠ z → ∑' m : ℕ, firstPassage Q z m w = 1) :
    ∑' m : ℕ, firstPassage Q z m z = 1 := by
  have hterm : ∀ w : α, tabooMatrix Q z z w * ∑' m : ℕ, firstPassage Q z m w
      = tabooMatrix Q z z w * 1 := by
    intro w
    rcases eq_or_ne w z with rfl | hw
    · rw [tabooMatrix_apply_self, zero_mul, zero_mul]
    · rw [h w hw]
  calc ∑' m : ℕ, firstPassage Q z m z
      = firstPassage Q z 0 z + ∑' m : ℕ, firstPassage Q z (m + 1) z :=
        tsum_eq_zero_add' ENNReal.summable
    _ = Q z z * 1 + ∑' w, tabooMatrix Q z z w * ∑' m : ℕ, firstPassage Q z m w := by
        rw [firstPassage_zero, mul_one]
        congr 1
        rw [tsum_congr fun m ↦ firstPassage_succ m z, ENNReal.tsum_comm]
        exact tsum_congr fun w ↦ ENNReal.tsum_mul_left
    _ = Q z z * 1 + ∑' w, tabooMatrix Q z z w * (1 : ℝ≥0∞) := by rw [tsum_congr hterm]
    _ = ∑' w, Q z w * (1 : ℝ≥0∞) :=
        (tsum_mul_eq_add_tsum_tabooMatrix_mul z fun _ ↦ (1 : ℝ≥0∞)).symm
    _ = 1 := by simpa using hQ

end ProbabilityTheory.Kernel

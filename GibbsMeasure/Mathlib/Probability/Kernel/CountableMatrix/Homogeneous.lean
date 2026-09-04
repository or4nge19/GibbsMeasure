/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix.Recurrence

/-!
# Transposed matrices, and translation invariant stochastic matrices

Two facts about matrices on a countable space that are needed for random walks but are
statements about kernels alone.

## Main results

* `ProbabilityTheory.Kernel.ofMatrix_transpose_pow_apply_singleton`: transposing a matrix
  transposes every power of the associated kernel, `ᵗQ^n(x, y) = Q^n(y, x)`. (No stochasticity,
  no positivity: this is path reversal for the matrix product.)
* `ProbabilityTheory.Kernel.not_isPositiveRecurrent_ofMatrix_of_translationInvariant`: a
  translation invariant stochastic matrix with positive entries on an *infinite* countable
  additive group is never positive recurrent. This is the "well-known" fact quoted in the proof
  of Georgii's Corollary (11.19) for `E = ℤ^N`. Georgii deduces it from the ergodic theorem
  (10.34); the proof here uses instead the Liouville property of recurrent kernels
  (`IsRecurrent.apply_eq_apply_of_lintegral_le`): an invariant probability vector `α` of `P` is
  a bounded harmonic function of the *transposed* matrix `ᵗP`, which is stochastic by translation
  invariance and recurrent by the transposition lemma above; hence `α` is constant, which no
  probability vector on an infinite space can be.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α} [Countable α] [MeasurableSingletonClass α]

/-- **Path reversal.** Transposing a matrix transposes every power of the associated kernel:
`ᵗQ^n(x, y) = Q^n(y, x)`. -/
theorem ofMatrix_transpose_pow_apply_singleton (Q : α → α → ℝ≥0∞) (n : ℕ) (x y : α) :
    (ofMatrix (fun a b ↦ Q b a) ^ n) x {y} = (ofMatrix Q ^ n) y {x} := by
  induction n generalizing x y with
  | zero =>
    rcases eq_or_ne x y with rfl | h
    · rfl
    · simp only [pow_zero_apply_singleton]
      rw [Set.indicator_of_notMem (by simpa using h),
        Set.indicator_of_notMem (by simpa using h.symm)]
  | succ n ih =>
    rw [ofMatrix_pow_succ_apply_singleton, ofMatrix_pow_succ'_apply_singleton]
    exact tsum_congr fun b ↦ by rw [ih, mul_comm]

section TranslationInvariant

variable {α : Type*} [AddCommGroup α] [Countable α] {mα : MeasurableSpace α}
  [MeasurableSingletonClass α] {P : α → α → ℝ≥0∞}

omit [Countable α] in
/-- A translation invariant matrix is determined by its `0`-th row: `P(x, y) = P(0, y - x)`. -/
theorem apply_eq_apply_zero_sub_of_translationInvariant
    (hhom : ∀ x y z, P (x + z) (y + z) = P x y) (x y : α) : P x y = P 0 (y - x) := by
  have h := hhom 0 (y - x) x
  rw [zero_add, sub_add_cancel] at h
  exact h

omit [Countable α] in
/-- The *columns* of a translation invariant stochastic matrix sum to one as well: the transposed
matrix `ᵗP` is stochastic. -/
theorem tsum_apply_eq_one_of_translationInvariant
    (hstoch : ∀ x, ∑' y, P x y = 1) (hhom : ∀ x y z, P (x + z) (y + z) = P x y) (x : α) :
    ∑' y, P y x = 1 := by
  calc ∑' y, P y x = ∑' y, P 0 (x - y) :=
        tsum_congr fun y ↦ apply_eq_apply_zero_sub_of_translationInvariant hhom y x
    _ = ∑' w, P 0 w := (Equiv.subLeft x).tsum_eq fun w ↦ P 0 w
    _ = 1 := hstoch 0

/-- **A translation invariant stochastic matrix with positive entries on an infinite countable
additive group is never positive recurrent.** (Georgii, proof of Corollary (11.19), step 1.) -/
theorem not_isPositiveRecurrent_ofMatrix_of_translationInvariant [Infinite α]
    (hpos : ∀ x y, 0 < P x y) (hstoch : ∀ x, ∑' y, P x y = 1)
    (hhom : ∀ x y z, P (x + z) (y + z) = P x y) :
    ¬ IsPositiveRecurrent (ofMatrix P) := by
  rintro ⟨hrec, μ, hμprob, hμinv⟩
  have := hμprob
  have : IsMarkovKernel (ofMatrix P) := isMarkovKernel_ofMatrix _ hstoch
  -- the transposed matrix
  set R : α → α → ℝ≥0∞ := fun x y ↦ P y x with hR
  have : IsMarkovKernel (ofMatrix R) := isMarkovKernel_ofMatrix _ fun x ↦
    tsum_apply_eq_one_of_translationInvariant hstoch hhom x
  have : IsIrreducible (Measure.count : Measure α) (ofMatrix R) :=
    isIrreducible_count_ofMatrix_of_forall_pos fun x y ↦ hpos y x
  have hRrec : IsRecurrent (ofMatrix R) := fun x ↦ by
    rw [potential_apply_singleton]
    calc ∑' n, (ofMatrix R ^ n) x {x}
        = ∑' n, (ofMatrix P ^ n) x {x} :=
          tsum_congr fun n ↦ ofMatrix_transpose_pow_apply_singleton P n x x
      _ = potential (ofMatrix P) x {x} := (potential_apply_singleton _ _ _).symm
      _ = ∞ := hrec x
  -- the invariant probability vector is harmonic for the transposed matrix
  have hharm : ∀ x, ∫⁻ y, μ {y} ∂(ofMatrix R x) = μ {x} := fun x ↦ by
    rw [lintegral_ofMatrix]
    exact ((hμinv.apply_singleton_eq_tsum x).trans
      (tsum_congr fun y ↦ by rw [ofMatrix_apply_singleton, hR, mul_comm])).symm
  have hconst := hRrec.apply_eq_apply_of_lintegral_le (r := fun x ↦ μ {x})
    (fun x ↦ measure_ne_top μ {x}) fun x ↦ (hharm x).le
  -- a constant probability vector on an infinite space is absurd
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  have hsum : ∑' _ : α, μ {x₀} = 1 := by
    calc ∑' _ : α, μ {x₀} = ∑' x, μ {x} := tsum_congr fun x ↦ (hconst x x₀).symm
      _ = μ Set.univ := Measure.tsum_apply_singleton μ
      _ = 1 := measure_univ
  rcases eq_or_ne (μ {x₀}) 0 with h0 | h0
  · simp [h0] at hsum
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hsum
    exact ENNReal.top_ne_one hsum

end TranslationInvariant

end ProbabilityTheory.Kernel

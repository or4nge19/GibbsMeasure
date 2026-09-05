/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Reflections of `ZMod n` in natural-number coordinates

The map `z ↦ -1 - z` is the involution of `ZMod n` that exchanges `{0, …, n/2 - 1}` and
`{n/2, …, n - 1}`; in natural-number coordinates it is `j ↦ n - 1 - j`
(`ZMod.neg_one_sub_natCast`).  These are the elementary facts needed whenever a cyclic group is
used as a discrete torus with a reflection.
-/

@[expose] public section

namespace ZMod

variable {n : ℕ} [NeZero n]

/-- `n - 1` is `-1` in `ZMod n`. -/
theorem natCast_pred_eq_neg_one : ((n - 1 : ℕ) : ZMod n) = -1 := by
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have h : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
    rw [← Nat.cast_one (R := ZMod n), ← Nat.cast_add, Nat.sub_add_cancel hn, ZMod.natCast_self]
  exact eq_neg_of_add_eq_zero_left h

/-- The reflection `z ↦ -1 - z` of `ZMod n` in natural-number coordinates. -/
theorem neg_one_sub_natCast {j : ℕ} (hj : j < n) :
    -1 - (j : ZMod n) = ((n - 1 - j : ℕ) : ZMod n) := by
  have h : ((n - 1 - j : ℕ) : ZMod n) + (j : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
  rw [natCast_pred_eq_neg_one] at h
  exact (eq_sub_of_add_eq h).symm

/-- Every element of `ZMod n` is the cast of its own `val`. -/
theorem natCast_val_self (z : ZMod n) : ((z.val : ℕ) : ZMod n) = z := by
  simp

end ZMod

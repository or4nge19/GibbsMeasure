/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The reflection `z ↦ -z` of `ZMod (2 * m)`

`z ↦ -z` reflects the cycle `ZMod (2 * m)` across its two fixed points `0` and `m`
(`ZMod.neg_eq_self_iff_of_two_mul`); in natural-number coordinates it is `v ↦ 2m - v` off `0`. It
exchanges the closed halves `{0, …, m}` and `{m, …, 2m - 1} ∪ {0}`, which cover the cycle and meet
in the fixed points (`ZMod.val_le_or_val_neg_le`, `ZMod.val_le_and_val_neg_le_iff`). A unit step
`{z, z + 1}` lies in a closed half, and for `1 < m` in only one
(`ZMod.val_le_and_val_add_one_le_iff_not`); so does `{z - 1, z, z + 1}` centred off the fixed
points. These are the two halves of a torus cut by a reflection plane through sites, with the
plane and its antipode fixed.
-/

public section

namespace ZMod

variable {n m : ℕ}

theorem val_add_one_eq_ite [NeZero n] (a : ZMod n) :
    (a + 1).val = if a.val + 1 = n then 0 else a.val + 1 := by
  have ha := a.val_lt
  rw [val_add, val_one_eq_one_mod, Nat.add_mod_mod]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem val_sub_one_eq_ite [NeZero n] (a : ZMod n) :
    (a - 1).val = if a.val = 0 then n - 1 else a.val - 1 := by
  have h := val_add_one_eq_ite (a - 1)
  rw [sub_add_cancel] at h
  have := (a - 1).val_lt
  split_ifs at h ⊢ <;> omega

theorem val_neg_eq_ite [NeZero n] (a : ZMod n) :
    (-a).val = if a.val = 0 then 0 else n - a.val := by
  rw [neg_val]
  by_cases h : a = 0
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right ((val_eq_zero a).not.2 h)]

theorem eq_natCast_iff_val_eq [NeZero n] {a : ZMod n} {k : ℕ} (hk : k < n) :
    a = k ↔ a.val = k := by
  refine ⟨fun h ↦ h ▸ val_cast_of_lt hk, fun h ↦ ?_⟩
  rw [← natCast_zmod_val a, h]

/-- The fixed points of `z ↦ -z` on `ZMod (2 * m)` are `0` and `m`. -/
theorem neg_eq_self_iff_of_two_mul [NeZero m] (a : ZMod (2 * m)) : -a = a ↔ a = 0 ∨ a = m := by
  have hm : m < 2 * m := by have := NeZero.pos m; omega
  rw [neg_eq_self_iff, eq_natCast_iff_val_eq hm, ← val_eq_zero]
  omega

/-- The closed halves `{0, …, m}` and `-{0, …, m}` cover `ZMod (2 * m)`. -/
theorem val_le_or_val_neg_le [NeZero m] (a : ZMod (2 * m)) : a.val ≤ m ∨ (-a).val ≤ m := by
  rw [val_neg_eq_ite]
  have := a.val_lt
  split_ifs <;> first | contradiction | omega

/-- The closed halves `{0, …, m}` and `-{0, …, m}` meet in the fixed points `0` and `m`. -/
theorem val_le_and_val_neg_le_iff [NeZero m] (a : ZMod (2 * m)) :
    a.val ≤ m ∧ (-a).val ≤ m ↔ a = 0 ∨ a = m := by
  have hm : m < 2 * m := by have := NeZero.pos m; omega
  rw [val_neg_eq_ite, ← val_eq_zero, eq_natCast_iff_val_eq hm]
  have := a.val_lt
  split_ifs <;> first | contradiction | omega

/-- A unit step `{a, a + 1}` lies in one of the closed halves `±{0, …, m}`. -/
theorem val_le_and_val_add_one_le_or [NeZero m] (a : ZMod (2 * m)) :
    a.val ≤ m ∧ (a + 1).val ≤ m ∨ (-a).val ≤ m ∧ (-(a + 1)).val ≤ m := by
  rw [val_neg_eq_ite, val_neg_eq_ite (a + 1), val_add_one_eq_ite]
  have := a.val_lt
  split_ifs <;> first | contradiction | omega

/-- For `1 < m` a unit step `{a, a + 1}` lies in exactly one of the closed halves `±{0, …, m}`:
it cannot join the fixed points `0` and `m`. -/
theorem val_le_and_val_add_one_le_iff_not (hm : 1 < m) (a : ZMod (2 * m)) :
    a.val ≤ m ∧ (a + 1).val ≤ m ↔ ¬((-a).val ≤ m ∧ (-(a + 1)).val ≤ m) := by
  have : NeZero m := ⟨by omega⟩
  rw [val_neg_eq_ite, val_neg_eq_ite (a + 1), val_add_one_eq_ite]
  have := a.val_lt
  split_ifs <;> first | contradiction | omega

/-- For `1 < m`, a double step `{a - 1, a, a + 1}` centred off the fixed points lies in exactly one
of the closed halves `±{0, …, m}`. -/
theorem val_sub_one_le_and_val_le_and_val_add_one_le_iff_not (hm : 1 < m) {a : ZMod (2 * m)}
    (h₀ : a ≠ 0) (hm' : a ≠ m) :
    (a - 1).val ≤ m ∧ a.val ≤ m ∧ (a + 1).val ≤ m ↔
      ¬((-(a - 1)).val ≤ m ∧ (-a).val ≤ m ∧ (-(a + 1)).val ≤ m) := by
  have : NeZero m := ⟨by omega⟩
  rw [Ne, ← val_eq_zero] at h₀
  rw [Ne, eq_natCast_iff_val_eq (show m < 2 * m by omega)] at hm'
  rw [val_neg_eq_ite (a - 1), val_neg_eq_ite a, val_neg_eq_ite (a + 1), val_sub_one_eq_ite,
    val_add_one_eq_ite]
  have := a.val_lt
  split_ifs <;> first | contradiction | omega

end ZMod

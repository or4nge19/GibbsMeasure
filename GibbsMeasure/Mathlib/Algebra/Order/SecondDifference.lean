/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# A quadratic bound from bounded second differences

If the second differences `g (n + 1) + g (n - 1) - 2 g n` of a sequence `g : ℤ → R` are bounded
above by `M`, then the symmetric second difference of step `k` is bounded by `k ^ 2 * M`:
`g k + g (-k) - 2 g 0 ≤ k ^ 2 * M`. This is the discrete analogue of `g'' ≤ M ⟹ g(k) + g(-k) -
2 g(0) ≤ k² M`, and is the estimate behind Georgii, *Gibbs Measures and Phase Transitions*,
Comment (9.13)(2).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Bounded second differences give a quadratic bound.** If
`g (n + 1) + g (n - 1) - 2 g n ≤ M` for every `n : ℤ`, then `g k + g (-k) - 2 g 0 ≤ k ^ 2 * M` for
every `k : ℕ`. -/
theorem add_neg_sub_two_mul_le_natCast_sq_mul_of_forall_le {g : ℤ → R} {M : R}
    (h : ∀ n : ℤ, g (n + 1) + g (n - 1) - 2 * g n ≤ M) (k : ℕ) :
    g k + g (-k) - 2 * g 0 ≤ (k : R) ^ 2 * M := by
  set a : ℤ → R := fun n ↦ g (n + 1) - g n with ha
  have hstep : ∀ n : ℤ, a n ≤ a (n - 1) + M := fun n ↦ by
    have := h n
    simp only [ha, sub_add_cancel]
    linarith
  -- forward differences grow at most linearly to the right ...
  have h1 : ∀ m : ℕ, a m ≤ a 0 + m * M := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have := hstep ((m : ℤ) + 1)
      rw [add_sub_cancel_right] at this
      push_cast
      linarith
  -- ... and decay at most linearly to the left
  have h2 : ∀ m : ℕ, a 0 - ((m : R) + 1) * M ≤ a (-((m : ℤ) + 1)) := by
    intro m
    induction m with
    | zero =>
      have := hstep 0
      simp only [zero_sub, Nat.cast_zero, zero_add] at this ⊢
      simpa using this
    | succ m ih =>
      have := hstep (-((m : ℤ) + 1))
      rw [show -((m : ℤ) + 1) - 1 = -(((m + 1 : ℕ) : ℤ) + 1) by push_cast; ring] at this
      push_cast at this ⊢
      linarith
  -- telescoping to the right
  have h3 : ∀ k : ℕ, 2 * (g k - g 0) ≤ 2 * k * a 0 + M * (k * (k - 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := h1 k
      have hg : g ((k + 1 : ℕ) : ℤ) - g 0 = (g k - g 0) + a k := by
        simp only [ha]
        push_cast
        ring
      rw [hg]
      push_cast
      nlinarith [hk, ih]
  -- telescoping to the left
  have h4 : ∀ k : ℕ, 2 * k * a 0 - M * (k * (k + 1)) ≤ 2 * (g 0 - g (-(k : ℤ))) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk := h2 k
      have hg : g 0 - g (-((k + 1 : ℕ) : ℤ)) = (g 0 - g (-(k : ℤ))) + a (-((k : ℤ) + 1)) := by
        simp only [ha]
        push_cast
        rw [show -((k : ℤ) + 1) + 1 = -(k : ℤ) by ring]
        ring
      rw [hg]
      push_cast
      nlinarith [hk, ih]
  have h5 := h3 k
  have h6 := h4 k
  have h2pos : (0 : R) < 2 := two_pos
  have : 2 * (g k + g (-(k : ℤ)) - 2 * g 0) ≤ 2 * ((k : R) ^ 2 * M) := by nlinarith [h5, h6]
  exact le_of_mul_le_mul_left this h2pos

end

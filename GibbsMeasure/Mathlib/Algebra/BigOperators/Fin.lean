/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Telescoping sums over `Fin`

`∑_{q : Fin n} (f q.castSucc - f q.succ) = f 0 - f (Fin.last n)` for `f : Fin (n + 1) → M`.

Searched (pin `d13f23b7`): `Mathlib/Algebra/BigOperators/Fin.lean` has the alternating
`Fin.sum_neg_one_pow_eq_zero` and the `range` telescopes `Finset.sum_range_sub`,
`Finset.sum_range_sub'`, but no telescope indexed by `Fin`.
-/

@[expose] public section

namespace Fin

variable {M : Type*} [AddCommGroup M]

/-- **Telescoping over `Fin`**: `∑_{q : Fin n} (f q.castSucc - f q.succ) = f 0 - f (last n)`. -/
theorem sum_univ_castSucc_sub_succ : ∀ {n : ℕ} (f : Fin (n + 1) → M),
    ∑ q : Fin n, (f q.castSucc - f q.succ) = f 0 - f (last n)
  | 0, f => by simp
  | n + 1, f => by
    rw [sum_univ_castSucc]
    have h := sum_univ_castSucc_sub_succ (n := n) (f ∘ castSucc)
    simp only [Function.comp_apply, castSucc_zero] at h
    simp only [succ_castSucc, h, succ_last]
    exact sub_add_sub_cancel _ _ _

end Fin

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.EReal.Inv

/-!
# Division in `EReal` by a natural number
-/

@[expose] public section

namespace EReal

/-- `⊥ / n = ⊥` for a nonzero natural number `n`. -/
lemma bot_div_natCast {n : ℕ} (hn : n ≠ 0) : (⊥ : EReal) / (n : EReal) = ⊥ := by
  rw [div_eq_mul_inv, ← EReal.coe_natCast, ← EReal.coe_inv]
  exact EReal.bot_mul_of_pos (EReal.coe_pos.2 (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))))

end EReal

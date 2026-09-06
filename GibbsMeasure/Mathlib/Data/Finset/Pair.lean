/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Set.Insert

/-!
# Equality of unordered pairs of a `Finset`

`Finset.pair_eq_pair_iff` is the `Finset` counterpart of `Set.pair_eq_pair_iff`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [DecidableEq α] {x y z w : α}

theorem pair_eq_pair_iff :
    ({x, y} : Finset α) = ({z, w} : Finset α) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  rw [← Finset.coe_inj]
  simpa using Set.pair_eq_pair_iff

end Finset

end

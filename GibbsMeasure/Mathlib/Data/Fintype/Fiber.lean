/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# The fibres of an evaluation map on a finite function space

For finite types `ι` and `α` and a point `j : ι`, the evaluation map `f ↦ f j` from `ι → α` to
`α` has fibres of constant size `|α| ^ (|ι| - 1)`: fixing one coordinate leaves the remaining
`|ι| - 1` coordinates free. This is Mathlib's
`Fintype.card_filter_piFinset_const_eq_of_mem` at `s = univ`, and the point of the two lemmas
below is only to have it in the `ι → α` form, without a `Fintype.piFinset`.

## Main results

* `Finset.card_filter_eval_eq`: the fibre `{f : ι → α | f j = v}` has `|α| ^ (|ι| - 1)` elements.
* `Finset.sum_ite_eval_eq`: summing a constant over that fibre.
-/

@[expose] public section

namespace Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- **The fibres of an evaluation map on a finite function space.**  Fixing the value of a
function `ι → α` at one point `j` leaves the other `|ι| - 1` coordinates free, so the fibre has
`|α| ^ (|ι| - 1)` elements. This is `Fintype.card_filter_piFinset_const_eq_of_mem` at
`s = Finset.univ`, where `Fintype.piFinset fun _ ↦ univ` is all of `ι → α`. -/
theorem card_filter_eval_eq (j : ι) (v : α) :
    (Finset.univ.filter fun f : ι → α ↦ f j = v).card
      = Fintype.card α ^ (Fintype.card ι - 1) := by
  simpa [Fintype.piFinset_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset α) j (Finset.mem_univ v)

/-- Summing a constant over the fibre `{f : ι → α | f j = v}` of an evaluation map. -/
theorem sum_ite_eval_eq {M : Type*} [AddCommMonoid M] (j : ι) (v : α) (c : M) :
    ∑ f : ι → α, (if f j = v then c else 0)
      = (Fintype.card α ^ (Fintype.card ι - 1)) • c := by
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_eval_eq j v]

end Finset

end

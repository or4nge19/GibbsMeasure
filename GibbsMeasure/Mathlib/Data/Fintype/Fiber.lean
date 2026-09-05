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
`|ι| - 1` coordinates free.

## Main results

* `Finset.card_filter_eval_eq`: the fibre `{f : ι → α | f j = v}` has `|α| ^ (|ι| - 1)` elements.
* `Finset.sum_ite_eval_eq`: summing a constant over that fibre.
-/

@[expose] public section

namespace Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-- **The fibres of an evaluation map on a finite function space.**  Fixing the value of a
function `ι → α` at one point `j` leaves the other `|ι| - 1` coordinates free, so the fibre has
`|α| ^ (|ι| - 1)` elements. -/
theorem card_filter_eval_eq (j : ι) (v : α) :
    (Finset.univ.filter fun f : ι → α ↦ f j = v).card
      = Fintype.card α ^ (Fintype.card ι - 1) := by
  have hset : (Finset.univ.filter fun f : ι → α ↦ f j = v)
      = Fintype.piFinset (fun c ↦ if c = j then ({v} : Finset α) else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h c
      by_cases hc : c = j
      · subst hc; simp [h]
      · simp [hc]
    · intro h; simpa using h j
  rw [hset, Fintype.card_piFinset, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  have hj : (if j = j then ({v} : Finset α) else Finset.univ).card = 1 := by simp
  have hother : ∀ c ∈ Finset.univ.erase j,
      (if c = j then ({v} : Finset α) else Finset.univ).card = Fintype.card α := by
    intro c hc
    have hne : ¬ (c = j) := Finset.ne_of_mem_erase hc
    simp only [hne, ↓reduceIte, Finset.card_univ]
  rw [Finset.prod_congr rfl hother, hj, mul_one, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]

/-- Summing a constant over the fibre `{f : ι → α | f j = v}` of an evaluation map. -/
theorem sum_ite_eval_eq {M : Type*} [AddCommMonoid M] (j : ι) (v : α) (c : M) :
    ∑ f : ι → α, (if f j = v then c else 0)
      = (Fintype.card α ^ (Fintype.card ι - 1)) • c := by
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_eval_eq j v]

end Finset

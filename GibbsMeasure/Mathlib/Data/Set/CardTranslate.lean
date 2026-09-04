/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Set.Card

/-!
# Translation parity of a finite set in an additive group

For a finite subset `s` of an additive group and any `g`, the elements of `s` whose translate
`x + g` leaves `s` are exactly as many as those whose translate `x - g` leaves `s`:

`{x ∈ s | x + g ∉ s}.ncard = {x ∈ s | x - g ∉ s}.ncard`.

Both counts equal `s.ncard - {x ∈ s | x + g ∈ s}.ncard`, and `x ↦ x + g` is a bijection from
`{x ∈ s | x + g ∈ s}` onto `{x ∈ s | x - g ∈ s}`.

Along a fixed direction of `ℤ²` this says that a finite set has as many "right ends" as
"left ends"; it is what makes the horizontal contributions cancel in Georgii's contour estimate
(6.24), see `GibbsMeasure/Model/RandomStaircase.lean`.
-/

@[expose] public section

namespace Set

variable {G : Type*} [AddGroup G] {s : Set G}

/-- The elements of `s` that stay in `s` after translation by `g` are in bijection, via that
translation, with the elements of `s` that stay in `s` after translation by `-g`. -/
theorem bijOn_add_sep_mem (s : Set G) (g : G) :
    BijOn (· + g) {x ∈ s | x + g ∈ s} {x ∈ s | x - g ∈ s} :=
  ⟨fun _ hx ↦ ⟨hx.2, by simpa using hx.1⟩, fun _ _ _ _ h ↦ by simpa using h,
    fun y hy ↦ ⟨y - g, ⟨hy.2, by simpa using hy.1⟩, by simp⟩⟩

/-- The elements of `s` leaving `s` under translation by `g`, together with those staying in `s`,
exhaust `s`. -/
theorem ncard_sep_add_notMem_add_ncard_sep_add_mem (hs : s.Finite) (g : G) :
    {x ∈ s | x + g ∉ s}.ncard + {x ∈ s | x + g ∈ s}.ncard = s.ncard := by
  rw [← ncard_union_eq (by
      rw [disjoint_left]
      rintro x ⟨-, hx⟩ ⟨-, hx'⟩
      exact hx hx') (hs.subset fun _ hx ↦ hx.1) (hs.subset fun _ hx ↦ hx.1)]
  congr 1
  ext x
  by_cases hx : x + g ∈ s <;> simp [hx, and_comm]

/-- **Translation parity.** In an additive group, a finite set has as many elements leaving it
under translation by `g` as under translation by `-g`. -/
theorem ncard_sep_add_notMem_eq (hs : s.Finite) (g : G) :
    {x ∈ s | x + g ∉ s}.ncard = {x ∈ s | x - g ∉ s}.ncard := by
  have hPQ : {x ∈ s | x + g ∈ s}.ncard = {x ∈ s | x - g ∈ s}.ncard :=
    (bijOn_add_sep_mem s g).ncard_eq
  have h₁ := ncard_sep_add_notMem_add_ncard_sep_add_mem hs g
  have h₂ := ncard_sep_add_notMem_add_ncard_sep_add_mem hs (-g)
  simp only [← sub_eq_add_neg] at h₂
  omega

end Set

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Comparing the oscillation of two uniformly close bounded functions

The *oscillation* of a bounded real function `g` along a filter `F` is `limsup g F − liminf g F`.
If `g` and `h` are uniformly within `c` of each other eventually along `F`, their oscillations
differ by at most `2c`.

## Main results

* `Filter.limsup_sub_liminf_le_of_eventually_abs_sub_le`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace Filter

variable {α : Type*} {F : Filter α} [F.NeBot] {g h : α → ℝ} {c M : ℝ}

/-- Two bounded functions that are eventually within `c` of one another have oscillations
`limsup − liminf` differing by at most `2c`. -/
theorem limsup_sub_liminf_le_of_eventually_abs_sub_le
    (hg : ∀ a, |g a| ≤ M) (hh : ∀ a, |h a| ≤ M) (hgh : ∀ᶠ a in F, |g a - h a| ≤ c) :
    limsup g F - liminf g F ≤ (limsup h F - liminf h F) + 2 * c := by
  have hgb : F.IsBoundedUnder (· ≤ ·) g := isBoundedUnder_of ⟨M, fun a ↦ (abs_le.1 (hg a)).2⟩
  have hhb : F.IsBoundedUnder (· ≤ ·) h := isBoundedUnder_of ⟨M, fun a ↦ (abs_le.1 (hh a)).2⟩
  have hgb' : F.IsBoundedUnder (· ≥ ·) g := isBoundedUnder_of ⟨-M, fun a ↦ (abs_le.1 (hg a)).1⟩
  have hhb' : F.IsBoundedUnder (· ≥ ·) h := isBoundedUnder_of ⟨-M, fun a ↦ (abs_le.1 (hh a)).1⟩
  have hgc : F.IsCoboundedUnder (· ≤ ·) g :=
    isCoboundedUnder_le_of_le (x := -M) F fun a ↦ (abs_le.1 (hg a)).1
  have hgc' : F.IsCoboundedUnder (· ≥ ·) g :=
    isCoboundedUnder_ge_of_le (x := M) F fun a ↦ (abs_le.1 (hg a)).2
  have hhc : F.IsCoboundedUnder (· ≤ ·) h :=
    isCoboundedUnder_le_of_le (x := -M) F fun a ↦ (abs_le.1 (hh a)).1
  have hhc' : F.IsCoboundedUnder (· ≥ ·) h :=
    isCoboundedUnder_ge_of_le (x := M) F fun a ↦ (abs_le.1 (hh a)).2
  have hbc : F.IsBoundedUnder (· ≤ ·) (fun a ↦ h a + c) :=
    isBoundedUnder_of ⟨M + c, fun a ↦ by linarith [(abs_le.1 (hh a)).2]⟩
  have hbc' : F.IsCoboundedUnder (· ≥ ·) (fun a ↦ g a + c) :=
    isCoboundedUnder_ge_of_le (x := M + c) F fun a ↦ by linarith [(abs_le.1 (hg a)).2]
  have h1 : limsup g F ≤ limsup h F + c := by
    have hle : g ≤ᶠ[F] fun a ↦ h a + c := hgh.mono fun a ha ↦ by
      have := (abs_le.1 ha).2; linarith
    calc limsup g F ≤ limsup (fun a ↦ h a + c) F := limsup_le_limsup hle hgc hbc
      _ = limsup h F + c := limsup_add_const F h c hhb hhc
  have h2 : liminf h F ≤ liminf g F + c := by
    have hle : h ≤ᶠ[F] fun a ↦ g a + c := hgh.mono fun a ha ↦ by
      have := (abs_le.1 ha).1; linarith
    calc liminf h F ≤ liminf (fun a ↦ g a + c) F := liminf_le_liminf hle hhb' hbc'
      _ = liminf g F + c := liminf_add_const F g c hgc' hgb'
  linarith

/-- If `g` oscillates along `F` by more than `2c` and `h` is eventually within `c` of `g`, then
`h` oscillates too. -/
theorem liminf_lt_limsup_of_eventually_abs_sub_le
    (hg : ∀ a, |g a| ≤ M) (hh : ∀ a, |h a| ≤ M) (hgh : ∀ᶠ a in F, |g a - h a| ≤ c)
    (hosc : 2 * c < limsup g F - liminf g F) : liminf h F < limsup h F := by
  have := limsup_sub_liminf_le_of_eventually_abs_sub_le hg hh hgh
  linarith

end Filter

end

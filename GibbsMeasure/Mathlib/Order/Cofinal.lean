/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Data.Countable.Basic
public import Mathlib.Order.Directed

/-!
# Cofinal sequences in countable directed preorders

A nonempty countable preorder directed upwards contains a monotone cofinal sequence
(`exists_monotone_cofinal`), and an infimum over an antitone family may then be computed along any
cofinal sequence (`iInf_eq_iInf_comp_of_cofinal`). Both are used to reduce statements about a
directed index set — Georgii's finite volumes, say — to statements about `ℕ`.
-/

@[expose] public section

/-- A nonempty countable preorder directed upwards contains a monotone cofinal sequence. -/
lemma exists_monotone_cofinal (ι : Type*) [Preorder ι] [Countable ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] : ∃ f : ℕ → ι, Monotone f ∧ ∀ i, ∃ n, i ≤ f n := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  choose g hg₁ hg₂ using fun a b : ι ↦ directed_of (· ≤ ·) a b
  refine ⟨fun n ↦ Nat.rec (e 0) (fun k ih ↦ g ih (e (k + 1))) n,
    monotone_nat_of_le_succ fun n ↦ hg₁ _ _, fun i ↦ ?_⟩
  obtain ⟨n, rfl⟩ := he i
  cases n with
  | zero => exact ⟨0, le_rfl⟩
  | succ k => exact ⟨k + 1, hg₂ _ _⟩

/-- An infimum over an antitone family may be computed along any cofinal sequence. -/
lemma iInf_eq_iInf_comp_of_cofinal {α ι : Type*} [CompleteLattice α] [Preorder ι] {m : ι → α}
    (hm : Antitone m) {f : ℕ → ι} (hcof : ∀ i, ∃ n, i ≤ f n) :
    ⨅ i, m i = ⨅ n, m (f n) :=
  le_antisymm (le_iInf fun n ↦ iInf_le m (f n))
    (le_iInf fun i ↦ by obtain ⟨n, hn⟩ := hcof i; exact (iInf_le _ n).trans (hm hn))

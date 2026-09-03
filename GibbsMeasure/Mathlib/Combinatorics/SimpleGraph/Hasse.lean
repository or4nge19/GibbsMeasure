/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Int.SuccPred

/-!
# The Hasse graph of `ℤ`

`SimpleGraph.hasse ℤ` is the nearest-neighbour graph of `ℤ`: `i` and `j` are adjacent iff
`|i - j| = 1`. It is locally finite, with `∂i = {i - 1, i + 1}`.
-/

@[expose] public section

namespace SimpleGraph

lemma hasse_int_adj (i j : ℤ) : (hasse ℤ).Adj i j ↔ i + 1 = j ∨ j + 1 = i := by
  rw [hasse_adj, Order.covBy_iff_add_one_eq, Order.covBy_iff_add_one_eq]

lemma neighborSet_hasse_int (i : ℤ) : (hasse ℤ).neighborSet i = ({i - 1, i + 1} : Set ℤ) := by
  ext j
  simp only [mem_neighborSet, hasse_int_adj, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- `ℤ` is a locally finite graph. -/
noncomputable instance instLocallyFiniteHasseInt : (hasse ℤ).LocallyFinite := fun i ↦
  (show ((hasse ℤ).neighborSet i).Finite by
    rw [neighborSet_hasse_int]
    exact Set.toFinite _).fintype

lemma neighborFinset_hasse_int (i : ℤ) : (hasse ℤ).neighborFinset i = {i - 1, i + 1} := by
  ext j
  simp only [mem_neighborFinset, hasse_int_adj, Finset.mem_insert, Finset.mem_singleton]
  omega

/-- `j ↦ s(j, j + 1)` is injective on `ℤ`: an edge of `hasse ℤ` determines its left endpoint. -/
lemma injective_mk_succ_int : Function.Injective fun j : ℤ ↦ s(j, j + 1) := by
  intro j k h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · omega

/-- The edges of `hasse ℤ` meeting `Λ` are the bonds `{j, j + 1}` with `j ∈ Λ` or `j + 1 ∈ Λ`. -/
lemma mem_bondsOf_hasse_int {Λ : Finset ℤ} {e : Sym2 ℤ} :
    e ∈ (hasse ℤ).bondsOf Λ ↔ ∃ j : ℤ, (j ∈ Λ ∨ j + 1 ∈ Λ) ∧ e = s(j, j + 1) := by
  constructor
  · induction e using Sym2.ind with
    | _ a b =>
      rw [mk_mem_bondsOf]
      rintro ⟨hadj, hab⟩
      rcases (hasse_int_adj a b).1 hadj with h | h
      · exact ⟨a, by rwa [h], by rw [h]⟩
      · exact ⟨b, by rw [h]; exact hab.symm, by rw [h, Sym2.eq_swap]⟩
  · rintro ⟨j, hj, rfl⟩
    exact mk_mem_bondsOf.2 ⟨(hasse_int_adj j (j + 1)).2 (Or.inl rfl), hj⟩

end SimpleGraph

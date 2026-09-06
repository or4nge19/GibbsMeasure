/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.InfiniteCluster
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.SelfAvoidingPath

/-!
# Monotonicity of the ocean part, and long paths in infinite clusters

Two complements to `GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.InfiniteCluster`, whose
natural home is that file.

* `SimpleGraph.oceanPart_mono`: enlarging `W` enlarges its ocean part `oceanPart G H R W`, under
  the standing hypothesis of `SimpleGraph.oceanPart_nonempty_iff` that `R` minus any finite set
  percolates in `H`.
* `SimpleGraph.exists_isPath_length_eq_of_mem_infiniteClusters`: in a locally finite graph, a
  vertex of an infinite cluster of `s` is the starting point of a path of every length in `s`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {R W W' s : Set V}

/-- **The ocean part is monotone in the set of vertices**: if `W ⊆ W' ⊆ R`, every ocean of `W`
in `R` is an ocean of `W'` in `R`, hence lies in the maximal one. -/
theorem oceanPart_mono (hGH : G ≤ H)
    (hR : ∀ F : Set V, F.Finite → (H.infiniteClusters (R \ F)).Nonempty)
    (hWW' : W ⊆ W') (hW'R : W' ⊆ R) : oceanPart G H R W ⊆ oceanPart G H R W' := by
  rcases (oceanPart G H R W).eq_empty_or_nonempty with h | h
  · rw [h]
    exact Set.empty_subset _
  · exact (isOceanIn_oceanPart_of_nonempty h).subset_oceanPart hGH hR
      ((oceanPart_subset.trans infiniteClusters_subset).trans hWW') hW'R

/-- In a locally finite graph, a vertex of an infinite cluster of `s` starts a path of every
length with support in `s`. -/
theorem exists_isPath_length_eq_of_mem_infiniteClusters [G.LocallyFinite] {a : V}
    (ha : a ∈ G.infiniteClusters s) (n : ℕ) :
    ∃ (x : V) (p : G.Walk a x), p.IsPath ∧ p.length = n ∧ ∀ v ∈ p.support, v ∈ s := by
  obtain ⟨has, h⟩ := ha
  exact exists_isPath_length_eq_of_infinite_supp has h n

end SimpleGraph

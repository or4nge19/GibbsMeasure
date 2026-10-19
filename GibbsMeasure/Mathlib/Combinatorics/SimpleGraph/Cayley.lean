/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Order.Units

/-!
# Cayley graphs: connectivity and bipartiteness

For a group `M` and generators `s`, Mathlib's Cayley graph `SimpleGraph.mulCayley s` joins `u` and
`u * g`, `g ∈ s`. Left multiplications are graph automorphisms (`mulCayleyMulLeft`), so

* `mulCayley_connected`: the Cayley graph is connected when `s` generates `M`;
* `mulCayley_isBipartite`: it is bipartite when a character `χ : M →* ℤˣ` is `-1` on `s`, with
  parts `χ = 1` and `χ = -1`.
-/

@[expose] public section

namespace SimpleGraph

variable {M : Type*} [Group M] (s : Set M)

/-- Left multiplication by `d` is an endomorphism of the Cayley graph. -/
def mulCayleyMulLeft (d : M) : mulCayley s →g mulCayley s where
  toFun u := d * u
  map_rel' h := mulCayley_adj_mul_iff_right.2 h

theorem mulCayleyMulLeft_apply (d u : M) : mulCayleyMulLeft s d u = d * u :=
  rfl

variable {s}

theorem mulCayley_reachable_one_of_mem_closure {g : M} (hg : g ∈ Subgroup.closure s) :
    (mulCayley s).Reachable 1 g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    by_cases h : g = 1
    · rw [h]
    · exact Adj.reachable ((mulCayley_adj s 1 g).2 ⟨Ne.symm h, .inl (by simpa using hg)⟩)
  | one => rfl
  | mul x y _ _ hx hy =>
    refine hx.trans ?_
    have := hy.map (mulCayleyMulLeft s x)
    simpa [mulCayleyMulLeft_apply] using this
  | inv x _ hx =>
    have := hx.map (mulCayleyMulLeft s x⁻¹)
    simp only [mulCayleyMulLeft_apply, mul_one, inv_mul_cancel] at this
    exact this.symm

/-- **A Cayley graph is connected when its generators generate the group.** -/
theorem mulCayley_connected (h : Subgroup.closure s = ⊤) : (mulCayley s).Connected :=
  have hr : ∀ g, (mulCayley s).Reachable 1 g := fun g ↦
    mulCayley_reachable_one_of_mem_closure (h ▸ Subgroup.mem_top g)
  ⟨fun u v ↦ (hr u).symm.trans (hr v)⟩

/-- **A Cayley graph is bipartite when a character `χ : M →* ℤˣ` is `-1` on the generators**:
adjacent vertices have opposite values of `χ`. -/
theorem mulCayley_isBipartite {χ : M →* ℤˣ} (hχ : ∀ g ∈ s, χ g = -1) :
    (mulCayley s).IsBipartite := by
  have hne : ∀ u : ℤˣ, u * -1 ≠ u := fun u h ↦ by
    have := congrArg (u⁻¹ * ·) h
    simp at this
  refine (Coloring.mk χ fun {u v} huv ↦ ?_).colorable
  rcases ((mulCayley_adj s u v).1 huv).2 with h | h
  · have := hχ _ h
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul] at this
    rw [this]
    exact (hne _).symm
  · have := hχ _ h
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul] at this
    rw [this]
    exact hne _

end SimpleGraph

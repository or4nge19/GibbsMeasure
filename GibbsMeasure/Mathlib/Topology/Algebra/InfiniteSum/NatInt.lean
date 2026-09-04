/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Partial products over `Finset.Ico n N` of a tail product

`HasProd.tendsto_prod_Ico_nat` and `Multipliable.tendsto_prod_Ico_nat` (with their additive
versions): if the tail `fun i ↦ f (i + n)` has product `m`, the partial products
`∏ i ∈ Ico n N, f i` converge to `m` as `N → ∞`. These are the `Ico` forms of
`HasProd.tendsto_prod_nat` and `Multipliable.tendsto_prod_nat`.
-/

@[expose] public section

open Filter Finset Topology

variable {M : Type*} [CommMonoid M] [TopologicalSpace M]

/-- If the tail `fun i ↦ f (i + n)` has product `m`, then the partial products
`∏ i ∈ Ico n N, f i` converge to `m` as `N → ∞`. -/
@[to_additive /-- If the tail `fun i ↦ f (i + n)` has sum `m`, then the partial sums
`∑ i ∈ Ico n N, f i` converge to `m` as `N → ∞`. -/]
theorem HasProd.tendsto_prod_Ico_nat {f : ℕ → M} {m : M} {n : ℕ}
    (h : HasProd (fun i ↦ f (i + n)) m) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, f i) atTop (𝓝 m) := by
  refine (h.tendsto_prod_nat.comp (tendsto_sub_atTop_nat n)).congr fun N ↦ ?_
  simp only [Function.comp_def, prod_Ico_eq_prod_range]
  exact prod_congr rfl fun k _ ↦ by rw [add_comm]

/-- If the tail `fun i ↦ f (i + n)` is multipliable, then the partial products
`∏ i ∈ Ico n N, f i` converge to the tail product `∏' i, f (i + n)` as `N → ∞`. -/
@[to_additive /-- If the tail `fun i ↦ f (i + n)` is summable, then the partial sums
`∑ i ∈ Ico n N, f i` converge to the tail sum `∑' i, f (i + n)` as `N → ∞`. -/]
theorem Multipliable.tendsto_prod_Ico_nat {f : ℕ → M} {n : ℕ}
    (h : Multipliable fun i ↦ f (i + n)) :
    Tendsto (fun N ↦ ∏ i ∈ Ico n N, f i) atTop (𝓝 (∏' i, f (i + n))) :=
  h.hasProd.tendsto_prod_Ico_nat

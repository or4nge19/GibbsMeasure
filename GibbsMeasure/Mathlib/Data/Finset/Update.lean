/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Set.Restrict
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Update a function on an arbitrary set of coordinates

`Mathlib.Data.Finset.Update` defines `Function.updateFinset x s y`, the vector `x` with the
coordinates in a *finite* set `s` replaced by `y`. This file provides the version
`Function.updateSet x s y` for an arbitrary `s : Set ι`, together with the `Set` analogues of the
`updateFinset` API and `Function.updateSet_coe`, which identifies the two operations at a coerced
`Finset`.

Since membership in an arbitrary set is not decidable, `updateSet` is classical, hence
noncomputable; this is the only difference from `updateFinset`, which takes `[DecidableEq ι]`.

## Main definitions

* `Function.updateSet x s y`: the vector `x` with the coordinates in `s` changed to the values
  of `y`.

## Main statements

* `Function.updateSet_coe`: `updateSet x ↑s y = updateFinset x s y` for `s : Finset ι`.
* `Function.measurable_updateSet`, `Function.measurable_updateSet_left`: measurability in each
  argument separately (Mathlib's home for the `Finset` versions is
  `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`).
-/

@[expose] public section

namespace Function

variable {ι : Type*} {π : ι → Type*} {x : ∀ i, π i} {s t : Set ι} {i : ι}

open Classical in
/-- `updateSet x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.
This is `Function.updateFinset` for an arbitrary, possibly infinite, set of coordinates. -/
noncomputable def updateSet (x : ∀ i, π i) (s : Set ι) (y : ∀ i : s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Classical in
theorem updateSet_def (y : ∀ i : s, π i) :
    updateSet x s y = fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else x i := rfl

@[simp]
theorem updateSet_apply_of_mem (hi : i ∈ s) (y : ∀ i : s, π i) :
    updateSet x s y i = y ⟨i, hi⟩ := by
  simp [updateSet, hi]

@[simp]
theorem updateSet_apply_of_notMem (hi : i ∉ s) (y : ∀ i : s, π i) : updateSet x s y i = x i := by
  simp [updateSet, hi]

@[simp]
theorem updateSet_empty (y : ∀ i : (∅ : Set ι), π i) : updateSet x ∅ y = x := by
  funext i; exact updateSet_apply_of_notMem (Set.notMem_empty i) y

theorem updateSet_univ (y : ∀ i : (Set.univ : Set ι), π i) :
    updateSet x Set.univ y = fun i ↦ y ⟨i, Set.mem_univ i⟩ := by
  funext i; exact updateSet_apply_of_mem (Set.mem_univ i) y

theorem updateSet_univ_apply (y : ∀ i : (Set.univ : Set ι), π i) :
    updateSet x Set.univ y i = y ⟨i, Set.mem_univ i⟩ :=
  updateSet_apply_of_mem (Set.mem_univ i) y

theorem updateSet_congr (h : s = t) (y : ∀ i : s, π i) :
    updateSet x s y = updateSet x t fun i ↦ y ⟨i, h ▸ i.2⟩ := by subst h; rfl

/-- `updateSet` at a coerced `Finset` is `Function.updateFinset`. -/
theorem updateSet_coe [DecidableEq ι] (x : ∀ i, π i) (s : Finset ι)
    (y : ∀ i : (s : Set ι), π i) :
    updateSet x (s : Set ι) y = updateFinset x s fun i ↦ y ⟨i, by simp⟩ := by
  funext i
  by_cases hi : i ∈ s
  · rw [updateSet_apply_of_mem (by simpa using hi)]
    simp [updateFinset, hi]
  · rw [updateSet_apply_of_notMem (by simpa using hi)]
    simp [updateFinset, hi]

/-! ### Iterated updates -/

/-- Updating on `t` overwrites a previous update on a smaller set `s`. -/
theorem updateSet_updateSet_of_subset (hst : s ⊆ t) (x : ∀ i, π i) (y : ∀ i : s, π i)
    (z : ∀ i : t, π i) : updateSet (updateSet x s y) t z = updateSet x t z := by
  funext i
  by_cases hi : i ∈ t
  · simp [hi]
  · rw [updateSet_apply_of_notMem hi, updateSet_apply_of_notMem hi,
      updateSet_apply_of_notMem fun h ↦ hi (hst h)]

@[simp]
theorem updateSet_updateSet (x : ∀ i, π i) (y z : ∀ i : s, π i) :
    updateSet (updateSet x s y) s z = updateSet x s z :=
  updateSet_updateSet_of_subset Set.Subset.rfl x y z

/-- Updating outside `s` at a single site commutes with `updateSet`. -/
theorem updateSet_update_of_notMem [DecidableEq ι] (hi : i ∉ s) (x : ∀ i, π i) (v : π i)
    (y : ∀ i : s, π i) :
    updateSet (Function.update x i v) s y = Function.update (updateSet x s y) i v := by
  funext j
  by_cases hj : j ∈ s
  · have hji : j ≠ i := fun h ↦ hi (h ▸ hj)
    rw [updateSet_apply_of_mem hj, Function.update_of_ne hji, updateSet_apply_of_mem hj]
  · by_cases hji : j = i
    · subst hji
      rw [updateSet_apply_of_notMem hj, Function.update_self, Function.update_self]
    · rw [updateSet_apply_of_notMem hj, Function.update_of_ne hji, Function.update_of_ne hji,
        updateSet_apply_of_notMem hj]

/-! ### Interaction with restriction -/

theorem domRestrict_updateSet_of_subset (hst : s ⊆ t) (x : ∀ i, π i) (y : ∀ i : t, π i) :
    Set.domRestrict s (updateSet x t y) = Set.domRestrict₂ hst y := by
  funext i
  exact updateSet_apply_of_mem (hst i.2) y

@[simp]
theorem domRestrict_updateSet (x : ∀ i, π i) (y : ∀ i : s, π i) :
    Set.domRestrict s (updateSet x s y) = y := by
  funext i
  exact updateSet_apply_of_mem i.2 y

@[simp]
theorem updateSet_domRestrict (x : ∀ i, π i) (s : Set ι) :
    updateSet x s (Set.domRestrict s x) = x := by
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

/-! ### Dependence -/

/-- If one replaces the variables indexed by a set `t`, then `f` no longer depends on those
variables. -/
theorem _root_.DependsOn.updateSet {α : Type*} {f : (∀ i, π i) → α} {s : Set ι}
    (hf : DependsOn f s) {t : Set ι} (y : ∀ i : t, π i) :
    DependsOn (fun x ↦ f (updateSet x t y)) (s \ t) := by
  refine fun x₁ x₂ h ↦ hf fun i hi ↦ ?_
  by_cases hit : i ∈ t
  · simp [hit]
  · simp [hit, h i ⟨hi, hit⟩]

/-! ### Order -/

theorem updateSet_le_updateSet [∀ i, Preorder (π i)] {x x' : ∀ i, π i} (hx : x ≤ x')
    (y : ∀ i : s, π i) : updateSet x s y ≤ updateSet x' s y := by
  intro i
  by_cases hi : i ∈ s
  · simp [hi]
  · simpa [hi] using hx i

theorem monotone_updateSet [∀ i, Preorder (π i)] (x : ∀ i, π i) (s : Set ι) :
    Monotone (updateSet x s) := by
  intro y z hyz i
  by_cases hi : i ∈ s
  · simpa [hi] using hyz ⟨i, hi⟩
  · simp [hi]

/-! ### Measurability

Mathlib's home for the `Finset` versions of these is
`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`. -/

section Measurable

variable {δ : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)] {u : Set δ}

@[fun_prop]
theorem measurable_updateSet' :
    Measurable fun p : (∀ i, X i) × (∀ i : u, X i) ↦ updateSet p.1 u p.2 := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ u
  · simpa only [updateSet_apply_of_mem hi] using measurable_snd.eval
  · simpa only [updateSet_apply_of_notMem hi] using measurable_fst.eval

@[fun_prop]
theorem measurable_updateSet {x : ∀ i, X i} : Measurable (updateSet x u) :=
  measurable_updateSet'.comp measurable_prodMk_left

@[fun_prop]
theorem measurable_updateSet_left {y : ∀ i : u, X i} : Measurable (updateSet · u y) :=
  measurable_updateSet'.comp measurable_prodMk_right

end Measurable

end Function

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Summability of a product over a finite index set

If `f : α → ℝ` is nonnegative and summable then `x ↦ ∏ i, f (x i)` is summable on `ι → α` for
every finite `ι`; this is the summability companion of
`MeasureTheory.integral_fintype_prod_eq_prod`.

## Main results

* `summable_pi_prod`
-/

@[expose] public section

/-- A product of summable nonnegative functions of the coordinates is summable on `Fin m → α`. -/
theorem summable_fin_prod {α : Type*} {f : α → ℝ} (hf : Summable f) (hf0 : ∀ x, 0 ≤ f x)
    (m : ℕ) : Summable fun x : Fin m → α ↦ ∏ i, f (x i) := by
  have h1 : (0 : α → ℝ) ≤ f := fun x ↦ hf0 x
  induction m with
  | zero =>
      have : Finite (Fin 0 → α) := by
        have : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty _
        exact Finite.of_subsingleton
      exact Summable.of_finite
  | succ m ih =>
      have h2 : (0 : (Fin m → α) → ℝ) ≤ fun y : Fin m → α ↦ ∏ i, f (y i) :=
        fun y ↦ Finset.prod_nonneg fun i _ ↦ hf0 (y i)
      -- The implicit arguments are supplied to avoid an expensive higher-order unification.
      have hprod := Summable.mul_of_nonneg (ι := α) (ι' := Fin m → α) (f := f)
        (g := fun y : Fin m → α ↦ ∏ i, f (y i)) hf ih h1 h2
      have hiff := Equiv.summable_iff (f := fun x : Fin (m + 1) → α ↦ ∏ i, f (x i))
        (Fin.consEquiv fun _ : Fin (m + 1) ↦ α)
      have hcomp : ((fun x : Fin (m + 1) → α ↦ ∏ i, f (x i))
          ∘ (Fin.consEquiv fun _ : Fin (m + 1) ↦ α))
          = fun p : α × (Fin m → α) ↦ f p.1 * ∏ i, f (p.2 i) := by
        funext p
        simp [Fin.prod_univ_succ]
      rw [hcomp] at hiff
      exact hiff.1 hprod

/-- A product of summable nonnegative functions of the coordinates is summable on `ι → α` for
every finite index type `ι`. -/
theorem summable_pi_prod {ι : Type*} [Fintype ι] {α : Type*} {f : α → ℝ} (hf : Summable f)
    (hf0 : ∀ x, 0 ≤ f x) : Summable fun x : ι → α ↦ ∏ i, f (x i) := by
  classical
  have hiff := Equiv.summable_iff (f := fun x : ι → α ↦ ∏ i, f (x i))
    (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl α))
  have hcomp : ((fun x : ι → α ↦ ∏ i, f (x i))
      ∘ (Equiv.arrowCongr (Fintype.equivFin ι).symm (Equiv.refl α)))
      = fun y : Fin (Fintype.card ι) → α ↦ ∏ j, f (y j) := by
    funext y
    simp only [Function.comp_apply, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
      Function.comp_def, id_eq]
    exact Equiv.prod_comp (Fintype.equivFin ι) fun j ↦ f (y j)
  rw [hcomp] at hiff
  exact hiff.1 (summable_fin_prod hf hf0 _)

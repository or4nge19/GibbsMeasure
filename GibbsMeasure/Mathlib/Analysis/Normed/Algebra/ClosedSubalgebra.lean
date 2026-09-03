/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.BoundedMeasurable
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Functional calculus on a closed subalgebra of a Banach algebra

A closed subalgebra of `lp (fun _ ↦ ℝ) ∞` is closed, by Weierstrass approximation, under
composition with any function continuous on a compact interval containing the range
(`Subalgebra.comp_mem_lp`); in particular it contains the pointwise inverse of any of its elements
that is bounded below by a positive constant (`Subalgebra.inv_mem_lp`).
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace lp

variable {α : Type*}

/-- Evaluation at a point, as an `ℝ`-algebra homomorphism on `lp (fun _ ↦ ℝ) ∞`. -/
def evalAlgHom (x : α) : lp (fun _ : α ↦ ℝ) ∞ →ₐ[ℝ] ℝ where
  toFun f := f x
  map_one' := by rw [lp.infty_coeFn_one]; rfl
  map_mul' f g := by rw [lp.infty_coeFn_mul]; rfl
  map_zero' := by rw [lp.coeFn_zero]; rfl
  map_add' f g := by rw [lp.coeFn_add]; rfl
  commutes' r := by
    change ((algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ) x = r
    rw [Algebra.algebraMap_eq_smul_one, lp.coeFn_smul]
    simp [lp.infty_coeFn_one]

@[simp] lemma evalAlgHom_apply (x : α) (f : lp (fun _ : α ↦ ℝ) ∞) : evalAlgHom x f = f x := rfl

lemma coeFn_aeval (p : Polynomial ℝ) (f : lp (fun _ : α ↦ ℝ) ∞) (x : α) :
    (Polynomial.aeval f p : lp (fun _ : α ↦ ℝ) ∞) x = Polynomial.eval (f x) p := by
  have h := Polynomial.aeval_algHom_apply (evalAlgHom (α := α) x) f p
  rw [evalAlgHom_apply] at h
  rw [show ((Polynomial.aeval f p : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ) x
      = evalAlgHom (α := α) x (Polynomial.aeval f p) from rfl, ← h,
    ← Polynomial.coe_aeval_eq_eval]

end lp

namespace Subalgebra

open scoped Polynomial

variable {α : Type*}

/-- **A closed subalgebra of `lp (fun _ ↦ ℝ) ∞` is closed under composition with any function
continuous on a compact interval containing the range.** Weierstrass approximation. -/
theorem comp_mem_lp {A : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞)}
    (hA : IsClosed (A : Set (lp (fun _ : α ↦ ℝ) ∞)))
    {f g : lp (fun _ : α ↦ ℝ) ∞} (hf : f ∈ A) {a b : ℝ}
    (hrange : ∀ x, (⇑f) x ∈ Set.Icc a b) {F : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc a b))
    (hg : ∀ x, (⇑g) x = F ((⇑f) x)) : g ∈ A := by
  rw [← SetLike.mem_coe, ← hA.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b F hF (ε / 2) (by positivity)
  have haeval : Polynomial.aeval f p ∈ A := by
    rw [Polynomial.aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun n _ ↦ Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hf n) _
  refine ⟨Polynomial.aeval f p, haeval, ?_⟩
  have hbound : ∀ x, ‖(⇑g) x - (⇑(Polynomial.aeval f p)) x‖ ≤ ε / 2 := by
    intro x
    rw [hg x, lp.coeFn_aeval, Real.norm_eq_abs, abs_sub_comm]
    exact le_of_lt (hp _ (hrange x))
  have : dist g (Polynomial.aeval f p) ≤ ε / 2 := by
    rw [dist_eq_norm]
    refine lp.norm_le_of_forall_le (by positivity) fun x ↦ ?_
    rw [lp.coeFn_sub, Pi.sub_apply]
    exact hbound x
  linarith [this]

/-- A closed subalgebra of `lp (fun _ ↦ ℝ) ∞` containing `f` bounded below by `m > 0` contains
the pointwise inverse of `f`. -/
theorem inv_mem_lp {A : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞)}
    (hA : IsClosed (A : Set (lp (fun _ : α ↦ ℝ) ∞)))
    {f g : lp (fun _ : α ↦ ℝ) ∞} (hf : f ∈ A) {m : ℝ} (hm : 0 < m)
    (hmf : ∀ x, m ≤ (⇑f) x) (hg : ∀ x, (⇑g) x = ((⇑f) x)⁻¹) : g ∈ A := by
  refine Subalgebra.comp_mem_lp hA hf (a := m) (b := ‖f‖)
    (fun x ↦ ⟨hmf x, le_trans (le_abs_self _) (lp.norm_apply_le_norm ENNReal.top_ne_zero f x)⟩)
    (F := (·⁻¹)) ?_ hg
  exact ContinuousOn.inv₀ continuousOn_id fun x hx ↦ ne_of_gt (lt_of_lt_of_le hm hx.1)

end Subalgebra

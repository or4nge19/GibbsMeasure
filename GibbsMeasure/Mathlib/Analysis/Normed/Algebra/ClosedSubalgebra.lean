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

A closed subalgebra is closed under any limit of polynomials in its elements: under the
exponential, under the inverse of an element `x` with `‖1 - c⁻¹ • x‖ < 1`, and — for
`lp (fun _ ↦ ℝ) ∞`, by Weierstrass approximation — under composition with any function continuous
on a compact interval containing the range (`Subalgebra.comp_mem_lp`).
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

/-- A closed subalgebra of a Banach algebra is closed under the exponential. -/
theorem Subalgebra.exp_mem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    {A : Subalgebra ℝ 𝔸} (hA : IsClosed (A : Set 𝔸)) {x : 𝔸} (hx : x ∈ A) :
    NormedSpace.exp x ∈ A := by
  refine hA.mem_of_tendsto (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x) (.of_forall fun s ↦ ?_)
  exact Subalgebra.sum_mem _ fun n _ ↦ Subalgebra.smul_mem _ (Subalgebra.pow_mem _ hx n) _

/-- The exponential on `lp (fun _ ↦ ℝ) ∞` is pointwise. -/
theorem lp.infty_coeFn_exp {α : Type*} (f : lp (fun _ : α ↦ ℝ) ∞) :
    ⇑(NormedSpace.exp f) = fun x ↦ Real.exp (f x) := by
  funext x
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) f
  have h1 : HasSum (fun n : ℕ ↦ ((n.factorial : ℝ))⁻¹ * (f x) ^ n)
      ((⇑(NormedSpace.exp f) : α → ℝ) x) := by
    refine (lp.tendsto_apply_of_tendsto h x).congr fun s ↦ ?_
    rw [lp.coeFn_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [lp.coeFn_smul, lp.infty_coeFn_pow]; rfl
  have h2 : HasSum (fun n : ℕ ↦ ((n.factorial : ℝ))⁻¹ * (f x) ^ n) (Real.exp (f x)) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [smul_eq_mul] using NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (f x : ℝ)
  exact h1.unique h2

/-- A closed subalgebra of a Banach algebra contains `Ring.inverse (1 - t)` whenever it contains `t`
and `‖t‖ < 1`. -/
theorem Subalgebra.inverse_one_sub_mem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [NormOneClass 𝔸] {A : Subalgebra ℝ 𝔸} (hA : IsClosed (A : Set 𝔸))
    {t : 𝔸} (ht : t ∈ A) (h : ‖t‖ < 1) : Ring.inverse (1 - t) ∈ A :=
  hA.mem_of_tendsto (hasSum_geom_series_inverse t h)
    (.of_forall fun _ ↦ Subalgebra.sum_mem _ fun n _ ↦ Subalgebra.pow_mem _ ht n)

/-- A closed subalgebra of a Banach algebra contains the inverse of any of its units `x` for which
some scalar multiple `c⁻¹ • x` is within distance `1` of `1`. -/
theorem Subalgebra.inverse_mem {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [NormOneClass 𝔸] {A : Subalgebra ℝ 𝔸} (hA : IsClosed (A : Set 𝔸))
    {x y : 𝔸} (hx : x ∈ A) {c : ℝ} (hc : c ≠ 0) (h : ‖1 - c⁻¹ • x‖ < 1)
    (hxy : x * y = 1) (hyx : y * x = 1) : y ∈ A := by
  have hunit : (c⁻¹ • x) * (c • y) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, hxy]
  have hunit' : (c • y) * (c⁻¹ • x) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, hyx]
  have hIsUnit : IsUnit (c⁻¹ • x) := ⟨⟨c⁻¹ • x, c • y, hunit, hunit'⟩, rfl⟩
  have hinv : Ring.inverse (c⁻¹ • x) = c • y :=
    calc Ring.inverse (c⁻¹ • x)
        = Ring.inverse (c⁻¹ • x) * ((c⁻¹ • x) * (c • y)) := by rw [hunit, mul_one]
      _ = Ring.inverse (c⁻¹ • x) * (c⁻¹ • x) * (c • y) := (mul_assoc _ _ _).symm
      _ = c • y := by rw [Ring.inverse_mul_cancel _ hIsUnit, one_mul]
  have hmem : Ring.inverse (c⁻¹ • x) ∈ A := by
    have := Subalgebra.inverse_one_sub_mem hA
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) (Subalgebra.smul_mem _ hx c⁻¹)) h
    simpa using this
  have : c • y ∈ A := hinv ▸ hmem
  simpa [smul_smul, inv_mul_cancel₀ hc] using Subalgebra.smul_mem _ this c⁻¹

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
    show ((algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ) x = r
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
    (fun x ↦ ⟨hmf x, le_trans (le_abs_self _) (lp.norm_apply_le_norm_top f x)⟩)
    (F := (·⁻¹)) ?_ hg
  exact ContinuousOn.inv₀ continuousOn_id fun x hx ↦ ne_of_gt (lt_of_lt_of_le hm hx.1)

end Subalgebra

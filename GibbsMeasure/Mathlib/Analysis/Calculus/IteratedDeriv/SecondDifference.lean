/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The second symmetric difference of a `C²` function

`f (x + s) + f (x - s) - 2 f x ≤ M s²` when `f'' ≤ M`.
-/

@[expose] public section

open Set

/-- **Second symmetric difference of a `C²` function.** If `f'' ≤ M` everywhere then
`f (x + h) + f (x - h) - 2 f x ≤ M h²`: the function `u ↦ M u² / 2 - f u` is convex.
Only the upper bound on `f''` is used. Intended home: `Mathlib/Analysis/Convex/Deriv.lean`. -/
theorem apply_add_apply_sub_le_of_iteratedDeriv_two_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ u, iteratedDeriv 2 f u ≤ M) (x h : ℝ) :
    f (x + h) + f (x - h) - 2 * f x ≤ M * h ^ 2 := by
  have h2 : iteratedDeriv 2 f = deriv (deriv f) := by rw [iteratedDeriv_eq_iterate]; rfl
  set g : ℝ → ℝ := fun u ↦ M / 2 * u ^ 2 - f u with hg
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two
  have hgd : ∀ u, HasDerivAt g (M * u - deriv f u) u := fun u ↦ by
    have h0 : HasDerivAt (fun u : ℝ ↦ M / 2 * u ^ 2) (M / 2 * (((2 : ℕ) : ℝ) * u ^ (2 - 1))) u :=
      (hasDerivAt_pow 2 u).const_mul (M / 2)
    have h0' : M / 2 * (((2 : ℕ) : ℝ) * u ^ (2 - 1)) = M * u := by norm_num; ring
    rw [h0'] at h0
    exact h0.sub (hf1 u).hasDerivAt
  have hg1 : Differentiable ℝ g := fun u ↦ (hgd u).differentiableAt
  have hderiv : deriv g = fun u ↦ M * u - deriv f u := funext fun u ↦ (hgd u).deriv
  have hgd2 : ∀ u, HasDerivAt (deriv g) (M - deriv (deriv f) u) u := fun u ↦ by
    rw [hderiv]
    have h1 := ((hasDerivAt_id' u).const_mul M).sub (hf2 u).hasDerivAt
    rwa [mul_one] at h1
  have hg2 : Differentiable ℝ (deriv g) := fun u ↦ (hgd2 u).differentiableAt
  have hconv : ConvexOn ℝ Set.univ g := by
    refine convexOn_univ_of_deriv2_nonneg hg1 hg2 fun u ↦ ?_
    change 0 ≤ deriv (deriv g) u
    rw [(hgd2 u).deriv]
    have := hM u
    rw [h2] at this
    linarith
  have := hconv.2 (Set.mem_univ (x + h)) (Set.mem_univ (x - h))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul, hg] at this
  have hx : 1 / 2 * (x + h) + 1 / 2 * (x - h) = x := by ring
  rw [hx] at this
  nlinarith [this]

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import GibbsMeasure.Mathlib.MeasureTheory.Order.StochasticDomination

/-!
# Holley's inequality and stochastic domination

Mathlib's `holley` compares two weight functions on a finite distributive lattice which
satisfy the lattice condition `f a * g b ≤ f (a ⊓ b) * g (a ⊔ b)`: monotone observables have larger
`g`-average than `f`-average.

Here it is put in the form in which correlation inequalities are used for Gibbs measures: an
*upper set* `A` of a target preorder `Ω`, pulled back along two monotone maps `F ≤ G`, is more
likely under `g ∘ G` than under `f ∘ F`. Taking `Ω = S → E` and `F`, `G` the two boundary
conditions of a finite-volume Gibbs distribution, this is the statement that the distribution is
stochastically increasing in the boundary condition.

## Main declarations

* `sum_indicator_le_of_holley`.
-/

@[expose] public section

open Finset Set

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Preorder Ω] {f g : (ι → Bool) → ℝ}
  {F G : (ι → Bool) → Ω}

/-- **Holley's inequality**, in the form used for monotonicity in the boundary condition: for
weights of equal mass satisfying the lattice condition, an upper set pulled back along a monotone
map is more likely under the larger weight and the larger map. -/
lemma sum_indicator_le_of_holley (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hsum : ∑ a, f a = ∑ a, g a) (hcond : ∀ a b, f a * g b ≤ f (a ⊓ b) * g (a ⊔ b))
    (hG : Monotone G) (hFG : ∀ a, F a ≤ G a) {A : Set Ω} (hA : IsUpperSet A) :
    ∑ a, f a * A.indicator (1 : Ω → ℝ) (F a) ≤ ∑ a, g a * A.indicator (1 : Ω → ℝ) (G a) := by
  set μ : (ι → Bool) → ℝ := fun a ↦ A.indicator (1 : Ω → ℝ) (G a) with hμdef
  have hμ₀ : 0 ≤ μ := fun a ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hμmono : Monotone μ := by
    intro a b hab
    by_cases ha : G a ∈ A
    · simp only [hμdef, Set.indicator_of_mem ha, Set.indicator_of_mem (hA (hG hab) ha),
        Pi.one_apply, le_refl]
    · simp only [hμdef, Set.indicator_of_notMem ha]
      exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hstep : ∀ a, f a * A.indicator (1 : Ω → ℝ) (F a) ≤ f a * μ a := by
    intro a
    refine mul_le_mul_of_nonneg_left ?_ (hf a)
    by_cases ha : F a ∈ A
    · rw [Set.indicator_of_mem ha, hμdef]
      simp only [Set.indicator_of_mem (hA (hFG a) ha), Pi.one_apply, le_refl]
    · rw [Set.indicator_of_notMem ha]
      exact hμ₀ a
  calc ∑ a, f a * A.indicator (1 : Ω → ℝ) (F a)
      ≤ ∑ a, μ a * f a := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        rw [mul_comm (μ a)]
        exact hstep a
    _ ≤ ∑ a, μ a * g a := holley (μ := μ) (f := f) (g := g) hμ₀ hf hg hμmono hsum hcond
    _ = ∑ a, g a * A.indicator (1 : Ω → ℝ) (G a) := by
        exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

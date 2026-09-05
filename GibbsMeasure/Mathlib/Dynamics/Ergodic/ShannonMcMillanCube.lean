/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Data.Countable.Basic
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MaximalInequality
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.ShannonMcMillanBreiman
public import GibbsMeasure.Mathlib.MeasureTheory.Group.Action.Synonym
public import Mathlib.Algebra.Order.Group.PiLex

/-!
# The Shannon–McMillan theorem on `ℤ^d`, along cubes

`MeasureTheory.tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate` is stated for
an arbitrary countable abelian group carrying a translation-invariant linear order. For `ℤ^d` that
order is the lexicographic one, which in Mathlib lives on the type synonym `Lex (ι → ℤ)`
(`Pi.Lex.linearOrder`, `Pi.Lex.isOrderedCancelAddMonoid`); the underlying type, the group
structure and the action are unchanged, so the block probabilities of the two spellings are the
same function. The three instances that `Lex` does not yet transport are in
`GibbsMeasure/Mathlib/Data/Countable/Basic.lean` (`Countable`) and
`GibbsMeasure/Mathlib/MeasureTheory/Group/Action/Synonym.lean` (`MeasurableConstVAdd`,
`VAddInvariantMeasure`). What is derived here is the statement Georgii uses: along an increasing
sequence of cubes `Λ_n = x_n + [0, r_n)^d` with `r_n → ∞`,
`∫ | -|Λ_n|⁻¹ log μ(X_{Λ_n} = X_{Λ_n} ω) - h | dμ(ω) → 0`
for an ergodic finite-state random field, where `h = entropyRate (Lex (ι → ℤ)) μ X` is the entropy
rate relative to the lexicographic past.
-/

@[expose] public section

open Filter Finset Set
open scoped ENNReal Pointwise symmDiff Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [AddAction (ι → ℤ) Ω]
  [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableConstVAdd (ι → ℤ) Ω]
  [VAddInvariantMeasure (ι → ℤ) Ω μ] [IsProbabilityMeasure μ] [MeasurableSpace E] [Finite E]
  [MeasurableSingletonClass E] (X : Ω → E)

/-- **The Shannon–McMillan theorem for a finite-state ergodic random field on `ℤ^d`, along
cubes** (the `L¹`, or McMillan, form). If `ℤ^d` acts ergodically on the probability space `(Ω, μ)`
by measure-preserving translations and `X : Ω → E` is measurable into a finite state space, then
along any sequence of cubes `Λ_n = x_n + [0, r_n)^d` whose side lengths tend to infinity,
`∫ | -|Λ_n|⁻¹ log μ(X_{Λ_n} = X_{Λ_n} ω) - h | dμ(ω) → 0`,
where `h = entropyRate (Lex (ι → ℤ)) μ X` is the mean conditional information of the spin at the
origin given the lexicographic past. This is the form of the theorem cited by Georgii, *Gibbs
Measures and Phase Transitions*, in the proof of the large deviation lower bound (15.47). -/
theorem tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate_cube
    (hX : Measurable X)
    (herg : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ)) Ω] A →
      μ A = 0 ∨ μ A = 1)
    (x : ℕ → ι → ℤ) {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun n ↦ ∫ ω, |(-(((x n +ᵥ Fintype.piFinset fun _ : ι ↦
          Finset.Ico (0 : ℤ) (r n)).card : ℝ)⁻¹ *
        Real.log (blockProb μ X (x n +ᵥ Fintype.piFinset fun _ : ι ↦
          Finset.Ico (0 : ℤ) (r n)) ω)))
      - entropyRate (Lex (ι → ℤ)) μ X| ∂μ) atTop (𝓝 0) := by
  refine tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate
    (G := Lex (ι → ℤ)) (F := fun n ↦ (x n +ᵥ Fintype.piFinset fun _ : ι ↦
      Finset.Ico (0 : ℤ) (r n) : Finset (ι → ℤ))) X hX herg ?_ fun g ↦ ?_
  · filter_upwards [hr.eventually_ge_atTop 1] with n hn
    refine ⟨x n +ᵥ (0 : ι → ℤ),
      Finset.mem_vadd_finset.2 ⟨0, Fintype.mem_piFinset.2 fun i ↦ ?_, rfl⟩⟩
    simp only [Finset.mem_Ico]
    refine ⟨le_rfl, ?_⟩
    change (0 : ℤ) < (r n : ℤ)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  · exact tendsto_card_vadd_cube_symmDiff_div_card x hr (ofLex g)

end MeasureTheory

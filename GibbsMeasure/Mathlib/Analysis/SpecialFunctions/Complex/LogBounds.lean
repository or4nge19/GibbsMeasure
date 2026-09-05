/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# `(1 + g a) ^ x a → exp t` for an arbitrary natural exponent

Mathlib's `Real.tendsto_one_add_pow_exp_of_tendsto` gives `(1 + g n) ^ n → exp t` when
`n * g n → t`, with the exponent equal to the index. Here the exponent is an arbitrary
natural-valued function `x` of the index, along an arbitrary filter; since `x` need not tend to
infinity, `g → 0` is assumed rather than derived. This is the form needed for the Poisson limit
theorem along an arbitrary sequence of trial numbers. Intended home:
`Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {α : Type*} {l : Filter α}

namespace Real

/-- The limit of `(1 + g a) ^ x a` is `exp t` when `x a * g a → t` and `g a → 0`. This is
`Real.tendsto_one_add_pow_exp_of_tendsto` with an arbitrary natural exponent `x a` in place of
the index `n`; since `x` need not tend to infinity, `g → 0` is assumed rather than derived. -/
lemma tendsto_one_add_pow_exp_of_tendsto_of_tendsto_zero {x : α → ℕ} {g : α → ℝ} {t : ℝ}
    (hx : Tendsto (fun a ↦ (x a : ℝ) * g a) l (𝓝 t)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun a ↦ (1 + g a) ^ x a) l (𝓝 (exp t)) := by
  have hsmall : ∀ᶠ a in l, g a ∈ Ioo (-1 / 2 : ℝ) (1 / 2) :=
    hg.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  -- `x a * log (1 + g a) → t`: the error `x a * (log (1 + g a) - g a)` is `O(|x a g a| |g a|)`.
  have hlog : Tendsto (fun a ↦ (x a : ℝ) * log (1 + g a)) l (𝓝 t) := by
    have herr : Tendsto (fun a ↦ (x a : ℝ) * (log (1 + g a) - g a)) l (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun a ↦ |(x a : ℝ) * g a| * (|g a| / (1 - |g a|))) ?_ ?_
      · filter_upwards [hsmall] with a ha
        have hg1 : |g a| < 1 := by rw [abs_lt]; constructor <;> linarith [ha.1, ha.2]
        have hbound := abs_log_sub_add_sum_range_le (x := -g a) (by rwa [abs_neg]) 1
        simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, sub_neg_eq_add,
          abs_neg] at hbound
        have hb : |log (1 + g a) - g a| ≤ |g a| ^ 2 / (1 - |g a|) := by
          rw [← neg_add_eq_sub]; simpa using hbound
        calc ‖(x a : ℝ) * (log (1 + g a) - g a)‖ = |(x a : ℝ)| * |log (1 + g a) - g a| := by
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ |(x a : ℝ)| * (|g a| ^ 2 / (1 - |g a|)) :=
              mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = |(x a : ℝ) * g a| * (|g a| / (1 - |g a|)) := by rw [abs_mul]; ring
      · have h1 : Tendsto (fun a ↦ 1 - |g a|) l (𝓝 (1 - |(0 : ℝ)|)) :=
          tendsto_const_nhds.sub hg.abs
        have h0 : Tendsto (fun a ↦ |g a| / (1 - |g a|)) l (𝓝 (|(0 : ℝ)| / (1 - |(0 : ℝ)|))) :=
          hg.abs.div h1 (by simp)
        simpa using hx.abs.mul h0
    have : (fun a ↦ (x a : ℝ) * log (1 + g a))
        = fun a ↦ (x a : ℝ) * g a + (x a : ℝ) * (log (1 + g a) - g a) := by
      ext a; ring
    rw [this]
    simpa using hx.add herr
  refine ((continuous_exp.tendsto t).comp hlog).congr' ?_
  filter_upwards [hsmall] with a ha
  have h1 : 0 < 1 + g a := by linarith [ha.1]
  simp only [Function.comp_apply]
  rw [← log_pow, exp_log (pow_pos h1 _)]

end Real

end

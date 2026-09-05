/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Natural powers in `ℝ≥0∞` reflect the order, and commute with infima

`x ↦ x ^ n` is a monotone bijection of `ℝ≥0∞` for `n ≠ 0`, with inverse `x ↦ x ^ (n⁻¹ : ℝ)`.
Mathlib has the two halves separately (`pow_le_pow_left'` and `ENNReal.rpow_inv_natCast_pow`)
but neither of the two consequences recorded here.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Taking `n`-th powers reflects the order on `ℝ≥0∞`. -/
lemma le_of_pow_le_pow_left' {a b : ℝ≥0∞} {n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h' : (a ^ (n : ℝ)) ^ ((n : ℝ)⁻¹) ≤ (b ^ (n : ℝ)) ^ ((n : ℝ)⁻¹) := by
    rw [ENNReal.rpow_natCast, ENNReal.rpow_natCast]
    exact ENNReal.rpow_le_rpow h (by positivity)
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hn0, ENNReal.rpow_one,
    ENNReal.rpow_one] at h'

/-- Taking `n`-th powers commutes with infima in `ℝ≥0∞`. -/
lemma iInf_pow {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0∞) {n : ℕ} (hn : n ≠ 0) :
    (⨅ i, f i) ^ n = ⨅ i, f i ^ n := by
  refine le_antisymm (le_iInf fun i ↦ pow_le_pow_left' (iInf_le f i) n) ?_
  have hL : ((⨅ i, f i ^ n) ^ ((n : ℝ)⁻¹)) ^ n = ⨅ i, f i ^ n :=
    ENNReal.rpow_inv_natCast_pow hn _
  have hle : (⨅ i, f i ^ n) ^ ((n : ℝ)⁻¹) ≤ ⨅ i, f i := by
    refine le_iInf fun i ↦ le_of_pow_le_pow_left' hn ?_
    rw [hL]
    exact iInf_le _ i
  calc (⨅ i, f i ^ n) = ((⨅ i, f i ^ n) ^ ((n : ℝ)⁻¹)) ^ n := hL.symm
    _ ≤ (⨅ i, f i) ^ n := pow_le_pow_left' hle n

end ENNReal

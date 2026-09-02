/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Divergence of `∑ 1 / ((k + 1) log (k + 1))`
-/

@[expose] public section

open Filter
open scoped Topology

/-- The series `∑_{k ≥ 1} 1 / ((k + 1) log (k + 1))` diverges (Cauchy condensation; the
condensed series is `∑ 1 / (k log 2)`). Intended home: `Mathlib/Analysis/PSeries.lean`. -/
theorem Real.not_summable_one_div_succ_mul_log_succ :
    ¬ Summable fun k : ℕ ↦ if k = 0 then (1 : ℝ) else 1 / ((k + 1) * Real.log (k + 1)) := by
  set f : ℕ → ℝ := fun k ↦ if k = 0 then (1 : ℝ) else 1 / ((k + 1) * Real.log (k + 1)) with hf
  have hf_nonneg : ∀ k, 0 ≤ f k := fun k ↦ by
    simp only [hf]
    split_ifs
    · exact zero_le_one
    · exact div_nonneg zero_le_one (mul_nonneg (by positivity)
        (Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])))
  have hf_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    simp only [hf, hm.ne', ite_false]
    have hn : n ≠ 0 := by omega
    simp only [hn, ite_false]
    have hm' : (1 : ℝ) < m + 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have hmn' : (m : ℝ) + 1 ≤ n + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hlogm : 0 < Real.log (m + 1) := Real.log_pos hm'
    have hlogn : Real.log (m + 1) ≤ Real.log (n + 1) := Real.log_le_log (by linarith) hmn'
    exact one_div_le_one_div_of_le (mul_pos (by linarith) hlogm)
      (mul_le_mul hmn' hlogn hlogm.le (by linarith))
  intro hsum
  have hcond := (summable_condensed_iff_of_nonneg hf_nonneg hf_mono).2 hsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- the condensed series dominates `1 / (2 (k + 1) log 2)`
  have hle : ∀ k : ℕ, 1 / (2 * Real.log 2) * (1 / ((k : ℝ) + 1)) ≤ (2 : ℝ) ^ k * f (2 ^ k) := by
    intro k
    have h2k : (2 : ℕ) ^ k ≠ 0 := by positivity
    simp only [hf, h2k, ite_false]
    have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    rw [hcast]
    have hpos : (0 : ℝ) < 2 ^ k := by positivity
    have hle2 : (2 : ℝ) ^ k + 1 ≤ 2 * 2 ^ k := by
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      linarith
    -- log (2^k + 1) ≤ log (2^(k+1)) = (k+1) log 2
    have hlog : Real.log ((2 : ℝ) ^ k + 1) ≤ (k + 1) * Real.log 2 := by
      calc Real.log ((2 : ℝ) ^ k + 1) ≤ Real.log ((2 : ℝ) ^ (k + 1)) :=
            Real.log_le_log (by positivity) (by rw [pow_succ]; linarith)
        _ = (k + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
    have hlogpos : 0 < Real.log ((2 : ℝ) ^ k + 1) := Real.log_pos (by linarith)
    rw [div_mul_div_comm, one_mul, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (1 : ℝ) * ((2 ^ k + 1) * Real.log (2 ^ k + 1))
        ≤ 1 * ((2 * 2 ^ k) * ((k + 1) * Real.log 2)) := by gcongr
      _ = 2 ^ k * (2 * Real.log 2 * (k + 1)) := by ring
  have hharm : Summable fun k : ℕ ↦ 1 / (2 * Real.log 2) * (1 / ((k : ℝ) + 1)) :=
    Summable.of_nonneg_of_le (fun k ↦ by positivity) hle hcond
  have : Summable fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) := by
    have h := hharm.mul_left (2 * Real.log 2)
    refine h.congr fun k ↦ ?_
    field_simp
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 ?_)
  refine this.congr fun k ↦ ?_
  push_cast
  ring

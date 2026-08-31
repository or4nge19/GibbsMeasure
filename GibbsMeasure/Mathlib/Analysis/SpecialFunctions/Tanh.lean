/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Increment and subadditivity bounds for `Real.tanh`

`|tanh b - tanh a| ≤ 2 * tanh (|b - a| / 2)`: the increment of `tanh` over an interval is
controlled by `tanh` of half the interval length. Since `tanh ≤ 1`, this refines the bound
`|tanh b - tanh a| ≤ 2` and, for small increments, the Lipschitz bound `|b - a|`.

The proof is the identity `tanh b - tanh a = sinh (b - a) / (cosh a * cosh b)` together with
`cosh ((b - a) / 2) ^ 2 ≤ cosh a * cosh b`, which follows from
`2 * cosh a * cosh b = cosh (a + b) + cosh (a - b) ≥ 1 + cosh (b - a)`.

`tanh` is also subadditive on `[0, ∞)`, and hence subadditive along finite sums of nonnegative
terms: `tanh (∑ f i) ≤ ∑ tanh (f i)`.

Finally `tanh (log (M / m) / 4) = (√M - √m) / (√M + √m)`, which identifies the sharp constant in
the comparison of two normalized measures with density ratio in `[m, M]`.
-/

@[expose] public section

namespace Real

/-- `2 * cosh a * cosh b = cosh (a + b) + cosh (a - b)`. -/
lemma two_mul_cosh_mul_cosh (a b : ℝ) : 2 * (cosh a * cosh b) = cosh (a + b) + cosh (a - b) := by
  rw [cosh_add, cosh_sub]; ring

/-- The half-angle bound behind the increment estimate for `tanh`. -/
lemma cosh_half_sq_le_cosh_mul_cosh (a b : ℝ) :
    cosh ((b - a) / 2) ^ 2 ≤ cosh a * cosh b := by
  have hhalf : cosh ((b - a) / 2) ^ 2 = (1 + cosh (b - a)) / 2 := by
    have hsq := cosh_sq ((b - a) / 2)
    have hdouble : cosh (b - a) = cosh ((b - a) / 2) ^ 2 + sinh ((b - a) / 2) ^ 2 := by
      have h2 := cosh_two_mul ((b - a) / 2)
      rwa [show 2 * ((b - a) / 2) = b - a by ring] at h2
    linarith
  have hsymm : cosh (b - a) = cosh (a - b) := by
    rw [show a - b = -(b - a) by ring, cosh_neg]
  rw [hhalf, hsymm, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have h := two_mul_cosh_mul_cosh a b
  have h1 : (1 : ℝ) ≤ cosh (a + b) := one_le_cosh _
  nlinarith

/-- `tanh b - tanh a = sinh (b - a) / (cosh a * cosh b)`. -/
lemma tanh_sub_tanh (a b : ℝ) : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := by
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_sub,
    div_sub_div _ _ (cosh_pos b).ne' (cosh_pos a).ne']
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **The increment of `tanh` is at most `2 * tanh` of half the increment**, for `a ≤ b`. -/
lemma tanh_sub_tanh_le_of_le {a b : ℝ} (hab : a ≤ b) :
    tanh b - tanh a ≤ 2 * tanh ((b - a) / 2) := by
  set d : ℝ := b - a with hd
  have hd0 : 0 ≤ d := by simp [hd]; linarith
  have hdouble : sinh d = 2 * sinh (d / 2) * cosh (d / 2) := by
    have h2 := sinh_two_mul (d / 2)
    rwa [show 2 * (d / 2) = d by ring] at h2
  have hsinh0 : 0 ≤ sinh (d / 2) := sinh_nonneg_iff.2 (by linarith)
  have hcosh : 0 < cosh (d / 2) := cosh_pos _
  have hprod : 0 < cosh a * cosh b := mul_pos (cosh_pos a) (cosh_pos b)
  have hsq := cosh_half_sq_le_cosh_mul_cosh a b
  rw [tanh_sub_tanh a b, ← hd, hdouble, tanh_eq_sinh_div_cosh]
  rw [div_le_iff₀ hprod]
  have hgoal : 2 * (sinh (d / 2) / cosh (d / 2)) * (cosh ((b - a) / 2) ^ 2)
      ≤ 2 * (sinh (d / 2) / cosh (d / 2)) * (cosh a * cosh b) := by
    have hc : 0 ≤ 2 * (sinh (d / 2) / cosh (d / 2)) := by positivity
    exact mul_le_mul_of_nonneg_left hsq hc
  have hleft : 2 * sinh (d / 2) * cosh (d / 2)
      = 2 * (sinh (d / 2) / cosh (d / 2)) * (cosh ((b - a) / 2) ^ 2) := by
    rw [← hd]
    field_simp
  rw [hleft]
  exact hgoal

/-- `tanh` is monotone. -/
lemma tanh_le_tanh_of_le {a b : ℝ} (hab : a ≤ b) : tanh a ≤ tanh b := by
  have h : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := tanh_sub_tanh a b
  have hnn : 0 ≤ tanh b - tanh a := by
    rw [h]
    exact div_nonneg (sinh_nonneg_iff.2 (by linarith)) (by positivity)
  linarith

/-- `tanh` is strictly monotone. -/
lemma tanh_lt_tanh_of_lt {a b : ℝ} (hab : a < b) : tanh a < tanh b := by
  have h : tanh b - tanh a = sinh (b - a) / (cosh a * cosh b) := tanh_sub_tanh a b
  have hpos : 0 < tanh b - tanh a := by
    rw [h]
    exact div_pos (sinh_pos_iff.2 (by linarith)) (by positivity)
  linarith

/-- **Georgii's inequality for `tanh`** (used in Example (8.9)(2)): the increment of `tanh` over
an interval is at most `2 * tanh` of half the interval length. -/
theorem abs_tanh_sub_tanh_le (a b : ℝ) : |tanh b - tanh a| ≤ 2 * tanh (|b - a| / 2) := by
  have hmono : ∀ x y : ℝ, x ≤ y → 0 ≤ tanh y - tanh x := by
    intro x y hxy
    rw [tanh_sub_tanh x y]
    exact div_nonneg (sinh_nonneg_iff.2 (by linarith)) (by positivity)
  rcases le_total a b with hab | hab
  · rw [abs_of_nonneg (hmono a b hab), abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
    exact tanh_sub_tanh_le_of_le hab
  · rw [abs_sub_comm (tanh b), abs_sub_comm b, abs_of_nonneg (hmono b a hab),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    exact tanh_sub_tanh_le_of_le hab

/-! ### Subadditivity on `[0, ∞)` -/

lemma tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tanh x := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_nonneg (sinh_nonneg_iff.2 hx) (cosh_pos x).le

/-- The addition formula for `tanh`. -/
lemma tanh_add (x y : ℝ) :
    tanh (x + y) = (tanh x + tanh y) / (1 + tanh x * tanh y) := by
  have hx : cosh x ≠ 0 := (cosh_pos x).ne'
  have hy : cosh y ≠ 0 := (cosh_pos y).ne'
  have hxy : cosh (x + y) ≠ 0 := (cosh_pos (x + y)).ne'
  have hden : 1 + tanh x * tanh y = cosh (x + y) / (cosh x * cosh y) := by
    rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, cosh_add]
    field_simp
  rw [tanh_eq_sinh_div_cosh, hden, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, sinh_add]
  field_simp

/-- **`tanh` is subadditive on `[0, ∞)`**: the addition formula divides by `1 + tanh x * tanh y`,
which is at least `1` when both arguments are nonnegative. -/
theorem tanh_add_le_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    tanh (x + y) ≤ tanh x + tanh y := by
  have hsum : 0 ≤ tanh x + tanh y := add_nonneg (tanh_nonneg hx) (tanh_nonneg hy)
  have hone : (1 : ℝ) ≤ 1 + tanh x * tanh y := by
    have := mul_nonneg (tanh_nonneg hx) (tanh_nonneg hy)
    linarith
  rw [tanh_add]
  exact div_le_of_le_mul₀ (by linarith) hsum (by nlinarith)

/-- **`tanh` is subadditive along finite sums of nonnegative terms.** -/
theorem tanh_sum_le {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    tanh (∑ i ∈ s, f i) ≤ ∑ i ∈ s, tanh (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hfs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (tanh_add_le_of_nonneg hfa hsum).trans (by gcongr; exact ih hfs)

/-! ### The quarter-log form -/

lemma exp_log_div_two {y : ℝ} (hy : 0 < y) : exp (log y / 2) = √y := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]
  congr 1
  ring

/-- `tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1)`. -/
lemma tanh_eq_exp_two_mul (x : ℝ) : tanh x = (exp (2 * x) - 1) / (exp (2 * x) + 1) := by
  have hx : exp x ≠ 0 := (exp_pos x).ne'
  have h2 : exp (2 * x) = exp x * exp x := by
    rw [two_mul, exp_add]
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, exp_neg, h2]
  field_simp

/-- **The sharp constant of the comparison of two normalized measures.** If the density ratio of
two measures lies in `[m, M]`, their total-variation distance is at most
`(√M - √m) / (√M + √m)`, and this equals `tanh (log (M / m) / 4)`. -/
theorem tanh_log_div_four {m M : ℝ} (hm : 0 < m) (hM : 0 < M) :
    tanh (log (M / m) / 4) = (√M - √m) / (√M + √m) := by
  have hMm : 0 < M / m := div_pos hM hm
  have hsm : 0 < √m := Real.sqrt_pos.2 hm
  have hsM : 0 < √M := Real.sqrt_pos.2 hM
  have hu : exp (2 * (log (M / m) / 4)) = √M / √m := by
    rw [show 2 * (log (M / m) / 4) = log (M / m) / 2 by ring, exp_log_div_two hMm,
      Real.sqrt_div hM.le]
  have hsum : √M + √m ≠ 0 := by positivity
  rw [tanh_eq_exp_two_mul, hu]
  rw [div_sub_one hsm.ne', div_add_one hsm.ne']
  exact div_div_div_cancel_right₀ hsm.ne' _ _

end Real

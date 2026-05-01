module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Inv

public section

namespace ENNReal
variable {α : Type*}

open NNReal

/-- Solve `a * b = c` for `a` using `b⁻¹` when `b` is finite and nonzero. -/
lemma eq_mul_inv_of_mul_eq {a b c : ℝ≥0∞} (hb : b ≠ 0) (ht : b ≠ ⊤) (h : a * b = c) :
    a = c * b⁻¹ := by
  have hb_inv : b * b⁻¹ = 1 := ENNReal.mul_inv_cancel hb ht
  calc
    a = a * 1 := by simp
    _ = a * (b * b⁻¹) := by simp [hb_inv]
    _ = (a * b) * b⁻¹ := by ac_rfl
    _ = c * b⁻¹ := by simp [h]

/-- Scalar multiplication by `r : ℝ≥0` on `ℝ≥0∞` is multiplication by the coercion. -/
lemma nnreal_smul_eq_coe_mul (r : ℝ≥0) (a : ℝ≥0∞) : r • a = (r : ℝ≥0∞) * a := by
  rw [ENNReal.smul_def, smul_eq_mul]

/-- The pathological factor `(0 : ℝ≥0)⁻¹` acts trivially on `ℝ≥0∞` (used for infinite total mass). -/
lemma nnreal_inv_zero_smul_eq_zero (a : ℝ≥0∞) : (0 : ℝ≥0)⁻¹ • a = 0 := by
  simp [nnreal_smul_eq_coe_mul]

@[simp] lemma ofReal_indicator_one (s : Set α) (a : α) :
    ENNReal.ofReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

@[simp] lemma tOReal_indicator_one (s : Set α) (a : α) :
    ENNReal.toReal (s.indicator 1 a) = s.indicator 1 a := by by_cases ha : a ∈ s <;> simp [ha]

end ENNReal

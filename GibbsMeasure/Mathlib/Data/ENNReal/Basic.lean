module

public import Mathlib.Algebra.Group.Indicator
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Analysis.SpecificLimits.Normed

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

/-- If `2 * a ≤ c` and `2 * b ≤ c` then `a + b ≤ c`. -/
theorem add_le_of_two_mul_le_of_two_mul_le {a b c : ℝ≥0∞} (h1 : 2 * a ≤ c) (h2 : 2 * b ≤ c) :
    a + b ≤ c := by
  have h : (a + b) * 2 ≤ c * 2 := by
    rw [add_mul]
    calc a * 2 + b * 2 ≤ c + c := by
          rw [mul_comm a 2, mul_comm b 2]
          exact add_le_add h1 h2
      _ = c * 2 := by ring
  exact (ENNReal.mul_le_mul_iff_left (a := a + b) (b := c) (c := 2) (by norm_num) (by norm_num)).1 h

open Filter Topology in
/-- Exponential growth beats polynomial growth in `ℝ≥0∞`: if `1 < r` then eventually
`n ^ k ≤ r ^ n`. The `ℝ≥0∞`-valued form of
`tendsto_pow_const_div_const_pow_of_one_lt`; it also holds at `r = ⊤`. -/
theorem eventually_pow_le_pow_of_one_lt {r : ℝ≥0∞} (hr : 1 < r) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ≥0∞) ^ k ≤ r ^ n := by
  rcases eq_or_ne r ⊤ with rfl | hrtop
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    rw [ENNReal.top_pow (by omega : n ≠ 0)]
    exact le_top
  · have hr' : (1 : ℝ) < r.toReal := by
      have h1 : ((1 : ℝ≥0∞)).toReal < r.toReal :=
        (ENNReal.toReal_lt_toReal (by norm_num) hrtop).2 hr
      simpa using h1
    have hev := tendsto_pow_const_div_const_pow_of_one_lt k hr'
    have h1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ k / r.toReal ^ n < 1 :=
      (tendsto_order.1 hev).2 1 one_pos
    filter_upwards [h1] with n hn
    have hpos : (0 : ℝ) < r.toReal ^ n := pow_pos (by linarith) n
    have hlt : (n : ℝ) ^ k < r.toReal ^ n := (div_lt_one hpos).1 hn
    have hle : ENNReal.ofReal ((n : ℝ) ^ k) ≤ ENNReal.ofReal (r.toReal ^ n) :=
      (ENNReal.ofReal_le_ofReal_iff hpos.le).2 hlt.le
    rwa [ENNReal.ofReal_pow (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ r.toReal), ENNReal.ofReal_toReal hrtop] at hle

end ENNReal

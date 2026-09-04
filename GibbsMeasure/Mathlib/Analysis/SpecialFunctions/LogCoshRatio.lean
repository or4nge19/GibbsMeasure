/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Tanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The function `φ_J(t) = ½ log (cosh (t + J) / cosh (t - J))`

This one-parameter family of functions is the recursion driving the Ising model on a Cayley
tree (Georgii (12.23)); it is also the "one-step magnetisation transfer" of a two-state
transfer matrix. The two closed forms

`logCoshRatio J t = ½ log (cosh (t + J) / cosh (t - J)) = artanh (tanh J * tanh t)`

are `logCoshRatio` and `logCoshRatio_eq_artanh`.

## Main results

* `logCoshRatio_eq_artanh`: the `artanh` form.
* `hasDerivAt_logCoshRatio`: `φ_J'(t) = sinh (2J) / (cosh (2t) + cosh (2J))`, together with the
  two equivalent expressions `deriv_logCoshRatio_eq_tanh_sub`
  (`½ tanh (t + J) - ½ tanh (t - J)`) and `deriv_logCoshRatio_eq_div_sinh_sq`
  (`w / (1 + (1 - w²) sinh² t)` for `w = tanh J`).
* `abs_logCoshRatio_lt`: `|φ_J(t)| < |J|` for `J ≠ 0`; in particular `φ_J` is bounded.
* `strictMono_logCoshRatio`, `strictAnti_logCoshRatio`: monotonicity in `t` for `J > 0`
  resp. `J < 0`.
* `deriv_logCoshRatio_le`: the maximal slope of `φ_J` is `φ_J'(0) = tanh J` (`J ≥ 0`), and
  `antitoneOn_deriv_logCoshRatio` is the concavity of `φ_J` on `[0, ∞)`.
* `logCoshRatio_neg_right`, `logCoshRatio_neg_left`: `φ_J` is odd, and `φ_{-J} = -φ_J`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Real

/-- **Georgii (12.23).** `φ_J(t) = ½ log (cosh (t + J) / cosh (t - J))`, the recursion of the
Ising model on a Cayley tree. Equivalently `artanh (tanh J * tanh t)`
(`logCoshRatio_eq_artanh`). -/
def logCoshRatio (J t : ℝ) : ℝ := log (cosh (t + J) / cosh (t - J)) / 2

lemma logCoshRatio_eq_sub (J t : ℝ) :
    logCoshRatio J t = (log (cosh (t + J)) - log (cosh (t - J))) / 2 := by
  rw [logCoshRatio, log_div (cosh_pos _).ne' (cosh_pos _).ne']

@[simp] lemma logCoshRatio_zero_left (t : ℝ) : logCoshRatio 0 t = 0 := by
  simp [logCoshRatio]

@[simp] lemma logCoshRatio_zero_right (J : ℝ) : logCoshRatio J 0 = 0 := by
  rw [logCoshRatio_eq_sub]
  simp [zero_sub, cosh_neg]

/-- `φ_J` is odd. -/
lemma logCoshRatio_neg_right (J t : ℝ) : logCoshRatio J (-t) = -logCoshRatio J t := by
  rw [logCoshRatio_eq_sub, logCoshRatio_eq_sub, ← neg_div]
  have h1 : -t + J = -(t - J) := by ring
  have h2 : -t - J = -(t + J) := by ring
  rw [h1, h2, cosh_neg, cosh_neg]
  ring

/-- Flipping the sign of the coupling flips the sign of `φ_J`. -/
lemma logCoshRatio_neg_left (J t : ℝ) : logCoshRatio (-J) t = -logCoshRatio J t := by
  rw [logCoshRatio_eq_sub, logCoshRatio_eq_sub, ← neg_div]
  have h1 : t + -J = t - J := by ring
  have h2 : t - -J = t + J := by ring
  rw [h1, h2]
  ring

/-- **Georgii (12.23), the `artanh` form**: `φ_J(t) = artanh (w tanh t)` with `w = tanh J`. -/
theorem logCoshRatio_eq_artanh (J t : ℝ) :
    logCoshRatio J t = artanh (tanh J * tanh t) := by
  have hJ := cosh_pos J
  have ht := cosh_pos t
  have hx : tanh J * tanh t ∈ Icc (-1 : ℝ) 1 := by
    rw [mem_Icc]
    refine ⟨?_, ?_⟩
    · nlinarith [neg_one_lt_tanh J, tanh_lt_one J, neg_one_lt_tanh t, tanh_lt_one t]
    · nlinarith [neg_one_lt_tanh J, tanh_lt_one J, neg_one_lt_tanh t, tanh_lt_one t]
  have h1 : 1 + tanh J * tanh t = cosh (t + J) / (cosh J * cosh t) := by
    rw [cosh_add, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp
  have h2 : 1 - tanh J * tanh t = cosh (t - J) / (cosh J * cosh t) := by
    rw [cosh_sub, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp
  rw [artanh_eq_half_log hx, h1, h2,
    show cosh (t + J) / (cosh J * cosh t) / (cosh (t - J) / (cosh J * cosh t))
      = cosh (t + J) / cosh (t - J) by field_simp, logCoshRatio]
  ring

/-- `2 cosh (t + J) cosh (t - J) = cosh (2t) + cosh (2J)`. -/
lemma two_mul_cosh_add_mul_cosh_sub (J t : ℝ) :
    2 * (cosh (t + J) * cosh (t - J)) = cosh (2 * t) + cosh (2 * J) := by
  have := two_mul_cosh_mul_cosh (t + J) (t - J)
  rwa [show t + J + (t - J) = 2 * t by ring, show t + J - (t - J) = 2 * J by ring] at this

lemma tanh_add_sub_tanh_sub (J t : ℝ) :
    (tanh (t + J) - tanh (t - J)) / 2 = sinh (2 * J) / (cosh (2 * t) + cosh (2 * J)) := by
  rw [tanh_sub_tanh, show t + J - (t - J) = 2 * J by ring, ← two_mul_cosh_add_mul_cosh_sub J t]
  ring

/-- **Georgii (12.26).** `φ_J'(t) = sinh (2J) / (cosh (2t) + cosh (2J))`. -/
theorem hasDerivAt_logCoshRatio (J t : ℝ) :
    HasDerivAt (logCoshRatio J) (sinh (2 * J) / (cosh (2 * t) + cosh (2 * J))) t := by
  have hc1 : HasDerivAt (fun s : ℝ ↦ cosh (s + J)) (sinh (t + J)) t := by
    simpa using ((hasDerivAt_id t).add_const J).cosh
  have hc2 : HasDerivAt (fun s : ℝ ↦ cosh (s - J)) (sinh (t - J)) t := by
    simpa using ((hasDerivAt_id t).sub_const J).cosh
  have h1 : HasDerivAt (fun s : ℝ ↦ log (cosh (s + J))) (tanh (t + J)) t := by
    simpa [tanh_eq_sinh_div_cosh] using HasDerivAt.log hc1 (cosh_pos _).ne'
  have h2 : HasDerivAt (fun s : ℝ ↦ log (cosh (s - J))) (tanh (t - J)) t := by
    simpa [tanh_eq_sinh_div_cosh] using HasDerivAt.log hc2 (cosh_pos _).ne'
  have h' : HasDerivAt (fun s : ℝ ↦ (log (cosh (s + J)) - log (cosh (s - J))) / 2)
      ((tanh (t + J) - tanh (t - J)) / 2) t := (h1.sub h2).div_const 2
  rw [tanh_add_sub_tanh_sub] at h'
  have hfun : logCoshRatio J = fun s ↦ (log (cosh (s + J)) - log (cosh (s - J))) / 2 :=
    funext (logCoshRatio_eq_sub J)
  rw [hfun]
  exact h'

/-- **Georgii (12.26), first form**: `φ_J'(t) = ½ tanh (t + J) - ½ tanh (t - J)`. -/
theorem deriv_logCoshRatio_eq_tanh_sub (J t : ℝ) :
    deriv (logCoshRatio J) t = tanh (t + J) / 2 - tanh (t - J) / 2 := by
  rw [(hasDerivAt_logCoshRatio J t).deriv, ← tanh_add_sub_tanh_sub, sub_div]

/-- **Georgii (12.26), second form**: `φ_J'(t) = w / (1 + (1 - w²) sinh² t)`, `w = tanh J`. -/
theorem deriv_logCoshRatio_eq_div_sinh_sq (J t : ℝ) :
    deriv (logCoshRatio J) t = tanh J / (1 + (1 - tanh J ^ 2) * sinh t ^ 2) := by
  rw [(hasDerivAt_logCoshRatio J t).deriv, tanh_eq_sinh_div_cosh]
  have hJ := cosh_pos J
  have hcs : cosh J ^ 2 - sinh J ^ 2 = 1 := cosh_sq_sub_sinh_sq J
  have hkey : 1 - (sinh J / cosh J) ^ 2 = 1 / cosh J ^ 2 := by field_simp; linarith
  have h2t : cosh (2 * t) = 1 + 2 * sinh t ^ 2 := by rw [cosh_two_mul, cosh_sq']; ring
  have h2J : cosh (2 * J) = 2 * cosh J ^ 2 - 1 := by rw [cosh_two_mul]; linarith
  rw [hkey, sinh_two_mul, h2t, h2J]
  have hd1 : (0 : ℝ) < 1 + 2 * sinh t ^ 2 + (2 * cosh J ^ 2 - 1) := by
    nlinarith [sq_nonneg (sinh t)]
  have hd2 : (0 : ℝ) < 1 + 1 / cosh J ^ 2 * sinh t ^ 2 := by
    have : (0 : ℝ) ≤ 1 / cosh J ^ 2 * sinh t ^ 2 := by positivity
    linarith
  rw [div_eq_div_iff hd1.ne' hd2.ne']
  field_simp
  ring

lemma deriv_logCoshRatio_zero (J : ℝ) : deriv (logCoshRatio J) 0 = tanh J := by
  simp [deriv_logCoshRatio_eq_div_sinh_sq]

/-! ### Monotonicity, boundedness and concavity -/

lemma deriv_logCoshRatio_pos {J : ℝ} (hJ : 0 < J) (t : ℝ) : 0 < deriv (logCoshRatio J) t := by
  rw [(hasDerivAt_logCoshRatio J t).deriv]
  have h1 : 0 < sinh (2 * J) := sinh_pos_iff.2 (by linarith)
  have h2 : 0 < cosh (2 * t) + cosh (2 * J) := by
    have := one_le_cosh (2 * t); have := one_le_cosh (2 * J); linarith
  positivity

lemma deriv_logCoshRatio_neg {J : ℝ} (hJ : J < 0) (t : ℝ) : deriv (logCoshRatio J) t < 0 := by
  rw [(hasDerivAt_logCoshRatio J t).deriv]
  have h1 : sinh (2 * J) < 0 := sinh_neg_iff.2 (by linarith)
  have h2 : 0 < cosh (2 * t) + cosh (2 * J) := by
    have := one_le_cosh (2 * t); have := one_le_cosh (2 * J); linarith
  exact div_neg_of_neg_of_pos h1 h2

lemma differentiable_logCoshRatio (J : ℝ) : Differentiable ℝ (logCoshRatio J) := fun t ↦
  (hasDerivAt_logCoshRatio J t).differentiableAt

lemma continuous_logCoshRatio (J : ℝ) : Continuous (logCoshRatio J) :=
  (differentiable_logCoshRatio J).continuous

/-- For a ferromagnetic coupling `J > 0`, `φ_J` is strictly increasing. -/
theorem strictMono_logCoshRatio {J : ℝ} (hJ : 0 < J) : StrictMono (logCoshRatio J) :=
  strictMono_of_deriv_pos (deriv_logCoshRatio_pos hJ)

/-- For an antiferromagnetic coupling `J < 0`, `φ_J` is strictly decreasing. -/
theorem strictAnti_logCoshRatio {J : ℝ} (hJ : J < 0) : StrictAnti (logCoshRatio J) :=
  strictAnti_of_deriv_neg (deriv_logCoshRatio_neg hJ)

lemma monotone_logCoshRatio {J : ℝ} (hJ : 0 ≤ J) : Monotone (logCoshRatio J) := by
  rcases hJ.lt_or_eq with h | h
  · exact (strictMono_logCoshRatio h).monotone
  · rw [← h]
    intro a b _
    simp

/-- For `J > 0` the recursion is bounded above by the coupling constant. -/
theorem logCoshRatio_lt {J : ℝ} (hJ : 0 < J) (t : ℝ) : logCoshRatio J t < J := by
  have hw : 0 < tanh J := tanh_pos hJ
  rw [logCoshRatio_eq_artanh]
  calc artanh (tanh J * tanh t) < artanh (tanh J) := by
        refine artanh_lt_artanh ?_ (tanh_lt_one J) ?_
        · nlinarith [neg_one_lt_tanh t, tanh_lt_one t, tanh_lt_one J]
        · nlinarith [tanh_lt_one t]
    _ = J := artanh_tanh J

/-- For `J > 0` the recursion is bounded below by minus the coupling constant. -/
theorem neg_lt_logCoshRatio {J : ℝ} (hJ : 0 < J) (t : ℝ) : -J < logCoshRatio J t := by
  have := logCoshRatio_lt hJ (-t)
  rw [logCoshRatio_neg_right] at this
  linarith

/-- `|φ_J(t)| < |J|`: the recursion is bounded by the coupling constant. -/
theorem abs_logCoshRatio_lt {J : ℝ} (hJ : J ≠ 0) (t : ℝ) : |logCoshRatio J t| < |J| := by
  rcases hJ.lt_or_gt with h | h
  · have h1 := logCoshRatio_lt (J := -J) (by linarith) t
    have h2 := neg_lt_logCoshRatio (J := -J) (by linarith) t
    rw [logCoshRatio_neg_left] at h1 h2
    rw [abs_lt, abs_of_neg h]
    constructor <;> linarith
  · rw [abs_lt, abs_of_pos h]
    exact ⟨neg_lt_logCoshRatio h t, logCoshRatio_lt h t⟩

/-- `e^{2 φ_J(t)} = cosh (t + J) / cosh (t - J)`. -/
lemma exp_two_mul_logCoshRatio (J t : ℝ) :
    exp (2 * logCoshRatio J t) = cosh (t + J) / cosh (t - J) := by
  rw [logCoshRatio, mul_div_cancel₀ _ (two_ne_zero), exp_log]
  positivity

/-! ### The maximal slope, evenness of the derivative, and concavity on `[0, ∞)` -/

/-- The derivative of `φ_J` is an even function. -/
lemma deriv_logCoshRatio_neg_arg (J t : ℝ) :
    deriv (logCoshRatio J) (-t) = deriv (logCoshRatio J) t := by
  rw [(hasDerivAt_logCoshRatio J (-t)).deriv, (hasDerivAt_logCoshRatio J t).deriv,
    show 2 * -t = -(2 * t) by ring, cosh_neg]

lemma deriv_logCoshRatio_eq (J : ℝ) :
    deriv (logCoshRatio J) = fun t ↦ sinh (2 * J) / (cosh (2 * t) + cosh (2 * J)) :=
  funext fun t ↦ (hasDerivAt_logCoshRatio J t).deriv

lemma cosh_add_cosh_pos (a b : ℝ) : 0 < cosh a + cosh b := by
  have := one_le_cosh a; have := one_le_cosh b; linarith

lemma continuous_deriv_logCoshRatio (J : ℝ) : Continuous (deriv (logCoshRatio J)) := by
  rw [deriv_logCoshRatio_eq]
  exact continuous_const.div
    ((continuous_cosh.comp (continuous_const.mul continuous_id)).add continuous_const)
    fun t ↦ (cosh_add_cosh_pos (2 * t) (2 * J)).ne'

/-- **Georgii, after (12.26).** The maximal slope of `φ_J` is `φ_J'(0) = w = tanh J`. -/
theorem deriv_logCoshRatio_le {J : ℝ} (hJ : 0 ≤ J) (t : ℝ) :
    deriv (logCoshRatio J) t ≤ tanh J := by
  rw [(hasDerivAt_logCoshRatio J t).deriv]
  have hs : 0 ≤ sinh (2 * J) := by
    rcases hJ.lt_or_eq with h | h
    · exact (sinh_pos_iff.2 (by linarith)).le
    · simp [← h]
  have h0 : sinh (2 * J) / (1 + cosh (2 * J)) = tanh J := by
    have hc := cosh_pos J
    have h1 : (1 : ℝ) + cosh (2 * J) = 2 * cosh J ^ 2 := by rw [cosh_two_mul, cosh_sq']; ring
    rw [h1, sinh_two_mul, tanh_eq_sinh_div_cosh]
    field_simp
  rw [← h0]
  refine div_le_div_of_nonneg_left hs (by linarith [one_le_cosh (2 * J)]) ?_
  linarith [one_le_cosh (2 * t)]

/-- For `J > 0` the slope of `φ_J` is strictly decreasing on `[0, ∞)`. -/
theorem strictAntiOn_deriv_logCoshRatio {J : ℝ} (hJ : 0 < J) :
    StrictAntiOn (deriv (logCoshRatio J)) (Ici 0) := by
  intro a ha b hb hab
  rw [(hasDerivAt_logCoshRatio J a).deriv, (hasDerivAt_logCoshRatio J b).deriv]
  have hs : 0 < sinh (2 * J) := sinh_pos_iff.2 (by linarith)
  have ha0 : (0 : ℝ) ≤ a := ha
  have hb0 : (0 : ℝ) ≤ b := hb
  have hlt : cosh (2 * a) < cosh (2 * b) := by
    rw [cosh_lt_cosh, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * b)]
    linarith
  exact div_lt_div_of_pos_left hs (cosh_add_cosh_pos (2 * a) (2 * J)) (by linarith)

/-- **Georgii, after (12.26).** For `J > 0`, `φ_J` is strictly concave on `[0, ∞)`. -/
theorem strictConcaveOn_logCoshRatio {J : ℝ} (hJ : 0 < J) :
    StrictConcaveOn ℝ (Ici 0) (logCoshRatio J) :=
  (strictAntiOn_deriv_logCoshRatio hJ).mono (by rw [interior_Ici]; exact Ioi_subset_Ici_self)
    |>.strictConcaveOn_of_deriv (convex_Ici 0) (continuous_logCoshRatio J).continuousOn

end Real

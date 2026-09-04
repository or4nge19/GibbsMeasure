/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatio
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Topology.Order.IntermediateValue

/-!
# The fixed points of the recursion `t ↦ h + d φ_J(t)`

`treeRecursion d J h t = h + d * logCoshRatio J t` is Georgii's recursion (12.22) for the Ising
model on the Cayley tree `CT(d)`; a real number `t` is a fixed point of it iff
`treeField d J t = t - d * logCoshRatio J t` equals `h`. Since `treeField d J` is continuous and
tends to `±∞` at `±∞`, there is always at least one solution; the whole question is how many.

## Main results

* `exists_treeField_eq`: (12.22) always has a solution.
* `strictMono_treeField`: for `d * tanh J ≤ 1` (Georgii's `dw ≤ 1`, i.e. `J ≤ J(d)`) the field
  function is strictly increasing, so `existsUnique_treeField_eq` gives *exactly one* solution,
  for every external field `h`.
* `criticalCoupling` is Georgii (12.28), `J(d) = ar coth d = ½ log ((d+1)/(d-1))`, and
  `le_criticalCoupling_iff` is `J ≤ J(d) ↔ d w ≤ 1` (`d ≥ 2`); for `d = 1`,
  `mul_tanh_lt_one_of_le_one` says `d w < 1` always, Georgii's `J(1) = ∞`.
* `treeField_eq_zero_iff_of_le_one` and `exists_treeField_eq_zero`: at zero external field the
  solutions of (12.22) are `{0}` when `d w ≤ 1`, and `{-t₊, 0, t₊}` for a unique `t₊ > 0` when
  `d w > 1` (Georgii (12.27) at `h = 0`, which is the phase transition at zero field).
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Real

/-- **Georgii (12.22).** The recursion `ψ_{J,h,d}(t) = h + d φ_J(t)` of the Ising model on the
Cayley tree `CT(d)`; its fixed points index the completely homogeneous Markov chains in
`𝒢(J, h)`. -/
def treeRecursion (d : ℕ) (J h t : ℝ) : ℝ := h + d * logCoshRatio J t

/-- The *field function* `g_{J,d}(t) = t - d φ_J(t)` of (12.22): `t` is a fixed point of
`treeRecursion d J h` iff `treeField d J t = h`. -/
def treeField (d : ℕ) (J t : ℝ) : ℝ := t - d * logCoshRatio J t

lemma treeRecursion_eq_self_iff {d : ℕ} {J h t : ℝ} :
    treeRecursion d J h t = t ↔ treeField d J t = h := by
  rw [treeRecursion, treeField]
  constructor <;> intro hh <;> linarith

@[simp] lemma treeField_zero (d : ℕ) (J : ℝ) : treeField d J 0 = 0 := by simp [treeField]

lemma treeField_neg (d : ℕ) (J t : ℝ) : treeField d J (-t) = -treeField d J t := by
  rw [treeField, treeField, logCoshRatio_neg_right]; ring

lemma continuous_treeField (d : ℕ) (J : ℝ) : Continuous (treeField d J) :=
  continuous_id.sub (continuous_const.mul (continuous_logCoshRatio J))

lemma hasDerivAt_treeField (d : ℕ) (J t : ℝ) :
    HasDerivAt (treeField d J) (1 - d * deriv (logCoshRatio J) t) t := by
  have h := (hasDerivAt_id t).sub (((hasDerivAt_logCoshRatio J t).const_mul (d : ℝ)))
  rw [(hasDerivAt_logCoshRatio J t).deriv]
  exact h

lemma deriv_treeField (d : ℕ) (J t : ℝ) :
    deriv (treeField d J) t = 1 - d * deriv (logCoshRatio J) t :=
  (hasDerivAt_treeField d J t).deriv

/-! ### Existence of a solution of (12.22) -/

lemma sub_mul_le_treeField {J : ℝ} (hJ : 0 < J) (d : ℕ) (t : ℝ) :
    t - d * J ≤ treeField d J t := by
  have := (logCoshRatio_lt hJ t).le
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (d : ℝ) * logCoshRatio J t ≤ d * J := by
    exact mul_le_mul_of_nonneg_left this hd
  simp only [treeField]
  linarith

lemma treeField_le_add_mul {J : ℝ} (hJ : 0 < J) (d : ℕ) (t : ℝ) :
    treeField d J t ≤ t + d * J := by
  have := (neg_lt_logCoshRatio hJ t).le
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : -((d : ℝ) * J) ≤ d * logCoshRatio J t := by
    have := mul_le_mul_of_nonneg_left this hd
    linarith [this]
  simp only [treeField]
  linarith

lemma tendsto_treeField_atTop {J : ℝ} (hJ : 0 < J) (d : ℕ) :
    Tendsto (treeField d J) atTop atTop :=
  tendsto_atTop_mono (sub_mul_le_treeField hJ d) (tendsto_atTop_add_const_right _ _ tendsto_id)

lemma tendsto_treeField_atBot {J : ℝ} (hJ : 0 < J) (d : ℕ) :
    Tendsto (treeField d J) atBot atBot :=
  tendsto_atBot_mono (treeField_le_add_mul hJ d) (tendsto_atBot_add_const_right _ _ tendsto_id)

/-- **(12.22) always has a solution.** -/
theorem exists_treeField_eq {J : ℝ} (hJ : 0 < J) (d : ℕ) (h : ℝ) :
    ∃ t, treeField d J t = h :=
  (continuous_treeField d J).surjective (tendsto_treeField_atTop hJ d)
    (tendsto_treeField_atBot hJ d) h

/-! ### `d w ≤ 1`: a unique solution for every external field -/

/-- Off the origin the slope of `φ_J` is strictly below its maximum `w = tanh J`. -/
lemma deriv_logCoshRatio_lt_tanh {J : ℝ} (hJ : 0 < J) {t : ℝ} (ht : t ≠ 0) :
    deriv (logCoshRatio J) t < tanh J := by
  rcases ht.lt_or_gt with h | h
  · rw [← deriv_logCoshRatio_neg_arg, ← deriv_logCoshRatio_zero J]
    exact strictAntiOn_deriv_logCoshRatio hJ (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith))
      (by linarith)
  · rw [← deriv_logCoshRatio_zero J]
    exact strictAntiOn_deriv_logCoshRatio hJ (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h

lemma deriv_treeField_pos_of_le_one {J : ℝ} (hJ : 0 < J) {d : ℕ}
    (hw : (d : ℝ) * tanh J ≤ 1) {t : ℝ} (ht : t ≠ 0) : 0 < deriv (treeField d J) t := by
  rw [deriv_treeField]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have := mul_lt_mul_of_pos_left (deriv_logCoshRatio_lt_tanh hJ ht) hd'
    linarith

/-- Gluing two strictly monotone halves at `0`. -/
private lemma strictMono_of_strictMonoOn_Iic_Ici {f : ℝ → ℝ} (h₁ : StrictMonoOn f (Iic 0))
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · exact h₁ (mem_Iic.2 (hab.le.trans hb)) (mem_Iic.2 hb) hab
  · rcases le_or_gt 0 a with ha | ha
    · exact h₂ (mem_Ici.2 ha) (mem_Ici.2 hb.le) hab
    · exact (h₁ (mem_Iic.2 ha.le) (mem_Iic.2 le_rfl) ha).trans
        (h₂ (mem_Ici.2 le_rfl) (mem_Ici.2 hb.le) hb)

/-- **Georgii, `J ≤ J(d)`.** When `d w ≤ 1` the field function `g(t) = t - d φ_J(t)` is strictly
increasing, since `d φ_J'(t) - 1 < d w - 1 ≤ 0` off the origin. -/
theorem strictMono_treeField {J : ℝ} (hJ : 0 < J) {d : ℕ} (hw : (d : ℝ) * tanh J ≤ 1) :
    StrictMono (treeField d J) := by
  refine strictMono_of_strictMonoOn_Iic_Ici ?_ ?_
  · refine strictMonoOn_of_deriv_pos (convex_Iic 0) (continuous_treeField d J).continuousOn ?_
    intro x hx
    rw [interior_Iic] at hx
    exact deriv_treeField_pos_of_le_one hJ hw (mem_Iio.1 hx).ne
  · refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_treeField d J).continuousOn ?_
    intro x hx
    rw [interior_Ici] at hx
    exact deriv_treeField_pos_of_le_one hJ hw (mem_Ioi.1 hx).ne'

/-- **Georgii Lemma (12.27)(i), the case `J ≤ J(d)`.** For `d w ≤ 1` the fixed point equation
(12.22) has exactly one solution, whatever the external field. -/
theorem existsUnique_treeField_eq {J : ℝ} (hJ : 0 < J) {d : ℕ} (hw : (d : ℝ) * tanh J ≤ 1)
    (h : ℝ) : ∃! t, treeField d J t = h := by
  obtain ⟨t, ht⟩ := exists_treeField_eq hJ d h
  exact ⟨t, ht, fun s hs ↦ (strictMono_treeField hJ hw).injective (hs.trans ht.symm)⟩

/-! ### Georgii (12.28): the critical coupling `J(d) = ar coth d` -/

/-- **Georgii (12.28).** The critical coupling `J(d) = ar coth d = ½ log ((d+1)/(d-1))` of the
Cayley tree `CT(d)`, `d ≥ 2`. (Georgii puts `J(1) = ∞`; see `mul_tanh_lt_one_of_le_one`.) -/
def criticalCoupling (d : ℕ) : ℝ := artanh (1 / d)

/-- **Georgii (12.28), explicit form.** -/
theorem criticalCoupling_eq_half_log {d : ℕ} (hd : 2 ≤ d) :
    criticalCoupling d = log (((d : ℝ) + 1) / (d - 1)) / 2 := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd.trans_lt' one_lt_two
  have hdpos : (0 : ℝ) < d := by linarith
  have hnn : (0 : ℝ) ≤ 1 / d := by positivity
  have hmem : (1 : ℝ) / d ∈ Icc (-1 : ℝ) 1 := by
    refine ⟨by linarith, ?_⟩
    rw [div_le_one hdpos]; linarith
  rw [criticalCoupling, artanh_eq_half_log hmem,
    show (1 + 1 / (d : ℝ)) / (1 - 1 / d) = ((d : ℝ) + 1) / (d - 1) by
      have hlt : (1 : ℝ) / d < 1 := by rw [div_lt_one hdpos]; linarith
      rw [div_eq_div_iff (by linarith) (by linarith)]
      field_simp]
  ring

/-- For `d = 1` (and `d = 0`) Georgii's condition `d w ≤ 1` holds for every coupling: `J(1) = ∞`. -/
theorem mul_tanh_lt_one_of_le_one {d : ℕ} (hd : d ≤ 1) (J : ℝ) : (d : ℝ) * tanh J < 1 := by
  have hd1 : (d : ℝ) ≤ 1 := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rcases le_or_gt (tanh J) 0 with hT | hT
  · nlinarith
  · nlinarith [tanh_lt_one J]

/-- **Georgii (12.28) as a criterion**: for `d ≥ 2` and `J > 0`, `J ≤ J(d) ↔ d w ≤ 1`. -/
theorem le_criticalCoupling_iff {d : ℕ} (hd : 2 ≤ d) (J : ℝ) :
    J ≤ criticalCoupling d ↔ (d : ℝ) * tanh J ≤ 1 := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd.trans_lt' one_lt_two
  have hdpos : (0 : ℝ) < d := by linarith
  have hlt : (1 : ℝ) / d < 1 := by rw [div_lt_one hdpos]; linarith
  have hgt : (-1 : ℝ) < 1 / d := by
    have : (0 : ℝ) < 1 / d := by positivity
    linarith
  have hstep : (d : ℝ) * tanh J ≤ 1 ↔ tanh J ≤ 1 / d := by
    rw [le_div_iff₀ hdpos, mul_comm]
  rw [hstep, criticalCoupling, ← artanh_tanh J,
    artanh_le_artanh_iff ⟨neg_one_lt_tanh J, tanh_lt_one J⟩ ⟨hgt, hlt⟩, artanh_tanh]

/-! ### `d w > 1`: the phase transition at zero external field -/

lemma deriv_treeField_zero (d : ℕ) (J : ℝ) :
    deriv (treeField d J) 0 = 1 - d * tanh J := by
  rw [deriv_treeField, deriv_logCoshRatio_zero]

lemma continuous_deriv_treeField (d : ℕ) (J : ℝ) : Continuous (deriv (treeField d J)) := by
  have : deriv (treeField d J) = fun t ↦ 1 - d * deriv (logCoshRatio J) t :=
    funext (deriv_treeField d J)
  rw [this]
  exact continuous_const.sub (continuous_const.mul (continuous_deriv_logCoshRatio J))

/-- The slope of `g = id - d φ_J` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_deriv_treeField {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d) :
    StrictMonoOn (deriv (treeField d J)) (Ici 0) := by
  intro a ha b hb hab
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h := strictAntiOn_deriv_logCoshRatio hJ ha hb hab
  rw [deriv_treeField, deriv_treeField]
  nlinarith

/-- **Georgii, after (12.26).** `g = id - d φ_J` is strictly convex on `[0, ∞)`. -/
theorem strictConvexOn_treeField {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d) :
    StrictConvexOn ℝ (Ici 0) (treeField d J) :=
  (strictMonoOn_deriv_treeField hJ hd).mono
      (by rw [interior_Ici]; exact Ioi_subset_Ici_self)
    |>.strictConvexOn_of_deriv (convex_Ici 0) (continuous_treeField d J).continuousOn

/-- A strictly convex function on `[0, ∞)` vanishing at `0` has at most one further zero. -/
private lemma eq_of_treeField_eq_zero_of_pos {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ha0 : treeField d J a = 0)
    (hb0 : treeField d J b = 0) : a = b := by
  have key : ∀ x y : ℝ, 0 < x → 0 < y → x < y → treeField d J x = 0 → treeField d J y = 0 →
      False := by
    intro x y hx hy hxy hx0 hy0
    have hθ : x = (1 - x / y) * 0 + (x / y) * y := by field_simp; ring
    have h1 : (0 : ℝ) < 1 - x / y := by
      have : x / y < 1 := (div_lt_one hy).2 hxy
      linarith
    have h2 : (0 : ℝ) < x / y := by positivity
    have h3 : (1 - x / y) + x / y = 1 := by ring
    have := (strictConvexOn_treeField hJ hd).2 (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le)
      (by linarith) h1 h2 h3
    simp only [smul_eq_mul] at this
    rw [← hθ, hx0, treeField_zero, hy0] at this
    simp at this
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd (key a b ha hb hlt ha0 hb0) not_false
  · exact heq
  · exact absurd (key b a hb ha hgt hb0 ha0) not_false

/-- For `d w > 1` the field function `g` is negative somewhere on `(0, ∞)`. -/
private lemma exists_pos_treeField_neg {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d)
    (hw : 1 < (d : ℝ) * tanh J) : ∃ δ > 0, treeField d J δ < 0 := by
  have h0 : deriv (treeField d J) 0 < 0 := by rw [deriv_treeField_zero]; linarith
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), deriv (treeField d J) t < 0 :=
    (continuous_deriv_treeField d J).continuousAt.eventually_lt_const h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, by linarith, ?_⟩
  have hδ : deriv (treeField d J) (ε / 2) < 0 := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hanti : StrictAntiOn (treeField d J) (Icc 0 (ε / 2)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 (ε / 2))
      (continuous_treeField d J).continuousOn fun x hx ↦ ?_
    rw [interior_Icc] at hx
    exact (strictMonoOn_deriv_treeField hJ hd (mem_Ici.2 hx.1.le)
      (mem_Ici.2 (by linarith [hx.1])) hx.2).trans hδ
  have := hanti (mem_Icc.2 ⟨le_rfl, by linarith⟩) (mem_Icc.2 ⟨by linarith, le_rfl⟩)
    (by linarith)
  rwa [treeField_zero] at this

/-- **Georgii Lemma (12.27) at `h = 0`, the case `d w > 1`.** There is a unique positive
solution of `t = d φ_J(t)`. -/
theorem existsUnique_pos_treeField_eq_zero {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d)
    (hw : 1 < (d : ℝ) * tanh J) : ∃! t : ℝ, 0 < t ∧ treeField d J t = 0 := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_treeField_neg hJ hd hw
  obtain ⟨T, hT0, hTδ⟩ :=
    (((tendsto_treeField_atTop hJ d).eventually_gt_atTop 0).and
      (eventually_gt_atTop δ)).exists
  have hsub := intermediate_value_Icc hTδ.le (continuous_treeField d J).continuousOn
  have hmem : (0 : ℝ) ∈ Icc (treeField d J δ) (treeField d J T) := ⟨hδ.le, hT0.le⟩
  obtain ⟨t, ht, ht0⟩ := hsub hmem
  refine ⟨t, ⟨by linarith [(mem_Icc.1 ht).1], ht0⟩, ?_⟩
  rintro s ⟨hs, hs0⟩
  exact eq_of_treeField_eq_zero_of_pos hJ hd hs (by linarith [(mem_Icc.1 ht).1]) hs0 ht0

/-- **Georgii Lemma (12.27) at `h = 0`, the case `d w ≤ 1`.** The origin is the only solution
of `t = d φ_J(t)`. -/
theorem treeField_eq_zero_iff_of_le_one {J : ℝ} (hJ : 0 < J) {d : ℕ}
    (hw : (d : ℝ) * tanh J ≤ 1) {t : ℝ} : treeField d J t = 0 ↔ t = 0 := by
  refine ⟨fun ht ↦ ?_, fun ht ↦ by rw [ht, treeField_zero]⟩
  exact (strictMono_treeField hJ hw).injective (by rw [ht, treeField_zero])

/-- **Georgii Lemma (12.27) at `h = 0`, the solution set.** For `d w > 1` the equation
`t = d φ_J(t)` has exactly the three solutions `-t₊ < 0 < t₊`; this is the phase transition of
the Ising ferromagnet on `CT(d)` at zero external field. -/
theorem setOf_treeField_eq_zero {J : ℝ} (hJ : 0 < J) {d : ℕ} (hd : 1 ≤ d)
    (hw : 1 < (d : ℝ) * tanh J) :
    ∃ tp : ℝ, 0 < tp ∧ {t : ℝ | treeField d J t = 0} = {-tp, 0, tp} := by
  obtain ⟨tp, ⟨htp0, htp⟩, huniq⟩ := existsUnique_pos_treeField_eq_zero hJ hd hw
  refine ⟨tp, htp0, ?_⟩
  ext t
  simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro ht
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · left
      have : treeField d J (-t) = 0 := by rw [treeField_neg, ht, neg_zero]
      have := huniq (-t) ⟨by linarith, this⟩
      linarith
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (huniq t ⟨hgt, ht⟩))
  · rintro (rfl | rfl | rfl)
    · rw [treeField_neg, htp, neg_zero]
    · exact treeField_zero d J
    · exact htp

end Real

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatio
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Topology.Order.IntermediateValue
public import GibbsMeasure.Mathlib.Dynamics.FixedPoints.MonotoneReal

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
* `treeCriticalPoint` is Georgii (12.29), `t_{J,d} = ar tanh √((d - w̄)/(d - w))`, and
  `treeCriticalField` is his critical external field `h(J, d)`;
  `isGreatest_treeCriticalField` is Georgii's defining property
  `h(J,d) = max_{t ≥ 0} [d φ_J(t) - t]`, `treeCriticalField_eq` is the explicit formula (12.30),
  and `treeCriticalField_eq_zero_iff` is `h(J,d) = 0 ↔ d w ≤ 1`, i.e. `↔ J ≤ J(d)`.
* **Lemma (12.27)** in full: `existsUnique_treeField_eq_of_le_or_lt` is (i)
  (one solution when `J ≤ J(d)` or `|h| > h(J,d)`), `exists_eq_pair_treeField_eq_of_abs_eq` is
  (ii) (exactly two when `|h| = h(J,d) > 0`) and `exists_eq_insert_treeField_eq_of_abs_lt` is
  (iii) (exactly three when `|h| < h(J,d)`); `exists_lt_and_treeField_eq` is the existence half of
  (ii) and (iii) at once. The three branches of the field function that make the count are
  `strictMonoOn_treeField_Iic`, `strictAntiOn_treeField_Icc`, `strictMonoOn_treeField_Ici`.

## A note on the names

`treeRecursion`, `treeField`, `criticalCoupling`, `treeCriticalPoint` and `treeCriticalField`
carry the vocabulary of the model the family comes from (the Ising model on a Cayley tree of
branching number `d`, with coupling `J` and external field `h`), and they are deliberately kept.
Nothing here mentions a graph, a configuration or a measure: every statement in this file is a
statement about the one real function `Real.logCoshRatio` and the two real parameters `d, J`, and
the declarations live in `Real` next to `Real.logCoshRatio` itself. What the names buy is the
characterisation, which purely descriptive names would hide:

* `criticalCoupling d = artanh (1 / d)` is the unique `J` with `d * tanh J = 1`
  (`le_criticalCoupling_iff`), i.e. the coupling at which `deriv (treeField d J) 0` changes sign
  (`deriv_treeField_zero`). A name recording only the formula (`artanhOneDiv`) would say nothing
  about why `artanh (1 / d)` is worth a definition.
* `treeCriticalPoint d J` is the unique positive zero of `deriv (treeField d J)`, and
  `treeCriticalField d J = -treeField d J (treeCriticalPoint d J)` is
  `max_{t ≥ 0} (d * logCoshRatio J t - t)` (`isGreatest_treeCriticalField`); the descriptive
  alternative is a mouthful (`sSup_sub_nsmul_logCoshRatio_Ici`) that still does not say that this
  is the threshold separating one solution from three.

There is also a hard constraint: `GibbsMeasure/Model/IsingCayleyTree.lean` uses these names and
the ~100 lemma names built on them. `@[deprecated] alias` is not a safe bridge for the `def`s —
an alias `def` is not reducible, so the renamed lemmas would no longer rewrite terms written with
the old spelling.
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

/-! ### Georgii, step 1 of the proof of Theorem (12.31): bounding a family by the extremal
fixed points

A family `u : ι → ℝ` bounded above by `h + dJ` and closed under the monotone bound
`(∀ i, u i ≤ c) → (∀ i, u i ≤ h + d φ_J(c))` lies below the greatest solution of (12.22); dually
for lower bounds. Georgii applies this to the numbers `t_{ij}` attached to an arbitrary boundary
law by (12.32). -/

lemma monotone_treeRecursion {J : ℝ} (hJ : 0 < J) (d : ℕ) (h : ℝ) :
    Monotone (treeRecursion d J h) := fun a b hab ↦ by
  have := (strictMono_logCoshRatio hJ).monotone hab
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp only [treeRecursion]
  nlinarith

lemma continuous_treeRecursion (J : ℝ) (d : ℕ) (h : ℝ) : Continuous (treeRecursion d J h) :=
  continuous_const.add (continuous_const.mul (continuous_logCoshRatio J))

lemma treeRecursion_lt {J : ℝ} (hJ : 0 < J) (d : ℕ) (h t : ℝ) :
    treeRecursion d J h t ≤ h + d * J := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := (logCoshRatio_lt hJ t).le
  simp only [treeRecursion]
  nlinarith

lemma le_treeRecursion {J : ℝ} (hJ : 0 < J) (d : ℕ) (h t : ℝ) :
    h - d * J ≤ treeRecursion d J h t := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := (neg_lt_logCoshRatio hJ t).le
  simp only [treeRecursion]
  nlinarith

/-- **Georgii, step 1 of the proof of Theorem (12.31), upper bound.** -/
theorem exists_treeField_eq_and_forall_le {J : ℝ} (hJ : 0 < J) {d : ℕ} {h : ℝ} {ι : Type*}
    {u : ι → ℝ} (hbdd : ∀ i, u i ≤ h + d * J)
    (hstep : ∀ c : ℝ, (∀ i, u i ≤ c) → ∀ i, u i ≤ treeRecursion d J h c) :
    ∃ p, treeField d J p = h ∧ ∀ i, u i ≤ p := by
  obtain ⟨p, hp, htend, -⟩ := (monotone_treeRecursion hJ d h).exists_fixedPt_tendsto_iterate_of_le
    (continuous_treeRecursion J d h) (m := h - d * J) (treeRecursion_lt hJ d h (h + d * J))
    (le_treeRecursion hJ d h)
  refine ⟨p, treeRecursion_eq_self_iff.1 hp, fun i ↦ ?_⟩
  have key : ∀ n : ℕ, ∀ i, u i ≤ (treeRecursion d J h)^[n] (h + d * J) := by
    intro n
    induction n with
    | zero => simpa using hbdd
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact hstep _ ih i
  exact _root_.ge_of_tendsto htend (Filter.Eventually.of_forall fun n ↦ key n i)

/-- **Georgii, step 1 of the proof of Theorem (12.31), lower bound.** -/
theorem exists_treeField_eq_and_forall_ge {J : ℝ} (hJ : 0 < J) {d : ℕ} {h : ℝ} {ι : Type*}
    {u : ι → ℝ} (hbdd : ∀ i, h - d * J ≤ u i)
    (hstep : ∀ c : ℝ, (∀ i, c ≤ u i) → ∀ i, treeRecursion d J h c ≤ u i) :
    ∃ p, treeField d J p = h ∧ ∀ i, p ≤ u i := by
  obtain ⟨p, hp, htend, -⟩ := (monotone_treeRecursion hJ d h).exists_fixedPt_tendsto_iterate_of_ge
    (continuous_treeRecursion J d h) (M := h + d * J) (le_treeRecursion hJ d h (h - d * J))
    (treeRecursion_lt hJ d h)
  refine ⟨p, treeRecursion_eq_self_iff.1 hp, fun i ↦ ?_⟩
  have key : ∀ n : ℕ, ∀ i, (treeRecursion d J h)^[n] (h - d * J) ≤ u i := by
    intro n
    induction n with
    | zero => simpa using hbdd
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact hstep _ ih i
  exact _root_.le_of_tendsto htend (Filter.Eventually.of_forall fun n ↦ key n i)

/-- **Georgii, step 1 + Lemma (12.27)(i).** If (12.22) has a *unique* solution `t`, every family
satisfying the two-sided monotone bounds of (12.32) is *constant*, equal to `t`. -/
theorem eq_of_forall_le_of_forall_ge_of_unique {J : ℝ} (hJ : 0 < J) {d : ℕ}
    {h : ℝ} {ι : Type*} {u : ι → ℝ} {t : ℝ}
    (ht : ∀ s, treeField d J s = h → s = t)
    (hbddU : ∀ i, u i ≤ h + d * J) (hbddL : ∀ i, h - d * J ≤ u i)
    (hstepU : ∀ c : ℝ, (∀ i, u i ≤ c) → ∀ i, u i ≤ treeRecursion d J h c)
    (hstepL : ∀ c : ℝ, (∀ i, c ≤ u i) → ∀ i, treeRecursion d J h c ≤ u i) (i : ι) :
    u i = t := by
  obtain ⟨p, hp, hple⟩ := exists_treeField_eq_and_forall_le hJ hbddU hstepU
  obtain ⟨q, hq, hqge⟩ := exists_treeField_eq_and_forall_ge hJ hbddL hstepL
  exact le_antisymm (ht p hp ▸ hple i) (ht q hq ▸ hqge i)

/-- **Georgii, step 1 + Lemma (12.27)(i), the case `d w ≤ 1`.** If `d tanh J ≤ 1`, every family
satisfying the two-sided monotone bounds of (12.32) is *constant*, equal to the unique solution of
(12.22). -/
theorem eq_of_forall_le_of_forall_ge {J : ℝ} (hJ : 0 < J) {d : ℕ}
    (hw : (d : ℝ) * tanh J ≤ 1) {h : ℝ} {ι : Type*} {u : ι → ℝ} {t : ℝ}
    (ht : treeField d J t = h)
    (hbddU : ∀ i, u i ≤ h + d * J) (hbddL : ∀ i, h - d * J ≤ u i)
    (hstepU : ∀ c : ℝ, (∀ i, u i ≤ c) → ∀ i, u i ≤ treeRecursion d J h c)
    (hstepL : ∀ c : ℝ, (∀ i, c ≤ u i) → ∀ i, treeRecursion d J h c ≤ u i) (i : ι) :
    u i = t :=
  eq_of_forall_le_of_forall_ge_of_unique hJ
    (fun _ hs ↦ (strictMono_treeField hJ hw).injective (hs.trans ht.symm)) hbddU hbddL hstepU
    hstepL i

/-! ### Georgii (12.29), (12.30): the maximiser `t_{J,d}` and the critical field `h(J,d)`

For `J > 0` and `d ≥ 1` the slope `g' = 1 - d φ_J'` of the field function is even and strictly
increasing on `[0, ∞)`, with `g'(0) = 1 - d w` (`w = tanh J`). So `g` is strictly monotone as soon
as `d w ≤ 1`; and when `d w > 1` it has a unique positive critical point `t_{J,d}`, the maximiser
(12.29) of `d φ_J(t) - t`, whose value is Georgii's critical external field `h(J, d)` of (12.27).
-/

section Critical

variable {J : ℝ} {d : ℕ}

/-- **Georgii (12.29).** `t_{J,d} = ar tanh √((d - w̄)/(d - w))` with `w = tanh J`, `w̄ = w⁻¹`:
the point at which `d φ_J(t) - t` attains its maximum over `[0, ∞)`. If `d w ≤ 1` (Georgii's
`J ≤ J(d)`) the radicand is `≤ 0` and `t_{J,d} = 0`. -/
def treeCriticalPoint (d : ℕ) (J : ℝ) : ℝ :=
  artanh (√(((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J)))

/-- **Georgii (12.27), (12.30).** The critical external field
`h(J, d) = max_{t ≥ 0} [d φ_J(t) - t] = d φ_J(t_{J,d}) - t_{J,d}`
(`isGreatest_treeCriticalField`). It vanishes iff `d w ≤ 1`, i.e. iff `J ≤ J(d)`. -/
def treeCriticalField (d : ℕ) (J : ℝ) : ℝ := -treeField d J (treeCriticalPoint d J)

lemma one_le_of_one_lt_mul_tanh (hw : 1 < (d : ℝ) * tanh J) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp at hw; linarith
  · exact hd

lemma sub_tanh_pos (hd : 1 ≤ d) (J : ℝ) : (0 : ℝ) < (d : ℝ) - tanh J := by
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have := tanh_lt_one J
  linarith

/-- The radicand of (12.29) is nonpositive exactly in Georgii's regime `J ≤ J(d)`. -/
lemma treeCriticalRadicand_nonpos (hJ : 0 < J) (hd : 1 ≤ d) (hw : (d : ℝ) * tanh J ≤ 1) :
    ((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J) ≤ 0 := by
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hnum : (d : ℝ) - (tanh J)⁻¹ ≤ 0 := by
    rw [sub_nonpos, inv_eq_one_div, le_div_iff₀ hwpos]
    exact hw
  exact div_nonpos_of_nonpos_of_nonneg hnum (sub_tanh_pos hd J).le

/-- In Georgii's regime `J > J(d)` the radicand of (12.29) lies in `(0, 1)`. -/
lemma treeCriticalRadicand_mem_Ioo (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    ((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J) ∈ Ioo (0 : ℝ) 1 := by
  have hd := one_le_of_one_lt_mul_tanh hw
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hwlt : tanh J < 1 := tanh_lt_one J
  have hden : (0 : ℝ) < (d : ℝ) - tanh J := sub_tanh_pos hd J
  have hnum : (0 : ℝ) < (d : ℝ) - (tanh J)⁻¹ := by
    rw [sub_pos, inv_eq_one_div, div_lt_iff₀ hwpos]
    exact hw
  refine ⟨div_pos hnum hden, ?_⟩
  rw [div_lt_one hden]
  have : tanh J < (tanh J)⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hwpos]
    nlinarith
  linarith

lemma treeCriticalPoint_nonneg (d : ℕ) (J : ℝ) : 0 ≤ treeCriticalPoint d J :=
  artanh_nonneg (Real.sqrt_nonneg _)

/-- **Georgii, `J ≤ J(d)`.** In the regime `d w ≤ 1` the maximiser (12.29) is the origin. -/
theorem treeCriticalPoint_of_mul_tanh_le_one (hJ : 0 < J) (hd : 1 ≤ d)
    (hw : (d : ℝ) * tanh J ≤ 1) : treeCriticalPoint d J = 0 := by
  rw [treeCriticalPoint, Real.sqrt_eq_zero'.2 (treeCriticalRadicand_nonpos hJ hd hw), artanh_zero]

/-- **Georgii, `J ≤ J(d)`.** In the regime `d w ≤ 1` the critical external field vanishes. -/
theorem treeCriticalField_of_mul_tanh_le_one (hJ : 0 < J) (hd : 1 ≤ d)
    (hw : (d : ℝ) * tanh J ≤ 1) : treeCriticalField d J = 0 := by
  rw [treeCriticalField, treeCriticalPoint_of_mul_tanh_le_one hJ hd hw, treeField_zero, neg_zero]

lemma tanh_treeCriticalPoint (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    tanh (treeCriticalPoint d J) = √(((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J)) := by
  obtain ⟨h0, h1⟩ := treeCriticalRadicand_mem_Ioo hJ hw
  refine tanh_artanh ⟨lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg _), ?_⟩
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt h0.le h1

/-- **Georgii, the derivation of (12.29)**: `sinh² t_{J,d} = (d w - 1)/(1 - w²)`. -/
theorem sinh_sq_treeCriticalPoint (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    sinh (treeCriticalPoint d J) ^ 2 = ((d : ℝ) * tanh J - 1) / (1 - tanh J ^ 2) := by
  obtain ⟨h0, h1⟩ := treeCriticalRadicand_mem_Ioo hJ hw
  set r : ℝ := ((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J) with hr
  have hd := one_le_of_one_lt_mul_tanh hw
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hwlt : tanh J < 1 := tanh_lt_one J
  have hden : (0 : ℝ) < (d : ℝ) - tanh J := sub_tanh_pos hd J
  have hmem : √r ∈ Ioo (-1 : ℝ) 1 := by
    refine ⟨lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg _), ?_⟩
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt h0.le h1
  have hsq : √r ^ 2 = r := Real.sq_sqrt h0.le
  have hpos : (0 : ℝ) < 1 - r := by linarith
  rw [treeCriticalPoint, ← hr, sinh_artanh hmem, div_pow, hsq, Real.sq_sqrt hpos.le]
  have hB : (0 : ℝ) < 1 - tanh J ^ 2 := by nlinarith
  rw [div_eq_div_iff hpos.ne' hB.ne', hr]
  field_simp
  ring

/-- **Georgii (12.29).** `t_{J,d}` is a critical point of the field function `g = id - d φ_J`. -/
theorem deriv_treeField_treeCriticalPoint (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    deriv (treeField d J) (treeCriticalPoint d J) = 0 := by
  have hd := one_le_of_one_lt_mul_tanh hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hwlt : tanh J < 1 := tanh_lt_one J
  have hw2 : (1 : ℝ) - tanh J ^ 2 ≠ 0 := by nlinarith
  have hkey : (1 : ℝ) + (1 - tanh J ^ 2) * (((d : ℝ) * tanh J - 1) / (1 - tanh J ^ 2))
      = (d : ℝ) * tanh J := by field_simp; ring
  rw [deriv_treeField, deriv_logCoshRatio_eq_div_sinh_sq, sinh_sq_treeCriticalPoint hJ hw, hkey]
  rw [show tanh J / ((d : ℝ) * tanh J) = 1 / d by
    rw [div_eq_div_iff (by positivity) hd0.ne']; ring,
    mul_one_div, div_self hd0.ne', sub_self]

/-- `t_{J,d} > 0` in the regime `d w > 1`. -/
theorem treeCriticalPoint_pos (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    0 < treeCriticalPoint d J := by
  obtain ⟨h0, h1⟩ := treeCriticalRadicand_mem_Ioo hJ hw
  refine artanh_pos ⟨Real.sqrt_pos.2 h0, ?_⟩
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt h0.le h1

/-! ### The three branches of the field function `g = id - d φ_J` for `d w > 1` -/

lemma deriv_treeField_neg_arg (d : ℕ) (J t : ℝ) :
    deriv (treeField d J) (-t) = deriv (treeField d J) t := by
  rw [deriv_treeField, deriv_treeField, deriv_logCoshRatio_neg_arg]

lemma deriv_treeField_abs (d : ℕ) (J t : ℝ) :
    deriv (treeField d J) t = deriv (treeField d J) |t| := by
  rcases abs_choice t with h | h
  · rw [h]
  · rw [h, deriv_treeField_neg_arg]

/-- Inside `(-t_{J,d}, t_{J,d})` the field function is strictly decreasing. -/
theorem deriv_treeField_neg_of_abs_lt (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {t : ℝ}
    (ht : |t| < treeCriticalPoint d J) : deriv (treeField d J) t < 0 := by
  have hd := one_le_of_one_lt_mul_tanh hw
  rw [deriv_treeField_abs, ← deriv_treeField_treeCriticalPoint hJ hw]
  exact strictMonoOn_deriv_treeField hJ hd (mem_Ici.2 (abs_nonneg t))
    (mem_Ici.2 (treeCriticalPoint_nonneg d J)) ht

/-- Outside `[-t_{J,d}, t_{J,d}]` the field function is strictly increasing. -/
theorem deriv_treeField_pos_of_lt_abs (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {t : ℝ}
    (ht : treeCriticalPoint d J < |t|) : 0 < deriv (treeField d J) t := by
  have hd := one_le_of_one_lt_mul_tanh hw
  rw [deriv_treeField_abs, ← deriv_treeField_treeCriticalPoint hJ hw]
  exact strictMonoOn_deriv_treeField hJ hd (mem_Ici.2 (treeCriticalPoint_nonneg d J))
    (mem_Ici.2 (abs_nonneg t)) ht

theorem strictAntiOn_treeField_Icc (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    StrictAntiOn (treeField d J)
      (Icc (-treeCriticalPoint d J) (treeCriticalPoint d J)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_treeField d J).continuousOn
    fun x hx ↦ ?_
  rw [interior_Icc] at hx
  exact deriv_treeField_neg_of_abs_lt hJ hw (abs_lt.2 ⟨hx.1, hx.2⟩)

theorem strictMonoOn_treeField_Ici (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    StrictMonoOn (treeField d J) (Ici (treeCriticalPoint d J)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (continuous_treeField d J).continuousOn
    fun x hx ↦ ?_
  rw [interior_Ici] at hx
  have hx0 : 0 < x := lt_of_le_of_lt (treeCriticalPoint_nonneg d J) hx
  exact deriv_treeField_pos_of_lt_abs hJ hw (by rwa [abs_of_pos hx0])

theorem strictMonoOn_treeField_Iic (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    StrictMonoOn (treeField d J) (Iic (-treeCriticalPoint d J)) := by
  refine strictMonoOn_of_deriv_pos (convex_Iic _) (continuous_treeField d J).continuousOn
    fun x hx ↦ ?_
  rw [interior_Iic] at hx
  have hx0 : x < 0 := lt_of_lt_of_le (mem_Iio.1 hx)
    (neg_nonpos.2 (treeCriticalPoint_nonneg d J))
  refine deriv_treeField_pos_of_lt_abs hJ hw ?_
  rw [abs_of_neg hx0]
  linarith [mem_Iio.1 hx]

@[simp] lemma treeField_treeCriticalPoint (d : ℕ) (J : ℝ) :
    treeField d J (treeCriticalPoint d J) = -treeCriticalField d J := by
  rw [treeCriticalField, neg_neg]

@[simp] lemma treeField_neg_treeCriticalPoint (d : ℕ) (J : ℝ) :
    treeField d J (-treeCriticalPoint d J) = treeCriticalField d J := by
  rw [treeField_neg, treeField_treeCriticalPoint, neg_neg]

/-- **Georgii (12.27), the definition of `h(J, d)`.** The critical external field is the maximum
of `d φ_J(t) - t` over `t ≥ 0`, attained at `t_{J,d}`. -/
theorem isGreatest_treeCriticalField (hJ : 0 < J) (hd : 1 ≤ d) :
    IsGreatest ((fun t ↦ (d : ℝ) * logCoshRatio J t - t) '' Ici 0) (treeCriticalField d J) := by
  have hval : ∀ t : ℝ, (d : ℝ) * logCoshRatio J t - t = -treeField d J t := fun t ↦ by
    rw [treeField]; ring
  refine ⟨⟨treeCriticalPoint d J, mem_Ici.2 (treeCriticalPoint_nonneg d J), ?_⟩, ?_⟩
  · simp only [hval, treeField_treeCriticalPoint, neg_neg]
  · rintro _ ⟨t, ht, rfl⟩
    simp only [hval, treeCriticalField, neg_le_neg_iff]
    rcases le_or_gt ((d : ℝ) * tanh J) 1 with hw | hw
    · rw [treeCriticalPoint_of_mul_tanh_le_one hJ hd hw, treeField_zero]
      have := (strictMono_treeField hJ hw).monotone (mem_Ici.1 ht)
      rwa [treeField_zero] at this
    · rcases le_or_gt t (treeCriticalPoint d J) with h | h
      · exact (strictAntiOn_treeField_Icc hJ hw).antitoneOn
          (mem_Icc.2 ⟨by linarith [treeCriticalPoint_nonneg d J, mem_Ici.1 ht], h⟩)
          (mem_Icc.2 ⟨by linarith [treeCriticalPoint_nonneg d J], le_rfl⟩) h
      · exact ((strictMonoOn_treeField_Ici hJ hw) (mem_Ici.2 le_rfl) (mem_Ici.2 h.le) h).le

end Critical

/-! ### Georgii Lemma (12.27): how many solutions (12.22) has

For `d w > 1` the field function `g = id - d φ_J` is strictly increasing on `(-∞, -t_{J,d}]` up to
the value `h(J,d)`, strictly decreasing on `[-t_{J,d}, t_{J,d}]` from `h(J,d)` down to `-h(J,d)`,
and strictly increasing on `[t_{J,d}, ∞)` from `-h(J,d)` to `+∞`. Counting the solutions of
`g(t) = h` on the three branches is Georgii's Lemma (12.27). -/

section Trichotomy

variable {J : ℝ} {d : ℕ} {h : ℝ}

/-- `h(J, d) > 0` in the regime `J > J(d)`. -/
theorem treeCriticalField_pos (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    0 < treeCriticalField d J := by
  have ht := treeCriticalPoint_pos hJ hw
  have := strictAntiOn_treeField_Icc hJ hw (mem_Icc.2 ⟨by linarith, le_of_lt ht⟩)
    (mem_Icc.2 ⟨by linarith, le_rfl⟩) ht
  rw [treeField_zero, treeField_treeCriticalPoint] at this
  linarith

theorem treeCriticalField_nonneg (hJ : 0 < J) (hd : 1 ≤ d) : 0 ≤ treeCriticalField d J := by
  rcases le_or_gt ((d : ℝ) * tanh J) 1 with hw | hw
  · rw [treeCriticalField_of_mul_tanh_le_one hJ hd hw]
  · exact (treeCriticalField_pos hJ hw).le

/-- **Georgii (12.30), the dichotomy.** `h(J, d) = 0` exactly in the regime `J ≤ J(d)`. -/
theorem treeCriticalField_eq_zero_iff (hJ : 0 < J) (hd : 1 ≤ d) :
    treeCriticalField d J = 0 ↔ (d : ℝ) * tanh J ≤ 1 := by
  refine ⟨fun hH ↦ ?_, treeCriticalField_of_mul_tanh_le_one hJ hd⟩
  by_contra hw
  exact absurd hH (treeCriticalField_pos hJ (not_le.1 hw)).ne'

/-- Below the critical point the field function does not exceed `h(J, d)`. -/
theorem treeField_le_treeCriticalField (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {t : ℝ}
    (ht : t ≤ treeCriticalPoint d J) : treeField d J t ≤ treeCriticalField d J := by
  rcases le_or_gt t (-treeCriticalPoint d J) with hlt | hlt
  · have := (strictMonoOn_treeField_Iic hJ hw).monotoneOn (mem_Iic.2 hlt) (mem_Iic.2 le_rfl) hlt
    rwa [treeField_neg_treeCriticalPoint] at this
  · have := (strictAntiOn_treeField_Icc hJ hw).antitoneOn
      (mem_Icc.2 ⟨le_rfl, by linarith [treeCriticalPoint_nonneg d J]⟩)
      (mem_Icc.2 ⟨hlt.le, ht⟩) hlt.le
    rwa [treeField_neg_treeCriticalPoint] at this

/-- Above minus the critical point the field function is at least `-h(J, d)`. -/
theorem neg_treeCriticalField_le_treeField (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {t : ℝ}
    (ht : -treeCriticalPoint d J ≤ t) : -treeCriticalField d J ≤ treeField d J t := by
  rcases le_or_gt t (treeCriticalPoint d J) with hlt | hlt
  · have := (strictAntiOn_treeField_Icc hJ hw).antitoneOn (mem_Icc.2 ⟨ht, hlt⟩)
      (mem_Icc.2 ⟨by linarith [treeCriticalPoint_nonneg d J], le_rfl⟩) hlt
    rwa [treeField_treeCriticalPoint] at this
  · have := (strictMonoOn_treeField_Ici hJ hw).monotoneOn (mem_Ici.2 le_rfl)
      (mem_Ici.2 hlt.le) hlt.le
    rwa [treeField_treeCriticalPoint] at this

/-- The right branch `[t_{J,d}, ∞)` carries exactly one solution of (12.22) for `h ≥ -h(J,d)`. -/
theorem existsUnique_treeField_eq_of_mem_Ici (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J)
    (hh : -treeCriticalField d J ≤ h) :
    ∃! t, treeCriticalPoint d J ≤ t ∧ treeField d J t = h := by
  obtain ⟨T, hT1, hT2⟩ := (((tendsto_treeField_atTop hJ d).eventually_ge_atTop h).and
    (eventually_ge_atTop (treeCriticalPoint d J))).exists
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hT2 (continuous_treeField d J).continuousOn
    (show h ∈ Icc (treeField d J (treeCriticalPoint d J)) (treeField d J T) from
      ⟨by rwa [treeField_treeCriticalPoint], hT1⟩)
  refine ⟨t, ⟨(mem_Icc.1 ht).1, hte⟩, ?_⟩
  rintro s ⟨hs, hse⟩
  exact (strictMonoOn_treeField_Ici hJ hw).injOn (mem_Ici.2 hs)
    (mem_Ici.2 (mem_Icc.1 ht).1) (hse.trans hte.symm)

/-- The left branch `(-∞, -t_{J,d}]` carries exactly one solution of (12.22) for `h ≤ h(J,d)`. -/
theorem existsUnique_treeField_eq_of_mem_Iic (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J)
    (hh : h ≤ treeCriticalField d J) :
    ∃! t, t ≤ -treeCriticalPoint d J ∧ treeField d J t = h := by
  obtain ⟨T, hT1, hT2⟩ := (((tendsto_treeField_atBot hJ d).eventually_le_atBot h).and
    (eventually_le_atBot (-treeCriticalPoint d J))).exists
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hT2 (continuous_treeField d J).continuousOn
    (show h ∈ Icc (treeField d J T) (treeField d J (-treeCriticalPoint d J)) from
      ⟨hT1, by rwa [treeField_neg_treeCriticalPoint]⟩)
  refine ⟨t, ⟨(mem_Icc.1 ht).2, hte⟩, ?_⟩
  rintro s ⟨hs, hse⟩
  exact (strictMonoOn_treeField_Iic hJ hw).injOn (mem_Iic.2 hs)
    (mem_Iic.2 (mem_Icc.1 ht).2) (hse.trans hte.symm)

/-- The middle branch `[-t_{J,d}, t_{J,d}]` carries exactly one solution of (12.22) for
`|h| ≤ h(J,d)`. -/
theorem existsUnique_treeField_eq_of_mem_Icc (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ treeCriticalField d J) :
    ∃! t, t ∈ Icc (-treeCriticalPoint d J) (treeCriticalPoint d J) ∧ treeField d J t = h := by
  obtain ⟨hh1, hh2⟩ := abs_le.1 hh
  have hle : -treeCriticalPoint d J ≤ treeCriticalPoint d J := by
    linarith [treeCriticalPoint_nonneg d J]
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' hle (continuous_treeField d J).continuousOn
    (show h ∈ Icc (treeField d J (treeCriticalPoint d J))
        (treeField d J (-treeCriticalPoint d J)) from
      ⟨by rwa [treeField_treeCriticalPoint], by rwa [treeField_neg_treeCriticalPoint]⟩)
  refine ⟨t, ⟨ht, hte⟩, ?_⟩
  rintro s ⟨hs, hse⟩
  exact (strictAntiOn_treeField_Icc hJ hw).injOn hs ht (hse.trans hte.symm)

/-- **Georgii Lemma (12.27)(i).** Outside the critical window the fixed point equation (12.22) has
exactly one solution; this covers Georgii's `|h| > h(J,d)` and, since `h(J,d) = 0` there, the whole
regime `J ≤ J(d)` with `h ≠ 0`. -/
theorem existsUnique_treeField_eq_of_lt_abs (hJ : 0 < J)
    (hh : treeCriticalField d J < |h|) : ∃! t, treeField d J t = h := by
  rcases le_or_gt ((d : ℝ) * tanh J) 1 with hwle | hw
  · exact existsUnique_treeField_eq hJ hwle h
  have hHpos := treeCriticalField_pos hJ hw
  rcases abs_cases h with ⟨he, -⟩ | ⟨he, -⟩
  · have hpos : treeCriticalField d J < h := by rwa [he] at hh
    obtain ⟨t, ⟨htc, hte⟩, huniq⟩ :=
      existsUnique_treeField_eq_of_mem_Ici hJ hw (by linarith : -treeCriticalField d J ≤ h)
    refine ⟨t, hte, fun s hs ↦ huniq s ⟨?_, hs⟩⟩
    by_contra hcon
    exact absurd (hs ▸ treeField_le_treeCriticalField hJ hw (not_le.1 hcon).le) (by linarith)
  · have hneg : h < -treeCriticalField d J := by rw [he] at hh; linarith
    obtain ⟨t, ⟨htc, hte⟩, huniq⟩ :=
      existsUnique_treeField_eq_of_mem_Iic hJ hw (by linarith : h ≤ treeCriticalField d J)
    refine ⟨t, hte, fun s hs ↦ huniq s ⟨?_, hs⟩⟩
    by_contra hcon
    exact absurd (hs ▸ neg_treeCriticalField_le_treeField hJ hw (not_le.1 hcon).le) (by linarith)

/-- **Georgii Lemma (12.27)(i), both clauses.** (12.22) has exactly one solution when
`J ≤ J(d)` (i.e. `d w ≤ 1`, whatever `h`) or when `|h| > h(J, d)`. -/
theorem existsUnique_treeField_eq_of_le_or_lt (hJ : 0 < J)
    (hh : (d : ℝ) * tanh J ≤ 1 ∨ treeCriticalField d J < |h|) : ∃! t, treeField d J t = h :=
  hh.elim (fun hw ↦ existsUnique_treeField_eq hJ hw h) (existsUnique_treeField_eq_of_lt_abs hJ)

/-- **Georgii Lemma (12.27)(ii), (iii), the existence half.** Inside the closed critical window
`|h| ≤ h(J, d)` (with `J > J(d)`) equation (12.22) has at least two solutions: Georgii's
`t₋ < t₊`. -/
theorem exists_lt_and_treeField_eq (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ treeCriticalField d J) :
    ∃ a b : ℝ, a < b ∧ treeField d J a = h ∧ treeField d J b = h := by
  obtain ⟨hh1, hh2⟩ := abs_le.1 hh
  obtain ⟨a, ⟨hac, hae⟩, -⟩ := existsUnique_treeField_eq_of_mem_Iic hJ hw hh2
  obtain ⟨b, ⟨hbc, hbe⟩, -⟩ := existsUnique_treeField_eq_of_mem_Ici hJ hw hh1
  exact ⟨a, b, by linarith [treeCriticalPoint_pos hJ hw], hae, hbe⟩

/-- **Georgii Lemma (12.27)(iii).** Strictly inside the critical window `|h| < h(J, d)` equation
(12.22) has exactly three solutions `t₋ < t_# < t₊`. -/
theorem exists_eq_insert_treeField_eq_of_abs_lt (hJ : 0 < J) (hd : 1 ≤ d)
    (hh : |h| < treeCriticalField d J) :
    ∃ a b c : ℝ, a < b ∧ b < c ∧ {t : ℝ | treeField d J t = h} = {a, b, c} := by
  have hw : 1 < (d : ℝ) * tanh J := by
    by_contra hcon
    rw [treeCriticalField_of_mul_tanh_le_one hJ hd (not_lt.1 hcon)] at hh
    exact absurd (abs_nonneg h) (by linarith)
  obtain ⟨hh1, hh2⟩ := abs_lt.1 hh
  obtain ⟨a, ⟨hac, hae⟩, hauniq⟩ := existsUnique_treeField_eq_of_mem_Iic hJ hw hh2.le
  obtain ⟨b, ⟨hbc, hbe⟩, hbuniq⟩ := existsUnique_treeField_eq_of_mem_Icc hJ hw hh.le
  obtain ⟨c, ⟨hcc, hce⟩, hcuniq⟩ := existsUnique_treeField_eq_of_mem_Ici hJ hw hh1.le
  have halt : a < -treeCriticalPoint d J := by
    rcases hac.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h' ▸ hae) (by rw [treeField_neg_treeCriticalPoint]; linarith)
  have hclt : treeCriticalPoint d J < c := by
    rcases hcc.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (h'.symm ▸ hce) (by rw [treeField_treeCriticalPoint]; linarith)
  refine ⟨a, b, c, lt_of_lt_of_le halt (mem_Icc.1 hbc).1, lt_of_le_of_lt (mem_Icc.1 hbc).2 hclt,
    ?_⟩
  ext s
  simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun hs ↦ ?_, ?_⟩
  · rcases le_or_gt s (-treeCriticalPoint d J) with h' | h'
    · exact Or.inl (hauniq s ⟨h', hs⟩)
    · rcases le_or_gt s (treeCriticalPoint d J) with h'' | h''
      · exact Or.inr (Or.inl (hbuniq s ⟨mem_Icc.2 ⟨h'.le, h''⟩, hs⟩))
      · exact Or.inr (Or.inr (hcuniq s ⟨h''.le, hs⟩))
  · rintro (rfl | rfl | rfl) <;> assumption

/-- **Georgii Lemma (12.27)(ii).** On the boundary `|h| = h(J, d) > 0` of the critical window
equation (12.22) has exactly two solutions `t₋ < t₊`. -/
theorem exists_eq_pair_treeField_eq_of_abs_eq (hJ : 0 < J) (hd : 1 ≤ d)
    (hHpos : 0 < treeCriticalField d J) (hh : |h| = treeCriticalField d J) :
    ∃ a b : ℝ, a < b ∧ {t : ℝ | treeField d J t = h} = {a, b} := by
  have hw : 1 < (d : ℝ) * tanh J := by
    by_contra hcon
    exact absurd (treeCriticalField_of_mul_tanh_le_one hJ hd (not_lt.1 hcon)) hHpos.ne'
  have htp := treeCriticalPoint_pos hJ hw
  have hle : |h| ≤ treeCriticalField d J := le_of_eq hh
  obtain ⟨hh1, hh2⟩ := abs_le.1 hle
  obtain ⟨a, ⟨hac, hae⟩, hauniq⟩ := existsUnique_treeField_eq_of_mem_Iic hJ hw hh2
  obtain ⟨b, ⟨hbc, hbe⟩, hbuniq⟩ := existsUnique_treeField_eq_of_mem_Icc hJ hw hle
  obtain ⟨c, ⟨hcc, hce⟩, hcuniq⟩ := existsUnique_treeField_eq_of_mem_Ici hJ hw hh1
  have hcov : ∀ s : ℝ, treeField d J s = h → s = a ∨ s = b ∨ s = c := by
    intro s hs
    rcases le_or_gt s (-treeCriticalPoint d J) with h' | h'
    · exact Or.inl (hauniq s ⟨h', hs⟩)
    · rcases le_or_gt s (treeCriticalPoint d J) with h'' | h''
      · exact Or.inr (Or.inl (hbuniq s ⟨mem_Icc.2 ⟨h'.le, h''⟩, hs⟩))
      · exact Or.inr (Or.inr (hcuniq s ⟨h''.le, hs⟩))
  rcases (abs_eq hHpos.le).1 hh with hcase | hcase
  · -- `h = h(J, d)`: the left and the middle branch both produce `-t_{J,d}`
    have hval : treeField d J (-treeCriticalPoint d J) = h := by
      rw [treeField_neg_treeCriticalPoint, hcase]
    have h1 : -treeCriticalPoint d J = a := hauniq _ ⟨le_rfl, hval⟩
    have h2 : -treeCriticalPoint d J = b := hbuniq _ ⟨mem_Icc.2 ⟨le_rfl, by linarith⟩, hval⟩
    refine ⟨a, c, by rw [← h1]; linarith, ?_⟩
    ext s
    simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun hs ↦ ?_, ?_⟩
    · rcases hcov s hs with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inl (h'.trans (h2.symm.trans h1))
      · exact Or.inr h'
    · rintro (rfl | rfl) <;> assumption
  · -- `h = -h(J, d)`: the middle and the right branch both produce `t_{J,d}`
    have hval : treeField d J (treeCriticalPoint d J) = h := by
      rw [treeField_treeCriticalPoint, hcase]
    have h2 : treeCriticalPoint d J = b := hbuniq _ ⟨mem_Icc.2 ⟨by linarith, le_rfl⟩, hval⟩
    have h3 : treeCriticalPoint d J = c := hcuniq _ ⟨le_rfl, hval⟩
    refine ⟨a, c, by rw [← h3]; linarith, ?_⟩
    ext s
    simp only [Set.mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun hs ↦ ?_, ?_⟩
    · rcases hcov s hs with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (h'.trans (h2.symm.trans h3))
      · exact Or.inr h'
    · rintro (rfl | rfl) <;> assumption

end Trichotomy

/-! ### Georgii (12.30): the explicit critical external field -/

/-- **Georgii (12.30).** For `J > J(d)` (i.e. `d w > 1`),
`h(J, d) = d · ar tanh √((d w - 1)/(d w̄ - 1)) - ar tanh √((d - w̄)/(d - w))`,
with `w = tanh J` and `w̄ = w⁻¹`. -/
theorem treeCriticalField_eq {J : ℝ} {d : ℕ} (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    treeCriticalField d J
      = d * artanh (√(((d : ℝ) * tanh J - 1) / ((d : ℝ) * (tanh J)⁻¹ - 1)))
        - artanh (√(((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J))) := by
  have hd := one_le_of_one_lt_mul_tanh hw
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hden : (0 : ℝ) < (d : ℝ) - tanh J := sub_tanh_pos hd J
  obtain ⟨h0, h1⟩ := treeCriticalRadicand_mem_Ioo hJ hw
  have hkey : tanh J * √(((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J))
      = √(((d : ℝ) * tanh J - 1) / ((d : ℝ) * (tanh J)⁻¹ - 1)) := by
    have hsplit : √(tanh J ^ 2 * (((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J)))
        = tanh J * √(((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - tanh J)) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hwpos.le]
    rw [← hsplit]
    congr 1
    have hne : (d : ℝ) * (tanh J)⁻¹ - 1 ≠ 0 := by
      have : (1 : ℝ) < (d : ℝ) * (tanh J)⁻¹ := by
        rw [inv_eq_one_div, mul_one_div, lt_div_iff₀ hwpos]; linarith
      linarith
    field_simp
  rw [treeCriticalField, treeField, logCoshRatio_eq_artanh, tanh_treeCriticalPoint hJ hw, hkey,
    treeCriticalPoint]
  ring

/-! ### Georgii (12.33): the magnetisation at the critical external field

At `h = -h(J, d)` the largest solution of (12.22) is `t₊ = t_{J,d}` (`treeField_treeCriticalPoint`),
and Georgii's computation of `sinh 2t_{J,d}` and `e^{-2J} + cosh 2t_{J,d}` turns the magnetisation
formula (12.25) into `(d - w)^{1/2}(d - w̄)^{1/2}(d - 1)^{-1}`. -/

section Magnetisation

variable {J : ℝ} {d : ℕ}

lemma exp_neg_two_mul_eq_div_tanh (J : ℝ) : exp (-(2 * J)) = (1 - tanh J) / (1 + tanh J) := by
  have hden : (0 : ℝ) < 1 + tanh J := by linarith [neg_one_lt_tanh J]
  have hc : (0 : ℝ) < cosh J := cosh_pos J
  have hp : (0 : ℝ) < exp J := exp_pos J
  rw [eq_div_iff hden.ne', tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq,
    show -(2 * J) = -J + -J by ring, exp_add]
  simp only [exp_neg]
  field_simp
  ring

/-- **Georgii, before (12.33).** At the critical external field `h = -h(J, d)` the largest
solution `t₊` of (12.22) is the critical point `t_{J,d}` of (12.29). -/
theorem le_treeCriticalPoint_of_treeField_eq (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {s : ℝ}
    (hs : treeField d J s = -treeCriticalField d J) : s ≤ treeCriticalPoint d J := by
  by_contra hcon
  have hlt := strictMonoOn_treeField_Ici hJ hw (mem_Ici.2 le_rfl) (mem_Ici.2 (not_le.1 hcon).le)
    (not_le.1 hcon)
  rw [treeField_treeCriticalPoint, hs] at hlt
  exact absurd hlt (lt_irrefl _)

/-- **Georgii (12.33).** At `J > J(d)` the magnetisation (12.25) evaluated at the critical point
`t_{J,d}` is `(d - w)^{1/2} (d - w̄)^{1/2} (d - 1)^{-1}` (`w = tanh J`, `w̄ = w⁻¹`). -/
theorem sinh_div_exp_add_cosh_treeCriticalPoint (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) :
    sinh (2 * treeCriticalPoint d J) / (exp (-(2 * J)) + cosh (2 * treeCriticalPoint d J))
      = √((d : ℝ) - tanh J) * √((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - 1) := by
  have hd := one_le_of_one_lt_mul_tanh hw
  have hwpos : (0 : ℝ) < tanh J := tanh_pos hJ
  have hwlt : tanh J < 1 := tanh_lt_one J
  obtain ⟨h0, h1⟩ := treeCriticalRadicand_mem_Ioo hJ hw
  set w : ℝ := tanh J with hwdef
  have hwne : w ≠ 0 := hwpos.ne'
  have hw1 : (1 : ℝ) + w ≠ 0 := by linarith
  have hw2 : (1 : ℝ) - w ^ 2 ≠ 0 := by nlinarith
  have hApos : (0 : ℝ) < (d : ℝ) - w := sub_tanh_pos hd J
  have hBpos : (0 : ℝ) < (d : ℝ) - w⁻¹ := by
    rw [sub_pos, inv_eq_one_div, div_lt_iff₀ hwpos]; exact hw
  obtain ⟨A, hA0, hAsq, hAeq⟩ : ∃ A : ℝ, 0 < A ∧ A ^ 2 = (d : ℝ) - w ∧ √((d : ℝ) - w) = A :=
    ⟨√((d : ℝ) - w), Real.sqrt_pos.2 hApos, Real.sq_sqrt hApos.le, rfl⟩
  obtain ⟨B, hB0, hBsq, hBeq⟩ :
      ∃ B : ℝ, 0 < B ∧ B ^ 2 = (d : ℝ) - w⁻¹ ∧ √((d : ℝ) - w⁻¹) = B :=
    ⟨√((d : ℝ) - w⁻¹), Real.sqrt_pos.2 hBpos, Real.sq_sqrt hBpos.le, rfl⟩
  have hrBA : √(((d : ℝ) - w⁻¹) / ((d : ℝ) - w)) = B / A := by
    rw [Real.sqrt_div hBpos.le, hAeq, hBeq]
  have hmem : B / A ∈ Ioo (-1 : ℝ) 1 := by
    rw [← hrBA]
    refine ⟨lt_of_lt_of_le (by norm_num) (Real.sqrt_nonneg _), ?_⟩
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt h0.le h1
  have hlt : B < A := by
    have hBA := (mem_Ioo.1 hmem).2
    rwa [div_lt_one hA0] at hBA
  have hK : (0 : ℝ) < A ^ 2 - B ^ 2 := by nlinarith
  have hKval : A ^ 2 - B ^ 2 = w⁻¹ - w := by rw [hAsq, hBsq]; ring
  have hKne : w⁻¹ - w ≠ 0 := by rw [← hKval]; exact hK.ne'
  have hone : (1 : ℝ) - (B / A) ^ 2 = (A ^ 2 - B ^ 2) / A ^ 2 := by field_simp
  obtain ⟨S, hS0, hSsq, hSeq⟩ :
      ∃ S : ℝ, 0 < S ∧ S ^ 2 = A ^ 2 - B ^ 2 ∧ √(A ^ 2 - B ^ 2) = S :=
    ⟨√(A ^ 2 - B ^ 2), Real.sqrt_pos.2 hK, Real.sq_sqrt hK.le, rfl⟩
  have hsqrt : √(1 - (B / A) ^ 2) = S / A := by
    rw [hone, Real.sqrt_div hK.le, Real.sqrt_sq hA0.le, hSeq]
  have hsinh : sinh (treeCriticalPoint d J) = B / S := by
    rw [treeCriticalPoint, ← hwdef, hrBA, sinh_artanh hmem, hsqrt]
    field_simp
  have hcosh : cosh (treeCriticalPoint d J) = A / S := by
    rw [treeCriticalPoint, ← hwdef, hrBA, cosh_artanh hmem, hsqrt]
    field_simp
  have hsinh2 : sinh (2 * treeCriticalPoint d J) = 2 * (A * B) / S ^ 2 := by
    rw [sinh_two_mul, hsinh, hcosh]
    field_simp
  have hcosh2 : cosh (2 * treeCriticalPoint d J) = (A ^ 2 + B ^ 2) / S ^ 2 := by
    have hS2 : (S : ℝ) ^ 2 ≠ 0 := by positivity
    rw [cosh_two_mul, hcosh, hsinh, div_pow, div_pow, eq_div_iff hS2, add_mul,
      div_mul_cancel₀ _ hS2, div_mul_cancel₀ _ hS2]
  have hd1 : (1 : ℝ) < (d : ℝ) := by nlinarith
  have hd1ne : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hinv : w⁻¹ - w = (1 - w ^ 2) / w := by field_simp
  have hden : exp (-(2 * J)) + cosh (2 * treeCriticalPoint d J)
      = 2 * ((d : ℝ) - 1) * w / (1 - w ^ 2) := by
    rw [exp_neg_two_mul_eq_div_tanh, ← hwdef, hcosh2, hSsq, hKval, hAsq, hBsq, hinv]
    field_simp
    ring
  have hnum : sinh (2 * treeCriticalPoint d J) = 2 * (A * B) * w / (1 - w ^ 2) := by
    rw [hsinh2, hSsq, hKval, hinv, div_div_eq_mul_div]
  rw [hnum, hden, hAeq, hBeq]
  rw [div_div_div_cancel_right₀]
  · field_simp
  · positivity

end Magnetisation

/-! ### Georgii (12.34), (12.35): the alternating recursion

For an antiferromagnetic coupling `J < 0` the recursion `ψ_{J,h,d} = h + d φ_J` is *decreasing*, so
it has a single fixed point; the object carrying the antiferromagnetic phase transition is its
second iterate `t ↦ h + d φ_J(h + d φ_J(t))`, Georgii's (12.35), whose fixed points are exactly the
pairs (12.34). That second iterate is increasing whatever the sign of `J`. -/

section Alternating

variable {J h : ℝ} {d : ℕ}

/-- `|φ_J(t)| ≤ |J|` for every coupling. -/
lemma abs_logCoshRatio_le (J t : ℝ) : |logCoshRatio J t| ≤ |J| := by
  rcases eq_or_ne J 0 with rfl | hJ
  · simp
  · exact (abs_logCoshRatio_lt hJ t).le

lemma tanh_eq_sinh_two_mul_div (J : ℝ) : tanh J = sinh (2 * J) / (1 + cosh (2 * J)) := by
  have hc := cosh_pos J
  have h1 : (1 : ℝ) + cosh (2 * J) = 2 * cosh J ^ 2 := by rw [cosh_two_mul, cosh_sq']; ring
  rw [h1, sinh_two_mul, tanh_eq_sinh_div_cosh]
  field_simp

lemma abs_deriv_logCoshRatio_eq (J t : ℝ) :
    |deriv (logCoshRatio J) t| = |sinh (2 * J)| / (cosh (2 * t) + cosh (2 * J)) := by
  rw [(hasDerivAt_logCoshRatio J t).deriv, abs_div,
    abs_of_pos (cosh_add_cosh_pos (2 * t) (2 * J))]

lemma abs_tanh_eq_div (J : ℝ) : |tanh J| = |sinh (2 * J)| / (1 + cosh (2 * J)) := by
  have hpos : (0 : ℝ) < 1 + cosh (2 * J) := by linarith [one_le_cosh (2 * J)]
  rw [tanh_eq_sinh_two_mul_div, abs_div, abs_of_pos hpos]

/-- **Georgii, after (12.26), for either sign of `J`.** The maximal slope of `φ_J` in absolute
value is `|w| = |tanh J|`. -/
theorem abs_deriv_logCoshRatio_le (J t : ℝ) : |deriv (logCoshRatio J) t| ≤ |tanh J| := by
  rw [abs_deriv_logCoshRatio_eq, abs_tanh_eq_div]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (by linarith [one_le_cosh (2 * J)])
    (by linarith [one_le_cosh (2 * t)])

/-- Off the origin, and for a non-zero coupling, the slope of `φ_J` is strictly below `|w|`. -/
theorem abs_deriv_logCoshRatio_lt (hJ : J ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    |deriv (logCoshRatio J) t| < |tanh J| := by
  rw [abs_deriv_logCoshRatio_eq, abs_tanh_eq_div]
  have hs : 0 < |sinh (2 * J)| :=
    abs_pos.2 fun hcon ↦ hJ (by simpa using sinh_eq_zero.1 hcon)
  have hct : 1 < cosh (2 * t) := by
    rw [one_lt_cosh]
    exact fun hcon ↦ ht (by linarith)
  exact div_lt_div_of_pos_left hs (by linarith [one_le_cosh (2 * J)]) (by linarith)

/-! #### Existence of a fixed point of (12.22) for either sign of `J` -/

lemma sub_mul_abs_le_treeField (d : ℕ) (J t : ℝ) : t - d * |J| ≤ treeField d J t := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := abs_le.1 (abs_logCoshRatio_le J t)
  simp only [treeField]
  nlinarith [this.2]

lemma treeField_le_add_mul_abs (d : ℕ) (J t : ℝ) : treeField d J t ≤ t + d * |J| := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := abs_le.1 (abs_logCoshRatio_le J t)
  simp only [treeField]
  nlinarith [this.1]

lemma tendsto_treeField_atTop' (d : ℕ) (J : ℝ) : Tendsto (treeField d J) atTop atTop :=
  tendsto_atTop_mono (sub_mul_abs_le_treeField d J)
    (tendsto_atTop_add_const_right _ _ tendsto_id)

lemma tendsto_treeField_atBot' (d : ℕ) (J : ℝ) : Tendsto (treeField d J) atBot atBot :=
  tendsto_atBot_mono (treeField_le_add_mul_abs d J)
    (tendsto_atBot_add_const_right _ _ tendsto_id)

/-- **(12.22) always has a solution**, for either sign of the coupling. -/
theorem exists_isFixedPt_treeRecursion (d : ℕ) (J h : ℝ) : ∃ t, treeRecursion d J h t = t := by
  obtain ⟨t, ht⟩ := (continuous_treeField d J).surjective (tendsto_treeField_atTop' d J)
    (tendsto_treeField_atBot' d J) h
  exact ⟨t, treeRecursion_eq_self_iff.2 ht⟩

/-! #### The second iterate (12.35) -/

/-- **Georgii (12.35).** `ψ_{J,h,d}(t) = h + d φ_J(h + d φ_J(t))`, the second iterate of the
recursion (12.22); its fixed points are Georgii's alternating pairs (12.34). -/
def treeRecursion₂ (d : ℕ) (J h t : ℝ) : ℝ := treeRecursion d J h (treeRecursion d J h t)

lemma continuous_treeRecursion₂ (d : ℕ) (J h : ℝ) : Continuous (treeRecursion₂ d J h) :=
  (continuous_treeRecursion J d h).comp (continuous_treeRecursion J d h)

lemma monotone_treeRecursion_of_nonneg (hJ : 0 ≤ J) (d : ℕ) (h : ℝ) :
    Monotone (treeRecursion d J h) := fun a b hab ↦ by
  have := (monotone_logCoshRatio hJ) hab
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp only [treeRecursion]
  nlinarith

lemma antitone_treeRecursion_of_nonpos (hJ : J ≤ 0) (d : ℕ) (h : ℝ) :
    Antitone (treeRecursion d J h) := fun a b hab ↦ by
  have hmono : logCoshRatio J b ≤ logCoshRatio J a := by
    have hstep := (monotone_logCoshRatio (neg_nonneg.2 hJ)) hab
    rw [logCoshRatio_neg_left, logCoshRatio_neg_left] at hstep
    linarith
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  simp only [treeRecursion]
  nlinarith

/-- **Georgii, after (12.35).** `ψ_{J,h,d}` is increasing, for either sign of the coupling. -/
theorem monotone_treeRecursion₂ (d : ℕ) (J h : ℝ) : Monotone (treeRecursion₂ d J h) := by
  intro a b hab
  rcases le_total 0 J with hJ | hJ
  · exact (monotone_treeRecursion_of_nonneg hJ d h)
      ((monotone_treeRecursion_of_nonneg hJ d h) hab)
  · exact (antitone_treeRecursion_of_nonpos hJ d h)
      ((antitone_treeRecursion_of_nonpos hJ d h) hab)

lemma hasDerivAt_treeRecursion (d : ℕ) (J h t : ℝ) :
    HasDerivAt (treeRecursion d J h) ((d : ℝ) * deriv (logCoshRatio J) t) t := by
  have hstep := ((hasDerivAt_logCoshRatio J t).const_mul (d : ℝ)).const_add h
  rw [(hasDerivAt_logCoshRatio J t).deriv]
  exact hstep

lemma hasDerivAt_treeRecursion₂ (d : ℕ) (J h t : ℝ) :
    HasDerivAt (treeRecursion₂ d J h)
      ((d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t) *
        ((d : ℝ) * deriv (logCoshRatio J) t)) t :=
  HasDerivAt.comp t (hasDerivAt_treeRecursion d J h (treeRecursion d J h t))
    (hasDerivAt_treeRecursion d J h t)

/-- **Georgii, `|J| ≤ J(d)`.** If `d |w| ≤ 1` then `t ↦ t - ψ_{J,h,d}(t)` is strictly increasing:
`|ψ'| = (d |φ_J'(·)|)(d |φ_J'(t)|) < 1` off the origin. -/
theorem strictMono_sub_treeRecursion₂ (d : ℕ) (J h : ℝ) (hw : (d : ℝ) * |tanh J| ≤ 1) :
    StrictMono (fun t ↦ t - treeRecursion₂ d J h t) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · intro a b hab
    simp only [treeRecursion₂, treeRecursion, Nat.cast_zero, zero_mul, add_zero]
    linarith
  rcases eq_or_ne J 0 with rfl | hJ
  · intro a b hab
    simp only [treeRecursion₂, treeRecursion, logCoshRatio_zero_left, mul_zero, add_zero]
    linarith
  have hd : (0 : ℝ) < d := by exact_mod_cast hd0
  have hcont : Continuous (fun t ↦ t - treeRecursion₂ d J h t) :=
    continuous_id.sub (continuous_treeRecursion₂ d J h)
  have hderiv : ∀ t : ℝ, deriv (fun s ↦ s - treeRecursion₂ d J h s) t
      = 1 - (d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t) *
          ((d : ℝ) * deriv (logCoshRatio J) t) :=
    fun t ↦ ((hasDerivAt_id t).sub (hasDerivAt_treeRecursion₂ d J h t)).deriv
  have hpos : ∀ {t : ℝ}, t ≠ 0 → 0 < deriv (fun s ↦ s - treeRecursion₂ d J h s) t := by
    intro t ht
    rw [hderiv]
    have h1 : |(d : ℝ) * deriv (logCoshRatio J) t| < 1 := by
      rw [abs_mul, abs_of_pos hd]
      exact lt_of_lt_of_le (by nlinarith [abs_deriv_logCoshRatio_lt hJ ht]) hw
    have h2 : |(d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t)| ≤ 1 := by
      rw [abs_mul, abs_of_pos hd]
      exact le_trans (by nlinarith [abs_deriv_logCoshRatio_le J (treeRecursion d J h t)]) hw
    have hprod : |(d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t) *
        ((d : ℝ) * deriv (logCoshRatio J) t)| < 1 := by
      rw [abs_mul]
      calc |(d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t)| *
            |(d : ℝ) * deriv (logCoshRatio J) t|
          ≤ 1 * |(d : ℝ) * deriv (logCoshRatio J) t| :=
            mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ < 1 := by rw [one_mul]; exact h1
    linarith [le_abs_self ((d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h t) *
      ((d : ℝ) * deriv (logCoshRatio J) t))]
  refine strictMono_of_strictMonoOn_Iic_Ici ?_ ?_
  · refine strictMonoOn_of_deriv_pos (convex_Iic 0) hcont.continuousOn fun x hx ↦ ?_
    rw [interior_Iic] at hx
    exact hpos (mem_Iio.1 hx).ne
  · refine strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn fun x hx ↦ ?_
    rw [interior_Ici] at hx
    exact hpos (mem_Ioi.1 hx).ne'

/-- **Georgii, `|J| ≤ J(d)`.** If `d |w| ≤ 1` then equation (12.35) has exactly one solution,
namely the unique solution of (12.22). -/
theorem existsUnique_isFixedPt_treeRecursion₂ (d : ℕ) (J h : ℝ) (hw : (d : ℝ) * |tanh J| ≤ 1) :
    ∃! t, treeRecursion₂ d J h t = t := by
  obtain ⟨t, ht⟩ := exists_isFixedPt_treeRecursion d J h
  have ht2 : treeRecursion₂ d J h t = t := by rw [treeRecursion₂, ht, ht]
  refine ⟨t, ht2, fun s hs ↦ (strictMono_sub_treeRecursion₂ d J h hw).injective ?_⟩
  simp only [hs, ht2, sub_self]

/-- The fixed points of the recursion (12.22) are fixed points of (12.35). -/
lemma isFixedPt_treeRecursion₂_of_isFixedPt {t : ℝ} (ht : treeRecursion d J h t = t) :
    treeRecursion₂ d J h t = t := by rw [treeRecursion₂, ht, ht]

/-- **Georgii (12.34) ⇔ (12.35).** A solution of (12.35) is exactly the first entry of a pair
`(t₀, t₁)` with `t₀ = h + d φ_J(t₁)` and `t₁ = h + d φ_J(t₀)`. -/
theorem isFixedPt_treeRecursion₂_iff {t : ℝ} :
    treeRecursion₂ d J h t = t ↔
      ∃ s : ℝ, t = h + d * logCoshRatio J s ∧ s = h + d * logCoshRatio J t := by
  refine ⟨fun ht ↦ ⟨treeRecursion d J h t, ht.symm, rfl⟩, ?_⟩
  rintro ⟨s, hts, hst⟩
  rw [treeRecursion₂, treeRecursion, treeRecursion, ← hst, ← hts]

end Alternating

end Real

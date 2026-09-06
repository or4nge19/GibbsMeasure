/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioFixedPoint

/-!
# The antiferromagnetic branch of the tree recursion

For a *negative* coupling `J < 0` the recursion `t ↦ h + d φ_J(t)` of Georgii (12.22)
(`Real.treeRecursion`) is decreasing, so it has exactly one fixed point `t_*`; the object
carrying the phase transition is its second iterate `Real.treeRecursion₂`, Georgii's (12.35).
This file proves that (12.35) has a fixed point other than `t_*` — hence a genuine alternating
pair (12.34) — as soon as

`J < -J(d)`   (equivalently `1 < d |tanh J|`)   and   `|h| < antiferroCriticalField d J`.

`antiferroCriticalField d J` is Georgii's `ĥ(J, d) = t_{-J,d} - d φ_J(t_{-J,d})`, the quantity
he uses to show that his phase transition interval `I(J, d)` is non-degenerate
(`sup I(J, d) ≥ ĥ(J, d) = h(-J, d) + 2 t_{-J,d} > 0`, `antiferroCriticalField_eq` and
`antiferroCriticalField_pos` below). Georgii's further assertion `I(J, d) = ]-ĥ, ĥ[` is stated in
the book as *suggested by numerical calculations*, not proved; what is proved here is the
inclusion `]-ĥ, ĥ[ ⊆ I(J, d)`, which is exactly the non-degeneracy he does establish.

## Main results

* `Real.strictMono_treeField_of_neg`, `Real.existsUnique_treeField_eq_of_neg` — for `J < 0` the
  field function `t ↦ t - d φ_J(t)` is strictly increasing, so (12.22) has exactly one solution.
* `Real.one_lt_sq_mul_deriv_logCoshRatio` — the derivative test: `|d φ_J'(t)| > 1` exactly for
  `|t| < t_{-J,d}`, by Georgii's computation (12.29) of the critical point.
* `Real.exists_isFixedPt_treeRecursion₂_ne` — the conclusion: a fixed point of (12.35) that is
  not a fixed point of (12.22).

## Why the derivative test is the right one

`ψ = ψ_{J,h,d}` is increasing with `ψ(t_*) = t_*` and `ψ'(t_*) = (d φ_J'(t_*))²`. If that
number exceeds `1` then `ψ(t) > t` just to the right of `t_*`, while `ψ ≤ h + d|J|` is bounded,
so `ψ(t) - t` changes sign and the intermediate value theorem produces a second fixed point.
The condition `(d φ_J'(t_*))² > 1` reads `sinh² t_* < (d|w| - 1)/(1 - w²)` with `w = tanh J`,
i.e. `|t_*| < t_{-J,d}` by Georgii's (12.29); and since `t_* = (treeField d J)⁻¹(h)` with
`treeField d J` odd and strictly increasing, that is `|h| < treeField d J (t_{-J,d}) = ĥ(J,d)`.
-/

@[expose] public section

open Filter Set

open scoped Topology

namespace Real

variable {J h : ℝ} {d : ℕ}

/-! ### The field function for a negative coupling -/

/-- For `J < 0` the field function `t ↦ t - d φ_J(t)` of (12.22) is strictly increasing: `φ_J`
is decreasing, so the derivative `1 - d φ_J'(t)` is at least `1`. -/
theorem strictMono_treeField_of_neg (hJ : J < 0) (d : ℕ) : StrictMono (treeField d J) :=
  strictMono_of_deriv_pos fun t ↦ by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have := deriv_logCoshRatio_neg hJ t
    rw [deriv_treeField]
    nlinarith

/-- For `J < 0` equation (12.22) has exactly one solution, for every external field. -/
theorem existsUnique_treeField_eq_of_neg (hJ : J < 0) (d : ℕ) (h : ℝ) :
    ∃! t, treeField d J t = h := by
  obtain ⟨t, ht⟩ := (continuous_treeField d J).surjective (tendsto_treeField_atTop' d J)
    (tendsto_treeField_atBot' d J) h
  exact ⟨t, ht, fun s hs ↦ (strictMono_treeField_of_neg hJ d).injective (hs.trans ht.symm)⟩

/-- For `J < 0` the recursion (12.22) has exactly one fixed point. -/
theorem existsUnique_isFixedPt_treeRecursion_of_neg (hJ : J < 0) (d : ℕ) (h : ℝ) :
    ∃! t, treeRecursion d J h t = t := by
  simpa only [treeRecursion_eq_self_iff] using existsUnique_treeField_eq_of_neg hJ d h

/-! ### Georgii's critical field `ĥ(J, d)` of the antiferromagnet -/

/-- **Georgii, after (12.35).** The antiferromagnetic critical field
`ĥ(J, d) = t_{-J,d} - d φ_J(t_{-J,d})`, the endpoint of the interval of external fields for which
the phase transition is established here. (Georgii writes `h(J, d)` for it, the same letter as the
ferromagnetic critical field (12.30) at the *reflected* coupling; the two are related by
`antiferroCriticalField_eq`.) -/
noncomputable def antiferroCriticalField (d : ℕ) (J : ℝ) : ℝ :=
  treeField d J (treeCriticalPoint d (-J))

/-- **Georgii, after (12.35).** `ĥ(J, d) = h(-J, d) + 2 t_{-J,d}`. -/
theorem antiferroCriticalField_eq (d : ℕ) (J : ℝ) :
    antiferroCriticalField d J
      = treeCriticalField d (-J) + 2 * treeCriticalPoint d (-J) := by
  rw [antiferroCriticalField, treeCriticalField, treeField, treeField, logCoshRatio_neg_left]
  ring

lemma tanh_neg_of_neg (hJ : J < 0) : tanh J < 0 := by
  rw [tanh_eq_sinh_div_cosh]
  exact div_neg_of_neg_of_pos (sinh_neg_iff.2 hJ) (cosh_pos J)

/-- With `J < 0`, Georgii's `J < -J(d)` says `1 < d |tanh J|`, i.e. `1 < d tanh (-J)` for the
reflected (ferromagnetic) coupling `-J > 0`. -/
theorem one_lt_mul_tanh_neg (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|) :
    1 < (d : ℝ) * tanh (-J) := by
  rwa [tanh_neg, ← abs_of_neg (tanh_neg_of_neg hJ)]

/-- `t_{-J,d} > 0` in Georgii's antiferromagnetic regime `J < -J(d)`. -/
theorem treeCriticalPoint_neg_pos (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|) :
    0 < treeCriticalPoint d (-J) :=
  treeCriticalPoint_pos (by linarith) (one_lt_mul_tanh_neg hJ hw)

/-- **Georgii, after (12.35): `I(J, d)` is non-degenerate.** In the regime `J < -J(d)` the
antiferromagnetic critical field is strictly positive. -/
theorem antiferroCriticalField_pos (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|) :
    0 < antiferroCriticalField d J := by
  have h0 : treeField d J 0 = 0 := treeField_zero d J
  have := (strictMono_treeField_of_neg hJ d) (treeCriticalPoint_neg_pos hJ hw)
  rwa [h0] at this

/-! ### The derivative test -/

/-- The derivative of `φ_{-J}` is the negative of the derivative of `φ_J`. -/
theorem deriv_logCoshRatio_neg_left (J t : ℝ) :
    deriv (logCoshRatio (-J)) t = -deriv (logCoshRatio J) t := by
  rw [(hasDerivAt_logCoshRatio (-J) t).deriv, (hasDerivAt_logCoshRatio J t).deriv,
    show 2 * -J = -(2 * J) by ring, cosh_neg, sinh_neg, neg_div]

/-- **Georgii (12.29), read at the reflected coupling.** At the critical point `t_{-J,d}` the
slope of the recursion (12.22) has absolute value exactly `1`: `d φ_J'(t_{-J,d}) = -1`. -/
theorem mul_deriv_logCoshRatio_treeCriticalPoint (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|) :
    (d : ℝ) * deriv (logCoshRatio J) (treeCriticalPoint d (-J)) = -1 := by
  have h := deriv_treeField_treeCriticalPoint (J := -J) (d := d) (by linarith)
    (one_lt_mul_tanh_neg hJ hw)
  rw [deriv_treeField, deriv_logCoshRatio_neg_left] at h
  linarith

/-- Off the critical point the slope of the recursion is compared with `1` by comparing `|t|` with
`t_{-J,d}`: `(d φ_J'(t))² > 1` when `|t| < t_{-J,d}`. -/
theorem one_lt_sq_mul_deriv_logCoshRatio (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|) {t : ℝ}
    (ht : |t| < treeCriticalPoint d (-J)) :
    1 < ((d : ℝ) * deriv (logCoshRatio J) t) ^ 2 := by
  set p := treeCriticalPoint d (-J) with hp
  have hppos : 0 < p := treeCriticalPoint_neg_pos hJ hw
  have hsJ : sinh (2 * J) < 0 := sinh_neg_iff.2 (by linarith)
  have hcp : 0 < cosh (2 * t) + cosh (2 * J) := cosh_add_cosh_pos _ _
  have hcpp : 0 < cosh (2 * p) + cosh (2 * J) := cosh_add_cosh_pos _ _
  have hDt : deriv (logCoshRatio J) t = sinh (2 * J) / (cosh (2 * t) + cosh (2 * J)) :=
    (hasDerivAt_logCoshRatio J t).deriv
  have hDp : deriv (logCoshRatio J) p = sinh (2 * J) / (cosh (2 * p) + cosh (2 * J)) :=
    (hasDerivAt_logCoshRatio J p).deriv
  have hcosh : cosh (2 * t) < cosh (2 * p) := by
    refine cosh_lt_cosh.2 ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hppos]
    linarith
  have hlt : |deriv (logCoshRatio J) p| < |deriv (logCoshRatio J) t| := by
    rw [hDt, hDp, abs_div, abs_div, abs_of_pos hcp, abs_of_pos hcpp]
    exact div_lt_div_of_pos_left (abs_pos.2 hsJ.ne) hcp (by linarith)
  have hdpos : (0 : ℝ) < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp only [Nat.cast_zero, zero_mul] at hw; linarith
    · exact_mod_cast hd
  have hkey : |(d : ℝ) * deriv (logCoshRatio J) p| < |(d : ℝ) * deriv (logCoshRatio J) t| := by
    rw [abs_mul, abs_mul]
    exact mul_lt_mul_of_pos_left hlt (by rwa [abs_of_pos hdpos])
  rw [mul_deriv_logCoshRatio_treeCriticalPoint hJ hw] at hkey
  have habs1 : (1 : ℝ) < |(d : ℝ) * deriv (logCoshRatio J) t| := by simpa using hkey
  nlinarith [sq_abs ((d : ℝ) * deriv (logCoshRatio J) t), habs1]

/-! ### The second fixed point -/

/-- `ψ_{J,h,d} ≤ h + d |J|`, so `ψ_{J,h,d}(t) - t` is eventually negative. -/
theorem treeRecursion₂_le (d : ℕ) (J h t : ℝ) : treeRecursion₂ d J h t ≤ h + d * |J| := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 := (abs_le.1 (abs_logCoshRatio_le J (treeRecursion d J h t))).2
  rw [treeRecursion₂, treeRecursion]
  nlinarith

/-- **Georgii, after (12.35): the antiferromagnetic phase transition.** For `J < -J(d)` (i.e.
`1 < d |tanh J|`) and `|h| < ĥ(J, d)`, equation (12.35) has a solution which is *not* a solution
of (12.22); equivalently, there is a genuine alternating pair `t₀ ≠ t₁` satisfying (12.34). -/
theorem exists_isFixedPt_treeRecursion₂_ne (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|)
    (hh : |h| < antiferroCriticalField d J) :
    ∃ t : ℝ, treeRecursion₂ d J h t = t ∧ treeRecursion d J h t ≠ t := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_isFixedPt_treeRecursion_of_neg hJ d h
  have hufield : treeField d J u = h := treeRecursion_eq_self_iff.1 hu
  have hmono : StrictMono (treeField d J) := strictMono_treeField_of_neg hJ d
  -- Step 1: `|u| < t_{-J,d}`, because `treeField d J` is odd and strictly increasing.
  have habs : |u| < treeCriticalPoint d (-J) := by
    obtain ⟨hh₁, hh₂⟩ := abs_lt.1 hh
    rw [antiferroCriticalField] at hh₁ hh₂
    refine abs_lt.2 ⟨hmono.lt_iff_lt.1 ?_, hmono.lt_iff_lt.1 ?_⟩
    · rw [treeField_neg, hufield]; linarith
    · rw [hufield]; exact hh₂
  -- Step 2: the second iterate has slope `> 1` at its fixed point `u`.
  have hslope : 1 < (d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h u) *
      ((d : ℝ) * deriv (logCoshRatio J) u) := by
    rw [hu, ← sq]
    exact one_lt_sq_mul_deriv_logCoshRatio hJ hw habs
  -- Step 3: `F = ψ - id` vanishes at `u` with positive derivative, so `F > 0` just to the right.
  set F : ℝ → ℝ := fun t ↦ treeRecursion₂ d J h t - t with hFdef
  have hFu : F u = 0 := by rw [hFdef]; simp only [treeRecursion₂, hu, sub_self]
  have hFderiv : HasDerivAt F
      ((d : ℝ) * deriv (logCoshRatio J) (treeRecursion d J h u) *
        ((d : ℝ) * deriv (logCoshRatio J) u) - 1) u :=
    (hasDerivAt_treeRecursion₂ d J h u).sub (hasDerivAt_id u)
  obtain ⟨v, huv, hFv⟩ : ∃ v, u < v ∧ 0 < F v := by
    have htend := hasDerivAt_iff_tendsto_slope.1 hFderiv
    have hev : ∀ᶠ y in 𝓝[≠] u, 0 < slope F u y :=
      htend.eventually (eventually_gt_nhds (by linarith))
    have hev' : ∀ᶠ y in 𝓝[>] u, 0 < slope F u y :=
      hev.filter_mono (nhdsWithin_mono u fun x hx ↦ hx.ne')
    obtain ⟨v, hvslope, hvmem⟩ := (hev'.and self_mem_nhdsWithin).exists
    have hvu : (0 : ℝ) < v - u := sub_pos.2 hvmem
    refine ⟨v, hvmem, ?_⟩
    rw [slope_def_field, hFu, sub_zero] at hvslope
    rcases div_pos_iff.1 hvslope with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · linarith
  -- Step 4: `F` is negative far to the right, so the intermediate value theorem gives a zero.
  set T : ℝ := max v (h + d * |J|) + 1 with hT
  have hvT : v ≤ T := le_trans (le_max_left _ _) (by linarith)
  have hFT : F T < 0 := by
    have h1 : treeRecursion₂ d J h T ≤ h + d * |J| := treeRecursion₂_le d J h T
    have h2 : h + (d : ℝ) * |J| ≤ max v (h + d * |J|) := le_max_right _ _
    rw [hFdef]
    simp only
    rw [hT]
    linarith
  have hcont : ContinuousOn F (Icc v T) :=
    ((continuous_treeRecursion₂ d J h).sub continuous_id).continuousOn
  obtain ⟨t, htmem, ht0⟩ : ∃ t ∈ Icc v T, F t = 0 :=
    intermediate_value_Icc' hvT hcont ⟨hFT.le, hFv.le⟩
  refine ⟨t, by rw [hFdef] at ht0; simp only at ht0; linarith, fun hcon ↦ ?_⟩
  have : t = u := huniq t hcon
  exact absurd (this ▸ htmem.1) (not_le.2 huv)

end Real

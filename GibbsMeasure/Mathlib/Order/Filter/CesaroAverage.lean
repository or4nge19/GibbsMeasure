/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Finitely many exceptional terms do not affect a Cesàro limit

If a real function is bounded below by `K` outside a finite set `T`, then its Cesàro averages over
finite sets whose cardinalities tend to infinity are eventually at least `K - |T| B / |F k|`, where
`B` bounds the defect on `T`. Any limit of the averages is therefore at least `K`.

## Main results

* `Filter.le_of_tendsto_inv_card_sum_of_forall_notMem`, and its one-point special case
  `Filter.le_of_tendsto_inv_card_sum_of_forall_ne`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset

open scoped Topology

namespace Filter

variable {G : Type*} {F : ℕ → Finset G} {w : G → ℝ} {j : G} {T : Finset G} {K B L : ℝ}

/-- **Finitely many exceptional indices do not affect a Cesàro limit.** If `K ≤ w i` for every
`i ∉ T` and the defect `K - w i` on `T` is at most `B ≥ 0`, then any limit `L` of the averages
`|F k|⁻¹ ∑_{i ∈ F k} w i` along a sequence of finite sets with `|F k| → ∞` satisfies `K ≤ L`. -/
theorem le_of_tendsto_inv_card_sum_of_forall_notMem
    (hcard : Tendsto (fun k ↦ ((F k).card : ℝ)) atTop atTop) (hB : 0 ≤ B)
    (h : ∀ i, i ∉ T → K ≤ w i) (hT : ∀ i ∈ T, K - w i ≤ B)
    (hL : Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, w i) atTop (𝓝 L)) :
    K ≤ L := by
  classical
  have hpos : ∀ᶠ k in atTop, (0 : ℝ) < (F k).card := hcard.eventually_gt_atTop 0
  have hbound : ∀ᶠ k in atTop, K - (T.card * B) / (F k).card
      ≤ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, w i := by
    filter_upwards [hpos] with k hk
    have hsum : ∑ i ∈ F k, (if i ∈ T then -B else (0 : ℝ)) ≤ ∑ i ∈ F k, (w i - K) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      by_cases hiT : i ∈ T
      · rw [ite_eq_left hiT]; linarith [hT i hiT]
      · rw [ite_eq_right hiT]; linarith [h i hiT]
    have hleft : -((T.card : ℝ) * B) ≤ ∑ i ∈ F k, (if i ∈ T then -B else (0 : ℝ)) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hsub : ((F k).filter (fun i ↦ i ∈ T)) ⊆ T := fun i hi ↦ (Finset.mem_filter.1 hi).2
      have hle : ((((F k).filter (fun i ↦ i ∈ T)).card : ℝ)) ≤ T.card := by
        exact_mod_cast Finset.card_le_card hsub
      nlinarith
    have hsub : ∑ i ∈ F k, (w i - K) = (∑ i ∈ F k, w i) - (F k).card * K := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hfinal : ((F k).card : ℝ) * K - (T.card * B) ≤ ∑ i ∈ F k, w i := by
      rw [hsub] at hsum; linarith
    have h1 : ((F k).card : ℝ)⁻¹ * (((F k).card : ℝ) * K - (T.card * B))
        ≤ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, w i :=
      mul_le_mul_of_nonneg_left hfinal (by positivity)
    have h2 : ((F k).card : ℝ)⁻¹ * (((F k).card : ℝ) * K - (T.card * B))
        = K - (T.card * B) / (F k).card := by field_simp
    rwa [h2] at h1
  have hK : Tendsto (fun k ↦ K - ((T.card : ℝ) * B) / ((F k).card : ℝ)) atTop (𝓝 K) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hcard)
  exact le_of_tendsto_of_tendsto hK hL hbound

open scoped Classical in
/-- **A single exceptional index does not affect a Cesàro limit.** -/
theorem le_of_tendsto_inv_card_sum_of_forall_ne
    (hcard : Tendsto (fun k ↦ ((F k).card : ℝ)) atTop atTop) (hB : 0 ≤ B)
    (h : ∀ i, i ≠ j → K ≤ w i) (hj : K - w j ≤ B)
    (hL : Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, w i) atTop (𝓝 L)) :
    K ≤ L :=
  le_of_tendsto_inv_card_sum_of_forall_notMem (T := ({j} : Finset G)) hcard hB
    (fun i hi ↦ h i (by simpa using hi)) (fun i hi ↦ by
      rw [Finset.mem_singleton] at hi; subst hi; exact hj) hL

end Filter

end

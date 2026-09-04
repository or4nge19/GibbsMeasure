/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Limits and continuity in `EReal`

* `EReal.tendsto_of_le_add_coe`: a two-sided squeeze for `EReal`-valued limits.
* `EReal.continuous_div_natCast`: division by a positive natural number is continuous.
-/

@[expose] public section

open Filter
open scoped Topology

/-- **A two-sided squeeze for `EReal`-valued limits.** If `u j → a`, the real numbers `ε j` tend to
`0`, and each of `u j`, `v j` is at most the other plus `ε j`, then `v j → a`. No finiteness of `u`
or `v` is needed, only `v j ≠ ⊥`.
(Intended home: `Mathlib/Topology/Instances/EReal/Lemmas.lean`.) -/
lemma EReal.tendsto_of_le_add_coe {κ : Type*} {l : Filter κ} {u v : κ → EReal} {ε : κ → ℝ}
    {a : EReal} (hu : Tendsto u l (𝓝 a)) (hε : Tendsto ε l (𝓝 0))
    (hv : ∀ᶠ j in l, ⊥ < v j) (h₁ : ∀ᶠ j in l, v j ≤ u j + (ε j : EReal))
    (h₂ : ∀ᶠ j in l, u j ≤ v j + (ε j : EReal)) :
    Tendsto v l (𝓝 a) := by
  rw [tendsto_order] at hu ⊢
  refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- `b < a`: eventually `b < v j`
    rcases eq_or_ne b ⊥ with rfl | hbbot
    · filter_upwards [hv] with j hj using hj
    obtain ⟨c, hbc, hca⟩ := exists_between hb
    have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
    have hctop : c ≠ ⊤ := (hca.trans_le le_top).ne
    have hcbot : c ≠ ⊥ := ((bot_lt_iff_ne_bot.2 hbbot).trans hbc).ne'
    lift b to ℝ using ⟨hbtop, hbbot⟩
    lift c to ℝ using ⟨hctop, hcbot⟩
    have hbc' : b < c := by exact_mod_cast hbc
    filter_upwards [hu.1 c hca, (tendsto_order.1 hε).2 (c - b) (by linarith), h₂]
      with j hj hje hj2
    by_contra hcon
    rw [not_lt] at hcon
    have hstep : v j + (ε j : EReal) ≤ ((b + ε j : ℝ) : EReal) := by
      rw [EReal.coe_add]
      exact add_le_add hcon le_rfl
    have hlt : ((b + ε j : ℝ) : EReal) < (c : EReal) :=
      EReal.coe_lt_coe_iff.2 (by linarith)
    exact absurd ((hj.trans_le (hj2.trans hstep)).trans hlt) (lt_irrefl _)
  · -- `a < b`: eventually `v j < b`
    rcases eq_or_ne b ⊤ with rfl | hbtop
    · obtain ⟨c, hac, hct⟩ := exists_between hb
      filter_upwards [hu.2 c hac, h₁] with j hj hj1
      exact hj1.trans_lt (EReal.add_lt_top (hj.trans hct).ne (EReal.coe_ne_top _))
    obtain ⟨c, hac, hcb⟩ := exists_between hb
    have hcbot : c ≠ ⊥ := (bot_le.trans_lt hac).ne'
    have hctop : c ≠ ⊤ := (hcb.trans (lt_top_iff_ne_top.2 hbtop)).ne
    have hbbot : b ≠ ⊥ := ((bot_le.trans_lt hac).trans hcb).ne'
    lift b to ℝ using ⟨hbtop, hbbot⟩
    lift c to ℝ using ⟨hctop, hcbot⟩
    have hcb' : c < b := by exact_mod_cast hcb
    filter_upwards [hu.2 c hac, (tendsto_order.1 hε).2 (b - c) (by linarith), h₁]
      with j hj hje hj1
    refine hj1.trans_lt ?_
    calc u j + (ε j : EReal) < (c : EReal) + ((b - c : ℝ) : EReal) :=
          EReal.add_lt_add hj (EReal.coe_lt_coe_iff.2 hje)
      _ = (b : EReal) := by rw [← EReal.coe_add]; norm_num

/-- Division by a positive natural number is continuous on `EReal`. -/
lemma EReal.continuous_div_natCast {n : ℕ} (hn : n ≠ 0) :
    Continuous fun x : EReal ↦ x / (n : EReal) := by
  have hinv : ((n : EReal))⁻¹ ≠ 0 := by
    rw [← EReal.coe_natCast, ← EReal.coe_inv, Ne, EReal.coe_eq_zero]
    exact inv_ne_zero (Nat.cast_ne_zero.2 hn)
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (x, ((n : EReal))⁻¹) :=
    EReal.continuousAt_mul (Or.inr (EReal.bot_lt_inv _).ne') (Or.inr (EReal.inv_lt_top _).ne)
      (Or.inr hinv) (Or.inr hinv)
  exact hcont.comp (f := fun x : EReal ↦ (x, ((n : EReal))⁻¹))
    (continuous_id.prodMk continuous_const).continuousAt

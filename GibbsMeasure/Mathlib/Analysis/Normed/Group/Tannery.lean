/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Tannery's theorem for sums of growing length, and Scheffé's lemma for series

Two consequences of Tannery's theorem `tendsto_tsum_of_dominated_convergence`, holding along an
arbitrary filter. Intended home: `Mathlib/Analysis/Normed/Group/Tannery.lean`.

* `tendsto_finsetSum_of_dominated_convergence`, `tendsto_sum_range_of_dominated_convergence`:
  dominated convergence for finite sums `∑ b ∈ s a, f a b` over a family of finite sets `s a`
  that eventually contains every index, e.g. renewal series `∑_{k < n} f n k` whose length grows
  with the index.
* `tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum`: **Scheffé's lemma for series**: pointwise
  convergence of nonnegative summable families together with convergence of their sums gives
  convergence in `ℓ¹`. This is Scheffé's lemma for the counting measure, proved directly (as
  Mathlib does for Tannery's theorem) to avoid the countable-generation and integrability
  hypotheses of the measure-theoretic statement.
-/

@[expose] public section

open Filter Finset Set
open scoped Topology

variable {α β : Type*} {l : Filter α}

/-! ### Tannery's theorem for sums over a growing family of finite sets -/

/-- **Tannery's theorem for finite sums of growing length.** If the finite sets `s a` eventually
contain every index, `f a b → g b` for every `b`, and `‖f a b‖ ≤ bound b` for `b ∈ s a` with `bound`
summable, then `∑ b ∈ s a, f a b → ∑' b, g b`. This is the dominated convergence theorem for
renewal-type series `∑_{k < n} f n k` whose length grows with the index. -/
theorem tendsto_finsetSum_of_dominated_convergence {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] {s : α → Finset β} {f : α → β → G} {g : β → G} {bound : β → ℝ}
    (h_sum : Summable bound) (hs : ∀ b, ∀ᶠ a in l, b ∈ s a)
    (hab : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (h_bound : ∀ᶠ a in l, ∀ b ∈ s a, ‖f a b‖ ≤ bound b) :
    Tendsto (fun a ↦ ∑ b ∈ s a, f a b) l (𝓝 (∑' b, g b)) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hbound0 : ∀ b, 0 ≤ bound b := fun b ↦ by
    obtain ⟨a, ha, hb⟩ := ((hs b).and h_bound).exists
    exact (norm_nonneg _).trans (hb b ha)
  rw [show (fun a ↦ ∑ b ∈ s a, f a b) = fun a ↦ ∑' b, (↑(s a) : Set β).indicator (f a) b from
    funext fun a ↦ sum_eq_tsum_indicator _ _]
  refine tendsto_tsum_of_dominated_convergence h_sum (fun b ↦ (hab b).congr' ?_) ?_
  · filter_upwards [hs b] with a ha
    exact (indicator_of_mem (Finset.mem_coe.2 ha) _).symm
  · filter_upwards [h_bound] with a ha b
    by_cases hb : b ∈ s a
    · rw [indicator_of_mem (Finset.mem_coe.2 hb)]; exact ha b hb
    · rw [indicator_of_notMem (Finset.mem_coe.not.2 hb), norm_zero]; exact hbound0 b

/-- Tannery's theorem for `∑ k ∈ range n, f n k`: if `f n k → g k` for every `k` and
`‖f n k‖ ≤ bound k` for `k < n` with `bound` summable, then `∑ k < n, f n k → ∑' k, g k`. -/
theorem tendsto_sum_range_of_dominated_convergence {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] {f : ℕ → ℕ → G} {g : ℕ → G} {bound : ℕ → ℝ} (h_sum : Summable bound)
    (hab : ∀ k, Tendsto (f · k) atTop (𝓝 (g k)))
    (h_bound : ∀ᶠ n in atTop, ∀ k < n, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∑ k ∈ range n, f n k) atTop (𝓝 (∑' k, g k)) :=
  tendsto_finsetSum_of_dominated_convergence h_sum (fun k ↦ by
    simpa using eventually_gt_atTop k) hab (by simpa using h_bound)

/-! ### Scheffé's lemma for series -/

/-- **Scheffé's lemma for series.** If nonnegative summable families `f a` converge pointwise to a
nonnegative summable `g`, and their sums converge to the sum of `g`, then `f a → g` in `ℓ¹`:
`∑' b, |f a b - g b| → 0`.

This is Scheffé's lemma for the counting measure; like Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`), from which it is deduced, it holds along an arbitrary
filter. The proof writes `|f - g| = 2 (g - f)⁺ + (f - g)`: the first term is dominated by `g`. -/
theorem tendsto_tsum_abs_sub_of_tendsto_of_tendsto_tsum {f : α → β → ℝ} {g : β → ℝ}
    (hf : ∀ᶠ a in l, ∀ b, 0 ≤ f a b) (hg : ∀ b, 0 ≤ g b)
    (hfs : ∀ᶠ a in l, Summable (f a)) (hgs : Summable g)
    (h : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (hsum : Tendsto (fun a ↦ ∑' b, f a b) l (𝓝 (∑' b, g b))) :
    Tendsto (fun a ↦ ∑' b, |f a b - g b|) l (𝓝 0) := by
  -- the positive parts `(g - f a)⁺` are dominated by `g` and tend to `0` pointwise
  have hpos : Tendsto (fun a ↦ ∑' b, max (g b - f a b) 0) l (𝓝 0) := by
    have hb : ∀ b, Tendsto (fun a ↦ max (g b - f a b) 0) l (𝓝 0) := fun b ↦ by
      simpa using ((tendsto_const_nhds (x := g b)).sub (h b)).max
        (tendsto_const_nhds (x := (0 : ℝ)))
    have := tendsto_tsum_of_dominated_convergence (𝓕 := l) (f := fun a b ↦ max (g b - f a b) 0)
      (g := fun _ ↦ 0) (bound := g) hgs hb ?_
    · simpa using this
    · filter_upwards [hf] with a ha b
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [ha b]) (hg b)
  have hid : ∀ a, (∀ b, 0 ≤ f a b) → Summable (f a) →
      ∑' b, |f a b - g b| = 2 * ∑' b, max (g b - f a b) 0 + (∑' b, f a b - ∑' b, g b) := by
    intro a ha hs
    have hmax : Summable fun b ↦ max (g b - f a b) 0 :=
      hgs.of_nonneg_of_le (fun b ↦ le_max_right _ _) fun b ↦ max_le (by linarith [ha b]) (hg b)
    rw [← tsum_mul_left, ← hs.tsum_sub hgs, ← (hmax.mul_left 2).tsum_add (hs.sub hgs)]
    refine tsum_congr fun b ↦ ?_
    rcases le_total (g b) (f a b) with hle | hle
    · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
  have : Tendsto (fun a ↦ 2 * ∑' b, max (g b - f a b) 0 + (∑' b, f a b - ∑' b, g b)) l (𝓝 0) := by
    simpa using (hpos.const_mul 2).add (hsum.sub_const (∑' b, g b))
  refine this.congr' ?_
  filter_upwards [hf, hfs] with a ha hs
  exact (hid a ha hs).symm

end

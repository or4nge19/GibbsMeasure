/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Basic.Real.ENatENNReal
public import GibbsMeasure.Mathlib.Analysis.Normed.Group.Tannery

/-!
# Fibrewise summation, subtraction, `ENNReal.ofReal`-summability, and Tannery's theorem in `ℝ≥0∞`

Besides the fibrewise and subtraction identities, this file contains the two forms of dominated
convergence for `ℝ≥0∞`-valued series that `ℝ≥0∞`'s failure to be a normed group puts out of
reach of `tendsto_tsum_of_dominated_convergence`:
`ENNReal.tendsto_finsetSum_of_dominated_convergence` (Tannery for sums over a growing family of
finite sets) and `ENNReal.tendsto_tsum_mul_of_tendsto` (`∑_j A k j w j → 0` for uniformly bounded
weights vanishing pointwise), together with the tail-splitting lemmas
`ENNReal.tsum_le_card_mul_add`, `ENNReal.tsum_ite_compl_eq` and
`ENNReal.exists_tsum_ite_compl_le` behind the latter.
-/

@[expose] public section

open scoped ENNReal

/-- Summing `g ∘ f` fiberwise: `∑' a, g (f a) = ∑' b, |f⁻¹{b}| g b` in `ℝ≥0∞`. Intended home:
`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`. -/
theorem ENNReal.tsum_comp_eq_tsum_encard_preimage_mul {α β : Type*} (f : α → β) (g : β → ℝ≥0∞) :
    ∑' a, g (f a) = ∑' b, ((f ⁻¹' {b}).encard : ℝ≥0∞) * g b := by
  rw [← (Equiv.sigmaFiberEquiv f).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun b ↦ ?_
  rw [← ENNReal.tsum_set_const]
  exact tsum_congr fun x ↦ by simp [Equiv.sigmaFiberEquiv, x.2]

/-- Subtraction of `ℝ≥0∞`-valued sums, general index (Mathlib's `ENNReal.tsum_sub` is stated for
`ℕ`): if `g ≤ f` pointwise and `∑ g < ∞`, then `∑ (f - g) = ∑ f - ∑ g`. -/
lemma ENNReal.tsum_tsub {ι : Type*} {f g : ι → ℝ≥0∞} (hfg : ∀ i, g i ≤ f i)
    (hg : ∑' i, g i ≠ ⊤) : ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i := by
  refine ENNReal.eq_sub_of_add_eq hg ?_
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun i ↦ tsub_add_cancel_of_le (hfg i)

/-- A nonnegative real family is summable iff its `ENNReal.ofReal`-series is finite: the converse
of `Summable.tsum_ofReal_ne_top`, which needs no sign condition. -/
theorem ENNReal.tsum_ofReal_ne_top_iff_summable {α : Type*} {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑' a, ENNReal.ofReal (f a) ≠ ∞ ↔ Summable f := by
  refine ⟨fun h ↦ ?_, Summable.tsum_ofReal_ne_top⟩
  refine (summable_congr fun a ↦ ?_).1 (ENNReal.summable_toReal h)
  exact ENNReal.toReal_ofReal (hf a)

/-! ### Tannery's theorem for sums over a growing family of finite sets, in `ℝ≥0∞` -/

section Tannery

open Filter Finset
open scoped Topology

variable {α β : Type*} {l : Filter α}

/-- **Tannery's theorem for finite sums of growing length**, in `ℝ≥0∞`: if the finite sets `s a`
eventually contain every index, `f a b → g b` for every `b`, and `f a b ≤ bound b` for `b ∈ s a`
with `∑' b, bound b < ∞`, then `∑ b ∈ s a, f a b → ∑' b, g b`. -/
theorem ENNReal.tendsto_finsetSum_of_dominated_convergence {s : α → Finset β}
    {f : α → β → ℝ≥0∞} {g : β → ℝ≥0∞} {bound : β → ℝ≥0∞} (h_sum : ∑' b, bound b ≠ ∞)
    (hs : ∀ b, ∀ᶠ a in l, b ∈ s a) (hab : ∀ b, Tendsto (f · b) l (𝓝 (g b)))
    (h_bound : ∀ᶠ a in l, ∀ b ∈ s a, f a b ≤ bound b) :
    Tendsto (fun a ↦ ∑ b ∈ s a, f a b) l (𝓝 (∑' b, g b)) := by
  rcases l.eq_or_neBot with rfl | _
  · simp
  have hbt : ∀ b, bound b ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top h_sum
  have hgb : ∀ b, g b ≤ bound b := fun b ↦
    le_of_tendsto (hab b) <| by filter_upwards [hs b, h_bound] with a ha hb using hb b ha
  have hgt : ∀ b, g b ≠ ∞ := fun b ↦ ne_top_of_le_ne_top (hbt b) (hgb b)
  have hgs : ∑' b, g b ≠ ∞ := ne_top_of_le_ne_top h_sum (ENNReal.tsum_le_tsum hgb)
  have hreal : Tendsto (fun a ↦ ∑ b ∈ s a, (f a b).toReal) l (𝓝 (∑' b, (g b).toReal)) := by
    refine _root_.tendsto_finsetSum_of_dominated_convergence (bound := fun b ↦ (bound b).toReal)
      (ENNReal.summable_toReal h_sum) hs
      (fun b ↦ (ENNReal.tendsto_toReal (hgt b)).comp (hab b)) ?_
    filter_upwards [h_bound] with a ha b hb
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (hbt b) (ha b hb)
  rw [← ENNReal.ofReal_toReal hgs, ENNReal.tsum_toReal_eq hgt]
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [h_bound] with a ha
  rw [← ENNReal.toReal_sum fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb),
    ENNReal.ofReal_toReal (ENNReal.sum_ne_top.2 fun b hb ↦ ne_top_of_le_ne_top (hbt b) (ha b hb))]

/-- Tannery's theorem for `∑ k ∈ range n, f n k` in `ℝ≥0∞`: if `f n k → g k` for every `k` and
`f n k ≤ bound k` for `k < n` with `∑' k, bound k < ∞`, then `∑ k < n, f n k → ∑' k, g k`. -/
theorem ENNReal.tendsto_sum_range_of_dominated_convergence {f : ℕ → ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞}
    {bound : ℕ → ℝ≥0∞} (h_sum : ∑' k, bound k ≠ ∞) (hab : ∀ k, Tendsto (f · k) atTop (𝓝 (g k)))
    (h_bound : ∀ᶠ n in atTop, ∀ k < n, f n k ≤ bound k) :
    Tendsto (fun n ↦ ∑ k ∈ range n, f n k) atTop (𝓝 (∑' k, g k)) :=
  ENNReal.tendsto_finsetSum_of_dominated_convergence h_sum (fun k ↦ by
    simpa using eventually_gt_atTop k) hab (by simpa using h_bound)

end Tannery


/-! ### Splitting a `tsum` at a finite set, and dominated convergence for `ℝ≥0∞` series -/

section DominatedConvergence

open Filter
open scoped Topology

namespace ENNReal

/-- Splitting a `tsum` at a finite set: the terms indexed by `J` are bounded by `δ`, the others
by `h`. -/
lemma tsum_le_card_mul_add {ι : Type*} [DecidableEq ι] (g h : ι → ℝ≥0∞) (J : Finset ι)
    (δ : ℝ≥0∞)
    (h1 : ∀ j ∈ J, g j ≤ δ) (h2 : ∀ j, j ∉ J → g j ≤ h j) :
    ∑' j, g j ≤ J.card * δ + ∑' j, (if j ∈ J then 0 else h j) := by
  classical
  have hstep : ∀ j, g j ≤ (if j ∈ J then δ else 0) + (if j ∈ J then 0 else h j) := by
    intro j
    by_cases hj : j ∈ J
    · simpa [hj] using h1 j hj
    · simpa [hj] using h2 j hj
  have hsum : ∑ j ∈ J, (if j ∈ J then δ else 0) = ∑ _j ∈ J, δ :=
    Finset.sum_congr rfl fun j hj ↦ by simp [hj]
  calc ∑' j, g j ≤ ∑' j, ((if j ∈ J then δ else 0) + (if j ∈ J then 0 else h j)) :=
        ENNReal.tsum_le_tsum hstep
    _ = (∑' j, if j ∈ J then δ else 0) + ∑' j, (if j ∈ J then 0 else h j) := ENNReal.tsum_add
    _ = J.card * δ + ∑' j, (if j ∈ J then 0 else h j) := by
        congr 1
        rw [tsum_eq_sum (s := J) fun b hb ↦ by simp [hb], hsum, Finset.sum_const, nsmul_eq_mul]

lemma tsum_ite_compl_eq {ι : Type*} [DecidableEq ι] (f : ι → ℝ≥0∞) (J : Finset ι) :
    ∑' j, (if j ∈ J then 0 else f j) = ∑' j : {x : ι // x ∉ J}, f j := by
  have hsub : ∑' j : {x : ι // x ∉ J}, f j = ∑' j, Set.indicator {x : ι | x ∉ J} f j :=
    tsum_subtype {x : ι | x ∉ J} f
  rw [hsub]
  exact tsum_congr fun j ↦ by by_cases hj : j ∈ J <;> simp [hj]

/-- The tail of a finite `ℝ≥0∞`-valued sum can be made arbitrarily small. -/
lemma exists_tsum_ite_compl_le {ι : Type*} [DecidableEq ι] {f : ι → ℝ≥0∞}
    (hf : ∑' j, f j ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ J : Finset ι, ∑' j, (if j ∈ J then 0 else f j) ≤ ε := by
  have h := ENNReal.tendsto_tsum_compl_atTop_zero hf
  rw [ENNReal.tendsto_nhds_zero] at h
  obtain ⟨J, hJ⟩ := (h ε hε).exists
  exact ⟨J, by rw [tsum_ite_compl_eq]; exact hJ⟩

/-- **Dominated convergence for `ℝ≥0∞`-valued series.** If the weights `A k j` are bounded by a
finite `M`, converge to `0` along `l` for each fixed `j`, and `w` is summable, then
`∑_j A k j w j → 0`: the terms with `j` outside a large finite set are controlled by the tail of
`∑_j w_j`, the finitely many remaining ones by the pointwise convergence.

This is the `ℝ≥0∞` analogue of Tannery's theorem `tendsto_tsum_of_dominated_convergence`, which
does not apply because `ℝ≥0∞` is not a normed group. -/
theorem tendsto_tsum_mul_of_tendsto {ι κ : Type*} {l : Filter κ}
    {A : κ → ι → ℝ≥0∞} {w : ι → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hA : ∀ k j, A k j ≤ M) (h0 : ∀ j, Tendsto (fun k ↦ A k j) l (𝓝 0))
    (hw : ∑' j, w j ≠ ⊤) :
    Tendsto (fun k ↦ ∑' j, A k j * w j) l (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hSw1 : (∑' j, w j) + 1 ≠ ⊤ := by
    rw [Ne, ENNReal.add_eq_top]
    simp [hw]
  obtain ⟨J, hJ⟩ := exists_tsum_ite_compl_le hw (ε := ε / 2 / (M + 1))
    (ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp [hM]))
  set δ : ℝ≥0∞ := ε / 2 / (J.card + 1) with hδ
  have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.half_pos hε.ne').ne' (by simp)
  set η : ℝ≥0∞ := δ / ((∑' j, w j) + 1) with hη
  have hηpos : 0 < η := ENNReal.div_pos hδpos.ne' hSw1
  have hev : ∀ᶠ k in l, ∀ j ∈ J, A k j ≤ η := by
    rw [Filter.eventually_all_finset]
    exact fun j _ ↦ (ENNReal.tendsto_nhds_zero.1 (h0 j)) η hηpos
  filter_upwards [hev] with k hk
  have hsmall : ∀ j ∈ J, A k j * w j ≤ δ := by
    intro j hj
    have h1 : A k j * w j ≤ η * ∑' j, w j :=
      mul_le_mul' (hk j hj) (ENNReal.le_tsum j)
    have h2 : η * (∑' j, w j) ≤ δ := by
      refine (mul_le_mul' (le_refl η) (le_self_add (b := (1 : ℝ≥0∞)))).trans ?_
      rw [hη, ENNReal.div_mul_cancel (by simp) hSw1]
    exact h1.trans h2
  have hcard : (J.card : ℝ≥0∞) * δ ≤ ε / 2 := by
    calc (J.card : ℝ≥0∞) * δ ≤ ((J.card : ℝ≥0∞) + 1) * δ := by gcongr; exact le_self_add
      _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp)
  have htail : ∑' j, (if j ∈ J then 0 else M * w j) ≤ ε / 2 := by
    calc ∑' j, (if j ∈ J then 0 else M * w j)
        = M * ∑' j, (if j ∈ J then 0 else w j) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun j ↦ by by_cases hj : j ∈ J <;> simp [hj]
      _ ≤ (M + 1) * (ε / 2 / (M + 1)) := mul_le_mul' le_self_add hJ
      _ = ε / 2 := ENNReal.mul_div_cancel' (by simp) (by simp [hM])
  calc ∑' j, A k j * w j
      ≤ (J.card : ℝ≥0∞) * δ + ∑' j, (if j ∈ J then 0 else M * w j) :=
        tsum_le_card_mul_add _ _ J δ hsmall fun j _ ↦ mul_le_mul' (hA k j) le_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add hcard htail
    _ = ε := ENNReal.add_halves ε

end ENNReal

end DominatedConvergence

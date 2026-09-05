/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Cesàro (Fejér) box averages of a summable function on `ℤ ^ ι`

For a finite index type `ι` write `Λ L := {0, …, L - 1} ^ ι ⊆ (ι → ℤ)` for the discrete box of
side `L`, that is, `Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (L : ℤ)`.

Given a summable `R : (ι → ℤ) → ℝ`, the doubly indexed average
`|Λ L|⁻¹ * ∑ a ∈ Λ L, ∑ b ∈ Λ L, R (a - b)` is the Fejér (Cesàro) average of `R` along the
Følner sequence `Λ L`. It converges to the total sum `∑' s, R s`: for `a` in the inner box
`[A, L - 1 - A] ^ ι` the differences `a - b`, `b ∈ Λ L`, exhaust the cube `[-A, A] ^ ι`, so the
inner sum is a partial sum of `R` over a large finite set; and the inner box occupies a fraction
`(1 - 2 * A / L) ^ Fintype.card ι → 1` of `Λ L`, so the boundary layer is asymptotically
negligible.

## Main results

* `Fintype.card_piFinset_Ico_zero`: the box `{0, …, L - 1} ^ ι` has `L ^ Fintype.card ι` elements.
* `Summable.tendsto_boxAverage_sub`: for summable `R : (ι → ℤ) → ℝ`, the box averages
  `((L : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a ∈ Λ L, ∑ b ∈ Λ L, R (a - b)` converge to `∑' s, R s`
  as `L → ∞`.
-/

@[expose] public section

open Filter Finset Topology

/-- The discrete box `{0, …, L - 1} ^ ι` has `L ^ Fintype.card ι` elements. -/
theorem Fintype.card_piFinset_Ico_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (L : ℕ) :
    #(Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (L : ℤ)) = L ^ Fintype.card ι := by
  simp

namespace Summable

/-- Reindexing along the bijection `b ↦ a - b` turns a sum of `R (a - b)` over a finite set of
`b`'s into a partial sum of `R` itself. -/
private theorem sum_sub_left_eq_sum_image {α : Type*} [AddGroup α] [DecidableEq α] {R : α → ℝ}
    (a : α) (T : Finset α) : ∑ b ∈ T, R (a - b) = ∑ s ∈ T.image (a - ·), R s :=
  (Finset.sum_image sub_right_injective.injOn).symm

/-- Any finite sum of translates of `R` is dominated by the total absolute sum. -/
private theorem abs_sum_sub_le_tsum_abs {α : Type*} [AddGroup α] {R : α → ℝ} (hR : Summable R)
    (a : α) (T : Finset α) : |∑ b ∈ T, R (a - b)| ≤ ∑' s, |R s| := by
  classical
  rw [sum_sub_left_eq_sum_image]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (hR.abs.sum_le_tsum _ fun _ _ ↦ abs_nonneg _)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : (ι → ℤ) → ℝ}

/-- The quantitative heart of `Summable.tendsto_boxAverage_sub`.

Suppose the partial sums of `R` over every finite superset of `F₀` are within `ε` of `∑' s, R s`,
and that `F₀` is contained in the cube `[-A, A] ^ ι`. If `2 * A ≤ L` then for every `a` in the
inner box `good = [A, L - 1 - A] ^ ι` the image `a - box` contains `F₀`, so the inner sum is
within `ε` of the total sum; for the remaining `a` the inner sum is only known to be bounded by
`∑' s, |R s|`. The inner box occupies a fraction `(1 - 2 * A / L) ^ Fintype.card ι` of `box`,
whence the stated bound. -/
private theorem abs_boxAverage_sub_le (hR : Summable R) {ε : ℝ} {F₀ : Finset (ι → ℤ)}
    (hF₀ : ∀ F : Finset (ι → ℤ), F₀ ⊆ F → |(∑ s ∈ F, R s) - ∑' s, R s| ≤ ε) (hε : 0 ≤ ε)
    {A : ℕ} (hA : ∀ s ∈ F₀, ∀ c : ι, -(A : ℤ) ≤ s c ∧ s c ≤ (A : ℤ))
    {L : ℕ} (hAL : 2 * A ≤ L) (hL : 0 < L) {box good : Finset (ι → ℤ)}
    (hbox : box = Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (L : ℤ))
    (hgood : good = Fintype.piFinset fun _ : ι ↦ Finset.Icc (A : ℤ) ((L : ℤ) - 1 - A)) :
    |((L : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a ∈ box, ∑ b ∈ box, R (a - b) - ∑' s, R s| ≤
      ε + (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) * (∑' s, |R s| + |∑' s, R s|) := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hLm : (0 : ℝ) < (L : ℝ) ^ Fintype.card ι := by positivity
  have hmul : ((L : ℝ) ^ Fintype.card ι)⁻¹ * (L : ℝ) ^ Fintype.card ι = 1 :=
    inv_mul_cancel₀ hLm.ne'
  -- Cardinalities of the two boxes.
  have hcb : (#box : ℝ) = (L : ℝ) ^ Fintype.card ι := by
    rw [hbox, Fintype.card_piFinset_Ico_zero]; push_cast; ring
  have hIcc : #(Finset.Icc (A : ℤ) ((L : ℤ) - 1 - A)) = L - 2 * A := by
    rw [Int.card_Icc]; omega
  have hcgnat : #good = (L - 2 * A) ^ Fintype.card ι := by
    simp [hgood, Fintype.card_piFinset, hIcc]
  have hcg : (#good : ℝ) = ((L : ℝ) - 2 * A) ^ Fintype.card ι := by
    rw [hcgnat, Nat.cast_pow, Nat.cast_sub hAL]; push_cast; ring
  -- The inner box sits inside the box.
  have hsub : good ⊆ box := by
    rw [hgood, hbox]
    intro a ha
    rw [Fintype.mem_piFinset] at ha ⊢
    intro c
    have hac := ha c
    rw [Finset.mem_Icc] at hac
    rw [Finset.mem_Ico]
    omega
  -- A crude bound valid for every `a`, and the sharp bound on the inner box.
  have hall : ∀ a : ι → ℤ, |(∑ b ∈ box, R (a - b)) - ∑' s, R s| ≤
      ∑' s, |R s| + |∑' s, R s| := fun a ↦ by
    calc |(∑ b ∈ box, R (a - b)) - ∑' s, R s| ≤ |∑ b ∈ box, R (a - b)| + |∑' s, R s| := by
          simpa [sub_eq_add_neg] using abs_add_le (∑ b ∈ box, R (a - b)) (-∑' s, R s)
      _ ≤ ∑' s, |R s| + |∑' s, R s| := by gcongr; exact abs_sum_sub_le_tsum_abs hR a box
  have hgoodbd : ∀ a ∈ good, |(∑ b ∈ box, R (a - b)) - ∑' s, R s| ≤ ε := by
    intro a ha
    rw [hgood, Fintype.mem_piFinset] at ha
    rw [sum_sub_left_eq_sum_image]
    refine hF₀ _ fun s hs ↦ ?_
    rw [Finset.mem_image]
    refine ⟨a - s, ?_, sub_sub_cancel a s⟩
    rw [hbox, Fintype.mem_piFinset]
    intro c
    have h1 := ha c
    rw [Finset.mem_Icc] at h1
    have h2 := hA s hs c
    rw [Finset.mem_Ico]
    simp only [Pi.sub_apply]
    omega
  -- Recentre the average.
  have hkey : ((L : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a ∈ box, ∑ b ∈ box, R (a - b) - ∑' s, R s =
      ((L : ℝ) ^ Fintype.card ι)⁻¹ * ∑ a ∈ box, ((∑ b ∈ box, R (a - b)) - ∑' s, R s) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcb, mul_sub,
      inv_mul_cancel_left₀ hLm.ne']
  -- Split the average over the inner box and its complement.
  have hbound : |∑ a ∈ box, ((∑ b ∈ box, R (a - b)) - ∑' s, R s)| ≤
      (#good : ℝ) * ε + ((#box : ℝ) - #good) * (∑' s, |R s| + |∑' s, R s|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← Finset.sum_sdiff hsub]
    have h1 : ∑ a ∈ box \ good, |(∑ b ∈ box, R (a - b)) - ∑' s, R s| ≤
        (#(box \ good) : ℝ) * (∑' s, |R s| + |∑' s, R s|) := by
      have h := Finset.sum_le_card_nsmul (box \ good)
        (fun a ↦ |(∑ b ∈ box, R (a - b)) - ∑' s, R s|) (∑' s, |R s| + |∑' s, R s|)
        fun a _ ↦ hall a
      rwa [nsmul_eq_mul] at h
    have h2 : ∑ a ∈ good, |(∑ b ∈ box, R (a - b)) - ∑' s, R s| ≤ (#good : ℝ) * ε := by
      have h := Finset.sum_le_card_nsmul good
        (fun a ↦ |(∑ b ∈ box, R (a - b)) - ∑' s, R s|) ε hgoodbd
      rwa [nsmul_eq_mul] at h
    have h3 : (#(box \ good) : ℝ) = (#box : ℝ) - #good := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [h3] at h1
    linarith
  -- The fraction of `box` occupied by the inner box.
  have hq0 : (0 : ℝ) ≤ 1 - 2 * (A : ℝ) / L := by
    rw [sub_nonneg, div_le_one hLR]
    exact_mod_cast hAL
  have hq1 : 1 - 2 * (A : ℝ) / L ≤ 1 := by
    have : (0 : ℝ) ≤ 2 * (A : ℝ) / L := by positivity
    linarith
  have hqpow : (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι ≤ 1 := pow_le_one₀ hq0 hq1
  have hqeq : (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι =
      ((L : ℝ) ^ Fintype.card ι)⁻¹ * ((L : ℝ) - 2 * A) ^ Fintype.card ι := by
    have h : 1 - 2 * (A : ℝ) / L = ((L : ℝ) - 2 * A) / L := by field_simp
    rw [h, div_pow]; ring
  rw [hkey, abs_mul, abs_of_nonneg (inv_nonneg.2 hLm.le)]
  calc ((L : ℝ) ^ Fintype.card ι)⁻¹ * |∑ a ∈ box, ((∑ b ∈ box, R (a - b)) - ∑' s, R s)|
      ≤ ((L : ℝ) ^ Fintype.card ι)⁻¹ *
          ((#good : ℝ) * ε + ((#box : ℝ) - #good) * (∑' s, |R s| + |∑' s, R s|)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hLm.le)
    _ = ((L : ℝ) ^ Fintype.card ι)⁻¹ * ((L : ℝ) - 2 * A) ^ Fintype.card ι * ε +
          (((L : ℝ) ^ Fintype.card ι)⁻¹ * (L : ℝ) ^ Fintype.card ι -
            ((L : ℝ) ^ Fintype.card ι)⁻¹ * ((L : ℝ) - 2 * A) ^ Fintype.card ι) *
            (∑' s, |R s| + |∑' s, R s|) := by
        rw [hcb, hcg]; ring
    _ = (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι * ε +
          (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) * (∑' s, |R s| + |∑' s, R s|) := by
        rw [hmul, hqeq]
    _ ≤ ε + (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) * (∑' s, |R s| + |∑' s, R s|) := by
        have := mul_le_of_le_one_left hε hqpow
        linarith

end Summable

/-- **Cesàro (Fejér) box averages of a summable function on `ℤ^ι`.** -/
theorem Summable.tendsto_boxAverage_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : (ι → ℤ) → ℝ} (hR : Summable R) :
    Filter.Tendsto
      (fun L : ℕ ↦ ((L : ℝ) ^ Fintype.card ι)⁻¹ *
        ∑ a ∈ Fintype.piFinset (fun _ : ι ↦ Finset.Ico (0 : ℤ) (L : ℤ)),
          ∑ b ∈ Fintype.piFinset (fun _ : ι ↦ Finset.Ico (0 : ℤ) (L : ℤ)), R (a - b))
      Filter.atTop (nhds (∑' s, R s)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- A finite set `F₀` all of whose finite supersets have partial sum within `ε / 2` of `∑' s, R s`.
  have h1 : Filter.Tendsto (fun F : Finset (ι → ℤ) ↦ ∑ s ∈ F, R s) Filter.atTop
      (nhds (∑' s, R s)) := hR.hasSum
  have hnhds : ∀ᶠ y : ℝ in nhds (∑' s, R s), |y - ∑' s, R s| ≤ ε / 2 := by
    filter_upwards [Metric.closedBall_mem_nhds (∑' s, R s) (by positivity : (0 : ℝ) < ε / 2)]
      with y hy
    rwa [Metric.mem_closedBall, Real.dist_eq] at hy
  obtain ⟨F₀, hF₀⟩ := Filter.eventually_atTop.1 (h1.eventually hnhds)
  -- `F₀` is contained in the cube `[-A, A] ^ ι`.
  obtain ⟨A, hA⟩ : ∃ A : ℕ, ∀ s ∈ F₀, ∀ c : ι, -(A : ℤ) ≤ s c ∧ s c ≤ (A : ℤ) := by
    refine ⟨F₀.sup fun s ↦ Finset.univ.sup fun c ↦ (s c).natAbs, fun s hs c ↦ ?_⟩
    have h : (s c).natAbs ≤ F₀.sup fun s ↦ Finset.univ.sup fun c ↦ (s c).natAbs :=
      (Finset.le_sup (f := fun c ↦ (s c).natAbs) (Finset.mem_univ c)).trans
        (Finset.le_sup (f := fun s : ι → ℤ ↦ Finset.univ.sup fun c ↦ (s c).natAbs) hs)
    omega
  -- The boundary correction is asymptotically negligible.
  have hlim : Filter.Tendsto (fun L : ℕ ↦ (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) *
      (∑' s, |R s| + |∑' s, R s|)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun L : ℕ ↦ 2 * (A : ℝ) / L) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have h3 : Filter.Tendsto (fun L : ℕ ↦ (1 : ℝ) - 2 * (A : ℝ) / L) Filter.atTop
        (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h0
    have h4 : Filter.Tendsto (fun L : ℕ ↦ (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) *
        (∑' s, |R s| + |∑' s, R s|)) Filter.atTop
        (nhds ((1 - ((1 : ℝ) - 0) ^ Fintype.card ι) * (∑' s, |R s| + |∑' s, R s|))) :=
      (tendsto_const_nhds.sub (h3.pow (Fintype.card ι))).mul_const _
    simpa using h4
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N₁, hN₁⟩ := hlim (ε / 2) (by positivity)
  refine ⟨max N₁ (max (2 * A) 1), fun L hL ↦ ?_⟩
  have hLN₁ : N₁ ≤ L := (le_max_left _ _).trans hL
  have hLA : 2 * A ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hL1 : 1 ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hL0 : 0 < L := hL1
  have hcorr : (1 - (1 - 2 * (A : ℝ) / L) ^ Fintype.card ι) * (∑' s, |R s| + |∑' s, R s|) <
      ε / 2 := by
    have h4 := hN₁ L hLN₁
    rw [Real.dist_eq, sub_zero] at h4
    exact (le_abs_self _).trans_lt h4
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (Summable.abs_boxAverage_sub_le hR (fun F hF ↦ hF₀ F hF)
    (by positivity) hA hLA hL0 rfl rfl) ?_
  linarith

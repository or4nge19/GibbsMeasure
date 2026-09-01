/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Uniform averages of a finite family of measures

`uniformAverage m F = |F|⁻¹ ∑_{i ∈ F} m i`, with the symmetric-difference estimates that drive
averaging arguments over Følner-type families: two uniform averages of probability measures differ
on every event by at most `|F ∆ F'|/|F| + ||F'|/|F| − 1|`, with the two specialisations for
`|F| = |F'|` and for `F' ⊆ F`.
-/

@[expose] public section

open scoped ENNReal symmDiff

noncomputable section

namespace MeasureTheory

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-! ### Uniform averages of a finite family of measures -/

/-- The uniform average `|F|⁻¹ ∑_{i ∈ F} m i` of a family of measures over a finite index set. -/
def uniformAverage (m : ι → Measure Ω) (F : Finset ι) : Measure Ω :=
  (F.card : ℝ≥0∞)⁻¹ • ∑ i ∈ F, m i

lemma uniformAverage_apply (m : ι → Measure Ω) (F : Finset ι) (A : Set Ω) :
    uniformAverage m F A = (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, m i A := by
  simp only [uniformAverage, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

lemma isProbabilityMeasure_uniformAverage (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F : Finset ι} (hF : F.Nonempty) :
    IsProbabilityMeasure (uniformAverage m F) := by
  constructor
  rw [uniformAverage_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ (hm i).measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hF.card_pos.ne') (ENNReal.natCast_ne_top _)

lemma uniformAverage_real_apply (m : ι → Measure Ω) (hm : ∀ i, IsProbabilityMeasure (m i))
    (F : Finset ι) (A : Set Ω) :
    (uniformAverage m F).real A = (F.card : ℝ)⁻¹ * ∑ i ∈ F, (m i).real A := by
  rw [measureReal_def, uniformAverage_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum fun i _ ↦ have := hm i; measure_ne_top _ A]
  simp only [measureReal_def]

/-- Two uniform averages over non-empty index sets `F`, `F'` differ on every event by at most
`|F ∆ F'| / |F| + | |F'| / |F| - 1 |`. -/
lemma abs_uniformAverage_real_sub_le [DecidableEq ι] (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F F' : Finset ι} (hF : F.Nonempty) (hF' : F'.Nonempty)
    (A : Set Ω) :
    |(uniformAverage m F).real A - (uniformAverage m F').real A| ≤
      ((F ∆ F').card : ℝ) / F.card + |(F'.card : ℝ) / F.card - 1| := by
  set g : ι → ℝ := fun i ↦ (m i).real A with hg
  have hg0 : ∀ i, 0 ≤ g i := fun _ ↦ measureReal_nonneg
  have hg1 : ∀ i, g i ≤ 1 := fun i ↦ have := hm i; measureReal_le_one
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hc' : (0 : ℝ) < F'.card := by exact_mod_cast hF'.card_pos
  rw [uniformAverage_real_apply m hm, uniformAverage_real_apply m hm]
  have hsum_le : ∀ T : Finset ι, ∑ i ∈ T, g i ≤ T.card := fun T ↦ by
    simpa using Finset.sum_le_card_nsmul T g 1 fun i _ ↦ hg1 i
  have hsum_nn : ∀ T : Finset ι, 0 ≤ ∑ i ∈ T, g i := fun T ↦
    Finset.sum_nonneg fun i _ ↦ hg0 i
  have hdecomp : (F.card : ℝ)⁻¹ * ∑ i ∈ F, g i - (F'.card : ℝ)⁻¹ * ∑ i ∈ F', g i =
      (F.card : ℝ)⁻¹ * (∑ i ∈ F \ F', g i - ∑ i ∈ F' \ F, g i) +
        ((F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹) * ∑ i ∈ F', g i := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]; ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (inv_pos.2 hc), div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hc).le
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hsum_nn _), abs_of_nonneg (hsum_nn _), Finset.symmDiff_def,
      Finset.card_union_of_disjoint disjoint_sdiff_sdiff, Nat.cast_add]
    exact add_le_add (hsum_le _) (hsum_le _)
  · rw [abs_mul, abs_of_nonneg (hsum_nn _)]
    calc |(F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹| * ∑ i ∈ F', g i
        ≤ |(F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹| * F'.card :=
          mul_le_mul_of_nonneg_left (hsum_le _) (abs_nonneg _)
      _ = |((F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹) * F'.card| := by rw [abs_mul, abs_of_pos hc']
      _ = |(F'.card : ℝ) / F.card - 1| := by
          congr 1
          rw [sub_mul, inv_mul_cancel₀ hc'.ne', div_eq_inv_mul]

/-- Uniform averages over index sets of the same cardinality differ by at most `|F ∆ F'| / |F|`. -/
lemma abs_uniformAverage_real_sub_le_of_card_eq [DecidableEq ι] (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F F' : Finset ι} (hF : F.Nonempty)
    (hcard : F.card = F'.card) (A : Set Ω) :
    |(uniformAverage m F).real A - (uniformAverage m F').real A| ≤
      ((F ∆ F').card : ℝ) / F.card := by
  have hF' : F'.Nonempty := Finset.card_pos.1 (hcard ▸ hF.card_pos)
  have h := abs_uniformAverage_real_sub_le m hm hF hF' A
  rwa [← hcard, div_self (by exact_mod_cast hF.card_pos.ne'), sub_self, abs_zero, add_zero] at h

/-- A uniform average over `F' ⊆ F` differs from the one over `F` by at most `2 (1 − |F'|/|F|)`. -/
lemma abs_uniformAverage_real_sub_le_of_subset [DecidableEq ι] (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F F' : Finset ι} (hF' : F'.Nonempty) (hsub : F' ⊆ F)
    (A : Set Ω) :
    |(uniformAverage m F).real A - (uniformAverage m F').real A| ≤
      2 * (1 - (F'.card : ℝ) / F.card) := by
  have hF : F.Nonempty := hF'.mono hsub
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hle : (F'.card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_le_card hsub
  have h := abs_uniformAverage_real_sub_le m hm hF hF' A
  have h1 : ((F ∆ F').card : ℝ) / F.card = 1 - F'.card / F.card := by
    rw [symmDiff_of_ge hsub, Finset.card_sdiff_of_subset hsub,
      Nat.cast_sub (Finset.card_le_card hsub), sub_div, div_self hc.ne']
  have h2 : |(F'.card : ℝ) / F.card - 1| = 1 - F'.card / F.card := by
    rw [abs_of_nonpos (by rw [sub_nonpos]; exact (div_le_one hc).2 hle)]; ring
  rw [h1, h2] at h
  linarith

end MeasureTheory

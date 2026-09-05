/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-!
# A π-system criterion for set integrals of `ℝ≥0∞`-valued functions
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory

/-- Two measurable `ℝ≥0∞`-valued functions with finite integrals which have the same integral over
every set of a π-system generating `m`, and over `univ`, have the same integral over every
`m`-measurable set. The `ℝ`-valued analogue is
`MeasureTheory.setIntegral_eq_of_generateFrom`. -/
lemma setLIntegral_eq_of_generateFrom {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {𝒞 : Set (Set Ω)}
    (h𝒞 : IsPiSystem 𝒞) (hgen : m = MeasurableSpace.generateFrom 𝒞) {f g : Ω → ℝ≥0∞}
    (hftop : ∫⁻ x, f x ∂μ ≠ ⊤)
    (h : ∀ s ∈ 𝒞, ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (huniv : ∫⁻ x, f x ∂μ = ∫⁻ x, g x ∂μ) :
    ∀ s, MeasurableSet[m] s → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ := by
  refine MeasurableSpace.induction_on_inter (m := m)
    (C := fun s _ ↦ ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) hgen h𝒞 (by simp)
    (fun t ht ↦ h t ht) (fun t ht hts ↦ ?_) (fun s hd hs hts ↦ ?_)
  · have hf' := lintegral_add_compl (μ := μ) f (hm _ ht)
    have hg' := lintegral_add_compl (μ := μ) g (hm _ ht)
    have hfne : ∫⁻ x in t, f x ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hftop (hf' ▸ le_self_add)
    refine (ENNReal.add_right_inj hfne).1 ?_
    rw [hf', huniv, ← hg', hts]
  · rw [lintegral_iUnion (fun i ↦ hm _ (hs i)) hd, lintegral_iUnion (fun i ↦ hm _ (hs i)) hd]
    exact tsum_congr hts

end MeasureTheory

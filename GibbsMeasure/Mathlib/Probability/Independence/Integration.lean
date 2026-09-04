/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Independence.Integration

/-!
# The Markov property of independent σ-algebras

`setLIntegral_eq_of_indep_sup`: if `m₁ ≤ m₂` and `m₂ ⊥ m₃`, then a version of the conditional
expectation `μ[g | m₁]` of an `m₂`-measurable `g ≥ 0` is also a version of `μ[g | m₁ ⊔ m₃]`.
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*}

/-- **Markov property of independent σ-algebras.** Let `m₁ ≤ m₂` and `m₃` be sub-σ-algebras with
`m₂` and `m₃` independent under the finite measure `μ`. If an `m₂`-measurable `g : Ω → ℝ≥0∞` of
finite integral and an `m₁`-measurable `g'` have the same integrals over all `m₁`-measurable sets
(`g'` is a version of the conditional expectation of `g` given `m₁`), then they have the same
integrals over all `m₁ ⊔ m₃`-measurable sets: `μ[g | m₁ ⊔ m₃] = μ[g | m₁]`. -/
theorem setLIntegral_eq_of_indep_sup {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ)
    (h₃ : m₃ ≤ mΩ) (hind : Indep m₂ m₃ μ) {g g' : Ω → ℝ≥0∞} (hg : Measurable[m₂] g)
    (hg' : Measurable[m₁] g') (hfin : ∫⁻ x, g x ∂μ ≠ ∞)
    (h : ∀ s, MeasurableSet[m₁] s → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, g' x ∂μ) :
    ∀ s, MeasurableSet[m₁ ⊔ m₃] s → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, g' x ∂μ := by
  have h₁ : m₁ ≤ mΩ := h₁₂.trans h₂
  have hle : m₁ ⊔ m₃ ≤ mΩ := sup_le h₁ h₃
  set C : Set (Set Ω) := {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₃] B ∧ s = A ∩ B}
  have hC : IsPiSystem C := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ -
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', Set.inter_inter_inter_comm A B A' B'⟩
  have hgen : m₁ ⊔ m₃ = MeasurableSpace.generateFrom C := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨A, Set.univ, hA, MeasurableSet.univ, (Set.inter_univ A).symm⟩
    · intro B hB
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, B, MeasurableSet.univ, hB, (Set.univ_inter B).symm⟩
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₃) A hA).inter ((le_sup_right : m₃ ≤ m₁ ⊔ m₃) B hB)
  -- the two measures `g μ` and `g' μ` on `m₁ ⊔ m₃`
  have : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hfin
  have hfin' : ∫⁻ x, g' x ∂μ ≠ ∞ := by
    rw [← setLIntegral_univ, ← h _ MeasurableSet.univ, setLIntegral_univ]
    exact hfin
  have : IsFiniteMeasure (μ.withDensity g') := isFiniteMeasure_withDensity hfin'
  have key : (μ.withDensity g).trim hle = (μ.withDensity g').trim hle := by
    refine @ext_of_generate_finite Ω (m₁ ⊔ m₃) _ _ C hgen hC _ ?_ ?_
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      rw [trim_measurableSet_eq hle (hgen ▸ MeasurableSpace.measurableSet_generateFrom
          ⟨A, B, hA, hB, rfl⟩),
        trim_measurableSet_eq hle (hgen ▸ MeasurableSpace.measurableSet_generateFrom
          ⟨A, B, hA, hB, rfl⟩),
        withDensity_apply _ ((h₁ A hA).inter (h₃ B hB)),
        withDensity_apply _ ((h₁ A hA).inter (h₃ B hB)),
        ← lintegral_indicator ((h₁ A hA).inter (h₃ B hB)),
        ← lintegral_indicator ((h₁ A hA).inter (h₃ B hB))]
      have hind' : ∀ {f : Ω → ℝ≥0∞}, Measurable[m₂] f →
          ∫⁻ x, (A ∩ B).indicator f x ∂μ = (∫⁻ x, A.indicator f x ∂μ) * μ B := by
        intro f hf
        have hfA : Measurable[m₂] (A.indicator f) := hf.indicator (h₁₂ A hA)
        have hB1 : Measurable[m₃] (B.indicator fun _ ↦ (1 : ℝ≥0∞)) := measurable_const.indicator hB
        calc ∫⁻ x, (A ∩ B).indicator f x ∂μ
            = ∫⁻ x, A.indicator f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ :=
              lintegral_congr fun x ↦ by rw [← Set.inter_indicator_mul]; simp
          _ = (∫⁻ x, A.indicator f x ∂μ) * ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ := by
              refine lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hfA.mono h₂
                  le_rfl).aemeasurable
                (hB1.mono h₃ le_rfl).aemeasurable ?_
              rw [IndepFun_iff_Indep]
              exact indep_of_indep_of_le hind (measurable_iff_comap_le.1 hfA)
                (measurable_iff_comap_le.1 hB1)
          _ = (∫⁻ x, A.indicator f x ∂μ) * μ B := by
              rw [lintegral_indicator (h₃ B hB), setLIntegral_const, one_mul]
      rw [hind' hg, hind' (hg'.mono h₁₂ le_rfl), lintegral_indicator (h₁ A hA),
        lintegral_indicator (h₁ A hA), h A hA]
    · rw [trim_measurableSet_eq hle MeasurableSet.univ, trim_measurableSet_eq hle
        MeasurableSet.univ,
        withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
        h _ MeasurableSet.univ]
  intro s hs
  have := congrArg (fun ρ ↦ ρ s) key
  simpa only [trim_measurableSet_eq hle hs, withDensity_apply _ (hle s hs)] using this

end MeasureTheory

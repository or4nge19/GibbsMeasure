import Comparator.Defs_LocalLimit

/-! # Comparator challenge: Georgii (7.12) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section LocalLimit

variable {S E : Type*} [MeasurableSpace E]

theorem georgii_7_12_a [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {f : Config S E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (nhds (∫ x, f x ∂μ)) :=
  sorry

theorem georgii_7_12_c [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Tendsto (fun n ↦ tvOn Δ (γ (Λ n) ω) μ) atTop (nhds 0) :=
  sorry

theorem exists_isLambdaSpec_isExtremeGibbs [Countable S] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsLambdaSpec ν (fun _ _ ↦ 1) (indepSpec (S := S) ν) ∧
      IsExtremeGibbs (indepSpec (S := S) ν) (Measure.infinitePi fun _ : S ↦ ν) :=
  sorry

end LocalLimit

end GibbsChallenge

end

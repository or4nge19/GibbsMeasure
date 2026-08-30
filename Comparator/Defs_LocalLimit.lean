import Comparator.Defs

/-! # Definitions: λ-specifications and local limits (Georgii, Theorem (7.12)) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section LocalLimit

variable {S E : Type*} [MeasurableSpace E]

structure IsExtremeGibbs (γ : Finset S → Config S E → Measure (Config S E))
    (μ : Measure (Config S E)) : Prop where
  isGibbs : IsGibbs γ μ
  extreme : ∀ ν₁ ν₂ : Measure (Config S E), IsGibbs γ ν₁ → IsGibbs γ ν₂ →
    ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 → μ = a • ν₁ + b • ν₂ → ν₁ = μ ∧ ν₂ = μ

structure IsLambdaSpec (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → Config S E → ℝ≥0∞)
    (γ : Finset S → Config S E → Measure (Config S E)) : Prop where
  measurable_density : ∀ Λ : Finset S, Measurable (ρ Λ)
  density_apply : ∀ (Λ : Finset S) (ω : Config S E) (A : Set (Config S E)), MeasurableSet A →
    γ Λ ω A = ∫⁻ σ in A, ρ Λ σ ∂(indepSpec ν Λ ω)
  isSpecification : IsSpecification γ

def tvOn (Δ : Finset S) (μ μ' : Measure (Config S E)) : ℝ≥0∞ :=
  ⨆ (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A),
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|

theorem le_tvOn {Δ : Finset S} (μ μ' : Measure (Config S E)) {A : Set (Config S E)}
    (hA : MeasurableSet[inside Δ] A) :
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal| ≤ tvOn Δ μ μ' :=
  le_iSup₂ (f := fun (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A) =>
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|) A hA

end LocalLimit

end GibbsChallenge

end

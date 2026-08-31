import Comparator.Defs

/-!
# Definitions: λ-specifications and local limits (Georgii, Theorem (7.12))

Vocabulary for Georgii's Theorem (7.12), extending the preamble `Comparator.Defs`.

## Main definitions

* `IsExtremeGibbs`: `μ ∈ ex 𝓖(γ)`, Georgii (7.1) applied to the convex set `𝓖(γ)`, written out by
  hand rather than through a convexity API
* `IsLambdaSpec`: a λ-specification `γ = ρ λ_·`, Georgii Definition (1.27), for a single-spin
  *probability* measure `ν` — no restriction for a finite a priori measure by Remark (1.28)(3),
  and the case Georgii reduces to at the start of the proof of (7.12)(c)
* `tvOn Δ`: `sup {|μ A − μ' A| : A ∈ 𝓕_Δ}`, Georgii's uniform distance (8.1) between the
  restrictions to `𝓕_Δ`, i.e. one half of their total variation distance.  Georgii writes the
  quantity converging in (7.12)(c) as `sup {|γ_Λ(f|ω) − μ(f)| : f ∈ 𝓛_Δ, ‖f‖ ≤ 1}`, which is
  `2 · tvOn Δ`; the two vanish together.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Theorem (7.12)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section LocalLimit

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (7.1)** for the convex set `𝓖(γ)`: `μ` is a Gibbs measure of `γ` and every
representation `μ = a • ν₁ + b • ν₂` as a convex combination of Gibbs measures with strictly
positive weights is the trivial one. -/
structure IsExtremeGibbs (γ : Finset S → Config S E → Measure (Config S E))
    (μ : Measure (Config S E)) : Prop where
  /-- `μ ∈ 𝓖(γ)` -/
  isGibbs : IsGibbs γ μ
  /-- `μ` is not a nontrivial convex combination of Gibbs measures -/
  extreme : ∀ ν₁ ν₂ : Measure (Config S E), IsGibbs γ ν₁ → IsGibbs γ ν₂ →
    ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 → μ = a • ν₁ + b • ν₂ → ν₁ = μ ∧ ν₂ = μ

/-- **Georgii, Definition (1.27)** for a single-spin probability measure `ν`: the family `ρ` of
measurable densities is a λ-modification and `γ_Λ(A | ω) = ∫_A ρ_Λ(σ) λ_Λ(dσ | ω)`, with
`λ_Λ = indepSpec ν Λ`. -/
structure IsLambdaSpec (ν : Measure E) [IsProbabilityMeasure ν]
    (ρ : Finset S → Config S E → ℝ≥0∞)
    (γ : Finset S → Config S E → Measure (Config S E)) : Prop where
  /-- each density is measurable -/
  measurable_density : ∀ Λ : Finset S, Measurable (ρ Λ)
  /-- `γ_Λ = ρ_Λ λ_Λ` -/
  density_apply : ∀ (Λ : Finset S) (ω : Config S E) (A : Set (Config S E)), MeasurableSet A →
    γ Λ ω A = ∫⁻ σ in A, ρ Λ σ ∂(indepSpec ν Λ ω)
  /-- `ρ λ_·` is a specification, i.e. `ρ` is a λ-modification -/
  isSpecification : IsSpecification γ

/-- `sup {|μ A − μ' A| : A ∈ 𝓕_Δ}`, Georgii's uniform distance (8.1) between the restrictions of
`μ` and `μ'` to `𝓕_Δ`, i.e. one half of their total variation distance.  The quantity Georgii
proves converges to `0` in Theorem (7.12)(c) is `sup {|γ_Λ(f|ω) − μ(f)| : f ∈ 𝓛_Δ, ‖f‖ ≤ 1}`,
which is twice this; the two vanish together. -/
def tvOn (Δ : Finset S) (μ μ' : Measure (Config S E)) : ℝ≥0∞ :=
  ⨆ (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A),
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|

theorem le_tvOn {Δ : Finset S} (μ μ' : Measure (Config S E)) {A : Set (Config S E)}
    (hA : MeasurableSet[inside Δ] A) :
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal| ≤ tvOn Δ μ μ' :=
  le_iSup₂ (f := fun (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A) =>
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|) A hA

/-- `tvOn Δ μ μ' = 0` forces `μ` and `μ'` to agree on `𝓕_Δ`, so convergence of `tvOn Δ` is genuine
total-variation convergence on `𝓕_Δ`. -/
theorem eq_of_tvOn_eq_zero {Δ : Finset S} {μ μ' : Measure (Config S E)} [IsFiniteMeasure μ]
    [IsFiniteMeasure μ'] (h : tvOn Δ μ μ' = 0) {A : Set (Config S E)}
    (hA : MeasurableSet[inside Δ] A) : μ A = μ' A := by
  have h1 : ENNReal.ofReal |(μ A).toReal - (μ' A).toReal| = 0 :=
    le_antisymm (h ▸ le_tvOn μ μ' hA) bot_le
  have h2 : |(μ A).toReal - (μ' A).toReal| ≤ 0 := by
    simpa using (ENNReal.ofReal_eq_zero.1 h1)
  have h3 : (μ A).toReal = (μ' A).toReal := by
    have := abs_nonneg ((μ A).toReal - (μ' A).toReal)
    have h4 : |(μ A).toReal - (μ' A).toReal| = 0 := le_antisymm h2 this
    have := abs_eq_zero.1 h4
    linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ A) (measure_ne_top μ' A)).1 h3

end LocalLimit

end GibbsChallenge

end

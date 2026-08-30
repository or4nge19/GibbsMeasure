import Comparator.Defs

/-!
# The simplex of Gibbs measures

Vocabulary for the extremal decomposition of the set of Gibbs measures, Georgii, *Gibbs Measures
and Phase Transitions*, 2nd ed., Theorems (7.7)(a) and (7.26).

## Main definitions

* `GibbsSet`: Georgii's `𝓖(γ)`
* `IsExtremeIn`: extremality written out by hand, invoking no convexity API
* `IsTailTrivialOn`: `μ A ∈ {0, 1}` for every tail event `A`

The barycentre `∫ ν w(dν)` is Mathlib's `Measure.join`; `join_eq_barycentre` records the
characterisation `Measure.join w A = ∫⁻ ν, ν A ∂w`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section Simplex

variable {S E : Type*} [MeasurableSpace E]

/-- Georgii's `𝓖(γ)`: the probability measures solving the DLR equations of `γ`. -/
def GibbsSet (γ : Finset S → Config S E → Measure (Config S E)) : Set (Measure (Config S E)) :=
  {μ | IsGibbs γ μ}

theorem mem_gibbsSet_iff {γ : Finset S → Config S E → Measure (Config S E)}
    {μ : Measure (Config S E)} : μ ∈ GibbsSet γ ↔ IsGibbs γ μ := Iff.rfl

/-- Extremality, from first principles: `μ ∈ P` and every representation `μ = a • ν₁ + b • ν₂` with
`ν₁, ν₂ ∈ P` and strictly positive weights summing to `1` is the trivial one `ν₁ = ν₂ = μ`. -/
def IsExtremeIn (P : Set (Measure (Config S E))) (μ : Measure (Config S E)) : Prop :=
  μ ∈ P ∧
    ∀ ν₁ ∈ P, ∀ ν₂ ∈ P, ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 →
      μ = a • ν₁ + b • ν₂ → ν₁ = μ ∧ ν₂ = μ

/-- Tail-triviality: every event of the tail σ-algebra `𝓣` has `μ`-probability `0` or `1`. -/
def IsTailTrivialOn (μ : Measure (Config S E)) : Prop :=
  ∀ A : Set (Config S E), MeasurableSet[tail S E] A → μ A = 0 ∨ μ A = 1

/-- `Measure.join` is the barycentre `∫ ν w(dν)`: it assigns to a measurable event `A` the average
`∫⁻ ν, ν A ∂w`.  This pins the notion down without trusting Mathlib's naming. -/
theorem join_eq_barycentre (w : Measure (Measure (Config S E)))
    {A : Set (Config S E)} (hA : MeasurableSet A) :
    Measure.join w A = ∫⁻ ν, ν A ∂w := Measure.join_apply hA

end Simplex

end GibbsChallenge

end

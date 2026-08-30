import Comparator.Defs

/-!
# Definitions: the simplex of Gibbs measures (Georgii, Theorems (7.7)(a) and (7.26))

This module extends the shared preamble `Comparator.Defs` with the vocabulary of the *extremal
decomposition* of the set of Gibbs measures, used by `Comparator/Challenge_Simplex.lean` and
`Comparator/Solution_Simplex.lean`.  **It imports `Comparator.Defs` — which imports `Mathlib` and
nothing else — and nothing further**, and every notion is spelled out from first principles.

## Dictionary (continuing the preamble's)

| Georgii | here |
| --- | --- |
| `𝓖(γ)`, the set of Gibbs measures | `GibbsSet γ` |
| `ex 𝓖(γ)`, the extreme Gibbs measures | `IsExtremeIn (GibbsSet γ)` |
| `μ` is trivial on the tail σ-algebra `𝓣` | `IsTailTrivialOn μ` |
| the barycentre `∫ ν w(dν)` | `Measure.join w` |

* **Extremality is written out by hand**: `μ` is extreme in `P` when `μ ∈ P` and the only way to
  write `μ = a • ν₁ + b • ν₂` with `ν₁, ν₂ ∈ P` and strictly positive weights `a + b = 1` is the
  trivial one `ν₁ = ν₂ = μ`.  No convexity API is invoked.
* **Tail-triviality** is `μ A ∈ {0, 1}` for every `A` in the tail σ-algebra `tail S E` of the
  preamble.
* The **barycentre** of a probability measure `w` on the space of measures is Mathlib's
  `Measure.join w`, characterised by `Measure.join w A = ∫⁻ ν, ν A ∂w`; `join_eq_barycentre`
  below records this, so no trust in the name `Measure.join` is required.
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

/-- Georgii's `𝓖(γ)`: the set of Gibbs measures of the family `γ`, i.e. the probability measures
solving the DLR equations of `γ`. -/
def GibbsSet (γ : Finset S → Config S E → Measure (Config S E)) : Set (Measure (Config S E)) :=
  {μ | IsGibbs γ μ}

theorem mem_gibbsSet_iff {γ : Finset S → Config S E → Measure (Config S E)}
    {μ : Measure (Config S E)} : μ ∈ GibbsSet γ ↔ IsGibbs γ μ := Iff.rfl

/-- **Extremality, from first principles.** `μ` is an extreme point of a set `P` of measures when
`μ ∈ P` and every representation `μ = a • ν₁ + b • ν₂` of `μ` as a nontrivial convex combination of
members of `P` (strictly positive weights `a, b` with `a + b = 1`) is the trivial one,
`ν₁ = ν₂ = μ`. -/
def IsExtremeIn (P : Set (Measure (Config S E))) (μ : Measure (Config S E)) : Prop :=
  μ ∈ P ∧
    ∀ ν₁ ∈ P, ∀ ν₂ ∈ P, ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 →
      μ = a • ν₁ + b • ν₂ → ν₁ = μ ∧ ν₂ = μ

/-- **Tail-triviality, from first principles**: every event of the tail σ-algebra `𝓣` of the
preamble has `μ`-probability `0` or `1`. -/
def IsTailTrivialOn (μ : Measure (Config S E)) : Prop :=
  ∀ A : Set (Config S E), MeasurableSet[tail S E] A → μ A = 0 ∨ μ A = 1

/-- The barycentre `∫ ν w(dν)` used below really is the barycentre: it assigns to a measurable
event `A` the average `∫⁻ ν, ν A ∂w` of the probabilities `ν A`. This pins down `Measure.join`
from first principles, so that the statement of `existsUnique_weight_isExtremeIn` can be read
without trusting Mathlib's naming. -/
theorem join_eq_barycentre (w : Measure (Measure (Config S E)))
    {A : Set (Config S E)} (hA : MeasurableSet A) :
    Measure.join w A = ∫⁻ ν, ν A ∂w := Measure.join_apply hA

end Simplex

end GibbsChallenge

end

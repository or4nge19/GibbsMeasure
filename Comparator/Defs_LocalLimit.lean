import Comparator.Defs

/-!
# Definitions: λ-specifications and local limits (Georgii, Theorem (7.12))

This module extends the shared preamble `Comparator.Defs` with the vocabulary needed to state
Georgii's Theorem (7.12), used by `Comparator/Challenge_LocalLimit.lean` and
`Comparator/Solution_LocalLimit.lean`.  **It imports `Comparator.Defs` — which imports `Mathlib`
and nothing else — and nothing further**, and every notion is spelled out from first principles.

## Dictionary (continuing the preamble's)

| Georgii | here |
| --- | --- |
| `𝓣 = ⋂_Λ 𝓣_Λ`, the tail σ-algebra | `tail S E` (preamble) |
| `𝓕_Δ`, the events of the finite volume `Δ` | `inside Δ` (preamble) |
| `λ_Λ(·\|ω) = λ^Λ × δ_{ω_{S∖Λ}}`, the independent kernel (1.25) | `indepSpec ν Λ ω` |
| `μ ∈ ex 𝓖(γ)`, an extreme Gibbs measure (7.1) | `IsExtremeGibbs γ μ` |
| a λ-specification `γ = ρ λ_·`, Definition (1.27) | `IsLambdaSpec ν ρ γ` |
| `sup {\|γ_Λ(A\|ω) − μ(A)\| : A ∈ 𝓕_Δ}` | `tvOn Δ (γ Λ ω) μ` |
| local (`𝓛`-) convergence, (4.2) | `TendstoLocally` (preamble) |

## Design notes

* **Extremality is written out by hand** (Georgii (7.1) applied to the convex set `𝓖(γ)`): `μ` is
  an extreme Gibbs measure when it is a Gibbs measure and the only way to write it as
  `a • ν₁ + b • ν₂` with `ν₁, ν₂` Gibbs and strictly positive weights `a + b = 1` is the trivial
  one `ν₁ = ν₂ = μ`.  No convexity API is invoked.
* **λ-specifications** are Georgii's Definition (1.27) verbatim, for a single-spin *probability*
  measure `ν` (which by Remark (1.28)(3) is no restriction for a finite a priori measure, and is
  the case Georgii himself reduces to at the start of the proof of (7.12)(c)): a family `ρ` of
  measurable densities `ρ_Λ : Ω → [0, ∞]` is a λ-modification when the kernels
  `γ_Λ(A|ω) = ∫_A ρ_Λ dλ_Λ(·|ω)` form a specification, and `γ` is then a λ-specification.  The
  independent kernel `λ_Λ = indepSpec ν Λ` is the preamble's, built from `Measure.infinitePi` and
  the gluing map, and the preamble proves it *is* a specification (`isSpecification_indep`).
* **The quantity that converges in (7.12)(c)** is `tvOn Δ`, the supremum of `|μ A − μ' A|` over the
  events `A` of the finite volume `Δ`.  Georgii writes it as
  `sup {|γ_Λ(f|ω) − μ(f)| : f ∈ 𝓛_Δ, ‖f‖ ≤ 1}` and remarks at the end of his proof that this is
  the total variation distance of the restrictions of `γ_Λ(·|ω)` and `μ` to `𝓕_Δ`; the supremum
  over events is that distance, and is the form the assertion takes here.  It lives in `ℝ≥0∞`, so
  the supremum is unconditionally defined.

## Non-degeneracy

The hypotheses used below are not vacuous: `Challenge_LocalLimit.exists_isLambdaSpec_isExtremeGibbs`
exhibits the preamble's independent specification as a λ-specification with `ρ ≡ 1`, whose Gibbs
measure `ν^S` is extreme.
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

/-- **An extreme Gibbs measure, from first principles**: Georgii's Definition (7.1) applied to the
convex set `𝓖(γ)`.  `μ` is a Gibbs measure of `γ`, and every representation `μ = a • ν₁ + b • ν₂`
of `μ` as a convex combination of Gibbs measures with strictly positive weights is the trivial one,
`ν₁ = ν₂ = μ`. -/
structure IsExtremeGibbs (γ : Finset S → Config S E → Measure (Config S E))
    (μ : Measure (Config S E)) : Prop where
  /-- `μ ∈ 𝓖(γ)` -/
  isGibbs : IsGibbs γ μ
  /-- `μ` is not a nontrivial convex combination of Gibbs measures -/
  extreme : ∀ ν₁ ν₂ : Measure (Config S E), IsGibbs γ ν₁ → IsGibbs γ ν₂ →
    ∀ a b : ℝ≥0∞, 0 < a → 0 < b → a + b = 1 → μ = a • ν₁ + b • ν₂ → ν₁ = μ ∧ ν₂ = μ

/-- **A λ-specification, from first principles**: Georgii's Definition (1.27) for a single-spin
probability measure `ν`.  The family `ρ` of measurable densities `ρ_Λ` is a *λ-modification*, and
`γ` is the associated λ-specification `γ = ρ λ_·`, i.e.
`γ_Λ(A | ω) = ∫_A ρ_Λ(σ) λ_Λ(dσ | ω)` with `λ_Λ = indepSpec ν Λ` the independent kernel of the
preamble. -/
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

/-- The distance of two measures **on the events of the finite volume `Δ`**:
`sup {|μ A − μ' A| : A ∈ 𝓕_Δ}`.  This is the total variation distance of the restrictions of `μ`
and `μ'` to `𝓕_Δ`, and is the quantity Georgii proves to converge to `0` in Theorem (7.12)(c). -/
def tvOn (Δ : Finset S) (μ μ' : Measure (Config S E)) : ℝ≥0∞ :=
  ⨆ (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A),
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|

theorem le_tvOn {Δ : Finset S} (μ μ' : Measure (Config S E)) {A : Set (Config S E)}
    (hA : MeasurableSet[inside Δ] A) :
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal| ≤ tvOn Δ μ μ' :=
  le_iSup₂ (f := fun (A : Set (Config S E)) (_ : MeasurableSet[inside Δ] A) =>
    ENNReal.ofReal |(μ A).toReal - (μ' A).toReal|) A hA

/-- `tvOn Δ` really does dominate the discrepancy on each event of `Δ`, and is `0` only when the
two measures agree on `𝓕_Δ`: convergence `tvOn Δ (γ_Λ (·|ω)) μ → 0` is genuine total-variation
convergence on `𝓕_Δ`. -/
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

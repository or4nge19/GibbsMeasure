/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Singleton

/-!
# From conditional probabilities to the DLR equations

Georgii's arguments in Chapters 1 and 13 (Theorem (1.33), and its use in Theorems (13.20) and
(13.22)) repeatedly produce the *conditional-probability* form of the DLR equations,
`μ(A | 𝒯_Λ) = γ_Λ(A | ·)` `μ`-a.s. for every `A ∈ 𝓕`, and then need the *kernel-composition* form
`μ γ_Λ = μ`. This file records that passage. It is a one-line consequence of
`ProbabilityTheory.Kernel.isCondExp_iff_bind_eq_left` and the properness of a specification, but
it is used by name in the Gaussian chapter and it is the only missing link between
`Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq` (Georgii (1.33))
and Lemma (13.10).

## Main results

* `Specification.bind_eq_of_condExp_ae_eq`: `μ(A|𝓕_{Λᶜ}) = γ_Λ(A|·)` a.s. for all measurable `A`
  implies `μ γ_Λ = μ`.
* `Specification.bind_singleton_eq_of_condExp_ae_eq`: the same at a singleton `Λ = {i}`, stated
  with the σ-algebra `cylinderEvents ({i}ᶜ : Set S)` (Georgii's `𝒯_{\{i\}}`) rather than with the
  coercion of the `Finset` `{i}`.
* `Specification.isGibbsMeasure_of_forall_singleton_condExp_ae_eq`: **Georgii (1.33), the form
  used in Chapter 13.** For a λ-specification of a σ-finite reference measure with a positive
  finite pre-modification, a probability measure whose conditional probabilities given `𝒯_{\{i\}}`
  are `γ_{\{i\}}` for every single site `i` is a Gibbs measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {γ : Specification S E} {μ : Measure (S → E)}

/-- If `γ_Λ(·|·)` is a version of the conditional probabilities of `μ` given the configuration
outside `Λ`, then `μ` satisfies the DLR equation `μ γ_Λ = μ` at `Λ`. -/
theorem bind_eq_of_condExp_ae_eq [IsFiniteMeasure μ] (Λ : Finset S)
    (h : ∀ A : Set (S → E), MeasurableSet A →
      μ[A.indicator 1 | cylinderEvents (Λ : Set S)ᶜ] =ᵐ[μ] fun ω ↦ (γ Λ ω A).toReal) :
    μ.bind (γ Λ) = μ :=
  (Kernel.isCondExp_iff_bind_eq_left (γ.isProper Λ) cylinderEvents_le_pi).1
    ⟨fun _A hA ↦ h _A hA⟩

/-- If, for every finite `Λ`, `γ_Λ(·|·)` is a version of the conditional probabilities of `μ`
given the configuration outside `Λ`, then `μ ∈ 𝒢(γ)`. -/
theorem isGibbsMeasure_of_forall_condExp_ae_eq [IsFiniteMeasure μ]
    (h : ∀ (Λ : Finset S) (A : Set (S → E)), MeasurableSet A →
      μ[A.indicator 1 | cylinderEvents (Λ : Set S)ᶜ] =ᵐ[μ] fun ω ↦ (γ Λ ω A).toReal) :
    γ.IsGibbsMeasure μ :=
  fun Λ ↦ ⟨fun _A hA ↦ h Λ _A hA⟩

/-- The single-site case of `Specification.bind_eq_of_condExp_ae_eq`, with Georgii's tail
σ-algebra `𝒯_{\{i\}} = cylinderEvents ({i}ᶜ)` written for the *set* `{i}`. -/
theorem bind_singleton_eq_of_condExp_ae_eq [IsFiniteMeasure μ] (i : S)
    (h : ∀ A : Set (S → E), MeasurableSet A →
      μ[A.indicator 1 | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ] fun ω ↦ (γ {i} ω A).toReal) :
    μ.bind (γ {i}) = μ := by
  refine bind_eq_of_condExp_ae_eq {i} fun A hA ↦ ?_
  simpa only [Finset.coe_singleton] using h A hA

/-- **Georgii (1.33), the form used in Chapter 13.** Let `ν` be a σ-finite non-zero measure on `E`
and `ρ` a positive finite pre-modification admissible for `ν`, so that `γ = ρλ_·` is a
specification. A probability measure `μ` whose conditional probabilities given `𝒯_{\{i\}}` are
given by `γ_{\{i\}}` for every site `i` is a Gibbs measure for `γ`. -/
theorem isGibbsMeasure_of_forall_singleton_condExp_ae_eq {ρ : Finset S → (S → E) → ℝ≥0∞}
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (h0 : ∀ Λ ω, ρ Λ ω ≠ 0) (htop : ∀ Λ ω, ρ Λ ω ≠ ⊤)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (h : ∀ (i : S) (A : Set (S → E)), MeasurableSet A →
      μ[A.indicator 1 | cylinderEvents ({i}ᶜ : Set S)] =ᵐ[μ]
        fun ω ↦ (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ {i} ω A).toReal) :
    (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ :=
  (lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq ν hρ h0 htop hZ).2
    fun i ↦ bind_singleton_eq_of_condExp_ae_eq i (h i)

end Specification

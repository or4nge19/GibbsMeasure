/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.UniquenessFromMixing

/-!
# Quasi-Gibbsian random fields

Georgii, §18.1, the definition preceding Lemma (18.16): a random field `μ` is *quasi-Gibbsian*
if there is a probability measure `λ ∈ 𝒫(E, ℰ)` such that for every tail event `A` with
`μ(A) > 0` the conditional field `μ(·|A)` is equivalent to `λ^S` on `𝓕_Λ`, for every finite
volume `Λ`.  Here `λ^S` restricted to `𝓕_Λ` is the reference kernel `λ_Λ(·|η)` of Georgii
(1.26) — `Specification.isssd` — whose value on an event of `𝓕_Λ` does not depend on `η`.

Georgii deduces from Theorem (7.7)(b) and Remarks (1.28)(2)–(3) that every Gibbs measure
relative to an arbitrary potential is quasi-Gibbsian.  The general statement is
`isQuasiGibbsian_of_isGibbsMeasure_lambdaSpecification`: every Gibbs measure of a
λ-specification with *positive* densities is quasi-Gibbsian.  That is exactly Georgii's
deduction: (7.7)(b) makes `μ(·|A)` a Gibbs measure again, and (1.28)(2) — here
`Specification.IsGibbsMeasure.lambdaSpecification_null_iff` — says a Gibbs measure of a positive
λ-specification has exactly the null sets of `λ_Λ` in `𝓕_Λ`.  The reduction of a finite `λ` to a
probability measure is (1.28)(3).

## Main declarations

* `MeasureTheory.GibbsMeasure.IsQuasiGibbsian`
* `MeasureTheory.GibbsMeasure.isQuasiGibbsian_of_isGibbsMeasure_lambdaSpecification`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii, §18.1.** A random field is *quasi-Gibbsian* if there is a single-spin probability
measure `λ` such that conditioning on any non-null tail event leaves a field equivalent to `λ^S`
in every finite volume. -/
def IsQuasiGibbsian (μ : Measure (S → E)) : Prop :=
  ∃ (ν : Measure E) (_ : IsProbabilityMeasure ν),
    ∀ A : Set (S → E), MeasurableSet[tailSigmaAlgebra S E] A → μ A ≠ 0 →
      ∀ (Δ : Finset S) (η : S → E) {C : Set (S → E)},
        MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] C →
        ((μ[|A]) C = 0 ↔ Specification.isssd ν Δ η C = 0)

/-- **Georgii, §18.1: every Gibbs measure is quasi-Gibbsian.**  A Gibbs measure of a
λ-specification with positive densities is quasi-Gibbsian, by Theorem (7.7)(b) and
Remark (1.28)(2). -/
theorem isQuasiGibbsian_of_isGibbsMeasure_lambdaSpecification
    (ν : Measure E) [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ) :
    IsQuasiGibbsian μ := by
  refine ⟨ν, inferInstance, fun A hA hA0 Δ η C hC ↦ ?_⟩
  haveI : IsProbabilityMeasure (μ[|A]) := cond_isProbabilityMeasure hA0
  haveI : NeZero (μ[|A]) := ⟨IsProbabilityMeasure.ne_zero _⟩
  have hcond := isGibbsMeasure_cond_of_tail μ hμ hA hA0
  rw [Specification.IsGibbsMeasure.lambdaSpecification_null_iff ν hcond hpos Δ hC]
  have hlam : ∀ η' : S → E, Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η' C
      = Specification.isssd (S := S) (E := E) ν Δ η C := by
    intro η'
    rw [Specification.sigmaFiniteLambdaFun_apply_congr ν Δ hC η' η,
      Specification.sigmaFiniteLambdaFun_eq_isssdFun]
    rfl
  exact ⟨fun h ↦ (hlam η) ▸ h η, fun h η' ↦ (hlam η').symm ▸ h⟩

end MeasureTheory.GibbsMeasure

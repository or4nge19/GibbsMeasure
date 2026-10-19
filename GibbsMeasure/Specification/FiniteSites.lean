/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable

/-!
# Specifications on a finite set of sites

When `S` is finite the full volume `S` is itself a finite volume, its exterior σ-algebra is
trivial, and `γ_S(·|η)` does not depend on the boundary condition `η`. By consistency it is then
a Gibbs measure, and every Gibbs measure equals it: a finite system has exactly one Gibbs
measure, its finite-volume Gibbs distribution (Georgii, Remark (1.24)(a) ⇔ (b) at `Λ = S`).
For the Gibbsian specification of a potential this distribution is the Boltzmann–Gibbs law
`e^{-β H_S} / Z · λ^S`.

## Main results

* `Specification.apply_univ_eq`: `γ_S(·|η) = γ_S(·|ζ)`.
* `Specification.isGibbsMeasure_apply_univ`: `γ_S(·|η) ∈ 𝒢(γ)`.
* `Specification.isGibbsMeasure_iff_eq_apply_univ`: `𝒢(γ) = {γ_S(·|η)}`.
* `Specification.isssd_apply_univ`: `λ_S(·|η) = λ^S` (`Measure.pi`).
* `Potential.gibbsSpecificationOfAbsolutelySummable_apply_univ`: `γ^Φ_S(·|η)` is
  `λ^S` with density `e^{-β H_S} / ∫ e^{-β H_S} dλ^S`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Specification

variable {S E : Type*} [Fintype S] [MeasurableSpace E]

/-- On a finite set of sites the kernel of the full volume does not see the boundary condition:
it is measurable for `cylinderEvents ∅ = ⊥`, hence constant. -/
lemma apply_univ_eq (γ : Specification S E) (η ζ : S → E) :
    γ Finset.univ η = γ Finset.univ ζ := by
  ext s hs
  have hbot : cylinderEvents (X := fun _ : S ↦ E) ((Finset.univ : Finset S) : Set S)ᶜ = ⊥ := by
    rw [Finset.coe_univ, Set.compl_univ, cylinderEvents_empty]
  have hm := (γ Finset.univ).measurable_coe hs (measurableSet_singleton (γ Finset.univ ζ s))
  generalize hT : (fun x ↦ γ Finset.univ x s) ⁻¹' {γ Finset.univ ζ s} = T at hm
  rw [hbot] at hm
  have hζ : ζ ∈ T := hT ▸ rfl
  rcases MeasurableSpace.measurableSet_bot_iff.1 hm with h | h
  · exact absurd (h ▸ hζ) (Set.notMem_empty ζ)
  · have hη : η ∈ T := h ▸ Set.mem_univ η
    rw [← hT] at hη
    exact hη

/-- **On a finite set of sites, the full-volume kernel is a Gibbs measure**: consistency
`γ_S ∘ γ_Λ = γ_S` is the DLR equation for `γ_S(·|η)`. -/
theorem isGibbsMeasure_apply_univ (γ : Specification S E) (η : S → E) :
    γ.IsGibbsMeasure (γ Finset.univ η) :=
  isGibbsMeasure_iff_forall_bind_eq_of_prob.2 fun Λ ↦ γ.bind (Finset.subset_univ Λ) η

/-- **On a finite set of sites, a Gibbs probability measure is the full-volume kernel.** The DLR
equation at `Λ = S` averages the constant kernel `γ_S` against `μ`. -/
theorem eq_apply_univ_of_isGibbsMeasure (γ : Specification S E) {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ) (η : S → E) : μ = γ Finset.univ η := by
  have h := isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ Finset.univ
  ext s hs
  rw [← h, Measure.bind_apply hs
    ((γ Finset.univ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable]
  simp_rw [γ.apply_univ_eq _ η]
  simp

/-- `𝒢(γ) = {γ_S(·|η)}` among probability measures, for any boundary condition `η`. -/
theorem isGibbsMeasure_iff_eq_apply_univ (γ : Specification S E) {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (η : S → E) : γ.IsGibbsMeasure μ ↔ μ = γ Finset.univ η :=
  ⟨fun h ↦ γ.eq_apply_univ_of_isGibbsMeasure h η, fun h ↦ h ▸ γ.isGibbsMeasure_apply_univ η⟩

/-- The independent kernel of the full volume is the product measure. -/
lemma isssd_apply_univ (ν : Measure E) [IsProbabilityMeasure ν] (η : S → E) :
    isssd ν Finset.univ η = Measure.pi fun _ : S ↦ ν := by
  have hpi : cylinderEvents (X := fun _ : S ↦ E) ((Finset.univ : Finset S) : Set S)
      = MeasurableSpace.pi := by
    rw [Finset.coe_univ, cylinderEvents_univ]
  ext A hA
  rw [isssd_apply_of_mem_cylinderEvents ν Finset.univ η (hpi ▸ hA), Measure.infinitePi_eq_pi]

end Specification

namespace Potential

variable {S E : Type*} [Fintype S] [MeasurableSpace E] {Φ : Potential S E} [IsPotential Φ]
  [IsAbsolutelySummable Φ]

/-- **The Boltzmann–Gibbs law of a finite system**: the full-volume kernel of the Gibbsian
specification of `βΦ` is the product measure `ν^S` with density
`e^{-β H_S} / ∫ e^{-β H_S} dν^S`; by `Specification.isGibbsMeasure_iff_eq_apply_univ` it is the
unique Gibbs measure. -/
theorem gibbsSpecificationOfAbsolutelySummable_apply_univ (ν : Measure E) [IsProbabilityMeasure ν]
    (β : ℝ) (η : S → E) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Finset.univ η
      = (Measure.pi fun _ : S ↦ ν).withDensity fun σ ↦
          Φ.boltzmannFactor β Finset.univ σ
            / ∫⁻ σ', Φ.boltzmannFactor β Finset.univ σ' ∂Measure.pi fun _ : S ↦ ν := by
  rw [gibbsSpecificationOfAbsolutelySummable, Specification.modification_apply,
    Specification.isssd_apply_univ]
  congr 1
  funext σ
  change _ / ∫⁻ x, _ ∂(Specification.isssd ν Finset.univ σ) = _
  rw [Specification.isssd_apply_univ]

end Potential

end

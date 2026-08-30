/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Transformation

/-!
# Georgii, Definition (5.21): broken symmetries

A symmetry of a specification is *broken* when some Gibbs measure fails to be invariant under it.
By Remark (5.10) the image of a Gibbs measure under a symmetry is again one, so a broken symmetry
forces `|𝒢(γ)| > 1`: this is the mechanism behind most of the phase transitions in the book.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure Set

namespace Specification

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {τ : Transformation S E}

/-- **Georgii, Definition (5.21).** A symmetry `τ` of `γ` is *broken* if some `μ ∈ 𝒢(γ)` has
`τ(μ) ≠ μ`. -/
def IsBrokenSymmetry (γ : Specification S E) (τ : Transformation S E) : Prop :=
  ∃ μ ∈ GP γ, μ.map τ.measurable_toFun.aemeasurable ≠ μ

/-- **Georgii, the remark following (5.21)**: a broken symmetry is a phase transition. -/
theorem nontrivial_GP_of_isBrokenSymmetry (hγ : IsInvariant τ γ)
    (h : γ.IsBrokenSymmetry τ) : (GP γ).Nontrivial := by
  obtain ⟨μ, hμ, hne⟩ := h
  exact ⟨_, hγ.map_mem_GP hμ, μ, hμ, hne⟩

/-- Contrapositive: if `𝒢(γ)` is a singleton then no symmetry of `γ` is broken — Georgii (5.11). -/
theorem not_isBrokenSymmetry_of_GP_eq_singleton (hγ : IsInvariant τ γ)
    {μ : ProbabilityMeasure (S → E)} (hGP : GP γ = {μ}) : ¬ γ.IsBrokenSymmetry τ := by
  rintro ⟨ν, hν, hne⟩
  rw [hGP, mem_singleton_iff] at hν
  subst hν
  refine hne (ProbabilityMeasure.toMeasure_injective ?_)
  rw [ProbabilityMeasure.toMeasure_map]
  exact (hγ.measurePreserving_of_GP_eq_singleton hGP).map_eq

end Specification

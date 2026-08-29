/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithSetwiseTopology
public import GibbsMeasure.Prereqs.CylinderEvents
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Topology of local convergence on probability measures

The **topology of local convergence** on `ProbabilityMeasure (S → E)` (Georgii (4.2)) is the
coarsest topology for which `μ ↦ μ A` is continuous for every finite-volume cylinder event `A`.
The cylinder events are Mathlib's `measurableCylinders`; `localEvents` is Georgii's name `𝓕⁰`
for them.
-/

@[expose] public section

open Set Filter Topology
open scoped Topology ENNReal

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii's algebra `𝓕⁰`** of finite-volume cylinder events: Mathlib's
`measurableCylinders`. -/
abbrev localEvents (S E : Type*) [MeasurableSpace E] : Set (Set (S → E)) :=
  measurableCylinders (fun _ : S ↦ E)

/-- A set is a local event iff it is `cylinderEvents`-measurable for some finite volume. -/
lemma mem_localEvents_iff_cylinderEvents {A : Set (S → E)} :
    A ∈ localEvents S E ↔
      ∃ Λ : Finset S, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A := by
  rw [localEvents, mem_measurableCylinders]
  constructor
  · rintro ⟨Λ, B, hB, rfl⟩
    refine ⟨Λ, ?_⟩
    rw [cylinderEvents_eq_comap_finsetRestrict]
    exact ⟨B, hB, rfl⟩
  · rintro ⟨Λ, hA⟩
    rw [cylinderEvents_eq_comap_finsetRestrict] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact ⟨Λ, B, hB, rfl⟩

/-- A set is a local event iff it is the `Finset.restrict`-preimage of a measurable set of some
finite-volume configuration space. -/
lemma mem_localEvents_iff_exists_finsetRestrict_preimage {A : Set (S → E)} :
    A ∈ localEvents S E ↔
      ∃ (Λ : Finset S) (B : Set (Π _ : Λ, E)), MeasurableSet B ∧ A = Λ.restrict ⁻¹' B :=
  mem_measurableCylinders A

lemma finsetRestrict_preimage_mem_localEvents (Λ : Finset S) {B : Set (Π _ : Λ, E)}
    (hB : MeasurableSet B) : Λ.restrict ⁻¹' B ∈ localEvents S E :=
  mem_localEvents_iff_exists_finsetRestrict_preimage.2 ⟨Λ, B, hB, rfl⟩

lemma mem_localEvents_of_cylinderEvents {A : Set (S → E)} (Λ : Finset S)
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    A ∈ localEvents S E :=
  mem_localEvents_iff_cylinderEvents.2 ⟨Λ, hA⟩

/-! ### The topology of local convergence -/

/-- **Georgii (4.2).** Probability measures on the configuration space, equipped with the topology
of local convergence: setwise convergence on the finite-volume cylinder events. -/
abbrev WithLocalConvergence (S E : Type*) [MeasurableSpace E] : Type _ :=
  WithSetwiseTopology (localEvents S E) (ProbabilityMeasure (S → E))

/-- The local events separate probability measures. -/
lemma separatesOn_localEvents :
    WithSetwiseTopology.SeparatesOn (localEvents S E) (fun μ ↦ IsProbabilityMeasure μ) :=
  WithSetwiseTopology.separatesOn_of_isPiSystem_of_generateFrom
    isPiSystem_measurableCylinders generateFrom_measurableCylinders.symm

/-- **Georgii (4.3)(1).** The topology of local convergence is Hausdorff. -/
instance : T2Space (WithLocalConvergence S E) :=
  WithSetwiseTopology.t2Space_probabilityMeasure separatesOn_localEvents

/-- **Georgii (4.2).** Local convergence is evaluation-wise convergence on the local events. -/
lemma tendsto_withLocalConvergence_iff {ι : Type*} {l : Filter ι}
    {μs : ι → WithLocalConvergence S E} {μ : WithLocalConvergence S E} :
    Filter.Tendsto μs l (𝓝 μ) ↔
      ∀ A ∈ localEvents S E,
        Filter.Tendsto (fun i ↦ ((μs i).toMeasure : Measure (S → E)) A) l
          (𝓝 ((μ.toMeasure : Measure (S → E)) A)) :=
  WithSetwiseTopology.tendsto_prob_iff

end MeasureTheory

module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithSetwiseTopology
public import GibbsMeasure.Prereqs.MeasureExt
public import GibbsMeasure.Prereqs.CylinderEvents
public import GibbsMeasure.Prereqs.SquareCylinders
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Topology of local convergence on probability measures

This file introduces the **topology of local convergence** on `ProbabilityMeasure (S → E)`.

Informally, local convergence is the coarsest topology for which the maps

`μ ↦ μ A`

are continuous for all finite-volume cylinder events `A`, i.e. events measurable with respect to
`cylinderEvents Λ` for some finite `Λ : Finset S`.

Square cylinders are kept as a generating π-system for separation and measure extensionality, but
the topology itself is induced by all local events.
-/

@[expose] public section

open Set Filter Topology
open scoped Topology
open scoped ENNReal

namespace MeasureTheory

namespace ProbabilityMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- Evaluation of a probability measure on a square cylinder. -/
def evalSquareCylinder (S E : Type*) [MeasurableSpace E] :
    ProbabilityMeasure (S → E) → (squareCylindersMeas S E) → ℝ≥0∞ :=
  fun μ A ↦ (μ : Measure (S → E)) A.1

/-- The finite-volume local events in configuration space. -/
def localEvents (S E : Type*) [MeasurableSpace E] : Set (Set (S → E)) :=
  {A | ∃ Λ : Finset S, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A}

/-- Evaluation of a probability measure on all finite-volume local events. -/
def evalLocalEvent (S E : Type*) [MeasurableSpace E] :
    ProbabilityMeasure (S → E) → (localEvents S E) → ℝ≥0∞ :=
  fun μ A ↦ (μ : Measure (S → E)) A.1

lemma squareCylinder_mem_localEvents {A : Set (S → E)}
    (hA : A ∈ squareCylindersMeas S E) : A ∈ localEvents S E := by
  classical
  rcases hA with ⟨Λ, t, ht, rfl⟩
  refine ⟨Λ, ?_⟩
  rw [cylinderEvents_eq_comap_restrict (S := S) (E := E) (Δ := (Λ : Set S))]
  let C : Set (↥(Λ : Set S) → E) :=
    (Set.univ : Set ↥(Λ : Set S)).pi (fun i : ↥(Λ : Set S) ↦ t i)
  refine ⟨C, ?_, ?_⟩
  · have hC : C ∈ squareCylindersMeas (Λ : Set S) E := by
      refine ⟨Finset.univ, fun i : ↥(Λ : Set S) ↦ t i, ?_, ?_⟩
      · intro i _hi
        exact ht i (by simp)
      · ext ζ
        simp [C, Set.mem_pi]
    have hgen :
        (inferInstance : MeasurableSpace (↥(Λ : Set S) → E))
          = MeasurableSpace.generateFrom (squareCylindersMeas ↥(Λ : Set S) E) :=
      generateFrom_squareCylindersMeas ↥(Λ : Set S) E
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hC
  · ext η
    change ((Set.restrict (π := fun _ : S ↦ E) (Λ : Set S) η) ∈ C) ↔
      η ∈ (Λ : Set S).pi t
    constructor
    · intro h i hi
      exact h ⟨i, hi⟩ (by simp)
    · intro h i _hi
      exact h i i.property

/-! ### The topology of local convergence -/

/-- **Georgii (4.2).** Probability measures on the configuration space, equipped with the topology
of local convergence: setwise convergence on the finite-volume cylinder events. -/
abbrev WithLocalConvergence (S E : Type*) [MeasurableSpace E] : Type _ :=
  WithSetwiseTopology (localEvents S E) (ProbabilityMeasure (S → E))

/-- The local events separate probability measures. -/
lemma separatesOn_localEvents :
    WithSetwiseTopology.SeparatesOn (localEvents S E) (fun μ ↦ IsProbabilityMeasure μ) :=
  WithSetwiseTopology.SeparatesOn.mono
    (WithSetwiseTopology.separatesOn_of_isPiSystem_of_generateFrom
      (isPiSystem_squareCylindersMeas S E) (generateFrom_squareCylindersMeas S E))
    fun A hA ↦ squareCylinder_mem_localEvents hA

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

end ProbabilityMeasure

end MeasureTheory

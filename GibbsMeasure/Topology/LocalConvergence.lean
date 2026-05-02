module

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

open Set Filter
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

/-! ### Local convergence topology -/

/-- The **topology of local convergence** on `ProbabilityMeasure (S → E)`.

It is the induced topology from the evaluation map on all finite-volume cylinder events. -/
@[reducible]
def localConvergence (S E : Type*) [MeasurableSpace E] :
    TopologicalSpace (ProbabilityMeasure (S → E)) :=
  TopologicalSpace.induced (evalLocalEvent S E) inferInstance

lemma nhds_eq_comap_evalLocalEvent (μ : ProbabilityMeasure (S → E)) :
    @nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ =
      Filter.comap (evalLocalEvent S E) (nhds (evalLocalEvent S E μ)) :=
  nhds_induced _ _

lemma tendsto_localConvergence_iff {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    @Tendsto ι (ProbabilityMeasure (S → E)) μs l
        (@nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ) ↔
      Tendsto (fun i ↦ evalLocalEvent S E (μs i)) l (nhds (evalLocalEvent S E μ)) := by
  rw [nhds_eq_comap_evalLocalEvent (S := S) (E := E) (μ := μ)]
  rw [Filter.tendsto_comap_iff]
  rfl

/-- In the topology of local convergence, `μs → μ` iff `μs(A) → μ(A)` for every local event `A`.
-/
lemma tendsto_localConvergence_iff_forall {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    @Tendsto ι (ProbabilityMeasure (S → E)) μs l
        (@nhds (ProbabilityMeasure (S → E)) (localConvergence S E) μ) ↔
      ∀ A : localEvents S E,
        Tendsto (fun i ↦ (μs i : Measure (S → E)) A.1) l (nhds ((μ : Measure (S → E)) A.1)) := by
  have := (tendsto_localConvergence_iff (S := S) (E := E) (l := l) (μs := μs) (μ := μ))
  simpa [evalLocalEvent, Function.comp] using (this.trans tendsto_pi_nhds)

/-! ### Hausdorffness -/

lemma evalSquareCylinder_injective :
    Function.Injective (evalSquareCylinder S E) := by
  classical
  intro μ₁ μ₂ h
  apply Subtype.ext
  let C : Set (Set (S → E)) := squareCylindersMeas S E
  have hC_pi : IsPiSystem C := by
    simpa [C] using (isPiSystem_squareCylindersMeas S E)
  have hgen : (inferInstance : MeasurableSpace (S → E)) = MeasurableSpace.generateFrom C := by
    simpa [C] using (generateFrom_squareCylindersMeas S E)
  have huniv : (Set.univ : Set (S → E)) ∈ C := by
    simpa [C] using (univ_mem_squareCylindersMeas S E)
  have hμ1 : (μ₁ : Measure (S → E)) Set.univ ≠ ⊤ := by simp
  refine
    MeasureTheory.Measure.ext_of_generateFrom_of_iUnion_univ (m := MeasurableSpace.pi) (C := C)
      (μ := (μ₁ : Measure (S → E))) (ν := (μ₂ : Measure (S → E)))
      (hA := hgen) (hC := hC_pi) (huniv := huniv) (hμ_univ := hμ1) ?_
  intro s hs
  simpa [evalSquareCylinder] using congrArg (fun f ↦ f ⟨s, hs⟩) h

lemma evalLocalEvent_injective :
    Function.Injective (evalLocalEvent S E) := by
  classical
  intro μ₁ μ₂ h
  apply Subtype.ext
  have hsq : evalSquareCylinder S E μ₁ = evalSquareCylinder S E μ₂ := by
    funext A
    exact congrArg
      (fun f ↦ f ⟨A.1, squareCylinder_mem_localEvents (S := S) (E := E) A.2⟩) h
  have hprob : μ₁ = μ₂ := evalSquareCylinder_injective (S := S) (E := E) hsq
  exact congrArg Subtype.val hprob

/-- The topology of local convergence is Hausdorff (T2). -/
theorem t2Space_localConvergence :
    @T2Space (ProbabilityMeasure (S → E)) (localConvergence S E) := by
  classical
  letI : TopologicalSpace (ProbabilityMeasure (S → E)) := localConvergence S E
  let f := evalLocalEvent S E
  have hf_inj : Function.Injective f := evalLocalEvent_injective (S := S) (E := E)
  refine T2Space.mk ?_
  intro μ₁ μ₂ hne
  have hne' : f μ₁ ≠ f μ₂ := by
    intro hEq
    exact hne (hf_inj hEq)
  rcases t2_separation hne' with ⟨U, V, hUo, hVo, hUμ, hVμ, hdisj⟩
  refine ⟨f ⁻¹' U, f ⁻¹' V, ?_, ?_, hUμ, hVμ, ?_⟩
  ·  exact isOpen_induced hUo
  · exact isOpen_induced hVo
  · exact hdisj.preimage (f := f)

end ProbabilityMeasure

end MeasureTheory

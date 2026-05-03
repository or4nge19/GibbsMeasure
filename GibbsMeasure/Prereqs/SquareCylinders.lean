module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Square cylinders (measurable rectangles) on configuration spaces

This file defines the recurring π-system `squareCylinders (measurableSet)` on `S → E` and
its basic properties (π-system + generates the product σ-algebra). It is used throughout the
Vol II / DLR development to avoid repeating boilerplate.
-/

@[expose] public section

open Set

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

/-- The π-system of **square cylinders** in `(S → E)` built from measurable sets. -/
def squareCylindersMeas (S E : Type*) [MeasurableSpace E] : Set (Set (S → E)) :=
  MeasureTheory.squareCylinders (fun _ : S ↦ {s : Set E | MeasurableSet s})

lemma isPiSystem_squareCylindersMeas (S E : Type*) [MeasurableSpace E] :
    IsPiSystem (squareCylindersMeas S E) := by
  classical
  refine isPiSystem_squareCylinders (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet) ?_
  intro _; exact MeasurableSet.univ

lemma generateFrom_squareCylindersMeas (S E : Type*) [MeasurableSpace E] :
    (inferInstance : MeasurableSpace (S → E))
      = MeasurableSpace.generateFrom (squareCylindersMeas S E) := by
  classical
  simpa [squareCylindersMeas] using
    (generateFrom_squareCylinders (ι := S) (α := fun _ : S ↦ E)).symm

lemma univ_mem_squareCylindersMeas (S E : Type*) [MeasurableSpace E] :
    (Set.univ : Set (S → E)) ∈ squareCylindersMeas S E := by
  classical
  refine ⟨∅, (fun _ : S ↦ (Set.univ : Set E)), ?_, ?_⟩
  · simp [Set.mem_pi, MeasurableSet.univ]
  · ext x; simp

/-- A finite square cylinder with measurable sides is measurable in the product space. -/
lemma measurableSet_finset_pi
    (s : Finset S) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet ((s : Set S).pi t) :=
  MeasurableSet.pi s.countable_toSet (fun i _ => ht i)

end MeasureTheory


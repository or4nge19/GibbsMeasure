module

public import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

public section

open MeasureTheory NNReal

namespace MeasureTheory.SimpleFunc
variable {α E : Type*} {mα mα₀ : MeasurableSpace α} [NormedAddCommGroup E] {μ : Measure[mα] α}

/-- A simple function measurable for a smaller σ-algebra is integrable on a finite measure space. -/
lemma integrable_of_isFiniteMeasure' (hα : mα₀ ≤ mα) [IsFiniteMeasure μ] (f : α →ₛ[mα₀] E) :
    Integrable f μ := by
  classical
  refine ⟨(SimpleFunc.stronglyMeasurable f).mono hα |>.aestronglyMeasurable, ?_⟩
  let C : ℝ≥0 := Finset.sup f.range fun y => ‖y‖₊
  have hC : ∀ x, ‖f x‖ ≤ (C : ℝ) := fun x => by
    rw [← coe_nnnorm (f x)]
    exact_mod_cast Finset.le_sup (f.mem_range_self x)
  exact HasFiniteIntegral.of_bounded (μ := μ) (ae_of_all _ hC)

end MeasureTheory.SimpleFunc

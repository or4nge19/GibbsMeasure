/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Normed.Lp.lpSpace
public import GibbsMeasure.Specification.QuasilocalAlgebra
public import GibbsMeasure.Topology.LocalConvergence

/-!
# Local observables are continuous for the topology of local convergence

Georgii (4.3)(2): the topology of local convergence is exactly the topology of convergence of the
integrals of all bounded local observables. The route is Georgii's: simple functions for a finite
volume are finite sums of evaluations, quasilocal observables are their uniform limits, and the
`L`-continuous observables are uniformly closed.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- The observables whose integral is continuous for the topology of local convergence. -/
def LContinuous (f : lp (fun _ : S → E ↦ ℝ) ∞) : Prop :=
  Continuous fun μ : WithLocalConvergence S E ↦
    ∫ x, (f : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E)))

/-- The measurable observables with `L`-continuous integral form a uniformly closed set. -/
theorem isClosed_lContinuous :
    IsClosed ((boundedMeasurable (MeasurableSpace.pi (X := fun _ : S ↦ E)) :
      Set (lp (fun _ : S → E ↦ ℝ) ∞)) ∩ {f | LContinuous f}) := by
  refine IsSeqClosed.isClosed fun F g hF hFg ↦ ?_
  have hgmeas : g ∈ boundedMeasurable (MeasurableSpace.pi (X := fun _ : S ↦ E)) :=
    (isClosed_boundedMeasurable _).mem_of_tendsto hFg (.of_forall fun n ↦ (hF n).1)
  refine ⟨hgmeas, ?_⟩
  refine TendstoUniformly.continuous
    (F := fun n ↦ fun μ : WithLocalConvergence S E ↦
      ∫ x, (F n : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E))))
    (p := (atTop : Filter ℕ)) (Metric.tendstoUniformly_iff.2 fun ε hε ↦ ?_)
    (.of_forall fun n ↦ (hF n).2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hFg (ε / 2) (by positivity)
  refine eventually_atTop.2 ⟨N, fun n hn μ ↦ ?_⟩
  have hprob : IsProbabilityMeasure ((μ.toMeasure : Measure (S → E))) := μ.toMeasure.2
  have hsub : ‖(∫ x, (g : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E))))
      - ∫ x, (F n : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E)))‖ ≤ ‖g - F n‖ := by
    rw [← integral_sub (lp.integrable_of_measurable hgmeas _)
      (lp.integrable_of_measurable (hF n).1 _)]
    have := norm_integral_le_of_norm_le_const (μ := (μ.toMeasure : Measure (S → E)))
      (C := ‖g - F n‖) (f := fun x ↦ (g : (S → E) → ℝ) x - (F n : (S → E) → ℝ) x)
      (.of_forall fun x ↦ by
        have := lp.norm_apply_le_norm ENNReal.top_ne_zero (g - F n) x
        rwa [lp.coeFn_sub, Pi.sub_apply] at this)
    simpa using this
  have hlt : ‖g - F n‖ < ε / 2 := by
    have : ‖F n - g‖ < ε / 2 := by simpa [dist_eq_norm] using hN n hn
    rwa [← norm_neg, neg_sub] at this
  simpa [Real.dist_eq, dist_eq_norm] using lt_of_le_of_lt hsub (by linarith)

/-- Simple functions for a finite volume are `L`-continuous. -/
theorem lContinuous_of_mem_simpleFunctions (Λ : Finset S)
    {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : f ∈ simpleFunctions (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))) :
    LContinuous f := by
  classical
  obtain ⟨g, hg⟩ := hf
  have hmle : cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)
      ≤ (inferInstance : MeasurableSpace (S → E)) := cylinderEvents_le_pi
  have hgmeas : Measurable (⇑g) :=
    (@SimpleFunc.measurable _ _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) _ g).mono
      hmle le_rfl
  have hfmeas : Measurable (⇑f) := by rw [hg]; exact hgmeas
  have key : ∀ μ : WithLocalConvergence S E,
      (∫ x, (f : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E))))
        = ∑ y ∈ @SimpleFunc.range _ _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) g,
            (μ.toMeasure : Measure (S → E)).real (⇑g ⁻¹' {y}) • y := by
    intro μ
    have hprob : IsProbabilityMeasure ((μ.toMeasure : Measure (S → E))) := μ.toMeasure.2
    have hint : Integrable (⇑g) ((μ.toMeasure : Measure (S → E))) := by
      have := lp.integrable_of_measurable (f := f) hfmeas ((μ.toMeasure : Measure (S → E)))
      rwa [hg] at this
    calc (∫ x, (f : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E))))
        = ∫ x, (g : (S → E) → ℝ) x ∂((μ.toMeasure : Measure (S → E))) := by rw [hg]
      _ = _ := integral_simpleFunc_larger_space hmle g hint
  simp only [LContinuous, key]
  refine continuous_finsetSum _ fun y _ ↦ ?_
  simp only [smul_eq_mul]
  refine Continuous.mul ?_ continuous_const
  refine WithSetwiseTopology.continuous_apply_real (𝒞 := localEvents S E) ?_
  exact mem_localEvents_of_cylinderEvents Λ (@SimpleFunc.measurableSet_fiber _ _
    (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) g y)

/-- Integration against a quasilocal observable is `L`-continuous. -/
theorem lContinuous_of_mem_quasilocalFunctions {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : f ∈ quasilocalFunctions S E) : LContinuous f := by
  have hloc : ∀ g : lp (fun _ : S → E ↦ ℝ) ∞, g ∈ localFunctions S E →
      g ∈ (boundedMeasurable (MeasurableSpace.pi (X := fun _ : S ↦ E)) :
        Set (lp (fun _ : S → E ↦ ℝ) ∞)) ∩ {f | LContinuous f} := by
    intro g hg
    obtain ⟨Λ, hΛ⟩ := mem_localFunctions.1 hg
    have hsub : (simpleFunctions (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) :
        Set (lp (fun _ : S → E ↦ ℝ) ∞))
        ⊆ (boundedMeasurable (MeasurableSpace.pi (X := fun _ : S ↦ E)) :
          Set (lp (fun _ : S → E ↦ ℝ) ∞)) ∩ {f | LContinuous f} := fun h hh ↦
      ⟨boundedMeasurable_mono cylinderEvents_le_pi (simpleFunctions_le_boundedMeasurable _ hh),
        lContinuous_of_mem_simpleFunctions Λ hh⟩
    have hmem : g ∈ closure (simpleFunctions
        (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) : Set (lp (fun _ : S → E ↦ ℝ) ∞)) := by
      have h := topologicalClosure_simpleFunctions
        (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))
      have : g ∈ (simpleFunctions
          (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))).topologicalClosure := by
        rw [h]; exact hΛ
      rwa [← Subalgebra.topologicalClosure_coe, SetLike.mem_coe]
    exact closure_minimal hsub isClosed_lContinuous hmem
  have := closure_minimal hloc isClosed_lContinuous
  exact (this (by rw [← Subalgebra.topologicalClosure_coe]; exact hf)).2

/-- The indicator of a set, as a bounded observable. -/
def indicatorLp (A : Set (S → E)) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨A.indicator (fun _ ↦ (1 : ℝ)), memℓp_infty ⟨1, by
    rintro _ ⟨x, rfl⟩; by_cases hx : x ∈ A <;> simp [hx]⟩⟩

omit [MeasurableSpace E] in
@[simp] lemma coeFn_indicatorLp (A : Set (S → E)) :
    ⇑(indicatorLp (S := S) (E := E) A) = A.indicator (fun _ ↦ (1 : ℝ)) := rfl

lemma indicatorLp_mem_localFunctions {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    indicatorLp A ∈ localFunctions S E := by
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  exact mem_localFunctions.2 ⟨Λ, by
    rw [mem_localFunctionsOn, coeFn_indicatorLp]; exact measurable_const.indicator hΛ⟩

/-- **Georgii (4.3)(2).** The topology of local convergence is the topology of convergence of the
integrals of all local observables. -/
theorem tendsto_iff_forall_localFunctions {ι : Type*} {l : Filter ι}
    {μs : ι → WithLocalConvergence S E} {μ : WithLocalConvergence S E} :
    Tendsto μs l (𝓝 μ) ↔
      ∀ f ∈ localFunctions S E,
        Tendsto (fun i ↦ ∫ x, (f : (S → E) → ℝ) x ∂((μs i).toMeasure : Measure (S → E))) l
          (𝓝 (∫ x, (f : (S → E) → ℝ) x ∂(μ.toMeasure : Measure (S → E)))) := by
  constructor
  · intro h f hf
    exact ((lContinuous_of_mem_quasilocalFunctions
      (localFunctions_le_quasilocalFunctions hf)).tendsto μ).comp h
  · intro h
    rw [(WithSetwiseTopology.isInducing_evalProb
      (𝒞 := localEvents S E)).tendsto_nhds_iff, tendsto_pi_nhds]
    rintro ⟨A, hA⟩
    obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
    have hAmeas : MeasurableSet A := cylinderEvents_le_pi (X := fun _ : S ↦ E) A hΛ
    have hint : ∀ ν : WithLocalConvergence S E,
        (∫ x, (indicatorLp (S := S) (E := E) A : (S → E) → ℝ) x
            ∂((ν.toMeasure : Measure (S → E))))
          = ((ν.toMeasure : Measure (S → E)) A).toReal := by
      intro ν
      rw [coeFn_indicatorLp, integral_indicator_const (1 : ℝ) hAmeas]
      simp [measureReal_def]
    have hconv := h (indicatorLp A) (indicatorLp_mem_localFunctions hA)
    simp only [hint] at hconv
    exact (ENNReal.tendsto_toReal_iff (fun i ↦ measure_ne_top _ _) (measure_ne_top _ _)).1 hconv

end MeasureTheory.GibbsMeasure

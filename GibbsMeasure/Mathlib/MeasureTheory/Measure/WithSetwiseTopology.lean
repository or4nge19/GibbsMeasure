/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The topology of setwise convergence on measures

`WithSetwiseTopology 𝒞 α` is a type synonym for a space of measures `α`, equipped with the topology
induced by evaluation on a family `𝒞` of sets. Following the pattern of
`MeasureTheory.LevyProkhorov`.

For probability measures the topology is Hausdorff as soon as `𝒞` separates
(`WithSetwiseTopology.t2Space_probabilityMeasure`), e.g. for a generating π-system.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Evaluation of a measure on a family `𝒞` of sets. -/
def setwiseEval (𝒞 : Set (Set Ω)) (μ : Measure Ω) : 𝒞 → ℝ≥0∞ := fun A ↦ μ A.1

/-- A type synonym, to be used for `Measure Ω`, `FiniteMeasure Ω` or `ProbabilityMeasure Ω` when
they are to be equipped with the topology of setwise convergence along a family `𝒞`. -/
structure WithSetwiseTopology {Ω : Type*} (𝒞 : Set (Set Ω)) (α : Type*) where
  ofMeasure ::
  toMeasure : α

namespace WithSetwiseTopology

variable {𝒞 : Set (Set Ω)} {α : Type*}

lemma toMeasure_injective : Function.Injective (toMeasure : WithSetwiseTopology 𝒞 α → α) :=
  fun ⟨_⟩ ⟨_⟩ ↦ by congr!

/-- `WithSetwiseTopology.toMeasure` as an equiv. -/
@[simps]
def toMeasureEquiv : WithSetwiseTopology 𝒞 α ≃ α where
  toFun := toMeasure
  invFun := ofMeasure

/-- Evaluation on `𝒞`. -/
def eval (𝒞 : Set (Set Ω)) : WithSetwiseTopology 𝒞 (Measure Ω) → 𝒞 → ℝ≥0∞ :=
  fun μ ↦ setwiseEval 𝒞 μ.toMeasure

/-- Evaluation on `𝒞`, for probability measures. -/
def evalProb (𝒞 : Set (Set Ω)) :
    WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) → 𝒞 → ℝ≥0∞ :=
  fun μ ↦ setwiseEval 𝒞 (μ.toMeasure : Measure Ω)

instance instTopologicalSpaceMeasure :
    TopologicalSpace (WithSetwiseTopology 𝒞 (Measure Ω)) := .induced (eval 𝒞) inferInstance

instance instTopologicalSpaceProbabilityMeasure :
    TopologicalSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) :=
  .induced (evalProb 𝒞) inferInstance

lemma isInducing_evalProb : Topology.IsInducing (evalProb (Ω := Ω) 𝒞) := ⟨rfl⟩

/-- Convergence in the setwise topology is evaluation-wise convergence on `𝒞`. -/
lemma tendsto_prob_iff {ι : Type*} {l : Filter ι}
    {μs : ι → WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)}
    {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)} :
    Tendsto μs l (𝓝 μ) ↔
      ∀ A ∈ 𝒞, Tendsto (fun i ↦ ((μs i).toMeasure : Measure Ω) A) l
        (𝓝 ((μ.toMeasure : Measure Ω) A)) := by
  rw [isInducing_evalProb.tendsto_nhds_iff, tendsto_pi_nhds]
  exact ⟨fun h A hA ↦ h ⟨A, hA⟩, fun h A ↦ h A.1 A.2⟩

/-- `𝒞` separates the measures satisfying `P`. -/
def SeparatesOn (𝒞 : Set (Set Ω)) (P : Measure Ω → Prop) : Prop :=
  ∀ ⦃μ ν : Measure Ω⦄, P μ → P ν → (∀ A ∈ 𝒞, μ A = ν A) → μ = ν

lemma SeparatesOn.mono {𝒟 : Set (Set Ω)} {P : Measure Ω → Prop} (h : SeparatesOn 𝒟 P)
    (hsub : 𝒟 ⊆ 𝒞) : SeparatesOn 𝒞 P :=
  fun _ _ hμ hν hAgree ↦ h hμ hν fun A hA ↦ hAgree A (hsub hA)

/-- A generating π-system separates probability measures. -/
theorem separatesOn_of_isPiSystem_of_generateFrom (hpi : IsPiSystem 𝒞)
    (hgen : (inferInstance : MeasurableSpace Ω) = MeasurableSpace.generateFrom 𝒞) :
    SeparatesOn 𝒞 (fun μ ↦ IsProbabilityMeasure μ) := fun μ ν hμ hν h ↦
  ext_of_generate_finite (μ := μ) (ν := ν) 𝒞 hgen hpi h (by simp)

/-- The setwise topology on probability measures is Hausdorff when `𝒞` separates. -/
theorem t2Space_probabilityMeasure (h𝒞 : SeparatesOn 𝒞 (fun μ ↦ IsProbabilityMeasure μ)) :
    T2Space (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) := by
  refine Topology.IsEmbedding.t2Space (f := evalProb (Ω := Ω) 𝒞) ⟨isInducing_evalProb, ?_⟩
  rintro ⟨μ⟩ ⟨ν⟩ h
  have : (μ : Measure Ω) = (ν : Measure Ω) :=
    h𝒞 μ.2 ν.2 fun A hA ↦ congrArg (fun g ↦ g ⟨A, hA⟩) h
  simp [ProbabilityMeasure.toMeasure_injective this]

lemma continuous_apply_enn {A : Set Ω} (hA : A ∈ 𝒞) :
    Continuous fun μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) ↦
      ((μ.toMeasure : Measure Ω) A) :=
  (_root_.continuous_apply (⟨A, hA⟩ : 𝒞)).comp isInducing_evalProb.continuous

lemma continuous_apply_real {A : Set Ω} (hA : A ∈ 𝒞) :
    Continuous fun μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) ↦
      (μ.toMeasure : Measure Ω).real A := by
  refine continuous_iff_continuousAt.2 fun μ ↦ ?_
  have h1 : ContinuousAt (fun μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) ↦
      ((μ.toMeasure : Measure Ω) A)) μ := (continuous_apply_enn hA).continuousAt
  have h2 : ContinuousAt ENNReal.toReal ((μ.toMeasure : Measure Ω) A) :=
    ENNReal.continuousAt_toReal (measure_ne_top _ _)
  show ContinuousAt _ μ
  simpa [measureReal_def, ContinuousAt, Function.comp_def] using Filter.Tendsto.comp h2 h1

end WithSetwiseTopology

end MeasureTheory

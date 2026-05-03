module

public import GibbsMeasure.Prereqs.Kernel.Feller
public import GibbsMeasure.Specification
public import GibbsMeasure.Specification.Quasilocal
public import Mathlib.Topology.Continuous

/-!
# Continuous/Feller quasilocal specifications

This file links the *functional-analytic* notion of quasilocal observables to specifications.

Assuming a specification `γ` has **Feller** kernels (in the sense of
`ProbabilityTheory.Kernel.IsFeller`), we can define the induced action on bounded continuous
observables. Markovness is already bundled in `Specification`:

`f ↦ (η ↦ ∫ x, f x ∂(γ Λ η))`.

A specification is **Feller-quasilocal** if this action preserves the submodule of continuous
Feller-quasilocal observables (uniform closure of bounded continuous cylinder observables).

This is a continuous/Feller version of Georgii's Definition 2.23. Georgii's full definition is
formulated using bounded local measurable functions and their uniform closure, not only bounded
continuous observables. The old `IsQuasilocal` name is kept as a compatibility alias, but new
statements should use `IsFellerQuasilocal` unless the full measurable Georgii algebra has been
formalized.

We also record the convenient “dense-check” formulation: it suffices to verify quasilocality on
cylinder observables, since the action is continuous in the sup-norm.
-/

@[expose] public section

open Set
open scoped Topology

namespace Specification

open ProbabilityTheory
open ProbabilityTheory.Kernel

variable {S E : Type*} [MeasurableSpace E] [TopologicalSpace E]
variable [OpensMeasurableSpace (S → E)]

-- We work with bounded continuous observables on the configuration space.
open BoundedContinuousFunction
local notation3 (prettyPrint := false) "Obs" => ((S → E) →ᵇ ℝ)

/-- A specification is **Feller** if all of its finite-volume kernels are Feller kernels. -/
class IsFeller (γ : Specification S E) : Prop where
  isFellerKernel : ∀ Λ, ProbabilityTheory.Kernel.IsFeller (γ Λ)

namespace IsFeller

instance (γ : Specification S E) [γ.IsFeller] (Λ : Finset S) :
    ProbabilityTheory.Kernel.IsFeller (γ Λ) :=
  IsFeller.isFellerKernel (γ := γ) Λ

end IsFeller

section Action

variable (γ : Specification S E)
variable [γ.IsFeller]

/-- The (Feller) action of `γ(Λ)` on bounded continuous observables. -/
noncomputable def continuousAction (Λ : Finset S) : Obs → Obs :=
  fun f => ProbabilityTheory.Kernel.continuousAction (κ := γ Λ) f

omit [OpensMeasurableSpace (S → E)] in
@[simp] lemma continuousAction_apply (Λ : Finset S) (f : Obs) (η : S → E) :
    continuousAction γ Λ f η = ∫ x, f x ∂(γ Λ η) := by
  simp [continuousAction]

/-- The action operator as a continuous linear map on observables. -/
noncomputable def continuousActionCLM (Λ : Finset S) : Obs →L[ℝ] Obs :=
  ProbabilityTheory.Kernel.continuousActionCLM (κ := γ Λ)

@[simp] lemma continuousActionCLM_apply (Λ : Finset S) (f : Obs) :
    continuousActionCLM γ Λ f = continuousAction γ Λ f :=
  rfl

lemma continuous_continuousAction (Λ : Finset S) :
    Continuous (continuousAction γ Λ : Obs → Obs) :=
  (continuousActionCLM γ Λ).continuous

end Action

/-! ### Continuous/Feller quasilocality -/

section Quasilocal

variable (γ : Specification S E)
variable [γ.IsFeller]

open BoundedContinuousFunction

/-- A specification is **Feller-quasilocal** if its Feller action preserves continuous
Feller-quasilocal observables. -/
def IsFellerQuasilocal : Prop :=
  ∀ (Λ : Finset S) (f : Obs),
    f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) →
      continuousAction γ Λ f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ)

/-- Compatibility alias for the current continuous/Feller quasilocality predicate. Prefer
`IsFellerQuasilocal` in new statements. -/
abbrev IsQuasilocal : Prop :=
  IsFellerQuasilocal γ

/-- Dense-check version: it suffices to verify Feller-quasilocality on cylinder observables. -/
def IsFellerQuasilocalOnCylinder : Prop :=
  ∀ (Λ : Finset S) (f : Obs),
    f ∈ cylinderFunctions (S := S) (E := E) (F := ℝ) →
      continuousAction γ Λ f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ)

/-- Compatibility alias for the dense-check predicate. Prefer
`IsFellerQuasilocalOnCylinder` in new statements. -/
abbrev IsQuasilocal' : Prop :=
  IsFellerQuasilocalOnCylinder γ

lemma IsFellerQuasilocal.of_onCylinder
    (h : IsFellerQuasilocalOnCylinder γ) : IsFellerQuasilocal γ := by
  intro Λ f hf
  have hf' : f ∈ closure (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs) := by
    simpa [fellerQuasilocalFunctions, Submodule.topologicalClosure_coe] using hf
  have h_cont : Continuous (continuousAction γ Λ : Obs → Obs) :=
    continuous_continuousAction γ Λ
  have himage :
      continuousAction γ Λ f ∈
        closure
          ((continuousAction γ Λ) ''
            (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs)) :=
    by
      let s : Set Obs := (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs)
      have hx : continuousAction γ Λ f ∈ (continuousAction γ Λ) '' closure s :=
        ⟨f, hf', rfl⟩
      exact (image_closure_subset_closure_image h_cont (s := s)) hx
  have hsubset :
      (continuousAction γ Λ) '' (cylinderFunctions (S := S) (E := E) (F := ℝ) : Set Obs) ⊆
        (fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) := by
    intro g hg
    rcases hg with ⟨f0, hf0, rfl⟩
    exact h Λ f0 hf0
  have hclosed :
      IsClosed (fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) :=
    Submodule.isClosed_topologicalClosure _
  have :
      continuousAction γ Λ f ∈
        closure (fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) : Set Obs) :=
    closure_mono hsubset himage
  simpa [hclosed.closure_eq, fellerQuasilocalFunctions] using this

lemma IsQuasilocal.of_IsQuasilocal' (h : IsQuasilocal' γ) : IsQuasilocal γ :=
  IsFellerQuasilocal.of_onCylinder γ h

lemma IsFellerQuasilocal_iff_onCylinder :
    IsFellerQuasilocal γ ↔ IsFellerQuasilocalOnCylinder γ := by
  constructor
  · intro h Λ f hf
    -- Cylinder observables are Feller-quasilocal by definition.
    have hf' : f ∈ fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) :=
      cylinderFunctions_le_fellerQuasilocalFunctions (S := S) (E := E) (F := ℝ) hf
    exact h Λ f hf'
  · intro h
    exact IsFellerQuasilocal.of_onCylinder γ h

lemma IsQuasilocal_iff_IsQuasilocal' :
    IsQuasilocal γ ↔ IsQuasilocal' γ := by
  exact IsFellerQuasilocal_iff_onCylinder γ

end Quasilocal

end Specification

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Prereqs.Kernel.Feller
public import GibbsMeasure.Specification
public import Mathlib.Topology.Continuous

/-!
# Feller specifications

`Specification.IsFeller`: a specification whose kernels are all Feller
(`ProbabilityTheory.Kernel.IsFeller`), the hypothesis under which weak-convergence existence
arguments run (`Specification/Existence.lean`). The induced action on bounded continuous
observables is the kernel-level `ProbabilityTheory.Kernel.continuousAction` of
`Prereqs/Kernel/Feller.lean`; this file adds nothing beyond the class.
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


end Specification

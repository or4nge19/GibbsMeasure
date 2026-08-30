/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Topology.ClusterPoints
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-!
# Metrizability of the topology of local convergence

**Georgii Remark (4.3)(3).** When the state space `E` is finite and the site set `S` is countable,
Georgii's algebra `𝓕⁰` of local events (`localEvents S E`) is countable, so the topology of local
convergence on `ProbabilityMeasure (S → E)` is metrizable: by `isInducing_evalProb` it is the
initial topology of the evaluation map into the countable product `↥(localEvents S E) → ℝ≥0∞`,
which is metrizable. Together with Georgii (4.11)(2) (`CompactSpace`), the space of random fields
over a finite state space is then compact metrizable.
-/

@[expose] public section


open Set Filter Topology TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (4.3)(3).** Over a countable site set and a finite state space, the local events
form a countable family. -/
lemma countable_localEvents [Countable S] [Finite E] : (localEvents S E).Countable := by
  refine (Set.countable_iUnion fun Λ : Finset S ↦
    Set.countable_range fun B : Set (Π _ : Λ, E) ↦ Λ.restrict ⁻¹' B).mono ?_
  intro A hA
  obtain ⟨Λ, B, -, rfl⟩ := mem_localEvents_iff_exists_finsetRestrict_preimage.1 hA
  exact Set.mem_iUnion.2 ⟨Λ, Set.mem_range_self B⟩

/-- Over a countable site set and a finite state space, the type of local events is countable. -/
instance [Countable S] [Finite E] : Countable (localEvents S E) :=
  countable_localEvents.to_subtype

/-- **Georgii (4.3)(3).** Over a countable site set and a finite state space, the topology of
local convergence is pseudo-metrizable. -/
instance [Countable S] [Finite E] : PseudoMetrizableSpace (WithLocalConvergence S E) :=
  WithSetwiseTopology.isInducing_evalProb.pseudoMetrizableSpace

/-- **Georgii (4.3)(3).** Over a countable site set and a finite state space, the topology of
local convergence is metrizable. -/
instance [Countable S] [Finite E] : MetrizableSpace (WithLocalConvergence S E) :=
  PseudoMetrizableSpace.toMetrizableSpace

/-! ### Corollary: the space of random fields over a finite state space is compact metrizable -/



/-- **Georgii (4.3)(3) + (4.11)(2).** Over a countable site set and a finite (discrete) state
space, the space of random fields is compact metrizable. -/
lemma compactSpace_and_metrizableSpace_withLocalConvergence [Countable S] [Finite E]
    [MeasurableSingletonClass E] :
    CompactSpace (WithLocalConvergence S E) ∧ MetrizableSpace (WithLocalConvergence S E) :=
  ⟨inferInstance, inferInstance⟩

/-- Over a countable site set and a finite (discrete) state space, the space of random fields is
completely metrizable, being compact metrizable. -/
instance [Countable S] [Finite E] [MeasurableSingletonClass E] :
    IsCompletelyMetrizableSpace (WithLocalConvergence S E) :=
  letI : UniformSpace (WithLocalConvergence S E) := pseudoMetrizableSpaceUniformity _
  haveI := pseudoMetrizableSpaceUniformity_countably_generated (WithLocalConvergence S E)
  IsCompletelyMetrizableSpace.of_completeSpace_metrizable

/-- **Georgii (4.3)(3) + (4.11)(2).** Over a countable site set and a finite (discrete) state
space, the space of random fields is Polish. -/
instance [Countable S] [Finite E] [MeasurableSingletonClass E] :
    PolishSpace (WithLocalConvergence S E) where

end MeasureTheory

end

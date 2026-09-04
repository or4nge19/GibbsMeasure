/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.UniformSpace.Pi

/-!
# Countable products of (pseudo-)metrizable spaces

Mathlib's `TopologicalSpace.pseudoMetrizableSpace_pi` and `TopologicalSpace.metrizableSpace_pi`
are stated for a *finite* index type. The same proof — choose a compatible pseudo-metric on each
factor; the product uniformity of countably many countably generated uniformities is countably
generated (`Pi.instIsCountablyGeneratedUniformity`), hence pseudo-metrizable — gives the countable
case, which is the one needed for configuration spaces `S → E` over a countable site set `S`.
Metrizability of the product then follows from `T0Space` of the product
(`TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`).
-/

@[expose] public section

namespace TopologicalSpace

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

/-- A countable product of pseudo-metrizable spaces is pseudo-metrizable. -/
instance pseudoMetrizableSpace_pi_countable [Countable ι] [∀ i, PseudoMetrizableSpace (X i)] :
    PseudoMetrizableSpace (∀ i, X i) :=
  let := fun i ↦ pseudoMetrizableSpaceUniformity (X i)
  have := fun i ↦ pseudoMetrizableSpaceUniformity_countably_generated (X i)
  inferInstance

/-- A countable product of metrizable spaces is metrizable. -/
example [Countable ι] [∀ i, MetrizableSpace (X i)] : MetrizableSpace (∀ i, X i) := inferInstance

end TopologicalSpace

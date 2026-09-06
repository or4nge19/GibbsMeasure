/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Ergodicity
public import GibbsMeasure.Topology.CountableCore

/-!
# `𝓟_Θ` in the `𝒞`-topology of a countable core

Georgii's Step 3 in the proof of the large-deviation upper bound (15.46) replaces the topology
`𝓛` of local convergence on the shift-invariant random fields `𝓟_Θ` by the `𝒞`-topology of a
countable core `𝒞 ⊆ 𝓕⁰` of cylinder events (Corollary (4.A13)), in which `𝓟(Ω, 𝓕)` is compact
metrizable (Comment (4.A10)(1)). This file records that `𝓟_Θ` is closed, hence compact, in that
topology — for a core stable under the relabellings in `Θ`, which is what
`MeasureTheory.GibbsMeasure.exists_isCountableCore_subset_localEvents_forall_preimage` provides
and what the shift group satisfies.

The stability hypothesis is genuinely needed; see the module documentation of
`GibbsMeasure/Topology/CountableCore.lean` for the counterexample without it, and for the reason
why the change of topology does **not** deliver Georgii's Step 3 as he states it: the Choquet
argument in the `𝒞`-topology bounds the infimum over the `𝒞`-closure of `C`, not over its closure
in the topology of local convergence. `Specification/LargeDeviationsUpper.lean` therefore proves
(15.46) over a standard Borel state space with Georgii's `cx̄ C` on the right, which is a stronger
statement than the one this file would supply.

## Main statements

* `MeasureTheory.GibbsMeasure.isClosed_setOf_mem_invariantFields_withCoreTopology`: `𝓟_Θ` is
  `𝒞`-closed.
* `MeasureTheory.GibbsMeasure.exists_isCountableCore_isCompact_setOf_mem_invariantFields`: over a
  countable additive site group and a standard Borel state space there is a countable core of
  local events in whose topology `𝓟_Θ` is **compact** — Georgii's change of topology, for the
  shift group.
-/

@[expose] public section

open MeasurableSpace Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (14.1) in the `𝒞`-topology.** `𝓟_Θ` is closed in the topology of setwise
convergence along a countable core `𝒞` stable under the preimages along `Θ`. -/
theorem isClosed_setOf_mem_invariantFields_withCoreTopology {𝒞 : Set (Set (S → E))}
    (h𝒞 : IsCountableCore 𝒞) (Θ : Subgroup (Transformation S E))
    (hstab : ∀ τ ∈ Θ, ∀ A ∈ 𝒞, τ.toFun ⁻¹' A ∈ 𝒞) :
    IsClosed {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
      (μ.toMeasure : Measure (S → E)) ∈ invariantFields Θ} := by
  have hset : {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
        (μ.toMeasure : Measure (S → E)) ∈ invariantFields Θ}
      = {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
        ∀ τ ∈ (Θ : Set (Transformation S E)),
          MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
    ext μ
    simp only [Set.mem_ofPred_eq, mem_invariantFields_iff, SetLike.mem_coe]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨μ.toMeasure.2, h⟩⟩
  rw [hset]
  exact isClosed_setOf_forall_measurePreserving_withCoreTopology h𝒞 _ hstab

/-- **Georgii, Comment (4.A10)(1) for `𝓟_Θ`.** `𝓟_Θ` is compact in the `𝒞`-topology of a
countable core stable under the preimages along `Θ`. -/
theorem isCompact_setOf_mem_invariantFields_withCoreTopology {𝒞 : Set (Set (S → E))}
    (h𝒞 : IsCountableCore 𝒞) (Θ : Subgroup (Transformation S E))
    (hstab : ∀ τ ∈ Θ, ∀ A ∈ 𝒞, τ.toFun ⁻¹' A ∈ 𝒞) :
    IsCompact {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
      (μ.toMeasure : Measure (S → E)) ∈ invariantFields Θ} :=
  letI := compactSpace_withCoreTopology h𝒞
  (isClosed_setOf_mem_invariantFields_withCoreTopology h𝒞 Θ hstab).isCompact

/-- **Georgii's change of topology in the proof of (15.46).** Over a countable additive group of
sites and a standard Borel state space there is a countable core `𝒞 ⊆ 𝓕⁰` of local events such
that the shift-invariant random fields `𝓟_Θ` are compact in the `𝒞`-topology — which, by
`MeasureTheory.GibbsMeasure.continuous_ofMeasure_withLocalConvergence`, is coarser than the
topology of local convergence. -/
theorem exists_isCountableCore_isCompact_setOf_mem_invariantFields [AddGroup S] [Countable S]
    [StandardBorelSpace E] :
    ∃ 𝒞 ⊆ localEvents S E, IsCountableCore 𝒞 ∧
      IsCompact {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
        (μ.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)} := by
  obtain ⟨𝒞, hsub, hcore, hstab⟩ :=
    exists_isCountableCore_subset_localEvents_forall_preimage (E := E)
      (shiftGroup S E : Set (Transformation S E)) (by rintro τ ⟨j, rfl⟩ i; rfl)
  exact ⟨𝒞, hsub, hcore,
    isCompact_setOf_mem_invariantFields_withCoreTopology hcore _ fun τ hτ ↦ hstab τ hτ⟩

end MeasureTheory.GibbsMeasure

end

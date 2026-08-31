/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Prereqs.Transformation

/-!
# Invariant random fields

Georgii, remark after (5.12): the `I`-invariant random fields `𝒫_I(Ω, 𝓕)` are closed in the
topology of local convergence, and so is the set `𝒢_I(γ)` of (5.13) of `I`-invariant Gibbs
measures of a quasilocal specification.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

open Transformation

variable {S E : Type*} [MeasurableSpace E]

namespace Transformation

/-- The preimage of a local event under a transformation is a local event (Georgii, after
(5.12): `f ∘ τ ∈ 𝓛` for `f ∈ 𝓛`). -/
lemma preimage_mem_localEvents (τ : Transformation S E) {A : Set (S → E)}
    (hA : A ∈ localEvents S E) : τ.toFun ⁻¹' A ∈ localEvents S E := by
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  refine mem_localEvents_of_cylinderEvents (Λ.preimage τ.sites τ.sites.injective.injOn) ?_
  rw [Finset.coe_preimage]
  exact τ.measurable_toFun_cylinderEvents (Λ : Set S) hΛ

/-- The `τ`-image `μ ↦ τ(μ) = μ ∘ τ⁻¹` is continuous for the topology of local convergence
(Georgii, after (5.12)). -/
lemma continuous_map_withLocalConvergence (τ : Transformation S E) :
    Continuous fun μ : WithLocalConvergence S E ↦
      (WithSetwiseTopology.ofMeasure (μ.toMeasure.map τ.measurable_toFun.aemeasurable) :
        WithLocalConvergence S E) := by
  refine continuous_iff_continuousAt.2 fun μ ↦ ?_
  rw [ContinuousAt, tendsto_withLocalConvergence_iff]
  intro A hA
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply τ.measurable_toFun hAm]
  exact tendsto_withLocalConvergence_iff.1 tendsto_id _ (τ.preimage_mem_localEvents hA)

end Transformation

/-! ### Georgii, remark after (5.12): invariant random fields are `L`-closed -/

/-- **Georgii, remark after (5.12).** The `τ`-invariant random fields `{μ : τ(μ) = μ}` are closed
in the topology of local convergence.  ((5.12) itself is the *definition* of `𝒫_I(Ω, 𝓕)`.) -/
theorem isClosed_setOf_measurePreserving (τ : Transformation S E) :
    IsClosed {μ : WithLocalConvergence S E |
      MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  convert isClosed_eq τ.continuous_map_withLocalConvergence continuous_id using 1
  ext μ
  simp only [mem_ofPred_eq, id_eq]
  rw [← WithSetwiseTopology.toMeasure_injective.eq_iff,
    ← ProbabilityMeasure.toMeasure_injective.eq_iff]
  exact ⟨fun h ↦ h.map_eq, fun h ↦ ⟨τ.measurable_toFun, h⟩⟩

/-- **Georgii, remark after (5.12).** The `I`-invariant random fields `𝒫_I` are closed in the
topology of local convergence. -/
theorem isClosed_setOf_forall_measurePreserving (I : Set (Transformation S E)) :
    IsClosed {μ : WithLocalConvergence S E |
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  have : {μ : WithLocalConvergence S E |
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} =
      ⋂ τ ∈ I, {μ : WithLocalConvergence S E |
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
    ext μ; simp
  rw [this]
  exact isClosed_biInter fun τ _ ↦ isClosed_setOf_measurePreserving τ

/-! ### The set `𝒢_I(γ)` of Georgii (5.13) is `L`-closed -/

/-- The set `𝒢_I(γ) = 𝒢(γ) ∩ 𝒫_I` of Georgii (5.13) is closed in the topology of local
convergence, by the remark after (5.12) together with the closedness of `𝒢(γ)` for a quasilocal
`γ` (`isClosed_setOf_mem_GP`).  No `I`-invariance of `γ` is needed, although Georgii introduces
`𝒢_I(γ)` for an `I`-invariant `γ`. -/
theorem isClosed_setOf_mem_GP_and_measurePreserving {γ : Specification S E}
    (hγ : γ.IsQuasilocal) (I : Set (Transformation S E)) :
    IsClosed {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  rw [ofPred_and]
  exact (isClosed_setOf_mem_GP hγ).inter (isClosed_setOf_forall_measurePreserving I)

end MeasureTheory.GibbsMeasure

end

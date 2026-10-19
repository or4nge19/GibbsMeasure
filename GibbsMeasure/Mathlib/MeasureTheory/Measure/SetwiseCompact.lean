/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.CountableCore
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithSetwiseTopology
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Sequences

/-!
# Compactness of the setwise topology along a countable core

For a countable family `𝒞` of events, the topology of setwise convergence along `𝒞` on
`ProbabilityMeasure Ω` (`MeasureTheory.WithSetwiseTopology`) is metrizable, being the initial
topology of a map into the countable product `𝒞 → ℝ≥0∞`. If `𝒞` is moreover a **countable core**
(`MeasurableSpace.IsCountableCore`), the space of probability measures is *compact*: the range of
the evaluation map is sequentially closed in the compact metrizable product, precisely by
condition (4.A9)(ii).

This is Georgii's Comment (4.A10)(1). Georgii metrises the topology by the explicit metric
`d(μ, ν) = ∑ₙ 2⁻ⁿ |μ Aₙ − ν Aₙ|` for an enumeration `(Aₙ)` of `𝒞`; that metric is not constructed
here, because everything it is used for is carried by `MetrizableSpace` together with the
description of its convergent sequences,
`MeasureTheory.WithSetwiseTopology.tendsto_prob_iff` — `d`-convergence *is* setwise convergence on
`𝒞`. His diagonal extraction is the compactness of `𝒞 → ℝ≥0∞`.

## Main statements

* `MeasureTheory.WithSetwiseTopology.instPseudoMetrizableSpace`: metrizability for countable `𝒞`.
* `MeasureTheory.WithSetwiseTopology.compactSpace_of_isCountableCore`,
  `…metrizableSpace_of_isCountableCore`, `…seqCompactSpace_of_isCountableCore`: **Georgii
  (4.A10)(1)**, `𝓟(Ω, 𝓕)` is compact metrizable in the `𝒞`-topology of a countable core.
* `MeasureTheory.WithSetwiseTopology.continuous_ofMeasure_of_subset`: the `𝒞`-topology is coarser
  than the `𝒟`-topology when `𝒞 ⊆ 𝒟`. With `𝒟` the local events this is Georgii's "the
  `𝒞`-topology is coarser than the `𝓛`-topology". Compactness therefore transfers from the finer
  topology to the coarser one (`…isCompact_image_of_subset`), and along a countable core it
  turns into closedness (`…isClosed_image_of_isCompact`).
* `MeasureTheory.WithSetwiseTopology.isClosed_setOf_measurePreserving`: the measures invariant
  under a measurable map `f` are `𝒞`-closed **as soon as `𝒞` is stable under `f⁻¹`**. Stability is
  not automatic and cannot be dropped: see the module documentation of
  `GibbsMeasure/Topology/CountableCore.lean`.
-/

@[expose] public section

open Filter MeasurableSpace Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

namespace WithSetwiseTopology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝒞 𝒟 : Set (Set Ω)}

/-- A countable core separates probability measures: it is a generating π-system. -/
lemma _root_.MeasurableSpace.IsCountableCore.separatesOn (h : IsCountableCore 𝒞) :
    SeparatesOn 𝒞 (fun μ ↦ IsProbabilityMeasure μ) :=
  separatesOn_of_isPiSystem_of_generateFrom h.isPiSystem h.generateFrom_eq.symm

/-- Along a countable family of events, the setwise topology on probability measures is
pseudo-metrizable: it is induced from the countable product `𝒞 → ℝ≥0∞`. -/
instance instPseudoMetrizableSpace [Countable 𝒞] :
    PseudoMetrizableSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) :=
  isInducing_evalProb.pseudoMetrizableSpace

/-- **Georgii (4.A10)(1).** In the topology of setwise convergence along a countable core, the
space of probability measures is compact.

The evaluation `μ ↦ (A ↦ μ A)` embeds it in the compact metrizable product `𝒞 → ℝ≥0∞`, with
sequentially closed range: a sequence in the range converges pointwise on `𝒞`, so condition
(4.A9)(ii) provides a probability measure realising the limit. -/
theorem compactSpace_of_isCountableCore (h : IsCountableCore 𝒞) :
    CompactSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) := by
  have hcount : Countable 𝒞 := h.countable.to_subtype
  refine Topology.IsClosedEmbedding.compactSpace (f := evalProb (Ω := Ω) 𝒞) ⟨⟨isInducing_evalProb,
    ?_⟩, ?_⟩
  · rintro ⟨μ⟩ ⟨ν⟩ hμν
    have : (μ : Measure Ω) = ν :=
      h.separatesOn μ.2 ν.2 fun A hA ↦ congrArg (fun g ↦ g ⟨A, hA⟩) hμν
    simp [ProbabilityMeasure.toMeasure_injective this]
  · refine IsSeqClosed.isClosed fun {g y} hg hy ↦ ?_
    choose μ hμ using hg
    have hcoord : ∀ A : 𝒞, Tendsto (fun n ↦ ((μ n).toMeasure : Measure Ω) A.1) atTop (𝓝 (y A)) :=
      fun A ↦ by
        have := (tendsto_pi_nhds.1 hy) A
        simpa only [← hμ, evalProb] using this
    obtain ⟨ν, hν, htends⟩ := h.exists_isProbabilityMeasure_tendsto
      (fun n ↦ ((μ n).toMeasure : Measure Ω)) (fun n ↦ (μ n).toMeasure.2)
      fun A hA ↦ ⟨y ⟨A, hA⟩, hcoord ⟨A, hA⟩⟩
    refine ⟨ofMeasure ⟨ν, hν⟩, funext fun A ↦ ?_⟩
    exact tendsto_nhds_unique (htends A.1 A.2) (hcoord A)

/-- **Georgii (4.A10)(1).** The `𝒞`-topology of a countable core is metrizable. -/
theorem metrizableSpace_of_isCountableCore (h : IsCountableCore 𝒞) :
    MetrizableSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) := by
  have : Countable 𝒞 := h.countable.to_subtype
  have : T2Space (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) :=
    t2Space_probabilityMeasure h.separatesOn
  exact PseudoMetrizableSpace.toMetrizableSpace

/-- **Georgii (4.A10)(1), the diagonal argument.** In the `𝒞`-topology of a countable core, every
sequence of probability measures has a convergent subsequence. -/
theorem seqCompactSpace_of_isCountableCore (h : IsCountableCore 𝒞) :
    SeqCompactSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) := by
  have : Countable 𝒞 := h.countable.to_subtype
  have := compactSpace_of_isCountableCore h
  exact compactSpace_iff_seqCompactSpace.1 this

/-- Along a countable core the setwise topology is Hausdorff. -/
theorem t2Space_of_isCountableCore (h : IsCountableCore 𝒞) :
    T2Space (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) :=
  t2Space_probabilityMeasure h.separatesOn

/-! ### Comparison of setwise topologies -/

/-- Setwise convergence along a larger family is finer: the identity is continuous from the
`𝒟`-topology to the `𝒞`-topology when `𝒞 ⊆ 𝒟`. -/
theorem continuous_ofMeasure_of_subset (h : 𝒞 ⊆ 𝒟) :
    Continuous fun μ : WithSetwiseTopology 𝒟 (ProbabilityMeasure Ω) ↦
      (ofMeasure μ.toMeasure : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) := by
  rw [isInducing_evalProb.continuous_iff]
  exact continuous_pi fun A ↦ continuous_apply_enn (h A.2)

/-- A set of probability measures compact for a finer setwise topology is compact for a coarser
one. -/
theorem isCompact_image_of_subset (h : 𝒞 ⊆ 𝒟)
    {P : Set (WithSetwiseTopology 𝒟 (ProbabilityMeasure Ω))} (hP : IsCompact P) :
    IsCompact ((fun μ ↦ (ofMeasure μ.toMeasure : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)))
      '' P) :=
  hP.image (continuous_ofMeasure_of_subset h)

/-- **Georgii's transfer of the level sets in the proof of (15.46).** A set of probability
measures compact for a finer setwise topology is closed in the `𝒞`-topology of a countable core,
which is Hausdorff. This is what keeps a functional with compact level sets lower semicontinuous
after the change of topology. -/
theorem isClosed_image_of_isCompact (h𝒞 : IsCountableCore 𝒞) (h : 𝒞 ⊆ 𝒟)
    {P : Set (WithSetwiseTopology 𝒟 (ProbabilityMeasure Ω))} (hP : IsCompact P) :
    IsClosed ((fun μ ↦ (ofMeasure μ.toMeasure : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)))
      '' P) :=
  letI := t2Space_of_isCountableCore h𝒞
  (isCompact_image_of_subset h hP).isClosed

/-! ### Invariant measures -/

/-- The probability measures invariant under a measurable map `f` are closed in the setwise
topology along a generating π-system `𝒞` **which is stable under `f⁻¹`**.

Stability is essential, and it is what Georgii's shift-invariant random fields `𝓟_Θ` use: for a
Borel automorphism `f` and a core `𝒞` not stable under `f⁻¹`, a setwise limit along `𝒞` of
`f`-invariant measures need not be `f`-invariant. -/
theorem isClosed_setOf_measurePreserving (hpi : IsPiSystem 𝒞)
    (hgen : MeasurableSpace.generateFrom 𝒞 = mΩ) {f : Ω → Ω} (hf : Measurable f)
    (hstab : ∀ A ∈ 𝒞, f ⁻¹' A ∈ 𝒞) :
    IsClosed {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
      MeasurePreserving f (μ.toMeasure : Measure Ω) (μ.toMeasure : Measure Ω)} := by
  have hset : {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
        MeasurePreserving f (μ.toMeasure : Measure Ω) (μ.toMeasure : Measure Ω)}
      = ⋂ A ∈ 𝒞, {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
        ((μ.toMeasure : Measure Ω)) (f ⁻¹' A) = ((μ.toMeasure : Measure Ω)) A} := by
    ext μ
    simp only [mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro hmp A hA
      have hAm : MeasurableSet A := hgen ▸ measurableSet_generateFrom hA
      rw [← Measure.map_apply hf hAm, hmp.map_eq]
    · intro hall
      refine ⟨hf, ?_⟩
      have : IsProbabilityMeasure ((μ.toMeasure : Measure Ω).map f) :=
        inferInstance
      refine ext_of_generate_finite 𝒞 hgen.symm hpi (fun A hA ↦ ?_) (by simp)
      rw [Measure.map_apply hf (hgen ▸ measurableSet_generateFrom hA)]
      exact hall A hA
  rw [hset]
  exact isClosed_biInter fun A hA ↦
    isClosed_eq (continuous_apply_enn (hstab A hA)) (continuous_apply_enn hA)

/-- The probability measures invariant under every map of a family `I` are closed in the setwise
topology along an `I`-stable generating π-system. -/
theorem isClosed_setOf_forall_measurePreserving {ζ : Type*} (I : Set ζ) (f : ζ → Ω → Ω)
    (hpi : IsPiSystem 𝒞) (hgen : MeasurableSpace.generateFrom 𝒞 = mΩ)
    (hf : ∀ τ ∈ I, Measurable (f τ)) (hstab : ∀ τ ∈ I, ∀ A ∈ 𝒞, f τ ⁻¹' A ∈ 𝒞) :
    IsClosed {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
      ∀ τ ∈ I, MeasurePreserving (f τ) (μ.toMeasure : Measure Ω) (μ.toMeasure : Measure Ω)} := by
  have hset : {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
        ∀ τ ∈ I, MeasurePreserving (f τ) (μ.toMeasure : Measure Ω) (μ.toMeasure : Measure Ω)}
      = ⋂ τ ∈ I, {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) |
        MeasurePreserving (f τ) (μ.toMeasure : Measure Ω) (μ.toMeasure : Measure Ω)} := by
    ext μ; simp
  rw [hset]
  exact isClosed_biInter fun τ hτ ↦
    isClosed_setOf_measurePreserving hpi hgen (hf τ hτ) (hstab τ hτ)

end WithSetwiseTopology

end MeasureTheory

end

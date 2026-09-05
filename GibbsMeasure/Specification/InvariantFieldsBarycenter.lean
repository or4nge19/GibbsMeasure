/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.BarycenterJensen
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.SetwiseEmbedding
public import GibbsMeasure.Specification.Ergodicity
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Topology.Metrizable

/-!
# `𝓟_Θ` as a compact convex set, and Georgii (15.54)

Georgii's Step 3 in the proof of the large-deviation upper bound (15.46) needs convex analysis on
the set `𝓟_Θ` of shift-invariant random fields. To apply it he changes the topology: by Corollary
(4.A13) the σ-algebra of a standard Borel configuration space has a *countable core* `𝒞` of
cylinder events, and by Comment (4.A10)(1) the `𝒞`-topology turns `𝓟(Ω, 𝓕)` into a compact
metrizable set.

**Over a finite state space and a countable site set the change of topology is unnecessary**: the
algebra `𝓕⁰ = localEvents S E` of *all* local events is already countable
(`MeasureTheory.countable_localEvents`) and the space of random fields is already compact
metrizable in the topology `𝓛` of local convergence (`MeasureTheory.instCompactSpace…`,
`MeasureTheory.instMetrizableSpace…`). One may therefore take `𝒞 = 𝓕⁰`, and then the
`𝒞`-topology *is* the `𝓛`-topology. What remains to be supplied is the ambient *vector space*: the
locally convex Polish space `𝓕⁰ → ℝ`, into which the random fields are embedded by evaluation
`μ ↦ (A ↦ μ.real A)` (`MeasureTheory.WithSetwiseTopology.evalReal`).

## Main statements

* `MeasureTheory.GibbsMeasure.isClosedEmbedding_evalLocalEvents`: over a countable site set and a
  finite state space, `μ ↦ (A ↦ μ.real A)` is a closed topological embedding of the random fields
  with the topology of local convergence into `localEvents S E → ℝ`.
* `MeasureTheory.GibbsMeasure.isCompact_image_evalLocalEvents`,
  `MeasureTheory.GibbsMeasure.convex_image_evalLocalEvents`: the image of a closed,
  mixture-stable set of random fields — `𝓟_Θ` in particular, by
  `MeasureTheory.GibbsMeasure.convex_image_invariantFields_shiftGroup` — is a **compact convex**
  subset of that space.
* `MeasureTheory.GibbsMeasure.exists_isBarycenter_lintegral_eq`: **Georgii's display before
  (15.54)** — a random field `μ` in the closed convex hull `cx̄ C` of `C ⊆ 𝓟_Θ` is the barycentre
  of a probability measure `w_μ` carried by (the image of) `C`, and every affine lower
  semicontinuous `𝒜 : 𝓟_Θ → [0, ∞]` satisfies `𝒜(μ) = ∫ 𝒜(ν) w_μ(dν)`. The representation is
  `MeasureTheory.exists_isBarycenter_of_mem_closedConvexHull` and the identity is Phelps'
  Lemma 9.7, `MeasureTheory.IsBarycenter.lintegral_eq_of_affineENNReal`.
* `MeasureTheory.GibbsMeasure.iInf_closedConvexHull_eq_iInf_closure_evalLocalEvents`: **Georgii
  (15.54)** in the ambient vector space, and
  `MeasureTheory.GibbsMeasure.iInf_closedConvexHull_eq_iInf_closure_of_lowerSemicontinuousOn`:
  Georgii (15.54) for a functional `𝒜 : 𝓟_Θ → [0, ∞]` on the random fields themselves — the
  infimum of an affine (indeed only concave) lower semicontinuous `𝒜` over the smallest
  `𝓛`-closed mixture-stable set containing `C` equals its infimum over the `𝓛`-closure of `C`.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- Evaluation of a random field on the algebra `𝓕⁰` of local events: the embedding of the space
of random fields into the locally convex Polish space `localEvents S E → ℝ`. -/
abbrev evalLocalEvents (S E : Type*) [MeasurableSpace E] :
    WithLocalConvergence S E → (localEvents S E → ℝ) :=
  WithSetwiseTopology.evalReal (localEvents S E)

section Embedding

variable [Countable S] [Finite E] [MeasurableSingletonClass E]

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii (4.3)(1) + Comment (4.A10).** Evaluation on the local events is a topological
embedding of the random fields into `localEvents S E → ℝ`: the local events separate probability
measures, and the topology of local convergence is by definition the induced topology. -/
theorem isEmbedding_evalLocalEvents : Topology.IsEmbedding (evalLocalEvents S E) :=
  WithSetwiseTopology.isEmbedding_evalReal separatesOn_localEvents

omit [Countable S] in
/-- Over a finite state space the space of random fields is compact, so the embedding of
`isEmbedding_evalLocalEvents` is a *closed* embedding. -/
theorem isClosedEmbedding_evalLocalEvents : Topology.IsClosedEmbedding (evalLocalEvents S E) :=
  WithSetwiseTopology.continuous_evalReal.isClosedEmbedding
    (WithSetwiseTopology.injective_evalReal separatesOn_localEvents)

omit [Countable S] in
/-- The image of a closed set of random fields is compact. -/
theorem isCompact_image_evalLocalEvents {P : Set (WithLocalConvergence S E)} (hP : IsClosed P) :
    IsCompact (evalLocalEvents S E '' P) :=
  (hP.isCompact).image WithSetwiseTopology.continuous_evalReal

omit [Countable S] in
/-- The image of a closed set of random fields is closed. -/
theorem isClosed_image_evalLocalEvents {P : Set (WithLocalConvergence S E)} (hP : IsClosed P) :
    IsClosed (evalLocalEvents S E '' P) :=
  (isCompact_image_evalLocalEvents hP).isClosed

omit [Countable S] in
/-- Closures are preserved by the embedding. -/
theorem image_closure_evalLocalEvents (C : Set (WithLocalConvergence S E)) :
    evalLocalEvents S E '' closure C = closure (evalLocalEvents S E '' C) :=
  (isClosedEmbedding_evalLocalEvents.closure_image_eq C).symm

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- **Convexity of the image.** If `P` is stable under mixtures then its image in
`localEvents S E → ℝ` is convex. -/
theorem convex_image_evalLocalEvents {P : Set (WithLocalConvergence S E)}
    (hP : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E))) :
    Convex ℝ (evalLocalEvents S E '' P) :=
  WithSetwiseTopology.convex_image_evalReal hP

end Embedding


/-! ### `𝓟_Θ` is compact and convex -/

section InvariantFields

variable [Countable S] [Finite E] [MeasurableSingletonClass E]

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii (14.1).** `𝓟_Θ`, as a set of random fields with the topology of local convergence:
the `Θ`-invariant probability measures. -/
theorem isClosed_setOf_mem_invariantFields (Θ : Subgroup (Transformation S E)) :
    IsClosed {μ : WithLocalConvergence S E |
      (μ.toMeasure : Measure (S → E)) ∈ invariantFields Θ} := by
  have : {μ : WithLocalConvergence S E |
        (μ.toMeasure : Measure (S → E)) ∈ invariantFields Θ}
      = {μ : WithLocalConvergence S E |
        ∀ τ ∈ (Θ : Set (Transformation S E)),
          MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
    ext μ
    simp only [Set.mem_ofPred_eq, mem_invariantFields_iff, SetLike.mem_coe]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨μ.toMeasure.2, h⟩⟩
  rw [this]
  exact isClosed_setOf_forall_measurePreserving _

variable [AddGroup S]

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii (14.1): `𝓟_Θ` is convex.** Convex combinations of shift-invariant random fields are
shift invariant, so the image of `𝓟_Θ` in `localEvents S E → ℝ` is convex. -/
theorem convex_image_invariantFields_shiftGroup :
    Convex ℝ (evalLocalEvents S E ''
      {μ : WithLocalConvergence S E |
        (μ.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)}) := by
  refine convex_image_evalLocalEvents fun μ hμ ν hν a b ha hb hab ↦ ?_
  have hst : a.toNNReal + b.toNNReal = 1 := by
    rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have hmix := smul_add_smul_mem_invariantFields_shiftGroup hμ hν hst
  refine ⟨⟨⟨_, hmix.1⟩⟩, hmix, ?_⟩
  have : (a.toNNReal : ℝ≥0) • (μ.toMeasure : Measure (S → E))
        + (b.toNNReal : ℝ≥0) • (ν.toMeasure : Measure (S → E))
      = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
        + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)) := by
    rw [ENNReal.smul_def, ENNReal.smul_def]; rfl
  exact this

omit [Countable S] in
/-- **`𝓟_Θ` is a compact convex subset of a locally convex Polish space.** This is what Georgii's
Step 3 needs in order to apply Choquet theory; over a finite state space no change of topology is
required. -/
theorem isCompact_and_convex_image_invariantFields_shiftGroup :
    IsCompact (evalLocalEvents S E ''
        {μ : WithLocalConvergence S E |
          (μ.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)}) ∧
      Convex ℝ (evalLocalEvents S E ''
        {μ : WithLocalConvergence S E |
          (μ.toMeasure : Measure (S → E)) ∈ invariantFields (shiftGroup S E)}) :=
  ⟨isCompact_image_evalLocalEvents (isClosed_setOf_mem_invariantFields _),
    convex_image_invariantFields_shiftGroup⟩

end InvariantFields

/-! ### Georgii (15.54) in the ambient vector space -/

section Georgii1554

variable [Countable S] [Finite E] [MeasurableSingletonClass E]

/-- **Georgii (15.54)**, in the ambient locally convex space `localEvents S E → ℝ`: for a concave
(in particular affine) lower semicontinuous `g : 𝓟 → [0, ∞]` on the image of a closed
mixture-stable set `P` of random fields, the infimum of `g` over the closed convex hull of the
image of `C ⊆ P` equals the infimum over the closure of that image. -/
theorem iInf_closedConvexHull_eq_iInf_closure_evalLocalEvents
    {P : Set (WithLocalConvergence S E)} (hPcl : IsClosed P)
    (hPconv : Convex ℝ (evalLocalEvents S E '' P))
    {C : Set (WithLocalConvergence S E)} (hC : C ⊆ P)
    {g : (localEvents S E → ℝ) → ℝ≥0∞} (hgm : Measurable g)
    (hglsc : LowerSemicontinuousOn g (evalLocalEvents S E '' P))
    (hgconc : ConcaveOnENNReal (evalLocalEvents S E '' P) g) :
    (⨅ v ∈ closedConvexHull ℝ (evalLocalEvents S E '' C), g v)
      = ⨅ v ∈ closure (evalLocalEvents S E '' C), g v :=
  iInf_closedConvexHull_eq_iInf_closure (isCompact_image_evalLocalEvents hPcl) hPconv
    (image_mono hC) hgm hglsc hgconc

end Georgii1554


/-! ### Georgii (15.54) for a functional on the random fields -/

section Transport

variable [Countable S] [Finite E] [MeasurableSingletonClass E]
  {P C : Set (WithLocalConvergence S E)} {𝒜 : WithLocalConvergence S E → ℝ≥0∞}

/-- A functional `𝒜` on the random fields, transported to the ambient vector space
`localEvents S E → ℝ` along the evaluation embedding and extended by `∞` off the image of `P`.
Extension by `∞` is what keeps the transported functional lower semicontinuous. -/
def extendAlongEvalLocalEvents (P : Set (WithLocalConvergence S E))
    (𝒜 : WithLocalConvergence S E → ℝ≥0∞) : (localEvents S E → ℝ) → ℝ≥0∞ :=
  fun v ↦ ⨅ μ ∈ {μ | μ ∈ P ∧ evalLocalEvents S E μ = v}, 𝒜 μ

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
@[simp] lemma extendAlongEvalLocalEvents_apply {μ : WithLocalConvergence S E} (hμ : μ ∈ P) :
    extendAlongEvalLocalEvents P 𝒜 (evalLocalEvents S E μ) = 𝒜 μ := by
  have hset : {ν | ν ∈ P ∧ evalLocalEvents S E ν = evalLocalEvents S E μ} = {μ} := by
    ext ν
    refine ⟨fun h ↦ ?_, ?_⟩
    · exact WithSetwiseTopology.injective_evalReal separatesOn_localEvents h.2
    · rintro rfl; exact ⟨hμ, rfl⟩
  rw [extendAlongEvalLocalEvents, hset]
  simp

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
lemma extendAlongEvalLocalEvents_of_notMem {v : localEvents S E → ℝ}
    (hv : v ∉ evalLocalEvents S E '' P) : extendAlongEvalLocalEvents P 𝒜 v = ⊤ := by
  have hset : {μ | μ ∈ P ∧ evalLocalEvents S E μ = v} = ∅ := by
    ext μ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro hμ rfl
    exact hv ⟨μ, hμ, rfl⟩
  rw [extendAlongEvalLocalEvents, hset]
  simp

omit [Countable S] in
/-- The transported functional is lower semicontinuous on the whole ambient space: on the (closed)
image of `P` this is lower semicontinuity of `𝒜` transported along the embedding, and off the
image the value `∞` is locally constant. -/
theorem lowerSemicontinuous_extendAlongEvalLocalEvents (hPcl : IsClosed P)
    (h𝒜 : LowerSemicontinuousOn 𝒜 P) :
    LowerSemicontinuous (extendAlongEvalLocalEvents P 𝒜) := by
  intro v c hc
  by_cases hv : v ∈ evalLocalEvents S E '' P
  · obtain ⟨μ, hμP, rfl⟩ := hv
    rw [extendAlongEvalLocalEvents_apply hμP] at hc
    obtain ⟨W, hWopen, hμW, hWsub⟩ := mem_nhdsWithin.1 (h𝒜 μ hμP c hc)
    obtain ⟨U, hUopen, hU⟩ := isEmbedding_evalLocalEvents.isInducing.isOpen_iff.1 hWopen
    have hRclosed : IsClosed (Set.range (evalLocalEvents S E)) :=
      isClosedEmbedding_evalLocalEvents.isClosed_range
    have hnotmem : ∀ w : localEvents S E → ℝ, w ∉ Set.range (evalLocalEvents S E) →
        w ∉ evalLocalEvents S E '' P := fun w hw hwP ↦ hw ⟨hwP.choose, hwP.choose_spec.2⟩
    refine Filter.eventually_iff_exists_mem.2
      ⟨U ∪ (Set.range (evalLocalEvents S E))ᶜ, ?_, ?_⟩
    · refine (hUopen.union hRclosed.isOpen_compl).mem_nhds (Or.inl ?_)
      have : μ ∈ evalLocalEvents S E ⁻¹' U := by rw [hU]; exact hμW
      exact this
    · rintro w (hwU | hwR)
      · by_cases hwrange : w ∈ Set.range (evalLocalEvents S E)
        · obtain ⟨ν, rfl⟩ := hwrange
          have hνW : ν ∈ W := by rw [← hU]; exact hwU
          by_cases hνP : ν ∈ P
          · rw [extendAlongEvalLocalEvents_apply hνP]
            exact hWsub ⟨hνW, hνP⟩
          · rw [extendAlongEvalLocalEvents_of_notMem (fun h ↦ hνP (by
              obtain ⟨ρ, hρP, hρ⟩ := h
              rwa [WithSetwiseTopology.injective_evalReal separatesOn_localEvents hρ] at hρP))]
            exact lt_of_lt_of_le hc le_top
        · rw [extendAlongEvalLocalEvents_of_notMem (hnotmem w hwrange)]
          exact lt_of_lt_of_le hc le_top
      · rw [extendAlongEvalLocalEvents_of_notMem (hnotmem w hwR)]
        exact lt_of_lt_of_le hc le_top
  · rw [extendAlongEvalLocalEvents_of_notMem hv] at hc
    filter_upwards [(isClosed_image_evalLocalEvents hPcl).isOpen_compl.mem_nhds hv] with w hw
    rw [extendAlongEvalLocalEvents_of_notMem hw]
    exact hc

omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- Concavity of `𝒜` on `P`, in the tree's language, transports to `ℝ≥0∞`-concavity of the
transported functional on the image of `P`. -/
theorem concaveOnENNReal_extendAlongEvalLocalEvents
    (hPmix : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)))
    (h𝒜 : ∀ μ ∈ P, ∀ ν ∈ P, ∀ ρ ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)) →
      ENNReal.ofReal a * 𝒜 μ + ENNReal.ofReal b * 𝒜 ν ≤ 𝒜 ρ) :
    ConcaveOnENNReal (evalLocalEvents S E '' P) (extendAlongEvalLocalEvents P 𝒜) := by
  rintro _ ⟨μ, hμP, rfl⟩ _ ⟨ν, hνP, rfl⟩ a b ha hb hab
  obtain ⟨ρ, hρP, hρ⟩ := hPmix μ hμP ν hνP a b ha hb hab
  rw [← WithSetwiseTopology.evalReal_of_toMeasure_eq ha hb hρ,
    extendAlongEvalLocalEvents_apply hρP, extendAlongEvalLocalEvents_apply hμP,
    extendAlongEvalLocalEvents_apply hνP]
  exact h𝒜 μ hμP ν hνP ρ hρP a b ha hb hab hρ


omit [Countable S] [Finite E] [MeasurableSingletonClass E] in
/-- Convexity of `𝒜` on `P` transports to `ℝ≥0∞`-convexity of the transported functional. -/
theorem convexOnENNReal_extendAlongEvalLocalEvents
    (hPmix : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)))
    (h𝒜 : ∀ μ ∈ P, ∀ ν ∈ P, ∀ ρ ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)) →
      𝒜 ρ ≤ ENNReal.ofReal a * 𝒜 μ + ENNReal.ofReal b * 𝒜 ν) :
    ConvexOnENNReal (evalLocalEvents S E '' P) (extendAlongEvalLocalEvents P 𝒜) := by
  rintro _ ⟨μ, hμP, rfl⟩ _ ⟨ν, hνP, rfl⟩ a b ha hb hab
  obtain ⟨ρ, hρP, hρ⟩ := hPmix μ hμP ν hνP a b ha hb hab
  rw [← WithSetwiseTopology.evalReal_of_toMeasure_eq ha hb hρ,
    extendAlongEvalLocalEvents_apply hρP, extendAlongEvalLocalEvents_apply hμP,
    extendAlongEvalLocalEvents_apply hνP]
  exact h𝒜 μ hμP ν hνP ρ hρP a b ha hb hab hρ

/-- **Georgii's display before (15.54), in the tree's language.** Let `P` be a closed,
mixture-stable set of random fields (`𝓟_Θ`) and let `C ⊆ P` be closed. If `μ ∈ P` lies in
Georgii's `cx̄ C` — its evaluation lies in the closed convex hull of the evaluation of `C` — then
there is a probability measure `w_μ` on the ambient space `localEvents S E → ℝ`, **carried by the
image of `C`**, whose **barycentre** is the evaluation of `μ`; and every affine lower
semicontinuous `𝒜 : P → [0, ∞]` satisfies `𝒜 μ = ∫⁻ 𝒜 d w_μ`.

The second identity is Phelps' Lemma 9.7
(`MeasureTheory.IsBarycenter.lintegral_eq_of_affineENNReal`); Georgii writes it as
`𝒜(μ|Φ) = ∫ 𝒜(ν|Φ) w_μ(dν)`. -/
theorem exists_isBarycenter_lintegral_eq
    (hPcl : IsClosed P)
    (hPmix : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)))
    (hCcl : IsClosed C) (hC : C ⊆ P) (h𝒜lsc : LowerSemicontinuousOn 𝒜 P)
    (h𝒜aff : ∀ μ ∈ P, ∀ ν ∈ P, ∀ ρ ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)) →
      𝒜 ρ = ENNReal.ofReal a * 𝒜 μ + ENNReal.ofReal b * 𝒜 ν)
    {μ : WithLocalConvergence S E} (hμP : μ ∈ P)
    (hμ : evalLocalEvents S E μ ∈ closedConvexHull ℝ (evalLocalEvents S E '' C)) :
    ∃ w : Measure (localEvents S E → ℝ), IsProbabilityMeasure w ∧
      w (evalLocalEvents S E '' C)ᶜ = 0 ∧ IsBarycenter w (evalLocalEvents S E μ) ∧
      ∫⁻ v, extendAlongEvalLocalEvents P 𝒜 v ∂w = 𝒜 μ := by
  have hPconv : Convex ℝ (evalLocalEvents S E '' P) := convex_image_evalLocalEvents hPmix
  obtain ⟨w, hwprob, hwC, hwbar⟩ := exists_isBarycenter_of_mem_closedConvexHull
    (isCompact_image_evalLocalEvents hPcl) hPconv (isClosed_image_evalLocalEvents hCcl)
    (image_mono hC) hμ
  have : IsProbabilityMeasure w := hwprob
  refine ⟨w, hwprob, hwC, hwbar, ?_⟩
  have hwP : w (evalLocalEvents S E '' P)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (image_mono hC)) hwC
  have hglsc : LowerSemicontinuous (extendAlongEvalLocalEvents P 𝒜) :=
    lowerSemicontinuous_extendAlongEvalLocalEvents hPcl h𝒜lsc
  have heq := hwbar.lintegral_eq_of_affineENNReal (isCompact_image_evalLocalEvents hPcl) hPconv
    hwP hglsc.measurable (hglsc.lowerSemicontinuousOn _)
    (convexOnENNReal_extendAlongEvalLocalEvents hPmix
      (fun μ' hμ' ν' hν' ρ hρ a b ha hb hab hmix => le_of_eq
        (h𝒜aff μ' hμ' ν' hν' ρ hρ a b ha hb hab hmix)))
    (concaveOnENNReal_extendAlongEvalLocalEvents hPmix
      (fun μ' hμ' ν' hν' ρ hρ a b ha hb hab hmix => ge_of_eq
        (h𝒜aff μ' hμ' ν' hν' ρ hρ a b ha hb hab hmix)))
  rw [heq, extendAlongEvalLocalEvents_apply hμP]

/-- **Georgii (15.54), in the tree's language.** Let `P` be a closed, mixture-stable set of random
fields — `𝓟_Θ`, by `isClosed_setOf_mem_invariantFields` and
`smul_add_smul_mem_invariantFields_shiftGroup` — and let `𝒜 : P → [0, ∞]` be lower semicontinuous
for the topology of local convergence and concave (in particular affine, as Georgii's excess free
energy `𝒜(· | Φ)` is). Then for `C ⊆ P` the infimum of `𝒜` over the *closed convex hull of `C`
inside `P`* — the random fields whose evaluation lies in
`closedConvexHull ℝ (evalLocalEvents '' C)`, Georgii's `cx̄ C` — equals the infimum of `𝒜` over
the closure of `C`.

This is exactly Step 3 of Georgii's proof of Theorem (15.45): it converts the large-deviation upper
bound with `cx̄ C` on the right-hand side into the bound with `C̄`. -/
theorem iInf_closedConvexHull_eq_iInf_closure_of_lowerSemicontinuousOn
    (hPcl : IsClosed P)
    (hPmix : ∀ μ ∈ P, ∀ ν ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ ρ ∈ P, (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)))
    (hC : C ⊆ P) (h𝒜lsc : LowerSemicontinuousOn 𝒜 P)
    (h𝒜conc : ∀ μ ∈ P, ∀ ν ∈ P, ∀ ρ ∈ P, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (ρ.toMeasure : Measure (S → E))
        = ENNReal.ofReal a • (μ.toMeasure : Measure (S → E))
          + ENNReal.ofReal b • (ν.toMeasure : Measure (S → E)) →
      ENNReal.ofReal a * 𝒜 μ + ENNReal.ofReal b * 𝒜 ν ≤ 𝒜 ρ) :
    (⨅ μ ∈ {μ | μ ∈ P ∧
        evalLocalEvents S E μ ∈ closedConvexHull ℝ (evalLocalEvents S E '' C)}, 𝒜 μ)
      = ⨅ μ ∈ closure C, 𝒜 μ := by
  set g := extendAlongEvalLocalEvents P 𝒜 with hg
  have hglsc : LowerSemicontinuous g := lowerSemicontinuous_extendAlongEvalLocalEvents hPcl h𝒜lsc
  have hmain := iInf_closedConvexHull_eq_iInf_closure_evalLocalEvents hPcl
    (convex_image_evalLocalEvents hPmix) hC hglsc.measurable
    (hglsc.lowerSemicontinuousOn _)
    (concaveOnENNReal_extendAlongEvalLocalEvents hPmix h𝒜conc)
  -- the closed convex hull of the image of `C` lies in the image of `P`
  have hsub : closedConvexHull ℝ (evalLocalEvents S E '' C) ⊆ evalLocalEvents S E '' P :=
    closedConvexHull_min (image_mono hC) (convex_image_evalLocalEvents hPmix)
      (isClosed_image_evalLocalEvents hPcl)
  set T : Set (WithLocalConvergence S E) :=
    {μ | μ ∈ P ∧ evalLocalEvents S E μ ∈ closedConvexHull ℝ (evalLocalEvents S E '' C)} with hT
  have hTP : ∀ μ ∈ T, μ ∈ P := fun μ hμ ↦ hμ.1
  have hhull : closedConvexHull ℝ (evalLocalEvents S E '' C) = evalLocalEvents S E '' T := by
    refine Subset.antisymm (fun v hv ↦ ?_) ?_
    · obtain ⟨μ, hμP, rfl⟩ := hsub hv
      exact ⟨μ, ⟨hμP, hv⟩, rfl⟩
    · rintro _ ⟨μ, hμ, rfl⟩; exact hμ.2
  have hclos : closure (evalLocalEvents S E '' C) = evalLocalEvents S E '' closure C :=
    (image_closure_evalLocalEvents C).symm
  have hL : (⨅ v ∈ closedConvexHull ℝ (evalLocalEvents S E '' C), g v) = ⨅ μ ∈ T, 𝒜 μ := by
    rw [hhull, iInf_image]
    exact iInf_congr fun μ ↦ iInf_congr fun hμ ↦ extendAlongEvalLocalEvents_apply (hTP μ hμ)
  have hR : (⨅ v ∈ closure (evalLocalEvents S E '' C), g v) = ⨅ μ ∈ closure C, 𝒜 μ := by
    rw [hclos, iInf_image]
    exact iInf_congr fun μ ↦ iInf_congr fun hμ ↦
      extendAlongEvalLocalEvents_apply (hPcl.closure_subset_iff.2 hC hμ)
  rw [← hL, ← hR, hmain]

end Transport

end MeasureTheory.GibbsMeasure

end

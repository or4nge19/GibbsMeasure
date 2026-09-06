/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Measure.SetwiseCompact
public import GibbsMeasure.Prereqs.Transformation
public import GibbsMeasure.Topology.LocalConvergence

/-!
# The `𝒞`-topology on random fields (Georgii (4.A13) and (4.A10)(1))

Over a countable site set `S` and a **standard Borel** state space `E`, Georgii's Corollary
(4.A13) provides a countable core `𝒞 ⊆ 𝓕⁰` of the configuration σ-algebra consisting of *local
events*. The **`𝒞`-topology** on the random fields — the coarsest topology making `ν ↦ ν A`
continuous for `A ∈ 𝒞` — is then compact metrizable (Comment (4.A10)(1)) and coarser than the
topology `𝓛` of local convergence. This is the change of topology used in Step 3 of Georgii's
proof of the large-deviation upper bound (15.46).

Over a *finite* state space no change of topology is needed: `𝓕⁰` is itself countable
(`MeasureTheory.countable_localEvents`) and `𝓛` is already compact metrizable. The point of this
file is the infinite standard Borel state space.

## What the change of topology does and does not give in Step 3

Georgii's Step 3 concludes `inf_{cx̄ C} 𝓀(·|Φ) = inf_{C̄} 𝓀(·|Φ)` with `C̄` the closure in the
topology `𝓛` of local convergence. The Choquet argument run in the `𝒞`-topology produces a
representing measure carried by the **`𝒞`-closure** `C̃` of `C`, and therefore only
`inf_{cx̄ C} 𝓀(·|Φ) ≥ inf_{C̃} 𝓀(·|Φ)`. Since `𝒞`-convergence tests only the countably many events
of `𝒞`, `C̃` is in general strictly larger than `C̄`: a sequence of probability measures may
converge on `𝒞` and on no other local event, and its `𝒞`-limit then lies in `C̃ ∖ C̄`. The core
cannot be repaired by adjoining the missing local events, because condition (ii) of a countable
core (`MeasurableSpace.IsCountableCore.exists_isProbabilityMeasure_tendsto`) fails for
`𝒞 ∪ {A}` with a general `A ∈ 𝓕⁰`. The coincidence of the `𝓛`- and `𝒞`-topologies on each
sublevel set of `𝓀(·|Φ)`, which is what Georgii's argument establishes, says nothing about nets
in `C` that leave every sublevel set.

Consequently `Specification/LargeDeviationsUpper.lean` proves the large-deviation upper bound over
a standard Borel state space with Georgii's `cx̄ C` on the right and does **not** use the
`𝒞`-topology: the bound with `cx̄ C` is stronger than the bound with `C̃` that the `𝒞`-topology
would give, since `cx̄ C ⊆ cx̄_𝒞 C`. The files here record Appendix 4.A for its own sake.

## Main statements

* `MeasureTheory.GibbsMeasure.exists_isCountableCore_subset_localEvents`: **Georgii (4.A13)**.
* `MeasureTheory.GibbsMeasure.exists_isCountableCore_subset_localEvents_forall_preimage`: the core
  can be chosen stable under a family of coordinate relabellings — the shifts, in particular.
* `MeasureTheory.GibbsMeasure.continuous_ofMeasure_withLocalConvergence`: **the `𝒞`-topology is
  coarser than `𝓛`** for any `𝒞 ⊆ 𝓕⁰`.
* `MeasureTheory.GibbsMeasure.compactSpace_withCoreTopology`,
  `…metrizableSpace_withCoreTopology`: **Comment (4.A10)(1)**.
* `MeasureTheory.GibbsMeasure.isClosed_setOf_forall_measurePreserving_withCoreTopology`: the
  measures invariant under a family of relabellings are `𝒞`-closed, hence `𝒞`-compact
  (`…isCompact_setOf_forall_measurePreserving_withCoreTopology`).

## The stability hypothesis is not decorative

Georgii asserts in the proof of (15.46) that the `𝒞`-topology "turns `𝓟_Θ(Ω, 𝓕)` into a compact
metrizable set", i.e. that `𝓟_Θ` is `𝒞`-closed. Two things have to be said about that.

*It does not follow from `𝓛`-closedness.* The `𝓛`-closedness of `𝓟_Θ`
(`MeasureTheory.GibbsMeasure.isClosed_setOf_forall_measurePreserving`) says nothing here: the
identity `𝓛 → 𝒞` is continuous, which transports compactness forward, not closedness. A
`𝒞`-convergent sequence of invariant measures controls only the sets of `𝒞`, and `τ⁻¹A` need not
be one of them.

*For a group acting by measure-theoretic automorphisms it is false.* Let `τ` be the Borel
involution of the Cantor space exchanging `x ↔ z` and `aₙ ↔ bₙ`, where `aₙ → x`, `bₙ → y`, and
`x, y, z` are distinct points fixed by `τ` apart from the swap `x ↔ z`. Each
`(δ_{aₙ} + δ_{bₙ})/2` is `τ`-invariant and converges on every cylinder event to
`(δ_x + δ_y)/2`, whose `τ`-image is `(δ_z + δ_y)/2`. (Such a `τ` is not one of Georgii's
transformations (5.1); no contradiction with the `𝓛`-closedness above, which is proved *from*
`τ ⁻¹' 𝓕⁰ ⊆ 𝓕⁰`.)

What is true, and what Georgii's `Θ` — the shift group — satisfies, is that the core built in
`MeasurableSpace.cylinderCore` from **one** Borel embedding `f : E → (ℕ → Bool)` used in every
coordinate is stable under every relabelling of the sites: `preimage_mem_cylinderCore` below. The
hypothesis is therefore carried explicitly.
-/

@[expose] public section

open Filter MeasurableSpace Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Georgii (4.A13): a countable core of local events -/

/-- **Georgii (4.A13).** Over a countable site set and a standard Borel state space, the
configuration σ-algebra has a countable core consisting of local events. -/
theorem exists_isCountableCore_subset_localEvents (S E : Type*) [Countable S] [MeasurableSpace E]
    [StandardBorelSpace E] :
    ∃ 𝒞 ⊆ localEvents S E, IsCountableCore 𝒞 :=
  exists_isCountableCore_subset_measurableCylinders (fun _ : S ↦ E)

/-- A relabelling of the sites maps the core `MeasurableSpace.cylinderCore (fun _ ↦ f)` of
(4.A13) into itself: the event "`f (ω i)` has `n`-th digit `b`" is transported to the same event
at the site `τ⁻¹ i`. -/
theorem preimage_mem_cylinderCore (f : E → ℕ → Bool) {τ : Transformation S E}
    (hτ : ∀ i, τ.spin i = MeasurableEquiv.refl E) {A : Set (S → E)}
    (hA : A ∈ cylinderCore (fun _ : S ↦ f)) :
    τ.toFun ⁻¹' A ∈ cylinderCore (fun _ : S ↦ f) := by
  classical
  obtain ⟨J, rfl⟩ := hA
  refine ⟨J.image fun q ↦ ((τ.sites.symm q.1.1, q.1.2), q.2), ?_⟩
  ext ω
  simp only [Finset.forall_mem_image, mem_preimage, Set.mem_ofPred_eq]
  refine forall₂_congr fun q _ ↦ ?_
  rw [Transformation.toFun, hτ]
  rfl

/-- The shift `θ_j` relabels the sites: its spin part is the identity. -/
@[simp] lemma shift_spin {S : Type*} [AddGroup S] (j : S) (i : S) :
    (shift E j).spin i = MeasurableEquiv.refl E := rfl

/-- **Georgii (4.A13), with the stability needed for `𝓟_Θ`.** Over a countable site set and a
standard Borel state space, the countable core of local events can be chosen stable under the
preimages of an arbitrary family of relabellings of the sites — the shifts in particular. -/
theorem exists_isCountableCore_subset_localEvents_forall_preimage [Countable S]
    [StandardBorelSpace E] (I : Set (Transformation S E))
    (hI : ∀ τ ∈ I, ∀ i, τ.spin i = MeasurableEquiv.refl E) :
    ∃ 𝒞 ⊆ localEvents S E, IsCountableCore 𝒞 ∧
      ∀ τ ∈ I, ∀ A ∈ 𝒞, τ.toFun ⁻¹' A ∈ 𝒞 := by
  obtain ⟨f, hf, hclosed⟩ := exists_measurableEmbedding_natBool_isClosed_range E
  refine ⟨cylinderCore (fun _ : S ↦ f),
    cylinderCore_subset_measurableCylinders fun _ ↦ hf.measurable,
    isCountableCore_cylinderCore (fun _ ↦ hf) (fun _ ↦ hclosed),
    fun τ hτ A hA ↦ preimage_mem_cylinderCore f (hI τ hτ) hA⟩

/-! ### The `𝒞`-topology -/

/-- **The `𝒞`-topology is coarser than the topology `𝓛` of local convergence**, for every family
`𝒞` of local events: the identity is continuous from `𝓛` to the `𝒞`-topology. -/
theorem continuous_ofMeasure_withLocalConvergence {𝒞 : Set (Set (S → E))}
    (h𝒞 : 𝒞 ⊆ localEvents S E) :
    Continuous fun μ : WithLocalConvergence S E ↦
      (WithSetwiseTopology.ofMeasure μ.toMeasure :
        WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E))) :=
  WithSetwiseTopology.continuous_ofMeasure_of_subset h𝒞

/-- **Georgii, Comment (4.A10)(1).** In the `𝒞`-topology of a countable core, the random fields
form a compact space. -/
theorem compactSpace_withCoreTopology {𝒞 : Set (Set (S → E))} (h𝒞 : IsCountableCore 𝒞) :
    CompactSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E))) :=
  WithSetwiseTopology.compactSpace_of_isCountableCore h𝒞

/-- **Georgii, Comment (4.A10)(1).** The `𝒞`-topology of a countable core is metrizable. -/
theorem metrizableSpace_withCoreTopology {𝒞 : Set (Set (S → E))} (h𝒞 : IsCountableCore 𝒞) :
    MetrizableSpace (WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E))) :=
  WithSetwiseTopology.metrizableSpace_of_isCountableCore h𝒞

/-! ### Invariant random fields in the `𝒞`-topology -/

/-- The random fields invariant under a family `I` of transformations are closed in the
`𝒞`-topology of a core stable under the preimages along `I`. -/
theorem isClosed_setOf_forall_measurePreserving_withCoreTopology {𝒞 : Set (Set (S → E))}
    (h𝒞 : IsCountableCore 𝒞) (I : Set (Transformation S E))
    (hstab : ∀ τ ∈ I, ∀ A ∈ 𝒞, τ.toFun ⁻¹' A ∈ 𝒞) :
    IsClosed {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E))
        (μ.toMeasure : Measure (S → E))} :=
  WithSetwiseTopology.isClosed_setOf_forall_measurePreserving I Transformation.toFun
    h𝒞.isPiSystem h𝒞.generateFrom_eq (fun τ _ ↦ τ.measurable_toFun) hstab

/-- **Georgii, Comment (4.A10)(1) applied to `𝓟_Θ`.** The random fields invariant under a family
`I` of transformations are compact in the `𝒞`-topology of a core stable under the preimages along
`I`. This is the compactness used in Step 3 of the proof of (15.46). -/
theorem isCompact_setOf_forall_measurePreserving_withCoreTopology {𝒞 : Set (Set (S → E))}
    (h𝒞 : IsCountableCore 𝒞) (I : Set (Transformation S E))
    (hstab : ∀ τ ∈ I, ∀ A ∈ 𝒞, τ.toFun ⁻¹' A ∈ 𝒞) :
    IsCompact {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure (S → E)) |
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E))
        (μ.toMeasure : Measure (S → E))} :=
  letI := compactSpace_withCoreTopology h𝒞
  (isClosed_setOf_forall_measurePreserving_withCoreTopology h𝒞 I hstab).isCompact

end MeasureTheory.GibbsMeasure

end

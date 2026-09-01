/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.IsingFKG
public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Model.PhaseTransition
public import GibbsMeasure.Topology.Metrizable

/-!
# The plus and minus phases of the ferromagnetic Ising model

For a ferromagnetic coupling `J ≥ 0` and `β ≥ 0`, the net of finite-volume Ising distributions
under the all-`+` boundary condition is stochastically decreasing in the volume
(`stochasticallyLE_isingSpecification_plus`).  We show that it converges in the topology of local
convergence to a Gibbs measure `plusState`, the **plus phase**, and dually that the all-`-` net
converges to the **minus phase** `minusState`.  The plus phase is the largest element of the set
of Gibbs measures for the stochastic order, the minus phase the smallest; Georgii, Section 6.2,
after (6.9), states only the weaker `μ₊^β(σ₀) ≥ μ(σ₀)` for all `μ ∈ 𝒢(βΦ)`.

## Main declarations

* `upEvent`: the local upper events `{σ | σ ≡ + on F}`; they form a generating π-system.
* `exists_tendsto_of_forall_upEvent`: a net of probability measures on `S → Bool` whose masses on
  the up-events converge, converges in the topology of local convergence.
* `stochasticallyLE_of_forall_upper_localEvents`: on the configuration space over a countable site
  set, domination on the local upper events implies stochastic domination.
* `plusState`, `minusState`: the two extreme phases, defined as genuine local limits.
* `tendsto_plusState`, `tendsto_minusState`: the defining local limits exist.
* `plusState_mem_GP`, `minusState_mem_GP`: the two phases are Gibbs measures (Georgii (4.18)).
* `stochasticallyLE_plusState`, `minusState_stochasticallyLE`: every Gibbs measure lies between
  the minus and the plus phase.
* `map_plusState`, `map_minusState`: monotone symmetries of the specification fix both phases;
  `measurePreserving_shift_plusState` and `measurePreserving_shift_minusState` specialise this to
  the shifts of `ℤ^d`.
* `map_plusState_eq_minusState`: an order-reversing symmetry exchanges the two phases;
  `map_spinFlip_plusState` specialises this to the spin flip of the zero-field Ising model
  on `ℤ²`.
* `eq_plusState_of_stochasticallyLE`, `eq_plusState_of_mapClusterPt`: the plus phase is the
  *unique* `≼`-maximum of `𝒢(βΦ)`, and every local cluster point of a net dominating it which is
  a Gibbs measure equals it.
* `eq_plusState_of_mapClusterPt_plusCubeAverage`, `tendsto_plusCubeAverage`: **there is only one
  plus phase.**  Georgii constructs `μ₊^β` in the proof of (6.9) as a cluster point of the
  cube-averaged `+`-boundary distributions (`Peierls.plusCubeAverage`), in order to get shift
  invariance; for `β ≥ 0` that cluster point is unique and equal to `plusState`, and the averages
  converge to it with no subsequence extraction.  `Peierls.plusPhase_eq_plusState` in
  `GibbsMeasure/Model/LowTemperatureLimit.lean` is the statement for Georgii's own `μ₊^β`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.Measure.StochasticallyLE

variable {ι : Type*} {μ ν : Measure (ι → Bool)}

/-- **Antisymmetry of the stochastic order on `ι → Bool`.**  Two mutually dominating probability
measures on a configuration space with two-point spins are equal: the coordinate events are
measurable upper sets and they generate the product σ-algebra. -/
protected lemma antisymm [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h₁ : μ.StochasticallyLE ν) (h₂ : ν.StochasticallyLE μ) : μ = ν :=
  h₁.eq_of_forall_apply_eq fun i ↦ le_antisymm
    (h₁ (measurableSet_setOf_eq_true i) (isUpperSet_setOf_eq_true i))
    (h₂ (measurableSet_setOf_eq_true i) (isUpperSet_setOf_eq_true i))

end MeasureTheory.Measure.StochasticallyLE

namespace MeasureTheory.GibbsMeasure

/-! ### The generating π-system of local upper events -/

section UpEvent
variable {S : Type*}

/-- The event that the configuration is `+` on the finite set `F`.  These sets are local upper
events, and they form a π-system generating the product σ-algebra. -/
def upEvent (F : Finset S) : Set (S → Bool) := {σ | ∀ i ∈ F, σ i = true}

@[simp] lemma mem_upEvent {F : Finset S} {σ : S → Bool} :
    σ ∈ upEvent F ↔ ∀ i ∈ F, σ i = true := Iff.rfl

lemma isUpperSet_upEvent (F : Finset S) : IsUpperSet (upEvent F) := by
  intro σ τ hστ hσ i hi
  have h1 := hστ i
  rw [hσ i hi] at h1
  exact le_antisymm (by simp) h1

lemma upEvent_mem_localEvents (F : Finset S) : upEvent F ∈ localEvents S Bool := by
  refine mem_localEvents_iff_exists_finsetRestrict_preimage.2
    ⟨F, {ζ : ∀ _ : F, Bool | ∀ i : F, ζ i = true}, (Set.toFinite _).measurableSet, ?_⟩
  ext σ
  simp [Finset.restrict, Subtype.forall]

lemma measurableSet_upEvent (F : Finset S) : MeasurableSet (upEvent F) :=
  MeasurableSet.of_mem_measurableCylinders (upEvent_mem_localEvents F)

lemma upEvent_inter [DecidableEq S] (F F' : Finset S) :
    upEvent F ∩ upEvent F' = upEvent (F ∪ F') := by
  ext σ
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · exact h1 i hi
    · exact h2 i hi
  · intro hh
    exact ⟨fun i hi ↦ hh i (Finset.mem_union_left _ hi),
      fun i hi ↦ hh i (Finset.mem_union_right _ hi)⟩

lemma isPiSystem_range_upEvent : IsPiSystem (Set.range (upEvent (S := S))) := by
  classical
  rintro _ ⟨F, rfl⟩ _ ⟨F', rfl⟩ -
  exact ⟨F ∪ F', (upEvent_inter F F').symm⟩

lemma generateFrom_range_upEvent :
    MeasurableSpace.generateFrom (Set.range (upEvent (S := S)))
      = (inferInstance : MeasurableSpace (S → Bool)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨F, rfl⟩
    exact measurableSet_upEvent F
  · rw [← Measure.StochasticallyLE.generateFrom_setOf_eq_true (ι := S)]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨i, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom ⟨{i}, ?_⟩
    ext σ
    simp [upEvent]

/-- Two probability measures on `S → Bool` agreeing on all up-events are equal. -/
lemma ext_of_forall_upEvent {μ ν : Measure (S → Bool)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ F : Finset S, μ (upEvent F) = ν (upEvent F)) : μ = ν := by
  refine ext_of_generate_finite _ generateFrom_range_upEvent.symm isPiSystem_range_upEvent
    ?_ (by simp)
  rintro _ ⟨F, rfl⟩
  exact h F

end UpEvent

/-! ### Local convergence from convergence on the up-events -/

section LocalLimit
variable {S : Type*}

instance : Nonempty (WithLocalConvergence S Bool) :=
  ⟨WithSetwiseTopology.ofMeasure ⟨Measure.dirac fun _ ↦ true, inferInstance⟩⟩

/-- The value at a local event of a cluster point of a net of probability measures whose masses on
that event converge is the limit of those masses. -/
lemma eval_eq_of_mapClusterPt {ι : Type*} {l : Filter ι} [l.NeBot] {A : Set (S → Bool)}
    (hA : A ∈ localEvents S Bool) {c : ℝ≥0∞} {ms : ι → ProbabilityMeasure (S → Bool)}
    {m : WithLocalConvergence S Bool}
    (hm : MapClusterPt m l fun i ↦ WithSetwiseTopology.ofMeasure (ms i))
    (hc : Tendsto (fun i ↦ (ms i : Measure (S → Bool)) A) l (𝓝 c)) :
    (m.toMeasure : Measure (S → Bool)) A = c := by
  have hcont : Continuous fun v : WithLocalConvergence S Bool ↦
      (v.toMeasure : Measure (S → Bool)) A :=
    WithSetwiseTopology.continuous_apply_enn hA
  have hcl : ClusterPt ((m.toMeasure : Measure (S → Bool)) A)
      (Filter.map (fun i ↦ (ms i : Measure (S → Bool)) A) l) := by
    refine ClusterPt.map (f := fun v : WithLocalConvergence S Bool ↦
      (v.toMeasure : Measure (S → Bool)) A) hm hcont.continuousAt ?_
    exact le_of_eq Filter.map_map
  have hnb : ((𝓝 ((m.toMeasure : Measure (S → Bool)) A))
      ⊓ Filter.map (fun i ↦ (ms i : Measure (S → Bool)) A) l).NeBot := hcl
  exact tendsto_nhds_unique (l := (𝓝 ((m.toMeasure : Measure (S → Bool)) A))
      ⊓ Filter.map (fun i ↦ (ms i : Measure (S → Bool)) A) l) (f := id)
    (tendsto_id.mono_left inf_le_left) (tendsto_id.mono_left (le_trans inf_le_right hc))

/-- **A net of probability measures on `S → Bool` whose masses on the up-events converge is
locally convergent.**  Local convergence is metrizable and the space of random fields is compact
(Georgii (4.3)(3), (4.11)(2)), so it is enough to know that the up-events, which generate the
σ-algebra, separate the cluster points. -/
theorem exists_tendsto_of_forall_upEvent {ι : Type*} {l : Filter ι} [l.NeBot]
    (ms : ι → ProbabilityMeasure (S → Bool))
    (hconv : ∀ F : Finset S, ∃ c : ℝ≥0∞,
      Tendsto (fun i ↦ (ms i : Measure (S → Bool)) (upEvent F)) l (𝓝 c)) :
    ∃ μ : ProbabilityMeasure (S → Bool),
      Tendsto (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) : WithLocalConvergence S Bool)) l
        (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace
    (Filter.map (fun i ↦ (WithSetwiseTopology.ofMeasure (ms i) : WithLocalConvergence S Bool)) l)
  refine ⟨ν.toMeasure, ?_⟩
  have key : ∀ w : WithLocalConvergence S Bool,
      MapClusterPt w l (fun i ↦ WithSetwiseTopology.ofMeasure (ms i)) → w = ν := by
    intro w hw
    have hmeas : (w.toMeasure : Measure (S → Bool)) = (ν.toMeasure : Measure (S → Bool)) := by
      refine ext_of_forall_upEvent fun F ↦ ?_
      obtain ⟨c, hc⟩ := hconv F
      rw [eval_eq_of_mapClusterPt (upEvent_mem_localEvents F) hw hc,
        eval_eq_of_mapClusterPt (upEvent_mem_localEvents F) hν hc]
    obtain ⟨w⟩ := w
    obtain ⟨ν⟩ := ν
    exact congrArg WithSetwiseTopology.ofMeasure (ProbabilityMeasure.toMeasure_injective hmeas)
  exact tendsto_nhds_of_unique_mapClusterPt key

end LocalLimit

/-! ### From local upper events to all measurable upper sets -/

section Upgrade
variable {S : Type*}

/-- The **local upper hull** of a set `K` at the finite volume `Δ`: the configurations dominating
some element of `K` on `Δ`.  It is a local upper event containing `K`. -/
def upHull (Δ : Finset S) (K : Set (S → Bool)) : Set (S → Bool) :=
  {σ | ∃ κ ∈ K, ∀ i ∈ Δ, κ i ≤ σ i}

lemma subset_upHull (Δ : Finset S) (K : Set (S → Bool)) : K ⊆ upHull Δ K :=
  fun κ hκ ↦ ⟨κ, hκ, fun _ _ ↦ le_rfl⟩

lemma isUpperSet_upHull (Δ : Finset S) (K : Set (S → Bool)) : IsUpperSet (upHull Δ K) := by
  rintro σ τ hστ ⟨κ, hκ, hle⟩
  exact ⟨κ, hκ, fun i hi ↦ (hle i hi).trans (hστ i)⟩

lemma upHull_mem_localEvents (Δ : Finset S) (K : Set (S → Bool)) :
    upHull Δ K ∈ localEvents S Bool := by
  refine mem_localEvents_iff_exists_finsetRestrict_preimage.2
    ⟨Δ, {ζ : ∀ _ : Δ, Bool | ∃ κ ∈ K, ∀ i : Δ, κ i ≤ ζ i}, (Set.toFinite _).measurableSet, ?_⟩
  ext σ
  simp [upHull, Finset.restrict, Subtype.forall]

lemma measurableSet_upHull (Δ : Finset S) (K : Set (S → Bool)) :
    MeasurableSet (upHull Δ K) :=
  MeasurableSet.of_mem_measurableCylinders (upHull_mem_localEvents Δ K)

lemma directed_upHull (K : Set (S → Bool)) :
    Directed (fun s t : Set (S → Bool) ↦ s ⊇ t) fun Δ : Finset S ↦ upHull Δ K := by
  classical
  refine fun Δ Δ' ↦ ⟨Δ ∪ Δ', ?_, ?_⟩ <;>
    rintro σ ⟨κ, hκ, hle⟩ <;> exact ⟨κ, hκ, fun i hi ↦ hle i (by simp [hi])⟩

/-- A configuration dominating, on every finite volume, some element of a compact set `K`
dominates an element of `K`. -/
lemma exists_le_of_forall_mem_upHull {K : Set (S → Bool)} (hK : IsCompact K) {σ : S → Bool}
    (hσ : ∀ Δ : Finset S, σ ∈ upHull Δ K) : ∃ κ ∈ K, κ ≤ σ := by
  classical
  set t : Finset S → Set (S → Bool) := fun Δ ↦ {κ | κ ∈ K ∧ ∀ i ∈ Δ, κ i ≤ σ i} with ht
  have htcl : ∀ Δ, IsClosed (t Δ) := by
    intro Δ
    have h1 : t Δ = K ∩ ⋂ i ∈ Δ, (fun κ : S → Bool ↦ κ i) ⁻¹' {b : Bool | b ≤ σ i} := by
      ext κ; simp [ht]
    rw [h1]
    refine hK.isClosed.inter (isClosed_biInter fun i _ ↦ ?_)
    exact IsClosed.preimage (continuous_apply i) (isClosed_discrete _)
  have htc : ∀ Δ, IsCompact (t Δ) := fun Δ ↦ hK.of_isClosed_subset (htcl Δ) fun _ hx ↦ hx.1
  have htn : ∀ Δ, (t Δ).Nonempty := by
    intro Δ
    obtain ⟨κ, hκ, hle⟩ := hσ Δ
    exact ⟨κ, hκ, hle⟩
  have htd : Directed (fun s r : Set (S → Bool) ↦ s ⊇ r) t := by
    refine fun Δ Δ' ↦ ⟨Δ ∪ Δ', ?_, ?_⟩ <;>
      exact fun κ hκ ↦ ⟨hκ.1, fun i hi ↦ hκ.2 i (by simp [hi])⟩
  obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    htc htcl
  rw [Set.mem_iInter] at hκ
  exact ⟨κ, (hκ ∅).1, fun i ↦ (hκ {i}).2 i (Finset.mem_singleton_self i)⟩

/-- **Local domination implies stochastic domination on `S → Bool`.** Two finite measures on the
configuration space over a countable site set comparable on the local upper events are comparable
on all measurable upper sets: a measurable set is inner regular, a compact set is the decreasing
intersection of its local upper hulls, and an upper set contains the up-closure of any of its
subsets. -/
theorem stochasticallyLE_of_forall_upper_localEvents [Countable S] {μ ν : Measure (S → Bool)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hlocal : ∀ A ∈ localEvents S Bool, IsUpperSet A → μ A ≤ ν A) : μ.StochasticallyLE ν := by
  intro A hA hup
  rw [hA.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hK ↦ ?_
  have hstep : ∀ Δ : Finset S, μ K ≤ ν (upHull Δ K) := fun Δ ↦
    (measure_mono (subset_upHull Δ K)).trans
      (hlocal _ (upHull_mem_localEvents Δ K) (isUpperSet_upHull Δ K))
  have hsub : (⋂ Δ : Finset S, upHull Δ K) ⊆ A := by
    intro σ hσ
    obtain ⟨κ, hκ, hle⟩ := exists_le_of_forall_mem_upHull hK (Set.mem_iInter.1 hσ)
    exact hup hle (hKA hκ)
  have hiInter : ν (⋂ Δ : Finset S, upHull Δ K) = ⨅ Δ : Finset S, ν (upHull Δ K) :=
    Directed.measure_iInter (fun Δ ↦ (measurableSet_upHull Δ K).nullMeasurableSet)
      (directed_upHull K) ⟨∅, measure_ne_top _ _⟩
  calc μ K ≤ ⨅ Δ : Finset S, ν (upHull Δ K) := le_iInf hstep
    _ = ν (⋂ Δ : Finset S, upHull Δ K) := hiInter.symm
    _ ≤ ν A := measure_mono hsub

end Upgrade

/-! ### The plus and minus phases -/

section Phases
variable {S : Type*} [Countable S] (G : SimpleGraph S) [G.LocallyFinite] (J h β : ℝ)

/-- The net of finite-volume Ising distributions under the all-`+` boundary condition. -/
def plusNet : Finset S → ProbabilityMeasure (S → Bool) :=
  finiteVolumeDistributions (isingSpecification G J h β) fun _ ↦ true

/-- The net of finite-volume Ising distributions under the all-`-` boundary condition. -/
def minusNet : Finset S → ProbabilityMeasure (S → Bool) :=
  finiteVolumeDistributions (isingSpecification G J h β) fun _ ↦ false

@[simp] lemma coe_plusNet (Λ : Finset S) :
    (plusNet G J h β Λ : Measure (S → Bool)) = isingSpecification G J h β Λ fun _ ↦ true := rfl

@[simp] lemma coe_minusNet (Λ : Finset S) :
    (minusNet G J h β Λ : Measure (S → Bool)) = isingSpecification G J h β Λ fun _ ↦ false := rfl

lemma antitone_plusNet_apply (hJ : 0 ≤ J) (hβ : 0 ≤ β) {A : Set (S → Bool)}
    (hA : MeasurableSet A) (hup : IsUpperSet A) :
    Antitone fun Λ : Finset S ↦ (plusNet G J h β Λ : Measure (S → Bool)) A :=
  fun _ _ hΛ ↦ stochasticallyLE_isingSpecification_plus G J h β hJ hβ hΛ hA hup

lemma monotone_minusNet_apply (hJ : 0 ≤ J) (hβ : 0 ≤ β) {A : Set (S → Bool)}
    (hA : MeasurableSet A) (hup : IsUpperSet A) :
    Monotone fun Λ : Finset S ↦ (minusNet G J h β Λ : Measure (S → Bool)) A :=
  fun _ _ hΛ ↦ stochasticallyLE_isingSpecification_minus G J h β hJ hβ hΛ hA hup

lemma exists_tendsto_plusNet (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    ∃ μ : ProbabilityMeasure (S → Bool),
      Tendsto (fun Λ ↦ (WithSetwiseTopology.ofMeasure (plusNet G J h β Λ) :
        WithLocalConvergence S Bool)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  classical
  refine exists_tendsto_of_forall_upEvent _ fun F ↦ ⟨_, tendsto_atTop_iInf ?_⟩
  exact antitone_plusNet_apply G J h β hJ hβ (measurableSet_upEvent F) (isUpperSet_upEvent F)

lemma exists_tendsto_minusNet (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    ∃ μ : ProbabilityMeasure (S → Bool),
      Tendsto (fun Λ ↦ (WithSetwiseTopology.ofMeasure (minusNet G J h β Λ) :
        WithLocalConvergence S Bool)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  classical
  refine exists_tendsto_of_forall_upEvent _ fun F ↦ ⟨_, tendsto_atTop_iSup ?_⟩
  exact monotone_minusNet_apply G J h β hJ hβ (measurableSet_upEvent F) (isUpperSet_upEvent F)

/-- **The plus phase.** The local limit of the finite-volume Ising distributions under the
all-`+` boundary condition (Georgii, Section 6.2). -/
def plusState : ProbabilityMeasure (S → Bool) :=
  (limUnder atTop fun Λ ↦ (WithSetwiseTopology.ofMeasure (plusNet G J h β Λ) :
    WithLocalConvergence S Bool)).toMeasure

/-- **The minus phase.** The local limit of the finite-volume Ising distributions under the
all-`-` boundary condition (Georgii, Section 6.2). -/
def minusState : ProbabilityMeasure (S → Bool) :=
  (limUnder atTop fun Λ ↦ (WithSetwiseTopology.ofMeasure (minusNet G J h β Λ) :
    WithLocalConvergence S Bool)).toMeasure

/-- **The plus phase is a genuine local limit.** -/
theorem tendsto_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    Tendsto (fun Λ ↦ (WithSetwiseTopology.ofMeasure (plusNet G J h β Λ) :
      WithLocalConvergence S Bool)) atTop
      (𝓝 (WithSetwiseTopology.ofMeasure (plusState G J h β))) := by
  obtain ⟨μ, hμ⟩ := exists_tendsto_plusNet G J h β hJ hβ
  have hlim : (limUnder atTop fun Λ ↦ (WithSetwiseTopology.ofMeasure (plusNet G J h β Λ) :
      WithLocalConvergence S Bool)) = WithSetwiseTopology.ofMeasure μ := hμ.limUnder_eq
  rw [plusState, hlim]
  exact hμ

/-- **The minus phase is a genuine local limit.** -/
theorem tendsto_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    Tendsto (fun Λ ↦ (WithSetwiseTopology.ofMeasure (minusNet G J h β Λ) :
      WithLocalConvergence S Bool)) atTop
      (𝓝 (WithSetwiseTopology.ofMeasure (minusState G J h β))) := by
  obtain ⟨μ, hμ⟩ := exists_tendsto_minusNet G J h β hJ hβ
  have hlim : (limUnder atTop fun Λ ↦ (WithSetwiseTopology.ofMeasure (minusNet G J h β Λ) :
      WithLocalConvergence S Bool)) = WithSetwiseTopology.ofMeasure μ := hμ.limUnder_eq
  rw [minusState, hlim]
  exact hμ

/-- Local events are integrated in the limit. -/
theorem tendsto_measure_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {A : Set (S → Bool)}
    (hA : A ∈ localEvents S Bool) :
    Tendsto (fun Λ : Finset S ↦ isingSpecification G J h β Λ (fun _ ↦ true) A) atTop
      (𝓝 ((plusState G J h β : Measure (S → Bool)) A)) :=
  tendsto_withLocalConvergence_iff.1 (tendsto_plusState G J h β hJ hβ) A hA

theorem tendsto_measure_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {A : Set (S → Bool)}
    (hA : A ∈ localEvents S Bool) :
    Tendsto (fun Λ : Finset S ↦ isingSpecification G J h β Λ (fun _ ↦ false) A) atTop
      (𝓝 ((minusState G J h β : Measure (S → Bool)) A)) :=
  tendsto_withLocalConvergence_iff.1 (tendsto_minusState G J h β hJ hβ) A hA

/-- **Georgii (4.18) for the plus phase.** The plus phase is a Gibbs measure. -/
theorem plusState_mem_GP (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    plusState G J h β ∈ GP (S := S) (E := Bool) (isingSpecification G J h β) := by
  have hcl : IsLocalThermodynamicLimit (isingSpecification G J h β) (fun _ ↦ true)
      (plusState G J h β) :=
    ClusterPt.of_le_nhds' (tendsto_plusState G J h β hJ hβ) inferInstance
  exact IsLocalThermodynamicLimit.mem_GP
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure β) hcl

theorem minusState_mem_GP (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    minusState G J h β ∈ GP (S := S) (E := Bool) (isingSpecification G J h β) := by
  have hcl : IsLocalThermodynamicLimit (isingSpecification G J h β) (fun _ ↦ false)
      (minusState G J h β) :=
    ClusterPt.of_le_nhds' (tendsto_minusState G J h β hJ hβ) inferInstance
  exact IsLocalThermodynamicLimit.mem_GP
    (Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable uniformSpinMeasure β) hcl

/-! ### The plus phase dominates, the minus phase is dominated -/

/-- Every Gibbs measure is stochastically dominated by every finite-volume Ising distribution
with all-`+` boundary condition (Georgii, Section 6.2). -/
theorem stochasticallyLE_isingSpecification_plus_of_mem_GP (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)) (Λ : Finset S) :
    (μ : Measure (S → Bool)).StochasticallyLE
      (isingSpecification G J h β Λ fun _ ↦ true) := by
  intro A hA hup
  have hbind : (μ : Measure (S → Bool)).bind (isingSpecification G J h β Λ)
      = (μ : Measure (S → Bool)) :=
    congrArg Subtype.val ((mem_GP_iff_forall_bindPM_eq μ).1 hμ Λ)
  have hmeas := (isingSpecification G J h β).measurable_kernel_toMeasure Λ
  calc (μ : Measure (S → Bool)) A
      = ((μ : Measure (S → Bool)).bind (isingSpecification G J h β Λ)) A := by rw [hbind]
    _ = ∫⁻ η, isingSpecification G J h β Λ η A ∂(μ : Measure (S → Bool)) :=
        Measure.bind_apply hA hmeas.aemeasurable
    _ ≤ ∫⁻ _, isingSpecification G J h β Λ (fun _ ↦ true) A ∂(μ : Measure (S → Bool)) :=
        lintegral_mono fun η ↦ stochasticallyLE_isingSpecification_of_le G J h β hJ hβ Λ
          (fun x ↦ Bool.le_true (η x)) hA hup
    _ = isingSpecification G J h β Λ (fun _ ↦ true) A := by
        rw [lintegral_const, measure_univ, mul_one]

/-- Every finite-volume Ising distribution with all-`-` boundary condition is stochastically
dominated by every Gibbs measure. -/
theorem stochasticallyLE_isingSpecification_minus_of_mem_GP (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)) (Λ : Finset S) :
    (isingSpecification G J h β Λ fun _ ↦ false).StochasticallyLE
      (μ : Measure (S → Bool)) := by
  intro A hA hup
  have hbind : (μ : Measure (S → Bool)).bind (isingSpecification G J h β Λ)
      = (μ : Measure (S → Bool)) :=
    congrArg Subtype.val ((mem_GP_iff_forall_bindPM_eq μ).1 hμ Λ)
  have hmeas := (isingSpecification G J h β).measurable_kernel_toMeasure Λ
  calc isingSpecification G J h β Λ (fun _ ↦ false) A
      = ∫⁻ _, isingSpecification G J h β Λ (fun _ ↦ false) A ∂(μ : Measure (S → Bool)) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ η, isingSpecification G J h β Λ η A ∂(μ : Measure (S → Bool)) :=
        lintegral_mono fun η ↦ stochasticallyLE_isingSpecification_of_le G J h β hJ hβ Λ
          (fun x ↦ Bool.false_le (η x)) hA hup
    _ = ((μ : Measure (S → Bool)).bind (isingSpecification G J h β Λ)) A :=
        (Measure.bind_apply hA hmeas.aemeasurable).symm
    _ = (μ : Measure (S → Bool)) A := by rw [hbind]

/-- **The plus phase is the largest Gibbs measure for the stochastic order.**  Georgii,
Section 6.2, the paragraph after (6.9), states only the weaker maximality of the
magnetisation, `μ₊^β(σ₀) ≥ μ(σ₀)` for all `μ ∈ 𝒢(βΦ)`. -/
theorem stochasticallyLE_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)) :
    (μ : Measure (S → Bool)).StochasticallyLE (plusState G J h β) := by
  refine stochasticallyLE_of_forall_upper_localEvents fun A hA hup ↦ ?_
  refine ge_of_tendsto (tendsto_measure_plusState G J h β hJ hβ hA) (.of_forall fun Λ ↦ ?_)
  exact stochasticallyLE_isingSpecification_plus_of_mem_GP G J h β hJ hβ hμ Λ
    (MeasurableSet.of_mem_measurableCylinders hA) hup

/-- **The minus phase is the smallest Gibbs measure for the stochastic order.**  Georgii,
Section 6.2, the paragraph after (6.9), records only the maximality of the magnetisation of
`μ₊`; the dual statement for `μ₋` is not made there. -/
theorem minusState_stochasticallyLE (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)) :
    (minusState G J h β : Measure (S → Bool)).StochasticallyLE (μ : Measure (S → Bool)) := by
  refine stochasticallyLE_of_forall_upper_localEvents fun A hA hup ↦ ?_
  refine le_of_tendsto (tendsto_measure_minusState G J h β hJ hβ hA) (.of_forall fun Λ ↦ ?_)
  exact stochasticallyLE_isingSpecification_minus_of_mem_GP G J h β hJ hβ hμ Λ
    (MeasurableSet.of_mem_measurableCylinders hA) hup

/-- The minus phase is dominated by the plus phase. -/
theorem minusState_stochasticallyLE_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) :
    (minusState G J h β : Measure (S → Bool)).StochasticallyLE (plusState G J h β) :=
  minusState_stochasticallyLE G J h β hJ hβ (plusState_mem_GP G J h β hJ hβ)

/-! ### The plus phase is the unique maximum of the stochastic order -/

/-- **The plus phase is dominated by every finite-volume `+`-boundary distribution**: it is their
decreasing limit. -/
theorem plusState_stochasticallyLE_isingSpecification_plus (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    (Λ : Finset S) :
    (plusState G J h β : Measure (S → Bool)).StochasticallyLE
      (isingSpecification G J h β Λ fun _ ↦ true) := by
  refine stochasticallyLE_of_forall_upper_localEvents fun A hA hup ↦ ?_
  refine le_of_tendsto (tendsto_measure_plusState G J h β hJ hβ hA) ?_
  filter_upwards [eventually_ge_atTop Λ] with Λ' hΛ'
  exact stochasticallyLE_isingSpecification_plus G J h β hJ hβ hΛ'
    (MeasurableSet.of_mem_measurableCylinders hA) hup

/-- **Every finite-volume `-`-boundary distribution is dominated by the minus phase**: it is their
increasing limit. -/
theorem isingSpecification_minus_stochasticallyLE_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    (Λ : Finset S) :
    (isingSpecification G J h β Λ fun _ ↦ false).StochasticallyLE
      (minusState G J h β : Measure (S → Bool)) := by
  refine stochasticallyLE_of_forall_upper_localEvents fun A hA hup ↦ ?_
  refine ge_of_tendsto (tendsto_measure_minusState G J h β hJ hβ hA) ?_
  filter_upwards [eventually_ge_atTop Λ] with Λ' hΛ'
  exact stochasticallyLE_isingSpecification_minus G J h β hJ hβ hΛ'
    (MeasurableSet.of_mem_measurableCylinders hA) hup

/-- **The plus phase is dominated by every average of finite-volume `+`-boundary distributions**
(Georgii (5.18)): the stochastic order is preserved by mixtures. -/
theorem plusState_stochasticallyLE_average (hJ : 0 ≤ J) (hβ : 0 ≤ β) {R : Finset (Finset S)}
    (hR : R.Nonempty) :
    (plusState G J h β : Measure (S → Bool)).StochasticallyLE
      ((isingSpecification G J h β).average (Measure.dirac fun _ ↦ true) R) := by
  intro A hA hup
  rw [Specification.average_apply]
  have hterm : ∀ Λ ∈ R, (plusState G J h β : Measure (S → Bool)) A
      ≤ (Measure.dirac (fun _ ↦ true : S → Bool)).bind (isingSpecification G J h β Λ) A := by
    intro Λ _
    rw [Measure.dirac_bind ((isingSpecification G J h β).measurable_kernel_toMeasure Λ)]
    exact plusState_stochasticallyLE_isingSpecification_plus G J h β hJ hβ Λ hA hup
  calc (plusState G J h β : Measure (S → Bool)) A
      = (R.card : ℝ≥0∞)⁻¹ * ((R.card : ℝ≥0∞) * (plusState G J h β : Measure (S → Bool)) A) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hR.card_pos.ne')
          (ENNReal.natCast_ne_top _), one_mul]
    _ = (R.card : ℝ≥0∞)⁻¹ * ∑ _Λ ∈ R, (plusState G J h β : Measure (S → Bool)) A := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (R.card : ℝ≥0∞)⁻¹ * ∑ Λ ∈ R, (Measure.dirac (fun _ ↦ true : S → Bool)).bind
          (isingSpecification G J h β Λ) A := mul_le_mul_right (Finset.sum_le_sum hterm) _

/-- **The plus phase is the only Gibbs measure that dominates it.**  With
`stochasticallyLE_plusState` this says that `μ₊^β` is the unique `≼`-maximum of `𝒢(βΦ)`, so any
construction of a Gibbs measure that is `≽ μ₊^β` produces `μ₊^β` itself. -/
theorem eq_plusState_of_stochasticallyLE (hJ : 0 ≤ J) (hβ : 0 ≤ β)
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β))
    (hle : (plusState G J h β : Measure (S → Bool)).StochasticallyLE μ) :
    μ = plusState G J h β :=
  ProbabilityMeasure.toMeasure_injective (Measure.StochasticallyLE.antisymm
    (stochasticallyLE_plusState G J h β hJ hβ hμ) hle)

/-- **Every local cluster point of a net dominating the plus phase which is itself a Gibbs measure
is the plus phase.**  This is the uniqueness that identifies the compactness constructions of the
plus phase (Georgii's proof of (6.9)) with the monotone boundary-condition limit. -/
theorem eq_plusState_of_mapClusterPt (hJ : 0 ≤ J) (hβ : 0 ≤ β) {ι : Type*} {l : Filter ι}
    {ms : ι → ProbabilityMeasure (S → Bool)}
    (hms : ∀ᶠ i in l, (plusState G J h β : Measure (S → Bool)).StochasticallyLE (ms i))
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β))
    (hm : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S Bool) l
      fun i ↦ WithSetwiseTopology.ofMeasure (ms i)) :
    μ = plusState G J h β := by
  refine eq_plusState_of_stochasticallyLE G J h β hJ hβ hμ ?_
  refine stochasticallyLE_of_forall_upper_localEvents fun A hA hup ↦ ?_
  refine le_eval_of_mapClusterPt hA hm ?_
  filter_upwards [hms] with i hi
  exact hi (MeasurableSet.of_mem_measurableCylinders hA) hup

end Phases

/-! ### Symmetries: shift invariance and spin-flip duality -/

section Symmetry
variable {S : Type*} [Countable S] (G : SimpleGraph S) [G.LocallyFinite] (J h β : ℝ)

private lemma le_of_add_eq_one {a b c d : ℝ≥0∞} (hab : a + b = 1) (hcd : c + d = 1)
    (hdb : d ≤ b) (hb : b ≠ ⊤) : a ≤ c := by
  refine (ENNReal.add_le_add_iff_right hb).1 ?_
  rw [hab, ← hcd]
  exact add_le_add le_rfl hdb

omit [Countable S] [G.LocallyFinite] in
/-- The push-forward of a probability measure by a transformation is a probability measure. -/
lemma isProbabilityMeasure_map_transformation {E : Type*} [MeasurableSpace E]
    (τ : Transformation S E) (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (Measure.map τ.toFun μ) :=
  ⟨by rw [Measure.map_apply τ.measurable_toFun MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

omit [Countable S] [G.LocallyFinite] in
/-- **Georgii (5.10).** The push-forward of a Gibbs measure by a symmetry of the specification
is again a Gibbs measure. -/
lemma isGibbsMeasure_map_of_isInvariant {E : Type*} [MeasurableSpace E]
    {γ : Specification S E} {τ : Transformation S E} (hτ : Specification.IsInvariant τ γ)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ) :
    γ.IsGibbsMeasure (Measure.map τ.toFun μ) := by
  classical
  have hbind := Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ
  have hprob : IsProbabilityMeasure (Measure.map τ.toFun μ) :=
    isProbabilityMeasure_map_transformation τ μ
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have hmapΛ : Finset.map τ.sites.toEmbedding (Finset.map τ.sites.symm.toEmbedding Λ) = Λ := by
    simp
  have hcomm : (fun ω ↦ (γ Λ) ω) ∘ τ.toFun
      = fun ω ↦ Measure.map τ.toFun ((γ (Finset.map τ.sites.symm.toEmbedding Λ)) ω) := by
    funext ω
    rw [Function.comp_apply, Specification.isInvariant_iff.1 hτ
      (Finset.map τ.sites.symm.toEmbedding Λ) ω, hmapΛ]
  calc (Measure.map τ.toFun μ).bind (γ Λ)
      = μ.bind ((fun ω ↦ (γ Λ) ω) ∘ τ.toFun) :=
        Measure.bind_map τ.measurable_toFun (γ.measurable_kernel_toMeasure Λ)
    _ = μ.bind (fun ω ↦ Measure.map τ.toFun
          ((γ (Finset.map τ.sites.symm.toEmbedding Λ)) ω)) := by rw [hcomm]
    _ = Measure.map τ.toFun (μ.bind (γ (Finset.map τ.sites.symm.toEmbedding Λ))) :=
        (Measure.map_bind
          (γ.measurable_kernel_toMeasure (Finset.map τ.sites.symm.toEmbedding Λ))
          τ.measurable_toFun).symm
    _ = Measure.map τ.toFun μ := by rw [hbind]

/-- The push-forward of a Gibbs measure of the Ising specification by a symmetry, as an element
of `GP`. -/
lemma map_mem_GP_isingSpecification {τ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β))
    {μ : ProbabilityMeasure (S → Bool)}
    (hμ : μ ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)) :
    (⟨Measure.map τ.toFun (μ : Measure (S → Bool)),
      isProbabilityMeasure_map_transformation τ (μ : Measure (S → Bool))⟩ :
      ProbabilityMeasure (S → Bool)) ∈ GP (S := S) (E := Bool) (isingSpecification G J h β) :=
  isGibbsMeasure_map_of_isInvariant hτ hμ

/-- A symmetry of the Ising specification moves the plus phase down in the stochastic order. -/
theorem measure_preimage_plusState_le (hJ : 0 ≤ J) (hβ : 0 ≤ β) {τ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β)) {A : Set (S → Bool)}
    (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' A)
      ≤ (plusState G J h β : Measure (S → Bool)) A := by
  have hle : Measure.map τ.toFun (plusState G J h β : Measure (S → Bool)) A
      ≤ (plusState G J h β : Measure (S → Bool)) A :=
    stochasticallyLE_plusState G J h β hJ hβ
      (map_mem_GP_isingSpecification G J h β hτ (plusState_mem_GP G J h β hJ hβ)) hA hup
  rwa [Measure.map_apply τ.measurable_toFun hA] at hle

/-- A symmetry of the Ising specification moves the minus phase up in the stochastic order. -/
theorem le_measure_preimage_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {τ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β)) {A : Set (S → Bool)}
    (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (minusState G J h β : Measure (S → Bool)) A
      ≤ (minusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' A) := by
  have hle : (minusState G J h β : Measure (S → Bool)) A
      ≤ Measure.map τ.toFun (minusState G J h β : Measure (S → Bool)) A :=
    minusState_stochasticallyLE G J h β hJ hβ
      (map_mem_GP_isingSpecification G J h β hτ (minusState_mem_GP G J h β hJ hβ)) hA hup
  rwa [Measure.map_apply τ.measurable_toFun hA] at hle

/-- **A monotone symmetry of the Ising specification whose right inverse `σ` is again a
symmetry fixes the plus phase.**  (Taking `σ = τ.inv` requires
`Specification.IsInvariant τ.inv (isingSpecification G J h β)`.) -/
theorem map_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {τ σ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β))
    (hσ : Specification.IsInvariant σ (isingSpecification G J h β))
    (hmono : Monotone τ.toFun) (hcomp : ∀ ω, τ.toFun (σ.toFun ω) = ω) :
    Measure.map τ.toFun (plusState G J h β : Measure (S → Bool))
      = (plusState G J h β : Measure (S → Bool)) := by
  have hprob : IsProbabilityMeasure
      (Measure.map τ.toFun (plusState G J h β : Measure (S → Bool))) :=
    isProbabilityMeasure_map_transformation τ (plusState G J h β : Measure (S → Bool))
  refine ext_of_forall_upEvent fun F ↦ ?_
  rw [Measure.map_apply τ.measurable_toFun (measurableSet_upEvent F)]
  refine le_antisymm (measure_preimage_plusState_le G J h β hJ hβ hτ
    (measurableSet_upEvent F) (isUpperSet_upEvent F)) ?_
  have hupper : IsUpperSet (τ.toFun ⁻¹' upEvent F) := fun a b hab ha ↦
    isUpperSet_upEvent F (hmono hab) ha
  have h1 := measure_preimage_plusState_le G J h β hJ hβ hσ
    (τ.measurable_toFun (measurableSet_upEvent F)) hupper
  have h2 : σ.toFun ⁻¹' (τ.toFun ⁻¹' upEvent F) = upEvent F := by
    ext ω
    simp only [Set.mem_preimage, hcomp ω]
  rwa [h2] at h1

/-- **A monotone symmetry of the Ising specification whose right inverse `σ` is again a
symmetry fixes the minus phase.** -/
theorem map_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {τ σ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β))
    (hσ : Specification.IsInvariant σ (isingSpecification G J h β))
    (hmono : Monotone τ.toFun) (hcomp : ∀ ω, τ.toFun (σ.toFun ω) = ω) :
    Measure.map τ.toFun (minusState G J h β : Measure (S → Bool))
      = (minusState G J h β : Measure (S → Bool)) := by
  have hprob : IsProbabilityMeasure
      (Measure.map τ.toFun (minusState G J h β : Measure (S → Bool))) :=
    isProbabilityMeasure_map_transformation τ (minusState G J h β : Measure (S → Bool))
  refine ext_of_forall_upEvent fun F ↦ ?_
  rw [Measure.map_apply τ.measurable_toFun (measurableSet_upEvent F)]
  refine le_antisymm ?_ (le_measure_preimage_minusState G J h β hJ hβ hτ
    (measurableSet_upEvent F) (isUpperSet_upEvent F))
  have hupper : IsUpperSet (τ.toFun ⁻¹' upEvent F) := fun a b hab ha ↦
    isUpperSet_upEvent F (hmono hab) ha
  have h1 := le_measure_preimage_minusState G J h β hJ hβ hσ
    (τ.measurable_toFun (measurableSet_upEvent F)) hupper
  have h2 : σ.toFun ⁻¹' (τ.toFun ⁻¹' upEvent F) = upEvent F := by
    ext ω
    simp only [Set.mem_preimage, hcomp ω]
  rwa [h2] at h1

/-- **Spin-flip duality.** An order-reversing symmetry `τ` of the Ising specification whose
right inverse `σ` is again a symmetry maps the plus phase to the minus phase.  (Georgii,
Section 6.2, *defines* `μ₋^β = τ(μ₊^β)`; here both phases are boundary-condition limits.) -/
theorem map_plusState_eq_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) {τ σ : Transformation S Bool}
    (hτ : Specification.IsInvariant τ (isingSpecification G J h β))
    (hσ : Specification.IsInvariant σ (isingSpecification G J h β))
    (hanti : Antitone τ.toFun) (hcomp : ∀ ω, τ.toFun (σ.toFun ω) = ω) :
    Measure.map τ.toFun (plusState G J h β : Measure (S → Bool))
      = (minusState G J h β : Measure (S → Bool)) := by
  have hprob : IsProbabilityMeasure
      (Measure.map τ.toFun (plusState G J h β : Measure (S → Bool))) :=
    isProbabilityMeasure_map_transformation τ (plusState G J h β : Measure (S → Bool))
  refine ext_of_forall_upEvent fun F ↦ ?_
  have hA : MeasurableSet (upEvent F) := measurableSet_upEvent F
  have hup : IsUpperSet (upEvent F) := isUpperSet_upEvent F
  rw [Measure.map_apply τ.measurable_toFun hA]
  have hCup : IsUpperSet (τ.toFun ⁻¹' (upEvent F)ᶜ) := fun a b hab ha hb ↦
    ha (hup (hanti hab) hb)
  have hCmeas : MeasurableSet (τ.toFun ⁻¹' (upEvent F)ᶜ) := τ.measurable_toFun hA.compl
  have hpre : σ.toFun ⁻¹' (τ.toFun ⁻¹' (upEvent F)ᶜ) = (upEvent F)ᶜ := by
    ext ω
    simp only [Set.mem_preimage, hcomp ω]
  have hlow : (minusState G J h β : Measure (S → Bool)) (upEvent F)
      ≤ (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' upEvent F) := by
    have hle : (minusState G J h β : Measure (S → Bool)) (upEvent F)
        ≤ Measure.map τ.toFun (plusState G J h β : Measure (S → Bool)) (upEvent F) :=
      minusState_stochasticallyLE G J h β hJ hβ
        (map_mem_GP_isingSpecification G J h β hτ (plusState_mem_GP G J h β hJ hβ)) hA hup
    rwa [Measure.map_apply τ.measurable_toFun hA] at hle
  have hkey : (minusState G J h β : Measure (S → Bool)) (upEvent F)ᶜ
      ≤ (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' (upEvent F)ᶜ) := by
    have hle : Measure.map σ.toFun (minusState G J h β : Measure (S → Bool))
          (τ.toFun ⁻¹' (upEvent F)ᶜ)
        ≤ (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' (upEvent F)ᶜ) :=
      stochasticallyLE_plusState G J h β hJ hβ
        (map_mem_GP_isingSpecification G J h β hσ (minusState_mem_GP G J h β hJ hβ)) hCmeas hCup
    rw [Measure.map_apply σ.measurable_toFun hCmeas, hpre] at hle
    exact hle
  have hsum1 : (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' upEvent F)
      + (plusState G J h β : Measure (S → Bool)) (τ.toFun ⁻¹' (upEvent F)ᶜ) = 1 := by
    rw [Set.preimage_compl, measure_add_measure_compl (τ.measurable_toFun hA)]
    exact measure_univ
  have hsum2 : (minusState G J h β : Measure (S → Bool)) (upEvent F)
      + (minusState G J h β : Measure (S → Bool)) (upEvent F)ᶜ = 1 := by
    rw [measure_add_measure_compl hA]
    exact measure_univ
  exact le_antisymm (le_of_add_eq_one hsum1 hsum2 hkey (measure_ne_top _ _)) hlow

end Symmetry

/-! ### Shift invariance on `ℤ^d` -/

section Shift
variable {d : ℕ} (J h β : ℝ)

lemma monotone_shift_toFun (j : Fin d → ℤ) : Monotone (shift Bool j).toFun := by
  intro ω ω' hω i
  simpa using hω (i - j)

lemma shift_toFun_shift_toFun_neg (j : Fin d → ℤ) (ω : (Fin d → ℤ) → Bool) :
    (shift Bool j).toFun ((shift Bool (-j)).toFun ω) = ω := by
  funext i
  simp

/-- **The plus phase on `ℤ^d` is shift invariant** (Georgii (5.11) is not needed: the plus phase
is the greatest Gibbs measure, and the shift is a monotone symmetry). -/
theorem measurePreserving_shift_plusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) (j : Fin d → ℤ) :
    MeasurePreserving (shift Bool j).toFun
      (plusState (latticeGraph d) J h β : Measure ((Fin d → ℤ) → Bool))
      (plusState (latticeGraph d) J h β : Measure ((Fin d → ℤ) → Bool)) :=
  ⟨(shift Bool j).measurable_toFun,
    map_plusState (latticeGraph d) J h β hJ hβ (isInvariant_shift_isingSpecification d J h β j)
      (isInvariant_shift_isingSpecification d J h β (-j)) (monotone_shift_toFun j)
      (shift_toFun_shift_toFun_neg j)⟩

/-- **The minus phase on `ℤ^d` is shift invariant.** -/
theorem measurePreserving_shift_minusState (hJ : 0 ≤ J) (hβ : 0 ≤ β) (j : Fin d → ℤ) :
    MeasurePreserving (shift Bool j).toFun
      (minusState (latticeGraph d) J h β : Measure ((Fin d → ℤ) → Bool))
      (minusState (latticeGraph d) J h β : Measure ((Fin d → ℤ) → Bool)) :=
  ⟨(shift Bool j).measurable_toFun,
    map_minusState (latticeGraph d) J h β hJ hβ (isInvariant_shift_isingSpecification d J h β j)
      (isInvariant_shift_isingSpecification d J h β (-j)) (monotone_shift_toFun j)
      (shift_toFun_shift_toFun_neg j)⟩

end Shift

/-! ### Spin-flip duality on `ℤ²` at zero external field -/

section SpinFlip
open MeasureTheory.GibbsMeasure.Peierls

lemma antitone_spinFlip_toFun : Antitone spinFlip.toFun := by
  intro a c hac i
  have h := hac i
  simp only [spinFlip_toFun_apply]
  cases hb : a i <;> cases hc : c i <;> simp_all

lemma spinFlip_toFun_spinFlip_toFun (ω : Site → Bool) :
    spinFlip.toFun (spinFlip.toFun ω) = ω := by
  funext i
  simp

/-- **Spin-flip duality** (Georgii, Section 6.2): on `ℤ²` at zero external field the minus phase
is the image of the plus phase under the global spin flip `σ ↦ -σ`. -/
theorem map_spinFlip_plusState (b : ℝ) (hb : 0 ≤ b) :
    Measure.map spinFlip.toFun (plusState (latticeGraph 2) 1 0 b : Measure (Site → Bool))
      = (minusState (latticeGraph 2) 1 0 b : Measure (Site → Bool)) :=
  map_plusState_eq_minusState (latticeGraph 2) 1 0 b zero_le_one hb (isInvariant_spinFlip b)
    (isInvariant_spinFlip b) antitone_spinFlip_toFun spinFlip_toFun_spinFlip_toFun

end SpinFlip

/-! ### Georgii's cube-average construction of the plus phase on `ℤ²` -/

section CubeAverage
open MeasureTheory.GibbsMeasure.Peierls

/-- **The library has one plus phase.**  Every cluster point, in the topology of local
convergence, of Georgii's cube-averaged `+`-boundary distributions — the construction in the proof
of (6.9), which produces a *shift-invariant* Gibbs measure but no uniqueness — is the monotone
boundary-condition limit `plusState`.  In particular that cluster point is unique. -/
theorem eq_plusState_of_mapClusterPt_plusCubeAverage {b : ℝ} (hb : 0 ≤ b)
    {m : ProbabilityMeasure (Site → Bool)}
    (hm : MapClusterPt (WithSetwiseTopology.ofMeasure m : WithLocalConvergence Site Bool) atTop
      fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N)) :
    m = plusState (latticeGraph 2) 1 0 b :=
  eq_plusState_of_mapClusterPt (latticeGraph 2) 1 0 b zero_le_one hb
    (ms := fun N ↦ plusCubeAverage b N)
    (.of_forall fun N ↦ plusState_stochasticallyLE_average (latticeGraph 2) 1 0 b zero_le_one hb
      (cubeTranslates_nonempty 2 N N))
    (mem_GP_of_mapClusterPt_plusCubeAverage hm) hm

/-- **Georgii's cube averages converge**, with no subsequence extraction: `μ_N → μ₊^β` in the
topology of local convergence, because the space of random fields is compact and `plusState` is
the only cluster point. -/
theorem tendsto_plusCubeAverage {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun N ↦ (WithSetwiseTopology.ofMeasure (plusCubeAverage b N) :
      WithLocalConvergence Site Bool)) atTop
      (𝓝 (WithSetwiseTopology.ofMeasure (plusState (latticeGraph 2) 1 0 b))) := by
  refine tendsto_nhds_of_unique_mapClusterPt fun v hv ↦ ?_
  obtain ⟨v⟩ := v
  exact congrArg WithSetwiseTopology.ofMeasure
    (eq_plusState_of_mapClusterPt_plusCubeAverage hb hv)

end CubeAverage

end MeasureTheory.GibbsMeasure

end

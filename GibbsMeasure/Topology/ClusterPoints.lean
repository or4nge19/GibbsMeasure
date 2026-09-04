/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import GibbsMeasure.Mathlib.Topology.Order.LiminfLimsup
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Ultrafilter

/-!
# Cluster points of locally equicontinuous families of random fields

Georgii §4.2. A family of random fields indexed along a filter is *locally equicontinuous*
(Georgii (4.6)) if on each finite volume the measures of events decreasing to `∅` tend to `0`
uniformly along the family. Over a standard Borel state space every locally equicontinuous family
has a cluster point in the topology of local convergence (Georgii (4.9)); the proof is Georgii's:
a pointwise ultrafilter limit in the compact space `ℝ≥0∞`, σ-additive on each finite volume by
equicontinuity, extends to a random field by the Kolmogorov extension theorem. Uniform domination
by finite measures yields compact sets of random fields (Georgii (4.10)).
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {ι : Type*}

/-! ### Georgii (4.6): local equicontinuity -/

/-- **Georgii (4.6).** A family `μs` of random fields, indexed along a filter `l`, is *locally
equicontinuous* if for every finite volume `Λ` and every antitone sequence of `Λ`-local events
decreasing to `∅`, the `limsup` over the family of the measures of the events tends to `0`. -/
def LocallyEquicontinuous (l : Filter ι) (μs : ι → ProbabilityMeasure (S → E)) : Prop :=
  ∀ (Λ : Finset S) (A : ℕ → Set (S → E)),
    (∀ m, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (A m)) →
    Antitone A → (⋂ m, A m) = ∅ →
    Tendsto (fun m ↦ limsup (fun i ↦ (μs i : Measure (S → E)) (A m)) l) atTop (𝓝 0)

/-- **Georgii (4.5).** A family `μs` of random fields is *equicontinuous* if for every antitone
sequence of local events (in the algebra `𝓕⁰ = localEvents S E`) decreasing to `∅`, the `limsup`
over the family of the measures of the events tends to `0`. -/
def EquicontinuousOnLocalEvents (l : Filter ι) (μs : ι → ProbabilityMeasure (S → E)) : Prop :=
  ∀ A : ℕ → Set (S → E),
    (∀ m, A m ∈ localEvents S E) → Antitone A → (⋂ m, A m) = ∅ →
    Tendsto (fun m ↦ limsup (fun i ↦ (μs i : Measure (S → E)) (A m)) l) atTop (𝓝 0)

/-- **Georgii (4.5) ⇒ (4.6).** Equicontinuity on the algebra `𝓕⁰` implies local
equicontinuity, since every `𝓕_Λ`-measurable event is a local event. -/
theorem EquicontinuousOnLocalEvents.locallyEquicontinuous {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} (h : EquicontinuousOnLocalEvents l μs) :
    LocallyEquicontinuous l μs :=
  fun Λ A hmeas hanti hempty ↦
    h A (fun m ↦ mem_localEvents_of_cylinderEvents Λ (hmeas m)) hanti hempty

/-- Local equicontinuity passes to a subnet: if `μs` is locally equicontinuous along `l` and
`g` tends to `l` along `l'`, then `μs ∘ g` is locally equicontinuous along `l'`. -/
lemma LocallyEquicontinuous.comp {ι' : Type*} {l : Filter ι} {l' : Filter ι'}
    {μs : ι → ProbabilityMeasure (S → E)} (h : LocallyEquicontinuous l μs) {g : ι' → ι}
    (hg : Tendsto g l' l) : LocallyEquicontinuous l' (μs ∘ g) := by
  intro Λ A hA hanti hinter
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h Λ A hA hanti hinter)
    (fun _ ↦ zero_le) fun m ↦ ?_
  exact hg.limsup_comp_le_limsup (u := fun i ↦ (μs i : Measure (S → E)) (A m))

/-! ### Pointwise ultrafilter limits in the compact space `ℝ≥0∞` -/

/-- The pointwise limit along an ultrafilter `U` of the evaluations `i ↦ μs i A`.
This is Georgii's `μ⁰ ∈ [0,1]^{𝓕⁰}` (we take values in the compact space `ℝ≥0∞`). -/
def ultrafilterLimit (U : Ultrafilter ι) (μs : ι → ProbabilityMeasure (S → E))
    (A : Set (S → E)) : ℝ≥0∞ :=
  (U.map fun i ↦ (μs i : Measure (S → E)) A).lim

/-- The evaluations converge along `U` to the ultrafilter limit. -/
lemma tendsto_ultrafilterLimit (U : Ultrafilter ι) (μs : ι → ProbabilityMeasure (S → E))
    (A : Set (S → E)) :
    Tendsto (fun i ↦ (μs i : Measure (S → E)) A) U (𝓝 (ultrafilterLimit U μs A)) :=
  (U.map fun i ↦ (μs i : Measure (S → E)) A).le_nhds_lim

lemma ultrafilterLimit_congr {U : Ultrafilter ι} {μs : ι → ProbabilityMeasure (S → E)}
    {A : Set (S → E)} {c : ℝ≥0∞}
    (h : Tendsto (fun i ↦ (μs i : Measure (S → E)) A) U (𝓝 c)) :
    ultrafilterLimit U μs A = c :=
  tendsto_nhds_unique (tendsto_ultrafilterLimit U μs A) h

@[simp] lemma ultrafilterLimit_empty (U : Ultrafilter ι) (μs : ι → ProbabilityMeasure (S → E)) :
    ultrafilterLimit U μs ∅ = 0 :=
  ultrafilterLimit_congr (by simp)

@[simp] lemma ultrafilterLimit_univ (U : Ultrafilter ι) (μs : ι → ProbabilityMeasure (S → E)) :
    ultrafilterLimit U μs univ = 1 :=
  ultrafilterLimit_congr (by simp)

/-- Finite additivity of the ultrafilter limit (`ℝ≥0∞` has `ContinuousAdd`). -/
lemma ultrafilterLimit_union (U : Ultrafilter ι) (μs : ι → ProbabilityMeasure (S → E))
    {A B : Set (S → E)} (hB : MeasurableSet B) (hAB : Disjoint A B) :
    ultrafilterLimit U μs (A ∪ B) = ultrafilterLimit U μs A + ultrafilterLimit U μs B :=
  ultrafilterLimit_congr <| by
    have h : ∀ i, (μs i : Measure (S → E)) (A ∪ B)
        = (μs i : Measure (S → E)) A + (μs i : Measure (S → E)) B := fun i ↦
      measure_union hAB hB
    simpa [h] using
      (tendsto_ultrafilterLimit U μs A).add (tendsto_ultrafilterLimit U μs B)

/-- The ultrafilter limit is dominated by the `limsup` along any coarser filter. -/
lemma ultrafilterLimit_le_limsup {U : Ultrafilter ι} {l : Filter ι} (hU : ↑U ≤ l)
    (μs : ι → ProbabilityMeasure (S → E)) (A : Set (S → E)) :
    ultrafilterLimit U μs A ≤ limsup (fun i ↦ (μs i : Measure (S → E)) A) l :=
  Ultrafilter.lim_le_limsup hU _

/-! ### σ-additivity on each finite-volume σ-algebra -/

/-- **Continuity at `∅` of the ultrafilter limit on a finite volume** (the heart of
Georgii's proof of (4.9)): for an antitone sequence of `Λ`-local events with empty
intersection, the ultrafilter limits tend to `0`, by local equicontinuity and
`ultrafilterLimit_le_limsup`. -/
lemma tendsto_ultrafilterLimit_zero {U : Ultrafilter ι} {l : Filter ι} (hU : ↑U ≤ l)
    {μs : ι → ProbabilityMeasure (S → E)} (hle : LocallyEquicontinuous l μs)
    (Λ : Finset S) (A : ℕ → Set (S → E))
    (hmeas : ∀ m, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (A m))
    (hanti : Antitone A) (hempty : (⋂ m, A m) = ∅) :
    Tendsto (fun m ↦ ultrafilterLimit U μs (A m)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun _ : ℕ ↦ (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h0 (hle Λ A hmeas hanti hempty)
    (fun _ ↦ zero_le) fun m ↦ ultrafilterLimit_le_limsup hU μs (A m)

/-- **σ-additivity of the ultrafilter limit on the finite volume `Λ`.**  Finite additivity plus
`tendsto_ultrafilterLimit_zero` applied to the tails `Λ.restrict ⁻¹' (⋃ n ≥ m, f n)`. -/
lemma ultrafilterLimit_iUnion {U : Ultrafilter ι} {l : Filter ι} (hU : ↑U ≤ l)
    {μs : ι → ProbabilityMeasure (S → E)} (hle : LocallyEquicontinuous l μs)
    (Λ : Finset S) ⦃f : ℕ → Set (Π _ : Λ, E)⦄ (hf : ∀ n, MeasurableSet (f n))
    (hdisj : Pairwise (Function.onFun Disjoint f)) :
    ultrafilterLimit U μs (⋃ n, Λ.restrict ⁻¹' f n)
      = ∑' n, ultrafilterLimit U μs (Λ.restrict ⁻¹' f n) := by
  classical
  set C : Set (Set (S → E)) :=
    {A | MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A} with hC_def
  have hC : IsSetRing C := by
    constructor
    · exact @MeasurableSet.empty _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))
    · intro s t hs ht
      have hs' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] s := hs
      have ht' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] t := ht
      exact hs'.union ht'
    · intro s t hs ht
      have hs' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] s := hs
      have ht' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] t := ht
      exact hs'.diff ht'
  set μc : AddContent ℝ≥0∞ C := hC.addContent_of_union (fun A ↦ ultrafilterLimit U μs A)
    (ultrafilterLimit_empty U μs)
    (fun {s t} _ ht hdis ↦
      ultrafilterLimit_union U μs (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ ht) hdis)
  have hfC : ∀ n, Λ.restrict ⁻¹' f n ∈ C := fun n ↦ by
    rw [hC_def, mem_ofPred_eq, cylinderEvents_eq_comap_finsetRestrict]
    exact ⟨f n, hf n, rfl⟩
  have hUfC : (⋃ n, Λ.restrict ⁻¹' f n) ∈ C := by
    have h : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
        (Λ.restrict ⁻¹' f n) := hfC
    exact MeasurableSet.iUnion h
  have h_ne_top : ∀ s ∈ C, μc s ≠ ∞ := fun s _ ↦
    ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ∞)
      (le_trans (ultrafilterLimit_le_limsup le_rfl μs s)
        (limsup_le_of_le (h := Eventually.of_forall fun i ↦ prob_le_one)))
  exact addContent_iUnion_eq_sum_of_tendsto_zero hC μc h_ne_top
    (fun s hs hanti hempty ↦ tendsto_ultrafilterLimit_zero hU hle Λ s hs hanti hempty)
    hfC hUfC (fun n m hnm ↦ Disjoint.preimage _ (hdisj hnm))

/-! ### The finite-volume marginal measures -/

variable {U : Ultrafilter ι} {l : Filter ι} {μs : ι → ProbabilityMeasure (S → E)}

/-- The finite-volume marginal of the ultrafilter limit, as a measure on `Π _ : Λ, E`,
built by `Measure.ofMeasurable` from σ-additivity (`ultrafilterLimit_iUnion`). -/
def finVolMeasure (hU : ↑U ≤ l) (hle : LocallyEquicontinuous l μs) (Λ : Finset S) :
    Measure (Π _ : Λ, E) :=
  Measure.ofMeasurable (fun B _ ↦ ultrafilterLimit U μs (Λ.restrict ⁻¹' B))
    (by simp)
    (fun f hf hdisj ↦ by
      rw [preimage_iUnion]; exact ultrafilterLimit_iUnion hU hle Λ hf hdisj)

@[simp] lemma finVolMeasure_apply (hU : ↑U ≤ l) (hle : LocallyEquicontinuous l μs) (Λ : Finset S)
    {B : Set (Π _ : Λ, E)} (hB : MeasurableSet B) :
    finVolMeasure hU hle Λ B = ultrafilterLimit U μs (Λ.restrict ⁻¹' B) :=
  Measure.ofMeasurable_apply B hB

lemma isProbabilityMeasure_finVolMeasure (hU : ↑U ≤ l) (hle : LocallyEquicontinuous l μs)
    (Λ : Finset S) : IsProbabilityMeasure (finVolMeasure hU hle Λ) :=
  ⟨by rw [finVolMeasure_apply hU hle Λ MeasurableSet.univ]; simp⟩

/-! ### Projectivity and the Kolmogorov extension -/

/-- **Consistency of the marginals** (Georgii's "consistent system of marginal
distributions"): `restrict₂ ∘ I.restrict = J.restrict` is definitional, so the
pushforward of the `I`-marginal is the `J`-marginal. -/
lemma isProjectiveMeasureFamily_finVolMeasure (hU : ↑U ≤ l)
    (hle : LocallyEquicontinuous l μs) :
    IsProjectiveMeasureFamily (α := fun _ : S ↦ E) (finVolMeasure hU hle) := by
  intro I J hJI
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.map_apply (μ := finVolMeasure hU hle I) (Finset.measurable_restrict₂ hJI) hB,
    finVolMeasure_apply hU hle J hB,
    finVolMeasure_apply hU hle I ((Finset.measurable_restrict₂ hJI) hB),
    ← preimage_comp, Finset.restrict₂_comp_restrict]

/-- **Kolmogorov extension step**: the limit random field.  `StandardBorelSpace (Π _ : Λ, E)`
is found by `StandardBorelSpace.pi_countable`. -/
lemma exists_isProjectiveLimit_finVolMeasure [StandardBorelSpace E] (hU : ↑U ≤ l)
    (hle : LocallyEquicontinuous l μs) :
    ∃ μ : Measure (S → E), IsProjectiveLimit μ (finVolMeasure hU hle) :=
  have : ∀ Λ : Finset S, IsFiniteMeasure (finVolMeasure hU hle Λ) := fun Λ ↦
    haveI := isProbabilityMeasure_finVolMeasure hU hle Λ; inferInstance
  exists_isProjectiveLimit_of_standardBorel (isProjectiveMeasureFamily_finVolMeasure hU hle)

/-- The projective limit evaluates to the ultrafilter limit on every local event. -/
lemma eval_localEvents_of_isProjectiveLimit {hU : ↑U ≤ l} {hle : LocallyEquicontinuous l μs}
    {ν : Measure (S → E)} (hν : IsProjectiveLimit ν (finVolMeasure hU hle))
    {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    ν A = ultrafilterLimit U μs A := by
  obtain ⟨Λ, B, hB, rfl⟩ := mem_localEvents_iff_exists_finsetRestrict_preimage.1 hA
  rw [← Measure.map_apply Λ.measurable_restrict hB, hν Λ, finVolMeasure_apply hU hle Λ hB]

lemma isProbabilityMeasure_of_isProjectiveLimit_finVol {hU : ↑U ≤ l}
    {hle : LocallyEquicontinuous l μs} {ν : Measure (S → E)}
    (hν : IsProjectiveLimit ν (finVolMeasure hU hle)) :
    IsProbabilityMeasure ν :=
  ⟨by
    have := eval_localEvents_of_isProjectiveLimit hν (A := univ)
      (mem_localEvents_of_cylinderEvents ∅ MeasurableSet.univ)
    simpa using this⟩

/-! ### Georgii (4.9) -/

/-- **Ultrafilter form of Georgii (4.9)**: along any ultrafilter refining `l`, a locally
equicontinuous family converges in the topology of local convergence. -/
theorem exists_tendsto_of_locallyEquicontinuous [StandardBorelSpace E]
    {μs : ι → WithLocalConvergence S E} (U : Ultrafilter ι) {l : Filter ι} (hU : ↑U ≤ l)
    (hle : LocallyEquicontinuous l fun i ↦ (μs i).toMeasure) :
    ∃ μ : WithLocalConvergence S E, Tendsto μs U (𝓝 μ) := by
  obtain ⟨ν, hν⟩ := exists_isProjectiveLimit_finVolMeasure hU hle
  have hprob : IsProbabilityMeasure ν := isProbabilityMeasure_of_isProjectiveLimit_finVol hν
  refine ⟨WithSetwiseTopology.ofMeasure ⟨ν, hprob⟩, ?_⟩
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  have hcoe : (((WithSetwiseTopology.ofMeasure ⟨ν, hprob⟩ :
      WithLocalConvergence S E)).toMeasure : Measure (S → E)) A = ν A := rfl
  rw [hcoe, eval_localEvents_of_isProjectiveLimit hν hA]
  exact tendsto_ultrafilterLimit U _ A

/-- **Georgii Proposition (4.9).**  Over a standard Borel state space, every locally
equicontinuous net of random fields has a cluster point in the topology of local
convergence. -/
theorem exists_mapClusterPt_of_locallyEquicontinuous [StandardBorelSpace E]
    {μs : ι → WithLocalConvergence S E} {l : Filter ι} [l.NeBot]
    (hle : LocallyEquicontinuous l fun i ↦ (μs i).toMeasure) :
    ∃ μ : WithLocalConvergence S E, MapClusterPt μ l μs := by
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le l
  obtain ⟨μ, hμ⟩ := exists_tendsto_of_locallyEquicontinuous U hU hle
  exact ⟨μ, mapClusterPt_iff_ultrafilter.2 ⟨U, hU, hμ⟩⟩

/-! ### Georgii (4.10): compact sets of random fields -/

variable (S E) in
/-- The random fields dominated on each finite volume by the finite measure `ν Λ`
(Georgii's set `𝒦` in Corollary (4.10)). Georgii's `ν_Λ` lives on the sub-σ-algebra `𝓕_Λ`;
since only the values on `𝓕_Λ`-events enter, taking full product-σ-algebra measures is
equivalent for `Nonempty E` (extend along the section used in the `(4.11)(2)` instance below). -/
def dominatedBy (ν : Finset S → Measure (S → E)) : Set (WithLocalConvergence S E) :=
  {μ | ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄,
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
    (μ.toMeasure : Measure (S → E)) A ≤ ν Λ A}

@[simp] lemma mem_dominatedBy {ν : Finset S → Measure (S → E)}
    {μ : WithLocalConvergence S E} :
    μ ∈ dominatedBy S E ν ↔ ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
      (μ.toMeasure : Measure (S → E)) A ≤ ν Λ A :=
  Iff.rfl

/-- **Eventual pointwise domination implies local equicontinuity**: the special case of
Georgii's *local uniform domination* (the remark before (4.10)) with linear modulus, which is
the case used in (4.10)–(4.13). -/
lemma locallyEquicontinuous_of_eventually_le {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} (ν : Finset S → Measure (S → E))
    [∀ Λ, IsFiniteMeasure (ν Λ)]
    (hdom : ∀ Λ : Finset S, ∀ᶠ i in l, ∀ ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
      (μs i : Measure (S → E)) A ≤ ν Λ A) :
    LocallyEquicontinuous l μs := by
  intro Λ A hmeas hanti hempty
  have hbound : ∀ m, limsup (fun i ↦ (μs i : Measure (S → E)) (A m)) l ≤ ν Λ (A m) := fun m ↦
    limsup_le_of_le (h := (hdom Λ).mono fun i hi ↦ hi (hmeas m))
  have hν : Tendsto (fun m ↦ ν Λ (A m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := ν Λ)
      (fun m ↦ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ (hmeas m)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rwa [hempty, measure_empty] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hν
    (fun _ ↦ zero_le) hbound

lemma isClosed_dominatedBy (ν : Finset S → Measure (S → E)) :
    IsClosed (dominatedBy S E ν) := by
  have h : dominatedBy S E ν = ⋂ (Λ : Finset S), ⋂ (A : Set (S → E)),
      ⋂ (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A),
        {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) A ≤ ν Λ A} := by
    ext μ
    simp only [dominatedBy, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isClosed_iInter fun Λ ↦ isClosed_iInter fun A ↦ isClosed_iInter fun hA ↦
    isClosed_le (WithSetwiseTopology.continuous_apply_enn
      (mem_localEvents_of_cylinderEvents Λ hA)) continuous_const

/-- **Georgii Corollary (4.10).**  The set of random fields uniformly dominated on each finite
volume by a finite measure is compact in the topology of local convergence. -/
theorem isCompact_dominatedBy [StandardBorelSpace E] (ν : Finset S → Measure (S → E))
    [∀ Λ, IsFiniteMeasure (ν Λ)] : IsCompact (dominatedBy S E ν) := by
  have hK : IsClosed (dominatedBy S E ν) := isClosed_dominatedBy ν
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro U hU
  have hKU : dominatedBy S E ν ∈ U := le_principal_iff.1 hU
  have hle : LocallyEquicontinuous (↑U : Filter (WithLocalConvergence S E))
      (fun μ ↦ μ.toMeasure) :=
    locallyEquicontinuous_of_eventually_le ν fun Λ ↦
      Filter.mem_of_superset hKU fun μ hμ ↦ hμ Λ
  obtain ⟨μ, hμ⟩ := exists_tendsto_of_locallyEquicontinuous
    (μs := fun μ : WithLocalConvergence S E ↦ μ) U le_rfl hle
  have hUμ : (↑U : Filter (WithLocalConvergence S E)) ≤ 𝓝 μ := hμ
  have hmem : μ ∈ dominatedBy S E ν := by
    have := mem_closure_iff_ultrafilter.2 ⟨U, hKU, hUμ⟩
    rwa [hK.closure_eq] at this
  exact ⟨μ, hmem, hUμ⟩

/-! ### Georgii (4.11)(2): for a finite state space, the space of random fields is compact -/

/-- **Georgii Example (4.11)(2).**  Over a finite state space, the whole space of random fields is
compact in the topology of local convergence: every random field is dominated by the counting-type
measures `ν Λ (σ_Λ ∈ A) = |A|`. (`MeasurableSingletonClass E` encodes Georgii's discrete reading
of a finite state space.) -/
instance [Finite E] [MeasurableSingletonClass E] :
    CompactSpace (WithLocalConvergence S E) := by
  classical
  rcases isEmpty_or_nonempty (S → E) with h | h
  · constructor
    have hempty : IsEmpty (WithLocalConvergence S E) := ⟨fun μ ↦ by
      have hμ : IsProbabilityMeasure (μ.toMeasure : Measure (S → E)) := μ.toMeasure.2
      have h0 : (μ.toMeasure : Measure (S → E)) univ = 0 := by
        rw [Set.univ_eq_empty_iff.2 h]; exact measure_empty
      rw [hμ.measure_univ] at h0
      exact one_ne_zero h0⟩
    rw [Set.univ_eq_empty_iff.2 hempty]
    exact isCompact_empty
  · obtain ⟨η₀⟩ := h
    constructor
    -- the section `Π i : Λ, E → (S → E)` extending by `η₀`
    set sec : ∀ Λ : Finset S, (Π _ : Λ, E) → (S → E) := fun Λ x j ↦
      if hj : j ∈ Λ then x ⟨j, hj⟩ else η₀ j with hsec
    have hsecmeas : ∀ Λ, Measurable (sec Λ) := fun Λ ↦
      measurable_pi_lambda _ fun j ↦ by
        by_cases hj : j ∈ Λ
        · simpa [hsec, hj] using measurable_pi_apply (⟨j, hj⟩ : Λ)
        · simpa [hsec, hj] using measurable_const
    have hsecres : ∀ (Λ : Finset S) (x : Π _ : Λ, E), Λ.restrict (sec Λ x) = x := by
      intro Λ x
      funext i
      simp [hsec, i.2]
    set ν : Finset S → Measure (S → E) := fun Λ ↦ Measure.count.map (sec Λ) with hν
    have : ∀ Λ, IsFiniteMeasure (ν Λ) := fun Λ ↦ by
      rw [hν]
      exact Measure.isFiniteMeasure_map _ _
    have hdom : (univ : Set (WithLocalConvergence S E)) = dominatedBy S E ν := by
      refine (Set.eq_of_subset_of_subset (fun μ _ ↦ ?_) (subset_univ _))
      intro Λ A hA
      have hμ : IsProbabilityMeasure (μ.toMeasure : Measure (S → E)) := μ.toMeasure.2
      rw [cylinderEvents_eq_comap_finsetRestrict] at hA
      obtain ⟨B, hB, rfl⟩ := hA
      rcases eq_empty_or_nonempty B with rfl | ⟨b, hb⟩
      · simp
      · have hAmeas : MeasurableSet (Λ.restrict ⁻¹' B : Set (S → E)) :=
          Λ.measurable_restrict hB
        have hcount : ν Λ (Λ.restrict ⁻¹' B) = Measure.count B := by
          rw [hν, Measure.map_apply (hsecmeas Λ) hAmeas, ← Set.preimage_comp]
          congr 1
          ext x
          simp [Function.comp_def, hsecres Λ]
        have hone : (1 : ℝ≥0∞) ≤ Measure.count B := by
          rw [Measure.count_apply hB]
          exact_mod_cast Set.one_le_encard_iff_nonempty.2 ⟨b, hb⟩
        calc (μ.toMeasure : Measure (S → E)) (Λ.restrict ⁻¹' B) ≤ 1 := prob_le_one
          _ ≤ Measure.count B := hone
          _ = ν Λ (Λ.restrict ⁻¹' B) := hcount.symm
    rw [hdom]
    exact isCompact_dominatedBy ν

/-- **Georgii (4.4), the necessary condition.** If `μ` is a cluster point of the family `μs`
along `l`, then for every antitone sequence of local events decreasing to `∅` the `liminf` of the
evaluations tends to `0`. -/
theorem tendsto_liminf_zero_of_mapClusterPt {l : Filter ι}
    {μs : ι → WithLocalConvergence S E} {μ : WithLocalConvergence S E}
    (hcp : MapClusterPt μ l μs)
    (A : ℕ → Set (S → E)) (hA : ∀ m, A m ∈ localEvents S E)
    (hanti : Antitone A) (hempty : (⋂ m, A m) = ∅) :
    Tendsto (fun m ↦ liminf (fun i ↦ ((μs i).toMeasure : Measure (S → E)) (A m)) l)
      atTop (𝓝 0) := by
  obtain ⟨U, hUle, hUconv⟩ := mapClusterPt_iff_ultrafilter.1 hcp
  have heval : ∀ m, Tendsto (fun i ↦ ((μs i).toMeasure : Measure (S → E)) (A m)) U
      (𝓝 ((μ.toMeasure : Measure (S → E)) (A m))) := fun m ↦
    tendsto_withLocalConvergence_iff.1 hUconv (A m) (hA m)
  have hbound : ∀ m, liminf (fun i ↦ ((μs i).toMeasure : Measure (S → E)) (A m)) l
      ≤ (μ.toMeasure : Measure (S → E)) (A m) := by
    intro m
    calc liminf (fun i ↦ ((μs i).toMeasure : Measure (S → E)) (A m)) l
        ≤ liminf (fun i ↦ ((μs i).toMeasure : Measure (S → E)) (A m)) U :=
          liminf_le_liminf_of_le hUle
      _ = (μ.toMeasure : Measure (S → E)) (A m) := (heval m).liminf_eq
  have hμ0 : Tendsto (fun m ↦ (μ.toMeasure : Measure (S → E)) (A m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := (μ.toMeasure : Measure (S → E)))
      (fun m ↦ (MeasurableSet.of_mem_measurableCylinders (hA m)).nullMeasurableSet)
      hanti ⟨0, measure_ne_top _ _⟩
    rwa [hempty, measure_empty] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hμ0
    (fun _ ↦ zero_le) hbound

end MeasureTheory.GibbsMeasure

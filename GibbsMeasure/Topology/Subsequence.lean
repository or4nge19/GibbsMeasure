/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Topology.ClusterPoints
public import GibbsMeasure.Topology.LocalConvergence

/-!
# Georgii Proposition (4.15)

A cluster point of a locally equicontinuous sequence of random fields is the limit of a
subsequence.
-/

@[expose] public section

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### A countable generating π-system for a finite-volume cylinder σ-algebra -/

section PiSystem

variable {α : Type*}

/-- The family of finite intersections of a family of sets: the π-system it generates. -/
def finiteInters (b : Set (Set α)) : Set (Set α) :=
  Set.range fun F : Finset b ↦ ⋂ x ∈ F, (x : Set α)

lemma subset_finiteInters (b : Set (Set α)) : b ⊆ finiteInters b := by
  classical
  intro s hs
  exact ⟨{⟨s, hs⟩}, by simp⟩

lemma countable_finiteInters {b : Set (Set α)} (hb : b.Countable) :
    (finiteInters b).Countable := by
  have := hb.to_subtype
  exact Set.countable_range _

lemma isPiSystem_finiteInters (b : Set (Set α)) : IsPiSystem (finiteInters b) := by
  classical
  rintro _ ⟨F₁, rfl⟩ _ ⟨F₂, rfl⟩ -
  refine ⟨F₁ ∪ F₂, ?_⟩
  ext y
  simp only [Set.mem_iInter, Finset.mem_union, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (Or.inl hi), fun i hi ↦ h i (Or.inr hi)⟩
  · rintro ⟨h₁, h₂⟩ i (hi | hi)
    · exact h₁ i hi
    · exact h₂ i hi

lemma generateFrom_finiteInters (b : Set (Set α)) :
    MeasurableSpace.generateFrom (finiteInters b) = MeasurableSpace.generateFrom b := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
    (MeasurableSpace.generateFrom_mono (subset_finiteInters b))
  rintro _ ⟨F, rfl⟩
  exact F.measurableSet_biInter fun x _ ↦ MeasurableSpace.measurableSet_generateFrom x.2

lemma generateFrom_iUnion' {ι : Sort*} (s : ι → Set (Set α)) :
    MeasurableSpace.generateFrom (⋃ i, s i) = ⨆ i, MeasurableSpace.generateFrom (s i) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
    (iSup_le fun i ↦ MeasurableSpace.generateFrom_mono (Set.subset_iUnion s i))
  intro t ht
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
  exact (le_iSup (fun i ↦ MeasurableSpace.generateFrom (s i)) i) _
    (MeasurableSpace.measurableSet_generateFrom hi)

end PiSystem

/-! ### The countable seed algebra `𝒜⁰` of Georgii (4.15) -/

section Seeds

open MeasurableSpace

variable {S E : Type*} [MeasurableSpace E]

/-- The countable family of coordinate generators of the cylinder σ-algebra `𝓕_Λ` of a finite
volume `Λ`, over a countably generated state space. -/
def coordGen [CountablyGenerated E] (Λ : Finset S) : Set (Set (S → E)) :=
  ⋃ i ∈ (Λ : Set S), (fun G ↦ (fun ω : S → E ↦ ω i) ⁻¹' G) '' countableGeneratingSet E

lemma countable_coordGen [CountablyGenerated E] (Λ : Finset S) :
    (coordGen (S := S) (E := E) Λ).Countable :=
  Λ.countable_toSet.biUnion fun _ _ ↦ countable_countableGeneratingSet.image _

lemma generateFrom_coordGen [CountablyGenerated E] (Λ : Finset S) :
    generateFrom (coordGen (S := S) (E := E) Λ)
      = cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) := by
  rw [coordGen, cylinderEvents, generateFrom_iUnion']
  refine iSup_congr fun i ↦ ?_
  rw [generateFrom_iUnion']
  refine iSup_congr fun _ ↦ ?_
  rw [← comap_generateFrom, generateFrom_countableGeneratingSet]

/-- **Georgii (4.15), the algebra `𝒜⁰_Λ`.** A countable π-system generating the finite-volume
σ-algebra `𝓕_Λ`. Georgii builds it from the Radon–Nikodym densities `h_{n,Λ}`; over a countably
generated state space one can take the finite intersections of coordinate generators, which is
enough (and, unlike Georgii's, does not depend on the sequence of measures). -/
def localGen [CountablyGenerated E] (Λ : Finset S) : Set (Set (S → E)) :=
  finiteInters (coordGen Λ)

lemma countable_localGen [CountablyGenerated E] (Λ : Finset S) :
    (localGen (S := S) (E := E) Λ).Countable :=
  countable_finiteInters (countable_coordGen Λ)

lemma isPiSystem_localGen [CountablyGenerated E] (Λ : Finset S) :
    IsPiSystem (localGen (S := S) (E := E) Λ) :=
  isPiSystem_finiteInters _

lemma generateFrom_localGen [CountablyGenerated E] (Λ : Finset S) :
    generateFrom (localGen (S := S) (E := E) Λ)
      = cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) := by
  rw [localGen, generateFrom_finiteInters, generateFrom_coordGen]

lemma localGen_subset_localEvents [CountablyGenerated E] (Λ : Finset S) :
    localGen (S := S) (E := E) Λ ⊆ localEvents S E := by
  intro A hA
  refine mem_localEvents_of_cylinderEvents Λ ?_
  rw [← generateFrom_localGen (S := S) (E := E) Λ]
  exact measurableSet_generateFrom hA

variable (S E) in
/-- **Georgii (4.15), the countable algebra `𝒜⁰ = ⋃_Λ 𝒜⁰_Λ`.** -/
def dynkinSeeds [Countable S] [CountablyGenerated E] : Set (Set (S → E)) :=
  ⋃ Λ : Finset S, localGen Λ

lemma countable_dynkinSeeds [Countable S] [CountablyGenerated E] :
    (dynkinSeeds S E).Countable :=
  Set.countable_iUnion fun Λ ↦ countable_localGen Λ

lemma localGen_subset_dynkinSeeds [Countable S] [CountablyGenerated E] (Λ : Finset S) :
    localGen (S := S) (E := E) Λ ⊆ dynkinSeeds S E :=
  Set.subset_iUnion (fun Λ : Finset S ↦ localGen (S := S) (E := E) Λ) Λ

lemma univ_mem_dynkinSeeds [Countable S] [CountablyGenerated E] :
    Set.univ ∈ dynkinSeeds S E := by
  refine localGen_subset_dynkinSeeds ∅ ?_
  exact ⟨∅, by simp⟩

lemma nonempty_dynkinSeeds [Countable S] [CountablyGenerated E] :
    (dynkinSeeds S E).Nonempty :=
  ⟨Set.univ, univ_mem_dynkinSeeds⟩

end Seeds

/-! ### Georgii Proposition (4.15) -/

section Georgii415

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii Proposition (4.15).** A cluster point of a locally equicontinuous *sequence* of
random fields is the limit of a subsequence.

Georgii's proof uses the Radon–Nikodym densities `h_{n,Λ}` of `μ_n|𝓕_Λ` with respect to
`ν = ∑ 2⁻ⁿ μ_n` in order to produce a countable generating π-system of a sub-σ-algebra of `𝓕_Λ`
carrying the restrictions `μ_n|𝓕_Λ`. Here we assume instead that `E` is countably generated —
which holds in the standard Borel setting of §4.2, and is what makes `𝓕_Λ` itself countably
generated — and run Georgii's diagonal and Dynkin-system argument on the resulting countable
π-system `𝒜⁰ = ⋃_Λ 𝒜⁰_Λ` (`dynkinSeeds`). -/
theorem exists_subseq_tendsto_of_mapClusterPt [Countable S]
    [MeasurableSpace.CountablyGenerated E]
    {μs : ℕ → WithLocalConvergence S E} {μ : WithLocalConvergence S E}
    (hle : LocallyEquicontinuous atTop fun n ↦ (μs n).toMeasure)
    (hcp : MapClusterPt μ atTop μs) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  classical
  -- Georgii's countable algebra `𝒜⁰ = {A₁, A₂, …}`
  obtain ⟨A, hA⟩ :=
    (countable_dynkinSeeds (S := S) (E := E)).exists_eq_range nonempty_dynkinSeeds
  have hAmem : ∀ ℓ, A ℓ ∈ dynkinSeeds S E := fun ℓ ↦ hA ▸ Set.mem_range_self ℓ
  have hAloc : ∀ ℓ, A ℓ ∈ localEvents S E := by
    intro ℓ
    obtain ⟨Λ, hΛ⟩ := Set.mem_iUnion.1 (hAmem ℓ)
    exact localGen_subset_localEvents Λ hΛ
  -- the diagonal subsequence: a cluster point in the metrizable space `ℕ → ℝ≥0∞`
  set T : WithLocalConvergence S E → (ℕ → ℝ≥0∞) :=
    fun ν ℓ ↦ ((ν.toMeasure : Measure (S → E)) (A ℓ)) with hT
  have hTcont : Continuous T :=
    continuous_pi fun ℓ ↦ WithSetwiseTopology.continuous_apply_enn (hAloc ℓ)
  have hcp' : MapClusterPt (T μ) atTop (T ∘ μs) :=
    hcp.map hTcont.continuousAt (le_of_eq Filter.map_map)
  obtain ⟨φ, hφ, hφlim⟩ := hcp'.tendsto_subseq
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hcoord : ∀ ℓ, Tendsto (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) (A ℓ)) atTop
      (𝓝 ((μ.toMeasure : Measure (S → E)) (A ℓ))) := fun ℓ ↦ tendsto_pi_nhds.1 hφlim ℓ
  refine ⟨φ, hφ, ?_⟩
  rw [tendsto_withLocalConvergence_iff]
  -- Georgii's Dynkin-system argument, volume by volume
  have key : ∀ (Λ : Finset S) (t : Set (S → E)),
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] t →
      Tendsto (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) t) atTop
        (𝓝 ((μ.toMeasure : Measure (S → E)) t)) := by
    intro Λ
    refine @MeasurableSpace.induction_on_inter (S → E)
      (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S))
      (fun t _ ↦ Tendsto (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) t) atTop
        (𝓝 ((μ.toMeasure : Measure (S → E)) t)))
      (localGen Λ) (generateFrom_localGen Λ).symm (isPiSystem_localGen Λ) ?_ ?_ ?_ ?_
    · simp
    · intro t ht
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, A ℓ = t := by
        have : t ∈ Set.range A := hA ▸ localGen_subset_dynkinSeeds Λ ht
        exact this
      exact hℓ ▸ hcoord ℓ
    · intro t htm h
      have htm' : MeasurableSet t := cylinderEvents_le_pi (X := fun _ : S ↦ E) _ htm
      have hc : ∀ ν : ProbabilityMeasure (S → E),
          ((ν : Measure (S → E)) tᶜ) = 1 - (ν : Measure (S → E)) t := by
        intro ν
        have : IsProbabilityMeasure (ν : Measure (S → E)) := ν.2
        exact prob_compl_eq_one_sub htm'
      simp only [hc]
      exact ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl (by simp))
    · intro f hdisj hfm hf
      have hfm' : ∀ i, MeasurableSet (f i) := fun i ↦
        cylinderEvents_le_pi (X := fun _ : S ↦ E) _ (hfm i)
      set C : ℕ → Set (S → E) := fun m ↦ ⋃ i ∈ Finset.range m, f i with hC
      have hCmono : Monotone C := fun m₁ m₂ hm ↦
        Set.iUnion₂_subset fun i hi ↦
          Set.subset_iUnion₂ (s := fun i (_ : i ∈ Finset.range m₂) ↦ f i) i
            (Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hm))
      have hCsub : ∀ m, C m ⊆ ⋃ i, f i := fun m ↦
        Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion f i
      have hCmeas : ∀ m, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (C m) :=
        fun m ↦ Finset.measurableSet_biUnion _ fun i _ ↦ hfm i
      have hCmeas' : ∀ m, MeasurableSet (C m) := fun m ↦
        cylinderEvents_le_pi (X := fun _ : S ↦ E) _ (hCmeas m)
      -- the finite unions converge
      have hCsum : ∀ (ν : Measure (S → E)) (m : ℕ),
          ν (C m) = ∑ i ∈ Finset.range m, ν (f i) := fun ν m ↦
        measure_biUnion_finset (hdisj.set_pairwise _) fun i _ ↦ hfm' i
      have hCconv : ∀ m, Tendsto (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) (C m)) atTop
          (𝓝 ((μ.toMeasure : Measure (S → E)) (C m))) := by
        intro m
        simp only [hCsum]
        exact tendsto_finsetSum _ fun i _ ↦ hf i
      -- the tail `B \ C m ↓ ∅`
      have hdiffmeas : ∀ m,
          MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] ((⋃ i, f i) \ C m) :=
        fun m ↦ (MeasurableSet.iUnion hfm).diff (hCmeas m)
      have hanti : Antitone fun m ↦ (⋃ i, f i) \ C m := fun m₁ m₂ hm ↦
        Set.sdiff_subset_sdiff_right (hCmono hm)
      have hempty : (⋂ m, (⋃ i, f i) \ C m) = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (Set.mem_iInter.1 hx 0).1
        exact (Set.mem_iInter.1 hx (i + 1)).2
          (Set.mem_iUnion₂.2 ⟨i, Finset.self_mem_range_succ i, hi⟩)
      have hM := hle Λ (fun m ↦ (⋃ i, f i) \ C m) hdiffmeas hanti hempty
      -- upper bound on the `limsup` along the subsequence
      have hup : limsup (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) (⋃ i, f i)) atTop
          ≤ (μ.toMeasure : Measure (S → E)) (⋃ i, f i) := by
        refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
        have hhalf : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 :=
          ENNReal.half_pos (by simpa using hε.ne')
        obtain ⟨m, hm⟩ := (hM.eventually_lt_const hhalf).exists
        have hev1 : ∀ᶠ k in atTop,
            ((μs (φ k)).toMeasure : Measure (S → E)) ((⋃ i, f i) \ C m) < (ε : ℝ≥0∞) / 2 :=
          hφtop.eventually (eventually_lt_of_limsup_lt hm)
        have hev2 : ∀ᶠ k in atTop, ((μs (φ k)).toMeasure : Measure (S → E)) (C m)
            < (μ.toMeasure : Measure (S → E)) (C m) + (ε : ℝ≥0∞) / 2 :=
          (hCconv m).eventually_lt_const (ENNReal.lt_add_right (measure_ne_top _ _) hhalf.ne')
        refine Filter.limsup_le_of_le (h := ?_)
        filter_upwards [hev1, hev2] with k h1 h2
        have hsplit : ((μs (φ k)).toMeasure : Measure (S → E)) ((⋃ i, f i) \ C m)
            + ((μs (φ k)).toMeasure : Measure (S → E)) (C m)
            = ((μs (φ k)).toMeasure : Measure (S → E)) (⋃ i, f i) := by
          have := measure_sdiff_add_inter (μ := ((μs (φ k)).toMeasure : Measure (S → E)))
            (⋃ i, f i) (hCmeas' m)
          rwa [Set.inter_eq_self_of_subset_right (hCsub m)] at this
        calc ((μs (φ k)).toMeasure : Measure (S → E)) (⋃ i, f i)
            = ((μs (φ k)).toMeasure : Measure (S → E)) ((⋃ i, f i) \ C m)
              + ((μs (φ k)).toMeasure : Measure (S → E)) (C m) := hsplit.symm
          _ ≤ (ε : ℝ≥0∞) / 2 + ((μ.toMeasure : Measure (S → E)) (C m) + (ε : ℝ≥0∞) / 2) :=
              add_le_add h1.le h2.le
          _ = (μ.toMeasure : Measure (S → E)) (C m) + ε := by
              rw [add_comm ((ε : ℝ≥0∞) / 2), add_assoc, ENNReal.add_halves]
          _ ≤ (μ.toMeasure : Measure (S → E)) (⋃ i, f i) + ε := by
              gcongr
              exact hCsub m
      -- lower bound on the `liminf` along the subsequence
      have hlow : (μ.toMeasure : Measure (S → E)) (⋃ i, f i)
          ≤ liminf (fun k ↦ ((μs (φ k)).toMeasure : Measure (S → E)) (⋃ i, f i)) atTop := by
        have hμC : Tendsto (fun m ↦ (μ.toMeasure : Measure (S → E)) (C m)) atTop
            (𝓝 ((μ.toMeasure : Measure (S → E)) (⋃ m, C m))) :=
          tendsto_measure_iUnion_atTop hCmono
        have hunion : (⋃ m, C m) = ⋃ i, f i := by
          refine Set.Subset.antisymm (Set.iUnion_subset hCsub) (Set.iUnion_subset fun i ↦ ?_)
          exact fun x hx ↦ Set.mem_iUnion.2
            ⟨i + 1, Set.mem_iUnion₂.2 ⟨i, Finset.self_mem_range_succ i, hx⟩⟩
        rw [hunion] at hμC
        refine le_of_tendsto hμC (Eventually.of_forall fun m ↦ ?_)
        rw [← (hCconv m).liminf_eq]
        exact liminf_le_liminf (Eventually.of_forall fun k ↦ measure_mono (hCsub m))
      exact tendsto_of_le_liminf_of_limsup_le hlow hup
  intro B hB
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hB
  exact key Λ B hΛ

/-- **Georgii (4.15)** for a sequence of probability measures. -/
theorem exists_strictMono_tendsto_of_mapClusterPt [Countable S] [StandardBorelSpace E]
    {μs : ℕ → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)}
    (hle : LocallyEquicontinuous atTop μs)
    (hcp : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) atTop
      fun n ↦ (WithSetwiseTopology.ofMeasure (μs n) : WithLocalConvergence S E)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ (WithSetwiseTopology.ofMeasure (μs (φ k)) : WithLocalConvergence S E))
        atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  exists_subseq_tendsto_of_mapClusterPt
    (μs := fun n ↦ (WithSetwiseTopology.ofMeasure (μs n) : WithLocalConvergence S E)) hle hcp

/-- **Georgii (4.9) + (4.15).** Over a standard Borel state space, every locally equicontinuous
sequence of random fields has a subsequence converging in the topology of local convergence. -/
theorem exists_subseq_tendsto_of_locallyEquicontinuous [Countable S] [StandardBorelSpace E]
    {μs : ℕ → WithLocalConvergence S E}
    (hle : LocallyEquicontinuous atTop fun n ↦ (μs n).toMeasure) :
    ∃ (μ : WithLocalConvergence S E) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := exists_mapClusterPt_of_locallyEquicontinuous hle
  obtain ⟨φ, hφ, h⟩ := exists_subseq_tendsto_of_mapClusterPt hle hμ
  exact ⟨μ, φ, hφ, h⟩

end Georgii415

end MeasureTheory.GibbsMeasure

end

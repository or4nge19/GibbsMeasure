/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Countable cores of a σ-algebra

A **countable core** of a measurable space `(Ω, 𝓕)` is a countable π-system `𝒞` generating `𝓕`
which is *complete for setwise limits of probability measures*: whenever `μₙ A` converges for
every `A ∈ 𝒞`, there is a probability measure `ν` with `ν A = limₙ μₙ A` on `𝒞`. Such an `ν` is
unique, since `𝒞` is a generating π-system.

The point of the notion is **compactness**: the coarsest topology on the probability measures
making `μ ↦ μ A` continuous for `A ∈ 𝒞` is then compact and metrizable. That is done in
`GibbsMeasure/Mathlib/MeasureTheory/Measure/SetwiseCompact.lean`; this file constructs the cores.

## Main definitions and results

* `MeasurableSpace.IsCountableCore`: the definition.
* `MeasurableSpace.IsCountableCore.ext`: the limit measure is unique.
* `MeasurableSpace.IsCountableCore.comap`: transport along a surjection `φ` with
  `𝓕 = φ⁻¹ 𝓕'`, and `MeasurableSpace.IsCountableCore.comap_measurableEquiv` along a Borel
  isomorphism.
* `MeasureTheory.boolCylinder`, `MeasurableSpace.isCountableCore_range_boolCylinder`: the basic
  clopen events of a Cantor cube `γ → Bool` over a countable index `γ` form a countable core.
* `MeasurableSpace.isCountableCore_preimage_image_of_isClopen`: the general construction. A
  countable clopen generating π-system of a compact space pulls back, along a measurable embedding
  with **closed** range, to a countable core.
* `MeasureTheory.exists_measurableEmbedding_natBool_isClosed_range`: every standard Borel space is
  Borel isomorphic to a closed subset of the Cantor space.
* `MeasurableSpace.exists_isCountableCore`: **every standard Borel space has a countable core**.
* `MeasurableSpace.exists_isCountableCore_subset_measurableCylinders`: over a countable index set
  and standard Borel factors, the core can be taken to consist of **cylinder events**.

## Implementation notes

The limit measure of condition (ii) is obtained from the compactness of the space of probability
measures on a compact space (`MeasureTheory.instCompactSpaceProbabilityMeasure`, i.e. Prokhorov's
theorem via Riesz-Markov-Kakutani) together with the portmanteau theorem, rather than from
Georgii's Carathéodory extension of the finitely additive set function `A ↦ lim μₙ A`. The two
arguments use compactness at the same point: Georgii's `σ`-additivity comes from "a decreasing
sequence of compact cylinder events with empty intersection is eventually empty", which is what
makes the space of probability measures compact in the first place.

The closedness of `range f` cannot be dropped, and is what replaces Georgii's case distinction
between the three model spaces of the isomorphism theorem (4.A6): the half-open interval `(0, 1]`
is a standard Borel space, but the traces on it of the dyadic cylinder events of `[0, 1]` do
**not** form a countable core — the Dirac measures at `1/n` converge on all of them, with no
limit measure on `(0, 1]`.

## References

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Definition (4.A9), Comment (4.A10)(2),
Theorem (4.A11) and Corollary (4.A13).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasurableSpace

variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  {𝒞 : Set (Set Ω)} {𝒞' : Set (Set Ω')}

/-- **Georgii (4.A9).** A **countable core** of a measurable space `(Ω, 𝓕)`: a countable
π-system `𝒞` generating `𝓕` such that every sequence of probability measures which converges
setwise on `𝒞` converges setwise on `𝒞` *to a probability measure*.

The last condition is the substantive one: it fails for the traces on `(0, 1]` of the dyadic
intervals of `[0, 1]`, while it holds for the cylinder events of a Cantor cube. -/
structure IsCountableCore {Ω : Type*} [m : MeasurableSpace Ω] (𝒞 : Set (Set Ω)) : Prop where
  /-- A countable core is countable. -/
  countable : 𝒞.Countable
  /-- A countable core is stable under finite intersections, Georgii (4.A9)(i). -/
  isPiSystem : IsPiSystem 𝒞
  /-- A countable core generates the σ-algebra, Georgii (4.A9)(i). -/
  generateFrom_eq : generateFrom 𝒞 = m
  /-- **Georgii (4.A9)(ii).** A sequence of probability measures converging setwise on the core
  converges setwise on the core to a probability measure. -/
  exists_isProbabilityMeasure_tendsto (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
      (hlim : ∀ A ∈ 𝒞, ∃ c : ℝ≥0∞, Tendsto (fun n ↦ μ n A) atTop (𝓝 c)) :
    ∃ ν : Measure Ω, IsProbabilityMeasure ν ∧
      ∀ A ∈ 𝒞, Tendsto (fun n ↦ μ n A) atTop (𝓝 (ν A))

namespace IsCountableCore

lemma measurableSet (h : IsCountableCore 𝒞) {A : Set Ω} (hA : A ∈ 𝒞) : MeasurableSet A :=
  h.generateFrom_eq ▸ measurableSet_generateFrom hA

/-- The limit measure in Georgii (4.A9)(ii) is unique: two probability measures agreeing on a
countable core are equal. -/
theorem ext (h : IsCountableCore 𝒞) {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : ∀ A ∈ 𝒞, μ A = ν A) : μ = ν :=
  ext_of_generate_finite 𝒞 h.generateFrom_eq.symm h.isPiSystem hμν (by simp)

/-- Adjoining the whole space to a countable core gives a countable core. -/
theorem insert_univ (h : IsCountableCore 𝒞) : IsCountableCore (insert univ 𝒞) where
  countable := h.countable.insert _
  isPiSystem := by
    rintro s (rfl | hs) t (rfl | ht) hst
    · simp
    · simp [ht]
    · simp [hs]
    · exact Or.inr (h.isPiSystem s hs t ht hst)
  generateFrom_eq := by
    refine le_antisymm ?_ ?_
    · refine generateFrom_le ?_
      rintro t (rfl | ht)
      · exact MeasurableSet.univ
      · exact h.measurableSet ht
    · exact h.generateFrom_eq.ge.trans (generateFrom_mono (subset_insert _ _))
  exists_isProbabilityMeasure_tendsto μ hμ hlim := by
    obtain ⟨ν, hν, htendsto⟩ :=
      h.exists_isProbabilityMeasure_tendsto μ hμ fun A hA ↦ hlim A (mem_insert_of_mem _ hA)
    refine ⟨ν, hν, ?_⟩
    rintro A (rfl | hA)
    · have := hν
      simp only [measure_univ]
      exact tendsto_const_nhds
    · exact htendsto A hA

/-- **Georgii (4.A10)(2).** If `φ : Ω → Ω'` is onto and `𝓕 = φ⁻¹𝓕'`, then the `φ`-preimages of a
countable core of `𝓕'` form a countable core of `𝓕`. -/
theorem comap {φ : Ω → Ω'} (hφ : Function.Surjective φ) (hcomap : MeasurableSpace.comap φ mΩ' = mΩ)
    (h : IsCountableCore 𝒞') : IsCountableCore (preimage φ '' 𝒞') := by
  have hφm : Measurable φ := measurable_iff_comap_le.2 hcomap.le
  -- the section `s` of `φ` is measurable, because every event of `Ω` is a `φ`-preimage
  have hs : Measurable (Function.surjInv hφ) := by
    refine measurable_iff_comap_le.2 ?_
    rw [← hcomap, MeasurableSpace.comap_comp]
    exact le_of_eq (by rw [Function.rightInverse_surjInv hφ |>.comp_eq_id]; simp)
  refine ⟨h.countable.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    obtain ⟨x, hx⟩ := hne
    refine ⟨A ∩ B, h.isPiSystem A hA B hB ⟨φ x, hx.1, hx.2⟩, ?_⟩
    simp [preimage_inter]
  · rw [← MeasurableSpace.comap_generateFrom, h.generateFrom_eq, hcomap]
  · intro μ hμ hlim
    have := hμ
    have hprob : ∀ n, IsProbabilityMeasure ((μ n).map φ) := fun n ↦
      Measure.isProbabilityMeasure_map hφm.aemeasurable
    have hval : ∀ (n : ℕ) (A : Set Ω'), MeasurableSet A → ((μ n).map φ) A = μ n (φ ⁻¹' A) :=
      fun n A hA ↦ Measure.map_apply hφm hA
    obtain ⟨ν, hν, htendsto⟩ :=
      h.exists_isProbabilityMeasure_tendsto (fun n ↦ (μ n).map φ) hprob fun A hA ↦ by
        obtain ⟨c, hc⟩ := hlim _ ⟨A, hA, rfl⟩
        exact ⟨c, by simpa only [hval _ A (h.measurableSet hA)] using hc⟩
    have := hν
    refine ⟨ν.map (Function.surjInv hφ), Measure.isProbabilityMeasure_map hs.aemeasurable, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    have hAm : MeasurableSet A := h.measurableSet hA
    have hpre : (ν.map (Function.surjInv hφ)) (φ ⁻¹' A) = ν A := by
      rw [Measure.map_apply hs (hφm hAm), ← preimage_comp,
        (Function.rightInverse_surjInv hφ).comp_eq_id, preimage_id]
    rw [hpre]
    simpa only [hval _ A hAm] using htendsto A hA

/-- **Georgii (4.A10)(2)** for a Borel isomorphism: a countable core transports along a
measurable equivalence. -/
theorem comap_measurableEquiv (e : Ω ≃ᵐ Ω') (h : IsCountableCore 𝒞') :
    IsCountableCore (preimage e '' 𝒞') :=
  h.comap e.surjective (MeasurableEmbedding.iff_comap_eq.1 e.measurableEmbedding).2.1

end IsCountableCore

/-! ### The core produced by a compact model -/

/-- **The construction behind Georgii (4.A11).** Let `X` be a compact space whose σ-algebra is
generated by a countable π-system `𝒟` of *clopen* sets, and let `f : Ω → X` be a measurable
embedding whose range is *closed*. Then `f⁻¹𝒟` is a countable core of `Ω`.

The limit measure of (4.A9)(ii) is a cluster point `ν` of the image measures `μₙ ∘ f⁻¹`, which
exists because the probability measures on a compact space are compact (Prokhorov). Portmanteau
for the closed set `range f` shows `ν (range f) = 1`, so `ν` pulls back to a probability measure
on `Ω`; portmanteau for a set with empty boundary shows `ν A = lim μₙ (f⁻¹A)` on `𝒟`. -/
theorem isCountableCore_preimage_image_of_isClopen {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [HasOuterApproxClosed X] [mX : MeasurableSpace X] [BorelSpace X]
    {𝒟 : Set (Set X)} (hcount : 𝒟.Countable) (hpi : IsPiSystem 𝒟)
    (hclopen : ∀ A ∈ 𝒟, IsClopen A) (hgen : generateFrom 𝒟 = mX)
    {f : Ω → X} (hf : MeasurableEmbedding f) (hrange : IsClosed (range f)) :
    IsCountableCore (preimage f '' 𝒟) := by
  have hmeas : ∀ A ∈ 𝒟, MeasurableSet A := fun A hA ↦ hgen ▸ measurableSet_generateFrom hA
  refine ⟨hcount.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
    obtain ⟨x, hx⟩ := hne
    exact ⟨A ∩ B, hpi A hA B hB ⟨f x, hx.1, hx.2⟩, by simp [preimage_inter]⟩
  · rw [← MeasurableSpace.comap_generateFrom, hgen]
    exact (MeasurableEmbedding.iff_comap_eq.1 hf).2.1
  · intro μ hμ hlim
    have := hμ
    -- the image measures on the compact model
    set P : ℕ → ProbabilityMeasure X := fun n ↦
      ⟨(μ n).map f, Measure.isProbabilityMeasure_map hf.measurable.aemeasurable⟩ with hP
    obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (Filter.map P atTop)
    set L : Filter (ProbabilityMeasure X) := 𝓝 ν ⊓ Filter.map P atTop with hLdef
    have : L.NeBot := hν
    have hLnhds : Tendsto (id : ProbabilityMeasure X → ProbabilityMeasure X) L (𝓝 ν) :=
      tendsto_id.mono_left inf_le_left
    have hLmap : L ≤ Filter.map P atTop := inf_le_right
    have hPapply : ∀ (n : ℕ) (A : Set X), MeasurableSet A →
        ((P n : Measure X)) A = μ n (f ⁻¹' A) := fun n A hA ↦ by
      simpa [hP] using Measure.map_apply hf.measurable hA
    -- `ν` is carried by the closed set `range f`
    have hcarrier : (ν : Measure X) (range f) = 1 := by
      have h1 : (L.limsup fun ρ : ProbabilityMeasure X ↦ (ρ : Measure X) (range f))
          ≤ (ν : Measure X) (range f) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hLnhds hrange
      have h2 : ∀ᶠ ρ : ProbabilityMeasure X in L, (ρ : Measure X) (range f) = 1 :=
        Filter.Eventually.filter_mono hLmap (Filter.eventually_map.2 (.of_forall fun n ↦ by
          rw [hPapply n _ hf.measurableSet_range, preimage_range]; exact measure_univ))
      rw [Filter.limsup_congr h2, limsup_const] at h1
      exact le_antisymm prob_le_one h1
    have hcompl : (ν : Measure X) (range f)ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hf.measurableSet_range]
      exact hcarrier
    refine ⟨(ν : Measure X).comap f, ⟨by rw [hf.comap_apply, image_univ, hcarrier]⟩, ?_⟩
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨c, hc⟩ := hlim _ ⟨A, hA, rfl⟩
    have hνA : (ν : Measure X) A = c := by
      refine tendsto_nhds_unique
        (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hLnhds
          (by simp [(hclopen A hA).frontier_eq])) ?_
      refine Tendsto.mono_left ?_ hLmap
      rw [tendsto_map'_iff]
      simpa only [Function.comp_def, id_eq, hPapply _ A (hmeas A hA)] using hc
    have : ((ν : Measure X).comap f) (f ⁻¹' A) = (ν : Measure X) A := by
      rw [hf.comap_apply, image_preimage_eq_inter_range, measure_inter_conull hcompl]
    rw [this, hνA]
    exact hc

/-- A countable clopen generating π-system of a compact space is a countable core. -/
theorem isCountableCore_of_isClopen {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [HasOuterApproxClosed X] [mX : MeasurableSpace X] [BorelSpace X] {𝒟 : Set (Set X)}
    (hcount : 𝒟.Countable) (hpi : IsPiSystem 𝒟) (hclopen : ∀ A ∈ 𝒟, IsClopen A)
    (hgen : generateFrom 𝒟 = mX) : IsCountableCore 𝒟 := by
  have := isCountableCore_preimage_image_of_isClopen hcount hpi hclopen hgen
    (MeasurableEmbedding.id (α := X)) (by simp)
  simpa using this

end MeasurableSpace

/-! ### The Cantor cube -/

namespace MeasureTheory

variable {γ : Type*}

/-- The basic clopen event of the Cantor cube `γ → Bool` prescribed by a finite set `J` of
(coordinate, value) pairs. These sets form a countable π-system generating the product σ-algebra,
and they are compact, which is what makes them a countable core. -/
def boolCylinder (J : Finset (γ × Bool)) : Set (γ → Bool) := {x | ∀ q ∈ J, x q.1 = q.2}

@[simp] lemma mem_boolCylinder {J : Finset (γ × Bool)} {x : γ → Bool} :
    x ∈ boolCylinder J ↔ ∀ q ∈ J, x q.1 = q.2 := Iff.rfl

lemma boolCylinder_eq_iInter (J : Finset (γ × Bool)) :
    boolCylinder J = ⋂ q ∈ J, (fun x : γ → Bool ↦ x q.1) ⁻¹' {q.2} := by
  ext x; simp [boolCylinder]

lemma isClopen_boolCylinder (J : Finset (γ × Bool)) : IsClopen (boolCylinder J) := by
  rw [boolCylinder_eq_iInter]
  exact isClopen_biInter_finset fun q _ ↦
    (isClopen_discrete {q.2}).preimage (continuous_apply q.1)

lemma measurableSet_boolCylinder (J : Finset (γ × Bool)) :
    MeasurableSet[MeasurableSpace.pi] (boolCylinder J) := by
  rw [boolCylinder_eq_iInter]
  exact MeasurableSet.biInter J.countable_toSet fun q _ ↦
    (measurable_pi_apply q.1) (measurableSet_singleton q.2)

@[simp] lemma boolCylinder_union [DecidableEq (γ × Bool)] (J K : Finset (γ × Bool)) :
    boolCylinder (J ∪ K) = boolCylinder J ∩ boolCylinder K := by
  ext x
  simp only [mem_boolCylinder, Set.mem_inter_iff, Finset.mem_union]
  exact ⟨fun h ↦ ⟨fun q hq ↦ h q (Or.inl hq), fun q hq ↦ h q (Or.inr hq)⟩,
    fun h q hq ↦ hq.elim (h.1 q) (h.2 q)⟩

lemma isPiSystem_range_boolCylinder : IsPiSystem (range (boolCylinder (γ := γ))) := by
  classical
  rintro _ ⟨J, rfl⟩ _ ⟨K, rfl⟩ -
  exact ⟨J ∪ K, boolCylinder_union J K⟩

lemma countable_range_boolCylinder [Countable γ] :
    (range (boolCylinder (γ := γ))).Countable := countable_range _

/-- The basic clopen events generate the product σ-algebra of the Cantor cube. -/
lemma generateFrom_range_boolCylinder :
    MeasurableSpace.generateFrom (range (boolCylinder (γ := γ))) = MeasurableSpace.pi := by
  refine le_antisymm ?_ ?_
  · exact MeasurableSpace.generateFrom_le (by rintro _ ⟨J, rfl⟩; exact measurableSet_boolCylinder J)
  · refine iSup_le fun i ↦ ?_
    rintro _ ⟨t, -, rfl⟩
    have hpre : (fun x : γ → Bool ↦ x i) ⁻¹' t = ⋃ b ∈ t, boolCylinder {(i, b)} := by
      ext x; simp [boolCylinder]
    rw [hpre]
    exact MeasurableSet.biUnion t.to_countable fun b _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨_, rfl⟩

end MeasureTheory

namespace MeasurableSpace

open MeasureTheory

/-- **Georgii (4.A11), Case 3.** Over a countable index set, the basic clopen events of the Cantor
cube `γ → Bool` form a countable core: they are compact, so a setwise limit of probability
measures along them is `σ`-additive. -/
theorem isCountableCore_range_boolCylinder {γ : Type*} [Countable γ] :
    IsCountableCore (range (boolCylinder (γ := γ))) :=
  isCountableCore_of_isClopen countable_range_boolCylinder isPiSystem_range_boolCylinder
    (by rintro _ ⟨J, rfl⟩; exact isClopen_boolCylinder J) generateFrom_range_boolCylinder

end MeasurableSpace

/-! ### Standard Borel spaces are closed subsets of the Cantor space -/

namespace MeasureTheory

/-- The sequences with at most one `true`: a countably infinite *closed* subset of the Cantor
space, and the range of `MeasureTheory.optionNatToNatBool`. -/
def atMostOneTrue : Set (ℕ → Bool) := {x | ∀ i j, x i = true → x j = true → i = j}

/-- The parametrisation of `MeasureTheory.atMostOneTrue` by `Option ℕ`: `some n` is sent to the
indicator of `{n}` and `none` to the constant sequence `false`. -/
def optionNatToNatBool (o : Option ℕ) : ℕ → Bool := fun k ↦ decide (o = some k)

lemma injective_optionNatToNatBool : Function.Injective optionNatToNatBool := by
  intro o o' h
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some m =>
      have := congrFun h m
      simp [optionNatToNatBool] at this
  | some n =>
    have hn : optionNatToNatBool o' n = true := by
      rw [← h]; simp [optionNatToNatBool]
    simp only [optionNatToNatBool, decide_eq_true_eq] at hn
    exact hn.symm

lemma range_optionNatToNatBool : range optionNatToNatBool = atMostOneTrue := by
  ext x
  constructor
  · rintro ⟨o, rfl⟩ i j hi hj
    simp only [optionNatToNatBool, decide_eq_true_eq] at hi hj
    exact Option.some_injective _ (hi ▸ hj)
  · intro hx
    by_cases h : ∃ n, x n = true
    · obtain ⟨n, hn⟩ := h
      have hxk : ∀ k, x k = decide (n = k) := fun k ↦ by
        by_cases hk : x k = true
        · have hkn : k = n := hx k n hk hn
          subst hkn
          simp [hk]
        · simp only [Bool.not_eq_true] at hk
          rw [hk]
          refine (decide_eq_false ?_).symm
          rintro rfl
          rw [hk] at hn
          exact Bool.false_ne_true hn
      exact ⟨some n, funext fun k ↦ by simp [optionNatToNatBool, hxk k]⟩
    · push Not at h
      refine ⟨none, funext fun k ↦ ?_⟩
      simpa [optionNatToNatBool] using (h k)

lemma isClosed_atMostOneTrue : IsClosed atMostOneTrue := by
  have : atMostOneTrue = ⋂ i, ⋂ j, {x : ℕ → Bool | x i = true → x j = true → i = j} := by
    ext x; simp [atMostOneTrue]
  rw [this]
  refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_
  by_cases hij : i = j
  · simp [hij]
  · have : {x : ℕ → Bool | x i = true → x j = true → i = j}
        = ((fun x : ℕ → Bool ↦ x i) ⁻¹' {true} ∩ (fun x : ℕ → Bool ↦ x j) ⁻¹' {true})ᶜ := by
      ext x; simp [hij]
    rw [this]
    exact (((isClopen_discrete {true}).preimage (continuous_apply i)).inter
      ((isClopen_discrete {true}).preimage (continuous_apply j))).isOpen.isClosed_compl

/-- **The form of Georgii's isomorphism theorem (4.A6) used for (4.A11).** Every standard Borel
space is Borel isomorphic to a **closed** subset of the Cantor space `ℕ → Bool`: an uncountable
one to the whole cube, a countably infinite one to the sequences with at most one `true`, a finite
one to a finite subset of those.

Closedness is what makes the cylinder events pull back to a *countable core*: a merely Borel
range would let the limit measure escape. -/
theorem exists_measurableEmbedding_natBool_isClosed_range (Ω : Type*) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] :
    ∃ f : Ω → (ℕ → Bool), MeasurableEmbedding f ∧ IsClosed (range f) := by
  by_cases hcount : Countable Ω
  · have := hcount
    have : MeasurableSingletonClass Ω := by
      let _ := upgradeStandardBorel Ω
      infer_instance
    rcases finite_or_infinite Ω with hfin | hinf
    · obtain ⟨e, he⟩ := Countable.exists_injective_nat Ω
      refine ⟨fun x ↦ optionNatToNatBool (some (e x)), ?_, ?_⟩
      · exact (measurable_of_countable _).measurableEmbedding
          (injective_optionNatToNatBool.comp (Option.some_injective _ |>.comp he))
      · exact (Set.finite_range _).isClosed
    · obtain ⟨e⟩ : Nonempty (Ω ≃ Option ℕ) := nonempty_equiv_of_countable
      refine ⟨optionNatToNatBool ∘ e, ?_, ?_⟩
      · exact (measurable_of_countable _).measurableEmbedding
          (injective_optionNatToNatBool.comp e.injective)
      · rw [Set.range_comp, e.range_eq_univ, image_univ, range_optionNatToNatBool]
        exact isClosed_atMostOneTrue
  · refine ⟨PolishSpace.measurableEquivNatBoolOfNotCountable hcount,
      (PolishSpace.measurableEquivNatBoolOfNotCountable hcount).measurableEmbedding, ?_⟩
    rw [(PolishSpace.measurableEquivNatBoolOfNotCountable hcount).surjective.range_eq]
    exact isClosed_univ

end MeasureTheory

namespace MeasurableSpace

open MeasureTheory

/-- **Georgii (4.A11), first half.** The σ-algebra of a standard Borel space has a countable
core. -/
theorem exists_isCountableCore (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    ∃ 𝒞 : Set (Set Ω), IsCountableCore 𝒞 := by
  obtain ⟨f, hf, hclosed⟩ := exists_measurableEmbedding_natBool_isClosed_range Ω
  exact ⟨_, isCountableCore_preimage_image_of_isClopen countable_range_boolCylinder
    isPiSystem_range_boolCylinder (by rintro _ ⟨J, rfl⟩; exact isClopen_boolCylinder J)
    generateFrom_range_boolCylinder hf hclosed⟩

/-! ### Cylinder cores of a countable product -/

section Cylinders

variable {ι : Type*} {α : ι → Type*}

/-- The events cut out by finitely many binary digits of coordinatewise maps
`f i : α i → (ℕ → Bool)` into the Cantor space: `J` prescribes the value of the `n`-th digit of
`f i (ω i)` for finitely many pairs `(i, n)`.

For Borel embeddings `f i` with closed range this is Georgii's countable core of cylinder events,
Corollary (4.A13). Keeping the construction explicit — rather than only its existence — is what
lets one check that the core is stable under a relabelling of the coordinates. -/
def cylinderCore (f : ∀ i, α i → ℕ → Bool) : Set (Set (∀ i, α i)) :=
  range fun J : Finset ((ι × ℕ) × Bool) ↦ {ω | ∀ q ∈ J, f q.1.1 (ω q.1.1) q.1.2 = q.2}

/-- The coordinatewise embedding of `∀ i, α i` into the Cantor cube over `ι × ℕ` attached to a
family of maps `f i : α i → (ℕ → Bool)`. -/
def cantorEmbedding (f : ∀ i, α i → ℕ → Bool) : (∀ i, α i) → (ι × ℕ) → Bool :=
  fun ω p ↦ f p.1 (ω p.1) p.2

lemma mem_cylinderCore_iff {f : ∀ i, α i → ℕ → Bool} {A : Set (∀ i, α i)} :
    A ∈ cylinderCore f ↔
      ∃ J : Finset ((ι × ℕ) × Bool), A = {ω | ∀ q ∈ J, f q.1.1 (ω q.1.1) q.1.2 = q.2} :=
  ⟨fun ⟨J, hJ⟩ ↦ ⟨J, hJ.symm⟩, fun ⟨J, hJ⟩ ↦ ⟨J, hJ.symm⟩⟩

/-- `cylinderCore f` is the pullback along `cantorEmbedding f` of the basic clopen events of the
Cantor cube. -/
lemma cylinderCore_eq_preimage_image (f : ∀ i, α i → ℕ → Bool) :
    cylinderCore f = preimage (cantorEmbedding f) '' range boolCylinder := by
  rw [cylinderCore, ← Set.range_comp]
  rfl

lemma injective_cantorEmbedding {f : ∀ i, α i → ℕ → Bool} (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (cantorEmbedding f) := by
  intro ω ω' h
  funext i
  refine hf i (funext fun n ↦ ?_)
  exact congrFun h (i, n)

lemma measurable_cantorEmbedding [∀ i, MeasurableSpace (α i)] {f : ∀ i, α i → ℕ → Bool}
    (hf : ∀ i, Measurable (f i)) :
    Measurable (cantorEmbedding f) :=
  Measurable.of_eval fun p ↦
    (measurable_pi_apply p.2).comp ((hf p.1).comp (measurable_pi_apply p.1))

lemma range_cantorEmbedding (f : ∀ i, α i → ℕ → Bool) :
    range (cantorEmbedding f) =
      ⋂ i, (fun x : (ι × ℕ) → Bool ↦ fun n ↦ x (i, n)) ⁻¹' range (f i) := by
  ext x
  simp only [mem_range, mem_iInter, mem_preimage]
  constructor
  · rintro ⟨ω, rfl⟩ i
    exact ⟨ω i, rfl⟩
  · intro hx
    choose g hg using hx
    exact ⟨g, funext fun p ↦ congrFun (hg p.1) p.2⟩

lemma isClosed_range_cantorEmbedding {f : ∀ i, α i → ℕ → Bool}
    (hclosed : ∀ i, IsClosed (range (f i))) : IsClosed (range (cantorEmbedding f)) := by
  rw [range_cantorEmbedding]
  exact isClosed_iInter fun i ↦
    (hclosed i).preimage (continuous_pi fun n ↦ continuous_apply (i, n))

/-- **Georgii (4.A13).** The events cut out by finitely many binary digits of coordinatewise Borel
embeddings with closed range form a countable core of the product σ-algebra. -/
theorem isCountableCore_cylinderCore [∀ i, MeasurableSpace (α i)] [Countable ι]
    [∀ i, StandardBorelSpace (α i)]
    {f : ∀ i, α i → ℕ → Bool} (hf : ∀ i, MeasurableEmbedding (f i))
    (hclosed : ∀ i, IsClosed (range (f i))) : IsCountableCore (cylinderCore f) := by
  rw [cylinderCore_eq_preimage_image]
  refine isCountableCore_preimage_image_of_isClopen countable_range_boolCylinder
    isPiSystem_range_boolCylinder (by rintro _ ⟨J, rfl⟩; exact isClopen_boolCylinder J)
    generateFrom_range_boolCylinder ?_ (isClosed_range_cantorEmbedding hclosed)
  exact (measurable_cantorEmbedding fun i ↦ (hf i).measurable).measurableEmbedding
    (injective_cantorEmbedding fun i ↦ (hf i).injective)

/-- The events of `MeasurableSpace.cylinderCore` are cylinder events: each of them depends on the
finitely many coordinates named by `J`. -/
theorem cylinderCore_subset_measurableCylinders [∀ i, MeasurableSpace (α i)]
    {f : ∀ i, α i → ℕ → Bool} (hf : ∀ i, Measurable (f i)) :
    cylinderCore f ⊆ measurableCylinders α := by
  classical
  have hsingle : ∀ q : (ι × ℕ) × Bool,
      {ω : ∀ i, α i | f q.1.1 (ω q.1.1) q.1.2 = q.2} ∈ measurableCylinders α := by
    intro q
    refine (mem_measurableCylinders _).2 ⟨{q.1.1},
      {y : ∀ j : ({q.1.1} : Finset ι), α j |
        f q.1.1 (y ⟨q.1.1, Finset.mem_singleton_self _⟩) q.1.2 = q.2}, ?_, rfl⟩
    exact ((measurable_pi_apply q.1.2).comp ((hf q.1.1).comp
      (measurable_pi_apply (⟨q.1.1, Finset.mem_singleton_self _⟩ : ({q.1.1} : Finset ι)))))
      (measurableSet_singleton q.2)
  have key : ∀ J : Finset ((ι × ℕ) × Bool),
      {ω : ∀ i, α i | ∀ q ∈ J, f q.1.1 (ω q.1.1) q.1.2 = q.2} ∈ measurableCylinders α := by
    intro J
    induction J using Finset.induction with
    | empty => simpa using univ_mem_measurableCylinders α
    | insert q J hq ih =>
      have hins : {ω : ∀ i, α i | ∀ r ∈ insert q J, f r.1.1 (ω r.1.1) r.1.2 = r.2}
          = {ω : ∀ i, α i | f q.1.1 (ω q.1.1) q.1.2 = q.2} ∩
            {ω : ∀ i, α i | ∀ r ∈ J, f r.1.1 (ω r.1.1) r.1.2 = r.2} := by
        ext ω; simp
      rw [hins]
      exact inter_mem_measurableCylinders (hsingle q) ih
  rintro _ ⟨J, rfl⟩
  exact key J

/-- **Georgii (4.A13).** Over a countable index set and standard Borel factors, the product
σ-algebra has a countable core consisting of cylinder events. -/
theorem exists_isCountableCore_subset_measurableCylinders (α : ι → Type*)
    [∀ i, MeasurableSpace (α i)] [Countable ι] [∀ i, StandardBorelSpace (α i)] :
    ∃ 𝒞 ⊆ measurableCylinders α, IsCountableCore 𝒞 := by
  choose f hf hclosed using fun i ↦ exists_measurableEmbedding_natBool_isClosed_range (α i)
  exact ⟨cylinderCore f, cylinderCore_subset_measurableCylinders fun i ↦ (hf i).measurable,
    isCountableCore_cylinderCore hf hclosed⟩

end Cylinders

end MeasurableSpace

end

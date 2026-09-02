/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Ergodicity
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.CountablyGeneratedModNull
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.MeasureTheory.Measure.MeasuredSets

/-!
# Ergodic Gibbs measures (Georgii §14.1–14.2: (14.9), (14.14), (14.15))

Let `Θ` be a countable subgroup of the transformation group `T` of configuration space `S → E`
(Georgii: the shift group of `ℤ^d`), `𝓘 = invariantEvents Θ` the invariant σ-algebra (14.2),
`𝓟_Θ = invariantFields Θ` the `Θ`-invariant random fields (14.1), and `𝓣 = tailSigmaAlgebra S E`
the tail σ-algebra.

## Main results

* `exists_measurableSet_tail_measure_symmDiff_eq_zero` — **Proposition (14.9)**: for
  `μ ∈ 𝓟_Θ`, `𝓘 ⊆ 𝓣` `μ`-a.s.: every `A ∈ 𝓘` has a `B ∈ 𝓣` with `μ (A ∆ B) = 0`. In particular
  a tail-trivial `μ ∈ 𝓟_Θ` is ergodic (`mem_trivialOn_invariantEvents_of_mem_trivialOn_tail`,
  `ergodicSMul_of_mem_trivialOn_tail`).
* `invariantG γ Θ` — **display (14.14)**: `𝒢_Θ(γ) = 𝒢(γ) ∩ 𝓟_Θ`, the `Θ`-invariant Gibbs
  measures, defined as that intersection.
* `extremePoints_invariantG` — **Theorem (14.15)(a)**: `ex 𝒢_Θ(γ) = 𝒢_Θ(γ) ∩ ex 𝓟_Θ`; so a
  `Θ`-invariant Gibbs measure is extreme in `𝒢_Θ(γ)` iff it is ergodic
  (`mem_extremePoints_invariantG_iff_mem_trivialOn`,
  `mem_extremePoints_invariantG_iff_ergodicSMul`).
* `mem_invariantG_of_absolutelyContinuous` — **Theorem (14.15)(b)**: if `μ ∈ 𝒢_Θ(γ)` and
  `ν ∈ 𝓟_Θ` is absolutely continuous with respect to `μ`, then `ν ∈ 𝒢_Θ(γ)`.
* `isExtreme_invariantG` — **Theorem (14.15)(c)**: `𝒢_Θ(γ)` is a face of `𝓟_Θ`.
* `eq_of_forall_measurableSet_invariantEvents_eq_of_mem_invariantG`,
  `exists_measurableSet_invariantEvents_eq_one_eq_zero_of_mem_extremePoints_invariantG` — the
  remark after (14.15): Theorem (14.5)(c), (d) hold with `𝒢_Θ(γ)` in place of `𝓟_Θ`.

## The hypothesis on `Θ`

Georgii's proof of (14.9) chooses, for each finite volume `Λ`, a shift `θ_i` with
`Λ ∩ (Λ + i) = ∅`, and he remarks that the proposition therefore holds for any *infinite* subgroup
of the shift group. What the proof consumes is exactly that `Θ` **moves every finite volume off
itself**:

`∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' Λ) Λ`.

This is the hypothesis `hΘ` carried by every statement below that depends on (14.9). An infinite
subgroup of the *full* transformation group need not satisfy it (a group of spin flips fixes every
site), so this is the honest hypothesis, not "`Θ` infinite". The shift group of an infinite
additive site group satisfies it (`shiftGroup_exists_disjoint_sites_preimage`), and so does any
subgroup containing a shift `θ_j` of infinite order (`exists_disjoint_sites_preimage_of_shift_mem`)
— Georgii's remark after (14.15) that (14.15) holds for "any countable subgroup of `T` which
contains a (non-trivial) shift".

## Generality

Georgii states (14.15) for a *shift-invariant* specification `γ`. No invariance of `γ` is used:
(a)–(c) are consequences of (14.9), Theorem (14.5) and Theorem (7.7)(b), none of which involves
`τ(γ)`. Invariance of `γ` is what makes `𝒢_Θ(γ)` non-empty (Georgii §5.2), not what makes it a
face. `Countable S` is needed for the tail σ-algebra to be reached along a cofinal sequence of
volumes, and `Countable Θ` for Remark (14.3)(2), exactly as in `Ergodicity.lean`.

The measure-theoretic engine of (14.9) is
`MeasureTheory.exists_measurableSet_iInf_measure_symmDiff_eq_zero`, a Borel–Cantelli statement for
an *infimum* of σ-algebras which generalises
`MeasureTheory.exists_measurableSet_measure_symmDiff_eq_zero`: approximants that are eventually
measurable for each `M i` have a `limsup` measurable for `⨅ i, M i`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Set
open scoped ENNReal symmDiff

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Approximation by local events -/

/-- Every event is approximated in measure by local events (Georgii, proof of (14.9): "a
well-known corollary to Carathéodory's extension theorem"). This is Mathlib's
`exists_measure_symmDiff_lt_of_generateFrom_isSetRing` for the set ring `measurableCylinders`. -/
lemma exists_mem_localEvents_measure_symmDiff_lt (μ : Measure (S → E)) [IsFiniteMeasure μ]
    {A : Set (S → E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ B ∈ localEvents S E, μ (A ∆ B) < ε := by
  obtain ⟨B, hB, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
    isSetRing_measurableCylinders
    ⟨{Set.univ}, Set.countable_singleton _,
      Set.singleton_subset_iff.2 (univ_mem_measurableCylinders (fun _ : S ↦ E)), by simp⟩
    generateFrom_measurableCylinders.symm hA hε
  exact ⟨B, hB, by rwa [symmDiff_comm]⟩

/-! ### Georgii, Proposition (14.9): `𝓘 ⊆ 𝓣` almost surely -/

section Prop149

variable {Θ : Subgroup (Transformation S E)}

/-- Moving an approximant by a transformation of `Θ` does not change how well it approximates an
invariant event: for `A ∈ 𝓘`, `μ ∈ 𝓟_Θ` and `τ ∈ Θ`,
`μ (A ∆ θ_τ B) = μ (θ_τ A ∆ θ_τ B) = μ (A ∆ B)` (Georgii, proof of (14.9)). -/
lemma measure_symmDiff_preimage_eq {μ : Measure (S → E)} (hμ : μ ∈ invariantFields Θ)
    {A : Set (S → E)} (hA : MeasurableSet[invariantEvents Θ] A) {τ : Transformation S E}
    (hτ : τ ∈ Θ) {B : Set (S → E)} (hB : MeasurableSet B) :
    μ (A ∆ (τ.toFun ⁻¹' B)) = μ (A ∆ B) := by
  obtain ⟨hAm, hAinv⟩ := measurableSet_invariantEvents.1 hA
  have hmp : MeasurePreserving τ.toFun μ μ := (mem_invariantFields_iff.1 hμ).2 τ hτ
  rw [← hAinv τ hτ, ← preimage_symmDiff, hmp.measure_preimage (hAm.symmDiff hB).nullMeasurableSet,
    hAinv τ hτ]

/-- **Georgii, Proposition (14.9).** Let `Θ` move every finite volume off itself and let
`μ ∈ 𝓟_Θ`. Then `𝓘 ⊆ 𝓣` `μ`-almost surely: every invariant event `A ∈ 𝓘` agrees up to a
`μ`-null set with a tail event `B ∈ 𝓣`.

Proof (Georgii): approximate `A` by local events `Bₙ ∈ 𝓕_{Λₙ}` with `μ (A ∆ Bₙ) < 2⁻ⁿ`, along a
cofinal sequence of volumes `Λₙ`; move each `Bₙ` by a `τₙ ∈ Θ` with `τₙ⁻¹ Λₙ ∩ Λₙ = ∅`, so that
`B̃ₙ = θ_{τₙ} Bₙ ∈ 𝓕_{Λₙᶜ}` while still `μ (A ∆ B̃ₙ) < 2⁻ⁿ`; then `B = limsup B̃ₙ ∈ 𝓣` and
`μ (A ∆ B) = 0` by Borel–Cantelli. -/
theorem exists_measurableSet_tail_measure_symmDiff_eq_zero [Countable S] {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ)
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {A : Set (S → E)} (hA : MeasurableSet[invariantEvents Θ] A) :
    ∃ B, MeasurableSet[tailSigmaAlgebra S E] B ∧ μ (A ∆ B) = 0 := by
  classical
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hAm : MeasurableSet A := (measurableSet_invariantEvents.1 hA).1
  -- local approximants `Bₙ ∈ 𝓕_{Λₙ}` with `μ (A ∆ Bₙ) < 2⁻ⁿ`
  have happrox : ∀ n : ℕ, ∃ B : Set (S → E),
      (∃ Λ : Finset S, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] B) ∧
        μ (A ∆ B) < (2⁻¹ : ℝ≥0∞) ^ n := fun n ↦ by
    obtain ⟨B, hB, hAB⟩ := exists_mem_localEvents_measure_symmDiff_lt μ hAm
      (ε := (2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
    exact ⟨B, mem_localEvents_iff_cylinderEvents.1 hB, hAB⟩
  choose B hBΛ hAB using happrox
  choose Λ hBΛ using hBΛ
  -- enlarge the volumes so that they exhaust `S`
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ℕ → Finset S, ∀ n, Δ n = Λ n ∪ exhaustionVolumes n := ⟨_, fun _ ↦ rfl⟩
  have hBΔ : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ n : Set S)] (B n) :=
    fun n ↦ cylinderEvents_mono (by rw [hΔ n]; exact Finset.coe_subset.2 Finset.subset_union_left)
      _ (hBΛ n)
  -- move each approximant off its own volume
  choose τ hτΘ hτdisj using fun n ↦ hΘ (Δ n)
  set C : ℕ → Set (S → E) := fun n ↦ (τ n).toFun ⁻¹' B n with hC
  have hCΔ : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ n : Set S)ᶜ)] (C n) :=
    fun n ↦ cylinderEvents_mono (hτdisj n).subset_compl_right _
      ((τ n).measurable_toFun_cylinderEvents _ (hBΔ n))
  have hAC : ∀ n, μ (A ∆ C n) < (2⁻¹ : ℝ≥0∞) ^ n := fun n ↦ by
    rw [hC, measure_symmDiff_preimage_eq hμ hA (hτΘ n) (cylinderEvents_le_pi _ (hBΛ n))]
    exact hAB n
  -- Borel–Cantelli along the tail
  refine exists_measurableSet_iInf_measure_symmDiff_eq_zero (t := C) (fun Λ' ↦ ?_) ?_
  · obtain ⟨N, hN⟩ := exhaustionVolumes_cofinal Λ'
    refine eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
    have hsub : (Λ' : Set S) ⊆ (Δ n : Set S) := by
      rw [Finset.coe_subset, hΔ n]
      exact (hN.trans (exhaustionVolumes_monotone hn)).trans Finset.subset_union_right
    exact cylinderEvents_mono (compl_subset_compl.2 hsub) _ (hCΔ n)
  · refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n ↦ (hAC n).le)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top

/-- **Georgii (14.9), second assertion.** If `Θ` moves every finite volume off itself, a
`Θ`-invariant random field that is trivial on the tail σ-algebra is trivial on the invariant
σ-algebra `𝓘`. -/
theorem mem_trivialOn_invariantEvents_of_mem_trivialOn_tail [Countable S] {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ)
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    (htail : μ ∈ trivialOn (tailSigmaAlgebra S E)) : μ ∈ trivialOn (invariantEvents Θ) := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := exists_measurableSet_tail_measure_symmDiff_eq_zero hμ hΘ hA
  rw [measure_congr (measure_symmDiff_eq_zero_iff.1 hAB)]
  exact htail B hB

/-- **Georgii (14.9), second assertion**, in the language of Definition (14.6): a tail-trivial
`Θ`-invariant random field is ergodic. -/
theorem ergodicSMul_of_mem_trivialOn_tail [Countable S] [Countable Θ] {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ)
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    (htail : μ ∈ trivialOn (tailSigmaAlgebra S E)) : ErgodicSMul Θ (S → E) μ := by
  have := hμ.1
  exact (ergodicSMul_iff_mem_trivialOn_invariantEvents hμ.2).2
    (mem_trivialOn_invariantEvents_of_mem_trivialOn_tail hμ hΘ htail)

end Prop149

/-! ### Groups that move every finite volume off itself -/

section MovesVolumes

variable [AddGroup S]

/-- For `j ∉ -Λ + Λ`, the shift `θ_j` moves the finite volume `Λ` off itself:
`θ_j⁻¹ Λ ∩ Λ = ∅`. -/
lemma disjoint_shift_sites_preimage_of_notMem [DecidableEq S] (Λ : Finset S) {j : S}
    (hj : j ∉ (Λ ×ˢ Λ).image fun p : S × S ↦ -p.1 + p.2) :
    Disjoint ((shift E j).sites ⁻¹' (Λ : Set S)) (Λ : Set S) := by
  refine Set.disjoint_left.2 fun i hi hi' ↦ hj ?_
  have hij : i + j ∈ Λ := by simpa [shift] using hi
  exact Finset.mem_image.2 ⟨(i, i + j), Finset.mem_product.2 ⟨hi', hij⟩, neg_add_cancel_left i j⟩

/-- The shift group of an **infinite** additive group of sites moves every finite volume off
itself: for `Λ` finite there is `j` with `Λ ∩ (Λ + j) = ∅` — any `j ∉ -Λ + Λ`. This is the
choice of `i(n)` in Georgii's proof of (14.9), and the form in which "`Θ` is infinite" enters.
Commutativity of the site group is not needed. -/
lemma shiftGroup_exists_disjoint_sites_preimage [Infinite S] (Λ : Finset S) :
    ∃ τ ∈ shiftGroup S E, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S) := by
  classical
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset ((Λ ×ˢ Λ).image fun p : S × S ↦ -p.1 + p.2)
  exact ⟨shift E j, shift_mem_shiftGroup j, disjoint_shift_sites_preimage_of_notMem Λ hj⟩

/-- **Georgii (14.9) for the shift group** of an infinite countable site group: every
shift-invariant event agrees almost surely, under any shift-invariant random field, with a tail
event. -/
theorem exists_measurableSet_tail_measure_symmDiff_eq_zero_shiftGroup [Countable S] [Infinite S]
    {μ : Measure (S → E)} (hμ : μ ∈ invariantFields (shiftGroup S E)) {A : Set (S → E)}
    (hA : MeasurableSet[invariantEvents (shiftGroup S E)] A) :
    ∃ B, MeasurableSet[tailSigmaAlgebra S E] B ∧ μ (A ∆ B) = 0 :=
  exists_measurableSet_tail_measure_symmDiff_eq_zero hμ
    (shiftGroup_exists_disjoint_sites_preimage (E := E)) hA

end MovesVolumes

section ShiftOfInfiniteOrder

variable [AddCommGroup S]

variable (E) in
/-- `j ↦ θ_j` is a group homomorphism from the (multiplicatively written) site group into the
transformation group: `θ_i ∘ θ_j = θ_{i + j}` (Georgii (5.2)(1)). -/
def shiftHom : Multiplicative S →* Transformation S E where
  toFun x := shift E x.toAdd
  map_one' := Transformation.ext (Equiv.ext fun k ↦ by simp [shift, Transformation.id]) rfl
  map_mul' x y := Transformation.ext
    (Equiv.ext fun k ↦ by simp [shift, Transformation.comp, add_comm, add_left_comm]) rfl

@[simp] lemma shiftHom_ofAdd (j : S) : shiftHom E (Multiplicative.ofAdd j) = shift E j := rfl

/-- `θ_{k • j} = θ_j ^ k`: the shifts along the multiples of `j` are the powers of `θ_j`. -/
lemma shift_zsmul (j : S) (k : ℤ) : shift E (k • j) = shift E j ^ k := by
  rw [← shiftHom_ofAdd, ofAdd_zsmul, map_zpow, shiftHom_ofAdd]

/-- **Georgii, remark after (14.15).** A subgroup `Θ` of the transformation group containing a
shift `θ_j` of infinite order (on `ℤ^d`: any non-trivial shift) moves every finite volume off
itself: some power `θ_{k • j} ∈ Θ` has `Λ ∩ (Λ + k • j) = ∅`. Hence (14.9) and (14.15) hold for
"any countable subgroup of `T` which contains a (non-trivial) shift". -/
lemma exists_disjoint_sites_preimage_of_shift_mem {Θ : Subgroup (Transformation S E)} {j : S}
    (hj : ¬ IsOfFinAddOrder j) (hjΘ : shift E j ∈ Θ) (Λ : Finset S) :
    ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S) := by
  classical
  have hinj : Function.Injective fun k : ℤ ↦ k • j :=
    injective_zsmul_iff_not_isOfFinAddOrder.2 hj
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finset
    ((Λ ×ˢ Λ).image fun p : S × S ↦ -p.1 + p.2)
  exact ⟨shift E (k • j), by rw [shift_zsmul]; exact zpow_mem hjΘ k,
    disjoint_shift_sites_preimage_of_notMem Λ hk⟩

end ShiftOfInfiniteOrder

/-! ### Georgii (14.14): the `Θ`-invariant Gibbs measures -/

variable (γ : Specification S E) (Θ : Subgroup (Transformation S E))

/-- **Georgii (14.14).** The set `𝒢_Θ(γ) = 𝒢(γ) ∩ 𝓟_Θ` of `Θ`-invariant Gibbs measures for `γ`. -/
abbrev invariantG : Set (Measure (S → E)) := G γ ∩ invariantFields Θ

variable {γ Θ}

lemma mem_invariantG {μ : Measure (S → E)} :
    μ ∈ invariantG γ Θ ↔
      IsProbabilityMeasure μ ∧ γ.IsGibbsMeasure μ ∧ SMulInvariantMeasure Θ (S → E) μ :=
  ⟨fun h ↦ ⟨h.1.1, h.1.2, h.2.2⟩, fun h ↦ ⟨⟨h.1, h.2.1⟩, h.1, h.2.2⟩⟩

lemma invariantG_subset_invariantFields : invariantG γ Θ ⊆ invariantFields Θ :=
  inter_subset_right

lemma invariantG_subset_G : invariantG γ Θ ⊆ G γ := inter_subset_left

/-! ### Georgii (14.15): the structure of `𝒢_Θ(γ)` -/

section Thm1415

variable [Countable S] [Countable Θ]

/-- **The remark before (14.15).** For `μ ∈ 𝒢_Θ(γ)`, the `μ`-almost surely `Θ`-invariant σ-algebra
`𝓘(μ)` is contained in the `μ`-almost surely `γ_Λ`-invariant σ-algebra of every volume `Λ`:
a measurable `A` with `θ_τ⁻¹ A = A` `μ`-a.s. for all `τ ∈ Θ` satisfies `γ_Λ(A | ·) = 1_A`
`μ`-a.s. Indeed `A` agrees a.s. with a strictly invariant event (Remark (14.3)(2)), which agrees
a.s. with a tail event `B` (Proposition (14.9)), and `γ_Λ(B | ·) = 1_B` everywhere by
properness. -/
lemma mem_aeInvariantSets_kerAmbient_of_forall_preimage_smul_ae_eq {μ : Measure (S → E)}
    (hμ : μ ∈ invariantG γ Θ)
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {A : Set (S → E)} (hA : MeasurableSet A) (hae : ∀ τ : Θ, (τ • ·) ⁻¹' A =ᵐ[μ] A)
    (Λ : Finset S) : A ∈ aeInvariantSets (γ.toAbstract.kerAmbient Λ) μ := by
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  obtain ⟨A', hA', hAA'⟩ := exists_measurableSet_invariants_ae_eq hA hae
  obtain ⟨B, hB, hA'B⟩ := exists_measurableSet_tail_measure_symmDiff_eq_zero hμ.2 hΘ hA'
  have hBΛ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B :=
    measurableSet_cylinderEvents_compl_of_measurableSet_tail Λ hB
  have hBm : MeasurableSet B := cylinderEvents_le_pi _ hBΛ
  have hAB : A =ᵐ[μ] B :=
    (measure_symmDiff_eq_zero_iff.1 hAA').trans (measure_symmDiff_eq_zero_iff.1 hA'B)
  -- `γ_Λ(B | ω) = 1_B ω` for every `ω`, by properness
  have hker : ∀ ω, γ Λ ω B = B.indicator 1 ω := fun ω ↦ by
    rw [(γ.isProper Λ).apply_eq_indicator_mul_univ cylinderEvents_le_pi hBΛ ω, measure_univ,
      mul_one]
  -- `γ_Λ(A ∆ B | ω) = 0` for `μ`-a.e. `ω`, since `μ γ_Λ = μ` and `μ (A ∆ B) = 0`
  have hbind : μ.bind (γ Λ) = μ :=
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 hμ.1.2 Λ
  have hnull : ∀ᵐ ω ∂μ, γ Λ ω (A ∆ B) = 0 := by
    have hmeas : Measurable fun ω ↦ γ Λ ω (A ∆ B) :=
      ((γ Λ).measurable_coe (hA.symmDiff hBm)).mono cylinderEvents_le_pi le_rfl
    refine (lintegral_eq_zero_iff hmeas).1 ?_
    rw [← Measure.bind_apply (hA.symmDiff hBm)
      ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable, hbind]
    exact measure_symmDiff_eq_zero_iff.2 hAB
  refine ⟨hA, ?_⟩
  filter_upwards [hnull, Filter.eventuallyEq_set.1 hAB] with ω hω hωAB
  change γ Λ ω A = A.indicator 1 ω
  rw [measure_congr (measure_symmDiff_eq_zero_iff.1 hω), hker ω]
  by_cases h : ω ∈ A
  · simp [h, hωAB.1 h]
  · simp [h, mt hωAB.2 h]

/-- **Georgii, Theorem (14.15)(b).** If `μ ∈ 𝒢_Θ(γ)` and `ν ∈ 𝓟_Θ` is absolutely continuous
with respect to `μ`, then `ν ∈ 𝒢_Θ(γ)`.

Proof: by (14.5)(b) the density `f = dν/dμ` is measurable for `𝓘(μ)`; by the remark before
(14.15) it is then measurable for the a.s. `γ_Λ`-invariant σ-algebra of every `Λ`, and by (7.3)
`ν = f·μ` is `γ_Λ`-invariant. No invariance of `γ` under `Θ` is needed. -/
theorem mem_invariantG_of_absolutelyContinuous
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ ν : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) (hν : ν ∈ invariantFields Θ)
    (hνμ : ν ≪ μ) : ν ∈ invariantG γ Θ := by
  have hμp : IsProbabilityMeasure μ := hμ.1.1
  have hνp : IsProbabilityMeasure ν := hν.1
  refine ⟨⟨hνp, ?_⟩, hν⟩
  set f := ν.rnDeriv μ with hfdef
  have hfm : Measurable f := ν.measurable_rnDeriv μ
  have hwd : μ.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
  have hfin : ∫⁻ ω, f ω ∂μ ≠ ∞ := by
    rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ, hwd]
    exact measure_ne_top _ _
  have hinvμ : ∀ τ : Θ, Invariant (smulKernel Θ τ) μ :=
    smulInvariantMeasure_iff_forall_invariant.1 hμ.2.2
  have hinvν : ∀ τ : Θ, Invariant (smulKernel Θ τ) ν :=
    smulInvariantMeasure_iff_forall_invariant.1 hν.2
  -- (14.5)(b): `f` is `𝓘(μ)`-measurable
  have hfΘ : Measurable[aeInvariantSigmaAlgebraFamily (smulKernel Θ) hinvμ] f :=
    (measurable_aeInvariantSigmaAlgebraFamily_iff hinvμ).2 fun τ ↦
      measurable_of_invariant_withDensity (hinvμ τ) hfm hfin (hwd ▸ hinvν τ)
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have hbind : Invariant (γ.toAbstract.kerAmbient Λ) μ :=
    (γ.toAbstract.invariant_kerAmbient_iff Λ).2
      ((Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 hμ.1.2 Λ)
  -- the remark before (14.15): `f` is measurable for the a.s. `γ_Λ`-invariant σ-algebra
  have hfΛ : Measurable[aeInvariantSigmaAlgebra hbind] f := fun U hU ↦ by
    obtain ⟨hpm, hae⟩ := (measurableSet_aeInvariantSigmaAlgebraFamily_smul hinvμ).1 (hfΘ hU)
    exact mem_aeInvariantSets_kerAmbient_of_forall_preimage_smul_ae_eq hμ hΘ hpm hae Λ
  -- (7.3): `f·μ = ν` is `γ_Λ`-invariant
  have h := invariant_withDensity_of_measurable hbind hfΛ
  rwa [hwd] at h

/-- **Georgii, Theorem (14.15)(c).** `𝒢_Θ(γ)` is a face of `𝓟_Θ`: if `μ, ν ∈ 𝓟_Θ` and a proper
convex combination of them lies in `𝒢_Θ(γ)`, then so do `μ` and `ν`. Immediate from (b), since
each endpoint is absolutely continuous with respect to the combination. -/
theorem isExtreme_invariantG
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S)) :
    IsExtreme ℝ≥0∞ (invariantFields Θ) (invariantG γ Θ) := by
  refine ⟨invariantG_subset_invariantFields, fun μ hμ ν hν ρ hρ hseg ↦ ?_⟩
  obtain ⟨a, b, ha, -, -, hsum⟩ := hseg
  have hμρ : μ ≪ ρ := fun s hs ↦ by
    have h := congrArg (fun m : Measure (S → E) ↦ m s) hsum
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [← h] at hs
    rcases mul_eq_zero.1 (add_eq_zero.1 hs).1 with h | h
    · exact absurd h ha.ne'
    · exact h
  exact mem_invariantG_of_absolutelyContinuous hΘ hρ hμ hμρ

/-- **Georgii, Theorem (14.15)(c)** as literally stated: if `μ, ν ∈ 𝓟_Θ` and `0 < s < 1` are such
that `s μ + (1 - s) ν ∈ 𝒢_Θ(γ)`, then `μ, ν ∈ 𝒢_Θ(γ)`. -/
theorem mem_invariantG_of_smul_add_smul_mem
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ ν : Measure (S → E)} (hμ : μ ∈ invariantFields Θ) (hν : ν ∈ invariantFields Θ)
    {s : ℝ≥0∞} (hs0 : 0 < s) (hs1 : s < 1) (h : s • μ + (1 - s) • ν ∈ invariantG γ Θ) :
    μ ∈ invariantG γ Θ ∧ ν ∈ invariantG γ Θ := by
  have hseg : s • μ + (1 - s) • ν ∈ openSegment ℝ≥0∞ μ ν :=
    ⟨s, 1 - s, hs0, tsub_pos_of_lt hs1, add_tsub_cancel_of_le hs1.le, rfl⟩
  exact ⟨(isExtreme_invariantG hΘ).left_mem_of_mem_openSegment hμ hν h hseg,
    (isExtreme_invariantG hΘ).right_mem_of_mem_openSegment hμ hν h hseg⟩

/-- **Georgii, Theorem (14.15)(a)**, displayed form: `ex 𝒢_Θ(γ) = 𝒢_Θ(γ) ∩ ex 𝓟_Θ`. -/
theorem extremePoints_invariantG
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S)) :
    (invariantG γ Θ).extremePoints ℝ≥0∞ =
      invariantG γ Θ ∩ (invariantFields Θ).extremePoints ℝ≥0∞ :=
  (isExtreme_invariantG (γ := γ) hΘ).extremePoints_eq

/-- **Georgii, Theorem (14.15)(a).** A `Θ`-invariant Gibbs measure is extreme in `𝒢_Θ(γ)` if and
only if it is trivial on the invariant σ-algebra `𝓘`. -/
theorem mem_extremePoints_invariantG_iff_mem_trivialOn
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) :
    μ ∈ (invariantG γ Θ).extremePoints ℝ≥0∞ ↔ μ ∈ trivialOn (invariantEvents Θ) := by
  rw [extremePoints_invariantG hΘ, mem_inter_iff, and_iff_right hμ,
    mem_extremePoints_invariantFields_iff_mem_trivialOn hμ.2]

/-- **Georgii, Theorem (14.15)(a)**, in the language of Definition (14.6): a `Θ`-invariant Gibbs
measure is extreme in `𝒢_Θ(γ)` if and only if it is ergodic. -/
theorem mem_extremePoints_invariantG_iff_ergodicSMul
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) :
    μ ∈ (invariantG γ Θ).extremePoints ℝ≥0∞ ↔ ErgodicSMul Θ (S → E) μ := by
  have := hμ.1.1
  rw [mem_extremePoints_invariantG_iff_mem_trivialOn hΘ hμ,
    ergodicSMul_iff_mem_trivialOn_invariantEvents hμ.2.2]

/-- Extreme points of `𝒢_Θ(γ)` are extreme in `𝓟_Θ` — one inclusion of (14.15)(a), and the
content of "`𝒢_Θ(γ)` is a face". -/
theorem extremePoints_invariantG_subset
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S)) :
    (invariantG γ Θ).extremePoints ℝ≥0∞ ⊆ (invariantFields Θ).extremePoints ℝ≥0∞ :=
  (isExtreme_invariantG (γ := γ) hΘ).extremePoints_subset_extremePoints

/-! #### The remark after (14.15): Theorem (14.5)(c), (d) with `𝒢_Θ(γ)` in place of `𝓟_Θ` -/

omit [Countable S] in
/-- **Georgii, remark after (14.15): Theorem (14.5)(c) for `𝒢_Θ(γ)`.** Each `μ ∈ 𝒢_Θ(γ)` is
uniquely determined within `𝒢_Θ(γ)` by its restriction to `𝓘`. (This needs neither (14.9) nor the
volume-moving hypothesis: `𝒢_Θ(γ) ⊆ 𝓟_Θ`.) -/
theorem eq_of_forall_measurableSet_invariantEvents_eq_of_mem_invariantG
    {μ ν : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) (hν : ν ∈ invariantG γ Θ)
    (h : ∀ A, MeasurableSet[invariantEvents Θ] A → μ A = ν A) : μ = ν :=
  eq_of_forall_measurableSet_invariantEvents_eq hμ.2 hν.2 h

/-- **Georgii, remark after (14.15): Theorem (14.5)(d) for `𝒢_Θ(γ)`.** Distinct extreme points
of `𝒢_Θ(γ)` are mutually singular *on `𝓘`*: some `A ∈ 𝓘` has `μ A = 1` and `ν A = 0`. -/
theorem exists_measurableSet_invariantEvents_eq_one_eq_zero_of_mem_extremePoints_invariantG
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ ν : Measure (S → E)} (hμ : μ ∈ (invariantG γ Θ).extremePoints ℝ≥0∞)
    (hν : ν ∈ (invariantG γ Θ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    ∃ A, MeasurableSet[invariantEvents Θ] A ∧ μ A = 1 ∧ ν A = 0 :=
  exists_measurableSet_invariantEvents_eq_one_eq_zero
    (extremePoints_invariantG_subset hΘ hμ) (extremePoints_invariantG_subset hΘ hν) hne

/-- **Georgii, remark after (14.15): Theorem (14.5)(d) for `𝒢_Θ(γ)`**, measure form: distinct
extreme `Θ`-invariant Gibbs measures are mutually singular. -/
theorem mutuallySingular_of_mem_extremePoints_invariantG
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {μ ν : Measure (S → E)} (hμ : μ ∈ (invariantG γ Θ).extremePoints ℝ≥0∞)
    (hν : ν ∈ (invariantG γ Θ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) : μ.MutuallySingular ν :=
  mutuallySingular_of_mem_extremePoints_invariantFields
    (extremePoints_invariantG_subset hΘ hμ) (extremePoints_invariantG_subset hΘ hν) hne

end Thm1415

/-! ### The shift group: Georgii's setting -/

section ShiftGroup

variable [AddGroup S] [Countable S] [Infinite S]

/-- **Georgii, Theorem (14.15)(a) for the shift group**: a shift-invariant Gibbs measure on an
infinite countable site group is extreme among the shift-invariant Gibbs measures iff it is
ergodic. -/
theorem mem_extremePoints_invariantG_shiftGroup_iff_ergodicSMul {μ : Measure (S → E)}
    (hμ : μ ∈ invariantG γ (shiftGroup S E)) :
    μ ∈ (invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞ ↔
      ErgodicSMul (shiftGroup S E) (S → E) μ :=
  mem_extremePoints_invariantG_iff_ergodicSMul
    (shiftGroup_exists_disjoint_sites_preimage (E := E)) hμ

/-- **Georgii, Theorem (14.15)(c) for the shift group**: the shift-invariant Gibbs measures form
a face of the shift-invariant random fields. -/
theorem isExtreme_invariantG_shiftGroup :
    IsExtreme ℝ≥0∞ (invariantFields (shiftGroup S E)) (invariantG γ (shiftGroup S E)) :=
  isExtreme_invariantG (shiftGroup_exists_disjoint_sites_preimage (E := E))

end ShiftGroup

end GibbsMeasure

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ExtremeCorollaries
public import GibbsMeasure.Specification.Singleton
public import GibbsMeasure.Potential.GibbsTransformation
public import GibbsMeasure.Potential.FiniteReference
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.Analysis.PSeries

/-!
# Georgii §9.1: symmetries inherited by all Gibbs measures

The general mechanism of Chapter 9 (absence of symmetry breaking), Propositions (9.1) and (9.3),
together with the specification-level infrastructure they need.

## Main results

* `MeasureTheory.GibbsMeasure.IsSymmetryDominated`: **Georgii (9.2)**, the hypothesis of (9.1):
  for a symmetry `τ` of `γ` and constants `a, b ≥ 0`, every cylinder event `A` admits a volume `Λ`
  with `a γ_Λ(τ⁻¹ A | ·) + b γ_Λ(τ A | ·) ≥ γ_Λ(A | ·)`.
* `MeasureTheory.GibbsMeasure.IsSymmetryDominated.map_eq_of_mem_extremePoints`: **Georgii (9.1)
  for extreme Gibbs measures**, over an arbitrary state space: the inequality passes from the
  cylinder events to the tail σ-algebra by approximation (Mathlib's
  `exists_measure_symmDiff_lt_of_generateFrom_isSetRing`), and Theorem (7.7)(d)
  (`exists_tail_eq_one_eq_zero_of_mem_extremePoints`) forbids `τ(μ) ≠ μ`.
* `MeasureTheory.GibbsMeasure.IsSymmetryDominated.measurePreserving`: **Georgii, Proposition
  (9.1)** in full. The standard Borel hypothesis on `E` enters *only* here, through the extreme
  decomposition (7.26)/(7.28) (`map_eq_self_iff_weightOf_map_eq_self`,
  `weightOf_extremePoints_compl`), which reduces the claim to the extreme case.
* `MeasureTheory.GibbsMeasure.Transformation.IsLocalizedVersion`: **Georgii (9.3)(i)**, the
  *localized versions* `τ̃` of `τ` (equal to `τ` on `Δ`, inverse equal to `τ⁻¹` on `Δ`, identity
  off `Λ`), with `Transformation.spinLocalize` (the localized version `(τ ω)_Λ ω_{S∖Λ}` of a pure
  spin transformation used in (9.11)).
* `MeasureTheory.GibbsMeasure.measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion`:
  **Georgii, Proposition (9.3)**, at his hypotheses — `E` standard Borel, `λ ∈ 𝓜(E, ℰ)` σ-finite,
  `Φ` `λ`-admissible, `τ` a `λ`-preserving symmetry of `Φ`, constants `0 ≤ c ≤ 1`, `C`, and for
  each `Δ` a `λ`-preserving localized version `τ̃` on some `Λ` with
  `c H_Λ ∘ τ̃ + (1 − c) H_Λ ∘ τ̃⁻¹ − H_Λ ≤ C` (read with `β H_Λ`). Georgii's extra requirement
  `Δ ⊆ Λ` is not used and not assumed. Variants for a finite a priori measure and an absolutely
  summable potential (`..._gibbsSpecificationOfFiniteReference_...`,
  `..._gibbsSpecificationOfAbsolutelySummable_...`).
* `Specification.lambdaSpecification_apply_le_of_isLocalizedVersion`: the kernel-level content of
  the proof of (9.3), for any `λ`-specification `ρ λ_·`: a pointwise bound
  `ρ_Λ ≤ a ρ_Λ ∘ τ̃⁻¹ + b ρ_Λ ∘ τ̃` on the unnormalized densities gives (9.2) for `γ_Λ`.
  Georgii's normalization step `Z_Λ ∘ τ̃ = Z_Λ` is not needed.
* `Specification.sigmaFiniteLambdaFun_map_toFun`, `Specification.lambdaSpecification_map`,
  `Potential.map_gibbsSpecificationOfSigmaFiniteAdmissible`,
  `Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible`: **Georgii (5.6)(a),(b),(c)
  and (5.9)(b) over a σ-finite a priori measure**, extending the probability-measure versions of
  `GibbsMeasure/Potential/GibbsTransformation.lean`.
* `MeasureTheory.GibbsMeasure.Transformation.IsPureSpin`: **Georgii (9.9)**, pure spin
  transformations `τ ω = (τ_i ω_i)_i`.
* `Specification.map_eval_absolutelyContinuous_of_mem_G`,
  `Specification.absolutelyContinuous_map_eval_of_mem_G`: **Georgii, Remark (1.28)(2)**, the
  single-site marginal `σ_i(μ)` of a Gibbs measure of `ρ λ_·` is equivalent to `λ` (used in
  Corollary (9.16)).

The one-dimensional applications (9.5), (9.11), (9.16) are in
`GibbsMeasure/Model/OneDimensionalSymmetry.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter
open scoped ENNReal NNReal symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

local notation3 "Ω" => (S → E)

/-! ### Georgii (9.2) -/

/-- **Georgii (9.2).** For the transformation `τ` and the constants `a, b ≥ 0`, every cylinder
event `A` admits a volume `Λ` with `a γ_Λ(τ⁻¹ A | ·) + b γ_Λ(τ A | ·) ≥ γ_Λ(A | ·)`. Here
`τ⁻¹ A = τ.toFun ⁻¹' A` and `τ A = τ.inv.toFun ⁻¹' A`. -/
def IsSymmetryDominated (γ : Specification S E) (τ : Transformation S E) (a b : ℝ≥0) : Prop :=
  ∀ A ∈ localEvents S E, ∃ Λ : Finset S, ∀ ω : Ω,
    γ Λ ω A ≤ a * γ Λ ω (τ.toFun ⁻¹' A) + b * γ Λ ω (τ.inv.toFun ⁻¹' A)

variable {γ : Specification S E} {τ : Transformation S E} {a b : ℝ≥0}

lemma measurableSet_of_mem_localEvents {A : Set Ω} (hA : A ∈ localEvents S E) :
    MeasurableSet A := by
  obtain ⟨Λ, hΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  exact cylinderEvents_le_pi _ hΛ

/-- The kernel measurability `ω ↦ γ_Λ(B | ω)`, for the product σ-algebra. -/
lemma measurable_apply_kernel (γ : Specification S E) (Λ : Finset S) {B : Set Ω}
    (hB : MeasurableSet B) : Measurable fun ω ↦ γ Λ ω B :=
  (Measure.measurable_coe hB).comp (γ.measurable_kernel_toMeasure Λ)

/-- Georgii, first display in the proof of (9.1): for `μ ∈ 𝒢(γ)` and a cylinder event `A`,
`a μ(τ⁻¹ A) + b μ(τ A) ≥ μ(A)`. -/
lemma IsSymmetryDominated.measure_le_of_mem_localEvents (h : IsSymmetryDominated γ τ a b)
    {μ : Measure Ω} (hμ : μ ∈ G γ) {A : Set Ω} (hA : A ∈ localEvents S E) :
    μ A ≤ a * μ (τ.toFun ⁻¹' A) + b * μ (τ.inv.toFun ⁻¹' A) := by
  obtain ⟨Λ, hΛ⟩ := h A hA
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hbind : μ.bind (γ Λ) = μ := (Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμ.2) Λ
  have hAm : MeasurableSet A := measurableSet_of_mem_localEvents hA
  have hκ := (γ.measurable_kernel_toMeasure Λ).aemeasurable (μ := μ)
  have key : ∀ B : Set Ω, MeasurableSet B → μ B = ∫⁻ ω, γ Λ ω B ∂μ := fun B hB ↦ by
    conv_lhs => rw [← hbind]
    exact Measure.bind_apply hB hκ
  rw [key A hAm, key _ (τ.measurable_toFun hAm), key _ (τ.inv.measurable_toFun hAm),
    ← lintegral_const_mul _ (measurable_apply_kernel γ Λ (τ.measurable_toFun hAm)),
    ← lintegral_const_mul _ (measurable_apply_kernel γ Λ (τ.inv.measurable_toFun hAm)),
    ← lintegral_add_left ((measurable_apply_kernel γ Λ (τ.measurable_toFun hAm)).const_mul _)]
  exact lintegral_mono fun ω ↦ hΛ ω

/-- Georgii, proof of (9.1), the monotone class step: the inequality
`a μ(τ⁻¹ A) + b μ(τ A) ≥ μ(A)` passes from the algebra of cylinder events to all of `𝓕`. -/
theorem IsSymmetryDominated.measure_le (h : IsSymmetryDominated γ τ a b)
    {μ : Measure Ω} (hμ : μ ∈ G γ) {A : Set Ω} (hA : MeasurableSet A) :
    μ A ≤ a * μ (τ.toFun ⁻¹' A) + b * μ (τ.inv.toFun ⁻¹' A) := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  set ν : Measure Ω := (a : ℝ≥0∞) • μ.map τ.toFun + (b : ℝ≥0∞) • μ.map τ.inv.toFun with hν
  have hνapply : ∀ B : Set Ω, MeasurableSet B →
      ν B = a * μ (τ.toFun ⁻¹' B) + b * μ (τ.inv.toFun ⁻¹' B) := fun B hB ↦ by
    simp only [hν, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Measure.map_apply τ.measurable_toFun hB, Measure.map_apply τ.inv.measurable_toFun hB]
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνapply _ MeasurableSet.univ]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _),
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)⟩
  have hloc : ∀ t ∈ localEvents S E, μ t ≤ ν t := fun t ht ↦ by
    rw [hνapply t (measurableSet_of_mem_localEvents ht)]
    exact h.measure_le_of_mem_localEvents hμ ht
  rw [← hνapply A hA]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  have hε2 : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) / 2 := by
    exact ENNReal.div_pos (by exact_mod_cast hε.ne') ENNReal.ofNat_ne_top
  obtain ⟨t, ht, htA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ + ν)
    isSetRing_measurableCylinders
    ⟨{univ}, countable_singleton _, by
      simpa [singleton_subset_iff] using univ_mem_measurableCylinders (fun _ : S ↦ E), by simp⟩
    (generateFrom_measurableCylinders (α := fun _ : S ↦ E)).symm hA hε2
  have hAt : A ⊆ t ∪ (t ∆ A) := fun x hx ↦ by
    by_cases hxt : x ∈ t
    · exact Or.inl hxt
    · exact Or.inr (by rw [Set.symmDiff_def]; exact Or.inr ⟨hx, hxt⟩)
  have htA' : t ⊆ A ∪ (t ∆ A) := fun x hx ↦ by
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr (by rw [Set.symmDiff_def]; exact Or.inl ⟨hx, hxA⟩)
  have h1 : μ (t ∆ A) ≤ (μ + ν) (t ∆ A) := by
    simp only [Measure.coe_add, Pi.add_apply]; exact le_self_add
  have h2 : ν (t ∆ A) ≤ (μ + ν) (t ∆ A) := by
    simp only [Measure.coe_add, Pi.add_apply]; exact le_add_self
  calc μ A ≤ μ t + μ (t ∆ A) := (measure_mono hAt).trans (measure_union_le _ _)
    _ ≤ ν t + ε / 2 := add_le_add (hloc t ht) (h1.trans htA.le)
    _ ≤ (ν A + ν (t ∆ A)) + ε / 2 := by
        gcongr; exact (measure_mono htA').trans (measure_union_le _ _)
    _ ≤ (ν A + ε / 2) + ε / 2 := by gcongr; exact h2.trans htA.le
    _ = ν A + ε := by rw [add_assoc, ENNReal.add_halves]

/-- **Georgii (9.1)** for an extreme Gibbs measure: this is the case in which the extreme
decomposition (7.26) is not needed, and no standard Borel hypothesis is used. If `τ` is a symmetry
of `γ` satisfying (9.2), then `τ` preserves each `μ ∈ ex 𝒢(γ)`. -/
theorem IsSymmetryDominated.map_eq_of_mem_extremePoints [Countable S]
    (hτ : Specification.IsInvariant τ γ) (h : IsSymmetryDominated γ τ a b) {μ : Measure Ω}
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) : μ.map τ.toFun = μ := by
  have hμG : μ ∈ G γ := extremePoints_subset hμ
  have hprob : IsProbabilityMeasure μ := hμG.1
  by_contra hne
  have hcomp : τ.toFun ∘ τ.inv.toFun = id := funext fun ω ↦ τ.toFun_inv_toFun ω
  have hne' : μ.map τ.inv.toFun ≠ μ := fun heq ↦ hne (by
    conv_lhs => rw [← heq]
    rw [Measure.map_map τ.measurable_toFun τ.inv.measurable_toFun, hcomp, Measure.map_id])
  obtain ⟨A₁, hA₁, hμA₁, hτA₁⟩ := exists_tail_eq_one_eq_zero_of_mem_extremePoints hμ
    (map_mem_extremePoints_G hτ hμ) (Ne.symm hne)
  obtain ⟨A₂, hA₂, hμA₂, hτA₂⟩ := exists_tail_eq_one_eq_zero_of_mem_extremePoints hμ
    (map_mem_extremePoints_G hτ.inv hμ) (Ne.symm hne')
  have hA₁m : MeasurableSet A₁ := measurableSet_of_measurableSet_tail hA₁
  have hA₂m : MeasurableSet A₂ := measurableSet_of_measurableSet_tail hA₂
  have hμA : μ (A₁ ∩ A₂) = 1 := by
    rw [← prob_compl_eq_zero_iff (hA₁m.inter hA₂m), Set.compl_inter]
    refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
    rw [(prob_compl_eq_zero_iff hA₁m).2 hμA₁, (prob_compl_eq_zero_iff hA₂m).2 hμA₂, add_zero]
  have hle := h.measure_le hμG (hA₁m.inter hA₂m)
  rw [hμA, ← Measure.map_apply τ.measurable_toFun (hA₁m.inter hA₂m),
    ← Measure.map_apply τ.inv.measurable_toFun (hA₁m.inter hA₂m)] at hle
  have h1 : μ.map τ.toFun (A₁ ∩ A₂) = 0 :=
    measure_mono_null Set.inter_subset_left hτA₁
  have h2 : μ.map τ.inv.toFun (A₁ ∩ A₂) = 0 :=
    measure_mono_null Set.inter_subset_right hτA₂
  rw [h1, h2, mul_zero, mul_zero, add_zero] at hle
  exact one_ne_zero (le_antisymm hle bot_le)

/-- **Georgii, Proposition (9.1).** Let `E` be standard Borel, `γ` a specification, `τ` a
symmetry of `γ` and `a, b ≥ 0` constants such that (9.2) holds: each cylinder event `A` admits a
volume `Λ` with `a γ_Λ(τ⁻¹ A | ·) + b γ_Λ(τ A | ·) ≥ γ_Λ(A | ·)`. Then `τ` preserves every
`μ ∈ 𝒢(γ)`.

The standard Borel hypothesis enters only through the extreme decomposition theorem (7.26), which
reduces the claim to extreme Gibbs measures
(`IsSymmetryDominated.map_eq_of_mem_extremePoints`, valid for any state space). -/
theorem IsSymmetryDominated.map_eq [Countable S] [StandardBorelSpace E]
    (hτ : Specification.IsInvariant τ γ) (h : IsSymmetryDominated γ τ a b) {μ : Measure Ω}
    (hμ : μ ∈ G γ) : μ.map τ.toFun = μ := by
  have hG : (G γ).Nonempty := ⟨μ, hμ⟩
  refine (map_eq_self_iff_weightOf_map_eq_self hG hτ hμ).2 ?_
  have hae : (fun ν : Measure Ω ↦ ν.map τ.toFun) =ᵐ[weightOf hG μ] id := by
    have h0 := weightOf_extremePoints_compl hG hμ
    rw [measure_eq_zero_iff_ae_notMem] at h0
    filter_upwards [h0] with ν hν
    exact h.map_eq_of_mem_extremePoints hτ (not_not.1 hν)
  rw [Measure.map_congr hae, Measure.map_id]

/-- **Georgii, Proposition (9.1)**, in the language of `MeasurePreserving`. -/
theorem IsSymmetryDominated.measurePreserving [Countable S] [StandardBorelSpace E]
    (hτ : Specification.IsInvariant τ γ) (h : IsSymmetryDominated γ τ a b) {μ : Measure Ω}
    (hμ : μ ∈ G γ) : MeasurePreserving τ.toFun μ μ :=
  ⟨τ.measurable_toFun, h.map_eq hτ hμ⟩

/-- **Georgii, Proposition (9.1)** for `GP γ`. -/
theorem IsSymmetryDominated.measurePreserving_of_mem_GP [Countable S] [StandardBorelSpace E]
    (hτ : Specification.IsInvariant τ γ) (h : IsSymmetryDominated γ τ a b)
    {μ : ProbabilityMeasure Ω} (hμ : μ ∈ GP γ) : MeasurePreserving τ.toFun μ μ :=
  h.measurePreserving hτ ⟨inferInstance, hμ⟩

/-! ### Georgii (9.3)(i): localized versions of a transformation -/

namespace Transformation

variable {τ' τ : Transformation S E} {Δ Λ : Finset S}

/-- **Georgii (9.3)(i).** `τ'` is a *localized version* of `τ` on `Δ` within `Λ`: `τ'` and `τ`
agree on `Δ`, so do their inverses, and `τ'` leaves the spins outside `Λ` alone,
`(τ' ω)_{S ∖ Λ} = ω_{S ∖ Λ}`. -/
structure IsLocalizedVersion (τ' τ : Transformation S E) (Δ Λ : Finset S) : Prop where
  /-- `(τ' ω)_Δ = (τ ω)_Δ`. -/
  toFun_eq_of_mem : ∀ (ω : Ω), ∀ i ∈ Δ, τ'.toFun ω i = τ.toFun ω i
  /-- `(τ'⁻¹ ω)_Δ = (τ⁻¹ ω)_Δ`. -/
  inv_toFun_eq_of_mem : ∀ (ω : Ω), ∀ i ∈ Δ, τ'.inv.toFun ω i = τ.inv.toFun ω i
  /-- `(τ' ω)_{S ∖ Λ} = ω_{S ∖ Λ}`. -/
  toFun_eq_of_notMem : ∀ (ω : Ω), ∀ i ∉ Λ, τ'.toFun ω i = ω i

namespace IsLocalizedVersion

variable (h : τ'.IsLocalizedVersion τ Δ Λ)
include h

/-- The inverse of a localized version is also the identity outside `Λ`. -/
lemma inv_toFun_eq_of_notMem (ω : Ω) {i : S} (hi : i ∉ Λ) : τ'.inv.toFun ω i = ω i := by
  have := h.toFun_eq_of_notMem (τ'.inv.toFun ω) i hi
  rw [τ'.toFun_inv_toFun] at this
  exact this.symm

/-- `τ'⁻¹ A = τ⁻¹ A` for `A ∈ 𝓕_Δ`. -/
lemma preimage_eq {A : Set Ω} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    τ'.toFun ⁻¹' A = τ.toFun ⁻¹' A :=
  Set.ext fun ω ↦ mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
    h.toFun_eq_of_mem ω i (Finset.mem_coe.1 hi)

/-- `τ' A = τ A` for `A ∈ 𝓕_Δ`. -/
lemma inv_preimage_eq {A : Set Ω}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    τ'.inv.toFun ⁻¹' A = τ.inv.toFun ⁻¹' A :=
  Set.ext fun ω ↦ mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
    h.inv_toFun_eq_of_mem ω i (Finset.mem_coe.1 hi)

/-- For a non-degenerate state space the spatial part of a localized version fixes the sites
outside `Λ`. -/
lemma sites_symm_eq [Nontrivial E] {i : S} (hi : i ∉ Λ) : τ'.sites.symm i = i := by
  classical
  by_contra hne
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  have h1 := h.toFun_eq_of_notMem (Function.update (fun _ ↦ x) (τ'.sites.symm i) y) i hi
  have h2 := h.toFun_eq_of_notMem (fun _ ↦ x) i hi
  simp only [Transformation.toFun, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    at h1 h2
  exact hxy ((τ'.spin i).injective (h2.trans h1.symm))

/-- For a non-degenerate state space the spins of a localized version are trivial outside
`Λ`. -/
lemma spin_eq [Nontrivial E] {i : S} (hi : i ∉ Λ) : τ'.spin i = MeasurableEquiv.refl E := by
  ext x
  have := h.toFun_eq_of_notMem (fun _ ↦ x) i hi
  simpa [Transformation.toFun] using this

/-- The spatial part of a localized version maps `Λ` onto `Λ` (non-degenerate `E`). -/
lemma map_sites_symm_eq [Nontrivial E] : Λ.map τ'.sites.symm.toEmbedding = Λ := by
  ext i
  rw [Finset.mem_map_equiv, Equiv.symm_symm]
  constructor
  · intro hs
    by_contra hi
    have := h.sites_symm_eq hi
    have h' : τ'.sites i = i := by
      conv_lhs => rw [← this]
      exact τ'.sites.apply_symm_apply i
    exact hi (h' ▸ hs)
  · intro hi
    by_contra hs
    have := h.sites_symm_eq hs
    rw [Equiv.symm_apply_apply] at this
    exact hs (this ▸ hi)

end IsLocalizedVersion

/-- The identity is a localized version of `τ` on `∅` within any `Λ`. -/
lemma isLocalizedVersion_id (τ : Transformation S E) (Λ : Finset S) :
    (Transformation.id : Transformation S E).IsLocalizedVersion τ ∅ Λ where
  toFun_eq_of_mem _ i hi := absurd hi (Finset.notMem_empty i)
  inv_toFun_eq_of_mem _ i hi := absurd hi (Finset.notMem_empty i)
  toFun_eq_of_notMem ω i _ := congrFun (Transformation.id_toFun ω) i

end Transformation

end MeasureTheory.GibbsMeasure

/-! ### Georgii (5.6)(a) and (5.5) for a σ-finite a priori measure -/

namespace Specification

open MeasureTheory.GibbsMeasure Transformation

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
  (τ : Transformation S E)

/-- **Georgii (5.6)(a)** for the σ-finite reference kernels of Notation (1.26):
`τ(λ_·)_Λ(· | ω) = λ_{τ_*⁻¹ Λ}(τ⁻¹ · | τ⁻¹ ω) = λ_Λ(· | ω)` when `τ` is `λ`-preserving. -/
lemma sigmaFiniteLambdaFun_map_toFun (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S)
    (ω : S → E) :
    (sigmaFiniteLambdaFun (S := S) (E := E) ν (Λ.map τ.sites.symm.toEmbedding)
      (τ.inv.toFun ω)).map τ.toFun = sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω := by
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map,
    Measure.map_map τ.measurable_toFun Measurable.juxt, τ.toFun_comp_juxt,
    ← Measure.map_map Measurable.juxt (τ.measurePreserving_spin_piCongrLeft hτ Λ).measurable,
    (τ.measurePreserving_spin_piCongrLeft hτ Λ).map_eq]

/-- **Georgii (5.5)** for `λ_·` over a σ-finite `λ`:
`λ_Λ(f ∘ τ⁻¹) = λ_{τ_*⁻¹ Λ}(f) ∘ τ⁻¹` when `τ` is `λ`-preserving. -/
lemma lintegral_sigmaFiniteLambdaFun_comp_inv (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (Λ : Finset S) (ω : S → E) (f : (S → E) → ℝ≥0∞) :
    ∫⁻ x, f (τ.inv.toFun x) ∂sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω =
      ∫⁻ x, f x ∂sigmaFiniteLambdaFun (S := S) (E := E) ν (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun ω) := by
  rw [← sigmaFiniteLambdaFun_map_toFun ν τ hτ Λ ω]
  have h := lintegral_map_equiv (μ := sigmaFiniteLambdaFun (S := S) (E := E) ν
    (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω)) (fun x ↦ f (τ.inv.toFun x))
    τ.toMeasurableEquiv
  rw [show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl] at h
  rw [h]
  simp only [τ.inv_toFun_toFun]

variable {ν τ}

/-- The reference kernel `λ_Λ(· | ω)` depends on `ω` only through `ω_{S ∖ Λ}`. -/
lemma sigmaFiniteLambdaFun_congr_of_eqOn_compl {Λ : Finset S} {ω₁ ω₂ : S → E}
    (h : ∀ i ∉ Λ, ω₁ i = ω₂ i) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω₁ =
      sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω₂ := by
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map]
  congr 1
  funext ζ i
  by_cases hi : i ∈ Λ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hi), juxt_apply_of_mem (Finset.mem_coe.2 hi)]
  · rw [juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi),
      juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi), h i hi]

/-- A `λ`-preserving localized version `τ'` (identity outside `Λ`) preserves the reference
kernel `λ_Λ(· | ω)`: this is Georgii's "the second equality follows from the hypotheses that
`τ̃` is `λ`-preserving and preserves all spins outside `Λ`" in the proof of (9.3). -/
lemma _root_.MeasureTheory.GibbsMeasure.Transformation.IsLocalizedVersion.map_sigmaFiniteLambdaFun
    {τ' : Transformation S E} {Δ Λ : Finset S} (h : τ'.IsLocalizedVersion τ Δ Λ)
    (hν : ∀ i, MeasurePreserving (τ'.spin i) ν ν) (ω : S → E) :
    (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω).map τ'.toFun =
      sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : τ'.toFun = id := funext fun ω ↦ funext fun i ↦ Subsingleton.elim _ _
    rw [this, Measure.map_id]
  · have h1 := sigmaFiniteLambdaFun_map_toFun ν τ' hν Λ ω
    rw [h.map_sites_symm_eq,
      sigmaFiniteLambdaFun_congr_of_eqOn_compl (fun i hi ↦ h.inv_toFun_eq_of_notMem ω hi)] at h1
    exact h1

lemma _root_.MeasureTheory.GibbsMeasure.Transformation.IsLocalizedVersion.map_inv_sigmaFiniteLambdaFun
    {τ' : Transformation S E} {Δ Λ : Finset S} (h : τ'.IsLocalizedVersion τ Δ Λ)
    (hν : ∀ i, MeasurePreserving (τ'.spin i) ν ν) (ω : S → E) :
    (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω).map τ'.inv.toFun =
      sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω := by
  conv_lhs => rw [← h.map_sigmaFiniteLambdaFun hν ω]
  rw [Measure.map_map τ'.inv.measurable_toFun τ'.measurable_toFun,
    show τ'.inv.toFun ∘ τ'.toFun = id from funext fun ω ↦ τ'.inv_toFun_toFun ω, Measure.map_id]

/-- Change of variables in a set integral along a measure-preserving bijection `f` with inverse
`g`: `∫_{f⁻¹ A} ρ dμ = ∫_A ρ ∘ g dμ`. -/
lemma setLIntegral_preimage_of_map_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → X} (hf : Measurable f) (hg : Measurable g) (hgf : ∀ x, g (f x) = x)
    (hμ : μ.map f = μ) {ρ : X → ℝ≥0∞} (hρ : Measurable ρ) {A : Set X} (hA : MeasurableSet A) :
    ∫⁻ x in f ⁻¹' A, ρ x ∂μ = ∫⁻ y in A, ρ (g y) ∂μ := by
  conv_rhs => rw [← hμ]
  rw [setLIntegral_map (f := fun y ↦ ρ (g y)) hA (hρ.comp hg) hf]
  simp only [hgf]

/-- **Georgii, proof of (9.3), kernel level.** For a `λ`-specification `γ = ρ λ_·`, a
`λ`-preserving localized version `τ'` (identity outside `Λ`) and the pointwise bound
`ρ_Λ ≤ a ρ_Λ ∘ τ'⁻¹ + b ρ_Λ ∘ τ'` on the *unnormalized* densities,
`γ_Λ(A | ·) ≤ a γ_Λ(τ'⁻¹ A | ·) + b γ_Λ(τ' A | ·)`. Georgii's normalization step
`Z_Λ ∘ τ̃ = Z_Λ` is not needed: both sides carry the same `Z_Λ(ω)⁻¹`. -/
theorem lambdaSpecification_apply_le_of_isLocalizedVersion [NeZero ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {τ' : Transformation S E} {Δ Λ : Finset S} (h : τ'.IsLocalizedVersion τ Δ Λ)
    (hν : ∀ i, MeasurePreserving (τ'.spin i) ν ν) {a b : ℝ≥0∞}
    (hle : ∀ ζ, ρ Λ ζ ≤ a * ρ Λ (τ'.inv.toFun ζ) + b * ρ Λ (τ'.toFun ζ)) (ω : S → E)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω A ≤
      a * lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω (τ'.toFun ⁻¹' A) +
        b * lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω (τ'.inv.toFun ⁻¹' A) := by
  simp only [lambdaSpecification_apply]
  rw [withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E) ν hρ hA,
    withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E) ν hρ
      (τ'.measurable_toFun hA),
    withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E) ν hρ
      (τ'.inv.measurable_toFun hA),
    setLIntegral_preimage_of_map_eq τ'.measurable_toFun τ'.inv.measurable_toFun
      τ'.inv_toFun_toFun (h.map_sigmaFiniteLambdaFun hν ω) (hρ.measurable Λ) hA,
    setLIntegral_preimage_of_map_eq τ'.inv.measurable_toFun τ'.measurable_toFun
      τ'.toFun_inv_toFun (h.map_inv_sigmaFiniteLambdaFun hν ω) (hρ.measurable Λ) hA,
    mul_left_comm a, mul_left_comm b, ← mul_add]
  gcongr
  rw [← lintegral_const_mul a (f := fun y ↦ ρ Λ (τ'.inv.toFun y))
      ((hρ.measurable Λ).comp τ'.inv.measurable_toFun),
    ← lintegral_const_mul b (f := fun y ↦ ρ Λ (τ'.toFun y))
      ((hρ.measurable Λ).comp τ'.measurable_toFun),
    ← lintegral_add_left (f := fun y ↦ a * ρ Λ (τ'.inv.toFun y))
      (((hρ.measurable Λ).comp τ'.inv.measurable_toFun).const_mul _)]
  exact lintegral_mono fun ζ ↦ hle ζ

end Specification

/-! ### Georgii (5.6)(b),(c) and (5.9)(b) for a σ-finite a priori measure -/

namespace Specification

open MeasureTheory.GibbsMeasure Transformation

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
  (τ : Transformation S E) (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
  (ρ : Finset S → (S → E) → ℝ≥0∞)
include hτ

/-- **Georgii (5.6)(c), the partition function**, over a σ-finite `λ`:
`Z^{τ(ρ)}_Λ = Z^ρ_{τ_*⁻¹ Λ} ∘ τ⁻¹`. -/
lemma sigmaFiniteLambdaZ_map (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun η) :=
  lintegral_sigmaFiniteLambdaFun_comp_inv ν τ hτ Λ η _

/-- **Georgii (5.6)(c), normalized densities**, over a σ-finite `λ`: `τ(ρ)/Z^{τ(ρ)} = τ(ρ/Z^ρ)`. -/
lemma sigmaFinitePremodifierNorm_map (Λ : Finset S) (η : S → E) :
    sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun η) := by
  simp only [sigmaFinitePremodifierNorm, sigmaFiniteLambdaZ_map ν τ hτ]

omit hτ in
/-- The image `τ(ρ)` of a premodifier under a transformation is a premodifier. -/
lemma IsPremodifier.map (hρ : IsPremodifier (S := S) (E := E) ρ) :
    IsPremodifier (S := S) (E := E)
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) where
  measurable Λ := (hρ.measurable _).comp τ.inv.measurable_toFun
  comm_of_subset Λ₁ Λ₂ ζ η hΛ hres := by
    refine hρ.comm_of_subset (Finset.map_subset_map.2 hΛ) fun s hs ↦ ?_
    have hs' : τ.sites s ∉ Λ₁ := by
      rwa [Finset.mem_map_equiv, Equiv.symm_symm] at hs
    simp only [Transformation.inv, Transformation.toFun, Equiv.symm_symm, hres _ hs']

/-- `λ`-admissibility is transported by (5.3) over a σ-finite `λ`. -/
lemma IsSigmaFiniteLambdaAdmissible.map
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := fun Λ η ↦ by
  rw [sigmaFiniteLambdaZ_map ν τ hτ]
  exact hZ _ _

/-- **Georgii (5.6)(b)** over a σ-finite `λ`: `τ(ρ λ_·) = τ(ρ) λ_·` for a `λ`-preserving `τ`. -/
theorem lambdaSpecification_map [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).map τ =
      lambdaSpecification (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) (hρ.map τ)
        (hZ.map ν τ hτ) := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  rw [map_apply, lambdaSpecification_apply, lambdaSpecification_apply,
    show (τ.toFun : (S → E) → (S → E)) = τ.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_withDensity,
    show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl,
    sigmaFiniteLambdaFun_map_toFun ν τ hτ]
  congr 1
  funext x
  exact (sigmaFinitePremodifierNorm_map ν τ hτ ρ Λ x).symm

end Specification

namespace Potential

open MeasureTheory.GibbsMeasure Transformation Specification

variable {S E : Type*} [MeasurableSpace E] (Φ : Potential S E) (β : ℝ) (τ : Transformation S E)

/-- The Boltzmann factors of `τ(Φ)` are the `τ`-image (5.3) of those of `Φ`. -/
lemma boltzmannFactor_map_eq :
    (Potential.map τ Φ).boltzmannFactor β =
      fun Λ η ↦ Φ.boltzmannFactor β (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) :=
  funext fun Λ ↦ funext fun η ↦ boltzmannFactor_map' τ Φ β Λ η

variable (ν : Measure E) [SigmaFinite ν] (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
include hτ

/-- `λ`-admissibility of `Φ` transports to `τ(Φ)` for a `λ`-preserving `τ`. -/
lemma isSigmaFiniteLambdaAdmissible_boltzmannFactor_map
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β)) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((Potential.map τ Φ).boltzmannFactor β) := by
  rw [boltzmannFactor_map_eq Φ β τ]
  exact hadm.map ν τ hτ

variable [Countable S] [IsPotential Φ] [IsSummable Φ] [NeZero ν]

/-- **Georgii (5.6)(c) at the specification level, over a σ-finite `λ`.** `τ(γ^Φ) = γ^{τ(Φ)}`
for a `λ`-preserving `τ` and a `λ`-admissible `Φ`; `τ(Φ)` is again `λ`-admissible
(`isSigmaFiniteLambdaAdmissible_boltzmannFactor_map`). -/
theorem map_gibbsSpecificationOfSigmaFiniteAdmissible
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (hadm' : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((Potential.map τ Φ).boltzmannFactor β)) :
    (gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm).map τ =
      gibbsSpecificationOfSigmaFiniteAdmissible (Potential.map τ Φ) ν β hadm' := by
  unfold gibbsSpecificationOfSigmaFiniteAdmissible
  rw [Specification.lambdaSpecification_map ν τ hτ]
  exact Specification.lambdaSpecification_congr ν (boltzmannFactor_map_eq Φ β τ).symm _ _ _ _

/-- **Georgii (5.9)(b) over a σ-finite `λ`.** If the `λ`-admissible `Φ` is `τ`-invariant and `τ`
is `λ`-preserving, then `γ^Φ` is `τ`-invariant. -/
theorem isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (h : Potential.map τ Φ = Φ) :
    Specification.IsInvariant τ (gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) := by
  unfold Specification.IsInvariant gibbsSpecificationOfSigmaFiniteAdmissible
  rw [Specification.lambdaSpecification_map ν τ hτ]
  refine Specification.lambdaSpecification_congr ν ?_ _ _ _ _
  rw [← boltzmannFactor_map_eq Φ β τ, h]

end Potential

/-! ### Georgii (9.3) -/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

local notation3 "Ω" => (S → E)

/-- Georgii, proof of (9.3): condition (ii) gives, by the weighted AM–GM inequality,
`h_Λ ≤ (1 - c) e^C h_Λ ∘ τ̃⁻¹ + c e^C h_Λ ∘ τ̃` for the Boltzmann factors `h_Λ = e^{-β H_Λ}`.
Georgii's (ii) is the case `β = 1`; in general it is read with `β H_Λ` in place of `H_Λ`. -/
lemma boltzmannFactor_le_of_hamiltonian_le {Φ : Potential S E} {β c C : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) {Λ : Finset S} {τ' : Transformation S E}
    (hH : ∀ ω, β * (c * Φ.hamiltonian Λ (τ'.toFun ω) + (1 - c) * Φ.hamiltonian Λ (τ'.inv.toFun ω)
      - Φ.hamiltonian Λ ω) ≤ C) (ζ : Ω) :
    Φ.boltzmannFactor β Λ ζ ≤
      ENNReal.ofReal ((1 - c) * Real.exp C) * Φ.boltzmannFactor β Λ (τ'.inv.toFun ζ) +
        ENNReal.ofReal (c * Real.exp C) * Φ.boltzmannFactor β Λ (τ'.toFun ζ) := by
  simp only [Potential.boltzmannFactor]
  set p₁ := Real.exp (-β * Φ.hamiltonian Λ (τ'.toFun ζ)) with hp₁
  set p₂ := Real.exp (-β * Φ.hamiltonian Λ (τ'.inv.toFun ζ)) with hp₂
  have hc1' : 0 ≤ 1 - c := sub_nonneg.2 hc1
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hc0 hc1' (Real.exp_pos _).le
    (Real.exp_pos _).le (show c + (1 - c) = 1 by ring) (p₁ := p₁) (p₂ := p₂)
  have hprod : p₁ ^ c * p₂ ^ (1 - c) =
      Real.exp (-β * Φ.hamiltonian Λ (τ'.toFun ζ) * c +
        -β * Φ.hamiltonian Λ (τ'.inv.toFun ζ) * (1 - c)) := by
    rw [hp₁, hp₂, Real.exp_add, ← Real.exp_mul, ← Real.exp_mul]
  have hexp : Real.exp (-β * Φ.hamiltonian Λ ζ) ≤ Real.exp C * (p₁ ^ c * p₂ ^ (1 - c)) := by
    rw [hprod, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := hH ζ
    linarith
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.exp (-β * Φ.hamiltonian Λ ζ)
      ≤ Real.exp C * (p₁ ^ c * p₂ ^ (1 - c)) := hexp
    _ ≤ Real.exp C * (c * p₁ + (1 - c) * p₂) := by gcongr
    _ = (1 - c) * Real.exp C * p₂ + c * Real.exp C * p₁ := by ring

/-- **Georgii, Proposition (9.3).** Let `E` be standard Borel, `λ` a σ-finite non-zero a priori
measure, `Φ` a `λ`-admissible potential and `τ` a `λ`-preserving symmetry of `Φ`. Suppose there
are constants `0 ≤ c ≤ 1` and `C` such that for each `Δ ∈ 𝒮` there are `Λ ∈ 𝒮` and a
`λ`-preserving localized version `τ̃` of `τ` on `Δ` within `Λ` (`IsLocalizedVersion`, Georgii's
(i)) with `c H_Λ ∘ τ̃ + (1 - c) H_Λ ∘ τ̃⁻¹ - H_Λ ≤ C` (Georgii's (ii), read with `β H_Λ` in
place of `H_Λ`). Then each `μ ∈ 𝒢(Φ)` is `τ`-invariant.

Georgii also asks `Δ ⊆ Λ`; this is not used in the proof and is not assumed. The standard Borel
hypothesis enters only through (9.1), i.e. through the extreme decomposition (7.26). -/
theorem measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion
    [Countable S] [StandardBorelSpace E] {Φ : Potential S E} [Potential.IsPotential Φ]
    [Potential.IsSummable Φ] (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β))
    {τ : Transformation S E} (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hτΦ : Potential.map τ Φ = Φ) {c C : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h : ∀ Δ : Finset S, ∃ (Λ : Finset S) (τ' : Transformation S E),
      (∀ i, MeasurePreserving (τ'.spin i) ν ν) ∧ τ'.IsLocalizedVersion τ Δ Λ ∧
      ∀ ω, β * (c * Φ.hamiltonian Λ (τ'.toFun ω) + (1 - c) * Φ.hamiltonian Λ (τ'.inv.toFun ω)
        - Φ.hamiltonian Λ ω) ≤ C)
    {μ : Measure Ω}
    (hμ : μ ∈ G (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm)) :
    MeasurePreserving τ.toFun μ μ := by
  refine IsSymmetryDominated.measurePreserving (a := ((1 - c) * Real.exp C).toNNReal)
    (b := (c * Real.exp C).toNNReal)
    (Potential.isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible Φ β τ ν hτν hadm hτΦ) ?_ hμ
  intro A hA
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  obtain ⟨Λ, τ', hτ'ν, hloc, hH⟩ := h Δ
  refine ⟨Λ, fun ω ↦ ?_⟩
  rw [← hloc.preimage_eq hΔ, ← hloc.inv_preimage_eq hΔ]
  exact Specification.lambdaSpecification_apply_le_of_isLocalizedVersion
    (Potential.isPremodifier_boltzmannFactor (Φ := Φ) β) hadm hloc hτ'ν
    (boltzmannFactor_le_of_hamiltonian_le hc0 hc1 hH) ω (cylinderEvents_le_pi _ hΔ)

omit [MeasurableSpace E] in
/-- The Hamiltonian of the empty volume vanishes. -/
lemma _root_.Potential.hamiltonian_empty {E : Type*} [MeasurableSpace E] (Φ : Potential S E)
    (η : S → E) : Φ.hamiltonian ∅ η = 0 := by
  unfold Potential.hamiltonian
  have : Φ.hamiltonianTerms ∅ η = 0 :=
    funext fun A ↦ Potential.hamiltonianTerms_of_disjoint (Finset.disjoint_empty_right A) η
  rw [this]
  exact tsum_zero

/-- **Georgii, Proposition (9.3)** for an absolutely summable potential and a finite a priori
measure (the setting of Theorem (9.5)). -/
theorem measurePreserving_gibbsSpecificationOfFiniteReference_of_isLocalizedVersion
    [Countable S] [StandardBorelSpace E] {Φ : Potential S E} [Potential.IsPotential Φ]
    [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    {τ : Transformation S E} (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hτΦ : Potential.map τ Φ = Φ) {c C : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h : ∀ Δ : Finset S, ∃ (Λ : Finset S) (τ' : Transformation S E),
      (∀ i, MeasurePreserving (τ'.spin i) ν ν) ∧ τ'.IsLocalizedVersion τ Δ Λ ∧
      ∀ ω, β * (c * Φ.hamiltonian Λ (τ'.toFun ω) + (1 - c) * Φ.hamiltonian Λ (τ'.inv.toFun ω)
        - Φ.hamiltonian Λ ω) ≤ C)
    {μ : Measure Ω} (hμ : μ ∈ G (Potential.gibbsSpecificationOfFiniteReference Φ ν β)) :
    MeasurePreserving τ.toFun μ μ :=
  measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion ν β
    (Potential.isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν β) hτν hτΦ hc0 hc1 h hμ

/-- **Georgii, Proposition (9.3)** for an absolutely summable potential and a probability a
priori measure, in terms of `Potential.gibbsSpecificationOfAbsolutelySummable`. -/
theorem measurePreserving_gibbsSpecificationOfAbsolutelySummable_of_isLocalizedVersion
    [Countable S] [StandardBorelSpace E] {Φ : Potential S E} [Potential.IsPotential Φ]
    [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    {τ : Transformation S E} (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hτΦ : Potential.map τ Φ = Φ) {c C : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h : ∀ Δ : Finset S, ∃ (Λ : Finset S) (τ' : Transformation S E),
      (∀ i, MeasurePreserving (τ'.spin i) ν ν) ∧ τ'.IsLocalizedVersion τ Δ Λ ∧
      ∀ ω, β * (c * Φ.hamiltonian Λ (τ'.toFun ω) + (1 - c) * Φ.hamiltonian Λ (τ'.inv.toFun ω)
        - Φ.hamiltonian Λ ω) ≤ C)
    {μ : Measure Ω}
    (hμ : μ ∈ G (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β)) :
    MeasurePreserving τ.toFun μ μ := by
  rw [← Potential.gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure] at hμ
  exact measurePreserving_gibbsSpecificationOfFiniteReference_of_isLocalizedVersion ν β hτν hτΦ
    hc0 hc1 h hμ

/-! ### Pure spin transformations, Georgii (9.9) -/

namespace Transformation

variable {τ : Transformation S E}

/-- **Georgii (9.9).** A transformation is a *pure spin transformation* if its spatial part is the
identity: `τ ω = (τ_i ω_i)_{i ∈ S}`. -/
def IsPureSpin (τ : Transformation S E) : Prop := τ.sites = Equiv.refl S

lemma IsPureSpin.toFun_apply (h : τ.IsPureSpin) (ω : Ω) (i : S) :
    τ.toFun ω i = τ.spin i (ω i) := by
  rw [Transformation.toFun, h]; rfl

lemma IsPureSpin.inv (h : τ.IsPureSpin) : τ.inv.IsPureSpin := by
  simp only [IsPureSpin, Transformation.inv] at h ⊢
  rw [h]; rfl

lemma IsPureSpin.inv_toFun_apply (h : τ.IsPureSpin) (ω : Ω) (i : S) :
    τ.inv.toFun ω i = (τ.spin i).symm (ω i) := by
  rw [h.inv.toFun_apply]
  simp only [Transformation.inv, IsPureSpin] at h ⊢
  rw [h]; rfl

/-- The iterates of a pure spin transformation act site-wise by the iterates of the spins. -/
lemma IsPureSpin.iterate_toFun_apply (h : τ.IsPureSpin) (k : ℕ) (ω : Ω) (i : S) :
    τ.toFun^[k] ω i = (τ.spin i)^[k] (ω i) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h.toFun_apply]

section SpinLocalize

variable [DecidableEq S]

/-- Georgii, proof of (9.11): the localized version `τ̃ ω = (τ ω)_Λ ω_{S ∖ Λ}` of a pure spin
transformation — the spins of `τ` inside `Λ`, the identity outside. -/
def spinLocalize (τ : Transformation S E) (Λ : Finset S) : Transformation S E where
  sites := Equiv.refl S
  spin i := if i ∈ Λ then τ.spin i else MeasurableEquiv.refl E

lemma isPureSpin_spinLocalize (τ : Transformation S E) (Λ : Finset S) :
    (τ.spinLocalize Λ).IsPureSpin := rfl

@[simp] lemma spinLocalize_toFun_apply (τ : Transformation S E) (Λ : Finset S) (ω : Ω) (i : S) :
    (τ.spinLocalize Λ).toFun ω i = if i ∈ Λ then τ.spin i (ω i) else ω i := by
  rw [(τ.isPureSpin_spinLocalize Λ).toFun_apply]
  simp only [spinLocalize]
  split_ifs <;> rfl

@[simp] lemma spinLocalize_inv_toFun_apply (τ : Transformation S E) (Λ : Finset S) (ω : Ω)
    (i : S) :
    (τ.spinLocalize Λ).inv.toFun ω i = if i ∈ Λ then (τ.spin i).symm (ω i) else ω i := by
  rw [(τ.isPureSpin_spinLocalize Λ).inv_toFun_apply]
  simp only [spinLocalize]
  split_ifs <;> rfl

/-- `τ̃ = (τ ω)_Λ ω_{S ∖ Λ}` is a localized version of the pure spin transformation `τ` on every
`Δ ⊆ Λ`. -/
lemma isLocalizedVersion_spinLocalize (h : τ.IsPureSpin) {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) :
    (τ.spinLocalize Λ).IsLocalizedVersion τ Δ Λ where
  toFun_eq_of_mem ω i hi := by rw [spinLocalize_toFun_apply, ite_eq_left (hΔ hi), h.toFun_apply]
  inv_toFun_eq_of_mem ω i hi := by
    rw [spinLocalize_inv_toFun_apply, ite_eq_left (hΔ hi), h.inv_toFun_apply]
  toFun_eq_of_notMem ω i hi := by rw [spinLocalize_toFun_apply, ite_eq_right hi]

/-- The spins of `τ̃` preserve `λ` when those of `τ` do. -/
lemma measurePreserving_spin_spinLocalize {ν : Measure E}
    (hν : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S) (i : S) :
    MeasurePreserving ((τ.spinLocalize Λ).spin i) ν ν := by
  simp only [spinLocalize]
  split_ifs
  · exact hν i
  · exact MeasurePreserving.id ν

end SpinLocalize

end Transformation

end MeasureTheory.GibbsMeasure

/-! ### Georgii, Remark (1.28)(2): single-site marginals of Gibbs measures -/

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

/-- `λ_{{i}}(σ_i ∈ B | ω) = λ(B)`: resampling the single site `i` from `λ`. -/
lemma sigmaFiniteLambdaFun_singleton_eval_preimage (i : S) (ω : S → E) {B : Set E}
    (hB : MeasurableSet B) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν {i} ω ((fun ω : S → E ↦ ω i) ⁻¹' B) = ν B := by
  rw [sigmaFiniteLambdaFun_apply_eq_map,
    Measure.map_apply Measurable.juxt (measurable_pi_apply i hB)]
  have hi : i ∈ ({i} : Finset S) := Finset.mem_singleton_self i
  have hset : juxt (({i} : Finset S) : Set S) ω ⁻¹' ((fun ω : S → E ↦ ω i) ⁻¹' B) =
      (MeasurableEquiv.piUnique fun _ : ({i} : Finset S) ↦ E) ⁻¹' B := by
    ext ζ
    simp only [Set.mem_preimage, juxt_apply_of_mem (Finset.mem_coe.2 hi),
      MeasurableEquiv.piUnique_apply]
    rfl
  have hmp := measurePreserving_piUnique fun _ : ({i} : Finset S) ↦ ν
  rw [hset, ← Measure.map_apply hmp.measurable hB, hmp.map_eq]

variable [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifier (S := S) (E := E) ρ)
  (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
include hρ hZ

/-- **Georgii, Remark (1.28)(2), first half.** For a Gibbs measure `μ` of a `λ`-specification
`ρ λ_·`, the single-site marginal `σ_i(μ)` is absolutely continuous with respect to `λ`. -/
theorem map_eval_absolutelyContinuous_of_mem_G {μ : Measure (S → E)}
    (hμ : μ ∈ G (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)) (i : S) :
    μ.map (fun ω ↦ ω i) ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hνB ↦ ?_
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hBm : MeasurableSet ((fun ω : S → E ↦ ω i) ⁻¹' B) := measurable_pi_apply i hB
  have hbind := (isGibbsMeasure_iff_forall_bind_eq.1 hμ.2) {i}
  rw [Measure.map_apply (measurable_pi_apply i) hB]
  conv_lhs => rw [← hbind]
  rw [Measure.bind_apply hBm
    ((lambdaSpecification ν ρ hρ hZ).measurable_kernel_toMeasure {i}).aemeasurable]
  refine (lintegral_eq_zero_iff (measurable_apply_kernel _ {i} hBm)).2
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [Pi.zero_apply, lambdaSpecification_apply]
  rw [withDensity_apply _ hBm, Measure.restrict_eq_zero.2 (by
    rw [sigmaFiniteLambdaFun_singleton_eval_preimage ν i ω hB]; exact hνB), lintegral_zero_measure]

/-- **Georgii, Remark (1.28)(2), second half.** If the densities `ρ_Λ` are strictly positive —
as the Boltzmann factors `e^{-β H_Λ}` of a `λ`-admissible potential are — then `λ` is absolutely
continuous with respect to the single-site marginal `σ_i(μ)` of every Gibbs measure `μ`; together
with the first half, `σ_i(μ)` and `λ` are equivalent. -/
theorem absolutelyContinuous_map_eval_of_mem_G (hρ0 : ∀ (Λ : Finset S) (η : S → E), ρ Λ η ≠ 0)
    {μ : Measure (S → E)} (hμ : μ ∈ G (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ))
    (i : S) : ν ≪ μ.map (fun ω ↦ ω i) := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hμB ↦ ?_
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hae : (ae μ).NeBot := IsProbabilityMeasure.ae_neBot
  have hBm : MeasurableSet ((fun ω : S → E ↦ ω i) ⁻¹' B) := measurable_pi_apply i hB
  have hbind := (isGibbsMeasure_iff_forall_bind_eq.1 hμ.2) {i}
  rw [Measure.map_apply (measurable_pi_apply i) hB] at hμB
  have hμB' : μ.bind ((lambdaSpecification ν ρ hρ hZ) {i}) ((fun ω : S → E ↦ ω i) ⁻¹' B) = 0 :=
    by rwa [hbind]
  rw [Measure.bind_apply hBm
    ((lambdaSpecification ν ρ hρ hZ).measurable_kernel_toMeasure {i}).aemeasurable,
    lintegral_eq_zero_iff (measurable_apply_kernel _ {i} hBm)] at hμB'
  obtain ⟨ω, hω⟩ := hμB'.exists
  simp only [Pi.zero_apply, lambdaSpecification_apply] at hω
  rw [withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E) ν hρ hBm, mul_eq_zero,
    ENNReal.inv_eq_zero] at hω
  rcases hω with hω | hω
  · exact absurd hω (hZ.ne_top _ _)
  · rw [lintegral_eq_zero_iff (hρ.measurable {i}), Filter.EventuallyEq, ae_iff] at hω
    have huniv : {x | ¬ ρ {i} x = (0 : (S → E) → ℝ≥0∞) x} = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ hρ0 _ x
    rw [huniv, Measure.restrict_apply_univ,
      sigmaFiniteLambdaFun_singleton_eval_preimage ν i ω hB] at hω
    exact hω

end Specification

end

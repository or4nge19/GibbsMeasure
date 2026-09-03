/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Subadditive.Cubes
public import GibbsMeasure.Mathlib.InformationTheory.RelativeEntropy
public import GibbsMeasure.Mathlib.Probability.ProductMeasure
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import GibbsMeasure.Specification.Ergodicity
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Specific entropy (Georgii §15.2)

Throughout, `(E, ℰ)` is an arbitrary measurable space, `S = ℤ^d` is spelled `ι → ℤ` for a finite
type `ι`, and `λ` is an a priori *probability* measure on `E` with product `λ^S = ⨂_{i ∈ S} λ`
(`Measure.infinitePi`). Georgii allows a finite `λ`, normalises it in every proof, and records that
the entropies then change by the constant `|Λ| log λ(E)`; we take `λ` to be a probability measure
from the start, so that `σ_Λ⁻¹(λ^Λ) = λ^S | 𝓕_Λ` and Georgii's `log λ(E)` is `0`.

## Main definitions

* `relativeEntropyIn Λ μ ν`, Georgii (15.8): the relative entropy `𝓗_Λ(μ | ν)` of `μ` with respect
  to `ν` on the cylinder σ-algebra `𝓕_Λ = cylinderEvents Λ`, i.e. Mathlib's `klDiv` of the trimmed
  measures (see `GibbsMeasure/Mathlib/InformationTheory/RelativeEntropy.lean`). It is defined for
  any set of sites `Λ`, finite or not.
* `entropyIn λ Λ μ = -𝓗_Λ(μ | λ^S)`, Georgii (15.9): the entropy of `μ` in `Λ` relative to `λ`, an
  extended real in `[-∞, 0]`.
* `specificEntropy λ μ`, Georgii (15.13): the specific entropy `𝓀(μ) = inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ 𝓗_Δ(μ)`
  over the rectangular boxes, in `EReal` (values in `[-∞, 0]`). By Theorem (15.12) it is the limit
  `lim |Λ_n|⁻¹ 𝓗_{Λ_n}(μ)` along cubes for shift-invariant `μ`.

## Main results

* `relativeEntropyIn_add_relativeEntropyIn_le`, **Georgii Proposition (15.10)**: for any
  probability measure `μ` and any sets of sites `Λ, Δ` (Georgii: finite),
  `𝓗_Λ(μ | λ^S) + 𝓗_Δ(μ | λ^S) ≤ 𝓗_{Λ ∩ Δ}(μ | λ^S) + 𝓗_{Λ ∪ Δ}(μ | λ^S)`; in Georgii's sign
  convention this is the strong subadditivity `𝓗_Λ(μ) + 𝓗_Δ(μ) ≥ 𝓗_{Λ ∩ Δ}(μ) + 𝓗_{Λ ∪ Δ}(μ)` of
  the entropy (`entropyIn_add_entropyIn_le`). Together with `relativeEntropyIn_mono` (Georgii
  (15.5)(c)), `relativeEntropyIn_empty` and the shift invariance `relativeEntropyIn_image_add`
  for shift-invariant `μ`, this is `boxSubadditive_entropyIn`: Georgii's hypotheses
  (15.11)(i)–(ii).
* `tendsto_entropyIn_div_card`, **Georgii Theorem (15.12)**: for shift-invariant `μ` and boxes
  `Λ_j` all of whose sides tend to infinity, `|Λ_j|⁻¹ 𝓗_{Λ_j}(μ) → 𝓀(μ)` in `EReal`;
  `tendsto_entropyIn_div_card_cube` is the statement for cubes with `|Λ_n| → ∞`.
* `specificEntropy_nonpos`: `𝓀(μ) ≤ 0 = log λ(E)`.
* **Georgii Proposition (15.14)**: `smul_specificEntropy_add_smul_specificEntropy_le` (concavity,
  for all finite measures, from the concavity `smul_entropyIn_add_smul_entropyIn_le` of `𝓗_Λ`,
  Georgii (15.5)(d)) and `specificEntropy_smul_add_smul_le` (convexity, for shift-invariant
  measures in dimension `d ≥ 1`, from the convexity defect `entropyIn_smul_add_smul_le` and the
  limit (15.12)), so `𝓀` is affine on `𝓟_Θ`; `upperSemicontinuous_specificEntropy`, upper
  semicontinuity for the topology of local convergence `WithLocalConvergence`, on all of
  `𝓟(Ω, 𝓕)` (from `lowerSemicontinuous_relativeEntropyIn`, Georgii's Corollary (15.7)).
  Convexity genuinely needs `d ≥ 1`: on `ℤ^0` the specific entropy is `-𝓗(μ | λ)`, which is
  strictly concave.

## Proof of (15.10)

Georgii's proof compares `μ` with the measure `ν = μ λ_{Δ ∖ Λ}` obtained by resampling the spins
in `Δ ∖ Λ` from `λ`. On `𝓕_{Λ ∪ Δ}` this measure is `f_Λ λ^S`, with `f_Λ` the density of `μ` on
`𝓕_Λ`, so we take `ν = λ^S.withDensity f_Λ` directly. Two general facts do the work:

* the chain rule `klDiv_eq_add_klDiv_trim_of_withDensity`: if `ν = g λ` with `g` measurable for a
  sub-σ-algebra `m` on which `μ = ν`, then `𝓗(μ | λ) = 𝓗(μ | ν) + 𝓗_m(μ | λ)`;
* the Markov property of independence `setLIntegral_eq_of_indep_sup`: if `m₂ ⊥ m₃` and `m₁ ≤ m₂`,
  an `m₂`-measurable density has the same integrals over the sets of `m₁ ⊔ m₃` as its
  `m₁`-conditional version. Applied to `𝓕_Λ ⊥ 𝓕_{Δ ∖ Λ}` under the product measure
  (`indep_cylinderEvents_compl_infinitePi`) and `𝓕_Δ = 𝓕_{Λ ∩ Δ} ⊔ 𝓕_{Δ ∖ Λ}`, it shows that
  `ν = f_{Λ ∩ Δ} λ^S` on `𝓕_Δ`.

Then `𝓗_{Λ ∪ Δ}(μ | λ^S) = 𝓗_{Λ ∪ Δ}(μ | ν) + 𝓗_Λ(μ | λ^S)`, `𝓗_Δ(μ | λ^S) = 𝓗_Δ(μ | ν) +
𝓗_{Λ ∩ Δ}(μ | λ^S)` and `𝓗_Δ(μ | ν) ≤ 𝓗_{Λ ∪ Δ}(μ | ν)` (Georgii (15.5)(c)). No finiteness of
`Λ`, `Δ` is used.

## General lemmas that belong in Mathlib

The first section has no Georgii content: `Real.continuous_mul_log_div`
(`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`), `EReal.continuous_div_natCast`
(`Mathlib/Topology/Instances/EReal/Lemmas.lean`), `cylinderEvents_union`, `cylinderEvents_empty`
and `cylinderEvents_comap_precomp` (`Mathlib/MeasureTheory/Constructions/Cylinders.lean`;
`Specification/MarkovInt.lean` has the first two for `S = ℤ` only), `Measure.trim_smul` and
`isProbabilityMeasure_trim` (`Mathlib/MeasureTheory/Measure/Trim.lean`),
`setLIntegral_eq_of_indep_sup` (`Mathlib/Probability/Independence/Integration.lean`),
`klDiv_trim_le_klDiv_trim_comap`, `klDiv_eq_add_klDiv_trim_of_withDensity` and
`smul_klDiv_add_smul_klDiv_le` (`Mathlib/InformationTheory/KullbackLeibler/`). In the Georgii
section, `measurePreserving_shift_infinitePi` (`λ^S` is shift invariant) and
`smul_add_smul_mem_invariantFields_shiftGroup` (`𝓟_Θ` is convex) belong in
`Prereqs/Transformation.lean` and `Specification/Ergodicity.lean`; `Model/PeriodicSymmetry.lean`
proves the general `Transformation.measurePreserving_infinitePi` in a leaf file, which this file
cannot import.

Not in this file: Proposition (15.16) (the specific entropy as a conditional entropy given the
lexicographic past, and `inf_{Δ ∈ 𝒮}` in place of `inf_{Δ ∈ 𝒮_□}`), formula (15.18)–(15.19),
Theorem (15.20) (the `𝓘 ∩ 𝓣`-measurable integrand `h` with `𝓀(μ) = μ(h)`, standard Borel `E`), and
the compactness of the level sets `{𝓀 ≥ c}` for standard Borel `E` (which needs Proposition (4.9)).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Topology
open InformationTheory Real
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Missing general lemmas -/

/-- `x ↦ x log (x / c)` is continuous on `ℝ` (with Mathlib's conventions `log 0 = 0`,
`x / 0 = 0`). -/
lemma Real.continuous_mul_log_div (c : ℝ) : Continuous fun x : ℝ ↦ x * log (x / c) := by
  by_cases hc : c = 0
  · simp only [hc, div_zero, Real.log_zero, mul_zero]
    exact continuous_const
  have : (fun x : ℝ ↦ x * log (x / c)) = fun x ↦ x * log x - x * log c := by
    funext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hc, mul_sub]
  rw [this]
  exact Real.continuous_mul_log.sub (continuous_id.mul continuous_const)

/-- Division by a positive natural number is continuous on `EReal`. -/
lemma EReal.continuous_div_natCast {n : ℕ} (hn : n ≠ 0) :
    Continuous fun x : EReal ↦ x / (n : EReal) := by
  have hinv : ((n : EReal))⁻¹ ≠ 0 := by
    rw [← EReal.coe_natCast, ← EReal.coe_inv, Ne, EReal.coe_eq_zero]
    exact inv_ne_zero (Nat.cast_ne_zero.2 hn)
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (x, ((n : EReal))⁻¹) :=
    EReal.continuousAt_mul (Or.inr (EReal.bot_lt_inv _).ne') (Or.inr (EReal.inv_lt_top _).ne)
      (Or.inr hinv) (Or.inr hinv)
  exact hcont.comp (f := fun x : EReal ↦ (x, ((n : EReal))⁻¹))
    (continuous_id.prodMk continuous_const).continuousAt

namespace MeasureTheory

section Trim

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

lemma Measure.trim_smul (hm : m ≤ m0) (c : ℝ≥0) : (c • μ).trim hm = c • μ.trim hm :=
  @Measure.ext _ m _ _ fun s hs ↦ by
    rw [trim_measurableSet_eq hm hs, Measure.smul_apply, Measure.smul_apply,
      trim_measurableSet_eq hm hs]

instance isProbabilityMeasure_trim (hm : m ≤ m0) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.trim hm) :=
  ⟨by rw [trim_measurableSet_eq hm MeasurableSet.univ, measure_univ]⟩

end Trim

section IndepSup

variable {Ω : Type*}

/-- **Markov property of independent σ-algebras.** Let `m₁ ≤ m₂` and `m₃` be sub-σ-algebras with
`m₂` and `m₃` independent under the finite measure `μ`. If an `m₂`-measurable `g : Ω → ℝ≥0∞` of
finite integral and an `m₁`-measurable `g'` have the same integrals over all `m₁`-measurable sets
(`g'` is a version of the conditional expectation of `g` given `m₁`), then they have the same
integrals over all `m₁ ⊔ m₃`-measurable sets: `μ[g | m₁ ⊔ m₃] = μ[g | m₁]`. -/
theorem setLIntegral_eq_of_indep_sup {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ)
    (h₃ : m₃ ≤ mΩ) (hind : Indep m₂ m₃ μ) {g g' : Ω → ℝ≥0∞} (hg : Measurable[m₂] g)
    (hg' : Measurable[m₁] g') (hfin : ∫⁻ x, g x ∂μ ≠ ∞)
    (h : ∀ s, MeasurableSet[m₁] s → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, g' x ∂μ) :
    ∀ s, MeasurableSet[m₁ ⊔ m₃] s → ∫⁻ x in s, g x ∂μ = ∫⁻ x in s, g' x ∂μ := by
  have h₁ : m₁ ≤ mΩ := h₁₂.trans h₂
  have hle : m₁ ⊔ m₃ ≤ mΩ := sup_le h₁ h₃
  set C : Set (Set Ω) := {s | ∃ A B, MeasurableSet[m₁] A ∧ MeasurableSet[m₃] B ∧ s = A ∩ B}
  have hC : IsPiSystem C := by
    rintro _ ⟨A, B, hA, hB, rfl⟩ _ ⟨A', B', hA', hB', rfl⟩ -
    exact ⟨A ∩ A', B ∩ B', hA.inter hA', hB.inter hB', Set.inter_inter_inter_comm A B A' B'⟩
  have hgen : m₁ ⊔ m₃ = MeasurableSpace.generateFrom C := by
    refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨A, Set.univ, hA, MeasurableSet.univ, (Set.inter_univ A).symm⟩
    · intro B hB
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, B, MeasurableSet.univ, hB, (Set.univ_inter B).symm⟩
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      exact ((le_sup_left : m₁ ≤ m₁ ⊔ m₃) A hA).inter ((le_sup_right : m₃ ≤ m₁ ⊔ m₃) B hB)
  -- the two measures `g μ` and `g' μ` on `m₁ ⊔ m₃`
  have : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hfin
  have hfin' : ∫⁻ x, g' x ∂μ ≠ ∞ := by
    rw [← setLIntegral_univ, ← h _ MeasurableSet.univ, setLIntegral_univ]
    exact hfin
  have : IsFiniteMeasure (μ.withDensity g') := isFiniteMeasure_withDensity hfin'
  have key : (μ.withDensity g).trim hle = (μ.withDensity g').trim hle := by
    refine @ext_of_generate_finite Ω (m₁ ⊔ m₃) _ _ C hgen hC _ ?_ ?_
    · rintro _ ⟨A, B, hA, hB, rfl⟩
      rw [trim_measurableSet_eq hle (hgen ▸ MeasurableSpace.measurableSet_generateFrom
          ⟨A, B, hA, hB, rfl⟩),
        trim_measurableSet_eq hle (hgen ▸ MeasurableSpace.measurableSet_generateFrom
          ⟨A, B, hA, hB, rfl⟩),
        withDensity_apply _ ((h₁ A hA).inter (h₃ B hB)),
        withDensity_apply _ ((h₁ A hA).inter (h₃ B hB)),
        ← lintegral_indicator ((h₁ A hA).inter (h₃ B hB)),
        ← lintegral_indicator ((h₁ A hA).inter (h₃ B hB))]
      have hind' : ∀ {f : Ω → ℝ≥0∞}, Measurable[m₂] f →
          ∫⁻ x, (A ∩ B).indicator f x ∂μ = (∫⁻ x, A.indicator f x ∂μ) * μ B := by
        intro f hf
        have hfA : Measurable[m₂] (A.indicator f) := hf.indicator (h₁₂ A hA)
        have hB1 : Measurable[m₃] (B.indicator fun _ ↦ (1 : ℝ≥0∞)) := measurable_const.indicator hB
        calc ∫⁻ x, (A ∩ B).indicator f x ∂μ
            = ∫⁻ x, A.indicator f x * B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ :=
              lintegral_congr fun x ↦ by rw [← Set.inter_indicator_mul]; simp
          _ = (∫⁻ x, A.indicator f x ∂μ) * ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ := by
              refine lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hfA.mono h₂ le_rfl).aemeasurable
                (hB1.mono h₃ le_rfl).aemeasurable ?_
              rw [IndepFun_iff_Indep]
              exact indep_of_indep_of_le hind (measurable_iff_comap_le.1 hfA)
                (measurable_iff_comap_le.1 hB1)
          _ = (∫⁻ x, A.indicator f x ∂μ) * μ B := by
              rw [lintegral_indicator (h₃ B hB), setLIntegral_const, one_mul]
      rw [hind' hg, hind' (hg'.mono h₁₂ le_rfl), lintegral_indicator (h₁ A hA),
        lintegral_indicator (h₁ A hA), h A hA]
    · rw [trim_measurableSet_eq hle MeasurableSet.univ, trim_measurableSet_eq hle MeasurableSet.univ,
        withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
        h _ MeasurableSet.univ]
  intro s hs
  have := congrArg (fun ρ ↦ ρ s) key
  simpa only [trim_measurableSet_eq hle hs, withDensity_apply _ (hle s hs)] using this

end IndepSup

end MeasureTheory

namespace InformationTheory

variable {𝓧 : Type*}

/-- If a measurable `f` preserves `μ` and `ν`, the relative entropy on a sub-σ-algebra `m` is at
most the relative entropy on its preimage `f⁻¹ m`: this is the data processing inequality
`klDiv_map_le` for `f : (𝓧, f⁻¹ m) → (𝓧, m)`. Both measures being invariant, `f⁻¹ m` and `m`
give the same relative entropy as soon as `m` is itself a preimage (as for translates). -/
theorem klDiv_trim_le_klDiv_trim_comap {m m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hm : m ≤ m𝓧) {f : 𝓧 → 𝓧} (hf : Measurable f) (hμ : μ.map f = μ)
    (hν : ν.map f = ν) :
    klDiv (μ.trim hm) (ν.trim hm)
      ≤ klDiv (μ.trim (hf.mono le_rfl hm).comap_le) (ν.trim (hf.mono le_rfl hm).comap_le) := by
  have key : ∀ ρ : Measure 𝓧, ρ.map f = ρ →
      ρ.trim hm = @Measure.map _ _ (m.comap f) m f (ρ.trim (hf.mono le_rfl hm).comap_le) := by
    intro ρ hρ
    rw [map_trim_comap (hf.mono le_rfl hm)]
    conv_lhs => rw [← hρ]
    rw [trim_eq_map, Measure.map_map (measurable_id'' hm) hf]
    rfl
  rw [key μ hμ, key ν hν]
  exact klDiv_map_le _ _ (Measurable.of_comap_le le_rfl)

/-- **Chain rule for the relative entropy through a density measurable for a sub-σ-algebra.**
Let `ν = g • lam` with `g` measurable for `m ≤ m𝓧`, and suppose `μ = ν` on `m`. Then
`𝓗(μ | lam) = 𝓗(μ | ν) + 𝓗_m(μ | lam)`, in `[0, ∞]`. (Georgii uses this in the proofs of (15.10)
and (15.16): `𝓗_Λ(μ) − 𝓗_{Λ ∪ Δ}(μ) = 𝓗_{Λ ∪ Δ}(μ | μ λ_{Δ ∖ Λ})`.) -/
theorem klDiv_eq_add_klDiv_trim_of_withDensity {m m𝓧 : MeasurableSpace 𝓧} (hm : m ≤ m𝓧)
    {μ ν lam : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure lam]
    {g : 𝓧 → ℝ≥0∞} (hg : Measurable[m] g) (hν : ν = lam.withDensity g)
    (hμν : μ.trim hm = ν.trim hm) :
    klDiv μ lam = klDiv μ ν + klDiv (μ.trim hm) (lam.trim hm) := by
  have hg' : Measurable g := hg.mono hm le_rfl
  have hνl : ν ≪ lam := hν ▸ withDensity_absolutelyContinuous _ _
  have hνm : ν.trim hm = (lam.trim hm).withDensity g := by rw [hν, trim_withDensity hm hg]
  by_cases hac : μ ≪ lam
  swap
  · have hac' : ¬ μ ≪ ν := fun h ↦ hac (h.trans hνl)
    rw [klDiv_of_not_ac hac, klDiv_of_not_ac hac', top_add]
  -- `μ` does not charge `{g = 0}`, hence `μ ≪ ν`
  have hZ : MeasurableSet[m] {x | g x = 0} := hg (measurableSet_singleton 0)
  have hμZ : μ {x | g x = 0} = 0 := by
    calc μ {x | g x = 0} = μ.trim hm {x | g x = 0} := (trim_measurableSet_eq hm hZ).symm
      _ = ν.trim hm {x | g x = 0} := by rw [hμν]
      _ = ν {x | g x = 0} := trim_measurableSet_eq hm hZ
      _ = 0 := by
        rw [hν, withDensity_apply_eq_zero hg']
        have : {x | g x ≠ 0} ∩ {x | g x = 0} = ∅ := by ext x; simp
        rw [this, measure_empty]
  have hμν' : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
    rw [hν, withDensity_apply_eq_zero hg'] at hνs
    have h1 : μ ({x | g x ≠ 0} ∩ s) = 0 := hac hνs
    have h2 : μ ({x | g x = 0} ∩ s) = 0 := measure_mono_null Set.inter_subset_left hμZ
    refine le_antisymm ?_ zero_le
    calc μ s = μ (({x | g x ≠ 0} ∩ s) ∪ ({x | g x = 0} ∩ s)) := by
          congr 1
          ext x
          by_cases hx : g x = 0 <;> simp [hx]
      _ ≤ μ ({x | g x ≠ 0} ∩ s) + μ ({x | g x = 0} ∩ s) := measure_union_le _ _
      _ = 0 := by rw [h1, h2, add_zero]
  -- the log-likelihood ratios: `llr μ lam = llr μ ν + log g` `μ`-a.e.
  have hgν : ν.rnDeriv lam =ᵐ[lam] g := hν ▸ Measure.rnDeriv_withDensity lam hg'
  have hchain : μ.rnDeriv ν * ν.rnDeriv lam =ᵐ[lam] μ.rnDeriv lam :=
    Measure.rnDeriv_mul_rnDeriv hμν'
  have hgpos : ∀ᵐ x ∂μ, g x ≠ 0 := by
    rw [ae_iff]
    simpa using hμZ
  have hgne : ∀ᵐ x ∂μ, g x ≠ ∞ := by
    refine hac.ae_le ?_
    filter_upwards [hgν, Measure.rnDeriv_ne_top ν lam] with x hx hx'
    rwa [hx] at hx'
  have hllr : llr μ lam =ᵐ[μ] fun x ↦ llr μ ν x + log (g x).toReal := by
    filter_upwards [hac.ae_le hchain, hac.ae_le hgν, Measure.rnDeriv_pos hμν',
      hμν'.ae_le (Measure.rnDeriv_ne_top μ ν), hgpos, hgne] with x h1 h2 h3 h4 h5 h6
    simp only [llr_def]
    rw [← h1, Pi.mul_apply, h2, ENNReal.toReal_mul, Real.log_mul]
    · exact (ENNReal.toReal_pos h3.ne' h4).ne'
    · exact (ENNReal.toReal_pos h5 h6).ne'
  -- the relative entropy on `m` is `μ(log g)`
  have hgm : StronglyMeasurable[m] fun x ↦ log (g x).toReal :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hg)).stronglyMeasurable
  have hac_trim : μ.trim hm ≪ lam.trim hm := hac.trim hm
  have hllr_trim : llr (μ.trim hm) (lam.trim hm) =ᵐ[μ.trim hm] fun x ↦ log (g x).toReal := by
    have h1 : (μ.trim hm).rnDeriv (lam.trim hm) =ᵐ[lam.trim hm] g := by
      rw [hμν, hνm]
      exact Measure.rnDeriv_withDensity _ hg
    filter_upwards [hac_trim.ae_le h1] with x hx
    simp only [llr_def, hx]
  by_cases hA : Integrable (llr μ lam) μ
  swap
  · rw [klDiv_of_not_integrable hA]
    by_cases hB : Integrable (llr μ ν) μ
    · have hC : ¬ Integrable (fun x ↦ log (g x).toReal) μ := fun hC ↦
        hA ((hB.add hC).congr hllr.symm)
      have : klDiv (μ.trim hm) (lam.trim hm) = ∞ :=
        klDiv_of_not_integrable fun h ↦ hC (integrable_of_integrable_trim hm (h.congr hllr_trim))
      rw [this, add_top]
    · rw [klDiv_of_not_integrable hB, top_add]
  -- all three relative entropies are finite
  have hBtrim : Integrable (llr (μ.trim hm) (lam.trim hm)) (μ.trim hm) := by
    have h := klDiv_ne_top hac hA
    have h' : klDiv (μ.trim hm) (lam.trim hm) ≠ ∞ := ne_top_of_le_ne_top h (klDiv_trim_le μ lam hm)
    exact (klDiv_ne_top_iff.1 h').2
  have hC : Integrable (fun x ↦ log (g x).toReal) μ :=
    integrable_of_integrable_trim hm (hBtrim.congr hllr_trim)
  have hB : Integrable (llr μ ν) μ := by
    refine (hA.sub hC).congr ?_
    filter_upwards [hllr] with x hx
    simp only [Pi.sub_apply]
    rw [hx]
    ring
  rw [klDiv_of_ac_of_integrable hac hA, klDiv_of_ac_of_integrable hμν' hB,
    klDiv_of_ac_of_integrable hac_trim hBtrim,
    ← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg hμν' hB)
      (integral_llr_add_sub_measure_univ_nonneg hac_trim hBtrim)]
  congr 1
  have hνμ : ν.real Set.univ = μ.real Set.univ := by
    simp only [measureReal_def]
    rw [← trim_measurableSet_eq hm MeasurableSet.univ, ← hμν,
      trim_measurableSet_eq hm MeasurableSet.univ]
  have hint : ∫ x, llr μ lam x ∂μ = ∫ x, llr μ ν x ∂μ + ∫ x, log (g x).toReal ∂μ := by
    rw [← integral_add hB hC]
    exact integral_congr_ae hllr
  have htrim : ∫ x, llr (μ.trim hm) (lam.trim hm) x ∂(μ.trim hm)
      = ∫ x, log (g x).toReal ∂μ := by
    rw [integral_congr_ae hllr_trim, ← integral_trim hm hgm]
  have huniv : (μ.trim hm).real Set.univ = μ.real Set.univ := by
    simp [measureReal_def, trim_measurableSet_eq hm MeasurableSet.univ]
  have huniv' : (lam.trim hm).real Set.univ = lam.real Set.univ := by
    simp [measureReal_def, trim_measurableSet_eq hm MeasurableSet.univ]
  rw [htrim, huniv, huniv', hint, hνμ]
  ring

/-- The pointwise inequality behind `smul_klDiv_add_smul_klDiv_le`: for `s + t = 1` and
`x, y ≥ 0`, `s ψ(x) + t ψ(y) ≤ ψ(s x + t y) + s x log (1/s) + t y log (1/t)`, where `ψ = klFun`.
It follows from `log x ≤ log (s x + t y) - log s`. -/
private lemma smul_klFun_add_smul_klFun_le {s t x y : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    s * klFun x + t * klFun y
      ≤ klFun (s * x + t * y) + s * x * (-log s) + t * y * (-log t) := by
  have key : ∀ {a u : ℝ}, 0 < a → 0 ≤ u → a * u ≤ s * x + t * y →
      a * u * log u ≤ a * u * log (s * x + t * y) - a * u * log a := by
    intro a u ha hu hle
    rcases hu.eq_or_lt with rfl | hu'
    · simp
    · have h1 : log (a * u) ≤ log (s * x + t * y) := Real.log_le_log (by positivity) hle
      rw [Real.log_mul ha.ne' hu'.ne'] at h1
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ a * u)
      linarith
  have h1 := key hs hx (by nlinarith)
  have h2 := key ht hy (by nlinarith)
  simp only [klFun_apply]
  nlinarith

/-- **The convexity defect of the Kullback–Leibler divergence in its first argument** (Georgii,
in the proof of Proposition (15.14)): for probability measures and `s + t = 1`,
`s 𝓗(μ₁ | ν) + t 𝓗(μ₂ | ν) ≤ 𝓗(s μ₁ + t μ₂ | ν) + s log (1/s) + t log (1/t)`. Together with the
convexity `klDiv_smul_add_smul_le` this makes `μ ↦ 𝓗(μ | ν)` affine up to a bounded error. -/
theorem smul_klDiv_add_smul_klDiv_le {α : Type*} {mα : MeasurableSpace α} {μ₁ μ₂ ν : Measure α}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν] {s t : ℝ≥0}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) :
    s * klDiv μ₁ ν + t * klDiv μ₂ ν
      ≤ klDiv (s • μ₁ + t • μ₂) ν + ENNReal.ofReal (-(s * log s)) + ENNReal.ofReal (-(t * log t)) := by
  by_cases hac : s • μ₁ + t • μ₂ ≪ ν
  swap
  · simp [klDiv_of_not_ac hac]
  have hs1 : (s : ℝ) ≤ 1 := by
    have : (s : ℝ) + t = 1 := by exact_mod_cast hst
    linarith [NNReal.coe_pos.2 ht]
  have ht1 : (t : ℝ) ≤ 1 := by
    have : (s : ℝ) + t = 1 := by exact_mod_cast hst
    linarith [NNReal.coe_pos.2 hs]
  have hlogs : 0 ≤ -log (s : ℝ) := neg_nonneg.2 (Real.log_nonpos s.coe_nonneg hs1)
  have hlogt : 0 ≤ -log (t : ℝ) := neg_nonneg.2 (Real.log_nonpos t.coe_nonneg ht1)
  have hcs : 0 ≤ (s : ℝ) * (-log s) := mul_nonneg s.coe_nonneg hlogs
  have hct : 0 ≤ (t : ℝ) * (-log t) := mul_nonneg t.coe_nonneg hlogt
  have hac' : ∀ {a : ℝ≥0} {ρ ρ' : Measure α}, 0 < a → a • ρ + ρ' ≪ ν → ρ ≪ ν := by
    intro a ρ ρ' ha h
    refine Measure.AbsolutelyContinuous.mk fun A hA hν ↦ ?_
    have := h hν
    rw [Measure.add_apply, Measure.smul_apply, add_eq_zero, smul_eq_zero] at this
    exact this.1.resolve_left (by exact_mod_cast ha.ne')
  have h₁ : μ₁ ≪ ν := hac' hs hac
  have h₂ : μ₂ ≪ ν := hac' ht (by rwa [add_comm] at hac)
  have hf : (s • μ₁ + t • μ₂).rnDeriv ν =ᵐ[ν] fun x ↦ s * μ₁.rnDeriv ν x + t * μ₂.rnDeriv ν x := by
    filter_upwards [Measure.rnDeriv_add (s • μ₁) (t • μ₂) ν, Measure.rnDeriv_smul_left μ₁ ν s,
      Measure.rnDeriv_smul_left μ₂ ν t] with x hx h1 h2
    rw [hx, Pi.add_apply, h1, h2]
    rfl
  have hm : ∀ ρ : Measure α, Measurable fun x ↦ ENNReal.ofReal (klFun (ρ.rnDeriv ν x).toReal) :=
    fun ρ ↦ ENNReal.measurable_ofReal.comp (measurable_klFun.comp
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _)))
  -- the two constants as integrals against `ν`
  have hconst : ∀ {a : ℝ≥0} {ρ : Measure α} [IsProbabilityMeasure ρ], ρ ≪ ν →
      0 ≤ (a : ℝ) * (-log a) →
      ENNReal.ofReal (-(a * log a))
        = ∫⁻ x, ENNReal.ofReal (a * (ρ.rnDeriv ν x).toReal * (-log a)) ∂ν := by
    intro a ρ _ hρ ha
    calc ENNReal.ofReal (-(a * log a)) = ENNReal.ofReal (a * (-log a)) * ρ Set.univ := by
          rw [measure_univ, mul_one, mul_neg]
      _ = ENNReal.ofReal (a * (-log a)) * ∫⁻ x, ρ.rnDeriv ν x ∂ν := by
          rw [Measure.lintegral_rnDeriv hρ]
      _ = ∫⁻ x, ENNReal.ofReal (a * (-log a)) * ρ.rnDeriv ν x ∂ν :=
          (lintegral_const_mul _ (Measure.measurable_rnDeriv _ _)).symm
      _ = _ := by
          refine lintegral_congr_ae ?_
          filter_upwards [Measure.rnDeriv_ne_top ρ ν] with x hx
          conv_lhs => rw [← ENNReal.ofReal_toReal hx]
          rw [← ENNReal.ofReal_mul ha]
          congr 1
          ring
  rw [klDiv_eq_lintegral_klFun_of_ac hac, klDiv_eq_lintegral_klFun_of_ac h₁,
    klDiv_eq_lintegral_klFun_of_ac h₂, ← lintegral_const_mul _ (hm μ₁), ← lintegral_const_mul _ (hm μ₂),
    ← lintegral_add_left ((hm μ₁).const_mul _), hconst h₁ hcs, hconst h₂ hct,
    ← lintegral_add_left (by fun_prop), ← lintegral_add_left (by fun_prop)]
  refine lintegral_mono_ae ?_
  filter_upwards [hf, Measure.rnDeriv_ne_top μ₁ ν, Measure.rnDeriv_ne_top μ₂ ν] with x hx h1 h2
  rw [hx]
  set x₁ := (μ₁.rnDeriv ν x).toReal with hx₁_def
  set x₂ := (μ₂.rnDeriv ν x).toReal with hx₂_def
  have hx₁ : 0 ≤ x₁ := ENNReal.toReal_nonneg
  have hx₂ : 0 ≤ x₂ := ENNReal.toReal_nonneg
  have hu : ((s : ℝ≥0∞) * μ₁.rnDeriv ν x + t * μ₂.rnDeriv ν x).toReal = s * x₁ + t * x₂ := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal]
  rw [hu]
  have hu₀ : 0 ≤ (s : ℝ) * x₁ + t * x₂ :=
    add_nonneg (mul_nonneg s.coe_nonneg hx₁) (mul_nonneg t.coe_nonneg hx₂)
  calc (s : ℝ≥0∞) * ENNReal.ofReal (klFun x₁) + t * ENNReal.ofReal (klFun x₂)
      = ENNReal.ofReal (s * klFun x₁ + t * klFun x₂) := by
        rw [ENNReal.ofReal_add (mul_nonneg s.coe_nonneg (klFun_nonneg hx₁))
          (mul_nonneg t.coe_nonneg (klFun_nonneg hx₂)), ENNReal.ofReal_mul s.coe_nonneg,
          ENNReal.ofReal_mul t.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    _ ≤ ENNReal.ofReal (klFun (s * x₁ + t * x₂) + s * x₁ * (-log s) + t * x₂ * (-log t)) :=
        ENNReal.ofReal_le_ofReal (smul_klFun_add_smul_klFun_le (by exact_mod_cast hs)
          (by exact_mod_cast ht) (by exact_mod_cast hst) hx₁ hx₂)
    _ = _ := by
        rw [ENNReal.ofReal_add (add_nonneg (klFun_nonneg hu₀)
            (mul_nonneg (mul_nonneg s.coe_nonneg hx₁) hlogs))
            (mul_nonneg (mul_nonneg t.coe_nonneg hx₂) hlogt),
          ENNReal.ofReal_add (klFun_nonneg hu₀) (mul_nonneg (mul_nonneg s.coe_nonneg hx₁) hlogs)]

end InformationTheory

/-! ### Georgii §15.2 -/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (15.8).** The relative entropy `𝓗_Λ(μ | ν)` of `μ` with respect to `ν` on the
cylinder σ-algebra `𝓕_Λ` of a set of sites `Λ`: Mathlib's Kullback–Leibler divergence of the
measures trimmed to `cylinderEvents Λ`. -/
abbrev relativeEntropyIn (Λ : Set S) (μ ν : Measure (S → E)) : ℝ≥0∞ :=
  klDiv (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ)))
    (ν.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ)))

variable {μ ν : Measure (S → E)}

/-- **Georgii (15.5)(c).** The relative entropy is monotone in the volume. -/
lemma relativeEntropyIn_mono [IsFiniteMeasure μ] [IsFiniteMeasure ν] {Λ Δ : Set S} (h : Λ ⊆ Δ) :
    relativeEntropyIn Λ μ ν ≤ relativeEntropyIn Δ μ ν :=
  klDiv_trim_mono (cylinderEvents_mono h) cylinderEvents_le_pi

/-- `𝓗_∅(μ | ν) = 0` for probability measures. -/
@[simp] lemma relativeEntropyIn_empty [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    relativeEntropyIn (∅ : Set S) μ ν = 0 := by
  rw [relativeEntropyIn, klDiv_trim_eq_zero_iff]
  intro s hs
  rw [cylinderEvents_empty, MeasurableSpace.measurableSet_bot_iff] at hs
  rcases hs with rfl | rfl <;> simp

section Shift

variable [AddGroup S]

/-- The shift `θ_j` pulls `𝓕_Λ` back to `𝓕_{Λ - j}`. -/
lemma cylinderEvents_comap_shift (j : S) (Λ : Set S) :
    (cylinderEvents (X := fun _ : S ↦ E) Λ).comap (shift E j).toFun
      = cylinderEvents (X := fun _ : S ↦ E) ((· - j) '' Λ) := by
  have : (shift E j).toFun = fun ω : S → E ↦ fun i ↦ ω (i - j) := by
    funext ω i
    exact shift_toFun_apply j ω i
  rw [this, cylinderEvents_comap_precomp]

/-- The product measure `λ^S` of a probability measure is shift invariant. -/
lemma measurePreserving_shift_infinitePi (lam : Measure E) [IsProbabilityMeasure lam] (j : S) :
    MeasurePreserving (shift E j).toFun (Measure.infinitePi fun _ : S ↦ lam)
      (Measure.infinitePi fun _ : S ↦ lam) :=
  (shift E j).measurePreserving_infinitePi fun _ ↦ MeasurePreserving.id lam

/-- For measures invariant under the shift `θ_j`, `𝓗_Λ(μ | ν) ≤ 𝓗_{Λ - j}(μ | ν)`. -/
lemma relativeEntropyIn_le_relativeEntropyIn_image_sub [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {j : S} (hμ : MeasurePreserving (shift E j).toFun μ μ)
    (hν : MeasurePreserving (shift E j).toFun ν ν) (Λ : Set S) :
    relativeEntropyIn Λ μ ν ≤ relativeEntropyIn ((· - j) '' Λ) μ ν := by
  have h := klDiv_trim_le_klDiv_trim_comap (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ))
    (shift E j).measurable_toFun hμ.map_eq hν.map_eq
  refine h.trans (le_of_eq ?_)
  exact klDiv_trim_congr (cylinderEvents_comap_shift j Λ) _ _

/-- **Shift invariance of the relative entropy**, Georgii's remark after (15.10): for
shift-invariant `μ` and `ν`, `𝓗_{Λ + i}(μ | ν) = 𝓗_Λ(μ | ν)`. -/
lemma relativeEntropyIn_image_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ)
    (hν : ∀ j, MeasurePreserving (shift E j).toFun ν ν) (Λ : Set S) (i : S) :
    relativeEntropyIn ((· + i) '' Λ) μ ν = relativeEntropyIn Λ μ ν := by
  refine le_antisymm ?_ ?_
  · refine (relativeEntropyIn_le_relativeEntropyIn_image_sub (hμ i) (hν i) _).trans (le_of_eq ?_)
    congr 1
    rw [Set.image_image]
    simp
  · refine (relativeEntropyIn_le_relativeEntropyIn_image_sub (hμ (-i)) (hν (-i)) _).trans
      (le_of_eq ?_)
    congr 1
    simp [sub_eq_add_neg]

end Shift

section StrongSubadditivity

variable (lam : Measure E) [IsProbabilityMeasure lam]

/-- **Georgii Proposition (15.10)**, strong subadditivity of the entropy, stated for the relative
entropy with respect to the product measure `λ^S` (which is therefore *supermodular*): for every
probability measure `μ` on configuration space and all sets of sites `Λ, Δ`,
`𝓗_Λ(μ | λ^S) + 𝓗_Δ(μ | λ^S) ≤ 𝓗_{Λ ∩ Δ}(μ | λ^S) + 𝓗_{Λ ∪ Δ}(μ | λ^S)`.
Georgii states it for finite `Λ, Δ`; finiteness is not used. -/
theorem relativeEntropyIn_add_relativeEntropyIn_le [IsProbabilityMeasure μ] (Λ Δ : Set S) :
    relativeEntropyIn Λ μ (Measure.infinitePi fun _ ↦ lam)
        + relativeEntropyIn Δ μ (Measure.infinitePi fun _ ↦ lam)
      ≤ relativeEntropyIn (Λ ∩ Δ) μ (Measure.infinitePi fun _ ↦ lam)
        + relativeEntropyIn (Λ ∪ Δ) μ (Measure.infinitePi fun _ ↦ lam) := by
  set γ : Measure (S → E) := Measure.infinitePi fun _ ↦ lam with hγ_def
  have hΛ : cylinderEvents (X := fun _ : S ↦ E) Λ ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hΔ : cylinderEvents (X := fun _ : S ↦ E) Δ ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hΛΔ : cylinderEvents (X := fun _ : S ↦ E) (Λ ∪ Δ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hI : cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hD : cylinderEvents (X := fun _ : S ↦ E) (Δ \ Λ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hΛ_le : cylinderEvents (X := fun _ : S ↦ E) Λ ≤ cylinderEvents (X := fun _ : S ↦ E) (Λ ∪ Δ) :=
    cylinderEvents_mono Set.subset_union_left
  have hΔ_le : cylinderEvents (X := fun _ : S ↦ E) Δ ≤ cylinderEvents (X := fun _ : S ↦ E) (Λ ∪ Δ) :=
    cylinderEvents_mono Set.subset_union_right
  have hI_le : cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ≤ cylinderEvents (X := fun _ : S ↦ E) Λ :=
    cylinderEvents_mono Set.inter_subset_left
  have hI_leΔ : cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ≤ cylinderEvents (X := fun _ : S ↦ E) Δ :=
    cylinderEvents_mono Set.inter_subset_right
  by_cases hac : μ.trim hΛΔ ≪ γ.trim hΛΔ
  swap
  · have : relativeEntropyIn (Λ ∪ Δ) μ γ = ∞ := klDiv_of_not_ac hac
    rw [this, add_top]
    exact le_top
  -- `g`: the density of `μ` on `𝓕_Λ`; `ν = g λ^S` is Georgii's `μ λ_{Δ ∖ Λ}` on `𝓕_{Λ ∪ Δ}`
  set g := (μ.trim hΛ).rnDeriv (γ.trim hΛ) with hg_def
  have hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λ] g := Measure.measurable_rnDeriv _ _
  have hacΛ : μ.trim hΛ ≪ γ.trim hΛ := by
    rw [← trim_trim (hm₁₂ := hΛ_le) (hm₂ := hΛΔ), ← trim_trim (hm₁₂ := hΛ_le) (hm₂ := hΛΔ)]
    exact hac.trim hΛ_le
  have hgfin : ∫⁻ x, g x ∂γ ≠ ∞ := by
    rw [← lintegral_trim hΛ hg]
    exact (Measure.lintegral_rnDeriv_lt_top _ _).ne
  set ν : Measure (S → E) := γ.withDensity g with hν_def
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_withDensity hgfin
  have hνΛ : ν.trim hΛ = μ.trim hΛ := by
    rw [hν_def, trim_withDensity hΛ hg, Measure.withDensity_rnDeriv_eq _ _ hacΛ]
  have hνΛΔ : ν.trim hΛΔ = (γ.trim hΛΔ).withDensity g :=
    trim_withDensity hΛΔ (hg.mono hΛ_le le_rfl)
  -- `g'`: the density of `ν` on `𝓕_{Λ ∩ Δ}`, which is also its density on `𝓕_Δ`
  set g' := (ν.trim hI).rnDeriv (γ.trim hI) with hg'_def
  have hg' : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ)] g' :=
    Measure.measurable_rnDeriv _ _
  have hνI : ν.trim hI = (γ.trim hI).withDensity g' :=
    (Measure.withDensity_rnDeriv_eq _ _ ((withDensity_absolutelyContinuous γ g).trim hI)).symm
  have hνΔ : ν.trim hΔ = (γ.trim hΔ).withDensity g' := by
    refine @Measure.ext _ (cylinderEvents (X := fun _ : S ↦ E) Δ) _ _ fun s hs ↦ ?_
    rw [trim_measurableSet_eq hΔ hs, withDensity_apply _ hs, restrict_trim hΔ γ hs,
      lintegral_trim hΔ (hg'.mono hI_leΔ le_rfl), hν_def, withDensity_apply _ (hΔ s hs)]
    have hsup : cylinderEvents (X := fun _ : S ↦ E) Δ
        = cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ⊔ cylinderEvents (X := fun _ : S ↦ E) (Δ \ Λ) := by
      rw [← cylinderEvents_union]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
      tauto
    refine setLIntegral_eq_of_indep_sup hI_le hΛ hD ?_ hg hg' hgfin ?_ s (hsup ▸ hs)
    · exact indep_of_indep_of_le_right (indep_cylinderEvents_compl_infinitePi (fun _ ↦ lam) Λ)
        (cylinderEvents_mono fun x hx ↦ hx.2)
    · intro B hB
      have := congrArg (fun ρ ↦ ρ B) hνI
      rwa [trim_measurableSet_eq hI hB, withDensity_apply _ hB, restrict_trim hI γ hB,
        lintegral_trim hI hg', hν_def, withDensity_apply _ (hI B hB)] at this
  -- the two chain rules and the monotonicity
  have hB1 : klDiv (μ.trim hΛΔ) (γ.trim hΛΔ)
      = klDiv (μ.trim hΛΔ) (ν.trim hΛΔ) + klDiv (μ.trim hΛ) (γ.trim hΛ) := by
    have := klDiv_eq_add_klDiv_trim_of_withDensity hΛ_le (μ := μ.trim hΛΔ) (ν := ν.trim hΛΔ)
      (lam := γ.trim hΛΔ) hg hνΛΔ (by rw [trim_trim, trim_trim, hνΛ])
    rwa [trim_trim, trim_trim] at this
  have hB2 : klDiv (μ.trim hΔ) (γ.trim hΔ)
      = klDiv (μ.trim hΔ) (ν.trim hΔ) + klDiv (μ.trim hI) (γ.trim hI) := by
    have hμνI : μ.trim hI = ν.trim hI := by
      rw [← trim_trim (hm₁₂ := hI_le) (hm₂ := hΛ), ← trim_trim (hm₁₂ := hI_le) (hm₂ := hΛ), hνΛ]
    have := klDiv_eq_add_klDiv_trim_of_withDensity hI_leΔ (μ := μ.trim hΔ) (ν := ν.trim hΔ)
      (lam := γ.trim hΔ) hg' hνΔ (by rw [trim_trim, trim_trim, hμνI])
    rwa [trim_trim, trim_trim] at this
  have hM : klDiv (μ.trim hΔ) (ν.trim hΔ) ≤ klDiv (μ.trim hΛΔ) (ν.trim hΛΔ) := by
    have := klDiv_trim_mono (μ := μ) (ν := ν) hΔ_le hΛΔ
    exact this
  change klDiv (μ.trim hΛ) (γ.trim hΛ) + klDiv (μ.trim hΔ) (γ.trim hΔ)
    ≤ klDiv (μ.trim hI) (γ.trim hI) + klDiv (μ.trim hΛΔ) (γ.trim hΛΔ)
  rw [hB1, hB2]
  calc klDiv (μ.trim hΛ) (γ.trim hΛ) + (klDiv (μ.trim hΔ) (ν.trim hΔ) + klDiv (μ.trim hI) (γ.trim hI))
      = klDiv (μ.trim hI) (γ.trim hI)
          + (klDiv (μ.trim hΔ) (ν.trim hΔ) + klDiv (μ.trim hΛ) (γ.trim hΛ)) := by ring
    _ ≤ klDiv (μ.trim hI) (γ.trim hI)
          + (klDiv (μ.trim hΛΔ) (ν.trim hΛΔ) + klDiv (μ.trim hΛ) (γ.trim hΛ)) := by gcongr

end StrongSubadditivity

section Entropy

variable (lam : Measure E) [IsProbabilityMeasure lam]

/-- **Georgii (15.9).** The entropy `𝓗_Λ(μ) = -𝓗_Λ(μ | λ^S)` of `μ` in `Λ` relative to the a priori
probability measure `λ`, an extended real in `[-∞, 0]` (`-∞` when `μ` is not absolutely continuous
with respect to `λ^S` on `𝓕_Λ`, or the density has no integrable logarithm). -/
abbrev entropyIn (Λ : Set S) (μ : Measure (S → E)) : EReal :=
  -(relativeEntropyIn Λ μ (Measure.infinitePi fun _ ↦ lam) : EReal)

variable {lam}

omit [IsProbabilityMeasure lam] in
lemma entropyIn_nonpos (Λ : Set S) (μ : Measure (S → E)) : entropyIn lam Λ μ ≤ 0 :=
  EReal.neg_le_zero.2 (EReal.coe_ennreal_nonneg _)

omit [IsProbabilityMeasure lam] in
lemma entropyIn_ne_top (Λ : Set S) (μ : Measure (S → E)) : entropyIn lam Λ μ ≠ ⊤ := by
  rw [Ne, EReal.neg_eq_top_iff]
  exact EReal.coe_ennreal_ne_bot _

@[simp] lemma entropyIn_empty [IsProbabilityMeasure μ] : entropyIn lam (∅ : Set S) μ = 0 := by
  simp [entropyIn]

private lemma neg_coe_add_neg_coe (x y : ℝ≥0∞) :
    -(x : EReal) + -(y : EReal) = -((x + y : ℝ≥0∞) : EReal) := by
  rw [EReal.coe_ennreal_add, EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg]

/-- **Georgii Proposition (15.10)**, strong subadditivity of the entropy:
`𝓗_{Λ ∩ Δ}(μ) + 𝓗_{Λ ∪ Δ}(μ) ≤ 𝓗_Λ(μ) + 𝓗_Δ(μ)`. -/
theorem entropyIn_add_entropyIn_le [IsProbabilityMeasure μ] (Λ Δ : Set S) :
    entropyIn lam (Λ ∩ Δ) μ + entropyIn lam (Λ ∪ Δ) μ ≤ entropyIn lam Λ μ + entropyIn lam Δ μ := by
  rw [entropyIn, entropyIn, entropyIn, entropyIn, neg_coe_add_neg_coe, neg_coe_add_neg_coe,
    EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  exact relativeEntropyIn_add_relativeEntropyIn_le lam Λ Δ

/-- Subadditivity of the entropy on disjoint volumes (Georgii, after (15.10)). -/
theorem entropyIn_union_le [IsProbabilityMeasure μ] {Λ Δ : Set S} (h : Disjoint Λ Δ) :
    entropyIn lam (Λ ∪ Δ) μ ≤ entropyIn lam Λ μ + entropyIn lam Δ μ := by
  have := entropyIn_add_entropyIn_le (lam := lam) (μ := μ) Λ Δ
  rwa [Set.disjoint_iff_inter_eq_empty.1 h, entropyIn_empty, zero_add] at this

/-- Shift invariance of the entropy for shift-invariant `μ`: `𝓗_{Λ + i}(μ) = 𝓗_Λ(μ)`. -/
theorem entropyIn_image_add [AddGroup S] [IsFiniteMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Set S) (i : S) :
    entropyIn lam ((· + i) '' Λ) μ = entropyIn lam Λ μ := by
  rw [entropyIn, entropyIn,
    relativeEntropyIn_image_add hμ (measurePreserving_shift_infinitePi lam) Λ i]

private lemma mul_neg_ereal (x y : EReal) : x * -y = -(x * y) := by
  rw [EReal.mul_comm, EReal.neg_mul, EReal.mul_comm]

/-- **Georgii (15.5)(d)**: the entropy `𝓗_Λ(·)` is concave. -/
theorem smul_entropyIn_add_smul_entropyIn_le {μ₁ μ₂ : Measure (S → E)} [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂] {s t : ℝ≥0} (hst : s + t = 1) (Λ : Set S) :
    ((s : ℝ) : EReal) * entropyIn lam Λ μ₁ + ((t : ℝ) : EReal) * entropyIn lam Λ μ₂
      ≤ entropyIn lam Λ (s • μ₁ + t • μ₂) := by
  have h := klDiv_smul_add_smul_le (μ₁ := μ₁.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ)))
    (μ₂ := μ₂.trim cylinderEvents_le_pi)
    (ν₁ := (Measure.infinitePi fun _ ↦ lam).trim cylinderEvents_le_pi)
    (ν₂ := (Measure.infinitePi fun _ ↦ lam).trim cylinderEvents_le_pi) s t
  rw [← add_smul, hst, one_smul, ← Measure.trim_smul, ← Measure.trim_smul, ← trim_add] at h
  simp only [entropyIn, mul_neg_ereal, ← EReal.coe_nnreal_eq_coe_real, ← EReal.coe_ennreal_mul,
    neg_coe_add_neg_coe, EReal.neg_le_neg_iff, EReal.coe_ennreal_le_coe_ennreal_iff]
  exact h

/-- **Georgii, in the proof of Proposition (15.14)**: the convexity defect of the entropy,
`𝓗_Λ(s μ₁ + t μ₂) ≤ s 𝓗_Λ(μ₁) + t 𝓗_Λ(μ₂) - s log s - t log t` for `s + t = 1`. -/
theorem entropyIn_smul_add_smul_le {μ₁ μ₂ : Measure (S → E)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t) (hst : s + t = 1) (Λ : Set S) :
    entropyIn lam Λ (s • μ₁ + t • μ₂)
      ≤ ((s : ℝ) : EReal) * entropyIn lam Λ μ₁ + ((t : ℝ) : EReal) * entropyIn lam Λ μ₂
        + ((-(s * log s) + -(t * log t) : ℝ) : EReal) := by
  have h := smul_klDiv_add_smul_klDiv_le (μ₁ := μ₁.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ)))
    (μ₂ := μ₂.trim cylinderEvents_le_pi)
    (ν := (Measure.infinitePi fun _ ↦ lam).trim cylinderEvents_le_pi) hs ht hst
  rw [← Measure.trim_smul, ← Measure.trim_smul, ← trim_add] at h
  have hs1 : (s : ℝ) ≤ 1 := by
    have : (s : ℝ) + t = 1 := by exact_mod_cast hst
    linarith [NNReal.coe_pos.2 ht]
  have ht1 : (t : ℝ) ≤ 1 := by
    have : (s : ℝ) + t = 1 := by exact_mod_cast hst
    linarith [NNReal.coe_pos.2 hs]
  have hcs : 0 ≤ -((s : ℝ) * log s) := by
    rw [neg_mul_eq_mul_neg]
    exact mul_nonneg s.coe_nonneg (neg_nonneg.2 (Real.log_nonpos s.coe_nonneg hs1))
  have hct : 0 ≤ -((t : ℝ) * log t) := by
    rw [neg_mul_eq_mul_neg]
    exact mul_nonneg t.coe_nonneg (neg_nonneg.2 (Real.log_nonpos t.coe_nonneg ht1))
  -- pass to `EReal`
  set K := relativeEntropyIn Λ (s • μ₁ + t • μ₂) (Measure.infinitePi fun _ ↦ lam)
  set K₁ := relativeEntropyIn Λ μ₁ (Measure.infinitePi fun _ ↦ lam)
  set K₂ := relativeEntropyIn Λ μ₂ (Measure.infinitePi fun _ ↦ lam)
  set c : ℝ≥0∞ := ENNReal.ofReal (-(s * log s)) + ENNReal.ofReal (-(t * log t)) with hc_def
  have hc : (c : EReal) = ((-(s * log s) + -(t * log t) : ℝ) : EReal) := by
    rw [hc_def, EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
      max_eq_left hcs, max_eq_left hct, EReal.coe_add]
  have h' : ((s * K₁ + t * K₂ : ℝ≥0∞) : EReal) ≤ (K : EReal) + c := by
    rw [← EReal.coe_ennreal_add, EReal.coe_ennreal_le_coe_ennreal_iff, hc_def, ← add_assoc]
    exact h
  have hcne : c ≠ ⊤ := by
    rw [hc_def]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  change -(K : EReal) ≤ ((s : ℝ) : EReal) * -(K₁ : EReal) + ((t : ℝ) : EReal) * -(K₂ : EReal)
    + ((-(s * log s) + -(t * log t) : ℝ) : EReal)
  rw [mul_neg_ereal, mul_neg_ereal, ← EReal.coe_nnreal_eq_coe_real, ← EReal.coe_nnreal_eq_coe_real,
    ← EReal.coe_ennreal_mul, ← EReal.coe_ennreal_mul, neg_coe_add_neg_coe, ← hc,
    ← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ennreal_ne_bot _))
      (Or.inl (by rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact hcne)),
    ← EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot _)) (Or.inr (EReal.coe_ennreal_ne_bot _)),
    EReal.neg_le_neg_iff]
  exact h'

end Entropy

/-! ### Specific entropy on `ℤ^d` (Georgii Theorem (15.12), Definition (15.13)) -/

section Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : Measure E) [IsProbabilityMeasure lam]
  {μ : Measure ((ι → ℤ) → E)}

/-- The entropy `Λ ↦ 𝓗_Λ(μ)` of a shift-invariant random field satisfies Georgii's hypotheses
(15.11)(i)–(ii): translation invariance and subadditivity on disjoint boxes. -/
theorem boxSubadditive_entropyIn [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) :
    BoxSubadditive fun Λ : Finset (ι → ℤ) ↦ entropyIn lam (Λ : Set (ι → ℤ)) μ where
  image_add_right Λ _ i := by
    rw [Finset.coe_image]
    exact entropyIn_image_add hμ _ i
  union_le Λ Δ _ _ hd _ := by
    rw [Finset.coe_union]
    exact entropyIn_union_le (Finset.disjoint_coe.2 hd)

variable (μ) in
/-- **Georgii Definition (15.13).** The *specific entropy* (mean entropy, entropy rate)
`𝓀(μ) = inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ 𝓗_Δ(μ)` of a random field `μ` on `ℤ^d` relative to the a priori
probability measure `λ`, as an extended real in `[-∞, 0]`; the infimum runs over the rectangular
boxes `Finset.IsBox`. By **Theorem (15.12)** (`tendsto_entropyIn_div_card`), for shift-invariant
`μ` this is the limit `lim |Λ_n|⁻¹ 𝓗_{Λ_n}(μ)` along any sequence of boxes all of whose sides tend
to infinity, in particular along cubes with `|Λ_n| → ∞`. -/
def specificEntropy : EReal :=
  ⨅ Δ : Finset (ι → ℤ), ⨅ (_ : Δ.IsBox), entropyIn lam (Δ : Set (ι → ℤ)) μ / (#Δ : EReal)

omit [IsProbabilityMeasure lam] in
lemma specificEntropy_le_entropyIn_div_card {Δ : Finset (ι → ℤ)} (hΔ : Δ.IsBox) :
    specificEntropy lam μ ≤ entropyIn lam (Δ : Set (ι → ℤ)) μ / (#Δ : EReal) :=
  iInf₂_le Δ hΔ

omit [IsProbabilityMeasure lam] in
/-- `𝓀(μ) ≤ 0` (Georgii: `𝓀(μ) ≤ log λ(E)`). -/
lemma specificEntropy_nonpos : specificEntropy lam μ ≤ 0 :=
  (specificEntropy_le_entropyIn_div_card lam (isBox_singleton 0)).trans
    (EReal.div_nonpos_of_nonpos_of_nonneg (entropyIn_nonpos _ _) (Nat.cast_nonneg' _))

omit [IsProbabilityMeasure lam] in
lemma specificEntropy_ne_top : specificEntropy lam μ ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (specificEntropy_nonpos lam)

variable {κ : Type*} {l : Filter κ} {m n : κ → ι → ℤ}

/-- **Georgii Theorem (15.12).** For a shift-invariant random field `μ ∈ 𝓟_Θ` and boxes
`Λ_j = ∏ₖ [mⱼₖ, nⱼₖ]` all of whose side lengths tend to infinity, `|Λ_j|⁻¹ 𝓗_{Λ_j}(μ)` converges
in `[-∞, 0]` to the specific entropy `𝓀(μ) = inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ 𝓗_Δ(μ)`. -/
theorem tendsto_entropyIn_div_card (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ entropyIn lam (Icc (m j) (n j) : Set (ι → ℤ)) μ / (#(Icc (m j) (n j)) : EReal))
      l (𝓝 (specificEntropy lam μ)) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  exact (boxSubadditive_entropyIn lam hpres).tendsto_div_card (fun Λ _ ↦ entropyIn_ne_top _ _) h

/-- **Georgii Theorem (15.12) as stated**, for cubes `Λ_n` with `|Λ_n| → ∞`. -/
theorem tendsto_entropyIn_div_card_cube (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    {s : κ → ℕ} (hs : Tendsto (fun j ↦ #(Icc (m j) fun k ↦ m j k + s j)) l atTop) :
    Tendsto (fun j ↦ entropyIn lam (Icc (m j) fun k ↦ m j k + s j : Set (ι → ℤ)) μ
      / (#(Icc (m j) fun k ↦ m j k + s j) : EReal)) l (𝓝 (specificEntropy lam μ)) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  exact (boxSubadditive_entropyIn lam hpres).tendsto_div_card_of_tendsto_card
    (fun Λ _ ↦ entropyIn_ne_top _ _) hs

/-! ### Georgii Proposition (15.14): `𝓀` is affine -/

/-- **Georgii Proposition (15.14), concavity.** `𝓀(s μ₁ + t μ₂) ≥ s 𝓀(μ₁) + t 𝓀(μ₂)` for
`s + t = 1`, for all finite measures `μ₁, μ₂` (no shift invariance is needed for this half). -/
theorem smul_specificEntropy_add_smul_specificEntropy_le {μ₁ μ₂ : Measure ((ι → ℤ) → E)}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {s t : ℝ≥0} (hst : s + t = 1) :
    ((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂
      ≤ specificEntropy lam (s • μ₁ + t • μ₂) := by
  refine le_iInf₂ fun Δ hΔ ↦ ?_
  have hs : (0 : EReal) ≤ ((s : ℝ) : EReal) := EReal.coe_nonneg.2 s.coe_nonneg
  have ht : (0 : EReal) ≤ ((t : ℝ) : EReal) := EReal.coe_nonneg.2 t.coe_nonneg
  calc ((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂
      ≤ ((s : ℝ) : EReal) * (entropyIn lam (Δ : Set (ι → ℤ)) μ₁ / (#Δ : EReal))
          + ((t : ℝ) : EReal) * (entropyIn lam (Δ : Set (ι → ℤ)) μ₂ / (#Δ : EReal)) :=
        add_le_add (mul_le_mul_of_nonneg_left (specificEntropy_le_entropyIn_div_card lam hΔ) hs)
          (mul_le_mul_of_nonneg_left (specificEntropy_le_entropyIn_div_card lam hΔ) ht)
    _ = (((s : ℝ) : EReal) * entropyIn lam (Δ : Set (ι → ℤ)) μ₁
          + ((t : ℝ) : EReal) * entropyIn lam (Δ : Set (ι → ℤ)) μ₂) / (#Δ : EReal) := by
        rw [EReal.mul_div, EReal.mul_div, EReal.add_div_of_nonneg_right (Nat.cast_nonneg' _)]
    _ ≤ entropyIn lam (Δ : Set (ι → ℤ)) (s • μ₁ + t • μ₂) / (#Δ : EReal) :=
        EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _)
          (smul_entropyIn_add_smul_entropyIn_le hst _)

/-- The cardinality of the cube `[0, N]^d` tends to infinity with `N` when `d ≥ 1`. -/
lemma tendsto_card_Icc_zero_natCast [Nonempty ι] :
    Tendsto (fun N : ℕ ↦ (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : ℝ)) atTop atTop := by
  have hcard : ∀ N : ℕ, N + 1 ≤ #(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) := fun N ↦ by
    simp only [Pi.card_Icc, Int.card_Icc, prod_const, card_univ]
    exact Nat.le_self_pow Fintype.card_ne_zero _
  refine tendsto_atTop_mono (fun N ↦ ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  exact_mod_cast (Nat.le_succ N).trans (hcard N)

/-- **Georgii Proposition (15.14), convexity.** For shift-invariant `μ₁, μ₂ ∈ 𝓟_Θ` and
`s + t = 1` with `s, t > 0`, `𝓀(s μ₁ + t μ₂) ≤ s 𝓀(μ₁) + t 𝓀(μ₂)`; with
`smul_specificEntropy_add_smul_specificEntropy_le`, `𝓀` is affine on `𝓟_Θ`. The dimension must
be positive: on `ℤ^0` the specific entropy is `-𝓗(μ | λ)`, which is strictly concave. -/
theorem specificEntropy_smul_add_smul_le [Nonempty ι] {μ₁ μ₂ : Measure ((ι → ℤ) → E)}
    (hμ₁ : μ₁ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hμ₂ : μ₂ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t = 1) :
    specificEntropy lam (s • μ₁ + t • μ₂)
      ≤ ((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂ := by
  have hμ := smul_add_smul_mem_invariantFields_shiftGroup hμ₁ hμ₂ hst
  have : IsProbabilityMeasure μ₁ := (mem_invariantFields_shiftGroup.1 hμ₁).1
  have : IsProbabilityMeasure μ₂ := (mem_invariantFields_shiftGroup.1 hμ₂).1
  -- the limits along the cubes `[0, N]^d`
  have hside : ∀ k : ι, Tendsto (fun N : ℕ ↦ (fun _ : ι ↦ (N : ℤ)) k - (fun _ : ι ↦ (0 : ℤ)) k)
      atTop atTop := fun k ↦ by simpa using tendsto_natCast_atTop_atTop (R := ℤ)
  have h₀ := tendsto_entropyIn_div_card lam hμ hside
  have h₁ := tendsto_entropyIn_div_card lam hμ₁ hside
  have h₂ := tendsto_entropyIn_div_card lam hμ₂ hside
  set c : ℝ := -(s * log s) + -(t * log t) with hc_def
  have hc : Tendsto (fun N : ℕ ↦ (c : EReal) / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal))
      atTop (𝓝 0) := by
    have : ∀ N : ℕ, (c : EReal) / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal)
        = ((c / #(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : ℝ) : EReal) := fun N ↦ by
      rw [EReal.coe_div, EReal.coe_natCast]
    simp_rw [this]
    rw [← EReal.coe_zero]
    exact EReal.tendsto_coe.2 (tendsto_const_nhds.div_atTop tendsto_card_Icc_zero_natCast)
  -- the limit of the right-hand side
  have hmul : ∀ {a : ℝ} {x : EReal} {u : ℕ → EReal}, 0 < a → x ≠ ⊤ → Tendsto u atTop (𝓝 x) →
      Tendsto (fun N ↦ (a : EReal) * u N) atTop (𝓝 ((a : EReal) * x)) := by
    intro a x u ha hx hu
    have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) ((a : EReal), x) :=
      EReal.continuousAt_mul (Or.inl (EReal.coe_ne_zero.2 ha.ne')) (Or.inl (EReal.coe_ne_zero.2 ha.ne'))
        (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))
    exact hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds hu)
  have hne : ∀ {a : ℝ} {x : EReal}, 0 < a → x ≤ 0 → (a : EReal) * x ≠ ⊤ := by
    intro a x ha hx
    exact ne_top_of_le_ne_top (by simp)
      (EReal.mul_nonpos_iff.2 (Or.inl ⟨EReal.coe_nonneg.2 ha.le, hx⟩))
  have hs' : (0 : ℝ) < s := NNReal.coe_pos.2 hs
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  have hadd : Tendsto (fun N : ℕ ↦ ((s : ℝ) : EReal)
      * (entropyIn lam (Icc (fun _ : ι ↦ (0 : ℤ)) (fun _ ↦ (N : ℤ)) : Set (ι → ℤ)) μ₁
        / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal))
      + ((t : ℝ) : EReal)
      * (entropyIn lam (Icc (fun _ : ι ↦ (0 : ℤ)) (fun _ ↦ (N : ℤ)) : Set (ι → ℤ)) μ₂
        / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal))
      + (c : EReal) / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal)) atTop
      (𝓝 (((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂
        + 0)) := by
    have hA := hmul hs' (specificEntropy_ne_top lam) h₁
    have hB := hmul ht' (specificEntropy_ne_top lam) h₂
    have hAB : Tendsto (fun N : ℕ ↦ ((s : ℝ) : EReal)
        * (entropyIn lam (Icc (fun _ : ι ↦ (0 : ℤ)) (fun _ ↦ (N : ℤ)) : Set (ι → ℤ)) μ₁
          / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal))
        + ((t : ℝ) : EReal)
        * (entropyIn lam (Icc (fun _ : ι ↦ (0 : ℤ)) (fun _ ↦ (N : ℤ)) : Set (ι → ℤ)) μ₂
          / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal))) atTop
        (𝓝 (((s : ℝ) : EReal) * specificEntropy lam μ₁
          + ((t : ℝ) : EReal) * specificEntropy lam μ₂)) := by
      have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
          (((s : ℝ) : EReal) * specificEntropy lam μ₁, ((t : ℝ) : EReal) * specificEntropy lam μ₂) :=
        EReal.continuousAt_add (Or.inl (hne hs' (specificEntropy_nonpos lam)))
          (Or.inr (hne ht' (specificEntropy_nonpos lam)))
      exact hcont.tendsto.comp (hA.prodMk_nhds hB)
    have hcont : ContinuousAt (fun p : EReal × EReal ↦ p.1 + p.2)
        (((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂,
          0) :=
      EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
    exact hcont.tendsto.comp (hAB.prodMk_nhds hc)
  rw [add_zero] at hadd
  refine le_of_tendsto_of_tendsto' h₀ hadd fun N ↦ ?_
  -- the finite-volume inequality, divided by `|Λ_N|`
  have hN : (0 : EReal) ≤ (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) : EReal) :=
    Nat.cast_nonneg' _
  rw [EReal.mul_div, EReal.mul_div, ← EReal.add_div_of_nonneg_right hN,
    ← EReal.add_div_of_nonneg_right hN]
  exact EReal.div_le_div_right_of_nonneg hN (entropyIn_smul_add_smul_le hs ht hst _)

end Lattice

/-! ### Georgii Proposition (15.14): upper semicontinuity -/

section LocalConvergence

variable (ν : Measure (S → E)) [IsFiniteMeasure ν]

/-- **Georgii, in the proof of Proposition (15.14)** (via Corollary (15.7)): for a finite volume
`Λ`, `μ ↦ 𝓗_Λ(μ | ν)` is lower semicontinuous in the topology of local convergence. -/
theorem lowerSemicontinuous_relativeEntropyIn (Λ : Finset S) :
    LowerSemicontinuous fun μ : WithLocalConvergence S E ↦
      relativeEntropyIn (Λ : Set S) (μ.toMeasure : Measure (S → E)) ν := by
  have hΛ : cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  simp_rw [relativeEntropyIn, klDiv_trim_eq_iSup_sum hΛ]
  refine lowerSemicontinuous_biSup fun P hP ↦ ?_
  -- the `if` as a sum of lower semicontinuous summands
  have hsum : ∀ μ : Measure (S → E),
      (if ∀ A ∈ P, ν A = 0 → μ A = 0 then
        ∑ A ∈ P, ENNReal.ofReal (μ.real A * log (μ.real A / ν.real A) + ν.real A - μ.real A)
      else ∞)
      = ∑ A ∈ P, if ν A = 0 ∧ μ A ≠ 0 then ∞ else
          ENNReal.ofReal (μ.real A * log (μ.real A / ν.real A) + ν.real A - μ.real A) := by
    intro μ
    split_ifs with h
    · refine Finset.sum_congr rfl fun A hA ↦ ?_
      split_ifs with h'
      · exact absurd (h A hA h'.1) h'.2
      · rfl
    · push Not at h
      obtain ⟨A, hA, h1, h2⟩ := h
      exact (ENNReal.sum_eq_top.2 ⟨A, hA, by simp [h1, h2]⟩).symm
  simp_rw [hsum]
  refine lowerSemicontinuous_sum fun A hA ↦ ?_
  have hA' : A ∈ localEvents S E := mem_localEvents_of_cylinderEvents Λ (hP.2.2 A hA)
  have hcont : Continuous fun μ : WithLocalConvergence S E ↦
      ENNReal.ofReal ((μ.toMeasure : Measure (S → E)).real A
        * log ((μ.toMeasure : Measure (S → E)).real A / ν.real A) + ν.real A
        - (μ.toMeasure : Measure (S → E)).real A) := by
    refine ENNReal.continuous_ofReal.comp (Continuous.sub (Continuous.add ?_ continuous_const)
      (WithSetwiseTopology.continuous_apply_real hA'))
    exact (Real.continuous_mul_log_div (ν.real A)).comp
      (WithSetwiseTopology.continuous_apply_real hA')
  by_cases hνA : ν A = 0
  · have : (fun μ : WithLocalConvergence S E ↦
        if ν A = 0 ∧ (μ.toMeasure : Measure (S → E)) A ≠ 0 then ∞ else
          ENNReal.ofReal ((μ.toMeasure : Measure (S → E)).real A
            * log ((μ.toMeasure : Measure (S → E)).real A / ν.real A) + ν.real A
            - (μ.toMeasure : Measure (S → E)).real A))
        = {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) A ≠ 0}.indicator
            fun _ ↦ ∞ := by
      funext μ
      split_ifs with h
      · rw [Set.indicator_of_mem h.2]
      · have hμA : (μ.toMeasure : Measure (S → E)) A = 0 := by
          by_contra hμA
          exact h ⟨hνA, hμA⟩
        rw [Set.indicator_of_notMem (by simpa using hμA)]
        simp [measureReal_def, hμA, hνA]
    rw [this]
    exact (isOpen_ne.preimage (WithSetwiseTopology.continuous_apply_enn hA')).lowerSemicontinuous_indicator
      bot_le
  · simp only [hνA, false_and, ↓reduceIte]
    exact hcont.lowerSemicontinuous

variable (lam : Measure E) [IsProbabilityMeasure lam]

/-- For a finite volume `Λ`, `μ ↦ 𝓗_Λ(μ)` is upper semicontinuous in the topology of local
convergence. -/
theorem upperSemicontinuous_entropyIn (Λ : Finset S) :
    UpperSemicontinuous fun μ : WithLocalConvergence S E ↦
      entropyIn lam (Λ : Set S) (μ.toMeasure : Measure (S → E)) := by
  have hg : Continuous fun x : ℝ≥0∞ ↦ -(x : EReal) :=
    continuous_neg.comp continuous_coe_ennreal_ereal
  exact hg.comp_lowerSemicontinuous_antitone
    (lowerSemicontinuous_relativeEntropyIn (Measure.infinitePi fun _ ↦ lam) Λ)
    fun a b h ↦ EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2 h)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Georgii Proposition (15.14), upper semicontinuity.** The specific entropy `𝓀` is upper
semicontinuous in the topology of local convergence (on all probability measures; Georgii states
it on `𝓟_Θ`). -/
theorem upperSemicontinuous_specificEntropy :
    UpperSemicontinuous fun μ : WithLocalConvergence (ι → ℤ) E ↦
      specificEntropy lam (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine upperSemicontinuous_biInf fun Δ hΔ ↦ ?_
  exact (EReal.continuous_div_natCast hΔ.card_pos.ne').comp_upperSemicontinuous
    (upperSemicontinuous_entropyIn lam Δ) (EReal.monotone_div_right_of_nonneg (Nat.cast_nonneg' _))

end LocalConvergence

end MeasureTheory.GibbsMeasure

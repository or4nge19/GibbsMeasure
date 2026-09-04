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
public import GibbsMeasure.Specification.InvariantDecomposition
public import GibbsMeasure.Topology.ClusterPoints
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
  strictly concave. `isCompact_setOf_le_specificEntropy`: for standard Borel `E` the level sets
  `{𝓀 ≥ c}` are compact in `WithLocalConvergence` (closed by upper semicontinuity, locally
  equicontinuous by the uniform absolute continuity `exists_forall_measure_le_of_klDiv_le` under
  an entropy bound, then Georgii's Proposition (4.9) `exists_tendsto_of_locallyEquicontinuous`).
* `specificEntropy_eq_neg_relativeEntropyIn_lexPast`, **Georgii Proposition (15.16)**: for
  `μ ∈ 𝓟_Θ` and every site `j`, `𝓀(μ) = -𝓗_{V(j)}(μ | μ λ_{j})`, with `V(j) = lexPast j` the
  lexicographic past (15.15) and `μ λ_{j} = μ.bind (isssd λ {j})` the field with the spin at
  `j` resampled from `λ`; `specificEntropy_eq_iInf_finset`: the infimum may be taken over all
  nonempty finite volumes. The two inequalities (15.17) are
  `neg_relativeEntropyIn_lexPast_le_specificEntropy` and
  `specificEntropy_le_neg_relativeEntropyIn_lexPast`, from the telescoping identity
  `relativeEntropyIn_eq_sum_relativeEntropyIn_bind_isssd` and the chain rule for resampling
  `relativeEntropyIn_eq_relativeEntropyIn_bind_isssd_add`.
* `specificEntropy_eq_neg_lintegral_klDiv_withDensity`, **Georgii (15.18)**: if
  `μ = g · μ λ_0` on `𝓕_{V(0)}` (which holds as soon as `𝓀(μ) > -∞`,
  `exists_measurable_trim_eq_withDensity_of_relativeEntropyIn_lexPast_ne_top`), then
  `𝓀(μ) = -μ(𝓗_ℰ(q^· | λ))`, where `q^ω = g(· ω_{S ∖ 0}) λ` is the conditional distribution of
  the spin at `0` given the past: `toReal_lintegral_update_ae_eq_condExp` identifies `q^·(A)`
  with Mathlib's `μ[1_{σ_0 ∈ A} | 𝓕_{V*(0)}]`.
* `specificEntropy_uniformOn_eq_neg_integral_sum_mul_log`, **Georgii (15.19)**: for a finite
  state space and the uniform a priori measure `λ = |E|⁻¹ ∑ δ_x`,
  `𝓀(μ) = -μ(∑_x p_x log p_x) - log |E|` with `p_x = μ(σ_0 = x | 𝓕_{V*(0)})` (Georgii uses
  counting measure, which removes the constant `-log |E| = log λ(E)`); in particular `𝓀(μ)` is
  finite (`specificEntropy_uniformOn_ne_bot`). The ingredients are Shannon's formula
  `klDiv_uniformOn_univ` and Gibbs' inequality `Real.neg_log_card_le_sum_mul_log`.
* **Georgii Theorem (15.20)** for standard Borel `E`:
  `exists_measurable_specificEntropy_eq_neg_lintegral` provides an `𝓘`-measurable
  `h : Ω → [-∞, 0]` with `𝓀(μ) = μ(h)` for all `μ ∈ 𝓟_Θ`, namely
  `h = 𝓀(κ^·)` for a `(𝓟_Θ, 𝓘)`-kernel `κ` from Theorem (14.10)
  (`IsPAKernel.specificEntropy_eq_neg_lintegral`, `IsPAKernel.measurable_specificEntropy_comp`),
  and `specificEntropy_join_eq_neg_lintegral` is the second assertion,
  `𝓀(∫ ν w(dν)) = ∫ 𝓀(ν) w(dν)` for a weight `w` carried by `𝓟_Θ`. Georgii's `h` is moreover
  `𝓣`-measurable, because his kernel of (14.10) is built to be `𝓘 ∩ 𝓣 ∩ 𝓕_{V(0)}`-measurable; the
  kernel `exists_isPAKernel_invariantFields_shiftGroup_int` of `InvariantDecomposition.lean`
  is only exposed as `𝓘`-measurable, so only `𝓘`-measurability of `h` is stated here.

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
`klDiv_trim_le_klDiv_trim_comap`, `klDiv_trim_map_eq_klDiv_trim_comap`,
`klDiv_eq_add_klDiv_trim_of_withDensity`, `smul_klDiv_add_smul_klDiv_le`,
`measurable_klDiv_kernel` (measurability of `a ↦ 𝓗(κ a | η a)` for kernels into a countably
generated space), `exists_forall_measure_le_of_klDiv_le` (uniform absolute continuity under an
entropy bound), `klDiv_eq_sum_singleton` and `klDiv_uniformOn_univ` (the relative entropy on a
finite type; Shannon's formula) (`Mathlib/InformationTheory/KullbackLeibler/`),
`Real.neg_log_card_le_sum_mul_log` (Gibbs' inequality,
`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`), `cylinderEvents_iUnion`,
`EReal.bot_div_natCast` and `Finset.exists_isBox_subset`. In the Georgii section,
`measurePreserving_shift_infinitePi` (`λ^S` is shift invariant) and
`smul_add_smul_mem_invariantFields_shiftGroup` (`𝓟_Θ` is convex) belong in
`Prereqs/Transformation.lean` and `Specification/Ergodicity.lean`; `Model/PeriodicSymmetry.lean`
proves the general `Transformation.measurePreserving_infinitePi` in a leaf file, which this file
cannot import. The lemmas on resampling (`bind_isssd_trim_eq_withDensity`, the chain rule
`relativeEntropyIn_eq_relativeEntropyIn_bind_isssd_add`, the shift equivariance
`bind_isssd_singleton_map_shift`) and the `(P, 𝒜)`-kernel lemmas
`IsPAKernel.setLIntegral_apply_eq`, `IsPAKernel.setLIntegral_lintegral_eq` belong next to
`isssd` in `Specification.lean` and next to `IsPAKernel` in `Specification/Ergodicity.lean`.

Georgii's remark after (15.14), upper semicontinuity of `𝓀` for the weak topology when `E` is
Polish, is not in this file.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Topology
open InformationTheory Real
open scoped ENNReal NNReal Topology symmDiff

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

/-- **Gibbs' inequality** on a finite type: the entropy `-∑ p log p` of a probability vector `p`
is at most `log |α|`, i.e. `-log |α| ≤ ∑ x, p x * log (p x)`. Summing `t - 1 ≤ t log t` at
`t = |α| p x` over `x`, the left-hand sides cancel. -/
theorem Real.neg_log_card_le_sum_mul_log {α : Type*} [Fintype α] [Nonempty α] {p : α → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x = 1) :
    -log (Fintype.card α) ≤ ∑ x, p x * log (p x) := by
  set c : ℝ := (Fintype.card α : ℝ) with hc_def
  have hc : 0 < c := by
    rw [hc_def]
    exact_mod_cast Fintype.card_pos
  have h : ∀ x, (c * p x - 1) / c ≤ p x * log (c * p x) := fun x ↦ by
    have h1 := Real.self_sub_one_le_mul_log (mul_nonneg hc.le (hp0 x))
    rw [div_le_iff₀ hc]
    nlinarith [h1]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ h x
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hp, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, sub_self, zero_div] at hsum
  have heq : ∑ x, p x * log (c * p x) = ∑ x, p x * log (p x) + log c := by
    rw [show ∑ x, p x * log (p x) + log c = ∑ x, (p x * log (p x) + p x * log c) by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : p x = 0
    · simp [hx]
    · rw [log_mul hc.ne' hx]
      ring
  linarith

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
              refine lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hfA.mono h₂
                  le_rfl).aemeasurable
                (hB1.mono h₃ le_rfl).aemeasurable ?_
              rw [IndepFun_iff_Indep]
              exact indep_of_indep_of_le hind (measurable_iff_comap_le.1 hfA)
                (measurable_iff_comap_le.1 hB1)
          _ = (∫⁻ x, A.indicator f x ∂μ) * μ B := by
              rw [lintegral_indicator (h₃ B hB), setLIntegral_const, one_mul]
      rw [hind' hg, hind' (hg'.mono h₁₂ le_rfl), lintegral_indicator (h₁ A hA),
        lintegral_indicator (h₁ A hA), h A hA]
    · rw [trim_measurableSet_eq hle MeasurableSet.univ, trim_measurableSet_eq hle
        MeasurableSet.univ,
        withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
        h _ MeasurableSet.univ]
  intro s hs
  have := congrArg (fun ρ ↦ ρ s) key
  simpa only [trim_measurableSet_eq hle hs, withDensity_apply _ (hle s hs)] using this

end IndepSup


/-- The cylinder σ-algebra of a union is the supremum of the cylinder σ-algebras. -/
lemma cylinderEvents_iUnion {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {κ : Sort*}
    (Δ : κ → Set ι) :
    cylinderEvents (X := X) (⋃ k, Δ k) = ⨆ k, cylinderEvents (X := X) (Δ k) := by
  simp only [cylinderEvents]
  exact iSup_iUnion Δ _

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
      ≤ klDiv (s • μ₁ + t • μ₂) ν + ENNReal.ofReal (-(s * log s)) + ENNReal.ofReal (-(t * log t))
          := by
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
    klDiv_eq_lintegral_klFun_of_ac h₂, ← lintegral_const_mul _ (hm μ₁), ← lintegral_const_mul _
        (hm μ₂),
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


/-- **Invariance of the relative entropy on a sub-σ-algebra under a measurable bijection.** If the
measurable map `f` has a two-sided inverse `g` (automatically measurable from `m` to `f⁻¹ m`), the
relative entropy of the images `f_* μ`, `f_* ν` on `m` is the relative entropy of `μ`, `ν` on the
preimage σ-algebra `f⁻¹ m`. Both inequalities are the data processing inequality `klDiv_map_le`,
for `f` and for `g`. -/
theorem klDiv_trim_map_eq_klDiv_trim_comap {𝓧 : Type*} {m m𝓧 : MeasurableSpace 𝓧}
    {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hm : m ≤ m𝓧) {f g : 𝓧 → 𝓧}
    (hf : Measurable f) (hfg : ∀ x, f (g x) = x) (hgf : ∀ x, g (f x) = x) :
    klDiv ((μ.map f).trim hm) ((ν.map f).trim hm)
      = klDiv (μ.trim (hf.mono le_rfl hm).comap_le) (ν.trim (hf.mono le_rfl hm).comap_le) := by
  have key : ∀ ρ : Measure 𝓧, (ρ.map f).trim hm
      = @Measure.map _ _ (m.comap f) m f (ρ.trim (hf.mono le_rfl hm).comap_le) := by
    intro ρ
    rw [map_trim_comap (hf.mono le_rfl hm), trim_eq_map, Measure.map_map (measurable_id'' hm) hf]
    rfl
  rw [key μ, key ν]
  have hf' : Measurable[m.comap f, m] f := Measurable.of_comap_le le_rfl
  have hg' : Measurable[m, m.comap f] g := by
    rintro _ ⟨t, ht, rfl⟩
    have : g ⁻¹' (f ⁻¹' t) = t := by ext x; simp [hfg]
    rw [this]
    exact ht
  refine le_antisymm (klDiv_map_le _ _ hf') ?_
  have hback : ∀ ρ : @Measure 𝓧 (m.comap f),
      @Measure.map _ _ m (m.comap f) g (@Measure.map _ _ (m.comap f) m f ρ) = ρ := by
    intro ρ
    rw [@Measure.map_map _ _ _ (m.comap f) m (m.comap f) _ _ _ hg' hf']
    have : g ∘ f = id := funext hgf
    rw [this, Measure.map_id]
  calc klDiv (μ.trim (hf.mono le_rfl hm).comap_le) (ν.trim (hf.mono le_rfl hm).comap_le)
      = klDiv (@Measure.map _ _ m (m.comap f) g
            (@Measure.map _ _ (m.comap f) m f (μ.trim (hf.mono le_rfl hm).comap_le)))
          (@Measure.map _ _ m (m.comap f) g
            (@Measure.map _ _ (m.comap f) m f (ν.trim (hf.mono le_rfl hm).comap_le))) := by
        rw [hback, hback]
    _ ≤ _ := klDiv_map_le _ _ hg'


/-- **Measurability of `a ↦ 𝓗(κ a | η a)`** for finite kernels into a countably generated space:
on `{κ a ≪ η a}` it is the integral of `klFun` of the jointly measurable kernel Radon–Nikodym
derivative, and `∞` elsewhere. -/
theorem measurable_klDiv_kernel {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    [MeasurableSpace.CountablyGenerated γ] (κ η : Kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    Measurable fun a ↦ klDiv (κ a) (η a) := by
  classical
  have hf : Measurable fun a ↦ ∫⁻ x, ENNReal.ofReal (klFun (κ.rnDeriv η a x).toReal) ∂(η a) :=
    Measurable.lintegral_kernel_prod_right' (κ := η)
      (f := fun p : α × γ ↦ ENNReal.ofReal (klFun (κ.rnDeriv η p.1 p.2).toReal))
      (ENNReal.measurable_ofReal.comp (measurable_klFun.comp
        (ENNReal.measurable_toReal.comp (Kernel.measurable_rnDeriv κ η))))
  have heq : (fun a ↦ klDiv (κ a) (η a)) = fun a ↦
      if κ a ≪ η a then ∫⁻ x, ENNReal.ofReal (klFun (κ.rnDeriv η a x).toReal) ∂(η a) else ∞ := by
    funext a
    split_ifs with h
    · rw [klDiv_eq_lintegral_klFun_of_ac h]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with x hx
      rw [hx]
    · exact klDiv_of_not_ac h
  rw [heq]
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous κ η) hf measurable_const


/-- **Uniform absolute continuity from an entropy bound** (Georgii, Step 3 in the proof of
Proposition (15.14)): for every bound `b < ∞` and `ε > 0` there is `δ > 0` such that every
probability measure `μ` with `𝓗(μ | ν) ≤ b` satisfies `μ A ≤ ε` on every measurable `A` with
`ν A ≤ δ`. With `f = dμ/dν` and a threshold `C`,
`μ A ≤ C ν A + ∫_{f > C} f dν` and `∫_{f > C} f dν ≤ (𝓗(μ | ν) + 1) / log C`. -/
theorem exists_forall_measure_le_of_klDiv_le {α : Type*} {mα : MeasurableSpace α} {b : ℝ≥0∞}
    (hb : b ≠ ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ (μ ν : Measure α) [IsProbabilityMeasure μ] [IsFiniteMeasure ν],
      klDiv μ ν ≤ b → ∀ ⦃A : Set α⦄, MeasurableSet A → ν A ≤ δ → μ A ≤ ε := by
  by_cases hεtop : ε = ∞
  · exact ⟨1, one_pos, fun μ ν _ _ _ A _ _ ↦ by rw [hεtop]; exact le_top⟩
  set e : ℝ := ε.toReal with he
  have he0 : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  set C : ℝ := Real.exp (2 * (b.toReal + 1) / e) with hC
  have hC1 : 1 < C := by
    rw [hC, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by positivity)
  have hlogC : Real.log C = 2 * (b.toReal + 1) / e := by rw [hC, Real.log_exp]
  have hlogC0 : 0 < Real.log C := by rw [hlogC]; positivity
  refine ⟨ENNReal.ofReal (e / (2 * C)), ENNReal.ofReal_pos.2 (by positivity), ?_⟩
  intro μ ν _ _ hkl A hA hνA
  have hac : μ ≪ ν := by
    by_contra h
    rw [klDiv_of_not_ac h] at hkl
    exact hb (top_le_iff.1 hkl)
  set f := μ.rnDeriv ν with hf
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  set T : Set α := {x | ENNReal.ofReal C < f x} with hT
  have hTm : MeasurableSet T := measurableSet_lt measurable_const hfm
  -- pointwise, `f ≤ C + f 1_{f > C}`
  have hpt : ∀ x, f x ≤ ENNReal.ofReal C + T.indicator f x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]
      exact le_add_self
    · rw [Set.indicator_of_notMem hx, add_zero]
      exact not_lt.1 hx
  -- on `{f > C}`, `log C · f ≤ ψ(f) + f`
  have hkey : ∀ x, f x ≠ ∞ → ENNReal.ofReal (Real.log C) * T.indicator f x
      ≤ ENNReal.ofReal (klFun (f x).toReal) + T.indicator f x := by
    intro x hx
    by_cases hxT : x ∈ T
    · rw [Set.indicator_of_mem hxT]
      have hCx : C < (f x).toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hx).1 hxT
      have hx0 : 0 < (f x).toReal := by linarith
      have hreal : Real.log C * (f x).toReal ≤ klFun (f x).toReal + (f x).toReal := by
        rw [klFun_apply]
        have h1 := Real.log_le_log (by linarith) hCx.le
        nlinarith [mul_le_mul_of_nonneg_left h1 hx0.le]
      calc ENNReal.ofReal (Real.log C) * f x
          = ENNReal.ofReal (Real.log C * (f x).toReal) := by
            rw [ENNReal.ofReal_mul hlogC0.le, ENNReal.ofReal_toReal hx]
        _ ≤ ENNReal.ofReal (klFun (f x).toReal + (f x).toReal) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (klFun (f x).toReal) + f x := by
            rw [ENNReal.ofReal_add (klFun_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg,
              ENNReal.ofReal_toReal hx]
    · rw [Set.indicator_of_notMem hxT, mul_zero]
      exact zero_le
  have hTint : ∫⁻ x, T.indicator f x ∂ν ≤ ENNReal.ofReal (e / 2) := by
    have h1 : (∫⁻ x, T.indicator f x ∂ν) * ENNReal.ofReal (Real.log C) ≤ b + 1 := by
      rw [mul_comm, ← lintegral_const_mul _ (hfm.indicator hTm)]
      calc ∫⁻ x, ENNReal.ofReal (Real.log C) * T.indicator f x ∂ν
          ≤ ∫⁻ x, ENNReal.ofReal (klFun (f x).toReal) + T.indicator f x ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx using hkey x hx
        _ = klDiv μ ν + ∫⁻ x, T.indicator f x ∂ν := by
            rw [lintegral_add_left (f := fun x ↦ ENNReal.ofReal (klFun (f x).toReal))
              (by fun_prop), klDiv_eq_lintegral_klFun_of_ac hac]
        _ ≤ b + 1 := by
            refine add_le_add hkl ?_
            rw [lintegral_indicator hTm, Measure.setLIntegral_rnDeriv hac]
            exact prob_le_one
    have hlog : ENNReal.ofReal (Real.log C) ≠ 0 := (ENNReal.ofReal_pos.2 hlogC0).ne'
    rw [← ENNReal.le_div_iff_mul_le (Or.inl hlog) (Or.inl ENNReal.ofReal_ne_top)] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ← ENNReal.ofReal_div_of_pos hlogC0,
      hlogC]
    congr 1
    field_simp
  calc μ A = ∫⁻ x in A, f x ∂ν := (Measure.setLIntegral_rnDeriv hac A).symm
    _ ≤ ∫⁻ x in A, ENNReal.ofReal C + T.indicator f x ∂ν := lintegral_mono hpt
    _ = ENNReal.ofReal C * ν A + ∫⁻ x in A, T.indicator f x ∂ν := by
        rw [lintegral_add_left measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (e / (2 * C)) + ENNReal.ofReal (e / 2) := by
        gcongr
        exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans hTint
    _ = ε := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        have : C * (e / (2 * C)) + e / 2 = e := by field_simp; ring
        rw [this, he, ENNReal.ofReal_toReal hεtop]

/-- **The relative entropy on a finite type** with measurable singletons is Georgii's sum
`∑_x μ{x} log (μ{x} / ν{x})` (in Mathlib's normalisation, with the correction
`ν{x} - μ{x}` per point), provided `ν{x} = 0 → μ{x} = 0` for all `x`; otherwise it is `∞`
(`klDiv_eq_top_of_measure_eq_zero`). -/
theorem klDiv_eq_sum_singleton {α : Type*} [Fintype α] {mα : MeasurableSpace α}
    [MeasurableSingletonClass α] {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hac : ∀ x, ν {x} = 0 → μ {x} = 0) :
    klDiv μ ν = ∑ x, ENNReal.ofReal
      (μ.real {x} * log (μ.real {x} / ν.real {x}) + ν.real {x} - μ.real {x}) := by
  classical
  set P : Finset (Set α) := Finset.univ.image fun x ↦ ({x} : Set α) with hP
  have hmemP : ∀ A, A ∈ P ↔ ∃ x, A = {x} := fun A ↦ by
    simp only [hP, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]
  have hP_disj : (P : Set (Set α)).PairwiseDisjoint id := by
    intro A hA B hB hAB
    obtain ⟨x, rfl⟩ := (hmemP A).1 hA
    obtain ⟨y, rfl⟩ := (hmemP B).1 hB
    exact Set.disjoint_singleton.2 fun h ↦ hAB (h ▸ rfl)
  have hP_cover : ⋃₀ (P : Set (Set α)) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_sUnion.2 ⟨{x}, (hmemP _).2 ⟨x, rfl⟩, rfl⟩
  have hP_meas : ∀ A ∈ P, MeasurableSet A := fun A hA ↦ by
    obtain ⟨x, rfl⟩ := (hmemP A).1 hA
    exact measurableSet_singleton x
  have hgen : MeasurableSpace.generateFrom (P : Set (Set α)) = mα := by
    refine le_antisymm (MeasurableSpace.generateFrom_le hP_meas) fun s _ ↦ ?_
    rw [← Set.biUnion_of_singleton s]
    exact MeasurableSet.biUnion s.to_countable fun x _ ↦
      MeasurableSpace.measurableSet_generateFrom ((hmemP _).2 ⟨x, rfl⟩)
  have h := klDiv_trim_generateFrom_eq_sum (μ := μ) (ν := ν) hP_disj hP_cover hP_meas
    fun A hA ↦ by obtain ⟨x, rfl⟩ := (hmemP A).1 hA; exact hac x
  rw [klDiv_trim_congr hgen _ le_rfl, trim_eq_self, trim_eq_self] at h
  rw [h, hP, Finset.sum_image fun x _ y _ hxy ↦ Set.singleton_injective hxy]

/-- **Shannon's formula.** The relative entropy of a probability measure `μ` on a finite type
with respect to the uniform distribution is `∑_x μ{x} log μ{x} + log |α|`, the difference
between the maximal entropy `log |α|` and the entropy `-∑_x μ{x} log μ{x}` of `μ`. -/
theorem klDiv_uniformOn_univ {α : Type*} [Fintype α] [Nonempty α] {mα : MeasurableSpace α}
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] :
    klDiv μ (uniformOn Set.univ)
      = ENNReal.ofReal (∑ x, μ.real {x} * log (μ.real {x}) + log (Fintype.card α)) := by
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hν : ∀ x, (uniformOn (Set.univ : Set α)).real {x} = 1 / Fintype.card α := fun x ↦ by
    rw [measureReal_def, uniformOn_univ, Measure.count_singleton, ENNReal.toReal_div,
      ENNReal.toReal_one, ENNReal.toReal_natCast]
  have hterm : ∀ x, μ.real {x} * log (μ.real {x} / (1 / Fintype.card α)) + 1 / Fintype.card α
      - μ.real {x} = μ.real {x} * log (μ.real {x}) + μ.real {x} * log (Fintype.card α)
        + 1 / Fintype.card α - μ.real {x} := fun x ↦ by
    by_cases hx : μ.real {x} = 0
    · simp [hx]
    · rw [div_div_eq_mul_div, div_one, log_mul hx hcard.ne', mul_add]
  have hnn : ∀ x, 0 ≤ μ.real {x} * log (μ.real {x} / (1 / Fintype.card α)) + 1 / Fintype.card α
      - μ.real {x} := fun x ↦ by
    have : klFun (μ.real {x} / (1 / Fintype.card α)) * (1 / Fintype.card α)
        = μ.real {x} * log (μ.real {x} / (1 / Fintype.card α)) + 1 / Fintype.card α
          - μ.real {x} := by
      rw [klFun_apply]
      field_simp
    rw [← this]
    exact mul_nonneg (klFun_nonneg (div_nonneg measureReal_nonneg (by positivity)))
      (by positivity)
  rw [klDiv_eq_sum_singleton fun x h ↦ absurd h (by
      rw [uniformOn_univ, Measure.count_singleton]
      exact (ENNReal.div_pos one_ne_zero (ENNReal.natCast_ne_top _)).ne')]
  simp_rw [hν]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hnn x]
  congr 1
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_measureReal_singleton, Finset.coe_univ, probReal_univ, one_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard.ne']
  ring

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
  have hΛ_le : cylinderEvents (X := fun _ : S ↦ E) Λ ≤ cylinderEvents (X := fun _ : S ↦ E) (Λ ∪
      Δ) :=
    cylinderEvents_mono Set.subset_union_left
  have hΔ_le : cylinderEvents (X := fun _ : S ↦ E) Δ ≤ cylinderEvents (X := fun _ : S ↦ E) (Λ ∪
      Δ) :=
    cylinderEvents_mono Set.subset_union_right
  have hI_le : cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ≤ cylinderEvents (X := fun _ : S ↦ E)
      Λ :=
    cylinderEvents_mono Set.inter_subset_left
  have hI_leΔ : cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ≤ cylinderEvents (X := fun _ : S ↦ E)
      Δ :=
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
        = cylinderEvents (X := fun _ : S ↦ E) (Λ ∩ Δ) ⊔ cylinderEvents (X := fun _ : S ↦ E) (Δ \
            Λ) := by
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
  calc klDiv (μ.trim hΛ) (γ.trim hΛ) + (klDiv (μ.trim hΔ) (ν.trim hΔ) + klDiv (μ.trim hI) (γ.trim
      hI))
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
  have h := klDiv_smul_add_smul_le (μ₁ := μ₁.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ
      := Λ)))
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
  have h := smul_klDiv_add_smul_klDiv_le (μ₁ := μ₁.trim (cylinderEvents_le_pi (X := fun _ : S ↦
      E) (Δ := Λ)))
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
      ≤ ((s : ℝ) : EReal) * specificEntropy lam μ₁ + ((t : ℝ) : EReal) * specificEntropy lam μ₂
          := by
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
  have hc : Tendsto (fun N : ℕ ↦ (c : EReal) / (#(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) :
      EReal))
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
      EReal.continuousAt_mul (Or.inl (EReal.coe_ne_zero.2 ha.ne')) (Or.inl (EReal.coe_ne_zero.2
          ha.ne'))
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
          (((s : ℝ) : EReal) * specificEntropy lam μ₁, ((t : ℝ) : EReal) * specificEntropy lam
              μ₂) :=
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
    exact (isOpen_ne.preimage (WithSetwiseTopology.continuous_apply_enn
        hA')).lowerSemicontinuous_indicator
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


/-! ### Resampling a finite volume from the a priori measure -/

section Resampling

variable {S E : Type*} [MeasurableSpace E] (lam : Measure E) [IsProbabilityMeasure lam]
  {μ : Measure (S → E)}

/-- The resampled measure `μ λ_Δ` agrees with `μ` on `𝓕_{Δᶜ}` (properness of `λ_Δ`). -/
lemma bind_isssd_apply_of_measurableSet_cylinderEvents_compl (Δ : Finset S) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Set S)ᶜ)] A) :
    μ.bind (Specification.isssd lam Δ) A = μ A := by
  rw [Measure.bind_apply (cylinderEvents_le_pi _ hA)
    (Specification.measurable_isssd_coe Δ).aemeasurable]
  have h : ∀ ω, Specification.isssd lam Δ ω A = A.indicator 1 ω := fun ω ↦ by
    rw [((Specification.isssd lam).isProper Δ).apply_eq_indicator_mul_univ cylinderEvents_le_pi hA
      ω, measure_univ, mul_one]
  simp_rw [h]
  exact lintegral_indicator_one (cylinderEvents_le_pi _ hA)

/-- `μ λ_Δ = μ` on `𝓕_Λ` when `Λ` is disjoint from `Δ`. -/
lemma bind_isssd_trim_eq_of_disjoint (Δ : Finset S) {Λ : Set S} (h : Disjoint Λ (Δ : Set S)) :
    (μ.bind (Specification.isssd lam Δ)).trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ))
      = μ.trim cylinderEvents_le_pi :=
  @Measure.ext _ (cylinderEvents Λ) _ _ fun A hA ↦ by
    rw [trim_measurableSet_eq _ hA, trim_measurableSet_eq _ hA]
    exact bind_isssd_apply_of_measurableSet_cylinderEvents_compl lam Δ
      (cylinderEvents_mono h.subset_compl_right _ hA)

/-- For `A ∈ 𝓕_Λ`, the resampling probability `ω ↦ λ_Δ(A | ω)` depends only on the coordinates in
`Λ ∖ Δ`. -/
lemma measurable_isssd_apply_of_measurableSet_cylinderEvents (Δ : Finset S) {Λ : Set S}
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Λ] A) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ)]
      fun ω ↦ Specification.isssd lam Δ ω A := by
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  refine measurable_cylinderEvents_iff_dependsOn.2
    ⟨((Specification.isssd lam Δ).measurable_coe hA').mono cylinderEvents_le_pi le_rfl, ?_⟩
  intro ω ω' hωω'
  change Measure.map (juxt (Δ : Set S) ω) (Measure.pi fun _ : Δ ↦ lam) A
    = Measure.map (juxt (Δ : Set S) ω') (Measure.pi fun _ : Δ ↦ lam) A
  rw [Measure.map_apply Measurable.juxt hA', Measure.map_apply Measurable.juxt hA']
  congr 1
  ext ζ
  simp only [Set.mem_preimage]
  refine mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ ?_
  by_cases hiΔ : i ∈ Δ
  · rw [juxt_apply_of_mem (by simpa using hiΔ), juxt_apply_of_mem (by simpa using hiΔ)]
  · rw [juxt_apply_of_not_mem (by simpa using hiΔ), juxt_apply_of_not_mem (by simpa using hiΔ)]
    exact hωω' i ⟨hi, hiΔ⟩

/-- **The resampled measure through a density.** If `μ = g λ^S` on `𝓕_{Λ ∖ Δ}` with `g`
`𝓕_{Λ ∖ Δ}`-measurable, then `μ λ_Δ = g λ^S` on `𝓕_Λ`: resampling `Δ` from `λ` and then
restricting to `𝓕_Λ` only sees the law of the coordinates in `Λ ∖ Δ`. -/
lemma bind_isssd_trim_eq_withDensity (Δ : Finset S) {Λ : Set S} {g : (S → E) → ℝ≥0∞}
    (hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ)] g)
    (hμ : μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ \ Δ))
      = ((Measure.infinitePi fun _ : S ↦ lam).trim cylinderEvents_le_pi).withDensity g) :
    (μ.bind (Specification.isssd lam Δ)).trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ))
      = ((Measure.infinitePi fun _ : S ↦ lam).trim cylinderEvents_le_pi).withDensity g := by
  set γ : Measure (S → E) := Measure.infinitePi fun _ : S ↦ lam with hγ
  have hΛ : cylinderEvents (X := fun _ : S ↦ E) Λ ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hΛΔ : cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hle : cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ) ≤ cylinderEvents Λ :=
    cylinderEvents_mono Set.sdiff_subset
  have hg' : Measurable g := hg.mono hΛΔ le_rfl
  have hgdep : DependsOn g (Λ \ Δ) := (measurable_cylinderEvents_iff_dependsOn.1 hg).2
  refine @Measure.ext _ (cylinderEvents Λ) _ _ fun A hA ↦ ?_
  have hA' : MeasurableSet A := hΛ _ hA
  set φ : (S → E) → ℝ≥0∞ := fun ω ↦ Specification.isssd lam Δ ω A with hφ_def
  have hφ : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ)] φ :=
    measurable_isssd_apply_of_measurableSet_cylinderEvents lam Δ hA
  have hgj : ∀ ω (ζ : Δ → E), g (juxt (Δ : Set S) ω ζ) = g ω := fun ω ζ ↦
    hgdep fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi.2) ζ
  calc (μ.bind (Specification.isssd lam Δ)).trim hΛ A
      = ∫⁻ ω, φ ω ∂μ := by
        rw [trim_measurableSet_eq hΛ hA,
          Measure.bind_apply hA' (Specification.measurable_isssd_coe Δ).aemeasurable]
    _ = ∫⁻ ω, φ ω ∂(μ.trim hΛΔ) := (lintegral_trim hΛΔ hφ).symm
    _ = ∫⁻ ω, g ω * φ ω ∂γ := by
        rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hg hφ, lintegral_trim hΛΔ (hg.mul hφ)]
        rfl
    _ = ∫⁻ ω, ∫⁻ σ, A.indicator g σ ∂(Specification.isssd lam Δ ω) ∂γ := by
        refine lintegral_congr fun ω ↦ ?_
        rw [Specification.lintegral_isssd_eq Δ ω (hg'.indicator hA')]
        change g ω * Measure.map (juxt (Δ : Set S) ω) (Measure.pi fun _ : Δ ↦ lam) A = _
        rw [Measure.map_apply Measurable.juxt hA', ← lintegral_indicator_one (Measurable.juxt hA'),
          ← lintegral_const_mul _ (measurable_one.indicator (Measurable.juxt hA'))]
        refine lintegral_congr fun ζ ↦ ?_
        by_cases hζ : juxt (Δ : Set S) ω ζ ∈ A <;> simp [Set.indicator, hζ, hgj ω ζ]
    _ = ∫⁻ σ, A.indicator g σ ∂(γ.bind (Specification.isssd lam Δ)) :=
        (Measure.lintegral_bind (Specification.measurable_isssd_coe Δ).aemeasurable
          (hg'.indicator hA').aemeasurable).symm
    _ = ∫⁻ σ in A, g σ ∂γ := by
        rw [hγ, Specification.infinitePi_bind_isssd, lintegral_indicator hA']
    _ = (γ.trim hΛ).withDensity g A := by
        rw [withDensity_apply _ hA, restrict_trim hΛ γ hA, lintegral_trim hΛ (hg.mono hle le_rfl)]

/-- **The chain rule for resampling** (Georgii, in the proofs of (15.10) and (15.16)): for any
set of sites `Λ` and finite `Δ`,
`𝓗_Λ(μ | λ^S) = 𝓗_Λ(μ | μ λ_Δ) + 𝓗_{Λ ∖ Δ}(μ | λ^S)`, in `[0, ∞]`. -/
theorem relativeEntropyIn_eq_relativeEntropyIn_bind_isssd_add [IsProbabilityMeasure μ]
    (Λ : Set S) (Δ : Finset S) :
    relativeEntropyIn Λ μ (Measure.infinitePi fun _ : S ↦ lam)
      = relativeEntropyIn Λ μ (μ.bind (Specification.isssd lam Δ))
        + relativeEntropyIn (Λ \ Δ) μ (Measure.infinitePi fun _ : S ↦ lam) := by
  set γ : Measure (S → E) := Measure.infinitePi fun _ : S ↦ lam with hγ
  have hΛ : cylinderEvents (X := fun _ : S ↦ E) Λ ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hΛΔ : cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hle : cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ) ≤ cylinderEvents Λ :=
    cylinderEvents_mono Set.sdiff_subset
  by_cases hac : μ.trim hΛΔ ≪ γ.trim hΛΔ
  swap
  · have h1 : relativeEntropyIn (Λ \ Δ) μ γ = ∞ := klDiv_of_not_ac hac
    have h2 : relativeEntropyIn Λ μ γ = ∞ :=
      top_le_iff.1 (h1 ▸ relativeEntropyIn_mono (μ := μ) (ν := γ) Set.sdiff_subset)
    rw [h1, h2, add_top]
  set g := (μ.trim hΛΔ).rnDeriv (γ.trim hΛΔ) with hg_def
  have hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ \ Δ)] g :=
    Measure.measurable_rnDeriv _ _
  have hμg : μ.trim hΛΔ = (γ.trim hΛΔ).withDensity g :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  set ν := μ.bind (Specification.isssd lam Δ) with hν
  have hνΛ : ν.trim hΛ = (γ.trim hΛ).withDensity g :=
    bind_isssd_trim_eq_withDensity lam Δ hg hμg
  have hμν : (μ.trim hΛ).trim hle = (ν.trim hΛ).trim hle := by
    rw [trim_trim, trim_trim, hν, bind_isssd_trim_eq_of_disjoint lam Δ Set.disjoint_sdiff_left]
  have := klDiv_eq_add_klDiv_trim_of_withDensity hle (μ := μ.trim hΛ) (ν := ν.trim hΛ)
    (lam := γ.trim hΛ) hg hνΛ hμν
  rwa [trim_trim, trim_trim] at this

end Resampling

/-! ### Shift equivariance of resampling -/

section Shift

variable {S E : Type*} [MeasurableSpace E] (lam : Measure E) [IsProbabilityMeasure lam]
  {μ : Measure (S → E)} [AddCommGroup S]

/-- The shift `θ_k` maps `μ λ_{j}` to `(θ_k μ) λ_{j + k}`, Georgii (5.6)(a) for a single site. -/
lemma bind_isssd_singleton_map_shift (j k : S) :
    (μ.bind (Specification.isssd lam {j})).map (shift E k).toFun
      = (μ.map (shift E k).toFun).bind (Specification.isssd lam {j + k}) := by
  rw [Measure.map_bind (Specification.measurable_isssd_coe _) (shift E k).measurable_toFun,
    Measure.bind_map (shift E k).measurable_toFun (Specification.measurable_isssd_coe _)]
  congr 1
  funext ω
  have h := Specification.isssdFun_map_toFun lam (shift E k) (fun _ ↦ MeasurePreserving.id lam)
    {j + k} ((shift E k).toFun ω)
  rw [Transformation.inv_toFun_toFun] at h
  have hmap : Finset.map (shift E k).sites.symm.toEmbedding {j + k} = {j} := by
    rw [Finset.map_singleton]
    simp [shift, Equiv.addRight_symm]
  rw [hmap] at h
  exact h

/-- **Shift invariance of the relative entropy with respect to a resampled measure**: for
shift-invariant `μ`, `𝓗_Λ(μ | μ λ_{j + k}) = 𝓗_{Λ - k}(μ | μ λ_j)`. -/
lemma relativeEntropyIn_bind_isssd_singleton_eq_image_sub [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Set S) (j k : S) :
    relativeEntropyIn Λ μ (μ.bind (Specification.isssd lam {j + k}))
      = relativeEntropyIn ((· - k) '' Λ) μ (μ.bind (Specification.isssd lam {j})) := by
  have h := klDiv_trim_map_eq_klDiv_trim_comap (μ := μ)
    (ν := μ.bind (Specification.isssd lam {j}))
    (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := Λ)) (shift E k).measurable_toFun
    (g := (shift E (-k)).toFun) (fun x ↦ by funext i; simp) (fun x ↦ by funext i; simp)
  rw [(hμ k).map_eq, bind_isssd_singleton_map_shift, (hμ k).map_eq] at h
  exact h.trans (klDiv_trim_congr (cylinderEvents_comap_shift k Λ) _ _)

end Shift

/-! ### The lexicographic past (Georgii (15.15)) -/

section LexPast

variable {ι : Type*} [LinearOrder ι]

/-- **Georgii (15.15).** The *lexicographic past* `V(j) = {i ∈ ℤ^d : i ≤ j}` of a site `j`, for
the lexicographic order on `ℤ^d = ι → ℤ` induced by the linear order of the coordinates `ι`. -/
def lexPast (j : ι → ℤ) : Set (ι → ℤ) := {i | toLex i ≤ toLex j}

lemma mem_lexPast {i j : ι → ℤ} : i ∈ lexPast j ↔ toLex i ≤ toLex j := Iff.rfl

lemma self_mem_lexPast (j : ι → ℤ) : j ∈ lexPast j := mem_lexPast.2 le_rfl

/-- The lexicographic order is translation invariant: `V(j) - k = V(j - k)`. -/
lemma image_sub_lexPast (j k : ι → ℤ) : (· - k) '' lexPast j = lexPast (j - k) := by
  ext i
  simp only [Set.mem_image, mem_lexPast]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sub_le_sub_right hx (toLex k)
  · intro hi
    refine ⟨i + k, ?_, by simp⟩
    calc toLex (i + k) = toLex i + toLex k := rfl
      _ ≤ toLex (j - k) + toLex k := add_le_add hi le_rfl
      _ = toLex j := sub_add_cancel (toLex j) (toLex k)

/-- `V(j) ∖ {j}` is the strict lexicographic past `V*(j)`. -/
lemma lexPast_diff_singleton (j : ι → ℤ) : lexPast j \ {j} = {i | toLex i < toLex j} := by
  ext i
  change i ∈ lexPast j ∧ i ∉ ({j} : Set (ι → ℤ)) ↔ toLex i < toLex j
  rw [Set.mem_singleton_iff, mem_lexPast]
  constructor
  · rintro ⟨h1, h2⟩
    exact lt_of_le_of_ne h1 (toLex.injective.ne h2)
  · intro h
    exact ⟨le_of_lt h, fun hij ↦ ne_of_lt h (congrArg toLex hij)⟩

end LexPast

/-! ### The specific entropy as a conditional entropy given the past (Georgii (15.16)) -/

section Lexicographic

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace E] (lam : Measure E)
  [IsProbabilityMeasure lam] {μ : Measure ((ι → ℤ) → E)}

/-- **The telescoping identity** (Georgii, in the proofs of (15.10) and (15.16)): enumerating a
finite volume `Λ` in lexicographic order, `𝓗_Λ(μ | λ^S) = ∑_{i ∈ Λ} 𝓗_{(Λ - i) ∩ V(0)}(μ | μ λ_0)`
for shift-invariant `μ`. -/
theorem relativeEntropyIn_eq_sum_relativeEntropyIn_bind_isssd [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Finset (ι → ℤ)) :
    relativeEntropyIn (Λ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam)
      = ∑ i ∈ Λ, relativeEntropyIn ((· - i) '' ((Λ : Set (ι → ℤ)) ∩ lexPast i)) μ
          (μ.bind (Specification.isssd lam {0})) := by
  classical
  refine Finset.induction_on_max_value toLex Λ (by simp) fun a s has hle ih ↦ ?_
  · rw [Finset.sum_insert has]
    have h1 := relativeEntropyIn_eq_relativeEntropyIn_bind_isssd_add lam (μ := μ)
      ((insert a s : Finset (ι → ℤ)) : Set (ι → ℤ)) {a}
    have h2 : ((insert a s : Finset (ι → ℤ)) : Set (ι → ℤ))
        \ (({a} : Finset (ι → ℤ)) : Set (ι → ℤ)) = (s : Set (ι → ℤ)) := by
      ext x
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, Set.mem_insert_iff,
        Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, h'⟩
        · exact absurd h h'
        · exact h
      · intro h
        exact ⟨Or.inr h, fun h' ↦ has (h' ▸ h)⟩
    rw [h2] at h1
    rw [h1, ih]
    congr 1
    · have := relativeEntropyIn_bind_isssd_singleton_eq_image_sub lam hμ
        ((insert a s : Finset (ι → ℤ)) : Set (ι → ℤ)) 0 a
      rw [zero_add] at this
      rw [this]
      congr 2
      refine (Set.inter_eq_left.2 ?_).symm
      intro x hx
      rw [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact self_mem_lexPast _
      · exact hle x hx
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      congr 2
      ext x
      constructor
      · rintro ⟨hx, hxi⟩
        exact ⟨Finset.mem_coe.2 (Finset.mem_insert_of_mem hx), hxi⟩
      · rintro ⟨hx, hxi⟩
        rw [Finset.mem_coe, Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact absurd (toLex.injective (le_antisymm (mem_lexPast.1 hxi) (hle i hi)) ▸ hi) has
        · exact ⟨hx, hxi⟩

/-- **Georgii (15.17), first inequality, finite-volume form**: for shift-invariant `μ` and finite
`Λ`, `𝓗_Λ(μ | λ^S) ≤ |Λ| 𝓗_{V(0)}(μ | μ λ_0)`. -/
theorem relativeEntropyIn_le_card_mul_relativeEntropyIn_lexPast [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Finset (ι → ℤ)) :
    relativeEntropyIn (Λ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam)
      ≤ #Λ * relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) := by
  rw [relativeEntropyIn_eq_sum_relativeEntropyIn_bind_isssd lam hμ Λ, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ relativeEntropyIn_mono ?_
  rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
  calc toLex (x - i) = toLex x - toLex i := rfl
    _ ≤ toLex i - toLex i := sub_le_sub_right (mem_lexPast.1 hx) (toLex i)
    _ = toLex 0 := sub_self (toLex i)

/-- **Georgii (15.17), second inequality, finite-volume form**: for shift-invariant `μ`, a
finite volume `Λ` and a finite `Δ ⊆ V(0)`,
`|{i ∈ Λ : Δ + i ⊆ Λ}| 𝓗_Δ(μ | μ λ_0) ≤ 𝓗_Λ(μ | λ^S)`. -/
theorem card_mul_relativeEntropyIn_le_relativeEntropyIn [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ Δ : Finset (ι → ℤ))
    (hΔ : (Δ : Set (ι → ℤ)) ⊆ lexPast 0) :
    #{i ∈ Λ | ∀ d ∈ Δ, d + i ∈ Λ}
        * relativeEntropyIn (Δ : Set (ι → ℤ)) μ (μ.bind (Specification.isssd lam {0}))
      ≤ relativeEntropyIn (Λ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam) := by
  rw [relativeEntropyIn_eq_sum_relativeEntropyIn_bind_isssd lam hμ Λ, ← nsmul_eq_mul]
  calc #{i ∈ Λ | ∀ d ∈ Δ, d + i ∈ Λ}
        • relativeEntropyIn (Δ : Set (ι → ℤ)) μ (μ.bind (Specification.isssd lam {0}))
      ≤ ∑ i ∈ {i ∈ Λ | ∀ d ∈ Δ, d + i ∈ Λ},
          relativeEntropyIn ((· - i) '' ((Λ : Set (ι → ℤ)) ∩ lexPast i)) μ
            (μ.bind (Specification.isssd lam {0})) := by
        refine Finset.card_nsmul_le_sum _ _ _ fun i hi ↦ relativeEntropyIn_mono ?_
        rw [Finset.mem_filter] at hi
        intro d hd
        refine ⟨d + i, ⟨hi.2 d hd, ?_⟩, by simp⟩
        calc toLex (d + i) = toLex d + toLex i := rfl
          _ ≤ toLex 0 + toLex i := add_le_add (mem_lexPast.1 (hΔ hd)) le_rfl
          _ = toLex i := zero_add (toLex i)
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- `-(x / n)` for `x ∈ [0, ∞)` and `n ∈ ℕ`, in `EReal`. -/
lemma neg_coe_ennreal_div_natCast {x : ℝ≥0∞} (hx : x ≠ ∞) (n : ℕ) :
    -(x : EReal) / (n : EReal) = ((-(x.toReal / n) : ℝ) : EReal) := by
  rw [← EReal.coe_ennreal_toReal hx, ← EReal.coe_neg, ← EReal.coe_natCast, ← EReal.coe_div,
    neg_div]

lemma _root_.EReal.bot_div_natCast {n : ℕ} (hn : n ≠ 0) : (⊥ : EReal) / (n : EReal) = ⊥ := by
  rw [div_eq_mul_inv, ← EReal.coe_natCast, ← EReal.coe_inv]
  exact EReal.bot_mul_of_pos (EReal.coe_pos.2 (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))))

/-- **Georgii (15.17), first inequality**: for shift-invariant `μ` and every nonempty finite
`Δ`, `-𝓗_{V(0)}(μ | μ λ_0) ≤ |Δ|⁻¹ 𝓗_Δ(μ)`. -/
theorem neg_relativeEntropyIn_lexPast_le_entropyIn_div_card [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) {Δ : Finset (ι → ℤ)} (hΔ : Δ.Nonempty) :
    -(relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) : EReal)
      ≤ entropyIn lam (Δ : Set (ι → ℤ)) μ / (#Δ : EReal) := by
  set K := relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) with hK_def
  have hΔK := relativeEntropyIn_le_card_mul_relativeEntropyIn_lexPast lam hμ Δ
  by_cases hK : K = ∞
  · rw [hK, EReal.coe_ennreal_top, EReal.neg_top]
    exact bot_le
  have hH : relativeEntropyIn (Δ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hK) hΔK
  rw [entropyIn, neg_coe_ennreal_div_natCast hH, ← EReal.coe_ennreal_toReal hK, ← EReal.coe_neg,
    EReal.coe_le_coe_iff, neg_le_neg_iff, div_le_iff₀ (by exact_mod_cast hΔ.card_pos)]
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hK) hΔK
  rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_comm] at this

/-- **Georgii (15.17), first inequality, for the specific entropy**:
`-𝓗_{V(0)}(μ | μ λ_0) ≤ 𝓀(μ)` for shift-invariant `μ`. -/
theorem neg_relativeEntropyIn_lexPast_le_specificEntropy [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) :
    -(relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) : EReal)
      ≤ specificEntropy lam μ :=
  le_iInf₂ fun _ hΔ ↦ neg_relativeEntropyIn_lexPast_le_entropyIn_div_card lam hμ hΔ.nonempty

/-- **Georgii (15.17), second inequality, for a finite `Δ ⊆ V(0)`**:
`𝓀(μ) ≤ -𝓗_Δ(μ | μ λ_0)`, by the finite-volume bound
`card_mul_relativeEntropyIn_le_relativeEntropyIn` along the cubes `[-N, N]^d`, in which the
translates of `Δ` fitting inside have asymptotic density `1`. -/
theorem specificEntropy_le_neg_relativeEntropyIn_of_subset_lexPast
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {Δ : Finset (ι → ℤ)}
    (hΔ : (Δ : Set (ι → ℤ)) ⊆ lexPast 0) :
    specificEntropy lam μ
      ≤ -(relativeEntropyIn (Δ : Set (ι → ℤ)) μ (μ.bind (Specification.isssd lam {0})) : EReal)
        := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  set K := relativeEntropyIn (Δ : Set (ι → ℤ)) μ (μ.bind (Specification.isssd lam {0}))
    with hK_def
  -- `R` bounds the coordinates of the sites of `Δ`
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ d ∈ Δ, ∀ k, |d k| ≤ R := by
    refine ⟨Δ.sup fun d ↦ Finset.univ.sup fun k ↦ (d k).natAbs, fun d hd k ↦ ?_⟩
    have h1 : (d k).natAbs ≤ Finset.univ.sup fun k ↦ (d k).natAbs :=
      Finset.le_sup (f := fun k ↦ (d k).natAbs) (Finset.mem_univ k)
    have h2 := Finset.le_sup (f := fun d ↦ Finset.univ.sup fun k ↦ (d k).natAbs) hd
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans h2
  set m : ℕ → ι → ℤ := fun N _ ↦ -(N : ℤ) with hm
  set n : ℕ → ι → ℤ := fun N _ ↦ (N : ℤ) with hn
  set c : ℕ → ℕ := fun N ↦ #{i ∈ Icc (m N) (n N) | ∀ d ∈ Δ, d + i ∈ Icc (m N) (n N)} with hc
  have hside : ∀ k, Tendsto (fun N ↦ n N k - m N k) atTop atTop := fun k ↦ by
    simp only [hm, hn, sub_neg_eq_add]
    exact tendsto_atTop_mono (fun N ↦ le_add_of_nonneg_left (Nat.cast_nonneg N))
      tendsto_natCast_atTop_atTop
  have hlim := tendsto_entropyIn_div_card lam hμ hside
  have hbound : ∀ N, (c N : ℝ≥0∞) * K
      ≤ relativeEntropyIn (Icc (m N) (n N) : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam) :=
    fun N ↦ card_mul_relativeEntropyIn_le_relativeEntropyIn lam hpres _ Δ hΔ
  have hsub : ∀ N, Icc (fun k ↦ m N k + R) (fun k ↦ n N k - R)
      ⊆ {i ∈ Icc (m N) (n N) | ∀ d ∈ Δ, d + i ∈ Icc (m N) (n N)} := by
    intro N i hi
    rw [Finset.mem_Icc] at hi
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨fun k ↦ ?_, fun k ↦ ?_⟩,
      fun d hd ↦ Finset.mem_Icc.2 ⟨fun k ↦ ?_, fun k ↦ ?_⟩⟩
    · have := hi.1 k; simp only [hm] at this ⊢; omega
    · have := hi.2 k; simp only [hn] at this ⊢; omega
    · have h1 := hi.1 k; have h2 := abs_le.1 (hR d hd k); simp only [hm, Pi.add_apply] at h1 ⊢
      omega
    · have h1 := hi.2 k; have h2 := abs_le.1 (hR d hd k); simp only [hn, Pi.add_apply] at h1 ⊢
      omega
  have hcard : ∀ N, 0 < #(Icc (m N) (n N)) := fun N ↦ (isBox_Icc (by
    intro k; simp only [hm, hn]; omega)).card_pos
  by_cases hK : K = ∞
  · -- then `𝓗_Λ(μ | λ^S) = ∞` as soon as one translate of `Δ` fits in `Λ`
    have hc1 : 1 ≤ c R := by
      refine Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨fun k ↦ ?_, fun k ↦ ?_⟩,
        fun d hd ↦ Finset.mem_Icc.2 ⟨fun k ↦ ?_, fun k ↦ ?_⟩⟩⟩
      · simp [hm]
      · simp [hn]
      · have := abs_le.1 (hR d hd k); simp only [hm, Pi.add_apply, Pi.zero_apply, add_zero]; omega
      · have := abs_le.1 (hR d hd k); simp only [hn, Pi.add_apply, Pi.zero_apply, add_zero]; omega
    have hH : relativeEntropyIn (Icc (m R) (n R) : Set (ι → ℤ)) μ
        (Measure.infinitePi fun _ ↦ lam) = ∞ := by
      refine top_le_iff.1 ((hbound R).trans' ?_)
      rw [hK, ENNReal.mul_top (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hc1)]
    rw [hK, EReal.coe_ennreal_top, EReal.neg_top]
    refine (specificEntropy_le_entropyIn_div_card lam (isBox_Icc (m := m R) (n := n R) (by
      intro k; simp only [hm, hn]; omega))).trans ?_
    rw [entropyIn, hH, EReal.coe_ennreal_top, EReal.neg_top,
      EReal.bot_div_natCast (hcard R).ne']
  -- the real-valued bound along the cubes
  set r : ℕ → ℝ := fun N ↦ -((c N : ℝ) / #(Icc (m N) (n N)) * K.toReal) with hr
  have hle : ∀ N, entropyIn lam (Icc (m N) (n N) : Set (ι → ℤ)) μ / (#(Icc (m N) (n N)) : EReal)
      ≤ ((r N : ℝ) : EReal) := by
    intro N
    by_cases hH : relativeEntropyIn (Icc (m N) (n N) : Set (ι → ℤ)) μ
        (Measure.infinitePi fun _ ↦ lam) = ∞
    · rw [entropyIn, hH, EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_div_natCast (hcard N).ne']
      exact bot_le
    rw [entropyIn, neg_coe_ennreal_div_natCast hH, EReal.coe_le_coe_iff, hr, neg_le_neg_iff,
      div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by exact_mod_cast hcard N)]
    have := ENNReal.toReal_mono hH (hbound N)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
  have hratio : Tendsto (fun N ↦ (c N : ℝ) / #(Icc (m N) (n N))) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (Finset.tendsto_card_Icc_div_card_Icc hside R)
      tendsto_const_nhds (fun N ↦ ?_) (fun N ↦ ?_)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.2 (Finset.card_le_card (hsub N)))
        (Nat.cast_nonneg _)
    · exact div_le_one_of_le₀ (Nat.cast_le.2 (Finset.card_filter_le _ _)) (Nat.cast_nonneg _)
  have hr_lim : Tendsto r atTop (𝓝 (-(1 * K.toReal))) := (hratio.mul_const _).neg
  have := le_of_tendsto_of_tendsto' hlim (EReal.tendsto_coe.2 hr_lim) hle
  rwa [one_mul, EReal.coe_neg, EReal.coe_ennreal_toReal hK] at this

/-- **Georgii (15.17), second inequality**: `𝓀(μ) ≤ -𝓗_{V(0)}(μ | μ λ_0)` for `μ ∈ 𝓟_Θ`, from
the finite `Δ ⊆ V(0)` by Georgii (15.6) along `Δ_n = V(0) ∩ [-n, n]^d ↑ V(0)`. -/
theorem specificEntropy_le_neg_relativeEntropyIn_lexPast
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy lam μ
      ≤ -(relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) : EReal) := by
  classical
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  set ν := μ.bind (Specification.isssd lam {0}) with hν
  set Δ : ℕ → Finset (ι → ℤ) := fun N ↦
    (Icc (fun _ ↦ -(N : ℤ)) fun _ ↦ (N : ℤ)).filter (· ∈ lexPast (0 : ι → ℤ)) with hΔ
  have hΔmono : Monotone Δ := fun a b hab ↦ Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc (fun k ↦ by simp; omega) fun k ↦ by simp; omega)
  have hΔsub : ∀ N, (Δ N : Set (ι → ℤ)) ⊆ lexPast 0 := fun N i hi ↦ (Finset.mem_filter.1 hi).2
  have hΔunion : ⋃ N, (Δ N : Set (ι → ℤ)) = lexPast 0 := by
    refine Set.Subset.antisymm (Set.iUnion_subset hΔsub) fun i hi ↦ ?_
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k, |i k| ≤ N :=
      ⟨Finset.univ.sup fun k ↦ (i k).natAbs, fun k ↦ by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast Finset.le_sup (f := fun k ↦ (i k).natAbs) (Finset.mem_univ k)⟩
    refine Set.mem_iUnion.2 ⟨N, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨fun k ↦ ?_, fun k ↦ ?_⟩, hi⟩⟩
    · have := abs_le.1 (hN k); exact this.1
    · have := abs_le.1 (hN k); exact this.2
  let ℱ : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace ((ι → ℤ) → E)) :=
    ⟨fun N ↦ cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Δ N : Set (ι → ℤ)),
      fun a b hab ↦ cylinderEvents_mono (Finset.coe_subset.2 (hΔmono hab)),
      fun _ ↦ cylinderEvents_le_pi⟩
  have hsup : (⨆ N, ℱ N) = cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0) := by
    rw [← hΔunion, cylinderEvents_iUnion]
  have hlim : Tendsto (fun N ↦ (relativeEntropyIn (Δ N : Set (ι → ℤ)) μ ν : EReal)) atTop
      (𝓝 (relativeEntropyIn (lexPast 0) μ ν : EReal)) := by
    have := tendsto_klDiv_trim (μ := μ) (ν := ν) ℱ
    rw [klDiv_trim_congr hsup (iSup_le ℱ.le) cylinderEvents_le_pi] at this
    exact (continuous_coe_ennreal_ereal.tendsto _).comp this
  refine EReal.le_neg.2 (le_of_tendsto' hlim fun N ↦ EReal.le_neg.1 ?_)
  exact specificEntropy_le_neg_relativeEntropyIn_of_subset_lexPast lam hμ (hΔsub N)

/-- **Georgii Proposition (15.16).** For `μ ∈ 𝓟_Θ` and every site `j`, the specific entropy is
the (negative) relative entropy of `μ` with respect to `μ λ_{j}` (the field with the spin at `j`
resampled from `λ`) on the lexicographic past `V(j)`:
`𝓀(μ) = -𝓗_{V(j)}(μ | μ λ_{j})`. -/
theorem specificEntropy_eq_neg_relativeEntropyIn_lexPast
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) (j : ι → ℤ) :
    specificEntropy lam μ
      = -(relativeEntropyIn (lexPast j) μ (μ.bind (Specification.isssd lam {j})) : EReal) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have h0 : relativeEntropyIn (lexPast j) μ (μ.bind (Specification.isssd lam {j}))
      = relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) := by
    have := relativeEntropyIn_bind_isssd_singleton_eq_image_sub lam hpres (lexPast j) 0 j
    rwa [zero_add, image_sub_lexPast, sub_self] at this
  rw [h0]
  exact le_antisymm (specificEntropy_le_neg_relativeEntropyIn_lexPast lam hμ)
    (neg_relativeEntropyIn_lexPast_le_specificEntropy lam hpres)

/-- **Georgii Proposition (15.16), first equality**: for `μ ∈ 𝓟_Θ` the infimum defining `𝓀(μ)`
may be taken over all nonempty finite volumes instead of the boxes,
`𝓀(μ) = inf_{Δ ∈ 𝒮} |Δ|⁻¹ 𝓗_Δ(μ)`. -/
theorem specificEntropy_eq_iInf_finset (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy lam μ
      = ⨅ Δ : Finset (ι → ℤ), ⨅ (_ : Δ.Nonempty), entropyIn lam (Δ : Set (ι → ℤ)) μ / (#Δ : EReal)
        := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  refine le_antisymm (le_iInf₂ fun Δ hΔ ↦ ?_) (le_iInf₂ fun Δ hΔ ↦ iInf₂_le Δ hΔ.nonempty)
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hμ 0]
  exact neg_relativeEntropyIn_lexPast_le_entropyIn_div_card lam hpres hΔ

end Lexicographic


section CountablyGenerated

variable {S E : Type*} [MeasurableSpace E]

/-- For a countable site set and a standard Borel state space, every cylinder σ-algebra `𝓕_Δ` is
countably generated (Georgii, in the proof of (15.20)). -/
lemma countablyGenerated_cylinderEvents [Countable S] [StandardBorelSpace E] (Δ : Set S) :
    @MeasurableSpace.CountablyGenerated (S → E) (cylinderEvents (X := fun _ : S ↦ E) Δ) := by
  rw [cylinderEvents_eq_comap_restrict]
  exact MeasurableSpace.CountablyGenerated.comap _

end CountablyGenerated

/-! ### `(P, 𝒜)`-kernels as conditional expectations of nonnegative functions -/

section PAKernel

variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [m : MeasurableSpace Ω] {P : Set (Measure Ω)}
  {κ : Kernel[𝒜, m] Ω Ω} [IsMarkovKernel κ]

/-- `∫_A κ(B | ω) μ(dω) = μ(A ∩ B)` for `A ∈ 𝒜`, `μ ∈ P`. -/
lemma IsPAKernel.setLIntegral_apply_eq (hκ : IsPAKernel P 𝒜 κ) (h𝒜 : 𝒜 ≤ m) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) {A : Set Ω} (hA : MeasurableSet[𝒜] A) {B : Set Ω}
    (hB : MeasurableSet B) :
    ∫⁻ ω in A, κ ω B ∂μ = μ (A ∩ B) := by
  have : SigmaFinite (μ.trim h𝒜) := inferInstance
  have hA' : MeasurableSet A := h𝒜 _ hA
  have hreal : ∫ ω in A, (κ ω).real B ∂μ = μ.real (A ∩ B) := by
    calc ∫ ω in A, (κ ω).real B ∂μ
        = ∫ ω in A, (μ[B.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ω ∂μ :=
          integral_congr_ae (ae_restrict_of_ae (hκ.1 μ hμ B hB))
      _ = ∫ ω in A, B.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ :=
          setIntegral_condExp h𝒜 ((integrable_const _).indicator hB) hA
      _ = μ.real (A ∩ B) := by
          rw [integral_indicator hB, Measure.restrict_restrict hB, setIntegral_const, smul_eq_mul,
            mul_one, Set.inter_comm]
  have hmeas : Measurable fun ω ↦ κ ω B := measurable_kernel_coe_of_le h𝒜 hB
  have htoReal : ∫ ω in A, (κ ω).real B ∂μ = (∫⁻ ω in A, κ ω B ∂μ).toReal := by
    simp only [measureReal_def]
    exact integral_toReal hmeas.aemeasurable (Eventually.of_forall fun ω ↦ measure_lt_top _ _)
  have hne : ∫⁻ ω in A, κ ω B ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μ) (by simp) ?_
    exact lintegral_mono fun ω ↦ prob_le_one
  rw [htoReal, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hne (measure_ne_top _ _)).1 hreal

/-- `∫_A κ(F | ω) μ(dω) = ∫_A F dμ` for `A ∈ 𝒜`, `μ ∈ P` and measurable `F ≥ 0`: a `(P, 𝒜)`-kernel
is a version of the conditional expectation `μ(· | 𝒜)` on nonnegative functions. -/
lemma IsPAKernel.setLIntegral_lintegral_eq (hκ : IsPAKernel P 𝒜 κ) (h𝒜 : 𝒜 ≤ m) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) {A : Set Ω} (hA : MeasurableSet[𝒜] A) {F : Ω → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω in A, ∫⁻ ω', F ω' ∂(κ ω) ∂μ = ∫⁻ ω in A, F ω ∂μ := by
  refine Measurable.ennreal_induction
    (motive := fun F ↦ ∫⁻ ω in A, ∫⁻ ω', F ω' ∂(κ ω) ∂μ = ∫⁻ ω in A, F ω ∂μ) ?_ ?_ ?_ hF
  · intro c B hB
    simp_rw [lintegral_indicator_const hB]
    rw [lintegral_const_mul _ (measurable_kernel_coe_of_le h𝒜 hB),
      hκ.setLIntegral_apply_eq h𝒜 hμ hA hB, Measure.restrict_apply hB, Set.inter_comm]
  · intro f g _ hf hg ihf ihg
    have hf' : Measurable fun ω ↦ ∫⁻ ω', f ω' ∂(κ ω) :=
      (Measurable.lintegral_kernel hf).mono h𝒜 le_rfl
    simp_rw [Pi.add_apply, lintegral_add_left hf]
    rw [lintegral_add_left hf', ihf, ihg]
  · intro f hfm hfmono ih
    have hf' : ∀ n, Measurable fun ω ↦ ∫⁻ ω', f n ω' ∂(κ ω) := fun n ↦
      (Measurable.lintegral_kernel (hfm n)).mono h𝒜 le_rfl
    simp_rw [lintegral_iSup hfm hfmono]
    rw [lintegral_iSup hf' fun a b hab ω ↦ lintegral_mono fun ω' ↦ hfmono hab ω']
    exact iSup_congr ih

end PAKernel

/-! ### Invariant events are measurable with respect to the lexicographic past, almost surely -/

section LexPastInvariant

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] [MeasurableSpace E]
  {μ : Measure ((ι → ℤ) → E)}

/-- Every finite volume can be shifted into the strict lexicographic past `V*(0)` (in dimension
`d ≥ 1`). -/
lemma exists_image_sub_subset_lexPast_diff (Λ : Finset (ι → ℤ)) :
    ∃ k : ι → ℤ, (· - k) '' (Λ : Set (ι → ℤ)) ⊆ lexPast 0 \ {0} := by
  classical
  set i₀ : ι := Finset.univ.min' Finset.univ_nonempty with hi₀
  set M : ℕ := Λ.sup fun x ↦ (x i₀).toNat with hM
  refine ⟨Pi.single i₀ ((M : ℤ) + 1), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [lexPast_diff_singleton]
  have hxM : x i₀ ≤ M := (Int.self_le_toNat _).trans
    (by exact_mod_cast Finset.le_sup (f := fun x ↦ (x i₀).toNat) hx)
  refine ⟨i₀, fun j hj ↦ absurd hj (not_lt.2 (Finset.min'_le _ _ (Finset.mem_univ j))), ?_⟩
  simp only [Pi.toLex_apply, Pi.sub_apply, Pi.single_eq_same, Pi.zero_apply]
  omega

/-- **Invariant events are almost surely measurable with respect to the strict lexicographic
past** (the analogue of Georgii's Proposition (14.9) for `V*(0)` in place of the tail): for
`μ ∈ 𝓟_Θ` and `A ∈ 𝓘` there is `B ∈ 𝓕_{V*(0)}` with `μ(A ∆ B) = 0`. Local approximants of `A`
are shifted into `V*(0)`, at no cost by the shift invariance of `μ` and of `A`, and the limit
superior of the shifted approximants does the job (Borel–Cantelli). -/
theorem exists_measurableSet_cylinderEvents_lexPast_diff_measure_symmDiff_eq_zero
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {A : Set ((ι → ℤ) → E)}
    (hA : MeasurableSet[invariantEvents (shiftGroup (ι → ℤ) E)] A) :
    ∃ B, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] B
      ∧ μ (A ∆ B) = 0 := by
  classical
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hAm : MeasurableSet A := (measurableSet_invariantEvents.1 hA).1
  have happrox : ∀ n : ℕ, ∃ B : Set ((ι → ℤ) → E),
      (∃ Λ : Finset (ι → ℤ), MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Λ : Set _)] B)
        ∧ μ (A ∆ B) < (2⁻¹ : ℝ≥0∞) ^ n := fun n ↦ by
    obtain ⟨B, hB, hAB⟩ := exists_mem_localEvents_measure_symmDiff_lt μ hAm
      (ε := (2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
    exact ⟨B, mem_localEvents_iff_cylinderEvents.1 hB, hAB⟩
  choose B hBΛ hAB using happrox
  choose Λ hBΛ using hBΛ
  choose k hk using fun n ↦ exists_image_sub_subset_lexPast_diff (Λ n)
  set C : ℕ → Set ((ι → ℤ) → E) := fun n ↦ (shift E (k n)).toFun ⁻¹' B n with hC
  have hCm : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] (C n) :=
    fun n ↦ by
      refine cylinderEvents_mono (hk n) _ ?_
      rw [← cylinderEvents_comap_shift]
      exact MeasurableSpace.measurableSet_comap.2 ⟨B n, hBΛ n, rfl⟩
  have hAC : ∀ n, μ (A ∆ C n) < (2⁻¹ : ℝ≥0∞) ^ n := fun n ↦ by
    rw [hC, measure_symmDiff_preimage_eq hμ hA (shift_mem_shiftGroup (k n))
      (cylinderEvents_le_pi _ (hBΛ n))]
    exact hAB n
  have hsum : ∑' n, μ (A ∆ C n) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun n ↦ (hAC n).le)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  obtain ⟨u, hu, hAu⟩ := exists_measurableSet_iInf_measure_symmDiff_eq_zero (μ := μ) (ι := Unit)
    (M := fun _ ↦ cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})) (t := C)
    (fun _ ↦ Eventually.of_forall hCm) hsum
  rw [iInf_const] at hu
  exact ⟨u, hu, hAu⟩

end LexPastInvariant

/-! ### Georgii (15.18): the specific entropy as a conditional entropy of one spin -/

section Formula1518

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace E] (lam : Measure E)
  [IsProbabilityMeasure lam] {μ : Measure ((ι → ℤ) → E)}

/-- **Georgii (15.18), integral form.** If `μ = g · μ λ_0` on `𝓕_{V(0)}` with `g`
`𝓕_{V(0)}`-measurable, then `𝓗_{V(0)}(μ | μ λ_0) = μ(𝓗_ℰ(q^· | λ))`, where
`q^ω = g(· ω_{S ∖ 0}) λ` is the conditional distribution of the spin at `0` given the past and
`𝓗_ℰ(q^ω | λ) = ∫ ψ(g(x ω_{S ∖ 0})) λ(dx)` with `ψ = klFun`. -/
theorem relativeEntropyIn_lexPast_eq_lintegral_lintegral_klFun [IsProbabilityMeasure μ]
    {g : ((ι → ℤ) → E) → ℝ≥0∞}
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g) :
    relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0}))
      = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal (klFun (g (update ω 0 x)).toReal) ∂lam ∂μ := by
  have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  have hk : Measurable fun x ↦ ENNReal.ofReal (klFun (g x).toReal) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp (ENNReal.measurable_toReal.comp hg'))
  rw [relativeEntropyIn, klDiv_trim_eq_lintegral_klFun_of_trim_eq_withDensity _ hg hμg,
    Measure.lintegral_bind (Specification.measurable_isssd_coe _).aemeasurable hk.aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [Specification.isssd_singleton_eq_map, lintegral_map hk (measurable_update ω)]

/-- **Georgii (15.18).** For `μ ∈ 𝓟_Θ` with `μ = g · μ λ_0` on `𝓕_{V(0)}`,
`𝓀(μ) = -μ(𝓗_ℰ(q^· | λ))`: the specific entropy is the conditional entropy of the spin at `0`
given the lexicographic past. -/
theorem specificEntropy_eq_neg_lintegral_lintegral_klFun
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) {g : ((ι → ℤ) → E) → ℝ≥0∞}
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g) :
    specificEntropy lam μ
      = -(∫⁻ ω, ∫⁻ x, ENNReal.ofReal (klFun (g (update ω 0 x)).toReal) ∂lam ∂μ : EReal) := by
  have : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hμ 0,
    relativeEntropyIn_lexPast_eq_lintegral_lintegral_klFun lam hg hμg]

omit [Fintype ι] in
/-- If `𝓗_{V(0)}(μ | μ λ_0) < ∞`, Georgii's density `g` exists: `μ = g · μ λ_0` on `𝓕_{V(0)}`
with `g` `𝓕_{V(0)}`-measurable (Radon–Nikodym). -/
lemma exists_measurable_trim_eq_withDensity_of_relativeEntropyIn_lexPast_ne_top
    [IsProbabilityMeasure μ]
    (h : relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) ≠ ∞) :
    ∃ g : ((ι → ℤ) → E) → ℝ≥0∞, Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g
      ∧ μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
        = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g :=
  ⟨_, Measure.measurable_rnDeriv _ _,
    (Measure.withDensity_rnDeriv_eq _ _ (klDiv_ne_top_iff.1 h).1).symm⟩

/-- For `μ ∈ 𝓟_Θ`, `𝓀(μ) > -∞` if and only if `𝓗_{V(0)}(μ | μ λ_0) < ∞`. -/
lemma specificEntropy_ne_bot_iff (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy lam μ ≠ ⊥
      ↔ relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0})) ≠ ∞ := by
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hμ 0, ne_eq, EReal.neg_eq_bot_iff,
    EReal.coe_ennreal_eq_top_iff]

end Formula1518

/-! ### Georgii Theorem (15.20): the specific entropy as the integral of a fixed function -/

section Theorem1520

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι] [MeasurableSpace E]
  [StandardBorelSpace E] (lam : Measure E) [IsProbabilityMeasure lam]
  {κ : Kernel[invariantEvents (shiftGroup (ι → ℤ) E)] ((ι → ℤ) → E) ((ι → ℤ) → E)}
  [IsMarkovKernel κ]

omit [Nonempty ι] [IsMarkovKernel κ] in
/-- `ω ↦ 𝓗_{V(0)}(κ^ω | κ^ω λ_0)` is `𝓘`-measurable for a Markov kernel `κ` from `𝓘`
(measurability of `𝓗_{V(0)}(·)`, Georgii's Step 1 in the proof of (15.20), through the
kernel Radon–Nikodym derivative). -/
lemma measurable_relativeEntropyIn_lexPast_kernel [IsMarkovKernel κ] :
    Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] fun ω ↦
      relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind (Specification.isssd lam {0})) := by
  have hV : cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have : @MeasurableSpace.CountablyGenerated ((ι → ℤ) → E)
      (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) :=
    countablyGenerated_cylinderEvents _
  have hid : Measurable[MeasurableSpace.pi, cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)]
    id := measurable_id'' hV
  -- the kernel `ω ↦ κ^ω λ_0`, as the composition `λ_0 ∘ κ`
  have hmk := Kernel.IsMarkovKernel.map κ hid
  have hmk₀ := Kernel.IsMarkovKernel.map
    ((Specification.isssd (S := ι → ℤ) lam {0}).comap id (measurable_id'' cylinderEvents_le_pi)
      ∘ₖ κ) hid
  have heq : (fun ω ↦ relativeEntropyIn (lexPast 0) (κ ω)
      ((κ ω).bind (Specification.isssd lam {0}))) = fun ω ↦
        klDiv ((@Kernel.map _ _ _ _ _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) κ id) ω)
          ((@Kernel.map _ _ _ _ _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0))
            ((Specification.isssd (S := ι → ℤ) lam {0}).comap id
              (measurable_id'' cylinderEvents_le_pi) ∘ₖ κ) id) ω) := by
    funext ω
    rw [Kernel.map_apply _ hid, Kernel.map_apply _ hid, ← trim_eq_map hV, ← trim_eq_map hV,
      Kernel.comp_apply]
    rfl
  rw [heq]
  exact measurable_klDiv_kernel _ _

omit [Nonempty ι] in
/-- **Georgii Theorem (15.20), the integrand**: for a `(𝓟_Θ, 𝓘)`-kernel `κ`, the function
`h = 𝓀(κ^·)` is `𝓘`-measurable (Georgii: `𝓘 ∩ 𝓣 ∩ 𝓕_{V(0)}`-measurable for his particular
kernel, built from a countable core of cylinder events averaged over the past; a general
`(𝓟_Θ, 𝓘)`-kernel only gives `𝓘`-measurability, which is all that (15.20) uses). -/
theorem IsPAKernel.measurable_specificEntropy_comp
    (hκ : IsPAKernel (invariantFields (shiftGroup (ι → ℤ) E))
      (invariantEvents (shiftGroup (ι → ℤ) E)) κ) :
    Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] fun ω ↦ specificEntropy lam (κ ω) := by
  have : (fun ω ↦ specificEntropy lam (κ ω)) = fun ω ↦
      -(relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind (Specification.isssd lam {0})) : EReal) :=
    funext fun ω ↦ specificEntropy_eq_neg_relativeEntropyIn_lexPast lam (hκ.2 ω) 0
  rw [this]
  exact measurable_neg.comp
    (measurable_coe_ennreal_ereal.comp (measurable_relativeEntropyIn_lexPast_kernel lam))

/-- **Georgii Theorem (15.20), main identity**: for a `(𝓟_Θ, 𝓘)`-kernel `κ` and `μ ∈ 𝓟_Θ`,
`𝓗_{V(0)}(μ | μ λ_0) = ∫ 𝓗_{V(0)}(κ^ω | κ^ω λ_0) μ(dω)`, i.e. `𝓀(μ) = μ(h)` with
`h = 𝓀(κ^·) = -𝓗_{V(0)}(κ^· | κ^· λ_0)`. -/
theorem IsPAKernel.relativeEntropyIn_lexPast_eq_lintegral
    (hκ : IsPAKernel (invariantFields (shiftGroup (ι → ℤ) E))
      (invariantEvents (shiftGroup (ι → ℤ) E)) κ)
    {μ : Measure ((ι → ℤ) → E)} (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    relativeEntropyIn (lexPast 0) μ (μ.bind (Specification.isssd lam {0}))
      = ∫⁻ ω, relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind (Specification.isssd lam {0})) ∂μ
        := by
  classical
  have h𝓘 : invariantEvents (shiftGroup (ι → ℤ) E) ≤ MeasurableSpace.pi :=
    fun s hs ↦ (measurableSet_invariantEvents.1 hs).1
  have hκm : Measurable κ := κ.measurable.mono h𝓘 le_rfl
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hV : cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  set L0 := Specification.isssd (S := ι → ℤ) lam {0} with hL0
  have hL0m : Measurable L0 := Specification.measurable_isssd_coe _
  have hKκ : Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] fun ω ↦
      relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind L0) :=
    measurable_relativeEntropyIn_lexPast_kernel lam
  have hKκ' : Measurable fun ω ↦ relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind L0) :=
    hKκ.mono h𝓘 le_rfl
  set ν := μ.bind L0 with hν
  have hνκm : Measurable fun ω ↦ (κ ω).bind L0 := (Measure.measurable_bind' hL0m).comp hκm
  have hbind : (μ.bind fun ω ↦ (κ ω).bind L0) = ν := by
    rw [← Measure.bind_bind hκm.aemeasurable hL0m.aemeasurable, hκ.bind_eq h𝓘 hμ]
  -- unless both sides are infinite, `μ ≪ μ λ_0` on `𝓕_{V(0)}`
  by_cases hinf : relativeEntropyIn (lexPast 0) μ ν = ∞
      ∧ ∫⁻ ω, relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind L0) ∂μ = ∞
  · rw [hinf.1, hinf.2]
  have hac : μ.trim hV ≪ ν.trim hV := by
    rcases not_and_or.1 hinf with h | h
    · exact (klDiv_ne_top_iff.1 h).1
    · have hae : ∀ᵐ ω ∂μ, (κ ω).trim hV ≪ ((κ ω).bind L0).trim hV := by
        filter_upwards [ae_lt_top hKκ' h] with ω hω
        exact (klDiv_ne_top_iff.1 hω.ne).1
      refine Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
      have hs' : MeasurableSet s := hV s hs
      rw [trim_measurableSet_eq hV hs] at hνs ⊢
      rw [← hbind, Measure.bind_apply hs' hνκm.aemeasurable] at hνs
      rw [← hκ.bind_eq h𝓘 hμ, Measure.bind_apply hs' hκm.aemeasurable]
      have hmeas : Measurable fun ω ↦ (κ ω).bind L0 s := (Measure.measurable_coe hs').comp hνκm
      have h0 : ∀ᵐ ω ∂μ, (κ ω).bind L0 s = 0 := (lintegral_eq_zero_iff hmeas).1 hνs
      refine (lintegral_eq_zero_iff (measurable_kernel_coe_of_le h𝓘 hs')).2 ?_
      filter_upwards [hae, h0] with ω hω h0ω
      have := hω (show ((κ ω).bind L0).trim hV s = 0 by rwa [trim_measurableSet_eq hV hs])
      rwa [trim_measurableSet_eq hV hs] at this
  set g := (μ.trim hV).rnDeriv (ν.trim hV) with hg_def
  have hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g :=
    Measure.measurable_rnDeriv _ _
  have hg' : Measurable g := hg.mono hV le_rfl
  have hμg : μ.trim hV = (ν.trim hV).withDensity g :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  -- Step 2: `κ^ω = g · κ^ω λ_0` on `𝓕_{V(0)}` for `μ`-a.e. `ω`
  have hB : ∀ B, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] B →
      ∀ᵐ ω ∂μ, κ ω B = ∫⁻ ω' in B, g ω' ∂((κ ω).bind L0) := by
    intro B hB
    have hB' : MeasurableSet B := hV B hB
    set Φ : ((ι → ℤ) → E) → ℝ≥0∞ := fun ω'' ↦ ∫⁻ ω', B.indicator g ω' ∂(L0 ω'') with hΦ
    have hΦm : Measurable Φ :=
      (Measurable.lintegral_kernel (hg'.indicator hB')).mono cylinderEvents_le_pi le_rfl
    have hF₂ : ∀ ω, ∫⁻ ω' in B, g ω' ∂((κ ω).bind L0) = ∫⁻ ω'', Φ ω'' ∂(κ ω) := fun ω ↦ by
      rw [← lintegral_indicator hB',
        Measure.lintegral_bind hL0m.aemeasurable (hg'.indicator hB').aemeasurable]
    simp_rw [hF₂]
    have hm₁ : Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] fun ω ↦ κ ω B :=
      κ.measurable_coe hB'
    have hm₂ : Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] fun ω ↦ ∫⁻ ω'', Φ ω'' ∂(κ ω) :=
      Measurable.lintegral_kernel hΦm
    have : SigmaFinite (μ.trim h𝓘) := inferInstance
    refine ae_eq_of_ae_eq_trim (hm := h𝓘)
      (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := μ.trim h𝓘) hm₁ hm₂ fun A hA _ ↦ ?_)
    rw [restrict_trim h𝓘 μ hA, lintegral_trim _ hm₁, lintegral_trim _ hm₂,
      hκ.setLIntegral_apply_eq h𝓘 hμ hA hB', hκ.setLIntegral_lintegral_eq h𝓘 hμ hA hΦm]
    -- `∫_A Φ dμ = μ(A ∩ B)`, through an `𝓕_{V*(0)}`-measurable version `A'` of `A`
    obtain ⟨A', hA', hAA'⟩ :=
      exists_measurableSet_cylinderEvents_lexPast_diff_measure_symmDiff_eq_zero hμ hA
    have hA'V : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] A' :=
      cylinderEvents_mono Set.sdiff_subset _ hA'
    have hA'c : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ))ᶜ)] A' :=
      cylinderEvents_mono (fun x hx ↦ by simpa using hx.2) _ hA'
    have hA'm : MeasurableSet A' := hV _ hA'V
    have hAA'ae : A =ᵐ[μ] A' := measure_symmDiff_eq_zero_iff.1 hAA'
    have hind : Measurable fun ω' ↦ A'.indicator 1 ω' * B.indicator g ω' :=
      (measurable_one.indicator hA'm).mul (hg'.indicator hB')
    calc μ (A ∩ B) = μ (A' ∩ B) := measure_congr (hAA'ae.inter (ae_eq_refl B))
      _ = μ.trim hV (A' ∩ B) := (trim_measurableSet_eq hV (hA'V.inter hB)).symm
      _ = ∫⁻ ω' in A' ∩ B, g ω' ∂ν := by
          rw [hμg, withDensity_apply _ (hA'V.inter hB), restrict_trim hV ν (hA'V.inter hB),
            lintegral_trim hV hg]
      _ = ∫⁻ ω', A'.indicator 1 ω' * B.indicator g ω' ∂ν := by
          rw [← lintegral_indicator (hA'm.inter hB')]
          refine lintegral_congr fun ω' ↦ ?_
          by_cases h1 : ω' ∈ A' <;> by_cases h2 : ω' ∈ B <;> simp [Set.indicator, h1, h2]
      _ = ∫⁻ ω'', ∫⁻ ω', A'.indicator 1 ω' * B.indicator g ω' ∂(L0 ω'') ∂μ :=
          Measure.lintegral_bind hL0m.aemeasurable hind.aemeasurable
      _ = ∫⁻ ω'', A'.indicator 1 ω'' * Φ ω'' ∂μ := by
          refine lintegral_congr fun ω'' ↦ ?_
          rw [hΦ, ← lintegral_const_mul _ (hg'.indicator hB')]
          refine (Specification.isResampling_isssd lam).lintegral_congr hind
            ((hg'.indicator hB').const_mul _) fun ζ hζ ↦ ?_
          congr 1
          have hmem := mem_congr_of_measurableSet_cylinderEvents hA'c
            fun i hi ↦ hζ i (by simpa using hi)
          by_cases h : ω'' ∈ A' <;> simp [Set.indicator, h, hmem]
      _ = ∫⁻ ω'' in A', Φ ω'' ∂μ := by
          rw [← lintegral_indicator hA'm]
          refine lintegral_congr fun ω'' ↦ ?_
          by_cases h1 : ω'' ∈ A' <;> simp [Set.indicator, h1]
      _ = ∫⁻ ω'' in A, Φ ω'' ∂μ := by rw [Measure.restrict_congr_set hAA'ae.symm]
  have : @MeasurableSpace.CountablyGenerated ((ι → ℤ) → E)
      (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) :=
    countablyGenerated_cylinderEvents _
  have hall : ∀ᵐ ω ∂μ, ∀ t : Finset ℕ,
      κ ω (@piNatGen _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _ t)
        = ∫⁻ ω' in (@piNatGen _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _ t), g ω'
            ∂((κ ω).bind L0) :=
    ae_all_iff.2 fun t ↦ hB _
      (@measurableSet_piNatGen _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _ t)
  have hae : ∀ᵐ ω ∂μ, (κ ω).trim hV = (((κ ω).bind L0).trim hV).withDensity g := by
    filter_upwards [hall, hB Set.univ MeasurableSet.univ] with ω hω hωu
    have hfin : IsFiniteMeasure ((κ ω).trim hV) := isFiniteMeasure_trim hV
    refine MeasureTheory.ext_of_generate_finite
      (m0 := cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) (μ := (κ ω).trim hV)
      (ν := (((κ ω).bind L0).trim hV).withDensity g)
      (@piNatGenSet _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _)
      (@generateFrom_piNatGenSet _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _).symm
      (@isPiSystem_piNatGenSet _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)) _) ?_ ?_
    · rintro s ⟨t, rfl⟩
      have hs := @measurableSet_piNatGen _ (cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0))
        _ t
      rw [trim_measurableSet_eq hV hs, withDensity_apply _ hs, restrict_trim hV _ hs,
        lintegral_trim hV hg]
      exact hω t
    · rw [trim_measurableSet_eq hV MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
        restrict_trim hV _ MeasurableSet.univ, lintegral_trim hV hg]
      exact hωu
  -- Step 3: integrate `𝓗_{V(0)}(κ^ω | κ^ω λ_0) = κ^ω λ_0 (ψ ∘ g)` over `μ`
  have hK : relativeEntropyIn (lexPast 0) μ ν = ∫⁻ x, ENNReal.ofReal (klFun (g x).toReal) ∂ν :=
    klDiv_trim_eq_lintegral_klFun_of_trim_eq_withDensity hV hg hμg
  have hKκω : ∀ᵐ ω ∂μ, relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind L0)
      = ∫⁻ x, ENNReal.ofReal (klFun (g x).toReal) ∂((κ ω).bind L0) := by
    filter_upwards [hae] with ω hω
    exact klDiv_trim_eq_lintegral_klFun_of_trim_eq_withDensity hV hg hω
  have hk : Measurable fun x ↦ ENNReal.ofReal (klFun (g x).toReal) :=
    ENNReal.measurable_ofReal.comp (measurable_klFun.comp (ENNReal.measurable_toReal.comp hg'))
  rw [hK, lintegral_congr_ae hKκω, ← Measure.lintegral_bind hνκm.aemeasurable hk.aemeasurable,
    hbind]

/-- **Georgii Theorem (15.20)**, for a given `(𝓟_Θ, 𝓘)`-kernel `κ`: with `h = 𝓀(κ^·)`,
`𝓀(μ) = μ(h)` for every `μ ∈ 𝓟_Θ`, the `μ`-integral of the nonpositive function `h` being
`-∫ (-h) dμ`. -/
theorem IsPAKernel.specificEntropy_eq_neg_lintegral
    (hκ : IsPAKernel (invariantFields (shiftGroup (ι → ℤ) E))
      (invariantEvents (shiftGroup (ι → ℤ) E)) κ)
    {μ : Measure ((ι → ℤ) → E)} (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy lam μ = -(∫⁻ ω, (-specificEntropy lam (κ ω)).toENNReal ∂μ : EReal) := by
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hμ 0,
    hκ.relativeEntropyIn_lexPast_eq_lintegral lam hμ]
  congr 2
  refine lintegral_congr fun ω ↦ ?_
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam (hκ.2 ω) 0, neg_neg,
    EReal.toENNReal_coe]

/-- **Georgii Theorem (15.20), existence form.** There is an `𝓘`-measurable
`h : Ω → [-∞, 0]` (Georgii: `[-∞, log λ(E)]`) with `𝓀(μ) = μ(h)` for all `μ ∈ 𝓟_Θ`. -/
theorem exists_measurable_specificEntropy_eq_neg_lintegral :
    ∃ h : ((ι → ℤ) → E) → EReal, Measurable[invariantEvents (shiftGroup (ι → ℤ) E)] h
      ∧ (∀ ω, h ω ≤ 0) ∧ ∀ μ ∈ invariantFields (shiftGroup (ι → ℤ) E),
        specificEntropy lam μ = -(∫⁻ ω, (-h ω).toENNReal ∂μ : EReal) := by
  have hne : (invariantFields (shiftGroup (ι → ℤ) E)).Nonempty :=
    ⟨Measure.infinitePi fun _ ↦ lam,
      mem_invariantFields_shiftGroup.2 ⟨inferInstance, measurePreserving_shift_infinitePi lam⟩⟩
  obtain ⟨κ, hκM, hκ⟩ := exists_isPAKernel_invariantFields_shiftGroup_int hne
  exact ⟨fun ω ↦ specificEntropy lam (κ ω), hκ.measurable_specificEntropy_comp lam,
    fun ω ↦ specificEntropy_nonpos lam, fun μ hμ ↦ hκ.specificEntropy_eq_neg_lintegral lam hμ⟩

omit [IsMarkovKernel κ] in
/-- **Georgii Theorem (15.20), second assertion.** If `μ ∈ 𝓟_Θ` is the barycentre
`μ = ∫ ρ w(dρ)` of a probability weight `w` carried by `𝓟_Θ`, then
`𝓀(μ) = ∫ 𝓀(ρ) w(dρ)` (both sides in `[-∞, 0]`): the specific entropy is not just affine but
"integral-affine". -/
theorem specificEntropy_join_eq_neg_lintegral {w : Measure (Measure ((ι → ℤ) → E))}
    (hw : ∀ᵐ ρ ∂w, ρ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    {μ : Measure ((ι → ℤ) → E)} (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hjoin : w.join = μ) :
    specificEntropy lam μ = -(∫⁻ ρ, (-specificEntropy lam ρ).toENNReal ∂w : EReal) := by
  obtain ⟨κ, hκM, hκ⟩ := exists_isPAKernel_invariantFields_shiftGroup_int ⟨μ, hμ⟩
  have h𝓘 : invariantEvents (shiftGroup (ι → ℤ) E) ≤ MeasurableSpace.pi :=
    fun s hs ↦ (measurableSet_invariantEvents.1 hs).1
  have hKκ : Measurable fun ω ↦
      relativeEntropyIn (lexPast 0) (κ ω) ((κ ω).bind (Specification.isssd lam {0})) :=
    (measurable_relativeEntropyIn_lexPast_kernel lam).mono h𝓘 le_rfl
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hμ 0,
    hκ.relativeEntropyIn_lexPast_eq_lintegral lam hμ, ← hjoin,
    Measure.lintegral_join hKκ.aemeasurable]
  congr 2
  refine lintegral_congr_ae ?_
  filter_upwards [hw] with ρ hρ
  rw [specificEntropy_eq_neg_relativeEntropyIn_lexPast lam hρ 0,
    hκ.relativeEntropyIn_lexPast_eq_lintegral lam hρ, neg_neg, EReal.toENNReal_coe]

end Theorem1520

/-! ### Georgii Proposition (15.14): compactness of the level sets -/

section Compact

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (lam : Measure E)
  [IsProbabilityMeasure lam]

/-- Every finite volume of `ℤ^d` is contained in a box (intended home:
`GibbsMeasure/Mathlib/Analysis/Subadditive/Cubes.lean`). -/
lemma _root_.Finset.exists_isBox_subset (Λ : Finset (ι → ℤ)) :
    ∃ Δ : Finset (ι → ℤ), Δ.IsBox ∧ Λ ⊆ Δ := by
  classical
  set R : ℕ := Λ.sup fun x ↦ Finset.univ.sup fun k ↦ (x k).natAbs with hR
  refine ⟨Icc (fun _ ↦ -(R : ℤ)) fun _ ↦ (R : ℤ), isBox_Icc fun k ↦ by simp, fun x hx ↦ ?_⟩
  have hxR : ∀ k, |x k| ≤ R := fun k ↦ by
    have h1 : (x k).natAbs ≤ Finset.univ.sup fun k ↦ (x k).natAbs :=
      Finset.le_sup (f := fun k ↦ (x k).natAbs) (Finset.mem_univ k)
    have h2 := Finset.le_sup (f := fun x ↦ Finset.univ.sup fun k ↦ (x k).natAbs) hx
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans h2
  exact Finset.mem_Icc.2 ⟨fun k ↦ (abs_le.1 (hxR k)).1, fun k ↦ (abs_le.1 (hxR k)).2⟩

omit [IsProbabilityMeasure lam] in
/-- A level set `{𝓀 ≥ c}` has uniformly bounded finite-volume relative entropies on boxes:
`𝓗_Δ(μ | λ^S) ≤ (-c) |Δ|`. -/
lemma relativeEntropyIn_le_of_le_specificEntropy {μ : Measure ((ι → ℤ) → E)} {c : ℝ}
    (hμ : (c : EReal) ≤ specificEntropy lam μ) {Δ : Finset (ι → ℤ)} (hΔ : Δ.IsBox) :
    relativeEntropyIn (Δ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam)
      ≤ ENNReal.ofReal (-c) * #Δ := by
  have h1 := hμ.trans (specificEntropy_le_entropyIn_div_card lam hΔ)
  rw [entropyIn] at h1
  set H := relativeEntropyIn (Δ : Set (ι → ℤ)) μ (Measure.infinitePi fun _ ↦ lam) with hH_def
  by_cases hH : H = ∞
  · rw [hH, EReal.coe_ennreal_top, EReal.neg_top, EReal.bot_div_natCast hΔ.card_pos.ne'] at h1
    exact absurd h1 (not_le.2 (EReal.bot_lt_coe c))
  rw [neg_coe_ennreal_div_natCast hH, EReal.coe_le_coe_iff, le_neg,
    div_le_iff₀ (by exact_mod_cast hΔ.card_pos)] at h1
  have hc : 0 ≤ -c := by
    have := (div_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg (#Δ))).trans
      ((div_le_iff₀ (by exact_mod_cast hΔ.card_pos)).2 h1)
    nlinarith [(Nat.cast_pos.2 hΔ.card_pos : (0 : ℝ) < #Δ)]
  calc H = ENNReal.ofReal H.toReal := (ENNReal.ofReal_toReal hH).symm
    _ ≤ ENNReal.ofReal (-c * #Δ) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (-c) * #Δ := by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_natCast]

variable [StandardBorelSpace E]

/-- **Georgii Proposition (15.14), compactness.** For a standard Borel state space, the level
sets `{𝓀 ≥ c}` of the specific entropy are compact in the topology of local convergence (on all
random fields; Georgii states it on `𝓟_Θ`). The set is closed by upper semicontinuity, and it
is locally equicontinuous by the uniform absolute continuity `exists_forall_measure_le_of_klDiv_le`
under the entropy bound `relativeEntropyIn_le_of_le_specificEntropy`, so Proposition (4.9)
provides the cluster points. -/
theorem isCompact_setOf_le_specificEntropy (c : ℝ) :
    IsCompact {μ : WithLocalConvergence (ι → ℤ) E |
      (c : EReal) ≤ specificEntropy lam (μ.toMeasure : Measure ((ι → ℤ) → E))} := by
  set K := {μ : WithLocalConvergence (ι → ℤ) E |
    (c : EReal) ≤ specificEntropy lam (μ.toMeasure : Measure ((ι → ℤ) → E))} with hK
  have hclosed : IsClosed K :=
    (upperSemicontinuous_specificEntropy lam).isClosed_preimage (c : EReal)
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro U hU
  have hle : LocallyEquicontinuous (𝓟 K)
      fun μ : WithLocalConvergence (ι → ℤ) E ↦ (id μ).toMeasure := by
    intro Λ A hA hanti hempty
    obtain ⟨Δ, hΔ, hΛΔ⟩ := Finset.exists_isBox_subset Λ
    have hAΔ : ∀ m, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Δ : Set (ι → ℤ))]
        (A m) := fun m ↦ cylinderEvents_mono (Finset.coe_subset.2 hΛΔ) _ (hA m)
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := exists_forall_measure_le_of_klDiv_le
      (b := ENNReal.ofReal (-c) * #Δ) (by finiteness) hε
    have hlam : Tendsto (fun m ↦ (Measure.infinitePi fun _ : ι → ℤ ↦ lam) (A m)) atTop (𝓝 0) := by
      have := tendsto_measure_iInter_atTop (μ := Measure.infinitePi fun _ : ι → ℤ ↦ lam) (s := A)
        (fun m ↦ (cylinderEvents_le_pi _ (hA m)).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
      rwa [hempty, measure_empty] at this
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlam) δ hδ] with m hm
    refine limsup_le_of_le (by isBoundedDefault) ?_
    rw [eventually_principal]
    intro μ hμ
    have hkl := relativeEntropyIn_le_of_le_specificEntropy lam hμ hΔ
    have := hδε _ _ hkl (hAΔ m) (by rwa [trim_measurableSet_eq _ (hAΔ m)])
    rwa [trim_measurableSet_eq _ (hAΔ m)] at this
  obtain ⟨μ, hμ⟩ := exists_tendsto_of_locallyEquicontinuous (μs := id) U hU hle
  exact ⟨μ, hclosed.mem_of_tendsto hμ (Filter.le_principal_iff.1 hU), hμ⟩

end Compact

/-! ### The conditional distribution of one spin given the lexicographic past -/

section ConditionalSpin

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace E] (lam : Measure E)
  [IsProbabilityMeasure lam] {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ]
  {g : ((ι → ℤ) → E) → ℝ≥0∞}

omit [IsProbabilityMeasure μ] in
/-- **Georgii's conditional distribution `q^ω` of the spin at `0` given the past** (the display
after (15.17)): if `μ = g · μ λ_0` on `𝓕_{V(0)}`, then `q^ω(A) = ∫_A g(x ω_{S ∖ 0}) λ(dx)` is a
version of `μ(σ_0 ∈ A | 𝓕_{V*(0)})`, i.e. `∫_B q^ω(A) μ(dω) = μ({σ_0 ∈ A} ∩ B)` for every
`B ∈ 𝓕_{V*(0)}`. -/
theorem setLIntegral_lintegral_update_eq
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g)
    {A : Set E} (hA : MeasurableSet A) {B : Set ((ι → ℤ) → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] B) :
    ∫⁻ ω in B, ∫⁻ x in A, g (update ω 0 x) ∂lam ∂μ = μ ({ω | ω 0 ∈ A} ∩ B) := by
  have hV : cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hg' : Measurable g := hg.mono hV le_rfl
  have hAV : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] {ω | ω 0 ∈ A} :=
    measurable_cylinderEvent_apply (X := fun _ : ι → ℤ ↦ E) (self_mem_lexPast 0) hA
  have hBV : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] B :=
    cylinderEvents_mono Set.sdiff_subset _ hB
  have hBc : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
      ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ))ᶜ)] B :=
    cylinderEvents_mono (fun x hx ↦ by simpa using hx.2) _ hB
  have hC : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)]
    ({ω | ω 0 ∈ A} ∩ B) := hAV.inter hBV
  have hC' : MeasurableSet ({ω | ω 0 ∈ A} ∩ B) := hV _ hC
  have hBm : MeasurableSet B := hV _ hBV
  set ν := μ.bind (Specification.isssd lam {0}) with hν
  have hupd : ∀ ω x, update ω 0 x ∈ B ↔ ω ∈ B := fun ω x ↦
    mem_congr_of_measurableSet_cylinderEvents hBc fun i hi ↦
      Function.update_of_ne (by simpa using hi) x ω
  calc ∫⁻ ω in B, ∫⁻ x in A, g (update ω 0 x) ∂lam ∂μ
      = ∫⁻ ω, ∫⁻ x, ({ω | ω 0 ∈ A} ∩ B).indicator g (update ω 0 x) ∂lam ∂μ := by
        rw [← lintegral_indicator hBm]
        refine lintegral_congr fun ω ↦ ?_
        by_cases hωB : ω ∈ B
        · rw [Set.indicator_of_mem hωB, ← lintegral_indicator hA]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ A
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem]
            exact ⟨by simpa using hx, (hupd ω x).2 hωB⟩
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
            rintro ⟨h1, _⟩
            exact hx (by simpa using h1)
        · rw [Set.indicator_of_notMem hωB]
          refine ((lintegral_congr fun x ↦ ?_).trans lintegral_zero).symm
          rw [Set.indicator_of_notMem]
          rintro ⟨_, h2⟩
          exact hωB ((hupd ω x).1 h2)
    _ = ∫⁻ ω', ({ω | ω 0 ∈ A} ∩ B).indicator g ω' ∂ν := by
        rw [hν, Measure.lintegral_bind (Specification.measurable_isssd_coe _).aemeasurable
          (hg'.indicator hC').aemeasurable]
        refine lintegral_congr fun ω ↦ ?_
        rw [Specification.isssd_singleton_eq_map,
          lintegral_map (hg'.indicator hC') (measurable_update ω)]
    _ = μ ({ω | ω 0 ∈ A} ∩ B) := by
        rw [lintegral_indicator hC', ← lintegral_trim hV hg, ← restrict_trim hV ν hC,
          ← withDensity_apply _ hC, ← hμg, trim_measurableSet_eq hV hC]

/-- The conditional distribution `q^ω` of (15.18) is normalised for `μ`-a.e. `ω`:
`∫ g(x ω_{S ∖ 0}) λ(dx) = 1`. -/
theorem ae_lintegral_update_eq_one
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g) :
    ∀ᵐ ω ∂μ, ∫⁻ x, g (update ω 0 x) ∂lam = 1 := by
  have hV' : cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0}) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  have hgdep : DependsOn g (lexPast 0) := (measurable_cylinderEvents_iff_dependsOn.1 hg).2
  have hGm : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})]
      fun ω ↦ ∫⁻ x, g (update ω 0 x) ∂lam := by
    refine measurable_cylinderEvents_iff_dependsOn.2 ⟨?_, ?_⟩
    · exact Measurable.lintegral_prod_right'
        (f := fun p : ((ι → ℤ) → E) × E ↦ g (update p.1 0 p.2)) (hg'.comp measurable_update')
    · intro ω ω' hωω'
      refine lintegral_congr fun x ↦ hgdep fun i hi ↦ ?_
      by_cases hi0 : i = 0
      · subst hi0
        simp
      · rw [Function.update_of_ne hi0, Function.update_of_ne hi0]
        exact hωω' i ⟨hi, hi0⟩
  have : SigmaFinite (μ.trim hV') := inferInstance
  refine ae_eq_of_ae_eq_trim (hm := hV') (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (μ := μ.trim hV') hGm measurable_const fun B hB _ ↦ ?_)
  rw [restrict_trim hV' μ hB, lintegral_trim _ hGm, lintegral_trim _ measurable_const,
    setLIntegral_const, one_mul]
  have := setLIntegral_lintegral_update_eq lam hg hμg MeasurableSet.univ hB
  simpa using this

/-- Georgii's `q^ω = g(· ω_{S ∖ 0}) λ` is a probability measure for `μ`-a.e. `ω`. -/
theorem ae_isProbabilityMeasure_withDensity_update
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g) :
    ∀ᵐ ω ∂μ, IsProbabilityMeasure (lam.withDensity fun x ↦ g (update ω 0 x)) := by
  filter_upwards [ae_lintegral_update_eq_one lam hg hμg] with ω hω
  exact ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hω]⟩

omit [IsProbabilityMeasure μ] in
/-- **Georgii (15.18)**, as displayed: `𝓀(μ) = -μ(𝓗_ℰ(q^· | λ))` with `q^ω = g(· ω_{S ∖ 0}) λ`
the conditional distribution of the spin at `0` given the lexicographic past, for `μ ∈ 𝓟_Θ` with
`μ = g · μ λ_0` on `𝓕_{V(0)}`. -/
theorem specificEntropy_eq_neg_lintegral_klDiv_withDensity
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g) :
    specificEntropy lam μ
      = -(∫⁻ ω, klDiv (lam.withDensity fun x ↦ g (update ω 0 x)) lam ∂μ : EReal) := by
  have : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  rw [specificEntropy_eq_neg_lintegral_lintegral_klFun lam hμ hg hμg]
  congr 2
  refine lintegral_congr_ae ?_
  filter_upwards [ae_isProbabilityMeasure_withDensity_update lam hg hμg] with ω hω
  rw [klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_withDensity lam (f := fun x ↦ g (update ω 0 x))
    (hg'.comp (measurable_update ω))] with x hx
  rw [hx]

/-- **The conditional distribution `q^ω` of the spin at `0` given the past, as a conditional
expectation** (Georgii's display after (15.17)): `ω ↦ q^ω(A) = ∫_A g(x ω_{S ∖ 0}) λ(dx)` is a
version of `μ(σ_0 ∈ A | 𝓕_{V*(0)})`. -/
theorem toReal_lintegral_update_ae_eq_condExp
    (hg : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g)
    (hμg : μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
      = ((μ.bind (Specification.isssd lam {0})).trim cylinderEvents_le_pi).withDensity g)
    {A : Set E} (hA : MeasurableSet A) :
    (fun ω ↦ (∫⁻ x in A, g (update ω 0 x) ∂lam).toReal)
      =ᵐ[μ] μ[{ω | ω 0 ∈ A}.indicator fun _ ↦ (1 : ℝ) |
        cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] := by
  have hV' : cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0}) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  have hgdep : DependsOn g (lexPast 0) := (measurable_cylinderEvents_iff_dependsOn.1 hg).2
  have hA' : MeasurableSet {ω : (ι → ℤ) → E | ω 0 ∈ A} := measurable_pi_apply 0 hA
  set G : ((ι → ℤ) → E) → ℝ≥0∞ := fun ω ↦ ∫⁻ x in A, g (update ω 0 x) ∂lam with hG
  have hGm : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] G := by
    refine measurable_cylinderEvents_iff_dependsOn.2 ⟨?_, ?_⟩
    · exact Measurable.lintegral_prod_right' (ν := lam.restrict A)
        (f := fun p : ((ι → ℤ) → E) × E ↦ g (update p.1 0 p.2)) (hg'.comp measurable_update')
    · intro ω ω' hωω'
      refine lintegral_congr fun x ↦ hgdep fun i hi ↦ ?_
      by_cases hi0 : i = 0
      · subst hi0
        simp
      · rw [Function.update_of_ne hi0, Function.update_of_ne hi0]
        exact hωω' i ⟨hi, hi0⟩
  have hGm' : Measurable G := hGm.mono hV' le_rfl
  have hle : ∀ᵐ ω ∂μ, G ω ≤ 1 := by
    filter_upwards [ae_lintegral_update_eq_one lam hg hμg] with ω hω
    exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans hω.le
  have hint : Integrable (fun ω ↦ (G ω).toReal) μ := by
    refine Integrable.of_bound hGm'.ennreal_toReal.aestronglyMeasurable 1 ?_
    filter_upwards [hle] with ω hω
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  have : SigmaFinite (μ.trim hV') := inferInstance
  refine ae_eq_condExp_of_forall_setIntegral_eq hV' ((integrable_const _).indicator hA')
    (fun s _ _ ↦ hint.integrableOn) (fun s hs _ ↦ ?_)
    (ENNReal.measurable_toReal.comp hGm).stronglyMeasurable.aestronglyMeasurable
  have hs' : MeasurableSet s := hV' s hs
  rw [integral_toReal hGm'.aemeasurable (ae_restrict_of_ae (hle.mono fun ω hω ↦
      hω.trans_lt ENNReal.one_lt_top)),
    setLIntegral_lintegral_update_eq lam hg hμg hA hs, integral_indicator hA',
    Measure.restrict_restrict hA', setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

end ConditionalSpin

/-! ### Georgii (15.19): finite state space and uniform a priori measure -/

section FiniteState

variable {ι E : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace E] [Fintype E] [Nonempty E]
  [MeasurableSingletonClass E] {μ : Measure ((ι → ℤ) → E)}

omit [LinearOrder ι] in
/-- For a finite state space and the uniform a priori measure, resampling one spin from `λ`
decreases the measure of every event by at most the factor `|E|`: `μ ≤ |E| · μ λ_{j}`. -/
lemma le_card_smul_bind_isssd_singleton_uniformOn (j : ι → ℤ) :
    μ ≤ (Fintype.card E : ℝ≥0∞) • μ.bind (Specification.isssd (uniformOn Set.univ) {j}) := by
  classical
  refine Measure.le_iff.2 fun A hA ↦ ?_
  have hmeas : Measurable fun ω ↦ Specification.isssd (uniformOn (Set.univ : Set E)) {j} ω A :=
    ((Specification.isssd (uniformOn Set.univ) {j}).measurable_coe hA).mono cylinderEvents_le_pi
      le_rfl
  rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hA
    (Specification.measurable_isssd_coe _).aemeasurable, ← lintegral_const_mul _ hmeas,
    ← lintegral_indicator_one hA]
  refine lintegral_mono fun ω ↦ ?_
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Pi.one_apply, Specification.isssd_singleton_eq_map,
      Measure.map_apply (measurable_update ω) hA]
    calc (1 : ℝ≥0∞) = Fintype.card E * uniformOn (Set.univ : Set E) {ω j} := by
          rw [uniformOn_univ, Measure.count_singleton, one_div, ENNReal.mul_inv_cancel
            (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
      _ ≤ Fintype.card E * uniformOn (Set.univ : Set E) (update ω j ⁻¹' A) := by
          gcongr
          refine Set.singleton_subset_iff.2 ?_
          simpa [Set.mem_preimage, Function.update_eq_self] using hω
  · rw [Set.indicator_of_notMem hω]
    exact zero_le

omit [LinearOrder ι] in
/-- For a finite state space and the uniform a priori measure, `μ ≪ μ λ_{j}` on every cylinder
σ-algebra `𝓕_Λ`. -/
lemma absolutelyContinuous_trim_bind_isssd_singleton_uniformOn (Λ : Set (ι → ℤ)) (j : ι → ℤ) :
    μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := Λ))
      ≪ (μ.bind (Specification.isssd (uniformOn Set.univ) {j})).trim cylinderEvents_le_pi :=
  (Measure.absolutelyContinuous_of_le_smul (le_card_smul_bind_isssd_singleton_uniformOn j)).trim _

/-- For a finite state space and the uniform a priori measure, Georgii's density `g` of `μ`
with respect to `μ λ_0` on `𝓕_{V(0)}` always exists. -/
lemma exists_measurable_trim_eq_withDensity_uniformOn [IsProbabilityMeasure μ] :
    ∃ g : ((ι → ℤ) → E) → ℝ≥0∞, Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0)] g
      ∧ μ.trim (cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E) (Δ := lexPast 0))
        = ((μ.bind (Specification.isssd (uniformOn Set.univ) {0})).trim
          cylinderEvents_le_pi).withDensity g :=
  ⟨_, Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _
    (absolutelyContinuous_trim_bind_isssd_singleton_uniformOn _ 0)).symm⟩

/-- **Georgii (15.19).** For a finite state space `E` and the uniform a priori measure
`λ = |E|⁻¹ ∑_x δ_x`, the specific entropy of `μ ∈ 𝓟_Θ` is the conditional Shannon entropy of
the spin at `0` given its lexicographic past, up to the normalisation constant:
`𝓀(μ) = -μ(∑_x μ(σ_0 = x | 𝓕_{V*(0)}) log μ(σ_0 = x | 𝓕_{V*(0)})) - log |E|`. Georgii takes `λ`
to be counting measure, for which the constant `-log |E|` (Georgii: `log λ(E)`) is absent. In
particular `𝓀(μ)` is finite. -/
theorem specificEntropy_uniformOn_eq_neg_integral_sum_mul_log
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy (uniformOn Set.univ) μ
      = ((-∫ ω, ∑ x, (μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
              cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})]) ω
            * log ((μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
              cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})]) ω) ∂μ
          - log (Fintype.card E) : ℝ) : EReal) := by
  classical
  have hprob : IsProbabilityMeasure μ := (mem_invariantFields_shiftGroup.1 hμ).1
  set lam : Measure E := uniformOn Set.univ with hlam
  obtain ⟨g, hg, hμg⟩ := exists_measurable_trim_eq_withDensity_uniformOn (μ := μ)
  have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  set p : E → ((ι → ℤ) → E) → ℝ := fun x ↦ μ[{ω | ω 0 = x}.indicator fun _ ↦ (1 : ℝ) |
    cylinderEvents (X := fun _ : ι → ℤ ↦ E) (lexPast 0 \ {0})] with hp
  set q : ((ι → ℤ) → E) → E → ℝ := fun ω x ↦ (lam.withDensity fun y ↦ g (update ω 0 y)).real {x}
    with hq
  have hqm : ∀ x, Measurable fun ω ↦ q ω x := fun x ↦ by
    simp only [hq, measureReal_def, withDensity_apply _ (measurableSet_singleton x),
      lintegral_singleton]
    exact ((hg'.comp measurable_update_left).mul_const _).ennreal_toReal
  -- `q^·{x}` is a version of the conditional probability `p x`
  have hqp : ∀ᵐ ω ∂μ, ∀ x, q ω x = p x ω := by
    refine ae_all_iff.2 fun x ↦ ?_
    have := toReal_lintegral_update_ae_eq_condExp lam hg hμg (measurableSet_singleton x)
    filter_upwards [this] with ω hω
    simp only [hq, measureReal_def, withDensity_apply _ (measurableSet_singleton x)]
    rw [hω]
    rfl
  -- for a.e. `ω`, `q^ω` is a probability vector
  have hqprob : ∀ᵐ ω ∂μ, (∀ x, 0 ≤ q ω x) ∧ ∑ x, q ω x = 1 := by
    filter_upwards [ae_isProbabilityMeasure_withDensity_update lam hg hμg] with ω hω
    exact ⟨fun x ↦ measureReal_nonneg, by
      simp only [hq]
      rw [sum_measureReal_singleton, Finset.coe_univ, probReal_univ]⟩
  set F : ((ι → ℤ) → E) → ℝ := fun ω ↦ ∑ x, q ω x * log (q ω x) + log (Fintype.card E) with hF
  have hFm : Measurable F :=
    (Finset.measurable_sum _ fun x _ ↦ (hqm x).mul ((hqm x).log)).add_const _
  have hF_nn : 0 ≤ᵐ[μ] F := by
    filter_upwards [hqprob] with ω hω
    simp only [hF, Pi.zero_apply]
    have := Real.neg_log_card_le_sum_mul_log hω.1 hω.2
    linarith
  have hF_int : Integrable F μ := by
    refine Integrable.of_bound hFm.aestronglyMeasurable (Fintype.card E + |log (Fintype.card E)|)
      ?_
    filter_upwards [hqprob] with ω hω
    have hterm : ∀ x, |q ω x * log (q ω x)| ≤ 1 := fun x ↦ by
      rcases (hω.1 x).eq_or_lt with h | h
      · simp [← h]
      · have hle : q ω x ≤ 1 := by
          calc q ω x ≤ ∑ y, q ω y := Finset.single_le_sum (fun y _ ↦ hω.1 y) (Finset.mem_univ x)
            _ = 1 := hω.2
        rw [mul_comm]
        exact (abs_log_mul_self_lt _ h hle).le
    simp only [hF, Real.norm_eq_abs]
    calc |∑ x, q ω x * log (q ω x) + log (Fintype.card E)|
        ≤ |∑ x, q ω x * log (q ω x)| + |log (Fintype.card E)| := abs_add_le _ _
      _ ≤ ∑ x, |q ω x * log (q ω x)| + |log (Fintype.card E)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : E, (1 : ℝ) + |log (Fintype.card E)| := by
          gcongr with x
          exact hterm x
      _ = Fintype.card E + |log (Fintype.card E)| := by simp
  -- the relative entropy of `q^ω` with respect to `λ` is Shannon's formula
  have hkl : ∀ᵐ ω ∂μ, klDiv (lam.withDensity fun x ↦ g (update ω 0 x)) lam
      = ENNReal.ofReal (F ω) := by
    filter_upwards [ae_isProbabilityMeasure_withDensity_update lam hg hμg] with ω hω
    rw [hlam, klDiv_uniformOn_univ]
  rw [specificEntropy_eq_neg_lintegral_klDiv_withDensity lam hμ hg hμg, lintegral_congr_ae hkl,
    ← ofReal_integral_eq_lintegral_ofReal hF_int hF_nn, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg_of_ae hF_nn), ← EReal.coe_neg, EReal.coe_eq_coe_iff]
  have hFp : F =ᵐ[μ] fun ω ↦ ∑ x, p x ω * log (p x ω) + log (Fintype.card E) := by
    filter_upwards [hqp] with ω hω
    simp only [hF, hω]
  rw [integral_congr_ae hFp, integral_add ?_ (integrable_const _), integral_const, smul_eq_mul,
    probReal_univ, one_mul, neg_add]
  · rfl
  · have : (fun ω ↦ ∑ x, p x ω * log (p x ω)) =ᵐ[μ] fun ω ↦ F ω - log (Fintype.card E) := by
      filter_upwards [hqp] with ω hω
      simp only [hF, hω, add_sub_cancel_right]
    exact (hF_int.sub (integrable_const _)).congr this.symm

/-- For a finite state space the specific entropy is finite. -/
lemma specificEntropy_uniformOn_ne_bot (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) :
    specificEntropy (uniformOn Set.univ) μ ≠ ⊥ := by
  rw [specificEntropy_uniformOn_eq_neg_integral_sum_mul_log hμ]
  exact EReal.coe_ne_bot _

end FiniteState

end MeasureTheory.GibbsMeasure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Singleton
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import GibbsMeasure.Prereqs.IntervalBoundary
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Potential.Existence

/-!
# Georgii §10.1: Markov fields and Markov chains on `ℤ` with a general state space

Sites `ℤ`, an arbitrary measurable state space `(E, 𝓔)`. This file formalises Georgii,
Definition (10.2), Example (10.3), Definition (10.4) with (10.5)–(10.8), Remark (10.9) with the
local Markov property (10.10), and the identification of the finite-state objects of Chapter 3
(`GibbsMeasure/Model/MarkovChain.lean`) as instances.

## Conditional expectations of indicators

The whole section is a calculus of identities `μ(A | m₀) = μ(A | m')` between conditional
probabilities. The σ-algebra-level lemmas, stated for an arbitrary finite measure, are:

* `MeasureTheory.condExp_indicator_ae_eq_iff_forall_setIntegral`,
  `MeasureTheory.condExp_indicator_ae_eq_iff_forall_setIntegral'`: `μ(A | m₀) = μ(A | m')`
  (`m' ≤ m₀`) iff `∫_D μ(A | m') = μ(A ∩ D)` for all `D ∈ m₀`, iff `∫_A μ(D | m') = μ(A ∩ D)`;
* `MeasureTheory.integral_mul_indicator_eq_of_condExp_ae_eq`: its functional form
  `∫ f 1_A = ∫ f μ(A | m')` for bounded `m₀`-measurable `f`;
* `MeasureTheory.condExp_indicator_ae_eq_of_le`: the tower property for these identities;
* `MeasureTheory.condExp_indicator_ae_eq_sup`: absorbing `m'` into the events (`A ∈ m ⊔ m'`);
* `MeasureTheory.condExp_indicator_ae_eq_symm`: symmetry (conditional independence is
  symmetric);
* `MeasureTheory.setIntegral_eq_of_generateFrom`: Georgii's "standard extension argument"
  (a π-λ argument for set integrals).

## Markov properties of a measure on `E^ℤ`

* `boundarySet`: Georgii's boundary `∂V` of an arbitrary `V ⊆ ℤ` (`coe_boundary` identifies it
  with Chapter 3's `boundary` on finite volumes).
* `IsMarkovOn μ V`: the Markov property (10.10) at `V`, `μ(A | 𝓕_{ℤ∖V}) = μ(A | 𝓕_{∂V})` for
  `A ∈ 𝓕_V`; `IsLocalMarkov` (all finite `V`), `IsGlobalMarkov` (all `V`).
* `IsMarkovField` (10.6), `IsLeftMarkov` (10.7), `IsRightMarkov` (10.8), `IsOneSidedMarkov`.
* `IsMarkovOn.union`: Georgii's step 1) — (10.10) is stable under disjoint non-adjacent unions.
* `IsMarkovOn.of_forall_component`: (10.10) at `V` follows from (10.10) at the maximal intervals
  of `V` (`component`, `hull`), by the extension argument over finitely many sites.
* `isLeftMarkov_iff_isRightMarkov`: the equivalence of (10.7) and (10.8) stated after (10.8).
* `IsOneSidedMarkov.isMarkovField`: **Remark (10.9)(3)**.
* `isMarkovField_iff_isLocalMarkov`: **Remark (10.9)(1)**.
* `isOneSidedMarkov_iff_isGlobalMarkov`: **Remark (10.9)(2)**.

## Markov chains, Definition (10.4)

* `rect`, `rectangles`: rectangles over finite sets of sites and the π-systems they form
  (`cylinderEvents_eq_generateFrom_rectangles`).
* `chainKernel P hB n k`: the kernel `∫_{B_{k+1}} P_{k+1}(x, dx_1) ⋯ ∫_{B_{k+n}} P_{k+n}(x_{n-1}, ·)`
  of (10.5), as a composition of restricted kernels.
* `IsMarkovChain P μ`: **Definition (10.4)** via (ii),
  `μ(σ_i ∈ A | 𝓕_{]-∞,i[}) = P_i(σ_{i-1}, A)` a.s.
* `IsMarkovChain.measure_rect`: **(10.5)**, and `isMarkovChain_iff_forall_measure_rect`:
  **(10.4)(i) ⟺ (ii)** for probability kernels.
* `IsMarkovChain.map_restrict_inter_rect`: the finite-dimensional distributions in measure form.
* `IsMarkovChain.isLeftMarkov` (10.7), `IsMarkovChain.isRightMarkov` (10.8),
  `IsMarkovChain.isMarkovField`, `IsMarkovChain.isGlobalMarkov`.

## Markov specifications, Definition (10.2) and Example (10.3)

* `Specification.IsMarkovInt γ`: **Definition (10.2)**, `γ_{]i,k[}(A | ·)` is
  `𝓕_{{i,k}}`-measurable for `A ∈ 𝓕_{]i,k[}`; `Specification.IsMarkovianInt ρ`: `ρ_{]i,k[}` is
  `𝓕_{[i,k]}`-measurable.
* `Specification.isMarkovInt_lambdaSpecification`,
  `Specification.isMarkovInt_of_forall_apply_eq`: Georgii's remark that `ρλ` is Markov when
  `ρ` is Markovian, for σ-finite and for probability a priori measures.
* `Specification.chainDensity p`: Georgii's `g_{i,k}(ω) = ∏_{j=i+1}^{k} p_j(ω_{j-1}, ω_j)` of
  **Example (10.3)**, a Markovian pre-modification (`isPremodifier_chainDensity`,
  `isMarkovianInt_chainDensity`); `Specification.chainSpecification`: the Markov specification
  `ρλ` it defines under λ-admissibility, which holds for positive bounded densities
  (`isPremodifierAdmissible_chainDensity`). Georgii's fallback `ρ_{]i,k[} = g_{i,k-1}` on
  `{Z_{i,k} = 0}` for non-admissible densities is not formalised.

## Example (10.11)

* `IsMarkovChain.map_prodMk_eq_compProd`: the joint law of `(σ_i, σ_{i+n})` is the
  composition-product of the law of `σ_i` with the chain kernel.
* `lintegral_chainKernel_eq_lintegral_isssd`: for kernels with densities
  `P_j(x, dy) = p_j(x, y) λ(dy)`, the chain kernel is an integral against the independent
  resampling of the sites `k+1, …, k+n` weighted by `∏ p_j`;
  `chainKernel_univ_eq_withDensity_Ztilde`: the `n`-step kernel has density `Z_{i,i+n}(x, ·)`.
* `IsMarkovChain.measure_rect_inter_eq_lintegral_chainSpecification`: Georgii's identity
  `μ(σ_i ∈ A, σ_{]i,k[} ∈ B, σ_k ∈ C) = ∫_{σ_i ∈ A, σ_k ∈ C} γ_{]i,k[}(σ_{]i,k[} ∈ B | ·) dμ`.
* `IsMarkovChain.isGibbsMeasure_chainSpecification`: **Example (10.11)** — a Markov chain with
  transition densities `p_i` as in (10.3) (λ-admissible) is a Gibbs measure for `γ = ρλ`.

## Chapter 3 as an instance

* `isMarkovInt_markovSpecification`: Georgii's `γ_P` of a stochastic matrix (Chapter 3) is a
  Markov specification in the sense of (10.2).
* `isMarkovChain_stationaryChain`: the stationary chain `μ_P` of Georgii (3.3) is a Markov chain
  in the sense of (10.4) for any kernel with point masses `P(x, y)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m m' m₀ m₁ : MeasurableSpace Ω}
  {A B C D : Set Ω}

section Indicator

omit mΩ in
lemma indicator_inter_one_eq (B C : Set Ω) :
    (B ∩ C).indicator (1 : Ω → ℝ) = C.indicator (B.indicator (1 : Ω → ℝ)) := by
  rw [indicator_indicator, inter_comm]

lemma integrable_indicator_one (hA : MeasurableSet[mΩ] A) [IsFiniteMeasure μ] :
    Integrable (A.indicator (1 : Ω → ℝ)) μ :=
  (integrable_const (1 : ℝ)).indicator hA

lemma ae_abs_indicator_one_le (A : Set Ω) : ∀ᵐ x ∂μ, |A.indicator (1 : Ω → ℝ) x| ≤ (1 : ℝ) :=
  ae_of_all _ fun x ↦ by
    by_cases hx : x ∈ A <;> simp [hx]

lemma ae_abs_condExp_indicator_one_le (m : MeasurableSpace Ω) (A : Set Ω) :
    ∀ᵐ x ∂μ, |(μ[A.indicator (1 : Ω → ℝ) | m]) x| ≤ (1 : ℝ) :=
  ae_bdd_abs_condExp_of_ae_bdd_abs (ae_abs_indicator_one_le A)

lemma ae_norm_condExp_indicator_one_le (m : MeasurableSpace Ω) (A : Set Ω) :
    ∀ᵐ x ∂μ, ‖(μ[A.indicator (1 : Ω → ℝ) | m]) x‖ ≤ (1 : ℝ) := by
  simpa [Real.norm_eq_abs] using ae_abs_condExp_indicator_one_le (μ := μ) m A

lemma setIntegral_indicator_one' (hA : MeasurableSet[mΩ] A) (t : Set Ω) :
    ∫ x in t, A.indicator (1 : Ω → ℝ) x ∂μ = μ.real (A ∩ t) :=
  setIntegral_indicator_one (m0 := mΩ) μ hA t

lemma integral_mul_indicator_one (hD : MeasurableSet[mΩ] D) (f : Ω → ℝ) :
    ∫ x, f x * D.indicator (1 : Ω → ℝ) x ∂μ = ∫ x in D, f x ∂μ := by
  rw [← integral_indicator hD]
  congr 1
  ext x
  by_cases hx : x ∈ D <;> simp [hx]


omit mΩ in
lemma stronglyMeasurable_indicator_one (hA : MeasurableSet[m] A) :
    StronglyMeasurable[m] (A.indicator (1 : Ω → ℝ)) :=
  stronglyMeasurable_const.indicator hA

lemma ae_norm_indicator_one_le (A : Set Ω) : ∀ᵐ x ∂μ, ‖A.indicator (1 : Ω → ℝ) x‖ ≤ 1 :=
  ae_of_all _ fun x ↦ by by_cases hx : x ∈ A <;> simp [hx]

lemma ae_norm_mul_le_one {f g : Ω → ℝ} (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) (hg : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1) :
    ∀ᵐ x ∂μ, ‖f x * g x‖ ≤ 1 := by
  filter_upwards [hf, hg] with x hfx hgx
  rw [norm_mul]
  exact mul_le_one₀ hfx (norm_nonneg _) hgx

lemma setIntegral_inter_eq_integral_mul (hB : MeasurableSet[mΩ] B) (hC : MeasurableSet[mΩ] C)
    (g : Ω → ℝ) :
    ∫ x in B ∩ C, g x ∂μ = ∫ x, B.indicator (1 : Ω → ℝ) x * (C.indicator 1 x * g x) ∂μ := by
  rw [← integral_indicator (hB.inter hC)]
  congr 1
  ext x
  by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C <;> simp [hxB, hxC]

end Indicator

section PiSystem

/-- The intersections `B ∩ C` with `B` measurable for `m₁` and `C` measurable for `m₂`. -/
def interSets (m₁ m₂ : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ B C, MeasurableSet[m₁] B ∧ MeasurableSet[m₂] C ∧ s = B ∩ C}

omit mΩ in
lemma isPiSystem_interSets (m₁ m₂ : MeasurableSpace Ω) : IsPiSystem (interSets m₁ m₂) := by
  rintro _ ⟨B, C, hB, hC, rfl⟩ _ ⟨B', C', hB', hC', rfl⟩ -
  exact ⟨B ∩ B', C ∩ C', hB.inter hB', hC.inter hC', by ext; simp; tauto⟩

omit mΩ in
lemma univ_mem_interSets (m₁ m₂ : MeasurableSpace Ω) : univ ∈ interSets m₁ m₂ :=
  ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by simp⟩

omit mΩ in
lemma measurableSet_sup_of_mem_interSets {s : Set Ω} (hs : s ∈ interSets m₁ m) :
    MeasurableSet[m₁ ⊔ m] s := by
  obtain ⟨B, C, hB, hC, rfl⟩ := hs
  have h1 : m₁ ≤ m₁ ⊔ m := le_sup_left
  have h2 : m ≤ m₁ ⊔ m := le_sup_right
  exact (h1 _ hB).inter (h2 _ hC)

omit mΩ in
/-- `m₁ ⊔ m₂` is generated by the π-system of intersections `B ∩ C`. -/
lemma sup_eq_generateFrom_interSets (m₁ m₂ : MeasurableSpace Ω) :
    m₁ ⊔ m₂ = MeasurableSpace.generateFrom (interSets m₁ m₂) := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le fun s hs ↦
    measurableSet_sup_of_mem_interSets hs)
  · intro B hB
    exact MeasurableSpace.measurableSet_generateFrom ⟨B, univ, hB, MeasurableSet.univ, by simp⟩
  · intro C hC
    exact MeasurableSpace.measurableSet_generateFrom ⟨univ, C, MeasurableSet.univ, hC, by simp⟩

/-- Two integrable functions with the same integral over every set of a π-system generating `m`
and over `univ` have the same integral over every `m`-measurable set. -/
lemma setIntegral_eq_of_generateFrom (hm : m ≤ mΩ) {𝒞 : Set (Set Ω)} (h𝒞 : IsPiSystem 𝒞)
    (hgen : m = MeasurableSpace.generateFrom 𝒞) {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (h : ∀ s ∈ 𝒞, ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (huniv : ∫ x, f x ∂μ = ∫ x, g x ∂μ) :
    ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ := by
  refine MeasurableSpace.induction_on_inter (m := m)
    (C := fun s _ ↦ ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) hgen h𝒞 (by simp) (fun t ht ↦ h t ht)
    (fun t ht hts ↦ ?_) (fun s hd hs hts ↦ ?_)
  · have hf' := integral_add_compl (hm _ ht) hf
    have hg' := integral_add_compl (hm _ ht) hg
    linarith
  · rw [integral_iUnion (fun i ↦ hm _ (hs i)) hd hf.integrableOn,
      integral_iUnion (fun i ↦ hm _ (hs i)) hd hg.integrableOn]
    exact tsum_congr hts

end PiSystem

section CondExp

variable [IsFiniteMeasure μ]

/-- Pull-out: `∫ μ(A|m) 1_D = ∫ μ(A|m) μ(D|m)`. -/
lemma integral_condExp_indicator_mul_indicator (hm : m ≤ mΩ) (A : Set Ω)
    (hD : MeasurableSet[mΩ] D) :
    ∫ x, (μ[A.indicator (1 : Ω → ℝ) | m]) x * D.indicator (1 : Ω → ℝ) x ∂μ
      = ∫ x, (μ[A.indicator (1 : Ω → ℝ) | m]) x * (μ[D.indicator (1 : Ω → ℝ) | m]) x ∂μ := by
  rw [← integral_condExp hm (f := fun x ↦ (μ[A.indicator (1 : Ω → ℝ) | m]) x * D.indicator (1 : Ω
      → ℝ) x)]
  exact integral_congr_ae (condExp_stronglyMeasurable_mul_of_bound hm stronglyMeasurable_condExp
    (integrable_indicator_one hD) 1 (ae_norm_condExp_indicator_one_le m A))

/-- Symmetry of the conditional covariance: `∫_D μ(A|m) = ∫_A μ(D|m)`. -/
lemma setIntegral_condExp_indicator_comm (hm : m ≤ mΩ) (hA : MeasurableSet[mΩ] A)
    (hD : MeasurableSet[mΩ] D) :
    ∫ x in D, (μ[A.indicator (1 : Ω → ℝ) | m]) x ∂μ = ∫ x in A, (μ[D.indicator (1 : Ω → ℝ) | m])
        x ∂μ := by
  rw [← integral_mul_indicator_one hD, ← integral_mul_indicator_one hA,
    integral_condExp_indicator_mul_indicator hm A hD,
    integral_condExp_indicator_mul_indicator hm D hA]
  simp_rw [mul_comm]

/-- Georgii's `μ(A | m₀) = μ(A | m')` for a sub-σ-algebra `m' ≤ m₀`, characterised on the
conditioning side: `∫_D μ(A|m') = μ(A ∩ D)` for all `D ∈ m₀`. -/
lemma condExp_indicator_ae_eq_iff_forall_setIntegral (hm' : m' ≤ m₀) (hm₀ : m₀ ≤ mΩ)
    (hA : MeasurableSet[mΩ] A) :
    μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m'] ↔
      ∀ D, MeasurableSet[m₀] D → ∫ x in D, (μ[A.indicator (1 : Ω → ℝ) | m']) x ∂μ = μ.real (A ∩
          D) := by
  constructor
  · intro h D hD
    rw [← setIntegral_indicator_one' hA D, ← setIntegral_condExp hm₀ (integrable_indicator_one
        hA) hD]
    exact setIntegral_congr_ae (hm₀ _ hD) (h.mono fun x hx _ ↦ hx.symm)
  · intro h
    refine (ae_eq_condExp_of_forall_setIntegral_eq hm₀ (integrable_indicator_one hA)
      (fun s _ _ ↦ integrable_condExp.integrableOn) (fun s hs _ ↦ ?_)
      (stronglyMeasurable_condExp.mono hm').aestronglyMeasurable).symm
    rw [h s hs, setIntegral_indicator_one' hA s]

/-- Georgii's `μ(A | m₀) = μ(A | m')` characterised on the event side:
`∫_A μ(D|m') = μ(A ∩ D)` for all `D ∈ m₀`. -/
lemma condExp_indicator_ae_eq_iff_forall_setIntegral' (hm' : m' ≤ m₀) (hm₀ : m₀ ≤ mΩ)
    (hA : MeasurableSet[mΩ] A) :
    μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m'] ↔
      ∀ D, MeasurableSet[m₀] D → ∫ x in A, (μ[D.indicator (1 : Ω → ℝ) | m']) x ∂μ = μ.real (A ∩
          D) := by
  rw [condExp_indicator_ae_eq_iff_forall_setIntegral hm' hm₀ hA]
  refine forall₂_congr fun D hD ↦ ?_
  rw [setIntegral_condExp_indicator_comm (hm'.trans hm₀) hA (hm₀ _ hD)]

/-- The functional form of `μ(A | m₀) = μ(A | m')`: for every bounded `m₀`-measurable `f`,
`∫ f 1_A = ∫ f μ(A|m')`. -/
lemma integral_mul_indicator_eq_of_condExp_ae_eq (hm₀ : m₀ ≤ mΩ)
    (hA : MeasurableSet[mΩ] A) (h : μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω →
        ℝ) | m'])
    {f : Ω → ℝ} (hf : StronglyMeasurable[m₀] f) {c : ℝ} (hfc : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂μ = ∫ x, f x * (μ[A.indicator (1 : Ω → ℝ) | m']) x ∂μ
        := by
  rw [← integral_condExp hm₀ (f := fun x ↦ f x * A.indicator (1 : Ω → ℝ) x)]
  refine integral_congr_ae ((condExp_stronglyMeasurable_mul_of_bound hm₀ hf
    (integrable_indicator_one hA) c hfc).trans ?_)
  exact h.mono fun x hx ↦ by simp only [Pi.mul_apply, hx]

/-- Tower: for `m`-measurable bounded `f`, `∫ f 1_A = ∫ f μ(A|m)`. -/
lemma integral_mul_indicator_eq_integral_mul_condExp (hm : m ≤ mΩ) (hA : MeasurableSet[mΩ] A)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) {c : ℝ} (hfc : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂μ = ∫ x, f x * (μ[A.indicator (1 : Ω → ℝ) | m]) x ∂μ :=
  integral_mul_indicator_eq_of_condExp_ae_eq hm hA (ae_eq_refl _) hf hfc

/-- Monotonicity in the conditioning σ-algebra: if `μ(A|m₀) = μ(A|m')` and `m' ≤ m₁ ≤ m₀`, then
`μ(A|m₁) = μ(A|m')`. -/
lemma condExp_indicator_ae_eq_of_le (hm'₁ : m' ≤ m₁) (hm₁₀ : m₁ ≤ m₀) (hm₀ : m₀ ≤ mΩ) (h :
    μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m']) :
    μ[A.indicator (1 : Ω → ℝ) | m₁] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m'] := by
  calc μ[A.indicator (1 : Ω → ℝ) | m₁] =ᵐ[μ] μ[μ[A.indicator (1 : Ω → ℝ) | m₀] | m₁] :=
        (condExp_condExp_of_le (μ := μ) hm₁₀ hm₀).symm
    _ =ᵐ[μ] μ[μ[A.indicator (1 : Ω → ℝ) | m'] | m₁] := condExp_congr_ae h
    _ = μ[A.indicator (1 : Ω → ℝ) | m'] := condExp_of_stronglyMeasurable (μ := μ) (hm₁₀.trans hm₀)
        (stronglyMeasurable_condExp.mono hm'₁) integrable_condExp

/-- Absorbing the conditioning σ-algebra into the events: if `μ(A|m₀) = μ(A|m')` for all
`A ∈ m`, then also for all `A ∈ m ⊔ m'`. -/
lemma condExp_indicator_ae_eq_sup (hm' : m' ≤ m₀) (hm₀ : m₀ ≤ mΩ) (hm : m ≤ mΩ)
    (h : ∀ A, MeasurableSet[m] A →
      μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m']) :
    ∀ A, MeasurableSet[m ⊔ m'] A →
      μ[A.indicator (1 : Ω → ℝ) | m₀] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m'] := by
  have hsup : m ⊔ m' ≤ mΩ := sup_le hm (hm'.trans hm₀)
  intro A hA
  rw [condExp_indicator_ae_eq_iff_forall_setIntegral' hm' hm₀ (hsup _ hA)]
  intro D hD
  have hD' : MeasurableSet[mΩ] D := hm₀ _ hD
  rw [inter_comm, ← setIntegral_indicator_one' hD' A]
  refine setIntegral_eq_of_generateFrom hsup (isPiSystem_interSets m m')
    (sup_eq_generateFrom_interSets m m') integrable_condExp (integrable_indicator_one hD')
    ?_ (integral_condExp (μ := μ) (hm'.trans hm₀)) A hA
  · rintro _ ⟨B, C, hB, hC, rfl⟩
    have hB' : MeasurableSet[mΩ] B := hm _ hB
    have hC' : MeasurableSet[mΩ] C := hm₀ _ (hm' _ hC)
    have hBC' : MeasurableSet[mΩ] (B ∩ C) := hB'.inter hC'
    rw [← setIntegral_condExp_indicator_comm (hm'.trans hm₀) hBC' hD',
      setIntegral_indicator_one' hD' (B ∩ C), inter_comm D (B ∩ C),
      ← setIntegral_indicator_one' hBC' D,
      ← setIntegral_condExp hm₀ (integrable_indicator_one hBC') hD]
    refine setIntegral_congr_ae hD' ?_
    have h1 := condExp_indicator (m := m') (μ := μ) (integrable_indicator_one hB') hC
    have h2 := condExp_indicator (m := m₀) (μ := μ) (integrable_indicator_one hB') (hm' _ hC)
    rw [indicator_inter_one_eq]
    filter_upwards [h1, h2, h B hB] with x hx1 hx2 hx3
    intro _
    rw [hx1, hx2]
    by_cases hx : x ∈ C <;> simp [hx, hx3]

/-- Symmetry: if `μ(A | m₁) = μ(A | m')` for all `A ∈ m₂`, then `μ(A | m₂) = μ(A | m')` for all
`A ∈ m₁` (both say that `m₁` and `m₂` are conditionally independent given `m' ≤ m₁ ⊓ m₂`). -/
lemma condExp_indicator_ae_eq_symm {m₂ : MeasurableSpace Ω} (hm'₁ : m' ≤ m₁) (hm'₂ : m' ≤ m₂)
    (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    (h : ∀ A, MeasurableSet[m₂] A →
      μ[A.indicator (1 : Ω → ℝ) | m₁] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m']) :
    ∀ A, MeasurableSet[m₁] A →
      μ[A.indicator (1 : Ω → ℝ) | m₂] =ᵐ[μ] μ[A.indicator (1 : Ω → ℝ) | m'] := by
  intro A hA
  have hA' : MeasurableSet[mΩ] A := hm₁ _ hA
  rw [condExp_indicator_ae_eq_iff_forall_setIntegral hm'₂ hm₂ hA']
  intro D hD
  have hD' : MeasurableSet[mΩ] D := hm₂ _ hD
  have h1 := integral_mul_indicator_eq_of_condExp_ae_eq hm₁ hD' (h D hD)
    (stronglyMeasurable_indicator_one hA) (ae_norm_indicator_one_le A)
  have h2 := integral_mul_indicator_eq_integral_mul_condExp (μ := μ) (hm'₁.trans hm₁) hA'
    (f := μ[D.indicator (1 : Ω → ℝ) | m']) stronglyMeasurable_condExp
    (ae_norm_condExp_indicator_one_le m' D)
  have h3 := integral_mul_indicator_eq_of_condExp_ae_eq hm₁ hD' (h D hD)
    (f := μ[A.indicator (1 : Ω → ℝ) | m']) (stronglyMeasurable_condExp.mono hm'₁)
    (ae_norm_condExp_indicator_one_le m' A)
  rw [← setIntegral_indicator_one' hA' D, ← integral_mul_indicator_one hD',
    ← integral_mul_indicator_one hD']
  calc ∫ x, (μ[A.indicator (1 : Ω → ℝ) | m']) x * D.indicator 1 x ∂μ
      = ∫ x, (μ[A.indicator (1 : Ω → ℝ) | m']) x * (μ[D.indicator (1 : Ω → ℝ) | m']) x ∂μ := h3
    _ = ∫ x, (μ[D.indicator (1 : Ω → ℝ) | m']) x * (μ[A.indicator (1 : Ω → ℝ) | m']) x ∂μ := by
        congr 1; funext x; ring
    _ = ∫ x, (μ[D.indicator (1 : Ω → ℝ) | m']) x * A.indicator 1 x ∂μ := h2.symm
    _ = ∫ x, A.indicator (1 : Ω → ℝ) x * (μ[D.indicator (1 : Ω → ℝ) | m']) x ∂μ := by
        congr 1; funext x; ring
    _ = ∫ x, A.indicator (1 : Ω → ℝ) x * D.indicator 1 x ∂μ := h1.symm

end CondExp

end MeasureTheory

/-! ## Georgii §10.1: Markov properties of measures on `E^ℤ` -/

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] {μ : Measure (ℤ → E)} {V W : Set ℤ} {A : Set (ℤ → E)}

/-! ### Intervals and boundaries in `ℤ` -/

/-- Georgii's boundary `∂V = {i ∈ ℤ ∖ V : |i - j| = 1 for some j ∈ V}` of an arbitrary
`V ⊆ ℤ`. For a finite volume this is `Markov.boundary` (`coe_boundary`). -/
def boundarySet (V : Set ℤ) : Set ℤ := {i | i ∉ V ∧ (i + 1 ∈ V ∨ i - 1 ∈ V)}

lemma mem_boundarySet {i : ℤ} : i ∈ boundarySet V ↔ i ∉ V ∧ (i + 1 ∈ V ∨ i - 1 ∈ V) := Iff.rfl

lemma boundarySet_subset_compl (V : Set ℤ) : boundarySet V ⊆ Vᶜ := fun _ h ↦ h.1

lemma disjoint_boundarySet (V : Set ℤ) : Disjoint V (boundarySet V) :=
  Set.disjoint_left.2 fun _ hi hb ↦ hb.1 hi

/-- The set boundary of a finite volume is Georgii's (3.4) boundary of Chapter 3. -/
lemma coe_boundary (Λ : Finset ℤ) : (boundary Λ : Set ℤ) = boundarySet (Λ : Set ℤ) := by
  ext i
  simp only [Finset.mem_coe, mem_boundary, mem_boundarySet]
  constructor
  · rintro ⟨hi, j, hj, habs⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs
    refine ⟨hi, ?_⟩
    rcases habs with h | h
    · exact Or.inr (by rw [show i - 1 = j by omega]; exact hj)
    · exact Or.inl (by rw [show i + 1 = j by omega]; exact hj)
  · rintro ⟨hi, h | h⟩
    · exact ⟨hi, _, h, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩
    · exact ⟨hi, _, h, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩

@[simp] lemma boundarySet_univ : boundarySet (Set.univ : Set ℤ) = ∅ := by
  ext i; simp [mem_boundarySet]

@[simp] lemma boundarySet_empty : boundarySet (∅ : Set ℤ) = ∅ := by
  ext i; simp [mem_boundarySet]

lemma boundarySet_Ioo {i k : ℤ} (h : i + 1 < k) : boundarySet (Set.Ioo i k) = {i, k} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

lemma boundarySet_Icc {a b : ℤ} (h : a ≤ b) : boundarySet (Set.Icc a b) = {a - 1, b + 1} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

@[simp] lemma boundarySet_Ioi (i : ℤ) : boundarySet (Set.Ioi i) = {i} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Ioi, Set.mem_singleton_iff]
  omega

@[simp] lemma boundarySet_Iio (i : ℤ) : boundarySet (Set.Iio i) = {i} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Iio, Set.mem_singleton_iff]
  omega

@[simp] lemma boundarySet_Ici (i : ℤ) : boundarySet (Set.Ici i) = {i - 1} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Ici, Set.mem_singleton_iff]
  omega

@[simp] lemma boundarySet_Iic (i : ℤ) : boundarySet (Set.Iic i) = {i + 1} := by
  ext j
  simp only [mem_boundarySet, Set.mem_Iic, Set.mem_singleton_iff]
  omega

lemma Ioo_eq_empty_of_le {i k : ℤ} (h : k ≤ i + 1) : Set.Ioo i k = ∅ := by
  ext j; simp only [Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]; omega

lemma Icc_eq_Ioo (a b : ℤ) : Set.Icc a b = Set.Ioo (a - 1) (b + 1) := by
  ext j; simp only [Set.mem_Icc, Set.mem_Ioo]; omega

lemma Ici_eq_Ioi (a : ℤ) : Set.Ici a = Set.Ioi (a - 1) := by
  ext j; simp only [Set.mem_Ici, Set.mem_Ioi]; omega

lemma Iic_eq_Iio (b : ℤ) : Set.Iic b = Set.Iio (b + 1) := by
  ext j; simp only [Set.mem_Iic, Set.mem_Iio]; omega

lemma Ici_eq_Ioi_union (i : ℤ) : Set.Ici i = Set.Ioi i ∪ {i} := by
  ext j; simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]; omega

lemma Iic_eq_Iio_union (i : ℤ) : Set.Iic i = Set.Iio i ∪ {i} := by
  ext j; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]; omega

lemma compl_Ioo (i k : ℤ) : (Set.Ioo i k)ᶜ = Set.Iic i ∪ Set.Ici k := by
  ext j; simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_union, Set.mem_Iic, Set.mem_Ici]; omega

/-- The disjoint and non-adjacent unions of Georgii's step 1) in the proof of (10.9):
`V ∩ (W ∪ ∂W) = ∅`. -/
lemma boundarySet_union_of_disjoint (h : Disjoint V (W ∪ boundarySet W)) :
    boundarySet (V ∪ W) = boundarySet V ∪ boundarySet W := by
  have hd : ∀ i ∈ V, i ∉ W ∧ i ∉ boundarySet W := fun i hi ↦
    ⟨fun h' ↦ Set.disjoint_left.1 h hi (Or.inl h'), fun h' ↦ Set.disjoint_left.1 h hi (Or.inr h')⟩
  ext j
  simp only [mem_boundarySet, Set.mem_union, not_or]
  constructor
  · rintro ⟨⟨hjV, hjW⟩, h⟩
    rcases h with (h | h) | (h | h)
    · exact Or.inl ⟨hjV, Or.inl h⟩
    · exact Or.inr ⟨hjW, Or.inl h⟩
    · exact Or.inl ⟨hjV, Or.inr h⟩
    · exact Or.inr ⟨hjW, Or.inr h⟩
  · rintro (⟨hjV, h⟩ | ⟨hjW, h⟩)
    · refine ⟨⟨hjV, fun hjW ↦ ?_⟩, ?_⟩
      · rcases h with h | h
        · exact (hd _ h).2 ⟨(hd _ h).1, Or.inr (by rwa [show j + 1 - 1 = j by omega])⟩
        · exact (hd _ h).2 ⟨(hd _ h).1, Or.inl (by rwa [show j - 1 + 1 = j by omega])⟩
      · rcases h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
    · refine ⟨⟨fun hjV ↦ (hd _ hjV).2 ⟨hjW, h⟩, hjW⟩, ?_⟩
      rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

lemma subset_compl_of_disjoint_union (h : Disjoint V (W ∪ boundarySet W)) : W ⊆ Vᶜ :=
  fun _ hi hiV ↦ Set.disjoint_left.1 h hiV (Or.inl hi)

lemma boundarySet_subset_compl_of_disjoint_union (h : Disjoint V (W ∪ boundarySet W)) :
    boundarySet W ⊆ Vᶜ :=
  fun _ hi hiV ↦ Set.disjoint_left.1 h hiV (Or.inr hi)

lemma boundarySet_subset_compl_of_disjoint_union' (h : Disjoint V (W ∪ boundarySet W)) :
    boundarySet V ⊆ Wᶜ := by
  intro i hi hiW
  rcases hi.2 with h' | h'
  · exact Set.disjoint_left.1 h h' (Or.inr ⟨fun h'' ↦ Set.disjoint_left.1 h h' (Or.inl h''),
      Or.inr (by rwa [show i + 1 - 1 = i by omega])⟩)
  · exact Set.disjoint_left.1 h h' (Or.inr ⟨fun h'' ↦ Set.disjoint_left.1 h h' (Or.inl h''),
      Or.inl (by rwa [show i - 1 + 1 = i by omega])⟩)

/-! ### Cylinder σ-algebras on `ℤ` -/

/-! ### The Markov property (10.10) at a set of sites -/

/-- Georgii (10.10) at the set `V ⊆ ℤ`: `μ(A | 𝓕_{ℤ ∖ V}) = μ(A | 𝓕_{∂V})` `μ`-a.s. for every
`A ∈ 𝓕_V`. The *local* Markov property is this for finite `V`, the *global* one for all `V`. -/
def IsMarkovOn (μ : Measure (ℤ → E)) (V : Set ℤ) : Prop :=
  ∀ A, MeasurableSet[cylinderEvents V] A →
    μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents Vᶜ]
      =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V)]

/-- Georgii (10.6), the two-sided Markov property: `μ` is a *Markov field* if
`μ(A | 𝓕_{ℤ ∖ ]i,k[}) = μ(A | 𝓕_{{i,k}})` `μ`-a.s. for all `i + 1 < k` and `A ∈ 𝓕_{]i,k[}`. -/
def IsMarkovField (μ : Measure (ℤ → E)) : Prop :=
  ∀ i k : ℤ, i + 1 < k → ∀ A, MeasurableSet[cylinderEvents (Set.Ioo i k)] A →
    μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Ioo i k)ᶜ]
      =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents {i, k}]

/-- Georgii (10.7), the left-sided Markov property:
`μ(A | 𝓕_{]-∞,i]}) = μ(A | 𝓕_{{i}})` `μ`-a.s. for all `i` and `A ∈ 𝓕_{[i,∞[}`. -/
def IsLeftMarkov (μ : Measure (ℤ → E)) : Prop :=
  ∀ i : ℤ, ∀ A, MeasurableSet[cylinderEvents (Set.Ici i)] A →
    μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Iic i)]
      =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents {i}]

/-- Georgii (10.8), the right-sided Markov property:
`μ(A | 𝓕_{[i,∞[}) = μ(A | 𝓕_{{i}})` `μ`-a.s. for all `i` and `A ∈ 𝓕_{]-∞,i]}`. -/
def IsRightMarkov (μ : Measure (ℤ → E)) : Prop :=
  ∀ i : ℤ, ∀ A, MeasurableSet[cylinderEvents (Set.Iic i)] A →
    μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Ici i)]
      =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents {i}]

/-- Georgii's *one-sided Markov property*: (10.7) and (10.8) together. -/
def IsOneSidedMarkov (μ : Measure (ℤ → E)) : Prop := IsLeftMarkov μ ∧ IsRightMarkov μ

/-- The local Markov property of Georgii (8.24)/(10.10): (10.10) for every finite `V ⊆ ℤ`. -/
def IsLocalMarkov (μ : Measure (ℤ → E)) : Prop := ∀ V : Finset ℤ, IsMarkovOn μ (V : Set ℤ)

/-- The global Markov property of Georgii (8.24)/(10.9)(2): (10.10) for every `V ⊆ ℤ`. -/
def IsGlobalMarkov (μ : Measure (ℤ → E)) : Prop := ∀ V : Set ℤ, IsMarkovOn μ V

lemma IsGlobalMarkov.isLocalMarkov (h : IsGlobalMarkov μ) : IsLocalMarkov μ := fun V ↦ h V

section MarkovOn

variable [IsFiniteMeasure μ]

lemma cylinderEvents_boundarySet_le (V : Set ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (boundarySet V) ≤ cylinderEvents Vᶜ :=
  cylinderEvents_mono (boundarySet_subset_compl V)

/-- The functional form of (10.10): for `A ∈ 𝓕_V` and `f` bounded `𝓕_{ℤ∖V}`-measurable,
`∫ f 1_A dμ = ∫ f μ(A | 𝓕_{∂V}) dμ`. -/
lemma IsMarkovOn.integral_mul_indicator_eq (h : IsMarkovOn μ V)
    (hA : MeasurableSet[cylinderEvents V] A) {f : (ℤ → E) → ℝ}
    (hf : StronglyMeasurable[cylinderEvents Vᶜ] f) (hfc : ∀ᵐ x ∂μ, ‖f x‖ ≤ 1) :
    ∫ x, f x * A.indicator 1 x ∂μ
      = ∫ x, f x * (μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V)]) x ∂μ :=
  integral_mul_indicator_eq_of_condExp_ae_eq cylinderEvents_le_pi (cylinderEvents_le_pi _ hA)
    (h A hA) hf hfc

/-- (10.10) at `V` in the form `∫_A μ(D | 𝓕_{∂V}) = μ(A ∩ D)` for `A ∈ 𝓕_V`, `D ∈ 𝓕_{ℤ∖V}`. -/
lemma isMarkovOn_iff_forall_setIntegral :
    IsMarkovOn μ V ↔ ∀ A, MeasurableSet[cylinderEvents V] A →
      ∀ D, MeasurableSet[cylinderEvents Vᶜ] D →
        ∫ x in A, (μ[D.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V)]) x ∂μ
          = μ.real (A ∩ D) :=
  forall₂_congr fun _ hA ↦ condExp_indicator_ae_eq_iff_forall_setIntegral'
    (cylinderEvents_boundarySet_le V) cylinderEvents_le_pi (cylinderEvents_le_pi _ hA)

/-- If (10.10) holds at `V` and `V ⊆ V'`, `∂V ⊆ ∂V'`, then for `A ∈ 𝓕_V` also
`μ(A | 𝓕_{ℤ∖V'}) = μ(A | 𝓕_{∂V'})`: both sides equal `μ(A | 𝓕_{∂V})` by the tower property. -/
lemma IsMarkovOn.condExp_ae_eq_of_subset (h : IsMarkovOn μ V) {V' : Set ℤ}
    (hV' : V ⊆ V') (hbd : boundarySet V ⊆ boundarySet V')
    (hA : MeasurableSet[cylinderEvents V] A) :
    μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents V'ᶜ]
      =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V')] := by
  have hcc : V'ᶜ ⊆ Vᶜ := Set.compl_subset_compl.2 hV'
  have h1 := condExp_indicator_ae_eq_of_le (m₁ := cylinderEvents V'ᶜ)
    (cylinderEvents_mono (hbd.trans (boundarySet_subset_compl V')))
    (cylinderEvents_mono hcc) cylinderEvents_le_pi (h A hA)
  have h2 := condExp_indicator_ae_eq_of_le (m₁ := cylinderEvents (boundarySet V'))
    (cylinderEvents_mono hbd)
    (cylinderEvents_mono ((boundarySet_subset_compl V').trans hcc)) cylinderEvents_le_pi (h A hA)
  exact h1.trans h2.symm

omit [IsFiniteMeasure μ] in
lemma isMarkovOn_univ : IsMarkovOn μ (Set.univ : Set ℤ) := by
  intro A _
  simp only [Set.compl_univ, boundarySet_univ]
  exact ae_eq_refl _

lemma isMarkovOn_empty : IsMarkovOn μ (∅ : Set ℤ) := by
  intro A hA
  rw [cylinderEvents_empty, MeasurableSpace.measurableSet_bot_iff] at hA
  simp only [Set.compl_empty, boundarySet_empty, cylinderEvents_empty]
  rcases hA with rfl | rfl
  · simp
  · rw [Set.indicator_univ, show (1 : (ℤ → E) → ℝ) = fun _ ↦ 1 from rfl,
      condExp_const (μ := μ) cylinderEvents_le_pi, condExp_const (μ := μ) bot_le]

/-- **Georgii (10.9), step 1).** If (10.10) holds for `V` and `W` and `V ∩ (W ∪ ∂W) = ∅`, then
it holds for `V ∪ W`. -/
theorem IsMarkovOn.union (hV : IsMarkovOn μ V) (hW : IsMarkovOn μ W)
    (hVW : Disjoint V (W ∪ boundarySet W)) : IsMarkovOn μ (V ∪ W) := by
  have hWV : W ⊆ Vᶜ := subset_compl_of_disjoint_union hVW
  have hbdWV : boundarySet W ⊆ Vᶜ := boundarySet_subset_compl_of_disjoint_union hVW
  have hbdVW : boundarySet V ⊆ Wᶜ := boundarySet_subset_compl_of_disjoint_union' hVW
  have hVW' : V ⊆ Wᶜ := fun i hi hiW ↦ Set.disjoint_left.1 hVW hi (Or.inl hiW)
  have hbd := boundarySet_union_of_disjoint hVW
  have hcV : (V ∪ W)ᶜ ⊆ Vᶜ := Set.compl_subset_compl.2 Set.subset_union_left
  have hcW : (V ∪ W)ᶜ ⊆ Wᶜ := Set.compl_subset_compl.2 Set.subset_union_right
  have hbdV : boundarySet V ⊆ boundarySet (V ∪ W) := hbd ▸ Set.subset_union_left
  have hbdW : boundarySet W ⊆ boundarySet (V ∪ W) := hbd ▸ Set.subset_union_right
  rw [isMarkovOn_iff_forall_setIntegral]
  intro A hA D hD
  have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
  rw [inter_comm, ← setIntegral_indicator_one' hD' A]
  rw [cylinderEvents_union] at hA
  refine setIntegral_eq_of_generateFrom (sup_le cylinderEvents_le_pi cylinderEvents_le_pi)
    (isPiSystem_interSets _ _) (sup_eq_generateFrom_interSets _ _) integrable_condExp
    (integrable_indicator_one hD') ?_
    (integral_condExp (μ := μ) cylinderEvents_le_pi) A hA
  rintro _ ⟨B, C, hB, hC, rfl⟩
  have hB' : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hC' : MeasurableSet C := cylinderEvents_le_pi _ hC
  set gB := μ[B.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V)] with hgB
  set gC := μ[C.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet W)] with hgC
  set gD := μ[D.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet (V ∪ W))] with hgD
  have hgB_sm : StronglyMeasurable[cylinderEvents (boundarySet V)] gB := stronglyMeasurable_condExp
  have hgC_sm : StronglyMeasurable[cylinderEvents (boundarySet W)] gC := stronglyMeasurable_condExp
  have hgD_sm : StronglyMeasurable[cylinderEvents (boundarySet (V ∪ W))] gD :=
    stronglyMeasurable_condExp
  have hgB_le : ∀ᵐ x ∂μ, ‖gB x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ B
  have hgC_le : ∀ᵐ x ∂μ, ‖gC x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ C
  have hgD_le : ∀ᵐ x ∂μ, ‖gD x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ D
  -- forward: `μ(B ∩ C ∩ D) = ∫ gB gC gD`
  have s1 := hV.integral_mul_indicator_eq hB (f := fun x ↦ C.indicator 1 x * D.indicator 1 x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hWV _ hC)).mul
      (stronglyMeasurable_indicator_one (cylinderEvents_mono hcV _ hD)))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le C) (ae_norm_indicator_one_le D))
  have s2 := hW.integral_mul_indicator_eq hC (f := fun x ↦ D.indicator 1 x * gB x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hcW _ hD)).mul
      (hgB_sm.mono (cylinderEvents_mono hbdVW)))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le D) hgB_le)
  have s3 := integral_mul_indicator_eq_integral_mul_condExp (μ := μ)
    (m := cylinderEvents (boundarySet (V ∪ W))) cylinderEvents_le_pi hD' (f := fun x ↦ gB x * gC x)
    ((hgB_sm.mono (cylinderEvents_mono hbdV)).mul (hgC_sm.mono (cylinderEvents_mono hbdW)))
    (ae_norm_mul_le_one hgB_le hgC_le)
  -- backward: `∫ gB gC gD = ∫ 1_B 1_C gD`
  have s4 := hV.integral_mul_indicator_eq hB (f := fun x ↦ gC x * gD x)
    ((hgC_sm.mono (cylinderEvents_mono hbdWV)).mul
      (hgD_sm.mono (cylinderEvents_mono ((boundarySet_subset_compl _).trans hcV))))
    (ae_norm_mul_le_one hgC_le hgD_le)
  have s5 := hW.integral_mul_indicator_eq hC (f := fun x ↦ B.indicator 1 x * gD x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hVW' _ hB)).mul
      (hgD_sm.mono (cylinderEvents_mono ((boundarySet_subset_compl _).trans hcW))))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le B) hgD_le)
  rw [setIntegral_inter_eq_integral_mul hB' hC', setIntegral_inter_eq_integral_mul hB' hC']
  calc ∫ x, B.indicator (1 : (ℤ → E) → ℝ) x * (C.indicator 1 x * gD x) ∂μ
      = ∫ x, (B.indicator 1 x * gD x) * C.indicator 1 x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (B.indicator 1 x * gD x) * gC x ∂μ := s5
    _ = ∫ x, (gC x * gD x) * B.indicator 1 x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (gC x * gD x) * gB x ∂μ := s4
    _ = ∫ x, (gB x * gC x) * gD x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (gB x * gC x) * D.indicator 1 x ∂μ := s3.symm
    _ = ∫ x, (D.indicator 1 x * gB x) * gC x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (D.indicator 1 x * gB x) * C.indicator 1 x ∂μ := s2.symm
    _ = ∫ x, (C.indicator 1 x * D.indicator 1 x) * gB x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (C.indicator 1 x * D.indicator 1 x) * B.indicator 1 x ∂μ := s1.symm
    _ = ∫ x, B.indicator 1 x * (C.indicator 1 x * D.indicator 1 x) ∂μ := by
        congr 1; funext x; ring

end MarkovOn

/-! ### Extension from finitely many sites -/

/-- The π-system of events depending on finitely many sites of `V`. -/
def finiteCylinderEvents (E : Type*) [MeasurableSpace E] (V : Set ℤ) : Set (Set (ℤ → E)) :=
  {A | ∃ W : Finset ℤ, (W : Set ℤ) ⊆ V ∧ MeasurableSet[cylinderEvents (W : Set ℤ)] A}

lemma isPiSystem_finiteCylinderEvents (V : Set ℤ) :
    IsPiSystem (finiteCylinderEvents E V) := by
  rintro _ ⟨W₁, hW₁, hA₁⟩ _ ⟨W₂, hW₂, hA₂⟩ -
  refine ⟨W₁ ∪ W₂, by push_cast; exact Set.union_subset hW₁ hW₂, ?_⟩
  rw [Finset.coe_union]
  exact (cylinderEvents_mono Set.subset_union_left _ hA₁).inter
    (cylinderEvents_mono Set.subset_union_right _ hA₂)

lemma cylinderEvents_eq_generateFrom_finiteCylinderEvents (V : Set ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) V
      = MeasurableSpace.generateFrom (finiteCylinderEvents E V) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup₂_le fun i hi s hs ↦ ?_
    obtain ⟨t, ht, rfl⟩ := hs
    exact MeasurableSpace.measurableSet_generateFrom ⟨{i}, by simpa using hi,
      measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
        (Finset.mem_coe.2 (Finset.mem_singleton_self i)) ht⟩
  · rintro A ⟨W, hW, hA⟩
    exact cylinderEvents_mono hW _ hA

section MarkovOn

variable [IsFiniteMeasure μ]

/-- Georgii's "standard extension argument": (10.10) at `V` follows from the equality
`μ(A | 𝓕_{ℤ∖V}) = μ(A | 𝓕_{∂V})` for the events `A` depending on finitely many sites of `V`. -/
lemma IsMarkovOn.of_forall_finset
    (h : ∀ W : Finset ℤ, (W : Set ℤ) ⊆ V → ∀ A, MeasurableSet[cylinderEvents (W : Set ℤ)] A →
      μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents Vᶜ]
        =ᵐ[μ] μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (boundarySet V)]) :
    IsMarkovOn μ V := by
  rw [isMarkovOn_iff_forall_setIntegral]
  intro A hA D hD
  have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
  rw [inter_comm, ← setIntegral_indicator_one' hD' A]
  refine setIntegral_eq_of_generateFrom cylinderEvents_le_pi (isPiSystem_finiteCylinderEvents V)
    (cylinderEvents_eq_generateFrom_finiteCylinderEvents V) integrable_condExp
    (integrable_indicator_one hD') ?_ (integral_condExp (μ := μ) cylinderEvents_le_pi) A hA
  rintro B ⟨W, hW, hB⟩
  have := (condExp_indicator_ae_eq_iff_forall_setIntegral' (cylinderEvents_boundarySet_le V)
    cylinderEvents_le_pi (cylinderEvents_le_pi _ (cylinderEvents_mono hW _ hB))).1
    (h W hW B hB) D hD
  rw [this, setIntegral_indicator_one' hD' B, inter_comm]

end MarkovOn

/-! ### Maximal intervals -/

/-- The maximal interval of `V ⊆ ℤ` containing `w`: `{i | [min i w, max i w] ⊆ V}` (empty when
`w ∉ V`). -/
def component (V : Set ℤ) (w : ℤ) : Set ℤ := {i | Set.Icc (min i w) (max i w) ⊆ V}

variable {w w' i : ℤ}

lemma mem_component : i ∈ component V w ↔ Set.Icc (min i w) (max i w) ⊆ V := Iff.rfl

lemma component_subset (V : Set ℤ) (w : ℤ) : component V w ⊆ V := fun _ hi ↦
  hi ⟨min_le_left _ _, le_max_left _ _⟩

lemma mem_component_self (hw : w ∈ V) : w ∈ component V w := by
  intro j hj
  simp only [min_self, max_self, Set.mem_Icc] at hj
  rwa [show j = w by omega]

lemma succ_mem_component (hi : i ∈ component V w) (h : i + 1 ∈ V) : i + 1 ∈ component V w := by
  intro j hj
  simp only [Set.mem_Icc] at hj
  by_cases hji : j = i + 1
  · exact hji ▸ h
  · exact hi (by simp only [Set.mem_Icc]; omega)

lemma pred_mem_component (hi : i ∈ component V w) (h : i - 1 ∈ V) : i - 1 ∈ component V w := by
  intro j hj
  simp only [Set.mem_Icc] at hj
  by_cases hji : j = i - 1
  · exact hji ▸ h
  · exact hi (by simp only [Set.mem_Icc]; omega)

lemma mem_component_of_mem_of_mem (hi : i ∈ component V w) (hi' : i ∈ component V w') :
    w ∈ component V w' := by
  intro j hj
  simp only [Set.mem_Icc] at hj
  by_cases hj1 : min i w ≤ j ∧ j ≤ max i w
  · exact hi (Set.mem_Icc.2 hj1)
  · exact hi' (by simp only [Set.mem_Icc]; omega)

lemma component_subset_component (h : w' ∈ component V w) :
    component V w' ⊆ component V w := by
  intro i hi j hj
  simp only [Set.mem_Icc] at hj
  by_cases hj1 : min i w' ≤ j ∧ j ≤ max i w'
  · exact hi (Set.mem_Icc.2 hj1)
  · exact h (by simp only [Set.mem_Icc]; omega)

lemma ordConnected_component (V : Set ℤ) (w : ℤ) : (component V w).OrdConnected := by
  refine Set.ordConnected_def.2 fun i hi i' hi' j hj k hk ↦ ?_
  simp only [Set.mem_Icc] at hj hk
  by_cases hk1 : min i w ≤ k ∧ k ≤ max i w
  · exact hi (Set.mem_Icc.2 hk1)
  · exact hi' (by simp only [Set.mem_Icc]; omega)

/-- The union of the maximal intervals of `V` through the sites of the finite set `W`. -/
def hull (V : Set ℤ) (W : Finset ℤ) : Set ℤ := ⋃ w ∈ W, component V w

variable {W : Finset ℤ}

lemma hull_subset : hull V W ⊆ V := Set.iUnion₂_subset fun w _ ↦ component_subset V w

lemma subset_hull (hW : (W : Set ℤ) ⊆ V) : (W : Set ℤ) ⊆ hull V W := fun w hw ↦
  Set.mem_iUnion₂.2 ⟨w, hw, mem_component_self (hW hw)⟩

lemma boundarySet_hull_subset : boundarySet (hull V W) ⊆ boundarySet V := by
  rintro i ⟨hi, h⟩
  refine ⟨fun hiV ↦ hi ?_, ?_⟩
  · rcases h with h | h
    · obtain ⟨w, hw, hc⟩ := Set.mem_iUnion₂.1 h
      refine Set.mem_iUnion₂.2 ⟨w, hw, ?_⟩
      have := pred_mem_component hc (by rwa [show i + 1 - 1 = i by omega])
      rwa [show i + 1 - 1 = i by omega] at this
    · obtain ⟨w, hw, hc⟩ := Set.mem_iUnion₂.1 h
      refine Set.mem_iUnion₂.2 ⟨w, hw, ?_⟩
      have := succ_mem_component hc (by rwa [show i - 1 + 1 = i by omega])
      rwa [show i - 1 + 1 = i by omega] at this
  · rcases h with h | h
    · exact Or.inl (hull_subset h)
    · exact Or.inr (hull_subset h)

@[simp] lemma hull_empty : hull V ∅ = ∅ := by simp [hull]

lemma hull_insert [DecidableEq ℤ] (w : ℤ) (W : Finset ℤ) :
    hull V (insert w W) = component V w ∪ hull V W := by
  simp [hull]

lemma component_subset_hull (hw : w ∈ hull V W) : component V w ⊆ hull V W := by
  obtain ⟨w', hw', hc⟩ := Set.mem_iUnion₂.1 hw
  exact (component_subset_component hc).trans
    (Set.subset_iUnion₂ (s := fun w _ ↦ component V w) w' hw')

lemma disjoint_component_hull (hw : w ∉ hull V W) :
    Disjoint (component V w) (hull V W ∪ boundarySet (hull V W)) := by
  rw [Set.disjoint_left]
  intro i hi hi'
  have key : ∀ j, j ∈ component V w → j ∈ hull V W → False := fun j hj hj' ↦ by
    obtain ⟨w', hw', hc⟩ := Set.mem_iUnion₂.1 hj'
    exact hw (Set.mem_iUnion₂.2 ⟨w', hw', mem_component_of_mem_of_mem hj hc⟩)
  rcases hi' with hi' | ⟨_, h | h⟩
  · exact key i hi hi'
  · exact key (i + 1) (succ_mem_component hi (hull_subset h)) h
  · exact key (i - 1) (pred_mem_component hi (hull_subset h)) h

section MarkovOn

variable [IsFiniteMeasure μ]

lemma isMarkovOn_hull (h : ∀ w ∈ V, IsMarkovOn μ (component V w)) (W : Finset ℤ)
    (hW : (W : Set ℤ) ⊆ V) : IsMarkovOn μ (hull V W) := by
  classical
  induction W using Finset.induction_on with
  | empty => rw [hull_empty]; exact isMarkovOn_empty
  | insert w W hwW ih =>
    have hw : w ∈ V := hW (by simp)
    have hW' : (W : Set ℤ) ⊆ V := fun x hx ↦ hW (by simp [hx])
    rw [hull_insert]
    by_cases hwh : w ∈ hull V W
    · rw [Set.union_eq_right.2 (component_subset_hull hwh)]
      exact ih hW'
    · exact (h w hw).union (ih hW') (disjoint_component_hull hwh)

/-- **Georgii (10.9), steps 1) and 4).** (10.10) at `V` follows from (10.10) at each maximal
interval of `V`. -/
theorem IsMarkovOn.of_forall_component (h : ∀ w ∈ V, IsMarkovOn μ (component V w)) :
    IsMarkovOn μ V :=
  IsMarkovOn.of_forall_finset fun W hW _ hA ↦
    (isMarkovOn_hull h W hW).condExp_ae_eq_of_subset hull_subset boundarySet_hull_subset
      (cylinderEvents_mono (subset_hull hW) _ hA)

end MarkovOn

/-! ### Intervals of `ℤ` -/

lemma _root_.Set.OrdConnected.exists_eq_Icc_int {s : Set ℤ} (hs : s.OrdConnected) (hne : s.Nonempty)
    (hb : BddBelow s) (hb' : BddAbove s) : ∃ a b, a ≤ b ∧ s = Set.Icc a b := by
  obtain ⟨a, ha, hamin⟩ := Int.exists_least_of_bdd (P := (· ∈ s))
    (by obtain ⟨b, hb⟩ := hb; exact ⟨b, fun z hz ↦ hb hz⟩) hne
  obtain ⟨b, hb, hbmax⟩ := Int.exists_greatest_of_bdd (P := (· ∈ s))
    (by obtain ⟨c, hc⟩ := hb'; exact ⟨c, fun z hz ↦ hc hz⟩) hne
  exact ⟨a, b, hamin b hb, Set.Subset.antisymm (fun z hz ↦ ⟨hamin z hz, hbmax z hz⟩) (hs.out ha hb)⟩

/-- A nonempty order-connected subset of `ℤ` is `ℤ`, a half-line, or a closed interval. -/
lemma _root_.Set.OrdConnected.eq_univ_or_Ici_or_Iic_or_Icc_int {s : Set ℤ} (hs : s.OrdConnected)
    (hne : s.Nonempty) :
    s = Set.univ ∨ (∃ a, s = Set.Ici a) ∨ (∃ b, s = Set.Iic b) ∨ ∃ a b, a ≤ b ∧ s = Set.Icc a b
        := by
  by_cases hb : BddBelow s <;> by_cases hb' : BddAbove s
  · exact Or.inr (Or.inr (Or.inr (hs.exists_eq_Icc_int hne hb hb')))
  · obtain ⟨a, ha, hamin⟩ := Int.exists_least_of_bdd (P := (· ∈ s))
      (by obtain ⟨b, hb⟩ := hb; exact ⟨b, fun z hz ↦ hb hz⟩) hne
    refine Or.inr (Or.inl ⟨a, Set.Subset.antisymm (fun z hz ↦ hamin z hz) fun z hz ↦ ?_⟩)
    obtain ⟨y, hy, hzy⟩ := not_bddAbove_iff.1 hb' z
    exact hs.out ha hy ⟨hz, hzy.le⟩
  · obtain ⟨b, hbs, hbmax⟩ := Int.exists_greatest_of_bdd (P := (· ∈ s))
      (by obtain ⟨c, hc⟩ := hb'; exact ⟨c, fun z hz ↦ hc hz⟩) hne
    refine Or.inr (Or.inr (Or.inl ⟨b, Set.Subset.antisymm (fun z hz ↦ hbmax z hz) fun z hz ↦ ?_⟩))
    obtain ⟨y, hy, hzy⟩ := not_bddBelow_iff.1 hb z
    exact hs.out hy hbs ⟨hzy.le, hz⟩
  · refine Or.inl (Set.eq_univ_of_forall fun z ↦ ?_)
    obtain ⟨y, hy, hzy⟩ := not_bddAbove_iff.1 hb' z
    obtain ⟨x, hx, hxz⟩ := not_bddBelow_iff.1 hb z
    exact hs.out hx hy ⟨hxz.le, hzy.le⟩

/-! ### Georgii, Remark (10.9) -/

section Remarks

variable [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- The two-sided Markov property (10.6) is (10.10) at the open intervals `]i,k[`. -/
lemma isMarkovField_iff : IsMarkovField μ ↔ ∀ i k : ℤ, i + 1 < k → IsMarkovOn μ (Set.Ioo i k) := by
  refine forall₃_congr fun i k hik ↦ ?_
  rw [IsMarkovOn, boundarySet_Ioo hik]

lemma IsMarkovField.isMarkovOn_Ioo (h : IsMarkovField μ) (i k : ℤ) : IsMarkovOn μ (Set.Ioo i k)
    := by
  by_cases hik : i + 1 < k
  · exact isMarkovField_iff.1 h i k hik
  · rw [Ioo_eq_empty_of_le (by omega)]
    exact isMarkovOn_empty

lemma IsMarkovField.isMarkovOn_Icc (h : IsMarkovField μ) (a b : ℤ) : IsMarkovOn μ (Set.Icc a b)
    := by
  rw [Icc_eq_Ioo]
  exact h.isMarkovOn_Ioo _ _

/-- The left-sided Markov property (10.7) is (10.10) at the half-lines `]i,∞[`. -/
lemma isLeftMarkov_iff : IsLeftMarkov μ ↔ ∀ i, IsMarkovOn μ (Set.Ioi i) := by
  constructor
  · intro h i A hA
    rw [Set.compl_Ioi, boundarySet_Ioi]
    exact h i A (cylinderEvents_mono Set.Ioi_subset_Ici_self _ hA)
  · intro h i A hA
    have h' := h i
    simp only [IsMarkovOn, Set.compl_Ioi, boundarySet_Ioi] at h'
    rw [Ici_eq_Ioi_union, cylinderEvents_union] at hA
    exact condExp_indicator_ae_eq_sup (cylinderEvents_mono (by simp)) cylinderEvents_le_pi
      cylinderEvents_le_pi h' A hA

/-- The right-sided Markov property (10.8) is (10.10) at the half-lines `]-∞,i[`. -/
lemma isRightMarkov_iff : IsRightMarkov μ ↔ ∀ i, IsMarkovOn μ (Set.Iio i) := by
  constructor
  · intro h i A hA
    rw [Set.compl_Iio, boundarySet_Iio]
    exact h i A (cylinderEvents_mono Set.Iio_subset_Iic_self _ hA)
  · intro h i A hA
    have h' := h i
    simp only [IsMarkovOn, Set.compl_Iio, boundarySet_Iio] at h'
    rw [Iic_eq_Iio_union, cylinderEvents_union] at hA
    exact condExp_indicator_ae_eq_sup (cylinderEvents_mono (by simp)) cylinderEvents_le_pi
      cylinderEvents_le_pi h' A hA

/-- **Georgii, after (10.8).** The left-sided and the right-sided Markov properties are
equivalent. -/
theorem isLeftMarkov_iff_isRightMarkov : IsLeftMarkov μ ↔ IsRightMarkov μ := by
  constructor
  · intro h i
    exact condExp_indicator_ae_eq_symm (m₂ := cylinderEvents (Set.Ici i))
      (cylinderEvents_mono (by simp)) (cylinderEvents_mono (by simp)) cylinderEvents_le_pi
      cylinderEvents_le_pi (h i)
  · intro h i
    exact condExp_indicator_ae_eq_symm (m₂ := cylinderEvents (Set.Iic i))
      (cylinderEvents_mono (by simp)) (cylinderEvents_mono (by simp)) cylinderEvents_le_pi
      cylinderEvents_le_pi (h i)

lemma IsLeftMarkov.isOneSidedMarkov (h : IsLeftMarkov μ) : IsOneSidedMarkov μ :=
  ⟨h, isLeftMarkov_iff_isRightMarkov.1 h⟩

lemma IsRightMarkov.isOneSidedMarkov (h : IsRightMarkov μ) : IsOneSidedMarkov μ :=
  ⟨isLeftMarkov_iff_isRightMarkov.2 h, h⟩

/-- **Georgii, Remark (10.9)(3).** The one-sided Markov property implies the two-sided one:
every Markov chain is a Markov field. -/
theorem IsOneSidedMarkov.isMarkovField (h : IsOneSidedMarkov μ) : IsMarkovField μ := by
  obtain ⟨hL, hR⟩ := h
  intro i k hik A hA
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hik' : ({i, k} : Set ℤ) ⊆ (Set.Ioo i k)ᶜ := by
    intro j hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    simp only [Set.mem_compl_iff, Set.mem_Ioo]
    omega
  rw [condExp_indicator_ae_eq_iff_forall_setIntegral (cylinderEvents_mono hik')
    cylinderEvents_le_pi hA']
  intro D hD
  rw [← setIntegral_indicator_one' hA' D, compl_Ioo, cylinderEvents_union] at *
  refine setIntegral_eq_of_generateFrom (sup_le cylinderEvents_le_pi cylinderEvents_le_pi)
    (isPiSystem_interSets _ _) (sup_eq_generateFrom_interSets _ _) integrable_condExp
    (integrable_indicator_one hA') ?_ (integral_condExp (μ := μ) cylinderEvents_le_pi) D hD
  rintro _ ⟨D₁, D₂, hD₁, hD₂, rfl⟩
  have hD₁' : MeasurableSet D₁ := cylinderEvents_le_pi _ hD₁
  have hD₂' : MeasurableSet D₂ := cylinderEvents_le_pi _ hD₂
  set gA := μ[A.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents ({i, k} : Set ℤ)] with hgA
  set g₁ := μ[D₁.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents ({i} : Set ℤ)] with hg₁
  set g₂ := μ[D₂.indicator (1 : (ℤ → E) → ℝ) | cylinderEvents ({k} : Set ℤ)] with hg₂
  have hgA_sm : StronglyMeasurable[cylinderEvents ({i, k} : Set ℤ)] gA := stronglyMeasurable_condExp
  have hg₁_sm : StronglyMeasurable[cylinderEvents ({i} : Set ℤ)] g₁ := stronglyMeasurable_condExp
  have hg₂_sm : StronglyMeasurable[cylinderEvents ({k} : Set ℤ)] g₂ := stronglyMeasurable_condExp
  have hgA_le : ∀ᵐ x ∂μ, ‖gA x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ A
  have hg₁_le : ∀ᵐ x ∂μ, ‖g₁ x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ D₁
  have hg₂_le : ∀ᵐ x ∂μ, ‖g₂ x‖ ≤ 1 := ae_norm_condExp_indicator_one_le _ D₂
  have hIic : Set.Iic i ⊆ Set.Iic k := Set.Iic_subset_Iic.2 (by omega)
  have hIooK : Set.Ioo i k ⊆ Set.Iic k := fun j hj ↦ hj.2.le
  have hIooI : Set.Ioo i k ⊆ Set.Ici i := fun j hj ↦ hj.1.le
  have hkI : ({k} : Set ℤ) ⊆ Set.Ici i := Set.singleton_subset_iff.2 (by simp; omega)
  have hiK : ({i} : Set ℤ) ⊆ Set.Iic k := Set.singleton_subset_iff.2 (by simp; omega)
  have hikI : ({i, k} : Set ℤ) ⊆ Set.Ici i := by
    intro j hj; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj; simp; omega
  have hikK : ({i, k} : Set ℤ) ⊆ Set.Iic k := by
    intro j hj; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj; simp; omega
  have hi_ik : ({i} : Set ℤ) ⊆ {i, k} := Set.singleton_subset_iff.2 (by simp)
  have hk_ik : ({k} : Set ℤ) ⊆ {i, k} := Set.singleton_subset_iff.2 (by simp)
  -- the left-sided property at `k`, applied to `D₂ ∈ 𝓕_{[k,∞[}`
  have tL : ∀ f : (ℤ → E) → ℝ, StronglyMeasurable[cylinderEvents (Set.Iic k)] f →
      (∀ᵐ x ∂μ, ‖f x‖ ≤ 1) → ∫ x, f x * D₂.indicator 1 x ∂μ = ∫ x, f x * g₂ x ∂μ := fun f hf hfc ↦
    integral_mul_indicator_eq_of_condExp_ae_eq cylinderEvents_le_pi hD₂' (hL k D₂ hD₂) hf hfc
  -- the right-sided property at `i`, applied to `D₁ ∈ 𝓕_{]-∞,i]}`
  have tR : ∀ f : (ℤ → E) → ℝ, StronglyMeasurable[cylinderEvents (Set.Ici i)] f →
      (∀ᵐ x ∂μ, ‖f x‖ ≤ 1) → ∫ x, f x * D₁.indicator 1 x ∂μ = ∫ x, f x * g₁ x ∂μ := fun f hf hfc ↦
    integral_mul_indicator_eq_of_condExp_ae_eq cylinderEvents_le_pi hD₁' (hR i D₁ hD₁) hf hfc
  have t1 := tL (fun x ↦ D₁.indicator 1 x * A.indicator 1 x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hIic _ hD₁)).mul
      (stronglyMeasurable_indicator_one (cylinderEvents_mono hIooK _ hA)))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le D₁) (ae_norm_indicator_one_le A))
  have t2 := tR (fun x ↦ A.indicator 1 x * g₂ x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hIooI _ hA)).mul
      (hg₂_sm.mono (cylinderEvents_mono hkI)))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le A) hg₂_le)
  have t3 := integral_mul_indicator_eq_integral_mul_condExp (μ := μ)
    (m := cylinderEvents ({i, k} : Set ℤ)) cylinderEvents_le_pi hA' (f := fun x ↦ g₁ x * g₂ x)
    ((hg₁_sm.mono (cylinderEvents_mono hi_ik)).mul (hg₂_sm.mono (cylinderEvents_mono hk_ik)))
    (ae_norm_mul_le_one hg₁_le hg₂_le)
  have t4 := tR (fun x ↦ g₂ x * gA x)
    ((hg₂_sm.mono (cylinderEvents_mono hkI)).mul (hgA_sm.mono (cylinderEvents_mono hikI)))
    (ae_norm_mul_le_one hg₂_le hgA_le)
  have t5 := tL (fun x ↦ D₁.indicator 1 x * gA x)
    ((stronglyMeasurable_indicator_one (cylinderEvents_mono hIic _ hD₁)).mul
      (hgA_sm.mono (cylinderEvents_mono hikK)))
    (ae_norm_mul_le_one (ae_norm_indicator_one_le D₁) hgA_le)
  rw [setIntegral_inter_eq_integral_mul hD₁' hD₂', setIntegral_inter_eq_integral_mul hD₁' hD₂']
  calc ∫ x, D₁.indicator (1 : (ℤ → E) → ℝ) x * (D₂.indicator 1 x * gA x) ∂μ
      = ∫ x, (D₁.indicator 1 x * gA x) * D₂.indicator 1 x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (D₁.indicator 1 x * gA x) * g₂ x ∂μ := t5
    _ = ∫ x, (g₂ x * gA x) * D₁.indicator 1 x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (g₂ x * gA x) * g₁ x ∂μ := t4
    _ = ∫ x, (g₁ x * g₂ x) * gA x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (g₁ x * g₂ x) * A.indicator 1 x ∂μ := t3.symm
    _ = ∫ x, (A.indicator 1 x * g₂ x) * g₁ x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (A.indicator 1 x * g₂ x) * D₁.indicator 1 x ∂μ := t2.symm
    _ = ∫ x, (D₁.indicator 1 x * A.indicator 1 x) * g₂ x ∂μ := by congr 1; funext x; ring
    _ = ∫ x, (D₁.indicator 1 x * A.indicator 1 x) * D₂.indicator 1 x ∂μ := t1.symm
    _ = ∫ x, D₁.indicator (1 : (ℤ → E) → ℝ) x * (D₂.indicator 1 x * A.indicator 1 x) ∂μ := by
        congr 1; funext x; ring

/-- **Georgii, Remark (10.9)(1).** The two-sided Markov property is equivalent to the local
Markov property on `ℤ`. -/
theorem isMarkovField_iff_isLocalMarkov : IsMarkovField μ ↔ IsLocalMarkov μ := by
  constructor
  · intro h V
    refine IsMarkovOn.of_forall_component fun w hw ↦ ?_
    obtain ⟨a, b, -, hab⟩ := (ordConnected_component (V : Set ℤ) w).exists_eq_Icc_int
      ⟨w, mem_component_self hw⟩ ((Finset.bddBelow V).mono (component_subset _ _))
      ((Finset.bddAbove V).mono (component_subset _ _))
    rw [hab]
    exact h.isMarkovOn_Icc a b
  · intro h
    refine isMarkovField_iff.2 fun i k _ ↦ ?_
    simpa using h (Finset.Ioo i k)

/-- **Georgii, Remark (10.9)(2).** The one-sided Markov property is equivalent to the global
Markov property on `ℤ`. -/
theorem isOneSidedMarkov_iff_isGlobalMarkov : IsOneSidedMarkov μ ↔ IsGlobalMarkov μ := by
  constructor
  · intro h V
    refine IsMarkovOn.of_forall_component fun w hw ↦ ?_
    rcases (ordConnected_component V w).eq_univ_or_Ici_or_Iic_or_Icc_int
      ⟨w, mem_component_self hw⟩ with hc | ⟨a, hc⟩ | ⟨b, hc⟩ | ⟨a, b, -, hc⟩
    · rw [hc]; exact isMarkovOn_univ
    · rw [hc, Ici_eq_Ioi]; exact isLeftMarkov_iff.1 h.1 _
    · rw [hc, Iic_eq_Iio]; exact isRightMarkov_iff.1 h.2 _
    · rw [hc]; exact h.isMarkovField.isMarkovOn_Icc a b
  · intro h
    exact ⟨isLeftMarkov_iff.2 fun i ↦ h _, isRightMarkov_iff.2 fun i ↦ h _⟩

lemma IsGlobalMarkov.isMarkovField (h : IsGlobalMarkov μ) : IsMarkovField μ :=
  (isOneSidedMarkov_iff_isGlobalMarkov.2 h).isMarkovField

end Remarks

end MeasureTheory.GibbsMeasure.Markov

/-! ## Georgii (10.4): Markov chains with a general state space -/

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] {μ : Measure (ℤ → E)} {P : ℤ → Kernel E E}
  {B : ℤ → Set E} {i : ℤ} {n : ℕ}

/-! ### Rectangles -/

/-- The rectangle `{σ_j ∈ B_j for all j ∈ W}` over a finite set of sites. -/
def rect (W : Finset ℤ) (B : ℤ → Set E) : Set (ℤ → E) := {σ | ∀ j ∈ W, σ j ∈ B j}

omit [MeasurableSpace E] in
lemma mem_rect {W : Finset ℤ} {σ : ℤ → E} : σ ∈ rect W B ↔ ∀ j ∈ W, σ j ∈ B j := Iff.rfl

lemma measurableSet_cylinderEvents_rect {W : Finset ℤ} {V : Set ℤ} (hW : (W : Set ℤ) ⊆ V)
    (hB : ∀ k, MeasurableSet (B k)) : MeasurableSet[cylinderEvents V] (rect W B) := by
  have : rect W B = ⋂ j ∈ W, (fun σ : ℤ → E ↦ σ j) ⁻¹' B j := by ext; simp [rect]
  rw [this]
  exact Finset.measurableSet_biInter _ fun j hj ↦
    measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (hW hj) (hB j)

lemma measurableSet_rect {W : Finset ℤ} (hB : ∀ k, MeasurableSet (B k)) :
    MeasurableSet (rect W B) :=
  cylinderEvents_le_pi _ (measurableSet_cylinderEvents_rect (Set.subset_univ _) hB)

omit [MeasurableSpace E] in
/-- Splitting off one site of a rectangle. -/
lemma rect_eq_erase_inter {W : Finset ℤ} {j : ℤ} (hj : j ∈ W) :
    rect W B = rect (W.erase j) B ∩ (fun σ ↦ σ j) ⁻¹' B j := by
  ext σ
  simp only [mem_rect, Finset.mem_erase, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun k hk ↦ h k hk.2, h j hj⟩
  · rintro ⟨h₁, h₂⟩ k hk
    by_cases hkj : k = j
    · exact hkj ▸ h₂
    · exact h₁ k ⟨hkj, hk⟩

omit [MeasurableSpace E] in
/-- Replacing the set at one site of a rectangle. -/
lemma rect_update {W : Finset ℤ} {j : ℤ} (hj : j ∈ W) (S : Set E) :
    rect W (Function.update B j S) = (fun σ ↦ σ j) ⁻¹' S ∩ rect (W.erase j) B := by
  classical
  rw [rect_eq_erase_inter hj, Function.update_self, Set.inter_comm]
  congr 1
  ext σ
  simp only [mem_rect, Finset.mem_erase]
  exact ⟨fun h k hk ↦ by simpa [Function.update_of_ne hk.1] using h k hk,
    fun h k hk ↦ by simpa [Function.update_of_ne hk.1] using h k hk⟩

/-- The rectangles over an increasing family of finite volumes. -/
def rectangles (E : Type*) [MeasurableSpace E] (F : ℕ → Finset ℤ) : Set (Set (ℤ → E)) :=
  {t | ∃ (n : ℕ) (B : ℤ → Set E), (∀ k, MeasurableSet (B k)) ∧ t = rect (F n) B}

lemma isPiSystem_rectangles {F : ℕ → Finset ℤ} (hF : Monotone F) :
    IsPiSystem (rectangles E F) := by
  classical
  rintro _ ⟨n₁, B₁, hB₁, rfl⟩ _ ⟨n₂, B₂, hB₂, rfl⟩ -
  refine ⟨max n₁ n₂, fun k ↦ (if k ∈ F n₁ then B₁ k else Set.univ) ∩
    (if k ∈ F n₂ then B₂ k else Set.univ), fun k ↦ ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_ <;> split_ifs <;> simp [hB₁ k, hB₂ k]
  · ext σ
    simp only [Set.mem_inter_iff, mem_rect]
    constructor
    · rintro ⟨h₁, h₂⟩ j _
      refine ⟨?_, ?_⟩ <;> split_ifs with h
      · exact h₁ j h
      · trivial
      · exact h₂ j h
      · trivial
    · intro h
      refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
      · have := (h j (hF (le_max_left n₁ n₂) hj)).1
        simpa [hj] using this
      · have := (h j (hF (le_max_right n₁ n₂) hj)).2
        simpa [hj] using this

lemma cylinderEvents_eq_generateFrom_rectangles {F : ℕ → Finset ℤ} {V : Set ℤ}
    (hFV : ∀ n, (F n : Set ℤ) ⊆ V) (hV : ∀ k ∈ V, ∃ n, k ∈ F n) :
    cylinderEvents (X := fun _ : ℤ ↦ E) V = MeasurableSpace.generateFrom (rectangles E F) := by
  classical
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup₂_le fun k hk s hs ↦ ?_
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨n, hn⟩ := hV k hk
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨n, fun j ↦ if j = k then t else Set.univ,
        fun j ↦ by by_cases hjk : j = k <;> simp [hjk, ht], ?_⟩
    ext σ
    simp only [Set.mem_preimage, mem_rect]
    constructor
    · intro h j _
      split_ifs with hjk
      · exact hjk ▸ h
      · trivial
    · intro h
      simpa using h k hn
  · rintro _ ⟨n, B, hB, rfl⟩
    exact measurableSet_cylinderEvents_rect (hFV n) hB

omit [MeasurableSpace E] in
lemma monotone_Icc_left (i : ℤ) : Monotone fun n : ℕ ↦ Finset.Icc (i - n) i := fun _ _ h ↦
  Finset.Icc_subset_Icc (by omega) le_rfl

omit [MeasurableSpace E] in
lemma monotone_Icc_left' (i : ℤ) : Monotone fun n : ℕ ↦ Finset.Icc (i - n - 1) (i - 1) :=
  fun _ _ h ↦ Finset.Icc_subset_Icc (by omega) le_rfl

omit [MeasurableSpace E] in
lemma monotone_Icc_right (i : ℤ) : Monotone fun n : ℕ ↦ Finset.Icc i (i + n) := fun _ _ h ↦
  Finset.Icc_subset_Icc le_rfl (by omega)

lemma cylinderEvents_Iio_eq_generateFrom (i : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iio i)
      = MeasurableSpace.generateFrom (rectangles E fun n ↦ Finset.Icc (i - n - 1) (i - 1)) :=
  cylinderEvents_eq_generateFrom_rectangles (fun n j hj ↦ by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj; simp only [Set.mem_Iio]; omega)
    fun k hk ↦ ⟨(i - k - 1).toNat, by
      have := Int.toNat_of_nonneg (show 0 ≤ i - k - 1 by simp only [Set.mem_Iio] at hk; omega)
      simp only [Finset.mem_Icc]; omega⟩

lemma cylinderEvents_Iic_eq_generateFrom (i : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic i)
      = MeasurableSpace.generateFrom (rectangles E fun n ↦ Finset.Icc (i - n) i) :=
  cylinderEvents_eq_generateFrom_rectangles (fun n j hj ↦ by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj; exact hj.2)
    fun k hk ↦ ⟨(i - k).toNat, by
      have := Int.toNat_of_nonneg (show 0 ≤ i - k by simp only [Set.mem_Iic] at hk; omega)
      simp only [Finset.mem_Icc]; omega⟩

lemma cylinderEvents_Ici_eq_generateFrom (i : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici i)
      = MeasurableSpace.generateFrom (rectangles E fun n ↦ Finset.Icc i (i + n)) :=
  cylinderEvents_eq_generateFrom_rectangles (fun n j hj ↦ by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj; exact hj.1)
    fun k hk ↦ ⟨(k - i).toNat, by
      have := Int.toNat_of_nonneg (show 0 ≤ k - i by simp only [Set.mem_Ici] at hk; omega)
      simp only [Finset.mem_Icc]; omega⟩

omit [MeasurableSpace E] in
lemma rect_Icc_succ (i : ℤ) (n : ℕ) (B : ℤ → Set E) :
    rect (Finset.Icc i (i + (n + 1 : ℕ))) B
      = rect (Finset.Icc i (i + n)) B ∩ (fun σ ↦ σ (i + n + 1)) ⁻¹' B (i + n + 1) := by
  ext σ
  simp only [mem_rect, Finset.mem_Icc, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    exact ⟨fun j hj ↦ h j ⟨hj.1, by push_cast; omega⟩, h _ ⟨by omega, by push_cast; omega⟩⟩
  · rintro ⟨h₁, h₂⟩ j hj
    by_cases hj' : j = i + n + 1
    · exact hj' ▸ h₂
    · exact h₁ j ⟨hj.1, by push_cast at hj; omega⟩

omit [MeasurableSpace E] in
lemma rect_Icc_zero (i : ℤ) (B : ℤ → Set E) :
    rect (Finset.Icc i (i + (0 : ℕ))) B = (fun σ ↦ σ i) ⁻¹' B i := by
  ext σ; simp [rect]

omit [MeasurableSpace E] in
lemma Icc_erase_right (a b : ℤ) : (Finset.Icc a b).erase b = Finset.Icc a (b - 1) := by
  ext j; simp only [Finset.mem_erase, Finset.mem_Icc]; omega

/-! ### The chain kernel of (10.5) -/

/-- The kernel `x ↦ ∫_{B_{k+1}} P_{k+1}(x, dx_1) ⋯ ∫_{B_{k+n}} P_{k+n}(x_{n-1}, ·)` of Georgii
(10.5): the composition of the transition kernels `P_{k+1}, …, P_{k+n}` restricted to the sets
`B_{k+1}, …, B_{k+n}`. -/
def chainKernel (P : ℤ → Kernel E E) (hB : ∀ k, MeasurableSet (B k)) : ℕ → ℤ → Kernel E E
  | 0, _ => Kernel.id
  | n + 1, k => chainKernel P hB n (k + 1) ∘ₖ (P (k + 1)).restrict (hB (k + 1))

variable (hB : ∀ k, MeasurableSet (B k))

@[simp] lemma chainKernel_zero (k : ℤ) : chainKernel P hB 0 k = Kernel.id := rfl

lemma chainKernel_succ (n : ℕ) (k : ℤ) :
    chainKernel P hB (n + 1) k = chainKernel P hB n (k + 1) ∘ₖ (P (k + 1)).restrict (hB (k + 1)) :=
  rfl

/-- Peeling off the last step of the chain kernel. -/
lemma chainKernel_succ_last (n : ℕ) (k : ℤ) :
    chainKernel P hB (n + 1) k
      = (P (k + n + 1)).restrict (hB (k + n + 1)) ∘ₖ chainKernel P hB n k := by
  induction n generalizing k with
  | zero => simp [chainKernel_succ, Kernel.id_comp, Kernel.comp_id]
  | succ n ih =>
    rw [chainKernel_succ, ih, Kernel.comp_assoc, ← chainKernel_succ]
    have : k + 1 + n + 1 = k + (n + 1 : ℕ) + 1 := by push_cast; ring
    rw [this]

/-- The chain kernel only depends on the sets at the sites `k + 1, …, k + n`. -/
lemma chainKernel_congr {B' : ℤ → Set E} (hB' : ∀ k, MeasurableSet (B' k)) (n : ℕ) (k : ℤ)
    (h : ∀ j, k < j → j ≤ k + n → B j = B' j) : chainKernel P hB n k = chainKernel P hB' n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [chainKernel_succ, chainKernel_succ, ih (k + 1) fun j hj hj' ↦ h j (by omega)
      (by push_cast; omega)]
    congr 1
    ext x s hs
    rw [Kernel.restrict_apply' _ _ _ hs, Kernel.restrict_apply' _ _ _ hs,
      h (k + 1) (by omega) (by push_cast; omega)]

lemma chainKernel_apply_eq_of_eq {B' : ℤ → Set E} (hB' : ∀ k, MeasurableSet (B' k)) (n : ℕ)
    (k : ℤ) (h : ∀ j, k < j → j ≤ k + n → B j = B' j) (x : E) :
    chainKernel P hB n k x = chainKernel P hB' n k x := by
  rw [chainKernel_congr hB hB' n k h]

/-- The last step of the chain kernel, evaluated on a set: `(chainKernel (n+1) k) x S` integrates
`P_{k+n+1}(·, S ∩ B_{k+n+1})` against `(chainKernel n k) x`. -/
lemma chainKernel_succ_apply (n : ℕ) (k : ℤ) (x : E) {S : Set E} (hS : MeasurableSet S) :
    chainKernel P hB (n + 1) k x S
      = ∫⁻ y, P (k + n + 1) y (S ∩ B (k + n + 1)) ∂(chainKernel P hB n k x) := by
  rw [chainKernel_succ_last, Kernel.comp_apply' _ _ _ hS]
  exact lintegral_congr fun y ↦ Kernel.restrict_apply' _ _ _ hS

instance [∀ k, IsFiniteKernel (P k)] (n : ℕ) (k : ℤ) : IsFiniteKernel (chainKernel P hB n k) := by
  induction n generalizing k with
  | zero => rw [chainKernel_zero]; infer_instance
  | succ n ih => rw [chainKernel_succ]; infer_instance

/-- Georgii's iterated integral (10.5) in measure form, with the set at the last site
intersected with `S`: this is the chain kernel evaluated at `S`. -/
lemma chainKernel_update_last_apply_univ (n : ℕ) (k : ℤ) (x : E) {S : Set E}
    (hS : MeasurableSet S) :
    chainKernel P (B := Function.update B (k + n + 1) (B (k + n + 1) ∩ S))
      (fun j ↦ by
        by_cases hj : j = k + n + 1
        · subst hj; simp only [Function.update_self]; exact (hB _).inter hS
        · simp only [Function.update_of_ne hj]; exact hB j) (n + 1) k x Set.univ
      = chainKernel P hB (n + 1) k x S := by
  rw [chainKernel_succ_apply _ _ _ _ MeasurableSet.univ, chainKernel_succ_apply _ _ _ _ hS,
    Function.update_self, Set.univ_inter, chainKernel_apply_eq_of_eq _ hB n k
      (fun j hj hj' ↦ by rw [Function.update_of_ne (by omega)]) x]
  exact lintegral_congr fun y ↦ by rw [Set.inter_comm]

/-! ### Markov chains, Definition (10.4) -/

/-- **Georgii, Definition (10.4).** A probability measure `μ` on `E^ℤ` is a *Markov chain with
transition kernels* `(P_i)_{i ∈ ℤ}` if it satisfies (10.4)(ii):
`μ(σ_i ∈ A | 𝓕_{]-∞,i[}) = P_i(σ_{i-1}, A)` `μ`-a.s. for all `i ∈ ℤ` and `A ∈ 𝓔`.
The equivalent finite-dimensional formula (10.4)(i)/(10.5) is
    `isMarkovChain_iff_forall_measure_rect`. -/
structure IsMarkovChain (P : ℤ → Kernel E E) (μ : Measure (ℤ → E)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  condExp_preimage : ∀ (i : ℤ) (A : Set E), MeasurableSet A →
    μ[((fun σ : ℤ → E ↦ σ i) ⁻¹' A).indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Iio i)]
      =ᵐ[μ] fun σ ↦ (P i (σ (i - 1)) A).toReal

lemma measurable_cylinderEvents_kernel_apply (i : ℤ) {A : Set E} (hA : MeasurableSet A) :
    Measurable[cylinderEvents (Set.Iio i)] fun σ : ℤ → E ↦ P i (σ (i - 1)) A :=
  (Kernel.measurable_coe (P i) hA).comp
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (show i - 1 ∈ Set.Iio i by simp))

/-- (10.4)(ii) in set-integral form: `μ({σ_i ∈ A} ∩ t) = ∫_t P_i(σ_{i-1}, A) dμ` for every
`t ∈ 𝓕_{]-∞,i[}`. -/
lemma isMarkovChain_iff_forall_measure_inter [IsProbabilityMeasure μ]
    [∀ k, IsMarkovKernel (P k)] :
    IsMarkovChain P μ ↔ ∀ (i : ℤ) (A : Set E), MeasurableSet A →
      ∀ t, MeasurableSet[cylinderEvents (Set.Iio i)] t →
        μ ((fun σ ↦ σ i) ⁻¹' A ∩ t) = ∫⁻ σ in t, P i (σ (i - 1)) A ∂μ := by
  have key : ∀ (i : ℤ) (A : Set E), MeasurableSet A →
      ((μ[((fun σ : ℤ → E ↦ σ i) ⁻¹' A).indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Iio i)]
        =ᵐ[μ] (fun σ ↦ (P i (σ (i - 1)) A).toReal)) ↔
      ∀ t, MeasurableSet[cylinderEvents (Set.Iio i)] t →
        μ ((fun σ ↦ σ i) ⁻¹' A ∩ t) = ∫⁻ σ in t, P i (σ (i - 1)) A ∂μ) := fun i A hA ↦ by
    rw [Filter.eventuallyEq_comm]
    exact toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi
      (measurable_pi_apply i hA) (measure_ne_top _ _)
      (measurable_cylinderEvents_kernel_apply i hA).stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ measure_ne_top _ _)
  constructor
  · intro h i A hA
    exact (key i A hA).1 (h.condExp_preimage i A hA)
  · intro h
    exact ⟨inferInstance, fun i A hA ↦ (key i A hA).2 (h i A hA)⟩

lemma IsMarkovChain.measure_preimage_inter [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ)
    (i : ℤ) {A : Set E}
    (hA : MeasurableSet A) {t : Set (ℤ → E)} (ht : MeasurableSet[cylinderEvents (Set.Iio i)] t) :
    μ ((fun σ ↦ σ i) ⁻¹' A ∩ t) = ∫⁻ σ in t, P i (σ (i - 1)) A ∂μ := by
  have := h.isProbabilityMeasure
  exact isMarkovChain_iff_forall_measure_inter.1 h i A hA t ht

/-- The finite-dimensional distributions of a Markov chain, in measure form: for `D ∈ 𝓕_{]-∞,i[}`,
the law of `σ_{i+n}` under `μ` restricted to `D ∩ {σ_j ∈ B_j, i ≤ j ≤ i + n}` is the law of
`σ_i` under `μ|_D`, restricted to `B_i`, pushed through the chain kernel. -/
theorem IsMarkovChain.map_restrict_inter_rect [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ)
    (i : ℤ) {D : Set (ℤ → E)}
    (hD : MeasurableSet[cylinderEvents (Set.Iio i)] D) (n : ℕ) :
    (μ.restrict (D ∩ rect (Finset.Icc i (i + n)) B)).map (fun σ ↦ σ (i + n))
      = (((μ.restrict D).map (fun σ ↦ σ i)).restrict (B i)).bind (chainKernel P hB n i) := by
  induction n with
  | zero =>
    rw [rect_Icc_zero, chainKernel_zero]
    have hid : (⇑(Kernel.id : Kernel E E)) = Measure.dirac := funext Kernel.id_apply
    rw [hid, Measure.bind_dirac, Measure.restrict_map (measurable_pi_apply i) (hB i),
      Measure.restrict_restrict (measurable_pi_apply i (hB i)), Set.inter_comm]
    simp only [Nat.cast_zero, add_zero]
  | succ n ih =>
    have hcast : i + ((n + 1 : ℕ) : ℤ) = i + n + 1 := by push_cast; ring
    have hsucc : i + n + 1 - 1 = i + n := by ring
    have hrect : MeasurableSet[cylinderEvents (Set.Iio (i + n + 1))]
        (D ∩ rect (Finset.Icc i (i + n)) B) :=
      (cylinderEvents_mono (Set.Iio_subset_Iio (by omega)) _ hD).inter
        (measurableSet_cylinderEvents_rect (fun j hj ↦ by
          simp only [Finset.coe_Icc, Set.mem_Icc] at hj; simp only [Set.mem_Iio]; omega) hB)
    ext S hS
    have hg : Measurable fun y ↦ P (i + n + 1) y (B (i + n + 1) ∩ S) :=
      Kernel.measurable_coe _ ((hB _).inter hS)
    calc (μ.restrict (D ∩ rect (Finset.Icc i (i + (n + 1 : ℕ))) B)).map
          (fun σ ↦ σ (i + (n + 1 : ℕ))) S
        = μ ((fun σ ↦ σ (i + n + 1)) ⁻¹' (B (i + n + 1) ∩ S)
            ∩ (D ∩ rect (Finset.Icc i (i + n)) B)) := by
          rw [rect_Icc_succ, hcast, Measure.map_apply (measurable_pi_apply _) hS,
            Measure.restrict_apply (measurable_pi_apply _ hS)]
          congr 1
          ext σ; simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
      _ = ∫⁻ σ in D ∩ rect (Finset.Icc i (i + n)) B,
            P (i + n + 1) (σ (i + n)) (B (i + n + 1) ∩ S) ∂μ := by
          rw [h.measure_preimage_inter (i + n + 1) ((hB _).inter hS) hrect, hsucc]
      _ = ∫⁻ y, P (i + n + 1) y (B (i + n + 1) ∩ S)
            ∂((μ.restrict (D ∩ rect (Finset.Icc i (i + n)) B)).map (fun σ ↦ σ (i + n))) := by
          rw [lintegral_map hg (measurable_pi_apply _)]
      _ = ∫⁻ x, ∫⁻ y, P (i + n + 1) y (B (i + n + 1) ∩ S) ∂(chainKernel P hB n i x)
            ∂(((μ.restrict D).map (fun σ ↦ σ i)).restrict (B i)) := by
          rw [ih, Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
      _ = (((μ.restrict D).map (fun σ ↦ σ i)).restrict (B i)).bind
            (chainKernel P hB (n + 1) i) S := by
          rw [Measure.bind_apply hS (Kernel.aemeasurable _)]
          refine lintegral_congr fun x ↦ ?_
          rw [chainKernel_succ_apply _ _ _ _ hS, Set.inter_comm]

/-- **Georgii (10.5)**, the finite-dimensional distributions of a Markov chain:
`μ(σ_{i+j} ∈ A_j, 0 ≤ j ≤ n) = ∫_{A_0} σ_i(μ)(dx_0) ∫_{A_1} P_{i+1}(x_0, dx_1) ⋯ ∫_{A_n} P_{i+n}(x_{n-1}, dx_n)`. -/
theorem IsMarkovChain.measure_rect [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) (i : ℤ)
    (n : ℕ) :
    μ (rect (Finset.Icc i (i + n)) B)
      = ∫⁻ x in B i, chainKernel P hB n i x Set.univ ∂(μ.map fun σ ↦ σ i) := by
  have := h.map_restrict_inter_rect hB i (D := Set.univ) MeasurableSet.univ n
  have h1 := congrArg (fun ν : Measure E ↦ ν Set.univ) this
  simp only [Set.univ_inter, Measure.restrict_univ] at h1
  rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    at h1
  exact h1

/-- The measure form of (10.5) follows from the set form: if the finite-dimensional
distributions of `μ` are given by (10.5) for all rectangles, then the law of `σ_{i+n}` under
`μ` restricted to a rectangle is the corresponding chain-kernel image. -/
lemma map_restrict_rect_of_forall_measure_rect
    (h : ∀ (i : ℤ) (n : ℕ) (B : ℤ → Set E) (hB : ∀ k, MeasurableSet (B k)),
      μ (rect (Finset.Icc i (i + n)) B)
        = ∫⁻ x in B i, chainKernel P hB n i x Set.univ ∂(μ.map fun σ ↦ σ i))
    (i : ℤ) (n : ℕ) :
    (μ.restrict (rect (Finset.Icc i (i + n)) B)).map (fun σ ↦ σ (i + n))
      = ((μ.map (fun σ ↦ σ i)).restrict (B i)).bind (chainKernel P hB n i) := by
  classical
  ext S hS
  rw [Measure.map_apply (measurable_pi_apply _) hS, Measure.restrict_apply (measurable_pi_apply _
      hS),
    Measure.bind_apply hS (Kernel.aemeasurable _)]
  cases n with
  | zero =>
    rw [rect_Icc_zero]
    simp only [Nat.cast_zero, add_zero, chainKernel_zero, Kernel.id_apply]
    rw [← Set.preimage_inter, ← Measure.map_apply (measurable_pi_apply i) (hS.inter (hB i))]
    calc (μ.map fun σ ↦ σ i) (S ∩ B i)
        = ((μ.map fun σ ↦ σ i).restrict (B i)) S := (Measure.restrict_apply hS).symm
      _ = ∫⁻ x in B i, S.indicator 1 x ∂(μ.map fun σ ↦ σ i) := (lintegral_indicator_one hS).symm
      _ = _ := lintegral_congr fun x ↦ (Measure.dirac_apply' _ hS).symm
  | succ n =>
    have hcast : i + ((n + 1 : ℕ) : ℤ) = i + n + 1 := by push_cast; ring
    set B' := Function.update B (i + n + 1) (B (i + n + 1) ∩ S) with hB'
    have hB'm : ∀ k, MeasurableSet (B' k) := fun j ↦ by
      by_cases hj : j = i + n + 1
      · subst hj; simp only [hB', Function.update_self]; exact (hB _).inter hS
      · simp only [hB', Function.update_of_ne hj]; exact hB j
    have hset : (fun σ : ℤ → E ↦ σ (i + (n + 1 : ℕ))) ⁻¹' S ∩ rect (Finset.Icc i (i + (n + 1 :
        ℕ))) B
        = rect (Finset.Icc i (i + (n + 1 : ℕ))) B' := by
      rw [hB', rect_update (by simp only [Finset.mem_Icc]; omega), rect_eq_erase_inter
        (B := B) (show i + (n + 1 : ℕ) ∈ Finset.Icc i (i + (n + 1 : ℕ)) by
          simp only [Finset.mem_Icc]; omega), hcast]
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [hset, h i (n + 1) B' hB'm]
    have hBi : B' i = B i := by rw [hB', Function.update_of_ne (by omega)]
    rw [hBi]
    refine setLIntegral_congr_fun (hB i) fun x _ ↦ ?_
    have := chainKernel_update_last_apply_univ (P := P) hB n i x hS
    convert this using 2

/-- **Georgii (10.4)(i) ⇒ (ii).** A probability measure whose finite-dimensional distributions
are given by (10.5) is a Markov chain. -/
theorem isMarkovChain_of_forall_measure_rect [IsProbabilityMeasure μ] [∀ k, IsMarkovKernel (P k)]
    (h : ∀ (i : ℤ) (n : ℕ) (B : ℤ → Set E) (hB : ∀ k, MeasurableSet (B k)),
      μ (rect (Finset.Icc i (i + n)) B)
        = ∫⁻ x in B i, chainKernel P hB n i x Set.univ ∂(μ.map fun σ ↦ σ i)) :
    IsMarkovChain P μ := by
  classical
  rw [isMarkovChain_iff_forall_measure_inter]
  intro i A hA
  have hg : Measurable fun σ : ℤ → E ↦ P i (σ (i - 1)) A :=
    (Kernel.measurable_coe (P i) hA).comp (measurable_pi_apply _)
  have hgE : Measurable fun y : E ↦ P i y A := Kernel.measurable_coe (P i) hA
  -- both sides are finite measures in `t`; compare them on the rectangles generating `𝓕_{]-∞,i[}`
  have hfin : IsFiniteMeasure (μ.withDensity fun σ : ℤ → E ↦ P i (σ (i - 1)) A) :=
    isFiniteMeasure_withDensity (ne_top_of_le_ne_top (measure_ne_top μ Set.univ) (by
      calc ∫⁻ σ, P i (σ (i - 1)) A ∂μ ≤ ∫⁻ _, 1 ∂μ := lintegral_mono fun σ ↦ prob_le_one
        _ = μ Set.univ := by simp))
  intro t ht
  have key : ∀ (m : ℕ) (B' : ℤ → Set E) (hB' : ∀ k, MeasurableSet (B' k)),
      μ (rect (Finset.Icc (i - m - 1) (i - 1)) B' ∩ (fun σ : ℤ → E ↦ σ i) ⁻¹' A)
        = ∫⁻ σ in rect (Finset.Icc (i - m - 1) (i - 1)) B', P i (σ (i - 1)) A ∂μ := by
    intro m B' hB'
    set B'' := Function.update B' i A with hB''
    have hB''m : ∀ k, MeasurableSet (B'' k) := fun k ↦ by
      by_cases hk : k = i
      · subst hk; simp [hB'', hA]
      · simp [hB'', Function.update_of_ne hk, hB' k]
    have h1 : i - m - 1 + (m + 1 : ℕ) = i := by push_cast; ring
    have h2 : i - m - 1 + m = i - 1 := by ring
    have hset : rect (Finset.Icc (i - m - 1) (i - 1)) B' ∩ (fun σ : ℤ → E ↦ σ i) ⁻¹' A
        = rect (Finset.Icc (i - m - 1) (i - m - 1 + (m + 1 : ℕ))) B'' := by
      rw [h1, hB'', rect_update (by simp only [Finset.mem_Icc]; omega),
        Icc_erase_right, Set.inter_comm]
    rw [hset, h _ _ B'' hB''m, show B'' (i - m - 1) = B' (i - m - 1) by
      rw [hB'', Function.update_of_ne (by omega)]]
    -- the right-hand side through the measure form of (10.5) at level `m`
    have hM := map_restrict_rect_of_forall_measure_rect (B := B') hB' h (i - m - 1) m
    rw [h2] at hM
    calc ∫⁻ x in B' (i - m - 1), chainKernel P hB''m (m + 1) (i - m - 1) x Set.univ
          ∂(μ.map fun σ ↦ σ (i - m - 1))
        = ∫⁻ x in B' (i - m - 1), ∫⁻ y, P i y A ∂(chainKernel P hB' m (i - m - 1) x)
          ∂(μ.map fun σ ↦ σ (i - m - 1)) := by
          refine setLIntegral_congr_fun (hB' _) fun x _ ↦ ?_
          rw [chainKernel_succ_apply _ _ _ _ MeasurableSet.univ, h2, show i - 1 + 1 = i by ring,
            Set.univ_inter, chainKernel_apply_eq_of_eq hB''m hB' m (i - m - 1)
              (fun j hj hj' ↦ by rw [hB'', Function.update_of_ne (by omega)]) x]
          refine lintegral_congr fun y ↦ ?_
          rw [hB'', Function.update_self]
      _ = ∫⁻ y, P i y A ∂(((μ.map fun σ ↦ σ (i - m - 1)).restrict (B' (i - m - 1))).bind
            (chainKernel P hB' m (i - m - 1))) := by
          rw [Measure.lintegral_bind (Kernel.aemeasurable _) hgE.aemeasurable]
      _ = ∫⁻ y, P i y A ∂((μ.restrict (rect (Finset.Icc (i - m - 1) (i - 1)) B')).map
            fun σ ↦ σ (i - 1)) := by rw [hM]
      _ = ∫⁻ σ in rect (Finset.Icc (i - m - 1) (i - 1)) B', P i (σ (i - 1)) A ∂μ := by
          rw [lintegral_map hgE (measurable_pi_apply _)]
  have := ext_on_measurableSpace_of_generate_finite (MeasurableSpace.pi)
    (μ := μ.restrict ((fun σ : ℤ → E ↦ σ i) ⁻¹' A))
    (ν := μ.withDensity fun σ : ℤ → E ↦ P i (σ (i - 1)) A)
    (rectangles E fun n ↦ Finset.Icc (i - n - 1) (i - 1)) ?_ cylinderEvents_le_pi
    (cylinderEvents_Iio_eq_generateFrom i) (isPiSystem_rectangles (monotone_Icc_left' i)) ?_ ht
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _
      (cylinderEvents_le_pi _ ht), Set.inter_comm] at this
    exact this
  · rintro _ ⟨m, B', hB', rfl⟩
    rw [Measure.restrict_apply' (measurable_pi_apply i hA),
      withDensity_apply _ (measurableSet_rect hB')]
    exact key m B' hB'
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Set.univ_inter]
    have := key 0 (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
    have huniv : rect (Finset.Icc (i - (0 : ℕ) - 1) (i - 1)) (fun _ : ℤ ↦ (Set.univ : Set E))
        = Set.univ := by ext; simp [rect]
    rw [huniv, Set.univ_inter, Measure.restrict_univ] at this
    exact this

/-- **Georgii, Definition (10.4): (i) ⟺ (ii).** For probability kernels `P_i`, a probability
measure `μ` is a Markov chain with transition kernels `(P_i)` iff its finite-dimensional
distributions are given by (10.5). -/
theorem isMarkovChain_iff_forall_measure_rect [IsProbabilityMeasure μ]
    [∀ k, IsMarkovKernel (P k)] :
    IsMarkovChain P μ ↔ ∀ (i : ℤ) (n : ℕ) (B : ℤ → Set E) (hB : ∀ k, MeasurableSet (B k)),
      μ (rect (Finset.Icc i (i + n)) B)
        = ∫⁻ x in B i, chainKernel P hB n i x Set.univ ∂(μ.map fun σ ↦ σ i) :=
  ⟨fun h i n _ hB ↦ h.measure_rect hB i n, isMarkovChain_of_forall_measure_rect⟩

/-! ### The one-sided Markov property of a Markov chain, (10.7) and (10.8) -/

/-- **Georgii (10.7).** A Markov chain has the left-sided Markov property:
`μ(A | 𝓕_{]-∞,i]}) = μ(A | 𝓕_{{i}})` for `A ∈ 𝓕_{[i,∞[}`. -/
theorem IsMarkovChain.isLeftMarkov [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) :
    IsLeftMarkov μ := by
  classical
  have := h.isProbabilityMeasure
  intro i A hA
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hle : cylinderEvents (X := fun _ : ℤ ↦ E) ({i} : Set ℤ) ≤ cylinderEvents (Set.Iic i) :=
    cylinderEvents_mono (by simp)
  -- Step 1: the rectangles `{σ_j ∈ B_j, i ≤ j ≤ i + n}` satisfy (10.7)
  have hrect : ∀ (n : ℕ) (B : ℤ → Set E) (hB : ∀ k, MeasurableSet (B k)),
      μ[(rect (Finset.Icc i (i + n)) B).indicator (1 : (ℤ → E) → ℝ) | cylinderEvents (Set.Iic i)]
        =ᵐ[μ] μ[(rect (Finset.Icc i (i + n)) B).indicator (1 : (ℤ → E) → ℝ) |
          cylinderEvents ({i} : Set ℤ)] := by
    intro n B hB
    set F : E → ℝ≥0∞ := (B i).indicator fun x ↦ chainKernel P hB n i x Set.univ with hF
    have hFm : Measurable F := (Kernel.measurable_coe _ MeasurableSet.univ).indicator (hB i)
    have hFfin : ∀ x, F x ≠ ⊤ := fun x ↦ by
      by_cases hx : x ∈ B i
      · simp only [hF, Set.indicator_of_mem hx]; exact measure_ne_top _ _
      · simp [hF, Set.indicator_of_notMem hx]
    have hFσ : Measurable[cylinderEvents ({i} : Set ℤ)] fun σ : ℤ → E ↦ F (σ i) :=
      hFm.comp (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (Set.mem_singleton i))
    have hR : MeasurableSet (rect (Finset.Icc i (i + n)) B) := measurableSet_rect hB
    -- `μ(rect ∩ D) = ∫_D F(σ_i) dμ` on the rectangles `D` over `[i - m, i]`
    have basic : ∀ (m : ℕ) (B' : ℤ → Set E) (hB' : ∀ k, MeasurableSet (B' k)),
        μ (rect (Finset.Icc i (i + n)) B ∩ rect (Finset.Icc (i - m) i) B')
          = ∫⁻ σ in rect (Finset.Icc (i - m) i) B', F (σ i) ∂μ := by
      intro m B' hB'
      have hD₀ : MeasurableSet[cylinderEvents (Set.Iio i)] (rect (Finset.Icc (i - m) (i - 1)) B') :=
        measurableSet_cylinderEvents_rect (fun j hj ↦ by
          simp only [Finset.coe_Icc, Set.mem_Icc] at hj; simp only [Set.mem_Iio]; omega) hB'
      have hsplit : rect (Finset.Icc (i - m) i) B'
          = rect (Finset.Icc (i - m) (i - 1)) B' ∩ (fun σ ↦ σ i) ⁻¹' B' i := by
        rw [rect_eq_erase_inter (show i ∈ Finset.Icc (i - m) i by simp), Icc_erase_right]
      set B'' := Function.update B i (B i ∩ B' i) with hB''
      have hB''m : ∀ k, MeasurableSet (B'' k) := fun k ↦ by
        by_cases hk : k = i
        · subst hk; simp only [hB'', Function.update_self]; exact (hB _).inter (hB' _)
        · simp only [hB'', Function.update_of_ne hk]; exact hB k
      have hset : rect (Finset.Icc i (i + n)) B ∩ rect (Finset.Icc (i - m) i) B'
          = rect (Finset.Icc (i - m) (i - 1)) B' ∩ rect (Finset.Icc i (i + n)) B'' := by
        rw [hsplit, hB'', rect_update (by simp), rect_eq_erase_inter (B := B)
          (show i ∈ Finset.Icc i (i + n) by simp)]
        ext σ
        simp only [Set.mem_inter_iff, Set.mem_preimage]
        tauto
      rw [hset]
      have hM := h.map_restrict_inter_rect hB''m i hD₀ n
      have h1 := congrArg (fun ν : Measure E ↦ ν Set.univ) hM
      rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply_univ, Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
        at h1
      rw [h1, ← lintegral_indicator (hB''m i), lintegral_map
        ((Kernel.measurable_coe _ MeasurableSet.univ).indicator (hB''m i)) (measurable_pi_apply i),
        hsplit, Set.inter_comm, ← Measure.restrict_restrict (measurable_pi_apply i (hB' i)),
        ← lintegral_indicator (measurable_pi_apply i (hB' i))]
      refine lintegral_congr fun σ ↦ ?_
      have hK := chainKernel_apply_eq_of_eq (P := P) hB''m hB n i
        (fun j hj hj' ↦ by rw [hB'', Function.update_of_ne (by omega)]) (σ i)
      simp only [hB'', Function.update_self, hF, Set.indicator, Set.mem_inter_iff,
        Set.mem_preimage, hK]
      by_cases h₁ : σ i ∈ B i <;> by_cases h₂ : σ i ∈ B' i <;> simp [h₁, h₂]
    have key : ∀ D, MeasurableSet[cylinderEvents (Set.Iic i)] D →
        μ (rect (Finset.Icc i (i + n)) B ∩ D) = ∫⁻ σ in D, F (σ i) ∂μ := by
      intro D hD
      have := ext_on_measurableSpace_of_generate_finite (MeasurableSpace.pi)
        (μ := μ.restrict (rect (Finset.Icc i (i + n)) B))
        (ν := μ.withDensity fun σ : ℤ → E ↦ F (σ i))
        (rectangles E fun m ↦ Finset.Icc (i - m) i) ?_ cylinderEvents_le_pi
        (cylinderEvents_Iic_eq_generateFrom i) (isPiSystem_rectangles (monotone_Icc_left i)) ?_ hD
      · rwa [Measure.restrict_apply' hR, withDensity_apply _ (cylinderEvents_le_pi _ hD),
          Set.inter_comm] at this
      · rintro _ ⟨m, B', hB', rfl⟩
        rw [Measure.restrict_apply' hR, withDensity_apply _ (measurableSet_rect hB'),
          Set.inter_comm]
        exact basic m B' hB'
      · have := basic 0 (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
        have huniv : rect (Finset.Icc (i - (0 : ℕ)) i) (fun _ : ℤ ↦ (Set.univ : Set E))
            = Set.univ := by ext; simp [rect]
        rw [huniv, Set.inter_univ, Measure.restrict_univ] at this
        rw [Measure.restrict_apply' hR, withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ, Set.univ_inter]
        exact this
    have hg1 : (fun σ ↦ (F (σ i)).toReal) =ᵐ[μ]
        μ[(rect (Finset.Icc i (i + n)) B).indicator (1 : (ℤ → E) → ℝ) |
          cylinderEvents (Set.Iic i)] :=
      (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi hR
        (measure_ne_top _ _) (hFσ.mono hle le_rfl).stronglyMeasurable.aestronglyMeasurable
        (ae_of_all _ fun σ ↦ hFfin _)).2 key
    have hg2 : (fun σ ↦ (F (σ i)).toReal) =ᵐ[μ]
        μ[(rect (Finset.Icc i (i + n)) B).indicator (1 : (ℤ → E) → ℝ) |
          cylinderEvents ({i} : Set ℤ)] :=
      (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi hR
        (measure_ne_top _ _) hFσ.stronglyMeasurable.aestronglyMeasurable
        (ae_of_all _ fun σ ↦ hFfin _)).2 fun t ht ↦ key t (hle _ ht)
    exact hg1.symm.trans hg2
  -- Step 2: extend from rectangles to all of `𝓕_{[i,∞[}`
  rw [condExp_indicator_ae_eq_iff_forall_setIntegral' hle cylinderEvents_le_pi hA']
  intro D hD
  have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
  rw [inter_comm, ← setIntegral_indicator_one' hD' A]
  refine setIntegral_eq_of_generateFrom cylinderEvents_le_pi
    (isPiSystem_rectangles (monotone_Icc_right i)) (cylinderEvents_Ici_eq_generateFrom i)
    integrable_condExp (integrable_indicator_one hD') ?_
    (integral_condExp (μ := μ) cylinderEvents_le_pi) A hA
  rintro _ ⟨n, B, hB, rfl⟩
  have := (condExp_indicator_ae_eq_iff_forall_setIntegral' hle cylinderEvents_le_pi
    (measurableSet_rect hB)).1 (hrect n B hB) D hD
  rw [this, setIntegral_indicator_one' hD' _, inter_comm]

/-- **Georgii (10.8).** A Markov chain has the right-sided Markov property. -/
theorem IsMarkovChain.isRightMarkov [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) :
    IsRightMarkov μ :=
  have := h.isProbabilityMeasure
  isLeftMarkov_iff_isRightMarkov.1 h.isLeftMarkov

/-- A Markov chain has the one-sided Markov property. -/
theorem IsMarkovChain.isOneSidedMarkov [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) :
    IsOneSidedMarkov μ :=
  ⟨h.isLeftMarkov, h.isRightMarkov⟩

/-- **Georgii, Remark (10.9)(3).** Every Markov chain is a Markov field. -/
theorem IsMarkovChain.isMarkovField [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) :
    IsMarkovField μ :=
  have := h.isProbabilityMeasure
  h.isOneSidedMarkov.isMarkovField

/-- **Georgii, Remark (10.9)(2).** Every Markov chain has the global Markov property. -/
theorem IsMarkovChain.isGlobalMarkov [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ) :
    IsGlobalMarkov μ :=
  have := h.isProbabilityMeasure
  isOneSidedMarkov_iff_isGlobalMarkov.1 h.isOneSidedMarkov

end MeasureTheory.GibbsMeasure.Markov

/-! ## Georgii (10.2): Markov specifications on `ℤ` -/

namespace Specification

open MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] {ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞}

/-- **Georgii, Definition (10.2).** A specification `γ` on `ℤ` is a *Markov specification* if
`γ_{]i,k[}(A | ·)` is `𝓕_{{i,k}}`-measurable for all `A ∈ 𝓕_{]i,k[}` and all `i + 1 < k`: the
finite-volume kernel of an interval depends on the boundary condition only through the two
endpoints of the interval (the boundary `∂]i,k[ = {i, k}`). -/
def IsMarkovInt (γ : Specification ℤ E) : Prop :=
  ∀ i k : ℤ, i + 1 < k → ∀ A, MeasurableSet[cylinderEvents (Set.Ioo i k)] A →
    Measurable[cylinderEvents ({i, k} : Set ℤ)] fun ω ↦ γ (Finset.Ioo i k) ω A

/-- **Georgii, Definition (10.2).** A family of densities `ρ` (a λ-modification) is *Markovian*
if `ρ_{]i,k[}` is `𝓕_{[i,k]}`-measurable whenever `i + 1 < k`. -/
def IsMarkovianInt (ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞) : Prop :=
  ∀ i k : ℤ, i + 1 < k → Measurable[cylinderEvents (Set.Icc i k)] (ρ (Finset.Ioo i k))

lemma IsMarkovianInt.dependsOn (hρ : IsMarkovianInt ρ) {i k : ℤ} (hik : i + 1 < k) :
    DependsOn (ρ (Finset.Ioo i k)) ((Finset.Ioo i k : Set ℤ) ∪ {i, k}) :=
  (hρ i k hik).dependsOn_of_cylinderEvents.mono fun j hj ↦ by
    simp only [Finset.coe_Ioo, Set.mem_union, Set.mem_Ioo, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_Icc] at hj ⊢
    omega

/-! ### Normalised resampling densities depend only on the boundary -/

section Resampling

variable {Λ : Finset ℤ} {Δ : Set ℤ}

/-- For a density `f` whose values on the resampled configurations `juxt Λ ω ξ` depend on `ω`
only through the coordinates in `Δ`, the modified kernel `A ↦ ∫_A f dλ_Λ(·|ω)` depends on `ω`
only through `Δ` on the `𝓕_Λ`-events `A`. -/
lemma dependsOn_withDensity_map_juxt (m : Measure (Λ → E)) {f : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f)
    (hfdep : ∀ ⦃ω ω' : ℤ → E⦄, (∀ i ∈ Δ, ω i = ω' i) → ∀ ξ,
      f (juxt (Λ : Set ℤ) ω ξ) = f (juxt (Λ : Set ℤ) ω' ξ))
    {A : Set (ℤ → E)} (hA : MeasurableSet[cylinderEvents (Λ : Set ℤ)] A) :
    DependsOn (fun ω : ℤ → E ↦ ((Measure.map (juxt (Λ : Set ℤ) ω) m).withDensity f) A) Δ := by
  intro ω ω' h
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  simp only [withDensity_apply _ hA', ← lintegral_indicator hA',
    lintegral_map (hf.indicator hA') Measurable.juxt]
  refine lintegral_congr fun ξ ↦ ?_
  have hmem : juxt (Λ : Set ℤ) ω ξ ∈ A ↔ juxt (Λ : Set ℤ) ω' ξ ∈ A :=
    mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ by simp [juxt_apply_of_mem hi]
  by_cases hx : juxt (Λ : Set ℤ) ω ξ ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.1 hx), hfdep h ξ]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h' ↦ hx (hmem.2 h')]

/-- The normalised density `ρ / Z` with `Z(η) = ∫ ρ dλ_Λ(·|η)`, evaluated on the resampled
configurations `juxt Λ ω ξ`, depends on `ω` only through `Δ` as soon as `ρ` depends only on the
coordinates in `Λ ∪ Δ`. -/
lemma div_lintegral_map_juxt_congr (m : Measure (Λ → E)) {ρ : (ℤ → E) → ℝ≥0∞}
    (hρ : Measurable ρ) (hdep : DependsOn ρ ((Λ : Set ℤ) ∪ Δ)) ⦃ω ω' : ℤ → E⦄
    (h : ∀ i ∈ Δ, ω i = ω' i) (ξ : Λ → E) :
    ρ (juxt (Λ : Set ℤ) ω ξ)
        / ∫⁻ y, ρ y ∂(Measure.map (juxt (Λ : Set ℤ) (juxt (Λ : Set ℤ) ω ξ)) m)
      = ρ (juxt (Λ : Set ℤ) ω' ξ)
        / ∫⁻ y, ρ y ∂(Measure.map (juxt (Λ : Set ℤ) (juxt (Λ : Set ℤ) ω' ξ)) m) := by
  have hagree : ∀ ξ' : Λ → E, ∀ i ∈ ((Λ : Set ℤ) ∪ Δ),
      juxt (Λ : Set ℤ) ω ξ' i = juxt (Λ : Set ℤ) ω' ξ' i := fun ξ' i hi ↦ by
    rcases hi with hi | hi
    · simp [juxt_apply_of_mem hi]
    · by_cases hiΛ : i ∈ (Λ : Set ℤ)
      · simp [juxt_apply_of_mem hiΛ]
      · simp [juxt_apply_of_not_mem hiΛ, h i hi]
  rw [hdep (hagree ξ)]
  congr 1
  rw [lintegral_map hρ Measurable.juxt, lintegral_map hρ Measurable.juxt]
  simp_rw [juxt_juxt]
  exact lintegral_congr fun ξ' ↦ hdep (hagree ξ')

end Resampling

/-- **Georgii, after Definition (10.2).** A specification whose interval kernels are the
normalised densities `ρ_Λ / λ_Λ ρ_Λ` against the independent resampling kernels of a
probability measure `ν` is Markov as soon as `ρ` is Markovian. -/
theorem isMarkovInt_of_forall_apply_eq (γ : Specification ℤ E) (ν : Measure E)
    [IsProbabilityMeasure ν] (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ)
    (h : ∀ (Λ : Finset ℤ) (η : ℤ → E),
      γ Λ η = (isssd ν Λ η).withDensity (premodifierNorm ν ρ Λ)) :
    IsMarkovInt γ := by
  intro i k hik A hA
  set Λ := Finset.Ioo i k with hΛdef
  have hΛ : (Λ : Set ℤ) = Set.Ioo i k := Finset.coe_Ioo i k
  have hA' : MeasurableSet[cylinderEvents (Λ : Set ℤ)] A := by rw [hΛ]; exact hA
  have hmeas : Measurable fun ω ↦ γ Λ ω A :=
    ((γ Λ).measurable_coe (cylinderEvents_le_pi _ hA)).mono cylinderEvents_le_pi le_rfl
  refine hmeas.cylinderEvents_of_dependsOn ?_
  have hdep : DependsOn (ρ Λ) ((Λ : Set ℤ) ∪ {i, k}) := hM.dependsOn hik
  have key : ∀ ω, γ Λ ω A
      = ((Measure.map (juxt (Λ : Set ℤ) ω) (Measure.pi fun _ : Λ ↦ ν)).withDensity
        fun x ↦ ρ Λ x / ∫⁻ y, ρ Λ y ∂(Measure.map (juxt (Λ : Set ℤ) x)
          (Measure.pi fun _ : Λ ↦ ν))) A := fun ω ↦ by
    rw [h]
    rfl
  simp_rw [key]
  refine dependsOn_withDensity_map_juxt _ ?_ (fun ω ω' hωω' ξ ↦ ?_) hA'
  · exact measurable_relNorm (γ := isssd ν) hρ Λ
  · exact div_lintegral_map_juxt_congr _ (hρ Λ) hdep hωω' ξ

/-- **Georgii, after Definition (10.2)**, for a σ-finite a priori measure: the λ-specification
`ρλ` of a Markovian pre-modification is a Markov specification. -/
theorem isMarkovInt_lambdaSpecification (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hρ : IsPremodifier ρ) (hZ : IsSigmaFiniteLambdaAdmissible ν ρ) (hM : IsMarkovianInt ρ) :
    IsMarkovInt (lambdaSpecification ν ρ hρ hZ) := by
  intro i k hik A hA
  set Λ := Finset.Ioo i k with hΛdef
  have hΛ : (Λ : Set ℤ) = Set.Ioo i k := Finset.coe_Ioo i k
  have hA' : MeasurableSet[cylinderEvents (Λ : Set ℤ)] A := by rw [hΛ]; exact hA
  have hmeas : Measurable fun ω ↦ lambdaSpecification ν ρ hρ hZ Λ ω A :=
    ((lambdaSpecification ν ρ hρ hZ Λ).measurable_coe (cylinderEvents_le_pi _ hA)).mono
      cylinderEvents_le_pi le_rfl
  refine hmeas.cylinderEvents_of_dependsOn ?_
  have hdep : DependsOn (ρ Λ) ((Λ : Set ℤ) ∪ {i, k}) := hM.dependsOn hik
  have hnorm : sigmaFinitePremodifierNorm ν ρ Λ
      = fun x ↦ ρ Λ x / ∫⁻ y, ρ Λ y ∂(Measure.map (juxt (Λ : Set ℤ) x)
          (Measure.pi fun _ : Λ ↦ ν)) := by
    funext x
    rw [sigmaFinitePremodifierNorm, sigmaFiniteLambdaZ, sigmaFiniteLambdaFun_apply_eq_map]
  have key : ∀ ω, lambdaSpecification ν ρ hρ hZ Λ ω A
      = ((Measure.map (juxt (Λ : Set ℤ) ω) (Measure.pi fun _ : Λ ↦ ν)).withDensity
        fun x ↦ ρ Λ x / ∫⁻ y, ρ Λ y ∂(Measure.map (juxt (Λ : Set ℤ) x)
          (Measure.pi fun _ : Λ ↦ ν))) A := fun ω ↦ by
    rw [lambdaSpecification_apply, sigmaFiniteLambdaFun_apply_eq_map, hnorm]
  simp_rw [key]
  refine dependsOn_withDensity_map_juxt _ ?_ (fun ω ω' hωω' ξ ↦ ?_) hA'
  · rw [← hnorm]; exact sigmaFinitePremodifierNorm_measurable ν hρ Λ
  · exact div_lintegral_map_juxt_congr _ (hρ.measurable Λ) hdep hωω' ξ

/-! ### Georgii, Example (10.3): transition densities -/

/-- **Georgii, Example (10.3).** The family `g_Λ(ω) = ∏_{j} p_{j+1}(ω_j, ω_{j+1})`, the product
over the bonds `{j, j + 1}` meeting `Λ` (`bondsOf Λ`, indexed by the left endpoint `j`), the factor
of the bond `{j, j + 1}` being the transition density `p_{j+1}` into its right endpoint; for an
interval `Λ = ]i,k[` this is Georgii's `g_{i,k}(ω) = ∏_{j=i+1}^{k} p_j(ω_{j-1}, ω_j)`
(`chainDensity_Ioo`). -/
def chainDensity (p : ℤ → E → E → ℝ≥0∞) (Λ : Finset ℤ) (ω : ℤ → E) : ℝ≥0∞ :=
  ∏ j ∈ bondsOf Λ, p (j + 1) (ω j) (ω (j + 1))

variable {p : ℤ → E → E → ℝ≥0∞}

omit [MeasurableSpace E] in
lemma chainDensity_Ioo_eq_prod_Ico {i k : ℤ} (h : i + 1 < k) (ω : ℤ → E) :
    chainDensity p (Finset.Ioo i k) ω = ∏ j ∈ Finset.Ico i k, p (j + 1) (ω j) (ω (j + 1)) := by
  rw [chainDensity, bondsOf_Ioo h]

omit [MeasurableSpace E] in
/-- Georgii's `g_{i,k}(ω) = ∏_{j=i+1}^{k} p_j(ω_{j-1}, ω_j)` of Example (10.3). -/
lemma chainDensity_Ioo {i k : ℤ} (h : i + 1 < k) (ω : ℤ → E) :
    chainDensity p (Finset.Ioo i k) ω = ∏ j ∈ Finset.Ioc i k, p j (ω (j - 1)) (ω j) := by
  rw [chainDensity_Ioo_eq_prod_Ico h]
  refine Finset.prod_nbij' (· + 1) (· - 1) (fun j hj ↦ ?_) (fun j hj ↦ ?_) (fun _ _ ↦ by omega)
    (fun _ _ ↦ by omega) fun j _ ↦ by rw [add_sub_cancel_right]
  · simp only [Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢; omega
  · simp only [Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢; omega

omit [MeasurableSpace E] in
lemma chainDensity_Icc {a b : ℤ} (hab : a ≤ b) (ω : ℤ → E) :
    chainDensity p (Finset.Icc a b) ω
      = ∏ j ∈ Finset.Ico (a - 1) (b + 1), p (j + 1) (ω j) (ω (j + 1)) := by
  rw [chainDensity, bondsOf_Icc hab]

omit [MeasurableSpace E] in
lemma chainDensity_singleton (i : ℤ) (ω : ℤ → E) :
    chainDensity p {i} ω = p i (ω (i - 1)) (ω i) * p (i + 1) (ω i) (ω (i + 1)) := by
  rw [chainDensity, bondsOf_singleton, Finset.prod_pair (by omega), sub_add_cancel]

omit [MeasurableSpace E] in
/-- `g_Λ` depends only on the spins on the bonds meeting `Λ`. -/
lemma chainDensity_congr {Λ : Finset ℤ} {ω ω' : ℤ → E}
    (h : ∀ j ∈ bondsOf Λ, ω j = ω' j ∧ ω (j + 1) = ω' (j + 1)) :
    chainDensity p Λ ω = chainDensity p Λ ω' :=
  Finset.prod_congr rfl fun j hj ↦ by rw [(h j hj).1, (h j hj).2]

omit [MeasurableSpace E] in
lemma chainDensity_pos (hpos : ∀ j x y, 0 < p j x y) (Λ : Finset ℤ) (ω : ℤ → E) :
    0 < chainDensity p Λ ω :=
  pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦ (hpos _ _ _).ne')

omit [MeasurableSpace E] in
lemma chainDensity_ne_top (htop : ∀ j x y, p j x y ≠ ⊤) (Λ : Finset ℤ) (ω : ℤ → E) :
    chainDensity p Λ ω ≠ ⊤ :=
  (ENNReal.prod_lt_top fun _ _ ↦ (htop _ _ _).lt_top).ne

omit [MeasurableSpace E] in
/-- `g_{Λ₁ ∪ Λ₂} = g_{Λ₁} g_{Λ₂}` for volumes with no common bond. -/
lemma chainDensity_union {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂))
    (ω : ℤ → E) : chainDensity p (Λ₁ ∪ Λ₂) ω = chainDensity p Λ₁ ω * chainDensity p Λ₂ ω := by
  rw [chainDensity, bondsOf_union, Finset.prod_union h]
  rfl

omit [MeasurableSpace E] in
/-- The chain densities commute in the sense of Georgii (1.28)(5): the factors of `g_{Λ₂}` that
are not factors of `g_{Λ₁}` live on bonds not meeting `Λ₁`, hence agree on configurations agreeing
off `Λ₁`. -/
lemma chainDensity_mul_comm_of_subset {Λ₁ Λ₂ : Finset ℤ} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : ℤ → E}
    (hζη : ∀ s ∉ Λ₁, ζ s = η s) :
    chainDensity p Λ₂ ζ * chainDensity p Λ₁ η = chainDensity p Λ₁ ζ * chainDensity p Λ₂ η := by
  have hsplit : ∀ σ : ℤ → E, chainDensity p Λ₂ σ
      = (∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, p (j + 1) (σ j) (σ (j + 1))) * chainDensity p Λ₁ σ :=
    fun σ ↦ (Finset.prod_sdiff (bondsOf_mono hΛ)).symm
  have hrest : ∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, p (j + 1) (ζ j) (ζ (j + 1))
      = ∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, p (j + 1) (η j) (η (j + 1)) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hj' := (Finset.mem_sdiff.1 hj).2
    rw [mem_bondsOf, not_or] at hj'
    rw [hζη _ hj'.1, hζη _ hj'.2]
  rw [hsplit ζ, hsplit η, hrest]
  ring

lemma measurable_chainDensity (hp : ∀ j, Measurable (Function.uncurry (p j))) (Λ : Finset ℤ) :
    Measurable (chainDensity p Λ) := by
  refine Finset.measurable_prod _ fun j _ ↦ ?_
  exact Measurable.comp (hp (j + 1)) (f := fun a : ℤ → E ↦ (a j, a (j + 1)))
    ((measurable_pi_apply j).prodMk (measurable_pi_apply (j + 1)))

/-- The chain densities form a pre-modification (Georgii (1.31)). -/
theorem isPremodifier_chainDensity (hp : ∀ j, Measurable (Function.uncurry (p j))) :
    IsPremodifier (chainDensity p) where
  measurable := measurable_chainDensity hp
  comm_of_subset _ _ _ _ hΛ hζη := chainDensity_mul_comm_of_subset hΛ hζη

/-- The chain densities are Markovian: `g_{]i,k[}` depends only on `ω_i, …, ω_k`. -/
theorem isMarkovianInt_chainDensity (hp : ∀ j, Measurable (Function.uncurry (p j))) :
    IsMarkovianInt (chainDensity p) := by
  intro i k hik
  rw [show chainDensity p (Finset.Ioo i k)
      = fun ω ↦ ∏ j ∈ Finset.Ico i k, p (j + 1) (ω j) (ω (j + 1))
    from funext (chainDensity_Ioo_eq_prod_Ico hik)]
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  simp only [Finset.mem_Ico] at hj
  exact (hp (j + 1)).comp
    ((measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (show j ∈ Set.Icc i k by
        simp only [Set.mem_Icc]; omega)).prodMk
      (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (show j + 1 ∈ Set.Icc i k by
        simp only [Set.mem_Icc]; omega)))

/-- Positive and bounded transition densities are λ-admissible for a probability a priori
measure: `0 < λ_Λ g_Λ < ∞`. -/
theorem isPremodifierAdmissible_chainDensity (ν : Measure E) [IsProbabilityMeasure ν]
    (hp : ∀ j, Measurable (Function.uncurry (p j))) (hpos : ∀ j x y, 0 < p j x y) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hbd : ∀ j x y, p j x y ≤ C) :
    IsPremodifierAdmissible ν (chainDensity p) := by
  intro Λ η
  have := isMarkovKernel_isssdFun (ν := ν) (S := ℤ) Λ
  constructor
  · change (∫⁻ x, chainDensity p Λ x ∂(isssd ν Λ η)) ≠ 0
    rw [ne_eq, lintegral_eq_zero_iff (measurable_chainDensity hp Λ)]
    intro h
    have h' := h
    rw [Filter.EventuallyEq, ae_iff] at h'
    have huniv : {a | ¬ chainDensity p Λ a = (0 : (ℤ → E) → ℝ≥0∞) a} = Set.univ :=
      Set.eq_univ_of_forall fun a ↦ (chainDensity_pos hpos Λ a).ne'
    rw [huniv, measure_univ] at h'
    exact one_ne_zero h'
  · change (∫⁻ x, chainDensity p Λ x ∂(isssd ν Λ η)) ≠ ⊤
    refine ne_top_of_le_ne_top (b := C ^ (bondsOf Λ).card * (isssd ν Λ η) Set.univ) ?_ ?_
    · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hC) (measure_ne_top _ _)
    · rw [← lintegral_const]
      exact lintegral_mono fun σ ↦ Finset.prod_le_pow_card _ _ _ fun j _ ↦ hbd _ _ _

/-- **Georgii, Example (10.3)** (admissible case): the Markov specification `γ = ρλ` with
`ρ_{]i,k[} = g_{i,k} / Z_{i,k}` built from positive bounded transition densities. -/
noncomputable def chainSpecification (ν : Measure E) [IsProbabilityMeasure ν]
    (p : ℤ → E → E → ℝ≥0∞) (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) : Specification ℤ E :=
  premodification (isssd ν) (chainDensity p) (isResampling_isssd ν) (isPremodifier_chainDensity hp)
    hadm

lemma chainSpecification_apply (ν : Measure E) [IsProbabilityMeasure ν]
    (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) (Λ : Finset ℤ) (η : ℤ → E) :
    chainSpecification ν p hp hadm Λ η
      = (isssd ν Λ η).withDensity (premodifierNorm ν (chainDensity p) Λ) := rfl

/-- **Georgii, Example (10.3)**: the specification of a family of transition densities is a Markov
specification. -/
theorem isMarkovInt_chainSpecification (ν : Measure E) [IsProbabilityMeasure ν]
    (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) :
    IsMarkovInt (chainSpecification ν p hp hadm) :=
  isMarkovInt_of_forall_apply_eq _ ν (measurable_chainDensity hp) (isMarkovianInt_chainDensity hp)
    (chainSpecification_apply ν hp hadm)

end Specification

/-! ## Georgii, Example (10.11): Markov chains with transition densities are Gibbs measures -/

namespace MeasureTheory.GibbsMeasure.Markov

open Specification

variable {E : Type*} [MeasurableSpace E] {μ : Measure (ℤ → E)} {P : ℤ → Kernel E E}
  {B : ℤ → Set E} {ν : Measure E} [IsProbabilityMeasure ν] {p : ℤ → E → E → ℝ≥0∞}

/-! ### Integration against the independent kernels -/

/-- Integrating a function of the configurations which agree with `ω` off `Λ`. -/
lemma lintegral_isssd_congr_of_eqOn {Λ : Finset ℤ} (ω : ℤ → E) {F G : (ℤ → E) → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (h : ∀ σ, (∀ j ∉ Λ, σ j = ω j) → F σ = G σ) :
    ∫⁻ σ, F σ ∂(isssd ν Λ ω) = ∫⁻ σ, G σ ∂(isssd ν Λ ω) := by
  rw [lintegral_isssd_eq Λ ω hF, lintegral_isssd_eq Λ ω hG]
  exact lintegral_congr fun ξ ↦ h _ fun j hj ↦ juxt_apply_of_not_mem (by simpa using hj) ξ

/-- The resampling integral of a function depending only on `Λ ∪ Δ` depends on the boundary
condition only through `Δ`. -/
lemma lintegral_isssd_congr_of_dependsOn {Λ : Finset ℤ} {Δ : Set ℤ} {F : (ℤ → E) → ℝ≥0∞}
    (hF : Measurable F) (hdep : DependsOn F ((Λ : Set ℤ) ∪ Δ)) {ω ω' : ℤ → E}
    (h : ∀ i ∈ Δ, ω i = ω' i) :
    ∫⁻ σ, F σ ∂(isssd ν Λ ω) = ∫⁻ σ, F σ ∂(isssd ν Λ ω') := by
  rw [lintegral_isssd_eq Λ ω hF, lintegral_isssd_eq Λ ω' hF]
  refine lintegral_congr fun ξ ↦ hdep fun i hi ↦ ?_
  rcases hi with hi | hi
  · simp [juxt_apply_of_mem hi]
  · by_cases hiΛ : i ∈ (Λ : Set ℤ)
    · simp [juxt_apply_of_mem hiΛ]
    · simp [juxt_apply_of_not_mem hiΛ, h i hi]

/-- Resampling the empty volume does nothing. -/
lemma lintegral_isssd_empty (ω : ℤ → E) {F : (ℤ → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ σ, F σ ∂(isssd ν (∅ : Finset ℤ) ω) = F ω := by
  rw [lintegral_isssd_eq ∅ ω hF, Measure.pi_of_empty (fun _ : ((∅ : Finset ℤ) : Type) ↦ ν),
    lintegral_dirac' _ (f := fun ζ : ((∅ : Finset ℤ) : Type) → E ↦ F (juxt _ ω ζ))
      (hF.comp Measurable.juxt)]
  congr 1
  funext j
  exact juxt_apply_of_not_mem (by simp) _

/-- Resampling on `Λ ∪ {j}` is resampling the site `j` and then the volume `Λ`. -/
lemma lintegral_isssd_union_singleton (Λ : Finset ℤ) (j : ℤ) (ω : ℤ → E)
    {F : (ℤ → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ σ, F σ ∂(isssd ν (Λ ∪ {j}) ω)
      = ∫⁻ y, ∫⁻ σ, F σ ∂(isssd ν Λ (Function.update ω j y)) ∂ν := by
  classical
  have hcomp := isssd_comp_isssd (S := ℤ) (ν := ν) Λ {j}
  have h1 : isssd ν (Λ ∪ {j}) ω = (isssd ν {j} ω).bind (isssd ν Λ) := by
    have := DFunLike.congr_fun hcomp ω
    simp only [Kernel.comp_apply, Kernel.comap_apply, id_eq] at this
    rw [← this]
    congr 1
  have hmeas : Measurable fun ω' ↦ ∫⁻ σ, F σ ∂(isssd ν Λ ω') :=
    (Measurable.lintegral_kernel (κ := isssd ν Λ) hF).mono cylinderEvents_le_pi le_rfl
  rw [h1, Measure.lintegral_bind ((isssd ν Λ).measurable.mono cylinderEvents_le_pi
      le_rfl).aemeasurable
    hF.aemeasurable, Specification.isssd_singleton_eq_map, lintegral_map hmeas (measurable_update
        ω)]

/-! ### The joint law of two coordinates of a Markov chain -/

/-- The joint law of `(σ_i, σ_{i+n})` under a Markov chain restricted to a rectangle is the
composition-product of the law of `σ_i` with the chain kernel. -/
theorem IsMarkovChain.map_prodMk_eq_compProd [∀ k, IsMarkovKernel (P k)] (h : IsMarkovChain P μ)
    (hB : ∀ k, MeasurableSet (B k)) (i : ℤ) (n : ℕ) :
    (μ.restrict (rect (Finset.Icc i (i + n)) B)).map (fun σ ↦ (σ i, σ (i + n)))
      = ((μ.map fun σ ↦ σ i).restrict (B i)) ⊗ₘ chainKernel P hB n i := by
  classical
  have := h.isProbabilityMeasure
  have hmeas : Measurable fun σ : ℤ → E ↦ (σ i, σ (i + n)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply _)
  refine Measure.ext_prod fun {s} {t} hs ht ↦ ?_
  rw [Measure.map_apply hmeas (hs.prod ht), Measure.restrict_apply (hmeas (hs.prod ht)),
    Measure.compProd_apply_prod hs ht, Measure.restrict_restrict hs, Set.mk_preimage_prod]
  set B'' := Function.update B i (B i ∩ s) with hB''
  have hB''m : ∀ k, MeasurableSet (B'' k) := fun k ↦ by
    by_cases hk : k = i
    · subst hk; simp only [hB'', Function.update_self]; exact (hB _).inter hs
    · simp only [hB'', Function.update_of_ne hk]; exact hB k
  have hset : (fun σ : ℤ → E ↦ σ i) ⁻¹' s ∩ (fun σ ↦ σ (i + n)) ⁻¹' t ∩ rect (Finset.Icc i (i +
      n)) B
      = (fun σ ↦ σ (i + n)) ⁻¹' t ∩ (Set.univ ∩ rect (Finset.Icc i (i + n)) B'') := by
    rw [hB'', rect_update (by simp), rect_eq_erase_inter (B := B) (show i ∈ Finset.Icc i (i + n)
        by simp)]
    ext σ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, true_and]
    tauto
  rw [hset]
  have hM := h.map_restrict_inter_rect hB''m i (D := Set.univ) MeasurableSet.univ n
  have h1 := congrArg (fun ν : Measure E ↦ ν t) hM
  simp only [Measure.restrict_univ] at h1
  rw [Measure.map_apply (measurable_pi_apply _) ht, Measure.restrict_apply (measurable_pi_apply _
      ht),
    Measure.bind_apply ht (Kernel.aemeasurable _)] at h1
  rw [h1, show B'' i = s ∩ B i by rw [hB'', Function.update_self, Set.inter_comm]]
  refine setLIntegral_congr_fun (hs.inter (hB i)) fun x _ ↦ ?_
  rw [chainKernel_apply_eq_of_eq (P := P) hB''m hB n i
    (fun j hj hj' ↦ by rw [hB'', Function.update_of_ne (by omega)]) x]

/-! ### The chain kernel of kernels with densities -/

lemma measurable_prod_p (hp : ∀ j, Measurable (Function.uncurry (p j))) (s : Finset ℤ) :
    Measurable fun σ : ℤ → E ↦ ∏ j ∈ s, p j (σ (j - 1)) (σ j) := by
  refine Finset.measurable_prod _ fun j _ ↦ ?_
  exact Measurable.comp (hp j) (f := fun a : ℤ → E ↦ (a (j - 1), a j))
    ((measurable_pi_apply (j - 1)).prodMk (measurable_pi_apply j))

/-- Georgii's iterated integral (10.5) for the kernels `P_j(x, dy) = p_j(x, y) ν(dy)`: integrating
against the chain kernel started at `ω_k` is integrating against the independent resampling of
the sites `k + 1, …, k + n` with boundary condition `ω`, weighted by the transition densities. -/
theorem lintegral_chainKernel_eq_lintegral_isssd (hP : ∀ j x, P j x = ν.withDensity (p j x))
    (hp : ∀ j, Measurable (Function.uncurry (p j))) (hB : ∀ k, MeasurableSet (B k)) (n : ℕ) :
    ∀ (k : ℤ) (ω : ℤ → E) {F : E → ℝ≥0∞}, Measurable F →
      ∫⁻ y, F y ∂(chainKernel P hB n k (ω k))
        = ∫⁻ σ in rect (Finset.Ioc k (k + n)) B,
            F (σ (k + n)) * ∏ j ∈ Finset.Ioc k (k + n), p j (σ (j - 1)) (σ j)
              ∂(isssd ν (Finset.Ioc k (k + n)) ω) := by
  classical
  induction n with
  | zero =>
    intro k ω F hF
    have h0 : Finset.Ioc k (k + ((0 : ℕ) : ℤ)) = ∅ := by simp
    rw [h0, chainKernel_zero, Kernel.id_apply, lintegral_dirac' _ hF,
      show rect (∅ : Finset ℤ) B = Set.univ by ext; simp [rect], Measure.restrict_univ]
    simp only [Finset.prod_empty, mul_one, Nat.cast_zero, add_zero]
    rw [lintegral_isssd_empty ω (F := fun σ ↦ F (σ k)) (hF.comp (measurable_pi_apply k))]
  | succ n ih =>
    intro k ω F hF
    have hcast : k + ((n + 1 : ℕ) : ℤ) = k + 1 + n := by push_cast; ring
    have hIoc : Finset.Ioc k (k + (n + 1 : ℕ)) = Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1} := by
      ext j; simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_singleton]; omega
    have hk1 : k + 1 ∉ Finset.Ioc (k + 1) (k + 1 + n) := by simp
    have hpx : Measurable (p (k + 1) (ω k)) :=
      (hp (k + 1)).comp (measurable_const.prodMk measurable_id)
    have hG : Measurable fun y' ↦ ∫⁻ y, F y ∂(chainKernel P hB n (k + 1) y') :=
      Measurable.lintegral_kernel hF
    have hih : ∀ y', ∫⁻ y, F y ∂(chainKernel P hB n (k + 1) y')
        = ∫⁻ σ in rect (Finset.Ioc (k + 1) (k + 1 + n)) B,
            F (σ (k + 1 + n)) * ∏ j ∈ Finset.Ioc (k + 1) (k + 1 + n), p j (σ (j - 1)) (σ j)
              ∂(isssd ν (Finset.Ioc (k + 1) (k + 1 + n)) (Function.update ω (k + 1) y')) :=
      fun y' ↦ by simpa using ih (k + 1) (Function.update ω (k + 1) y') hF
    -- the integrand over the volume `]k+1, k+1+n]`
    set G : (ℤ → E) → ℝ≥0∞ := (rect (Finset.Ioc (k + 1) (k + 1 + n)) B).indicator fun σ ↦
      F (σ (k + 1 + n)) * ∏ j ∈ Finset.Ioc (k + 1) (k + 1 + n), p j (σ (j - 1)) (σ j) with hGdef
    have hGm : Measurable G :=
      ((hF.comp (measurable_pi_apply _)).mul (measurable_prod_p hp _)).indicator
        (measurableSet_rect hB)
    have hGint : Measurable fun y' ↦ ∫⁻ σ, G σ ∂(isssd ν (Finset.Ioc (k + 1) (k + 1 + n))
        (Function.update ω (k + 1) y')) :=
      ((Measurable.lintegral_kernel (κ := isssd ν _) hGm).mono cylinderEvents_le_pi le_rfl).comp
        (measurable_update ω)
    -- left-hand side: peel off the first step
    rw [chainKernel_succ, Kernel.lintegral_comp _ _ _ hF]
    simp_rw [Kernel.restrict_apply, hP]
    rw [setLIntegral_withDensity_eq_setLIntegral_mul _ hpx hG (hB (k + 1))]
    simp_rw [hih]
    -- right-hand side: split off the site `k + 1`
    rw [hIoc, hcast, ← lintegral_indicator (measurableSet_rect hB),
      lintegral_isssd_union_singleton _ _ ω
        (F := (rect (Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1}) B).indicator fun σ ↦
          F (σ (k + 1 + n)) * ∏ j ∈ Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1}, p j (σ (j - 1)) (σ j))
        (((hF.comp (measurable_pi_apply _)).mul (measurable_prod_p hp _)).indicator
          (measurableSet_rect hB)),
      ← lintegral_indicator (hB (k + 1))]
    refine lintegral_congr fun y' ↦ ?_
    rw [lintegral_isssd_congr_of_eqOn (Function.update ω (k + 1) y')
      (F := (rect (Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1}) B).indicator fun σ ↦
          F (σ (k + 1 + n)) * ∏ j ∈ Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1}, p j (σ (j - 1)) (σ j))
      (((hF.comp (measurable_pi_apply _)).mul (measurable_prod_p hp _)).indicator
        (measurableSet_rect hB))
      (G := fun σ ↦ (B (k + 1)).indicator (fun _ ↦ p (k + 1) (ω k) y') y' * G σ)
      (measurable_const.mul hGm) ?_, lintegral_const_mul _ hGm]
    · by_cases hy : y' ∈ B (k + 1)
      · simp only [Set.indicator_of_mem hy, Pi.mul_apply, hGdef,
          lintegral_indicator (measurableSet_rect hB)]
      · simp only [Set.indicator_of_notMem hy, zero_mul]
    · intro σ hσ
      have hσk : σ k = ω k := by
        rw [hσ k (by simp), Function.update_of_ne (by omega)]
      have hσk1 : σ (k + 1) = y' := by rw [hσ (k + 1) hk1, Function.update_self]
      have hmem : σ ∈ rect (Finset.Ioc (k + 1) (k + 1 + n) ∪ {k + 1}) B
          ↔ σ ∈ rect (Finset.Ioc (k + 1) (k + 1 + n)) B ∧ y' ∈ B (k + 1) := by
        simp only [mem_rect, Finset.mem_union, Finset.mem_singleton]
        constructor
        · intro h
          exact ⟨fun j hj ↦ h j (Or.inl hj), hσk1 ▸ h (k + 1) (Or.inr rfl)⟩
        · rintro ⟨h₁, h₂⟩ j hj
          rcases hj with hj | rfl
          · exact h₁ j hj
          · exact hσk1 ▸ h₂
      simp only [hGdef, Set.indicator]
      rw [Finset.prod_union (Finset.disjoint_singleton_right.2 hk1), Finset.prod_singleton,
        show k + 1 - 1 = k by ring, hσk, hσk1]
      simp only [hmem]
      by_cases h₁ : σ ∈ rect (Finset.Ioc (k + 1) (k + 1 + n)) B <;>
        by_cases h₂ : y' ∈ B (k + 1) <;> simp [h₁, h₂, mul_comm, mul_left_comm]


/-! ### The core identity of Example (10.11) -/

/-- The boundary configuration with value `x` everywhere except `y` at the site `i + n`. -/
def boundaryCfg (i : ℤ) (n : ℕ) (x y : E) : ℤ → E := Function.update (fun _ ↦ x) (i + n) y

omit [IsProbabilityMeasure ν] in
lemma measurable_boundaryCfg (i : ℤ) (n : ℕ) :
    Measurable fun z : E × E ↦ boundaryCfg i n z.1 z.2 := by
  refine measurable_pi_lambda _ fun j ↦ ?_
  by_cases hj : j = i + n
  · subst hj; simp only [boundaryCfg, Function.update_self]; exact measurable_snd
  · simp only [boundaryCfg, Function.update_of_ne hj]; exact measurable_fst

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma boundaryCfg_apply_self (i : ℤ) (n : ℕ) (x y : E) : boundaryCfg i n x y (i + n) = y := by
  simp [boundaryCfg]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma boundaryCfg_apply_of_ne (i : ℤ) (n : ℕ) (x y : E) {j : ℤ} (hj : j ≠ i + n) :
    boundaryCfg i n x y j = x := by
  simp [boundaryCfg, Function.update_of_ne hj]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma boundaryCfg_eq_update (i : ℤ) (n : ℕ) (x y : E) :
    boundaryCfg i n x y = Function.update (fun _ ↦ x) (i + n) y := rfl

variable (ν p) in
/-- Georgii's `Z_{i,k}` at the boundary values `x` (at `i`) and `y` (at `k = i + n`). -/
def Ztilde (i : ℤ) (n : ℕ) (x y : E) : ℝ≥0∞ :=
  ∫⁻ σ, chainDensity p (Finset.Ioo i (i + n)) σ ∂(isssd ν (Finset.Ioo i (i + n)) (boundaryCfg i n
      x y))

variable (ν p) in
/-- `∫_{σ_Λ ∈ B} g_{i,k} dλ_Λ` at the boundary values `x`, `y`. -/
def Gtilde (i : ℤ) (n : ℕ) (B : ℤ → Set E) (x y : E) : ℝ≥0∞ :=
  ∫⁻ σ in rect (Finset.Ioo i (i + n)) B, chainDensity p (Finset.Ioo i (i + n)) σ
    ∂(isssd ν (Finset.Ioo i (i + n)) (boundaryCfg i n x y))

lemma measurable_Ztilde (hp : ∀ j, Measurable (Function.uncurry (p j))) (i : ℤ) (n : ℕ) :
    Measurable fun z : E × E ↦ Ztilde ν p i n z.1 z.2 :=
  ((Measurable.lintegral_kernel (κ := isssd ν (Finset.Ioo i (i + n)))
    (measurable_chainDensity hp _)).mono cylinderEvents_le_pi le_rfl).comp
        (measurable_boundaryCfg i n)

lemma measurable_Gtilde (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hB : ∀ k, MeasurableSet (B k)) (i : ℤ) (n : ℕ) :
    Measurable fun z : E × E ↦ Gtilde ν p i n B z.1 z.2 := by
  simp only [Gtilde, ← lintegral_indicator (measurableSet_rect hB)]
  exact ((Measurable.lintegral_kernel (κ := isssd ν (Finset.Ioo i (i + n)))
    ((measurable_chainDensity hp _).indicator (measurableSet_rect hB))).mono cylinderEvents_le_pi
    le_rfl).comp (measurable_boundaryCfg i n)

omit [IsProbabilityMeasure ν] in
lemma Ioc_eq_Ioo_union (i : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    Finset.Ioc i (i + n) = Finset.Ioo i (i + n) ∪ {i + n} := by
  ext j; simp only [Finset.mem_Ioc, Finset.mem_Ioo, Finset.mem_union, Finset.mem_singleton]; omega

/-- The `n`-step transition kernel of the density kernels has density `Z̃(x, ·)`:
`(P_{i+1} ⋯ P_{i+n})(x, dy) = Z_{i,i+n}(x, y) ν(dy)`. -/
lemma chainKernel_univ_eq_withDensity_Ztilde (hP : ∀ j x, P j x = ν.withDensity (p j x))
    (hp : ∀ j, Measurable (Function.uncurry (p j))) (i : ℤ) (n : ℕ) (hn : 2 ≤ n) (x : E) :
    chainKernel P (B := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) n i x
      = ν.withDensity (Ztilde ν p i n x) := by
  ext S hS
  have h1 := lintegral_chainKernel_eq_lintegral_isssd hP hp (fun _ ↦ MeasurableSet.univ) n i
    (fun _ ↦ x) (F := S.indicator 1) (measurable_const.indicator hS)
  rw [lintegral_indicator_one hS] at h1
  have hFm : Measurable fun σ : ℤ → E ↦ S.indicator (1 : E → ℝ≥0∞) (σ (i + n))
      * ∏ j ∈ Finset.Ioo i (i + n) ∪ {i + n}, p j (σ (j - 1)) (σ j) :=
    ((measurable_const.indicator hS).comp (measurable_pi_apply _)).mul (measurable_prod_p hp _)
  rw [h1, withDensity_apply _ hS, show rect (Finset.Ioc i (i + n)) (fun _ ↦ (Set.univ : Set E))
      = Set.univ by ext; simp [rect], Measure.restrict_univ, Ioc_eq_Ioo_union i n (by omega),
    lintegral_isssd_union_singleton _ _ _ (F := fun σ : ℤ → E ↦ S.indicator (1 : E → ℝ≥0∞)
      (σ (i + n)) * ∏ j ∈ Finset.Ioo i (i + n) ∪ {i + n}, p j (σ (j - 1)) (σ j)) hFm,
    ← lintegral_indicator hS]
  refine lintegral_congr fun y ↦ ?_
  rw [lintegral_isssd_congr_of_eqOn _ (F := fun σ : ℤ → E ↦ S.indicator (1 : E → ℝ≥0∞)
      (σ (i + n)) * ∏ j ∈ Finset.Ioo i (i + n) ∪ {i + n}, p j (σ (j - 1)) (σ j)) hFm
    (G := fun σ ↦ S.indicator (1 : E → ℝ≥0∞) y * chainDensity p (Finset.Ioo i (i + n)) σ)
    (measurable_const.mul (measurable_chainDensity hp _)) ?_, lintegral_const_mul _
    (measurable_chainDensity hp _)]
  · by_cases hy : y ∈ S
    · simp [Set.indicator_of_mem hy, Ztilde, boundaryCfg]
    · simp [Set.indicator_of_notMem hy]
  · intro σ hσ
    rw [hσ (i + n) (by simp), Function.update_self, chainDensity_Ioo (by omega),
      ← Ioc_eq_Ioo_union i n (by omega)]

/-- The chain kernel with the sets `B` on `]i, i+n[` and `C` at `i + n`, evaluated on `univ`,
is `∫_C G̃(x, y) ν(dy)`. -/
lemma chainKernel_apply_univ_eq_lintegral_Gtilde (hP : ∀ j x, P j x = ν.withDensity (p j x))
    (hp : ∀ j, Measurable (Function.uncurry (p j))) (i : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hB : ∀ k, MeasurableSet (B k)) {C : Set E} (hC : MeasurableSet C) (x : E) :
    chainKernel P (B := Function.update B (i + n) C)
        (fun j ↦ by
          by_cases hj : j = i + n
          · subst hj; simp only [Function.update_self]; exact hC
          · simp only [Function.update_of_ne hj]; exact hB j) n i x Set.univ
      = ∫⁻ y in C, Gtilde ν p i n B x y ∂ν := by
  classical
  have hB'm : ∀ j, MeasurableSet (Function.update B (i + n) C j) := fun j ↦ by
    by_cases hj : j = i + n
    · subst hj; simp only [Function.update_self]; exact hC
    · simp only [Function.update_of_ne hj]; exact hB j
  have h1 := lintegral_chainKernel_eq_lintegral_isssd hP hp (B := Function.update B (i + n) C)
    hB'm n i (fun _ ↦ x) (F := fun _ ↦ 1) measurable_const
  simp only [lintegral_const, one_mul] at h1
  rw [h1, Ioc_eq_Ioo_union i n (by omega), ← lintegral_indicator (measurableSet_rect hB'm),
    lintegral_isssd_union_singleton _ _ _ (F := (rect (Finset.Ioo i (i + n) ∪ {i + n})
      (Function.update B (i + n) C)).indicator fun σ ↦
        ∏ j ∈ Finset.Ioo i (i + n) ∪ {i + n}, p j (σ (j - 1)) (σ j))
      ((measurable_prod_p hp _).indicator (measurableSet_rect hB'm)), ← lintegral_indicator hC]
  refine lintegral_congr fun y ↦ ?_
  have hmem : ∀ σ : ℤ → E, σ (i + n) = y →
      (σ ∈ rect (Finset.Ioo i (i + n) ∪ {i + n}) (Function.update B (i + n) C)
        ↔ σ ∈ rect (Finset.Ioo i (i + n)) B ∧ y ∈ C) := by
    intro σ hσ
    simp only [mem_rect, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro h
      refine ⟨fun j hj ↦ ?_, ?_⟩
      · have := h j (Or.inl hj)
        rwa [Function.update_of_ne (by simp only [Finset.mem_Ioo] at hj; omega)] at this
      · have := h (i + n) (Or.inr rfl)
        rwa [Function.update_self, hσ] at this
    · rintro ⟨h₁, h₂⟩ j hj
      rcases hj with hj | rfl
      · rw [Function.update_of_ne (by simp only [Finset.mem_Ioo] at hj; omega)]
        exact h₁ j hj
      · rw [Function.update_self, hσ]; exact h₂
  rw [lintegral_isssd_congr_of_eqOn _ (F := (rect (Finset.Ioo i (i + n) ∪ {i + n})
      (Function.update B (i + n) C)).indicator fun σ ↦
        ∏ j ∈ Finset.Ioo i (i + n) ∪ {i + n}, p j (σ (j - 1)) (σ j))
    ((measurable_prod_p hp _).indicator (measurableSet_rect hB'm))
    (G := fun σ ↦ C.indicator (fun _ ↦ 1) y
      * (rect (Finset.Ioo i (i + n)) B).indicator (chainDensity p (Finset.Ioo i (i + n))) σ)
    (measurable_const.mul ((measurable_chainDensity hp _).indicator (measurableSet_rect hB))) ?_,
    lintegral_const_mul _ ((measurable_chainDensity hp _).indicator (measurableSet_rect hB)),
    lintegral_indicator (measurableSet_rect hB)]
  · by_cases hy : y ∈ C
    · simp [Set.indicator_of_mem hy, Gtilde, boundaryCfg]
    · simp [Set.indicator_of_notMem hy]
  · intro σ hσ
    have hσy : σ (i + n) = y := by rw [hσ (i + n) (by simp), Function.update_self]
    simp only [Set.indicator_apply]
    rw [hmem σ hσy, ← Ioc_eq_Ioo_union i n (by omega),
      ← chainDensity_Ioo (show i + 1 < i + n by omega)]
    by_cases h₁ : σ ∈ rect (Finset.Ioo i (i + n)) B <;> by_cases h₂ : y ∈ C <;> simp [h₁, h₂]

/-- The normalised kernel of Example (10.3) on a rectangle, as a function of the two boundary
values. -/
lemma chainSpecification_apply_rect (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) (i : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hB : ∀ k, MeasurableSet (B k)) (ω : ℤ → E) :
    chainSpecification ν p hp hadm (Finset.Ioo i (i + n)) ω (rect (Finset.Ioo i (i + n)) B)
      = (Ztilde ν p i n (ω i) (ω (i + n)))⁻¹ * Gtilde ν p i n B (ω i) (ω (i + n)) := by
  rw [chainSpecification_apply, withDensity_premodifierNorm_apply ν (isPremodifier_chainDensity hp)
    (measurableSet_rect hB)]
  have hdep : DependsOn (chainDensity p (Finset.Ioo i (i + n)))
      ((Finset.Ioo i (i + n) : Set ℤ) ∪ {i, i + n}) :=
    (isMarkovianInt_chainDensity hp).dependsOn (by omega)
  have hbd : ∀ j ∈ ({i, i + n} : Set ℤ), ω j = boundaryCfg i n (ω i) (ω (i + n)) j := by
    intro j hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with rfl | rfl
    · rw [boundaryCfg_apply_of_ne _ _ _ _ (by omega)]
    · rw [boundaryCfg_apply_self]
  congr 1
  · congr 1
    exact lintegral_isssd_congr_of_dependsOn (measurable_chainDensity hp _) hdep hbd
  · rw [Gtilde, ← lintegral_indicator (measurableSet_rect hB),
      ← lintegral_indicator (measurableSet_rect hB)]
    refine lintegral_isssd_congr_of_dependsOn
      ((measurable_chainDensity hp _).indicator (measurableSet_rect hB)) (fun σ σ' h ↦ ?_) hbd
    have hmem : σ ∈ rect (Finset.Ioo i (i + n)) B ↔ σ' ∈ rect (Finset.Ioo i (i + n)) B :=
      mem_congr_of_measurableSet_cylinderEvents (measurableSet_cylinderEvents_rect subset_rfl hB)
        fun j hj ↦ h j (Or.inl hj)
    by_cases hσ : σ ∈ rect (Finset.Ioo i (i + n)) B
    · rw [Set.indicator_of_mem hσ, Set.indicator_of_mem (hmem.1 hσ), hdep h]
    · rw [Set.indicator_of_notMem hσ, Set.indicator_of_notMem fun h' ↦ hσ (hmem.2 h')]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma rect_update_of_notMem {W : Finset ℤ} {j : ℤ} (hj : j ∉ W) (S : Set E) :
    rect W (Function.update B j S) = rect W B := by
  ext σ
  simp only [mem_rect]
  exact ⟨fun h k hk ↦ by simpa [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)] using h k hk,
    fun h k hk ↦ by simpa [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)] using h k hk⟩

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma rect_Ioo_inter_eq (i : ℤ) (n : ℕ) (hn : 2 ≤ n) (B : ℤ → Set E) (A C : Set E) :
    rect (Finset.Ioo i (i + n)) B ∩ ((fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C)
      = rect (Finset.Icc i (i + n)) (Function.update (Function.update B i A) (i + n) C) := by
  classical
  rw [rect_update (by simp only [Finset.mem_Icc]; omega),
    rect_update (by simp only [Finset.mem_erase, Finset.mem_Icc]; omega),
    show ((Finset.Icc i (i + n)).erase (i + n)).erase i = Finset.Ioo i (i + n) by
      ext j; simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ioo]; omega]
  ext σ
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  tauto

/-- **The core identity of Example (10.11)**: for `A, C ∈ 𝓔` and a rectangle `B` over `]i,k[`,
`μ(σ_i ∈ A, σ_{]i,k[} ∈ B, σ_k ∈ C) = ∫_{σ_i ∈ A, σ_k ∈ C} γ_{]i,k[}(σ_{]i,k[} ∈ B | ·) dμ`. -/
theorem IsMarkovChain.measure_rect_inter_eq_lintegral_chainSpecification
    [∀ k, IsMarkovKernel (P k)] (hμ : IsMarkovChain P μ)
    (hP : ∀ j x, P j x = ν.withDensity (p j x)) (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) (i : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hB : ∀ k, MeasurableSet (B k)) {A C : Set E} (hA : MeasurableSet A) (hC : MeasurableSet C) :
    μ (rect (Finset.Ioo i (i + n)) B ∩ ((fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C))
      = ∫⁻ ω in (fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C,
          chainSpecification ν p hp hadm (Finset.Ioo i (i + n)) ω (rect (Finset.Ioo i (i + n)) B)
            ∂μ := by
  classical
  have := hμ.isProbabilityMeasure
  set B' := Function.update (Function.update B i A) (i + n) C with hB'
  have hB'm : ∀ j, MeasurableSet (B' j) := fun j ↦ by
    by_cases hj : j = i + n
    · subst hj; simp only [hB', Function.update_self]; exact hC
    · by_cases hj' : j = i
      · subst hj'; simp only [hB', Function.update_of_ne hj, Function.update_self]; exact hA
      · simp only [hB', Function.update_of_ne hj, Function.update_of_ne hj']; exact hB j
  have hB'i : B' i = A := by rw [hB', Function.update_of_ne (by omega), Function.update_self]
  -- the left-hand side through (10.5)
  have hLHS : μ (rect (Finset.Ioo i (i + n)) B ∩ ((fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C))
      = ∫⁻ x in A, ∫⁻ y in C, Gtilde ν p i n B x y ∂ν ∂(μ.map fun σ ↦ σ i) := by
    rw [rect_Ioo_inter_eq i n hn, hμ.measure_rect hB'm i n, hB'i]
    refine setLIntegral_congr_fun hA fun x _ ↦ ?_
    have := chainKernel_apply_univ_eq_lintegral_Gtilde (P := P) hP hp i n hn
      (B := Function.update B i A) (fun j ↦ by
        by_cases hj : j = i
        · subst hj; simp only [Function.update_self]; exact hA
        · simp only [Function.update_of_ne hj]; exact hB j) hC x
    have hG : ∀ y, Gtilde ν p i n (Function.update B i A) x y = Gtilde ν p i n B x y :=
      fun y ↦ by unfold Gtilde; rw [rect_update_of_notMem (by simp)]
    simp_rw [hG] at this
    rw [← this]
  -- the right-hand side through the joint law of `(σ_i, σ_{i+n})`
  set H : E × E → ℝ≥0∞ := fun z ↦ (Ztilde ν p i n z.1 z.2)⁻¹ * Gtilde ν p i n B z.1 z.2 with hH
  have hHm : Measurable H := (measurable_Ztilde hp i n).inv.mul (measurable_Gtilde hp hB i n)
  have hprodmk : Measurable fun σ : ℤ → E ↦ (σ i, σ (i + n)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply _)
  have hRHS : ∫⁻ ω in (fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C,
        chainSpecification ν p hp hadm (Finset.Ioo i (i + n)) ω (rect (Finset.Ioo i (i + n)) B) ∂μ
      = ∫⁻ x in A, ∫⁻ y in C, H (x, y)
          ∂(chainKernel P (B := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) n i x)
          ∂(μ.map fun σ ↦ σ i) := by
    have hjoint := hμ.map_prodMk_eq_compProd (B := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
      i n
    rw [show rect (Finset.Icc i (i + n)) (fun _ ↦ (Set.univ : Set E)) = Set.univ by
      ext; simp [rect], Measure.restrict_univ, Measure.restrict_univ] at hjoint
    calc ∫⁻ ω in (fun σ ↦ σ i) ⁻¹' A ∩ (fun σ ↦ σ (i + n)) ⁻¹' C,
          chainSpecification ν p hp hadm (Finset.Ioo i (i + n)) ω (rect (Finset.Ioo i (i + n)) B) ∂μ
        = ∫⁻ ω in (fun σ : ℤ → E ↦ (σ i, σ (i + n))) ⁻¹' (A ×ˢ C), H (ω i, ω (i + n)) ∂μ := by
          rw [Set.mk_preimage_prod]
          exact setLIntegral_congr_fun ((measurable_pi_apply i hA).inter
            (measurable_pi_apply _ hC)) fun ω _ ↦ chainSpecification_apply_rect hp hadm i n hn hB ω
      _ = ∫⁻ z in A ×ˢ C, H z ∂(μ.map fun σ ↦ (σ i, σ (i + n))) := by
          rw [Measure.restrict_map hprodmk (hA.prod hC), lintegral_map hHm hprodmk]
      _ = ∫⁻ z, (A ×ˢ C).indicator H z ∂((μ.map fun σ ↦ σ i) ⊗ₘ
            chainKernel P (B := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) n i) := by
          rw [hjoint, lintegral_indicator (hA.prod hC)]
      _ = ∫⁻ x, ∫⁻ y, (A ×ˢ C).indicator H (x, y)
            ∂(chainKernel P (B := fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ) n i x)
            ∂(μ.map fun σ ↦ σ i) :=
          Measure.lintegral_compProd (hHm.indicator (hA.prod hC))
      _ = _ := by
          rw [← lintegral_indicator hA]
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ A
          · rw [Set.indicator_of_mem hx, ← lintegral_indicator hC]
            refine lintegral_congr fun y ↦ ?_
            by_cases hy : y ∈ C
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mk_mem_prod hx hy)]
            · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem
                (fun h ↦ hy (Set.mem_prod.1 h).2)]
          · rw [Set.indicator_of_notMem hx]
            refine (lintegral_congr fun y ↦ ?_).trans lintegral_zero
            rw [Set.indicator_of_notMem (fun h ↦ hx (Set.mem_prod.1 h).1)]
  rw [hLHS, hRHS]
  refine setLIntegral_congr_fun hA fun x _ ↦ ?_
  rw [chainKernel_univ_eq_withDensity_Ztilde hP hp i n hn x,
    setLIntegral_withDensity_eq_setLIntegral_mul ν (f := Ztilde ν p i n x) (g := fun y ↦ H (x, y))
      (by exact (measurable_Ztilde hp i n).comp (measurable_const.prodMk measurable_id))
      (by exact hHm.comp (measurable_const.prodMk measurable_id)) hC]
  refine setLIntegral_congr_fun hC fun y _ ↦ ?_
  simp only [Pi.mul_apply, hH]
  have hZ := hadm (Finset.Ioo i (i + n)) (boundaryCfg i n x y)
  have hZ0 : Ztilde ν p i n x y ≠ 0 := hZ.1
  have hZtop : Ztilde ν p i n x y ≠ ⊤ := hZ.2
  rw [← mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, one_mul]

/-! ### Assembling Example (10.11) -/

lemma cylinderEvents_singleton_int (i : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) ({i} : Set ℤ)
      = MeasurableSpace.comap (fun σ : ℤ → E ↦ σ i) inferInstance := by
  simp [cylinderEvents]

lemma measurableSet_cylinderEvents_singleton_iff {i : ℤ} {D : Set (ℤ → E)} :
    MeasurableSet[cylinderEvents ({i} : Set ℤ)] D
      ↔ ∃ A : Set E, MeasurableSet A ∧ D = (fun σ ↦ σ i) ⁻¹' A := by
  rw [cylinderEvents_singleton_int, MeasurableSpace.measurableSet_comap]
  constructor
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩
  · rintro ⟨A, hA, rfl⟩; exact ⟨A, hA, rfl⟩

/-- The conditional probability of a rectangle over `]i,k[` given the exterior is the chain
specification: Georgii's computation in Example (10.11), combined with the Markov field property
of the chain (Remark (10.9)(3)). -/
theorem IsMarkovChain.condExp_rect_ae_eq [∀ k, IsMarkovKernel (P k)] (hμ : IsMarkovChain P μ)
    (hP : ∀ j x, P j x = ν.withDensity (p j x)) (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) (i : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hB : ∀ k, MeasurableSet (B k)) :
    μ[(rect (Finset.Ioo i (i + n)) B).indicator (1 : (ℤ → E) → ℝ) |
        cylinderEvents (Set.Ioo i (i + n))ᶜ]
      =ᵐ[μ] fun ω ↦ (chainSpecification ν p hp hadm (Finset.Ioo i (i + n)) ω
        (rect (Finset.Ioo i (i + n)) B)).toReal := by
  classical
  have := hμ.isProbabilityMeasure
  set Λ := Finset.Ioo i (i + n) with hΛ
  set γ := chainSpecification ν p hp hadm with hγ
  have hS₁m : MeasurableSet (rect Λ B) := measurableSet_rect hB
  have hΛcoe : (Λ : Set ℤ) = Set.Ioo i (i + n) := Finset.coe_Ioo _ _
  have hS₁Λ : MeasurableSet[cylinderEvents (Set.Ioo i (i + n))] (rect Λ B) := by
    rw [← hΛcoe]; exact measurableSet_cylinderEvents_rect subset_rfl hB
  have hgm : Measurable[cylinderEvents ({i, i + n} : Set ℤ)] fun ω ↦ γ Λ ω (rect Λ B) :=
    isMarkovInt_chainSpecification ν hp hadm i (i + n) (by omega) _ hS₁Λ
  have key : ∀ D, MeasurableSet[cylinderEvents ({i, i + n} : Set ℤ)] D →
      μ (rect Λ B ∩ D) = ∫⁻ ω in D, γ Λ ω (rect Λ B) ∂μ := by
    intro D hD
    have hgen : cylinderEvents (X := fun _ : ℤ ↦ E) ({i, i + n} : Set ℤ)
        = MeasurableSpace.generateFrom (interSets (cylinderEvents ({i} : Set ℤ))
          (cylinderEvents ({i + n} : Set ℤ))) := by
      rw [Set.insert_eq, cylinderEvents_union, sup_eq_generateFrom_interSets]
    have := ext_on_measurableSpace_of_generate_finite MeasurableSpace.pi (μ := μ.restrict (rect Λ
        B))
      (ν := μ.withDensity fun ω ↦ γ Λ ω (rect Λ B)) _ ?_ cylinderEvents_le_pi hgen
      (isPiSystem_interSets _ _) ?_ hD
    · rwa [Measure.restrict_apply' hS₁m, withDensity_apply _ (cylinderEvents_le_pi _ hD),
        Set.inter_comm] at this
    · rintro _ ⟨D₁, D₂, hD₁, hD₂, rfl⟩
      obtain ⟨A, hA, rfl⟩ := measurableSet_cylinderEvents_singleton_iff.1 hD₁
      obtain ⟨C, hC, rfl⟩ := measurableSet_cylinderEvents_singleton_iff.1 hD₂
      rw [Measure.restrict_apply' hS₁m, withDensity_apply _
        ((measurable_pi_apply i hA).inter (measurable_pi_apply _ hC)), Set.inter_comm]
      exact hμ.measure_rect_inter_eq_lintegral_chainSpecification hP hp hadm i n hn hB hA hC
    · rw [Measure.restrict_apply' hS₁m, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, Set.univ_inter]
      have := hμ.measure_rect_inter_eq_lintegral_chainSpecification hP hp hadm i n hn hB
        MeasurableSet.univ MeasurableSet.univ
      simpa using this
  have hg1 : (fun ω ↦ (γ Λ ω (rect Λ B)).toReal) =ᵐ[μ]
      μ[(rect Λ B).indicator (1 : (ℤ → E) → ℝ) | cylinderEvents ({i, i + n} : Set ℤ)] :=
    (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi hS₁m
      (measure_ne_top _ _) hgm.stronglyMeasurable.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ measure_ne_top _ _)).2 key
  exact (hμ.isMarkovField i (i + n) (by omega) _ hS₁Λ).trans hg1.symm

/-- The DLR equation of Example (10.11) on an interval `]i, i+n[`, `n ≥ 2`. -/
theorem IsMarkovChain.isCondExp_chainSpecification_Ioo [∀ k, IsMarkovKernel (P k)]
    (hμ : IsMarkovChain P μ) (hP : ∀ j x, P j x = ν.withDensity (p j x))
    (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) (i : ℤ) (n : ℕ) (hn : 2 ≤ n) :
    (chainSpecification ν p hp hadm (Finset.Ioo i (i + n))).IsCondExp μ := by
  classical
  have := hμ.isProbabilityMeasure
  set Λ := Finset.Ioo i (i + n) with hΛ
  set γ := chainSpecification ν p hp hadm with hγ
  have hΛcoe : (Λ : Set ℤ) = Set.Ioo i (i + n) := Finset.coe_Ioo _ _
  have haem : AEMeasurable (γ Λ) μ :=
    ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  have star : ∀ S₁, MeasurableSet[cylinderEvents (Λ : Set ℤ)] S₁ →
      ∀ t, MeasurableSet[cylinderEvents (Λ : Set ℤ)ᶜ] t →
        μ (S₁ ∩ t) = ∫⁻ ω in t, γ Λ ω S₁ ∂μ := by
    intro S₁ hS₁ t ht
    have ht' : MeasurableSet t := cylinderEvents_le_pi _ ht
    have hgen : cylinderEvents (X := fun _ : ℤ ↦ E) (Λ : Set ℤ)
        = MeasurableSpace.generateFrom (rectangles E fun _ ↦ Λ) :=
      cylinderEvents_eq_generateFrom_rectangles (fun _ ↦ subset_rfl) fun k hk ↦ ⟨0, hk⟩
    have := ext_on_measurableSpace_of_generate_finite MeasurableSpace.pi (μ := μ.restrict t)
      (ν := (μ.restrict t).bind (γ Λ)) _ ?_ cylinderEvents_le_pi hgen
      (isPiSystem_rectangles monotone_const) ?_ hS₁
    · rwa [Measure.restrict_apply' ht', Measure.bind_apply (cylinderEvents_le_pi _ hS₁)
        haem.restrict]
        at this
    · rintro _ ⟨_, B, hB, rfl⟩
      rw [Measure.restrict_apply' ht', Measure.bind_apply (measurableSet_rect hB) haem.restrict]
      have h1 := hμ.condExp_rect_ae_eq hP hp hadm i n hn hB
      rw [← hΛcoe] at h1
      have hgm : Measurable[cylinderEvents (Λ : Set ℤ)ᶜ] fun ω ↦ γ Λ ω (rect Λ B) :=
        (γ Λ).measurable_coe (measurableSet_rect hB)
      exact (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi
        (measurableSet_rect hB) (measure_ne_top _ _) hgm.stronglyMeasurable.aestronglyMeasurable
        (ae_of_all _ fun _ ↦ measure_ne_top _ _)).1 h1.symm t ht
    · rw [Measure.restrict_apply' ht', Measure.bind_apply MeasurableSet.univ haem.restrict,
        Set.univ_inter]
      simp
  refine ⟨fun S hS ↦ ?_⟩
  have hgm : Measurable[cylinderEvents (Λ : Set ℤ)ᶜ] fun ω ↦ γ Λ ω S := (γ Λ).measurable_coe hS
  refine ((toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq cylinderEvents_le_pi hS
    (measure_ne_top _ _) hgm.stronglyMeasurable.aestronglyMeasurable
    (ae_of_all _ fun _ ↦ measure_ne_top _ _)).2 fun t ht ↦ ?_).symm
  have ht' : MeasurableSet t := cylinderEvents_le_pi _ ht
  have hgen : (MeasurableSpace.pi : MeasurableSpace (ℤ → E))
      = MeasurableSpace.generateFrom (interSets (cylinderEvents (Λ : Set ℤ))
        (cylinderEvents (Λ : Set ℤ)ᶜ)) := by
    rw [← sup_eq_generateFrom_interSets, ← cylinderEvents_union, Set.union_compl_self,
      cylinderEvents_univ]
  have := ext_on_measurableSpace_of_generate_finite MeasurableSpace.pi (μ := μ.restrict t)
    (ν := (μ.restrict t).bind (γ Λ)) _ ?_ le_rfl hgen (isPiSystem_interSets _ _) ?_ hS
  · rwa [Measure.restrict_apply' ht', Measure.bind_apply hS haem.restrict] at this
  · rintro _ ⟨S₁, S₂, hS₁, hS₂, rfl⟩
    have hS₁' : MeasurableSet S₁ := cylinderEvents_le_pi _ hS₁
    have hS₂' : MeasurableSet S₂ := cylinderEvents_le_pi _ hS₂
    rw [Measure.restrict_apply' ht', Measure.bind_apply (hS₁'.inter hS₂') haem.restrict]
    simp_rw [γ.isProper.inter_eq_indicator_mul Λ hS₁' hS₂]
    have hind : ∀ ω, S₂.indicator (1 : (ℤ → E) → ℝ≥0∞) ω * γ Λ ω S₁
        = S₂.indicator (fun ω ↦ γ Λ ω S₁) ω := fun ω ↦ by
      by_cases h : ω ∈ S₂ <;> simp [h]
    simp_rw [hind]
    rw [lintegral_indicator hS₂', Measure.restrict_restrict hS₂',
      ← star S₁ hS₁ (S₂ ∩ t) (hS₂.inter ht)]
    congr 1
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  · rw [Measure.restrict_apply' ht', Measure.bind_apply MeasurableSet.univ haem.restrict,
      Set.univ_inter]
    simp

/-- **Georgii, Example (10.11).** A Markov chain whose transition kernels have densities
`P_i(x, dy) = p_i(x, y) λ(dy)` with `p_i` as in Example (10.3) is a Gibbs measure for the Markov
specification `γ = ρλ` of that example: `μ ∈ 𝒢(γ)`. -/
theorem IsMarkovChain.isGibbsMeasure_chainSpecification [∀ k, IsMarkovKernel (P k)]
    (hμ : IsMarkovChain P μ) (hP : ∀ j x, P j x = ν.withDensity (p j x))
    (hp : ∀ j, Measurable (Function.uncurry (p j)))
    (hadm : IsPremodifierAdmissible ν (chainDensity p)) :
    (chainSpecification ν p hp hadm).IsGibbsMeasure μ := by
  have := hμ.isProbabilityMeasure
  rw [isGibbsMeasure_iff_frequently_bind_eq_of_prob, Filter.frequently_atTop]
  intro Λ₀
  have hb := boundOf_nonneg Λ₀
  have hnat := Int.toNat_of_nonneg (show 0 ≤ 2 * boundOf Λ₀ + 2 by omega)
  refine ⟨Finset.Ioo (-boundOf Λ₀ - 1) (-boundOf Λ₀ - 1 + ((2 * boundOf Λ₀ + 2).toNat : ℕ)),
    fun j hj ↦ ?_, ?_⟩
  · have := subset_Icc_boundOf Λ₀ hj
    simp only [Finset.mem_Icc] at this
    simp only [Finset.mem_Ioo]
    omega
  · exact (Kernel.isCondExp_iff_bind_eq_left ((chainSpecification ν p hp hadm).isProper _)
      cylinderEvents_le_pi).1 (hμ.isCondExp_chainSpecification_Ioo hP hp hadm _ _ (by omega))

end MeasureTheory.GibbsMeasure.Markov

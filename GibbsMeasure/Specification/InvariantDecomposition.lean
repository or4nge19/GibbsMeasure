/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.Pointwise
public import GibbsMeasure.Mathlib.Probability.Kernel.StieltjesPoint
public import GibbsMeasure.Specification.PAKernel
public import GibbsMeasure.Specification.ExtremeCorollaries
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.InvariantFields

/-!
# The ergodic decomposition (Georgii §14.1–14.2)

Georgii's Theorem (14.10) represents every `Θ`-invariant random field `μ ∈ 𝓟_Θ` as a mixture of
ergodic ones, `μ = ∫_{ex 𝓟_Θ} ν w_μ(dν)`, through a `(𝓟_Θ, 𝓘)`-kernel in the sense of Definition
(7.21), and Theorem (14.17) shows that for `μ ∈ 𝒢_Θ(γ)` the mixture lives on `ex 𝒢_Θ(γ)`. This
file proves (14.10), (14.11), (14.17), (14.18) and (14.25).

## The `(𝓟_G, 𝓘)`-kernel (Theorem (14.10), first assertion)

For a countable abelian group `G` acting measurably on a standard Borel space `Ω`, with an
increasing regular Følner sequence `F : ℕ → Finset G` (the cubes of `ℤ^d`), `ergodicKernel`
is Georgii's kernel: on the invariant set `Ω₀` (`ergodicConvergenceSet`) where the ergodic
averages of the indicators of the half-lines `{e ≤ q}`, `q : ℚ`, of the Borel embedding
`e = embeddingReal Ω` converge, the limits form a rational CDF (`ergodicRatCDF`), turned into a
probability measure on `Ω` by `kernelOfMeasurableRat` and `Kernel.comapRight`; off the invariant
set where this measure is invariant it is replaced by a fixed invariant `ν₀`. The
multidimensional ergodic theorem (14.A8), `ae_forall_tendsto_inv_card_smul_sum_vadd_condExp`,
identifies the result `μ`-a.s. with `condExpKernel μ 𝓘` for every invariant `μ`
(`ae_ergodicKernel_eq_condExpKernel`), and `condExp_comp_vadd_smulInvariants`
(`μ(θ_i A | 𝓘) = μ(A | 𝓘)`) shows that these conditional distributions are a.s. invariant.
`isPAKernel_ergodicKernel` is the `(𝓟_G, 𝓘)`-kernel, `exists_isPAKernel_of_vaddInvariant` its
existence. `IsPAKernel.ae_eq_condExpKernel` records that *any* `(P, 𝒜)`-kernel is a.s.
`condExpKernel μ 𝒜`.

## The decomposition governed by a `(P, 𝒜)`-kernel (Theorem (7.26) and its corollaries)

Proposition (7.22) (`IsPAKernel.exists_unique_representing_weight`) gives the unique
representing weight `weight π μ` of `μ ∈ P` for any `(P, 𝒜)`-kernel `π`. The statements of
Theorem (7.26) — `w_μ` is carried by `ex P`, `μ ↦ w_μ` is an affine bijection onto the probability
weights on `ex P`, `w_μ(ν(A) ≤ c) = μ(μ(A | 𝒜) ≤ c)` — and of Corollaries (7.28), (7.29) and
(7.30) use nothing about `P` beyond `ex P = P ∩ P_𝒜` and measurability of `P`; they are proved
once, in the namespace `IsPAKernel` of `GibbsMeasure/Specification/PAKernel.lean`, and
instantiated here at `P = 𝓟_Θ` (Theorem (14.10)) and `P = 𝒢_Θ(γ)` (Theorem (14.17), Corollaries
(14.18), (14.25)), exactly as the Chapter 7 statements in `ExtremeDecomposition.lean` and
`ExtremeCorollaries.lean` are the instance `P = 𝒢(γ)`, `𝒜 = 𝓣`.

## Configuration space

The shift group `Θ = shiftGroup S E` of an abelian site group `S` acts on `S → E`; the bridge to
the additive action of `S` is the *local* instance `shiftAddAction` (`j +ᵥ ω = θ_j ω`), under
which the invariant σ-algebra of `S` is `invariantEvents Θ` and the invariant probability
measures are `invariantFields Θ`. Then:

* `exists_isPAKernel_invariantFields_shiftGroup`, `exists_isPAKernel_invariantFields_shiftGroup_int`
  — **Theorem (14.10), existence of the `(𝓟_Θ, 𝓘)`-kernel**, along a regular Følner sequence of
  volumes and along the cubes of `ℤ^d`;
* `ergodicDecomposition_invariantFields` — **Theorem (14.10)**, the affine bijection `μ ↦ w_μ`
  and the level-set formula, for any countable subgroup `Θ ≤ T` with a `(𝓟_Θ, 𝓘)`-kernel;
* `weight_map_of_mem_normalizer` — **Corollary (14.11)**: `w_{τ(μ)} = τ(w_μ)` for `τ` in the
  normaliser of `Θ` (Georgii's `τ ∘ Θ = Θ ∘ τ`, (5.14));
* `ae_mem_invariantG_of_isPAKernel_invariantFields`, `weight_extremePoints_invariantG_compl`,
  `ergodicDecomposition_invariantG` — **Theorem (14.17)**: any `(𝓟_Θ, 𝓘)`-kernel takes its
  values in `𝒢_Θ(γ)` a.s. (the computation `π'γ_Λ(A) = μ(γ_Λ(A|·)|𝓘) = μ(μ(A|𝓕_{Λᶜ})|𝓘) =
  μ(A|𝓘) = π'(A)`, with Proposition (14.9) in the form
  `condExp_condExp_cylinderEvents_compl_invariantEvents`), so `w_μ` is supported on `ex 𝒢_Θ(γ)`
  and `μ ∈ 𝒢_Θ(γ)` has a unique extreme decomposition within `𝒢_Θ(γ)`;
* `le_encard_extremePoints_invariantG_iff` — **Corollary (14.18)**: `|ex 𝒢_Θ(γ)| ≥ N` iff
  `𝒢_Θ(γ)` contains `N` linearly independent elements;
* `setOf_mem_invariantG_eq_closure_convexCombos` — **Corollary (14.25)**, conditional form: for
  quasilocal `γ`, `𝒢_Θ(γ)` is the closed convex hull (in the topology of local convergence) of any
  `L ⊆ 𝒢_Θ(γ)` containing `ex 𝒢_Θ(γ)`. Georgii's `L` is the set `𝒢_{Θ,lim}(γ)` of averaged
  limiting Gibbs measures, and `ex 𝒢_Θ(γ) ⊆ 𝒢_{Θ,lim}(γ) ⊆ 𝒢_Θ(γ)` is the content of Theorem
  (14.20)(c) together with the argument of Example (5.20)(1); those two inclusions are exactly
  what this file consumes from (14.20).
* The `_shiftGroup` versions instantiate (14.17), (14.18), (14.25) at the shift group of an
  infinite countable abelian site group with a regular Følner sequence.

## Hypotheses

`E` standard Borel (so `S → E` is, for countable `S`): the Borel embedding `embeddingReal`
builds the kernel, `condExpKernel` identifies it, and the countable π-system `piNatGen` makes
`𝓟_Θ`, `𝒢(γ)` and `ex P` measurable in `Measure (S → E)`. `Countable Θ` is Remark (14.3)(2), for
(14.5)(a) `ex 𝓟_Θ = 𝓟_Θ ∩ P_𝓘`. The hypothesis that `Θ` moves every finite volume off itself
(automatic for the shift group of an infinite site group) is Proposition (14.9), used in (14.17)
and its corollaries. Georgii's remark that (14.10) holds for any finitely generated abelian
subgroup of `T` is the general-`G` form `isPAKernel_ergodicKernel`: what is used is a countable
abelian group acting measurably, with a regular Følner sequence.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal Topology Pointwise symmDiff

namespace MeasureTheory.GibbsMeasure

/-! ### The invariant σ-algebra and the invariant probability measures of an additive action -/

section Additive

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω]

/-- The invariant σ-algebra `𝓘` of an additive action, `MeasurableSpace.smulInvariants
(Multiplicative G) Ω`. -/
local notation "𝓘" => MeasurableSpace.smulInvariants (Multiplicative G) Ω

lemma vaddInvariantMeasure_iff_smulInvariantMeasure_multiplicative {μ : Measure Ω} :
    VAddInvariantMeasure G Ω μ ↔ SMulInvariantMeasure (Multiplicative G) Ω μ :=
  ⟨fun h ↦ ⟨fun c _ hs ↦ h.measure_preimage_vadd (Multiplicative.toAdd c) hs⟩,
    fun h ↦ ⟨fun c _ hs ↦ h.measure_preimage_smul (Multiplicative.ofAdd c) hs⟩⟩

/-- A measurable set is strictly invariant iff it is fixed by every `(g +ᵥ ·)`. -/
lemma measurableSet_smulInvariants_multiplicative_iff {A : Set Ω} :
    MeasurableSet[𝓘] A ↔ MeasurableSet A ∧ ∀ g : G, (g +ᵥ ·) ⁻¹' A = A :=
  ⟨fun h ↦ ⟨h.1, fun g ↦ h.2 (Multiplicative.ofAdd g)⟩,
    fun h ↦ ⟨h.1, fun c ↦ h.2 (Multiplicative.toAdd c)⟩⟩

variable [MeasurableConstVAdd G Ω]

/-- The conditional expectation on the invariant σ-algebra does not see a translation of the
integrand: for an invariant finite measure, `μ[f ∘ (g +ᵥ ·) | 𝓘] = μ[f | 𝓘]` a.e. (Georgii, proof
of (14.10): "the obvious fact that `μ(θ_i A | 𝓘) = μ(A | 𝓘)`"). -/
lemma condExp_comp_vadd_smulInvariants {μ : Measure Ω} [IsFiniteMeasure μ]
    [VAddInvariantMeasure G Ω μ] {f : Ω → ℝ} (hf : Integrable f μ) (g : G) :
    μ[fun ω ↦ f (g +ᵥ ω) | 𝓘] =ᵐ[μ] μ[f | 𝓘] := by
  have hle : 𝓘 ≤ ‹MeasurableSpace Ω› := MeasurableSpace.smulInvariants_le
  have hmp : MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ := measurePreserving_vadd g μ
  have hf' : Integrable (fun ω ↦ f (g +ᵥ ω)) μ := (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  refine (ae_eq_condExp_of_forall_setIntegral_eq hle hf'
    (fun s _ _ ↦ integrable_condExp.integrableOn)
    (fun s hs _ ↦ ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  rw [setIntegral_condExp hle hf hs]
  have hsg : (g +ᵥ · : Ω → Ω) ⁻¹' s = s := hs.2 (Multiplicative.ofAdd g)
  calc ∫ x in s, f x ∂μ = ∫ x in (g +ᵥ · : Ω → Ω) ⁻¹' s, f (g +ᵥ x) ∂μ :=
        (hmp.setIntegral_preimage_emb (MeasurableEquiv.vadd g).measurableEmbedding f s).symm
    _ = ∫ x in s, f (g +ᵥ x) ∂μ := by rw [hsg]

/-- The conditional probability of a translated event given `𝓘` is that of the event. -/
lemma condExp_indicator_preimage_vadd_smulInvariants {μ : Measure Ω} [IsFiniteMeasure μ]
    [VAddInvariantMeasure G Ω μ] {A : Set Ω} (hA : MeasurableSet A) (g : G) :
    μ[((g +ᵥ · : Ω → Ω) ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) | 𝓘] =ᵐ[μ]
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝓘] :=
  condExp_comp_vadd_smulInvariants ((integrable_const (1 : ℝ)).indicator hA) g

end Additive

/-! ### A countable core for invariant probability measures -/

section Core

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω]
  [MeasurableSpace.CountablyGenerated Ω] [MeasurableConstVAdd G Ω]

variable (G) in
/-- A *countable* core formulation of "invariant probability measure": mass one, and invariance
under each `g ∈ G` on the countable π-system `piNatGen`. This cuts out a measurable subset of
`Measure Ω` (Georgii, proof of (14.10): `{π' ∈ 𝓟_Θ} = ⋂_{A ∈ 𝒞, i} {π'(θ_i A) = π'(A)}`). -/
def IsVAddInvariantCore (ν : Measure Ω) : Prop :=
  ν univ = 1 ∧ ∀ (g : G) (t : Finset ℕ), ν ((g +ᵥ ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)

lemma isVAddInvariantCore_iff {ν : Measure Ω} :
    IsVAddInvariantCore G ν ↔ IsProbabilityMeasure ν ∧ VAddInvariantMeasure G Ω ν := by
  constructor
  · rintro ⟨h1, h⟩
    have hprob : IsProbabilityMeasure ν := ⟨h1⟩
    refine ⟨hprob, ⟨fun g s hs ↦ ?_⟩⟩
    have hmap : ν.map (g +ᵥ ·) = ν := by
      have : IsProbabilityMeasure (ν.map (g +ᵥ · : Ω → Ω)) :=
        Measure.isProbabilityMeasure_map (measurable_const_vadd g).aemeasurable
      refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
        generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
      rintro s ⟨t, rfl⟩
      rw [Measure.map_apply (measurable_const_vadd g) (measurableSet_piNatGen t)]
      exact h g t
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply (measurable_const_vadd g) hs]
  · rintro ⟨hprob, hinv⟩
    exact ⟨measure_univ, fun g t ↦ hinv.measure_preimage_vadd g (measurableSet_piNatGen t)⟩

variable (G Ω) in
lemma measurableSet_isVAddInvariantCore [Countable G] :
    MeasurableSet {ν : Measure Ω | IsVAddInvariantCore G ν} := by
  have h_univ : MeasurableSet {ν : Measure Ω | ν univ = (1 : ℝ≥0∞)} :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage (Measure.measurable_coe MeasurableSet.univ)
  have hEq (g : G) (t : Finset ℕ) : MeasurableSet {ν : Measure Ω |
      ν ((g +ᵥ ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)} :=
    measurableSet_eq_fun
      (Measure.measurable_coe ((measurableSet_piNatGen t).preimage (measurable_const_vadd g)))
      (Measure.measurable_coe (measurableSet_piNatGen t))
  have hAll : MeasurableSet {ν : Measure Ω | ∀ (g : G) (t : Finset ℕ),
      ν ((g +ᵥ ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)} := by
    simpa [Set.ofPred_forall] using
      MeasurableSet.iInter fun g ↦ MeasurableSet.iInter fun t ↦ hEq g t
  simpa [IsVAddInvariantCore, Set.ofPred_and, Set.ofPred_forall] using h_univ.inter hAll

/-- The invariant probability measures of a countable group action form a measurable subset of
`Measure Ω` (for the evaluation σ-algebra). -/
lemma measurableSet_setOf_isProbabilityMeasure_and_vaddInvariantMeasure [Countable G] :
    MeasurableSet {ν : Measure Ω | IsProbabilityMeasure ν ∧ VAddInvariantMeasure G Ω ν} := by
  have : {ν : Measure Ω | IsProbabilityMeasure ν ∧ VAddInvariantMeasure G Ω ν} =
      {ν : Measure Ω | IsVAddInvariantCore G ν} := Set.ext fun _ ↦ isVAddInvariantCore_iff.symm
  rw [this]
  exact measurableSet_isVAddInvariantCore G Ω

end Core

/-! ### The `(𝓟_G, 𝓘)`-kernel of an action along a regular Følner sequence

Georgii's construction in the proof of (14.10): the countable core `𝒞` of `𝓕` is replaced by the
half-lines `{e ≤ q}`, `q : ℚ`, of the Borel embedding `e = embeddingReal Ω`; `Ω₀` is the
invariant set on which the ergodic averages of their indicators converge; on `Ω₀` the limits form a
rational CDF, hence (via `kernelOfMeasurableRat` and `Kernel.comapRight`) a probability measure on
`Ω`; the multidimensional ergodic theorem (14.A8) shows that for every invariant `μ` this measure
is `μ`-a.s. the conditional distribution `μ(· | 𝓘)`; the bad invariant set is sent to a fixed
invariant probability measure `ν₀`. -/

section ErgodicKernel

variable {G : Type*} (Ω : Type*) [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω]
  [MeasurableConstVAdd G Ω] [StandardBorelSpace Ω] (F : ℕ → Finset G)

/-- The invariant σ-algebra `𝓘` of the action. -/
local notation "𝓘" => MeasurableSpace.smulInvariants (Multiplicative G) Ω

/-- Georgii's `Ω₀`: the points at which the ergodic averages of the indicators of all the
half-lines `{e ≤ q}`, `q : ℚ`, converge. -/
def ergodicConvergenceSet : Set Ω :=
  ⋂ q : ℚ, {ω | ∃ c : ℝ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n,
    (embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (i +ᵥ ω)) atTop (𝓝 c)}

omit [MeasurableConstVAdd G Ω] in
lemma mem_ergodicConvergenceSet {ω : Ω} :
    ω ∈ ergodicConvergenceSet Ω F ↔ ∀ q : ℚ, ∃ c : ℝ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ •
      ∑ i ∈ F n, (embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (i +ᵥ ω)) atTop
        (𝓝 c) :=
  Set.mem_iInter

omit [StandardBorelSpace Ω] in
lemma measurable_inv_card_smul_sum_vadd {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable fun ω : Ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) := by
  fun_prop

lemma measurableSet_ergodicConvergenceSet : MeasurableSet (ergodicConvergenceSet Ω F) :=
  MeasurableSet.iInter fun _ ↦ measurableSet_exists_tendsto fun n ↦
    measurable_inv_card_smul_sum_vadd Ω F (measurable_const.indicator
      (measurableSet_Iic.preimage (measurable_embeddingReal Ω))) n

variable {Ω F}

omit [MeasurableSpace Ω] [MeasurableConstVAdd G Ω] [StandardBorelSpace Ω] in
/-- Along a Følner sequence, the ergodic averages of a bounded function at `ω` and at `g +ᵥ ω`
have the same limits. -/
lemma tendsto_inv_card_smul_sum_vadd_vadd_iff [DecidableEq G]
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    {f : Ω → ℝ} {M : ℝ} (hM : ∀ ω, |f ω| ≤ M) (g : G) (ω : Ω) {c : ℝ} :
    Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ (g +ᵥ ω))) atTop (𝓝 c) ↔
      Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop (𝓝 c) := by
  have hdiff := tendsto_inv_card_smul_sum_vadd_sub_vadd hFol hM g ω
  have hcomm : ∀ i : G, i +ᵥ (g +ᵥ ω) = g +ᵥ (i +ᵥ ω) := fun i ↦ vadd_comm i g ω
  simp only [hcomm]
  simp only [smul_sub, Finset.sum_sub_distrib] at hdiff
  constructor
  · intro h
    simpa using h.sub hdiff
  · intro h
    simpa using h.add hdiff

omit [MeasurableConstVAdd G Ω] in
/-- Georgii's `Ω₀` is invariant: `Ω₀ ∈ 𝓘`. -/
lemma vadd_mem_ergodicConvergenceSet [DecidableEq G]
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    {ω : Ω} (hω : ω ∈ ergodicConvergenceSet Ω F) (g : G) : g +ᵥ ω ∈ ergodicConvergenceSet Ω F := by
  rw [mem_ergodicConvergenceSet] at hω ⊢
  intro q
  obtain ⟨c, hc⟩ := hω q
  refine ⟨c, (tendsto_inv_card_smul_sum_vadd_vadd_iff hFol (M := 1) (fun ω ↦ ?_) g ω).2 hc⟩
  by_cases h : ω ∈ embeddingReal Ω ⁻¹' Iic (q : ℝ) <;> simp [h]

lemma measurableSet_smulInvariants_ergodicConvergenceSet [DecidableEq G]
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0)) :
    MeasurableSet[𝓘] (ergodicConvergenceSet Ω F) := by
  refine ⟨measurableSet_ergodicConvergenceSet Ω F, fun c ↦ Set.ext fun ω ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · have := vadd_mem_ergodicConvergenceSet hFol h (-Multiplicative.toAdd c)
    rwa [show (-Multiplicative.toAdd c) +ᵥ (c • ω) = ω from
      neg_vadd_vadd (Multiplicative.toAdd c) ω] at this
  · exact vadd_mem_ergodicConvergenceSet hFol h (Multiplicative.toAdd c)

variable (Ω F) in
/-- The rational ergodic CDF `ω ↦ (q ↦ lim_n |F n|⁻¹ ∑_{i ∈ F n} 1_{e ≤ q} (i +ᵥ ω))` on `Ω₀`,
and `0` off `Ω₀`. -/
noncomputable def ergodicRatCDF (ω : Ω) : ℚ → ℝ :=
  (ergodicConvergenceSet Ω F).indicator (fun ω q ↦ limUnder atTop fun n ↦ ((F n).card : ℝ)⁻¹ •
    ∑ i ∈ F n, (embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (i +ᵥ ω)) ω

omit [MeasurableConstVAdd G Ω] in
lemma ergodicRatCDF_of_mem {ω : Ω} (hω : ω ∈ ergodicConvergenceSet Ω F) (q : ℚ) :
    ergodicRatCDF Ω F ω q = limUnder atTop fun n ↦ ((F n).card : ℝ)⁻¹ •
      ∑ i ∈ F n, (embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (i +ᵥ ω) := by
  simp [ergodicRatCDF, hω]

lemma measurable_ergodicRatCDF' : Measurable (ergodicRatCDF Ω F) := by
  refine Measurable.indicator ?_ (measurableSet_ergodicConvergenceSet Ω F)
  refine measurable_pi_iff.2 fun q ↦ ?_
  exact (StronglyMeasurable.limUnder fun n ↦ Measurable.stronglyMeasurable
    (measurable_inv_card_smul_sum_vadd Ω F (measurable_const.indicator
      (measurableSet_Iic.preimage (measurable_embeddingReal Ω))) n)).measurable

omit [MeasurableConstVAdd G Ω] in
/-- The rational ergodic CDF is invariant, hence `𝓘`-measurable (Georgii: "`π(A | ·)` is
`𝓘`-measurable for `A ∈ 𝒞`"). -/
lemma ergodicRatCDF_vadd [DecidableEq G]
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (g : G) (ω : Ω) : ergodicRatCDF Ω F (g +ᵥ ω) = ergodicRatCDF Ω F ω := by
  by_cases hω : ω ∈ ergodicConvergenceSet Ω F
  · have hgω := vadd_mem_ergodicConvergenceSet hFol hω g
    funext q
    rw [ergodicRatCDF_of_mem hω, ergodicRatCDF_of_mem hgω]
    obtain ⟨c, hc⟩ := (mem_ergodicConvergenceSet Ω F).1 hω q
    have hgc := (tendsto_inv_card_smul_sum_vadd_vadd_iff hFol (M := 1) (fun ω ↦ by
      by_cases h : ω ∈ embeddingReal Ω ⁻¹' Iic (q : ℝ) <;> simp [h]) g ω).2 hc
    rw [hgc.limUnder_eq, hc.limUnder_eq]
  · have hgω : g +ᵥ ω ∉ ergodicConvergenceSet Ω F := fun h ↦ hω (by
      simpa using vadd_mem_ergodicConvergenceSet hFol h (-g))
    simp [ergodicRatCDF, hω, hgω]

lemma measurable_ergodicRatCDF [DecidableEq G]
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0)) :
    Measurable[𝓘] (ergodicRatCDF Ω F) :=
  MeasurableSpace.measurable_invariants_of_forall_smul_eq measurable_ergodicRatCDF'
    fun c ω ↦ ergodicRatCDF_vadd hFol (Multiplicative.toAdd c) ω

variable (Ω F) [DecidableEq G]
  (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))

/-- The `𝓘`-measurable kernel to `ℝ` obtained from the rational ergodic CDF. -/
noncomputable def ergodicRealKernel : Kernel[𝓘] Ω ℝ :=
  kernelOfMeasurableRat 𝓘 (ergodicRatCDF Ω F) (measurable_ergodicRatCDF hFol)

instance : IsMarkovKernel (ergodicRealKernel Ω F hFol) := isMarkovKernel_kernelOfMeasurableRat _ _ _

variable (ν₀ : Measure Ω)

/-- The invariant event on which `ergodicRealKernel` is carried by the range of `embeddingReal`. -/
def ergodicRangeSet : Set Ω := {ω | ergodicRealKernel Ω F hFol ω (range (embeddingReal Ω)) = 1}

lemma measurableSet_ergodicRangeSet : MeasurableSet[𝓘] (ergodicRangeSet Ω F hFol) :=
  (measurableSet_singleton 1).preimage
    (Kernel.measurable_coe _ (measurableEmbedding_embeddingReal _).measurableSet_range)

variable {Ω}

open Classical in
/-- `ergodicRealKernel`, replaced off `ergodicRangeSet` by the pushforward of `ν₀`. -/
noncomputable def ergodicRealKernel' : Kernel[𝓘] Ω ℝ :=
  Kernel.piecewise (measurableSet_ergodicRangeSet Ω F hFol) (ergodicRealKernel Ω F hFol)
    (@Kernel.const Ω ℝ 𝓘 _ (ν₀.map (embeddingReal Ω)))

lemma ergodicRealKernel'_apply_range [IsProbabilityMeasure ν₀] (ω : Ω) :
    ergodicRealKernel' F hFol ν₀ ω (range (embeddingReal Ω)) = 1 := by
  classical
  rw [ergodicRealKernel', Kernel.piecewise_apply]
  split_ifs with h
  · exact h
  · rw [Kernel.const_apply, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]

/-- The candidate `(𝓟_G, 𝓘)`-kernel, before correction on the bad invariant set. -/
noncomputable def ergodicKernelAux : Kernel[𝓘] Ω Ω :=
  Kernel.comapRight (ergodicRealKernel' F hFol ν₀) (measurableEmbedding_embeddingReal Ω)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (ergodicKernelAux F hFol ν₀) :=
  Kernel.IsMarkovKernel.comapRight _ _ (ergodicRealKernel'_apply_range F hFol ν₀)

variable [Countable G]

/-- The invariant event on which `ergodicKernelAux` is an invariant probability measure. -/
def ergodicInvariantSet : Set Ω := {ω | IsVAddInvariantCore G (ergodicKernelAux F hFol ν₀ ω)}

lemma measurableSet_ergodicInvariantSet : MeasurableSet[𝓘] (ergodicInvariantSet F hFol ν₀) :=
  (measurableSet_isVAddInvariantCore G Ω).preimage (ergodicKernelAux F hFol ν₀).measurable

open Classical in
/-- **Georgii (14.10), the `(𝓟_Θ, 𝓘)`-kernel**: the `μ`-independent kernel from `(Ω, 𝓘)` to
`(Ω, 𝓕)`, equal to `ν₀` off `ergodicInvariantSet`. -/
noncomputable def ergodicKernel : Kernel[𝓘] Ω Ω :=
  Kernel.piecewise (measurableSet_ergodicInvariantSet F hFol ν₀) (ergodicKernelAux F hFol ν₀)
    (@Kernel.const Ω Ω 𝓘 _ ν₀)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (ergodicKernel F hFol ν₀) := by
  unfold ergodicKernel; infer_instance

/-- Every value of `ergodicKernel` is an invariant probability measure. -/
lemma ergodicKernel_mem [IsProbabilityMeasure ν₀] [VAddInvariantMeasure G Ω ν₀] (ω : Ω) :
    IsProbabilityMeasure (ergodicKernel F hFol ν₀ ω) ∧
      VAddInvariantMeasure G Ω (ergodicKernel F hFol ν₀ ω) := by
  classical
  rw [ergodicKernel, Kernel.piecewise_apply]
  split_ifs with h
  · exact isVAddInvariantCore_iff.1 h
  · rw [Kernel.const_apply]; exact ⟨‹_›, ‹_›⟩

/-! #### Identification with `μ(· | 𝓘)` -/

variable {F ν₀} {μ : Measure Ω} [IsProbabilityMeasure μ] [VAddInvariantMeasure G Ω μ]
  {C : ℝ≥0∞}

include hFol in
/-- The multidimensional ergodic theorem (14.A8) on the countable core: for `μ`-a.e. `ω`, the
ergodic averages of all the half-line indicators converge to `μ(e ≤ q | 𝓘)(ω)`. -/
lemma ae_forall_tendsto_inv_card_smul_sum_vadd_indicator (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ •
      ∑ i ∈ F n, (embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) (i +ᵥ ω)) atTop
        (𝓝 ((μ[(embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) | 𝓘]) ω)) :=
  ae_forall_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC' fun _ ↦
    (integrable_const (1 : ℝ)).indicator (measurableSet_Iic.preimage (measurable_embeddingReal Ω))

include hFol in
lemma ae_mem_ergodicConvergenceSet (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞) :
    ∀ᵐ ω ∂μ, ω ∈ ergodicConvergenceSet Ω F := by
  filter_upwards [ae_forall_tendsto_inv_card_smul_sum_vadd_indicator (μ := μ) hFol hF hne hC hC']
    with ω hω
  exact (mem_ergodicConvergenceSet Ω F).2 fun q ↦ ⟨_, hω q⟩

include hFol in
/-- On `Ω₀`, the rational ergodic CDF is `μ`-a.s. the CDF of the image under `embeddingReal` of
the conditional distribution `μ(· | 𝓘)`. -/
lemma ae_forall_ergodicRatCDF_eq (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, ergodicRatCDF Ω F ω q =
      ((condExpKernel μ 𝓘 ω).map (embeddingReal Ω)).real (Iic (q : ℝ)) := by
  have hle : 𝓘 ≤ ‹MeasurableSpace Ω› := MeasurableSpace.smulInvariants_le
  have hker : ∀ᵐ ω ∂μ, ∀ q : ℚ, (condExpKernel μ 𝓘 ω).real (embeddingReal Ω ⁻¹' Iic (q : ℝ)) =
      (μ[(embeddingReal Ω ⁻¹' Iic (q : ℝ)).indicator (fun _ ↦ (1 : ℝ)) | 𝓘]) ω :=
    ae_all_iff.2 fun q ↦ condExpKernel_ae_eq_condExp hle
      (measurableSet_Iic.preimage (measurable_embeddingReal Ω))
  filter_upwards [ae_forall_tendsto_inv_card_smul_sum_vadd_indicator (μ := μ) hFol hF hne hC hC',
    hker] with ω hω hkω
  have hω₀ : ω ∈ ergodicConvergenceSet Ω F := (mem_ergodicConvergenceSet Ω F).2 fun q ↦ ⟨_, hω q⟩
  intro q
  rw [ergodicRatCDF_of_mem hω₀, (hω q).limUnder_eq, ← hkω q,
    map_measureReal_apply (measurable_embeddingReal _) measurableSet_Iic]

lemma ae_ergodicRealKernel_eq_map (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞) :
    ∀ᵐ ω ∂μ, ergodicRealKernel Ω F hFol ω = (condExpKernel μ 𝓘 ω).map (embeddingReal Ω) := by
  filter_upwards [ae_forall_ergodicRatCDF_eq (μ := μ) hFol hF hne hC hC'] with ω hω
  have : IsProbabilityMeasure ((condExpKernel μ 𝓘 ω).map (embeddingReal Ω)) :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal _).aemeasurable
  exact kernelOfMeasurableRat_eq 𝓘 (measurable_ergodicRatCDF hFol) _ hω

omit [DecidableEq G] in
/-- The conditional distributions `μ(· | 𝓘)` of an invariant probability measure are `μ`-a.s.
invariant probability measures (Georgii: `{π' ∈ 𝓟_Θ}` has `μ`-probability one). -/
lemma ae_isVAddInvariantCore_condExpKernel :
    ∀ᵐ ω ∂μ, IsVAddInvariantCore G (condExpKernel μ 𝓘 ω) := by
  have hle : 𝓘 ≤ ‹MeasurableSpace Ω› := MeasurableSpace.smulInvariants_le
  have h : ∀ᵐ ω ∂μ, ∀ (g : G) (t : Finset ℕ),
      condExpKernel μ 𝓘 ω ((g +ᵥ ·) ⁻¹' piNatGen (Ω := Ω) t)
        = condExpKernel μ 𝓘 ω (piNatGen t) := by
    refine ae_all_iff.2 fun g ↦ ae_all_iff.2 fun t ↦ ?_
    have hB := measurableSet_piNatGen (Ω := Ω) t
    filter_upwards [condExpKernel_ae_eq_condExp hle (hB.preimage (measurable_const_vadd g)),
      condExpKernel_ae_eq_condExp hle hB,
      condExp_indicator_preimage_vadd_smulInvariants (μ := μ) hB g] with ω h1 h2 h3
    have hreal : (condExpKernel μ 𝓘 ω).real ((g +ᵥ ·) ⁻¹' piNatGen (Ω := Ω) t) =
        (condExpKernel μ 𝓘 ω).real (piNatGen t) := by rw [h1, h2, h3]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
  filter_upwards [h] with ω hω
  exact ⟨measure_univ, hω⟩

/-- `ergodicKernel` is `μ`-a.s. the conditional distribution `μ(· | 𝓘)`, for every invariant
probability measure `μ`. -/
lemma ae_ergodicKernel_eq_condExpKernel [IsProbabilityMeasure ν₀] (hF : Monotone F)
    (hne : (F 0).Nonempty) (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card)
    (hC' : C ≠ ∞) :
    ∀ᵐ ω ∂μ, ergodicKernel F hFol ν₀ ω = condExpKernel μ 𝓘 ω := by
  classical
  filter_upwards [ae_ergodicRealKernel_eq_map (μ := μ) hFol hF hne hC hC',
    ae_isVAddInvariantCore_condExpKernel (G := G) (μ := μ)] with ω h1 h2
  have hrange : ω ∈ ergodicRangeSet Ω F hFol := by
    change ergodicRealKernel Ω F hFol ω (range (embeddingReal Ω)) = 1
    rw [h1, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]
  have haux : ergodicKernelAux F hFol ν₀ ω = condExpKernel μ 𝓘 ω := by
    rw [ergodicKernelAux, Kernel.comapRight_apply, ergodicRealKernel', Kernel.piecewise_apply,
      ite_eq_left hrange, h1, (measurableEmbedding_embeddingReal _).comap_map]
  have hgood : ω ∈ ergodicInvariantSet F hFol ν₀ := by
    change IsVAddInvariantCore G (ergodicKernelAux F hFol ν₀ ω)
    rw [haux]; exact h2
  rw [ergodicKernel, Kernel.piecewise_apply, ite_eq_left hgood, haux]

/-- Georgii (7.21)(i) for `ergodicKernel`: it is a version of `μ(· | 𝓘)` for every invariant
probability measure `μ`. -/
theorem condExp_ae_eq_ergodicKernel [IsProbabilityMeasure ν₀] (hF : Monotone F)
    (hne : (F 0).Nonempty) (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card)
    (hC' : C ≠ ∞) {A : Set Ω} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝓘] =ᵐ[μ] fun ω ↦ (ergodicKernel F hFol ν₀ ω).real A := by
  filter_upwards [ae_ergodicKernel_eq_condExpKernel (μ := μ) (ν₀ := ν₀) hFol hF hne hC hC',
    condExpKernel_ae_eq_condExp (μ := μ)
      (MeasurableSpace.smulInvariants_le (M := Multiplicative G)) hA]
    with ω h1 h2
  rw [h1, ← h2]

variable (Ω F ν₀) in
/-- **Georgii, Theorem (14.10), first assertion, for a countable abelian group** acting on a
standard Borel space along an increasing regular Følner sequence: `ergodicKernel F hFol ν₀` is a
`(𝓟_G, 𝓘)`-kernel — a version of `μ(· | 𝓘)` for every invariant probability measure `μ`, with all
its values invariant probability measures. `P` is the set of invariant probability measures,
given through the characterisation `hP`. -/
theorem isPAKernel_ergodicKernel [IsProbabilityMeasure ν₀] [VAddInvariantMeasure G Ω ν₀]
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {P : Set (Measure Ω)} (hP : ∀ ν, ν ∈ P ↔ IsProbabilityMeasure ν ∧ VAddInvariantMeasure G Ω ν) :
    IsPAKernel P 𝓘 (ergodicKernel F hFol ν₀) :=
  ⟨fun μ hμ A hA ↦ by
    obtain ⟨hμ₁, hμ₂⟩ := (hP μ).1 hμ
    exact (condExp_ae_eq_ergodicKernel (μ := μ) hFol hF hne hC hC' hA).symm,
    fun ω ↦ (hP _).2 (ergodicKernel_mem F hFol ν₀ ω)⟩

include hFol in
variable (G Ω) in
/-- **Georgii, Theorem (14.10), first assertion**: for a countable abelian group `G` acting
measurably on a standard Borel space `Ω`, with an increasing regular Følner sequence of finite
sets (cubes on `ℤ^d`), there is a `(𝓟_G, 𝓘)`-kernel as soon as `𝓟_G ≠ ∅`. -/
theorem exists_isPAKernel_of_vaddInvariant (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {P : Set (Measure Ω)} (hP : ∀ ν, ν ∈ P ↔ IsProbabilityMeasure ν ∧ VAddInvariantMeasure G Ω ν)
    (hne' : P.Nonempty) :
    ∃ π : Kernel[𝓘] Ω Ω, IsMarkovKernel π ∧ IsPAKernel P 𝓘 π := by
  obtain ⟨ν₀, hν₀⟩ := hne'
  obtain ⟨h₁, h₂⟩ := (hP ν₀).1 hν₀
  exact ⟨ergodicKernel F hFol ν₀, inferInstance,
    isPAKernel_ergodicKernel Ω F hFol ν₀ hF hne hC hC' hP⟩

end ErgodicKernel

namespace IsPAKernel

section StandardBorel

variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [m : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Set (Measure Ω)} {π : Kernel[𝒜, m] Ω Ω} [IsMarkovKernel π]
  (hπ : IsPAKernel P 𝒜 π) (h𝒜 : 𝒜 ≤ m)

include hπ h𝒜

/-- A `(P, 𝒜)`-kernel is, for every `μ ∈ P`, `μ`-a.s. equal to the regular conditional
distribution `condExpKernel μ 𝒜`: both are versions of `μ(· | 𝒜)` on a countable π-system
generating the σ-algebra. -/
lemma ae_eq_condExpKernel {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    ∀ᵐ ω ∂μ, π ω = condExpKernel μ 𝒜 ω := by
  have h : ∀ᵐ ω ∂μ, ∀ t : Finset ℕ,
      π ω (piNatGen (Ω := Ω) t) = condExpKernel μ 𝒜 ω (piNatGen t) := by
    refine ae_all_iff.2 fun t ↦ ?_
    filter_upwards [hπ.1 μ hμ _ (measurableSet_piNatGen t),
      condExpKernel_ae_eq_condExp (μ := μ) h𝒜 (measurableSet_piNatGen t)] with ω h1 h2
    have hreal : (π ω).real (piNatGen (Ω := Ω) t) = (condExpKernel μ 𝒜 ω).real (piNatGen t) := by
      rw [h1, h2]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
  filter_upwards [h] with ω hω
  refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
    generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
  rintro s ⟨t, rfl⟩
  exact hω t

end StandardBorel

end IsPAKernel

/-! ### Configuration space: the shift group of an abelian site group

Georgii's Chapter 14 acts on `S → E` through the shift group `Θ = shiftGroup S E ≤ T` (5.2)(1),
while the ergodic theorem (14.A8) is stated for an additive group acting by `+ᵥ`. The bridge is
the action `j +ᵥ ω = θ_j ω` of the site group on configuration space, a *local* instance
(`Pi.instVAdd` would compete with it whenever `E` is itself an `S`-set): under it, the invariant
σ-algebra `MeasurableSpace.smulInvariants (Multiplicative S) (S → E)` is `invariantEvents Θ` and
the invariant probability measures are `invariantFields Θ`. -/

section Shift

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S]

attribute [local instance] shiftAddAction measurableConstVAdd_shift

/-- `𝓟_Θ` is measurable in `Measure (S → E)` for the shift group of a countable site group. -/
lemma measurableSet_invariantFields_shiftGroup [Countable S] [StandardBorelSpace E] :
    MeasurableSet (invariantFields (shiftGroup S E)) := by
  have : invariantFields (shiftGroup S E) =
      {ν : Measure (S → E) | IsProbabilityMeasure ν ∧ VAddInvariantMeasure S (S → E) ν} :=
    Set.ext fun _ ↦ mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure
  rw [this]
  exact measurableSet_setOf_isProbabilityMeasure_and_vaddInvariantMeasure

/-! #### Georgii (14.10) on configuration space -/

variable [Countable S] [DecidableEq S] [StandardBorelSpace E] (F : ℕ → Finset S)
  (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
  (ν₀ : Measure (S → E))

/-- **Georgii (14.10), the `(𝓟_Θ, 𝓘)`-kernel on configuration space**: `ergodicKernel` for the
shift action, read as a kernel from `(Ω, 𝓘)`, `𝓘 = invariantEvents Θ`. -/
noncomputable def shiftErgodicKernel :
    Kernel[invariantEvents (shiftGroup S E)] (S → E) (S → E) :=
  (ergodicKernel F hFol ν₀).comap id
    (measurable_id'' smulInvariants_multiplicative_eq_invariantEvents_shiftGroup.le)

@[simp] lemma shiftErgodicKernel_apply (ω : S → E) :
    shiftErgodicKernel F hFol ν₀ ω = ergodicKernel F hFol ν₀ ω := rfl

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (shiftErgodicKernel F hFol ν₀) := by
  unfold shiftErgodicKernel; infer_instance

variable {F ν₀} {C : ℝ≥0∞}

/-- **Georgii, Theorem (14.10), first assertion, on configuration space**: along an increasing
regular Følner sequence of finite volumes (cubes on `ℤ^d`), `shiftErgodicKernel F hFol ν₀` is a
`(𝓟_Θ, 𝓘)`-kernel for every `ν₀ ∈ 𝓟_Θ`. -/
theorem isPAKernel_shiftErgodicKernel (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hν₀ : ν₀ ∈ invariantFields (shiftGroup S E)) :
    IsPAKernel (invariantFields (shiftGroup S E)) (invariantEvents (shiftGroup S E))
      (shiftErgodicKernel F hFol ν₀) := by
  obtain ⟨h₁, h₂⟩ := mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure.1 hν₀
  have h := isPAKernel_ergodicKernel (S → E) F hFol ν₀ hF hne hC hC'
    (P := invariantFields (shiftGroup S E))
    fun _ ↦ mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure
  refine ⟨fun μ hμ A hA ↦ ?_, h.2⟩
  have hce : μ[A.indicator (fun _ ↦ (1 : ℝ)) | invariantEvents (shiftGroup S E)] =
      μ[A.indicator (fun _ ↦ (1 : ℝ)) |
        MeasurableSpace.smulInvariants (Multiplicative S) (S → E)] := by
    rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
  rw [hce]
  exact h.1 μ hμ A hA

include hFol in
/-- **Georgii, Theorem (14.10), first assertion**: for the shift group `Θ` of a countable
abelian site group admitting an increasing regular Følner sequence, and a standard Borel state
space, there is a `(𝓟_Θ, 𝓘)`-kernel as soon as `𝓟_Θ ≠ ∅`. -/
theorem exists_isPAKernel_invariantFields_shiftGroup (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    (hne' : (invariantFields (shiftGroup S E)).Nonempty) :
    ∃ π : Kernel[invariantEvents (shiftGroup S E)] (S → E) (S → E), IsMarkovKernel π ∧
      IsPAKernel (invariantFields (shiftGroup S E)) (invariantEvents (shiftGroup S E)) π := by
  obtain ⟨ν₀, hν₀⟩ := hne'
  have := (mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure.1 hν₀).1
  exact ⟨shiftErgodicKernel F hFol ν₀, inferInstance,
    isPAKernel_shiftErgodicKernel hFol hF hne hC hC' hν₀⟩

end Shift

/-! #### The cubes of `ℤ^d` -/

section Cube

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E] [StandardBorelSpace E]

omit [Fintype ι] [DecidableEq ι] in
/-- **Georgii, Theorem (14.10), first assertion, on `ℤ^d`**: for a standard Borel state space
there is a `(𝓟_Θ, 𝓘)`-kernel for the shift group of `ℤ^d` (along the cubes `[0, n)^d`), as
soon as `𝓟_Θ ≠ ∅`. -/
theorem exists_isPAKernel_invariantFields_shiftGroup_int [Finite ι]
    (hne' : (invariantFields (shiftGroup (ι → ℤ) E)).Nonempty) :
    ∃ π : Kernel[invariantEvents (shiftGroup (ι → ℤ) E)] ((ι → ℤ) → E) ((ι → ℤ) → E),
      IsMarkovKernel π ∧
        IsPAKernel (invariantFields (shiftGroup (ι → ℤ) E))
          (invariantEvents (shiftGroup (ι → ℤ) E)) π := by
  classical
  have := Fintype.ofFinite ι
  set F : ℕ → Finset (ι → ℤ) := fun n ↦ (fun _ : ι ↦ (0 : ℤ)) +ᵥ
    Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) ((n + 1 : ℕ) : ℤ) with hFdef
  have hF : Monotone F := fun a b hab ↦ Finset.image_subset_image
    (Fintype.piFinset_subset _ _ fun _ ↦ Finset.Ico_subset_Ico le_rfl
      (by exact_mod_cast Nat.add_le_add_right hab 1))
  have hne : (F 0).Nonempty :=
    ⟨_, Finset.mem_vadd_finset.2 ⟨0, Fintype.mem_piFinset.2 fun _ ↦ by simp, rfl⟩⟩
  have hFol : ∀ g : ι → ℤ,
      Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0) := fun g ↦
    tendsto_card_vadd_cube_symmDiff_div_card (ι := ι) (fun _ _ ↦ 0) (r := fun n ↦ n + 1)
      (tendsto_add_atTop_nat 1) g
  have hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ (3 ^ Fintype.card ι : ℝ≥0∞) * (F n).card :=
    fun n ↦ by exact_mod_cast card_sub_add_cube_le (fun _ : ι ↦ (0 : ℤ)) (n + 1)
  exact exists_isPAKernel_invariantFields_shiftGroup (F := F) hFol hF hne hC (by simp) hne'

end Cube

/-! ### `𝓟_Θ` for a countable subgroup `Θ ≤ T`: measurability, convexity, the decomposition -/

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated Ω]

/-- The invariant probability measures of a countable group action form a measurable subset of
`Measure Ω`: they are cut out by the countable core `ν(g • A) = ν(A)`, `A` in a countable
generating π-system (Georgii, proof of (14.10)). -/
lemma measurableSet_setOf_isProbabilityMeasure_and_smulInvariantMeasure {M : Type*} [Group M]
    [Countable M] [MulAction M Ω] [MeasurableConstSMul M Ω] :
    MeasurableSet {ν : Measure Ω | IsProbabilityMeasure ν ∧ SMulInvariantMeasure M Ω ν} := by
  have hcore : {ν : Measure Ω | IsProbabilityMeasure ν ∧ SMulInvariantMeasure M Ω ν} =
      {ν : Measure Ω | ν univ = 1 ∧ ∀ (g : M) (t : Finset ℕ),
        ν ((g • ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)} := by
    ext ν
    constructor
    · rintro ⟨hprob, hinv⟩
      exact ⟨measure_univ, fun g t ↦ hinv.measure_preimage_smul g (measurableSet_piNatGen t)⟩
    · rintro ⟨h1, h⟩
      have hprob : IsProbabilityMeasure ν := ⟨h1⟩
      refine ⟨hprob, ⟨fun g s hs ↦ ?_⟩⟩
      have hmap : ν.map (g • ·) = ν := by
        have : IsProbabilityMeasure (ν.map (g • · : Ω → Ω)) :=
          Measure.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable
        refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
          generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
        rintro s ⟨t, rfl⟩
        rw [Measure.map_apply (measurable_const_smul g) (measurableSet_piNatGen t)]
        exact h g t
      conv_rhs => rw [← hmap]
      rw [Measure.map_apply (measurable_const_smul g) hs]
  rw [hcore]
  have h_univ : MeasurableSet {ν : Measure Ω | ν univ = (1 : ℝ≥0∞)} :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage (Measure.measurable_coe MeasurableSet.univ)
  have hEq (g : M) (t : Finset ℕ) : MeasurableSet {ν : Measure Ω |
      ν ((g • ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)} :=
    measurableSet_eq_fun
      (Measure.measurable_coe ((measurableSet_piNatGen t).preimage (measurable_const_smul g)))
      (Measure.measurable_coe (measurableSet_piNatGen t))
  have hAll : MeasurableSet {ν : Measure Ω | ∀ (g : M) (t : Finset ℕ),
      ν ((g • ·) ⁻¹' piNatGen (Ω := Ω) t) = ν (piNatGen t)} := by
    simpa [Set.ofPred_forall] using
      MeasurableSet.iInter fun g ↦ MeasurableSet.iInter fun t ↦ hEq g t
  simpa [Set.ofPred_and, Set.ofPred_forall] using h_univ.inter hAll

end Measurability

section InvariantFields

variable {S E : Type*} [MeasurableSpace E] {Θ : Subgroup (Transformation S E)}

/-- `𝓟_Θ` is measurable in `Measure (S → E)` for a countable subgroup `Θ ≤ T`. -/
lemma measurableSet_invariantFields [Countable S] [StandardBorelSpace E] [Countable Θ] :
    MeasurableSet (invariantFields Θ) :=
  measurableSet_setOf_isProbabilityMeasure_and_smulInvariantMeasure (M := Θ)

/-- Every element of `𝓟_Θ` is a probability measure. -/
lemma isProbabilityMeasure_of_mem_invariantFields {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ) : IsProbabilityMeasure μ :=
  (mem_invariantFields.1 hμ).1

/-- **Georgii, Theorem (14.5)(a)**, set form: `ex 𝓟_Θ = 𝓟_Θ ∩ P_𝓘`. -/
lemma extremePoints_invariantFields_eq_inter_trivialOn [Countable Θ] :
    (invariantFields Θ).extremePoints ℝ≥0∞ =
      invariantFields Θ ∩ trivialOn (invariantEvents Θ) := by
  ext μ
  exact ⟨fun h ↦ ⟨extremePoints_subset h,
      (mem_extremePoints_invariantFields_iff_mem_trivialOn (extremePoints_subset h)).1 h⟩,
    fun h ↦ (mem_extremePoints_invariantFields_iff_mem_trivialOn h.1).2 h.2⟩

/-- The barycentre of a probability weight carried by `𝓟_Θ` lies in `𝓟_Θ`. -/
lemma join_mem_invariantFields [Countable S] [StandardBorelSpace E] [Countable Θ]
    (w : Measure (Measure (S → E))) [IsProbabilityMeasure w] (hw : w (invariantFields Θ)ᶜ = 0) :
    Measure.join w ∈ invariantFields Θ := by
  have hae : ∀ᵐ ν ∂w, ν ∈ invariantFields Θ := ae_iff.2 hw
  refine mem_invariantFields.2 ⟨isProbabilityMeasure_join_of_ae w
    (hae.mono fun ν hν ↦ isProbabilityMeasure_of_mem_invariantFields hν), ?_⟩
  exact smulInvariantMeasure_join_of_ae w (hae.mono fun ν hν ↦ (mem_invariantFields.1 hν).2)

/-- **Georgii, Theorem (14.10)** for a countable subgroup `Θ ≤ T`, given a `(𝓟_Θ, 𝓘)`-kernel
`π` (which exists for the shift group of a site group with a regular Følner sequence, by
`exists_isPAKernel_invariantFields_shiftGroup`): `ex 𝓟_Θ ≠ ∅`; every `μ ∈ 𝓟_Θ` is represented by a
unique probability weight on `ex 𝓟_Θ`; `μ ↦ w_μ = weight π μ` is an affine bijection from `𝓟_Θ`
onto the probability weights carried by `ex 𝓟_Θ`; `w_μ` is the image of `μ` under `ω ↦ π(· | ω)`;
and `w_μ(ν(A) ≤ c) = μ(μ(A | 𝓘) ≤ c)`. -/
theorem ergodicDecomposition_invariantFields [Countable S] [StandardBorelSpace E] [Countable Θ]
    {π : Kernel[invariantEvents Θ] (S → E) (S → E)} [IsMarkovKernel π]
    (hπ : IsPAKernel (invariantFields Θ) (invariantEvents Θ) π)
    (hne : (invariantFields Θ).Nonempty) :
    ((invariantFields Θ).extremePoints ℝ≥0∞).Nonempty ∧
    (∀ μ ∈ invariantFields Θ, ∃! w : Measure (Measure (S → E)), IsProbabilityMeasure w ∧
      w ((invariantFields Θ).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ) ∧
    BijOn (weight π) (invariantFields Θ) {w : Measure (Measure (S → E)) |
      IsProbabilityMeasure w ∧ w ((invariantFields Θ).extremePoints ℝ≥0∞)ᶜ = 0} ∧
    (∀ (μ ν : Measure (S → E)) (a b : ℝ≥0∞),
      weight π (a • μ + b • ν) = a • weight π μ + b • weight π ν) ∧
    (∀ μ : Measure (S → E), weight π μ = μ.map π) ∧
    ∀ μ ∈ invariantFields Θ, ∀ A, MeasurableSet A → ∀ c : ℝ,
      weight π μ {ν | ν.real A ≤ c} =
        μ {ω | (μ[A.indicator (fun _ ↦ (1 : ℝ)) | invariantEvents Θ]) ω ≤ c} := by
  have hle : invariantEvents Θ ≤ MeasurableSpace.pi := MeasurableSpace.smulInvariants_le
  have hP : ∀ μ ∈ invariantFields Θ, IsProbabilityMeasure μ := fun _ ↦
    isProbabilityMeasure_of_mem_invariantFields
  refine ⟨hπ.nonempty_extremePoints hle hP extremePoints_invariantFields_eq_inter_trivialOn hne,
    fun μ hμ ↦ hπ.exists_unique_weight_extremePoints hle hP measurableSet_invariantFields
      extremePoints_invariantFields_eq_inter_trivialOn hμ,
    hπ.bijOn_weight hle hP measurableSet_invariantFields
      extremePoints_invariantFields_eq_inter_trivialOn fun w hw hw' ↦ ?_,
    fun μ ν a b ↦ IsPAKernel.weight_add_smul hle μ ν a b, fun _ ↦ rfl,
    fun μ hμ A hA c ↦ hπ.weight_setOf_real_le hle hP hμ hA c⟩
  exact join_mem_invariantFields w
    (measure_mono_null (compl_subset_compl.2 extremePoints_subset) hw')

/-! #### Georgii (14.11): symmetries commuting with `Θ` -/

section Normalizer

variable {τ : Transformation S E}

/-- A transformation normalising `Θ` (Georgii's `τ ∘ Θ = Θ ∘ τ`, (5.14)) pulls invariant events
back to invariant events: `𝓘` is stable under `τ⁻¹`. -/
lemma preimage_measurableSet_invariantEvents_of_mem_normalizer
    (hτ : τ ∈ Subgroup.normalizer (Θ : Set (Transformation S E)))
    {A : Set (S → E)} (hA : MeasurableSet[invariantEvents Θ] A) :
    MeasurableSet[invariantEvents Θ] (τ.toFun ⁻¹' A) := by
  rw [measurableSet_invariantEvents] at hA ⊢
  refine ⟨hA.1.preimage τ.measurable_toFun, fun θ hθ ↦ ?_⟩
  have hθ' : τ * θ * τ⁻¹ ∈ Θ := (Subgroup.mem_normalizer_iff.1 hτ θ).1 hθ
  ext ω
  simp only [Set.mem_preimage]
  have hcomm : τ.toFun (θ.toFun ω) = (τ * θ * τ⁻¹).toFun (τ.toFun ω) := by
    change τ • (θ • ω) = (τ * θ * τ⁻¹) • (τ • ω)
    rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
  rw [hcomm]
  exact Set.ext_iff.1 (hA.2 _ hθ') (τ.toFun ω)

/-- **Georgii, before (14.11)**: a transformation normalising `Θ` maps `𝓟_Θ` into itself. -/
lemma map_mem_invariantFields_of_mem_normalizer
    (hτ : τ ∈ Subgroup.normalizer (Θ : Set (Transformation S E))) {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ) : μ.map τ.toFun ∈ invariantFields Θ := by
  rw [mem_invariantFields_iff] at hμ ⊢
  obtain ⟨hprob, hinv⟩ := hμ
  refine ⟨Measure.isProbabilityMeasure_map τ.measurable_toFun.aemeasurable, fun θ hθ ↦ ?_⟩
  have hθ' : τ⁻¹ * θ * τ ∈ Θ := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hτ) θ).1 hθ
    rwa [inv_inv] at this
  have hcomp : θ.toFun ∘ τ.toFun = τ.toFun ∘ (τ⁻¹ * θ * τ).toFun := by
    funext ω
    change θ • (τ • ω) = τ • ((τ⁻¹ * θ * τ) • ω)
    rw [← mul_smul, ← mul_smul, ← mul_assoc, mul_inv_cancel_left]
  refine ⟨θ.measurable_toFun, ?_⟩
  rw [Measure.map_map θ.measurable_toFun τ.measurable_toFun, hcomp,
    ← Measure.map_map τ.measurable_toFun (τ⁻¹ * θ * τ).measurable_toFun, (hinv _ hθ').map_eq]

/-- A transformation normalising `Θ` preserves triviality on `𝓘`. -/
lemma map_mem_trivialOn_invariantEvents_of_mem_normalizer
    (hτ : τ ∈ Subgroup.normalizer (Θ : Set (Transformation S E)))
    {μ : Measure (S → E)} (hμ : μ ∈ trivialOn (invariantEvents Θ)) :
    μ.map τ.toFun ∈ trivialOn (invariantEvents Θ) := fun A hA ↦ by
  rw [Measure.map_apply τ.measurable_toFun (MeasurableSpace.smulInvariants_le _ hA)]
  exact hμ _ (preimage_measurableSet_invariantEvents_of_mem_normalizer hτ hA)

/-- **Georgii, before (14.11)**: a transformation normalising `Θ` maps ergodic (extreme)
`Θ`-invariant random fields to ergodic ones. -/
lemma map_mem_extremePoints_invariantFields_of_mem_normalizer [Countable Θ]
    (hτ : τ ∈ Subgroup.normalizer (Θ : Set (Transformation S E))) {μ : Measure (S → E)}
    (hμ : μ ∈ (invariantFields Θ).extremePoints ℝ≥0∞) :
    μ.map τ.toFun ∈ (invariantFields Θ).extremePoints ℝ≥0∞ := by
  have hμP := extremePoints_subset hμ
  rw [mem_extremePoints_invariantFields_iff_mem_trivialOn hμP] at hμ
  rw [mem_extremePoints_invariantFields_iff_mem_trivialOn
    (map_mem_invariantFields_of_mem_normalizer hτ hμP)]
  exact map_mem_trivialOn_invariantEvents_of_mem_normalizer hτ hμ

/-- **Georgii, Corollary (14.11)**: for a transformation `τ` normalising `Θ` (`τ ∘ Θ = Θ ∘ τ`),
the ergodic decomposition commutes with `τ`: `w_{τ(μ)} = τ(w_μ)` for `μ ∈ 𝓟_Θ`. -/
theorem weight_map_of_mem_normalizer [Countable S] [StandardBorelSpace E] [Countable Θ]
    {π : Kernel[invariantEvents Θ] (S → E) (S → E)} [IsMarkovKernel π]
    (hπ : IsPAKernel (invariantFields Θ) (invariantEvents Θ) π)
    (hτ : τ ∈ Subgroup.normalizer (Θ : Set (Transformation S E)))
    {μ : Measure (S → E)} (hμ : μ ∈ invariantFields Θ) :
    weight π (μ.map τ.toFun) = (weight π μ).map (Measure.map τ.toFun) :=
  hπ.weight_map MeasurableSpace.smulInvariants_le
    (fun _ ↦ isProbabilityMeasure_of_mem_invariantFields) measurableSet_invariantFields
    extremePoints_invariantFields_eq_inter_trivialOn τ.measurable_toFun
    (fun _ hν ↦ map_mem_extremePoints_invariantFields_of_mem_normalizer hτ hν) hμ

end Normalizer

end InvariantFields

/-! ### Georgii (14.17): the ergodic components of an invariant Gibbs measure are Gibbs -/

section Thm1417

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  {γ : Specification S E} {Θ : Subgroup (Transformation S E)} [Countable Θ]
  (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))

include hΘ

omit [StandardBorelSpace E] [Countable Θ] in
/-- **Georgii (14.9), conditional-expectation form.** For `μ ∈ 𝓟_Θ` (and `Θ` moving every finite
volume off itself), conditioning on `𝓘` factors through every outside σ-algebra `𝓕_{Λᶜ}`:
`μ(μ(f | 𝓕_{Λᶜ}) | 𝓘) = μ(f | 𝓘)` a.s. — because every invariant event agrees a.s. with a
tail event, and `𝓣 ⊆ 𝓕_{Λᶜ}`. -/
lemma condExp_condExp_cylinderEvents_compl_invariantEvents {μ : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ) (Λ : Finset S) {f : (S → E) → ℝ} (hf : Integrable f μ) :
    μ[μ[f | cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] | invariantEvents Θ] =ᵐ[μ]
      μ[f | invariantEvents Θ] := by
  have := isProbabilityMeasure_of_mem_invariantFields hμ
  refine condExp_condExp_of_forall_exists_measure_symmDiff_eq_zero
    MeasurableSpace.smulInvariants_le cylinderEvents_le_pi (fun s hs ↦ ?_) hf
  obtain ⟨t, ht, hst⟩ := exists_measurableSet_tail_measure_symmDiff_eq_zero hμ hΘ hs
  exact ⟨t, tailSigmaAlgebra_le_cylinderEvents Λ _ ht, hst⟩

omit [Countable Θ] in
/-- Georgii's computation in the proof of (14.17): for `μ ∈ 𝒢_Θ(γ)`, the conditional
distributions `μ(· | 𝓘)` are a.s. fixed by every `γ_Λ` on every measurable set,
`π'γ_Λ(A) = μ(γ_Λ(A | ·) | 𝓘) = μ(μ(A | 𝓕_{Λᶜ}) | 𝓘) = μ(A | 𝓘) = π'(A)`. -/
lemma ae_bind_condExpKernel_invariantEvents_apply_eq {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantG γ Θ) (Λ : Finset S) {B : Set (S → E)}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, (condExpKernel μ (invariantEvents Θ) ω).bind (γ Λ) B =
      condExpKernel μ (invariantEvents Θ) ω B := by
  have hle : invariantEvents Θ ≤ MeasurableSpace.pi := MeasurableSpace.smulInvariants_le
  set g : (S → E) → ℝ := fun x ↦ (γ Λ x B).toReal with hg
  have hg_meas : Measurable g :=
    ((Kernel.measurable_coe (γ Λ) hB).mono cylinderEvents_le_pi le_rfl).ennreal_toReal
  have hg_int : ∀ (ν : Measure (S → E)) [IsFiniteMeasure ν], Integrable g ν := fun ν _ ↦
    (memLp_top_of_bound hg_meas.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))).integrable
      le_top
  have h1 : μ[g | invariantEvents Θ] =ᵐ[μ]
      fun ω ↦ ∫ y, g y ∂(condExpKernel μ (invariantEvents Θ) ω) :=
    condExp_ae_eq_integral_condExpKernel hle (hg_int μ)
  have h2 : g =ᵐ[μ] μ[B.indicator (fun _ ↦ (1 : ℝ)) |
      cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] :=
    (AbstractSpecification.condExp_sub_ae_eq (γ := γ.toAbstract)
      (mem_toAbstract_invariant_of_mem_G hμ.1) Λ hB).symm
  have h3 : μ[g | invariantEvents Θ] =ᵐ[μ] μ[B.indicator (fun _ ↦ (1 : ℝ)) | invariantEvents Θ] :=
    (condExp_congr_ae h2).trans (condExp_condExp_cylinderEvents_compl_invariantEvents hΘ hμ.2 Λ
      ((integrable_const (1 : ℝ)).indicator hB))
  filter_upwards [h1, h3, condExpKernel_ae_eq_condExp (μ := μ) hle hB] with ω h1ω h3ω h4ω
  have hint : ∫ y, g y ∂(condExpKernel μ (invariantEvents Θ) ω) =
      (condExpKernel μ (invariantEvents Θ) ω).real B := by
    rw [← h1ω, h3ω, h4ω]
  have hlint : ∫⁻ x, γ Λ x B ∂(condExpKernel μ (invariantEvents Θ) ω)
      = ENNReal.ofReal (∫ y, g y ∂(condExpKernel μ (invariantEvents Θ) ω)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hg_int _) (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)]
    exact lintegral_congr fun x ↦ (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [Measure.bind_apply hB ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable,
    hlint, hint, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

omit [Countable Θ] in
/-- For `μ ∈ 𝒢_Θ(γ)`, the conditional distributions `μ(· | 𝓘)` a.s. satisfy the countable Gibbs
core. -/
lemma ae_isGibbsCore_condExpKernel_invariantEvents {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantG γ Θ) :
    ∀ᵐ ω ∂μ, IsGibbsCore γ (condExpKernel μ (invariantEvents Θ) ω) := by
  have h : ∀ᵐ ω ∂μ, ∀ (Λ : Finset S) (t : Finset ℕ),
      ((condExpKernel μ (invariantEvents Θ) ω).bind (γ Λ)) (piNatGen (Ω := S → E) t) =
        condExpKernel μ (invariantEvents Θ) ω (piNatGen t) :=
    ae_all_iff.2 fun Λ ↦ ae_all_iff.2 fun t ↦
      ae_bind_condExpKernel_invariantEvents_apply_eq hΘ hμ Λ (measurableSet_piNatGen t)
  filter_upwards [h] with ω hω
  exact ⟨measure_univ, hω⟩

variable {π : Kernel[invariantEvents Θ] (S → E) (S → E)} [IsMarkovKernel π]
  (hπ : IsPAKernel (invariantFields Θ) (invariantEvents Θ) π)

include hπ

omit [Countable Θ] in
/-- **Georgii, Theorem (14.17), key step**: any `(𝓟_Θ, 𝓘)`-kernel takes Gibbs values at
`μ`-almost every `ω`, for every `μ ∈ 𝒢_Θ(γ)`. -/
theorem ae_mem_G_of_isPAKernel_invariantFields {μ : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) :
    ∀ᵐ ω ∂μ, π ω ∈ G γ := by
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  filter_upwards [hπ.ae_eq_condExpKernel MeasurableSpace.smulInvariants_le hμ.2,
    ae_isGibbsCore_condExpKernel_invariantEvents hΘ hμ] with ω h1 h2
  rw [h1]
  exact (G.mem_iff _).2 ⟨⟨h2.1⟩, isGibbsMeasure_of_isGibbsCore γ h2⟩

omit [Countable Θ] in
/-- **Georgii, Theorem (14.17)**, pointwise form: "any `(𝓟_Θ, 𝓘)`-kernel is also a
`(𝒢_Θ(γ), 𝓘)`-kernel": `π(· | ω) ∈ 𝒢_Θ(γ)` for `μ`-a.e. `ω`, `μ ∈ 𝒢_Θ(γ)`. -/
theorem ae_mem_invariantG_of_isPAKernel_invariantFields {μ : Measure (S → E)}
    (hμ : μ ∈ invariantG γ Θ) : ∀ᵐ ω ∂μ, π ω ∈ invariantG γ Θ := by
  filter_upwards [ae_mem_G_of_isPAKernel_invariantFields hΘ hπ hμ] with ω h
  exact ⟨h, hπ.2 ω⟩

/-- **Georgii, Theorem (14.17)**: for `μ ∈ 𝒢_Θ(γ)`, the representing weight `w_μ` of
Theorem (14.10) is supported on `ex 𝒢_Θ(γ)`. -/
theorem weight_extremePoints_invariantG_compl {μ : Measure (S → E)} (hμ : μ ∈ invariantG γ Θ) :
    weight π μ ((invariantG γ Θ).extremePoints ℝ≥0∞)ᶜ = 0 := by
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  have hle : invariantEvents Θ ≤ MeasurableSpace.pi := MeasurableSpace.smulInvariants_le
  rw [extremePoints_invariantG hΘ]
  have hmeas : MeasurableSet (invariantG γ Θ ∩ (invariantFields Θ).extremePoints ℝ≥0∞) :=
    ((measurableSet_G γ).inter measurableSet_invariantFields).inter
      (hπ.measurableSet_extremePoints hle (fun _ ↦ isProbabilityMeasure_of_mem_invariantFields)
        measurableSet_invariantFields extremePoints_invariantFields_eq_inter_trivialOn)
  rw [weight_apply hle μ hmeas.compl]
  refine ae_iff.1 ?_
  filter_upwards [ae_mem_invariantG_of_isPAKernel_invariantFields hΘ hπ hμ,
    hπ.ae_mem_extremePoints hle (fun _ ↦ isProbabilityMeasure_of_mem_invariantFields)
      measurableSet_invariantFields extremePoints_invariantFields_eq_inter_trivialOn hμ.2]
    with ω h1 h2
  exact ⟨h1, h2⟩

omit hΘ hπ in
variable (γ π) in
/-- The `(𝓟_Θ, 𝓘)`-kernel `π`, normalised to take its values in `𝒢_Θ(γ)`: it is replaced by a
fixed `ν₀` on the invariant event `{ω | π(· | ω) ∉ 𝒢(γ)}`. -/
noncomputable def invariantGibbsKernel (ν₀ : Measure (S → E)) :
    Kernel[invariantEvents Θ] (S → E) (S → E) :=
  open Classical in
  Kernel.piecewise (s := {ω | π ω ∈ G γ}) ((measurableSet_G γ).preimage π.measurable) π
    (@Kernel.const (S → E) (S → E) (invariantEvents Θ) _ ν₀)

omit hΘ hπ in
instance {ν₀ : Measure (S → E)} [IsProbabilityMeasure ν₀] :
    IsMarkovKernel (invariantGibbsKernel γ π ν₀) := by
  unfold invariantGibbsKernel; infer_instance

omit hΘ hπ [Countable Θ] [IsMarkovKernel π] in
lemma invariantGibbsKernel_apply_of_mem {ν₀ : Measure (S → E)} {ω : S → E} (h : π ω ∈ G γ) :
    invariantGibbsKernel γ π ν₀ ω = π ω := by
  classical
  rw [invariantGibbsKernel, Kernel.piecewise_apply, ite_eq_left (show ω ∈ {ω | π ω ∈ G γ} from h)]

omit [Countable Θ] in
/-- The normalised kernel is a `(𝒢_Θ(γ), 𝓘)`-kernel, for any `ν₀ ∈ 𝒢_Θ(γ)`. -/
theorem isPAKernel_invariantGibbsKernel {ν₀ : Measure (S → E)} (hν₀ : ν₀ ∈ invariantG γ Θ) :
    IsPAKernel (invariantG γ Θ) (invariantEvents Θ) (invariantGibbsKernel γ π ν₀) := by
  classical
  refine ⟨fun μ hμ A hA ↦ ?_, fun ω ↦ ?_⟩
  · have hprob : IsProbabilityMeasure μ := hμ.1.1
    filter_upwards [hπ.1 μ hμ.2 A hA, ae_mem_G_of_isPAKernel_invariantFields hΘ hπ hμ]
      with ω h1 h2
    rw [invariantGibbsKernel_apply_of_mem h2]
    exact h1
  · rw [invariantGibbsKernel, Kernel.piecewise_apply]
    split_ifs with h
    · exact ⟨h, hπ.2 ω⟩
    · rw [Kernel.const_apply]; exact hν₀

omit [Countable Θ] in
/-- The normalised kernel has the same weights as `π` on `𝒢_Θ(γ)`. -/
lemma weight_invariantGibbsKernel {ν₀ : Measure (S → E)} {μ : Measure (S → E)}
    (hμ : μ ∈ invariantG γ Θ) : weight (invariantGibbsKernel γ π ν₀) μ = weight π μ :=
  Measure.map_congr ((ae_mem_G_of_isPAKernel_invariantFields hΘ hπ hμ).mono fun _ h ↦
    invariantGibbsKernel_apply_of_mem h)

omit hπ [StandardBorelSpace E] in
/-- **Georgii, Theorem (14.15)(a)**, set form: `ex 𝒢_Θ(γ) = 𝒢_Θ(γ) ∩ P_𝓘`. -/
lemma extremePoints_invariantG_eq_inter_trivialOn :
    (invariantG γ Θ).extremePoints ℝ≥0∞ = invariantG γ Θ ∩ trivialOn (invariantEvents Θ) := by
  ext μ
  exact ⟨fun h ↦ ⟨extremePoints_subset h,
      (mem_extremePoints_invariantG_iff_mem_trivialOn hΘ (extremePoints_subset h)).1 h⟩,
    fun h ↦ (mem_extremePoints_invariantG_iff_mem_trivialOn hΘ h.1).2 h.2⟩

omit hΘ hπ in
/-- `𝒢_Θ(γ)` is measurable in `Measure (S → E)`. -/
lemma measurableSet_invariantG : MeasurableSet (invariantG γ Θ) :=
  (measurableSet_G γ).inter measurableSet_invariantFields

omit hΘ hπ in
/-- The barycentre of a probability weight carried by `𝒢_Θ(γ)` lies in `𝒢_Θ(γ)`. -/
lemma join_mem_invariantG (w : Measure (Measure (S → E))) [IsProbabilityMeasure w]
    (hw : w (invariantG γ Θ)ᶜ = 0) : Measure.join w ∈ invariantG γ Θ :=
  ⟨join_mem_G w (measure_mono_null (compl_subset_compl.2 inter_subset_left) hw),
    join_mem_invariantFields w (measure_mono_null (compl_subset_compl.2 inter_subset_right) hw)⟩

/-- **Georgii, Theorem (14.17)**, decomposition form: every `μ ∈ 𝒢_Θ(γ)` has a unique extreme
decomposition within `𝒢_Θ(γ)`, `μ = ∫_{ex 𝒢_Θ(γ)} ν w_μ(dν)`, with `w_μ = weight π μ` the weight
of Theorem (14.10); and `μ ↦ w_μ` is an affine bijection from `𝒢_Θ(γ)` onto the probability
weights carried by `ex 𝒢_Θ(γ)`. -/
theorem ergodicDecomposition_invariantG (hne : (invariantG γ Θ).Nonempty) :
    ((invariantG γ Θ).extremePoints ℝ≥0∞).Nonempty ∧
    (∀ μ ∈ invariantG γ Θ, ∃! w : Measure (Measure (S → E)), IsProbabilityMeasure w ∧
      w ((invariantG γ Θ).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ) ∧
    (∀ μ ∈ invariantG γ Θ, IsProbabilityMeasure (weight π μ) ∧
      weight π μ ((invariantG γ Θ).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join (weight π μ) = μ) ∧
    BijOn (weight π) (invariantG γ Θ) {w : Measure (Measure (S → E)) |
      IsProbabilityMeasure w ∧ w ((invariantG γ Θ).extremePoints ℝ≥0∞)ᶜ = 0} := by
  obtain ⟨ν₀, hν₀⟩ := hne
  have := hν₀.1.1
  have hle : invariantEvents Θ ≤ MeasurableSpace.pi := MeasurableSpace.smulInvariants_le
  have hP : ∀ μ ∈ invariantG γ Θ, IsProbabilityMeasure μ := fun _ (h : _ ∈ invariantG γ Θ) ↦ h.1.1
  have hπ' := isPAKernel_invariantGibbsKernel hΘ hπ hν₀
  have hex := extremePoints_invariantG_eq_inter_trivialOn (γ := γ) hΘ
  refine ⟨hπ'.nonempty_extremePoints hle hP hex ⟨ν₀, hν₀⟩,
    fun μ hμ ↦ hπ'.exists_unique_weight_extremePoints hle hP measurableSet_invariantG hex hμ,
    fun μ hμ ↦ ?_, ?_⟩
  · have := hμ.1.1
    exact ⟨isProbabilityMeasure_weight hle μ, weight_extremePoints_invariantG_compl hΘ hπ hμ,
      hπ.join_weight hle hμ.2⟩
  · have hbij := hπ'.bijOn_weight hle hP measurableSet_invariantG hex fun w hw hw' ↦
      join_mem_invariantG w (measure_mono_null (compl_subset_compl.2 extremePoints_subset) hw')
    refine hbij.congr fun μ hμ ↦ weight_invariantGibbsKernel hΘ hπ hμ

/-! #### Georgii (14.18): linear independence in `𝒢_Θ(γ)` counts `ex 𝒢_Θ(γ)` -/

/-- **Georgii, Corollary (14.18)**: `|ex 𝒢_Θ(γ)| ≥ N` iff `𝒢_Θ(γ)` contains `N` linearly
independent elements. -/
theorem le_encard_extremePoints_invariantG_iff (N : ℕ) :
    (N : ℕ∞) ≤ ((invariantG γ Θ).extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure (S → E), (∀ i, μ i ∈ invariantG γ Θ) ∧ LinearIndependent ℝ≥0∞ μ := by
  rcases (invariantG γ Θ).eq_empty_or_nonempty with h | ⟨ν₀, hν₀⟩
  · rw [h, extremePoints_empty, encard_empty]
    constructor
    · intro hN
      have hN0 : N = 0 := by exact_mod_cast nonpos_iff_eq_zero.1 hN
      subst hN0
      exact ⟨Fin.elim0, fun i ↦ i.elim0, linearIndependent_empty_type⟩
    · rintro ⟨μ, hμ, -⟩
      cases N with
      | zero => simp
      | succ n => exact absurd (hμ 0) id
  · have := hν₀.1.1
    exact (isPAKernel_invariantGibbsKernel hΘ hπ hν₀).le_encard_extremePoints_iff
      MeasurableSpace.smulInvariants_le (fun _ (h : _ ∈ invariantG γ Θ) ↦ h.1.1)
      measurableSet_invariantG
      (extremePoints_invariantG_eq_inter_trivialOn hΘ) N

end Thm1417

/-! ### Georgii (14.25): the closed convex hull of the averaged limiting Gibbs measures -/

section Corollary1425

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]

variable {γ : Specification S E} {Θ : Subgroup (Transformation S E)} [Countable Θ]

omit [Countable S] [StandardBorelSpace E] [Countable Θ] in
/-- `𝒢_Θ(γ)` is closed in the topology of local convergence for a quasilocal `γ` (Georgii,
remark after (5.12)). -/
lemma isClosed_setOf_mem_invariantG (hγ : γ.IsQuasilocal) :
    IsClosed {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ} := by
  have h := isClosed_setOf_mem_GP_and_measurePreserving hγ (Θ : Set (Transformation S E))
  convert h using 1
  ext μ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hG, hinv⟩
    exact ⟨((G.mem_iff _).1 hG).2, (mem_invariantFields_iff.1 hinv).2⟩
  · rintro ⟨hG, hinv⟩
    exact ⟨(G.mem_iff _).2 ⟨inferInstance, hG⟩, mem_invariantFields_iff.2 ⟨inferInstance, hinv⟩⟩

/-- Finite convex combinations of elements of `𝒢_Θ(γ)` lie in `𝒢_Θ(γ)`. -/
lemma convexCombos_subset_setOf_mem_invariantG {L : Set (WithLocalConvergence S E)}
    (hL : L ⊆ {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ}) :
    convexCombos L ⊆
      {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ} := by
  rintro μ ⟨n, c, ν, hν, hc, hμeq⟩
  change (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ
  rw [hμeq, ← join_finset_sum_smul_dirac]
  have hw : IsProbabilityMeasure
      (∑ i, c i • Measure.dirac ((ν i).toMeasure : Measure (S → E))) :=
    isProbabilityMeasure_sum_smul (fun _ ↦ inferInstance) hc
  refine join_mem_invariantG _ ?_
  rw [Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hνi : ((ν i).toMeasure : Measure (S → E)) ∉ (invariantG γ Θ)ᶜ :=
    Set.notMem_compl_iff.2 (hL (hν i))
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_invariantG.compl,
    Set.indicator_of_notMem hνi, smul_zero]

/-- **Georgii, Corollary (14.25)**, conditional form. Let `γ` be a quasilocal specification and
`Θ` a countable subgroup of `T` moving every finite volume off itself, with a `(𝓟_Θ, 𝓘)`-kernel
`π` (Theorem (14.10)). If `L` is a set of `Θ`-invariant Gibbs measures containing every extreme
point of `𝒢_Θ(γ)` — Georgii's `𝒢_{Θ,lim}(γ)`, by Theorem (14.20) — then `𝒢_Θ(γ)` is the closed
convex hull of `L` in the topology of local convergence. -/
theorem setOf_mem_invariantG_eq_closure_convexCombos (hγ : γ.IsQuasilocal)
    (hΘ : ∀ Λ : Finset S, ∃ τ ∈ Θ, Disjoint (τ.sites ⁻¹' (Λ : Set S)) (Λ : Set S))
    {π : Kernel[invariantEvents Θ] (S → E) (S → E)} [IsMarkovKernel π]
    (hπ : IsPAKernel (invariantFields Θ) (invariantEvents Θ) π)
    {L : Set (WithLocalConvergence S E)}
    (hL : L ⊆ {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ})
    (hlim : ∀ μ : ProbabilityMeasure (S → E),
      (μ : Measure (S → E)) ∈ (invariantG γ Θ).extremePoints ℝ≥0∞ →
        (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ L) :
    {μ : WithLocalConvergence S E | (μ.toMeasure : Measure (S → E)) ∈ invariantG γ Θ} =
      closure (convexCombos L) := by
  refine Subset.antisymm ?_
    (closure_minimal (convexCombos_subset_setOf_mem_invariantG hL)
      (isClosed_setOf_mem_invariantG hγ))
  rcases (invariantG γ Θ).eq_empty_or_nonempty with h | ⟨ν₀, hν₀⟩
  · intro μ hμ
    exact absurd (h ▸ hμ) (Set.notMem_empty _)
  · have := hν₀.1.1
    exact (isPAKernel_invariantGibbsKernel hΘ hπ hν₀).setOf_mem_subset_closure_convexCombos
      MeasurableSpace.smulInvariants_le (fun _ (h : _ ∈ invariantG γ Θ) ↦ h.1.1)
      measurableSet_invariantG (extremePoints_invariantG_eq_inter_trivialOn hΘ)
      (fun _ hA ↦ MeasurableSet.of_mem_measurableCylinders hA) hlim

end Corollary1425

/-! ### The shift group: Georgii's setting -/

section ShiftGroupCorollaries

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [Countable S] [Infinite S]
  [DecidableEq S] [StandardBorelSpace E] {γ : Specification S E} {F : ℕ → Finset S}
  (hFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
  {C : ℝ≥0∞} (hF : Monotone F) (hne : (F 0).Nonempty)
  (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)

include hFol hF hne hC hC'

/-- **Georgii, Theorem (14.17) for the shift group**: for an infinite countable abelian site
group with an increasing regular Følner sequence and a standard Borel state space, every
`μ ∈ 𝒢_Θ(γ)` has a unique extreme decomposition within `𝒢_Θ(γ)`, governed by a
`(𝓟_Θ, 𝓘)`-kernel. -/
theorem ergodicDecomposition_invariantG_shiftGroup
    (hne' : (invariantG γ (shiftGroup S E)).Nonempty) :
    ∃ π : Kernel[invariantEvents (shiftGroup S E)] (S → E) (S → E), IsMarkovKernel π ∧
      IsPAKernel (invariantFields (shiftGroup S E)) (invariantEvents (shiftGroup S E)) π ∧
      (∀ μ ∈ invariantG γ (shiftGroup S E), ∀ᵐ ω ∂μ, π ω ∈ invariantG γ (shiftGroup S E)) ∧
      ((invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞).Nonempty ∧
      (∀ μ ∈ invariantG γ (shiftGroup S E), ∃! w : Measure (Measure (S → E)),
        IsProbabilityMeasure w ∧
          w ((invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ) ∧
      (∀ μ ∈ invariantG γ (shiftGroup S E), IsProbabilityMeasure (weight π μ) ∧
        weight π μ ((invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞)ᶜ = 0 ∧
          Measure.join (weight π μ) = μ) := by
  obtain ⟨π, hMarkov, hπ⟩ := exists_isPAKernel_invariantFields_shiftGroup hFol hF hne hC hC'
    ⟨hne'.some, hne'.some_mem.2⟩
  have hΘ := shiftGroup_exists_disjoint_sites_preimage (E := E) (S := S)
  obtain ⟨h1, h2, h3, -⟩ := ergodicDecomposition_invariantG hΘ hπ hne'
  exact ⟨π, hMarkov, hπ, fun μ hμ ↦ ae_mem_invariantG_of_isPAKernel_invariantFields hΘ hπ hμ,
    h1, h2, h3⟩

/-- **Georgii, Corollary (14.18) for the shift group**: `|ex 𝒢_Θ(γ)| ≥ N` iff `𝒢_Θ(γ)` contains
`N` linearly independent elements. -/
theorem le_encard_extremePoints_invariantG_shiftGroup_iff (N : ℕ) :
    (N : ℕ∞) ≤ ((invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure (S → E),
        (∀ i, μ i ∈ invariantG γ (shiftGroup S E)) ∧ LinearIndependent ℝ≥0∞ μ := by
  rcases (invariantG γ (shiftGroup S E)).eq_empty_or_nonempty with h | hne'
  · rw [h, extremePoints_empty, encard_empty]
    constructor
    · intro hN
      have hN0 : N = 0 := by exact_mod_cast nonpos_iff_eq_zero.1 hN
      subst hN0
      exact ⟨Fin.elim0, fun i ↦ i.elim0, linearIndependent_empty_type⟩
    · rintro ⟨μ, hμ, -⟩
      cases N with
      | zero => simp
      | succ n => exact absurd (hμ 0) id
  · obtain ⟨π, hMarkov, hπ⟩ := exists_isPAKernel_invariantFields_shiftGroup hFol hF hne hC hC'
      ⟨hne'.some, hne'.some_mem.2⟩
    exact le_encard_extremePoints_invariantG_iff
      (shiftGroup_exists_disjoint_sites_preimage (E := E) (S := S)) hπ N

/-- **Georgii, Corollary (14.25) for the shift group**, conditional form: for a quasilocal
`γ` and a set `L ⊆ 𝒢_Θ(γ)` containing `ex 𝒢_Θ(γ)` (Georgii's `𝒢_{Θ,lim}(γ)`, by Theorem (14.20)),
`𝒢_Θ(γ)` is the closed convex hull of `L` in the topology of local convergence. -/
theorem setOf_mem_invariantG_shiftGroup_eq_closure_convexCombos (hγ : γ.IsQuasilocal)
    {L : Set (WithLocalConvergence S E)}
    (hL : L ⊆ {μ : WithLocalConvergence S E |
      (μ.toMeasure : Measure (S → E)) ∈ invariantG γ (shiftGroup S E)})
    (hlim : ∀ μ : ProbabilityMeasure (S → E),
      (μ : Measure (S → E)) ∈ (invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞ →
        (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ L) :
    {μ : WithLocalConvergence S E |
      (μ.toMeasure : Measure (S → E)) ∈ invariantG γ (shiftGroup S E)} =
      closure (convexCombos L) := by
  rcases (invariantG γ (shiftGroup S E)).eq_empty_or_nonempty with h | hne'
  · refine Subset.antisymm ?_ (closure_minimal (convexCombos_subset_setOf_mem_invariantG hL)
      (isClosed_setOf_mem_invariantG hγ))
    intro μ hμ
    exact absurd (h ▸ hμ) (Set.notMem_empty _)
  · obtain ⟨π, hMarkov, hπ⟩ := exists_isPAKernel_invariantFields_shiftGroup hFol hF hne hC hC'
      ⟨hne'.some, hne'.some_mem.2⟩
    exact setOf_mem_invariantG_eq_closure_convexCombos hγ
      (shiftGroup_exists_disjoint_sites_preimage (E := E) (S := S)) hπ hL hlim

end ShiftGroupCorollaries

end MeasureTheory.GibbsMeasure

end

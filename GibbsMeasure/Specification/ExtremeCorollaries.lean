/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ExtremeDecomposition
public import GibbsMeasure.Specification.LocalLimits
public import GibbsMeasure.Specification.Transformation
public import GibbsMeasure.Specification.UniformLocalLimits

/-!
# Georgii, Corollaries (7.28), (7.29) and (7.30)

Complements to the extreme decomposition theorem (7.26) for a specification `γ` on `S → E`
(`S` countable, `E` standard Borel). As in `ExtremeDecomposition.lean`, (7.28), (7.29) and the
density step of (7.30) are the instance `P = G(γ)`, `𝒜 = 𝓣` of the abstract statements in
`GibbsMeasure/Specification/PAKernel.lean` (namespace `IsPAKernel`).

* **(7.7)(c)**: each `μ ∈ G(γ)` is uniquely determined within `G(γ)` by its restriction to the
  tail σ-algebra `𝓣` (`eq_of_forall_measurableSet_tail_eq`); this and **(7.7)(d)** — distinct
  extreme Gibbs measures are separated by a tail event, hence mutually singular — hold for an
  arbitrary state space `E`, without the standard Borel assumption of §7.3.
* **(7.28)**: the weight map `μ ↦ w_μ` commutes with every symmetry `τ` of `γ`:
  `w_{τ(μ)} = τ(w_μ)`; in particular `μ` is `τ`-invariant iff `w_μ` is.
* **(7.29)**: `|ex G(γ)| ≥ N` iff `G(γ)` contains `N` linearly independent measures.
* **(7.30)**: `G(γ)` is the closed convex hull of the limiting Gibbs measures `G_lim(γ)` in the
  topology of local convergence, at Georgii's own hypotheses — a standard Borel state space and a
  quasilocal λ-specification `γ = ρ λ_·`. Two readings of Definition (1.27), made one by
  Remark (1.28)(3): `setOf_mem_GP_eq_closure_convexCombosLimitGibbs_modification_isssd` for an
  arbitrary λ-modification `ρ` over a probability a priori measure, and
  `setOf_mem_GP_eq_closure_convexCombosLimitGibbs_lambdaSpecification` for a normalized
  pre-modification over an arbitrary σ-finite non-zero `λ ∈ 𝓜(E, ℰ)`. For an arbitrary quasilocal
  specification over a finite state space it is
  `setOf_mem_GP_eq_closure_convexCombosLimitGibbs`. All three follow from the density step
  `setOf_mem_GP_subset_closure_convexCombosLimitGibbs`, which needs only `ex G(γ) ⊆ G_lim(γ)` —
  Theorem (7.12)(c), supplied over a finite state space by
  `ofMeasure_mem_limitGibbs_of_mem_extremePoints_G`, and for a λ-specification over *any* state
  space by the uniform total-variation form of (7.12)(c)
  (`ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G`) via
  `ofMeasure_mem_limitGibbs_modification_isssd`.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii (7.7)(c)–(d): tail determinacy and mutual singularity

Georgii states Theorem (7.7) for an arbitrary specification over an arbitrary state space, so
this section assumes only `[Countable S]` — no `[StandardBorelSpace E]`. Part (c) follows from
(7.7)(b) (`ae_eq_tailMeasurable_of_forall_boundary`) applied to the mixture `(μ + ν) / 2`, and
part (d) is immediate from (a) (`tailTrivial_of_mem_extremePoints_G`) and (c). -/

section Theorem77

variable {S E : Type*} [MeasurableSpace E] [Countable S] {γ : Specification S E}

local notation3 (prettyPrint := false) "Ω" => (S → E)

/-- **Georgii, Theorem (7.7)(c)**: each `μ ∈ G(γ)` is uniquely determined within `G(γ)` by its
restriction to the tail σ-algebra `𝓣`. -/
theorem eq_of_forall_measurableSet_tail_eq {μ ν : Measure Ω} (hμ : μ ∈ G γ) (hν : ν ∈ G γ)
    (h : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = ν A) : μ = ν := by
  have hμp : IsProbabilityMeasure μ := hμ.1
  have hνp : IsProbabilityMeasure ν := hν.1
  set ρ : Measure Ω := (2⁻¹ : ℝ≥0∞) • μ + (2⁻¹ : ℝ≥0∞) • ν with hρdef
  have hρG : ρ ∈ G γ := add_smul_mem_G hμ hν ENNReal.inv_two_add_inv_two
  have hρp : IsProbabilityMeasure ρ := hρG.1
  have hhalf : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have hμρ : μ ≪ ρ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
    simp only [hρdef, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 (add_eq_zero.1 h0).1).resolve_left hhalf
  have hνρ : ν ≪ ρ := by
    refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
    simp only [hρdef, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 (add_eq_zero.1 h0).2).resolve_left hhalf
  obtain ⟨f, hf_tail, hμf⟩ :=
    ae_eq_tailMeasurable_of_forall_boundary (S := S) (E := E) (γ := γ) hρG.2 hμ.2 hμρ
  obtain ⟨g, hg_tail, hνg⟩ :=
    ae_eq_tailMeasurable_of_forall_boundary (S := S) (E := E) (γ := γ) hρG.2 hν.2 hνρ
  have : μ.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite μ ρ
  have : ν.HaveLebesgueDecomposition ρ := Measure.haveLebesgueDecomposition_of_sigmaFinite ν ρ
  have hμ_repr : ρ.withDensity f = μ := by
    rw [← withDensity_congr_ae hμf]
    exact Measure.withDensity_rnDeriv_eq μ ρ hμρ
  have hν_repr : ρ.withDensity g = ν := by
    rw [← withDensity_congr_ae hνg]
    exact Measure.withDensity_rnDeriv_eq ν ρ hνρ
  have hm := tailSigmaAlgebra_le_pi (S := S) (E := E)
  have htrim : μ.trim hm = ν.trim hm :=
    @Measure.ext _ (@tailSigmaAlgebra S E _) _ _ fun A hA ↦ by
      rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
      exact h A hA
  have hfg_trim : f =ᵐ[ρ.trim hm] g := by
    have h1 : (ρ.trim hm).withDensity f = (ρ.trim hm).withDensity g := by
      rw [← trim_withDensity hm hf_tail, ← trim_withDensity hm hg_tail, hμ_repr, hν_repr, htrim]
    exact (withDensity_eq_iff_of_sigmaFinite hf_tail.aemeasurable hg_tail.aemeasurable).1 h1
  have hfg : f =ᵐ[ρ] g := ae_of_ae_trim hm hfg_trim
  calc μ = ρ.withDensity f := hμ_repr.symm
    _ = ρ.withDensity g := withDensity_congr_ae hfg
    _ = ν := hν_repr

/-- **Georgii, Theorem (7.7)(d)**, tail form: distinct extreme Gibbs measures are separated by a
*tail* event — they are mutually singular on `𝓣`, not merely on the product σ-algebra. -/
theorem exists_tail_eq_one_eq_zero_of_mem_extremePoints {μ ν : Measure Ω}
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) (hν : ν ∈ (G γ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    ∃ A, MeasurableSet[@tailSigmaAlgebra S E _] A ∧ μ A = 1 ∧ ν A = 0 := by
  have hμG : μ ∈ G γ := extremePoints_subset hμ
  have hνG : ν ∈ G γ := extremePoints_subset hν
  have hμp : IsProbabilityMeasure μ := hμG.1
  have hνp : IsProbabilityMeasure ν := hνG.1
  obtain ⟨A, hA, hAne⟩ : ∃ A, MeasurableSet[@tailSigmaAlgebra S E _] A ∧ μ A ≠ ν A := by
    by_contra hall
    push Not at hall
    exact hne (eq_of_forall_measurableSet_tail_eq hμG hνG hall)
  rcases tailTrivial_of_mem_extremePoints_G (γ := γ) hμ A hA with hμ0 | hμ1
  · rcases tailTrivial_of_mem_extremePoints_G (γ := γ) hν A hA with hν0 | hν1
    · exact absurd (hμ0.trans hν0.symm) hAne
    · exact ⟨Aᶜ, hA.compl, (prob_compl_eq_one_iff (measurableSet_of_measurableSet_tail hA)).2 hμ0,
        (prob_compl_eq_zero_iff (measurableSet_of_measurableSet_tail hA)).2 hν1⟩
  · rcases tailTrivial_of_mem_extremePoints_G (γ := γ) hν A hA with hν0 | hν1
    · exact ⟨A, hA, hμ1, hν0⟩
    · exact absurd (hμ1.trans hν1.symm) hAne

/-- **Georgii, Theorem (7.7)(d)**: distinct extreme Gibbs measures are mutually singular. -/
theorem mutuallySingular_of_mem_extremePoints {μ ν : Measure Ω}
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) (hν : ν ∈ (G γ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    μ.MutuallySingular ν := by
  obtain ⟨A, hA, hμA, hνA⟩ := exists_tail_eq_one_eq_zero_of_mem_extremePoints hμ hν hne
  have : IsProbabilityMeasure μ := (extremePoints_subset hμ).1
  refine ⟨Aᶜ, (measurableSet_of_measurableSet_tail hA).compl, ?_, ?_⟩
  · exact (prob_compl_eq_zero_iff (measurableSet_of_measurableSet_tail hA)).2 hμA
  · rwa [compl_compl]

end Theorem77

/-! ### Symmetries act on `G(γ)` and `ex G(γ)` -/

section Symmetry

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  {γ : Specification S E}

local notation3 (prettyPrint := false) "Ω" => (S → E)

omit [Countable S] [StandardBorelSpace E] in
/-- **Georgii (5.10)**, `Measure` form: a symmetry of `γ` maps `G(γ)` into itself. -/
lemma map_mem_G {τ : Transformation S E} (hτ : Specification.IsInvariant τ γ)
    {μ : Measure Ω} (hμ : μ ∈ G γ) : μ.map τ.toFun ∈ G γ := by
  obtain ⟨hprob, hgibbs⟩ := (G.mem_iff μ).1 hμ
  have h2 := hτ.map_mem_GP (show (⟨μ, hprob⟩ : ProbabilityMeasure Ω) ∈ GP γ from hgibbs)
  have h3 : Specification.IsGibbsMeasure γ
      ((ProbabilityMeasure.map (⟨μ, hprob⟩ : ProbabilityMeasure Ω)
        τ.measurable_toFun.aemeasurable : ProbabilityMeasure Ω) : Measure Ω) := h2
  have hmeq : ((ProbabilityMeasure.map (⟨μ, hprob⟩ : ProbabilityMeasure Ω)
      τ.measurable_toFun.aemeasurable : ProbabilityMeasure Ω) : Measure Ω) =
      μ.map τ.toFun :=
    ProbabilityMeasure.toMeasure_map (⟨μ, hprob⟩ : ProbabilityMeasure Ω)
      τ.measurable_toFun.aemeasurable
  exact ⟨Measure.isProbabilityMeasure_map τ.measurable_toFun.aemeasurable, hmeq ▸ h3⟩

omit [Countable S] [StandardBorelSpace E] in
/-- A symmetry of `γ` maps extreme Gibbs measures to extreme Gibbs measures. -/
lemma map_mem_extremePoints_G {τ : Transformation S E} (hτ : Specification.IsInvariant τ γ)
    {μ : Measure Ω} (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) :
    μ.map τ.toFun ∈ (G γ).extremePoints ℝ≥0∞ := by
  rw [mem_extremePoints] at hμ ⊢
  obtain ⟨hμG, hext⟩ := hμ
  have hcompinv : τ.inv.toFun ∘ τ.toFun = id := funext fun ω ↦ τ.inv_toFun_toFun ω
  have hcomp : τ.toFun ∘ τ.inv.toFun = id := funext fun ω ↦ τ.toFun_inv_toFun ω
  refine ⟨map_mem_G hτ hμG, ?_⟩
  rintro x hx y hy ⟨a, b, ha, hb, hab, heq⟩
  have hμeq : (μ.map τ.toFun).map τ.inv.toFun = μ := by
    rw [Measure.map_map τ.inv.measurable_toFun τ.measurable_toFun, hcompinv, Measure.map_id]
  have hseg : a • x.map τ.inv.toFun + b • y.map τ.inv.toFun = μ := by
    rw [← Measure.map_smul, ← Measure.map_smul,
      ← Measure.map_add _ _ τ.inv.measurable_toFun, heq, hμeq]
  obtain ⟨hxeq, hyeq⟩ := hext _ (map_mem_G hτ.inv hx) _ (map_mem_G hτ.inv hy)
    ⟨a, b, ha, hb, hab, hseg⟩
  constructor
  · have := congrArg (Measure.map τ.toFun) hxeq
    rwa [Measure.map_map τ.measurable_toFun τ.inv.measurable_toFun, hcomp, Measure.map_id] at this
  · have := congrArg (Measure.map τ.toFun) hyeq
    rwa [Measure.map_map τ.measurable_toFun τ.inv.measurable_toFun, hcomp, Measure.map_id] at this

/-- `ex G(γ)` is measurable in `Measure (S → E)`: it agrees with `G(γ) ∩ fixedCore π` for the
`(G(γ), 𝓣)`-kernel `π`. -/
lemma measurableSet_extremePoints_G (hG : (G γ).Nonempty) :
    MeasurableSet ((G γ).extremePoints ℝ≥0∞) :=
  (isPAKernel_gibbsKernel_some hG).measurableSet_extremePoints
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ)

/-- **Georgii (7.26), pointwise form.** For a Gibbs measure `μ`, the `(𝒢(γ), 𝓣)`-kernel of
Proposition (7.25) takes an *extreme* Gibbs measure as value at `μ`-almost every boundary
condition.

This is the conclusion that the tail-kernel statements of
`GibbsMeasure/Specification/ErgodicDecomposition.lean` reach for, and unlike those it assumes no
countable generation of the tail σ-algebra — a hypothesis which is unsatisfiable for countably
infinite `S` and `2 ≤ #E`. The kernel here is `gibbsKernel γ ν₀`, which is a version of
`μ(· | 𝓣)` for *every* `μ ∈ 𝒢(γ)` at once (`isPAKernel_gibbsKernel`), so nothing is lost by using
it in place of the conditional-expectation kernel. -/
theorem ae_mem_extremePoints_G_gibbsKernel (hG : (G γ).Nonempty) {μ : Measure Ω}
    (hμ : μ ∈ G γ) :
    ∀ᵐ ω ∂μ, gibbsKernel γ hG.some ω ∈ (G γ).extremePoints ℝ≥0∞ :=
  (isPAKernel_gibbsKernel_some hG).ae_mem_extremePoints
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) hμ

/-! ### Georgii (7.28): the weight map commutes with every symmetry -/

/-- **Georgii, Corollary (7.28)**: for a symmetry `τ` of `γ`, `w_{τ(μ)} = τ(w_μ)`. -/
theorem weightOf_map (hG : (G γ).Nonempty) {τ : Transformation S E}
    (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    weightOf hG (μ.map τ.toFun) = (weightOf hG μ).map (Measure.map τ.toFun) :=
  (isPAKernel_gibbsKernel_some hG).weight_map
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) τ.measurable_toFun
    (fun _ hν ↦ map_mem_extremePoints_G hτ hν) hμ

/-- **Georgii, Corollary (7.28)**, second half: `μ ∈ G(γ)` is `τ`-invariant iff its weight
`w_μ` is invariant under `ν ↦ τ(ν)`. -/
theorem map_eq_self_iff_weightOf_map_eq_self (hG : (G γ).Nonempty) {τ : Transformation S E}
    (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    μ.map τ.toFun = μ ↔ (weightOf hG μ).map (Measure.map τ.toFun) = weightOf hG μ :=
  (isPAKernel_gibbsKernel_some hG).map_eq_self_iff_weight_map_eq_self
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) τ.measurable_toFun
    (fun _ hν ↦ map_mem_extremePoints_G hτ hν) hμ

/-- Georgii (7.28): `τ` preserves `μ ∈ G(γ)` iff `ν ↦ τ(ν)` preserves the weight `w_μ`. -/
theorem measurePreserving_iff_measurePreserving_weightOf (hG : (G γ).Nonempty)
    {τ : Transformation S E} (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω}
    (hμ : μ ∈ G γ) :
    MeasurePreserving τ.toFun μ μ ↔
      MeasurePreserving (Measure.map τ.toFun) (weightOf hG μ) (weightOf hG μ) :=
  (isPAKernel_gibbsKernel_some hG).measurePreserving_iff_measurePreserving_weight
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) τ.measurable_toFun
    (fun _ hν ↦ map_mem_extremePoints_G hτ hν) hμ

end Symmetry

/-! ### Georgii (7.29): linear dimension of `G(γ)` counts the extreme points -/

section Corollary729

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  {γ : Specification S E}

local notation3 (prettyPrint := false) "Ω" => (S → E)

/-- An extreme Gibbs measure gives full mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_gibbsKernel_eq_self (hG : (G γ).Nonempty) {μ : Measure Ω}
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) :
    μ {ω | gibbsKernel γ hG.some ω = μ} = 1 :=
  (isPAKernel_gibbsKernel_some hG).measure_kernel_eq_self
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) hμ

/-- Any extreme Gibbs measure `ν ≠ μ` gives zero mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_gibbsKernel_eq_ne (hG : (G γ).Nonempty) {μ ν : Measure Ω}
    (hν : ν ∈ (G γ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    ν {ω | gibbsKernel γ hG.some ω = μ} = 0 :=
  (isPAKernel_gibbsKernel_some hG).measure_kernel_eq_ne
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) hν hne

/-- **Georgii, Corollary (7.29)**, part 1: distinct extreme Gibbs measures are linearly
independent over `ℝ≥0∞`. -/
theorem linearIndependent_of_mem_extremePoints (hG : (G γ).Nonempty) {N : ℕ}
    {μ : Fin N → Measure Ω} (hμ : ∀ i, μ i ∈ (G γ).extremePoints ℝ≥0∞)
    (hinj : Function.Injective μ) : LinearIndependent ℝ≥0∞ μ :=
  (isPAKernel_gibbsKernel_some hG).linearIndependent_of_mem_extremePoints
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) hμ hinj

/-- Georgii (7.29), part 1 in relation form: no nontrivial `ℝ≥0∞`-linear relation holds between
distinct extreme Gibbs measures. -/
theorem eq_of_sum_smul_extremePoints_eq (hG : (G γ).Nonempty) {N : ℕ}
    {μ : Fin N → Measure Ω} (hμ : ∀ i, μ i ∈ (G γ).extremePoints ℝ≥0∞)
    (hinj : Function.Injective μ) {c d : Fin N → ℝ≥0∞}
    (h : ∑ i, c i • μ i = ∑ i, d i • μ i) : c = d :=
  funext (Fintype.linearIndependent_iffₛ.1 (linearIndependent_of_mem_extremePoints hG hμ hinj)
    c d h)

/-- **Georgii, Corollary (7.29)**, part 2: if `ex G(γ)` has fewer than `N` elements, any `N`
Gibbs measures satisfy a nontrivial `ℝ≥0∞`-linear relation. -/
theorem exists_ne_sum_smul_eq_sum_smul (hG : (G γ).Nonempty) {N : ℕ}
    (hcard : ((G γ).extremePoints ℝ≥0∞).encard < N) {μ : Fin N → Measure Ω}
    (hμ : ∀ i, μ i ∈ G γ) :
    ∃ c d : Fin N → ℝ≥0∞, c ≠ d ∧ ∑ i, c i • μ i = ∑ i, d i • μ i :=
  (isPAKernel_gibbsKernel_some hG).exists_ne_sum_smul_eq_sum_smul
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) hcard hμ

/-- **Georgii, Corollary (7.29)**: `|ex G(γ)| ≥ N` iff `G(γ)` contains `N` linearly independent
measures. -/
theorem le_encard_extremePoints_iff (hG : (G γ).Nonempty) (N : ℕ) :
    (N : ℕ∞) ≤ ((G γ).extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure Ω, (∀ i, μ i ∈ G γ) ∧ LinearIndependent ℝ≥0∞ μ :=
  (isPAKernel_gibbsKernel_some hG).le_encard_extremePoints_iff
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) N

end Corollary729

/-! ### Georgii (7.30): `G(γ)` is the closed convex hull of the limiting Gibbs measures -/

section Corollary730

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  {γ : Specification S E}

local notation3 (prettyPrint := false) "Ω" => (S → E)

/-- `G(γ)` is convex: finite convex combinations of Gibbs measures are Gibbs measures. -/
lemma sum_smul_mem_G {n : ℕ} {c : Fin n → ℝ≥0∞} {ν : Fin n → Measure Ω}
    (hν : ∀ i, ν i ∈ G γ) (hc : ∑ i, c i = 1) : (∑ i, c i • ν i) ∈ G γ := by
  have hwprob : IsProbabilityMeasure (∑ i, c i • Measure.dirac (ν i) : Measure (Measure Ω)) := by
    constructor
    rw [Measure.finsetSum_apply]
    have h1 : ∀ i : Fin n, (c i • Measure.dirac (ν i) : Measure (Measure Ω)) univ = c i := by
      intro i
      rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun i _ ↦ h1 i]
    exact hc
  have hnull : (∑ i, c i • Measure.dirac (ν i) : Measure (Measure Ω)) ((G γ)ᶜ) = 0 := by
    rw [Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_G γ).compl,
      Set.indicator_of_notMem (Set.notMem_compl_iff.2 (hν i)), smul_zero]
  rw [← join_finset_sum_smul_dirac (Finset.univ : Finset (Fin n)) c ν]
  exact join_mem_G _ hnull

variable (γ) in
/-- Finite convex combinations of limiting Gibbs measures (Georgii's `cx G_lim(γ)`), inside the
space of probability measures with the topology of local convergence. -/
def convexCombosLimitGibbs : Set (WithLocalConvergence S E) :=
  convexCombos (limitGibbs γ)

omit [Countable S] [StandardBorelSpace E] in
variable (γ) in
/-- Georgii's `cx G_lim(γ)` of (7.30) is `convexCombos (limitGibbs γ)`. -/
lemma convexCombosLimitGibbs_eq_convexCombos :
    convexCombosLimitGibbs γ = convexCombos (limitGibbs γ) := rfl

omit [Countable S] [StandardBorelSpace E] in
/-- `G_lim(γ)` consists of trivial (one-point) convex combinations of itself. -/
lemma limitGibbs_subset_convexCombosLimitGibbs :
    limitGibbs γ ⊆ convexCombosLimitGibbs γ :=
  subset_convexCombos _

/-- Georgii (7.30), easy inclusion: the closed convex hull of `G_lim(γ)` lies in `G(γ)`. -/
theorem closure_convexCombosLimitGibbs_subset (hγ : γ.IsQuasilocal) :
    closure (convexCombosLimitGibbs γ) ⊆
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} := by
  refine closure_minimal ?_ (isClosed_setOf_mem_GP hγ)
  rintro μ ⟨n, c, ν, hν, hc, hμeq⟩
  have hmem : ∀ i, ((ν i).toMeasure : Measure Ω) ∈ G γ := fun i ↦
    (G.mem_iff _).2 ⟨inferInstance, limitGibbs_subset_GP γ hγ (hν i)⟩
  have hsum := sum_smul_mem_G hmem hc
  change Specification.IsGibbsMeasure γ (μ.toMeasure : Measure Ω)
  rw [hμeq]
  exact ((G.mem_iff _).1 hsum).2

/-- Discretisation step of Georgii (7.30): a Gibbs measure is approximated within `1/r` on
finitely many events by a finite convex combination of extreme Gibbs measures. -/
theorem exists_extremePoints_combo_approx (hG : (G γ).Nonempty) {μ : Measure Ω} (hμ : μ ∈ G γ)
    {k : ℕ} (A : Fin k → Set Ω) (hA : ∀ j, MeasurableSet (A j)) {r : ℕ} (hr : 0 < r) :
    ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → Measure Ω),
      (∀ i, ν i ∈ (G γ).extremePoints ℝ≥0∞) ∧ (∑ i, c i) = 1 ∧
      ∀ j, (∑ i, c i • ν i) (A j) ≤ μ (A j) + (r : ℝ≥0∞)⁻¹ ∧
        μ (A j) ≤ (∑ i, c i • ν i) (A j) + (r : ℝ≥0∞)⁻¹ :=
  (isPAKernel_gibbsKernel_some hG).exists_extremePoints_combo_approx
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) hμ A hA hr

/-- Hard inclusion of **Georgii, Corollary (7.30)**, given Theorem (7.12)(c): if every extreme
Gibbs measure is a limiting Gibbs measure, `ex G(γ) ⊆ G_lim(γ)`, then every Gibbs measure lies in
the closed convex hull of `G_lim(γ)`. This is `IsPAKernel.setOf_mem_subset_closure_convexCombos`
at `P = G(γ)`, `𝒜 = 𝓣`, `𝒞 = localEvents S E`. -/
theorem setOf_mem_GP_subset_closure_convexCombosLimitGibbs
    (hlim : ∀ μ : ProbabilityMeasure Ω, (μ : Measure Ω) ∈ (G γ).extremePoints ℝ≥0∞ →
      (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ limitGibbs γ) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} ⊆
      closure (convexCombosLimitGibbs γ) := by
  intro μ0 hμ0
  have hμG : (μ0.toMeasure : Measure Ω) ∈ G γ := (G.mem_iff _).2 ⟨inferInstance, hμ0⟩
  have hG : (G γ).Nonempty := ⟨_, hμG⟩
  exact (isPAKernel_gibbsKernel_some hG).setOf_mem_subset_closure_convexCombos
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ)
    (fun _ hA ↦ MeasurableSet.of_mem_measurableCylinders hA) hlim hμG

/-- **Georgii, Corollary (7.30)**, conditional form: for a quasilocal specification `γ` with
`ex G(γ) ⊆ G_lim(γ)` — the conclusion of Theorem (7.12)(c) — the Gibbs measures form the closed
convex hull of the limiting Gibbs measures in the topology of local convergence. -/
theorem setOf_mem_GP_eq_closure_convexCombosLimitGibbs_of_mem_limitGibbs
    (hγ : γ.IsQuasilocal)
    (hlim : ∀ μ : ProbabilityMeasure Ω, (μ : Measure Ω) ∈ (G γ).extremePoints ℝ≥0∞ →
      (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ limitGibbs γ) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} =
      closure (convexCombosLimitGibbs γ) :=
  Subset.antisymm (setOf_mem_GP_subset_closure_convexCombosLimitGibbs hlim)
    (closure_convexCombosLimitGibbs_subset hγ)

/-- **Georgii, Corollary (7.30)** (finite `E`): for a quasilocal specification, the Gibbs
measures form the closed convex hull of the limiting Gibbs measures `G_lim(γ)` in the topology
of local convergence. -/
theorem setOf_mem_GP_eq_closure_convexCombosLimitGibbs [Finite E] (hγ : γ.IsQuasilocal) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} =
      closure (convexCombosLimitGibbs γ) :=
  setOf_mem_GP_eq_closure_convexCombosLimitGibbs_of_mem_limitGibbs hγ fun _ hμ ↦
    ofMeasure_mem_limitGibbs_of_mem_extremePoints_G γ hμ

/-! ### (7.30) at Georgii's hypotheses: a quasilocal λ-specification

Georgii states Corollary (7.30) for a standard Borel state space and a quasilocal
λ-specification `γ = ρ λ_·` (Definition (1.27)), where `λ ∈ 𝓜(E, ℰ)` is σ-finite and non-zero.
The extra input over `setOf_mem_GP_eq_closure_convexCombosLimitGibbs_of_mem_limitGibbs` is
Theorem (7.12)(c), `ex G(γ) ⊆ G_lim(γ)`, which holds for a λ-specification over an arbitrary
state space.

Remark (1.28)(3) makes the two readings of "λ-specification" one: with
`λ̃ = r · λ` for a measurable `r > 0` with `λ(r) = 1`, a λ-specification is a `λ̃`-specification
for a *probability* `λ̃`.  So the general statement is the one for a probability a priori measure
and an arbitrary λ-modification `ρ`, i.e. an arbitrary `Specification.IsModifier` of
`Specification.isssd` (`setOf_mem_GP_eq_closure_convexCombosLimitGibbs_modification_isssd`); the
σ-finite reading, in the normalized-premodifier form in which this library builds Gibbsian
specifications, is `setOf_mem_GP_eq_closure_convexCombosLimitGibbs_lambdaSpecification`. -/

section LambdaSpecification

variable {ν : Measure E} {ρ : Finset S → (S → E) → ℝ≥0∞}

section Modification

variable [IsProbabilityMeasure ν]

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification `γ = ρ λ_·` in the sense of Definition
(1.27), in the topology of local convergence: for `μ ∈ ex G(γ)` and `μ`-almost every boundary
condition `ω`, `γ_{Λ_m}(· | ω) → μ` locally along the canonical exhaustion.

This reads the uniform total-variation form of (7.12)(c)
(`ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G`) off on a single local event `A`:
`A` is `𝓕_Δ`-measurable for some finite `Δ`, and the supremum over `𝓕_Δ` dominates the deviation
at `A`. -/
theorem ae_tendsto_finiteVolumeDistributions_exhaustion_modification_isssd
    (hmod : (Specification.isssd (S := S) (E := E) ν).IsModifier ρ)
    {μ : ProbabilityMeasure Ω}
    (hμ : (μ : Measure Ω) ∈
      (G ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod)).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      Tendsto (fun m ↦ (WithSetwiseTopology.ofMeasure
          (finiteVolumeDistributions ((Specification.isssd ν).modification ρ hmod) ω
            (exhaustionVolumes m)) : WithLocalConvergence S E))
        atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  filter_upwards [ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G hmod hμ
    exhaustionVolumes_monotone exhaustionVolumes_cofinal] with ω hω
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  set κ : ℕ → Measure Ω := fun m ↦
    ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod) (exhaustionVolumes m) ω
    with hκ
  -- the total-variation deviation on `𝓕_Δ` dominates the deviation at `A`
  have hle : ∀ m, ENNReal.ofReal |(κ m A).toReal - ((μ : Measure Ω) A).toReal| ≤
      ⨆ (B : Set Ω)
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] B),
        ENNReal.ofReal |(κ m B).toReal - ((μ : Measure Ω) B).toReal| :=
    fun m ↦ le_iSup₂ (f := fun B
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] B) ↦
      ENNReal.ofReal |(κ m B).toReal - ((μ : Measure Ω) B).toReal|) A hΔ
  have hofReal : Tendsto (fun m ↦ ENNReal.ofReal
      |(κ m A).toReal - ((μ : Measure Ω) A).toReal|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω Δ) (fun m ↦ zero_le) hle
  have habs : Tendsto (fun m ↦ |(κ m A).toReal - ((μ : Measure Ω) A).toReal|) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hofReal
    simpa [Function.comp_def, ENNReal.toReal_ofReal, abs_nonneg] using h
  have hto : Tendsto (fun m ↦ (κ m A).toReal) atTop (𝓝 (((μ : Measure Ω) A).toReal)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using habs
  exact (ENNReal.tendsto_toReal_iff (fun m ↦ measure_ne_top _ _) (measure_ne_top _ _)).1 hto

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification: every extreme Gibbs measure is a
limiting Gibbs measure, `ex G(γ) ⊆ G_lim(γ)`. -/
theorem ofMeasure_mem_limitGibbs_modification_isssd
    (hmod : (Specification.isssd (S := S) (E := E) ν).IsModifier ρ)
    {μ : ProbabilityMeasure Ω}
    (hμ : (μ : Measure Ω) ∈
      (G ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod)).extremePoints ℝ≥0∞) :
    (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈
      limitGibbs ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod) := by
  obtain ⟨ω, hω⟩ :=
    (ae_tendsto_finiteVolumeDistributions_exhaustion_modification_isssd hmod hμ).exists
  exact ⟨exhaustionVolumes, fun _ ↦ ω, tendsto_exhaustionVolumes_atTop, hω⟩

/-- **Georgii, Corollary (7.30)**, at the book's hypotheses: over a standard Borel state space,
the Gibbs measures of a quasilocal λ-specification `γ = ρ λ_·` form the closed convex hull of the
limiting Gibbs measures `G_lim(γ)` in the topology of local convergence.

Here `ρ` is an arbitrary λ-modification in the sense of Definition (1.27) — a density family
making `ρ λ_·` a specification, i.e. a `Specification.IsModifier` of `Specification.isssd ν` —
and, by Remark (1.28)(3), taking the a priori measure to be a probability measure is no
restriction: see `setOf_mem_GP_eq_closure_convexCombosLimitGibbs_lambdaSpecification` for the
σ-finite form. -/
theorem setOf_mem_GP_eq_closure_convexCombosLimitGibbs_modification_isssd
    (hmod : (Specification.isssd (S := S) (E := E) ν).IsModifier ρ)
    (hγ : ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod).IsQuasilocal) :
    {μ : WithLocalConvergence S E |
        μ.toMeasure ∈ GP ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod)} =
      closure (convexCombosLimitGibbs
        ((Specification.isssd (S := S) (E := E) ν).modification ρ hmod)) :=
  setOf_mem_GP_eq_closure_convexCombosLimitGibbs_of_mem_limitGibbs hγ fun _ hμ ↦
    ofMeasure_mem_limitGibbs_modification_isssd hmod hμ

end Modification

section SigmaFinite

variable [SigmaFinite ν] [NeZero ν]

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for the λ-specification of a normalized pre-modification over
an arbitrary σ-finite non-zero a priori measure `λ ∈ 𝓜(E, ℰ)`.

The reduction to a probability a priori measure is Georgii's Remark (1.28)(3): choose a
measurable `r > 0` with `λ(r) = 1`
(`MeasureTheory.Measure.exists_measurable_pos_isProbabilityMeasure_withDensity`); then
`ρ̃_Λ = ρ_Λ / ∏_{i ∈ Λ} r(ω_i)` is a pre-modification for `λ̃ = r · λ` with `ρ̃ λ̃_· = ρ λ_·`
(`Specification.modificationKer_sigmaFiniteLambdaFun_of_withDensity`). -/
theorem ae_tendsto_finiteVolumeDistributions_exhaustion_lambdaSpecification
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : ProbabilityMeasure Ω}
    (hμ : (μ : Measure Ω) ∈
      (G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)).extremePoints ℝ≥0∞) :
    ∀ᵐ ω ∂(μ : Measure Ω),
      Tendsto (fun m ↦ (WithSetwiseTopology.ofMeasure
          (finiteVolumeDistributions (Specification.lambdaSpecification ν ρ hρ hZ) ω
            (exhaustionVolumes m)) : WithLocalConvergence S E))
        atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  obtain ⟨r, hr, h0, htop, hprob⟩ :=
    Measure.exists_measurable_pos_isProbabilityMeasure_withDensity ν
  have := hprob
  have hρ' : Specification.IsPremodifier (S := S) (E := E) (Specification.rescale r ρ) :=
    Specification.isPremodifier_rescale (S := S) (E := E) hr h0 htop hρ
  have hZ' : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) (ν.withDensity r)
      (Specification.rescale r ρ) :=
    (Specification.isSigmaFiniteLambdaAdmissible_rescale (S := S) (E := E) ν hr h0 htop
      hρ.measurable).2 hZ
  -- Remark (1.28)(3): `ρ̃ λ̃_· = ρ λ_·`
  have hγ : Specification.lambdaSpecification (S := S) (E := E) (ν.withDensity r)
        (Specification.rescale r ρ) hρ' hZ'
      = Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ := by
    refine Specification.ext fun Λ ↦ ?_
    rw [Specification.coe_lambdaSpecification, Specification.coe_lambdaSpecification]
    exact congrFun (Specification.modificationKer_sigmaFiniteLambdaFun_of_withDensity
      (S := S) (E := E) ν (ν.withDensity r) hr h0 htop rfl hρ.measurable _ _) Λ
  rw [← hγ, Specification.lambdaSpecification_eq_modification_isssd] at hμ ⊢
  exact ae_tendsto_finiteVolumeDistributions_exhaustion_modification_isssd _ hμ

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification over a σ-finite non-zero a priori
measure: every extreme Gibbs measure is a limiting Gibbs measure, `ex G(γ) ⊆ G_lim(γ)`. -/
theorem ofMeasure_mem_limitGibbs_lambdaSpecification
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : ProbabilityMeasure Ω}
    (hμ : (μ : Measure Ω) ∈
      (G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)).extremePoints ℝ≥0∞) :
    (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈
      limitGibbs (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) := by
  obtain ⟨ω, hω⟩ :=
    (ae_tendsto_finiteVolumeDistributions_exhaustion_lambdaSpecification hρ hZ hμ).exists
  exact ⟨exhaustionVolumes, fun _ ↦ ω, tendsto_exhaustionVolumes_atTop, hω⟩

/-- **Georgii, Corollary (7.30)** for the λ-specification of a normalized pre-modification over an
arbitrary σ-finite non-zero a priori measure `λ ∈ 𝓜(E, ℰ)`, the form in which this library builds
Gibbsian specifications: over a standard Borel state space, the Gibbs measures of a quasilocal
λ-specification form the closed convex hull of the limiting Gibbs measures `G_lim(γ)` in the
topology of local convergence. -/
theorem setOf_mem_GP_eq_closure_convexCombosLimitGibbs_lambdaSpecification
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (hγ : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsQuasilocal) :
    {μ : WithLocalConvergence S E |
        μ.toMeasure ∈ GP (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)} =
      closure (convexCombosLimitGibbs
        (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)) :=
  setOf_mem_GP_eq_closure_convexCombosLimitGibbs_of_mem_limitGibbs hγ fun _ hμ ↦
    ofMeasure_mem_limitGibbs_lambdaSpecification hρ hZ hμ

end SigmaFinite

end LambdaSpecification

end Corollary730

end MeasureTheory.GibbsMeasure

end

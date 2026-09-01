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
(`S` countable, `E` standard Borel):

* **(7.7)(c)**: each `μ ∈ G(γ)` is uniquely determined within `G(γ)` by its restriction to the
  tail σ-algebra `𝓣` (`eq_of_forall_measurableSet_tail_eq`); this and **(7.7)(d)** — distinct
  extreme Gibbs measures are separated by a tail event, hence mutually singular — hold for an
  arbitrary state space `E`, without the standard Borel assumption of §7.3.
* **(7.28)**: the weight map `μ ↦ w_μ` commutes with every symmetry `τ` of `γ`:
  `w_{τ(μ)} = τ(w_μ)`; in particular `μ` is `τ`-invariant iff `w_μ` is.
* **(7.29)**: `|ex G(γ)| ≥ N` iff `G(γ)` contains `N` linearly independent measures.
* **(7.30)**: `G(γ)` is the closed convex hull of the limiting Gibbs measures `G_lim(γ)` in the
  topology of local convergence — at Georgii's hypotheses, a standard Borel state space and a
  quasilocal λ-specification (`setOf_mem_GP_eq_closure_convexCombosLimitGibbs_lambdaSpecification`),
  and for an arbitrary quasilocal specification over a finite state space
  (`setOf_mem_GP_eq_closure_convexCombosLimitGibbs`). Both follow from the density step
  `setOf_mem_GP_subset_closure_convexCombosLimitGibbs`, which needs only `ex G(γ) ⊆ G_lim(γ)` —
  Theorem (7.12)(c), supplied over a finite state space by
  `ofMeasure_mem_limitGibbs_of_mem_extremePoints_G` and for a λ-specification by the uniform form
  of (7.12)(c) (`ae_forall_tendsto_iSup_ofReal_abs_sub_lambdaSpecification`) via
  `ofMeasure_mem_limitGibbs_lambdaSpecification`.
-/

@[expose] public section


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

/-! ### Giry-monad helpers -/

section GiryHelpers

variable {X : Type*} [MeasurableSpace X]

/-- The join of a finite combination of Dirac masses is the corresponding combination. -/
lemma join_finset_sum_smul_dirac {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0∞) (ν : ι → Measure X) :
    Measure.join (∑ i ∈ s, c i • Measure.dirac (ν i)) = ∑ i ∈ s, c i • ν i := by
  ext A hA
  rw [Measure.join_apply hA, lintegral_finsetSum_measure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (Measure.measurable_coe hA), Measure.smul_apply]

variable [MeasurableSpace.CountablyGenerated X]

/-- In a countably generated space, the singleton of a probability measure is measurable in
`Measure X` (Georgii's remark (iii) on the evaluation σ-algebra). -/
lemma measurableSet_singleton_measure (ν : Measure X) [IsProbabilityMeasure ν] :
    MeasurableSet ({ν} : Set (Measure X)) := by
  have hset : ({ν} : Set (Measure X)) =
      {ρ : Measure X | ρ univ = 1} ∩
        ⋂ t : Finset ℕ, {ρ : Measure X | ρ (piNatGen (Ω := X) t) = ν (piNatGen (Ω := X) t)} := by
    ext ρ
    simp only [mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro rfl
      exact ⟨measure_univ, fun t ↦ rfl⟩
    · rintro ⟨hρuniv, hρ⟩
      have : IsProbabilityMeasure ρ := ⟨hρuniv⟩
      refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet X)
        generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
      rintro s ⟨t, rfl⟩
      exact hρ t
  rw [hset]
  exact ((measurableSet_singleton 1).preimage (Measure.measurable_coe MeasurableSet.univ)).inter
    (MeasurableSet.iInter fun t ↦ (measurableSet_singleton _).preimage
      (Measure.measurable_coe (measurableSet_piNatGen t)))

/-- A weight carried by a finite set of probability measures is a finite combination of Dirac
masses. -/
lemma eq_sum_smul_dirac (w : Measure (Measure X)) (T : Finset (Measure X))
    (hT : ∀ ν ∈ T, IsProbabilityMeasure ν) (hw : w ((↑T : Set (Measure X))ᶜ) = 0) :
    w = ∑ ν ∈ T, w {ν} • Measure.dirac ν := by
  classical
  have hsing : ∀ ν ∈ T, MeasurableSet ({ν} : Set (Measure X)) := fun ν hν ↦
    have := hT ν hν
    measurableSet_singleton_measure ν
  have hTmeas : MeasurableSet (↑T : Set (Measure X)) := by
    rw [← Set.biUnion_of_singleton (↑T : Set (Measure X))]
    exact MeasurableSet.biUnion T.countable_toSet fun ν hν ↦ hsing ν hν
  ext M hM
  have h1 : w M = w (M ∩ ↑T) := by
    have h0 : w (M \ ↑T) = 0 := measure_mono_null (fun ν hν ↦ hν.2) hw
    rw [← measure_inter_add_sdiff M hTmeas, h0, add_zero]
  have h2 : M ∩ ↑T = ⋃ ν ∈ T.filter (· ∈ M), ({ν} : Set (Measure X)) := by
    ext ρ
    simp only [mem_inter_iff, mem_iUnion, mem_singleton_iff, Finset.mem_filter, Finset.mem_coe,
      exists_prop]
    constructor
    · rintro ⟨hρM, hρT⟩
      exact ⟨ρ, ⟨hρT, hρM⟩, rfl⟩
    · rintro ⟨ν, ⟨hνT, hνM⟩, rfl⟩
      exact ⟨hνM, hνT⟩
  have hdisj : (↑(T.filter (· ∈ M)) : Set (Measure X)).PairwiseDisjoint
      (fun ν ↦ ({ν} : Set (Measure X))) :=
    fun a _ b _ hab ↦ Set.disjoint_singleton.2 hab
  rw [h1, h2, measure_biUnion_finset hdisj
    (fun ν hν ↦ hsing ν (Finset.mem_of_mem_filter ν hν)), Measure.finsetSum_apply,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν hν ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hM, smul_eq_mul, Set.indicator_apply]
  split_ifs with h <;> simp

/-- The barycentre of a weight carried by a finite set of probability measures is the
corresponding finite convex combination. -/
lemma join_eq_sum_smul (w : Measure (Measure X)) (T : Finset (Measure X))
    (hT : ∀ ν ∈ T, IsProbabilityMeasure ν) (hw : w ((↑T : Set (Measure X))ᶜ) = 0) :
    Measure.join w = ∑ ν ∈ T, w {ν} • ν := by
  conv_lhs => rw [eq_sum_smul_dirac w T hT hw]
  simpa using join_finset_sum_smul_dirac T (fun ν ↦ w {ν}) (fun ν ↦ ν)

end GiryHelpers

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
/-- The inverse of a symmetry of `γ` (Georgii (5.7)) is a symmetry of `γ`. -/
theorem _root_.Specification.IsInvariant.inv {τ : Transformation S E}
    (hτ : Specification.IsInvariant τ γ) : Specification.IsInvariant τ.inv γ := by
  have hid : τ.inv.comp τ = Transformation.id := by simpa using inv_mul_cancel τ
  have h1 : γ.map (τ.inv.comp τ) = (γ.map τ).map τ.inv := Specification.map_comp τ.inv τ γ
  rw [hid, Specification.map_id] at h1
  show γ.map τ.inv = γ
  conv_lhs => rw [← hτ]
  exact h1.symm

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
    MeasurableSet ((G γ).extremePoints ℝ≥0∞) := by
  have hν₀ := hG.some_mem
  have := hν₀.1
  have hset : (G γ).extremePoints ℝ≥0∞ = G γ ∩ fixedCore (gibbsKernel γ hG.some) := by
    rw [extremePoints_G_eq_inter_trivialOn]
    ext ν
    simp only [mem_inter_iff, and_congr_right_iff]
    intro hν
    have := hν.1
    exact ((isPAKernel_gibbsKernel γ hG.some hν₀).mem_fixedCore_iff
      tailSigmaAlgebra_le_pi hν).symm
  rw [hset]
  exact (measurableSet_G γ).inter (measurableSet_fixedCore tailSigmaAlgebra_le_pi)

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
    ∀ᵐ ω ∂μ, gibbsKernel γ hG.some ω ∈ (G γ).extremePoints ℝ≥0∞ := by
  have hmeas := measurableSet_extremePoints_G (γ := γ) hG
  have hzero : μ (gibbsKernel γ hG.some ⁻¹' ((G γ).extremePoints ℝ≥0∞)ᶜ) = 0 := by
    rw [← weightOf_apply hG μ hmeas.compl]
    exact weightOf_extremePoints_compl hG hμ
  rw [ae_iff]
  convert hzero using 2
  ext ω
  simp

/-! ### Georgii (7.28): the weight map commutes with every symmetry -/

/-- **Georgii, Corollary (7.28)**: for a symmetry `τ` of `γ`, `w_{τ(μ)} = τ(w_μ)`. -/
theorem weightOf_map (hG : (G γ).Nonempty) {τ : Transformation S E}
    (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    weightOf hG (μ.map τ.toFun) = (weightOf hG μ).map (Measure.map τ.toFun) := by
  have := hμ.1
  refine (eq_weightOf_of_join_eq hG ?_ ?_).symm
  · rw [Measure.map_apply (Measure.measurable_map _ τ.measurable_toFun)
      (measurableSet_extremePoints_G hG).compl]
    exact measure_mono_null (fun ν hν hνex ↦ hν (map_mem_extremePoints_G hτ hνex))
      (weightOf_extremePoints_compl hG hμ)
  · rw [Measure.join_map_map τ.measurable_toFun, join_weightOf hG hμ]

/-- **Georgii, Corollary (7.28)**, second half: `μ ∈ G(γ)` is `τ`-invariant iff its weight
`w_μ` is invariant under `ν ↦ τ(ν)`. -/
theorem map_eq_self_iff_weightOf_map_eq_self (hG : (G γ).Nonempty) {τ : Transformation S E}
    (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    μ.map τ.toFun = μ ↔ (weightOf hG μ).map (Measure.map τ.toFun) = weightOf hG μ := by
  constructor
  · intro h
    rw [← weightOf_map hG hτ hμ, h]
  · intro h
    calc μ.map τ.toFun = Measure.join (weightOf hG (μ.map τ.toFun)) :=
          (join_weightOf hG (map_mem_G hτ hμ)).symm
      _ = Measure.join ((weightOf hG μ).map (Measure.map τ.toFun)) := by
          rw [weightOf_map hG hτ hμ]
      _ = Measure.join (weightOf hG μ) := by rw [h]
      _ = μ := join_weightOf hG hμ

/-- Georgii (7.28): `τ` preserves `μ ∈ G(γ)` iff `ν ↦ τ(ν)` preserves the weight `w_μ`. -/
theorem measurePreserving_iff_measurePreserving_weightOf (hG : (G γ).Nonempty)
    {τ : Transformation S E} (hτ : Specification.IsInvariant τ γ) {μ : Measure Ω}
    (hμ : μ ∈ G γ) :
    MeasurePreserving τ.toFun μ μ ↔
      MeasurePreserving (Measure.map τ.toFun) (weightOf hG μ) (weightOf hG μ) := by
  constructor
  · intro h
    exact ⟨Measure.measurable_map _ τ.measurable_toFun,
      (map_eq_self_iff_weightOf_map_eq_self hG hτ hμ).1 h.map_eq⟩
  · intro h
    exact ⟨τ.measurable_toFun, (map_eq_self_iff_weightOf_map_eq_self hG hτ hμ).2 h.map_eq⟩

end Symmetry

/-! ### Georgii (7.29): linear dimension of `G(γ)` counts the extreme points -/

section Corollary729

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  {γ : Specification S E}

local notation3 (prettyPrint := false) "Ω" => (S → E)

/-- An extreme Gibbs measure gives full mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_gibbsKernel_eq_self (hG : (G γ).Nonempty) {μ : Measure Ω}
    (hμ : μ ∈ (G γ).extremePoints ℝ≥0∞) :
    μ {ω | gibbsKernel γ hG.some ω = μ} = 1 := by
  have hν₀ := hG.some_mem
  have := hν₀.1
  have hμG : μ ∈ G γ := extremePoints_subset hμ
  have := hμG.1
  have hμ' := hμ
  rw [extremePoints_G_eq_inter_trivialOn] at hμ'
  have hae : ∀ᵐ ω ∂μ, gibbsKernel γ hG.some ω = μ :=
    (isPAKernel_gibbsKernel γ hG.some hν₀).ae_eq_of_mem_trivialOn tailSigmaAlgebra_le_pi
      hμG hμ'.2
  rw [← prob_compl_eq_zero_iff
    (tailSigmaAlgebra_le_pi _ (measurableSet_eq_measure (π := gibbsKernel γ hG.some) μ))]
  rw [compl_ofPred]
  exact ae_iff.1 hae

/-- Any extreme Gibbs measure `ν ≠ μ` gives zero mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_gibbsKernel_eq_ne (hG : (G γ).Nonempty) {μ ν : Measure Ω}
    (hν : ν ∈ (G γ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    ν {ω | gibbsKernel γ hG.some ω = μ} = 0 := by
  have hν₀ := hG.some_mem
  have := hν₀.1
  have hνG : ν ∈ G γ := extremePoints_subset hν
  have := hνG.1
  have hν' := hν
  rw [extremePoints_G_eq_inter_trivialOn] at hν'
  have hae : ∀ᵐ ω ∂ν, gibbsKernel γ hG.some ω = ν :=
    (isPAKernel_gibbsKernel γ hG.some hν₀).ae_eq_of_mem_trivialOn tailSigmaAlgebra_le_pi
      hνG hν'.2
  refine measure_mono_null ?_ (ae_iff.1 hae)
  intro ω hω hcontra
  exact hne (by rw [← hω, hcontra])

/-- **Georgii, Corollary (7.29)**, part 1: distinct extreme Gibbs measures are linearly
independent over `ℝ≥0∞`. -/
theorem linearIndependent_of_mem_extremePoints (hG : (G γ).Nonempty) {N : ℕ}
    {μ : Fin N → Measure Ω} (hμ : ∀ i, μ i ∈ (G γ).extremePoints ℝ≥0∞)
    (hinj : Function.Injective μ) : LinearIndependent ℝ≥0∞ μ := by
  rw [Fintype.linearIndependent_iffₛ]
  intro c d hcd i
  set A : Set Ω := {ω | gibbsKernel γ hG.some ω = μ i} with hAdef
  have key : ∀ e : Fin N → ℝ≥0∞, (∑ l, e l • μ l) A = e i := by
    intro e
    rw [Measure.finsetSum_apply]
    rw [Finset.sum_eq_single i (fun l _ hl ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)]
    · rw [Measure.smul_apply, measure_gibbsKernel_eq_self hG (hμ i), smul_eq_mul, mul_one]
    · rw [Measure.smul_apply, measure_gibbsKernel_eq_ne hG (hμ l) (hinj.ne hl.symm),
        smul_eq_mul, mul_zero]
  have h2 : (∑ l, c l • μ l) A = (∑ l, d l • μ l) A := congrArg (fun ρ : Measure Ω ↦ ρ A) hcd
  rwa [key c, key d] at h2

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
    ∃ c d : Fin N → ℝ≥0∞, c ≠ d ∧ ∑ i, c i • μ i = ∑ i, d i • μ i := by
  classical
  have hfin : ((G γ).extremePoints ℝ≥0∞).Finite := encard_lt_top_iff.1 (hcard.trans_le le_top)
  have hTcard : hfin.toFinset.card < N := by
    have h1 : (hfin.toFinset.card : ℕ∞) < N := by
      rw [← hfin.encard_eq_coe_toFinset_card]
      exact hcard
    exact_mod_cast h1
  have hTprob : ∀ ν ∈ hfin.toFinset, IsProbabilityMeasure ν := fun ν hν ↦
    (extremePoints_subset (hfin.mem_toFinset.1 hν)).1
  have hprob : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ (hμ i).1
  have hwnull : ∀ i, (weightOf hG (μ i)) ((↑hfin.toFinset : Set (Measure Ω))ᶜ) = 0 := by
    intro i
    have := hprob i
    have h := weightOf_extremePoints_compl hG (hμ i)
    rwa [← hfin.coe_toFinset] at h
  have hrep : ∀ i, μ i = ∑ ν ∈ hfin.toFinset, (weightOf hG (μ i)) {ν} • ν := fun i ↦ by
    have := hprob i
    conv_lhs => rw [← join_weightOf hG (hμ i)]
    exact join_eq_sum_smul _ hfin.toFinset hTprob (hwnull i)
  -- the real weight vectors are linearly dependent
  set v : Fin N → (↥hfin.toFinset → ℝ) :=
    fun i t ↦ ((weightOf hG (μ i)) {t.1}).toReal with hvdef
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hLI
    have hle := hLI.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at hle
    omega
  obtain ⟨g, hg0, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hofmax : ∀ a : ℝ, ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
    intro a
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  refine ⟨fun i ↦ ENNReal.ofReal (g i), fun i ↦ ENNReal.ofReal (-g i), ?_, ?_⟩
  · -- the two coefficient families differ at `i₀`
    intro hcd
    have h := congrFun hcd i₀
    rcases lt_or_gt_of_ne hgi₀ with hneg | hpos
    · rw [ENNReal.ofReal_of_nonpos hneg.le] at h
      exact (ENNReal.ofReal_pos.2 (neg_pos.2 hneg)).ne h
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 hpos.le)] at h
      exact (ENNReal.ofReal_pos.2 hpos).ne' h
  · -- the two combinations agree
    have hcoord : ∀ ν ∈ hfin.toFinset,
        ∑ i, ENNReal.ofReal (g i) * (weightOf hG (μ i)) {ν} =
          ∑ i, ENNReal.ofReal (-g i) * (weightOf hG (μ i)) {ν} := by
      intro ν hν
      have hreal : ∑ i, g i * v i ⟨ν, hν⟩ = 0 := by
        have h := congrFun hg0 ⟨ν, hν⟩
        simpa using h
      have hsplit : ∑ i, max (g i) 0 * v i ⟨ν, hν⟩ = ∑ i, max (-g i) 0 * v i ⟨ν, hν⟩ := by
        have h2 : ∑ i, (max (g i) 0 * v i ⟨ν, hν⟩ - max (-g i) 0 * v i ⟨ν, hν⟩) = 0 := by
          calc ∑ i, (max (g i) 0 * v i ⟨ν, hν⟩ - max (-g i) 0 * v i ⟨ν, hν⟩)
              = ∑ i, g i * v i ⟨ν, hν⟩ := Finset.sum_congr rfl fun i _ ↦ by
                rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
            _ = 0 := hreal
        rw [Finset.sum_sub_distrib] at h2
        exact sub_eq_zero.1 h2
      calc ∑ i, ENNReal.ofReal (g i) * (weightOf hG (μ i)) {ν}
          = ∑ i, ENNReal.ofReal (max (g i) 0 * v i ⟨ν, hν⟩) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have := hprob i
            rw [ENNReal.ofReal_mul (le_max_right (g i) 0), hofmax,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ = ENNReal.ofReal (∑ i, max (g i) 0 * v i ⟨ν, hν⟩) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ ↦
              mul_nonneg (le_max_right (g i) 0) ENNReal.toReal_nonneg).symm
        _ = ENNReal.ofReal (∑ i, max (-g i) 0 * v i ⟨ν, hν⟩) := by rw [hsplit]
        _ = ∑ i, ENNReal.ofReal (max (-g i) 0 * v i ⟨ν, hν⟩) :=
            ENNReal.ofReal_sum_of_nonneg fun i _ ↦
              mul_nonneg (le_max_right (-g i) 0) ENNReal.toReal_nonneg
        _ = ∑ i, ENNReal.ofReal (-g i) * (weightOf hG (μ i)) {ν} := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have := hprob i
            rw [ENNReal.ofReal_mul (le_max_right (-g i) 0), hofmax,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hassemble : ∀ e : Fin N → ℝ≥0∞, ∑ i, e i • μ i =
        ∑ ν ∈ hfin.toFinset, (∑ i, e i * (weightOf hG (μ i)) {ν}) • ν := by
      intro e
      calc ∑ i, e i • μ i
          = ∑ i, ∑ ν ∈ hfin.toFinset, e i • ((weightOf hG (μ i)) {ν} • ν) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            conv_lhs => rw [hrep i]
            rw [Finset.smul_sum]
        _ = ∑ ν ∈ hfin.toFinset, ∑ i, e i • ((weightOf hG (μ i)) {ν} • ν) := Finset.sum_comm
        _ = ∑ ν ∈ hfin.toFinset, (∑ i, e i * (weightOf hG (μ i)) {ν}) • ν := by
            refine Finset.sum_congr rfl fun ν _ ↦ ?_
            rw [Finset.sum_smul]
            exact Finset.sum_congr rfl fun i _ ↦ smul_smul _ _ _
    rw [hassemble, hassemble]
    exact Finset.sum_congr rfl fun ν hν ↦ by rw [hcoord ν hν]

/-- **Georgii, Corollary (7.29)**: `|ex G(γ)| ≥ N` iff `G(γ)` contains `N` linearly independent
measures. -/
theorem le_encard_extremePoints_iff (hG : (G γ).Nonempty) (N : ℕ) :
    (N : ℕ∞) ≤ ((G γ).extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure Ω, (∀ i, μ i ∈ G γ) ∧ LinearIndependent ℝ≥0∞ μ := by
  constructor
  · intro hN
    obtain ⟨t, htsub, htcard⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
    have hcard : htfin.toFinset.card = N := by
      have h := htfin.encard_eq_coe_toFinset_card
      rw [htcard] at h
      exact_mod_cast h.symm
    set e := Finset.equivFinOfCardEq hcard with hedef
    have hext : ∀ i, ((e.symm i : ↥htfin.toFinset) : Measure Ω) ∈ (G γ).extremePoints ℝ≥0∞ :=
      fun i ↦ htsub (htfin.mem_toFinset.1 (e.symm i).2)
    refine ⟨fun i ↦ ((e.symm i : ↥htfin.toFinset) : Measure Ω),
      fun i ↦ extremePoints_subset (hext i), ?_⟩
    exact linearIndependent_of_mem_extremePoints hG hext
      fun i j h ↦ e.symm.injective (Subtype.coe_injective h)
  · rintro ⟨μ, hμG, hLI⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, d, hcd, hsum⟩ := exists_ne_sum_smul_eq_sum_smul hG hlt hμG
    exact hcd (funext (Fintype.linearIndependent_iffₛ.1 hLI c d hsum))

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
  {μ | ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → WithLocalConvergence S E),
    (∀ i, ν i ∈ limitGibbs γ) ∧ ∑ i, c i = 1 ∧
    (μ.toMeasure : Measure Ω) = ∑ i, c i • ((ν i).toMeasure : Measure Ω)}

omit [Countable S] [StandardBorelSpace E] in
/-- `G_lim(γ)` consists of trivial (one-point) convex combinations of itself. -/
lemma limitGibbs_subset_convexCombosLimitGibbs :
    limitGibbs γ ⊆ convexCombosLimitGibbs γ := by
  intro μ hμ
  refine ⟨1, fun _ ↦ 1, fun _ ↦ μ, fun _ ↦ hμ, by simp, ?_⟩
  simp

/-- Georgii (7.30), easy inclusion: the closed convex hull of `G_lim(γ)` lies in `G(γ)`. -/
theorem closure_convexCombosLimitGibbs_subset (hγ : γ.IsQuasilocal) :
    closure (convexCombosLimitGibbs γ) ⊆
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} := by
  refine closure_minimal ?_ (isClosed_setOf_mem_GP hγ)
  rintro μ ⟨n, c, ν, hν, hc, hμeq⟩
  have hmem : ∀ i, ((ν i).toMeasure : Measure Ω) ∈ G γ := fun i ↦
    (G.mem_iff _).2 ⟨inferInstance, limitGibbs_subset_GP γ hγ (hν i)⟩
  have hsum := sum_smul_mem_G hmem hc
  show Specification.IsGibbsMeasure γ (μ.toMeasure : Measure Ω)
  rw [hμeq]
  exact ((G.mem_iff _).1 hsum).2

/-- Discretisation step of Georgii (7.30): a Gibbs measure is approximated within `1/r` on
finitely many events by a finite convex combination of extreme Gibbs measures. -/
theorem exists_extremePoints_combo_approx (hG : (G γ).Nonempty) {μ : Measure Ω} (hμ : μ ∈ G γ)
    {k : ℕ} (A : Fin k → Set Ω) (hA : ∀ j, MeasurableSet (A j)) {r : ℕ} (hr : 0 < r) :
    ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → Measure Ω),
      (∀ i, ν i ∈ (G γ).extremePoints ℝ≥0∞) ∧ (∑ i, c i) = 1 ∧
      ∀ j, (∑ i, c i • ν i) (A j) ≤ μ (A j) + (r : ℝ≥0∞)⁻¹ ∧
        μ (A j) ≤ (∑ i, c i • ν i) (A j) + (r : ℝ≥0∞)⁻¹ := by
  classical
  have hprobμ := hμ.1
  set w := weightOf hG μ with hwdef
  have hwprob : IsProbabilityMeasure w := hwdef ▸ isProbabilityMeasure_weightOf hG μ
  have hXm : MeasurableSet ((G γ).extremePoints ℝ≥0∞) := measurableSet_extremePoints_G hG
  have hwX : w (((G γ).extremePoints ℝ≥0∞)ᶜ) = 0 := weightOf_extremePoints_compl hG hμ
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  -- the grid index of a measure
  set idx : Measure Ω → Fin k → ℕ := fun ρ j ↦ ⌊(ρ (A j)).toReal * r⌋₊ with hidxdef
  have hidx_meas : ∀ (j : Fin k) (m : ℕ), MeasurableSet {ρ : Measure Ω | idx ρ j = m} := by
    intro j m
    have h1 : Measurable fun ρ : Measure Ω ↦ (ρ (A j)).toReal * (r : ℝ) :=
      ((Measure.measurable_coe (hA j)).ennreal_toReal).mul_const _
    exact h1.nat_floor (measurableSet_singleton m)
  -- the cells of the induced partition of `ex G(γ)`
  set cell : (Fin k → Fin (r + 1)) → Set (Measure Ω) :=
    fun p ↦ ((G γ).extremePoints ℝ≥0∞) ∩ {ρ | ∀ j, idx ρ j = (p j : ℕ)} with hcelldef
  have hcell_meas : ∀ p, MeasurableSet (cell p) := by
    intro p
    refine hXm.inter ?_
    have h : {ρ : Measure Ω | ∀ j, idx ρ j = (p j : ℕ)} =
        ⋂ j, {ρ : Measure Ω | idx ρ j = (p j : ℕ)} := Set.ofPred_forall _
    rw [h]
    exact MeasurableSet.iInter fun j ↦ hidx_meas j (p j)
  have hdisj : (↑(Finset.univ : Finset (Fin k → Fin (r + 1))) :
      Set (Fin k → Fin (r + 1))).PairwiseDisjoint cell := by
    intro p _ q _ hpq
    refine Set.disjoint_left.2 fun ρ hρp hρq ↦ hpq ?_
    funext j
    exact Fin.val_injective ((hρp.2 j).symm.trans (hρq.2 j))
  have hcover : ((G γ).extremePoints ℝ≥0∞) =
      ⋃ p ∈ (Finset.univ : Finset (Fin k → Fin (r + 1))), cell p := by
    ext ρ
    constructor
    · intro hρ
      have : IsProbabilityMeasure ρ := (extremePoints_subset hρ).1
      have hbound : ∀ j, idx ρ j < r + 1 := by
        intro j
        have hle1 : (ρ (A j)).toReal ≤ 1 := by
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := A j))
        have hler : (ρ (A j)).toReal * r ≤ (r : ℝ) := by
          calc (ρ (A j)).toReal * r ≤ 1 * (r : ℝ) :=
                mul_le_mul_of_nonneg_right hle1 (Nat.cast_nonneg r)
            _ = r := one_mul _
        calc idx ρ j ≤ ⌊(r : ℝ)⌋₊ := Nat.floor_mono hler
          _ = r := Nat.floor_natCast r
          _ < r + 1 := Nat.lt_succ_self r
      exact Set.mem_iUnion₂.2 ⟨fun j ↦ ⟨idx ρ j, hbound j⟩, Finset.mem_univ _,
        hρ, fun j ↦ rfl⟩
    · intro hρ
      obtain ⟨p, -, hρp⟩ := Set.mem_iUnion₂.1 hρ
      exact hρp.1
  -- representatives: one extreme point per nonempty cell
  obtain ⟨νstar, hνstar⟩ := nonempty_extremePoints_G hG
  have hrepex : ∀ p, ∃ ρ : Measure Ω,
      ρ ∈ (G γ).extremePoints ℝ≥0∞ ∧ ((cell p).Nonempty → ρ ∈ cell p) := by
    intro p
    by_cases hp : (cell p).Nonempty
    · exact ⟨hp.some, hp.some_mem.1, fun _ ↦ hp.some_mem⟩
    · exact ⟨νstar, hνstar, fun h ↦ absurd h hp⟩
  choose rep hrepX hrepmem using hrepex
  -- total weight one
  have hsum1 : ∑ p : (Fin k → Fin (r + 1)), w (cell p) = 1 := by
    rw [← measure_biUnion_finset hdisj fun p _ ↦ hcell_meas p, ← hcover]
    exact (prob_compl_eq_zero_iff hXm).1 hwX
  -- diameter bound on cells
  have hdiam : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k) (ρ σ : Measure Ω), ρ ∈ cell p →
      σ ∈ cell p → ρ (A j) ≤ σ (A j) + (r : ℝ≥0∞)⁻¹ := by
    intro p j ρ σ hρ hσ
    have : IsProbabilityMeasure ρ := (extremePoints_subset hρ.1).1
    have : IsProbabilityMeasure σ := (extremePoints_subset hσ.1).1
    have hx : (ρ (A j)).toReal * r < (idx ρ j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hy : (idx σ j : ℝ) ≤ (σ (A j)).toReal * r := Nat.floor_le (by positivity)
    have heq : idx ρ j = idx σ j := (hρ.2 j).trans (hσ.2 j).symm
    have hreal : (ρ (A j)).toReal ≤ (σ (A j)).toReal + (r : ℝ)⁻¹ := by
      rw [heq] at hx
      have h1 : (ρ (A j)).toReal * r ≤ (σ (A j)).toReal * r + 1 := by linarith
      have h2 : (ρ (A j)).toReal ≤ ((σ (A j)).toReal * r + 1) / r := by
        rw [le_div_iff₀ hr0]
        exact h1
      calc (ρ (A j)).toReal ≤ ((σ (A j)).toReal * r + 1) / r := h2
        _ = (σ (A j)).toReal + (r : ℝ)⁻¹ := by
          rw [add_div, mul_div_cancel_right₀ _ hr0.ne', one_div]
    calc ρ (A j) = ENNReal.ofReal ((ρ (A j)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((σ (A j)).toReal + (r : ℝ)⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((σ (A j)).toReal) + ENNReal.ofReal ((r : ℝ)⁻¹) :=
          ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)
      _ = σ (A j) + (r : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_inv_of_pos hr0,
            ENNReal.ofReal_natCast]
  -- per-cell comparison of the representative with the integral
  have hcell_upper : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k), w (cell p) * (rep p) (A j) ≤
      (∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
    intro p j
    by_cases hp : (cell p).Nonempty
    · have hrepp := hrepmem p hp
      calc w (cell p) * (rep p) (A j) = ∫⁻ _ in cell p, (rep p) (A j) ∂w := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ ρ in cell p, (ρ (A j) + (r : ℝ≥0∞)⁻¹) ∂w :=
            setLIntegral_mono ((Measure.measurable_coe (hA j)).add_const _)
              fun ρ hρ ↦ hdiam p j (rep p) ρ hrepp hρ
        _ = (∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_comm]
    · have hempty : cell p = ∅ := Set.not_nonempty_iff_eq_empty.1 hp
      simp [hempty]
  have hcell_lower : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k),
      (∫⁻ ρ in cell p, ρ (A j) ∂w) ≤
        w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
    intro p j
    by_cases hp : (cell p).Nonempty
    · have hrepp := hrepmem p hp
      calc ∫⁻ ρ in cell p, ρ (A j) ∂w
          ≤ ∫⁻ _ in cell p, ((rep p) (A j) + (r : ℝ≥0∞)⁻¹) ∂w :=
            setLIntegral_mono measurable_const fun ρ hρ ↦ hdiam p j ρ (rep p) hρ hrepp
        _ = w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
            rw [setLIntegral_const]
            ring
    · have hempty : cell p = ∅ := Set.not_nonempty_iff_eq_empty.1 hp
      simp [hempty]
  -- decomposition of `μ` over the cells
  have hμdecomp : ∀ j : Fin k,
      μ (A j) = ∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w := by
    intro j
    have h1 : μ (A j) = ∫⁻ ρ, ρ (A j) ∂w := by
      conv_lhs => rw [← join_weightOf hG hμ]
      rw [Measure.join_apply (hA j)]
    have h2 : ∫⁻ ρ, ρ (A j) ∂w = ∫⁻ ρ in (G γ).extremePoints ℝ≥0∞, ρ (A j) ∂w := by
      rw [← lintegral_add_compl (fun ρ ↦ ρ (A j)) hXm]
      have h0 : ∫⁻ ρ in ((G γ).extremePoints ℝ≥0∞)ᶜ, ρ (A j) ∂w = 0 := by
        rw [Measure.restrict_eq_zero.2 hwX]
        exact lintegral_zero_measure _
      rw [h0, add_zero]
    rw [h1, h2, hcover, lintegral_biUnion_finset hdisj (fun p _ ↦ hcell_meas p)]
  -- the two estimates
  have hupper : ∀ j : Fin k, ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) ≤
      μ (A j) + (r : ℝ≥0∞)⁻¹ := by
    intro j
    calc ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)
        ≤ ∑ p : (Fin k → Fin (r + 1)),
            ((∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹) :=
          Finset.sum_le_sum fun p _ ↦ hcell_upper p j
      _ = (∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w) +
            (∑ p : (Fin k → Fin (r + 1)), w (cell p)) * (r : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = μ (A j) + (r : ℝ≥0∞)⁻¹ := by rw [← hμdecomp j, hsum1, one_mul]
  have hlower : ∀ j : Fin k, μ (A j) ≤
      (∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)) + (r : ℝ≥0∞)⁻¹ := by
    intro j
    calc μ (A j) = ∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w := hμdecomp j
      _ ≤ ∑ p : (Fin k → Fin (r + 1)),
            (w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹) :=
          Finset.sum_le_sum fun p _ ↦ hcell_lower p j
      _ = (∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)) +
            (∑ p : (Fin k → Fin (r + 1)), w (cell p)) * (r : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by rw [hsum1, one_mul]
  -- reindex over `Fin n`
  set eqv := Fintype.equivFin (Fin k → Fin (r + 1)) with heqv
  refine ⟨Fintype.card (Fin k → Fin (r + 1)), fun i ↦ w (cell (eqv.symm i)),
    fun i ↦ rep (eqv.symm i), fun i ↦ hrepX (eqv.symm i), ?_, fun j ↦ ?_⟩
  · rw [Equiv.sum_comp eqv.symm fun p ↦ w (cell p)]
    exact hsum1
  · have hcombo : (∑ i, w (cell (eqv.symm i)) • rep (eqv.symm i)) (A j) =
        ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) := by
      calc (∑ i, w (cell (eqv.symm i)) • rep (eqv.symm i)) (A j)
          = ∑ i, w (cell (eqv.symm i)) * (rep (eqv.symm i)) (A j) := by
            rw [Measure.finsetSum_apply]
            exact Finset.sum_congr rfl fun i _ ↦ by rw [Measure.smul_apply, smul_eq_mul]
        _ = ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) :=
            Equiv.sum_comp eqv.symm fun p ↦ w (cell p) * (rep p) (A j)
    rw [hcombo]
    exact ⟨hupper j, hlower j⟩

/-- Hard inclusion of **Georgii, Corollary (7.30)**, given Theorem (7.12)(c): if every extreme
Gibbs measure is a limiting Gibbs measure, `ex G(γ) ⊆ G_lim(γ)`, then every Gibbs measure lies in
the closed convex hull of `G_lim(γ)`.  Georgii's proof: the neighbourhoods of `μ ∈ G(γ)` in the
topology of local convergence are indexed by the directed family of pairs (finitely many local
events `I`, precision `1/(r+1)`), and `exists_extremePoints_combo_approx` — the partition of
`ex G(γ)` by a grid on the values `ν(A)`, `A ∈ I` — meets each of them with a finite convex
combination of extreme Gibbs measures. -/
theorem setOf_mem_GP_subset_closure_convexCombosLimitGibbs
    (hlim : ∀ μ : ProbabilityMeasure Ω, (μ : Measure Ω) ∈ (G γ).extremePoints ℝ≥0∞ →
      (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) ∈ limitGibbs γ) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP γ} ⊆
      closure (convexCombosLimitGibbs γ) := by
  classical
  intro μ0 hμ0
  have hμG : (μ0.toMeasure : Measure Ω) ∈ G γ := (G.mem_iff _).2 ⟨inferInstance, hμ0⟩
  have hG : (G γ).Nonempty := ⟨_, hμG⟩
  -- stage-`(I, r)` approximation: precision `1 / (r + 1)` on the local events in `I`
  have happrox : ∀ p : Finset (localEvents S E) × ℕ,
      ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → Measure Ω),
        (∀ i, ν i ∈ (G γ).extremePoints ℝ≥0∞) ∧ (∑ i, c i) = 1 ∧
        ∀ A ∈ p.1,
          (∑ i, c i • ν i) (A : Set Ω) ≤
              (μ0.toMeasure : Measure Ω) (A : Set Ω) + ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ ∧
            (μ0.toMeasure : Measure Ω) (A : Set Ω) ≤
              (∑ i, c i • ν i) (A : Set Ω) + ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rintro ⟨I, r⟩
    obtain ⟨n, c, ν, hν, hc, hbounds⟩ := exists_extremePoints_combo_approx hG hμG
      (fun j : Fin I.card ↦ ((I.equivFin.symm j : localEvents S E) : Set Ω))
      (fun j ↦ MeasurableSet.of_mem_measurableCylinders (I.equivFin.symm j).1.2)
      (r := r + 1) r.succ_pos
    refine ⟨n, c, ν, hν, hc, fun A hA ↦ ?_⟩
    have h := hbounds (I.equivFin ⟨A, hA⟩)
    rwa [Equiv.symm_apply_apply] at h
  choose n c ν hν hc hbounds using happrox
  have hprob : ∀ p, IsProbabilityMeasure (∑ i, c p i • ν p i : Measure Ω) := fun p ↦
    (sum_smul_mem_G (fun i ↦ extremePoints_subset (hν p i)) (hc p)).1
  set combo : Finset (localEvents S E) × ℕ → WithLocalConvergence S E := fun p ↦
    WithSetwiseTopology.ofMeasure (⟨∑ i, c p i • ν p i, hprob p⟩ : ProbabilityMeasure Ω)
    with hcombodef
  -- each `combo p` is a finite convex combination of limiting Gibbs measures
  have hmem : ∀ p, combo p ∈ convexCombosLimitGibbs γ := fun p ↦
    ⟨n p, c p, fun i ↦ WithSetwiseTopology.ofMeasure
      (⟨ν p i, (extremePoints_subset (hν p i)).1⟩ : ProbabilityMeasure Ω),
      fun i ↦ hlim _ (hν p i), hc p, rfl⟩
  -- `combo → μ0` along the directed family of stages
  have htendsto : Tendsto combo atTop (𝓝 μ0) := by
    rw [tendsto_withLocalConvergence_iff]
    intro B hB
    set ε : Finset (localEvents S E) × ℕ → ℝ≥0∞ := fun p ↦ ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ with hεdef
    have hsnd : Tendsto (fun p : Finset (localEvents S E) × ℕ ↦ p.2) atTop atTop :=
      tendsto_atTop_atTop.2 fun b ↦ ⟨(∅, b), fun p hp ↦ hp.2⟩
    have hεtendsto : Tendsto ε atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp ((tendsto_add_atTop_nat 1).comp hsnd)
    have hupper : Tendsto (fun p ↦ (μ0.toMeasure : Measure Ω) B + ε p) atTop
        (𝓝 ((μ0.toMeasure : Measure Ω) B)) := by
      have h := Tendsto.add
        (tendsto_const_nhds (x := (μ0.toMeasure : Measure Ω) B)
          (f := (atTop : Filter (Finset (localEvents S E) × ℕ)))) hεtendsto
      simpa using h
    have hlower : Tendsto (fun p ↦ (μ0.toMeasure : Measure Ω) B - ε p) atTop
        (𝓝 ((μ0.toMeasure : Measure Ω) B)) := by
      have h := ENNReal.Tendsto.sub
        (tendsto_const_nhds (x := (μ0.toMeasure : Measure Ω) B)
          (f := (atTop : Filter (Finset (localEvents S E) × ℕ)))) hεtendsto
        (Or.inl (measure_ne_top _ _))
      simpa using h
    have hBev : ∀ᶠ p : Finset (localEvents S E) × ℕ in atTop, (⟨B, hB⟩ : localEvents S E) ∈ p.1 :=
      eventually_atTop.2 ⟨({⟨B, hB⟩}, 0), fun p hp ↦ hp.1 (Finset.mem_singleton_self _)⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · filter_upwards [hBev] with p hp
      exact tsub_le_iff_right.2 (hbounds p ⟨B, hB⟩ hp).2
    · filter_upwards [hBev] with p hp
      exact (hbounds p ⟨B, hB⟩ hp).1
  exact mem_closure_of_tendsto htendsto (Eventually.of_forall hmem)

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

section LambdaSpecification

variable {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification, in the topology of local convergence:
for `μ ∈ ex G(γ)` and `μ`-a.e. boundary condition `ω`, `γ_{Λ_m}(· | ω) → μ` locally along the
canonical exhaustion.  This is the uniform total-variation-on-each-finite-volume form
(`ae_forall_tendsto_iSup_ofReal_abs_sub_lambdaSpecification`) read off on each local event. -/
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
  filter_upwards [ae_forall_tendsto_iSup_ofReal_abs_sub_lambdaSpecification hρ hZ hμ
    exhaustionVolumes_monotone exhaustionVolumes_cofinal] with ω hω
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  -- the total-variation distance on the events of `Δ` dominates the distance at `A`
  have hle : ∀ m, ENNReal.ofReal
      |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
          (exhaustionVolumes m) ω) A).toReal - ((μ : Measure Ω) A).toReal| ≤
      ⨆ (B : Set Ω)
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] B),
        ENNReal.ofReal |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
          (exhaustionVolumes m) ω) B).toReal - ((μ : Measure Ω) B).toReal| :=
    fun m ↦ le_iSup₂ (f := fun B
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] B) ↦
      ENNReal.ofReal |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
        (exhaustionVolumes m) ω) B).toReal - ((μ : Measure Ω) B).toReal|) A hΔ
  have hofReal : Tendsto (fun m ↦ ENNReal.ofReal
      |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
          (exhaustionVolumes m) ω) A).toReal - ((μ : Measure Ω) A).toReal|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hω Δ)
      (fun m ↦ zero_le) hle
  have habs : Tendsto (fun m ↦
      |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
          (exhaustionVolumes m) ω) A).toReal - ((μ : Measure Ω) A).toReal|) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hofReal
    simpa [Function.comp_def, ENNReal.toReal_ofReal, abs_nonneg] using h
  have hto : Tendsto (fun m ↦ ((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
      (exhaustionVolumes m) ω) A).toReal) atTop (𝓝 (((μ : Measure Ω) A).toReal)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using habs
  exact (ENNReal.tendsto_toReal_iff (fun m ↦ measure_ne_top _ _) (measure_ne_top _ _)).1 hto

omit [StandardBorelSpace E] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification: every extreme Gibbs measure is a
limiting Gibbs measure, `ex G(γ) ⊆ G_lim(γ)`. -/
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

/-- **Georgii, Corollary (7.30)**, at the book's hypotheses: over a standard Borel state space,
the Gibbs measures of a quasilocal λ-specification form the closed convex hull of the limiting
Gibbs measures `G_lim(γ)` in the topology of local convergence.  By Remark (1.28)(3)
(`Specification.lambdaSpecification_probNormalize`), the probability a priori measure covers
every finite non-zero `λ`. -/
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

end LambdaSpecification

end Corollary730

end MeasureTheory.GibbsMeasure

end

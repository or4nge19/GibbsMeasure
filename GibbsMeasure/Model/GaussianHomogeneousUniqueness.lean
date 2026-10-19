/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianShiftInvariance
public import GibbsMeasure.Model.GaussianConvolution
public import GibbsMeasure.Model.GaussianHomogeneousExtreme

/-!
# Georgii Corollary (13.40): the shift-invariant Gauss fields with finite second moment

Georgii's Corollary (13.40) reads:

> Let `J : ℤ^d → ℝ` be as before. If `Ĵ^{-1}` is integrable and `Ĵ(z) = 0` for some `z ∈ G` then
> `ex 𝒢_Θ(γ^{J,0})` contains uncountably many Gibbs measures with finite second moment.
> Conversely, if `Ĵ` has no root in `G` then `μ_C` is the only element of `𝒢_Θ(γ^{J,0})` with
> finite second moment.

## Main results

TODO
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Adding a constant configuration commutes with the shifts -/

section Const

variable {S : Type*} [AddCommGroup S] {μ : Measure (S → ℝ)}

lemma comp_add_const_eq (c : ℝ) (k : S) :
    (shift ℝ k).toFun ∘ (fun x : S → ℝ ↦ x + fun _ ↦ c)
      = (fun x : S → ℝ ↦ x + fun _ ↦ c) ∘ (shift ℝ k).toFun := by
  funext ω i
  simp [shift_toFun_apply]

/-- **A shift-invariant random field stays shift invariant under a constant translation.** -/
theorem map_add_const_mem_invariantFields [MeasurableSpace S]
    (hμ : μ ∈ invariantFields (shiftGroup S ℝ)) (c : ℝ) :
    (μ.map fun x ↦ x + fun _ ↦ c) ∈ invariantFields (shiftGroup S ℝ) := by
  obtain ⟨hprob, hshift⟩ := mem_invariantFields_shiftGroup.1 hμ
  have hT : Measurable (fun x : S → ℝ ↦ x + fun _ ↦ c) := by fun_prop
  refine mem_invariantFields_shiftGroup.2
    ⟨inferInstance, fun k ↦ ?_⟩
  refine ⟨Transformation.measurable_toFun _, ?_⟩
  rw [Measure.map_map (Transformation.measurable_toFun _) hT, comp_add_const_eq c k,
    ← Measure.map_map hT (Transformation.measurable_toFun _), (hshift k).map_eq]

end Const

end MeasureTheory.GibbsMeasure

namespace Potential

/-! ### Corollary (13.40)(a) for a root at the identity of `G` -/

section RootAtIdentity

open UnitAddTorus MeasureTheory.GibbsMeasure

attribute [local instance] Potential.instMeasureSpaceUnitAddCircle
  Potential.instIsAddHaarMeasureUnitAddCircleVolume
  Potential.instIsProbabilityMeasureUnitAddCircleVolume

variable {d : Type*} [Fintype d] [LinearOrder (d → ℤ)] {J' : (d → ℤ) → ℝ}

/-- **Georgii Corollary (13.40), first half, for a root at the identity of `G`.** If `Ĵ⁻¹` is
integrable and `Ĵ(1) = ∑_n J(n) = 0` — Georgii's root `z = 1`, the case of all three of his
Examples (13.43)–(13.45) — then `ex 𝒢_Θ(γ^{J,0})` contains uncountably many Gibbs measures with
finite second moment, namely the translates `τ^{c 1}(μ_C)` of the centred Gauss field `μ_C` by
the constant configurations `c ∈ ℝ`, which lie in `M_{J,0}` by
`Potential.const_mem_gaussianMeanSubmodule_of_tsum_eq_zero`.

Each `τ^{c 1}(μ_C)` is *extreme in `𝒢(γ^{J,0})`* by Theorem (13.24), and shift-invariant because
`μ_C` is (its covariance, the limit (13.25), is homogeneous) and a constant translation commutes
with the shifts; extremality in the smaller convex set `𝒢_Θ` follows
(`Set.inter_extremePoints_subset_extremePoints_of_subset`).

The hypothesis that the root be the identity is not cosmetic on this route: if `Ĵ(1) ≠ 0` then a
translate `τ^m(μ_C)` is shift-invariant only for `m = 0`, so `ex 𝒢(γ^{J,0}) ∩ 𝒢_Θ = {μ_C}` and the
further extreme points of `𝒢_Θ` that Georgii produces from a root `z ≠ 1` are *not* extreme in
`𝒢`. Producing them needs his ergodic input — Corollary (7.4) and the unique ergodicity of the
rotation by `z` on the closure of `{z^k : k ∈ ℤ^d}` — which is not in the tree; see the module
docstring. -/
theorem not_countable_setOf_mem_extremePoints_invariantG_memLp
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hint : ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞)
    (hzero : (∑' n, J' n) = 0) :
    ¬ {μ : Measure ((d → ℤ) → ℝ) |
        μ ∈ (invariantG (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
              (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin)
              hPD 1 one_pos) (shiftGroup (d → ℤ) ℝ)).extremePoints ℝ≥0∞ ∧
          ∀ i, MemLp (fun ω : (d → ℤ) → ℝ ↦ ω i) 2 μ}.Countable := by
  classical
  haveI : DecidableEq (d → ℤ) := Classical.decEq _
  set γ := gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
    (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos
    with hγ
  -- `𝒢(γ^{J,0}) ≠ ∅`
  have hM0 : (fun _ ↦ (0 : ℝ)) ∈ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ (0 : ℝ)) := by
    refine ⟨?_, fun i ↦ by simp⟩
    rw [gaussianConvergenceSet_eq_univ_of_finiteRowSupport _
      (finite_setOf_homogeneousCoupling_ne_zero hFin)]
    trivial
  have hG : (G γ).Nonempty :=
    nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top hJ' hint hEven hFin hPD hpos ⟨_, hM0⟩
  -- the limit (13.25) and the Gauss field it defines
  have h27 := bddAbove_gaussianCovEntry_of_nonempty_G (symm_homogeneousCoupling hEven)
    (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD hG
  choose C hC using exists_tendsto_gaussianCovEntry hPD h27
  set μC : Measure ((d → ℤ) → ℝ) :=
    ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) with hμC
  have hgauss : ProbabilityTheory.IsGaussianProcess (fun i (ω : (d → ℤ) → ℝ) ↦ ω i) μC :=
    ProbabilityTheory.isGaussianProcess_gaussianField _
  -- `μ_C` is shift-invariant, because the limit (13.25) is homogeneous
  have hhom : ∀ i j, C i j = C 0 (j - i) := eq_homogeneousCoupling_of_tendsto_gaussianCovEntry hC
  have hμCinv : μC ∈ invariantFields (shiftGroup (d → ℤ) ℝ) :=
    mem_invariantFields_of_isGaussianProcess_homogeneous (c := fun n ↦ C 0 n) hgauss
      (ProbabilityTheory.integral_eval_gaussianField _) fun i j ↦ by
        rw [ProbabilityTheory.covariance_eval_gaussianField]; exact hhom i j
  have hext := extremePoints_G_eq_image_gaussianField (symm_homogeneousCoupling hEven)
    (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD hC hG
  -- the family of constant translates
  set F : ℝ → Measure ((d → ℤ) → ℝ) := fun c ↦ μC.map (fun x ↦ x + fun _ ↦ c) with hF
  have hFinj : Function.Injective F := by
    intro a b hab
    have hinj := injective_map_add_gaussianField (S := d → ℤ)
      (posSemidef_covMatrix_of_tendsto hPD hC)
    have := hinj (a₁ := fun _ ↦ a) (a₂ := fun _ ↦ b) hab
    exact congrFun this 0
  have hFmem : ∀ c : ℝ, F c ∈ {μ : Measure ((d → ℤ) → ℝ) |
      μ ∈ (invariantG γ (shiftGroup (d → ℤ) ℝ)).extremePoints ℝ≥0∞ ∧
        ∀ i, MemLp (fun ω : (d → ℤ) → ℝ ↦ ω i) 2 μ} := by
    intro c
    have hmemc : (fun _ : d → ℤ ↦ c) ∈ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
      := const_mem_gaussianMeanSubmodule_of_tsum_eq_zero hJ' hzero c
    have hexG : F c ∈ (G γ).extremePoints ℝ≥0∞ := by
      rw [hext]
      exact ⟨_, hmemc, rfl⟩
    have hinvF : F c ∈ invariantFields (shiftGroup (d → ℤ) ℝ) :=
      map_add_const_mem_invariantFields hμCinv c
    refine ⟨?_, fun i ↦ ?_⟩
    · exact _root_.inter_extremePoints_subset_extremePoints_of_subset
        (invariantG_subset_G γ (shiftGroup (d → ℤ) ℝ)) ⟨⟨hexG.1, hinvF⟩, hexG⟩
    · have hT : Measurable (fun x : (d → ℤ) → ℝ ↦ x + fun _ ↦ c) := by fun_prop
      rw [hF]
      refine (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
        hT.aemeasurable).2 ?_
      have h1 : MemLp (fun ω : (d → ℤ) → ℝ ↦ ω i) 2 μC :=
        (hgauss.hasGaussianLaw_eval i).memLp_two
      have h2 : MemLp (fun _ : (d → ℤ) → ℝ ↦ c) 2 μC := memLp_const c
      exact h1.add h2
  intro hcount
  have : Countable ℝ :=
    (Equiv.ofInjective _ hFinj).countable_iff.2
      (hcount.mono (by rintro _ ⟨c, rfl⟩; exact hFmem c)).to_subtype
  exact Cardinal.not_countable_real Set.countable_univ

end RootAtIdentity

end Potential

end

end

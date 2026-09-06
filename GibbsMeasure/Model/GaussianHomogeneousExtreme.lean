/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianExtreme
public import GibbsMeasure.Model.GaussianHomogeneous

/-!
# Georgii Theorem (13.36): the necessity half

`GibbsMeasure/Model/GaussianHomogeneous.lean` proves the sufficiency half of Georgii's Theorem
(13.36) — if `M_{J,h} ≠ ∅` and `∫_G Ĵ(z)⁻¹ dz < ∞` then `𝒢(γ^{J,h}) ≠ ∅` — and the necessity of
the spectral integrability for a *Gaussian* Gibbs measure with homogeneous covariance. What was
missing was Georgii's Step 2, which reads the necessity off Theorem (13.24): if
`𝒢(γ^{J,h}) ≠ ∅` then the limits `C(i,j) = lim_Λ 𝒥_Λ⁻¹(i,j)` of (13.25) exist, `C` is homogeneous
and nonnegative definite, and the centred Gauss field `μ_C` with covariance `C` lies in
`𝒢(γ^{J,0})`; Herglotz's lemma then forces `Ĵ⁻¹ dz` to be dominated by a finite measure.

Theorem (13.24) is `GibbsMeasure/Model/GaussianExtreme.lean`. The one genuinely new ingredient
here is the **homogeneity of the limit (13.25)**: for `J(i,j) = J'(j - i)` the matrix `𝒥_{Λ+k}` is
the relabelling of `𝒥_Λ` along `x ↦ x - k`, so `𝒥_{Λ+k}⁻¹(i+k, j+k) = 𝒥_Λ⁻¹(i,j)`, and
`Λ ↦ Λ + k` is cofinal, so the limit inherits the invariance.

## Main results

* `MeasureTheory.GibbsMeasure.gaussianCovEntry_homogeneousCoupling_map_addRight`: `𝒥_Λ⁻¹` is
  translation covariant for a homogeneous coupling.
* `MeasureTheory.GibbsMeasure.gaussianCovEntry_limit_homogeneous` and
  `MeasureTheory.GibbsMeasure.eq_homogeneousCoupling_of_tendsto_gaussianCovEntry`: the limit
  (13.25) is homogeneous, `C(i,j) = C(0, j-i)`.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_nonempty_G`: **Georgii Theorem
  (13.36), the necessity half** — `𝒢(γ^{J,h}) ≠ ∅` implies `∫_G Ĵ(z)⁻¹ dz < ∞`.
* `Potential.nonempty_G_homogeneousCoupling_iff`: **Georgii Theorem (13.36)**, both halves:
  `𝒢(γ^{J,h}) ≠ ∅ ↔ M_{J,h} ≠ ∅ ∧ ∫_G Ĵ(z)⁻¹ dz < ∞`.
* `Potential.not_countable_extremePoints_G_homogeneousCoupling`: **the conclusion Georgii draws in
  Examples (13.43)–(13.45)** — a root of `Ĵ` on `G` together with `𝒢(γ^{J,h}) ≠ ∅` makes
  `ex 𝒢(γ^{J,h})` uncountable. (`GibbsMeasure/Model/GaussianHomogeneous.lean` had this for
  `M_{J,h}`; Theorem (13.24) transports it to `ex 𝒢`.)
* `Potential.not_countable_extremePoints_G_harmonicCrystalCoupling`: **Georgii Example (13.43)
  for `d ≥ 3` as he states it** — the harmonic crystal has uncountably many extreme Gibbs
  measures, permuted by the continuous symmetry `ω ↦ (ω_i + t)_i`.

## What is *not* proved here

The descriptions `𝒢(γ^{J,h}) = {μ_C * ν : ν(M_{J,h}) = 1}` and
`𝒢_Θ(γ^{J,h}) = {μ_C * ν : ν ∈ 𝒫_Θ, ν(M_{J,h}) = 1}` of Theorem (13.36): the first needs the
measurable transport of Theorem (7.26) along the bijection `M_{J,h} ≃ ex 𝒢(γ^{J,h})` (see the
"What is not proved here" section of `GibbsMeasure/Model/GaussianExtreme.lean`), the second needs
in addition Corollary (7.28) and the shift-invariance of a centred Gauss field with homogeneous
covariance.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ## The translation covariance of `𝒥_Λ⁻¹` for a homogeneous coupling -/

section Translation

variable {S : Type*} [AddCommGroup S] [LinearOrder S] {J' : S → ℝ}

/-- The relabelling `Λ + k ≃ Λ`, `x ↦ x - k`. -/
def finsetAddRightEquiv (Λ : Finset S) (k : S) :
    ↥(Λ.map (Equiv.addRight k).toEmbedding) ≃ ↥Λ where
  toFun x := ⟨x.1 - k, by simpa [sub_eq_add_neg] using Finset.mem_map_equiv.1 x.2⟩
  invFun y := ⟨y.1 + k, Finset.mem_map_equiv.2 (by simp)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

omit [LinearOrder S] in
@[simp] lemma coe_finsetAddRightEquiv (Λ : Finset S) (k : S)
    (x : ↥(Λ.map (Equiv.addRight k).toEmbedding)) :
    ((finsetAddRightEquiv Λ k x : ↥Λ) : S) = x.1 - k := rfl

omit [LinearOrder S] in
/-- For a homogeneous coupling `J(i,j) = J'(j - i)`, the interaction matrix of `Λ + k` is the
relabelling of the interaction matrix of `Λ`. -/
theorem gaussianCouplingMatrix_homogeneousCoupling_map_addRight (Λ : Finset S) (k : S) :
    Potential.gaussianCouplingMatrix (Potential.homogeneousCoupling J')
        (Λ.map (Equiv.addRight k).toEmbedding)
      = (Potential.gaussianCouplingMatrix (Potential.homogeneousCoupling J') Λ).submatrix
          (finsetAddRightEquiv Λ k) (finsetAddRightEquiv Λ k) := by
  funext a b
  rw [Matrix.submatrix_apply, Potential.gaussianCouplingMatrix_apply,
    Potential.gaussianCouplingMatrix_apply, Potential.homogeneousCoupling,
    Potential.homogeneousCoupling, coe_finsetAddRightEquiv, coe_finsetAddRightEquiv]
  congr 1
  abel

/-- **The translation covariance of `𝒥_Λ⁻¹`.** For a homogeneous coupling,
`𝒥_{Λ+k}⁻¹(i+k, j+k) = 𝒥_Λ⁻¹(i,j)`. -/
theorem gaussianCovEntry_homogeneousCoupling_map_addRight (Λ : Finset S) (k i j : S) :
    gaussianCovEntry (Potential.homogeneousCoupling J') (Λ.map (Equiv.addRight k).toEmbedding)
        (i + k) (j + k)
      = gaussianCovEntry (Potential.homogeneousCoupling J') Λ i j := by
  classical
  have hmem : ∀ x : S, x + k ∈ Λ.map (Equiv.addRight k).toEmbedding ↔ x ∈ Λ := by
    intro x
    rw [Finset.mem_map_equiv]
    simp
  by_cases hij : i ∈ Λ ∧ j ∈ Λ
  · have hi' : i + k ∈ Λ.map (Equiv.addRight k).toEmbedding := (hmem i).2 hij.1
    have hj' : j + k ∈ Λ.map (Equiv.addRight k).toEmbedding := (hmem j).2 hij.2
    have ha : finsetAddRightEquiv Λ k ⟨i + k, hi'⟩ = ⟨i, hij.1⟩ := Subtype.ext (by simp)
    have hb : finsetAddRightEquiv Λ k ⟨j + k, hj'⟩ = ⟨j, hij.2⟩ := Subtype.ext (by simp)
    rw [gaussianCovEntry_of_mem hi' hj', gaussianCovEntry_of_mem hij.1 hij.2,
      gaussianCouplingMatrix_homogeneousCoupling_map_addRight Λ k,
      Matrix.inv_submatrix_equiv, Matrix.submatrix_apply, ha, hb]
  · rcases not_and_or.1 hij with hi | hj
    · rw [gaussianCovEntry_of_notMem_left hi,
        gaussianCovEntry_of_notMem_left (fun hc ↦ hi ((hmem i).1 hc))]
    · rw [gaussianCovEntry_of_notMem_right hj,
        gaussianCovEntry_of_notMem_right (fun hc ↦ hj ((hmem j).1 hc))]

omit [LinearOrder S] in
/-- The translation `Λ ↦ Λ + k` is cofinal in the finite volumes. -/
theorem tendsto_finset_map_addRight_atTop (k : S) :
    Tendsto (fun Λ : Finset S ↦ Λ.map (Equiv.addRight k).toEmbedding) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun Δ ↦ ⟨Δ.map (Equiv.addRight (-k)).toEmbedding, fun Λ hΛ ↦ ?_⟩
  intro x hx
  refine Finset.mem_map_equiv.2 (hΛ (Finset.mem_map_equiv.2 ?_))
  simpa using hx

/-- **The limit (13.25) of a homogeneous coupling is homogeneous.** -/
theorem gaussianCovEntry_limit_homogeneous {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦
      gaussianCovEntry (Potential.homogeneousCoupling J') Λ i j) atTop (𝓝 (C i j)))
    (i j k : S) : C (i + k) (j + k) = C i j := by
  refine tendsto_nhds_unique ?_ (hC i j)
  refine ((hC (i + k) (j + k)).comp (tendsto_finset_map_addRight_atTop k)).congr fun Λ ↦ ?_
  exact gaussianCovEntry_homogeneousCoupling_map_addRight Λ k i j

/-- **The limit (13.25) of a homogeneous coupling is homogeneous**, in the form
`C = homogeneousCoupling c` with `c n = C(0, n)`. -/
theorem eq_homogeneousCoupling_of_tendsto_gaussianCovEntry {C : S → S → ℝ}
    (hC : ∀ i j, Tendsto (fun Λ : Finset S ↦
      gaussianCovEntry (Potential.homogeneousCoupling J') Λ i j) atTop (𝓝 (C i j)))
    (i j : S) : C i j = C 0 (j - i) := by
  have h := gaussianCovEntry_limit_homogeneous hC 0 (j - i) i
  rw [zero_add, sub_add_cancel] at h
  exact h

end Translation

end MeasureTheory.GibbsMeasure

namespace Potential

open MeasureTheory.GibbsMeasure

/-! ## Georgii Theorem (13.36), the necessity half -/

section Necessity

open UnitAddTorus

attribute [local instance] Potential.instMeasureSpaceUnitAddCircle
  Potential.instIsAddHaarMeasureUnitAddCircleVolume
  Potential.instIsProbabilityMeasureUnitAddCircleVolume

variable {d : Type*} [Fintype d] [LinearOrder (d → ℤ)] {J' : (d → ℤ) → ℝ} {h : ℝ}
  (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
  (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
  (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)

include hJ' hEven hFin hPD hpos

/-- **Georgii Theorem (13.36), the necessity half.** If `𝒢(γ^{J,h}) ≠ ∅` for a homogeneous,
absolutely summable, finite-range `J` with `Ĵ ≥ 0`, then `∫_G Ĵ(z)⁻¹ dz < ∞`.

Georgii's Step 2. Theorem (13.24) —
`MeasureTheory.GibbsMeasure.bddAbove_gaussianCovEntry_of_nonempty_G` and
`MeasureTheory.GibbsMeasure.tendsto_gaussianCovEntry_of_mem_extremePoints_G` — gives the
limits `C(i,j) = lim_Λ 𝒥_Λ⁻¹(i,j)` of (13.25); these are homogeneous
(`MeasureTheory.GibbsMeasure.eq_homogeneousCoupling_of_tendsto_gaussianCovEntry`), nonnegative
definite and an inverse of `J`, so the centred Gauss field `μ_C` with covariance `C` is a Gibbs
measure for `γ^{J,0}` and Herglotz's lemma applies to it. -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_nonempty_G
    (hG : (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
      (fun _ ↦ h) (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos)).Nonempty) :
    ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞ := by
  classical
  -- (13.27), hence the limits (13.25)
  have h27 := bddAbove_gaussianCovEntry_of_nonempty_G (symm_homogeneousCoupling hEven)
    (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD hG
  choose C hC using exists_tendsto_gaussianCovEntry hPD h27
  -- the limit is homogeneous
  have hhom : ∀ i j, C i j = C 0 (j - i) := eq_homogeneousCoupling_of_tendsto_gaussianCovEntry hC
  -- the centred Gauss field with covariance `C`
  set μC : Measure ((d → ℤ) → ℝ) :=
    ProbabilityTheory.gaussianField C (posSemidef_covMatrix_of_tendsto hPD hC) with hμC
  have hzero : (fun _ ↦ (0 : ℝ)) ∈
      gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ (0 : ℝ)) := by
    refine ⟨?_, fun i ↦ by simp⟩
    rw [gaussianConvergenceSet_eq_univ_of_finiteRowSupport _
      (finite_setOf_homogeneousCoupling_ne_zero hFin)]
    trivial
  have hmean : ∀ i, ∫ ω, ω i ∂μC = 0 :=
    ProbabilityTheory.integral_eval_gaussianField _
  have hGibbs : (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1
      one_pos).IsGibbsMeasure μC := by
    refine isGibbsMeasure_of_isGaussianProcess_covariance_eq (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD hC
      (ProbabilityTheory.isGaussianProcess_gaussianField _)
      (ProbabilityTheory.covariance_eval_gaussianField _) ?_
    simpa only [hmean] using hzero
  refine lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_isGibbsMeasure (c := fun n ↦ C 0 n)
    hJ' hEven hFin hPD hpos (ProbabilityTheory.isGaussianProcess_gaussianField _) hmean
    (fun i j ↦ ?_) hGibbs
  rw [ProbabilityTheory.covariance_eval_gaussianField]
  exact hhom i j

/-- **Georgii Theorem (13.36)**, both halves: for `S = ℤ^d` and a homogeneous, absolutely
summable, finite-range, positive definite `J`,

`𝒢(γ^{J,h}) ≠ ∅` **iff** `M_{J,h} ≠ ∅` and `∫_G Ĵ(z)⁻¹ dz < ∞`.

Sufficiency is `Potential.nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top`; necessity is
the previous theorem together with Theorem (13.24)
(`MeasureTheory.GibbsMeasure.nonempty_gaussianMeanSet_of_nonempty_G`). -/
theorem nonempty_G_homogeneousCoupling_iff :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
        (fun _ ↦ h) (symm_homogeneousCoupling hEven)
        (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos)).Nonempty ↔
      (gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h)).Nonempty ∧
        ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞ := by
  refine ⟨fun hG ↦ ⟨MeasureTheory.GibbsMeasure.nonempty_gaussianMeanSet_of_nonempty_G
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD hG,
    lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_nonempty_G hJ' hEven hFin hPD hpos hG⟩,
    fun ⟨hM, hint⟩ ↦ ?_⟩
  exact nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top hJ' hint hEven hFin hPD hpos hM

end Necessity

/-! ## Uncountably many extreme Gibbs measures from a root of `Ĵ` -/

section Uncountable

variable {d : Type*} [Fintype d] [LinearOrder (d → ℤ)] {J' : (d → ℤ) → ℝ} {h : (d → ℤ) → ℝ}
  (hEven : ∀ n, J' (-n) = J' n)
  (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)

include hEven hPD

/-- **Georgii's conclusion in Examples (13.43)–(13.45).** If `Ĵ` has a root on `G` and
`𝒢(γ^{J,h}) ≠ ∅` then `ex 𝒢(γ^{J,h})` is *uncountable*: the root gives a non-zero element
`m = (Re z^i)_i` of `M_{J,0}` (Georgii's Step 2 in the proof of Remark (13.39)), so `M_{J,h}` is
uncountable, and Theorem (13.24) puts it in bijection with `ex 𝒢(γ^{J,h})`.

This is the strengthening, from `M_{J,h}` to `ex 𝒢(γ^{J,h})`, of
`Potential.not_countable_gaussianMeanSet_homogeneousCoupling`. -/
theorem not_countable_extremePoints_G_homogeneousCoupling
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite) (hJ' : Summable fun n ↦ |J' n|)
    {z : UnitAddTorus d} (hz : fourierHomogeneousCoupling J' z = 0)
    (hG : (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J') h
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1
      one_pos)).Nonempty) :
    ¬ ((MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J') h
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1
      one_pos)).extremePoints ℝ≥0∞).Countable :=
  MeasureTheory.GibbsMeasure.not_countable_extremePoints_G (symm_homogeneousCoupling hEven)
    (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD
    (re_mFourier_mem_gaussianMeanSubmodule hJ' hz) (re_mFourier_ne_zero z) hG

end Uncountable

section HarmonicCrystal

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [LinearOrder (d → ℤ)] {β : ℝ}

/-- **Georgii Example (13.43) for `d ≥ 3`, as he states it**: the harmonic crystal on `ℤ^d`,
`d ≥ 3`, has *uncountably many* extreme Gibbs measures, permuted by the continuous symmetry
`ω ↦ (ω_i + t)_{i ∈ S}` of `γ^{J,0}`.

`Ĵ(1) = 0` for the harmonic crystal, so the identity of `G` is a root of `Ĵ` and the constants lie
in `M_{J,0}`; `∫_G Ĵ⁻¹ dz < ∞` for `d ≥ 3` gives `𝒢(γ^{J,0}) ≠ ∅`
(`Potential.nonempty_G_harmonicCrystalCoupling`); Theorem (13.24) then makes
`ex 𝒢(γ^{J,0})` a copy of the uncountable `M_{J,0}`. -/
theorem not_countable_extremePoints_G_harmonicCrystalCoupling (hβ : 0 < β)
    (hd : 3 ≤ Fintype.card d) :
    ¬ ((MeasureTheory.GibbsMeasure.G (gaussianSpecification
      (homogeneousCoupling (harmonicCrystalCoupling d β)) (fun _ ↦ (0 : ℝ))
      (symm_homogeneousCoupling harmonicCrystalCoupling_neg)
      (finite_setOf_homogeneousCoupling_ne_zero finite_setOf_harmonicCrystalCoupling_ne_zero)
      (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ) 1
      one_pos)).extremePoints ℝ≥0∞).Countable := by
  refine MeasureTheory.GibbsMeasure.not_countable_extremePoints_G _ _ _
    (m := fun _ ↦ (1 : ℝ)) ?_ ?_ (nonempty_G_harmonicCrystalCoupling hβ hd)
  · exact const_mem_gaussianMeanSubmodule_of_tsum_eq_zero summable_abs_harmonicCrystalCoupling
      tsum_harmonicCrystalCoupling 1
  · intro hc
    have := congrFun hc (0 : d → ℤ)
    norm_num at this

end HarmonicCrystal

end Potential

end

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianHomogeneous
public import GibbsMeasure.Model.GaussianField
public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Reindex
public import GibbsMeasure.Specification.ErgodicGibbs

/-!
# Georgii's remark preceding Corollary (13.42), and the `𝒢_Θ` form of the corollary

"Recall that a centred Gauss field `μ` is shift-invariant if and only if its covariance function
`C` is homogeneous." Both directions are proved here:

* if `C(i,j) = c(j - i)` then `μ = μ_C` is invariant under every shift `θ_k : ω ↦ (ω_{i-k})_i`,
  because `θ_k` reindexes the coordinates by `i ↦ i - k`, the pushforward of a Gauss field along
  a coordinate reindexing is the Gauss field of the reindexed covariance
  (`ProbabilityTheory.map_comp_gaussianField`), and `C(a-k, b-k) = C(a,b)`;
* conversely, shift invariance transports the covariance, `C(i,j) = C(i-k, j-k)`, and `k = i`
  gives `C(i,j) = C(0, j-i)`.

With that, Georgii's Corollary (13.42) — proved in
`GibbsMeasure/Model/GaussianHomogeneous.lean` in the form
`μ ∈ 𝒢(γ^{J,0}) ↔ α = Ĵ⁻¹ dz + α₀` — takes the shape he gives it, with `𝒢_Θ(γ^{J,0})` on the
left: for a *centred Gauss field with homogeneous covariance* the two memberships agree.

## Main results

* `ProbabilityTheory.map_shift_gaussianField_homogeneous`: `θ_k(μ_C) = μ_C` for a homogeneous
  covariance function.
* `MeasureTheory.GibbsMeasure.mem_invariantFields_of_isGaussianProcess_homogeneous`: **a centred
  Gauss field with homogeneous covariance is shift-invariant.**
* `MeasureTheory.GibbsMeasure.covariance_eval_sub_of_smulInvariantMeasure`: the converse — a
  shift-invariant random field has a homogeneous covariance function.
* `Potential.mem_invariantG_iff_exists_spectralMeasure_decomposition`: **Georgii Corollary
  (13.42) as he states it**, with `𝒢_Θ(γ^{J,0})`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Set

noncomputable section

/-! ### Shift invariance of a centred Gauss field with homogeneous covariance -/

namespace ProbabilityTheory

variable {S : Type*} [AddCommGroup S] [DecidableEq S] {c : S → ℝ}

/-- **The shift `θ_k` leaves the centred Gauss field with homogeneous covariance invariant.**
`θ_k` is the coordinate reindexing `i ↦ i - k`, under which a homogeneous covariance function is
unchanged. -/
theorem map_shift_gaussianField_homogeneous
    (hC : ∀ I : Finset S, (covMatrix (Potential.homogeneousCoupling c) I).PosSemidef) (k : S) :
    (gaussianField (Potential.homogeneousCoupling c) hC).map
        (MeasureTheory.GibbsMeasure.shift ℝ k).toFun
      = gaussianField (Potential.homogeneousCoupling c) hC := by
  have hfun : (MeasureTheory.GibbsMeasure.shift ℝ k).toFun
      = fun ω : S → ℝ ↦ ω ∘ fun i ↦ i - k := by
    funext ω i
    simp [MeasureTheory.GibbsMeasure.shift_toFun_apply]
  rw [hfun]
  refine map_comp_gaussianField_self _ hC fun a b ↦ ?_
  simp only [Potential.homogeneousCoupling_apply]
  congr 1
  abel

end ProbabilityTheory

namespace MeasureTheory.GibbsMeasure

variable {S : Type*} [AddCommGroup S] {μ : Measure (S → ℝ)}

/-- **A shift-invariant random field has a homogeneous covariance function** — the "only if" half
of Georgii's remark preceding Corollary (13.42). Shifting by `k` replaces the pair of sites
`(i, j)` by `(i - k, j - k)`, so the covariance depends on `j - i` alone. -/
theorem covariance_eval_sub_of_smulInvariantMeasure
    (hμ : ∀ k : S, MeasurePreserving (shift ℝ k).toFun μ μ) (i j : S) :
    cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ]
      = cov[fun ω : S → ℝ ↦ ω 0, fun ω : S → ℝ ↦ ω (j - i); μ] := by
  have hmeas : Measurable (shift ℝ i).toFun := Transformation.measurable_toFun _
  have hmap : μ.map (shift ℝ i).toFun = μ := (hμ i).map_eq
  calc cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ]
      = cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ.map (shift ℝ i).toFun] := by rw [hmap]
    _ = cov[(fun ω : S → ℝ ↦ ω i) ∘ (shift ℝ i).toFun,
          (fun ω : S → ℝ ↦ ω j) ∘ (shift ℝ i).toFun; μ] :=
        covariance_map (Measurable.aestronglyMeasurable (by fun_prop))
          (Measurable.aestronglyMeasurable (by fun_prop)) hmeas.aemeasurable
    _ = cov[fun ω : S → ℝ ↦ ω 0, fun ω : S → ℝ ↦ ω (j - i); μ] := by
        simp only [Function.comp_def, shift_toFun_apply, sub_self]

variable [DecidableEq S] {c : S → ℝ}

/-- **A centred Gauss field with homogeneous covariance is shift-invariant** — the "if" half of
Georgii's remark preceding Corollary (13.42). -/
theorem mem_invariantFields_of_isGaussianProcess_homogeneous
    (hμ : IsGaussianProcess (fun i (ω : S → ℝ) ↦ ω i) μ) (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : S → ℝ ↦ ω i, fun ω : S → ℝ ↦ ω j; μ] = c (j - i)) :
    μ ∈ invariantFields (shiftGroup S ℝ) := by
  have hprob := hμ.isProbabilityMeasure
  have hC : ∀ I : Finset S, (covMatrix (Potential.homogeneousCoupling c) I).PosSemidef := by
    intro I
    have hEq : covMatrix (Potential.homogeneousCoupling c) I
        = Matrix.of fun a b : I ↦ cov[fun ω : S → ℝ ↦ ω a.1, fun ω : S → ℝ ↦ ω b.1; μ] := by
      funext a b
      exact (hcov a.1 b.1).symm
    rw [hEq]
    exact Matrix.PosSemidef.submatrix (posSemidef_covar_of_isGaussianProcess hμ)
      fun a : I ↦ (a : S)
  have hμeq : μ = gaussianField (Potential.homogeneousCoupling c) hC :=
    eq_gaussianField hC hμ hmean fun i j ↦ hcov i j
  refine mem_invariantFields_shiftGroup.2 ⟨hprob, fun k ↦ ?_⟩
  refine ⟨Transformation.measurable_toFun _, ?_⟩
  rw [hμeq]
  exact ProbabilityTheory.map_shift_gaussianField_homogeneous hC k

end MeasureTheory.GibbsMeasure

/-! ### Georgii Corollary (13.42) with `𝒢_Θ` -/

namespace Potential

open UnitAddTorus MeasureTheory.GibbsMeasure

/-- Normalised Haar measure on `ℝ/ℤ`, as in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`. -/
local instance instMeasureSpaceUnitAddCircleShiftInv : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance instIsAddHaarMeasureVolumeShiftInv :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance instIsProbabilityMeasureVolumeShiftInv :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d] [DecidableEq (d → ℤ)] [LinearOrder (d → ℤ)]
  {J' c : (d → ℤ) → ℝ}

/-- **Georgii Corollary (13.42), as he states it.** Let `μ` be a *shift-invariant* centred Gauss
field on `ℤ^d`, i.e. (by the remark preceding the corollary, proved here as
`MeasureTheory.GibbsMeasure.mem_invariantFields_of_isGaussianProcess_homogeneous` and
`MeasureTheory.GibbsMeasure.covariance_eval_sub_of_smulInvariantMeasure`) a centred Gauss field
whose covariance function is homogeneous, `cov[σ_i, σ_j] = c(j-i)`. Then
`μ ∈ 𝒢_Θ(γ^{J,0})` if and only if its spectral measure `α` decomposes as
`α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`.

The membership in `𝒢_Θ` rather than `𝒢` costs nothing beyond the remark: such a `μ` is
automatically shift-invariant. -/
theorem mem_invariantG_iff_exists_spectralMeasure_decomposition
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    {μ : Measure ((d → ℤ) → ℝ)}
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : (d → ℤ) → ℝ) ↦ ω i) μ)
    (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : (d → ℤ) → ℝ ↦ ω i, fun ω : (d → ℤ) → ℝ ↦ ω j; μ] = c (j - i)) :
    μ ∈ invariantG
        (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
          (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin)
          hPD 1 one_pos)
        (shiftGroup (d → ℤ) ℝ)
      ↔ ∃ α : Measure (UnitAddTorus d), IsFiniteMeasure α ∧
          (∀ n, ∫ z, mFourier n z ∂α = (c n : ℂ)) ∧
          ∃ α₀ : Measure (UnitAddTorus d),
            α₀ {z | (fourierHomogeneousCoupling J' z).re ≠ 0} = 0
              ∧ α = spectralMeasure J' + α₀ := by
  have hprob := hμ.isProbabilityMeasure
  have hinv : μ ∈ invariantFields (shiftGroup (d → ℤ) ℝ) :=
    mem_invariantFields_of_isGaussianProcess_homogeneous hμ hmean hcov
  rw [← isGibbsMeasure_iff_exists_spectralMeasure_decomposition hJ' hEven hFin hPD hpos hμ hmean
    hcov]
  exact ⟨fun h ↦ h.1.2, fun h ↦ ⟨⟨hprob, h⟩, hinv⟩⟩

end Potential

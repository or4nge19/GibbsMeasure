/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.KolmogorovExtension
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Existence of a centred Gaussian process with prescribed covariance

Given an index type `ι` and a *covariance kernel* `C : ι → ι → ℝ` all of whose finite submatrices
`(C i j)_{i, j ∈ I}` are positive semidefinite, this file constructs a probability measure
`gaussianField C hC` on `ι → ℝ` under which the coordinate process `ω ↦ (ω i)_{i ∈ ι}` is a
centred Gaussian process with covariance `C`.

The construction is the classical one: the finite-dimensional marginals are the centred
multivariate Gaussian measures `ProbabilityTheory.multivariateGaussian 0 (covMatrix C I)`
(transported from `EuclideanSpace ℝ I` to `I → ℝ`), they form a projective family by
`ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian`, and they are glued by the
Kolmogorov extension theorem `MeasureTheory.projectiveLimit`.

Degeneracy is allowed: `multivariateGaussian` is defined through the characteristic function
`exp (-x ⬝ᵥ S *ᵥ x / 2)` (concretely, as the pushforward of a standard Gaussian along
`CFC.sqrt S`), so a merely positive *semi*definite `C` — which has no Lebesgue density — is
covered.

## Main definitions

* `ProbabilityTheory.covMatrix C I`: the finite submatrix `(C i j)_{i, j ∈ I}`.
* `ProbabilityTheory.gaussianProjectiveFamily C I`: the centred Gaussian measure on `I → ℝ` with
  covariance matrix `covMatrix C I`.
* `ProbabilityTheory.gaussianField C hC`: the centred Gaussian measure on `ι → ℝ` with covariance
  kernel `C`.

## Main statements

* `ProbabilityTheory.isProjectiveMeasureFamily_gaussianProjectiveFamily`: the finite-dimensional
  marginals are consistent.
* `ProbabilityTheory.isGaussianProcess_gaussianField`: the coordinate process is Gaussian.
* `ProbabilityTheory.integral_eval_gaussianField`: it is centred.
* `ProbabilityTheory.covariance_eval_gaussianField`: its covariance is `C`.
* `ProbabilityTheory.eq_gaussianField`: uniqueness — any centred Gaussian process on `ι → ℝ` with
  covariance `C` *is* `gaussianField C hC`.
* `ProbabilityTheory.exists_isGaussianProcess_covariance_eq` and
  `ProbabilityTheory.existsUnique_isGaussianProcess_covariance_eq`: Georgii's Proposition (13.A7).

## Relation to `ProbabilityTheory.BrownianReal`

Mathlib's `Mathlib/Probability/BrownianMotion/GaussianProjectiveFamily.lean` builds the
finite-dimensional distributions of real Brownian motion by exactly this construction, at the
single covariance kernel `C s t = min s t` on `ℝ≥0`. The family here subsumes it: `covMatrix`
and `gaussianProjectiveFamily` specialise to `BrownianReal.covMatrix` and
`BrownianReal.projectiveFamily` definitionally
(`ProbabilityTheory.BrownianReal.covMatrix_eq_covMatrix`,
`ProbabilityTheory.BrownianReal.projectiveFamily_eq_gaussianProjectiveFamily`), and, since
`Mathlib` has no Kolmogorov extension theorem yet, `gaussianField` at that kernel supplies the
measure on `ℝ≥0 → ℝ` that `BrownianReal.projectiveFamily` was built to be extended to
(`ProbabilityTheory.BrownianReal.isProjectiveLimit_gaussianField`). Only the covariance kernel is
special there; nothing else in that file is.

## Tags

Gaussian process, covariance, Kolmogorov extension
-/

@[expose] public section

open MeasureTheory NormedSpace Set WithLp Matrix

open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {ι : Type*} {C : ι → ι → ℝ} {I J : Finset ι}

section CovMatrix

/-- The finite submatrix `(C i j)_{i, j ∈ I}` of a covariance kernel `C : ι → ι → ℝ`. -/
def covMatrix (C : ι → ι → ℝ) (I : Finset ι) : Matrix I I ℝ := .of fun i j ↦ C i j

@[simp]
lemma covMatrix_apply (C : ι → ι → ℝ) (I : Finset ι) (i j : I) :
    covMatrix C I i j = C i j := rfl

lemma covMatrix_submatrix (C : ι → ι → ℝ) (hJI : J ⊆ I) :
    (covMatrix C I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
      covMatrix C J := rfl

end CovMatrix

section ProjectiveFamily

variable [DecidableEq ι]

/-- The finite-dimensional marginal of the centred Gaussian field with covariance kernel `C`: the
centred Gaussian measure on `I → ℝ` with covariance matrix `covMatrix C I`.

As in `ProbabilityTheory.BrownianReal.projectiveFamily`, the measure is built on `I → ℝ` rather
than on `EuclideanSpace ℝ I`, because the Kolmogorov extension theorem is phrased for measures on
pi types. -/
noncomputable def gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) : Measure (I → ℝ) :=
  (multivariateGaussian 0 (covMatrix C I)).map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/-- Up to a measurable equivalence, `gaussianProjectiveFamily C I` is the centred multivariate
Gaussian measure with covariance matrix `covMatrix C I`. -/
lemma measurePreserving_ofLp_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) :
    MeasurePreserving ofLp (multivariateGaussian 0 (covMatrix C I))
      (gaussianProjectiveFamily C I) where
  measurable := by fun_prop
  map_eq := rfl

/-- Up to a measurable equivalence, `gaussianProjectiveFamily C I` is the centred multivariate
Gaussian measure with covariance matrix `covMatrix C I`. -/
lemma measurePreserving_toLp_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) :
    MeasurePreserving (toLp 2) (gaussianProjectiveFamily C I)
      (multivariateGaussian 0 (covMatrix C I)) where
  measurable := by fun_prop
  map_eq := by
    rw [gaussianProjectiveFamily, Measure.map_map]
    · simp [← MeasurableEquiv.coe_toLp]
    all_goals fun_prop

instance isGaussian_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) :
    IsGaussian (gaussianProjectiveFamily C I) := by
  rw [gaussianProjectiveFamily,
    show ⇑(MeasurableEquiv.toLp 2 (I → ℝ)).symm = ⇑(EuclideanSpace.equiv I ℝ) from rfl]
  infer_instance

lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ι → ι → ℝ) (I : Finset ι) (f : (I → ℝ) → E) :
    ∫ x, f x ∂gaussianProjectiveFamily C I =
      ∫ x, f (ofLp x) ∂multivariateGaussian 0 (covMatrix C I) := by
  simp [gaussianProjectiveFamily, integral_map_equiv]

@[to_fun covariance_fun_gaussianProjectiveFamily]
lemma covariance_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) (f g : (I → ℝ) → ℝ) :
    cov[f, g; gaussianProjectiveFamily C I] =
      cov[f ∘ ofLp, g ∘ ofLp; multivariateGaussian 0 (covMatrix C I)] := by
  rw [gaussianProjectiveFamily, covariance_map_equiv]
  rfl

@[simp]
lemma integral_id_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) :
    ∫ x, x ∂(gaussianProjectiveFamily C I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← PiLp.coe_continuousLinearEquiv 2 ℝ,
    ContinuousLinearEquiv.integral_comp_id_comm, integral_id_multivariateGaussian, map_zero]

/-- The finite-dimensional marginals of the centred Gaussian field are centred. -/
@[simp]
lemma integral_eval_gaussianProjectiveFamily (C : ι → ι → ℝ) (I : Finset ι) (i : I) :
    ∫ x, x i ∂(gaussianProjectiveFamily C I) = 0 := by
  conv => enter [1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) i x
  rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
  exact IsGaussian.integrable_id

/-- The covariance of two coordinates under `gaussianProjectiveFamily C I` is the corresponding
entry of `C`, provided the submatrix `covMatrix C I` is positive semidefinite. -/
lemma covariance_eval_gaussianProjectiveFamily (hC : (covMatrix C I).PosSemidef) (i j : I) :
    cov[fun x ↦ x i, fun x ↦ x j; gaussianProjectiveFamily C I] = C i j := by
  rw [covariance_fun_gaussianProjectiveFamily, covariance_eval_multivariateGaussian hC,
    covMatrix_apply]

/-- **The finite-dimensional centred Gaussian marginals are consistent.** Restricting
`gaussianProjectiveFamily C I` to the coordinates in `J ⊆ I` gives `gaussianProjectiveFamily C J`.

This is Georgii's consistency step in Proposition (13.A7): by (13.A1) the `J`-projection of a
centred Gaussian with covariance `C_I` is centred Gaussian with covariance `C_J`. -/
lemma isProjectiveMeasureFamily_gaussianProjectiveFamily
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) :
    IsProjectiveMeasureFamily (α := fun _ : ι ↦ ℝ) (gaussianProjectiveFamily C) := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have h : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        ofLp ∘ (EuclideanSpace.restrict₂ hJI) := by ext; simp
    rw [h, ((measurePreserving_ofLp_gaussianProjectiveFamily C J).comp
      (measurePreserving_restrict₂_multivariateGaussian (hC I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _
  · fun_prop

end ProjectiveFamily

section GaussianField

variable [DecidableEq ι]

/-- **Georgii's Proposition (13.A7)**: the centred Gaussian field on `ι → ℝ` with covariance
kernel `C`, obtained from the finite-dimensional marginals `gaussianProjectiveFamily C I` by the
Kolmogorov extension theorem.

The hypothesis is that every finite submatrix `(C i j)_{i, j ∈ I}` is positive semidefinite; note
that `Matrix.PosSemidef` includes hermiticity, so `C` is in particular symmetric. Degenerate
submatrices are allowed. -/
noncomputable def gaussianField (C : ι → ι → ℝ)
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) : Measure (ι → ℝ) :=
  MeasureTheory.projectiveLimit (α := fun _ : ι ↦ ℝ) (gaussianProjectiveFamily C)
    (isProjectiveMeasureFamily_gaussianProjectiveFamily hC)

variable (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef)

/-- The finite-dimensional marginals of `gaussianField C hC` are the centred multivariate
Gaussians `gaussianProjectiveFamily C I`. -/
lemma isProjectiveLimit_gaussianField :
    IsProjectiveLimit (gaussianField C hC) (gaussianProjectiveFamily C) :=
  MeasureTheory.isProjectiveLimit_projectiveLimit _

instance isProbabilityMeasure_gaussianField : IsProbabilityMeasure (gaussianField C hC) :=
  (isProjectiveLimit_gaussianField hC).isProbabilityMeasure

/-- **The coordinate process of `gaussianField C hC` is a Gaussian process.** -/
theorem isGaussianProcess_gaussianField :
    IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) (gaussianField C hC) where
  hasGaussianLaw I := by
    constructor
    rw [show (fun ω : ι → ℝ ↦ I.restrict fun i ↦ ω i) = I.restrict from rfl,
      isProjectiveLimit_gaussianField hC I]
    infer_instance

/-- **`gaussianField C hC` is centred.** -/
@[simp]
theorem integral_eval_gaussianField (i : ι) : ∫ ω, ω i ∂(gaussianField C hC) = 0 := by
  have hmem : i ∈ ({i} : Finset ι) := Finset.mem_singleton_self i
  have h := integral_eval_gaussianProjectiveFamily C {i} ⟨i, hmem⟩
  rw [← isProjectiveLimit_gaussianField hC {i},
    integral_map (Finset.measurable_restrict _).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))] at h
  exact h

/-- **The covariance function of `gaussianField C hC` is `C`.** -/
theorem covariance_eval_gaussianField (i j : ι) :
    cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; gaussianField C hC] = C i j := by
  have hi : i ∈ ({i, j} : Finset ι) := by simp
  have hj : j ∈ ({i, j} : Finset ι) := by simp
  calc cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; gaussianField C hC]
      = cov[(fun x : (({i, j} : Finset ι) → ℝ) ↦ x ⟨i, hi⟩) ∘ ({i, j} : Finset ι).restrict,
          (fun x : (({i, j} : Finset ι) → ℝ) ↦ x ⟨j, hj⟩) ∘ ({i, j} : Finset ι).restrict;
          gaussianField C hC] := rfl
    _ = cov[fun x : (({i, j} : Finset ι) → ℝ) ↦ x ⟨i, hi⟩,
          fun x : (({i, j} : Finset ι) → ℝ) ↦ x ⟨j, hj⟩;
          (gaussianField C hC).map ({i, j} : Finset ι).restrict] :=
        (covariance_map (Measurable.aestronglyMeasurable (by fun_prop))
          (Measurable.aestronglyMeasurable (by fun_prop))
          (Finset.measurable_restrict _).aemeasurable).symm
    _ = C i j := by
        rw [isProjectiveLimit_gaussianField hC]
        exact covariance_eval_gaussianProjectiveFamily (hC _) _ _

end GaussianField

section Uniqueness

variable [DecidableEq ι] {μ : Measure (ι → ℝ)}

/-- **The finite-dimensional marginals of a centred Gaussian process with covariance `C` are the
centred multivariate Gaussians of the submatrices of `C`.** This is Georgii's (13.A1)-based
identification of `σ_Λ(μ)`, in the form needed for the uniqueness half of Proposition (13.A7). -/
theorem map_restrict_eq_gaussianProjectiveFamily
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ)
    (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = C i j)
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) (I : Finset ι) :
    μ.map I.restrict = gaussianProjectiveFamily C I := by
  set e : (I → ℝ) ≃L[ℝ] EuclideanSpace ℝ I := (EuclideanSpace.equiv I ℝ).symm with he
  have hres : IsGaussian (μ.map I.restrict) := (hμ.hasGaussianLaw I).isGaussian_map
  have hemeas : Measurable (fun x : I → ℝ ↦ e x) := e.continuous.measurable
  have hmap : μ.map (fun ω ↦ e (I.restrict ω)) = (μ.map I.restrict).map (fun x ↦ e x) :=
    (Measure.map_map hemeas (Finset.measurable_restrict _)).symm
  have hgauss : IsGaussian (μ.map fun ω ↦ e (I.restrict ω)) := by
    rw [hmap, show (fun x : I → ℝ ↦ e x) = ⇑(e : (I → ℝ) →L[ℝ] EuclideanSpace ℝ I) from rfl]
    infer_instance
  have hmean' : ∫ x, x ∂(μ.map I.restrict) = 0 := by
    have hint : Integrable id (μ.map I.restrict) := IsGaussian.integrable_id
    funext i
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I ↦ ℝ) i).integral_comp_id_comm
      hint
    rw [Pi.zero_apply, show (∫ x, x ∂(μ.map I.restrict)) i
      = ∫ x, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I ↦ ℝ) i) x ∂(μ.map I.restrict)
      from hproj.symm, integral_map (Finset.measurable_restrict _).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    exact hmean i
  have key : μ.map (fun ω ↦ e (I.restrict ω)) = multivariateGaussian 0 (covMatrix C I) := by
    refine IsGaussian.ext ?_ ?_
    · rw [integral_id_multivariateGaussian', hmap]
      show ∫ x, x ∂((μ.map I.restrict).map fun x ↦ e x) = 0
      rw [show (fun x : I → ℝ ↦ e x) = ⇑e from rfl, ContinuousLinearEquiv.integral_id_map,
        hmean', map_zero]
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun I ℝ).toBasis fun i j ↦ ?_
      rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
        covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
        covarianceBilin_multivariateGaussian (hC I),
        covariance_map (Measurable.aestronglyMeasurable (by fun_prop))
          (Measurable.aestronglyMeasurable (by fun_prop)) (by fun_prop)]
      have hb (k : I) : (fun u : EuclideanSpace ℝ I ↦
          ⟪(EuclideanSpace.basisFun I ℝ).toBasis k, u⟫) ∘ (fun ω : ι → ℝ ↦ e (I.restrict ω))
          = fun ω : ι → ℝ ↦ ω k := by
        ext ω
        simp [he, PiLp.inner_apply]
      simp_rw [hb, hcov]
      simp
  rw [gaussianProjectiveFamily, ← key, hmap, Measure.map_map (by fun_prop) hemeas]
  simp [he, Function.comp_def, Measure.map_id']

/-- **Georgii's Proposition (13.A7), uniqueness part.** A probability measure on `ι → ℝ` under
which the coordinate process is a centred Gaussian process with covariance `C` is
`gaussianField C hC`. -/
theorem eq_gaussianField (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef)
    (hμ : IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ)
    (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = C i j) :
    μ = gaussianField C hC := by
  have hlim : IsProjectiveLimit μ (gaussianProjectiveFamily C) :=
    map_restrict_eq_gaussianProjectiveFamily hμ hmean hcov hC
  exact hlim.unique (isProjectiveLimit_gaussianField hC)

end Uniqueness

section Existence

/-- **Georgii's Proposition (13.A7), existence part.** Let `C : ι → ι → ℝ` be a covariance kernel
all of whose finite submatrices `(C i j)_{i, j ∈ I}` are positive semidefinite (in particular `C`
is symmetric, since `Matrix.PosSemidef` includes hermiticity). Then there is a probability measure
on `ι → ℝ` under which the coordinate process is a centred Gaussian process with covariance `C`.

No countability assumption on `ι` is needed, and the submatrices are allowed to be degenerate. -/
theorem exists_isGaussianProcess_covariance_eq (C : ι → ι → ℝ)
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧
      IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ ∧
      (∀ i, ∫ ω, ω i ∂μ = 0) ∧
      ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = C i j := by
  classical
  exact ⟨gaussianField C hC, inferInstance, isGaussianProcess_gaussianField hC,
    integral_eval_gaussianField hC, covariance_eval_gaussianField hC⟩

/-- **Georgii's Proposition (13.A7)**: for a nonnegative definite symmetric `C : ι → ι → ℝ` there
is a *unique* centred Gaussian field on `ι → ℝ` with covariance function `C`.

Georgii states this for countably infinite `S`; countability plays no role in the argument, and
`Matrix.PosSemidef` of every finite submatrix is exactly his "nonnegative definite symmetric". -/
theorem existsUnique_isGaussianProcess_covariance_eq (C : ι → ι → ℝ)
    (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) :
    ∃! μ : Measure (ι → ℝ), IsGaussianProcess (fun i (ω : ι → ℝ) ↦ ω i) μ ∧
      (∀ i, ∫ ω, ω i ∂μ = 0) ∧
      ∀ i j, cov[fun ω : ι → ℝ ↦ ω i, fun ω : ι → ℝ ↦ ω j; μ] = C i j := by
  classical
  refine ⟨gaussianField C hC, ⟨isGaussianProcess_gaussianField hC,
    integral_eval_gaussianField hC, covariance_eval_gaussianField hC⟩, ?_⟩
  rintro ν ⟨hν, hmean, hcov⟩
  exact eq_gaussianField hC hν hmean hcov

end Existence

section Brownian

open scoped NNReal

namespace BrownianReal

/-- Mathlib's Brownian covariance matrix is the submatrix of the covariance kernel
`C s t = min s t`. -/
lemma covMatrix_eq_covMatrix (I : Finset ℝ≥0) :
    covMatrix I
      = ProbabilityTheory.covMatrix (fun s t : ℝ≥0 ↦ min (s : ℝ) (t : ℝ)) I := rfl

/-- Mathlib's finite-dimensional distributions of real Brownian motion are the centred Gaussian
marginals of the covariance kernel `C s t = min s t`. -/
lemma projectiveFamily_eq_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    projectiveFamily I
      = gaussianProjectiveFamily (fun s t : ℝ≥0 ↦ min (s : ℝ) (t : ℝ)) I := rfl

/-- Every finite submatrix of the Brownian covariance kernel `C s t = min s t` is positive
semidefinite, so `gaussianField` applies to it. -/
lemma posSemidef_covMatrix_min (I : Finset ℝ≥0) :
    (ProbabilityTheory.covMatrix (fun s t : ℝ≥0 ↦ min (s : ℝ) (t : ℝ)) I).PosSemidef :=
  posSemidef_covMatrix I

/-- **The law of real Brownian motion as a Gaussian field.** `gaussianField` at the covariance
kernel `C s t = min s t` is a measure on `ℝ≥0 → ℝ` whose finite-dimensional marginals are
`BrownianReal.projectiveFamily`; it is the measure that file was written to be extended to, and
it is unique with this property by `MeasureTheory.IsProjectiveLimit.unique`. No path regularity
is asserted. -/
theorem isProjectiveLimit_gaussianField :
    MeasureTheory.IsProjectiveLimit
      (gaussianField (fun s t : ℝ≥0 ↦ min (s : ℝ) (t : ℝ)) posSemidef_covMatrix_min)
      projectiveFamily :=
  ProbabilityTheory.isProjectiveLimit_gaussianField posSemidef_covMatrix_min

end BrownianReal

end Brownian

end ProbabilityTheory

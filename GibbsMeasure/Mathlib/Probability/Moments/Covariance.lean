/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Bilinearity of the covariance, and the covariance matrix is positive semidefinite
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- The covariance only depends on the almost-everywhere classes of its arguments. Intended home:
`Mathlib/Probability/Moments/Covariance.lean`, next to `covariance_comm`. -/
theorem covariance_congr_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  exact integral_congr_ae ((hX.sub Filter.EventuallyEq.rfl).mul (hY.sub Filter.EventuallyEq.rfl))

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → ℝ} {s : Finset ι}

/-- **Missing from Mathlib** (`Mathlib/Probability/Moments/Covariance.lean`). The covariance of
two finite linear combinations of an `L²` family expands bilinearly into the pairwise covariances.
This is the identity behind both Georgii's (13.3) (nonnegative definiteness of a covariance
function, taking `a = b`) and (13.2) (the variance of `∑ᵢ tᵢ σᵢ` in the characteristic function of
a Gaussian field). -/
theorem covariance_sum_smul_sum_smul (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (a b : ι → ℝ) :
    cov[∑ i ∈ s, a i • X i, ∑ j ∈ s, b j • X j; μ] =
      ∑ i ∈ s, ∑ j ∈ s, a i * b j * cov[X i, X j; μ] := by
  have hXa : ∀ i ∈ s, MemLp (a i • X i) 2 μ := fun i hi ↦ (hX i hi).const_smul _
  have hXb : ∀ j ∈ s, MemLp (b j • X j) 2 μ := fun j hj ↦ (hX j hj).const_smul _
  rw [covariance_sum_left' hXa (memLp_finsetSum' s hXb)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [covariance_smul_left, covariance_sum_right' hXb (hX i hi), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [covariance_smul_right]
  ring

end ProbabilityTheory

namespace Matrix

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {X : ι → Ω → ℝ}

/-- **Missing from Mathlib** (same file as `ProbabilityTheory.covariance_sum_smul_sum_smul`, or a
new `Mathlib/Probability/Moments/CovarianceMatrix.lean`). The covariance "matrix" of an arbitrary
`L²` family, indexed by an arbitrary type `ι` (no `Fintype` assumption — `Matrix.PosSemidef` is
already stated over finitely supported coefficients `ι →₀ ℝ`, matching Georgii's (13.3) exactly).
This is the general fact behind Georgii's remark, before (13.7), that *every* covariance function
is nonnegative definite. -/
theorem posSemidef_covariance (hX : ∀ i, MemLp (X i) 2 μ) :
    Matrix.PosSemidef (fun i j ↦ cov[X i, X j; μ] : Matrix ι ι ℝ) := by
  refine ⟨Matrix.IsHermitian.ext fun i j ↦ ?_, fun x ↦ ?_⟩
  · simpa using covariance_comm (X := X j) (Y := X i) (μ := μ)
  · have hxs : ∀ i ∈ x.support, MemLp (X i) 2 μ := fun i _ ↦ hX i
    have hrw : x.sum (fun i xi ↦ x.sum fun j xj ↦ star xi *
        (fun i j ↦ cov[X i, X j; μ] : Matrix ι ι ℝ) i j * xj) =
        ∑ i ∈ x.support, ∑ j ∈ x.support, x i * x j * cov[X i, X j; μ] := by
      simp only [Finsupp.sum, star_trivial]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hrw]
    have hmem : MemLp (∑ i ∈ x.support, x i • X i) 2 μ :=
      memLp_finsetSum' x.support fun i hi ↦ (hxs i hi).const_smul (x i)
    calc (0 : ℝ) ≤ Var[∑ i ∈ x.support, x i • X i; μ] := variance_nonneg _ _
      _ = cov[∑ i ∈ x.support, x i • X i, ∑ j ∈ x.support, x j • X j; μ] :=
          (covariance_self hmem.aestronglyMeasurable.aemeasurable).symm
      _ = ∑ i ∈ x.support, ∑ j ∈ x.support, x i * x j * cov[X i, X j; μ] :=
          covariance_sum_smul_sum_smul hxs x x

end Matrix

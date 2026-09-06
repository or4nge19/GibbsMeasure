/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Distributions.Gaussian.Existence

/-!
# Reindexing a centred Gaussian field

The pushforward of the centred Gaussian field with covariance kernel `C : ι → ι → ℝ` along a
reindexing `ω ↦ ω ∘ e` of the coordinates, `e : κ → ι`, is the centred Gaussian field on `κ → ℝ`
with the reindexed covariance kernel `(a, b) ↦ C (e a) (e b)`. Both statements follow from the
uniqueness of a centred Gaussian process with a given covariance
(`ProbabilityTheory.eq_gaussianField`, Georgii's Proposition (13.A7)).

The reindexing need not be injective: a covariance kernel pulled back along an arbitrary `e` is
still nonnegative definite, because `Matrix.PosSemidef` is stable under arbitrary `submatrix e e`.

## Main results

* `ProbabilityTheory.posSemidef_covMatrix_comp`: the pulled-back kernel is nonnegative definite.
* `ProbabilityTheory.map_comp_gaussianField`: the pushforward formula.
* `ProbabilityTheory.map_comp_gaussianField_self`: a covariance kernel invariant under the
  diagonal action of `e` gives a Gaussian field invariant under `ω ↦ ω ∘ e`; with `e` the
  translation `i ↦ i - j` of an additive group of sites this is the shift invariance of a centred
  Gauss field with homogeneous covariance function.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace ProbabilityTheory

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {C : ι → ι → ℝ}

omit [DecidableEq ι] [DecidableEq κ] in
/-- **A reindexed covariance kernel is again nonnegative definite.** No injectivity of `e` is
needed: `Matrix.PosSemidef` is stable under `submatrix e e` for an arbitrary `e`. -/
theorem posSemidef_covMatrix_comp (e : κ → ι) (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef)
    (J : Finset κ) : (covMatrix (fun a b ↦ C (e a) (e b)) J).PosSemidef := by
  classical
  have hsub : covMatrix (fun a b ↦ C (e a) (e b)) J
      = (covMatrix C (J.image e)).submatrix
          (fun a : J ↦ (⟨e a.1, Finset.mem_image_of_mem e a.2⟩ : (J.image e : Finset ι)))
          (fun a : J ↦ (⟨e a.1, Finset.mem_image_of_mem e a.2⟩ : (J.image e : Finset ι))) := by
    ext a b
    simp [covMatrix]
  rw [hsub]
  exact (hC _).submatrix _

omit [DecidableEq ι] [DecidableEq κ] in
lemma measurable_comp_reindex (e : κ → ι) : Measurable fun ω : ι → ℝ ↦ ω ∘ e :=
  measurable_pi_lambda _ fun a ↦ measurable_pi_apply (e a)

/-- **Reindexing a centred Gaussian field.** The image of `gaussianField C` under the coordinate
reindexing `ω ↦ ω ∘ e` is the centred Gaussian field with the pulled-back covariance kernel. -/
theorem map_comp_gaussianField (e : κ → ι) (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef) :
    (gaussianField C hC).map (fun ω : ι → ℝ ↦ ω ∘ e)
      = gaussianField (fun a b ↦ C (e a) (e b)) (posSemidef_covMatrix_comp e hC) := by
  have hmeas : Measurable fun ω : ι → ℝ ↦ ω ∘ e := measurable_comp_reindex e
  have hgp : IsGaussianProcess (fun a (ω : ι → ℝ) ↦ ω (e a)) (gaussianField C hC) :=
    (isGaussianProcess_gaussianField hC).comp_right e
  refine eq_gaussianField _ ⟨fun J ↦ ?_⟩ (fun a ↦ ?_) (fun a b ↦ ?_)
  · constructor
    have hcomp : ((gaussianField C hC).map fun ω : ι → ℝ ↦ ω ∘ e).map
          (fun ω' : κ → ℝ ↦ J.restrict fun a ↦ ω' a)
        = (gaussianField C hC).map fun ω : ι → ℝ ↦ J.restrict fun a ↦ ω (e a) := by
      rw [Measure.map_map (Finset.measurable_restrict _) hmeas]
      rfl
    rw [hcomp]
    exact (hgp.hasGaussianLaw J).isGaussian_map
  · rw [integral_map hmeas.aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    exact integral_eval_gaussianField hC (e a)
  · rw [covariance_map (Measurable.aestronglyMeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop)) hmeas.aemeasurable]
    exact covariance_eval_gaussianField hC (e a) (e b)

/-- **A Gaussian field is invariant under a reindexing that preserves its covariance.** With
`e : i ↦ i - j` on an additive group of sites and a homogeneous covariance function, this is the
shift invariance of a centred Gauss field. -/
theorem map_comp_gaussianField_self (e : ι → ι) (hC : ∀ I : Finset ι, (covMatrix C I).PosSemidef)
    (he : ∀ a b, C (e a) (e b) = C a b) :
    (gaussianField C hC).map (fun ω : ι → ℝ ↦ ω ∘ e) = gaussianField C hC := by
  rw [map_comp_gaussianField e hC]
  congr 1
  funext a b
  exact he a b

end ProbabilityTheory

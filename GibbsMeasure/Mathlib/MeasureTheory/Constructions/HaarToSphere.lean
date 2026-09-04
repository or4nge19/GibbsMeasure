/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Linear isometries of the unit sphere and the surface measure

A linear isometric equivalence `e` of a normed space restricts to a homeomorphism `e.sphere` of
the unit sphere; for an additive Haar measure `μ` preserved by `e`, the restriction preserves
the surface measure `μ.toSphere`. On a finite-dimensional inner product space every linear
isometric equivalence preserves `volume`, so every rotation preserves `volume.toSphere`
(`LinearIsometryEquiv.measurePreserving_sphere_toSphere_volume`).
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped Pointwise

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The restriction of a linear isometric equivalence to the unit sphere, as a homeomorphism.
Intended home: `Mathlib/Analysis/Normed/Operator/LinearIsometry.lean`. -/
def sphere (e : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ₜ Metric.sphere (0 : E) 1 :=
  e.toHomeomorph.subtype fun x ↦ by simp

@[simp] lemma coe_sphere_apply (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    (e.sphere x : E) = e x := rfl

@[simp] lemma sphere_symm (e : E ≃ₗᵢ[ℝ] E) : e.sphere.symm = e.symm.sphere := rfl

lemma sphere_trans (e f : E ≃ₗᵢ[ℝ] E) : e.sphere.trans f.sphere = (e.trans f).sphere := rfl

lemma sphere_refl : (LinearIsometryEquiv.refl ℝ E).sphere = Homeomorph.refl _ := rfl

variable [MeasurableSpace E] [BorelSpace E]

/-- The restriction of a linear isometric equivalence to the unit sphere, as a measurable
equivalence. -/
def sphereMeasurableEquiv (e : E ≃ₗᵢ[ℝ] E) :
    Metric.sphere (0 : E) 1 ≃ᵐ Metric.sphere (0 : E) 1 :=
  e.sphere.toMeasurableEquiv

@[simp] lemma coe_sphereMeasurableEquiv_apply (e : E ≃ₗᵢ[ℝ] E) (x : Metric.sphere (0 : E) 1) :
    (e.sphereMeasurableEquiv x : E) = e x := rfl

@[simp] lemma sphereMeasurableEquiv_symm (e : E ≃ₗᵢ[ℝ] E) :
    e.sphereMeasurableEquiv.symm = e.symm.sphereMeasurableEquiv := rfl

lemma sphereMeasurableEquiv_trans (e f : E ≃ₗᵢ[ℝ] E) :
    e.sphereMeasurableEquiv.trans f.sphereMeasurableEquiv = (e.trans f).sphereMeasurableEquiv :=
  rfl

lemma sphereMeasurableEquiv_refl :
    (LinearIsometryEquiv.refl ℝ E).sphereMeasurableEquiv = MeasurableEquiv.refl _ := rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- The preimage of a set of the sphere under `e.sphere`, seen in `E`, is the preimage under `e`
of the set seen in `E`. -/
lemma image_val_preimage_sphere (e : E ≃ₗᵢ[ℝ] E) (s : Set (Metric.sphere (0 : E) 1)) :
    Subtype.val '' (e.sphere ⁻¹' s) = e ⁻¹' (Subtype.val '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨e.sphere y, hy, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.sphere.symm y, ?_, ?_⟩
    · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hy
    · simp only [sphere_symm, coe_sphere_apply]
      exact e.symm_apply_eq.2 hxy

/-- A linear isometric equivalence preserving an additive Haar measure `μ` preserves the surface
measure `μ.toSphere` on the unit sphere. Intended home:
`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`. -/
theorem measurePreserving_sphere_toSphere (e : E ≃ₗᵢ[ℝ] E) {μ : Measure E}
    (hμ : MeasurePreserving e μ μ) :
    MeasurePreserving e.sphereMeasurableEquiv μ.toSphere μ.toSphere := by
  refine ⟨e.sphereMeasurableEquiv.measurable, ?_⟩
  ext s hs
  rw [e.sphereMeasurableEquiv.map_apply s, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (e.sphereMeasurableEquiv.measurable hs)]
  change _ * μ (Ioo (0 : ℝ) 1 • (Subtype.val '' (e.sphere ⁻¹' s))) = _
  rw [image_val_preimage_sphere]
  congr 1
  have : Ioo (0 : ℝ) 1 • (e ⁻¹' (Subtype.val '' s)) = e ⁻¹' (Ioo (0 : ℝ) 1 • Subtype.val '' s) := by
    have h1 : ∀ X : Set E, e ⁻¹' X = e.symm '' X := fun X ↦ by
      rw [e.symm.image_eq_preimage_symm, LinearIsometryEquiv.symm_symm]
    rw [h1, h1]
    exact (Set.image_image2_distrib_right (f := fun (c : ℝ) (x : E) ↦ c • x) (g := e.symm)
      fun c x ↦ e.symm.map_smul c x).symm
  have hmap : μ.map e.toHomeomorph.toMeasurableEquiv = μ := hμ.map_eq
  rw [this]
  change μ (e.toHomeomorph.toMeasurableEquiv ⁻¹' _) = _
  rw [← MeasurableEquiv.map_apply e.toHomeomorph.toMeasurableEquiv, hmap]

/-- Every linear isometric equivalence of a finite-dimensional real inner product space
preserves the surface measure `volume.toSphere` of the unit sphere. -/
theorem measurePreserving_sphere_toSphere_volume {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving e.sphereMeasurableEquiv volume.toSphere volume.toSphere :=
  e.measurePreserving_sphere_toSphere e.measurePreserving

end LinearIsometryEquiv

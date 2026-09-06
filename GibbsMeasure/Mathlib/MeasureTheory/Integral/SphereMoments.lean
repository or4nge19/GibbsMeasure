/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The first two moments of a rotation invariant measure on the unit sphere

Let `V` be a finite-dimensional real inner product space of dimension `N` and let `μ` be a
probability measure on the unit sphere of `V` which is invariant under every linear isometry of
`V`. Then

* `MeasureTheory.integral_inner_eq_zero`: `∫ ⟪x, u⟫ dμ(x) = 0`;
* `MeasureTheory.integral_inner_sq`: `∫ ⟪x, u⟫² dμ(x) = ‖u‖² / N`.

The second identity is Georgii's `N ∫ x₁² λ(dx) = ∫ ∑_n x_n² λ(dx) = λ(E)` in the proof of
Theorem (16.27): the diagonal entries of the second-moment form of a rotation invariant law are
all equal (transpose two vectors of an orthonormal basis), and they sum to `∫ ‖x‖² dμ = 1`.

The first identity needs only the invariance under `x ↦ -x`.

Intended home: `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` (or a new
`Mathlib/MeasureTheory/Integral/SphereMoments.lean`), next to `MeasureTheory.Measure.toSphere`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Metric MeasureTheory Module
open scoped RealInnerProductSpace

noncomputable section

namespace MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] {μ : Measure (sphere (0 : V) 1)}

omit [MeasurableSpace V] [BorelSpace V] in
/-- The linear form `x ↦ ⟪x, u⟫` is continuous on the unit sphere. -/
lemma continuous_inner_sphere (u : V) :
    Continuous fun x : sphere (0 : V) 1 ↦ ⟪(x : V), u⟫ :=
  (continuous_subtype_val.inner continuous_const)

omit [MeasurableSpace V] [BorelSpace V] in
/-- On the unit sphere `|⟪x, u⟫| ≤ ‖u‖`. -/
lemma abs_inner_sphere_le (u : V) (x : sphere (0 : V) 1) : |⟪(x : V), u⟫| ≤ ‖u‖ := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [mem_sphere_zero_iff_norm.1 x.2, one_mul]

variable [IsFiniteMeasure μ]

/-- `x ↦ ⟪x, u⟫` is integrable on the unit sphere for a finite measure. -/
lemma integrable_inner_sphere (u : V) :
    Integrable (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), u⟫) μ :=
  (integrable_const ‖u‖).mono' (continuous_inner_sphere u).aestronglyMeasurable
    (.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs] using abs_inner_sphere_le u x)

/-- `x ↦ ⟪x, u⟫ ⟪x, w⟫` is integrable on the unit sphere for a finite measure. -/
lemma integrable_inner_mul_inner_sphere (u w : V) :
    Integrable (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), u⟫ * ⟪(x : V), w⟫) μ :=
  (integrable_const (‖u‖ * ‖w‖)).mono'
    ((continuous_inner_sphere u).mul (continuous_inner_sphere w)).aestronglyMeasurable
    (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_inner_sphere_le u x) (abs_inner_sphere_le w x) (abs_nonneg _)
        (norm_nonneg u))

omit [IsFiniteMeasure μ] in
/-- The second-moment form of a measure on the unit sphere is invariant under every linear
isometry preserving the measure. -/
lemma integral_inner_mul_inner_map (e : V ≃ₗᵢ[ℝ] V)
    (he : MeasurePreserving e.sphereMeasurableEquiv μ μ) (u w : V) :
    ∫ x, ⟪(x : V), e u⟫ * ⟪(x : V), e w⟫ ∂μ = ∫ x, ⟪(x : V), u⟫ * ⟪(x : V), w⟫ ∂μ := by
  rw [← he.integral_comp' (f := e.sphereMeasurableEquiv)
    (g := fun x : sphere (0 : V) 1 ↦ ⟪(x : V), e u⟫ * ⟪(x : V), e w⟫)]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [LinearIsometryEquiv.coe_sphereMeasurableEquiv_apply,
    LinearIsometryEquiv.inner_map_map]

omit [IsFiniteMeasure μ] in
/-- **The first moment of a centrally symmetric measure on the unit sphere vanishes.** -/
theorem integral_inner_eq_zero
    (hμ : MeasurePreserving (LinearIsometryEquiv.neg ℝ (E := V)).sphereMeasurableEquiv μ μ)
    (u : V) : ∫ x, ⟪(x : V), u⟫ ∂μ = 0 := by
  have h : ∫ x, ⟪(x : V), u⟫ ∂μ = ∫ x, -⟪(x : V), u⟫ ∂μ := by
    conv_rhs => rw [← hμ.integral_comp'
      (f := (LinearIsometryEquiv.neg ℝ (E := V)).sphereMeasurableEquiv)
      (g := fun x : sphere (0 : V) 1 ↦ -⟪(x : V), u⟫)]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [LinearIsometryEquiv.coe_sphereMeasurableEquiv_apply, inner_neg_left]
  rw [integral_neg] at h
  linarith

variable [FiniteDimensional ℝ V] [IsProbabilityMeasure μ]

omit [FiniteDimensional ℝ V] in
/-- The diagonal entries of the second-moment form of a rotation invariant probability measure on
the unit sphere along an orthonormal basis are all equal to `1 / N`, where `N` is the cardinality
of the index set of the basis. -/
theorem integral_inner_orthonormalBasis_sq
    (hμ : ∀ e : V ≃ₗᵢ[ℝ] V, MeasurePreserving e.sphereMeasurableEquiv μ μ)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V) (i : Fin n) :
    ∫ x, ⟪(x : V), b i⟫ ^ 2 ∂μ = 1 / n := by
  -- all diagonal entries agree, by transposing two basis vectors
  have hdiag : ∀ j : Fin n, ∫ x, ⟪(x : V), b j⟫ ^ 2 ∂μ = ∫ x, ⟪(x : V), b i⟫ ^ 2 ∂μ := by
    intro j
    have h := integral_inner_mul_inner_map (b.equiv b (Equiv.swap i j))
      (hμ _) (b i) (b i)
    simp only [OrthonormalBasis.equiv_apply_basis, Equiv.swap_apply_left] at h
    simpa only [← sq] using h
  -- they sum to `∫ ‖x‖² dμ = 1`
  have hsum : ∑ j : Fin n, ∫ x, ⟪(x : V), b j⟫ ^ 2 ∂μ = 1 := by
    rw [← integral_finsetSum _ fun j _ ↦ by
      simpa only [← sq] using integrable_inner_mul_inner_sphere (μ := μ) (b j) (b j)]
    have hx : ∀ x : sphere (0 : V) 1, ∑ j : Fin n, ⟪(x : V), b j⟫ ^ 2 = 1 := by
      intro x
      rw [b.sum_sq_inner_left (x : V), mem_sphere_zero_iff_norm.1 x.2, one_pow]
    simp [hx]
  rw [Finset.sum_congr rfl fun j _ ↦ hdiag j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hn : (n : ℝ) ≠ 0 := by
    rintro h
    rw [h, zero_mul] at hsum
    exact zero_ne_one hsum
  field_simp at hsum ⊢
  linarith

/-- **The second moment of a rotation invariant probability measure on the unit sphere.**
`∫ ⟪x, u⟫² dμ(x) = ‖u‖² / N`, where `N = dim V`. This is Georgii's identity
`N ∫ x₁² λ(dx) = λ(E)` in the proof of Theorem (16.27). -/
theorem integral_inner_sq
    (hμ : ∀ e : V ≃ₗᵢ[ℝ] V, MeasurePreserving e.sphereMeasurableEquiv μ μ) (u : V) :
    ∫ x, ⟪(x : V), u⟫ ^ 2 ∂μ = ‖u‖ ^ 2 / finrank ℝ V := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hnt : Nontrivial V := ⟨⟨u, 0, hu⟩⟩
  have hpos : 0 < finrank ℝ V := finrank_pos
  have : NeZero (finrank ℝ V) := ⟨hpos.ne'⟩
  set v : V := ‖u‖⁻¹ • u with hvdef
  have hvnorm : ‖v‖ = 1 := by
    rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnu]
  have hpt : ∀ x : sphere (0 : V) 1, ⟪(x : V), u⟫ = ‖u‖ * ⟪(x : V), v⟫ := fun x ↦ by
    rw [hvdef, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hnu, one_mul]
  have hcard : finrank ℝ V = Fintype.card (Fin (finrank ℝ V)) := (Fintype.card_fin _).symm
  have horth : Orthonormal ℝ
      (Set.domRestrict ({0} : Set (Fin (finrank ℝ V))) (fun _ : Fin (finrank ℝ V) ↦ v)) := by
    refine ⟨fun j ↦ hvnorm, ?_⟩
    intro j k hjk
    exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 j.2).trans
      (Set.mem_singleton_iff.1 k.2).symm)) hjk
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := V) hcard horth
  have hb0 : b 0 = v := hb 0 rfl
  have hkey := integral_inner_orthonormalBasis_sq (μ := μ) hμ b 0
  rw [hb0] at hkey
  calc ∫ x, ⟪(x : V), u⟫ ^ 2 ∂μ = ∫ x, ‖u‖ ^ 2 * ⟪(x : V), v⟫ ^ 2 ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hpt x, mul_pow]
    _ = ‖u‖ ^ 2 * ∫ x, ⟪(x : V), v⟫ ^ 2 ∂μ := integral_const_mul _ _
    _ = ‖u‖ ^ 2 / finrank ℝ V := by rw [hkey]; ring

end MeasureTheory

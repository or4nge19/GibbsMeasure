/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Lattice

/-!
# Perron–Frobenius theorem for strictly positive matrices

For a real square matrix `A` with all entries strictly positive we prove the existence of a
strictly positive eigenvector with a strictly positive eigenvalue (the Perron root), the
uniqueness of that eigenvalue among those admitting a positive eigenvector, and the
one-dimensionality of the corresponding eigenspace (Georgii, *Gibbs Measures and Phase
Transitions*, Appendix 3.A). The spectral dominance of the Perron root over the other
eigenvalues is not covered.

This is the positive-matrix special case of the Perron–Frobenius theory of
[or4nge19/MCMC](https://github.com/or4nge19/MCMC) (`MCMC/PF/LinearAlgebra/Matrix/PerronFrobenius/*`:
`Matrix.collatzWielandtFn`, `Matrix.perronRoot`, `exists_positive_eigenvector_of_primitive`,
`uniqueness_of_positive_eigenvector`, spectral dominance for irreducible matrices), kept minimal
here and to be replaced by that API once it is in Mathlib.

The existence proof is the Collatz–Wielandt argument: maximise `⨅ i, (A *ᵥ y) i / y i` over
the (compact) image of the standard simplex under the normalised map `y ↦ A *ᵥ y / ∑ (A *ᵥ y)`.
-/

@[expose] public section

namespace Matrix

open Finset

variable {n : Type*} [Fintype n] (A : Matrix n n ℝ)

/-- A positive matrix sends a nonzero nonnegative vector to a strictly positive one. -/
theorem mulVec_pos_of_nonneg_of_ne_zero (hA : ∀ i j, 0 < A i j) {x : n → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hx0 : x ≠ 0) (i : n) : 0 < (A *ᵥ x) i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx0
  rw [mulVec_apply_eq_sum]
  exact Finset.sum_pos' (fun k _ => mul_nonneg (hA i k).le (hx k))
    ⟨j, mem_univ _, mul_pos (hA i j) (lt_of_le_of_ne (hx j) (Ne.symm hj))⟩

variable [Nonempty n]

/-- A positive matrix sends a strictly positive vector to a strictly positive one. -/
theorem mulVec_pos_of_pos (hA : ∀ i j, 0 < A i j) {x : n → ℝ} (hx : ∀ j, 0 < x j) (i : n) :
    0 < (A *ᵥ x) i := by
  rw [mulVec_apply_eq_sum]
  exact Finset.sum_pos (fun k _ => mul_pos (hA i k) (hx k)) univ_nonempty

/-- The Collatz–Wielandt quotient `⨅ i, (A *ᵥ y) i / y i` of a vector `y`. -/
noncomputable def collatzWielandt (y : n → ℝ) : ℝ :=
  univ.inf' univ_nonempty fun i => (A *ᵥ y) i / y i

theorem collatzWielandt_le (y : n → ℝ) (i : n) : collatzWielandt A y ≤ (A *ᵥ y) i / y i :=
  inf'_le _ (mem_univ i)

theorem lt_collatzWielandt_iff {y : n → ℝ} {a : ℝ} :
    a < collatzWielandt A y ↔ ∀ i, a < (A *ᵥ y) i / y i := by
  simp [collatzWielandt, lt_inf'_iff]

theorem collatzWielandt_smul {y : n → ℝ} {c : ℝ} (hc : c ≠ 0) :
    collatzWielandt A (c • y) = collatzWielandt A y := by
  unfold collatzWielandt
  congr 1
  ext i
  rw [mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ hc]

theorem continuousOn_collatzWielandt {s : Set (n → ℝ)} (hs : ∀ y ∈ s, ∀ i, y i ≠ 0) :
    ContinuousOn (collatzWielandt A) s := by
  have hmul : Continuous fun y : n → ℝ => A *ᵥ y :=
    Continuous.matrix_mulVec continuous_const continuous_id
  unfold collatzWielandt
  refine ContinuousOn.finset_inf'_apply (f := fun i y => (A *ᵥ y) i / y i) univ_nonempty
    fun i _ => ?_
  exact ContinuousOn.div ((continuous_apply i).comp hmul).continuousOn
    (continuous_apply i).continuousOn fun y hy => hs y hy i

/-- **Perron–Frobenius**, existence: a strictly positive matrix has a strictly positive
eigenvector with a strictly positive eigenvalue. -/
theorem exists_pos_eigenvector_of_pos (hA : ∀ i j, 0 < A i j) :
    ∃ r : ℝ, 0 < r ∧ ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  set K : Set (n → ℝ) := stdSimplex ℝ n with hK
  set g : (n → ℝ) → (n → ℝ) := fun x => (∑ i, (A *ᵥ x) i)⁻¹ • (A *ᵥ x) with hg
  have hAx_pos : ∀ x ∈ K, ∀ i, 0 < (A *ᵥ x) i := by
    intro x hx i
    refine mulVec_pos_of_nonneg_of_ne_zero A hA hx.1 ?_ i
    rintro rfl
    simp [hK, stdSimplex] at hx
  have hsum_pos : ∀ x ∈ K, 0 < ∑ i, (A *ᵥ x) i := fun x hx =>
    Finset.sum_pos (fun i _ => hAx_pos x hx i) univ_nonempty
  have hg_pos : ∀ x ∈ K, ∀ i, 0 < g x i := fun x hx i => by
    simp only [hg, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.2 (hsum_pos x hx)) (hAx_pos x hx i)
  have hg_mem : ∀ x ∈ K, g x ∈ K := by
    intro x hx
    refine ⟨fun i => (hg_pos x hx i).le, ?_⟩
    simp only [hg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (hsum_pos x hx).ne'
  have hcont_g : ContinuousOn g K := by
    have h1 : Continuous fun x : n → ℝ => A *ᵥ x :=
      Continuous.matrix_mulVec continuous_const continuous_id
    have h2 : Continuous fun x : n → ℝ => ∑ i, (A *ᵥ x) i :=
      continuous_finsetSum _ fun i _ => (continuous_apply i).comp h1
    exact (h2.continuousOn.inv₀ fun x hx => (hsum_pos x hx).ne').smul h1.continuousOn
  have hKne : K.Nonempty := by
    refine ⟨fun _ => (Fintype.card n : ℝ)⁻¹, fun _ => by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  set K2 := g '' K with hK2
  have hK2c : IsCompact K2 := (isCompact_stdSimplex ℝ n).image_of_continuousOn hcont_g
  have hK2_pos : ∀ y ∈ K2, ∀ i, 0 < y i := by
    rintro y ⟨x, hx, rfl⟩ i
    exact hg_pos x hx i
  have hK2_sub : ∀ y ∈ K2, y ∈ K := by
    rintro y ⟨x, hx, rfl⟩
    exact hg_mem x hx
  obtain ⟨y0, hy0, hmax⟩ := hK2c.exists_isMaxOn (hKne.image g)
    (continuousOn_collatzWielandt A fun y hy i => (hK2_pos y hy i).ne')
  have hy0pos : ∀ i, 0 < y0 i := hK2_pos y0 hy0
  have hrpos : 0 < collatzWielandt A y0 := by
    rw [lt_collatzWielandt_iff]
    exact fun i => div_pos (mulVec_pos_of_pos A hA hy0pos i) (hy0pos i)
  have hle : ∀ i, collatzWielandt A y0 * y0 i ≤ (A *ᵥ y0) i := fun i =>
    (le_div_iff₀ (hy0pos i)).1 (collatzWielandt_le A y0 i)
  refine ⟨collatzWielandt A y0, hrpos, y0, hy0pos, ?_⟩
  by_contra hne
  have hw_nonneg : ∀ i, 0 ≤ (A *ᵥ y0 - collatzWielandt A y0 • y0) i := fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hle i]
  have hAw : ∀ i, 0 < (A *ᵥ (A *ᵥ y0 - collatzWielandt A y0 • y0)) i :=
    mulVec_pos_of_nonneg_of_ne_zero A hA hw_nonneg (sub_ne_zero.2 hne)
  have hzpos : ∀ i, 0 < (A *ᵥ y0) i := mulVec_pos_of_pos A hA hy0pos
  have hlam_z : collatzWielandt A y0 < collatzWielandt A (A *ᵥ y0) := by
    rw [lt_collatzWielandt_iff]
    intro i
    rw [lt_div_iff₀ (hzpos i)]
    have := hAw i
    rw [mulVec_sub, mulVec_smul] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hgy0 : g y0 ∈ K2 := ⟨y0, hK2_sub y0 hy0, rfl⟩
  have hlam_g : collatzWielandt A (g y0) = collatzWielandt A (A *ᵥ y0) := by
    simp only [hg]
    exact collatzWielandt_smul A (inv_ne_zero (hsum_pos y0 (hK2_sub y0 hy0)).ne')
  have := isMaxOn_iff.1 hmax _ hgy0
  rw [hlam_g] at this
  exact absurd (lt_of_lt_of_le hlam_z this) (lt_irrefl _)

/-- **Perron–Frobenius**, uniqueness of the eigenvalue: two strictly positive eigenvectors of a
strictly positive matrix have the same eigenvalue. -/
theorem eigenvalue_eq_of_pos_eigenvector (hA : ∀ i j, 0 < A i j) {r s : ℝ} {v w : n → ℝ}
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) (hw : ∀ i, 0 < w i) (hAw : A *ᵥ w = s • w) :
    r = s := by
  obtain ⟨t, -, u, hu, hAu⟩ := exists_pos_eigenvector_of_pos Aᵀ fun i j => hA j i
  rw [mulVec_transpose] at hAu
  have key : ∀ (c : ℝ) (x : n → ℝ), (∀ i, 0 < x i) → A *ᵥ x = c • x → c = t := by
    intro c x hx hAx
    have h1 : u ⬝ᵥ (A *ᵥ x) = c * (u ⬝ᵥ x) := by rw [hAx, dotProduct_smul, smul_eq_mul]
    have h2 : u ⬝ᵥ (A *ᵥ x) = t * (u ⬝ᵥ x) := by
      rw [dotProduct_mulVec, hAu, smul_dotProduct, smul_eq_mul]
    have hpos : 0 < u ⬝ᵥ x := Finset.sum_pos (fun i _ => mul_pos (hu i) (hx i)) univ_nonempty
    exact mul_right_cancel₀ hpos.ne' (h1.symm.trans h2)
  rw [key r v hv hAv, key s w hw hAw]

/-- **Perron–Frobenius**, simplicity: every eigenvector for the eigenvalue of a strictly positive
eigenvector `v` of a strictly positive matrix is a multiple of `v`. -/
theorem eigenvector_eq_smul_of_pos (hA : ∀ i j, 0 < A i j) {r : ℝ} {v w : n → ℝ}
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) (hAw : A *ᵥ w = r • w) :
    ∃ c : ℝ, w = c • v := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image univ (fun i => w i / v i) univ_nonempty
  refine ⟨w i0 / v i0, ?_⟩
  have hu_nonneg : ∀ i, 0 ≤ (w - (w i0 / v i0) • v) i := fun i => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := (le_div_iff₀ (hv i)).1 (hi0 i (mem_univ i))
    linarith
  have hu_i0 : (w - (w i0 / v i0) • v) i0 = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ (hv i0).ne', sub_self]
  have hAu : A *ᵥ (w - (w i0 / v i0) • v) = r • (w - (w i0 / v i0) • v) := by
    rw [mulVec_sub, mulVec_smul, hAv, hAw, smul_sub, smul_comm]
  by_contra hne
  have hpos := mulVec_pos_of_nonneg_of_ne_zero A hA hu_nonneg (sub_ne_zero.2 hne) i0
  rw [hAu, Pi.smul_apply, hu_i0, smul_zero] at hpos
  exact lt_irrefl _ hpos

/-- **Perron–Frobenius**: a strictly positive matrix has a unique eigenvalue admitting a strictly
positive eigenvector, and that eigenvalue is strictly positive. -/
theorem exists_unique_perron (hA : ∀ i j, 0 < A i j) :
    ∃! r : ℝ, 0 < r ∧ ∃ v : n → ℝ, (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  obtain ⟨r, hr, v, hv, hAv⟩ := exists_pos_eigenvector_of_pos A hA
  refine ⟨r, ⟨hr, v, hv, hAv⟩, ?_⟩
  rintro s ⟨-, w, hw, hAw⟩
  exact eigenvalue_eq_of_pos_eigenvector A hA hw hAw hv hAv

/-- The Perron root of a strictly positive matrix. -/
noncomputable def perronRoot (hA : ∀ i j, 0 < A i j) : ℝ :=
  (exists_pos_eigenvector_of_pos A hA).choose

/-- A strictly positive eigenvector of a strictly positive matrix for its Perron root. -/
noncomputable def perronVector (hA : ∀ i j, 0 < A i j) : n → ℝ :=
  (exists_pos_eigenvector_of_pos A hA).choose_spec.2.choose

theorem perronRoot_pos (hA : ∀ i j, 0 < A i j) : 0 < perronRoot A hA :=
  (exists_pos_eigenvector_of_pos A hA).choose_spec.1

theorem perronVector_pos (hA : ∀ i j, 0 < A i j) (i : n) : 0 < perronVector A hA i :=
  (exists_pos_eigenvector_of_pos A hA).choose_spec.2.choose_spec.1 i

theorem mulVec_perronVector (hA : ∀ i j, 0 < A i j) :
    A *ᵥ perronVector A hA = perronRoot A hA • perronVector A hA :=
  (exists_pos_eigenvector_of_pos A hA).choose_spec.2.choose_spec.2

theorem eq_perronRoot_of_pos_eigenvector (hA : ∀ i j, 0 < A i j) {r : ℝ} {v : n → ℝ}
    (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = r • v) : r = perronRoot A hA :=
  eigenvalue_eq_of_pos_eigenvector A hA hv hAv (perronVector_pos A hA) (mulVec_perronVector A hA)

theorem exists_eq_smul_perronVector (hA : ∀ i j, 0 < A i j) {w : n → ℝ}
    (hAw : A *ᵥ w = perronRoot A hA • w) : ∃ c : ℝ, w = c • perronVector A hA :=
  eigenvector_eq_smul_of_pos A hA (perronVector_pos A hA) (mulVec_perronVector A hA) hAw

end Matrix

end

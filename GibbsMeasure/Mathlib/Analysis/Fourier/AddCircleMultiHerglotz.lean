/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Herglotz's lemma on the `d`-dimensional torus

A function `C : ℤ^d → ℝ` is *nonnegative definite* when all its Toeplitz matrices
`(C(a - b))_{a, b ∈ I}`, `I ⊆ ℤ^d` finite, are positive semidefinite; hermiticity of those
matrices is exactly the evenness `C(-n) = C(n)`. **Herglotz's lemma** — the discrete counterpart of
Bochner's theorem — says that such a `C` is the Fourier–Stieltjes transform of a finite measure on
the dual group `G = (ℝ/ℤ)^d`:

`C(n) = ∫_G z^n α(dz)` for all `n ∈ ℤ^d`.

## Main statement

* `UnitAddTorus.exists_isFiniteMeasure_integral_mFourier_eq`: Herglotz's lemma.

## Implementation notes

The proof is the classical one (Georgii, *Gibbs Measures and Phase Transitions*, Proposition
(13.A9)). Over the boxes `Λ_N = {-N, …, N}^d` one forms the Fejér-type densities

`g_N(z) = |Λ_N|⁻¹ ∑_{a, b ∈ Λ_N} C(a - b) z^{b-a}`,

which are nonnegative — this is the positive definiteness of `C` evaluated at the vector
`u_a = z^a` — of total mass `C(0)`, and whose Fourier–Stieltjes coefficients are
`C(n) |Λ_N ∩ (Λ_N - n)| / |Λ_N|`. The Fejér weights tend to `1` because the boundary layer of a
box is negligible. Since `G` is a compact group, the finite measures of mass at most `C(0)` form a
compact set (`MeasureTheory.isCompact_setOfPred_finiteMeasure_le_of_compactSpace`, a consequence of
Riesz–Markov–Kakutani), and any cluster point of `(g_N dz)_N` has the required coefficients: the
maps `ρ ↦ ∫ f dρ` are continuous on `MeasureTheory.FiniteMeasure` for bounded continuous `f`.

No countability or separability input beyond `Fintype d` is used, and the measure produced is
automatically invariant under `z ↦ -z` (its coefficients are real and even), although that is not
recorded here.
-/

public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal NNReal Topology

/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The box `{-N, …, N}^d ⊆ ℤ^d`, the index set of the `d`-dimensional Fejér kernel. -/
private def herglotzBox (d : Type*) [Fintype d] [DecidableEq d] (N : ℕ) : Finset (d → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)

private lemma mem_herglotzBox {N : ℕ} {j : d → ℤ} :
    j ∈ herglotzBox d N ↔ ∀ ℓ, -(N : ℤ) ≤ j ℓ ∧ j ℓ ≤ (N : ℤ) := by
  simp only [herglotzBox, Fintype.mem_piFinset, Finset.mem_Icc]

private lemma card_herglotzBox (N : ℕ) :
    (herglotzBox d N).card = (2 * N + 1) ^ Fintype.card d := by
  rw [herglotzBox, Fintype.card_piFinset]
  have h : ∀ _ : d, (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
    intro _
    rw [Int.card_Icc]
    omega
  rw [Finset.prod_congr rfl fun i _ ↦ h i, Finset.prod_const, Finset.card_univ]

private lemma card_herglotzBox_pos (N : ℕ) : 0 < (herglotzBox d N).card := by
  rw [card_herglotzBox]
  positivity

/-- The points of the small box `{-K, …, K}^d` stay in `{-N, …, N}^d` after translation by `m`,
as soon as `K + ‖m‖_∞ ≤ N`. -/
private lemma herglotzBox_subset_filter {N K : ℕ} {m : d → ℤ}
    (h : ∀ ℓ, (m ℓ).natAbs + K ≤ N) :
    herglotzBox d K ⊆ (herglotzBox d N).filter fun j ↦ j + m ∈ herglotzBox d N := by
  intro j hj
  rw [mem_herglotzBox] at hj
  refine Finset.mem_filter.2 ⟨mem_herglotzBox.2 fun ℓ ↦ ?_, mem_herglotzBox.2 fun ℓ ↦ ?_⟩
  · have h1 := hj ℓ
    have hm := h ℓ
    omega
  · have h1 := hj ℓ
    have hm := h ℓ
    simp only [Pi.add_apply]
    omega

/-- The Fejér weight `#{j ∈ Λ_N : j + m ∈ Λ_N} / #Λ_N` of the box `Λ_N`. -/
private def herglotzWeight (d : Type*) [Fintype d] [DecidableEq d] (N : ℕ) (m : d → ℤ) : ℝ :=
  (((herglotzBox d N).filter fun j ↦ j + m ∈ herglotzBox d N).card : ℝ) /
    ((herglotzBox d N).card : ℝ)

private lemma herglotzWeight_le_one (N : ℕ) (m : d → ℤ) : herglotzWeight d N m ≤ 1 := by
  rw [herglotzWeight, div_le_one (by exact_mod_cast card_herglotzBox_pos (d := d) N)]
  exact_mod_cast Finset.card_filter_le _ _

private lemma herglotzWeight_nonneg (N : ℕ) (m : d → ℤ) : 0 ≤ herglotzWeight d N m :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The Fejér weights tend to `1`: the boundary layer of a box is negligible. -/
private lemma tendsto_herglotzWeight (m : d → ℤ) :
    Filter.Tendsto (fun N ↦ herglotzWeight d N m) atTop (𝓝 1) := by
  set M : ℕ := Finset.univ.sup fun ℓ ↦ (m ℓ).natAbs with hM
  rw [← tendsto_add_atTop_iff_nat M]
  -- lower bound: the box of radius `K` sits inside the good set at radius `K + M`
  have hlow : ∀ K : ℕ,
      ((2 * (K : ℝ) + 1) / (2 * ((K : ℝ) + M) + 1)) ^ Fintype.card d
        ≤ herglotzWeight d (K + M) m := by
    intro K
    have hsub := herglotzBox_subset_filter (d := d) (N := K + M) (K := K) (m := m) fun ℓ ↦ by
      have : (m ℓ).natAbs ≤ M := Finset.le_sup (f := fun ℓ ↦ (m ℓ).natAbs) (Finset.mem_univ ℓ)
      omega
    have hcard0 := Finset.card_le_card hsub
    rw [card_herglotzBox] at hcard0
    have hcard : (2 * (K : ℝ) + 1) ^ Fintype.card d
        ≤ ((((herglotzBox d (K + M)).filter fun j ↦ j + m ∈ herglotzBox d (K + M)).card : ℕ)
            : ℝ) := by
      calc (2 * (K : ℝ) + 1) ^ Fintype.card d = (((2 * K + 1) ^ Fintype.card d : ℕ) : ℝ) := by
            push_cast; ring
        _ ≤ _ := by exact_mod_cast hcard0
    rw [herglotzWeight, card_herglotzBox, div_pow]
    have hden : (((2 * (K + M) + 1) ^ Fintype.card d : ℕ) : ℝ)
        = (2 * ((K : ℝ) + M) + 1) ^ Fintype.card d := by push_cast; ring
    rw [hden, div_le_div_iff_of_pos_right (by positivity)]
    exact hcard
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ tendsto_const_nhds
    (Filter.Eventually.of_forall hlow)
    (Filter.Eventually.of_forall fun K ↦ herglotzWeight_le_one _ _)
  -- `(2K+1)/(2(K+M)+1) → 1`
  have hden : Filter.Tendsto (fun K : ℕ ↦ (2 * (K : ℝ) + 2 * M + 1)) atTop atTop := by
    refine Filter.tendsto_atTop_add_const_right _ _ ?_
    exact Filter.tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have h0 : Filter.Tendsto (fun K : ℕ ↦ (2 * M : ℝ) / (2 * (K : ℝ) + 2 * M + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop _
  have hratio : Filter.Tendsto
      (fun K : ℕ ↦ (2 * (K : ℝ) + 1) / (2 * ((K : ℝ) + M) + 1)) atTop (𝓝 1) := by
    have hEq : (fun K : ℕ ↦ (2 * (K : ℝ) + 1) / (2 * ((K : ℝ) + M) + 1))
        = fun K : ℕ ↦ 1 - (2 * M : ℝ) / (2 * (K : ℝ) + 2 * M + 1) := by
      funext K
      have hne : (2 * (K : ℝ) + 2 * M + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hEq]
    simpa using tendsto_const_nhds.sub h0
  simpa using hratio.pow (Fintype.card d)

/-! ### The Fejér-type kernel of a positive definite function -/

section Kernel

variable {C : (d → ℤ) → ℝ}

omit [Fintype d] [DecidableEq d] in
/-- A double sum of an antisymmetric family over a square vanishes. -/
private lemma sum_sum_eq_zero_of_antisymm {I : Finset (d → ℤ)} {g : (d → ℤ) → (d → ℤ) → ℝ}
    (h : ∀ a b, g a b + g b a = 0) : ∑ a ∈ I, ∑ b ∈ I, g a b = 0 := by
  have h2 : (∑ a ∈ I, ∑ b ∈ I, g a b) + (∑ a ∈ I, ∑ b ∈ I, g a b) = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun b _ ↦ h a b
  linarith

variable (hC : ∀ I : Finset (d → ℤ), (Matrix.of fun a b : I ↦ C (a.1 - b.1)).PosSemidef)
include hC

omit [DecidableEq d] in
-- `Fintype d` is invisible in the statement but supplies `DecidableEq (d → ℤ)` in the proof.
set_option linter.unusedFintypeInType false in
/-- **A nonnegative definite function is even**: hermiticity of the Toeplitz matrices
`(C(a-b))_{a,b ∈ I}` is exactly the evenness `C(-n) = C(n)`. This is Georgii's standing hypothesis
in Proposition (13.A9), so it need not be assumed separately. -/
theorem even_of_posSemidef_toeplitz (n : d → ℤ) : C (-n) = C n := by
  have h := (hC {0, n}).isHermitian.apply
    (⟨0, Finset.mem_insert_self 0 {n}⟩ : ({0, n} : Finset (d → ℤ)))
    ⟨n, Finset.mem_insert_of_mem (Finset.mem_singleton_self n)⟩
  simpa using h.symm

omit [Fintype d] [DecidableEq d] in
/-- The Toeplitz quadratic form of `C` at a real vector is nonnegative. -/
private lemma herglotz_quadForm_nonneg (I : Finset (d → ℤ)) (x : (d → ℤ) → ℝ) :
    0 ≤ ∑ a ∈ I, ∑ b ∈ I, x a * x b * C (a - b) := by
  have h := (hC I).dotProduct_mulVec_nonneg fun a : I ↦ x a.1
  refine le_of_le_of_eq h ?_
  rw [← Finset.sum_coe_sort I fun a ↦ ∑ b ∈ I, x a * x b * C (a - b)]
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, star_trivial]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← Finset.sum_coe_sort I fun b ↦ x a.1 * x b * C (a.1 - b), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- Georgii's `g_Λ(z) = ∑_{a,b ∈ Λ} C(a-b) Re z^{b-a}` in the proof of Proposition (13.A9),
before dividing by `|Λ|`. -/
private def herglotzSum (C : (d → ℤ) → ℝ) (N : ℕ) (z : UnitAddTorus d) : ℝ :=
  ∑ a ∈ herglotzBox d N, ∑ b ∈ herglotzBox d N, C (a - b) * (mFourier (b - a) z).re

omit hC in
private lemma continuous_herglotzSum (N : ℕ) : Continuous (herglotzSum C N) :=
  continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦
    continuous_const.mul (Complex.continuous_re.comp (mFourier (b - a)).continuous)

/-- **Georgii's positivity in the proof of (13.A9)**: `g_Λ(z) ≥ 0`. Taking `u_a = z^a` in the
positive definiteness of `C` splits the Toeplitz form into the quadratic forms at `Re u` and at
`Im u`. -/
private lemma herglotzSum_nonneg (N : ℕ) (z : UnitAddTorus d) : 0 ≤ herglotzSum C N z := by
  have hpt : ∀ a b : d → ℤ, C (a - b) * (mFourier (b - a) z).re
      = (mFourier a z).re * (mFourier b z).re * C (a - b)
        + (mFourier a z).im * (mFourier b z).im * C (a - b) := by
    intro a b
    rw [mFourier_sub]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [herglotzSum, hpt, Finset.sum_add_distrib]
  exact add_nonneg (herglotz_quadForm_nonneg hC _ fun a ↦ (mFourier a z).re)
    (herglotz_quadForm_nonneg hC _ fun a ↦ (mFourier a z).im)

/-- `g_Λ` written as a complex trigonometric polynomial: the imaginary parts cancel in pairs. -/
private lemma ofReal_herglotzSum (N : ℕ) (z : UnitAddTorus d) :
    ((herglotzSum C N z : ℝ) : ℂ)
      = ∑ a ∈ herglotzBox d N, ∑ b ∈ herglotzBox d N,
          ((C (a - b) : ℝ) : ℂ) * mFourier (b - a) z := by
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, herglotzSum, Complex.re_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by
      rw [Complex.re_sum]
      exact Finset.sum_congr rfl fun b _ ↦ by simp [Complex.mul_re]
  · rw [Complex.ofReal_im, Complex.im_sum]
    have him : ∀ a ∈ herglotzBox d N,
        (∑ b ∈ herglotzBox d N, ((C (a - b) : ℝ) : ℂ) * mFourier (b - a) z).im
          = ∑ b ∈ herglotzBox d N, C (a - b) * (mFourier (b - a) z).im := fun a _ ↦ by
      rw [Complex.im_sum]
      exact Finset.sum_congr rfl fun b _ ↦ by simp [Complex.mul_im]
    rw [Finset.sum_congr rfl him]
    refine Eq.symm (sum_sum_eq_zero_of_antisymm fun a b ↦ ?_)
    have hba : C (b - a) = C (a - b) := by
      have h := even_of_posSemidef_toeplitz hC (a - b)
      rwa [neg_sub] at h
    have hmf : (mFourier (a - b) z).im = -(mFourier (b - a) z).im := by
      rw [← neg_sub b a, mFourier_neg, Complex.conj_im]
    rw [hba, hmf]
    ring

/-- **The Fourier–Stieltjes coefficients of Georgii's `g_Λ`**:
`∫_G z^n g_Λ(z) dz = C(n) · #{b ∈ Λ : b + n ∈ Λ}`. -/
private lemma integral_mFourier_mul_herglotzSum (n : d → ℤ) (N : ℕ) :
    ∫ z, mFourier n z * ((herglotzSum C N z : ℝ) : ℂ)
      = (C n : ℂ) *
          ((((herglotzBox d N).filter fun j ↦ j + n ∈ herglotzBox d N).card : ℕ) : ℂ) := by
  have hint : ∀ a b : d → ℤ, Integrable
      fun z : UnitAddTorus d ↦ mFourier n z * (((C (a - b) : ℝ) : ℂ) * mFourier (b - a) z) :=
    fun a b ↦ ((mFourier n).continuous.mul
      (continuous_const.mul (mFourier (b - a)).continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hstep : ∫ z, mFourier n z * ((herglotzSum C N z : ℝ) : ℂ)
      = ∑ a ∈ herglotzBox d N, ∑ b ∈ herglotzBox d N,
          ((C (a - b) : ℝ) : ℂ) * (if n + (b - a) = 0 then 1 else 0) := by
    simp_rw [ofReal_herglotzSum hC N, Finset.mul_sum]
    rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint a b]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [integral_finsetSum _ fun b _ ↦ hint a b]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    have hpt : ∀ z : UnitAddTorus d,
        mFourier n z * (((C (a - b) : ℝ) : ℂ) * mFourier (b - a) z)
          = ((C (a - b) : ℝ) : ℂ) * mFourier (n + (b - a)) z := fun z ↦ by
      rw [mFourier_add]; ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_mFourier]
  have hcond : ∀ a b : d → ℤ, (n + (b - a) = 0) ↔ (a = b + n) := fun a b ↦ by
    rw [show n + (b - a) = (b + n) - a from by abel, sub_eq_zero, eq_comm]
  rw [hstep]
  simp_rw [hcond, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun b (_ : b ∈ herglotzBox d N) ↦
    Finset.sum_ite_eq' (herglotzBox d N) (b + n) fun a ↦ ((C (a - b) : ℝ) : ℂ)]
  simp only [add_sub_cancel_left]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

end Kernel

/-! ### The approximating measures and the passage to the limit -/

section HerglotzMeasure

variable {C : (d → ℤ) → ℝ}

/-- Georgii's measure `g_Λ(z) dz / |Λ|` on the dual group. -/
private def herglotzMeasure (C : (d → ℤ) → ℝ) (N : ℕ) : Measure (UnitAddTorus d) :=
  volume.withDensity fun z ↦
    ENNReal.ofReal (((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z)

private lemma measurable_herglotzDensity (N : ℕ) :
    Measurable fun z : UnitAddTorus d ↦
      ENNReal.ofReal (((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z) :=
  (Measurable.const_mul (continuous_herglotzSum (C := C) N).measurable _).ennreal_ofReal

private lemma integrable_herglotzDensity (N : ℕ) :
    Integrable fun z ↦ ((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z :=
  (continuous_const.mul (continuous_herglotzSum (C := C) N)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private instance isFiniteMeasure_herglotzMeasure (N : ℕ) :
    IsFiniteMeasure (herglotzMeasure C N) := by
  refine isFiniteMeasure_withDensity (ne_of_lt ?_)
  refine lt_of_le_of_lt (lintegral_mono fun z ↦ ?_) (integrable_herglotzDensity (C := C) N).2
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)

variable (hC : ∀ I : Finset (d → ℤ), (Matrix.of fun a b : I ↦ C (a.1 - b.1)).PosSemidef)
include hC

private lemma herglotzDensity_nonneg (N : ℕ) (z : UnitAddTorus d) :
    0 ≤ ((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z :=
  mul_nonneg (by positivity) (herglotzSum_nonneg hC N z)

private lemma integral_herglotzMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (f : UnitAddTorus d → E) :
    ∫ z, f z ∂(herglotzMeasure C N)
      = ∫ z, (((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z) • f z := by
  rw [herglotzMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_herglotzDensity (C := C) N)
    (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [ENNReal.toReal_ofReal (herglotzDensity_nonneg hC N z)]

/-- The Fourier–Stieltjes coefficients of the approximating measures:
`∫_G z^n dα_N = C(n) · w_N(n)` with the Fejér weight `w_N(n)`. -/
private lemma integral_mFourier_herglotzMeasure (n : d → ℤ) (N : ℕ) :
    ∫ z, mFourier n z ∂(herglotzMeasure C N) = (C n : ℂ) * (herglotzWeight d N n : ℂ) := by
  rw [integral_herglotzMeasure hC N]
  have hpt : ∀ z : UnitAddTorus d,
      (((herglotzBox d N).card : ℝ)⁻¹ * herglotzSum C N z) • mFourier n z
        = (((herglotzBox d N).card : ℝ) : ℂ)⁻¹ *
            (mFourier n z * ((herglotzSum C N z : ℝ) : ℂ)) := fun z ↦ by
    rw [Complex.real_smul]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_mFourier_mul_herglotzSum hC n N, herglotzWeight]
  have hcard : (((herglotzBox d N).card : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (card_herglotzBox_pos (d := d) N).ne'
  push_cast
  field_simp

omit hC in
/-- The Fejér weight at `n = 0` is `1`. -/
private lemma herglotzWeight_zero (N : ℕ) : herglotzWeight d N 0 = 1 := by
  rw [herglotzWeight, Finset.filter_true_of_mem fun j hj ↦ by simpa using hj]
  exact div_self (by exact_mod_cast (card_herglotzBox_pos (d := d) N).ne')

/-- The total mass of the approximating measures is `C(0)`. -/
private lemma mass_herglotzMeasure (N : ℕ) :
    (herglotzMeasure C N) Set.univ = ENNReal.ofReal (C 0) := by
  have h1 := integral_mFourier_herglotzMeasure hC 0 N
  rw [mFourier_zero, herglotzWeight_zero (d := d) N] at h1
  simp only [ContinuousMap.one_apply, Complex.ofReal_one, mul_one, integral_const,
    Complex.real_smul] at h1
  have h2 : ((herglotzMeasure C N) Set.univ).toReal = C 0 := by exact_mod_cast h1
  rw [← h2, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end HerglotzMeasure

/-! ### Herglotz's lemma -/

section Herglotz

/-- At a cluster point of a filter along which a continuous map converges, the map takes the
limiting value. -/
private lemma eq_of_clusterPt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {x : X} {F : Filter X} (hcl : ClusterPt x F) {Φ : X → Y} (hΦ : Continuous Φ) {y : Y}
    (hy : Filter.Tendsto Φ F (𝓝 y)) : Φ x = y := by
  have : (𝓝 x ⊓ F).NeBot := hcl
  exact tendsto_nhds_unique (hΦ.continuousAt.mono_left inf_le_left) (hy.mono_left inf_le_right)

variable {C : (d → ℤ) → ℝ}

omit [DecidableEq d] in
/-- **Herglotz's lemma, Georgii Proposition (13.A9).** An even nonnegative definite function
`C : ℤ^d → ℝ` — equivalently, one whose Toeplitz matrices `(C(a-b))_{a,b ∈ I}` are positive
semidefinite, hermiticity being exactly evenness — is the Fourier–Stieltjes transform of a finite
measure `α` on the dual group `G = (ℝ/ℤ)^d`: `C(n) = ∫_G z^n α(dz)`.

Georgii's proof: the Fejér-type densities
`g_Λ(z) = |Λ|⁻¹ ∑_{a,b ∈ Λ} C(a-b) z^{b-a}` over boxes `Λ = {-N, …, N}^d` are nonnegative (this is
the positive definiteness of `C` at `u_a = z^a`), have total mass `C(0)` and Fourier–Stieltjes
coefficients `C(n) |Λ ∩ (Λ - n)| / |Λ| → C(n)`. On the compact group `G` the finite measures of
mass at most `C(0)` form a compact set
(`MeasureTheory.isCompact_setOfPred_finiteMeasure_le_of_compactSpace`), and any cluster point of
the sequence `g_Λ dz` has the required coefficients. -/
theorem exists_isFiniteMeasure_integral_mFourier_eq
    (hC : ∀ I : Finset (d → ℤ), (Matrix.of fun a b : I ↦ C (a.1 - b.1)).PosSemidef) :
    ∃ α : Measure (UnitAddTorus d), IsFiniteMeasure α ∧
      ∀ n, ∫ z, mFourier n z ∂α = (C n : ℂ) := by
  classical
  set C0 : ℝ≥0 := (C 0).toNNReal with hC0
  set μ : ℕ → FiniteMeasure (UnitAddTorus d) :=
    fun N ↦ ⟨herglotzMeasure C N, isFiniteMeasure_herglotzMeasure N⟩ with hμ
  have hmass : ∀ N, (μ N).mass = C0 := by
    intro N
    rw [← ENNReal.coe_inj, FiniteMeasure.ennreal_mass]
    exact mass_herglotzMeasure hC N
  have hle : Filter.map μ atTop
      ≤ Filter.principal {ρ : FiniteMeasure (UnitAddTorus d) | ρ.mass ≤ C0} :=
    Filter.le_principal_iff.2 (Filter.eventually_map.2
      (Filter.Eventually.of_forall fun N ↦ le_of_eq (hmass N)))
  obtain ⟨ν, -, hcl⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace (UnitAddTorus d) C0).exists_clusterPt hle
  refine ⟨(ν : Measure (UnitAddTorus d)), inferInstance, fun n ↦ ?_⟩
  -- the two real coordinates of the coefficient
  have hcoeff : ∀ N, ∫ z, mFourier n z ∂(herglotzMeasure C N)
      = ((C n * herglotzWeight d N n : ℝ) : ℂ) := fun N ↦ by
    rw [integral_mFourier_herglotzMeasure hC n N]
    push_cast
    ring
  have hproj : ∀ (g : UnitAddTorus d → ℝ) (hg : Continuous g)
      (r : ℝ) (_ : ∀ N, ∫ z, g z ∂(herglotzMeasure C N) = r * herglotzWeight d N n),
      ∫ z, g z ∂(ν : Measure (UnitAddTorus d)) = r := by
    intro g hg r hgN
    refine eq_of_clusterPt hcl
      (FiniteMeasure.continuous_integral_boundedContinuousFunction
        (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩)) ?_
    rw [Filter.tendsto_map'_iff]
    have : (fun N ↦ ∫ z, (BoundedContinuousFunction.mkOfCompact ⟨g, hg⟩ : UnitAddTorus d → ℝ) z
        ∂(μ N : Measure (UnitAddTorus d))) = fun N ↦ r * herglotzWeight d N n := funext hgN
    rw [Function.comp_def, this]
    simpa using (tendsto_herglotzWeight (d := d) n).const_mul r
  have hI : ∀ ρ : Measure (UnitAddTorus d), ∀ _ : IsFiniteMeasure ρ,
      Integrable (fun z ↦ mFourier n z) ρ := fun ρ _ ↦ integrable_mFourier ρ n
  have hre : ∫ z, (mFourier n z).re ∂(ν : Measure (UnitAddTorus d)) = C n := by
    refine hproj (fun z ↦ (mFourier n z).re)
      (Complex.continuous_re.comp (mFourier n).continuous) (C n) fun N ↦ ?_
    have h := Complex.reCLM.integral_comp_comm
      (hI (herglotzMeasure C N) (isFiniteMeasure_herglotzMeasure N))
    simp only [Complex.reCLM_apply] at h
    rw [h, hcoeff N, Complex.ofReal_re]
  have him : ∫ z, (mFourier n z).im ∂(ν : Measure (UnitAddTorus d)) = 0 := by
    refine hproj (fun z ↦ (mFourier n z).im)
      (Complex.continuous_im.comp (mFourier n).continuous) 0 fun N ↦ ?_
    have h := Complex.imCLM.integral_comp_comm
      (hI (herglotzMeasure C N) (isFiniteMeasure_herglotzMeasure N))
    simp only [Complex.imCLM_apply] at h
    rw [h, hcoeff N, Complex.ofReal_im, zero_mul]
  have hreν := Complex.reCLM.integral_comp_comm (hI (ν : Measure (UnitAddTorus d)) inferInstance)
  have himν := Complex.imCLM.integral_comp_comm (hI (ν : Measure (UnitAddTorus d)) inferInstance)
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hreν himν
  refine Complex.ext ?_ ?_
  · rw [← hreν, hre, Complex.ofReal_re]
  · rw [← himν, him, Complex.ofReal_im]

end Herglotz

end UnitAddTorus

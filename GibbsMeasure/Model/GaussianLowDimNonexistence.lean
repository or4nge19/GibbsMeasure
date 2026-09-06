/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianHomogeneousExtreme
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.BallInvNormPow
public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Georgii Corollary (13.41): no Gibbs measure in dimensions `d ≤ 2`

Georgii's Corollary (13.41). Let `d ≤ 2`, `h ∈ ℝ`, and let `J : ℤ^d → ℝ` be even, positive
definite and absolutely summable, and suppose there is a constant `L < ∞` with

  `∑_{0 < |i| ≤ m} |i|^d |J(i)| ≤ L log m`  for all `m ≥ 2`.

If `Ĵ(q) = 0` for some `q` on the torus `G` then `𝒢(γ^{J,h}) = ∅`.

## The analytic core

Everything is in the estimate `Ĵ(q + p) ≤ M ‖p‖^d log ‖p‖^{-1}` near the root: with it,
`∫_G Ĵ^{-1} dz = ∞` because `∫_0^δ (r log r^{-1})^{-1} dr = ∞`
(`MeasureTheory.setLIntegral_inv_mul_norm_pow_mul_log_inv_ball_eq_top`), and then
`𝒢(γ^{J,h}) = ∅` by the necessity half of Theorem (13.36),
`Potential.nonempty_G_homogeneousCoupling_iff`.

Georgii proves the estimate by expanding `Ĵ(p) - Ĵ(q)` and, in dimension `2`, adding the
vanishing gradient `grad Ĵ(q) = 0` (which he gets from `Ĵ ≥ 0`, `Ĵ(q) = 0` and the
differentiability of `Ĵ`, itself a consequence of `∑_i |i| |J(i)| < ∞`). **Here the gradient is
avoided**: `Ĵ` is *symmetrised* about the root,

  `Ĵ(q + u) + Ĵ(q - u) = 2 ∑_i J(i) Re(z_q^i) (Re(z_u^i) - 1)`   (`Ĵ(q) = 0`),

so that `0 ≤ Ĵ(q + u) ≤ Ĵ(q + u) + Ĵ(q - u) ≤ 2 ∑_i |J(i)| (1 - Re z_u^i)`
(`Potential.re_fourierHomogeneousCoupling_add_le`). The odd part — Georgii's gradient term — is
killed by the symmetrisation, in every dimension and with no differentiability at all. This is a
deviation from the book's proof, not from its statement.

The remaining estimate is Georgii's, with his splitting at `|i| = ‖p‖^{-2}`:
`1 - cos t ≤ |t|^n / n` for `n ∈ {1, 2}` on the head, `1 - cos t ≤ 2` on the tail. The head is
`≤ C ‖p‖^n log ‖p‖^{-1}` by the logarithmic hypothesis; the tail is `≤ C ‖p‖^n` because
`‖i‖ > ‖p‖^{-2}` forces `1 ≤ ‖p‖^n √(‖i‖^n)`, and `∑_i |J(i)| √(‖i‖^n)` converges — this last
point is where the logarithmic hypothesis is used a second time, through the dyadic estimate
`Potential.summable_abs_mul_sqrt_pow_norm`.

## Errata in Georgii's proof

* The exponent and the shape `M |p - q|^d log |p - q|^{-1}` are correct, and so is the splitting
  at `|i| = |p-q|^{-2}`; his tail bound uses `∑_i |J(i)| |i|^{d/2}` and `∑_i |J(i)| |i|^{3/2}`,
  both finite under the logarithmic hypothesis (dyadic blocks give
  `∑_{2^k < |i| ≤ 2^{k+1}} |J(i)| ≤ L (k+1) log 2 · 2^{-kd}`, so `∑_i |J(i)| |i|^s < ∞` for every
  `s < d`, and `d/2, 3/2 < 2 = d`).
* The constant in the polar-coordinate computation is wrong for `d = 1`: Georgii writes
  `∫_{|p-q| ≤ δ} |p-q|^{-d} (log|p-q|^{-1})^{-1} dp = (2π)^{d-1} ∫_0^δ (r log r^{-1})^{-1} dr`,
  and for `d = 1` the surface constant is `2` (the two points `±1`), not `(2π)^0 = 1`. Harmless:
  the integral is `∞`.

## Main results

* `Potential.summable_abs_mul_sqrt_pow_norm`: **the dyadic consequence of Georgii's hypothesis** —
  `∑_i |J(i)| √(‖i‖^n) < ∞`.
* `Potential.re_fourierHomogeneousCoupling_add_le`: **the symmetrisation at a root**,
  `Ĵ(q + u) ≤ 2 ∑_i |J(i)| (1 - Re z_u^i)`.
* `Potential.re_fourierHomogeneousCoupling_le_mul_log`: **Georgii's estimate near the root**,
  `Ĵ(q + p) ≤ M ‖p‖^n log ‖p‖^{-1}` for `‖p‖ < 1/2`.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_eq_top_of_root`: **the analytic content
  of (13.41)**, `∫_G Ĵ(z)^{-1} dz = ∞`.
* `Potential.not_nonempty_G_homogeneousCoupling_of_root`: **Corollary (13.41)** for the
  specifications `γ^{J,h}` of the tree, and
  `Potential.G_homogeneousCoupling_eq_empty_of_root`, the same statement as `𝒢(γ^{J,h}) = ∅`.
* `Potential.log_moment_of_finite_range` and
  `Potential.G_homogeneousCoupling_eq_empty_of_root_of_finiteRange`: Georgii's logarithmic
  condition is automatic for the finite-range `J` of the tree's standing hypotheses, so the
  corollary applies to every `γ^{J,h}` that is defined. Specialised to Example (13.43) this
  reproves `Potential.not_nonempty_G_harmonicCrystalCoupling` of
  `GibbsMeasure/Model/GaussianHarmonicCrystalLowDim.lean`, which is the same statement for the
  harmonic crystal with the elementary bound `Ĵ(z_p) ≤ 2π²β‖p‖²` in place of the logarithmic
  one.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Set

open scoped ENNReal

noncomputable section

namespace Potential

/-! ### Georgii's logarithmic moment condition and its dyadic consequence -/

section LogMoment

variable {d : Type*} [Fintype d] [DecidableEq d] {J' : (d → ℤ) → ℝ} {L : ℝ} {n : ℕ}

/-- **The index set of Georgii's hypothesis in Corollary (13.41)**: the lattice points of `ℤ^d`
of supremum norm at most `m`. Georgii writes `{0 < |i| ≤ m}` with the Euclidean norm; the two
conditions define the same class of couplings `J`, because two norms on `ℝ^d` differ by a factor
`c` and `log (c m) ≤ (1 + log c / log 2) log m` for `m ≥ 2`. -/
abbrev latticeCube (d : Type*) [Fintype d] [DecidableEq d] (m : ℕ) : Finset (d → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-(m : ℤ)) (m : ℤ)

lemma mem_latticeCube_iff {m : ℕ} {i : d → ℤ} : i ∈ latticeCube d m ↔ ‖i‖ ≤ m := by
  rw [latticeCube, Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg (by positivity)]
  simp only [Finset.mem_Icc, Int.norm_eq_abs, abs_le]
  refine forall_congr' fun ℓ ↦ ⟨fun h ↦ ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩,
    fun h ↦ ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩⟩

lemma latticeCube_subset {m m' : ℕ} (h : m ≤ m') : latticeCube d m ⊆ latticeCube d m' := by
  intro i hi
  rw [mem_latticeCube_iff] at hi ⊢
  exact hi.trans (by exact_mod_cast h)

/-- `√(2 ^ m) = (√2) ^ m`. -/
private lemma sqrt_two_pow (m : ℕ) : Real.sqrt ((2 : ℝ) ^ m) = Real.sqrt 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ih]

/-- Georgii's hypothesis forces the constant `L` to be nonnegative. -/
lemma nonneg_of_log_moment
    (hlog : ∀ m : ℕ, 2 ≤ m → ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ n ≤ L * Real.log m) :
    0 ≤ L := by
  have h2 := hlog 2 le_rfl
  have hnn : (0 : ℝ) ≤ ∑ i ∈ latticeCube d 2, |J' i| * ‖i‖ ^ n :=
    Finset.sum_nonneg fun i _ ↦ by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hle : (0 : ℝ) ≤ L * Real.log ((2 : ℕ) : ℝ) := le_trans hnn h2
  rw [show (((2 : ℕ) : ℝ)) = (2 : ℝ) by norm_num] at hle
  nlinarith

/-- **The dyadic block estimate.** Outside the cube `‖i‖ ≤ 2^j` the weight `√(‖i‖^n)` is at most
`‖i‖^n / (√2)^{jn}`, and Georgii's hypothesis bounds `∑ |J(i)| ‖i‖^n` over the cube `‖i‖ ≤ 2^{j+1}`
by `L (j+1) log 2`. -/
lemma sum_sdiff_latticeCube_le
    (hlog : ∀ m : ℕ, 2 ≤ m → ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ n ≤ L * Real.log m) (j : ℕ) :
    ∑ i ∈ latticeCube d (2 ^ (j + 1)) \ latticeCube d (2 ^ j), |J' i| * Real.sqrt (‖i‖ ^ n)
      ≤ L * Real.log 2 * (((j : ℝ) + 1) * ((Real.sqrt 2 ^ n)⁻¹) ^ j) := by
  have hL : 0 ≤ L := nonneg_of_log_moment hlog
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := by linarith
  have hinv : ((Real.sqrt 2 ^ n)⁻¹) ^ j = (Real.sqrt 2 ^ (j * n))⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm n j]
  -- pointwise bound outside the inner cube
  have hpt : ∀ i ∈ latticeCube d (2 ^ (j + 1)) \ latticeCube d (2 ^ j),
      |J' i| * Real.sqrt (‖i‖ ^ n) ≤ ((Real.sqrt 2 ^ n)⁻¹) ^ j * (|J' i| * ‖i‖ ^ n) := by
    intro i hi
    simp only [Finset.mem_sdiff, mem_latticeCube_iff, not_le] at hi
    have hlow : ((2 : ℝ) ^ j) < ‖i‖ := by exact_mod_cast hi.2
    have hpos : (0 : ℝ) < ‖i‖ := lt_of_lt_of_le (by positivity) hlow.le
    have hsq : Real.sqrt 2 ^ (j * n) ≤ Real.sqrt (‖i‖ ^ n) := by
      rw [show Real.sqrt 2 ^ (j * n) = Real.sqrt (((2 : ℝ) ^ j) ^ n) by
        rw [← pow_mul, sqrt_two_pow]]
      exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hlow.le n)
    have hsqpos : (0 : ℝ) < Real.sqrt 2 ^ (j * n) := by positivity
    have hsq0 : (0 : ℝ) < Real.sqrt (‖i‖ ^ n) := Real.sqrt_pos.2 (by positivity)
    have hid : Real.sqrt (‖i‖ ^ n) * Real.sqrt (‖i‖ ^ n) = ‖i‖ ^ n :=
      Real.mul_self_sqrt (by positivity)
    have hkey : Real.sqrt (‖i‖ ^ n) ≤ ((Real.sqrt 2 ^ n)⁻¹) ^ j * ‖i‖ ^ n := by
      rw [hinv, inv_mul_eq_div, le_div_iff₀ hsqpos]
      nlinarith [hsq, hsq0, hid]
    calc |J' i| * Real.sqrt (‖i‖ ^ n)
        ≤ |J' i| * (((Real.sqrt 2 ^ n)⁻¹) ^ j * ‖i‖ ^ n) :=
          mul_le_mul_of_nonneg_left hkey (abs_nonneg _)
      _ = ((Real.sqrt 2 ^ n)⁻¹) ^ j * (|J' i| * ‖i‖ ^ n) := by ring
  calc ∑ i ∈ latticeCube d (2 ^ (j + 1)) \ latticeCube d (2 ^ j), |J' i| * Real.sqrt (‖i‖ ^ n)
      ≤ ∑ i ∈ latticeCube d (2 ^ (j + 1)) \ latticeCube d (2 ^ j),
          ((Real.sqrt 2 ^ n)⁻¹) ^ j * (|J' i| * ‖i‖ ^ n) := Finset.sum_le_sum hpt
    _ = ((Real.sqrt 2 ^ n)⁻¹) ^ j *
          ∑ i ∈ latticeCube d (2 ^ (j + 1)) \ latticeCube d (2 ^ j), |J' i| * ‖i‖ ^ n :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ((Real.sqrt 2 ^ n)⁻¹) ^ j * ∑ i ∈ latticeCube d (2 ^ (j + 1)), |J' i| * ‖i‖ ^ n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          fun i _ _ ↦ by positivity
    _ ≤ ((Real.sqrt 2 ^ n)⁻¹) ^ j * (L * Real.log ((2 ^ (j + 1) : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (hlog _ ?_) (by positivity)
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = L * Real.log 2 * (((j : ℝ) + 1) * ((Real.sqrt 2 ^ n)⁻¹) ^ j) := by
        rw [show (((2 ^ (j + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (j + 1) by push_cast; ring,
          Real.log_pow]
        push_cast
        ring

/-- **Georgii's logarithmic hypothesis implies `∑_i |J(i)| √(‖i‖^n) < ∞`.** This is the
quantitative content of his remark, in the proof of (13.41), that the tail sums
`∑_{|i| > ρ} |J(i)| [2|i|^{d/2} + (d-1)|i|^{3/2}]` converge: from `∑_{‖i‖ ≤ m} |J(i)| ‖i‖^n ≤
L log m` the dyadic blocks give `∑_{2^j < ‖i‖ ≤ 2^{j+1}} |J(i)| ≤ L (j+1) log 2 · 2^{-jn}`, so
`∑_i |J(i)| ‖i‖^s < ∞` for every `s < n`; `s = n/2` is the case used below. -/
theorem summable_abs_mul_sqrt_pow_norm (hn : 1 ≤ n) (hJ : Summable fun i ↦ |J' i|)
    (hlog : ∀ m : ℕ, 2 ≤ m → ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ n ≤ L * Real.log m) :
    Summable fun i ↦ |J' i| * Real.sqrt (‖i‖ ^ n) := by
  classical
  have hL : 0 ≤ L := nonneg_of_log_moment hlog
  have hs2 : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set q : ℝ := (Real.sqrt 2 ^ n)⁻¹ with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  have hq1 : q < 1 := by
    rw [hq, inv_lt_one_iff₀]
    exact Or.inr (one_lt_pow₀ hs2 (by omega))
  have hgeo : Summable fun j : ℕ ↦ ((j : ℝ) + 1) * q ^ j := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q)
      (by rw [Real.norm_eq_abs, abs_of_pos hqpos]; exact hq1)
    have h2 : Summable fun j : ℕ ↦ q ^ j := summable_geometric_of_lt_one hqpos.le hq1
    refine (h1.add h2).congr fun j ↦ ?_
    simp only [pow_one]
    ring
  set T : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) * q ^ j with hT
  set A : ℝ := ∑' i, |J' i| with hA
  -- the inner cube
  have hbase : ∑ i ∈ latticeCube d 1, |J' i| * Real.sqrt (‖i‖ ^ n) ≤ A := by
    refine le_trans (Finset.sum_le_sum fun i hi ↦ ?_)
      (hJ.sum_le_tsum _ fun i _ ↦ abs_nonneg _)
    rw [mem_latticeCube_iff] at hi
    have h1 : ‖i‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (by exact_mod_cast hi)
    have h2 : Real.sqrt (‖i‖ ^ n) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt h1
    nlinarith [abs_nonneg (J' i), Real.sqrt_nonneg (‖i‖ ^ n)]
  -- the dyadic bound on the cubes `‖i‖ ≤ 2^{K+1}`
  have hcube : ∀ K : ℕ, ∑ i ∈ latticeCube d (2 ^ (K + 1)), |J' i| * Real.sqrt (‖i‖ ^ n)
      ≤ A + L * Real.log 2 * ∑ j ∈ Finset.range (K + 1), ((j : ℝ) + 1) * q ^ j := by
    intro K
    induction K with
    | zero =>
        have hsub : latticeCube d (2 ^ 0) ⊆ latticeCube d (2 ^ (0 + 1)) :=
          latticeCube_subset (by norm_num)
        rw [← Finset.sum_sdiff (f := fun i ↦ |J' i| * Real.sqrt (‖i‖ ^ n)) hsub]
        have hb := sum_sdiff_latticeCube_le hlog (J' := J') (L := L) (n := n) 0
        have hc0 : latticeCube d (2 ^ 0) = latticeCube d 1 := by norm_num
        rw [hc0] at hb ⊢
        simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_zero, mul_one] at hb ⊢
        linarith
    | succ K ih =>
        have hsub : latticeCube d (2 ^ (K + 1)) ⊆ latticeCube d (2 ^ (K + 1 + 1)) :=
          latticeCube_subset (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [← Finset.sum_sdiff (f := fun i ↦ |J' i| * Real.sqrt (‖i‖ ^ n)) hsub,
          Finset.sum_range_succ]
        have hb := sum_sdiff_latticeCube_le hlog (J' := J') (L := L) (n := n) (K + 1)
        rw [← hq] at hb
        push_cast at hb ⊢
        linarith [ih, hb]
  -- every finite set sits in such a cube
  refine summable_of_sum_le (c := A + L * Real.log 2 * T) (fun i ↦ by positivity) fun F ↦ ?_
  set N : ℕ := F.sup fun i ↦ ⌈‖i‖⌉₊ with hN
  have hFsub : F ⊆ latticeCube d (2 ^ (N + 1)) := by
    intro i hi
    rw [mem_latticeCube_iff]
    have h1 : ‖i‖ ≤ (⌈‖i‖⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈‖i‖⌉₊ : ℕ) ≤ N := Finset.le_sup (f := fun i ↦ ⌈‖i‖⌉₊) hi
    have h3 : N ≤ 2 ^ (N + 1) := le_trans (Nat.le_succ N) (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
    calc ‖i‖ ≤ (⌈‖i‖⌉₊ : ℝ) := h1
      _ ≤ (N : ℝ) := by exact_mod_cast h2
      _ ≤ ((2 ^ (N + 1) : ℕ) : ℝ) := by exact_mod_cast h3
  calc ∑ i ∈ F, |J' i| * Real.sqrt (‖i‖ ^ n)
      ≤ ∑ i ∈ latticeCube d (2 ^ (N + 1)), |J' i| * Real.sqrt (‖i‖ ^ n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hFsub fun i _ _ ↦ by positivity
    _ ≤ A + L * Real.log 2 * ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + 1) * q ^ j := hcube N
    _ ≤ A + L * Real.log 2 * T := by
        have hle : ∑ j ∈ Finset.range (N + 1), ((j : ℝ) + 1) * q ^ j ≤ T :=
          hgeo.sum_le_tsum _ fun j _ ↦ by positivity
        have hLl : (0 : ℝ) ≤ L * Real.log 2 :=
          mul_nonneg hL (Real.log_nonneg (by norm_num))
        linarith [mul_le_mul_of_nonneg_left hle hLl]

end LogMoment

/-! ### The symmetrisation of `Ĵ` at a root -/

section Symmetrisation

open UnitAddTorus

attribute [local instance] Potential.instMeasureSpaceUnitAddCircle
  Potential.instIsAddHaarMeasureUnitAddCircleVolume
  Potential.instIsProbabilityMeasureUnitAddCircleVolume

variable {d : Type*} [Fintype d] {J' : (d → ℤ) → ℝ}

lemma one_sub_re_mFourier_nonneg (i : d → ℤ) (u : UnitAddTorus d) :
    0 ≤ 1 - (mFourier i u).re := by
  have h1 := Complex.abs_re_le_norm (mFourier i u)
  rw [norm_mFourier_apply] at h1
  linarith [(abs_le.1 h1).2]

lemma one_sub_re_mFourier_le_two (i : d → ℤ) (u : UnitAddTorus d) :
    1 - (mFourier i u).re ≤ 2 := by
  have h1 := Complex.abs_re_le_norm (mFourier i u)
  rw [norm_mFourier_apply] at h1
  linarith [(abs_le.1 h1).1]

lemma summable_mul_re_mFourier (hJ : Summable fun i ↦ |J' i|) (z : UnitAddTorus d) :
    Summable fun i ↦ J' i * (mFourier i z).re := by
  refine Summable.of_abs (hJ.of_nonneg_of_le (fun i ↦ abs_nonneg _) fun i ↦ ?_)
  rw [abs_mul]
  have h1 := Complex.abs_re_le_norm (mFourier i z)
  rw [norm_mFourier_apply] at h1
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- `Ĵ(z)` is the real series `∑_i J(i) Re z^i` when `J` is absolutely summable. -/
lemma re_fourierHomogeneousCoupling_eq_tsum (hJ : Summable fun i ↦ |J' i|) (z : UnitAddTorus d) :
    (fourierHomogeneousCoupling J' z).re = ∑' i, J' i * (mFourier i z).re := by
  have hsum : Summable fun i : d → ℤ ↦ (J' i : ℂ) * mFourier i z :=
    summable_mul_mFourier (summable_ofReal_of_summable_abs hJ) z
  rw [fourierHomogeneousCoupling, Complex.re_tsum hsum]
  exact tsum_congr fun i ↦ by simp [Complex.mul_re]

/-- The real parts of `z^i` at `q + u` and at `q - u` add up to `2 Re(z_q^i) Re(z_u^i)`: the odd
part about `q` cancels. -/
lemma re_mFourier_add_add_re_mFourier_sub (i : d → ℤ) (q u : UnitAddTorus d) :
    (mFourier i (q + u)).re + (mFourier i (q - u)).re
      = 2 * (mFourier i q).re * (mFourier i u).re := by
  have h2 : ‖mFourier i u‖ = 1 := norm_mFourier_apply i u
  have hne : mFourier i u ≠ 0 := by
    intro hc
    rw [hc] at h2
    simp at h2
  have h1 : mFourier i u * mFourier i (-u) = 1 := by
    rw [← mFourier_add_apply, add_neg_cancel, mFourier_zero_apply]
  have hinv : mFourier i (-u) = (starRingEnd ℂ) (mFourier i u) := by
    rw [← Complex.inv_eq_conj h2]
    field_simp
    linear_combination h1
  rw [sub_eq_add_neg, mFourier_add_apply, mFourier_add_apply, hinv, ← Complex.add_re,
    ← mul_add, Complex.add_conj, Complex.mul_re]
  simp
  ring

/-- **The symmetrisation of `Ĵ` at a root.** If `Ĵ ≥ 0` and `Ĵ(q) = 0` then, for every `u` on the
torus,

  `Ĵ(q + u) ≤ 2 ∑_i |J(i)| (1 - Re z_u^i)`.

This replaces Georgii's step "since `Ĵ ≥ 0` and `Ĵ(q) = 0`, `grad Ĵ(q) = 0`" in the proof of
Corollary (13.41): adding the value at `q - u` cancels the odd part of `Ĵ` about `q`, so no
differentiability of `Ĵ` — and hence no extra summability of `J` — is needed. -/
theorem re_fourierHomogeneousCoupling_add_le (hJ : Summable fun i ↦ |J' i|)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : (fourierHomogeneousCoupling J' q).re = 0) (u : UnitAddTorus d) :
    (fourierHomogeneousCoupling J' (q + u)).re
      ≤ 2 * ∑' i, |J' i| * (1 - (mFourier i u).re) := by
  set a : (d → ℤ) → ℝ := fun i ↦ J' i * (mFourier i q).re with ha
  have habs : ∀ i, |a i| ≤ |J' i| := by
    intro i
    have h1 := Complex.abs_re_le_norm (mFourier i q)
    rw [norm_mFourier_apply] at h1
    rw [ha, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) h1
  have hasum : Summable a := summable_mul_re_mFourier hJ q
  have ha0 : ∑' i, a i = 0 := by
    rw [ha, ← re_fourierHomogeneousCoupling_eq_tsum hJ q]
    exact hq
  have hsub : Summable fun i ↦ a i * ((mFourier i u).re - 1) := by
    refine Summable.of_abs ((hJ.mul_left 2).of_nonneg_of_le (fun i ↦ abs_nonneg _) fun i ↦ ?_)
    rw [abs_mul]
    have hb : |(mFourier i u).re - 1| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [one_sub_re_mFourier_le_two i u],
        by linarith [one_sub_re_mFourier_nonneg i u]⟩
    calc |a i| * |(mFourier i u).re - 1| ≤ |J' i| * 2 :=
          mul_le_mul (habs i) hb (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |J' i| := by ring
  have hmaj : Summable fun i ↦ |J' i| * (1 - (mFourier i u).re) := by
    refine (hJ.mul_left 2).of_nonneg_of_le
      (fun i ↦ mul_nonneg (abs_nonneg _) (one_sub_re_mFourier_nonneg i u)) fun i ↦ ?_
    calc |J' i| * (1 - (mFourier i u).re) ≤ |J' i| * 2 :=
          mul_le_mul_of_nonneg_left (one_sub_re_mFourier_le_two i u) (abs_nonneg _)
      _ = 2 * |J' i| := by ring
  have hkey : (fourierHomogeneousCoupling J' (q + u)).re
      + (fourierHomogeneousCoupling J' (q - u)).re
      = 2 * ∑' i, a i * ((mFourier i u).re - 1) := by
    rw [re_fourierHomogeneousCoupling_eq_tsum hJ, re_fourierHomogeneousCoupling_eq_tsum hJ,
      ← Summable.tsum_add (summable_mul_re_mFourier hJ (q + u))
        (summable_mul_re_mFourier hJ (q - u))]
    have hterm : ∀ i, J' i * (mFourier i (q + u)).re + J' i * (mFourier i (q - u)).re
        = 2 * (a i * ((mFourier i u).re - 1)) + 2 * a i := by
      intro i
      have hi := re_mFourier_add_add_re_mFourier_sub i q u
      rw [ha]
      linear_combination J' i * hi
    rw [tsum_congr hterm, Summable.tsum_add (hsub.mul_left 2) (hasum.mul_left 2),
      hsub.tsum_mul_left 2, hasum.tsum_mul_left 2, ha0]
    ring
  have hle : ∀ i, a i * ((mFourier i u).re - 1) ≤ |J' i| * (1 - (mFourier i u).re) := by
    intro i
    have h2 := one_sub_re_mFourier_nonneg i u
    calc a i * ((mFourier i u).re - 1) = (-(a i)) * (1 - (mFourier i u).re) := by ring
      _ ≤ |a i| * (1 - (mFourier i u).re) := mul_le_mul_of_nonneg_right (neg_le_abs (a i)) h2
      _ ≤ |J' i| * (1 - (mFourier i u).re) := mul_le_mul_of_nonneg_right (habs i) h2
  calc (fourierHomogeneousCoupling J' (q + u)).re
      ≤ (fourierHomogeneousCoupling J' (q + u)).re
        + (fourierHomogeneousCoupling J' (q - u)).re := le_add_of_nonneg_right (hpos _)
    _ = 2 * ∑' i, a i * ((mFourier i u).re - 1) := hkey
    _ ≤ 2 * ∑' i, |J' i| * (1 - (mFourier i u).re) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hle hsub hmaj) (by norm_num)

end Symmetrisation

/-! ### Georgii's estimate near the root -/

section NearRoot

open UnitAddTorus

attribute [local instance] Potential.instMeasureSpaceUnitAddCircle
  Potential.instIsAddHaarMeasureUnitAddCircleVolume
  Potential.instIsProbabilityMeasureUnitAddCircleVolume

variable {d : Type*} [Fintype d] [DecidableEq d] {J' : (d → ℤ) → ℝ} {L : ℝ}

/-- `1 - cos t ≤ |t|^n / n` for `n = 1` and `n = 2`. For `n = 1` this is the Lipschitz bound
`|cos t - cos 0| ≤ |t|`, for `n = 2` the Taylor bound `1 - t²/2 ≤ cos t`. (It fails for `n ≥ 3`:
take `t = π`.) -/
lemma one_sub_cos_le_pow_div {n : ℕ} (hn1 : 1 ≤ n) (hn2 : n ≤ 2) (t : ℝ) :
    1 - Real.cos t ≤ |t| ^ n / n := by
  interval_cases n
  · have h := Real.abs_cos_sub_cos_le t 0
    rw [Real.cos_zero, sub_zero] at h
    simp only [pow_one, Nat.cast_one, div_one]
    linarith [(abs_le.1 h).1]
  · have h := Real.one_sub_sq_div_two_le_cos (x := t)
    rw [show |t| ^ 2 = t ^ 2 from sq_abs t]
    push_cast
    linarith

/-- `|⟨i, x⟩| ≤ (card d) ‖i‖ ‖x‖` for the supremum norms on `ℤ^d` and `ℝ^d`. -/
lemma abs_inner_le (i : d → ℤ) (x : d → ℝ) :
    |∑ ℓ, (i ℓ : ℝ) * x ℓ| ≤ (Fintype.card d : ℝ) * ‖i‖ * ‖x‖ := by
  calc |∑ ℓ, (i ℓ : ℝ) * x ℓ| ≤ ∑ ℓ, |(i ℓ : ℝ) * x ℓ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ℓ : d, ‖i‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun ℓ _ ↦ ?_
        rw [abs_mul]
        have h1 : |(i ℓ : ℝ)| ≤ ‖i‖ := by
          rw [← Int.norm_eq_abs]
          exact norm_le_pi_norm i ℓ
        have h2 : |x ℓ| ≤ ‖x‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm x ℓ
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card d : ℝ) * ‖i‖ * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]

/-- `Re z_x^i = cos(2π ⟨i, x⟩)` for the point `x mod 1` of the torus. -/
lemma re_mFourier_coe (i : d → ℤ) (x : d → ℝ) :
    (mFourier i (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re
      = Real.cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ) := by
  rw [mFourier_coe]
  have hsum : (∑ ℓ, 2 * (Real.pi : ℂ) * Complex.I * (i ℓ : ℂ) * (x ℓ : ℂ))
      = ((2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun ℓ _ ↦ by ring
  rw [hsum, Complex.exp_ofReal_mul_I_re]

/-- **Georgii's estimate near a root of `Ĵ`.** Under his logarithmic hypothesis there is a
constant `M` with

  `Ĵ(q + p) ≤ M ‖p‖^d log ‖p‖^{-1}`  for `‖p‖ < 1/2`,

`q` being a root of `Ĵ` on the torus. This is his displayed chain of inequalities in the proof of
Corollary (13.41), with the splitting at `‖i‖ = ‖p‖^{-2}`: on the head `1 - cos t ≤ |t|^d / d`
and the logarithmic hypothesis give `≤ C ‖p‖^d log ‖p‖^{-1}`; on the tail `1 - cos t ≤ 2` and
`1 ≤ ‖p‖^d √(‖i‖^d)` give `≤ C ‖p‖^d`. -/
theorem re_fourierHomogeneousCoupling_le_mul_log
    (hn1 : 1 ≤ Fintype.card d) (hn2 : Fintype.card d ≤ 2) (hJ : Summable fun i ↦ |J' i|)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : (fourierHomogeneousCoupling J' q).re = 0)
    (hlog : ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ L * Real.log m) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : d → ℝ, ‖x‖ < 1 / 2 →
      (fourierHomogeneousCoupling J' (q + fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re
        ≤ M * ‖x‖ ^ Fintype.card d * Real.log ‖x‖⁻¹ := by
  classical
  set n : ℕ := Fintype.card d with hn
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hL : 0 ≤ L := nonneg_of_log_moment hlog
  have hB := summable_abs_mul_sqrt_pow_norm hn1 hJ hlog
  set B : ℝ := ∑' i, |J' i| * Real.sqrt (‖i‖ ^ n) with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun i ↦ by positivity
  set κ : ℝ := (2 * Real.pi * (n : ℝ)) ^ n / (n : ℝ) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * (3 * κ * L + 2 * B / Real.log 2) + 1, by positivity, fun x hx ↦ ?_⟩
  set r : ℝ := ‖x‖ with hr
  rcases eq_or_lt_of_le (norm_nonneg x) with hr0 | hr0
  · -- `x = 0`: both sides vanish, because `q` is a root
    have hx0 : (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle)) = (0 : UnitAddTorus d) := by
      have : x = 0 := by
        rw [← norm_eq_zero]
        exact hr0.symm
      rw [this]
      funext ℓ
      simp
    rw [hx0, add_zero, hq]
    have hrz : r = 0 := hr.trans hr0.symm
    rw [hrz, zero_pow (show n ≠ 0 by omega)]
    simp
  -- the splitting radius
  set m : ℕ := ⌈r⁻¹ ^ 2⌉₊ with hm
  have hrlt : r < 1 / 2 := hx
  have hrinv : (2 : ℝ) < r⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hr0]
    linarith
  have hm4 : (4 : ℝ) ≤ r⁻¹ ^ 2 := by nlinarith
  have hmge : (r⁻¹ ^ 2 : ℝ) ≤ (m : ℝ) := Nat.le_ceil _
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hmle : (m : ℝ) ≤ 2 * r⁻¹ ^ 2 := by
    have h1 : (m : ℝ) ≤ r⁻¹ ^ 2 + 1 := by
      have := Nat.ceil_lt_add_one (a := r⁻¹ ^ 2) (by positivity)
      linarith
    linarith
  have hlogr : Real.log 2 ≤ Real.log r⁻¹ := by
    refine Real.log_le_log (by norm_num) ?_
    linarith
  have hlogrpos : 0 < Real.log r⁻¹ := lt_of_lt_of_le hlog2 hlogr
  -- `log m ≤ 3 log r⁻¹`
  have hlogm : Real.log (m : ℝ) ≤ 3 * Real.log r⁻¹ := by
    have h1 : Real.log (m : ℝ) ≤ Real.log (2 * r⁻¹ ^ 2) := by
      refine Real.log_le_log ?_ hmle
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      linarith
    have h2 : Real.log (2 * r⁻¹ ^ 2) = Real.log 2 + 2 * Real.log r⁻¹ := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    linarith
  -- the head and tail majorants
  set head : (d → ℤ) → ℝ :=
    fun i ↦ if ‖i‖ ≤ (m : ℝ) then κ * r ^ n * (|J' i| * ‖i‖ ^ n) else 0 with hhead
  set tail : (d → ℤ) → ℝ :=
    fun i ↦ if ‖i‖ ≤ (m : ℝ) then 0 else 2 * (r ^ n * (|J' i| * Real.sqrt (‖i‖ ^ n)))
    with htail
  have hheadsupp : ∀ i ∉ latticeCube d m, head i = 0 := by
    intro i hi
    rw [hhead]
    simp only
    rw [if_neg]
    exact fun hc ↦ hi (mem_latticeCube_iff.2 hc)
  have hheadsum : Summable head :=
    summable_of_finite_support (Set.Finite.subset (latticeCube d m).finite_toSet fun i hi ↦ by
      by_contra hc
      exact hi (hheadsupp i hc))
  have htailsum : Summable tail := by
    refine ((hB.mul_left (2 * r ^ n)).of_nonneg_of_le (fun i ↦ ?_) fun i ↦ ?_)
    · rw [htail]
      dsimp only
      split
      · positivity
      · positivity
    · rw [htail]
      dsimp only
      split
      · positivity
      · apply le_of_eq; ring
  -- the pointwise bound
  have hpt : ∀ i, |J' i| * (1 - (mFourier i (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re)
      ≤ head i + tail i := by
    intro i
    rw [re_mFourier_coe]
    by_cases hi : ‖i‖ ≤ (m : ℝ)
    · rw [hhead, htail]
      simp only [if_pos hi, add_zero]
      have hcos := one_sub_cos_le_pow_div hn1 hn2 (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ)
      have habs : |2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ| ≤ 2 * Real.pi * ((n : ℝ) * ‖i‖ * r) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
        exact mul_le_mul_of_nonneg_left (abs_inner_le i x) (by positivity)
      have hpow : |2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ| ^ n
          ≤ (2 * Real.pi * ((n : ℝ) * ‖i‖ * r)) ^ n :=
        pow_le_pow_left₀ (abs_nonneg _) habs n
      have hfin : (2 * Real.pi * ((n : ℝ) * ‖i‖ * r)) ^ n / (n : ℝ)
          = κ * r ^ n * ‖i‖ ^ n := by
        rw [hκ]
        rw [show 2 * Real.pi * ((n : ℝ) * ‖i‖ * r) = (2 * Real.pi * (n : ℝ)) * (‖i‖ * r) by ring,
          mul_pow, mul_pow]
        field_simp
        ring
      have hstep : 1 - Real.cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ) ≤ κ * r ^ n * ‖i‖ ^ n := by
        refine hcos.trans ?_
        rw [← hfin]
        exact div_le_div_of_nonneg_right hpow hN.le
      calc |J' i| * (1 - Real.cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ))
          ≤ |J' i| * (κ * r ^ n * ‖i‖ ^ n) :=
            mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
        _ = κ * r ^ n * (|J' i| * ‖i‖ ^ n) := by ring
    · rw [hhead, htail]
      simp only [if_neg hi, zero_add]
      push_neg at hi
      have hnorm : (m : ℝ) < ‖i‖ := hi
      have hge : r⁻¹ ^ 2 ≤ ‖i‖ := le_trans hmge hnorm.le
      have hipos : (0 : ℝ) < ‖i‖ := lt_of_lt_of_le (by positivity) hge
      have hsqrt : r⁻¹ ^ n ≤ Real.sqrt (‖i‖ ^ n) := by
        rw [show (r⁻¹ : ℝ) ^ n = Real.sqrt ((r⁻¹ ^ 2) ^ n) by
          rw [← pow_mul, mul_comm 2 n, pow_mul, Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hge n)
      have hone : (1 : ℝ) ≤ r ^ n * Real.sqrt (‖i‖ ^ n) := by
        have h1 : r ^ n * r⁻¹ ^ n = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hr0.ne', one_pow]
        calc (1 : ℝ) = r ^ n * r⁻¹ ^ n := h1.symm
          _ ≤ r ^ n * Real.sqrt (‖i‖ ^ n) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      have hcos2 : 1 - Real.cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ) ≤ 2 := by
        have := Real.neg_one_le_cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ)
        linarith
      calc |J' i| * (1 - Real.cos (2 * Real.pi * ∑ ℓ, (i ℓ : ℝ) * x ℓ))
          ≤ |J' i| * 2 := mul_le_mul_of_nonneg_left hcos2 (abs_nonneg _)
        _ = 2 * (|J' i| * 1) := by ring
        _ ≤ 2 * (|J' i| * (r ^ n * Real.sqrt (‖i‖ ^ n))) := by
            have : |J' i| * 1 ≤ |J' i| * (r ^ n * Real.sqrt (‖i‖ ^ n)) :=
              mul_le_mul_of_nonneg_left hone (abs_nonneg _)
            linarith
        _ = 2 * (r ^ n * (|J' i| * Real.sqrt (‖i‖ ^ n))) := by ring
  -- summing the two majorants
  have hheadval : ∑' i, head i ≤ κ * r ^ n * (L * (3 * Real.log r⁻¹)) := by
    rw [tsum_eq_sum hheadsupp]
    have hval : ∑ i ∈ latticeCube d m, head i
        = κ * r ^ n * ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [hhead]
      simp only
      rw [if_pos (mem_latticeCube_iff.1 hi)]
    rw [hval]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (hlog m hm2) ?_
    exact mul_le_mul_of_nonneg_left hlogm hL
  have htailval : ∑' i, tail i ≤ 2 * (r ^ n * B) := by
    rw [hBdef, ← mul_assoc, ← hB.tsum_mul_left (2 * r ^ n)]
    refine Summable.tsum_le_tsum (fun i ↦ ?_) htailsum (hB.mul_left (2 * r ^ n))
    rw [htail]
    dsimp only
    split
    · positivity
    · apply le_of_eq; ring
  -- assembling
  have hmain : (fourierHomogeneousCoupling J' (q + fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re
      ≤ 2 * (κ * r ^ n * (L * (3 * Real.log r⁻¹)) + 2 * (r ^ n * B)) := by
    refine le_trans (re_fourierHomogeneousCoupling_add_le hJ hpos hq _) ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have hsum1 : Summable fun i ↦ |J' i| *
        (1 - (mFourier i (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re) := by
      refine (hJ.mul_left 2).of_nonneg_of_le
        (fun i ↦ mul_nonneg (abs_nonneg _) (one_sub_re_mFourier_nonneg _ _)) fun i ↦ ?_
      calc |J' i| * (1 - (mFourier i (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re)
          ≤ |J' i| * 2 := mul_le_mul_of_nonneg_left (one_sub_re_mFourier_le_two _ _)
            (abs_nonneg _)
        _ = 2 * |J' i| := by ring
    calc ∑' i, |J' i| * (1 - (mFourier i (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re)
        ≤ ∑' i, (head i + tail i) :=
          Summable.tsum_le_tsum hpt hsum1 (hheadsum.add htailsum)
      _ = ∑' i, head i + ∑' i, tail i := Summable.tsum_add hheadsum htailsum
      _ ≤ κ * r ^ n * (L * (3 * Real.log r⁻¹)) + 2 * (r ^ n * B) := by
          exact add_le_add hheadval htailval
  refine hmain.trans ?_
  have hrn : (0 : ℝ) < r ^ n := by positivity
  have hkey : 2 * B ≤ 2 * B / Real.log 2 * Real.log r⁻¹ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    nlinarith
  nlinarith [hrn, hlogrpos, hB0, hκ0, hL]

end NearRoot

/-! ### Corollary (13.41) -/

section Corollary

open UnitAddTorus

attribute [local instance] Potential.instMeasureSpaceUnitAddCircle
  Potential.instIsAddHaarMeasureUnitAddCircleVolume
  Potential.instIsProbabilityMeasureUnitAddCircleVolume

variable {d : Type*} [Fintype d] [DecidableEq d] {J' : (d → ℤ) → ℝ} {L : ℝ}

/-- **The analytic content of Georgii's Corollary (13.41)**: in dimensions `d ≤ 2` a root of `Ĵ`
on the torus forces `∫_G Ĵ(z)⁻¹ dz = ∞`.

Translate the root to the origin, read the torus integral on the fundamental cube
`]-1/2, 1/2]^d`, restrict it to the ball of radius `1/2`, and use Georgii's estimate
`Ĵ(q + p) ≤ M ‖p‖^d log ‖p‖^{-1}` together with the divergence of
`∫_{‖p‖ < 1/2} (‖p‖^d log ‖p‖^{-1})^{-1} dp` for `d ≤ 2`. -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_eq_top_of_root
    (hn1 : 1 ≤ Fintype.card d) (hn2 : Fintype.card d ≤ 2) (hJ : Summable fun i ↦ |J' i|)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : (fourierHomogeneousCoupling J' q).re = 0)
    (hlog : ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ L * Real.log m) :
    ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ = ∞ := by
  haveI : Nonempty d := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨M, hM0, hMle⟩ :=
    re_fourierHomogeneousCoupling_le_mul_log hn1 hn2 hJ hpos hq hlog
  rw [← lintegral_add_left_eq_self
    (fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹) q,
    UnitAddTorus.lintegral_preimage _ fun _ : d ↦ (-(1 : ℝ) / 2)]
  -- the open ball of radius `1/2` for the supremum norm sits inside the fundamental cube
  have hball : Metric.ball (0 : d → ℝ) (1 / 2)
      ⊆ {y : d → ℝ | ∀ i, y i ∈ Set.Ioc ((fun _ : d ↦ -(1 : ℝ) / 2) i)
        ((fun _ : d ↦ -(1 : ℝ) / 2) i + 1)} := by
    intro y hy i
    have hyi : |y i| < 1 / 2 := by
      have h1 := norm_le_pi_norm y i
      have hy' : ‖y‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
      simpa [Real.norm_eq_abs] using lt_of_le_of_lt h1 hy'
    rw [abs_lt] at hyi
    constructor <;> simp <;> linarith [hyi.1, hyi.2]
  refine top_le_iff.1 (le_trans ?_ (lintegral_mono' (Measure.restrict_mono hball le_rfl) le_rfl))
  rw [← setLIntegral_inv_mul_norm_pow_mul_log_inv_ball_eq_top (ι := d) (k := Fintype.card d)
    (c := M) (R := 1 / 2) le_rfl hM0 (by norm_num) (by norm_num)]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_ball (x := (0 : d → ℝ)) (ε := 1 / 2))] with y hy
  have hylt : ‖y‖ < 1 / 2 := by simpa [Metric.mem_ball, dist_zero_right] using hy
  exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hMle y hylt))

variable [LinearOrder (d → ℤ)]

/-- **Georgii Corollary (13.41).** Let `d ≤ 2` and let `J : ℤ^d → ℝ` be even, of finite range and
positive definite (the standing hypotheses under which `γ^{J,h}` is defined), and suppose

  `∑_{‖i‖ ≤ m} ‖i‖^d |J(i)| ≤ L log m`  for every `m ≥ 2`.

If `Ĵ` has a root on the torus then `𝒢(γ^{J,h}) = ∅` for every constant external field `h`. -/
theorem not_nonempty_G_homogeneousCoupling_of_root
    (hn1 : 1 ≤ Fintype.card d) (hn2 : Fintype.card d ≤ 2) (hJ : Summable fun i ↦ |J' i|)
    (hEven : ∀ i, J' (-i) = J' i) (hFin : {i : d → ℤ | J' i ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : (fourierHomogeneousCoupling J' q).re = 0)
    (hlog : ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ L * Real.log m)
    (h : ℝ) :
    ¬ (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
      (fun _ ↦ h) (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos)).Nonempty := by
  intro hG
  have hne := (nonempty_G_homogeneousCoupling_iff hJ hEven hFin hPD hpos).1 hG
  exact hne.2 (lintegral_inv_re_fourierHomogeneousCoupling_eq_top_of_root hn1 hn2 hJ hpos hq hlog)

/-- **Georgii Corollary (13.41)**, as the equality `𝒢(γ^{J,h}) = ∅`. -/
theorem G_homogeneousCoupling_eq_empty_of_root
    (hn1 : 1 ≤ Fintype.card d) (hn2 : Fintype.card d ≤ 2) (hJ : Summable fun i ↦ |J' i|)
    (hEven : ∀ i, J' (-i) = J' i) (hFin : {i : d → ℤ | J' i ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : (fourierHomogeneousCoupling J' q).re = 0)
    (hlog : ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ L * Real.log m)
    (h : ℝ) :
    MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
      (fun _ ↦ h) (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos) = ∅ :=
  Set.not_nonempty_iff_eq_empty.1
    (not_nonempty_G_homogeneousCoupling_of_root hn1 hn2 hJ hEven hFin hPD hpos hq hlog h)

/-- **Georgii's logarithmic hypothesis is automatic for a finite-range `J`**, with
`L = (∑_i ‖i‖^d |J(i)|) / log 2`. -/
theorem log_moment_of_finite_range (hFin : {i : d → ℤ | J' i ≠ 0}.Finite) :
    ∃ L : ℝ, ∀ m : ℕ, 2 ≤ m →
      ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ L * Real.log m := by
  classical
  refine ⟨(∑ i ∈ hFin.toFinset, |J' i| * ‖i‖ ^ Fintype.card d) / Real.log 2, fun m hm ↦ ?_⟩
  set A : ℝ := ∑ i ∈ hFin.toFinset, |J' i| * ‖i‖ ^ Fintype.card d with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ by positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : Real.log 2 ≤ Real.log (m : ℝ) := by
    refine Real.log_le_log (by norm_num) ?_
    exact_mod_cast hm
  have hzero : ∀ x ∈ latticeCube d m, x ∉ latticeCube d m ∩ hFin.toFinset →
      |J' x| * ‖x‖ ^ Fintype.card d = 0 := by
    intro x hx hxn
    have hJ0 : J' x = 0 := by
      by_contra hne
      exact hxn (Finset.mem_inter.2 ⟨hx, hFin.mem_toFinset.2 hne⟩)
    simp [hJ0]
  have heq : ∑ i ∈ latticeCube d m ∩ hFin.toFinset, |J' i| * ‖i‖ ^ Fintype.card d
      = ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d :=
    Finset.sum_subset Finset.inter_subset_left hzero
  have hsum : ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ A := by
    rw [← heq, hA]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun i _ _ ↦ by positivity
  calc ∑ i ∈ latticeCube d m, |J' i| * ‖i‖ ^ Fintype.card d ≤ A := hsum
    _ = A / Real.log 2 * Real.log 2 := by field_simp
    _ ≤ A / Real.log 2 * Real.log (m : ℝ) :=
        mul_le_mul_of_nonneg_left hlogm (by positivity)

/-- A finite-range coupling is absolutely summable. -/
lemma summable_abs_of_finite_range (hFin : {i : d → ℤ | J' i ≠ 0}.Finite) :
    Summable fun i ↦ |J' i| := by
  refine summable_of_finite_support (hFin.subset fun i hi ↦ ?_)
  simpa [Function.mem_support] using hi

/-- **Georgii Corollary (13.41) under the standing hypotheses of the tree.** For `d ≤ 2` and an
even, finite-range `J : ℤ^d → ℝ` with `Ĵ ≥ 0` and every `𝒥_Λ` positive definite, a root of `Ĵ` on
the torus makes `𝒢(γ^{J,h})` empty for every constant external field `h`. Georgii's logarithmic
condition is automatic for a finite-range `J` (`Potential.log_moment_of_finite_range`). -/
theorem G_homogeneousCoupling_eq_empty_of_root_of_finiteRange
    (hn1 : 1 ≤ Fintype.card d) (hn2 : Fintype.card d ≤ 2)
    (hEven : ∀ i, J' (-i) = J' i) (hFin : {i : d → ℤ | J' i ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) {q : UnitAddTorus d}
    (hq : fourierHomogeneousCoupling J' q = 0) (h : ℝ) :
    MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
      (fun _ ↦ h) (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos) = ∅ := by
  obtain ⟨L, hL⟩ := log_moment_of_finite_range (J' := J') hFin
  exact G_homogeneousCoupling_eq_empty_of_root hn1 hn2 (summable_abs_of_finite_range hFin)
    hEven hFin hPD hpos ((fourierHomogeneousCoupling_eq_zero_iff hEven q).1 hq) hL h

end Corollary

end Potential

end

end

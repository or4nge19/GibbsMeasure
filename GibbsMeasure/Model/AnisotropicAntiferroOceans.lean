/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AnisotropicHeisenbergOceans
public import GibbsMeasure.Model.IsingOceans

/-!
# Georgii 18.3.7: anisotropic Heisenberg antiferromagnets in an external field

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.7, first model.  The state space is the
unit sphere `E` of a finite-dimensional real inner product space `V` (Georgii: `ℝⁿ`, `n ≥ 2`),
the a priori measure is the normalised surface measure `sphereProb V`, and the `C`-potential is
**(18.34)**

`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} [σ_{i,1}σ_{j,1} + α ∑_{ℓ ≥ 2} σ_{i,ℓ}σ_{j,ℓ}] - h ∑_{i ∈ C} σ_{i,1}`,

the sign of the bond term of the ferromagnet (18.33) reversed and an external field `h` in the
direction of the anisotropy axis `u`.  As in `GibbsMeasure/Model/AnisotropicHeisenbergOceans.lean`
the bracket is `anisoBond α u x y = (1 - α) ⟪x, u⟫⟪y, u⟫ + α ⟪x, y⟫`.

## Georgii's hypothesis `|h| < 2` is not enough

Georgii states (18.34) for `0 ≤ α < 1` and `|h| < 2` and asserts that the two staggered polar
configurations are *the only* local ground states.  **That is false** as soon as
`h² > 4(1 - α²)`: for `n = 2`, `α = 9/10`, `h = 19/10` (both inside Georgii's ranges), the
configuration `σ_{(0,0)} = σ_{(1,1)} = (1/10)u + √(99)/10 w`,
`σ_{(1,0)} = σ_{(0,1)} = (1/10)u - √(99)/10 w` with `w ⊥ u` has all four bonds at inner product
`-49/50` and hence `Φ_C = -4.284 < -4`.  Expanding `Φ_C` to second order about the staggered
polar state gives the quadratic form `(2 + h)ε₁² + (2 - h)ε₂² - 4αε₁ε₂` in the two tilt angles,
which is positive definite exactly when `h² < 4(1 - α²)`.  The correct hypothesis, used
throughout below, is therefore

`h² < 4 (1 - α²)`,

which is Georgii's `|h| < 2` in the Ising-like case `α = 0` and is what his own comparison with
the Ising antiferromagnet 18.3.2 suggests.  `exists_lt_neg_four_anisoAntiCube` proves the failure:
for `4(1 - α²) < h²` the value `-4` is *not* a lower bound for `Φ_C`.

## Main results

* `anisoAntiBond`, `anisoAntiCube_eq_cubeBondSum` — in the plane every corner of `C` lies on
  exactly two edges, so (18.34) is the bond sum of
  `ψ(x, y) = anisoBond α u x y - h (⟪x, u⟫ + ⟪y, u⟫)/2` and Georgii's minimisation of `Φ_C`
  reduces to a minimisation over a *single* bond, exactly as he does for the plane rotor (18.35).
* `neg_one_le_anisoAntiBond` and `anisoAntiBond_eq_neg_one_iff` — **the bond minimum is `-1`,
  attained exactly at the antipodal polar pairs `(u, -u)` and `(-u, u)`**, under
  `h² < 4(1 - α²)`.  The proof is the identity
  `1 + PQ - αRS = (1 + α)K + (1 - α)L` with `K = (1 + PQ - RS)/2`, `L = (1 + PQ + RS)/2`,
  `KL = ((P + Q)/2)²`, where `P, Q` are the polar components and `R, S` the norms of the
  transverse components; the arithmetic-geometric mean inequality then compares the field term
  `h(P + Q)/2` with `2√(1 - α²)√(KL)` (`le_add_of_mul_eq_sq`, `eq_zero_of_add_eq_of_mul_eq_sq`).
* `localGroundEnergy_anisoAntiCube`, `anisoAntiCube_eq_neg_four_iff` — **`m_Φ = -4` and the local
  ground states are the two staggered polar configurations** `polarStagger u 0`, `polarStagger u 1`
  (`ζ_c = (-1)^{n + c_1 + ⋯ + c_d} u`), by the connectedness of the cube.
* `anisoAntiG` — Georgii's `G_1 = ∏_{i ∈ C} U_{(-1)^{i_1+i_2+1}}` and `G_2 = r_0 G_1`, the
  *staggered* polar caps; `isPStablePartition_anisoAntiG` is the stability (18.23)(a)(ii) and
  `isPhiSymmetric_anisoAntiG` the `Φ`-symmetry, both `r_0` and `r_1, r_2` exchanging `G_1`
  and `G_2` because they reverse the parity of the corners.
* `eventually_two_le_encard_extremePoints_anisoAnti` — **Georgii's conclusion**,
  `|ex 𝒢(βΦ)| ≥ 2` for large `β` (not `𝒢_Θ`: the partition is staggered, hence not
  `r`-symmetric), and `eventually_exists_anisoAnti_gibbsMeasure_pair` for the two measures with
  their invariance under the even shifts and the transformations exchanging them.

`GibbsMeasure/Model/IsingOceans.lean` is imported for `sum_latticeParity_two`, the computation of
the parity of `r^a` that identifies Georgii's shift group `Θ̃` (its intended home is
`GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`, next to `latticeParity`); 18.3.7 is
Georgii's sphere-valued version of the Ising antiferromagnet 18.3.2, which lives there.

Georgii's second model of 18.3.7, the plane rotor (18.35) with a *transverse* field, is not
formalised here; see the report accompanying this file.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii's "by continuity, `G_ε(Φ) ⊆ G_1 ∪ ⋯ ∪ G_N` for small `ε`"

Intended home: `GibbsMeasure/Specification/LocalGroundStates.lean`, next to
`localGroundStates` and `exists_pos_localGroundStates_subset` (the finite state space version in
`GibbsMeasure/Model/DiscreteSymmetryBreakingExamples.lean`).  It is here because that file is not
editable in the session in which this one was written, and because the three continuous examples
18.3.7, 18.3.8 and 18.3.9 all need it. -/

section Shrink

variable {d : ℕ} {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  [(cubeMeasure d ν).IsOpenPosMeasure]

/-- **Georgii's "by continuity, `G_ε(Φ) ⊆ G_1 ∪ ⋯ ∪ G_N` when `ε > 0` is small enough"**
(18.23)(a)(i) for a *continuous* cube interaction with compact sublevel sets: on the compact set
`{Φ_C ≤ m_Φ + ε₀} \ U` the continuous `Φ_C` attains a minimum, which exceeds `m_Φ` because every
exact local ground state lies in the open set `U`.

This is the counterpart of `exists_pos_localGroundStates_subset`, which reads off the same
conclusion from the finiteness of the range of `Φ_C` over a finite state space. -/
theorem exists_pos_localGroundStates_subset_of_isCompact (hφc : Continuous φ) {m : ℝ}
    (hm : ∀ ζ, m ≤ φ ζ) {ζ₀ : (Fin d → Fin 2) → E} (hζ₀ : φ ζ₀ = m) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hcpt : IsCompact {ζ | φ ζ ≤ m + ε₀}) {U : Set ((Fin d → Fin 2) → E)} (hU : IsOpen U)
    (hUsub : {ζ | φ ζ = m} ⊆ U) :
    ∃ ε > 0, localGroundStates φ ν ε ⊆ U := by
  have hmΦ : localGroundEnergy φ ν = m := localGroundEnergy_eq_of_isOpenPosMeasure hφc hm hζ₀
  rcases Set.eq_empty_or_nonempty ({ζ | φ ζ ≤ m + ε₀} \ U) with hKe | hKne
  · refine ⟨ε₀, hε₀, fun ζ hζ ↦ ?_⟩
    rw [mem_localGroundStates, hmΦ] at hζ
    by_contra hnot
    exact (Set.eq_empty_iff_forall_notMem.1 hKe ζ) ⟨hζ, hnot⟩
  · obtain ⟨ζ₁, hζ₁K, hζ₁min⟩ := (hcpt.diff hU).exists_isMinOn hKne hφc.continuousOn
    have hlt : m < φ ζ₁ := lt_of_le_of_ne (hm ζ₁) fun heq ↦ hζ₁K.2 (hUsub heq.symm)
    refine ⟨min ε₀ ((φ ζ₁ - m) / 2), lt_min hε₀ (by linarith), fun ζ hζ ↦ ?_⟩
    rw [mem_localGroundStates, hmΦ] at hζ
    by_contra hnot
    have hmem : ζ ∈ {ζ | φ ζ ≤ m + ε₀} \ U :=
      ⟨hζ.trans (by have := min_le_left ε₀ ((φ ζ₁ - m) / 2); linarith), hnot⟩
    have hmin : φ ζ₁ ≤ φ ζ := isMinOn_iff.1 hζ₁min ζ hmem
    have := min_le_right ε₀ ((φ ζ₁ - m) / 2)
    linarith

/-- **Georgii's "by continuity"** over a *compact* state space: `E^C` is then compact, so every
sublevel set of a continuous `Φ_C` is compact. -/
theorem exists_pos_localGroundStates_subset_of_compactSpace [CompactSpace E] (hφc : Continuous φ)
    {m : ℝ} (hm : ∀ ζ, m ≤ φ ζ) {ζ₀ : (Fin d → Fin 2) → E} (hζ₀ : φ ζ₀ = m)
    {U : Set ((Fin d → Fin 2) → E)} (hU : IsOpen U) (hUsub : {ζ | φ ζ = m} ⊆ U) :
    ∃ ε > 0, localGroundStates φ ν ε ⊆ U :=
  exists_pos_localGroundStates_subset_of_isCompact hφc hm hζ₀ one_pos
    (IsClosed.isCompact (isClosed_le hφc continuous_const)) hU hUsub

end Shrink

/-! ### The arithmetic behind Georgii's ground state computation -/

section Arithmetic

/-- If `t² ≤ (X + Y)²` and `X, Y ≥ 0` then `t ≤ X + Y`. -/
lemma le_add_of_sq_le_sq_add {X Y t : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : t ^ 2 ≤ (X + Y) ^ 2) :
    t ≤ X + Y := by
  have habs : |t| ≤ |X + Y| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h
  calc t ≤ |t| := le_abs_self t
    _ ≤ |X + Y| := habs
    _ = X + Y := abs_of_nonneg (by linarith)

/-- **The arithmetic-geometric mean step of Georgii's minimisation of (18.34)**: if
`K, L ≥ 0` have `KL = m²` and `h² ≤ 4(1 - α²)`, then `hm ≤ (1 + α)K + (1 - α)L`.  Applied with
`K = (1 + PQ - RS)/2`, `L = (1 + PQ + RS)/2` and `m = (P + Q)/2` this is exactly
`h(P + Q)/2 ≤ 1 + PQ - αRS`, the statement that the bond interaction of (18.34) is at least
`-1`. -/
lemma le_add_of_mul_eq_sq {α h K L m : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hh : h ^ 2 ≤ 4 * (1 - α ^ 2)) (hK : 0 ≤ K) (hL : 0 ≤ L) (hKL : K * L = m ^ 2) :
    h * m ≤ (1 + α) * K + (1 - α) * L := by
  have hX : 0 ≤ (1 + α) * K := by positivity
  have hY : 0 ≤ (1 - α) * L := mul_nonneg (by linarith) hL
  refine le_add_of_sq_le_sq_add hX hY ?_
  have hXY : ((1 + α) * K) * ((1 - α) * L) = (1 - α ^ 2) * m ^ 2 := by
    rw [show ((1 + α) * K) * ((1 - α) * L) = (1 - α ^ 2) * (K * L) by ring, hKL]
  nlinarith [sq_nonneg ((1 + α) * K - (1 - α) * L), sq_nonneg m]

/-- **The equality case of `le_add_of_mul_eq_sq`** under the strict hypothesis
`h² < 4(1 - α²)`: the bond interaction of (18.34) attains its minimum only where both
`K` and `L` vanish, that is, only at the antipodal polar pairs. -/
lemma eq_zero_of_add_eq_of_mul_eq_sq {α h K L m : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hh : h ^ 2 < 4 * (1 - α ^ 2)) (hK : 0 ≤ K) (hL : 0 ≤ L) (hKL : K * L = m ^ 2)
    (heq : (1 + α) * K + (1 - α) * L = h * m) : K = 0 ∧ L = 0 := by
  have hXY : ((1 + α) * K) * ((1 - α) * L) = (1 - α ^ 2) * m ^ 2 := by
    rw [show ((1 + α) * K) * ((1 - α) * L) = (1 - α ^ 2) * (K * L) by ring, hKL]
  have hm : m = 0 := by
    by_contra hm0
    have hpos : 0 < m ^ 2 := by positivity
    have hstrict : h ^ 2 * m ^ 2 < 4 * (1 - α ^ 2) * m ^ 2 :=
      (mul_lt_mul_of_pos_right hh hpos)
    have hsq : ((1 + α) * K + (1 - α) * L) ^ 2 = (h * m) ^ 2 := by rw [heq]
    nlinarith [sq_nonneg ((1 + α) * K - (1 - α) * L), hsq, hstrict, hXY]
  rw [hm, mul_zero] at heq
  have hX : 0 ≤ (1 + α) * K := by positivity
  have hY : 0 ≤ (1 - α) * L := mul_nonneg (by linarith) hL
  refine ⟨?_, ?_⟩
  · have hz : (1 + α) * K = 0 := by linarith
    rcases mul_eq_zero.1 hz with h1 | h1
    · linarith
    · exact h1
  · have hz : (1 - α) * L = 0 := by linarith
    rcases mul_eq_zero.1 hz with h1 | h1
    · linarith
    · exact h1

/-- **Georgii's minimisation of the bond interaction of (18.34)**, in polar coordinates: `P, Q`
are the components of the two spins along the anisotropy axis and `R, S ≥ 0` the norms of their
transverse components, so that `P² + R² = Q² + S² = 1`.  The identity
`1 + PQ - αRS = (1 + α)K + (1 - α)L` with `K = (1 + PQ - RS)/2 ≥ 0`, `L = (1 + PQ + RS)/2 ≥ 0`
and `KL = ((P + Q)/2)²` turns the bound into `le_add_of_mul_eq_sq`. -/
lemma neg_one_le_polarCore {α h P Q R S : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hh : h ^ 2 ≤ 4 * (1 - α ^ 2)) (hPR : P ^ 2 + R ^ 2 = 1) (hQS : Q ^ 2 + S ^ 2 = 1) :
    -1 ≤ P * Q - α * (R * S) - h * (P + Q) / 2 := by
  have hKL : ((1 + P * Q - R * S) / 2) * ((1 + P * Q + R * S) / 2) = ((P + Q) / 2) ^ 2 := by
    linear_combination (-(1 - Q ^ 2) / 4) * hPR + (-(R ^ 2) / 4) * hQS
  have hK : (0 : ℝ) ≤ (1 + P * Q - R * S) / 2 := by
    nlinarith [sq_nonneg (P + Q), sq_nonneg (R - S)]
  have hL : (0 : ℝ) ≤ (1 + P * Q + R * S) / 2 := by
    nlinarith [sq_nonneg (P + Q), sq_nonneg (R + S)]
  have hkey := le_add_of_mul_eq_sq hα0 hα1 hh hK hL hKL
  have hid : (1 + α) * ((1 + P * Q - R * S) / 2) + (1 - α) * ((1 + P * Q + R * S) / 2)
      = 1 + P * Q - α * (R * S) := by ring
  rw [hid] at hkey
  linarith

/-- **The equality case of `neg_one_le_polarCore`** under `h² < 4(1 - α²)`: the two spins are
antipodal and lie on the anisotropy axis. -/
lemma polarCore_eq_neg_one {α h P Q R S : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hh : h ^ 2 < 4 * (1 - α ^ 2)) (hPR : P ^ 2 + R ^ 2 = 1) (hQS : Q ^ 2 + S ^ 2 = 1)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (heq : P * Q - α * (R * S) - h * (P + Q) / 2 = -1) :
    R = 0 ∧ S = 0 ∧ P * Q = -1 := by
  have hKL : ((1 + P * Q - R * S) / 2) * ((1 + P * Q + R * S) / 2) = ((P + Q) / 2) ^ 2 := by
    linear_combination (-(1 - Q ^ 2) / 4) * hPR + (-(R ^ 2) / 4) * hQS
  have hK : (0 : ℝ) ≤ (1 + P * Q - R * S) / 2 := by
    nlinarith [sq_nonneg (P + Q), sq_nonneg (R - S)]
  have hL : (0 : ℝ) ≤ (1 + P * Q + R * S) / 2 := by
    nlinarith [sq_nonneg (P + Q), sq_nonneg (R + S)]
  have heq2 : (1 + α) * ((1 + P * Q - R * S) / 2) + (1 - α) * ((1 + P * Q + R * S) / 2)
      = h * ((P + Q) / 2) := by
    have hid : (1 + α) * ((1 + P * Q - R * S) / 2) + (1 - α) * ((1 + P * Q + R * S) / 2)
        = 1 + P * Q - α * (R * S) := by ring
    rw [hid]
    linarith
  obtain ⟨hK0, hL0⟩ := eq_zero_of_add_eq_of_mul_eq_sq hα0 hα1 hh hK hL hKL heq2
  have hPQ : P * Q = -1 := by linarith
  have hRS : R * S = 0 := by linarith
  have hRz : R = 0 := by nlinarith [hPR, hQS, hRS, hPQ, hR, hS, sq_nonneg (R - S)]
  have hSz : S = 0 := by nlinarith [hPR, hQS, hRS, hPQ, hR, hS, sq_nonneg (R - S)]
  exact ⟨hRz, hSz, hPQ⟩

end Arithmetic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The polar decomposition of a spin -/

section Polar

variable {u x y : V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The transverse component `x - ⟪x, u⟫ u` of a unit spin is orthogonal to the anisotropy
axis, and `⟪x, u⟫² + ‖x - ⟪x, u⟫ u‖² = 1`. -/
lemma inner_sq_add_norm_sub_proj_sq (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
    ⟪x, u⟫ ^ 2 + ‖x - ⟪x, u⟫ • u‖ ^ 2 = 1 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hx, hu]
  simp only [Real.norm_eq_abs, mul_one, one_pow, sq_abs]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The polar lower bound for the inner product**: the transverse components contribute at
least `-‖x'‖‖y'‖`. -/
lemma inner_polar_le_inner (hu : ‖u‖ = 1) :
    ⟪x, u⟫ * ⟪y, u⟫ - ‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖ ≤ ⟪x, y⟫ := by
  have hexp : ⟪x - ⟪x, u⟫ • u, y - ⟪y, u⟫ • u⟫ = ⟪x, y⟫ - ⟪x, u⟫ * ⟪y, u⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    rw [real_inner_comm u y]
    ring
  have hcs : -(‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖) ≤ ⟪x - ⟪x, u⟫ • u, y - ⟪y, u⟫ • u⟫ :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  rw [hexp] at hcs
  linarith

end Polar

/-! ### Georgii (18.34): the bond interaction with the external field -/

variable (α h : ℝ) (u : V) in
/-- **The bond interaction of Georgii (18.34)**: the anisotropic antiferromagnetic bond together
with half of the external field at each of its two ends.  In the plane every corner of `C` lies
on exactly two edges, so summing this over the four edges of `C` gives (18.34)
(`anisoAntiCube_eq_cubeBondSum`). -/
def anisoAntiBond (x y : V) : ℝ := anisoBond α u x y - h * (⟪x, u⟫ + ⟪y, u⟫) / 2

variable {α h : ℝ} {u x y : V}

lemma anisoAntiBond_comm : anisoAntiBond α h u x y = anisoAntiBond α h u y x := by
  rw [anisoAntiBond, anisoAntiBond, anisoBond_comm]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_anisoAntiBond (α h : ℝ) (u : V) :
    Continuous (Function.uncurry (anisoAntiBond α h u)) := by
  unfold Function.uncurry anisoAntiBond anisoBond
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **`ψ(u, -u) = -1`**: an antipodal polar bond is at the minimum, the external field cancelling
between the two ends. -/
lemma anisoAntiBond_polar (hu : ‖u‖ = 1) : anisoAntiBond α h u u (-u) = -1 := by
  rw [anisoAntiBond, anisoBond]
  simp only [inner_neg_left, inner_neg_right, real_inner_self_eq_norm_sq, hu]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The polar data of a unit spin: the component along `u` and the norm of the transverse
component. -/
lemma polar_data (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) :
    ⟪x, u⟫ ^ 2 + ‖x - ⟪x, u⟫ • u‖ ^ 2 = 1 ∧ 0 ≤ ‖x - ⟪x, u⟫ • u‖ :=
  ⟨inner_sq_add_norm_sub_proj_sq hu hx, norm_nonneg _⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **Georgii's minimum of the bond interaction of (18.34) is `-1`**, provided
`h² ≤ 4(1 - α²)`. -/
lemma neg_one_le_anisoAntiBond (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hh : h ^ 2 ≤ 4 * (1 - α ^ 2))
    (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : -1 ≤ anisoAntiBond α h u x y := by
  obtain ⟨hPR, hR⟩ := polar_data hu hx
  obtain ⟨hQS, hS⟩ := polar_data hu hy
  have hcore := neg_one_le_polarCore hα0 hα1 hh hPR hQS
  have hinner := inner_polar_le_inner (x := x) (y := y) hu
  have hmul : 0 ≤ α * (⟪x, y⟫ - (⟪x, u⟫ * ⟪y, u⟫ - ‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖)) :=
    mul_nonneg hα0 (by linarith)
  rw [anisoAntiBond, anisoBond]
  nlinarith [hcore, hmul]

/-- **Georgii's "it is easily seen that … are the only local ground states"** at the level of a
single bond: under the strict hypothesis `h² < 4(1 - α²)` the bond interaction of (18.34) equals
its minimum `-1` exactly at the two antipodal polar pairs. -/
lemma anisoAntiBond_eq_neg_one_iff (hα0 : 0 ≤ α) (hα1 : α < 1) (hh : h ^ 2 < 4 * (1 - α ^ 2))
    (hu : ‖u‖ = 1) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    anisoAntiBond α h u x y = -1 ↔ (x = u ∧ y = -u) ∨ (x = -u ∧ y = u) := by
  constructor
  · intro heq
    obtain ⟨hPR, hR⟩ := polar_data hu hx
    obtain ⟨hQS, hS⟩ := polar_data hu hy
    have hcore := neg_one_le_polarCore hα0 hα1.le hh.le hPR hQS
    have hinner := inner_polar_le_inner (x := x) (y := y) hu
    have hmul : 0 ≤ α * (⟪x, y⟫ - (⟪x, u⟫ * ⟪y, u⟫ - ‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖)) :=
      mul_nonneg hα0 (by linarith)
    have hle : ⟪x, u⟫ * ⟪y, u⟫ - α * (‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖)
        - h * (⟪x, u⟫ + ⟪y, u⟫) / 2 ≤ anisoAntiBond α h u x y := by
      rw [anisoAntiBond, anisoBond]
      nlinarith [hmul]
    have hcoreq : ⟪x, u⟫ * ⟪y, u⟫ - α * (‖x - ⟪x, u⟫ • u‖ * ‖y - ⟪y, u⟫ • u‖)
        - h * (⟪x, u⟫ + ⟪y, u⟫) / 2 = -1 := by
      rw [heq] at hle
      linarith
    obtain ⟨hRz, hSz, hPQ⟩ := polarCore_eq_neg_one hα0 hα1 hh hPR hQS hR hS hcoreq
    have hxP : x = ⟪x, u⟫ • u := sub_eq_zero.1 (norm_eq_zero.1 hRz)
    have hyQ : y = ⟪y, u⟫ • u := sub_eq_zero.1 (norm_eq_zero.1 hSz)
    have hP1 : ⟪x, u⟫ ^ 2 = 1 := by
      have : ‖x - ⟪x, u⟫ • u‖ ^ 2 = 0 := by rw [hRz]; ring
      linarith
    have hfac : (⟪x, u⟫ - 1) * (⟪x, u⟫ + 1) = 0 := by nlinarith [hP1]
    rcases mul_eq_zero.1 hfac with hp | hp
    · have hp1 : ⟪x, u⟫ = 1 := by linarith
      have hq1 : ⟪y, u⟫ = -1 := by rw [hp1] at hPQ; linarith
      refine Or.inl ⟨by rw [hxP, hp1, one_smul], ?_⟩
      rw [hyQ, hq1]
      module
    · have hp1 : ⟪x, u⟫ = -1 := by linarith
      have hq1 : ⟪y, u⟫ = 1 := by rw [hp1] at hPQ; linarith
      refine Or.inr ⟨?_, by rw [hyQ, hq1, one_smul]⟩
      rw [hxP, hp1]
      module
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact anisoAntiBond_polar hu
    · rw [anisoAntiBond_comm]
      exact anisoAntiBond_polar hu


/-! ### Georgii (18.34): the cube interaction -/

/-- The corner sum changes by `1` along every edge of the cube: adjacent corners have opposite
parity.  (Intended home: `GibbsMeasure/Model/DiscreteSymmetryBreakingExamples.lean`, next to
`cubeGraph_adj_iff_add_single`.) -/
lemma sum_eq_add_one_of_adj {d : ℕ} {c c' : Fin d → Fin 2} (h : (cubeGraph d).Adj c c') :
    ∑ k, c' k = ∑ k, c k + 1 := by
  obtain ⟨k, hk⟩ := cubeGraph_adj_iff_add_single.1 h
  have hc' : c' = c + Pi.single k 1 := by
    have h1 : c' + c + c = Pi.single k 1 + c := by rw [hk]
    rwa [add_assoc, corner_add_self, add_zero, add_comm (Pi.single k 1) c] at h1
  rw [hc', sum_add_single]

/-- The corner sum changes by `1` under a reflection of the cube. -/
lemma sum_cubeSiteRefl {d : ℕ} (k : Fin d) (c : Fin d → Fin 2) :
    ∑ l, cubeSiteRefl k c l = ∑ l, c l + 1 := by
  rw [cubeSiteRefl_eq_add_single, sum_add_single]

variable (α h : ℝ) (u : sphere (0 : V) 1) (d : ℕ) in
/-- **Georgii (18.34)**: the `C`-potential of the anisotropic Heisenberg antiferromagnet with
anisotropy `α` in the direction of the unit vector `u` and an external field `h` in the same
direction.  Only the sign of the bond term distinguishes it from the ferromagnet (18.33). -/
abbrev anisoAntiCube : ((Fin d → Fin 2) → sphere (0 : V) 1) → ℝ := fun ζ ↦
  cubeBondSum d (fun x y : sphere (0 : V) 1 ↦ anisoBond α (u : V) (x : V) (y : V)) ζ
    - h * cubeSiteSum d (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) ζ

variable {α h : ℝ} {u : sphere (0 : V) 1} {d : ℕ}

lemma continuous_anisoAntiCube : Continuous (anisoAntiCube α h u d) := by
  refine Continuous.sub (continuous_cubeBondSum ?_) (continuous_const.mul ?_)
  · have hc : Continuous fun p : sphere (0 : V) 1 × sphere (0 : V) 1 ↦ ((p.1 : V), (p.2 : V)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (continuous_anisoBond α (u : V)).comp hc
  · unfold cubeSiteSum
    exact continuous_finsetSum _ fun c _ ↦
      (continuous_subtype_val.comp (continuous_apply c)).inner continuous_const

lemma measurable_anisoAntiCube : Measurable (anisoAntiCube α h u d) :=
  continuous_anisoAntiCube.measurable

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Condition (iii) of Georgii (17.18)** for (18.34). -/
lemma anisoAntiCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    anisoAntiCube α h u d (cubeRefl (sphere (0 : V) 1) k ζ) = anisoAntiCube α h u d ζ := by
  simp only [anisoAntiCube, cubeBondSum_cubeRefl, cubeSiteSum_cubeRefl]

/-- **In the plane, (18.34) is the bond sum of `anisoAntiBond`**: every corner of `C` lies on
exactly two of the four edges, so the site sum `h ∑_{i ∈ C} ⟪σ_i, u⟫` can be split over the
edges.  This is what reduces Georgii's minimisation of `Φ_C` to a minimisation over one bond. -/
lemma anisoAntiCube_eq_cubeBondSum (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    anisoAntiCube α h u 2 ζ
      = cubeBondSum 2
          (fun x y : sphere (0 : V) 1 ↦ anisoAntiBond α h (u : V) (x : V) (y : V)) ζ := by
  rw [anisoAntiCube,
    cubeBondSum_two (fun x y : sphere (0 : V) 1 ↦ anisoBond_comm α (u : V) (x : V) (y : V)) ζ,
    cubeBondSum_two (fun _ _ : sphere (0 : V) 1 ↦ anisoAntiBond_comm) ζ, cubeSiteSum_def,
    sum_univ_cubeCorners]
  simp only [anisoAntiBond]
  ring

section Bounds

variable (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hh : h ^ 2 ≤ 4 * (1 - α ^ 2))

include hα0 hα1 hh

/-- **Georgii's `Φ_C ≥ -4`** for (18.34), under `h² ≤ 4(1 - α²)`. -/
lemma neg_four_le_anisoAntiCube (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    -4 ≤ anisoAntiCube α h u 2 ζ := by
  rw [anisoAntiCube_eq_cubeBondSum]
  have hb := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ anisoAntiBond α h (u : V) (x : V) (y : V)) (m := -1)
    (ζ := ζ) fun c c' ↦ neg_one_le_anisoAntiBond hα0 hα1 hh (norm_sphere_eq_one u)
      (norm_sphere_eq_one _) (norm_sphere_eq_one _)
  norm_num at hb
  linarith

end Bounds

/-- **`|Φ_C| ≤ 4 + 4|h|`** for (18.34), the first alternative of condition (iv) of (17.18). -/
lemma abs_anisoAntiCube_le (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) : |anisoAntiCube α h u 2 ζ| ≤ 4 + 4 * |h| := by
  have hb1 := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ anisoBond α (u : V) (x : V) (y : V)) (m := -1) (ζ := ζ)
    fun c c' ↦ by
      have := neg_anisoBond_le_one (α := α) (u := (u : V)) (x := (ζ c : V)) (y := (ζ c' : V))
        hα0 hα1 (norm_sphere_eq_one u) (norm_sphere_eq_one _) (norm_sphere_eq_one _)
      linarith
  have hb2 := cubeBondSum_le (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ anisoBond α (u : V) (x : V) (y : V)) (M := 1) (ζ := ζ)
    fun c c' ↦ anisoBond_le_one hα0 hα1 (norm_sphere_eq_one u) (norm_sphere_eq_one _)
      (norm_sphere_eq_one _)
  have hs1 := cubeSiteSum_ge (d := 2)
    (v := fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) (m := -1) (ζ := ζ) fun c ↦ by
      have := abs_real_inner_le_one (norm_sphere_eq_one (ζ c)) (norm_sphere_eq_one u)
      cases abs_le.1 this; linarith
  have hs2 := cubeSiteSum_le (d := 2)
    (v := fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) (M := 1) (ζ := ζ) fun c ↦ by
      have := abs_real_inner_le_one (norm_sphere_eq_one (ζ c)) (norm_sphere_eq_one u)
      cases abs_le.1 this; linarith
  norm_num at hb1 hb2 hs1 hs2
  have hb : |cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦
      anisoBond α (u : V) (x : V) (y : V)) ζ| ≤ 4 := abs_le.2 ⟨hb1, hb2⟩
  have hs : |cubeSiteSum 2 (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) ζ| ≤ 4 :=
    abs_le.2 ⟨hs1, hs2⟩
  have habs : |anisoAntiCube α h u 2 ζ|
      ≤ |cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ anisoBond α (u : V) (x : V) (y : V)) ζ|
        + |h * cubeSiteSum 2 (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) ζ| := by
    simpa only [anisoAntiCube, sub_eq_add_neg, abs_neg] using
      abs_add_le (cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦
        anisoBond α (u : V) (x : V) (y : V)) ζ)
        (-(h * cubeSiteSum 2 (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) ζ))
  refine habs.trans ?_
  rw [abs_mul]
  have : |h| * |cubeSiteSum 2 (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫) ζ| ≤ |h| * 4 := by
    gcongr
  linarith

/-! ### The staggered polar configurations -/

/-- In `Fin 2`, `(x + 1) + (y + 1) = x + y`: two parity flips cancel. -/
lemma fin_two_add_one_add_add_one (x y : Fin 2) : x + 1 + (y + 1) = x + y := by
  revert x y; decide

/-- In `Fin 2`, `x + (y + 1) = (x + 1) + y`. -/
lemma fin_two_add_add_one (x y : Fin 2) : x + (y + 1) = x + 1 + y := by
  revert x y; decide

/-- In `Fin 2`, `x + 1 + 1 = x`. -/
lemma fin_two_add_one_add_one (x : Fin 2) : x + 1 + 1 = x := by
  revert x; decide


variable (u) in
/-- The two polar spins `±u` of Georgii 18.3.7, indexed by `Fin 2`. -/
def polarSpin (n : Fin 2) : sphere (0 : V) 1 := if n = 0 then u else -u

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma polarSpin_zero : polarSpin u 0 = u := rfl

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] lemma polarSpin_one : polarSpin u 1 = -u := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma coe_polarSpin (n : Fin 2) : ((polarSpin u n : sphere (0 : V) 1) : V)
    = anisoSign n • (u : V) := by
  fin_cases n <;> simp [polarSpin, anisoSign]

lemma inner_coe_polarSpin (n : Fin 2) :
    ⟪((polarSpin u n : sphere (0 : V) 1) : V), (u : V)⟫ = anisoSign n := by
  rw [coe_polarSpin, real_inner_smul_left, real_inner_self_eq_norm_sq, norm_sphere_eq_one u]
  ring

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma coe_polarSpin_add_one (n : Fin 2) : ((polarSpin u (n + 1) : sphere (0 : V) 1) : V)
    = -((polarSpin u n : sphere (0 : V) 1) : V) := by
  fin_cases n <;> simp [polarSpin]

/-- `u ≠ -u`: the two poles are distinct. -/
lemma coe_ne_neg_coe : (u : V) ≠ -(u : V) := by
  intro hcon
  have h1 : ⟪(u : V), (u : V)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_sphere_eq_one u]; norm_num
  have h2 : ⟪(u : V), (u : V)⟫ = -1 := by
    nth_rewrite 1 [hcon]
    rw [inner_neg_left, h1]
  linarith

variable (u) in
/-- **Georgii's staggered polar configurations** of the unit cube:
`ζ_c = (-1)^{n + c_1 + ⋯ + c_d} u`, the two local ground states of (18.34). -/
def polarStagger (n : Fin 2) : (Fin d → Fin 2) → sphere (0 : V) 1 :=
  fun c ↦ polarSpin u (n + ∑ k, c k)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma polarStagger_apply (n : Fin 2) (c : Fin d → Fin 2) :
    polarStagger u n c = polarSpin u (n + ∑ k, c k) := rfl

/-- Along an edge of the cube a staggered polar configuration takes the two opposite values. -/
lemma anisoAntiBond_polarStagger_adj {n : Fin 2} {c c' : Fin d → Fin 2}
    (hcc' : (cubeGraph d).Adj c c') :
    anisoAntiBond α h (u : V) ((polarStagger u n c : sphere (0 : V) 1) : V)
      ((polarStagger u n c' : sphere (0 : V) 1) : V) = -1 := by
  have hs : n + ∑ k, c' k = (n + ∑ k, c k) + 1 := by
    rw [sum_eq_add_one_of_adj hcc', ← add_assoc]
  rw [polarStagger_apply, polarStagger_apply, hs, coe_polarSpin_add_one]
  rcases fin_two_eq_zero_or_one (n + ∑ k, c k) with hm | hm <;> rw [hm]
  · simpa using anisoAntiBond_polar (α := α) (h := h) (u := (u : V)) (norm_sphere_eq_one u)
  · simp only [polarSpin_one]
    rw [anisoAntiBond_comm]
    have hcoe : ((-u : sphere (0 : V) 1) : V) = -(u : V) := by simp
    rw [hcoe, neg_neg]
    exact anisoAntiBond_polar (α := α) (h := h) (u := (u : V)) (norm_sphere_eq_one u)

section GroundStates

variable (hα0 : 0 ≤ α) (hα1 : α < 1) (hh : h ^ 2 < 4 * (1 - α ^ 2))

include hα0 hα1 hh

/-- **Georgii's local ground states of (18.34)**: the staggered polar configuration has
`Φ_C = -4`. -/
lemma anisoAntiCube_polarStagger (n : Fin 2) :
    anisoAntiCube α h u 2 (polarStagger u n) = -4 := by
  rw [anisoAntiCube_eq_cubeBondSum]
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (-1 : ℝ))) = -4 := by norm_num
  rw [← hval]
  refine (cubeBondSum_eq_iff_forall_adj (fun a b ↦
    neg_one_le_anisoAntiBond hα0 hα1.le hh.le (norm_sphere_eq_one u) (norm_sphere_eq_one a)
      (norm_sphere_eq_one b)) _).2 fun c c' hcc' ↦ anisoAntiBond_polarStagger_adj hcc'

/-- **Georgii's "it is easily seen that the two staggered polar squares are the only local ground
states of `Φ`"** — under the corrected hypothesis `h² < 4(1 - α²)`.  The bond minimisation
`anisoAntiBond_eq_neg_one_iff` puts every spin at a pole and makes adjacent spins opposite, and
the connectedness of the cube (`cubeGraph_forall_eq_of_adj`) turns that into the staggered
pattern. -/
theorem anisoAntiCube_eq_neg_four_iff (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    anisoAntiCube α h u 2 ζ = -4 ↔ ∃ n : Fin 2, ζ = polarStagger u n := by
  classical
  constructor
  · intro h4
    have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (-1 : ℝ))) = -4 := by norm_num
    rw [anisoAntiCube_eq_cubeBondSum, ← hval] at h4
    have hall := (cubeBondSum_eq_iff_forall_adj (fun a b ↦
      neg_one_le_anisoAntiBond hα0 hα1.le hh.le (norm_sphere_eq_one u) (norm_sphere_eq_one a)
        (norm_sphere_eq_one b)) ζ).1 h4
    have hpair : ∀ c c', (cubeGraph 2).Adj c c' →
        ((ζ c : V) = (u : V) ∧ (ζ c' : V) = -(u : V)) ∨
          ((ζ c : V) = -(u : V) ∧ (ζ c' : V) = (u : V)) := fun c c' hcc' ↦
      (anisoAntiBond_eq_neg_one_iff hα0 hα1 hh (norm_sphere_eq_one u) (norm_sphere_eq_one _)
        (norm_sphere_eq_one _)).1 (hall c c' hcc')
    have hpsinj : ∀ a b : Fin 2, polarSpin u a = polarSpin u b → a = b := by
      intro a b hab
      rcases fin_two_eq_zero_or_one a with rfl | rfl <;>
        rcases fin_two_eq_zero_or_one b with rfl | rfl
      · rfl
      · exact absurd (congrArg Subtype.val hab) (by simpa using coe_ne_neg_coe (u := u))
      · exact absurd (congrArg Subtype.val hab).symm (by simpa using coe_ne_neg_coe (u := u))
      · rfl
    have hex : ∀ c, ∃ m : Fin 2, ζ c = polarSpin u m := by
      intro c
      rcases hpair c (cubeSiteRefl 0 c) (cubeGraph_adj_cubeSiteRefl_self 0 c) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨0, Subtype.ext (by rw [h1]; rfl)⟩
      · exact ⟨1, Subtype.ext (by rw [h1]; simp)⟩
    choose f hζf using hex
    have hflip : ∀ c c', (cubeGraph 2).Adj c c' → f c' = f c + 1 := by
      intro c c' hcc'
      have hval0 : ∀ b, (ζ b : V) = (u : V) → f b = 0 := fun b hb ↦
        hpsinj _ _ (by rw [← hζf b]; exact Subtype.ext (by rw [hb]; rfl))
      have hval1 : ∀ b, (ζ b : V) = -(u : V) → f b = 1 := fun b hb ↦
        hpsinj _ _ (by rw [← hζf b]; exact Subtype.ext (by rw [hb]; simp))
      rcases hpair c c' hcc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hval0 c h1, hval1 c' h2]
        rfl
      · rw [hval1 c h1, hval0 c' h2]
        rfl
    have hconst : ∀ c c', (cubeGraph 2).Adj c c' →
        (fun c ↦ f c + ∑ k, c k) c = (fun c ↦ f c + ∑ k, c k) c' := by
      intro c c' hcc'
      change f c + ∑ k, c k = f c' + ∑ k, c' k
      rw [hflip c c' hcc', sum_eq_add_one_of_adj hcc', fin_two_add_one_add_add_one]
    refine ⟨f 0, funext fun c ↦ ?_⟩
    have hc := cubeGraph_forall_eq_of_adj hconst c
    have h0 : ∑ k, (0 : Fin 2 → Fin 2) k = 0 := by simp
    change ζ c = polarStagger u (f 0) c
    rw [hζf c, polarStagger_apply]
    congr 1
    have hc' : f c + ∑ k, c k = f 0 := by
      have hcc : (fun c ↦ f c + ∑ k, c k) c = (fun c ↦ f c + ∑ k, c k) 0 := hc
      simpa [h0] using hcc
    rw [← hc', add_assoc, fin_two_add_self, add_zero]
  · rintro ⟨n, rfl⟩
    exact anisoAntiCube_polarStagger hα0 hα1 hh n

variable [Nontrivial V]

/-- **Georgii's `m_Φ = -4`** for (18.34). -/
theorem localGroundEnergy_anisoAntiCube :
    localGroundEnergy (anisoAntiCube α h u 2) (sphereProb V) = -4 :=
  localGroundEnergy_eq_of_isOpenPosMeasure continuous_anisoAntiCube
    (neg_four_le_anisoAntiCube hα0 hα1.le hh.le) (ζ₀ := polarStagger u 0)
    (anisoAntiCube_polarStagger hα0 hα1 hh 0)

end GroundStates

/-! ### Georgii's staggered polar caps `G_1 = ∏_{i ∈ C} U_{(-1)^{i_1+i_2+1}}` and `G_2 = r_0 G_1` -/

/-- **Georgii's `G_1` and `G_2` of 18.3.7**: `G_n = ∏_{i ∈ C} U_{(-1)^{n + i_1 + i_2}}`, the cube
configurations whose spins lie in the polar cap `U_±` of 18.3.6 with the *staggered* sign.  The
strict inequality makes these sets open, which is what Georgii's "by continuity" needs. -/
def anisoAntiG (δ : ℝ) (u : sphere (0 : V) 1) (n : Fin 2) :
    Set ((Fin 2 → Fin 2) → sphere (0 : V) 1) :=
  {ζ | ∀ c, 1 - δ < anisoSign (n + ∑ k, c k) * ⟪(ζ c : V), (u : V)⟫}

variable {δ : ℝ}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma mem_anisoAntiG {n : Fin 2} {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1} :
    ζ ∈ anisoAntiG δ u n ↔ ∀ c, 1 - δ < anisoSign (n + ∑ k, c k) * ⟪(ζ c : V), (u : V)⟫ :=
  Iff.rfl

lemma isOpen_anisoAntiG (n : Fin 2) : IsOpen (anisoAntiG δ u n) := by
  have h : anisoAntiG δ u n = ⋂ c, {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 |
      1 - δ < anisoSign (n + ∑ k, c k) * ⟪(ζ c : V), (u : V)⟫} := by
    ext ζ
    simp [anisoAntiG, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun c ↦
    isOpen_lt continuous_const (continuous_const.mul (continuous_inner_apply c))

lemma measurableSet_anisoAntiG (n : Fin 2) : MeasurableSet (anisoAntiG δ u n) :=
  (isOpen_anisoAntiG n).measurableSet

/-- The staggered polar ground state lies in its own cap. -/
lemma polarStagger_mem_anisoAntiG (hδ : 0 < δ) (n : Fin 2) :
    polarStagger u n ∈ anisoAntiG δ u n := by
  intro c
  rw [polarStagger_apply, inner_coe_polarSpin]
  have hsq : anisoSign (n + ∑ k, c k) * anisoSign (n + ∑ k, c k) = 1 := by
    rcases fin_two_eq_zero_or_one (n + ∑ k, c k) with hm | hm <;> rw [hm] <;>
      norm_num [anisoSign]
  rw [hsq]
  linarith

/-- **Georgii's stability of `{G_1, G_2}`**: the two staggered patterns disagree at *every*
corner, and the polar caps are disjoint for `δ ≤ 1`, so already a single corner of a face
separates `G_1` from `G_2`. -/
theorem pairwise_disjoint_faceRestrict_anisoAntiG (hδ1 : δ ≤ 1) (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict (sphere (0 : V) 1) k a '' anisoAntiG δ u m)
      (faceRestrict (sphere (0 : V) 1) k a '' anisoAntiG δ u n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  rintro g ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hfe⟩
  have hcorner : ζ (fun _ ↦ a) = ξ (fun _ ↦ a) :=
    (congrFun hfe (⟨fun _ ↦ a, rfl⟩ : {c : Fin 2 → Fin 2 // c k = a})).symm
  have h1 := hζ (fun _ ↦ a)
  have h2 := hξ (fun _ ↦ a)
  rw [← hcorner] at h2
  have hne : m + ∑ l, (fun _ : Fin 2 ↦ a) l ≠ n + ∑ l, (fun _ : Fin 2 ↦ a) l := by
    simpa using hmn
  rw [anisoSign_eq_neg_of_ne hne] at h1
  nlinarith [h1, h2, hδ1]

/-! ### The symmetries `r_1, r_2` and `r_0` exchange `G_1` and `G_2` -/

lemma fin_two_add_one_eq_of_ne {m n : Fin 2} (h : m ≠ n) : m + 1 = n := by
  revert h; fin_cases m <;> fin_cases n <;> decide

lemma preimage_cubeRefl_anisoAntiG (k : Fin 2) (m : Fin 2) :
    cubeRefl (sphere (0 : V) 1) k ⁻¹' anisoAntiG δ u m = anisoAntiG δ u (m + 1) := by
  ext ζ
  simp only [Set.mem_preimage, mem_anisoAntiG, cubeRefl_apply]
  constructor
  · intro hζ c
    have hc := hζ (cubeSiteRefl k c)
    rw [cubeSiteRefl_cubeSiteRefl, sum_cubeSiteRefl] at hc
    rwa [fin_two_add_add_one] at hc
  · intro hζ c
    have hc := hζ (cubeSiteRefl k c)
    rw [sum_cubeSiteRefl] at hc
    rwa [fin_two_add_one_add_add_one] at hc

/-- **A spatial cube transformation which reverses the parity of the corners exchanges the two
staggered caps.**  `ρ` is the corner map of `τ`; the hypothesis `hpar` is that it changes the
parity of a corner, which holds for each reflection `r_k` and for the rotation `r_0`. -/
lemma preimage_onCube_anisoAntiG (τ : CubeTransformation (sphere (0 : V) 1) 2)
    (ρ : (Fin 2 → Fin 2) → (Fin 2 → Fin 2)) (hsurj : Function.Surjective ρ)
    (hτζ : ∀ (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) c, τ.onCube.toFun ζ c = ζ (ρ c))
    (hpar : ∀ c, ∑ l, ρ c l = ∑ l, c l + 1) (n : Fin 2) :
    τ.onCube.toFun ⁻¹' anisoAntiG δ u n = anisoAntiG δ u (n + 1) := by
  ext ζ
  simp only [Set.mem_preimage, mem_anisoAntiG, hτζ]
  constructor
  · intro hζ c'
    obtain ⟨c, rfl⟩ := hsurj c'
    rw [hpar c, fin_two_add_one_add_add_one]
    exact hζ c
  · intro hζ c
    have hc := hζ (ρ c)
    rwa [hpar c, fin_two_add_one_add_add_one] at hc

lemma image_onCube_anisoAntiG (τ : CubeTransformation (sphere (0 : V) 1) 2)
    (ρ : (Fin 2 → Fin 2) → (Fin 2 → Fin 2)) (hsurj : Function.Surjective ρ)
    (hτζ : ∀ (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) c, τ.onCube.toFun ζ c = ζ (ρ c))
    (hpar : ∀ c, ∑ l, ρ c l = ∑ l, c l + 1) {m n : Fin 2} (hmn : m ≠ n) :
    τ.onCube.toFun '' anisoAntiG δ u m = anisoAntiG δ u n := by
  have hm : m = n + 1 := by
    rw [← fin_two_add_one_eq_of_ne hmn]
    revert hmn; fin_cases m <;> fin_cases n <;> decide
  rw [hm, ← preimage_onCube_anisoAntiG τ ρ hsurj hτζ hpar n,
    Set.image_preimage_eq _ (Function.RightInverse.surjective τ.onCube.toFun_inv_toFun)]

/-- The corner map of the reflection `r_k` is `cubeSiteRefl k`. -/
lemma onCube_refl_apply (k : Fin 2) (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1)
    (c : Fin 2 → Fin 2) :
    (CubeTransformation.refl (E := sphere (0 : V) 1) k).onCube.toFun ζ c
      = ζ (cubeSiteRefl k c) := by
  rw [CubeTransformation.refl_onCube_toFun, cubeRefl_apply]

lemma image_onCube_refl_anisoAntiG (k : Fin 2) {m n : Fin 2} (hmn : m ≠ n) :
    (CubeTransformation.refl (E := sphere (0 : V) 1) k).onCube.toFun '' anisoAntiG δ u m
      = anisoAntiG δ u n :=
  image_onCube_anisoAntiG _ (cubeSiteRefl k) (cubeSiteRefl k).surjective (onCube_refl_apply k)
    (sum_cubeSiteRefl k) hmn

/-- The corner map of Georgii's rotation `r_0` (18.20) of the unit square. -/
def sqRotCorner (c : Fin 2 → Fin 2) : Fin 2 → Fin 2 :=
  Function.update (Function.update c 0 (c 1)) 1 (c 0 + 1)

lemma sqRotCorner_zero (c : Fin 2 → Fin 2) : sqRotCorner c 0 = c 1 := by
  simp [sqRotCorner]

lemma sqRotCorner_one (c : Fin 2 → Fin 2) : sqRotCorner c 1 = c 0 + 1 := by
  simp [sqRotCorner]

lemma sqRotCorner_surjective : Function.Surjective sqRotCorner := by
  intro c'
  refine ⟨![c' 1 + 1, c' 0], funext fun l ↦ ?_⟩
  rcases fin_two_eq_zero_or_one l with rfl | rfl
  · rw [sqRotCorner_zero]; rfl
  · rw [sqRotCorner_one]
    change c' 1 + 1 + 1 = c' 1
    exact fin_two_add_one_add_one _

/-- Georgii's rotation `r_0` reverses the parity of the corners of the unit square. -/
lemma sum_sqRotCorner (c : Fin 2 → Fin 2) : ∑ l, sqRotCorner c l = ∑ l, c l + 1 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, sqRotCorner_zero, sqRotCorner_one,
    add_comm (c 0) (c 1), ← add_assoc]

lemma onCube_planeRot_apply (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) (c : Fin 2 → Fin 2) :
    (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onCube.toFun ζ c
      = ζ (sqRotCorner c) :=
  CubeTransformation.planeRot_onCube_toFun_apply ζ c

/-- Georgii's rotation `r_0` exchanges the two staggered caps. -/
lemma image_onCube_planeRot_anisoAntiG {m n : Fin 2} (hmn : m ≠ n) :
    (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onCube.toFun ''
      anisoAntiG δ u m = anisoAntiG δ u n :=
  image_onCube_anisoAntiG _ sqRotCorner sqRotCorner_surjective onCube_planeRot_apply
    sum_sqRotCorner hmn

/-- **Georgii's shift group `Θ̃ = {θ_i : i_1 + i_2 ≡ 0 mod 2}`** for (18.34): the iterated
reflection `r^a` fixes a staggered cap exactly when `a_1 + a_2` is even. -/
lemma preimage_tauPow_anisoAntiG {a : Fin 2 → ℤ} (ha : Even (a 0 + a 1)) (n : Fin 2) :
    tauPow (cubeRefl (sphere (0 : V) 1)) (latticeToTorus 0 a) ⁻¹' anisoAntiG δ u n
      = anisoAntiG δ u n := by
  have hp : ∑ k, latticeParity a k = 0 := sum_latticeParity_two ha
  ext ζ
  simp only [Set.mem_preimage, mem_anisoAntiG, tauPow_cubeRefl_latticeToTorus_zero]
  constructor
  · intro hζ c
    have hc := hζ (c + latticeParity a)
    rwa [add_assoc, corner_add_self, add_zero, sum_add, hp, add_zero] at hc
  · intro hζ c
    have hc := hζ (c + latticeParity a)
    rwa [sum_add, hp, add_zero] at hc

/-- Georgii's rotation `r_0` (18.20) belongs to `I_{C,λ}(Φ)` for (18.34). -/
theorem isSymmetry_planeRot_anisoAntiCube [Nontrivial V] :
    (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).IsSymmetry
      (anisoAntiCube α h u 2) (sphereProb V) :=
  CubeTransformation.isSymmetry_of_spin_refl anisoAntiCube_cubeRefl (fun _ ↦ rfl) fun ζ ↦ by
    have hb := cubeBondSum_onCube_of_spin_refl
      (ψ := fun x y : sphere (0 : V) 1 ↦ anisoBond α (u : V) (x : V) (y : V))
      (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)) (fun _ ↦ rfl) ζ
    have hs := cubeSiteSum_onCube_of_spin_refl
      (v := fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (u : V)⟫)
      (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)) (fun _ ↦ rfl) ζ
    simp only [anisoAntiCube]
    rw [hb, hs]


/-- **Georgii's "`G_1` and `G_2` are related to each other by `r_0, r_1, r_2`"** for (18.34). -/
theorem isPhiSymmetric_anisoAntiG [Nontrivial V] :
    IsPhiSymmetric (anisoAntiCube α h u 2) (sphereProb V) (anisoAntiG δ u) :=
  isPhiSymmetric_of_ne anisoAntiCube_cubeRefl fun m n hmn ↦
    ⟨CubeTransformation.refl 0, CubeTransformation.isSymmetry_refl anisoAntiCube_cubeRefl 0,
      image_onCube_refl_anisoAntiG 0 hmn⟩

/-! ### Georgii 18.3.7: the conclusion -/

section Conclusion

variable [Nontrivial V] (hα0 : 0 ≤ α) (hα1 : α < 1) (hh : h ^ 2 < 4 * (1 - α ^ 2))
  (hδ0 : 0 < δ)

include hα0 hα1 hh hδ0

/-- **Georgii's "by continuity, `G_ε(Φ) ⊆ G_1 ∪ G_2` when `ε > 0` is small enough"** for
(18.34): the two exact local ground states lie in the *open* set `G_1 ∪ G_2`, and `E^C` is
compact. -/
theorem exists_localGroundStates_subset_anisoAntiG :
    ∃ ε > 0, localGroundStates (anisoAntiCube α h u 2) (sphereProb V) ε
      ⊆ ⋃ n, anisoAntiG δ u n := by
  refine exists_pos_localGroundStates_subset_of_compactSpace continuous_anisoAntiCube
    (neg_four_le_anisoAntiCube hα0 hα1.le hh.le) (ζ₀ := polarStagger u 0)
    (anisoAntiCube_polarStagger hα0 hα1 hh 0) (isOpen_iUnion fun n ↦ isOpen_anisoAntiG n) ?_
  intro ζ hζ
  obtain ⟨n, rfl⟩ := (anisoAntiCube_eq_neg_four_iff hα0 hα1 hh ζ).1 hζ
  exact Set.mem_iUnion.2 ⟨n, polarStagger_mem_anisoAntiG hδ0 n⟩

variable (hδ1 : δ ≤ 1)

include hδ1

/-- **Georgii's "`{G_1, G_2}` is a stable partition of the local ground states"** for (18.34). -/
theorem isPStablePartition_anisoAntiG :
    IsPStablePartition (anisoAntiCube α h u 2) (sphereProb V) Set.univ (anisoAntiG δ u) where
  exists_localGroundStates_subset := exists_localGroundStates_subset_anisoAntiG hα0 hα1 hh hδ0
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_anisoAntiG hδ1 k a

/-- **Georgii 18.3.7, the anisotropic Heisenberg antiferromagnet in an external field (18.34).**
*Theorem (18.25) ensures that `|ex 𝒢(βΦ)| ≥ 2` when `β` is large enough.*

The local ground states are the two staggered polar configurations
(`anisoAntiCube_eq_neg_four_iff`), the partition into the two staggered polar caps is stable
because the two patterns disagree at every corner and the caps are disjoint
(`isPStablePartition_anisoAntiG`), and it is `Φ`-symmetric because each reflection `r_k` of the
cube reverses the parity of the corners (`isPhiSymmetric_anisoAntiG`).  As in the Ising
antiferromagnet 18.3.2 the partition is *not* `r`-symmetric, so this is the count in `𝒢(βΦ)`,
through Corollary (7.29), and not in `𝒢_Θ(βΦ)`. -/
theorem eventually_two_le_encard_extremePoints_anisoAnti :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * anisoAntiCube α h u 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * anisoAntiCube α h u 2 ζ),
      (2 : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G (cubeGibbsSpec (sphere (0 : V) 1)
        (fun ζ ↦ β * anisoAntiCube α h u 2 ζ) (sphereProb V) hφβ hMβ)).extremePoints
          ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hGε⟩ :=
    exists_localGroundStates_subset_anisoAntiG (u := u) (δ := δ) hα0 hα1 hh hδ0
  exact eventually_le_encard_extremePoints_G (E := sphere (0 : V) 1)
    (φ := anisoAntiCube α h u 2) (ν := sphereProb V) (Gs := anisoAntiG δ u)
    measurable_anisoAntiCube (neg_four_le_anisoAntiCube hα0 hα1.le hh.le) anisoAntiCube_cubeRefl
    (isCubeConfining_univ ⟨4 + 4 * |h|, abs_anisoAntiCube_le hα0 hα1.le⟩)
    (isPStablePartition_anisoAntiG hα0 hα1 hh hδ0 hδ1)
    (isPhiSymmetric_anisoAntiG (u := u) (δ := δ) (α := α) (h := h))
    measurableSet_anisoAntiG hε hGε

open Peierls in
/-- **Georgii 18.3.7**, the two Gibbs measures themselves: for `β` large enough there are two
mutually singular Gibbs measures for `βΦ`, random perturbations of the two staggered polar
ground states, invariant under the shifts `θ_a` with `a_1 + a_2` even and exchanged by the
`Φ`-symmetries `r_0`, `r_1`, `r_2` and by the shifts `θ_{(1,0)}`, `θ_{(0,1)}`. -/
theorem eventually_exists_anisoAnti_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * anisoAntiCube α h u 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * anisoAntiCube α h u 2 ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → sphere (0 : V) 1),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (sphere (0 : V) 1)
          (fun ζ ↦ β * anisoAntiCube α h u 2 ζ) (sphereProb V) hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart (sphere (0 : V) 1) (anisoAntiG δ u n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ), Even (a 0 + a 1) →
          MeasurePreserving (shift (sphere (0 : V) 1) a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onLattice
          (sphere (0 : V) 1)).toFun = μ 1 ∧
        (μ 1).map ((CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onLattice
          (sphere (0 : V) 1)).toFun = μ 0 ∧
        (∀ k : Fin 2, (μ 0).map ((CubeTransformation.refl (E := sphere (0 : V) 1) k).onLattice
          (sphere (0 : V) 1)).toFun = μ 1) ∧
        (∀ k : Fin 2, (μ 1).map ((CubeTransformation.refl (E := sphere (0 : V) 1) k).onLattice
          (sphere (0 : V) 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 1).map (shift (sphere (0 : V) 1) (Pi.single k 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 0).map (shift (sphere (0 : V) 1) (Pi.single k 1)).toFun = μ 1) := by
  obtain ⟨ε, hε, hGε⟩ :=
    exists_localGroundStates_subset_anisoAntiG (u := u) (δ := δ) hα0 hα1 hh hδ0
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := sphere (0 : V) 1)
    (φ := anisoAntiCube α h u 2) (ν := sphereProb V) (G := anisoAntiG δ u)
    measurable_anisoAntiCube (neg_four_le_anisoAntiCube hα0 hα1.le hh.le) anisoAntiCube_cubeRefl
    (isCubeConfining_univ ⟨4 + 4 * |h|, abs_anisoAntiCube_le hα0 hα1.le⟩)
    (isPStablePartition_anisoAntiG hα0 hα1 hh hδ0 hδ1)
    (isPhiSymmetric_anisoAntiG (u := u) (δ := δ) (α := α) (h := h))
    measurableSet_anisoAntiG hε hGε] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, h9⟩ := hβ hφβ hMβ
  have hrot : (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).IsSymmetry
      (fun ζ ↦ β * anisoAntiCube α h u 2 ζ) (sphereProb V) :=
    isSymmetry_planeRot_anisoAntiCube.const_mul anisoAntiCube_cubeRefl β
  have hrefl : ∀ k : Fin 2, (CubeTransformation.refl (E := sphere (0 : V) 1) k).IsSymmetry
      (fun ζ ↦ β * anisoAntiCube α h u 2 ζ) (sphereProb V) := fun k ↦
    CubeTransformation.isSymmetry_refl (ν := sphereProb V)
      (fun k ζ ↦ by rw [anisoAntiCube_cubeRefl k ζ]) k
  exact ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n a ha ↦ h6 n a (preimage_tauPow_anisoAntiG ha n),
    h8 0 1 _ hrot (image_onCube_planeRot_anisoAntiG (by decide)),
    h8 1 0 _ hrot (image_onCube_planeRot_anisoAntiG (by decide)),
    fun k ↦ h8 0 1 _ (hrefl k) (image_onCube_refl_anisoAntiG k (by decide)),
    fun k ↦ h8 1 0 _ (hrefl k) (image_onCube_refl_anisoAntiG k (by decide)),
    fun k ↦ h9 0 1 k (by rw [preimage_cubeRefl_anisoAntiG]; rfl),
    fun k ↦ h9 1 0 k (by rw [preimage_cubeRefl_anisoAntiG]; rfl)⟩

end Conclusion

/-! ### Georgii's hypothesis `|h| < 2` is not sufficient -/

section Counterexample

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The inner product of two vectors of the plane spanned by an orthonormal pair `e, f`. -/
lemma inner_smul_add_smul {e f : V} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪f, e⟫ = 0)
    (t s t' s' : ℝ) : ⟪t • e + s • f, t' • e + s' • f⟫ = t * t' + s * s' := by
  have hef' : ⟪e, f⟫ = 0 := by rw [real_inner_comm]; exact hef
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he, hf, hef, hef']
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- A unit vector of the plane spanned by an orthonormal pair. -/
lemma norm_smul_add_smul {e f : V} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪f, e⟫ = 0) {t s : ℝ}
    (hts : t ^ 2 + s ^ 2 = 1) : ‖t • e + s • f‖ = 1 := by
  have hsq : ‖t • e + s • f‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, inner_smul_add_smul he hf hef]
    nlinarith [hts]
  have hfac : (‖t • e + s • f‖ - 1) * (‖t • e + s • f‖ + 1) = 0 := by nlinarith [hsq]
  rcases mul_eq_zero.1 hfac with hz | hz
  · linarith
  · linarith [norm_nonneg (t • e + s • f)]

/-- **Georgii's hypothesis `|h| < 2` in (18.34) is not sufficient.**  As soon as
`4(1 - α²) < h²` the value `-4` is *not* a lower bound for `Φ_C`, so the two staggered polar
squares are not the local ground states of `Φ`: the configuration with
`σ_{(0,0)} = σ_{(1,1)} = t u + s w` and `σ_{(1,0)} = σ_{(0,1)} = t u - s w`, `w ⊥ u` a unit
vector and `t = h/(2(1 + α))`, `s = √(1 - t²)`, has all four bonds equal to
`(1 + α)t² - α - ht = -α - h²/(4(1 + α))`, hence `Φ_C = -4α - h²/(1 + α) < -4`.  The hypothesis
`h² < 4(1 - α²)` of the theorems above is therefore not an artefact of the proof; it is exactly
the positive-definiteness of the second variation of `Φ_C` at the staggered polar state.

`w` exists as soon as `2 ≤ finrank ℝ V`, which is Georgii's `n ≥ 2`. -/
theorem exists_lt_neg_four_anisoAntiCube {w : V} (hα0 : 0 ≤ α) (hh4 : h ^ 2 < 4)
    (hh : 4 * (1 - α ^ 2) < h ^ 2) (hw : ‖w‖ = 1) (huw : ⟪w, (u : V)⟫ = 0) :
    ∃ ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1, anisoAntiCube α h u 2 ζ < -4 := by
  have hu : ‖(u : V)‖ = 1 := norm_sphere_eq_one u
  have h1α : (0 : ℝ) < 1 + α := by linarith
  set t : ℝ := h / (2 * (1 + α)) with ht
  have ht1 : t ^ 2 ≤ 1 := by
    rw [ht, div_pow, div_le_one (by positivity)]
    nlinarith
  set s : ℝ := Real.sqrt (1 - t ^ 2) with hs
  have hs2 : s ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  have hts : t ^ 2 + s ^ 2 = 1 := by rw [hs2]; ring
  have hts' : t ^ 2 + (-s) ^ 2 = 1 := by rw [neg_sq]; exact hts
  set x : sphere (0 : V) 1 :=
    ⟨t • (u : V) + s • w, mem_sphere_zero_iff_norm.2 (norm_smul_add_smul hu hw huw hts)⟩ with hx
  set y : sphere (0 : V) 1 :=
    ⟨t • (u : V) + (-s) • w, mem_sphere_zero_iff_norm.2 (norm_smul_add_smul hu hw huw hts')⟩
      with hy
  refine ⟨sqOf x y y x, ?_⟩
  have hxu : ⟪(x : V), (u : V)⟫ = t := by
    have hxu' := inner_smul_add_smul (e := (u : V)) (f := w) hu hw huw t s 1 0
    rw [one_smul, zero_smul, add_zero] at hxu'
    rw [hx]
    simpa using hxu'
  have hyu : ⟪(y : V), (u : V)⟫ = t := by
    have hyu' := inner_smul_add_smul (e := (u : V)) (f := w) hu hw huw t (-s) 1 0
    rw [one_smul, zero_smul, add_zero] at hyu'
    rw [hy]
    simpa using hyu'
  have hxy : ⟪(x : V), (y : V)⟫ = t ^ 2 - s ^ 2 := by
    have hxy' := inner_smul_add_smul (e := (u : V)) (f := w) hu hw huw t s t (-s)
    rw [hx, hy]
    rw [show ((⟨t • (u : V) + s • w, _⟩ : sphere (0 : V) 1) : V) = t • (u : V) + s • w from rfl,
      show ((⟨t • (u : V) + (-s) • w, _⟩ : sphere (0 : V) 1) : V) = t • (u : V) + (-s) • w from rfl,
      hxy']
    ring
  have hbond : anisoAntiBond α h (u : V) (x : V) (y : V) = (1 + α) * t ^ 2 - α - h * t := by
    rw [anisoAntiBond, anisoBond, hxu, hyu, hxy, hs2]
    ring
  rw [anisoAntiCube_eq_cubeBondSum,
    cubeBondSum_two (fun _ _ : sphere (0 : V) 1 ↦ anisoAntiBond_comm) (sqOf x y y x)]
  simp only [sqOf_sqCorner_zero_zero, sqOf_sqCorner_one_zero, sqOf_sqCorner_zero_one,
    sqOf_sqCorner_one_one]
  rw [anisoAntiBond_comm (x := (y : V)) (y := (x : V)), hbond]
  have hkey : (1 + α) * t ^ 2 - α - h * t < -1 := by
    have hexp : (1 + α) * t ^ 2 - α - h * t = -α - h ^ 2 / (4 * (1 + α)) := by
      rw [ht]
      field_simp
      ring
    rw [hexp]
    have hdiv : 1 - α < h ^ 2 / (4 * (1 + α)) := by
      rw [lt_div_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith

end Counterexample

end MeasureTheory.GibbsMeasure

end

end

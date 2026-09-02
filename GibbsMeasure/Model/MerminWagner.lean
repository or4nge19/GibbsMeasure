/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.SymmetryInheritance
public import GibbsMeasure.Potential.Pair
public import GibbsMeasure.Mathlib.Analysis.Calculus.IteratedDeriv.SecondDifference
public import GibbsMeasure.Mathlib.Analysis.PSeries
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import GibbsMeasure.Mathlib.Data.Countable.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Data.Prod.Lex

/-!
# Georgii §9.2: continuous symmetries in two dimensions (Mermin–Wagner)

Theorem (9.20) and its two lemmas (9.28), (9.33): a one-parameter group `(τ^t)_{t ∈ ℝ}` of
`λ`-preserving pure spin symmetries of a pair potential on `ℤ²` cannot be broken, provided the
interaction is twice differentiable along the group with second derivative bounded by a
coupling `J` obeying the logarithmic decay condition (9.21).

The mechanism is Proposition (9.3)
(`measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion`, in
`GibbsMeasure/Specification/SymmetryInheritance.lean`); this file only constructs the localized
versions and proves the energy estimate.

## Site set

Lemma (9.33) is an estimate about a function `‖·‖ : S → ℕ` and a distance `d : S → S → ℕ` on the
sites: `‖j‖ ≤ ‖i‖ + d(i, j)`, `d` symmetric, and the *two-dimensional* counting bound
`|{‖·‖ = m}| ≤ c₀ (m + 1)` (Georgii: `|{‖·‖ = ℓ}| = 8 ℓ` on `ℤ²` for the maximum norm). This is
`IsPlanarSiteNorm`, and Lemma (9.33) and Theorem (9.20) are proved for any countable linearly
ordered site set carrying such a norm (`Potential.pair` needs the linear order to pick the
representative `i < j` of a pair `{i, j}`). Georgii's `S = ℤ²` is the instance
`ℤ ×ₗ ℤ` (`Lex (ℤ × ℤ)`: the product `ℤ × ℤ` carries Mathlib's product *partial* order, so the
lexicographic type synonym is the Mathlib way to put a linear order on it without an instance
diamond) with the maximum norm, `isPlanarSiteNorm_int_lex`.

## Main results

* `apply_add_apply_sub_le_of_iteratedDeriv_two_le`: the Taylor bound behind (9.28),
  `f(x + h) + f(x − h) − 2 f(x) ≤ M h²` when `f'' ≤ M`; (9.28) uses only the *upper* bound on
  the second derivative.
* `MeasureTheory.GibbsMeasure.spinWave`: the transformations `τ̃ = (τ_i^{t(i)})_{i ∈ S}` of
  (9.27), with the site-wise group law `spin_spin_of_mul_eq` derived from (9.18).
* `MeasureTheory.GibbsMeasure.hamiltonian_spinWave_add_sub_le`: **Lemma (9.28)**,
  `β (H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ − 2 H_Λ) ≤ ∑_{i, j} J(i, j) (t(i) − t(j))²` (the right-hand side is
  the `dirichletEnergy`, summed over ordered pairs; the unordered sum (9.29) over the pairs
  meeting `Λ` is smaller). Only Georgii's summability (2.2) of `Φ` is used.
* `MeasureTheory.GibbsMeasure.MerminWagner.dirichletEnergy_profile_le`: **Lemma (9.33)** in
  quantitative form, `∑_{i, j} J(i, j) (t(i) − t(j))² ≤ 1096 c₀ (N + 1)² K / Q(L)` for the
  profile `t = r(‖·‖ − N, L)` of (9.30)–(9.32) (`profile`), and
  `MerminWagner.exists_dirichletEnergy_profile_le`, Georgii's statement: for every `C > 0` some
  `L ≥ 1` makes the energy at most `C`. Georgii's three sums `Σ₁, Σ₂, Σ₃` are `shellBound`; the
  split between `Σ₂` and `Σ₃` is at `d(i, j) ≤ (‖i‖ − N)³` rather than Georgii's `(‖i‖ − N)²`,
  because the tail estimate `tsum_ofReal_mul_Q_sq_le` used here is `∑_{d > R} J Q(d)² ≲ 1/R`
  (Georgii's is `≲ R^{-3/2}`); the cubic split costs nothing.
* `MeasureTheory.GibbsMeasure.measurePreserving_of_logDecay`: **Theorem (9.20)** on a countable
  linearly ordered site set with a planar norm, for every `τ^u`, `u ∈ ℝ` (Georgii reduces to
  `u = 1`; here the profile is scaled by `u` and (9.33) is applied with `C = 1 / (u² + 1)`), and
  `measurePreserving_of_logDecay_int_lex` on `ℤ² = ℤ ×ₗ ℤ` (`isPlanarSiteNorm_int_lex`).

Georgii's Examples (9.22)–(9.23) (plane rotators, Heisenberg models) and Corollary (9.24) are
not formalised here.

## Conventions

The inverse temperature `β` multiplies the Hamiltonian; Georgii's statement is `β = 1`. The
hypothesis (ii) of (9.20) is read with `β Φ`: `β ∂²_t φ_{ij}(x, τ^t_j y) ≤ J(i, j)`, so no sign
condition on `β` is needed. The family `(τ^u)` is given by `hτ : ∀ u, (τ u).IsPureSpin` and the
group law (9.18) `hgrp : ∀ s t, τ s * τ t = τ (s + t)` in the group `Transformation S E`; `τ⁰ = id`
and `(τ_i^t)⁻¹ = τ_i^{-t}` are derived (`spin_zero_of_mul_eq`, `spin_symm_of_mul_eq`). The
`(τ^u)`-invariance of `Φ` is `hsym`, in the form of `Potential.map_pair_eq_iff`. `J` is assumed
symmetric and nonnegative, as in Georgii; the constant `K` of (9.21) is automatically
nonnegative (`LogDecay.nonneg`).

The decay condition (9.21) is stated with the maximum norm `‖·‖` instead of Georgii's Euclidean
`|·|`; since `‖·‖ ≤ |·| ≤ 2 ‖·‖`, the two are equivalent up to the constant `K` (Georgii uses
this in step 3 of his proof).

## Missing Mathlib

The first section contains general lemmas with their intended Mathlib homes:
`apply_add_apply_sub_le_of_iteratedDeriv_two_le` (`Mathlib/Analysis/Convex/Deriv.lean`),
`Real.not_summable_one_div_succ_mul_log_succ` (`Mathlib/Analysis/PSeries.lean`),
`ENNReal.tsum_comp_eq_tsum_encard_preimage_mul`
(`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`), `Lex.instCountable`
(`Mathlib/Data/Countable/Basic.lean`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Georgii (9.30)–(9.32): the profile

All sequences are indexed from `0`, so `q k` below is Georgii's `q(k + 1)`, `Q L` is his `Q(L)`
and `r L m` is his `r(m, L)`. -/

namespace MeasureTheory.GibbsMeasure

namespace MerminWagner

/-- **Georgii (9.30)**, shifted: `q 0 = 1` and `q k = 1 / ((k + 1) log (k + 1))` for `k ≥ 1`. -/
def q (k : ℕ) : ℝ := if k = 0 then 1 else 1 / ((k + 1) * Real.log (k + 1))

/-- **Georgii (9.31)**: `Q L = ∑_{k < L} q k`. -/
def Q (L : ℕ) : ℝ := ∑ k ∈ Finset.range L, q k

/-- **Georgii (9.32)**: `r L m = (∑_{m ≤ k < L} q k) / Q L`, equal to `1` at `m = 0` and to `0`
for `m ≥ L`. -/
def r (L m : ℕ) : ℝ := (∑ k ∈ Finset.Ico m L, q k) / Q L

lemma q_nonneg (k : ℕ) : 0 ≤ q k := by
  unfold q
  split_ifs
  · exact zero_le_one
  · exact div_nonneg zero_le_one (mul_nonneg (by positivity)
      (Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])))

lemma q_zero : q 0 = 1 := by simp [q]

lemma q_le_one (k : ℕ) : q k ≤ 1 := by
  unfold q
  split_ifs with hk
  · exact le_rfl
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    have hlog : Real.log 2 ≤ Real.log (k + 1) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [div_le_one (by nlinarith)]
    nlinarith

/-- `q` is antitone on `ℕ`. -/
lemma q_antitone : Antitone q := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [q_zero]; exact q_le_one 1
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [q, hk0, ite_false, Nat.succ_ne_zero, Nat.cast_succ]
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlogk : 0 < Real.log (k + 1) := Real.log_pos (by linarith)
    have hlog : Real.log (k + 1) ≤ Real.log (k + 1 + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul (by linarith) hlog hlogk.le (by linarith))

lemma Q_nonneg (L : ℕ) : 0 ≤ Q L := Finset.sum_nonneg fun k _ ↦ q_nonneg k

lemma Q_mono : Monotone Q := fun _ _ h ↦
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun k _ _ ↦ q_nonneg k

lemma one_le_Q {L : ℕ} (hL : 1 ≤ L) : 1 ≤ Q L :=
  (by simp [Q, q_zero] : (1 : ℝ) = Q 1) ▸ Q_mono hL

lemma Q_pos {L : ℕ} (hL : 1 ≤ L) : 0 < Q L := zero_lt_one.trans_le (one_le_Q hL)

/-- Georgii, step 2 of the proof of (9.33): `Q(L) < 1 + log L`, in the form
`Q d ≤ 1 + log d / log 2`, hence `Q d ≤ m + 1` for `d ≤ 2 ^ m`. -/
lemma Q_le_of_le_pow {d m : ℕ} (hd : d ≤ 2 ^ m) : Q d ≤ m + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp only [Q, Finset.range_zero, Finset.sum_empty]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `q k ≤ 1 / ((k + 1) log 2)` for `k ≥ 1`
  have hq : ∀ k ∈ Finset.range d,
      q k ≤ if k = 0 then 1 else 1 / Real.log 2 * (1 / ((k : ℝ) + 1)) := by
    intro k _
    unfold q
    split_ifs with hk
    · exact le_rfl
    · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
      rw [show 1 / Real.log 2 * (1 / ((k : ℝ) + 1)) = 1 / (((k : ℝ) + 1) * Real.log 2) by
        rw [div_mul_div_comm, one_mul, mul_comm]]
      exact one_div_le_one_div_of_le (mul_pos (by positivity) hlog2)
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by linarith)) (by positivity))
  have hharm : (∑ k ∈ Finset.range d,
      if k = 0 then (1 : ℝ) else 1 / Real.log 2 * (1 / ((k : ℝ) + 1)))
      ≤ 1 + 1 / Real.log 2 * Real.log d := by
    have hsplit : (∑ k ∈ Finset.range d,
        if k = 0 then (1 : ℝ) else 1 / Real.log 2 * (1 / ((k : ℝ) + 1)))
        = 1 + 1 / Real.log 2 * (∑ k ∈ Finset.range d, 1 / ((k : ℝ) + 1) - 1) := by
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [Nat.succ_ne_zero, ite_false, ite_true, Nat.cast_zero, zero_add, div_one,
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Finset.mul_sum]
      ring
    rw [hsplit]
    have hH : (∑ k ∈ Finset.range d, 1 / ((k : ℝ) + 1)) ≤ 1 + Real.log d := by
      have := harmonic_le_one_add_log d
      push_cast [harmonic] at this
      simpa only [one_div] using this
    have : 0 ≤ 1 / Real.log 2 := by positivity
    nlinarith
  have hlogd : Real.log d ≤ m * Real.log 2 := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by exact_mod_cast hd0) (by exact_mod_cast hd)
  calc Q d ≤ ∑ k ∈ Finset.range d,
        if k = 0 then (1 : ℝ) else 1 / Real.log 2 * (1 / ((k : ℝ) + 1)) := Finset.sum_le_sum hq
    _ ≤ 1 + 1 / Real.log 2 * Real.log d := hharm
    _ ≤ 1 + 1 / Real.log 2 * (m * Real.log 2) := by gcongr
    _ = m + 1 := by field_simp; ring

/-- `Q` is unbounded (Georgii: `Q(L) > log log L`). -/
lemma exists_le_Q (M : ℝ) : ∃ L : ℕ, 1 ≤ L ∧ M ≤ Q L := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg q_nonneg).1
    Real.not_summable_one_div_succ_mul_log_succ
  obtain ⟨L, hL⟩ := (tendsto_atTop_atTop.1 hdiv) (max M 1)
  refine ⟨L, ?_, (le_max_left _ _).trans (hL L le_rfl)⟩
  by_contra h
  have hL0 : L = 0 := by omega
  have := hL L le_rfl
  simp [hL0] at this
  linarith [le_max_right M 1]

lemma r_zero {L : ℕ} (hL : 1 ≤ L) : r L 0 = 1 := by
  rw [r, ← Finset.range_eq_Ico]
  exact div_self (Q_pos hL).ne'

lemma r_of_le {L m : ℕ} (h : L ≤ m) : r L m = 0 := by
  simp [r, Finset.Ico_eq_empty_of_le h]

lemma r_nonneg (L m : ℕ) : 0 ≤ r L m :=
  div_nonneg (Finset.sum_nonneg fun k _ ↦ q_nonneg k) (Q_nonneg L)

lemma r_antitone (L : ℕ) : Antitone (r L) := fun _ _ hab ↦
  div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left hab) fun k _ _ ↦ q_nonneg k)
    (Q_nonneg L)

/-- Georgii, step 1 of the proof of (9.33): for `a ≤ b`,
`r L a - r L b ≤ (b - a) q a / Q L` (`q` is antitone). -/
lemma r_sub_r_le_mul_q {L a b : ℕ} (hab : a ≤ b) :
    r L a - r L b ≤ (b - a : ℕ) * q a / Q L := by
  unfold r
  rw [← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Q_nonneg L)
  rcases le_or_gt b L with hbL | hbL
  · rw [← Finset.sum_Ico_consecutive _ hab hbL, add_sub_cancel_right]
    calc ∑ k ∈ Finset.Ico a b, q k ≤ ∑ k ∈ Finset.Ico a b, q a :=
          Finset.sum_le_sum fun k hk ↦ q_antitone (Finset.mem_Ico.1 hk).1
      _ = (b - a : ℕ) * q a := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  · rw [Finset.Ico_eq_empty_of_le hbL.le, Finset.sum_empty, sub_zero]
    rcases le_or_gt a L with haL | haL
    · calc ∑ k ∈ Finset.Ico a L, q k ≤ ∑ k ∈ Finset.Ico a L, q a :=
            Finset.sum_le_sum fun k hk ↦ q_antitone (Finset.mem_Ico.1 hk).1
        _ = (L - a : ℕ) * q a := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (b - a : ℕ) * q a :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le_sub_right hbL.le a)
              (q_nonneg a)
    · rw [Finset.Ico_eq_empty_of_le haL.le, Finset.sum_empty]
      exact mul_nonneg (Nat.cast_nonneg _) (q_nonneg a)

/-- Georgii, step 1 of the proof of (9.33): for `a ≤ b`, `r L a - r L b ≤ Q (b - a) / Q L`. -/
lemma r_sub_r_le_Q {L a b : ℕ} (hab : a ≤ b) : r L a - r L b ≤ Q (b - a) / Q L := by
  unfold r
  rw [← sub_div]
  refine div_le_div_of_nonneg_right ?_ (Q_nonneg L)
  have key : ∀ c, c ≤ b → ∑ k ∈ Finset.Ico a c, q k ≤ Q (b - a) := by
    intro c hcb
    calc ∑ k ∈ Finset.Ico a c, q k ≤ ∑ k ∈ Finset.Ico a b, q k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hcb)
            fun k _ _ ↦ q_nonneg k
      _ = ∑ k ∈ Finset.range (b - a), q (a + k) := Finset.sum_Ico_eq_sum_range _ _ _
      _ ≤ ∑ k ∈ Finset.range (b - a), q k :=
          Finset.sum_le_sum fun k _ ↦ q_antitone (Nat.le_add_left k a)
  rcases le_or_gt b L with hbL | hbL
  · rw [← Finset.sum_Ico_consecutive _ hab hbL, add_sub_cancel_right]
    exact key b le_rfl
  · rw [Finset.Ico_eq_empty_of_le hbL.le, Finset.sum_empty, sub_zero]
    rcases le_or_gt a L with haL | haL
    · exact key L hbL.le
    · rw [Finset.Ico_eq_empty_of_le haL.le, Finset.sum_empty]
      exact Q_nonneg _

lemma r_sub_r_nonneg {L a b : ℕ} (hab : a ≤ b) : 0 ≤ r L a - r L b :=
  sub_nonneg.2 (r_antitone L hab)

/-- Georgii, proof of (9.33), estimate of `Σ₂`: `k log(2 k³) q(k)² ≤ 4 q(k)`, here in the shifted
form `k log (2 k³) (q k)² ≤ 4 q k`. -/
lemma mul_log_mul_q_sq_le (k : ℕ) : k * Real.log (2 * (k : ℝ) ^ 3) * q k ^ 2 ≤ 4 * q k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [q_zero]
  have hk0 : k ≠ 0 := hk.ne'
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogk : 0 < Real.log (k + 1) := Real.log_pos (by linarith)
  have hq : q k = 1 / ((k + 1) * Real.log (k + 1)) := by simp [q, hk0]
  have hlog : Real.log (2 * (k : ℝ) ^ 3) ≤ 4 * Real.log (k + 1) := by
    rw [show (4 : ℝ) * Real.log (k + 1) = Real.log (((k : ℝ) + 1) ^ 4) by
      rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by positivity) ?_
    nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg (k : ℝ)]
  have hqpos : 0 < q k := by rw [hq]; positivity
  rw [hq]
  have hden : 0 < (k + 1) * Real.log (k + 1) := by positivity
  rw [div_pow, one_pow, mul_one_div, mul_one_div, div_le_div_iff₀ (by positivity) hden]
  have : (k : ℝ) * Real.log (2 * (k : ℝ) ^ 3) ≤ 4 * ((k + 1) * Real.log (k + 1)) := by
    calc (k : ℝ) * Real.log (2 * (k : ℝ) ^ 3) ≤ k * (4 * Real.log (k + 1)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 4 * ((k + 1) * Real.log (k + 1)) := by nlinarith
  nlinarith [mul_pos hden hden]

/-- `(ℓ + 2)³ ≤ 27 · 2^ℓ`. -/
lemma add_two_pow_three_le (ℓ : ℕ) : (ℓ + 2) ^ 3 ≤ 27 * 2 ^ ℓ := by
  induction ℓ with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> norm_num
    · have h1 : (n + 3) ^ 3 ≤ 2 * (n + 2) ^ 3 := by
        nlinarith [Nat.pow_le_pow_left hn 3, Nat.pow_le_pow_left hn 2, hn]
      calc (n + 1 + 2) ^ 3 = (n + 3) ^ 3 := by ring
        _ ≤ 2 * (n + 2) ^ 3 := h1
        _ ≤ 2 * (27 * 2 ^ n) := by omega
        _ = 27 * 2 ^ (n + 1) := by ring

/-! ### Site sets with a planar norm; the decay condition (9.21) -/

variable {S : Type*}

/-- A *planar norm* on the site set: a "norm" `‖·‖ : S → ℕ` and a "distance" `d : S → S → ℕ`
with `d` symmetric, the triangle inequality `‖j‖ ≤ ‖i‖ + d(i, j)`, finite balls, and the
two-dimensional counting bound `|{‖·‖ = m}| ≤ c₀ (m + 1)`. On `ℤ²` with the maximum norm one may
take `c₀ = 8` (`isPlanarSiteNorm_int_lex`); Georgii's proof of (9.33) uses exactly these four
properties, and Comment (9.34)(1) explains why the linear growth of the spheres is essential. -/
structure IsPlanarSiteNorm (nrm : S → ℕ) (d : S → S → ℕ) (c₀ : ℕ) : Prop where
  /-- `d(i, j) = d(j, i)`. -/
  d_comm : ∀ i j, d i j = d j i
  /-- `‖j‖ ≤ ‖i‖ + d(i, j)`. -/
  nrm_le : ∀ i j, nrm j ≤ nrm i + d i j
  /-- `|{‖·‖ = m}| ≤ c₀ (m + 1)`. -/
  encard_le : ∀ m, {i | nrm i = m}.encard ≤ (c₀ * (m + 1) : ℕ)
  /-- The balls `{d(i, ·) ≤ n}` are finite. -/
  finite_ball : ∀ i n, {j | d i j ≤ n}.Finite

/-- **Georgii (9.21)** (with the norm underlying `d`): `∑_{0 < d(i,j) ≤ n} d(i,j)² J(i,j) ≤ K log n`
for all `i` and `n ≥ 2`. The sum is a `tsum` over `S`; it is a finite sum whenever the balls of `d`
are finite (`IsPlanarSiteNorm.finite_ball`), which is the only situation in which this condition
is used (for a `d` with infinite balls and a non-summable `J` the `tsum` convention would make it
vacuous). -/
def LogDecay (d : S → S → ℕ) (J : S → S → ℝ) (K : ℝ) : Prop :=
  ∀ i, ∀ n : ℕ, 2 ≤ n →
    ∑' j, (if 0 < d i j ∧ d i j ≤ n then (d i j : ℝ) ^ 2 * J i j else 0) ≤ K * Real.log n

/-- The Dirichlet energy `∑_{(i, j) ∈ S × S} J(i, j) (t(i) − t(j))²` of a profile `t`, over
*ordered* pairs; Georgii's sum (9.29) over unordered pairs is half of it (for a symmetric `J`). -/
def dirichletEnergy (J : S → S → ℝ) (t : S → ℝ) : ℝ≥0∞ :=
  ∑' p : S × S, ENNReal.ofReal (J p.1 p.2 * (t p.1 - t p.2) ^ 2)

/-- Georgii, proof of (9.33): the profile `t(i) = r(‖i‖ − N, L)`, equal to `1` on `{‖·‖ ≤ N}` and
to `0` off `{‖·‖ < N + L}`. -/
def profile (nrm : S → ℕ) (N L : ℕ) (i : S) : ℝ := r L (nrm i - N)

variable {nrm : S → ℕ} {d : S → S → ℕ} {c₀ : ℕ} {J : S → S → ℝ} {K : ℝ}

lemma profile_of_le {N L : ℕ} (hL : 1 ≤ L) {i : S} (hi : nrm i ≤ N) : profile nrm N L i = 1 := by
  rw [profile, Nat.sub_eq_zero_of_le hi, r_zero hL]

lemma profile_of_ge {N L : ℕ} {i : S} (hi : N + L ≤ nrm i) : profile nrm N L i = 0 :=
  r_of_le (by omega)

lemma profile_nonneg (N L : ℕ) (i : S) : 0 ≤ profile nrm N L i := r_nonneg _ _

lemma profile_antitone (N L : ℕ) {i j : S} (h : nrm i ≤ nrm j) :
    profile nrm N L j ≤ profile nrm N L i :=
  r_antitone L (Nat.sub_le_sub_right h N)

/-- The decay condition (9.21) in `ℝ≥0∞`. -/
lemma LogDecay.tsum_ofReal_le (hgeo : IsPlanarSiteNorm nrm d c₀) (hJ0 : ∀ i j, 0 ≤ J i j)
    (hJ : LogDecay d J K) (i : S) {n : ℕ} (hn : 2 ≤ n) :
    ∑' j, (if 0 < d i j ∧ d i j ≤ n then ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0) ≤
      ENNReal.ofReal (K * Real.log n) := by
  set f : S → ℝ := fun j ↦ if 0 < d i j ∧ d i j ≤ n then (d i j : ℝ) ^ 2 * J i j else 0 with hf
  have hf0 : ∀ j, 0 ≤ f j := fun j ↦ by
    simp only [hf]
    split_ifs
    · exact mul_nonneg (by positivity) (hJ0 i j)
    · exact le_rfl
  have hsum : Summable f := by
    refine summable_of_ne_finset_zero (s := (hgeo.finite_ball i n).toFinset) fun j hj ↦ ?_
    simp only [hf]
    rw [ite_eq_right]
    rintro ⟨-, h2⟩
    exact hj ((hgeo.finite_ball i n).mem_toFinset.2 h2)
  calc ∑' j, (if 0 < d i j ∧ d i j ≤ n then ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0)
      = ∑' j, ENNReal.ofReal (f j) := tsum_congr fun j ↦ by
        simp only [hf]
        split_ifs <;> simp
    _ = ENNReal.ofReal (∑' j, f j) := (ENNReal.ofReal_tsum_of_nonneg hf0 hsum).symm
    _ ≤ ENNReal.ofReal (K * Real.log n) := ENNReal.ofReal_le_ofReal (hJ i n hn)

/-- Georgii, steps 2 and 3 of the proof of (9.33), combined: the weighted tails
`∑_{d(i,j) > R} J(i,j) Q(d(i,j))² ≤ 108 K / (R + 1)`. The range of `d(i, ·)` is cut into the
dyadic shells `2^ℓ ≤ d < 2^{ℓ+1}`, on which `Q(d) ≤ ℓ + 2` (`Q_le_of_le_pow`) and the decay
condition controls `∑ d² J`. -/
lemma tsum_ofReal_mul_Q_sq_le (hgeo : IsPlanarSiteNorm nrm d c₀) (hJ0 : ∀ i j, 0 ≤ J i j)
    (hJ : LogDecay d J K) (hK : 0 ≤ K) (i : S) (R : ℕ) :
    ∑' j, (if R < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) ≤
      ENNReal.ofReal (108 * K / (R + 1)) := by
  set ℓ₀ := Nat.log 2 R with hℓ₀
  set c : ℕ → ℝ≥0∞ := fun ℓ ↦ ENNReal.ofReal (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ) with hc
  -- step A: pointwise domination by the shell decomposition
  have hA : ∀ j, (if R < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) ≤
      ∑' ℓ, (if ℓ₀ ≤ ℓ ∧ 2 ^ ℓ ≤ d i j ∧ d i j < 2 ^ (ℓ + 1) then
        ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) * c ℓ else 0) := by
    intro j
    split_ifs with hR
    · have hd0 : d i j ≠ 0 := by omega
      set ℓ := Nat.log 2 (d i j) with hℓ
      have h1 : 2 ^ ℓ ≤ d i j := Nat.pow_log_le_self 2 hd0
      have h2 : d i j < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self one_lt_two _
      have h0 : ℓ₀ ≤ ℓ := Nat.log_mono_right hR.le
      refine le_trans ?_ (ENNReal.le_tsum ℓ)
      have hJij : 0 ≤ J i j := hJ0 i j
      have hdJ : 0 ≤ (d i j : ℝ) ^ 2 * J i j := mul_nonneg (by positivity) hJij
      rw [ite_eq_left ⟨h0, h1, h2⟩, hc, ← ENNReal.ofReal_mul hdJ]
      refine ENNReal.ofReal_le_ofReal ?_
      have hQ : Q (d i j) ≤ ℓ + 2 := by
        have := Q_le_of_le_pow (m := ℓ + 1) h2.le
        push_cast at this
        linarith
      have hQ0 : 0 ≤ Q (d i j) := Q_nonneg _
      have hdpos : (0 : ℝ) < d i j := by exact_mod_cast Nat.pos_of_ne_zero hd0
      have h4 : (4 : ℝ) ^ ℓ ≤ (d i j : ℝ) ^ 2 := by
        have h1' : ((2 : ℝ) ^ ℓ) ≤ d i j := by exact_mod_cast h1
        calc (4 : ℝ) ^ ℓ = ((2 : ℝ) ^ ℓ) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          _ ≤ (d i j : ℝ) ^ 2 := by gcongr
      calc J i j * Q (d i j) ^ 2 ≤ J i j * ((ℓ : ℝ) + 2) ^ 2 := by gcongr
        _ = (d i j : ℝ) ^ 2 * J i j * (((ℓ : ℝ) + 2) ^ 2 / (d i j : ℝ) ^ 2) := by
            field_simp
        _ ≤ (d i j : ℝ) ^ 2 * J i j * (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ) := by
            gcongr
    · exact zero_le
  -- step B: each shell contributes at most `27 K / 2^ℓ`
  have hB : ∀ ℓ, ∑' j, (if ℓ₀ ≤ ℓ ∧ 2 ^ ℓ ≤ d i j ∧ d i j < 2 ^ (ℓ + 1) then
        ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) * c ℓ else 0) ≤
      if ℓ₀ ≤ ℓ then ENNReal.ofReal (27 * K / 2 ^ ℓ) else 0 := by
    intro ℓ
    split_ifs with hℓ
    · have hn : 2 ≤ 2 ^ (ℓ + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc ∑' j, (if ℓ₀ ≤ ℓ ∧ 2 ^ ℓ ≤ d i j ∧ d i j < 2 ^ (ℓ + 1) then
              ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) * c ℓ else 0)
          ≤ ∑' j, (if 0 < d i j ∧ d i j ≤ 2 ^ (ℓ + 1) then
              ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0) * c ℓ := by
            refine ENNReal.tsum_le_tsum fun j ↦ ?_
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd ⟨lt_of_lt_of_le (by positivity) h1.2.1, h1.2.2.le⟩ h2
            · exact zero_le
            · exact zero_le
        _ = (∑' j, (if 0 < d i j ∧ d i j ≤ 2 ^ (ℓ + 1) then
              ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0)) * c ℓ := ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal (K * Real.log ((2 ^ (ℓ + 1) : ℕ) : ℝ)) * c ℓ := by
            gcongr
            exact hJ.tsum_ofReal_le hgeo hJ0 i hn
        _ ≤ ENNReal.ofReal (27 * K / 2 ^ ℓ) := by
            rw [hc, ← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have hl2 : Real.log 2 ≤ 1 := by
              linarith [Real.log_le_sub_one_of_pos (zero_lt_two' ℝ)]
            have h27 : ((ℓ : ℝ) + 2) ^ 3 ≤ 27 * 2 ^ ℓ := by exact_mod_cast add_two_pow_three_le ℓ
            have h4 : (4 : ℝ) ^ ℓ = 2 ^ ℓ * 2 ^ ℓ := by rw [← mul_pow]; norm_num
            have hpos : (0 : ℝ) < 2 ^ ℓ := by positivity
            calc K * Real.log ((2 ^ (ℓ + 1) : ℕ) : ℝ) * (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ)
                = K * (((ℓ : ℝ) + 1) * Real.log 2) * (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ) := by
                  push_cast
                  rw [Real.log_pow]
                  push_cast
                  ring
              _ ≤ K * (((ℓ : ℝ) + 1) * 1) * (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ) := by gcongr
              _ ≤ K * ((ℓ : ℝ) + 2) * (((ℓ : ℝ) + 2) ^ 2 / 4 ^ ℓ) := by gcongr; linarith
              _ = K * (((ℓ : ℝ) + 2) ^ 3 / 4 ^ ℓ) := by ring
              _ ≤ K * ((27 * 2 ^ ℓ) / (2 ^ ℓ * 2 ^ ℓ)) := by rw [h4]; gcongr
              _ = 27 * K / 2 ^ ℓ := by field_simp
    · simp only [hℓ, false_and, ite_false, tsum_zero, le_refl]
  -- step C: the geometric tail
  have hC : ∑' ℓ, (if ℓ₀ ≤ ℓ then ENNReal.ofReal (27 * K / 2 ^ ℓ) else 0) ≤
      ENNReal.ofReal (108 * K / (R + 1)) := by
    have hreindex : ∑' ℓ, (if ℓ₀ ≤ ℓ then ENNReal.ofReal (27 * K / 2 ^ ℓ) else 0) =
        ∑' m, ENNReal.ofReal (27 * K / 2 ^ (m + ℓ₀)) := by
      rw [← (add_left_injective ℓ₀).tsum_eq (f := fun ℓ ↦
        if ℓ₀ ≤ ℓ then ENNReal.ofReal (27 * K / 2 ^ ℓ) else 0)]
      · exact tsum_congr fun m ↦ by simp
      · intro ℓ hℓ
        simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hℓ
        obtain ⟨hℓ, -⟩ := hℓ
        exact ⟨ℓ - ℓ₀, show ℓ - ℓ₀ + ℓ₀ = ℓ by omega⟩
    rw [hreindex]
    refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun m _ ↦ by positivity]
    refine ENNReal.ofReal_le_ofReal ?_
    have hR : (R : ℝ) + 1 ≤ 2 * 2 ^ ℓ₀ := by
      have h := Nat.lt_pow_succ_log_self one_lt_two R
      rw [← hℓ₀, pow_succ] at h
      have h' : R + 1 ≤ 2 * 2 ^ ℓ₀ := by omega
      exact_mod_cast h'
    have hgeom := sum_geometric_two_le n
    have hpos : (0 : ℝ) < 2 ^ ℓ₀ := by positivity
    calc ∑ m ∈ Finset.range n, 27 * K / 2 ^ (m + ℓ₀)
        = 27 * K / 2 ^ ℓ₀ * ∑ m ∈ Finset.range n, (1 / (2 : ℝ)) ^ m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ ↦ ?_
          rw [pow_add, one_div_pow]
          field_simp
      _ ≤ 27 * K / 2 ^ ℓ₀ * 2 := by gcongr
      _ ≤ 108 * K / (R + 1) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hpos (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hR hK]
  calc ∑' j, (if R < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0)
      ≤ ∑' j, ∑' ℓ, (if ℓ₀ ≤ ℓ ∧ 2 ^ ℓ ≤ d i j ∧ d i j < 2 ^ (ℓ + 1) then
          ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) * c ℓ else 0) := ENNReal.tsum_le_tsum hA
    _ = ∑' ℓ, ∑' j, (if ℓ₀ ≤ ℓ ∧ 2 ^ ℓ ≤ d i j ∧ d i j < 2 ^ (ℓ + 1) then
          ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) * c ℓ else 0) := ENNReal.tsum_comm
    _ ≤ ∑' ℓ, (if ℓ₀ ≤ ℓ then ENNReal.ofReal (27 * K / 2 ^ ℓ) else 0) := ENNReal.tsum_le_tsum hB
    _ ≤ ENNReal.ofReal (108 * K / (R + 1)) := hC

/-- The decay condition forces `K ≥ 0` as soon as there is a site. -/
lemma LogDecay.nonneg (hJ0 : ∀ i j, 0 ≤ J i j) (hJ : LogDecay d J K) (i : S) : 0 ≤ K := by
  have h := hJ i 2 le_rfl
  have h0 : 0 ≤ ∑' j, (if 0 < d i j ∧ d i j ≤ 2 then (d i j : ℝ) ^ 2 * J i j else 0) :=
    tsum_nonneg fun j ↦ by
      split_ifs
      · exact mul_nonneg (by positivity) (hJ0 i j)
      · exact le_rfl
  have hlog : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
  exact (mul_nonneg_iff_of_pos_right hlog).1 (h0.trans h)

/-- The balls `{‖·‖ < M}` are finite: each sphere has finite `encard`. -/
lemma IsPlanarSiteNorm.finite_lt (hgeo : IsPlanarSiteNorm nrm d c₀) (M : ℕ) :
    {i | nrm i < M}.Finite := by
  have : {i | nrm i < M} = ⋃ m ∈ Finset.range M, {i | nrm i = m} := by
    ext i
    simp
  rw [this]
  exact (Finset.range M).finite_toSet.biUnion fun m _ ↦
    Set.finite_of_encard_le_coe (hgeo.encard_le m)

/-! ### `ℤ²` with the maximum norm

Georgii's site set `S = ℤ²`, as the lexicographic type synonym `ℤ ×ₗ ℤ` (a linear order, as
`Potential.pair` needs), with the maximum norm `‖(a, b)‖ = |a| ∨ |b|`. Georgii's count
`|{‖·‖ = ℓ}| = 8 ℓ` is replaced by the crude bound `|{‖·‖ = m}| ≤ 4 (2 m + 1) ≤ 8 (m + 1)`. -/

/-- The maximum norm `‖(a, b)‖ = |a| ∨ |b|` on `ℤ² = ℤ ×ₗ ℤ`. -/
def intLexNorm (i : ℤ ×ₗ ℤ) : ℕ := max (ofLex i).1.natAbs (ofLex i).2.natAbs

/-- The maximum-norm distance `‖i − j‖` on `ℤ ×ₗ ℤ`. -/
def intLexDist (i j : ℤ ×ₗ ℤ) : ℕ :=
  max ((ofLex i).1 - (ofLex j).1).natAbs ((ofLex i).2 - (ofLex j).2).natAbs

/-- The sphere `{‖·‖ = m}` of `ℤ²` lies in the four sides of the square `[-m, m]²`. -/
lemma setOf_intLexNorm_eq_subset (m : ℕ) :
    {i : ℤ ×ₗ ℤ | intLexNorm i = m} ⊆
      ((Finset.Icc (-(m : ℤ)) m ×ˢ ({-(m : ℤ), (m : ℤ)} : Finset ℤ) ∪
        ({-(m : ℤ), (m : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-(m : ℤ)) m).map toLex.toEmbedding :
        Set (ℤ ×ₗ ℤ)) := by
  intro i hi
  simp only [Set.mem_ofPred_eq, intLexNorm] at hi
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_union, Finset.mem_product,
    Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton, Equiv.coe_toEmbedding]
  refine ⟨ofLex i, ?_, rfl⟩
  omega

/-- `ℤ²` with the maximum norm is a planar site set (with `c₀ = 8`). -/
theorem isPlanarSiteNorm_int_lex : IsPlanarSiteNorm intLexNorm intLexDist 8 where
  d_comm i j := by
    simp only [intLexDist]
    omega
  nrm_le i j := by
    simp only [intLexNorm, intLexDist]
    omega
  encard_le m := by
    refine (Set.encard_le_encard (setOf_intLexNorm_eq_subset m)).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map]
    refine Nat.cast_le.2 ((Finset.card_union_le _ _).trans ?_)
    rw [Finset.card_product, Finset.card_product, Int.card_Icc]
    have h2 : ({-(m : ℤ), (m : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
    have h3 : ((m : ℤ) + 1 - -m).toNat = 2 * m + 1 := by omega
    rw [h3]
    nlinarith
  finite_ball i n := by
    refine (((Set.finite_Icc ((ofLex i).1 - n) ((ofLex i).1 + n)).prod
      (Set.finite_Icc ((ofLex i).2 - n) ((ofLex i).2 + n))).image toLex).subset ?_
    intro j hj
    simp only [Set.mem_ofPred_eq, intLexDist] at hj
    refine ⟨ofLex j, ?_, rfl⟩
    simp only [Set.mem_prod, Set.mem_Icc]
    omega

/-! ### Georgii, Lemma (9.33) -/

variable (hgeo : IsPlanarSiteNorm nrm d c₀)
include hgeo

/-- Georgii, step 1 of the proof of (9.33): for `‖i‖ < ‖j‖`,
`t(i) − t(j) ≤ Q(d(i, j)) / Q(L)`. -/
lemma profile_sub_profile_le_Q {N L : ℕ} {i j : S} (hij : nrm i < nrm j) :
    profile nrm N L i - profile nrm N L j ≤ Q (d i j) / Q L := by
  have h := hgeo.nrm_le i j
  refine (r_sub_r_le_Q (L := L) (Nat.sub_le_sub_right hij.le N)).trans ?_
  exact div_le_div_of_nonneg_right (Q_mono (by omega)) (Q_nonneg L)

/-- Georgii, step 1 of the proof of (9.33): for `‖i‖ < ‖j‖`,
`t(i) − t(j) ≤ d(i, j) q(‖i‖ − N) / Q(L)`. -/
lemma profile_sub_profile_le_mul_q {N L : ℕ} {i j : S} (hij : nrm i < nrm j) :
    profile nrm N L i - profile nrm N L j ≤ d i j * q (nrm i - N) / Q L := by
  have h := hgeo.nrm_le i j
  refine (r_sub_r_le_mul_q (L := L) (Nat.sub_le_sub_right hij.le N)).trans ?_
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (q_nonneg _)) (Q_nonneg L)
  exact_mod_cast (show nrm j - N - (nrm i - N) ≤ d i j by omega)

omit hgeo in
lemma profile_sub_profile_nonneg (N L : ℕ) {i j : S} (hij : nrm i ≤ nrm j) :
    0 ≤ profile nrm N L i - profile nrm N L j :=
  sub_nonneg.2 (profile_antitone N L hij)

omit hgeo in
/-- `‖i‖ = ‖j‖` gives `t(i) = t(j)`. -/
lemma profile_eq_of_nrm_eq (N L : ℕ) {i j : S} (hij : nrm i = nrm j) :
    profile nrm N L i = profile nrm N L j := by
  simp only [profile, hij]

/-- The bound on `∑_{‖j‖ > ‖i‖} J(i, j) (t(i) − t(j))²` for the profile `t = r(‖·‖ − N, L)`, as a
function of `m = ‖i‖`: Georgii's three sums `Σ₁` (`m ≤ N`), `Σ₂ + Σ₃` (`N < m < N + L`; the pairs
are split at `d(i, j) ≤ (m − N)³`) and `0` (`t(i) = 0` for `m ≥ N + L`). -/
def shellBound (K : ℝ) (N L m : ℕ) : ℝ :=
  if m ≤ N then 108 * K / Q L ^ 2
  else if m < N + L then
    K * Real.log (2 * ((m - N : ℕ) : ℝ) ^ 3) * q (m - N) ^ 2 / Q L ^ 2 +
      108 * K / (((m - N) ^ 3 : ℕ) + 1) / Q L ^ 2
  else 0

omit hgeo in
lemma shellBound_of_le {K : ℝ} {N L m : ℕ} (hm : m ≤ N) :
    shellBound K N L m = 108 * K / Q L ^ 2 := by
  simp [shellBound, hm]

omit hgeo in
lemma shellBound_of_lt {K : ℝ} {N L m : ℕ} (hm : N < m) (hmL : m < N + L) :
    shellBound K N L m = K * Real.log (2 * ((m - N : ℕ) : ℝ) ^ 3) * q (m - N) ^ 2 / Q L ^ 2 +
      108 * K / (((m - N) ^ 3 : ℕ) + 1) / Q L ^ 2 := by
  simp [shellBound, hm.not_ge, hmL]

omit hgeo in
lemma shellBound_of_ge {K : ℝ} {N L m : ℕ} (hL : 1 ≤ L) (hm : N + L ≤ m) :
    shellBound K N L m = 0 := by
  have h1 : ¬ m ≤ N := by omega
  have h2 : ¬ m < N + L := by omega
  simp [shellBound, h1, h2]

omit hgeo in
lemma shellBound_nonneg {K : ℝ} (hK : 0 ≤ K) (N L m : ℕ) : 0 ≤ shellBound K N L m := by
  unfold shellBound
  split_ifs with h1 h2
  · positivity
  · have ha : (1 : ℝ) ≤ ((m - N : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m - N by omega)
    have hlog : 0 ≤ Real.log (2 * ((m - N : ℕ) : ℝ) ^ 3) :=
      Real.log_nonneg (by linarith [one_le_pow₀ ha (n := 3)])
    positivity
  · exact le_rfl

variable (hJ0 : ∀ i j, 0 ≤ J i j) (hJ : LogDecay d J K) (hK : 0 ≤ K)
include hJ0 hJ hK

/-- Georgii, estimate of `Σ₁` in the proof of (9.33): for `‖i‖ ≤ N`,
`∑_{‖j‖ > ‖i‖} J(i, j) (t(i) − t(j))² ≤ 108 K / Q(L)²`. -/
lemma tsum_profile_le_of_le {N L : ℕ} {i : S} (hi : nrm i ≤ N) :
    ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) ≤
      ENNReal.ofReal (shellBound K N L (nrm i)) := by
  rw [shellBound_of_le hi]
  have hpt : ∀ j, (if nrm i < nrm j then
      ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) ≤
      (if 0 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) *
        ENNReal.ofReal (1 / Q L ^ 2) := by
    intro j
    split_ifs with h1 h2
    · rw [← ENNReal.ofReal_mul (mul_nonneg (hJ0 i j) (sq_nonneg _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hd := profile_sub_profile_le_Q hgeo (N := N) (L := L) h1
      have h0 := profile_sub_profile_nonneg (nrm := nrm) N L h1.le
      calc J i j * (profile nrm N L i - profile nrm N L j) ^ 2
          ≤ J i j * (Q (d i j) / Q L) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hd 2) (hJ0 i j)
        _ = J i j * Q (d i j) ^ 2 * (1 / Q L ^ 2) := by rw [div_pow]; ring
    · exact absurd (by have := hgeo.nrm_le i j; omega) h2
    · exact zero_le
    · exact zero_le
  calc ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0)
      ≤ ∑' j, (if 0 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) *
          ENNReal.ofReal (1 / Q L ^ 2) := ENNReal.tsum_le_tsum hpt
    _ = (∑' j, (if 0 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0)) *
          ENNReal.ofReal (1 / Q L ^ 2) := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (108 * K / ((0 : ℕ) + 1)) * ENNReal.ofReal (1 / Q L ^ 2) := by
        gcongr
        exact tsum_ofReal_mul_Q_sq_le hgeo hJ0 hJ hK i 0
    _ = ENNReal.ofReal (108 * K / Q L ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [Nat.cast_zero, zero_add, div_one, mul_one_div]

/-- Georgii, estimates of `Σ₂` and `Σ₃` in the proof of (9.33): for `N < ‖i‖ < N + L`, with
`a = ‖i‖ − N`, the pairs `d(i, j) ≤ a³` are controlled by the decay condition and the pairs
`d(i, j) > a³` by the tail estimate `tsum_ofReal_mul_Q_sq_le`. -/
lemma tsum_profile_le_of_lt {N L : ℕ} {i : S} (hi : N < nrm i) (hiL : nrm i < N + L) :
    ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) ≤
      ENNReal.ofReal (shellBound K N L (nrm i)) := by
  rw [shellBound_of_lt hi hiL]
  set a := nrm i - N with ha
  have ha1 : 1 ≤ a := by omega
  have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hlog : 0 ≤ Real.log (2 * (a : ℝ) ^ 3) :=
    Real.log_nonneg (by linarith [one_le_pow₀ ha1' (n := 3)])
  have hpt : ∀ j, (if nrm i < nrm j then
      ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) ≤
      (if 0 < d i j ∧ d i j ≤ 2 * a ^ 3 then ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0) *
        ENNReal.ofReal (q a ^ 2 / Q L ^ 2) +
      (if a ^ 3 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) *
        ENNReal.ofReal (1 / Q L ^ 2) := by
    intro j
    by_cases h1 : nrm i < nrm j
    · rw [ite_eq_left h1]
      have hd0 : 0 < d i j := by have := hgeo.nrm_le i j; omega
      have h0 := profile_sub_profile_nonneg (nrm := nrm) N L h1.le
      rcases le_or_gt (d i j) (a ^ 3) with hd | hd
      · refine le_trans ?_ le_self_add
        rw [ite_eq_left ⟨hd0, by omega⟩,
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (hJ0 i j))]
        refine ENNReal.ofReal_le_ofReal ?_
        have hb := profile_sub_profile_le_mul_q hgeo (N := N) (L := L) h1
        rw [← ha] at hb
        calc J i j * (profile nrm N L i - profile nrm N L j) ^ 2
            ≤ J i j * (d i j * q a / Q L) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hb 2) (hJ0 i j)
          _ = (d i j : ℝ) ^ 2 * J i j * (q a ^ 2 / Q L ^ 2) := by
              rw [div_pow, mul_pow]; ring
      · refine le_trans ?_ le_add_self
        rw [ite_eq_left hd, ← ENNReal.ofReal_mul (mul_nonneg (hJ0 i j) (sq_nonneg _))]
        refine ENNReal.ofReal_le_ofReal ?_
        have hb := profile_sub_profile_le_Q hgeo (N := N) (L := L) h1
        calc J i j * (profile nrm N L i - profile nrm N L j) ^ 2
            ≤ J i j * (Q (d i j) / Q L) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hb 2) (hJ0 i j)
          _ = J i j * Q (d i j) ^ 2 * (1 / Q L ^ 2) := by rw [div_pow]; ring
    · rw [ite_eq_right h1]
      exact zero_le
  have hn : 2 ≤ 2 * a ^ 3 := by nlinarith [Nat.one_le_pow 3 a ha1]
  calc ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0)
      ≤ ∑' j, ((if 0 < d i j ∧ d i j ≤ 2 * a ^ 3 then
            ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0) *
          ENNReal.ofReal (q a ^ 2 / Q L ^ 2) +
        (if a ^ 3 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0) *
          ENNReal.ofReal (1 / Q L ^ 2)) := ENNReal.tsum_le_tsum hpt
    _ = (∑' j, (if 0 < d i j ∧ d i j ≤ 2 * a ^ 3 then
            ENNReal.ofReal ((d i j : ℝ) ^ 2 * J i j) else 0)) *
          ENNReal.ofReal (q a ^ 2 / Q L ^ 2) +
        (∑' j, (if a ^ 3 < d i j then ENNReal.ofReal (J i j * Q (d i j) ^ 2) else 0)) *
          ENNReal.ofReal (1 / Q L ^ 2) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (K * Real.log ((2 * a ^ 3 : ℕ) : ℝ)) *
          ENNReal.ofReal (q a ^ 2 / Q L ^ 2) +
        ENNReal.ofReal (108 * K / ((a ^ 3 : ℕ) + 1)) * ENNReal.ofReal (1 / Q L ^ 2) := by
        gcongr
        · exact hJ.tsum_ofReal_le hgeo hJ0 i hn
        · exact tsum_ofReal_mul_Q_sq_le hgeo hJ0 hJ hK i (a ^ 3)
    _ = ENNReal.ofReal (K * Real.log (2 * (a : ℝ) ^ 3) * q a ^ 2 / Q L ^ 2) +
        ENNReal.ofReal (108 * K / ((a ^ 3 : ℕ) + 1) / Q L ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        · push_cast
          ring
        · rw [mul_one_div]
    _ = ENNReal.ofReal (K * Real.log (2 * (a : ℝ) ^ 3) * q a ^ 2 / Q L ^ 2 +
        108 * K / ((a ^ 3 : ℕ) + 1) / Q L ^ 2) :=
        (ENNReal.ofReal_add (div_nonneg (mul_nonneg (mul_nonneg hK hlog) (sq_nonneg _))
          (sq_nonneg _)) (by positivity)).symm

omit hgeo hJ0 hJ hK in
/-- For `‖i‖ ≥ N + L` the profile vanishes at `i` and beyond. -/
lemma tsum_profile_eq_zero_of_ge {N L : ℕ} {i : S} (hi : N + L ≤ nrm i) :
    ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun j ↦ ?_
  split_ifs with h
  · rw [profile_of_ge hi, profile_of_ge (by omega)]
    simp
  · rfl

/-- The inner sums of the Dirichlet energy of the profile are bounded by `shellBound`. -/
lemma tsum_profile_le_shellBound (N L : ℕ) (i : S) :
    ∑' j, (if nrm i < nrm j then
        ENNReal.ofReal (J i j * (profile nrm N L i - profile nrm N L j) ^ 2) else 0) ≤
      ENNReal.ofReal (shellBound K N L (nrm i)) := by
  rcases le_or_gt (nrm i) N with h1 | h1
  · exact tsum_profile_le_of_le hgeo hJ0 hJ hK h1
  rcases lt_or_ge (nrm i) (N + L) with h2 | h2
  · exact tsum_profile_le_of_lt hgeo hJ0 hJ hK h1 h2
  · rw [tsum_profile_eq_zero_of_ge h2]
    exact zero_le

omit hgeo hJ0 hJ in
/-- Georgii, estimate of `Σ₁`: the sites `‖·‖ ≤ N` contribute at most
`108 c₀ (N + 1)² K / Q(L)²`. -/
lemma sum_shellBound_range_le (N L : ℕ) :
    ∑ m ∈ Finset.range (N + 1), ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m ≤
      108 * c₀ * (N + 1) ^ 2 * K / Q L ^ 2 := by
  have hterm : ∀ m ∈ Finset.range (N + 1),
      ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m ≤ c₀ * (N + 1) * (108 * K / Q L ^ 2) := by
    intro m hm
    rw [Finset.mem_range] at hm
    rw [shellBound_of_le (by omega)]
    push_cast
    gcongr
    exact_mod_cast (show m ≤ N by omega)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

omit hgeo hJ0 hJ in
/-- Georgii, estimates of `Σ₂` and `Σ₃`: the sites `N < ‖·‖ < N + L` contribute at most
`2 c₀ (N + 1) K (4 Q(L) + 216) / Q(L)²`. -/
lemma sum_shellBound_Ico_le (N : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ∑ m ∈ Finset.Ico (N + 1) (N + L), ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m ≤
      2 * c₀ * (N + 1) * K * (4 * Q L + 216) / Q L ^ 2 := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (N + L - (N + 1)),
      ((c₀ * (N + 1 + k + 1) : ℕ) : ℝ) * shellBound K N L (N + 1 + k) ≤
        2 * c₀ * (N + 1) / Q L ^ 2 *
          (4 * K * q (k + 1) + 216 * K * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [shellBound_of_lt (by omega) (by omega), show N + 1 + k - N = k + 1 by omega]
    have hQ : 0 ≤ Q L ^ 2 := by positivity
    have hq0 := q_nonneg (k + 1)
    have hk1 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    -- the counting factor
    have hcount : ((c₀ * (N + 1 + k + 1) : ℕ) : ℝ) ≤ 2 * c₀ * (N + 1) * ((k : ℝ) + 1) := by
      push_cast
      nlinarith [(Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀), (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀) (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
        mul_nonneg (mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀)
          (Nat.cast_nonneg N : (0 : ℝ) ≤ N)) hk1,
        mul_nonneg (Nat.cast_nonneg c₀ : (0 : ℝ) ≤ c₀) hk1]
    -- `Σ₂`: `(k + 1) log (2 (k + 1)³) q(k + 1)² ≤ 4 q(k + 1)`
    have hS2 : ((k : ℝ) + 1) * (K * Real.log (2 * ((k + 1 : ℕ) : ℝ) ^ 3) * q (k + 1) ^ 2) ≤
        4 * K * q (k + 1) := by
      have := mul_log_mul_q_sq_le (k + 1)
      push_cast at this ⊢
      nlinarith [mul_le_mul_of_nonneg_left this hK]
    -- `Σ₃`: `(k + 1) / ((k + 1)³ + 1) ≤ 2 (1 / (k + 1) − 1 / (k + 2))`
    have hS3 : ((k : ℝ) + 1) * (108 * K / (((k + 1) ^ 3 : ℕ) + 1)) ≤
        216 * K * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)) := by
      push_cast
      have h1 : ((k : ℝ) + 1) / (((k : ℝ) + 1) ^ 3 + 1) ≤
          2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)) := by
        rw [div_sub_div _ _ (by positivity) (by positivity), ← mul_div_assoc,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_nonneg hk1 3, pow_nonneg hk1 2, sq_nonneg ((k : ℝ) + 1)]
      calc ((k : ℝ) + 1) * (108 * K / (((k : ℝ) + 1) ^ 3 + 1))
          = 108 * K * (((k : ℝ) + 1) / (((k : ℝ) + 1) ^ 3 + 1)) := by ring
        _ ≤ 108 * K * (2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1))) := by gcongr
        _ = 216 * K * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)) := by ring
    have hsb : 0 ≤ K * Real.log (2 * ((k + 1 : ℕ) : ℝ) ^ 3) * q (k + 1) ^ 2 / Q L ^ 2 +
        108 * K / (((k + 1) ^ 3 : ℕ) + 1) / Q L ^ 2 := by
      have := shellBound_nonneg (L := L) (N := N) hK (N + 1 + k)
      rwa [shellBound_of_lt (by omega) (by omega), show N + 1 + k - N = k + 1 by omega] at this
    calc ((c₀ * (N + 1 + k + 1) : ℕ) : ℝ) *
          (K * Real.log (2 * ((k + 1 : ℕ) : ℝ) ^ 3) * q (k + 1) ^ 2 / Q L ^ 2 +
            108 * K / (((k + 1) ^ 3 : ℕ) + 1) / Q L ^ 2)
        ≤ 2 * c₀ * (N + 1) * ((k : ℝ) + 1) *
          (K * Real.log (2 * ((k + 1 : ℕ) : ℝ) ^ 3) * q (k + 1) ^ 2 / Q L ^ 2 +
            108 * K / (((k + 1) ^ 3 : ℕ) + 1) / Q L ^ 2) := mul_le_mul_of_nonneg_right hcount hsb
      _ = 2 * c₀ * (N + 1) / Q L ^ 2 *
          (((k : ℝ) + 1) * (K * Real.log (2 * ((k + 1 : ℕ) : ℝ) ^ 3) * q (k + 1) ^ 2) +
            ((k : ℝ) + 1) * (108 * K / (((k + 1) ^ 3 : ℕ) + 1))) := by ring
      _ ≤ 2 * c₀ * (N + 1) / Q L ^ 2 *
          (4 * K * q (k + 1) + 216 * K * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1))) := by
          gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have htel : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)) =
      1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [htel]
  have hQsum : ∑ k ∈ Finset.range (N + L - (N + 1)), q (k + 1) ≤ Q L := by
    calc ∑ k ∈ Finset.range (N + L - (N + 1)), q (k + 1)
        = ∑ k ∈ Finset.Ico 1 (N + L - (N + 1) + 1), q k := by
          rw [Finset.sum_Ico_eq_sum_range]
          simp only [Nat.add_sub_cancel]
          exact Finset.sum_congr rfl fun k _ ↦ by rw [add_comm]
      _ ≤ ∑ k ∈ Finset.range L, q k := by
          rw [Finset.range_eq_Ico]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Ico_subset_Ico (by omega) (by omega)) fun k _ _ ↦ q_nonneg k
  have htel' : 1 - 1 / (((N + L - (N + 1) : ℕ) : ℝ) + 1) ≤ 1 := by
    have : 0 ≤ 1 / (((N + L - (N + 1) : ℕ) : ℝ) + 1) := by positivity
    linarith
  have hc : 0 ≤ 2 * (c₀ : ℝ) * (N + 1) / Q L ^ 2 := by positivity
  calc 2 * (c₀ : ℝ) * (N + 1) / Q L ^ 2 *
        (4 * K * ∑ k ∈ Finset.range (N + L - (N + 1)), q (k + 1) +
          216 * K * (1 - 1 / (((N + L - (N + 1) : ℕ) : ℝ) + 1)))
      ≤ 2 * (c₀ : ℝ) * (N + 1) / Q L ^ 2 * (4 * K * Q L + 216 * K * 1) := by gcongr
    _ = 2 * c₀ * (N + 1) * K * (4 * Q L + 216) / Q L ^ 2 := by ring

omit hgeo hJ0 hJ in
/-- Georgii, proof of (9.33), the three sums combined:
`∑_m |{‖·‖ = m}| shellBound(m) ≤ 548 c₀ (N + 1)² K / Q(L)`. -/
lemma sum_shellBound_le (N : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ∑ m ∈ Finset.range (N + L), ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m ≤
      548 * c₀ * (N + 1) ^ 2 * K / Q L := by
  rw [← Finset.sum_range_add_sum_Ico _ (show N + 1 ≤ N + L by omega)]
  refine (add_le_add (sum_shellBound_range_le hK N L) (sum_shellBound_Ico_le hK N hL)).trans ?_
  have hQ1 := one_le_Q hL
  have hQ : 0 < Q L := Q_pos hL
  rw [← add_div, div_le_div_iff₀ (by positivity) hQ]
  have hc : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hX : 0 ≤ (c₀ : ℝ) * (N + 1) * K := by positivity
  have hXN : 0 ≤ (c₀ : ℝ) * (N + 1) * K * N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hQ1 hX, mul_le_mul_of_nonneg_left hQ1 hXN,
    mul_nonneg hX (sub_nonneg.2 hQ1), mul_nonneg hXN (sub_nonneg.2 hQ1),
    mul_nonneg (mul_nonneg hX (sub_nonneg.2 hQ1)) hQ.le,
    mul_nonneg (mul_nonneg hXN (sub_nonneg.2 hQ1)) hQ.le]

omit hgeo hJ0 hJ hK in
lemma dirichletEnergy_const_mul (J : S → S → ℝ) (u : ℝ) (t : S → ℝ) :
    dirichletEnergy J (fun i ↦ u * t i) = ENNReal.ofReal (u ^ 2) * dirichletEnergy J t := by
  unfold dirichletEnergy
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg u)]
  congr 1
  ring

/-- **Georgii, Lemma (9.33)**, quantitative form: the Dirichlet energy of the profile
`t = r(‖·‖ − N, L)` is at most `1096 c₀ (N + 1)² K / Q(L)`, hence tends to `0` as `L → ∞`. -/
theorem dirichletEnergy_profile_le (hJsymm : ∀ i j, J i j = J j i) (N : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    dirichletEnergy J (profile nrm N L) ≤
      ENNReal.ofReal (1096 * c₀ * (N + 1) ^ 2 * K / Q L) := by
  set t := profile nrm N L with ht
  set F : S → S → ℝ≥0∞ := fun i j ↦
    if nrm i < nrm j then ENNReal.ofReal (J i j * (t i - t j) ^ 2) else 0 with hF
  -- the energy is at most twice the sum over the pairs `‖i‖ < ‖j‖`
  have hpt : ∀ p : S × S, ENNReal.ofReal (J p.1 p.2 * (t p.1 - t p.2) ^ 2) ≤
      F p.1 p.2 + F p.2 p.1 := by
    rintro ⟨i, j⟩
    simp only [hF]
    rcases lt_trichotomy (nrm i) (nrm j) with h | h | h
    · rw [ite_eq_left h]; exact le_self_add
    · rw [ht, profile_eq_of_nrm_eq N L h]
      simp
    · rw [ite_eq_left h, hJsymm i j, show (t i - t j) ^ 2 = (t j - t i) ^ 2 by ring]
      exact le_add_self
  have hswap : ∑' p : S × S, F p.2 p.1 = ∑' p : S × S, F p.1 p.2 :=
    (Equiv.prodComm S S).tsum_eq fun p ↦ F p.1 p.2
  have h2 : dirichletEnergy J t ≤ 2 * ∑' i, ∑' j, F i j := by
    calc dirichletEnergy J t ≤ ∑' p : S × S, (F p.1 p.2 + F p.2 p.1) := ENNReal.tsum_le_tsum hpt
      _ = 2 * ∑' i, ∑' j, F i j := by
        rw [ENNReal.tsum_add, hswap, ← ENNReal.tsum_prod, two_mul]
  -- the inner sums are bounded by `shellBound`, and the outer sum is a finite sum over shells
  have h3 : ∑' i, ∑' j, F i j ≤ ∑' i, ENNReal.ofReal (shellBound K N L (nrm i)) :=
    ENNReal.tsum_le_tsum fun i ↦ tsum_profile_le_shellBound hgeo hJ0 hJ hK N L i
  have h4 : ∑' i, ENNReal.ofReal (shellBound K N L (nrm i)) ≤
      ∑ m ∈ Finset.range (N + L),
        ((c₀ * (m + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (shellBound K N L m) := by
    rw [ENNReal.tsum_comp_eq_tsum_encard_preimage_mul nrm
      (fun m ↦ ENNReal.ofReal (shellBound K N L m))]
    rw [tsum_eq_sum (s := Finset.range (N + L)) fun m hm ↦ by
      rw [Finset.mem_range, not_lt] at hm
      simp [shellBound_of_ge hL hm]]
    refine Finset.sum_le_sum fun m _ ↦ ?_
    gcongr
    have h := ENat.toENNReal_le.2 (hgeo.encard_le m)
    rw [ENat.toENNReal_coe] at h
    exact h
  have h5 : ∑ m ∈ Finset.range (N + L),
      ((c₀ * (m + 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (shellBound K N L m) =
      ENNReal.ofReal (∑ m ∈ Finset.range (N + L),
        ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun m _ ↦
      mul_nonneg (Nat.cast_nonneg _) (shellBound_nonneg hK N L m)]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  calc dirichletEnergy J t ≤ 2 * ∑' i, ∑' j, F i j := h2
    _ ≤ 2 * ENNReal.ofReal (∑ m ∈ Finset.range (N + L),
        ((c₀ * (m + 1) : ℕ) : ℝ) * shellBound K N L m) := by
        rw [← h5]
        gcongr
        exact h3.trans h4
    _ ≤ 2 * ENNReal.ofReal (548 * c₀ * (N + 1) ^ 2 * K / Q L) := by
        gcongr
        exact sum_shellBound_le hK N hL
    _ = ENNReal.ofReal (1096 * c₀ * (N + 1) ^ 2 * K / Q L) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- **Georgii, Lemma (9.33).** Let `N ≥ 1` and `C > 0`. Under the decay condition (9.21) on `J`
there is `L ≥ 1` such that the Dirichlet energy (9.29) of the profile `t = r(‖·‖ − N, L)` is at
most `C`. -/
theorem exists_dirichletEnergy_profile_le (hJsymm : ∀ i j, J i j = J j i) (N : ℕ) {C : ℝ}
    (hC : 0 < C) :
    ∃ L : ℕ, 1 ≤ L ∧ dirichletEnergy J (profile nrm N L) ≤ ENNReal.ofReal C := by
  set M : ℝ := 1096 * c₀ * (N + 1) ^ 2 * K with hM
  have hM0 : 0 ≤ M := by positivity
  obtain ⟨L, hL, hLM⟩ := exists_le_Q (M / C)
  refine ⟨L, hL, (dirichletEnergy_profile_le hgeo hJ0 hJ hK hJsymm N hL).trans
    (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [← hM, div_le_iff₀ (Q_pos hL)]
  have : C * (M / C) = M := by field_simp
  calc M = C * (M / C) := this.symm
    _ ≤ C * Q L := mul_le_mul_of_nonneg_left hLM hC.le

end MerminWagner

/-! ### Georgii (9.27): spin waves, and Lemma (9.28) -/

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (9.27).** The *spin wave* `τ̃ = (τ_i^{t(i)})_{i ∈ S}` of a one-parameter family
`(τ^u)_{u ∈ ℝ}` of pure spin transformations with profile `t : S → ℝ`. -/
def spinWave (τ : ℝ → Transformation S E) (t : S → ℝ) : Transformation S E where
  sites := Equiv.refl S
  spin i := (τ (t i)).spin i

variable {τ : ℝ → Transformation S E}

lemma isPureSpin_spinWave (τ : ℝ → Transformation S E) (t : S → ℝ) :
    (spinWave τ t).IsPureSpin := rfl

@[simp] lemma spinWave_spin (t : S → ℝ) (i : S) : (spinWave τ t).spin i = (τ (t i)).spin i := rfl

@[simp] lemma spinWave_toFun_apply (t : S → ℝ) (ω : S → E) (i : S) :
    (spinWave τ t).toFun ω i = (τ (t i)).spin i (ω i) :=
  (isPureSpin_spinWave τ t).toFun_apply ω i

@[simp] lemma spinWave_inv_toFun_apply (t : S → ℝ) (ω : S → E) (i : S) :
    (spinWave τ t).inv.toFun ω i = ((τ (t i)).spin i).symm (ω i) :=
  (isPureSpin_spinWave τ t).inv_toFun_apply ω i

/-- Georgii (9.18) for pure spin transformations, site-wise: `τ_i^s ∘ τ_i^t = τ_i^{s + t}`. -/
lemma spin_spin_of_mul_eq (hτ : ∀ u, (τ u).IsPureSpin) (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (s t : ℝ) (i : S) (x : E) : (τ s).spin i ((τ t).spin i x) = (τ (s + t)).spin i x := by
  have h := congrArg (fun ρ : Transformation S E ↦ ρ.spin i x) (hgrp s t)
  have hi : (τ s).sites.symm i = i := by rw [hτ s]; rfl
  change (τ s).spin i ((τ t).spin ((τ s).sites.symm i) x) = (τ (s + t)).spin i x at h
  rwa [hi] at h

/-- `τ^0` is the identity (Georgii (9.18) at `s = t = 0`). -/
lemma spin_zero_of_mul_eq (hτ : ∀ u, (τ u).IsPureSpin) (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (i : S) (x : E) : (τ 0).spin i x = x := by
  have h := spin_spin_of_mul_eq hτ hgrp 0 0 i x
  rw [add_zero] at h
  exact ((τ 0).spin i).injective h

/-- The inverse of `τ_i^t` is `τ_i^{-t}` (Georgii (9.18)). -/
lemma spin_symm_of_mul_eq (hτ : ∀ u, (τ u).IsPureSpin) (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (t : ℝ) (i : S) (x : E) : ((τ t).spin i).symm x = (τ (-t)).spin i x := by
  rw [MeasurableEquiv.symm_apply_eq, spin_spin_of_mul_eq hτ hgrp, add_neg_cancel,
    spin_zero_of_mul_eq hτ hgrp]

section PairPotential

open Potential

variable [LinearOrder S] {φ : S → S → E → E → ℝ} {J : S → S → ℝ} {β : ℝ}

/-- Georgii, proof of (9.28): `ψ_{ij}(x, y) ≤ J(i, j) (t(i) − t(j))²`. By the
`(τ^u)`-invariance of `φ_{ij}`, `ψ_{ij}(x, y) = g(s) + g(-s) - 2 g(0)` with
`g(u) = φ_{ij}(x, τ_j^u y)` and `s = t(j) - t(i)`, and Taylor's formula
(`apply_add_apply_sub_le_of_iteratedDeriv_two_le`) bounds this by `J(i, j) s²`. -/
lemma pair_spinWave_add_sub_le (hτ : ∀ u, (τ u).IsPureSpin)
    (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (hsym : ∀ u i j, i < j → ∀ x y, φ i j ((τ u).spin i x) ((τ u).spin j y) = φ i j x y)
    (hφ : ∀ i j, i < j → ∀ x y, ContDiff ℝ 2 fun u ↦ φ i j x ((τ u).spin j y))
    (hJ : ∀ i j, i < j → ∀ x y u,
      β * iteratedDeriv 2 (fun u ↦ φ i j x ((τ u).spin j y)) u ≤ J i j)
    {i j : S} (hij : i < j) (t : S → ℝ) (x y : E) :
    β * (φ i j ((τ (t i)).spin i x) ((τ (t j)).spin j y) +
      φ i j ((τ (-t i)).spin i x) ((τ (-t j)).spin j y) - 2 * φ i j x y) ≤
      J i j * (t i - t j) ^ 2 := by
  set g : ℝ → ℝ := fun u ↦ φ i j x ((τ u).spin j y) with hg
  have h1 : φ i j ((τ (t i)).spin i x) ((τ (t j)).spin j y) = g (0 + (t j - t i)) := by
    rw [← hsym (-t i) i j hij, spin_spin_of_mul_eq hτ hgrp, spin_spin_of_mul_eq hτ hgrp,
      neg_add_cancel, spin_zero_of_mul_eq hτ hgrp, hg]
    simp only
    rw [show -t i + t j = 0 + (t j - t i) by ring]
  have h2 : φ i j ((τ (-t i)).spin i x) ((τ (-t j)).spin j y) = g (0 - (t j - t i)) := by
    rw [← hsym (t i) i j hij, spin_spin_of_mul_eq hτ hgrp, spin_spin_of_mul_eq hτ hgrp,
      add_neg_cancel, spin_zero_of_mul_eq hτ hgrp, hg]
    simp only
    rw [show t i + -t j = 0 - (t j - t i) by ring]
  have h3 : φ i j x y = g 0 := by
    simp only [hg, spin_zero_of_mul_eq hτ hgrp]
  have hcont : ContDiff ℝ 2 fun u ↦ β * g u := contDiff_const.mul (hφ i j hij x y)
  have hM : ∀ u, iteratedDeriv 2 (fun u ↦ β * g u) u ≤ J i j := fun u ↦ by
    rw [iteratedDeriv_const_mul β (hφ i j hij x y).contDiffAt]
    exact hJ i j hij x y u
  have := apply_add_apply_sub_le_of_iteratedDeriv_two_le hcont hM 0 (t j - t i)
  rw [h1, h2, h3, show (t i - t j) ^ 2 = (t j - t i) ^ 2 by ring]
  linarith

/-- **Georgii, Lemma (9.28).** For any profile `t` and any `Λ`,
`β (H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ − 2 H_Λ) ≤ ∑_{i, j} J(i, j) (t(i) − t(j))²` (the Dirichlet energy over
ordered pairs; Georgii's sum (9.29) over unordered pairs meeting `Λ` is smaller). The bound is
proved on the partial sums of the Hamiltonian series, so only Georgii's summability (2.2) is
used. The hypothesis (ii) of (9.20) is read with `β Φ`: `β ∂²_u φ_{ij}(x, τ_j^u y) ≤ J(i, j)`. -/
lemma hamiltonian_spinWave_add_sub_le [IsSummable (pair φ)] (hτ : ∀ u, (τ u).IsPureSpin)
    (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (hsym : ∀ u i j, i < j → ∀ x y, φ i j ((τ u).spin i x) ((τ u).spin j y) = φ i j x y)
    (hφ : ∀ i j, i < j → ∀ x y, ContDiff ℝ 2 fun u ↦ φ i j x ((τ u).spin j y))
    (hJ : ∀ i j, i < j → ∀ x y u,
      β * iteratedDeriv 2 (fun u ↦ φ i j x ((τ u).spin j y)) u ≤ J i j)
    (hJ0 : ∀ i j, 0 ≤ J i j) (t : S → ℝ) (Λ : Finset S) (ω : S → E) :
    ENNReal.ofReal (β * ((pair φ).hamiltonian Λ ((spinWave τ t).toFun ω) +
      (pair φ).hamiltonian Λ ((spinWave τ t).inv.toFun ω) -
      2 * (pair φ).hamiltonian Λ ω)) ≤ MerminWagner.dirichletEnergy J t := by
  set τ' := spinWave τ t with hτ'
  have hsum := (((hasSum_hamiltonian (Φ := pair φ) Λ (τ'.toFun ω)).add
    (hasSum_hamiltonian (Φ := pair φ) Λ (τ'.inv.toFun ω))).sub
    ((hasSum_hamiltonian (Φ := pair φ) Λ ω).mul_left 2)).mul_left β
  have htend : Tendsto (fun Δ : Finset S ↦ ENNReal.ofReal (∑ A ∈ Δ.powerset,
      β * ((pair φ).hamiltonianTerms Λ (τ'.toFun ω) A +
        (pair φ).hamiltonianTerms Λ (τ'.inv.toFun ω) A -
        2 * (pair φ).hamiltonianTerms Λ ω A))) atTop
      (𝓝 (ENNReal.ofReal (β * ((pair φ).hamiltonian Λ (τ'.toFun ω) +
        (pair φ).hamiltonian Λ (τ'.inv.toFun ω) -
        2 * (pair φ).hamiltonian Λ ω)))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (hsum.comp (Filter.tendsto_map (f := Finset.powerset)))
  refine le_of_tendsto' htend fun Δ ↦ ?_
  have hnn : ∀ i j, 0 ≤ (if i < j then J i j * (t i - t j) ^ 2 else 0) := fun i j ↦ by
    split_ifs
    · exact mul_nonneg (hJ0 i j) (sq_nonneg _)
    · exact le_rfl
  have hpt : ∀ A, β * ((pair φ).hamiltonianTerms Λ (τ'.toFun ω) A +
      (pair φ).hamiltonianTerms Λ (τ'.inv.toFun ω) A -
      2 * (pair φ).hamiltonianTerms Λ ω A) ≤
      pairTerms (fun i j ↦ J i j * (t i - t j) ^ 2) A := by
    intro A
    simp only [hamiltonianTerms_pair]
    rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
    · simp only [pairTerms_pair hij]
      by_cases hd : Disjoint ({i, j} : Finset S) Λ
      · rw [ite_eq_right (not_not.2 hd), ite_eq_right (not_not.2 hd),
          ite_eq_right (not_not.2 hd)]
        simp only [mul_zero, add_zero, sub_zero]
        exact mul_nonneg (hJ0 i j) (sq_nonneg _)
      · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hd, hτ']
        simp only [spinWave_toFun_apply, spinWave_inv_toFun_apply, spin_symm_of_mul_eq hτ hgrp]
        exact pair_spinWave_add_sub_le hτ hgrp hsym hφ hJ hij t (ω i) (ω j)
    · simp only [pairTerms_eq_zero hA, mul_zero, add_zero, sub_zero, le_refl]
  calc ENNReal.ofReal (∑ A ∈ Δ.powerset, β * ((pair φ).hamiltonianTerms Λ (τ'.toFun ω) A +
        (pair φ).hamiltonianTerms Λ (τ'.inv.toFun ω) A -
        2 * (pair φ).hamiltonianTerms Λ ω A))
      ≤ ENNReal.ofReal (∑ A ∈ Δ.powerset, pairTerms (fun i j ↦ J i j * (t i - t j) ^ 2) A) :=
        ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun A _ ↦ hpt A)
    _ = ENNReal.ofReal (∑ i ∈ Δ, ∑ j ∈ Δ, if i < j then J i j * (t i - t j) ^ 2 else 0) := by
        rw [sum_powerset_pairTerms]
    _ ≤ ∑ i ∈ Δ, ∑ j ∈ Δ, ENNReal.ofReal (J i j * (t i - t j) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hnn i j]
        refine Finset.sum_le_sum fun j _ ↦ ?_
        split_ifs
        · exact le_rfl
        · simp
    _ = ∑ p ∈ Δ ×ˢ Δ, ENNReal.ofReal (J p.1 p.2 * (t p.1 - t p.2) ^ 2) :=
        (Finset.sum_product' Δ Δ _).symm
    _ ≤ MerminWagner.dirichletEnergy J t := ENNReal.sum_le_tsum _

/-- **Georgii, Theorem (9.20) (Mermin–Wagner).** Let `S` be a countable linearly ordered site
set with a planar norm (`IsPlanarSiteNorm`; `ℤ²` with the maximum norm is
`isPlanarSiteNorm_int_lex`), `E` standard Borel, `λ` a σ-finite non-zero a priori measure, and
`(τ^u)_{u ∈ ℝ}` a family of `λ`-preserving pure spin transformations with `τ^s τ^t = τ^{s+t}`
(9.18). Let `Φ` be a `(τ^u)`-invariant `λ`-admissible pair potential (9.19) such that

* (i) `u ↦ φ_{ij}(x, τ_j^u y)` is `C²` for all `i < j` and `x, y`;
* (ii) `β ∂²_u φ_{ij}(x, τ_j^u y) ≤ J(i, j)` for a symmetric `J ≥ 0` satisfying the decay
  condition (9.21), `∑_{0 < d(i,j) ≤ n} d(i, j)² J(i, j) ≤ K log n` (`LogDecay`).

Then every `μ ∈ 𝒢(βΦ)` is invariant under every `τ^u`.

The inverse temperature `β` multiplies the Hamiltonian; Georgii's statement is `β = 1`, and
(ii) is read with `β Φ`, so no sign condition on `β` is needed. The proof is Georgii's: the
spin wave `τ̃ = (τ_i^{u r(‖i‖ − N, L)})` (`spinWave`) is a localized version of `τ^u` on
`{‖·‖ ≤ N} ⊇ Δ` within `{‖·‖ < N + L}`, Lemma (9.28) (`hamiltonian_spinWave_add_sub_le`) bounds
`β (H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ − 2 H_Λ)` by `u²` times the Dirichlet energy of the profile, Lemma
(9.33) (`exists_dirichletEnergy_profile_le`) makes the latter at most `1 / (u² + 1)`, and
Proposition (9.3) with `c = C = 1/2` concludes. -/
theorem measurePreserving_of_logDecay [Countable S] [StandardBorelSpace E]
    [IsPotential (pair φ)] [IsSummable (pair φ)] (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((pair φ).boltzmannFactor β))
    (hτ : ∀ u, (τ u).IsPureSpin) (hgrp : ∀ s t, τ s * τ t = τ (s + t))
    (hτν : ∀ u i, MeasurePreserving ((τ u).spin i) ν ν)
    (hsym : ∀ u i j, i < j → ∀ x y, φ i j ((τ u).spin i x) ((τ u).spin j y) = φ i j x y)
    (hφ : ∀ i j, i < j → ∀ x y, ContDiff ℝ 2 fun u ↦ φ i j x ((τ u).spin j y))
    (hJ : ∀ i j, i < j → ∀ x y u,
      β * iteratedDeriv 2 (fun u ↦ φ i j x ((τ u).spin j y)) u ≤ J i j)
    (hJ0 : ∀ i j, 0 ≤ J i j) (hJsymm : ∀ i j, J i j = J j i)
    {nrm : S → ℕ} {d : S → S → ℕ} {c₀ : ℕ} (hgeo : MerminWagner.IsPlanarSiteNorm nrm d c₀)
    {K : ℝ} (hdecay : MerminWagner.LogDecay d J K)
    {μ : Measure (S → E)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair φ) ν β hadm)) (u : ℝ) :
    MeasurePreserving (τ u).toFun μ μ := by
  refine measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion ν β
    hadm (hτν u) ((map_pair_eq_iff φ (hτ u)).2 (hsym u)) (c := 1 / 2) (C := 1 / 2)
    (by norm_num) (by norm_num) ?_ hμ
  intro Δ
  rcases Δ.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · refine ⟨∅, Transformation.id, fun _ ↦ MeasurePreserving.id ν,
      Transformation.isLocalizedVersion_id _ _, fun ω ↦ ?_⟩
    rw [Transformation.id_toFun, Transformation.id_inv_toFun]
    have : (1 : ℝ) / 2 * (pair φ).hamiltonian ∅ ω + (1 - 1 / 2) * (pair φ).hamiltonian ∅ ω -
        (pair φ).hamiltonian ∅ ω = 0 := by ring
    rw [this, mul_zero]
    norm_num
  · have hK : 0 ≤ K := hdecay.nonneg hJ0 i₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Δ.sup nrm := ⟨_, rfl⟩
    obtain ⟨L, hL, hE⟩ := MerminWagner.exists_dirichletEnergy_profile_le hgeo hJ0 hdecay hK
      hJsymm N (C := 1 / (u ^ 2 + 1)) (by positivity)
    obtain ⟨t, ht⟩ : ∃ t : S → ℝ, t = fun i ↦ u * MerminWagner.profile nrm N L i := ⟨_, rfl⟩
    have hfin := hgeo.finite_lt (N + L)
    have htΔ : ∀ i ∈ Δ, t i = u := fun i hi ↦ by
      have hiN : nrm i ≤ N := hN ▸ Finset.le_sup (f := nrm) hi
      rw [ht]
      simp only [MerminWagner.profile_of_le hL hiN, mul_one]
    refine ⟨hfin.toFinset, spinWave τ t, fun i ↦ hτν (t i) i, ?_, fun ω ↦ ?_⟩
    · refine ⟨fun ω i hi ↦ ?_, fun ω i hi ↦ ?_, fun ω i hi ↦ ?_⟩
      · rw [spinWave_toFun_apply, htΔ i hi, (hτ u).toFun_apply]
      · rw [spinWave_inv_toFun_apply, htΔ i hi, (hτ u).inv_toFun_apply]
      · have hi' : N + L ≤ nrm i := by
          rw [hfin.mem_toFinset] at hi
          exact not_lt.1 hi
        have hti : t i = 0 := by
          rw [ht]
          simp only [MerminWagner.profile_of_ge hi', mul_zero]
        rw [spinWave_toFun_apply, hti, spin_zero_of_mul_eq hτ hgrp]
    · have h28 := hamiltonian_spinWave_add_sub_le hτ hgrp hsym hφ hJ hJ0 t hfin.toFinset ω
      have hD : MerminWagner.dirichletEnergy J t =
          ENNReal.ofReal (u ^ 2) *
            MerminWagner.dirichletEnergy J (MerminWagner.profile nrm N L) := by
        rw [ht, MerminWagner.dirichletEnergy_const_mul]
      rw [hD] at h28
      have hu : ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (1 / (u ^ 2 + 1)) ≤ 1 := by
        rw [← ENNReal.ofReal_mul (sq_nonneg u)]
        refine ENNReal.ofReal_le_one.2 ?_
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
      have hE' : ENNReal.ofReal (u ^ 2) *
          MerminWagner.dirichletEnergy J (MerminWagner.profile nrm N L) ≤
          ENNReal.ofReal (u ^ 2) * ENNReal.ofReal (1 / (u ^ 2 + 1)) := by gcongr
      have key := ENNReal.ofReal_le_one.1 (h28.trans (hE'.trans hu))
      linarith

/-- **Georgii, Theorem (9.20)** on `S = ℤ²` (as `ℤ ×ₗ ℤ`, with the maximum norm and its
distance `intLexDist`). -/
theorem measurePreserving_of_logDecay_int_lex [StandardBorelSpace E]
    {φ : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → E → E → ℝ} [IsPotential (pair φ)] [IsSummable (pair φ)]
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] {β : ℝ}
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ ×ₗ ℤ) (E := E) ν
      ((pair φ).boltzmannFactor β))
    {τ : ℝ → Transformation (ℤ ×ₗ ℤ) E} (hτ : ∀ u, (τ u).IsPureSpin)
    (hgrp : ∀ s t, τ s * τ t = τ (s + t)) (hτν : ∀ u i, MeasurePreserving ((τ u).spin i) ν ν)
    (hsym : ∀ u i j, i < j → ∀ x y, φ i j ((τ u).spin i x) ((τ u).spin j y) = φ i j x y)
    (hφ : ∀ i j, i < j → ∀ x y, ContDiff ℝ 2 fun u ↦ φ i j x ((τ u).spin j y))
    {J : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ} (hJ : ∀ i j, i < j → ∀ x y u,
      β * iteratedDeriv 2 (fun u ↦ φ i j x ((τ u).spin j y)) u ≤ J i j)
    (hJ0 : ∀ i j, 0 ≤ J i j) (hJsymm : ∀ i j, J i j = J j i)
    {K : ℝ} (hdecay : MerminWagner.LogDecay MerminWagner.intLexDist J K)
    {μ : Measure (ℤ ×ₗ ℤ → E)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair φ) ν β hadm)) (u : ℝ) :
    MeasurePreserving (τ u).toFun μ μ :=
  measurePreserving_of_logDecay ν hadm hτ hgrp hτν hsym hφ hJ hJ0 hJsymm
    MerminWagner.isPlanarSiteNorm_int_lex hdecay hμ u

end PairPotential

end MeasureTheory.GibbsMeasure

end

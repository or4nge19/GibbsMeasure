/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLawPhaseTransition

/-!
# Georgii §11.3: Kalikow's example of phase transition

State space `E = ℤ₊ = ℕ`, sites `ℤ`. Fix `0 < q < p < 1` and put, as in Georgii (11.34),
`a = p(1-p)(1-q)/(p-q)`, `b = q(1-p)(1-q)/(p-q)`, `c = a - b = (1-p)(1-q)`; then `a/b = p/q` and
`a(1-p)⁻¹ - b(1-q)⁻¹ = 1`. Georgii's vector (11.35) is `α(x) = a p^x - b q^x`, a strictly
positive probability vector on `ℕ` satisfying the recursion (11.36) `α(0) = c`,
`α(x+1) = p α(x) + c q^{x+1}`, and his matrix (11.37) is

`Q(x, y) = [p δ_{x-1}(y) + c q^x] α(y) / α(x)`.

`Q` is positive and stochastic with invariant vector `α`, and Kalikow's discovery is the
non-trivial entrance law (11.38): with `s = q/p ∈ (0, 1)`,

`α_i = α` for `i ≥ 1`, `α_i = (1 - s^{1-i}) δ_{-i} + s^{1-i} α` for `i ≤ 0`,

which satisfies `α_i Q = α_{i+1}` and reaches equilibrium in finite time.

## Main declarations

* `alpha`, `alpha_zero`, `alpha_succ`, `alpha_pos`, `tsum_alpha`, `alpha_eq` — **Georgii
  (11.34)–(11.36)**: `α` is a strictly positive probability vector satisfying the recursion, and
  `α(x) = c(p^{x+1} - q^{x+1})/(p-q)`.
* `matrixReal`, `matrix` — **Georgii (11.37)**; `matrixReal_pos`, `tsum_matrixReal`
  (`Q` is positive and stochastic), `matrixReal_zero` (`Q(0, ·) = α`),
  `tsum_alpha_mul_matrixReal` (`α Q = α`), `isTransferMatrix` (Georgii (11.1)).
* `entranceNat`, `entranceReal`, `entrance` — **Georgii (11.38)**; `sRatio_key_one`,
  `sRatio_key_two` are the two algebraic identities behind Georgii's computation,
  `tsum_entranceNat_mul_matrixReal` is `α_{-n} Q = (1 - s^n) δ_{n-1} + s^n α`, and
  `tsum_entranceReal_mul_matrixReal` / `isEntranceLaw` is `α_i Q = α_{i+1}` for all `i ∈ ℤ`.
* `isBoundaryLaw`, `chain`, `isGibbsMeasure_chain` — Georgii's `μ_0 ∈ 𝒢(Q)` via Theorem
  (11.9)(a).
* `not_mem_invariantG_chain`, `injective_map_shift_chain`, `infinite_extremePoints_G` —
  **the phase transition**: `μ_0` is not shift invariant (its one-site marginals at the sites `0`
  and `1` differ by `(1-s)(1-c) > 0`), its translates are pairwise distinct, and `ex 𝒢(γ^Q)` is
  infinite. This is the conclusion `|ex 𝒢(Q)| = ∞` that Georgii draws from Corollary (11.14)(b)
  before Theorem (11.39).
* `powNumer`, `matrixRealPow`, `matrixRealPow_zero`, `tsum_powNumer_mul`,
  `tsum_matrixRealPow_mul_matrixReal`, `matrix_pow_apply_singleton` — **Step 1 in the proof of
  Theorem (11.39)**: `Q^{n+1}(x, y) = [p^{n+1} δ_{x-n-1}(y) + q^{(x-n) ∨ 0} α(x ∧ n)] α(y)/α(x)`,
  by induction on `n`, the algebraic input being `c p^{n+1} + q α(n) = α(n+1)`
  (`cCoeff_mul_pow_succ_add_q_mul_alpha`, from `a q = b p`), `p + c (1-q)⁻¹ = 1`
  (`p_mul_one_sub_q_add_cCoeff`) and `pow_mul_alpha_min_succ`.

The **full classification** `ex 𝒢(Q) = {μ_Q} ∪ {μ_j : j ∈ ℤ}` of Theorem (11.39), and with it the
extreme decomposition directed by `Z = lim_{i → -∞}(σ_i + i)`, is **not** formalised. What is
missing is not Step 1 (above) but Georgii's Steps 2 and 3: Step 2 needs the *quantitative* half of
Theorem (11.9)(c), the limit formulas `ℓ_i/ℓ_0(0) = lim_n Q^{n+i}(x_n, ·)/Q^n(x_n, 0)` and
`r_i/r_0(0) = lim_n Q^{n-i}(·, y_n)/Q^n(0, y_n)` for the boundary law of an extreme Gibbs measure
— `exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints`
(`GibbsMeasure/Model/BoundaryLawUniqueness.lean`) supplies the boundary law but not these formulas
— and Step 3 needs a Borel–Cantelli argument for `Z` under each extreme element together with the
extreme decomposition theorem (7.26).
* `invariantG_eq_singleton` — `𝒢_Θ(Q) = {μ_Q}` (Theorem (11.13) for this `Q`), and
  `chain_intervalCylinder_eq` — `μ_0 = μ_Q` on the cylinders in `]0, ∞[`, Georgii's one-sided
  shift invariance of `μ_0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov.Kalikow

/-! ## Georgii (11.34)–(11.36): the vector `α` -/

section Real

variable (p q : ℝ)

/-- Georgii (11.34): `a = p(1-p)(1-q)/(p-q)`. -/
def aCoeff : ℝ := p * (1 - p) * (1 - q) / (p - q)

/-- Georgii (11.34): `b = q(1-p)(1-q)/(p-q)`. -/
def bCoeff : ℝ := q * (1 - p) * (1 - q) / (p - q)

/-- Georgii (11.34): `c = a - b = (1-p)(1-q)`. -/
def cCoeff : ℝ := (1 - p) * (1 - q)

/-- Georgii's `s = q/p`, the ratio governing the entrance law (11.38). -/
def sRatio : ℝ := q / p

/-- **Georgii (11.35).** `α(x) = a p^x - b q^x`. -/
def alpha (x : ℕ) : ℝ := aCoeff p q * p ^ x - bCoeff p q * q ^ x

variable {p q} (hq : 0 < q) (hqp : q < p) (hp : p < 1)
include hq hqp hp

omit hq in
lemma q_lt_one : q < 1 := hqp.trans hp

omit hp in
lemma p_pos : 0 < p := hq.trans hqp

omit hq hp in
lemma sub_pos' : 0 < p - q := sub_pos.2 hqp

omit hq in
lemma cCoeff_pos : 0 < cCoeff p q :=
  mul_pos (by linarith) (by linarith [q_lt_one hqp hp])

lemma aCoeff_pos : 0 < aCoeff p q :=
  div_pos (mul_pos (mul_pos (p_pos hq hqp) (by linarith)) (by linarith [q_lt_one hqp hp]))
    (sub_pos' hqp)

lemma bCoeff_pos : 0 < bCoeff p q :=
  div_pos (mul_pos (mul_pos hq (by linarith)) (by linarith [q_lt_one hqp hp])) (sub_pos' hqp)

omit hq hp in
/-- `a - b = c`, the first half of Georgii (11.34). -/
lemma aCoeff_sub_bCoeff : aCoeff p q - bCoeff p q = cCoeff p q := by
  have h : p - q ≠ 0 := (sub_pos' hqp).ne'
  simp only [aCoeff, bCoeff, cCoeff]
  field_simp

omit hp in
/-- `a q = b p`, i.e. `a / b = p / q`, the second half of Georgii (11.34). -/
lemma aCoeff_mul_q : aCoeff p q * q = bCoeff p q * p := by
  have h : p - q ≠ 0 := (sub_pos' hqp).ne'
  simp only [aCoeff, bCoeff]
  field_simp

omit hq hp in
/-- **Georgii (11.36).** `α(0) = c`. -/
lemma alpha_zero : alpha p q 0 = cCoeff p q := by
  simp only [alpha, pow_zero, mul_one]
  exact aCoeff_sub_bCoeff hqp

omit hp in
/-- **Georgii (11.36).** `α(x+1) = p α(x) + c q^{x+1}`. -/
lemma alpha_succ (x : ℕ) : alpha p q (x + 1) = p * alpha p q x + cCoeff p q * q ^ (x + 1) := by
  have hab := aCoeff_mul_q hq hqp
  have hc := aCoeff_sub_bCoeff hqp
  simp only [alpha, ← hc, pow_succ]
  linear_combination (-(q ^ x) : ℝ) * hab

/-- `α` is strictly positive (Georgii's third expression `α(x) = c ∑_{k≤x} p^k q^{x-k}`). -/
lemma alpha_pos (x : ℕ) : 0 < alpha p q x := by
  induction x with
  | zero => rw [alpha_zero hqp]; exact cCoeff_pos hqp hp
  | succ n ih =>
      rw [alpha_succ hq hqp]
      have h1 : 0 < p * alpha p q n := mul_pos (p_pos hq hqp) ih
      have h2 : 0 < cCoeff p q * q ^ (n + 1) :=
        mul_pos (cCoeff_pos hqp hp) (pow_pos hq _)
      linarith

lemma summable_alpha : Summable (alpha p q) :=
  Summable.sub (Summable.mul_left _ (summable_geometric_of_lt_one (p_pos hq hqp).le hp))
    (Summable.mul_left _ (summable_geometric_of_lt_one hq.le (q_lt_one hqp hp)))

/-- `α` is a probability vector: the second requirement in Georgii (11.34). -/
lemma tsum_alpha : ∑' x : ℕ, alpha p q x = 1 := by
  have hp0 : (0 : ℝ) ≤ p := (p_pos hq hqp).le
  have hq1 : q < 1 := q_lt_one hqp hp
  have hsp : Summable (fun x : ℕ ↦ p ^ x) := summable_geometric_of_lt_one hp0 hp
  have hsq : Summable (fun x : ℕ ↦ q ^ x) := summable_geometric_of_lt_one hq.le hq1
  have key : aCoeff p q * (1 - p)⁻¹ - bCoeff p q * (1 - q)⁻¹ = 1 := by
    have h1p : (1 : ℝ) - p ≠ 0 := by linarith
    have h1q : (1 : ℝ) - q ≠ 0 := by linarith
    have hpq : p - q ≠ 0 := (sub_pos' hqp).ne'
    simp only [aCoeff, bCoeff]
    field_simp
    ring
  calc ∑' x : ℕ, alpha p q x
      = ∑' x : ℕ, (aCoeff p q * p ^ x - bCoeff p q * q ^ x) := rfl
    _ = (∑' x : ℕ, aCoeff p q * p ^ x) - ∑' x : ℕ, bCoeff p q * q ^ x :=
        Summable.tsum_sub (hsp.mul_left _) (hsq.mul_left _)
    _ = aCoeff p q * (1 - p)⁻¹ - bCoeff p q * (1 - q)⁻¹ := by
        rw [hsp.tsum_mul_left, hsq.tsum_mul_left, tsum_geometric_of_lt_one hp0 hp,
          tsum_geometric_of_lt_one hq.le hq1]
    _ = 1 := key

/-! ## Georgii (11.37): the matrix `Q` -/

omit hq hp in
/-- Georgii's second expression for `α` in (11.35): `α(x) = c (p^{x+1} - q^{x+1})/(p-q)`. -/
lemma alpha_eq (x : ℕ) :
    alpha p q x = cCoeff p q * (p ^ (x + 1) - q ^ (x + 1)) / (p - q) := by
  have h : p - q ≠ 0 := (sub_pos' hqp).ne'
  simp only [alpha, aCoeff, bCoeff, cCoeff, pow_succ]
  field_simp

lemma alpha_ne_zero (x : ℕ) : alpha p q x ≠ 0 := (alpha_pos hq hqp hp x).ne'

/-- **Georgii (11.37).** `Q(x, y) = [p δ_{x-1}(y) + c q^x] α(y) / α(x)`. -/
def matrixReal (p q : ℝ) (x y : ℕ) : ℝ :=
  ((if x = y + 1 then p else 0) + cCoeff p q * q ^ x) * alpha p q y / alpha p q x

/-- `Q(x, y)` split into its two summands, each a constant multiple of `α(y)`. -/
lemma matrixReal_eq (x y : ℕ) :
    matrixReal p q x y = (if x = y + 1 then p / alpha p q x * alpha p q y else 0)
      + cCoeff p q * q ^ x / alpha p q x * alpha p q y := by
  have h := alpha_ne_zero hq hqp hp x
  simp only [matrixReal]
  split_ifs <;> (field_simp; try ring)

/-- `Q(0, ·) = α`, since `α(0) = c` and `δ_{-1}` vanishes on `ℕ`. -/
lemma matrixReal_zero (y : ℕ) : matrixReal p q 0 y = alpha p q y := by
  have h := alpha_ne_zero hq hqp hp 0
  have h0 : alpha p q 0 = cCoeff p q := alpha_zero hqp
  have hc := (cCoeff_pos hqp hp (p := p) (q := q)).ne'
  have hne : ¬ ((0 : ℕ) = y + 1) := by omega
  simp only [matrixReal, pow_zero, mul_one, h0, hne, ite_false, zero_add]
  field_simp

/-- `Q` is strictly positive: Georgii's `Q` at (11.37) is a positive matrix. -/
lemma matrixReal_pos (x y : ℕ) : 0 < matrixReal p q x y := by
  have hx := alpha_pos hq hqp hp x
  have hy := alpha_pos hq hqp hp y
  have hc := cCoeff_pos hqp hp (p := p) (q := q)
  have hnum : 0 < (if x = y + 1 then p else 0) + cCoeff p q * q ^ x := by
    have : 0 < cCoeff p q * q ^ x := mul_pos hc (pow_pos hq _)
    split_ifs with h
    · linarith [p_pos hq hqp]
    · linarith
  exact div_pos (mul_pos hnum hy) hx

lemma summable_matrixReal (x : ℕ) : Summable fun y ↦ matrixReal p q x y := by
  simp only [matrixReal_eq hq hqp hp]
  refine Summable.add ?_ ((summable_alpha hq hqp hp).mul_left _)
  refine summable_of_ne_finset_zero (s := Finset.range x) fun y hy ↦ ?_
  simp only [Finset.mem_range, not_lt] at hy
  have hne : ¬ (x = y + 1) := by omega
  simp only [hne, ite_false]

/-- **`Q` is stochastic**: `∑_y Q(x, y) = 1`, by the recursion (11.36). -/
lemma tsum_matrixReal (x : ℕ) : ∑' y : ℕ, matrixReal p q x y = 1 := by
  have hx := alpha_ne_zero hq hqp hp x
  have hsa := summable_alpha hq hqp hp
  have hs1 : Summable fun y ↦ (if x = y + 1 then p / alpha p q x * alpha p q y else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range x) fun y hy ↦ ?_
    simp only [Finset.mem_range, not_lt] at hy
    have hne : ¬ (x = y + 1) := by omega
    simp only [hne, ite_false]
  have hs2 : Summable fun y ↦ cCoeff p q * q ^ x / alpha p q x * alpha p q y := hsa.mul_left _
  have h2 : ∑' y, cCoeff p q * q ^ x / alpha p q x * alpha p q y
      = cCoeff p q * q ^ x / alpha p q x := by
    rw [hsa.tsum_mul_left, tsum_alpha hq hqp hp, mul_one]
  simp only [matrixReal_eq hq hqp hp]
  rw [Summable.tsum_add hs1 hs2, h2]
  cases x with
  | zero =>
      have hc := (cCoeff_pos hqp hp (p := p) (q := q)).ne'
      have h1 : ∑' y : ℕ, (if (0 : ℕ) = y + 1 then p / alpha p q 0 * alpha p q y else 0) = 0 := by
        simp
      rw [h1, zero_add, pow_zero, mul_one, alpha_zero hqp]
      field_simp
  | succ n =>
      have hrec := alpha_succ hq hqp (p := p) (q := q) n
      have hA := alpha_ne_zero hq hqp hp (n + 1)
      have h1 : ∑' y : ℕ,
          (if n + 1 = y + 1 then p / alpha p q (n + 1) * alpha p q y else 0)
            = p / alpha p q (n + 1) * alpha p q n := by
        simp
      rw [h1]
      field_simp
      linarith [hrec]

/-- `α(x) Q(x, y) = [p δ_{x-1}(y) + c q^x] α(y)`: the `α(x)` in the denominator of (11.37)
cancels. -/
lemma alpha_mul_matrixReal (x y : ℕ) : alpha p q x * matrixReal p q x y
    = (if x = y + 1 then p * alpha p q y else 0) + cCoeff p q * q ^ x * alpha p q y := by
  have hx := alpha_ne_zero hq hqp hp x
  simp only [matrixReal]
  split_ifs <;> (field_simp; try ring)

/-- **`α Q = α`**: `α` is the equilibrium distribution of Kalikow's matrix. -/
lemma tsum_alpha_mul_matrixReal (y : ℕ) :
    ∑' x : ℕ, alpha p q x * matrixReal p q x y = alpha p q y := by
  have hq1 : q < 1 := q_lt_one hqp hp
  have hgeo : Summable fun x : ℕ ↦ q ^ x := summable_geometric_of_lt_one hq.le hq1
  have hs1 : Summable fun x : ℕ ↦ (if x = y + 1 then p * alpha p q y else 0) := by
    refine summable_of_ne_finset_zero (s := {y + 1}) fun x hx ↦ ?_
    simp only [Finset.mem_singleton] at hx
    simp only [hx, ite_false]
  have hs2 : Summable fun x : ℕ ↦ cCoeff p q * q ^ x * alpha p q y := by
    have : (fun x : ℕ ↦ cCoeff p q * q ^ x * alpha p q y)
        = fun x : ℕ ↦ (cCoeff p q * alpha p q y) * q ^ x := by funext x; ring
    rw [this]; exact hgeo.mul_left _
  have h1 : ∑' x : ℕ, (if x = y + 1 then p * alpha p q y else 0) = p * alpha p q y := by
    simp
  have h2 : ∑' x : ℕ, cCoeff p q * q ^ x * alpha p q y
      = cCoeff p q * alpha p q y * (1 - q)⁻¹ := by
    have heq : (fun x : ℕ ↦ cCoeff p q * q ^ x * alpha p q y)
        = fun x : ℕ ↦ (cCoeff p q * alpha p q y) * q ^ x := by funext x; ring
    rw [heq, hgeo.tsum_mul_left, tsum_geometric_of_lt_one hq.le hq1]
  simp only [alpha_mul_matrixReal hq hqp hp]
  rw [Summable.tsum_add hs1 hs2, h1, h2]
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  simp only [cCoeff]
  field_simp
  ring

lemma summable_alpha_mul_matrixReal (y : ℕ) :
    Summable fun x : ℕ ↦ alpha p q x * matrixReal p q x y := by
  have hgeo : Summable fun x : ℕ ↦ q ^ x :=
    summable_geometric_of_lt_one hq.le (q_lt_one hqp hp)
  simp only [alpha_mul_matrixReal hq hqp hp]
  refine Summable.add ?_ ?_
  · refine summable_of_ne_finset_zero (s := {y + 1}) fun x hx ↦ ?_
    simp only [Finset.mem_singleton] at hx
    simp only [hx, ite_false]
  · have heq : (fun x : ℕ ↦ cCoeff p q * q ^ x * alpha p q y)
        = fun x : ℕ ↦ (cCoeff p q * alpha p q y) * q ^ x := by funext x; ring
    rw [heq]; exact hgeo.mul_left _

/-! ## Georgii, Step 1 in the proof of Theorem (11.39): the powers of `Q` -/

omit hq hqp hp in
/-- A `δ`-sum on `ℕ`: `∑_y 1_{x = y + m} f(y) = f(x - m)` if `m ≤ x`, and `0` otherwise. -/
lemma tsum_ite_add_eq (m x : ℕ) (f : ℕ → ℝ) :
    ∑' y : ℕ, (if x = y + m then f y else 0) = if m ≤ x then f (x - m) else 0 := by
  rcases le_or_gt m x with h | h
  · rw [ite_eq_left h]
    refine (tsum_eq_single (x - m) fun y hy ↦ ?_).trans ?_
    · rw [ite_eq_right (by omega)]
    · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (not_le.2 h)]
    have hz : ∀ y : ℕ, (if x = y + m then f y else 0) = 0 := fun y ↦ ite_eq_right (by omega)
    simp [hz]

omit hq hqp hp in
lemma summable_ite_add (m x : ℕ) (f : ℕ → ℝ) :
    Summable fun y : ℕ ↦ (if x = y + m then f y else 0) :=
  summable_of_ne_finset_zero (s := {x - m}) fun y hy ↦ by
    simp only [Finset.mem_singleton] at hy
    exact ite_eq_right (by omega)

omit hq hqp hp in
lemma summable_ite_eq_const (b : ℕ) (c : ℝ) :
    Summable fun y : ℕ ↦ (if y = b then c else 0) :=
  summable_of_ne_finset_zero (s := {b}) fun y hy ↦
    ite_eq_right (by simpa using hy)

omit hp in
/-- `c p^{n+1} + q α(n) = α(n+1)`: the identity behind Georgii's induction step, a consequence of
`a q = b p` in (11.34). -/
lemma cCoeff_mul_pow_succ_add_q_mul_alpha (n : ℕ) :
    cCoeff p q * p ^ (n + 1) + q * alpha p q n = alpha p q (n + 1) := by
  have hab := aCoeff_mul_q hq hqp (p := p) (q := q)
  have hc := aCoeff_sub_bCoeff hqp (p := p) (q := q)
  simp only [alpha, ← hc, pow_succ]
  linear_combination (p ^ n) * hab

omit hq hqp hp in
/-- `p (1 - q) + c = 1 - q`, i.e. `p + c (1 - q)⁻¹ = 1`, Georgii's `p + c(1-q)^{-1} = 1`. -/
lemma p_mul_one_sub_q_add_cCoeff : p * (1 - q) + cCoeff p q = 1 - q := by
  simp only [cCoeff]; ring

/-- The numerator of Georgii's formula for `Q^{n+1}`:
`A_n(x, y) = p^{n+1} δ_{x-n-1}(y) + q^{(x-n) ∨ 0} α(x ∧ n)`. -/
def powNumer (p q : ℝ) (n x y : ℕ) : ℝ :=
  (if x = y + (n + 1) then p ^ (n + 1) else 0) + q ^ (x - n) * alpha p q (min x n)

/-- **Georgii, Step 1 in the proof of Theorem (11.39).**
`Q^{n+1}(x, y) = [p^{n+1} δ_{x-n-1}(y) + q^{(x-n) ∨ 0} α(x ∧ n)] α(y)/α(x)`. -/
def matrixRealPow (p q : ℝ) (n x y : ℕ) : ℝ :=
  powNumer p q n x y * alpha p q y / alpha p q x

omit hq hp in
lemma matrixRealPow_zero (x y : ℕ) : matrixRealPow p q 0 x y = matrixReal p q x y := by
  simp only [matrixRealPow, powNumer, matrixReal, Nat.zero_add, pow_one, Nat.sub_zero,
    Nat.min_zero, alpha_zero hqp]
  ring

lemma powNumer_nonneg (n x y : ℕ) : 0 ≤ powNumer p q n x y := by
  refine add_nonneg ?_ (mul_nonneg (pow_nonneg hq.le _) (alpha_pos hq hqp hp _).le)
  split_ifs
  · exact pow_nonneg (p_pos hq hqp).le _
  · exact le_rfl

lemma matrixRealPow_nonneg (n x y : ℕ) : 0 ≤ matrixRealPow p q n x y :=
  div_nonneg (mul_nonneg (powNumer_nonneg hq hqp hp n x y) (alpha_pos hq hqp hp y).le)
    (alpha_pos hq hqp hp x).le

omit hp in
/-- Georgii's identity `c p^{n+1} q^{x-n-1} 1_{[0,x]}(n+1) + q^{x-n} α(x ∧ n)
= q^{x-n-1} α(x ∧ (n+1))`, the last equality of his induction step. -/
lemma pow_mul_alpha_min_succ (n x : ℕ) :
    (if n + 1 ≤ x then p ^ (n + 1) * cCoeff p q * q ^ (x - (n + 1)) else 0)
        + q ^ (x - n) * alpha p q (min x n)
      = q ^ (x - (n + 1)) * alpha p q (min x (n + 1)) := by
  rcases le_or_gt (n + 1) x with h | h
  · rw [ite_eq_left h, show min x n = n from min_eq_right (by omega),
      show min x (n + 1) = n + 1 from min_eq_right h,
      show x - n = x - (n + 1) + 1 from by omega, pow_succ,
      ← cCoeff_mul_pow_succ_add_q_mul_alpha hq hqp n]
    ring
  · rw [ite_eq_right (by omega), show min x n = x from min_eq_left (by omega),
      show min x (n + 1) = x from min_eq_left (by omega), show x - n = 0 from by omega,
      show x - (n + 1) = 0 from by omega]
    ring

omit hq hqp hp in
/-- `A_n(x, ·) Q(·, z)` split into its four summands. -/
lemma powNumer_mul_expand (n x z y : ℕ) :
    powNumer p q n x y * ((if y = z + 1 then p else 0) + cCoeff p q * q ^ y)
      = (if x = y + (n + 1) then p ^ (n + 1) * (if y = z + 1 then p else 0) else 0)
        + (if x = y + (n + 1) then p ^ (n + 1) * (cCoeff p q * q ^ y) else 0)
        + (if y = z + 1 then q ^ (x - n) * alpha p q (min x n) * p else 0)
        + q ^ (x - n) * alpha p q (min x n) * cCoeff p q * q ^ y := by
  simp only [powNumer]
  split_ifs <;> ring

lemma summable_powNumer_mul (n x z : ℕ) :
    Summable fun y : ℕ ↦ powNumer p q n x y
      * ((if y = z + 1 then p else 0) + cCoeff p q * q ^ y) := by
  have hgeo : Summable fun y : ℕ ↦ q ^ y :=
    summable_geometric_of_lt_one hq.le (q_lt_one hqp hp)
  simp only [powNumer_mul_expand]
  exact (((summable_ite_add _ _ _).add (summable_ite_add _ _ _)).add
    (summable_ite_eq_const _ _)).add (hgeo.mul_left _)

/-- **Georgii's induction step for Step 1 of Theorem (11.39)**, on the numerators:
`∑_y A_n(x, y) [p δ_{y-1}(z) + c q^y] = A_{n+1}(x, z)`. -/
lemma tsum_powNumer_mul (n x z : ℕ) :
    ∑' y : ℕ, powNumer p q n x y * ((if y = z + 1 then p else 0) + cCoeff p q * q ^ y)
      = powNumer p q (n + 1) x z := by
  have hq1 : q < 1 := q_lt_one hqp hp
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  have hgeo : Summable fun y : ℕ ↦ q ^ y := summable_geometric_of_lt_one hq.le hq1
  have hs1 := summable_ite_add (n + 1) x fun y ↦ p ^ (n + 1) * (if y = z + 1 then p else 0)
  have hs2 := summable_ite_add (n + 1) x fun y ↦ p ^ (n + 1) * (cCoeff p q * q ^ y)
  have hs3 := summable_ite_eq_const (z + 1) (q ^ (x - n) * alpha p q (min x n) * p)
  have hs4 : Summable fun y : ℕ ↦
      q ^ (x - n) * alpha p q (min x n) * cCoeff p q * q ^ y := hgeo.mul_left _
  have h1 : ∑' y : ℕ,
      (if x = y + (n + 1) then p ^ (n + 1) * (if y = z + 1 then p else 0) else 0)
      = if x = z + (n + 1 + 1) then p ^ (n + 1 + 1) else 0 := by
    rw [tsum_ite_add_eq]
    rcases eq_or_ne x (z + (n + 1 + 1)) with hx | hx
    · rw [ite_eq_left (show n + 1 ≤ x by omega), ite_eq_left (show x - (n + 1) = z + 1 by omega),
        ite_eq_left hx]
      ring
    · rw [ite_eq_right hx]
      split_ifs with h h'
      · exact absurd (show x = z + (n + 1 + 1) by omega) hx
      · rw [mul_zero]
      · rfl
  have h2 : ∑' y : ℕ, (if x = y + (n + 1) then p ^ (n + 1) * (cCoeff p q * q ^ y) else 0)
      = if n + 1 ≤ x then p ^ (n + 1) * cCoeff p q * q ^ (x - (n + 1)) else 0 := by
    rw [tsum_ite_add_eq]
    split_ifs
    · ring
    · rfl
  have h3 : ∑' y : ℕ, (if y = z + 1 then q ^ (x - n) * alpha p q (min x n) * p else 0)
      = q ^ (x - n) * alpha p q (min x n) * p := by simp
  have h4 : ∑' y : ℕ, q ^ (x - n) * alpha p q (min x n) * cCoeff p q * q ^ y
      = q ^ (x - n) * alpha p q (min x n) * cCoeff p q * (1 - q)⁻¹ := by
    rw [hgeo.tsum_mul_left, tsum_geometric_of_lt_one hq.le hq1]
  have hone : p + cCoeff p q * (1 - q)⁻¹ = 1 := by
    have hc := p_mul_one_sub_q_add_cCoeff (p := p) (q := q)
    field_simp
    linarith
  have hkey := pow_mul_alpha_min_succ hq hqp n x
  rw [tsum_congr (powNumer_mul_expand n x z), Summable.tsum_add ((hs1.add hs2).add hs3) hs4,
    Summable.tsum_add (hs1.add hs2) hs3, Summable.tsum_add hs1 hs2, h1, h2, h3, h4, powNumer]
  linear_combination hkey + (q ^ (x - n) * alpha p q (min x n)) * hone

lemma matrixRealPow_mul_matrixReal (n x y z : ℕ) :
    matrixRealPow p q n x y * matrixReal p q y z
      = powNumer p q n x y * ((if y = z + 1 then p else 0) + cCoeff p q * q ^ y)
          * (alpha p q z / alpha p q x) := by
  have hax := alpha_ne_zero hq hqp hp x
  have hay := alpha_ne_zero hq hqp hp y
  simp only [matrixRealPow, matrixReal]
  field_simp

lemma summable_matrixRealPow_mul_matrixReal (n x z : ℕ) :
    Summable fun y : ℕ ↦ matrixRealPow p q n x y * matrixReal p q y z := by
  simp only [matrixRealPow_mul_matrixReal hq hqp hp]
  exact (summable_powNumer_mul hq hqp hp n x z).mul_right _

/-- **Georgii's induction step for Step 1 of Theorem (11.39).** `Q^{n+1} Q = Q^{n+2}` in the
explicit form of the formula. -/
lemma tsum_matrixRealPow_mul_matrixReal (n x z : ℕ) :
    ∑' y : ℕ, matrixRealPow p q n x y * matrixReal p q y z = matrixRealPow p q (n + 1) x z := by
  rw [tsum_congr (matrixRealPow_mul_matrixReal hq hqp hp n x · z), tsum_mul_right,
    tsum_powNumer_mul hq hqp hp n x z, matrixRealPow, mul_div_assoc]

/-! ## Georgii (11.38): Kalikow's entrance law -/

omit hp in
lemma sRatio_pos : 0 < sRatio p q := div_pos hq (p_pos hq hqp)

omit hp in
lemma sRatio_lt_one : sRatio p q < 1 := (div_lt_one (p_pos hq hqp)).2 hqp

/-- Georgii (11.38) for `i = -n ≤ 0`: `α_{-n} = (1 - s^{n+1}) δ_n + s^{n+1} α`. -/
def entranceNat (p q : ℝ) (n x : ℕ) : ℝ :=
  (1 - sRatio p q ^ (n + 1)) * (if x = n then 1 else 0) + sRatio p q ^ (n + 1) * alpha p q x

/-- **Georgii (11.38).** `α_i = α` for `i ≥ 1`, and `α_i = (1 - s^{1-i}) δ_{-i} + s^{1-i} α` for
`i ≤ 0`, where `s = q/p`. -/
def entranceReal (p q : ℝ) (i : ℤ) (x : ℕ) : ℝ :=
  if 1 ≤ i then alpha p q x else entranceNat p q (-i).toNat x

omit hp in
lemma sRatio_pow_le_one (n : ℕ) : sRatio p q ^ n ≤ 1 :=
  pow_le_one₀ (sRatio_pos hq hqp).le (sRatio_lt_one hq hqp).le

lemma entranceNat_pos (n x : ℕ) : 0 < entranceNat p q n x := by
  have h1 : 0 ≤ (1 - sRatio p q ^ (n + 1)) * (if x = n then 1 else 0) := by
    have := sRatio_pow_le_one hq hqp (n + 1) (p := p) (q := q)
    have : (0 : ℝ) ≤ 1 - sRatio p q ^ (n + 1) := by linarith
    split_ifs <;> linarith
  have h2 : 0 < sRatio p q ^ (n + 1) * alpha p q x :=
    mul_pos (pow_pos (sRatio_pos hq hqp) _) (alpha_pos hq hqp hp x)
  simp only [entranceNat]
  linarith

lemma entranceReal_pos (i : ℤ) (x : ℕ) : 0 < entranceReal p q i x := by
  simp only [entranceReal]
  split_ifs
  · exact alpha_pos hq hqp hp x
  · exact entranceNat_pos hq hqp hp _ x

lemma summable_entranceNat (n : ℕ) : Summable fun x : ℕ ↦ entranceNat p q n x := by
  simp only [entranceNat]
  refine Summable.add ?_ ((summable_alpha hq hqp hp).mul_left _)
  refine summable_of_ne_finset_zero (s := {n}) fun x hx ↦ ?_
  simp only [Finset.mem_singleton] at hx
  simp only [hx, ite_false, mul_zero]

lemma tsum_entranceNat (n : ℕ) : ∑' x : ℕ, entranceNat p q n x = 1 := by
  simp only [entranceNat]
  rw [Summable.tsum_add ?_ ((summable_alpha hq hqp hp).mul_left _),
    (summable_alpha hq hqp hp).tsum_mul_left, tsum_alpha hq hqp hp, mul_one]
  · rw [show (∑' x : ℕ, (1 - sRatio p q ^ (n + 1)) * (if x = n then 1 else 0))
        = 1 - sRatio p q ^ (n + 1) by simp]
    ring
  · refine summable_of_ne_finset_zero (s := {n}) fun x hx ↦ ?_
    simp only [Finset.mem_singleton] at hx
    simp only [hx, ite_false, mul_zero]

lemma summable_entranceReal (i : ℤ) : Summable fun x : ℕ ↦ entranceReal p q i x := by
  by_cases hi : 1 ≤ i
  · have h : ∀ x : ℕ, entranceReal p q i x = alpha p q x := fun x ↦ by
      simp only [entranceReal, hi, ite_true]
    simp only [h]
    exact summable_alpha hq hqp hp
  · have h : ∀ x : ℕ, entranceReal p q i x = entranceNat p q (-i).toNat x := fun x ↦ by
      simp only [entranceReal, hi, ite_false]
    simp only [h]
    exact summable_entranceNat hq hqp hp _

lemma tsum_entranceReal (i : ℤ) : ∑' x : ℕ, entranceReal p q i x = 1 := by
  simp only [entranceReal]
  split_ifs
  · exact tsum_alpha hq hqp hp
  · exact tsum_entranceNat hq hqp hp _

/-! ### The two algebraic identities behind `α_i Q = α_{i+1}` -/

/-- The identity `(1 - s^{n+1}) c q^n / α(n) + s^{n+1} = s^n` used by Georgii to evaluate the
coefficient of `α` in `α_i Q`. -/
lemma sRatio_key_one (n : ℕ) :
    (1 - sRatio p q ^ (n + 1)) * (cCoeff p q * q ^ n / alpha p q n) + sRatio p q ^ (n + 1)
      = sRatio p q ^ n := by
  have hp0 : p ≠ 0 := (p_pos hq hqp).ne'
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp0
  have hc : cCoeff p q ≠ 0 := (cCoeff_pos hqp hp).ne'
  have hpq : p - q ≠ 0 := (sub_pos' hqp).ne'
  have hlt : q ^ (n + 1) < p ^ (n + 1) := by gcongr
  have hd : p ^ (n + 1) - q ^ (n + 1) ≠ 0 := by intro h; linarith
  rw [alpha_eq hqp n]
  simp only [sRatio, div_pow]
  field_simp
  ring

/-- The identity `(1 - s^{n+2}) p α(n) / α(n+1) = 1 - s^{n+1}` used by Georgii to evaluate the
coefficient of `δ_{-i-1}` in `α_i Q`. -/
lemma sRatio_key_two (m : ℕ) :
    (1 - sRatio p q ^ (m + 1 + 1)) * (p * alpha p q m / alpha p q (m + 1))
      = 1 - sRatio p q ^ (m + 1) := by
  have hp0 : p ≠ 0 := (p_pos hq hqp).ne'
  have hpn : p ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
  have hc : cCoeff p q ≠ 0 := (cCoeff_pos hqp hp).ne'
  have hpq : p - q ≠ 0 := (sub_pos' hqp).ne'
  have hlt : q ^ (m + 1 + 1) < p ^ (m + 1 + 1) := by gcongr
  have hd : p ^ (m + 1 + 1) - q ^ (m + 1 + 1) ≠ 0 := by intro h; linarith
  rw [alpha_eq hqp m, alpha_eq hqp (m + 1)]
  simp only [sRatio, div_pow]
  field_simp
  ring

/-- **Georgii's computation of `α_i Q` for `i ≤ 0`.** With `n = -i`,
`α_{-n} Q = (1 - s^n) δ_{n-1} + s^n α`. -/
lemma tsum_entranceNat_mul_matrixReal (n y : ℕ) :
    ∑' x : ℕ, entranceNat p q n x * matrixReal p q x y
      = (if n = y + 1 then 1 - sRatio p q ^ n else 0) + sRatio p q ^ n * alpha p q y := by
  have hfun : ∀ x : ℕ, entranceNat p q n x * matrixReal p q x y
      = (1 - sRatio p q ^ (n + 1)) * ((if x = n then 1 else 0) * matrixReal p q x y)
        + sRatio p q ^ (n + 1) * (alpha p q x * matrixReal p q x y) := by
    intro x; simp only [entranceNat]; ring
  have hs1 : Summable fun x : ℕ ↦
      (1 - sRatio p q ^ (n + 1)) * ((if x = n then 1 else 0) * matrixReal p q x y) := by
    refine summable_of_ne_finset_zero (s := {n}) fun x hx ↦ ?_
    simp only [Finset.mem_singleton] at hx
    simp only [hx, ite_false, zero_mul, mul_zero]
  have hs2 : Summable fun x : ℕ ↦
      sRatio p q ^ (n + 1) * (alpha p q x * matrixReal p q x y) :=
    (summable_alpha_mul_matrixReal hq hqp hp y).mul_left _
  have h1 : ∑' x : ℕ, (1 - sRatio p q ^ (n + 1)) * ((if x = n then 1 else 0)
      * matrixReal p q x y) = (1 - sRatio p q ^ (n + 1)) * matrixReal p q n y := by simp
  have h2 : ∑' x : ℕ, sRatio p q ^ (n + 1) * (alpha p q x * matrixReal p q x y)
      = sRatio p q ^ (n + 1) * alpha p q y := by
    rw [(summable_alpha_mul_matrixReal hq hqp hp y).tsum_mul_left,
      tsum_alpha_mul_matrixReal hq hqp hp y]
  simp only [hfun]
  rw [Summable.tsum_add hs1 hs2, h1, h2]
  rcases eq_or_ne n (y + 1) with hn | hn
  · subst hn
    have k1 := sRatio_key_one hq hqp hp (y + 1)
    have k2 := sRatio_key_two hq hqp hp y
    have hαn := alpha_ne_zero hq hqp hp (y + 1)
    simp only [matrixReal, ite_true]
    have expand :
        (1 - sRatio p q ^ (y + 1 + 1)) * ((p + cCoeff p q * q ^ (y + 1)) * alpha p q y
              / alpha p q (y + 1))
            + sRatio p q ^ (y + 1 + 1) * alpha p q y
          = (1 - sRatio p q ^ (y + 1 + 1)) * (p * alpha p q y / alpha p q (y + 1))
            + ((1 - sRatio p q ^ (y + 1 + 1))
                * (cCoeff p q * q ^ (y + 1) / alpha p q (y + 1))
              + sRatio p q ^ (y + 1 + 1)) * alpha p q y := by
      field_simp
      ring
    rw [expand, k1, k2]
  · have k1 := sRatio_key_one hq hqp hp n
    have hαn := alpha_ne_zero hq hqp hp n
    simp only [matrixReal, hn, ite_false, zero_add]
    have expand : (1 - sRatio p q ^ (n + 1))
          * (cCoeff p q * q ^ n * alpha p q y / alpha p q n)
          + sRatio p q ^ (n + 1) * alpha p q y
        = ((1 - sRatio p q ^ (n + 1)) * (cCoeff p q * q ^ n / alpha p q n)
            + sRatio p q ^ (n + 1)) * alpha p q y := by
      field_simp
    rw [expand, k1]

lemma summable_entranceNat_mul_matrixReal (n y : ℕ) :
    Summable fun x : ℕ ↦ entranceNat p q n x * matrixReal p q x y := by
  have hfun : ∀ x : ℕ, entranceNat p q n x * matrixReal p q x y
      = (1 - sRatio p q ^ (n + 1)) * ((if x = n then 1 else 0) * matrixReal p q x y)
        + sRatio p q ^ (n + 1) * (alpha p q x * matrixReal p q x y) := by
    intro x; simp only [entranceNat]; ring
  simp only [hfun]
  refine Summable.add ?_ ((summable_alpha_mul_matrixReal hq hqp hp y).mul_left _)
  refine summable_of_ne_finset_zero (s := {n}) fun x hx ↦ ?_
  simp only [Finset.mem_singleton] at hx
  simp only [hx, ite_false, zero_mul, mul_zero]

lemma summable_entranceReal_mul_matrixReal (i : ℤ) (y : ℕ) :
    Summable fun x : ℕ ↦ entranceReal p q i x * matrixReal p q x y := by
  by_cases hi : 1 ≤ i
  · have h : ∀ x : ℕ, entranceReal p q i x = alpha p q x := fun x ↦ by
      simp only [entranceReal, hi, ite_true]
    simp only [h]
    exact summable_alpha_mul_matrixReal hq hqp hp y
  · have h : ∀ x : ℕ, entranceReal p q i x = entranceNat p q (-i).toNat x := fun x ↦ by
      simp only [entranceReal, hi, ite_false]
    simp only [h]
    exact summable_entranceNat_mul_matrixReal hq hqp hp _ y

/-- **Georgii (11.38): `{α_i}` is an entrance law for `Q`,** `α_i Q = α_{i+1}` for all `i ∈ ℤ`. -/
lemma tsum_entranceReal_mul_matrixReal (i : ℤ) (y : ℕ) :
    ∑' x : ℕ, entranceReal p q i x * matrixReal p q x y = entranceReal p q (i + 1) y := by
  by_cases hi : 1 ≤ i
  · have h : ∀ x : ℕ, entranceReal p q i x = alpha p q x := fun x ↦ by
      simp only [entranceReal, hi, ite_true]
    have h' : entranceReal p q (i + 1) y = alpha p q y := by
      simp only [entranceReal, show (1 : ℤ) ≤ i + 1 by omega, ite_true]
    simp only [h, h']
    exact tsum_alpha_mul_matrixReal hq hqp hp y
  · have h : ∀ x : ℕ, entranceReal p q i x = entranceNat p q (-i).toNat x := fun x ↦ by
      simp only [entranceReal, hi, ite_false]
    simp only [h, tsum_entranceNat_mul_matrixReal hq hqp hp]
    by_cases hi1 : 1 ≤ i + 1
    · have hi0 : i = 0 := by omega
      subst hi0
      simp only [entranceReal, hi1, ite_true, neg_zero, Int.toNat_zero, pow_zero, one_mul]
      simp
    · have h' : entranceReal p q (i + 1) y = entranceNat p q (-(i + 1)).toNat y := by
        simp only [entranceReal, hi1, ite_false]
      have hn : ((-i).toNat) = (-(i + 1)).toNat + 1 := by omega
      rw [h', hn]
      simp only [entranceNat]
      congr 1
      split_ifs with h1 h2 h2
      · rw [mul_one]
      · omega
      · omega
      · rw [mul_zero]

end Real

/-! ## Kalikow's matrix as a transfer matrix on `E = ℤ₊`, and the phase transition -/

section Transfer

/-- **Georgii (11.37)** as an `ℝ≥0∞`-valued matrix on the state space `E = ℤ₊ = ℕ`. -/
def matrix (p q : ℝ) (x y : ℕ) : ℝ≥0∞ := ENNReal.ofReal (matrixReal p q x y)

/-- **Georgii (11.35)** as an `ℝ≥0∞`-valued probability vector on `E = ℤ₊ = ℕ`. -/
def stationary (p q : ℝ) (x : ℕ) : ℝ≥0∞ := ENNReal.ofReal (alpha p q x)

/-- **Georgii (11.38)** as an `ℝ≥0∞`-valued entrance law. -/
def entrance (p q : ℝ) (i : ℤ) (x : ℕ) : ℝ≥0∞ := ENNReal.ofReal (entranceReal p q i x)

variable {p q : ℝ} (hq : 0 < q) (hqp : q < p) (hp : p < 1)
include hq hqp hp

lemma matrix_pos (x y : ℕ) : 0 < matrix p q x y :=
  ENNReal.ofReal_pos.2 (matrixReal_pos hq hqp hp x y)

lemma tsum_matrix (x : ℕ) : ∑' y : ℕ, matrix p q x y = 1 := by
  simp only [matrix]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ (matrixReal_pos hq hqp hp x y).le)
    (summable_matrixReal hq hqp hp x), tsum_matrixReal hq hqp hp x, ENNReal.ofReal_one]

/-- Kalikow's `Q` is a transfer matrix in the sense of Georgii (11.1): it is positive, and its
powers are finite because it is stochastic. -/
lemma isTransferMatrix : IsTransferMatrix (matrix p q) :=
  isTransferMatrix_of_stochastic (matrix_pos hq hqp hp) (tsum_matrix hq hqp hp)

lemma stationary_pos (x : ℕ) : 0 < stationary p q x :=
  ENNReal.ofReal_pos.2 (alpha_pos hq hqp hp x)

omit hq hqp hp in
lemma stationary_ne_top (x : ℕ) : stationary p q x ≠ ⊤ := ENNReal.ofReal_ne_top

lemma tsum_stationary : ∑' x : ℕ, stationary p q x = 1 := by
  simp only [stationary]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ (alpha_pos hq hqp hp x).le)
    (summable_alpha hq hqp hp), tsum_alpha hq hqp hp, ENNReal.ofReal_one]

/-- **`α Q = α`** in `ℝ≥0∞`. -/
lemma tsum_stationary_mul_matrix (y : ℕ) :
    ∑' x : ℕ, stationary p q x * matrix p q x y = stationary p q y := by
  have hmul : ∀ x : ℕ, stationary p q x * matrix p q x y
      = ENNReal.ofReal (alpha p q x * matrixReal p q x y) := fun x ↦
    (ENNReal.ofReal_mul (alpha_pos hq hqp hp x).le).symm
  simp only [hmul]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun x ↦ mul_nonneg (alpha_pos hq hqp hp x).le (matrixReal_pos hq hqp hp x y).le)
      (summable_alpha_mul_matrixReal hq hqp hp y),
    tsum_alpha_mul_matrixReal hq hqp hp y]
  rfl

/-- **Georgii (11.38).** Kalikow's `{α_i}` is an entrance law for `Q` in the sense of
`IsEntranceLaw`. -/
theorem isEntranceLaw : IsEntranceLaw (matrix p q) (entrance p q) where
  pos i x := ENNReal.ofReal_pos.2 (entranceReal_pos hq hqp hp i x)
  tsum_eq_one i := by
    simp only [entrance]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun x ↦ (entranceReal_pos hq hqp hp i x).le)
      (summable_entranceReal hq hqp hp i), tsum_entranceReal hq hqp hp i, ENNReal.ofReal_one]
  step i y := by
    have hmul : ∀ x : ℕ, entrance p q i x * matrix p q x y
        = ENNReal.ofReal (entranceReal p q i x * matrixReal p q x y) := fun x ↦
      (ENNReal.ofReal_mul (entranceReal_pos hq hqp hp i x).le).symm
    simp only [hmul]
    rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun x ↦ mul_nonneg (entranceReal_pos hq hqp hp i x).le
          (matrixReal_pos hq hqp hp x y).le)
        (summable_entranceReal_mul_matrixReal hq hqp hp i y),
      tsum_entranceReal_mul_matrixReal hq hqp hp i y]
    rfl

/-- **Georgii (11.38) as a boundary law.** `{α_i, 1}` is a boundary law for Kalikow's `Q`. -/
theorem isBoundaryLaw : IsBoundaryLaw (matrix p q) (entrance p q) (fun _ _ ↦ 1) :=
  (isEntranceLaw hq hqp hp).isBoundaryLaw (tsum_matrix hq hqp hp)

/-- Georgii's `μ_0`: the Markov chain for `Q` defined by the entrance law (11.38) through
(11.10). -/
def chain : Measure (ℤ → ℕ) := boundaryLawMeasure (isBoundaryLaw hq hqp hp)

instance isProbabilityMeasure_chain : IsProbabilityMeasure (chain hq hqp hp) :=
  inferInstanceAs (IsProbabilityMeasure (boundaryLawMeasure (isBoundaryLaw hq hqp hp)))

/-- `μ_0 ∈ 𝒢(Q)`: Theorem (11.9)(a). -/
theorem isGibbsMeasure_chain :
    (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)).IsGibbsMeasure
      (chain hq hqp hp) :=
  isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _

omit hp in
/-- The one-site marginals of `μ_0` at the sites `0` and `1` differ: `α_0(0) = 1 - s + sc` while
`α_1(0) = α(0) = c`, and `(1-s)(1-c) > 0`. -/
theorem entranceReal_one_lt_entranceReal_zero (hc : cCoeff p q < 1) :
    entranceReal p q 1 0 < entranceReal p q 0 0 := by
  have hs : sRatio p q < 1 := sRatio_lt_one hq hqp
  have h1 : entranceReal p q 1 0 = alpha p q 0 := by
    simp only [entranceReal, show (1 : ℤ) ≤ 1 from le_rfl, ite_true]
  have h0 : entranceReal p q 0 0
      = (1 - sRatio p q) * 1 + sRatio p q * alpha p q 0 := by
    simp only [entranceReal, show ¬ ((1 : ℤ) ≤ 0) by omega, ite_false, neg_zero,
      Int.toNat_zero, entranceNat]
    norm_num
  rw [h1, h0, alpha_zero hqp]
  nlinarith [hs, hc]

/-- `c = (1-p)(1-q) < 1`. -/
lemma cCoeff_lt_one : cCoeff p q < 1 := by
  have hq1 : q < 1 := q_lt_one hqp hp
  have hp0 : 0 < p := p_pos hq hqp
  simp only [cCoeff]
  nlinarith

/-- **Kalikow's phase transition, Georgii §11.3.** `μ_0` is a Gibbs measure for `γ^Q` that is not
shift invariant; consequently `ex 𝒢(γ^Q)` is infinite. -/
theorem entrance_zero_ne_entrance_one :
    entrance p q 0 0 * 1 ≠ entrance p q 1 0 * 1 := by
  have hlt : entranceReal p q 1 0 < entranceReal p q 0 0 :=
    entranceReal_one_lt_entranceReal_zero hq hqp (cCoeff_lt_one hq hqp hp)
  have : ENNReal.ofReal (entranceReal p q 1 0) < ENNReal.ofReal (entranceReal p q 0 0) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (entranceReal_pos hq hqp hp 1 0).le).2 hlt
  simpa only [mul_one, entrance] using this.ne'

theorem not_mem_invariantG_chain :
    chain hq hqp hp ∉ invariantG
      (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)) (shiftGroup ℤ ℕ) :=
  not_mem_invariantG_boundaryLawMeasure_of_marginal_ne (i := 0) (j := 1) (x := 0)
    (isBoundaryLaw hq hqp hp) (isTransferMatrix hq hqp hp)
    (entrance_zero_ne_entrance_one hq hqp hp)

/-- **Kalikow's phase transition (Georgii §11.3, the conclusion `|ex 𝒢(Q)| = ∞` of Theorem
(11.39)).** -/
theorem infinite_extremePoints_G :
    ((G (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))).extremePoints
      ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_of_exists_not_mem_invariantG _ _
    ⟨inferInstance, isGibbsMeasure_chain hq hqp hp⟩ (not_mem_invariantG_chain hq hqp hp)

/-- **Georgii, before (11.39).** The translates `θ_j(μ_0)`, `j ∈ ℤ`, are pairwise distinct. -/
theorem injective_map_shift_chain :
    Function.Injective fun j : ℤ ↦ (chain hq hqp hp).map (shift ℕ j).toFun :=
  injective_map_shift_of_not_mem_invariantG _ (isTransferMatrix hq hqp hp)
    ⟨inferInstance, isGibbsMeasure_chain hq hqp hp⟩ (not_mem_invariantG_chain hq hqp hp)

/-- **Georgii, before (11.39).** `α` is an invariant probability vector of the stochastic `Q`, so
Theorem (11.13) gives `𝒢_Θ(Q) = {μ_Q}`, where `μ_Q` is the measure (11.10) of the constant
boundary law `ℓ_i = α`, `r_i = 1`. -/
theorem invariantG_eq_singleton :
    invariantG (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp))
        (shiftGroup ℤ ℕ)
      = {boundaryLawMeasure (isBoundaryLaw_const (tsum_matrix hq hqp hp)
          (stationary_pos hq hqp hp) (stationary_ne_top (p := p) (q := q))
          (tsum_stationary hq hqp hp) (tsum_stationary_mul_matrix hq hqp hp))} :=
  invariantG_eq_singleton_boundaryLawMeasure_const _ (isTransferMatrix hq hqp hp)
    (matrix_pos hq hqp hp) (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
    (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
    (tsum_stationary_mul_matrix hq hqp hp) rfl

/-- **Georgii, before (11.39): `μ_0 = μ_Q` on `𝓕_{]0,∞[}`.** The entrance law reaches equilibrium
at time `1`, so `μ_0` and `μ_Q` agree on every cylinder `{σ_a = x_a, …, σ_b = x_b}` with
`1 ≤ a ≤ b`. -/
theorem chain_intervalCylinder_eq {a b : ℤ} (ha : 1 ≤ a) (hab : a ≤ b) (σ : ℤ → ℕ) :
    chain hq hqp hp (intervalCylinder a b σ)
      = boundaryLawMeasure (isBoundaryLaw_const (tsum_matrix hq hqp hp)
          (stationary_pos hq hqp hp) (stationary_ne_top (p := p) (q := q))
          (tsum_stationary hq hqp hp) (tsum_stationary_mul_matrix hq hqp hp))
        (intervalCylinder a b σ) := by
  rw [chain, IsBoundaryLaw.boundaryLawMeasure_intervalCylinder _ hab,
    IsBoundaryLaw.boundaryLawMeasure_intervalCylinder _ hab]
  congr 1
  congr 1
  simp only [entrance, entranceReal, ha, ite_true, stationary]

/-- **Georgii, Step 1 in the proof of Theorem (11.39).** The entries of the powers of Kalikow's
`Q`: `Q^{n+1}(x, y) = [p^{n+1} δ_{x-n-1}(y) + q^{(x-n) ∨ 0} α(x ∧ n)] α(y)/α(x)`. -/
theorem matrix_pow_apply_singleton (n x y : ℕ) :
    (Kernel.ofMatrix (matrix p q) ^ (n + 1)) x {y} = ENNReal.ofReal (matrixRealPow p q n x y) := by
  induction n generalizing y with
  | zero =>
      rw [zero_add, pow_one, Kernel.ofMatrix_apply_singleton, matrix, matrixRealPow_zero hqp]
  | succ n ih =>
      have hmul : ∀ w : ℕ, (Kernel.ofMatrix (matrix p q) ^ (n + 1)) x {w} * matrix p q w y
          = ENNReal.ofReal (matrixRealPow p q n x w * matrixReal p q w y) := fun w ↦ by
        rw [ih w, matrix, ← ENNReal.ofReal_mul (matrixRealPow_nonneg hq hqp hp n x w)]
      rw [Kernel.ofMatrix_pow_succ'_apply_singleton]
      simp only [hmul]
      rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun w ↦ mul_nonneg (matrixRealPow_nonneg hq hqp hp n x w)
            (matrixReal_pos hq hqp hp w y).le)
          (summable_matrixRealPow_mul_matrixReal hq hqp hp n x y),
        tsum_matrixRealPow_mul_matrixReal hq hqp hp n x y]

end Transfer








end MeasureTheory.GibbsMeasure.Markov.Kalikow

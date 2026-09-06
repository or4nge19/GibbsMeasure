/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLawPhaseTransition
public import GibbsMeasure.Model.BoundaryLawLimits
public import GibbsMeasure.Mathlib.Data.ENNReal.DivRatio

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

**Theorem (11.39)** — `ex 𝒢(Q) = {μ_Q} ∪ {μ_j : j ∈ ℤ}`, the almost-sure existence of
`Z = lim_{i → -∞}(σ_i + i) ∈ {-∞} ∪ ℤ` under every `μ ∈ 𝒢(Q)`, the extreme decomposition
`μ = μ(Z = -∞) μ_Q + ∑_j μ(Z = j) μ_j`, and "each `μ ∈ 𝒢(Q)` is a Markov chain" — is proved in
full: Steps 1 and 2 are in this file, Step 3 and the conclusion in
`GibbsMeasure/Model/KalikowClassification.lean`.

* `invariantChain` (Georgii's `μ_Q`, the measure of the constant boundary law `α`, `1`),
  `shiftedChain j` (his `μ_j = θ_j(μ_0)`), `shiftedChain_eq_boundaryLawMeasure` (the boundary
  law of `μ_j` is `ℓ_i = α_{i-j}`, `r_i = 1`), and the one-site marginals
  `invariantChain_preimage_singleton`, `shiftedChain_preimage_singleton`.
* **Step 2** (`exists_eq_of_mem_extremePoints`): every `μ ∈ ex 𝒢(Q)` is `μ_Q` or some `μ_j`.
  Theorem (11.9)(c) (`exists_isBoundaryLaw_and_tendsto_of_mem_extremePoints`,
  `GibbsMeasure/Model/BoundaryLawLimits.lean`) represents `μ` by a boundary law `{ℓ_i, r_i}`
  together with the limit formulas (11.40), (11.41) along sequences `(x_n)`, `(y_n)`. Georgii's
  "there is no loss in assuming `r_0(0) = 1`" is replaced by proving `r ≡ r_0(0)` outright
  (`right_eq_of_tendsto`: by Step 1 the ratios `Q^{n-i}(x, y_n)/Q^n(0, y_n)` of (11.41) equal
  `1` for large `n`), so that `∑_y ℓ_i(y) = r_0(0)⁻¹`. The ratios of entries of powers of `Q`
  fall into three regimes (`matrixRealPow_div_of_lt`, `matrixRealPow_div_of_le`,
  `matrixRealPow_div_of_eq`, with the asymptotics `α(k) ∼ a p^k` in `tendsto_alpha_div_pow`),
  and `forall_frequently_lt_or_gt_of_forall_eventually_ne` sorts the sequence `(x_n - n)` into
  Georgii's three cases: `limsup = ∞` is contradictory (`not_forall_frequently_lt_of_tendsto`:
  the limit `s^{-i} α/c` of (11.42) would make `∑_y ℓ_i(y)` depend on `i`); `liminf = -∞` gives
  `ℓ_i ∝ α` for `i < 0` (`mul_stationary_eq_of_forall_frequently_lt`) and `μ = μ_Q`; a value `j`
  taken infinitely often gives `ℓ_i ∝ α_{i-j}` for `i < j ∧ 0` (`mul_entrance_eq_of_frequently_eq`,
  through the same-exponent ratios `matrixRealPow_div_same_of_eq`,
  `limit_eq_entranceNat_div_same`) and `μ = μ_j`. In each case the proportionality constant is
  fixed by the total masses (`mul_eq_of_forall_mul_eq_mul`), propagated to all `i` along
  `ℓ_i Q = ℓ_{i+1}` (`mul_eq_of_step_of_forall_lt`), and (11.10) identifies the measure.
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

/-! ### Georgii, Step 2 in the proof of Theorem (11.39): the three regimes of the powers of `Q`

By Step 1, `Q^{m+1}(x, y) = A_m(x, y) α(y)/α(x)` with
`A_m(x, y) = p^{m+1} δ_{x-m-1}(y) + q^{(x-m) ∨ 0} α(x ∧ m)`, so a ratio of two entries of powers
of `Q` with a *common left index* `x` is the ratio of the numerators `A` times `α(y)/α(y')`
(`matrixRealPow_div_matrixRealPow`). Georgii's Step 2 evaluates such a ratio in the three
regimes of `x` relative to the two exponents `m ≤ m + e`:

* `m + e + 1 + y < x` (`matrixRealPow_div_of_lt`): both `δ` terms vanish and the ratio is
  `q^e (α(m)/α(m+e)) α(y)/c`;
* `x ≤ m` (`matrixRealPow_div_of_le`): both numerators are `α(x)` and the ratio is `α(y)/c`;
* `x = m + 1 + (J₀ + e)` with `J₀ ≥ 1` (`matrixRealPow_div_of_eq`): the `δ` term survives in the
  numerator only.

The limits are then read off from the asymptotics `α(k) ∼ a p^k` (`tendsto_alpha_div_pow`). -/

open Filter
open scoped Topology

lemma powNumer_pos (n x y : ℕ) : 0 < powNumer p q n x y := by
  have h : 0 < q ^ (x - n) * alpha p q (min x n) :=
    mul_pos (pow_pos hq _) (alpha_pos hq hqp hp _)
  have h' : (0 : ℝ) ≤ if x = y + (n + 1) then p ^ (n + 1) else 0 := by
    split_ifs
    · exact (pow_pos (p_pos hq hqp) _).le
    · exact le_rfl
  simp only [powNumer]
  linarith

lemma matrixRealPow_pos (n x y : ℕ) : 0 < matrixRealPow p q n x y :=
  div_pos (mul_pos (powNumer_pos hq hqp hp n x y) (alpha_pos hq hqp hp y))
    (alpha_pos hq hqp hp x)

omit hq hqp hp in
/-- `A_m(x, y) = α(x)` for `x ≤ m`: Kalikow's chain has reached equilibrium, the `δ` term
vanishes and the exponent `(x - m) ∨ 0` is `0`. -/
lemma powNumer_of_le {m x : ℕ} (hx : x ≤ m) (y : ℕ) : powNumer p q m x y = alpha p q x := by
  rw [powNumer, ite_eq_right (show ¬ (x = y + (m + 1)) by omega), show x - m = 0 by omega,
    min_eq_left hx]
  ring

/-- `Q^{m+1}(x, y) = α(y)` for `x ≤ m`. -/
lemma matrixRealPow_of_le {m x : ℕ} (hx : x ≤ m) (y : ℕ) :
    matrixRealPow p q m x y = alpha p q y := by
  have hax := alpha_ne_zero hq hqp hp x
  rw [matrixRealPow, powNumer_of_le hx, mul_comm, mul_div_assoc, div_self hax, mul_one]

omit hq hqp hp in
/-- `A_m(x, y) = p^{m+1} δ_{x-m-1}(y) + q^{x-m} α(m)` for `m ≤ x`. -/
lemma powNumer_of_ge {m x : ℕ} (hx : m ≤ x) (y : ℕ) :
    powNumer p q m x y
      = (if x = y + (m + 1) then p ^ (m + 1) else 0) + q ^ (x - m) * alpha p q m := by
  rw [powNumer, min_eq_right hx]

/-- A ratio of two entries of powers of `Q` with a common left index `x`: the factors `α(x)⁻¹`
cancel, leaving a ratio of the numerators of Step 1. -/
lemma matrixRealPow_div_matrixRealPow (m m' x y y' : ℕ) :
    matrixRealPow p q m x y / matrixRealPow p q m' x y'
      = powNumer p q m x y * alpha p q y / (powNumer p q m' x y' * alpha p q y') := by
  have hax := alpha_ne_zero hq hqp hp x
  have h1 := (powNumer_pos hq hqp hp m' x y').ne'
  have h2 := (alpha_pos hq hqp hp y').ne'
  simp only [matrixRealPow]
  field_simp

omit hq hqp hp in
/-- `a = p c / (p - q)`, the form of Georgii (11.34) used in the limit computations. -/
lemma aCoeff_eq_mul_div (p q : ℝ) : aCoeff p q = p * cCoeff p q / (p - q) := by
  simp only [aCoeff, cCoeff]; ring

/-! #### The asymptotics `α(k) ∼ a p^k` -/

omit hp in
/-- **Georgii's `α(k) ∼ a p^k`.** `α(k)/p^k = a - b s^k → a`, since `s = q/p < 1`. -/
lemma tendsto_alpha_div_pow :
    Tendsto (fun k : ℕ ↦ alpha p q k / p ^ k) atTop (𝓝 (aCoeff p q)) := by
  have hp0 : (0 : ℝ) < p := p_pos hq hqp
  have hfun : ∀ k : ℕ, alpha p q k / p ^ k = aCoeff p q - bCoeff p q * sRatio p q ^ k := by
    intro k
    have hpk : (p : ℝ) ^ k ≠ 0 := (pow_pos hp0 k).ne'
    simp only [alpha, sRatio, div_pow]
    field_simp
  simp only [hfun]
  have hs : Tendsto (fun k : ℕ ↦ sRatio p q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sRatio_pos hq hqp).le (sRatio_lt_one hq hqp)
  simpa using (tendsto_const_nhds (x := aCoeff p q)).sub (hs.const_mul (bCoeff p q))

/-- `p^k/α(k) → a⁻¹`. -/
lemma tendsto_pow_div_alpha :
    Tendsto (fun k : ℕ ↦ p ^ k / alpha p q k) atTop (𝓝 (aCoeff p q)⁻¹) := by
  simpa only [inv_div] using (tendsto_alpha_div_pow hq hqp).inv₀ (aCoeff_pos hq hqp hp).ne'

/-- `α(k)/α(k + d) → p^{-d}`. -/
lemma tendsto_alpha_div_alpha_add (d : ℕ) :
    Tendsto (fun k : ℕ ↦ alpha p q k / alpha p q (k + d)) atTop (𝓝 (p ^ d)⁻¹) := by
  have hp0 : (0 : ℝ) < p := p_pos hq hqp
  have ha := (aCoeff_pos hq hqp hp).ne'
  have hpd : (p : ℝ) ^ d ≠ 0 := (pow_pos hp0 d).ne'
  have h3 : Tendsto (fun k : ℕ ↦ p ^ (k + d) / alpha p q (k + d)) atTop (𝓝 (aCoeff p q)⁻¹) :=
    (tendsto_pow_div_alpha hq hqp hp).comp (tendsto_add_atTop_nat d)
  have hfun : ∀ k : ℕ, alpha p q k / alpha p q (k + d)
      = alpha p q k / p ^ k * (p ^ (k + d) / alpha p q (k + d)) / p ^ d := by
    intro k
    have h1' : (p : ℝ) ^ k ≠ 0 := (pow_pos hp0 k).ne'
    have h2' := alpha_ne_zero hq hqp hp (k + d)
    field_simp
    ring
  simp only [hfun]
  have := ((tendsto_alpha_div_pow hq hqp).mul h3).div_const (p ^ d)
  rwa [mul_inv_cancel₀ ha, one_div] at this

/-- `p^{k+1}/α(k + d) → p/(a p^d)`. -/
lemma tendsto_pow_succ_div_alpha_add (d : ℕ) :
    Tendsto (fun k : ℕ ↦ p ^ (k + 1) / alpha p q (k + d)) atTop
      (𝓝 (p / (aCoeff p q * p ^ d))) := by
  have hp0 : (0 : ℝ) < p := p_pos hq hqp
  have ha := (aCoeff_pos hq hqp hp).ne'
  have hpd : (p : ℝ) ^ d ≠ 0 := (pow_pos hp0 d).ne'
  have h3 : Tendsto (fun k : ℕ ↦ p ^ (k + d) / alpha p q (k + d)) atTop (𝓝 (aCoeff p q)⁻¹) :=
    (tendsto_pow_div_alpha hq hqp hp).comp (tendsto_add_atTop_nat d)
  have hfun : ∀ k : ℕ, p ^ (k + 1) / alpha p q (k + d)
      = p ^ (k + d) / alpha p q (k + d) * p / p ^ d := by
    intro k
    have h2' := alpha_ne_zero hq hqp hp (k + d)
    field_simp
    ring
  simp only [hfun]
  have := (h3.mul_const p).div_const (p ^ d)
  convert this using 2
  field_simp

/-! #### The three regimes -/

/-- **Regime A of Georgii's Step 2** (`limsup(x_n - n) = ∞`). If `x` lies strictly above both
exponents and above `y`, both `δ` terms vanish and the ratio is `q^e (α(m)/α(m+e)) α(y)/c`. -/
lemma matrixRealPow_div_of_lt {m e x y : ℕ} (hx : m + e + 1 + y < x) :
    matrixRealPow p q m x y / matrixRealPow p q (m + e) x 0
      = q ^ e * (alpha p q m / alpha p q (m + e)) * alpha p q y / cCoeff p q := by
  have hm : m ≤ x := by omega
  have hme : m + e ≤ x := by omega
  have hq' : (q : ℝ) ^ (x - (m + e)) ≠ 0 := (pow_pos hq _).ne'
  have hc := (cCoeff_pos hqp hp (p := p) (q := q)).ne'
  have hme' := alpha_ne_zero hq hqp hp (m + e)
  have hpow : (q : ℝ) ^ (x - m) = q ^ e * q ^ (x - (m + e)) := by
    rw [← pow_add]; congr 1; omega
  rw [matrixRealPow_div_matrixRealPow hq hqp hp, powNumer_of_ge hm, powNumer_of_ge hme,
    ite_eq_right (show ¬ (x = y + (m + 1)) by omega),
    ite_eq_right (show ¬ (x = 0 + (m + e + 1)) by omega), alpha_zero hqp, hpow]
  field_simp
  ring

/-- **Regime B of Georgii's Step 2** (`liminf(x_n - n) = -∞`). If `x` lies below both exponents,
both numerators are `α(x)` and the ratio is `α(y)/c`. -/
lemma matrixRealPow_div_of_le {m e x y : ℕ} (hx : x ≤ m) :
    matrixRealPow p q m x y / matrixRealPow p q (m + e) x 0 = alpha p q y / cCoeff p q := by
  rw [matrixRealPow_of_le hq hqp hp hx, matrixRealPow_of_le hq hqp hp (show x ≤ m + e by omega),
    alpha_zero hqp]

/-- **Regime C of Georgii's Step 2** (the cluster point `j`). If `x = m + 1 + (J₀ + e)` with
`J₀ ≥ 1`, the `δ` term survives in the numerator only. -/
lemma matrixRealPow_div_of_eq {m e J₀ y : ℕ} (hJ₀ : 1 ≤ J₀) :
    matrixRealPow p q m (m + 1 + (J₀ + e)) y / matrixRealPow p q (m + e) (m + 1 + (J₀ + e)) 0
      = ((if J₀ + e = y then p ^ (m + 1) / alpha p q (m + e) else 0)
          + q ^ (J₀ + e + 1) * (alpha p q m / alpha p q (m + e)))
        * alpha p q y / (q ^ (J₀ + 1) * cCoeff p q) := by
  have hc := (cCoeff_pos hqp hp (p := p) (q := q)).ne'
  have hme' := alpha_ne_zero hq hqp hp (m + e)
  have hqJ : (q : ℝ) ^ (J₀ + 1) ≠ 0 := (pow_pos hq _).ne'
  have hif : (if m + 1 + (J₀ + e) = y + (m + 1) then p ^ (m + 1) else 0)
      = (if J₀ + e = y then p ^ (m + 1) else 0) := by
    by_cases h : J₀ + e = y
    · rw [ite_eq_left h, ite_eq_left (show m + 1 + (J₀ + e) = y + (m + 1) by omega)]
    · rw [ite_eq_right h, ite_eq_right (show ¬ (m + 1 + (J₀ + e) = y + (m + 1)) by omega)]
  rw [matrixRealPow_div_matrixRealPow hq hqp hp,
    powNumer_of_ge (show m ≤ m + 1 + (J₀ + e) by omega),
    powNumer_of_ge (show m + e ≤ m + 1 + (J₀ + e) by omega),
    ite_eq_right (show ¬ (m + 1 + (J₀ + e) = 0 + (m + e + 1)) by omega), alpha_zero hqp, hif,
    show m + 1 + (J₀ + e) - m = J₀ + e + 1 by omega,
    show m + 1 + (J₀ + e) - (m + e) = J₀ + 1 by omega]
  split_ifs <;> (field_simp; ring)

/-- The limit in Regime C is a ratio of Kalikow's entrance vectors (11.38): with `J = J₀ + e`,
`[p (a p^e)⁻¹ δ_J(y) + q^{J+1} p^{-e}] α(y)/(q^{J₀+1} c) = α_{-J}(y)/α_{-J₀}(0)`. This is the
identity behind Georgii's `ℓ_i = (1 - s^{1-i+j}) δ_{j-i} + s^{1-i+j} α = α_{i-j}`; the algebraic
input is `a (p - q) = p c` (`aCoeff_eq_mul_div`), i.e. `p α(J)/a = p^{J+1} - q^{J+1}`. -/
lemma limit_eq_entranceNat_div {e J₀ y : ℕ} (hJ₀ : 1 ≤ J₀) :
    ((if J₀ + e = y then p / (aCoeff p q * p ^ e) else 0) + q ^ (J₀ + e + 1) * (p ^ e)⁻¹)
        * alpha p q y / (q ^ (J₀ + 1) * cCoeff p q)
      = entranceNat p q (J₀ + e) y / entranceNat p q J₀ 0 := by
  have hp0 : (0 : ℝ) < p := p_pos hq hqp
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have hqne : (q : ℝ) ≠ 0 := hq.ne'
  have hc := (cCoeff_pos hqp hp (p := p) (q := q)).ne'
  have hpq := (sub_pos' hqp).ne'
  have hpe : (p : ℝ) ^ e ≠ 0 := pow_ne_zero _ hpne
  have hpJ : (p : ℝ) ^ (J₀ + 1) ≠ 0 := pow_ne_zero _ hpne
  have hpJe : (p : ℝ) ^ (J₀ + e + 1) ≠ 0 := pow_ne_zero _ hpne
  have hqJ : (q : ℝ) ^ (J₀ + 1) ≠ 0 := pow_ne_zero _ hqne
  have hE0 : entranceNat p q J₀ 0 = q ^ (J₀ + 1) / p ^ (J₀ + 1) * cCoeff p q := by
    rw [entranceNat, ite_eq_right (show ¬ ((0 : ℕ) = J₀) by omega), mul_zero, zero_add,
      alpha_zero hqp, sRatio, div_pow]
  have hEy : entranceNat p q (J₀ + e) y
      = (1 - q ^ (J₀ + e + 1) / p ^ (J₀ + e + 1)) * (if y = J₀ + e then 1 else 0)
        + q ^ (J₀ + e + 1) / p ^ (J₀ + e + 1) * alpha p q y := by
    rw [entranceNat, sRatio, div_pow]
  rw [hE0, hEy, aCoeff_eq_mul_div, inv_eq_one_div]
  by_cases h : J₀ + e = y
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, alpha_eq hqp (J₀ + e)]
    field_simp
    ring
  · rw [ite_eq_right h, ite_eq_right (fun hy : y = J₀ + e ↦ h hy.symm)]
    field_simp
    ring

/-! #### The limits along the regimes, and two general facts about sequences -/

omit hq hqp hp in
/-- `n ↦ (n + c).toNat` tends to infinity with `n`, for every fixed `c ∈ ℤ`. -/
lemma tendsto_toNat_natCast_add (c : ℤ) :
    Tendsto (fun n : ℕ ↦ ((n : ℤ) + c).toNat) atTop atTop :=
  tendsto_atTop_atTop.2 fun b ↦ ⟨(b - c).toNat, fun n hn ↦ by omega⟩

omit hq hqp hp in
/-- Two convergent ratios with a common, eventually non-zero denominator: if `A_n/B_n → a` and
`A'_n/B_n → a' ≠ 0`, then `A_n/A'_n → a/a'`. This turns the limit formula (11.40) of Georgii
Theorem (11.9)(c), which normalises by `Q^n(x_n, 0)`, into a limit of ratios of two entries of
the *same* power of `Q`. -/
lemma tendsto_div_of_tendsto_div_of_tendsto_div {A A' B : ℕ → ℝ} {a a' : ℝ}
    (hB : ∀ᶠ n in atTop, B n ≠ 0) (h : Tendsto (fun n ↦ A n / B n) atTop (𝓝 a))
    (h' : Tendsto (fun n ↦ A' n / B n) atTop (𝓝 a')) (ha' : a' ≠ 0) :
    Tendsto (fun n ↦ A n / A' n) atTop (𝓝 (a / a')) :=
  (h.div h' ha').congr' (hB.mono fun _ hn ↦ div_div_div_cancel_right₀ hn _ _)

/-- **Regime C with a common exponent**: `Q^{m+1}(m+1+J, y)/Q^{m+1}(m+1+J, 0)` for `J ≥ 1`; this
is `matrixRealPow_div_of_eq` at `e = 0`. -/
lemma matrixRealPow_div_same_of_eq {m J y : ℕ} (hJ : 1 ≤ J) :
    matrixRealPow p q m (m + 1 + J) y / matrixRealPow p q m (m + 1 + J) 0
      = ((if J = y then p ^ (m + 1) / alpha p q m else 0) + q ^ (J + 1)) * alpha p q y
        / (q ^ (J + 1) * cCoeff p q) := by
  have := matrixRealPow_div_of_eq hq hqp hp (m := m) (e := 0) (J₀ := J) (y := y) hJ
  simpa only [add_zero, div_self (alpha_ne_zero hq hqp hp m), mul_one] using this

/-- The limit in Regime C with a common exponent is the ratio `α_{-J}(y)/α_{-J}(0)` of Kalikow's
entrance vectors (11.38): `limit_eq_entranceNat_div` at `e = 0`. -/
lemma limit_eq_entranceNat_div_same {J y : ℕ} (hJ : 1 ≤ J) :
    ((if J = y then p / aCoeff p q else 0) + q ^ (J + 1)) * alpha p q y
        / (q ^ (J + 1) * cCoeff p q)
      = entranceNat p q J y / entranceNat p q J 0 := by
  have := limit_eq_entranceNat_div hq hqp hp (e := 0) (J₀ := J) (y := y) hJ
  simpa only [add_zero, pow_zero, mul_one, inv_one] using this

/-- **The limit in Regime A.** Along any `f n → ∞`,
`q^e (α(f n)/α(f n + e)) α(y)/c → q^e p^{-e} α(y)/c = s^e α(y)/c`. -/
lemma tendsto_ratio_of_lt {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) (e y : ℕ) :
    Tendsto (fun n ↦ q ^ e * (alpha p q (f n) / alpha p q (f n + e)) * alpha p q y / cCoeff p q)
      atTop (𝓝 (q ^ e * (p ^ e)⁻¹ * alpha p q y / cCoeff p q)) := by
  have := (tendsto_alpha_div_alpha_add hq hqp hp e).comp hf
  exact ((this.const_mul _).mul_const _).div_const _

/-- **The limit in Regime C.** Along any `f n → ∞`, the common-exponent ratio of
`matrixRealPow_div_same_of_eq` tends to `α_{-J}(y)/α_{-J}(0)`, because `p^{k+1}/α(k) → p/a`. -/
lemma tendsto_ratio_of_eq {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) {J : ℕ} (hJ : 1 ≤ J)
    (y : ℕ) :
    Tendsto (fun n ↦ ((if J = y then p ^ (f n + 1) / alpha p q (f n) else 0) + q ^ (J + 1))
      * alpha p q y / (q ^ (J + 1) * cCoeff p q)) atTop
      (𝓝 (entranceNat p q J y / entranceNat p q J 0)) := by
  rw [← limit_eq_entranceNat_div_same hq hqp hp hJ]
  refine (Tendsto.mul_const _ (Tendsto.add ?_ tendsto_const_nhds)).div_const _
  by_cases h : J = y
  · simp only [ite_eq_left h]
    have := (tendsto_pow_succ_div_alpha_add hq hqp hp 0).comp hf
    simpa only [Function.comp_def, add_zero, pow_zero, mul_one] using this
  · simp only [ite_eq_right h]
    exact tendsto_const_nhds

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
abbrev chain : Measure (ℤ → ℕ) := boundaryLawMeasure (isBoundaryLaw hq hqp hp)

/-- `μ_0 ∈ 𝒢(Q)`: Theorem (11.9)(a). -/
theorem isGibbsMeasure_chain :
    (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)).IsGibbsMeasure
      (chain hq hqp hp) :=
  isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _

/-- **Georgii's `μ_Q`** for Kalikow's matrix: the shift-invariant Markov chain of the constant
boundary law `ℓ_i = α`, `r_i = 1` (the invariant probability vector `α` of the stochastic `Q`).
By Theorem (11.13) it is the only element of `𝒢_Θ(Q)` (`invariantG_eq_singleton`), and it is one
of the two kinds of extreme Gibbs measures in Theorem (11.39). -/
abbrev invariantChain : Measure (ℤ → ℕ) :=
  boundaryLawMeasure (isBoundaryLaw_const (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
    (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
    (tsum_stationary_mul_matrix hq hqp hp))

/-- **Georgii's `μ_j = θ_j(μ_0)`**, `j ∈ ℤ`: the translates of Kalikow's chain `μ_0`. Under `θ_j`
the coordinate `σ_i` becomes `σ_{i-j}`, so `μ_j` is the measure (11.10) of the boundary law
`ℓ_i = α_{i-j}`, `r_i = 1` (`shiftedChain_eq_boundaryLawMeasure`). -/
abbrev shiftedChain (j : ℤ) : Measure (ℤ → ℕ) := (chain hq hqp hp).map (shift ℕ j).toFun

/-- `μ_j` is the measure (11.10) of the shifted boundary law `{α_{i-j}, 1}`. -/
theorem shiftedChain_eq_boundaryLawMeasure (j : ℤ) :
    shiftedChain hq hqp hp j = boundaryLawMeasure ((isBoundaryLaw hq hqp hp).shift j) :=
  (isBoundaryLaw hq hqp hp).boundaryLawMeasure_map_shift j

@[simp] lemma shiftedChain_zero : shiftedChain hq hqp hp 0 = chain hq hqp hp :=
  map_shift_zero _

theorem isGibbsMeasure_shiftedChain (j : ℤ) :
    (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)).IsGibbsMeasure
      (shiftedChain hq hqp hp j) := by
  rw [shiftedChain_eq_boundaryLawMeasure]
  exact isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _

theorem isGibbsMeasure_invariantChain :
    (transferSpecification (matrix p q) (isTransferMatrix hq hqp hp)).IsGibbsMeasure
      (invariantChain hq hqp hp) :=
  isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _

/-- The one-site marginal of `μ_j`: `μ_j(σ_i = x) = α_{i-j}(x)`. -/
theorem shiftedChain_preimage_singleton (j i : ℤ) (x : ℕ) :
    shiftedChain hq hqp hp j ((fun ω : ℤ → ℕ ↦ ω i) ⁻¹' {x}) = entrance p q (i - j) x := by
  rw [shiftedChain_eq_boundaryLawMeasure]
  have h := IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_self
    ((isBoundaryLaw hq hqp hp).shift j) i (fun _ ↦ x)
  rw [intervalCylinder_self] at h
  simpa using h

/-- The one-site marginal of `μ_Q`: `μ_Q(σ_i = x) = α(x)`. -/
theorem invariantChain_preimage_singleton (i : ℤ) (x : ℕ) :
    invariantChain hq hqp hp ((fun ω : ℤ → ℕ ↦ ω i) ⁻¹' {x}) = stationary p q x := by
  have h := IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_self
    (isBoundaryLaw_const (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
      (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
      (tsum_stationary_mul_matrix hq hqp hp)) i (fun _ ↦ x)
  rw [intervalCylinder_self] at h
  simpa using h

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
      = {invariantChain hq hqp hp} :=
  invariantG_eq_singleton_boundaryLawMeasure_const _ (isTransferMatrix hq hqp hp)
    (matrix_pos hq hqp hp) (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
    (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
    (tsum_stationary_mul_matrix hq hqp hp) rfl

/-- **Georgii, before (11.39): `μ_0 = μ_Q` on `𝓕_{]0,∞[}`.** The entrance law reaches equilibrium
at time `1`, so `μ_0` and `μ_Q` agree on every cylinder `{σ_a = x_a, …, σ_b = x_b}` with
`1 ≤ a ≤ b`. -/
theorem chain_intervalCylinder_eq {a b : ℤ} (ha : 1 ≤ a) (hab : a ≤ b) (σ : ℤ → ℕ) :
    chain hq hqp hp (intervalCylinder a b σ)
      = invariantChain hq hqp hp (intervalCylinder a b σ) := by
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

/-! ## Georgii Theorem (11.39), Step 2: `ex 𝒢(Q) ⊆ {μ_Q} ∪ {μ_j : j ∈ ℤ}`

Given `μ ∈ ex 𝒢(Q)`, Theorem (11.9)(c)
(`MeasureTheory.GibbsMeasure.Markov.exists_isBoundaryLaw_and_tendsto_of_mem_extremePoints`, with
the reference state `a = 0`) represents `μ` by a boundary law `{ℓ_i, r_i}` and supplies sequences
`(x_n)`, `(z_n)` with (11.40) `ℓ_i/ℓ_0(0) = lim_n Q^{n+i}(x_n, ·)/Q^n(x_n, 0)` for `i < 0` and
(11.41) `r_i/r_0(0) = lim_n Q^{n-i}(·, z_n)/Q^n(0, z_n)` for `i > 0`. Georgii normalises
`r_0(0) = 1`; here instead `r ≡ κ := r_0(0)` is proved directly (`right_eq_of_tendsto`), and the
identities `ℓ_i κ = v_i` are established for the candidate laws `v_i = α` and `v_i = α_{i-j}`.

The sequence `x_n - n` either has a cluster point `j ∈ ℤ`, or is frequently above every bound, or
frequently below every bound (`forall_frequently_lt_or_gt_of_forall_eventually_ne`). The three
regimes of the powers of `Q` computed at the end of `section Real` identify the limits (11.40) in
each case: Regime A is contradictory (`not_forall_frequently_lt_of_tendsto`), Regime B gives
`ℓ_i ∝ α` (`mul_stationary_eq_of_forall_frequently_lt`) and hence `μ = μ_Q`, and Regime C gives
`ℓ_i ∝ α_{i-j}` (`mul_entrance_eq_of_frequently_eq`) and hence `μ = μ_j`. -/

open Filter
open scoped Topology

/-- The real value of an entry of `Q^{m+1}`: `matrix_pow_apply_singleton` read in `ℝ`. -/
lemma toReal_matrix_pow_apply_singleton (m x y : ℕ) :
    ((Kernel.ofMatrix (matrix p q) ^ (m + 1)) x {y}).toReal = matrixRealPow p q m x y := by
  rw [matrix_pow_apply_singleton hq hqp hp,
    ENNReal.toReal_ofReal (matrixRealPow_nonneg hq hqp hp m x y)]

/-- The real value of an entry of `Q^n` for `n ≥ 1`. -/
lemma toReal_matrix_pow_apply_singleton_of_pos {n : ℕ} (hn : 0 < n) (x y : ℕ) :
    ((Kernel.ofMatrix (matrix p q) ^ n) x {y}).toReal = matrixRealPow p q (n - 1) x y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [toReal_matrix_pow_apply_singleton hq hqp hp, Nat.add_sub_cancel]

omit hq hqp hp in
/-- An integer sequence that eventually avoids every value is frequently above every bound or
frequently below every bound: Georgii's trichotomy `limsup = ∞`, `liminf = -∞`, or a cluster
point, in the form used in Step 2 of the proof of Theorem (11.39). -/
lemma forall_frequently_lt_or_gt_of_forall_eventually_ne {d : ℕ → ℤ}
    (h : ∀ j : ℤ, ∀ᶠ n in atTop, d n ≠ j) :
    (∀ K : ℤ, ∃ᶠ n in atTop, K < d n) ∨ (∀ K : ℤ, ∃ᶠ n in atTop, d n < K) := by
  by_contra hcon
  obtain ⟨K₁, hK₁⟩ := not_forall.1 fun h₁ ↦ hcon (Or.inl h₁)
  obtain ⟨K₂, hK₂⟩ := not_forall.1 fun h₂ ↦ hcon (Or.inr h₂)
  rw [Filter.not_frequently] at hK₁ hK₂
  have hall : ∀ᶠ n in atTop, ∀ j ∈ Finset.Icc K₂ K₁, d n ≠ j :=
    (Filter.eventually_all_finset _).2 fun j _ ↦ h j
  obtain ⟨n, hn₁, hn₂, hn₃⟩ := (hK₁.and (hK₂.and hall)).exists
  exact hn₃ (d n) (Finset.mem_Icc.2 ⟨not_lt.1 hn₂, not_lt.1 hn₁⟩) rfl

omit hq hqp hp in
/-- If `ℓ` is proportional to a probability vector `v` — `ℓ(y) v(0) = v(y) ℓ(0)` for all `y` —
and `(∑_y ℓ(y)) κ = 1`, then `ℓ(y) κ = v(y)`. This is Georgii's "since `ℓ_i` and `α` are
probability vectors" step, without normalising `ℓ_i`. -/
lemma mul_eq_of_forall_mul_eq_mul {ℓ v : ℕ → ℝ≥0∞} {κ : ℝ≥0∞} (hv0 : v 0 ≠ 0) (hvt : v 0 ≠ ⊤)
    (hv1 : ∑' y, v y = 1) (hℓκ : (∑' y, ℓ y) * κ = 1) (h : ∀ y, ℓ y * v 0 = v y * ℓ 0) (y : ℕ) :
    ℓ y * κ = v y := by
  have hsum : (∑' y, ℓ y) * v 0 = ℓ 0 := by
    rw [← ENNReal.tsum_mul_right]
    simp_rw [h]
    rw [ENNReal.tsum_mul_right, hv1, one_mul]
  refine (ENNReal.mul_left_inj hv0 hvt).1 ?_
  calc ℓ y * κ * v 0 = (ℓ y * v 0) * κ := by ring
    _ = v y * ℓ 0 * κ := by rw [h y]
    _ = v y * ((∑' y, ℓ y) * v 0) * κ := by rw [hsum]
    _ = v y * v 0 * ((∑' y, ℓ y) * κ) := by ring
    _ = v y * v 0 := by rw [hℓκ, mul_one]

omit hq hqp hp in
/-- Upward propagation along the recursions `ℓ_i Q = ℓ_{i+1}` and `v_i Q = v_{i+1}`: an identity
`ℓ_i κ = v_i` valid for all `i < i₀` is valid for all `i ∈ ℤ`. -/
lemma mul_eq_of_step_of_forall_lt {Q : ℕ → ℕ → ℝ≥0∞} {ℓ v : ℤ → ℕ → ℝ≥0∞} {κ : ℝ≥0∞}
    (hℓ : ∀ i y, ∑' x, ℓ i x * Q x y = ℓ (i + 1) y)
    (hv : ∀ i y, ∑' x, v i x * Q x y = v (i + 1) y)
    {i₀ : ℤ} (h : ∀ i < i₀, ∀ y, ℓ i y * κ = v i y) (i : ℤ) (y : ℕ) : ℓ i y * κ = v i y := by
  have hstep : ∀ i, (∀ y, ℓ i y * κ = v i y) → ∀ y, ℓ (i + 1) y * κ = v (i + 1) y := by
    intro i hi y
    rw [← hℓ i y, ← hv i y, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun s ↦ by rw [mul_right_comm, hi s]
  have hup : ∀ k : ℕ, ∀ y, ℓ (i₀ - 1 + k) y * κ = v (i₀ - 1 + k) y := by
    intro k
    induction k with
    | zero => intro y; rw [Nat.cast_zero, add_zero]; exact h _ (by omega) y
    | succ m ihm =>
      rw [show i₀ - 1 + ((m + 1 : ℕ) : ℤ) = (i₀ - 1 + (m : ℤ)) + 1 by push_cast; ring]
      exact hstep _ ihm
  rcases lt_or_ge i i₀ with hi | hi
  · exact h i hi y
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = i₀ - 1 + (k : ℤ) := ⟨(i - i₀ + 1).toNat, by omega⟩
    exact hup k y

/-- **Georgii's `r_i ≡ 1` in Step 2 of Theorem (11.39)**, without the normalisation `r_0(0) = 1`:
every `r_i(y)` equals `r_0(0)`. For `i > 0` the ratio `Q^{n-i}(y, z_n)/Q^n(0, z_n)` in (11.41) is
`α(z_n)/α(z_n) = 1` as soon as `n ≥ y + i + 2`, by Step 1 and `matrixRealPow_of_le`; the
identity then propagates downward along `Q r_i = r_{i-1}`, since `Q` is stochastic. -/
theorem right_eq_of_tendsto {ℓ r : ℤ → ℕ → ℝ≥0∞} (hbl : IsBoundaryLaw (matrix p q) ℓ r)
    {z : ℕ → ℕ}
    (hz : ∀ i : ℤ, 0 < i → ∀ y : ℕ, Tendsto
      (fun n : ℕ ↦ ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) - i).toNat) y {z n}).toReal
        / ((Kernel.ofMatrix (matrix p q) ^ n) (0 : ℕ) {z n}).toReal) atTop
      (𝓝 ((r i y).toReal / (r 0 0).toReal)))
    (i : ℤ) (y : ℕ) : r i y = r 0 0 := by
  have hr0 : (0 : ℝ) < (r 0 0).toReal :=
    ENNReal.toReal_pos (hbl.right_pos 0 0).ne' (hbl.right_ne_top 0 0)
  have hpos : ∀ i : ℤ, 0 < i → ∀ y : ℕ, r i y = r 0 0 := by
    intro i hi y
    have hev : ∀ᶠ n : ℕ in atTop,
        ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) - i).toNat) y {z n}).toReal
          / ((Kernel.ofMatrix (matrix p q) ^ n) (0 : ℕ) {z n}).toReal = 1 := by
      filter_upwards [eventually_ge_atTop (y + i.toNat + 2)] with n hn
      rw [toReal_matrix_pow_apply_singleton_of_pos hq hqp hp (by omega),
        toReal_matrix_pow_apply_singleton_of_pos hq hqp hp (by omega),
        matrixRealPow_of_le hq hqp hp (show y ≤ ((n : ℤ) - i).toNat - 1 by omega),
        matrixRealPow_of_le hq hqp hp (Nat.zero_le _), div_self (alpha_ne_zero hq hqp hp _)]
    have h1 : (r i y).toReal / (r 0 0).toReal = 1 :=
      tendsto_nhds_unique (hz i hi y) (tendsto_const_nhds.congr' (hev.mono fun n hn ↦ hn.symm))
    rw [div_eq_one_iff_eq hr0.ne'] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (hbl.right_ne_top i y) (hbl.right_ne_top 0 0)).1 h1
  have hdown : ∀ k : ℕ, ∀ y, r (1 - (k : ℤ)) y = r 0 0 := by
    intro k
    induction k with
    | zero => intro y; rw [Nat.cast_zero, sub_zero]; exact hpos 1 one_pos y
    | succ m ihm =>
      intro y
      rw [show (1 : ℤ) - ((m + 1 : ℕ) : ℤ) = (1 - (m : ℤ)) - 1 by push_cast; ring,
        ← hbl.tsum_mul_right]
      simp_rw [ihm]
      rw [ENNReal.tsum_mul_right, tsum_matrix hq hqp hp, one_mul]
  rcases le_or_gt i 1 with hi | hi
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = 1 - (k : ℤ) := ⟨(1 - i).toNat, by omega⟩
    exact hdown k y
  · exact hpos i (by omega) y

/-- **The common-exponent form of (11.40).** Dividing the limits (11.40) at `y` and at `0` gives
`ℓ_i(y)/ℓ_i(0) = lim_n Q^{n+i}(x_n, y)/Q^{n+i}(x_n, 0)` for `i < 0`, with the entries of the
powers of `Q` written through Step 1 with the exponent `n + i = (n + (i - 1)).toNat + 1`. -/
theorem tendsto_matrixRealPow_div_of_tendsto {ℓ : ℤ → ℕ → ℝ≥0∞} (hℓ0 : ∀ i y, ℓ i y ≠ 0)
    (hℓt : ∀ i y, ℓ i y ≠ ⊤) {x : ℕ → ℕ}
    (hx : ∀ i : ℤ, i < 0 → ∀ y : ℕ, Tendsto
      (fun n : ℕ ↦ ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) + i).toNat) (x n) {y}).toReal
        / ((Kernel.ofMatrix (matrix p q) ^ n) (x n) {(0 : ℕ)}).toReal) atTop
      (𝓝 ((ℓ i y).toReal / (ℓ 0 0).toReal)))
    {i : ℤ} (hi : i < 0) (y : ℕ) :
    Tendsto (fun n : ℕ ↦ matrixRealPow p q ((n : ℤ) + (i - 1)).toNat (x n) y
      / matrixRealPow p q ((n : ℤ) + (i - 1)).toNat (x n) 0) atTop
      (𝓝 ((ℓ i y).toReal / (ℓ i 0).toReal)) := by
  have h00 : (ℓ 0 0).toReal ≠ 0 := (ENNReal.toReal_pos (hℓ0 0 0) (hℓt 0 0)).ne'
  have hi0 : (ℓ i 0).toReal / (ℓ 0 0).toReal ≠ 0 :=
    div_ne_zero (ENNReal.toReal_pos (hℓ0 i 0) (hℓt i 0)).ne' h00
  have hB : ∀ᶠ n : ℕ in atTop,
      ((Kernel.ofMatrix (matrix p q) ^ n) (x n) {(0 : ℕ)}).toReal ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [toReal_matrix_pow_apply_singleton_of_pos hq hqp hp hn]
    exact (matrixRealPow_pos hq hqp hp _ _ _).ne'
  have h := tendsto_div_of_tendsto_div_of_tendsto_div hB (hx i hi y) (hx i hi 0) hi0
  rw [div_div_div_cancel_right₀ h00] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 - i).toNat] with n hn
  have hn' : 0 < ((n : ℤ) + i).toNat := by omega
  simp only [toReal_matrix_pow_apply_singleton_of_pos hq hqp hp hn',
    show ((n : ℤ) + i).toNat - 1 = ((n : ℤ) + (i - 1)).toNat by omega]

/-- **Regime A of Georgii's Step 2 is contradictory.** If `x_n - n` is frequently above every
bound then, for every `i < 0` and `y`, infinitely many `n` have `x_n > n + y`, where the ratio
in (11.40) is `q^{-i} (α(n+i-1)/α(n-1)) α(y)/c`; its limit gives `ℓ_i(y)/ℓ_0(0) = s^{-i} α(y)/c`.
Summing over `y` — all `ℓ_i` have the same total mass `S`, since `r ≡ κ` — gives
`S/ℓ_0(0) = s^{-i}/c` for every `i < 0`, so `s = s²`, which is impossible for `0 < s < 1`. -/
theorem not_forall_frequently_lt_of_tendsto {ℓ : ℤ → ℕ → ℝ≥0∞} (hℓ0 : ∀ i y, ℓ i y ≠ 0)
    (hℓt : ∀ i y, ℓ i y ≠ ⊤) {S : ℝ≥0∞} (hS : ∀ i, ∑' y, ℓ i y = S) {x : ℕ → ℕ}
    (hx : ∀ i : ℤ, i < 0 → ∀ y : ℕ, Tendsto
      (fun n : ℕ ↦ ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) + i).toNat) (x n) {y}).toReal
        / ((Kernel.ofMatrix (matrix p q) ^ n) (x n) {(0 : ℕ)}).toReal) atTop
      (𝓝 ((ℓ i y).toReal / (ℓ 0 0).toReal)))
    (hA : ∀ K : ℤ, ∃ᶠ n in atTop, K < (x n : ℤ) - n) : False := by
  have hL : (0 : ℝ) < (ℓ 0 0).toReal := ENNReal.toReal_pos (hℓ0 0 0) (hℓt 0 0)
  have hc : cCoeff p q ≠ 0 := (cCoeff_pos hqp hp).ne'
  have key : ∀ i : ℤ, i < 0 → ∀ y : ℕ, (ℓ i y).toReal / (ℓ 0 0).toReal
      = q ^ (-i).toNat * (p ^ (-i).toNat)⁻¹ * alpha p q y / cCoeff p q := by
    intro i hi y
    refine tendsto_nhds_unique_of_frequently_eq (hx i hi y)
      (tendsto_ratio_of_lt hq hqp hp (tendsto_toNat_natCast_add (i - 1)) (-i).toNat y) ?_
    refine ((hA y).and_eventually (eventually_ge_atTop (1 - i).toNat)).mono
      fun n ⟨hn₁, hn₂⟩ ↦ ?_
    rw [toReal_matrix_pow_apply_singleton_of_pos hq hqp hp (show 0 < ((n : ℤ) + i).toNat by omega),
      toReal_matrix_pow_apply_singleton_of_pos hq hqp hp (show 0 < n by omega),
      show ((n : ℤ) + i).toNat - 1 = ((n : ℤ) + (i - 1)).toNat by omega,
      show n - 1 = ((n : ℤ) + (i - 1)).toNat + (-i).toNat by omega]
    exact matrixRealPow_div_of_lt hq hqp hp (by omega)
  have hsum : ∀ i : ℤ, i < 0 → S.toReal
      = (ℓ 0 0).toReal * (q ^ (-i).toNat * (p ^ (-i).toNat)⁻¹ / cCoeff p q) := by
    intro i hi
    have hpt : ∀ y, (ℓ i y).toReal
        = (ℓ 0 0).toReal * (q ^ (-i).toNat * (p ^ (-i).toNat)⁻¹ / cCoeff p q) * alpha p q y := by
      intro y
      have h := key i hi y
      rw [div_eq_iff hL.ne'] at h
      rw [h]; ring
    rw [← hS i, ENNReal.tsum_toReal_eq (hℓt i)]
    simp_rw [hpt]
    rw [tsum_mul_left, tsum_alpha hq hqp hp, mul_one]
  have hsum' : ∀ e : ℕ, 1 ≤ e → S.toReal
      = (ℓ 0 0).toReal * (q ^ e * (p ^ e)⁻¹ / cCoeff p q) := by
    intro e he
    have h := hsum (-(e : ℤ)) (by omega)
    rwa [show (-(-(e : ℤ))).toNat = e by omega] at h
  have h3 : q ^ 1 * (p ^ 1)⁻¹ / cCoeff p q = q ^ 2 * (p ^ 2)⁻¹ / cCoeff p q :=
    mul_left_cancel₀ hL.ne' ((hsum' 1 le_rfl).symm.trans (hsum' 2 one_le_two))
  have h4 : q ^ 1 * (p ^ 1)⁻¹ = q ^ 2 * (p ^ 2)⁻¹ := (div_left_inj' hc).1 h3
  have hs : sRatio p q ^ 1 = sRatio p q ^ 2 := by
    rw [sRatio, div_pow, div_pow, div_eq_mul_inv, div_eq_mul_inv]
    exact h4
  have hs0 := sRatio_pos hq hqp (p := p) (q := q)
  have hs1 := sRatio_lt_one hq hqp (p := p) (q := q)
  have := mul_lt_mul_of_pos_left hs1 hs0
  rw [pow_one, pow_two] at hs
  linarith

/-- **Regime B of Georgii's Step 2.** If `x_n - n` is frequently below every bound then, for
every `i < 0`, infinitely many `n` have `x_n ≤ n + i - 1`, where both entries in the
common-exponent ratio are `α`; hence `ℓ_i(y)/ℓ_i(0) = α(y)/α(0)`, i.e.
`ℓ_i(y) α(0) = α(y) ℓ_i(0)`. -/
theorem mul_stationary_eq_of_forall_frequently_lt {ℓ : ℤ → ℕ → ℝ≥0∞} (hℓ0 : ∀ i y, ℓ i y ≠ 0)
    (hℓt : ∀ i y, ℓ i y ≠ ⊤) {x : ℕ → ℕ}
    (hx : ∀ i : ℤ, i < 0 → ∀ y : ℕ, Tendsto
      (fun n : ℕ ↦ ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) + i).toNat) (x n) {y}).toReal
        / ((Kernel.ofMatrix (matrix p q) ^ n) (x n) {(0 : ℕ)}).toReal) atTop
      (𝓝 ((ℓ i y).toReal / (ℓ 0 0).toReal)))
    (hB : ∀ K : ℤ, ∃ᶠ n in atTop, (x n : ℤ) - n < K) {i : ℤ} (hi : i < 0) (y : ℕ) :
    ℓ i y * stationary p q 0 = stationary p q y * ℓ i 0 := by
  have hratio : (ℓ i y).toReal / (ℓ i 0).toReal = alpha p q y / cCoeff p q := by
    refine tendsto_nhds_unique_of_frequently_eq
      (tendsto_matrixRealPow_div_of_tendsto hq hqp hp hℓ0 hℓt hx hi y) tendsto_const_nhds ?_
    refine (hB i).mono fun n hn ↦ ?_
    rw [matrixRealPow_of_le hq hqp hp (show x n ≤ ((n : ℤ) + (i - 1)).toNat by omega),
      matrixRealPow_of_le hq hqp hp (show x n ≤ ((n : ℤ) + (i - 1)).toNat by omega),
      alpha_zero hqp]
  refine ENNReal.mul_eq_mul_of_toReal_div_eq (hℓt i y) (hℓ0 i 0) (hℓt i 0) ENNReal.ofReal_ne_top
    (stationary_pos hq hqp hp 0).ne' ENNReal.ofReal_ne_top ?_
  rw [hratio, stationary, stationary, ENNReal.toReal_ofReal (alpha_pos hq hqp hp y).le,
    ENNReal.toReal_ofReal (alpha_pos hq hqp hp 0).le, alpha_zero hqp]

/-- **Regime C of Georgii's Step 2.** If `x_n - n = j` frequently then, for every `i < j ∧ 0`,
`x_n = (n + i - 1) + 1 + (j - i)` along these `n`, where the common-exponent ratio is given by
`matrixRealPow_div_same_of_eq` and tends to `α_{i-j}(y)/α_{i-j}(0)`; hence
`ℓ_i(y) α_{i-j}(0) = α_{i-j}(y) ℓ_i(0)`. -/
theorem mul_entrance_eq_of_frequently_eq {ℓ : ℤ → ℕ → ℝ≥0∞} (hℓ0 : ∀ i y, ℓ i y ≠ 0)
    (hℓt : ∀ i y, ℓ i y ≠ ⊤) {x : ℕ → ℕ}
    (hx : ∀ i : ℤ, i < 0 → ∀ y : ℕ, Tendsto
      (fun n : ℕ ↦ ((Kernel.ofMatrix (matrix p q) ^ ((n : ℤ) + i).toNat) (x n) {y}).toReal
        / ((Kernel.ofMatrix (matrix p q) ^ n) (x n) {(0 : ℕ)}).toReal) atTop
      (𝓝 ((ℓ i y).toReal / (ℓ 0 0).toReal)))
    {j : ℤ} (hj : ∃ᶠ n in atTop, (x n : ℤ) - n = j) {i : ℤ} (hi : i < min j 0) (y : ℕ) :
    ℓ i y * entrance p q (i - j) 0 = entrance p q (i - j) y * ℓ i 0 := by
  have hi0 : i < 0 := lt_of_lt_of_le hi (min_le_right _ _)
  have hij : i < j := lt_of_lt_of_le hi (min_le_left _ _)
  have hJ : 1 ≤ (j - i).toNat := by omega
  have hratio : (ℓ i y).toReal / (ℓ i 0).toReal
      = entranceNat p q (j - i).toNat y / entranceNat p q (j - i).toNat 0 := by
    refine tendsto_nhds_unique_of_frequently_eq
      (tendsto_matrixRealPow_div_of_tendsto hq hqp hp hℓ0 hℓt hx hi0 y)
      (tendsto_ratio_of_eq hq hqp hp (tendsto_toNat_natCast_add (i - 1)) hJ y) ?_
    refine (hj.and_eventually (eventually_ge_atTop (1 - i).toNat)).mono fun n ⟨hn₁, hn₂⟩ ↦ ?_
    rw [show x n = ((n : ℤ) + (i - 1)).toNat + 1 + (j - i).toNat by omega,
      matrixRealPow_div_same_of_eq hq hqp hp hJ]
  have hE : ∀ w, (entrance p q (i - j) w).toReal = entranceNat p q (j - i).toNat w := by
    intro w
    rw [entrance, ENNReal.toReal_ofReal (entranceReal_pos hq hqp hp _ _).le, entranceReal,
      ite_eq_right (by omega), show (-(i - j)).toNat = (j - i).toNat by omega]
  refine ENNReal.mul_eq_mul_of_toReal_div_eq (hℓt i y) (hℓ0 i 0) (hℓt i 0) ENNReal.ofReal_ne_top
    ((isEntranceLaw hq hqp hp).pos _ _).ne' ENNReal.ofReal_ne_top ?_
  rw [hratio, hE, hE]

/-- **Georgii Theorem (11.39), Step 2.** Every extreme Gibbs measure for Kalikow's matrix is
`μ_Q` or one of the translates `μ_j = θ_j(μ_0)`. -/
theorem exists_eq_of_mem_extremePoints {μ : Measure (ℤ → ℕ)}
    (hμ : μ ∈ (G (transferSpecification (matrix p q)
      (isTransferMatrix hq hqp hp))).extremePoints ℝ≥0∞) :
    μ = invariantChain hq hqp hp ∨ ∃ j : ℤ, μ = shiftedChain hq hqp hp j := by
  classical
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  obtain ⟨ℓ, r, hbl, rfl, ⟨x, hx⟩, ⟨z, hz⟩⟩ :=
    exists_isBoundaryLaw_and_tendsto_of_mem_extremePoints (isTransferMatrix hq hqp hp) hμ 0
  have hℓ0 : ∀ i y, ℓ i y ≠ 0 := fun i y ↦ (hbl.left_pos i y).ne'
  have hℓt : ∀ i y, ℓ i y ≠ ⊤ := hbl.left_ne_top
  -- `r ≡ κ := r_0(0)`, hence every `ℓ_i` has total mass `κ⁻¹`
  have hr : ∀ i y, r i y = r 0 0 := right_eq_of_tendsto hq hqp hp hbl hz
  have hℓκ : ∀ i, (∑' y, ℓ i y) * r 0 0 = 1 := fun i ↦ by
    rw [← hbl.tsum_left_mul_right i, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun y ↦ by rw [hr i y]
  -- an identity `ℓ_i κ = v_i` for a boundary law `{v_i, 1}` identifies `μ` through (11.10)
  have hconcl : ∀ (v : ℤ → ℕ → ℝ≥0∞) (hv : IsBoundaryLaw (matrix p q) v (fun _ _ ↦ 1)),
      (∀ i y, ℓ i y * r 0 0 = v i y) → boundaryLawMeasure hbl = boundaryLawMeasure hv := by
    intro v hv h
    refine hv.eq_boundaryLawMeasure_of_forall_intervalCylinder fun a b hab σ ↦ ?_
    rw [hbl.boundaryLawMeasure_intervalCylinder hab σ, hr b (σ b), mul_right_comm, h a (σ a),
      mul_one]
  by_cases hC : ∃ j : ℤ, ∃ᶠ n in atTop, (x n : ℤ) - n = j
  · -- Regime C: a cluster point `j` of `x_n - n`, and `μ = μ_j`
    obtain ⟨j, hj⟩ := hC
    refine Or.inr ⟨j, ?_⟩
    rw [shiftedChain_eq_boundaryLawMeasure]
    refine hconcl (fun i ↦ entrance p q (i - j)) ((isBoundaryLaw hq hqp hp).shift j)
      (mul_eq_of_step_of_forall_lt hbl.tsum_left_mul (fun i y ↦ ?_) (i₀ := min j 0)
        fun i hi y ↦ ?_)
    · show ∑' x, entrance p q (i - j) x * matrix p q x y = entrance p q (i + 1 - j) y
      rw [(isEntranceLaw hq hqp hp).step, show i - j + 1 = i + 1 - j by ring]
    · exact mul_eq_of_forall_mul_eq_mul ((isEntranceLaw hq hqp hp).pos _ 0).ne'
        ENNReal.ofReal_ne_top ((isEntranceLaw hq hqp hp).tsum_eq_one _) (hℓκ i)
        (mul_entrance_eq_of_frequently_eq hq hqp hp hℓ0 hℓt hx hj hi) y
  · have hC' : ∀ j : ℤ, ∀ᶠ n in atTop, (x n : ℤ) - n ≠ j := fun j ↦
      Filter.not_frequently.1 (not_exists.1 hC j)
    rcases forall_frequently_lt_or_gt_of_forall_eventually_ne hC' with hA | hB
    · -- Regime A: `limsup (x_n - n) = ∞` is impossible
      exact (not_forall_frequently_lt_of_tendsto hq hqp hp hℓ0 hℓt
        (fun i ↦ ENNReal.eq_inv_of_mul_eq_one_left (hℓκ i)) hx hA).elim
    · -- Regime B: `liminf (x_n - n) = -∞`, and `μ = μ_Q`
      refine Or.inl (hconcl (fun _ ↦ stationary p q)
        (isBoundaryLaw_const (tsum_matrix hq hqp hp) (stationary_pos hq hqp hp)
          (stationary_ne_top (p := p) (q := q)) (tsum_stationary hq hqp hp)
          (tsum_stationary_mul_matrix hq hqp hp))
        (mul_eq_of_step_of_forall_lt hbl.tsum_left_mul
          (fun i y ↦ tsum_stationary_mul_matrix hq hqp hp y) (i₀ := 0) fun i hi y ↦ ?_))
      exact mul_eq_of_forall_mul_eq_mul (stationary_pos hq hqp hp 0).ne'
        (stationary_ne_top (p := p) (q := q) 0) (tsum_stationary hq hqp hp) (hℓκ i)
        (mul_stationary_eq_of_forall_frequently_lt hq hqp hp hℓ0 hℓt hx hB hi) y

end Transfer








end MeasureTheory.GibbsMeasure.Markov.Kalikow

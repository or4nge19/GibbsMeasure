/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLawPhaseTransition
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.OneSubPow
public import GibbsMeasure.Mathlib.Probability.Distributions.Poisson.Convergence
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# Georgii §11.2: the Spitzer–Cox example of phase transition

State space `E = ℤ₊ = ℕ`, sites `ℤ`. Fix `0 < p < 1` and put `q = 1 - p`. Georgii's matrix
(11.26)–(11.27) is

`Q(x, ·) = ℓ(x, p, ·) ∗ 𝔭(q, ·)`,  `Q(x, y) = ∑_{k ≤ x ∧ y} ℓ(x, p, k) 𝔭(q, y - k)`,

the transition matrix of a population in which every individual survives with probability `p` and
an independent `Poisson(q)` number of immigrants is added. Here `ℓ(n, p, k)` (11.20) is the
binomial and `𝔭(a, k)` (11.21) the Poisson weight.

Georgii's two-parameter family of boundary laws (11.29) is `ℓ^u_i(x) = 𝔭(1 + u p^i, x)`,
`r^v_i(x) = 𝔭(1 + v p^{-i}, x)/α(x)` with `α = 𝔭(1, ·)`, normalised by `ℓ^u_i r^v_i = e^{uv}`.
Since `α = 𝔭(1, ·)` the right vectors have the closed form `r^v_i(x) = e^{-v p^{-i}}(1 + v
p^{-i})^x`, and the whole family is handled here by generating functions: the generating function
of `Q(x, ·)` is `(1 - p + p z)^x e^{(1-p)(z-1)}` (`tsum_matrixReal_mul_pow`, from the binomial and
Poisson generating functions), which evaluated at `z = 1 + v p^{-i}` gives `Q r^v_i = r^v_{i-1}`,
while `ℓ^u_i Q = ℓ^u_{i+1}` is Georgii (11.25) followed by (11.24). The one-site marginals are
`μ^{u,v}(σ_i = ·) = 𝔭((1 + u p^i)(1 + v p^{-i}), ·)`, Georgii (11.30); they depend on `i` unless
`u = v = 0`, and they determine `(u, v)`, so the `μ^{u,v}` are pairwise distinct and `𝒢(γ^Q)` is
uncountable.

The power formula **(11.32)** `Q^n(x, ·) = ℓ(x, p^n, ·) ∗ 𝔭(1 - p^n, ·)` is
`matrix_pow_apply_singleton`, proved by Georgii's induction: (11.22) splits the thinning of the
survivors and the immigrants of the previous step, (11.25) thins the Poisson part, (11.23)
composes the two binomial thinnings and (11.24) merges the two Poisson parts. Together with the
Poisson convergence theorem (`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul`,
`GibbsMeasure/Mathlib/Probability/Distributions/Poisson/Convergence.lean`) it gives the *limit*
half of Step 1 of the proof of Theorem (11.31): `Q^{m_n}(x_n, ·) → 𝔭(1 + a, ·)` whenever
`m_n → ∞` and `x_n p^{m_n} → a` (`tendsto_matrix_pow_apply_singleton`), hence
`Q^{n+i}(x_n, ·) → ℓ^u_i` whenever `x_n p^n → u`
(`tendsto_matrix_pow_apply_singleton_entrance`).

**Step 1 of the proof of Theorem (11.31) is proved in full**
(`exists_tendsto_matrix_pow_apply_singleton_of_tendsto_ratio`): if
`c = lim_n Q^{n-1}(x_n, 0)/Q^n(x_n, 0)` exists and is positive, then `u = lim_n x_n p^n` exists
and `Q^{n+i}(x_n, ·) → ℓ^u_i` for every `i`. Georgii's estimate
`Q^{n-1}(x_n,0)/Q^n(x_n,0) ≤ e · exp[-x_n p^{n-1}(1 - p)]`
(`toReal_matrix_pow_apply_zero_div_le`, using `matrix_pow_apply_zero`) bounds `(x_n p^n)`, and
`c = ℓ^u_{-1}(0)/ℓ^u_0(0) = exp(-u(1-p)/p)` pins down the unique cluster point.

The full Theorem (11.31) — `ex 𝒢(Q) = {μ^{u,v} : u, v ≥ 0}` together with the integral
representation over the limits `U = lim_{i → -∞} σ_i p^{-i}`, `V = lim_{i → ∞} σ_i p^i` — is
**not** formalised, and neither is Corollary (11.33). What is still missing is:

* **the quantitative half of Theorem (11.9)(c)**, i.e. the explicit limit formulas
  `ℓ_i = ℓ_0(0) lim_n Q^{n+i}(x_n, ·)/Q^n(x_n, 0)` (`i < 0`) and
  `r_i = r_0(0) lim_n Q^{n-i}(·, y_n)/Q^n(0, y_n)` (`i > 0`) for the boundary law of an extreme
  Gibbs measure. `exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints`
  (`GibbsMeasure/Model/BoundaryLawUniqueness.lean`) gives the *existence* of the boundary law but
  not these formulas; they need the backward martingale theorem together with the triviality of
  the left tail under an extreme Gibbs measure. This is the sole obstruction to Steps 2 and 4;
* Step 3, the Borel–Cantelli argument giving `μ^{u,v}(U = u, V = v) = 1`, and the extreme
  decomposition theorem (7.26) bookkeeping of Step 4.

## Main declarations

* `binomialWeight`, `poissonWeight` — **Georgii (11.20), (11.21)**, tied to Mathlib's
  `ProbabilityTheory.binomial` and `ProbabilityTheory.poissonMeasure` by
  `binomialWeight_eq_binomial_real`, `poissonWeight_eq_poissonMeasure_real` and
  `poissonWeight_eq_poissonMeasure_real_toNNReal`.
* `sum_binomialWeight_mul_binomialWeight` — **Georgii (11.22)**, `ℓ(m,p,·) ∗ ℓ(n,p,·)
  = ℓ(m+n,p,·)` (Vandermonde).
* `hasSum_binomialWeight_mul_binomialWeight`, `sum_binomialWeight_mul_binomialWeight_left` —
  **Georgii (11.23)**, `∑_k ℓ(n,p₁,k) ℓ(k,p₂,·) = ℓ(n,p₁p₂,·)`.
* `sum_poissonWeight_mul_poissonWeight` — **Georgii (11.24)**, `𝔭(a,·) ∗ 𝔭(b,·) = 𝔭(a+b,·)`.
* `hasSum_poissonWeight_mul_binomialWeight` — **Georgii (11.25)**,
  `∑_x 𝔭(a, x) ℓ(x, p, ·) = 𝔭(a p, ·)`.
* `hasSum_binomialWeight_mul_pow`, `hasSum_poissonWeight_mul_pow`, `tsum_matrixReal_mul_pow` —
  the generating functions `(1 - p + pz)^n`, `e^{a(z-1)}` and `(1 - p + pz)^x e^{(1-p)(z-1)}`.
* `matrixReal`, `matrix` — **Georgii (11.26)–(11.27)**; `matrixReal_pos`, `tsum_matrixReal`
  (positive and stochastic), `isTransferMatrix` (Georgii (11.1)).
* `binomialPoissonWeight`, `matrix_pow_apply_singleton` — **Georgii (11.32)**,
  `Q^n(x, ·) = ℓ(x, p^n, ·) ∗ 𝔭(1 - p^n, ·)`; `matrix_pow_apply_zero` is its value at `y = 0`.
* `tendsto_matrix_pow_apply_singleton`, `tendsto_matrix_pow_apply_singleton_entrance`,
  `exists_tendsto_mul_pow_of_tendsto_ratio`,
  `exists_tendsto_matrix_pow_apply_singleton_of_tendsto_ratio` — **Georgii Theorem (11.31),
  Step 1**: `x_n p^n → u` implies `Q^{n+i}(x_n, ·) → ℓ^u_i`, and a positive limit of the ratios
  `Q^{n-1}(x_n, 0)/Q^n(x_n, 0)` forces `x_n p^n` to converge.
* `poissonWeight_one_mul_matrixReal_comm` — **Georgii (11.28)**, reversibility of `α = 𝔭(1, ·)`:
  `α(x) Q(x, y) = α(y) Q(y, x)`, both sides being the symmetric sum
  `∑_{k ≤ x ∧ y} c_k q^{x-k} q^{y-k}/((x-k)!(y-k)!)` (`reversibleSummand`).
* `tsum_poissonWeight_mul_matrixReal` — `𝔭(a, ·) Q = 𝔭(a p + q, ·)`, the computation of `ℓ^u_i Q`.
* `entrance`, `isEntranceLaw`, `rightReal`, `right`, `tsum_matrixReal_mul_rightReal`,
  `tsum_poissonWeight_mul_rightReal`, `isBoundaryLaw`, `chain` — **Georgii (11.29)**: the full
  two-parameter boundary law `{ℓ^u_i, e^{-uv} r^v_i}` and its Markov chain `μ^{u,v}`.
* `chain_intervalCylinder_self` — **Georgii (11.30)**,
  `μ^{u,v}(σ_i = x) = 𝔭((1 + u p^i)(1 + v p^{-i}), x)`.
* `eq_of_chain_eq` — **Georgii, before (11.31)**: the `μ^{u,v}` are pairwise distinct.
* `not_mem_invariantG_chain`, `injective_map_shift_chain`, `infinite_extremePoints_G`,
  `not_countable_G` — **the phase transition**: `μ^{u,0}` is not shift invariant for `u > 0`, its
  translates are pairwise distinct, `ex 𝒢(γ^Q)` is infinite and `𝒢(γ^Q)` is uncountable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Nat unitInterval

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov.SpitzerCox

/-! ## Georgii (11.20)–(11.25): binomial and Poisson weights -/

/-- **Georgii (11.20).** The binomial weight `ℓ(n, p, k) = C(n,k) p^k (1-p)^{n-k}`; it is the
mass that Mathlib's `ProbabilityTheory.binomial` puts on `{k}`
(`binomialWeight_eq_binomial_real`). -/
def binomialWeight (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := n.choose k * p ^ k * (1 - p) ^ (n - k)

/-- **Georgii (11.21).** The Poisson weight `𝔭(a, k) = e^{-a} a^k / k!`.

For `0 ≤ a` this is the mass that Mathlib's `ProbabilityTheory.poissonMeasure` puts on `{k}`
(`poissonWeight_eq_poissonMeasure_real`, `poissonWeight_eq_poissonMeasure_real_toNNReal`), and
every fact about it below that needs a sign is taken from there. It is *not* an abbreviation for
that mass, because Mathlib's rate is an `ℝ≥0` while several of Georgii's identities are
identities of real polynomials in the rate that hold with no sign hypothesis at all:
`sum_poissonWeight_mul_poissonWeight` (11.24) for arbitrary real rates, and
`hasSum_poissonWeight_mul_binomialWeight` (11.25),
`poissonWeight_one_mul_binomialWeight_mul_poissonWeight` and
`poissonWeight_one_mul_matrixReal_comm` (11.28) for arbitrary real survival probability `p`, hence
for the possibly negative rates `a * p` and `1 - p`. -/
def poissonWeight (a : ℝ) (k : ℕ) : ℝ := Real.exp (-a) * a ^ k / k !

lemma binomialWeight_eq_binomial_real (n k : ℕ) (p : I) :
    binomialWeight n p k = Bin(n, p).real {k} := (binomial_real_singleton n k p).symm

lemma poissonWeight_eq_poissonMeasure_real (a : ℝ≥0) (k : ℕ) :
    poissonWeight a k = Po(a).real {k} := (poissonMeasure_real_singleton a k).symm

section Weights

/-- **Georgii (11.21) against Mathlib, at a nonnegative real rate.** `𝔭(a, ·)` is the one-point
mass of `ProbabilityTheory.poissonMeasure` at rate `a.toNNReal`. -/
lemma poissonWeight_eq_poissonMeasure_real_toNNReal {a : ℝ} (ha : 0 ≤ a) (k : ℕ) :
    poissonWeight a k = Po(a.toNNReal).real {k} := by
  rw [← poissonWeight_eq_poissonMeasure_real, Real.coe_toNNReal a ha]

lemma poissonWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ poissonWeight a k := by
  rw [poissonWeight_eq_poissonMeasure_real_toNNReal ha]; exact measureReal_nonneg

lemma poissonWeight_pos {a : ℝ} (ha : 0 < a) (k : ℕ) : 0 < poissonWeight a k := by
  rw [poissonWeight_eq_poissonMeasure_real_toNNReal ha.le]
  exact poissonMeasure_real_singleton_pos k (Real.toNNReal_pos.2 ha)

lemma poissonWeight_zero (a : ℝ) : poissonWeight a 0 = Real.exp (-a) := by
  simp [poissonWeight]

lemma hasSum_poissonWeight {a : ℝ} (ha : 0 ≤ a) : HasSum (poissonWeight a) 1 := by
  have h := hasSum_one_poissonMeasure a.toNNReal
  rwa [Real.coe_toNNReal a ha] at h

lemma summable_poissonWeight {a : ℝ} (ha : 0 ≤ a) : Summable (poissonWeight a) :=
  (hasSum_poissonWeight ha).summable

lemma tsum_poissonWeight {a : ℝ} (ha : 0 ≤ a) : ∑' k : ℕ, poissonWeight a k = 1 :=
  (hasSum_poissonWeight ha).tsum_eq

/-- `∑_j x^j / j! = e^x`, the Poisson weights with the exponential factor removed. -/
lemma hasSum_pow_div_factorial {a : ℝ} (ha : 0 ≤ a) :
    HasSum (fun j : ℕ ↦ a ^ j / j !) (Real.exp a) := by
  have h := (hasSum_poissonWeight ha).mul_left (Real.exp a)
  rw [mul_one] at h
  refine h.congr_fun fun j ↦ ?_
  simp only [poissonWeight]
  rw [← mul_div_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

lemma binomialWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    0 ≤ binomialWeight n p k := by
  have : (0 : ℝ) ≤ 1 - p := by linarith
  simp only [binomialWeight]; positivity

lemma binomialWeight_eq_zero {p : ℝ} {n k : ℕ} (h : n < k) : binomialWeight n p k = 0 := by
  simp [binomialWeight, Nat.choose_eq_zero_of_lt h]

lemma sum_binomialWeight (p : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binomialWeight n p k = 1 := by
  have h : (p + (1 - p)) ^ n = ∑ k ∈ Finset.range (n + 1), p ^ k * (1 - p) ^ (n - k)
      * (n.choose k) := add_pow p (1 - p) n
  rw [show p + (1 - p) = 1 by ring, one_pow] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ ↦ by simp only [binomialWeight]; ring

lemma hasSum_binomialWeight (p : ℝ) (n : ℕ) :
    HasSum (binomialWeight n p) 1 := by
  have h : HasSum (binomialWeight n p)
      (∑ k ∈ Finset.range (n + 1), binomialWeight n p k) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦
      binomialWeight_eq_zero (by simpa [Nat.lt_succ_iff] using hk)
  rwa [sum_binomialWeight p n] at h

lemma summable_binomialWeight (p : ℝ) (n : ℕ) :
    Summable (binomialWeight n p) := (hasSum_binomialWeight p n).summable

/-- **Georgii (11.24).** `𝔭(a, ·) ∗ 𝔭(b, ·) = 𝔭(a + b, ·)`. -/
lemma sum_poissonWeight_mul_poissonWeight (a b : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), poissonWeight a k * poissonWeight b (n - k)
      = poissonWeight (a + b) n := by
  have key : ∀ k ∈ Finset.range (n + 1), poissonWeight a k * poissonWeight b (n - k)
      = Real.exp (-(a + b)) / n ! * (a ^ k * b ^ (n - k) * (n.choose k)) := by
    intro k hk
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hfac : ((n.choose k : ℝ)) * (k ! : ℝ) * (((n - k)! : ℕ) : ℝ) = (n ! : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.choose_mul_factorial_mul_factorial hk)
    have hk0 : ((k ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    have hnk0 : (((n - k)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hn0 : ((n ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    have hchoose : ((n.choose k : ℝ)) = (n ! : ℝ) / ((k ! : ℝ) * (((n - k)! : ℕ) : ℝ)) := by
      rw [eq_div_iff (by positivity)]
      linarith [hfac]
    simp only [poissonWeight, neg_add, Real.exp_add, hchoose]
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← add_pow]
  simp only [poissonWeight]
  ring

/-- **Georgii (11.25).** `∑_x 𝔭(a, x) ℓ(x, p, k) = 𝔭(a p, k)`: thinning a Poisson number of
individuals by independent survival with probability `p` gives a Poisson distribution. -/
lemma hasSum_poissonWeight_mul_binomialWeight {a p : ℝ} (ha : 0 ≤ a) (hp1 : p ≤ 1) (k : ℕ) :
    HasSum (fun x : ℕ ↦ poissonWeight a x * binomialWeight x p k) (poissonWeight (a * p) k) := by
  have hc : (0 : ℝ) ≤ a * (1 - p) := mul_nonneg ha (by linarith)
  have hshift : ∀ j : ℕ, poissonWeight a (j + k) * binomialWeight (j + k) p k
      = (Real.exp (-a) * (a * p) ^ k / k !) * ((a * (1 - p)) ^ j / j !) := by
    intro j
    have hfac : (((j + k).choose k : ℝ)) * (k ! : ℝ) * ((j ! : ℕ) : ℝ) = (((j + k)! : ℕ) : ℝ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k j)
      simp only [Nat.add_sub_cancel] at h
      exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) h
    have hk0 : ((k ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    have hj0 : ((j ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    have hjk0 : ((((j + k))! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hchoose : (((j + k).choose k : ℝ))
        = ((((j + k))! : ℕ) : ℝ) / ((k ! : ℝ) * ((j ! : ℕ) : ℝ)) := by
      rw [eq_div_iff (by positivity)]
      linarith [hfac]
    simp only [poissonWeight, binomialWeight, Nat.add_sub_cancel, hchoose, mul_pow]
    field_simp
    ring
  have hbase : HasSum (fun j : ℕ ↦ (Real.exp (-a) * (a * p) ^ k / k !)
      * ((a * (1 - p)) ^ j / j !))
      ((Real.exp (-a) * (a * p) ^ k / k !) * Real.exp (a * (1 - p))) :=
    (hasSum_pow_div_factorial hc).mul_left _
  have hadd : HasSum (fun j : ℕ ↦ poissonWeight a (j + k) * binomialWeight (j + k) p k)
      ((Real.exp (-a) * (a * p) ^ k / k !) * Real.exp (a * (1 - p))) :=
    hbase.congr_fun fun j ↦ hshift j
  have hzero : ∀ i ∈ Finset.range k, poissonWeight a i * binomialWeight i p k = 0 := by
    intro i hi
    rw [binomialWeight_eq_zero (by simpa using hi), mul_zero]
  have hsum :=
    (hasSum_nat_add_iff (f := fun x : ℕ ↦ poissonWeight a x * binomialWeight x p k) k).1 hadd
  rw [Finset.sum_eq_zero hzero, add_zero] at hsum
  have he : Real.exp (-a) * Real.exp (a * (1 - p)) = Real.exp (-(a * p)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hX : Real.exp (-a) * (a * p) ^ k / (k ! : ℝ) * Real.exp (a * (1 - p))
      = poissonWeight (a * p) k := by
    rw [poissonWeight, div_mul_eq_mul_div, mul_right_comm, he]
  rwa [hX] at hsum

/-- **Georgii (11.22).** `ℓ(m, p, ·) ∗ ℓ(n, p, ·) = ℓ(m + n, p, ·)`: pooling two independent
groups of `m` and `n` individuals, each surviving with probability `p`. -/
lemma sum_binomialWeight_mul_binomialWeight (p : ℝ) (m n k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), binomialWeight m p j * binomialWeight n p (k - j)
      = binomialWeight (m + n) p k := by
  have key : ∀ j ∈ Finset.range (k + 1), binomialWeight m p j * binomialWeight n p (k - j)
      = ((m.choose j : ℝ) * (n.choose (k - j) : ℝ)) * (p ^ k * (1 - p) ^ (m + n - k)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rcases lt_or_ge m j with hjm | hjm
    · simp [binomialWeight, Nat.choose_eq_zero_of_lt hjm]
    rcases lt_or_ge n (k - j) with hn | hn
    · simp [binomialWeight, Nat.choose_eq_zero_of_lt hn]
    have h1 : p ^ k = p ^ j * p ^ (k - j) := by rw [← pow_add]; congr 1; omega
    have h2 : (1 - p) ^ (m + n - k) = (1 - p) ^ (m - j) * (1 - p) ^ (n - (k - j)) := by
      rw [← pow_add]; congr 1; omega
    simp only [binomialWeight]
    rw [h1, h2]; ring
  have hvan : ∑ j ∈ Finset.range (k + 1), m.choose j * n.choose (k - j) = (m + n).choose k := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hvanR : ∑ j ∈ Finset.range (k + 1), ((m.choose j : ℝ) * (n.choose (k - j) : ℝ))
      = ((m + n).choose k : ℝ) := by exact_mod_cast hvan
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul, hvanR]
  simp only [binomialWeight]; ring

/-- **Georgii (11.23), in the form of a finite sum.** `∑_{k ≤ n} ℓ(n, p₁, k) ℓ(k, p₂, j)
= ℓ(n, p₁ p₂, j)`. -/
lemma sum_binomialWeight_mul_binomialWeight_left (p₁ p₂ : ℝ) (n j : ℕ) :
    ∑ k ∈ Finset.range (n + 1), binomialWeight n p₁ k * binomialWeight k p₂ j
      = binomialWeight n (p₁ * p₂) j := by
  rcases lt_or_ge n j with hjn | hjn
  · rw [binomialWeight_eq_zero hjn]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    rw [binomialWeight_eq_zero
      (lt_of_le_of_lt (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hjn), mul_zero]
  have hsub : Finset.Ico j (n + 1) ⊆ Finset.range (n + 1) := by
    rw [Finset.range_eq_Ico]; exact Finset.Ico_subset_Ico (Nat.zero_le j) le_rfl
  have hzero : ∀ k ∈ Finset.range (n + 1), k ∉ Finset.Ico j (n + 1) →
      binomialWeight n p₁ k * binomialWeight k p₂ j = 0 := by
    intro k hk hk'
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Ico, not_and, not_lt] at hk'
    rcases lt_or_ge k j with h | h
    · rw [binomialWeight_eq_zero h, mul_zero]
    · exact absurd (hk' h) (by omega)
  rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
    show n + 1 - j = n - j + 1 by omega]
  have key : ∀ i ∈ Finset.range (n - j + 1),
      binomialWeight n p₁ (j + i) * binomialWeight (j + i) p₂ j
      = ((n.choose j : ℝ) * (p₁ * p₂) ^ j)
        * ((((n - j).choose i : ℝ)) * (p₁ * (1 - p₂)) ^ i * (1 - p₁) ^ (n - j - i)) := by
    intro i hi
    have hi' : i ≤ n - j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hchoose : (n.choose (j + i) : ℝ) * (((j + i).choose j : ℝ))
        = (n.choose j : ℝ) * (((n - j).choose i : ℝ)) := by
      have h := Nat.choose_mul (n := n) (k := j + i) (s := j) (Nat.le_add_right j i)
      simp only [Nat.add_sub_cancel_left] at h
      exact_mod_cast h
    have hq1 : (1 - p₁) ^ (n - (j + i)) = (1 - p₁) ^ (n - j - i) := by congr 1; omega
    simp only [binomialWeight, Nat.add_sub_cancel_left, pow_add, mul_pow, hq1]
    linear_combination (p₁ ^ j * p₁ ^ i * (1 - p₁) ^ (n - j - i) * p₂ ^ j * (1 - p₂) ^ i)
      * hchoose
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have hadd : ∑ i ∈ Finset.range (n - j + 1),
      ((((n - j).choose i : ℝ)) * (p₁ * (1 - p₂)) ^ i * (1 - p₁) ^ (n - j - i))
      = (1 - p₁ * p₂) ^ (n - j) := by
    rw [show (1 : ℝ) - p₁ * p₂ = p₁ * (1 - p₂) + (1 - p₁) by ring, add_pow]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hadd]
  simp only [binomialWeight]

/-- **Georgii (11.23).** `∑_k ℓ(n, p₁, k) ℓ(k, p₂, ·) = ℓ(n, p₁ p₂, ·)`: thinning with survival
probability `p₁` and then with `p₂` is thinning with `p₁ p₂`. -/
lemma hasSum_binomialWeight_mul_binomialWeight (p₁ p₂ : ℝ) (n j : ℕ) :
    HasSum (fun k : ℕ ↦ binomialWeight n p₁ k * binomialWeight k p₂ j)
      (binomialWeight n (p₁ * p₂) j) := by
  have hfin : HasSum (fun k : ℕ ↦ binomialWeight n p₁ k * binomialWeight k p₂ j)
      (∑ k ∈ Finset.range (n + 1), binomialWeight n p₁ k * binomialWeight k p₂ j) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦ by
      rw [binomialWeight_eq_zero (by simpa [Nat.lt_succ_iff] using hk), zero_mul]
  rwa [sum_binomialWeight_mul_binomialWeight_left p₁ p₂ n j] at hfin

/-- The probability generating function of the binomial weights **(11.20)**:
`∑_k ℓ(n, p, k) z^k = (1 - p + p z)^n`. -/
lemma hasSum_binomialWeight_mul_pow (p z : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ ↦ binomialWeight n p k * z ^ k) ((1 - p + p * z) ^ n) := by
  have hfin : HasSum (fun k : ℕ ↦ binomialWeight n p k * z ^ k)
      (∑ k ∈ Finset.range (n + 1), binomialWeight n p k * z ^ k) :=
    hasSum_sum_of_ne_finset_zero fun k hk ↦ by
      rw [binomialWeight_eq_zero (by simpa [Nat.lt_succ_iff] using hk), zero_mul]
  have h : (1 - p + p * z) ^ n = ∑ k ∈ Finset.range (n + 1), binomialWeight n p k * z ^ k := by
    rw [show (1 : ℝ) - p + p * z = p * z + (1 - p) by ring, add_pow]
    exact Finset.sum_congr rfl fun k _ ↦ by simp only [binomialWeight, mul_pow]; ring
  rwa [h]

lemma summable_binomialWeight_mul_pow (p z : ℝ) (n : ℕ) :
    Summable fun k : ℕ ↦ binomialWeight n p k * z ^ k :=
  (hasSum_binomialWeight_mul_pow p z n).summable

/-- The probability generating function of the Poisson weights **(11.21)**:
`∑_k 𝔭(a, k) z^k = e^{a (z - 1)}`. -/
lemma hasSum_poissonWeight_mul_pow {a z : ℝ} (ha : 0 ≤ a) (hz : 0 ≤ z) :
    HasSum (fun k : ℕ ↦ poissonWeight a k * z ^ k) (Real.exp (a * (z - 1))) := by
  have h : HasSum (fun k : ℕ ↦ Real.exp (-a) * ((a * z) ^ k / k !))
      (Real.exp (-a) * Real.exp (a * z)) :=
    (hasSum_pow_div_factorial (mul_nonneg ha hz)).mul_left _
  rw [← Real.exp_add, show -a + a * z = a * (z - 1) by ring] at h
  exact h.congr_fun fun k ↦ by simp only [poissonWeight, mul_pow]; ring

lemma summable_poissonWeight_mul_pow {a z : ℝ} (ha : 0 ≤ a) (hz : 0 ≤ z) :
    Summable fun k : ℕ ↦ poissonWeight a k * z ^ k :=
  (hasSum_poissonWeight_mul_pow ha hz).summable

end Weights

/-! ## Georgii (11.26)–(11.27): the matrix `Q` -/

section Matrix

/-- **Georgii (11.26)–(11.27).** `Q(x, y) = ∑_{k ≤ x ∧ y} ℓ(x, p, k) 𝔭(1 - p, y - k)`, the
transition matrix of a population whose members survive independently with probability `p` and
which receives an independent `Poisson(1-p)` number of immigrants. (The binomial weight vanishes
for `k > x`, so summing `k` over `range (y+1)` is Georgii's `k ≤ x ∧ y`.) -/
def matrixReal (p : ℝ) (x y : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (y + 1), binomialWeight x p k * poissonWeight (1 - p) (y - k)

variable {p : ℝ}

lemma binomialWeight_zero_pos (hp1 : p < 1) (x : ℕ) : 0 < binomialWeight x p 0 := by
  have : (0 : ℝ) < 1 - p := by linarith
  simp only [binomialWeight, Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero]
  positivity

lemma matrixReal_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : ℕ) : 0 ≤ matrixReal p x y :=
  Finset.sum_nonneg fun k _ ↦
    mul_nonneg (binomialWeight_nonneg hp0 hp1 x k) (poissonWeight_nonneg (by linarith) _)

/-- `Q` is a positive matrix: the `k = 0` term `(1-p)^x 𝔭(1-p, y)` is already positive. -/
lemma matrixReal_pos (hp0 : 0 < p) (hp1 : p < 1) (x y : ℕ) : 0 < matrixReal p x y := by
  refine Finset.sum_pos' (fun k _ ↦ mul_nonneg (binomialWeight_nonneg hp0.le hp1.le x k)
    (poissonWeight_nonneg (by linarith) _)) ⟨0, Finset.mem_range.2 (Nat.succ_pos y), ?_⟩
  exact mul_pos (binomialWeight_zero_pos hp1 x) (poissonWeight_pos (by linarith) _)

lemma summable_prod_binomialWeight_poissonWeight (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) :
    Summable fun z : ℕ × ℕ ↦ binomialWeight x p z.1 * poissonWeight (1 - p) z.2 :=
  (summable_binomialWeight p x).mul_of_nonneg (summable_poissonWeight (by linarith))
    (fun k ↦ binomialWeight_nonneg hp0 hp1 x k) (fun j ↦ poissonWeight_nonneg (by linarith) j)

lemma summable_matrixReal (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) :
    Summable fun y ↦ matrixReal p x y :=
  summable_sum_mul_range_of_summable_mul (summable_prod_binomialWeight_poissonWeight hp0 hp1 x)

/-- **`Q` is stochastic**: the Cauchy product of two probability weights. -/
lemma tsum_matrixReal (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) :
    ∑' y : ℕ, matrixReal p x y = 1 := by
  have h := (summable_binomialWeight p x).tsum_mul_tsum_eq_tsum_sum_range
    (summable_poissonWeight (a := 1 - p) (by linarith))
    (summable_prod_binomialWeight_poissonWeight hp0 hp1 x)
  rw [(hasSum_binomialWeight p x).tsum_eq,
    tsum_poissonWeight (show (0 : ℝ) ≤ 1 - p by linarith), one_mul] at h
  exact h.symm

/-- **Georgii's computation of `ℓ^u_i Q` at (11.29).** `𝔭(a, ·) Q = 𝔭(a p + (1-p), ·)`: (11.25)
thins the binomial part to `𝔭(a p, ·)`, and (11.24) convolves it with `𝔭(1-p, ·)`. -/
lemma tsum_poissonWeight_mul_matrixReal {a : ℝ} (ha : 0 ≤ a) (hp1 : p ≤ 1) (y : ℕ) :
    ∑' x : ℕ, poissonWeight a x * matrixReal p x y = poissonWeight (a * p + (1 - p)) y := by
  have hstep : ∀ x : ℕ, poissonWeight a x * matrixReal p x y
      = ∑ k ∈ Finset.range (y + 1),
          poissonWeight a x * binomialWeight x p k * poissonWeight (1 - p) (y - k) := by
    intro x
    simp only [matrixReal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hsummand : ∀ k ∈ Finset.range (y + 1), Summable fun x : ℕ ↦
      poissonWeight a x * binomialWeight x p k * poissonWeight (1 - p) (y - k) := fun k _ ↦
    ((hasSum_poissonWeight_mul_binomialWeight ha hp1 k).summable).mul_right _
  rw [tsum_congr hstep, Summable.tsum_finsetSum hsummand]
  have hk : ∀ k ∈ Finset.range (y + 1),
      (∑' x : ℕ, poissonWeight a x * binomialWeight x p k * poissonWeight (1 - p) (y - k))
        = poissonWeight (a * p) k * poissonWeight (1 - p) (y - k) := by
    intro k _
    rw [Summable.tsum_mul_right _ (hasSum_poissonWeight_mul_binomialWeight ha hp1 k).summable,
      (hasSum_poissonWeight_mul_binomialWeight ha hp1 k).tsum_eq]
  rw [Finset.sum_congr rfl hk, sum_poissonWeight_mul_poissonWeight]

lemma summable_poissonWeight_mul_matrixReal {a : ℝ} (ha : 0 ≤ a) (hp1 : p ≤ 1) (y : ℕ) :
    Summable fun x : ℕ ↦ poissonWeight a x * matrixReal p x y := by
  have hstep : (fun x : ℕ ↦ poissonWeight a x * matrixReal p x y)
      = fun x : ℕ ↦ ∑ k ∈ Finset.range (y + 1),
          poissonWeight a x * binomialWeight x p k * poissonWeight (1 - p) (y - k) := by
    funext x
    simp only [matrixReal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hstep]
  exact summable_sum fun k _ ↦
    ((hasSum_poissonWeight_mul_binomialWeight ha hp1 k).summable).mul_right _

/-- The summand of Georgii's reversibility computation (11.28):
`c_k q^{x-k} q^{y-k} / ((x-k)! (y-k)!)` with `c_k = e^{-1-q} p^k / k!` and `q = 1 - p`. It is
visibly symmetric in `x` and `y` (`reversibleSummand_comm`). -/
def reversibleSummand (p : ℝ) (k x y : ℕ) : ℝ :=
  Real.exp (-1 - (1 - p)) * p ^ k * ((1 - p) ^ (x - k) * (1 - p) ^ (y - k))
    / ((k ! : ℝ) * (((x - k)! : ℕ) : ℝ) * (((y - k)! : ℕ) : ℝ))

lemma reversibleSummand_comm (p : ℝ) (k x y : ℕ) :
    reversibleSummand p k x y = reversibleSummand p k y x := by
  simp only [reversibleSummand]; ring

/-- `α(x) ℓ(x, p, k) 𝔭(1-p, y-k) = c_k q^{x-k} q^{y-k}/((x-k)!(y-k)!)` for `k ≤ x`, where
`α = 𝔭(1, ·)`: the display in Georgii's verification of (11.28). -/
lemma poissonWeight_one_mul_binomialWeight_mul_poissonWeight {k x : ℕ} (hkx : k ≤ x) (y : ℕ) :
    poissonWeight 1 x * (binomialWeight x p k * poissonWeight (1 - p) (y - k))
      = reversibleSummand p k x y := by
  have hfac : (x.choose k : ℝ) * ((k ! : ℕ) : ℝ) * (((x - k)! : ℕ) : ℝ) = ((x ! : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.choose_mul_factorial_mul_factorial hkx)
  have hk0 : ((k ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
  have hxk0 : (((x - k)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hyk0 : (((y - k)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hx0 : ((x ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero x)
  simp only [poissonWeight, binomialWeight, reversibleSummand, one_pow, mul_one,
    show (-1 : ℝ) - (1 - p) = -1 + -(1 - p) by ring, Real.exp_add]
  field_simp
  linear_combination (p ^ k * (1 - p) ^ (x - k) * (1 - p) ^ (y - k)) * hfac

/-- `α(x) Q(x, y)` as a sum of terms symmetric in `x` and `y`, `α = 𝔭(1, ·)`. -/
lemma poissonWeight_one_mul_matrixReal (x y : ℕ) :
    poissonWeight 1 x * matrixReal p x y
      = ∑ k ∈ Finset.range (min x y + 1), reversibleSummand p k x y := by
  have hsub : Finset.range (min x y + 1) ⊆ Finset.range (y + 1) :=
    fun k hk ↦ Finset.mem_range.2
      ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ (min_le_right x y)))
  have hzero : ∀ k ∈ Finset.range (y + 1), k ∉ Finset.range (min x y + 1) →
      poissonWeight 1 x * (binomialWeight x p k * poissonWeight (1 - p) (y - k)) = 0 := by
    intro k hk hk'
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    simp only [Finset.mem_range, Nat.lt_succ_iff, not_le] at hk'
    rcases min_lt_iff.1 hk' with h | h
    · rw [binomialWeight_eq_zero h, zero_mul, mul_zero]
    · exact absurd h (not_lt.2 hk)
  rw [matrixReal, Finset.mul_sum, ← Finset.sum_subset hsub hzero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkx : k ≤ x :=
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans (min_le_left x y)
  exact poissonWeight_one_mul_binomialWeight_mul_poissonWeight hkx y

/-- **Georgii (11.28): `α` is a reversible measure for `Q`,** `α(x) Q(x, y) = α(y) Q(y, x)` with
`α = 𝔭(1, ·)`. Both sides equal `∑_{k ≤ x ∧ y} c_k q^{x-k} q^{y-k}/((x-k)!(y-k)!)`. -/
theorem poissonWeight_one_mul_matrixReal_comm (x y : ℕ) :
    poissonWeight 1 x * matrixReal p x y = poissonWeight 1 y * matrixReal p y x := by
  rw [poissonWeight_one_mul_matrixReal, poissonWeight_one_mul_matrixReal, min_comm]
  exact Finset.sum_congr rfl fun k _ ↦ reversibleSummand_comm p k x y

/-- The `y`-th term of the generating function of `Q(x, ·)` as a Cauchy-product term of the
binomial and the Poisson generating functions. -/
lemma matrixReal_mul_pow (z : ℝ) (x y : ℕ) :
    matrixReal p x y * z ^ y = ∑ k ∈ Finset.range (y + 1),
      binomialWeight x p k * z ^ k * (poissonWeight (1 - p) (y - k) * z ^ (y - k)) := by
  rw [matrixReal, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hky : k ≤ y := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hzy : z ^ y = z ^ k * z ^ (y - k) := by rw [← pow_add, Nat.add_sub_cancel' hky]
  rw [hzy]; ring

/-- The Cauchy-product summability behind `tsum_matrixReal_mul_pow`. -/
lemma summable_prod_binomialWeight_poissonWeight_mul_pow (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {z : ℝ}
    (hz : 0 ≤ z) (x : ℕ) : Summable fun w : ℕ × ℕ ↦
      (binomialWeight x p w.1 * z ^ w.1) * (poissonWeight (1 - p) w.2 * z ^ w.2) :=
  (summable_binomialWeight_mul_pow p z x).mul_of_nonneg
    (summable_poissonWeight_mul_pow (show (0 : ℝ) ≤ 1 - p by linarith) hz)
    (fun k ↦ mul_nonneg (binomialWeight_nonneg hp0 hp1 x k) (pow_nonneg hz k))
    (fun j ↦ mul_nonneg (poissonWeight_nonneg (by linarith) j) (pow_nonneg hz j))

lemma summable_matrixReal_mul_pow (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z) (x : ℕ) :
    Summable fun y : ℕ ↦ matrixReal p x y * z ^ y := by
  simp_rw [matrixReal_mul_pow]
  exact summable_sum_mul_range_of_summable_mul
    (f := fun k : ℕ ↦ binomialWeight x p k * z ^ k)
    (g := fun j : ℕ ↦ poissonWeight (1 - p) j * z ^ j)
    (summable_prod_binomialWeight_poissonWeight_mul_pow hp0 hp1 hz x)

/-- **The generating function of Georgii's `Q(x, ·)` at (11.26).** `Q(x, ·)` is the convolution
of `ℓ(x, p, ·)` with `𝔭(1 - p, ·)`, so
`∑_y Q(x, y) z^y = (1 - p + p z)^x e^{(1-p)(z-1)}` for `z ≥ 0`. -/
lemma tsum_matrixReal_mul_pow (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z) (x : ℕ) :
    ∑' y : ℕ, matrixReal p x y * z ^ y
      = (1 - p + p * z) ^ x * Real.exp ((1 - p) * (z - 1)) := by
  have hb := summable_binomialWeight_mul_pow p z x
  have hpo := summable_poissonWeight_mul_pow (show (0 : ℝ) ≤ 1 - p by linarith) hz
  have h := hb.tsum_mul_tsum_eq_tsum_sum_range hpo
    (summable_prod_binomialWeight_poissonWeight_mul_pow hp0 hp1 hz x)
  rw [(hasSum_binomialWeight_mul_pow p z x).tsum_eq,
    (hasSum_poissonWeight_mul_pow (show (0 : ℝ) ≤ 1 - p by linarith) hz).tsum_eq] at h
  rw [h]
  exact tsum_congr fun y ↦ matrixReal_mul_pow z x y

end Matrix

/-! ## Georgii (11.32): the powers of `Q` -/

section Powers

/-- The weight `ℓ(x, a, ·) ∗ 𝔭(b, ·)`: the law of the sum of a `Binomial(x, a)` variable and an
independent `Poisson(b)` variable. Georgii's matrix (11.26) is `Q = ℓ(·, p, ·) ∗ 𝔭(1 - p, ·)`
(`matrixReal_eq_binomialPoissonWeight`), and **(11.32)** says that its `n`-th power is
`ℓ(·, p^n, ·) ∗ 𝔭(1 - p^n, ·)`: after `n` time units each of the original `x` individuals is
still alive with probability `p^n`, and the immigrants of the intermediate steps have
accumulated to an independent `Poisson(1 - p^n)` number. -/
def binomialPoissonWeight (a b : ℝ) (x y : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (y + 1), binomialWeight x a k * poissonWeight b (y - k)

/-- **Georgii (11.26)** is the case `a = p`, `b = 1 - p` of `binomialPoissonWeight`. -/
lemma matrixReal_eq_binomialPoissonWeight (p : ℝ) (x y : ℕ) :
    matrixReal p x y = binomialPoissonWeight p (1 - p) x y := rfl

variable {a b p q : ℝ}

lemma binomialPoissonWeight_nonneg (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (x y : ℕ) :
    0 ≤ binomialPoissonWeight a b x y :=
  Finset.sum_nonneg fun k _ ↦
    mul_nonneg (binomialWeight_nonneg ha0 ha1 x k) (poissonWeight_nonneg hb _)

/-- `ℓ(x, a, ·) ∗ 𝔭(b, ·)` summed over the *binomial* index: `ℓ(x, a, k)` vanishes for `k > x`,
so the convolution may be summed over `range (x + 1)`, at the price of truncating the Poisson
factor. Both forms are the sum over `k ≤ x ∧ y`. -/
lemma binomialPoissonWeight_eq_sum_range (a b : ℝ) (x y : ℕ) :
    binomialPoissonWeight a b x y
      = ∑ k ∈ Finset.range (x + 1),
          binomialWeight x a k * (if k ≤ y then poissonWeight b (y - k) else 0) := by
  have hsub₁ : Finset.range (min x y + 1) ⊆ Finset.range (y + 1) := fun k hk ↦
    Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ (min_le_right x y)))
  have hsub₂ : Finset.range (min x y + 1) ⊆ Finset.range (x + 1) := fun k hk ↦
    Finset.mem_range.2 ((Finset.mem_range.1 hk).trans_le (Nat.succ_le_succ (min_le_left x y)))
  have h₁ : binomialPoissonWeight a b x y
      = ∑ k ∈ Finset.range (min x y + 1), binomialWeight x a k * poissonWeight b (y - k) := by
    refine (Finset.sum_subset hsub₁ fun k hk hk' ↦ ?_).symm
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk hk'
    rw [binomialWeight_eq_zero (by omega), zero_mul]
  have h₂ : (∑ k ∈ Finset.range (x + 1),
        binomialWeight x a k * (if k ≤ y then poissonWeight b (y - k) else 0))
      = ∑ k ∈ Finset.range (min x y + 1),
          binomialWeight x a k * (if k ≤ y then poissonWeight b (y - k) else 0) := by
    refine (Finset.sum_subset hsub₂ fun k hk hk' ↦ ?_).symm
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk hk'
    rw [ite_eq_right (by omega), mul_zero]
  rw [h₁, h₂]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [ite_eq_left (by omega)]

/-- The `k`-th slice of Georgii's double Cauchy product: an independent `Poisson(b)` immigration
of `l` individuals joins `k` survivors, and the resulting `l + k` individuals are thinned by `p`.
By (11.22) the thinning splits, and by (11.25) the Poisson part becomes `𝔭(b p, ·)`. -/
private lemma hasSum_poissonWeight_mul_binomialWeight_add (hb : 0 ≤ b) (hp1 : p ≤ 1) (k m : ℕ) :
    HasSum (fun l : ℕ ↦ poissonWeight b l * binomialWeight (l + k) p m)
      (∑ i ∈ Finset.range (m + 1), binomialWeight k p i * poissonWeight (b * p) (m - i)) := by
  have hterm : ∀ l : ℕ, poissonWeight b l * binomialWeight (l + k) p m
      = ∑ i ∈ Finset.range (m + 1),
          binomialWeight k p i * (poissonWeight b l * binomialWeight l p (m - i)) := by
    intro l
    rw [add_comm l k, ← sum_binomialWeight_mul_binomialWeight p k l m, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  exact (hasSum_sum fun i _ ↦
    (hasSum_poissonWeight_mul_binomialWeight hb hp1 (m - i)).mul_left
      (binomialWeight k p i)).congr_fun hterm

/-- The same slice, indexed by the total population `w = l + k` rather than by the number `l` of
immigrants. -/
private lemma hasSum_ite_poissonWeight_mul_binomialWeight (hb : 0 ≤ b) (hp1 : p ≤ 1) (k m : ℕ) :
    HasSum (fun w : ℕ ↦ (if k ≤ w then poissonWeight b (w - k) else 0) * binomialWeight w p m)
      (∑ i ∈ Finset.range (m + 1), binomialWeight k p i * poissonWeight (b * p) (m - i)) := by
  set F : ℕ → ℝ :=
    fun w ↦ (if k ≤ w then poissonWeight b (w - k) else 0) * binomialWeight w p m with hF
  have hshift : ∀ l : ℕ, F (l + k) = poissonWeight b l * binomialWeight (l + k) p m := fun l ↦ by
    simp [hF, Nat.le_add_left k l]
  have hzero : ∀ i ∈ Finset.range k, F i = 0 := fun i hi ↦ by
    simp only [Finset.mem_range] at hi
    simp [hF, Nat.not_le.2 hi]
  have h := (hasSum_nat_add_iff (f := F) k).1
    ((hasSum_poissonWeight_mul_binomialWeight_add hb hp1 k m).congr_fun hshift)
  rwa [Finset.sum_eq_zero hzero, add_zero] at h

/-- **Thinning `ℓ(x, a, ·) ∗ 𝔭(b, ·)` by `p`.** Each of the two independent summands is thinned
separately: (11.23) turns `ℓ(x, a, ·)` into `ℓ(x, a p, ·)` and (11.25) turns `𝔭(b, ·)` into
`𝔭(b p, ·)`. -/
lemma hasSum_binomialPoissonWeight_mul_binomialWeight (hb : 0 ≤ b) (hp1 : p ≤ 1) (x m : ℕ) :
    HasSum (fun w : ℕ ↦ binomialPoissonWeight a b x w * binomialWeight w p m)
      (binomialPoissonWeight (a * p) (b * p) x m) := by
  have hterm : ∀ w : ℕ, binomialPoissonWeight a b x w * binomialWeight w p m
      = ∑ k ∈ Finset.range (x + 1), binomialWeight x a k *
          ((if k ≤ w then poissonWeight b (w - k) else 0) * binomialWeight w p m) := fun w ↦ by
    rw [binomialPoissonWeight_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hsum := (hasSum_sum fun k (_ : k ∈ Finset.range (x + 1)) ↦
    (hasSum_ite_poissonWeight_mul_binomialWeight hb hp1 k m).mul_left
      (binomialWeight x a k)).congr_fun hterm
  have hval : (∑ k ∈ Finset.range (x + 1), binomialWeight x a k *
      ∑ i ∈ Finset.range (m + 1), binomialWeight k p i * poissonWeight (b * p) (m - i))
      = binomialPoissonWeight (a * p) (b * p) x m := by
    have h1 : ∀ k ∈ Finset.range (x + 1), binomialWeight x a k *
        ∑ i ∈ Finset.range (m + 1), binomialWeight k p i * poissonWeight (b * p) (m - i)
        = ∑ i ∈ Finset.range (m + 1),
            binomialWeight x a k * binomialWeight k p i * poissonWeight (b * p) (m - i) :=
      fun k _ ↦ by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    have h2 : ∀ i ∈ Finset.range (m + 1),
        (∑ k ∈ Finset.range (x + 1),
          binomialWeight x a k * binomialWeight k p i * poissonWeight (b * p) (m - i))
        = binomialWeight x (a * p) i * poissonWeight (b * p) (m - i) := fun i _ ↦ by
      rw [← Finset.sum_mul, sum_binomialWeight_mul_binomialWeight_left a p x i]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2,
      binomialPoissonWeight]
  rwa [hval] at hsum

/-- **Convolving the Poisson part**, Georgii's last step in the induction for (11.32):
`(ℓ(x, a, ·) ∗ 𝔭(b, ·)) ∗ 𝔭(q, ·) = ℓ(x, a, ·) ∗ 𝔭(b + q, ·)`, by (11.24). -/
lemma sum_binomialPoissonWeight_mul_poissonWeight (a b q : ℝ) (x y : ℕ) :
    ∑ m ∈ Finset.range (y + 1), binomialPoissonWeight a b x m * poissonWeight q (y - m)
      = binomialPoissonWeight a (b + q) x y := by
  have hterm : ∀ m ∈ Finset.range (y + 1),
      binomialPoissonWeight a b x m * poissonWeight q (y - m)
      = ∑ k ∈ Finset.range (x + 1), binomialWeight x a k *
          ((if k ≤ m then poissonWeight b (m - k) else 0) * poissonWeight q (y - m)) :=
    fun m _ ↦ by
      rw [binomialPoissonWeight_eq_sum_range, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm,
    binomialPoissonWeight_eq_sum_range a (b + q) x y]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  by_cases hky : k ≤ y
  · rw [ite_eq_left hky]
    have hsub : Finset.Ico k (y + 1) ⊆ Finset.range (y + 1) := by
      rw [Finset.range_eq_Ico]; exact Finset.Ico_subset_Ico (Nat.zero_le k) le_rfl
    have hz : ∀ m ∈ Finset.range (y + 1), m ∉ Finset.Ico k (y + 1) →
        (if k ≤ m then poissonWeight b (m - k) else 0) * poissonWeight q (y - m) = 0 := by
      intro m hm hm'
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hm
      simp only [Finset.mem_Ico, not_and, not_lt] at hm'
      rw [ite_eq_right (fun h ↦ absurd (hm' h) (by omega)), zero_mul]
    have hre : ∀ t ∈ Finset.range (y - k + 1),
        (if k ≤ k + t then poissonWeight b (k + t - k) else 0) * poissonWeight q (y - (k + t))
        = poissonWeight b t * poissonWeight q (y - k - t) := by
      intro t ht
      simp only [Finset.mem_range, Nat.lt_succ_iff] at ht
      rw [ite_eq_left (Nat.le_add_right k t)]
      congr 2 <;> omega
    rw [← Finset.sum_subset hsub hz, Finset.sum_Ico_eq_sum_range,
      show y + 1 - k = y - k + 1 from by omega, Finset.sum_congr rfl hre,
      sum_poissonWeight_mul_poissonWeight]
  · rw [ite_eq_right hky]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hm
    rw [ite_eq_right (fun h ↦ hky (h.trans hm)), zero_mul]

/-- **The Chapman–Kolmogorov step of Georgii's induction for (11.32).** Applying the matrix
`ℓ(·, p, ·) ∗ 𝔭(q, ·)` to `ℓ(x, a, ·) ∗ 𝔭(b, ·)` gives `ℓ(x, a p, ·) ∗ 𝔭(b p + q, ·)`:
`hasSum_binomialPoissonWeight_mul_binomialWeight` thins the pair by `p`, and
`sum_binomialPoissonWeight_mul_poissonWeight` adds the new immigrants. -/
lemma hasSum_binomialPoissonWeight_mul_binomialPoissonWeight (hb : 0 ≤ b) (hp1 : p ≤ 1)
    (x y : ℕ) :
    HasSum (fun w : ℕ ↦ binomialPoissonWeight a b x w * binomialPoissonWeight p q w y)
      (binomialPoissonWeight (a * p) (b * p + q) x y) := by
  have hterm : ∀ w : ℕ, binomialPoissonWeight a b x w * binomialPoissonWeight p q w y
      = ∑ m ∈ Finset.range (y + 1),
          binomialPoissonWeight a b x w * binomialWeight w p m * poissonWeight q (y - m) :=
    fun w ↦ by
      have hbp : binomialPoissonWeight p q w y
          = ∑ m ∈ Finset.range (y + 1), binomialWeight w p m * poissonWeight q (y - m) := rfl
      rw [hbp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ ↦ by ring
  have hsum := (hasSum_sum fun m (_ : m ∈ Finset.range (y + 1)) ↦
    (hasSum_binomialPoissonWeight_mul_binomialWeight (a := a) hb hp1 x m).mul_right
      (poissonWeight q (y - m))).congr_fun hterm
  rwa [sum_binomialPoissonWeight_mul_poissonWeight] at hsum

/-- `ℓ(x, 1, ·) ∗ 𝔭(0, ·) = δ_x`: the case `n = 0` of (11.32), where nobody dies and nobody
immigrates. -/
lemma binomialWeight_one (x k : ℕ) : binomialWeight x 1 k = if k = x then 1 else 0 := by
  simp only [binomialWeight, one_pow, mul_one, sub_self]
  rcases lt_trichotomy k x with h | rfl | h
  · rw [zero_pow (by omega), mul_zero, ite_eq_right (by omega)]
  · simp
  · rw [Nat.choose_eq_zero_of_lt h, ite_eq_right (by omega)]
    simp

lemma poissonWeight_zero_rate (k : ℕ) : poissonWeight 0 k = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [poissonWeight]
  · rw [ite_eq_right hk.ne', poissonWeight, zero_pow hk.ne', mul_zero, zero_div]

lemma binomialPoissonWeight_one_zero (x y : ℕ) :
    binomialPoissonWeight 1 0 x y = if x = y then 1 else 0 := by
  simp only [binomialPoissonWeight, binomialWeight_one, poissonWeight_zero_rate]
  rcases le_or_gt x y with hxy | hxy
  · rw [Finset.sum_eq_single x (fun k _ hk ↦ by rw [ite_eq_right hk, zero_mul])
      (fun hx ↦ absurd (Finset.mem_range.2 (by omega)) hx), ite_eq_left rfl, one_mul]
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [ite_eq_right (by omega), zero_mul]

end Powers

/-! ## Georgii (11.29): the right vectors `r^v_i` -/

section RightVector

variable {p u v : ℝ}

/-- **Georgii (11.29).** `r^v_i(x) = 𝔭(1 + v p^{-i}, x) / α(x)` with `α = 𝔭(1, ·)`
(`rightReal_eq_poissonWeight_div`); dividing out the factorials this is
`r^v_i(x) = e^{-v p^{-i}} (1 + v p^{-i})^x`, which is the form used in the computations. -/
def rightReal (p v : ℝ) (i : ℤ) (x : ℕ) : ℝ :=
  Real.exp (-(v * p ^ (-i))) * (1 + v * p ^ (-i)) ^ x

lemma mul_zpow_neg_nonneg (hp0 : 0 < p) (hv : 0 ≤ v) (i : ℤ) : 0 ≤ v * p ^ (-i) :=
  mul_nonneg hv (zpow_pos hp0 _).le

lemma rightReal_pos (hp0 : 0 < p) (hv : 0 ≤ v) (i : ℤ) (x : ℕ) : 0 < rightReal p v i x :=
  mul_pos (Real.exp_pos _) (pow_pos (by linarith [mul_zpow_neg_nonneg hp0 hv i]) x)

/-- **Georgii (11.29), as stated.** `r^v_i = 𝔭(1 + v p^{-i}, ·) / α` with `α = 𝔭(1, ·)`. -/
lemma rightReal_eq_poissonWeight_div (i : ℤ) (x : ℕ) :
    rightReal p v i x = poissonWeight (1 + v * p ^ (-i)) x / poissonWeight 1 x := by
  have hx : ((x ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero x)
  have h1ne : poissonWeight (1 : ℝ) x ≠ 0 := (poissonWeight_pos one_pos x).ne'
  rw [eq_div_iff h1ne, rightReal, poissonWeight, poissonWeight,
    show -(1 + v * p ^ (-i)) = -1 + -(v * p ^ (-i)) by ring, Real.exp_add]
  field_simp
  ring

/-- `v p^{-(i-1)} = p (v p^{-i})`, the shift of the rate of `r^v` by one site. -/
lemma mul_zpow_neg_sub_one (hp0 : 0 < p) (i : ℤ) :
    v * p ^ (-(i - 1)) = p * (v * p ^ (-i)) := by
  rw [show -(i - 1) = 1 + -i by ring, zpow_add₀ hp0.ne', zpow_one]
  ring

/-- **Georgii (11.29).** `Q r^v_i = r^v_{i-1}`: apply the generating function of `Q(x, ·)` at
`z = 1 + v p^{-i}`, where it equals `(1 + p v p^{-i})^x e^{(1-p) v p^{-i}}`. -/
lemma tsum_matrixReal_mul_rightReal (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : 0 ≤ v) (i : ℤ) (x : ℕ) :
    ∑' y : ℕ, matrixReal p x y * rightReal p v i y = rightReal p v (i - 1) x := by
  set t : ℝ := v * p ^ (-i) with ht
  have ht0 : 0 ≤ t := mul_zpow_neg_nonneg hp0 hv i
  have hz : (0 : ℝ) ≤ 1 + t := by linarith
  have hcongr : ∀ y : ℕ, matrixReal p x y * rightReal p v i y
      = Real.exp (-t) * (matrixReal p x y * (1 + t) ^ y) := fun y ↦ by
    simp only [rightReal, ← ht]; ring
  have hr : rightReal p v (i - 1) x = Real.exp (-(p * t)) * (1 + p * t) ^ x := by
    simp only [rightReal, mul_zpow_neg_sub_one hp0, ← ht]
  rw [tsum_congr hcongr, tsum_mul_left, tsum_matrixReal_mul_pow hp0.le hp1 hz x, hr,
    show (1 : ℝ) - p + p * (1 + t) = 1 + p * t by ring,
    show ((1 : ℝ) - p) * (1 + t - 1) = (1 - p) * t by ring,
    show Real.exp (-t) * ((1 + p * t) ^ x * Real.exp ((1 - p) * t))
      = Real.exp (-t) * Real.exp ((1 - p) * t) * (1 + p * t) ^ x by ring,
    ← Real.exp_add, show -t + (1 - p) * t = -(p * t) by ring]

/-- **Georgii (11.29).** `ℓ^u_i r^v_i = e^{uv}` for every `i`: the generating function of
`𝔭(1 + u p^i, ·)` at `z = 1 + v p^{-i}`. -/
lemma tsum_poissonWeight_mul_rightReal (hp0 : 0 < p) (hu : 0 ≤ u) (hv : 0 ≤ v) (i : ℤ) :
    ∑' x : ℕ, poissonWeight (1 + u * p ^ i) x * rightReal p v i x = Real.exp (u * v) := by
  set t : ℝ := v * p ^ (-i) with ht
  have ht0 : 0 ≤ t := mul_zpow_neg_nonneg hp0 hv i
  have hz : (0 : ℝ) ≤ 1 + t := by linarith
  have ha : (0 : ℝ) ≤ 1 + u * p ^ i := by
    have := mul_nonneg hu (zpow_pos hp0 i).le; linarith
  have hpi : p ^ i * p ^ (-i) = 1 := by rw [← zpow_add₀ hp0.ne']; simp
  have hcongr : ∀ x : ℕ, poissonWeight (1 + u * p ^ i) x * rightReal p v i x
      = Real.exp (-t) * (poissonWeight (1 + u * p ^ i) x * (1 + t) ^ x) := fun x ↦ by
    simp only [rightReal, ← ht]; ring
  rw [tsum_congr hcongr, tsum_mul_left, (hasSum_poissonWeight_mul_pow ha hz).tsum_eq,
    ← Real.exp_add]
  congr 1
  rw [ht]
  linear_combination (u * v) * hpi

/-- **Georgii (11.30).** `ℓ^u_i(x) e^{-uv} r^v_i(x) = 𝔭((1 + u p^i)(1 + v p^{-i}), x)`. -/
lemma poissonWeight_mul_exp_mul_rightReal (hp0 : 0 < p) (i : ℤ) (x : ℕ) :
    poissonWeight (1 + u * p ^ i) x * (Real.exp (-(u * v)) * rightReal p v i x)
      = poissonWeight ((1 + u * p ^ i) * (1 + v * p ^ (-i))) x := by
  have hpi : p ^ i * p ^ (-i) = 1 := by rw [← zpow_add₀ hp0.ne']; simp
  have hexp : -(1 + u * p ^ i) + (-(u * v) + -(v * p ^ (-i)))
      = -((1 + u * p ^ i) * (1 + v * p ^ (-i))) := by linear_combination (u * v) * hpi
  simp only [poissonWeight, rightReal, mul_pow]
  rw [show Real.exp (-(1 + u * p ^ i)) * (1 + u * p ^ i) ^ x / (x ! : ℝ)
      * (Real.exp (-(u * v)) * (Real.exp (-(v * p ^ (-i))) * (1 + v * p ^ (-i)) ^ x))
      = Real.exp (-(1 + u * p ^ i)) * (Real.exp (-(u * v)) * Real.exp (-(v * p ^ (-i))))
        * ((1 + u * p ^ i) ^ x * (1 + v * p ^ (-i)) ^ x) / (x ! : ℝ) by ring,
    ← Real.exp_add, ← Real.exp_add, hexp]

lemma summable_matrixReal_mul_rightReal (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : 0 ≤ v) (i : ℤ)
    (x : ℕ) : Summable fun y : ℕ ↦ matrixReal p x y * rightReal p v i y := by
  have ht0 : 0 ≤ v * p ^ (-i) := mul_zpow_neg_nonneg hp0 hv i
  have h := (summable_matrixReal_mul_pow hp0.le hp1
    (show (0 : ℝ) ≤ 1 + v * p ^ (-i) by linarith) x).mul_left (Real.exp (-(v * p ^ (-i))))
  exact h.congr fun y ↦ by simp only [rightReal]; ring

lemma summable_poissonWeight_mul_rightReal (hp0 : 0 < p) (hu : 0 ≤ u) (hv : 0 ≤ v) (i : ℤ) :
    Summable fun x : ℕ ↦ poissonWeight (1 + u * p ^ i) x * rightReal p v i x := by
  have ht0 : 0 ≤ v * p ^ (-i) := mul_zpow_neg_nonneg hp0 hv i
  have ha : (0 : ℝ) ≤ 1 + u * p ^ i := by
    have := mul_nonneg hu (zpow_pos hp0 i).le; linarith
  have h := (summable_poissonWeight_mul_pow ha
    (show (0 : ℝ) ≤ 1 + v * p ^ (-i) by linarith)).mul_left (Real.exp (-(v * p ^ (-i))))
  exact h.congr fun x ↦ by simp only [rightReal]; ring

end RightVector

/-! ## The transfer matrix, Georgii's boundary laws (11.29), and the phase transition -/

section Transfer

/-- **Georgii (11.26)** as an `ℝ≥0∞`-valued matrix on the state space `E = ℤ₊ = ℕ`. -/
def matrix (p : ℝ) (x y : ℕ) : ℝ≥0∞ := ENNReal.ofReal (matrixReal p x y)

/-- **Georgii (11.29) at `v = 0`.** `ℓ^u_i(x) = 𝔭(1 + u p^i, x)`. -/
def entrance (p u : ℝ) (i : ℤ) (x : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (poissonWeight (1 + u * p ^ i) x)

variable {p u : ℝ}

lemma rate_pos (hp0 : 0 < p) (hu : 0 ≤ u) (i : ℤ) : 0 < 1 + u * p ^ i := by
  have : (0 : ℝ) ≤ u * p ^ i := mul_nonneg hu (zpow_pos hp0 i).le
  linarith

lemma matrix_pos (hp0 : 0 < p) (hp1 : p < 1) (x y : ℕ) : 0 < matrix p x y :=
  ENNReal.ofReal_pos.2 (matrixReal_pos hp0 hp1 x y)

lemma tsum_matrix (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℕ) : ∑' y : ℕ, matrix p x y = 1 := by
  simp only [matrix]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun y ↦ matrixReal_nonneg hp0 hp1 x y)
    (summable_matrixReal hp0 hp1 x), tsum_matrixReal hp0 hp1 x, ENNReal.ofReal_one]

/-- Georgii's `Q` is a transfer matrix in the sense of (11.1): positive, with finite powers
because it is stochastic. -/
lemma isTransferMatrix (hp0 : 0 < p) (hp1 : p < 1) : IsTransferMatrix (matrix p) :=
  isTransferMatrix_of_stochastic (matrix_pos hp0 hp1) (tsum_matrix hp0.le hp1.le)

/-- **Georgii (11.32).** `Q^n(x, ·) = ℓ(x, p^n, ·) ∗ 𝔭(1 - p^n, ·)`: after `n` time units each of
the `x` initial individuals is still alive with probability `p^n`, independently of the others,
and the immigrants that arrived in the meantime form an independent `Poisson(1 - p^n)`
population. This is Georgii's induction: (11.22) splits the thinning of the `k` survivors and the
`l` immigrants of the previous step, (11.25) thins the Poisson part, (11.23) composes the two
binomial thinnings, and (11.24) merges the two Poisson parts — all of it packaged in
`hasSum_binomialPoissonWeight_mul_binomialPoissonWeight`. The identity also holds for `n = 0`,
where `ℓ(x, 1, ·) ∗ 𝔭(0, ·) = δ_x`. -/
theorem matrix_pow_apply_singleton (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n x y : ℕ) :
    (Kernel.ofMatrix (matrix p) ^ n) x {y}
      = ENNReal.ofReal (binomialPoissonWeight (p ^ n) (1 - p ^ n) x y) := by
  induction n generalizing y with
  | zero =>
      rw [Kernel.pow_zero_apply_singleton, pow_zero, sub_self, binomialPoissonWeight_one_zero]
      rcases eq_or_ne x y with rfl | hxy
      · simp
      · rw [Set.indicator_of_notMem (by simpa using hxy), ite_eq_right hxy,
          ENNReal.ofReal_zero]
  | succ n ih =>
      have hpn0 : (0 : ℝ) ≤ p ^ n := pow_nonneg hp0 n
      have hpn1 : p ^ n ≤ 1 := pow_le_one₀ hp0 hp1
      have hb : (0 : ℝ) ≤ 1 - p ^ n := by linarith
      have hq : (0 : ℝ) ≤ 1 - p := by linarith
      have hmul : ∀ w : ℕ, (Kernel.ofMatrix (matrix p) ^ n) x {w} * matrix p w y
          = ENNReal.ofReal (binomialPoissonWeight (p ^ n) (1 - p ^ n) x w
              * binomialPoissonWeight p (1 - p) w y) := fun w ↦ by
        rw [ih w,
          show matrix p w y = ENNReal.ofReal (binomialPoissonWeight p (1 - p) w y) from rfl,
          ← ENNReal.ofReal_mul (binomialPoissonWeight_nonneg hpn0 hpn1 hb x w)]
      have hkey := hasSum_binomialPoissonWeight_mul_binomialPoissonWeight
        (a := p ^ n) (q := 1 - p) hb hp1 x y
      have hrate : (1 - p ^ n) * p + (1 - p) = 1 - p ^ (n + 1) := by rw [pow_succ]; ring
      rw [Kernel.ofMatrix_pow_succ'_apply_singleton]
      simp only [hmul]
      rw [← ENNReal.ofReal_tsum_of_nonneg
          (fun w ↦ mul_nonneg (binomialPoissonWeight_nonneg hpn0 hpn1 hb x w)
            (binomialPoissonWeight_nonneg hp0 hp1 hq w y)) hkey.summable,
        hkey.tsum_eq, ← pow_succ, hrate]

/-- **Georgii (11.29) at `v = 0`:** `ℓ^u_i Q = ℓ^u_{i+1}`, because
`(1 + u p^i) p + (1 - p) = 1 + u p^{i+1}`. -/
theorem isEntranceLaw (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) :
    IsEntranceLaw (matrix p) (entrance p u) where
  pos i x := ENNReal.ofReal_pos.2 (poissonWeight_pos (rate_pos hp0 hu i) x)
  tsum_eq_one i := by
    simp only [entrance]
    rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun x ↦ poissonWeight_nonneg (rate_pos hp0 hu i).le x)
        (summable_poissonWeight (rate_pos hp0 hu i).le),
      tsum_poissonWeight (rate_pos hp0 hu i).le, ENNReal.ofReal_one]
  step i y := by
    have hmul : ∀ x : ℕ, entrance p u i x * matrix p x y
        = ENNReal.ofReal (poissonWeight (1 + u * p ^ i) x * matrixReal p x y) := fun x ↦
      (ENNReal.ofReal_mul (poissonWeight_nonneg (rate_pos hp0 hu i).le x)).symm
    have hrate : (1 + u * p ^ i) * p + (1 - p) = 1 + u * p ^ (i + 1) := by
      rw [zpow_add_one₀ hp0.ne' i]; ring
    simp only [hmul]
    rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun x ↦ mul_nonneg (poissonWeight_nonneg (rate_pos hp0 hu i).le x)
          (matrixReal_nonneg hp0.le hp1.le x y))
        (summable_poissonWeight_mul_matrixReal (rate_pos hp0 hu i).le hp1.le y),
      tsum_poissonWeight_mul_matrixReal (rate_pos hp0 hu i).le hp1.le y, hrate]
    rfl

/-! ### Georgii Theorem (11.31), Step 1: the limits of the rows `Q^n(x_n, ·)` -/

section RowLimits

open Filter
open scoped Topology

/-- `Q^n(x, 0) = (1 - p^n)^x e^{-(1 - p^n)}`: after `n` steps the whole initial population is
extinct and no immigrant is alive. This is the quantity whose ratios Georgii uses in Step 1 of
the proof of Theorem (11.31). -/
theorem matrix_pow_apply_zero (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n x : ℕ) :
    (Kernel.ofMatrix (matrix p) ^ n) x {0}
      = ENNReal.ofReal ((1 - p ^ n) ^ x * Real.exp (-(1 - p ^ n))) := by
  rw [matrix_pow_apply_singleton hp0 hp1 n x 0]
  congr 1
  simp [binomialPoissonWeight, binomialWeight, poissonWeight_zero]

lemma continuous_poissonWeight (k : ℕ) : Continuous fun a : ℝ ↦ poissonWeight a k := by
  unfold poissonWeight
  fun_prop

/-- **Georgii Theorem (11.31), Step 1 (the limit).** If `m_n → ∞` and `x_n p^{m_n} → a`, then
`Q^{m_n}(x_n, ·) → 𝔭(1 + a, ·)`.

By (11.32) the row `Q^m(x, ·)` is the convolution `ℓ(x, p^m, ·) ∗ 𝔭(1 - p^m, ·)`, a *finite* sum
at each `y`; the binomial factor converges to `𝔭(a, ·)` by the Poisson limit theorem
(`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul`) and the Poisson factor to `𝔭(1, ·)`,
and `𝔭(a, ·) ∗ 𝔭(1, ·) = 𝔭(1 + a, ·)` by (11.24). -/
theorem tendsto_matrix_pow_apply_singleton (hp0 : 0 < p) (hp1 : p < 1)
    {x m : ℕ → ℕ} {a : ℝ} (hm : Tendsto m atTop atTop)
    (hlim : Tendsto (fun n ↦ (x n : ℝ) * p ^ m n) atTop (𝓝 a)) (y : ℕ) :
    Tendsto (fun n ↦ (Kernel.ofMatrix (matrix p) ^ m n) (x n) {y}) atTop
      (𝓝 (ENNReal.ofReal (poissonWeight (1 + a) y))) := by
  have hpm : Tendsto (fun n ↦ p ^ m n) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hp0.le hp1).comp hm
  have hbin : ∀ k : ℕ, Tendsto (fun n ↦ binomialWeight (x n) (p ^ m n) k) atTop
      (𝓝 (poissonWeight a k)) := fun k ↦
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul hlim hpm k
  have hpois : ∀ k : ℕ, Tendsto (fun n ↦ poissonWeight (1 - p ^ m n) k) atTop
      (𝓝 (poissonWeight 1 k)) := fun k ↦ by
    refine ((continuous_poissonWeight k).tendsto 1).comp ?_
    simpa using tendsto_const_nhds.sub hpm
  have hconv : Tendsto (fun n ↦ binomialPoissonWeight (p ^ m n) (1 - p ^ m n) (x n) y) atTop
      (𝓝 (∑ k ∈ Finset.range (y + 1), poissonWeight a k * poissonWeight 1 (y - k))) :=
    tendsto_finsetSum _ fun k _ ↦ (hbin k).mul (hpois (y - k))
  have hval : (∑ k ∈ Finset.range (y + 1), poissonWeight a k * poissonWeight 1 (y - k))
      = poissonWeight (1 + a) y := by
    rw [sum_poissonWeight_mul_poissonWeight a 1 y, add_comm]
  rw [← hval]
  exact (ENNReal.tendsto_ofReal hconv).congr fun n ↦
    (matrix_pow_apply_singleton hp0.le hp1.le (m n) (x n) y).symm

/-- **Georgii Theorem (11.31), Step 1.** If `x_n p^n → u` then `Q^{n+i}(x_n, ·) → ℓ^u_i` for
every `i ∈ ℤ`, where `ℓ^u_i = 𝔭(1 + u p^i, ·)` is Georgii's left boundary vector (11.29). -/
theorem tendsto_matrix_pow_apply_singleton_entrance (hp0 : 0 < p) (hp1 : p < 1) {u : ℝ}
    {x : ℕ → ℕ} (hlim : Tendsto (fun n ↦ (x n : ℝ) * p ^ n) atTop (𝓝 u)) (i : ℤ) (y : ℕ) :
    Tendsto (fun n : ℕ ↦ (Kernel.ofMatrix (matrix p) ^ ((n : ℤ) + i).toNat) (x n) {y}) atTop
      (𝓝 (entrance p u i y)) := by
  have hm : Tendsto (fun n : ℕ ↦ ((n : ℤ) + i).toNat) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b ↦ ⟨b + i.natAbs, fun n hn ↦ ?_⟩
    have hn' : (b : ℤ) + (i.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have heq : ∀ᶠ n : ℕ in atTop,
      ((x n : ℝ) * p ^ n) * p ^ i = (x n : ℝ) * p ^ (((n : ℤ) + i).toNat) := by
    filter_upwards [eventually_ge_atTop i.natAbs] with n hn
    have hn' : (i.natAbs : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have hz : ((((n : ℤ) + i).toNat : ℕ) : ℤ) = (n : ℤ) + i := by omega
    rw [← zpow_natCast p (((n : ℤ) + i).toNat), hz, zpow_add₀ hp0.ne', zpow_natCast]
    ring
  exact tendsto_matrix_pow_apply_singleton hp0 hp1 hm
    (Tendsto.congr' heq (hlim.mul_const (p ^ i))) y

/-- **Georgii's Step-1 estimate** for Theorem (11.31): the ratio of two consecutive extinction
probabilities is at most `e · exp[-x p^m (1 - p)]`, because
`(1 - p^m)/(1 - p^{m+1}) ≤ 1 - p^m(1 - p)`. It is what forces the sequence `(x_n p^n)` to be
bounded when the ratio has a positive limit. -/
private lemma toReal_matrix_pow_apply_zero_div_le (hp0 : 0 < p) (hp1 : p < 1) (m x : ℕ) :
    ((Kernel.ofMatrix (matrix p) ^ m) x {0}).toReal
      / ((Kernel.ofMatrix (matrix p) ^ (m + 1)) x {0}).toReal
      ≤ Real.exp 1 * Real.exp (-((x : ℝ) * (p ^ m * (1 - p)))) := by
  set q : ℝ := p ^ m with hq
  have hq0 : 0 < q := pow_pos hp0 m
  have hq1 : q ≤ 1 := pow_le_one₀ hp0.le hp1.le
  have hqp : p ^ (m + 1) = q * p := by rw [hq, pow_succ]
  have hB1 : (0 : ℝ) < 1 - q * p := by nlinarith
  have hA0 : (0 : ℝ) ≤ 1 - q := by linarith
  have hAnn : (0 : ℝ) ≤ (1 - q) ^ x * Real.exp (-(1 - q)) :=
    mul_nonneg (pow_nonneg hA0 x) (Real.exp_pos _).le
  have hBpos : (0 : ℝ) < (1 - q * p) ^ x * Real.exp (-(1 - q * p)) :=
    mul_pos (pow_pos hB1 x) (Real.exp_pos _)
  rw [matrix_pow_apply_zero hp0.le hp1.le m x, matrix_pow_apply_zero hp0.le hp1.le (m + 1) x,
    ENNReal.toReal_ofReal hAnn, hqp, ENNReal.toReal_ofReal hBpos.le]
  have hsplit : ((1 - q) ^ x * Real.exp (-(1 - q))) / ((1 - q * p) ^ x * Real.exp (-(1 - q * p)))
      = ((1 - q) / (1 - q * p)) ^ x * Real.exp (q - q * p) := by
    rw [← div_mul_div_comm, ← Real.exp_sub, ← div_pow]
    congr 2
    ring
  rw [hsplit]
  have hbase : (1 - q) / (1 - q * p) ≤ 1 - q * (1 - p) := by
    rw [div_le_iff₀ hB1]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hq0.le hq0.le) hp0.le)
      (sub_nonneg.2 hp1.le)]
  have hpow : ((1 - q) / (1 - q * p)) ^ x ≤ Real.exp (-(q * (1 - p) * x)) :=
    (pow_le_pow_left₀ (by positivity) hbase x).trans
      (Real.one_sub_pow_le_exp_neg_mul (by nlinarith) x)
  have hexp : Real.exp (q - q * p) ≤ Real.exp 1 := Real.exp_le_exp.2 (by nlinarith)
  calc ((1 - q) / (1 - q * p)) ^ x * Real.exp (q - q * p)
      ≤ Real.exp (-(q * (1 - p) * x)) * Real.exp 1 :=
        mul_le_mul hpow hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp 1 * Real.exp (-((x : ℝ) * (p ^ m * (1 - p)))) := by
        rw [mul_comm]
        congr 2
        rw [hq]
        ring

/-- **Georgii Theorem (11.31), Step 1 (the existence of `u`).** If the ratios
`Q^{n-1}(x_n, 0)/Q^n(x_n, 0)` converge to a positive limit `c`, then `u = lim_n x_n p^n` exists
and is nonnegative.

Georgii's estimate `toReal_matrix_pow_apply_zero_div_le` bounds the ratio by
`e · exp[-x_n p^{n-1}(1 - p)]`, so a positive limit forces `(x_n p^n)` to be bounded; every
cluster point `u` of the bounded sequence satisfies `c = ℓ^u_{-1}(0)/ℓ^u_0(0) = exp(-u(1-p)/p)`
by `tendsto_matrix_pow_apply_singleton`, so the cluster point is unique and the sequence
converges. -/
theorem exists_tendsto_mul_pow_of_tendsto_ratio (hp0 : 0 < p) (hp1 : p < 1) {x : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c)
    (hratio : Tendsto (fun n : ℕ ↦
        ((Kernel.ofMatrix (matrix p) ^ (n - 1)) (x n) {0}).toReal
          / ((Kernel.ofMatrix (matrix p) ^ n) (x n) {0}).toReal) atTop (𝓝 c)) :
    ∃ u : ℝ, 0 ≤ u ∧ Tendsto (fun n : ℕ ↦ (x n : ℝ) * p ^ n) atTop (𝓝 u) := by
  have hq1 : (0 : ℝ) < 1 - p := by linarith
  set t : ℕ → ℝ := fun n ↦ (x n : ℝ) * p ^ n with hty
  have ht0 : ∀ n, 0 ≤ t n := fun n ↦ by positivity
  set R : ℕ → ℝ := fun n ↦ ((Kernel.ofMatrix (matrix p) ^ (n - 1)) (x n) {0}).toReal
      / ((Kernel.ofMatrix (matrix p) ^ n) (x n) {0}).toReal with hRy
  -- Step 1a: the sequence `(t n)` is bounded.
  set M : ℝ := -(p * Real.log (c / (2 * Real.exp 1))) / (1 - p) with hMy
  have hbdd : ∀ᶠ n in atTop, t n ≤ M := by
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_order.1 hratio).1 (c / 2) (by linarith)] with n hn hgt
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hle : R (m + 1) ≤ Real.exp 1 * Real.exp (-((x (m + 1) : ℝ) * (p ^ m * (1 - p)))) := by
      simpa only [hRy, Nat.add_sub_cancel] using
        toReal_matrix_pow_apply_zero_div_le hp0 hp1 m (x (m + 1))
    have hpm : (0 : ℝ) < p ^ m := pow_pos hp0 m
    have hrewrite : (x (m + 1) : ℝ) * (p ^ m * (1 - p)) = t (m + 1) * (1 - p) / p := by
      rw [hty]
      field_simp [pow_succ]
      ring
    rw [hrewrite] at hle
    have hexp : c / (2 * Real.exp 1) < Real.exp (-(t (m + 1) * (1 - p) / p)) := by
      have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [Real.exp_pos (-(t (m + 1) * (1 - p) / p))]
    have hlog := Real.log_lt_log (by positivity) hexp
    rw [Real.log_exp] at hlog
    have hkey : t (m + 1) * (1 - p) / p < -Real.log (c / (2 * Real.exp 1)) := by linarith
    rw [div_lt_iff₀ hp0] at hkey
    rw [hMy, le_div_iff₀ hq1]
    linarith
  -- Step 1b: every cluster point of `(t n)` equals `u₀`.
  set u₀ : ℝ := -(p * Real.log c) / (1 - p) with hu₀y
  have hcluster : ∀ θ : ℕ → ℕ, Tendsto θ atTop atTop → ∀ a : ℝ,
      Tendsto (fun j ↦ t (θ j)) atTop (𝓝 a) → a = u₀ := by
    intro θ hθ a ha
    have hden : Tendsto (fun j ↦ (Kernel.ofMatrix (matrix p) ^ θ j) (x (θ j)) {0}) atTop
        (𝓝 (ENNReal.ofReal (poissonWeight (1 + a) 0))) :=
      tendsto_matrix_pow_apply_singleton hp0 hp1 hθ ha 0
    have hθ1 : Tendsto (fun j ↦ θ j - 1) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b ↦ ?_
      obtain ⟨j₀, hj₀⟩ := tendsto_atTop_atTop.1 hθ (b + 1)
      exact ⟨j₀, fun j hj ↦ by have := hj₀ j hj; omega⟩
    have hnumlim : Tendsto (fun j ↦ (x (θ j) : ℝ) * p ^ (θ j - 1)) atTop (𝓝 (a / p)) := by
      refine Tendsto.congr' ?_ (ha.div_const p)
      filter_upwards [hθ.eventually_ge_atTop 1] with j hj
      simp only [hty]
      have hpj : p ^ (θ j) = p ^ (θ j - 1) * p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpj]
      field_simp
    have hnum : Tendsto (fun j ↦ (Kernel.ofMatrix (matrix p) ^ (θ j - 1)) (x (θ j)) {0}) atTop
        (𝓝 (ENNReal.ofReal (poissonWeight (1 + a / p) 0))) :=
      tendsto_matrix_pow_apply_singleton hp0 hp1 hθ1 hnumlim 0
    have hnumR : Tendsto (fun j ↦ ((Kernel.ofMatrix (matrix p) ^ (θ j - 1)) (x (θ j)) {0}).toReal)
        atTop (𝓝 (Real.exp (-(1 + a / p)))) := by
      have hval : (ENNReal.ofReal (poissonWeight (1 + a / p) 0)).toReal
          = Real.exp (-(1 + a / p)) := by
        rw [poissonWeight_zero, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      have h1 : Tendsto (fun j ↦ ((Kernel.ofMatrix (matrix p) ^ (θ j - 1)) (x (θ j)) {0}).toReal)
          atTop (𝓝 (ENNReal.ofReal (poissonWeight (1 + a / p) 0)).toReal) :=
        (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hnum
      rwa [hval] at h1
    have hdenR : Tendsto (fun j ↦ ((Kernel.ofMatrix (matrix p) ^ θ j) (x (θ j)) {0}).toReal)
        atTop (𝓝 (Real.exp (-(1 + a)))) := by
      have hval : (ENNReal.ofReal (poissonWeight (1 + a) 0)).toReal = Real.exp (-(1 + a)) := by
        rw [poissonWeight_zero, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      have h1 : Tendsto (fun j ↦ ((Kernel.ofMatrix (matrix p) ^ θ j) (x (θ j)) {0}).toReal)
          atTop (𝓝 (ENNReal.ofReal (poissonWeight (1 + a) 0)).toReal) :=
        (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp hden
      rwa [hval] at h1
    have hRlim : Tendsto (fun j ↦ R (θ j)) atTop
        (𝓝 (Real.exp (-(1 + a / p)) / Real.exp (-(1 + a)))) :=
      hnumR.div hdenR (Real.exp_pos _).ne'
    have hRc : Tendsto (fun j ↦ R (θ j)) atTop (𝓝 c) := hratio.comp hθ
    have heq : Real.exp (-(1 + a / p)) / Real.exp (-(1 + a)) = c :=
      tendsto_nhds_unique hRlim hRc
    rw [← Real.exp_sub] at heq
    have hlog : -(1 + a / p) - -(1 + a) = Real.log c := by
      rw [← heq, Real.log_exp]
    have hpa : a - a / p = Real.log c := by linarith
    have hpne : p ≠ 0 := hp0.ne'
    have hmul : a * p - a = p * Real.log c := by
      field_simp at hpa
      linarith
    rw [hu₀y, eq_div_iff (by linarith : (1 : ℝ) - p ≠ 0)]
    linarith
  -- Step 1c: a bounded sequence with a unique cluster point converges.
  have hconv : Tendsto t atTop (𝓝 u₀) := by
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    have hfreq : ∃ᶠ j in atTop, t (ns j) ∈ Set.Icc 0 M := by
      refine ((hns.eventually hbdd).mono fun j hj ↦ ?_).frequently
      exact ⟨ht0 _, hj⟩
    obtain ⟨b, _, ms, hms, hmslim⟩ :=
      tendsto_subseq_of_frequently_bounded (Metric.isBounded_Icc 0 M) hfreq
    refine ⟨ms, ?_⟩
    have hθ : Tendsto (fun j ↦ ns (ms j)) atTop atTop := hns.comp hms.tendsto_atTop
    have hb : b = u₀ := hcluster _ hθ b hmslim
    rw [← hb]
    exact hmslim
  exact ⟨u₀, ge_of_tendsto' hconv ht0, hconv⟩

/-- **Georgii Theorem (11.31), Step 1**, in full: let `(x_n)` be a sequence in `E` for which
`c = lim_n Q^{n-1}(x_n, 0)/Q^n(x_n, 0)` exists and is positive. Then `u = lim_n x_n p^n` exists
and `lim_n Q^{n+i}(x_n, ·) = ℓ^u_i` for every `i ∈ ℤ`.

This is the point at which Steps 2 and 4 of Georgii's proof read off the parameter `u` of an
extreme Gibbs measure from the limit formulas of Theorem (11.9)(c). -/
theorem exists_tendsto_matrix_pow_apply_singleton_of_tendsto_ratio (hp0 : 0 < p) (hp1 : p < 1)
    {x : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hratio : Tendsto (fun n : ℕ ↦
        ((Kernel.ofMatrix (matrix p) ^ (n - 1)) (x n) {0}).toReal
          / ((Kernel.ofMatrix (matrix p) ^ n) (x n) {0}).toReal) atTop (𝓝 c)) :
    ∃ u : ℝ, 0 ≤ u ∧ Tendsto (fun n : ℕ ↦ (x n : ℝ) * p ^ n) atTop (𝓝 u) ∧
      ∀ (i : ℤ) (y : ℕ), Tendsto
        (fun n : ℕ ↦ (Kernel.ofMatrix (matrix p) ^ ((n : ℤ) + i).toNat) (x n) {y}) atTop
        (𝓝 (entrance p u i y)) := by
  obtain ⟨u, hu0, hu⟩ := exists_tendsto_mul_pow_of_tendsto_ratio hp0 hp1 hc hratio
  exact ⟨u, hu0, hu, fun i y ↦ tendsto_matrix_pow_apply_singleton_entrance hp0 hp1 hu i y⟩

end RowLimits

/-- **Georgii (11.29).** The right vector `e^{-uv} r^v_i` of Georgii's boundary law, as an
`ℝ≥0∞`-valued function. -/
def right (p u v : ℝ) (i : ℤ) (x : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(u * v)) * rightReal p v i x)

variable {v : ℝ}

lemma right_pos (hp0 : 0 < p) (hv : 0 ≤ v) (i : ℤ) (x : ℕ) : 0 < right p u v i x :=
  ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) (rightReal_pos hp0 hv i x))

/-- At `v = 0` the right vectors are identically `1`, because `α = 𝔭(1, ·)`; Georgii's boundary
law then degenerates to the entrance law `{ℓ^u_i}`. -/
@[simp] lemma right_zero (i : ℤ) (x : ℕ) : right p u 0 i x = 1 := by
  simp [right, rightReal]

/-- **Georgii (11.29).** `{ℓ^u_i, e^{-uv} r^v_i : i ∈ ℤ}` is a boundary law for `Q`: the three
conditions are `ℓ^u_i Q = ℓ^u_{i+1}` (the entrance law `isEntranceLaw`), `Q r^v_i = r^v_{i-1}`
(`tsum_matrixReal_mul_rightReal`), and the normalisation `ℓ^u_i r^v_i = e^{uv}`
(`tsum_poissonWeight_mul_rightReal`). -/
theorem isBoundaryLaw (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    IsBoundaryLaw (matrix p) (entrance p u) (right p u v) := by
  have hC : (0 : ℝ) ≤ Real.exp (-(u * v)) := (Real.exp_pos _).le
  refine IsBoundaryLaw.of_tsum
    (fun i x ↦ ENNReal.ofReal_pos.2 (poissonWeight_pos (rate_pos hp0 hu i) x))
    (fun _ _ ↦ ENNReal.ofReal_ne_top) (fun i x ↦ right_pos hp0 hv i x)
    (fun _ _ ↦ ENNReal.ofReal_ne_top) (fun i y ↦ (isEntranceLaw hp0 hp1 hu).step i y)
    (fun i x ↦ ?_) (fun i ↦ ?_)
  · have hmul : ∀ y : ℕ, matrix p x y * right p u v i y
        = ENNReal.ofReal (matrixReal p x y * (Real.exp (-(u * v)) * rightReal p v i y)) :=
      fun y ↦ (ENNReal.ofReal_mul (matrixReal_nonneg hp0.le hp1.le x y)).symm
    have hnn : ∀ y : ℕ, 0 ≤ matrixReal p x y * (Real.exp (-(u * v)) * rightReal p v i y) :=
      fun y ↦ mul_nonneg (matrixReal_nonneg hp0.le hp1.le x y)
        (mul_nonneg hC (rightReal_pos hp0 hv i y).le)
    have hcongr : (fun y : ℕ ↦ matrixReal p x y * (Real.exp (-(u * v)) * rightReal p v i y))
        = fun y : ℕ ↦ Real.exp (-(u * v)) * (matrixReal p x y * rightReal p v i y) :=
      funext fun y ↦ by ring
    have hsum : Summable
        fun y : ℕ ↦ matrixReal p x y * (Real.exp (-(u * v)) * rightReal p v i y) := by
      rw [hcongr]
      exact (summable_matrixReal_mul_rightReal hp0 hp1.le hv i x).mul_left _
    have htsum : (∑' y : ℕ, matrixReal p x y * (Real.exp (-(u * v)) * rightReal p v i y))
        = Real.exp (-(u * v)) * rightReal p v (i - 1) x := by
      rw [hcongr, tsum_mul_left, tsum_matrixReal_mul_rightReal hp0 hp1.le hv i x]
    simp only [hmul]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, htsum]
    rfl
  · have hmul : ∀ x : ℕ, entrance p u i x * right p u v i x
        = ENNReal.ofReal (poissonWeight (1 + u * p ^ i) x
            * (Real.exp (-(u * v)) * rightReal p v i x)) :=
      fun x ↦ (ENNReal.ofReal_mul (poissonWeight_nonneg (rate_pos hp0 hu i).le x)).symm
    have hnn : ∀ x : ℕ, 0 ≤ poissonWeight (1 + u * p ^ i) x
        * (Real.exp (-(u * v)) * rightReal p v i x) :=
      fun x ↦ mul_nonneg (poissonWeight_nonneg (rate_pos hp0 hu i).le x)
        (mul_nonneg hC (rightReal_pos hp0 hv i x).le)
    have hcongr : (fun x : ℕ ↦ poissonWeight (1 + u * p ^ i) x
          * (Real.exp (-(u * v)) * rightReal p v i x))
        = fun x : ℕ ↦ Real.exp (-(u * v))
            * (poissonWeight (1 + u * p ^ i) x * rightReal p v i x) := funext fun x ↦ by ring
    have hsum : Summable fun x : ℕ ↦ poissonWeight (1 + u * p ^ i) x
        * (Real.exp (-(u * v)) * rightReal p v i x) := by
      rw [hcongr]
      exact (summable_poissonWeight_mul_rightReal hp0 hu hv i).mul_left _
    have htsum : (∑' x : ℕ, poissonWeight (1 + u * p ^ i) x
        * (Real.exp (-(u * v)) * rightReal p v i x)) = 1 := by
      rw [hcongr, tsum_mul_left, tsum_poissonWeight_mul_rightReal hp0 hu hv i,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [hmul]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, htsum, ENNReal.ofReal_one]

/-- Georgii's `μ^{u,v}`, the Markov chain (11.10) of the boundary law `{ℓ^u_i, e^{-uv} r^v_i}`. -/
abbrev chain (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) : Measure (ℤ → ℕ) :=
  boundaryLawMeasure (isBoundaryLaw hp0 hp1 hu hv)

/-- `μ^{u,v} ∈ 𝒢(Q)`: Theorem (11.9)(a). -/
theorem isGibbsMeasure_chain (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)).IsGibbsMeasure
      (chain hp0 hp1 hu hv) :=
  isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _

/-- **Georgii (11.30).** `μ^{u,v}(σ_i = x) = 𝔭((1 + u p^i)(1 + v p^{-i}), x)`. -/
theorem chain_intervalCylinder_self (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (i : ℤ) (ω : ℤ → ℕ) :
    chain hp0 hp1 hu hv (intervalCylinder i i ω)
      = ENNReal.ofReal (poissonWeight ((1 + u * p ^ i) * (1 + v * p ^ (-i))) (ω i)) := by
  rw [chain, IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_self _ i ω, entrance, right,
    ← ENNReal.ofReal_mul (poissonWeight_nonneg (rate_pos hp0 hu i).le (ω i)),
    poissonWeight_mul_exp_mul_rightReal hp0]

/-- For `u > 0` the one-site marginals of `μ^{u,0}` at the sites `0` and `1` differ: the rates
`1 + u` and `1 + u p` are different because `p < 1`. -/
theorem entrance_mul_right_zero_ne_one (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 < u) :
    entrance p u 0 0 * right p u 0 0 0 ≠ entrance p u 1 0 * right p u 0 1 0 := by
  have hlt : 1 + u * p ^ (1 : ℤ) < 1 + u * p ^ (0 : ℤ) := by
    simp only [zpow_one, zpow_zero, mul_one]
    nlinarith
  have h : poissonWeight (1 + u * p ^ (0 : ℤ)) 0 < poissonWeight (1 + u * p ^ (1 : ℤ)) 0 := by
    simp only [poissonWeight_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (poissonWeight_nonneg (rate_pos hp0 hu.le 0).le 0)).2 h
  simpa only [right_zero, mul_one, entrance] using this.ne

/-- **The Spitzer–Cox phase transition (Georgii §11.2).** For `0 < p < 1` and `u > 0` the Gibbs
measure `μ^{u,0}` of `γ^Q` is not shift invariant. -/
theorem not_mem_invariantG_chain (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 < u) :
    chain (v := 0) hp0 hp1 hu.le le_rfl ∉ invariantG
      (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)) (shiftGroup ℤ ℕ) :=
  not_mem_invariantG_boundaryLawMeasure_of_marginal_ne (i := 0) (j := 1) (x := 0)
    (isBoundaryLaw hp0 hp1 hu.le le_rfl) (isTransferMatrix hp0 hp1)
    (entrance_mul_right_zero_ne_one hp0 hp1 hu)

/-- **The Spitzer–Cox phase transition (Georgii §11.2), the conclusion `|ex 𝒢(Q)| = ∞` of
Theorem (11.31).** -/
theorem infinite_extremePoints_G (hp0 : 0 < p) (hp1 : p < 1) :
    ((G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1))).extremePoints
      ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_of_exists_not_mem_invariantG _ _
    ⟨inferInstance, isGibbsMeasure_chain hp0 hp1 (zero_le_one' ℝ) (v := 0) le_rfl⟩
    (not_mem_invariantG_chain hp0 hp1 one_pos)

/-- **Georgii, before (11.31): the translates of `μ^{u,0}` are pairwise distinct** for `u > 0`. -/
theorem injective_map_shift_chain (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 < u) :
    Function.Injective
      fun j : ℤ ↦ (chain (v := 0) hp0 hp1 hu.le le_rfl).map (shift ℕ j).toFun :=
  injective_map_shift_of_not_mem_invariantG _ (isTransferMatrix hp0 hp1)
    ⟨inferInstance, isGibbsMeasure_chain hp0 hp1 hu.le le_rfl⟩ (not_mem_invariantG_chain hp0 hp1 hu)

/-- **Georgii, before (11.31): the measures `μ^{u,v}` are pairwise distinct.** The one-site
marginals (11.30) give `(1 + u p^i)(1 + v p^{-i}) = (1 + u' p^i)(1 + v' p^{-i})` for every `i`,
and the three indices `i = -1, 0, 1` already force `u = u'` and `v = v'`. -/
theorem eq_of_chain_eq (hp0 : 0 < p) (hp1 : p < 1) {u' v' : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu' : 0 ≤ u') (hv' : 0 ≤ v') (h : chain hp0 hp1 hu hv = chain hp0 hp1 hu' hv') :
    u = u' ∧ v = v' := by
  have hrate : ∀ i : ℤ, (1 + u * p ^ i) * (1 + v * p ^ (-i))
      = (1 + u' * p ^ i) * (1 + v' * p ^ (-i)) := by
    intro i
    have hc := congrArg (fun μ : Measure (ℤ → ℕ) ↦ μ (intervalCylinder i i fun _ ↦ 0)) h
    simp only [chain_intervalCylinder_self hp0 hp1 hu hv i fun _ ↦ 0,
      chain_intervalCylinder_self hp0 hp1 hu' hv' i fun _ ↦ 0, poissonWeight_zero] at hc
    have hexp := (ENNReal.ofReal_eq_ofReal_iff (Real.exp_nonneg _) (Real.exp_nonneg _)).1 hc
    have := Real.exp_eq_exp.1 hexp
    linarith
  have hw : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hpinv : 0 < p⁻¹ := inv_pos.2 hp0
  have h0 := hrate 0
  have h1 := hrate 1
  have hm := hrate (-1)
  simp only [zpow_zero, neg_zero, mul_one, zpow_one, zpow_neg_one, neg_neg] at h0 h1 hm
  have hlt : p < p⁻¹ := by
    have hkey : (p⁻¹ - p) * p = 1 - p ^ 2 := by field_simp
    nlinarith
  have hgt : 2 < p + p⁻¹ := by
    have hkey : p + p⁻¹ - 2 = (1 - p) ^ 2 * p⁻¹ := by field_simp; ring
    nlinarith [pow_pos (show (0 : ℝ) < 1 - p by linarith) 2]
  have hdiff : (p - p⁻¹) * (u - u' - (v - v')) = 0 := by linear_combination h1 - hm
  have hsum : (u - u') * (1 - p) + (v - v') * (1 - p⁻¹) = 0 := by
    linear_combination h0 - h1 + (u * v - u' * v') * hw
  have he : u - u' = v - v' := by
    rcases mul_eq_zero.1 hdiff with hz | hz
    · exact absurd hz (by linarith)
    · linarith
  have h2 : (u - u') * (2 - p - p⁻¹) = 0 := by linear_combination hsum + (1 - p⁻¹) * he
  have hdu : u - u' = 0 := by
    rcases mul_eq_zero.1 h2 with hz | hz
    · exact hz
    · exact absurd hz (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- **The Spitzer–Cox example has uncountably many phases (Georgii §11.2).** Already the
one-parameter subfamily `{μ^{u,0} : u ≥ 0}` of Gibbs measures for `γ^Q` is uncountable, so
`𝒢(γ^Q)` is not countable. (Georgii's Theorem (11.31) says more: these measures, together with
the `μ^{u,v}`, are exactly the *extreme* points of `𝒢(Q)`.) -/
theorem not_countable_G (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ (G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1))).Countable := by
  intro hc
  set f : ℝ → Measure (ℤ → ℕ) := fun t ↦
    chain (u := Real.exp t) (v := 0) hp0 hp1 (Real.exp_pos t).le le_rfl with hf
  have hinj : Function.Injective f := fun s t hst ↦
    Real.exp_eq_exp.1 (eq_of_chain_eq hp0 hp1 (Real.exp_pos s).le le_rfl
      (Real.exp_pos t).le le_rfl hst).1
  have hpre : f ⁻¹' (G (transferSpecification (matrix p) (isTransferMatrix hp0 hp1)))
      = Set.univ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_univ, iff_true, hf]
    exact ⟨inferInstance, isGibbsMeasure_chain hp0 hp1 (Real.exp_pos t).le le_rfl⟩
  have hcount := hc.preimage hinj
  rw [hpre] at hcount
  exact Cardinal.not_countable_real hcount

end Transfer

end MeasureTheory.GibbsMeasure.Markov.SpitzerCox



/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.ProductMeasure
public import GibbsMeasure.Specification.HewittSavage

/-!
# Georgii (7.17) and (7.31): de Finetti's theorem in the version of Dynkin

The extreme exchangeable probability measures on `(E, ℰ)^ℕ` are exactly the i.i.d. product
measures (Georgii, Example (7.17)), and — over a standard Borel state space — every exchangeable
probability measure is the barycentre of a unique mixing measure on `𝒫(E, ℰ)`
(Georgii, Example (7.31): de Finetti's theorem in the version of Dynkin).

## Main results

* `MeasureTheory.GibbsMeasure.symmAvg_le_prod_add` /
  `MeasureTheory.GibbsMeasure.prod_le_symmAvg_add`: for `a i j ≤ 1` and `k ≤ n`, the symmetrised
  product and the product of the empirical averages differ by at most `∑_{j<k} j/(n−j)` — Georgii's
  `|M₁(k,n)|/|M(k,n)| → 1`, in a subtraction-free form obtained by group translations alone.
* `MeasureTheory.GibbsMeasure.eq_infinitePi_of_mem_extremePoints`: **Georgii (7.17)**, the
  substantial half — an extreme exchangeable probability measure is the i.i.d. product of its
  one-dimensional marginal. No hypothesis on the state space.
* `MeasureTheory.GibbsMeasure.mem_extremePoints_exchangeable_iff`: `ex 𝒫_I` is exactly the set of
  i.i.d. product measures.
* `MeasureTheory.GibbsMeasure.existsUnique_mixing_of_isExchangeable`: **Georgii (7.31)** — over a
  standard Borel state space, every exchangeable probability measure `μ` is `∫ λ^ℕ m(dλ)` for a
  unique probability measure `m` on `𝒫(E, ℰ)`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E]

/-! ### The symmetrisation estimate

For `a : ℕ → ℕ → ℝ≥0∞` with values `≤ 1`, the symmetrised product
`|Iₙ|⁻¹ ∑_{σ ∈ Iₙ} ∏_{i<k} a i (σ i)` differs from the product of the empirical averages
`∏_{i<k} (n⁻¹ ∑_{j<n} a i j)` by at most `∑_{j<k} j/(n−j)`. The proof needs no counting of
injections: only translation of the sum over the subgroup `Iₙ` by transpositions, and the fact
that elements of `Iₙ` permute `{0, …, n−1}`. -/

section Estimate

variable {n k : ℕ} {a : ℕ → ℕ → ℝ≥0∞}

variable (n a) in
/-- The symmetrised product `|Iₙ|⁻¹ ∑_{σ ∈ Iₙ} ∏_{i<k} a i (σ i)`. -/
def symmAvg (k : ℕ) : ℝ≥0∞ :=
  (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ *
    ∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)

variable (n a) in
/-- The empirical average `n⁻¹ ∑_{j<n} a i j` of the `i`-th row. -/
def empAvg (i : ℕ) : ℝ≥0∞ := (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range n, a i j

@[simp] lemma symmAvg_zero : symmAvg n a 0 = 1 := by
  simp [symmAvg, ENNReal.inv_mul_cancel (card_finPerm_ne_zero n) (card_finPerm_ne_top n)]

lemma symmAvg_le_one (ha : ∀ i j, a i j ≤ 1) (k : ℕ) : symmAvg n a k ≤ 1 := by
  calc symmAvg n a k
      ≤ (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * ∑ _σ : finPerm n, 1 := by
        rw [symmAvg]
        gcongr with σ
        exact Finset.prod_le_one (fun _ _ ↦ zero_le) fun i _ ↦ ha i _
    _ = 1 := by
        simp [ENNReal.inv_mul_cancel (card_finPerm_ne_zero n) (card_finPerm_ne_top n)]

lemma empAvg_le_one (ha : ∀ i j, a i j ≤ 1) (i : ℕ) : empAvg n a i ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [empAvg]
  calc empAvg n a i ≤ (n : ℝ≥0∞)⁻¹ * ∑ _j ∈ Finset.range n, 1 := by
        rw [empAvg]; gcongr; exact ha i _
    _ = 1 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp)

/-- Translating the sum over `Iₙ` by an element of `Iₙ`. -/
lemma sum_finPerm_mul_right {M : Type*} [AddCommMonoid M] (F : Equiv.Perm ℕ → M)
    {τ : Equiv.Perm ℕ} (hτ : τ ∈ finPerm n) :
    ∑ σ : finPerm n, F ((σ : Equiv.Perm ℕ) * τ) = ∑ σ : finPerm n, F σ :=
  Fintype.sum_equiv (Equiv.mulRight (⟨τ, hτ⟩ : finPerm n))
    (fun σ ↦ F ((σ : Equiv.Perm ℕ) * τ)) (fun σ ↦ F σ) fun _ ↦ rfl

/-- Elements of `Iₙ` permute `{0, …, n−1}`: re-indexing a sum over `range n`. -/
lemma sum_range_comp_finPerm {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    {σ : Equiv.Perm ℕ} (hσ : σ ∈ finPerm n) :
    ∑ j ∈ Finset.range n, f (σ j) = ∑ j ∈ Finset.range n, f j :=
  Equiv.Perm.sum_comp σ (Finset.range n) f fun j hj ↦ by
    by_contra hlt
    exact hj (hσ j (not_lt.1 (by simpa using hlt)))

lemma swap_mem_finPerm {k j : ℕ} (hk : k < n) (hj : j < n) : Equiv.swap k j ∈ finPerm n :=
  fun i hi ↦ Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- The exact one-step identity: `(n − k) ∑_σ ∏_{i<k+1} = ∑_σ (∏_{i<k}) · ∑_{j ∈ [k,n)} a k (σ j)`,
by translating with the transpositions `(k j)`, `k ≤ j < n`. -/
lemma sum_symmAvg_succ (hk : k < n) :
    ((n - k : ℕ) : ℝ≥0∞) * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)
      = ∑ σ : finPerm n, (∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i))
          * ∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j) := by
  have key : ∀ j ∈ Finset.Ico k n,
      ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)
        = ∑ σ : finPerm n,
            (∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)) * a k ((σ : Equiv.Perm ℕ) j) := by
    intro j hj
    obtain ⟨hkj, hjn⟩ := Finset.mem_Ico.1 hj
    rw [← sum_finPerm_mul_right
      (fun ρ ↦ ∏ i ∈ Finset.range (k + 1), a i (ρ i)) (swap_mem_finPerm hk hjn)]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [Finset.prod_range_succ]
    congr 1
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      have hik : i < k := Finset.mem_range.1 hi
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  calc ((n - k : ℕ) : ℝ≥0∞)
        * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)
      = ∑ j ∈ Finset.Ico k n,
          ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ = ∑ j ∈ Finset.Ico k n, ∑ σ : finPerm n,
          (∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)) * a k ((σ : Equiv.Perm ℕ) j) :=
        Finset.sum_congr rfl key
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ ↦ by rw [Finset.mul_sum]

/-- The one-coordinate case: the symmetrised average of a single row is its empirical average. -/
lemma symmAvg_one (hn : 0 < n) : symmAvg n a 1 = empAvg n a 0 := by
  have h := sum_symmAvg_succ (a := a) (k := 0) hn
  simp only [Nat.sub_zero, Finset.range_zero, Finset.prod_empty, one_mul, zero_add,
    Finset.range_one, Finset.prod_singleton] at h
  have hIco : Finset.Ico 0 n = Finset.range n := by
    rw [Finset.range_eq_Ico]
  rw [hIco] at h
  have hre : ∀ σ : finPerm n, ∑ j ∈ Finset.range n, a 0 ((σ : Equiv.Perm ℕ) j)
      = ∑ j ∈ Finset.range n, a 0 j := fun σ ↦ sum_range_comp_finPerm _ σ.2
  rw [Finset.sum_congr rfl fun σ _ ↦ hre σ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [symmAvg, empAvg]
  simp only [Finset.range_one, Finset.prod_singleton]
  calc (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * ∑ σ : finPerm n, a 0 ((σ : Equiv.Perm ℕ) 0)
      = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * ((n : ℝ≥0∞)⁻¹
          * ((n : ℝ≥0∞) * ∑ σ : finPerm n, a 0 ((σ : Equiv.Perm ℕ) 0))) := by
        rw [← mul_assoc ((n : ℝ≥0∞)⁻¹), ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne')
          (by simp), one_mul]
    _ = (n : ℝ≥0∞)⁻¹ * ((Fintype.card (finPerm n) : ℝ≥0∞)⁻¹
          * ((Fintype.card (finPerm n) : ℝ≥0∞) * ∑ j ∈ Finset.range n, a 0 j)) := by
        rw [h]; ring
    _ = (n : ℝ≥0∞)⁻¹ * ∑ j ∈ Finset.range n, a 0 j := by
        rw [← mul_assoc ((Fintype.card (finPerm n) : ℝ≥0∞)⁻¹),
          ENNReal.inv_mul_cancel (card_finPerm_ne_zero n) (card_finPerm_ne_top n), one_mul]

variable (n a) in
/-- The accumulated error `∑_{j<k} j/(n−j)` in the symmetrisation estimate. -/
def symmErr (k : ℕ) : ℝ≥0∞ := ∑ j ∈ Finset.range k, (j : ℝ≥0∞) / ((n - j : ℕ) : ℝ≥0∞)

lemma symmErr_le : symmErr n k ≤ (k : ℝ≥0∞) * k / ((n - k : ℕ) : ℝ≥0∞) := by
  calc symmErr n k ≤ ∑ _j ∈ Finset.range k, (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hjk : j < k := Finset.mem_range.1 hj
        have hsub : n - k ≤ n - j := Nat.sub_le_sub_left hjk.le n
        exact ENNReal.div_le_div (by exact_mod_cast hjk.le) (by exact_mod_cast hsub)
    _ = (k : ℝ≥0∞) * k / ((n - k : ℕ) : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc]

/-- One-step upper bound: `symmAvg (k+1) ≤ empAvg k · symmAvg k + k/(n−k)`. -/
lemma symmAvg_succ_le (ha : ∀ i j, a i j ≤ 1) (hk : k < n) :
    symmAvg n a (k + 1) ≤ empAvg n a k * symmAvg n a k + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) := by
  have hnk0 : ((n - k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  have hnktop : ((n - k : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  -- `(n−k) · S(k+1) ≤ A_k · S k` where `A_k = ∑_{j<n} a k j`
  have hupper : ((n - k : ℕ) : ℝ≥0∞)
        * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)
      ≤ (∑ j ∈ Finset.range n, a k j)
        * ∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i) := by
    rw [sum_symmAvg_succ hk, Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ ↦ ?_
    rw [mul_comm ((∑ j ∈ Finset.range n, a k j))]
    gcongr
    calc ∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j)
        ≤ ∑ j ∈ Finset.range n, a k ((σ : Equiv.Perm ℕ) j) := by
          refine Finset.sum_le_sum_of_subset fun j hj ↦ ?_
          rw [Finset.mem_range]
          exact (Finset.mem_Ico.1 hj).2
      _ = ∑ j ∈ Finset.range n, a k j := sum_range_comp_finPerm _ σ.2
  -- divide by `|Iₙ|` and by `n − k`
  have h1 : ((n - k : ℕ) : ℝ≥0∞) * symmAvg n a (k + 1)
      ≤ (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) := by
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast ((Nat.zero_lt_of_lt hk)).ne'
    calc ((n - k : ℕ) : ℝ≥0∞) * symmAvg n a (k + 1)
        = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * (((n - k : ℕ) : ℝ≥0∞)
            * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)) := by
          rw [symmAvg]; ring
      _ ≤ (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * ((∑ j ∈ Finset.range n, a k j)
            * ∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)) := by
          gcongr
      _ = (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) := by
          rw [empAvg, symmAvg, ← mul_assoc ((n : ℝ≥0∞)), ← mul_assoc ((n : ℝ≥0∞)),
            ENNReal.mul_inv_cancel hn0 (by simp), one_mul]
          ring
  calc symmAvg n a (k + 1)
      = ((n - k : ℕ) : ℝ≥0∞) * symmAvg n a (k + 1) / ((n - k : ℕ) : ℝ≥0∞) := by
        rw [mul_comm (((n - k : ℕ) : ℝ≥0∞)), mul_div_assoc, ENNReal.div_self hnk0 hnktop,
          mul_one]
    _ ≤ (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) / ((n - k : ℕ) : ℝ≥0∞) := by gcongr
    _ = (((n - k : ℕ) : ℝ≥0∞) + (k : ℝ≥0∞)) * (empAvg n a k * symmAvg n a k)
          / ((n - k : ℕ) : ℝ≥0∞) := by
        congr 2
        have : (n : ℝ≥0∞) = ((n - k + k : ℕ) : ℝ≥0∞) := by
          rw [Nat.sub_add_cancel hk.le]
        rw [this]
        push_cast
        ring
    _ = empAvg n a k * symmAvg n a k
          + (k : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) / ((n - k : ℕ) : ℝ≥0∞) := by
        rw [add_mul, ENNReal.add_div, mul_comm (((n - k : ℕ) : ℝ≥0∞)), mul_div_assoc,
          ENNReal.div_self hnk0 hnktop, mul_one]
    _ ≤ empAvg n a k * symmAvg n a k + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) := by
        gcongr
        calc (k : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) ≤ (k : ℝ≥0∞) * (1 * 1) := by
              gcongr
              · exact empAvg_le_one ha k
              · exact symmAvg_le_one ha k
          _ = (k : ℝ≥0∞) := by rw [mul_one, mul_one]

/-- One-step lower bound: `empAvg k · symmAvg k ≤ symmAvg (k+1) + k/n`. -/
lemma empAvg_mul_symmAvg_le (ha : ∀ i j, a i j ≤ 1) (hk : k < n) :
    empAvg n a k * symmAvg n a k ≤ symmAvg n a (k + 1) + (k : ℝ≥0∞) / (n : ℝ≥0∞) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast ((Nat.zero_lt_of_lt hk)).ne'
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := by simp
  -- `A_k · S k ≤ k · S k + (n − k) · S (k+1)`
  have hlower : (∑ j ∈ Finset.range n, a k j)
        * ∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)
      ≤ (k : ℝ≥0∞) * (∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i))
        + ((n - k : ℕ) : ℝ≥0∞)
          * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i) := by
    rw [sum_symmAvg_succ hk, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun σ _ ↦ ?_
    have hsplit : ∑ j ∈ Finset.range n, a k j
        = ∑ j ∈ Finset.range k, a k ((σ : Equiv.Perm ℕ) j)
          + ∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j) := by
      rw [Finset.sum_range_add_sum_Ico (fun j ↦ a k ((σ : Equiv.Perm ℕ) j)) hk.le,
        sum_range_comp_finPerm (fun j ↦ a k j) σ.2]
    calc (∑ j ∈ Finset.range n, a k j) * ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)
        = (∑ j ∈ Finset.range k, a k ((σ : Equiv.Perm ℕ) j))
              * ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)
            + (∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j))
              * ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i) := by
          rw [hsplit, add_mul]
      _ ≤ (k : ℝ≥0∞) * ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)
            + (∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i))
              * ∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j) := by
          rw [mul_comm (∑ j ∈ Finset.Ico k n, a k ((σ : Equiv.Perm ℕ) j))]
          gcongr
          calc ∑ j ∈ Finset.range k, a k ((σ : Equiv.Perm ℕ) j)
              ≤ ∑ _j ∈ Finset.range k, 1 := Finset.sum_le_sum fun j _ ↦ ha k _
            _ = (k : ℝ≥0∞) := by simp
  have h2 : (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k)
      ≤ (k : ℝ≥0∞) + (n : ℝ≥0∞) * symmAvg n a (k + 1) := by
    calc (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k)
        = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * ((∑ j ∈ Finset.range n, a k j)
            * ∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i)) := by
          rw [empAvg, symmAvg, ← mul_assoc ((n : ℝ≥0∞)), ← mul_assoc ((n : ℝ≥0∞)),
            ENNReal.mul_inv_cancel hn0 hntop, one_mul]
          ring
      _ ≤ (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹
            * ((k : ℝ≥0∞) * (∑ σ : finPerm n, ∏ i ∈ Finset.range k, a i ((σ : Equiv.Perm ℕ) i))
              + ((n - k : ℕ) : ℝ≥0∞)
                * ∑ σ : finPerm n, ∏ i ∈ Finset.range (k + 1), a i ((σ : Equiv.Perm ℕ) i)) := by
          gcongr
      _ = (k : ℝ≥0∞) * symmAvg n a k + ((n - k : ℕ) : ℝ≥0∞) * symmAvg n a (k + 1) := by
          rw [mul_add, symmAvg, symmAvg]
          ring
      _ ≤ (k : ℝ≥0∞) * 1 + (n : ℝ≥0∞) * symmAvg n a (k + 1) := by
          gcongr
          · exact symmAvg_le_one ha k
          · exact_mod_cast Nat.sub_le n k
      _ = (k : ℝ≥0∞) + (n : ℝ≥0∞) * symmAvg n a (k + 1) := by rw [mul_one]
  calc empAvg n a k * symmAvg n a k
      = (n : ℝ≥0∞) * (empAvg n a k * symmAvg n a k) / (n : ℝ≥0∞) := by
        rw [mul_comm ((n : ℝ≥0∞)), mul_div_assoc, ENNReal.div_self hn0 hntop, mul_one]
    _ ≤ ((k : ℝ≥0∞) + (n : ℝ≥0∞) * symmAvg n a (k + 1)) / (n : ℝ≥0∞) := by gcongr
    _ = (k : ℝ≥0∞) / (n : ℝ≥0∞) + (n : ℝ≥0∞) * symmAvg n a (k + 1) / (n : ℝ≥0∞) := by
        rw [ENNReal.add_div]
    _ = (k : ℝ≥0∞) / (n : ℝ≥0∞) + symmAvg n a (k + 1) := by
        rw [mul_comm ((n : ℝ≥0∞)), mul_div_assoc, ENNReal.div_self hn0 hntop, mul_one]
    _ = symmAvg n a (k + 1) + (k : ℝ≥0∞) / (n : ℝ≥0∞) := add_comm _ _

/-- **The symmetrisation estimate, upper half**: the symmetrised product is at most the product
of the empirical averages plus `∑_{j<k} j/(n−j)`. -/
theorem symmAvg_le_prod_add (ha : ∀ i j, a i j ≤ 1) (hk : k ≤ n) :
    symmAvg n a k ≤ (∏ i ∈ Finset.range k, empAvg n a i) + symmErr n k := by
  induction k with
  | zero => simp [symmErr]
  | succ k ih =>
      have hkn : k < n := hk
      calc symmAvg n a (k + 1)
          ≤ empAvg n a k * symmAvg n a k + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) :=
            symmAvg_succ_le ha hkn
        _ ≤ empAvg n a k * ((∏ i ∈ Finset.range k, empAvg n a i) + symmErr n k)
              + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) := by
            gcongr
            exact ih hkn.le
        _ ≤ (∏ i ∈ Finset.range (k + 1), empAvg n a i) + symmErr n k
              + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) := by
            rw [mul_add, Finset.prod_range_succ, mul_comm (∏ i ∈ Finset.range k, empAvg n a i)]
            gcongr
            calc empAvg n a k * symmErr n k ≤ 1 * symmErr n k := by
                  gcongr; exact empAvg_le_one ha k
              _ = symmErr n k := one_mul _
        _ = (∏ i ∈ Finset.range (k + 1), empAvg n a i) + symmErr n (k + 1) := by
            rw [symmErr, symmErr, Finset.sum_range_succ, ← add_assoc]

/-- **The symmetrisation estimate, lower half**: the product of the empirical averages is at most
the symmetrised product plus `∑_{j<k} j/(n−j)`. -/
theorem prod_le_symmAvg_add (ha : ∀ i j, a i j ≤ 1) (hk : k ≤ n) :
    (∏ i ∈ Finset.range k, empAvg n a i) ≤ symmAvg n a k + symmErr n k := by
  induction k with
  | zero => simp [symmErr]
  | succ k ih =>
      have hkn : k < n := hk
      have hnk : (k : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) :=
        ENNReal.div_le_div le_rfl (by exact_mod_cast Nat.sub_le n k)
      calc ∏ i ∈ Finset.range (k + 1), empAvg n a i
          = empAvg n a k * ∏ i ∈ Finset.range k, empAvg n a i := by
            rw [Finset.prod_range_succ, mul_comm]
        _ ≤ empAvg n a k * (symmAvg n a k + symmErr n k) := by
            gcongr
            exact ih hkn.le
        _ ≤ empAvg n a k * symmAvg n a k + symmErr n k := by
            rw [mul_add]
            gcongr
            calc empAvg n a k * symmErr n k ≤ 1 * symmErr n k := by
                  gcongr; exact empAvg_le_one ha k
              _ = symmErr n k := one_mul _
        _ ≤ symmAvg n a (k + 1) + (k : ℝ≥0∞) / (n : ℝ≥0∞) + symmErr n k := by
            gcongr
            exact empAvg_mul_symmAvg_le ha hkn
        _ ≤ symmAvg n a (k + 1) + symmErr n (k + 1) := by
            rw [show symmErr n (k + 1) = symmErr n k + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) from by
              rw [symmErr, symmErr, Finset.sum_range_succ]]
            calc symmAvg n a (k + 1) + (k : ℝ≥0∞) / (n : ℝ≥0∞) + symmErr n k
                ≤ symmAvg n a (k + 1) + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞) + symmErr n k := by
                  gcongr
              _ = symmAvg n a (k + 1) + (symmErr n k + (k : ℝ≥0∞) / ((n - k : ℕ) : ℝ≥0∞)) := by
                  ring

end Estimate

/-! ### Georgii (7.17): extreme exchangeable measures are product measures -/

section Extreme

variable {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]

/-- The indicator data of a family of single-spin sets along a configuration. -/
private def rowOf (A : ℕ → Set E) (ω : ℕ → E) : ℕ → ℕ → ℝ≥0∞ := fun i j ↦
  (A i).indicator 1 (ω j)

omit [MeasurableSpace E] [IsProbabilityMeasure μ] in
private lemma rowOf_le_one (A : ℕ → Set E) (ω : ℕ → E) (i j : ℕ) : rowOf A ω i j ≤ 1 := by
  unfold rowOf
  by_cases h : ω j ∈ A i <;> simp [h]

private lemma measurableSet_rangePi {A : ℕ → Set E} (hA : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet ((Finset.range k : Set ℕ).pi A) :=
  MeasurableSet.pi (Finset.range k).countable_toSet fun i _ ↦ hA i

/-- The symmetrisation of a box is the symmetrised product of the rows. -/
private lemma symmKernel_rangePi {A : ℕ → Set E} (hA : ∀ i, MeasurableSet (A i)) (n k : ℕ)
    (ω : ℕ → E) :
    symmKernel E n ω ((Finset.range k : Set ℕ).pi A) = symmAvg n (rowOf A ω) k := by
  rw [symmKernel_apply n ω (measurableSet_rangePi hA k), symmAvg, symmSum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  by_cases h : permute (σ : Equiv.Perm ℕ) ω ∈ (Finset.range k : Set ℕ).pi A
  · rw [Set.indicator_of_mem h, Pi.one_apply]
    refine (Finset.prod_eq_one fun i hi ↦ ?_).symm
    have hmem : ω ((σ : Equiv.Perm ℕ) i) ∈ A i := h i (by simpa using hi)
    simp [rowOf, hmem]
  · rw [Set.indicator_of_notMem h]
    obtain ⟨i, hi, hmem⟩ : ∃ i ∈ Finset.range k, ω ((σ : Equiv.Perm ℕ) i) ∉ A i := by
      by_contra hcon
      push Not at hcon
      exact h fun i hi ↦ hcon i (by simpa using hi)
    exact (Finset.prod_eq_zero hi (by simp [rowOf, hmem])).symm

/-- The empirical identification: the symmetrisation of `{ω | ω 0 ∈ A i}` is the empirical
frequency of `A i` on the first `n` coordinates. -/
private lemma symmKernel_single {A : ℕ → Set E} (hA : ∀ i, MeasurableSet (A i)) {n : ℕ}
    (hn : 0 < n) (ω : ℕ → E) (i : ℕ) :
    symmKernel E n ω {ω' : ℕ → E | ω' 0 ∈ A i} = empAvg n (rowOf A ω) i := by
  have hbox : {ω' : ℕ → E | ω' 0 ∈ A i} = (Finset.range 1 : Set ℕ).pi (fun _ ↦ A i) := by
    ext ω'
    simp
  rw [hbox, symmKernel_rangePi (fun _ ↦ hA i) n 1 ω, symmAvg_one hn]
  rfl

/-- Along an invariant measure trivial on the symmetric σ-algebra, the symmetrisations of an
event converge a.e. to its measure. -/
private lemma ae_tendsto_symmKernel (hμ : μ ∈ (exchangeableSpec E).invariant)
    (htriv : μ ∈ trivialOn (symmetricSigmaAlgebra E)) {B : Set (ℕ → E)} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ symmKernel E n ω B) atTop (𝓝 (μ B)) := by
  have hint : Integrable (B.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const 1).indicator hB
  have hlevy := hint.tendsto_ae_condExp_of_antitone (ℱ := symmSub E) symmSub_antitone symmSub_le
  have hker : ∀ᵐ ω ∂μ, ∀ n, (μ[B.indicator fun _ ↦ (1 : ℝ) | symmSub E n]) ω
      = (symmKernel E n ω B).toReal :=
    ae_all_iff.2 fun n ↦ AbstractSpecification.condExp_sub_ae_eq (γ := exchangeableSpec E) hμ n hB
  have hconst : ∃ c : ℝ, (μ[B.indicator fun _ ↦ (1 : ℝ) | ⨅ n, symmSub E n]) =ᵐ[μ] fun _ ↦ c := by
    refine exists_ae_eq_const_of_forall_measure_eq_zero_or_one (𝒜 := symmetricSigmaAlgebra E)
      symmetricSigmaAlgebra_le htriv ?_
    exact (stronglyMeasurable_condExp (m := ⨅ n, symmSub E n)).measurable
  obtain ⟨c, hc⟩ := hconst
  have hcval : c = (μ B).toReal := by
    have h1 : ∫ ω, (μ[B.indicator fun _ ↦ (1 : ℝ) | ⨅ n, symmSub E n]) ω ∂μ
        = ∫ ω, B.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ :=
      integral_condExp ((iInf_le _ 0).trans (symmSub_le 0))
    rw [integral_congr_ae hc, integral_const, integral_indicator_const _ hB] at h1
    simpa [measureReal_def] using h1
  filter_upwards [hlevy, hker, hc] with ω hω hkerω hcω
  have htoReal : Tendsto (fun n ↦ (symmKernel E n ω B).toReal) atTop (𝓝 (μ B).toReal) := by
    have h := hω
    rw [hcω, hcval] at h
    exact h.congr fun n ↦ hkerω n
  rw [← ENNReal.tendsto_toReal_iff (fun n ↦ measure_ne_top _ _) (measure_ne_top _ _)]
  exact htoReal

/-- The error `symmErr n k` vanishes as `n → ∞` for each fixed `k`. -/
private lemma tendsto_symmErr (k : ℕ) : Tendsto (fun n ↦ symmErr n k) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n : ℕ ↦ (k : ℝ≥0∞) * k * ((n - k : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ ↦ ((n - k : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_sub_atTop_nat k)
    simpa using ENNReal.Tendsto.const_mul hinv
      (Or.inr (ENNReal.mul_ne_top (by simp) (by simp)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun n ↦ zero_le) fun n ↦ ?_
  calc symmErr n k ≤ (k : ℝ≥0∞) * k / ((n - k : ℕ) : ℝ≥0∞) := symmErr_le
    _ = (k : ℝ≥0∞) * k * ((n - k : ℕ) : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]

/-- **Georgii (7.17), the substantial half, in coordinates.** An extreme exchangeable probability
measure gives every finite-dimensional box the product of its one-coordinate masses. -/
theorem measure_rangePi_eq_prod_of_mem_extremePoints
    (hμ : μ ∈ (exchangeableSpec E).invariant.extremePoints ℝ≥0∞)
    {A : ℕ → Set E} (hA : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    μ ((Finset.range k : Set ℕ).pi A) = ∏ i ∈ Finset.range k, μ {ω : ℕ → E | ω 0 ∈ A i} := by
  have hμinv : μ ∈ (exchangeableSpec E).invariant := hμ.1
  have htriv : μ ∈ trivialOn (symmetricSigmaAlgebra E) :=
    (mem_extremePoints_iff_mem_trivialOn_symmetric hμinv).1 hμ
  have hsingle : ∀ i, MeasurableSet {ω' : ℕ → E | ω' 0 ∈ A i} := fun i ↦
    (hA i).preimage (measurable_pi_apply 0)
  set X : ℕ → ℕ → (ℕ → E) → ℝ≥0∞ := fun i n ω ↦ symmKernel E n ω {ω' : ℕ → E | ω' 0 ∈ A i}
    with hX
  set P : ℝ≥0∞ := ∏ i ∈ Finset.range k, μ {ω : ℕ → E | ω 0 ∈ A i} with hP
  -- invariance: `μ(B) = ∫ γₙ(B | ·) dμ`
  have hinv : ∀ (n : ℕ) {B : Set (ℕ → E)}, MeasurableSet B →
      μ B = ∫⁻ ω, symmKernel E n ω B ∂μ := by
    intro n B hB
    conv_lhs => rw [← hμinv.2 n]
    rw [Measure.bind_apply hB ((exchangeableSpec E).aemeasurable_ker n μ)]
    rfl
  -- a.e. convergence of the product of the one-coordinate symmetrisations
  have haetendsto : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∏ i ∈ Finset.range k, X i n ω) atTop (𝓝 P) := by
    have hae : ∀ᵐ ω ∂μ, ∀ i,
        Tendsto (fun n ↦ X i n ω) atTop (𝓝 (μ {ω' : ℕ → E | ω' 0 ∈ A i})) :=
      ae_all_iff.2 fun i ↦ ae_tendsto_symmKernel hμinv htriv (hsingle i)
    filter_upwards [hae] with ω hω
    have hgen : ∀ m : ℕ, Tendsto (fun n ↦ ∏ i ∈ Finset.range m, X i n ω) atTop
        (𝓝 (∏ i ∈ Finset.range m, μ {ω' : ℕ → E | ω' 0 ∈ A i})) := by
      intro m
      induction m with
      | zero => simp only [Finset.range_zero, Finset.prod_empty]; exact tendsto_const_nhds
      | succ m ih =>
          simp only [Finset.prod_range_succ]
          exact ENNReal.Tendsto.mul ih (Or.inr (measure_ne_top _ _)) (hω m)
            (Or.inr (ne_top_of_le_ne_top ENNReal.one_ne_top
              (Finset.prod_le_one (fun _ _ ↦ zero_le) fun i _ ↦ prob_le_one)))
    exact hgen k
  -- dominated convergence
  have hmeasX : ∀ n, Measurable fun ω ↦ ∏ i ∈ Finset.range k, X i n ω := fun n ↦
    Finset.measurable_prod _ fun i _ ↦
      (Kernel.measurable_coe (symmKernel E n) (hsingle i)).mono (symmSub_le n) le_rfl
  have hdct : Tendsto (fun n ↦ ∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ) atTop (𝓝 P) := by
    have h := tendsto_lintegral_of_dominated_convergence (bound := fun _ ↦ 1)
      (F := fun n ω ↦ ∏ i ∈ Finset.range k, X i n ω) hmeasX
      (fun n ↦ ae_of_all _ fun ω ↦
        Finset.prod_le_one (fun _ _ ↦ zero_le) fun i _ ↦ prob_le_one)
      (by simp) haetendsto
    simpa using h
  -- the two-sided symmetrisation estimate, integrated
  have hone : ∀ᶠ n in atTop, μ ((Finset.range k : Set ℕ).pi A)
      ≤ (∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ) + symmErr n k := by
    filter_upwards [eventually_ge_atTop (max k 1)] with n hn
    have hkn : k ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : 0 < n := lt_of_lt_of_le (by omega) hn
    calc μ ((Finset.range k : Set ℕ).pi A)
        = ∫⁻ ω, symmKernel E n ω ((Finset.range k : Set ℕ).pi A) ∂μ :=
          hinv n (measurableSet_rangePi hA k)
      _ ≤ ∫⁻ ω, (∏ i ∈ Finset.range k, X i n ω) + symmErr n k ∂μ := by
          refine lintegral_mono fun ω ↦ ?_
          rw [symmKernel_rangePi hA n k ω,
            Finset.prod_congr rfl fun i (_ : i ∈ Finset.range k) ↦
              symmKernel_single hA hn0 ω i]
          exact symmAvg_le_prod_add (rowOf_le_one A ω) hkn
      _ = (∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ) + symmErr n k := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have htwo : ∀ᶠ n in atTop, (∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ)
      ≤ μ ((Finset.range k : Set ℕ).pi A) + symmErr n k := by
    filter_upwards [eventually_ge_atTop (max k 1)] with n hn
    have hkn : k ≤ n := le_trans (le_max_left _ _) hn
    have hn0 : 0 < n := lt_of_lt_of_le (by omega) hn
    calc ∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ
        ≤ ∫⁻ ω, symmKernel E n ω ((Finset.range k : Set ℕ).pi A) + symmErr n k ∂μ := by
          refine lintegral_mono fun ω ↦ ?_
          rw [symmKernel_rangePi hA n k ω,
            Finset.prod_congr rfl fun i (_ : i ∈ Finset.range k) ↦
              symmKernel_single hA hn0 ω i]
          exact prod_le_symmAvg_add (rowOf_le_one A ω) hkn
      _ = μ ((Finset.range k : Set ℕ).pi A) + symmErr n k := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            ← hinv n (measurableSet_rangePi hA k)]
  -- squeeze
  have hupper : μ ((Finset.range k : Set ℕ).pi A) ≤ P := by
    have hlim : Tendsto (fun n ↦ (∫⁻ ω, ∏ i ∈ Finset.range k, X i n ω ∂μ) + symmErr n k)
        atTop (𝓝 P) := by
      simpa using hdct.add (tendsto_symmErr k)
    exact ge_of_tendsto hlim hone
  have hlower : P ≤ μ ((Finset.range k : Set ℕ).pi A) := by
    have hlim : Tendsto (fun n ↦ μ ((Finset.range k : Set ℕ).pi A) + symmErr n k)
        atTop (𝓝 (μ ((Finset.range k : Set ℕ).pi A))) := by
      simpa using tendsto_const_nhds.add (tendsto_symmErr k)
    exact le_of_tendsto_of_tendsto hdct hlim htwo
  exact le_antisymm hupper hlower

/-- **Georgii (7.17), the substantial half.** An extreme exchangeable probability measure is the
i.i.d. product of its one-dimensional marginal. No hypothesis on the state space. -/
theorem eq_infinitePi_of_mem_extremePoints
    (hμ : μ ∈ (exchangeableSpec E).invariant.extremePoints ℝ≥0∞) :
    μ = Measure.infinitePi fun _ : ℕ ↦ μ.map fun ω ↦ ω 0 := by
  have : IsProbabilityMeasure (μ.map fun ω : ℕ → E ↦ ω 0) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable
  refine Measure.eq_infinitePi _ fun s t ht ↦ ?_
  classical
  set k : ℕ := s.sup id + 1 with hk
  have hsub : s ⊆ Finset.range k := fun i hi ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  set t' : ℕ → Set E := fun i ↦ if i ∈ s then t i else univ with ht'
  have ht'meas : ∀ i, MeasurableSet (t' i) := fun i ↦ by
    by_cases hi : i ∈ s <;> simp [ht', hi, ht i]
  have hpi : (s : Set ℕ).pi t = (Finset.range k : Set ℕ).pi t' := by
    ext ω
    constructor
    · intro hω i hi
      by_cases his : i ∈ s
      · simpa [ht', his] using hω i his
      · simp [ht', his]
    · intro hω i hi
      have h2 := hω i (hsub hi)
      simp only [ht'] at h2
      rwa [ite_eq_left (show i ∈ s by simpa using hi)] at h2
  rw [hpi, measure_rangePi_eq_prod_of_mem_extremePoints hμ ht'meas k]
  have hmap : ∀ i, μ {ω : ℕ → E | ω 0 ∈ t' i} = (μ.map fun ω : ℕ → E ↦ ω 0) (t' i) := fun i ↦ by
    rw [Measure.map_apply (measurable_pi_apply 0) (ht'meas i)]
    rfl
  rw [Finset.prod_congr rfl fun i _ ↦ hmap i]
  refine (Finset.prod_subset hsub fun i _ his ↦ ?_).symm.trans
    (Finset.prod_congr rfl fun i hi ↦ by rw [ht']; simp [hi])
  simp [ht', his]

/-- **Georgii (7.17).** The extreme points of the exchangeable probability measures are exactly
the i.i.d. product measures. -/
theorem mem_extremePoints_exchangeable_iff {μ : Measure (ℕ → E)} :
    μ ∈ (exchangeableSpec E).invariant.extremePoints ℝ≥0∞ ↔
      ∃ lam : Measure E, IsProbabilityMeasure lam
        ∧ μ = Measure.infinitePi fun _ : ℕ ↦ lam := by
  constructor
  · intro hμ
    have : IsProbabilityMeasure μ := hμ.1.1
    exact ⟨μ.map fun ω ↦ ω 0,
      Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable,
      eq_infinitePi_of_mem_extremePoints hμ⟩
  · rintro ⟨lam, hlam, rfl⟩
    exact infinitePi_mem_extremePoints

end Extreme

/-! ### Georgii (7.31): de Finetti's theorem in the version of Dynkin -/

section DeFinetti

variable [StandardBorelSpace E] [Nonempty E] {μ : Measure (ℕ → E)} [IsProbabilityMeasure μ]

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
/-- Membership of the i.i.d. product in `𝒫_I ∩ P_𝓘` for a probability `lam`. -/
private lemma iid_mem_inter (lam : Measure E) (hlam : IsProbabilityMeasure lam) :
    Measure.infinitePi (fun _ : ℕ ↦ lam)
      ∈ (exchangeableSpec E).invariant ∩ trivialOn ((exchangeableSpec E).tail) := by
  have := hlam
  exact ⟨(mem_exchangeableSpec_invariant_iff _).2 ⟨inferInstance, isExchangeable_infinitePi⟩,
    mem_trivialOn_symmetricSigmaAlgebra_infinitePi⟩

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
/-- Members of `𝒫_I ∩ P_𝓘` are i.i.d. products of their marginals. -/
private lemma eq_iid_of_mem_inter {ν : Measure (ℕ → E)}
    (hν : ν ∈ (exchangeableSpec E).invariant ∩ trivialOn ((exchangeableSpec E).tail)) :
    ν = Measure.infinitePi fun _ : ℕ ↦ ν.map fun ω ↦ ω 0 := by
  have : IsProbabilityMeasure ν := hν.1.1
  exact eq_infinitePi_of_mem_extremePoints
    (AbstractSpecification.mem_extremePoints_of_mem_trivialOn hν.1 hν.2)

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
private lemma measurable_iid :
    Measurable fun lam : Measure E ↦ Measure.infinitePi fun _ : ℕ ↦ lam :=
  Measure.measurable_infinitePi_const

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
private lemma measurable_marg :
    Measurable fun ν : Measure (ℕ → E) ↦ ν.map fun ω ↦ ω 0 :=
  Measure.measurable_map _ (measurable_pi_apply 0)

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
private lemma measurableSet_probSet :
    MeasurableSet {lam : Measure E | IsProbabilityMeasure lam} := by
  have h : {lam : Measure E | IsProbabilityMeasure lam}
      = (fun lam : Measure E ↦ lam univ) ⁻¹' {1} := by
    ext lam
    simp [isProbabilityMeasure_iff]
  rw [h]
  exact (measurableSet_singleton 1).preimage (Measure.measurable_coe .univ)

omit [Nonempty E] in
/-- **Georgii, Example (7.31): de Finetti's theorem in the version of Dynkin.** Over a standard
Borel state space, every exchangeable probability measure on `E^ℕ` is the mixture `∫ λ^ℕ m(dλ)`
of i.i.d. product measures under a unique probability measure `m` on `𝒫(E, ℰ)`. -/
theorem existsUnique_mixing_of_isExchangeable (hμ : IsExchangeable μ) :
    ∃! m : Measure (Measure E), IsProbabilityMeasure m
      ∧ m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0
      ∧ m.bind (fun lam ↦ Measure.infinitePi fun _ : ℕ ↦ lam) = μ := by
  classical
  set γ := exchangeableSpec E with hγ
  have hμinv : μ ∈ γ.invariant := (mem_exchangeableSpec_invariant_iff μ).2 ⟨inferInstance, hμ⟩
  obtain ⟨π, hMarkov, hπ⟩ := AbstractSpecification.exists_isPAKernel_invariant (γ := γ)
    ⟨μ, hμinv⟩
  have hP : ∀ ν ∈ γ.invariant, IsProbabilityMeasure ν := fun ν hν ↦ hν.1
  have hPm : MeasurableSet γ.invariant := AbstractSpecification.measurableSet_invariant γ
  obtain ⟨w, ⟨hwprob, hwcompl, hwjoin⟩, hwuniq⟩ :=
    hπ.exists_unique_representing_weight (𝒜 := γ.tail) γ.tail_le hP hPm hμinv
  set iid : Measure E → Measure (ℕ → E) := fun lam ↦ Measure.infinitePi fun _ : ℕ ↦ lam
    with hiid
  set marg : Measure (ℕ → E) → Measure E := fun ν ↦ ν.map fun ω ↦ ω 0 with hmarg
  -- the mixing measure: push the representing weight to the marginals
  refine ⟨w.map marg, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Measure.isProbabilityMeasure_map measurable_marg.aemeasurable
  · rw [Measure.map_apply measurable_marg measurableSet_probSet.compl]
    refine measure_mono_null (fun ν hν ↦ ?_) hwcompl
    intro hmem
    have : IsProbabilityMeasure ν := (hP ν hmem.1)
    exact hν (Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable)
  · -- `(w.map marg).bind iid = w.join = μ`
    refine Measure.ext fun B hB ↦ ?_
    have hiidB : Measurable fun lam ↦ iid lam B :=
      (Measure.measurable_coe hB).comp measurable_iid
    have h1 : (w.map marg).bind iid B = ∫⁻ ν, iid (marg ν) B ∂w := by
      rw [Measure.bind_apply hB measurable_iid.aemeasurable, lintegral_map hiidB measurable_marg]
    have h2 : ∫⁻ ν, iid (marg ν) B ∂w = ∫⁻ ν, ν B ∂w := by
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ ν ∂w, ν ∈ γ.invariant ∩ trivialOn γ.tail := ae_iff.2 hwcompl
      filter_upwards [hae] with ν hν
      conv_rhs => rw [eq_iid_of_mem_inter hν]
    rw [h1, h2, ← Measure.join_apply hB, hwjoin]
  · -- uniqueness: pull any mixing measure back to a representing weight
    rintro m ⟨hmprob, hmcompl, hmbind⟩
    have hmae : ∀ᵐ lam ∂m, IsProbabilityMeasure lam := by
      rw [ae_iff]
      convert hmcompl using 2
      ext lam
      simp
    -- `m.map iid` is a representing weight
    have hiidP : ∀ lam : Measure E, IsProbabilityMeasure lam →
        iid lam ∈ γ.invariant ∩ trivialOn γ.tail := fun lam hlam ↦ iid_mem_inter lam hlam
    have hw' : w = m.map iid := by
      refine (hwuniq (m.map iid) ⟨?_, ?_, ?_⟩).symm
      · exact Measure.isProbabilityMeasure_map measurable_iid.aemeasurable
      · -- the carried set is measurable: within `𝒫_I` triviality on `𝓘` is the countable set
        -- of equalities `ν = iid (marg ν)` on the generating π-system
        set D : Set (Measure (ℕ → E)) := {ν | ∀ t : Finset ℕ,
          ν (piNatGen (Ω := ℕ → E) t) = iid (marg ν) (piNatGen (Ω := ℕ → E) t)} with hD
        have hDmeas : MeasurableSet D := by
          have hDeq : D = ⋂ t : Finset ℕ, {ν : Measure (ℕ → E) |
              ν (piNatGen (Ω := ℕ → E) t) = iid (marg ν) (piNatGen (Ω := ℕ → E) t)} := by
            ext ν
            simp [hD, Set.mem_iInter]
          rw [hDeq]
          refine MeasurableSet.iInter fun t ↦ ?_
          exact measurableSet_eq_fun
            (Measure.measurable_coe (measurableSet_piNatGen (Ω := ℕ → E) t))
            ((Measure.measurable_coe (measurableSet_piNatGen (Ω := ℕ → E) t)).comp
              (measurable_iid.comp measurable_marg))
        have hPD : γ.invariant ∩ trivialOn γ.tail = γ.invariant ∩ D := by
          ext ν
          refine and_congr_right fun hν ↦ ?_
          constructor
          · intro htriv t
            conv_lhs => rw [eq_iid_of_mem_inter ⟨hν, htriv⟩]
          · intro hd
            have : IsProbabilityMeasure ν := hν.1
            have : IsProbabilityMeasure (marg ν) :=
              Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable
            have hext : ν = iid (marg ν) := by
              refine ext_of_generate_finite (piNatGenSet (ℕ → E))
                generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_ (by simp)
              rintro _ ⟨t, rfl⟩
              exact hd t
            rw [hext]
            exact (iid_mem_inter (marg ν) inferInstance).2
        rw [hPD, Measure.map_apply measurable_iid (hPm.inter hDmeas).compl]
        refine measure_mono_null (fun lam hlam ↦ ?_) hmcompl
        intro hprob
        have : IsProbabilityMeasure lam := hprob
        refine hlam ?_
        rw [← hPD]
        exact iid_mem_inter lam inferInstance
      · show (m.map iid).join = μ
        rw [show (m.map iid).join = m.bind iid from rfl, hmbind]
    -- recover `m` from the weight
    have hrec : ∀ (m' : Measure (Measure E)), m' {lam | IsProbabilityMeasure lam}ᶜ = 0 →
        (m'.map iid).map marg = m' := by
      intro m' hm'
      have hcongr : (fun lam ↦ marg (iid lam)) =ᵐ[m'] id := by
        have hae' : ∀ᵐ lam ∂m', IsProbabilityMeasure lam := by
          rw [ae_iff]
          convert hm' using 2
          ext lam
          simp
        filter_upwards [hae'] with lam hlam
        have := hlam
        change (Measure.infinitePi fun _ : ℕ ↦ lam).map (fun ω ↦ ω 0) = lam
        exact Measure.infinitePi_map_eval (μ := fun _ : ℕ ↦ lam) 0
      rw [Measure.map_map measurable_marg measurable_iid,
        show ((fun ν : Measure (ℕ → E) ↦ ν.map fun ω ↦ ω 0)
            ∘ fun lam : Measure E ↦ Measure.infinitePi fun _ : ℕ ↦ lam)
          = fun lam ↦ marg (iid lam) from rfl,
        Measure.map_congr hcongr, Measure.map_id]
    calc m = (m.map iid).map marg := (hrec m hmcompl).symm
      _ = w.map marg := by rw [← hw']

omit [StandardBorelSpace E] [Nonempty E] [IsProbabilityMeasure μ] in
/-- The converse sanity check to de Finetti: every mixture of i.i.d. product measures under a
weight carried by the probability measures is exchangeable, so the representation of
`existsUnique_mixing_of_isExchangeable` characterises exchangeability. -/
theorem isExchangeable_bind_infinitePi {m : Measure (Measure E)}
    (hm : m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0) :
    IsExchangeable (m.bind fun lam ↦ Measure.infinitePi fun _ : ℕ ↦ lam) := by
  intro σ hσ
  have hiid : Measurable fun lam : Measure E ↦ Measure.infinitePi fun _ : ℕ ↦ lam :=
    Measure.measurable_infinitePi_const
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.map_apply (measurable_permute σ) hB,
    Measure.bind_apply (measurable_permute σ hB) hiid.aemeasurable,
    Measure.bind_apply hB hiid.aemeasurable]
  refine lintegral_congr_ae ?_
  have hae : ∀ᵐ lam ∂m, IsProbabilityMeasure lam := by
    rw [ae_iff]
    convert hm using 2
    ext lam
    simp
  filter_upwards [hae] with lam hlam
  have := hlam
  calc Measure.infinitePi (fun _ : ℕ ↦ lam) (permute σ ⁻¹' B)
      = (Measure.infinitePi fun _ : ℕ ↦ lam).map (permute σ) B :=
        (Measure.map_apply (measurable_permute σ) hB).symm
    _ = Measure.infinitePi (fun _ : ℕ ↦ lam) B := by rw [isExchangeable_infinitePi σ hσ]

end DeFinetti

end MeasureTheory.GibbsMeasure

end

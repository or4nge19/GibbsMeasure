/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising

/-!
# The GKS (Griffiths–Kelly–Sherman) correlation inequalities

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., the discussion following
Theorem (6.9) (p. 100), and Section 9.1 (p. 365):

> "By an inequality of Griffiths (1967a), `μ₊^β(σ₀)` is a nonnegative nondecreasing function
> of `β`.  Consequently, there exists a critical inverse temperature `0 ≤ β_c ≤ ∞` such that
> `|𝒢(βΦ)| = 1` when `β < β_c` and `|𝒢(βΦ)| > 1` when `β > β_c`."

This file supplies the inequality of Griffiths.  Everything here is *finite volume*: a
configuration is a function `σ : V → Bool` on a finite set `V` of sites, `Bool` being read as
`{-1, +1}` through `spin`, and all sums are finite sums, so no measure theory is involved.

## The general ferromagnet

Following Griffiths, we work with the general ferromagnetic Hamiltonian

`H(σ) = - ∑_{c} J_c σ_{C c}`,   `σ_A = ∏_{i ∈ A} σ_i`,   `J_c ≥ 0`,

where `c` ranges over a finite index type `ι` and `C c` is a finite set of sites.  This covers
the Ising model with an arbitrary ferromagnetic pair interaction `J_{ij} ≥ 0` **and** an
arbitrary nonnegative external field `h_i ≥ 0`; in particular it covers the finite-volume
Ising Gibbs distribution in `Λ` with the `+` boundary condition, for which `h_i` is the sum of
the couplings from `i` to its neighbours outside `Λ` (see `plusField`).

## Main results

* `sum_spinPow_nonneg` — the combinatorial core: `∑_σ σ^m ≥ 0` for every multi-index `m`
  (it is `2^{|V|}` if all exponents are even and `0` otherwise).
* `unnorm_nonneg`, `corr_nonneg` — **GKS-I** (Griffiths' first inequality): `⟨σ_A⟩ ≥ 0`.
* `unnorm_mul_unnorm_le`, `corr_mul_corr_le` — **GKS-II** (Griffiths' second inequality):
  `⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩ ⟨σ_B⟩`.
* `corr_mono` — monotonicity of every correlation in every coupling constant.
* `corr_mono_beta`, `monotoneOn_corr_beta` — **monotonicity in the inverse temperature**:
  `β ↦ ⟨σ_A⟩_{βJ}` is nondecreasing on `[0, ∞)`.
* `magnetisation_nonneg`, `monotoneOn_magnetisation` — the specialisation to the Ising
  magnetisation `β ↦ ⟨σ_i⟩` : nonnegative and nondecreasing in `β`.

## Proof outline

Since `σ_A ∈ {-1, 1}`, `exp(K σ_A) = cosh K + sinh K · σ_A`, so the Boltzmann weight expands
as a *finite* sum over subsets `t` of the index set,

`exp(∑_c J_c σ_{C c}) = ∑_t (∏_{c ∈ t} cosh J_c) (∏_{c ∉ t} sinh J_c) · σ^{m_t}`,

with nonnegative coefficients when `J ≥ 0`.  GKS-I then reduces to `∑_σ σ^m ≥ 0`.

GKS-II is the duplicate-variable trick: with `σ' = σ τ` (a bijection of pairs), the doubled
weight is `exp(∑_c J_c (1 + τ_{C c}) σ_{C c})`, which is again ferromagnetic in `σ` for each
fixed `τ` because `1 + τ_{C c} ≥ 0`; GKS-I applied to it, times the nonnegative factor
`1 - τ_B`, gives the inequality.

Monotonicity in the couplings is deduced from GKS-II by expanding the extra Boltzmann factor
`exp(∑_c K_c σ_{C c})` (`K = J' - J ≥ 0`) in the same way — no differentiation is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

noncomputable section

namespace MeasureTheory.GibbsMeasure.GKS

/-! ### Spin monomials -/

section Monomials

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin monomial `σ_A = ∏_{i ∈ A} σ_i`. -/
def spinMonomial (A : Finset V) (σ : V → Bool) : ℝ := ∏ i ∈ A, spin (σ i)

/-- The spin monomial attached to a multi-index: `σ^m = ∏_i σ_i^{m i}`. -/
def spinPow (m : V → ℕ) (σ : V → Bool) : ℝ := ∏ i, spin (σ i) ^ m i

/-- The multi-index of a finite set of sites. -/
def indicatorIdx (A : Finset V) : V → ℕ := fun i ↦ if i ∈ A then 1 else 0

lemma spin_eq_one_or_neg_one (b : Bool) : spin b = 1 ∨ spin b = -1 := by
  cases b <;> simp [spin]

lemma spin_beq (b c : Bool) : spin (b == c) = spin b * spin c := by
  cases b <;> cases c <;> simp [spin]

omit [DecidableEq V] in
lemma spinPow_zero (σ : V → Bool) : spinPow (0 : V → ℕ) σ = 1 := by simp [spinPow]

omit [DecidableEq V] in
lemma spinPow_add (m n : V → ℕ) (σ : V → Bool) :
    spinPow (m + n) σ = spinPow m σ * spinPow n σ := by
  simp only [spinPow, Pi.add_apply, pow_add]
  exact Finset.prod_mul_distrib

omit [DecidableEq V] in
lemma spinPow_eq_one_or_neg_one (m : V → ℕ) (σ : V → Bool) :
    spinPow m σ = 1 ∨ spinPow m σ = -1 := by
  refine Finset.prod_induction _ (fun x : ℝ ↦ x = 1 ∨ x = -1) ?_ (Or.inl rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · intro i _
    rcases spin_eq_one_or_neg_one (σ i) with h | h
    · rw [h, one_pow]; exact Or.inl rfl
    · rw [h]
      rcases Nat.even_or_odd (m i) with he | ho
      · exact Or.inl he.neg_one_pow
      · exact Or.inr ho.neg_one_pow

omit [DecidableEq V] in
lemma spinPow_le_one (m : V → ℕ) (σ : V → Bool) : spinPow m σ ≤ 1 := by
  rcases spinPow_eq_one_or_neg_one m σ with h | h
  · rw [h]
  · rw [h]; norm_num

omit [DecidableEq V] in
lemma neg_one_le_spinPow (m : V → ℕ) (σ : V → Bool) : -1 ≤ spinPow m σ := by
  rcases spinPow_eq_one_or_neg_one m σ with h | h
  · rw [h]; norm_num
  · rw [h]

lemma spinMonomial_eq_spinPow (A : Finset V) (σ : V → Bool) :
    spinMonomial A σ = spinPow (indicatorIdx A) σ := by
  have h : ∀ i : V, spin (σ i) ^ indicatorIdx A i = if i ∈ A then spin (σ i) else 1 := by
    intro i
    simp only [indicatorIdx]
    split_ifs <;> simp
  simp only [spinPow, h, spinMonomial]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

omit [Fintype V] [DecidableEq V] in
lemma spinMonomial_eq_one_or_neg_one (A : Finset V) (σ : V → Bool) :
    spinMonomial A σ = 1 ∨ spinMonomial A σ = -1 := by
  refine Finset.prod_induction _ (fun x : ℝ ↦ x = 1 ∨ x = -1) ?_ (Or.inl rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · intro i _
    exact spin_eq_one_or_neg_one (σ i)

omit [Fintype V] [DecidableEq V] in
lemma neg_one_le_spinMonomial (A : Finset V) (σ : V → Bool) : -1 ≤ spinMonomial A σ := by
  rcases spinMonomial_eq_one_or_neg_one A σ with h | h
  · rw [h]; norm_num
  · rw [h]

omit [DecidableEq V] in
lemma spinPow_beq (m : V → ℕ) (σ τ : V → Bool) :
    spinPow m (fun i ↦ (σ i == τ i)) = spinPow m σ * spinPow m τ := by
  simp only [spinPow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [spin_beq, mul_pow]

omit [Fintype V] [DecidableEq V] in
lemma spinMonomial_beq (A : Finset V) (σ τ : V → Bool) :
    spinMonomial A (fun i ↦ (σ i == τ i)) = spinMonomial A σ * spinMonomial A τ := by
  simp only [spinMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ spin_beq _ _

/-- **The combinatorial core of GKS.** Summing a spin monomial over all configurations gives
`∏_i (1 + (-1)^{m i})`, i.e. `2^{|V|}` if every exponent is even and `0` otherwise. -/
lemma sum_spinPow (m : V → ℕ) :
    ∑ σ : V → Bool, spinPow m σ = ∏ i : V, ((1 : ℝ) ^ m i + (-1 : ℝ) ^ m i) := by
  have h := Finset.sum_prod_piFinset (ι := V) (κ := Bool) (R := ℝ) Finset.univ
    (fun i b ↦ spin b ^ m i)
  rw [Fintype.piFinset_univ] at h
  simp only [spinPow]
  rw [h]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Fintype.sum_bool]
  simp [spin]

/-- **The combinatorial core of GKS**, in the form used below: the sum of any spin monomial
over all configurations is nonnegative. -/
lemma sum_spinPow_nonneg (m : V → ℕ) : 0 ≤ ∑ σ : V → Bool, spinPow m σ := by
  rw [sum_spinPow]
  refine Finset.prod_nonneg fun i _ ↦ ?_
  rcases Nat.even_or_odd (m i) with he | ho
  · rw [one_pow, he.neg_one_pow]; norm_num
  · rw [one_pow, ho.neg_one_pow]; norm_num

end Monomials

/-! ### The finite-volume ferromagnet -/

section Ferromagnet

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- The multi-index `∑_{c ∈ u} 1_{C c}` of a family of interaction sets. -/
def multiIdx (C : ι → Finset V) (u : Finset ι) : V → ℕ :=
  fun i ↦ ∑ c ∈ u, indicatorIdx (C c) i

omit [Fintype ι] [DecidableEq ι] in
lemma prod_spinMonomial (C : ι → Finset V) (u : Finset ι) (σ : V → Bool) :
    ∏ c ∈ u, spinMonomial (C c) σ = spinPow (multiIdx C u) σ := by
  simp only [spinMonomial_eq_spinPow, spinPow, multiIdx]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ ↦ Finset.prod_pow_eq_pow_sum _ _ _

/-- `cosh`, spelled out. -/
def ch (K : ℝ) : ℝ := (Real.exp K + Real.exp (-K)) / 2

/-- `sinh`, spelled out. -/
def sh (K : ℝ) : ℝ := (Real.exp K - Real.exp (-K)) / 2

lemma ch_nonneg (K : ℝ) : 0 ≤ ch K := by
  have h1 := (Real.exp_pos K).le
  have h2 := (Real.exp_pos (-K)).le
  simp only [ch]
  linarith

lemma sh_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ sh K := by
  have h : Real.exp (-K) ≤ Real.exp K := Real.exp_le_exp.2 (by linarith)
  simp only [sh]
  linarith

lemma exp_mul_eq_of_eq_one_or_neg_one (K s : ℝ) (hs : s = 1 ∨ s = -1) :
    Real.exp (K * s) = ch K + sh K * s := by
  rcases hs with rfl | rfl
  · rw [mul_one]; simp only [ch, sh]; ring
  · rw [show K * (-1 : ℝ) = -K by ring]; simp only [ch, sh]; ring

/-- The energy `∑_c J_c σ_{C c}` (the *negative* of the Hamiltonian, absorbing `β`). -/
def energy (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) : ℝ :=
  ∑ c, J c * spinMonomial (C c) σ

/-- The (unnormalised) Boltzmann weight `exp(∑_c J_c σ_{C c})`. -/
def weight (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) : ℝ := Real.exp (energy C J σ)

/-- The unnormalised correlation `∑_σ σ^m exp(∑_c J_c σ_{C c})`. -/
def unnorm (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) : ℝ :=
  ∑ σ : V → Bool, spinPow m σ * weight C J σ

/-- The partition function. -/
def partition (C : ι → Finset V) (J : ι → ℝ) : ℝ := ∑ σ : V → Bool, weight C J σ

/-- The finite-volume correlation `⟨σ^m⟩`. -/
def corr (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) : ℝ := unnorm C J m / partition C J

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
lemma energy_def (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) :
    energy C J σ = ∑ c, J c * spinMonomial (C c) σ := rfl

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
lemma weight_def (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) :
    weight C J σ = Real.exp (energy C J σ) := rfl

omit [DecidableEq ι] in
lemma unnorm_def (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) :
    unnorm C J m = ∑ σ : V → Bool, spinPow m σ * weight C J σ := rfl

omit [DecidableEq ι] in
lemma partition_def (C : ι → Finset V) (J : ι → ℝ) :
    partition C J = ∑ σ : V → Bool, weight C J σ := rfl

omit [DecidableEq ι] in
lemma corr_def (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) :
    corr C J m = unnorm C J m / partition C J := rfl

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
lemma weight_pos (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) : 0 < weight C J σ :=
  Real.exp_pos _

omit [DecidableEq ι] in
lemma partition_pos (C : ι → Finset V) (J : ι → ℝ) : 0 < partition C J := by
  rw [partition_def]
  exact Finset.sum_pos (fun σ _ ↦ weight_pos C J σ) Finset.univ_nonempty

omit [DecidableEq ι] in
lemma partition_eq_unnorm_zero (C : ι → Finset V) (J : ι → ℝ) :
    partition C J = unnorm C J 0 := by
  rw [partition_def, unnorm_def]
  exact Finset.sum_congr rfl fun σ _ ↦ by rw [spinPow_zero, one_mul]

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
lemma energy_add (C : ι → Finset V) (J K : ι → ℝ) (σ : V → Bool) :
    energy C (J + K) σ = energy C J σ + energy C K σ := by
  simp only [energy_def, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
lemma weight_add (C : ι → Finset V) (J K : ι → ℝ) (σ : V → Bool) :
    weight C (J + K) σ = weight C J σ * weight C K σ := by
  rw [weight_def, weight_def, weight_def, energy_add, Real.exp_add]

/-! #### The high-temperature (finite) expansion of the Boltzmann weight -/

/-- The coefficient of the subset `t` in the expansion of the Boltzmann weight. -/
def expCoeff (J : ι → ℝ) (t : Finset ι) : ℝ :=
  (∏ c ∈ t, ch (J c)) * ∏ c ∈ Finset.univ \ t, sh (J c)

lemma expCoeff_nonneg {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (t : Finset ι) : 0 ≤ expCoeff J t :=
  mul_nonneg (Finset.prod_nonneg fun _ _ ↦ ch_nonneg _)
    (Finset.prod_nonneg fun c _ ↦ sh_nonneg (hJ c))

/-- Because each `σ_{C c}` is `± 1`, the Boltzmann weight is a *finite* linear combination of
spin monomials, with coefficients `expCoeff J t` that are nonnegative when `J ≥ 0`. -/
lemma weight_eq_sum (C : ι → Finset V) (J : ι → ℝ) (σ : V → Bool) :
    weight C J σ = ∑ t ∈ (Finset.univ : Finset ι).powerset,
      expCoeff J t * spinPow (multiIdx C (Finset.univ \ t)) σ := by
  have h1 : weight C J σ = ∏ c : ι, Real.exp (J c * spinMonomial (C c) σ) := by
    rw [weight_def, energy_def, Real.exp_sum]
  have h2 : ∀ c : ι, Real.exp (J c * spinMonomial (C c) σ)
      = ch (J c) + sh (J c) * spinMonomial (C c) σ := fun c ↦
    exp_mul_eq_of_eq_one_or_neg_one _ _ (spinMonomial_eq_one_or_neg_one (C c) σ)
  rw [h1]
  simp only [h2]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Finset.prod_mul_distrib, prod_spinMonomial, expCoeff]
  ring

/-! #### GKS-I -/

omit [DecidableEq ι] in
/-- **Griffiths' first inequality (GKS-I), unnormalised form.**  For a ferromagnetic
interaction (`J ≥ 0`, which includes a nonnegative external field) and any multi-index `m`,
`∑_σ σ^m exp(∑_c J_c σ_{C c}) ≥ 0`. -/
theorem unnorm_nonneg (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m : V → ℕ) :
    0 ≤ unnorm C J m := by
  classical
  have step : unnorm C J m
      = ∑ σ : V → Bool, ∑ t ∈ (Finset.univ : Finset ι).powerset,
          expCoeff J t * spinPow (m + multiIdx C (Finset.univ \ t)) σ := by
    rw [unnorm_def]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [weight_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [spinPow_add]
    ring
  rw [step, Finset.sum_comm]
  refine Finset.sum_nonneg fun t _ ↦ ?_
  rw [← Finset.mul_sum]
  exact mul_nonneg (expCoeff_nonneg hJ t) (sum_spinPow_nonneg _)

omit [DecidableEq ι] in
/-- **Griffiths' first inequality (GKS-I).**  In a finite-volume ferromagnet with nonnegative
couplings and nonnegative external field, every correlation `⟨σ_A⟩` is nonnegative. -/
theorem corr_nonneg (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m : V → ℕ) :
    0 ≤ corr C J m :=
  div_nonneg (unnorm_nonneg C hJ m) (partition_pos C J).le

omit [DecidableEq ι] in
lemma unnorm_le_partition (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) :
    unnorm C J m ≤ partition C J := by
  rw [unnorm_def, partition_def]
  refine Finset.sum_le_sum fun σ _ ↦ ?_
  nth_rewrite 2 [← one_mul (weight C J σ)]
  exact mul_le_mul_of_nonneg_right (spinPow_le_one m σ) (weight_pos C J σ).le

omit [DecidableEq ι] in
lemma corr_le_one (C : ι → Finset V) (J : ι → ℝ) (m : V → ℕ) : corr C J m ≤ 1 := by
  rw [corr_def, div_le_one (partition_pos C J)]
  exact unnorm_le_partition C J m

/-! #### GKS-II -/

/-- Multiplication by a fixed configuration, as a permutation of configuration space.  This is
the change of variables `σ' ↦ σ σ'` of the duplicate-variable argument. -/
def flipPerm (σ : V → Bool) : (V → Bool) ≃ (V → Bool) where
  toFun τ := fun i ↦ (σ i == τ i)
  invFun τ := fun i ↦ (σ i == τ i)
  left_inv τ := by funext i; cases h : σ i <;> cases h' : τ i <;> simp [h, h']
  right_inv τ := by funext i; cases h : σ i <;> cases h' : τ i <;> simp [h, h']

omit [Fintype V] [DecidableEq V] in
lemma flipPerm_apply (σ τ : V → Bool) : flipPerm σ τ = fun i ↦ (σ i == τ i) := rfl

omit [Fintype V] [DecidableEq V] [DecidableEq ι] in
/-- The doubled Boltzmann weight of the duplicate-variable argument: for fixed `τ`, it is again
a ferromagnetic weight in `σ`, with couplings `J_c (1 + τ_{C c}) ≥ 0`. -/
lemma weight_mul_weight_flipPerm (C : ι → Finset V) (J : ι → ℝ) (σ τ : V → Bool) :
    weight C J σ * weight C J (flipPerm σ τ)
      = weight C (fun c ↦ J c * (1 + spinMonomial (C c) τ)) σ := by
  rw [weight_def, weight_def, weight_def, ← Real.exp_add]
  congr 1
  simp only [energy_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [flipPerm_apply, spinMonomial_beq]
  ring

omit [DecidableEq ι] in
/-- **Griffiths' second inequality (GKS-II), unnormalised form.** -/
theorem unnorm_mul_unnorm_le (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m n : V → ℕ) :
    unnorm C J m * unnorm C J n ≤ unnorm C J (m + n) * partition C J := by
  classical
  set Jt : (V → Bool) → ι → ℝ := fun τ c ↦ J c * (1 + spinMonomial (C c) τ) with hJt
  have hJtnn : ∀ τ : V → Bool, ∀ c, 0 ≤ Jt τ c := by
    intro τ c
    refine mul_nonneg (hJ c) ?_
    have := neg_one_le_spinMonomial (C c) τ
    linarith
  have main : ∀ σ τ : V → Bool,
      spinPow (m + n) σ * weight C J σ * weight C J (flipPerm σ τ)
          - spinPow m σ * weight C J σ
              * (spinPow n (flipPerm σ τ) * weight C J (flipPerm σ τ))
        = spinPow (m + n) σ * weight C (Jt τ) σ * (1 - spinPow n τ) := by
    intro σ τ
    have hw : weight C J σ * weight C J (flipPerm σ τ) = weight C (Jt τ) σ :=
      weight_mul_weight_flipPerm C J σ τ
    have hs : spinPow n (flipPerm σ τ) = spinPow n σ * spinPow n τ := by
      rw [flipPerm_apply, spinPow_beq]
    have hmn : spinPow (m + n) σ = spinPow m σ * spinPow n σ := spinPow_add m n σ
    rw [hs, hmn]
    have : spinPow m σ * spinPow n σ * weight C J σ * weight C J (flipPerm σ τ)
        - spinPow m σ * weight C J σ
            * (spinPow n σ * spinPow n τ * weight C J (flipPerm σ τ))
        = (spinPow m σ * spinPow n σ) * (weight C J σ * weight C J (flipPerm σ τ))
            * (1 - spinPow n τ) := by ring
    rw [this, hw]
  have expandMul : ∀ f g : (V → Bool) → ℝ,
      (∑ σ : V → Bool, f σ) * (∑ σ' : V → Bool, g σ')
        = ∑ σ : V → Bool, ∑ σ' : V → Bool, f σ * g σ' := by
    intro f g
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ ↦ by rw [Finset.mul_sum]
  have key : unnorm C J (m + n) * partition C J - unnorm C J m * unnorm C J n
      = ∑ τ : V → Bool, (1 - spinPow n τ) * unnorm C (Jt τ) (m + n) := by
    calc unnorm C J (m + n) * partition C J - unnorm C J m * unnorm C J n
        = ∑ σ : V → Bool, ∑ σ' : V → Bool,
            (spinPow (m + n) σ * weight C J σ * weight C J σ'
              - spinPow m σ * weight C J σ * (spinPow n σ' * weight C J σ')) := by
          rw [unnorm_def, unnorm_def, unnorm_def, partition_def, expandMul, expandMul,
            ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun σ _ ↦ by rw [← Finset.sum_sub_distrib]
      _ = ∑ σ : V → Bool, ∑ τ : V → Bool,
            (spinPow (m + n) σ * weight C J σ * weight C J (flipPerm σ τ)
              - spinPow m σ * weight C J σ
                  * (spinPow n (flipPerm σ τ) * weight C J (flipPerm σ τ))) := by
          refine Finset.sum_congr rfl fun σ _ ↦ ?_
          exact (Equiv.sum_comp (flipPerm σ) _).symm
      _ = ∑ σ : V → Bool, ∑ τ : V → Bool,
            spinPow (m + n) σ * weight C (Jt τ) σ * (1 - spinPow n τ) :=
          Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun τ _ ↦ main σ τ
      _ = ∑ τ : V → Bool, (1 - spinPow n τ) * unnorm C (Jt τ) (m + n) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun τ _ ↦ ?_
          rw [unnorm_def, Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ ↦ by ring
  have hnn : 0 ≤ ∑ τ : V → Bool, (1 - spinPow n τ) * unnorm C (Jt τ) (m + n) := by
    refine Finset.sum_nonneg fun τ _ ↦ ?_
    refine mul_nonneg ?_ (unnorm_nonneg C (hJtnn τ) (m + n))
    have := spinPow_le_one n τ
    linarith
  linarith [key ▸ hnn]

omit [DecidableEq ι] in
/-- **Griffiths' second inequality (GKS-II).**  In a finite-volume ferromagnet with
nonnegative couplings and nonnegative external field, `⟨σ_A σ_B⟩ ≥ ⟨σ_A⟩ ⟨σ_B⟩`. -/
theorem corr_mul_corr_le (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m n : V → ℕ) :
    corr C J m * corr C J n ≤ corr C J (m + n) := by
  have hZ : 0 < partition C J := partition_pos C J
  rw [corr_def, corr_def, corr_def, div_mul_div_comm,
    div_le_div_iff₀ (mul_pos hZ hZ) hZ]
  have h := mul_le_mul_of_nonneg_right (unnorm_mul_unnorm_le C hJ m n) hZ.le
  calc unnorm C J m * unnorm C J n * partition C J
      ≤ unnorm C J (m + n) * partition C J * partition C J := h
    _ = unnorm C J (m + n) * (partition C J * partition C J) := by ring

/-! #### Monotonicity in the couplings, and in the inverse temperature -/

lemma unnorm_add_eq (C : ι → Finset V) (J K : ι → ℝ) (m : V → ℕ) :
    unnorm C (J + K) m
      = ∑ t ∈ (Finset.univ : Finset ι).powerset,
          expCoeff K t * unnorm C J (m + multiIdx C (Finset.univ \ t)) := by
  have step : unnorm C (J + K) m
      = ∑ σ : V → Bool, ∑ t ∈ (Finset.univ : Finset ι).powerset,
          expCoeff K t * (spinPow (m + multiIdx C (Finset.univ \ t)) σ * weight C J σ) := by
    rw [unnorm_def]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [weight_add, weight_eq_sum C K σ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [spinPow_add]
    ring
  rw [step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [unnorm_def, Finset.mul_sum]

lemma partition_add_eq (C : ι → Finset V) (J K : ι → ℝ) :
    partition C (J + K)
      = ∑ t ∈ (Finset.univ : Finset ι).powerset,
          expCoeff K t * unnorm C J (multiIdx C (Finset.univ \ t)) := by
  rw [partition_eq_unnorm_zero, unnorm_add_eq]
  exact Finset.sum_congr rfl fun t _ ↦ by rw [zero_add]

omit [DecidableEq ι] in
/-- **Monotonicity of the correlations in the couplings** (Griffiths (1967a)).  If all
couplings are nonnegative and are increased, every correlation increases.  This is the
consequence of GKS-II that Georgii invokes; the usual proof differentiates `⟨σ_A⟩` in `J_c`
and applies GKS-II to the derivative, but the finite expansion of the extra Boltzmann factor
gives it directly. -/
theorem corr_mono (C : ι → Finset V) {J J' : ι → ℝ} (hJ : ∀ c, 0 ≤ J c)
    (hle : ∀ c, J c ≤ J' c) (m : V → ℕ) : corr C J m ≤ corr C J' m := by
  classical
  have hK : ∀ c, 0 ≤ (fun c ↦ J' c - J c) c := fun c ↦ sub_nonneg.2 (hle c)
  have hJK : J' = J + fun c ↦ J' c - J c := by funext c; simp
  have hZ : 0 < partition C J := partition_pos C J
  have hZ' : 0 < partition C J' := partition_pos C J'
  rw [corr_def, corr_def, div_le_div_iff₀ hZ hZ']
  rw [hJK, unnorm_add_eq, partition_add_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  have h2 := unnorm_mul_unnorm_le C hJ m (multiIdx C (Finset.univ \ t))
  have hc := expCoeff_nonneg hK t
  calc unnorm C J m * (expCoeff (fun c ↦ J' c - J c) t
          * unnorm C J (multiIdx C (Finset.univ \ t)))
      = expCoeff (fun c ↦ J' c - J c) t
          * (unnorm C J m * unnorm C J (multiIdx C (Finset.univ \ t))) := by ring
    _ ≤ expCoeff (fun c ↦ J' c - J c) t
          * (unnorm C J (m + multiIdx C (Finset.univ \ t)) * partition C J) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = expCoeff (fun c ↦ J' c - J c) t
          * unnorm C J (m + multiIdx C (Finset.univ \ t)) * partition C J := by ring

omit [DecidableEq ι] in
/-- **Monotonicity of the correlations in the inverse temperature.**  For a ferromagnetic
interaction, `β ↦ ⟨σ_A⟩_{βJ}` is nondecreasing on `[0, ∞)`. -/
theorem corr_mono_beta (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m : V → ℕ)
    {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    corr C (fun c ↦ β₁ * J c) m ≤ corr C (fun c ↦ β₂ * J c) m :=
  corr_mono C (fun c ↦ mul_nonneg h0 (hJ c)) (fun c ↦ mul_le_mul_of_nonneg_right h12 (hJ c)) m

omit [DecidableEq ι] in
/-- **Monotonicity of the correlations in the inverse temperature**, as a `MonotoneOn`. -/
theorem monotoneOn_corr_beta (C : ι → Finset V) {J : ι → ℝ} (hJ : ∀ c, 0 ≤ J c) (m : V → ℕ) :
    MonotoneOn (fun β : ℝ ↦ corr C (fun c ↦ β * J c) m) (Set.Ici 0) :=
  fun _ hb₁ _ _ h12 ↦ corr_mono_beta C hJ m hb₁ h12

end Ferromagnet

/-! ### The Ising ferromagnet in a finite volume -/

section Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The interaction sets of an Ising model: the bond `{i, j}` for each ordered pair `(i, j)`,
and the singleton `{i}` carrying the external field at `i`. -/
def pairSets : V × V ⊕ V → Finset V
  | Sum.inl p => {p.1, p.2}
  | Sum.inr i => {i}

/-- The couplings of an Ising model with pair interaction `K` and external field `h`.
Each unordered bond `{i, j}` occurs twice among the ordered pairs, so `K` should be taken to
be half the physical coupling. -/
def pairCouplings (K : V → V → ℝ) (h : V → ℝ) : V × V ⊕ V → ℝ
  | Sum.inl p => K p.1 p.2
  | Sum.inr i => h i

omit [Fintype V] [DecidableEq V] in
lemma pairCouplings_nonneg {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) : ∀ c, 0 ≤ pairCouplings K h c := by
  rintro (⟨i, j⟩ | i)
  · exact hK i j
  · exact hh i

/-- The energy of the Ising model in the familiar form
`∑_{i,j} K_{ij} σ_i σ_j + ∑_i h_i σ_i`. -/
lemma energy_pairCouplings (K : V → V → ℝ) (hdiag : ∀ i, K i i = 0) (h : V → ℝ)
    (σ : V → Bool) :
    energy pairSets (pairCouplings K h) σ
      = (∑ p : V × V, K p.1 p.2 * (spin (σ p.1) * spin (σ p.2))) + ∑ i, h i * spin (σ i) := by
  rw [energy_def, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun p _ ↦ ?_
    rcases eq_or_ne p.1 p.2 with heq | hne
    · rw [show pairCouplings K h (Sum.inl p) = K p.1 p.2 from rfl, heq, hdiag, zero_mul, zero_mul]
    · rw [show pairCouplings K h (Sum.inl p) = K p.1 p.2 from rfl,
        show pairSets (Sum.inl p) = ({p.1, p.2} : Finset V) from rfl, spinMonomial,
        Finset.prod_pair hne]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [show pairCouplings K h (Sum.inr i) = h i from rfl,
      show pairSets (Sum.inr i : V × V ⊕ V) = ({i} : Finset V) from rfl, spinMonomial,
      Finset.prod_singleton]

/-- The finite-volume Ising correlation at inverse temperature `β`. -/
def isingCorr (K : V → V → ℝ) (h : V → ℝ) (β : ℝ) (m : V → ℕ) : ℝ :=
  corr pairSets (fun c ↦ β * pairCouplings K h c) m

/-- The finite-volume Ising magnetisation at the site `i`: `⟨σ_i⟩`. -/
def magnetisation (K : V → V → ℝ) (h : V → ℝ) (β : ℝ) (i : V) : ℝ :=
  isingCorr K h β (indicatorIdx {i})

/-- **GKS-I for the Ising ferromagnet.**  Every correlation of the finite-volume Ising
ferromagnet with nonnegative couplings and nonnegative external field is nonnegative. -/
theorem isingCorr_nonneg {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) {β : ℝ} (hβ : 0 ≤ β) (m : V → ℕ) : 0 ≤ isingCorr K h β m :=
  corr_nonneg _ (fun c ↦ mul_nonneg hβ (pairCouplings_nonneg hK hh c)) m

/-- **GKS-II for the Ising ferromagnet.** -/
theorem isingCorr_mul_le {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) {β : ℝ} (hβ : 0 ≤ β) (m n : V → ℕ) :
    isingCorr K h β m * isingCorr K h β n ≤ isingCorr K h β (m + n) :=
  corr_mul_corr_le _ (fun c ↦ mul_nonneg hβ (pairCouplings_nonneg hK hh c)) m n

/-- **The magnetisation of the finite-volume Ising ferromagnet is nonnegative** — the first
half of Georgii's "`μ₊^β(σ₀)` is a nonnegative nondecreasing function of `β`". -/
theorem magnetisation_nonneg {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) {β : ℝ} (hβ : 0 ≤ β) (i : V) : 0 ≤ magnetisation K h β i :=
  isingCorr_nonneg hK hh hβ _

theorem magnetisation_le_one (K : V → V → ℝ) (h : V → ℝ) (β : ℝ) (i : V) :
    magnetisation K h β i ≤ 1 :=
  corr_le_one _ _ _

/-- **The magnetisation of the finite-volume Ising ferromagnet is nondecreasing in `β`** —
the second half of Georgii's "`μ₊^β(σ₀)` is a nonnegative nondecreasing function of `β`",
at finite volume.  This is the inequality of Griffiths (1967a) that Georgii cites after
Theorem (6.9). -/
theorem magnetisation_mono {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) (i : V) {β₁ β₂ : ℝ} (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    magnetisation K h β₁ i ≤ magnetisation K h β₂ i :=
  corr_mono_beta _ (pairCouplings_nonneg hK hh) _ h0 h12

/-- **The magnetisation of the finite-volume Ising ferromagnet is nondecreasing in `β`**,
as a `MonotoneOn`. -/
theorem monotoneOn_magnetisation {K : V → V → ℝ} {h : V → ℝ} (hK : ∀ i j, 0 ≤ K i j)
    (hh : ∀ i, 0 ≤ h i) (i : V) :
    MonotoneOn (fun β : ℝ ↦ magnetisation K h β i) (Set.Ici 0) :=
  fun _ hb₁ _ _ h12 ↦ magnetisation_mono hK hh i hb₁ h12

/-! ### The `+` boundary condition in a finite volume -/

section PlusBoundary

variable {S : Type*} [DecidableEq S] (G : SimpleGraph S) [DecidableRel G.Adj]
  [G.LocallyFinite] (Λ : Finset S) (K h₀ : ℝ)

/-- The Ising couplings *inside* a finite volume `Λ` of a graph `G`: the coupling `K` across
each bond of `G` joining two sites of `Λ`.  (Each unordered bond occurs twice among the
ordered pairs, whence `K / 2`.) -/
def restrictedCoupling : {x // x ∈ Λ} → {x // x ∈ Λ} → ℝ :=
  fun i j ↦ if G.Adj i.1 j.1 then K / 2 else 0

/-- The external field produced in `Λ` by the `+` boundary condition: on top of the physical
field `h₀`, the site `i ∈ Λ` is coupled with strength `K` to each of its `G`-neighbours
outside `Λ`, all of which carry the spin `+1`.  Together with `restrictedCoupling` this is
exactly the Hamiltonian of `γ_Λ^{βΦ}(·|ω⁺)` for the Ising potential `Φ` of Georgii (6.8);
see `energy_pairCouplings` for the Hamiltonian in explicit form. -/
def plusField : {x // x ∈ Λ} → ℝ :=
  fun i ↦ h₀ + K * ((((G.neighborFinset i.1).filter fun y ↦ y ∉ Λ)).card : ℝ)

/-- The magnetisation at `i ∈ Λ` of the Ising ferromagnet in the finite volume `Λ` with `+`
boundary condition, at inverse temperature `β`. -/
def plusMagnetisation (β : ℝ) (i : {x // x ∈ Λ}) : ℝ :=
  magnetisation (restrictedCoupling G Λ K) (plusField G Λ K h₀) β i

omit [DecidableEq S] [G.LocallyFinite] in
lemma restrictedCoupling_nonneg (hK : 0 ≤ K) (i j : {x // x ∈ Λ}) :
    0 ≤ restrictedCoupling G Λ K i j := by
  simp only [restrictedCoupling]
  split_ifs with hadj
  · linarith
  · exact le_rfl

omit [DecidableEq S] [G.LocallyFinite] in
lemma restrictedCoupling_diag (i : {x // x ∈ Λ}) : restrictedCoupling G Λ K i i = 0 := by
  simp only [restrictedCoupling, ite_eq_right_iff]
  intro hadj
  exact absurd hadj (SimpleGraph.irrefl G)

omit [DecidableRel G.Adj] in
lemma plusField_nonneg (hK : 0 ≤ K) (hh : 0 ≤ h₀) (i : {x // x ∈ Λ}) :
    0 ≤ plusField G Λ K h₀ i := by
  have h : (0 : ℝ) ≤ K * ((((G.neighborFinset i.1).filter fun y ↦ y ∉ Λ)).card : ℝ) :=
    mul_nonneg hK (Nat.cast_nonneg _)
  simp only [plusField]
  linarith

/-- **GKS-I for the finite-volume `+`-boundary Ising ferromagnet**: the magnetisation is
nonnegative. -/
theorem plusMagnetisation_nonneg (hK : 0 ≤ K) (hh : 0 ≤ h₀) {β : ℝ} (hβ : 0 ≤ β)
    (i : {x // x ∈ Λ}) : 0 ≤ plusMagnetisation G Λ K h₀ β i :=
  magnetisation_nonneg (restrictedCoupling_nonneg G Λ K hK) (plusField_nonneg G Λ K h₀ hK hh)
    hβ i

theorem plusMagnetisation_le_one (β : ℝ) (i : {x // x ∈ Λ}) :
    plusMagnetisation G Λ K h₀ β i ≤ 1 :=
  magnetisation_le_one _ _ _ _

/-- **Griffiths' inequality for the finite-volume `+`-boundary Ising ferromagnet**: the
magnetisation is nondecreasing in the inverse temperature.  This is Georgii's
"`μ₊^β(σ₀)` is a nonnegative nondecreasing function of `β`", at finite volume. -/
theorem plusMagnetisation_mono (hK : 0 ≤ K) (hh : 0 ≤ h₀) (i : {x // x ∈ Λ}) {β₁ β₂ : ℝ}
    (h0 : 0 ≤ β₁) (h12 : β₁ ≤ β₂) :
    plusMagnetisation G Λ K h₀ β₁ i ≤ plusMagnetisation G Λ K h₀ β₂ i :=
  magnetisation_mono (restrictedCoupling_nonneg G Λ K hK) (plusField_nonneg G Λ K h₀ hK hh)
    i h0 h12

/-- **Griffiths' inequality for the finite-volume `+`-boundary Ising ferromagnet**,
as a `MonotoneOn`. -/
theorem monotoneOn_plusMagnetisation (hK : 0 ≤ K) (hh : 0 ≤ h₀) (i : {x // x ∈ Λ}) :
    MonotoneOn (fun β : ℝ ↦ plusMagnetisation G Λ K h₀ β i) (Set.Ici 0) :=
  fun _ hb₁ _ _ h12 ↦ plusMagnetisation_mono G Λ K h₀ hK hh i hb₁ h12

end PlusBoundary

end Ising

end MeasureTheory.GibbsMeasure.GKS

end

end

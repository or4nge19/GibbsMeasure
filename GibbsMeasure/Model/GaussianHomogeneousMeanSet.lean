/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianHomogeneous
public import GibbsMeasure.Mathlib.Algebra.MvPolynomial.Moments
public import GibbsMeasure.Mathlib.Analysis.Complex.MultivariateLaurentRoot

/-!
# Georgii Remark (13.39): the mean set of a homogeneous coupling of finite range

Georgii's Remark (13.39). Let `h ∈ ℝ` and let `J : ℤ^d → ℝ` be even, positive definite and of
finite range. Then `M_{J,h} ≠ ∅`; and if `J(i) ≠ 0` for at least one `i ≠ 0`, then `M_{J,h}` is
uncountable.

Both halves are proved here, with hypotheses weaker than Georgii's: neither half uses positive
definiteness, and the first half uses neither evenness nor positive definiteness.

## Georgii's proof, and the form it takes here

Georgii writes `J̃(p) = Ĵ(z_p)` on `]-1,1]^d`, notes that it is even, analytic and not identically
zero, picks a multi-index `n` of *minimal* total degree with `c(n) = ∂^n J̃(0) ≠ 0`, and checks
that

  `m_i = -c(n)^{-1} h π^{‖n‖} (-1)^{‖n‖/2} i_1^{n_1} ⋯ i_d^{n_d}`

lies in `M_{J,h}`. Up to the constant `π^{‖n‖}(-1)^{‖n‖/2}`, his `c(n)` is the **moment**

  `μ_n = ∑_{ν ∈ ℤ^d} J(ν) ν_1^{n_1} ⋯ ν_d^{n_d}`,

because `J̃(p) = ∑_ν J(ν) cos(π p·ν)`. Stated through the moments, no analysis is needed:

* a finitely supported `J ≠ 0` has a non-vanishing moment, because the point evaluations at
  distinct lattice points are linearly independent on polynomials
  (`MvPolynomial.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`);
* if `n` has minimal total degree among the multi-indices with `μ_n ≠ 0`, then the multinomial
  expansion of `∑_ν J(ν) ∏_ℓ (i_ℓ + ν_ℓ)^{n_ℓ}` keeps only the term `κ = n`, since every other
  `κ ≤ n` has smaller total degree and hence `μ_κ = 0`. So `∑_j J(j-i) m_j` is the **constant**
  `μ_n` times the leading factor, and the scaling `-h/μ_n` puts `m` in `M_{J,h}`.

Georgii's step 2 is the fundamental theorem of algebra: the Laurent polynomial `Ĵ`, read on
`(ℂ ∖ {0})^d`, has a root `z` there, and `m = (Re z^i)_{i ∈ ℤ^d}` is a non-zero element of the
linear space `M_{J,0}`, which is therefore uncountable. That input is
`Complex.exists_forall_ne_zero_sum_mul_prod_zpow_eq_zero`; note that the root is genuinely off the
torus in general (for `d = 1`, `J(0) = 1`, `J(±1) = 1/4` one gets `z = -2 ± √3`), so this is not
the root-on-`G` statement `Potential.re_mFourier_mem_gaussianMeanSubmodule` already in
`GibbsMeasure/Model/GaussianHomogeneous.lean`, and the element of `M_{J,0}` produced here is
unbounded.

## Main results

* `Potential.exists_couplingMoment_ne_zero`: a finitely supported `J ≠ 0` has a non-vanishing
  moment.
* `Potential.tsum_homogeneousCoupling_mul_monomial`: for a multi-index `n` all of whose proper
  lower multi-indices have vanishing moment, `∑_j J(j-i) ∏_ℓ j_ℓ^{n_ℓ} = μ_n`, a constant.
* `Potential.nonempty_gaussianMeanSet_homogeneousCoupling`: **Remark (13.39), part 1** —
  `M_{J,h} ≠ ∅` for a finite-range `J ≠ 0` and a constant `h`.
* `Potential.laurentCharacter_mem_gaussianMeanSubmodule`: a root `z ∈ (ℂ ∖ {0})^d` of the
  Laurent-extended `Ĵ` gives the element `(Re z^i)_i` of `M_{J,0}`.
* `Potential.not_countable_gaussianMeanSet_of_ne_zero`: **Remark (13.39), part 2** — `M_{J,h}` is
  uncountable when `J` has finite range, is even and `J(i) ≠ 0` for some `i ≠ 0`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory Set

noncomputable section

namespace Potential

variable {d : Type*} [Fintype d] {J' : (d → ℤ) → ℝ}

/-! ### Georgii's `c(n)`: the moments of a finitely supported coupling -/

/-- **The moments of a finitely supported coupling**, `μ_n = ∑_ν J(ν) ν_1^{n_1} ⋯ ν_d^{n_d}`.
Up to the factor `π^{‖n‖} (-1)^{‖n‖/2}` this is Georgii's `c(n) = ∂^n J̃(0)` in the proof of
Remark (13.39), because `J̃(p) = ∑_ν J(ν) cos(π p·ν)`. -/
def couplingMoment (J' : (d → ℤ) → ℝ) (n : d → ℕ) : ℝ :=
  ∑' ν : d → ℤ, J' ν * ∏ ℓ, (ν ℓ : ℝ) ^ n ℓ

lemma couplingMoment_eq_sum (hFin : {n : d → ℤ | J' n ≠ 0}.Finite) (n : d → ℕ) :
    couplingMoment J' n = ∑ ν ∈ hFin.toFinset, J' ν * ∏ ℓ, (ν ℓ : ℝ) ^ n ℓ := by
  refine tsum_eq_sum fun ν hν ↦ ?_
  have : J' ν = 0 := by
    by_contra hcon
    exact hν (hFin.mem_toFinset.2 hcon)
  simp [this]

/-- **A finitely supported coupling `J ≠ 0` has a non-vanishing moment.** This is the content of
Georgii's "`J̃` is analytic and not identically zero, hence some `c(n) ≠ 0`": the point
evaluations at distinct lattice points are linearly independent on polynomials. -/
theorem exists_couplingMoment_ne_zero (hFin : {n : d → ℤ | J' n ≠ 0}.Finite) (hJ0 : J' ≠ 0) :
    ∃ n : d → ℕ, couplingMoment J' n ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨ν₀, hν₀⟩ := Function.ne_iff.1 hJ0
  refine hν₀ ?_
  refine MvPolynomial.eq_zero_of_forall_sum_mul_prod_pow_eq_zero hFin.toFinset
    (fun ν ℓ ↦ (ν ℓ : ℝ)) (fun ν _ ν' _ hvv ↦ ?_) J' (fun n ↦ ?_)
    (hFin.mem_toFinset.2 hν₀)
  · funext ℓ
    have hl : ((ν ℓ : ℤ) : ℝ) = ((ν' ℓ : ℤ) : ℝ) := congrFun hvv ℓ
    exact_mod_cast hl
  · rw [← couplingMoment_eq_sum hFin n]
    exact hcon n

/-! ### The multinomial computation: `∑_j J(j-i) ∏_ℓ j_ℓ^{n_ℓ}` is constant -/

/-- The multinomial expansion `∏_ℓ (x_ℓ + y_ℓ)^{n_ℓ}`. -/
lemma prod_add_pow_eq_sum_piFinset [DecidableEq d] (n : d → ℕ) (x y : d → ℝ) :
    (∏ ℓ, (x ℓ + y ℓ) ^ n ℓ)
      = ∑ κ ∈ Fintype.piFinset fun ℓ ↦ Finset.range (n ℓ + 1),
          ∏ ℓ, x ℓ ^ κ ℓ * y ℓ ^ (n ℓ - κ ℓ) * ((n ℓ).choose (κ ℓ) : ℝ) := by
  have h1 : ∀ ℓ, (x ℓ + y ℓ) ^ n ℓ
      = ∑ k ∈ Finset.range (n ℓ + 1), x ℓ ^ k * y ℓ ^ (n ℓ - k) * ((n ℓ).choose k : ℝ) :=
    fun ℓ ↦ add_pow _ _ _
  simp_rw [h1]
  exact Finset.prod_univ_sum _ _

/-- **Georgii's computation in the proof of Remark (13.39).** If every multi-index `κ ≤ n` other
than `n` has vanishing moment, then `∑_{j} J(j - i) ∏_ℓ j_ℓ^{n_ℓ} = μ_n` for every `i`: the
convolution of the monomial `j ↦ j^n` with `J` is the constant `μ_n`. -/
theorem tsum_homogeneousCoupling_mul_monomial (hFin : {n : d → ℤ | J' n ≠ 0}.Finite) {n : d → ℕ}
    (hmin : ∀ κ : d → ℕ, (∀ ℓ, κ ℓ ≤ n ℓ) → κ ≠ n → couplingMoment J' κ = 0) (i : d → ℤ) :
    ∑' j : d → ℤ, homogeneousCoupling J' i j * ∏ ℓ, (j ℓ : ℝ) ^ n ℓ = couplingMoment J' n := by
  classical
  set F : Finset (d → ℤ) := hFin.toFinset with hF
  -- Only the translated support contributes.
  have hsupp : ∀ j ∉ F.map (Equiv.addRight i).toEmbedding,
      homogeneousCoupling J' i j * ∏ ℓ, (j ℓ : ℝ) ^ n ℓ = 0 := by
    intro j hj
    have : J' (j - i) = 0 := by
      by_contra hcon
      refine hj (Finset.mem_map_equiv.2 ?_)
      simpa [hF, sub_eq_add_neg] using hFin.mem_toFinset.2 hcon
    simp [homogeneousCoupling, this]
  rw [tsum_eq_sum hsupp, Finset.sum_map]
  -- Expand `(ν + i)^n` multinomially.
  have hstep : ∀ ν : d → ℤ,
      homogeneousCoupling J' i ((Equiv.addRight i).toEmbedding ν)
          * ∏ ℓ, (((Equiv.addRight i).toEmbedding ν : d → ℤ) ℓ : ℝ) ^ n ℓ
        = ∑ κ ∈ Fintype.piFinset fun ℓ ↦ Finset.range (n ℓ + 1),
            (∏ ℓ, (i ℓ : ℝ) ^ (n ℓ - κ ℓ) * ((n ℓ).choose (κ ℓ) : ℝ))
              * (J' ν * ∏ ℓ, (ν ℓ : ℝ) ^ κ ℓ) := by
    intro ν
    have hcoord : ∀ ℓ, (((Equiv.addRight i).toEmbedding ν : d → ℤ) ℓ : ℝ)
        = (ν ℓ : ℝ) + (i ℓ : ℝ) := by
      intro ℓ
      simp [Equiv.addRight]
    simp_rw [hcoord]
    rw [prod_add_pow_eq_sum_piFinset n (fun ℓ ↦ (ν ℓ : ℝ)) (fun ℓ ↦ (i ℓ : ℝ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ ↦ ?_
    have hsplit : ∀ ℓ, (ν ℓ : ℝ) ^ κ ℓ * (i ℓ : ℝ) ^ (n ℓ - κ ℓ) * ((n ℓ).choose (κ ℓ) : ℝ)
        = ((i ℓ : ℝ) ^ (n ℓ - κ ℓ) * ((n ℓ).choose (κ ℓ) : ℝ)) * (ν ℓ : ℝ) ^ κ ℓ := by
      intro ℓ; ring
    simp_rw [hsplit]
    rw [Finset.prod_mul_distrib]
    have hJ : homogeneousCoupling J' i ((Equiv.addRight i).toEmbedding ν) = J' ν := by
      simp [homogeneousCoupling, Equiv.addRight]
    rw [hJ]
    ring
  simp_rw [hstep]
  rw [Finset.sum_comm]
  -- Only `κ = n` survives.
  have hmem : n ∈ Fintype.piFinset fun ℓ ↦ Finset.range (n ℓ + 1) :=
    Fintype.mem_piFinset.2 fun ℓ ↦ Finset.mem_range.2 (Nat.lt_succ_self _)
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
      Finset.prod_const_one, one_mul]
    exact (couplingMoment_eq_sum hFin n).symm
  · intro κ hκ hne
    have hle : ∀ ℓ, κ ℓ ≤ n ℓ := fun ℓ ↦
      Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hκ ℓ))
    rw [← Finset.mul_sum, ← couplingMoment_eq_sum hFin, hmin κ hle hne, mul_zero]
  · intro hcon; exact absurd hmem hcon

/-! ### Georgii Remark (13.39), part 1: `M_{J,h} ≠ ∅` -/

/-- **Georgii Remark (13.39), part 1.** For a homogeneous coupling `J(i,j) = J'(j-i)` of finite
range with `J' ≠ 0` and a constant external field `h`, the mean set `M_{J,h}` is non-empty: it
contains the monomial `m_i = -μ_n^{-1} h i_1^{n_1} ⋯ i_d^{n_d}` for a multi-index `n` of minimal
total degree with non-vanishing moment.

Georgii assumes in addition that `J` is even and positive definite; neither is used. -/
theorem nonempty_gaussianMeanSet_homogeneousCoupling
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite) (hJ0 : J' ≠ 0) (h' : ℝ) :
    (gaussianMeanSet (homogeneousCoupling J') fun _ ↦ h').Nonempty := by
  classical
  -- A multi-index of minimal total degree with non-vanishing moment.
  have hex : ∃ k : ℕ, ∃ n : d → ℕ, (∑ ℓ, n ℓ) = k ∧ couplingMoment J' n ≠ 0 := by
    obtain ⟨n, hn⟩ := exists_couplingMoment_ne_zero hFin hJ0
    exact ⟨∑ ℓ, n ℓ, n, rfl, hn⟩
  obtain ⟨n, hnsum, hn⟩ := Nat.find_spec hex
  have hmin : ∀ κ : d → ℕ, (∀ ℓ, κ ℓ ≤ n ℓ) → κ ≠ n → couplingMoment J' κ = 0 := by
    intro κ hκ hne
    by_contra hcon
    have hlt : (∑ ℓ, κ ℓ) < ∑ ℓ, n ℓ := by
      obtain ⟨ℓ₀, hℓ₀⟩ := Function.ne_iff.1 hne
      exact Finset.sum_lt_sum (fun ℓ _ ↦ hκ ℓ)
        ⟨ℓ₀, Finset.mem_univ ℓ₀, lt_of_le_of_ne (hκ ℓ₀) hℓ₀⟩
    exact Nat.find_min hex (hnsum ▸ hlt) ⟨κ, rfl, hcon⟩
  -- The monomial, scaled.
  refine ⟨fun j ↦ (-h' / couplingMoment J' n) * ∏ ℓ, (j ℓ : ℝ) ^ n ℓ, ?_, fun i ↦ ?_⟩
  · rw [gaussianConvergenceSet_eq_univ_of_finiteRowSupport (homogeneousCoupling J')
      (finite_setOf_homogeneousCoupling_ne_zero hFin)]
    trivial
  · have hsum : ∑' j : d → ℤ, homogeneousCoupling J' i j
          * ((-h' / couplingMoment J' n) * ∏ ℓ, (j ℓ : ℝ) ^ n ℓ)
        = (-h' / couplingMoment J' n) * couplingMoment J' n := by
      rw [← tsum_homogeneousCoupling_mul_monomial hFin hmin i, ← tsum_mul_left]
      exact tsum_congr fun j ↦ by ring
    rw [hsum, div_mul_cancel₀ _ hn]
    ring

/-! ### Georgii Remark (13.39), part 2: a root of `Ĵ` off the torus -/

section Roots

variable {z : d → ℂ}

/-- The character `i ↦ z^i = ∏_ℓ z_ℓ^{i_ℓ}` attached to `z ∈ (ℂ ∖ {0})^d`, the Laurent extension
of Georgii's `z^i` off the torus. -/
def laurentCharacter (z : d → ℂ) (i : d → ℤ) : ℂ := ∏ ℓ, z ℓ ^ i ℓ

@[simp] lemma laurentCharacter_zero (z : d → ℂ) : laurentCharacter z 0 = 1 := by
  simp [laurentCharacter]

lemma laurentCharacter_add (hz : ∀ ℓ, z ℓ ≠ 0) (i j : d → ℤ) :
    laurentCharacter z (i + j) = laurentCharacter z i * laurentCharacter z j := by
  simp only [laurentCharacter, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ℓ _ ↦ zpow_add₀ (hz ℓ) _ _

/-- **Georgii's step 2 in the proof of Remark (13.39).** A root `z ∈ (ℂ ∖ {0})^d` of the
Laurent-extended `Ĵ` produces the element `m = (Re z^i)_{i ∈ ℤ^d}` of `M_{J,0}`, because
`∑_j J(j - i) m_j = Re(z^i Ĵ(z)) = 0`. Unlike the root-on-the-torus case
(`Potential.re_mFourier_mem_gaussianMeanSubmodule`) this `m` need not be bounded. -/
theorem laurentCharacter_mem_gaussianMeanSubmodule (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hz : ∀ ℓ, z ℓ ≠ 0)
    (hroot : ∑ ν ∈ hFin.toFinset, (J' ν : ℂ) * laurentCharacter z ν = 0) :
    (fun i ↦ (laurentCharacter z i).re) ∈ gaussianMeanSubmodule (homogeneousCoupling J') := by
  classical
  rw [mem_gaussianMeanSubmodule_iff]
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [gaussianConvergenceSet_eq_univ_of_finiteRowSupport (homogeneousCoupling J')
      (finite_setOf_homogeneousCoupling_ne_zero hFin)]
    trivial
  set F : Finset (d → ℤ) := hFin.toFinset with hF
  have hsupp : ∀ j ∉ F.map (Equiv.addRight i).toEmbedding,
      homogeneousCoupling J' i j * (laurentCharacter z j).re = 0 := by
    intro j hj
    have : J' (j - i) = 0 := by
      by_contra hcon
      refine hj (Finset.mem_map_equiv.2 ?_)
      simpa [hF, sub_eq_add_neg] using hFin.mem_toFinset.2 hcon
    simp [homogeneousCoupling, this]
  simp only [Pi.zero_apply, zero_add]
  rw [tsum_eq_sum hsupp, Finset.sum_map]
  have hterm : ∀ ν : d → ℤ,
      homogeneousCoupling J' i ((Equiv.addRight i).toEmbedding ν)
          * (laurentCharacter z ((Equiv.addRight i).toEmbedding ν)).re
        = ((J' ν : ℂ) * laurentCharacter z ν * laurentCharacter z i).re := by
    intro ν
    have hJ : homogeneousCoupling J' i ((Equiv.addRight i).toEmbedding ν) = J' ν := by
      simp [homogeneousCoupling, Equiv.addRight]
    have hc : laurentCharacter z ((Equiv.addRight i).toEmbedding ν)
        = laurentCharacter z ν * laurentCharacter z i := by
      have : ((Equiv.addRight i).toEmbedding ν : d → ℤ) = ν + i := rfl
      rw [this, laurentCharacter_add hz]
    rw [hJ, hc, mul_assoc]
    simp
  simp_rw [hterm]
  rw [← Complex.re_sum, ← Finset.sum_mul, hroot, zero_mul, Complex.zero_re]

/-- The element `(Re z^i)_{i}` is non-zero: its value at `i = 0` is `1`. -/
lemma re_laurentCharacter_ne_zero (z : d → ℂ) :
    (fun i ↦ (laurentCharacter z i).re) ≠ (0 : (d → ℤ) → ℝ) := by
  intro hcon
  have hval := congrFun hcon (0 : d → ℤ)
  rw [laurentCharacter_zero z] at hval
  simp at hval

end Roots

/-! ### Georgii Remark (13.39), part 2: `M_{J,h}` is uncountable -/

/-- **Georgii Remark (13.39), part 2.** If `J` has finite range, is even and `J(i) ≠ 0` for at
least one `i ≠ 0`, then `M_{J,0}` contains a non-zero element: the real part of a character
attached to a root of `Ĵ` in `(ℂ ∖ {0})^d`, which exists by the fundamental theorem of algebra
because `Ĵ` has at least the two terms `J(i) z^i` and `J(-i) z^{-i}`. -/
theorem exists_ne_zero_mem_gaussianMeanSubmodule (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hEven : ∀ n, J' (-n) = J' n) {i₀ : d → ℤ} (hi₀ : i₀ ≠ 0) (hJi₀ : J' i₀ ≠ 0) :
    ∃ m ∈ gaussianMeanSubmodule (homogeneousCoupling J'), m ≠ 0 := by
  classical
  set F : Finset (d → ℤ) := hFin.toFinset with hF
  -- `i₀` and `-i₀` are two distinct points of the support.
  have hne : (-i₀) ≠ i₀ := by
    intro hcon
    refine hi₀ ?_
    funext ℓ
    have hℓ := congrFun hcon ℓ
    simp only [Pi.neg_apply] at hℓ
    simp only [Pi.zero_apply]
    omega
  have h1 : i₀ ∈ F := hFin.mem_toFinset.2 hJi₀
  have h2 : (-i₀) ∈ F := hFin.mem_toFinset.2 (show J' (-i₀) ≠ 0 by rw [hEven]; exact hJi₀)
  have hcard : 1 < F.card := Finset.one_lt_card.2 ⟨-i₀, h2, i₀, h1, hne⟩
  obtain ⟨z, hz, hroot⟩ :=
    Complex.exists_forall_ne_zero_sum_mul_prod_zpow_eq_zero F (fun ν ↦ (J' ν : ℂ))
      (fun ν hν ↦ by
        simpa using hFin.mem_toFinset.1 (hF ▸ hν)) hcard
  exact ⟨fun i ↦ (laurentCharacter z i).re,
    laurentCharacter_mem_gaussianMeanSubmodule hFin hz hroot, re_laurentCharacter_ne_zero z⟩

/-- **Georgii Remark (13.39) as he states it.** For a homogeneous coupling of finite range with
`J` even and `J(i) ≠ 0` for at least one `i ≠ 0`, the mean set `M_{J,h}` is uncountable, for
every constant external field `h`. (`M_{J,h} ≠ ∅` is part 1, and `M_{J,h}` is a coset of the
linear space `M_{J,0}`, which contains a non-zero element.) -/
theorem not_countable_gaussianMeanSet_of_ne_zero (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hEven : ∀ n, J' (-n) = J' n) {i₀ : d → ℤ} (hi₀ : i₀ ≠ 0) (hJi₀ : J' i₀ ≠ 0) (h' : ℝ) :
    ¬ (gaussianMeanSet (homogeneousCoupling J') fun _ ↦ h').Countable := by
  obtain ⟨m₀, hm₀⟩ := nonempty_gaussianMeanSet_homogeneousCoupling hFin
    (fun hcon ↦ hJi₀ (by rw [hcon]; rfl)) h'
  obtain ⟨m, hm, hm0⟩ := exists_ne_zero_mem_gaussianMeanSubmodule hFin hEven hi₀ hJi₀
  exact not_countable_gaussianMeanSet _ hm₀ hm hm0

end Potential

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# A multivariate Laurent polynomial with at least two terms has a root in `(ℂ ∖ {0})^d`

A *Laurent polynomial* in `d` complex variables is a finite sum `∑_ν g ν ∏_ℓ z_ℓ^{ν_ℓ}` with
`ν` ranging over a finite subset of `ℤ^d`. If at least two of the coefficients are non-zero, it
has a zero off the coordinate hyperplanes, i.e. in `(ℂ ∖ {0})^d`.

The proof reduces to one variable by a *monomial substitution* `z_ℓ = w^{a_ℓ}`: choosing
`a ∈ ℤ^d` so that `ν ↦ a · ν` is injective on the (finite) support turns the sum into an honest
univariate Laurent polynomial `∑_ν g ν w^{a·ν}` with distinct exponents, hence — after clearing
the smallest exponent — into a polynomial of degree `≥ 1` with non-zero constant term. The
fundamental theorem of algebra provides a root, which is non-zero because the constant term is.
The separating `a` is found among the vectors `(t^0, …, t^{d-1})`: for each pair of distinct
support points, the `t` that fail are the roots of a non-zero integer polynomial, and there are
finitely many of them.

This is the algebraic input to Georgii's Remark (13.39), step 2: a homogeneous coupling of finite
range which is not concentrated at the origin has a root of its (Laurent-extended) Fourier
transform off the coordinate hyperplanes, and the real part of the corresponding character is a
non-zero element of the mean set `M_{J,0}`.

## Main results

* `Int.exists_injOn_sum_mul`: a `ℤ`-linear form separating the points of a finite subset of `ℤ^d`.
* `Complex.exists_forall_ne_zero_sum_mul_prod_zpow_eq_zero`: the statement above.
-/

@[expose] public section

open Finset Polynomial

/-! ### A linear form separating a finite set of lattice points -/

namespace Int

variable {d : Type*} [Fintype d]

/-- **A `ℤ`-linear form separating a finite set of lattice points.** For every finite
`F ⊆ ℤ^d` there is `a ∈ ℤ^d` such that `ν ↦ ∑_ℓ a_ℓ ν_ℓ` is injective on `F`.

Take `a = (t^{e ℓ})_ℓ` for an enumeration `e` of the coordinates. For a fixed pair `ν ≠ ν'` of
points of `F` the values of `t` that fail are the integer roots of the non-zero polynomial
`∑_ℓ (ν_ℓ - ν'_ℓ) X^{e ℓ}`, of which there are finitely many; finitely many pairs leave all but
finitely many `t` admissible. -/
theorem exists_injOn_sum_mul (F : Finset (d → ℤ)) :
    ∃ a : d → ℤ, Set.InjOn (fun ν : d → ℤ ↦ ∑ ℓ, a ℓ * ν ℓ) F := by
  classical
  set e : d ≃ Fin (Fintype.card d) := Fintype.equivFin d with he
  -- The polynomial attached to a difference vector.
  set P : (d → ℤ) → ℤ[X] := fun δ ↦ ∑ ℓ, Polynomial.C (δ ℓ) * Polynomial.X ^ (e ℓ : ℕ) with hP
  have hcoeff : ∀ (δ : d → ℤ) (ℓ₀ : d), (P δ).coeff (e ℓ₀ : ℕ) = δ ℓ₀ := by
    intro δ ℓ₀
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single ℓ₀]
    · simp
    · intro ℓ _ hne
      have hℓ : (e ℓ₀ : ℕ) ≠ (e ℓ : ℕ) := fun hcon ↦ hne (e.injective (Fin.ext hcon)).symm
      simp [Polynomial.coeff_X_pow, hℓ]
    · intro hcon; exact absurd (Finset.mem_univ ℓ₀) hcon
  have hPne : ∀ δ : d → ℤ, δ ≠ 0 → P δ ≠ 0 := by
    intro δ hδ hcon
    obtain ⟨ℓ₀, hℓ₀⟩ := Function.ne_iff.1 hδ
    exact hℓ₀ (by rw [← hcoeff δ ℓ₀, hcon, Polynomial.coeff_zero]; rfl)
  have heval : ∀ (δ : d → ℤ) (t : ℤ),
      Polynomial.eval t (P δ) = ∑ ℓ, δ ℓ * t ^ (e ℓ : ℕ) := by
    intro δ t
    simp [hP, Polynomial.eval_finsetSum]
  -- The bad values of `t`.
  set B : Set ℤ := ⋃ p ∈ ((F ×ˢ F).filter fun p ↦ p.1 ≠ p.2 : Finset ((d → ℤ) × (d → ℤ))),
    {t : ℤ | (P (p.1 - p.2)).IsRoot t} with hB
  have hBfin : B.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp ↦ ?_
    refine Polynomial.finite_setOfPred_isRoot (hPne _ (sub_ne_zero.2 ?_))
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
  obtain ⟨t, ht⟩ := hBfin.infinite_compl.nonempty
  refine ⟨fun ℓ ↦ t ^ (e ℓ : ℕ), fun ν hν ν' hν' hval ↦ ?_⟩
  by_contra hne
  have hmem : ((ν, ν') : (d → ℤ) × (d → ℤ)) ∈
      ((F ×ˢ F).filter fun p ↦ p.1 ≠ p.2 : Finset ((d → ℤ) × (d → ℤ))) :=
    Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨Finset.mem_coe.1 hν, Finset.mem_coe.1 hν'⟩, hne⟩
  have hroot : (P (ν - ν')).IsRoot t := by
    rw [Polynomial.IsRoot.def, heval]
    have hterm : ∀ ℓ : d,
        (ν - ν') ℓ * t ^ (e ℓ : ℕ) = t ^ (e ℓ : ℕ) * ν ℓ - t ^ (e ℓ : ℕ) * ν' ℓ := by
      intro ℓ
      simp only [Pi.sub_apply]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, sub_eq_zero]
    exact hval
  exact ht (Set.mem_biUnion (Finset.mem_coe.2 hmem) hroot)

end Int

/-! ### The root of a multivariate Laurent polynomial -/

namespace Complex

variable {d : Type*} [Fintype d]

omit [Fintype d] in
/-- `∏ i ∈ s, a ^ c i = a ^ ∑ i ∈ s, c i` for a non-zero `a` in a commutative group with zero. -/
theorem prod_zpow_eq_zpow_sum₀ {G₀ : Type*} [CommGroupWithZero G₀] {a : G₀} (ha : a ≠ 0)
    {ι : Type*} (s : Finset ι) (c : ι → ℤ) : ∏ i ∈ s, a ^ c i = a ^ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

/-- **A multivariate Laurent polynomial with at least two terms has a root off the coordinate
hyperplanes.** If `g` is non-zero on a finite set `F ⊆ ℤ^d` with at least two elements, there is
`z ∈ (ℂ ∖ {0})^d` with `∑_{ν ∈ F} g ν ∏_ℓ z_ℓ^{ν_ℓ} = 0`. -/
theorem exists_forall_ne_zero_sum_mul_prod_zpow_eq_zero (F : Finset (d → ℤ))
    (g : (d → ℤ) → ℂ) (hg : ∀ ν ∈ F, g ν ≠ 0) (hcard : 1 < F.card) :
    ∃ z : d → ℂ, (∀ ℓ, z ℓ ≠ 0) ∧ ∑ ν ∈ F, g ν * ∏ ℓ, z ℓ ^ ν ℓ = 0 := by
  classical
  obtain ⟨a, ha⟩ := Int.exists_injOn_sum_mul F
  set φ : (d → ℤ) → ℤ := fun ν ↦ ∑ ℓ, a ℓ * ν ℓ with hφ
  have hFne : F.Nonempty := Finset.card_pos.1 (by omega)
  set k₀ : ℤ := F.inf' hFne φ with hk₀
  set k₁ : ℤ := F.sup' hFne φ with hk₁
  obtain ⟨ν₀, hν₀F, hν₀⟩ := Finset.exists_mem_eq_inf' hFne φ
  obtain ⟨ν₁, hν₁F, hν₁⟩ := Finset.exists_mem_eq_sup' hFne φ
  have hle : ∀ ν ∈ F, k₀ ≤ φ ν := fun ν hν ↦ Finset.inf'_le _ hν
  have hge : ∀ ν ∈ F, φ ν ≤ k₁ := fun ν hν ↦ Finset.le_sup' _ hν
  -- `φ` is injective on `F`, which has at least two elements, so `k₀ < k₁`.
  have hlt : k₀ < k₁ := by
    rcases ((hle ν₀ hν₀F).trans (hge ν₀ hν₀F)).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard
      have hx' : φ x = k₀ := le_antisymm ((hge x hx).trans_eq h.symm) (hle x hx)
      have hy' : φ y = k₀ := le_antisymm ((hge y hy).trans_eq h.symm) (hle y hy)
      exact hxy (ha (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy)
        (show φ x = φ y by rw [hx', hy']))
  -- The univariate polynomial obtained by clearing the smallest exponent.
  set P : ℂ[X] := ∑ ν ∈ F, Polynomial.C (g ν) * Polynomial.X ^ (φ ν - k₀).toNat with hP
  have hcoeff : ∀ ν₂ ∈ F, P.coeff (φ ν₂ - k₀).toNat = g ν₂ := by
    intro ν₂ hν₂
    rw [hP, Polynomial.finsetSum_coeff, Finset.sum_eq_single ν₂]
    · simp
    · intro ν hν hne
      have hexp : (φ ν₂ - k₀).toNat ≠ (φ ν - k₀).toNat := by
        intro hcon
        refine hne (ha (Finset.mem_coe.2 hν) (Finset.mem_coe.2 hν₂) ?_)
        have hA := hle ν₂ hν₂
        have hB := hle ν hν
        have h1 : φ ν₂ - k₀ = φ ν - k₀ := by omega
        exact (sub_left_inj.1 h1).symm
      simp [Polynomial.coeff_X_pow, hexp]
    · intro hcon; exact absurd hν₂ hcon
  have hpos : 0 < (φ ν₁ - k₀).toNat := by
    have h1 : k₀ < φ ν₁ := by rw [← hν₁]; exact hlt
    omega
  have hdeg : 0 < P.degree := by
    refine Polynomial.natDegree_pos_iff_degree_pos.1 (lt_of_lt_of_le hpos ?_)
    exact Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff ν₁ hν₁F]; exact hg ν₁ hν₁F)
  obtain ⟨w, hw⟩ := Complex.exists_root hdeg
  have hw0 : w ≠ 0 := by
    intro hcon
    have hz : (φ ν₀ - k₀).toNat = 0 := by
      have : φ ν₀ = k₀ := by rw [hk₀, ← hν₀]
      simp [this]
    have h0 : P.eval 0 = g ν₀ := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, ← hz]
      exact hcoeff ν₀ hν₀F
    rw [Polynomial.IsRoot.def, hcon, h0] at hw
    exact hg ν₀ hν₀F hw
  refine ⟨fun ℓ ↦ w ^ a ℓ, fun ℓ ↦ zpow_ne_zero _ hw0, ?_⟩
  -- The substitution turns the multivariate sum into `w^{k₀} P(w)`.
  have hmono : ∀ ν : d → ℤ, (∏ ℓ, (w ^ a ℓ) ^ ν ℓ) = w ^ φ ν := by
    intro ν
    simp_rw [← zpow_mul]
    exact prod_zpow_eq_zpow_sum₀ hw0 _ _
  have hval : ∑ ν ∈ F, g ν * ∏ ℓ, (w ^ a ℓ) ^ ν ℓ = w ^ k₀ * P.eval w := by
    rw [hP, Polynomial.eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν hν ↦ ?_
    have hexp : (((φ ν - k₀).toNat : ℕ) : ℤ) = φ ν - k₀ :=
      Int.toNat_of_nonneg (by linarith [hle ν hν])
    calc g ν * ∏ ℓ, (w ^ a ℓ) ^ ν ℓ = g ν * w ^ φ ν := by rw [hmono ν]
      _ = w ^ k₀ * (g ν * w ^ ((φ ν - k₀).toNat : ℕ)) := by
          rw [← zpow_natCast w ((φ ν - k₀).toNat), hexp, ← mul_assoc, mul_comm (w ^ k₀) (g ν),
            mul_assoc, ← zpow_add₀ hw0]
          congr 2
          ring
      _ = w ^ k₀ * Polynomial.eval w
            (Polynomial.C (g ν) * Polynomial.X ^ (φ ν - k₀).toNat) := by simp
  rw [hval, Polynomial.IsRoot.def.1 hw, mul_zero]

end Complex

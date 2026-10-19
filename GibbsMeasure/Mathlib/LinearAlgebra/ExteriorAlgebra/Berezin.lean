/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.LinearCombination

/-!
# The Berezin integral

Let `M` be a free `R`-module with a basis `b : Basis ι R M` indexed by a finite linearly ordered
type, so that `ExteriorAlgebra R M` is the Grassmann algebra on the generators `ι R (b i)`. Its
**Berezin integral** `berezin b : ExteriorAlgebra R M →ₗ[R] R` is the coefficient of the top
monomial `b i₁ ∧ ⋯ ∧ b iₙ` (`i₁ < ⋯ < iₙ`) in Mathlib's basis `Module.Basis.ExteriorAlgebra`
(the graded collection of the `Module.Basis.exteriorPower` bases). Integration is coefficient
extraction; the order on `ι` fixes the sign of the top monomial.

## Main results

* `berezin_eq_zero_of_mem_exteriorPower`: `∫` vanishes on every degree other than `card ι`
  (in particular on odd elements when the rank is even); `eq_zero_of_mem_exteriorPower`:
  `⋀ⁿ M = 0` above the rank.
* `berezin_ιMulti_comp`: the ordered product `v (e 0) ∧ ⋯ ∧ v (e (n-1))` integrates to the
  determinant `b.det v`.
* `berezin_map`: a linear substitution `f` of the generators multiplies `∫` by `det_{b'} (f ∘ b)`;
  `berezin_eq_det_mul` is the change of basis.
* `berezin_map_mul_map`: Berezin–Fubini, `∫ (x y) = ∫ x · ∫ y` for `x`, `y` in the subalgebras of
  two consecutive blocks of generators; `berezin_map_mul_map_eq_star_mul` and
  `berezin_map_mul_map_self_nonneg` are the reflected form `∫ Θ(ξ') ξ = (∫ ξ')⋆ ∫ ξ ≥ 0`.
* `berezin_exp_gaussian`: the Gaussian Berezin integral `∫ exp (-∑ᵢⱼ Dᵢⱼ ψ̄ᵢ ψⱼ) = det D · b.det v`
  for generator pairs `ψᵢ = v (i, 0)`, `ψ̄ᵢ = v (i, 1)`; with `v = b`, `berezin_exp_gaussian_self`
  gives `det D`. The division-free form is `berezin_gaussian_pow_card`
  (`∫ (-ψ̄ D ψ) ^ m = m! · det D · b.det v`).

## Conventions

The pairs are indexed by `κ ×ₗ Fin 2` (lexicographic): the generators are ordered
`ψ₁, ψ̄₁, ψ₂, ψ̄₂, …`, so the top monomial is `∏ᵢ ψᵢ ψ̄ᵢ` and `∫ ∏ᵢ ψᵢ ψ̄ᵢ = 1` for `v = b`
(`berezin_prod_ι_mul_ι`). The pairs are even, so their order is immaterial. The quadratic form is
`ψ̄ D ψ = ∑ᵢⱼ Dᵢⱼ ψ̄ᵢ ψⱼ`. For one mode `exp (-D ψ̄ ψ) = 1 + D ψ ψ̄` integrates to `D`. The
exponential is Mathlib's `IsNilpotent.exp`, the finite exponential series of a nilpotent element
of a `ℚ`-algebra.

## Implementation notes

The Gaussian formula is proved in the commutative centre: the pair products `ψᵢ ψ̄ᵢ` are central
(`ι_mul_ι_mem_center`) and square to zero, so `(∑ᵢ ψᵢ ψ̄ᵢ) ^ m = m! ∏ᵢ ψᵢ ψ̄ᵢ`
(`Finset.sum_pow_card_of_mul_self_eq_zero`). The substitution `ψ ↦ D ψ` is the right action of the
block matrix `diag (Dᵀ, 1)` on the generator family (`Module.Basis.det_sum_smul`).

Searched (pin `d13f23b7`): `Mathlib/LinearAlgebra/ExteriorAlgebra/*`, `ExteriorPower/*`
(`Module.Basis.ExteriorAlgebra`, `Module.Basis.exteriorPower`, `exteriorPower.ιMultiDual`), and
`rg -i "berezin|grassmann|top degree"`: no top-degree coefficient, no Berezin integral (only
`RingTheory.Grassmannian`). Open PRs (`gh search prs --repo leanprover-community/mathlib4`
`Berezin`, `Grassmann algebra`, `ExteriorAlgebra`): none; nearest are #41028 (exterior power of a
product) and #43719 (exterior algebra of the ring itself).

## References

* [M] (2.1), [Q] (2.16)–(2.17), (2.25), (2.34): the QED₃ chamber manuscripts (Berezin
  normalization, Gaussian integral, reflected Berezin integrals).
-/

@[expose] public section

open Module Set.powersetCard

/-! ### Square-zero elements of a commutative ring -/

section SquareZero

variable {Z : Type*} [CommRing Z]

/-- Truncated binomial formula for a square-zero summand. -/
theorem add_pow_succ_of_mul_self_eq_zero {X : Z} (hX : X * X = 0) (Y : Z) (n : ℕ) :
    (X + Y) ^ (n + 1) = Y ^ (n + 1) + (n + 1 : ℕ) * (X * Y ^ n) := by
  induction n with
  | zero => simp [add_comm]
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (↑n + 1) * Y ^ n * hX

/-- For a family of square-zero elements of a commutative ring, the `#s`-th power of their sum
over `s` is `#s !` times their product, and the next power vanishes. -/
theorem Finset.sum_pow_card_of_mul_self_eq_zero {κ : Type*} {x : κ → Z}
    (hx : ∀ i, x i * x i = 0) (s : Finset κ) :
    (∑ i ∈ s, x i) ^ s.card = s.card.factorial * ∏ i ∈ s, x i ∧
      (∑ i ∈ s, x i) ^ (s.card + 1) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · rw [add_pow_succ_of_mul_self_eq_zero (hx a), ih.2, ih.1, Nat.factorial_succ]
      push_cast
      ring
    · rw [add_pow_succ_of_mul_self_eq_zero (hx a), pow_succ, ih.2]
      simp

end SquareZero

/-! ### Enumerations of lexicographic products and sums -/

/-- `finProdFinEquiv` as an order isomorphism onto the lexicographic product: `k ↦ (k / n, k % n)`
is strictly increasing. -/
def finProdFinLexOrderIso (m n : ℕ) : Fin (m * n) ≃o Fin m ×ₗ Fin n where
  toEquiv := finProdFinEquiv.symm.trans toLex
  map_rel_iff' := by
    refine StrictMono.le_iff_le fun a b hab ↦ ?_
    simp only [Equiv.trans_apply, finProdFinEquiv_symm_apply, Prod.Lex.toLex_lt_toLex,
      Fin.lt_def, Fin.coe_divNat, Fin.coe_modNat, Fin.ext_iff]
    have ha := Nat.div_add_mod a n
    have hb := Nat.div_add_mod b n
    rcases (Nat.div_le_div_right (c := n) hab.le).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rw [h] at ha
      omega

/-- `finSumFinEquiv` as an order isomorphism onto the lexicographic sum. -/
def finSumFinLexOrderIso (m n : ℕ) : Fin (m + n) ≃o Fin m ⊕ₗ Fin n where
  toEquiv := finSumFinEquiv.symm.trans toLex
  map_rel_iff' := by
    refine StrictMono.le_iff_le fun a b hab ↦ ?_
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        have : (i : ℕ) < j := by
          rwa [Fin.lt_def, Fin.val_castAdd, Fin.val_castAdd] at hab
        simpa [Sum.Lex.inl_lt_inl_iff] using this
      | right j => simp
    | right i =>
      induction b using Fin.addCases with
      | left j => exact absurd hab (not_lt.2 (Fin.le_def.2 (by simp; omega)))
      | right j => simpa [Sum.Lex.inr_lt_inr_iff] using hab

/-! ### Determinants of transformed families -/

namespace Module.Basis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- The determinant of a family in a basis is multiplicative under the right action of matrices:
`det_b (v · A) = det A · det_b v`. -/
theorem det_sum_smul (b : Basis ι R M) (A : Matrix ι ι R) (v : ι → M) :
    b.det (fun j ↦ ∑ i, A i j • v i) = A.det * b.det v := by
  have : b.toMatrix (fun j ↦ ∑ i, A i j • v i) = b.toMatrix v * A := by
    ext k j
    simp [Basis.toMatrix_apply, Matrix.mul_apply, mul_comm]
  rw [det_apply, det_apply, this, Matrix.det_mul, mul_comm]

end Module.Basis

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Products of two generators -/

/-- A product of two generators has degree two. -/
theorem ι_mul_ι_mem_exteriorPower (x y : M) : ι R x * ι R y ∈ ⋀[R]^2 M := by
  simpa using ιMulti_range R 2 (Set.mem_range_self ![x, y])

/-- A product of two generators is central: even elements of the exterior algebra commute with
everything. -/
theorem ι_mul_ι_mem_center (x y : M) :
    ι R x * ι R y ∈ Subalgebra.center R (ExteriorAlgebra R M) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using ExteriorAlgebra.induction with
  | algebraMap r => exact Algebra.commutes r _
  | ι z =>
    have hx : ι R z * ι R x = -(ι R x * ι R z) := eq_neg_of_add_eq_zero_left (ι_add_mul_swap z x)
    have hy : ι R z * ι R y = -(ι R y * ι R z) := eq_neg_of_add_eq_zero_left (ι_add_mul_swap z y)
    rw [← mul_assoc, hx, neg_mul, mul_assoc, hy, mul_neg, neg_neg, mul_assoc]
  | mul a c ha hc => rw [mul_assoc, hc, ← mul_assoc, ha, mul_assoc]
  | add a c ha hc => rw [add_mul, mul_add, ha, hc]

/-- A product of two generators squares to zero. -/
theorem ι_mul_ι_mul_self (x y : M) : ι R x * ι R y * (ι R x * ι R y) = 0 := by
  have hyx : ι R y * ι R x = -(ι R x * ι R y) := eq_neg_of_add_eq_zero_left (ι_add_mul_swap y x)
  calc ι R x * ι R y * (ι R x * ι R y) = ι R x * (ι R y * ι R x) * ι R y := by
        simp only [mul_assoc]
    _ = 0 := by rw [hyx, mul_neg, neg_mul, ← mul_assoc, ι_sq_zero, zero_mul, zero_mul, neg_zero]

/-! ### Homogeneous components in a basis -/

section Basis

variable {ι : Type*} [LinearOrder ι] (b : Basis ι R M)

/-- A homogeneous element of degree `n` has no coordinate on the basis monomials of other
degrees. -/
theorem basis_repr_eq_zero_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) {s : Finset ι} (hs : s.card ≠ n) : b.ExteriorAlgebra.repr x s = 0 := by
  rw [Basis.ExteriorAlgebra, Basis.repr_reindex_apply, prodEquiv_symm_apply]
  exact (DirectSum.Decomposition.isInternal _).collectedBasis_repr_of_mem_ne _ hs.symm hx

/-- The image of the basis monomial `b_s` under `map f` has degree `#s`. -/
lemma map_basis_mem_exteriorPower {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (s : Finset ι) : map f (b.ExteriorAlgebra s) ∈ ⋀[R]^s.card N := by
  rw [basis_apply_ofCard b rfl, ιMulti_family, map_apply_ιMulti]
  exact ιMulti_range R _ ⟨_, rfl⟩

variable [Fintype ι]

include b in
/-- The exterior powers of a free module of finite rank vanish above the rank. -/
theorem eq_zero_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M)
    (hn : Fintype.card ι < n) : x = 0 :=
  (Basis.ExteriorAlgebra b).ext_elem fun s ↦ by
    rw [map_zero, Finsupp.zero_apply]
    exact basis_repr_eq_zero_of_mem_exteriorPower b hx (s.card_le_univ.trans_lt hn).ne

/-- The top monomial of `b` is the ordered product `b (e 0) ∧ ⋯ ∧ b (e (n - 1))` for the
increasing enumeration `e` of the index type. -/
theorem basis_univ_eq_ιMulti {n : ℕ} (e : Fin n ≃o ι) :
    b.ExteriorAlgebra Finset.univ = ιMulti R n (b ∘ e) := by
  have hcard : (Finset.univ : Finset ι).card = n := by
    simpa using (Fintype.card_congr e.toEquiv).symm
  rw [basis_apply_ofCard b hcard, ιMulti_family]
  congr 2
  have := Finset.orderEmbOfFin_unique' hcard (f := e.toOrderEmbedding) (fun _ ↦ by simp)
  exact funext fun k ↦ (congrArg (· k) this).symm

end Basis

/-! ### The Berezin integral -/

section Integral

variable {ι : Type*} [Fintype ι] [LinearOrder ι] (b : Basis ι R M)

/-- The **Berezin integral** on the exterior (Grassmann) algebra of a free module with an ordered
finite basis `b`: the coefficient of the top monomial `b i₁ ∧ ⋯ ∧ b iₙ`, `i₁ < ⋯ < iₙ`, in the
basis `b.ExteriorAlgebra` of `ExteriorAlgebra R M`. -/
noncomputable def berezin : ExteriorAlgebra R M →ₗ[R] R :=
  b.ExteriorAlgebra.coord Finset.univ

lemma berezin_apply (x : ExteriorAlgebra R M) :
    berezin b x = b.ExteriorAlgebra.repr x Finset.univ :=
  rfl

@[simp]
lemma berezin_basis_univ : berezin b (b.ExteriorAlgebra Finset.univ) = 1 := by
  simp [berezin_apply]

lemma berezin_basis_of_ne {s : Finset ι} (hs : s ≠ Finset.univ) :
    berezin b (b.ExteriorAlgebra s) = 0 := by
  simp [berezin_apply, hs]

/-- The Berezin integral vanishes on every homogeneous component other than the top one. -/
theorem berezin_eq_zero_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^n M) (hn : n ≠ Fintype.card ι) : berezin b x = 0 :=
  basis_repr_eq_zero_of_mem_exteriorPower b hx (by simpa using hn.symm)

/-- **Berezin integral of an ordered product of generators.** Integrating the ordered product
`v (e 0) ∧ ⋯ ∧ v (e (n - 1))` of a family `v : ι → M` against the basis `b` gives the determinant
of `v` in the basis `b`. -/
theorem berezin_ιMulti_comp {n : ℕ} (e : Fin n ≃o ι) (v : ι → M) :
    berezin b (ιMulti R n (v ∘ e)) = b.det v := by
  let F : M [⋀^ι]→ₗ[R] R :=
    (berezin b).compAlternatingMap ((ιMulti R n).domDomCongr e.toEquiv)
  have hF : ∀ w, F w = berezin b (ιMulti R n (w ∘ e)) := fun _ ↦ rfl
  rw [← hF, AlternatingMap.eq_smul_basis_det b F, AlternatingMap.smul_apply, hF,
    ← basis_univ_eq_ιMulti, berezin_basis_univ, one_smul]

/-- **Linear change of generators.** For a linear map `f : M → N` and ordered bases `b`, `b'` of
`M`, `N` indexed by the same ordered type, `∫_{b'} (map f x) = det_{b'} (f ∘ b) · ∫_b x`. -/
theorem berezin_map {N : Type*} [AddCommGroup N] [Module R N] (b' : Basis ι R N)
    (f : M →ₗ[R] N) (x : ExteriorAlgebra R M) :
    berezin b' (map f x) = b'.det (f ∘ b) * berezin b x := by
  have key : berezin b' ∘ₗ (map f).toLinearMap = b'.det (f ∘ b) • berezin b := by
    refine b.ExteriorAlgebra.ext fun s ↦ ?_
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    by_cases hs : s = Finset.univ
    · subst hs
      rw [berezin_basis_univ, mul_one, basis_univ_eq_ιMulti b (monoEquivOfFin ι rfl),
        map_apply_ιMulti, ← Function.comp_assoc, berezin_ιMulti_comp]
    · have hcard : s.card ≠ Fintype.card ι := fun h ↦ hs (Finset.eq_univ_of_card s h)
      rw [berezin_eq_zero_of_mem_exteriorPower b' (map_basis_mem_exteriorPower b f s) hcard,
        berezin_basis_of_ne b hs, mul_zero]
  exact congrArg (· x) key

/-- **Change of basis.** Berezin integrals against two ordered bases differ by the determinant of
the first basis in the second one. -/
theorem berezin_eq_det_mul (b' : Basis ι R M) (x : ExteriorAlgebra R M) :
    berezin b' x = b'.det b * berezin b x := by
  simpa using berezin_map b b' LinearMap.id x

end Integral

/-! ### Factorization over two blocks of generators -/

section Factorization

variable {ι₁ ι₂ M₁ M₂ : Type*} [Fintype ι₁] [LinearOrder ι₁] [Fintype ι₂] [LinearOrder ι₂]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- **Berezin–Fubini factorization.** Let the ordered basis `b` of `M` list the images
`f₁ (b₁ i)` of the generators of `M₁` before the images `f₂ (b₂ j)` of those of `M₂`
(lexicographic sum `ι₁ ⊕ₗ ι₂`). Then the integral of a product `x y` of an `M₁`-element by an
`M₂`-element factors: `∫_b (x y) = ∫_{b₁} x · ∫_{b₂} y`. -/
theorem berezin_map_mul_map (b : Basis (ι₁ ⊕ₗ ι₂) R M) (b₁ : Basis ι₁ R M₁)
    (b₂ : Basis ι₂ R M₂) {f₁ : M₁ →ₗ[R] M} {f₂ : M₂ →ₗ[R] M}
    (h₁ : ∀ i, f₁ (b₁ i) = b (toLex (.inl i))) (h₂ : ∀ j, f₂ (b₂ j) = b (toLex (.inr j)))
    (x : ExteriorAlgebra R M₁) (y : ExteriorAlgebra R M₂) :
    berezin b (map f₁ x * map f₂ y) = berezin b₁ x * berezin b₂ y := by
  let B : ExteriorAlgebra R M₁ →ₗ[R] ExteriorAlgebra R M₂ →ₗ[R] R :=
    ((LinearMap.mul R (ExteriorAlgebra R M)).compl₁₂ (map f₁).toLinearMap
      (map f₂).toLinearMap).compr₂ (berezin b)
  let B' : ExteriorAlgebra R M₁ →ₗ[R] ExteriorAlgebra R M₂ →ₗ[R] R :=
    (LinearMap.mul R R).compl₁₂ (berezin b₁) (berezin b₂)
  have key : B = B' := by
    refine LinearMap.ext_basis b₁.ExteriorAlgebra b₂.ExteriorAlgebra fun s t ↦ ?_
    simp only [B, B', LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
      AlgHom.toLinearMap_apply]
    by_cases hst : s = Finset.univ ∧ t = Finset.univ
    · obtain ⟨rfl, rfl⟩ := hst
      set e₁ := monoEquivOfFin ι₁ rfl
      set e₂ := monoEquivOfFin ι₂ rfl
      rw [berezin_basis_univ, berezin_basis_univ, mul_one, basis_univ_eq_ιMulti b₁ e₁,
        basis_univ_eq_ιMulti b₂ e₂, map_apply_ιMulti, map_apply_ιMulti, ιMulti_mul_ιMulti]
      have : Fin.append (f₁ ∘ b₁ ∘ e₁) (f₂ ∘ b₂ ∘ e₂) =
          b ∘ (finSumFinLexOrderIso _ _).trans (OrderIso.sumLexCongr e₁ e₂) := by
        funext k
        induction k using Fin.addCases <;> simp [finSumFinLexOrderIso, h₁, h₂]
      rw [this, berezin_ιMulti_comp, Basis.det_self]
    · have hdeg : map f₁ (b₁.ExteriorAlgebra s) * map f₂ (b₂.ExteriorAlgebra t) ∈
          ⋀[R]^(s.card + t.card) M :=
        SetLike.mul_mem_graded (map_basis_mem_exteriorPower b₁ f₁ s)
          (map_basis_mem_exteriorPower b₂ f₂ t)
      have h1 := s.card_le_univ
      have h2 := t.card_le_univ
      have hcard : s.card + t.card ≠ Fintype.card (ι₁ ⊕ₗ ι₂) := by
        simp only [Fintype.card_lex, Fintype.card_sum]
        rcases not_and_or.1 hst with h | h
        · have := (Finset.card_lt_iff_ne_univ _).2 h
          omega
        · have := (Finset.card_lt_iff_ne_univ _).2 h
          omega
      rw [berezin_eq_zero_of_mem_exteriorPower b hdeg hcard]
      rcases not_and_or.1 hst with h | h
      · rw [berezin_basis_of_ne b₁ h, zero_mul]
      · rw [berezin_basis_of_ne b₂ h, mul_zero]
  exact LinearMap.congr_fun₂ key x y

variable [StarRing R]

/-- **Reflected Berezin integrals** ([Q] (2.34)). Let `b` list the lower generators (images of
`b₂`) before the upper ones (images of `b₁`), and let `Θ` carry upper elements to lower ones with
`∫_{b₂} Θ ξ = (∫_{b₁} ξ)⋆` ([Q] (2.25)). Then the reflected integral separates:
`∫_b Θ(ξ') ξ = (∫_{b₁} ξ')⋆ · ∫_{b₁} ξ`. -/
theorem berezin_map_mul_map_eq_star_mul (b : Basis (ι₂ ⊕ₗ ι₁) R M) (b₁ : Basis ι₁ R M₁)
    (b₂ : Basis ι₂ R M₂) {f₁ : M₁ →ₗ[R] M} {f₂ : M₂ →ₗ[R] M}
    (h₁ : ∀ i, f₁ (b₁ i) = b (toLex (.inr i))) (h₂ : ∀ j, f₂ (b₂ j) = b (toLex (.inl j)))
    {Θ : ExteriorAlgebra R M₁ → ExteriorAlgebra R M₂}
    (hΘ : ∀ ξ, berezin b₂ (Θ ξ) = star (berezin b₁ ξ)) (ξ' ξ : ExteriorAlgebra R M₁) :
    berezin b (map f₂ (Θ ξ') * map f₁ ξ) = star (berezin b₁ ξ') * berezin b₁ ξ := by
  rw [berezin_map_mul_map b b₂ b₁ h₂ h₁, hΘ]

/-- **Grassmann reflection positivity.** Under the hypotheses of
`berezin_map_mul_map_eq_star_mul`, the reflected form `∫ Θ(ξ) ξ = |∫ ξ|²` is nonnegative. -/
theorem berezin_map_mul_map_self_nonneg [PartialOrder R] [StarOrderedRing R]
    (b : Basis (ι₂ ⊕ₗ ι₁) R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) {f₁ : M₁ →ₗ[R] M}
    {f₂ : M₂ →ₗ[R] M} (h₁ : ∀ i, f₁ (b₁ i) = b (toLex (.inr i)))
    (h₂ : ∀ j, f₂ (b₂ j) = b (toLex (.inl j))) {Θ : ExteriorAlgebra R M₁ → ExteriorAlgebra R M₂}
    (hΘ : ∀ ξ, berezin b₂ (Θ ξ) = star (berezin b₁ ξ)) (ξ : ExteriorAlgebra R M₁) :
    0 ≤ berezin b (map f₂ (Θ ξ) * map f₁ ξ) := by
  rw [berezin_map_mul_map_eq_star_mul b b₁ b₂ h₁ h₂ hΘ]
  exact star_mul_self_nonneg _

end Factorization

/-! ### Generator pairs and the Gaussian integral -/

section Gaussian

variable {κ : Type*} [Fintype κ] [LinearOrder κ]

/-- The commutative product over `κ` of the central pair products `ψᵢ ψ̄ᵢ`, `ψᵢ = v (i, 0)`,
`ψ̄ᵢ = v (i, 1)`, is the ordered product `ψ₁ ψ̄₁ ψ₂ ψ̄₂ ⋯` of the generator family `v` along the
increasing enumeration of `κ ×ₗ Fin 2`. -/
theorem coe_prod_ι_mul_ι {m : ℕ} (e : Fin m ≃o κ) (v : κ ×ₗ Fin 2 → M) :
    ((∏ i, ⟨ι R (v (toLex (i, 0))) * ι R (v (toLex (i, 1))), ι_mul_ι_mem_center _ _⟩ :
        Subalgebra.center R (ExteriorAlgebra R M)) : ExteriorAlgebra R M) =
      ιMulti R (m * 2)
        (v ∘ (finProdFinLexOrderIso m 2).trans (Prod.Lex.prodLexCongr e (OrderIso.refl _))) := by
  set E := (finProdFinLexOrderIso m 2).trans (Prod.Lex.prodLexCongr e (OrderIso.refl (Fin 2)))
  have hE (i : Fin m) (j : Fin 2) (h : (i : ℕ) * 2 + j < m * 2) :
      E ⟨i * 2 + j, h⟩ = toLex (e i, j) := by
    have hij : finProdFinEquiv.symm (⟨i * 2 + j, h⟩ : Fin (m * 2)) = (i, j) := by
      rw [Equiv.symm_apply_eq]
      ext
      simp [finProdFinEquiv, mul_comm, add_comm]
    simp [E, finProdFinLexOrderIso, hij]
  rw [← e.toEquiv.prod_comp, ← List.prod_ofFn, SubmonoidClass.coe_list_prod, List.map_ofFn,
    ιMulti_apply, List.ofFn_mul, List.prod_flatten, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i ↦ ?_)
  simp [List.ofFn_succ, hE]

variable (b : Basis (κ ×ₗ Fin 2) R M)

/-- **Berezin integral of the product of the pairs.** `∫ ∏ᵢ ψᵢ ψ̄ᵢ = det_b v` for the generator
family `ψᵢ = v (i, 0)`, `ψ̄ᵢ = v (i, 1)`; for `v = b` this is the normalization
`∫ ∏ᵢ ψᵢ ψ̄ᵢ = 1` of [Q] (2.16). -/
theorem berezin_prod_ι_mul_ι (v : κ ×ₗ Fin 2 → M) :
    berezin b ((∏ i, ⟨ι R (v (toLex (i, 0))) * ι R (v (toLex (i, 1))), ι_mul_ι_mem_center _ _⟩ :
        Subalgebra.center R (ExteriorAlgebra R M)) : ExteriorAlgebra R M) = b.det v := by
  rw [coe_prod_ι_mul_ι (monoEquivOfFin κ rfl), berezin_ιMulti_comp]

/-- **Pair sum, top power.** For generator pairs `ψᵢ = v (i, 0)`, `ψ̄ᵢ = v (i, 1)` over `m`
modes, `∫ (∑ᵢ ψᵢ ψ̄ᵢ) ^ m = m! · det_b v`. -/
theorem berezin_sum_ι_mul_ι_pow_card (v : κ ×ₗ Fin 2 → M) :
    berezin b ((∑ i, ι R (v (toLex (i, 0))) * ι R (v (toLex (i, 1)))) ^ Fintype.card κ) =
      (Fintype.card κ).factorial * b.det v := by
  set c : κ → Subalgebra.center R (ExteriorAlgebra R M) :=
    fun i ↦ ⟨ι R (v (toLex (i, 0))) * ι R (v (toLex (i, 1))), ι_mul_ι_mem_center _ _⟩
  have hc (i : κ) : c i * c i = 0 := Subtype.ext (ι_mul_ι_mul_self _ _)
  have hsum : (∑ i, ι R (v (toLex (i, 0))) * ι R (v (toLex (i, 1)))) =
      ((∑ i, c i : Subalgebra.center R (ExteriorAlgebra R M)) : ExteriorAlgebra R M) := by
    simp [c]
  rw [hsum, ← SubmonoidClass.coe_pow, ← Finset.card_univ,
    (Finset.sum_pow_card_of_mul_self_eq_zero hc _).1, Finset.card_univ, Subalgebra.coe_mul]
  simp only [SubringClass.coe_natCast, ← nsmul_eq_mul, map_nsmul, c, berezin_prod_ι_mul_ι]

/-- **Gaussian Berezin integral, top power.** With generators `ψᵢ = v (i, 0)`, `ψ̄ᵢ = v (i, 1)`
over `m` modes and `D : Matrix κ κ R`, `∫ (-∑ᵢⱼ Dᵢⱼ ψ̄ᵢ ψⱼ) ^ m = m! · det D · det_b v`. -/
theorem berezin_gaussian_pow_card (v : κ ×ₗ Fin 2 → M) (D : Matrix κ κ R) :
    berezin b ((-∑ i, ∑ j, D i j • (ι R (v (toLex (i, 1))) * ι R (v (toLex (j, 0))))) ^
      Fintype.card κ) = (Fintype.card κ).factorial * (D.det * b.det v) := by
  set B := Matrix.reindex toLex toLex (Matrix.blockDiagonal ![D.transpose, 1])
  set w : κ ×ₗ Fin 2 → M := fun q ↦ ∑ p, B p q • v p
  have hw0 (i : κ) : w (toLex (i, 0)) = ∑ j, D i j • v (toLex (j, 0)) := by
    simp only [w, B]
    rw [← (toLex : κ × Fin 2 ≃ _).sum_comp]
    simp [Fintype.sum_prod_type, Matrix.blockDiagonal_apply']
  have hw1 (i : κ) : w (toLex (i, 1)) = v (toLex (i, 1)) := by
    simp only [w, B]
    rw [← (toLex : κ × Fin 2 ≃ _).sum_comp]
    simp [Fintype.sum_prod_type, Matrix.blockDiagonal_apply', Matrix.one_apply]
  have hS : -∑ i, ∑ j, D i j • (ι R (v (toLex (i, 1))) * ι R (v (toLex (j, 0)))) =
      ∑ i, ι R (w (toLex (i, 0))) * ι R (w (toLex (i, 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib, hw0, hw1, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, smul_mul_assoc, ← smul_neg,
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap (v (toLex (j, 0))) (v (toLex (i, 1))))]
  have hB : B.det = D.det := by
    simp [B, Matrix.det_blockDiagonal, Fin.prod_univ_two]
  rw [hS, berezin_sum_ι_mul_ι_pow_card, Basis.det_sum_smul, hB]

/-- **Gaussian Berezin integral** ([M] (2.1), [Q] (2.16)). With generators `ψᵢ = v (i, 0)`,
`ψ̄ᵢ = v (i, 1)` and `D : Matrix κ κ R`, `∫ exp (-∑ᵢⱼ Dᵢⱼ ψ̄ᵢ ψⱼ) = det D · det_b v`. The
exponential of the nilpotent quadratic form is the finite sum `IsNilpotent.exp`. -/
theorem berezin_exp_gaussian [Module ℚ R] [Module ℚ (ExteriorAlgebra R M)]
    (v : κ ×ₗ Fin 2 → M) (D : Matrix κ κ R) :
    berezin b (IsNilpotent.exp
      (-∑ i, ∑ j, D i j • (ι R (v (toLex (i, 1))) * ι R (v (toLex (j, 0)))))) =
      D.det * b.det v := by
  set S := -∑ i, ∑ j, D i j • (ι R (v (toLex (i, 1))) * ι R (v (toLex (j, 0))))
  have hS : S ∈ ⋀[R]^2 M :=
    neg_mem <| Submodule.sum_mem _ fun i _ ↦ Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (ι_mul_ι_mem_exteriorPower _ _)
  have hcard : Fintype.card (κ ×ₗ Fin 2) = Fintype.card κ * 2 := by simp
  have hnil : S ^ (Fintype.card κ + 1) = 0 :=
    eq_zero_of_mem_exteriorPower b (SetLike.pow_mem_graded _ hS)
      (by rw [hcard, smul_eq_mul]; lia)
  rw [IsNilpotent.exp_eq_sum hnil, map_sum, Finset.sum_eq_single (Fintype.card κ)]
  · rw [map_rat_smul, berezin_gaussian_pow_card, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · intro k _ hk
    rw [map_rat_smul, berezin_eq_zero_of_mem_exteriorPower b (SetLike.pow_mem_graded k hS)
      (by rw [hcard, smul_eq_mul]; lia), smul_zero]
  · simp

/-- **Gaussian Berezin integral in the generator basis** ([M] (2.1)). If `b` is the basis
`ψ₁, ψ̄₁, …, ψₘ, ψ̄ₘ` (`ψᵢ = b (i, 0)`, `ψ̄ᵢ = b (i, 1)`, lexicographic order), so that
`∫ ψ₁ ψ̄₁ ⋯ ψₘ ψ̄ₘ = 1`, then `∫ exp (-∑ᵢⱼ Dᵢⱼ ψ̄ᵢ ψⱼ) = det D`. -/
theorem berezin_exp_gaussian_self [Module ℚ R] [Module ℚ (ExteriorAlgebra R M)]
    (D : Matrix κ κ R) :
    berezin b (IsNilpotent.exp
      (-∑ i, ∑ j, D i j • (ι R (b (toLex (i, 1))) * ι R (b (toLex (j, 0)))))) = D.det := by
  rw [berezin_exp_gaussian, Basis.det_self, mul_one]

end Gaussian

end ExteriorAlgebra

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.PowersetCard

/-!
# Cubical cochains of a lattice

Let `X` be an abelian group with unit steps `e : ι → X`, the directions `ι` finite and linearly
ordered. Its cubical complex has the oriented `k`-cells `x + [0,1]^I`, `x : X`, `I` a `k`-set of
directions ordered increasingly (`CubicalCell X ι k`); a `k`-cochain is a function on them. This
covers `ℤᵈ` (`e = Pi.single · 1`), the cubic torus `(ℤ/N)ᵈ` and every torus `ℤᵈ ⧸ Γ`. Vertices,
links `x → x + e μ` and plaquettes `(x; μ < ν)` are the `0`-, `1`- and `2`-cells
(`vertexEquiv`, `linkEquiv`, `plaquetteEquiv`).

All degrees are handled at once on the *total cochains* `X → Finset ι → R`: at each site the
coordinates of an element of `⋀ Rⁱ` in the basis `e_I`. There `e_j ∧ ·` is `wedge j` and the
contraction with `e_j*` is `contract j`; they satisfy the canonical anticommutation relations
(`wedge_wedge`, `wedge_wedge_self`, `contract_wedge_add_wedge_contract`), and `contract j` is the
transpose of `wedge j` (`sum_wedge_mul`). The coboundary is the Koszul differential of the
commuting forward differences `Δ_[e j]` (Mathlib's `fwdDiff`),
`totalCoboundary e U x = ∑ j, wedge j (Δ_[e j] U x)`,
and `totalCoboundary_totalCoboundary` (`d ∘ d = 0`) is the anticommutation of the `wedge j`
against the commutation of the `Δ_[e j]`. The degree-`k` coboundary `coboundary e k` is its
restriction to `k`-cochains (`extend_coboundary`); in degrees `0` and `1` it is the lattice
gradient and the lattice curl (`coboundary_zero_apply`, `coboundary_one_apply`).

## Main results

* `coboundary_coboundary`: `d ∘ d = 0` on `k`-cochains.
* `coboundary_add_coboundary`: gauge invariance `d (A + d χ) = d A`.
* `coboundary_map`: `d` commutes with every ring homomorphism of the coefficients (integer
  cochains, such as integer fluxes, are real cochains).
-/

@[expose] public section

open Finset

namespace CubicalCochain

variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-! ### Signs -/

/-- Removing `i ∈ J` flips the sign `(-1) ^ #{k ∈ J | k < j}` exactly when `i < j`. -/
theorem neg_one_pow_card_filter_erase {J : Finset ι} {i : ι} (hi : i ∈ J) (j : ι) :
    (-1 : R) ^ #{k ∈ J.erase i | k < j} =
      if i < j then -(-1) ^ #{k ∈ J | k < j} else (-1) ^ #{k ∈ J | k < j} := by
  rw [filter_erase]
  split_ifs with h
  · have hmem : i ∈ ({k ∈ J | k < j} : Finset ι) := mem_filter.2 ⟨hi, h⟩
    rw [← card_erase_add_one hmem, pow_succ]
    ring
  · rw [erase_eq_of_notMem (s := ({k ∈ J | k < j} : Finset ι)) (by simp [h])]

/-- Inserting `i ∉ I` flips the sign `(-1) ^ #{k ∈ I | k < j}` exactly when `i < j`. -/
theorem neg_one_pow_card_filter_insert {I : Finset ι} {i : ι} (hi : i ∉ I) (j : ι) :
    (-1 : R) ^ #{k ∈ insert i I | k < j} =
      if i < j then -(-1) ^ #{k ∈ I | k < j} else (-1) ^ #{k ∈ I | k < j} := by
  have h := neg_one_pow_card_filter_erase (R := R) (mem_insert_self i I) j
  rw [erase_insert hi] at h
  split_ifs at h ⊢ <;> simp [h]

/-! ### Exterior multiplication and contraction in the basis `e_I` -/

/-- Exterior multiplication `e_j ∧ ·` in the coordinates of the basis `e_I`, `I : Finset ι`:
`e_j ∧ e_I = (-1) ^ #{i ∈ I | i < j} e_{insert j I}` for `j ∉ I`, and `0` otherwise. -/
def wedge (j : ι) : (Finset ι → R) →ₗ[R] Finset ι → R where
  toFun f J := if j ∈ J then (-1) ^ #{i ∈ J | i < j} * f (J.erase j) else 0
  map_add' f g := by ext J; by_cases h : j ∈ J <;> simp [h, mul_add]
  map_smul' c f := by ext J; by_cases h : j ∈ J <;> simp [h, mul_left_comm]

/-- Contraction with the dual vector `e_j*` in the coordinates of the basis `e_I`:
`e_j* ⌟ e_J = (-1) ^ #{i ∈ J | i < j} e_{J.erase j}` for `j ∈ J`, and `0` otherwise. -/
def contract (j : ι) : (Finset ι → R) →ₗ[R] Finset ι → R where
  toFun f I := if j ∈ I then 0 else (-1) ^ #{i ∈ I | i < j} * f (insert j I)
  map_add' f g := by ext I; by_cases h : j ∈ I <;> simp [h, mul_add]
  map_smul' c f := by ext I; by_cases h : j ∈ I <;> simp [h, mul_left_comm]

theorem wedge_apply (j : ι) (f : Finset ι → R) (J : Finset ι) :
    wedge j f J = if j ∈ J then (-1) ^ #{i ∈ J | i < j} * f (J.erase j) else 0 :=
  rfl

theorem contract_apply (j : ι) (f : Finset ι → R) (I : Finset ι) :
    contract j f I = if j ∈ I then 0 else (-1) ^ #{i ∈ I | i < j} * f (insert j I) :=
  rfl

@[simp]
theorem wedge_wedge_self (j : ι) (f : Finset ι → R) : wedge j (wedge j f) = 0 := by
  ext J
  simp [wedge_apply]

/-- Exterior multiplications anticommute: `e_i ∧ e_j ∧ · = - e_j ∧ e_i ∧ ·`. -/
theorem wedge_wedge (i j : ι) (f : Finset ι → R) :
    wedge i (wedge j f) = -wedge j (wedge i f) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  ext J
  simp only [wedge_apply, mem_erase, Pi.neg_apply]
  by_cases hi : i ∈ J
  · by_cases hj : j ∈ J
    · rw [ite_eq_left hi, ite_eq_left ⟨hij.symm, hj⟩, ite_eq_left hj, ite_eq_left ⟨hij, hi⟩,
        neg_one_pow_card_filter_erase hi, neg_one_pow_card_filter_erase hj, erase_right_comm]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [ite_eq_left h, ite_eq_right h.not_gt]; ring
      · rw [ite_eq_right h.not_gt, ite_eq_left h]; ring
    · simp [hj]
  · simp [hi]

/-- The canonical anticommutation relation `e_i* ⌟ (e_j ∧ ·) + e_j ∧ (e_i* ⌟ ·) = δᵢⱼ`. -/
theorem contract_wedge_add_wedge_contract (i j : ι) (f : Finset ι → R) :
    contract i (wedge j f) + wedge j (contract i f) = if i = j then f else 0 := by
  ext I
  simp only [contract_apply, wedge_apply, Pi.add_apply, mem_insert, mem_erase]
  rcases eq_or_ne i j with rfl | hij
  · rw [ite_eq_left rfl]
    by_cases hi : i ∈ I
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_right (fun h ↦ h.1 rfl),
        neg_one_pow_card_filter_erase hi, ite_eq_right (lt_irrefl i), insert_erase hi, zero_add,
        ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      simp
    · rw [ite_eq_right hi, ite_eq_left (Or.inl rfl), ite_eq_right hi, erase_insert hi, add_zero,
        ← mul_assoc, neg_one_pow_card_filter_insert hi, ite_eq_right (lt_irrefl i), ← pow_add,
        ← two_mul, pow_mul]
      simp
  · rw [ite_eq_right hij]
    by_cases hi : i ∈ I
    · simp [hi, hij]
    by_cases hj : j ∈ I
    · rw [ite_eq_right hi, ite_eq_left (Or.inr hj), ite_eq_left hj, ite_eq_right (by tauto),
        neg_one_pow_card_filter_insert hi, neg_one_pow_card_filter_erase hj,
        erase_insert_of_ne hij]
      rcases lt_or_gt_of_ne hij with h | h
      · rw [ite_eq_left h, ite_eq_right h.not_gt]; simp; ring
      · rw [ite_eq_right h.not_gt, ite_eq_left h]; simp; ring
    · simp [hi, hj, Ne.symm hij]

/-- `contract j` is the transpose of `wedge j` for the pairing `∑_I f I * g I` in which the basis
`e_I` is orthonormal. -/
theorem sum_wedge_mul [Fintype ι] (j : ι) (f g : Finset ι → R) :
    ∑ J, wedge j f J * g J = ∑ I, f I * contract j g I := by
  let t : Finset ι ≃ Finset ι := Function.Involutive.toPerm
    (fun J ↦ if j ∈ J then J.erase j else insert j J) fun J ↦ by
      by_cases h : j ∈ J
      · simp [h, insert_erase h]
      · simp [h, erase_insert h]
  refine (Fintype.sum_equiv t _ _ fun I ↦ ?_).symm
  have ht : t I = if j ∈ I then I.erase j else insert j I := rfl
  by_cases h : j ∈ I
  · simp [ht, h, wedge_apply, contract_apply]
  · rw [ht, ite_eq_right h, wedge_apply, ite_eq_left (mem_insert_self j I), erase_insert h,
      contract_apply, ite_eq_right h, neg_one_pow_card_filter_insert h, ite_eq_right (lt_irrefl j)]
    ring

/-! ### Total cochains and the coboundary -/

variable {X : Type*} [AddCommGroup X] [Fintype ι]

/-- The coboundary of total cochains `X → Finset ι → R`: the Koszul differential
`d U = ∑ⱼ e_j ∧ Δ_[e j] U` of the commuting forward differences. In the basis,
`d U x J = ∑_{j ∈ J} (-1) ^ #{i ∈ J | i < j} (U (x + e j) (J ∖ j) - U x (J ∖ j))`
(`totalCoboundary_apply`): the signed sum over the faces of the cube `x + [0,1]^J`. -/
def totalCoboundary (e : ι → X) : (X → Finset ι → R) →ₗ[R] X → Finset ι → R where
  toFun U x := ∑ j, wedge j (fwdDiff (e j) U x)
  map_add' U V := by ext x; simp [fwdDiff, sub_add_sub_comm, sum_add_distrib]
  map_smul' c U := by
    ext x : 1
    simp only [fwdDiff, Pi.smul_apply, RingHom.id_apply, ← smul_sub, map_smul, Finset.smul_sum]

theorem totalCoboundary_apply' (e : ι → X) (U : X → Finset ι → R) (x : X) :
    totalCoboundary e U x = ∑ j, wedge j (fwdDiff (e j) U x) :=
  rfl

theorem totalCoboundary_apply (e : ι → X) (U : X → Finset ι → R) (x : X) (J : Finset ι) :
    totalCoboundary e U x J =
      ∑ j ∈ J, (-1) ^ #{i ∈ J | i < j} * (U (x + e j) (J.erase j) - U x (J.erase j)) := by
  rw [totalCoboundary_apply', Finset.sum_apply, ← sum_filter_add_sum_filter_not univ (· ∈ J)]
  simp only [wedge_apply, fwdDiff, Pi.sub_apply]
  rw [sum_eq_zero fun j hj ↦ ite_eq_right (mem_filter.1 hj).2, add_zero, filter_mem_eq_inter,
    univ_inter]
  exact sum_congr rfl fun j hj ↦ ite_eq_left hj

/-- `∑ᵢⱼ e_i ∧ e_j ∧ a i j = 0` for a symmetric family: the pairs `(i, j)` and `(j, i)` cancel
and the diagonal vanishes. -/
theorem sum_wedge_wedge_of_symm {a : ι → ι → Finset ι → R} (ha : ∀ i j, a i j = a j i) :
    ∑ i, ∑ j, wedge i (wedge j (a i j)) = 0 := by
  rw [← Fintype.sum_prod_type']
  refine sum_ninvolution Prod.swap (fun p ↦ ?_) (fun p hp hs ↦ hp ?_) (fun _ ↦ mem_univ _)
    fun _ ↦ rfl
  · rw [Prod.fst_swap, Prod.snd_swap, ha p.2 p.1, wedge_wedge, neg_add_cancel]
  · obtain ⟨i, j⟩ := p
    obtain rfl : i = j := congrArg Prod.fst hs |>.symm
    exact wedge_wedge_self _ _

/-- **`d ∘ d = 0`** on total cochains. -/
@[simp]
theorem totalCoboundary_totalCoboundary (e : ι → X) (U : X → Finset ι → R) :
    totalCoboundary e (totalCoboundary e U) = 0 := by
  ext x : 1
  have h : ∀ i, fwdDiff (e i) (totalCoboundary e U) x =
      ∑ j, wedge j (fwdDiff (e i) (fwdDiff (e j) U) x) := fun i ↦ by
    simp only [fwdDiff, totalCoboundary_apply', ← sum_sub_distrib, ← map_sub]
  simp only [totalCoboundary_apply', h, map_sum, Pi.zero_apply]
  refine sum_wedge_wedge_of_symm fun i j ↦ ?_
  simp only [fwdDiff]
  rw [add_right_comm x (e j) (e i)]
  abel

/-- `d` commutes with a ring homomorphism of the coefficients. -/
theorem totalCoboundary_map {S : Type*} [CommRing S] (f : R →+* S) (e : ι → X)
    (U : X → Finset ι → R) :
    totalCoboundary e (fun x I ↦ f (U x I)) = fun x I ↦ f (totalCoboundary e U x I) := by
  ext x J
  simp [totalCoboundary_apply, map_sum]

/-- The total coboundary of a cochain of degree `k` has degree `k + 1`. -/
theorem totalCoboundary_apply_of_card_ne {e : ι → X} {k : ℕ} {U : X → Finset ι → R}
    (hU : ∀ x I, #I ≠ k → U x I = 0) (x : X) {J : Finset ι} (hJ : #J ≠ k + 1) :
    totalCoboundary e U x J = 0 := by
  rw [totalCoboundary_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  have hne : #(J.erase j) ≠ k := by rw [card_erase_of_mem hj]; have := card_pos.2 ⟨j, hj⟩; omega
  rw [hU _ _ hne, hU _ _ hne, sub_self, mul_zero]

end CubicalCochain

/-! ### Cells and `k`-cochains -/

/-- An oriented `k`-cell of the cubical complex of `X`: the cube `site + [0,1]^dirs`, oriented by
the increasing order of `dirs`. A `k`-cochain is a function `CubicalCell X ι k → R`. -/
@[ext]
structure CubicalCell (X ι : Type*) (k : ℕ) where
  /-- The lowest vertex of the cube. -/
  site : X
  /-- The `k` directions spanned by the cube. -/
  dirs : Set.powersetCard ι k
  deriving DecidableEq

namespace CubicalCell

variable {X ι : Type*} {k : ℕ}

/-- A cell is its lowest vertex and its set of directions. -/
def equivProd : CubicalCell X ι k ≃ X × Set.powersetCard ι k where
  toFun c := (c.site, c.dirs)
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem equivProd_apply (c : CubicalCell X ι k) : equivProd c = (c.site, c.dirs) :=
  rfl

@[simp]
theorem equivProd_symm_apply (p : X × Set.powersetCard ι k) : equivProd.symm p = ⟨p.1, p.2⟩ :=
  rfl

instance [Fintype X] [Fintype ι] : Fintype (CubicalCell X ι k) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Finite X] [Finite ι] : Finite (CubicalCell X ι k) :=
  .of_equiv _ equivProd.symm

/-- `V` sites and `d` directions give `V * (d choose k)` cells of dimension `k`; e.g. `3V` links
and `3V` plaquettes in three dimensions. -/
theorem card_eq_mul_choose [Fintype X] [Fintype ι] :
    Fintype.card (CubicalCell X ι k) = Fintype.card X * (Fintype.card ι).choose k := by
  rw [Fintype.card_eq_nat_card, Nat.card_congr equivProd, Nat.card_prod, Set.powersetCard.card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

instance [Countable X] [Countable ι] : Countable (CubicalCell X ι k) :=
  have : Countable (Set.powersetCard ι k) := Subtype.countable
  .of_equiv _ equivProd.symm

/-- The vertices are the `0`-cells. -/
def vertexEquiv : X ≃ CubicalCell X ι 0 where
  toFun x := ⟨x, Set.powersetCard.ofCard (Finset.card_empty)⟩
  invFun c := c.site
  right_inv c := by
    obtain ⟨x, I, hI⟩ := c
    have : I = ∅ := Finset.card_eq_zero.1 (Set.powersetCard.mem_iff.1 hI)
    subst this
    rfl

@[simp]
theorem vertexEquiv_apply (x : X) :
    vertexEquiv x = (⟨x, Set.powersetCard.ofCard Finset.card_empty⟩ : CubicalCell X ι 0) :=
  rfl

/-- The links `x → x + e μ` are the `1`-cells. -/
noncomputable def linkEquiv : X × ι ≃ CubicalCell X ι 1 :=
  (Equiv.prodCongr (.refl X) Set.powersetCard.ofSingleton).trans equivProd.symm

@[simp]
theorem linkEquiv_apply (x : X) (μ : ι) :
    linkEquiv (x, μ) = ⟨x, Set.powersetCard.ofCard (Finset.card_singleton μ)⟩ :=
  rfl

/-- The plaquettes `(x; μ ν)`, `μ < ν`, are the `2`-cells. -/
def plaquetteEquiv [LinearOrder ι] : X × {p : ι × ι // p.1 < p.2} ≃ CubicalCell X ι 2 where
  toFun p := ⟨p.1, Set.powersetCard.ofCard (Finset.card_pair p.2.2.ne)⟩
  invFun c :=
    have hne : (c.dirs : Finset ι).Nonempty := Finset.card_pos.1 (by simp)
    (c.site, ⟨((c.dirs : Finset ι).min' hne, (c.dirs : Finset ι).max' hne),
      Finset.min'_lt_max'_of_card _ (by simp)⟩)
  left_inv := by
    rintro ⟨x, ⟨μ, ν⟩, h⟩
    simp only [Set.powersetCard.val_ofCard, Prod.mk.injEq, Subtype.mk.injEq, true_and]
    constructor
    · rw [Finset.min'_insert _ _ (Finset.singleton_nonempty ν), Finset.min'_singleton]
      exact min_eq_left h.le
    · rw [Finset.max'_insert _ _ (Finset.singleton_nonempty ν), Finset.max'_singleton]
      exact max_eq_right h.le
  right_inv := by
    rintro ⟨x, I⟩
    have hne : (I : Finset ι).Nonempty := Finset.card_pos.1 (by simp)
    have hlt := Finset.min'_lt_max'_of_card (I : Finset ι) (by simp)
    refine CubicalCell.ext rfl (Subtype.ext ?_)
    change ({(I : Finset ι).min' hne, (I : Finset ι).max' hne} : Finset ι) = I
    refine Finset.eq_of_subset_of_card_le (Finset.insert_subset (Finset.min'_mem _ hne)
      (Finset.singleton_subset_iff.2 (Finset.max'_mem _ hne))) ?_
    rw [Set.powersetCard.card_eq, Finset.card_pair hlt.ne]

@[simp]
theorem plaquetteEquiv_apply [LinearOrder ι] (x : X) {μ ν : ι} (h : μ < ν) :
    plaquetteEquiv (x, ⟨(μ, ν), h⟩) = ⟨x, Set.powersetCard.ofCard (Finset.card_pair h.ne)⟩ :=
  rfl

end CubicalCell

namespace CubicalCochain

open CubicalCell

variable {X ι R : Type*} [CommRing R] {k : ℕ}

/-- A `k`-cochain as a total cochain, zero off degree `k`. -/
def extend (k : ℕ) : (CubicalCell X ι k → R) →ₗ[R] X → Finset ι → R where
  toFun u x I := if h : #I = k then u ⟨x, Set.powersetCard.ofCard h⟩ else 0
  map_add' u v := by ext x I; by_cases h : #I = k <;> simp [h]
  map_smul' c u := by ext x I; by_cases h : #I = k <;> simp [h]

/-- The degree-`k` part of a total cochain. -/
def restrict (k : ℕ) : (X → Finset ι → R) →ₗ[R] CubicalCell X ι k → R where
  toFun U c := U c.site c.dirs
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extend_apply (u : CubicalCell X ι k → R) (x : X) (I : Finset ι) :
    extend k u x I = if h : #I = k then u ⟨x, Set.powersetCard.ofCard h⟩ else 0 :=
  rfl

@[simp]
theorem extend_apply_mk (u : CubicalCell X ι k → R) (x : X) (I : Set.powersetCard ι k) :
    extend k u x I = u ⟨x, I⟩ := by
  simp [extend_apply, Set.powersetCard.card_eq]

theorem extend_apply_of_card_ne (u : CubicalCell X ι k → R) (x : X) {I : Finset ι}
    (h : #I ≠ k) : extend k u x I = 0 :=
  dite_eq_right h

theorem extend_apply_of_card_eq (u : CubicalCell X ι k → R) (x : X) {I : Finset ι}
    (h : #I = k) : extend k u x I = u ⟨x, Set.powersetCard.ofCard h⟩ :=
  dite_eq_left h

@[simp]
theorem restrict_apply (U : X → Finset ι → R) (c : CubicalCell X ι k) :
    restrict k U c = U c.site c.dirs :=
  rfl

@[simp]
theorem restrict_extend (u : CubicalCell X ι k → R) : restrict k (extend k u) = u := by
  ext c
  simp

theorem extend_restrict {U : X → Finset ι → R} (hU : ∀ x I, #I ≠ k → U x I = 0) :
    extend k (restrict k U) = U := by
  ext x I
  by_cases h : #I = k
  · simp [extend_apply, h]
  · rw [extend_apply_of_card_ne _ _ h, hU _ _ h]

theorem extend_injective : Function.Injective (extend k : (CubicalCell X ι k → R) → _) :=
  Function.LeftInverse.injective restrict_extend

variable [AddCommGroup X] [LinearOrder ι] [Fintype ι]

/-- The coboundary `d : C^k → C^{k+1}`:
`d u (x + [0,1]^J) = ∑_{j ∈ J} (-1) ^ #{i ∈ J | i < j} (u (x + e j, J ∖ j) - u (x, J ∖ j))`. -/
def coboundary (e : ι → X) (k : ℕ) :
    (CubicalCell X ι k → R) →ₗ[R] CubicalCell X ι (k + 1) → R :=
  restrict (k + 1) ∘ₗ totalCoboundary e ∘ₗ extend k

variable {e : ι → X}

theorem extend_coboundary (u : CubicalCell X ι k → R) :
    extend (k + 1) (coboundary e k u) = totalCoboundary e (extend k u) :=
  extend_restrict fun x _ hJ ↦
    totalCoboundary_apply_of_card_ne (fun x _ hI ↦ extend_apply_of_card_ne u x hI) x hJ

theorem coboundary_apply (u : CubicalCell X ι k → R) (c : CubicalCell X ι (k + 1)) :
    coboundary e k u c = ∑ j ∈ (c.dirs : Finset ι), (-1) ^ #{i ∈ (c.dirs : Finset ι) | i < j} *
      (extend k u (c.site + e j) ((c.dirs : Finset ι).erase j) -
        extend k u c.site ((c.dirs : Finset ι).erase j)) :=
  totalCoboundary_apply _ _ _ _

/-- **`d ∘ d = 0`.** -/
@[simp]
theorem coboundary_coboundary (u : CubicalCell X ι k → R) :
    coboundary e (k + 1) (coboundary e k u) = 0 := by
  rw [coboundary, LinearMap.comp_apply, LinearMap.comp_apply, extend_coboundary,
    totalCoboundary_totalCoboundary, map_zero]

theorem coboundary_comp_coboundary :
    coboundary e (k + 1) ∘ₗ coboundary e k = (0 : (CubicalCell X ι k → R) →ₗ[R] _) :=
  LinearMap.ext coboundary_coboundary

/-- **Gauge invariance**: `d (A + d χ) = d A`. -/
@[simp]
theorem coboundary_add_coboundary (u : CubicalCell X ι (k + 1) → R)
    (χ : CubicalCell X ι k → R) :
    coboundary e (k + 1) (u + coboundary e k χ) = coboundary e (k + 1) u := by
  rw [map_add, coboundary_coboundary, add_zero]

/-- `d` commutes with a ring homomorphism of the coefficients: an integer cochain and its real
image have the same coboundary. -/
theorem coboundary_map {S : Type*} [CommRing S] (f : R →+* S) (u : CubicalCell X ι k → R) :
    coboundary e k (fun c ↦ f (u c)) = fun c ↦ f (coboundary e k u c) := by
  have h : extend k (fun c ↦ f (u c)) = fun x I ↦ f (extend k u x I) := by
    ext x I
    by_cases h : #I = k <;> simp [extend_apply, h]
  ext c
  rw [coboundary, LinearMap.comp_apply, LinearMap.comp_apply, h, totalCoboundary_map]
  rfl

/-- **Degree `0`**: `d` is the lattice gradient, `(d λ)(x, μ) = λ (x + e μ) - λ x`. -/
theorem coboundary_zero_apply (u : CubicalCell X ι 0 → R) (x : X) (μ : ι) :
    coboundary e 0 u (linkEquiv (x, μ)) = u (vertexEquiv (x + e μ)) - u (vertexEquiv x) := by
  rw [coboundary_apply, linkEquiv_apply, Set.powersetCard.val_ofCard, sum_singleton,
    erase_singleton, filter_singleton, ite_eq_right (lt_irrefl μ), card_empty, pow_zero, one_mul,
    extend_apply_of_card_eq _ _ card_empty, extend_apply_of_card_eq _ _ card_empty]
  rfl

/-- **Degree `1`**: `d` is the lattice curl,
`(dA)(x; μ ν) = A_μ(x) + A_ν(x + e_μ) - A_μ(x + e_ν) - A_ν(x)` for `μ < ν`. -/
theorem coboundary_one_apply (u : CubicalCell X ι 1 → R) (x : X) {μ ν : ι} (h : μ < ν) :
    coboundary e 1 u (plaquetteEquiv (x, ⟨(μ, ν), h⟩)) =
      u (linkEquiv (x, μ)) + u (linkEquiv (x + e μ, ν)) - u (linkEquiv (x + e ν, μ)) -
        u (linkEquiv (x, ν)) := by
  have h1 : ({μ, ν} : Finset ι).erase μ = {ν} := by
    rw [erase_insert (by simpa using h.ne)]
  have h2 : ({μ, ν} : Finset ι).erase ν = {μ} := by
    rw [erase_insert_of_ne h.ne, erase_singleton, insert_empty_eq]
  have c1 : #{i ∈ ({μ, ν} : Finset ι) | i < μ} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    exact ⟨lt_irrefl μ, h.not_gt⟩
  have c2 : #{i ∈ ({μ, ν} : Finset ι) | i < ν} = 1 := by
    rw [card_eq_one]
    exact ⟨μ, by ext i; simp only [mem_filter, mem_insert, mem_singleton]; grind⟩
  rw [plaquetteEquiv_apply, coboundary_apply, Set.powersetCard.val_ofCard, sum_pair h.ne, h1, h2,
    c1, c2,
    extend_apply_of_card_eq _ _ (card_singleton ν), extend_apply_of_card_eq _ _ (card_singleton ν),
    extend_apply_of_card_eq _ _ (card_singleton μ), extend_apply_of_card_eq _ _ (card_singleton μ)]
  simp only [linkEquiv_apply]
  ring

end CubicalCochain

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Basic
public import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.LinearCombination

/-!
# Oriented pullback of cubical cochains by lattice isometries

A map `φ : X → Y` between lattices with steps `e : ι → X`, `e' : ι' → Y` is *cubical* along a
bijection of directions `σ : ι ≃ ι'` and signs `s : ι → ℤˣ` if `φ (x + e i) = φ x + s i • e' (σ i)`
(an additive map plus a translation). It carries the cube `x + [0,1]^I` onto the cube
`φ x - ∑_{i ∈ I, s i = -1} e' (σ i) + [0,1]^{σ I}`, with the orientation sign
`orientation σ s I = ∏_{i ∈ I} s i · (-1)^{#inversions of σ on I}`. The oriented pullback
`totalPullback φ σ s e'` (on total cochains) and `pullback φ σ s e' k` (on `k`-cochains) evaluate
a cochain on the image cell with that sign, `(g* u)(c) = ± u(g c)`.

One definition covers the three cases the lattice theory uses: the signed permutations of `ℤⁱ`
followed by a translation, for `ι = Fin 3` the lattice isometry group `ℤ³ ⋊ O_cub`,
`O_cub = O(3) ∩ GL(3, ℤ)` (`signedPerm`, `signedPerm_single`, `coboundary_pullback_signedPerm`);
and, with `σ = 1`, `s = 1`, the maps sending steps to steps — translations `x ↦ x + v` and the
periodic extension along `ℤᵈ → ℤᵈ ⧸ Γ` (`pullback_refl_one_apply`, `coboundary_comp`). A
bijective cubical map preserves the pairing (`sum_pullback_mul_pullback`).

## Main results

* `totalCoboundary_totalPullback`, `coboundary_pullback`: **`d (g* u) = g* (d u)`**: the
  pullback preserves the signed boundary of every cell.
* `coboundary_comp`: translation and periodic extension commute with `d`.
* `sum_pullback_mul_pullback`: lattice isometries preserve `∑_c u c * v c`.
-/

@[expose] public section

open Finset

namespace CubicalCochain

open CubicalCell

variable {ι ι' R : Type*} [LinearOrder ι] [LinearOrder ι'] [CommRing R]

/-! ### Orientation signs -/

omit [LinearOrder ι] in
theorem neg_one_pow_card_filter_eq_prod (J : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (-1 : R) ^ #{a ∈ J | p a} = ∏ a ∈ J, if p a then -1 else 1 := by
  rw [prod_ite, prod_const_one, mul_one, prod_const]

/-- The orientation sign of the image of an `I`-cube under a cubical map along `σ` and `s`: the
product of the signs `s i`, `i ∈ I`, and of `-1` for each inversion of `σ` on `I`. -/
def orientation (σ : ι ≃ ι') (s : ι → ℤˣ) (I : Finset ι) : R :=
  (∏ i ∈ I, ((s i : ℤ) : R)) * ∏ a ∈ I, ∏ b ∈ I, if a < b ∧ σ b < σ a then -1 else 1

theorem units_cast_mul_self (u : ℤˣ) : ((u : ℤ) : R) * ((u : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem orientation_mul_orientation (σ : ι ≃ ι') (s : ι → ℤˣ) (I : Finset ι) :
    orientation (R := R) σ s I * orientation σ s I = 1 := by
  rw [orientation, mul_mul_mul_comm, ← prod_mul_distrib, ← prod_mul_distrib]
  simp only [units_cast_mul_self, prod_const_one, one_mul, ← prod_mul_distrib]
  exact prod_eq_one fun a _ ↦ prod_eq_one fun b _ ↦ by split_ifs <;> simp

/-- Removing `j` from `I` splits off its sign and its inversions. -/
theorem orientation_eq_mul_erase (σ : ι ≃ ι') (s : ι → ℤˣ) {J : Finset ι} {j : ι} (hj : j ∈ J) :
    orientation (R := R) σ s J = ((s j : ℤ) : R) * orientation σ s (J.erase j) *
      ∏ a ∈ J, ((if j < a ∧ σ a < σ j then -1 else 1) *
        (if a < j ∧ σ j < σ a then -1 else 1)) := by
  have hF : ∀ a ∈ J, (∏ b ∈ J, if a < b ∧ σ b < σ a then (-1 : R) else 1) =
      (if a < j ∧ σ j < σ a then -1 else 1) *
        ∏ b ∈ J.erase j, if a < b ∧ σ b < σ a then -1 else 1 :=
    fun a _ ↦ (mul_prod_erase J _ hj).symm
  have hjj : ∏ a ∈ J.erase j, (if a < j ∧ σ j < σ a then (-1 : R) else 1) =
      ∏ a ∈ J, if a < j ∧ σ j < σ a then -1 else 1 := by
    rw [← mul_prod_erase J _ hj, ite_eq_right (fun h ↦ lt_irrefl j h.1), one_mul]
  rw [orientation, orientation, ← mul_prod_erase J _ hj, ← mul_prod_erase J _ hj,
    prod_congr rfl fun a ha ↦ hF a (mem_of_mem_erase ha), prod_mul_distrib, hjj,
    prod_mul_distrib (s := J)]
  ring

/-- The sign identity behind `d (g* u) = g* (d u)`: moving `e j` to the front of `J` before or
after the cubical map differs by `s j` and the orientations. -/
theorem neg_one_pow_mul_orientation_erase (σ : ι ≃ ι') (s : ι → ℤˣ) {J : Finset ι} {j : ι}
    (hj : j ∈ J) :
    (-1 : R) ^ #{i ∈ J | i < j} * orientation σ s (J.erase j) =
      ((s j : ℤ) : R) * orientation σ s J * (-1) ^ #{i ∈ J.map σ.toEmbedding | i < σ j} := by
  rw [orientation_eq_mul_erase σ s hj, filter_map, card_map,
    neg_one_pow_card_filter_eq_prod, neg_one_pow_card_filter_eq_prod]
  have key : ∀ a, (if a < j then (-1 : R) else 1) =
      ((if j < a ∧ σ a < σ j then -1 else 1) * (if a < j ∧ σ j < σ a then -1 else 1)) *
        (if (σ.toEmbedding a) < σ j then -1 else 1) := fun a ↦ by
    simp only [Equiv.coe_toEmbedding]
    rcases lt_trichotomy a j with h | rfl | h
    · rcases lt_or_gt_of_ne (σ.injective.ne h.ne) with h' | h'
      · simp [h, h', h.not_gt, h'.not_gt]
      · simp [h, h', h.not_gt, h'.not_gt]
    · simp
    · rcases lt_or_gt_of_ne (σ.injective.ne h.ne') with h' | h'
      · simp [h, h', h.not_gt, h'.not_gt]
      · simp [h, h', h.not_gt, h'.not_gt]
  rw [prod_congr rfl fun a _ ↦ key a, prod_mul_distrib]
  simp only [Function.comp_apply]
  linear_combination -(orientation (R := R) σ s (J.erase j) *
    (∏ a ∈ J, ((if j < a ∧ σ a < σ j then (-1 : R) else 1) *
      (if a < j ∧ σ j < σ a then -1 else 1))) *
    ∏ a ∈ J, (if σ.toEmbedding a < σ j then (-1 : R) else 1)) *
    units_cast_mul_self (R := R) (s j)

/-! ### Total cochains -/

variable {X Y : Type*} [AddCommGroup Y]

/-- The oriented pullback of total cochains along a cubical map `φ` with directions `σ` and
signs `s`: `g* U x I = orientation σ s I * U (φ x - ∑_{i ∈ I, s i = -1} e' (σ i)) (σ I)`, the
value on the image of the cube `x + [0,1]^I` with its orientation. -/
def totalPullback (φ : X → Y) (σ : ι ≃ ι') (s : ι → ℤˣ) (e' : ι' → Y) :
    (Y → Finset ι' → R) →ₗ[R] X → Finset ι → R where
  toFun U x I :=
    orientation σ s I * U (φ x - ∑ i ∈ I with s i = -1, e' (σ i)) (I.map σ.toEmbedding)
  map_add' U V := by ext x I; simp [mul_add]
  map_smul' c U := by ext x I; simp [mul_left_comm]

theorem totalPullback_apply (φ : X → Y) (σ : ι ≃ ι') (s : ι → ℤˣ) (e' : ι' → Y)
    (U : Y → Finset ι' → R) (x : X) (I : Finset ι) :
    totalPullback φ σ s e' U x I =
      orientation σ s I * U (φ x - ∑ i ∈ I with s i = -1, e' (σ i)) (I.map σ.toEmbedding) :=
  rfl

theorem sum_filter_eq_neg_one_eq_add_sum_erase (s : ι → ℤˣ) (f : ι → Y) {J : Finset ι}
    {j : ι} (hj : j ∈ J) :
    ∑ i ∈ J with s i = -1, f i = (if s j = -1 then f j else 0) + ∑ i ∈ J.erase j with s i = -1,
      f i := by
  rw [sum_filter, sum_filter, ← add_sum_erase J _ hj]

variable [Fintype ι] [Fintype ι']

/-- **`d (g* U) = g* (d U)`**: a cubical map preserves the signed boundary of each cube. -/
theorem totalCoboundary_totalPullback [AddCommGroup X] {e : ι → X} {e' : ι' → Y} {φ : X → Y}
    {σ : ι ≃ ι'} {s : ι → ℤˣ} (hφ : ∀ x i, φ (x + e i) = φ x + (s i : ℤ) • e' (σ i))
    (U : Y → Finset ι' → R) :
    totalCoboundary e (totalPullback φ σ s e' U) =
      totalPullback φ σ s e' (totalCoboundary e' U) := by
  ext x J
  rw [totalCoboundary_apply, totalPullback_apply, totalCoboundary_apply, sum_map, mul_sum]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [← map_erase]
  simp only [totalPullback_apply]
  rw [sum_filter_eq_neg_one_eq_add_sum_erase s _ hj, hφ]
  have hsign := neg_one_pow_mul_orientation_erase (R := R) σ s hj
  simp only [Equiv.coe_toEmbedding] at hsign ⊢
  set Sh := ∑ i ∈ J.erase j with s i = -1, e' (σ i)
  set K := map σ.toEmbedding (J.erase j)
  rcases Int.units_eq_one_or (s j) with h | h
  · rw [h, ite_eq_right (by decide), zero_add, Units.val_one, one_smul,
      show φ x + e' (σ j) - Sh = φ x - Sh + e' (σ j) by abel]
    rw [h, Units.val_one, Int.cast_one, one_mul] at hsign
    linear_combination (U (φ x - Sh + e' (σ j)) K - U (φ x - Sh) K) * hsign
  · rw [h, ite_eq_left rfl, Units.val_neg, Units.val_one, neg_smul, one_smul,
      show φ x + -e' (σ j) - Sh = φ x - (e' (σ j) + Sh) by abel,
      show φ x - (e' (σ j) + Sh) + e' (σ j) = φ x - Sh by abel]
    rw [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at hsign
    linear_combination (U (φ x - (e' (σ j) + Sh)) K - U (φ x - Sh) K) * hsign

/-! ### `k`-cochains -/

variable {e : ι → X} {e' : ι' → Y} {φ : X → Y} {σ : ι ≃ ι'} {s : ι → ℤˣ} {k : ℕ}

omit [Fintype ι] [Fintype ι'] in
/-- The total pullback of a cochain of degree `k` has degree `k`. -/
theorem totalPullback_apply_of_card_ne {U : Y → Finset ι' → R}
    (hU : ∀ y J, #J ≠ k → U y J = 0) (x : X) {I : Finset ι} (hI : #I ≠ k) :
    totalPullback φ σ s e' U x I = 0 := by
  rw [totalPullback_apply, hU _ _ (by rwa [card_map]), mul_zero]

/-- The oriented pullback of `k`-cochains along a cubical map:
`g* u (x + [0,1]^I) = orientation σ s I * u (φ x - ∑_{i ∈ I, s i = -1} e' (σ i) + [0,1]^{σ I})`
(`pullback_apply`). -/
def pullback (φ : X → Y) (σ : ι ≃ ι') (s : ι → ℤˣ) (e' : ι' → Y) (k : ℕ) :
    (CubicalCell Y ι' k → R) →ₗ[R] CubicalCell X ι k → R :=
  restrict k ∘ₗ totalPullback φ σ s e' ∘ₗ extend k

omit [Fintype ι] [Fintype ι'] in
theorem pullback_apply (u : CubicalCell Y ι' k → R) (c : CubicalCell X ι k) :
    pullback φ σ s e' k u c = orientation σ s c.dirs *
      u ⟨φ c.site - ∑ i ∈ (c.dirs : Finset ι) with s i = -1, e' (σ i),
        Set.powersetCard.map k σ.toEmbedding c.dirs⟩ := by
  simp only [pullback, LinearMap.comp_apply, restrict_apply, totalPullback_apply]
  rw [← Set.powersetCard.val_map, extend_apply_mk]

omit [Fintype ι] [Fintype ι'] in
theorem extend_pullback (u : CubicalCell Y ι' k → R) :
    extend k (pullback φ σ s e' k u) = totalPullback φ σ s e' (extend k u) :=
  extend_restrict fun x _ hI ↦
    totalPullback_apply_of_card_ne (fun y _ hJ ↦ extend_apply_of_card_ne u y hJ) x hI

/-- **`d (g* u) = g* (d u)`** on `k`-cochains. -/
theorem coboundary_pullback [AddCommGroup X] (hφ : ∀ x i, φ (x + e i) = φ x + (s i : ℤ) • e' (σ i))
    (u : CubicalCell Y ι' k → R) :
    coboundary e k (pullback φ σ s e' k u) = pullback φ σ s e' (k + 1) (coboundary e' k u) := by
  apply extend_injective
  rw [extend_coboundary, extend_pullback, totalCoboundary_totalPullback hφ, extend_pullback,
    extend_coboundary]

omit [Fintype ι] [Fintype ι'] in
@[simp]
theorem orientation_refl_one (I : Finset ι) :
    orientation (R := R) (Equiv.refl ι) (fun _ ↦ 1) I = 1 := by
  simp only [orientation, Units.val_one, Int.cast_one, prod_const_one, one_mul,
    Equiv.refl_apply]
  exact prod_eq_one fun a _ ↦ prod_eq_one fun b _ ↦ ite_eq_right fun h ↦ lt_asymm h.1 h.2

omit [Fintype ι] [Fintype ι'] [LinearOrder ι'] in
/-- Along a map sending steps to steps the pullback is composition. -/
theorem pullback_refl_one_apply {e' : ι → Y} (u : CubicalCell Y ι k → R)
    (c : CubicalCell X ι k) :
    pullback φ (Equiv.refl ι) (fun _ ↦ 1) e' k u c = u ⟨φ c.site, c.dirs⟩ := by
  rw [pullback_apply, orientation_refl_one, one_mul]
  congr 2
  · simp [show (1 : ℤˣ) ≠ -1 by decide]
  · ext; simp

omit [Fintype ι'] [LinearOrder ι'] in
/-- **Periodic extension commutes with `d`**: for `φ` sending steps to steps
(`φ (x + e i) = φ x + e' i`), e.g. the quotient map `ℤᵈ → ℤᵈ ⧸ Γ` or a translation,
`d (u ∘ φ) = (d u) ∘ φ` on cells. -/
theorem coboundary_comp [AddCommGroup X] {e' : ι → Y} (hφ : ∀ x i, φ (x + e i) = φ x + e' i)
    (u : CubicalCell Y ι k → R) :
    coboundary e k (fun c ↦ u ⟨φ c.site, c.dirs⟩) =
      fun c ↦ coboundary e' k u ⟨φ c.site, c.dirs⟩ := by
  have h := coboundary_pullback (R := R) (e := e) (e' := e') (σ := Equiv.refl ι)
    (s := fun _ ↦ 1) (φ := φ) (k := k) (fun x i ↦ by simp [hφ]) u
  have h₁ : pullback φ (Equiv.refl ι) (fun _ ↦ 1) e' k u = fun c ↦ u ⟨φ c.site, c.dirs⟩ :=
    funext (pullback_refl_one_apply u)
  rw [h₁] at h
  rw [h]
  exact funext (pullback_refl_one_apply _)

/-- **The pullback by a bijective cubical map preserves the pairing** `∑_c u c * v c`. -/
theorem sum_pullback_mul_pullback [Fintype X] [Fintype Y] (hφ : Function.Bijective φ)
    (u v : CubicalCell Y ι' k → R) :
    ∑ c, pullback φ σ s e' k u c * pullback φ σ s e' k v c = ∑ c, u c * v c := by
  let T : CubicalCell X ι k → CubicalCell Y ι' k := fun c ↦
    ⟨φ c.site - ∑ i ∈ (c.dirs : Finset ι) with s i = -1, e' (σ i),
      Set.powersetCard.map k σ.toEmbedding c.dirs⟩
  have hT : Function.Bijective T := by
    refine ⟨fun c c' hcc' ↦ ?_, fun d ↦ ?_⟩
    · have hd : c.dirs = c'.dirs := by
        have := congrArg (fun c ↦ (c.dirs : Finset ι')) hcc'
        simp only [T, Set.powersetCard.val_map] at this
        exact Subtype.ext (map_injective _ this)
      have hs := congrArg CubicalCell.site hcc'
      simp only [T, hd, sub_left_inj] at hs
      exact CubicalCell.ext (hφ.1 hs) hd
    · let I : Set.powersetCard ι k := Set.powersetCard.map k σ.symm.toEmbedding d.dirs
      obtain ⟨x, hx⟩ := hφ.2 (d.site + ∑ i ∈ (I : Finset ι) with s i = -1, e' (σ i))
      refine ⟨⟨x, I⟩, CubicalCell.ext ?_ ?_⟩
      · simp [T, hx]
      · ext; simp [T, I, Finset.map_map]
  rw [← Function.Bijective.sum_comp hT (fun c ↦ u c * v c)]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [pullback_apply, pullback_apply, mul_mul_mul_comm, orientation_mul_orientation, one_mul]

/-! ### Signed permutations of `ℤⁱ` -/

/-- The signed permutation of `ℤⁱ` sending `e i` to `s i • e (σ i)`:
`x ↦ (i' ↦ s (σ⁻¹ i') * x (σ⁻¹ i'))`. For `ι = Fin 3` these are the 48 elements of
`O_cub = O(3) ∩ GL(3, ℤ)`; with the translations they are the lattice isometries of `ℤ³`. -/
def signedPerm (σ : ι ≃ ι') (s : ι → ℤˣ) : (ι → ℤ) ≃+ (ι' → ℤ) where
  toFun x i' := (s (σ.symm i') : ℤ) * x (σ.symm i')
  invFun y i := (s i : ℤ) * y (σ i)
  left_inv x := by ext i; simp [← mul_assoc, ← Units.val_mul, Int.units_mul_self]
  right_inv y := by ext i'; simp [← mul_assoc, ← Units.val_mul, Int.units_mul_self]
  map_add' x y := by ext i'; simp [mul_add]

omit [LinearOrder ι] [LinearOrder ι'] [Fintype ι] [Fintype ι'] in
theorem signedPerm_apply (σ : ι ≃ ι') (s : ι → ℤˣ) (x : ι → ℤ) (i' : ι') :
    signedPerm σ s x i' = (s (σ.symm i') : ℤ) * x (σ.symm i') :=
  rfl

omit [Fintype ι] [Fintype ι'] in
theorem signedPerm_single (σ : ι ≃ ι') (s : ι → ℤˣ) (i : ι) :
    signedPerm σ s (Pi.single i 1) = (s i : ℤ) • Pi.single (σ i) 1 := by
  ext i'
  rcases eq_or_ne i' (σ i) with rfl | h
  · simp [signedPerm_apply]
  · rw [signedPerm_apply, Pi.single_eq_of_ne (by rwa [Ne, Equiv.symm_apply_eq]),
      Pi.smul_apply, Pi.single_eq_of_ne h, mul_zero, smul_zero]

/-- **`d` commutes with the lattice isometries `x ↦ r x + a` of `ℤⁱ`**, `r` a signed
permutation. -/
theorem coboundary_pullback_signedPerm (a : ι' → ℤ) (u : CubicalCell (ι' → ℤ) ι' k → R) :
    coboundary (fun i ↦ Pi.single i 1) k
        (pullback (fun x ↦ signedPerm σ s x + a) σ s (fun i' ↦ Pi.single i' 1) k u) =
      pullback (fun x ↦ signedPerm σ s x + a) σ s (fun i' ↦ Pi.single i' 1) (k + 1)
        (coboundary (fun i' ↦ Pi.single i' 1) k u) := by
  refine coboundary_pullback (fun x i ↦ ?_) u
  rw [map_add, signedPerm_single]
  abel

end CubicalCochain

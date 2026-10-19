/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Int.Order.Units
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Signed permutations: the hyperoctahedral group

A *signed permutation* of `ι` sends each coordinate vector `e i` of `ℤ^ι` to `± e (σ i)` for a
permutation `σ`. For finite `ι` they form the hyperoctahedral group: the symmetry group of the
cube `[-1, 1]^ι`, the Weyl group of type `B = C`, and the integral orthogonal group
`O(ι) ∩ GL(ι, ℤ)` (`orthogonalGroupEquiv`). We take it to be Mathlib's semidirect product

  `SignedPerm ι = (ι → ℤˣ) ⋊ Perm ι`,

the permutations acting on the sign changes by `(σ • t) i = t (σ⁻¹ i)` (`mulAutArrow`). The
element `⟨t, σ⟩ = inl t * inr σ` first permutes the coordinates and then changes their signs: on
`ι → M`, `M` any additive group, `(⟨t, σ⟩ • x) i = t i • x (σ⁻¹ i)` (`smul_apply`), so
`⟨t, σ⟩ • e i = t (σ i) • e (σ i)` (`smul_single`), with matrix `diagonal t * P_{σ⁻¹}`
(`toMatrix`, `toMatrix_mulVec`).

## Main results

* `orthogonalGroupEquiv`: **`SignedPerm ι ≃* O(ι, ℤ)`**, the signed permutations are exactly the
  integral orthogonal matrices (`Matrix.orthogonalGroup ι ℤ`).
* `dotProduct_smul_smul`: signed permutations preserve the standard bilinear form.
* `sign`, `det_toMatrix`: the determinant `(∏ i, t i) * sign σ` as a character.
* `card`: `Nat.card (SignedPerm ι) = 2 ^ n * n !`, `n = Nat.card ι`; `Fintype` and `DecidableEq`
  shortcut instances (the unfolded instance terms are too large for products of index types).
* `reflection`, `reflection_smul`: for integral `n` with `n ⬝ᵥ n ∣ 2` (the roots `± e i`,
  `± e i ± e j`) the orthogonal reflection `x ↦ x - (2 / (n ⬝ᵥ n)) (n ⬝ᵥ x) n` is a signed
  permutation, of sign `-1` (`sign_reflection`); `reflection_single` and
  `reflection_single_add_single_neg_one` identify the sign changes and the transpositions.
* `smul_injective`: the action on `ℤ^ι` is faithful.
* `closure_insert_inl_mulSingle_image_inr`: one sign change together with generators of the
  symmetric group generate; for `Fin (n + 1)` the adjacent transpositions and one sign change
  (`closure_inl_mulSingle_inr_swap_castSucc_succ`).
-/

@[expose] public section

open Equiv Finset Function Matrix SemidirectProduct

/-- The hyperoctahedral group of the **signed permutations** of `ι`: the sign changes `ι → ℤˣ`
extended by the permutations of `ι`, which act on them by `(σ • t) i = t (σ⁻¹ i)`. The element
`⟨t, σ⟩` maps `e i` to `t (σ i) • e (σ i)`. -/
abbrev SignedPerm (ι : Type*) := (ι → ℤˣ) ⋊[mulAutArrow] Perm ι

namespace SignedPerm

variable {ι M : Type*}

/-- Shortcut instance: the derived one unfolds the semidirect product and the sign functions, and
its term exceeds the instance size limit inside index types such as `(X × SignedPerm ι) × s ⊕ ⋯`.
-/
instance [Fintype ι] [DecidableEq ι] : DecidableEq (SignedPerm ι) :=
  inferInstanceAs (DecidableEq ((ι → ℤˣ) ⋊[mulAutArrow] Perm ι))

/-- Shortcut instance, as for `DecidableEq`. -/
instance [Fintype ι] [DecidableEq ι] : Fintype (SignedPerm ι) :=
  inferInstanceAs (Fintype ((ι → ℤˣ) ⋊[mulAutArrow] Perm ι))

theorem mul_left_apply (r r' : SignedPerm ι) (i : ι) :
    (r * r').left i = r.left i * r'.left (r.right⁻¹ i) :=
  rfl

theorem inv_left_apply (r : SignedPerm ι) (i : ι) : r⁻¹.left i = r.left (r.right i) := by
  change (r.left (r.right⁻¹⁻¹ i))⁻¹ = _
  rw [inv_inv, Int.units_inv_eq_self]

/-! ### The action on `ι → M` -/

section Action

variable [AddCommGroup M]

instance : MulAction (SignedPerm ι) (ι → M) where
  smul r x i := r.left i • x (r.right⁻¹ i)
  one_smul x := funext fun i ↦ by
    change (1 : ι → ℤˣ) i • x ((1 : Perm ι)⁻¹ i) = x i
    simp
  mul_smul r r' x := funext fun i ↦ by
    change (r * r').left i • x ((r.right * r'.right)⁻¹ i) =
      r.left i • r'.left (r.right⁻¹ i) • x (r'.right⁻¹ (r.right⁻¹ i))
    rw [mul_left_apply, mul_smul, _root_.mul_inv_rev, Perm.mul_apply]

theorem smul_apply (r : SignedPerm ι) (x : ι → M) (i : ι) :
    (r • x) i = r.left i • x (r.right⁻¹ i) :=
  rfl

instance : DistribMulAction (SignedPerm ι) (ι → M) where
  smul_zero r := funext fun i ↦ by simp [smul_apply]
  smul_add r x y := funext fun i ↦ by simp [smul_apply, smul_add]

instance {R : Type*} [Semiring R] [Module R M] : SMulCommClass (SignedPerm ι) R (ι → M) where
  smul_comm r c x := funext fun i ↦ by
    simp only [smul_apply, Pi.smul_apply, Units.smul_def]
    exact (smul_comm c ((r.left i : ℤ)) (x _)).symm

theorem inl_smul (t : ι → ℤˣ) (x : ι → M) :
    (inl t : SignedPerm ι) • x = fun i ↦ t i • x i := by
  ext i
  simp [smul_apply]

theorem inr_smul (σ : Perm ι) (x : ι → M) :
    (inr σ : SignedPerm ι) • x = fun i ↦ x (σ⁻¹ i) := by
  ext i
  simp [smul_apply]

theorem smul_single [DecidableEq ι] (r : SignedPerm ι) (i : ι) (m : M) :
    r • (Pi.single i m : ι → M) = Pi.single (r.right i) (r.left (r.right i) • m) := by
  ext j
  rcases eq_or_ne j (r.right i) with rfl | h
  · simp [smul_apply]
  · rw [smul_apply, Pi.single_eq_of_ne (by rwa [Ne, Perm.inv_eq_iff_eq]), smul_zero,
      Pi.single_eq_of_ne h]

/-- `r` maps `e i` to `e j` iff `σ i = j` and the sign at `j` is `+1`. -/
theorem smul_single_one_eq_single_one_iff [DecidableEq ι] (r : SignedPerm ι) (i j : ι) :
    r • (Pi.single i 1 : ι → ℤ) = Pi.single j 1 ↔ r.right i = j ∧ r.left j = 1 := by
  rw [smul_single]
  constructor
  · intro h
    have hσ : r.right i = j := by
      by_contra hne
      have := congrFun h j
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at this
      exact one_ne_zero this.symm
    refine ⟨hσ, Units.ext ?_⟩
    have := congrFun h j
    rwa [hσ, Pi.single_eq_same, Pi.single_eq_same, Units.smul_def, smul_eq_mul, mul_one] at this
  · rintro ⟨rfl, h⟩
    rw [h, one_smul]

/-- Signed permutations commute with additive maps of the coordinates, e.g. with the cast
`ℤ → ℝ`. -/
theorem comp_smul {N : Type*} [AddCommGroup N] (f : M →+ N) (r : SignedPerm ι) (x : ι → M) :
    (fun i ↦ f ((r • x) i)) = r • fun i ↦ f (x i) := by
  ext i
  simp [smul_apply, Units.smul_def]

/-- The action on `ι → ℤ` is faithful. -/
theorem smul_injective {r r' : SignedPerm ι} (h : ∀ x : ι → ℤ, r • x = r' • x) : r = r' := by
  classical
  have hσ : ∀ i, r.right i = r'.right i := fun i ↦ by
    have := congrFun (h (Pi.single i 1)) (r.right i)
    rw [smul_single, smul_single, Pi.single_eq_same] at this
    by_contra hne
    rw [Pi.single_eq_of_ne hne, Units.smul_def, smul_eq_mul, mul_one] at this
    exact Units.ne_zero _ this
  have hσ' : r.right = r'.right := Equiv.ext hσ
  refine SemidirectProduct.ext (funext fun i ↦ ?_) hσ'
  have := congrFun (h (Pi.single (r.right⁻¹ i) 1)) i
  rw [smul_single, smul_single, ← hσ', ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply,
    Pi.single_eq_same, Pi.single_eq_same, Units.smul_def, Units.smul_def, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one] at this
  exact Units.ext this

/-- Signed permutations preserve the standard bilinear form. -/
theorem dotProduct_smul_smul [Fintype ι] {R : Type*} [CommRing R] (r : SignedPerm ι)
    (x y : ι → R) : (r • x) ⬝ᵥ (r • y) = x ⬝ᵥ y := by
  simp only [dotProduct, smul_apply, Units.smul_def, zsmul_eq_mul]
  have h : ∀ i, ((r.left i : ℤ) : R) * x (r.right⁻¹ i) * (((r.left i : ℤ) : R) *
      y (r.right⁻¹ i)) = x (r.right⁻¹ i) * y (r.right⁻¹ i) := fun i ↦ by
    rw [mul_mul_mul_comm, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_mul]
  simp_rw [h]
  exact Equiv.sum_comp r.right⁻¹ fun i ↦ x i * y i

theorem smul_dotProduct_eq_dotProduct_inv_smul [Fintype ι] {R : Type*} [CommRing R]
    (r : SignedPerm ι) (x y : ι → R) : (r • x) ⬝ᵥ y = x ⬝ᵥ (r⁻¹ • y) := by
  conv_rhs => rw [← dotProduct_smul_smul r, smul_inv_smul]

end Action

/-! ### Matrices and the integral orthogonal group -/

section Matrix

variable [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R]

/-- The matrix of a signed permutation, `diagonal t * P_{σ⁻¹}`: its entry `(i, j)` is `t i` if
`σ j = i` and `0` otherwise (`toMatrix_apply`), and `toMatrix R r *ᵥ x = r • x`. -/
def toMatrix : SignedPerm ι →* Matrix ι ι R where
  toFun r := diagonal (fun i ↦ ((r.left i : ℤ) : R)) * permMatrixHom r.right
  map_one' := by simp
  map_mul' r r' := by
    refine Matrix.toLin'.injective (LinearMap.ext fun x ↦ ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, permMatrixHom_apply,
      permMatrix_mulVec]
    ext i
    simp [mulVec_diagonal, mul_left_apply, mul_assoc]

variable {R}

theorem toMatrix_apply (r : SignedPerm ι) (i j : ι) :
    toMatrix R r i j = if r.right j = i then ((r.left i : ℤ) : R) else 0 := by
  simp only [toMatrix, MonoidHom.coe_mk, OneHom.coe_mk, diagonal_mul, permMatrixHom_apply,
    PEquiv.toMatrix_apply, toPEquiv_apply, Option.mem_def, Option.some_inj,
    Perm.inv_eq_iff_eq, mul_ite, mul_one, mul_zero]
  exact if_congr eq_comm rfl rfl

/-- **The matrix of `r` acts as `r`.** -/
theorem toMatrix_mulVec (r : SignedPerm ι) (x : ι → R) : toMatrix R r *ᵥ x = r • x := by
  ext i
  simp only [toMatrix, MonoidHom.coe_mk, OneHom.coe_mk, ← mulVec_mulVec, permMatrixHom_apply,
    permMatrix_mulVec, mulVec_diagonal, Function.comp_apply, smul_apply, Units.smul_def,
    zsmul_eq_mul]

theorem toMatrix_map_intCast (r : SignedPerm ι) : (toMatrix ℤ r).map (Int.cast : ℤ → R) =
    toMatrix R r := by
  ext i j
  rw [map_apply, toMatrix_apply, toMatrix_apply]
  split_ifs <;> simp

theorem toMatrix_injective : Function.Injective (toMatrix ℤ : SignedPerm ι → Matrix ι ι ℤ) :=
  fun r r' h ↦ smul_injective fun x ↦ by
    simpa only [toMatrix_mulVec] using congrArg (· *ᵥ x) h

theorem transpose_toMatrix (r : SignedPerm ι) : (toMatrix R r)ᵀ = toMatrix R r⁻¹ := by
  ext i j
  rw [transpose_apply, toMatrix_apply, toMatrix_apply, inv_right, inv_left_apply]
  simp only [Perm.inv_eq_iff_eq]
  by_cases h : r.right i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem toMatrix_mem_orthogonalGroup (r : SignedPerm ι) :
    toMatrix R r ∈ orthogonalGroup ι R := by
  rw [mem_orthogonalGroup_iff', transpose_toMatrix, ← map_mul, inv_mul_cancel, map_one]

omit [DecidableEq ι] in
/-- A unit vector of `ℤ^ι` has a single nonzero coordinate, equal to `± 1`. -/
theorem mul_self_eq_one_and_eq_zero_of_dotProduct_self_eq_one {v : ι → ℤ} (hv : v ⬝ᵥ v = 1)
    {i : ι} (hi : v i ≠ 0) : v i * v i = 1 ∧ ∀ i' ≠ i, v i' = 0 := by
  classical
  rw [dotProduct, ← add_sum_erase _ _ (mem_univ i)] at hv
  have h1 : 1 ≤ v i * v i := by nlinarith [Int.one_le_abs hi, abs_mul_abs_self (v i)]
  have hnn : 0 ≤ ∑ k ∈ univ.erase i, v k * v k := sum_nonneg fun k _ ↦ mul_self_nonneg (v k)
  refine ⟨by linarith, fun i' hi' ↦ mul_self_eq_zero.1 ?_⟩
  exact (sum_eq_zero_iff_of_nonneg fun k _ ↦ mul_self_nonneg (v k)).1 (by linarith) i'
    (mem_erase.2 ⟨hi', mem_univ _⟩)

/-- **Every integral orthogonal matrix is a signed permutation matrix.** -/
theorem exists_toMatrix_eq_of_transpose_mul_self_eq_one {A : Matrix ι ι ℤ} (hA : Aᵀ * A = 1) :
    ∃ r : SignedPerm ι, toMatrix ℤ r = A := by
  have hcol : ∀ j, (fun i ↦ A i j) ⬝ᵥ (fun i ↦ A i j) = 1 := fun j ↦ by
    simpa [mul_apply, dotProduct] using congrFun (congrFun hA j) j
  have hoff : ∀ j j', j ≠ j' → ∑ i, A i j * A i j' = 0 := fun j j' h ↦ by
    simpa [mul_apply, one_apply_ne h] using congrFun (congrFun hA j) j'
  have hex : ∀ j, ∃ i, A i j ≠ 0 := fun j ↦ by
    by_contra! h
    simpa [dotProduct, h] using hcol j
  choose f hf using hex
  have hzero : ∀ j i, i ≠ f j → A i j = 0 := fun j i hi ↦
    (mul_self_eq_one_and_eq_zero_of_dotProduct_self_eq_one (hcol j) (hf j)).2 i hi
  have hinj : Injective f := fun j j' hjj' ↦ by
    by_contra h
    have := hoff j j' h
    rw [sum_eq_single (f j) (fun i _ hi ↦ by rw [hzero j i hi, zero_mul]) (by simp)] at this
    exact mul_ne_zero (hf j) (hjj' ▸ hf j') this
  let σ : Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hσ : ∀ j, σ j = f j := fun _ ↦ rfl
  have hunit : ∀ j, IsUnit (A (σ j) j) := fun j ↦ IsUnit.of_mul_eq_one _
    (mul_self_eq_one_and_eq_zero_of_dotProduct_self_eq_one (hcol j) (hf j)).1
  refine ⟨⟨fun i ↦ (hunit (σ⁻¹ i)).unit, σ⟩, ext fun i j ↦ ?_⟩
  rw [toMatrix_apply]
  split_ifs with h
  · subst h
    simp
  · exact (hzero j i (by rwa [← hσ, Ne, eq_comm])).symm

/-- Signed permutations as integral orthogonal matrices. -/
def toOrthogonalGroup : SignedPerm ι →* orthogonalGroup ι ℤ where
  toFun r := ⟨toMatrix ℤ r, toMatrix_mem_orthogonalGroup r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' r r' := Subtype.ext (map_mul _ r r')

/-- **The hyperoctahedral group is the integral orthogonal group** `O(ι) ∩ GL(ι, ℤ)`: the
integral matrices `A` with `Aᵀ A = 1` are exactly the signed permutation matrices. -/
noncomputable def orthogonalGroupEquiv : SignedPerm ι ≃* orthogonalGroup ι ℤ :=
  MulEquiv.ofBijective toOrthogonalGroup
    ⟨fun _ _ h ↦ toMatrix_injective (congrArg Subtype.val h), fun A ↦
      (exists_toMatrix_eq_of_transpose_mul_self_eq_one
        ((mem_orthogonalGroup_iff' ι ℤ).1 A.2)).imp fun _ h ↦ Subtype.ext h⟩

@[simp]
theorem coe_orthogonalGroupEquiv (r : SignedPerm ι) :
    (orthogonalGroupEquiv r : Matrix ι ι ℤ) = toMatrix ℤ r :=
  rfl

@[simp]
theorem toMatrix_orthogonalGroupEquiv_symm (A : orthogonalGroup ι ℤ) :
    toMatrix ℤ (orthogonalGroupEquiv.symm A) = A := by
  rw [← coe_orthogonalGroupEquiv, MulEquiv.apply_symm_apply]

end Matrix

/-! ### The sign character and the order -/

/-- The hyperoctahedral group has order `2 ^ n * n !`. -/
theorem card [Finite ι] : Nat.card (SignedPerm ι) = 2 ^ Nat.card ι * (Nat.card ι).factorial := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_perm, Nat.card_eq_fintype_card (α := ℤˣ),
    Fintype.card_units_int]

section Sign

variable [Fintype ι] [DecidableEq ι]

/-- The sign character `⟨t, σ⟩ ↦ (∏ i, t i) * sign σ` of the hyperoctahedral group, the
determinant of the signed permutation matrix (`det_toMatrix`). -/
def sign : SignedPerm ι →* ℤˣ where
  toFun r := (∏ i, r.left i) * Perm.sign r.right
  map_one' := by simp
  map_mul' r r' := by
    simp only [mul_left_apply, mul_right, prod_mul_distrib, map_mul,
      Equiv.prod_comp r.right⁻¹ r'.left]
    exact mul_mul_mul_comm _ _ _ _

theorem sign_apply (r : SignedPerm ι) : sign r = (∏ i, r.left i) * Perm.sign r.right :=
  rfl

@[simp]
theorem sign_inl (t : ι → ℤˣ) : sign (inl t : SignedPerm ι) = ∏ i, t i := by
  simp [sign_apply]

@[simp]
theorem sign_inr (σ : Perm ι) : sign (inr σ : SignedPerm ι) = Perm.sign σ := by
  simp [sign_apply]

theorem det_toMatrix {R : Type*} [CommRing R] (r : SignedPerm ι) :
    (toMatrix R r).det = ((sign r : ℤ) : R) := by
  simp [toMatrix, det_mul, det_diagonal, sign_apply, Perm.sign_inv]

end Sign

/-! ### Reflections -/

section Reflection

variable [Fintype ι] [DecidableEq ι] {n : ι → ℤ}

theorem transpose_mul_self_one_sub_smul_vecMulVec (hn : n ⬝ᵥ n ∣ 2) :
    (1 - (2 / (n ⬝ᵥ n)) • vecMulVec n n)ᵀ * (1 - (2 / (n ⬝ᵥ n)) • vecMulVec n n) = 1 := by
  set c := 2 / (n ⬝ᵥ n)
  have hc : c * (n ⬝ᵥ n) = 2 := Int.ediv_mul_cancel hn
  have hN : vecMulVec n n * vecMulVec n n = (n ⬝ᵥ n) • vecMulVec n n := by
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul]
  rw [transpose_sub, transpose_one, transpose_smul, transpose_vecMulVec, sub_mul, mul_sub,
    mul_sub, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hN, smul_smul,
    smul_smul, mul_assoc, hc]
  module

/-- The orthogonal reflection `x ↦ x - (2 / (n ⬝ᵥ n)) (n ⬝ᵥ x) n` in the hyperplane `n^⊥`, for
`n ∈ ℤ^ι` with `n ⬝ᵥ n ∣ 2`, i.e. `n = ± e i` or `n = ± e i ± e j` (`i ≠ j`): its matrix
`1 - (2 / (n ⬝ᵥ n)) n nᵀ` is integral and orthogonal, hence a signed permutation
(`reflection_smul`). -/
noncomputable def reflection (n : ι → ℤ) (hn : n ⬝ᵥ n ∣ 2) : SignedPerm ι :=
  orthogonalGroupEquiv.symm ⟨1 - (2 / (n ⬝ᵥ n)) • vecMulVec n n,
    (mem_orthogonalGroup_iff' ι ℤ).2 (transpose_mul_self_one_sub_smul_vecMulVec hn)⟩

theorem toMatrix_reflection (hn : n ⬝ᵥ n ∣ 2) :
    toMatrix ℤ (reflection n hn) = 1 - (2 / (n ⬝ᵥ n)) • vecMulVec n n := by
  rw [reflection, toMatrix_orthogonalGroupEquiv_symm]

/-- **The reflection formula** `r_n x = x - (2 / (n ⬝ᵥ n)) (n ⬝ᵥ x) n`, over any commutative
ring. -/
theorem reflection_smul {R : Type*} [CommRing R] (hn : n ⬝ᵥ n ∣ 2) (x : ι → R) :
    reflection n hn • x =
      x - (((2 / (n ⬝ᵥ n) : ℤ) : R) * ((fun i ↦ (n i : R)) ⬝ᵥ x)) • fun i ↦ (n i : R) := by
  have hM : toMatrix R (reflection n hn) =
      1 - ((2 / (n ⬝ᵥ n) : ℤ) : R) • vecMulVec (fun i ↦ (n i : R)) fun i ↦ (n i : R) := by
    ext i j
    rw [← toMatrix_map_intCast, toMatrix_reflection, map_apply, Matrix.sub_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, vecMulVec_apply, vecMulVec_apply,
      one_apply, one_apply, smul_eq_mul, smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  rw [← toMatrix_mulVec, hM, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

/-- Reflections are odd. -/
theorem sign_reflection (hn : n ⬝ᵥ n ∣ 2) : sign (reflection n hn) = -1 := by
  have hc : 2 / (n ⬝ᵥ n) * (n ⬝ᵥ n) = 2 := Int.ediv_mul_cancel hn
  have h := det_toMatrix (R := ℤ) (reflection n hn)
  rw [Int.cast_id, toMatrix_reflection, vecMulVec_eq Unit, sub_eq_add_neg, ← neg_smul,
    ← Matrix.smul_mul, ← replicateCol_smul, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul, neg_mul, hc] at h
  exact Units.ext (by rw [← h]; norm_num)

/-- The reflection in `e i ^⊥` changes the sign of the `i`-th coordinate. -/
theorem reflection_single (i : ι) (h : Pi.single i (1 : ℤ) ⬝ᵥ Pi.single i 1 ∣ 2) :
    reflection (Pi.single i 1) h = inl (Pi.mulSingle i (-1)) := by
  refine smul_injective fun x ↦ funext fun k ↦ ?_
  rw [reflection_smul (R := ℤ), inl_smul]
  rcases eq_or_ne k i with rfl | hk
  · simp [Pi.single_apply, dotProduct]
    ring
  · simp [Pi.single_apply, hk]

/-- The reflection in `(e i - e j)^⊥` is the transposition of `i` and `j`. -/
theorem reflection_single_add_single_neg_one {i j : ι} (hij : i ≠ j)
    (h : (Pi.single i 1 + Pi.single j (-1) : ι → ℤ) ⬝ᵥ (Pi.single i 1 + Pi.single j (-1)) ∣ 2) :
    reflection (Pi.single i 1 + Pi.single j (-1) : ι → ℤ) h = inr (Equiv.swap i j) := by
  have hnn : (Pi.single i 1 + Pi.single j (-1) : ι → ℤ) ⬝ᵥ (Pi.single i 1 + Pi.single j (-1)) =
      2 := by
    simp [dotProduct_add, hij, hij.symm]
  refine smul_injective fun x ↦ funext fun k ↦ ?_
  have hdot : (Pi.single i 1 + Pi.single j (-1) : ι → ℤ) ⬝ᵥ x = x i - x j := by
    rw [add_dotProduct, single_dotProduct, single_dotProduct]
    ring
  rw [reflection_smul (R := ℤ), inr_smul, hnn]
  simp only [Int.cast_id, show (2 : ℤ) / 2 = 1 from rfl, one_mul, hdot]
  rcases eq_or_ne k i with rfl | hki
  · simp [Pi.single_apply, hij, swap_apply_left]
  rcases eq_or_ne k j with rfl | hkj
  · simp [Pi.single_apply, hki, swap_apply_right]
  · simp [Pi.single_apply, hki, hkj, swap_apply_of_ne_of_ne hki hkj]

end Reflection

/-! ### Generators -/

section Closure

variable [DecidableEq ι]

theorem mulAutArrow_swap_mulSingle (i₀ i : ι) (u : ℤˣ) :
    mulAutArrow (Equiv.swap i₀ i) (Pi.mulSingle i₀ u : ι → ℤˣ) = Pi.mulSingle i u := by
  funext j
  rw [mulAutArrow_apply_apply]
  change (Pi.mulSingle i₀ u : ι → ℤˣ) ((Equiv.swap i₀ i)⁻¹ j) = _
  rw [swap_inv, Pi.mulSingle_apply, Pi.mulSingle_apply]
  simp only [swap_apply_eq_iff, swap_apply_left]

/-- **One sign change and generators of the symmetric group generate the signed
permutations.** -/
theorem closure_insert_inl_mulSingle_image_inr [Finite ι] {S : Set (Perm ι)}
    (hS : Subgroup.closure S = ⊤) (i₀ : ι) :
    Subgroup.closure (insert (inl (Pi.mulSingle i₀ (-1))) (inr '' S) :
      Set (SignedPerm ι)) = ⊤ := by
  set H := Subgroup.closure (insert (inl (Pi.mulSingle i₀ (-1))) (inr '' S) :
    Set (SignedPerm ι))
  have hinr : ∀ σ, (inr σ : SignedPerm ι) ∈ H := fun σ ↦ by
    have hσ : σ ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top σ
    induction hσ using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
    | one => rw [map_one]; exact H.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact H.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact H.inv_mem hx
  have hflip : ∀ i, (inl (Pi.mulSingle i (-1)) : SignedPerm ι) ∈ H := fun i ↦ by
    rw [← mulAutArrow_swap_mulSingle i₀ i, inl_aut]
    exact H.mul_mem (H.mul_mem (hinr _) (Subgroup.subset_closure (Set.mem_insert _ _)))
      (hinr _)
  have hinl : ∀ t, (inl t : SignedPerm ι) ∈ H := fun t ↦ by
    have := Fintype.ofFinite ι
    change t ∈ H.comap inl
    rw [← Finset.univ_prod_mulSingle t]
    refine Subgroup.prod_mem _ fun i _ ↦ ?_
    rcases Int.units_eq_one_or (t i) with h | h
    · rw [h, Pi.mulSingle_one]; exact Subgroup.one_mem _
    · rw [h]; exact hflip i
  refine eq_top_iff.2 fun r _ ↦ ?_
  rw [← inl_left_mul_inr_right r]
  exact H.mul_mem (hinl _) (hinr _)

/-- The signed permutations of `Fin (n + 1)` are generated by the adjacent transpositions and any
one sign change. -/
theorem closure_inl_mulSingle_inr_swap_castSucc_succ (n : ℕ) (i₀ : Fin (n + 1)) :
    Subgroup.closure (insert (inl (Pi.mulSingle i₀ (-1)))
      (Set.range fun i : Fin n ↦ inr (Equiv.swap i.castSucc i.succ)) :
        Set (SignedPerm (Fin (n + 1)))) = ⊤ := by
  rw [← closure_insert_inl_mulSingle_image_inr
    (Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ n)) i₀,
    ← Set.range_comp]
  rfl

end Closure

end SignedPerm

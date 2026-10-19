/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Basic

/-!
# The adjoint coboundary and the Hodge Laplacian of a cubical lattice

On total cochains the adjoint coboundary is `totalCodiff e V x = ∑ j, contract j (Δ_[-e j] V x)`:
the contraction `contract j` is the transpose of `wedge j` and the backward difference
`Δ_[-e j]` that of `Δ_[e j]`, so for a finite `X` it is the transpose of `totalCoboundary e` for
the pairing `∑ₓ ∑_I U x I * V x I`, in which the cells are orthonormal
(`sum_totalCoboundary_mul`). Because the differences commute and `contract i`, `wedge j`
anticommute to `δᵢⱼ`, the Hodge Laplacian of the flat cubical complex is the lattice Laplacian
acting on each component (`totalCodiff_totalCoboundary_add_totalCoboundary_totalCodiff`):
`d* d + d d* = ∑ⱼ Δ_[-e j] Δ_[e j]`, `(d* d + d d*) U x = ∑ⱼ (2 U x - U (x + e j) - U (x - e j))`.

On `k`-cochains `codiff e k : C^{k+1} → C^k` is the transpose of `coboundary e k`
(`sum_coboundary_mul`), and `hodgeLaplacian e k` is `d* d` in degree `0` and `d* d + d d*` above
(`hodgeLaplacian_zero`, `hodgeLaplacian_succ`); it is the componentwise lattice Laplacian
(`hodgeLaplacian_apply`), symmetric (`sum_hodgeLaplacian_mul_comm`), and its bilinear form is
`⟨d u, d v⟩ + ⟨d* u, d* v⟩` (`sum_hodgeLaplacian_mul_succ`, `sum_hodgeLaplacian_mul_zero`), so it
is nonnegative (`sum_hodgeLaplacian_mul_self_nonneg`).
-/

@[expose] public section

open Finset

namespace CubicalCochain

open CubicalCell

variable {X ι R : Type*} [AddCommGroup X] [LinearOrder ι] [Fintype ι] [CommRing R]

/-! ### Total cochains -/

/-- The adjoint coboundary of total cochains, `d* V = ∑ⱼ e_j* ⌟ Δ_[-e j] V`. In the basis,
`d* V x I = ∑_{j ∉ I} (-1) ^ #{i ∈ I | i < j} (V (x - e j) (insert j I) - V x (insert j I))`
(`totalCodiff_apply`): the signed sum over the cubes having `x + [0,1]^I` as a face. -/
def totalCodiff (e : ι → X) : (X → Finset ι → R) →ₗ[R] X → Finset ι → R where
  toFun V x := ∑ j, contract j (fwdDiff (-e j) V x)
  map_add' U V := by ext x; simp [fwdDiff, sub_add_sub_comm, sum_add_distrib]
  map_smul' c U := by
    ext x : 1
    simp only [fwdDiff, Pi.smul_apply, RingHom.id_apply, ← smul_sub, map_smul, Finset.smul_sum]

theorem totalCodiff_apply' (e : ι → X) (V : X → Finset ι → R) (x : X) :
    totalCodiff e V x = ∑ j, contract j (fwdDiff (-e j) V x) :=
  rfl

theorem totalCodiff_apply (e : ι → X) (V : X → Finset ι → R) (x : X) (I : Finset ι) :
    totalCodiff e V x I = ∑ j ∈ univ.filter (· ∉ I),
      (-1) ^ #{i ∈ I | i < j} * (V (x - e j) (insert j I) - V x (insert j I)) := by
  rw [totalCodiff_apply', Finset.sum_apply, ← sum_filter_add_sum_filter_not univ (· ∈ I)]
  simp only [contract_apply, fwdDiff, Pi.sub_apply, ← sub_eq_add_neg]
  rw [sum_eq_zero fun j hj ↦ ite_eq_left (mem_filter.1 hj).2, zero_add]
  exact sum_congr rfl fun j hj ↦ ite_eq_right (mem_filter.1 hj).2

/-- The total adjoint coboundary of a cochain of degree `k + 1` has degree `k`. -/
theorem totalCodiff_apply_of_card_ne {e : ι → X} {k : ℕ} {V : X → Finset ι → R}
    (hV : ∀ x J, #J ≠ k + 1 → V x J = 0) (x : X) {I : Finset ι} (hI : #I ≠ k) :
    totalCodiff e V x I = 0 := by
  rw [totalCodiff_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  have hne : #(insert j I) ≠ k + 1 := by
    rw [card_insert_of_notMem (mem_filter.1 hj).2]; omega
  rw [hV _ _ hne, hV _ _ hne, sub_self, mul_zero]

/-- **`d*` is the transpose of `d`** for the pairing in which the cells are orthonormal. -/
theorem sum_totalCoboundary_mul [Fintype X] (e : ι → X) (U V : X → Finset ι → R) :
    ∑ x, ∑ J, totalCoboundary e U x J * V x J = ∑ x, ∑ I, U x I * totalCodiff e V x I := by
  have h₁ : ∀ x, ∑ J, totalCoboundary e U x J * V x J =
      ∑ j, (∑ I, U (x + e j) I * contract j (V x) I - ∑ I, U x I * contract j (V x) I) :=
    fun x ↦ by
      simp only [totalCoboundary_apply', Finset.sum_apply, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [sum_wedge_mul, ← sum_sub_distrib]
      simp [fwdDiff, sub_mul]
  have h₂ : ∀ x, ∑ I, U x I * totalCodiff e V x I =
      ∑ j, (∑ I, U x I * contract j (V (x - e j)) I - ∑ I, U x I * contract j (V x) I) :=
    fun x ↦ by
      simp only [totalCodiff_apply', Finset.sum_apply, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun I _ ↦ ?_
      simp [fwdDiff, sub_eq_add_neg, mul_add]
  simp only [h₁, h₂, sum_sub_distrib]
  congr 1
  rw [sum_comm, sum_comm (f := fun x j ↦ ∑ I, U x I * contract j (V (x - e j)) I)]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← (Equiv.subRight (e j)).sum_comp]
  simp

/-- `∑ᵢⱼ (e_i* ⌟ e_j ∧ a i j + e_j ∧ e_i* ⌟ a i j) = ∑ᵢ a i i`. -/
theorem sum_contract_wedge_add_wedge_contract (a : ι → ι → Finset ι → R) :
    ∑ i, ∑ j, (contract i (wedge j (a i j)) + wedge j (contract i (a i j))) = ∑ i, a i i := by
  simp_rw [contract_wedge_add_wedge_contract]
  exact sum_congr rfl fun i _ ↦ by simp

/-- **The Hodge Laplacian of the flat cubical complex is the lattice Laplacian on each
component**: `d* d + d d* = ∑ⱼ Δ_[-e j] Δ_[e j]`, since the differences commute and
`contract i`, `wedge j` anticommute to `δᵢⱼ`. -/
theorem totalCodiff_totalCoboundary_add_totalCoboundary_totalCodiff (e : ι → X)
    (U : X → Finset ι → R) :
    totalCodiff e (totalCoboundary e U) + totalCoboundary e (totalCodiff e U) =
      ∑ j, fwdDiff (-e j) (fwdDiff (e j) U) := by
  ext x : 1
  have h₁ : ∀ i, fwdDiff (-e i) (totalCoboundary e U) x =
      ∑ j, wedge j (fwdDiff (-e i) (fwdDiff (e j) U) x) := fun i ↦ by
    simp only [fwdDiff, totalCoboundary_apply', ← sum_sub_distrib, ← map_sub]
  have h₂ : ∀ j, fwdDiff (e j) (totalCodiff e U) x =
      ∑ i, contract i (fwdDiff (-e i) (fwdDiff (e j) U) x) := fun j ↦ by
    simp only [fwdDiff, totalCodiff_apply', ← sum_sub_distrib, ← map_sub]
    refine sum_congr rfl fun i _ ↦ congrArg _ ?_
    rw [add_right_comm x (e j) (-e i)]
    abel
  simp only [Pi.add_apply, totalCodiff_apply', totalCoboundary_apply', h₁, h₂, map_sum,
    Finset.sum_apply]
  rw [sum_comm (s := univ) (t := univ) (f := fun j i ↦ wedge j (contract i _)),
    ← sum_add_distrib]
  simp_rw [← sum_add_distrib]
  exact sum_contract_wedge_add_wedge_contract _

omit [LinearOrder ι] [Fintype ι] in
theorem fwdDiff_neg_fwdDiff_apply (h : X) (U : X → Finset ι → R) (x : X) :
    fwdDiff (-h) (fwdDiff h U) x = 2 • U x - U (x + h) - U (x - h) := by
  simp only [fwdDiff, ← sub_eq_add_neg, sub_add_cancel]
  abel

/-! ### `k`-cochains -/

variable {e : ι → X} {k : ℕ}

/-- The adjoint coboundary `d* : C^{k+1} → C^k`:
`d* v (x + [0,1]^I) = ∑_{j ∉ I} (-1) ^ #{i ∈ I | i < j} (v (x - e j, I ∪ j) - v (x, I ∪ j))`. -/
def codiff (e : ι → X) (k : ℕ) :
    (CubicalCell X ι (k + 1) → R) →ₗ[R] CubicalCell X ι k → R :=
  restrict k ∘ₗ totalCodiff e ∘ₗ extend (k + 1)

theorem extend_codiff (v : CubicalCell X ι (k + 1) → R) :
    extend k (codiff e k v) = totalCodiff e (extend (k + 1) v) :=
  extend_restrict fun x _ hI ↦
    totalCodiff_apply_of_card_ne (fun x _ hJ ↦ extend_apply_of_card_ne v x hJ) x hI

/-- The total adjoint coboundary vanishes on cochains of degree `0`. -/
theorem totalCodiff_extend_zero (u : CubicalCell X ι 0 → R) : totalCodiff e (extend 0 u) = 0 := by
  ext x I
  rw [totalCodiff_apply, Pi.zero_apply, Pi.zero_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  have hne : #(insert j I) ≠ 0 := (card_pos.2 ⟨j, mem_insert_self j I⟩).ne'
  rw [extend_apply_of_card_ne _ _ hne, extend_apply_of_card_ne _ _ hne, sub_self, mul_zero]

omit [AddCommGroup X] [LinearOrder ι] in
/-- The pairing of `k`-cochains, `∑_c u c * v c`, is that of their extensions. -/
theorem sum_mul_eq_sum_extend_mul [Fintype X] (u v : CubicalCell X ι k → R) :
    ∑ c, u c * v c = ∑ x, ∑ I, extend k u x I * extend k v x I := by
  rw [← Equiv.sum_comp (equivProd (X := X) (ι := ι) (k := k)).symm (fun c ↦ u c * v c),
    Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← sum_filter_add_sum_filter_not univ (fun I : Finset ι ↦ #I = k)]
  rw [sum_eq_zero (s := univ.filter fun I : Finset ι ↦ ¬#I = k) fun I hI ↦ by
    rw [extend_apply_of_card_ne _ _ (mem_filter.1 hI).2, zero_mul], add_zero]
  rw [sum_subtype (p := (· ∈ Set.powersetCard ι k))
    (F := inferInstanceAs (Fintype (Set.powersetCard ι k)))
    (univ.filter fun I : Finset ι ↦ #I = k) (fun I ↦ by simp [Set.powersetCard.mem_iff])]
  simp

/-- **`d*` is the transpose of `d`** on `k`-cochains of a finite lattice. -/
theorem sum_coboundary_mul [Fintype X] (u : CubicalCell X ι k → R)
    (v : CubicalCell X ι (k + 1) → R) :
    ∑ c, coboundary e k u c * v c = ∑ c, u c * codiff e k v c := by
  rw [sum_mul_eq_sum_extend_mul, sum_mul_eq_sum_extend_mul, extend_coboundary, extend_codiff,
    sum_totalCoboundary_mul]

/-- The Hodge Laplacian on `k`-cochains: the degree-`k` part of `d* d + d d*`. -/
def hodgeLaplacian (e : ι → X) (k : ℕ) :
    (CubicalCell X ι k → R) →ₗ[R] CubicalCell X ι k → R :=
  restrict k ∘ₗ (totalCodiff e ∘ₗ totalCoboundary e + totalCoboundary e ∘ₗ totalCodiff e) ∘ₗ
    extend k

theorem hodgeLaplacian_zero :
    hodgeLaplacian e 0 = codiff e 0 ∘ₗ coboundary (R := R) e 0 := by
  ext u c
  simp only [hodgeLaplacian, codiff, LinearMap.comp_apply, LinearMap.add_apply,
    extend_coboundary, totalCodiff_extend_zero, map_zero, add_zero]

theorem hodgeLaplacian_succ :
    hodgeLaplacian e (k + 1) =
      codiff e (k + 1) ∘ₗ coboundary (R := R) e (k + 1) + coboundary e k ∘ₗ codiff e k := by
  ext u c
  have h₁ : codiff e (k + 1) (coboundary e (k + 1) u) =
      restrict (k + 1) (totalCodiff e (totalCoboundary e (extend (k + 1) u))) := by
    rw [codiff, LinearMap.comp_apply, LinearMap.comp_apply, extend_coboundary]
  have h₂ : coboundary e k (codiff e k u) =
      restrict (k + 1) (totalCoboundary e (totalCodiff e (extend (k + 1) u))) := by
    rw [coboundary, LinearMap.comp_apply, LinearMap.comp_apply, extend_codiff]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply, h₁, h₂, hodgeLaplacian,
    map_add]

/-- **The Hodge Laplacian is the lattice Laplacian on each component**:
`Δ u (x + [0,1]^I) = ∑ⱼ (2 u (x, I) - u (x + e j, I) - u (x - e j, I))`. -/
theorem hodgeLaplacian_apply (u : CubicalCell X ι k → R) (c : CubicalCell X ι k) :
    hodgeLaplacian e k u c =
      ∑ j, (2 * u c - u ⟨c.site + e j, c.dirs⟩ - u ⟨c.site - e j, c.dirs⟩) := by
  have h : hodgeLaplacian e k u c = (totalCodiff e (totalCoboundary e (extend k u)) +
      totalCoboundary e (totalCodiff e (extend k u))) c.site c.dirs := rfl
  rw [h, totalCodiff_totalCoboundary_add_totalCoboundary_totalCodiff, Finset.sum_apply,
    Finset.sum_apply]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [fwdDiff_neg_fwdDiff_apply]
  simp

/-- `∑ (d* w) v = ∑ w (d v)`, the transpose identity read from the other side. -/
theorem sum_codiff_mul [Fintype X] (w : CubicalCell X ι (k + 1) → R)
    (v : CubicalCell X ι k → R) :
    ∑ c, codiff e k w c * v c = ∑ c, w c * coboundary e k v c := by
  rw [sum_congr rfl fun c _ ↦ mul_comm (codiff e k w c) (v c), ← sum_coboundary_mul]
  exact sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- The bilinear form of the Hodge Laplacian on `k + 1`-cochains is
`⟨d u, d v⟩ + ⟨d* u, d* v⟩`. -/
theorem sum_hodgeLaplacian_mul_succ [Fintype X] (u v : CubicalCell X ι (k + 1) → R) :
    ∑ c, hodgeLaplacian e (k + 1) u c * v c =
      ∑ c, coboundary e (k + 1) u c * coboundary e (k + 1) v c +
        ∑ c, codiff e k u c * codiff e k v c := by
  rw [hodgeLaplacian_succ]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Pi.add_apply, add_mul, sum_add_distrib]
  rw [sum_codiff_mul, sum_coboundary_mul (u := codiff e k u)]

/-- The bilinear form of the Hodge Laplacian on `0`-cochains is `⟨d u, d v⟩`. -/
theorem sum_hodgeLaplacian_mul_zero [Fintype X] (u v : CubicalCell X ι 0 → R) :
    ∑ c, hodgeLaplacian e 0 u c * v c = ∑ c, coboundary e 0 u c * coboundary e 0 v c := by
  rw [hodgeLaplacian_zero, LinearMap.comp_apply, sum_codiff_mul]

/-- **The Hodge Laplacian is symmetric.** -/
theorem sum_hodgeLaplacian_mul_comm [Fintype X] (u v : CubicalCell X ι k → R) :
    ∑ c, hodgeLaplacian e k u c * v c = ∑ c, u c * hodgeLaplacian e k v c := by
  have h : ∑ c, hodgeLaplacian e k u c * v c = ∑ c, hodgeLaplacian e k v c * u c := by
    cases k with
    | zero =>
      rw [sum_hodgeLaplacian_mul_zero, sum_hodgeLaplacian_mul_zero]
      exact sum_congr rfl fun _ _ ↦ mul_comm _ _
    | succ k =>
      rw [sum_hodgeLaplacian_mul_succ, sum_hodgeLaplacian_mul_succ]
      congr 1 <;> exact sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [h]
  exact sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- **The Hodge Laplacian is nonnegative.** -/
theorem sum_hodgeLaplacian_mul_self_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype X] (u : CubicalCell X ι k → R) :
    0 ≤ ∑ c, hodgeLaplacian e k u c * u c := by
  cases k with
  | zero => rw [sum_hodgeLaplacian_mul_zero]; exact sum_nonneg fun _ _ ↦ mul_self_nonneg _
  | succ k =>
    rw [sum_hodgeLaplacian_mul_succ]
    exact add_nonneg (sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      (sum_nonneg fun _ _ ↦ mul_self_nonneg _)

end CubicalCochain

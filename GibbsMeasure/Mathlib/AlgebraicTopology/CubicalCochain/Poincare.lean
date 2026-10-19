/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Cohomology
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.SuccPred
import Mathlib.Tactic.LinearCombination

/-!
# The Poincaré lemma on `ℤᵈ`

On `X = ι → ℤ` with the unit steps `Pi.single i 1`, every closed cubical cochain of positive
degree is exact and every closed `0`-cochain is constant: `H^{k+1}(ℤᵈ; R) = 0` and
`H⁰(ℤᵈ; R) = R` for every commutative ring `R` (`ℤ` for integer fluxes, `ℝ` for potentials).

The proof is the Koszul contracting homotopy of the commuting differences, one direction at a
time. The oriented sum along the `j`-th coordinate line,
`lineSum j U x = ∑_{t=0}^{x j - 1} U (x with x j := t)` (`orientedSum`; for `x j < 0` it is
`-∑_{t = x j}^{-1}`), inverts the forward difference `Δ_[e j]` from the right
(`fwdDiff_lineSum`), from the left up to the value on the hyperplane `x j = 0`
(`lineSum_fwdDiff_self`), and commutes with the other differences (`lineSum_fwdDiff_of_ne`).
For `h_j = e_j* ⌟ lineSum j` (`lineHomotopy`) the anticommutation relations of `contract` and
`wedge` turn these into the operator identity
`d h_j + h_j d = 1 - r_j` (`totalCoboundary_lineHomotopy_add_lineHomotopy_totalCoboundary`),
where `r_j U x I = [j ∉ I] U (x with x j := 0) I` (`lineRetraction`) keeps the components
without `e_j`, restricted to `x j = 0` and extended constantly along `e j`. Composing over all
directions, a closed total cochain is a coboundary plus its constant degree-`0` part at the
origin (`exists_eq_totalCoboundary_add`).

The primitive is that of [M] Lemma 2.14: the explicit primitives (2.2) of a closed integer
two-cochain and of a closed one-cochain on `ℤ³` are the iterated oriented sums. Only additions
enter, so integer cochains have integer primitives; the primitive of a periodic cochain is in
general not periodic.

## Main results

* `exists_coboundary_eq`: **Poincaré lemma**, `d u = 0` on `(k + 1)`-cochains of `ℤᵈ`
  implies `u = d v`;
* `cocycles_le_coboundaries_succ`, `subsingleton_cohomology_succ`,
  `exactAt_cochainComplex_succ`: the same as `H^{k+1}(ℤᵈ; R) = 0` and exactness;
* `closure_range_single_int`: the unit steps generate `ℤᵈ`, so `H⁰(ℤᵈ; R) ≃ R` is
  `cohomologyZeroEquiv closure_range_single_int`.
-/

@[expose] public section

open Finset Function

namespace CubicalCochain

/-! ### Oriented sums on `ℤ` -/

section OrientedSum

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- The oriented sum `∑_{t=0}^{n-1} g t` over `ℤ`, read as `-∑_{t=n}^{-1} g t` when `n < 0`:
the discrete antiderivative of `g` vanishing at `0` (`orientedSum_add_one`,
`orientedSum_fwdDiff`). -/
def orientedSum (g : ℤ → M) (n : ℤ) : M :=
  ∑ t ∈ Ico 0 n, g t - ∑ t ∈ Ico n 0, g t

@[simp]
theorem orientedSum_zero (g : ℤ → M) : orientedSum g 0 = 0 := by
  simp [orientedSum]

theorem orientedSum_add_one (g : ℤ → M) (n : ℤ) :
    orientedSum g (n + 1) = orientedSum g n + g n := by
  rcases le_or_gt 0 n with h | h
  · rw [orientedSum, orientedSum, ← insert_Ico_right_eq_Ico_add_one h, sum_insert (by simp),
      Ico_eq_empty_of_le (by omega : (0 : ℤ) ≤ n + 1), Ico_eq_empty_of_le h]
    abel
  · rw [orientedSum, orientedSum, Ico_eq_empty_of_le (by omega : n + 1 ≤ 0),
      Ico_eq_empty_of_le h.le, ← insert_Ico_add_one_left_eq_Ico h, sum_insert (by simp)]
    abel

/-- `orientedSum g` is a discrete antiderivative of `g`. -/
theorem fwdDiff_orientedSum (g : ℤ → M) : fwdDiff 1 (orientedSum g) = g := by
  ext n
  rw [fwdDiff, orientedSum_add_one, add_sub_cancel_left]

/-- The oriented sum of a forward difference telescopes. -/
theorem orientedSum_fwdDiff (g : ℤ → M) (n : ℤ) : orientedSum (fwdDiff 1 g) n = g n - g 0 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih => rw [orientedSum_add_one, ih, fwdDiff]; abel
  | pred n ih =>
    have h := orientedSum_add_one (fwdDiff 1 g) (-n - 1)
    rw [sub_add_cancel, ih, fwdDiff, sub_add_cancel] at h
    rw [eq_sub_of_add_eq h.symm]
    abel

theorem orientedSum_add (g h : ℤ → M) (n : ℤ) :
    orientedSum (fun t ↦ g t + h t) n = orientedSum g n + orientedSum h n := by
  simp only [orientedSum, sum_add_distrib]
  abel

theorem orientedSum_sub (g h : ℤ → M) (n : ℤ) :
    orientedSum (fun t ↦ g t - h t) n = orientedSum g n - orientedSum h n := by
  simp only [orientedSum, sum_sub_distrib]
  abel

theorem orientedSum_smul {S : Type*} [Monoid S] [DistribMulAction S M] (c : S) (g : ℤ → M)
    (n : ℤ) : orientedSum (fun t ↦ c • g t) n = c • orientedSum g n := by
  simp only [orientedSum, smul_sub, smul_sum]

theorem map_orientedSum {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (L : F)
    (g : ℤ → M) (n : ℤ) : L (orientedSum g n) = orientedSum (fun t ↦ L (g t)) n := by
  simp only [orientedSum, map_sub, map_sum]

theorem orientedSum_sum {α : Type*} (s : Finset α) (g : α → ℤ → M) (n : ℤ) :
    orientedSum (fun t ↦ ∑ a ∈ s, g a t) n = ∑ a ∈ s, orientedSum (g a) n := by
  simp only [orientedSum, sum_sub_distrib]
  congr 1 <;> exact sum_comm

end OrientedSum

/-! ### Oriented sums along coordinate lines -/

section LineSum

variable {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [AddCommGroup N]

/-- Summation along the `j`-th coordinate line from the hyperplane `x j = 0`:
`lineSum j U x = ∑_{t=0}^{x j - 1} U (x with x j := t)`, an oriented sum. -/
def lineSum (j : ι) (U : (ι → ℤ) → M) (x : ι → ℤ) : M :=
  orientedSum (fun t ↦ U (update x j t)) (x j)

theorem update_add_single_self (x : ι → ℤ) (j : ι) (t : ℤ) :
    update x j t + Pi.single j 1 = update x j (t + 1) := by
  ext i
  rcases eq_or_ne i j with rfl | h <;> simp [*]

theorem update_add_single_self_left (x : ι → ℤ) (j : ι) (t : ℤ) :
    update (x + Pi.single j 1) j t = update x j t := by
  ext i
  rcases eq_or_ne i j with rfl | h <;> simp [*]

theorem update_add_single_of_ne (x : ι → ℤ) {i j : ι} (h : i ≠ j) (t : ℤ) :
    update (x + Pi.single i 1) j t = update x j t + Pi.single i 1 := by
  ext l
  rcases eq_or_ne l j with rfl | hl
  · simp [h.symm]
  · simp [hl]

/-- `lineSum j` is a right inverse of the difference `Δ_[e j]`. -/
theorem fwdDiff_lineSum (j : ι) (U : (ι → ℤ) → M) :
    fwdDiff (Pi.single j 1) (lineSum j U) = U := by
  ext x
  simp only [fwdDiff, lineSum, update_add_single_self_left, Pi.add_apply, Pi.single_eq_same,
    orientedSum_add_one, update_eq_self, add_sub_cancel_left]

/-- `lineSum j` is a left inverse of `Δ_[e j]` up to the value on the hyperplane `x j = 0`. -/
theorem lineSum_fwdDiff_self (j : ι) (U : (ι → ℤ) → M) (x : ι → ℤ) :
    lineSum j (fwdDiff (Pi.single j 1) U) x = U x - U (update x j 0) := by
  have h : (fun t ↦ fwdDiff (Pi.single j 1) U (update x j t)) =
      fwdDiff 1 (fun t ↦ U (update x j t)) := by
    ext t
    simp [fwdDiff, update_add_single_self]
  rw [lineSum, h, orientedSum_fwdDiff, update_eq_self]

/-- `lineSum j` commutes with the differences in the other directions. -/
theorem lineSum_fwdDiff_of_ne {i j : ι} (h : i ≠ j) (U : (ι → ℤ) → M) :
    lineSum j (fwdDiff (Pi.single i 1) U) = fwdDiff (Pi.single i 1) (lineSum j U) := by
  ext x
  simp only [lineSum, fwdDiff, Pi.add_apply, Pi.single_apply, ite_eq_right h.symm, add_zero,
    update_add_single_of_ne x h, orientedSum_sub]

theorem lineSum_add (j : ι) (U V : (ι → ℤ) → M) (x : ι → ℤ) :
    lineSum j (U + V) x = lineSum j U x + lineSum j V x :=
  orientedSum_add _ _ _

theorem lineSum_smul {S : Type*} [Monoid S] [DistribMulAction S M] (j : ι) (c : S)
    (U : (ι → ℤ) → M) (x : ι → ℤ) : lineSum j (c • U) x = c • lineSum j U x :=
  orientedSum_smul _ _ _

theorem map_lineSum {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (L : F) (j : ι)
    (U : (ι → ℤ) → M) (x : ι → ℤ) : L (lineSum j U x) = lineSum j (fun y ↦ L (U y)) x :=
  map_orientedSum _ _ _

theorem lineSum_sum {α : Type*} (s : Finset α) (j : ι) (U : α → (ι → ℤ) → M) (x : ι → ℤ) :
    lineSum j (fun y ↦ ∑ a ∈ s, U a y) x = ∑ a ∈ s, lineSum j (U a) x :=
  orientedSum_sum _ _ _

end LineSum

/-! ### The contracting homotopy -/

variable {ι R : Type*} [LinearOrder ι] [CommRing R]

/-- `e_j* ⌟ (e_j ∧ f)` is the part of `f` without `e_j`. -/
theorem contract_wedge_self_apply (j : ι) (f : Finset ι → R) (I : Finset ι) :
    contract j (wedge j f) I = if j ∈ I then 0 else f I := by
  by_cases h : j ∈ I
  · simp [contract_apply, h]
  · rw [contract_apply, ite_eq_right h, ite_eq_right h, wedge_apply,
      ite_eq_left (mem_insert_self j I), erase_insert h, ← mul_assoc,
      neg_one_pow_card_filter_insert h, ite_eq_right (lt_irrefl j), ← pow_add, ← two_mul,
      pow_mul]
    simp

/-- The retraction of the `j`-th direction: the components without `e_j`, restricted to the
hyperplane `x j = 0` and extended constantly along `e j`. -/
def lineRetraction (j : ι) : ((ι → ℤ) → Finset ι → R) →ₗ[R] (ι → ℤ) → Finset ι → R where
  toFun U x I := if j ∈ I then 0 else U (update x j 0) I
  map_add' U V := by ext x I; by_cases h : j ∈ I <;> simp [h]
  map_smul' c U := by ext x I; by_cases h : j ∈ I <;> simp [h]

theorem lineRetraction_apply (j : ι) (U : (ι → ℤ) → Finset ι → R) (x : ι → ℤ) (I : Finset ι) :
    lineRetraction j U x I = if j ∈ I then 0 else U (update x j 0) I :=
  rfl

/-- The contracting homotopy of the `j`-th direction, `h_j U x = e_j* ⌟ lineSum j U x`. -/
def lineHomotopy (j : ι) : ((ι → ℤ) → Finset ι → R) →ₗ[R] (ι → ℤ) → Finset ι → R where
  toFun U x := contract j (lineSum j U x)
  map_add' U V := by ext x : 1; simp [lineSum_add]
  map_smul' c U := by ext x : 1; simp [lineSum_smul]

theorem lineHomotopy_apply (j : ι) (U : (ι → ℤ) → Finset ι → R) (x : ι → ℤ) :
    lineHomotopy j U x = contract j (lineSum j U x) :=
  rfl

variable [Fintype ι]

/-- **The homotopy formula of the `j`-th direction**: `d h_j + h_j d = 1 - r_j`. -/
theorem totalCoboundary_lineHomotopy_add_lineHomotopy_totalCoboundary (j : ι)
    (U : (ι → ℤ) → Finset ι → R) :
    totalCoboundary (fun i ↦ Pi.single i 1) (lineHomotopy j U) +
        lineHomotopy j (totalCoboundary (fun i ↦ Pi.single i 1) U) =
      U - lineRetraction j U := by
  ext x : 1
  have h₁ : ∀ i, fwdDiff (Pi.single i 1) (lineHomotopy j U) x =
      contract j (fwdDiff (Pi.single i 1) (lineSum j U) x) := fun i ↦
    (map_sub (contract j) _ _).symm
  have h₂ : lineHomotopy j (totalCoboundary (fun i ↦ Pi.single i 1) U) x =
      ∑ i, contract j (wedge i (lineSum j (fwdDiff (Pi.single i 1) U) x)) := by
    have hD : totalCoboundary (fun i ↦ Pi.single i 1) U =
        fun y ↦ ∑ i, wedge i (fwdDiff (Pi.single i 1) U y) :=
      funext (totalCoboundary_apply' _ U)
    rw [lineHomotopy_apply, hD, lineSum_sum, map_sum]
    simp only [← map_lineSum]
  simp only [Pi.add_apply, Pi.sub_apply, totalCoboundary_apply', h₁, h₂, ← sum_add_distrib]
  rw [sum_eq_single j]
  · have hCAR := contract_wedge_add_wedge_contract j j (U x)
    rw [ite_eq_left rfl] at hCAR
    rw [fwdDiff_lineSum, lineSum_fwdDiff_self, map_sub, map_sub]
    ext I
    have hI := congrFun hCAR I
    simp only [Pi.add_apply, Pi.sub_apply] at hI ⊢
    rw [lineRetraction_apply, ← contract_wedge_self_apply]
    linear_combination hI
  · intro i _ hij
    rw [lineSum_fwdDiff_of_ne hij, add_comm, contract_wedge_add_wedge_contract,
      ite_eq_right hij.symm]
  · simp

/-- Composing the homotopies of the directions in `T`: a closed total cochain is a coboundary
plus its components without directions in `T`, restricted to `x_T = 0`. -/
theorem exists_eq_totalCoboundary_add_of_finset (T : Finset ι) {U : (ι → ℤ) → Finset ι → R}
    (hU : totalCoboundary (fun i ↦ Pi.single i 1) U = 0) :
    ∃ V, U = totalCoboundary (fun i ↦ Pi.single i 1) V + fun x I ↦
      if ∀ j ∈ T, j ∉ I then U (fun i ↦ if i ∈ T then 0 else x i) I else 0 := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    ext x I
    simp
  | insert j T hj ih =>
    obtain ⟨V, hV⟩ := ih
    set W : (ι → ℤ) → Finset ι → R :=
      fun x I ↦ if ∀ j ∈ T, j ∉ I then U (fun i ↦ if i ∈ T then 0 else x i) I else 0 with hW
    have hWc : totalCoboundary (fun i ↦ Pi.single i 1) W = 0 := by
      have : W = U - totalCoboundary (fun i ↦ Pi.single i 1) V := by
        rw [hV]
        abel
      rw [this, map_sub, hU, totalCoboundary_totalCoboundary, sub_zero]
    have hh := totalCoboundary_lineHomotopy_add_lineHomotopy_totalCoboundary j W
    rw [hWc, map_zero, add_zero] at hh
    have hr : lineRetraction j W = fun x I ↦
        if ∀ l ∈ insert j T, l ∉ I then U (fun i ↦ if i ∈ insert j T then 0 else x i) I
        else 0 := by
      ext x I
      rw [lineRetraction_apply]
      by_cases hjI : j ∈ I
      · simp [hjI]
      · have hx : (fun i ↦ if i ∈ T then 0 else update x j 0 i) =
            fun i ↦ if i ∈ insert j T then 0 else x i := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp [hj]
          · simp [hij]
        simp only [hjI, ite_false, forall_mem_insert, not_false_eq_true, true_and, hW, hx]
    refine ⟨V + lineHomotopy j W, ?_⟩
    rw [map_add, hh, ← hr]
    conv_lhs => rw [hV]
    abel

/-- **Contracting homotopy of `ℤᵈ`**: a closed total cochain is a coboundary plus its constant
degree-`0` part at the origin. -/
theorem exists_eq_totalCoboundary_add {U : (ι → ℤ) → Finset ι → R}
    (hU : totalCoboundary (fun i ↦ Pi.single i 1) U = 0) :
    ∃ V, U = totalCoboundary (fun i ↦ Pi.single i 1) V +
      fun _ I ↦ if I = ∅ then U 0 ∅ else 0 := by
  obtain ⟨V, hV⟩ := exists_eq_totalCoboundary_add_of_finset univ hU
  refine ⟨V, hV.trans (congrArg _ ?_)⟩
  ext x I
  by_cases hI : I = ∅
  · subst hI
    simp only [notMem_empty, not_false_eq_true, implies_true, ite_true, mem_univ]
    rfl
  · have h : ¬∀ j ∈ univ, j ∉ I := fun h ↦
      hI (eq_empty_of_forall_notMem fun j ↦ h j (mem_univ j))
    simp only [h, hI, ite_false]

/-! ### The Poincaré lemma -/

variable {k : ℕ}

/-- **Poincaré lemma on `ℤᵈ`**: a closed `(k + 1)`-cochain is exact. -/
theorem exists_coboundary_eq {u : CubicalCell (ι → ℤ) ι (k + 1) → R}
    (hu : coboundary (fun i ↦ Pi.single i 1) (k + 1) u = 0) :
    ∃ v, coboundary (fun i ↦ Pi.single i 1) k v = u := by
  have hU : totalCoboundary (fun i ↦ Pi.single i 1) (extend (k + 1) u) = 0 := by
    rw [← extend_coboundary, hu, map_zero]
  obtain ⟨V, hV⟩ := exists_eq_totalCoboundary_add hU
  have h0 : extend (k + 1) u 0 ∅ = 0 := extend_apply_of_card_ne _ _ (by simp)
  have hV' : extend (k + 1) u = totalCoboundary (fun i ↦ Pi.single i 1) V := by
    conv_lhs => rw [hV]
    ext x I
    simp [h0]
  exact ⟨restrict k V, by rw [← restrict_totalCoboundary, ← hV', restrict_extend]⟩

variable (R) in
/-- **`H^{k+1}(ℤᵈ; R) = 0`**: closed cochains of positive degree are exact. -/
theorem cocycles_le_coboundaries_succ :
    cocycles R (fun i : ι ↦ (Pi.single i 1 : ι → ℤ)) (k + 1) ≤
      coboundaries R (fun i ↦ Pi.single i 1) (k + 1) :=
  fun _ hu ↦ LinearMap.mem_range.2 (exists_coboundary_eq hu)

instance subsingleton_cohomology_succ :
    Subsingleton (cohomology R (fun i : ι ↦ (Pi.single i 1 : ι → ℤ)) (k + 1)) :=
  subsingleton_cohomology_iff.2 (cocycles_le_coboundaries_succ R)

variable (R) in
/-- The cubical cochain complex of `ℤᵈ` is exact in every positive degree. -/
theorem exactAt_cochainComplex_succ :
    (cochainComplex R (fun i : ι ↦ (Pi.single i 1 : ι → ℤ))).ExactAt (k + 1) :=
  exactAt_cochainComplex_succ_iff.2 (cocycles_le_coboundaries_succ R)

omit [LinearOrder ι] [Fintype ι] in
/-- The unit steps generate `ℤᵈ`; hence `H⁰(ℤᵈ; R) ≃ R` (`cohomologyZeroEquiv`). -/
theorem closure_range_single_int [Finite ι] [DecidableEq ι] :
    AddSubgroup.closure (Set.range fun i : ι ↦ (Pi.single i 1 : ι → ℤ)) = ⊤ :=
  closure_range_single_one fun _ n ↦ ⟨n, Int.cast_id⟩

end CubicalCochain

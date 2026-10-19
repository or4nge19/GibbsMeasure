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
public import Mathlib.GroupTheory.QuotientGroup.Defs

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
For `h_j U x = e_j* ⌟ lineSum j U x` the homotopy formula of one direction
(`totalCoboundary_contract_add_contract_totalCoboundary`) gives
`d h_j + h_j d = 1 - r_j` (`totalCoboundary_contract_lineSum_add`), where
`r_j U x I = [j ∉ I] U (x with x j := 0) I` keeps the components without `e_j`, restricted to
`x j = 0` and extended constantly along `e j`. Composing over all
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
* `closure_range_single_int`, `closure_range_mk_single_int`: the unit steps generate `ℤᵈ` and
  every torus `ℤᵈ ⧸ Γ`, so `H⁰ ≃ R` there is `cohomologyZeroEquiv` of these.
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
def lineSum (j : ι) : ((ι → ℤ) → M) →+ (ι → ℤ) → M where
  toFun U x := orientedSum (fun t ↦ U (update x j t)) (x j)
  map_zero' := by ext x; simp [orientedSum]
  map_add' U V := by ext x; exact orientedSum_add _ _ _

theorem lineSum_apply (j : ι) (U : (ι → ℤ) → M) (x : ι → ℤ) :
    lineSum j U x = orientedSum (fun t ↦ U (update x j t)) (x j) :=
  rfl

/-- `lineSum j` is a right inverse of the difference `Δ_[e j]`. -/
theorem fwdDiff_lineSum (j : ι) (U : (ι → ℤ) → M) :
    fwdDiff (Pi.single j 1) (lineSum j U) = U := by
  ext x
  simp only [fwdDiff, lineSum_apply, update_add_single_left_self, Pi.add_apply,
    Pi.single_eq_same, orientedSum_add_one, update_eq_self, add_sub_cancel_left]

/-- `lineSum j` is a left inverse of `Δ_[e j]` up to the value on the hyperplane `x j = 0`. -/
theorem lineSum_fwdDiff_self (j : ι) (U : (ι → ℤ) → M) (x : ι → ℤ) :
    lineSum j (fwdDiff (Pi.single j 1) U) x = U x - U (update x j 0) := by
  have h : (fun t ↦ fwdDiff (Pi.single j 1) U (update x j t)) =
      fwdDiff 1 (fun t ↦ U (update x j t)) := by
    ext t
    simp [fwdDiff, update_add_single_self]
  rw [lineSum_apply, h, orientedSum_fwdDiff, update_eq_self]

/-- `lineSum j` commutes with the differences in the other directions. -/
theorem lineSum_fwdDiff_of_ne {i j : ι} (h : i ≠ j) (U : (ι → ℤ) → M) :
    lineSum j (fwdDiff (Pi.single i 1) U) = fwdDiff (Pi.single i 1) (lineSum j U) := by
  ext x
  simp only [lineSum_apply, fwdDiff, Pi.add_apply, Pi.single_apply, ite_eq_right h.symm,
    add_zero, update_add_single_of_ne x h, orientedSum_sub]

theorem map_lineSum {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (L : F) (j : ι)
    (U : (ι → ℤ) → M) (x : ι → ℤ) : L (lineSum j U x) = lineSum j (fun y ↦ L (U y)) x :=
  map_orientedSum _ _ _

end LineSum

/-! ### The contracting homotopy -/

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R]

/-- **The homotopy formula of the `j`-th direction of `ℤᵈ`**: for `h_j U x = e_j* ⌟ lineSum j U x`,
`d h_j + h_j d = 1 - r_j`, where `r_j U x = e_j* ⌟ e_j ∧ U (x with x j := 0)` keeps the components
without `e_j`, restricted to the hyperplane `x j = 0` and extended constantly along `e j`. -/
theorem totalCoboundary_contract_lineSum_add (j : ι) (U : (ι → ℤ) → Finset ι → R) :
    totalCoboundary (fun i ↦ Pi.single i 1) (fun x ↦ contract j (lineSum j U x)) +
        (fun x ↦ contract j (lineSum j (totalCoboundary (fun i ↦ Pi.single i 1) U) x)) =
      U - fun x ↦ contract j (wedge j (U (update x j 0))) := by
  have h := totalCoboundary_contract_add_contract_totalCoboundary (e := fun i ↦ Pi.single i 1) j
    (lineSum j) (fun U x ↦ U (update x j 0)) (fun _ ↦ 0)
    (fun L U ↦ funext fun x ↦ (map_lineSum L j U x).symm)
    (fun U ↦ (fwdDiff_lineSum j U).trans (sub_zero U).symm)
    (fun U ↦ funext fun x ↦ lineSum_fwdDiff_self j U x)
    (fun i hij U ↦ lineSum_fwdDiff_of_ne hij U) U
  rw [h]
  congr 1
  ext x : 1
  simp

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
    have hh : totalCoboundary (fun i ↦ Pi.single i 1) (fun x ↦ contract j (lineSum j W x)) =
        W - fun x ↦ contract j (wedge j (W (update x j 0))) := by
      rw [← totalCoboundary_contract_lineSum_add j W, hWc]
      ext x : 1
      simp
    have hr : (fun x ↦ contract j (wedge j (W (update x j 0)))) = fun x I ↦
        if ∀ l ∈ insert j T, l ∉ I then U (fun i ↦ if i ∈ insert j T then 0 else x i) I
        else 0 := by
      ext x I
      rw [contract_wedge_self_apply]
      by_cases hjI : j ∈ I
      · simp [hjI]
      · have hx : (fun i ↦ if i ∈ T then 0 else update x j 0 i) =
            fun i ↦ if i ∈ insert j T then 0 else x i := by
          ext i
          rcases eq_or_ne i j with rfl | hij
          · simp [hj]
          · simp [hij]
        simp only [hjI, ite_false, forall_mem_insert, not_false_eq_true, true_and, hW, hx]
    refine ⟨V + fun x ↦ contract j (lineSum j W x), ?_⟩
    rw [map_add, hh, hr]
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

omit [LinearOrder ι] [Fintype ι] in
/-- The images of the unit steps generate every torus `ℤᵈ ⧸ Γ`; hence `H⁰(ℤᵈ ⧸ Γ; R) ≃ R`
(`cohomologyZeroEquiv`). -/
theorem closure_range_mk_single_int [Finite ι] [DecidableEq ι] (Γ : AddSubgroup (ι → ℤ)) :
    AddSubgroup.closure
      (Set.range fun i : ι ↦ (QuotientAddGroup.mk (Pi.single i 1) : (ι → ℤ) ⧸ Γ)) = ⊤ :=
  closure_range_comp (QuotientAddGroup.mk' Γ) (QuotientAddGroup.mk'_surjective Γ)
    closure_range_single_int

end CubicalCochain

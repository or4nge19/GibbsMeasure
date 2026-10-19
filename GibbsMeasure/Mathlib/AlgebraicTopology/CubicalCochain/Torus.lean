/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Cohomology
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cohomology of the product tori

Let `X = ∀ i, ZMod (n i)`, `n i ≥ 1`, with the unit steps `Pi.single i 1`: the cubical torus
`∏ ℤ/nᵢ`, e.g. the cubic torus `(ℤ/N)ᵈ` and the coordinate tori `C(n₁, n₂, n₃)` of [Q], [M].
Its cohomology with coefficients in any commutative ring `R` is free, with one generator for
each coordinate subtorus: `H^k ≃ (Set.powersetCard ι k → R)` (`cohomologyEquiv`), the coordinate
space of `⋀^k Rᵈ` in the basis `e_I` (`Module.Basis.exteriorPower` is indexed by the same
`Set.powersetCard ι k`).

The class of a closed `k`-cochain `u` is read off from its *periods* `periods x u I`, the sums of
`u` over the coordinate `I`-torus `{y | y i = x i for i ∉ I}` (`#I = k`); for a closed cochain
they do not depend on `x` (`periods_eq_of_mem_cocycles`), and they vanish on exact cochains
(`periods_coboundary`). The *seam cochain* `seam c` is `c I` on the cells `y + [0,1]^I` with
`y i = -1` for all `i ∈ I`, the cells crossing the seams `-1 → 0`, and `0` elsewhere; it is
closed with periods `c` (`coboundary_seam`, `periods_seam`). Every closed cochain is exact plus
the seam cochain of its periods (`sub_seam_periods_mem_coboundaries`,
`exists_eq_coboundary_add_seam`); hence it is exact if and only if its periods vanish
(`mem_coboundaries_iff_periods_eq_zero`).

For `R = ℤ`, `ι = Fin 3`, these are [Q] (20.6) and (20.7): a closed integer two-cochain `z` has an
integer primitive if and only if its fluxes `w_μν(z)` through the coordinate two-tori vanish (and
`w_μν(z)` does not depend on the transverse coordinate); a closed integer one-cochain is
`dλ + ∑_μ j_μ k^(μ)`, with the seam cochains `k^(μ)_ν(c) = δ_μν 1{c_μ = n_μ - 1}` of (20.4).

The proof is the homotopy formula of one direction
(`totalCoboundary_contract_add_contract_totalCoboundary`) with the cyclic line sum
`torusLineSum j U x = ∑_{t=0}^{x j - 1} U (x with x j := t)`, `x j` read in `[0, n j)`, which
inverts `Δ_[e j]` except on the seam `x j = -1`, where it subtracts the line total
(`fwdDiff_torusLineSum`). Composing over all directions, a closed total cochain is a coboundary
plus the seam cochain of its periods (`exists_eq_totalCoboundary_add_seam`).
-/

@[expose] public section

open Finset Function

namespace CubicalCochain

open CubicalCell

/-! ### Cyclic sums -/

section CyclicSum

variable {M : Type*} [AddCommGroup M] {N : ℕ}

theorem sum_range_natCast_zmod [NeZero N] (g : ZMod N → M) : ∑ s ∈ range N, g s = ∑ s, g s :=
  sum_nbij' (fun s ↦ (s : ZMod N)) ZMod.val (fun _ _ ↦ mem_univ _)
    (fun a _ ↦ mem_range.2 (ZMod.val_lt a)) (fun _ h ↦ ZMod.val_natCast_of_lt (mem_range.1 h))
    (fun a _ ↦ ZMod.natCast_zmod_val a) (fun _ _ ↦ rfl)

/-- The sum `∑_{s=0}^{t-1} g s` along `ZMod N`, `t` read in `[0, N)`. -/
def cyclicSum (g : ZMod N → M) (t : ZMod N) : M :=
  ∑ s ∈ range t.val, g s

@[simp]
theorem cyclicSum_zero (g : ZMod N → M) : cyclicSum g 0 = 0 := by
  simp [cyclicSum]

/-- The cyclic sum inverts the difference except at the seam `t = -1`, where it subtracts the
total. -/
theorem fwdDiff_cyclicSum [NeZero N] (g : ZMod N → M) (t : ZMod N) :
    fwdDiff 1 (cyclicSum g) t = g t - if t = -1 then ∑ s, g s else 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, (Nat.sub_add_cancel NeZero.one_le).symm⟩
  rw [fwdDiff]
  by_cases ht : t = -1
  · subst ht
    have hm : ((m : ℕ) : ZMod (m + 1)) = -1 := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_succ, ZMod.natCast_self]
    rw [ite_eq_left rfl, neg_add_cancel, cyclicSum_zero, cyclicSum, ZMod.val_neg_one,
      ← sum_range_natCast_zmod, sum_range_succ, hm]
    abel
  · have hlt : t.val + 1 < m + 1 := by
      have h1 := ZMod.val_lt t
      have h2 : t.val ≠ m := fun h ↦ ht (ZMod.val_injective _ (h.trans (ZMod.val_neg_one m).symm))
      omega
    have hv : (t + 1).val = t.val + 1 := by
      have : t + 1 = ((t.val + 1 : ℕ) : ZMod (m + 1)) := by
        rw [Nat.cast_succ, ZMod.natCast_zmod_val]
      rw [this, ZMod.val_natCast_of_lt hlt]
    rw [ite_eq_right ht, cyclicSum, cyclicSum, hv, sum_range_succ, ZMod.natCast_zmod_val]
    abel

/-- The cyclic sum of a difference telescopes. -/
theorem cyclicSum_fwdDiff [NeZero N] (g : ZMod N → M) (t : ZMod N) :
    cyclicSum (fwdDiff 1 g) t = g t - g 0 := by
  have h := sum_range_sub (fun s : ℕ ↦ g s) t.val
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, ZMod.natCast_zmod_val] at h
  simpa [cyclicSum, fwdDiff] using h

end CyclicSum

/-! ### Cyclic sums along coordinate circles -/

section TorusLineSum

variable {ι M M' : Type*} [DecidableEq ι] {n : ι → ℕ} [AddCommGroup M] [AddCommGroup M']

/-- Summation along the `j`-th coordinate circle from the hyperplane `x j = 0`:
`torusLineSum j U x = ∑_{t=0}^{x j - 1} U (x with x j := t)`, `x j` read in `[0, n j)`. -/
def torusLineSum (j : ι) : ((∀ i, ZMod (n i)) → M) →+ (∀ i, ZMod (n i)) → M where
  toFun U x := cyclicSum (fun t ↦ U (update x j t)) (x j)
  map_zero' := by ext x; simp [cyclicSum]
  map_add' U V := by ext x; simp [cyclicSum, sum_add_distrib]

theorem torusLineSum_apply (j : ι) (U : (∀ i, ZMod (n i)) → M) (x : ∀ i, ZMod (n i)) :
    torusLineSum j U x = cyclicSum (fun t ↦ U (update x j t)) (x j) :=
  rfl

/-- `torusLineSum j` inverts `Δ_[e j]` except on the seam `x j = -1`, where it subtracts the
total over the circle through `x`. -/
theorem fwdDiff_torusLineSum [∀ i, NeZero (n i)] (j : ι) (U : (∀ i, ZMod (n i)) → M)
    (x : ∀ i, ZMod (n i)) :
    fwdDiff (Pi.single j 1) (torusLineSum j U) x =
      U x - if x j = -1 then ∑ t, U (update x j t) else 0 := by
  have h := fwdDiff_cyclicSum (fun t ↦ U (update x j t)) (x j)
  rw [fwdDiff, update_eq_self] at h
  simp only [fwdDiff, torusLineSum_apply, update_add_single_left_self, Pi.add_apply,
    Pi.single_eq_same, h]

/-- `torusLineSum j` is a left inverse of `Δ_[e j]` up to the value on `x j = 0`. -/
theorem torusLineSum_fwdDiff_self [∀ i, NeZero (n i)] (j : ι) (U : (∀ i, ZMod (n i)) → M)
    (x : ∀ i, ZMod (n i)) :
    torusLineSum j (fwdDiff (Pi.single j 1) U) x = U x - U (update x j 0) := by
  have h : (fun t ↦ fwdDiff (Pi.single j 1) U (update x j t)) =
      fwdDiff 1 (fun t ↦ U (update x j t)) := by
    ext t
    simp [fwdDiff, update_add_single_self]
  rw [torusLineSum_apply, h, cyclicSum_fwdDiff, update_eq_self]

/-- `torusLineSum j` commutes with the differences in the other directions. -/
theorem torusLineSum_fwdDiff_of_ne {i j : ι} (h : i ≠ j) (U : (∀ i, ZMod (n i)) → M) :
    torusLineSum j (fwdDiff (Pi.single i 1) U) = fwdDiff (Pi.single i 1) (torusLineSum j U) := by
  ext x
  simp only [torusLineSum_apply, fwdDiff, Pi.add_apply, Pi.single_eq_of_ne h.symm, add_zero,
    update_add_single_of_ne x h, cyclicSum, sum_sub_distrib]

theorem map_torusLineSum {F : Type*} [FunLike F M M'] [AddMonoidHomClass F M M'] (L : F) (j : ι)
    (U : (∀ i, ZMod (n i)) → M) (x : ∀ i, ZMod (n i)) :
    L (torusLineSum j U x) = torusLineSum j (fun y ↦ L (U y)) x := by
  simp only [torusLineSum_apply, cyclicSum, map_sum]

end TorusLineSum

/-- The unit steps generate the product torus; hence `H⁰ ≃ R` (`cohomologyZeroEquiv`). -/
theorem closure_range_single_zmod {ι : Type*} [Finite ι] [DecidableEq ι] (n : ι → ℕ) :
    AddSubgroup.closure (Set.range fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) = ⊤ :=
  closure_range_single_one fun _ ↦ ZMod.intCast_surjective

/-! ### The contracting homotopy of the torus -/

variable {ι R : Type*} [LinearOrder ι] [Fintype ι] [CommRing R] {n : ι → ℕ}
  [∀ i, NeZero (n i)]

/-- **The homotopy formula of the `j`-th direction of the torus**: for
`h_j U x = e_j* ⌟ torusLineSum j U x`, `d h_j + h_j d = 1 - r_j` with
`r_j U x = e_j* ⌟ e_j ∧ U (x with x j := 0) + e_j ∧ e_j* ⌟ [x j = -1] ∑_t U (x with x j := t)`. -/
theorem totalCoboundary_contract_torusLineSum_add (j : ι)
    (U : (∀ i, ZMod (n i)) → Finset ι → R) :
    totalCoboundary (fun i ↦ Pi.single i 1) (fun x ↦ contract j (torusLineSum j U x)) +
        (fun x ↦ contract j (torusLineSum j (totalCoboundary (fun i ↦ Pi.single i 1) U) x)) =
      U - fun x ↦ contract j (wedge j (U (update x j 0))) +
        wedge j (contract j (if x j = -1 then ∑ t, U (update x j t) else 0)) := by
  have hS : ∀ (L : (Finset ι → R) →ₗ[R] Finset ι → R) (U : (∀ i, ZMod (n i)) → Finset ι → R),
      torusLineSum j (fun y ↦ L (U y)) = fun x ↦ L (torusLineSum j U x) := fun L U ↦
    funext fun x ↦ (map_torusLineSum L j U x).symm
  have hright : ∀ U : (∀ i, ZMod (n i)) → Finset ι → R,
      fwdDiff (Pi.single j 1) (torusLineSum j U) =
        U - fun x ↦ if x j = -1 then ∑ t, U (update x j t) else 0 := fun U ↦
    funext fun x ↦ fwdDiff_torusLineSum j U x
  have hleft : ∀ U : (∀ i, ZMod (n i)) → Finset ι → R,
      torusLineSum j (fwdDiff (Pi.single j 1) U) = U - fun x ↦ U (update x j 0) := fun U ↦
    funext fun x ↦ torusLineSum_fwdDiff_self j U x
  -- `convert` instead of `exact`: the unifier otherwise unfolds the `ZMod (n i)` instances
  have h := totalCoboundary_contract_add_contract_totalCoboundary (X := ∀ i, ZMod (n i)) (R := R)
    (e := fun i ↦ Pi.single i 1) j (torusLineSum j) (fun U x ↦ U (update x j 0))
    (fun U x ↦ if x j = -1 then ∑ t, U (update x j t) else 0) hS hright hleft
    (fun i hij U ↦ torusLineSum_fwdDiff_of_ne hij U) U
  convert h using 1

/-- For `j ∉ T` and `j ∈ I`: the points that agree with `x` (its `j`-th coordinate moved to `t`)
off `T` and vanish on `T ∖ I` are the fibre over `t` of `y ↦ y j` among the points that agree
with `x` off `insert j T` and vanish on `insert j T ∖ I`. -/
theorem filter_update_eq_filter (T I : Finset ι) {j : ι} (hj : j ∉ T) (hjI : j ∈ I)
    (x : ∀ i, ZMod (n i)) (t : ZMod (n j)) :
    univ.filter (fun y : ∀ i, ZMod (n i) ↦
        ∀ i, (i ∉ T → y i = update x j t i) ∧ (i ∈ T → i ∉ I → y i = 0)) =
      (univ.filter fun y : ∀ i, ZMod (n i) ↦
        ∀ i, (i ∉ insert j T → y i = x i) ∧ (i ∈ insert j T → i ∉ I → y i = 0)).filter
          fun y ↦ y j = t := by
  ext y
  simp only [mem_filter, mem_univ, true_and, mem_insert, not_or]
  constructor
  · intro h
    refine ⟨fun i ↦ ⟨fun hi ↦ ?_, fun hi hiI ↦ ?_⟩, ?_⟩
    · rw [(h i).1 hi.2, update_of_ne hi.1]
    · rcases hi with rfl | hi
      · exact absurd hjI hiI
      · exact (h i).2 hi hiI
    · rw [(h j).1 hj, update_self]
  · rintro ⟨h, rfl⟩
    refine fun i ↦ ⟨fun hi ↦ ?_, fun hi hiI ↦ (h i).2 (Or.inr hi) hiI⟩
    rcases eq_or_ne i j with rfl | hij
    · rw [update_self]
    · rw [update_of_ne hij, (h i).1 ⟨hij, hi⟩]

/-- Composing the homotopies of the directions in `T`: a closed total cochain is a coboundary
plus, at `x`, the sum of its values over the points agreeing with `x` off `T` and vanishing on
`T ∖ I`, when `x i = -1` for all `i ∈ T ∩ I`, and `0` otherwise. -/
theorem exists_eq_totalCoboundary_add_of_finset_torus (T : Finset ι)
    {U : (∀ i, ZMod (n i)) → Finset ι → R}
    (hU : totalCoboundary (fun i ↦ Pi.single i 1) U = 0) :
    ∃ V, U = totalCoboundary (fun i ↦ Pi.single i 1) V + fun x I ↦
      if ∀ l ∈ T, l ∈ I → x l = -1 then
        ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦
          ∀ i, (i ∉ T → y i = x i) ∧ (i ∈ T → i ∉ I → y i = 0)), U y I
      else 0 := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    ext x I
    have h : univ.filter (fun y : ∀ i, ZMod (n i) ↦ ∀ i, y i = x i) = {x} := by
      ext y
      simp [funext_iff]
    simp [h]
  | insert j T hj ih =>
    obtain ⟨V, hV⟩ := ih
    set W : (∀ i, ZMod (n i)) → Finset ι → R := fun x I ↦
      if ∀ l ∈ T, l ∈ I → x l = -1 then
        ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦
          ∀ i, (i ∉ T → y i = x i) ∧ (i ∈ T → i ∉ I → y i = 0)), U y I
      else 0 with hW
    have hWc : totalCoboundary (fun i ↦ Pi.single i 1) W = 0 := by
      have : W = U - totalCoboundary (fun i ↦ Pi.single i 1) V := by
        rw [hV]
        abel
      rw [this, map_sub, hU, totalCoboundary_totalCoboundary, sub_zero]
    have hh : totalCoboundary (fun i ↦ Pi.single i 1)
        (fun x ↦ contract j (torusLineSum j W x)) =
        W - fun x ↦ contract j (wedge j (W (update x j 0))) +
          wedge j (contract j (if x j = -1 then ∑ t, W (update x j t) else 0)) := by
      rw [← totalCoboundary_contract_torusLineSum_add j W, hWc]
      ext x : 1
      simp
    have hT : ∀ (z : ∀ i, ZMod (n i)) (I : Finset ι),
        (∀ l ∈ T, l ∈ I → update z j 0 l = -1) ↔ ∀ l ∈ T, l ∈ I → z l = -1 := fun z I ↦
      forall₂_congr fun l hl ↦ by rw [update_of_ne (ne_of_mem_of_not_mem hl hj)]
    have hr : (fun x ↦ contract j (wedge j (W (update x j 0))) +
        wedge j (contract j (if x j = -1 then ∑ t, W (update x j t) else 0))) = fun x I ↦
          if ∀ l ∈ insert j T, l ∈ I → x l = -1 then
            ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦
              ∀ i, (i ∉ insert j T → y i = x i) ∧ (i ∈ insert j T → i ∉ I → y i = 0)), U y I
          else 0 := by
      ext x I
      rw [Pi.add_apply, contract_wedge_self_apply, wedge_contract_self_apply]
      by_cases hjI : j ∈ I
      · have hcond : (∀ l ∈ insert j T, l ∈ I → x l = -1) ↔
            x j = -1 ∧ ∀ l ∈ T, l ∈ I → x l = -1 := by
          simp [hjI]
        have hC : ∀ t : ZMod (n j), (∀ l ∈ T, l ∈ I → update x j t l = -1) ↔
            ∀ l ∈ T, l ∈ I → x l = -1 := fun t ↦
          forall₂_congr fun l hl ↦ by rw [update_of_ne (ne_of_mem_of_not_mem hl hj)]
        rw [ite_eq_left hjI, ite_eq_left hjI, zero_add]
        simp only [hcond]
        by_cases hx : x j = -1
        · rw [ite_eq_left hx, Finset.sum_apply]
          by_cases hCx : ∀ l ∈ T, l ∈ I → x l = -1
          · rw [ite_eq_left ⟨hx, hCx⟩, ← sum_fiberwise _ (fun y : ∀ i, ZMod (n i) ↦ y j)]
            refine sum_congr rfl fun t _ ↦ ?_
            rw [hW]
            dsimp only
            rw [ite_eq_left ((hC t).2 hCx), filter_update_eq_filter T I hj hjI x t]
          · rw [ite_eq_right fun h ↦ hCx h.2]
            refine sum_eq_zero fun t _ ↦ ?_
            rw [hW]
            dsimp only
            rw [ite_eq_right fun h ↦ hCx ((hC t).1 h)]
        · rw [ite_eq_right hx, ite_eq_right fun h ↦ hx h.1, Pi.zero_apply]
      · have hcond : (∀ l ∈ insert j T, l ∈ I → x l = -1) ↔
            ∀ l ∈ T, l ∈ I → update x j 0 l = -1 := by
          rw [hT x I]
          simp [hjI]
        have hF : univ.filter (fun y : ∀ i, ZMod (n i) ↦
            ∀ i, (i ∉ T → y i = update x j 0 i) ∧ (i ∈ T → i ∉ I → y i = 0)) =
            univ.filter (fun y : ∀ i, ZMod (n i) ↦
              ∀ i, (i ∉ insert j T → y i = x i) ∧ (i ∈ insert j T → i ∉ I → y i = 0)) := by
          refine filter_congr fun y _ ↦ forall_congr' fun i ↦ ?_
          rcases eq_or_ne i j with rfl | hij
          · simp [hj, hjI]
          · simp [hij]
        rw [ite_eq_right hjI, ite_eq_right hjI, add_zero]
        simp only [hcond]
        rw [hW]
        dsimp only
        rw [hF]
    refine ⟨V + fun x ↦ contract j (torusLineSum j W x), ?_⟩
    rw [map_add, hh, hr]
    conv_lhs => rw [hV]
    abel

/-- **Contracting homotopy of the torus**: a closed total cochain is a coboundary plus, on each
cell `x + [0,1]^I` with `x i = -1` for all `i ∈ I`, its total over the coordinate `I`-torus
through `0`. -/
theorem exists_eq_totalCoboundary_add_seam {U : (∀ i, ZMod (n i)) → Finset ι → R}
    (hU : totalCoboundary (fun i ↦ Pi.single i 1) U = 0) :
    ∃ V, U = totalCoboundary (fun i ↦ Pi.single i 1) V + fun x I ↦
      if ∀ l ∈ I, x l = -1 then
        ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦ ∀ i ∉ I, y i = 0), U y I
      else 0 := by
  obtain ⟨V, hV⟩ := exists_eq_totalCoboundary_add_of_finset_torus univ hU
  refine ⟨V, hV.trans (congrArg _ ?_)⟩
  ext x I
  simp only [mem_univ, not_true_eq_false, false_implies, true_and, true_implies]

/-! ### Periods and seam cochains -/

variable {k : ℕ}

/-- The periods of a `k`-cochain: its sums over the coordinate `I`-tori through `x`,
`{y | y i = x i for i ∉ I}`, for `#I = k`. For `k = 2` these are the fluxes through the
coordinate two-tori. -/
def periods (x : ∀ i, ZMod (n i)) :
    (CubicalCell (∀ i, ZMod (n i)) ι k → R) →ₗ[R] Set.powersetCard ι k → R where
  toFun u I := ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦ ∀ i ∉ (I : Finset ι), y i = x i),
    u ⟨y, I⟩
  map_add' u v := by ext I; simp [sum_add_distrib]
  map_smul' c u := by ext I; simp [mul_sum]

theorem periods_apply (x : ∀ i, ZMod (n i)) (u : CubicalCell (∀ i, ZMod (n i)) ι k → R)
    (I : Set.powersetCard ι k) :
    periods x u I = ∑ y ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦
      ∀ i ∉ (I : Finset ι), y i = x i), u ⟨y, I⟩ :=
  rfl

/-- The seam cochain of `c`: `c I` on the cells `y + [0,1]^I` with `y i = -1` for all `i ∈ I`,
which cross the seams `-1 → 0` of the directions in `I`, and `0` elsewhere. -/
def seam : (Set.powersetCard ι k → R) →ₗ[R] CubicalCell (∀ i, ZMod (n i)) ι k → R where
  toFun c σ := if ∀ i ∈ (σ.dirs : Finset ι), σ.site i = -1 then c σ.dirs else 0
  map_add' c c' := by
    ext σ
    by_cases h : ∀ i ∈ (σ.dirs : Finset ι), σ.site i = -1
    · simp only [Pi.add_apply, ite_eq_left h]
    · simp only [Pi.add_apply, ite_eq_right h, add_zero]
  map_smul' r c := by
    ext σ
    by_cases h : ∀ i ∈ (σ.dirs : Finset ι), σ.site i = -1
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ite_eq_left h]
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ite_eq_right h, mul_zero]

omit [∀ i, NeZero (n i)] in
theorem seam_apply (c : Set.powersetCard ι k → R) (σ : CubicalCell (∀ i, ZMod (n i)) ι k) :
    seam c σ = if ∀ i ∈ (σ.dirs : Finset ι), σ.site i = -1 then c σ.dirs else 0 :=
  rfl

omit [∀ i, NeZero (n i)] in
/-- A seam cochain is invariant under the steps transverse to the cell. -/
theorem seam_add_single (c : Set.powersetCard ι k → R) (x : ∀ i, ZMod (n i))
    (I : Set.powersetCard ι k) {j : ι} (hj : j ∉ (I : Finset ι)) :
    seam c ⟨x + Pi.single j 1, I⟩ = seam c ⟨x, I⟩ :=
  if_congr (forall₂_congr fun i hi ↦ by
    dsimp only
    rw [Pi.add_apply, Pi.single_eq_of_ne (ne_of_mem_of_not_mem hi hj), add_zero]) rfl rfl

omit [∀ i, NeZero (n i)] in
/-- **Seam cochains are closed.** -/
theorem coboundary_seam (c : Set.powersetCard ι k → R) :
    coboundary (fun i ↦ Pi.single i 1) k (seam (n := n) c) = 0 := by
  ext σ
  rw [coboundary_apply, Pi.zero_apply]
  refine sum_eq_zero fun j hj ↦ ?_
  have hc : #((σ.dirs : Finset ι).erase j) = k := by
    rw [card_erase_of_mem hj, Set.powersetCard.card_eq, Nat.add_sub_cancel]
  have hjc : j ∉ ((Set.powersetCard.ofCard hc : Set.powersetCard ι k) : Finset ι) := by
    simp
  rw [extend_apply_of_card_eq _ _ hc, extend_apply_of_card_eq _ _ hc, seam_add_single _ _ _ hjc,
    sub_self, mul_zero]

/-- **The periods of a seam cochain are its coefficients**, on every parallel subtorus. -/
theorem periods_seam (x : ∀ i, ZMod (n i)) (c : Set.powersetCard ι k → R) :
    periods x (seam c) = c := by
  ext I
  rw [periods_apply]
  let y₀ : ∀ i, ZMod (n i) := fun i ↦ if i ∈ (I : Finset ι) then -1 else x i
  have hy₀ : y₀ ∈ univ.filter (fun y : ∀ i, ZMod (n i) ↦ ∀ i ∉ (I : Finset ι), y i = x i) :=
    mem_filter.2 ⟨mem_univ _, fun i hi ↦ by simp [y₀, hi]⟩
  rw [sum_eq_single_of_mem y₀ hy₀]
  · exact ite_eq_left fun i hi ↦ ite_eq_left hi
  · intro y hy hne
    rw [seam_apply, ite_eq_right]
    intro h
    refine hne (funext fun i ↦ ?_)
    by_cases hi : i ∈ (I : Finset ι)
    · have hy₀i : y₀ i = -1 := ite_eq_left hi
      rw [hy₀i]
      exact h i hi
    · have hy₀i : y₀ i = x i := ite_eq_right hi
      rw [hy₀i]
      exact (mem_filter.1 hy).2 i hi

/-- **Exact cochains have vanishing periods**: translation along a direction of `I` preserves
the coordinate `I`-torus. -/
theorem periods_coboundary (x : ∀ i, ZMod (n i))
    (v : CubicalCell (∀ i, ZMod (n i)) ι k → R) :
    periods x (coboundary (fun i ↦ Pi.single i 1) k v) = 0 := by
  ext J
  simp only [periods_apply, coboundary_apply, Pi.zero_apply]
  rw [sum_comm]
  refine sum_eq_zero fun j hj ↦ ?_
  rw [← mul_sum, sum_sub_distrib, sub_eq_zero.2 ?_, mul_zero]
  refine sum_equiv (Equiv.addRight (Pi.single j 1)) (fun y ↦ ?_) fun _ _ ↦ rfl
  simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight, Pi.add_apply]
  refine forall₂_congr fun i hi ↦ ?_
  have hij : i ≠ j := fun h ↦ hi (h ▸ hj)
  rw [Pi.single_eq_of_ne hij, add_zero]

theorem periods_eq_zero_of_mem_coboundaries (x : ∀ i, ZMod (n i))
    {u : CubicalCell (∀ i, ZMod (n i)) ι k → R}
    (hu : u ∈ coboundaries R (fun i ↦ Pi.single i 1) k) : periods x u = 0 := by
  cases k with
  | zero =>
    rw [coboundaries_zero, Submodule.mem_bot] at hu
    rw [hu, map_zero]
  | succ k =>
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hu
    exact periods_coboundary x v

/-- **A closed cochain is exact plus the seam cochain of its periods.** -/
theorem sub_seam_periods_mem_coboundaries {u : CubicalCell (∀ i, ZMod (n i)) ι k → R}
    (hu : u ∈ cocycles R (fun i ↦ Pi.single i 1) k) :
    u - seam (periods 0 u) ∈ coboundaries R (fun i ↦ Pi.single i 1) k := by
  have hU : totalCoboundary (fun i ↦ Pi.single i 1) (extend k u) = 0 := by
    rw [← extend_coboundary, mem_cocycles_iff.1 hu, map_zero]
  obtain ⟨V, hV⟩ := exists_eq_totalCoboundary_add_seam hU
  have h : u - seam (periods 0 u) = restrict k (totalCoboundary (fun i ↦ Pi.single i 1) V) := by
    rw [sub_eq_iff_eq_add]
    ext c
    conv_lhs => rw [← restrict_extend u, hV]
    simp [seam_apply, periods_apply]
  rw [h]
  cases k with
  | zero => rw [restrict_zero_totalCoboundary]; exact zero_mem _
  | succ k => rw [restrict_totalCoboundary]; exact LinearMap.mem_range_self _ _

/-- **[Q] (20.7)**: a closed `(k + 1)`-cochain of the torus is `d v` plus the seam cochain of its
periods. -/
theorem exists_eq_coboundary_add_seam {u : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → R}
    (hu : coboundary (fun i ↦ Pi.single i 1) (k + 1) u = 0) :
    ∃ v : CubicalCell (∀ i, ZMod (n i)) ι k → R,
      u = coboundary (fun i ↦ Pi.single i 1) k v + seam (periods 0 u) := by
  obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (sub_seam_periods_mem_coboundaries hu)
  exact ⟨v, by rw [hv, sub_add_cancel]⟩

/-- **The periods of a closed cochain do not depend on the base point.** -/
theorem periods_eq_of_mem_cocycles {u : CubicalCell (∀ i, ZMod (n i)) ι k → R}
    (hu : u ∈ cocycles R (fun i ↦ Pi.single i 1) k) (x : ∀ i, ZMod (n i)) :
    periods x u = periods 0 u := by
  have h := periods_eq_zero_of_mem_coboundaries x (sub_seam_periods_mem_coboundaries hu)
  rwa [map_sub, periods_seam, sub_eq_zero] at h

/-- **[Q] (20.6)**: a closed cochain of the torus is exact if and only if its periods vanish. -/
theorem mem_coboundaries_iff_periods_eq_zero {u : CubicalCell (∀ i, ZMod (n i)) ι k → R}
    (hu : u ∈ cocycles R (fun i ↦ Pi.single i 1) k) :
    u ∈ coboundaries R (fun i ↦ Pi.single i 1) k ↔ periods 0 u = 0 := by
  refine ⟨periods_eq_zero_of_mem_coboundaries 0, fun h ↦ ?_⟩
  have := sub_seam_periods_mem_coboundaries hu
  rwa [h, map_zero, sub_zero] at this

variable (R n k) in
/-- **`H^k(∏ ℤ/nᵢ; R) ≃ R^(d choose k)`**: the periods identify the cohomology of the torus with
the functions on the `k`-sets of directions. -/
noncomputable def cohomologyEquiv :
    cohomology R (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) k ≃ₗ[R]
      (Set.powersetCard ι k → R) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext u
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker,
        LinearMap.comp_apply]
      exact mem_coboundaries_iff_periods_eq_zero u.2)).trans
    (LinearMap.quotKerEquivOfSurjective
      (periods 0 ∘ₗ (cocycles R (fun i ↦ Pi.single i 1) k).subtype) fun c ↦
        ⟨⟨seam c, coboundary_seam c⟩, periods_seam 0 c⟩)

theorem cohomologyEquiv_mk (u : cocycles R (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) k) :
    cohomologyEquiv R n k (Submodule.Quotient.mk u) =
      periods 0 (u : CubicalCell (∀ i, ZMod (n i)) ι k → R) :=
  rfl

end CubicalCochain

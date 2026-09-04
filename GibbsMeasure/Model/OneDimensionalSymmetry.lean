/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.SymmetryInheritance
public import GibbsMeasure.Potential.Pair

/-!
# Georgii §9.1: discrete symmetries in one dimension

The one-dimensional applications of Propositions (9.1) and (9.3)
(`GibbsMeasure/Specification/SymmetryInheritance.lean`): shift-periodicity of Gibbs measures on
`ℤ` (Theorem (9.5)), conservation of pure spin symmetries on `ℤ` or `ℕ` (Theorem (9.11)) and the
resulting non-existence theorem for dissipative symmetries (Corollary (9.16)).

## Pair potentials

* `Potential.pair`: **Georgii (9.10)**, the pair potential `Φ_{{i,j}} = φ_{ij}(σ_i, σ_j)`,
  `i < j`, on any linearly ordered set of sites; `Potential.pairTerms` is the underlying
  "pair family" with its enumeration `Potential.tsum_pairTerms` and finite-volume sum
  `Potential.sum_powerset_pairTerms`. `Potential.map_pair_eq_iff` is Georgii's remark after
  (9.10): a pure spin transformation is a symmetry iff `φ_{ij}(τ_i x, τ_j y) = φ_{ij}(x, y)`.
* `Potential.pairShift`: **Georgii (9.4)**, the shift-invariant case `φ_{ij} = φ_{j-i}` on `ℤ`;
  `Potential.isShiftInvariant_pairShift`, and `Potential.normAt_pairShift_le`,
  `Potential.isAbsolutelySummable_pairShift`: `Φ ∈ ℬ` when `∑_{k ≥ 1} ‖φ_k‖ < ∞` (Georgii,
  after (9.4)).

## Main results

* `MeasureTheory.GibbsMeasure.measurePreserving_shift_of_shiftDefect_ne_top`: **Georgii, Theorem
  (9.5)**. `S = ℤ`, `E` standard Borel, `λ` finite, `Φ ∈ ℬ_Θ` of the form (9.4), `p ≥ 1` with
  (9.6) `∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖ < ∞` (`shiftDefect`): every `μ ∈ 𝒢(Φ)` is `θ_p`-invariant.
  The proof is Georgii's: the localized shift `θ̃_p` is the cyclic rotation `rotateIcc` of
  `[m, n]` (`localizedShift`, `isLocalizedVersion_localizedShift`), and the estimate
  `‖H_Λ ∘ θ̃_p − H_Λ‖ ≤ 2p ‖Φ‖₀ + 2 ∑_k k ‖φ_{k+p} − φ_k‖`
  (`enorm_hamiltonian_localizedShift_sub_le`) is obtained by splitting `H_Λ` into the terms
  meeting the `p` boundary sites and a pair sum (`remainderPair`) which is reindexed along the
  rotation and compared term by term (`Σ̃₁ = Σ₁`, `|Σ̃₂ − Σ₂|`, `|Σ̃₃ − Σ₃|`).
* `MeasureTheory.GibbsMeasure.measurePreserving_of_pairDefectBound_ne_top`: **Georgii, Theorem
  (9.11)**, for any linear order of sites with predecessors and finite intervals (`ℤ` and `ℕ`):
  a `λ`-preserving pure spin symmetry `τ` of a `λ`-admissible pair potential with
  `C(Φ, τ) = sup_n ∑_{i ≤ n < j} J(i, j) < ∞` (`pairDefectBound`, (9.12)) preserves every Gibbs
  measure. The localized version is `τ̃ = (τ ω)_Λ ω_{S∖Λ}` (`Transformation.spinLocalize`), and
  `H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ − 2 H_Λ ≤ 2 C(Φ, τ)` (`hamiltonian_spinLocalize_add_sub_le`) is
  proved on the partial sums of the Hamiltonian series, so that only Georgii's summability (2.2)
  is used, not absolute summability.
* `MeasureTheory.GibbsMeasure.G_eq_empty_of_pairDefectBound_ne_top_of_dissipative`: **Georgii,
  Corollary (9.16)**: if moreover `τ` is dissipative — a bounded measurable `f ≥ 0` with
  `λ(f) > 0` and `f ∘ τ_i^k → 0` `λ`-a.s. at some site `i` — then `𝒢(Φ) = ∅`. The single-site
  marginal is equivalent to `λ` by Remark (1.28)(2), and dominated convergence does the rest.
* `MeasureTheory.GibbsMeasure.shiftDefect_mul_le`: **Georgii, Comment (9.7)(2)**, second half:
  for `φ_k = J(k) ψ` with `J ≥ 0` decreasing, `∑_k k ‖φ_{k+1} − φ_k‖ ≤ ‖ψ‖ ∑_k J(k)`.
* `MeasureTheory.GibbsMeasure.measurePreserving_shift_longRangeIsing`: **Georgii, Example
  (9.8)(1)**, the long-range Ising ferromagnet `Φ_{{i,j}} = −β |i − j|^{-a} σ_i σ_j`, `a > 1`:
  every Gibbs measure is invariant under every shift, `𝒢(Φ) = 𝒢_Θ(Φ)`
  (`measurePreserving_shift_of_one` passes from `θ_1` to all `θ_p`).

The inverse temperature `β` of the library's Gibbs specifications multiplies the Hamiltonian;
Georgii's statements are the case `β = 1`. Theorem (9.11) and Corollary (9.16) are stated for
`β ≥ 0` (the sign matters, since only an upper bound on `H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ − 2 H_Λ` is
available); Theorem (9.5) holds for every `β`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section


/-! ### Georgii, Theorem (9.11): pure spin symmetries in one dimension -/

namespace MeasureTheory.GibbsMeasure

open Potential Transformation

variable {S E : Type*} [MeasurableSpace E] [LinearOrder S]

/-- **Georgii (9.11).** `J(i, j) = sup_{x, y} [φ_{ij}(τ_i x, y) + φ_{ij}(x, τ_j y) - 2 φ_{ij}(x, y)]₊`. -/
def pairDefect (φ : S → S → E → E → ℝ) (τ : Transformation S E) (i j : S) : ℝ≥0∞ :=
  ⨆ (x : E) (y : E),
    ENNReal.ofReal (φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y)

/-- The sum `∑_{i ≤ n < j} J(i, j)` over the pairs straddling the cut after `n`. -/
def cutSum (J : S → S → ℝ≥0∞) (n : S) : ℝ≥0∞ :=
  ∑' q : S × S, if q.1 ≤ n ∧ n < q.2 then J q.1 q.2 else 0

/-- **Georgii (9.12).** `C(Φ, τ) = sup_n ∑_{i ≤ n < j} J(i, j)`; condition (9.12) is
`C(Φ, τ) < ∞`. -/
def pairDefectBound (φ : S → S → E → E → ℝ) (τ : Transformation S E) : ℝ≥0∞ :=
  ⨆ n : S, cutSum (pairDefect φ τ) n

variable {φ : S → S → E → E → ℝ} {τ : Transformation S E}

omit [LinearOrder S] in
lemma ofReal_le_pairDefect (i j : S) (x y : E) :
    ENNReal.ofReal (φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y) ≤
      pairDefect φ τ i j :=
  le_iSup₂ (f := fun x y ↦
    ENNReal.ofReal (φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y)) x y

lemma pairDefect_le_cutSum {i j n : S} (hi : i ≤ n) (hj : n < j) :
    pairDefect φ τ i j ≤ cutSum (pairDefect φ τ) n := by
  refine le_trans ?_ (ENNReal.le_tsum (i, j))
  simp [hi, hj]

lemma cutSum_le_pairDefectBound (n : S) : cutSum (pairDefect φ τ) n ≤ pairDefectBound φ τ :=
  le_iSup (fun n ↦ cutSum (pairDefect φ τ) n) n

lemma pairDefect_ne_top (hC : pairDefectBound φ τ ≠ ⊤) {i j : S} (hij : i < j) :
    pairDefect φ τ i j ≠ ⊤ :=
  ne_top_of_le_ne_top hC ((pairDefect_le_cutSum le_rfl hij).trans (cutSum_le_pairDefectBound i))

/-- Georgii, proof of (9.11): the summands of `Σ₂` and `Σ₃` are dominated by `J(i, j)`. -/
lemma sub_le_pairDefect_toReal (hC : pairDefectBound φ τ ≠ ⊤) {i j : S} (hij : i < j) (x y : E) :
    φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y ≤
      (pairDefect φ τ i j).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (pairDefect_ne_top hC hij)).1 (ofReal_le_pairDefect i j x y)

section Bound

variable [LocallyFiniteOrder S] [PredOrder S]

/-- The real-valued bound on the summands of `H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ - 2 H_Λ`, `Λ = [m, n]`:
`J(i, j)` for the pairs with exactly one site in `Λ`. -/
private def straddleBound (φ : S → S → E → E → ℝ) (τ : Transformation S E) (m n i j : S) : ℝ :=
  if (i ∈ Finset.Icc m n ∧ j ∉ Finset.Icc m n) ∨ (i ∉ Finset.Icc m n ∧ j ∈ Finset.Icc m n) then
    (pairDefect φ τ i j).toReal else 0

omit [PredOrder S] in
/-- Georgii, proof of (9.11): the pointwise bound `Σ₁ = 0`, `Σ₂, Σ₃ ≤ J(i, j)` on the terms of
`H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ - 2 H_Λ`. -/
private lemma hamiltonianTerms_spinLocalize_le
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (hC : pairDefectBound φ τ ≠ ⊤) (m n : S) (ω : S → E) (A : Finset S) :
    (pair φ).hamiltonianTerms (Finset.Icc m n) ((τ.spinLocalize (Finset.Icc m n)).toFun ω) A +
      (pair φ).hamiltonianTerms (Finset.Icc m n)
        ((τ.spinLocalize (Finset.Icc m n)).inv.toFun ω) A -
      2 * (pair φ).hamiltonianTerms (Finset.Icc m n) ω A ≤
      pairTerms (straddleBound φ τ m n) A := by
  have h0 : ∀ i j, i < j → 0 ≤ straddleBound φ τ m n i j := fun i j _ ↦ by
    unfold straddleBound
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  simp only [hamiltonianTerms_pair]
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · simp only [pairTerms_pair hij]
    by_cases hd : Disjoint ({i, j} : Finset S) (Finset.Icc m n)
    · rw [ite_eq_right (not_not.2 hd), ite_eq_right (not_not.2 hd), ite_eq_right (not_not.2 hd)]
      simp only [mul_zero, add_zero, sub_zero]
      exact h0 i j hij
    · rw [ite_eq_left hd, ite_eq_left hd, ite_eq_left hd]
      simp only [spinLocalize_toFun_apply, spinLocalize_inv_toFun_apply]
      rw [Finset.disjoint_insert_left, Finset.disjoint_singleton_left, not_and_or, not_not,
        not_not] at hd
      unfold straddleBound
      by_cases hi : i ∈ Finset.Icc m n <;> by_cases hj : j ∈ Finset.Icc m n
      · have hc : ¬ (i ∈ Finset.Icc m n ∧ j ∉ Finset.Icc m n ∨
            i ∉ Finset.Icc m n ∧ j ∈ Finset.Icc m n) := by simp [hi, hj]
        simp only [ite_eq_left hi, ite_eq_left hj, ite_eq_right hc]
        have h2 := hsym i j hij ((τ.spin i).symm (ω i)) ((τ.spin j).symm (ω j))
        rw [MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply] at h2
        rw [hsym i j hij, ← h2]
        exact le_of_eq (by ring)
      · have hc : i ∈ Finset.Icc m n ∧ j ∉ Finset.Icc m n ∨
            i ∉ Finset.Icc m n ∧ j ∈ Finset.Icc m n := Or.inl ⟨hi, hj⟩
        simp only [ite_eq_left hi, ite_eq_right hj, ite_eq_left hc]
        have h2 := hsym i j hij ((τ.spin i).symm (ω i)) (ω j)
        rw [MeasurableEquiv.apply_symm_apply] at h2
        rw [← h2]
        exact sub_le_pairDefect_toReal hC hij _ _
      · have hc : i ∈ Finset.Icc m n ∧ j ∉ Finset.Icc m n ∨
            i ∉ Finset.Icc m n ∧ j ∈ Finset.Icc m n := Or.inr ⟨hi, hj⟩
        simp only [ite_eq_right hi, ite_eq_left hj, ite_eq_left hc]
        have h2 := hsym i j hij (ω i) ((τ.spin j).symm (ω j))
        rw [MeasurableEquiv.apply_symm_apply] at h2
        rw [← h2, add_comm]
        exact sub_le_pairDefect_toReal hC hij _ _
      · exact absurd hd (by simp [hi, hj])
  · simp only [pairTerms_eq_zero hA, mul_zero, add_zero, sub_zero, le_refl]

/-- Georgii, proof of (9.11): `Σ₂ ≤ C(Φ, τ)` and `Σ₃ ≤ C(Φ, τ)`, on the partial sums over the
pairs in a finite volume `Δ`. -/
private lemma sum_straddleBound_le (hC : pairDefectBound φ τ ≠ ⊤) (m n : S) (Δ : Finset S) :
    ∑ i ∈ Δ, ∑ j ∈ Δ, (if i < j then straddleBound φ τ m n i j else 0) ≤
      2 * (pairDefectBound φ τ).toReal := by
  set J := pairDefect φ τ with hJ
  set C := pairDefectBound φ τ with hCdef
  let f₂ : S → S → ℝ≥0∞ := fun i j ↦
    if i < j ∧ i ∉ Finset.Icc m n ∧ j ∈ Finset.Icc m n then J i j else 0
  let f₃ : S → S → ℝ≥0∞ := fun i j ↦
    if i < j ∧ i ∈ Finset.Icc m n ∧ j ∉ Finset.Icc m n then J i j else 0
  have hpt : ∀ i j, ENNReal.ofReal (if i < j then straddleBound φ τ m n i j else 0) ≤
      f₂ i j + f₃ i j := by
    intro i j
    unfold straddleBound
    simp only [f₂, f₃]
    by_cases hij : i < j
    · rw [ite_eq_left hij]
      by_cases hi : i ∈ Finset.Icc m n <;> by_cases hj : j ∈ Finset.Icc m n
      · rw [ite_eq_right (by simp [hi, hj]), ENNReal.ofReal_zero]
        exact bot_le
      · rw [ite_eq_left (Or.inl ⟨hi, hj⟩), ite_eq_right (by simp [hi]),
          ite_eq_left ⟨hij, hi, hj⟩, ENNReal.ofReal_toReal (pairDefect_ne_top hC hij), zero_add]
      · rw [ite_eq_left (Or.inr ⟨hi, hj⟩), ite_eq_left ⟨hij, hi, hj⟩,
          ite_eq_right (by simp [hi]), ENNReal.ofReal_toReal (pairDefect_ne_top hC hij), add_zero]
      · rw [ite_eq_right (by simp [hi, hj]), ENNReal.ofReal_zero]
        exact bot_le
    · rw [ite_eq_right hij, ENNReal.ofReal_zero]
      exact bot_le
  have hcut : ∀ (n₀ : S) (g : S → S → ℝ≥0∞),
      (∀ i j, g i j ≤ if i ≤ n₀ ∧ n₀ < j then J i j else 0) →
      ∑ i ∈ Δ, ∑ j ∈ Δ, g i j ≤ C := by
    intro n₀ g hg
    calc ∑ i ∈ Δ, ∑ j ∈ Δ, g i j
        ≤ ∑ i ∈ Δ, ∑ j ∈ Δ, (if i ≤ n₀ ∧ n₀ < j then J i j else 0) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hg i j
      _ = ∑ q ∈ Δ ×ˢ Δ, (if q.1 ≤ n₀ ∧ n₀ < q.2 then J q.1 q.2 else 0) :=
          (Finset.sum_product' Δ Δ _).symm
      _ ≤ cutSum J n₀ := ENNReal.sum_le_tsum _
      _ ≤ C := cutSum_le_pairDefectBound n₀
  have h₂ : ∑ i ∈ Δ, ∑ j ∈ Δ, f₂ i j ≤ C := by
    by_cases hm : IsMin m
    · refine le_trans (le_of_eq (Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_))
        bot_le
      simp only [f₂]
      rw [ite_eq_right]
      rintro ⟨hij, hi, hj⟩
      rw [Finset.mem_Icc] at hi hj
      exact hi ⟨not_lt.1 fun h ↦ absurd (hm h.le) (not_le.2 h), hij.le.trans hj.2⟩
    · refine hcut (Order.pred m) f₂ fun i j ↦ ?_
      simp only [f₂]
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        obtain ⟨hij, hi, hj⟩ := h1
        rw [Finset.mem_Icc] at hi hj
        refine h2 ⟨Order.le_pred_of_lt ?_, (Order.pred_lt_of_not_isMin hm).trans_le hj.1⟩
        by_contra hmi
        exact hi ⟨not_lt.1 hmi, hij.le.trans hj.2⟩
      · exact bot_le
      · exact le_rfl
  have h₃ : ∑ i ∈ Δ, ∑ j ∈ Δ, f₃ i j ≤ C := by
    refine hcut n f₃ fun i j ↦ ?_
    simp only [f₃]
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso
      obtain ⟨hij, hi, hj⟩ := h1
      rw [Finset.mem_Icc] at hi hj
      refine h2 ⟨hi.2, ?_⟩
      by_contra hnj
      exact hj ⟨hi.1.trans hij.le, not_lt.1 hnj⟩
    · exact bot_le
    · exact le_rfl
  have hC2 : (2 : ℝ≥0∞) * C ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC
  have key : ENNReal.ofReal (∑ i ∈ Δ, ∑ j ∈ Δ, (if i < j then straddleBound φ τ m n i j else 0))
      ≤ 2 * C := by
    have hnn : ∀ i j, 0 ≤ (if i < j then straddleBound φ τ m n i j else 0) := fun i j ↦ by
      unfold straddleBound
      split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j]
    simp_rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ hnn _ j]
    calc ∑ i ∈ Δ, ∑ j ∈ Δ, ENNReal.ofReal (if i < j then straddleBound φ τ m n i j else 0)
        ≤ ∑ i ∈ Δ, ∑ j ∈ Δ, (f₂ i j + f₃ i j) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
      _ = ∑ i ∈ Δ, ∑ j ∈ Δ, f₂ i j + ∑ i ∈ Δ, ∑ j ∈ Δ, f₃ i j := by
          simp_rw [Finset.sum_add_distrib]
      _ ≤ C + C := add_le_add h₂ h₃
      _ = 2 * C := (two_mul C).symm
  have := (ENNReal.ofReal_le_iff_le_toReal hC2).1 key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

/-- Georgii, proof of (9.11): `H_Λ ∘ τ̃ + H_Λ ∘ τ̃⁻¹ - 2 H_Λ ≤ 2 C(Φ, τ)` for `Λ = [m, n]`. -/
lemma hamiltonian_spinLocalize_add_sub_le [IsSummable (pair φ)]
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (hC : pairDefectBound φ τ ≠ ⊤) (m n : S) (ω : S → E) :
    (pair φ).hamiltonian (Finset.Icc m n) ((τ.spinLocalize (Finset.Icc m n)).toFun ω) +
      (pair φ).hamiltonian (Finset.Icc m n) ((τ.spinLocalize (Finset.Icc m n)).inv.toFun ω) -
      2 * (pair φ).hamiltonian (Finset.Icc m n) ω ≤ 2 * (pairDefectBound φ τ).toReal := by
  set Λ := Finset.Icc m n
  have hsum := ((hasSum_hamiltonian (Φ := pair φ) Λ ((τ.spinLocalize Λ).toFun ω)).add
    (hasSum_hamiltonian (Φ := pair φ) Λ ((τ.spinLocalize Λ).inv.toFun ω))).sub
    ((hasSum_hamiltonian (Φ := pair φ) Λ ω).mul_left 2)
  have htend : Tendsto (fun Δ : Finset S ↦ ∑ A ∈ Δ.powerset,
      ((pair φ).hamiltonianTerms Λ ((τ.spinLocalize Λ).toFun ω) A +
        (pair φ).hamiltonianTerms Λ ((τ.spinLocalize Λ).inv.toFun ω) A -
        2 * (pair φ).hamiltonianTerms Λ ω A)) atTop
      (𝓝 ((pair φ).hamiltonian Λ ((τ.spinLocalize Λ).toFun ω) +
        (pair φ).hamiltonian Λ ((τ.spinLocalize Λ).inv.toFun ω) -
        2 * (pair φ).hamiltonian Λ ω)) :=
    hsum.comp (Filter.tendsto_map (f := Finset.powerset))
  refine le_of_tendsto' htend fun Δ ↦ ?_
  calc ∑ A ∈ Δ.powerset, ((pair φ).hamiltonianTerms Λ ((τ.spinLocalize Λ).toFun ω) A +
        (pair φ).hamiltonianTerms Λ ((τ.spinLocalize Λ).inv.toFun ω) A -
        2 * (pair φ).hamiltonianTerms Λ ω A)
      ≤ ∑ A ∈ Δ.powerset, pairTerms (straddleBound φ τ m n) A :=
        Finset.sum_le_sum fun A _ ↦ hamiltonianTerms_spinLocalize_le hsym hC m n ω A
    _ = ∑ i ∈ Δ, ∑ j ∈ Δ, (if i < j then straddleBound φ τ m n i j else 0) :=
        sum_powerset_pairTerms Δ _
    _ ≤ 2 * (pairDefectBound φ τ).toReal := sum_straddleBound_le hC m n Δ

/-- **Georgii, Theorem (9.11).** Let `S = ℤ` or `ℕ` (any linear order with predecessors and
finite intervals), `E` standard Borel, `λ` an a priori measure, `Φ` a `λ`-admissible pair
potential of the form (9.10), and `τ = (τ_i)` a `λ`-preserving pure spin symmetry of `Φ`.
If `C(Φ, τ) < ∞` (9.12), then `τ` preserves each `μ ∈ 𝒢(Φ)`.

The inverse temperature `β ≥ 0` multiplies the Hamiltonian; Georgii's statement is `β = 1`. -/
theorem measurePreserving_of_pairDefectBound_ne_top [Countable S] [StandardBorelSpace E]
    [IsPotential (pair φ)] [IsSummable (pair φ)] (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    {β : ℝ} (hβ : 0 ≤ β)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((pair φ).boltzmannFactor β))
    (hτ : τ.IsPureSpin) (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (hC : pairDefectBound φ τ ≠ ⊤) {μ : Measure (S → E)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair φ) ν β hadm)) :
    MeasurePreserving τ.toFun μ μ := by
  refine measurePreserving_gibbsSpecificationOfSigmaFiniteAdmissible_of_isLocalizedVersion ν β
    hadm hτν ((map_pair_eq_iff φ hτ).2 hsym) (c := 1 / 2)
    (C := β * (pairDefectBound φ τ).toReal) (by norm_num) (by norm_num) ?_ hμ
  intro Δ
  rcases Δ.eq_empty_or_nonempty with rfl | hΔ
  · refine ⟨∅, τ.spinLocalize ∅, measurePreserving_spin_spinLocalize hτν ∅,
      isLocalizedVersion_spinLocalize hτ (subset_refl ∅), fun ω ↦ ?_⟩
    simp only [Potential.hamiltonian_empty, mul_zero, add_zero, sub_zero]
    positivity
  · set m := Δ.min' hΔ
    set n := Δ.max' hΔ
    have hΔΛ : Δ ⊆ Finset.Icc m n := fun i hi ↦
      Finset.mem_Icc.2 ⟨Δ.min'_le i hi, Δ.le_max' i hi⟩
    refine ⟨Finset.Icc m n, τ.spinLocalize _, measurePreserving_spin_spinLocalize hτν _,
      isLocalizedVersion_spinLocalize hτ hΔΛ, fun ω ↦ ?_⟩
    have h := hamiltonian_spinLocalize_add_sub_le hsym hC m n ω
    have h' : 1 / 2 * (pair φ).hamiltonian (Finset.Icc m n)
          ((τ.spinLocalize (Finset.Icc m n)).toFun ω) +
        (1 - 1 / 2) * (pair φ).hamiltonian (Finset.Icc m n)
          ((τ.spinLocalize (Finset.Icc m n)).inv.toFun ω) -
        (pair φ).hamiltonian (Finset.Icc m n) ω ≤ (pairDefectBound φ τ).toReal := by
      linarith
    exact mul_le_mul_of_nonneg_left h' hβ

/-- **Georgii, Corollary (9.16).** Let `S = ℤ` or `ℕ`, `E` standard Borel, `λ ∈ 𝓜(E, ℰ)` and
`τ = (τ_i) ∈ T_λ⁰` a `λ`-preserving pure spin transformation which is *dissipative*: there are a
bounded measurable `f ≥ 0` on `E` with `λ(f) > 0` and a site `i` with `f ∘ τ_i^k → 0` `λ`-a.s.
If `Φ` is a `τ`-invariant `λ`-admissible pair potential (9.10) with `C(Φ, τ) < ∞` (9.12), then
`𝒢(Φ) = ∅`. -/
theorem G_eq_empty_of_pairDefectBound_ne_top_of_dissipative [Countable S] [StandardBorelSpace E]
    [IsPotential (pair φ)] [IsSummable (pair φ)] (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    {β : ℝ} (hβ : 0 ≤ β)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((pair φ).boltzmannFactor β))
    (hτ : τ.IsPureSpin) (hτν : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (hC : pairDefectBound φ τ ≠ ⊤) {f : E → ℝ≥0∞} (hf : Measurable f) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hfM : ∀ x, f x ≤ M) (hf0 : ∫⁻ x, f x ∂ν ≠ 0) (i : S)
    (hdiss : ∀ᵐ x ∂ν, Tendsto (fun k ↦ f ((τ.spin i)^[k] x)) atTop (𝓝 0)) :
    G (gibbsSpecificationOfSigmaFiniteAdmissible (pair φ) ν β hadm) = ∅ :=
  G_gibbsSpecificationOfSigmaFiniteAdmissible_eq_empty_of_dissipative ν β hadm hf hM hfM hf0 i
    (τ := fun k ↦ τ ^ k) (fun k ↦ hτ.pow k)
    (by simpa only [hτ.pow_spin_apply] using hdiss) fun μ hμ k ↦ by
      rw [Transformation.pow_toFun]
      exact (measurePreserving_of_pairDefectBound_ne_top ν hβ hadm hτ hτν hsym hC hμ).iterate k

end Bound

end MeasureTheory.GibbsMeasure


/-! ### The cyclic rotation of an integer interval (Georgii, proof of (9.5)) -/

namespace MeasureTheory.GibbsMeasure

/-- The cyclic rotation `k ↦ k - p` (mod `[m, n]`) of the integer interval `[m, n]`, the
identity outside: Georgii's spatial part of the localized shift `θ̃_p` in the proof of (9.5),
`(θ̃_p ω)_i = ω_{i-p}` for `m + p ≤ i ≤ n`, `ω_{i-p+n-m+1}` for `m ≤ i < m + p`, `ω_i` off
`[m, n]`. -/
def rotateIcc (m n p : ℤ) (hp : 0 ≤ p) (hpL : p ≤ n - m + 1) : ℤ ≃ ℤ where
  toFun k := if m + p ≤ k ∧ k ≤ n then k - p else if m ≤ k ∧ k < m + p then k - p + (n - m + 1)
    else k
  invFun k := if m ≤ k ∧ k ≤ n - p then k + p else if n - p < k ∧ k ≤ n then k + p - (n - m + 1)
    else k
  left_inv k := by
    simp only
    split_ifs <;> omega
  right_inv k := by
    simp only
    split_ifs <;> omega

variable {m n p : ℤ} {hp : 0 ≤ p} {hpL : p ≤ n - m + 1}

lemma rotateIcc_apply (k : ℤ) :
    rotateIcc m n p hp hpL k = if m + p ≤ k ∧ k ≤ n then k - p
      else if m ≤ k ∧ k < m + p then k - p + (n - m + 1) else k := rfl

lemma rotateIcc_symm_apply (k : ℤ) :
    (rotateIcc m n p hp hpL).symm k = if m ≤ k ∧ k ≤ n - p then k + p
      else if n - p < k ∧ k ≤ n then k + p - (n - m + 1) else k := rfl

lemma rotateIcc_apply_of_upper {k : ℤ} (h1 : m + p ≤ k) (h2 : k ≤ n) :
    rotateIcc m n p hp hpL k = k - p := by
  rw [rotateIcc_apply, ite_eq_left ⟨h1, h2⟩]

lemma rotateIcc_apply_of_lower {k : ℤ} (h1 : m ≤ k) (h2 : k < m + p) :
    rotateIcc m n p hp hpL k = k - p + (n - m + 1) := by
  rw [rotateIcc_apply, ite_eq_right (by omega), ite_eq_left ⟨h1, h2⟩]

lemma rotateIcc_apply_of_notMem {k : ℤ} (h : k < m ∨ n < k) :
    rotateIcc m n p hp hpL k = k := by
  rw [rotateIcc_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

lemma rotateIcc_symm_apply_of_mem {k : ℤ} (h1 : m ≤ k) (h2 : k ≤ n - p) :
    (rotateIcc m n p hp hpL).symm k = k + p := by
  rw [rotateIcc_symm_apply, ite_eq_left ⟨h1, h2⟩]

/-- The three regions of the rotation. -/
lemma rotateIcc_cases (k : ℤ) :
    (m + p ≤ k ∧ k ≤ n ∧ rotateIcc m n p hp hpL k = k - p) ∨
      (m ≤ k ∧ k < m + p ∧ rotateIcc m n p hp hpL k = k - p + (n - m + 1)) ∨
      ((k < m ∨ n < k) ∧ rotateIcc m n p hp hpL k = k) := by
  by_cases h1 : m + p ≤ k ∧ k ≤ n
  · exact Or.inl ⟨h1.1, h1.2, rotateIcc_apply_of_upper h1.1 h1.2⟩
  · by_cases h2 : m ≤ k ∧ k < m + p
    · exact Or.inr (Or.inl ⟨h2.1, h2.2, rotateIcc_apply_of_lower h2.1 h2.2⟩)
    · exact Or.inr (Or.inr ⟨by omega, rotateIcc_apply_of_notMem (by omega)⟩)

/-- Georgii's localized shift `θ̃_p` on `[m, n]`: `(θ̃_p ω)_i = ω_{r i}` for the rotation `r`. -/
def localizedShift (E : Type*) [MeasurableSpace E] (m n p : ℤ) (hp : 0 ≤ p)
    (hpL : p ≤ n - m + 1) : Transformation ℤ E :=
  siteEquiv E (rotateIcc m n p hp hpL).symm

variable (E : Type*) [MeasurableSpace E]

@[simp] lemma localizedShift_toFun_apply (ω : ℤ → E) (i : ℤ) :
    (localizedShift E m n p hp hpL).toFun ω i = ω (rotateIcc m n p hp hpL i) := by
  simp [localizedShift]

@[simp] lemma localizedShift_inv_toFun_apply (ω : ℤ → E) (i : ℤ) :
    (localizedShift E m n p hp hpL).inv.toFun ω i = ω ((rotateIcc m n p hp hpL).symm i) := by
  simp [localizedShift, Transformation.inv, Transformation.toFun, siteEquiv]

lemma localizedShift_spin (i : ℤ) :
    (localizedShift E m n p hp hpL).spin i = MeasurableEquiv.refl E := rfl

/-- `θ̃_p` is a localized version of the shift `θ_p` on `Δ ⊆ [m + p, n − p]` within `[m, n]`
(Georgii: "condition (i) of Proposition (9.3) then evidently holds"). -/
lemma isLocalizedVersion_localizedShift {Δ : Finset ℤ} (hΔ : Δ ⊆ Finset.Icc (m + p) (n - p)) :
    (localizedShift E m n p hp hpL).IsLocalizedVersion (shift E p) Δ (Finset.Icc m n) where
  toFun_eq_of_mem ω i hi := by
    have := Finset.mem_Icc.1 (hΔ hi)
    rw [localizedShift_toFun_apply, shift_toFun_apply, rotateIcc_apply_of_upper this.1 (by omega)]
  inv_toFun_eq_of_mem ω i hi := by
    have := Finset.mem_Icc.1 (hΔ hi)
    rw [localizedShift_inv_toFun_apply, shift_inv_toFun_apply,
      rotateIcc_symm_apply_of_mem (by omega) this.2]
  toFun_eq_of_notMem ω i hi := by
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi
    rw [localizedShift_toFun_apply, rotateIcc_apply_of_notMem hi]

end MeasureTheory.GibbsMeasure


/-! ### Georgii, Theorem (9.5): shift-periodicity in one dimension -/

namespace MeasureTheory.GibbsMeasure

open Potential

variable {E : Type*} [MeasurableSpace E] (φ : ℤ → E → E → ℝ)

/-- The pair family of the remainder `∑_{A ∩ Λ₁ ≠ ∅, A ∩ Λ₂ = ∅} Φ_A` of the potential (9.4),
indexed by the pairs `(i, j)`. -/
def remainderPair (Λ₁ Λ₂ : Finset ℤ) (η : ℤ → E) (q : ℤ × ℤ) : ℝ :=
  if q.1 < q.2 then
    (if Disjoint {q.1, q.2} Λ₂ then
      (if ¬ Disjoint {q.1, q.2} Λ₁ then φ (q.2 - q.1) (η q.1) (η q.2) else 0) else 0)
  else 0

lemma ite_hamiltonianTerms_pairShift_eq (Λ₁ Λ₂ : Finset ℤ) (η : ℤ → E) (A : Finset ℤ) :
    (if Disjoint A Λ₂ then (pairShift φ).hamiltonianTerms Λ₁ η A else 0) =
      pairTerms (fun i j ↦ if Disjoint {i, j} Λ₂ then
        (if ¬ Disjoint {i, j} Λ₁ then φ (j - i) (η i) (η j) else 0) else 0) A := by
  rw [← ite_pairTerms (fun B ↦ Disjoint B Λ₂)]
  congr 1
  exact hamiltonianTerms_pair _ Λ₁ η A

/-- The remainder of the Hamiltonian of (9.4) as a sum over pairs. -/
lemma tsum_ite_hamiltonianTerms_pairShift (Λ₁ Λ₂ : Finset ℤ) (η : ℤ → E) :
    ∑' A : Finset ℤ, (if Disjoint A Λ₂ then (pairShift φ).hamiltonianTerms Λ₁ η A else 0) =
      ∑' q : ℤ × ℤ, remainderPair φ Λ₁ Λ₂ η q := by
  simp_rw [ite_hamiltonianTerms_pairShift_eq]
  rw [tsum_pairTerms]
  rfl

lemma summable_remainderPair [IsAbsolutelySummable (pairShift φ)] (Λ₁ Λ₂ : Finset ℤ)
    (η : ℤ → E) : Summable (remainderPair φ Λ₁ Λ₂ η) := by
  have hind : (fun A : Finset ℤ ↦
      if Disjoint A Λ₂ then (pairShift φ).hamiltonianTerms Λ₁ η A else 0) =
      {A : Finset ℤ | Disjoint A Λ₂}.indicator ((pairShift φ).hamiltonianTerms Λ₁ η) := by
    funext A
    rw [Set.indicator_apply]
    congr
  have hs : Summable fun A : Finset ℤ ↦
      if Disjoint A Λ₂ then (pairShift φ).hamiltonianTerms Λ₁ η A else 0 := by
    rw [hind]
    exact (summable_hamiltonianTerms Λ₁ η).indicator _
  simp_rw [ite_hamiltonianTerms_pairShift_eq] at hs
  rw [summable_pairTerms_iff] at hs
  exact hs

/-- `H_{[m, n]} = H_{[n − p + 1, n]} + Σ₁ + Σ₂ + Σ₃`, Georgii's decomposition in the proof of
(9.5), with the remainder as a pair sum. -/
lemma hamiltonian_Icc_eq_add_tsum_remainderPair [IsAbsolutelySummable (pairShift φ)]
    {m n a : ℤ} (h1 : m ≤ a + 1) (h2 : a ≤ n) (η : ℤ → E) :
    (pairShift φ).hamiltonian (Finset.Icc m n) η =
      (pairShift φ).hamiltonian (Finset.Icc (a + 1) n) η +
        ∑' q : ℤ × ℤ, remainderPair φ (Finset.Icc m a) (Finset.Icc (a + 1) n) η q := by
  have hunion : Finset.Icc m n = Finset.Icc m a ∪ Finset.Icc (a + 1) n := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [hunion, hamiltonian_union_eq_add_tsum, tsum_ite_hamiltonianTerms_pairShift]

/-- `H_{[m, n]} = H_{[m, m + p − 1]} + Σ̃₁ + Σ̃₂ + Σ̃₃`. -/
lemma hamiltonian_Icc_eq_add_tsum_remainderPair' [IsAbsolutelySummable (pairShift φ)]
    {m n a : ℤ} (h1 : m ≤ a + 1) (h2 : a ≤ n) (η : ℤ → E) :
    (pairShift φ).hamiltonian (Finset.Icc m n) η =
      (pairShift φ).hamiltonian (Finset.Icc m a) η +
        ∑' q : ℤ × ℤ, remainderPair φ (Finset.Icc (a + 1) n) (Finset.Icc m a) η q := by
  have hunion : Finset.Icc m n = Finset.Icc (a + 1) n ∪ Finset.Icc m a := by
    ext i
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  rw [hunion, hamiltonian_union_eq_add_tsum, tsum_ite_hamiltonianTerms_pairShift]

/-- **Georgii (9.6).** `∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖`. -/
def shiftDefect (p : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * pairDist φ (k + 1 + p) (k + 1)

section Estimate

variable {m n : ℤ} {p : ℕ}

/-- The bound on the `Σ₂`-terms: pairs `m + p ≤ i ≤ n < j`. -/
private def boundTwo (m n : ℤ) (p : ℕ) (q : ℤ × ℤ) : ℝ≥0∞ :=
  if m + p ≤ q.1 ∧ q.1 ≤ n ∧ n < q.2 then pairDist φ (q.2 - q.1) (q.2 - (q.1 - p)) else 0

/-- The bound on the `Σ₃`-terms: pairs `i < m`, `m + p ≤ j ≤ n`. -/
private def boundThree (m n : ℤ) (p : ℕ) (q : ℤ × ℤ) : ℝ≥0∞ :=
  if q.1 < m ∧ m + p ≤ q.2 ∧ q.2 ≤ n then pairDist φ (q.2 - q.1) ((q.2 - p) - q.1) else 0

/-- Georgii, proof of (9.5): term by term, `Σ̃₁ = Σ₁`, and the summands of `Σ̃₂ − Σ₂` and
`Σ̃₃ − Σ₃` are bounded by `‖φ_{j-i} − φ_{j-i+p}‖` resp. `‖φ_{j-i} − φ_{j-i-p}‖`, after the
reindexing along the rotation. -/
private lemma enorm_remainderPair_sub_le (hp : 0 < p) (hL : 2 * (p : ℤ) + 1 ≤ n - m + 1)
    (ω : ℤ → E) (q : ℤ × ℤ) :
    ‖remainderPair φ (Finset.Icc (m + p) n) (Finset.Icc m (m + p - 1))
        ((localizedShift E m n p (by positivity) (by omega)).toFun ω) q -
      remainderPair φ (Finset.Icc m (n - p)) (Finset.Icc (n - p + 1) n) ω
        (rotateIcc m n p (by positivity) (by omega) q.1, rotateIcc m n p (by positivity) (by
            omega) q.2)‖ₑ
      ≤ boundTwo φ m n p q + boundThree φ m n p q := by
  obtain ⟨i, j⟩ := q
  simp only [remainderPair, boundTwo, boundThree, localizedShift_toFun_apply,
    Finset.disjoint_insert_left, Finset.disjoint_singleton_left, Finset.mem_Icc]
  rcases rotateIcc_cases (m := m) (n := n) (p := p) (hp := by positivity) (hpL := by omega) i with
      ⟨hi1, hi2, hri⟩ | ⟨hi1, hi2, hri⟩ | ⟨hi, hri⟩ <;>
    rcases rotateIcc_cases (m := m) (n := n) (p := p) (hp := by positivity) (hpL := by omega) j
      with ⟨hj1, hj2, hrj⟩ | ⟨hj1, hj2, hrj⟩ | ⟨hj, hrj⟩ <;>
    rw [hri, hrj] <;>
    split_ifs <;>
    first
    | (exfalso; omega)
    | (simp; done)
    | exact le_trans (enorm_sub_le_pairDist φ _ _ _ _) le_self_add
    | exact le_trans (enorm_sub_le_pairDist φ _ _ _ _) le_add_self

/-- Counting the pairs with a given difference: `∑_q F q ≤ ∑_k (k + 1) a k` when `F` is carried
by an injective image of `ℕ × ℤ` on which the `k`-th fibre is dominated by `a k` on an interval
of `k + 1` sites. -/
private lemma tsum_le_tsum_succ_mul (F : ℤ × ℤ → ℝ≥0∞) (a : ℕ → ℝ≥0∞) (g : ℕ × ℤ → ℤ × ℤ)
    (hg : Function.Injective g) (hsupp : Function.support F ⊆ Set.range g) (lo : ℕ → ℤ)
    (hF : ∀ k i, F (g (k, i)) ≤ if lo k ≤ i ∧ i ≤ lo k + k then a k else 0) :
    ∑' q, F q ≤ ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * a k := by
  rw [← hg.tsum_eq hsupp, ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun k ↦ ?_
  calc ∑' i, F (g (k, i))
      ≤ ∑' i : ℤ, (if lo k ≤ i ∧ i ≤ lo k + k then a k else 0) := ENNReal.tsum_le_tsum (hF k)
    _ = ∑ i ∈ Finset.Icc (lo k) (lo k + k), (if lo k ≤ i ∧ i ≤ lo k + k then a k else 0) :=
        tsum_eq_sum fun i hi ↦ ite_eq_right (by rwa [Finset.mem_Icc] at hi)
    _ = ∑ i ∈ Finset.Icc (lo k) (lo k + k), a k :=
        Finset.sum_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_Icc.1 hi)
    _ = ((k : ℝ≥0∞) + 1) * a k := by
        rw [Finset.sum_const, Int.card_Icc, show (lo k + k + 1 - lo k).toNat = k + 1 by omega,
          nsmul_eq_mul, Nat.cast_succ]

omit [MeasurableSpace E] in
private lemma tsum_boundTwo_le (m n : ℤ) (p : ℕ) :
    ∑' q, boundTwo φ m n p q ≤ shiftDefect φ p := by
  refine tsum_le_tsum_succ_mul _ _ (fun ki ↦ (ki.2, ki.2 + 1 + ki.1)) ?_ ?_ (fun k ↦ n - k) ?_
  · rintro ⟨k, i⟩ ⟨l, j⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : k = l := by omega
    rw [this]
  · intro q hq
    simp only [boundTwo, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hq
    refine ⟨((q.2 - q.1 - 1).toNat, q.1), ?_⟩
    ext
    · rfl
    · simp only
      omega
  · intro k i
    simp only [boundTwo]
    by_cases h : m + p ≤ i ∧ i ≤ n ∧ n < i + 1 + k
    · rw [ite_eq_left h, ite_eq_left (show n - k ≤ i ∧ i ≤ n - k + k by omega),
        pairDist_comm]
      refine le_of_eq ?_
      congr 1 <;> ring
    · rw [ite_eq_right h]
      exact bot_le

omit [MeasurableSpace E] in
private lemma tsum_boundThree_le (m n : ℤ) (p : ℕ) :
    ∑' q, boundThree φ m n p q ≤ shiftDefect φ p := by
  refine tsum_le_tsum_succ_mul _ _ (fun kj ↦ (kj.2 - p - 1 - kj.1, kj.2)) ?_ ?_ (fun _ ↦ m + p) ?_
  · rintro ⟨k, i⟩ ⟨l, j⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, rfl⟩ := h
    have : k = l := by omega
    rw [this]
  · intro q hq
    simp only [boundThree, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hq
    refine ⟨((q.2 - q.1 - p - 1).toNat, q.2), ?_⟩
    ext
    · simp only
      omega
    · rfl
  · intro k j
    simp only [boundThree]
    by_cases h : j - p - 1 - k < m ∧ m + p ≤ j ∧ j ≤ n
    · rw [ite_eq_left h, ite_eq_left (show m + p ≤ j ∧ j ≤ m + p + k by omega)]
      refine le_of_eq ?_
      congr 1 <;> ring
    · rw [ite_eq_right h]
      exact bot_le

/-- `H_{[a, a + p − 1]}` is bounded by `p ‖Φ‖₀` for the shift-invariant potential (9.4). -/
lemma enorm_hamiltonian_Icc_le [IsAbsolutelySummable (pairShift φ)] (a : ℤ) (p : ℕ) (η : ℤ → E) :
    ‖(pairShift φ).hamiltonian (Finset.Icc a (a + p - 1)) η‖ₑ ≤ p * (pairShift φ).normAt 0 := by
  refine (enorm_hamiltonian_le _ _).trans (le_of_eq ?_)
  rw [Finset.sum_congr rfl fun i _ ↦ normAt_eq_of_isShiftInvariant (isShiftInvariant_pairShift φ) i,
    Finset.sum_const, Int.card_Icc, show (a + p - 1 + 1 - a).toNat = p by omega, nsmul_eq_mul]

/-- **Georgii, proof of (9.5), the estimate `‖H_Λ ∘ θ̃_p − H_Λ‖ ≤ C`** on `Λ = [m, n]`, with
`C = 2p ‖Φ‖₀ + 2 ∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖` (Georgii writes `‖Φ‖₀ = 2 ∑_k ‖φ_k‖`). -/
theorem enorm_hamiltonian_localizedShift_sub_le [IsAbsolutelySummable (pairShift φ)]
    (hp : 0 < p) (hL : 2 * (p : ℤ) + 1 ≤ n - m + 1) (ω : ℤ → E) :
    ‖(pairShift φ).hamiltonian (Finset.Icc m n)
        ((localizedShift E m n p (by positivity) (by omega)).toFun ω) -
      (pairShift φ).hamiltonian (Finset.Icc m n) ω‖ₑ ≤
      2 * p * (pairShift φ).normAt 0 + 2 * shiftDefect φ p := by
  set r := rotateIcc m n p (by positivity) (by omega) with hr
  set τ' := localizedShift E m n p (by positivity) (by omega) with hτ'
  have h1 := hamiltonian_Icc_eq_add_tsum_remainderPair' φ (m := m) (n := n) (a := m + p - 1)
    (by omega) (by omega) (τ'.toFun ω)
  have h2 := hamiltonian_Icc_eq_add_tsum_remainderPair φ (m := m) (n := n) (a := n - p)
    (by omega) (by omega) ω
  rw [show m + p - 1 + 1 = m + p by ring] at h1
  rw [h1, h2]
  set R := fun q : ℤ × ℤ ↦ remainderPair φ (Finset.Icc m (n - p)) (Finset.Icc (n - p + 1) n) ω q
    with hR
  set R' := fun q : ℤ × ℤ ↦ remainderPair φ (Finset.Icc (m + p) n) (Finset.Icc m (m + p - 1))
    (τ'.toFun ω) q with hR'
  have hre : ∑' q, R q = ∑' q : ℤ × ℤ, R (r q.1, r q.2) := by
    rw [← (Equiv.prodCongr r r).tsum_eq R]
    exact tsum_congr fun q ↦ by rw [Equiv.prodCongr_apply, Prod.map]
  have hsumR : Summable fun q : ℤ × ℤ ↦ R (r q.1, r q.2) := by
    have := ((Equiv.prodCongr r r).summable_iff (f := R)).2 (summable_remainderPair φ _ _ ω)
    exact this.congr fun q ↦ by rw [Function.comp_apply, Equiv.prodCongr_apply, Prod.map]
  have hsumR' : Summable R' := summable_remainderPair φ _ _ _
  have hdiff : ((pairShift φ).hamiltonian (Finset.Icc m (m + p - 1)) (τ'.toFun ω) +
        ∑' q, R' q) - ((pairShift φ).hamiltonian (Finset.Icc (n - p + 1) n) ω + ∑' q, R q) =
      ((pairShift φ).hamiltonian (Finset.Icc m (m + p - 1)) (τ'.toFun ω) -
        (pairShift φ).hamiltonian (Finset.Icc (n - p + 1) n) ω) +
        ∑' q, (R' q - R (r q.1, r q.2)) := by
    rw [hre, hsumR'.tsum_sub hsumR]
    ring
  rw [hdiff]
  have hH4 := enorm_hamiltonian_Icc_le φ (n - p + 1) p ω
  rw [show n - p + 1 + p - 1 = n by ring] at hH4
  calc _ ≤ ‖(pairShift φ).hamiltonian (Finset.Icc m (m + p - 1)) (τ'.toFun ω) -
          (pairShift φ).hamiltonian (Finset.Icc (n - p + 1) n) ω‖ₑ +
        ‖∑' q, (R' q - R (r q.1, r q.2))‖ₑ := enorm_add_le _ _
    _ ≤ (‖(pairShift φ).hamiltonian (Finset.Icc m (m + p - 1)) (τ'.toFun ω)‖ₑ +
          ‖(pairShift φ).hamiltonian (Finset.Icc (n - p + 1) n) ω‖ₑ) +
        ∑' q, ‖R' q - R (r q.1, r q.2)‖ₑ :=
        add_le_add enorm_sub_le enorm_tsum_le_tsum_enorm
    _ ≤ (p * (pairShift φ).normAt 0 + p * (pairShift φ).normAt 0) +
        ∑' q, (boundTwo φ m n p q + boundThree φ m n p q) :=
        add_le_add (add_le_add (enorm_hamiltonian_Icc_le φ m p _) hH4)
          (ENNReal.tsum_le_tsum fun q ↦ enorm_remainderPair_sub_le φ hp hL ω q)
    _ ≤ (p * (pairShift φ).normAt 0 + p * (pairShift φ).normAt 0) +
        (shiftDefect φ p + shiftDefect φ p) := by
        rw [ENNReal.tsum_add]
        gcongr
        · exact tsum_boundTwo_le φ m n p
        · exact tsum_boundThree_le φ m n p
    _ = 2 * p * (pairShift φ).normAt 0 + 2 * shiftDefect φ p := by ring

end Estimate

/-- **Georgii, Theorem (9.5).** Let `S = ℤ`, `E` standard Borel, `λ` a finite a priori measure
and `Φ ∈ ℬ_Θ` the shift-invariant pair potential (9.4) built from measurable `φ_k`. If `p ≥ 1`
satisfies (9.6), `∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖ < ∞`, then every `μ ∈ 𝒢(Φ)` is `θ_p`-invariant.

The constant of Proposition (9.3) is `|β| (2p ‖Φ‖₀ + 2 ∑_k k ‖φ_{k+p} − φ_k‖)`, where
`‖Φ‖₀ = ‖Φ‖_0 ≤ 2 ∑_k ‖φ_k‖` (`Potential.normAt_pairShift_le`); Georgii's constant is the
right-hand side at `β = 1`. -/
theorem measurePreserving_shift_of_shiftDefect_ne_top [StandardBorelSpace E]
    [IsPotential (pairShift φ)] [IsAbsolutelySummable (pairShift φ)]
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) {p : ℕ} (hp : 0 < p)
    (hK : shiftDefect φ p ≠ ⊤) {μ : Measure (ℤ → E)}
    (hμ : μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift φ) ν β)) :
    MeasurePreserving (shift E (p : ℤ)).toFun μ μ := by
  set B : ℝ≥0∞ := 2 * p * (pairShift φ).normAt 0 + 2 * shiftDefect φ p with hBdef
  have hB : B ≠ ⊤ := ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.natCast_ne_top p))
      (IsAbsolutelySummable.normAt_ne_top 0), ENNReal.mul_ne_top ENNReal.ofNat_ne_top hK⟩
  refine measurePreserving_gibbsSpecificationOfFiniteReference_of_isLocalizedVersion ν β
    (τ := shift E (p : ℤ)) (fun _ ↦ MeasurePreserving.id ν) (isShiftInvariant_pairShift φ p)
    (c := 1) (C := |β| * B.toReal) zero_le_one le_rfl ?_ hμ
  intro Δ
  rcases Δ.eq_empty_or_nonempty with rfl | hΔ
  · refine ⟨∅, Transformation.id, fun _ ↦ MeasurePreserving.id ν,
      Transformation.isLocalizedVersion_id _ _, fun ω ↦ ?_⟩
    simp only [Potential.hamiltonian_empty, mul_zero, add_zero, sub_zero]
    positivity
  · obtain ⟨i₀, hi₀⟩ := hΔ
    set m := Δ.min' ⟨i₀, hi₀⟩ - p with hm
    set n := Δ.max' ⟨i₀, hi₀⟩ + p with hn
    have hmin := Δ.min'_le i₀ hi₀
    have hmax := Δ.le_max' i₀ hi₀
    have hL : 2 * (p : ℤ) + 1 ≤ n - m + 1 := by omega
    have hΔ' : Δ ⊆ Finset.Icc (m + p) (n - p) := fun i hi ↦
      Finset.mem_Icc.2 ⟨by have := Δ.min'_le i hi; omega, by have := Δ.le_max' i hi; omega⟩
    refine ⟨Finset.Icc m n, localizedShift E m n p (by positivity) (by omega),
      fun i ↦ by rw [localizedShift_spin]; exact MeasurePreserving.id ν,
      isLocalizedVersion_localizedShift E hΔ', fun ω ↦ ?_⟩
    have h := enorm_hamiltonian_localizedShift_sub_le φ hp hL ω
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_iff_le_toReal hB] at h
    simp only [one_mul, sub_self, zero_mul, add_zero]
    calc β * ((pairShift φ).hamiltonian (Finset.Icc m n)
            ((localizedShift E m n p (by positivity) (by omega)).toFun ω) -
          (pairShift φ).hamiltonian (Finset.Icc m n) ω)
        ≤ |β * ((pairShift φ).hamiltonian (Finset.Icc m n)
            ((localizedShift E m n p (by positivity) (by omega)).toFun ω) -
          (pairShift φ).hamiltonian (Finset.Icc m n) ω)| := le_abs_self _
      _ = |β| * |(pairShift φ).hamiltonian (Finset.Icc m n)
            ((localizedShift E m n p (by positivity) (by omega)).toFun ω) -
          (pairShift φ).hamiltonian (Finset.Icc m n) ω| := abs_mul _ _
      _ ≤ |β| * B.toReal := mul_le_mul_of_nonneg_left h (abs_nonneg β)

/-! ### From `θ_1` to every shift -/

lemma shift_toFun_eq_iterate (k : ℕ) : (shift E (k : ℤ)).toFun = (shift E 1).toFun^[k] := by
  induction k with
  | zero =>
    funext ω i
    simp
  | succ k ih =>
    funext ω i
    rw [Function.iterate_succ_apply', ← ih]
    simp only [shift_toFun_apply]
    congr 1
    push_cast
    ring

lemma shift_neg_toFun_eq_iterate (k : ℕ) :
    (shift E (-(k : ℤ))).toFun = (shift E 1).inv.toFun^[k] := by
  induction k with
  | zero =>
    funext ω i
    simp
  | succ k ih =>
    funext ω i
    rw [Function.iterate_succ_apply', ← ih]
    simp only [shift_toFun_apply, shift_inv_toFun_apply]
    congr 1
    push_cast
    ring

/-- A measure preserved by `θ_1` is preserved by every shift `θ_p`, `p ∈ ℤ`. -/
theorem measurePreserving_shift_of_one {μ : Measure (ℤ → E)}
    (h : MeasurePreserving (shift E (1 : ℤ)).toFun μ μ) (p : ℤ) :
    MeasurePreserving (shift E p).toFun μ μ := by
  have hinv : MeasurePreserving (shift E (1 : ℤ)).inv.toFun μ μ := by
    refine ⟨(shift E (1 : ℤ)).inv.measurable_toFun, ?_⟩
    conv_lhs => rw [← h.map_eq]
    rw [Measure.map_map (shift E (1 : ℤ)).inv.measurable_toFun (shift E (1 : ℤ)).measurable_toFun,
      show (shift E (1 : ℤ)).inv.toFun ∘ (shift E (1 : ℤ)).toFun = id from
        funext fun ω ↦ (shift E (1 : ℤ)).inv_toFun_toFun ω, Measure.map_id]
  rcases le_or_gt 0 p with hp | hp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [shift_toFun_eq_iterate]
    exact h.iterate k
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hp.le
    rw [shift_neg_toFun_eq_iterate]
    exact hinv.iterate k

/-! ### Georgii, Comment (9.7)(2) and Example (9.8)(1) -/

omit [MeasurableSpace E] in
/-- Georgii (9.7)(2), the arithmetic of the second half: for a decreasing `J ≥ 0` on `k ≥ 1`,
`∑_{k ≥ 1} k (J(k) − J(k+1)) ≤ ∑_{k ≥ 1} J(k)`. -/
lemma tsum_succ_mul_ofReal_sub_le {J : ℤ → ℝ} (hJ0 : ∀ k : ℕ, 0 ≤ J ((k : ℤ) + 1))
    (hanti : ∀ k : ℕ, J ((k : ℤ) + 2) ≤ J ((k : ℤ) + 1)) :
    ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (J ((k : ℤ) + 1) - J ((k : ℤ) + 2)) ≤
      ∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1)) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N ↦ ?_
  have hreal : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, ((k : ℝ) + 1) * (J ((k : ℤ) + 1) - J ((k : ℤ) + 2)) =
        ∑ k ∈ Finset.range N, J ((k : ℤ) + 1) - N * J ((N : ℤ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
        show ((N + 1 : ℕ) : ℤ) + 1 = (N : ℤ) + 2 by push_cast; ring]
      push_cast
      ring
  calc ∑ k ∈ Finset.range N, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (J ((k : ℤ) + 1) - J ((k : ℤ) + 2))
      = ENNReal.ofReal (∑ k ∈ Finset.range N,
          ((k : ℝ) + 1) * (J ((k : ℤ) + 1) - J ((k : ℤ) + 2))) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun k _ ↦
          mul_nonneg (by positivity) (sub_nonneg.2 (hanti k))]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    _ ≤ ENNReal.ofReal (∑ k ∈ Finset.range N, J ((k : ℤ) + 1)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hreal]
        have : 0 ≤ (N : ℝ) * J ((N : ℤ) + 1) := mul_nonneg (by positivity) (hJ0 N)
        linarith
    _ = ∑ k ∈ Finset.range N, ENNReal.ofReal (J ((k : ℤ) + 1)) :=
        ENNReal.ofReal_sum_of_nonneg fun k _ ↦ hJ0 k
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1)) := ENNReal.sum_le_tsum _

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(2), second half.** If `φ_k = J(k) ψ` with `ψ` bounded and `J ≥ 0`
decreasing on `k ≥ 1`, then `∑_{k ≥ 1} k ‖φ_{k+1} − φ_k‖ ≤ ‖ψ‖ ∑_{k ≥ 1} J(k)`: condition (9.6)
holds for `p = 1` as soon as `∑_k J(k) < ∞`. -/
theorem shiftDefect_mul_le {J : ℤ → ℝ} (hJ0 : ∀ k : ℕ, 0 ≤ J ((k : ℤ) + 1))
    (hanti : ∀ k : ℕ, J ((k : ℤ) + 2) ≤ J ((k : ℤ) + 1)) (ψ : E → E → ℝ) :
    shiftDefect (fun k x y ↦ J k * ψ x y) 1 ≤
      (∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1))) * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ := by
  have hpt : ∀ k : ℕ, pairDist (fun k x y ↦ J k * ψ x y) (k + 1 + 1) (k + 1) ≤
      ENNReal.ofReal (J ((k : ℤ) + 1) - J ((k : ℤ) + 2)) * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ := by
    intro k
    refine iSup₂_le fun x y ↦ ?_
    have : J ((k : ℤ) + 1 + 1) * ψ x y - J ((k : ℤ) + 1) * ψ x y =
        (J ((k : ℤ) + 1) - J ((k : ℤ) + 2)) * (-ψ x y) := by
      rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring]
      ring
    rw [this, enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sub_nonneg.2 (hanti k)),
      enorm_neg]
    exact mul_le_mul' le_rfl (le_iSup₂ (f := fun x y ↦ ‖ψ x y‖ₑ) x y)
  calc shiftDefect (fun k x y ↦ J k * ψ x y) 1
      ≤ ∑' k : ℕ, ((k : ℝ≥0∞) + 1) *
          (ENNReal.ofReal (J ((k : ℤ) + 1) - J ((k : ℤ) + 2)) * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ) :=
        ENNReal.tsum_le_tsum fun k ↦ mul_le_mul' le_rfl (hpt k)
    _ = (∑' k : ℕ, ((k : ℝ≥0∞) + 1) * ENNReal.ofReal (J ((k : ℤ) + 1) - J ((k : ℤ) + 2))) *
          ⨆ (x : E) (y : E), ‖ψ x y‖ₑ := by
        rw [← ENNReal.tsum_mul_right]
        simp_rw [mul_assoc]
    _ ≤ (∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1))) * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ :=
        mul_le_mul' (tsum_succ_mul_ofReal_sub_le hJ0 hanti) le_rfl

/-- **Georgii, Example (9.8)(1): the long-range Ising ferromagnet** on `ℤ`, in the form
`Φ_{{i, j}} = -β |i - j|^{-a} s(σ_i) s(σ_j)`, for a spin observable `s : E → ℝ` (Georgii:
`E = {-1, 1}` and `s = id`). -/
def longRangeIsing (s : E → ℝ) (β a : ℝ) : ℤ → E → E → ℝ :=
  fun k x y ↦ (k : ℝ) ^ (-a) * (-β * (s x * s y))

variable {s : E → ℝ} {β a : ℝ}

omit [MeasurableSpace E] in
lemma iSup_enorm_neg_mul_le (hs : ∀ x, |s x| ≤ 1) :
    ⨆ (x : E) (y : E), ‖-β * (s x * s y)‖ₑ ≤ ENNReal.ofReal |β| := by
  refine iSup₂_le fun x y ↦ ?_
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_neg, abs_mul]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : |s x| * |s y| ≤ 1 :=
    (mul_le_mul (hs x) (hs y) (abs_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
  calc |β| * (|s x| * |s y|) ≤ |β| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg β)
    _ = |β| := mul_one _

omit [MeasurableSpace E] in
lemma summable_rpow_succ (ha : 1 < a) : Summable fun k : ℕ ↦ ((k : ℝ) + 1) ^ (-a) := by
  have := (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-a)) 1).2
    (Real.summable_nat_rpow.2 (by linarith : -a < -1))
  refine this.congr fun k ↦ ?_
  push_cast
  rfl

omit [MeasurableSpace E] in
/-- The long-range Ising ferromagnet satisfies (9.6) with `p = 1` (Georgii, Example (9.8)(1),
via Comment (9.7)(2)): `k ↦ k^{-a}` is decreasing and summable for `a > 1`. -/
theorem shiftDefect_longRangeIsing_ne_top (ha : 1 < a) (hs : ∀ x, |s x| ≤ 1) :
    shiftDefect (longRangeIsing s β a) 1 ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (shiftDefect_mul_le (J := fun k : ℤ ↦ (k : ℝ) ^ (-a))
    (fun k ↦ by push_cast; exact Real.rpow_nonneg (by positivity) _)
    (fun k ↦ by
      push_cast
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith))
    (fun x y ↦ -β * (s x * s y)))
  refine ENNReal.mul_ne_top ?_ (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_enorm_neg_mul_le hs))
  refine ne_top_of_le_ne_top (summable_rpow_succ ha).tsum_ofReal_ne_top
    (le_of_eq (tsum_congr fun k ↦ ?_))
  push_cast
  rfl

/-- The long-range Ising ferromagnet is absolutely summable for `a > 1`. -/
theorem isAbsolutelySummable_pairShift_longRangeIsing (ha : 1 < a) (hs : ∀ x, |s x| ≤ 1) :
    IsAbsolutelySummable (pairShift (longRangeIsing s β a)) := by
  refine isAbsolutelySummable_pairShift _ (ne_top_of_le_ne_top
    (((summable_rpow_succ ha).mul_right |β|).tsum_ofReal_ne_top)
    (ENNReal.tsum_le_tsum fun k ↦ ?_))
  refine iSup₂_le fun x y ↦ ?_
  simp only [longRangeIsing]
  rw [enorm_mul, ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
  refine mul_le_mul' (le_of_eq ?_) ((le_iSup₂ (f := fun x y ↦ ‖-β * (s x * s y)‖ₑ) x y).trans
    (iSup_enorm_neg_mul_le hs))
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.rpow_nonneg (by push_cast; positivity) _)]
  push_cast
  rfl

/-- The long-range Ising ferromagnet is a potential when the spin observable is measurable. -/
theorem isPotential_pairShift_longRangeIsing (hs : Measurable s) :
    IsPotential (pairShift (longRangeIsing s β a)) :=
  isPotential_pairShift _ fun k ↦ by
    unfold longRangeIsing Function.uncurry
    exact measurable_const.mul (measurable_const.mul
      ((hs.comp measurable_fst).mul (hs.comp measurable_snd)))

/-- **Georgii, Example (9.8)(1).** For the long-range Ising ferromagnet `Φ` with `a > 1` on
`ℤ`, `𝒢(Φ) = 𝒢_Θ(Φ)`: every Gibbs measure is invariant under every shift. (Georgii: this is
non-trivial when `1 < a ≤ 2` and `β` is large, where the spin-flip symmetry is broken.) -/
theorem measurePreserving_shift_longRangeIsing [StandardBorelSpace E] (hsm : Measurable s)
    (hs : ∀ x, |s x| ≤ 1) (ha : 1 < a) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β' : ℝ)
    {μ : Measure (ℤ → E)}
    (hμ : haveI := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
      haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
      μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsing s β a)) ν β'))
    (p : ℤ) : MeasurePreserving (shift E p).toFun μ μ := by
  have := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
  refine measurePreserving_shift_of_one ?_ p
  have := measurePreserving_shift_of_shiftDefect_ne_top (longRangeIsing s β a) ν β'
    Nat.one_pos (shiftDefect_longRangeIsing_ne_top ha hs) hμ
  simpa using this

end MeasureTheory.GibbsMeasure

end

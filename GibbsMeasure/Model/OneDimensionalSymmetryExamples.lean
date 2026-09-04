/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.OneDimensionalSymmetry
public import GibbsMeasure.Specification.OneDimensionalUniqueness
public import GibbsMeasure.Mathlib.Algebra.Order.SecondDifference
public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Model.InhomogeneousIsingChain
public import GibbsMeasure.Specification.Pullback
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Georgii §9.1: comments and examples

The comments and examples accompanying Theorems (9.5) and (9.11) of Georgii, *Gibbs Measures and
Phase Transitions*, §9.1, on top of `GibbsMeasure/Model/OneDimensionalSymmetry.lean`.

## Comments (9.7) on condition (9.6)

* `MeasureTheory.GibbsMeasure.shiftDefectSubgroup`: **Comment (9.7)(1)**, the integers `p`
  satisfying (9.6) form a subgroup of `ℤ` (`shiftDefect_add_le`, `shiftDefect_sub_le`), and
  `MeasureTheory.GibbsMeasure.shiftInvariantSubgroup`: the periods common to a set of measures
  form a subgroup, so `{p : θ_p(μ) = μ for all μ ∈ 𝒢(Φ)}` is a subgroup as well;
  `measurePreserving_shift_of_mem_shiftDefectSubgroup` is Theorem (9.5) for every element of the
  first subgroup.
* `MeasureTheory.GibbsMeasure.tsum_pairNorm_le_shiftDefect`: **Comment (9.7)(2), first half**:
  if `‖φ_k‖ → 0` then `∑_{k ≥ 1} ‖φ_k‖ ≤ ∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖` for every `p ≥ 1`, by
  the telescoping bound `‖φ_k‖ ≤ ∑_{n ≥ k} ‖φ_{n+p} − φ_n‖`; `shiftDefect_mul_eq` is the
  equality case of the second half (`shiftDefect_mul_le` in `OneDimensionalSymmetry.lean`).
* `MeasureTheory.GibbsMeasure.shiftDefect_recentre_le`: **Comment (9.7)(3)**: for `Φ` of the
  form (9.4), `φ̃_k = φ_k − inf φ_k` (`recentre`) satisfies
  `∑_k k ‖φ̃_{k+p} − φ̃_k‖ ≤ 2 ∑_{k ≥ 1} k δ(φ_k)`, i.e. (9.6) for every `p` under Georgii's
  uniqueness condition (8.42) (`oscSpanDiam`), and `Φ̃` is equivalent to `Φ`
  (`isEquivalent_pairShift_recentre`).

## Example (9.8)(2): the long-range antiferromagnet

* `MeasureTheory.GibbsMeasure.longRangeIsingAlt`: `Φ̃_{{i,j}} = −β (−1)^{i+j} |i − j|^{-a} σ_i σ_j`,
  and `measurePreserving_shift_two_longRangeIsingAlt`: every `μ ∈ 𝒢(Φ̃)` is `θ_2`-invariant
  ((9.6) holds for `p = 2`, `shiftDefect_longRangeIsingAlt_two_ne_top`).
* `map_alternatingFlip_pairShift_longRangeIsing`: `Φ̃ = τ(Φ)` for `(τ ω)_i = (−1)^i ω_i`
  (`alternatingFlip`, an involution: `alternatingFlip_mul_self`), so the involution `μ ↦ τ(μ)`
  is a bijection `𝒢(Φ) ↔ 𝒢(Φ̃)` (`bijOn_map_alternatingFlip`, from
  `map_alternatingFlip_mem_G_longRangeIsingAlt` and `map_alternatingFlip_mem_G_longRangeIsing`);
  `alternatingFlip_mul_shift_two` is `τ θ_2 = θ_2 τ`, so `θ_2`-invariance transfers along `τ`
  (`measurePreserving_shift_two_map_alternatingFlip`, Mathlib's
  `MeasurePreserving.of_semiconj`), and `exists_not_measurePreserving_shift_one_longRangeIsingAlt`:
  a breaking of the spin-flip symmetry in `𝒢(Φ)` is a breaking of `θ_1` in `𝒢(Φ̃)`. Georgii's
  input that the spin flip *is* broken for `1 < a ≤ 2` and large `β` is Theorem (20.21), not in
  this library; it is the explicit hypothesis of that theorem.

## Comments (9.13) on condition (9.12)

* `MeasureTheory.GibbsMeasure.pairOscBound`: **(9.14)**,
  `sup_n ∑_{i ≤ n < j} sup_{x,y} |φ_{ij}(τ_i x, y) − φ_{ij}(x, y)|`, and
  `pairDefectBound_le_two_mul_pairOscBound`: **Comment (9.13)(1)**, (9.14) implies (9.12) for a
  symmetry `τ`.
* `pairDefectBound_pow_le`: **Comment (9.13)(2)**, `C(Φ, τ^k) ≤ k² C(Φ, τ)` (and
  `pairDefectBound_inv` for `τ⁻¹`), from the second-difference bound
  `add_neg_sub_two_mul_le_natCast_sq_mul_of_forall_le`; `pairOscSymmetries`: the symmetries of
  `Φ` in `T_λ⁰` satisfying (9.14) form a subgroup.
* `pairOscBound_le_iSup_oscSpan`: **Comment (9.13)(3)**, Georgii's uniqueness condition (8.40)
  (`oscSpan`) implies (9.14), and a fortiori (9.12).
* Comment (9.13)(4) refers forward to (9.34)(2) (§9.3) and is not treated here.

## Example (9.15)

* `MeasureTheory.GibbsMeasure.squarePotential J K`: the nearest-neighbour potential
  `φ_{i,i+1}(x, y) = −J_i x₁ y₁ − K x₁ x₂ y₁ y₂` on `S = ℕ`, `E = {−1, 1}²`; `squareFlip₁`,
  `squareFlip₂` are the reflections `τ⁽¹⁾, τ⁽²⁾`, both symmetries
  (`map_squareFlip₁_squarePotential`, `map_squareFlip₂_squarePotential`).
* `pairOscBound_squareFlip₂`: the expression (9.14) for `τ⁽²⁾` equals `2K`, and
  `measurePreserving_squareFlip₂`: every `μ ∈ 𝒢(Φ)` is `τ⁽²⁾`-invariant (Theorem (9.11)).
* `not_measurePreserving_squareFlip₁_of_integral_pos`: a measure with `μ(σ_{i1}) > 0` is not
  `τ⁽¹⁾`-invariant. Georgii obtains such a `μ₊ ∈ 𝒢(Φ)` from Theorem (6.4) (`K = 0`) and from
  Griffiths' inequalities (`K > 0`, the existence of the limit `lim γ_{[1,N]}(·|ω⁺)` and its
  monotonicity in `K`). For an arbitrary specification the existence of `μ₊` is the hypothesis of
  `exists_not_measurePreserving_squareFlip₁`; at `K = 0` it is a **theorem**,
  `exists_not_measurePreserving_squareFlip₁_of_summable`, at every inverse temperature `β > 0`
  under Georgii's condition (6.1) for `βJ`: the
  potential is then the pullback of the inhomogeneous chain potential (6.2) along the projection
  onto the first layer (`comap_fst_isingChainPotential`), so Theorem (6.4)
  (`exists_mem_G_integral_spin_pos`) and the transport of `GibbsMeasure/Specification/Pullback.lean`
  produce `μ₊ = μ₊^{(6.4)} ⊗ λ^ℕ`. For `K > 0` the existence of `μ₊` is still open here: the
  finite-volume GKS inequalities of `Model/GKSInequalities.lean` are stated for `V → Bool` spins
  and a general ferromagnetic multi-body interaction — which does cover the two-layer chain on
  `V = Λ × Fin 2` — but the bridge from `γ_{Λ_N}(·|ω⁺)` for `E = Bool × Bool` to `GKS.corr`
  (the analogue of `Model/LebowitzMartinLof.lean`'s `fvMag_eq_corr` for the single-layer Ising
  model) is not written, and neither is the `N → ∞` limit for the two-layer chain.

## Example (9.17)

* `MeasureTheory.GibbsMeasure.gradientPotential u`: `φ_{i,i+1}(x, y) = u(y − x)` on `S = ℤ` over
  an additive group `E` with a translation-invariant `λ` (Lebesgue measure on `ℝ`, counting
  measure on `ℤ`); `isSigmaFiniteLambdaAdmissible_gradientPotential` is the λ-admissibility
  computation `λ_Λ h_Λ ≤ λ(e^{-u})^{|Λ|}`, by integrating out the sites of `Λ` from the top
  (`lmarginal_prod_translate_eq_pow`, Mathlib's `lmarginal`).
* `pairDefectBound_gradientPotential`: `C(Φ, τ) = c(u) = sup_x [u(x+1) + u(x−1) − 2u(x)]₊` for
  the spin translation `τ ω = (ω_i + 1)_i` (`constSpinTranslation`).
* `G_gradientPotential_eq_empty`: **Example (9.17)**: `𝒢(Φ) = ∅` when `λ(e^{-u}) < ∞`,
  `c(u) < ∞` and `u(x + k) → ∞`; `G_gaussianGradient_eq_empty` is the case `E = ℝ`, Lebesgue
  measure, `u(x) = β x²` (`β > 0`), where `λ(e^{-u}) = √(π/β)` is finite by Mathlib's Gaussian
  integral and `c(u) = 2β`, and `G_intGaussianGradient_eq_empty` the case `E = ℤ`, counting
  measure, `u(x) = β x²` of Georgii's closing remark (the one-dimensional potential (6.16)).
  Georgii's other instances `u(x) = β |x|^p`, `0 < p < 2`, are not treated.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Georgii, Comment (9.7)(1): the periods satisfying (9.6) form a subgroup -/

namespace MeasureTheory.GibbsMeasure

open Potential

variable {E : Type*} [MeasurableSpace E] (φ : ℤ → E → E → ℝ)

omit [MeasurableSpace E] in
@[simp] lemma shiftDefect_zero : shiftDefect φ 0 = 0 := by
  simp [shiftDefect]

omit [MeasurableSpace E] in
/-- Shifting the summation index of (9.6): `∑_k (k + 1) ‖φ_{k+r+1+q} − φ_{k+r+1}‖ ≤
∑_m (m + 1) ‖φ_{m+1+q} − φ_{m+1}‖`. -/
private lemma tsum_succ_mul_pairDist_add_le (r q : ℕ) :
    ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * pairDist φ (((k + r : ℕ) : ℤ) + 1 + q) (((k + r : ℕ) : ℤ) + 1) ≤
      shiftDefect φ q := by
  calc ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * pairDist φ (((k + r : ℕ) : ℤ) + 1 + q) (((k + r : ℕ) : ℤ) + 1)
      ≤ ∑' k : ℕ, (fun m : ℕ ↦ ((m : ℝ≥0∞) + 1) * pairDist φ (m + 1 + q) (m + 1)) (k + r) := by
        refine ENNReal.tsum_le_tsum fun k ↦ ?_
        dsimp only
        refine mul_le_mul' ?_ le_rfl
        push_cast
        exact add_le_add le_self_add le_rfl
    _ ≤ shiftDefect φ q := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective r) _

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(1)**, closure under addition: (9.6) for `p` and `q` gives (9.6) for
`p + q`. -/
theorem shiftDefect_add_le (p q : ℕ) :
    shiftDefect φ (p + q) ≤ shiftDefect φ p + shiftDefect φ q := by
  calc shiftDefect φ (p + q)
      ≤ ∑' k : ℕ, (((k : ℝ≥0∞) + 1) *
          pairDist φ (((k + p : ℕ) : ℤ) + 1 + q) (((k + p : ℕ) : ℤ) + 1) +
        ((k : ℝ≥0∞) + 1) * pairDist φ (k + 1 + p) (k + 1)) := by
        refine ENNReal.tsum_le_tsum fun k ↦ ?_
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        have h1 : ((k : ℤ) + 1 + ((p + q : ℕ) : ℤ)) = ((k + p : ℕ) : ℤ) + 1 + q := by
          push_cast; ring
        have h2 : ((k : ℤ) + 1 + (p : ℤ)) = ((k + p : ℕ) : ℤ) + 1 := by push_cast; ring
        rw [h1, ← h2]
        exact pairDist_le_add φ _ _ _
    _ = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) *
          pairDist φ (((k + p : ℕ) : ℤ) + 1 + q) (((k + p : ℕ) : ℤ) + 1) + shiftDefect φ p :=
        ENNReal.tsum_add
    _ ≤ shiftDefect φ q + shiftDefect φ p :=
        add_le_add (tsum_succ_mul_pairDist_add_le φ p q) le_rfl
    _ = shiftDefect φ p + shiftDefect φ q := add_comm _ _

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(1)**, closure under subtraction: (9.6) for `p` and `q ≤ p` gives
(9.6) for `p − q`. -/
theorem shiftDefect_sub_le {p q : ℕ} (hqp : q ≤ p) :
    shiftDefect φ (p - q) ≤ shiftDefect φ p + shiftDefect φ q := by
  calc shiftDefect φ (p - q)
      ≤ ∑' k : ℕ, (((k : ℝ≥0∞) + 1) *
          pairDist φ (((k + (p - q) : ℕ) : ℤ) + 1 + q) (((k + (p - q) : ℕ) : ℤ) + 1) +
        ((k : ℝ≥0∞) + 1) * pairDist φ (k + 1 + p) (k + 1)) := by
        refine ENNReal.tsum_le_tsum fun k ↦ ?_
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        have h1 : ((k : ℤ) + 1 + ((p - q : ℕ) : ℤ)) = ((k + (p - q) : ℕ) : ℤ) + 1 := by
          push_cast; ring
        have h2 : ((k : ℤ) + 1 + (p : ℤ)) = ((k + (p - q) : ℕ) : ℤ) + 1 + q := by
          push_cast [Nat.cast_sub hqp]; ring
        rw [h1, pairDist_comm φ (((k + (p - q) : ℕ) : ℤ) + 1 + q), ← h2]
        exact pairDist_le_add φ _ _ _
    _ = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) *
          pairDist φ (((k + (p - q) : ℕ) : ℤ) + 1 + q) (((k + (p - q) : ℕ) : ℤ) + 1) +
        shiftDefect φ p := ENNReal.tsum_add
    _ ≤ shiftDefect φ q + shiftDefect φ p :=
        add_le_add (tsum_succ_mul_pairDist_add_le φ (p - q) q) le_rfl
    _ = shiftDefect φ p + shiftDefect φ q := add_comm _ _

omit [MeasurableSpace E] in
private lemma natAbs_add_cases (p q : ℤ) :
    (p + q).natAbs = p.natAbs + q.natAbs ∨ (p + q).natAbs + q.natAbs = p.natAbs ∨
      (p + q).natAbs + p.natAbs = q.natAbs := by
  omega

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(1).** The set of all integers `p` satisfying (9.6) is a subgroup of
`ℤ`. (9.6) is read at `|p|`, as `θ_p`-invariance and `θ_{-p}`-invariance are the same
condition.) -/
def shiftDefectSubgroup : AddSubgroup ℤ where
  carrier := {p | shiftDefect φ p.natAbs ≠ ⊤}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    simp only [Set.mem_ofPred_eq] at hp hq ⊢
    rcases natAbs_add_cases p q with h | h | h
    · rw [h]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hp, hq⟩) (shiftDefect_add_le φ _ _)
    · rw [show (p + q).natAbs = p.natAbs - q.natAbs by omega]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hp, hq⟩)
        (shiftDefect_sub_le φ (by omega))
    · rw [show (p + q).natAbs = q.natAbs - p.natAbs by omega]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hq, hp⟩)
        (shiftDefect_sub_le φ (by omega))
  neg_mem' := by
    intro p hp
    simpa using hp

omit [MeasurableSpace E] in
lemma mem_shiftDefectSubgroup_iff {p : ℤ} :
    p ∈ shiftDefectSubgroup φ ↔ shiftDefect φ p.natAbs ≠ ⊤ := Iff.rfl

variable {φ}

/-- A measure preserved by `θ_j` is preserved by `θ_{-j}`. -/
lemma measurePreserving_shift_neg {S : Type*} [AddGroup S] {j : S} {μ : Measure (S → E)}
    (h : MeasurePreserving (shift E j).toFun μ μ) :
    MeasurePreserving (shift E (-j)).toFun μ μ := by
  rw [shift_neg_toFun_eq]
  exact (MeasurePreserving.symm (shift E j).toMeasurableEquiv h)

lemma shift_zero_toFun_eq {S : Type*} [AddGroup S] : (shift E (0 : S)).toFun = id := by
  funext ω i
  simp

variable (E) in
/-- **Georgii, Comment (9.7)(1).** The common periods of a set `M` of measures,
`{p : θ_p(μ) = μ for all μ ∈ M}`, form a subgroup of the group of sites; Georgii's case is
`S = ℤ` and `M = 𝒢(Φ)`. -/
def shiftInvariantSubgroup {S : Type*} [AddGroup S] (M : Set (Measure (S → E))) :
    AddSubgroup S where
  carrier := {j | ∀ μ ∈ M, MeasurePreserving (shift E j).toFun μ μ}
  zero_mem' μ _ := by
    rw [shift_zero_toFun_eq]
    exact MeasurePreserving.id μ
  add_mem' {j k} hj hk μ hμ := by
    rw [shift_add_toFun_eq]
    exact (hk μ hμ).comp (hj μ hμ)
  neg_mem' {j} hj μ hμ := measurePreserving_shift_neg (hj μ hμ)

lemma mem_shiftInvariantSubgroup_iff {S : Type*} [AddGroup S] {M : Set (Measure (S → E))}
    {j : S} :
    j ∈ shiftInvariantSubgroup E M ↔ ∀ μ ∈ M, MeasurePreserving (shift E j).toFun μ μ :=
  Iff.rfl

/-- **Georgii, Theorem (9.5) on the subgroup of Comment (9.7)(1)**: every period `p ∈ ℤ`
satisfying (9.6) is a period of every Gibbs measure, i.e. the subgroup of (9.7)(1) is contained
in the subgroup of common periods of `𝒢(Φ)`. -/
theorem measurePreserving_shift_of_mem_shiftDefectSubgroup [StandardBorelSpace E]
    [IsPotential (pairShift φ)] [IsAbsolutelySummable (pairShift φ)]
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) {p : ℤ}
    (hp : p ∈ shiftDefectSubgroup φ) {μ : Measure (ℤ → E)}
    (hμ : μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift φ) ν β)) :
    MeasurePreserving (shift E p).toFun μ μ := by
  rw [mem_shiftDefectSubgroup_iff] at hp
  rcases lt_trichotomy p 0 with hneg | rfl | hpos
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨p.natAbs, by omega⟩
    have hn0 : 0 < n := by omega
    rw [hn]
    refine measurePreserving_shift_neg ?_
    have := measurePreserving_shift_of_shiftDefect_ne_top φ ν β hn0
      (by simpa [hn] using hp) hμ
    exact this
  · rw [shift_zero_toFun_eq]
    exact MeasurePreserving.id μ
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    exact measurePreserving_shift_of_shiftDefect_ne_top φ ν β (by omega)
      (by simpa using hp) hμ

theorem shiftDefectSubgroup_le_shiftInvariantSubgroup [StandardBorelSpace E]
    [IsPotential (pairShift φ)] [IsAbsolutelySummable (pairShift φ)]
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    shiftDefectSubgroup φ ≤
      shiftInvariantSubgroup E (G (gibbsSpecificationOfFiniteReference (pairShift φ) ν β)) :=
  fun _ hp _ hμ ↦ measurePreserving_shift_of_mem_shiftDefectSubgroup ν β hp hμ

/-! ### Georgii, Comment (9.7)(2), first half: the telescoping bound -/

omit [MeasurableSpace E] in
/-- `∑_{k} ∑_{n ≥ k} d_n = ∑_n (n + 1) d_n`. -/
private lemma tsum_tsum_ite_le_eq (d : ℕ → ℝ≥0∞) :
    ∑' k : ℕ, ∑' n : ℕ, (if k ≤ n then d n else 0) = ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * d n := by
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun n ↦ ?_
  rw [tsum_eq_sum (s := Finset.range (n + 1)) fun k hk ↦
    ite_eq_right (by simpa [Nat.lt_succ_iff] using hk)]
  rw [Finset.sum_congr rfl fun k hk ↦ ite_eq_left (by simpa [Nat.lt_succ_iff] using hk),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_succ]

omit [MeasurableSpace E] in
/-- Georgii, Comment (9.7)(2): `φ_k = ∑_{ℓ ≥ 0} (φ_{k+ℓp} − φ_{k+ℓp+p})` when `‖φ_k‖ → 0`, hence
`‖φ_k‖ ≤ ∑_{n ≥ k} ‖φ_{n+p} − φ_n‖`. -/
lemma pairNorm_le_tsum_pairDist (htend : Tendsto (fun k : ℕ ↦ pairNorm φ (k + 1)) atTop (𝓝 0))
    {p : ℕ} (hp : 0 < p) (k : ℕ) :
    pairNorm φ (k + 1) ≤ ∑' n : ℕ, (if k ≤ n then pairDist φ (n + 1 + p) (n + 1) else 0) := by
  set d : ℕ → ℝ≥0∞ := fun n ↦ pairDist φ (n + 1 + p) (n + 1) with hd
  have hN : ∀ N : ℕ, pairNorm φ (k + 1) ≤
      (∑ ℓ ∈ Finset.range N, d (k + ℓ * p)) + pairNorm φ (((k + N * p : ℕ) : ℤ) + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, add_assoc]
      refine add_le_add le_rfl ?_
      refine iSup₂_le fun x y ↦ ?_
      have e1 : ((k + N * p : ℕ) : ℤ) + 1 + p = ((k + (N + 1) * p : ℕ) : ℤ) + 1 := by
        push_cast; ring
      calc ‖φ (((k + N * p : ℕ) : ℤ) + 1) x y‖ₑ
          = ‖(φ (((k + N * p : ℕ) : ℤ) + 1) x y - φ (((k + N * p : ℕ) : ℤ) + 1 + p) x y) +
              φ (((k + N * p : ℕ) : ℤ) + 1 + p) x y‖ₑ := by ring_nf
        _ ≤ ‖φ (((k + N * p : ℕ) : ℤ) + 1) x y - φ (((k + N * p : ℕ) : ℤ) + 1 + p) x y‖ₑ +
              ‖φ (((k + N * p : ℕ) : ℤ) + 1 + p) x y‖ₑ := enorm_add_le _ _
        _ ≤ d (k + N * p) + pairNorm φ (((k + (N + 1) * p : ℕ) : ℤ) + 1) := by
            refine add_le_add ?_ ?_
            · simp only [hd]
              rw [pairDist_comm]
              exact enorm_sub_le_pairDist φ _ _ x y
            · rw [← e1]
              exact enorm_le_pairNorm φ _ x y
  have hsum : ∀ N : ℕ, ∑ ℓ ∈ Finset.range N, d (k + ℓ * p) ≤
      ∑' n : ℕ, (if k ≤ n then d n else 0) := by
    intro N
    have hinj : Function.Injective fun ℓ : ℕ ↦ k + ℓ * p := fun a b h ↦ by
      simp only at h
      exact Nat.eq_of_mul_eq_mul_right hp (by omega)
    calc ∑ ℓ ∈ Finset.range N, d (k + ℓ * p)
        = ∑ n ∈ (Finset.range N).image (fun ℓ ↦ k + ℓ * p), (if k ≤ n then d n else 0) := by
          rw [Finset.sum_image fun a _ b _ h ↦ hinj h]
          exact Finset.sum_congr rfl fun ℓ _ ↦ (ite_eq_left (Nat.le_add_right _ _)).symm
      _ ≤ ∑' n : ℕ, (if k ≤ n then d n else 0) := ENNReal.sum_le_tsum _
  have hlim : Tendsto (fun N : ℕ ↦ pairNorm φ (((k + N * p : ℕ) : ℤ) + 1)) atTop (𝓝 0) := by
    refine htend.comp (tendsto_atTop_mono (fun N ↦ ?_) tendsto_id)
    simp only [id]
    nlinarith
  have htend' : Tendsto (fun N : ℕ ↦ (∑' n : ℕ, (if k ≤ n then d n else 0)) +
      pairNorm φ (((k + N * p : ℕ) : ℤ) + 1)) atTop
      (𝓝 ((∑' n : ℕ, (if k ≤ n then d n else 0)) + 0)) :=
    tendsto_const_nhds.add hlim
  have := ge_of_tendsto' htend' fun N ↦ (hN N).trans (add_le_add (hsum N) le_rfl)
  simpa using this

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(2), first half.** If `‖φ_k‖ → 0`, then
`∑_{k ≥ 1} ‖φ_k‖ ≤ ∑_{k ≥ 1} k ‖φ_{k+p} − φ_k‖` for every `p ≥ 1`: condition (9.6) implies
absolute summability of the potential (9.4). -/
theorem tsum_pairNorm_le_shiftDefect
    (htend : Tendsto (fun k : ℕ ↦ pairNorm φ (k + 1)) atTop (𝓝 0)) {p : ℕ} (hp : 0 < p) :
    ∑' k : ℕ, pairNorm φ (k + 1) ≤ shiftDefect φ p := by
  calc ∑' k : ℕ, pairNorm φ (k + 1)
      ≤ ∑' k : ℕ, ∑' n : ℕ, (if k ≤ n then pairDist φ (n + 1 + p) (n + 1) else 0) :=
        ENNReal.tsum_le_tsum fun k ↦ pairNorm_le_tsum_pairDist htend hp k
    _ = shiftDefect φ p := tsum_tsum_ite_le_eq _

omit [MeasurableSpace E] in
lemma pairNorm_mul (J : ℤ → ℝ) (ψ : E → E → ℝ) (k : ℤ) :
    pairNorm (fun k x y ↦ J k * ψ x y) k = ENNReal.ofReal |J k| * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ := by
  simp only [pairNorm, enorm_mul, Real.enorm_eq_ofReal_abs (J k), ENNReal.mul_iSup]

omit [MeasurableSpace E] in
/-- **Georgii, Comment (9.7)(2), the equality case.** For `φ_k = J(k) ψ` with `ψ` bounded and
`J ≥ 0` decreasing and summable on `k ≥ 1`,
`∑_{k ≥ 1} k ‖φ_{k+1} − φ_k‖ = ‖ψ‖ ∑_{k ≥ 1} J(k)`. -/
theorem shiftDefect_mul_eq {J : ℤ → ℝ} (hJ0 : ∀ k : ℕ, 0 ≤ J ((k : ℤ) + 1))
    (hanti : ∀ k : ℕ, J ((k : ℤ) + 2) ≤ J ((k : ℤ) + 1))
    (hsum : Summable fun k : ℕ ↦ J ((k : ℤ) + 1)) {ψ : E → E → ℝ}
    (hψ : (⨆ (x : E) (y : E), ‖ψ x y‖ₑ) ≠ ⊤) :
    shiftDefect (fun k x y ↦ J k * ψ x y) 1 =
      (∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1))) * ⨆ (x : E) (y : E), ‖ψ x y‖ₑ := by
  refine le_antisymm (shiftDefect_mul_le hJ0 hanti ψ) ?_
  set B := ⨆ (x : E) (y : E), ‖ψ x y‖ₑ
  have hnorm : ∀ k : ℕ, pairNorm (fun k x y ↦ J k * ψ x y) (k + 1) =
      ENNReal.ofReal (J ((k : ℤ) + 1)) * B := fun k ↦ by
    rw [pairNorm_mul, abs_of_nonneg (hJ0 k)]
  have htend : Tendsto (fun k : ℕ ↦ pairNorm (fun k x y ↦ J k * ψ x y) (k + 1)) atTop (𝓝 0) := by
    simp_rw [hnorm]
    have := ENNReal.Tendsto.mul_const (b := B) (ENNReal.tendsto_ofReal hsum.tendsto_atTop_zero)
      (Or.inr hψ)
    simpa using this
  calc (∑' k : ℕ, ENNReal.ofReal (J ((k : ℤ) + 1))) * B
      = ∑' k : ℕ, pairNorm (fun k x y ↦ J k * ψ x y) (k + 1) := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun k ↦ (hnorm k).symm
    _ ≤ shiftDefect (fun k x y ↦ J k * ψ x y) 1 :=
        tsum_pairNorm_le_shiftDefect htend Nat.one_pos

/-! ### Georgii, Comment (9.7)(3): condition (8.42) implies (9.6) after recentring -/

variable (φ)

omit [MeasurableSpace E] in
/-- Georgii, Comment (9.7)(3): `φ̃_k = φ_k − inf φ_k`. -/
def recentre : ℤ → E → E → ℝ :=
  fun k x y ↦ φ k x y - sInf (Set.range fun q : E × E ↦ φ k q.1 q.2)

lemma pairShift_sub_pairShift_recentre (A : Finset ℤ) (η : ℤ → E) :
    (pairShift φ - pairShift (recentre φ)) A η =
      pairTerms (fun i j : ℤ ↦ sInf (Set.range fun q : E × E ↦ φ (j - i) q.1 q.2)) A := by
  simp only [Potential.sub_apply, pairShift, pair_apply, recentre]
  rw [← pairTerms_sub]
  exact pairTerms_congr (fun i j _ ↦ by ring) A

/-- **Georgii, Comment (9.7)(3).** `Φ̃` is equivalent to `Φ`: the two potentials differ by the
constants `inf φ_k`, so the Hamiltonian of the difference does not depend on the configuration
at all. -/
theorem isEquivalent_pairShift_recentre :
    IsEquivalent (pairShift φ) (pairShift (recentre φ)) := by
  intro Λ
  have hconst : ∀ η η' : ℤ → E,
      (pairShift φ - pairShift (recentre φ)).hamiltonian Λ η =
        (pairShift φ - pairShift (recentre φ)).hamiltonian Λ η' := by
    intro η η'
    unfold Potential.hamiltonian
    congr 1
    funext A
    simp only [hamiltonianTerms, Set.indicator, pairShift_sub_pairShift_recentre]
  rcases isEmpty_or_nonempty (ℤ → E) with h | ⟨⟨η₀⟩⟩
  · exact @Subsingleton.measurable _ _ _ (cylinderEvents ((Λ : Set ℤ))ᶜ) _ _
  · have : (pairShift φ - pairShift (recentre φ)).hamiltonian Λ =
        fun _ ↦ (pairShift φ - pairShift (recentre φ)).hamiltonian Λ η₀ :=
      funext fun η ↦ hconst η η₀
    rw [this]
    exact measurable_const

/-- Georgii, Comment (9.7)(3): `‖φ_k − inf φ_k‖ ≤ δ(φ_k)`, the oscillation of `Φ_{{0,k}}`. -/
lemma enorm_recentre_le_osc {k : ℤ} (hk : 0 < k) (x y : E) :
    ‖recentre φ k x y‖ₑ ≤ Dobrushin.osc (pairShift φ {0, k}) := by
  set δ := Dobrushin.osc (pairShift φ {0, k}) with hδ
  by_cases hδtop : δ = ⊤
  · rw [hδtop]; exact le_top
  set f : E × E → ℝ := fun q ↦ φ k q.1 q.2 with hf
  have hbound : ∀ q q' : E × E, |f q - f q'| ≤ δ.toReal := by
    intro q q'
    classical
    let ζ : ℤ → E := fun i ↦ if i = 0 then q.1 else q.2
    let η : ℤ → E := fun i ↦ if i = 0 then q'.1 else q'.2
    have h := Dobrushin.le_osc (pairShift φ {0, k}) ζ η
    rw [pairShift_pair φ hk, pairShift_pair φ hk] at h
    simp only [ζ, η, ite_eq_left rfl, ite_eq_right hk.ne', sub_zero] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hδtop).1 h
  have hbdd : BddBelow (Set.range f) := ⟨f (x, y) - δ.toReal, by
    rintro _ ⟨q, rfl⟩
    have := hbound (x, y) q
    rw [abs_le] at this
    linarith⟩
  have h1 : sInf (Set.range f) ≤ f (x, y) := csInf_le hbdd (Set.mem_range_self _)
  have h2 : f (x, y) - δ.toReal ≤ sInf (Set.range f) := by
    refine le_csInf ⟨f (x, y), Set.mem_range_self _⟩ ?_
    rintro _ ⟨q, rfl⟩
    have := hbound (x, y) q
    rw [abs_le] at this
    linarith
  rw [recentre, Real.enorm_eq_ofReal_abs, abs_of_nonneg (by simpa [f] using sub_nonneg.2 h1)]
  refine (ENNReal.ofReal_le_ofReal (by simpa [f] using sub_le_comm.1 h2)).trans ?_
  rw [ENNReal.ofReal_toReal hδtop]

/-- The interaction terms of a pair potential other than the pairs have no oscillation. -/
lemma osc_pairShift_eq_zero_of_not_pair (A : Finset ℤ) (hA : ∀ a b : ℤ, a < b → A ≠ {a, b}) :
    Dobrushin.osc (pairShift φ A) = 0 := by
  rw [pairShift, pair_eq_zero _ hA]
  exact Dobrushin.osc_const 0

/-- `∑_{n ≥ 1} n δ(φ_n) ≤` the sum (8.42). -/
lemma tsum_succ_mul_osc_le_oscSpanDiam :
    ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * Dobrushin.osc (pairShift φ {0, ((n : ℤ) + 1)}) ≤
      oscSpanDiam (pairShift φ) := by
  rw [oscSpanDiam_eq_tsum_pair fun A _ hA ↦ osc_pairShift_eq_zero_of_not_pair φ A hA]
  calc ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * Dobrushin.osc (pairShift φ {0, ((n : ℤ) + 1)})
      = ∑' n : ℕ, (fun m : ℕ ↦ (m : ℝ≥0∞) * Dobrushin.osc (pairShift φ {0, (m : ℤ)})) (n + 1) := by
        refine tsum_congr fun n ↦ ?_
        push_cast
        rfl
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective 1) _

/-- **Georgii, Comment (9.7)(3).** For `Φ` of the form (9.4), the recentred potential
`φ̃_k = φ_k − inf φ_k` satisfies `∑_{k ≥ 1} k ‖φ̃_{k+p} − φ̃_k‖ ≤ 2 ∑_{k ≥ 1} k δ(φ_k)`, the right
side being twice Georgii's sum (8.42): condition (8.42) implies (9.6) for every `p`. -/
theorem shiftDefect_recentre_le (p : ℕ) :
    shiftDefect (recentre φ) p ≤ 2 * oscSpanDiam (pairShift φ) := by
  set δ : ℕ → ℝ≥0∞ := fun n ↦ Dobrushin.osc (pairShift φ {0, ((n : ℤ) + 1)}) with hδ
  have hpt : ∀ k : ℕ, ((k : ℝ≥0∞) + 1) * pairDist (recentre φ) (k + 1 + p) (k + 1) ≤
      ((k : ℝ≥0∞) + 1) * δ (k + p) + ((k : ℝ≥0∞) + 1) * δ k := by
    intro k
    rw [← mul_add]
    refine mul_le_mul' le_rfl ((pairDist_le_pairNorm_add _ _ _).trans (add_le_add ?_ ?_))
    · refine iSup₂_le fun x y ↦ ?_
      have := enorm_recentre_le_osc φ (k := (k : ℤ) + 1 + p) (by positivity) x y
      simpa [hδ, add_right_comm (k : ℤ) 1 (p : ℤ)] using this
    · exact iSup₂_le fun x y ↦ enorm_recentre_le_osc φ (by positivity) x y
  calc shiftDefect (recentre φ) p
      ≤ ∑' k : ℕ, (((k : ℝ≥0∞) + 1) * δ (k + p) + ((k : ℝ≥0∞) + 1) * δ k) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ (k + p) + ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ k :=
        ENNReal.tsum_add
    _ ≤ ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ k + ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ k := by
        refine add_le_add ?_ le_rfl
        calc ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ (k + p)
            ≤ ∑' k : ℕ, (fun m : ℕ ↦ ((m : ℝ≥0∞) + 1) * δ m) (k + p) := by
              refine ENNReal.tsum_le_tsum fun k ↦ ?_
              dsimp only
              refine mul_le_mul' ?_ le_rfl
              push_cast
              exact add_le_add le_self_add le_rfl
          _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective p) _
    _ = 2 * ∑' k : ℕ, ((k : ℝ≥0∞) + 1) * δ k := (two_mul _).symm
    _ ≤ 2 * oscSpanDiam (pairShift φ) :=
        mul_le_mul' le_rfl (tsum_succ_mul_osc_le_oscSpanDiam φ)

/-- **Georgii, Comment (9.7)(3).** Under (8.42), `Φ̃` satisfies (9.6) for all `p`. -/
theorem shiftDefect_recentre_ne_top (h : oscSpanDiam (pairShift φ) ≠ ⊤) (p : ℕ) :
    shiftDefect (recentre φ) p ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top h) (shiftDefect_recentre_le φ p)

/-- Under (8.42) the recentred potential is absolutely summable, `Φ̃ ∈ ℬ_Θ`. -/
theorem isAbsolutelySummable_pairShift_recentre (h : oscSpanDiam (pairShift φ) ≠ ⊤) :
    IsAbsolutelySummable (pairShift (recentre φ)) := by
  refine isAbsolutelySummable_pairShift _ (ne_top_of_le_ne_top h ?_)
  refine le_trans (ENNReal.tsum_le_tsum fun k ↦ ?_) (tsum_succ_mul_osc_le_oscSpanDiam φ)
  calc pairNorm (recentre φ) (k + 1)
      ≤ Dobrushin.osc (pairShift φ {0, ((k : ℤ) + 1)}) :=
        iSup₂_le fun x y ↦ enorm_recentre_le_osc φ (by positivity) x y
    _ ≤ ((k : ℝ≥0∞) + 1) * Dobrushin.osc (pairShift φ {0, ((k : ℤ) + 1)}) :=
        le_mul_of_one_le_left bot_le le_add_self

end MeasureTheory.GibbsMeasure

/-! ### Pure spin transformations and the group structure -/

/-! ### Georgii, Comments (9.13) -/

namespace MeasureTheory.GibbsMeasure

open Potential Transformation

variable {S E : Type*} [MeasurableSpace E] [LinearOrder S]

section CutSum

variable {J J' : S → S → ℝ≥0∞}

lemma cutSum_mono (h : ∀ i j, i < j → J i j ≤ J' i j) (n : S) : cutSum J n ≤ cutSum J' n :=
  ENNReal.tsum_le_tsum fun q ↦ by
    split_ifs with hq
    · exact h _ _ (hq.1.trans_lt hq.2)
    · exact le_rfl

lemma cutSum_mul_left (c : ℝ≥0∞) (J : S → S → ℝ≥0∞) (n : S) :
    cutSum (fun i j ↦ c * J i j) n = c * cutSum J n := by
  unfold cutSum
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun q ↦ ?_
  split_ifs <;> simp

lemma cutSum_add (J J' : S → S → ℝ≥0∞) (n : S) :
    cutSum (fun i j ↦ J i j + J' i j) n = cutSum J n + cutSum J' n := by
  unfold cutSum
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun q ↦ ?_
  split_ifs <;> simp

end CutSum

variable (φ : S → S → E → E → ℝ) (τ : Transformation S E)

/-- Georgii (9.14): the single-site oscillation `sup_{x, y} |φ_{ij}(τ_i x, y) − φ_{ij}(x, y)|`. -/
def pairOsc (i j : S) : ℝ≥0∞ := ⨆ (x : E) (y : E), ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ

/-- **Georgii (9.14).** `sup_n ∑_{i ≤ n < j} sup_{x,y} |φ_{ij}(τ_i x, y) − φ_{ij}(x, y)|`. -/
def pairOscBound : ℝ≥0∞ := ⨆ n : S, cutSum (pairOsc φ τ) n

variable {φ τ}

omit [LinearOrder S] in
/-- Georgii, Comment (9.13)(1), termwise: for a symmetry, `J(i, j) ≤ 2 sup |φ_{ij}(τ_i ·, ·) −
φ_{ij}|`, by the identity `|φ_{ij}(x, τ_j y) − φ_{ij}(x, y)| = |φ_{ij}(τ_i x', y) − φ_{ij}(x', y)|`,
`x' = τ_i⁻¹ x`. -/
lemma pairDefect_le_two_mul_pairOsc {i j : S}
    (hsym : ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) :
    pairDefect φ τ i j ≤ 2 * pairOsc φ τ i j := by
  refine iSup₂_le fun x y ↦ ?_
  have h1 : φ i j x (τ.spin j y) - φ i j x y =
      φ i j ((τ.spin i).symm x) y - φ i j (τ.spin i ((τ.spin i).symm x)) y := by
    rw [← hsym ((τ.spin i).symm x) y, MeasurableEquiv.apply_symm_apply]
  calc ENNReal.ofReal (φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y)
      = ENNReal.ofReal ((φ i j (τ.spin i x) y - φ i j x y) + (φ i j x (τ.spin j y) - φ i j x y))
          := by
        ring_nf
    _ ≤ ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ + ‖φ i j x (τ.spin j y) - φ i j x y‖ₑ :=
        ENNReal.ofReal_add_le.trans (add_le_add
          (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _))
          (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)))
    _ ≤ pairOsc φ τ i j + pairOsc φ τ i j := by
        refine add_le_add (le_iSup₂ (f := fun x y ↦ ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ) x y) ?_
        rw [h1, enorm_sub_rev]
        exact le_iSup₂ (f := fun x y ↦ ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ) ((τ.spin i).symm x) y
    _ = 2 * pairOsc φ τ i j := (two_mul _).symm

/-- **Georgii, Comment (9.13)(1).** For a symmetry `τ` of `Φ`, condition (9.14) implies (9.12):
`C(Φ, τ) ≤ 2 · (9.14)`. -/
theorem pairDefectBound_le_two_mul_pairOscBound
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) :
    pairDefectBound φ τ ≤ 2 * pairOscBound φ τ := by
  refine iSup_le fun n ↦ ?_
  calc cutSum (pairDefect φ τ) n
      ≤ cutSum (fun i j ↦ 2 * pairOsc φ τ i j) n :=
        cutSum_mono (fun i j hij ↦ pairDefect_le_two_mul_pairOsc (hsym i j hij)) n
    _ = 2 * cutSum (pairOsc φ τ) n := cutSum_mul_left _ _ n
    _ ≤ 2 * pairOscBound φ τ := mul_le_mul' le_rfl (le_iSup (fun n ↦ cutSum (pairOsc φ τ) n) n)

theorem pairDefectBound_ne_top_of_pairOscBound_ne_top
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (h : pairOscBound φ τ ≠ ⊤) : pairDefectBound φ τ ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top h)
    (pairDefectBound_le_two_mul_pairOscBound hsym)

/-! #### Comment (9.13)(2): powers and inverses of a symmetry -/

omit [LinearOrder S] in
/-- `J(i, j)` is the same for `τ` and `τ⁻¹`. -/
lemma pairDefect_inv (hτ : τ.IsPureSpin) {i j : S}
    (hsym : ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) :
    pairDefect φ τ⁻¹ i j = pairDefect φ τ i j := by
  have key : ∀ x y, φ i j (τ⁻¹.spin i x) y + φ i j x (τ⁻¹.spin j y) - 2 * φ i j x y =
      φ i j (τ.spin i x) y + φ i j x (τ.spin j y) - 2 * φ i j x y := fun x y ↦ by
    rw [hτ.inv_spin_apply, hτ.inv_spin_apply]
    have h1 := hsym ((τ.spin i).symm x) y
    rw [MeasurableEquiv.apply_symm_apply] at h1
    have h2 := hsym x ((τ.spin j).symm y)
    rw [MeasurableEquiv.apply_symm_apply] at h2
    rw [← h1, ← h2]
    ring
  simp only [pairDefect, key]

/-- **Georgii, Comment (9.13)(2)** for the inverse: `C(Φ, τ⁻¹) = C(Φ, τ)`. -/
theorem pairDefectBound_inv (hτ : τ.IsPureSpin)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) :
    pairDefectBound φ τ⁻¹ = pairDefectBound φ τ := by
  refine iSup_congr fun n ↦ tsum_congr fun q ↦ ?_
  split_ifs with hq
  · rw [pairDefect_inv hτ (hsym _ _ (hq.1.trans_lt hq.2))]
  · rfl

omit [LinearOrder S] in
/-- Georgii, proof of Comment (9.13)(2): `φ_{ij}(x, τ_j^k y) = φ_{ij}(τ_i^{-k} x, y)`. -/
lemma pair_iterate_spin_eq {i j : S}
    (hsym : ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) (k : ℕ) (x y : E) :
    φ i j x ((τ.spin j)^[k] y) = φ i j (((τ.spin i).symm)^[k] x) y := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ← ih ((τ.spin i).symm x)]
    have := hsym ((τ.spin i).symm x) ((τ.spin j)^[k] y)
    rw [MeasurableEquiv.apply_symm_apply] at this
    exact this

omit [LinearOrder S] in
/-- **Georgii, Comment (9.13)(2), termwise**: `J_{τ^k}(i, j) ≤ k² J_τ(i, j)`, from the
second-difference identity of Georgii (`add_neg_sub_two_mul_le_natCast_sq_mul_of_forall_le`). -/
lemma pairDefect_pow_le (hτ : τ.IsPureSpin) {i j : S}
    (hsym : ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) (k : ℕ) :
    pairDefect φ (τ ^ k) i j ≤ (k : ℝ≥0∞) ^ 2 * pairDefect φ τ i j := by
  by_cases hJ : pairDefect φ τ i j = ⊤
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [Nat.cast_zero, zero_pow two_ne_zero, zero_mul]
      refine iSup₂_le fun x y ↦ ?_
      rw [pow_zero]
      simp only [show ∀ i x, (1 : Transformation S E).spin i x = x from fun _ _ ↦ rfl]
      rw [show φ i j x y + φ i j x y - 2 * φ i j x y = 0 by ring, ENNReal.ofReal_zero]
    · rw [hJ, ENNReal.mul_top (by positivity)]
      exact le_top
  refine iSup₂_le fun x y ↦ ?_
  set e : Equiv.Perm E := (τ.spin i).toEquiv with he
  set g : ℤ → ℝ := fun ℓ ↦ φ i j ((e ^ ℓ) x) y with hg
  have hsecond : ∀ ℓ : ℤ, g (ℓ + 1) + g (ℓ - 1) - 2 * g ℓ ≤ (pairDefect φ τ i j).toReal := by
    intro ℓ
    have h1 : (e ^ (ℓ + 1)) x = τ.spin i ((e ^ ℓ) x) := by
      rw [add_comm, zpow_one_add, Equiv.Perm.mul_apply]
      rfl
    have h2 : (e ^ (ℓ - 1)) x = (τ.spin i).symm ((e ^ ℓ) x) := by
      have : (e ^ ℓ) x = τ.spin i ((e ^ (ℓ - 1)) x) := by
        conv_lhs => rw [show ℓ = 1 + (ℓ - 1) by ring, zpow_one_add, Equiv.Perm.mul_apply]
        rfl
      rw [this, MeasurableEquiv.symm_apply_apply]
    simp only [hg]
    rw [h1, h2]
    set x' := (e ^ ℓ) x
    have h3 := hsym ((τ.spin i).symm x') y
    rw [MeasurableEquiv.apply_symm_apply] at h3
    rw [← h3]
    exact (ENNReal.ofReal_le_iff_le_toReal hJ).1 (ofReal_le_pairDefect i j x' y)
  have hbound := add_neg_sub_two_mul_le_natCast_sq_mul_of_forall_le hsecond k
  have hk1 : (e ^ (k : ℤ)) x = (τ ^ k).spin i x := by
    rw [zpow_natCast, Equiv.Perm.coe_pow, hτ.pow_spin_apply]
    rfl
  have hk2 : (e ^ (-(k : ℤ))) x = ((τ.spin i).symm)^[k] x := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow, Equiv.Perm.inv_def]
    rfl
  calc ENNReal.ofReal (φ i j ((τ ^ k).spin i x) y + φ i j x ((τ ^ k).spin j y) - 2 * φ i j x y)
      = ENNReal.ofReal (g k + g (-k) - 2 * g 0) := by
        simp only [hg]
        rw [hk1, hk2, zpow_zero, Equiv.Perm.one_apply, hτ.pow_spin_apply, hτ.pow_spin_apply,
          pair_iterate_spin_eq hsym]
    _ ≤ ENNReal.ofReal ((k : ℝ) ^ 2 * (pairDefect φ τ i j).toReal) :=
        ENNReal.ofReal_le_ofReal hbound
    _ = (k : ℝ≥0∞) ^ 2 * pairDefect φ τ i j := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hJ, ENNReal.ofReal_pow
          (by positivity), ENNReal.ofReal_natCast]

/-- **Georgii, Comment (9.13)(2).** `C(Φ, τ^k) ≤ k² C(Φ, τ)` for every `k ∈ ℕ`; together with
`pairDefectBound_inv` this covers all `k ∈ ℤ`: condition (9.12) passes from `τ` to every power
of `τ`. -/
theorem pairDefectBound_pow_le (hτ : τ.IsPureSpin)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) (k : ℕ) :
    pairDefectBound φ (τ ^ k) ≤ (k : ℝ≥0∞) ^ 2 * pairDefectBound φ τ := by
  refine iSup_le fun n ↦ ?_
  calc cutSum (pairDefect φ (τ ^ k)) n
      ≤ cutSum (fun i j ↦ (k : ℝ≥0∞) ^ 2 * pairDefect φ τ i j) n :=
        cutSum_mono (fun i j hij ↦ pairDefect_pow_le hτ (hsym i j hij) k) n
    _ = (k : ℝ≥0∞) ^ 2 * cutSum (pairDefect φ τ) n := cutSum_mul_left _ _ n
    _ ≤ (k : ℝ≥0∞) ^ 2 * pairDefectBound φ τ :=
        mul_le_mul' le_rfl (le_iSup (fun n ↦ cutSum (pairDefect φ τ) n) n)

theorem pairDefectBound_pow_ne_top (hτ : τ.IsPureSpin)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y)
    (hC : pairDefectBound φ τ ≠ ⊤) (k : ℕ) : pairDefectBound φ (τ ^ k) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)) hC)
    (pairDefectBound_pow_le hτ hsym k)

/-! #### Comment (9.13)(2), second sentence: (9.14) defines a subgroup -/

omit [LinearOrder S] in
lemma pairOsc_mul_le (hτ : τ.IsPureSpin) (σ : Transformation S E) (i j : S) :
    pairOsc φ (τ * σ) i j ≤ pairOsc φ τ i j + pairOsc φ σ i j := by
  refine iSup₂_le fun x y ↦ ?_
  rw [hτ.mul_spin_apply]
  calc ‖φ i j (τ.spin i (σ.spin i x)) y - φ i j x y‖ₑ
      = ‖(φ i j (τ.spin i (σ.spin i x)) y - φ i j (σ.spin i x) y) +
          (φ i j (σ.spin i x) y - φ i j x y)‖ₑ := by ring_nf
    _ ≤ ‖φ i j (τ.spin i (σ.spin i x)) y - φ i j (σ.spin i x) y‖ₑ +
          ‖φ i j (σ.spin i x) y - φ i j x y‖ₑ := enorm_add_le _ _
    _ ≤ _ := add_le_add
        (le_iSup₂ (f := fun x y ↦ ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ) (σ.spin i x) y)
        (le_iSup₂ (f := fun x y ↦ ‖φ i j (σ.spin i x) y - φ i j x y‖ₑ) x y)

omit [LinearOrder S] in
lemma pairOsc_inv (hτ : τ.IsPureSpin) (i j : S) : pairOsc φ τ⁻¹ i j = pairOsc φ τ i j := by
  refine le_antisymm (iSup₂_le fun x y ↦ ?_) (iSup₂_le fun x y ↦ ?_)
  · rw [hτ.inv_spin_apply, enorm_sub_rev]
    have := le_iSup₂ (f := fun x y ↦ ‖φ i j (τ.spin i x) y - φ i j x y‖ₑ) ((τ.spin i).symm x) y
    rwa [MeasurableEquiv.apply_symm_apply] at this
  · rw [enorm_sub_rev]
    have := le_iSup₂ (f := fun x y ↦ ‖φ i j (τ⁻¹.spin i x) y - φ i j x y‖ₑ) (τ.spin i x) y
    rwa [hτ.inv_spin_apply, MeasurableEquiv.symm_apply_apply] at this

theorem pairOscBound_mul_le (hτ : τ.IsPureSpin) (σ : Transformation S E) :
    pairOscBound φ (τ * σ) ≤ pairOscBound φ τ + pairOscBound φ σ := by
  refine iSup_le fun n ↦ ?_
  calc cutSum (pairOsc φ (τ * σ)) n
      ≤ cutSum (fun i j ↦ pairOsc φ τ i j + pairOsc φ σ i j) n :=
        cutSum_mono (fun i j _ ↦ pairOsc_mul_le hτ σ i j) n
    _ = cutSum (pairOsc φ τ) n + cutSum (pairOsc φ σ) n := cutSum_add _ _ n
    _ ≤ _ := add_le_add (le_iSup (fun n ↦ cutSum (pairOsc φ τ) n) n)
        (le_iSup (fun n ↦ cutSum (pairOsc φ σ) n) n)

theorem pairOscBound_inv (hτ : τ.IsPureSpin) : pairOscBound φ τ⁻¹ = pairOscBound φ τ := by
  have : pairOsc φ τ⁻¹ = pairOsc φ τ := funext fun i ↦ funext fun j ↦ pairOsc_inv hτ i j
  simp only [pairOscBound, this]

theorem pairOscBound_one : pairOscBound φ (1 : Transformation S E) = 0 := by
  refine le_antisymm (iSup_le fun n ↦ le_of_eq ?_) bot_le
  unfold cutSum
  refine ENNReal.tsum_eq_zero.2 fun q ↦ ?_
  split_ifs
  · simp [pairOsc, one_def,
      show ∀ i x, (Transformation.id : Transformation S E).spin i x = x from fun _ _ ↦ rfl]
  · rfl

variable (φ) in
/-- **Georgii, Comment (9.13)(2).** The symmetries `τ ∈ T_λ⁰` of the pair potential `Φ` that
satisfy (9.14) form a subgroup of `T` (contained in `T_λ⁰`). -/
def pairOscSymmetries (ν : Measure E) : Subgroup (Transformation S E) where
  carrier := {τ | τ.IsPureSpin ∧ (∀ i, MeasurePreserving (τ.spin i) ν ν) ∧
    Potential.map τ (pair φ) = pair φ ∧ pairOscBound φ τ ≠ ⊤}
  one_mem' := ⟨IsPureSpin.one, fun _ ↦ MeasurePreserving.id ν, by
    rw [one_def]; exact Potential.map_id _, by
    rw [pairOscBound_one]; exact ENNReal.zero_ne_top⟩
  mul_mem' := by
    rintro τ σ ⟨hτ, hτν, hτΦ, hτb⟩ ⟨hσ, hσν, hσΦ, hσb⟩
    refine ⟨hτ.mul hσ, fun i ↦ ?_, ?_, ?_⟩
    · change MeasurePreserving ((σ.spin (τ.sites.symm i)).trans (τ.spin i)) ν ν
      rw [MeasurableEquiv.coe_trans]
      exact (hτν i).comp (hσν _)
    · rw [mul_def, ← Potential.map_map, hσΦ, hτΦ]
    · exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hτb, hσb⟩) (pairOscBound_mul_le hτ σ)
  inv_mem' := by
    rintro τ ⟨hτ, hτν, hτΦ, hτb⟩
    refine ⟨hτ.inv, fun i ↦ ?_, ?_, ?_⟩
    · change MeasurePreserving (τ.spin (τ.sites i)).symm ν ν
      exact (hτν _).symm _
    · have := congrArg (Potential.map τ⁻¹) hτΦ
      rw [Potential.map_map, ← mul_def, inv_mul_cancel, one_def, Potential.map_id] at this
      exact this.symm
    · rw [pairOscBound_inv hτ]; exact hτb

lemma mem_pairOscSymmetries_iff {ν : Measure E} :
    τ ∈ pairOscSymmetries φ ν ↔ τ.IsPureSpin ∧ (∀ i, MeasurePreserving (τ.spin i) ν ν) ∧
      Potential.map τ (pair φ) = pair φ ∧ pairOscBound φ τ ≠ ⊤ := Iff.rfl

/-! #### Comment (9.13)(3): the uniqueness condition (8.40) implies (9.14) -/

/-- The single-site oscillation (9.14) is dominated by the oscillation `δ(Φ_{{i,j}})`. -/
lemma pairOsc_le_osc_pair {i j : S} (hij : i < j) :
    pairOsc φ τ i j ≤ Dobrushin.osc (pair φ {i, j}) := by
  refine iSup₂_le fun x y ↦ ?_
  classical
  let η : S → E := fun k ↦ if k = i then x else y
  have h := Dobrushin.le_osc (pair φ {i, j}) (Function.update η i (τ.spin i x)) η
  rw [pair_pair φ hij, pair_pair φ hij] at h
  simp only [η, Function.update_self, Function.update_of_ne hij.ne', ite_eq_left rfl,
    ite_eq_right hij.ne'] at h
  rwa [Real.enorm_eq_ofReal_abs]

/-- **Georgii, Comment (9.13)(3), at each cut.** The sum in (9.14) over the pairs straddling `n`
is at most the sum (8.40) at `n`. -/
theorem cutSum_pairOsc_le_oscSpan (n : S) : cutSum (pairOsc φ τ) n ≤ oscSpan (pair φ) n := by
  unfold cutSum oscSpan
  let g : {q : S × S // q.1 < q.2} → Finset S := fun q ↦ {q.1.1, q.1.2}
  have hg : Function.Injective g := fun q q' h ↦ by
    obtain ⟨h1, h2⟩ := (pair_eq_pair_iff_of_lt q.2 q'.2).1 h
    exact Subtype.ext (Prod.ext h1 h2)
  rw [← tsum_subtype_eq_of_support_subset (s := {q : S × S | q.1 < q.2})
    (f := fun q : S × S ↦ if q.1 ≤ n ∧ n < q.2 then pairOsc φ τ q.1 q.2 else 0)
    (fun q hq ↦ by
      by_contra h
      exact hq (ite_eq_right fun h' ↦ h (h'.1.trans_lt h'.2)))]
  refine le_trans (ENNReal.tsum_le_tsum fun q ↦ ?_) (ENNReal.tsum_comp_le_tsum_of_injective hg _)
  by_cases h : q.1.1 ≤ n ∧ n < q.1.2
  · rw [ite_eq_left h, Set.indicator_of_mem (show g q ∈ {A : Finset S | Spans A n} from
      ⟨⟨q.1.1, by simp [g], h.1⟩, ⟨q.1.2, by simp [g], h.2⟩⟩)]
    exact pairOsc_le_osc_pair q.2
  · rw [ite_eq_right h]
    exact bot_le

/-- **Georgii, Comment (9.13)(3).** Georgii's uniqueness condition (8.40) for a pair potential,
`sup_n ∑_{A : min A ≤ n < max A} δ(Φ_A) < ∞`, implies (9.14) for every pure spin transformation,
and a fortiori (9.12) for every pure spin symmetry
(`pairDefectBound_ne_top_of_pairOscBound_ne_top`). -/
theorem pairOscBound_le_iSup_oscSpan : pairOscBound φ τ ≤ ⨆ n : S, oscSpan (pair φ) n :=
  iSup_mono fun n ↦ cutSum_pairOsc_le_oscSpan n

theorem pairDefectBound_ne_top_of_oscSpan_le {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (h : ∀ n : S, oscSpan (pair φ) n ≤ s)
    (hsym : ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y) :
    pairDefectBound φ τ ≠ ⊤ :=
  pairDefectBound_ne_top_of_pairOscBound_ne_top hsym
    (ne_top_of_le_ne_top hs (pairOscBound_le_iSup_oscSpan.trans (iSup_le h)))

end MeasureTheory.GibbsMeasure

namespace Potential

/-- Equal potentials have equal Gibbsian specifications (the admissibility proofs are
irrelevant). -/
lemma gibbsSpecificationOfSigmaFiniteAdmissible_congr {S E : Type*} [MeasurableSpace E]
    [Countable S] {Φ Ψ : Potential S E} [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ]
    [IsSummable Ψ] (h : Φ = Ψ) (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Ψ.boltzmannFactor β)) :
    gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hΦ =
      gibbsSpecificationOfSigmaFiniteAdmissible Ψ ν β hΨ := by
  subst h
  rfl

end Potential

/-! ### Georgii, Example (9.8)(2): the long-range Ising antiferromagnet -/

namespace MeasureTheory.GibbsMeasure

open Potential Transformation

variable {E : Type*} [MeasurableSpace E]

/-- **Georgii, Example (9.8)(2): the long-range Ising antiferromagnet**,
`Φ̃_{{i,j}} = −β (−1)^{i+j} |i − j|^{-a} s(σ_i) s(σ_j)`. Since `(−1)^{i+j} = (−1)^{j−i}`, it is the
potential (9.4) with `φ̃_k = (−1)^k φ_k`, `φ_k` the ferromagnetic interaction `longRangeIsing`. -/
def longRangeIsingAlt (s : E → ℝ) (β a : ℝ) : ℤ → E → E → ℝ :=
  fun k x y ↦ (-1 : ℝ) ^ k * longRangeIsing s β a k x y

variable {s : E → ℝ} {β a : ℝ}

omit [MeasurableSpace E] in
lemma enorm_longRangeIsingAlt (k : ℤ) (x y : E) :
    ‖longRangeIsingAlt s β a k x y‖ₑ = ‖longRangeIsing s β a k x y‖ₑ := by
  rw [longRangeIsingAlt, enorm_mul, Real.enorm_eq_ofReal_abs ((-1 : ℝ) ^ k), abs_neg_one_zpow,
    ENNReal.ofReal_one, one_mul]

omit [MeasurableSpace E] in
/-- `‖φ̃_{k+2} − φ̃_k‖ = ‖φ_{k+2} − φ_k‖`: the sign is `2`-periodic. -/
lemma pairDist_longRangeIsingAlt_add_two (k : ℤ) :
    pairDist (longRangeIsingAlt s β a) (k + 2) k = pairDist (longRangeIsing s β a) (k + 2) k := by
  simp only [pairDist, longRangeIsingAlt]
  refine iSup_congr fun x ↦ iSup_congr fun y ↦ ?_
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num, mul_one,
    ← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs ((-1 : ℝ) ^ k), abs_neg_one_zpow,
    ENNReal.ofReal_one, one_mul]

omit [MeasurableSpace E] in
/-- **Georgii (9.8)(2)**: `Φ̃` has the same sum (9.6) for `p = 2` as `Φ`. -/
theorem shiftDefect_longRangeIsingAlt_two :
    shiftDefect (longRangeIsingAlt s β a) 2 = shiftDefect (longRangeIsing s β a) 2 := by
  simp only [shiftDefect, Nat.cast_ofNat]
  exact tsum_congr fun k ↦ by rw [pairDist_longRangeIsingAlt_add_two]

omit [MeasurableSpace E] in
/-- **Georgii (9.8)(2)**: `Φ̃` satisfies (9.6) for `p = 2`. -/
theorem shiftDefect_longRangeIsingAlt_two_ne_top (ha : 1 < a) (hs : ∀ x, |s x| ≤ 1) :
    shiftDefect (longRangeIsingAlt s β a) 2 ≠ ⊤ := by
  rw [shiftDefect_longRangeIsingAlt_two]
  have h := shiftDefect_longRangeIsing_ne_top (s := s) (β := β) ha hs
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h, h⟩) (shiftDefect_add_le _ 1 1)

lemma normAt_pairShift_longRangeIsingAlt (i : ℤ) :
    (pairShift (longRangeIsingAlt s β a)).normAt i = (pairShift (longRangeIsing s β a)).normAt i
        := by
  unfold normAt
  refine tsum_congr fun A ↦ ?_
  by_cases hi : i ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | i ∈ A} from hi),
      Set.indicator_of_mem (show A ∈ {A : Finset ℤ | i ∈ A} from hi)]
    refine iSup_congr fun η ↦ ?_
    rcases exists_lt_pair_or A with ⟨b, c, hbc, rfl⟩ | hA
    · rw [pairShift_pair _ hbc, pairShift_pair _ hbc, enorm_longRangeIsingAlt]
    · rw [pairShift, pairShift, pair_eq_zero _ hA, pair_eq_zero _ hA]
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | i ∈ A} from hi),
      Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | i ∈ A} from hi)]

theorem isAbsolutelySummable_pairShift_longRangeIsingAlt (ha : 1 < a) (hs : ∀ x, |s x| ≤ 1) :
    IsAbsolutelySummable (pairShift (longRangeIsingAlt s β a)) :=
  haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
  ⟨fun i ↦ by
    rw [normAt_pairShift_longRangeIsingAlt]
    exact IsAbsolutelySummable.normAt_ne_top i⟩

theorem isPotential_pairShift_longRangeIsingAlt (hs : Measurable s) :
    IsPotential (pairShift (longRangeIsingAlt s β a)) :=
  isPotential_pairShift _ fun k ↦ by
    unfold longRangeIsingAlt longRangeIsing Function.uncurry
    exact measurable_const.mul (measurable_const.mul (measurable_const.mul
      ((hs.comp measurable_fst).mul (hs.comp measurable_snd))))

/-- **Georgii, Example (9.8)(2).** Every Gibbs measure of the long-range antiferromagnet with
`a > 1` is periodic with period two: `θ_2`-invariant, by Theorem (9.5) with `p = 2`. -/
theorem measurePreserving_shift_two_longRangeIsingAlt [StandardBorelSpace E] (hsm : Measurable s)
    (hs : ∀ x, |s x| ≤ 1) (ha : 1 < a) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β' : ℝ)
    {μ : Measure (ℤ → E)}
    (hμ : haveI := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
      haveI := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
      μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsingAlt s β a)) ν β')) :
    MeasurePreserving (shift E 2).toFun μ μ := by
  have := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
  have h := measurePreserving_shift_of_shiftDefect_ne_top (longRangeIsingAlt s β a) ν β'
    (p := 2) two_pos (shiftDefect_longRangeIsingAlt_two_ne_top ha hs) hμ
  simpa using h

/-! #### The isomorphism `Φ̃ = τ(Φ)` -/

variable (E) in
/-- Georgii (9.8)(2): `(τ ω)_i = (−1)^i ω_i`, the spin flip `f` at odd sites and the identity at
even sites. -/
def alternatingFlip (f : E ≃ᵐ E) : Transformation ℤ E where
  sites := Equiv.refl ℤ
  spin i := if Even i then MeasurableEquiv.refl E else f

variable (E) in
/-- The global spin flip `ω ↦ (f ω_i)_i`. -/
def spinFlip (f : E ≃ᵐ E) : Transformation ℤ E where
  sites := Equiv.refl ℤ
  spin _ := f

variable (f : E ≃ᵐ E)

lemma isPureSpin_alternatingFlip : (alternatingFlip E f).IsPureSpin := rfl

lemma isPureSpin_spinFlip : (spinFlip E f).IsPureSpin := rfl

lemma alternatingFlip_spin_apply (i : ℤ) (x : E) :
    (alternatingFlip E f).spin i x = if Even i then x else f x := by
  simp only [alternatingFlip]
  split_ifs <;> rfl

lemma alternatingFlip_spin_symm_apply (i : ℤ) (x : E) :
    ((alternatingFlip E f).spin i).symm x = if Even i then x else f.symm x := by
  simp only [alternatingFlip]
  split_ifs <;> rfl

lemma measurePreserving_spin_alternatingFlip {ν : Measure E} (hf : MeasurePreserving f ν ν)
    (i : ℤ) : MeasurePreserving ((alternatingFlip E f).spin i) ν ν := by
  simp only [alternatingFlip]
  split_ifs
  · exact MeasurePreserving.id ν
  · exact hf

/-- **Georgii (9.8)(2): `Φ̃ = τ(Φ)`** for a spin flip `f` with `s ∘ f = −s`. -/
theorem map_alternatingFlip_pairShift_longRangeIsing (hf : ∀ x, s (f x) = -s x) :
    Potential.map (alternatingFlip E f) (pairShift (longRangeIsing s β a)) =
      pairShift (longRangeIsingAlt s β a) := by
  have hf' : ∀ x, s (f.symm x) = -s x := fun x ↦ by
    have := hf (f.symm x)
    rw [MeasurableEquiv.apply_symm_apply] at this
    linarith
  have hε : ∀ (i : ℤ) (x : E), s (((alternatingFlip E f).spin i).symm x) = (-1 : ℝ) ^ i * s x := by
    intro i x
    rw [alternatingFlip_spin_symm_apply]
    split_ifs with h
    · rw [Even.neg_one_zpow h, one_mul]
    · rw [Odd.neg_one_zpow (Int.not_even_iff_odd.1 h), hf', neg_one_mul]
  have hpar : ∀ i j : ℤ, (-1 : ℝ) ^ i * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (j - i) := by
    intro i j
    rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), show j - i = i + j - 2 * i by ring,
      zpow_sub₀ (by norm_num : (-1 : ℝ) ≠ 0), zpow_mul, show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num,
      one_zpow, div_one]
  funext A η
  rw [Potential.map_apply, show (alternatingFlip E f).sites = Equiv.refl ℤ from rfl,
    Equiv.refl_symm, Equiv.refl_toEmbedding, Finset.map_refl]
  simp only [pairShift, pair_apply]
  refine pairTerms_congr (fun i j _ ↦ ?_) A
  rw [(isPureSpin_alternatingFlip f).inv_toFun_apply, (isPureSpin_alternatingFlip
      f).inv_toFun_apply,
    longRangeIsingAlt, longRangeIsing, longRangeIsing, hε, hε, ← hpar]
  ring

/-- Georgii (9.8)(2): `τ` is an involution when the spin flip `f` is. -/
lemma alternatingFlip_mul_self (hff : ∀ x, f (f x) = x) :
    alternatingFlip E f * alternatingFlip E f = 1 := by
  refine Transformation.ext ?_ ?_
  · ext i
    rfl
  · funext i
    apply MeasurableEquiv.ext
    funext x
    change (alternatingFlip E f).spin i ((alternatingFlip E f).spin i x) = x
    rw [alternatingFlip_spin_apply, alternatingFlip_spin_apply]
    split_ifs <;> simp [hff]

lemma alternatingFlip_toFun_comp_self (hff : ∀ x, f (f x) = x) :
    (alternatingFlip E f).toFun ∘ (alternatingFlip E f).toFun = id := by
  funext ω
  have := congrArg (fun τ : Transformation ℤ E ↦ τ.toFun ω) (alternatingFlip_mul_self f hff)
  simp only [mul_def, comp_toFun] at this
  exact this

/-- **Georgii (9.8)(2)**: conversely `Φ = τ(Φ̃)`, `τ` being an involution. -/
theorem map_alternatingFlip_pairShift_longRangeIsingAlt (hf : ∀ x, s (f x) = -s x)
    (hff : ∀ x, f (f x) = x) :
    Potential.map (alternatingFlip E f) (pairShift (longRangeIsingAlt s β a)) =
      pairShift (longRangeIsing s β a) := by
  rw [← map_alternatingFlip_pairShift_longRangeIsing f hf, Potential.map_map, ← mul_def,
    alternatingFlip_mul_self f hff, one_def, Potential.map_id]

/-- **Georgii (9.8)(2)**: `μ ↦ τ(μ)` maps `𝒢(Φ)` into `𝒢(Φ̃)` (Proposition (5.6) and Remark
(5.10)); as `τ` is an involution, it is a bijection (`bijOn_map_alternatingFlip`). -/
theorem map_alternatingFlip_mem_G_longRangeIsingAlt (hsm : Measurable s) (hs : ∀ x, |s x| ≤ 1)
    (ha : 1 < a) (hf : ∀ x, s (f x) = -s x) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (hfν : MeasurePreserving f ν ν) (β' : ℝ) {μ : Measure (ℤ → E)}
    (hμ : haveI := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
      haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
      μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsing s β a)) ν β')) :
    haveI := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
    haveI := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
    μ.map (alternatingFlip E f).toFun ∈
      G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsingAlt s β a)) ν β') := by
  have := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
  have := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
  have h1 := Specification.map_mem_G_map (alternatingFlip E f) hμ
  rw [gibbsSpecificationOfFiniteReference, map_gibbsSpecificationOfSigmaFiniteAdmissible _ _ _ ν
    (measurePreserving_spin_alternatingFlip f hfν) _
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor ν β'),
    gibbsSpecificationOfSigmaFiniteAdmissible_congr
      (map_alternatingFlip_pairShift_longRangeIsing f hf) ν β' _
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor ν β')] at h1
  exact h1

/-- **Georgii (9.8)(2)**: `μ ↦ τ(μ)` maps `𝒢(Φ̃)` into `𝒢(Φ)`. -/
theorem map_alternatingFlip_mem_G_longRangeIsing (hsm : Measurable s) (hs : ∀ x, |s x| ≤ 1)
    (ha : 1 < a) (hf : ∀ x, s (f x) = -s x) (hff : ∀ x, f (f x) = x) (ν : Measure E)
    [IsFiniteMeasure ν] [NeZero ν] (hfν : MeasurePreserving f ν ν) (β' : ℝ) {μ : Measure (ℤ → E)}
    (hμ : haveI := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
      haveI := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
      μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsingAlt s β a)) ν β')) :
    haveI := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
    haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
    μ.map (alternatingFlip E f).toFun ∈
      G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsing s β a)) ν β') := by
  have := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
  have := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
  have h1 := Specification.map_mem_G_map (alternatingFlip E f) hμ
  rw [gibbsSpecificationOfFiniteReference, map_gibbsSpecificationOfSigmaFiniteAdmissible _ _ _ ν
    (measurePreserving_spin_alternatingFlip f hfν) _
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor ν β'),
    gibbsSpecificationOfSigmaFiniteAdmissible_congr
      (map_alternatingFlip_pairShift_longRangeIsingAlt f hf hff) ν β' _
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor ν β')] at h1
  exact h1

/-- **Georgii (9.8)(2)**: the involution `μ ↦ τ(μ)` is a bijection between `𝒢(Φ)` and
`𝒢(Φ̃)`. -/
theorem bijOn_map_alternatingFlip [StandardBorelSpace E] (hsm : Measurable s)
    (hs : ∀ x, |s x| ≤ 1) (ha : 1 < a) (hf : ∀ x, s (f x) = -s x) (hff : ∀ x, f (f x) = x)
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (hfν : MeasurePreserving f ν ν) (β' : ℝ) :
    haveI := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
    haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
    haveI := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
    haveI := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
    Set.BijOn (fun μ : Measure (ℤ → E) ↦ μ.map (alternatingFlip E f).toFun)
      (G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsing s β a)) ν β'))
      (G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsingAlt s β a)) ν β')) := by
  have := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
  have := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
  have := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
  have hinv : ∀ μ : Measure (ℤ → E),
      (μ.map (alternatingFlip E f).toFun).map (alternatingFlip E f).toFun = μ := fun μ ↦ by
    rw [Measure.map_map (alternatingFlip E f).measurable_toFun
      (alternatingFlip E f).measurable_toFun, alternatingFlip_toFun_comp_self f hff, Measure.map_id]
  refine ⟨fun μ hμ ↦ map_alternatingFlip_mem_G_longRangeIsingAlt f hsm hs ha hf ν hfν β' hμ,
    fun μ _ μ' _ h ↦ ?_,
    fun μ hμ ↦ ⟨μ.map (alternatingFlip E f).toFun,
      map_alternatingFlip_mem_G_longRangeIsing f hsm hs ha hf hff ν hfν β' hμ, hinv μ⟩⟩
  rw [← hinv μ, ← hinv μ']
  exact congrArg (fun m : Measure (ℤ → E) ↦ m.map (alternatingFlip E f).toFun) h

/-- Georgii (9.8)(2): `τ` commutes with `θ_2`. -/
theorem alternatingFlip_mul_shift_two :
    alternatingFlip E f * shift E 2 = shift E 2 * alternatingFlip E f := by
  have hpar : ∀ i : ℤ, Even (i + -2) ↔ Even i := fun i ↦ by
    rw [Int.even_add]
    simp [show Even (-2 : ℤ) from ⟨-1, by norm_num⟩]
  refine Transformation.ext ?_ ?_
  · ext i
    rfl
  · funext i
    apply MeasurableEquiv.ext
    funext x
    change (alternatingFlip E f).spin i (((shift E (2 : ℤ)).spin i) x) =
      ((shift E (2 : ℤ)).spin i) (((alternatingFlip E f).spin ((shift E (2 : ℤ)).sites.symm i)) x)
    rw [alternatingFlip_spin_apply, alternatingFlip_spin_apply]
    change (if Even i then x else f x) = if Even (i + -2) then x else f x
    simp only [hpar]

/-- **Georgii (9.8)(2)**: as `τ` commutes with `θ_2`, `θ_2`-invariance passes from `μ` to
`τ(μ)` (Mathlib's `MeasurePreserving.of_semiconj`); with `bijOn_map_alternatingFlip` this is
Georgii's "the `θ_2`-invariance of the Gibbs measures in `𝒢(Φ)` implies that of those in
`𝒢(Φ̃)`, and vice versa". -/
theorem measurePreserving_shift_two_map_alternatingFlip {μ : Measure (ℤ → E)}
    (hμ : MeasurePreserving (shift E 2).toFun μ μ) :
    MeasurePreserving (shift E 2).toFun (μ.map (alternatingFlip E f).toFun)
      (μ.map (alternatingFlip E f).toFun) :=
  MeasurePreserving.of_semiconj ⟨(alternatingFlip E f).measurable_toFun, rfl⟩ hμ
    (fun ω ↦ by
      have h := congrArg (fun τ : Transformation ℤ E ↦ τ.toFun ω) (alternatingFlip_mul_shift_two f)
      simpa only [mul_def, comp_toFun] using h)
    (shift E 2).measurable_toFun

/-- Georgii (9.8)(2): `θ_1 ∘ τ = τ ∘ F ∘ θ_1` for the global spin flip `F`. -/
lemma shift_one_comp_alternatingFlip (hff : ∀ x, f (f x) = x) :
    (shift E 1).toFun ∘ (alternatingFlip E f).toFun =
      (alternatingFlip E f).toFun ∘ (spinFlip E f).toFun ∘ (shift E 1).toFun := by
  funext ω i
  simp only [Function.comp_apply, shift_toFun_apply, (isPureSpin_alternatingFlip f).toFun_apply,
    (isPureSpin_spinFlip f).toFun_apply, alternatingFlip_spin_apply]
  change (if Even (i - 1) then ω (i - 1) else f (ω (i - 1))) =
    if Even i then f (ω (i - 1)) else f (f (ω (i - 1)))
  have hpar : Even (i - 1) ↔ ¬ Even i := by
    rw [Int.even_sub]
    simp
  by_cases h : Even i
  · rw [ite_eq_left h, ite_eq_right fun h' ↦ hpar.1 h' h]
  · rw [ite_eq_right h, ite_eq_left (hpar.2 h), hff]

/-- **Georgii (9.8)(2), the transfer of symmetry breaking.** If `μ` is `θ_1`-invariant but not
invariant under the global spin flip `F`, then `τ(μ)` is not `θ_1`-invariant: since
`θ_1 τ = τ F θ_1`, `θ_1`-invariance of `τ(μ)` would force `F(μ) = μ`. -/
theorem not_measurePreserving_shift_one_map_alternatingFlip (hff : ∀ x, f (f x) = x)
    {μ : Measure (ℤ → E)} (hθ : MeasurePreserving (shift E 1).toFun μ μ)
    (hF : ¬ MeasurePreserving (spinFlip E f).toFun μ μ) :
    ¬ MeasurePreserving (shift E 1).toFun (μ.map (alternatingFlip E f).toFun)
      (μ.map (alternatingFlip E f).toFun) := by
  intro h
  apply hF
  refine ⟨(spinFlip E f).measurable_toFun, ?_⟩
  have h1 := h.map_eq
  rw [Measure.map_map (shift E 1).measurable_toFun (alternatingFlip E f).measurable_toFun,
    shift_one_comp_alternatingFlip f hff,
    ← Measure.map_map (alternatingFlip E f).measurable_toFun
      ((spinFlip E f).measurable_toFun.comp (shift E 1).measurable_toFun),
    ← Measure.map_map (spinFlip E f).measurable_toFun (shift E 1).measurable_toFun,
    hθ.map_eq] at h1
  have h2 := congrArg (Measure.map (alternatingFlip E f).inv.toFun) h1
  rw [Measure.map_map (alternatingFlip E f).inv.measurable_toFun
      (alternatingFlip E f).measurable_toFun,
    Measure.map_map (alternatingFlip E f).inv.measurable_toFun
      (alternatingFlip E f).measurable_toFun,
    show (alternatingFlip E f).inv.toFun ∘ (alternatingFlip E f).toFun = id from
      funext (alternatingFlip E f).inv_toFun_toFun,
    Measure.map_id, Measure.map_id] at h2
  exact h2

/-- **Georgii, Example (9.8)(2), last sentence.** If the spin-flip symmetry is broken in `𝒢(Φ)`
(Georgii: for `1 < a ≤ 2` and large `β`, by Theorem (20.21) — not in this library, hence the
hypothesis `hbreak`), then `𝒢(Φ̃)` exhibits a breaking of `θ_1`: this is why `Φ̃` cannot satisfy
(9.6) for `p = 1`. -/
theorem exists_not_measurePreserving_shift_one_longRangeIsingAlt [StandardBorelSpace E]
    (hsm : Measurable s) (hs : ∀ x, |s x| ≤ 1) (ha : 1 < a) (hf : ∀ x, s (f x) = -s x)
    (hff : ∀ x, f (f x) = x) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (hfν : MeasurePreserving f ν ν) (β' : ℝ)
    (hbreak : haveI := isPotential_pairShift_longRangeIsing (β := β) (a := a) hsm
      haveI := isAbsolutelySummable_pairShift_longRangeIsing (β := β) ha hs
      ∃ μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsing s β a)) ν β'),
        ¬ MeasurePreserving (spinFlip E f).toFun μ μ) :
    haveI := isPotential_pairShift_longRangeIsingAlt (β := β) (a := a) hsm
    haveI := isAbsolutelySummable_pairShift_longRangeIsingAlt (β := β) ha hs
    ∃ μ ∈ G (gibbsSpecificationOfFiniteReference (pairShift (longRangeIsingAlt s β a)) ν β'),
      ¬ MeasurePreserving (shift E 1).toFun μ μ := by
  obtain ⟨μ, hμ, hF⟩ := hbreak
  exact ⟨μ.map (alternatingFlip E f).toFun,
    map_alternatingFlip_mem_G_longRangeIsingAlt f hsm hs ha hf ν hfν β' hμ,
    not_measurePreserving_shift_one_map_alternatingFlip f hff
      (measurePreserving_shift_longRangeIsing hsm hs ha ν β' hμ 1) hF⟩

end MeasureTheory.GibbsMeasure

/-! ### Georgii, Example (9.15) -/

namespace MeasureTheory.GibbsMeasure

open Potential Transformation

lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> simp [spin]

/-- **Georgii, Example (9.15).** The nearest-neighbour potential on `S = ℕ`, `E = {−1, 1}²`,
`φ_{i,i+1}(x, y) = −J_i x₁ y₁ − K x₁ x₂ y₁ y₂` (the vertices of a square as the state space). -/
def squarePotential (J : ℕ → ℝ) (K : ℝ) : ℕ → ℕ → Bool × Bool → Bool × Bool → ℝ :=
  fun i j x y ↦ if j = i + 1 then
    -J i * (spin x.1 * spin y.1) - K * (spin x.1 * spin x.2 * (spin y.1 * spin y.2)) else 0

/-- Georgii (9.15): the reflection `τ⁽¹⁾`, `(τ⁽¹⁾ ω)_i = (−ω_{i1}, ω_{i2})`. -/
def squareFlip₁ : Transformation ℕ (Bool × Bool) where
  sites := Equiv.refl ℕ
  spin _ := boolNot.prodCongr (MeasurableEquiv.refl Bool)

/-- Georgii (9.15): the reflection `τ⁽²⁾`, `(τ⁽²⁾ ω)_i = (ω_{i1}, −ω_{i2})`. -/
def squareFlip₂ : Transformation ℕ (Bool × Bool) where
  sites := Equiv.refl ℕ
  spin _ := (MeasurableEquiv.refl Bool).prodCongr boolNot

lemma squareFlip₁_spin_apply (i : ℕ) (x : Bool × Bool) : squareFlip₁.spin i x = (!x.1, x.2) := rfl

lemma squareFlip₂_spin_apply (i : ℕ) (x : Bool × Bool) : squareFlip₂.spin i x = (x.1, !x.2) := rfl

lemma isPureSpin_squareFlip₁ : squareFlip₁.IsPureSpin := rfl

lemma isPureSpin_squareFlip₂ : squareFlip₂.IsPureSpin := rfl

variable (J : ℕ → ℝ) (K : ℝ)

/-- Georgii (9.15): `Φ` is invariant under `τ⁽¹⁾`. -/
theorem map_squareFlip₁_squarePotential :
    Potential.map squareFlip₁ (pair (squarePotential J K)) = pair (squarePotential J K) :=
  (map_pair_eq_iff _ isPureSpin_squareFlip₁).2 fun i j _ x y ↦ by
    simp only [squarePotential, squareFlip₁_spin_apply, spin_not]
    split_ifs <;> ring

/-- Georgii (9.15): `Φ` is invariant under `τ⁽²⁾`. -/
theorem map_squareFlip₂_squarePotential :
    Potential.map squareFlip₂ (pair (squarePotential J K)) = pair (squarePotential J K) :=
  (map_pair_eq_iff _ isPureSpin_squareFlip₂).2 fun i j _ x y ↦ by
    simp only [squarePotential, squareFlip₂_spin_apply, spin_not]
    split_ifs <;> ring

lemma abs_squarePotential_le (i j : ℕ) (x y : Bool × Bool) :
    |squarePotential J K i j x y| ≤ |J i| + |K| := by
  unfold squarePotential
  split_ifs
  · have h1 : |spin x.1 * spin y.1| = 1 := by rw [abs_mul, abs_spin, abs_spin, mul_one]
    have h2 : |spin x.1 * spin x.2 * (spin y.1 * spin y.2)| = 1 := by
      simp only [abs_mul, abs_spin, mul_one]
    calc |-J i * (spin x.1 * spin y.1) - K * (spin x.1 * spin x.2 * (spin y.1 * spin y.2))|
        ≤ |-J i * (spin x.1 * spin y.1)| + |K * (spin x.1 * spin x.2 * (spin y.1 * spin y.2))| :=
          abs_sub _ _
      _ = |J i| + |K| := by rw [abs_mul (-J i), abs_mul K, abs_neg, h1, h2, mul_one, mul_one]
  · simp only [abs_zero]
    positivity

theorem isPotential_pair_squarePotential : IsPotential (pair (squarePotential J K)) :=
  isPotential_pair _ fun _ _ ↦ Measurable.of_discrete

theorem isFiniteRange_pair_squarePotential : IsFiniteRange (pair (squarePotential J K)) :=
  isFiniteRange_pair (fun i ↦ Finset.Icc (i - 1) (i + 1)) (fun i ↦ by simp)
    fun i j _ ⟨x, y, hxy⟩ ↦ by
      have : j = i + 1 := by
        by_contra h
        exact hxy (by simp [squarePotential, h])
      subst this
      simp only [Finset.mem_Icc]
      omega

theorem isAbsolutelySummable_pair_squarePotential :
    IsAbsolutelySummable (pair (squarePotential J K)) :=
  haveI := isFiniteRange_pair_squarePotential J K
  IsAbsolutelySummable.of_isFiniteRange (iSup_enorm_pair_ne_top fun i j _ ↦
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup₂_le fun x y ↦ by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (abs_squarePotential_le J K i j x y)))

/-- Georgii (9.15): the single-site oscillation (9.14) of `Φ` under `τ⁽²⁾` is `2K` on the
nearest-neighbour bonds and `0` elsewhere. -/
lemma pairOsc_squareFlip₂ (hK : 0 ≤ K) (i j : ℕ) :
    pairOsc (squarePotential J K) squareFlip₂ i j =
      if j = i + 1 then ENNReal.ofReal (2 * K) else 0 := by
  unfold pairOsc
  split_ifs with hj
  · have key : ∀ x y : Bool × Bool,
        ‖squarePotential J K i j (squareFlip₂.spin i x) y - squarePotential J K i j x y‖ₑ =
          ENNReal.ofReal (2 * K) := by
      intro x y
      have h1 : squarePotential J K i j (squareFlip₂.spin i x) y - squarePotential J K i j x y =
          2 * K * (spin x.1 * spin x.2 * (spin y.1 * spin y.2)) := by
        simp only [squarePotential, ite_eq_left hj, squareFlip₂_spin_apply, spin_not]
        ring
      rw [h1, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 2 * K)]
      simp only [abs_mul, abs_spin, mul_one]
    simp only [key, iSup_const]
  · simp only [squarePotential, ite_eq_right hj, sub_self, enorm_zero]
    simp

/-- Georgii (9.15): the sum in (9.14) over every cut equals `2K`. -/
theorem cutSum_pairOsc_squareFlip₂ (hK : 0 ≤ K) (n : ℕ) :
    cutSum (pairOsc (squarePotential J K) squareFlip₂) n = ENNReal.ofReal (2 * K) := by
  unfold cutSum
  rw [tsum_eq_single (n, n + 1)]
  · simp [pairOsc_squareFlip₂ J K hK]
  · intro q hq
    split_ifs with h
    · rw [pairOsc_squareFlip₂ J K hK, ite_eq_right]
      intro h2
      apply hq
      ext <;> simp only <;> omega
    · rfl

/-- **Georgii, Example (9.15).** For `τ = τ⁽²⁾` the expression (9.14) equals `2K`. -/
theorem pairOscBound_squareFlip₂ (hK : 0 ≤ K) :
    pairOscBound (squarePotential J K) squareFlip₂ = ENNReal.ofReal (2 * K) := by
  simp only [pairOscBound, cutSum_pairOsc_squareFlip₂ J K hK, iSup_const]

/-- **Georgii, Example (9.15).** Every `μ ∈ 𝒢(Φ)` is `τ⁽²⁾`-invariant, by Theorem (9.11) and
Comment (9.13)(1), for any finite a priori measure preserved by `τ⁽²⁾` (Georgii: the
equidistribution). -/
theorem measurePreserving_squareFlip₂ (hK : 0 ≤ K) (ν : Measure (Bool × Bool)) [IsFiniteMeasure ν]
    [NeZero ν] (hν : MeasurePreserving ((MeasurableEquiv.refl Bool).prodCongr boolNot) ν ν)
    {β : ℝ} (hβ : 0 ≤ β) {μ : Measure (ℕ → Bool × Bool)}
    (hμ : haveI := isPotential_pair_squarePotential J K
      haveI := isAbsolutelySummable_pair_squarePotential J K
      μ ∈ G (gibbsSpecificationOfFiniteReference (pair (squarePotential J K)) ν β)) :
    MeasurePreserving squareFlip₂.toFun μ μ := by
  have := isPotential_pair_squarePotential J K
  have := isAbsolutelySummable_pair_squarePotential J K
  have hsym := (map_pair_eq_iff _ isPureSpin_squareFlip₂).1 (map_squareFlip₂_squarePotential J K)
  exact measurePreserving_of_pairDefectBound_ne_top ν hβ
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor ν β) isPureSpin_squareFlip₂ (fun _ ↦ hν) hsym
    (pairDefectBound_ne_top_of_pairOscBound_ne_top hsym
      (by rw [pairOscBound_squareFlip₂ J K hK]; exact ENNReal.ofReal_ne_top)) hμ

/-- **Georgii, Example (9.15), the broken symmetry.** A finite measure with `μ(σ_{i1}) > 0` is not
`τ⁽¹⁾`-invariant. -/
theorem not_measurePreserving_squareFlip₁_of_integral_pos {μ : Measure (ℕ → Bool × Bool)}
    (i : ℕ) (h : 0 < ∫ ω, spin (ω i).1 ∂μ) : ¬ MeasurePreserving squareFlip₁.toFun μ μ := by
  intro hτ
  have h1 := (show MeasurePreserving squareFlip₁.toMeasurableEquiv μ μ from hτ).integral_comp'
    fun ω : ℕ → Bool × Bool ↦ spin (ω i).1
  have h2 : ∀ ω : ℕ → Bool × Bool, spin ((squareFlip₁.toMeasurableEquiv ω) i).1 = -spin (ω i).1 :=
    fun ω ↦ spin_not _
  simp only [h2, integral_neg] at h1
  linarith

/-- **Georgii, Example (9.15).** Georgii's `μ₊ ∈ 𝒢(Φ)` with `μ₊(σ_{i1}) > 0` (from Theorem (6.4)
when `K = 0`, and from Griffiths' inequalities when `K > 0`) is the hypothesis `hex`; given it,
`𝒢(Φ)` exhibits a breaking of `τ⁽¹⁾`. -/
theorem exists_not_measurePreserving_squareFlip₁ {γ : Specification ℕ (Bool × Bool)} (i : ℕ)
    (hex : ∃ μ ∈ G γ, 0 < ∫ ω, spin (ω i).1 ∂μ) :
    ∃ μ ∈ G γ, ¬ MeasurePreserving squareFlip₁.toFun μ μ :=
  let ⟨μ, hμ, h⟩ := hex
  ⟨μ, hμ, not_measurePreserving_squareFlip₁_of_integral_pos i h⟩

/-- **Georgii, Example (9.15) at `K = 0`.** The two-layer potential reads only the first layer: it
is the pullback of the inhomogeneous Ising chain potential (6.2) along `Prod.fst`. -/
theorem comap_fst_isingChainPotential (J : ℕ → ℝ) :
    (isingChainPotential J).comap (Prod.fst : Bool × Bool → Bool)
      = pair (squarePotential J 0) := by
  rw [isingChainPotential, Potential.comap_pair]
  congr 1
  funext i j x y
  simp only [squarePotential, isingChainPair]
  split_ifs <;> ring

/-- **Georgii, Example (9.15) at `K = 0`: the symmetry `τ⁽¹⁾` is broken.** For `K = 0` the two
layers decouple and Georgii invokes Theorem (6.4) for the first one. At an inverse temperature
`β > 0`, under the hypotheses of (6.4) for the couplings `βJ` — `J_n > 0` and
`∑_n e^{-2βJ_n} < ∞`, Georgii (6.1) — the chain has a Gibbs measure `μ₊` with `μ₊(σ_n) > 0` at
every site (`exists_mem_G_integral_spin_pos`, transported to `β` by
`isingChainSpecification_smul`); the product `μ₊ ⊗ λ^ℕ` with a free second layer is a Gibbs
measure for `Φ = pair (squarePotential J 0)` (`mem_G_map_symm_prod_infinitePi_comap_fst`) whose
first-layer magnetisation is again `μ₊(σ_n)`, so it is not `τ⁽¹⁾`-invariant. The a priori measure
is Georgii's equidistribution on the four vertices of the square, `λ = λ₁ ⊗ λ₁`. -/
theorem exists_not_measurePreserving_squareFlip₁_of_summable {J : ℕ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hJ : ∀ n, 0 < J n) (h61 : Summable fun n ↦ Real.exp (-2 * (β * J n))) (i : ℕ) :
    haveI := isPotential_pair_squarePotential J 0
    haveI := isAbsolutelySummable_pair_squarePotential J 0
    ∃ μ ∈ G (gibbsSpecificationOfFiniteReference (pair (squarePotential J 0))
        (uniformSpinMeasure.prod uniformSpinMeasure) β),
      ¬ MeasurePreserving squareFlip₁.toFun μ μ := by
  have := isPotential_pair_squarePotential J 0
  have := isAbsolutelySummable_pair_squarePotential J 0
  obtain ⟨μ₁, hμ₁', hpos⟩ := exists_mem_G_integral_spin_pos (J := β • J)
    (fun n ↦ mul_pos hβ (hJ n)) (by simpa using h61)
  rw [isingChainSpecification_smul] at hμ₁'
  have hμ₁ : μ₁ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := isingChainPotential J)
    uniformSpinMeasure β) := hμ₁'
  have : IsProbabilityMeasure μ₁ := hμ₁.1
  set e := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool ℕ with he
  set μ := (μ₁.prod (Measure.infinitePi fun _ : ℕ ↦ uniformSpinMeasure)).map e.symm with hμdef
  have hlift : μ ∈ G (gibbsSpecificationOfAbsolutelySummable
      (Φ := (isingChainPotential J).comap (Prod.fst : Bool × Bool → Bool))
      (uniformSpinMeasure.prod uniformSpinMeasure) β) :=
    mem_G_map_symm_prod_infinitePi_comap_fst (isingChainPotential J) uniformSpinMeasure
      uniformSpinMeasure β hμ₁
  have hspec : gibbsSpecificationOfFiniteReference (pair (squarePotential J 0))
      (uniformSpinMeasure.prod uniformSpinMeasure) β
      = gibbsSpecificationOfAbsolutelySummable
        (Φ := (isingChainPotential J).comap (Prod.fst : Bool × Bool → Bool))
        (uniformSpinMeasure.prod uniformSpinMeasure) β := by
    rw [gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure]
    exact gibbsSpecification_congr _ β (comap_fst_isingChainPotential J) |>.symm
  have hq : Measurable fun ω : ℕ → Bool × Bool ↦ fun j ↦ (ω j).1 :=
    measurable_pi_lambda _ fun j ↦ (measurable_pi_apply j).fst
  have hmar : μ.map (fun ω j ↦ (ω j).1) = μ₁ :=
    map_fst_map_arrowProdEquivProdArrow_symm_prod μ₁ _
  have hint : ∫ ω, spin (ω i).1 ∂μ = ∫ x, spin (x i) ∂μ₁ := by
    have h := integral_map (μ := μ) (φ := fun ω : ℕ → Bool × Bool ↦ fun j ↦ (ω j).1)
      (f := fun x : ℕ → Bool ↦ spin (x i)) hq.aemeasurable
      (((Measurable.of_discrete (f := spin)).comp (measurable_pi_apply i)).aestronglyMeasurable)
    rw [hmar] at h
    exact h.symm
  exact ⟨μ, hspec ▸ hlift,
    not_measurePreserving_squareFlip₁_of_integral_pos i (hint ▸ hpos i)⟩

end MeasureTheory.GibbsMeasure

/-! ### Georgii, Example (9.17): a potential without Gibbs measures in one dimension -/

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

/-- Integrating against Georgii's `λ_Λ(·|η)` is Mathlib's marginal integral `∫⋯∫⁻_Λ` at `η`. -/
theorem lintegral_sigmaFiniteLambdaFun_eq_lmarginal [DecidableEq S] (ν : Measure E)
    [SigmaFinite ν] (Λ : Finset S) (η : S → E) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) =
      (∫⋯∫⁻_Λ, F ∂(fun _ : S ↦ ν)) η := by
  rw [sigmaFiniteLambdaFun_apply_eq_map, lintegral_map hF Measurable.juxt]
  unfold lmarginal
  refine lintegral_congr fun y ↦ ?_
  congr 1
  funext i
  by_cases h : i ∈ Λ
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 h)]
    simp [Function.updateFinset, h]
  · rw [juxt_apply_of_not_mem (by simpa using h)]
    simp [Function.updateFinset, h]

/-- `∫⋯∫⁻_s, c * f = c * ∫⋯∫⁻_s, f`. -/
lemma lmarginal_const_mul' [DecidableEq S] (ν : Measure E) (s : Finset S) (c : ℝ≥0∞)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    (∫⋯∫⁻_s, (fun x ↦ c * f x) ∂(fun _ : S ↦ ν)) = fun x ↦ c * (∫⋯∫⁻_s, f ∂(fun _ : S ↦ ν)) x := by
  funext x
  simp only [lmarginal]
  exact lintegral_const_mul _ (hf.comp measurable_updateFinset)

end Specification

namespace MeasureTheory.GibbsMeasure

open Potential Transformation

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [MeasurableSub₂ E]

/-- **Georgii, Example (9.17).** The nearest-neighbour "gradient" potential
`φ_{i,i+1}(x, y) = u(y − x)` on `S = ℤ`, for a function `u` on an additive group of spins. -/
def gradientPotential (u : E → ℝ) : ℤ → ℤ → E → E → ℝ :=
  fun i j x y ↦ if j = i + 1 then u (y - x) else 0

variable (E) in
/-- Georgii (9.17): the spin translation `τ ω = (ω_i + c)_i`, the constant case of the general
`MeasureTheory.GibbsMeasure.spinTranslation` of `Prereqs/Transformation.lean`. -/
abbrev constSpinTranslation (c : E) : Transformation ℤ E := spinTranslation fun _ : ℤ ↦ c

variable (c : E)

omit [MeasurableSub₂ E] in
lemma isPureSpin_constSpinTranslation : (constSpinTranslation E c).IsPureSpin := rfl

omit [MeasurableSub₂ E] in
lemma constSpinTranslation_spin_apply (i : ℤ) (x : E) :
    (constSpinTranslation E c).spin i x = x + c := rfl

omit [MeasurableSub₂ E] in
lemma constSpinTranslation_spin_iterate (i : ℤ) (k : ℕ) (x : E) :
    ((constSpinTranslation E c).spin i)^[k] x = x + k • c := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, constSpinTranslation_spin_apply, succ_nsmul, add_assoc]

variable (u : E → ℝ)

omit [MeasurableSub₂ E] in
/-- Georgii (9.17): `Φ` is invariant under the spin translation. -/
theorem map_constSpinTranslation_gradientPotential :
    Potential.map (constSpinTranslation E c) (pair (gradientPotential u)) = pair (gradientPotential u) :=
  (map_pair_eq_iff _ (isPureSpin_constSpinTranslation c)).2 fun i j _ x y ↦ by
    simp only [gradientPotential, constSpinTranslation_spin_apply, add_sub_add_right_eq_sub]

omit [MeasurableAdd E] in
theorem isPotential_pair_gradientPotential (hu : Measurable u) :
    IsPotential (pair (gradientPotential u)) :=
  isPotential_pair _ fun i j ↦ by
    unfold gradientPotential Function.uncurry
    split_ifs
    · exact hu.comp (measurable_snd.sub measurable_fst)
    · exact measurable_const

omit [MeasurableAdd E] [MeasurableSub₂ E] in
theorem isFiniteRange_pair_gradientPotential : IsFiniteRange (pair (gradientPotential u)) :=
  isFiniteRange_pair (fun i ↦ Finset.Icc (i - 1) (i + 1)) (fun i ↦ by simp)
    fun i j _ ⟨x, y, hxy⟩ ↦ by
      have : j = i + 1 := by
        by_contra h
        exact hxy (by simp [gradientPotential, h])
      subst this
      simp only [Finset.mem_Icc]
      omega

omit [MeasurableAdd E] [MeasurableSub₂ E] in
lemma pair_gradientPotential_nonneg (hu0 : ∀ x, 0 ≤ u x) (A : Finset ℤ) (η : ℤ → E) :
    0 ≤ pair (gradientPotential u) A η :=
  pairTerms_nonneg (fun i j _ ↦ by
    unfold gradientPotential
    split_ifs
    · exact hu0 _
    · exact le_rfl) A

omit [MeasurableAdd E] [MeasurableSub₂ E] in
lemma pair_gradientPotential_pair (η : ℤ → E) (i : ℤ) :
    pair (gradientPotential u) {i - 1, i} η = u (η i - η (i - 1)) := by
  rw [pair_pair _ (by omega : i - 1 < i)]
  simp [gradientPotential]

omit [MeasurableAdd E] [MeasurableSub₂ E] in
/-- Georgii (9.17): `H_Λ ≥ ∑_{i ∈ Λ} u(σ_i − σ_{i−1})`, dropping the nonnegative bonds leaving
`Λ` upwards. -/
theorem sum_le_hamiltonian_gradientPotential (hu0 : ∀ x, 0 ≤ u x) (Λ : Finset ℤ) (η : ℤ → E) :
    haveI := isFiniteRange_pair_gradientPotential u
    ∑ i ∈ Λ, u (η i - η (i - 1)) ≤ (pair (gradientPotential u)).hamiltonian Λ η := by
  have := isFiniteRange_pair_gradientPotential u
  rw [hamiltonian_eq_interactingHamiltonian, interactingHamiltonian]
  set Φ := pair (gradientPotential u) with hΦ
  have hinj : Function.Injective (fun i : ℤ ↦ ({i - 1, i} : Finset ℤ)) := fun i j h ↦
    ((pair_eq_pair_iff_of_lt (by omega : i - 1 < i) (by omega : j - 1 < j)).1 h).2
  calc ∑ i ∈ Λ, u (η i - η (i - 1))
      = ∑ i ∈ Λ, Φ {i - 1, i} η :=
        Finset.sum_congr rfl fun i _ ↦ (pair_gradientPotential_pair u η i).symm
    _ = ∑ A ∈ Λ.image (fun i ↦ ({i - 1, i} : Finset ℤ)), Φ A η :=
        (Finset.sum_image (f := fun A ↦ Φ A η) fun i _ j _ h ↦ hinj h).symm
    _ = ∑ A ∈ (Λ.image (fun i ↦ ({i - 1, i} : Finset ℤ))).filter
          (· ∈ interactingSupport (Φ := Φ) Λ), Φ A η := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun A hA hA' ↦ ?_).symm
        rw [Finset.mem_filter, not_and] at hA'
        have hΦA : Φ A = 0 := by
          by_contra h
          apply hA' hA
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
          exact (mem_interactingSupport (Φ := Φ)).2 ⟨⟨i, by simp, by simpa using hi⟩, h⟩
        rw [hΦA]
        rfl
    _ ≤ ∑ A ∈ interactingSupport (Φ := Φ) Λ, Φ A η :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun A hA ↦ (Finset.mem_filter.1 hA).2)
          fun A _ _ ↦ pair_gradientPotential_nonneg u hu0 A η

omit [MeasurableAdd E] [MeasurableSub₂ E] in
/-- Georgii (9.17): `h_Λ ≤ ∏_{i ∈ Λ} exp(−u(σ_i − σ_{i−1}))`. -/
theorem boltzmannFactor_gradientPotential_le (hu0 : ∀ x, 0 ≤ u x) (Λ : Finset ℤ) (η : ℤ → E) :
    haveI := isFiniteRange_pair_gradientPotential u
    (pair (gradientPotential u)).boltzmannFactor 1 Λ η ≤
      ∏ i ∈ Λ, ENNReal.ofReal (Real.exp (-u (η i - η (i - 1)))) := by
  have := isFiniteRange_pair_gradientPotential u
  rw [boltzmannFactor, ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ (Real.exp_pos _).le),
    ← Real.exp_sum, Finset.sum_neg_distrib]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := sum_le_hamiltonian_gradientPotential u hu0 Λ η
  linarith

/-- **Georgii (9.17), the λ-admissibility computation.** Integrating out the sites of `Λ` from
the top, `∫ λ_Λ(dζ|η) ∏_{i ∈ Λ} g(ζ_i − ζ_{i−1}) = λ(g)^{|Λ|}` for a translation-invariant `λ`. -/
theorem lmarginal_prod_translate_eq_pow (ν : Measure E) [SigmaFinite ν] [ν.IsAddRightInvariant]
    {g : E → ℝ≥0∞} (hg : Measurable g) (Λ : Finset ℤ) (η : ℤ → E) :
    (∫⋯∫⁻_Λ, (fun ζ ↦ ∏ i ∈ Λ, g (ζ i - ζ (i - 1))) ∂(fun _ : ℤ ↦ ν)) η =
      (∫⁻ x, g x ∂ν) ^ Λ.card := by
  have hmeas : ∀ t : Finset ℤ, Measurable fun ζ : ℤ → E ↦ ∏ i ∈ t, g (ζ i - ζ (i - 1)) :=
    fun t ↦ Finset.measurable_prod _ fun i _ ↦
      hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply (i - 1)))
  induction Λ using Finset.induction_on_max generalizing η with
  | empty => simp
  | insert a s hs ih =>
    have ha : a ∉ s := fun h ↦ lt_irrefl a (hs a h)
    rw [lmarginal_insert' _ (hmeas _) ha]
    have hinner : (fun ζ : ℤ → E ↦ ∫⁻ x, ∏ i ∈ insert a s,
        g (Function.update ζ a x i - Function.update ζ a x (i - 1)) ∂ν) =
        fun ζ ↦ (∫⁻ x, g x ∂ν) * ∏ i ∈ s, g (ζ i - ζ (i - 1)) := by
      funext ζ
      have hprod : ∀ x, ∏ i ∈ insert a s,
          g (Function.update ζ a x i - Function.update ζ a x (i - 1)) =
          g (x - ζ (a - 1)) * ∏ i ∈ s, g (ζ i - ζ (i - 1)) := by
        intro x
        rw [Finset.prod_insert ha, Function.update_self,
          Function.update_of_ne (by omega : a - 1 ≠ a)]
        congr 1
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hi' := hs i hi
        rw [Function.update_of_ne (by omega : i ≠ a), Function.update_of_ne (by omega : i - 1 ≠ a)]
      simp_rw [hprod]
      have hgc : Measurable fun x : E ↦ g (x - ζ (a - 1)) :=
        hg.comp (measurable_id.sub measurable_const)
      rw [lintegral_mul_const _ hgc, lintegral_sub_right_eq_self g (ζ (a - 1))]
    rw [hinner, Specification.lmarginal_const_mul' ν s _ (hmeas s)]
    dsimp only
    rw [ih η, Finset.card_insert_of_notMem ha, pow_succ']

/-- **Georgii, Example (9.17): `Φ` is λ-admissible** when `λ(e^{-u}) < ∞`, since
`λ_Λ h_Λ ≤ λ(e^{-u})^{|Λ|}`. -/
theorem isSigmaFiniteLambdaAdmissible_gradientPotential (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    [ν.IsAddRightInvariant] (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x)
    (hν : ∫⁻ x, ENNReal.ofReal (Real.exp (-u x)) ∂ν ≠ ⊤) :
    haveI := isPotential_pair_gradientPotential u hu
    haveI := isFiniteRange_pair_gradientPotential u
    Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) ν
      ((pair (gradientPotential u)).boltzmannFactor 1) := by
  have := isPotential_pair_gradientPotential u hu
  have := isFiniteRange_pair_gradientPotential u
  intro Λ η
  have hne : Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) ν Λ η ≠ 0 := by
    rw [Specification.sigmaFiniteLambdaFun_apply_eq_map]
    intro h
    have := congrArg (fun m ↦ m Set.univ) h
    simp only [Measure.map_apply Measurable.juxt MeasurableSet.univ, Set.preimage_univ,
      Measure.pi_univ, Measure.coe_zero, Pi.zero_apply, Finset.prod_const] at this
    exact pow_ne_zero _ (Measure.measure_univ_ne_zero.2 (NeZero.ne ν)) this
  constructor
  · intro h0
    rw [Specification.sigmaFiniteLambdaZ, lintegral_eq_zero_iff (measurable_boltzmannFactor 1 Λ)]
      at h0
    have : ∀ᵐ ζ ∂(Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) ν Λ η), False :=
      h0.mono fun ζ hζ ↦ (boltzmannFactor_pos 1 Λ ζ).ne' hζ
    exact hne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 this))
  · rw [Specification.sigmaFiniteLambdaZ,
      Specification.lintegral_sigmaFiniteLambdaFun_eq_lmarginal ν Λ η
        (measurable_boltzmannFactor 1 Λ)]
    refine ne_top_of_le_ne_top (ENNReal.pow_ne_top hν (n := Λ.card)) ?_
    refine le_trans ?_ (le_of_eq (lmarginal_prod_translate_eq_pow ν
      ((Real.measurable_exp.comp hu.neg).ennreal_ofReal) Λ η))
    exact lmarginal_mono (fun ζ ↦ boltzmannFactor_gradientPotential_le u hu0 Λ ζ) η

/-- Georgii (9.17): `c(u) = sup_x [u(x + c) + u(x − c) − 2 u(x)]₊`, the quadratic growth
constant of `u` in the direction `c` (Georgii: `c = 1`). -/
def quadDefect : ℝ≥0∞ := ⨆ x : E, ENNReal.ofReal (u (x + c) + u (x - c) - 2 * u x)

omit [MeasurableSub₂ E] in
/-- Georgii (9.17): `J(i, i+1) = c(u)` and `J(i, j) = 0` for `j ≠ i + 1`. -/
lemma pairDefect_gradientPotential (i j : ℤ) :
    pairDefect (gradientPotential u) (constSpinTranslation E c) i j =
      if j = i + 1 then quadDefect c u else 0 := by
  unfold pairDefect quadDefect
  split_ifs with hj
  · have key : ∀ x y : E, u (y - (x + c)) + u (y + c - x) - 2 * u (y - x) =
        u ((y - x) + c) + u ((y - x) - c) - 2 * u (y - x) := fun x y ↦ by
      rw [show y - (x + c) = y - x - c by abel, show y + c - x = y - x + c by abel]
      ring
    simp only [gradientPotential, ite_eq_left hj, constSpinTranslation_spin_apply, key]
    refine le_antisymm (iSup₂_le fun x y ↦
      le_iSup (fun z ↦ ENNReal.ofReal (u (z + c) + u (z - c) - 2 * u z)) (y - x))
      (iSup_le fun z ↦ ?_)
    have := le_iSup₂ (f := fun x y : E ↦
      ENNReal.ofReal (u ((y - x) + c) + u ((y - x) - c) - 2 * u (y - x))) 0 z
    simpa using this
  · simp [gradientPotential, ite_eq_right hj]

omit [MeasurableSub₂ E] in
theorem cutSum_pairDefect_gradientPotential (n : ℤ) :
    cutSum (pairDefect (gradientPotential u) (constSpinTranslation E c)) n = quadDefect c u := by
  unfold cutSum
  rw [tsum_eq_single (n, n + 1)]
  · simp [pairDefect_gradientPotential]
  · intro q hq
    split_ifs with h
    · rw [pairDefect_gradientPotential, ite_eq_right]
      intro h2
      apply hq
      ext <;> simp only <;> omega
    · rfl

omit [MeasurableSub₂ E] in
/-- **Georgii (9.17): `C(Φ, τ) = c(u)`.** -/
theorem pairDefectBound_gradientPotential :
    pairDefectBound (gradientPotential u) (constSpinTranslation E c) = quadDefect c u := by
  simp only [pairDefectBound, cutSum_pairDefect_gradientPotential, iSup_const]

/-- **Georgii, Example (9.17).** Let `S = ℤ`, `E` an additive group of spins with a
translation-invariant σ-finite a priori measure `λ` (`ℤ` with counting measure, `ℝ` with Lebesgue
measure), and `u ≥ 0` measurable with `λ(e^{-u}) < ∞`, `c(u) < ∞` (quadratic growth) and
`u(x + k c) → ∞` (divergence at infinity along the translation). Then `Φ` is `λ`-admissible but
`𝒢(Φ) = ∅`: `Φ` is invariant under the dissipative spin translation `τ`, and Corollary (9.16)
applies with `f = e^{-u}`. -/
theorem G_gradientPotential_eq_empty [StandardBorelSpace E] (ν : Measure E) [SigmaFinite ν]
    [NeZero ν] [ν.IsAddRightInvariant] (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x)
    (hν : ∫⁻ x, ENNReal.ofReal (Real.exp (-u x)) ∂ν ≠ ⊤) (hc : quadDefect c u ≠ ⊤)
    (hdiv : ∀ x, Tendsto (fun k : ℕ ↦ u (x + k • c)) atTop atTop) :
    haveI := isPotential_pair_gradientPotential u hu
    haveI := isFiniteRange_pair_gradientPotential u
    G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (gradientPotential u)) ν 1
      (isSigmaFiniteLambdaAdmissible_gradientPotential u ν hu hu0 hν)) = ∅ := by
  have := isPotential_pair_gradientPotential u hu
  have := isFiniteRange_pair_gradientPotential u
  have hsym := (map_pair_eq_iff _ (isPureSpin_constSpinTranslation c)).1
    (map_constSpinTranslation_gradientPotential c u)
  have hf : Measurable fun x : E ↦ ENNReal.ofReal (Real.exp (-u x)) :=
    (Real.measurable_exp.comp hu.neg).ennreal_ofReal
  refine G_eq_empty_of_pairDefectBound_ne_top_of_dissipative ν zero_le_one _
    (isPureSpin_constSpinTranslation c) (fun _ ↦ measurePreserving_add_right ν c) hsym
    (by rw [pairDefectBound_gradientPotential]; exact hc) hf (M := 1) ENNReal.one_ne_top
    (fun x ↦ ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (hu0 x)))) ?_ 0 ?_
  · intro h0
    rw [lintegral_eq_zero_iff hf] at h0
    have : ∀ᵐ x ∂ν, False :=
      h0.mono fun x hx ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hx
    exact NeZero.ne ν (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 this))
  · refine Filter.Eventually.of_forall fun x ↦ ?_
    simp only [constSpinTranslation_spin_iterate]
    have := ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.comp (hdiv x))
    simpa [Function.comp_def] using this

/-- Georgii (9.17): `λ(e^{-βx²}) < ∞` for Lebesgue measure (Mathlib's Gaussian integral). -/
lemma lintegral_ofReal_exp_neg_mul_sq_ne_top {β : ℝ} (hβ : 0 < β) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(β * x ^ 2))) ∂(volume : Measure ℝ) ≠ ⊤ := by
  have h := (integrable_exp_neg_mul_sq hβ).hasFiniteIntegral
  refine (lt_of_eq_of_lt (lintegral_congr fun x ↦ ?_) h).ne
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _), neg_mul]

/-- **Georgii, Example (9.17), the Gaussian case.** For `E = ℝ`, Lebesgue measure and
`u(x) = β x²` with `β > 0`, `Φ` is λ-admissible (`λ(e^{-u}) = √(π/β) < ∞`), `c(u) = 2β`, and
`𝒢(Φ) = ∅`. -/
theorem G_gaussianGradient_eq_empty {β : ℝ} (hβ : 0 < β) :
    haveI := isPotential_pair_gradientPotential (fun x : ℝ ↦ β * x ^ 2) (by fun_prop)
    haveI := isFiniteRange_pair_gradientPotential (fun x : ℝ ↦ β * x ^ 2)
    G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (gradientPotential fun x : ℝ ↦ β * x ^ 2))
      volume 1 (isSigmaFiniteLambdaAdmissible_gradientPotential (fun x : ℝ ↦ β * x ^ 2) volume
        (by fun_prop) (fun x ↦ by positivity) (lintegral_ofReal_exp_neg_mul_sq_ne_top hβ))) =
      ∅ := by
  refine G_gradientPotential_eq_empty 1 (fun x : ℝ ↦ β * x ^ 2) volume (by fun_prop)
    (fun x ↦ by positivity) (lintegral_ofReal_exp_neg_mul_sq_ne_top hβ) ?_ ?_
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * β)) (iSup_le fun x ↦ le_of_eq ?_)
    congr 1
    ring
  · intro x
    simp only [nsmul_eq_mul, mul_one]
    exact ((Filter.tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_left _ x tendsto_natCast_atTop_atTop)).const_mul_atTop hβ

/-- Georgii (9.17): `∑_{n ∈ ℤ} e^{-β n²} < ∞`, i.e. `λ(e^{-u}) < ∞` for counting measure on `ℤ`
and `u(n) = β n²`. -/
lemma lintegral_count_ofReal_exp_neg_mul_sq_ne_top {β : ℝ} (hβ : 0 < β) :
    ∫⁻ n : ℤ, ENNReal.ofReal (Real.exp (-(β * (n : ℝ) ^ 2))) ∂Measure.count ≠ ⊤ := by
  have hnat : Summable fun n : ℕ ↦ Real.exp (-(β * (n : ℝ) ^ 2)) := by
    have := Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hβ) (f := fun n : ℕ ↦ (n : ℝ) ^ 2)
      fun n ↦ by exact_mod_cast Nat.le_self_pow two_ne_zero n
    simpa only [neg_mul] using this
  have hsum : Summable fun n : ℤ ↦ Real.exp (-(β * (n : ℝ) ^ 2)) :=
    summable_int_iff_summable_nat_and_neg.2
      ⟨by simpa only [Int.cast_natCast] using hnat,
        by simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hnat⟩
  rw [lintegral_count, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ (Real.exp_pos _).le) hsum]
  exact ENNReal.ofReal_ne_top

/-- **Georgii, Example (9.17), the discrete Gaussian case**: `E = ℤ`, counting measure and
`u(x) = β x²` with `β > 0` — Georgii's closing remark, the one-dimensional version of the potential
(6.16) of §6.3, which has infinitely many extreme Gibbs measures on `ℤ²` for large `β` but none
on `ℤ`. `Φ` is λ-admissible and `𝒢(Φ) = ∅`. -/
theorem G_intGaussianGradient_eq_empty {β : ℝ} (hβ : 0 < β) :
    haveI := isPotential_pair_gradientPotential (fun n : ℤ ↦ β * (n : ℝ) ^ 2)
      Measurable.of_discrete
    haveI := isFiniteRange_pair_gradientPotential (fun n : ℤ ↦ β * (n : ℝ) ^ 2)
    G (gibbsSpecificationOfSigmaFiniteAdmissible
      (pair (gradientPotential fun n : ℤ ↦ β * (n : ℝ) ^ 2)) Measure.count 1
      (isSigmaFiniteLambdaAdmissible_gradientPotential (fun n : ℤ ↦ β * (n : ℝ) ^ 2)
        Measure.count Measurable.of_discrete (fun x ↦ by positivity)
        (lintegral_count_ofReal_exp_neg_mul_sq_ne_top hβ))) = ∅ := by
  refine G_gradientPotential_eq_empty 1 (fun n : ℤ ↦ β * (n : ℝ) ^ 2) Measure.count
    Measurable.of_discrete (fun x ↦ by positivity)
    (lintegral_count_ofReal_exp_neg_mul_sq_ne_top hβ) ?_ ?_
  · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * β)) (iSup_le fun x ↦ le_of_eq ?_)
    congr 1
    push_cast
    ring
  · intro x
    simp only [nsmul_one, Int.cast_add, Int.cast_natCast]
    exact ((Filter.tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_left _ (x : ℝ) tendsto_natCast_atTop_atTop)).const_mul_atTop hβ

end MeasureTheory.GibbsMeasure

end

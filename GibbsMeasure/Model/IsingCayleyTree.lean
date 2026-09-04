/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLawChains
public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.CayleyTree
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioFixedPoint

/-!
# Georgii §12.2: the Ising model on Cayley trees

Sites are the vertices of a Cayley tree `S = 𝒞𝒯(d)` (`SimpleGraph.IsCayleyTree`: a tree in which
every vertex has `d + 1` neighbours), spins are `Bool` (`spin false = -1`, `spin true = 1`), and
the a priori measure is counting measure. Everything is an instance of the transfer-family theory
of §12.1 in `GibbsMeasure/Model/TreeBoundaryLaw.lean` and
`GibbsMeasure/Model/TreeBoundaryLawChains.lean`.

## Main declarations

* `isingTransfer` — **Georgii (12.20)**, the transfer matrix `Q_{J,h}` of the Ising potential
  (12.19) on `𝒞𝒯(d)`, and `isTransferFamily_isingTransfer` its `IsTransferFamily` property.
  `isingTreeSpecification` is *defined* as the transfer specification (12.8) of `Q_{J,h}`; its
  identification with the Gibbsian specification `γ^{Φ^{J,h}}` of the potential (12.19) — the
  step Georgii takes "in view of (12.7) and (12.9)" — is **not** proved here (see below).
* `isingBoundaryVec` — the constant boundary law of Proposition (12.24), `ℓ_t(-) = 1`,
  `ℓ_t(+) = exp (2t - 2h/(d+1))`; `isingBoundaryVec_solves_iff` is **(12.21) ⇔ (12.22)** and
  `isBoundaryLaw_isingBoundaryVec_iff` says `ℓ_t` is a boundary law iff `t = h + d φ_J(t)`,
  with `φ_J = Real.logCoshRatio J` of **(12.23)**.
* **Proposition (12.24)** in full: `isingChain` is `μ_t` (`isGibbsMeasure_isingChain`,
  `isCompletelyHomogeneousMarkovChain_isingChain`), `isingTransition` its transition matrix `P_t`
  (`transitionProb_isingChain`), `isingMarginal` its one-dimensional marginal `α_t`
  (`measure_preimage_singleton_isingChain`), and `isingChain_inj` / `exists_eq_isingChain` are the
  two halves of the one-to-one correspondence `t ↔ μ_t`.
* **(12.25)**: `integral_spin_isingChain`, the magnetisation `sinh 2t / (e^{-2J} + cosh 2t)`;
  `isingTransition_mul_div_mul` is Georgii's remark that `e^{4J}` is read off the bond marginal.
* **(12.32)**: `isingParam_eq_add_sum`, the equation `t_{ij} = h + ∑_{k ∈ ∂i∖{j}} φ_J(t_{ki})`
  for the parameters `isingParam` of an arbitrary boundary law normalised at `-1`, and step 1
  of the proof of (12.31): `exists_treeField_eq_and_forall_isingParam_le` /
  `exists_treeField_eq_and_forall_le_isingParam` squeeze them between solutions of (12.22), so
  `eq_isingBoundaryVec_of_unique` makes every boundary law constant when (12.22) has one solution.
* **Theorem (12.31)(a)**: `exists_G_isingTreeSpecification_eq_singleton` — if `J ≤ J(d)`
  (`d tanh J ≤ 1`) or `|h| > h(J, d)` then `𝒢(J, h) = {μ_*}`. Its ingredients are Theorem (12.6)
  (`exists_isMarkovChain_of_mem_extremePoints`), Theorem (12.12)(b), step 1, and Theorem (7.26)
  (`G_eq_singleton_of_extremePoints_subset_singleton`).
* **Theorem (12.31)(b), non-uniqueness**: `exists_ne_isingChain` (two distinct completely
  homogeneous Markov chains in `𝒢(J, h)` when `J > J(d)` and `|h| ≤ h(J,d)`) and
  `exists_three_isingChain` (three of them when `|h| < h(J,d)`).
* **(12.33)**: `integral_spin_isingChain_treeCriticalPoint`, the magnetisation
  `(d - w)^{1/2}(d - w̄)^{1/2}(d - 1)^{-1}` of `μ₊` at the critical field `h = -h(J, d)`
  (`treeCriticalPoint_solves`, `le_treeCriticalPoint_of_solves` identify `t₊ = t_{J,d}`).
* **(12.34)**, the antiferromagnetic case: `isingAltLaw` is Georgii's alternating boundary law for
  the bipartition `c` of `𝒞𝒯(d)`, `isBoundaryLaw_isingAltLaw_iff` is (12.34), `isingAltChain` the
  associated alternating Markov chain, and `isingAltChain_ne_comp_not` /
  `exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂` give the two distinct phases
  `μ_{-+} ≠ μ_{+-}` attached to a solution of **(12.35)** that does not solve (12.22).

The real analysis behind (12.23), (12.26)–(12.30), (12.33) and (12.35) — `Real.logCoshRatio`,
`Real.criticalCoupling` `J(d)`, `Real.treeCriticalPoint` `t_{J,d}`, `Real.treeCriticalField`
`h(J,d)`, Lemma (12.27) and the second iterate `Real.treeRecursion₂` — is in
`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/LogCoshRatio.lean` and
`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/LogCoshRatioFixedPoint.lean`.

## Not formalised here

Georgii's Theorem (12.31)(b) also asserts that `μ₋, μ₊` are *extreme* in `𝒢(J, h)` and in
`𝒢_{I(B)}(J, h)`, and that `ex 𝒢(J, h) ∖ ex 𝒢_{I(B)}(J, h)` is infinite (steps 3)–5) of his
proof: a stochastic-domination argument for `r_{Λ,ζ}`, the inhomogeneous boundary laws built from
a non-fixed orbit of `h + d φ_J`, and a mixing property of a completely homogeneous chain under
`I(B, n)`). Those three steps are not proved in this file. His remark that
`I(J, d) = ]-h(J,d), h(J,d)[` in the antiferromagnetic case is explicitly stated in the book as
suggested by numerical calculations, not as a theorem.

Three further gaps:

* `isingTreeSpecification = γ^{Φ^{J,h}}`. The transfer weight `∏_{b ∩ Λ ≠ ∅} Q_b` equals
  `exp (-H_Λ^{Φ^{J,h}})` times a factor depending only on `ω` off `Λ`, so the two λ-specifications
  agree (`Specification.lambdaSpecification_eq_of_mul_boundary`); that lemma is not applied here,
  so `𝒢` below is the Gibbs-measure set of the transfer specification, not (yet) of (12.19).
* The existence of `𝒞𝒯(d)` for `d ≥ 2`. Every theorem here is stated for a graph carrying
  `SimpleGraph.IsCayleyTree d`, but the only such graph built in this library is
  `SimpleGraph.isCayleyTree_hasse_int : (hasse ℤ).IsCayleyTree 1`. Since `d = 1` forces
  `d tanh J < 1` (`Real.mul_tanh_lt_one_of_le_one`), the hypotheses of `exists_ne_isingChain`,
  `exists_three_isingChain`, `integral_spin_isingChain_treeCriticalPoint` and
  `exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂` cannot be met by any graph in this
  library; only (12.31)(a) can currently be instantiated.
* The antiferromagnetic transition itself: `exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂`
  *assumes* a fixed point of (12.35) that is not one of (12.22). Georgii's argument that such a
  fixed point exists for `J < -J(d)` and `h ∈ I(J, d)` (the non-degeneracy of `I(J, d)`), and his
  converse `|𝒢(J,h)| = 1` iff (12.35) has one solution, are not proved.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Tree

variable {S : Type*} [DecidableEq S] {G : SimpleGraph S} [G.LocallyFinite] {d : ℕ} {J h t : ℝ}

/-! ## Georgii (12.19), (12.20): the Ising transfer matrix on `𝒞𝒯(d)` -/

/-- **Georgii (12.20).** The transfer matrix of the Ising potential (12.19) with coupling `J` and
external field `h` on the Cayley tree `𝒞𝒯(d)`: the external field is shared equally among the
`d + 1` bonds at each site, so that

`Q(-,-) = exp (J - 2h/(d+1))`, `Q(-,+) = Q(+,-) = exp (-J)`, `Q(+,+) = exp (J + 2h/(d+1))`. -/
def isingTransfer (d : ℕ) (J h : ℝ) (x y : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (J * spin x * spin y + h / (d + 1) * (spin x + spin y)))

lemma isingTransfer_apply (x y : Bool) :
    isingTransfer d J h x y
      = ENNReal.ofReal (exp (J * spin x * spin y + h / (d + 1) * (spin x + spin y))) := rfl

@[simp] lemma isingTransfer_false_false :
    isingTransfer d J h false false = ENNReal.ofReal (exp (J - 2 * (h / (d + 1)))) := by
  rw [isingTransfer_apply]
  norm_num [spin]
  ring_nf

@[simp] lemma isingTransfer_false_true :
    isingTransfer d J h false true = ENNReal.ofReal (exp (-J)) := by
  rw [isingTransfer_apply]
  norm_num [spin]

@[simp] lemma isingTransfer_true_false :
    isingTransfer d J h true false = ENNReal.ofReal (exp (-J)) := by
  rw [isingTransfer_apply]
  norm_num [spin]

@[simp] lemma isingTransfer_true_true :
    isingTransfer d J h true true = ENNReal.ofReal (exp (J + 2 * (h / (d + 1)))) := by
  rw [isingTransfer_apply]
  norm_num [spin]
  ring_nf

/-- **Georgii (12.9) for (12.20)**: the Ising transfer matrix is symmetric. -/
lemma isingTransfer_symm (x y : Bool) : isingTransfer d J h x y = isingTransfer d J h y x := by
  rw [isingTransfer_apply, isingTransfer_apply]
  ring_nf

lemma isingTransfer_pos (x y : Bool) : 0 < isingTransfer d J h x y :=
  ENNReal.ofReal_pos.2 (exp_pos _)

lemma isingTransfer_ne_top (x y : Bool) : isingTransfer d J h x y ≠ ⊤ := ENNReal.ofReal_ne_top

/-- **Georgii (12.20).** The Ising specification on `𝒞𝒯(d)` is the transfer specification of
`isingTransfer`: the family is a transfer family in the sense of §12.1. -/
theorem isTransferFamily_isingTransfer (G : SimpleGraph S) [G.LocallyFinite] (d : ℕ) (J h : ℝ) :
    IsTransferFamily G (fun _ _ : S ↦ isingTransfer d J h) :=
  isTransferFamily_of_finite (fun _ _ x y ↦ isingTransfer_symm x y)
    (fun _ _ _ x y ↦ isingTransfer_pos x y) fun _ _ _ x y ↦ isingTransfer_ne_top x y

/-! ## Georgii (12.21), (12.22): the boundary law equation and the fixed point equation -/

/-- The constant boundary law of **Proposition (12.24)**: `ℓ_t(-) = 1`,
`ℓ_t(+) = exp (2t - 2h/(d+1))`. -/
def isingBoundaryVec (d : ℕ) (h t : ℝ) (x : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (exp ((t - h / (d + 1)) * (spin x + 1)))

@[simp] lemma isingBoundaryVec_false : isingBoundaryVec d h t false = 1 := by
  rw [isingBoundaryVec]
  norm_num [spin]

@[simp] lemma isingBoundaryVec_true :
    isingBoundaryVec d h t true = ENNReal.ofReal (exp (2 * t - 2 * (h / (d + 1)))) := by
  rw [isingBoundaryVec]
  norm_num [spin]
  ring_nf

lemma isingBoundaryVec_pos (x : Bool) : 0 < isingBoundaryVec d h t x :=
  ENNReal.ofReal_pos.2 (exp_pos _)

lemma isingBoundaryVec_ne_top (x : Bool) : isingBoundaryVec d h t x ≠ ⊤ := ENNReal.ofReal_ne_top

private lemma two_mul_exp_mul_cosh (a b : ℝ) :
    2 * exp a * cosh b = exp (a + b) + exp (a - b) := by
  rw [cosh_eq, exp_add, exp_sub, exp_neg]
  have := exp_pos b
  field_simp

/-- The row vector `ℓ_t Q` at `+`. -/
lemma tsum_isingBoundaryVec_mul_isingTransfer_true :
    ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y true
      = ENNReal.ofReal (2 * exp t * cosh (t + J)) := by
  rw [tsum_bool, isingBoundaryVec_false, isingBoundaryVec_true, isingTransfer_false_true,
    isingTransfer_true_true, one_mul, ← ENNReal.ofReal_mul (exp_nonneg _), ← exp_add,
    ← ENNReal.ofReal_add (exp_nonneg _) (exp_nonneg _)]
  congr 1
  rw [two_mul_exp_mul_cosh, add_comm (exp (t + (t + J))),
    show (2 : ℝ) * t - 2 * (h / (d + 1)) + (J + 2 * (h / (d + 1))) = t + (t + J) by ring,
    show -J = t - (t + J) by ring]

/-- The row vector `ℓ_t Q` at `-`. -/
lemma tsum_isingBoundaryVec_mul_isingTransfer_false :
    ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false
      = ENNReal.ofReal (2 * exp (t - 2 * (h / (d + 1))) * cosh (t - J)) := by
  rw [tsum_bool, isingBoundaryVec_false, isingBoundaryVec_true, isingTransfer_false_false,
    isingTransfer_true_false, one_mul, ← ENNReal.ofReal_mul (exp_nonneg _), ← exp_add,
    ← ENNReal.ofReal_add (exp_nonneg _) (exp_nonneg _)]
  congr 1
  rw [two_mul_exp_mul_cosh, add_comm (exp (t - 2 * (h / (d + 1)) + (t - J))),
    show (2 : ℝ) * t - 2 * (h / (d + 1)) + -J = t - 2 * (h / (d + 1)) + (t - J) by ring,
    show J - 2 * (h / (d + 1)) = t - 2 * (h / (d + 1)) - (t - J) by ring]

lemma tsum_isingBoundaryVec_mul_isingTransfer_pos (x : Bool) :
    0 < ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x := by
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum false)
  exact ENNReal.mul_pos (isingBoundaryVec_pos false).ne' (isingTransfer_pos _ _).ne'

lemma tsum_isingBoundaryVec_mul_isingTransfer_ne_top (x : Bool) :
    ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x ≠ ⊤ := by
  cases x
  · rw [tsum_isingBoundaryVec_mul_isingTransfer_false]; exact ENNReal.ofReal_ne_top
  · rw [tsum_isingBoundaryVec_mul_isingTransfer_true]; exact ENNReal.ofReal_ne_top

private lemma field_split (d : ℕ) (h : ℝ) :
    h / (d + 1) + (d : ℝ) * (h / (d + 1)) = h := by
  have hd : ((d : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- The ratio `(ℓ_t Q)(+) / (ℓ_t Q)(-)` of Georgii (12.21) is `exp (2h/(d+1) + 2 φ_J(t))`. -/
lemma tsum_isingBoundaryVec_div :
    (∑' y, isingBoundaryVec d h t y * isingTransfer d J h y true) /
        (∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false)
      = ENNReal.ofReal (exp (2 * (h / (d + 1)) + 2 * logCoshRatio J t)) := by
  have hcJ := cosh_pos (t - J)
  have hcJ' := cosh_pos (t + J)
  have hpos : (0 : ℝ) < 2 * exp (t - 2 * (h / (d + 1))) * cosh (t - J) := by positivity
  rw [tsum_isingBoundaryVec_mul_isingTransfer_true,
    tsum_isingBoundaryVec_mul_isingTransfer_false, ← ENNReal.ofReal_div_of_pos hpos]
  congr 1
  rw [exp_add, exp_two_mul_logCoshRatio, exp_sub]
  have h1 := exp_pos t
  have h2 : (0 : ℝ) < exp (2 * (h / (d + 1))) := exp_pos _
  field_simp

/-- **Georgii (12.21) ⇔ (12.22), two parameters.** The row `ℓ_t Q` renormalised at `-1` and
raised to the power `d` is `ℓ_s` exactly when `s = h + d φ_J(t)`. Georgii's equation (12.21) is
the diagonal case `s = t` (`isingBoundaryVec_solves_iff`); the off-diagonal case is the alternating
equation (12.34). -/
theorem isingBoundaryVec_solves_iff' {s : ℝ} :
    (∀ x : Bool, isingBoundaryVec d h s x
        = ((∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x) /
            ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false) ^ d)
      ↔ s = h + d * logCoshRatio J t := by
  have hc := field_split d h
  have expand : (d : ℝ) * (2 * (h / (d + 1)) + 2 * logCoshRatio J t)
      = 2 * ((d : ℝ) * (h / (d + 1))) + 2 * ((d : ℝ) * logCoshRatio J t) := by ring
  constructor
  · intro hsol
    have hthis := hsol true
    rw [tsum_isingBoundaryVec_div, isingBoundaryVec_true,
      ← ENNReal.ofReal_pow (exp_nonneg _), ← exp_nat_mul,
      ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp, expand] at hthis
    linarith
  · intro hsol x
    have hkey : 2 * s - 2 * (h / (d + 1))
        = (d : ℝ) * (2 * (h / (d + 1)) + 2 * logCoshRatio J t) := by rw [expand]; linarith
    cases x
    · rw [isingBoundaryVec_false, ENNReal.div_self
        (tsum_isingBoundaryVec_mul_isingTransfer_pos false).ne'
        (tsum_isingBoundaryVec_mul_isingTransfer_ne_top false), one_pow]
    · rw [tsum_isingBoundaryVec_div, isingBoundaryVec_true,
        ← ENNReal.ofReal_pow (exp_nonneg _), ← exp_nat_mul, hkey]

/-- **Georgii (12.21) ⇔ (12.22).** With `s = ℓ_t(+) = exp (2t - 2h/(d+1))`, the boundary-law
equation (12.16) for the Ising transfer matrix (12.20) on `𝒞𝒯(d)`,
`s = ((Q(-,+) + s Q(+,+)) / (Q(-,-) + s Q(+,-)))^d`, is Georgii's equation (12.22)
`t = h + d φ_J(t)`, with `φ_J = Real.logCoshRatio J` of (12.23). -/
theorem isingBoundaryVec_solves_iff :
    (∀ x : Bool, isingBoundaryVec d h t x
        = ((∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x) /
            ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false) ^ d)
      ↔ t = h + d * logCoshRatio J t := isingBoundaryVec_solves_iff'

/-- **Georgii (12.21) ⇔ (12.22), as a boundary law.** On `𝒞𝒯(d)` the constant family `ℓ_t` is a
boundary law of Definition (12.10) for the Ising transfer matrix (12.20) iff `t` solves the
fixed point equation (12.22). -/
theorem isBoundaryLaw_isingBoundaryVec_iff (hG : G.IsCayleyTree d) :
    IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) (fun _ _ ↦ isingBoundaryVec d h t)
      ↔ t = h + d * logCoshRatio J t := by
  rw [isBoundaryLaw_const_iff G hG.isRegularOfDegree (fun x y ↦ isingTransfer_pos x y)
    (fun x ↦ isingBoundaryVec_pos x) (fun x ↦ isingBoundaryVec_ne_top x)
    (isingBoundaryVec_false (d := d) (h := h) (t := t)) hG.exists_adj,
    ← isingBoundaryVec_solves_iff (d := d) (J := J) (h := h) (t := t)]
  refine and_iff_left ?_
  rw [tsum_bool]
  exact ENNReal.add_ne_top.2
    ⟨ENNReal.pow_ne_top (tsum_isingBoundaryVec_mul_isingTransfer_ne_top false),
      ENNReal.pow_ne_top (tsum_isingBoundaryVec_mul_isingTransfer_ne_top true)⟩

/-! ## Georgii Proposition (12.24): the completely homogeneous Markov chains `μ_t` -/

section Chains

/-- **Georgii (12.19), (12.20).** The Ising specification `γ^{J,h}` on the Cayley tree `𝒞𝒯(d)`,
as the transfer specification (12.8) of the transfer matrix (12.20). -/
def isingTreeSpecification (G : SimpleGraph S) [G.LocallyFinite] (d : ℕ) (J h : ℝ) :
    Specification S Bool :=
  transferSpecification G (isTransferFamily_isingTransfer G d J h)

/-- **Georgii Proposition (12.24).** The Markov chain `μ_t` attached to a solution `t` of the
fixed point equation (12.22): the measure (12.13) of the boundary law `ℓ_t`. -/
def isingChain (hG : G.IsCayleyTree d) (hsol : t = h + d * logCoshRatio J t) :
    Measure (S → Bool) :=
  boundaryLawMeasure (isTransferFamily_isingTransfer G d J h)
    ((isBoundaryLaw_isingBoundaryVec_iff hG).2 hsol) hG.isTree

instance isProbabilityMeasure_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) : IsProbabilityMeasure (isingChain hG hsol) :=
  isProbabilityMeasure_boundaryLawMeasure _ _ _

/-- **Georgii Proposition (12.24).** `μ_t ∈ 𝒢(J, h)`. -/
theorem isGibbsMeasure_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) :
    (isingTreeSpecification G d J h).IsGibbsMeasure (isingChain hG hsol) :=
  IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _ _

/-- **Georgii Proposition (12.24).** `μ_t` is a completely homogeneous Markov chain. -/
theorem isCompletelyHomogeneousMarkovChain_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) :
    IsCompletelyHomogeneousMarkovChain G (isingChain hG hsol) :=
  IsBoundaryLaw.isCompletelyHomogeneousMarkovChain_boundaryLawMeasure _ _ _

end Chains

/-! ### Georgii Proposition (12.24): the transition matrix `P_t` -/

/-- **Georgii Proposition (12.24).** The transition matrix `P_t` of `μ_t`:
`P_t(-,-) = e^{J-t}/2cosh(J-t)`, `P_t(-,+) = e^{t-J}/2cosh(J-t)`,
`P_t(+,-) = e^{-J-t}/2cosh(J+t)`, `P_t(+,+) = e^{J+t}/2cosh(J+t)`. -/
def isingTransition (J t : ℝ) (x y : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (J * spin x * spin y + t * spin y) / (2 * cosh (t + J * spin x)))

@[simp] lemma isingTransition_false_false :
    isingTransition J t false false = ENNReal.ofReal (exp (J - t) / (2 * cosh (t - J))) := by
  rw [isingTransition]
  norm_num [spin]
  ring_nf

@[simp] lemma isingTransition_false_true :
    isingTransition J t false true = ENNReal.ofReal (exp (t - J) / (2 * cosh (t - J))) := by
  rw [isingTransition]
  norm_num [spin]
  ring_nf

@[simp] lemma isingTransition_true_false :
    isingTransition J t true false = ENNReal.ofReal (exp (-J - t) / (2 * cosh (t + J))) := by
  rw [isingTransition]
  norm_num [spin]
  ring_nf

@[simp] lemma isingTransition_true_true :
    isingTransition J t true true = ENNReal.ofReal (exp (J + t) / (2 * cosh (t + J))) := by
  rw [isingTransition]
  norm_num [spin]

private lemma exp_div_two_mul_exp_mul {a b c : ℝ} (hc : 0 < c) :
    exp a / (2 * exp b * c) = exp (a - b) / (2 * c) := by
  rw [exp_sub]
  have := exp_pos b
  field_simp

/-- The row sums of the transfer weights, as a row of the matrix. -/
lemma tsum_isingBoundaryVec_mul_isingTransfer_row (x : Bool) :
    ∑' y, isingBoundaryVec d h t y * isingTransfer d J h x y
      = ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x :=
  tsum_congr fun y ↦ by rw [isingTransfer_symm]

omit [DecidableEq S] in
/-- **Georgii Proposition (12.24), the matrix `P_t`.** The transition matrix
`boundaryLawTransition` of the boundary law `ℓ_t` is Georgii's `P_t`. -/
theorem boundaryLawTransition_isingBoundaryVec (i j : S) (x y : Bool) :
    boundaryLawTransition (fun _ _ : S ↦ isingTransfer d J h)
      (fun _ _ ↦ isingBoundaryVec d h t) i j x y = isingTransition J t x y := by
  rw [boundaryLawTransition, tsum_isingBoundaryVec_mul_isingTransfer_row]
  cases x <;> cases y <;>
    simp only [tsum_isingBoundaryVec_mul_isingTransfer_false,
      tsum_isingBoundaryVec_mul_isingTransfer_true, isingBoundaryVec_false, isingBoundaryVec_true,
      isingTransfer_false_false, isingTransfer_false_true, isingTransfer_true_false,
      isingTransfer_true_true, isingTransition_false_false, isingTransition_false_true,
      isingTransition_true_false, isingTransition_true_true, one_mul,
      ← ENNReal.ofReal_mul (exp_nonneg _), ← exp_add]
  all_goals rw [← ENNReal.ofReal_div_of_pos (by positivity),
    exp_div_two_mul_exp_mul (by positivity)]
  all_goals congr 2
  all_goals refine congrArg exp ?_
  all_goals ring

/-- **Georgii Proposition (12.24).** The transition matrices of `μ_t` are `P_t` on every bond. -/
theorem transitionProb_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) {i j : S} (hij : G.Adj i j) (x y : Bool) :
    transitionProb (isingChain hG hsol) i j x y = isingTransition J t x y := by
  have hQ := isTransferFamily_isingTransfer G d J h
  have hl := (isBoundaryLaw_isingBoundaryVec_iff (t := t) hG).2 hsol
  have hchain : isingChain hG hsol = boundaryLawMeasure hQ hl hG.isTree := rfl
  have hpos : 0 < isingChain hG hsol ((fun σ : S → Bool ↦ σ i) ⁻¹' {x}) := by
    rw [preimage_singleton_eq_cyl i x (baseConfig (S := S) (E := Bool))]
    exact measure_cyl_pos_of_isGibbsMeasure hQ (isGibbsMeasure_isingChain hG hsol) _ _
  have hstep := hl.measure_preimage_inter_preimage_eq hQ hG.isTree hij x y
  rw [transitionProb, Set.inter_comm, hchain, hstep, ← hchain,
    ENNReal.mul_div_cancel_right hpos.ne' (measure_ne_top _ _),
    boundaryLawTransition_isingBoundaryVec]

/-! ### Georgii Proposition (12.24): the marginal `α_t` and the magnetization (12.25) -/

private lemma exp_two_mul' (a : ℝ) : exp (2 * a) = exp a * exp a := by
  rw [← exp_add]; ring_nf

private lemma two_mul_cosh (a : ℝ) : 2 * cosh a = exp a + exp (-a) := by
  rw [cosh_eq]; ring

/-- **Georgii Proposition (12.24).** The one-dimensional marginal
`α_t = (2e^{-2J} + 2 cosh 2t)^{-1} (e^{-2J} + e^{-2t}, e^{-2J} + e^{2t})` of `μ_t`. -/
def isingMarginal (J t : ℝ) (x : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal ((exp (-(2 * J)) + exp (2 * t * spin x)) /
    (2 * exp (-(2 * J)) + 2 * cosh (2 * t)))

lemma isingMarginal_denom_pos (J t : ℝ) :
    (0 : ℝ) < 2 * exp (-(2 * J)) + 2 * cosh (2 * t) := by positivity

@[simp] lemma isingMarginal_false :
    isingMarginal J t false
      = ENNReal.ofReal ((exp (-(2 * J)) + exp (-(2 * t))) /
          (2 * exp (-(2 * J)) + 2 * cosh (2 * t))) := by
  rw [isingMarginal]
  norm_num [spin]

@[simp] lemma isingMarginal_true :
    isingMarginal J t true
      = ENNReal.ofReal ((exp (-(2 * J)) + exp (2 * t)) /
          (2 * exp (-(2 * J)) + 2 * cosh (2 * t))) := by
  rw [isingMarginal]
  norm_num [spin]

lemma tsum_isingMarginal (J t : ℝ) : ∑' x, isingMarginal J t x = 1 := by
  have hD := isingMarginal_denom_pos J t
  rw [tsum_bool, isingMarginal_false, isingMarginal_true,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_eq_one, ← add_div,
    div_eq_one_iff_eq hD.ne', two_mul_cosh]
  ring

lemma isingTransition_pos (J t : ℝ) (x y : Bool) : 0 < isingTransition J t x y := by
  rw [isingTransition]
  refine ENNReal.ofReal_pos.2 (div_pos (exp_pos _) ?_)
  positivity

lemma tsum_isingTransition (J t : ℝ) (x : Bool) : ∑' y, isingTransition J t x y = 1 := by
  have hm := cosh_pos (t - J)
  have hp := cosh_pos (t + J)
  cases x
  · rw [tsum_bool, isingTransition_false_false, isingTransition_false_true,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_eq_one,
      ← add_div, div_eq_one_iff_eq (by positivity), two_mul_cosh]
    rw [show -(t - J) = J - t by ring]
    exact add_comm _ _
  · rw [tsum_bool, isingTransition_true_false, isingTransition_true_true,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_eq_one,
      ← add_div, div_eq_one_iff_eq (by positivity), two_mul_cosh]
    rw [show -(t + J) = -J - t by ring, show t + J = J + t by ring]
    exact add_comm _ _

/-- **Georgii Comment (12.3)(5) for `P_t`.** `P_t` is reversible with respect to `α_t`. -/
theorem isingMarginal_mul_isingTransition (J t : ℝ) (x y : Bool) :
    isingMarginal J t x * isingTransition J t x y
      = isingMarginal J t y * isingTransition J t y x := by
  have hu := exp_pos t
  have hv := exp_pos J
  have hD := isingMarginal_denom_pos J t
  have hm := cosh_pos (t - J)
  have hp := cosh_pos (t + J)
  cases x <;> cases y
  · rfl
  · rw [isingMarginal_false, isingMarginal_true, isingTransition_false_true,
      isingTransition_true_false, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [cosh_eq, exp_sub, exp_add, exp_neg, exp_two_mul']
    field_simp
    ring
  · rw [isingMarginal_false, isingMarginal_true, isingTransition_false_true,
      isingTransition_true_false, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [cosh_eq, exp_sub, exp_add, exp_neg, exp_two_mul']
    field_simp
    ring
  · rfl

/-- **Georgii Proposition (12.24).** The one-dimensional marginals of `μ_t` are `α_t`. -/
theorem measure_preimage_singleton_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) (k : S) (x : Bool) :
    isingChain hG hsol ((fun σ : S → Bool ↦ σ k) ⁻¹' {x}) = isingMarginal J t x := by
  obtain ⟨j, hkj⟩ := hG.exists_adj_right k
  exact measure_preimage_singleton_eq_of_reversible (G := G) (isingTransition_pos J t)
    (tsum_isingTransition J t) (tsum_isingMarginal J t) (isingMarginal_mul_isingTransition J t)
    (fun i j hij x y _ ↦ transitionProb_isingChain hG hsol hij x y) hkj x

/-- **Georgii (12.25).** The magnetization of `μ_t` is `sinh 2t / (e^{-2J} + cosh 2t)`; in
particular it has the same sign as `t`. -/
theorem integral_spin_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) (i : S) :
    ∫ σ, spin (σ i) ∂(isingChain hG hsol)
      = sinh (2 * t) / (exp (-(2 * J)) + cosh (2 * t)) := by
  have hmeas : Measurable (fun σ : S → Bool ↦ σ i) := measurable_pi_apply i
  have hprob : IsProbabilityMeasure ((isingChain hG hsol).map (fun σ : S → Bool ↦ σ i)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hint : Integrable spin ((isingChain hG hsol).map (fun σ : S → Bool ↦ σ i)) :=
    Integrable.of_finite
  have hval : ∀ x : Bool,
      ((isingChain hG hsol).map (fun σ : S → Bool ↦ σ i)).real {x}
        = (isingMarginal J t x).toReal := fun x ↦ by
    rw [measureReal_def, Measure.map_apply hmeas (measurableSet_singleton x),
      measure_preimage_singleton_isingChain hG hsol i x]
  rw [← integral_map hmeas.aemeasurable measurable_spin.aestronglyMeasurable,
    integral_fintype hint,
    show (Finset.univ : Finset Bool) = {true, false} from Fintype.univ_bool,
    Finset.sum_insert (by simp), Finset.sum_singleton, hval true, hval false]
  have hD : (0 : ℝ) < 2 * exp (-(2 * J)) + 2 * cosh (2 * t) := isingMarginal_denom_pos J t
  have hD' : (0 : ℝ) < exp (-(2 * J)) + cosh (2 * t) := by positivity
  rw [isingMarginal_false, isingMarginal_true, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), sinh_eq, cosh_eq]
  simp only [spin, smul_eq_mul]
  norm_num
  rw [cosh_eq] at hD'
  field_simp
  ring

/-- **Georgii, after Proposition (12.24).** The coupling constant is recovered from the bond
marginal of `μ_t`: `P_t(+,+) P_t(-,-) / (P_t(+,-) P_t(-,+)) = e^{4J}`. -/
theorem isingTransition_mul_div_mul (J t : ℝ) :
    isingTransition J t true true * isingTransition J t false false
      = ENNReal.ofReal (exp (4 * J))
        * (isingTransition J t true false * isingTransition J t false true) := by
  have hm := cosh_pos (t - J)
  have hp := cosh_pos (t + J)
  rw [isingTransition_true_true, isingTransition_false_false, isingTransition_true_false,
    isingTransition_false_true, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 := exp_pos t
  have h2 := exp_pos J
  simp only [show (4 : ℝ) * J = J + J + (J + J) from by ring, exp_add, exp_sub, exp_neg]
  field_simp

/-! ### Georgii Proposition (12.24): the one-to-one correspondence -/

/-- **Georgii Proposition (12.24), injectivity.** Distinct solutions of (12.22) give distinct
completely homogeneous Markov chains. -/
theorem isingChain_inj (hG : G.IsCayleyTree d) {t₁ t₂ : ℝ}
    (hs₁ : t₁ = h + d * logCoshRatio J t₁) (hs₂ : t₂ = h + d * logCoshRatio J t₂)
    (heq : isingChain hG hs₁ = isingChain hG hs₂) : t₁ = t₂ := by
  have hQ := isTransferFamily_isingTransfer G d J h
  have hl₁ := (isBoundaryLaw_isingBoundaryVec_iff (t := t₁) hG).2 hs₁
  have hl₂ := (isBoundaryLaw_isingBoundaryVec_iff (t := t₂) hG).2 hs₂
  have hvec : isingBoundaryVec d h t₁ = isingBoundaryVec d h t₂ :=
    eq_of_isBoundaryLaw_const_boundaryLawMeasure_eq hQ hG.isTree false hl₁ hl₂
      isingBoundaryVec_false isingBoundaryVec_false hG.exists_adj heq
  have hval := congrFun hvec true
  rw [isingBoundaryVec_true, isingBoundaryVec_true,
    ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp] at hval
  linarith

/-- **Georgii Proposition (12.24), surjectivity.** Every completely homogeneous Markov chain in
`𝒢(J, h)` is `μ_t` for a solution `t` of (12.22). -/
theorem exists_eq_isingChain (hG : G.IsCayleyTree d) {μ : Measure (S → Bool)}
    [IsProbabilityMeasure μ] (hGibbs : (isingTreeSpecification G d J h).IsGibbsMeasure μ)
    (hcc : IsCompletelyHomogeneousMarkovChain G μ) :
    ∃ (t : ℝ) (hsol : t = h + d * logCoshRatio J t), μ = isingChain hG hsol := by
  obtain ⟨i₀, j₀, hij₀⟩ := hG.exists_adj
  obtain ⟨ℓ0, hℓ0, ha1, hμeq, h16, -⟩ :=
    hcc.exists_isBoundaryLaw_const_solves_and_eq (isTransferFamily_isingTransfer G d J h)
      hG.isTree hGibbs false hG.isRegularOfDegree (fun x y ↦ isingTransfer_pos x y)
      hG.exists_adj
  have hpos : 0 < (ℓ0 true).toReal :=
    ENNReal.toReal_pos (hℓ0.pos hij₀ true).ne' (hℓ0.ne_top hij₀ true)
  obtain ⟨t, hfun⟩ : ∃ t : ℝ, ℓ0 = isingBoundaryVec d h t := by
    refine ⟨h / (d + 1) + log ((ℓ0 true).toReal) / 2, funext fun x ↦ ?_⟩
    cases x
    · rw [isingBoundaryVec_false, ha1]
    · rw [isingBoundaryVec_true,
        show 2 * (h / (d + 1) + log ((ℓ0 true).toReal) / 2) - 2 * (h / (d + 1))
          = log ((ℓ0 true).toReal) by ring,
        exp_log hpos, ENNReal.ofReal_toReal (hℓ0.ne_top hij₀ true)]
  subst hfun
  have hsol : t = h + d * logCoshRatio J t := isingBoundaryVec_solves_iff.1 h16
  exact ⟨t, hsol, hμeq⟩


/-! ## Georgii (12.32): the parameters of an arbitrary boundary law

Georgii attaches to a boundary law `{ℓ_{ij}}` normalised at `-1` the numbers
`t_{ij} = h (d+1)^{-1} + ½ log ℓ_{ij}(+)`; equation (12.15) then becomes (12.32),
`t_{ij} = h + ∑_{k ∈ ∂i ∖ {j}} φ_J(t_{ki})`. Step 1 of the proof of Theorem (12.31) squeezes
these numbers between the extremal solutions of (12.22). -/

section Params

/-- Georgii's parameter `t_{ij} = h(d+1)^{-1} + ½ log ℓ_{ij}(+)` of a boundary-law vector
normalised at `-1`. It inverts `isingBoundaryVec` (`isingParam_isingBoundaryVec`,
`isingBoundaryVec_isingParam`). -/
def isingParam (d : ℕ) (h : ℝ) (ℓ0 : Bool → ℝ≥0∞) : ℝ :=
  h / (d + 1) + log (ℓ0 true).toReal / 2

@[simp] lemma isingParam_isingBoundaryVec (d : ℕ) (h t : ℝ) :
    isingParam d h (isingBoundaryVec d h t) = t := by
  rw [isingParam, isingBoundaryVec_true, ENNReal.toReal_ofReal (exp_nonneg _), log_exp]
  ring

lemma isingBoundaryVec_isingParam (d : ℕ) (h : ℝ) {ℓ0 : Bool → ℝ≥0∞} (h1 : ℓ0 false = 1)
    (hpos : 0 < ℓ0 true) (htop : ℓ0 true ≠ ⊤) :
    isingBoundaryVec d h (isingParam d h ℓ0) = ℓ0 := by
  have hr : 0 < (ℓ0 true).toReal := ENNReal.toReal_pos hpos.ne' htop
  funext x
  cases x
  · rw [isingBoundaryVec_false, h1]
  · rw [isingBoundaryVec_true, isingParam,
      show 2 * (h / (d + 1) + log (ℓ0 true).toReal / 2) - 2 * (h / (d + 1))
        = log (ℓ0 true).toReal by ring, exp_log hr, ENNReal.ofReal_toReal htop]

/-- A positive finite vector normalised at `-1` is `ℓ_t` for `t` its own parameter. -/
lemma exists_eq_isingBoundaryVec (d : ℕ) (h : ℝ) {ℓ0 : Bool → ℝ≥0∞} (h1 : ℓ0 false = 1)
    (hpos : 0 < ℓ0 true) (htop : ℓ0 true ≠ ⊤) : ∃ t : ℝ, ℓ0 = isingBoundaryVec d h t :=
  ⟨isingParam d h ℓ0, (isingBoundaryVec_isingParam d h h1 hpos htop).symm⟩

lemma apply_true_eq_of_normalized (d : ℕ) (h : ℝ) {ℓ0 : Bool → ℝ≥0∞} (h1 : ℓ0 false = 1)
    (hpos : 0 < ℓ0 true) (htop : ℓ0 true ≠ ⊤) :
    ℓ0 true = ENNReal.ofReal (exp (2 * isingParam d h ℓ0 - 2 * (h / (d + 1)))) := by
  obtain ⟨t, rfl⟩ := exists_eq_isingBoundaryVec d h h1 hpos htop
  rw [isingParam_isingBoundaryVec, isingBoundaryVec_true]

/-- The ratio `(ℓ Q)(+) / (ℓ Q)(-)` of (12.21) in terms of the parameter of `ℓ`. -/
lemma tsum_div_of_normalized (d : ℕ) (J h : ℝ) {ℓ0 : Bool → ℝ≥0∞} (h1 : ℓ0 false = 1)
    (hpos : 0 < ℓ0 true) (htop : ℓ0 true ≠ ⊤) :
    (∑' y, ℓ0 y * isingTransfer d J h y true) / ∑' y, ℓ0 y * isingTransfer d J h y false
      = ENNReal.ofReal (exp (2 * (h / (d + 1)) + 2 * logCoshRatio J (isingParam d h ℓ0))) := by
  obtain ⟨t, rfl⟩ := exists_eq_isingBoundaryVec d h h1 hpos htop
  rw [isingParam_isingBoundaryVec]
  exact tsum_isingBoundaryVec_div

variable {ℓ : S → S → Bool → ℝ≥0∞}

/-- **Georgii (12.32).** For a boundary law of the Ising transfer matrix (12.20) on `𝒞𝒯(d)`
normalised at `-1`, the parameters `t_{ij}` satisfy
`t_{ij} = h + ∑_{k ∈ ∂i ∖ {j}} φ_J(t_{ki})`. -/
theorem isingParam_eq_add_sum (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) {i j : S} (hij : G.Adj i j) :
    isingParam d h (ℓ i j)
      = h + ∑ k ∈ (G.neighborFinset i).erase j, logCoshRatio J (isingParam d h (ℓ k i)) := by
  classical
  have hadj : ∀ k ∈ (G.neighborFinset i).erase j, G.Adj k i := fun k hk ↦
    ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm
  have h15 := hℓ.eq_prod_div_of_normalized (fun _ _ _ x y ↦ isingTransfer_pos x y) ha hij true
  have hfac : ∀ k ∈ (G.neighborFinset i).erase j,
      (∑' y, ℓ k i y * isingTransfer d J h y true)
          / ∑' y, ℓ k i y * isingTransfer d J h y false
        = ENNReal.ofReal
            (exp (2 * (h / (d + 1)) + 2 * logCoshRatio J (isingParam d h (ℓ k i)))) :=
    fun k hk ↦ tsum_div_of_normalized d J h (ha (hadj k hk)) (hℓ.pos (hadj k hk) true)
      (hℓ.ne_top (hadj k hk) true)
  rw [Finset.prod_congr rfl hfac,
    ← ENNReal.ofReal_prod_of_nonneg (fun k _ ↦ (exp_nonneg _)), ← exp_sum,
    apply_true_eq_of_normalized d h (ha hij) (hℓ.pos hij true) (hℓ.ne_top hij true),
    ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp] at h15
  rw [Finset.sum_add_distrib, Finset.sum_const, hG.card_neighborFinset_erase hij,
    ← Finset.mul_sum, nsmul_eq_mul] at h15
  have hc := field_split d h
  linarith

/-! ### Step 1 of the proof of Theorem (12.31): the parameters lie between `t₋` and `t₊` -/

/-- The oriented bonds `B̄` of `G`, the index set of Georgii's family `{t_{ij}}`. -/
private def orientedBonds (G : SimpleGraph S) : Type _ := {p : S × S // G.Adj p.1 p.2}

private lemma isingParam_le_add_mul (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) {i j : S} (hij : G.Adj i j) :
    isingParam d h (ℓ i j) ≤ h + d * J := by
  rw [isingParam_eq_add_sum hG hℓ ha hij]
  have hbound : ∑ k ∈ (G.neighborFinset i).erase j, logCoshRatio J (isingParam d h (ℓ k i))
      ≤ ∑ _k ∈ (G.neighborFinset i).erase j, J :=
    Finset.sum_le_sum fun k _ ↦ (logCoshRatio_lt hJ _).le
  rw [Finset.sum_const, hG.card_neighborFinset_erase hij, nsmul_eq_mul] at hbound
  linarith

private lemma sub_mul_le_isingParam (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) {i j : S} (hij : G.Adj i j) :
    h - d * J ≤ isingParam d h (ℓ i j) := by
  rw [isingParam_eq_add_sum hG hℓ ha hij]
  have hbound : ∑ _k ∈ (G.neighborFinset i).erase j, (-J)
      ≤ ∑ k ∈ (G.neighborFinset i).erase j, logCoshRatio J (isingParam d h (ℓ k i)) :=
    Finset.sum_le_sum fun k _ ↦ (neg_lt_logCoshRatio hJ _).le
  rw [Finset.sum_const, hG.card_neighborFinset_erase hij, nsmul_eq_mul] at hbound
  linarith

/-- **Georgii, step 1 of the proof of Theorem (12.31), upper bound.** The parameters of an
arbitrary normalised boundary law are dominated by a solution of (12.22). -/
theorem exists_treeField_eq_and_forall_isingParam_le (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) :
    ∃ p : ℝ, treeField d J p = h ∧ ∀ ⦃i j⦄, G.Adj i j → isingParam d h (ℓ i j) ≤ p := by
  set u : orientedBonds G → ℝ := fun q ↦ isingParam d h (ℓ q.1.1 q.1.2) with hu
  have hstep : ∀ c : ℝ, (∀ q, u q ≤ c) → ∀ q, u q ≤ Real.treeRecursion d J h c := by
    intro c hc q
    rw [hu]
    simp only
    rw [isingParam_eq_add_sum hG hℓ ha q.2, Real.treeRecursion]
    have hbound : ∑ k ∈ (G.neighborFinset q.1.1).erase q.1.2,
        logCoshRatio J (isingParam d h (ℓ k q.1.1))
        ≤ ∑ _k ∈ (G.neighborFinset q.1.1).erase q.1.2, logCoshRatio J c :=
      Finset.sum_le_sum fun k hk ↦ (monotone_logCoshRatio hJ.le)
        (hc ⟨(k, q.1.1), ((G.mem_neighborFinset q.1.1 k).1 (Finset.mem_of_mem_erase hk)).symm⟩)
    rw [Finset.sum_const, hG.card_neighborFinset_erase q.2, nsmul_eq_mul] at hbound
    linarith
  obtain ⟨p, hp, hple⟩ := Real.exists_treeField_eq_and_forall_le (J := J) hJ (d := d) (h := h)
    (u := u) (fun q ↦ isingParam_le_add_mul hJ hG hℓ ha q.2) hstep
  exact ⟨p, hp, fun i j hij ↦ hple ⟨(i, j), hij⟩⟩

/-- **Georgii, step 1 of the proof of Theorem (12.31), lower bound.** -/
theorem exists_treeField_eq_and_forall_le_isingParam (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) :
    ∃ p : ℝ, treeField d J p = h ∧ ∀ ⦃i j⦄, G.Adj i j → p ≤ isingParam d h (ℓ i j) := by
  set u : orientedBonds G → ℝ := fun q ↦ isingParam d h (ℓ q.1.1 q.1.2) with hu
  have hstep : ∀ c : ℝ, (∀ q, c ≤ u q) → ∀ q, Real.treeRecursion d J h c ≤ u q := by
    intro c hc q
    rw [hu]
    simp only
    rw [isingParam_eq_add_sum hG hℓ ha q.2, Real.treeRecursion]
    have hbound : ∑ _k ∈ (G.neighborFinset q.1.1).erase q.1.2, logCoshRatio J c
        ≤ ∑ k ∈ (G.neighborFinset q.1.1).erase q.1.2,
            logCoshRatio J (isingParam d h (ℓ k q.1.1)) :=
      Finset.sum_le_sum fun k hk ↦ (monotone_logCoshRatio hJ.le)
        (hc ⟨(k, q.1.1), ((G.mem_neighborFinset q.1.1 k).1 (Finset.mem_of_mem_erase hk)).symm⟩)
    rw [Finset.sum_const, hG.card_neighborFinset_erase q.2, nsmul_eq_mul] at hbound
    linarith
  obtain ⟨p, hp, hple⟩ := Real.exists_treeField_eq_and_forall_ge (J := J) hJ (d := d) (h := h)
    (u := u) (fun q ↦ sub_mul_le_isingParam hJ hG hℓ ha q.2) hstep
  exact ⟨p, hp, fun i j hij ↦ hple ⟨(i, j), hij⟩⟩

/-- **Georgii, step 1 of the proof of Theorem (12.31), the uniqueness case.** If (12.22) has a
single solution `t`, then *every* boundary law of the Ising transfer matrix on `𝒞𝒯(d)` normalised
at `-1` is the constant law `ℓ_t`. -/
theorem eq_isingBoundaryVec_of_unique (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ)
    (ha : ∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) {t : ℝ}
    (huniq : ∀ s : ℝ, treeField d J s = h → s = t) {i j : S} (hij : G.Adj i j) :
    ℓ i j = isingBoundaryVec d h t := by
  obtain ⟨p, hp, hple⟩ := exists_treeField_eq_and_forall_isingParam_le hJ hG hℓ ha
  obtain ⟨q, hq, hqle⟩ := exists_treeField_eq_and_forall_le_isingParam hJ hG hℓ ha
  have hpar : isingParam d h (ℓ i j) = t :=
    le_antisymm (huniq p hp ▸ hple hij) (huniq q hq ▸ hqle hij)
  rw [← hpar, isingBoundaryVec_isingParam d h (ha hij) (hℓ.pos hij true) (hℓ.ne_top hij true)]

end Params


/-! ## Georgii Theorem (12.31)(a): `𝒢(J, h) = {μ_*}` outside the critical window

Georgii's steps 1) and 2): every extreme Gibbs measure is a Markov chain (Theorem (12.6)), hence
the measure (12.13) of a boundary law (Theorem (12.12)(b)); normalising that boundary law at `-1`
and squeezing its parameters between the extremal solutions of (12.22) (step 1, above) identifies
it with the constant law `ℓ_{t_*}` as soon as (12.22) has a single solution. So `ex 𝒢(J,h)` is the
singleton `{μ_*}`, and Theorem (7.26) gives `𝒢(J,h) = {μ_*}`. -/

section Uniqueness

variable [Countable S]

/-- **Georgii Theorem (12.31)(a), given a unique solution of (12.22).** If the fixed point
equation (12.22) has `t` as its only solution then `𝒢(J, h) = {μ_t}`. -/
theorem G_isingTreeSpecification_eq_singleton (hJ : 0 < J) (hG : G.IsCayleyTree d)
    {t : ℝ} (hsol : t = h + d * logCoshRatio J t)
    (huniq : ∀ s : ℝ, treeField d J s = h → s = t) :
    _root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)
      = {isingChain hG hsol} := by
  have hQ := isTransferFamily_isingTransfer G d J h
  have hconst : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h)
      (fun _ _ ↦ isingBoundaryVec d h t) := (isBoundaryLaw_isingBoundaryVec_iff hG).2 hsol
  refine G_eq_singleton_of_extremePoints_subset_singleton
    ⟨inferInstance, isGibbsMeasure_isingChain hG hsol⟩ fun μ hμext ↦ ?_
  have hμP : IsProbabilityMeasure μ := hμext.1.1
  have hμG : (transferSpecification G hQ).IsGibbsMeasure μ := hμext.1.2
  have hchain : IsMarkovChain G μ :=
    exists_isMarkovChain_of_mem_extremePoints hG.isTree
      (isMarkovSpecification_transferSpecification hQ) hμext
  have hbl := hchain.isBoundaryLaw_chainBoundaryLaw hQ hμG hG.isTree false
  have hnorm := hbl.isBoundaryLaw_normalizeAt false
  have ha : ∀ ⦃i j⦄, G.Adj i j →
      normalizeBoundaryLaw (chainBoundaryLaw (fun _ _ ↦ isingTransfer d J h) μ false)
        false i j false = 1 := fun i j hij ↦ normalizeBoundaryLaw_apply_self hbl hij false
  have hagree : ∀ ⦃i j⦄, G.Adj i j → ∀ x,
      normalizeBoundaryLaw (chainBoundaryLaw (fun _ _ ↦ isingTransfer d J h) μ false)
        false i j x = isingBoundaryVec d h t x := fun i j hij x ↦ by
    rw [eq_isingBoundaryVec_of_unique hJ hG hnorm ha huniq hij]
  rw [Set.mem_singleton_iff, hchain.eq_boundaryLawMeasure hQ hμG hG.isTree false,
    ← hbl.boundaryLawMeasure_normalizeAt_eq hQ hG.isTree false hnorm,
    hnorm.boundaryLawMeasure_eq_of_forall_adj hQ hG.isTree hconst hagree]
  rfl

/-- **Georgii Theorem (12.31)(a).** On the Cayley tree `𝒞𝒯(d)` (`d ≥ 1`) with a ferromagnetic
coupling `J > 0`, if `J ≤ J(d)` (equivalently `d tanh J ≤ 1`, `Real.le_criticalCoupling_iff`) or
`|h| > h(J, d)`, then `𝒢(J, h) = {μ_*}` for the unique completely homogeneous Markov chain `μ_*`
attached to the unique solution of (12.22). -/
theorem exists_G_isingTreeSpecification_eq_singleton (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hcase : (d : ℝ) * tanh J ≤ 1 ∨ Real.treeCriticalField d J < |h|) :
    ∃ (t : ℝ) (hsol : t = h + d * logCoshRatio J t),
      _root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)
      = {isingChain hG hsol} := by
  obtain ⟨t, ht, huniq⟩ := Real.existsUnique_treeField_eq_of_le_or_lt hJ hcase
  have hsol : t = h + d * logCoshRatio J t := by rw [Real.treeField] at ht; linarith
  exact ⟨t, hsol, G_isingTreeSpecification_eq_singleton hJ hG hsol huniq⟩

end Uniqueness

/-! ## Georgii Theorem (12.31)(b): phase transition inside the critical window

Inside the closed critical window `J > J(d)`, `|h| ≤ h(J, d)` equation (12.22) has at least two
solutions `t₋ < t₊` (Lemma (12.27)(ii), (iii)), hence — by the one-to-one correspondence of
Proposition (12.24) (`isingChain_inj`) — at least two distinct completely homogeneous Markov
chains in `𝒢(J, h)`, and three of them strictly inside the window. -/

section PhaseTransition

/-- **Georgii Theorem (12.31)(b), non-uniqueness.** For `J > J(d)` (i.e. `d tanh J > 1`) and
`|h| ≤ h(J, d)` there are two *distinct* completely homogeneous Markov chains `μ₋ ≠ μ₊` in
`𝒢(J, h)`; in particular `|𝒢(J, h)| > 1`. -/
theorem exists_ne_isingChain (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ∃ (t₁ t₂ : ℝ) (hs₁ : t₁ = h + d * logCoshRatio J t₁)
      (hs₂ : t₂ = h + d * logCoshRatio J t₂), isingChain hG hs₁ ≠ isingChain hG hs₂ := by
  obtain ⟨a, b, hab, hae, hbe⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hsa : a = h + d * logCoshRatio J a := by rw [Real.treeField] at hae; linarith
  have hsb : b = h + d * logCoshRatio J b := by rw [Real.treeField] at hbe; linarith
  exact ⟨a, b, hsa, hsb, fun heq ↦ hab.ne (isingChain_inj hG hsa hsb heq)⟩

/-- **Georgii Theorem (12.31)(b), three phases.** Strictly inside the critical window
`|h| < h(J, d)` the three solutions `t₋ < t_# < t₊` of (12.22) give three pairwise distinct
completely homogeneous Markov chains in `𝒢(J, h)`. -/
theorem exists_three_isingChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d)
    (hh : |h| < Real.treeCriticalField d J) :
    ∃ (t₁ t₂ t₃ : ℝ) (hs₁ : t₁ = h + d * logCoshRatio J t₁)
      (hs₂ : t₂ = h + d * logCoshRatio J t₂) (hs₃ : t₃ = h + d * logCoshRatio J t₃),
      isingChain hG hs₁ ≠ isingChain hG hs₂ ∧ isingChain hG hs₂ ≠ isingChain hG hs₃ ∧
        isingChain hG hs₁ ≠ isingChain hG hs₃ := by
  obtain ⟨a, b, c, hab, hbc, hset⟩ := Real.exists_eq_insert_treeField_eq_of_abs_lt hJ hd hh
  have hmem : ∀ x ∈ ({a, b, c} : Set ℝ), treeField d J x = h := fun x hx ↦ by
    rw [← hset] at hx; exact hx
  have hae := hmem a (by simp)
  have hbe := hmem b (by simp)
  have hce := hmem c (by simp)
  have hsa : a = h + d * logCoshRatio J a := by rw [Real.treeField] at hae; linarith
  have hsb : b = h + d * logCoshRatio J b := by rw [Real.treeField] at hbe; linarith
  have hsc : c = h + d * logCoshRatio J c := by rw [Real.treeField] at hce; linarith
  exact ⟨a, b, c, hsa, hsb, hsc,
    fun heq ↦ hab.ne (isingChain_inj hG hsa hsb heq),
    fun heq ↦ hbc.ne (isingChain_inj hG hsb hsc heq),
    fun heq ↦ (hab.trans hbc).ne (isingChain_inj hG hsa hsc heq)⟩

end PhaseTransition


/-! ## Georgii (12.33): the magnetisation at the critical external field

At `h = -h(J, d)` the critical point `t_{J,d}` of (12.29) solves (12.22), and it is the largest
solution (`Real.le_treeCriticalPoint_of_treeField_eq`), i.e. Georgii's `t₊`. Its magnetisation
(12.25) is `(d - w)^{1/2}(d - w̄)^{1/2}(d - 1)^{-1}`. -/

section CriticalMagnetisation

/-- At the critical external field `h = -h(J, d)`, the critical point `t_{J,d}` solves the fixed
point equation (12.22). -/
theorem treeCriticalPoint_solves (d : ℕ) (J : ℝ) :
    Real.treeCriticalPoint d J
      = -Real.treeCriticalField d J
        + d * logCoshRatio J (Real.treeCriticalPoint d J) := by
  have hval := Real.treeField_treeCriticalPoint d J
  rw [Real.treeField] at hval
  linarith

/-- **Georgii, before (12.33).** At `h = -h(J, d)` the chain `μ₊` attached to the largest solution
of (12.22) is the one attached to the critical point `t_{J,d}`. -/
theorem le_treeCriticalPoint_of_solves (hJ : 0 < J) (hw : 1 < (d : ℝ) * tanh J) {s : ℝ}
    (hs : s = -Real.treeCriticalField d J + d * logCoshRatio J s) :
    s ≤ Real.treeCriticalPoint d J :=
  Real.le_treeCriticalPoint_of_treeField_eq hJ hw (by rw [Real.treeField]; linarith)

/-- **Georgii (12.33).** For `J > J(d)` and `h = -h(J, d)`, the magnetisation of the maximal
completely homogeneous Markov chain `μ₊ = μ_{t_{J,d}}` is
`(d - w)^{1/2} (d - w̄)^{1/2} (d - 1)^{-1} > 0` (`w = tanh J`, `w̄ = w⁻¹`). -/
theorem integral_spin_isingChain_treeCriticalPoint (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hw : 1 < (d : ℝ) * tanh J) (i : S) :
    ∫ σ, spin (σ i) ∂(isingChain hG (treeCriticalPoint_solves d J))
      = √((d : ℝ) - tanh J) * √((d : ℝ) - (tanh J)⁻¹) / ((d : ℝ) - 1) := by
  rw [integral_spin_isingChain hG (treeCriticalPoint_solves d J) i,
    Real.sinh_div_exp_add_cosh_treeCriticalPoint hJ hw]

end CriticalMagnetisation


/-! ## Georgii (12.34), (12.35): the antiferromagnetic case and alternating Markov chains

`𝒞𝒯(d)` is bipartite (`SimpleGraph.IsCayleyTree.exists_bool_coloring`), and Georgii calls a
boundary law *alternating* if `ℓ_{ij}` depends only on the side `c j` of the bipartition that `j`
lies in. For the Ising transfer matrix (12.20) such a law is a pair `(t₀, t₁) = (τ false, τ true)`
solving **(12.34)**, `τ(!b) = h + d φ_J(τ b)` for both `b`; equivalently `τ false` solves
**(12.35)**, `t = ψ_{J,h,d}(t)` with `ψ = (h + d φ_J) ∘ (h + d φ_J)`
(`Real.isFixedPt_treeRecursion₂_iff`). Exchanging the two sides of the bipartition gives Georgii's
second alternating chain, and the two are distinct as soon as `τ false ≠ τ true`. -/

section AlternatingChains

omit [DecidableEq S] [G.LocallyFinite] in
/-- Along a bond, the two sides of the bipartition are exchanged. -/
lemma coloring_eq_not {c : S → Bool} (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {u v : S}
    (huv : G.Adj u v) : c v = !c u := by
  have hne := hc huv
  rcases Bool.eq_false_or_eq_true (c u) with h1 | h1 <;>
    rcases Bool.eq_false_or_eq_true (c v) with h2 | h2 <;> simp_all

/-- **Georgii §12.2, the alternating boundary law.** Given the bipartition `c` of `𝒞𝒯(d)` and a
pair `τ : Bool → ℝ`, the family `ℓ_{ij} = ℓ_{τ (c j)}`. -/
def isingAltLaw (d : ℕ) (h : ℝ) (τ : Bool → ℝ) (c : S → Bool) : S → S → Bool → ℝ≥0∞ :=
  fun _ j ↦ isingBoundaryVec d h (τ (c j))

/-- **Georgii (12.34).** On `𝒞𝒯(d)` with bipartition `c`, the alternating family
`isingAltLaw d h τ c` is a boundary law for the Ising transfer matrix (12.20) iff the pair
`(τ false, τ true)` solves (12.34), i.e. `τ (!b) = h + d φ_J(τ b)` for both `b`. -/
theorem isBoundaryLaw_isingAltLaw_iff (hG : G.IsCayleyTree d) {c : S → Bool}
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {τ : Bool → ℝ} :
    IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) (isingAltLaw d h τ c)
      ↔ ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b) := by
  obtain ⟨i₀, j₀, hij₀⟩ := hG.exists_adj
  refine Iff.trans (isBoundaryLaw_target_iff G hG.isRegularOfDegree
    (fun x y ↦ isingTransfer_pos x y) (m := fun j : S ↦ isingBoundaryVec d h (τ (c j)))
    (fun _ x ↦ isingBoundaryVec_pos x) (fun _ x ↦ isingBoundaryVec_ne_top x)
    (fun _ ↦ isingBoundaryVec_false)) ?_
  have hmass : ∀ i : S, ∑' x, (∑' y, isingBoundaryVec d h (τ (c i)) y
      * isingTransfer d J h y x) ^ (d + 1) ≠ ⊤ := fun i ↦ by
    rw [tsum_bool]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.pow_ne_top (tsum_isingBoundaryVec_mul_isingTransfer_ne_top false),
        ENNReal.pow_ne_top (tsum_isingBoundaryVec_mul_isingTransfer_ne_top true)⟩
  rw [and_iff_left hmass]
  constructor
  · intro hh b
    have key : ∀ ⦃u v : S⦄, G.Adj u v → τ (c v) = h + d * logCoshRatio J (τ (c u)) :=
      fun u v huv ↦ isingBoundaryVec_solves_iff'.1 (hh huv)
    have h1 := key hij₀
    have h2 := key hij₀.symm
    rw [coloring_eq_not hc hij₀] at h1 h2
    have hb : b = c i₀ ∨ b = !c i₀ := by
      rcases Bool.eq_false_or_eq_true (c i₀) with hci | hci <;> cases b <;> simp [hci]
    rcases hb with rfl | rfl
    · exact h1
    · rw [Bool.not_not]
      exact h2
  · intro hh i j hij
    refine isingBoundaryVec_solves_iff'.2 ?_
    rw [coloring_eq_not hc hij]
    exact hh (c i)

/-- **Georgii §12.2.** The alternating Markov chain of a solution of (12.34): the measure (12.13)
of the alternating boundary law. -/
def isingAltChain (hG : G.IsCayleyTree d) {c : S → Bool}
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {τ : Bool → ℝ}
    (hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b)) : Measure (S → Bool) :=
  boundaryLawMeasure (isTransferFamily_isingTransfer G d J h)
    ((isBoundaryLaw_isingAltLaw_iff hG hc).2 hsol) hG.isTree

instance isProbabilityMeasure_isingAltChain (hG : G.IsCayleyTree d) {c : S → Bool}
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {τ : Bool → ℝ}
    (hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b)) :
    IsProbabilityMeasure (isingAltChain hG hc hsol) :=
  isProbabilityMeasure_boundaryLawMeasure _ _ _

/-- **Georgii §12.2.** The alternating Markov chains belong to `𝒢(J, h)`. -/
theorem isGibbsMeasure_isingAltChain (hG : G.IsCayleyTree d) {c : S → Bool}
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {τ : Bool → ℝ}
    (hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b)) :
    (isingTreeSpecification G d J h).IsGibbsMeasure (isingAltChain hG hc hsol) :=
  IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _ _

/-- Exchanging the two sides `S₀`, `S₁` of the bipartition takes a solution of (12.34) to a
solution of (12.34): Georgii's passage from `μ_{-+}` to `μ_{+-}`. -/
theorem isingAltSol_comp_not {τ : Bool → ℝ}
    (hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b)) :
    ∀ b : Bool, (τ ∘ not) (!b) = h + d * logCoshRatio J ((τ ∘ not) b) := by
  intro b
  have hstep := hsol (!b)
  rw [Bool.not_not] at hstep
  simpa only [Function.comp_apply, Bool.not_not] using hstep

/-- **Georgii §12.2, `μ_{-+} ≠ μ_{+-}`.** The two alternating Markov chains obtained from each
other by exchanging the two sides of the bipartition are distinct as soon as `τ false ≠ τ true`. -/
theorem isingAltChain_ne_comp_not (hG : G.IsCayleyTree d) {c : S → Bool}
    (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {τ : Bool → ℝ}
    (hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b)) (hne : τ false ≠ τ true) :
    isingAltChain hG hc hsol ≠ isingAltChain hG hc (isingAltSol_comp_not hsol) := by
  intro heq
  obtain ⟨i, j, hij⟩ := hG.exists_adj
  obtain ⟨κ, -, -, hκ⟩ :=
    IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq
      (isTransferFamily_isingTransfer G d J h) hG.isTree
      ((isBoundaryLaw_isingAltLaw_iff hG hc).2 hsol)
      ((isBoundaryLaw_isingAltLaw_iff hG hc).2 (isingAltSol_comp_not hsol)) heq hij
  have hfalse := hκ false
  rw [isingAltLaw, isingAltLaw] at hfalse
  simp only [isingBoundaryVec_false, mul_one] at hfalse
  have htrue := hκ true
  rw [isingAltLaw, isingAltLaw] at htrue
  simp only [← hfalse, one_mul, isingBoundaryVec_true, Function.comp_apply] at htrue
  rw [ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp] at htrue
  rcases Bool.eq_false_or_eq_true (c i) with hci | hci <;> rw [hci] at htrue <;>
    simp only [Bool.not_false, Bool.not_true] at htrue
  · exact hne (by linarith)
  · exact hne (by linarith)

/-- **Georgii, the antiferromagnetic phase transition.** If (12.35) has a solution `t` which is
*not* a solution of (12.22), the two alternating Markov chains `μ_{-+} ≠ μ_{+-}` both belong to
`𝒢(J, h)`; in particular `|𝒢(J, h)| > 1`. (Compare Georgii's `|𝒢(J,h)| = 1` iff (12.35) has only
one solution: `Real.existsUnique_isFixedPt_treeRecursion₂` gives that single solution whenever
`d |tanh J| ≤ 1`, i.e. `|J| ≤ J(d)`.) -/
theorem exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂ (hG : G.IsCayleyTree d)
    {c : S → Bool} (hc : ∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) {t : ℝ}
    (hfix : Real.treeRecursion₂ d J h t = t) (hne : Real.treeRecursion d J h t ≠ t) :
    ∃ μ ν : Measure (S → Bool), μ ≠ ν ∧
      (isingTreeSpecification G d J h).IsGibbsMeasure μ ∧
      (isingTreeSpecification G d J h).IsGibbsMeasure ν := by
  set τ : Bool → ℝ := fun b ↦ cond b (Real.treeRecursion d J h t) t with hτ
  have hτf : τ false = t := rfl
  have hτt : τ true = Real.treeRecursion d J h t := rfl
  have hsol : ∀ b : Bool, τ (!b) = h + d * logCoshRatio J (τ b) := by
    intro b
    cases b
    · rw [Bool.not_false, hτt, hτf, Real.treeRecursion]
    · rw [Bool.not_true, hτt, hτf]
      exact hfix.symm
  exact ⟨isingAltChain hG hc hsol, isingAltChain hG hc (isingAltSol_comp_not hsol),
    isingAltChain_ne_comp_not hG hc hsol (by rw [hτf, hτt]; exact fun hcon ↦ hne hcon.symm),
    isGibbsMeasure_isingAltChain hG hc hsol,
    isGibbsMeasure_isingAltChain hG hc (isingAltSol_comp_not hsol)⟩

end AlternatingChains

end MeasureTheory.GibbsMeasure.Tree

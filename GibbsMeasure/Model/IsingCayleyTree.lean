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
  (12.19) on `𝒞𝒯(d)`, and `isTransferFamily_isingTransfer` its `IsTransferFamily` property, so
  that `transferSpecification` gives Georgii's `γ^{J,h}`.
* `isingBoundaryVec` — the constant boundary law of Proposition (12.24), `ℓ(-) = 1`,
  `ℓ(+) = exp (2t - 2h/(d+1))`.
* `isBoundaryLaw_isingBoundaryVec_iff` — **Georgii (12.21) ⇔ (12.22)**: `ℓ_t` is a boundary law
  iff `t = h + d φ_J(t)`, with `φ_J = Real.logCoshRatio J` of (12.23).
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

/-- **Georgii (12.21) ⇔ (12.22).** With `s = ℓ_t(+) = exp (2t - 2h/(d+1))`, the boundary-law
equation (12.16) for the Ising transfer matrix (12.20) on `𝒞𝒯(d)`,
`s = ((Q(-,+) + s Q(+,+)) / (Q(-,-) + s Q(+,-)))^d`, is Georgii's equation (12.22)
`t = h + d φ_J(t)`, with `φ_J = Real.logCoshRatio J` of (12.23). -/
theorem isingBoundaryVec_solves_iff :
    (∀ x : Bool, isingBoundaryVec d h t x
        = ((∑' y, isingBoundaryVec d h t y * isingTransfer d J h y x) /
            ∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false) ^ d)
      ↔ t = h + d * logCoshRatio J t := by
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
    have hkey : 2 * t - 2 * (h / (d + 1))
        = (d : ℝ) * (2 * (h / (d + 1)) + 2 * logCoshRatio J t) := by rw [expand]; linarith
    cases x
    · rw [isingBoundaryVec_false, ENNReal.div_self
        (tsum_isingBoundaryVec_mul_isingTransfer_pos false).ne'
        (tsum_isingBoundaryVec_mul_isingTransfer_ne_top false), one_pow]
    · rw [tsum_isingBoundaryVec_div, isingBoundaryVec_true,
        ← ENNReal.ofReal_pow (exp_nonneg _), ← exp_nat_mul, hkey]

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

end MeasureTheory.GibbsMeasure.Tree

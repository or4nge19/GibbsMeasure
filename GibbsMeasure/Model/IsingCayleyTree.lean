/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLawChains
public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.CayleyTree
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.RootedTree
public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.TreeBall
public import Mathlib.LinearAlgebra.Vandermonde
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioFixedPoint
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioAntiferro
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.LogCoshRatioExtremalSolutions

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
  step Georgii takes "in view of (12.7) and (12.9)" — is
  `isingTreeSpecification_eq_isingSpecification` below.
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
* **Theorem (12.31)(b), step 3)**: `mem_extremePoints_G_isingChain_of_isGreatest` and
  `mem_extremePoints_G_isingChain_of_isLeast` — the chains attached to the largest and the
  smallest solution of (12.22) are *extreme* in `𝒢(J, h)`. Georgii's comparison of the ratios
  `r_{Λ,ζ}(μ) = μ(σ_{Λ∪∂Λ} = ζ)/μ(σ_{Λ∪∂Λ} ≡ -1)` is
  `IsBoundaryLaw.measure_cyl_mul_le_of_le` (`TreeBoundaryLaw.lean`) plus the two extremality
  criteria `mem_extremePoints_G_boundaryLawMeasure_of_forall_le` / `..._of_forall_ge`
  (`TreeBoundaryLawChains.lean`); the passage from extreme to arbitrary Gibbs measures is
  `mul_measure_le_mul_measure_of_forall_extremePoints`, Theorem (7.26) as a comparison principle.
  `mem_extremePoints_invariantG_isingChain_of_isGreatest` / `..._of_isLeast` add extremality in
  `𝒢_{I(B)}(J, h) = invariantG` (Georgii (14.14) at `I(B) = graphAutomorphisms`), since a
  completely homogeneous chain is `I(B)`-invariant by Comment (12.3)(5)
  (`mem_invariantG_isingChain`) and an extreme point of a set is extreme in any subset containing
  it. `exists_ne_mem_extremePoints_G_inter_invariantG_isingChain` is the first clause of
  (12.31)(b) in one statement.
* **Theorem (12.31)(b), step 4)**: `isingTreeParam` is Georgii's inhomogeneous family of
  parameters `t_{ij}` attached to a root `r` (`Real.treeBackOrbit`, the backward orbit of `t`
  under `ψ = h + d φ_J` inside `]t₋, t₊[`, on the bonds pointing towards `r`;
  `Real.treeAwayOrbit` on the bonds pointing away), `isBoundaryLaw_isingTreeParam` verifies
  (12.32) for it — through `isBoundaryLaw_isingBoundaryVec_family_iff`, the **converse of
  (12.32)** — and `isingTreeChain` is the Markov chain `ν_t` it defines. `isingTreeChain_inj`,
  `not_isCompletelyHomogeneousMarkovChain_isingTreeChain`,
  `infinite_setOf_mem_G_not_isCompletelyHomogeneous`: the `ν_t` are pairwise distinct, none of
  them is completely homogeneous when `t` is not itself a solution of (12.22), and there are
  infinitely many of them. The rooted-tree input (unique parent, all other neighbours farther) is
  `GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/RootedTree.lean`.
* **(12.33)**: `integral_spin_isingChain_treeCriticalPoint`, the magnetisation
  `(d - w)^{1/2}(d - w̄)^{1/2}(d - 1)^{-1}` of `μ₊` at the critical field `h = -h(J, d)`
  (`treeCriticalPoint_solves`, `le_treeCriticalPoint_of_solves` identify `t₊ = t_{J,d}`).
* **(12.34)**, the antiferromagnetic case: `isingAltLaw` is Georgii's alternating boundary law for
  the bipartition `c` of `𝒞𝒯(d)`, `isBoundaryLaw_isingAltLaw_iff` is (12.34), `isingAltChain` the
  associated alternating Markov chain, and `isingAltChain_ne_comp_not` /
  `exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂` give the two distinct phases
  `μ_{-+} ≠ μ_{+-}` attached to a solution of **(12.35)** that does not solve (12.22).
* **The antiferromagnetic transition itself**, unconditionally:
  `exists_ne_isGibbsMeasure_of_abs_lt_antiferroCriticalField` and
  `exists_ne_isGibbsMeasure_isingSpecification_antiferro` — for `J < -J(d)` (i.e.
  `1 < d |tanh J|`) and `|h| < ĥ(J, d) = Real.antiferroCriticalField d J`, equation (12.35) has a
  solution off (12.22) (`Real.exists_isFixedPt_treeRecursion₂_ne`), so `|𝒢(J, h)| > 1` although
  (12.22) has a unique solution. `ĥ(J,d) = h(-J,d) + 2 t_{-J,d} > 0` is exactly the quantity with
  which Georgii shows his interval `I(J, d)` is non-degenerate.

The real analysis behind (12.23), (12.26)–(12.30), (12.33) and (12.35) — `Real.logCoshRatio`,
`Real.criticalCoupling` `J(d)`, `Real.treeCriticalPoint` `t_{J,d}`, `Real.treeCriticalField`
`h(J,d)`, Lemma (12.27) and the second iterate `Real.treeRecursion₂` — is in
`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/LogCoshRatio.lean` and
`GibbsMeasure/Mathlib/Analysis/SpecialFunctions/LogCoshRatioFixedPoint.lean`.

## Georgii Theorem (12.31)(b), last clause: `|ex 𝒢(J,h) ∖ ex 𝒢_{I(B)}(J,h)| = ∞`

* `infinite_extremePoints_G_isingTreeSpecification` — `ex 𝒢(J, h)` is infinite. Georgii finishes
  step 4) with the *linear independence* of the family `{ν_t : t₋ < t < t₊}` and Corollary (7.29);
  the linear independence is read off a sphere. All the bonds from the sphere `∂B(r, n)` into the
  ball `B(r, n)` carry one and the same parameter `u_{n+1}(t)` of the backward orbit
  (`isingTreeParam_anchor_ballFinset`), so the probability of the cylinder "`-1` on `B(r,n)`, `+1`
  exactly on `U ⊆ ∂B(r,n)`" is `ν_t(σ ≡ -1) s_n(t)^{|U|}` with `s_n(t) = exp(2u_{n+1}(t) - 2J)`
  (`isingTreeChain_cyl_mul_pow`, `toReal_isingTreeChain_cyl`): a *geometric* function of `|U|`.
  Distinct `t` give distinct `s_n(t)` (`Real.treeBackOrbit_inj`, `isingSphereRatio_inj`) and the
  spheres are arbitrarily large (`SimpleGraph.lt_card_outerBoundary_ballFinset`, for `d ≥ 2` —
  which `d tanh J > 1` forces), so `N` of the `ν_t` are separated by a Vandermonde system
  (`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`) and admit no nontrivial linear relation;
  Corollary (7.29) over `ℝ` (`exists_ne_zero_sum_toReal_eq_zero`, the real form of (7.29) whose
  `ℝ≥0∞`-form is unusable here — over `ℝ≥0∞`, `∞ • μ = ∞ • ν` for measures with the same null
  sets) then gives `|ex 𝒢(J,h)| ≥ N` for every `N`.
* `finite_extremePoints_G_inter_invariantG` — `ex 𝒢(J,h) ∩ 𝒢_{I(B)}(J,h)` is finite (at most the
  three solutions of (12.22)). This is Comment (12.3)(5) read backwards and uses the homogeneity of
  Georgii's `𝒞𝒯(d)`, in the form `SimpleGraph.IsArcTransitive`: an `I(B)`-invariant Markov chain
  has the same transition matrix on every oriented bond, hence is completely homogeneous
  (`isCompletelyHomogeneousMarkovChain_of_forall_measurePreserving`), and an extreme Gibbs measure
  is a Markov chain by Theorem (12.6). Arc-transitivity *does* hold for every `IsCayleyTree` —
  Georgii's "`S` is *the* unique connected tree with `|∂i| = d + 1`", which he states without proof
  and which would need a back-and-forth construction of an isomorphism between two `(d+1)`-regular
  trees — but that uniqueness is not formalised here, so arc-transitivity appears as a hypothesis
  and is discharged for the model `SimpleGraph.reducedWordTree`
  (`SimpleGraph.isArcTransitive_reducedWordTree`: left multiplications in the free product
  `(ℤ/2)^{*(d+1)}` move `nil` anywhere, alphabet permutations rotate the bonds at `nil`), on which
  the clause is therefore unconditional
  (`infinite_extremePoints_G_sdiff_extremePoints_invariantG_reducedWordTree`).
* `infinite_extremePoints_G_sdiff_extremePoints_invariantG` is the two together, and
  `..._isingSpecification` / `..._reducedWordTree` are the clause for the Ising *potential* and its
  unconditional witness on `𝒞𝒯(2)`.

## Not formalised here

Of Georgii's Theorem (12.31)(b) the last clause — "if `|h| < h(J, d)` then `μ_#` is a third
*extreme* element of `𝒢_{I(B)}(J, h)`" — is **not** proved. What is proved of it:
`exists_three_mem_invariantG_isingChain`, that `μ₋`, `μ_#`, `μ₊` are three distinct *elements* of
`𝒢_{I(B)}(J, h)`, of which the outer two are extreme (in `𝒢(J,h)` and hence in `𝒢_{I(B)}(J,h)`).

What is missing is Georgii's step 5) in its entirety: a completely homogeneous Markov chain `μ` is
extreme in `𝓟_{I(B)}(Ω, 𝓕)` — hence in the smaller `𝒢_{I(B)}(J,h)` — because of a *mixing*
property along the subgroups `I(B, n) = {τ ∈ I(B) : d(τ i, i) ≥ n for all i}`,

  `lim_n sup_{τ ∈ I(B,n)} |μ(A ∩ τ⁻¹C) - μ(A) μ(C)| = 0`.

Three inputs are absent from this development, and none of them is a detail:

* Georgii's (12.4), `μ(σ_Λ = ζ) = α_k(ζ_k) ∏_{ij ⊆ Λ} P_{ij}(ζ_i, ζ_j)` for connected `Λ`, and the
  two-block estimate it yields for volumes `Λ` and `τ⁻¹Δ` at distance `≥ k`, namely
  `|μ(A ∩ τ⁻¹C) - μ(A)μ(C)| ≤ max_x ∑_y |P^k(x, y) - α(y)|`;
* the convergence `P^k → α` of Theorem (3.A3) (elementary for the positive `2 × 2` matrix `P_t`,
  but not available here);
* `I(B, n) ≠ ∅`, i.e. automorphisms of `𝒞𝒯(d)` displacing *every* vertex by at least `n`. For
  `reducedWordTree` these are the left multiplications by cyclically reduced words of length `n`
  (Georgii's "horizontal shift by `n`"), whose displacement bound `d(gw, w) ≥ |g|` needs the normal
  form and the length function of the free product; only the *generators* `ReducedWord.lstep` and
  the alphabet permutations are constructed here, which is exactly what arc-transitivity — and
  hence the clause proved above — requires.

Georgii's Corollary (7.4) itself *is* available, in the form he uses it (invariance only
`μ`-almost everywhere): `mem_extremePoints_iff_trivialOn_aeInvariant`, in the namespace
`MeasureTheory.GibbsMeasure.AbstractSpecification` of `GibbsMeasure/Specification/Abstract.lean`.
Note that the countable-group form (Theorem (14.5)(a),
`mem_extremePoints_invariantFields_iff_mem_trivialOn`) does *not* apply: `I(B)` is uncountable for
`d ≥ 2`, the only case in which (12.31)(b) has any content. (For `d = 1`, `𝒞𝒯(1) = ℤ` and `I(B)`
*is* countable — but there `h(J, 1) = 0` and `𝒢(J, h)` is a singleton.)

Georgii's remark that `I(J, d) = ]-h(J,d), h(J,d)[` in the antiferromagnetic case is explicitly
stated in the book as suggested by numerical calculations, not as a theorem; the inclusion
`]-ĥ, ĥ[ ⊆ I(J,d)` that he *does* establish is `Real.exists_isFixedPt_treeRecursion₂_ne` and
`exists_ne_isGibbsMeasure_of_abs_lt_antiferroCriticalField` below. His converse `|𝒢(J,h)| = 1` iff
(12.35) has one solution is proved only in the direction `d|tanh J| ≤ 1 ⟹` uniqueness of the
solution (`Real.existsUnique_isFixedPt_treeRecursion₂`).

## The identification with the Ising potential, and a witness

* `isingTreeSpecification_eq_isingSpecification` — **Georgii (12.7), (12.9)**: on `𝒞𝒯(d)` the
  transfer specification of (12.20) *is* the Gibbsian specification of the Ising potential
  (12.19), so `𝒢(J, h)` above really is Georgii's `𝒢(Φ^{J,h})`. Its ingredients are
  `hamiltonian_isingPotential` (`H_Λ = -J ∑_{b ∩ Λ ≠ ∅} σ_iσ_j - h ∑_{i ∈ Λ} σ_i`),
  `sum_bondsOf_spinSum` (each site of `Λ` lies on `d + 1` bonds meeting `Λ`, so it collects
  `h σ_i/(d+1)` from each) and `Specification.lambdaSpecification_eq_of_mul_boundary` (the ends of
  those bonds in `∂Λ` give a factor depending only on the configuration off `Λ`, which cancels).
* `exists_G_isingSpecification_eq_singleton`, `exists_ne_isGibbsMeasure_isingSpecification` —
  (12.31)(a), (b) restated for `𝒢(Φ^{J,h})`.
* `exists_ne_isGibbsMeasure_isingSpecification_reducedWordTree` — the non-uniqueness theorem
  witnessed: `SimpleGraph.isCayleyTree_reducedWordTree` builds `𝒞𝒯(d)` for every `d` as the tree
  of reduced words over `Fin (d+1)`, and at `d = 2`, `J = ar tanh (3/4)`, `h = 0` the Ising
  potential has two distinct Gibbs measures.

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

/-- The row `ℓ_t Q` at `+` is the row at `-` times `exp (2h/(d+1) + 2 φ_J(t))`. -/
lemma tsum_isingBoundaryVec_mul_isingTransfer_true_eq (d : ℕ) (J h t : ℝ) :
    (∑' y, isingBoundaryVec d h t y * isingTransfer d J h y true)
      = (∑' y, isingBoundaryVec d h t y * isingTransfer d J h y false)
        * ENNReal.ofReal (exp (2 * (h / (d + 1)) + 2 * logCoshRatio J t)) := by
  rw [← tsum_isingBoundaryVec_div]
  exact (ENNReal.mul_div_cancel'
    (fun hcon ↦ absurd hcon (tsum_isingBoundaryVec_mul_isingTransfer_pos false).ne')
    (fun hcon ↦ absurd hcon (tsum_isingBoundaryVec_mul_isingTransfer_ne_top false))).symm

/-- **Georgii (12.32), converse.** A family `ℓ_{ij} = ℓ_{T_{ij}}` of Ising boundary vectors on
`𝒞𝒯(d)` is a boundary law of Definition (12.10) for the transfer matrix (12.20) **iff** its
parameters satisfy Georgii's equation (12.32),
`T_{ij} = h + ∑_{k ∈ ∂i ∖ {j}} φ_J(T_{ki})`.

The forward direction is `isingParam_eq_add_sum` (every boundary law normalised at `-1` has
parameters obeying (12.32)); the converse is what step 4) of the proof of Theorem (12.31) needs, to
turn Georgii's recursively defined family `t_{ij}` into an actual boundary law. -/
theorem isBoundaryLaw_isingBoundaryVec_family_iff (hG : G.IsCayleyTree d) (T : S → S → ℝ) :
    IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) (fun i j ↦ isingBoundaryVec d h (T i j))
      ↔ ∀ ⦃i j⦄, G.Adj i j →
          T i j = h + ∑ k ∈ (G.neighborFinset i).erase j, logCoshRatio J (T k i) := by
  classical
  have hnorm : ∀ ⦃i j : S⦄, G.Adj i j → (fun i j ↦ isingBoundaryVec d h (T i j)) i j false = 1 :=
    fun _ _ _ ↦ isingBoundaryVec_false
  constructor
  · intro hℓ i j hij
    simpa only [isingParam_isingBoundaryVec] using isingParam_eq_add_sum hG hℓ hnorm hij
  · intro hT
    refine IsBoundaryLaw.of_finite G _ _ (fun _ _ _ x y ↦ isingTransfer_ne_top x y)
      (fun _ _ _ x ↦ isingBoundaryVec_pos x) (fun _ _ _ x ↦ isingBoundaryVec_ne_top x)
      fun i j hij ↦ ?_
    set V := (G.neighborFinset i).erase j with hV
    set A : S → ℝ≥0∞ := fun k ↦
      ∑' y, isingBoundaryVec d h (T k i) y * isingTransfer d J h y false with hA
    have hP0 : (∏ k ∈ V, A k) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun _ _ ↦ (tsum_isingBoundaryVec_mul_isingTransfer_pos false).ne'
    have hPt : (∏ k ∈ V, A k) ≠ ⊤ :=
      ENNReal.prod_ne_top fun _ _ ↦ tsum_isingBoundaryVec_mul_isingTransfer_ne_top false
    refine ⟨(∏ k ∈ V, A k)⁻¹, ENNReal.inv_ne_zero.2 hPt, ENNReal.inv_ne_top.2 hP0, fun x ↦ ?_⟩
    cases x
    · simpa only [isingBoundaryVec_false] using (ENNReal.inv_mul_cancel hP0 hPt).symm
    · have hstep : ∀ k ∈ V, (∑' y, isingBoundaryVec d h (T k i) y * isingTransfer d J h y true)
          = A k * ENNReal.ofReal (exp (2 * (h / (d + 1)) + 2 * logCoshRatio J (T k i))) :=
        fun k _ ↦ tsum_isingBoundaryVec_mul_isingTransfer_true_eq d J h (T k i)
      rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib,
        ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ exp_nonneg _), ← exp_sum, ← mul_assoc,
        ENNReal.inv_mul_cancel hP0 hPt, one_mul, isingBoundaryVec_true]
      congr 1
      rw [exp_eq_exp, Finset.sum_add_distrib, Finset.sum_const,
        hG.card_neighborFinset_erase hij, ← Finset.mul_sum, nsmul_eq_mul]
      have hc := field_split d h
      have hTij := hT hij
      rw [← hV] at hTij
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


/-! ## Georgii Theorem (12.31)(b), step 3): `μ₋` and `μ₊` are extreme in `𝒢(J, h)`

Georgii compares an arbitrary `μ ∈ 𝒢(J, h)` with the completely homogeneous chains through the
ratios `r_{Λ,ζ}(μ) = μ(σ_{Λ ∪ ∂Λ} = ζ)/μ(σ_{Λ ∪ ∂Λ} ≡ -1)`. By step 1 the parameters (12.32) of the
normalised boundary law of an extreme Gibbs measure lie between the extremal solutions `t₋ ≤ t₊`
of (12.22) (`Real.exists_isLeast_treeField_eq`, `Real.exists_isGreatest_treeField_eq`), so its
boundary law is squeezed between `ℓ_{t₋}` and `ℓ_{t₊}` pointwise — `ℓ(-1) = 1` for all of them and
`ℓ(+1) = exp(2t - 2h/(d+1))` is increasing in `t`. The general extremality criteria of
`TreeBoundaryLawChains.lean` (`mem_extremePoints_G_boundaryLawMeasure_of_forall_le` and its
mirror image) then make `μ_{t₊}` and `μ_{t₋}` extreme. -/

section Extremality

variable [Countable S]

/-- Georgii, steps 2)–3): an extreme Gibbs measure of `γ^{J,h}` on `𝒞𝒯(d)` is the measure (12.13)
of a boundary law normalised at `-1` — Theorem (12.6) makes it a Markov chain, Theorem (12.12)(b)
produces the boundary law, and `normalizeBoundaryLaw` normalises it without changing the
measure. -/
theorem exists_isBoundaryLaw_normalized_eq_of_mem_extremePoints (hG : G.IsCayleyTree d)
    {μ : Measure (S → Bool)}
    (hμext : μ ∈ (_root_.MeasureTheory.GibbsMeasure.G
      (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞) :
    ∃ (ℓ : S → S → Bool → ℝ≥0∞) (hℓ : IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h) ℓ),
      (∀ ⦃i j⦄, G.Adj i j → ℓ i j false = 1) ∧
        μ = boundaryLawMeasure (isTransferFamily_isingTransfer G d J h) hℓ hG.isTree := by
  have hQ := isTransferFamily_isingTransfer G d J h
  have hμP : IsProbabilityMeasure μ := hμext.1.1
  have hμG : (transferSpecification G hQ).IsGibbsMeasure μ := hμext.1.2
  have hchain : IsMarkovChain G μ :=
    exists_isMarkovChain_of_mem_extremePoints hG.isTree
      (isMarkovSpecification_transferSpecification hQ) hμext
  have hbl := hchain.isBoundaryLaw_chainBoundaryLaw hQ hμG hG.isTree false
  have hnorm := hbl.isBoundaryLaw_normalizeAt false
  refine ⟨_, hnorm, fun i j hij ↦ normalizeBoundaryLaw_apply_self hbl hij false, ?_⟩
  rw [hbl.boundaryLawMeasure_normalizeAt_eq hQ hG.isTree false hnorm]
  exact hchain.eq_boundaryLawMeasure hQ hμG hG.isTree false

/-- **Georgii Theorem (12.31)(b): `μ₊ ∈ ex 𝒢(J, h)`.** The completely homogeneous Markov chain
attached to the *largest* solution of (12.22) is an extreme Gibbs measure. -/
theorem mem_extremePoints_G_isingChain_of_isGreatest (hJ : 0 < J) (hG : G.IsCayleyTree d)
    {t : ℝ} (hsol : t = h + d * logCoshRatio J t)
    (hmax : ∀ s : ℝ, Real.treeField d J s = h → s ≤ t) :
    isingChain hG hsol ∈ (_root_.MeasureTheory.GibbsMeasure.G
      (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ := by
  refine mem_extremePoints_G_boundaryLawMeasure_of_forall_le
    (isTransferFamily_isingTransfer G d J h) hG.isTree
    ((isBoundaryLaw_isingBoundaryVec_iff hG).2 hsol) (fun _ _ _ ↦ isingBoundaryVec_false)
    fun μ hμext ↦ ?_
  obtain ⟨ℓ, hℓ, ha, rfl⟩ := exists_isBoundaryLaw_normalized_eq_of_mem_extremePoints hG hμext
  obtain ⟨p, hp, hple⟩ := exists_treeField_eq_and_forall_isingParam_le hJ hG hℓ ha
  refine ⟨ℓ, hℓ, ha, fun i j hij x ↦ ?_, rfl⟩
  cases x
  · rw [ha hij, isingBoundaryVec_false]
  · rw [apply_true_eq_of_normalized d h (ha hij) (hℓ.pos hij true) (hℓ.ne_top hij true),
      isingBoundaryVec_true]
    exact ENNReal.ofReal_le_ofReal (exp_le_exp.2 (by linarith [hmax p hp, hple hij]))

/-- **Georgii Theorem (12.31)(b): `μ₋ ∈ ex 𝒢(J, h)`.** The completely homogeneous Markov chain
attached to the *smallest* solution of (12.22) is an extreme Gibbs measure. -/
theorem mem_extremePoints_G_isingChain_of_isLeast (hJ : 0 < J) (hG : G.IsCayleyTree d)
    {t : ℝ} (hsol : t = h + d * logCoshRatio J t)
    (hmin : ∀ s : ℝ, Real.treeField d J s = h → t ≤ s) :
    isingChain hG hsol ∈ (_root_.MeasureTheory.GibbsMeasure.G
      (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ := by
  refine mem_extremePoints_G_boundaryLawMeasure_of_forall_ge
    (isTransferFamily_isingTransfer G d J h) hG.isTree
    ((isBoundaryLaw_isingBoundaryVec_iff hG).2 hsol) (fun _ _ _ ↦ isingBoundaryVec_false)
    fun μ hμext ↦ ?_
  obtain ⟨ℓ, hℓ, ha, rfl⟩ := exists_isBoundaryLaw_normalized_eq_of_mem_extremePoints hG hμext
  obtain ⟨q, hq, hqle⟩ := exists_treeField_eq_and_forall_le_isingParam hJ hG hℓ ha
  refine ⟨ℓ, hℓ, ha, fun i j hij x ↦ ?_, rfl⟩
  cases x
  · rw [ha hij, isingBoundaryVec_false]
  · rw [apply_true_eq_of_normalized d h (ha hij) (hℓ.pos hij true) (hℓ.ne_top hij true),
      isingBoundaryVec_true]
    exact ENNReal.ofReal_le_ofReal (exp_le_exp.2 (by linarith [hmin q hq, hqle hij]))

/-- **Georgii Theorem (12.31)(b), first clause.** For `J > J(d)` (i.e. `d tanh J > 1`) and
`|h| ≤ h(J, d)` the two completely homogeneous Markov chains `μ₋ ≠ μ₊` attached to the smallest and
the largest solution of (12.22) are *distinct extreme* elements of `𝒢(J, h)`. -/
theorem exists_ne_mem_extremePoints_G_isingChain (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ∃ (t₁ t₂ : ℝ) (hs₁ : t₁ = h + d * logCoshRatio J t₁)
      (hs₂ : t₂ = h + d * logCoshRatio J t₂),
      isingChain hG hs₁ ≠ isingChain hG hs₂ ∧
        isingChain hG hs₁ ∈ (_root_.MeasureTheory.GibbsMeasure.G
          (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ ∧
        isingChain hG hs₂ ∈ (_root_.MeasureTheory.GibbsMeasure.G
          (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ := by
  obtain ⟨tmin, hmin, hminle⟩ := Real.exists_isLeast_treeField_eq hJ d h
  obtain ⟨tmax, hmax, hmaxle⟩ := Real.exists_isGreatest_treeField_eq hJ d h
  obtain ⟨a, b, hab, hae, hbe⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hsmin : tmin = h + d * logCoshRatio J tmin := by rw [Real.treeField] at hmin; linarith
  have hsmax : tmax = h + d * logCoshRatio J tmax := by rw [Real.treeField] at hmax; linarith
  have hlt : tmin < tmax := lt_of_le_of_lt (hminle a hae) (lt_of_lt_of_le hab (hmaxle b hbe))
  exact ⟨tmin, tmax, hsmin, hsmax, fun heq ↦ hlt.ne (isingChain_inj hG hsmin hsmax heq),
    mem_extremePoints_G_isingChain_of_isLeast hJ hG hsmin hminle,
    mem_extremePoints_G_isingChain_of_isGreatest hJ hG hsmax hmaxle⟩

/-! ### Georgii Theorem (12.31)(b): extremality in `𝒢_{I(B)}(J, h)`

Georgii's `𝒢_{I(B)}(J, h) = 𝒢(J, h) ∩ 𝓟_{I(B)}` is `invariantG` (Georgii (14.14)) at the group
`I(B) = graphAutomorphisms` of graph automorphisms. A completely homogeneous Markov chain belongs
to it by Comment (12.3)(5) (`measurePreserving_of_mem_graphAutomorphisms`), and an extreme point of
a set is extreme in every subset containing it, so `μ₋, μ₊ ∈ ex 𝒢(J,h) ∩ ex 𝒢_{I(B)}(J,h)` — the
first clause of Georgii's (12.31)(b). -/

omit [Countable S] in
/-- **Georgii Comment (12.3)(5) for `μ_t`.** The completely homogeneous Markov chain `μ_t` is
invariant under every element of Georgii's group `I(B)` of graph automorphisms. -/
theorem measurePreserving_isingChain_of_mem_graphAutomorphisms (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) {τ : Transformation S Bool}
    (hτ : τ ∈ graphAutomorphisms Bool G) :
    MeasurePreserving τ.toFun (isingChain hG hsol) (isingChain hG hsol) := by
  obtain ⟨i₀, j₀, hij₀⟩ := hG.exists_adj
  have : Nontrivial S := ⟨i₀, j₀, hij₀.ne⟩
  exact measurePreserving_of_mem_graphAutomorphisms hG.isTree
    (isCompletelyHomogeneousMarkovChain_isingChain hG hsol).isMarkovChain
    (isingTransition_pos J t) (tsum_isingTransition J t)
    (fun _ _ hij x y _ ↦ transitionProb_isingChain hG hsol hij x y) hτ

omit [Countable S] in
/-- **Georgii §12.2.** `μ_t ∈ 𝒢_{I(B)}(J, h)`. -/
theorem mem_invariantG_isingChain (hG : G.IsCayleyTree d)
    (hsol : t = h + d * logCoshRatio J t) :
    isingChain hG hsol
      ∈ invariantG (isingTreeSpecification G d J h) (graphAutomorphisms Bool G) :=
  ⟨⟨inferInstance, isGibbsMeasure_isingChain hG hsol⟩,
    mem_invariantFields_iff.2 ⟨inferInstance,
      fun _ hτ ↦ measurePreserving_isingChain_of_mem_graphAutomorphisms hG hsol hτ⟩⟩

/-- **Georgii Theorem (12.31)(b): `μ₊ ∈ ex 𝒢_{I(B)}(J, h)`.** An extreme point of `𝒢(J, h)` which
is `I(B)`-invariant is extreme in the smaller set `𝒢_{I(B)}(J, h)`. -/
theorem mem_extremePoints_invariantG_isingChain_of_isGreatest (hJ : 0 < J)
    (hG : G.IsCayleyTree d) {t : ℝ} (hsol : t = h + d * logCoshRatio J t)
    (hmax : ∀ s : ℝ, Real.treeField d J s = h → s ≤ t) :
    isingChain hG hsol ∈ (invariantG (isingTreeSpecification G d J h)
      (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ :=
  inter_extremePoints_subset_extremePoints_of_subset Set.inter_subset_left
    ⟨mem_invariantG_isingChain hG hsol,
      mem_extremePoints_G_isingChain_of_isGreatest hJ hG hsol hmax⟩

/-- **Georgii Theorem (12.31)(b): `μ₋ ∈ ex 𝒢_{I(B)}(J, h)`.** -/
theorem mem_extremePoints_invariantG_isingChain_of_isLeast (hJ : 0 < J)
    (hG : G.IsCayleyTree d) {t : ℝ} (hsol : t = h + d * logCoshRatio J t)
    (hmin : ∀ s : ℝ, Real.treeField d J s = h → t ≤ s) :
    isingChain hG hsol ∈ (invariantG (isingTreeSpecification G d J h)
      (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ :=
  inter_extremePoints_subset_extremePoints_of_subset Set.inter_subset_left
    ⟨mem_invariantG_isingChain hG hsol, mem_extremePoints_G_isingChain_of_isLeast hJ hG hsol hmin⟩

/-- **Georgii Theorem (12.31)(b), first clause in full.** For `J > J(d)` and `|h| ≤ h(J, d)`,
`μ₋ ≠ μ₊` and both lie in `ex 𝒢(J, h) ∩ ex 𝒢_{I(B)}(J, h)`. -/
theorem exists_ne_mem_extremePoints_G_inter_invariantG_isingChain (hJ : 0 < J)
    (hG : G.IsCayleyTree d) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    ∃ (t₁ t₂ : ℝ) (hs₁ : t₁ = h + d * logCoshRatio J t₁)
      (hs₂ : t₂ = h + d * logCoshRatio J t₂),
      isingChain hG hs₁ ≠ isingChain hG hs₂ ∧
        isingChain hG hs₁ ∈ (_root_.MeasureTheory.GibbsMeasure.G
            (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ ∩
          (invariantG (isingTreeSpecification G d J h)
            (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ ∧
        isingChain hG hs₂ ∈ (_root_.MeasureTheory.GibbsMeasure.G
            (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ ∩
          (invariantG (isingTreeSpecification G d J h)
            (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ := by
  obtain ⟨tmin, hmin, hminle⟩ := Real.exists_isLeast_treeField_eq hJ d h
  obtain ⟨tmax, hmax, hmaxle⟩ := Real.exists_isGreatest_treeField_eq hJ d h
  obtain ⟨a, b, hab, hae, hbe⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hsmin : tmin = h + d * logCoshRatio J tmin := by rw [Real.treeField] at hmin; linarith
  have hsmax : tmax = h + d * logCoshRatio J tmax := by rw [Real.treeField] at hmax; linarith
  have hlt : tmin < tmax := lt_of_le_of_lt (hminle a hae) (lt_of_lt_of_le hab (hmaxle b hbe))
  exact ⟨tmin, tmax, hsmin, hsmax, fun heq ↦ hlt.ne (isingChain_inj hG hsmin hsmax heq),
    ⟨mem_extremePoints_G_isingChain_of_isLeast hJ hG hsmin hminle,
      mem_extremePoints_invariantG_isingChain_of_isLeast hJ hG hsmin hminle⟩,
    ⟨mem_extremePoints_G_isingChain_of_isGreatest hJ hG hsmax hmaxle,
      mem_extremePoints_invariantG_isingChain_of_isGreatest hJ hG hsmax hmaxle⟩⟩

omit [Countable S] in
/-- **Georgii Theorem (12.31)(b), third clause, without step 5).** For `|h| < h(J, d)` the three
completely homogeneous Markov chains `μ₋`, `μ_#`, `μ₊` attached to the three solutions of (12.22)
are three *distinct elements* of `𝒢_{I(B)}(J, h)` (Comment (12.3)(5)). That the intermediate one is
moreover *extreme* in `𝒢_{I(B)}(J, h)` is Georgii's step 5), which rests on a mixing property of
completely homogeneous chains along `I(B, n)` and is not proved here; the outer two are extreme
already in `𝒢(J, h)` (`mem_extremePoints_G_isingChain_of_isLeast` / `..._of_isGreatest`). -/
theorem exists_three_mem_invariantG_isingChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d)
    (hh : |h| < Real.treeCriticalField d J) :
    ∃ (t₁ t₂ t₃ : ℝ) (hs₁ : t₁ = h + d * logCoshRatio J t₁)
      (hs₂ : t₂ = h + d * logCoshRatio J t₂) (hs₃ : t₃ = h + d * logCoshRatio J t₃),
      isingChain hG hs₁ ≠ isingChain hG hs₂ ∧ isingChain hG hs₂ ≠ isingChain hG hs₃ ∧
        isingChain hG hs₁ ≠ isingChain hG hs₃ ∧
        isingChain hG hs₁ ∈ invariantG (isingTreeSpecification G d J h)
          (graphAutomorphisms Bool G) ∧
        isingChain hG hs₂ ∈ invariantG (isingTreeSpecification G d J h)
          (graphAutomorphisms Bool G) ∧
        isingChain hG hs₃ ∈ invariantG (isingTreeSpecification G d J h)
          (graphAutomorphisms Bool G) := by
  obtain ⟨t₁, t₂, t₃, hs₁, hs₂, hs₃, h₁₂, h₂₃, h₁₃⟩ := exists_three_isingChain hJ hd hG hh
  exact ⟨t₁, t₂, t₃, hs₁, hs₂, hs₃, h₁₂, h₂₃, h₁₃, mem_invariantG_isingChain hG hs₁,
    mem_invariantG_isingChain hG hs₂, mem_invariantG_isingChain hG hs₃⟩

end Extremality


/-! ## Georgii, step 4) of the proof of Theorem (12.31): inhomogeneous phases

Georgii builds, for each `t` strictly between the extremal solutions `t₋ < t₊` of (12.22), a
boundary law that is *not* constant, and hence a Markov chain in `𝒢(J, h)` that is not completely
homogeneous. Fix a root `r`. On the bonds `ij` pointing *towards* `r` (i.e. `j` is closer to `r`)
put `t_{ij} = u_{d(r,i)}`, where `(u_n)` is the backward orbit of `t` under `ψ = h + d φ_J`
(`Real.treeBackOrbit`, which exists because `ψ` maps `]t₋, t₊[` bijectively onto itself); on the
bonds pointing *away* from `r` put `t_{ij} = v_{d(r,i)}`, where `v` is determined by (12.32)
(`Real.treeAwayOrbit`). The consistency equation (12.32) at a bond `ij` then splits into three
cases according to whether `j` is the parent of `i`, `i` is the root, or `i` has a parent — see
`isBoundaryLaw_isingTreeParam`. -/

section Inhomogeneous

open scoped Classical in
/-- **Georgii, step 4) of the proof of Theorem (12.31).** The inhomogeneous parameter family
attached to a root `r` and the orbits of `t`: `u_{d(r,i)}` on the bonds pointing towards `r`,
`v_{d(r,i)}` on the bonds pointing away from it. -/
noncomputable def isingTreeParam (G : SimpleGraph S) (d : ℕ) (J h t : ℝ) (r : S) : S → S → ℝ :=
  fun i j ↦ if r ∈ G.past i j then Real.treeAwayOrbit d J h t (G.dist r i)
    else Real.treeBackOrbit d J h t (G.dist r i)

omit [DecidableEq S] [G.LocallyFinite] in
lemma isingTreeParam_of_mem_past {r i j : S} (h' : r ∈ G.past i j) :
    isingTreeParam G d J h t r i j = Real.treeAwayOrbit d J h t (G.dist r i) := by
  simp [isingTreeParam, h']

omit [DecidableEq S] [G.LocallyFinite] in
lemma isingTreeParam_of_notMem_past {r i j : S} (h' : r ∉ G.past i j) :
    isingTreeParam G d J h t r i j = Real.treeBackOrbit d J h t (G.dist r i) := by
  simp [isingTreeParam, h']

/-- **Georgii, step 4) of the proof of Theorem (12.31).** The family `isingTreeParam` satisfies
Georgii's consistency equation (12.32), so `ℓ_{ij} = ℓ_{t_{ij}}` is a boundary law. -/
theorem isBoundaryLaw_isingTreeParam (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) :
    IsBoundaryLaw G (fun _ _ ↦ isingTransfer d J h)
      (fun i j ↦ isingBoundaryVec d h (isingTreeParam G d J h t r i j)) := by
  classical
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [isBoundaryLaw_isingBoundaryVec_family_iff hG]
  intro i j hij
  by_cases hrj : r ∈ G.past i j
  · -- `j` is farther from the root than `i`: the bond points away from `r`
    rw [isingTreeParam_of_mem_past hrj]
    by_cases hri : r = i
    · -- `i` is the root
      subst hri
      have hsum : ∀ k ∈ (G.neighborFinset r).erase j,
          logCoshRatio J (isingTreeParam G d J h t r k r) = logCoshRatio J t := by
        intro k hk
        have hrk : G.Adj r k := (G.mem_neighborFinset r k).1 (Finset.mem_of_mem_erase hk)
        rw [isingTreeParam_of_notMem_past SimpleGraph.notMem_past_self_root,
          G.dist_eq_one_iff_adj.2 hrk, Real.treeBackOrbit_one hJ hd]
      rw [Finset.sum_congr rfl hsum, Finset.sum_const, hG.card_neighborFinset_erase hij,
        nsmul_eq_mul, SimpleGraph.dist_self, Real.treeAwayOrbit_zero, Real.treeRecursion]
    · -- `i` has a parent `p`, which is not `j`
      obtain ⟨p, hip, hrp⟩ := hG.isTree.exists_adj_mem_past (fun hcon ↦ hri hcon)
      have hpj : p ≠ j := fun hcon ↦
        SimpleGraph.notMem_past_of_mem_past_swap (hcon ▸ hrp) hrj
      have hpV : p ∈ (G.neighborFinset i).erase j :=
        Finset.mem_erase.2 ⟨hpj, (G.mem_neighborFinset i p).2 hip⟩
      have hdist : G.dist r i = G.dist r p + 1 := SimpleGraph.mem_past.1 hrp
      have hsum : ∀ k ∈ ((G.neighborFinset i).erase j).erase p,
          logCoshRatio J (isingTreeParam G d J h t r k i)
            = logCoshRatio J (Real.treeBackOrbit d J h t (G.dist r p + 2)) := by
        intro k hk
        have hkp : p ≠ k := (Finset.mem_erase.1 hk).1.symm
        have hik : G.Adj i k :=
          (G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk))
        have hrk : r ∈ G.past i k := hG.isTree.mem_past_of_ne hip hik hrp hkp
        rw [isingTreeParam_of_notMem_past (SimpleGraph.notMem_past_of_mem_past_swap hrk),
          SimpleGraph.mem_past.1 hrk, hdist]
      rw [← Finset.add_sum_erase _ _ hpV, Finset.sum_congr rfl hsum, Finset.sum_const,
        Finset.card_erase_of_mem hpV, hG.card_neighborFinset_erase hij, nsmul_eq_mul,
        isingTreeParam_of_mem_past hrp, hdist, Real.treeAwayOrbit_succ]
      rw [Nat.cast_sub hd, Nat.cast_one]
      ring
  · -- `j` is the parent of `i`: the bond points towards `r`
    have hrj' : r ∈ G.past j i := (hG.isTree.mem_past_or_mem_past_swap hij r).resolve_left hrj
    rw [isingTreeParam_of_notMem_past hrj]
    have hsum : ∀ k ∈ (G.neighborFinset i).erase j,
        logCoshRatio J (isingTreeParam G d J h t r k i)
          = logCoshRatio J (Real.treeBackOrbit d J h t (G.dist r i + 1)) := by
      intro k hk
      have hjk : j ≠ k := (Finset.mem_erase.1 hk).1.symm
      have hik : G.Adj i k := (G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)
      have hrk : r ∈ G.past i k := hG.isTree.mem_past_of_ne hij hik hrj' hjk
      rw [isingTreeParam_of_notMem_past (SimpleGraph.notMem_past_of_mem_past_swap hrk),
        SimpleGraph.mem_past.1 hrk]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, hG.card_neighborFinset_erase hij,
      nsmul_eq_mul, ← Real.treeRecursion,
      Real.treeRecursion_treeBackOrbit_succ hJ hd ha hb hab ht]

/-- **Georgii, step 4) of the proof of Theorem (12.31).** The inhomogeneous Markov chain `ν_t`:
the measure (12.13) of the boundary law `isingTreeParam`. -/
noncomputable def isingTreeChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) : Measure (S → Bool) :=
  boundaryLawMeasure (isTransferFamily_isingTransfer G d J h)
    (isBoundaryLaw_isingTreeParam hJ hd hG r ha hb hab ht) hG.isTree

instance isProbabilityMeasure_isingTreeChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d)
    (r : S) {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) :
    IsProbabilityMeasure (isingTreeChain hJ hd hG r ha hb hab ht) :=
  isProbabilityMeasure_boundaryLawMeasure _ _ _

/-- **Georgii, step 4).** `ν_t ∈ 𝒢(J, h)`. -/
theorem isGibbsMeasure_isingTreeChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) :
    (isingTreeSpecification G d J h).IsGibbsMeasure (isingTreeChain hJ hd hG r ha hb hab ht) :=
  IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _ _

/-- **Georgii, step 4): the family `{ν_t}` is injectively parametrised.** Distinct parameters give
distinct Markov chains: by the uniqueness up to a constant of the boundary law (Theorem
(12.12)(b)), equality of the measures forces equality of the normalised boundary laws, hence of
`t_{jr} = u_1 = t` at any bond `jr` at the root. -/
theorem isingTreeChain_inj (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) {t s : ℝ} (ht : t ∈ Set.Ioo a b) (hs : s ∈ Set.Ioo a b)
    (heq : isingTreeChain hJ hd hG r ha hb hab ht = isingTreeChain hJ hd hG r ha hb hab hs) :
    t = s := by
  obtain ⟨j, hrj⟩ := hG.exists_adj_right r
  obtain ⟨c, -, -, hc⟩ := IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq
    (isTransferFamily_isingTransfer G d J h) hG.isTree
    (isBoundaryLaw_isingTreeParam hJ hd hG r ha hb hab ht)
    (isBoundaryLaw_isingTreeParam hJ hd hG r ha hb hab hs) heq hrj
  have hparam : ∀ {p : ℝ} (hp : p ∈ Set.Ioo a b),
      isingTreeParam G d J h p r j r = p := by
    intro p hp
    rw [isingTreeParam_of_notMem_past SimpleGraph.notMem_past_self_root,
      G.dist_eq_one_iff_adj.2 hrj, Real.treeBackOrbit_one hJ hd]
  have hc1 : c = 1 := by
    have h1 := hc false
    simp only [isingBoundaryVec_false, mul_one] at h1
    exact h1.symm
  have h2 := hc true
  rw [hc1, one_mul, hparam ht, hparam hs, isingBoundaryVec_true, isingBoundaryVec_true,
    ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp] at h2
  linarith

/-- **Georgii, step 4).** `ν_t` is a Markov chain on `𝒞𝒯(d)`. -/
theorem isMarkovChain_isingTreeChain (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) :
    IsMarkovChain G (isingTreeChain hJ hd hG r ha hb hab ht) :=
  IsBoundaryLaw.isMarkovChain_boundaryLawMeasure _ _ _

/-- **Georgii, step 4): `ν_t` "fails to be completely homogeneous".** If `t` is not itself a
solution of (12.22) — Georgii's choice of a `t ∈ ]t₋, t₊[` different from `t_#` — then `ν_t` is
*not* a completely homogeneous Markov chain: its parameters at the two orientations of a bond at
the root are `t` and `ψ(t) = h + d φ_J(t)`, which differ. -/
theorem not_isCompletelyHomogeneousMarkovChain_isingTreeChain (hJ : 0 < J) (hd : 1 ≤ d)
    (hG : G.IsCayleyTree d) (r : S) {a b : ℝ} (ha : Real.treeRecursion d J h a = a)
    (hb : Real.treeRecursion d J h b = b) (hab : a < b) (ht : t ∈ Set.Ioo a b)
    (hfix : Real.treeRecursion d J h t ≠ t) :
    ¬ IsCompletelyHomogeneousMarkovChain G (isingTreeChain hJ hd hG r ha hb hab ht) := by
  intro hcc
  obtain ⟨j, hrj⟩ := hG.exists_adj_right r
  have hQ := isTransferFamily_isingTransfer G d J h
  have hℓ := isBoundaryLaw_isingTreeParam hJ hd hG r ha hb hab ht
  obtain ⟨ℓ0, hℓ0, ha0, hμeq⟩ := hcc.exists_isBoundaryLaw_const_boundaryLawMeasure_eq
    (Q₀ := isingTransfer d J h) hQ hG.isTree
    (isGibbsMeasure_isingTreeChain hJ hd hG r ha hb hab ht) false ⟨r, j, hrj⟩
  obtain ⟨c, -, -, hc⟩ := IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq hQ hG.isTree
    hℓ hℓ0 hμeq hrj
  obtain ⟨c', -, -, hc'⟩ := IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq hQ hG.isTree
    hℓ hℓ0 hμeq hrj.symm
  have hc1 : c = 1 := by
    have h1 := hc false
    rw [isingBoundaryVec_false, ha0, mul_one] at h1
    exact h1.symm
  have hc'1 : c' = 1 := by
    have h1 := hc' false
    rw [isingBoundaryVec_false, ha0, mul_one] at h1
    exact h1.symm
  have hjr : isingTreeParam G d J h t r j r = t := by
    rw [isingTreeParam_of_notMem_past SimpleGraph.notMem_past_self_root,
      G.dist_eq_one_iff_adj.2 hrj, Real.treeBackOrbit_one hJ hd]
  have hrjp : isingTreeParam G d J h t r r j = Real.treeRecursion d J h t := by
    rw [isingTreeParam_of_mem_past (SimpleGraph.mem_past_self_of_adj hrj),
      SimpleGraph.dist_self, Real.treeAwayOrbit_zero]
  have h2 := hc true
  have h3 := hc' true
  rw [hc1, one_mul, hjr] at h2
  rw [hc'1, one_mul, hrjp] at h3
  have h4 : isingBoundaryVec d h t true
      = isingBoundaryVec d h (Real.treeRecursion d J h t) true := h2.trans h3.symm
  rw [isingBoundaryVec_true, isingBoundaryVec_true,
    ENNReal.ofReal_eq_ofReal_iff (exp_nonneg _) (exp_nonneg _), exp_eq_exp] at h4
  exact hfix (by linarith)

/-- **Georgii Theorem (12.31)(b), step 4).** For `J > J(d)` (i.e. `d tanh J > 1`) and
`|h| ≤ h(J, d)`, `𝒢(J, h)` contains an injectively parametrised family of Markov chains indexed by
the open interval `]t₋, t₊[` between the extremal solutions of (12.22); in particular `𝒢(J, h)` is
infinite. -/
theorem infinite_G_isingTreeSpecification [Countable S] (hJ : 0 < J) (hd : 1 ≤ d)
    (hG : G.IsCayleyTree d) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    (_root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)).Infinite := by
  obtain ⟨tmin, hmin, hminle⟩ := Real.exists_isLeast_treeField_eq hJ d h
  obtain ⟨tmax, hmax, hmaxle⟩ := Real.exists_isGreatest_treeField_eq hJ d h
  obtain ⟨c, e, hce, hcf, hef⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hlt : tmin < tmax := lt_of_le_of_lt (hminle c hcf) (lt_of_lt_of_le hce (hmaxle e hef))
  have ha : Real.treeRecursion d J h tmin = tmin := Real.treeRecursion_eq_self_iff.2 hmin
  have hb : Real.treeRecursion d J h tmax = tmax := Real.treeRecursion_eq_self_iff.2 hmax
  obtain ⟨r⟩ := hG.nonempty
  have : Infinite (Set.Ioo tmin tmax) := Set.Ioo.infinite hlt
  refine Set.infinite_of_injective_forall_mem
    (f := fun p : Set.Ioo tmin tmax ↦ isingTreeChain hJ hd hG r ha hb hlt p.2) ?_ ?_
  · intro p q hpq
    exact Subtype.ext (isingTreeChain_inj hJ hd hG r ha hb hlt p.2 q.2 hpq)
  · exact fun p ↦ ⟨inferInstance, isGibbsMeasure_isingTreeChain hJ hd hG r ha hb hlt p.2⟩

/-- The solutions of (12.22) are finitely many in the critical window: three when
`|h| < h(J, d)`, two when `|h| = h(J, d) > 0`, and one when `h(J, d) = 0`. -/
theorem finite_setOf_isFixedPt_treeRecursion (hJ : 0 < J) (hd : 1 ≤ d)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    {t : ℝ | Real.treeRecursion d J h t = t}.Finite := by
  have hcongr : {t : ℝ | Real.treeRecursion d J h t = t} = {t : ℝ | Real.treeField d J t = h} := by
    ext t; exact Real.treeRecursion_eq_self_iff
  rw [hcongr]
  rcases lt_or_eq_of_le hh with hlt | heq
  · obtain ⟨a, b, c, -, -, hset⟩ := Real.exists_eq_insert_treeField_eq_of_abs_lt hJ hd hlt
    rw [hset]
    exact ((Set.finite_singleton c).insert b).insert a
  · rcases eq_or_lt_of_le (Real.treeCriticalField_nonneg hJ hd) with hzero | hpos
    · obtain ⟨t₀, ht₀, huniq⟩ := Real.existsUnique_treeField_eq hJ (by
        rw [← Real.treeCriticalField_eq_zero_iff hJ hd]; exact hzero.symm) h
      refine Set.Finite.subset (Set.finite_singleton t₀) fun s hs ↦ ?_
      exact Set.mem_singleton_iff.2 (huniq s hs)
    · obtain ⟨a, b, -, hset⟩ := Real.exists_eq_pair_treeField_eq_of_abs_eq hJ hd hpos heq
      rw [hset]
      exact (Set.finite_singleton b).insert a

/-- **Georgii Theorem (12.31)(b), step 4), in Georgii's own words.** For `J > J(d)` and
`|h| ≤ h(J, d)`, "besides `μ₋`, `μ_#` and `μ₊` there is an infinite number of inhomogeneous
phases": the Gibbs measures of `Φ^{J,h}` that are Markov chains but are *not* completely
homogeneous form an infinite set. -/
theorem infinite_setOf_mem_G_not_isCompletelyHomogeneous [Countable S] (hJ : 0 < J) (hd : 1 ≤ d)
    (hG : G.IsCayleyTree d) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    {μ : Measure (S → Bool) |
      μ ∈ _root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h) ∧
        IsMarkovChain G μ ∧ ¬ IsCompletelyHomogeneousMarkovChain G μ}.Infinite := by
  obtain ⟨tmin, hmin, hminle⟩ := Real.exists_isLeast_treeField_eq hJ d h
  obtain ⟨tmax, hmax, hmaxle⟩ := Real.exists_isGreatest_treeField_eq hJ d h
  obtain ⟨c, e, hce, hcf, hef⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hlt : tmin < tmax := lt_of_le_of_lt (hminle c hcf) (lt_of_lt_of_le hce (hmaxle e hef))
  have ha : Real.treeRecursion d J h tmin = tmin := Real.treeRecursion_eq_self_iff.2 hmin
  have hb : Real.treeRecursion d J h tmax = tmax := Real.treeRecursion_eq_self_iff.2 hmax
  obtain ⟨r⟩ := hG.nonempty
  have hIoo : (Set.Ioo tmin tmax).Infinite := Set.infinite_coe_iff.1 (Set.Ioo.infinite hlt)
  have hdiff : (Set.Ioo tmin tmax \ {t : ℝ | Real.treeRecursion d J h t = t}).Infinite :=
    hIoo.sdiff (finite_setOf_isFixedPt_treeRecursion hJ hd hh)
  have : Infinite (Set.Ioo tmin tmax \ {t : ℝ | Real.treeRecursion d J h t = t} : Set ℝ) :=
    hdiff.to_subtype
  refine Set.infinite_of_injective_forall_mem
    (f := fun p : (Set.Ioo tmin tmax \ {t : ℝ | Real.treeRecursion d J h t = t} : Set ℝ) ↦
      isingTreeChain hJ hd hG r ha hb hlt p.2.1) ?_ ?_
  · intro p q hpq
    exact Subtype.ext (isingTreeChain_inj hJ hd hG r ha hb hlt p.2.1 q.2.1 hpq)
  · exact fun p ↦ ⟨⟨inferInstance, isGibbsMeasure_isingTreeChain hJ hd hG r ha hb hlt p.2.1⟩,
      isMarkovChain_isingTreeChain hJ hd hG r ha hb hlt p.2.1,
      not_isCompletelyHomogeneousMarkovChain_isingTreeChain hJ hd hG r ha hb hlt p.2.1 p.2.2⟩

end Inhomogeneous



/-! ## Georgii Theorem (12.31)(b), last clause: `|ex 𝒢(J,h) ∖ ex 𝒢_{I(B)}(J,h)| = ∞`

Georgii finishes step 4) with: "the family `{ν_t : t₋ < t < t₊}` is linearly independent. This can
be seen by a straightforward modification of the proof of Corollary (12.18). The result thus
follows from Theorem (7.26)."

The linear independence is read off a *sphere*. Take the ball `Λ = B(r, n)` around the root `r` of
`ν_t`; its outer boundary is the sphere of radius `n + 1`, all of whose bonds into the ball carry
one and the same parameter `u_{n+1}(t)` of the backward orbit. By
`IsBoundaryLaw.boundaryLawMeasure_cyl_ite_mul_pow` the probability of the cylinder "`-1` on the
ball, `+1` exactly on `U ⊆ ∂Λ`" is therefore `ν_t(σ ≡ -1 on B(r,n+1)) · s_n(t)^{|U|}` with
`s_n(t) = exp(2u_{n+1}(t) - 2J) > 0`, a *geometric* function of `|U|`. Distinct `t` give distinct
`s_n(t)` (`Real.treeBackOrbit_inj`), and the sphere is arbitrarily large
(`SimpleGraph.lt_card_outerBoundary_ballFinset`), so any `N` of the `ν_t` are separated by a
Vandermonde system and cannot satisfy a nontrivial linear relation
(`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`). By Corollary (7.29) over `ℝ`
(`exists_ne_zero_sum_toReal_eq_zero`) that forces `|ex 𝒢(J,h)| ≥ N` for every `N`.

The invariant half of the clause is Comment (12.3)(5) read backwards: on an *arc-transitive*
Cayley tree (`SimpleGraph.IsArcTransitive`, which Georgii's `𝒞𝒯(d)` is —
`SimpleGraph.isArcTransitive_reducedWordTree`) an `I(B)`-invariant Markov chain has one and the
same transition matrix on every oriented bond, so it is completely homogeneous; by Theorem (12.6)
and Proposition (12.24) the extreme `I(B)`-invariant Gibbs measures are therefore among the `μ_t`,
`t` a solution of (12.22), of which there are at most three. -/

section InfinitelyManyPhases

open SimpleGraph

/-- **The parameter of `ν_t` on the sphere `∂B(r, n)`.** Every vertex of the outer boundary of the
ball `B(r, n)` is at distance `n + 1` from the root and its anchor is its parent, so the bond
`k k_Λ` points towards `r` and carries the parameter `u_{n+1}` of the backward orbit. -/
theorem isingTreeParam_anchor_ballFinset (hG : G.IsCayleyTree d) (r : S) (n : ℕ) {k : S}
    (hk : k ∈ G.outerBoundary (G.ballFinset r n)) :
    isingTreeParam G d J h t r k (G.anchor (G.ballFinset r n) k)
      = Real.treeBackOrbit d J h t (n + 1) := by
  have hkd : G.dist r k = n + 1 :=
    (SimpleGraph.mem_outerBoundary_ballFinset_iff hG.connected).1 hk
  have hanc : G.dist r (G.anchor (G.ballFinset r n) k) ≤ n :=
    SimpleGraph.dist_le_of_mem_ballFinset hG.connected (G.anchor_mem hk)
  have hnot : r ∉ G.past k (G.anchor (G.ballFinset r n) k) := by
    simp only [SimpleGraph.mem_past]
    omega
  rw [isingTreeParam_of_notMem_past hnot, hkd]

/-- **Georgii, step 4): the sphere probabilities of `ν_t` are geometric.** The probability of the
cylinder "`-1` on the ball `B(r, n)` and on the sphere `∂B(r, n)` except on `U`, `+1` on `U`" is
the probability of the constant cylinder `-1` times `(ℓ_{u_{n+1}}(+) Q(-,+)/Q(-,-))^{|U|}`. -/
theorem isingTreeChain_cyl_mul_pow (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) (n : ℕ) {U : Finset S}
    (hU : U ⊆ G.outerBoundary (G.ballFinset r n)) :
    isingTreeChain hJ hd hG r ha hb hab ht
          (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n))
            (fun i ↦ if i ∈ U then true else false))
        * isingTransfer d J h false false ^ U.card
      = isingTreeChain hJ hd hG r ha hb hab ht
            (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n)) (fun _ ↦ false))
        * (isingBoundaryVec d h (Real.treeBackOrbit d J h t (n + 1)) true
            * isingTransfer d J h false true) ^ U.card :=
  IsBoundaryLaw.boundaryLawMeasure_cyl_ite_mul_pow (isTransferFamily_isingTransfer G d J h)
    hG.isTree (isBoundaryLaw_isingTreeParam hJ hd hG r ha hb hab ht)
    (SimpleGraph.connected_induce_ballFinset r n)
    (fun _ _ ↦ isingBoundaryVec_false)
    (fun _ hk ↦ by rw [isingTreeParam_anchor_ballFinset hG r n hk])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hU

/-- Georgii, step 4): the geometric ratio `s_n(t) = exp(2 u_{n+1}(t) - 2J)` of the sphere
probabilities of `ν_t` at radius `n + 1`. -/
noncomputable def isingSphereRatio (d : ℕ) (J h t : ℝ) (n : ℕ) : ℝ :=
  exp (2 * Real.treeBackOrbit d J h t (n + 1) - 2 * J)

lemma isingSphereRatio_pos (d : ℕ) (J h t : ℝ) (n : ℕ) : 0 < isingSphereRatio d J h t n :=
  exp_pos _

/-- **Georgii, step 4): the sphere probabilities of `ν_t`, over `ℝ`.** -/
theorem toReal_isingTreeChain_cyl (hJ : 0 < J) (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (r : S)
    {a b : ℝ} (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b)
    (hab : a < b) (ht : t ∈ Set.Ioo a b) (n : ℕ) {U : Finset S}
    (hU : U ⊆ G.outerBoundary (G.ballFinset r n)) :
    (isingTreeChain hJ hd hG r ha hb hab ht
          (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n))
            (fun i ↦ if i ∈ U then true else false))).toReal
      = (isingTreeChain hJ hd hG r ha hb hab ht
            (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n)) (fun _ ↦ false))).toReal
        * isingSphereRatio d J h t n ^ U.card := by
  have hmain := isingTreeChain_cyl_mul_pow hJ hd hG r ha hb hab ht n hU
  have hq : (isingTransfer d J h false false).toReal = exp (J - 2 * (h / (d + 1))) := by
    rw [isingTransfer_false_false, ENNReal.toReal_ofReal (exp_nonneg _)]
  have hLp : (isingBoundaryVec d h (Real.treeBackOrbit d J h t (n + 1)) true
        * isingTransfer d J h false true).toReal
      = exp (2 * Real.treeBackOrbit d J h t (n + 1) - 2 * (h / (d + 1))) * exp (-J) := by
    rw [isingBoundaryVec_true, isingTransfer_false_true, ← ENNReal.ofReal_mul (exp_nonneg _),
      ENNReal.toReal_ofReal (by positivity)]
  have hreal := congrArg ENNReal.toReal hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, hq,
    hLp] at hreal
  have hexp : isingSphereRatio d J h t n * exp (J - 2 * (h / (d + 1)))
      = exp (2 * Real.treeBackOrbit d J h t (n + 1) - 2 * (h / (d + 1))) * exp (-J) := by
    rw [isingSphereRatio, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpos : (0 : ℝ) < exp (J - 2 * (h / (d + 1))) ^ U.card := pow_pos (exp_pos _) _
  refine mul_right_cancel₀ hpos.ne' ?_
  rw [hreal, mul_assoc, ← mul_pow, hexp]

/-- Distinct parameters give distinct sphere ratios. -/
theorem isingSphereRatio_inj (hJ : 0 < J) (hd : 1 ≤ d) {a b : ℝ}
    (ha : Real.treeRecursion d J h a = a) (hb : Real.treeRecursion d J h b = b) (hab : a < b)
    {t s : ℝ} (ht : t ∈ Set.Ioo a b) (hs : s ∈ Set.Ioo a b) (n : ℕ)
    (heq : isingSphereRatio d J h t n = isingSphereRatio d J h s n) : t = s := by
  rw [isingSphereRatio, isingSphereRatio, exp_eq_exp] at heq
  exact Real.treeBackOrbit_inj hJ hd ha hb hab n ht hs (by linarith)


/-- **Georgii Theorem (12.31)(b), step 4) completed: `|ex 𝒢(J, h)| = ∞`.** For `J > J(d)` (i.e.
`d tanh J > 1`) and `|h| ≤ h(J, d)` the set of extreme Gibbs measures is infinite. Georgii's
linear independence of the family `{ν_t : t₋ < t < t₊}` is realised on a sphere: `N` of the `ν_t`
are separated by the `N` cylinder events "`-1` on `B(r,n)`, `+1` on `U ⊆ ∂B(r,n)`",
`|U| = 0, …, N - 1`, whose probabilities are `ν_t(σ ≡ -1) s_n(t)^{|U|}` with `s_n(t)` injective in
`t`, a Vandermonde system; Corollary (7.29) over `ℝ` then forces `|ex 𝒢(J,h)| ≥ N`. -/
theorem infinite_extremePoints_G_isingTreeSpecification [Countable S] (hJ : 0 < J) (hd : 1 ≤ d)
    (hG : G.IsCayleyTree d) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    ((_root_.MeasureTheory.GibbsMeasure.G
      (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞).Infinite := by
  classical
  have hd2 : 2 ≤ d := by
    by_contra hcon
    exact absurd hw (not_lt.2 (Real.mul_tanh_lt_one_of_le_one (by omega) J).le)
  obtain ⟨tmin, hmin, hminle⟩ := Real.exists_isLeast_treeField_eq hJ d h
  obtain ⟨tmax, hmax, hmaxle⟩ := Real.exists_isGreatest_treeField_eq hJ d h
  obtain ⟨c₀, e₀, hce, hcf, hef⟩ := Real.exists_lt_and_treeField_eq hJ hw hh
  have hlt : tmin < tmax := lt_of_le_of_lt (hminle c₀ hcf) (lt_of_lt_of_le hce (hmaxle e₀ hef))
  have ha : Real.treeRecursion d J h tmin = tmin := Real.treeRecursion_eq_self_iff.2 hmin
  have hb : Real.treeRecursion d J h tmax = tmax := Real.treeRecursion_eq_self_iff.2 hmax
  obtain ⟨r⟩ := hG.nonempty
  by_contra hcon
  rw [Set.not_infinite] at hcon
  obtain ⟨N, hN0, hcard⟩ : ∃ N : ℕ, 0 < N ∧ ((_root_.MeasureTheory.GibbsMeasure.G
      (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞).encard < N := by
    refine ⟨hcon.toFinset.card + 1, Nat.succ_pos _, ?_⟩
    rw [hcon.encard_eq_coe_toFinset_card]
    exact_mod_cast Nat.lt_succ_self _
  -- `N` distinct parameters in `]t₋, t₊[`
  obtain ⟨T, hTsub, hTcard⟩ :=
    (Set.infinite_coe_iff.1 (Set.Ioo.infinite hlt)).exists_subset_card_eq N
  have hTeq : T ≃ Fin N := Finset.equivFinOfCardEq hTcard
  have hτmem : ∀ i : Fin N, ((hTeq.symm i : T) : ℝ) ∈ Set.Ioo tmin tmax := fun i ↦
    hTsub (Finset.mem_coe.2 (hTeq.symm i).2)
  have hτinj : Function.Injective fun i : Fin N ↦ ((hTeq.symm i : T) : ℝ) := fun i j hij ↦
    hTeq.symm.injective (Subtype.ext hij)
  -- a sphere with at least `N` sites, and nested subsets of it of every size below `N`
  obtain ⟨n, hn⟩ := SimpleGraph.exists_le_card_outerBoundary_ballFinset hG hd2 r N
  have hUex : ∀ m : Fin N, ∃ U ⊆ G.outerBoundary (G.ballFinset r n), U.card = (m : ℕ) :=
    fun m ↦ Finset.exists_subset_card_eq (le_trans m.isLt.le hn)
  choose U hUsub hUcard using hUex
  have hνG : ∀ i : Fin N, isingTreeChain hJ hd hG r ha hb hlt (hτmem i)
      ∈ _root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h) := fun i ↦
    ⟨inferInstance, isGibbsMeasure_isingTreeChain hJ hd hG r ha hb hlt (hτmem i)⟩
  have hGne : (_root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)).Nonempty :=
    ⟨_, hνG ⟨0, hN0⟩⟩
  obtain ⟨g, hg0, hgsum⟩ := _root_.MeasureTheory.GibbsMeasure.exists_ne_zero_sum_toReal_eq_zero
    hGne hcard hνG
  -- the constant-`-1` cylinder has positive probability
  have hxpos : ∀ i : Fin N, 0 < (isingTreeChain hJ hd hG r ha hb hlt (hτmem i)
      (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n)) (fun _ ↦ false))).toReal := by
    intro i
    refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
    exact (measure_cyl_pos_of_isGibbsMeasure (isTransferFamily_isingTransfer G d J h)
      (isGibbsMeasure_isingTreeChain hJ hd hG r ha hb hlt (hτmem i)) _ _).ne'
  -- the sphere ratios are pairwise distinct
  have hsinj : Function.Injective
      fun i : Fin N ↦ isingSphereRatio d J h ((hTeq.symm i : T) : ℝ) n := fun i j hij ↦
    hτinj (isingSphereRatio_inj hJ hd ha hb hlt (hτmem i) (hτmem j) n hij)
  -- the Vandermonde system
  have hzero : ∀ m : Fin N, ∑ i : Fin N,
      (g i * (isingTreeChain hJ hd hG r ha hb hlt (hτmem i)
          (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n)) (fun _ ↦ false))).toReal)
        * isingSphereRatio d J h ((hTeq.symm i : T) : ℝ) n ^ (m : ℕ) = 0 := by
    intro m
    rw [← hgsum (cyl (G.ballFinset r n ∪ G.outerBoundary (G.ballFinset r n))
      (fun v ↦ if v ∈ U m then true else false)) (measurableSet_cyl _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [toReal_isingTreeChain_cyl hJ hd hG r ha hb hlt (hτmem i) n (hUsub m), hUcard m]
    ring
  have hzero' := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hsinj hzero
  refine hg0 (funext fun i ↦ ?_)
  have hi := congrFun hzero' i
  simp only [Pi.zero_apply] at hi
  exact (mul_eq_zero.1 hi).resolve_right (hxpos i).ne'


/-- **Georgii Comment (12.3)(5), converse.** On an *arc-transitive* Cayley tree an `I(B)`-invariant
Markov chain is completely homogeneous: an automorphism carrying a fixed oriented bond `i₀j₀` to
`ij` carries the transition matrix at `i₀j₀` to the one at `ij`, and invariance of `μ` says the two
agree. (Without arc-transitivity there is nothing to prove and nothing to conclude: `𝒢_{I(B)}`
would be `𝒢`.) -/
theorem isCompletelyHomogeneousMarkovChain_of_forall_measurePreserving (hG : G.IsCayleyTree d)
    (harc : G.IsArcTransitive) {μ : Measure (S → Bool)} (hmc : IsMarkovChain G μ)
    (hinv : ∀ τ ∈ graphAutomorphisms Bool G, MeasurePreserving τ.toFun μ μ) :
    IsCompletelyHomogeneousMarkovChain G μ := by
  obtain ⟨i₀, j₀, hij₀⟩ := hG.exists_adj
  refine ⟨fun x y ↦ transitionProb μ i₀ j₀ x y, hmc, fun i j hij x y _ ↦ ?_⟩
  obtain ⟨φ, hφi, hφj⟩ := harc hij₀ hij
  have hmap : μ.map (siteEquiv Bool φ.toEquiv).toFun = μ :=
    (hinv _ (mem_graphAutomorphisms.2 ⟨φ, rfl⟩)).map_eq
  have hstep := transitionProb_map_siteEquiv (E := Bool) φ.toEquiv μ i j x y
  rw [hmap] at hstep
  have h1 : φ.toEquiv.symm i = i₀ := (Equiv.symm_apply_eq φ.toEquiv).2 hφi.symm
  have h2 : φ.toEquiv.symm j = j₀ := (Equiv.symm_apply_eq φ.toEquiv).2 hφj.symm
  rw [hstep, h1, h2]

/-- **Georgii Theorem (12.31)(b): the invariant extreme phases are among the `μ_t`.** On an
arc-transitive Cayley tree an extreme `I(B)`-invariant Gibbs measure is a Markov chain (Theorem
(12.6)), hence completely homogeneous, hence `μ_t` for a solution `t` of (12.22) (Proposition
(12.24)); and (12.22) has at most three solutions in the critical window. So
`ex 𝒢(J, h) ∩ 𝒢_{I(B)}(J, h)` is finite. -/
theorem finite_extremePoints_G_inter_invariantG [Countable S] (hJ : 0 < J) (hd : 1 ≤ d)
    (hG : G.IsCayleyTree d) (harc : G.IsArcTransitive)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    ((_root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ ∩
      invariantG (isingTreeSpecification G d J h) (graphAutomorphisms Bool G)).Finite := by
  classical
  refine Set.Finite.subset ((finite_setOf_isFixedPt_treeRecursion hJ hd hh).image
    (fun s ↦ if hsol : s = h + d * logCoshRatio J s then isingChain hG hsol else 0)) ?_
  rintro μ ⟨hext, hinvG⟩
  have hμP : IsProbabilityMeasure μ := hext.1.1
  have hmc : IsMarkovChain G μ :=
    exists_isMarkovChain_of_mem_extremePoints hG.isTree
      (isMarkovSpecification_transferSpecification (isTransferFamily_isingTransfer G d J h)) hext
  have hinv : ∀ τ ∈ graphAutomorphisms Bool G, MeasurePreserving τ.toFun μ μ :=
    (mem_invariantFields_iff.1 hinvG.2).2
  obtain ⟨t, hsol, rfl⟩ := exists_eq_isingChain hG hext.1.2
    (isCompletelyHomogeneousMarkovChain_of_forall_measurePreserving hG harc hmc hinv)
  refine ⟨t, ?_, ?_⟩
  · change Real.treeRecursion d J h t = t
    rw [Real.treeRecursion]
    linarith
  · exact dite_eq_left hsol

/-- **Georgii Theorem (12.31)(b), last clause: `|ex 𝒢(J,h) ∖ ex 𝒢_{I(B)}(J,h)| = ∞`.** For
`J > J(d)` and `|h| ≤ h(J,d)` on an arc-transitive Cayley tree there are infinitely many extreme
Gibbs measures that are not `I(B)`-invariant — Georgii's step 4) in full: `ex 𝒢(J,h)` is infinite
while `ex 𝒢(J,h) ∩ 𝒢_{I(B)}(J,h)` has at most three elements. -/
theorem infinite_extremePoints_G_sdiff_extremePoints_invariantG [Countable S] (hJ : 0 < J)
    (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (harc : G.IsArcTransitive)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ((_root_.MeasureTheory.GibbsMeasure.G (isingTreeSpecification G d J h)).extremePoints ℝ≥0∞ \
      (invariantG (isingTreeSpecification G d J h)
        (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞).Infinite := by
  refine Set.Infinite.mono (fun μ hμ ↦ ⟨hμ.1, fun hcon ↦ hμ.2 ⟨hμ.1, extremePoints_subset hcon⟩⟩)
    ((infinite_extremePoints_G_isingTreeSpecification hJ hd hG hw hh).sdiff
      (finite_extremePoints_G_inter_invariantG hJ hd hG harc hh))

end InfinitelyManyPhases

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

/-- **Georgii, the antiferromagnetic phase transition.** For `J < -J(d)` (i.e. `1 < d |tanh J|`)
and `|h| < ĥ(J, d)`, equation (12.35) *does* have a solution off (12.22)
(`Real.exists_isFixedPt_treeRecursion₂_ne`), so `𝒢(J, h)` contains the two distinct alternating
Markov chains `μ_{-+} ≠ μ_{+-}`; in particular `|𝒢(J, h)| > 1`. Here
`ĥ(J, d) = t_{-J,d} - d φ_J(t_{-J,d}) = h(-J, d) + 2 t_{-J,d} > 0` is the quantity with which
Georgii establishes that his transition interval `I(J, d)` is non-degenerate; his further
assertion `I(J, d) = ]-ĥ, ĥ[` is stated in the book as suggested by numerical calculations, and
is not proved here. -/
theorem exists_ne_isGibbsMeasure_of_abs_lt_antiferroCriticalField (hG : G.IsCayleyTree d)
    (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|)
    (hh : |h| < Real.antiferroCriticalField d J) :
    ∃ μ ν : Measure (S → Bool), μ ≠ ν ∧
      (isingTreeSpecification G d J h).IsGibbsMeasure μ ∧
      (isingTreeSpecification G d J h).IsGibbsMeasure ν := by
  obtain ⟨c, hc⟩ := hG.exists_bool_coloring
  obtain ⟨t, hfix, hne⟩ := Real.exists_isFixedPt_treeRecursion₂_ne hJ hw hh
  exact exists_ne_isGibbsMeasure_of_isFixedPt_treeRecursion₂ hG hc hfix hne

end AlternatingChains


/-! ## Georgii (12.7), (12.9): `γ^{J,h}` is the Gibbs specification of the Ising potential

Georgii's `𝒢(J, h)` is the set of Gibbs measures of the Gibbsian specification `γ^{Φ^{J,h}}` of
the Ising potential (12.19); he passes to the transfer specification (12.8) of the matrix (12.20)
"in view of (12.7) and (12.9)". That step is proved here. On `𝒞𝒯(d)` every site of `Λ` lies on
exactly `d + 1` bonds meeting `Λ`, so it collects `h σ_i/(d+1)` from each of them, i.e. exactly
`h σ_i` in total; the ends in `∂Λ` of the bonds meeting `Λ` contribute a factor depending only on
the configuration off `Λ`, and such a factor cancels between the density and the partition
function of a λ-specification (`Specification.lambdaSpecification_eq_of_mul_boundary`). -/

section GibbsRepresentation

/-! ### Double counting the ends of the bonds meeting `Λ` -/

variable (G) in
/-- The number of bonds meeting `Λ` that are incident to the site `k`. For `k ∈ Λ` this is the
degree of `k`, i.e. `d + 1` on `𝒞𝒯(d)`; for `k ∈ ∂Λ` it is the number of neighbours of `k`
in `Λ`. -/
def bondCount (Λ : Finset S) (k : S) : ℕ := (G.incidenceFinset k ∩ G.bondsOf Λ).card

/-- **Double counting.** The two ends of each bond meeting `Λ` are collected site by site. -/
lemma sum_bondsOf_spinSum (Λ : Finset S) (σ : S → Bool) :
    ∑ b ∈ G.bondsOf Λ, spinSum σ b
      = ∑ k ∈ Λ ∪ G.outerBoundary Λ, (bondCount G Λ k : ℝ) * spin (σ k) := by
  classical
  have hstep : ∀ b ∈ G.bondsOf Λ, spinSum σ b = ∑ k ∈ b.toFinset, spin (σ k) := by
    intro b hb
    revert hb
    refine Sym2.inductionOn b fun i j hb ↦ ?_
    have hij : i ≠ j := (SimpleGraph.mk_mem_bondsOf.1 hb).1.ne
    rw [spinSum_mk, Sym2.toFinset_mk_eq, Finset.sum_pair hij]
  have hcomm : ∀ (b : Sym2 S) (k : S),
      b ∈ G.bondsOf Λ ∧ k ∈ b.toFinset
        ↔ b ∈ G.incidenceFinset k ∩ G.bondsOf Λ ∧ k ∈ Λ ∪ G.outerBoundary Λ := by
    intro b k
    simp only [Sym2.mem_toFinset, Finset.mem_inter, SimpleGraph.mem_incidenceFinset,
      SimpleGraph.incidenceSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hb, hk⟩
      exact ⟨⟨⟨(SimpleGraph.mem_bondsOf.1 hb).1, hk⟩, hb⟩,
        mem_union_outerBoundary_of_mem_bondsOf G hb hk⟩
    · rintro ⟨⟨⟨-, hk⟩, hb⟩, -⟩
      exact ⟨hb, hk⟩
  calc ∑ b ∈ G.bondsOf Λ, spinSum σ b
      = ∑ b ∈ G.bondsOf Λ, ∑ k ∈ b.toFinset, spin (σ k) := Finset.sum_congr rfl hstep
    _ = ∑ k ∈ Λ ∪ G.outerBoundary Λ, ∑ _b ∈ G.incidenceFinset k ∩ G.bondsOf Λ, spin (σ k) :=
        Finset.sum_comm' hcomm
    _ = ∑ k ∈ Λ ∪ G.outerBoundary Λ, (bondCount G Λ k : ℝ) * spin (σ k) :=
        Finset.sum_congr rfl fun k _ ↦ by rw [Finset.sum_const, nsmul_eq_mul, bondCount]

/-- On `𝒞𝒯(d)` every site of `Λ` lies on exactly `d + 1` bonds meeting `Λ`. -/
lemma bondCount_of_mem (hG : G.IsCayleyTree d) {Λ : Finset S} {k : S} (hk : k ∈ Λ) :
    bondCount G Λ k = d + 1 := by
  have hsub : G.incidenceFinset k ⊆ G.bondsOf Λ := by
    rw [← SimpleGraph.bondsOf_singleton (G := G)]
    exact SimpleGraph.bondsOf_mono (Finset.singleton_subset_iff.2 hk)
  rw [bondCount, Finset.inter_eq_left.2 hsub, SimpleGraph.incidenceFinset_eq_image,
    Finset.card_image_of_injective _ (SimpleGraph.injective_mk_left k), hG.card_neighborFinset]

/-! ### The bond product is the Boltzmann factor times a boundary factor -/

variable (G d h) in
/-- Georgii's boundary term: the contribution of the ends in `∂Λ` of the bonds meeting `Λ`, each
carrying `h/(d+1)` per bond. It depends on the configuration only off `Λ`. -/
def isingBoundarySum (Λ : Finset S) (σ : S → Bool) : ℝ :=
  h / (d + 1) * ∑ k ∈ G.outerBoundary Λ, (bondCount G Λ k : ℝ) * spin (σ k)

variable (G d h) in
/-- The boundary weight `exp (isingBoundarySum)`: the factor by which the bond product
`∏_{b ∩ Λ ≠ ∅} Q_b` of (12.20) differs from the Boltzmann factor `e^{-H_Λ}` of (12.19). -/
def isingBoundaryWeight (Λ : Finset S) (σ : S → Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (isingBoundarySum G d h Λ σ))

lemma isingBoundaryWeight_ne_zero (Λ : Finset S) (σ : S → Bool) :
    isingBoundaryWeight G d h Λ σ ≠ 0 := (ENNReal.ofReal_pos.2 (exp_pos _)).ne'

lemma isingBoundaryWeight_ne_top (Λ : Finset S) (σ : S → Bool) :
    isingBoundaryWeight G d h Λ σ ≠ ⊤ := ENNReal.ofReal_ne_top

lemma dependsOn_isingBoundaryWeight (Λ : Finset S) :
    DependsOn (isingBoundaryWeight G d h Λ) ((Λ : Set S)ᶜ) := by
  intro σ τ hst
  have hsum : ∀ k ∈ G.outerBoundary Λ,
      (bondCount G Λ k : ℝ) * spin (σ k) = (bondCount G Λ k : ℝ) * spin (τ k) := fun k hk ↦ by
    rw [hst k (by simpa using G.notMem_of_mem_outerBoundary hk)]
  rw [isingBoundaryWeight, isingBoundaryWeight, isingBoundarySum, isingBoundarySum,
    Finset.sum_congr rfl hsum]

/-- Each bond weight of (12.20) is `exp` of the bond energy plus the shared external field. -/
lemma bondWeight_isingTransfer (σ : S → Bool) (b : Sym2 S) :
    bondWeight (fun _ _ : S ↦ isingTransfer d J h)
        (isTransferFamily_isingTransfer G d J h).symm σ b
      = ENNReal.ofReal (exp (J * spinBond σ b + h / (d + 1) * spinSum σ b)) := by
  refine Sym2.inductionOn b fun i j ↦ ?_
  rw [bondWeight_mk, isingTransfer_apply, spinBond_mk, spinSum_mk]
  congr 2
  ring

/-- **Georgii (12.7), (12.9).** The bond product `∏_{b ∩ Λ ≠ ∅} Q_b` of the transfer matrix
(12.20) is the Boltzmann factor `e^{-H_Λ^{Φ^{J,h}}}` of the Ising potential (12.19) times a factor
depending only on the configuration outside `Λ`: on `𝒞𝒯(d)` each site of `Λ` collects
`h σ_i/(d+1)` from each of its `d + 1` bonds, i.e. `h σ_i` in total. -/
theorem transferWeight_isingTransfer_eq (hG : G.IsCayleyTree d) (Λ : Finset S) (σ : S → Bool) :
    transferWeight G (fun _ _ : S ↦ isingTransfer d J h)
        (isTransferFamily_isingTransfer G d J h).symm Λ σ
      = (isingPotential G J h).boltzmannFactor 1 Λ σ * isingBoundaryWeight G d h Λ σ := by
  classical
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  have hsplit : ∑ k ∈ Λ ∪ G.outerBoundary Λ, (bondCount G Λ k : ℝ) * spin (σ k)
      = ((d : ℝ) + 1) * ∑ k ∈ Λ, spin (σ k)
        + ∑ k ∈ G.outerBoundary Λ, (bondCount G Λ k : ℝ) * spin (σ k) := by
    rw [Finset.sum_union (G.disjoint_outerBoundary Λ), Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [bondCount_of_mem hG hk]
      push_cast
      ring
  have hexp : ∑ b ∈ G.bondsOf Λ, (J * spinBond σ b + h / (d + 1) * spinSum σ b)
      = -1 * (isingPotential G J h).hamiltonian Λ σ + isingBoundarySum G d h Λ σ := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_bondsOf_spinSum, hsplit,
      hamiltonian_isingPotential, isingBoundarySum, mul_add]
    have hcancel : h / ((d : ℝ) + 1) * (((d : ℝ) + 1) * ∑ k ∈ Λ, spin (σ k))
        = h * ∑ k ∈ Λ, spin (σ k) := by field_simp
    rw [hcancel]
    ring
  rw [transferWeight, Finset.prod_congr rfl (fun b _ ↦ bondWeight_isingTransfer (G := G) σ b),
    ← ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ exp_nonneg _), ← Real.exp_sum, hexp, Real.exp_add,
    ENNReal.ofReal_mul (exp_nonneg _)]
  rfl

/-! ### Georgii's identification `γ^{J,h} = γ^{Φ^{J,h}}` -/

lemma count_univ_bool : (Measure.count : Measure Bool) Set.univ = 2 := by
  rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
  norm_num

/-- The counting measure on `E = {-1, 1}` normalises to the uniform a priori measure of the Ising
model, so Georgii's counting a priori measure and `uniformSpinMeasure` give the same Gibbsian
specification (Remark (1.28)(3)). -/
lemma probNormalize_count_bool :
    (Measure.count : Measure Bool).probNormalize = uniformSpinMeasure := by
  rw [Measure.probNormalize_def, count_univ_bool, uniformSpinMeasure]

/-- **Georgii (12.7), (12.9): the identification.** On the Cayley tree `𝒞𝒯(d)` the transfer
specification (12.8) of the Ising transfer matrix (12.20) *is* the Gibbsian specification
`γ^{Φ^{J,h}}` of the Ising potential (12.19) at inverse temperature `1`. Hence
`𝒢(J, h) = 𝒢(Φ^{J,h})` really is the Gibbs-measure set of `isingTreeSpecification`, and every
theorem of §12.2 above is a theorem about the Ising potential. -/
theorem isingTreeSpecification_eq_isingSpecification [Countable S] (hG : G.IsCayleyTree d) :
    isingTreeSpecification G d J h = isingSpecification G J h 1 := by
  classical
  have : IsFiniteMeasure (Measure.count : Measure Bool) :=
    ⟨by rw [count_univ_bool]; norm_num⟩
  have : NeZero (Measure.count : Measure Bool) := ⟨fun hcon ↦ by
    have hu := count_univ_bool
    rw [hcon] at hu
    simp at hu⟩
  have hQ := isTransferFamily_isingTransfer G d J h
  have hρ₁ : Specification.IsPremodifier (S := S) (E := Bool)
      ((isingPotential G J h).boltzmannFactor 1) := Potential.isPremodifier_boltzmannFactor 1
  have hZ₁ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := Bool)
      Measure.count ((isingPotential G J h).boltzmannFactor 1) :=
    Potential.isSigmaFiniteLambdaAdmissible_boltzmannFactor Measure.count 1
  have h3 : isingTreeSpecification G d J h
      = Specification.lambdaSpecification (S := S) (E := Bool) Measure.count
          ((isingPotential G J h).boltzmannFactor 1) hρ₁ hZ₁ :=
    Specification.lambdaSpecification_eq_of_mul_boundary (S := S) (E := Bool) Measure.count
      hρ₁ hZ₁ (isPremodifier_transferWeight hQ.symm) hQ.isSigmaFiniteLambdaAdmissible
      (fun Λ ω ↦ isingBoundaryWeight_ne_zero Λ ω) (fun Λ ω ↦ isingBoundaryWeight_ne_top Λ ω)
      (fun Λ ↦ dependsOn_isingBoundaryWeight Λ)
      (fun Λ ω ↦ transferWeight_isingTransfer_eq hG Λ ω)
  calc isingTreeSpecification G d J h
      = Potential.gibbsSpecificationOfFiniteReference (isingPotential G J h)
          (Measure.count : Measure Bool) 1 := h3
    _ = Potential.gibbsSpecificationOfAbsolutelySummable
          (Measure.count : Measure Bool).probNormalize 1 :=
        Potential.gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable
          (Φ := isingPotential G J h) Measure.count 1
    _ = isingSpecification G J h 1 := by
        rw [isingSpecification]
        simp only [probNormalize_count_bool]

end GibbsRepresentation

/-! ## Georgii §12.2 for `𝒢(J, h) = 𝒢(Φ^{J,h})`

The conclusions of §12.2, restated — as Georgii states them — for the Gibbs-measure set of the
Ising potential (12.19) itself. -/

section IsingPotentialConclusions

variable [Countable S]

/-- **Georgii Theorem (12.31)(a) for `𝒢(J, h)`.** On `𝒞𝒯(d)` with `J > 0`, if `J ≤ J(d)`
(equivalently `d tanh J ≤ 1`) or `|h| > h(J, d)`, the Ising potential (12.19) has exactly one
Gibbs measure. -/
theorem exists_G_isingSpecification_eq_singleton (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hcase : (d : ℝ) * tanh J ≤ 1 ∨ Real.treeCriticalField d J < |h|) :
    ∃ μ : Measure (S → Bool),
      _root_.MeasureTheory.GibbsMeasure.G (isingSpecification G J h 1) = {μ} := by
  obtain ⟨t, hsol, ht⟩ := exists_G_isingTreeSpecification_eq_singleton hJ hG hcase
  exact ⟨isingChain hG hsol, by rw [← isingTreeSpecification_eq_isingSpecification hG]; exact ht⟩

/-- **Georgii Theorem (12.31)(b) for `𝒢(J, h)`.** On `𝒞𝒯(d)` with `J > J(d)` (i.e.
`d tanh J > 1`) and `|h| ≤ h(J, d)`, the Ising potential (12.19) has at least two distinct Gibbs
measures: the completely homogeneous Markov chains `μ₋ ≠ μ₊` of Proposition (12.24). -/
theorem exists_ne_isGibbsMeasure_isingSpecification (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ∃ μ ν : Measure (S → Bool), μ ≠ ν ∧
      (isingSpecification G J h 1).IsGibbsMeasure μ ∧
      (isingSpecification G J h 1).IsGibbsMeasure ν := by
  obtain ⟨t₁, t₂, hs₁, hs₂, hne⟩ := exists_ne_isingChain hJ hG hw hh
  refine ⟨isingChain hG hs₁, isingChain hG hs₂, hne, ?_, ?_⟩ <;>
    rw [← isingTreeSpecification_eq_isingSpecification hG]
  · exact isGibbsMeasure_isingChain hG hs₁
  · exact isGibbsMeasure_isingChain hG hs₂

/-- **Georgii, the antiferromagnetic phase transition for `𝒢(J, h)`.** On `𝒞𝒯(d)` with
`J < -J(d)` (i.e. `1 < d |tanh J|`) and `|h| < ĥ(J, d)`, the *antiferromagnetic* Ising potential
(12.19) has at least two distinct Gibbs measures: the alternating Markov chains `μ_{-+} ≠ μ_{+-}`
of (12.34). -/
theorem exists_ne_isGibbsMeasure_isingSpecification_antiferro (hG : G.IsCayleyTree d)
    (hJ : J < 0) (hw : 1 < (d : ℝ) * |tanh J|)
    (hh : |h| < Real.antiferroCriticalField d J) :
    ∃ μ ν : Measure (S → Bool), μ ≠ ν ∧
      (isingSpecification G J h 1).IsGibbsMeasure μ ∧
      (isingSpecification G J h 1).IsGibbsMeasure ν := by
  obtain ⟨μ, ν, hne, hμ, hν⟩ :=
    exists_ne_isGibbsMeasure_of_abs_lt_antiferroCriticalField hG hJ hw hh
  refine ⟨μ, ν, hne, ?_, ?_⟩ <;> rwa [← isingTreeSpecification_eq_isingSpecification hG]

/-- **Georgii Theorem (12.31)(b), first clause, for `𝒢(J, h)`.** On `𝒞𝒯(d)` with `J > J(d)` and
`|h| ≤ h(J, d)`, the Ising potential (12.19) has two distinct Gibbs measures `μ₋ ≠ μ₊` which are
both extreme in `𝒢(J, h)` and extreme in `𝒢_{I(B)}(J, h)`. -/
theorem exists_ne_mem_extremePoints_G_isingSpecification (hJ : 0 < J) (hG : G.IsCayleyTree d)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ∃ μ ν : Measure (S → Bool), μ ≠ ν ∧
      μ ∈ (_root_.MeasureTheory.GibbsMeasure.G
            (isingSpecification G J h 1)).extremePoints ℝ≥0∞ ∩
          (invariantG (isingSpecification G J h 1)
            (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ ∧
      ν ∈ (_root_.MeasureTheory.GibbsMeasure.G
            (isingSpecification G J h 1)).extremePoints ℝ≥0∞ ∩
          (invariantG (isingSpecification G J h 1)
            (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞ := by
  obtain ⟨t₁, t₂, hs₁, hs₂, hne, h₁, h₂⟩ :=
    exists_ne_mem_extremePoints_G_inter_invariantG_isingChain hJ hG hw hh
  rw [← isingTreeSpecification_eq_isingSpecification hG]
  exact ⟨isingChain hG hs₁, isingChain hG hs₂, hne, h₁, h₂⟩

/-- **Georgii Theorem (12.31)(b), last clause, for the Ising potential.** On an arc-transitive
Cayley tree, `|ex 𝒢(Φ^{J,h}) ∖ ex 𝒢_{I(B)}(Φ^{J,h})| = ∞` for `J > J(d)` and `|h| ≤ h(J, d)`. -/
theorem infinite_extremePoints_G_sdiff_extremePoints_invariantG_isingSpecification (hJ : 0 < J)
    (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (harc : G.IsArcTransitive)
    (hw : 1 < (d : ℝ) * tanh J) (hh : |h| ≤ Real.treeCriticalField d J) :
    ((_root_.MeasureTheory.GibbsMeasure.G (isingSpecification G J h 1)).extremePoints ℝ≥0∞ \
      (invariantG (isingSpecification G J h 1)
        (graphAutomorphisms Bool G)).extremePoints ℝ≥0∞).Infinite := by
  rw [← isingTreeSpecification_eq_isingSpecification hG]
  exact infinite_extremePoints_G_sdiff_extremePoints_invariantG hJ hd hG harc hw hh

/-- **Georgii Theorem (12.31)(b), step 4), for `𝒢(J, h)`.** On `𝒞𝒯(d)` with `J > J(d)` and
`|h| ≤ h(J, d)` the Ising potential (12.19) has infinitely many Gibbs measures which are Markov
chains but *not* completely homogeneous. -/
theorem infinite_setOf_mem_G_not_isCompletelyHomogeneous_isingSpecification (hJ : 0 < J)
    (hd : 1 ≤ d) (hG : G.IsCayleyTree d) (hw : 1 < (d : ℝ) * tanh J)
    (hh : |h| ≤ Real.treeCriticalField d J) :
    {μ : Measure (S → Bool) |
      μ ∈ _root_.MeasureTheory.GibbsMeasure.G (isingSpecification G J h 1) ∧
        IsMarkovChain G μ ∧ ¬ IsCompletelyHomogeneousMarkovChain G μ}.Infinite := by
  rw [← isingTreeSpecification_eq_isingSpecification hG]
  exact infinite_setOf_mem_G_not_isCompletelyHomogeneous hJ hd hG hw hh

end IsingPotentialConclusions

/-! ## A witness: the Ising ferromagnet on `𝒞𝒯(2)`

`SimpleGraph.isCayleyTree_reducedWordTree` builds `𝒞𝒯(d)` for every `d`, so the hypotheses of
Theorem (12.31)(b) can be met. Here is the smallest instance: `d = 2` and a coupling with
`2 tanh J > 1`, i.e. `J > J(2) = ar coth 2`. -/

section CayleyTreeTwo

open SimpleGraph

/-- The coupling `J = ar tanh (3/4)` of the witness below: `2 tanh J = 3/2 > 1`, i.e.
`J > J(2) = ar coth 2`. -/
noncomputable def witnessCoupling : ℝ := artanh (3 / 4)

lemma witnessCoupling_pos : 0 < witnessCoupling := artanh_pos ⟨by norm_num, by norm_num⟩

lemma tanh_witnessCoupling : tanh witnessCoupling = 3 / 4 :=
  tanh_artanh ⟨by norm_num, by norm_num⟩

lemma one_lt_two_mul_tanh_witnessCoupling : 1 < (2 : ℝ) * tanh witnessCoupling := by
  rw [tanh_witnessCoupling]
  norm_num

/-- **Georgii Theorem (12.31)(b), witnessed.** On the Cayley tree `𝒞𝒯(2)` — the tree of reduced
words over `Fin 3`, `SimpleGraph.isCayleyTree_reducedWordTree` — the ferromagnetic Ising potential
(12.19) with coupling `J = ar tanh (3/4)` (so `2 tanh J = 3/2 > 1`, i.e. `J > J(2)`) and no
external field has at least two distinct Gibbs measures: a phase transition for the Ising model
itself, not merely for a transfer specification. -/
theorem exists_ne_isGibbsMeasure_isingSpecification_reducedWordTree :
    ∃ μ ν : Measure (ReducedWord 3 → Bool), μ ≠ ν ∧
      (isingSpecification (reducedWordTree 3) witnessCoupling 0 1).IsGibbsMeasure μ ∧
      (isingSpecification (reducedWordTree 3) witnessCoupling 0 1).IsGibbsMeasure ν :=
  exists_ne_isGibbsMeasure_isingSpecification witnessCoupling_pos
    (isCayleyTree_reducedWordTree 2) (by simpa using one_lt_two_mul_tanh_witnessCoupling)
    (by
      rw [abs_zero]
      exact Real.treeCriticalField_nonneg witnessCoupling_pos (by norm_num))

/-- **Georgii, the antiferromagnetic phase transition, witnessed.** On `𝒞𝒯(2)` the
*antiferromagnetic* Ising potential with coupling `J = -ar tanh (3/4)` (so `2 |tanh J| = 3/2 > 1`,
i.e. `J < -J(2)`) and no external field has at least two distinct Gibbs measures. Note that,
unlike the ferromagnet, this happens although (12.22) has a *unique* solution, i.e. although
`𝒢(J, h)` contains only one completely homogeneous Markov chain. -/
theorem exists_ne_isGibbsMeasure_isingSpecification_reducedWordTree_antiferro :
    ∃ μ ν : Measure (ReducedWord 3 → Bool), μ ≠ ν ∧
      (isingSpecification (reducedWordTree 3) (-witnessCoupling) 0 1).IsGibbsMeasure μ ∧
      (isingSpecification (reducedWordTree 3) (-witnessCoupling) 0 1).IsGibbsMeasure ν := by
  have hJ : -witnessCoupling < 0 := neg_neg_iff_pos.2 witnessCoupling_pos
  have hw : 1 < (2 : ℝ) * |tanh (-witnessCoupling)| := by
    rw [tanh_neg, abs_neg, abs_of_pos (by rw [tanh_witnessCoupling]; norm_num)]
    simpa using one_lt_two_mul_tanh_witnessCoupling
  refine exists_ne_isGibbsMeasure_isingSpecification_antiferro (isCayleyTree_reducedWordTree 2)
    hJ (by simpa using hw) ?_
  rw [abs_zero]
  exact Real.antiferroCriticalField_pos hJ (by simpa using hw)

/-- **Georgii Theorem (12.31)(b), last clause, witnessed.** On `𝒞𝒯(2)` at `J = ar tanh (3/4)`,
`h = 0` the ferromagnetic Ising potential has infinitely many extreme Gibbs measures that are not
invariant under the automorphism group `I(B)` of the tree: the tree of reduced words over `Fin 3`
is arc-transitive (`SimpleGraph.isArcTransitive_reducedWordTree`). -/
theorem infinite_extremePoints_G_sdiff_extremePoints_invariantG_reducedWordTree :
    ((_root_.MeasureTheory.GibbsMeasure.G (isingSpecification (reducedWordTree 3) witnessCoupling
          0 1)).extremePoints ℝ≥0∞ \
      (invariantG (isingSpecification (reducedWordTree 3) witnessCoupling 0 1)
        (graphAutomorphisms Bool (reducedWordTree 3))).extremePoints ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_sdiff_extremePoints_invariantG_isingSpecification witnessCoupling_pos
    (by norm_num) (isCayleyTree_reducedWordTree 2) isArcTransitive_reducedWordTree
    (by simpa using one_lt_two_mul_tanh_witnessCoupling)
    (by
      rw [abs_zero]
      exact Real.treeCriticalField_nonneg witnessCoupling_pos (by norm_num))

end CayleyTreeTwo

end MeasureTheory.GibbsMeasure.Tree

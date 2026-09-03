/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLaw
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.ExtremeCorollaries
public import GibbsMeasure.Mathlib.Probability.TailTriviality
public import GibbsMeasure.Prereqs.MeasureExt
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Georgii §12.1: Markov chains and boundary laws on trees, continued

Continues `GibbsMeasure.Model.TreeBoundaryLaw` (which has Definitions (12.1), (12.2), (12.8)–
(12.10), Theorem (12.12)(a), (12.12)(b)'s existence clause, and Corollary (12.17)'s "construction"
direction) with the remaining numbered items of §12.1: Comments (12.3)(2), (4), equation (12.5),
the uniqueness-up-to-a-factor clause of Theorem (12.12)(b), the full Markov-chain correspondence of
Corollary (12.17) (both directions, and its uniqueness), and **Theorem (12.6)** itself — every
extreme Gibbs measure of a Markov specification on a locally finite tree is a Markov chain. A
previous pass of this file claimed (12.6) was blocked on "the backward martingale convergence
theorem"; that tool (Lévy's downward theorem, `Integrable.tendsto_ae_condExp_of_antitone` in
`GibbsMeasure/Mathlib/Probability/Martingale/Convergence.lean`) was already in the library, and
Georgii's own proof of (12.6) needs nothing more exotic — see the `## Georgii Theorem (12.6)`
section below for the full account, including exactly which hypotheses are used. **Corollary
(12.18)** is now formalised too (see its own section below), generalised to any locally finite
tree and any transfer family (Georgii's `𝒞𝒯(d)`/complete homogeneity are not used by the proof).
Comments (12.3)(3), (5), (6) remain **not formalised**; see below for exactly why in each case.

## What is proved here

* Comment (12.3)(2) (equation (12.4)), Comment (12.3)(4) (equation (12.5)), the uniqueness clause
  of Theorem (12.12)(b), and the two-directional Corollary (12.17), as in the previous pass of this
  file (sections below, unchanged).
* **Theorem (12.6)**: `exists_isMarkovChain_of_mem_extremePoints`, in the section
  `## Georgii Theorem (12.6)` — see that section's own module-doc-style header for the exact
  statements of every lemma along the way, the hypotheses used, and where the general lemmas
  (`condExp_eq_condExp_of_le_of_condExp_eq`, `exists_ae_eq_single_of_forall_measure_eq_zero_or_one`,
  `IsMarkovSpecification.dependsOn_apply(_cyl)`,
  `IsGibbsMeasure.condExp_indicator_ae_eq_toReal_of_isMarkovSpecification`) belong once upstreamed.
* **Corollary (12.18)**: `not_isMarkovChain_sum_smul_of_forall_adj_exists_boundaryLaw_eq`, in the
  section `## Georgii Corollary (12.18)` — see that section's own header for the exact hypotheses,
  the (weaker, still Georgii-faithful) generality at which it is proved, and the general lemmas
  along the way (`boundaryLawWeight_singleton_eq`, `normalizeBoundaryLaw` and its two properties,
  `MeasureTheory.GibbsMeasure.sum_smul_mem_G` for the convexity of `𝒢(γ)`, and the equality case of
  Jensen's inequality, `StrictConvexOn.map_sum_eq_iff_of_nonneg`, for the quadratic/linear
  identity).

## What is not formalised, beyond (12.6) and (12.18)

* **Comments (12.3)(3) and (12.3)(6)** are not formalised: (3) needs a formal notion of a graph
  embedding `ℤ ↪ S` (an embedded bi-infinite geodesic) that does not yet exist anywhere in the tree
  combinatorics files, and (6) needs a `𝒯_Λ`-style "local tail" σ-algebra and its associated
  generated-π-system argument, neither of which exists yet either; both are genuine follow-on
  constructions rather than gaps in the argument given here.
* **Comment (12.3)(5)** (a positive stochastic matrix is the transition matrix of a completely
  homogeneous Markov chain iff it is reversible, and in that case the chain is invariant under the
  full graph-automorphism group `I(B)` of `S`) is not formalised: the reversibility half already
  follows from `isCompletelyHomogeneousMarkovChain_iff_exists_isBoundaryLaw_const_solves` above
  (Corollary (12.17)) combined with `isBoundaryLaw_const_iff` (12.16)'s reversibility content, but
  the automorphism-invariance half needs a formal notion of a graph automorphism of `S` (`I(B)`)
  and the fact from (12.4) that `boundaryLawMeasure` of a *constant* boundary law is invariant
  under it; no such automorphism-group infrastructure exists yet in the tree combinatorics files,
  and building it is a genuine follow-on construction, not a gap in the argument given here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Tree

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

local notation "λ₀" => Specification.sigmaFiniteLambdaFun (S := S) (E := E) Measure.count

/-! ## Comment (12.3)(4), necessity, and equation (12.5)

These two lemmas are about `transitionProb` (defined in `TreeBoundaryLaw.lean`) and an arbitrary
probability measure `μ` on `S → E`; they do not use `IsMarkovChain` or any graph structure. This is
deliberate: Georgii's `P_{ij}` in Comment (12.3)(4) is *any* stochastic matrix satisfying
`μ(σ_j = y | 𝓕_{\{i\}}) = P_{ij}(σ_i, y)` a.s., but wherever `α_i(x) > 0` this a.s. equation pins
`P_{ij}(x, ·)` down to the concrete ratio `transitionProb μ i j x ·`
(`IsMarkovChain.measure_preimage_inter_cyl` with `Δ = {i}` already proves this, and is exactly how
`chainBoundaryLaw`/(12.12)(b) uses `transitionProb` as *the* transition matrix of a Markov chain).
So proving (12.5) for `transitionProb` is the content of Comment (12.3)(4)'s necessity direction,
and it holds unconditionally, not just for actual Markov chains. -/

section TransitionProbSwap

variable {μ : Measure (S → E)} [IsProbabilityMeasure μ]

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
/-- The defining ratio of `transitionProb`, cleared of its denominator: `α_i(x) P_{ij}(x, y) =
μ(σ_i = x, σ_j = y)`. This holds unconditionally (in particular also when `α_i(x) = 0`, in which
case both sides vanish since `σ_i = x, σ_j = y` is a subset of `σ_i = x`). -/
theorem transitionProb_mul_measure_eq (i j : S) (x y : E) :
    μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) * transitionProb μ i j x y
      = μ ((fun σ : S → E ↦ σ i) ⁻¹' {x} ∩ (fun σ : S → E ↦ σ j) ⁻¹' {y}) :=
  ENNReal.mul_div_cancel' (fun h ↦ measure_mono_null Set.inter_subset_left h)
    (fun h ↦ absurd h (measure_ne_top μ _))

omit [DecidableEq S] [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii equation (12.5) / Comment (12.3)(4), necessity.** `α_i(x) P_{ij}(x, y) = α_j(y)
P_{ji}(y, x)`, where `α_k(x) = μ(σ_k = x)` is the marginal of `μ` at `k` and `P_{ij} =
transitionProb μ i j`. -/
theorem transitionProb_mul_transitionProb_swap_eq (i j : S) (x y : E) :
    μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) * transitionProb μ i j x y
      = μ ((fun σ : S → E ↦ σ j) ⁻¹' {y}) * transitionProb μ j i y x := by
  rw [transitionProb_mul_measure_eq, transitionProb_mul_measure_eq, Set.inter_comm]

omit [DecidableEq S] in
/-- `transitionProb μ i j x` is a probability vector in `y` whenever `x` has positive marginal
probability: `∑_y P_{ij}(x, y) = 1`. Together with `transitionProb_mul_transitionProb_swap_eq`
this is Comment (12.3)(4): `transitionProb μ i j` is a genuine stochastic matrix satisfying (12.5)
with `α_k` the marginal of `μ`. -/
theorem tsum_transitionProb_eq_one {i j : S} {x : E}
    (hx : μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) ≠ 0) :
    ∑' y, transitionProb μ i j x y = 1 := by
  set A := (fun σ : S → E ↦ σ i) ⁻¹' {x} with hA
  have hUnion : A = ⋃ y : E, A ∩ (fun σ : S → E ↦ σ j) ⁻¹' {y} := by
    ext σ; simp [hA]
  have hdisj : Pairwise (Function.onFun Disjoint fun y : E ↦ A ∩ (fun σ : S → E ↦ σ j) ⁻¹' {y}) :=
    fun y y' hyy' ↦ Set.disjoint_left.2 (by
      rintro σ ⟨-, hy⟩ ⟨-, hy'⟩; exact hyy' (hy.symm.trans hy'))
  have hsum : μ A = ∑' y, μ (A ∩ (fun σ : S → E ↦ σ j) ⁻¹' {y}) := by
    conv_lhs => rw [hUnion]
    exact measure_iUnion hdisj fun y ↦ (measurable_pi_apply i (measurableSet_singleton x)).inter
      (measurable_pi_apply j (measurableSet_singleton y))
  simp_rw [transitionProb, ← hA, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, ← hsum, ENNReal.mul_inv_cancel hx (measure_ne_top μ A)]

end TransitionProbSwap

/-! ## Comment (12.3)(2): equation (12.4)

Georgii states (12.4) as `μ(σ_Λ = ζ) = α_k(ζ_k) ∏_{ij ∈ B̄ : i, j ∈ Λ} P_{ij}(ζ_i, ζ_j)`, the
product over the bonds of `Λ` "oriented away from `k`", and remarks that it is "easily seen by
induction on `|Λ|`". Making the orientation of each bond of `Λ` explicit as a *function of `k`
alone* (say, `j ↦` the neighbour of `j` closer to `k`) needs its own well-definedness lemma (that
every vertex of a connected `Λ` other than `k` has such a neighbour, and that it lies in `Λ`); we
do not build that here. Instead we run exactly Georgii's induction on `|Λ|`, via
`SimpleGraph.connected_induction` growing `Λ` outward from `{k}` one boundary vertex at a time
(the same induction principle `boundaryLawWeight_insert_eq`/(12.14) and
`IsMarkovChain.measure_cyl_union_eq_mul_prod` already use for related purposes), and obtain the
orientation *produced by that induction* as an explicit `parent : S → S` map, together with the
factorisation (12.4). At the step that inserts a new vertex `i`, its parent is
`G.anchor Λ' i` -- the unique neighbour of `i` already present -- which is exactly the "neighbour of
`i` closer to `k`", so this `parent` map is the canonical one; we simply do not separately prove
its intrinsic (traversal-independent) characterisation, since the factorisation itself is all
(12.4) asserts. -/

section RootedTransitionWeight

variable {G : SimpleGraph S} [G.LocallyFinite] {μ : Measure (S → E)}

omit [Countable E] in
/-- **Georgii equation (12.4) / Comment (12.3)(2).** For a Markov chain `μ` on a tree, a connected
`Λ` and a root `k ∈ Λ`, there is a "parent" assignment `j ↦ parent j` (for `j ∈ Λ`, pointing to a
neighbour of `j` in `Λ` closer to `k`, produced by growing `Λ` outward from `{k}`) such that
`μ(σ_Λ = ζ) = μ(σ_k = ζ_k) ∏_{j ∈ Λ, j ≠ k} P_{parent j, j}(ζ_{parent j}, ζ_j)` for every `ζ`. -/
theorem IsMarkovChain.exists_parent_measure_cyl_eq (hμ : IsMarkovChain G μ) (hG : G.IsTree)
    {k : S} {Λ : Finset S} (hΛ : (G.induce (Λ : Set S)).Connected) (hk : k ∈ Λ) :
    ∃ parent : S → S, ∀ ζ : S → E,
      μ (cyl Λ ζ) = μ (cyl ({k} : Finset S) ζ)
        * ∏ j ∈ Λ.erase k, transitionProb μ (parent j) j (ζ (parent j)) (ζ j) := by
  refine SimpleGraph.connected_induction (P := fun Λ' ↦ ∃ parent : S → S, ∀ ζ : S → E,
      μ (cyl Λ' ζ) = μ (cyl ({k} : Finset S) ζ)
        * ∏ j ∈ Λ'.erase k, transitionProb μ (parent j) j (ζ (parent j)) (ζ j))
    (connected_induce_singleton k) hΛ (Finset.singleton_subset_iff.2 hk) ⟨id, fun ζ ↦ by simp⟩ ?_
  rintro Λ' hΛ' hkΛ' - i - hi ⟨parent, hparent⟩
  have hkΛ'' : k ∈ Λ' := Finset.singleton_subset_iff.1 hkΛ'
  have hiΛ' : i ∉ Λ' := G.notMem_of_mem_outerBoundary hi
  have hik : i ≠ k := by rintro rfl; exact hiΛ' hkΛ''
  refine ⟨Function.update parent i (G.anchor Λ' i), fun ζ ↦ ?_⟩
  have hpast : (Λ' : Set S) ⊆ G.past (G.anchor Λ' i) i := by
    intro x hx
    rw [Finset.mem_coe] at hx
    refine hG.isAcyclic.mem_past_anchor hΛ' hi (Finset.mem_union_left _ hx) ?_
    rintro rfl
    exact hiΛ' hx
  have hkey := hμ.measure_preimage_inter_cyl (G.adj_anchor hi).symm hpast (G.anchor_mem hi) ζ (ζ i)
  have hLHS : μ (cyl (insert i Λ') ζ)
      = transitionProb μ (G.anchor Λ' i) i (ζ (G.anchor Λ' i)) (ζ i) * μ (cyl Λ' ζ) := by
    rw [cyl_insert_eq_inter]; exact hkey
  have herase : (insert i Λ').erase k = insert i (Λ'.erase k) := Finset.erase_insert_of_ne hik
  have hprod : ∏ j ∈ Λ'.erase k, transitionProb μ (Function.update parent i (G.anchor Λ' i) j) j
      (ζ (Function.update parent i (G.anchor Λ' i) j)) (ζ j)
      = ∏ j ∈ Λ'.erase k, transitionProb μ (parent j) j (ζ (parent j)) (ζ j) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hji : j ≠ i := by rintro rfl; exact hiΛ' (Finset.mem_of_mem_erase hj)
    rw [Function.update_of_ne hji]
  rw [herase, Finset.prod_insert (fun h ↦ hiΛ' (Finset.mem_of_mem_erase h)), hprod,
    Function.update_self, hLHS, hparent ζ]
  ring

end RootedTransitionWeight

/-! ## Georgii Theorem (12.12)(b), uniqueness of the boundary law up to a positive factor

Georgii's proof compares two representations `μ = (12.13)_ℓ = (12.13)_{ℓ'}` at the singleton
volume `Λ = {i}` and a configuration constant at a reference state `a` off one neighbour `j`, where
the (unknown, common) factor coming from `transferWeight {i}` cancels between the `ℓ`- and
`ℓ'`-formulas. -/

section BoundaryLawRatio

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) (hG : G.IsTree) {ℓ ℓ' : S → S → E → ℝ≥0∞}

/-- **Georgii Theorem (12.12)(b), uniqueness of the boundary law up to a positive factor.** If two
boundary laws for the same transfer family `Q` represent the same measure via (12.13), then on
every oriented bond `ji` (`j` a neighbour of `i`), `ℓ_{ji}` is a positive finite multiple of
`ℓ'_{ji}`. -/
theorem IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq (hℓ : IsBoundaryLaw G Q ℓ)
    (hℓ' : IsBoundaryLaw G Q ℓ')
    (heq : boundaryLawMeasure hQ hℓ hG = boundaryLawMeasure hQ hℓ' hG) ⦃i j : S⦄
    (hij : G.Adj i j) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ x, ℓ j i x = c * ℓ' j i x := by
  classical
  set V := volumeLaw G Q hQ.symm ℓ {i} Set.univ with hVdef
  set V' := volumeLaw G Q hQ.symm ℓ' {i} Set.univ with hV'def
  have hV0 : V ≠ 0 := volumeLaw_univ_ne_zero G Q hQ.symm ℓ hQ.pos hℓ.pos {i}
  have hVt : V ≠ ⊤ := hℓ.volumeLaw_singleton_univ_ne_top hQ.symm i
  have hV'0 : V' ≠ 0 := volumeLaw_univ_ne_zero G Q hQ.symm ℓ' hQ.pos hℓ'.pos {i}
  have hV't : V' ≠ ⊤ := hℓ'.volumeLaw_singleton_univ_ne_top hQ.symm i
  -- the singleton-volume weight `boundaryLawWeight {i} ζ`, unfolded via `outerBoundary_singleton`
  -- and `anchor_singleton`, is a product over the neighbours of `i` times `transferWeight {i} ζ`
  have hbw : ∀ (ℓ₀ : S → S → E → ℝ≥0∞) (ζ : S → E),
      boundaryLawWeight G Q hQ.symm ℓ₀ {i} ζ
        = (∏ k ∈ G.neighborFinset i, ℓ₀ k i (ζ k)) * transferWeight G Q hQ.symm {i} ζ := by
    intro ℓ₀ ζ
    rw [boundaryLawWeight, SimpleGraph.outerBoundary_singleton]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by
      rw [SimpleGraph.anchor_singleton (SimpleGraph.outerBoundary_singleton (G := G) i ▸ hk)]
  -- cross-multiplying the two representations of `μ (cyl ({i} ∪ ∂{i}) ζ)`
  have hAeq : ∀ ζ : S → E,
      V' * ∏ k ∈ G.neighborFinset i, ℓ k i (ζ k) = V * ∏ k ∈ G.neighborFinset i, ℓ' k i (ζ k) := by
    intro ζ
    have hval : boundaryLawMeasure hQ hℓ hG (cyl ({i} ∪ G.outerBoundary {i}) ζ)
        = boundaryLawMeasure hQ hℓ' hG (cyl ({i} ∪ G.outerBoundary {i}) ζ) := by rw [heq]
    rw [hℓ.boundaryLawMeasure_cyl hQ hG (connected_induce_singleton i),
      hℓ'.boundaryLawMeasure_cyl hQ hG (connected_induce_singleton i)] at hval
    have hval2 : boundaryLawWeight G Q hQ.symm ℓ {i} ζ / V
        = boundaryLawWeight G Q hQ.symm ℓ' {i} ζ / V' := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm _ V⁻¹, mul_comm _ V'⁻¹]; exact hval
    have hcross := (ENNReal.div_eq_div_iff hV'0 hV't hV0 hVt).1 hval2
    rw [hbw ℓ ζ, hbw ℓ' ζ] at hcross
    have hTpos := (hQ.transferWeight_pos ({i} : Finset S) ζ).ne'
    have hTtop := hQ.transferWeight_ne_top ({i} : Finset S) ζ
    refine (ENNReal.mul_left_inj hTpos hTtop).1 ?_
    rw [mul_assoc, mul_assoc]; exact hcross
  -- specialise to a configuration constant at a reference state `a`, off the neighbour `j`
  have hjmem : j ∈ G.neighborFinset i := (G.mem_neighborFinset i j).2 hij
  obtain ⟨a⟩ : Nonempty E := inferInstance
  set P := ∏ k ∈ (G.neighborFinset i).erase j, ℓ k i a with hPdef
  set P' := ∏ k ∈ (G.neighborFinset i).erase j, ℓ' k i a with hP'def
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦
    (hℓ.pos ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a).ne'
  have hPt : P ≠ ⊤ := ENNReal.prod_ne_top fun k hk ↦
    hℓ.ne_top ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a
  have hP'0 : P' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦
    (hℓ'.pos ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a).ne'
  have hP't : P' ≠ ⊤ := ENNReal.prod_ne_top fun k hk ↦
    hℓ'.ne_top ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a
  have hVP0 : V' * P ≠ 0 := mul_ne_zero hV'0 hP0
  have hVPt : V' * P ≠ ⊤ := ENNReal.mul_ne_top hV't hPt
  refine ⟨(V * P') / (V' * P), ENNReal.div_ne_zero.2 ⟨mul_ne_zero hV0 hP'0, hVPt⟩,
    ENNReal.div_ne_top (ENNReal.mul_ne_top hVt hP't) hVP0, fun x ↦ ?_⟩
  set ζ₀ : S → E := Function.update (fun _ ↦ a) j x with hζ₀
  have hAζ₀ : ∏ k ∈ G.neighborFinset i, ℓ k i (ζ₀ k) = ℓ j i x * P := by
    rw [← Finset.mul_prod_erase _ _ hjmem, hζ₀, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.1 hk).1]
  have hA'ζ₀ : ∏ k ∈ G.neighborFinset i, ℓ' k i (ζ₀ k) = ℓ' j i x * P' := by
    rw [← Finset.mul_prod_erase _ _ hjmem, hζ₀, Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ by
      rw [Function.update_of_ne (Finset.mem_erase.1 hk).1]
  have hmain : ℓ j i x * (V' * P) = ℓ' j i x * (V * P') := by
    have := hAeq ζ₀
    rw [hAζ₀, hA'ζ₀] at this
    calc ℓ j i x * (V' * P) = V' * (ℓ j i x * P) := by ring
      _ = V * (ℓ' j i x * P') := this
      _ = ℓ' j i x * (V * P') := by ring
  have hmain' : V' * P * ℓ j i x = ℓ' j i x * (V * P') := by rw [mul_comm]; exact hmain
  rw [(ENNReal.eq_div_iff hVP0 hVPt).2 hmain', mul_div_assoc, mul_comm]

end BoundaryLawRatio

/-! ## `transitionProb` of `boundaryLawMeasure` equals `boundaryLawTransition`

This intermediate fact is proved (but not exposed) inside `IsBoundaryLaw.isMarkovChain_boundaryLawMeasure`
in `TreeBoundaryLaw.lean`, via a conditional-expectation argument. It is exposed here through a
direct, elementary marginalisation of (12.13) instead, using the public
`IsBoundaryLaw.measure_preimage_inter_cyl_erase` (one-step Markov property in finite volume) and
`measure_cyl_eq_lintegral_lambdaCount` (summing out the free coordinates); this route needs
nothing about conditional expectations. It is the missing link for the "completely homogeneous"
clause of Corollary (12.17): with constant `Q, ℓ`, `boundaryLawTransition` is manifestly
bond-independent, so this identity transports that independence to `transitionProb`. -/

section TransitionProbEqBoundaryLawTransition

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) (hG : G.IsTree) {ℓ : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ)

/-- `μ (σ_j = y, σ_i = x) = P_{ij}(x, y) μ (σ_i = x)`, `μ = boundaryLawMeasure`, `P_{ij} =
boundaryLawTransition Q ℓ i j`. -/
theorem IsBoundaryLaw.measure_preimage_inter_preimage_eq {i j : S} (hij : G.Adj i j) (x y : E) :
    boundaryLawMeasure hQ hℓ hG
        ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ (fun σ : S → E ↦ σ i) ⁻¹' {x})
      = boundaryLawTransition Q ℓ i j x y
        * boundaryLawMeasure hQ hℓ hG ((fun σ : S → E ↦ σ i) ⁻¹' {x}) := by
  classical
  set μ := boundaryLawMeasure hQ hℓ hG with hμdef
  have hjB : j ∈ G.outerBoundary ({i} : Finset S) := by
    rw [SimpleGraph.outerBoundary_singleton]; exact (G.mem_neighborFinset i j).2 hij
  set H : Finset S := (({i} : Finset S) ∪ G.outerBoundary {i}).erase j with hHdef
  set V : Finset S := H.erase i with hVdef
  have hiH : i ∈ H := by
    rw [hHdef]; exact Finset.mem_erase.2 ⟨hij.ne, Finset.mem_union_left _
      (Finset.mem_singleton_self i)⟩
  have hunion : ({i} : Finset S) ∪ V = H := by
    rw [hVdef, Finset.singleton_union, Finset.insert_erase hiH]
  have hdisj : Disjoint ({i} : Finset S) V := by
    rw [hVdef]; exact Finset.disjoint_singleton_left.2 (Finset.notMem_erase i H)
  have hinotV : i ∉ V := by rw [hVdef]; exact Finset.notMem_erase i H
  obtain ⟨a₀⟩ : Nonempty (S → E) := ⟨fun _ ↦ Classical.arbitrary E⟩
  set ηx : S → E := Function.update a₀ i x with hηxdef
  have hηxi : ηx i = x := by rw [hηxdef, Function.update_self]
  have hpreim : (fun σ : S → E ↦ σ i) ⁻¹' {x} = cyl ({i} : Finset S) ηx := by
    rw [hηxdef]; exact preimage_singleton_eq_cyl i x a₀
  have hanc : G.anchor ({i} : Finset S) j = i := SimpleGraph.anchor_singleton hjB
  have hImu : μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) = ∫⁻ ξ, μ (cyl H ξ) ∂(λ₀ V ηx) := by
    rw [hpreim, measure_cyl_eq_lintegral_lambdaCount μ hdisj ηx, hunion]
  have hJmu : μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ (fun σ : S → E ↦ σ i) ⁻¹' {x})
      = ∫⁻ ξ, μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl H ξ) ∂(λ₀ V ηx) := by
    have hrestr := measure_cyl_eq_lintegral_lambdaCount
      (μ.restrict ((fun σ : S → E ↦ σ j) ⁻¹' {y})) hdisj ηx
    rw [hunion] at hrestr
    have hLHS : (μ.restrict ((fun σ : S → E ↦ σ j) ⁻¹' {y})) (cyl ({i} : Finset S) ηx)
        = μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ (fun σ : S → E ↦ σ i) ⁻¹' {x}) := by
      rw [Measure.restrict_apply (measurableSet_cyl _ _), ← hpreim, Set.inter_comm]
    have hRHS : ∀ ξ, (μ.restrict ((fun σ : S → E ↦ σ j) ⁻¹' {y})) (cyl H ξ)
        = μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl H ξ) := fun ξ ↦ by
      rw [Measure.restrict_apply (measurableSet_cyl _ _), Set.inter_comm]
    rw [hLHS] at hrestr
    simp_rw [hRHS] at hrestr
    exact hrestr
  have hFmeas : Measurable fun ξ : S → E ↦ μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl H ξ) := by
    have heq : (fun ξ : S → E ↦ μ ((fun σ : S → E ↦ σ j) ⁻¹' {y} ∩ cyl H ξ))
        = fun ξ ↦ (μ.restrict ((fun σ : S → E ↦ σ j) ⁻¹' {y})) (cyl H ξ) := by
      funext ξ
      rw [Measure.restrict_apply (measurableSet_cyl _ _), Set.inter_comm]
    rw [heq]; exact measurable_measure_cyl _ H
  rw [hJmu, hImu, ← lintegral_const_mul _ (measurable_measure_cyl μ H)]
  refine lintegral_lambdaCount_congr V ηx hFmeas
    (measurable_const.mul (measurable_measure_cyl μ H)) fun ξ hξ ↦ ?_
  have hξi : ξ i = x := by rw [hξ i hinotV, hηxi]
  have hstep := hℓ.measure_preimage_inter_cyl_erase hQ hG (connected_induce_singleton i) hjB ξ y
  rw [hanc, ← hHdef] at hstep
  rw [hstep, hξi]

end TransitionProbEqBoundaryLawTransition

/-! ## Boundary laws that agree on adjacent pairs, or agree up to a global positive factor,
represent the same measure

Two general facts about `boundaryLawMeasure`, used for the surjectivity half of Corollary
(12.17)'s correspondence: `boundaryLawWeight`/`volumeLaw`/`boundaryLawMeasure` only ever evaluate
`ℓ` at pairs `(k, G.anchor Λ k)`, i.e. at *adjacent* pairs, so a boundary law is determined by its
restriction to adjacent pairs; and rescaling every value of `ℓ` by the same positive finite
constant does not change `boundaryLawMeasure`, since the constant cancels between the weight and
its normalising total mass in (12.13). -/

section BoundaryLawMeasureInvariance

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) (hG : G.IsTree) {ℓ ℓ' : S → S → E → ℝ≥0∞} (hℓ : IsBoundaryLaw G Q ℓ)

omit [Nonempty E] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- `IsBoundaryLaw` only depends on `ℓ`'s values at adjacent pairs: transporting along an
agreement on all adjacent pairs preserves it. Used to recognise a constant family as a boundary
law once a general (bond-dependent) boundary law happens to take the same value on every bond, as
in the "surjectivity" half of Corollary (12.17)'s correspondence. -/
theorem IsBoundaryLaw.congr_of_forall_adj (hℓ : IsBoundaryLaw G Q ℓ)
    (hagree : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x = ℓ' i j x) :
    IsBoundaryLaw G Q ℓ' where
  pos i j hij x := by rw [← hagree hij x]; exact hℓ.pos hij x
  ne_top i j hij x := by rw [← hagree hij x]; exact hℓ.ne_top hij x
  consistent i j hij := by
    obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent hij
    refine ⟨c, hc0, hct, fun x ↦ ?_⟩
    rw [← hagree hij x, hc x]
    refine congrArg (c * ·) (Finset.prod_congr rfl fun k hk ↦ ?_)
    have hki : G.Adj k i := ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm
    exact tsum_congr fun y ↦ by rw [hagree hki y]
  mass_ne_top i := by
    have h := hℓ.mass_ne_top i
    have heq : ∀ x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ' k i y * Q k i y x
        = ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x := fun x ↦
      Finset.prod_congr rfl fun k hk ↦ tsum_congr fun y ↦ by
        rw [hagree ((G.mem_neighborFinset i k).1 hk).symm y]
    simp_rw [heq]
    exact h

/-- `boundaryLawMeasure` only depends on `ℓ`'s values at adjacent pairs. -/
theorem IsBoundaryLaw.boundaryLawMeasure_eq_of_forall_adj (hℓ' : IsBoundaryLaw G Q ℓ')
    (hagree : ∀ ⦃i j⦄, G.Adj i j → ∀ x, ℓ i j x = ℓ' i j x) :
    boundaryLawMeasure hQ hℓ hG = boundaryLawMeasure hQ hℓ' hG := by
  have hbw : ∀ (Λ : Finset S) (ζ : S → E),
      boundaryLawWeight G Q hQ.symm ℓ Λ ζ = boundaryLawWeight G Q hQ.symm ℓ' Λ ζ := fun Λ ζ ↦ by
    rw [boundaryLawWeight, boundaryLawWeight]
    congr 1
    exact Finset.prod_congr rfl fun k hk ↦ hagree (G.adj_anchor hk) (ζ k)
  refine hℓ'.eq_boundaryLawMeasure_of_forall_cyl hQ hG fun Λ hΛ ζ ↦ ?_
  rw [hℓ.boundaryLawMeasure_cyl hQ hG hΛ, hbw Λ ζ]
  congr 1
  rw [volumeLaw_univ_eq_lintegral, volumeLaw_univ_eq_lintegral]
  congr 1
  exact lintegral_congr fun ζ' ↦ hbw Λ ζ'

variable {κ : ℝ≥0∞} (hκ0 : κ ≠ 0) (hκt : κ ≠ ⊤)
include hκ0 hκt

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Rescaling every value of a boundary law by the same positive finite constant `κ` is again a
boundary law: the bond-wise constant `c_{ij}` of `IsBoundaryLaw.consistent` picks up a factor
`κ ^ (n - 1)`, `n = |∂i \ {j}|` (written `c_{ij} κ ^ n / κ` to avoid subtracting in `ℕ`). -/
theorem IsBoundaryLaw.div_const (hℓ : IsBoundaryLaw G Q ℓ) :
    IsBoundaryLaw G Q (fun i j x ↦ ℓ i j x / κ) where
  pos i j hij x := ENNReal.div_pos (hℓ.pos hij x).ne' hκt
  ne_top i j hij x := ENNReal.div_ne_top (hℓ.ne_top hij x) hκ0
  consistent i j hij := by
    obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent hij
    set n := ((G.neighborFinset i).erase j).card with hn
    have hterm : ∀ x, ∀ k, ∑' y, ℓ k i y / κ * Q k i y x
        = (∑' y, ℓ k i y * Q k i y x) * κ⁻¹ := fun x k ↦ by
      simp_rw [div_eq_mul_inv, mul_right_comm]
      exact ENNReal.tsum_mul_right
    have hprod : ∀ x, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y / κ * Q k i y x
        = (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * κ⁻¹ ^ n := by
      intro x
      simp_rw [hterm x]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    have hκinv : κ ^ n * κ⁻¹ ^ n = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel hκ0 hκt, one_pow]
    refine ⟨c * κ ^ n / κ, ENNReal.div_ne_zero.2 ⟨mul_ne_zero hc0 (pow_ne_zero n hκ0), hκt⟩,
      ENNReal.div_ne_top (ENNReal.mul_ne_top hct (ENNReal.pow_ne_top hκt)) hκ0, fun x ↦ ?_⟩
    rw [hprod x, div_eq_mul_inv (c * κ ^ n), div_eq_mul_inv]
    calc ℓ i j x * κ⁻¹
        = c * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * κ⁻¹ := by
          rw [hc x]
      _ = c * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * κ⁻¹
          * (κ ^ n * κ⁻¹ ^ n) := by rw [hκinv, mul_one]
      _ = c * κ ^ n * κ⁻¹
          * ((∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * κ⁻¹ ^ n) := by
          ring
  mass_ne_top i := by
    have hterm : ∀ x, ∀ k, ∑' y, ℓ k i y / κ * Q k i y x
        = (∑' y, ℓ k i y * Q k i y x) * κ⁻¹ := fun x k ↦ by
      simp_rw [div_eq_mul_inv, mul_right_comm]
      exact ENNReal.tsum_mul_right
    have heq : ∀ x, ∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y / κ * Q k i y x
        = (∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x) * κ⁻¹ ^ (G.neighborFinset i).card
        := fun x ↦ by
      simp_rw [hterm x]
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    simp_rw [heq]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top (hℓ.mass_ne_top i)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hκ0))

/-- Rescaling every value of a boundary law by the same positive finite constant does not change
`boundaryLawMeasure`: the constant cancels between the weight and its normalising total mass in
(12.13). -/
theorem IsBoundaryLaw.boundaryLawMeasure_div_const_eq
    (hℓ' : IsBoundaryLaw G Q (fun i j x ↦ ℓ i j x / κ)) :
    boundaryLawMeasure hQ hℓ' hG = boundaryLawMeasure hQ hℓ hG := by
  have hbw : ∀ (Λ : Finset S) (ζ' : S → E),
      boundaryLawWeight G Q hQ.symm (fun i j x ↦ ℓ i j x / κ) Λ ζ'
        = boundaryLawWeight G Q hQ.symm ℓ Λ ζ' / κ ^ (G.outerBoundary Λ).card := by
    intro Λ ζ'
    have hprod : ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k) / κ
        = (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k))
          * κ⁻¹ ^ (G.outerBoundary Λ).card := by
      calc ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k) / κ
          = ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k) * κ⁻¹ :=
            Finset.prod_congr rfl fun k _ ↦ div_eq_mul_inv _ _
        _ = (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k))
              * ∏ _k ∈ G.outerBoundary Λ, κ⁻¹ := Finset.prod_mul_distrib
        _ = (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k))
              * κ⁻¹ ^ (G.outerBoundary Λ).card := by rw [Finset.prod_const]
    calc boundaryLawWeight G Q hQ.symm (fun i j x ↦ ℓ i j x / κ) Λ ζ'
        = ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k)) * κ⁻¹ ^ (G.outerBoundary Λ).card)
            * transferWeight G Q hQ.symm Λ ζ' := by rw [boundaryLawWeight, hprod]
      _ = ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k)) * transferWeight G Q hQ.symm Λ ζ')
            * κ⁻¹ ^ (G.outerBoundary Λ).card := by ring
      _ = boundaryLawWeight G Q hQ.symm ℓ Λ ζ' * κ⁻¹ ^ (G.outerBoundary Λ).card := by
          rw [boundaryLawWeight]
      _ = boundaryLawWeight G Q hQ.symm ℓ Λ ζ' / κ ^ (G.outerBoundary Λ).card := by
          rw [div_eq_mul_inv, ← ENNReal.inv_pow]
  have hvw : ∀ Λ : Finset S, volumeLaw G Q hQ.symm (fun i j x ↦ ℓ i j x / κ) Λ Set.univ
      = volumeLaw G Q hQ.symm ℓ Λ Set.univ / κ ^ (G.outerBoundary Λ).card := by
    intro Λ
    rw [volumeLaw_univ_eq_lintegral, volumeLaw_univ_eq_lintegral, div_eq_mul_inv,
      ← lintegral_mul_const _ (measurable_boundaryLawWeight G Q hQ.symm ℓ Λ)]
    refine lintegral_congr fun ζ' ↦ ?_
    rw [hbw Λ ζ', div_eq_mul_inv]
  refine hℓ.eq_boundaryLawMeasure_of_forall_cyl hQ hG fun Λ hΛ ζ ↦ ?_
  rw [hℓ'.boundaryLawMeasure_cyl hQ hG hΛ, hbw Λ ζ, hvw Λ]
  set V := volumeLaw G Q hQ.symm ℓ Λ Set.univ with hVdef
  set W := boundaryLawWeight G Q hQ.symm ℓ Λ ζ with hWdef
  set c := κ ^ (G.outerBoundary Λ).card with hcdef
  have hκn0 : c ≠ 0 := pow_ne_zero _ hκ0
  have hκnt : c ≠ ⊤ := ENNReal.pow_ne_top hκt
  have hV0 : V ≠ 0 := volumeLaw_univ_ne_zero G Q hQ.symm ℓ hQ.pos hℓ.pos Λ
  have hVt : V ≠ ⊤ := hℓ.volumeLaw_univ_ne_top hQ.symm hG.isAcyclic hΛ
  have hVc : (V / c)⁻¹ = V⁻¹ * c := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hV0) (Or.inl hVt), inv_inv]
  rw [hVc, div_eq_mul_inv]
  calc V⁻¹ * c * (W * c⁻¹) = V⁻¹ * W * (c * c⁻¹) := by ring
    _ = V⁻¹ * W * 1 := by rw [ENNReal.mul_inv_cancel hκn0 hκnt]
    _ = V⁻¹ * W := by ring

end BoundaryLawMeasureInvariance

/-! ## Corollary (12.17): completely homogeneous Markov chains on `CT(d)`

Georgii assumes `E` finite throughout Chapter 12 (see the module doc of `TreeBoundaryLaw.lean`);
`[Finite E]` is used here to get `IsTransferFamily`/`IsBoundaryLaw` for a constant `Q₀` from
positivity and symmetry alone (`isTransferFamily_of_finite`, `IsBoundaryLaw.of_finite`), matching
`isBoundaryLaw_const_iff`'s own standing hypotheses. -/

section CompletelyHomogeneous

variable {G : SimpleGraph S}

/-- **Georgii Definition (12.2), "completely homogeneous".** A Markov chain `μ` is completely
homogeneous if it has the *same* transition matrix `P` on every oriented bond, wherever the
marginal is positive (Comment (12.3)(4) shows `transitionProb` is *the* transition matrix there). -/
structure IsCompletelyHomogeneousMarkovChain (G : SimpleGraph S) (μ : Measure (S → E)) : Prop where
  isMarkovChain : IsMarkovChain G μ
  exists_transitionProb_eq : ∃ P : E → E → ℝ≥0∞, ∀ ⦃i j : S⦄, G.Adj i j → ∀ x y : E,
    0 < μ ((fun σ : S → E ↦ σ i) ⁻¹' {x}) → transitionProb μ i j x y = P x y

end CompletelyHomogeneous

section CTChains

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q₀ : E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G (fun _ _ ↦ Q₀)) (hG : G.IsTree) {ℓ0 : E → ℝ≥0∞}
  (hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0))

/-- The boundary-law measure of a *constant* boundary law is a completely homogeneous Markov
chain — the "construction" half of Corollary (12.17)'s correspondence, via (12.13). -/
theorem IsBoundaryLaw.isCompletelyHomogeneousMarkovChain_boundaryLawMeasure :
    IsCompletelyHomogeneousMarkovChain G (boundaryLawMeasure hQ hℓ0 hG) where
  isMarkovChain := hℓ0.isMarkovChain_boundaryLawMeasure hQ hG
  exists_transitionProb_eq :=
    ⟨fun x y ↦ ℓ0 y * Q₀ x y / ∑' y', ℓ0 y' * Q₀ x y', fun i j hij x y hx ↦ by
      have hstep := hℓ0.measure_preimage_inter_preimage_eq hQ hG hij x y
      have hmm := transitionProb_mul_measure_eq (μ := boundaryLawMeasure hQ hℓ0 hG) i j x y
      refine (ENNReal.mul_right_inj hx.ne' (measure_ne_top _ _)).1 ?_
      rw [hmm, Set.inter_comm, hstep, mul_comm]
      rfl⟩

end CTChains

/-! ## Corollary (12.17), surjectivity and uniqueness

The converse half of the correspondence: every completely homogeneous Markov chain `μ ∈ 𝒢(γ^Q)`
comes from a solution of (12.16), and two normalised solutions representing the same `μ` coincide.
Together with `IsBoundaryLaw.isCompletelyHomogeneousMarkovChain_boundaryLawMeasure` above (the
"construction" half) this is Georgii's "one-to-one correspondence". -/

section CTChainsConverse

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q₀ : E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G (fun _ _ ↦ Q₀)) (hG : G.IsTree) {μ : Measure (S → E)}
  [IsProbabilityMeasure μ] (hGibbs : (transferSpecification G hQ).IsGibbsMeasure μ) (a : E)

include hQ hGibbs in
/-- The boundary law `chainBoundaryLaw` of a completely homogeneous Markov chain in `𝒢(γ^Q)` is
constant across bonds: it is built from the single transition matrix `P` of
`IsCompletelyHomogeneousMarkovChain.exists_transitionProb_eq`, evaluated at the reference row `a`.
This is the computational core of the "surjectivity" half of Corollary (12.17)'s correspondence. -/
theorem IsCompletelyHomogeneousMarkovChain.exists_forall_chainBoundaryLaw_eq
    (hcc : IsCompletelyHomogeneousMarkovChain G μ) :
    ∃ ℓ0 : E → ℝ≥0∞,
      ∀ ⦃i j⦄, G.Adj i j → ∀ x, chainBoundaryLaw (fun _ _ ↦ Q₀) μ a i j x = ℓ0 x := by
  obtain ⟨P, hP⟩ := hcc.exists_transitionProb_eq
  refine ⟨fun x ↦ P a x / Q₀ a x, fun i j hij x ↦ ?_⟩
  have ha0 : 0 < μ ((fun σ : S → E ↦ σ j) ⁻¹' {a}) := by
    rw [preimage_singleton_eq_cyl j a (baseConfig (S := S) (E := E))]
    exact measure_cyl_pos_of_isGibbsMeasure hQ hGibbs _ _
  rw [chainBoundaryLaw, hP hij.symm a x ha0]

include hQ hGibbs in
/-- **Georgii Corollary (12.17), surjectivity.** Every completely homogeneous Markov chain
`μ ∈ 𝒢(γ^Q)` is `boundaryLawMeasure` of a boundary law that is constant across bonds and
normalised at the reference state `a`. -/
theorem IsCompletelyHomogeneousMarkovChain.exists_isBoundaryLaw_const_boundaryLawMeasure_eq
    (hne : ∃ i j : S, G.Adj i j) (hcc : IsCompletelyHomogeneousMarkovChain G μ) :
    ∃ ℓ0 : E → ℝ≥0∞, ∃ hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0),
      ℓ0 a = 1 ∧ μ = boundaryLawMeasure hQ hℓ0 hG := by
  obtain ⟨i, j, hij⟩ := hne
  obtain ⟨ℓ0, hagree⟩ := hcc.exists_forall_chainBoundaryLaw_eq (Q₀ := Q₀) hQ hGibbs a
  set hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0) :=
    (hcc.isMarkovChain.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a).congr_of_forall_adj hagree
    with hℓ0def
  have hμeq : μ = boundaryLawMeasure hQ hℓ0 hG := by
    rw [hcc.isMarkovChain.eq_boundaryLawMeasure hQ hGibbs hG a]
    exact (hcc.isMarkovChain.isBoundaryLaw_chainBoundaryLaw hQ hGibbs hG a)
      |>.boundaryLawMeasure_eq_of_forall_adj hQ hG hℓ0 hagree
  have hκ0 : ℓ0 a ≠ 0 := (hℓ0.pos hij a).ne'
  have hκt : ℓ0 a ≠ ⊤ := hℓ0.ne_top hij a
  set ℓ0' : E → ℝ≥0∞ := fun x ↦ ℓ0 x / ℓ0 a with hℓ0'def
  have hℓ0' : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0') := hℓ0.div_const hκ0 hκt
  refine ⟨ℓ0', hℓ0', ?_, ?_⟩
  · rw [hℓ0'def]; exact ENNReal.div_self hκ0 hκt
  · rw [hμeq]
    exact (hℓ0.boundaryLawMeasure_div_const_eq hQ hG hκ0 hκt hℓ0').symm

include hQ hGibbs in
/-- **Georgii Corollary (12.17), surjectivity onto solutions of (12.16).** Every completely
homogeneous Markov chain `μ ∈ 𝒢(γ^Q)` on `CT(d)` (a locally finite tree regular of degree `d + 1`)
is `boundaryLawMeasure` of a boundary law that is constant across bonds, normalised at `a`, and a
solution of (12.16). -/
theorem IsCompletelyHomogeneousMarkovChain.exists_isBoundaryLaw_const_solves_and_eq
    {d : ℕ} (hreg : G.IsRegularOfDegree (d + 1)) (hpos : ∀ x y, 0 < Q₀ x y)
    (hne : ∃ i j : S, G.Adj i j) (hcc : IsCompletelyHomogeneousMarkovChain G μ) :
    ∃ ℓ0 : E → ℝ≥0∞, ∃ hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0),
      ℓ0 a = 1 ∧ μ = boundaryLawMeasure hQ hℓ0 hG ∧
      (∀ x, ℓ0 x = ((∑' y, ℓ0 y * Q₀ y x) / ∑' y, ℓ0 y * Q₀ y a) ^ d) ∧
      ∑' x, (∑' y, ℓ0 y * Q₀ y x) ^ (d + 1) ≠ ⊤ := by
  obtain ⟨ℓ0, hℓ0, ha1, hμeq⟩ :=
    hcc.exists_isBoundaryLaw_const_boundaryLawMeasure_eq (Q₀ := Q₀) hQ hG hGibbs a hne
  obtain ⟨i, j, hij⟩ := hne
  exact ⟨ℓ0, hℓ0, ha1, hμeq,
    (isBoundaryLaw_const_iff G hreg hpos (hℓ0.pos hij) (hℓ0.ne_top hij) ha1
      ⟨i, j, hij⟩).1 hℓ0⟩

/-- **Georgii Corollary (12.17), uniqueness.** Two solutions of (12.16), normalised at the same
reference state `a`, whose `boundaryLawMeasure`s agree are equal. -/
theorem eq_of_isBoundaryLaw_const_boundaryLawMeasure_eq {ℓ0 ℓ0' : E → ℝ≥0∞}
    (hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0))
    (hℓ0' : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0')) (ha0 : ℓ0 a = 1) (ha0' : ℓ0' a = 1)
    (hne : ∃ i j : S, G.Adj i j)
    (heq : boundaryLawMeasure hQ hℓ0 hG = boundaryLawMeasure hQ hℓ0' hG) : ℓ0 = ℓ0' := by
  obtain ⟨i, j, hij⟩ := hne
  obtain ⟨c, -, -, hc⟩ :=
    IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq hQ hG hℓ0 hℓ0' heq hij
  have hc1 : c = 1 := by have := hc a; rw [ha0, ha0', mul_one] at this; exact this.symm
  funext x
  rw [hc x, hc1, one_mul]

include hGibbs in
/-- **Georgii Corollary (12.17), the correspondence, as an iff.** On `CT(d)` with a completely
homogeneous positive Markov specification, `μ ∈ 𝒢(γ^Q)` is a completely homogeneous Markov chain
iff it is `boundaryLawMeasure` of a solution of (12.16) normalised at `a`. Combined with
`eq_of_isBoundaryLaw_const_boundaryLawMeasure_eq` (that solution is unique) and
`IsBoundaryLaw.isCompletelyHomogeneousMarkovChain_boundaryLawMeasure` /
`IsBoundaryLaw.isGibbsMeasure_transferSpecification_boundaryLawMeasure` (every such solution gives
a completely homogeneous chain in `𝒢(γ^Q)`), this is Georgii's "one-to-one correspondence between
the completely homogeneous Markov chains `μ ∈ 𝒢(γ)` and the solutions `ℓ ∈ ]0, ∞[^E` of (12.16)". -/
theorem isCompletelyHomogeneousMarkovChain_iff_exists_isBoundaryLaw_const_solves
    {d : ℕ} (hreg : G.IsRegularOfDegree (d + 1)) (hpos : ∀ x y, 0 < Q₀ x y)
    (hne : ∃ i j : S, G.Adj i j) :
    IsCompletelyHomogeneousMarkovChain G μ ↔
      ∃ ℓ0 : E → ℝ≥0∞, ∃ hℓ0 : IsBoundaryLaw G (fun _ _ ↦ Q₀) (fun _ _ ↦ ℓ0),
        ℓ0 a = 1 ∧ μ = boundaryLawMeasure hQ hℓ0 hG ∧
        (∀ x, ℓ0 x = ((∑' y, ℓ0 y * Q₀ y x) / ∑' y, ℓ0 y * Q₀ y a) ^ d) ∧
        ∑' x, (∑' y, ℓ0 y * Q₀ y x) ^ (d + 1) ≠ ⊤ := by
  refine ⟨fun hcc ↦ hcc.exists_isBoundaryLaw_const_solves_and_eq hQ hG hGibbs a hreg hpos hne,
    fun ⟨ℓ0, hℓ0, _, hμeq, _, _⟩ ↦ ?_⟩
  rw [hμeq]
  exact hℓ0.isCompletelyHomogeneousMarkovChain_boundaryLawMeasure hQ hG

end CTChainsConverse

/-! ## Georgii Theorem (12.6): extreme Gibbs measures of a Markov specification are Markov chains

Georgii's own proof of (12.6) is *not* the (10.21) machinery of `Specification/MarkovIntChains.lean`
transplanted to a tree (that theorem produces explicit transition densities from Georgii's stronger
hypothesis (10.19), via `isssd`-resampling and a Fubini argument needed only because `ℤ`'s proof
does not get to assume `E` countable at that step). Theorem (12.6) itself needs nothing beyond:
tail-triviality of extreme Gibbs measures (`tailTrivial_of_mem_extremePoints_G`, already in the
library, no `Countable S` needed for *this* direction), the backward martingale convergence theorem
(`Integrable.tendsto_ae_condExp_of_antitone`, Lévy's downward theorem, already in
`GibbsMeasure/Mathlib/Probability/Martingale/Convergence.lean`), and the Markov property of `γ` on
connected volumes (`IsMarkovSpecification`, Definition (12.1)). Because Chapter 12 already assumes
`E` countable, the "freezing" step of Georgii's proof needs no resampling and no Fubini argument at
all: fixing the single coordinate `σ_i` collapses a tail-trivial-conditioned function to a function
of `σ_i` alone by nothing more than a countable intersection of a.e. statements
(`exists_ae_eq_single_of_forall_measure_eq_zero_or_one` below), because every function out of a
countable, measurably-singleton space is automatically measurable.

### What is proved

* `IsMarkovSpecification.dependsOn_apply_cyl`, `IsMarkovSpecification.dependsOn_apply`: Definition
  (12.1)'s literal hypothesis (`𝓕_{∂Λ}`-measurability of `γ_Λ(σ_Λ = ζ | ·)`) extends from cylinder
  atoms `cyl Λ ζ` to *every* `A ∈ 𝓕_Λ`, via `measure_cyl_eq_lintegral_lambdaCount` (disintegrating a
  coarser cylinder into the finer ones) for the atom case and `ext_of_generate_finite_of_isProbability
  Measure` (agreeing on the generating π-system `cylindersIn (Λ : Set S)`) for the general case.
* `IsGibbsMeasure.condExp_indicator_ae_eq_toReal_of_isMarkovSpecification`: the basic "Markov ⇒
  conditioning on any `Δ` between `∂Λ` and `Λᶜ` is the same as conditioning on all of `Λᶜ`" fact,
  by the tower property (`condExp_condExp_of_le`) plus the `𝓕_{∂Λ}`-measurability just established.
  This is the general fact used implicitly throughout Georgii's Chapter 12 whenever he writes
  `μ(A | 𝓕_Δ) = γ_Λ(A | ·)` for `Δ ⊇ ∂Λ`.
* `exists_ae_eq_single_of_forall_measure_eq_zero_or_one`: the "freezing" lemma described above.
* `condExp_eq_condExp_of_le_of_condExp_eq`: the elementary "sandwich" fact (two applications of the
  tower property) that closes Georgii's proof: if `μ[f | m₁] =ᵐ μ[f | m₃]` for `m₁ ≤ m₂ ≤ m₃`, then
  already `μ[f | m₁] =ᵐ μ[f | m₂]`.
* `treeExhaustion`: Georgii's `Λ(n)`, built as the connected hull (`SimpleGraph.hull`) of
  `exhaustionVolumes n ∩ G.past root cut`, rooted at `root`; it exhausts `G.past root cut`
  (`treeExhaustion_cofinal`) and, being connected and containing `root`, has outer boundary confined
  to `{cut} ∪ (G.past root cut \ treeExhaustion n)` by `IsAcyclic.mem_past_of_mem_union_outerBoundary`
  (`outerBoundary_treeExhaustion_subset`) — this replaces Georgii's literal metric ball `Δ(n)`, which
  needs no counterpart here since only these two properties of `Λ(n)` are ever used.
* `exists_isMarkovChain_of_mem_extremePoints`: **Theorem (12.6)** itself.

### Hypotheses, exactly

`Countable S` is used only to build `treeExhaustion` (via the global exhaustion
`GibbsMeasure.exhaustionVolumes`, which needs it); it is automatic for a locally finite connected
graph (a routine breadth-first-search argument) but is taken as a standing hypothesis here rather
than derived, to keep this addition to its stated scope. `Nonempty E` is used for
`cylinderEvents_eq_generateFrom_cylindersIn`; Georgii's own standing hypothesis in Chapter 12,
`Countable E` with the discrete σ-algebra, is otherwise all that is needed — no `StandardBorelSpace
E` (Theorem (12.6) is not an existence statement) and no extra countability of `E` beyond what
Chapter 12 already assumes throughout. `G.LocallyFinite` and `G.IsTree` are Georgii's own standing
hypotheses (the local-finiteness/tree structure of Definition preceding (12.1)); the general
Markov-specification lemmas above need only `G.LocallyFinite`.
-/

section GeneralLemmas

end GeneralLemmas

/-! ## Markov specifications: `𝓕_{∂Λ}`-measurability extends from cylinder atoms

Definition (12.1) is stated for the cylinder atoms `cyl Λ ζ` only; the general fact used
throughout §12.1 (whenever Georgii writes `μ(A | 𝓕_Δ) = γ_Λ(A | ·)`, `Δ ⊇ ∂Λ`) needs it for
*every* `A ∈ 𝓕_Λ`. Both lemmas need only `G.LocallyFinite`, not `G.IsTree`. -/

section MarkovSpecificationGeneral

variable {G : SimpleGraph S} [G.LocallyFinite] {γ : Specification S E}

/-- `IsMarkovSpecification` extends from the cylinder atom `cyl Λ ζ` to the cylinder `cyl W ζ` of
any sub-volume `W ⊆ Λ`: disintegrate the coarser cylinder into the finer ones over the extra
coordinates `Λ ∖ W` (`measure_cyl_eq_lintegral_lambdaCount`), where the two kernel values already
agree by hypothesis. -/
theorem IsMarkovSpecification.dependsOn_apply_cyl (hγM : IsMarkovSpecification G γ)
    (Λ W : Finset S) (hW : W ⊆ Λ) (ζ : S → E) :
    DependsOn (fun ω ↦ γ Λ ω (cyl W ζ)) (G.outerBoundary Λ : Set S) := by
  intro ω ω' hωω'
  change γ Λ ω (cyl W ζ) = γ Λ ω' (cyl W ζ)
  have hdisj : Disjoint W (Λ \ W) := Finset.disjoint_sdiff
  have hUW : W ∪ (Λ \ W) = Λ := Finset.union_sdiff_of_subset hW
  have h1 := measure_cyl_eq_lintegral_lambdaCount (γ Λ ω) hdisj ζ
  have h2 := measure_cyl_eq_lintegral_lambdaCount (γ Λ ω') hdisj ζ
  rw [hUW] at h1 h2
  rw [h1, h2]
  exact lintegral_congr fun ξ ↦ (hγM Λ ξ).dependsOn_of_cylinderEvents hωω'

variable [Nonempty E]

/-- `IsMarkovSpecification` extends from cylinder atoms to *every* `A ∈ 𝓕_Λ`: the trimmed kernel
values `(γ Λ ω).trim`, `(γ Λ ω').trim` at `𝓕_Λ` are probability measures agreeing on the
generating π-system `cylindersIn (Λ : Set S)` (by `dependsOn_apply_cyl`), hence equal
(`ext_of_generate_finite_of_isProbabilityMeasure`). -/
theorem IsMarkovSpecification.dependsOn_apply (hγM : IsMarkovSpecification G γ) (Λ : Finset S)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (Λ : Set S)] A) :
    DependsOn (fun ω ↦ γ Λ ω A) (G.outerBoundary Λ : Set S) := by
  intro ω ω' hωω'
  have hle : cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) ≤ MeasurableSpace.pi :=
    cylinderEvents_le_pi
  have hp : IsProbabilityMeasure ((γ Λ ω).trim hle) :=
    ⟨by rw [trim_measurableSet_eq hle MeasurableSet.univ, measure_univ]⟩
  have hp' : IsProbabilityMeasure ((γ Λ ω').trim hle) :=
    ⟨by rw [trim_measurableSet_eq hle MeasurableSet.univ, measure_univ]⟩
  have heq : (γ Λ ω).trim hle = (γ Λ ω').trim hle := by
    have := hp
    have := hp'
    refine MeasureTheory.Measure.ext_of_generate_finite_of_isProbabilityMeasure
      (cylindersIn (E := E) (Λ : Set S)) (cylinderEvents_eq_generateFrom_cylindersIn (Λ : Set S))
      (isPiSystem_cylindersIn (Λ : Set S)) fun B hB ↦ ?_
    obtain ⟨W, ζ, hW, rfl⟩ := hB
    rw [trim_measurableSet_eq hle (measurableSet_cylinderEvents_cyl hW ζ),
      trim_measurableSet_eq hle (measurableSet_cylinderEvents_cyl hW ζ)]
    exact IsMarkovSpecification.dependsOn_apply_cyl hγM Λ W (Finset.coe_subset.1 hW) ζ hωω'
  calc γ Λ ω A = (γ Λ ω).trim hle A := (trim_measurableSet_eq hle hA).symm
    _ = (γ Λ ω').trim hle A := by rw [heq]
    _ = γ Λ ω' A := trim_measurableSet_eq hle hA

/-- **The basic fact behind Georgii's Chapter 12 whenever he writes `μ(A | 𝓕_Δ) = γ_Λ(A | ·)`,
`Δ ⊇ ∂Λ`.** For a Markov specification `γ`, a Gibbs measure `μ`, a finite volume `Λ`, a set `Δ`
with `∂Λ ⊆ Δ ⊆ Λᶜ`, and an event `A` local to `Λ`: conditioning `μ` on `Δ` gives the same result
as conditioning on all of `Λᶜ`, namely `γ_Λ(A | ·)`. Proof: `γ_Λ(A | ·)` is already `𝓕_Δ`-measurable
(`IsMarkovSpecification.dependsOn_apply`, since `∂Λ ⊆ Δ`), so conditioning the DLR equation
`μ(A | 𝓕_{Λᶜ}) = γ_Λ(A | ·)` down from `𝓕_{Λᶜ}` to the smaller `𝓕_Δ` (tower property,
`condExp_condExp_of_le`) does nothing. -/
theorem IsGibbsMeasure.condExp_indicator_ae_eq_toReal_of_isMarkovSpecification
    (hγM : IsMarkovSpecification G γ) {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) {Λ : Finset S} {Δ : Set S}
    (hΔ1 : (G.outerBoundary Λ : Set S) ⊆ Δ) (hΔ2 : Δ ⊆ (Λ : Set S)ᶜ) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (Λ : Set S)] A) :
    μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents Δ] =ᵐ[μ] fun ω ↦ (γ Λ ω A).toReal := by
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hΔle : cylinderEvents (X := fun _ : S ↦ E) Δ ≤ cylinderEvents ((Λ : Set S)ᶜ) :=
    cylinderEvents_mono hΔ2
  have h1 : μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents ((Λ : Set S)ᶜ)]
      =ᵐ[μ] fun ω ↦ (γ Λ ω A).toReal := (hμ Λ).condExp_ae_eq_kernel_apply hA'
  have hInt : Integrable (fun ω ↦ (γ Λ ω A).toReal) μ := integrable_condExp.congr h1
  have hMeasBase : Measurable fun ω ↦ (γ Λ ω A).toReal :=
    ((Kernel.measurable_coe (γ Λ) hA').mono cylinderEvents_le_pi le_rfl).ennreal_toReal
  have hDepends : DependsOn (fun ω ↦ (γ Λ ω A).toReal) (G.outerBoundary Λ : Set S) :=
    fun ω ω' hωω' ↦ congrArg ENNReal.toReal (IsMarkovSpecification.dependsOn_apply hγM Λ hA hωω')
  have hMeasΔ : Measurable[cylinderEvents Δ] fun ω ↦ (γ Λ ω A).toReal :=
    (hMeasBase.cylinderEvents_of_dependsOn hDepends).mono (cylinderEvents_mono hΔ1) le_rfl
  calc μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents Δ]
      =ᵐ[μ] μ[μ[A.indicator (1 : (S → E) → ℝ) | cylinderEvents ((Λ : Set S)ᶜ)] | cylinderEvents Δ] :=
        (condExp_condExp_of_le hΔle cylinderEvents_le_pi).symm
    _ =ᵐ[μ] μ[(fun ω ↦ (γ Λ ω A).toReal) | cylinderEvents Δ] := condExp_congr_ae h1
    _ = fun ω ↦ (γ Λ ω A).toReal :=
        condExp_of_stronglyMeasurable cylinderEvents_le_pi hMeasΔ.stronglyMeasurable hInt

end MarkovSpecificationGeneral

/-! ## The tree-specific exhaustion `treeExhaustion` and Theorem (12.6) -/

section TreeExhaustion

variable [Countable S] (G : SimpleGraph S)

/-- The generating finite subsets of `G.past root cut` used to build `treeExhaustion`: the global
exhaustion `GibbsMeasure.exhaustionVolumes` of `S`, intersected with `G.past root cut`. -/
noncomputable def pastGenerators (root cut : S) (n : ℕ) : Finset S :=
  haveI := Classical.decPred (· ∈ G.past root cut)
  (GibbsMeasure.exhaustionVolumes n).filter (· ∈ G.past root cut)

omit [DecidableEq S] in
theorem mem_pastGenerators_iff {root cut : S} {n : ℕ} {x : S} :
    x ∈ pastGenerators G root cut n ↔
      x ∈ GibbsMeasure.exhaustionVolumes n ∧ x ∈ G.past root cut := by
  classical
  simp [pastGenerators]

/-- **Georgii's `Λ(n)`.** The connected hull, rooted at `root`, of `pastGenerators root cut n`:
a finite connected set containing `root`, staying inside `G.past root cut`
(`treeExhaustion_subset_past`), monotone in `n` (`monotone_treeExhaustion`), and exhausting
`G.past root cut` (`treeExhaustion_cofinal`). -/
noncomputable def treeExhaustion (hGc : G.Connected) (root cut : S) (n : ℕ) : Finset S :=
  SimpleGraph.hull hGc root (pastGenerators G root cut n)

variable {root cut : S} (hGc : G.Connected)

theorem mem_treeExhaustion_self (n : ℕ) : root ∈ treeExhaustion G hGc root cut n :=
  SimpleGraph.mem_hull_self hGc root (pastGenerators G root cut n)

theorem treeExhaustion_subset_past (hG : G.IsAcyclic) (hrc : G.Adj root cut) (n : ℕ) :
    ∀ x ∈ treeExhaustion G hGc root cut n, x ∈ G.past root cut :=
  hG.hull_subset_past hGc hrc fun _k hk ↦ (mem_pastGenerators_iff G).1 hk |>.2

theorem connected_induce_treeExhaustion (n : ℕ) :
    (G.induce ((treeExhaustion G hGc root cut n : Finset S) : Set S)).Connected :=
  SimpleGraph.connected_induce_hull hGc root (pastGenerators G root cut n)

theorem monotone_treeExhaustion : Monotone (treeExhaustion G hGc root cut) := by
  intro m n hmn
  refine SimpleGraph.hull_mono hGc root fun x hx ↦ ?_
  obtain ⟨hx1, hx2⟩ := (mem_pastGenerators_iff G).1 hx
  exact (mem_pastGenerators_iff G).2 ⟨GibbsMeasure.exhaustionVolumes_monotone hmn hx1, hx2⟩

/-- `treeExhaustion` exhausts `G.past root cut`: every finite `Λ₀` is eventually contained, once
restricted to `G.past root cut`. -/
theorem treeExhaustion_cofinal (Λ₀ : Finset S) :
    ∃ n, ∀ x ∈ Λ₀, x ∈ G.past root cut → x ∈ treeExhaustion G hGc root cut n := by
  obtain ⟨n, hn⟩ := GibbsMeasure.exhaustionVolumes_cofinal (S := S) Λ₀
  refine ⟨n, fun x hxΛ₀ hxpast ↦ ?_⟩
  exact SimpleGraph.subset_hull hGc root (pastGenerators G root cut n)
    ((mem_pastGenerators_iff G).2 ⟨hn hxΛ₀, hxpast⟩)

end TreeExhaustion

omit [DecidableEq S] in
/-- On any graph, the two "sides" `G.past j i` and `G.past i j` of an oriented pair are disjoint:
`x ∈ G.past j i` means `dist x i = dist x j + 1`, while `x ∈ G.past i j` means
`dist x j = dist x i + 1`; both together force `dist x i = dist x i + 2`. Purely arithmetic, no
tree structure needed. -/
theorem notMem_past_of_mem_past_swap {G : SimpleGraph S} {i j x : S} (hx : x ∈ G.past j i) :
    x ∉ G.past i j := by
  intro hx'
  rw [SimpleGraph.mem_past] at hx hx'
  omega

section OuterBoundaryTreeExhaustion

variable [Countable S] (G : SimpleGraph S) [G.LocallyFinite] (hGc : G.Connected) {root cut : S}

/-- **Georgii's boundary control on `Λ(n)`.** The outer boundary of `treeExhaustion` is confined
to `{cut} ∪ (G.past root cut \ treeExhaustion n)`: this replaces the metric-ball argument Georgii
uses for his literal `Δ(n)`, since only this containment (together with `treeExhaustion_cofinal`)
is used in the proof of Theorem (12.6). -/
theorem outerBoundary_treeExhaustion_subset (hG : G.IsAcyclic) (hrc : G.Adj root cut) (n : ℕ) :
    (G.outerBoundary (treeExhaustion G hGc root cut n) : Set S)
      ⊆ ({cut} : Set S) ∪ (G.past root cut \ (treeExhaustion G hGc root cut n : Set S)) := by
  intro k hk
  by_cases hkc : k = cut
  · exact Or.inl hkc
  · refine Or.inr ⟨hG.mem_past_of_mem_union_outerBoundary hrc
      (connected_induce_treeExhaustion G hGc n) (mem_treeExhaustion_self G hGc n)
      (treeExhaustion_subset_past G hGc hG hrc n) (Finset.mem_union_right _ hk) hkc,
      G.notMem_of_mem_outerBoundary hk⟩

end OuterBoundaryTreeExhaustion

section TheoremTwelvePointSix

/-- **Georgii, Theorem (12.6).** Every extreme Gibbs measure of a Markov specification `γ` on a
locally finite tree is a Markov chain (Definition (12.2)). Mirrors Georgii's own proof (not the
(10.21)/`Specification.MarkovIntChains` machinery, see the module doc above): freeze the parent
coordinate `σ_i` using tail-triviality along the past of the oriented bond `ij`, identify both
resulting limits with `lim_n γ_{Λ(n)}(σ_j = y | ·)` via Lévy's downward theorem, and close with the
elementary "sandwich" property of conditional expectation. -/
theorem exists_isMarkovChain_of_mem_extremePoints [Countable S] {G : SimpleGraph S}
    [G.LocallyFinite] (hGT : G.IsTree) {γ : Specification S E} (hγM : IsMarkovSpecification G γ)
    {μ : Measure (S → E)} (hμ : μ ∈ (GibbsMeasure.G (γ := γ)).extremePoints ℝ≥0∞) :
    IsMarkovChain G μ := by
  have hμIP : IsProbabilityMeasure μ := hμ.1.1
  have hμG : γ.IsGibbsMeasure μ := hμ.1.2
  refine ⟨hμIP, fun i j hij y ↦ ?_⟩
  have : Nonempty E := ⟨y⟩
  set Λn : ℕ → Finset S := treeExhaustion G hGT.connected j i with hΛndef
  set T : ℕ → Set S := fun n ↦ (G.past j i : Set S) \ (Λn n : Set S) with hTdef
  set A : Set (S → E) := (fun σ : S → E ↦ σ j) ⁻¹' {y} with hAdef
  set f : (S → E) → ℝ := A.indicator (1 : (S → E) → ℝ) with hfdef
  have hA' : MeasurableSet A := measurable_pi_apply j (measurableSet_singleton y)
  have hAcyl : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ({j} : Set S)] A :=
    measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Set.mem_singleton j)
      (measurableSet_singleton y)
  have hjΛn : ∀ n, j ∈ Λn n := fun n ↦ mem_treeExhaustion_self G hGT.connected n
  have hAΛn : ∀ n, MeasurableSet[cylinderEvents (Λn n : Set S)] A := fun n ↦
    cylinderEvents_mono (Set.singleton_subset_iff.2 (hjΛn n)) A hAcyl
  have hΛnPast : ∀ n, ∀ x ∈ Λn n, x ∈ G.past j i :=
    fun n ↦ treeExhaustion_subset_past G hGT.connected hGT.isAcyclic hij.symm n
  have hiNotPastji : i ∉ G.past j i := SimpleGraph.notMem_past_self j i
  have hiNotinΛn : ∀ n, i ∉ Λn n := fun n hin ↦ hiNotPastji (hΛnPast n i hin)
  have hiNotinT : ∀ n, i ∉ T n := fun n hin ↦ hiNotPastji hin.1
  have hΛnMono : Monotone Λn := monotone_treeExhaustion G hGT.connected
  have hTAnti : Antitone T := fun m n hmn ↦
    Set.sdiff_subset_sdiff_right (Finset.coe_subset.2 (hΛnMono hmn))
  have houterSubset : ∀ n, (G.outerBoundary (Λn n) : Set S) ⊆ ({i} : Set S) ∪ T n :=
    fun n ↦ outerBoundary_treeExhaustion_subset G hGT.connected hGT.isAcyclic hij.symm n
  have hΛnComplSubset : ∀ n, ({i} : Set S) ∪ T n ⊆ (Λn n : Set S)ᶜ := by
    intro n x hx
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hiNotinΛn n
    · exact hx.2
  have hPastIJSubsetCompl : ∀ n, (G.past i j : Set S) ⊆ (Λn n : Set S)ᶜ := by
    intro n x hx hx'
    exact notMem_past_of_mem_past_swap (hΛnPast n x hx') hx
  have hTle : (⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)) ≤ tailSigmaAlgebra S E := by
    refine le_iInf fun Λ₀ ↦ ?_
    obtain ⟨n, hn⟩ := treeExhaustion_cofinal G hGT.connected Λ₀
    refine le_trans (iInf_le _ n) (cylinderEvents_mono ?_)
    intro x hx
    simp only [Set.mem_compl_iff, Finset.mem_coe]
    intro hxΛ₀
    exact hx.2 (hn x hxΛ₀ hx.1)
  have htrivT : ∀ B, MeasurableSet[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)] B →
      μ B = 0 ∨ μ B = 1 := fun B hB ↦ tailTrivial_of_mem_extremePoints_G hμ B (hTle B hB)
  have hIntf : Integrable f μ := (integrable_const (1 : ℝ)).indicator hA'
  -- **The freezing step**: `μ[f | cylinderEvents {i}] =ᵐ μ[f | ⨅ n, cylinderEvents ({i} ∪ T n)]`.
  set g : (S → E) → ℝ :=
    μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)] with hgdef
  have hgmeas : Measurable[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)] g :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨q, hqmeas, hqae⟩ :=
    exists_ae_eq_single_of_forall_measure_eq_zero_or_one hiNotinT htrivT hgmeas
  have hqmeasξ : Measurable[cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)]
      (fun σ ↦ q (σ i)) :=
    (hqmeas.comp (measurable_pi_apply i)).cylinderEvents_of_dependsOn
      fun ω ω' hωω' ↦ congrArg q (hωω' i (Set.mem_singleton i))
  have hcyl_le_H : cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)
      ≤ ⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n) :=
    le_iInf fun n ↦ cylinderEvents_mono Set.subset_union_left
  have hHlepi : (⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n))
      ≤ MeasurableSpace.pi := (iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi
  have hqintegrable : Integrable (fun σ ↦ q (σ i)) μ := integrable_condExp.congr hqae
  have hEQ1 : μ[f | cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)] =ᵐ[μ] g := by
    calc μ[f | cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)]
        =ᵐ[μ] μ[g | cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)] := by
          rw [hgdef]; exact (condExp_condExp_of_le hcyl_le_H hHlepi).symm
      _ =ᵐ[μ] μ[(fun σ ↦ q (σ i)) | cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)] :=
          condExp_congr_ae hqae
      _ = fun σ ↦ q (σ i) := condExp_of_stronglyMeasurable cylinderEvents_le_pi
          hqmeasξ.stronglyMeasurable hqintegrable
      _ =ᵐ[μ] g := hqae.symm
  -- **Comparing the two limits of `n ↦ γ_{Λ(n)}(A | ·)`** via Lévy's downward theorem.
  have hAntiΛ : Antitone (fun n ↦ cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ)) :=
    fun m n hmn ↦
      cylinderEvents_mono (Set.compl_subset_compl.2 (Finset.coe_subset.2 (hΛnMono hmn)))
  have hAntiT : Antitone (fun n ↦ cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)) :=
    fun m n hmn ↦ cylinderEvents_mono (Set.union_subset_union_right _ (hTAnti hmn))
  have hTendstoΛ := hIntf.tendsto_ae_condExp_of_antitone hAntiΛ (fun _ ↦ cylinderEvents_le_pi)
  have hTendstoT := hIntf.tendsto_ae_condExp_of_antitone hAntiT (fun _ ↦ cylinderEvents_le_pi)
  have hEqΛ : ∀ n, μ[f | cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ)]
      =ᵐ[μ] fun ω ↦ (γ (Λn n) ω A).toReal := fun n ↦ (hμG (Λn n)).condExp_ae_eq_kernel_apply hA'
  have hEqT : ∀ n, μ[f | cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)]
      =ᵐ[μ] fun ω ↦ (γ (Λn n) ω A).toReal := fun n ↦
    IsGibbsMeasure.condExp_indicator_ae_eq_toReal_of_isMarkovSpecification hγM hμG
      (houterSubset n) (hΛnComplSubset n) (hAΛn n)
  have hEQ4 : μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)]
      =ᵐ[μ] μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ)] := by
    filter_upwards [hTendstoΛ, hTendstoT, ae_all_iff.2 hEqΛ, ae_all_iff.2 hEqT]
      with ω h1 h2 h3 h4
    have e1 : Tendsto (fun n ↦ (γ (Λn n) ω A).toReal) atTop
        (𝓝 (μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ)] ω)) :=
      h1.congr fun n ↦ h3 n
    have e2 : Tendsto (fun n ↦ (γ (Λn n) ω A).toReal) atTop
        (𝓝 (μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) (({i} : Set S) ∪ T n)] ω)) :=
      h2.congr fun n ↦ h4 n
    exact tendsto_nhds_unique e2 e1
  have hEQ5 : μ[f | cylinderEvents (X := fun _ : S ↦ E) ({i} : Set S)]
      =ᵐ[μ] μ[f | ⨅ n, cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ)] := hEQ1.trans hEQ4
  -- **The sandwich step**, closing the proof.
  have hiInPastij : ({i} : Set S) ⊆ (G.past i j : Set S) :=
    Set.singleton_subset_iff.2 (SimpleGraph.mem_past_self_of_adj hij)
  have hpastij_le : cylinderEvents (X := fun _ : S ↦ E) (G.past i j : Set S)
      ≤ ⨅ n, cylinderEvents (X := fun _ : S ↦ E) ((Λn n : Set S)ᶜ) :=
    le_iInf fun n ↦ cylinderEvents_mono (hPastIJSubsetCompl n)
  exact (MeasureTheory.condExp_eq_condExp_of_le_of_condExp_eq (cylinderEvents_mono hiInPastij)
    hpastij_le ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) hEQ5).symm

end TheoremTwelvePointSix

/-! ## General lemma: the singleton-volume weight, for any `ℓ`

Reusable form of the `hbw` step inside `IsBoundaryLaw.exists_const_mul_eq_of_boundaryLawMeasure_eq`
above: it needs no `IsBoundaryLaw` hypothesis at all, only `G.outerBoundary {i} =
G.neighborFinset i` and `G.anchor {i} k = i`. Intended home, once upstreamed: next to
`boundaryLawWeight` in `GibbsMeasure/Model/TreeBoundaryLaw.lean`. (Left duplicated, rather than
factored out of `exists_const_mul_eq_of_boundaryLawMeasure_eq`, to avoid touching that
already-compiling proof; see the report for this note.) -/

section SingletonBoundaryLawWeight

variable {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem boundaryLawWeight_singleton_eq (hs : ∀ i j x y, Q i j x y = Q j i y x)
    (ℓ' : S → S → E → ℝ≥0∞) (i : S) (ζ : S → E) :
    boundaryLawWeight G Q hs ℓ' {i} ζ
      = (∏ k ∈ G.neighborFinset i, ℓ' k i (ζ k)) * transferWeight G Q hs {i} ζ := by
  rw [boundaryLawWeight, SimpleGraph.outerBoundary_singleton]
  congr 1
  exact Finset.prod_congr rfl fun k hk ↦ by
    rw [SimpleGraph.anchor_singleton (SimpleGraph.outerBoundary_singleton (G := G) i ▸ hk)]

end SingletonBoundaryLawWeight

/-! ## General lemmas: per-bond normalisation of a boundary law

Georgii's remark preceding Corollary (12.17) ("It is sometimes useful ... to introduce a
normalization ... We will say that a boundary law is normalized at a reference state `a` if
`ℓ_{ij}(a) = 1`") is used below in the proof of Corollary (12.18): *every* boundary law can be
replaced by one representing the *same* measure and normalised at `a`, simply by dividing each
`ℓ_{ij}` by its own value `ℓ_{ij}(a)` (positive and finite, by `IsBoundaryLaw.pos`/`ne_top`). This
generalises `IsBoundaryLaw.div_const` / `IsBoundaryLaw.boundaryLawMeasure_div_const_eq` above
(which rescale every bond by the *same* global constant `κ`) to a per-bond constant `ℓ_{ij}(a)`.
Intended home, once upstreamed: next to those two lemmas in
`GibbsMeasure/Model/TreeBoundaryLaw.lean`. -/

section NormalizeBoundaryLaw

variable [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite] {Q : S → S → E → E → ℝ≥0∞}
  (hQ : IsTransferFamily G Q) (hG : G.IsTree) {ℓ : S → S → E → ℝ≥0∞}

/-- Rescaling a boundary law bond-by-bond by its own value at a reference state `a`. -/
def normalizeBoundaryLaw (ℓ : S → S → E → ℝ≥0∞) (a : E) : S → S → E → ℝ≥0∞ :=
  fun i j x ↦ ℓ i j x / ℓ i j a

omit [Nonempty E] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The rescaled family is again a boundary law: the per-bond constant `c_{ij}` of
`IsBoundaryLaw.consistent` picks up the finite factor `(∏_{k ∈ ∂i∖{j}} ℓ_{ki}(a)) / ℓ_{ij}(a)`. -/
theorem IsBoundaryLaw.isBoundaryLaw_normalizeAt (hℓ : IsBoundaryLaw G Q ℓ) (a : E) :
    IsBoundaryLaw G Q (normalizeBoundaryLaw ℓ a) where
  pos i j hij x := ENNReal.div_pos (hℓ.pos hij x).ne' (hℓ.ne_top hij a)
  ne_top i j hij x := ENNReal.div_ne_top (hℓ.ne_top hij x) (hℓ.pos hij a).ne'
  consistent i j hij := by
    obtain ⟨c, hc0, hct, hc⟩ := hℓ.consistent hij
    have hterm : ∀ (x : E) (k : S), ∑' y, normalizeBoundaryLaw ℓ a k i y * Q k i y x
        = (∑' y, ℓ k i y * Q k i y x) / ℓ k i a := fun x k ↦ by
      simp_rw [normalizeBoundaryLaw, div_eq_mul_inv, mul_right_comm]
      exact ENNReal.tsum_mul_right
    set K := ∏ k ∈ (G.neighborFinset i).erase j, ℓ k i a with hKdef
    have hK0 : K ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦
      (hℓ.pos ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a).ne'
    have hKt : K ≠ ⊤ := ENNReal.prod_ne_top fun k hk ↦
      hℓ.ne_top ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a
    have hprod : ∀ x, ∏ k ∈ (G.neighborFinset i).erase j, ∑' y,
        normalizeBoundaryLaw ℓ a k i y * Q k i y x
        = (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) / K := by
      intro x
      simp_rw [hterm x]
      exact ENNReal.prod_div_distrib_of_ne_top fun k hk ↦
        hℓ.ne_top ((G.mem_neighborFinset i k).1 (Finset.mem_of_mem_erase hk)).symm a
    have hija0 : ℓ i j a ≠ 0 := (hℓ.pos hij a).ne'
    have hijat : ℓ i j a ≠ ⊤ := hℓ.ne_top hij a
    refine ⟨c * K / ℓ i j a, ENNReal.div_ne_zero.2 ⟨mul_ne_zero hc0 hK0, hijat⟩,
      ENNReal.div_ne_top (ENNReal.mul_ne_top hct hKt) hija0, fun x ↦ ?_⟩
    rw [hprod x, normalizeBoundaryLaw, div_eq_mul_inv (c * K), div_eq_mul_inv]
    calc ℓ i j x * (ℓ i j a)⁻¹
        = c * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x)
            * (ℓ i j a)⁻¹ := by rw [hc x]
      _ = c * (∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * (ℓ i j a)⁻¹
          * (K * K⁻¹) := by rw [ENNReal.mul_inv_cancel hK0 hKt, mul_one]
      _ = c * K * (ℓ i j a)⁻¹
          * ((∏ k ∈ (G.neighborFinset i).erase j, ∑' y, ℓ k i y * Q k i y x) * K⁻¹) := by ring
  mass_ne_top i := by
    have hterm : ∀ (x : E) (k : S), ∑' y, normalizeBoundaryLaw ℓ a k i y * Q k i y x
        = (∑' y, ℓ k i y * Q k i y x) / ℓ k i a := fun x k ↦ by
      simp_rw [normalizeBoundaryLaw, div_eq_mul_inv, mul_right_comm]
      exact ENNReal.tsum_mul_right
    set Kfull := ∏ k ∈ G.neighborFinset i, ℓ k i a with hKfulldef
    have hKfull0 : Kfull ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦
      (hℓ.pos ((G.mem_neighborFinset i k).1 hk).symm a).ne'
    have heq : ∀ x, ∏ k ∈ G.neighborFinset i, ∑' y, normalizeBoundaryLaw ℓ a k i y * Q k i y x
        = (∏ k ∈ G.neighborFinset i, ∑' y, ℓ k i y * Q k i y x) / Kfull := fun x ↦ by
      simp_rw [hterm x]
      exact ENNReal.prod_div_distrib_of_ne_top fun k hk ↦
        hℓ.ne_top ((G.mem_neighborFinset i k).1 hk).symm a
    simp_rw [heq, div_eq_mul_inv]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top (hℓ.mass_ne_top i) (ENNReal.inv_ne_top.2 hKfull0)

omit [Nonempty E] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- `normalizeBoundaryLaw` is normalised at `a`: `ℓ_{ij}(a) / ℓ_{ij}(a) = 1`. -/
theorem normalizeBoundaryLaw_apply_self (hℓ : IsBoundaryLaw G Q ℓ) {i j : S} (hij : G.Adj i j)
    (a : E) : normalizeBoundaryLaw ℓ a i j a = 1 :=
  ENNReal.div_self (hℓ.pos hij a).ne' (hℓ.ne_top hij a)

/-- `boundaryLawMeasure` is unchanged by `normalizeBoundaryLaw`: the same computation as
`IsBoundaryLaw.boundaryLawMeasure_div_const_eq` above, with the single global `κ` there replaced by
the `Λ`-dependent (but `ζ`-independent) constant `∏_{k ∈ ∂Λ} ℓ_{k, k_Λ}(a)`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_normalizeAt_eq (hℓ : IsBoundaryLaw G Q ℓ) (a : E)
    (hℓ' : IsBoundaryLaw G Q (normalizeBoundaryLaw ℓ a)) :
    boundaryLawMeasure hQ hℓ' hG = boundaryLawMeasure hQ hℓ hG := by
  have hbw : ∀ (Λ : Finset S) (ζ' : S → E),
      boundaryLawWeight G Q hQ.symm (normalizeBoundaryLaw ℓ a) Λ ζ'
        = boundaryLawWeight G Q hQ.symm ℓ Λ ζ'
          / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a := by
    intro Λ ζ'
    have hprod : ∏ k ∈ G.outerBoundary Λ, normalizeBoundaryLaw ℓ a k (G.anchor Λ k) (ζ' k)
        = (∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k))
          / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a :=
      ENNReal.prod_div_distrib_of_ne_top fun k hk ↦ hℓ.ne_top (G.adj_anchor hk) a
    calc boundaryLawWeight G Q hQ.symm (normalizeBoundaryLaw ℓ a) Λ ζ'
        = ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k))
              / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a)
            * transferWeight G Q hQ.symm Λ ζ' := by rw [boundaryLawWeight, hprod]
      _ = ((∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) (ζ' k)) * transferWeight G Q hQ.symm Λ ζ')
            / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ = boundaryLawWeight G Q hQ.symm ℓ Λ ζ' / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a := by
          rw [boundaryLawWeight]
  have hvw : ∀ Λ : Finset S, volumeLaw G Q hQ.symm (normalizeBoundaryLaw ℓ a) Λ Set.univ
      = volumeLaw G Q hQ.symm ℓ Λ Set.univ / ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a := by
    intro Λ
    rw [volumeLaw_univ_eq_lintegral, volumeLaw_univ_eq_lintegral, div_eq_mul_inv,
      ← lintegral_mul_const _ (measurable_boundaryLawWeight G Q hQ.symm ℓ Λ)]
    refine lintegral_congr fun ζ' ↦ ?_
    rw [hbw Λ ζ', div_eq_mul_inv]
  refine hℓ.eq_boundaryLawMeasure_of_forall_cyl hQ hG fun Λ hΛ ζ ↦ ?_
  rw [hℓ'.boundaryLawMeasure_cyl hQ hG hΛ, hbw Λ ζ, hvw Λ]
  set V := volumeLaw G Q hQ.symm ℓ Λ Set.univ with hVdef
  set W := boundaryLawWeight G Q hQ.symm ℓ Λ ζ with hWdef
  set c := ∏ k ∈ G.outerBoundary Λ, ℓ k (G.anchor Λ k) a with hcdef
  have hcn0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k hk ↦ (hℓ.pos (G.adj_anchor hk) a).ne'
  have hcnt : c ≠ ⊤ := ENNReal.prod_ne_top fun k hk ↦ hℓ.ne_top (G.adj_anchor hk) a
  have hV0 : V ≠ 0 := volumeLaw_univ_ne_zero G Q hQ.symm ℓ hQ.pos hℓ.pos Λ
  have hVt : V ≠ ⊤ := hℓ.volumeLaw_univ_ne_top hQ.symm hG.isAcyclic hΛ
  have hVc : (V / c)⁻¹ = V⁻¹ * c := by
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hV0) (Or.inl hVt), inv_inv]
  rw [hVc, div_eq_mul_inv]
  calc V⁻¹ * c * (W * c⁻¹) = V⁻¹ * W * (c * c⁻¹) := by ring
    _ = V⁻¹ * W * 1 := by rw [ENNReal.mul_inv_cancel hcn0 hcnt]
    _ = V⁻¹ * W := by ring

end NormalizeBoundaryLaw

/-! ## Georgii Corollary (12.18): a non-trivial mixture of distinct Markov chains fails to be one

Georgii states this for `S = 𝒞𝒯(d)` and a *completely homogeneous* positive Markov specification
(a single transfer matrix `Q` on every bond). **Neither hypothesis is used anywhere in the proof
below** — only `G.LocallyFinite`, `G.IsTree`, and positivity/finiteness of a (possibly
bond-dependent) transfer family `Q` via `IsTransferFamily` — so it is proved here at this weaker,
still Georgii-faithful, hypothesis: any locally finite tree and any transfer family. Taking `Q`
constant and `G` regular recovers Georgii's literal statement (Weakest hypotheses, per the project
conventions).

Each `μ n` is represented, via **Theorem (12.12)**, by its own boundary law `ℓ n` for `Q`; Georgii's
own reduction ("we will say a boundary law is normalized at `a` if `ℓ_{ij}(a) = 1`", the remark
preceding Corollary (12.17)) lets us take it normalised at a common reference state `a`
(`IsBoundaryLaw.isBoundaryLaw_normalizeAt` / `IsBoundaryLaw.boundaryLawMeasure_normalizeAt_eq`
above) — this is exactly Georgii's "let ... `{ℓ_{ij}^{(n)}}` be the associated boundary laws for
`γ` which are normalized at some `a`". Georgii's hypothesis `hcor` is that for every oriented bond
`ij` there is some *other* neighbour `k` of `i` at which every `ℓ n` agrees with its own value at
`ji`: `ℓ n k i = ℓ n j i` for all `n`.

Given, for contradiction, that the mixture `μ = ∑ t n • μ n` is itself a Markov chain: it is Gibbs
for `γ := transferSpecification G hQ` (convexity of `𝒢(γ)`, `sum_smul_mem_G`), so by (12.12)(b) it
too has a (normalised) boundary law `ℓ0`. Applying (12.13) at `Λ = {i}` to a configuration constant
at `a` off the two neighbours `j, k` and comparing the mixture's representation with each `μ n`'s
gives, after the volume/transfer-weight normalising factors cancel, weights `w n ≥ 0` (built from
`t n` and the volume-law masses) with `∑ w n = 1` and the identity
`ℓ0 j i x * ℓ0 k i y = ∑ n, w n * ℓ n j i x * ℓ n j i y`. Two specialisations (`y := a`, `x := a`)
turn this into the *linear* identity `ℓ0 j i z = ℓ0 k i z = ∑ n, w n * ℓ n j i z`, and the diagonal
specialisation `x = y = z` into the *quadratic* one
`(∑ n, w n * ℓ n j i z) ^ 2 = ∑ n, w n * (ℓ n j i z) ^ 2`: exactly the equality case of Jensen's
inequality for the strictly convex `t ↦ t ^ 2` (`StrictConvexOn.map_sum_eq_iff_of_nonneg`, fed
`strictConvexOn_pow`), after transporting out of `ℝ≥0∞` via `ENNReal.toReal` (sound since every
value involved is finite: `IsBoundaryLaw.ne_top` for the `ℓ`'s, and the `w n`'s are finite since
`t n ≤ 1` and the volume-law masses are positive and finite). This forces `ℓ n j i z = ℓ m j i z`
for every `n, m` with `w n, w m ≠ 0` (equivalently `t n, t m ≠ 0`, since `w n`'s other factors are
always positive and finite) — for *every* `z` and *every* bond `ji`. Given two indices `m ≠ n` with
`t m, t n ≠ 0` (the "non-trivial mixture" hypothesis), this makes `ℓ m` and `ℓ n` agree on every
adjacent pair, so `boundaryLawMeasure hQ (hℓ n) hG = boundaryLawMeasure hQ (hℓ m) hG`
(`IsBoundaryLaw.boundaryLawMeasure_eq_of_forall_adj` above), i.e. `μ n = μ m`, contradicting
pairwise distinctness. -/

section CorollaryTwelvePointEighteen

variable [Countable S] [Nonempty E] {G : SimpleGraph S} [G.LocallyFinite]
  {Q : S → S → E → E → ℝ≥0∞} (hQ : IsTransferFamily G Q) (hG : G.IsTree)

/-- **Georgii Corollary (12.18)** (generalised, see the section docstring for why: any locally
finite tree, any transfer family, no regularity or homogeneity needed). A finite family
`μ : Fin N → Measure (S → E)` of pairwise distinct measures, each equal to `boundaryLawMeasure` of
its own boundary law `ℓ n` for `Q`, each normalised at a common reference state `a`, such that every
oriented bond `ij` has some *other* neighbour `k` of `i` at which `ℓ n k i = ℓ n j i` for every `n`
— under a non-trivial convex combination (some `t m, t n ≠ 0` with `m ≠ n`), the mixture
`∑ n, t n • μ n` is *not* a Markov chain. -/
theorem not_isMarkovChain_sum_smul_of_forall_adj_exists_boundaryLaw_eq
    {N : ℕ} {t : Fin N → ℝ≥0∞} (ht : ∑ n, t n = 1) {a : E} {μ : Fin N → Measure (S → E)}
    {ℓ : Fin N → S → S → E → ℝ≥0∞} (hℓ : ∀ n, IsBoundaryLaw G Q (ℓ n))
    (hℓa : ∀ n, ∀ ⦃i j⦄, G.Adj i j → ℓ n i j a = 1)
    (hμeq : ∀ n, μ n = boundaryLawMeasure hQ (hℓ n) hG)
    (hμdistinct : Function.Injective μ)
    (hcor : ∀ ⦃i j⦄, G.Adj i j → ∃ k ∈ (G.neighborFinset i).erase j, ∀ n, ℓ n k i = ℓ n j i)
    (htnontrivial : ∃ m n : Fin N, m ≠ n ∧ t m ≠ 0 ∧ t n ≠ 0) :
    ¬ IsMarkovChain G (∑ n, t n • μ n) := by
  intro hMarkovMix
  -- **Convexity of `𝒢(γ)`**: the mixture is Gibbs for `γ := transferSpecification G hQ`.
  have hμGibbs : ∀ n, (transferSpecification G hQ).IsGibbsMeasure (μ n) := fun n ↦
    hμeq n ▸ (hℓ n).isGibbsMeasure_transferSpecification_boundaryLawMeasure hQ hG
  have hμIP : ∀ n, IsProbabilityMeasure (μ n) := fun n ↦
    hμeq n ▸ isProbabilityMeasure_boundaryLawMeasure hQ (hℓ n) hG
  have hμmemG : ∀ n, μ n ∈ MeasureTheory.GibbsMeasure.G (transferSpecification G hQ) := fun n ↦
    (MeasureTheory.GibbsMeasure.G.mem_iff (μ n)).2 ⟨hμIP n, hμGibbs n⟩
  have hmixmemG : (∑ n, t n • μ n) ∈ MeasureTheory.GibbsMeasure.G (transferSpecification G hQ) :=
    MeasureTheory.GibbsMeasure.sum_smul_mem_G hμmemG ht
  obtain ⟨hmixIP, hmixGibbs⟩ :=
    (MeasureTheory.GibbsMeasure.G.mem_iff (∑ n, t n • μ n)).1 hmixmemG
  have := hmixIP
  -- **The mixture's own boundary law**, via (12.12)(b), immediately normalised at `a`.
  set ℓmix0 := chainBoundaryLaw Q (∑ n, t n • μ n) a with hℓmix0def
  have hℓmix0 : IsBoundaryLaw G Q ℓmix0 :=
    hMarkovMix.isBoundaryLaw_chainBoundaryLaw hQ hmixGibbs hG a
  set ℓ0 := normalizeBoundaryLaw ℓmix0 a with hℓ0def
  have hℓ0 : IsBoundaryLaw G Q ℓ0 := hℓmix0.isBoundaryLaw_normalizeAt a
  have hℓ0a : ∀ ⦃p q⦄, G.Adj p q → ℓ0 p q a = 1 := fun p q hpq ↦
    normalizeBoundaryLaw_apply_self hℓmix0 hpq a
  have hμ0eq : (∑ n, t n • μ n) = boundaryLawMeasure hQ hℓ0 hG := by
    rw [hℓmix0.boundaryLawMeasure_normalizeAt_eq hQ hG a hℓ0]
    exact hMarkovMix.eq_boundaryLawMeasure hQ hmixGibbs hG a
  -- **The singleton-volume product collapses** at a configuration constant at `a` off two
  -- neighbours `j, k` of `i`, for any boundary law normalised at `a`.
  have hprodcollapse : ∀ (ℓ' : S → S → E → ℝ≥0∞), (∀ ⦃p q⦄, G.Adj p q → ℓ' p q a = 1) →
      ∀ {i j k : S}, j ∈ G.neighborFinset i → k ∈ (G.neighborFinset i).erase j → ∀ x y : E,
      ∏ m ∈ G.neighborFinset i,
          ℓ' m i (Function.update (Function.update (fun _ ↦ a) k y) j x m)
        = ℓ' j i x * ℓ' k i y := by
    intro ℓ' hℓ'norm i j k hjmem hkmem x y
    have hjk : j ≠ k := (Finset.ne_of_mem_erase hkmem).symm
    set ζ : S → E := Function.update (Function.update (fun _ ↦ a) k y) j x with hζdef
    have hζj : ζ j = x := by rw [hζdef, Function.update_self]
    have hζk : ζ k = y := by rw [hζdef, Function.update_of_ne hjk.symm, Function.update_self]
    rw [← Finset.mul_prod_erase _ _ hjmem, hζj, ← Finset.mul_prod_erase _ _ hkmem, hζk]
    have hrest : ∏ m ∈ ((G.neighborFinset i).erase j).erase k, ℓ' m i (ζ m) = 1 := by
      refine Finset.prod_eq_one fun m hm ↦ ?_
      have hmk : m ≠ k := (Finset.mem_erase.1 hm).1
      have hmj : m ≠ j := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hm)).1
      have hζm : ζ m = a := by rw [hζdef, Function.update_of_ne hmj, Function.update_of_ne hmk]
      rw [hζm]
      exact hℓ'norm ((G.mem_neighborFinset i m).1
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm))).symm
    rw [hrest, mul_one]
  -- **The core comparison**: for every oriented bond `ij`, every `z`, and every `n, m` with
  -- positive weight `t`, `ℓ n j i z = ℓ m j i z`.
  have hbond : ∀ ⦃i j⦄ (_ : G.Adj i j), ∀ n0 m0 : Fin N, t n0 ≠ 0 → t m0 ≠ 0 →
      ∀ z, ℓ n0 j i z = ℓ m0 j i z := by
    intro i j hij n0 m0 htn0 htm0 z
    obtain ⟨k, hkmem, hcorij⟩ := hcor hij
    have hjmem : j ∈ G.neighborFinset i := (G.mem_neighborFinset i j).2 hij
    have hkmem' : k ∈ G.neighborFinset i := Finset.mem_of_mem_erase hkmem
    have hki : G.Adj k i := ((G.mem_neighborFinset i k).1 hkmem').symm
    set V0 := volumeLaw G Q hQ.symm ℓ0 {i} Set.univ with hV0def
    set Vn : Fin N → ℝ≥0∞ := fun n ↦ volumeLaw G Q hQ.symm (ℓ n) {i} Set.univ with hVndef
    have hV00 : V0 ≠ 0 := volumeLaw_univ_ne_zero G Q hQ.symm ℓ0 hQ.pos hℓ0.pos {i}
    have hV0t : V0 ≠ ⊤ := hℓ0.volumeLaw_singleton_univ_ne_top hQ.symm i
    have hVn0 : ∀ n, Vn n ≠ 0 := fun n ↦
      volumeLaw_univ_ne_zero G Q hQ.symm (ℓ n) hQ.pos (hℓ n).pos {i}
    have hVnt : ∀ n, Vn n ≠ ⊤ := fun n ↦ (hℓ n).volumeLaw_singleton_univ_ne_top hQ.symm i
    have hbw0 : ∀ x y, boundaryLawWeight G Q hQ.symm ℓ0 {i}
        (Function.update (Function.update (fun _ ↦ a) k y) j x)
        = (ℓ0 j i x * ℓ0 k i y) * transferWeight G Q hQ.symm {i}
            (Function.update (Function.update (fun _ ↦ a) k y) j x) := fun x y ↦ by
      rw [boundaryLawWeight_singleton_eq hQ.symm ℓ0 i, hprodcollapse ℓ0 hℓ0a hjmem hkmem x y]
    have hbwn : ∀ n x y, boundaryLawWeight G Q hQ.symm (ℓ n) {i}
        (Function.update (Function.update (fun _ ↦ a) k y) j x)
        = (ℓ n j i x * ℓ n j i y) * transferWeight G Q hQ.symm {i}
            (Function.update (Function.update (fun _ ↦ a) k y) j x) := fun n x y ↦ by
      rw [boundaryLawWeight_singleton_eq hQ.symm (ℓ n) i,
        hprodcollapse (ℓ n) (hℓa n) hjmem hkmem x y, congrFun (hcorij n) y]
    have hident : ∀ x y : E, V0⁻¹ * ((ℓ0 j i x * ℓ0 k i y) * transferWeight G Q hQ.symm {i}
          (Function.update (Function.update (fun _ ↦ a) k y) j x))
        = ∑ n, t n * ((Vn n)⁻¹ * ((ℓ n j i x * ℓ n j i y) * transferWeight G Q hQ.symm {i}
            (Function.update (Function.update (fun _ ↦ a) k y) j x))) := by
      intro x y
      set ζ := Function.update (Function.update (fun _ ↦ a) k y) j x with hζdef
      have hbw0ζ : boundaryLawWeight G Q hQ.symm ℓ0 {i} ζ
          = (ℓ0 j i x * ℓ0 k i y) * transferWeight G Q hQ.symm {i} ζ := by
        rw [hζdef]; exact hbw0 x y
      have hbwnζ : ∀ n, boundaryLawWeight G Q hQ.symm (ℓ n) {i} ζ
          = (ℓ n j i x * ℓ n j i y) * transferWeight G Q hQ.symm {i} ζ := fun n ↦ by
        rw [hζdef]; exact hbwn n x y
      have hmix : (∑ n, t n • μ n) (cyl (({i} : Finset S) ∪ G.outerBoundary {i}) ζ)
          = ∑ n, t n * μ n (cyl (({i} : Finset S) ∪ G.outerBoundary {i}) ζ) := by
        rw [Measure.finsetSum_apply]
        exact Finset.sum_congr rfl fun n _ ↦ by rw [Measure.smul_apply, smul_eq_mul]
      rw [hμ0eq, hℓ0.boundaryLawMeasure_cyl hQ hG (connected_induce_singleton i)] at hmix
      have hn : ∀ n, μ n (cyl (({i} : Finset S) ∪ G.outerBoundary {i}) ζ)
          = (Vn n)⁻¹ * boundaryLawWeight G Q hQ.symm (ℓ n) {i} ζ := fun n ↦ by
        rw [hμeq n, (hℓ n).boundaryLawMeasure_cyl hQ hG (connected_induce_singleton i)]
      simp_rw [hn] at hmix
      rw [← hbw0ζ]
      simp_rw [← hbwnζ]
      exact hmix
    have hcancel : ∀ x y, V0⁻¹ * (ℓ0 j i x * ℓ0 k i y)
        = ∑ n, t n * ((Vn n)⁻¹ * (ℓ n j i x * ℓ n j i y)) := by
      intro x y
      set T := transferWeight G Q hQ.symm {i}
        (Function.update (Function.update (fun _ ↦ a) k y) j x) with hTdef
      have hT0 : T ≠ 0 := (hQ.transferWeight_pos ({i} : Finset S) _).ne'
      have hTt : T ≠ ⊤ := hQ.transferWeight_ne_top ({i} : Finset S) _
      refine (ENNReal.mul_left_inj hT0 hTt).1 ?_
      calc V0⁻¹ * (ℓ0 j i x * ℓ0 k i y) * T
          = V0⁻¹ * ((ℓ0 j i x * ℓ0 k i y) * T) := by ring
        _ = ∑ n, t n * ((Vn n)⁻¹ * ((ℓ n j i x * ℓ n j i y) * T)) := hident x y
        _ = (∑ n, t n * ((Vn n)⁻¹ * (ℓ n j i x * ℓ n j i y))) * T := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun n _ ↦ by ring
    set w : Fin N → ℝ≥0∞ := fun n ↦ t n * (Vn n)⁻¹ * V0 with hwdef
    have hMAIN : ∀ x y, ℓ0 j i x * ℓ0 k i y = ∑ n, w n * (ℓ n j i x * ℓ n j i y) := by
      intro x y
      have hV0eq : V0 * (V0⁻¹ * (ℓ0 j i x * ℓ0 k i y)) = ℓ0 j i x * ℓ0 k i y := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hV00 hV0t, one_mul]
      rw [← hV0eq, hcancel x y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ ↦ by rw [hwdef]; ring
    have hℓ0_ji_a : ℓ0 j i a = 1 := hℓ0a hij.symm
    have hℓ0_ki_a : ℓ0 k i a = 1 := hℓ0a hki
    have hℓ_ji_a : ∀ n, ℓ n j i a = 1 := fun n ↦ hℓa n hij.symm
    have hw_sum1 : ∑ n, w n = 1 := by
      have h1 := hMAIN a a
      rw [hℓ0_ji_a, hℓ0_ki_a, mul_one] at h1
      simp_rw [hℓ_ji_a, mul_one] at h1
      exact h1.symm
    have hw_lin : ∀ z, ℓ0 j i z = ∑ n, w n * ℓ n j i z := by
      intro z
      have h2 := hMAIN z a
      rw [hℓ0_ki_a, mul_one] at h2
      simp_rw [hℓ_ji_a, mul_one] at h2
      exact h2
    have hw_link : ∀ z, ℓ0 k i z = ∑ n, w n * ℓ n j i z := by
      intro z
      have h3 := hMAIN a z
      rw [hℓ0_ji_a, one_mul] at h3
      simp_rw [hℓ_ji_a, one_mul] at h3
      exact h3
    have hMAINzz : ∀ z, ℓ0 j i z * ℓ0 k i z = ∑ n, w n * ℓ n j i z ^ 2 := fun z ↦ by
      rw [hMAIN z z]; exact Finset.sum_congr rfl fun n _ ↦ by rw [sq]
    have hjieqki : ∀ z, ℓ0 j i z = ℓ0 k i z := fun z ↦ (hw_lin z).trans (hw_link z).symm
    have hFinalsq : ∀ z, (∑ n, w n * ℓ n j i z) ^ 2 = ∑ n, w n * ℓ n j i z ^ 2 := by
      intro z
      rw [sq, ← hw_lin z, congrArg (ℓ0 j i z * ·) (hjieqki z)]
      exact hMAINzz z
    have htnt : ∀ n, t n ≠ ⊤ := fun n ↦ by
      have hle : t n ≤ 1 := ht ▸ Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ n)
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hwnt : ∀ n, w n ≠ ⊤ := fun n ↦
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (htnt n) (ENNReal.inv_ne_top.2 (hVn0 n))) hV0t
    have hwn0iff : ∀ n, w n ≠ 0 ↔ t n ≠ 0 := fun n ↦ by
      simp only [hwdef, ne_eq, mul_eq_zero, ENNReal.inv_eq_zero, not_or]
      exact ⟨fun h ↦ h.1.1, fun h ↦ ⟨⟨h, hVnt n⟩, hV00⟩⟩
    -- **Transport to `ℝ` and the Jensen equality case.**
    have hLt : (∑ n, w n * ℓ n j i z) ≠ ⊤ := by
      rw [← hw_lin z]; exact hℓ0.ne_top hij.symm z
    have hsumR : (∑ n, w n * ℓ n j i z).toReal
        = ∑ n, (w n).toReal * (ℓ n j i z).toReal := by
      rw [ENNReal.toReal_sum (fun n _ ↦ ENNReal.mul_ne_top (hwnt n) ((hℓ n).ne_top hij.symm z))]
      exact Finset.sum_congr rfl fun n _ ↦ ENNReal.toReal_mul
    have hRsumR : (∑ n, w n * ℓ n j i z ^ 2).toReal
        = ∑ n, (w n).toReal * (ℓ n j i z).toReal ^ 2 := by
      rw [ENNReal.toReal_sum (fun n _ ↦ ENNReal.mul_ne_top (hwnt n)
        (ENNReal.pow_ne_top ((hℓ n).ne_top hij.symm z)))]
      exact Finset.sum_congr rfl fun n _ ↦ by rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
    have hReal : (∑ n, (w n).toReal * (ℓ n j i z).toReal) ^ 2
        = ∑ n, (w n).toReal * (ℓ n j i z).toReal ^ 2 := by
      rw [← hsumR, ← hRsumR, ← ENNReal.toReal_pow, hFinalsq z]
    have hw_sum1R : ∑ n, (w n).toReal = 1 := by
      rw [← ENNReal.toReal_sum (fun n _ ↦ hwnt n), hw_sum1, ENNReal.toReal_one]
    have hJ := (strictConvexOn_pow (n := 2) le_rfl).map_sum_eq_iff_of_nonneg
        (t := (Finset.univ : Finset (Fin N))) (w := fun n ↦ (w n).toReal)
        (p := fun n ↦ (ℓ n j i z).toReal) (fun n _ ↦ ENNReal.toReal_nonneg) hw_sum1R
        (fun n _ ↦ ENNReal.toReal_nonneg)
    simp only [smul_eq_mul] at hJ
    have hwR_ne_zero_iff : ∀ n, (w n).toReal ≠ 0 ↔ w n ≠ 0 := fun n ↦
      not_congr (by rw [ENNReal.toReal_eq_zero_iff]; simp [hwnt n])
    have hpnm := hJ.1 hReal (Finset.mem_univ n0) ((hwR_ne_zero_iff n0).2 ((hwn0iff n0).2 htn0))
      (Finset.mem_univ m0) ((hwR_ne_zero_iff m0).2 ((hwn0iff m0).2 htm0))
    exact (ENNReal.toReal_eq_toReal_iff' ((hℓ n0).ne_top hij.symm z)
      ((hℓ m0).ne_top hij.symm z)).1 hpnm
  -- **Conclusion**: two positively-weighted indices agree everywhere, contradicting distinctness.
  obtain ⟨m0, n0, hmn, htm0, htn0⟩ := htnontrivial
  have hkey : ∀ ⦃p q⦄, G.Adj p q → ∀ z, ℓ n0 p q z = ℓ m0 p q z := fun p q hpq z ↦
    hbond hpq.symm n0 m0 htn0 htm0 z
  have hboundaryEq : boundaryLawMeasure hQ (hℓ n0) hG = boundaryLawMeasure hQ (hℓ m0) hG :=
    (hℓ n0).boundaryLawMeasure_eq_of_forall_adj hQ hG (hℓ m0) hkey
  have hμeqmn : μ n0 = μ m0 := by rw [hμeq n0, hμeq m0, hboundaryEq]
  exact hmn (hμdistinct hμeqmn).symm

end CorollaryTwelvePointEighteen

end MeasureTheory.GibbsMeasure.Tree

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLaw
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Mathlib.Probability.TailTriviality
public import GibbsMeasure.Prereqs.MeasureExt

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
section below for the full account, including exactly which hypotheses are used. Comments
(12.3)(3), (5), (6), and Corollary (12.18) are **not formalised**; see below for exactly why in
each case.

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

## What is not formalised, beyond (12.6)

* **Comments (12.3)(3) and (12.3)(6)** are not formalised: (3) needs a formal notion of a graph
  embedding `ℤ ↪ S` (an embedded bi-infinite geodesic) that does not yet exist anywhere in the tree
  combinatorics files, and (6) needs a `𝒯_Λ`-style "local tail" σ-algebra and its associated
  generated-π-system argument, neither of which exists yet either; both are genuine follow-on
  constructions rather than gaps in the argument given here.
* **Corollary (12.18)** (a non-trivial convex mixture of pairwise distinct Markov chains, whose
  normalised boundary laws agree at every bond in the sense of the corollary's hypothesis, is not a
  Markov chain) is **not formalised**. Two independent things are needed, neither of them a small
  step, and neither present yet:
  1. **Convexity of `𝒢(γ)` is not yet in the project.** Georgii's proof applies (12.12)(b) to the
     mixture `μ = Σ tₙ μₙ` itself, which needs `μ ∈ 𝒢(γ^Q)` — i.e. that a finite convex combination
     of Gibbs measures for the same specification is again a Gibbs measure. This is true and not
     hard (`Specification.IsGibbsMeasure` is the affine condition `μ.bind (γ Λ) = μ`, so it reduces
     to `Measure.bind` being additive and positively homogeneous in its base measure, via
     `lintegral_add_measure`/`lintegral_smul_measure`), but no such lemma — for `Measure.bind`, or
     for `Specification.IsGibbsMeasure` — exists anywhere in `GibbsMeasure/Specification/` today;
     it would need to be built first.
  2. **The quadratic/linear identity and its equality-case argument.** From (12.13) at singleton
     volumes one derives, for the mixture's own normalised boundary law `ℓ`, an identity
     `ℓ_ji(x) ℓ_ji(y) = Σ_n wₙ ℓ_ji⁽ⁿ⁾(x) ℓ_ji⁽ⁿ⁾(y)` with `Σ wₙ = 1`, `wₙ ≥ 0`; setting `x = y = z`
     and comparing with the *linear* identity `ℓ_ji(z) = Σ wₙ ℓ_ji⁽ⁿ⁾(z)` (obtained by setting
     `y = a` instead) forces the discrete-variance identity `Σ_n wₙ ℓ_ji⁽ⁿ⁾(z)² = (Σ_n wₙ
     ℓ_ji⁽ⁿ⁾(z))²`. Unlike Georgii's own route (an explicit sum-of-squares identity, delicate in
     `ℝ≥0∞` since subtraction there is truncated), the clean way to close this step is the
     *equality case of Jensen's inequality* for the strictly convex `x ↦ x²`:
     `StrictConvexOn.map_sum_eq_iff_of_nonneg` (`Mathlib/Analysis/Convex/Jensen.lean`), fed
     `Even.strictConvexOn_pow`/`strictConvexOn_pow` (`Mathlib/Analysis/Convex/SpecificFunctions/
     Deriv.lean`), gives exactly "equal weighted linear and quadratic averages ⇒ equal values on
     the support of `w`" — but only over a field with subtraction (`ℝ`), so the identity must first
     be transported out of `ℝ≥0∞` via `ENNReal.toReal` (sound here since every `ℓ_ji⁽ⁿ⁾(z)` is
     finite, `IsBoundaryLaw.ne_top`). What remains, beyond locating this lemma, is: extracting the
     positive finite constants `cₙ` from the ratios of (12.13)'s normalising `z_{\{i\}}`'s across
     `μ, μ₁, …, μ_N`; using the corollary's hypothesis (`∀ ij, ∃ k ∈ ∂i∖{j}, ℓ_ki⁽ⁿ⁾ = ℓ_ji⁽ⁿ⁾ ∀n`)
     to transport the identity from the bond `ki` where it is derived to the bond `ji` where it is
     needed; and closing the final contradiction (equal boundary laws on every bond ⇒ equal
     measures, `IsBoundaryLaw.eq_boundaryLawMeasure_of_forall_cyl`, against pairwise distinctness).
  Formalising both of these is a substantial independent undertaking — item 1 is a small new
  general lemma, item 2 a proof of comparable size to the (12.12)(b)/(12.17) development above —
  and was not completed in this pass.
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

/-- **The "sandwich" property of conditional expectation.** If the conditional expectations of an
integrable `f` with respect to two nested sub-σ-algebras `m₁ ≤ m₂ ≤ m₃ ≤ m0` agree `μ`-a.e. with
the conditional expectation with respect to the *largest* one `m₃`, then `m₁` and `m₂` already
agree with each other. Two applications of the tower property (`condExp_condExp_of_le`). Intended
home: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`, next to
`condExp_condExp_of_le` itself. -/
theorem _root_.MeasureTheory.condExp_eq_condExp_of_le_of_condExp_eq
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {m₁ m₂ m₃ : MeasurableSpace Ω}
    (h12 : m₁ ≤ m₂) (h23 : m₂ ≤ m₃) (h3 : m₃ ≤ m0) {f : Ω → ℝ}
    (heq : μ[f | m₁] =ᵐ[μ] μ[f | m₃]) : μ[f | m₁] =ᵐ[μ] μ[f | m₂] := by
  have hm2 : m₂ ≤ m0 := h23.trans h3
  calc μ[f | m₁] = μ[μ[f | m₁] | m₂] :=
        (condExp_of_stronglyMeasurable hm2 (stronglyMeasurable_condExp.mono h12)
          integrable_condExp).symm
    _ =ᵐ[μ] μ[μ[f | m₃] | m₂] := condExp_congr_ae heq
    _ =ᵐ[μ] μ[f | m₂] := condExp_condExp_of_le h23 h3

/-- **The "freezing" argument behind Georgii's Theorem (12.6).** If `μ` is trivial on
`⨅ n, cylinderEvents (T n)` for a family `T : ℕ → Set S` of coordinate sets avoiding a fixed site
`i` (`i ∉ T n` for every `n`), then every function measurable for `⨅ n, cylinderEvents ({i} ∪ T
n)` is `μ`-a.e. a function of the single coordinate `σ i`. Unlike the analogous two-coordinate
statement `exists_ae_eq_pair_of_forall_measure_eq_zero_or_one` in
`GibbsMeasure/Specification/MarkovIntChains.lean` (needed there because Georgii's hypothesis
(10.19) genuinely involves both endpoints `σ_{j-1}, σ_j` of a step of `ℤ`), no resampling and no
Fubini argument is needed here: fixing the single coordinate directly produces, for every `x`, an
a.e.-constant function (tail triviality), and the countably many resulting null sets (one per `x
∈ E`, `E` countable) are combined by `Filter.ae_all_iff`. Intended home:
`Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated`, next to
`measurable_cylinderEvents_iff_dependsOn`. -/
theorem _root_.MeasureTheory.exists_ae_eq_single_of_forall_measure_eq_zero_or_one
    {S E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] {i : S} {T : ℕ → Set S} (hi : ∀ n, i ∉ T n)
    (htriv : ∀ A, MeasurableSet[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)] A →
      μ A = 0 ∨ μ A = 1)
    {f : (S → E) → ℝ}
    (hf : Measurable[⨅ n, cylinderEvents (X := fun _ : S ↦ E) ({i} ∪ T n)] f) :
    ∃ q : E → ℝ, Measurable q ∧ f =ᵐ[μ] fun σ ↦ q (σ i) := by
  classical
  have hf' : Measurable f := hf.mono ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) le_rfl
  set q : E → ℝ := fun x ↦ ∫ ω, f (Function.update ω i x) ∂μ with hq_def
  refine ⟨q, measurable_of_countable q, ?_⟩
  have hconst : ∀ x : E, ∀ᵐ ω ∂μ, f (Function.update ω i x) = q x := by
    intro x
    have hshift : Measurable fun ω : S → E ↦ f (Function.update ω i x) :=
      hf'.comp measurable_update_left
    have hmeasT : Measurable[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)]
        fun ω ↦ f (Function.update ω i x) := by
      rw [measurable_iInf_iff_forall]
      intro n
      have hdep : DependsOn f ({i} ∪ T n) :=
        (hf.mono (iInf_le _ n) le_rfl).dependsOn_of_cylinderEvents
      refine hshift.cylinderEvents_of_dependsOn fun ω ω' hωω' ↦ hdep fun k hk ↦ ?_
      rcases hk with hk | hk
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        simp
      · have hki : k ≠ i := fun h ↦ (h ▸ hi n) hk
        simp only [Function.update_of_ne hki]
        exact hωω' k hk
    obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one
      ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) htriv hmeasT
    have hqc : q x = c := by
      simp only [hq_def]
      rw [integral_congr_ae hc, integral_const]
      simp
    rw [hqc]
    exact hc
  filter_upwards [ae_all_iff.2 hconst] with ω hω
  have h := hω (ω i)
  rwa [Function.update_eq_self] at h

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

end MeasureTheory.GibbsMeasure.Tree

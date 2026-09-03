/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.TreeBoundaryLaw

/-!
# Georgii §12.1: Markov chains and boundary laws on trees, continued

Continues `GibbsMeasure.Model.TreeBoundaryLaw` (which has Definitions (12.1), (12.2), (12.8)–
(12.10), Theorem (12.12)(a), (12.12)(b)'s existence clause, and Corollary (12.17)'s "construction"
direction) with the remaining numbered items of §12.1: Comments (12.3)(2), (4), equation (12.5),
the uniqueness-up-to-a-factor clause of Theorem (12.12)(b), and the full Markov-chain
correspondence of Corollary (12.17) (both directions, and its uniqueness). Comments (12.3)(3),
(5), (6), Theorem (12.6), and Corollary (12.18) are **not formalised**; see below for exactly why
in each case.

## What is proved here

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

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

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

end MeasureTheory.GibbsMeasure.Tree

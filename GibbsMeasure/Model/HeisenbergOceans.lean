/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.OceanPart
public import GibbsMeasure.Model.LowEnergyOceanPhase
public import GibbsMeasure.Model.LowEnergyOceans
public import GibbsMeasure.Model.MerminWagnerExamples
public import GibbsMeasure.Specification.ChainEstimate
public import GibbsMeasure.Specification.CubePotentialSingleSite
public import GibbsMeasure.Specification.Singleton

/-!
# Georgii, Example (18.19): the classical Heisenberg model in the plane

Georgii, *Gibbs Measures and Phase Transitions*, §18.1, Example (18.19).  The state space is the
unit sphere `E = Metric.sphere (0 : V) 1` of a finite-dimensional real inner product space `V`
(Georgii: `ℝⁿ`, `n ≥ 2`; nothing below needs more than `Nontrivial V`), the a priori measure is
the normalised surface measure `sphereProb V = volume.toSphere.probNormalize` (Georgii writes
`λ` for the surface measure and `λ̃ = λ(E)⁻¹ λ`; `LocalGroundStates.lean` explains why the
normalised measure is the one to use with `t(G, Φ)`), and the `C`-potential is
`Φ_C = -∑_{{i,j} ⊆ C, |i-j| = 1} σ_i · σ_j`.

## The cube interaction

* `cubeGraph d` is the graph of the unit cube `C = {0, 1}^d`: two corners are adjacent when they
  differ in exactly one coordinate, i.e. when one is the image of the other under one of
  Georgii's reflections `r_k` (`cubeSiteRefl k`).  Every corner has degree `d`
  (`card_neighborFinset_cubeGraph`), and the cube is connected
  (`cubeGraph_forall_eq_of_adj`).
* `cubeBondSum d ψ` is the bond sum `∑_{{a,b} ⊆ C, |a-b| = 1} ψ(ζ_a, ζ_b)` of a *symmetric* bond
  interaction `ψ`, written as half the sum over the ordered adjacent pairs so that no choice of
  an orientation of the edges is needed (for a non-symmetric `ψ` it is the bond sum of the
  symmetrisation).  It is measurable when `ψ` is (`measurable_cubeBondSum`), invariant under
  every reflection `r_k` of the cube (`cubeBondSum_cubeRefl`, condition (iii) of Georgii (17.18),
  for *any* `ψ`), bounded by `2^{d-1} d` times a bound for `ψ` (`cubeBondSum_ge`,
  `cubeBondSum_le`), and changes by at most `d (M - m)` when one corner spin is changed
  (`cubeBondSum_sub_le`).
* `heisenbergCube V d` is Georgii's `Φ_C = -∑_{{i,j} ⊆ C, |i-j| = 1} σ_i · σ_j`, the bond sum of
  `ψ(x, y) = -⟪x, y⟫`.  It is measurable (`measurable_heisenbergCube`), reflection invariant
  (`heisenbergCube_cubeRefl`) and bounded by `2^{d-1} d` (`neg_le_heisenbergCube`,
  `heisenbergCube_le`); for `d = 2` this is Georgii's `Φ_C ≥ -4` and `|Φ_C| ≤ 4`
  (`neg_four_le_heisenbergCube`, `abs_heisenbergCube_le_four`), the first alternative of
  condition (iv) of (17.18).  Its one-corner oscillation is `2d` (`heisenbergCube_sub_le`,
  `smul_heisenbergCube_sub_le`) — the `4` behind Georgii's `e^{16β}` below.

## Georgii's two "clearly"s

* `localGroundEnergy_heisenbergCube`: **`m_Φ = -4`** (`localGroundEnergy_heisenbergCube_two`;
  for general `d`, `m_Φ = -2^{d-1} d`).  The lower bound is the pointwise bound `Φ_C ≥ -4`; the
  upper bound is the statement that `λ̃^C(Φ_C ≤ -4 + δ) > 0` for every `δ > 0`, which holds
  because that set contains the product of the spherical caps `{x : ⟪x, y⟫ > 1 - η}` around any
  unit vector `y` — a nonempty open set, and the surface measure is positive on nonempty open
  sets (Mathlib's `Measure.toSphere.instIsOpenPosMeasure`, inherited by the product measure
  `λ̃^C` through `Measure.pi.isOpenPosMeasure`).  The elementary estimate behind "the caps are
  almost aligned" is `real_inner_ge_of_real_inner_ge`.
* `heisenbergCube_eq_iff_forall_adj`, `heisenbergCube_eq_neg_four_iff` and
  `mem_localGroundStates_zero_iff_const`: **the local ground states are the constant
  configurations**.  This is the equality case of Cauchy–Schwarz on the sphere
  (`inner_eq_one_iff_of_norm_eq_one`) on every edge, together with the connectedness of the cube.

## The aligned configurations `G̃_ε`

* `heisenbergAligned V d ε` is Georgii's
  `G̃_ε = {ω ∈ E^C : ω_i · ω_j ≥ 1 - ε for all i, j ∈ C with |i - j| = 1}`; it is measurable
  (`measurableSet_heisenbergAligned`) and `r`-symmetric (`isRSymmetric_heisenbergAligned`), so
  Theorem (18.17) and Corollary (18.18) apply to it as well.
* `localGroundStates_subset_heisenbergAligned`: **Georgii's `G_ε(Φ) ⊆ G̃_ε`**
  (`mem_heisenbergAligned_of_heisenbergCube_le` is the quantitative form).  From
  `∑_{edges} σ_i · σ_j ≥ 4 - ε` and `σ_i · σ_j ≤ 1` on each edge every edge term is at least
  `1 - ε`; the symmetry `σ_i · σ_j = σ_j · σ_i` of the ordered-pair sum is what gives `1 - ε`
  rather than `1 - 2ε`.
* `alignedPair V ε i j` is the two-site event `{σ_i · σ_j ≥ 1 - ε}` on the lattice, and
  `mem_alignedPair_of_mem_latticePattern` is the step from the pattern to it: if two
  neighbouring sites of `ℤ^d` both carry `G̃_ε`, one of them is the lower corner of an
  elementary cube containing the other, so their spins are almost aligned.

## Georgii's conclusion at low temperature

* `real_inner_ge_of_mem_latticeOceanPart_localGroundStates`: any two adjacent sites of the ocean
  `ξ⁰_P(G_ε(Φ), ω)` carry spins with `σ_i · σ_j ≥ 1 - ε`, because every site of the ocean carries
  the pattern `G_ε(Φ) ⊆ G̃_ε`.
* `eventually_exists_mem_GP_measure_setOf_latticeOceanPart_heisenberg`: **for β large enough
  there is a `μ ∈ 𝒢(βΦ)`, invariant under the shifts of the plane and the reflections
  `r_1, r_2`, with `μ(ξ⁰_P(G_ε(Φ), ·) ≠ ∅) = 1`** — Corollary (18.18) (second assertion, in
  `GibbsMeasure/Model/LowEnergyOceanPhase.lean`) instantiated at the Heisenberg cube
  interaction; `abs_heisenbergCube_le_four` discharges the confinement hypothesis through
  `isCubeConfining_univ`, and the sphere is standard Borel because it is compact metrizable.

## Georgii's conclusion at high temperature

`measure_setOf_mem_infiniteClusters_heisenbergAligned_eq_zero` and
`measure_setOf_infiniteClusters_heisenbergAligned_nonempty_eq_zero`: **a low energy ocean need
not exist at high temperature.**  If `ρ` bounds the a priori measure of every spherical cap
`{x : x · u ≥ 1 - ε}` and

`(2d - 1) · e^{2^d · 2dβ} · ρ < 1`

— for `d = 2`, Georgii's `3 r(β, ε) < 1` with `r(β, ε) = e^{16β} λ̃(x_1 ≥ 1 - ε)` — then every
Gibbs measure of `βΦ` gives probability `0` to `{V(G̃_ε, ·) percolates}`, hence *a fortiori* to
`{ξ⁰_P(G̃_ε, ·) ≠ ∅}`.  The three ingredients are

* `cubeGibbsSpec_singleton_alignedPair_le`, Georgii's
  `γ^{βΦ}_{\{i\}}(σ_i · ω_j ≥ 1 - ε | ω) ≤ e^{16β} λ̃(cap)`: the kernel does not move `σ_j`
  (`Specification.apply_le_of_inter_subset`), and the single-site kernel of a `C`-potential is
  dominated by the a priori measure with the Boltzmann constant of the oscillation of `H_{\{i\}}`
  (`cubeGibbsSpec_singleton_apply_preimage_eval_le`, built on
  `Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le` and
  `hamiltonian_cubePotential_singleton_sub_le`).  The constant is `2^d` cubes containing `i`
  times the `2d` one-corner oscillation of `Φ_C`, i.e. `16β` for `d = 2` — Georgii's exponent.
* `Specification.measure_chainEvent_le`, the iterated conditioning along a self-avoiding path.
* `SimpleGraph.card_pathLists_succ_le`, the count `2d (2d - 1)^n` of self-avoiding paths of
  length `n + 1` (Georgii's `4 · 3^{ℓ-1}`), together with
  `SimpleGraph.exists_isPath_length_eq_of_mem_infiniteClusters`.

## Deviations from Georgii, and what is not here

* Georgii's `r(β, ε) = e^{16β} λ(x_1 ≥ 1 - ε)/λ(E)` is the measure of *one* cap, which he may use
  because the surface measure is invariant under rotations of the sphere.  That invariance is not
  in the tree, so the hypothesis above is a *uniform* bound `ρ` over all caps; taking `ρ` to be
  the supremum of the cap measures gives Georgii's statement verbatim once
  `volume.toSphere` is known to be `O(n)`-invariant.  Likewise Georgii's "when both `β` and `ε`
  are small" needs `λ̃(x_1 ≥ 1 - ε) → 0` as `ε → 0`, i.e. that a point of the sphere is null;
  neither fact is used below, and neither is proved here.
* **Comment (17.19)(2)** — that `Φ` is equivalent (Georgii, Definition (2.33)) to twice the
  nearest-neighbour Heisenberg pair potential `Ψ_{\{i,j\}} = -σ_i · σ_j` — is *not* formalised.
  The statement is true and the argument is short (each nearest-neighbour bond of `ℤ^2` lies in
  exactly two elementary cubes, so `H^Φ_Λ - 2 H^Ψ_Λ` only collects bonds disjoint from `Λ`, and
  is therefore `𝓕_{Λᶜ}`-measurable), but three pieces are missing from the tree: the pair
  potential `Potential.pair` needs a `LinearOrder` on the site type, while the `C`-potential
  lives on `Fin d → ℤ` (the tree's ordered lattice is the *different* type `ℤ ×ₗ ℤ` of
  `GibbsMeasure/Model/MerminWagner.lean`); there is no `IsFiniteRange` instance and no
  finite-sum formula for the Hamiltonian of a finite-range pair potential; and the
  bond-counting identity itself has no counterpart here.  Nothing in §18.1 uses the equivalence:
  it is Georgii's aside identifying his `Φ` with the familiar Heisenberg potential.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The graph of the unit cube -/

variable {d : ℕ}

lemma fin_two_rev_ne (v : Fin 2) : Fin.rev v ≠ v := by fin_cases v <;> decide

lemma fin_two_rev_eq_zero {v : Fin 2} (hv : v ≠ 0) : Fin.rev v = 0 := by
  fin_cases v
  · exact absurd rfl hv
  · rfl

/-- The graph of the unit cube `C = {0, 1}^d`: two corners are adjacent when they differ in
exactly one coordinate, that is, when one is the image of the other under one of the reflections
`r_k` of the cube (`cubeSiteRefl k`).  Georgii writes this as `|i - j| = 1` for `i, j ∈ C`. -/
def cubeGraph (d : ℕ) : SimpleGraph (Fin d → Fin 2) where
  Adj c c' := ∃ k, cubeSiteRefl k c = c'
  symm := ⟨fun c c' h ↦ by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, cubeSiteRefl_cubeSiteRefl k c⟩⟩
  loopless := ⟨fun c h ↦ by
    obtain ⟨k, hk⟩ := h
    have h := congrFun hk k
    rw [cubeSiteRefl_apply, Function.update_self] at h
    exact fin_two_rev_ne (c k) h⟩

lemma cubeGraph_adj {c c' : Fin d → Fin 2} :
    (cubeGraph d).Adj c c' ↔ ∃ k, cubeSiteRefl k c = c' := Iff.rfl

instance : DecidableRel (cubeGraph d).Adj := fun c c' ↦
  decidable_of_iff (∃ k, cubeSiteRefl k c = c') cubeGraph_adj.symm

lemma cubeGraph_adj_cubeSiteRefl_self (k : Fin d) (c : Fin d → Fin 2) :
    (cubeGraph d).Adj c (cubeSiteRefl k c) := ⟨k, rfl⟩

/-- Two reflections of the cube commute. -/
lemma cubeSiteRefl_comm (k k' : Fin d) (c : Fin d → Fin 2) :
    cubeSiteRefl k (cubeSiteRefl k' c) = cubeSiteRefl k' (cubeSiteRefl k c) := by
  rcases eq_or_ne k k' with rfl | hkk'
  · rfl
  · funext i
    simp only [cubeSiteRefl_apply, Function.update_apply]
    by_cases hik : i = k
    · subst hik
      simp [hkk']
    · by_cases hik' : i = k'
      · subst hik'
        simp [Ne.symm hkk']
      · simp [hik, hik']

/-- The reflections of the cube are automorphisms of its graph. -/
lemma cubeGraph_adj_cubeSiteRefl (k : Fin d) (c c' : Fin d → Fin 2) :
    (cubeGraph d).Adj (cubeSiteRefl k c) (cubeSiteRefl k c') ↔ (cubeGraph d).Adj c c' := by
  simp only [cubeGraph_adj]
  refine exists_congr fun k' ↦ ?_
  rw [cubeSiteRefl_comm]
  exact (cubeSiteRefl k).injective.eq_iff

/-- The neighbours of a corner are its `d` reflections. -/
lemma neighborFinset_cubeGraph (c : Fin d → Fin 2) :
    (cubeGraph d).neighborFinset c = Finset.univ.image fun k ↦ cubeSiteRefl k c := by
  ext c'
  simp [SimpleGraph.mem_neighborFinset, cubeGraph_adj]

lemma cubeSiteRefl_left_injective (c : Fin d → Fin 2) :
    Function.Injective fun k ↦ cubeSiteRefl k c := by
  intro k k' h
  by_contra hne
  have := congrFun h k
  simp only [cubeSiteRefl_apply, Function.update_self, Function.update_of_ne hne] at this
  exact fin_two_rev_ne (c k) this

/-- **The cube is `d`-regular.** -/
lemma card_neighborFinset_cubeGraph (c : Fin d → Fin 2) :
    ((cubeGraph d).neighborFinset c).card = d := by
  rw [neighborFinset_cubeGraph, Finset.card_image_of_injective _ (cubeSiteRefl_left_injective c),
    Finset.card_univ, Fintype.card_fin]

/-- The neighbours of a reflected corner are the reflected neighbours. -/
lemma neighborFinset_cubeGraph_cubeSiteRefl (k : Fin d) (c : Fin d → Fin 2) :
    (cubeGraph d).neighborFinset (cubeSiteRefl k c)
      = ((cubeGraph d).neighborFinset c).map (cubeSiteRefl k).toEmbedding := by
  ext c'
  rw [Finset.mem_map_equiv, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset,
    cubeSiteRefl_symm]
  conv_lhs => rw [← cubeSiteRefl_cubeSiteRefl k c']
  exact cubeGraph_adj_cubeSiteRefl k c (cubeSiteRefl k c')

/-- **The cube is connected**: a function on the corners which agrees on adjacent corners is
constant. -/
lemma cubeGraph_forall_eq_of_adj {X : Type*} {f : (Fin d → Fin 2) → X}
    (hf : ∀ c c', (cubeGraph d).Adj c c' → f c = f c') (c : Fin d → Fin 2) : f c = f 0 := by
  classical
  suffices h : ∀ n : ℕ, ∀ c : Fin d → Fin 2, (Finset.univ.filter fun k ↦ c k ≠ 0).card = n →
      f c = f 0 from h _ c rfl
  intro n
  induction n with
  | zero =>
    intro c hc
    have h0 : c = 0 := by
      funext k
      by_contra hk
      have : k ∈ Finset.univ.filter fun k ↦ c k ≠ 0 := Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
      rw [Finset.card_eq_zero.1 hc] at this
      exact absurd this (Finset.notMem_empty k)
    rw [h0]
  | succ n ih =>
    intro c hc
    obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ.filter fun k ↦ c k ≠ 0) = ∅ := Finset.filter_eq_empty_iff.2 fun k _ ↦
        not_not.2 (hcon k)
      rw [this, Finset.card_empty] at hc
      exact absurd hc (Nat.succ_ne_zero n).symm
    rw [hf c (cubeSiteRefl k c) (cubeGraph_adj_cubeSiteRefl_self k c)]
    refine ih _ ?_
    have hrev : Fin.rev (c k) = 0 := fin_two_rev_eq_zero hk
    have hfilter : (Finset.univ.filter fun k' ↦ cubeSiteRefl k c k' ≠ 0)
        = (Finset.univ.filter fun k' ↦ c k' ≠ 0).erase k := by
      ext k'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, cubeSiteRefl_apply,
        Function.update_apply]
      by_cases hk' : k' = k
      · subst hk'
        simp [hrev]
      · simp [hk']
    have hkmem : k ∈ Finset.univ.filter fun k' ↦ c k' ≠ 0 :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩
    rw [hfilter, Finset.card_erase_of_mem hkmem, hc]
    rfl

/-! ### Bond sums over the edges of the cube -/

section BondSum

variable {E : Type*}

/-- The bond sum `∑_{{a, b} ⊆ C, |a - b| = 1} ψ(ζ_a, ζ_b)` of a bond interaction `ψ` over the
edges of the unit cube, written as half the sum over the ordered adjacent pairs so that no choice
of an orientation of the edges is needed. -/
def cubeBondSum (d : ℕ) (ψ : E → E → ℝ) (ζ : (Fin d → Fin 2) → E) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ c, ∑ c' ∈ (cubeGraph d).neighborFinset c, ψ (ζ c) (ζ c')

lemma cubeBondSum_def (ψ : E → E → ℝ) (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ ζ = (2 : ℝ)⁻¹ * ∑ c, ∑ c' ∈ (cubeGraph d).neighborFinset c, ψ (ζ c) (ζ c') :=
  rfl

/-- The number of ordered adjacent pairs of corners of the cube is `2^d d`. -/
lemma sum_neighborFinset_cubeGraph_const (m : ℝ) :
    ∑ _c : Fin d → Fin 2, ∑ _c' ∈ (cubeGraph d).neighborFinset _c, m = (2 ^ d : ℕ) * d * m := by
  simp only [Finset.sum_const, card_neighborFinset_cubeGraph, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- A lower bound for the bond interaction on the spins of `ζ` gives the lower bound
`2^{d-1} d m` for the bond sum: the cube has `2^d` corners of degree `d`. -/
lemma cubeBondSum_ge {ψ : E → E → ℝ} {m : ℝ} {ζ : (Fin d → Fin 2) → E}
    (hm : ∀ c c', m ≤ ψ (ζ c) (ζ c')) : (2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d * m) ≤ cubeBondSum d ψ ζ := by
  unfold cubeBondSum
  gcongr
  rw [← sum_neighborFinset_cubeGraph_const]
  exact Finset.sum_le_sum fun c _ ↦ Finset.sum_le_sum fun c' _ ↦ hm _ _

/-- An upper bound for the bond interaction on the spins of `ζ` gives the upper bound
`2^{d-1} d M` for the bond sum. -/
lemma cubeBondSum_le {ψ : E → E → ℝ} {M : ℝ} {ζ : (Fin d → Fin 2) → E}
    (hM : ∀ c c', ψ (ζ c) (ζ c') ≤ M) : cubeBondSum d ψ ζ ≤ (2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d * M) := by
  have h := cubeBondSum_ge (ψ := fun x y ↦ -ψ x y) (m := -M) (ζ := ζ)
    fun c c' ↦ neg_le_neg (hM c c')
  have hneg : cubeBondSum d (fun x y ↦ -ψ x y) ζ = -cubeBondSum d ψ ζ := by
    simp [cubeBondSum, Finset.sum_neg_distrib]
  rw [hneg] at h
  linarith

/-- **The one-corner oscillation of a bond sum.**  Changing the spin at a single corner `a` of
the cube changes only the `2d` ordered adjacent pairs incident to `a`, so a bond interaction with
values in `[m, M]` gives a bond sum that changes by at most `d (M - m)`.  (For the Heisenberg
interaction `ψ = -⟪·,·⟫` on the sphere this is `2d`, and for `d = 2` it is the constant `4`
behind Georgii's `e^{16β}` in Example (18.19).) -/
lemma cubeBondSum_sub_le {ψ : E → E → ℝ} {m M : ℝ} (hm : ∀ x y, m ≤ ψ x y)
    (hM : ∀ x y, ψ x y ≤ M) (a : Fin d → Fin 2) {ζ ζ' : (Fin d → Fin 2) → E}
    (h : ∀ c, c ≠ a → ζ c = ζ' c) :
    cubeBondSum d ψ ζ - cubeBondSum d ψ ζ' ≤ d * (M - m) := by
  classical
  set f : (Fin d → Fin 2) → (Fin d → Fin 2) → ℝ :=
    fun c c' ↦ ψ (ζ c) (ζ c') - ψ (ζ' c) (ζ' c') with hf
  have hfle : ∀ c c', f c c' ≤ M - m := fun c c' ↦ sub_le_sub (hM _ _) (hm _ _)
  have hf0 : ∀ c c', c ≠ a → c' ≠ a → f c c' = 0 := fun c c' hc hc' ↦ by
    simp only [hf, h c hc, h c' hc', sub_self]
  set F : (Fin d → Fin 2) → ℝ := fun c ↦ ∑ c' ∈ (cubeGraph d).neighborFinset c, f c c' with hF
  -- the corner `a` contributes at most `d (M - m)`
  have hFa : F a ≤ d * (M - m) :=
    calc ∑ c' ∈ (cubeGraph d).neighborFinset a, f a c'
        ≤ ∑ _c' ∈ (cubeGraph d).neighborFinset a, (M - m) :=
          Finset.sum_le_sum fun c' _ ↦ hfle a c'
      _ = d * (M - m) := by
          rw [Finset.sum_const, card_neighborFinset_cubeGraph, nsmul_eq_mul]
  -- the other corners contribute only through their single bond to `a`
  have hFc : ∀ c ∈ (cubeGraph d).neighborFinset a, F c ≤ M - m := by
    intro c hc
    have hca : (cubeGraph d).Adj c a := ((SimpleGraph.mem_neighborFinset _ _ _).1 hc).symm
    change ∑ c' ∈ (cubeGraph d).neighborFinset c, f c c' ≤ M - m
    rw [Finset.sum_eq_single a (fun c' _ hc' ↦ hf0 c c' hca.ne hc')
      fun hmem ↦ absurd ((SimpleGraph.mem_neighborFinset _ _ _).2 hca) hmem]
    exact hfle c a
  have hrest : ∑ c ∈ Finset.univ.erase a, F c ≤ d * (M - m) := by
    have hsub : (cubeGraph d).neighborFinset a ⊆ Finset.univ.erase a := fun c hc ↦
      Finset.mem_erase.2
        ⟨((SimpleGraph.mem_neighborFinset _ _ _).1 hc).ne', Finset.mem_univ c⟩
    have hzero : ∀ c ∈ Finset.univ.erase a, c ∉ (cubeGraph d).neighborFinset a → F c = 0 := by
      intro c hc hcn
      change ∑ c' ∈ (cubeGraph d).neighborFinset c, f c c' = 0
      refine Finset.sum_eq_zero fun c' hc' ↦ hf0 c c' (Finset.mem_erase.1 hc).1 fun hc'a ↦ hcn ?_
      exact (SimpleGraph.mem_neighborFinset _ _ _).2
        ((SimpleGraph.mem_neighborFinset _ _ _).1 (hc'a ▸ hc')).symm
    rw [← Finset.sum_subset hsub hzero]
    calc ∑ c ∈ (cubeGraph d).neighborFinset a, F c
        ≤ ∑ _c ∈ (cubeGraph d).neighborFinset a, (M - m) := Finset.sum_le_sum hFc
      _ = d * (M - m) := by
          rw [Finset.sum_const, card_neighborFinset_cubeGraph, nsmul_eq_mul]
  have hsplit : ∑ c, F c ≤ 2 * (d * (M - m)) := by
    rw [← Finset.add_sum_erase _ F (Finset.mem_univ a)]
    linarith
  have hkey : cubeBondSum d ψ ζ - cubeBondSum d ψ ζ' = (2 : ℝ)⁻¹ * ∑ c, F c := by
    simp only [cubeBondSum_def, hF, hf, Finset.sum_sub_distrib]
    ring
  rw [hkey]
  linarith

variable [MeasurableSpace E]

lemma measurable_cubeBondSum {ψ : E → E → ℝ} (hψ : Measurable (Function.uncurry ψ)) :
    Measurable (cubeBondSum d ψ) := by
  refine measurable_const.mul (Finset.measurable_sum _ fun c _ ↦ Finset.measurable_sum _
    fun c' _ ↦ ?_)
  have h : Measurable fun ζ : (Fin d → Fin 2) → E ↦ (ζ c, ζ c') :=
    (measurable_pi_apply c).prodMk (measurable_pi_apply c')
  exact hψ.comp h

/-- **Condition (iii) of Georgii (17.18)** for a bond sum: it is invariant under every
reflection `r_k` of the cube, for any bond interaction `ψ`. -/
lemma cubeBondSum_cubeRefl (ψ : E → E → ℝ) (k : Fin d) (ζ : (Fin d → Fin 2) → E) :
    cubeBondSum d ψ (cubeRefl E k ζ) = cubeBondSum d ψ ζ := by
  unfold cubeBondSum
  congr 1
  refine Fintype.sum_equiv (cubeSiteRefl k) _ _ fun c ↦ ?_
  rw [neighborFinset_cubeGraph_cubeSiteRefl, Finset.sum_map]
  rfl

end BondSum

/-! ### Georgii (18.19): the Heisenberg cube interaction -/

section Sphere

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (V) in
/-- **Georgii (18.19).** The cube interaction `Φ_C = -∑_{{i,j} ⊆ C, |i-j| = 1} σ_i · σ_j` of the
classical Heisenberg model, on the unit sphere of `V`. -/
abbrev heisenbergCube (d : ℕ) : ((Fin d → Fin 2) → sphere (0 : V) 1) → ℝ :=
  cubeBondSum d fun x y ↦ -⟪(x : V), (y : V)⟫

lemma neg_one_le_real_inner_sphere (x y : sphere (0 : V) 1) : -1 ≤ ⟪(x : V), (y : V)⟫ := by
  have h := neg_le_of_abs_le (abs_real_inner_le_norm (x : V) (y : V))
  rwa [mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.2, one_mul] at h

lemma real_inner_sphere_le_one (x y : sphere (0 : V) 1) : ⟪(x : V), (y : V)⟫ ≤ 1 := by
  have h := real_inner_le_norm (x : V) (y : V)
  rwa [mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.2, one_mul] at h

/-- `Φ_C ≥ -2^{d-1} d`; for `d = 2` this is Georgii's `Φ_C ≥ -4`. -/
lemma neg_le_heisenbergCube (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) ≤ heisenbergCube V d ζ := by
  have h := cubeBondSum_ge (ψ := fun x y : sphere (0 : V) 1 ↦ -⟪(x : V), (y : V)⟫) (m := -1)
    (ζ := ζ) fun c c' ↦ neg_le_neg (real_inner_sphere_le_one (ζ c) (ζ c'))
  simpa [mul_neg] using h

/-- `Φ_C ≤ 2^{d-1} d`. -/
lemma heisenbergCube_le (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    heisenbergCube V d ζ ≤ (2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d) := by
  have h := cubeBondSum_le (ψ := fun x y : sphere (0 : V) 1 ↦ -⟪(x : V), (y : V)⟫) (M := 1)
    (ζ := ζ) fun c c' ↦ by linarith [neg_one_le_real_inner_sphere (ζ c) (ζ c')]
  simpa using h

/-- **Georgii's `Φ_C ≥ -4`** in the plane. -/
lemma neg_four_le_heisenbergCube (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    -4 ≤ heisenbergCube V 2 ζ := by
  have h := neg_le_heisenbergCube ζ
  norm_num at h
  exact h

/-- **Georgii's `‖Φ_C‖ ≤ 4`** in the plane: the first alternative of condition (iv) of
(17.18). -/
lemma abs_heisenbergCube_le_four (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    |heisenbergCube V 2 ζ| ≤ 4 := by
  have h1 := neg_le_heisenbergCube ζ
  have h2 := heisenbergCube_le ζ
  norm_num at h1 h2
  exact abs_le.2 ⟨h1, h2⟩

/-- **The one-corner oscillation of the Heisenberg cube interaction is `2d`.**  Changing the spin
at one corner changes the `2d` ordered bonds at that corner, each by at most `2`.  For `d = 2`
this is the constant `4` behind Georgii's `e^{16β}` in Example (18.19). -/
lemma heisenbergCube_sub_le (a : Fin d → Fin 2) {ζ ζ' : (Fin d → Fin 2) → sphere (0 : V) 1}
    (h : ∀ c, c ≠ a → ζ c = ζ' c) :
    heisenbergCube V d ζ - heisenbergCube V d ζ' ≤ 2 * d := by
  have h2 := cubeBondSum_sub_le (ψ := fun x y : sphere (0 : V) 1 ↦ -⟪(x : V), (y : V)⟫)
    (m := -1) (M := 1) (fun x y ↦ by linarith [real_inner_sphere_le_one x y])
    (fun x y ↦ by linarith [neg_one_le_real_inner_sphere x y]) a h
  norm_num at h2
  linarith

/-- The one-corner oscillation of `βΦ_C` is `2dβ`, the hypothesis of
`MeasureTheory.GibbsMeasure.cubeGibbsSpec_singleton_apply_le`. -/
lemma smul_heisenbergCube_sub_le {β : ℝ} (hβ : 0 ≤ β)
    (ζ ζ' : (Fin d → Fin 2) → sphere (0 : V) 1) (a : Fin d → Fin 2)
    (h : ∀ c, c ≠ a → ζ c = ζ' c) :
    β * heisenbergCube V d ζ - β * heisenbergCube V d ζ' ≤ β * (2 * d) := by
  rw [← mul_sub]
  exact mul_le_mul_of_nonneg_left (heisenbergCube_sub_le a h) hβ

/-! ### The local ground states are the constant configurations -/

/-- **The equality case**: `Φ_C = -2^{d-1} d` exactly when all adjacent spins coincide. -/
theorem heisenbergCube_eq_iff_forall_adj (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    heisenbergCube V d ζ = -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) ↔
      ∀ c c', (cubeGraph d).Adj c c' → ζ c = ζ c' := by
  have hsum := sum_neighborFinset_cubeGraph_const (d := d) (1 : ℝ)
  have hle : ∀ c ∈ (Finset.univ : Finset (Fin d → Fin 2)),
      (∑ c' ∈ (cubeGraph d).neighborFinset c, ⟪(ζ c : V), (ζ c' : V)⟫)
        ≤ ∑ _c' ∈ (cubeGraph d).neighborFinset c, (1 : ℝ) :=
    fun c _ ↦ Finset.sum_le_sum fun c' _ ↦ real_inner_sphere_le_one _ _
  have hφ : heisenbergCube V d ζ
      = -((2 : ℝ)⁻¹ * ∑ c, ∑ c' ∈ (cubeGraph d).neighborFinset c, ⟪(ζ c : V), (ζ c' : V)⟫) := by
    simp only [heisenbergCube, cubeBondSum_def, Finset.sum_neg_distrib, mul_neg]
  have hkey : heisenbergCube V d ζ = -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) ↔
      (∑ c : Fin d → Fin 2, ∑ c' ∈ (cubeGraph d).neighborFinset c, ⟪(ζ c : V), (ζ c' : V)⟫)
        = ∑ c : Fin d → Fin 2, ∑ _c' ∈ (cubeGraph d).neighborFinset c, (1 : ℝ) := by
    rw [hφ]
    constructor <;> intro h <;> linarith
  rw [hkey, Finset.sum_eq_sum_iff_of_le hle]
  constructor
  · intro h c c' hcc'
    have h1 := (Finset.sum_eq_sum_iff_of_le fun c' _ ↦ real_inner_sphere_le_one (ζ c) (ζ c')).1
      (h c (Finset.mem_univ c)) c' ((SimpleGraph.mem_neighborFinset _ _ _).2 hcc')
    exact Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (mem_sphere_zero_iff_norm.1 (ζ c).2)
      (mem_sphere_zero_iff_norm.1 (ζ c').2)).1 h1)
  · intro h c _
    refine (Finset.sum_eq_sum_iff_of_le fun c' _ ↦ real_inner_sphere_le_one (ζ c) (ζ c')).2
      fun c' hc' ↦ ?_
    rw [h c c' ((SimpleGraph.mem_neighborFinset _ _ _).1 hc')]
    exact (inner_eq_one_iff_of_norm_eq_one (mem_sphere_zero_iff_norm.1 (ζ c').2)
      (mem_sphere_zero_iff_norm.1 (ζ c').2)).2 rfl

/-- **Georgii's "the local ground states are the constant configurations"**, in the plane:
`Φ_C(ζ) = -4` exactly when `ζ` is constant. -/
theorem heisenbergCube_eq_neg_four_iff (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    heisenbergCube V 2 ζ = -4 ↔ ∀ c, ζ c = ζ 0 := by
  have h := heisenbergCube_eq_iff_forall_adj ζ
  norm_num at h
  rw [h]
  exact ⟨fun hadj c ↦ cubeGraph_forall_eq_of_adj hadj c,
    fun hconst c c' _ ↦ by rw [hconst c, hconst c']⟩

/-! ### Georgii's `G̃_ε`: the configurations with aligned adjacent spins -/

variable (V) in
/-- **Georgii (18.19).** `G̃_ε = {ω ∈ E^C : ω_i · ω_j ≥ 1 - ε for all i, j ∈ C with |i - j| = 1}`,
the cube configurations whose adjacent spins are aligned up to `ε`. -/
def heisenbergAligned (d : ℕ) (ε : ℝ) : Set ((Fin d → Fin 2) → sphere (0 : V) 1) :=
  {ζ | ∀ c c', (cubeGraph d).Adj c c' → 1 - ε ≤ ⟪(ζ c : V), (ζ c' : V)⟫}

lemma mem_heisenbergAligned {ε : ℝ} {ζ : (Fin d → Fin 2) → sphere (0 : V) 1} :
    ζ ∈ heisenbergAligned V d ε ↔
      ∀ c c', (cubeGraph d).Adj c c' → 1 - ε ≤ ⟪(ζ c : V), (ζ c' : V)⟫ := Iff.rfl

/-- **Georgii's `G_ε(Φ) ⊆ G̃_ε`** in the form: if `Φ_C(ζ) ≤ -2^{d-1} d + ε`, then every pair of
adjacent spins of `ζ` has `σ_i · σ_j ≥ 1 - ε`. -/
theorem mem_heisenbergAligned_of_heisenbergCube_le {ε : ℝ}
    {ζ : (Fin d → Fin 2) → sphere (0 : V) 1}
    (hζ : heisenbergCube V d ζ ≤ -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) + ε) :
    ζ ∈ heisenbergAligned V d ε := by
  intro a b hab
  set u : (Fin d → Fin 2) → (Fin d → Fin 2) → ℝ := fun c c' ↦ 1 - ⟪(ζ c : V), (ζ c' : V)⟫
    with hu
  have hu0 : ∀ c c', 0 ≤ u c c' := fun c c' ↦ by
    simp only [hu]
    linarith [real_inner_sphere_le_one (ζ c) (ζ c')]
  -- the total defect is at most `2ε`
  have htotal : ∑ c : Fin d → Fin 2, ∑ c' ∈ (cubeGraph d).neighborFinset c, u c c' ≤ 2 * ε := by
    have hsum : ∑ c : Fin d → Fin 2, ∑ c' ∈ (cubeGraph d).neighborFinset c, u c c'
        = ((2 ^ d : ℕ) : ℝ) * d + 2 * heisenbergCube V d ζ := by
      have h1 := sum_neighborFinset_cubeGraph_const (d := d) (1 : ℝ)
      have hφ : heisenbergCube V d ζ = -((2 : ℝ)⁻¹ *
          ∑ c, ∑ c' ∈ (cubeGraph d).neighborFinset c, ⟪(ζ c : V), (ζ c' : V)⟫) := by
        simp only [heisenbergCube, cubeBondSum_def, Finset.sum_neg_distrib, mul_neg]
      simp only [hu, Finset.sum_sub_distrib, hφ]
      rw [h1]
      ring
    rw [hsum]
    linarith
  -- the two ordered copies of the edge `{a, b}` contribute twice `u a b`
  have hab' : a ≠ b := (cubeGraph d).ne_of_adj hab
  have hpair : u a b + u b a
      ≤ ∑ c : Fin d → Fin 2, ∑ c' ∈ (cubeGraph d).neighborFinset c, u c c' := by
    calc u a b + u b a
        ≤ (∑ c' ∈ (cubeGraph d).neighborFinset a, u a c')
          + ∑ c' ∈ (cubeGraph d).neighborFinset b, u b c' :=
          add_le_add
            (Finset.single_le_sum (fun c' _ ↦ hu0 a c')
              ((SimpleGraph.mem_neighborFinset _ _ _).2 hab))
            (Finset.single_le_sum (fun c' _ ↦ hu0 b c')
              ((SimpleGraph.mem_neighborFinset _ _ _).2 hab.symm))
      _ = ∑ c ∈ ({a, b} : Finset (Fin d → Fin 2)),
            ∑ c' ∈ (cubeGraph d).neighborFinset c, u c c' :=
          (Finset.sum_pair (f := fun c ↦ ∑ c' ∈ (cubeGraph d).neighborFinset c, u c c') hab').symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun c _ _ ↦ Finset.sum_nonneg fun c' _ ↦ hu0 c c'
  have hsymm : u b a = u a b := by
    simp only [hu, real_inner_comm]
  have : u a b ≤ ε := by linarith
  simp only [hu] at this
  linarith

/-- Two unit vectors close to a third one are close to each other:
`⟪x, y⟫ ≥ 1 - η` and `⟪z, y⟫ ≥ 1 - η` give `⟪x, z⟫ ≥ 1 - 4η`. -/
lemma real_inner_ge_of_real_inner_ge {x y z : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    {η : ℝ} (hxy : 1 - η ≤ ⟪x, y⟫) (hzy : 1 - η ≤ ⟪z, y⟫) : 1 - 4 * η ≤ ⟪x, z⟫ := by
  have h1 : ‖x - y‖ ^ 2 = 2 - 2 * ⟪x, y⟫ := by
    rw [norm_sub_sq_real, hx, hy]; ring
  have h2 : ‖y - z‖ ^ 2 = 2 - 2 * ⟪z, y⟫ := by
    rw [norm_sub_sq_real, hy, hz, real_inner_comm]; ring
  have h3 : ‖x - z‖ ^ 2 = 2 - 2 * ⟪x, z⟫ := by
    rw [norm_sub_sq_real, hx, hz]; ring
  have h4 : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := norm_sub_le_norm_sub_add_norm_sub x y z
  have h5 : ‖x - z‖ ^ 2 ≤ 2 * (‖x - y‖ ^ 2 + ‖y - z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x - y‖ - ‖y - z‖), norm_nonneg (x - z), norm_nonneg (x - y),
      norm_nonneg (y - z)]
  linarith

/-! ### Measurability and reflection symmetry on the sphere -/

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

lemma measurable_heisenbergCube : Measurable (heisenbergCube V d) := by
  refine measurable_cubeBondSum (Continuous.measurable ?_)
  exact ((continuous_subtype_val.comp continuous_fst).inner
    (continuous_subtype_val.comp continuous_snd)).neg

omit [BorelSpace V] [FiniteDimensional ℝ V] in
/-- **Condition (iii) of Georgii (17.18)** for the Heisenberg model. -/
lemma heisenbergCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    heisenbergCube V d (cubeRefl (sphere (0 : V) 1) k ζ) = heisenbergCube V d ζ :=
  cubeBondSum_cubeRefl _ k ζ

lemma measurable_real_inner_apply (c c' : Fin d → Fin 2) :
    Measurable fun ζ : (Fin d → Fin 2) → sphere (0 : V) 1 ↦ ⟪(ζ c : V), (ζ c' : V)⟫ :=
  ((continuous_subtype_val.comp (continuous_apply c)).inner
    (continuous_subtype_val.comp (continuous_apply c'))).measurable

lemma measurableSet_heisenbergAligned (ε : ℝ) : MeasurableSet (heisenbergAligned V d ε) := by
  simp only [heisenbergAligned, Set.ofPred_forall]
  exact MeasurableSet.iInter fun c ↦ MeasurableSet.iInter fun c' ↦ MeasurableSet.iInter fun _ ↦
    measurableSet_le measurable_const (measurable_real_inner_apply c c')

omit [BorelSpace V] [FiniteDimensional ℝ V] in
/-- `G̃_ε` is `r`-symmetric, so that Theorem (18.17) applies to it. -/
lemma isRSymmetric_heisenbergAligned (ε : ℝ) :
    IsRSymmetric (sphere (0 : V) 1) (heisenbergAligned V d ε) := by
  intro k
  ext ζ
  simp only [mem_preimage, mem_heisenbergAligned, cubeRefl_apply]
  constructor
  · intro h c c' hcc'
    have := h (cubeSiteRefl k c) (cubeSiteRefl k c') ((cubeGraph_adj_cubeSiteRefl k c c').2 hcc')
    rwa [cubeSiteRefl_cubeSiteRefl, cubeSiteRefl_cubeSiteRefl] at this
  · intro h c c' hcc'
    exact h _ _ ((cubeGraph_adj_cubeSiteRefl k c c').2 hcc')

/-! ### The a priori measure: the normalised surface measure -/

variable (V) in
/-- The normalised surface measure `λ̃ = λ(E)⁻¹ λ` of the unit sphere of `V`, the a priori
measure of Georgii's Heisenberg model in the normalisation of `LocalGroundStates.lean`. -/
abbrev sphereProb : Measure (sphere (0 : V) 1) := (volume : Measure V).toSphere.probNormalize

instance [Nontrivial V] : IsProbabilityMeasure (sphereProb V) :=
  Measure.isProbabilityMeasure_probNormalize _

/-- The normalised surface measure charges every nonempty open subset of the sphere. -/
instance : (sphereProb V).IsOpenPosMeasure :=
  Measure.isOpenPosMeasure_smul (volume : Measure V).toSphere
    (ENNReal.inv_ne_zero.2 (measure_ne_top _ _))

/-- `λ̃^C` charges every nonempty open subset of `E^C`.  This is Mathlib's
`MeasureTheory.Measure.pi.isOpenPosMeasure`, named here so that the three instance arguments are
synthesised separately: found in one search, the resulting instance term overruns
`synthInstance.maxSize`, because `SigmaFinite (sphereProb V)` is reconstructed through
`Measure.Regular` instead of through `IsProbabilityMeasure`. -/
instance [Nontrivial V] : (cubeMeasure d (sphereProb V)).IsOpenPosMeasure :=
  Measure.pi.isOpenPosMeasure _

/-- **Georgii's "clearly, `m_Φ = -4`"**, for the cube of any dimension: the local ground energy
of the Heisenberg cube interaction is its pointwise infimum `-2^{d-1} d`.  The lower bound is the
pointwise bound; the upper bound is the positivity of the surface measure of a product of
spherical caps. -/
theorem localGroundEnergy_heisenbergCube [Nontrivial V] :
    localGroundEnergy (heisenbergCube V d) (sphereProb V)
      = -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) := by
  set m : ℝ := -((2 : ℝ)⁻¹ * ((2 ^ d : ℕ) * d)) with hm
  refine le_antisymm ?_ (le_localGroundEnergy fun ζ ↦ neg_le_heisenbergCube ζ)
  rw [localGroundEnergy_eq_sSup fun ζ ↦ neg_le_heisenbergCube ζ]
  refine csSup_le ⟨m - 1, ?_⟩ fun c hc ↦ ?_
  · have hempty : {ζ : (Fin d → Fin 2) → sphere (0 : V) 1 | heisenbergCube V d ζ ≤ m - 1} = ∅ := by
      ext ζ
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [neg_le_heisenbergCube (V := V) ζ]
    change cubeMeasure d (sphereProb V) {ζ | heisenbergCube V d ζ ≤ m - 1} = 0
    rw [hempty, measure_empty]
  · by_contra hlt
    push Not at hlt
    -- a product of spherical caps lies in `{Φ_C ≤ c}` and has positive measure
    obtain ⟨y⟩ : Nonempty (sphere (0 : V) 1) := (sphereProb V).nonempty_of_neZero
    set δ : ℝ := c - m with hδ
    have hδpos : 0 < δ := by linarith
    set η : ℝ := δ / (2 * ((2 ^ d : ℕ) * d) + 1) with hη
    have hηpos : 0 < η := by positivity
    set U : Set ((Fin d → Fin 2) → sphere (0 : V) 1) :=
      {ζ | ∀ a, 1 - η < ⟪(ζ a : V), (y : V)⟫} with hU
    have hUopen : IsOpen U := by
      simp only [hU, Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun a ↦ isOpen_lt continuous_const
        ((continuous_subtype_val.comp (continuous_apply a)).inner continuous_const)
    have hUne : U.Nonempty := by
      refine ⟨fun _ ↦ y, fun a ↦ ?_⟩
      rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 y.2]
      linarith
    have hUsub : U ⊆ {ζ | heisenbergCube V d ζ ≤ c} := by
      intro ζ hζ
      have hbond : ∀ a b, -⟪(ζ a : V), (ζ b : V)⟫ ≤ -(1 - 4 * η) := fun a b ↦
        neg_le_neg (real_inner_ge_of_real_inner_ge (mem_sphere_zero_iff_norm.1 (ζ a).2)
          (mem_sphere_zero_iff_norm.1 y.2) (mem_sphere_zero_iff_norm.1 (ζ b).2)
          (hζ a).le (hζ b).le)
      have h := cubeBondSum_le (ψ := fun x y : sphere (0 : V) 1 ↦ -⟪(x : V), (y : V)⟫)
        (M := -(1 - 4 * η)) (ζ := ζ) hbond
      change heisenbergCube V d ζ ≤ _ at h
      refine h.trans ?_
      have hηle : (2 * ((2 ^ d : ℕ) * d) + 1) * η = δ := by
        rw [hη, mul_div_cancel₀ _ (by positivity)]
      have hcd : c = m + δ := by rw [hδ]; ring
      rw [hcd, hm]
      nlinarith [hηle, hηpos, show (0 : ℝ) ≤ (2 ^ d : ℕ) * d by positivity]
    have hpos : 0 < cubeMeasure d (sphereProb V) U := hUopen.measure_pos _ hUne
    exact absurd hc ((measure_mono hUsub).trans_lt' hpos).ne'

/-- **Georgii's "clearly, `m_Φ = -4`"** in the plane. -/
theorem localGroundEnergy_heisenbergCube_two [Nontrivial V] :
    localGroundEnergy (heisenbergCube V 2) (sphereProb V) = -4 := by
  rw [localGroundEnergy_heisenbergCube]
  norm_num

/-- **Georgii's "the local ground states are the constant configurations"**: `ζ ∈ G_0(Φ)` exactly
when `ζ` is constant, in the plane. -/
theorem mem_localGroundStates_zero_iff_const [Nontrivial V]
    (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    ζ ∈ localGroundStates (heisenbergCube V 2) (sphereProb V) 0 ↔ ∀ c, ζ c = ζ 0 := by
  rw [mem_localGroundStates, localGroundEnergy_heisenbergCube_two, add_zero,
    ← heisenbergCube_eq_neg_four_iff]
  exact ⟨fun h ↦ le_antisymm h (neg_four_le_heisenbergCube ζ), fun h ↦ h.le⟩

/-- **Georgii's `G_ε(Φ) ⊆ G̃_ε`.** -/
theorem localGroundStates_subset_heisenbergAligned [Nontrivial V] (ε : ℝ) :
    localGroundStates (heisenbergCube V d) (sphereProb V) ε ⊆ heisenbergAligned V d ε := by
  intro ζ hζ
  rw [mem_localGroundStates, localGroundEnergy_heisenbergCube] at hζ
  exact mem_heisenbergAligned_of_heisenbergCube_le hζ

/-! ### From the pattern `G̃_ε` to Georgii's two-site events -/

variable (V) in
/-- **Georgii's two-site event `{σ_i · σ_j ≥ 1 - ε}`** of Example (18.19). -/
def alignedPair (ε : ℝ) (i j : Fin d → ℤ) : Set ((Fin d → ℤ) → sphere (0 : V) 1) :=
  {ω | 1 - ε ≤ ⟪(ω i : V), (ω j : V)⟫}

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
lemma mem_alignedPair {ε : ℝ} {i j : Fin d → ℤ} {ω : (Fin d → ℤ) → sphere (0 : V) 1} :
    ω ∈ alignedPair V ε i j ↔ 1 - ε ≤ ⟪(ω i : V), (ω j : V)⟫ := Iff.rfl

/-- `{σ_i · σ_j ≥ 1 - ε}` reads only the two sites `i` and `j`. -/
lemma measurableSet_cylinderEvents_alignedPair (ε : ℝ) (i j : Fin d → ℤ) :
    MeasurableSet[cylinderEvents ({i, j} : Set (Fin d → ℤ))] (alignedPair V ε i j) := by
  have hi : Measurable[cylinderEvents ({i, j} : Set (Fin d → ℤ))]
      fun ω : (Fin d → ℤ) → sphere (0 : V) 1 ↦ ω i :=
    measurable_coordinate_projection_2 (by simp)
  have hj : Measurable[cylinderEvents ({i, j} : Set (Fin d → ℤ))]
      fun ω : (Fin d → ℤ) → sphere (0 : V) 1 ↦ ω j :=
    measurable_coordinate_projection_2 (by simp)
  exact measurableSet_le measurable_const
    (((continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd)).measurable.comp (hi.prodMk hj))

/-- The corner `e_k` of the cube, as the lattice step from `i` to `i + e_k`. -/
lemma add_intCubeCast_cubeSiteRefl_zero (k : Fin d) (i : Fin d → ℤ) :
    i + intCubeCast (cubeSiteRefl k (0 : Fin d → Fin 2)) = Function.update i k (i k + 1) := by
  funext l
  by_cases hl : l = k <;>
    simp [hl, intCubeCast, cubeSiteRefl_apply, Fin.rev]

omit [BorelSpace V] [FiniteDimensional ℝ V] in
/-- **Georgii's step from `V(G̃_ε, ω)` to the two-site events.**  If two neighbouring sites of
`ℤ^d` both carry the pattern `G̃_ε`, their spins are aligned: one of the two is the lower corner
of an elementary cube containing the other. -/
theorem mem_alignedPair_of_mem_latticePattern {ε : ℝ} {ω : (Fin d → ℤ) → sphere (0 : V) 1}
    {i j : Fin d → ℤ} (hij : (latticeGraph d).Adj i j)
    (hi : i ∈ latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)
    (hj : j ∈ latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω) :
    ω ∈ alignedPair V ε i j := by
  have hstep : ∀ {x : Fin d → ℤ} (k : Fin d),
      x ∈ latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω →
      1 - ε ≤ ⟪(ω x : V), (ω (Function.update x k (x k + 1)) : V)⟫ := by
    intro x k hx
    have hx' := (mem_latticePattern_of_isRSymmetric
      (isRSymmetric_heisenbergAligned (V := V) (d := d) ε) ω x).1 hx
    have := hx' 0 (cubeSiteRefl k 0) (cubeGraph_adj_cubeSiteRefl_self k 0)
    rwa [latticeCubeView_apply, latticeCubeView_apply, intCubeCast_zero, add_zero,
      add_intCubeCast_cubeSiteRefl_zero] at this
  obtain ⟨k, s, hs, hj'⟩ := latticeGraph_adj_decomp hij
  rcases hs with rfl | rfl
  · rw [mem_alignedPair, hj']
    exact hstep k hi
  · have hi' : i = Function.update j k (j k + 1) := by
      funext l
      by_cases hl : l = k <;> simp [hl, hj']
    rw [mem_alignedPair, real_inner_comm, hi']
    exact hstep k hj

/-! ### Georgii (18.19), first half: a low energy ocean at low temperature -/

/-- **The spins of a low energy ocean are almost aligned.**  Every site of `ξ⁰_P(G_ε(Φ), ω)`
carries the pattern `G_ε(Φ) ⊆ G̃_ε`, so any two adjacent sites of the ocean satisfy Georgii's
`σ_i · σ_j ≥ 1 - ε`. -/
theorem real_inner_ge_of_mem_latticeOceanPart_localGroundStates [Nontrivial V] {ε : ℝ}
    {ω : (Fin 2 → ℤ) → sphere (0 : V) 1} {i j : Fin 2 → ℤ} (hij : (latticeGraph 2).Adj i j)
    (hi : i ∈ latticeOceanPart (sphere (0 : V) 1)
      (localGroundStates (heisenbergCube V 2) (sphereProb V) ε) ω)
    (hj : j ∈ latticeOceanPart (sphere (0 : V) 1)
      (localGroundStates (heisenbergCube V 2) (sphereProb V) ε) ω) :
    1 - ε ≤ ⟪(ω i : V), (ω j : V)⟫ := by
  have hmono : ∀ {x : Fin 2 → ℤ}, x ∈ latticeOceanPart (sphere (0 : V) 1)
      (localGroundStates (heisenbergCube V 2) (sphereProb V) ε) ω →
      x ∈ latticePattern (sphere (0 : V) 1) (heisenbergAligned V 2 ε) ω := by
    intro x hx
    have h1 : x ∈ latticePattern (sphere (0 : V) 1)
        (localGroundStates (heisenbergCube V 2) (sphereProb V) ε) ω :=
      SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hx)
    rw [mem_latticePattern] at h1 ⊢
    exact localGroundStates_subset_heisenbergAligned ε h1
  exact mem_alignedPair_of_mem_latticePattern hij (hmono hi) (hmono hj)

/-- **Georgii's conclusion in Example (18.19).**  For all sufficiently large `β` there is a
`μ ∈ 𝒢(βΦ)` inheriting the shift group of the plane and the reflections `r_1, r_2` such that,
with probability `1`, `V(G_ε(Φ), ·)` contains an ocean; by
`MeasureTheory.GibbsMeasure.real_inner_ge_of_mem_latticeOceanPart_localGroundStates` any two
adjacent spins of that ocean point in almost the same direction, `σ_i · σ_j ≥ 1 - ε`.

This is Corollary (18.18), second assertion, for the Heisenberg `C`-potential: measurability is
`measurable_heisenbergCube`, condition (iii) of (17.18) is `heisenbergCube_cubeRefl`, the lower
bound is `neg_four_le_heisenbergCube`, and the first alternative of condition (iv) is
`abs_heisenbergCube_le_four`. -/
theorem eventually_exists_mem_GP_measure_setOf_latticeOceanPart_heisenberg [Nontrivial V]
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∃ μ : ProbabilityMeasure ((Fin 2 → ℤ) → sphere (0 : V) 1),
      (∀ hM' : ∃ M' : ℝ, ∀ ζ, M' ≤ β * heisenbergCube V 2 ζ,
          μ ∈ GP (cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V 2 ζ)
            (sphereProb V) (measurable_heisenbergCube.const_mul β) hM')) ∧
        (∀ a : Fin 2 → ℤ, MeasurePreserving (shift (sphere (0 : V) 1) a).toFun
            (μ : Measure ((Fin 2 → ℤ) → sphere (0 : V) 1)) μ) ∧
          (∀ k : Fin 2, MeasurePreserving
            (siteEquiv (sphere (0 : V) 1) (latticeReflAt k)).toFun
            (μ : Measure ((Fin 2 → ℤ) → sphere (0 : V) 1)) μ) ∧
          (μ : Measure ((Fin 2 → ℤ) → sphere (0 : V) 1))
            {ω | (latticeOceanPart (sphere (0 : V) 1)
              (localGroundStates (heisenbergCube V 2) (sphereProb V) ε) ω).Nonempty} = 1 :=
  eventually_exists_mem_GP_measure_setOf_latticeOceanPart_localGroundStates_eq_one
    measurable_heisenbergCube (M := -4) (fun ζ ↦ neg_four_le_heisenbergCube ζ)
    (fun k ζ ↦ heisenbergCube_cubeRefl k ζ)
    (isCubeConfining_univ ⟨4, fun ζ ↦ abs_heisenbergCube_le_four ζ⟩) hε

/-! ### Georgii (18.19), second half: no low energy ocean at high temperature

The single-site conditional probability of a two-site event. -/

variable [Nontrivial V]

/-- **Georgii's `r(β, ε)`.**  The single-site Gibbs kernel of the Heisenberg `C`-potential
`βΦ` gives the event `{σ_i · σ_j ≥ 1 - ε}` at most `e^{2^d · 2dβ}` times the a priori measure of
a spherical cap of half-width `ε`; for `d = 2` the constant is Georgii's `e^{16β}`.  The two steps
are `Specification.apply_le_of_inter_subset` (the kernel does not move `σ_j`, so the event becomes
the single-site event `{σ_i · ω_j ≥ 1 - ε}`) and
`MeasureTheory.GibbsMeasure.cubeGibbsSpec_singleton_apply_preimage_eval_le`. -/
theorem cubeGibbsSpec_singleton_alignedPair_le {β : ℝ} (hβ : 0 ≤ β)
    (hφ : Measurable fun ζ : (Fin d → Fin 2) → sphere (0 : V) 1 ↦ β * heisenbergCube V d ζ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * heisenbergCube V d ζ) {ε ρ : ℝ}
    (hρ : ∀ u : sphere (0 : V) 1,
      sphereProb V {x : sphere (0 : V) 1 | 1 - ε ≤ ⟪(x : V), (u : V)⟫} ≤ ENNReal.ofReal ρ)
    {i j : Fin d → ℤ} (hij : i ≠ j) (η : (Fin d → ℤ) → sphere (0 : V) 1) :
    cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V d ζ) (sphereProb V) hφ hM
        {i} η (alignedPair V ε i j)
      ≤ ENNReal.ofReal (Real.exp (2 ^ d * (β * (2 * d)))) * ENNReal.ofReal ρ := by
  set B : Set (sphere (0 : V) 1) := {x | 1 - ε ≤ ⟪(x : V), ((η j : sphere (0 : V) 1) : V)⟫} with hB
  have hBm : MeasurableSet B :=
    measurableSet_le measurable_const (continuous_subtype_val.inner continuous_const).measurable
  calc cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V d ζ) (sphereProb V) hφ hM
          {i} η (alignedPair V ε i j)
      ≤ cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V d ζ) (sphereProb V) hφ hM
          {i} η ((fun σ : (Fin d → ℤ) → sphere (0 : V) 1 ↦ σ i) ⁻¹' B) := by
        refine Specification.apply_le_of_inter_subset _ _ _ (by simpa using fun h ↦ hij h.symm)
          (cylinderEvents_le_pi _ (measurableSet_cylinderEvents_alignedPair (V := V) ε i j)) ?_
        rintro ω ⟨hω, hωj⟩
        rw [Set.mem_preimage, hB, Set.mem_ofPred_eq, ← hωj]
        exact hω
    _ ≤ ENNReal.ofReal (Real.exp (2 ^ d * (β * (2 * d)))) * sphereProb V B :=
        cubeGibbsSpec_singleton_apply_preimage_eval_le hφ hM
          (fun ζ ζ' c h ↦ smul_heisenbergCube_sub_le hβ ζ ζ' c h) i η hBm
    _ ≤ ENNReal.ofReal (Real.exp (2 ^ d * (β * (2 * d)))) * ENNReal.ofReal ρ := by
        gcongr
        exact hρ (η j)

/-! ### The union bound over self-avoiding paths -/

/-- **Georgii (18.19), second half.**  At high temperature there is no low energy ocean: if the
a priori measure of a spherical cap of half-width `ε` is at most `ρ` and

`(2d - 1) e^{2^d · 2dβ} ρ < 1`

then, for every Gibbs measure `μ` of the Heisenberg `C`-potential `βΦ`, almost surely the origin
of `ℤ^d` — indeed any site — is in no infinite cluster of `V(G̃_ε, ·)`.  Georgii's estimate: an
infinite cluster through `a` carries a self-avoiding path of every length `n + 1` from `a`, there
are at most `2d (2d-1)^n` of these, and each of them has probability at most `r^{n+1}` by the
chain estimate `Specification.measure_chainEvent_le` applied to the single-site bound
`MeasureTheory.GibbsMeasure.cubeGibbsSpec_singleton_alignedPair_le`. -/
theorem measure_setOf_mem_infiniteClusters_heisenbergAligned_eq_zero {β : ℝ} (hβ : 0 ≤ β)
    (hφ : Measurable fun ζ : (Fin d → Fin 2) → sphere (0 : V) 1 ↦ β * heisenbergCube V d ζ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * heisenbergCube V d ζ)
    {μ : Measure ((Fin d → ℤ) → sphere (0 : V) 1)} [IsProbabilityMeasure μ]
    (hμ : (cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V d ζ) (sphereProb V)
      hφ hM).IsGibbsMeasure μ) {ε ρ : ℝ}
    (hρ : ∀ u : sphere (0 : V) 1,
      sphereProb V {x : sphere (0 : V) 1 | 1 - ε ≤ ⟪(x : V), (u : V)⟫} ≤ ENNReal.ofReal ρ)
    (hlt : ((2 * d - 1 : ℕ) : ℝ) * (Real.exp (2 ^ d * (β * (2 * d))) * ρ) < 1)
    (a : Fin d → ℤ) :
    μ {ω | a ∈ (latticeGraph d).infiniteClusters
      (latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)} = 0 := by
  classical
  set P : Set ((Fin d → ℤ) → sphere (0 : V) 1) :=
    {ω | a ∈ (latticeGraph d).infiniteClusters
      (latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)} with hP
  set A : (Fin d → ℤ) → (Fin d → ℤ) → Set ((Fin d → ℤ) → sphere (0 : V) 1) :=
    fun i j ↦ alignedPair V ε i j with hA
  set r : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 ^ d * (β * (2 * d))) * ρ) with hr
  have hrfac : r = ENNReal.ofReal (Real.exp (2 ^ d * (β * (2 * d)))) * ENNReal.ofReal ρ := by
    rw [hr, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hrne : r ≠ ⊤ := by rw [hr]; exact ENNReal.ofReal_ne_top
  -- Georgii's chain estimate along a self-avoiding path
  have hchain : ∀ l : List (Fin d → ℤ), l.Nodup →
      μ (Specification.chainEvent A l) ≤ r ^ (l.length - 1) := by
    refine Specification.measure_chainEvent_le hμ
      (fun i j ↦ measurableSet_cylinderEvents_alignedPair (V := V) ε i j) ?_
    intro i j hij η
    rw [hrfac]
    exact cubeGibbsSpec_singleton_alignedPair_le hβ hφ hM hρ hij η
  -- Georgii's `μ(a ∈ ξ(G̃_ε, ·)) ≤ 2d (2d - 1)^n r^{n+1}`
  have hdeg : ∀ v : Fin d → ℤ, (latticeGraph d).degree v ≤ 2 * d := fun v ↦
    le_of_eq (card_neighborFinset_latticeGraph d v)
  have hbound : ∀ n : ℕ,
      μ P ≤ ((2 * d * (2 * d - 1) ^ n : ℕ) : ℝ≥0∞) * r ^ (n + 1) := by
    intro n
    have hsub : P ⊆ ⋃ l ∈ (latticeGraph d).pathLists a (n + 1), Specification.chainEvent A l := by
      intro ω hω
      obtain ⟨x, p, hp, hlen, hsupp⟩ :=
        SimpleGraph.exists_isPath_length_eq_of_mem_infiniteClusters hω (n + 1)
      have hmem : p.support.reverse ∈ (latticeGraph d).pathLists a (n + 1) :=
        hlen ▸ SimpleGraph.reverse_support_mem_pathLists hp
      refine Set.mem_iUnion₂.2 ⟨p.support.reverse, hmem, ?_⟩
      obtain ⟨-, -, hch, -⟩ := SimpleGraph.mem_pathLists_iff.1 hmem
      refine Specification.mem_chainEvent_of_isChain
        (P := fun z ↦ z ∈ latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)
        (fun i j hij hi hj ↦ mem_alignedPair_of_mem_latticePattern hij hi hj) hch ?_
      intro z hz
      exact hsupp z (List.mem_reverse.1 hz)
    calc μ P ≤ μ (⋃ l ∈ (latticeGraph d).pathLists a (n + 1), Specification.chainEvent A l) :=
          measure_mono hsub
      _ ≤ ∑ l ∈ (latticeGraph d).pathLists a (n + 1), μ (Specification.chainEvent A l) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _l ∈ (latticeGraph d).pathLists a (n + 1), r ^ (n + 1) := by
          refine Finset.sum_le_sum fun l hl ↦ ?_
          obtain ⟨hlen, -, -, hnd⟩ := SimpleGraph.mem_pathLists_iff.1 hl
          simpa [hlen] using hchain l hnd
      _ = (((latticeGraph d).pathLists a (n + 1)).card : ℝ≥0∞) * r ^ (n + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * d * (2 * d - 1) ^ n : ℕ) : ℝ≥0∞) * r ^ (n + 1) := by
          gcongr
          exact_mod_cast SimpleGraph.card_pathLists_succ_le hdeg a n
  -- the bound tends to `0`
  have hq : ((2 * d - 1 : ℕ) : ℝ≥0∞) * r < 1 := by
    rw [hr, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_lt_one.2 hlt
  have htend : Filter.Tendsto
      (fun n : ℕ ↦ ((2 * d * (2 * d - 1) ^ n : ℕ) : ℝ≥0∞) * r ^ (n + 1)) Filter.atTop (𝓝 0) := by
    have hrw : ∀ n : ℕ, ((2 * d * (2 * d - 1) ^ n : ℕ) : ℝ≥0∞) * r ^ (n + 1)
        = (((2 * d : ℕ) : ℝ≥0∞) * r) * (((2 * d - 1 : ℕ) : ℝ≥0∞) * r) ^ n := by
      intro n
      push_cast
      rw [mul_pow, pow_succ]
      ring
    simp only [hrw]
    have hmul : Filter.Tendsto
        (fun n : ℕ ↦ (((2 * d : ℕ) : ℝ≥0∞) * r) * (((2 * d - 1 : ℕ) : ℝ≥0∞) * r) ^ n)
        Filter.atTop (𝓝 ((((2 * d : ℕ) : ℝ≥0∞) * r) * 0)) :=
      ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
        (Or.inr (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hrne))
    simpa using hmul
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto htend (Filter.Eventually.of_forall hbound))

/-- **Georgii (18.19), second half, as stated**: at high temperature `V(G̃_ε, ·)` almost surely
does not percolate, so in particular it almost surely contains no ocean. -/
theorem measure_setOf_infiniteClusters_heisenbergAligned_nonempty_eq_zero {β : ℝ} (hβ : 0 ≤ β)
    (hφ : Measurable fun ζ : (Fin d → Fin 2) → sphere (0 : V) 1 ↦ β * heisenbergCube V d ζ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * heisenbergCube V d ζ)
    {μ : Measure ((Fin d → ℤ) → sphere (0 : V) 1)} [IsProbabilityMeasure μ]
    (hμ : (cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V d ζ) (sphereProb V)
      hφ hM).IsGibbsMeasure μ) {ε ρ : ℝ}
    (hρ : ∀ u : sphere (0 : V) 1,
      sphereProb V {x : sphere (0 : V) 1 | 1 - ε ≤ ⟪(x : V), (u : V)⟫} ≤ ENNReal.ofReal ρ)
    (hlt : ((2 * d - 1 : ℕ) : ℝ) * (Real.exp (2 ^ d * (β * (2 * d))) * ρ) < 1) :
    μ {ω | ((latticeGraph d).infiniteClusters
      (latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)).Nonempty} = 0 := by
  have hcover : {ω : (Fin d → ℤ) → sphere (0 : V) 1 | ((latticeGraph d).infiniteClusters
        (latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)).Nonempty}
      = ⋃ a : Fin d → ℤ, {ω | a ∈ (latticeGraph d).infiniteClusters
        (latticePattern (sphere (0 : V) 1) (heisenbergAligned V d ε) ω)} := by
    ext ω
    simp [Set.Nonempty]
  rw [hcover]
  exact measure_iUnion_null fun a ↦
    measure_setOf_mem_infiniteClusters_heisenbergAligned_eq_zero hβ hφ hM hμ hρ hlt a

/-- **Georgii (18.19), second half, in the form of §18.1**: at high temperature `V(G̃_ε, ·)`
almost surely contains no ocean, so the low energy ocean of Corollary (18.18) really is a
low-temperature phenomenon.  An ocean is an infinite cluster
(`SimpleGraph.oceanPart_subset`). -/
theorem measure_setOf_latticeOceanPart_heisenbergAligned_nonempty_eq_zero {β : ℝ} (hβ : 0 ≤ β)
    (hφ : Measurable fun ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 ↦ β * heisenbergCube V 2 ζ)
    (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * heisenbergCube V 2 ζ)
    {μ : Measure ((Fin 2 → ℤ) → sphere (0 : V) 1)} [IsProbabilityMeasure μ]
    (hμ : (cubeGibbsSpec (sphere (0 : V) 1) (fun ζ ↦ β * heisenbergCube V 2 ζ) (sphereProb V)
      hφ hM).IsGibbsMeasure μ) {ε ρ : ℝ}
    (hρ : ∀ u : sphere (0 : V) 1,
      sphereProb V {x : sphere (0 : V) 1 | 1 - ε ≤ ⟪(x : V), (u : V)⟫} ≤ ENNReal.ofReal ρ)
    (hlt : ((2 * 2 - 1 : ℕ) : ℝ) * (Real.exp (2 ^ 2 * (β * (2 * 2))) * ρ) < 1) :
    μ {ω | (latticeOceanPart (sphere (0 : V) 1) (heisenbergAligned V 2 ε) ω).Nonempty} = 0 :=
  measure_mono_null (fun _ hω ↦ hω.mono SimpleGraph.oceanPart_subset)
    (measure_setOf_infiniteClusters_heisenbergAligned_nonempty_eq_zero hβ hφ hM hμ hρ hlt)

end Sphere

end MeasureTheory.GibbsMeasure

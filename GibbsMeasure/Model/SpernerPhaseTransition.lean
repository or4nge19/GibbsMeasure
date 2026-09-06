/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Topology.ClusterPtProd
public import GibbsMeasure.Mathlib.Topology.KKM
public import GibbsMeasure.Model.GroundStateRefinement
public import GibbsMeasure.Specification.CubePotentialConvergence
public import GibbsMeasure.Specification.ResolvingPerturbations
public import Mathlib.Topology.Compactness.CountablyCompact

/-!
# Georgii §19.2: a phase transition without symmetry, by Sperner's lemma

Georgii, *Gibbs Measures and Phase Transitions*, §19.2, and Theorem (19.6) of §19.1.
Throughout, `d = 2`, and `G_0, …, G_N ∈ ℰ^C` are `r`-symmetric sets satisfying the stability
condition (18.23)(a)(ii); `G = G_0 ∪ ⋯ ∪ G_N`.

Theorem (18.25) produced `N + 1` phases out of a *`Φ`-symmetric* stable partition: the symmetry
made all the events `A_n = {ξ⁰_P(G_n, ·) ≠ ∅}` equally likely, so all of them were non-null.
Without a symmetry only their union is known to be non-null, and Georgii restores the balance by
*tuning a perturbation*: the parameter space is the simplex `𝒫_N` of probability vectors, and the
Knaster–Kuratowski–Mazurkiewicz lemma (19.12) — `exists_mem_stdSimplex_forall_exists` of
`GibbsMeasure/Mathlib/Topology/KKM.lean` — produces a parameter at which *every* `A_n` is
non-null at once.

## Main results

* `exists_mem_stdSimplex_forall_exists_measure_le` — **Proposition (19.13), Step 1**: the KKM
  selection of the parameter `α*`.
* `le_cond_measure_zero_mem_latticeOceanPart` — **Proposition (19.13), Step 2**: the estimate
  `μ_n(0 ∈ ξ⁰_P(G_n, ·)) ≥ 1 - Nc` for the conditional measure.
* `exists_gibbsMeasure_family_of_isCountablyCompact` — **Proposition (19.13)**.
* `exists_correspondence_of_patternWeight_le` — **Proposition (19.14)**: Georgii's correspondence
  `α ↦ Γ(α)` and the verification of the hypotheses (i), (ii), (iii) of (19.13).
* `exists_gibbsMeasure_family_of_patternWeight_le` — (19.13) and (19.14) chained.
* `eventually_exists_gibbsMeasure_family_of_resolvesOn` — **Theorem (19.6)**, in the quantitative
  form of Georgii's proof (19.15): for a resolving perturbation and every small weight `t`, for
  all large `β` there is `h(β)` in a prescribed neighbourhood of the origin such that
  `βΦ^{h(β)}` has `N + 1` mutually singular shift-invariant Gibbs measures with the ocean and
  invariance properties of (19.6)(ii)–(iii).
* `le_encard_extremePoints_of_latticeOceanPart` — the count `|ex 𝒢_Θ(γ)| ≥ N + 1`, the last
  statement of (18.25), (19.6) and (19.7).

## General lemmas proved here whose home is elsewhere

Each carries a docstring naming its home; they are collected here because those files are being
edited concurrently.

* `setOf_mem_latticePattern_mem_localEvents`, `setOf_notMem_latticePattern_mem_localEvents`,
  `setOf_mem_latticePattern_iUnion`, `disjoint_setOf_mem_latticePattern` — the events
  `{i ∈ V(G, ·)}` (`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`).
* `isQuasiGibbsianWith_of_isGibbsMeasure_cubeGibbsSpec` and
  `le_measure_mem_latticeOceanPart_of_forall_le_pow` — **Theorem (18.17)** from the chessboard
  estimate alone, without `μ ∈ 𝒢₀(Φ)` (`GibbsMeasure/Model/LowEnergyOceans.lean`).
* `le_encard_extremePoints_invariantG_shiftGroup_of_separated` — Corollary (14.18) for measures
  separated by events (`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`).
* `patternWeight_le_of_measure_diff_eq_zero` — **Remark (18.9)(1)** up to null sets
  (`GibbsMeasure/Specification/LocalGroundStates.lean`).
* `le_crossingBound` — `t ≤ z(t)` below the trivial range
  (`GibbsMeasure/Model/StarCrossing.lean`).
* `IsCubeConfining.add_of_abs_le` — condition (17.18)(iv) under a bounded perturbation
  (`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`).

## Deviations from Georgii's statements

* Georgii's hypothesis (19.13)(iii), `μ(0 ∈ V(G_n, ·) | 0 ∈ V(G, ·)) < 1/N`, is stated here with
  the denominator cleared, `N μ(0 ∈ V(G_n, ·)) < μ(0 ∈ V(G, ·))`; the two are equivalent because
  hypothesis (ii) makes the denominator at least `1 - c > 0`.
* Georgii's (19.14)(I) is "`‖Ψ^{α_k}_C - Ψ^α_C‖ → 0` whenever `α_k → α`"; it is used, and
  therefore stated, *relative to the simplex* (`𝓝[𝒫_N] α`), which is what the construction of
  (19.15) delivers — the map `α ↦ h(α)` is continuous along `𝒫_N` only.
* Georgii's Theorem (19.6) asserts `h(β) → 0` and `μ_n(0 ∈ ξ⁰_P(G_n, ·)) → 1` as `β → ∞`.  Here
  the neighbourhood `U₀` of the origin and the weight `t` are parameters, and the conclusion
  holds eventually in `β` for each of them; the two limits are that statement quantified over
  `U₀` and over `t → 0`.

## What is *not* here

**Example (19.8)**, Georgii's `|ex 𝒢_Θ(βΦ + βh(β)Φ¹)| ≥ 3` for the Blume–Capel model, is not
formalised.  Everything §19.1 provides for it is in `GibbsMeasure/Model/BlumeCapel.lean`
(`resolves_blumeCapel`, `isPStablePartition_blumeCapel`, `attainsGroundEnergy_blumeCapel`), and
the two theorems it has to be fed into are `eventually_exists_gibbsMeasure_family_of_resolvesOn`
above and `exists_gibbsMeasure_refinement` (Corollary (19.7)) of
`GibbsMeasure/Model/GroundStateRefinement.lean`.  What is missing is the *model-specific* input:
the `r`-symmetry of `{G_1, G_2}` and of the refinement `{G_{2,1}, G_{2,2}}`, the invariance of
`Φ_C` and `Φ^1_C` under the reflections of the unit square, the boundedness of `Φ_C` (whence
`IsCubeConfining` with `K_ℓ = E`), and the spin flip as a `CubeTransformation` of `E = {-1,0,1}`
that preserves the counting measure, `Φ_C` and `Φ^1_C`, and exchanges `G_{2,1}` with `G_{2,2}`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Pointwise Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E]

/-! ### The events `{i ∈ V(G, ·)}` -/

section Pattern

variable {d : ℕ} {W : Set ((Fin d → Fin 2) → E)}

/-- **The event that a given site shows the pattern (18.3) is a local event.**  Its home is next
to `forall_notMem_latticePattern_mem_localEvents` in
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`, of which it is the complement at a
one-point `D`. -/
lemma setOf_mem_latticePattern_mem_localEvents (hW : MeasurableSet W) (i : Fin d → ℤ) :
    {ω : (Fin d → ℤ) → E | i ∈ latticePattern E W ω} ∈ localEvents (Fin d → ℤ) E := by
  classical
  have h := forall_notMem_latticePattern_mem_localEvents hW {i}
  have hrw : {ω : (Fin d → ℤ) → E | ∀ j ∈ ({i} : Finset (Fin d → ℤ)),
        j ∉ latticePattern E W ω}
      = {ω : (Fin d → ℤ) → E | i ∈ latticePattern E W ω}ᶜ := by
    ext ω
    simp
  rw [hrw] at h
  simpa using compl_mem_measurableCylinders h

/-- Georgii's (18.3) is a preimage in the pattern: showing the pattern `⋃_n G_n` at a site means
showing one of the `G_n` there. -/
lemma setOf_mem_latticePattern_iUnion {ι : Type*} (G : ι → Set ((Fin d → Fin 2) → E))
    (i : Fin d → ℤ) :
    {ω : (Fin d → ℤ) → E | i ∈ latticePattern E (⋃ n, G n) ω}
      = ⋃ n, {ω : (Fin d → ℤ) → E | i ∈ latticePattern E (G n) ω} := by
  ext _
  simp [mem_latticePattern]

/-- Distinct members of a stable partition are shown at distinct sites: the events
`{i ∈ V(G_m, ·)}` are pairwise disjoint. -/
lemma disjoint_setOf_mem_latticePattern {ι : Type*} {φ : ((Fin d → Fin 2) → E) → ℝ}
    {ν : Measure E} {P : Set (Fin d)} {G : ι → Set ((Fin d → Fin 2) → E)}
    (h : IsPStablePartition φ ν P G) (hP : P.Nonempty) {m n : ι} (hmn : m ≠ n)
    (i : Fin d → ℤ) :
    Disjoint {ω : (Fin d → ℤ) → E | i ∈ latticePattern E (G m) ω}
      {ω : (Fin d → ℤ) → E | i ∈ latticePattern E (G n) ω} :=
  Set.disjoint_left.2 fun _ hm hn ↦ hmn (h.eq_of_mem_latticePattern hP hm hn)

end Pattern

/-! ### Georgii, Proposition (19.13), Step 1: the Sperner selection -/

section Step1

open Peierls

variable {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}

/-- The comparison `μ(0 ∈ V(G_n, ·)) / μ(0 ∈ V(G, ·)) ≥ 1/N` with the denominator cleared. -/
private lemma inv_le_div_iff_le_mul {a b : ℝ≥0∞} {m : ℕ} (ha : a ≠ ∞) (hb : b ≠ ∞)
    (hb0 : 0 < b.toReal) :
    ((m : ℝ) + 1)⁻¹ ≤ a.toReal / b.toReal ↔ b ≤ ((m : ℝ≥0∞) + 1) * a := by
  have hKr : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hKtop : ((m : ℝ≥0∞) + 1) ≠ ∞ := by simp
  have hmul : (((m : ℝ≥0∞) + 1) * a).toReal = ((m : ℝ) + 1) * a.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [le_div_iff₀ hb0, inv_mul_le_iff₀ hKr,
    ← ENNReal.toReal_le_toReal hb (ENNReal.mul_ne_top hKtop ha), hmul]

/-- The comparison `μ(0 ∈ V(G_n, ·)) / μ(0 ∈ V(G, ·)) < 1/N` with the denominator cleared. -/
private lemma div_lt_inv_iff_mul_lt {a b : ℝ≥0∞} {m : ℕ} (ha : a ≠ ∞) (hb : b ≠ ∞)
    (hb0 : 0 < b.toReal) :
    a.toReal / b.toReal < ((m : ℝ) + 1)⁻¹ ↔ ((m : ℝ≥0∞) + 1) * a < b := by
  rw [← not_le, ← not_le, not_iff_not]
  exact inv_le_div_iff_le_mul ha hb hb0

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Proposition (19.13), Step 1.**  Under the countable compactness (i), the lower
bound (ii) and the boundary condition (iii), there is one parameter `α*` of the simplex at which
*every* member of the partition carries at least the fraction `1/N` of the conditional
probability of showing the pattern `G` at the origin.

This is Lemma (19.12) — the Knaster–Kuratowski–Mazurkiewicz lemma — applied to the sets
`K_n = {α : q_n(μ) ≥ 1/N for some μ ∈ Γ(α)}` through the selection principle
`exists_mem_stdSimplex_forall_exists`: they cover the simplex because the `q_n(μ)` sum to `1`
(the members of the partition are disjoint and cover `G`), they are closed by (i), and they miss
the `n`-th face by (iii). -/
theorem exists_mem_stdSimplex_forall_exists_measure_le
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ n, MeasurableSet (G n))
    {Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E))}
    (hΓne : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), (Γ α).Nonempty)
    (hcc : IsCountablyCompact {p : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E |
      p.1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ p.2.toMeasure ∈ Γ p.1})
    (hpos : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α, 0 < (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω})
    (hiii : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 → ∀ μ ∈ Γ α,
      ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        < (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}) :
    ∃ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), ∃ μ ∈ Γ α,
      (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}
        ≤ ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (G n) ω} := by
  classical
  set C : Set ((Fin 2 → ℤ) → E) :=
    {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω} with hCdef
  set Cn : Fin (N + 1) → Set ((Fin 2 → ℤ) → E) :=
    fun n ↦ {ω | (0 : Site) ∈ latticePattern E (G n) ω} with hCndef
  have hCnmeas : ∀ n, MeasurableSet (Cn n) :=
    fun n ↦ measurableSet_setOf_mem_latticePattern (hGmeas n) 0
  have hCU : C = ⋃ n, Cn n := setOf_mem_latticePattern_iUnion G 0
  have hCdisj : Pairwise (Function.onFun Disjoint Cn) := fun m n hmn ↦
    disjoint_setOf_mem_latticePattern hpart Set.univ_nonempty hmn 0
  -- the two evaluations are finite and the denominator is positive
  have hCtop : ∀ μ : ProbabilityMeasure ((Fin 2 → ℤ) → E),
      (μ : Measure ((Fin 2 → ℤ) → E)) C ≠ ∞ := fun μ ↦ measure_ne_top _ _
  have hCntop : ∀ (μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)) n,
      (μ : Measure ((Fin 2 → ℤ) → E)) (Cn n) ≠ ∞ := fun μ n ↦ measure_ne_top _ _
  have hposR : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
      0 < ((μ : Measure ((Fin 2 → ℤ) → E)) C).toReal := by
    intro α hα μ hμ
    exact ENNReal.toReal_pos (hpos α hα μ hμ).ne' (hCtop μ)
  -- Georgii's `q_n(μ) = μ(0 ∈ V(G_n, ·) | 0 ∈ V(G, ·))`
  set q : Fin (N + 1) → ProbabilityMeasure ((Fin 2 → ℤ) → E) → ℝ := fun n μ ↦
    ((μ : Measure ((Fin 2 → ℤ) → E)) (Cn n)).toReal
      / ((μ : Measure ((Fin 2 → ℤ) → E)) C).toReal with hqdef
  have hsum : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α, ∑ n, q n μ = 1 := by
    intro α hα μ hμ
    have hadd : (μ : Measure ((Fin 2 → ℤ) → E)) C
        = ∑ n, (μ : Measure ((Fin 2 → ℤ) → E)) (Cn n) := by
      rw [hCU, measure_iUnion hCdisj hCnmeas, tsum_fintype]
    have hreal : ((μ : Measure ((Fin 2 → ℤ) → E)) C).toReal
        = ∑ n, ((μ : Measure ((Fin 2 → ℤ) → E)) (Cn n)).toReal := by
      rw [hadd, ENNReal.toReal_sum fun n _ ↦ hCntop μ n]
    rw [hqdef, ← Finset.sum_div, ← hreal, div_self (hposR α hα μ hμ).ne']
  refine exists_mem_stdSimplex_forall_exists (Γ := Γ) (q := q) hΓne hsum ?_ ?_ |>.imp ?_
  · -- closedness of `K_n`, from the countable compactness (i)
    intro n
    refine IsSeqClosed.isClosed ?_
    intro αs α hαs hlim
    have hαmem : α ∈ stdSimplex ℝ (Fin (N + 1)) :=
      (isCompact_stdSimplex ℝ (Fin (N + 1))).isClosed.mem_of_tendsto hlim
        (Eventually.of_forall fun k ↦ (hαs k).1)
    choose μs hμs hqs using fun k ↦ (hαs k).2
    obtain ⟨p, hp, hcp⟩ := hcc.seq_clusterPt
      (fun k ↦ (αs k, (WithSetwiseTopology.ofMeasure (μs k) :
        WithLocalConvergence (Fin 2 → ℤ) E)))
      (Eventually.of_forall fun k ↦ ⟨(hαs k).1, hμs k⟩)
    have hp1 : p.1 = α := (hcp.fst).eq_of_tendsto hlim
    have hclosedS : IsClosed {x : WithLocalConvergence (Fin 2 → ℤ) E |
        (x.toMeasure : Measure ((Fin 2 → ℤ) → E)) C
          ≤ ((N : ℝ≥0∞) + 1) * (x.toMeasure : Measure ((Fin 2 → ℤ) → E)) (Cn n)} := by
      refine isClosed_le (WithSetwiseTopology.continuous_apply_enn ?_)
        (((ENNReal.continuous_const_mul (by simp)).comp
          (WithSetwiseTopology.continuous_apply_enn ?_)))
      · rw [hCdef]
        exact setOf_mem_latticePattern_mem_localEvents (MeasurableSet.iUnion hGmeas) 0
      · rw [hCndef]
        exact setOf_mem_latticePattern_mem_localEvents (hGmeas n) 0
    have hpmem : p.2 ∈ {x : WithLocalConvergence (Fin 2 → ℤ) E |
        (x.toMeasure : Measure ((Fin 2 → ℤ) → E)) C
          ≤ ((N : ℝ≥0∞) + 1) * (x.toMeasure : Measure ((Fin 2 → ℤ) → E)) (Cn n)} := by
      refine hclosedS.mem_of_mapClusterPt hcp.snd (Eventually.of_forall fun k ↦ ?_)
      exact (inv_le_div_iff_le_mul (hCntop (μs k) n) (hCtop (μs k))
        (hposR _ (hαs k).1 _ (hμs k))).1 (hqs k)
    refine ⟨hαmem, p.2.toMeasure, hp1 ▸ hp.2, ?_⟩
    exact (inv_le_div_iff_le_mul (hCntop p.2.toMeasure n) (hCtop p.2.toMeasure)
      (hposR α hαmem _ (hp1 ▸ hp.2))).2 hpmem
  · -- the boundary condition (iii)
    intro n α hα hαn μ hμ
    exact (div_lt_inv_iff_mul_lt (hCntop μ n) (hCtop μ) (hposR α hα μ hμ)).2
      (hiii α hα n hαn μ hμ)
  · rintro α ⟨hα, hforall⟩
    refine ⟨hα, fun n ↦ ?_⟩
    obtain ⟨μ, hμ, hle⟩ := hforall n
    exact ⟨μ, hμ, (inv_le_div_iff_le_mul (hCntop μ n) (hCtop μ) (hposR α hα μ hμ)).1 hle⟩

end Step1

/-! ### Georgii, Proposition (19.13), Step 2: the conditional measures -/

section Step2

open Peierls

variable {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Proposition (19.13), Step 2**, the estimate.  If a random field puts the origin
into the maximal ocean of `G = G_0 ∪ ⋯ ∪ G_N` with probability at least `1 - c` and shows the
member `G_n` at the origin with at least the fraction `1/N` of the conditional probability of
showing `G` there, then the event `A_n = {ξ⁰_P(G_n, ·) ≠ ∅}` is non-null and, conditionally on
it, the origin lies in the ocean of `G_n` with probability at least `1 - Nc`.

Georgii's computation: by the stability of the partition
`{0 ∈ ξ⁰_P(G_n, ·)} = {0 ∈ ξ⁰_P(G, ·)} ∖ {0 ∈ V(G ∖ G_n, ·)}`, whose mass is at least
`(1 - c) - (1 - 1/N) = 1/N - c > 0`; and `A_n ∖ {0 ∈ ξ⁰_P(G_n, ·)} ⊆ {0 ∉ ξ⁰_P(G, ·)}` has mass
at most `c`, so the conditional probability is at least `a_n/(a_n + c) ≥ 1 - Nc`. -/
theorem le_cond_measure_zero_mem_latticeOceanPart
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ n, MeasurableSet (G n))
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] {c : ℝ≥0∞}
    (hc : c < ((N : ℝ≥0∞) + 1)⁻¹)
    (hii : 1 - c ≤ μ {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}) {n : Fin (N + 1)}
    (hle : μ {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}
      ≤ ((N : ℝ≥0∞) + 1) * μ {ω | (0 : Site) ∈ latticePattern E (G n) ω}) :
    0 < μ {ω | (latticeOceanPart E (G n) ω).Nonempty} ∧
      1 - ((N : ℝ≥0∞) + 1) * c
        ≤ (μ[|{ω | (latticeOceanPart E (G n) ω).Nonempty}])
            {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω} := by
  classical
  set C : Set ((Fin 2 → ℤ) → E) :=
    {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω} with hCdef
  set Cn : Fin (N + 1) → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (0 : Site) ∈ latticePattern E (G m) ω} with hCndef
  set A : Set ((Fin 2 → ℤ) → E) := {ω | (latticeOceanPart E (G n) ω).Nonempty} with hAdef
  set B : Set ((Fin 2 → ℤ) → E) := {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω} with hBdef
  set BU : Set ((Fin 2 → ℤ) → E) :=
    {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω} with hBUdef
  have hCnmeas : ∀ m, MeasurableSet (Cn m) :=
    fun m ↦ measurableSet_setOf_mem_latticePattern (hGmeas m) 0
  have hCmeas : MeasurableSet C :=
    measurableSet_setOf_mem_latticePattern (MeasurableSet.iUnion hGmeas) 0
  have hAmeas : MeasurableSet A := measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n)
  have hBmeas : MeasurableSet B := measurableSet_setOf_mem_latticeOceanPart (hGmeas n) 0
  have hBUmeas : MeasurableSet BU :=
    measurableSet_setOf_mem_latticeOceanPart (MeasurableSet.iUnion hGmeas) 0
  -- the elementary inclusions
  have hocean_pattern : ∀ (W : Set ((Fin 2 → Fin 2) → E)) (ω : (Fin 2 → ℤ) → E),
      (0 : Site) ∈ latticeOceanPart E W ω → (0 : Site) ∈ latticePattern E W ω :=
    fun W ω h ↦ SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset h)
  have hBUC : BU ⊆ C := fun ω hω ↦ hocean_pattern _ ω hω
  have hBCn : B ⊆ Cn n := fun ω hω ↦ hocean_pattern _ ω hω
  have hCnC : Cn n ⊆ C := by
    rw [hCdef, hCndef, setOf_mem_latticePattern_iUnion G 0]
    exact Set.subset_iUnion (fun m ↦ {ω : (Fin 2 → ℤ) → E |
      (0 : Site) ∈ latticePattern E (G m) ω}) n
  have hBA : B ⊆ A := fun ω hω ↦ ⟨0, hω⟩
  -- Georgii: `{0 ∈ ξ⁰(G_n, ·)} = {0 ∈ ξ⁰(G, ·)} ∖ {0 ∈ V(G ∖ G_n, ·)}`
  have hBeq : B = BU \ (C \ Cn n) := by
    refine Set.Subset.antisymm (fun ω hω ↦ ⟨?_, ?_⟩) fun ω hω ↦ ?_
    · exact latticeOceanPart_mono (E := E) (Set.subset_iUnion G n) ω hω
    · exact fun hc' ↦ hc'.2 (hBCn hω)
    · obtain ⟨hωBU, hωnot⟩ := hω
      have hωCn : ω ∈ Cn n := by
        by_contra hcon
        exact hωnot ⟨hBUC hωBU, hcon⟩
      have hmemU : ω ∈ ⋃ m, {ω' : (Fin 2 → ℤ) → E |
          (0 : Site) ∈ latticeOceanPart E (G m) ω'} := by
        rw [← hpart.setOf_mem_latticeOceanPart_iUnion_eq (0 : Site)]
        exact hωBU
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hmemU
      have hmn : m = n := by
        by_contra hmn
        exact Set.disjoint_left.1
          (disjoint_setOf_mem_latticePattern hpart Set.univ_nonempty hmn (0 : Site))
          (hocean_pattern _ ω hm) hωCn
      subst hmn
      exact hm
  -- Georgii: `A_n ∖ {0 ∈ ξ⁰(G_n, ·)} ⊆ {0 ∉ ξ⁰(G, ·)}`
  have hABU : A \ B ⊆ BUᶜ := by
    rintro ω ⟨hωA, hωB⟩ hωBU
    have hoc : latticeOceanPart E (⋃ m, G m) ω = latticeOceanPart E (G n) ω :=
      hpart.latticeOceanPart_iUnion_eq hωA
    have : (0 : Site) ∈ latticeOceanPart E (G n) ω := by rw [← hoc]; exact hωBU
    exact hωB this
  -- the real arithmetic
  set K : ℝ≥0∞ := (N : ℝ≥0∞) + 1 with hKdef
  set Kr : ℝ := (N : ℝ) + 1 with hKrdef
  have hKr1 : (1 : ℝ) ≤ Kr := by
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    rw [hKrdef]; linarith
  have hKr0 : (0 : ℝ) < Kr := lt_of_lt_of_le zero_lt_one hKr1
  have hKtop : K ≠ ∞ := by simp [hKdef]
  have hKtoReal : K.toReal = Kr := by
    rw [hKdef, hKrdef, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_one]
    norm_num
  have hKinvtop : K⁻¹ ≠ ∞ := by simp [hKdef]
  have hctop : c ≠ ∞ := hc.ne_top
  set cr : ℝ := c.toReal with hcrdef
  have hcr0 : 0 ≤ cr := ENNReal.toReal_nonneg
  have hcrlt : cr < Kr⁻¹ := by
    have := (ENNReal.toReal_lt_toReal hctop hKinvtop).2 hc
    rwa [ENNReal.toReal_inv, hKtoReal] at this
  have hK1 : (1 : ℝ≥0∞) ≤ K := by
    rw [hKdef]; exact le_add_self
  have hc1 : c ≤ 1 := (hc.le.trans (ENNReal.inv_le_one.2 hK1))
  set b : ℝ := (μ C).toReal with hbdef
  set a : ℝ := (μ (Cn n)).toReal with hadef
  set u : ℝ := (μ BU).toReal with hudef
  set an : ℝ := (μ B).toReal with handef
  set w : ℝ := (μ A).toReal with hwdef
  have hb1 : b ≤ 1 := by
    rw [hbdef]; simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := C))
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have han0 : 0 ≤ an := ENNReal.toReal_nonneg
  have hu1 : u ≤ 1 := by
    rw [hudef]; simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := BU))
  have hab : a ≤ b := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hCnC)
  have hbKa : b ≤ Kr * a := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hKtop (measure_ne_top _ _)) hle
    rwa [ENNReal.toReal_mul, hKtoReal] at this
  have hu : 1 - cr ≤ u := by
    have h1 := ENNReal.toReal_mono (measure_ne_top _ _) hii
    rwa [ENNReal.toReal_sub_of_le hc1 ENNReal.one_ne_top, ENNReal.toReal_one] at h1
  -- `μ(0 ∈ ξ⁰(G_n, ·)) ≥ (1 - c) - (1 - 1/N)`
  have hdiff : (μ (C \ Cn n)).toReal = b - a := by
    rw [measure_sdiff hCnC (hCnmeas n).nullMeasurableSet (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le (measure_mono hCnC) (measure_ne_top _ _)]
  have hanb : u - (b - a) ≤ an := by
    have hsub : BU ⊆ B ∪ (C \ Cn n) := by
      intro ω hω
      by_cases hcn : ω ∈ C \ Cn n
      · exact Or.inr hcn
      · exact Or.inl (hBeq ▸ ⟨hω, hcn⟩)
    have h1 : μ BU ≤ μ B + μ (C \ Cn n) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hdiff] at h2
    linarith
  have han : Kr⁻¹ - cr ≤ an := by
    have hbK : b / Kr ≤ a := by rw [div_le_iff₀ hKr0]; nlinarith
    have hb2 : b - b / Kr ≤ 1 - Kr⁻¹ := by
      rw [div_eq_mul_inv]
      nlinarith [inv_nonneg.2 hKr0.le, inv_le_one_of_one_le₀ hKr1]
    linarith
  have hanpos : 0 < an := lt_of_lt_of_le (by linarith) han
  have hwpos : 0 < w := by
    refine lt_of_lt_of_le hanpos ?_
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hBA)
  have hApos : 0 < μ A := by
    rw [pos_iff_ne_zero]
    intro h0
    rw [hwdef, h0, ENNReal.toReal_zero] at hwpos
    exact lt_irrefl 0 hwpos
  -- `μ(A_n) - μ(0 ∈ ξ⁰(G_n, ·)) ≤ c`
  have hw : w ≤ an + cr := by
    have h1 : μ A ≤ μ B + μ BUᶜ :=
      (measure_mono (fun ω hω ↦ by
        by_cases hb : ω ∈ B
        · exact Or.inl hb
        · exact Or.inr (hABU ⟨hω, hb⟩)) : μ A ≤ μ (B ∪ BUᶜ)).trans (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono (by finiteness) h1
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      prob_compl_eq_one_sub hBUmeas,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one] at h2
    linarith
  refine ⟨hApos, ?_⟩
  -- the conditional probability
  have hcond : ((μ[|A]) B).toReal = an / w := by
    rw [cond_apply hAmeas, Set.inter_eq_self_of_subset_right hBA, ENNReal.toReal_mul,
      ENNReal.toReal_inv, div_eq_inv_mul]
  have hfinal : 1 - Kr * cr ≤ an / w := by
    rw [le_div_iff₀ hwpos]
    nlinarith [mul_nonneg hcr0 (sub_nonneg.2 (show (1 : ℝ) ≤ Kr * (an + cr) by nlinarith))]
  rcases le_or_gt 1 (K * c) with hKc | hKc
  · simp [tsub_eq_zero_of_le hKc]
  · have hKcR : (K * c).toReal = Kr * cr := by
      rw [ENNReal.toReal_mul, hKtoReal]
    have hprob : IsProbabilityMeasure (μ[|A]) := cond_isProbabilityMeasure hApos.ne'
    rw [← ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top _ _),
      ENNReal.toReal_sub_of_le hKc.le ENNReal.one_ne_top, ENNReal.toReal_one, hKcR, hcond]
    exact hfinal

end Step2

/-! ### Georgii, Proposition (19.13) -/

section Prop1913

open Peierls

variable {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Proposition (19.13).**  Let `G_0, …, G_N ∈ ℰ^C` be `r`-symmetric sets satisfying
the stability condition (18.23)(a)(ii), `G = G_0 ∪ ⋯ ∪ G_N`, and let `(γ^α)_{α ∈ 𝒫_N}` be a
family of specifications indexed by the simplex of probability vectors of length `N + 1`.
Suppose each `α` carries a non-empty set `Γ(α)` of shift-invariant Gibbs measures for `γ^α`
such that

* (i) `Γ = {(α, μ) : α ∈ 𝒫_N, μ ∈ Γ(α)}` is countably compact in the product of the Euclidean
  topology of the simplex and the topology of local convergence;
* (ii) `μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - c` for all `μ ∈ ⋃_α Γ(α)`, where `0 ≤ c < 1/(N+1)`;
* (iii) `μ(0 ∈ V(G_n, ·) | 0 ∈ V(G, ·)) < 1/(N+1)` whenever `α(n) = 0` and `μ ∈ Γ(α)` — stated
  with the denominator cleared, which is equivalent because the denominator is at least
  `1 - c > 0`.

Then there is a parameter `α*` and `N + 1` mutually singular shift-invariant Gibbs measures
`μ_0, …, μ_N` for `γ^{α*}` with `μ_n(ξ⁰_P(G_n, ·) ≠ ∅) = 1` and
`μ_n(0 ∈ ξ⁰_P(G_n, ·)) ≥ 1 - (N+1)c`; moreover `τ(μ_n) = μ_n` for every cube transformation
`τ` with `τ G_n = G_n` that preserves every element of `⋃_α Γ(α)`.

The `μ_n` are the conditional measures `ν_n(· | ξ⁰_P(G_n, ·) ≠ ∅)` of measures `ν_n ∈ Γ(α*)`
selected by the Knaster–Kuratowski–Mazurkiewicz lemma
(`exists_mem_stdSimplex_forall_exists_measure_le`); conditioning stays inside the Gibbs measures
because `{ξ⁰_P(G_n, ·) ≠ ∅}` is a tail event (Theorem (7.7)(b)), and inside the shift-invariant
ones because the `G_n` are `r`-symmetric. -/
theorem exists_gibbsMeasure_family_of_isCountablyCompact
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ n, MeasurableSet (G n))
    (hGsym : ∀ n, IsRSymmetric E (G n))
    {γ : (Fin (N + 1) → ℝ) → Specification (Fin 2 → ℤ) E}
    {Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E))}
    (hΓne : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), (Γ α).Nonempty)
    (hΓgibbs : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
      Specification.IsGibbsMeasure (γ α) (μ : Measure ((Fin 2 → ℤ) → E)))
    (hΓshift : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α, ∀ a : Fin 2 → ℤ,
      MeasurePreserving (shift E a).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ)
    (hcc : IsCountablyCompact {p : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E |
      p.1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ p.2.toMeasure ∈ Γ p.1})
    {c : ℝ≥0∞} (hc : c < ((N : ℝ≥0∞) + 1)⁻¹)
    (hii : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
      1 - c ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω})
    (hiii : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 → ∀ μ ∈ Γ α,
      ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        < (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}) :
    ∃ α ∈ stdSimplex ℝ (Fin (N + 1)), ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (γ α) (ρ n)) ∧
      (∀ (n : Fin (N + 1)) (a : Fin 2 → ℤ),
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - ((N : ℝ≥0∞) + 1) * c
        ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
        (∀ β ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ β,
          MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) →
        τ.onCube.toFun '' G n = G n →
        MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) := by
  classical
  have hK1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) + 1 := le_add_self
  have hc1 : c < 1 := lt_of_lt_of_le hc (ENNReal.inv_le_one.2 hK1)
  -- Georgii's `μ(0 ∈ V(G, ·)) ≥ 1 - c > 0`
  have hpos : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
      0 < (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω} := by
    intro α hα μ hμ
    refine lt_of_lt_of_le (tsub_pos_of_lt hc1) ((hii α hα μ hμ).trans (measure_mono ?_))
    intro ω hω
    exact (SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hω) :
      (0 : Site) ∈ latticePattern E (⋃ m, G m) ω)
  obtain ⟨α, hα, hsel⟩ :=
    exists_mem_stdSimplex_forall_exists_measure_le hpart hGmeas hΓne hcc hpos hiii
  choose νs hνs hνle using hsel
  set A : Fin (N + 1) → Set ((Fin 2 → ℤ) → E) :=
    fun n ↦ {ω | (latticeOceanPart E (G n) ω).Nonempty} with hAdef
  have hAmeas : ∀ n, MeasurableSet (A n) :=
    fun n ↦ measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n)
  have hstep2 : ∀ n, 0 < (νs n : Measure ((Fin 2 → ℤ) → E)) (A n) ∧
      1 - ((N : ℝ≥0∞) + 1) * c
        ≤ ((νs n : Measure ((Fin 2 → ℤ) → E))[|A n])
            {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω} := fun n ↦
    le_cond_measure_zero_mem_latticeOceanPart hpart hGmeas hc
      (hii α hα (νs n) (hνs n)) (hνle n)
  have hA0 : ∀ n, (νs n : Measure ((Fin 2 → ℤ) → E)) (A n) ≠ 0 := fun n ↦ (hstep2 n).1.ne'
  refine ⟨α, hα, fun n ↦ (νs n : Measure ((Fin 2 → ℤ) → E))[|A n],
    fun n ↦ cond_isProbabilityMeasure (hA0 n), fun n ↦ ?_, fun n a ↦ ?_, fun m n hmn ↦ ?_,
    ?_, fun n ↦ cond_apply_self (hA0 n) (measure_ne_top _ _), fun n ↦ (hstep2 n).2,
    fun n τ hτ hGτ ↦ ?_⟩
  · exact isGibbsMeasure_cond_of_tail _ (hΓgibbs α hα (νs n) (hνs n))
      (tail_measurableSet_setOf_latticeOceanPart_nonempty (hGmeas n)) (hA0 n)
  · refine (hΓshift α hα (νs n) (hνs n) a).cond_of_preimage_eq (hAmeas n) ?_
    rw [hAdef, preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow,
      (hGsym n).preimage_tauPow]
  · refine ⟨(A m)ᶜ, (hAmeas m).compl, ?_, ?_⟩
    · rw [cond_apply (hAmeas m), Set.inter_compl_self, measure_empty, mul_zero]
    · rw [compl_compl, cond_apply (hAmeas n),
        Set.disjoint_iff_inter_eq_empty.1
          ((hpart.disjoint_setOf_latticeOceanPart_nonempty hmn).symm),
        measure_empty, mul_zero]
  · intro m n hmn
    by_contra hne
    have h1 : ((νs m : Measure ((Fin 2 → ℤ) → E))[|A m]) (A m) = 1 :=
      cond_apply_self (hA0 m) (measure_ne_top _ _)
    rw [show ((νs m : Measure ((Fin 2 → ℤ) → E))[|A m])
        = (νs n : Measure ((Fin 2 → ℤ) → E))[|A n] from hmn, cond_apply (hAmeas n),
      Set.disjoint_iff_inter_eq_empty.1
        (hpart.disjoint_setOf_latticeOceanPart_nonempty (Ne.symm hne)),
      measure_empty, mul_zero] at h1
    exact zero_ne_one h1
  · have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
    have hpre : τ.onCube.toFun ⁻¹' G n = G n := by
      conv_lhs => rw [← hGτ]
      exact Set.preimage_image_eq _ hinj
    refine (hτ α hα (νs n) (hνs n)).cond_of_preimage_eq (hAmeas n) ?_
    rw [hAdef, preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre]

end Prop1913

/-! ### The count of extreme shift-invariant Gibbs measures -/

section ExtremePoints

/-- **`N` shift-invariant Gibbs measures separated by a family of events give `|ex 𝒢_Θ(γ)| ≥ N`.**
The `i`-th measure carries the `i`-th event and misses the others, so the family is linearly
independent over `ℝ≥0∞`, and Corollary (14.18) for the shift group
(`le_encard_extremePoints_invariantG_shiftGroup_iff`) converts that into the count.

This is the general form of `le_encard_extremePoints_invariantG_shiftGroup_of_isRSymmetric` of
`GibbsMeasure/Model/DiscreteSymmetryBreaking.lean`, where it belongs: that statement is this one
for the conditional measures of a single `μ ∈ 𝒢₀(Φ)` on the events `{ξ⁰_P(G_n, ·) ≠ ∅}`. -/
theorem le_encard_extremePoints_invariantG_shiftGroup_of_separated {S : Type*} [AddCommGroup S]
    [Countable S] [Infinite S] [DecidableEq S] [StandardBorelSpace E] {γ : Specification S E}
    {F : ℕ → Finset S}
    (hFol : ∀ g : S, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) atTop (𝓝 0))
    {C : ℝ≥0∞} (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ k, ((F k - F k + F k).card : ℝ≥0∞) ≤ C * (F k).card) (hC' : C ≠ ∞)
    {n : ℕ} {ρ : Fin n → Measure (S → E)} {A : Fin n → Set (S → E)}
    (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin n) (a : S), MeasurePreserving (shift E a).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    (n : ℕ∞) ≤ ((invariantG γ (shiftGroup S E)).extremePoints ℝ≥0∞).encard :=
  (le_encard_extremePoints_invariantG_shiftGroup_iff hFol hF hne hC hC' n).2
    ⟨ρ, fun i ↦ mem_invariantG.2 ⟨hprob i, hgibbs i,
      smulInvariantMeasure_iff_forall_measurePreserving.2 (by
        rintro τ ⟨a, rfl⟩; exact hinv i a)⟩,
      linearIndependent_of_measure_eq_one_of_measure_eq_zero hself hother⟩

/-- **The last sentence of Georgii's Proposition (19.13)**: over a standard Borel state space the
`N + 1` measures of `exists_gibbsMeasure_family_of_isCountablyCompact` witness
`|ex 𝒢_Θ(γ^{α*})| ≥ N + 1`.  The Følner sequence is the cube sequence of
`exists_monotone_regular_foelner_cube`. -/
theorem le_encard_extremePoints_invariantG_shiftGroup_of_separated_lattice {ι : Type*}
    [Finite ι] [Nonempty ι] [StandardBorelSpace E]
    {γ : Specification (ι → ℤ) E}
    {n : ℕ} {ρ : Fin n → Measure ((ι → ℤ) → E)} {A : Fin n → Set ((ι → ℤ) → E)}
    (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin n) (a : ι → ℤ), MeasurePreserving (shift E a).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i (A i) = 1) (hother : ∀ i j, i ≠ j → ρ j (A i) = 0) :
    (n : ℕ∞) ≤ ((invariantG γ (shiftGroup (ι → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨F, C, hF, hne, hFol, hC, hC', -⟩ := exists_monotone_regular_foelner_cube (ι := ι)
  exact le_encard_extremePoints_invariantG_shiftGroup_of_separated hFol hF hne hC hC'
    hprob hgibbs hinv hself hother

end ExtremePoints

/-! ### Georgii (18.16)–(18.17) from the chessboard estimate alone -/

section Percolation

open Peierls

variable {ν : Measure E} [IsProbabilityMeasure ν]

/-- **Every Gibbs measure of a `C`-potential is quasi-Gibbsian**, with the a priori measure of
the potential.  This is `isQuasiGibbsianWith_of_mem_GZero` of
`GibbsMeasure/Model/LowEnergyOceans.lean` with the hypothesis `μ ∈ 𝒢₀(Φ)` — which enters there
only through `mem_GP_of_mem_GZero` — replaced by the Gibbs property itself; its home is that
file. -/
theorem isQuasiGibbsianWith_of_isGibbsMeasure_cubeGibbsSpec {d : ℕ}
    {φ' : ((Fin d → Fin 2) → E) → ℝ} (hφ : Measurable φ') (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ' ζ)
    {μ : Measure ((Fin d → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : Specification.IsGibbsMeasure (cubeGibbsSpec E φ' ν hφ hM) μ) :
    IsQuasiGibbsianWith ν μ := by
  have := isPotential_cubePotential (E := E) (φ := φ') hφ
  exact isQuasiGibbsianWith_of_isGibbsMeasure_lambdaSpecification ν
    (Potential.isPremodifier_boltzmannFactor (Φ := cubePotential E φ') 1)
    (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec)
    (fun Λ η ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne') hμ

/-- **Georgii, Theorem (18.17), first assertion, from the chessboard estimate alone.**  A
shift-invariant quasi-Gibbsian random field satisfying `μ(D ∩ V(G, ·) = ∅) ≤ t^{|D|}` for all
finite `D` puts the origin into the maximal ocean of `V(G, ·)` with probability at least
`1 - 4 z(t)`.

`le_measure_mem_latticeOceanPart` of `GibbsMeasure/Model/LowEnergyOceans.lean`, whose home this
is, is the case `μ ∈ 𝒢₀(Φ)`, where the chessboard estimate is Lemma (18.10); Georgii's §19.2
needs it for the larger class `Γ(α)` of Proposition (19.14), whose defining property (i) *is*
the chessboard estimate. -/
theorem le_measure_mem_latticeOceanPart_of_forall_le_pow {G' : Set ((Fin 2 → Fin 2) → E)}
    (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) {t : ℝ≥0∞}
    (hcb : ∀ D : Finset (Fin 2 → ℤ), μ {ω | ∀ i ∈ D, i ∉ latticePattern E G' ω} ≤ t ^ D.card) :
    1 - 4 * crossingBound t ≤ μ {ω | (0 : Site) ∈ latticeOceanPart E G' ω} := by
  refine le_trans ?_ (measure_crossEvent_le (ν := ν) hG hGsym hq hshift)
  rw [crossEvent_eq]
  exact le_measure_forall_mem_infiniteClusters μ (fun ω ↦ latticePattern E G' ω) hcb

end Percolation

/-! ### Georgii, Proposition (19.14) -/

section Prop1914

open Peierls

variable {ν : Measure E} [IsProbabilityMeasure ν]

/-- Upper semicontinuity in the limit: a quantity below `e^{4ε} c` for every `ε > 0` is below
`c`. -/
private lemma le_of_forall_exp_mul_le {a c : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal (Real.exp (4 * ε)) * c) : a ≤ c := by
  have hcont : Continuous fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h1 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε))) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (Real.exp (4 * (0 : ℝ))))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0
  have h2 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) * c) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have h3 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) * c) (𝓝[>] (0 : ℝ))
        (𝓝 (1 * c)) := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    simpa using h3
  exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun ε hε ↦ h ε hε)

/-- Georgii's `{i ∈ V(G, ·)}` as the complementary pattern event at a single site. -/
lemma setOf_forall_notMem_latticePattern_compl {d : ℕ} (W : Set ((Fin d → Fin 2) → E))
    (i : Fin d → ℤ) :
    {ω : (Fin d → ℤ) → E | ∀ j ∈ ({i} : Finset (Fin d → ℤ)), j ∉ latticePattern E Wᶜ ω}
      = {ω : (Fin d → ℤ) → E | i ∈ latticePattern E W ω} := by
  ext ω
  simp [mem_latticePattern]

/-- **The event that a given site does *not* show the pattern (18.3) is a local event.** -/
lemma setOf_notMem_latticePattern_mem_localEvents {d : ℕ} {W : Set ((Fin d → Fin 2) → E)}
    (hW : MeasurableSet W) (i : Fin d → ℤ) :
    {ω : (Fin d → ℤ) → E | i ∉ latticePattern E W ω} ∈ localEvents (Fin d → ℤ) E := by
  classical
  have h := forall_notMem_latticePattern_mem_localEvents hW {i}
  have hrw : {ω : (Fin d → ℤ) → E | ∀ j ∈ ({i} : Finset (Fin d → ℤ)),
        j ∉ latticePattern E W ω}
      = {ω : (Fin d → ℤ) → E | i ∉ latticePattern E W ω} := by
    ext ω
    simp
  rwa [hrw] at h

lemma isRSymmetric_iUnion {d : ℕ} {ι : Type*} {W : ι → Set ((Fin d → Fin 2) → E)}
    (hW : ∀ n, IsRSymmetric E (W n)) : IsRSymmetric E (⋃ n, W n) := by
  intro k
  rw [Set.preimage_iUnion]
  exact Set.iUnion_congr fun n ↦ hW n k

variable [StandardBorelSpace E] {N : ℕ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {ψ : (Fin (N + 1) → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ} {K : ℕ → Set E} {t : ℝ≥0∞}

/-- **Georgii, Proposition (19.14).**  Let `(E, ℰ)` be standard Borel, `G_0, …, G_N` measurable
`r`-symmetric pattern sets and `(Ψ^α)_{α ∈ 𝒫_N}` a family of `C`-potentials with a common
confining sequence `(K_ℓ)` of Georgii (17.18)(iv), such that

* (I) `α ↦ Ψ^α_C` is continuous in the uniform norm;
* (II) `t(G, Ψ^α) ≤ t` for all `α`, where `G = G_0 ∪ ⋯ ∪ G_N`;
* (III) `(N+1) t(E^C ∖ G_n, Ψ^α) < 1 - t` whenever `α(n) = 0`.

Then Georgii's correspondence

`Γ(α) = {μ ∈ 𝒢_Θ(Ψ^α) : μ(D ∩ V(G, ·) = ∅) ≤ t^{|D|}, μ(i ∈ V(G_n, ·)) ≤ t(E^C ∖ G_n, Ψ^α),`
`  μ(i ∉ V(K_ℓ^C, ·)) ≤ t(K_ℓ^C, Ψ^α), and τ(μ) = μ for every common symmetry τ}`

satisfies the hypotheses (i), (ii) (with `c = 4 z(t)`) and (iii) of Proposition (19.13).

Non-emptiness is `𝒢₀(Ψ^α) ⊆ Γ(α)`, which is Lemma (18.10) and Remark (18.22), together with
Proposition (18.12); hypothesis (ii) is Theorem (18.17) in the form
`le_measure_mem_latticeOceanPart_of_forall_le_pow`, which needs only the chessboard estimate;
hypothesis (iii) is condition (III); and hypothesis (i) is Corollary (4.13) plus
Proposition (4.19) — the latter for a `C`-potential, `tendsto_dist_action_cubeGibbsSpec`. -/
theorem exists_correspondence_of_patternWeight_le
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n))
    (hψmeas : ∀ α, Measurable (ψ α)) (hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψ α ζ)
    (hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψ α (cubeRefl E k ζ) = ψ α ζ)
    (hKconf : ∀ α, IsCubeConfining (ψ α) ν K)
    (hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψ α' ζ - ψ α ζ| ≤ ε)
    (hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), patternWeight (ψ α) ν (⋃ m, G m) ≤ t)
    (hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * patternWeight (ψ α) ν (G n)ᶜ < 1 - t) :
    ∃ Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E)),
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), (Γ α).Nonempty) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
        Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α))
          (μ : Measure ((Fin 2 → ℤ) → E))) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α, ∀ a : Fin 2 → ℤ,
        MeasurePreserving (shift E a).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
      IsCountablyCompact {p : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E |
        p.1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ p.2.toMeasure ∈ Γ p.1} ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
        1 - 4 * crossingBound t
          ≤ (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 → ∀ μ ∈ Γ α,
        ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticePattern E (G n) ω}
          < (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}) ∧
      (∀ (τ : CubeTransformation E 2),
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
          MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) := by
  classical
  have hE : Nonempty E := ν.nonempty_of_neZero
  have hGU : MeasurableSet (⋃ m, G m) := MeasurableSet.iUnion hGmeas
  have hGUsym : IsRSymmetric E (⋃ m, G m) := isRSymmetric_iUnion hGsym
  set Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E)) := fun α ↦
    {μ | Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α))
          (μ : Measure ((Fin 2 → ℤ) → E)) ∧
      (∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun
          (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
      (∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | ∀ i ∈ D, i ∉ latticePattern E (⋃ m, G m) ω} ≤ t ^ D.card) ∧
      (∀ (n : Fin (N + 1)) (i : Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | i ∈ latticePattern E (G n) ω} ≤ patternWeight (ψ α) ν (G n)ᶜ) ∧
      (∀ (ℓ : ℕ) (i : Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | i ∉ latticePattern E (cubePi 2 E (K ℓ)) ω}
            ≤ patternWeight (ψ α) ν (cubePi 2 E (K ℓ))) ∧
      (∀ τ : CubeTransformation E 2,
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ)} with hΓdef
  -- Georgii: `𝒢₀(Ψ^α) ⊆ Γ(α)`
  have hGZero : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      ∀ μ ∈ GZero E (ψ α) ν, μ ∈ Γ α := by
    intro α hα μ hμ
    refine ⟨mem_GP_of_mem_GZero (hψmeas α) (hψM α) hμ,
      fun a ↦ measurePreserving_shift_of_mem_GZero (hψmeas α) hμ a, fun D ↦ ?_,
      fun n i ↦ ?_, fun ℓ i ↦ ?_, fun τ hτ ↦ ?_⟩
    · refine le_trans (forall_notMem_latticePattern_le_patternWeight (d := 1) (hψmeas α)
        (hψM α).choose_spec (hψrefl α) hGU hGUsym hμ D) ?_
      exact pow_le_pow_left' (hII α hα) D.card
    · have h := forall_notMem_latticePattern_le_patternWeight (d := 1) (hψmeas α)
        (hψM α).choose_spec (hψrefl α) (hGmeas n).compl (isRSymmetric_compl (hGsym n)) hμ {i}
      rwa [setOf_forall_notMem_latticePattern_compl, Finset.card_singleton, pow_one] at h
    · have h := forall_notMem_latticePattern_le_patternWeight (d := 1) (hψmeas α)
        (hψM α).choose_spec (hψrefl α) (measurableSet_cubePi ((hKconf α).measurableSet ℓ))
        isRSymmetric_cubePi hμ {i}
      rw [Finset.card_singleton, pow_one] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext ω
      simp
    · exact (hτ α hα).measurePreserving_onLattice_of_mem_GZero (hψmeas α) (hψM α) hμ
  refine ⟨Γ, fun α hα ↦ ?_, fun α _ μ hμ ↦ hμ.1, fun α _ μ hμ ↦ hμ.2.1, ?_,
    fun α hα μ hμ ↦ ?_, fun α hα n hαn μ hμ ↦ ?_, fun τ hτ α hα μ hμ ↦ hμ.2.2.2.2.2 τ hτ⟩
  · -- non-emptiness, Georgii's `Γ(α) ⊇ 𝒢₀(Ψ^α) ≠ ∅` (Proposition (18.12))
    obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (ν := ν) (hψmeas α) (hψM α).choose_spec
      (hψrefl α) (hKconf α) (fun _ ↦ Classical.arbitrary E)
    exact ⟨μ, hGZero α hα μ hμ⟩
  · -- (i): countable compactness
    rw [isCountablyCompact_iff_seq_clusterPt]
    intro p hp
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hp
    set q : ℕ → (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E :=
      fun k ↦ p (k + k₀) with hqdef
    have hq : ∀ k, (q k).1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ (q k).2.toMeasure ∈ Γ (q k).1 :=
      fun k ↦ hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    obtain ⟨α, hα, ex, hexmono, hexlim⟩ :=
      (isCompact_stdSimplex ℝ (Fin (N + 1))).tendsto_subseq (fun k ↦ (hq k).1)
    set βs : ℕ → Fin (N + 1) → ℝ := fun j ↦ (q (ex j)).1 with hβsdef
    set ms : ℕ → ProbabilityMeasure ((Fin 2 → ℤ) → E) := fun j ↦ (q (ex j)).2.toMeasure with hmsdef
    have hβlim : Tendsto βs atTop (𝓝 α) := hexlim
    have hmsΓ : ∀ j, ms j ∈ Γ (βs j) := fun j ↦ (hq (ex j)).2
    -- Georgii's condition (I) along the subsequence
    have hβlim' : Tendsto βs atTop (𝓝[stdSimplex ℝ (Fin (N + 1))] α) :=
      tendsto_nhdsWithin_iff.2 ⟨hβlim, Eventually.of_forall fun j ↦ (hq (ex j)).1⟩
    have hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ ζ, |ψ (βs j) ζ - ψ α ζ| ≤ ε :=
      fun ε hε ↦ hβlim'.eventually (hI α hα ε hε)
    have hMα : ∀ ζ, (hψM α).choose ≤ ψ α ζ := (hψM α).choose_spec
    -- the semicontinuity (18.9)(3) along the subsequence
    have hsemi : ∀ (W : Set ((Fin 2 → Fin 2) → E)) (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
        patternWeight (ψ (βs j)) ν W
          ≤ ENNReal.ofReal (Real.exp (4 * ε)) * patternWeight (ψ α) ν W := by
      intro W ε hε
      filter_upwards [hunif ε hε] with j hj
      exact patternWeight_le_of_abs_sub_le hMα hε.le hj W
    have : ∀ j, Potential.IsPotential (cubePotential E (ψ (βs j))) :=
      fun j ↦ isPotential_cubePotential (hψmeas _)
    have hadm : ∀ j, Specification.IsPremodifierAdmissible (S := Fin 2 → ℤ) (E := E) ν
        ((cubePotential E (ψ (βs j))).boltzmannFactor 1) := fun j ↦
      (Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible ν _).2
        (isSigmaFiniteLambdaAdmissible_cubePotential (hψmeas _) (hψM (βs j)).choose_spec)
    -- Georgii's Corollary (4.13)
    have hle : LocallyEquicontinuous atTop ms := by
      refine Potential.locallyEquicontinuous_of_confinement_hamiltonian
        (fun j ↦ cubePotential E (ψ (βs j))) ν 1 hadm (fun j ↦ periodicCube 2 j)
        Potential.tendsto_latticeBox_atTop ms ms ?_ K (fun ℓ ↦ (hKconf α).measurableSet ℓ)
        (fun ℓ ↦ (hKconf α).measure_pos ℓ) ?_ ?_
      · intro j
        have hspec : cubeGibbsSpec E (ψ (βs j)) ν (hψmeas _) (hψM (βs j))
            = (Specification.isssd (S := Fin 2 → ℤ) (E := E) ν).modification
              (Specification.premodifierNorm ν
                ((cubePotential E (ψ (βs j))).boltzmannFactor 1))
              (Specification.IsPremodifier.isModifier_premodifierNorm ν
                (Potential.isPremodifier_boltzmannFactor
                  (Φ := cubePotential E (ψ (βs j))) 1) (hadm j)) :=
          Specification.lambdaSpecification_eq_modification_isssd ν
            (Potential.isPremodifier_boltzmannFactor (Φ := cubePotential E (ψ (βs j))) 1)
            (isSigmaFiniteLambdaAdmissible_cubePotential (hψmeas _) (hψM (βs j)).choose_spec)
        rw [← hspec]
        exact (Subtype.ext (Specification.isGibbsMeasure_iff_forall_bind_eq.1
          (hmsΓ j).1 (periodicCube 2 j))).symm
      · -- Georgii's hypothesis (ii)
        intro i
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          (tendsto_patternWeight_cubePi hMα (hKconf α))
          (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun ℓ ↦ ?_)
        refine le_of_forall_exp_mul_le fun ε hε ↦ ?_
        refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [hsemi (cubePi 2 E (K ℓ)) ε hε] with j hj
        refine le_trans (le_trans (measure_mono ?_) ((hmsΓ j).2.2.2.2.1 ℓ i)) hj
        exact fun ω hω hc ↦ hω (mem_of_mem_latticePattern_cubePi hc)
      · -- Georgii's hypothesis (iii)
        intro Λ
        refine ⟨Λ ∪ (cubeInteractingSet 2 Λ).biUnion id, Finset.subset_union_left, fun ℓ ↦ ?_⟩
        obtain ⟨cα, hcα⟩ := (hKconf α).bddOn ℓ
        refine ⟨(Potential.interactingSupport (Φ := cubePotential E (ψ α)) Λ).card * cα
          + (cubeInteractingSet 2 Λ).card * 1, ?_⟩
        have hpotα : Potential.IsPotential (cubePotential E (ψ α)) :=
          isPotential_cubePotential (hψmeas α)
        filter_upwards [hunif 1 one_pos] with j hj ω hω
        have hωsub : ∀ i ∈ hamSupport (ψ α) Λ, ω i ∈ K ℓ := by
          intro i hi
          refine hω i ?_
          rcases Finset.mem_union.1 hi with h | h
          · exact Finset.mem_union_left _ h
          · obtain ⟨A, hA, hiA⟩ := Finset.mem_biUnion.1 h
            refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨A, ?_, hiA⟩)
            exact interactingSupport_cubePotential_subset (hψmeas α) Λ hA
        have h1 : |(cubePotential E (ψ α)).hamiltonian Λ ω|
            ≤ (Potential.interactingSupport (Φ := cubePotential E (ψ α)) Λ).card * cα := by
          rw [Potential.hamiltonian_eq_interactingHamiltonian]
          exact abs_interactingHamiltonian_cubePotential_le (d := 1) hcα Λ hωsub
        have h2 := abs_hamiltonian_cubePotential_sub_le (hψmeas (βs j)) (hψmeas α) hj Λ ω
        have h3 := abs_sub_abs_le_abs_sub ((cubePotential E (ψ (βs j))).hamiltonian Λ ω)
          ((cubePotential E (ψ α)).hamiltonian Λ ω)
        calc |(cubePotential E (ψ (βs j))).hamiltonian Λ ω|
            ≤ |(cubePotential E (ψ α)).hamiltonian Λ ω|
              + |(cubePotential E (ψ (βs j))).hamiltonian Λ ω
                - (cubePotential E (ψ α)).hamiltonian Λ ω| := by linarith
          _ ≤ _ := by linarith
    obtain ⟨m, hm⟩ := exists_mapClusterPt_of_locallyEquicontinuous
      (μs := fun j ↦ (WithSetwiseTopology.ofMeasure (ms j) : WithLocalConvergence _ E)) hle
    -- the pair `(α, m)` is a cluster point of the original sequence
    have heq : (fun j ↦ ((βs j),
        (WithSetwiseTopology.ofMeasure (ms j) : WithLocalConvergence (Fin 2 → ℤ) E)))
        = q ∘ ex := rfl
    have hpairsub : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
        atTop (q ∘ ex) := heq ▸ hβlim.mapClusterPt_prod hm
    have hpair : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
        atTop p := by
      have h1 : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
          atTop q := MapClusterPt.of_comp hexmono.tendsto_atTop hpairsub
      have h2 : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
          atTop (p ∘ fun k ↦ k + k₀) := h1
      exact MapClusterPt.of_comp (tendsto_add_atTop_nat k₀) h2
    refine ⟨(α, m), ⟨hα, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpair⟩
    · -- the cluster point is a Gibbs measure for `Ψ^α` (Georgii (4.19) and (4.17))
      refine mem_GP_of_mapClusterPt (l := atTop)
        (isQuasilocal_cubeGibbsSpec (hψmeas α) (hψM α))
        (γs := fun j ↦ cubeGibbsSpec E (ψ (βs j)) ν (hψmeas _) (hψM (βs j)))
        (Λs := fun j ↦ periodicCube 2 j) (νs := ms) Potential.tendsto_latticeBox_atTop
        (fun Λ f hf ↦ tendsto_dist_action_cubeGibbsSpec_of_eventually (ν := ν)
          (fun j ↦ hψmeas _) (fun j ↦ hψM (βs j)) (hψmeas α) (hψM α) hunif Λ
          (measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hf))) ?_
      refine hm.congrFun ?_
      filter_upwards with j
      exact congrArg WithSetwiseTopology.ofMeasure
        (Subtype.ext (Specification.isGibbsMeasure_iff_forall_bind_eq.1
          (hmsΓ j).1 (periodicCube 2 j))).symm
    · -- shift invariance
      intro a
      exact measurePreserving_of_mapClusterPt (shift E a).measurable_toFun
        (fun A hA ↦ (shift E a).preimage_mem_localEvents hA) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.1 a)
    · -- the chessboard estimate
      intro D
      exact eval_le_of_mapClusterPt (forall_notMem_latticePattern_mem_localEvents hGU D) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.2.1 D)
    · -- the bound by `t(E^C ∖ G_n, Ψ^α)`
      intro n i
      refine le_of_forall_exp_mul_le fun ε hε ↦ ?_
      refine eval_le_of_mapClusterPt
        (setOf_mem_latticePattern_mem_localEvents (hGmeas n) i) hm ?_
      filter_upwards [hsemi (G n)ᶜ ε hε] with j hj
      exact le_trans ((hmsΓ j).2.2.2.1 n i) hj
    · -- the bound by `t(K_ℓ^C, Ψ^α)`
      intro ℓ i
      refine le_of_forall_exp_mul_le fun ε hε ↦ ?_
      refine eval_le_of_mapClusterPt
        (setOf_notMem_latticePattern_mem_localEvents
          (measurableSet_cubePi ((hKconf α).measurableSet ℓ)) i) hm ?_
      filter_upwards [hsemi (cubePi 2 E (K ℓ)) ε hε] with j hj
      exact le_trans ((hmsΓ j).2.2.2.2.1 ℓ i) hj
    · -- the common symmetries
      intro τ hτ
      exact measurePreserving_of_mapClusterPt (τ.onLattice E).measurable_toFun
        (fun A hA ↦ (τ.onLattice E).preimage_mem_localEvents hA) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.2.2.2.2 τ hτ)
  · -- (ii): Theorem (18.17) from the chessboard estimate
    exact le_measure_mem_latticeOceanPart_of_forall_le_pow (ν := ν) hGU hGUsym
      (isQuasiGibbsianWith_of_isGibbsMeasure_cubeGibbsSpec (hψmeas α) (hψM α) hμ.1)
      hμ.2.1 hμ.2.2.1
  · -- (iii): condition (III)
    have h1 : (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        ≤ patternWeight (ψ α) ν (G n)ᶜ := hμ.2.2.2.1 n 0
    have h2 : (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}ᶜ ≤ t := by
      have h := hμ.2.2.1 {(0 : Fin 2 → ℤ)}
      rw [Finset.card_singleton, pow_one] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext ω
      simp
    have h3 : 1 - t ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω} := by
      rw [tsub_le_iff_right]
      calc (1 : ℝ≥0∞)
          = (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}
            + (μ : Measure ((Fin 2 → ℤ) → E))
              {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}ᶜ := by
            rw [measure_add_measure_compl
              (measurableSet_setOf_mem_latticePattern hGU 0), measure_univ]
        _ ≤ _ := by gcongr
    calc ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        ≤ ((N : ℝ≥0∞) + 1) * patternWeight (ψ α) ν (G n)ᶜ := by gcongr
      _ < 1 - t := hIII α hα n hαn
      _ ≤ _ := h3

/-- **Georgii, Propositions (19.13) and (19.14) together.**  Under Georgii's conditions (I),
(II) and (III) on a family `(Ψ^α)_{α ∈ 𝒫_N}` of `C`-potentials over a standard Borel state
space, together with his `4 N z(t) < 1`, there is a parameter `α*` for which `Ψ^{α*}` has
`N + 1` mutually singular shift-invariant Gibbs measures `μ_0, …, μ_N`, the `n`-th living on the
event that the pattern `G_n` percolates and giving the origin's membership of that ocean
probability at least `1 - 4(N+1) z(t)`; and `μ_n` is invariant under every common symmetry of
the family that fixes `G_n`. -/
theorem exists_gibbsMeasure_family_of_patternWeight_le
    {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n))
    (hψmeas : ∀ α, Measurable (ψ α)) (hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψ α ζ)
    (hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψ α (cubeRefl E k ζ) = ψ α ζ)
    (hKconf : ∀ α, IsCubeConfining (ψ α) ν K)
    (hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψ α' ζ - ψ α ζ| ≤ ε)
    (hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), patternWeight (ψ α) ν (⋃ m, G m) ≤ t)
    (hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * patternWeight (ψ α) ν (G n)ᶜ < 1 - t)
    (hz : ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) < 1) :
    ∃ α ∈ stdSimplex ℝ (Fin (N + 1)), ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α)) (ρ n)) ∧
      (∀ (n : Fin (N + 1)) (a : Fin 2 → ℤ),
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - ((N : ℝ≥0∞) + 1) * (4 * crossingBound t)
        ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        τ.onCube.toFun '' G n = G n →
        MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) := by
  obtain ⟨Γ, hΓne, hΓgibbs, hΓshift, hcc, hii, hiii, hτ⟩ :=
    exists_correspondence_of_patternWeight_le hGmeas hGsym hψmeas hψM hψrefl hKconf hI hII hIII
  have hK0 : ((N : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hKtop : ((N : ℝ≥0∞) + 1) ≠ ∞ := by simp
  have hc : 4 * crossingBound t < ((N : ℝ≥0∞) + 1)⁻¹ := by
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : ((N : ℝ≥0∞) + 1) * ((N : ℝ≥0∞) + 1)⁻¹
        ≤ ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) := mul_le_mul' le_rfl hcon
    rw [ENNReal.mul_inv_cancel hK0 hKtop] at h2
    exact absurd hz (not_lt.2 h2)
  obtain ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_gibbsMeasure_family_of_isCountablyCompact (γ := fun α ↦
      cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α)) hpart hGmeas hGsym hΓne hΓgibbs hΓshift hcc
      hc hii hiii
  exact ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7,
    fun n τ hτsym hGτ ↦ h8 n τ (fun β hβ μ hμ ↦ hτ τ hτsym β hβ μ hμ) hGτ⟩

end Prop1914

/-! ### Georgii Remark (18.9)(1) up to null sets -/

section PatternWeightAe

variable {d : ℕ} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Remark (18.9)(1), up to `λ^C`-null sets.**  The weight `t(·, Φ)` sees the pattern
set only through its `λ^C`-equivalence class — it is built from `λ^C`-restricted to the
complement — so a pattern contained in another one *almost everywhere* has the larger weight.

Its home is next to `patternWeight_anti` in
`GibbsMeasure/Specification/LocalGroundStates.lean`, of which it is the generalisation from
inclusion to almost inclusion; that is what Georgii's Step 3 of (19.15) needs, where
`λ^C(G_δ(Φ^h) ∩ G_n) = 0` rather than `G_δ(Φ^h) ⊆ E^C ∖ G_n`. -/
theorem patternWeight_le_of_measure_diff_eq_zero {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    {W W' : Set ((Fin d → Fin 2) → E)} (h : cubeMeasure d ν (W' \ W) = 0) :
    patternWeight φ ν W ≤ patternWeight φ ν W' := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  have hae : (Wᶜ : Set ((Fin d → Fin 2) → E)) ≤ᵐ[cubeMeasure d ν] (W'ᶜ : Set _) := by
    refine ae_le_set.2 (measure_mono_null (fun ζ hζ ↦ ?_) h)
    exact ⟨not_not.1 hζ.2, hζ.1⟩
  have hmono : cubeMeasure d ν Wᶜ ≤ cubeMeasure d ν W'ᶜ := measure_mono_ae hae
  by_cases h0 : cubeMeasure d ν Wᶜ = 0
  · rw [patternWeight, h0, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  refine mul_le_mul' (mul_le_mul' ?_ ?_) le_rfl
  · have hne : NeZero ((cubeMeasure d ν).restrict Wᶜ) := by
      refine ⟨fun hc ↦ h0 ?_⟩
      rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
    have hle : energyOutside φ ν W' ≤ energyOutside φ ν W :=
      essInf_antitone_measure
        (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_ae hae))
        (isBoundedUnder_ge_ae (Filter.Eventually.of_forall hM))
        (isCoboundedUnder_ge_ae φ)
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  · exact ENNReal.rpow_le_rpow hmono hp.le

end PatternWeightAe

/-! ### Georgii (19.15): the parametrisation of the perturbations by the simplex -/

section SimplexDisadvantage

variable {N : ℕ}

variable (δ) in
/-- **Georgii's `2δ(1 - (max_{1 ≤ k ≤ N} α(k))^{-1} α(n))_{1 ≤ n ≤ N}`** of (19.15): the vector of
energetic disadvantages to be imposed on the members `G_0, …, G_N` of the partition at the
parameter `α` of the simplex.  It lies in `∂ℝ_+^N ∩ [0, 2δ]^N` — it vanishes at a coordinate
where `α` is largest (`simplexDisadvantage_mem_nonnegBoundary`) — and it equals `2δ` exactly at
the coordinates where `α` vanishes (`simplexDisadvantage_eq_of_eq_zero`), which is what makes
Georgii's condition (19.13)(iii) available at the faces of the simplex. -/
def simplexDisadvantage (δ : ℝ) (α : Fin (N + 1) → ℝ) : Fin (N + 1) → ℝ :=
  fun n ↦ 2 * δ * (1 - (Finset.univ.sup' Finset.univ_nonempty α)⁻¹ * α n)

variable {δ : ℝ} {α : Fin (N + 1) → ℝ}

lemma le_sup'_apply (n : Fin (N + 1)) : α n ≤ Finset.univ.sup' Finset.univ_nonempty α :=
  Finset.le_sup' α (Finset.mem_univ n)

/-- On the simplex the largest coordinate is positive. -/
lemma sup'_pos_of_mem_stdSimplex (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) :
    0 < Finset.univ.sup' Finset.univ_nonempty α := by
  by_contra hcon
  rw [not_lt] at hcon
  have h : ∑ n, α n ≤ 0 := by
    calc ∑ n, α n ≤ ∑ _n : Fin (N + 1), (0 : ℝ) :=
          Finset.sum_le_sum fun n _ ↦ le_trans (le_sup'_apply n) hcon
      _ = 0 := by simp
  rw [hα.2] at h
  exact absurd h (by norm_num)

lemma simplexDisadvantage_nonneg (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (hδ : 0 ≤ δ)
    (n : Fin (N + 1)) : 0 ≤ simplexDisadvantage δ α n := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  have h1 : (Finset.univ.sup' Finset.univ_nonempty α)⁻¹ * α n ≤ 1 := by
    rw [inv_mul_le_iff₀ hs, mul_one]
    exact le_sup'_apply n
  have : (0 : ℝ) ≤ 1 - (Finset.univ.sup' Finset.univ_nonempty α)⁻¹ * α n := by linarith
  simp only [simplexDisadvantage]
  positivity

lemma simplexDisadvantage_le (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (hδ : 0 ≤ δ)
    (n : Fin (N + 1)) : simplexDisadvantage δ α n ≤ 2 * δ := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  have h0 : 0 ≤ (Finset.univ.sup' Finset.univ_nonempty α)⁻¹ * α n :=
    mul_nonneg (inv_nonneg.2 hs.le) (hα.1 n)
  simp only [simplexDisadvantage]
  nlinarith

/-- **Georgii's map takes values in `∂ℝ_+^N`**: it vanishes at a coordinate where `α` is
largest. -/
lemma simplexDisadvantage_mem_nonnegBoundary (hα : α ∈ stdSimplex ℝ (Fin (N + 1)))
    (hδ : 0 ≤ δ) : simplexDisadvantage δ α ∈ nonnegBoundary (Fin (N + 1)) := by
  refine ⟨simplexDisadvantage_nonneg hα hδ, ?_⟩
  obtain ⟨n, -, hn⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty) α
  refine ⟨n, ?_⟩
  have hs := sup'_pos_of_mem_stdSimplex hα
  simp only [simplexDisadvantage, ← hn, inv_mul_cancel₀ hs.ne', sub_self, mul_zero]

/-- **Georgii's `g_n(h(α)) = 2δ` when `α(n) = 0`**, the boundary condition of (19.15). -/
lemma simplexDisadvantage_eq_of_eq_zero {n : Fin (N + 1)} (hn : α n = 0) :
    simplexDisadvantage δ α n = 2 * δ := by
  simp [simplexDisadvantage, hn]

/-- **Georgii's `α ↦ 2δ(1 - (max_k α(k))^{-1} α(n))_n` is continuous on the simplex.** -/
lemma continuousAt_simplexDisadvantage (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) :
    ContinuousAt (simplexDisadvantage δ) α := by
  have hs : Continuous fun β : Fin (N + 1) → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty β :=
    Continuous.finset_sup'_apply _ fun i _ ↦ continuous_apply i
  have hinv : ContinuousAt (fun β : Fin (N + 1) → ℝ ↦
      (Finset.univ.sup' Finset.univ_nonempty β)⁻¹) α :=
    (hs.continuousAt).inv₀ (sup'_pos_of_mem_stdSimplex hα).ne'
  refine continuousAt_pi.2 fun n ↦ ?_
  exact continuousAt_const.mul
    (continuousAt_const.sub (hinv.mul (continuous_apply n).continuousAt))

end SimplexDisadvantage

/-! ### Georgii (19.15), Step 2: the low-temperature limit of the perturbed weights -/

section LowTemperature

variable {N : ℕ} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {Ψ : Fin N → ((Fin 2 → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {U : Set (Fin N → ℝ)} {b : Fin N → ℝ} {M₀ δ : ℝ}

/-- **Georgii, Step 2 of (19.15).**  `t_β = sup_{h ∈ U} t(G_δ(Φ^h), βΦ^h) → 0` as `β → ∞`,
uniformly over the neighbourhood `U` on which the perturbations resolve the partition.

By (18.8) (`patternWeight_smul_le`), `t(G_δ(Φ^h), βΦ^h) ≤ e^{-βδ/2}/λ̃^C(G_{δ/2}(Φ^h))`, and
condition (19.4)(ii) bounds the denominator away from `0` uniformly in `h ∈ U`. -/
theorem eventually_forall_patternWeight_perturb_le (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hΨmeas : ∀ j, Measurable (Ψ j)) (hb : ∀ j ζ, |Ψ j ζ| ≤ b j)
    (hres : ResolvesOn φ ν Ψ G U) (hδ : 0 < δ) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ β : ℝ in atTop, ∀ h ∈ U,
      patternWeight (fun ζ ↦ β * perturb φ Ψ h ζ) ν (localGroundStates (perturb φ Ψ h) ν δ)
        ≤ ε := by
  obtain ⟨c, hc0, hc⟩ := hres.exists_measure_localGroundStates_pos (δ / 2) (by positivity)
  have hlim : Tendsto (fun β : ℝ ↦ ENNReal.ofReal (Real.exp (-(β * δ / 2))) / c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ ↦ β * δ / 2) atTop atTop := by
      have h := Filter.Tendsto.atTop_mul_const (show (0 : ℝ) < δ / 2 by linarith)
        (Filter.tendsto_id (α := ℝ))
      simpa [mul_div_assoc] using h
    have h2 : Tendsto (fun β : ℝ ↦ ENNReal.ofReal (Real.exp (-(β * δ / 2)))) atTop (𝓝 0) := by
      have h3 : Tendsto (fun β : ℝ ↦ Real.exp (-(β * δ / 2))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp h1)
      have h4 := (ENNReal.continuous_ofReal.tendsto 0).comp h3
      rw [ENNReal.ofReal_zero] at h4
      exact h4
    simp only [div_eq_mul_inv]
    have h5 := ENNReal.Tendsto.mul_const h2 (Or.inr (ENNReal.inv_ne_top.2 hc0.ne'))
    rwa [zero_mul] at h5
  intro ε hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), ENNReal.tendsto_nhds_zero.1 hlim ε hε]
    with β hβ hβε h hU
  refine le_trans ?_ hβε
  refine le_trans (patternWeight_smul_le (measurable_perturb hφ hΨmeas h)
    (perturb_lower_bound hM₀ hb) hδ hβ) ?_
  exact ENNReal.div_le_div_left (hc h hU) _

end LowTemperature

/-! ### Two small facts used by Georgii's Step 3 of (19.15) -/

section Step3Inputs

open Peierls

/-- **`t ≤ z(t)` below the trivial range.**  The `ℓ = 1` term of Georgii's series (18.13) is `t`
itself, so `z(t) ≥ 1 ⊓ t`; below `1` the infimum is the series.  This is Georgii's
`(N + 1) t_β < 4 N z(t_β) < 1` in Step 3 of (19.15).

Its home is next to `crossingBound_le_four_mul` in `GibbsMeasure/Model/StarCrossing.lean`. -/
theorem le_crossingBound {t : ℝ≥0∞} (ht : crossingBound t < 1) : t ≤ crossingBound t := by
  have hterm : t ≤ ∑' ℓ : ℕ, ((ℓ * 5 ^ (ℓ - 1) : ℕ) : ℝ≥0∞) * t ^ ℓ := by
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 1)
    norm_num
  have hS : ∑' ℓ : ℕ, ((ℓ * 5 ^ (ℓ - 1) : ℕ) : ℝ≥0∞) * t ^ ℓ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd ht (not_lt.2 (le_inf le_rfl hcon))
  rw [crossingBound, inf_eq_right.2 hS.le]
  exact hterm

variable {d : ℕ} {φ χ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}

/-- **Condition (iv) of Georgii (17.18) survives a bounded perturbation of the cube
interaction.**  Its home is next to `IsCubeConfining.const_mul` in
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem IsCubeConfining.add_of_abs_le {K : ℕ → Set E} (hK : IsCubeConfining φ ν K) {B : ℝ}
    (hχ : ∀ ζ, |χ ζ| ≤ B) : IsCubeConfining (fun ζ ↦ φ ζ + χ ζ) ν K where
  measurableSet := hK.measurableSet
  measure_pos := hK.measure_pos
  bddOn ℓ := by
    obtain ⟨c, hc⟩ := hK.bddOn ℓ
    refine ⟨c + B, fun ζ hζ ↦ ?_⟩
    calc |φ ζ + χ ζ| ≤ |φ ζ| + |χ ζ| := abs_add_le _ _
      _ ≤ c + B := add_le_add (hc ζ hζ) (hχ ζ)
  tendsto_atTop c := by
    obtain ⟨ℓ₀, hℓ₀⟩ := hK.tendsto_atTop (c + B)
    refine ⟨ℓ₀, fun ℓ hℓ ζ hζ ↦ ?_⟩
    have h1 := hℓ₀ ℓ hℓ ζ hζ
    have h2 := abs_le.1 (hχ ζ)
    linarith

end Step3Inputs

/-! ### Georgii (19.15), Step 1: the perturbation parameter as a function of the simplex -/

section Parametrisation

variable {N : ℕ} {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {Ψ : Fin N → ((Fin 2 → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {U : Set (Fin N → ℝ)}

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Step 1 of (19.15)**, the choice of `δ`: the image `g(U)` of a resolving
neighbourhood contains the whole box `∂ℝ_+^N ∩ [0, 2δ]^N` for every sufficiently small
`δ > 0`. -/
theorem exists_delta_box_subset_image (hres : ResolvesOn φ ν Ψ G U) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r₀ ∧
      {z : Fin (N + 1) → ℝ | z ∈ nonnegBoundary (Fin (N + 1)) ∧ ∀ n, z n ≤ 2 * δ}
        ⊆ perturbGap φ ν Ψ G '' U := by
  obtain ⟨u, hu, h0, husub⟩ := mem_nhdsWithin.1 hres.image_mem_nhdsWithin
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hu 0 h0
  refine ⟨min (r / 3) (r₀ / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  rintro z ⟨hz1, hz2⟩
  refine husub ⟨hball ?_, hz1⟩
  have hdist : dist z 0 ≤ 2 * min (r / 3) (r₀ / 2) := by
    refine (dist_pi_le_iff (by positivity)).2 fun n ↦ ?_
    rw [Pi.zero_apply, Real.dist_eq, sub_zero, abs_of_nonneg (hz1.1 n)]
    exact hz2 n
  refine Metric.mem_ball.2 (lt_of_le_of_lt hdist ?_)
  calc 2 * min (r / 3) (r₀ / 2) ≤ 2 * (r / 3) := by
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
    _ < r := by linarith

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Step 1 of (19.15)**, the map `α ↦ h(α)`: on the simplex the equation
`g(h(α)) = 2δ(1 - (max_k α(k))^{-1} α(n))_n` has a solution `h(α) ∈ U`, and `α ↦ h(α)` is
continuous along the simplex.  The solution is `g^{-1}` — the continuous left inverse supplied
by Definition (19.4)(i) — applied to `simplexDisadvantage δ α`, which lies in the box
`∂ℝ_+^N ∩ [0, 2δ]^N` and hence in `g(U)`. -/
theorem exists_perturbation_map (hres : ResolvesOn φ ν Ψ G U) {δ : ℝ} (hδ : 0 < δ)
    (hbox : {z : Fin (N + 1) → ℝ | z ∈ nonnegBoundary (Fin (N + 1)) ∧ ∀ n, z n ≤ 2 * δ}
      ⊆ perturbGap φ ν Ψ G '' U) :
    ∃ hmap : (Fin (N + 1) → ℝ) → (Fin N → ℝ),
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), hmap α ∈ U) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
        perturbGap φ ν Ψ G (hmap α) = simplexDisadvantage δ α) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
        ContinuousWithinAt hmap (stdSimplex ℝ (Fin (N + 1))) α) := by
  classical
  obtain ⟨γ, hγcont, hγinv⟩ := hres.exists_continuousOn_leftInverse
  have hmem : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      simplexDisadvantage δ α ∈ perturbGap φ ν Ψ G '' U := fun α hα ↦
    hbox ⟨simplexDisadvantage_mem_nonnegBoundary hα hδ.le,
      fun n ↦ simplexDisadvantage_le hα hδ.le n⟩
  refine ⟨fun α ↦ γ (simplexDisadvantage δ α), fun α hα ↦ ?_, fun α hα ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨h₀, hh₀U, hh₀⟩ := hmem α hα
    have hγ : γ (simplexDisadvantage δ α) = h₀ := by rw [← hh₀, hγinv h₀ hh₀U]
    have : γ (simplexDisadvantage δ α) ∈ U := by rw [hγ]; exact hh₀U
    exact this
  · obtain ⟨h₀, hh₀U, hh₀⟩ := hmem α hα
    have hγ : γ (simplexDisadvantage δ α) = h₀ := by rw [← hh₀, hγinv h₀ hh₀U]
    have : perturbGap φ ν Ψ G (γ (simplexDisadvantage δ α)) = simplexDisadvantage δ α := by
      rw [hγ]; exact hh₀
    exact this
  · refine ContinuousWithinAt.comp (t := perturbGap φ ν Ψ G '' U)
      (hγcont _ (hmem α hα))
      (continuousAt_simplexDisadvantage hα).continuousWithinAt (fun α' hα' ↦ hmem α' hα')

end Parametrisation

/-! ### Georgii, Theorem (19.6) -/

section Theorem196

open Peierls

variable [StandardBorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {φ : ((Fin 2 → Fin 2) → E) → ℝ} {Ψ : Fin N → ((Fin 2 → Fin 2) → E) → ℝ}
  {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)} {K : ℕ → Set E} {b : Fin N → ℝ} {M₀ : ℝ}
  {U U₀ : Set (Fin N → ℝ)}

/-- **Georgii, Theorem (19.6)**, in the quantitative form his proof (19.15) gives.  Let `Φ` be a
`C`-potential over a standard Borel state space with a stable partition `{G_0, …, G_N}` of its
local ground states into measurable `r`-symmetric sets satisfying (19.1), and let bounded
`C`-potentials `Φ^1, …, Φ^N` resolve the partition on a neighbourhood `U` of the origin.  Fix a
weight `t > 0` with `4 (N+1) z(t) < 1` — which by `le_crossingBound` gives Georgii's
`(N+1) t < 4 N z(t) < 1` — and an arbitrary neighbourhood `U₀` of the origin.  Then for all
sufficiently large `β` there is a parameter `h(β) ∈ U₀` such that
`βΦ^{h(β)}` has `N + 1` pairwise mutually singular shift-invariant Gibbs measures `μ_0, …, μ_N`
with

* `μ_n(ξ⁰_P(G_n, ·) ≠ ∅) = 1` and `μ_n(0 ∈ ξ⁰_P(G_n, ·)) ≥ 1 - 4(N+1) z(t)`;
* `τ(μ_n) = μ_n` for every `τ ∈ I_{C,λ}(Φ, Φ^1, …, Φ^N)` with `τ G_n = G_n`.

Since `t` may be taken arbitrarily small and `h(β)` lies in an arbitrarily small neighbourhood of
the origin, this is Georgii's `h(β) → 0` and `μ_n(0 ∈ ξ⁰_P(G_n, ·)) → 1`.

Georgii's proof (19.15): the box `∂ℝ_+^N ∩ [0, 2δ]^N` lies in `g(U)` for small `δ`
(`exists_delta_box_subset_image`), so the equation `g(h(α)) = 2δ(1 - (max_k α(k))^{-1} α(n))_n`
defines a continuous `h : 𝒫_N → U` (`exists_perturbation_map`); the resulting family
`Ψ^α = βΦ^{h(α)}` satisfies conditions (I), (II) and (III) of Proposition (19.14) — (II) and
(III) because `G_δ(Φ^{h(α)}) ⊆ G_ε(Φ) ⊆ G` and, at a vanishing coordinate, `G_δ(Φ^{h(α)})` misses
`G_n` up to a null set — and Proposition (19.13) then selects the parameter `α*`. -/
theorem eventually_exists_gibbsMeasure_family_of_resolvesOn
    (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hφrefl : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hΨmeas : ∀ j, Measurable (Ψ j)) (hb : ∀ j ζ, |Ψ j ζ| ≤ b j) (hb0 : ∀ j, 0 ≤ b j)
    (hΨrefl : ∀ (j : Fin N) (k : Fin 2) ζ, Ψ j (cubeRefl E k ζ) = Ψ j ζ)
    (hKconf : IsCubeConfining φ ν K)
    (hpart : IsPStablePartition φ ν Set.univ G) (hGmeas : ∀ n, MeasurableSet (G n))
    (hGsym : ∀ n, IsRSymmetric E (G n)) (h191 : ∀ n, AttainsGroundEnergy φ ν (G n))
    (hres : ResolvesOn φ ν Ψ G U) (hU₀ : U₀ ∈ 𝓝 (0 : Fin N → ℝ))
    {t : ℝ≥0∞} (ht0 : 0 < t)
    (htz : ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) < 1) :
    ∀ᶠ β : ℝ in atTop, ∃ h ∈ U₀,
      ∀ (hmeas : Measurable fun ζ ↦ β * perturb φ Ψ h ζ)
        (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * perturb φ Ψ h ζ),
      ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
        (∀ n, IsProbabilityMeasure (ρ n)) ∧
        (∀ n, Specification.IsGibbsMeasure
          (cubeGibbsSpec E (fun ζ ↦ β * perturb φ Ψ h ζ) ν hmeas hM) (ρ n)) ∧
        (∀ (n : Fin (N + 1)) (a : Fin 2 → ℤ),
          MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
        (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
        (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - ((N : ℝ≥0∞) + 1) * (4 * crossingBound t)
          ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
        (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
          (∀ c, MeasurePreserving (τ.spin c) ν ν) →
          (∀ ζ, φ (τ.onCube.toFun ζ) = φ ζ) →
          (∀ (j : Fin N) ζ, Ψ j (τ.onCube.toFun ζ) = Ψ j ζ) →
          τ.onCube.toFun '' G n = G n →
          MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) := by
  classical
  -- Georgii's `(N + 1) t < 4 N z(t) < 1`, whence his `t(E^C ∖ G_n, Ψ^α) ≤ t < (1 - t)/N`
  have hK1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) + 1 := le_add_self
  have hz1 : crossingBound t < 1 := by
    refine lt_of_le_of_lt (le_trans ?_ (le_mul_of_one_le_left (zero_le) hK1)) htz
    exact le_mul_of_one_le_left (zero_le) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have htle : t ≤ crossingBound t := le_crossingBound hz1
  have htN : ((N : ℝ≥0∞) + 1) * t < 1 - t := by
    rw [lt_tsub_iff_right]
    refine lt_of_le_of_lt (le_trans ?_ (le_of_eq rfl)) htz
    calc ((N : ℝ≥0∞) + 1) * t + t = ((N : ℝ≥0∞) + 2) * t := by ring
      _ ≤ ((N : ℝ≥0∞) + 2) * crossingBound t := by gcongr
      _ ≤ ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) := by
          rw [← mul_assoc]
          gcongr
          calc (N : ℝ≥0∞) + 2 ≤ (N : ℝ≥0∞) + 2 + (3 * (N : ℝ≥0∞) + 2) := le_self_add
            _ = ((N : ℝ≥0∞) + 1) * 4 := by ring
  obtain ⟨ε, hε, hεsub⟩ := hpart.exists_localGroundStates_subset
  -- Georgii's shrunken neighbourhood of the origin in `ℝ^{N-1}`
  set W : Set (Fin N → ℝ) := U₀ ∩ {h | ∑ k, |h k| * b k < ε / 4} with hWdef
  have hWnhds : W ∈ 𝓝 (0 : Fin N → ℝ) := by
    refine Filter.inter_mem hU₀ (IsOpen.mem_nhds ?_ (by simp; linarith))
    exact isOpen_lt (by fun_prop) continuous_const
  -- the continuous inverse of `g`
  obtain ⟨γ, hγcont, hγinv⟩ := hres.exists_continuousOn_leftInverse
  have hg0 : perturbGap φ ν Ψ G 0 = 0 := perturbGap_zero hφ hM₀ h191
  have h0mem : (0 : Fin (N + 1) → ℝ) ∈ perturbGap φ ν Ψ G '' U :=
    ⟨0, hres.zero_mem, hg0⟩
  have hγ0 : γ 0 = 0 := by
    have := hγinv 0 hres.zero_mem
    rwa [hg0] at this
  obtain ⟨rγ, hrγ, hrγW⟩ : ∃ r > 0, ∀ z ∈ perturbGap φ ν Ψ G '' U, dist z 0 < r → γ z ∈ W := by
    have hcw : ContinuousWithinAt γ (perturbGap φ ν Ψ G '' U) 0 := hγcont 0 h0mem
    have hev : ∀ᶠ z in 𝓝[perturbGap φ ν Ψ G '' U] (0 : Fin (N + 1) → ℝ), γ z ∈ W := by
      have := hcw.tendsto
      rw [hγ0] at this
      exact this hWnhds
    obtain ⟨u, hu, h0u, husub⟩ := mem_nhdsWithin.1 hev
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hu 0 h0u
    exact ⟨r, hr, fun z hz hdz ↦ husub ⟨hball (Metric.mem_ball.2 hdz), hz⟩⟩
  -- Georgii's `δ`
  obtain ⟨δ, hδ0, hδlt, hbox⟩ :=
    exists_delta_box_subset_image hres (r₀ := min (ε / 2) (rγ / 2)) (by positivity)
  have hδε : δ < ε / 2 := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδrγ : 2 * δ < rγ := by
    have := lt_of_lt_of_le hδlt (min_le_right _ _)
    linarith
  -- Georgii's map `α ↦ h(α)`
  obtain ⟨hmap, hmapU, hmapg, hmapcont⟩ := exists_perturbation_map hres hδ0 hbox
  have hmapγ : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), hmap α = γ (simplexDisadvantage δ α) := by
    intro α hα
    rw [← hmapg α hα, hγinv _ (hmapU α hα)]
  have hmapW : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), hmap α ∈ W := by
    intro α hα
    rw [hmapγ α hα]
    refine hrγW _ (hbox ⟨simplexDisadvantage_mem_nonnegBoundary hα hδ0.le,
      fun n ↦ simplexDisadvantage_le hα hδ0.le n⟩) ?_
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).2 fun n ↦ ?_) hδrγ
    rw [Pi.zero_apply, Real.dist_eq, sub_zero,
      abs_of_nonneg (simplexDisadvantage_nonneg hα hδ0.le n)]
    exact simplexDisadvantage_le hα hδ0.le n
  have hmapsmall : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      ∑ k, |hmap α k| * b k < ε / 4 := fun α hα ↦ (hmapW α hα).2
  have hGUpos : cubeMeasure 2 ν (⋃ m, G m) ≠ 0 := by
    refine fun h0 ↦ (h191 0).measure_pos.ne' ?_
    exact measure_mono_null (Set.subset_iUnion G 0) h0
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_forall_patternWeight_perturb_le hφ hM₀ hΨmeas hb hres hδ0 t ht0]
    with β hβ hβt
  set ψfam : (Fin (N + 1) → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ :=
    fun α ζ ↦ β * perturb φ Ψ (hmap α) ζ with hψfamdef
  have hψmeas : ∀ α, Measurable (ψfam α) :=
    fun α ↦ (measurable_perturb hφ hΨmeas _).const_mul β
  have hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψfam α ζ := fun α ↦
    ⟨β * (M₀ - ∑ k, |hmap α k| * b k), fun ζ ↦
      mul_le_mul_of_nonneg_left (perturb_lower_bound hM₀ hb ζ) hβ.le⟩
  have hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψfam α (cubeRefl E k ζ) = ψfam α ζ := by
    intro α k ζ
    simp only [hψfamdef, perturb_apply, hφrefl k ζ]
    congr 2
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hΨrefl j k ζ]
  have hχ : ∀ (α : Fin (N + 1) → ℝ) ζ,
      |∑ k, hmap α k * Ψ k ζ| ≤ ∑ k, |hmap α k| * b k := by
    intro α ζ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb k ζ) (abs_nonneg _)
  have hKconf' : ∀ α, IsCubeConfining (ψfam α) ν K :=
    fun α ↦ (hKconf.add_of_abs_le (hχ α)).const_mul hβ
  -- Georgii's condition (I)
  have hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ e : ℝ, 0 < e →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψfam α' ζ - ψfam α ζ| ≤ e := by
    intro α hα e he
    set B : ℝ := ∑ k, b k with hBdef
    have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ ↦ hb0 k
    have hden : (0 : ℝ) < β * B + 1 := by positivity
    set η : ℝ := e / (β * B + 1) with hηdef
    have hη0 : 0 < η := by positivity
    filter_upwards [(hmapcont α hα).eventually (Metric.ball_mem_nhds (hmap α) hη0)]
      with α' hα' ζ
    have hd : dist (hmap α') (hmap α) < η := Metric.mem_ball.1 hα'
    have h1 : |perturb φ Ψ (hmap α') ζ - perturb φ Ψ (hmap α) ζ|
        ≤ ∑ k, |hmap α' k - hmap α k| * b k := abs_perturb_sub_perturb_le hb ζ
    have h2 : ∑ k, |hmap α' k - hmap α k| * b k ≤ η * B := by
      calc ∑ k, |hmap α' k - hmap α k| * b k ≤ ∑ k, η * b k := by
            refine Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right ?_ (hb0 k)
            refine le_of_lt (lt_of_le_of_lt ?_ hd)
            simpa [Real.dist_eq] using dist_le_pi_dist (hmap α') (hmap α) k
        _ = η * B := by rw [← Finset.mul_sum]
    have h3 : β * (η * B) ≤ e := by
      have key : β * (η * B) * (β * B + 1) ≤ e * (β * B + 1) := by
        have heq : β * (η * B) * (β * B + 1) = (β * B) * e := by
          rw [hηdef]; field_simp
        rw [heq]
        nlinarith [he.le, mul_nonneg hβ.le hB0]
      exact le_of_mul_le_mul_right key hden
    have habs : |ψfam α' ζ - ψfam α ζ|
        = β * |perturb φ Ψ (hmap α') ζ - perturb φ Ψ (hmap α) ζ| := by
      simp only [hψfamdef, ← mul_sub, abs_mul, abs_of_pos hβ]
    rw [habs]
    nlinarith [abs_nonneg (perturb φ Ψ (hmap α') ζ - perturb φ Ψ (hmap α) ζ)]
  -- Georgii's condition (II)
  have hincl : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      localGroundStates (perturb φ Ψ (hmap α)) ν δ ⊆ ⋃ m, G m := by
    intro α hα
    refine subset_trans (fun ζ hζ ↦ ?_) hεsub
    have hd : ∀ ζ', |perturb φ Ψ (hmap α) ζ' - φ ζ'| ≤ ε / 4 :=
      fun ζ' ↦ le_of_lt (lt_of_le_of_lt (abs_perturb_sub_le hb ζ') (hmapsmall α hα))
    have h1 : localGroundEnergy (perturb φ Ψ (hmap α)) ν ≤ localGroundEnergy φ ν + ε / 4 :=
      localGroundEnergy_le_add hM₀ hd
    have h2 := (abs_le.1 (hd ζ)).1
    rw [mem_localGroundStates] at hζ ⊢
    linarith
  have hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      patternWeight (ψfam α) ν (⋃ m, G m) ≤ t := fun α hα ↦
    le_trans (patternWeight_anti (hψM α).choose_spec (hincl α hα)) (hβt _ (hmapU α hα))
  -- Georgii's condition (III)
  have hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * patternWeight (ψfam α) ν (G n)ᶜ < 1 - t := by
    intro α hα n hαn
    have hgap : localGroundEnergyOn (perturb φ Ψ (hmap α)) ν (G n)
        - localGroundEnergyOn (perturb φ Ψ (hmap α)) ν (⋃ m, G m) = 2 * δ := by
      have h := congrFun (hmapg α hα) n
      rw [simplexDisadvantage_eq_of_eq_zero hαn] at h
      exact h
    have hM' : ∀ ζ, M₀ - ∑ k, |hmap α k| * b k ≤ perturb φ Ψ (hmap α) ζ :=
      perturb_lower_bound hM₀ hb
    have hlow : localGroundEnergy (perturb φ Ψ (hmap α)) ν + 2 * δ
        ≤ localGroundEnergyOn (perturb φ Ψ (hmap α)) ν (G n) := by
      have h1 : localGroundEnergy (perturb φ Ψ (hmap α)) ν
          ≤ localGroundEnergyOn (perturb φ Ψ (hmap α)) ν (⋃ m, G m) :=
        localGroundEnergy_le_localGroundEnergyOn hM' hGUpos
      linarith
    have hnull : cubeMeasure 2 ν
        (localGroundStates (perturb φ Ψ (hmap α)) ν δ \ (G n)ᶜ) = 0 := by
      have hae := ae_localGroundEnergyOn_le (φ := perturb φ Ψ (hmap α)) (ν := ν) hM' (G n)
      rw [ae_iff, Measure.restrict_apply' (hGmeas n)] at hae
      refine measure_mono_null (fun ζ hζ ↦ ?_) hae
      refine ⟨?_, not_not.1 hζ.2⟩
      have h1 : perturb φ Ψ (hmap α) ζ ≤ localGroundEnergy (perturb φ Ψ (hmap α)) ν + δ :=
        hζ.1
      simp only [Set.mem_ofPred_eq, not_le]
      linarith
    refine lt_of_le_of_lt (mul_le_mul' le_rfl ?_) htN
    exact le_trans (patternWeight_le_of_measure_diff_eq_zero (hψM α).choose_spec hnull)
      (hβt _ (hmapU α hα))
  obtain ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_gibbsMeasure_family_of_patternWeight_le (t := t) hpart hGmeas hGsym hψmeas hψM
      hψrefl hKconf' hI hII hIII htz
  refine ⟨hmap α, (hmapW α hα).1, fun hmeas hM ↦ ⟨ρ, h1, h2, h3, h4, h5, h6, h7, ?_⟩⟩
  intro n τ hspin hφτ hΨτ hGτ
  refine h8 n τ (fun α' _ ↦ ?_) hGτ
  refine CubeTransformation.IsSymmetry.of_apply_onCube (hψrefl α') hspin fun ζ ↦ ?_
  simp only [hψfamdef, perturb_apply, hφτ ζ]
  congr 2
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hΨτ k ζ]


omit [IsProbabilityMeasure ν] in
/-- **The last statement of Georgii's Theorems (18.25), (19.6) and Corollary (19.7)**:
`n` shift-invariant Gibbs measures, the `i`-th living on the percolation event of the `i`-th
member of a stable family of pattern sets, give `|ex 𝒢_Θ(γ)| ≥ n`.  The percolation events are
pairwise disjoint (`IsPStablePartition.disjoint_setOf_latticeOceanPart_nonempty`), so the
measures are separated in the sense of
`le_encard_extremePoints_invariantG_shiftGroup_of_separated`. -/
theorem le_encard_extremePoints_of_latticeOceanPart {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ}
    {γ : Specification (Fin 2 → ℤ) E} {n : ℕ} {W : Fin n → Set ((Fin 2 → Fin 2) → E)}
    {ρ : Fin n → Measure ((Fin 2 → ℤ) → E)} (hpart : IsPStablePartition φ₀ ν Set.univ W)
    (hWmeas : ∀ i, MeasurableSet (W i)) (hprob : ∀ i, IsProbabilityMeasure (ρ i))
    (hgibbs : ∀ i, Specification.IsGibbsMeasure γ (ρ i))
    (hinv : ∀ (i : Fin n) (a : Fin 2 → ℤ), MeasurePreserving (shift E a).toFun (ρ i) (ρ i))
    (hself : ∀ i, ρ i {ω | (latticeOceanPart E (W i) ω).Nonempty} = 1) :
    (n : ℕ∞) ≤ ((invariantG γ (shiftGroup (Fin 2 → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  refine le_encard_extremePoints_invariantG_shiftGroup_of_separated_lattice (ι := Fin 2)
    (A := fun i ↦ {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (W i) ω).Nonempty})
    hprob hgibbs hinv hself fun i j hij ↦ ?_
  have hprobj := hprob j
  have hsub : {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (W i) ω).Nonempty}
      ⊆ {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E (W j) ω).Nonempty}ᶜ :=
    Set.disjoint_left.1 (hpart.disjoint_setOf_latticeOceanPart_nonempty hij)
  refine le_antisymm (le_trans (measure_mono hsub) (le_of_eq ?_)) zero_le
  rw [prob_compl_eq_one_sub (measurableSet_setOf_latticeOceanPart_nonempty (hWmeas j)),
    hself j, tsub_self]

end Theorem196

end MeasureTheory.GibbsMeasure

end

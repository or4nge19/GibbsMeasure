/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Combinatorics.SimpleGraph.Measurable
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.SymmetricChain
public import GibbsMeasure.Model.OceanNetwork
public import GibbsMeasure.Model.UniqueInfiniteCluster
public import GibbsMeasure.Model.StarCrossing
public import GibbsMeasure.Specification.PeriodicGibbsLimits

/-!
# Georgii §18.1 in the plane: percolation of a spin pattern under `𝒢₀(Φ)`

Georgii, *Gibbs Measures and Phase Transitions*, §18.1, from Lemma (18.10) to Corollary (18.18).
For `d = 2` the plane `P` of (18.5) is the whole lattice.

## Main results

* `le_measure_mem_infiniteClusters_latticePattern` — Georgii's displayed inequality between
  (18.14) and (18.15): `μ(0 ∈ ξ_Q(G, ·)) ≥ 1 - z(t(G, Φ))` for every `μ ∈ 𝒢₀(Φ)`, every
  `r`-symmetric `G` and each of the four quadrants `Q` with vertex `0`.
* `le_measure_cross_latticePattern` — the four-quadrant union bound `μ(X) ≥ 1 - 4 z(t(G, Φ))`
  for Georgii's event `X` that the origin is the centre of an infinite cross, the first
  paragraph of his proof of (18.16).
* `latticeOceanPart` — **Georgii (18.7)** in the plane, `ξ⁰_P(G, ·)`, with
  `latticeOceanPart_nonempty_iff` and the shift equivariance `latticeOceanPart_shift`.
* `pairCube`, `patternChain`, `barrierSeg`, `isssd_forall_notMem_latticePattern_eq_pi_patternChain`
  and `isssd_barrier_ne_zero` — a barrier segment in either lattice direction is a chain
  condition on the `|D| + 1` slices of the `2 × (|D| + 1)` strip it reads, and it is not
  `λ^S`-null as soon as `λ^C(E^C ∖ G) > 0`; the symmetry of the slice relation comes from the
  `r`-symmetry of `G` (`MeasureTheory.pi_chainSet_one_eq_zero_of_pi_chainSet_eq_zero`).
* `measure_setOf_frequently_barrier_eq_one` and `ae_forall_frequently_barrier` — **Georgii,
  Step 1 of the proof of (18.16)**: `μ(B_{k,ℓ}) = 1`, and almost surely every segment of either
  axis is a barrier of `V(G, ·)` at infinitely many translates along the shift.
  `ae_barriers_up`, `ae_barriers_down`, `ae_barriers_right`, `ae_barriers_left` are the
  geometric form used by Steps 2 and 3.
* `crossEvent`, `measurableSet_crossEvent` — Georgii's event `X`, and its measurability, which
  Poincaré recurrence needs.
* `ae_mem_crossEvent_imp_mem_latticeOceanPart` and `measure_crossEvent_le` — **Georgii, Lemma
  (18.16)**: a shift-invariant quasi-Gibbsian random field puts the origin into the maximal
  ocean `ξ⁰_P(G, ·)` almost surely on `X`, so `μ(X) ≤ μ(0 ∈ ξ⁰_P(G, ·))`;
  `le_measure_mem_latticeOceanPart_of_forall_quadrant` is the lemma as Georgii states it,
  `μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4z` from the four quadrant bounds `μ(0 ∈ ξ_Q(G, ·)) ≥ 1 - z`.
  Steps 2 and 3 are the planar combinatorics of `GibbsMeasure/Model/OceanNetwork.lean`
  (`Peierls.exists_isOceanIn_of_crossCentres`); the degenerate case `λ^C(G) = 1` of Georgii's
  proof is `ae_mem_latticeOceanPart_of_cubeMeasure_compl_eq_zero`.
* `le_measure_mem_latticeOceanPart` — **Georgii, Theorem (18.17)**, first assertion:
  `μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4 z(t(G, Φ))` for every `μ ∈ 𝒢₀(Φ)`.
* `measurableSet_setOf_latticeOceanPart_nonempty` and
  `tail_measurableSet_setOf_latticeOceanPart_nonempty` — the event `{ξ⁰_P(G, ·) ≠ ∅}` is
  measurable, and it is a **tail** event, the fact Georgii's proof of the second assertion of
  (18.17) invokes without proof.  Measurability is Definition (18.6) read as a countable
  condition (`SimpleGraph.measurableSet_setOf_oceanPart_nonempty`).  Tail measurability is that
  plus `Function.DependsOn`: altering the spins in a finite volume `Λ` alters `V(G, ·)` only at
  the finitely many sites whose elementary cube meets `Λ` (`cubePreSupport`,
  `latticePattern_diff_subset_cubePreSupport`), and whether a subset of the plane contains an
  ocean is unchanged by a finite modification (`Peierls.oceanPart_nonempty_congr_of_finite_diff`,
  whose planar input is `Peierls.eq_of_infinite_supp_of_forall_finite_island`).
* `le_measure_mem_latticeOceanPart_localGroundStates`,
  `tendsto_bound_latticeOceanPart_localGroundStates` and
  `tendsto_iInf_measure_mem_latticeOceanPart_localGroundStates` — **Georgii, Corollary (18.18)**,
  first assertion: the bound `1 - 4 z(t(G_ε(Φ), βΦ))` holds for every `μ ∈ 𝒢₀(βΦ)` and tends to
  `1` as `β → ∞`, so that, over a standard Borel state space with a confining cube interaction
  (which makes `𝒢₀(βΦ) ≠ ∅` by (18.12)), `lim_{β→∞} inf_{μ ∈ 𝒢₀(βΦ)} μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) = 1`
  as displayed.  `le_measure_mem_infiniteClusters_localGroundStates` is the same statement with
  the ocean `ξ⁰_P` replaced by the quadrant clusters `ξ_Q`.

## Georgii's step count

Georgii's proof of (18.16) is in three steps plus the union bound.  Step 1 is
`measure_setOf_frequently_barrier_eq_one`; Step 2 is
`Peierls.reachIn_upper_of_infiniteClusters_of_barrier` and its four orientations; Step 3 —
"clearly this network is an ocean", for which Georgii gives Figure 18.2 — is
`Peierls.finite_reachIn_star_of_circuit` and `Peierls.exists_isOceanIn_of_crossCentres`; the
final "`X ⊆ {ξ⁰_P ≠ ∅}` almost surely" is `ae_mem_crossEvent_imp_mem_latticeOceanPart`.

Two remarks on the statement.  Georgii's hypothesis `z < 1/4` in (18.16) is not used in his
proof and is not assumed here: it only makes the conclusion non-vacuous.  And Georgii's
conclusion is `μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4z` while his proof shows `X ⊆ {ξ⁰_P(G, ·) ≠ ∅}`; the
missing step is that on `X` the origin lies in an infinite cluster of `V(G, ·)`, so that
`ξ⁰_P(G, ·) ≠ ∅` forces `0 ∈ ξ⁰_P(G, ·)`.  That step is
`Peierls.mem_oceanPart_of_isOceanIn` together with `Peierls.IsCrossCentre.mem_infiniteClusters`.

## What is *not* in this file

* The second assertions of **(18.17)** and **(18.18)** — that for `z(t(G, Φ)) < 1/4` (resp. `β`
  large) there is a `μ ∈ 𝒢(Φ)` invariant under the shifts and the reflections `r_1, …, r_d`
  with `μ(ξ⁰_P(G, ·) ≠ ∅) = 1` — are in `GibbsMeasure/Model/LowEnergyOceanPhase.lean`.  They are
  Georgii's conditioning `μ = ν(· | ξ⁰_P(G, ·) ≠ ∅)` of a `ν ∈ 𝒢₀(Φ)` on the tail event above,
  and live in a separate file only because the reflection invariance of `𝒢₀(Φ)` is Remark
  (18.22), in `GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`, which is a §18.2 file.
* **Example (18.19)**, the classical Heisenberg model, is in
  `GibbsMeasure/Model/HeisenbergOceans.lean`: the `C`-potential
  `Φ_C = -∑_{{i,j} ⊆ C, |i-j| = 1} σ_i·σ_j` on the unit sphere with its `r`-symmetry and bound
  `|Φ_C| ≤ 4`, the identification `m_Φ = -4`, the description of the local ground states as the
  constant configurations, and Georgii's inclusion `G_ε(Φ) ⊆ G̃_ε`.  What is still missing there
  is the second half of (18.19): the high-temperature bound `μ(ξ(G̃_ε, ·) ≠ ∅) = 0` for
  `3 r(β, ε) < 1`, a self-avoiding path count over the single-site conditional probabilities
  `γ^{βΦ}_{\{i\}}(σ_i · ω_j ≥ 1 - ε | ω)`, which is independent of everything above.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E}
  [IsProbabilityMeasure ν] {G : Set ((Fin 2 → Fin 2) → E)}

/-- **Georgii, the display following Lemma (18.14).**  For an `r`-symmetric pattern `G`, a
`C`-potential `Φ` with cube interaction `φ`, and `μ ∈ 𝒢₀(Φ)`, the origin lies in an infinite
cluster of `V(G, ·) ∩ Q` with probability at least `1 - z(t(G, Φ))`, for each of the four
quadrants `Q` of the plane with vertex `0`. -/
theorem le_measure_mem_infiniteClusters_latticePattern (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G)
    {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)} (hμ : μ ∈ GZero E φ ν)
    {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    1 - Peierls.crossingBound (patternWeight φ ν G)
      ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Peierls.Site) ∈ (latticeGraph 2).infiniteClusters
          (latticePattern E G ω ∩ Peierls.quadrant s₁ s₂)} :=
  Peierls.le_measure_mem_infiniteClusters hs₁ hs₂ _ (fun ω ↦ latticePattern E G ω)
    fun D ↦ forall_notMem_latticePattern_le_patternWeight (d := 1) hφ hM hφk hG hGsym hμ D

/-- **Georgii, the first paragraph of the proof of (18.16).**  With probability at least
`1 - 4 z(t(G, Φ))` the origin is the point of intersection of an infinite "cross" in
`V(G, ·)`. -/
theorem le_measure_cross_latticePattern (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hG : MeasurableSet G) (hGsym : IsRSymmetric E G)
    {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)} (hμ : μ ∈ GZero E φ ν) :
    1 - 4 * Peierls.crossingBound (patternWeight φ ν G)
      ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
          (0 : Peierls.Site) ∈ (latticeGraph 2).infiniteClusters
            (latticePattern E G ω ∩ Peierls.quadrant s₁ s₂)} :=
  Peierls.le_measure_forall_mem_infiniteClusters _ (fun ω ↦ latticePattern E G ω)
    fun D ↦ forall_notMem_latticePattern_le_patternWeight (d := 1) hφ hM hφk hG hGsym hμ D

/-! ### Georgii Corollary (18.18) in the quadrant form -/

/-- Georgii's `z(t) → 0 as t → 0`, along a net: `z ∘ t → 0` whenever `t → 0`. -/
theorem tendsto_crossingBound_of_tendsto {ι : Type*} {l : Filter ι} {t : ι → ℝ≥0∞}
    (ht : Tendsto t l (𝓝 0)) : Tendsto (fun a ↦ Peierls.crossingBound (t a)) l (𝓝 0) := by
  have h4 : Tendsto (fun a ↦ 4 * t a) l (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) ht (Or.inr (by norm_num))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h4
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  have hpos : (0 : ℝ≥0∞) < (20 : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.2 (by norm_num)
  filter_upwards [ht (Iio_mem_nhds hpos)] with a ha
  exact Peierls.crossingBound_le_four_mul (le_of_lt ha)

/-- **Georgii, Remark (18.9)(4) combined with (18.10) and (18.14).**  The bound
`1 - z(t(G_ε(Φ), βΦ))` for the probability that the origin percolates in a quadrant tends to
`1` as `β → ∞`. -/
theorem tendsto_crossingBound_patternWeight_localGroundStates (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun β : ℝ ↦ Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) :=
  tendsto_crossingBound_of_tendsto (tendsto_patternWeight_smul_atTop hφ hM hε)

/-- **Georgii, Corollary (18.18), quadrant form.**  For every `μ ∈ 𝒢₀(βΦ)` and every quadrant
`Q` of the plane with vertex `0`, the origin lies in an infinite cluster of
`V(G_ε(Φ), ·) ∩ Q` with probability at least `1 - z(t(G_ε(Φ), βΦ))`, and that bound tends to
`1` as `β → ∞`. -/
theorem le_measure_mem_infiniteClusters_localGroundStates (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) (ε : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)}
    (hμ : μ ∈ GZero E (fun ζ ↦ β * φ ζ) ν) {s₁ s₂ : ℤ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    1 - Peierls.crossingBound (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
      ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Peierls.Site) ∈ (latticeGraph 2).infiniteClusters
          (latticePattern E (localGroundStates φ ν ε) ω ∩ Peierls.quadrant s₁ s₂)} :=
  le_measure_mem_infiniteClusters_latticePattern (hφ.const_mul β)
    (M := β * M) (fun ζ ↦ by nlinarith [hM ζ])
    (fun k ζ ↦ by rw [hφk k ζ])
    (measurableSet_localGroundStates hφ ε) (isRSymmetric_localGroundStates hφk ε) hμ hs₁ hs₂

/-! ### Georgii (18.7) in the plane: the maximal ocean of `V(G, ·)` -/

variable (E) in
/-- **Georgii (18.7)** for `d = 2`, where the plane `P` of (18.5) is the whole lattice:
`ξ⁰_P(G, ω)` is the union of the infinite clusters of `V(G, ω)` when that union is an ocean, and
`∅` otherwise. -/
def latticeOceanPart (G : Set ((Fin 2 → Fin 2) → E)) (ω : (Fin 2 → ℤ) → E) : Set Peierls.Site :=
  SimpleGraph.oceanPart (latticeGraph 2) (starLatticeGraph 2) Set.univ (latticePattern E G ω)

/-- **Georgii, the display after (18.7)**: `ξ⁰_P(G, ω) ≠ ∅` exactly when `V(G, ω)` contains an
ocean. -/
theorem latticeOceanPart_nonempty_iff (ω : (Fin 2 → ℤ) → E) :
    (latticeOceanPart E G ω).Nonempty ↔
      ∃ ξ, ξ ⊆ latticePattern E G ω ∧
        SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2) Set.univ ξ :=
  Peierls.oceanPart_nonempty_iff_exists_isOceanIn _

/-- **The event `{ξ⁰_P(G, ·) ≠ ∅}` is shift invariant**, one of the two invariances Georgii uses
at the end of the proof of (18.17). -/
theorem latticeOceanPart_shift (hGsym : IsRSymmetric E G) (a : Fin 2 → ℤ)
    (ω : (Fin 2 → ℤ) → E) :
    latticeOceanPart E G ((shift E a).toFun ω) = (· + a) '' latticeOceanPart E G ω := by
  rw [latticeOceanPart, latticeOceanPart, latticePattern_shift hGsym,
    Peierls.oceanPart_image_add_right]

/-- The event that the origin lies in the maximal ocean is shift invariant along the ocean:
`0 ∈ ξ⁰_P(G, θ_a ω)` iff `-a ∈ ξ⁰_P(G, ω)`. -/
theorem mem_latticeOceanPart_shift (hGsym : IsRSymmetric E G) (a i : Fin 2 → ℤ)
    (ω : (Fin 2 → ℤ) → E) :
    i ∈ latticeOceanPart E G ((shift E a).toFun ω) ↔ i - a ∈ latticeOceanPart E G ω := by
  rw [latticeOceanPart_shift hGsym]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · exact fun h ↦ ⟨i - a, h, sub_add_cancel i a⟩

/-! ### Georgii, Step 1 of the proof of (18.16): the barrier events -/

section Barriers

variable {d : ℕ} {G' : Set ((Fin d → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- Iterating the shift `θ_a` translates by `n • a`. -/
lemma shift_iterate_toFun (a : Fin d → ℤ) (n : ℕ) (ω : (Fin d → ℤ) → E) :
    ((shift E a).toFun)^[n] ω = (shift E (n • a)).toFun ω := by
  induction n generalizing ω with
  | zero => funext i; simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      funext i
      simp only [shift_toFun_apply]
      congr 1
      rw [succ_nsmul]
      abel

omit [IsProbabilityMeasure ν] in
/-- Georgii (18.3) under a shift, in membership form: `i ∈ V(G, θ_b ω) ↔ i - b ∈ V(G, ω)`. -/
lemma mem_latticePattern_shift_iff (hGsym : IsRSymmetric E G') (b i : Fin d → ℤ)
    (ω : (Fin d → ℤ) → E) :
    i ∈ latticePattern E G' ((shift E b).toFun ω) ↔ i - b ∈ latticePattern E G' ω := by
  rw [latticePattern_shift hGsym]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · exact fun h ↦ ⟨i - b, h, sub_add_cancel i b⟩

omit [IsProbabilityMeasure ν] in
/-- The `n`-th shift of Georgii's barrier event `{D ∩ V(G, ·) = ∅}` is the barrier event of the
translated set `D - n • a`. -/
lemma preimage_shift_iterate_forall_notMem_latticePattern (hGsym : IsRSymmetric E G')
    (a : Fin d → ℤ) (n : ℕ) (D : Finset (Fin d → ℤ)) :
    ((shift E a).toFun)^[n] ⁻¹' {ω : (Fin d → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G' ω}
      = {ω | ∀ i ∈ D.image (· - n • a), i ∉ latticePattern E G' ω} := by
  classical
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, shift_iterate_toFun,
    mem_latticePattern_shift_iff hGsym, Finset.mem_image]
  constructor
  · rintro h i ⟨j, hj, rfl⟩
    exact h j hj
  · intro h i hi
    exact h _ ⟨i, hi, rfl⟩

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma mem_cubeSupport_iff {D : Finset (Fin d → ℤ)} {x : Fin d → ℤ} :
    x ∈ cubeSupport D ↔ ∃ i ∈ D, ∃ c, i + intCubeCast c = x := by
  simp [cubeSupport]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
/-- The sites read by the translated barrier event are the translated sites. -/
lemma cubeSupport_image_sub (D : Finset (Fin d → ℤ)) (b : Fin d → ℤ) :
    cubeSupport (D.image (· - b)) = (cubeSupport D).image (· - b) := by
  classical
  ext x
  rw [mem_cubeSupport_iff, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, c, rfl⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    exact ⟨j + intCubeCast c, mem_cubeSupport_iff.2 ⟨j, hj, c, rfl⟩, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨j, hj, c, rfl⟩ := mem_cubeSupport_iff.1 hy
    exact ⟨j - b, Finset.mem_image.2 ⟨j, hj, rfl⟩, c, by abel⟩

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
/-- For a nonzero step `a`, the translates `s - n • a` of a finite set of sites eventually miss
any given finite set of sites. -/
lemma exists_forall_sub_nsmul_notMem {a : Fin d → ℤ} (ha : a ≠ 0)
    (s t : Finset (Fin d → ℤ)) : ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, x - n • a ∉ t := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, a k ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨M, hM⟩ := (s.image fun x ↦ |x k|).exists_le
  obtain ⟨M', hM'⟩ := (t.image fun y ↦ |y k|).exists_le
  refine ⟨(M + M').toNat + 1, fun n hn x hx hmem ↦ ?_⟩
  have h1 : |x k| ≤ M := hM _ (Finset.mem_image_of_mem _ hx)
  have h2 : |(x - n • a) k| ≤ M' := hM' _ (Finset.mem_image_of_mem _ hmem)
  have h3 : (x - n • a) k = x k - (n : ℤ) * a k := by
    simp [Pi.sub_apply, nsmul_eq_mul]
  rw [h3] at h2
  have hb1 := abs_le.1 h1
  have hb2 := abs_le.1 h2
  have hnn : ((M + M').toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hMM : M + M' + 1 ≤ (n : ℤ) := le_trans (by linarith [Int.self_le_toNat (M + M')]) hnn
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2]
  · nlinarith [hb1.1, hb1.2, hb2.1, hb2.2]

/-- **Georgii, Step 1 of the proof of (18.16): the barrier event is a tail event.**  The `n`-th
shift of the local event `{D ∩ V(G, ·) = ∅}` reads only the spins in the translate
`(D - n • a) + C`, and for `a ≠ 0` these translates leave every finite volume; so the set of
configurations for which the event occurs infinitely often along the orbit of `θ_a` is a tail
event. -/
theorem tail_measurableSet_setOf_frequently_shift_forall_notMem_latticePattern
    (hG : MeasurableSet G') (hGsym : IsRSymmetric E G') {a : Fin d → ℤ} (ha : a ≠ 0)
    (D : Finset (Fin d → ℤ)) :
    MeasurableSet[tailSigmaAlgebra (Fin d → ℤ) E]
      {ω | ∃ᶠ n in atTop, ((shift E a).toFun)^[n] ω ∈
        {ω' : (Fin d → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G' ω'}} := by
  classical
  set A : Set ((Fin d → ℤ) → E) := {ω | ∀ i ∈ D, i ∉ latticePattern E G' ω} with hAdef
  set U : ℕ → Set ((Fin d → ℤ) → E) :=
    fun N ↦ ⋃ n ∈ Set.Ici N, ((shift E a).toFun)^[n] ⁻¹' A with hUdef
  have hRU : {ω | ∃ᶠ n in atTop, ((shift E a).toFun)^[n] ω ∈ A} = ⋂ N : ℕ, U N := by
    ext ω
    simp only [Set.mem_ofPred_eq, Filter.frequently_atTop, Set.mem_iInter, hUdef,
      Set.mem_iUnion, Set.mem_Ici, Set.mem_preimage, exists_prop]
  have hUanti : ∀ {N M : ℕ}, N ≤ M → U M ⊆ U N := by
    intro N M hNM ω hω
    obtain ⟨n, hn, hn'⟩ := Set.mem_iUnion₂.1 hω
    exact Set.mem_iUnion₂.2 ⟨n, le_trans hNM hn, hn'⟩
  rw [hRU]
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ ?_
  obtain ⟨N₀, hN₀⟩ := exists_forall_sub_nsmul_notMem ha (cubeSupport D) Λ
  have hUmeas : ∀ n ≥ N₀,
      MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E) ((Λ : Set (Fin d → ℤ))ᶜ)]
        (((shift E a).toFun)^[n] ⁻¹' A) := by
    intro n hn
    rw [preimage_shift_iterate_forall_notMem_latticePattern hGsym]
    refine measurableSet_cylinderEvents_forall_notMem_latticePattern hG _ ?_
    intro i hi c
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have : j + intCubeCast c - n • a ∈ (cubeSupport D).image (· - n • a) :=
      Finset.mem_image.2 ⟨j + intCubeCast c, mem_cubeSupport_iff.2 ⟨j, hj, c, rfl⟩, rfl⟩
    have hne : j + intCubeCast c - n • a ∉ Λ :=
      hN₀ n hn _ (mem_cubeSupport_iff.2 ⟨j, hj, c, rfl⟩)
    simpa [sub_add_eq_add_sub] using hne
  have hiInf : (⋂ N : ℕ, U N) = ⋂ N : ℕ, U (N₀ + N) := by
    refine Set.Subset.antisymm (Set.iInter_mono' fun N ↦ ⟨N₀ + N, subset_rfl⟩) ?_
    refine Set.subset_iInter fun N ↦ ?_
    exact Set.iInter_subset_of_subset N (hUanti (Nat.le_add_left N N₀))
  rw [hiInf]
  refine MeasurableSet.iInter fun N ↦ ?_
  exact MeasurableSet.biUnion (Set.to_countable _) fun n hn ↦
    hUmeas n (le_trans (Nat.le_add_right N₀ N) hn)

end Barriers

/-! ### Georgii, Step 1 of the proof of (18.16): the barrier event is not null -/

section Chain

open Peierls

variable {G' : Set ((Fin 2 → Fin 2) → E)}

private lemma fin_two_cases : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide

private lemma fin_two_eq_or_rev : ∀ l dir : Fin 2, l = dir ∨ l = Fin.rev dir := by decide

private lemma fin_two_rev_ne : ∀ dir : Fin 2, Fin.rev dir ≠ dir := by decide

/-- The corner of the unit square with coordinate `a` in the direction `dir` and coordinate `i`
in the other direction. -/
def cubeCorner (dir : Fin 2) (a i : Fin 2) : Fin 2 → Fin 2 := fun l ↦ if l = dir then a else i

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
@[simp] lemma cubeCorner_self (dir a i : Fin 2) : cubeCorner dir a i dir = a := by
  simp [cubeCorner]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
@[simp] lemma cubeCorner_rev (dir a i : Fin 2) : cubeCorner dir a i (Fin.rev dir) = i := by
  simp [cubeCorner, fin_two_rev_ne dir]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma cubeCorner_eta (dir : Fin 2) (c : Fin 2 → Fin 2) :
    cubeCorner dir (c dir) (c (Fin.rev dir)) = c := by
  funext l
  rcases fin_two_eq_or_rev l dir with rfl | rfl
  · simp
  · simp

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma cubeCorner_injective (dir : Fin 2) :
    Function.Injective fun p : Fin 2 × Fin 2 ↦ cubeCorner dir p.1 p.2 := by
  rintro ⟨a, i⟩ ⟨a', i'⟩ h
  have h1 := congrFun h dir
  have h2 := congrFun h (Fin.rev dir)
  simp only [cubeCorner_self, cubeCorner_rev] at h1 h2
  exact Prod.ext h1 h2

variable (E) in
/-- The cube configuration glued from its two `dir`-slices.  Together with `patternChain` this
presents Georgii's barrier event `{D(k, ℓ) ∩ V(G, ·) = ∅}` as a *chain* condition on the
`|D| + 1` slices of the configuration that the event reads. -/
def pairCube (dir : Fin 2) (p : (Fin 2 → E) × (Fin 2 → E)) : (Fin 2 → Fin 2) → E :=
  fun c ↦ if c dir = 0 then p.1 (c (Fin.rev dir)) else p.2 (c (Fin.rev dir))

omit [IsProbabilityMeasure ν] in
lemma measurable_pairCube (dir : Fin 2) : Measurable (pairCube E dir) := by
  refine Measurable.of_eval fun c ↦ ?_
  by_cases h : c dir = 0
  · have hf : (fun p : (Fin 2 → E) × (Fin 2 → E) ↦ pairCube E dir p c)
        = fun p ↦ p.1 (c (Fin.rev dir)) := by
      funext p; simp [pairCube, h]
    rw [hf]
    exact (measurable_pi_apply _).comp measurable_fst
  · have hf : (fun p : (Fin 2 → E) × (Fin 2 → E) ↦ pairCube E dir p c)
        = fun p ↦ p.2 (c (Fin.rev dir)) := by
      funext p; simp [pairCube, h]
    rw [hf]
    exact (measurable_pi_apply _).comp measurable_snd

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
/-- The two `dir`-slices of a cube configuration glue back to it. -/
lemma pairCube_cols (dir : Fin 2) (ζ : (Fin 2 → Fin 2) → E) :
    pairCube E dir (fun i ↦ ζ (cubeCorner dir 0 i), fun i ↦ ζ (cubeCorner dir 1 i)) = ζ := by
  funext c
  rcases fin_two_cases (c dir) with hc | hc
  · rw [show pairCube E dir (fun i ↦ ζ (cubeCorner dir 0 i), fun i ↦ ζ (cubeCorner dir 1 i)) c
      = ζ (cubeCorner dir 0 (c (Fin.rev dir))) by simp [pairCube, hc], ← hc, cubeCorner_eta]
  · rw [show pairCube E dir (fun i ↦ ζ (cubeCorner dir 0 i), fun i ↦ ζ (cubeCorner dir 1 i)) c
      = ζ (cubeCorner dir 1 (c (Fin.rev dir))) by simp [pairCube, hc], ← hc, cubeCorner_eta]

omit [IsProbabilityMeasure ν] in
/-- Exchanging the two slices of a cube reflects it in the direction `dir`. -/
lemma pairCube_swap (dir : Fin 2) (p : (Fin 2 → E) × (Fin 2 → E)) :
    pairCube E dir (Prod.swap p) = cubeRefl E dir (pairCube E dir p) := by
  funext c
  rw [cubeRefl_apply, cubeSiteRefl_apply]
  have h0 : (Function.update c dir (Fin.rev (c dir))) dir = Fin.rev (c dir) := by simp
  have h1 : (Function.update c dir (Fin.rev (c dir))) (Fin.rev dir) = c (Fin.rev dir) :=
    Function.update_of_ne (fin_two_rev_ne dir) _ _
  have hr0 : Fin.rev (0 : Fin 2) = 1 := by decide
  have hr1 : Fin.rev (1 : Fin 2) = 0 := by decide
  rcases fin_two_cases (c dir) with hc | hc
  · rw [pairCube, pairCube, h0, h1, hc, hr0]
    simp
  · rw [pairCube, pairCube, h0, h1, hc, hr1]
    simp

omit [IsProbabilityMeasure ν] in
/-- **The pattern relation between consecutive slices is symmetric** when the pattern is
`r`-symmetric: this is what makes Georgii's barrier event of positive probability for every
length (see `MeasureTheory.prod_eq_zero_of_pi_chainSet_eq_zero`). -/
lemma swap_preimage_pairCube_preimage_compl (dir : Fin 2) (hGsym : IsRSymmetric E G') :
    Prod.swap ⁻¹' (pairCube E dir ⁻¹' G'ᶜ) = pairCube E dir ⁻¹' G'ᶜ := by
  ext p
  simp only [Set.mem_preimage, pairCube_swap, Set.mem_compl_iff]
  exact not_congr (Set.ext_iff.1 (hGsym dir) (pairCube E dir p))

variable (G') in
/-- Georgii's barrier event as a chain condition on slices: the `m` consecutive elementary
cubes of a `dir`-segment formed by `m + 1` consecutive slices all fail the pattern `G`.  This is
`MeasureTheory.chainSet` of the slice relation `pairCube E dir ⁻¹' Gᶜ`. -/
def patternChain (dir : Fin 2) (m : ℕ) : Set (Fin (m + 1) → (Fin 2 → E)) :=
  chainSet (pairCube E dir ⁻¹' G'ᶜ) m

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma mem_patternChain {dir : Fin 2} {m : ℕ} {y : Fin (m + 1) → (Fin 2 → E)} :
    y ∈ patternChain G' dir m ↔ ∀ j : Fin m, pairCube E dir (y j.castSucc, y j.succ) ∉ G' :=
  Iff.rfl

omit [IsProbabilityMeasure ν] in
lemma measurableSet_patternChain (dir : Fin 2) (hG : MeasurableSet G') (m : ℕ) :
    MeasurableSet (patternChain G' dir m) := by
  have hrw : patternChain G' dir m
      = ⋂ j : Fin m, (fun y : Fin (m + 1) → (Fin 2 → E) ↦
          pairCube E dir (y j.castSucc, y j.succ)) ⁻¹' G'ᶜ := by
    ext y
    simp [mem_patternChain]
  rw [hrw]
  exact MeasurableSet.iInter fun j ↦
    ((measurable_pairCube dir).comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) hG.compl

/-- **The one-link chain is the pattern itself.**  Under the product measure the two slices of
an elementary cube are a `λ^C`-distributed cube configuration. -/
theorem pi_patternChain_one (dir : Fin 2) (hG : MeasurableSet G') :
    (Measure.pi fun _ : Fin (1 + 1) ↦ (Measure.pi fun _ : Fin 2 ↦ ν))
        (patternChain G' dir 1) = cubeMeasure 2 ν G'ᶜ := by
  have hmp := measurePreserving_blocks (E := E) (κ := Fin 2 → Fin 2) (J := Fin 2) (ι := Fin 2)
    (g := fun (j i : Fin 2) ↦ cubeCorner dir j i) ν (cubeCorner_injective dir)
  have hpre : (fun (ζ : (Fin 2 → Fin 2) → E) (j i : Fin 2) ↦ ζ (cubeCorner dir j i)) ⁻¹'
      (patternChain G' dir 1) = G'ᶜ := by
    ext ζ
    have hz : pairCube E dir ((fun (j i : Fin 2) ↦ ζ (cubeCorner dir j i)) (0 : Fin 1).castSucc,
        (fun (j i : Fin 2) ↦ ζ (cubeCorner dir j i)) (0 : Fin 1).succ) = ζ := by
      rw [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      exact pairCube_cols dir ζ
    simp only [Set.mem_preimage, mem_patternChain, Fin.forall_fin_one, Set.mem_compl_iff, hz]
  rw [← hpre, hmp.measure_preimage (measurableSet_patternChain dir hG 1).nullMeasurableSet]

/-! #### The barrier segment and the strip it reads -/

/-- The site at position `t` along the direction `dir`, on the axis. -/
def segSite (dir : Fin 2) (t : ℤ) : Fin 2 → ℤ := fun l ↦ if l = dir then t else 0

/-- **Georgii's `D(k, ℓ)`** with `ℓ = k + m - 1`, in the direction `dir`: the segment of `m`
sites of `ℤ²` starting at `(k, 0)` for `dir = 0`, at `(0, k)` for `dir = 1`. -/
def barrierSeg (dir : Fin 2) (k : ℤ) (m : ℕ) : Finset (Fin 2 → ℤ) :=
  (Finset.range m).image fun j : ℕ ↦ segSite dir (k + (j : ℤ))

/-- The site of the `2 × (m + 1)` strip of spins read by the barrier event
`{D(k, k+m-1) ∩ V(G, ·) = ∅}`: position `k + j` along `dir` and `s` across it. -/
def barrierSite (dir : Fin 2) (k : ℤ) (j : ℕ) (s : Fin 2) : Fin 2 → ℤ :=
  fun l ↦ if l = dir then k + (j : ℤ) else ((s : ℕ) : ℤ)

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma mem_barrierSeg {dir : Fin 2} {k : ℤ} {m j : ℕ} (hj : j < m) :
    segSite dir (k + (j : ℤ)) ∈ barrierSeg dir k m :=
  Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma segSite_add_intCubeCast (dir : Fin 2) (t : ℤ) (c : Fin 2 → Fin 2) :
    segSite dir t + intCubeCast c = barrierSite dir t (c dir : ℕ) (c (Fin.rev dir)) := by
  funext l
  rcases fin_two_eq_or_rev l dir with rfl | rfl
  · simp [segSite, intCubeCast, barrierSite]
  · simp [segSite, intCubeCast, barrierSite, fin_two_rev_ne dir]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma barrierSite_add (dir : Fin 2) (k : ℤ) (j j' : ℕ) (s : Fin 2) :
    barrierSite dir (k + (j : ℤ)) j' s = barrierSite dir k (j + j') s := by
  funext l
  by_cases h : l = dir
  · simp only [barrierSite, h]
    push_cast
    ring
  · simp [barrierSite, h]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma barrierSite_mem_cubeSupport {dir : Fin 2} {k : ℤ} {m : ℕ} (hm : m ≠ 0) {j : ℕ}
    (hj : j ≤ m) (s : Fin 2) : barrierSite dir k j s ∈ cubeSupport (barrierSeg dir k m) := by
  classical
  rcases eq_or_lt_of_le hj with rfl | hlt
  · refine mem_cubeSupport_iff.2 ⟨segSite dir (k + ((j - 1 : ℕ) : ℤ)), mem_barrierSeg (by omega),
      cubeCorner dir 1 s, ?_⟩
    rw [segSite_add_intCubeCast, cubeCorner_self, cubeCorner_rev, barrierSite_add]
    have : (j - 1) + ((1 : Fin 2) : ℕ) = j := by
      have : ((1 : Fin 2) : ℕ) = 1 := rfl
      omega
    rw [this]
  · refine mem_cubeSupport_iff.2 ⟨segSite dir (k + (j : ℤ)), mem_barrierSeg hlt,
      cubeCorner dir 0 s, ?_⟩
    rw [segSite_add_intCubeCast, cubeCorner_self, cubeCorner_rev, barrierSite_add]
    have : j + ((0 : Fin 2) : ℕ) = j := by
      have : ((0 : Fin 2) : ℕ) = 0 := rfl
      omega
    rw [this]

/-- **Georgii, Step 1: the barrier event read slice by slice.**  The reference measure `λ^S`
gives the barrier event `{D(k, k+m-1) ∩ V(G, ·) = ∅}` exactly the probability that the `m + 1`
slices of the strip it reads form a chain of `m` cubes all failing the pattern. -/
theorem isssd_forall_notMem_latticePattern_eq_pi_patternChain (dir : Fin 2)
    (hG : MeasurableSet G') (hGsym : IsRSymmetric E G') (k : ℤ) {m : ℕ} (hm : m ≠ 0)
    (η : (Fin 2 → ℤ) → E) :
    Specification.isssd ν (cubeSupport (barrierSeg dir k m)) η
        {ω | ∀ i ∈ barrierSeg dir k m, i ∉ latticePattern E G' ω}
      = (Measure.pi fun _ : Fin (m + 1) ↦ (Measure.pi fun _ : Fin 2 ↦ ν))
          (patternChain G' dir m) := by
  classical
  set D := barrierSeg dir k m with hDdef
  set Δ := cubeSupport D with hΔdef
  set B := {ω : (Fin 2 → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G' ω} with hBdef
  have hBmeas : MeasurableSet B :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_forall_notMem_latticePattern hG D
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))
  set g : Fin (m + 1) → Fin 2 → ↥Δ := fun j s ↦
    ⟨barrierSite dir k (j : ℕ) s, barrierSite_mem_cubeSupport hm (Nat.lt_succ_iff.1 j.2) s⟩
    with hgdef
  have hginj : Function.Injective fun p : Fin (m + 1) × Fin 2 ↦ g p.1 p.2 := by
    rintro ⟨j, s⟩ ⟨j', s'⟩ h
    have h' : barrierSite dir k (j : ℕ) s = barrierSite dir k (j' : ℕ) s' := congrArg Subtype.val h
    have hval : ∀ (a : ℕ) (b : Fin 2), barrierSite dir k a b dir = k + (a : ℤ) := by
      intro a b; simp [barrierSite]
    have hval' : ∀ (a : ℕ) (b : Fin 2), barrierSite dir k a b (Fin.rev dir) = ((b : ℕ) : ℤ) := by
      intro a b; simp [barrierSite, fin_two_rev_ne dir]
    have hj : k + ((j : ℕ) : ℤ) = k + ((j' : ℕ) : ℤ) := by
      rw [← hval (j : ℕ) s, ← hval (j' : ℕ) s', h']
    have hs : ((s : ℕ) : ℤ) = ((s' : ℕ) : ℤ) := by
      rw [← hval' (j : ℕ) s, ← hval' (j' : ℕ) s', h']
    have hjv : (j : ℕ) = (j' : ℕ) := by omega
    have hsv : (s : ℕ) = (s' : ℕ) := by omega
    exact Prod.ext (Fin.ext hjv) (Fin.ext hsv)
  have hmp := measurePreserving_blocks (E := E) (κ := ↥Δ) (J := Fin (m + 1)) (ι := Fin 2) ν hginj
  have key : ∀ (x : ↥Δ → E) (jf : Fin m),
      latticeCubeView (juxt (Δ : Set (Fin 2 → ℤ)) η x) (segSite dir (k + ((jf : ℕ) : ℤ)))
        = pairCube E dir ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) := by
    intro x jf
    funext c
    rw [latticeCubeView_apply, segSite_add_intCubeCast, barrierSite_add,
      juxt_apply_of_mem (Finset.mem_coe.2 (barrierSite_mem_cubeSupport hm
        (by have := (c dir).isLt; have := jf.2; omega) (c (Fin.rev dir))))]
    rcases fin_two_cases (c dir) with hc | hc
    · rw [show pairCube E dir ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) c
        = x (g jf.castSucc (c (Fin.rev dir))) by simp [pairCube, hc]]
      congr 1
      refine Subtype.ext ?_
      simp only [hgdef, hc]
      norm_num
    · rw [show pairCube E dir ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) c
        = x (g jf.succ (c (Fin.rev dir))) by simp [pairCube, hc]]
      congr 1
      refine Subtype.ext ?_
      simp only [hgdef, hc, Fin.val_succ]
      norm_num
  have hpre : (juxt (Δ : Set (Fin 2 → ℤ)) η) ⁻¹' B
      = (fun (x : ↥Δ → E) (j : Fin (m + 1)) (s : Fin 2) ↦ x (g j s)) ⁻¹'
        (patternChain G' dir m) := by
    ext x
    simp only [Set.mem_preimage, hBdef, Set.mem_ofPred_eq, mem_patternChain]
    constructor
    · intro h jf
      have hh := h _ (mem_barrierSeg (dir := dir) (k := k) (m := m) jf.2)
      rw [mem_latticePattern_of_isRSymmetric hGsym, key x jf] at hh
      exact hh
    · intro h i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      have hjm : j < m := Finset.mem_range.1 hj
      have hk : latticeCubeView (juxt (Δ : Set (Fin 2 → ℤ)) η x) (segSite dir (k + (j : ℤ)))
          = pairCube E dir ((fun s ↦ x (g (⟨j, hjm⟩ : Fin m).castSucc s)),
            fun s ↦ x (g (⟨j, hjm⟩ : Fin m).succ s)) := key x ⟨j, hjm⟩
      rw [mem_latticePattern_of_isRSymmetric hGsym, hk]
      exact h ⟨j, hjm⟩
  rw [show Specification.isssd ν Δ η
      = Measure.map (juxt (Δ : Set (Fin 2 → ℤ)) η) (Measure.pi fun _ : Δ ↦ ν) from rfl,
    Measure.map_apply Measurable.juxt hBmeas, hpre,
    hmp.measure_preimage (measurableSet_patternChain dir hG m).nullMeasurableSet]

/-! #### Georgii, Step 1: the barrier event is not null -/

/-- **Georgii, Step 1 of (18.16), the missing link**: a barrier segment of any length has
positive probability under the reference measure `λ^S`, as soon as the pattern `G` is not
`λ^C`-almost sure.  The `r`-symmetry of `G` makes the slice relation symmetric, so
`MeasureTheory.pi_chainSet_one_eq_zero_of_pi_chainSet_eq_zero` reduces a null chain of any
length to a null chain of length one, which is `λ^C(E^C ∖ G)`. -/
theorem isssd_barrier_ne_zero (dir : Fin 2) (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0) (k : ℤ) {m : ℕ} (hm : m ≠ 0) (η : (Fin 2 → ℤ) → E) :
    Specification.isssd ν (cubeSupport (barrierSeg dir k m)) η
      {ω | ∀ i ∈ barrierSeg dir k m, i ∉ latticePattern E G' ω} ≠ 0 := by
  rw [isssd_forall_notMem_latticePattern_eq_pi_patternChain dir hG hGsym k hm η]
  intro h
  refine hGc ?_
  rw [← pi_patternChain_one (ν := ν) dir hG]
  exact pi_chainSet_one_eq_zero_of_pi_chainSet_eq_zero _
    ((measurable_pairCube (E := E) dir) hG.compl)
    (swap_preimage_pairCube_preimage_compl dir hGsym) hm h

end Chain

/-! ### `𝒢₀(Φ)` is quasi-Gibbsian at the reference measure `λ = ν` -/

/-- **Georgii, §18.1**: every element of `𝒢₀(Φ)` is quasi-Gibbsian *with the reference measure
`ν` of the specification*.  This is the form Step 1 of (18.16) consumes: the barrier event has
to be non-null for the same `ν` (`isssd_barrier_ne_zero`).  The version that only records the
existence of a witness is
`MeasureTheory.GibbsMeasure.isQuasiGibbsian_of_mem_GZero`. -/
theorem isQuasiGibbsianWith_of_mem_GZero {d : ℕ} {φ' : ((Fin d → Fin 2) → E) → ℝ}
    (hφ : Measurable φ') (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ' ζ)
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)} (hμ : μ ∈ GZero E φ' ν) :
    IsQuasiGibbsianWith ν (μ : Measure ((Fin d → ℤ) → E)) := by
  have := isPotential_cubePotential (E := E) (φ := φ') hφ
  exact isQuasiGibbsianWith_of_isGibbsMeasure_lambdaSpecification ν
    (Potential.isPremodifier_boltzmannFactor (Φ := cubePotential E φ') 1)
    (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec)
    (fun Λ η ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
    (mem_GP_of_mem_GZero hφ hM hμ)

/-! ### Georgii, Step 1 of the proof of (18.16): `μ(B_{k,ℓ}) = 1` -/

section Step1

open Peierls

variable {G' : Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
private lemma nonempty_of_isProbabilityMeasure [IsProbabilityMeasure ν] : Nonempty E := by
  rcases isEmpty_or_nonempty E with h | h
  · exact absurd (measure_univ (μ := ν)) (by simp [Set.univ_eq_empty_iff.2 h])
  · exact h

/-- **Georgii, Step 1 of the proof of Lemma (18.16).**  For a shift-invariant quasi-Gibbsian
random field `μ` with reference measure `λ = ν`, and a pattern `G` which is not `λ^C`-almost
sure, every barrier event `B(k, ℓ) = {D(k, ℓ) ∩ V(G, ·) = ∅}` occurs at infinitely many
translates along the orbit of `θ_a`, almost surely: `μ(B_{k,ℓ}) = 1`.

The event is local, so `isssd_barrier_ne_zero` makes it non-null for `λ^S`; the recurrence
theorem `MeasureTheory.GibbsMeasure.measure_setOf_frequently_shift_mem_eq_one` — Poincaré
recurrence applied to the conditional field on the tail event that the barrier is *not* seen
infinitely often — then gives full measure. -/
theorem measure_setOf_frequently_barrier_eq_one (dir : Fin 2) (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0)
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    {a : Fin 2 → ℤ} (ha : a ≠ 0) (hshift : MeasurePreserving (shift E a).toFun μ μ)
    (k : ℤ) {m : ℕ} (hm : m ≠ 0) :
    μ {ω | ∃ᶠ n in atTop, ((shift E a).toFun)^[n] ω ∈
      {ω' : (Fin 2 → ℤ) → E | ∀ i ∈ barrierSeg dir k m, i ∉ latticePattern E G' ω'}} = 1 := by
  have : Nonempty E := nonempty_of_isProbabilityMeasure (ν := ν)
  have hcyl := measurableSet_cylinderEvents_forall_notMem_latticePattern (E := E) hG
    (Δ := (cubeSupport (barrierSeg dir k m) : Set (Fin 2 → ℤ))) (barrierSeg dir k m)
    fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c)
  exact measure_setOf_frequently_shift_mem_eq_one (ν := ν)
    (η := fun _ ↦ Classical.arbitrary E) hq hshift (cylinderEvents_le_pi _ hcyl)
    (tail_measurableSet_setOf_frequently_shift_forall_notMem_latticePattern hG hGsym ha _)
    hcyl (isssd_barrier_ne_zero dir hG hGsym hGc k hm _)

/-- **Georgii's event `B` of Step 1**: almost surely, *every* segment `D(k, ℓ)` of the `dir`-axis
is a barrier of `V(G, ·)` at infinitely many translates along the orbit of `θ_a`. -/
theorem ae_forall_frequently_barrier (dir : Fin 2) (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0)
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    {a : Fin 2 → ℤ} (ha : a ≠ 0) (hshift : MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ∀ (k : ℤ) (m : ℕ), ∃ᶠ n in atTop,
      ∀ i ∈ barrierSeg dir k m, i ∉ latticePattern E G' (((shift E a).toFun)^[n] ω) := by
  have : Nonempty E := nonempty_of_isProbabilityMeasure (ν := ν)
  rw [ae_all_iff]
  intro k
  rw [ae_all_iff]
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · filter_upwards with ω
    refine Filter.Frequently.of_forall fun n i hi ↦ ?_
    simp [barrierSeg] at hi
  · set A : Set ((Fin 2 → ℤ) → E) := {ω | ∃ᶠ n in atTop, ((shift E a).toFun)^[n] ω ∈
      {ω' : (Fin 2 → ℤ) → E | ∀ i ∈ barrierSeg dir k m, i ∉ latticePattern E G' ω'}} with hA
    have hAmeas : MeasurableSet A :=
      measurableSet_setOf_frequently_iterate_mem hshift.measurable
        (cylinderEvents_le_pi _ (measurableSet_cylinderEvents_forall_notMem_latticePattern
          (E := E) hG (barrierSeg dir k m)
          fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c)))
    have h1 := measure_setOf_frequently_barrier_eq_one (ν := ν) dir hG hGsym hGc hq ha hshift k hm
    rw [ae_iff]
    have : {ω | ¬ ∃ᶠ n in atTop, ∀ i ∈ barrierSeg dir k m,
        i ∉ latticePattern E G' (((shift E a).toFun)^[n] ω)} = Aᶜ := rfl
    rw [this, prob_compl_eq_one_sub hAmeas, h1, tsub_self]

end Step1

/-! ### Georgii's event `X`: the origin is the centre of an infinite cross -/

section CrossEvent

open Peierls

variable {G' : Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- **The event that a given site shows the pattern (18.3) is measurable**, for an arbitrary
measurable `G ⊆ E^C`: (18.3) reads the spins of the elementary cube at `i` through the fixed
measurable bijection `r^i`, so `r`-symmetry of `G` is not needed.  The members of a stable
partition (18.23) are in general not `r`-symmetric, which is why §18.2 needs this form. -/
lemma measurableSet_setOf_mem_latticePattern {d : ℕ} {G' : Set ((Fin d → Fin 2) → E)}
    (hG : MeasurableSet G') (i : Fin d → ℤ) :
    MeasurableSet {ω : (Fin d → ℤ) → E | i ∈ latticePattern E G' ω} := by
  have hrw : {ω : (Fin d → ℤ) → E | i ∈ latticePattern E G' ω}
      = (fun ω : (Fin d → ℤ) → E ↦
          tauPow (cubeRefl E) (latticeToTorus 0 i) (latticeCubeView ω i)) ⁻¹' G' := rfl
  rw [hrw]
  exact ((measurable_tauPow (cubeRefl E) (latticeToTorus 0 i)).comp
    ((measurable_pi_apply i).comp measurable_latticeCubeView)) hG

omit [IsProbabilityMeasure ν] in
/-- Reachability inside `V(G, ·) ∩ Q` is a countable union of local events. -/
lemma measurableSet_setOf_reachIn (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (Q : Set Site) (o x : Site) :
    MeasurableSet {ω : (Fin 2 → ℤ) → E |
      ReachIn (latticeGraph 2) (latticePattern E G' ω ∩ Q) o x} := by
  classical
  have hrw : {ω : (Fin 2 → ℤ) → E |
      ReachIn (latticeGraph 2) (latticePattern E G' ω ∩ Q) o x}
      = ⋃ n : ℕ, ⋃ f ∈ {f : Fin (n + 1) → Site | f 0 = o ∧ f (Fin.last n) = x ∧
          (∀ k : Fin n, (latticeGraph 2).Adj (f k.castSucc) (f k.succ)) ∧ ∀ k, f k ∈ Q},
          ⋂ k, {ω : (Fin 2 → ℤ) → E | f k ∈ latticePattern E G' ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, exists_prop]
    constructor
    · intro h
      obtain ⟨n, f, h0, hn, hadj, hs⟩ := SimpleGraph.reachableIn_iff_exists_chain.1 h
      exact ⟨n, f, ⟨h0, hn, hadj, fun k ↦ (hs k).2⟩, fun k ↦ (hs k).1⟩
    · rintro ⟨n, f, ⟨h0, hn, hadj, hQ⟩, hW⟩
      exact SimpleGraph.reachableIn_iff_exists_chain.2
        ⟨n, f, h0, hn, hadj, fun k ↦ ⟨hW k, hQ k⟩⟩
  rw [hrw]
  refine MeasurableSet.iUnion fun n ↦ MeasurableSet.biUnion (Set.to_countable _) fun f _ ↦ ?_
  exact MeasurableSet.iInter fun k ↦ measurableSet_setOf_mem_latticePattern hG (f k)

omit [IsProbabilityMeasure ν] in
/-- Lying in an infinite cluster of `V(G, ·) ∩ Q` is a measurable event. -/
lemma measurableSet_setOf_mem_infiniteClusters (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (Q : Set Site) (o : Site) :
    MeasurableSet {ω : (Fin 2 → ℤ) → E |
      o ∈ (latticeGraph 2).infiniteClusters (latticePattern E G' ω ∩ Q)} := by
  have hrw : {ω : (Fin 2 → ℤ) → E |
      o ∈ (latticeGraph 2).infiniteClusters (latticePattern E G' ω ∩ Q)}
      = ⋂ n : ℕ, ⋃ x ∈ {x : Site | x ∉ box n}, {ω : (Fin 2 → ℤ) → E |
          ReachIn (latticeGraph 2) (latticePattern E G' ω ∩ Q) o x} := by
    ext ω
    rw [Set.mem_ofPred_eq, mem_infiniteClusters_iff_forall_exists]
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  rw [hrw]
  exact MeasurableSet.iInter fun n ↦ MeasurableSet.biUnion (Set.to_countable _)
    fun x _ ↦ measurableSet_setOf_reachIn hG hGsym Q o x

variable (E) in
/-- **Georgii's event `X`** in the proof of Lemma (18.16): the origin is the point of
intersection of an infinite "cross" of `V(G, ·)`, i.e. it lies in an infinite cluster of
`V(G, ·)` in each of the four quadrants. -/
def crossEvent (G' : Set ((Fin 2 → Fin 2) → E)) : Set ((Fin 2 → ℤ) → E) :=
  {ω | IsCrossCentre (latticePattern E G' ω) 0}

omit [IsProbabilityMeasure ν] in
lemma mem_crossEvent {ω : (Fin 2 → ℤ) → E} :
    ω ∈ crossEvent E G' ↔ IsCrossCentre (latticePattern E G' ω) 0 := Iff.rfl

omit [IsProbabilityMeasure ν] in
/-- Georgii's `X` is exactly the event bounded below in
`le_measure_cross_latticePattern`. -/
lemma crossEvent_eq :
    crossEvent E G' = {ω : (Fin 2 → ℤ) → E | ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) →
      (s₂ = 1 ∨ s₂ = -1) → (0 : Site) ∈ (latticeGraph 2).infiniteClusters
        (latticePattern E G' ω ∩ quadrant s₁ s₂)} := by
  ext ω
  simp only [mem_crossEvent, IsCrossCentre, Set.mem_ofPred_eq, quadrantAt_zero]

omit [IsProbabilityMeasure ν] in
lemma measurableSet_crossEvent (hG : MeasurableSet G') (hGsym : IsRSymmetric E G') :
    MeasurableSet (crossEvent E G') := by
  have hrw : crossEvent E G'
      = ⋂ s₁ ∈ ({1, -1} : Set ℤ), ⋂ s₂ ∈ ({1, -1} : Set ℤ),
        {ω : (Fin 2 → ℤ) → E | (0 : Site) ∈ (latticeGraph 2).infiniteClusters
          (latticePattern E G' ω ∩ quadrant s₁ s₂)} := by
    rw [crossEvent_eq]
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h s₁ hs₁ s₂ hs₂
      exact h s₁ s₂ hs₁ hs₂
    · intro h s₁ s₂ hs₁ hs₂
      exact h s₁ hs₁ s₂ hs₂
  rw [hrw]
  refine MeasurableSet.biInter (Set.Finite.countable (Set.toFinite _)) fun s₁ _ ↦ ?_
  exact MeasurableSet.biInter (Set.Finite.countable (Set.toFinite _)) fun s₂ _ ↦
    measurableSet_setOf_mem_infiniteClusters hG hGsym _ _

end CrossEvent

/-! ### Georgii, Step 1 in the geometric form used by Steps 2 and 3 -/

section Barriers2

open Peierls

variable {G' : Set ((Fin 2 → Fin 2) → E)}

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma nsmul_mk (a b : ℤ) (n : ℕ) : n • mk a b = mk ((n : ℤ) * a) ((n : ℤ) * b) := by
  rw [site_ext_iff]
  constructor <;> simp

omit [IsProbabilityMeasure ν] in
lemma mem_barrierSeg_iff {dir : Fin 2} {k : ℤ} {m : ℕ} {i : Fin 2 → ℤ} :
    i ∈ barrierSeg dir k m ↔ ∃ j < m, i = segSite dir (k + (j : ℤ)) := by
  simp only [barrierSeg, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨j, hj, hij⟩ ↦ ⟨j, hj, hij.symm⟩, fun ⟨j, hj, hij⟩ ↦ ⟨j, hj, hij.symm⟩⟩

omit [IsProbabilityMeasure ν] in
/-- The `n`-th shift of a barrier segment, in the four directions. -/
lemma notMem_latticePattern_shift_iff (hGsym : IsRSymmetric E G') (a : Fin 2 → ℤ) (n : ℕ)
    (i : Fin 2 → ℤ) (ω : (Fin 2 → ℤ) → E) :
    i ∉ latticePattern E G' (((shift E a).toFun)^[n] ω) ↔ i - n • a ∉ latticePattern E G' ω := by
  rw [shift_iterate_toFun, mem_latticePattern_shift_iff hGsym]

/-- **Georgii, Step 1 in geometric form: barriers above.**  Almost surely, every horizontal
segment `[-N, N] × {h}` with `h` arbitrarily large misses `V(G, ·)`. -/
theorem ae_barriers_up (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0) {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ]
    (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ∀ N y₀ : ℤ, ∃ h : ℤ, y₀ < h ∧
      ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ latticePattern E G' ω := by
  have ha : (mk 0 (-1) : Fin 2 → ℤ) ≠ 0 := by
    intro hc
    have := congrFun hc 1
    simp at this
  filter_upwards [ae_forall_frequently_barrier (ν := ν) 0 hG hGsym hGc hq ha
    (hshift (mk 0 (-1)))] with ω hω N y₀
  obtain ⟨n, hn, hbar⟩ := (hω (-N) (2 * N + 1).toNat).forall_exists_of_atTop
    (max (y₀ + 1) 0).toNat
  refine ⟨(n : ℤ), ?_, ?_⟩
  · have h1 : ((max (y₀ + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h2 := Int.self_le_toNat (max (y₀ + 1) 0)
    have h3 : y₀ + 1 ≤ max (y₀ + 1) 0 := le_max_left _ _
    omega
  · intro x hx hx'
    have hjmem : ∃ j : ℕ, j < (2 * N + 1).toNat ∧ -N + (j : ℤ) = x := by
      refine ⟨(x + N).toNat, ?_, ?_⟩
      · have := Int.self_le_toNat (2 * N + 1)
        have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
      · have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
    obtain ⟨j, hj, hjx⟩ := hjmem
    have hmem : segSite 0 (-N + (j : ℤ)) ∈ barrierSeg 0 (-N) (2 * N + 1).toNat :=
      mem_barrierSeg hj
    have := hbar _ hmem
    rw [notMem_latticePattern_shift_iff hGsym] at this
    have heq : segSite 0 (-N + (j : ℤ)) - n • (mk 0 (-1) : Fin 2 → ℤ) = mk x (n : ℤ) := by
      rw [nsmul_mk, site_ext_iff]
      constructor <;> simp [segSite, ← hjx]
    rwa [heq] at this

/-- **Georgii, Step 1 in geometric form: barriers below.** -/
theorem ae_barriers_down (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0) {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ]
    (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ∀ N y₀ : ℤ, ∃ h : ℤ, h < y₀ ∧
      ∀ x : ℤ, -N ≤ x → x ≤ N → mk x h ∉ latticePattern E G' ω := by
  have ha : (mk 0 1 : Fin 2 → ℤ) ≠ 0 := by
    intro hc
    have := congrFun hc 1
    simp at this
  filter_upwards [ae_forall_frequently_barrier (ν := ν) 0 hG hGsym hGc hq ha
    (hshift (mk 0 1))] with ω hω N y₀
  obtain ⟨n, hn, hbar⟩ := (hω (-N) (2 * N + 1).toNat).forall_exists_of_atTop
    (max (-y₀ + 1) 0).toNat
  refine ⟨-(n : ℤ), ?_, ?_⟩
  · have h1 : ((max (-y₀ + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h2 := Int.self_le_toNat (max (-y₀ + 1) 0)
    have h3 : -y₀ + 1 ≤ max (-y₀ + 1) 0 := le_max_left _ _
    omega
  · intro x hx hx'
    obtain ⟨j, hj, hjx⟩ : ∃ j : ℕ, j < (2 * N + 1).toNat ∧ -N + (j : ℤ) = x := by
      refine ⟨(x + N).toNat, ?_, ?_⟩
      · have := Int.self_le_toNat (2 * N + 1)
        have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
      · have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
    have := hbar _ (mem_barrierSeg (dir := 0) (k := -N) (m := (2 * N + 1).toNat) hj)
    rw [notMem_latticePattern_shift_iff hGsym] at this
    have heq : segSite 0 (-N + (j : ℤ)) - n • (mk 0 1 : Fin 2 → ℤ) = mk x (-(n : ℤ)) := by
      rw [nsmul_mk, site_ext_iff]
      constructor <;> simp [segSite, ← hjx]
    rwa [heq] at this

/-- **Georgii, Step 1 in geometric form: barriers to the right.** -/
theorem ae_barriers_right (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0) {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ]
    (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ∀ N x₀ : ℤ, ∃ h : ℤ, x₀ < h ∧
      ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ latticePattern E G' ω := by
  have ha : (mk (-1) 0 : Fin 2 → ℤ) ≠ 0 := by
    intro hc
    have := congrFun hc 0
    simp at this
  filter_upwards [ae_forall_frequently_barrier (ν := ν) 1 hG hGsym hGc hq ha
    (hshift (mk (-1) 0))] with ω hω N x₀
  obtain ⟨n, hn, hbar⟩ := (hω (-N) (2 * N + 1).toNat).forall_exists_of_atTop
    (max (x₀ + 1) 0).toNat
  refine ⟨(n : ℤ), ?_, ?_⟩
  · have h1 : ((max (x₀ + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h2 := Int.self_le_toNat (max (x₀ + 1) 0)
    have h3 : x₀ + 1 ≤ max (x₀ + 1) 0 := le_max_left _ _
    omega
  · intro x hx hx'
    obtain ⟨j, hj, hjx⟩ : ∃ j : ℕ, j < (2 * N + 1).toNat ∧ -N + (j : ℤ) = x := by
      refine ⟨(x + N).toNat, ?_, ?_⟩
      · have := Int.self_le_toNat (2 * N + 1)
        have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
      · have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
    have := hbar _ (mem_barrierSeg (dir := 1) (k := -N) (m := (2 * N + 1).toNat) hj)
    rw [notMem_latticePattern_shift_iff hGsym] at this
    have heq : segSite 1 (-N + (j : ℤ)) - n • (mk (-1) 0 : Fin 2 → ℤ) = mk (n : ℤ) x := by
      rw [nsmul_mk, site_ext_iff]
      constructor <;> simp [segSite, ← hjx]
    rwa [heq] at this

/-- **Georgii, Step 1 in geometric form: barriers to the left.** -/
theorem ae_barriers_left (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0) {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ]
    (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ∀ N x₀ : ℤ, ∃ h : ℤ, h < x₀ ∧
      ∀ x : ℤ, -N ≤ x → x ≤ N → mk h x ∉ latticePattern E G' ω := by
  have ha : (mk 1 0 : Fin 2 → ℤ) ≠ 0 := by
    intro hc
    have := congrFun hc 0
    simp at this
  filter_upwards [ae_forall_frequently_barrier (ν := ν) 1 hG hGsym hGc hq ha
    (hshift (mk 1 0))] with ω hω N x₀
  obtain ⟨n, hn, hbar⟩ := (hω (-N) (2 * N + 1).toNat).forall_exists_of_atTop
    (max (-x₀ + 1) 0).toNat
  refine ⟨-(n : ℤ), ?_, ?_⟩
  · have h1 : ((max (-x₀ + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h2 := Int.self_le_toNat (max (-x₀ + 1) 0)
    have h3 : -x₀ + 1 ≤ max (-x₀ + 1) 0 := le_max_left _ _
    omega
  · intro x hx hx'
    obtain ⟨j, hj, hjx⟩ : ∃ j : ℕ, j < (2 * N + 1).toNat ∧ -N + (j : ℤ) = x := by
      refine ⟨(x + N).toNat, ?_, ?_⟩
      · have := Int.self_le_toNat (2 * N + 1)
        have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
      · have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ x + N by omega)
        omega
    have := hbar _ (mem_barrierSeg (dir := 1) (k := -N) (m := (2 * N + 1).toNat) hj)
    rw [notMem_latticePattern_shift_iff hGsym] at this
    have heq : segSite 1 (-N + (j : ℤ)) - n • (mk 1 0 : Fin 2 → ℤ) = mk (-(n : ℤ)) x := by
      rw [nsmul_mk, site_ext_iff]
      constructor <;> simp [segSite, ← hjx]
    rwa [heq] at this

end Barriers2

/-! ### Georgii, Lemma (18.16), Step 4: the origin lies in the ocean -/

section Step4

open Peierls

variable {G' : Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- **Shift equivariance of Georgii's event `X`**: `θ_a ω ∈ X` exactly when `-a` is a cross
centre of `V(G, ω)`. -/
lemma mem_crossEvent_shift (hGsym : IsRSymmetric E G') (a : Fin 2 → ℤ) (ω : (Fin 2 → ℤ) → E) :
    (shift E a).toFun ω ∈ crossEvent E G' ↔ IsCrossCentre (latticePattern E G' ω) (-a) := by
  rw [mem_crossEvent, latticePattern_shift hGsym]
  have h := isCrossCentre_add (W := latticePattern E G' ω) (-a) a
  rwa [show (-a) + a = (0 : Fin 2 → ℤ) by abel] at h

omit [IsProbabilityMeasure ν] in
lemma mem_crossEvent_shift_iterate (hGsym : IsRSymmetric E G') (a : Fin 2 → ℤ) (n : ℕ)
    (ω : (Fin 2 → ℤ) → E) :
    ((shift E a).toFun)^[n] ω ∈ crossEvent E G' ↔
      IsCrossCentre (latticePattern E G' ω) (-(n • a)) := by
  rw [shift_iterate_toFun, mem_crossEvent_shift hGsym]

omit [IsProbabilityMeasure ν] in
lemma shift_apply_shift (a b : Fin 2 → ℤ) (ω : (Fin 2 → ℤ) → E) :
    (shift E a).toFun ((shift E b).toFun ω) = (shift E (a + b)).toFun ω :=
  congrFun (shift_toFun_comp_shift_toFun (E := E) a b) ω

/-- **Georgii, Lemma (18.16), Step 4.**  On the event `X` that the origin is the centre of an
infinite cross of `V(G, ·)`, the origin almost surely lies in the maximal ocean `ξ⁰_P(G, ·)`.

Poincaré recurrence along the four axis shifts produces cross centres `(0, n)` with `n`
arbitrarily large positive and negative, and, for any two of those heights `s` and `t`, cross
centres `(k, s)` and `(k, t)` with `k` arbitrarily large positive and negative; Step 1 supplies
barriers in all four directions; and `Peierls.exists_isOceanIn_of_crossCentres` turns that data
into an ocean inside `V(G, ω)`. -/
theorem ae_mem_crossEvent_imp_mem_latticeOceanPart_of_ne_zero (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (hGc : cubeMeasure 2 ν G'ᶜ ≠ 0)
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ω ∈ crossEvent E G' → (0 : Site) ∈ latticeOceanPart E G' ω := by
  classical
  have hXmeas := measurableSet_crossEvent hG hGsym
  have hrecU : ∀ᵐ ω ∂μ, ω ∈ crossEvent E G' →
      ∃ᶠ n in atTop, ((shift E (mk 0 (-1))).toFun)^[n] ω ∈ crossEvent E G' :=
    ((hshift (mk 0 (-1))).conservative).ae_mem_imp_frequently_image_mem hXmeas.nullMeasurableSet
  have hrecD : ∀ᵐ ω ∂μ, ω ∈ crossEvent E G' →
      ∃ᶠ n in atTop, ((shift E (mk 0 1)).toFun)^[n] ω ∈ crossEvent E G' :=
    ((hshift (mk 0 1)).conservative).ae_mem_imp_frequently_image_mem hXmeas.nullMeasurableSet
  set A : ℤ × ℤ → Set ((Fin 2 → ℤ) → E) := fun p ↦
    ((shift E (mk 0 (-p.1))).toFun ⁻¹' crossEvent E G') ∩
      ((shift E (mk 0 (-p.2))).toFun ⁻¹' crossEvent E G') with hAdef
  have hAmeas : ∀ p : ℤ × ℤ, MeasurableSet (A p) := fun p ↦
    (hXmeas.preimage (shift E _).measurable_toFun).inter
      (hXmeas.preimage (shift E _).measurable_toFun)
  have hrecR : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℤ, ω ∈ A p →
      ∃ᶠ k in atTop, ((shift E (mk (-1) 0)).toFun)^[k] ω ∈ A p := by
    rw [ae_all_iff]
    exact fun p ↦ ((hshift (mk (-1) 0)).conservative).ae_mem_imp_frequently_image_mem
      (hAmeas p).nullMeasurableSet
  have hrecL : ∀ᵐ ω ∂μ, ∀ p : ℤ × ℤ, ω ∈ A p →
      ∃ᶠ k in atTop, ((shift E (mk 1 0)).toFun)^[k] ω ∈ A p := by
    rw [ae_all_iff]
    exact fun p ↦ ((hshift (mk 1 0)).conservative).ae_mem_imp_frequently_image_mem
      (hAmeas p).nullMeasurableSet
  filter_upwards [hrecU, hrecD, hrecR, hrecL,
    ae_barriers_up (ν := ν) hG hGsym hGc hq hshift,
    ae_barriers_down (ν := ν) hG hGsym hGc hq hshift,
    ae_barriers_right (ν := ν) hG hGsym hGc hq hshift,
    ae_barriers_left (ν := ν) hG hGsym hGc hq hshift] with ω h1 h2 h3 h4 hbU hbD hbR hbL hX
  have hX' : IsCrossCentre (latticePattern E G' ω) 0 := hX
  have hmemA : ∀ s t : ℤ, IsCrossCentre (latticePattern E G' ω) (mk 0 s) →
      IsCrossCentre (latticePattern E G' ω) (mk 0 t) → ω ∈ A (s, t) := by
    intro s t hs ht
    have e1 : -(mk 0 (-s) : Fin 2 → ℤ) = mk 0 s := by rw [site_ext_iff]; simp
    have e2 : -(mk 0 (-t) : Fin 2 → ℤ) = mk 0 t := by rw [site_ext_iff]; simp
    exact ⟨by rw [Set.mem_preimage, mem_crossEvent_shift hGsym, e1]; exact hs,
      by rw [Set.mem_preimage, mem_crossEvent_shift hGsym, e2]; exact ht⟩
  obtain ⟨ξ, hξW, hocean⟩ := exists_isOceanIn_of_crossCentres
    (W := latticePattern E G' ω) (R := {i | IsCrossCentre (latticePattern E G' ω) i})
    hbU hbD hbR hbL (fun i hi ↦ hi) (by rw [Set.mem_ofPred_eq, mk_zero_zero]; exact hX')
    (fun M ↦ by
      obtain ⟨n, hn, hmem⟩ := (h1 hX).forall_exists_of_atTop (max (M + 1) 0).toNat
      rw [mem_crossEvent_shift_iterate hGsym] at hmem
      refine ⟨(n : ℤ), ?_, ?_⟩
      · have h1' : ((max (M + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        have h2' := Int.self_le_toNat (max (M + 1) 0)
        have h3' : M + 1 ≤ max (M + 1) 0 := le_max_left _ _
        omega
      · rwa [show -(n • (mk 0 (-1) : Fin 2 → ℤ)) = mk 0 (n : ℤ) by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hmem)
    (fun M ↦ by
      obtain ⟨n, hn, hmem⟩ := (h2 hX).forall_exists_of_atTop (max (-M + 1) 0).toNat
      rw [mem_crossEvent_shift_iterate hGsym] at hmem
      refine ⟨-(n : ℤ), ?_, ?_⟩
      · have h1' : ((max (-M + 1) 0).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        have h2' := Int.self_le_toNat (max (-M + 1) 0)
        have h3' : -M + 1 ≤ max (-M + 1) 0 := le_max_left _ _
        omega
      · rwa [show -(n • (mk 0 1 : Fin 2 → ℤ)) = mk 0 (-(n : ℤ)) by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hmem)
    (fun s t M hs ht ↦ by
      obtain ⟨k, hk, hmem⟩ := (h3 (s, t) (hmemA s t hs ht)).forall_exists_of_atTop
        (max (M + 1) 0).toNat
      rw [shift_iterate_toFun] at hmem
      obtain ⟨hm1, hm2⟩ := hmem
      rw [Set.mem_preimage, shift_apply_shift, mem_crossEvent_shift hGsym] at hm1 hm2
      refine ⟨(k : ℤ), ?_, ?_, ?_⟩
      · have h1' : ((max (M + 1) 0).toNat : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
        have h2' := Int.self_le_toNat (max (M + 1) 0)
        have h3' : M + 1 ≤ max (M + 1) 0 := le_max_left _ _
        omega
      · rwa [show -(mk 0 (-s) + k • (mk (-1) 0 : Fin 2 → ℤ)) = mk (k : ℤ) s by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hm1
      · rwa [show -(mk 0 (-t) + k • (mk (-1) 0 : Fin 2 → ℤ)) = mk (k : ℤ) t by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hm2)
    (fun s t M hs ht ↦ by
      obtain ⟨k, hk, hmem⟩ := (h4 (s, t) (hmemA s t hs ht)).forall_exists_of_atTop
        (max (-M + 1) 0).toNat
      rw [shift_iterate_toFun] at hmem
      obtain ⟨hm1, hm2⟩ := hmem
      rw [Set.mem_preimage, shift_apply_shift, mem_crossEvent_shift hGsym] at hm1 hm2
      refine ⟨-(k : ℤ), ?_, ?_, ?_⟩
      · have h1' : ((max (-M + 1) 0).toNat : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
        have h2' := Int.self_le_toNat (max (-M + 1) 0)
        have h3' : -M + 1 ≤ max (-M + 1) 0 := le_max_left _ _
        omega
      · rwa [show -(mk 0 (-s) + k • (mk 1 0 : Fin 2 → ℤ)) = mk (-(k : ℤ)) s by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hm1
      · rwa [show -(mk 0 (-t) + k • (mk 1 0 : Fin 2 → ℤ)) = mk (-(k : ℤ)) t by
          rw [nsmul_mk, site_ext_iff]; constructor <;> simp] at hm2)
  exact mem_oceanPart_of_isOceanIn hocean hξW hX'.mem_infiniteClusters

omit [IsProbabilityMeasure ν] in
lemma segSite_zero (dir : Fin 2) : segSite dir 0 = (0 : Fin 2 → ℤ) := by
  funext l
  simp [segSite]

omit [IsProbabilityMeasure ν] in
lemma barrierSeg_zero_one (dir : Fin 2) : barrierSeg dir 0 1 = {(0 : Fin 2 → ℤ)} := by
  rw [barrierSeg]
  ext i
  simp [segSite_zero]

/-- **Georgii, the degenerate case `λ^C(G) = 1` of the proof of Lemma (18.16).**  If the pattern
is `λ^C`-almost sure then `V(G, ·)` is almost surely the whole plane, which is an ocean. -/
theorem ae_mem_latticeOceanPart_of_cubeMeasure_compl_eq_zero (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (hGc : cubeMeasure 2 ν G'ᶜ = 0)
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, (0 : Site) ∈ latticeOceanPart E G' ω := by
  have : Nonempty E := nonempty_of_isProbabilityMeasure (ν := ν)
  have hmeas : ∀ i : Fin 2 → ℤ,
      MeasurableSet {ω : (Fin 2 → ℤ) → E | i ∉ latticePattern E G' ω} :=
    fun i ↦ (measurableSet_setOf_mem_latticePattern hG i).compl
  have h0 : μ {ω : (Fin 2 → ℤ) → E | (0 : Fin 2 → ℤ) ∉ latticePattern E G' ω} = 0 := by
    have hcyl := measurableSet_cylinderEvents_forall_notMem_latticePattern (E := E) hG
      (Δ := (cubeSupport (barrierSeg 0 0 1) : Set (Fin 2 → ℤ))) (barrierSeg 0 0 1)
      (fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))
    have heq : {ω : (Fin 2 → ℤ) → E | ∀ i ∈ barrierSeg 0 0 1, i ∉ latticePattern E G' ω}
        = {ω : (Fin 2 → ℤ) → E | (0 : Fin 2 → ℤ) ∉ latticePattern E G' ω} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, barrierSeg_zero_one]
      simp
    have hiszero : Specification.isssd ν (cubeSupport (barrierSeg 0 0 1))
        (fun _ ↦ Classical.arbitrary E)
        {ω : (Fin 2 → ℤ) → E | ∀ i ∈ barrierSeg 0 0 1, i ∉ latticePattern E G' ω} = 0 := by
      rw [isssd_forall_notMem_latticePattern_eq_pi_patternChain 0 hG hGsym 0 one_ne_zero,
        pi_patternChain_one 0 hG]
      exact hGc
    have hcond := (hq Set.univ MeasurableSet.univ (by simp)
      (cubeSupport (barrierSeg 0 0 1)) (fun _ ↦ Classical.arbitrary E)
      (cylinderEvents_le_pi _ hcyl |> fun _ ↦ hcyl)).2 hiszero
    rwa [ProbabilityTheory.cond_univ, heq] at hcond
  have hnull : ∀ i : Fin 2 → ℤ, μ {ω : (Fin 2 → ℤ) → E | i ∉ latticePattern E G' ω} = 0 := by
    intro i
    have hpre : (shift E i).toFun ⁻¹' {ω : (Fin 2 → ℤ) → E | i ∉ latticePattern E G' ω}
        = {ω : (Fin 2 → ℤ) → E | (0 : Fin 2 → ℤ) ∉ latticePattern E G' ω} := by
      ext ω
      rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
        mem_latticePattern_shift_iff hGsym, sub_self]
    have hmp := (hshift i).measure_preimage (hmeas i).nullMeasurableSet
    rw [hpre, h0] at hmp
    exact hmp.symm
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin 2 → ℤ, i ∈ latticePattern E G' ω := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    exact hnull i
  filter_upwards [hall] with ω hω
  have hW : latticePattern E G' ω = Set.univ := Set.eq_univ_of_forall hω
  rw [latticeOceanPart, hW]
  exact mem_oceanPart_of_isOceanIn isOceanIn_univ Set.Subset.rfl (mem_infiniteClusters_univ 0)

/-- **Georgii, Lemma (18.16).**  For a shift-invariant quasi-Gibbsian random field, the origin
lies almost surely in the maximal ocean `ξ⁰_P(G, ·)` on the event `X` that it is the centre of an
infinite cross of `V(G, ·)`. -/
theorem ae_mem_crossEvent_imp_mem_latticeOceanPart (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ]
    (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∀ᵐ ω ∂μ, ω ∈ crossEvent E G' → (0 : Site) ∈ latticeOceanPart E G' ω := by
  rcases eq_or_ne (cubeMeasure 2 ν G'ᶜ) 0 with hGc | hGc
  · filter_upwards [ae_mem_latticeOceanPart_of_cubeMeasure_compl_eq_zero hG hGsym hGc hq hshift]
      with ω hω _
    exact hω
  · exact ae_mem_crossEvent_imp_mem_latticeOceanPart_of_ne_zero hG hGsym hGc hq hshift

/-- **Georgii, Lemma (18.16)**, in the measure form: `μ(X) ≤ μ(0 ∈ ξ⁰_P(G, ·))`. -/
theorem measure_crossEvent_le (hG : MeasurableSet G') (hGsym : IsRSymmetric E G')
    {μ : Measure ((Fin 2 → ℤ) → E)} [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    μ (crossEvent E G') ≤ μ {ω | (0 : Site) ∈ latticeOceanPart E G' ω} := by
  have h := ae_mem_crossEvent_imp_mem_latticeOceanPart (ν := ν) hG hGsym hq hshift
  rw [ae_iff] at h
  calc μ (crossEvent E G')
      ≤ μ ({ω | (0 : Site) ∈ latticeOceanPart E G' ω} ∪
          {ω | ¬ (ω ∈ crossEvent E G' → (0 : Site) ∈ latticeOceanPart E G' ω)}) := by
        refine measure_mono fun ω hω ↦ ?_
        by_cases hc : (0 : Site) ∈ latticeOceanPart E G' ω
        · exact Or.inl hc
        · exact Or.inr fun himp ↦ hc (himp hω)
    _ ≤ μ {ω | (0 : Site) ∈ latticeOceanPart E G' ω}
        + μ {ω | ¬ (ω ∈ crossEvent E G' → (0 : Site) ∈ latticeOceanPart E G' ω)} :=
        measure_union_le _ _
    _ = μ {ω | (0 : Site) ∈ latticeOceanPart E G' ω} := by rw [h, add_zero]

end Step4

/-! ### Georgii, in the proof of Theorem (18.17): `{ξ⁰_P(G, ·) ≠ ∅}` is a tail event -/

section Tail

open Peierls

section AnyDim

variable {d : ℕ} {G' : Set ((Fin d → Fin 2) → E)}

/-- The sites whose elementary cube meets `Λ`, i.e. the sites at which Georgii (18.3) can change
when the spins in `Λ` are changed.  It is dual to `cubeSupport`, which collects the spins that
(18.3) reads over a given set of sites. -/
def cubePreSupport (Λ : Finset (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  Λ.biUnion fun x ↦ Finset.univ.image fun c : Fin d → Fin 2 ↦ x - intCubeCast c

lemma mem_cubePreSupport_iff {Λ : Finset (Fin d → ℤ)} {i : Fin d → ℤ} :
    i ∈ cubePreSupport Λ ↔ ∃ c, i + intCubeCast c ∈ Λ := by
  classical
  simp only [cubePreSupport, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, c, rfl⟩
    exact ⟨c, by simpa using hx⟩
  · rintro ⟨c, hc⟩
    exact ⟨i + intCubeCast c, hc, c, by abel⟩

omit [IsProbabilityMeasure ν] in
/-- **Georgii (18.3) reads only the spins outside `Λ` at the sites whose cube misses `Λ`.**  If
`ω` and `ω'` agree off a finite volume `Λ` then they show the same pattern at every site whose
elementary cube does not meet `Λ`. -/
lemma mem_latticePattern_congr_of_notMem_cubePreSupport {Λ : Finset (Fin d → ℤ)}
    {ω ω' : (Fin d → ℤ) → E} (h : ∀ i ∉ Λ, ω i = ω' i) {i : Fin d → ℤ}
    (hi : i ∉ cubePreSupport Λ) :
    i ∈ latticePattern E G' ω ↔ i ∈ latticePattern E G' ω' :=
  mem_latticePattern_congr fun c ↦ h _ fun hmem ↦ hi (mem_cubePreSupport_iff.2 ⟨c, hmem⟩)

omit [IsProbabilityMeasure ν] in
/-- **Altering the spins in a finite volume alters (18.3) only in a finite set of sites**: the
sites whose elementary cube meets that volume. -/
lemma latticePattern_diff_subset_cubePreSupport {Λ : Finset (Fin d → ℤ)}
    {ω ω' : (Fin d → ℤ) → E} (h : ∀ i ∉ Λ, ω i = ω' i) :
    latticePattern E G' ω \ latticePattern E G' ω' ⊆ (cubePreSupport Λ : Set (Fin d → ℤ)) := by
  intro i hi
  by_contra hmem
  exact hi.2 ((mem_latticePattern_congr_of_notMem_cubePreSupport h hmem).1 hi.1)

end AnyDim

variable {G' : Set ((Fin 2 → Fin 2) → E)}

omit [IsProbabilityMeasure ν] in
/-- **The event `{ξ⁰_P(G, ·) ≠ ∅}` is measurable.**  Georgii's Definition (18.6) is a countable
condition over the countable lattice `ℤ²`: `SimpleGraph.measurableSet_setOf_oceanPart_nonempty`
turns it into countably many reachability events, each of which is a countable union of the local
events `{i ∈ V(G, ·)}`. -/
lemma measurableSet_setOf_latticeOceanPart_nonempty (hG : MeasurableSet G') :
    MeasurableSet {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E G' ω).Nonempty} :=
  SimpleGraph.measurableSet_setOf_oceanPart_nonempty _ _
    (measurableSet_setOf_mem_latticePattern hG)

omit [IsProbabilityMeasure ν] in
/-- **Georgii, the tail property used in the proofs of Theorem (18.17) and Theorem (18.25)**:
`{ξ⁰_P(G, ·) ≠ ∅} ∈ 𝒯`, for an arbitrary measurable pattern `G`.

For a finite volume `Λ` the event is `𝓕_{Λᶜ}`-measurable, because it is measurable
(`measurableSet_setOf_latticeOceanPart_nonempty`) and depends only on the spins outside `Λ`:
changing those spins changes `V(G, ·)` only in the finitely many sites whose elementary cube
meets `Λ` (`latticePattern_diff_subset_cubePreSupport`), and whether a subset of the plane
contains an ocean is unchanged by a finite modification
(`Peierls.oceanPart_nonempty_congr_of_finite_diff`, whose planar input is the uniqueness of the
infinite cluster of a set with finite islands). -/
theorem tail_measurableSet_setOf_latticeOceanPart_nonempty (hG : MeasurableSet G) :
    MeasurableSet[@tailSigmaAlgebra (Fin 2 → ℤ) E _]
      {ω | (latticeOceanPart E G ω).Nonempty} := by
  have hamb : Measurable fun ω : (Fin 2 → ℤ) → E ↦ (latticeOceanPart E G ω).Nonempty := by
    rw [← measurableSet_setOfPred]
    exact measurableSet_setOf_latticeOceanPart_nonempty hG
  refine MeasurableSpace.measurableSet_iInf.2 fun Λ ↦ ?_
  have hdep : DependsOn (fun ω : (Fin 2 → ℤ) → E ↦ (latticeOceanPart E G ω).Nonempty)
      ((Λ : Set (Fin 2 → ℤ))ᶜ) := by
    intro ω ω' h
    have hΛ : ∀ i ∉ Λ, ω i = ω' i := fun i hi ↦ h i hi
    refine propext ?_
    change (latticeOceanPart E G ω).Nonempty ↔ (latticeOceanPart E G ω').Nonempty
    rw [latticeOceanPart, latticeOceanPart]
    exact oceanPart_nonempty_congr_of_finite_diff
      ((cubePreSupport Λ).finite_toSet.subset (latticePattern_diff_subset_cubePreSupport hΛ))
      ((cubePreSupport Λ).finite_toSet.subset
        (latticePattern_diff_subset_cubePreSupport fun i hi ↦ (hΛ i hi).symm))
  have hcyl := (hamb.cylinderEvents_of_dependsOn hdep) (measurableSet_singleton True)
  rwa [Set.preimage_singleton_true] at hcyl

end Tail

/-! ### Georgii, Theorem (18.17) and Corollary (18.18) -/

/-- **Georgii, Theorem (18.17).**  Let `G ∈ ℰ^C` be `r`-symmetric and let `Φ` be the
`C`-potential with cube interaction `φ`.  Then for every `μ ∈ 𝒢₀(Φ)`

`μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4 z(t(G, Φ))`.

This is Lemma (18.10) (`forall_notMem_latticePattern_le_patternWeight`), Lemma (18.14)
(`Peierls.le_measure_mem_infiniteClusters`) and Lemma (18.16)
(`measure_crossEvent_le`) combined. -/
theorem le_measure_mem_latticeOceanPart (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) (hG : MeasurableSet G)
    (hGsym : IsRSymmetric E G) {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)}
    (hμ : μ ∈ GZero E φ ν) :
    1 - 4 * Peierls.crossingBound (patternWeight φ ν G)
      ≤ (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Peierls.Site) ∈ latticeOceanPart E G ω} := by
  refine le_trans ?_ (measure_crossEvent_le (ν := ν) hG hGsym
    (isQuasiGibbsianWith_of_mem_GZero hφ ⟨M, hM⟩ hμ)
    (fun a ↦ measurePreserving_shift_of_mem_GZero hφ hμ a))
  rw [crossEvent_eq]
  exact le_measure_cross_latticePattern hφ hM hφk hG hGsym hμ

/-- **Georgii, Corollary (18.18)**, the uniform bound: for every `μ ∈ 𝒢₀(βΦ)` and every `ε`,

`μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) ≥ 1 - 4 z(t(G_ε(Φ), βΦ))`. -/
theorem le_measure_mem_latticeOceanPart_localGroundStates (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) (ε : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) {μ : ProbabilityMeasure ((Fin 2 → ℤ) → E)}
    (hμ : μ ∈ GZero E (fun ζ ↦ β * φ ζ) ν) :
    1 - 4 * Peierls.crossingBound
        (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))
      ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (localGroundStates φ ν ε) ω} :=
  le_measure_mem_latticeOceanPart (hφ.const_mul β) (M := β * M) (fun ζ ↦ by nlinarith [hM ζ])
    (fun k ζ ↦ by rw [hφk k ζ]) (measurableSet_localGroundStates hφ ε)
    (isRSymmetric_localGroundStates hφk ε) hμ

/-- **Georgii, Corollary (18.18)**, the limit: the uniform lower bound of
`le_measure_mem_latticeOceanPart_localGroundStates` tends to `1` as `β → ∞`, so that
`lim_{β→∞} inf_{μ ∈ 𝒢₀(βΦ)} μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) = 1`. -/
theorem tendsto_bound_latticeOceanPart_localGroundStates (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun β : ℝ ↦ 1 - 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 1) := by
  have h := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
  have h4 : Tendsto (fun β : ℝ ↦ 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε))) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) h (Or.inr (by norm_num))
  have hsub := ENNReal.Tendsto.sub (ma := fun _ : ℝ ↦ (1 : ℝ≥0∞))
    (mb := fun β : ℝ ↦ 4 * Peierls.crossingBound
      (patternWeight (fun ζ ↦ β * φ ζ) ν (localGroundStates φ ν ε)))
    tendsto_const_nhds h4 (Or.inl (by norm_num))
  simpa using hsub

/-- **Georgii, Lemma (18.16)** as stated: a shift-invariant quasi-Gibbsian `μ` with
`μ(0 ∈ ξ_Q(G, ·)) ≥ 1 - z` for each of the four quadrants `Q` with vertex `0` satisfies
`μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4z`.  Georgii's `z < 1/4` only makes the conclusion non-vacuous. -/
theorem le_measure_mem_latticeOceanPart_of_forall_quadrant {G' : Set ((Fin 2 → Fin 2) → E)}
    (hG : MeasurableSet G') (hGsym : IsRSymmetric E G') {μ : Measure ((Fin 2 → ℤ) → E)}
    [IsProbabilityMeasure μ] (hq : IsQuasiGibbsianWith ν μ)
    (hshift : ∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun μ μ) {z : ℝ≥0∞}
    (hz : ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
      1 - z ≤ μ {ω | (0 : Peierls.Site) ∈ (latticeGraph 2).infiniteClusters
        (latticePattern E G' ω ∩ Peierls.quadrant s₁ s₂)}) :
    1 - 4 * z ≤ μ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E G' ω} := by
  refine le_trans ?_ (measure_crossEvent_le (ν := ν) hG hGsym hq hshift)
  have hA : ∀ s₁ s₂ : ℤ, (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
      μ {ω | (0 : Peierls.Site) ∉ (latticeGraph 2).infiniteClusters
        (latticePattern E G' ω ∩ Peierls.quadrant s₁ s₂)} ≤ z := by
    intro s₁ s₂ hs₁ hs₂
    have hm := measurableSet_setOf_mem_infiniteClusters hG hGsym (Peierls.quadrant s₁ s₂) 0
    have h := tsub_le_iff_right.1 (hz s₁ s₂ hs₁ hs₂)
    rw [← Set.compl_setOf, prob_compl_eq_one_sub hm, tsub_le_iff_right, add_comm]
    exact h
  have hbad : μ (crossEvent E G')ᶜ ≤ 4 * z := by
    have hsub : (crossEvent E G')ᶜ ⊆
        {ω | (0 : Peierls.Site) ∉ (latticeGraph 2).infiniteClusters
          (latticePattern E G' ω ∩ Peierls.quadrant 1 1)} ∪
        {ω | (0 : Peierls.Site) ∉ (latticeGraph 2).infiniteClusters
          (latticePattern E G' ω ∩ Peierls.quadrant 1 (-1))} ∪
        {ω | (0 : Peierls.Site) ∉ (latticeGraph 2).infiniteClusters
          (latticePattern E G' ω ∩ Peierls.quadrant (-1) 1)} ∪
        {ω | (0 : Peierls.Site) ∉ (latticeGraph 2).infiniteClusters
          (latticePattern E G' ω ∩ Peierls.quadrant (-1) (-1))} := by
      intro ω hω
      rw [Set.mem_compl_iff, crossEvent_eq, Set.mem_ofPred_eq] at hω
      push_neg at hω
      obtain ⟨s₁, s₂, hs₁, hs₂, h⟩ := hω
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      rcases hs₁ with rfl | rfl <;> rcases hs₂ with rfl | rfl <;> tauto
    calc μ (crossEvent E G')ᶜ ≤ _ := measure_mono hsub
      _ ≤ z + z + z + z := by
        refine (measure_union_le _ _).trans (add_le_add ?_ (hA _ _ (by simp) (by simp)))
        refine (measure_union_le _ _).trans (add_le_add ?_ (hA _ _ (by simp) (by simp)))
        exact (measure_union_le _ _).trans
          (add_le_add (hA _ _ (by simp) (by simp)) (hA _ _ (by simp) (by simp)))
      _ = 4 * z := by ring
  rw [tsub_le_iff_right, ← prob_add_prob_compl (μ := μ) (measurableSet_crossEvent hG hGsym)]
  gcongr

/-- **Georgii, Corollary (18.18)** as displayed, over a standard Borel state space with a
confining cube interaction:
`lim_{β→∞} inf_{μ ∈ 𝒢₀(βΦ)} μ(0 ∈ ξ⁰_P(G_ε(Φ), ·)) = 1`. -/
theorem tendsto_iInf_measure_mem_latticeOceanPart_localGroundStates [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E}
    (hK : IsCubeConfining φ ν K) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun β : ℝ ↦ ⨅ μ ∈ GZero E (fun ζ ↦ β * φ ζ) ν, (μ : Measure ((Fin 2 → ℤ) → E))
      {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (localGroundStates φ ν ε) ω}) atTop (𝓝 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_bound_latticeOceanPart_localGroundStates (ν := ν) hφ hM hε) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with β hβ
    exact le_iInf₂ fun μ hμ ↦ le_measure_mem_latticeOceanPart_localGroundStates hφ hM hφk ε hβ hμ
  · filter_upwards [eventually_gt_atTop 0] with β hβ
    have : Nonempty E := ν.nonempty_of_neZero
    obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (hφ.const_mul β) (M := β * M)
      (fun ζ ↦ mul_le_mul_of_nonneg_left (hM ζ) hβ.le) (fun k ζ ↦ by rw [hφk k ζ])
      (hK.const_mul hβ) (fun _ ↦ Classical.arbitrary E)
    exact (iInf₂_le μ hμ).trans prob_le_one

end MeasureTheory.GibbsMeasure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.StarCrossing
public import GibbsMeasure.Specification.PeriodicGibbsLimits

/-!
# Georgii §18.1 in the plane: percolation of a spin pattern under `𝒢₀(Φ)`

Georgii, *Gibbs Measures and Phase Transitions*, §18.1, the passage from Lemma (18.10) to
Theorem (18.17).  For `d = 2` the plane `P` of (18.5) is the whole lattice, and the two
ingredients of Georgii's argument are already available:

* **(18.10)** for a Gibbs measure with periodic boundary condition,
  `MeasureTheory.GibbsMeasure.forall_notMem_latticePattern_le_patternWeight`, which is exactly
  the hypothesis shape `μ(D ∩ W = ∅) ≤ t^{|D|}` of
* **(18.14)**, `MeasureTheory.GibbsMeasure.Peierls.le_measure_mem_infiniteClusters`.

## Main results

* `le_measure_mem_infiniteClusters_latticePattern` — Georgii's displayed inequality between
  (18.14) and (18.15): `μ(0 ∈ ξ_Q(G, ·)) ≥ 1 - z(t(G, Φ))` for every `μ ∈ 𝒢₀(Φ)`, every
  `r`-symmetric `G` and each of the four quadrants `Q` of the plane with vertex `0`.
* `le_measure_cross_latticePattern` — the four-quadrant union bound `μ(X) ≥ 1 - 4 z(t(G, Φ))`
  for the event `X` that the origin is the centre of an infinite cross, which is the first
  paragraph of Georgii's proof of (18.16).
* `tendsto_crossingBound_patternWeight_localGroundStates` and
  `le_measure_mem_infiniteClusters_localGroundStates` — the low-temperature limit (Georgii
  (18.9)(4) plus the above): the bound `1 - z(t(G_ε(Φ), βΦ))` for
  `μ(0 ∈ ξ_Q(G_ε(Φ), ·))`, `μ ∈ 𝒢₀(βΦ)`, tends to `1` as `β → ∞`.  This is Georgii's
  Corollary (18.18) with the ocean `ξ⁰_P` replaced by the quadrant clusters `ξ_Q`.
* `latticeOceanPart` — **Georgii (18.7)** in the plane, `ξ⁰_P(G, ·)`, with
  `latticeOceanPart_nonempty_iff` and the shift equivariance `latticeOceanPart_shift`.

## What is still missing

Georgii's Lemma (18.16) — the passage from "the origin is the centre of an infinite cross in
`V(G, ·)`" to "the origin lies in an *ocean* of `V_P(G, ·)`" — is **not** proved here, and
neither is any statement that depends on it: Theorem (18.17), Corollary (18.18) in its stated
form, and Example (18.19).  Its Step 1 (the barrier events `B(k, ℓ)_∞(θ_{(0,-1)})`, which uses
Poincaré recurrence — Mathlib's `MeasureTheory.MeasurePreserving.conservative` together with
`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem` — and the quasi-Gibbs property
`MeasureTheory.GibbsMeasure.isQuasiGibbsian_of_mem_GZero`) is measure-theoretic and within
reach; its Steps 2 and 3 are a planar surgery on `ℤ²` paths ("`π_n^+` is bound to intersect
`π_{n+1}^-`"; "clearly this network is an ocean") for which Georgii gives pictures rather than
proofs.
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

end MeasureTheory.GibbsMeasure

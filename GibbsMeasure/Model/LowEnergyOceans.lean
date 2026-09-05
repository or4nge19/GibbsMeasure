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

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma cube_eta (c : Fin 2 → Fin 2) : ![c 0, c 1] = c := by
  funext l
  fin_cases l <;> simp

variable (E) in
/-- The cube configuration glued from its two columns.  Together with `patternChain` this
presents Georgii's barrier event `{D(k, ℓ) ∩ V(G, ·) = ∅}` as a *chain* condition on the
`|D| + 1` columns of the configuration that the event reads. -/
def pairCube (p : (Fin 2 → E) × (Fin 2 → E)) : (Fin 2 → Fin 2) → E :=
  fun c ↦ if c 0 = 0 then p.1 (c 1) else p.2 (c 1)

omit [IsProbabilityMeasure ν] in
lemma measurable_pairCube : Measurable (pairCube E) := by
  refine measurable_pi_lambda _ fun c ↦ ?_
  by_cases h : c 0 = 0
  · have hf : (fun p : (Fin 2 → E) × (Fin 2 → E) ↦ pairCube E p c) = fun p ↦ p.1 (c 1) := by
      funext p; simp [pairCube, h]
    rw [hf]
    exact (measurable_pi_apply (c 1)).comp measurable_fst
  · have hf : (fun p : (Fin 2 → E) × (Fin 2 → E) ↦ pairCube E p c) = fun p ↦ p.2 (c 1) := by
      funext p; simp [pairCube, h]
    rw [hf]
    exact (measurable_pi_apply (c 1)).comp measurable_snd

omit [IsProbabilityMeasure ν] in
/-- The two columns of a cube configuration glue back to it. -/
lemma pairCube_cols (ζ : (Fin 2 → Fin 2) → E) :
    pairCube E (fun i ↦ ζ ![0, i], fun i ↦ ζ ![1, i]) = ζ := by
  funext c
  rcases fin_two_cases (c 0) with hc | hc
  · have hcc : (![(0 : Fin 2), c 1] : Fin 2 → Fin 2) = c := by
      funext l; fin_cases l <;> simp [hc]
    rw [show pairCube E (fun i ↦ ζ ![0, i], fun i ↦ ζ ![1, i]) c = ζ ![0, c 1] by
      simp [pairCube, hc], hcc]
  · have hcc : (![(1 : Fin 2), c 1] : Fin 2 → Fin 2) = c := by
      funext l; fin_cases l <;> simp [hc]
    rw [show pairCube E (fun i ↦ ζ ![0, i], fun i ↦ ζ ![1, i]) c = ζ ![1, c 1] by
      simp [pairCube, hc], hcc]

omit [IsProbabilityMeasure ν] in
/-- Exchanging the two columns of a cube reflects it in the first direction. -/
lemma pairCube_swap (p : (Fin 2 → E) × (Fin 2 → E)) :
    pairCube E (Prod.swap p) = cubeRefl E 0 (pairCube E p) := by
  funext c
  rw [cubeRefl_apply, cubeSiteRefl_apply]
  have h0 : (Function.update c 0 (Fin.rev (c 0))) 0 = Fin.rev (c 0) := by simp
  have h1 : (Function.update c 0 (Fin.rev (c 0))) 1 = c 1 := by simp
  have hr0 : Fin.rev (0 : Fin 2) = 1 := by decide
  have hr1 : Fin.rev (1 : Fin 2) = 0 := by decide
  rcases fin_two_cases (c 0) with hc | hc
  · rw [pairCube, pairCube, h0, h1, hc, hr0]
    simp
  · rw [pairCube, pairCube, h0, h1, hc, hr1]
    simp

omit [IsProbabilityMeasure ν] in
/-- **The pattern relation between consecutive columns is symmetric** when the pattern is
`r`-symmetric: this is what makes Georgii's barrier event of positive probability for every
length (see `MeasureTheory.prod_eq_zero_of_pi_chainSet_eq_zero`). -/
lemma swap_preimage_pairCube_preimage_compl (hGsym : IsRSymmetric E G') :
    Prod.swap ⁻¹' (pairCube E ⁻¹' G'ᶜ) = pairCube E ⁻¹' G'ᶜ := by
  ext p
  simp only [Set.mem_preimage, pairCube_swap, Set.mem_compl_iff]
  exact not_congr (Set.ext_iff.1 (hGsym 0) (pairCube E p))

variable (G') in
/-- Georgii's barrier event as a chain condition on columns: the `m` consecutive elementary
cubes of a row formed by `m + 1` consecutive columns all fail the pattern `G`. -/
def patternChain (m : ℕ) : Set (Fin (m + 1) → (Fin 2 → E)) :=
  {y | ∀ j : Fin m, pairCube E (y j.castSucc, y j.succ) ∉ G'}

omit [IsProbabilityMeasure ν] in
lemma measurableSet_patternChain (hG : MeasurableSet G') (m : ℕ) :
    MeasurableSet (patternChain G' m) := by
  have hrw : patternChain G' m
      = ⋂ j : Fin m, (fun y : Fin (m + 1) → (Fin 2 → E) ↦
          pairCube E (y j.castSucc, y j.succ)) ⁻¹' G'ᶜ := by
    ext y
    simp [patternChain]
  rw [hrw]
  exact MeasurableSet.iInter fun j ↦
    (measurable_pairCube.comp
      ((measurable_pi_apply _).prodMk (measurable_pi_apply _))) hG.compl

/-- **The one-link chain is the pattern itself.**  Under the product measure the two columns of
an elementary cube are a `λ^C`-distributed cube configuration. -/
theorem pi_patternChain_one (hG : MeasurableSet G') :
    (Measure.pi fun _ : Fin (1 + 1) ↦ (Measure.pi fun _ : Fin 2 ↦ ν)) (patternChain G' 1)
      = cubeMeasure 2 ν G'ᶜ := by
  have hgc : Function.Injective fun p : Fin 2 × Fin 2 ↦ (![p.1, p.2] : Fin 2 → Fin 2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  have hmp := measurePreserving_blocks (E := E) (κ := Fin 2 → Fin 2) (J := Fin 2) (ι := Fin 2)
    (g := fun (j i : Fin 2) ↦ (![j, i] : Fin 2 → Fin 2)) ν hgc
  have hpre : (fun (ζ : (Fin 2 → Fin 2) → E) (j i : Fin 2) ↦ ζ ![j, i]) ⁻¹'
      (patternChain G' 1) = G'ᶜ := by
    ext ζ
    have hz : pairCube E ((fun (j i : Fin 2) ↦ ζ ![j, i]) (0 : Fin 1).castSucc,
        (fun (j i : Fin 2) ↦ ζ ![j, i]) (0 : Fin 1).succ) = ζ := by
      rw [Fin.castSucc_zero, Fin.succ_zero_eq_one]
      exact pairCube_cols ζ
    simp only [Set.mem_preimage, patternChain, Set.mem_ofPred_eq, Fin.forall_fin_one,
      Set.mem_compl_iff, hz]
  rw [← hpre, hmp.measure_preimage (measurableSet_patternChain hG 1).nullMeasurableSet]

/-! #### The barrier row and the strip it reads -/

/-- **Georgii's `D(k, ℓ)`** with `ℓ = k + m - 1`: the horizontal segment of `m` sites of `ℤ²`
starting at `(k, 0)`. -/
def barrierRow (k : ℤ) (m : ℕ) : Finset (Fin 2 → ℤ) :=
  (Finset.range m).image fun j : ℕ ↦ Peierls.mk (k + (j : ℤ)) 0

/-- The site `(k + j, s)` of the `2 × (m + 1)` strip of spins read by the barrier event
`{D(k, k+m-1) ∩ V(G, ·) = ∅}`. -/
def barrierSite (k : ℤ) (j : ℕ) (s : Fin 2) : Fin 2 → ℤ := Peierls.mk (k + j) ((s : ℕ) : ℤ)

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma intCubeCast_two (c : Fin 2 → Fin 2) :
    intCubeCast c = Peierls.mk ((c 0 : ℕ) : ℤ) ((c 1 : ℕ) : ℤ) := by
  funext l
  fin_cases l <;> simp [intCubeCast]

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma mk_add_mk (a b c e : ℤ) :
    Peierls.mk a b + Peierls.mk c e = Peierls.mk (a + c) (b + e) := by
  rw [Peierls.site_ext_iff]; simp

omit [MeasurableSpace E] [IsProbabilityMeasure ν] in
lemma barrierSite_mem_cubeSupport {k : ℤ} {m : ℕ} (hm : m ≠ 0) {j : ℕ} (hj : j ≤ m)
    (s : Fin 2) : barrierSite k j s ∈ cubeSupport (barrierRow k m) := by
  classical
  rcases eq_or_lt_of_le hj with rfl | hlt
  · refine mem_cubeSupport_iff.2 ⟨Peierls.mk (k + ((j - 1 : ℕ) : ℤ)) 0, ?_, ![1, s], ?_⟩
    · exact Finset.mem_image.2 ⟨j - 1, Finset.mem_range.2 (by omega), rfl⟩
    · rw [intCubeCast_two, mk_add_mk, barrierSite]
      have h0 : ((![(1 : Fin 2), s] : Fin 2 → Fin 2) 0 : ℕ) = 1 := rfl
      have h1 : ((![(1 : Fin 2), s] : Fin 2 → Fin 2) 1 : ℕ) = (s : ℕ) := rfl
      rw [h0, h1]
      congr 1
      · omega
      · omega
  · refine mem_cubeSupport_iff.2 ⟨Peierls.mk (k + (j : ℤ)) 0, ?_, ![0, s], ?_⟩
    · exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hlt, rfl⟩
    · rw [intCubeCast_two, mk_add_mk, barrierSite]
      have h0 : ((![(0 : Fin 2), s] : Fin 2 → Fin 2) 0 : ℕ) = 0 := rfl
      have h1 : ((![(0 : Fin 2), s] : Fin 2 → Fin 2) 1 : ℕ) = (s : ℕ) := rfl
      rw [h0, h1]
      congr 1
      · omega
      · omega

/-- **Georgii, Step 1: the barrier event read column by column.**  The reference measure `λ^S`
gives the barrier event `{D(k, k+m-1) ∩ V(G, ·) = ∅}` exactly the probability that the `m + 1`
columns of the strip it reads form a chain of `m` cubes all failing the pattern. -/
theorem isssd_forall_notMem_latticePattern_eq_pi_patternChain (hG : MeasurableSet G')
    (hGsym : IsRSymmetric E G') (k : ℤ) {m : ℕ} (hm : m ≠ 0) (η : (Fin 2 → ℤ) → E) :
    Specification.isssd ν (cubeSupport (barrierRow k m)) η
        {ω | ∀ i ∈ barrierRow k m, i ∉ latticePattern E G' ω}
      = (Measure.pi fun _ : Fin (m + 1) ↦ (Measure.pi fun _ : Fin 2 ↦ ν))
          (patternChain G' m) := by
  classical
  set D := barrierRow k m with hDdef
  set Δ := cubeSupport D with hΔdef
  set B := {ω : (Fin 2 → ℤ) → E | ∀ i ∈ D, i ∉ latticePattern E G' ω} with hBdef
  have hBmeas : MeasurableSet B :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_forall_notMem_latticePattern hG D
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))
  set g : Fin (m + 1) → Fin 2 → ↥Δ := fun j s ↦
    ⟨barrierSite k (j : ℕ) s, barrierSite_mem_cubeSupport hm (Nat.lt_succ_iff.1 j.2) s⟩
    with hgdef
  have hginj : Function.Injective fun p : Fin (m + 1) × Fin 2 ↦ g p.1 p.2 := by
    rintro ⟨j, s⟩ ⟨j', s'⟩ h
    have h' : barrierSite k (j : ℕ) s = barrierSite k (j' : ℕ) s' := congrArg Subtype.val h
    rw [barrierSite, barrierSite, Peierls.site_ext_iff] at h'
    simp only [Peierls.mk_zero, Peierls.mk_one] at h'
    have hj : (j : ℕ) = (j' : ℕ) := by omega
    have hs : (s : ℕ) = (s' : ℕ) := by omega
    exact Prod.ext (Fin.ext hj) (Fin.ext hs)
  have hmp := measurePreserving_blocks (E := E) (κ := ↥Δ) (J := Fin (m + 1)) (ι := Fin 2) ν hginj
  have key : ∀ (x : ↥Δ → E) (jf : Fin m),
      latticeCubeView (juxt (Δ : Set (Fin 2 → ℤ)) η x) (Peierls.mk (k + ((jf : ℕ) : ℤ)) 0)
        = pairCube E ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) := by
    intro x jf
    funext c
    rw [latticeCubeView_apply]
    have hsite : Peierls.mk (k + ((jf : ℕ) : ℤ)) 0 + intCubeCast c
        = barrierSite k ((jf : ℕ) + ((c 0 : ℕ))) (c 1) := by
      rw [intCubeCast_two, mk_add_mk, barrierSite]
      congr 1
      · push_cast; ring
      · omega
    rw [hsite, juxt_apply_of_mem (Finset.mem_coe.2
      (barrierSite_mem_cubeSupport hm (by have := (c 0).isLt; omega) (c 1)))]
    rcases fin_two_cases (c 0) with hc | hc
    · rw [show pairCube E ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) c
        = x (g jf.castSucc (c 1)) by simp [pairCube, hc]]
      congr 1
      exact Subtype.ext (by simp [hgdef, barrierSite, hc])
    · rw [show pairCube E ((fun s ↦ x (g jf.castSucc s)), fun s ↦ x (g jf.succ s)) c
        = x (g jf.succ (c 1)) by simp [pairCube, hc]]
      congr 1
      refine Subtype.ext ?_
      simp only [hgdef, barrierSite, hc, Fin.val_succ]
      norm_num
  have hpre : (juxt (Δ : Set (Fin 2 → ℤ)) η) ⁻¹' B
      = (fun (x : ↥Δ → E) (j : Fin (m + 1)) (s : Fin 2) ↦ x (g j s)) ⁻¹'
        (patternChain G' m) := by
    ext x
    simp only [Set.mem_preimage, hBdef, Set.mem_ofPred_eq, patternChain]
    constructor
    · intro h jf
      have hmem : Peierls.mk (k + ((jf : ℕ) : ℤ)) 0 ∈ D :=
        Finset.mem_image.2 ⟨(jf : ℕ), Finset.mem_range.2 jf.2, rfl⟩
      have hh := h _ hmem
      rw [mem_latticePattern_of_isRSymmetric hGsym, key x jf] at hh
      exact hh
    · intro h i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      rw [mem_latticePattern_of_isRSymmetric hGsym]
      have hjf : ((⟨j, Finset.mem_range.1 hj⟩ : Fin m) : ℕ) = j := rfl
      rw [show (Peierls.mk (k + (j : ℤ)) 0) = Peierls.mk (k + ((⟨j, Finset.mem_range.1 hj⟩ :
        Fin m) : ℕ) : ℤ) 0 by rw [hjf], key x ⟨j, Finset.mem_range.1 hj⟩]
      exact h ⟨j, Finset.mem_range.1 hj⟩
  rw [show Specification.isssd ν Δ η
      = Measure.map (juxt (Δ : Set (Fin 2 → ℤ)) η) (Measure.pi fun _ : Δ ↦ ν) from rfl,
    Measure.map_apply Measurable.juxt hBmeas, hpre,
    hmp.measure_preimage (measurableSet_patternChain hG m).nullMeasurableSet]

end Chain

end MeasureTheory.GibbsMeasure

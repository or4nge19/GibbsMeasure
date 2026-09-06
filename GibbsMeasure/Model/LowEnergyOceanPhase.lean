/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.Recurrence
public import GibbsMeasure.Model.LowEnergyOceans
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.PeriodicGibbsSymmetry

/-!
# Georgii (18.17) and (18.18), second assertions: a Gibbs measure carried by a low-energy ocean

Georgii, *Gibbs Measures and Phase Transitions*, §18.1.  The first assertions of Theorem (18.17)
and Corollary (18.18) — the lower bound `μ(0 ∈ ξ⁰_P(G, ·)) ≥ 1 - 4 z(t(G, Φ))` for `μ ∈ 𝒢₀(Φ)`
and its limit as `β → ∞` — are `GibbsMeasure/Model/LowEnergyOceans.lean`.  Here is what Georgii
deduces from them: as soon as the bound is non-trivial there is a Gibbs measure for which the
plane percolates *almost surely*, and it inherits the symmetries of `Φ`.

Georgii's argument is one line: put `μ = ν(· | ξ⁰_P(G, ·) ≠ ∅)` for a `ν ∈ 𝒢₀(Φ)`.  Its three
inputs are

* `𝒢₀(Φ) ≠ ∅` over a standard Borel state space — Proposition (18.12), `GZero_nonempty`;
* `{ξ⁰_P(G, ·) ≠ ∅} ∈ 𝒯`, so that conditioning stays inside `𝒢(Φ)` by Theorem (7.7)(b) —
  `tail_measurableSet_setOf_latticeOceanPart_nonempty` and `isGibbsMeasure_cond_of_tail`;
* the invariance of `ν` *and* of the conditioning event under the same transformations, so that
  the conditional measure is again invariant — `MeasurePreserving.cond_of_preimage_eq`.

## Main results

* `preimage_shift_setOf_latticeOceanPart_nonempty`,
  `preimage_latticeRefl_setOf_latticeOceanPart_nonempty` — the event `{ξ⁰_P(G, ·) ≠ ∅}` is
  strictly invariant under the shifts `θ_a` and under Georgii's reflections `r_1, …, r_d` of the
  lattice, for an `r`-symmetric pattern.  The second rests on the equivariance
  `V(G, r_k ω) = A_k V(G, ω)` of (18.3) (`CubeTransformation.latticePattern_onLattice`) and on
  the equivariance of the ocean part under the coordinate sign flip `A_k`
  (`Peierls.oceanPart_image_refl`).
* `exists_mem_GP_measure_setOf_latticeOceanPart_nonempty_eq_one` — **Georgii, Theorem (18.17),
  second assertion**: over a standard Borel state space, for a confining `C`-potential and an
  `r`-symmetric `G` with `z(t(G, Φ)) < 1/4`, there is a `μ ∈ 𝒢(Φ)` invariant under every shift
  and every reflection `r_k` with `μ(ξ⁰_P(G, ·) ≠ ∅) = 1`.
* `eventually_exists_mem_GP_measure_setOf_latticeOceanPart_localGroundStates_eq_one` —
  **Georgii, Corollary (18.18), second assertion**: the same for `G = G_ε(Φ)` and `βΦ`, for all
  large `β`.

Georgii states the invariance for the shifts `(θ_i)_{i ∈ P}` of the plane `P` of (18.5); for
`d = 2`, the case formalised here, `P` is the whole lattice and the shift group is the whole of
`ℤ²`.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {φ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E}
  [IsProbabilityMeasure ν] {G : Set ((Fin 2 → Fin 2) → E)}

/-! ### `{ξ⁰_P(G, ·) ≠ ∅}` is invariant under the shifts and the reflections -/

section Invariance

omit [IsProbabilityMeasure ν] in
/-- **The event `{ξ⁰_P(G, ·) ≠ ∅}` is strictly shift invariant.**  One of the two invariances
Georgii uses at the end of the proof of Theorem (18.17). -/
theorem preimage_shift_setOf_latticeOceanPart_nonempty (hGsym : IsRSymmetric E G)
    (a : Fin 2 → ℤ) :
    (shift E a).toFun ⁻¹' {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E G ω).Nonempty}
      = {ω | (latticeOceanPart E G ω).Nonempty} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, latticeOceanPart_shift hGsym,
    Set.image_nonempty]

omit [IsProbabilityMeasure ν] in
/-- **Georgii (18.3) under the reflection `r_k` of the lattice**: for an `r`-symmetric pattern,
`V(G, r_k ω)` is the image of `V(G, ω)` under the linear part `A_k` of `r_k`, the sign flip of
the `k`-th coordinate.  (The reflections `r^i` of (18.3) drop out precisely because `G` is
`r`-symmetric; this is `CubeTransformation.latticePattern_onLattice` at `τ = r_k`.) -/
theorem latticePattern_latticeRefl (hGsym : IsRSymmetric E G) (k : Fin 2)
    (ω : (Fin 2 → ℤ) → E) :
    latticePattern E G ((siteEquiv E (latticeReflAt k)).toFun ω)
      = (CubeTransformation.refl (E := E) k).lin '' latticePattern E G ω := by
  rw [← CubeTransformation.refl_onLattice E k, CubeTransformation.latticePattern_onLattice,
    CubeTransformation.refl_onCube_toFun, hGsym k]

omit [IsProbabilityMeasure ν] in
/-- The linear part of Georgii's reflection `r_k` of the plane is the coordinate sign flip
`Peierls.refl`, whose action on the ocean part is `Peierls.oceanPart_image_refl`. -/
theorem coe_cubeTransformationRefl_lin (k : Fin 2) :
    ⇑(CubeTransformation.refl (E := E) k).lin
      = Peierls.refl (if k = 0 then -1 else 1) (if k = 0 then 1 else -1) := by
  funext x
  rw [Peierls.site_ext_iff]
  fin_cases k <;>
    exact ⟨by simp [CubeTransformation.lin, CubeTransformation.refl],
      by simp [CubeTransformation.lin, CubeTransformation.refl]⟩

omit [IsProbabilityMeasure ν] in
/-- **The event `{ξ⁰_P(G, ·) ≠ ∅}` is strictly invariant under Georgii's reflections `r_k`.**
The second of the two invariances at the end of the proof of Theorem (18.17). -/
theorem preimage_latticeRefl_setOf_latticeOceanPart_nonempty (hGsym : IsRSymmetric E G)
    (k : Fin 2) :
    (siteEquiv E (latticeReflAt k)).toFun ⁻¹'
        {ω : (Fin 2 → ℤ) → E | (latticeOceanPart E G ω).Nonempty}
      = {ω | (latticeOceanPart E G ω).Nonempty} := by
  ext ω
  rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, latticeOceanPart, latticeOceanPart,
    latticePattern_latticeRefl hGsym k, coe_cubeTransformationRefl_lin,
    Peierls.oceanPart_image_refl (by split_ifs <;> simp) (by split_ifs <;> simp),
    Set.image_nonempty]

end Invariance

/-! ### Georgii, Theorem (18.17), second assertion -/

private lemma four_mul_lt_one_of_lt_one_div_four {z : ℝ≥0∞} (hz : z < 1 / 4) : 4 * z < 1 := by
  have h0 : (4 : ℝ≥0∞) ≠ 0 := by norm_num
  have htop : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  calc (4 : ℝ≥0∞) * z = z * 4 := mul_comm _ _
    _ < 1 / 4 * 4 := ENNReal.mul_lt_mul_left h0 htop hz
    _ = 1 := by rw [one_div, ENNReal.inv_mul_cancel h0 htop]

/-- **Georgii, Theorem (18.17), second assertion.**  Let `(E, ℰ)` be standard Borel, let `Φ` be
the `C`-potential with cube interaction `φ` — measurable, bounded below, invariant under the
reflections of `C` (17.18)(iii), and confining (17.18)(iv) — and let `G ∈ ℰ^C` be `r`-symmetric
with `z(t(G, Φ)) < 1/4`.  Then there is a Gibbs measure `μ ∈ 𝒢(Φ)`, invariant under the shift
group of the plane and under the reflections `r_1, r_2`, with

`μ(ξ⁰_P(G, ·) ≠ ∅) = 1`.

Georgii's proof, verbatim: pick `ν ∈ 𝒢₀(Φ)`, which is nonempty by Proposition (18.12)
(`GZero_nonempty`); the first assertion `le_measure_mem_latticeOceanPart` makes the event
`{ξ⁰_P(G, ·) ≠ ∅}` of `ν`-measure at least `1 - 4 z(t(G, Φ)) > 0`; the event is a tail event
(`tail_measurableSet_setOf_latticeOceanPart_nonempty`), so `μ = ν(· | ξ⁰_P(G, ·) ≠ ∅)` is again
Gibbs by Theorem (7.7)(b) (`isGibbsMeasure_cond_of_tail`); and `ν` and the event are invariant
under the same transformations, so `μ` is too
(`MeasureTheory.MeasurePreserving.cond_of_preimage_eq`). -/
theorem exists_mem_GP_measure_setOf_latticeOceanPart_nonempty_eq_one [StandardBorelSpace E]
    (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E}
    (hK : IsCubeConfining φ ν K) (hG : MeasurableSet G) (hGsym : IsRSymmetric E G)
    (hz : Peierls.crossingBound (patternWeight φ ν G) < 1 / 4) :
    ∃ μ ∈ GP (cubeGibbsSpec E φ ν hφ ⟨M, hM⟩),
      (∀ a : Fin 2 → ℤ,
          MeasurePreserving (shift E a).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
        (∀ k : Fin 2, MeasurePreserving (siteEquiv E (latticeReflAt k)).toFun
          (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
        (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (latticeOceanPart E G ω).Nonempty} = 1 := by
  classical
  have hne : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨ν₀, hν₀⟩ :=
    GZero_nonempty (d := 1) (ν := ν) hφ hM hφk hK fun _ ↦ Classical.arbitrary E
  set A : Set ((Fin 2 → ℤ) → E) := {ω | (latticeOceanPart E G ω).Nonempty} with hAdef
  have hAmeas : MeasurableSet A := measurableSet_setOf_latticeOceanPart_nonempty hG
  have hAtail : MeasurableSet[@tailSigmaAlgebra (Fin 2 → ℤ) E _] A :=
    tail_measurableSet_setOf_latticeOceanPart_nonempty hG
  -- `ν₀(ξ⁰_P ≠ ∅) ≥ ν₀(0 ∈ ξ⁰_P) ≥ 1 - 4 z > 0`.
  have hA0 : (ν₀ : Measure ((Fin 2 → ℤ) → E)) A ≠ 0 := by
    intro h0
    have hle : 1 - 4 * Peierls.crossingBound (patternWeight φ ν G)
        ≤ (ν₀ : Measure ((Fin 2 → ℤ) → E)) A :=
      (le_measure_mem_latticeOceanPart (ν := ν) hφ hM hφk hG hGsym hν₀).trans
        (measure_mono fun ω hω ↦ ⟨0, hω⟩)
    rw [h0, nonpos_iff_eq_zero, tsub_eq_zero_iff_le] at hle
    exact absurd hle (not_le_of_gt (four_mul_lt_one_of_lt_one_div_four hz))
  have hprob : IsProbabilityMeasure ((ν₀ : Measure ((Fin 2 → ℤ) → E))[|A]) :=
    ProbabilityTheory.cond_isProbabilityMeasure hA0
  refine ⟨⟨(ν₀ : Measure ((Fin 2 → ℤ) → E))[|A], hprob⟩, ?_, fun a ↦ ?_, fun k ↦ ?_, ?_⟩
  · exact isGibbsMeasure_cond_of_tail (γ := cubeGibbsSpec E φ ν hφ ⟨M, hM⟩) _
      (mem_GP_of_mem_GZero hφ ⟨M, hM⟩ hν₀) hAtail hA0
  · exact (measurePreserving_shift_of_mem_GZero hφ hν₀ a).cond_of_preimage_eq hAmeas
      (preimage_shift_setOf_latticeOceanPart_nonempty hGsym a)
  · exact (measurePreserving_latticeRefl_of_mem_GZero hφ ⟨M, hM⟩ hφk k hν₀).cond_of_preimage_eq
      hAmeas (preimage_latticeRefl_setOf_latticeOceanPart_nonempty hGsym k)
  · exact ProbabilityTheory.cond_apply_self hA0 (measure_ne_top _ _)

/-! ### Georgii, Corollary (18.18), second assertion -/

/-- **Georgii, Corollary (18.18), second assertion.**  For a standard Borel state space, a
confining `C`-potential `Φ` and `ε > 0`, all sufficiently large `β` admit a Gibbs measure for
`βΦ` which inherits the shift group of the plane and the reflections `r_1, r_2` of `Φ` and gives
full mass to the event that the local `ε`-ground states percolate in an ocean:

`μ(ξ⁰_P(G_ε(Φ), ·) ≠ ∅) = 1`.

This is Theorem (18.17) applied to `G_ε(Φ)` and `βΦ`, together with Remark (18.9)(4) in the
form `t(G_ε(Φ), βΦ) → 0`, hence `z(t(G_ε(Φ), βΦ)) → 0` as `β → ∞`
(`tendsto_crossingBound_patternWeight_localGroundStates`).

The universally quantified `hM'` is a formality: `cubeGibbsSpec` takes a proof that the cube
interaction is bounded below, `β * φ` is bounded below for every `β ≥ 0`, and the specification
does not depend on which proof is supplied. -/
theorem eventually_exists_mem_GP_measure_setOf_latticeOceanPart_localGroundStates_eq_one
    [StandardBorelSpace E] (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin 2) ζ, φ (cubeRefl E k ζ) = φ ζ) {K : ℕ → Set E}
    (hK : IsCubeConfining φ ν K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∃ μ : ProbabilityMeasure ((Fin 2 → ℤ) → E),
      (∀ hM' : ∃ M' : ℝ, ∀ ζ, M' ≤ β * φ ζ,
          μ ∈ GP (cubeGibbsSpec E (fun ζ ↦ β * φ ζ) ν (hφ.const_mul β) hM')) ∧
        (∀ a : Fin 2 → ℤ,
            MeasurePreserving (shift E a).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
          (∀ k : Fin 2, MeasurePreserving (siteEquiv E (latticeReflAt k)).toFun
            (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
          (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (latticeOceanPart E (localGroundStates φ ν ε) ω).Nonempty} = 1 := by
  have hpos : (0 : ℝ≥0∞) < 1 / 4 := by
    rw [one_div]
    exact ENNReal.inv_pos.2 (by norm_num)
  have htend := tendsto_crossingBound_patternWeight_localGroundStates (ν := ν) hφ hM hε
  filter_upwards [eventually_gt_atTop (0 : ℝ), htend (Iio_mem_nhds hpos)] with β hβ hzβ
  obtain ⟨μ, hμGP, hμshift, hμrefl, hμocean⟩ :=
    exists_mem_GP_measure_setOf_latticeOceanPart_nonempty_eq_one (ν := ν)
      (hφ.const_mul β) (M := β * M) (fun ζ ↦ mul_le_mul_of_nonneg_left (hM ζ) hβ.le)
      (fun k ζ ↦ by rw [hφk k ζ]) (hK.const_mul hβ)
      (measurableSet_localGroundStates hφ ε) (isRSymmetric_localGroundStates hφk ε) hzβ
  exact ⟨μ, fun _ ↦ hμGP, hμshift, hμrefl, hμocean⟩

end MeasureTheory.GibbsMeasure

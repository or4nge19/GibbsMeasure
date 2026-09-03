/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ErgodicGibbsLimits
public import GibbsMeasure.Specification.LocalContinuity
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Georgii §14.1–14.2: the remaining items (14.13), (14.16), (14.21)–(14.24)

This file disposes of the last unclaimed numbered items of Chapter 14 that are not full theorems
already carried by `Specification/Ergodicity.lean`, `Specification/ErgodicGibbs.lean`,
`Specification/ErgodicMixing.lean`, `Specification/ErgodicDense.lean`,
`Specification/InvariantDecomposition.lean` and `Specification/ErgodicGibbsLimits.lean`.

## (14.21)–(14.24): already present, and what was genuinely missing

These four displays sit inside Georgii's proof of Theorem (14.20)(c) and are already digitised in
`ErgodicGibbsLimits.lean`, under other names, exactly as that file's own module doc records:

* **(14.21)**, the averaged conditional density `ρ̃^n_Δ`, is the *definition*
  `Specification.shiftAvgCondDensity`, and the integral identity it names (the averaged kernel
  evaluations `|Λ'_n|⁻¹ ∑ γ_{Λ_n+i}(f | θ_i ω)` equal `∫ f dρ̃^n_Δ`) is
  `Specification.setLIntegral_prod_shiftAvgCondDensity` /
  `Specification.lintegral_shiftAvgCondDensity`.
* **(14.22)** is `Specification.toReal_shiftAvgCondDensity_ae_eq_condExp`, verbatim: `ρ̃^n_Δ` is
  the conditional expectation, given `𝓣_{Λ_n} × 𝓕_Δ`, of the ergodic average of `ρ̃_Δ`.
* **(14.23)–(14.24)**, combined, are `Specification.ae_tendsto_toReal_shiftAvgDensity_min` — but
  only for the **truncated** density `min ρ_Δ M`. Georgii's own argument for the *untruncated*
  statement applies the individual ergodic theorem (14.A8) directly to `ρ̃_Δ` under the invariant
  measure `ν̃ = μ ⊗ λ^Δ`; this needs only `ρ̃_Δ ∈ L¹(ν̃)`, not boundedness, and `ρ̃_Δ` is integrable
  because its conditional integral against a fixed inner configuration `ζ` is exactly `ρ̄_Δ(ζ)`,
  finite for `λ^Δ`-a.e. `ζ` since `∫ ρ̄_Δ dλ^Δ = 1`. The truncation in `ErgodicGibbsLimits.lean` is
  needed only for the *subsequent* step — combining (14.22) with (14.23)–(14.24) through Lemma
  (14.19) along the **decreasing** filtration `𝓣_{Λ_n} × 𝓕_Δ`, which does need a uniform
  dominating bound and genuinely fails for a general `ρ_Δ ∉ L log L`. That later step is not
  reproved here. What *is* missing, and is added below, is the honest, untruncated (14.23)–(14.24)
  themselves:

* `MeasureTheory.GibbsMeasure.ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn_of_integrable`:
  the individual ergodic theorem (14.A8) for an ergodic shift-invariant field, for a merely
  **integrable** (not bounded) function — the bounded case already in `ErgodicGibbsLimits.lean`
  specialised from this.
* `Specification.ae_tendsto_toReal_shiftAvgDensity`: (14.23)–(14.24) verbatim, for any Følner
  sequence `G` along which the average is taken directly (matching Georgii's own use of `Λ'_n` as
  the averaging sequence, rather than the two-step "average over `F n`, then transfer to the
  covering indices" route that forces truncation in the `_min` lemma).

## (14.13): a Comment, not a theorem — proved only in part

Georgii's Comment, for `E` a compact metric space: (i) `𝒫_Θ(Ω,𝓕)` is compact metrizable in the
*weak* topology; (ii) since the weak topology is coarser than the `𝓛`-topology (Remark (4.3)(3)),
Theorem (14.12) implies `ex 𝒫_Θ(Ω,𝓕)` is *weakly* dense; (iii) it is moreover a dense `G_δ`, i.e.
`𝒫_Θ(Ω,𝓕) ∖ ex 𝒫_Θ(Ω,𝓕)` is meager (a Poulsen simplex).

What is proved below is exactly (ii), at Georgii's own hypothesis (`E` compact metric): the
identity map `WithLocalConvergence S E → ProbabilityMeasure (S → E)` (`𝓛`-topology to Mathlib's
ambient weak topology on `ProbabilityMeasure`) is continuous — the compact-`E` case of Remark
(4.3)(3), proved via Georgii (2.21)(2) (`mem_quasilocalFunctions_of_uniformContinuous`) together
with Heine–Cantor (on a compact space every continuous function is uniformly continuous) — and the
resulting weak-density statement, transported along Theorem (14.12)'s closure identity.

(i) and (iii) are **not proved**. Precisely:

* (i) needs `ProbabilityMeasure (S → E)` bundled as a *metric* space in the weak topology
  (`MeasureTheory.LevyProkhorov`, `.instMetricSpaceProbabilityMeasure`, and the homeomorphism
  `ProbabilityMeasure Ω ≃ₜ LevyProkhorov (ProbabilityMeasure Ω)` in
  `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric`) together with compactness
  (`instCompactSpaceProbabilityMeasure` in `Mathlib.MeasureTheory.Measure.Prokhorov`), and then
  transferring both to the *subset* `𝒫_Θ` (as a subtype of `ProbabilityMeasure (S → E)`, cut out
  by shift-invariance, itself weakly closed).
* (iii) needs, on top of (i): the elementary convexity fact that a point of a convex set fails to
  be extreme iff it is the *midpoint* of two distinct points of the set (not merely a non-trivial
  convex combination at some other ratio) — used to identify `𝒫_Θ ∖ ex 𝒫_Θ` with Georgii's
  countable union `⋃ₙ Kₙ` of compact sets — and then the Baire category theorem for the resulting
  compact metric space.

None of this is in the codebase (`Topology/`, `Specification/`) under any name; building it is a
self-contained topology project (general convexity + Prokhorov/Lévy–Prokhorov bookkeeping +
Baire category), not a corollary of the ergodic-theory results proved elsewhere in Chapter 14, and
is left undone here rather than hand-waved.

## (14.16): an Example, not proved — needs a `Model/` instance

Georgii's Example is the one-dimensional Ising antiferromagnet at zero temperature: `S = ℤ`,
`E = {-1,1}`, `γ` the shift-invariant `λ`-specification (`λ` = counting measure) built from
`p_j(x,y) = 1` if `x ≠ y`, else `0` — the degenerate zero-temperature limit of Example (10.3). Its
content is that the two alternating-configuration Dirac masses `δ_{+-}, δ_{-+}` are extreme in
`𝒢(γ)` while their average is extreme in `𝒢_Θ(γ)`, exhibiting
`ex 𝒢_Θ(γ) ∖ ex 𝒢(γ) ≠ ∅` (so `𝒢_Θ(γ)` is *not* a face of `𝒢(γ)`, unlike the general fact
`Theorem (14.15)(c)` that it *is* a face of `𝒫_Θ(Ω,𝓕)`).

This is **not proved**: it requires constructing a concrete specification (Example (10.3)'s
degenerate kernel, at a state space `{-1,1}`, is a genuine `Model/`-level object, not a
specification-level generality) and is out of place in `Specification/`. Per the project's layout,
the honest home for it is a new `GibbsMeasure/Model/` file (e.g. alongside `Model/Ising.lean`),
building: the degenerate `λ`-specification from `p_j`; its two ground states as Dirac measures;
their extremality in `𝒢(γ)`; and the extremality of their average in `𝒢_Θ(γ)` via Theorem
(14.15)(a) (already available as `MeasureTheory.GibbsMeasure.ergodicSMul_iff_mem_extremePoints_...`
in `ErgodicGibbs.lean`) applied to the mixing/ergodicity of the average under the shift by 1. None
of that construction is attempted here, per the brief's instruction not to touch `Model/`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal Topology symmDiff Pointwise BoundedContinuousFunction

/-!
## General lemmas

Both belong upstream of this file:

* `MeasureTheory.GibbsMeasure.ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn_of_integrable`
  generalises `ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn` in
  `GibbsMeasure/Specification/ErgodicGibbsLimits.lean`, section `ShiftErgodic`, from a bounded to
  a merely integrable function; the bounded lemma should be re-derived from it in place.
* `MeasureTheory.GibbsMeasure.boundedContinuousToLp` and
  `MeasureTheory.GibbsMeasure.continuous_toMeasure_withLocalConvergence` belong with
  `GibbsMeasure/Topology/LocalConvergence.lean` / `GibbsMeasure/Specification/LocalContinuity.lean`
  as the compact-`E` case of Georgii's Remark (4.3)(3).
-/

namespace MeasureTheory.GibbsMeasure

section ShiftErgodic

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [Countable S] [DecidableEq S]
  {μ : Measure (S → E)} {F : ℕ → Finset S} {C : ℝ≥0∞}

end ShiftErgodic

/-! ### Georgii Remark (4.3)(3), compact-`E` case: the `𝓛`-topology is finer than the weak
topology -/

section WeakTopology

variable {S E : Type*} [MeasurableSpace E]

/-- A bounded continuous real function on configuration space, bundled as an `lp ∞` element (the
ambient type for Georgii's `𝓛`, `𝓛̄`). -/
def boundedContinuousToLp [TopologicalSpace E] (f : (S → E) →ᵇ ℝ) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨⇑f, memℓp_infty ⟨‖f‖, by rintro _ ⟨x, rfl⟩; exact f.norm_coe_le_norm x⟩⟩

omit [MeasurableSpace E] in
@[simp] lemma coeFn_boundedContinuousToLp [TopologicalSpace E] (f : (S → E) →ᵇ ℝ) :
    ⇑(boundedContinuousToLp (S := S) f) = ⇑f := rfl

/-- **Georgii, Remark (4.3)(3), for `E` compact metric.** The identity map from configuration
space's probability measures with the topology of local convergence to the same measures with
Mathlib's ambient weak topology (`MeasureTheory.ProbabilityMeasure`) is continuous: the
`𝓛`-topology is finer than the weak topology. On a compact space every continuous function is
uniformly continuous (Heine–Cantor), so every bounded continuous observable is quasilocal by
Georgii (2.21)(2) (`mem_quasilocalFunctions_of_uniformContinuous`), hence has `𝓛`-continuous
integral (`lContinuous_of_mem_quasilocalFunctions`); Mathlib's weak topology on
`ProbabilityMeasure (S → E)` is exactly the coarsest topology making all such integrals
continuous (`ProbabilityMeasure.continuous_iff_forall_continuous_integral`). -/
theorem continuous_toMeasure_withLocalConvergence [MetricSpace E] [CompactSpace E]
    [SecondCountableTopology E] [BorelSpace E] [Countable S] :
    Continuous (fun μ : WithLocalConvergence S E ↦ (μ.toMeasure : ProbabilityMeasure (S → E))) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hmeas : Measurable (⇑f : (S → E) → ℝ) := f.continuous.measurable
  have hunif : UniformContinuous (⇑f : (S → E) → ℝ) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  have hql : boundedContinuousToLp (S := S) f ∈ quasilocalFunctions S E :=
    mem_quasilocalFunctions_of_uniformContinuous hmeas hunif
  have hLC := lContinuous_of_mem_quasilocalFunctions hql
  simpa only [LContinuous, coeFn_boundedContinuousToLp] using hLC

end WeakTopology

end MeasureTheory.GibbsMeasure

open MeasureTheory MeasureTheory.GibbsMeasure

/-! ### Georgii Comment (14.13), for `E` compact metric: `ex 𝒫_Θ(Ω,𝓕)` is weakly dense -/

section EquiCube

variable {E : Type*} [MeasurableSpace E] {d : ℕ} [NeZero d]

/-- **Georgii, Comment (14.13), first half, on `ℤ^d`.** For `E` a compact metric space (Borel
`𝓔`), the shift-invariant random fields `ex 𝒫_Θ(Ω,𝓕)` that are ergodic are weakly dense among the
shift-invariant random fields `𝒫_Θ(Ω,𝓕)`, i.e. every shift-invariant random field lies in the
**weak** closure of the ergodic ones. This is Theorem (14.12) — closure in the `𝓛`-topology,
`ErgodicDense.closure_setOf_mem_extremePoints_invariantFields_shiftGroup_int` — transported along
`continuous_toMeasure_withLocalConvergence` (Remark (4.3)(3), compact-`E` case): a continuous map
sends the closure of a set into the closure of its image, and `WithSetwiseTopology.toMeasure` is a
bijection `WithLocalConvergence (Fin d → ℤ) E ≃ ProbabilityMeasure ((Fin d → ℤ) → E)`, so the
image of `𝒫_Θ` (resp. its ergodic subset) under this bijection is exactly the corresponding subset
of `ProbabilityMeasure ((Fin d → ℤ) → E)`. -/
theorem invariantFields_subset_closure_extremePoints_probabilityMeasure_int
    [MetricSpace E] [CompactSpace E] [SecondCountableTopology E] [BorelSpace E] :
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E) |
        (μ : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)} ⊆
      closure {μ : ProbabilityMeasure ((Fin d → ℤ) → E) |
        (μ : Measure ((Fin d → ℤ) → E)) ∈
          (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞} := by
  set φ : WithLocalConvergence (Fin d → ℤ) E → ProbabilityMeasure ((Fin d → ℤ) → E) :=
    fun ν ↦ (ν.toMeasure : ProbabilityMeasure ((Fin d → ℤ) → E)) with hφ
  set P : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    {ν | (ν.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)}
    with hP
  set D : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    {ν | (ν.toMeasure : Measure ((Fin d → ℤ) → E)) ∈
      (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞} with hD
  have hPD : closure D = P :=
    closure_setOf_mem_extremePoints_invariantFields_shiftGroup_int (E := E) (d := d)
  have hcont : Continuous φ := continuous_toMeasure_withLocalConvergence
  have hsub : φ '' closure D ⊆ closure (φ '' D) := image_closure_subset_closure_image hcont
  rw [hPD] at hsub
  have hPφ : φ '' P = {μ : ProbabilityMeasure ((Fin d → ℤ) → E) |
      (μ : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E)} := by
    ext μ
    simp only [hφ, hP, mem_image, mem_ofPred_eq]
    exact ⟨fun ⟨ν, hν, hνμ⟩ ↦ hνμ ▸ hν,
      fun hμ ↦ ⟨WithSetwiseTopology.ofMeasure μ, hμ, rfl⟩⟩
  have hDφ : φ '' D = {μ : ProbabilityMeasure ((Fin d → ℤ) → E) |
      (μ : Measure ((Fin d → ℤ) → E)) ∈
        (invariantFields (shiftGroup (Fin d → ℤ) E)).extremePoints ℝ≥0∞} := by
    ext μ
    simp only [hφ, hD, mem_image, mem_ofPred_eq]
    exact ⟨fun ⟨ν, hν, hνμ⟩ ↦ hνμ ▸ hν,
      fun hμ ↦ ⟨WithSetwiseTopology.ofMeasure μ, hμ, rfl⟩⟩
  rwa [hPφ, hDφ] at hsub

end EquiCube

/-! ### Georgii (14.23)–(14.24), untruncated -/

namespace Specification

open MeasureTheory.GibbsMeasure

section UntruncatedDensity

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [Countable S] [DecidableEq S]
  {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
  {μ : Measure (S → E)} [IsProbabilityMeasure μ] {C : ℝ≥0∞}

/-- **Georgii (14.23)–(14.24), untruncated.** For `μ` an ergodic shift-invariant Gibbs measure for
the `ν`-modification `ρ`, any inner volume `Δ`, and any increasing regular Følner sequence `G`
(Georgii takes `G n = Λ'_n`, the covering indices of Theorem (14.20)(c)'s proof): `νp`-almost
everywhere, `|G n|⁻¹ ∑_{i ∈ G n} ρ̃_Δ ∘ θ̃_i → ρ̄_Δ`, where `νp = μ ⊗ λ^Δ`. This is the individual
ergodic theorem (14.A8) applied directly to `ρ̃_Δ(ω, ζ) = ρ_Δ(ζ (θ_i ω)_{S∖Δ})` under the
`(θ̃_i)`-invariant `νp`, at each fixed `ζ`: `ρ̃_Δ(·, ζ)` is `μ`-integrable for `λ^Δ`-a.e. `ζ`
because its `μ`-integral is `ρ̄_Δ(ζ)`, finite `λ^Δ`-a.e. since `∫ ρ̄_Δ dλ^Δ = 1`
(`lintegral_avgKernel`); the ergodic average then converges `μ`-a.s. to that integral by
`ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn_of_integrable`. No truncation of `ρ_Δ` is
needed: unlike the *subsequent* combination with Lemma (14.19) along the decreasing filtration
`𝓣_{Λ_n} × 𝓕_Δ` (`ae_tendsto_toReal_shiftAvgDensity_min`), this ergodic-theorem step alone never
needed a uniform dominating bound. -/
theorem ae_tendsto_toReal_shiftAvgDensity (hmod : (isssd ν).IsModifier ρ)
    (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    (hμinv : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ)
    (htriv : μ ∈ trivialOn (invariantEvents (shiftGroup S E)))
    {G : ℕ → Finset S} (hG : Monotone G) (hGne : (G 0).Nonempty)
    (hGFol : ∀ g : S, Tendsto (fun n ↦ (((g +ᵥ G n) ∆ G n).card : ℝ) / (G n).card) atTop (𝓝 0))
    (hGC : ∀ n, ((G n - G n + G n).card : ℝ≥0∞) ≤ C * (G n).card) (hC' : C ≠ ∞) (Δ : Finset S) :
    ∀ᵐ p ∂(μ.prod (Measure.pi fun _ : Δ ↦ ν)),
      Tendsto (fun n ↦ (shiftAvgDensity ρ Δ (G n) p).toReal) atTop
        (𝓝 ((avgKernel ρ μ Δ p.2).toReal)) := by
  have hfin : ∀ᵐ ζ ∂(Measure.pi fun _ : Δ ↦ ν), avgKernel ρ μ Δ ζ ≠ ∞ :=
    (ae_lt_top' (measurable_avgKernel μ (hmod.measurable Δ)).aemeasurable
      (by rw [lintegral_avgKernel hmod hμ Δ]; exact ENNReal.one_ne_top)).mono fun ζ hζ ↦ hζ.ne
  have hstep : ∀ᵐ ζ ∂(Measure.pi fun _ : Δ ↦ ν), ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      (shiftAvgDensity ρ Δ (G n) (ω, ζ)).toReal) atTop (𝓝 ((avgKernel ρ μ Δ ζ).toReal)) := by
    filter_upwards [hfin] with ζ hζ
    have hmζ : Measurable fun ω ↦ ρ Δ (juxt (Δ : Set S) ω ζ) :=
      (hmod.measurable Δ).comp (measurable_juxt_boundary ζ)
    have hae_fin : ∀ᵐ ω ∂μ, ρ Δ (juxt (Δ : Set S) ω ζ) < ∞ := ae_lt_top' hmζ.aemeasurable hζ
    have hall_fin : ∀ᵐ ω ∂μ, ∀ i : S, ρ Δ (juxt (Δ : Set S) ((shift E i).toFun ω) ζ) < ∞ :=
      ae_all_iff.2 fun i ↦ (hμinv i).quasiMeasurePreserving.ae hae_fin
    have hint : ∫ ω, (ρ Δ (juxt (Δ : Set S) ω ζ)).toReal ∂μ = (avgKernel ρ μ Δ ζ).toReal := by
      rw [integral_toReal hmζ.aemeasurable hae_fin]; rfl
    have hInteg : Integrable (fun ω ↦ (ρ Δ (juxt (Δ : Set S) ω ζ)).toReal) μ :=
      integrable_toReal_of_lintegral_ne_top hmζ.aemeasurable hζ
    have herg := ae_tendsto_inv_card_smul_sum_shift_of_mem_trivialOn_of_integrable
      hμinv htriv hG hGne hGFol hGC hC' hInteg
    rw [hint] at herg
    filter_upwards [herg, hall_fin] with ω hω hallω
    have heq : (fun n ↦ (shiftAvgDensity ρ Δ (G n) (ω, ζ)).toReal) = fun n ↦
        ((G n).card : ℝ)⁻¹ * ∑ i ∈ G n, (ρ Δ (juxt (Δ : Set S) ((shift E i).toFun ω) ζ)).toReal :=
      funext fun n ↦ by
        rw [shiftAvgDensity, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ENNReal.toReal_sum fun i _ ↦ (hallω i).ne]
    rw [heq]
    simpa [smul_eq_mul] using hω
  have hmeas : MeasurableSet {p : (S → E) × (Δ → E) | Tendsto (fun n ↦
      (shiftAvgDensity ρ Δ (G n) p).toReal) atTop (𝓝 ((avgKernel ρ μ Δ p.2).toReal))} :=
    measurableSet_tendsto_nhds
      (fun n ↦ (measurable_shiftAvgDensity (hmod.measurable Δ) _).ennreal_toReal)
      (((measurable_avgKernel μ (hmod.measurable Δ)).comp measurable_snd).ennreal_toReal)
  exact (Measure.ae_prod_iff_ae_ae hmeas).2 ((Measure.ae_ae_comm hmeas).2 hstep)

end UntruncatedDensity

end Specification

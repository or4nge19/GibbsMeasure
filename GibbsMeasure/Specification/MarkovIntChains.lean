/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.MarkovInt
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.DoobDynkin
public import GibbsMeasure.Specification.ExtremeDecomposition
public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence
public import GibbsMeasure.Mathlib.Probability.TailTriviality
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Georgii §10.2: Markov fields which are Markov chains

Sites `ℤ`, an arbitrary measurable state space `(E, 𝓔)`, a probability a priori measure `ν`
(Georgii's `λ ∈ 𝒫(E, 𝓔)`, which he assumes without loss by Remark (1.28)(3)), and a specification
`γ = ρλ` given by a *Markovian λ-modification* `ρ`: `γ_Λ(·|η) = ρ_Λ λ_Λ(·|η)` with `ρ_{]i,k[}`
`𝓕_{[i,k]}`-measurable (`Specification.IsMarkovianInt`, Definition (10.2)). The question of the
section is which `μ ∈ 𝒢(γ)` are Markov chains (Definition (10.4)).

## Missing Mathlib

The section opens with general facts, stated in Mathlib's namespaces and with no Georgii
vocabulary; their intended homes are recorded in the docstrings:

* `MeasureTheory.Measure.withDensity_bind`: `withDensity` commutes with the Giry `bind`
  (`Mathlib/MeasureTheory/Measure/WithDensity.lean`).
* `MeasureTheory.Measure.AbsolutelyContinuous.bind`: `μ ≪ ν → μ κ ≪ ν κ`
  (`Mathlib/MeasureTheory/Measure/GiryMonad.lean`).
* `MeasureTheory.toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq` and
  `MeasureTheory.setLIntegral_ofReal_of_ae_eq_condExp`: an `m`-measurable `ℝ≥0∞`-valued function
  with the same set integrals as `f` over all `m`-sets is (the real part of) `μ[f | m]`, and
  conversely a nonnegative real version of `μ[f | m]` has, after `ENNReal.ofReal`, the same set
  integrals as `f` (`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`).
* `Measurable.exists_eq_comp_of_comap`: the Doob–Dynkin lemma for `ℝ≥0∞`-valued functions —
  a function measurable for `m.comap f` factors measurably through `f`
  (`Mathlib/MeasureTheory/MeasurableSpace/Basic.lean`).
* `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_le`
  (`Mathlib/MeasureTheory/Function/AEEqOfLIntegral.lean`).

## The objects (10.12)–(10.18)

For a general site set `S` (namespace `Specification`):

* `Specification.marginalDensity ν ρ Λ j`: Georgii's `ρ^j_Λ = λ_{Λ∖{j}} ρ_Λ` **(10.12)**, the
  density of the `j`-th coordinate of `γ_Λ` after the other sites of `Λ` are integrated out.
* `Specification.IsGibbsMeasure.eq_withDensity_bind_isssd`: **(10.14)** in the form
  `μ = ρ_Λ · (μ λ_Λ)` for every finite `Λ` (Georgii states it for `Λ = {j}`; the general volume
  is the "local absolute continuity" the proof of (10.21) needs), with
  `Specification.absolutelyContinuous_bind_isssd_of_subset` propagating it to sub-volumes.
* `Specification.IsGibbsMeasure.measure_eq_setLIntegral_marginalDensity`: **(10.15)**,
  `μ = ρ^j_Λ · ν_j` on `𝓣_{Λ∖{j}}`, where `ν_j = μ λ_{{j}}` is (10.13).
* `Specification.IsGibbsMeasure.toReal_marginalDensity_ae_eq_condExp`: **(10.16)**,
  `ρ^j_Λ = ν_j(ρ_{{j}} | 𝓣_{Λ∖{j}})` `ν_j`-a.s.

On `ℤ` (namespace `MeasureTheory.GibbsMeasure.Markov`):

* `measurable_marginalDensity_Ioo`: `ρ^j_{]i,k[}` is `𝓕_{{i,j,k}}`-measurable for Markovian `ρ`.
* `IsGibbsMeasure.toReal_marginalDensity_ae_eq_condExp_Ioo`: **(10.17)**,
  `ρ^j_{]i,k[} = ν_j(ρ_{{j}} | 𝓕_{{i,j} ∪ [k,∞[})`.
* `IsGibbsMeasure.tendsto_toReal_marginalDensity`: **(10.18)**, the backward martingale
  `k ↦ ρ^j_{]i,k[}` converges `ν_j`-a.s. to `ν_j(ρ_{{j}} | ⋂_k 𝓕_{{i,j} ∪ [k,∞[})`, and
  `IsGibbsMeasure.condExp_iInf_ae_eq_condExp_iInf_compl`: this limit is also
  `ν_j(ρ_{{j}} | ⋂_k 𝓣_{]i,k[ ∖ {j}})`.

## Lemma (10.20), Theorem (10.21), Corollary (10.22)

* `exists_ae_eq_pair_of_forall_measure_eq_zero_or_one`: the analytic core of (10.21). If the right
  tail `⋂_k 𝓕_{[k,∞[}` is `μ`-trivial, then every `⋂_k 𝓕_{{j-1,j} ∪ [k,∞[}`-measurable function is,
  `μ λ_{{j-1,j}}`-a.s., a measurable function of the two coordinates `j - 1, j`. Fixing those two
  coordinates turns such a function into a right-tail measurable one, hence into a constant; the
  constant depends measurably on them by Fubini. `μ λ_{{j-1,j}}` (rather than Georgii's `ν_j`) is
  what makes the two coordinates independent of everything else; `ν_j ≪ μ λ_{{j-1,j}}` transports
  the conclusion back. `exists_measurableSet_pair_ae_eq_of_forall_measure_eq_zero_or_one` is the
  same statement for events — Georgii's remark `𝓕_Δ = ⋂_{k>j} 𝓕_{Δ ∪ [k,∞[}`, whose failure
  without local absolute continuity he attributes to von Weizsäcker (1983).
* `IsGibbsMeasure.exists_density_of_ae_eq`: the normalisation step of **Lemma (10.20)** —
  replacing `q_j` by `1` on the `ν_j`-null set where `λ(q_j(x,·)) ≠ 1` produces a genuine
  probability density with `p_j(σ_{j-1}, σ_j) = ν_j(ρ_{{j}} | 𝓕_{]-∞,j]})` `ν_j`-a.s.
* `IsGibbsMeasure.exists_isMarkovChain_of_forall_exists_ae_eq`: **Lemma (10.20)** — if for
  every `j` the limit `ρ^j_{]j-1,∞[}` is a measurable function `q_j(σ_{j-1}, σ_j)` of the two
  coordinates `j - 1, j` (`ν_j`-a.s.), then `μ` is a Markov chain for kernels
  `P_j(x, ·) = p_j(x, ·) λ` with measurable, normalised densities `p_j` (Georgii's (i)–(iii)).
  `IsGibbsMeasure.exists_isMarkovChain_of_forall_condExp_iInf_ae_eq` is the same statement from
  Georgii's literal hypothesis **(10.19)**, `ρ^j_{]j-1,∞[} = ν_j(ρ_{{j}} | 𝓕_{{j-1,j}})`, via the
  two-point Doob–Dynkin lemma `exists_eq_pair_of_measurable_cylinderEvents`.
* `exists_isMarkovChain_of_mem_extremePoints`: **Theorem (10.21)** — every extreme
  `μ ∈ ex 𝒢(γ)` is a Markov chain of that form. No `StandardBorelSpace` and no countability of
  `E` is needed: extreme Gibbs measures are tail-trivial (Theorem (7.7), already in the library),
  and the passage from the triviality of the right tail `⋂_k 𝓕_{[k,∞[}` to (10.19) is Georgii's
  "local absolute continuity" argument, `μ ≪ μ λ_{{j-1,j}}`.
* `exists_isMarkovChain_of_nonempty_G`: **Corollary (10.22)** — for a standard Borel `E`, a
  non-empty `𝒢(γ)` contains a Markov chain (via Theorem (7.26), which is where
  `StandardBorelSpace E` enters, and the only place in this file where it is used).

The remainder of §10.2 — the irreducibility condition (10.23), its examples (10.24), and the
homogeneous theorem (10.25) with its Proposition (10.26) — is not in this file.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ## Georgii (10.12)–(10.16): the marginal densities of a λ-modification -/

namespace Specification

variable {S E : Type*} [DecidableEq S] [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {ρ : Finset S → (S → E) → ℝ≥0∞} {γ : Specification S E} {μ : Measure (S → E)}

/-- **Georgii (10.12).** For a density family `ρ` and `j ∈ Λ`, the *marginal density*
`ρ^j_Λ = λ_{Λ∖{j}} ρ_Λ`: the density of the `j`-th coordinate under `γ_Λ = ρ_Λ λ_Λ` once the
other sites of `Λ` have been integrated out,
`γ_Λ(σ_j ∈ A | ω) = ∫_A λ(dx) ρ^j_Λ(x ω_{S∖{j}})`. -/
def marginalDensity (ν : Measure E) [IsProbabilityMeasure ν] (ρ : Finset S → (S → E) → ℝ≥0∞)
    (Λ : Finset S) (j : S) (ω : S → E) : ℝ≥0∞ :=
  ∫⁻ σ, ρ Λ σ ∂(isssd ν (Λ.erase j) ω)

lemma measurable_marginalDensity_compl {Λ : Finset S} (hρ : Measurable (ρ Λ)) (j : S) :
    Measurable[cylinderEvents ((Λ.erase j : Finset S) : Set S)ᶜ] (marginalDensity ν ρ Λ j) :=
  Measurable.lintegral_kernel (κ := isssd ν (Λ.erase j)) hρ

lemma measurable_marginalDensity {Λ : Finset S} (hρ : Measurable (ρ Λ)) (j : S) :
    Measurable (marginalDensity ν ρ Λ j) :=
  (measurable_marginalDensity_compl hρ j).mono cylinderEvents_le_pi le_rfl

omit [DecidableEq S] in
/-- The resampled measure `μ λ_Λ` agrees with `μ` on the events outside `Λ`. -/
lemma bind_isssd_apply_of_measurableSet_compl {Λ : Finset S} {D : Set (S → E)}
    (hD : MeasurableSet[cylinderEvents (Λ : Set S)ᶜ] D) : (μ.bind (isssd ν Λ)) D = μ D := by
  have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
  rw [Measure.bind_apply hD' (measurable_isssd_coe Λ).aemeasurable, ← lintegral_indicator_one hD']
  refine lintegral_congr fun η ↦ ?_
  rw [((isssd ν).isProper Λ).apply_eq_indicator_mul_univ cylinderEvents_le_pi hD, measure_univ,
    mul_one]

section IsGibbsMeasure

variable [IsProbabilityMeasure μ]
  (hγ : ∀ (Λ : Finset S) (η : S → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
  (hρ : ∀ Λ, Measurable (ρ Λ))
include hγ hρ

omit [DecidableEq S] in
/-- **Georgii (10.14)**, for an arbitrary finite volume: a Gibbs measure for `γ = ρλ` is
`μ = ρ_Λ · (μ λ_Λ)`, absolutely continuous with respect to its own resampling of `Λ`. -/
theorem IsGibbsMeasure.eq_withDensity_bind_isssd (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) :
    μ = (μ.bind (isssd ν Λ)).withDensity (ρ Λ) := by
  calc μ = μ.bind (γ Λ) := (isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ Λ).symm
    _ = μ.bind fun η ↦ (isssd ν Λ η).withDensity (ρ Λ) := by
        congr 1
        funext η
        exact hγ Λ η
    _ = (μ.bind (isssd ν Λ)).withDensity (ρ Λ) :=
        (Measure.withDensity_bind (measurable_isssd_coe Λ) (hρ Λ)).symm

omit [DecidableEq S] in
lemma IsGibbsMeasure.measure_eq_setLIntegral_bind_isssd (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S)
    {D : Set (S → E)} (hD : MeasurableSet D) :
    μ D = ∫⁻ ω in D, ρ Λ ω ∂(μ.bind (isssd ν Λ)) := by
  conv_lhs => rw [hμ.eq_withDensity_bind_isssd hγ hρ Λ]
  rw [withDensity_apply _ hD]

omit [DecidableEq S] in
lemma IsGibbsMeasure.lintegral_bind_isssd (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) :
    ∫⁻ ω, ρ Λ ω ∂(μ.bind (isssd ν Λ)) = 1 := by
  have := hμ.measure_eq_setLIntegral_bind_isssd hγ hρ Λ MeasurableSet.univ
  rwa [Measure.restrict_univ, measure_univ, eq_comm] at this

omit [DecidableEq S] in
/-- `μ` is absolutely continuous with respect to `μ λ_Λ`. -/
lemma IsGibbsMeasure.absolutelyContinuous_bind_isssd (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) :
    μ ≪ μ.bind (isssd ν Λ) := by
  conv_lhs => rw [hμ.eq_withDensity_bind_isssd hγ hρ Λ]
  exact withDensity_absolutelyContinuous _ _

/-- **Georgii (10.15).** For `j ∈ Λ`, `μ = ρ^j_Λ · ν_j` on the events `𝓣_{Λ∖{j}}` outside
`Λ ∖ {j}`, where `ν_j = μ λ_{{j}}` is the measure (10.13). -/
theorem IsGibbsMeasure.measure_eq_setLIntegral_marginalDensity (hμ : γ.IsGibbsMeasure μ)
    {Λ : Finset S} {j : S} (hj : j ∈ Λ) {D : Set (S → E)}
    (hD : MeasurableSet[cylinderEvents ((Λ.erase j : Finset S) : Set S)ᶜ] D) :
    μ D = ∫⁻ ω in D, marginalDensity ν ρ Λ j ω ∂(μ.bind (isssd ν {j})) := by
  have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
  have hΛ : Λ.erase j ∪ {j} = Λ := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hj]
  have hm : Measurable (marginalDensity ν ρ Λ j) := measurable_marginalDensity (hρ Λ) j
  calc μ D = ∫⁻ η, ∫⁻ σ, D.indicator (ρ Λ) σ ∂(isssd ν Λ η) ∂μ := by
        rw [hμ.measure_eq_setLIntegral_bind_isssd hγ hρ Λ hD', ← lintegral_indicator hD',
          Measure.lintegral_bind (measurable_isssd_coe Λ).aemeasurable
            ((hρ Λ).indicator hD').aemeasurable]
    _ = ∫⁻ η, ∫⁻ ω, ∫⁻ σ, D.indicator (ρ Λ) σ ∂(isssd ν (Λ.erase j) ω) ∂(isssd ν {j} η) ∂μ := by
        refine lintegral_congr fun η ↦ ?_
        have h' : isssd ν Λ η = (isssd ν {j} η).bind (isssd ν (Λ.erase j)) := by
          rw [isssd_bind_isssd, hΛ]
        rw [h', Measure.lintegral_bind (measurable_isssd_coe (Λ.erase j)).aemeasurable
          ((hρ Λ).indicator hD').aemeasurable]
    _ = ∫⁻ η, ∫⁻ ω, D.indicator (marginalDensity ν ρ Λ j) ω ∂(isssd ν {j} η) ∂μ := by
        refine lintegral_congr fun η ↦ lintegral_congr fun ω ↦ ?_
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω, marginalDensity]
          refine (isResampling_isssd ν).lintegral_congr ((hρ Λ).indicator hD') (hρ Λ)
            fun σ hσ ↦ ?_
          rw [indicator_of_mem ((mem_congr_of_measurableSet_cylinderEvents hD
            fun i hi ↦ hσ i hi).2 hω)]
        · rw [indicator_of_notMem hω]
          refine ((isResampling_isssd ν).lintegral_congr (G := fun _ ↦ 0)
            ((hρ Λ).indicator hD') measurable_const fun σ hσ ↦ ?_).trans lintegral_zero
          rw [indicator_of_notMem fun h ↦ hω ((mem_congr_of_measurableSet_cylinderEvents hD
            fun i hi ↦ hσ i hi).1 h)]
    _ = ∫⁻ ω in D, marginalDensity ν ρ Λ j ω ∂(μ.bind (isssd ν {j})) := by
        rw [← lintegral_indicator hD',
          Measure.lintegral_bind (measurable_isssd_coe {j}).aemeasurable
            (hm.indicator hD').aemeasurable]

lemma IsGibbsMeasure.lintegral_marginalDensity (hμ : γ.IsGibbsMeasure μ) {Λ : Finset S} {j : S}
    (hj : j ∈ Λ) : ∫⁻ ω, marginalDensity ν ρ Λ j ω ∂(μ.bind (isssd ν {j})) = 1 := by
  have := hμ.measure_eq_setLIntegral_marginalDensity hγ hρ hj MeasurableSet.univ
  rwa [Measure.restrict_univ, measure_univ, eq_comm] at this

/-- **Georgii (10.16).** For `j ∈ Λ`, `ρ^j_Λ = ν_j(ρ_{{j}} | 𝓣_{Λ∖{j}})` `ν_j`-almost surely. -/
theorem IsGibbsMeasure.toReal_marginalDensity_ae_eq_condExp (hμ : γ.IsGibbsMeasure μ)
    {Λ : Finset S} {j : S} (hj : j ∈ Λ) :
    (fun ω ↦ (marginalDensity ν ρ Λ j ω).toReal) =ᵐ[μ.bind (isssd ν {j})]
      (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        cylinderEvents ((Λ.erase j : Finset S) : Set S)ᶜ] := by
  refine toReal_ae_eq_condExp_toReal_of_forall_setLIntegral_eq cylinderEvents_le_pi
    (hρ {j}).aemeasurable (measurable_marginalDensity_compl (hρ Λ) j)
    (by rw [hμ.lintegral_bind_isssd hγ hρ {j}]; exact ENNReal.one_ne_top)
    (by rw [hμ.lintegral_marginalDensity hγ hρ hj]; exact ENNReal.one_ne_top) fun t ht ↦ ?_
  rw [← hμ.measure_eq_setLIntegral_marginalDensity hγ hρ hj ht,
    hμ.measure_eq_setLIntegral_bind_isssd hγ hρ {j} (cylinderEvents_le_pi _ ht)]

end IsGibbsMeasure

/-- Integrating against the resampled measure `μ λ_{{i}}`: resample the single coordinate `i`. -/
lemma lintegral_bind_isssd_singleton (i : S) {F : (S → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(μ.bind (isssd ν {i})) = ∫⁻ ω, ∫⁻ y, F (Function.update ω i y) ∂ν ∂μ := by
  rw [Measure.lintegral_bind (measurable_isssd_coe {i}).aemeasurable hF.aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [isssd_singleton_eq_map, lintegral_map hF (measurable_update ω)]

/-- Updating a coordinate outside `Δ` does not change membership in a `𝓕_Δ`-event. -/
lemma update_mem_iff_of_measurableSet_cylinderEvents {Δ : Set S} {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents Δ] B) {i : S} (hi : i ∉ Δ) (ω : S → E) (y : E) :
    Function.update ω i y ∈ B ↔ ω ∈ B :=
  mem_congr_of_measurableSet_cylinderEvents hB fun _ hk ↦
    Function.update_of_ne (ne_of_mem_of_not_mem hk hi) _ _

omit [DecidableEq S] in
/-- Resampling a smaller volume keeps us absolutely continuous with respect to the resampling of
a larger one, as soon as `μ` itself is (Georgii's "local absolute continuity", the case
`Λ = ∅` being (10.14)). -/
lemma absolutelyContinuous_bind_isssd_of_subset {Λ Δ : Finset S}
    (h : μ ≪ μ.bind (isssd ν Δ)) (hΛΔ : Λ ⊆ Δ) :
    μ.bind (isssd ν Λ) ≪ μ.bind (isssd ν Δ) := by
  classical
  have hbb : (μ.bind (isssd ν Δ)).bind (isssd ν Λ) = μ.bind (isssd ν Δ) := by
    rw [Measure.bind_bind (measurable_isssd_coe Δ).aemeasurable
      (measurable_isssd_coe Λ).aemeasurable]
    exact congrArg _ (funext fun η ↦ (isssd_bind_isssd Λ Δ η).trans
      (by rw [Finset.union_eq_right.2 hΛΔ]))
  have hac := h.bind (measurable_isssd_coe (S := S) (E := E) (ν := ν) Λ)
  rwa [hbb] at hac

end Specification

/-! ## Georgii (10.17)–(10.18): the backward martingale on `ℤ` -/

namespace MeasureTheory.GibbsMeasure.Markov

open Specification

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
  {ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞} {γ : Specification ℤ E} {μ : Measure (ℤ → E)}

/-- For a Markovian `ρ`, the marginal density `ρ^j_{]i,k[}` is `𝓕_{{i,j,k}}`-measurable
(Georgii, after (10.12)). -/
lemma measurable_marginalDensity_Ioo (hρ : ∀ Λ, Measurable (ρ Λ)) (hM : IsMarkovianInt ρ)
    {i j k : ℤ} (hij : i < j) (hjk : j < k) :
    Measurable[cylinderEvents ({i, j, k} : Set ℤ)] (marginalDensity ν ρ (Finset.Ioo i k) j) := by
  refine (measurable_marginalDensity (hρ _) j).cylinderEvents_of_dependsOn fun ω ω' h ↦ ?_
  refine lintegral_isssd_congr_of_dependsOn (hρ _) ((hM.dependsOn (by omega)).mono ?_) h
  intro x hx
  simp only [Finset.coe_Ioo, Finset.coe_erase, Set.mem_union, Set.mem_Ioo, Set.mem_sdiff,
    Set.mem_singleton_iff, Set.mem_insert_iff] at hx ⊢
  omega

/-- The σ-algebras `𝓕_{{i,j} ∪ [k,∞[}` decrease in `k`. -/
lemma antitone_cylinderEvents_pair_Ici (i j : ℤ) :
    Antitone fun n : ℕ ↦ cylinderEvents (X := fun _ : ℤ ↦ E) ({i, j} ∪ Set.Ici (j + 1 + n)) :=
  fun m n hmn ↦ cylinderEvents_mono
    (Set.union_subset_union_right _ (Set.Ici_subset_Ici.2 (by omega)))

/-- The σ-algebras `𝓣_{]i,k[ ∖ {j}}` decrease in `k`. -/
lemma antitone_cylinderEvents_compl_erase (i j : ℤ) :
    Antitone fun n : ℕ ↦ cylinderEvents (X := fun _ : ℤ ↦ E)
      (((Finset.Ioo i (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ :=
  fun m n hmn ↦ cylinderEvents_mono (Set.compl_subset_compl.2 fun x hx ↦ by
    simp only [Finset.coe_erase, Finset.coe_Ioo, Set.mem_sdiff, Set.mem_Ioo,
      Set.mem_singleton_iff] at hx ⊢
    omega)

lemma cylinderEvents_Iic_le_iInf (j : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j) ≤ ⨅ n : ℕ,
      cylinderEvents (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ :=
  le_iInf fun n ↦ cylinderEvents_mono fun x hx ↦ by
    simp only [Finset.coe_erase, Finset.coe_Ioo, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_Ioo,
      Set.mem_singleton_iff, Set.mem_Iic] at hx ⊢
    omega

lemma cylinderEvents_pair_le_iInf (j : ℤ) :
    cylinderEvents (X := fun _ : ℤ ↦ E) ({j - 1, j} : Set ℤ) ≤ ⨅ n : ℕ,
      cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n)) :=
  le_iInf fun _ ↦ cylinderEvents_mono Set.subset_union_left

/-! ### The right tail, and Georgii's "local absolute continuity" step

The passage from the triviality of the **right tail** `⋂_{k>j} 𝓕_{[k,∞[}` to Georgii's
condition (10.19) is the only genuinely new argument in the proof of Theorem (10.21). Georgii
performs it on `ν_j = μ λ_{{j}}`; we do it on `μ λ_{{j-1,j}}`, where the two coordinates
`j - 1`, `j` are *both* independent of everything else, and transport the conclusion back to
`ν_j` along `ν_j ≪ μ λ_{{j-1,j}}` (`absolutelyContinuous_bind_isssd_of_subset`). Georgii's
remark after the proof — that the identity `𝓕_{{j-1,j}} = ⋂_{k>j} 𝓕_{{j-1,j} ∪ [k,∞[}` needs
the local absolute continuity of `μ` with respect to `λ^S` and fails in general (von
Weizsäcker) — is exactly the role played here by that absolute continuity.
-/

/-- The right tail `⋂_{k} 𝓕_{[k,∞[}` is contained in the tail σ-algebra `𝓣`, hence trivial
under any tail-trivial measure. -/
lemma iInf_cylinderEvents_Ici_le_tailSigmaAlgebra (j : ℤ) :
    (⨅ n : ℕ, cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici (j + 1 + n)))
      ≤ tailSigmaAlgebra ℤ E := by
  refine le_iInf fun Λ ↦ ?_
  obtain ⟨b, hb⟩ := Λ.exists_le (α := ℤ)
  refine le_trans (iInf_le _ (b - j).toNat) (cylinderEvents_mono fun x hx ↦ ?_)
  simp only [Set.mem_Ici] at hx
  simp only [Set.mem_compl_iff, Finset.mem_coe]
  intro hxΛ
  have h1 := hb x hxΛ
  have h2 : b - j ≤ ((b - j).toNat : ℤ) := Int.self_le_toNat _
  omega

/-- **Georgii, the key step in the proof of Theorem (10.21).** If the right tail
`⋂_{k>j} 𝓕_{[k,∞[}` is `μ`-trivial, then every real function measurable for
`⋂_{k>j} 𝓕_{{j-1,j} ∪ [k,∞[}` agrees, after the two coordinates `j - 1`, `j` have been
resampled from `λ`, with a measurable function of those two coordinates.

The argument: fixing the two resampled values `x, y`, the function `ω ↦ f (x ω_{j-1}, y ω_j, …)`
depends only on the coordinates in `[k, ∞[` for *every* `k`, so it is right-tail measurable,
hence `μ`-a.s. constant; that constant is its `μ`-integral, which is jointly measurable in
`(x, y)` by Fubini. -/
theorem exists_ae_eq_pair_of_forall_measure_eq_zero_or_one {μ : Measure (ℤ → E)}
    [IsProbabilityMeasure μ] {j : ℤ}
    (htriv : ∀ A, MeasurableSet[⨅ n : ℕ,
        cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici (j + 1 + n))] A → μ A = 0 ∨ μ A = 1)
    {f : (ℤ → E) → ℝ}
    (hf : Measurable[⨅ n : ℕ, cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n))] f) :
    ∃ q : E → E → ℝ, Measurable (Function.uncurry q) ∧
      f =ᵐ[μ.bind (isssd ν ({j - 1, j} : Finset ℤ))] fun σ ↦ q (σ (j - 1)) (σ j) := by
  classical
  have hjj : j - 1 ≠ j := by omega
  set u : (ℤ → E) → E → E → (ℤ → E) :=
    fun ω x y ↦ Function.update (Function.update ω (j - 1) x) j y with hu_def
  have hu_left : ∀ (ω : ℤ → E) (x y : E), u ω x y (j - 1) = x := fun ω x y ↦ by
    simp [hu_def, hjj]
  have hu_right : ∀ (ω : ℤ → E) (x y : E), u ω x y j = y := fun ω x y ↦ by simp [hu_def]
  have hf' : Measurable f := hf.mono ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) le_rfl
  have humeas : Measurable fun p : (E × E) × (ℤ → E) ↦ u p.2 p.1.1 p.1.2 := by
    simp only [hu_def]; fun_prop
  set q : E → E → ℝ := fun x y ↦ ∫ ω, f (u ω x y) ∂μ with hq_def
  have hsm : StronglyMeasurable fun p : (E × E) × (ℤ → E) ↦ f (u p.2 p.1.1 p.1.2) :=
    (hf'.comp humeas).stronglyMeasurable
  have hq_meas : Measurable (Function.uncurry q) :=
    (StronglyMeasurable.integral_prod_right' (ν := μ) hsm).measurable
  refine ⟨q, hq_meas, ?_⟩
  -- Step 1: for fixed `x, y` the shifted function is right-tail measurable, hence a.s. constant.
  have hconst : ∀ x y : E, ∀ᵐ ω ∂μ, f (u ω x y) = q x y := by
    intro x y
    have hshift : Measurable fun ω : ℤ → E ↦ f (u ω x y) := by
      refine hf'.comp ?_
      simp only [hu_def]; fun_prop
    have hmeasT : Measurable[⨅ n : ℕ,
        cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici (j + 1 + n))] fun ω ↦ f (u ω x y) := by
      rw [measurable_iInf_iff_forall]
      intro n
      have hdep : DependsOn f ({j - 1, j} ∪ Set.Ici (j + 1 + n)) :=
        (hf.mono (iInf_le _ n) le_rfl).dependsOn_of_cylinderEvents
      refine hshift.cylinderEvents_of_dependsOn fun ω ω' hωω' ↦ hdep fun i hi ↦ ?_
      rcases hi with hi | hi
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl
        · rw [hu_left, hu_left]
        · rw [hu_right, hu_right]
      · simp only [Set.mem_Ici] at hi
        have hij : i ≠ j := by omega
        have hij' : i ≠ j - 1 := by omega
        simp only [hu_def, Function.update_of_ne hij, Function.update_of_ne hij']
        exact hωω' i (by simp only [Set.mem_Ici]; omega)
    obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one
      ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) htriv hmeasT
    have hqc : q x y = c := by
      simp only [hq_def]
      rw [integral_congr_ae hc, integral_const]
      simp
    rw [hqc]
    exact hc
  -- Step 2: integrate the exceptional set out over the two resampled coordinates.
  have hbind : μ.bind (isssd ν ({j - 1, j} : Finset ℤ))
      = (μ.bind (isssd ν ({j - 1} : Finset ℤ))).bind (isssd ν ({j} : Finset ℤ)) := by
    rw [Measure.bind_bind (measurable_isssd_coe _).aemeasurable
      (measurable_isssd_coe _).aemeasurable]
    have hset : ({j} ∪ {j - 1} : Finset ℤ) = {j - 1, j} := by
      rw [Finset.union_comm, Finset.singleton_union]
    exact congrArg _ (funext fun η ↦ by rw [isssd_bind_isssd, hset])
  set A : Set (ℤ → E) := {σ | f σ = q (σ (j - 1)) (σ j)}ᶜ with hA_def
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun hf'
      (hq_meas.comp ((measurable_pi_apply (j - 1)).prodMk (measurable_pi_apply j)))).compl
  have hF : Measurable (A.indicator (1 : (ℤ → E) → ℝ≥0∞)) := measurable_one.indicator hA
  have hG : Measurable fun ω : ℤ → E ↦
      ∫⁻ y, A.indicator (1 : (ℤ → E) → ℝ≥0∞) (Function.update ω j y) ∂ν :=
    Measurable.lintegral_prod_right' (ν := ν) (hF.comp measurable_update')
  have hjoint : Measurable fun p : (ℤ → E) × (E × E) ↦
      A.indicator (1 : (ℤ → E) → ℝ≥0∞) (u p.1 p.2.1 p.2.2) := by
    refine hF.comp ?_
    simp only [hu_def]; fun_prop
  have h1 : (μ.bind (isssd ν ({j - 1, j} : Finset ℤ))) A
      = ∫⁻ ω, ∫⁻ p : E × E, A.indicator 1 (u ω p.1 p.2) ∂(ν.prod ν) ∂μ := by
    rw [← lintegral_indicator_one hA, hbind, lintegral_bind_isssd_singleton (i := j) hF,
      lintegral_bind_isssd_singleton (i := j - 1) hG]
    refine lintegral_congr fun ω ↦ ?_
    rw [lintegral_prod (fun p : E × E ↦ A.indicator (1 : (ℤ → E) → ℝ≥0∞) (u ω p.1 p.2))
      (hjoint.comp (measurable_const.prodMk measurable_id)).aemeasurable]
  have h2 : ∀ p : E × E, ∫⁻ ω, A.indicator (1 : (ℤ → E) → ℝ≥0∞) (u ω p.1 p.2) ∂μ = 0 := by
    intro p
    have hm : Measurable fun ω : ℤ → E ↦ A.indicator (1 : (ℤ → E) → ℝ≥0∞) (u ω p.1 p.2) := by
      refine hF.comp ?_
      simp only [hu_def]; fun_prop
    rw [lintegral_eq_zero_iff hm]
    filter_upwards [hconst p.1 p.2] with ω hω
    have : u ω p.1 p.2 ∉ A := by
      simp only [hA_def, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, hu_left, hu_right]
      exact hω
    simp [Set.indicator_of_notMem this]
  have hzero : (μ.bind (isssd ν ({j - 1, j} : Finset ℤ))) A = 0 := by
    rw [h1, lintegral_lintegral_swap (μ := μ) (ν := ν.prod ν)
      (f := fun ω (p : E × E) ↦ A.indicator (1 : (ℤ → E) → ℝ≥0∞) (u ω p.1 p.2)) hjoint.aemeasurable]
    simp [h2]
  rw [Filter.EventuallyEq, ae_iff]
  exact hzero

/-- **Georgii's remark following Theorem (10.21)**, at the level of events: if the right tail
`⋂_{k>j} 𝓕_{[k,∞[}` is `μ`-trivial then `𝓕_{{j-1,j}} = ⋂_{k>j} 𝓕_{{j-1,j} ∪ [k,∞[}` modulo the
null sets of `μ λ_{{j-1,j}}`. (Georgii states it modulo `μ`-null sets; the local absolute
continuity `μ ≪ μ λ_{{j-1,j}}` of a Gibbs measure, (10.14), transports it there. Without such an
absolute continuity the statement is false in general — von Weizsäcker (1983).) -/
theorem exists_measurableSet_pair_ae_eq_of_forall_measure_eq_zero_or_one {μ : Measure (ℤ → E)}
    [IsProbabilityMeasure μ] {j : ℤ}
    (htriv : ∀ A, MeasurableSet[⨅ n : ℕ,
        cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici (j + 1 + n))] A → μ A = 0 ∨ μ A = 1)
    {A : Set (ℤ → E)}
    (hA : MeasurableSet[⨅ n : ℕ, cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n))] A) :
    ∃ B, MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) ({j - 1, j} : Set ℤ)] B ∧
      (μ.bind (isssd ν ({j - 1, j} : Finset ℤ))) (symmDiff A B) = 0 := by
  classical
  have hind : Measurable[⨅ n : ℕ, cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n))]
      (A.indicator (1 : (ℤ → E) → ℝ)) := measurable_const.indicator hA
  obtain ⟨q, hq_meas, hq_ae⟩ :=
    exists_ae_eq_pair_of_forall_measure_eq_zero_or_one (ν := ν) htriv hind
  have hqm : Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({j - 1, j} : Set ℤ)]
      fun σ : ℤ → E ↦ q (σ (j - 1)) (σ j) :=
    hq_meas.comp (f := fun σ : ℤ → E ↦ ((σ (j - 1), σ j) : E × E))
      ((measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simp)).prodMk
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simp)))
  refine ⟨{σ | (2 : ℝ)⁻¹ ≤ q (σ (j - 1)) (σ j)}, hqm measurableSet_Ici,
    measure_mono_null (fun σ hσ ↦ ?_) (ae_iff.1 hq_ae)⟩
  simp only [Set.mem_ofPred_eq]
  rcases Set.mem_symmDiff.1 hσ with ⟨hA1, hB1⟩ | ⟨hB1, hA1⟩
  · simp only [Set.mem_ofPred_eq, not_le] at hB1
    rw [Set.indicator_of_mem hA1]
    exact fun h ↦ absurd (h ▸ hB1) (by norm_num)
  · simp only [Set.mem_ofPred_eq] at hB1
    rw [Set.indicator_of_notMem hA1]
    exact fun h ↦ absurd (h ▸ hB1) (by norm_num)

section IsGibbsMeasure

variable [IsProbabilityMeasure μ]
  (hγ : ∀ (Λ : Finset ℤ) (η : ℤ → E), γ Λ η = (isssd ν Λ η).withDensity (ρ Λ))
  (hρ : ∀ Λ, Measurable (ρ Λ))
include hγ hρ

lemma IsGibbsMeasure.integrable_toReal_singleton (hμ : γ.IsGibbsMeasure μ) (j : ℤ) :
    Integrable (fun ω ↦ (ρ {j} ω).toReal) (μ.bind (isssd ν {j})) :=
  integrable_toReal_of_lintegral_ne_top (hρ _).aemeasurable
    (by rw [hμ.lintegral_bind_isssd hγ hρ]; exact ENNReal.one_ne_top)

variable (hM : IsMarkovianInt ρ)
include hM

/-- **Georgii (10.17).** For `i < j < k`, `ρ^j_{]i,k[} = ν_j(ρ_{{j}} | 𝓕_{{i,j} ∪ [k,∞[})`
`ν_j`-almost surely. -/
theorem IsGibbsMeasure.toReal_marginalDensity_ae_eq_condExp_Ioo (hμ : γ.IsGibbsMeasure μ)
    {i j k : ℤ} (hij : i < j) (hjk : j < k) :
    (fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i k) j ω).toReal) =ᵐ[μ.bind (isssd ν {j})]
      (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        cylinderEvents ({i, j} ∪ Set.Ici k)] := by
  have hjΛ : j ∈ Finset.Ioo i k := by simp only [Finset.mem_Ioo]; omega
  have hm₁₀ : cylinderEvents (X := fun _ : ℤ ↦ E) ({i, j} ∪ Set.Ici k) ≤
      cylinderEvents (((Finset.Ioo i k).erase j : Finset ℤ) : Set ℤ)ᶜ :=
    cylinderEvents_mono fun x hx ↦ by
      simp only [Finset.coe_erase, Finset.coe_Ioo, Set.mem_compl_iff, Set.mem_sdiff, Set.mem_Ioo,
        Set.mem_singleton_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_Ici] at hx ⊢
      omega
  have hg : StronglyMeasurable[cylinderEvents ({i, j} ∪ Set.Ici k)]
      fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i k) j ω).toReal :=
    ((measurable_marginalDensity_Ioo hρ hM hij hjk).mono (cylinderEvents_mono fun x hx ↦ by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ici] at hx ⊢
      omega) le_rfl).ennreal_toReal.stronglyMeasurable
  have hint : Integrable (fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i k) j ω).toReal)
      (μ.bind (isssd ν {j})) :=
    integrable_toReal_of_lintegral_ne_top (measurable_marginalDensity (hρ _) j).aemeasurable
      (by rw [hμ.lintegral_marginalDensity hγ hρ hjΛ]; exact ENNReal.one_ne_top)
  calc (fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i k) j ω).toReal)
      = (μ.bind (isssd ν {j}))[fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i k) j ω).toReal |
          cylinderEvents ({i, j} ∪ Set.Ici k)] :=
        (condExp_of_stronglyMeasurable cylinderEvents_le_pi hg hint).symm
    _ =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[(μ.bind (isssd ν {j}))[
          fun ω ↦ (ρ {j} ω).toReal |
            cylinderEvents (((Finset.Ioo i k).erase j : Finset ℤ) : Set ℤ)ᶜ]
          | cylinderEvents ({i, j} ∪ Set.Ici k)] :=
        condExp_congr_ae (hμ.toReal_marginalDensity_ae_eq_condExp hγ hρ hjΛ)
    _ =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents ({i, j} ∪ Set.Ici k)] :=
        condExp_condExp_of_le hm₁₀ cylinderEvents_le_pi

/-- **Georgii (10.18)**, first half: the backward martingale `k ↦ ρ^j_{]i,k[}` converges
`ν_j`-almost surely to `ν_j(ρ_{{j}} | ⋂_{k>j} 𝓕_{{i,j} ∪ [k,∞[})`. -/
theorem IsGibbsMeasure.tendsto_toReal_marginalDensity (hμ : γ.IsGibbsMeasure μ) {i j : ℤ}
    (hij : i < j) :
    ∀ᵐ ω ∂(μ.bind (isssd ν {j})), Tendsto
      (fun n : ℕ ↦ (marginalDensity ν ρ (Finset.Ioo i (j + 1 + n)) j ω).toReal) atTop
      (𝓝 ((μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        ⨅ n : ℕ, cylinderEvents ({i, j} ∪ Set.Ici (j + 1 + n))] ω)) := by
  have h17 : ∀ n : ℕ, (fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i (j + 1 + n)) j ω).toReal)
      =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        cylinderEvents ({i, j} ∪ Set.Ici (j + 1 + n))] :=
    fun n ↦ IsGibbsMeasure.toReal_marginalDensity_ae_eq_condExp_Ioo hγ hρ hM hμ hij (by omega)
  filter_upwards [ae_all_iff.2 h17,
    (IsGibbsMeasure.integrable_toReal_singleton hγ hρ hμ j).tendsto_ae_condExp_of_antitone
    (antitone_cylinderEvents_pair_Ici i j) fun _ ↦ cylinderEvents_le_pi] with ω h1 h2
  exact h2.congr fun n ↦ (h1 n).symm

omit hM in
/-- **Georgii (10.18)**, second half: the same backward martingale converges `ν_j`-almost surely
to `ν_j(ρ_{{j}} | ⋂_{k>j} 𝓣_{]i,k[ ∖ {j}})`. -/
theorem IsGibbsMeasure.tendsto_toReal_marginalDensity_compl (hμ : γ.IsGibbsMeasure μ) {i j : ℤ}
    (hij : i < j) :
    ∀ᵐ ω ∂(μ.bind (isssd ν {j})), Tendsto
      (fun n : ℕ ↦ (marginalDensity ν ρ (Finset.Ioo i (j + 1 + n)) j ω).toReal) atTop
      (𝓝 ((μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
        cylinderEvents (((Finset.Ioo i (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] ω)) := by
  have h16 : ∀ n : ℕ, (fun ω ↦ (marginalDensity ν ρ (Finset.Ioo i (j + 1 + n)) j ω).toReal)
      =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        cylinderEvents (((Finset.Ioo i (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] :=
    fun n ↦ hμ.toReal_marginalDensity_ae_eq_condExp hγ hρ (by simp only [Finset.mem_Ioo]; omega)
  filter_upwards [ae_all_iff.2 h16,
    (IsGibbsMeasure.integrable_toReal_singleton hγ hρ hμ j).tendsto_ae_condExp_of_antitone
    (antitone_cylinderEvents_compl_erase i j) fun _ ↦ cylinderEvents_le_pi] with ω h1 h2
  exact h2.congr fun n ↦ (h1 n).symm

/-- **Georgii (10.18)**: the two descriptions of the limit `ρ^j_{]i,∞[}` agree. -/
theorem IsGibbsMeasure.condExp_iInf_ae_eq_condExp_iInf_compl (hμ : γ.IsGibbsMeasure μ) {i j : ℤ}
    (hij : i < j) :
    (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        ⨅ n : ℕ, cylinderEvents ({i, j} ∪ Set.Ici (j + 1 + n))]
      =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
        cylinderEvents (((Finset.Ioo i (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] := by
  filter_upwards [IsGibbsMeasure.tendsto_toReal_marginalDensity hγ hρ hM hμ hij,
    IsGibbsMeasure.tendsto_toReal_marginalDensity_compl hγ hρ hμ hij] with ω h1 h2
  exact tendsto_nhds_unique h1 h2

/-! ### Georgii (10.20): normalising the limit density -/

omit hM in
/-- The first half of **Georgii's Lemma (10.20)**: if the limit density `ρ^j_{]j-1,∞[}` is
`ν_j`-a.s. a measurable function `q` of the two coordinates `j - 1, j`, then, after `q` has been
replaced by `1` on the (`ν_j`-null) set of `x` where `λ(q(x, ·)) ≠ 1`, one gets a genuine
probability density `p`:

* `∫ p(x, ·) dλ = 1` for **every** `x` — so `P_j(x, ·) = p(x, ·) λ` is a probability kernel,
  Georgii's (ii);
* `μ(D) = ∫_D p(σ_{j-1}, σ_j) dν_j` for every `D ∈ 𝓕_{]-∞,j]}` — the identity that drives the
  one-sided Markov property, Georgii's (iii);
* `p(σ_{j-1}, σ_j) = ν_j(ρ_{{j}} | 𝓕_{]-∞,j]})` `ν_j`-a.s. — Georgii's (i), in the sharper
  form he derives on the way. -/
theorem IsGibbsMeasure.exists_density_of_ae_eq (hμ : γ.IsGibbsMeasure μ) (j : ℤ)
    {q : E → E → ℝ} (hq_meas : Measurable (Function.uncurry q))
    (hq_ae : (fun ω ↦ q (ω (j - 1)) (ω j)) =ᵐ[μ.bind (isssd ν {j})]
      (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
        cylinderEvents (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ]) :
    ∃ p : E → E → ℝ≥0∞, Measurable (Function.uncurry p) ∧ (∀ x, ∫⁻ y, p x y ∂ν = 1) ∧
      (∀ D, MeasurableSet[cylinderEvents (Set.Iic j)] D →
        ∫⁻ ω in D, p (ω (j - 1)) (ω j) ∂(μ.bind (isssd ν {j})) = μ D) ∧
      (fun ω ↦ (p (ω (j - 1)) (ω j)).toReal) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | cylinderEvents (Set.Iic j)] := by
  classical
  have hIic_le_G : cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j) ≤ ⨅ n : ℕ,
      cylinderEvents (X := fun _ : ℤ ↦ E)
        (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ :=
    cylinderEvents_Iic_le_iInf j
  have hG_le : (⨅ n : ℕ, cylinderEvents (X := fun _ : ℤ ↦ E)
      (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ) ≤ MeasurableSpace.pi :=
    (iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi
  have hρ_int : ∫⁻ ω, ρ {j} ω ∂(μ.bind (isssd ν {j})) = 1 := hμ.lintegral_bind_isssd hγ hρ {j}
  have hρ_ne : ∫⁻ ω, ρ {j} ω ∂(μ.bind (isssd ν {j})) ≠ ⊤ := by rw [hρ_int]; exact ENNReal.one_ne_top
  -- `q` is nonnegative almost surely, being a version of a conditional expectation of `ρ ≥ 0`.
  have hq_nonneg : 0 ≤ᵐ[μ.bind (isssd ν {j})] fun ω ↦ q (ω (j - 1)) (ω j) := by
    filter_upwards [hq_ae, condExp_nonneg (μ := μ.bind (isssd ν {j}))
      (m := ⨅ n : ℕ, cylinderEvents (X := fun _ : ℤ ↦ E)
        (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ)
      (f := fun ω ↦ (ρ {j} ω).toReal) (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
      with ω h1 h2
    rw [h1]; exact h2
  set Q : E → ℝ≥0∞ := fun x ↦ ∫⁻ y, ENNReal.ofReal (q x y) ∂ν with hQ_def
  have hqr : Measurable fun z : E × E ↦ ENNReal.ofReal (q z.1 z.2) :=
    ENNReal.measurable_ofReal.comp hq_meas
  have hQ_meas : Measurable Q := Measurable.lintegral_prod_right' (ν := ν) hqr
  set p : E → E → ℝ≥0∞ := fun x y ↦ if Q x = 1 then ENNReal.ofReal (q x y) else 1 with hp_def
  have hp_meas : Measurable (Function.uncurry p) := by
    refine Measurable.ite ?_ hqr measurable_const
    exact (hQ_meas.comp measurable_fst) (measurableSet_singleton (1 : ℝ≥0∞))
  have hp_one : ∀ x, ∫⁻ y, p x y ∂ν = 1 := by
    intro x
    by_cases h : Q x = 1
    · have hy : ∀ y, p x y = ENNReal.ofReal (q x y) := fun y ↦ by simp [hp_def, h]
      simp only [hy]; exact h
    · have hy : ∀ y, p x y = 1 := fun y ↦ by simp [hp_def, h]
      simp [hy]
  -- Georgii's normalisation: `λ(q(σ_{j-1}, ·)) = 1` `ν_j`-almost surely.
  have hQ_ae : (fun ω ↦ Q (ω (j - 1))) =ᵐ[μ.bind (isssd ν {j})] fun _ ↦ (1 : ℝ≥0∞) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_le
      (m := cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iio j)) cylinderEvents_le_pi
      (hQ_meas.comp (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
        (show j - 1 ∈ Set.Iio j by simp))) measurable_const fun B hB ↦ ?_
    have hB' : MeasurableSet B := cylinderEvents_le_pi _ hB
    have hBG : MeasurableSet[⨅ n : ℕ, cylinderEvents (X := fun _ : ℤ ↦ E)
      (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] B :=
      hIic_le_G _ (cylinderEvents_mono Set.Iio_subset_Iic_self _ hB)
    have hBc : MeasurableSet[cylinderEvents ((({j} : Finset ℤ) : Set ℤ)ᶜ)] B :=
      cylinderEvents_mono (by
        intro x hx
        simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
        simp only [Set.mem_Iio] at hx
        omega) _ hB
    have hm1 : Measurable (Set.indicator B fun σ : ℤ → E ↦ Q (σ (j - 1))) :=
      (hQ_meas.comp (measurable_pi_apply (j - 1))).indicator hB'
    have hqj : Measurable fun σ : ℤ → E ↦ ENNReal.ofReal (q (σ (j - 1)) (σ j)) :=
      hqr.comp (f := fun σ : ℤ → E ↦ ((σ (j - 1), σ j) : E × E))
        ((measurable_pi_apply (j - 1)).prodMk (measurable_pi_apply j))
    have hm2 :
        Measurable (Set.indicator B fun σ : ℤ → E ↦ ENNReal.ofReal (q (σ (j - 1)) (σ j))) :=
      hqj.indicator hB'
    have step : ∫⁻ ω in B, Q (ω (j - 1)) ∂(μ.bind (isssd ν {j}))
        = ∫⁻ ω in B, ENNReal.ofReal (q (ω (j - 1)) (ω j)) ∂(μ.bind (isssd ν {j})) := by
      rw [← lintegral_indicator hB', ← lintegral_indicator hB',
        lintegral_bind_isssd_singleton (i := j) hm1,
        lintegral_bind_isssd_singleton (i := j) hm2]
      refine lintegral_congr fun ω ↦ ?_
      have hupd : ∀ y : E, (Function.update ω j y ∈ B ↔ ω ∈ B) := fun y ↦
        update_mem_iff_of_measurableSet_cylinderEvents hB (by simp) ω y
      by_cases hω : ω ∈ B
      · have h1 : ∀ y : E, Set.indicator B (fun σ : ℤ → E ↦ Q (σ (j - 1)))
            (Function.update ω j y) = Q (ω (j - 1)) := fun y ↦ by
          rw [Set.indicator_of_mem ((hupd y).2 hω), Function.update_of_ne (by omega : j - 1 ≠ j)]
        have h2 : ∀ y : E, Set.indicator B
            (fun σ : ℤ → E ↦ ENNReal.ofReal (q (σ (j - 1)) (σ j))) (Function.update ω j y)
              = ENNReal.ofReal (q (ω (j - 1)) y) := fun y ↦ by
          rw [Set.indicator_of_mem ((hupd y).2 hω), Function.update_of_ne (by omega : j - 1 ≠ j),
            Function.update_self]
        simp only [h1, h2]
        rw [lintegral_const, measure_univ, mul_one]
      · have h1 : ∀ y : E, Set.indicator B (fun σ : ℤ → E ↦ Q (σ (j - 1)))
            (Function.update ω j y) = 0 := fun y ↦
          Set.indicator_of_notMem (fun h ↦ hω ((hupd y).1 h)) _
        have h2 : ∀ y : E, Set.indicator B
            (fun σ : ℤ → E ↦ ENNReal.ofReal (q (σ (j - 1)) (σ j))) (Function.update ω j y)
              = 0 := fun y ↦ Set.indicator_of_notMem (fun h ↦ hω ((hupd y).1 h)) _
        simp only [h1, h2]
    rw [step, setLIntegral_ofReal_of_ae_eq_condExp hG_le (hρ {j}).aemeasurable hρ_ne
      hq_nonneg hq_ae hBG, ← hμ.measure_eq_setLIntegral_bind_isssd hγ hρ {j} hB',
      setLIntegral_one, bind_isssd_apply_of_measurableSet_compl hBc]
  have hp_ae : (fun ω ↦ p (ω (j - 1)) (ω j)) =ᵐ[μ.bind (isssd ν {j})]
      fun ω ↦ ENNReal.ofReal (q (ω (j - 1)) (ω j)) := by
    filter_upwards [hQ_ae] with ω hω
    simp [hp_def, hω]
  refine ⟨p, hp_meas, hp_one, fun D hD ↦ ?_, ?_⟩
  · have hD' : MeasurableSet D := cylinderEvents_le_pi _ hD
    rw [setLIntegral_congr_fun_ae hD' (hp_ae.mono fun ω hω _ ↦ hω),
      setLIntegral_ofReal_of_ae_eq_condExp hG_le (hρ {j}).aemeasurable hρ_ne hq_nonneg hq_ae
        (hIic_le_G _ hD), ← hμ.measure_eq_setLIntegral_bind_isssd hγ hρ {j} hD']
  · have hsm : StronglyMeasurable[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]
        fun ω ↦ q (ω (j - 1)) (ω j) :=
      (hq_meas.comp ((measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
        (show j - 1 ∈ Set.Iic j by simp)).prodMk
        (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
          (show j ∈ Set.Iic j by simp)))).stronglyMeasurable
    have hint : Integrable (fun ω ↦ q (ω (j - 1)) (ω j)) (μ.bind (isssd ν {j})) :=
      integrable_condExp.congr hq_ae.symm
    have hcalc : (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]
        =ᵐ[μ.bind (isssd ν {j})] fun ω ↦ q (ω (j - 1)) (ω j) := by
      calc (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
            cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]
          =ᵐ[μ.bind (isssd ν {j})]
            (μ.bind (isssd ν {j}))[(μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
            ⨅ n : ℕ, cylinderEvents (X := fun _ : ℤ ↦ E)
            (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ] |
            cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)] :=
            (condExp_condExp_of_le hIic_le_G hG_le).symm
        _ =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ q (ω (j - 1)) (ω j) |
            cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)] := condExp_congr_ae hq_ae.symm
        _ =ᵐ[μ.bind (isssd ν {j})] fun ω ↦ q (ω (j - 1)) (ω j) := by
            rw [condExp_of_stronglyMeasurable cylinderEvents_le_pi hsm hint]
    filter_upwards [hp_ae, hq_nonneg, hcalc] with ω h1 h2 h3
    rw [h1, ENNReal.toReal_ofReal h2, h3]


omit hM in
/-- **Georgii, Lemma (10.20).** Let `ρ` be a `λ`-modification, `μ ∈ 𝒢(ρλ)`, and suppose that for
every `j` the limit density `ρ^j_{]j-1,∞[} = ν_j(ρ_{{j}} | ⋂_{k>j} 𝓣_{]j-1,k[∖{j}})` is
`ν_j`-a.s. a measurable function `q_j(σ_{j-1}, σ_j)` of the two coordinates `j - 1, j` — this is
Georgii's hypothesis (10.19), see `exists_isMarkovChain_of_forall_condExp_iInf_ae_eq`. Then there
is a family `p_j : E × E → [0, ∞]` of measurable functions with

* `∫ p_j(x, ·) dλ = 1` for every `x`, so `P_j(x, ·) = p_j(x, ·) λ` is a probability kernel
  (Georgii's (ii));
* `p_j(σ_{j-1}, σ_j) = ν_j(ρ_{{j}} | 𝓕_{]-∞,j]})` `ν_j`-a.s. (Georgii's (i), in the sharper form
  he derives on the way — the version with `𝓕_{{j-1,j}}` follows by the tower property);
* `μ` is a Markov chain for `(P_j)_{j ∈ ℤ}` (Georgii's (iii)). -/
theorem IsGibbsMeasure.exists_isMarkovChain_of_forall_exists_ae_eq (hμ : γ.IsGibbsMeasure μ)
    (hq : ∀ j : ℤ, ∃ q : E → E → ℝ, Measurable (Function.uncurry q) ∧
      (fun ω ↦ q (ω (j - 1)) (ω j)) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
          cylinderEvents (X := fun _ : ℤ ↦ E)
            (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ]) :
    ∃ (p : ℤ → E → E → ℝ≥0∞) (P : ℤ → Kernel E E),
      (∀ j, Measurable (Function.uncurry (p j))) ∧
      (∀ j x, P j x = ν.withDensity (p j x)) ∧
      (∀ j, IsMarkovKernel (P j)) ∧
      (∀ j, (fun ω ↦ (p j (ω (j - 1)) (ω j)).toReal) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]) ∧
      IsMarkovChain P μ := by
  classical
  choose q hq_meas hq_ae using hq
  choose p hp_meas hp_one hp_int hp_cond using fun j ↦
    IsGibbsMeasure.exists_density_of_ae_eq hγ hρ hμ j (hq_meas j) (hq_ae j)
  have hPapply : ∀ (j : ℤ) (x : E),
      ((Kernel.const E ν).withDensity (p j)) x = ν.withDensity (p j x) := fun j x ↦ by
    rw [Kernel.withDensity_apply _ (hp_meas j), Kernel.const_apply]
  have hPmarkov : ∀ j, IsMarkovKernel ((Kernel.const E ν).withDensity (p j)) := fun j ↦
    ⟨fun x ↦ ⟨by
      rw [hPapply j x, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        hp_one j x]⟩⟩
  refine ⟨p, fun j ↦ (Kernel.const E ν).withDensity (p j), hp_meas, hPapply, hPmarkov,
    hp_cond, ?_⟩
  have _ : ∀ k, IsMarkovKernel ((Kernel.const E ν).withDensity (p k)) := hPmarkov
  rw [isMarkovChain_iff_forall_measure_inter]
  intro i A hA t ht
  have hpi : Measurable fun σ : ℤ → E ↦ p i (σ (i - 1)) (σ i) :=
    (hp_meas i).comp (f := fun σ : ℤ → E ↦ ((σ (i - 1), σ i) : E × E))
      ((measurable_pi_apply (i - 1)).prodMk (measurable_pi_apply i))
  have ht' : MeasurableSet t := cylinderEvents_le_pi _ ht
  have hD : MeasurableSet[cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic i)]
      ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ t) :=
    MeasurableSet.inter
      ((measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (show i ∈ Set.Iic i by simp)) hA)
      (cylinderEvents_mono Set.Iio_subset_Iic_self _ ht)
  have hD' : MeasurableSet ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ t) := cylinderEvents_le_pi _ hD
  have hPA : ∀ x : E, ((Kernel.const E ν).withDensity (p i)) x A = ∫⁻ y in A, p i x y ∂ν :=
    fun x ↦ by rw [hPapply i x, withDensity_apply _ hA]
  simp only [hPA]
  rw [← hp_int i _ hD, ← lintegral_indicator hD',
    lintegral_bind_isssd_singleton (i := i) (hpi.indicator hD'), ← lintegral_indicator ht']
  refine lintegral_congr fun ω ↦ ?_
  have hmem : ∀ y : E, (Function.update ω i y ∈ (fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ t)
      ↔ (y ∈ A ∧ ω ∈ t) := fun y ↦ by
    rw [Set.mem_inter_iff, Set.mem_preimage, Function.update_self,
      update_mem_iff_of_measurableSet_cylinderEvents ht (by simp) ω y]
  by_cases hω : ω ∈ t
  · rw [Set.indicator_of_mem hω, ← lintegral_indicator hA]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem ((hmem y).2 ⟨hy, hω⟩), Set.indicator_of_mem hy,
        Function.update_of_ne (by omega : i - 1 ≠ i), Function.update_self]
    · rw [Set.indicator_of_notMem (fun h ↦ hy ((hmem y).1 h).1),
        Set.indicator_of_notMem hy]
  · have : ∀ y : E, Set.indicator ((fun σ : ℤ → E ↦ σ i) ⁻¹' A ∩ t)
        (fun σ : ℤ → E ↦ p i (σ (i - 1)) (σ i)) (Function.update ω i y) = 0 := fun y ↦
      Set.indicator_of_notMem (fun h ↦ hω ((hmem y).1 h).2) _
    simp only [this, Set.indicator_of_notMem hω, lintegral_zero]


omit hγ hρ hM in
/-- **Doob–Dynkin for a two-point cylinder σ-algebra.** A real function measurable for
`𝓕_{{a,b}}` is a measurable function of the two coordinates `a`, `b`. -/
lemma exists_eq_pair_of_measurable_cylinderEvents {a b : ℤ} (hab : a ≠ b)
    {g : (ℤ → E) → ℝ} (hg : Measurable[cylinderEvents (X := fun _ : ℤ ↦ E) ({a, b} : Set ℤ)] g) :
    ∃ q : E → E → ℝ, Measurable (Function.uncurry q) ∧ ∀ σ, g σ = q (σ a) (σ b) := by
  classical
  by_cases hne : Nonempty (ℤ → E)
  · obtain ⟨ω₀⟩ := hne
    have hdep : DependsOn g ({a, b} : Set ℤ) := hg.dependsOn_of_cylinderEvents
    have hg' : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
    refine ⟨fun x y ↦ g (Function.update (Function.update ω₀ a x) b y), ?_, fun σ ↦ ?_⟩
    · exact hg'.comp (f := fun z : E × E ↦ Function.update (Function.update ω₀ a z.1) b z.2)
        (by fun_prop)
    · refine hdep fun i hi ↦ ?_
      rcases hi with hi | hi
      · subst hi
        rw [Function.update_of_ne hab, Function.update_self]
      · simp only [Set.mem_singleton_iff] at hi
        subst hi
        rw [Function.update_self]
  · rw [not_nonempty_iff] at hne
    exact ⟨fun _ _ ↦ 0, measurable_const, fun σ ↦ isEmptyElim σ⟩

omit hM in
/-- **Georgii, Lemma (10.20)** from his literal hypothesis **(10.19)**: if for every `j` the limit
density `ρ^j_{]j-1,∞[}` equals `ν_j(ρ_{{j}} | 𝓕_{{j-1,j}})` `ν_j`-almost surely, then `μ` is a
Markov chain for kernels with densities. -/
theorem IsGibbsMeasure.exists_isMarkovChain_of_forall_condExp_iInf_ae_eq
    (hμ : γ.IsGibbsMeasure μ)
    (h19 : ∀ j : ℤ, (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal | ⨅ n : ℕ,
          cylinderEvents (X := fun _ : ℤ ↦ E)
            (((Finset.Ioo (j - 1) (j + 1 + n)).erase j : Finset ℤ) : Set ℤ)ᶜ]
        =ᵐ[μ.bind (isssd ν {j})] (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents (X := fun _ : ℤ ↦ E) ({j - 1, j} : Set ℤ)]) :
    ∃ (p : ℤ → E → E → ℝ≥0∞) (P : ℤ → Kernel E E),
      (∀ j, Measurable (Function.uncurry (p j))) ∧
      (∀ j x, P j x = ν.withDensity (p j x)) ∧
      (∀ j, IsMarkovKernel (P j)) ∧
      (∀ j, (fun ω ↦ (p j (ω (j - 1)) (ω j)).toReal) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]) ∧
      IsMarkovChain P μ := by
  refine IsGibbsMeasure.exists_isMarkovChain_of_forall_exists_ae_eq hγ hρ hμ fun j ↦ ?_
  obtain ⟨q, hq_meas, hq_eq⟩ := exists_eq_pair_of_measurable_cylinderEvents
    (a := j - 1) (b := j) (by omega) (stronglyMeasurable_condExp (m := cylinderEvents
      (X := fun _ : ℤ ↦ E) ({j - 1, j} : Set ℤ))
      (μ := μ.bind (isssd ν {j})) (f := fun ω ↦ (ρ {j} ω).toReal)).measurable
  exact ⟨q, hq_meas, by
    filter_upwards [h19 j] with ω hω
    rw [← hq_eq ω, ← hω]⟩

/-! ### Georgii (10.21) and (10.22) -/

/-- **Georgii, Theorem (10.21).** Every extreme Gibbs measure `μ ∈ ex 𝒢(γ)` of a Markovian
`λ`-modification `ρ`, `γ = ρλ`, is a Markov chain for transition kernels `P_j(x, ·) = p_j(x, ·) λ`
with measurable densities `p_j`, and `p_j(σ_{j-1}, σ_j) = ν_j(ρ_{{j}} | 𝓕_{]-∞,j]})` `ν_j`-a.s.

Neither `StandardBorelSpace E` nor countability of `E` is needed: the only input beyond
(10.12)–(10.20) is that extreme Gibbs measures are tail-trivial (Theorem (7.7)(a),
`tailTrivial_of_mem_extremePoints_G`), applied to the right tail `⋂_k 𝓕_{[k,∞[}`. -/
theorem exists_isMarkovChain_of_mem_extremePoints
    (hμ : μ ∈ (GibbsMeasure.G (γ := γ)).extremePoints ℝ≥0∞) :
    ∃ (p : ℤ → E → E → ℝ≥0∞) (P : ℤ → Kernel E E),
      (∀ j, Measurable (Function.uncurry (p j))) ∧
      (∀ j x, P j x = ν.withDensity (p j x)) ∧
      (∀ j, IsMarkovKernel (P j)) ∧
      (∀ j, (fun ω ↦ (p j (ω (j - 1)) (ω j)).toReal) =ᵐ[μ.bind (isssd ν {j})]
        (μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
          cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Iic j)]) ∧
      IsMarkovChain P μ := by
  have hμG : γ.IsGibbsMeasure μ := hμ.1.2
  refine IsGibbsMeasure.exists_isMarkovChain_of_forall_exists_ae_eq hγ hρ hμG fun j ↦ ?_
  -- the right tail is `μ`-trivial, by Theorem (7.7)(a)
  have htriv : ∀ A, MeasurableSet[⨅ n : ℕ,
      cylinderEvents (X := fun _ : ℤ ↦ E) (Set.Ici (j + 1 + n))] A → μ A = 0 ∨ μ A = 1 :=
    fun A hA ↦ GibbsMeasure.tailTrivial_of_mem_extremePoints_G (γ := γ) hμ A
      (iInf_cylinderEvents_Ici_le_tailSigmaAlgebra j _ hA)
  -- the limit of (10.18) is measurable for `⋂_k 𝓕_{{j-1,j} ∪ [k,∞[}`
  have hmeas : Measurable[⨅ n : ℕ, cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n))]
      ((μ.bind (isssd ν {j}))[fun ω ↦ (ρ {j} ω).toReal |
        ⨅ n : ℕ, cylinderEvents ({j - 1, j} ∪ Set.Ici (j + 1 + n))]) :=
    stronglyMeasurable_condExp.measurable
  obtain ⟨q, hq_meas, hq_ae⟩ :=
    exists_ae_eq_pair_of_forall_measure_eq_zero_or_one (ν := ν) htriv hmeas
  -- transport from `μ λ_{{j-1,j}}` to `ν_j` along `ν_j ≪ μ λ_{{j-1,j}}`
  have hac : μ.bind (isssd ν ({j} : Finset ℤ)) ≪ μ.bind (isssd ν ({j - 1, j} : Finset ℤ)) :=
    Specification.absolutelyContinuous_bind_isssd_of_subset
      (hμG.absolutelyContinuous_bind_isssd hγ hρ ({j - 1, j} : Finset ℤ))
      (by intro x hx; simp only [Finset.mem_singleton] at hx; simp [hx])
  refine ⟨q, hq_meas, ?_⟩
  filter_upwards [hac hq_ae.symm,
    IsGibbsMeasure.condExp_iInf_ae_eq_condExp_iInf_compl hγ hρ hM hμG
      (show j - 1 < j by omega)] with ω h1 h2
  rw [h1, h2]

/-- **Georgii, Corollary (10.22).** If `E` is standard Borel and `𝒢(γ)` is non-empty, then
`𝒢(γ)` contains a Markov chain: combine Theorem (7.26) (`nonempty_extremePoints_G`) with
Theorem (10.21). This is the only place in §10.2 where `StandardBorelSpace E` is used. -/
theorem exists_isMarkovChain_of_nonempty_G [StandardBorelSpace E]
    (hG : (GibbsMeasure.G (γ := γ)).Nonempty) :
    ∃ μ' ∈ GibbsMeasure.G (γ := γ), ∃ (p : ℤ → E → E → ℝ≥0∞) (P : ℤ → Kernel E E),
      (∀ j, Measurable (Function.uncurry (p j))) ∧
      (∀ j x, P j x = ν.withDensity (p j x)) ∧
      (∀ j, IsMarkovKernel (P j)) ∧
      IsMarkovChain P μ' := by
  obtain ⟨μ', hμ'⟩ := GibbsMeasure.nonempty_extremePoints_G (γ := γ) hG
  have : IsProbabilityMeasure μ' := hμ'.1.1
  obtain ⟨p, P, h1, h2, h3, -, h5⟩ :=
    exists_isMarkovChain_of_mem_extremePoints (μ := μ') hγ hρ hM hμ'
  exact ⟨μ', hμ'.1, p, P, h1, h2, h3, h5⟩

end IsGibbsMeasure

end MeasureTheory.GibbsMeasure.Markov


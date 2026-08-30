/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Average

/-!
# Existence of invariant Gibbs measures

Georgii Theorem (5.19), the counterpart to the general existence theorem (4.22): for a quasilocal
specification `γ` and a set `I` of transformations, the averages
`μ_α = |𝓡_α|⁻¹ ∑_{Λ ∈ 𝓡_α} ν_α γ^α_Λ` of an `I`-invariant approximating net `γ^α → γ` over
asymptotically `I`-invariant volume families `𝓡_α` with `⋂ 𝓡_α ↑ S` have a cluster point in
`𝒢_I(γ)`, provided they are locally equicontinuous.

The proof is Georgii's assembly of three earlier results:

* Proposition (4.9) (`exists_mapClusterPt_of_locallyEquicontinuous`) produces the cluster point;
* Theorem (4.17) (`mem_GP_of_mapClusterPt`) puts it in `𝒢(γ)`, using `μ_α γ^α_Λ = μ_α` for
  `Λ ⊆ ⋂ 𝓡_α` (`Specification.bind_average_of_subset`);
* Proposition (5.18) (`Specification.map_average`,
  `Specification.abs_average_real_sub_le_of_card_eq`) makes it `I`-invariant.

Since (5.19) lets `γ^α` and `ν_α` vary with `α` along an arbitrary net, the assembly uses a net
form `measurePreserving_of_mapClusterPt_average_net` of (5.18); it specialises to
`measurePreserving_of_mapClusterPt_average` of `GibbsMeasure/Specification/Average.lean` and is
proved from the same two estimates.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E ι : Type*} [MeasurableSpace E] {l : Filter ι}

/-! ### Georgii Proposition (5.18), net form -/

section Net

variable [DecidableEq S]

/-- **Georgii Proposition (5.18)**, for a net indexed by an arbitrary filter and with varying
specifications and boundary conditions: if `γ^α` and `ν_α` are `τ`-invariant and
`|τ_* 𝓡_α ∆ 𝓡_α| / |𝓡_α| → 0`, then every cluster point of the averages
`μ_α = |𝓡_α|⁻¹ ∑_{Λ ∈ 𝓡_α} ν_α γ^α_Λ` is `τ`-invariant. -/
theorem measurePreserving_of_mapClusterPt_average_net {τ : Transformation S E}
    {γs : ι → Specification S E} {νs : ι → ProbabilityMeasure (S → E)}
    (hγ : ∀ a, Specification.IsInvariant τ (γs a))
    (hν : ∀ a, MeasurePreserving τ.toFun (νs a : Measure (S → E)) (νs a))
    {R : ι → Finset (Finset S)} (hR : ∀ a, (R a).Nonempty)
    (hlim : Tendsto (fun a ↦
      (((R a).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding ∆ R a).card : ℝ) /
        (R a).card) l (𝓝 0))
    {μs : ι → ProbabilityMeasure (S → E)}
    (hμs : ∀ a, (μs a : Measure (S → E)) = (γs a).average (νs a) (R a))
    {μ : ProbabilityMeasure (S → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun a ↦ WithSetwiseTopology.ofMeasure (μs a)) :
    MeasurePreserving τ.toFun μ μ := by
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hμ
  refine ⟨τ.measurable_toFun, ?_⟩
  have hmap : IsProbabilityMeasure ((μ : Measure (S → E)).map τ.toFun) := by
    constructor
    rw [Measure.map_apply τ.measurable_toFun .univ, preimage_univ, measure_univ]
  refine separatesOn_localEvents hmap inferInstance fun A hA ↦ ?_
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  rw [Measure.map_apply τ.measurable_toFun hAm]
  -- evaluations on the local events `A` and `τ⁻¹ A` converge along the ultrafilter `U`
  have h1 : Tendsto (fun a ↦ ((μs a : Measure (S → E)) A).toReal) U
      (𝓝 (((μ : Measure (S → E)) A).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hU A hA)
  have h2 : Tendsto (fun a ↦ ((μs a : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal) U
      (𝓝 (((μ : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hU _ (τ.preimage_mem_localEvents hA))
  -- `μ_α(τ⁻¹ A)` is the average over `τ_* 𝓡_α` evaluated at `A`, by (5.5)
  have hn : ∀ a, ((μs a : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal =
      ((γs a).average (νs a)
        ((R a).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding)).real A := by
    intro a
    rw [measureReal_def, ← Specification.map_average (hγ a) (hν a),
      Measure.map_apply τ.measurable_toFun hAm, hμs]
  -- the difference `μ_α(τ⁻¹ A) - μ_α(A)` tends to `0`, by the estimate of (5.18)
  have hdiff : Tendsto (fun a ↦ ((μs a : Measure (S → E)) (τ.toFun ⁻¹' A)).toReal -
      ((μs a : Measure (S → E)) A).toReal) l (𝓝 0) := by
    refine squeeze_zero_norm (fun a ↦ ?_) hlim
    rw [Real.norm_eq_abs, hn a, ← measureReal_def, hμs a]
    have h := Specification.abs_average_real_sub_le_of_card_eq (γ := γs a) (ν := νs a)
      (R := (R a).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding) (R' := R a)
      (hR a).map (Finset.card_map _) A
    rwa [Finset.card_map] at h
  have h3 := tendsto_nhds_unique (h2.sub h1) (hdiff.mono_left hUle)
  rw [sub_eq_zero] at h3
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

end Net

/-! ### Georgii Theorem (5.19) -/

section Invariant

variable [DecidableEq S] {I : Set (Transformation S E)} {γ : Specification S E}
  {γs : ι → Specification S E} {R : ι → Finset (Finset S)}
  {νs μs : ι → ProbabilityMeasure (S → E)}

/-- **Georgii Theorem (5.19)**, cluster-point form: under hypotheses (i)–(iii) every cluster point
`μ` of `μ_α = |𝓡_α|⁻¹ ∑_{Λ ∈ 𝓡_α} ν_α γ^α_Λ` lies in `𝒢_I(γ)`.

Georgii additionally assumes `γ` itself to be `I`-invariant; only the `I`-invariance of the
approximating specifications `γ^α` enters the proof, so it is not assumed here. -/
theorem mem_GP_and_forall_measurePreserving_of_mapClusterPt_average [l.NeBot]
    (hγq : γ.IsQuasilocal)
    (hγs : ∀ τ ∈ I, ∀ a, Specification.IsInvariant τ (γs a))
    (hunif : ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun a ↦ dist ((γs a).action Λ f) (γ.action Λ f)) l (𝓝 0))
    (hR : ∀ a, (R a).Nonempty) (hΛ : Tendsto (fun a ↦ (R a).inf' (hR a) id) l atTop)
    (hsymm : ∀ τ ∈ I, Tendsto (fun a ↦
      (((R a).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding ∆ R a).card : ℝ) /
        (R a).card) l (𝓝 0))
    (hνs : ∀ τ ∈ I, ∀ a, MeasurePreserving τ.toFun (νs a : Measure (S → E)) (νs a))
    (hμs : ∀ a, (μs a : Measure (S → E)) = (γs a).average (νs a) (R a))
    {μ : ProbabilityMeasure (S → E)}
    (hμ : MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun a ↦ WithSetwiseTopology.ofMeasure (μs a)) :
    μ ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  refine ⟨?_, fun τ hτ ↦ measurePreserving_of_mapClusterPt_average_net
    (fun a ↦ hγs τ hτ a) (fun a ↦ hνs τ hτ a) hR (hsymm τ hτ) hμs hμ⟩
  -- `μ_α γ^α_Λ = μ_α` for every `Λ ⊆ ⋂ 𝓡_α`, by consistency
  have hfix : ∀ a, (γs a).bindPM ((R a).inf' (hR a) id) (μs a) = μs a := by
    intro a
    refine ProbabilityMeasure.toMeasure_injective ?_
    rw [Specification.coe_bindPM, hμs a]
    exact Specification.bind_average_of_subset fun Λ' hΛ' ↦ Finset.inf'_le id hΛ'
  exact mem_GP_of_mapClusterPt hγq (γs := γs) (Λs := fun a ↦ (R a).inf' (hR a) id) (νs := μs)
    hΛ hunif (by simpa only [hfix] using hμ)

/-- **Georgii Theorem (5.19).** Let `(E, ℰ)` be standard Borel, `I` a set of transformations and
`γ` a quasilocal specification. Given

* (i) a net `(γ^α)` of `I`-invariant specifications with `γ^α → γ`,
* (ii) a net `(𝓡_α)` of non-empty finite families of volumes with `⋂ 𝓡_α ↑ S` and
  `|τ_* 𝓡_α ∆ 𝓡_α| / |𝓡_α| → 0` for all `τ ∈ I`,
* (iii) a net `(ν_α)` of `I`-invariant random fields such that the averages
  `μ_α = |𝓡_α|⁻¹ ∑_{Λ ∈ 𝓡_α} ν_α γ^α_Λ` are locally equicontinuous,

then `𝒢_I(γ)` contains a cluster point of `(μ_α)`, and is in particular non-empty. -/
theorem exists_mem_GP_and_forall_measurePreserving [StandardBorelSpace E] [l.NeBot]
    (hγq : γ.IsQuasilocal)
    (hγs : ∀ τ ∈ I, ∀ a, Specification.IsInvariant τ (γs a))
    (hunif : ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun a ↦ dist ((γs a).action Λ f) (γ.action Λ f)) l (𝓝 0))
    (hR : ∀ a, (R a).Nonempty) (hΛ : Tendsto (fun a ↦ (R a).inf' (hR a) id) l atTop)
    (hsymm : ∀ τ ∈ I, Tendsto (fun a ↦
      (((R a).map (Finset.mapEmbedding τ.sites.toEmbedding).toEmbedding ∆ R a).card : ℝ) /
        (R a).card) l (𝓝 0))
    (hνs : ∀ τ ∈ I, ∀ a, MeasurePreserving τ.toFun (νs a : Measure (S → E)) (νs a))
    (hμs : ∀ a, (μs a : Measure (S → E)) = (γs a).average (νs a) (R a))
    (hle : LocallyEquicontinuous l μs) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ) ∧
        MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
          fun a ↦ WithSetwiseTopology.ofMeasure (μs a) := by
  obtain ⟨μ, hμ⟩ := exists_mapClusterPt_of_locallyEquicontinuous
    (μs := fun a ↦ (WithSetwiseTopology.ofMeasure (μs a) : WithLocalConvergence S E)) hle
  obtain ⟨hGP, hinv⟩ := mem_GP_and_forall_measurePreserving_of_mapClusterPt_average
    (I := I) hγq hγs hunif hR hΛ hsymm hνs hμs hμ
  exact ⟨μ.toMeasure, hGP, hinv, hμ⟩

end Invariant

/-! ### Georgii Example (4.11)(2): local equicontinuity over a finite state space -/

/-- **Georgii Example (4.11)(2).** Over a finite state space every family of random fields is
locally equicontinuous: a finite volume carries only finitely many local events, so an antitone
sequence of them decreasing to `∅` is eventually empty. -/
theorem locallyEquicontinuous_of_finite [Finite E] [Nonempty E]
    (l : Filter ι) (μs : ι → ProbabilityMeasure (S → E)) : LocallyEquicontinuous l μs := by
  classical
  obtain ⟨e⟩ := ‹Nonempty E›
  intro Λ A hmeas hanti hempty
  have hsurj : Function.Surjective (Λ.restrict : (S → E) → Π _ : Λ, E) := fun x ↦
    ⟨fun j ↦ if h : j ∈ Λ then x ⟨j, h⟩ else e, funext fun i ↦ by simp [i.2]⟩
  have hrange : ∀ B : Set (Π _ : Λ, E), B ⊆ range (Λ.restrict : (S → E) → Π _ : Λ, E) := by
    intro B
    rw [hsurj.range_eq]
    exact subset_univ _
  have hB : ∀ m, ∃ B : Set (Π _ : Λ, E), A m = Λ.restrict ⁻¹' B := by
    intro m
    have h := hmeas m
    rw [cylinderEvents_eq_comap_finsetRestrict] at h
    obtain ⟨B, -, hB⟩ := h
    exact ⟨B, hB.symm⟩
  choose B hBeq using hB
  have hBanti : Antitone B := by
    intro m m' h
    refine (Set.preimage_subset_preimage_iff (hrange _)).1 ?_
    rw [← hBeq, ← hBeq]
    exact hanti h
  have hBex : ∀ x : Π _ : Λ, E, ∃ m, x ∉ B m := by
    intro x
    by_contra hx
    push Not at hx
    obtain ⟨ω, hω⟩ := hsurj x
    have hmem : ω ∈ ⋂ m, A m := mem_iInter.2 fun m ↦ by
      rw [hBeq m]
      exact show Λ.restrict ω ∈ B m from hω ▸ hx m
    rw [hempty] at hmem
    exact hmem
  choose f hf using hBex
  obtain ⟨M, hM⟩ := Finite.exists_le f
  have hAM : ∀ m, M ≤ m → A m = ∅ := by
    intro m hm
    rw [hBeq m, Set.eq_empty_iff_forall_notMem]
    intro ω hω
    exact hf (Λ.restrict ω) (hBanti (hM _) (hBanti hm hω))
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop M] with m hm
  refine (le_antisymm (Filter.limsup_le_of_le (h := ?_)) zero_le).symm
  exact Eventually.of_forall fun i ↦ by simp [hAM m hm]

end MeasureTheory.GibbsMeasure

end

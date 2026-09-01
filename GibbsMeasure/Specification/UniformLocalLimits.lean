/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LocalLimits
public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Georgii, Theorem (7.12)(c): local convergence in total variation

Let `γ = ρ λ` be a λ-specification and `μ ∈ ex 𝒢(γ)`. Along an increasing cofinal sequence of
volumes `(Λ_n)`, the finite-volume Gibbs distributions converge to `μ` **uniformly on the events
of each finite volume `Δ`**, for `μ`-almost every boundary condition:

`sup {|γ_{Λ_n}(A | ω) - μ(A)| : A ∈ 𝓕_Δ} → 0`.

Theorem (7.12)(b) is weak convergence for a compact metric state space; local convergence is the
second conclusion of (7.12)(c) and is proved, for a finite state space, in
`Specification/LocalLimits.lean`. Total-variation convergence on each `𝓕_Δ` is stronger; this is
Georgii's argument, run through the densities.

Writing `ρ_Δ^Λ = λ_{Λ ∖ Δ} ρ_Λ` (`Specification.condDensity`) and
`ρ̄_Δ(σ) = ∫ μ(dη) ρ_Δ(σ_Δ η_{S∖Δ})` (`Specification.avgDensity`), and `v = μ λ_Δ`:

* `Specification.lintegral_modificationKer_isssd`: `γ_Λ f = λ_Δ(ρ_Δ^Λ f)` for `f ∈ 𝓕_{(Λ∖Δ)ᶜ}`;
* `Specification.condExp_ae_eq_condDensity`: hence `ρ_Δ^Λ = v(ρ_Δ | 𝓣_{Λ∖Δ})`;
* `Specification.condExp_iInf_ae_eq_avgDensity`: tail triviality of `μ` identifies
  `v(ρ_Δ | ⋂_n 𝓣_{Λ_n∖Δ})` with `ρ̄_Δ`;
* `Specification.ae_tendsto_toReal_condDensity`: Lévy's downward theorem then gives
  `ρ_Δ^{Λ_n} → ρ̄_Δ` `v`-almost everywhere;
* `Specification.tendsto_integral_abs_condDensity_sub_avgDensity`: both densities have `λ_Δ`-mass
  `1`, so Scheffé's lemma upgrades this to `λ_Δ(|ρ_Δ^{Λ_n} - ρ̄_Δ| | ω) → 0`.

## Main results

* `Specification.ae_tendsto_iSup_ofReal_abs_sub`;
* `MeasureTheory.GibbsMeasure.ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G`:
  (7.12)(c) as Georgii states it — one `μ`-full set of boundary conditions works for *every*
  finite volume `Δ`, along any monotone cofinal exhaustion.
* `MeasureTheory.GibbsMeasure.ae_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G`, for
  `μ ∈ ex 𝒢(γ)`;
* `MeasureTheory.GibbsMeasure.ae_tendsto_iSup_ofReal_abs_sub_lambdaSpecification`, stated for
  Georgii's λ-specifications of Definition (1.27).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} [DecidableEq S]
  (ν : Measure E) [IsProbabilityMeasure ν] (ρ : Finset S → (S → E) → ℝ≥0∞)

/-- Georgii's `ρ_Δ^Λ = λ_{Λ ∖ Δ} ρ_Λ` in the proof of (7.12)(c): the density, with respect to the
independent kernel `λ_Δ`, of the finite-volume Gibbs distribution `γ_Λ(· | ω)` on the events of
`Δ`. -/
noncomputable def condDensity (Δ Λ : Finset S) (ω : S → E) : ℝ≥0∞ :=
  ∫⁻ σ, ρ Λ σ ∂(isssd ν (Λ \ Δ) ω)

variable {ν ρ}

lemma measurable_condDensity (hρ : ∀ Λ, Measurable (ρ Λ)) (Δ Λ : Finset S) :
    Measurable[cylinderEvents ((Λ \ Δ : Finset S) : Set S)ᶜ] (condDensity ν ρ Δ Λ) :=
  (hρ Λ).lintegral_kernel

omit [DecidableEq S] in
/-- Resampling no site at all leaves the boundary condition alone. -/
@[simp] lemma isssd_empty_apply (ω : S → E) : isssd ν (∅ : Finset S) ω = Measure.dirac ω := by
  have h : juxt (((∅ : Finset S) : Set S)) ω = fun _ ↦ ω := by
    funext ζ x
    exact juxt_apply_of_not_mem (by simp) ζ
  simp [isssdFun_apply, h, Measure.map_const]

@[simp] lemma condDensity_self {Δ : Finset S} (hρ : Measurable (ρ Δ)) :
    condDensity ν ρ Δ Δ = ρ Δ := by
  funext ω
  rw [condDensity, Finset.sdiff_self, isssd_empty_apply, lintegral_dirac' _ hρ]

/-- Georgii (1.25) in measure form: resampling `Λ₁` and then `Λ₂` resamples `Λ₁ ∪ Λ₂`. -/
lemma isssd_bind_isssd (Λ₁ Λ₂ : Finset S) (ω : S → E) :
    (isssd ν Λ₁ ω).bind (isssd ν Λ₂) = isssd ν (Λ₂ ∪ Λ₁) ω := by
  have h := DFunLike.congr_fun (isssd_comp_isssd (ν := ν) Λ₂ Λ₁) ω
  rw [Kernel.comp_apply] at h
  simpa [Kernel.comap_apply] using h

/-- **The key identity of Georgii's proof of (7.12)(c)**: for `f` measurable with respect to the
events outside `Λ ∖ Δ` — in particular for every `f` measurable with respect to the events of `Δ` —
the finite-volume Gibbs distribution `γ_Λ(· | ω)` integrates `f` against the density `ρ_Δ^Λ` and the
independent kernel `λ_Δ`. -/
lemma lintegral_modificationKer_isssd (hρ : ∀ Λ, Measurable (ρ Λ)) {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable[cylinderEvents ((Λ \ Δ : Finset S) : Set S)ᶜ] f)
    (ω : S → E) :
    ∫⁻ σ, f σ ∂(modificationKer (isssd ν) ρ hρ Λ ω)
      = ∫⁻ σ, condDensity ν ρ Δ Λ σ * f σ ∂(isssd ν Δ ω) := by
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hunion : (Λ \ Δ) ∪ Δ = Λ := Finset.sdiff_union_of_subset hΔ
  have hae : AEMeasurable (fun τ ↦ isssd ν (Λ \ Δ) τ) (isssd ν Δ ω) :=
    (((isssd ν (Λ \ Δ)).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  calc ∫⁻ σ, f σ ∂(modificationKer (isssd ν) ρ hρ Λ ω)
      = ∫⁻ σ, ρ Λ σ * f σ ∂(isssd ν Λ ω) := by
        rw [modificationKer_apply, lintegral_withDensity_eq_lintegral_mul _ (hρ Λ) hfm]
        rfl
    _ = ∫⁻ σ, ρ Λ σ * f σ ∂((isssd ν Δ ω).bind (isssd ν (Λ \ Δ))) := by
        rw [isssd_bind_isssd, hunion]
    _ = ∫⁻ τ, (∫⁻ σ, ρ Λ σ * f σ ∂(isssd ν (Λ \ Δ) τ)) ∂(isssd ν Δ ω) :=
        Measure.lintegral_bind hae (((hρ Λ).mul hfm).aemeasurable)
    _ = ∫⁻ τ, condDensity ν ρ Δ Λ τ * f τ ∂(isssd ν Δ ω) := by
        refine lintegral_congr fun τ ↦ ?_
        simp_rw [mul_comm (ρ Λ _) (f _)]
        rw [Specification.lintegral_mul (isssd ν) (Λ \ Δ) (hρ Λ) hf, mul_comm]
        rfl

/-- The density `ρ_Δ^Λ` is normalized: `λ_Δ ρ_Δ^Λ = 1`. -/
lemma lintegral_condDensity (hmod : (isssd ν).IsModifier ρ) {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ)
    (ω : S → E) : ∫⁻ σ, condDensity ν ρ Δ Λ σ ∂(isssd ν Δ ω) = 1 := by
  have := hmod.isMarkovKernel Λ
  have h := lintegral_modificationKer_isssd (ν := ν) (ρ := ρ) hmod.measurable hΔ
    (f := fun _ ↦ 1) measurable_const ω
  rw [lintegral_one, measure_univ] at h
  simp only [mul_one] at h
  exact h.symm

/-- Georgii's identity `μ(f) = v(ρ_Δ^Λ f)` for `v = μ λ_Δ` and `f` measurable with respect to the
events outside `Λ ∖ Δ`. -/
lemma lintegral_eq_lintegral_condDensity_mul (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ] {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) {f : (S → E) → ℝ≥0∞}
    (hf : Measurable[cylinderEvents ((Λ \ Δ : Finset S) : Set S)ᶜ] f) :
    ∫⁻ σ, f σ ∂μ = ∫⁻ σ, condDensity ν ρ Δ Λ σ * f σ ∂(μ.bind (isssd ν Δ)) := by
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hcm : Measurable (condDensity ν ρ Δ Λ) :=
    (measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi le_rfl
  have hbind : μ.bind ((isssd ν).modification ρ hmod Λ) = μ :=
    (isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := (isssd ν).modification ρ hmod)
      (μ := μ)).1 hμ Λ
  have hae₁ : AEMeasurable (fun ω ↦ ((isssd ν).modification ρ hmod Λ) ω) μ :=
    ((((isssd ν).modification ρ hmod Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hae₂ : AEMeasurable (fun ω ↦ isssd ν Δ ω) μ :=
    (((isssd ν Δ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  calc ∫⁻ σ, f σ ∂μ
      = ∫⁻ σ, f σ ∂(μ.bind ((isssd ν).modification ρ hmod Λ)) := by rw [hbind]
    _ = ∫⁻ ω, ∫⁻ σ, f σ ∂((isssd ν).modification ρ hmod Λ ω) ∂μ :=
        Measure.lintegral_bind hae₁ hfm.aemeasurable
    _ = ∫⁻ ω, ∫⁻ σ, condDensity ν ρ Δ Λ σ * f σ ∂(isssd ν Δ ω) ∂μ :=
        lintegral_congr fun ω ↦ lintegral_modificationKer_isssd hmod.measurable hΔ hf ω
    _ = ∫⁻ σ, condDensity ν ρ Δ Λ σ * f σ ∂(μ.bind (isssd ν Δ)) :=
        (Measure.lintegral_bind hae₂ (hcm.mul hfm).aemeasurable).symm

omit [DecidableEq S] in
/-- The `Λ = Δ` case of `lintegral_eq_lintegral_condDensity_mul`: `μ(f) = v(ρ_Δ f)` for *every*
bounded measurable `f`, where `v = μ λ_Δ`. -/
lemma lintegral_eq_lintegral_mul_bind (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ] (Δ : Finset S) {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂μ = ∫⁻ σ, ρ Δ σ * f σ ∂(μ.bind (isssd ν Δ)) := by
  classical
  have hcyl : cylinderEvents (((Δ \ Δ : Finset S) : Set S))ᶜ
      = (inferInstance : MeasurableSpace (S → E)) := by
    simp
  have hf' : Measurable[cylinderEvents (((Δ \ Δ : Finset S) : Set S))ᶜ] f :=
    hf.mono (le_of_eq hcyl.symm) le_rfl
  simpa [condDensity_self (hmod.measurable Δ)] using
    lintegral_eq_lintegral_condDensity_mul hmod hμ (le_refl Δ) hf'

section AvgDensity

variable (ρ)

/-- Georgii's `ρ̄_Δ(σ) = ∫ μ(dη) ρ_Δ(σ_Δ η_{S∖Δ})`, the `μ`-average of `ρ_Δ` over the boundary
condition outside `Δ`. -/
noncomputable def avgDensity (μ : Measure (S → E)) (Δ : Finset S) (σ : S → E) : ℝ≥0∞ :=
  ∫⁻ η, ρ Δ (juxt (Δ : Set S) η (Δ.restrict σ)) ∂μ

variable {ρ}

omit [DecidableEq S] in
lemma measurable_juxt_restrict (Δ : Finset S) :
    Measurable fun p : (S → E) × (S → E) ↦ juxt (Δ : Set S) p.1 (Δ.restrict p.2) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ (Δ : Set S)
  · have h : (fun p : (S → E) × (S → E) ↦ juxt (Δ : Set S) p.1 (Δ.restrict p.2) i)
        = fun p ↦ p.2 i := funext fun p ↦ by simpa using juxt_apply_of_mem hi (Δ.restrict p.2)
    rw [h]
    exact (measurable_pi_apply i).comp measurable_snd
  · have h : (fun p : (S → E) × (S → E) ↦ juxt (Δ : Set S) p.1 (Δ.restrict p.2) i)
        = fun p ↦ p.1 i := funext fun p ↦ juxt_apply_of_not_mem hi (Δ.restrict p.2)
    rw [h]
    exact (measurable_pi_apply i).comp measurable_fst

omit [DecidableEq S] in
lemma measurable_avgDensity (μ : Measure (S → E)) [SFinite μ] {Δ : Finset S}
    (hρ : Measurable (ρ Δ)) :
    Measurable[cylinderEvents ((Δ : Finset S) : Set S)] (avgDensity ρ μ Δ) := by
  refine Measurable.cylinderEvents_of_dependsOn ?_ ?_
  · refine Measurable.lintegral_prod_right'
      (f := fun p : (S → E) × (S → E) ↦ ρ Δ (juxt (Δ : Set S) p.2 (Δ.restrict p.1))) ?_
    simpa [Function.comp_def] using hρ.comp ((measurable_juxt_restrict Δ).comp measurable_swap)
  · intro σ σ' h
    have : Δ.restrict σ = Δ.restrict σ' := funext fun i ↦ h i i.2
    simp [avgDensity, this]

omit [DecidableEq S] in
lemma measurable_juxt_snd (Δ : Finset S) :
    Measurable fun p : (Δ → E) × (S → E) ↦ juxt (Δ : Set S) p.2 p.1 := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ (Δ : Set S)
  · have h : (fun p : (Δ → E) × (S → E) ↦ juxt (Δ : Set S) p.2 p.1 i)
        = fun p ↦ p.1 ⟨i, hi⟩ := funext fun p ↦ juxt_apply_of_mem hi p.1
    rw [h]
    exact (measurable_pi_apply _).comp measurable_fst
  · have h : (fun p : (Δ → E) × (S → E) ↦ juxt (Δ : Set S) p.2 p.1 i)
        = fun p ↦ p.2 i := funext fun p ↦ juxt_apply_of_not_mem hi p.1
    rw [h]
    exact (measurable_pi_apply i).comp measurable_snd

omit [DecidableEq S] in
lemma restrict_juxt (Δ : Finset S) (η : S → E) (ζ : Δ → E) :
    Δ.restrict (juxt (Δ : Set S) η ζ) = ζ :=
  funext fun i ↦ juxt_apply_of_mem (by simp) ζ

omit [DecidableEq S] in
/-- **Georgii's identity for `ρ̄_Δ`**: for every boundary condition `ω` and every observable `f`
measurable with respect to the events of `Δ`, `λ_Δ(ρ̄_Δ f | ω) = μ(f)`.  Taking `f = 1` gives the
normalization `λ_Δ ρ̄_Δ = 1` used by Scheffé's lemma. -/
lemma lintegral_avgDensity_mul (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ] {Δ : Finset S} {f : (S → E) → ℝ≥0∞}
    (hf : Measurable[cylinderEvents ((Δ : Finset S) : Set S)] f) (ω : S → E) :
    ∫⁻ σ, avgDensity ρ μ Δ σ * f σ ∂(isssd ν Δ ω) = ∫⁻ σ, f σ ∂μ := by
  classical
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn f ((Δ : Finset S) : Set S) := hf.dependsOn_of_cylinderEvents
  have hjm : Measurable fun p : (Δ → E) × (S → E) ↦ juxt (Δ : Set S) p.2 p.1 :=
    measurable_juxt_snd Δ
  have hFm : Measurable (Function.uncurry fun (ζ : Δ → E) (η : S → E) ↦
      ρ Δ (juxt (Δ : Set S) η ζ) * f (juxt (Δ : Set S) η ζ)) :=
    ((hmod.measurable Δ).mul hfm).comp hjm
  have hmulm : Measurable fun σ ↦ ρ Δ σ * f σ := (hmod.measurable Δ).mul hfm
  have hae : AEMeasurable (fun τ ↦ isssd ν Δ τ) μ :=
    (((isssd ν Δ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have havg : Measurable fun σ ↦ avgDensity ρ μ Δ σ * f σ :=
    ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl).mul hfm
  calc ∫⁻ σ, avgDensity ρ μ Δ σ * f σ ∂(isssd ν Δ ω)
      = ∫⁻ ζ, avgDensity ρ μ Δ (juxt (Δ : Set S) ω ζ) * f (juxt (Δ : Set S) ω ζ)
          ∂(Measure.pi fun _ : Δ ↦ ν) := lintegral_isssd_eq Δ ω havg
    _ = ∫⁻ ζ, ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) * f (juxt (Δ : Set S) η ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) := by
        refine lintegral_congr fun ζ ↦ ?_
        have hconst : ∀ η : S → E, f (juxt (Δ : Set S) η ζ) = f (juxt (Δ : Set S) ω ζ) :=
          fun η ↦ hdep fun i hi ↦ by
            rw [juxt_apply_of_mem hi ζ, juxt_apply_of_mem hi ζ]
        simp only [hconst]
        rw [avgDensity, restrict_juxt Δ ω ζ]
        exact (lintegral_mul_const _
          ((hmod.measurable Δ).comp (measurable_juxt_boundary ζ))).symm
    _ = ∫⁻ η, ∫⁻ ζ, ρ Δ (juxt (Δ : Set S) η ζ) * f (juxt (Δ : Set S) η ζ)
          ∂(Measure.pi fun _ : Δ ↦ ν) ∂μ := lintegral_lintegral_swap hFm.aemeasurable
    _ = ∫⁻ η, ∫⁻ σ, ρ Δ σ * f σ ∂(isssd ν Δ η) ∂μ :=
        lintegral_congr fun η ↦ (lintegral_isssd_eq Δ η hmulm).symm
    _ = ∫⁻ σ, ρ Δ σ * f σ ∂(μ.bind (isssd ν Δ)) :=
        (Measure.lintegral_bind hae hmulm.aemeasurable).symm
    _ = ∫⁻ σ, f σ ∂μ := (lintegral_eq_lintegral_mul_bind hmod hμ Δ hfm).symm

variable (ρ) in
/-- The `Δ`-configuration form of `ρ̄_Δ`: `R_Δ(ζ) = ∫ μ(dη) ρ_Δ(ζ η_{S∖Δ})`. -/
noncomputable def avgKernel (μ : Measure (S → E)) (Δ : Finset S) (ζ : Δ → E) : ℝ≥0∞ :=
  ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) ∂μ

omit [DecidableEq S] in
lemma measurable_avgKernel (μ : Measure (S → E)) [SFinite μ] {Δ : Finset S}
    (hρ : Measurable (ρ Δ)) : Measurable (avgKernel ρ μ Δ) := by
  refine Measurable.lintegral_prod_right'
    (f := fun p : (Δ → E) × (S → E) ↦ ρ Δ (juxt (Δ : Set S) p.2 p.1)) ?_
  exact hρ.comp (measurable_juxt_snd Δ)

omit [DecidableEq S] in
lemma avgDensity_juxt (μ : Measure (S → E)) (Δ : Finset S) (ω : S → E) (ζ : Δ → E) :
    avgDensity ρ μ Δ (juxt (Δ : Set S) ω ζ) = avgKernel ρ μ Δ ζ := by
  rw [avgDensity, restrict_juxt Δ ω ζ, avgKernel]

omit [DecidableEq S] in
lemma lintegral_bind_isssd (μ : Measure (S → E)) [SFinite μ] (Δ : Finset S) {g : (S → E) → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ σ, g σ ∂(μ.bind (isssd ν Δ))
      = ∫⁻ ω, ∫⁻ ζ, g (juxt (Δ : Set S) ω ζ) ∂(Measure.pi fun _ : Δ ↦ ν) ∂μ := by
  have hae : AEMeasurable (fun τ ↦ isssd ν Δ τ) μ :=
    (((isssd ν Δ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  rw [Measure.lintegral_bind hae hg.aemeasurable]
  exact lintegral_congr fun ω ↦ lintegral_isssd_eq Δ ω hg

omit [DecidableEq S] in
/-- Fubini form of `v(ρ̄_Δ g)`: the `ρ̄` factor depends only on the `Δ`-coordinates, so it comes out
of the `μ`-integral. -/
lemma lintegral_avgDensity_mul_bind (μ : Measure (S → E)) [SFinite μ] {Δ : Finset S}
    (hρ : Measurable (ρ Δ)) {g : (S → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ σ, avgDensity ρ μ Δ σ * g σ ∂(μ.bind (isssd ν Δ))
      = ∫⁻ ζ, avgKernel ρ μ Δ ζ * ∫⁻ ω, g (juxt (Δ : Set S) ω ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) := by
  have hprod : Measurable (Function.uncurry fun (ω : S → E) (ζ : Δ → E) ↦
      avgKernel ρ μ Δ ζ * g (juxt (Δ : Set S) ω ζ)) := by
    refine ((measurable_avgKernel μ hρ).comp measurable_snd).mul (hg.comp ?_)
    exact (measurable_juxt_snd Δ).comp (measurable_swap)
  calc ∫⁻ σ, avgDensity ρ μ Δ σ * g σ ∂(μ.bind (isssd ν Δ))
      = ∫⁻ ω, ∫⁻ ζ, avgKernel ρ μ Δ ζ * g (juxt (Δ : Set S) ω ζ)
          ∂(Measure.pi fun _ : Δ ↦ ν) ∂μ := by
        have hm : Measurable fun σ ↦ avgDensity ρ μ Δ σ * g σ :=
          ((measurable_avgDensity μ hρ).mono cylinderEvents_le_pi le_rfl).mul hg
        rw [lintegral_bind_isssd μ Δ hm]
        exact lintegral_congr fun ω ↦ lintegral_congr fun ζ ↦ by rw [avgDensity_juxt]
    _ = ∫⁻ ζ, ∫⁻ ω, avgKernel ρ μ Δ ζ * g (juxt (Δ : Set S) ω ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) := lintegral_lintegral_swap hprod.aemeasurable
    _ = ∫⁻ ζ, avgKernel ρ μ Δ ζ * ∫⁻ ω, g (juxt (Δ : Set S) ω ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) :=
        lintegral_congr fun ζ ↦ lintegral_const_mul _ (hg.comp (measurable_juxt_boundary ζ))

omit [DecidableEq S] in
/-- Fubini form of `v(ρ_Δ g)`. -/
lemma lintegral_mul_bind (μ : Measure (S → E)) [SFinite μ] {Δ : Finset S}
    (hρ : Measurable (ρ Δ)) {g : (S → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ σ, ρ Δ σ * g σ ∂(μ.bind (isssd ν Δ))
      = ∫⁻ ζ, ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) * g (juxt (Δ : Set S) η ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) := by
  have hprod : Measurable (Function.uncurry fun (η : S → E) (ζ : Δ → E) ↦
      ρ Δ (juxt (Δ : Set S) η ζ) * g (juxt (Δ : Set S) η ζ)) := by
    have h : Measurable fun p : (S → E) × (Δ → E) ↦ juxt (Δ : Set S) p.1 p.2 :=
      (measurable_juxt_snd Δ).comp measurable_swap
    exact (hρ.comp h).mul (hg.comp h)
  have hm : Measurable fun σ ↦ ρ Δ σ * g σ := hρ.mul hg
  rw [lintegral_bind_isssd μ Δ hm]
  exact lintegral_lintegral_swap hprod.aemeasurable

end AvgDensity

section Normalization

variable (hmod : (isssd ν).IsModifier ρ) {μ : Measure (S → E)}
  (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) [IsProbabilityMeasure μ]

omit [DecidableEq S] in
include hmod hμ in
/-- `v(ρ_Δ) = 1`, where `v = μ λ_Δ`. -/
lemma lintegral_rho_bind (Δ : Finset S) :
    ∫⁻ σ, ρ Δ σ ∂(μ.bind (isssd ν Δ)) = 1 := by
  have h := lintegral_eq_lintegral_mul_bind hmod hμ Δ (f := fun _ ↦ 1) measurable_const
  simpa using h.symm

include hmod hμ in
/-- `v(ρ_Δ^Λ) = 1`. -/
lemma lintegral_condDensity_bind {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) :
    ∫⁻ σ, condDensity ν ρ Δ Λ σ ∂(μ.bind (isssd ν Δ)) = 1 := by
  have h := lintegral_eq_lintegral_condDensity_mul hmod hμ hΔ
    (f := fun _ ↦ 1) measurable_const
  simpa using h.symm

omit [DecidableEq S] in
include hmod hμ in
/-- `λ_Δ ρ̄_Δ = 1`, for every boundary condition. -/
lemma lintegral_avgDensity (Δ : Finset S) (ω : S → E) :
    ∫⁻ σ, avgDensity ρ μ Δ σ ∂(isssd ν Δ ω) = 1 := by
  have h := lintegral_avgDensity_mul hmod hμ (Δ := Δ) (f := fun _ ↦ 1) measurable_const ω
  simpa using h

omit [DecidableEq S] in
include hmod hμ in
/-- `v(ρ̄_Δ) = 1`. -/
lemma lintegral_avgDensity_bind (Δ : Finset S) :
    ∫⁻ σ, avgDensity ρ μ Δ σ ∂(μ.bind (isssd ν Δ)) = 1 := by
  have hae : AEMeasurable (fun τ ↦ isssd ν Δ τ) μ :=
    (((isssd ν Δ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have h : ∫⁻ ω, ∫⁻ x, avgDensity ρ μ Δ x ∂(isssd ν Δ ω) ∂μ = 1 := by
    rw [lintegral_congr fun ω ↦ lintegral_avgDensity hmod hμ Δ ω]
    simp
  rw [Measure.lintegral_bind hae
    ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl).aemeasurable]
  exact h

omit [DecidableEq S] in
include hmod hμ in
lemma setLIntegral_rho_bind (Δ : Finset S) {A : Set (S → E)} (hA : MeasurableSet A) :
    ∫⁻ σ in A, ρ Δ σ ∂(μ.bind (isssd ν Δ)) = μ A := by
  have hind : Measurable (A.indicator (1 : (S → E) → ℝ≥0∞)) := measurable_one.indicator hA
  have h : (fun σ ↦ ρ Δ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ) = A.indicator (ρ Δ) := by
    funext σ; by_cases hσ : σ ∈ A <;> simp [hσ]
  have key := lintegral_eq_lintegral_mul_bind hmod hμ Δ hind
  rw [lintegral_indicator_one hA] at key
  rw [h, lintegral_indicator hA] at key
  exact key.symm

include hmod hμ in
lemma setLIntegral_condDensity_bind {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ] A) :
    ∫⁻ σ in A, condDensity ν ρ Δ Λ σ ∂(μ.bind (isssd ν Δ)) = μ A := by
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hind : Measurable[cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ]
      (A.indicator (1 : (S → E) → ℝ≥0∞)) := Measurable.indicator measurable_const hA
  have h : (fun σ ↦ condDensity ν ρ Δ Λ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
      = A.indicator (condDensity ν ρ Δ Λ) := by
    funext σ; by_cases hσ : σ ∈ A <;> simp [hσ]
  have key := lintegral_eq_lintegral_condDensity_mul hmod hμ hΔ hind
  rw [lintegral_indicator_one hA'] at key
  rw [h, lintegral_indicator hA'] at key
  exact key.symm

end Normalization

section TailTrivial

/-- Gluing a fixed inner configuration `ζ` into a boundary condition sends the events outside `Λ`
to the events outside `Λ ∖ Δ`. -/
lemma measurable_juxt_cylinderEvents (Δ Λ : Finset S) (ζ : Δ → E) :
    Measurable[cylinderEvents (((Λ : Finset S) : Set S))ᶜ,
        cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ]
      fun ω : S → E ↦ juxt (Δ : Set S) ω ζ := by
  rw [measurable_cylinderEvents_iff (mα := cylinderEvents (((Λ : Finset S) : Set S))ᶜ)]
  intro i hi
  by_cases hiΔ : i ∈ (Δ : Set S)
  · simp only [juxt_apply_of_mem hiΔ]
    exact measurable_const
  · have hiΛ : i ∈ (((Λ : Finset S) : Set S))ᶜ := by
      simp only [Finset.coe_sdiff, Set.mem_compl_iff, Set.mem_sdiff, Finset.mem_coe] at hi
      simp only [Set.mem_compl_iff, Finset.mem_coe]
      exact fun h ↦ hi ⟨h, by simpa using hiΔ⟩
    simp only [juxt_apply_of_not_mem hiΔ]
    exact measurable_cylinderEvent_apply hiΛ

/-- **Georgii's identification of the limit of the reversed martingale.**  For an event `A` lying
in every `𝓣_{Λ_n ∖ Δ}`, tail triviality of `μ` makes `ρ̄_Δ` integrate against `1_A` exactly as
`ρ_Δ` does; this is what identifies `v(ρ_Δ | ⋂_n 𝓣_{Λ_n∖Δ})` with `ρ̄_Δ`. -/
lemma lintegral_avgDensity_mul_indicator [Countable S] (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {A : Set (S → E)}
    (hA : ∀ n, MeasurableSet[cylinderEvents (((Λ n \ Δ : Finset S) : Set S))ᶜ] A) :
    ∫⁻ σ, avgDensity ρ μ Δ σ * A.indicator 1 σ ∂(μ.bind (isssd ν Δ)) = μ A := by
  classical
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ (hA 0)
  have hind : Measurable (A.indicator (1 : (S → E) → ℝ≥0∞)) := measurable_one.indicator hAm
  -- the fibre `A_ζ` is a tail event, hence trivial
  have hfib : ∀ ζ : Δ → E, μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A) = 0 ∨
      μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A) = 1 := by
    intro ζ
    refine htail _ ?_
    rw [MeasureTheory.GibbsMeasure.tailSigmaAlgebra_eq_iInf_of_cofinal (E := E) hcof]
    exact MeasurableSpace.measurableSet_iInf.2
      fun n ↦ measurable_juxt_cylinderEvents Δ (Λ n) ζ (hA n)
  have hpre : ∀ (ζ : Δ → E), ∫⁻ ω, A.indicator (1 : (S → E) → ℝ≥0∞) (juxt (Δ : Set S) ω ζ) ∂μ
      = μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A) := by
    intro ζ
    have h : (fun ω : S → E ↦ A.indicator (1 : (S → E) → ℝ≥0∞) (juxt (Δ : Set S) ω ζ))
        = ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A).indicator 1 := by
      funext ω
      by_cases h : juxt (Δ : Set S) ω ζ ∈ A <;> simp [h, Set.mem_preimage]
    rw [h, lintegral_indicator_one ((measurable_juxt_boundary ζ) hAm)]
  have hkey : ∀ ζ : Δ → E, avgKernel ρ μ Δ ζ *
      ∫⁻ ω, A.indicator (1 : (S → E) → ℝ≥0∞) (juxt (Δ : Set S) ω ζ) ∂μ
      = ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) * A.indicator 1 (juxt (Δ : Set S) η ζ) ∂μ := by
    intro ζ
    rw [hpre ζ]
    rcases hfib ζ with h0 | h1
    · rw [h0, mul_zero]
      refine ((lintegral_eq_zero_iff' ?_).2 ?_).symm
      · exact ((hmod.measurable Δ).comp (measurable_juxt_boundary ζ)).aemeasurable.mul
          (hind.comp (measurable_juxt_boundary ζ)).aemeasurable
      · have hnull : ∀ᵐ ω ∂μ, juxt (Δ : Set S) ω ζ ∉ A := by
          rw [ae_iff]
          simp only [not_not]
          exact (show {a | juxt (Δ : Set S) a ζ ∈ A}
            = (fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A from rfl) ▸ h0
        filter_upwards [hnull] with ω hω
        simp [Set.indicator_of_notMem hω]
    · rw [h1, mul_one, avgKernel]
      refine lintegral_congr_ae ?_
      have h2 : μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A)ᶜ = 0 := by
        rw [measure_compl ((measurable_juxt_boundary ζ) hAm) (measure_ne_top _ _), h1,
          measure_univ, tsub_self]
      have hfull : ∀ᵐ ω ∂μ, juxt (Δ : Set S) ω ζ ∈ A := by
        rw [ae_iff]; exact h2
      filter_upwards [hfull] with ω hω
      simp [Set.indicator_of_mem hω]
  calc ∫⁻ σ, avgDensity ρ μ Δ σ * A.indicator 1 σ ∂(μ.bind (isssd ν Δ))
      = ∫⁻ ζ, avgKernel ρ μ Δ ζ *
          ∫⁻ ω, A.indicator (1 : (S → E) → ℝ≥0∞) (juxt (Δ : Set S) ω ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) :=
        lintegral_avgDensity_mul_bind μ (hmod.measurable Δ) hind
    _ = ∫⁻ ζ, ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) * A.indicator 1 (juxt (Δ : Set S) η ζ) ∂μ
          ∂(Measure.pi fun _ : Δ ↦ ν) := lintegral_congr hkey
    _ = ∫⁻ σ, ρ Δ σ * A.indicator 1 σ ∂(μ.bind (isssd ν Δ)) :=
        (lintegral_mul_bind μ (hmod.measurable Δ) hind).symm
    _ = ∫⁻ σ, A.indicator (1 : (S → E) → ℝ≥0∞) σ ∂μ :=
        (lintegral_eq_lintegral_mul_bind hmod hμ Δ hind).symm
    _ = μ A := lintegral_indicator_one hAm

lemma setLIntegral_avgDensity_bind [Countable S] (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {A : Set (S → E)}
    (hA : ∀ n, MeasurableSet[cylinderEvents (((Λ n \ Δ : Finset S) : Set S))ᶜ] A) :
    ∫⁻ σ in A, avgDensity ρ μ Δ σ ∂(μ.bind (isssd ν Δ)) = μ A := by
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ (hA 0)
  have h : (fun σ ↦ avgDensity ρ μ Δ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
      = A.indicator (avgDensity ρ μ Δ) := by
    funext σ; by_cases hσ : σ ∈ A <;> simp [hσ]
  have key := lintegral_avgDensity_mul_indicator hmod hμ htail hcof hA
  rw [h, lintegral_indicator hA'] at key
  exact key

end TailTrivial

section Martingale

variable (hmod : (isssd ν).IsModifier ρ) {μ : Measure (S → E)}
  (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) [IsProbabilityMeasure μ]

include hmod hμ

omit [DecidableEq S] in
lemma integrable_toReal_rho (Δ : Finset S) :
    Integrable (fun σ ↦ (ρ Δ σ).toReal) (μ.bind (isssd ν Δ)) :=
  integrable_toReal_of_lintegral_ne_top (hmod.measurable Δ).aemeasurable
    (by rw [lintegral_rho_bind hmod hμ Δ]; exact ENNReal.one_ne_top)

omit [DecidableEq S] in
lemma ae_lt_top_rho (Δ : Finset S) : ∀ᵐ σ ∂(μ.bind (isssd ν Δ)), ρ Δ σ < ⊤ :=
  ae_lt_top' (hmod.measurable Δ).aemeasurable
    (by rw [lintegral_rho_bind hmod hμ Δ]; exact ENNReal.one_ne_top)

lemma integrable_toReal_condDensity {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) :
    Integrable (fun σ ↦ (condDensity ν ρ Δ Λ σ).toReal) (μ.bind (isssd ν Δ)) :=
  integrable_toReal_of_lintegral_ne_top
    ((measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi le_rfl).aemeasurable
    (by rw [lintegral_condDensity_bind hmod hμ hΔ]; exact ENNReal.one_ne_top)

lemma ae_lt_top_condDensity {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) :
    ∀ᵐ σ ∂(μ.bind (isssd ν Δ)), condDensity ν ρ Δ Λ σ < ⊤ :=
  ae_lt_top'
    ((measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi le_rfl).aemeasurable
    (by rw [lintegral_condDensity_bind hmod hμ hΔ]; exact ENNReal.one_ne_top)

omit [DecidableEq S] in
lemma integrable_toReal_avgDensity (Δ : Finset S) :
    Integrable (fun σ ↦ (avgDensity ρ μ Δ σ).toReal) (μ.bind (isssd ν Δ)) :=
  integrable_toReal_of_lintegral_ne_top
    ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl).aemeasurable
    (by rw [lintegral_avgDensity_bind hmod hμ Δ]; exact ENNReal.one_ne_top)

omit [DecidableEq S] in
lemma ae_lt_top_avgDensity (Δ : Finset S) :
    ∀ᵐ σ ∂(μ.bind (isssd ν Δ)), avgDensity ρ μ Δ σ < ⊤ :=
  ae_lt_top'
    ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl).aemeasurable
    (by rw [lintegral_avgDensity_bind hmod hμ Δ]; exact ENNReal.one_ne_top)

/-- **Georgii's `ρ_Δ^Λ = v(ρ_Δ | 𝓣_{Λ ∖ Δ})`.** -/
lemma condExp_ae_eq_condDensity {Δ Λ : Finset S} (hΔ : Δ ⊆ Λ) :
    (fun σ ↦ (condDensity ν ρ Δ Λ σ).toReal)
      =ᵐ[μ.bind (isssd ν Δ)] (μ.bind (isssd ν Δ))[fun σ ↦ (ρ Δ σ).toReal |
        cylinderEvents (((Λ \ Δ : Finset S) : Set S))ᶜ] := by
  have : IsProbabilityMeasure (μ.bind (isssd ν Δ)) :=
    isProbabilityMeasure_bind (isssd ν) Δ μ
  refine ae_eq_condExp_of_forall_setIntegral_eq cylinderEvents_le_pi
    (integrable_toReal_rho hmod hμ Δ)
    (fun A _ _ ↦ (integrable_toReal_condDensity hmod hμ hΔ).integrableOn) (fun A hA _ ↦ ?_) ?_
  · have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
    rw [integral_toReal
        ((measurable_condDensity hmod.measurable Δ Λ).mono cylinderEvents_le_pi
          le_rfl).aemeasurable.restrict
        (ae_restrict_of_ae (ae_lt_top_condDensity hmod hμ hΔ)),
      integral_toReal (hmod.measurable Δ).aemeasurable.restrict
        (ae_restrict_of_ae (ae_lt_top_rho hmod hμ Δ)),
      setLIntegral_condDensity_bind hmod hμ hΔ hA, setLIntegral_rho_bind hmod hμ Δ hA']
  · exact ((measurable_condDensity hmod.measurable Δ Λ).ennreal_toReal).stronglyMeasurable
      |>.aestronglyMeasurable

/-- **Georgii's `ρ̄_Δ = v(ρ_Δ | ⋂_n 𝓣_{Λ_n ∖ Δ})`.** -/
lemma condExp_iInf_ae_eq_avgDensity [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    (fun σ ↦ (avgDensity ρ μ Δ σ).toReal)
      =ᵐ[μ.bind (isssd ν Δ)] (μ.bind (isssd ν Δ))[fun σ ↦ (ρ Δ σ).toReal |
        ⨅ n, cylinderEvents (X := fun _ : S ↦ E) (((Λ n \ Δ : Finset S) : Set S))ᶜ] := by
  have hprob : IsProbabilityMeasure (μ.bind (isssd ν Δ)) :=
    isProbabilityMeasure_bind (isssd ν) Δ μ
  have hΔle : ∀ n : ℕ, cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)
      ≤ cylinderEvents (X := fun _ : S ↦ E) (((Λ n \ Δ : Finset S) : Set S))ᶜ := by
    intro n
    refine cylinderEvents_mono ?_
    intro i hi
    simp only [Finset.mem_coe] at hi
    simp only [Finset.coe_sdiff, Set.mem_compl_iff, Set.mem_sdiff, Finset.mem_coe, not_and,
      not_not]
    exact fun _ ↦ hi
  have hle : (⨅ n : ℕ, cylinderEvents (X := fun _ : S ↦ E)
      (((Λ n \ Δ : Finset S) : Set S))ᶜ) ≤ MeasurableSpace.pi :=
    le_trans (iInf_le _ 0) cylinderEvents_le_pi
  refine ae_eq_condExp_of_forall_setIntegral_eq hle (integrable_toReal_rho hmod hμ Δ)
    (fun A _ _ ↦ (integrable_toReal_avgDensity hmod hμ Δ).integrableOn) (fun A hA _ ↦ ?_) ?_
  · have hAn : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E)
        (((Λ n \ Δ : Finset S) : Set S))ᶜ] A :=
      fun n ↦ MeasurableSpace.measurableSet_iInf.1 hA n
    have hA' : MeasurableSet A := cylinderEvents_le_pi _ (hAn 0)
    rw [integral_toReal
        ((measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi
          le_rfl).aemeasurable.restrict
        (ae_restrict_of_ae (ae_lt_top_avgDensity hmod hμ Δ)),
      integral_toReal (hmod.measurable Δ).aemeasurable.restrict
        (ae_restrict_of_ae (ae_lt_top_rho hmod hμ Δ)),
      setLIntegral_avgDensity_bind hmod hμ htail hcof hAn, setLIntegral_rho_bind hmod hμ Δ hA']
  · exact (((measurable_avgDensity μ (hmod.measurable Δ)).mono (le_iInf hΔle)
      le_rfl).ennreal_toReal).stronglyMeasurable.aestronglyMeasurable

/-- **Georgii (7.12)(c), the martingale step**: along an increasing cofinal sequence of volumes the
densities `ρ_Δ^{Λ_n}` converge `v`-almost everywhere to `ρ̄_Δ`. -/
lemma ae_tendsto_toReal_condDensity [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) (hΔ : ∀ n, Δ ⊆ Λ n) :
    ∀ᵐ σ ∂(μ.bind (isssd ν Δ)),
      Tendsto (fun n ↦ (condDensity ν ρ Δ (Λ n) σ).toReal) atTop
        (𝓝 ((avgDensity ρ μ Δ σ).toReal)) := by
  have hprob : IsProbabilityMeasure (μ.bind (isssd ν Δ)) :=
    isProbabilityMeasure_bind (isssd ν) Δ μ
  have hanti : Antitone fun n : ℕ ↦ cylinderEvents (X := fun _ : S ↦ E)
      (((Λ n \ Δ : Finset S) : Set S))ᶜ := by
    intro m n hmn
    exact cylinderEvents_mono (Set.compl_subset_compl.2
      (Finset.coe_subset.2 (Finset.sdiff_subset_sdiff (hmono hmn) le_rfl)))
  have hlev := tendsto_ae_condExp_of_antitone (μ := μ.bind (isssd ν Δ))
    (fun σ ↦ (ρ Δ σ).toReal) hanti fun _ ↦ cylinderEvents_le_pi
  have hall : ∀ᵐ σ ∂(μ.bind (isssd ν Δ)), ∀ n : ℕ,
      (condDensity ν ρ Δ (Λ n) σ).toReal
        = ((μ.bind (isssd ν Δ))[fun σ ↦ (ρ Δ σ).toReal |
            cylinderEvents (X := fun _ : S ↦ E) (((Λ n \ Δ : Finset S) : Set S))ᶜ]) σ :=
    ae_all_iff.2 fun n ↦ condExp_ae_eq_condDensity hmod hμ (hΔ n)
  filter_upwards [hall, hlev, condExp_iInf_ae_eq_avgDensity hmod hμ htail hcof]
    with σ hσall hσlev hσavg
  simp only [hσall]
  rw [hσavg]
  exact hσlev

end Martingale

/-- The events of `Δ` are events outside `Λ ∖ Δ`. -/
lemma cylinderEvents_le_compl_sdiff (Δ Λ : Finset S) :
    cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)
      ≤ cylinderEvents (X := fun _ : S ↦ E) (((Λ \ Δ : Finset S) : Set S))ᶜ := by
  refine cylinderEvents_mono ?_
  intro i hi
  simp only [Finset.mem_coe] at hi
  simp only [Finset.coe_sdiff, Set.mem_compl_iff, Set.mem_sdiff, Finset.mem_coe, not_and, not_not]
  exact fun _ ↦ hi

section Uniform

variable (hmod : (isssd ν).IsModifier ρ) {μ : Measure (S → E)}
  (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ) [IsProbabilityMeasure μ]

include hmod hμ

/-- **Scheffé's step in Georgii's proof of (7.12)(c)**: for a fixed boundary condition `ω`, almost
everywhere convergence of the densities `ρ_Δ^{Λ_n}(· | ω)` to `ρ̄_Δ`, both of total mass `1`,
upgrades itself to `λ_Δ(|ρ_Δ^{Λ_n} - ρ̄_Δ| | ω) → 0`. -/
lemma tendsto_integral_abs_condDensity_sub_avgDensity {Δ : Finset S} {Λ : ℕ → Finset S}
    (hΔ : ∀ n, Δ ⊆ Λ n) (ω : S → E)
    (hae : ∀ᵐ σ ∂(isssd ν Δ ω), Tendsto (fun n ↦ (condDensity ν ρ Δ (Λ n) σ).toReal) atTop
      (𝓝 ((avgDensity ρ μ Δ σ).toReal))) :
    Tendsto (fun n ↦ ∫ σ, |(condDensity ν ρ Δ (Λ n) σ).toReal - (avgDensity ρ μ Δ σ).toReal|
      ∂(isssd ν Δ ω)) atTop (𝓝 0) := by
  set m : Measure (S → E) := isssd ν Δ ω with hm
  have hcm : ∀ n, Measurable (condDensity ν ρ Δ (Λ n)) := fun n ↦
    (measurable_condDensity hmod.measurable Δ (Λ n)).mono cylinderEvents_le_pi le_rfl
  have ham : Measurable (avgDensity ρ μ Δ) :=
    (measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl
  have hcn : ∀ n, ∫⁻ σ, condDensity ν ρ Δ (Λ n) σ ∂m = 1 := fun n ↦
    lintegral_condDensity hmod (hΔ n) ω
  have han : ∫⁻ σ, avgDensity ρ μ Δ σ ∂m = 1 := lintegral_avgDensity hmod hμ Δ ω
  have hcint : ∀ n, Integrable (fun σ ↦ (condDensity ν ρ Δ (Λ n) σ).toReal) m := fun n ↦
    integrable_toReal_of_lintegral_ne_top (hcm n).aemeasurable
      (by rw [hcn n]; exact ENNReal.one_ne_top)
  have haint : Integrable (fun σ ↦ (avgDensity ρ μ Δ σ).toReal) m :=
    integrable_toReal_of_lintegral_ne_top ham.aemeasurable
      (by rw [han]; exact ENNReal.one_ne_top)
  have hcI : ∀ n, ∫ σ, ‖(condDensity ν ρ Δ (Λ n) σ).toReal‖ ∂m = 1 := by
    intro n
    simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [integral_toReal (hcm n).aemeasurable
      (ae_lt_top' (hcm n).aemeasurable (by rw [hcn n]; exact ENNReal.one_ne_top)), hcn n]
    simp
  have haI : ∫ σ, ‖(avgDensity ρ μ Δ σ).toReal‖ ∂m = 1 := by
    simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [integral_toReal ham.aemeasurable
      (ae_lt_top' ham.aemeasurable (by rw [han]; exact ENNReal.one_ne_top)), han]
    simp
  have hnorm : Tendsto (fun n ↦ ∫ σ, ‖(condDensity ν ρ Δ (Λ n) σ).toReal‖ ∂m) atTop
      (𝓝 (∫ σ, ‖(avgDensity ρ μ Δ σ).toReal‖ ∂m)) := by
    simp only [hcI, haI]
    exact tendsto_const_nhds
  have := tendsto_integral_norm_sub_zero_of_tendsto_integral_norm
    (fun n ↦ (hcint n).1) hcint haint hnorm hae
  simpa only [Real.norm_eq_abs] using this

/-- **Georgii's bound in (7.12)(c)**: on the events of `Δ`, the finite-volume Gibbs distribution
and `μ` differ by at most `λ_Δ(|ρ_Δ^Λ - ρ̄_Δ| | ω)`. -/
lemma abs_toReal_modification_sub_le {Δ Λ' : Finset S} (hΔ : Δ ⊆ Λ') (ω : S → E)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents ((Δ : Finset S) : Set S)] A) :
    |((((isssd ν).modification ρ hmod) Λ' ω) A).toReal - (μ A).toReal|
      ≤ ∫ σ, |(condDensity ν ρ Δ Λ' σ).toReal - (avgDensity ρ μ Δ σ).toReal|
          ∂(isssd ν Δ ω) := by
  have hAΛ : MeasurableSet[cylinderEvents (((Λ' \ Δ : Finset S) : Set S))ᶜ] A :=
    cylinderEvents_le_compl_sdiff Δ Λ' _ hA
  have hA' : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hcm : Measurable (condDensity ν ρ Δ Λ') :=
    (measurable_condDensity hmod.measurable Δ Λ').mono cylinderEvents_le_pi le_rfl
  have ham : Measurable (avgDensity ρ μ Δ) :=
    (measurable_avgDensity μ (hmod.measurable Δ)).mono cylinderEvents_le_pi le_rfl
  have hcn : ∫⁻ σ, condDensity ν ρ Δ Λ' σ ∂(isssd ν Δ ω) = 1 := lintegral_condDensity hmod hΔ ω
  have han : ∫⁻ σ, avgDensity ρ μ Δ σ ∂(isssd ν Δ ω) = 1 := lintegral_avgDensity hmod hμ Δ ω
  have hcint : Integrable (fun σ ↦ (condDensity ν ρ Δ Λ' σ).toReal) (isssd ν Δ ω) :=
    integrable_toReal_of_lintegral_ne_top hcm.aemeasurable (by rw [hcn]; exact ENNReal.one_ne_top)
  have haint : Integrable (fun σ ↦ (avgDensity ρ μ Δ σ).toReal) (isssd ν Δ ω) :=
    integrable_toReal_of_lintegral_ne_top ham.aemeasurable (by rw [han]; exact ENNReal.one_ne_top)
  -- both masses are set integrals of the densities
  have hind : Measurable[cylinderEvents (((Λ' \ Δ : Finset S) : Set S))ᶜ]
      (A.indicator (1 : (S → E) → ℝ≥0∞)) := Measurable.indicator measurable_const hAΛ
  have hindΔ : Measurable[cylinderEvents ((Δ : Finset S) : Set S)]
      (A.indicator (1 : (S → E) → ℝ≥0∞)) := Measurable.indicator measurable_const hA
  have h1 : (((isssd ν).modification ρ hmod) Λ' ω) A
      = ∫⁻ σ in A, condDensity ν ρ Δ Λ' σ ∂(isssd ν Δ ω) := by
    have h := lintegral_modificationKer_isssd (ν := ν) (ρ := ρ) hmod.measurable hΔ hind ω
    rw [lintegral_indicator_one hA'] at h
    rw [show (fun σ ↦ condDensity ν ρ Δ Λ' σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
        = A.indicator (condDensity ν ρ Δ Λ') by
      funext σ; by_cases hσ : σ ∈ A <;> simp [hσ], lintegral_indicator hA'] at h
    exact h
  have h2 : μ A = ∫⁻ σ in A, avgDensity ρ μ Δ σ ∂(isssd ν Δ ω) := by
    have h := lintegral_avgDensity_mul hmod hμ hindΔ ω
    rw [lintegral_indicator_one hA'] at h
    rw [show (fun σ ↦ avgDensity ρ μ Δ σ * A.indicator (1 : (S → E) → ℝ≥0∞) σ)
        = A.indicator (avgDensity ρ μ Δ) by
      funext σ; by_cases hσ : σ ∈ A <;> simp [hσ], lintegral_indicator hA'] at h
    exact h.symm
  rw [h1, h2, ← integral_toReal hcm.aemeasurable.restrict
      (ae_restrict_of_ae (ae_lt_top' hcm.aemeasurable (by rw [hcn]; exact ENNReal.one_ne_top))),
    ← integral_toReal ham.aemeasurable.restrict
      (ae_restrict_of_ae (ae_lt_top' ham.aemeasurable (by rw [han]; exact ENNReal.one_ne_top))),
    ← integral_sub hcint.integrableOn haint.integrableOn]
  calc |∫ σ in A, ((condDensity ν ρ Δ Λ' σ).toReal - (avgDensity ρ μ Δ σ).toReal)
          ∂(isssd ν Δ ω)|
      ≤ ∫ σ in A, |(condDensity ν ρ Δ Λ' σ).toReal - (avgDensity ρ μ Δ σ).toReal|
          ∂(isssd ν Δ ω) := by
        simpa using abs_integral_le_integral_abs (μ := (isssd ν Δ ω).restrict A)
          (f := fun σ ↦ (condDensity ν ρ Δ Λ' σ).toReal - (avgDensity ρ μ Δ σ).toReal)
    _ ≤ ∫ σ, |(condDensity ν ρ Δ Λ' σ).toReal - (avgDensity ρ μ Δ σ).toReal|
          ∂(isssd ν Δ ω) :=
        setIntegral_le_integral (hcint.sub haint).abs
          (Eventually.of_forall fun _ ↦ abs_nonneg _)

/-- **Georgii, Theorem (7.12)(c)**, analytic form: for `μ`-almost every boundary condition `ω`,
the densities of the finite-volume Gibbs distributions relative to `λ_Δ` converge to `ρ̄_Δ` in
`L¹(λ_Δ(· | ω))`. -/
theorem ae_tendsto_integral_abs_condDensity_sub_avgDensity [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) (hΔ : ∀ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ σ,
        |(condDensity ν ρ Δ (Λ n) σ).toReal - (avgDensity ρ μ Δ σ).toReal| ∂(isssd ν Δ ω))
      atTop (𝓝 0) := by
  have hae := Measure.ae_ae_of_ae_bind
    (((isssd ν Δ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
    (ae_tendsto_toReal_condDensity hmod hμ htail hmono hcof hΔ)
  filter_upwards [hae] with ω hω
  exact tendsto_integral_abs_condDensity_sub_avgDensity hmod hμ hΔ ω hω

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)**: for a λ-specification and a tail-trivial Gibbs measure `μ`, the
finite-volume Gibbs distributions `γ_{Λ_n}(· | ω)` converge to `μ` **in total variation on every
finite volume `Δ`**, for `μ`-almost every boundary condition `ω`. -/
theorem ae_tendsto_iSup_ofReal_abs_sub [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) (hΔ : ∀ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal |((((isssd ν).modification ρ hmod) (Λ n) ω) A).toReal - (μ A).toReal|)
      atTop (𝓝 0) := by
  classical
  filter_upwards [ae_tendsto_integral_abs_condDensity_sub_avgDensity hmod hμ htail hmono hcof hΔ]
    with ω hω
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ ↦ (0 : ℝ≥0∞))
    (h := fun n ↦ ENNReal.ofReal (∫ σ,
      |(condDensity ν ρ Δ (Λ n) σ).toReal - (avgDensity ρ μ Δ σ).toReal| ∂(isssd ν Δ ω)))
    tendsto_const_nhds ?_ (fun _ ↦ bot_le) fun n ↦ ?_
  · have h := (ENNReal.continuous_ofReal.tendsto 0).comp hω
    simpa [Function.comp_def] using h
  · exact iSup_le fun A ↦ iSup_le fun hA ↦
      ENNReal.ofReal_le_ofReal (abs_toReal_modification_sub_le hmod hμ (hΔ n) ω hA)

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)**, without the hypothesis `Δ ⊆ Λ n` for *every* `n`. That
hypothesis forces `Δ ⊆ Λ 0`, which Georgii does not assume: cofinality and monotonicity already
give `Δ ⊆ Λ n` for all large `n`, and convergence along `atTop` does not see finitely many initial
terms. Obtained from `ae_tendsto_iSup_ofReal_abs_sub` by shifting the exhaustion. -/
theorem ae_tendsto_iSup_ofReal_abs_sub_of_cofinal [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal |((((isssd ν).modification ρ hmod) (Λ n) ω) A).toReal - (μ A).toReal|)
      atTop (𝓝 0) := by
  obtain ⟨n₀, hn₀⟩ := hcof Δ
  have hmono' : Monotone fun n ↦ Λ (n + n₀) := fun _ _ hab ↦ hmono (by omega)
  have hcof' : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ (n + n₀) := fun Θ ↦ by
    obtain ⟨m, hm⟩ := hcof Θ
    exact ⟨m, hm.trans (hmono (by omega))⟩
  have hΔ' : ∀ n, Δ ⊆ Λ (n + n₀) := fun n ↦ hn₀.trans (hmono (by omega))
  filter_upwards [ae_tendsto_iSup_ofReal_abs_sub hmod hμ htail (Λ := fun n ↦ Λ (n + n₀))
    hmono' hcof' hΔ'] with ω hω
  exact (Filter.tendsto_add_atTop_iff_nat n₀).1 hω

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)** as the book states it: one `μ`-full set of boundary conditions
`ω` works simultaneously for **every** finite volume `Δ`. The exceptional set of
`ae_tendsto_iSup_ofReal_abs_sub_of_cofinal` may depend on `Δ`; since `Finset S` is countable the
quantifiers may be swapped. -/
theorem ae_forall_tendsto_iSup_ofReal_abs_sub [Countable S]
    (htail : ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal |((((isssd ν).modification ρ hmod) (Λ n) ω) A).toReal - (μ A).toReal|)
      atTop (𝓝 0) :=
  ae_all_iff.2 fun Δ ↦
    ae_tendsto_iSup_ofReal_abs_sub_of_cofinal hmod hμ htail (Δ := Δ) hmono hcof

end Uniform

end Specification

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} {mE : MeasurableSpace E} [Countable S] [DecidableEq S]
  {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)** for an extreme Gibbs measure: for a λ-specification `γ = ρ λ`
and `μ ∈ ex 𝒢(γ)`, the finite-volume Gibbs distributions `γ_{Λ_n}(· | ω)` converge to `μ` in total
variation on every finite volume `Δ`, for `μ`-almost every boundary condition `ω`. -/
theorem ae_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G
    (hmod : (Specification.isssd ν).IsModifier ρ) {μ : Measure (S → E)}
    (hμ : μ ∈ (G ((Specification.isssd ν).modification ρ hmod)).extremePoints ℝ≥0∞)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) (hΔ : ∀ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal
          |((((Specification.isssd ν).modification ρ hmod) (Λ n) ω) A).toReal - (μ A).toReal|)
      Filter.atTop (nhds 0) := by
  classical
  have : IsProbabilityMeasure μ := hμ.1.1
  exact Specification.ae_tendsto_iSup_ofReal_abs_sub hmod hμ.1.2
    (tailTrivial_of_mem_extremePoints_G hμ) hmono hcof hΔ

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)** stated for a λ-specification `γ = ρ λ` in the sense of
Definition (1.27).  By Remark (1.28)(3), `Specification.lambdaSpecification_probNormalize`, this
covers every finite non-zero a priori measure. -/
theorem ae_tendsto_iSup_ofReal_abs_sub_lambdaSpecification
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : Measure (S → E)}
    (hμ : μ ∈ (G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)).extremePoints
      ℝ≥0∞)
    {Δ : Finset S} {Λ : ℕ → Finset S} (hmono : Monotone Λ)
    (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) (hΔ : ∀ n, Δ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal
          |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ (Λ n) ω) A).toReal
            - (μ A).toReal|)
      Filter.atTop (nhds 0) := by
  classical
  rw [Specification.lambdaSpecification_eq_modification_isssd (S := S) (E := E) ν hρ hZ] at hμ ⊢
  exact ae_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G _ hμ hmono hcof hΔ

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)** for an extreme Gibbs measure, as the book states it: a single
`μ`-full set of boundary conditions serves **every** finite volume `Δ` at once, and the exhaustion
is only required to be monotone and cofinal. -/
theorem ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G
    (hmod : (Specification.isssd ν).IsModifier ρ) {μ : Measure (S → E)}
    (hμ : μ ∈ (G ((Specification.isssd ν).modification ρ hmod)).extremePoints ℝ≥0∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Filter.Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal
          |((((Specification.isssd ν).modification ρ hmod) (Λ n) ω) A).toReal - (μ A).toReal|)
      Filter.atTop (nhds 0) := by
  classical
  have : IsProbabilityMeasure μ := hμ.1.1
  exact Specification.ae_forall_tendsto_iSup_ofReal_abs_sub hmod hμ.1.2
    (tailTrivial_of_mem_extremePoints_G hμ) hmono hcof

omit [DecidableEq S] in
/-- **Georgii, Theorem (7.12)(c)** for a λ-specification, with one `μ`-full set for all `Δ`. -/
theorem ae_forall_tendsto_iSup_ofReal_abs_sub_lambdaSpecification
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : Measure (S → E)}
    (hμ : μ ∈ (G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)).extremePoints
      ℝ≥0∞)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Filter.Tendsto (fun n ↦ ⨆ (A : Set (S → E))
        (_ : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ : Finset S) : Set S)] A),
        ENNReal.ofReal
          |((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ (Λ n) ω) A).toReal
            - (μ A).toReal|)
      Filter.atTop (nhds 0) := by
  classical
  rw [Specification.lambdaSpecification_eq_modification_isssd (S := S) (E := E) ν hρ hZ] at hμ ⊢
  exact ae_forall_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G _ hμ hmono hcof

end MeasureTheory.GibbsMeasure

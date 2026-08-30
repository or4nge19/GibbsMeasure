/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LocalLimits
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Georgii, Theorem (7.12)(c): local convergence in total variation

Work in progress.
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

/-- The `Λ = Δ` case of `lintegral_eq_lintegral_condDensity_mul`: `μ(f) = v(ρ_Δ f)` for *every*
bounded measurable `f`, where `v = μ λ_Δ`. -/
lemma lintegral_eq_lintegral_mul_bind (hmod : (isssd ν).IsModifier ρ)
    {μ : Measure (S → E)} (hμ : ((isssd ν).modification ρ hmod).IsGibbsMeasure μ)
    [IsProbabilityMeasure μ] (Δ : Finset S) {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂μ = ∫⁻ σ, ρ Δ σ * f σ ∂(μ.bind (isssd ν Δ)) := by
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
lemma measurable_juxt_boundary (Δ : Finset S) (ζ : Δ → E) :
    Measurable fun η : S → E ↦ juxt (Δ : Set S) η ζ := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ (Δ : Set S)
  · simp only [juxt_apply_of_mem hi]
    exact measurable_const
  · simp only [juxt_apply_of_not_mem hi]
    exact measurable_pi_apply i

omit [DecidableEq S] in
lemma restrict_juxt (Δ : Finset S) (η : S → E) (ζ : Δ → E) :
    Δ.restrict (juxt (Δ : Set S) η ζ) = ζ :=
  funext fun i ↦ juxt_apply_of_mem (by simp) ζ

omit [DecidableEq S] in
lemma lintegral_isssd_eq (Δ : Finset S) (τ : S → E) {g : (S → E) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ σ, g σ ∂(isssd ν Δ τ) =
      ∫⁻ ζ, g (juxt (Δ : Set S) τ ζ) ∂(Measure.pi fun _ : Δ ↦ ν) := by
  rw [show (isssd ν Δ τ) = Measure.map (juxt (Δ : Set S) τ) (Measure.pi fun _ : Δ ↦ ν) from rfl,
    lintegral_map hg Measurable.juxt]
  rfl

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
          ((hmod.measurable Δ).comp (measurable_juxt_boundary Δ ζ))).symm
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
        lintegral_congr fun ζ ↦ lintegral_const_mul _ (hg.comp (measurable_juxt_boundary Δ ζ))

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

include hmod hμ in
/-- `λ_Δ ρ̄_Δ = 1`, for every boundary condition. -/
lemma lintegral_avgDensity (Δ : Finset S) (ω : S → E) :
    ∫⁻ σ, avgDensity ρ μ Δ σ ∂(isssd ν Δ ω) = 1 := by
  have h := lintegral_avgDensity_mul hmod hμ (Δ := Δ) (f := fun _ ↦ 1) measurable_const ω
  simpa using h

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
    rw [h, lintegral_indicator_one ((measurable_juxt_boundary Δ ζ) hAm)]
  have hkey : ∀ ζ : Δ → E, avgKernel ρ μ Δ ζ *
      ∫⁻ ω, A.indicator (1 : (S → E) → ℝ≥0∞) (juxt (Δ : Set S) ω ζ) ∂μ
      = ∫⁻ η, ρ Δ (juxt (Δ : Set S) η ζ) * A.indicator 1 (juxt (Δ : Set S) η ζ) ∂μ := by
    intro ζ
    rw [hpre ζ]
    rcases hfib ζ with h0 | h1
    · rw [h0, mul_zero]
      refine ((lintegral_eq_zero_iff' ?_).2 ?_).symm
      · exact ((hmod.measurable Δ).comp (measurable_juxt_boundary Δ ζ)).aemeasurable.mul
          (hind.comp (measurable_juxt_boundary Δ ζ)).aemeasurable
      · have hnull : ∀ᵐ ω ∂μ, juxt (Δ : Set S) ω ζ ∉ A := by
          rw [ae_iff]
          simp only [not_not]
          show μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A) = 0
          exact h0
        filter_upwards [hnull] with ω hω
        simp [Set.indicator_of_notMem hω]
    · rw [h1, mul_one, avgKernel]
      refine lintegral_congr_ae ?_
      have h2 : μ ((fun ω : S → E ↦ juxt (Δ : Set S) ω ζ) ⁻¹' A)ᶜ = 0 := by
        rw [measure_compl ((measurable_juxt_boundary Δ ζ) hAm) (measure_ne_top _ _), h1,
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

end TailTrivial

end Specification

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification
public import GibbsMeasure.Specification.QuasilocalAlgebra
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Quasilocal specifications

Georgii's Definition (2.23): a specification is quasilocal if each `γ Λ` maps quasilocal observables
to quasilocal observables. No topology on `E` is involved.

## Main declarations

* `Specification.action`: `γ_Λ f = ∫ f ∂γ_Λ(·|·)` on bounded observables.
* `Specification.IsQuasilocal`: Georgii (2.23).
* `Specification.isQuasilocal_iff_forall_mem_localFunctions`: it suffices to check local observables.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace Specification

open GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {Λ : Finset S}
  {f : lp (fun _ : S → E ↦ ℝ) ∞}

/-- `(γ_Λ f)(η) = ∫ f ∂γ_Λ(·|η)`, on bounded observables. -/
def action (γ : Specification S E) (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞) :
    lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ ∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η), by
    refine memℓp_infty ⟨‖f‖, ?_⟩
    rintro _ ⟨η, rfl⟩
    have h : ‖∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η)‖ ≤ ‖f‖ * (γ Λ η).real univ :=
      norm_integral_le_of_norm_le_const
        (.of_forall fun x ↦ lp.norm_apply_le_norm_top f x)
    simpa using h⟩

@[simp] lemma action_apply (γ : Specification S E) (Λ : Finset S)
    (f : lp (fun _ : S → E ↦ ℝ) ∞) (η : S → E) :
    (action γ Λ f : (S → E) → ℝ) η = ∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η) := rfl

/-- `γ_Λ f` is measurable for the boundary σ-algebra `cylinderEvents Λᶜ`. -/
lemma action_mem_localFunctionsOn_compl (hf : Measurable (⇑f)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
      ((action γ Λ f : (S → E) → ℝ)) :=
  (StronglyMeasurable.integral_kernel (κ := γ Λ) hf.stronglyMeasurable).measurable

lemma measurable_action (hf : Measurable (⇑f)) : Measurable ((action γ Λ f : (S → E) → ℝ)) :=
  (action_mem_localFunctionsOn_compl (γ := γ) (Λ := Λ) hf).mono cylinderEvents_le_pi le_rfl

/-- A bounded measurable observable is integrable against a probability kernel. -/
private lemma integrable_of_measurable {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable (⇑f))
    (η : S → E) : Integrable (⇑f) (γ Λ η) :=
  Integrable.mono' (integrable_const ‖f‖) hf.aestronglyMeasurable
    (.of_forall fun x ↦ by simpa using lp.norm_apply_le_norm_top f x)

/-- The action is a contraction on measurable observables. -/
lemma dist_action_le {f g : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : Measurable (⇑f)) (hg : Measurable (⇑g)) :
    dist (action γ Λ f) (action γ Λ g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun η ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, action_apply, action_apply,
    ← integral_sub (integrable_of_measurable hf η) (integrable_of_measurable hg η)]
  have h : ‖∫ x, ((f : (S → E) → ℝ) x - (g : (S → E) → ℝ) x) ∂(γ Λ η)‖
      ≤ ‖f - g‖ * (γ Λ η).real univ := by
    refine norm_integral_le_of_norm_le_const (.of_forall fun x ↦ ?_)
    have := lp.norm_apply_le_norm_top (f - g) x
    rwa [lp.coeFn_sub, Pi.sub_apply] at this
  simpa using h


end Specification

namespace Specification
open GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}

lemma _root_.GibbsMeasure.mem_quasilocalFunctions_iff_mem_closure
    {f : lp (fun _ : S → E ↦ ℝ) ∞} :
    f ∈ quasilocalFunctions S E ↔ f ∈ closure (localFunctions S E : Set (lp (fun _ : S → E ↦ ℝ) ∞)) :=
  Iff.rfl

/-- **Georgii, Definition (2.23).** -/
def IsQuasilocal (γ : Specification S E) : Prop :=
  ∀ (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞),
    f ∈ quasilocalFunctions S E → action γ Λ f ∈ quasilocalFunctions S E

/-- Georgii's remark following (2.23): it suffices to check local observables. -/
theorem isQuasilocal_iff_forall_mem_localFunctions :
    γ.IsQuasilocal ↔ ∀ (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞),
      f ∈ localFunctions S E → action γ Λ f ∈ quasilocalFunctions S E := by
  refine ⟨fun h Λ f hf ↦ h Λ f (localFunctions_le_quasilocalFunctions hf), fun h Λ f hf ↦ ?_⟩
  have hclosed : IsClosed (quasilocalFunctions S E : Set (lp (fun _ : S → E ↦ ℝ) ∞)) :=
    Subalgebra.isClosed_topologicalClosure _
  have hfmeas : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  rw [← SetLike.mem_coe, ← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ :=
    Metric.mem_closure_iff.1 (GibbsMeasure.mem_quasilocalFunctions_iff_mem_closure.1 hf) ε hε
  have hgmeas : Measurable (⇑g) :=
    measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hg)
  exact ⟨action γ Λ g, h Λ g hg, lt_of_le_of_lt (dist_action_le hfmeas hgmeas) hfg⟩

/-! ### The independent specification, and modifications of it -/

section Isssd

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- Integrating out `Λ` against the independent kernel sends a `Δ`-local observable to a
`Δ \ Λ`-local one. -/
lemma dependsOn_action_isssd [DecidableEq S] {f : (S → E) → ℝ} (hfm : Measurable f)
    {Δ : Finset S} (hf : DependsOn f (Δ : Set S)) (Λ : Finset S) :
    DependsOn (fun η ↦ ∫ x, f x ∂(isssd ν Λ η)) (((Δ \ Λ : Finset S) : Set S)) := by
  intro η η' hηη'
  have hint : ∀ ξ : S → E, ∫ x, f x ∂(isssd ν Λ ξ)
      = ∫ ζ, f (juxt (Λ : Set S) ξ ζ) ∂(Measure.pi fun _ : (Λ : Set S) ↦ ν) := by
    intro ξ
    show ∫ x, f x ∂(Measure.map (juxt (Λ : Set S) ξ) (Measure.pi fun _ : (Λ : Set S) ↦ ν)) = _
    rw [integral_map (Measurable.juxt).aemeasurable hfm.aestronglyMeasurable]
  dsimp only
  rw [hint η, hint η']
  refine integral_congr_ae (.of_forall fun ζ ↦ hf fun i hi ↦ ?_)
  by_cases hiΛ : i ∈ Λ
  · simp [juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hiΛ)]
  · have hmem : i ∈ ((Δ \ Λ : Finset S) : Set S) := by
      simpa using Finset.mem_sdiff.2 ⟨by exact_mod_cast hi, hiΛ⟩
    simp [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (by exact_mod_cast hiΛ), hηη' i hmem]

/-- The independent specification maps `Δ`-local observables to `Δ \ Λ`-local ones. -/
theorem action_isssd_mem_localFunctionsOn [DecidableEq S] (Λ Δ : Finset S)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctionsOn S E Δ) :
    action (isssd ν) Λ f ∈ localFunctionsOn S E (Δ \ Λ) := by
  have hfm : Measurable (⇑f) := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn (⇑f) (Δ : Set S) :=
    (mem_localFunctionsOn.1 hf).dependsOn_of_cylinderEvents
  rw [mem_localFunctionsOn, measurable_cylinderEvents_iff_dependsOn]
  exact ⟨measurable_action (γ := isssd ν) hfm, dependsOn_action_isssd ν hfm hdep Λ⟩

/-- Georgii, after (2.23): every independent specification is quasilocal. -/
theorem isQuasilocal_isssd [DecidableEq S] :
    (isssd (S := S) (E := E) ν).IsQuasilocal := by
  refine isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦ ?_
  obtain ⟨Δ, hΔ⟩ := mem_localFunctions.1 hf
  exact localFunctions_le_quasilocalFunctions
    (mem_localFunctions.2 ⟨Δ \ Λ, action_isssd_mem_localFunctionsOn ν Λ Δ hΔ⟩)

end Isssd

/-! ### Georgii (2.24) -/

/-- **Georgii (2.24)(a).** A modification of a quasilocal specification by quasilocal densities is
quasilocal. -/
theorem IsQuasilocal.modification {γ : Specification S E} (hγ : γ.IsQuasilocal)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : γ.IsModifier ρ)
    {r : Finset S → lp (fun _ : S → E ↦ ℝ) ∞}
    (hr : ∀ Λ, r Λ ∈ quasilocalFunctions S E)
    (hrρ : ∀ Λ η, (⇑(r Λ)) η = (ρ Λ η).toReal)
    (hfin : ∀ Λ η, ρ Λ η ≠ ∞) :
    (γ.modification ρ hρ).IsQuasilocal := by
  refine isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦ ?_
  have key : action (γ.modification ρ hρ) Λ f = action γ Λ (r Λ * f) := by
    refine lp.ext (funext fun η ↦ ?_)
    have hmeas : Measurable fun x ↦ ((⇑(r Λ)) x).toNNReal :=
      (measurable_of_mem_quasilocalFunctions (hr Λ)).real_toNNReal
    have hden : ρ Λ = fun x ↦ ((((⇑(r Λ)) x).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      funext x
      rw [hrρ Λ x, ← ENNReal.ofReal, ENNReal.ofReal_toReal (hfin Λ x)]
    change ∫ x, (⇑f) x ∂((γ Λ η).withDensity (ρ Λ)) = _
    rw [hden, integral_withDensity_eq_integral_smul hmeas, action_apply]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change ((⇑(r Λ)) x).toNNReal • (⇑f) x = _
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by rw [hrρ Λ x]; exact ENNReal.toReal_nonneg),
      lp.infty_coeFn_mul]
    rfl
  rw [key]
  exact hγ Λ (r Λ * f) (Subalgebra.mul_mem _ (hr Λ) (localFunctions_le_quasilocalFunctions hf))

section Boltzmann

/-- The Boltzmann factor of a bounded observable. -/
noncomputable def boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ Real.exp (-(⇑H) η), memℓp_infty ⟨Real.exp ‖H‖, by
    rintro _ ⟨η, rfl⟩
    change ‖Real.exp (-(⇑H) η)‖ ≤ Real.exp ‖H‖
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (neg_le_abs _) (lp.norm_apply_le_norm_top H η))⟩⟩

@[simp] lemma coeFn_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) :
    ⇑(boltzmann H) = fun η ↦ Real.exp (-(⇑H) η) := rfl

lemma boltzmann_mem_quasilocalFunctions {H : lp (fun _ : S → E ↦ ℝ) ∞}
    (hH : H ∈ quasilocalFunctions S E) : boltzmann H ∈ quasilocalFunctions S E :=
  Subalgebra.comp_mem_lp (Subalgebra.isClosed_topologicalClosure _) hH
    (a := -‖H‖) (b := ‖H‖)
    (fun x ↦ abs_le.1 (le_trans (le_abs_self _) (by simpa using lp.norm_apply_le_norm_top H x)))
    (F := fun t ↦ Real.exp (-t)) (Real.continuous_exp.comp continuous_neg).continuousOn
    (fun _ ↦ rfl)

lemma le_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) (η : S → E) :
    Real.exp (-‖H‖) ≤ (⇑(boltzmann H)) η :=
  Real.exp_le_exp.2 (neg_le_neg (le_trans (le_abs_self _) (lp.norm_apply_le_norm_top H η)))

variable (ν : Measure E) [IsProbabilityMeasure ν]

lemma integrable_boltzmann {H : lp (fun _ : S → E ↦ ℝ) ∞} (hH : H ∈ quasilocalFunctions S E)
    (Λ : Finset S) (η : S → E) :
    Integrable (⇑(boltzmann H)) (isssd ν Λ η) := by
  have hpm := Specification.isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η
  exact Integrable.mono' (integrable_const ‖boltzmann H‖)
    (measurable_of_mem_quasilocalFunctions
      (boltzmann_mem_quasilocalFunctions hH)).aestronglyMeasurable
    (.of_forall fun x ↦ by simpa using lp.norm_apply_le_norm_top (boltzmann H) x)

lemma le_action_isssd_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞)
    (hH : H ∈ quasilocalFunctions S E) (Λ : Finset S) (η : S → E) :
    Real.exp (-‖H‖) ≤ (⇑(action (isssd ν) Λ (boltzmann H))) η := by
  have hpm := Specification.isProbabilityMeasure_isssdFun_apply (S := S) (E := E) ν Λ η
  rw [action_apply]
  calc Real.exp (-‖H‖)
      = ∫ _ : S → E, Real.exp (-‖H‖) ∂(isssd ν Λ η) := by
        rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ _ := integral_mono (integrable_const _) (integrable_boltzmann ν hH Λ η)
        fun x ↦ le_boltzmann H x

/-- **Georgii (2.24)(b).** If every Hamiltonian is a quasilocal observable, the Gibbsian
specification is quasilocal. -/
theorem isQuasilocal_modification_premodifierNorm [DecidableEq S]
    {H : Finset S → lp (fun _ : S → E ↦ ℝ) ∞} (hH : ∀ Λ, H Λ ∈ quasilocalFunctions S E)
    (hρ : (isssd ν).IsModifier
      (premodifierNorm ν fun Λ η ↦ ENNReal.ofReal ((⇑(boltzmann (H Λ))) η))) :
    ((isssd ν).modification _ hρ).IsQuasilocal := by
  set h : Finset S → lp (fun _ : S → E ↦ ℝ) ∞ := fun Λ ↦ boltzmann (H Λ) with hh
  set Z : Finset S → lp (fun _ : S → E ↦ ℝ) ∞ := fun Λ ↦ action (isssd ν) Λ (h Λ) with hZ
  have hZpos : ∀ Λ η, 0 < (⇑(Z Λ)) η := fun Λ η ↦
    lt_of_lt_of_le (Real.exp_pos _) (le_action_isssd_boltzmann ν (H Λ) (hH Λ) Λ η)
  have hZql : ∀ Λ, Z Λ ∈ quasilocalFunctions S E := fun Λ ↦
    isQuasilocal_isssd ν Λ _ (boltzmann_mem_quasilocalFunctions (hH Λ))
  have hZmem : ∀ Λ, (fun η ↦ ((⇑(Z Λ)) η)⁻¹) ∈ lp (fun _ : S → E ↦ ℝ) ∞ := fun Λ ↦
    memℓp_infty ⟨(Real.exp (-‖H Λ‖))⁻¹, by
      rintro _ ⟨η, rfl⟩
      change ‖((⇑(Z Λ)) η)⁻¹‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hZpos Λ η))]
      exact inv_anti₀ (Real.exp_pos _) (le_action_isssd_boltzmann ν (H Λ) (hH Λ) Λ η)⟩
  set W : Finset S → lp (fun _ : S → E ↦ ℝ) ∞ := fun Λ ↦ ⟨_, hZmem Λ⟩ with hW
  have hWql : ∀ Λ, W Λ ∈ quasilocalFunctions S E := fun Λ ↦
    Subalgebra.inv_mem_lp (Subalgebra.isClosed_topologicalClosure _) (hZql Λ)
      (Real.exp_pos (-‖H Λ‖)) (le_action_isssd_boltzmann ν (H Λ) (hH Λ) Λ) fun _ ↦ rfl
  have hZof : ∀ Λ η, premodifierZ ν (fun Λ η ↦ ENNReal.ofReal ((⇑(h Λ)) η)) Λ η
      = ENNReal.ofReal ((⇑(Z Λ)) η) := by
    intro Λ η
    rw [hZ, action_apply, premodifierZ,
      ofReal_integral_eq_lintegral_ofReal (integrable_boltzmann ν (hH Λ) Λ η)
        (.of_forall fun x ↦ le_of_lt (Real.exp_pos _))]
  refine (isQuasilocal_isssd ν).modification hρ (r := fun Λ ↦ h Λ * W Λ)
    (fun Λ ↦ Subalgebra.mul_mem _ (boltzmann_mem_quasilocalFunctions (hH Λ)) (hWql Λ))
    (fun Λ η ↦ ?_) (fun Λ η ↦ ?_)
  · have hmul : (⇑(h Λ * W Λ)) η = (⇑(h Λ)) η * ((⇑(Z Λ)) η)⁻¹ := by
      rw [lp.infty_coeFn_mul]; rfl
    rw [hmul, premodifierNorm, hZof Λ η, ← ENNReal.ofReal_div_of_pos (hZpos Λ η),
      ENNReal.toReal_ofReal (le_of_lt (div_pos
        (lt_of_lt_of_le (Real.exp_pos (-‖H Λ‖)) (le_boltzmann (H Λ) η)) (hZpos Λ η))),
      div_eq_mul_inv]
  · rw [premodifierNorm, hZof Λ η]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simpa using hZpos Λ η)

end Boltzmann



end Specification

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
open scoped ENNReal Topology

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

end Specification

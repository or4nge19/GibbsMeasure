/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification

/-!
# The Dirac reference specification

`Specification.zeroDirac S E` is the specification `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`: resampling `Λ`
puts the zero configuration there. It is the "otherwise" branch of Georgii's Gaussian
specification (13.18), glued to the Gaussian branch off the convergence set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Specification

variable (S E : Type*) [MeasurableSpace E] [Zero E]

/-- The raw kernel `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`: the Dirac mass at the configuration agreeing
with `ω` off `Λ` and vanishing on `Λ`. -/
noncomputable def zeroDiracFun (Λ : Finset S) :
    Kernel[cylinderEvents ((Λ : Set S)ᶜ)] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _ (fun ω ↦ Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)))
    (Measure.measurable_dirac.comp (measurable_cylinderEvents_juxt_boundary (0 : Λ → E)))

@[simp] lemma zeroDiracFun_apply (Λ : Finset S) (ω : S → E) :
    zeroDiracFun S E Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) := rfl

variable {S E}

lemma isMarkovKernel_zeroDiracFun (Λ : Finset S) : IsMarkovKernel (zeroDiracFun S E Λ) :=
  ⟨fun ω ↦ by rw [zeroDiracFun_apply]; infer_instance⟩

lemma isProper_zeroDiracFun (Λ : Finset S) : (zeroDiracFun S E Λ).IsProper :=
  Kernel.IsProper.of_inter_eq_indicator_mul cylinderEvents_le_pi fun A hA B hB ω ↦ by
    have hBmeas : MeasurableSet B := cylinderEvents_le_pi _ hB
    have hcongr : juxt (Λ : Set S) ω (0 : Λ → E) ∈ B ↔ ω ∈ B :=
      mem_congr_of_measurableSet_cylinderEvents hB fun i hi ↦ juxt_apply_of_not_mem hi 0
    rw [zeroDiracFun_apply, Measure.dirac_apply' _ (hA.inter hBmeas), Measure.dirac_apply' _ hA]
    by_cases hωB : ω ∈ B
    · have hjB : juxt (Λ : Set S) ω 0 ∈ B := hcongr.2 hωB
      by_cases hjA : juxt (Λ : Set S) ω 0 ∈ A
      · simp [Set.indicator_of_mem (Set.mem_inter hjA hjB), Set.indicator_of_mem hωB,
          Set.indicator_of_mem hjA]
      · simp [Set.indicator_of_notMem
          (fun hmem : juxt (Λ : Set S) ω 0 ∈ A ∩ B ↦ hjA hmem.1),
          Set.indicator_of_mem hωB, Set.indicator_of_notMem hjA]
    · have hjB : juxt (Λ : Set S) ω 0 ∉ B := fun hc ↦ hωB (hcongr.1 hc)
      simp [Set.indicator_of_notMem
        (fun hmem : juxt (Λ : Set S) ω 0 ∈ A ∩ B ↦ hjB hmem.2),
        Set.indicator_of_notMem hωB]

omit [MeasurableSpace E] in
/-- The identity `juxt Λ₁ (juxt Λ₂ ω 0) 0 = juxt Λ₂ ω 0` for `Λ₁ ⊆ Λ₂`: resampling to `0` on `Λ₂`
and then again on the smaller `Λ₁` changes nothing further. -/
lemma juxt_juxt_zero_of_subset {Λ₁ Λ₂ : Finset S} (h : Λ₁ ⊆ Λ₂) (ω : S → E) :
    juxt (Λ₁ : Set S) (juxt (Λ₂ : Set S) ω (0 : Λ₂ → E)) (0 : Λ₁ → E) =
      juxt (Λ₂ : Set S) ω (0 : Λ₂ → E) := by
  funext x
  by_cases hx1 : x ∈ (Λ₁ : Set S)
  · have hx2 : x ∈ (Λ₂ : Set S) := h hx1
    rw [juxt_apply_of_mem hx1, juxt_apply_of_mem hx2]
    rfl
  · rw [juxt_apply_of_not_mem hx1]

lemma isConsistent_zeroDiracFun : IsConsistent (zeroDiracFun S E) := by
  intro Λ₁ Λ₂ hΛ
  ext ω A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  have h1 : ∀ ζ : S → E, ((zeroDiracFun S E Λ₁).comap id cylinderEvents_le_pi) ζ A =
      zeroDiracFun S E Λ₁ ζ A := fun _ ↦ rfl
  simp only [h1]
  rw [zeroDiracFun_apply]
  have hfmeas : Measurable (fun ζ : S → E ↦ zeroDiracFun S E Λ₁ ζ A) :=
    (Kernel.measurable_coe (zeroDiracFun S E Λ₁) hA).mono cylinderEvents_le_pi le_rfl
  rw [lintegral_dirac' _ hfmeas, zeroDiracFun_apply, juxt_juxt_zero_of_subset hΛ]

variable (S E) in
/-- The raw family before bundling the Markov and properness hypotheses. -/
noncomputable def zeroDiracPre : PreSpecification S E where
  toFun := zeroDiracFun S E
  isConsistent' := isConsistent_zeroDiracFun

variable (S E) in
/-- **The Dirac reference specification**: `γ_Λ(·|ω) = δ_{0_Λ ω_{S∖Λ}}`. Georgii's "otherwise"
branch of Definition (13.18). -/
noncomputable def zeroDirac : Specification S E where
  toPreSpecification := zeroDiracPre S E
  isMarkovKernel' := isMarkovKernel_zeroDiracFun
  isProper' := isProper_zeroDiracFun

@[simp] lemma zeroDirac_apply (Λ : Finset S) (ω : S → E) :
    zeroDirac S E Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) := rfl

end Specification

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Stochastic domination

A measure `ν` **stochastically dominates** `μ` when every measurable upper set is at least as
likely under `ν` as under `μ`. This is the order under which monotone observables have monotone
expectations, and it is the form in which correlation inequalities such as Holley's are used.

## Main declarations

* `MeasureTheory.Measure.StochasticallyLE`.
* `MeasureTheory.Measure.StochasticallyLE.lintegral_ofReal_le`, and
  `MeasureTheory.Measure.StochasticallyLE.integral_le`: monotone observables are integrated
  monotonically.
* `MeasureTheory.Measure.StochasticallyLE.eq_of_forall_eq`: two stochastically comparable finite
  measures of the same total mass which agree on a family of measurable upper sets generating the
  σ-algebra are equal. This is the mechanism that turns "the plus and minus phases have the same
  single-site marginals" into "the plus and minus phases coincide", with no coupling theorem
  needed: the family of upper sets on which two comparable measures agree is closed under
  intersection, because `μ(A ∩ B) + μ(A ∪ B) = μ(A) + μ(B)`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [Preorder α] {μ ν : Measure α}

/-- `μ.StochasticallyLE ν`: every measurable upper set is at least as likely under `ν` as under
`μ`. -/
def StochasticallyLE (μ ν : Measure α) : Prop :=
  ∀ ⦃A : Set α⦄, MeasurableSet A → IsUpperSet A → μ A ≤ ν A

namespace StochasticallyLE

@[refl] protected lemma refl (μ : Measure α) : μ.StochasticallyLE μ := fun _ _ _ ↦ le_rfl

protected lemma rfl : μ.StochasticallyLE μ := .refl μ

protected lemma trans {ξ : Measure α} (h₁ : μ.StochasticallyLE ν) (h₂ : ν.StochasticallyLE ξ) :
    μ.StochasticallyLE ξ := fun _ hA hup ↦ (h₁ hA hup).trans (h₂ hA hup)

/-- On measurable **lower** sets the inequality is reversed, provided the two measures are finite
of the same total mass. -/
lemma ge_of_isLowerSet [IsFiniteMeasure μ] (h : μ.StochasticallyLE ν)
    (huniv : μ univ = ν univ) {A : Set α} (hA : MeasurableSet A) (hlow : IsLowerSet A) :
    ν A ≤ μ A := by
  have hνfin : IsFiniteMeasure ν := ⟨by rw [← huniv]; exact measure_lt_top _ _⟩
  have hcompl : μ Aᶜ ≤ ν Aᶜ := h hA.compl hlow.compl
  have hμ : μ A = μ univ - μ Aᶜ := by
    rw [measure_compl hA (measure_ne_top _ _),
      ENNReal.sub_sub_cancel (measure_ne_top _ _) (measure_mono (subset_univ _))]
  have hν : ν A = ν univ - ν Aᶜ := by
    rw [measure_compl hA (measure_ne_top _ _),
      ENNReal.sub_sub_cancel (measure_ne_top _ _) (measure_mono (subset_univ _))]
  rw [hμ, hν, ← huniv]
  exact tsub_le_tsub_left hcompl _

/-- Nonnegative monotone observables are integrated monotonically. -/
lemma lintegral_ofReal_le (h : μ.StochasticallyLE ν) {f : α → ℝ} (hf : Measurable f)
    (hmono : Monotone f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂ν := by
  have hnn : ∀ ξ : Measure α, (0 : α → ℝ) ≤ᵐ[ξ] fun a ↦ max (f a) 0 :=
    fun _ ↦ .of_forall fun _ ↦ le_max_right _ _
  have hmax : ∀ a, ENNReal.ofReal (f a) = ENNReal.ofReal (max (f a) 0) := fun a ↦ by
    rcases le_total (f a) 0 with hfa | hfa
    · simp [max_eq_right hfa, ENNReal.ofReal_eq_zero.2 hfa]
    · rw [max_eq_left hfa]
  simp only [hmax]
  rw [lintegral_eq_lintegral_meas_le μ (hnn μ) (hf.max measurable_const).aemeasurable,
    lintegral_eq_lintegral_meas_le ν (hnn ν) (hf.max measurable_const).aemeasurable]
  exact lintegral_mono fun t ↦ h (measurableSet_le measurable_const (hf.max measurable_const))
    fun a b hab hta ↦ le_trans hta (max_le_max (hmono hab) le_rfl)

/-- Monotone integrable observables are integrated monotonically. -/
lemma integral_le [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ.StochasticallyLE ν)
    (huniv : μ univ = ν univ) {f : α → ℝ} (hf : Measurable f) (hmono : Monotone f)
    (hμ : Integrable f μ) (hν : Integrable f ν) : ∫ a, f a ∂μ ≤ ∫ a, f a ∂ν := by
  have hpos : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂ν :=
    h.lintegral_ofReal_le hf hmono
  have hneg : ∫⁻ a, ENNReal.ofReal (-f a) ∂ν ≤ ∫⁻ a, ENNReal.ofReal (-f a) ∂μ := by
    have hnn : ∀ ξ : Measure α, (0 : α → ℝ) ≤ᵐ[ξ] fun a ↦ max (-f a) 0 :=
      fun _ ↦ .of_forall fun _ ↦ le_max_right _ _
    have hmax : ∀ a, ENNReal.ofReal (-f a) = ENNReal.ofReal (max (-f a) 0) := fun a ↦ by
      rcases le_total (-f a) 0 with hfa | hfa
      · simp [max_eq_right hfa, ENNReal.ofReal_eq_zero.2 hfa]
      · rw [max_eq_left hfa]
    simp only [hmax]
    rw [lintegral_eq_lintegral_meas_le μ (hnn μ) (hf.neg.max measurable_const).aemeasurable,
      lintegral_eq_lintegral_meas_le ν (hnn ν) (hf.neg.max measurable_const).aemeasurable]
    exact lintegral_mono fun t ↦ h.ge_of_isLowerSet huniv
      (measurableSet_le measurable_const (hf.neg.max measurable_const))
      fun a b hab hta ↦ le_trans hta (max_le_max (neg_le_neg (hmono hab)) le_rfl)
  have hfin : ∀ (ξ : Measure α) (g : α → ℝ), Integrable g ξ →
      ∫⁻ a, ENNReal.ofReal (g a) ∂ξ ≠ ∞ := by
    intro ξ g hg
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun a ↦ ?_) hg.2)
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hν]
  have h₁ : (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal ≤ (∫⁻ a, ENNReal.ofReal (f a) ∂ν).toReal :=
    ENNReal.toReal_mono (hfin ν f hν) hpos
  have h₂ : (∫⁻ a, ENNReal.ofReal (-f a) ∂ν).toReal ≤ (∫⁻ a, ENNReal.ofReal (-f a) ∂μ).toReal :=
    ENNReal.toReal_mono (hfin μ (fun a ↦ -f a) hμ.neg) hneg
  simpa using sub_le_sub h₁ h₂

/-- **Two comparable finite measures of the same mass agreeing on enough upper sets are equal.**
The family of measurable upper sets on which `μ` and `ν` agree is closed under intersection, hence
contains the π-system generated by `𝒢`; if `𝒢` generates the σ-algebra, `μ = ν`. -/
lemma eq_of_forall_eq [IsFiniteMeasure μ] (h : μ.StochasticallyLE ν) {𝒢 : Set (Set α)}
    (hmeas : ∀ A ∈ 𝒢, MeasurableSet A) (hup : ∀ A ∈ 𝒢, IsUpperSet A)
    (hgen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom 𝒢)
    (heq : ∀ A ∈ 𝒢, μ A = ν A) (huniv : μ univ = ν univ) : μ = ν := by
  have hν : IsFiniteMeasure ν := ⟨by rw [← huniv]; exact measure_lt_top _ _⟩
  have key : ∀ A ∈ generatePiSystem 𝒢,
      MeasurableSet A ∧ IsUpperSet A ∧ μ A = ν A := by
    intro A hA
    induction hA with
    | base hs => exact ⟨hmeas _ hs, hup _ hs, heq _ hs⟩
    | @inter s t _ _ _ ih₁ ih₂ =>
      obtain ⟨hm₁, hu₁, he₁⟩ := ih₁
      obtain ⟨hm₂, hu₂, he₂⟩ := ih₂
      refine ⟨hm₁.inter hm₂, hu₁.inter hu₂, ?_⟩
      have hsum : μ (s ∩ t) + μ (s ∪ t) = ν (s ∩ t) + ν (s ∪ t) := by
        rw [add_comm (μ (s ∩ t)), add_comm (ν (s ∩ t)),
          measure_union_add_inter (μ := μ) s hm₂, measure_union_add_inter (μ := ν) s hm₂,
          he₁, he₂]
      have hle₁ : μ (s ∩ t) ≤ ν (s ∩ t) := h (hm₁.inter hm₂) (hu₁.inter hu₂)
      have hle₂ : μ (s ∪ t) ≤ ν (s ∪ t) := h (hm₁.union hm₂) (hu₁.union hu₂)
      have hstep : ν (s ∩ t) + ν (s ∪ t) ≤ μ (s ∩ t) + ν (s ∪ t) := by
        rw [← hsum]
        exact add_le_add le_rfl hle₂
      exact le_antisymm hle₁
        ((ENNReal.add_le_add_iff_right (measure_ne_top ν (s ∪ t))).1 hstep)
  refine ext_of_generate_finite (generatePiSystem 𝒢) ?_
    (isPiSystem_generatePiSystem 𝒢) (fun A hA ↦ (key A hA).2.2) huniv
  rw [hgen, generateFrom_generatePiSystem_eq]

section Pi

variable {ι : Type*} {μ ν : Measure (ι → Bool)}

omit [MeasurableSpace α] [Preorder α] in
lemma measurableSet_setOf_eq_true (i : ι) :
    MeasurableSet {σ : ι → Bool | σ i = true} := by
  have h : MeasurableSet ((fun σ : ι → Bool ↦ σ i) ⁻¹' {true}) :=
    measurable_pi_apply i (measurableSet_singleton true)
  exact h

omit [MeasurableSpace α] [Preorder α] in
lemma isUpperSet_setOf_eq_true (i : ι) : IsUpperSet {σ : ι → Bool | σ i = true} := by
  intro σ τ hστ hσ
  simp only [Set.mem_ofPred_eq] at hσ ⊢
  have h1 := hστ i
  rw [hσ] at h1
  exact le_antisymm (by simp) h1

omit [MeasurableSpace α] [Preorder α] in
/-- The coordinate events `{σ | σ i = true}` generate the product σ-algebra on `ι → Bool`. -/
lemma generateFrom_setOf_eq_true :
    MeasurableSpace.generateFrom {A : Set (ι → Bool) | ∃ i, A = {σ | σ i = true}}
      = (inferInstance : MeasurableSpace (ι → Bool)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro A ⟨i, rfl⟩
    exact measurableSet_setOf_eq_true i
  · refine iSup_le fun i ↦ ?_
    rintro _ ⟨s, -, rfl⟩
    have hbase : MeasurableSet[MeasurableSpace.generateFrom
        {A : Set (ι → Bool) | ∃ i, A = {σ | σ i = true}}] {σ : ι → Bool | σ i = true} :=
      MeasurableSpace.measurableSet_generateFrom ⟨i, rfl⟩
    by_cases htrue : true ∈ s <;> by_cases hfalse : false ∈ s
    · have : (fun b : ι → Bool ↦ b i) ⁻¹' s = Set.univ := by
        ext σ; cases h : σ i <;> simp [Set.mem_preimage, h, htrue, hfalse]
      rw [this]
      exact @MeasurableSet.univ _ (MeasurableSpace.generateFrom
        {A : Set (ι → Bool) | ∃ i, A = {σ | σ i = true}})
    · have : (fun b : ι → Bool ↦ b i) ⁻¹' s = {σ : ι → Bool | σ i = true} := by
        ext σ; cases h : σ i <;> simp [Set.mem_preimage, h, htrue, hfalse]
      rw [this]; exact hbase
    · have : (fun b : ι → Bool ↦ b i) ⁻¹' s = {σ : ι → Bool | σ i = true}ᶜ := by
        ext σ; cases h : σ i <;> simp [Set.mem_preimage, h, htrue, hfalse]
      rw [this]; exact hbase.compl
    · have : (fun b : ι → Bool ↦ b i) ⁻¹' s = (∅ : Set (ι → Bool)) := by
        ext σ; cases h : σ i <;> simp [Set.mem_preimage, h, htrue, hfalse]
      rw [this]
      exact @MeasurableSet.empty _ (MeasurableSpace.generateFrom
        {A : Set (ι → Bool) | ∃ i, A = {σ | σ i = true}})

/-- **Two stochastically comparable probability measures on `ι → Bool` with the same single-site
marginals coincide.** -/
lemma eq_of_forall_apply_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : μ.StochasticallyLE ν) (heq : ∀ i, μ {σ | σ i = true} = ν {σ | σ i = true}) :
    μ = ν := by
  refine h.eq_of_forall_eq (𝒢 := {A : Set (ι → Bool) | ∃ i, A = {σ | σ i = true}}) ?_ ?_
    generateFrom_setOf_eq_true.symm ?_ (by simp)
  · rintro A ⟨i, rfl⟩
    exact measurableSet_setOf_eq_true i
  · rintro A ⟨i, rfl⟩
    exact isUpperSet_setOf_eq_true i
  · rintro A ⟨i, rfl⟩
    exact heq i

end Pi

end StochasticallyLE

end MeasureTheory.Measure

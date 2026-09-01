/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.Probability.ProductMeasure

/-!
# Measurability of the infinite product measure in its parameters

`Measure.infinitePi` is jointly measurable in the family of measures: if `a ↦ μ a i` is
measurable for every `i`, so is `a ↦ Measure.infinitePi (μ a)` for the Giry σ-algebra. In
particular the i.i.d. map `λ ↦ λ^ι` on probability measures is measurable, which makes mixtures
of product measures (de Finetti representations) expressible as `Measure.bind`.

The file also records the independence of complementary groups of coordinates under an infinite
product measure, `ProbabilityTheory.indep_cylinderEvents_compl_infinitePi`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α ι : Type*} [MeasurableSpace α] [Countable ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

omit [Countable ι] in
lemma infinitePi_of_not_forall_isProbabilityMeasure {μ : (i : ι) → Measure (X i)}
    (h : ¬ ∀ i, IsProbabilityMeasure (μ i)) : infinitePi μ = 0 := by
  classical
  rw [infinitePi]
  exact dif_neg h

/-- **Measurability of the product measure in its parameters.** If each coordinate measure
depends measurably on a parameter, so does the infinite product measure. -/
theorem measurable_infinitePi {μ : α → (i : ι) → Measure (X i)}
    (hμ : ∀ i, Measurable fun a ↦ μ a i) :
    Measurable fun a ↦ infinitePi (μ a) := by
  refine measurable_of_measurable_coe _ fun B hB ↦ ?_
  have hProb : MeasurableSet {a | ∀ i, IsProbabilityMeasure (μ a i)} := by
    have : {a | ∀ i, IsProbabilityMeasure (μ a i)} = ⋂ i, {a | μ a i univ = 1} := by
      ext a
      simp [isProbabilityMeasure_iff]
    rw [this]
    exact MeasurableSet.iInter fun i ↦
      ((measurableSet_singleton 1).preimage ((measurable_coe .univ).comp (hμ i)))
  -- reduce to the π-system of measurable boxes
  induction B, hB using MeasurableSpace.induction_on_inter
    (m := MeasurableSpace.pi) (s := squareCylinders fun i ↦ {s : Set (X i) | MeasurableSet s})
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun i ↦ fun _ h₁ _ h₂ _ ↦ h₁.inter h₂) fun i ↦ .univ) with
  | empty => simp only [measure_empty]; exact measurable_const
  | basic B hBmem =>
      obtain ⟨s, t, ht, rfl⟩ := hBmem
      have hval : (fun a ↦ infinitePi (μ a) ((s : Set ι).pi t))
          = {a | ∀ i, IsProbabilityMeasure (μ a i)}.indicator
              fun a ↦ ∏ i ∈ s, μ a i (t i) := by
        funext a
        by_cases ha : ∀ i, IsProbabilityMeasure (μ a i)
        · rw [Set.indicator_of_mem
            (show a ∈ {a | ∀ i, IsProbabilityMeasure (μ a i)} from ha),
            infinitePi_pi _ fun i _ ↦ ht i trivial]
        · rw [Set.indicator_of_notMem (show a ∉ {a | ∀ i, IsProbabilityMeasure (μ a i)} from ha),
            infinitePi_of_not_forall_isProbabilityMeasure ha]
          rfl
      rw [hval]
      exact Measurable.indicator
        (Finset.measurable_prod _ fun i _ ↦ (measurable_coe (ht i trivial)).comp (hμ i)) hProb
  | compl B hBm hB =>
      have hval : (fun a ↦ infinitePi (μ a) Bᶜ)
          = fun a ↦ infinitePi (μ a) univ - infinitePi (μ a) B := by
        funext a
        by_cases ha : ∀ i, IsProbabilityMeasure (μ a i)
        · have : IsProbabilityMeasure (infinitePi (μ a)) := inferInstance
          rw [measure_compl hBm (measure_ne_top _ _)]
        · rw [infinitePi_of_not_forall_isProbabilityMeasure ha]
          simp
      have huniv : Measurable fun a ↦ infinitePi (μ a) univ := by
        have h : (univ : Set (∀ i, X i)) = (↑(∅ : Finset ι) : Set ι).pi fun i ↦ univ := by simp
        have hbox : Measurable fun a ↦ infinitePi (μ a) ((↑(∅ : Finset ι) : Set ι).pi
            fun i ↦ (univ : Set (X i))) := by
          have hval : (fun a ↦ infinitePi (μ a) ((↑(∅ : Finset ι) : Set ι).pi
              fun i ↦ (univ : Set (X i))))
              = {a | ∀ i, IsProbabilityMeasure (μ a i)}.indicator fun _ ↦ 1 := by
            funext a
            by_cases ha : ∀ i, IsProbabilityMeasure (μ a i)
            · rw [Set.indicator_of_mem
              (show a ∈ {a | ∀ i, IsProbabilityMeasure (μ a i)} from ha),
              infinitePi_pi _ fun i _ ↦ .univ]
              simp
            · rw [Set.indicator_of_notMem
                  (show a ∉ {a | ∀ i, IsProbabilityMeasure (μ a i)} from ha),
                infinitePi_of_not_forall_isProbabilityMeasure ha]
              rfl
          rw [hval]
          exact measurable_const.indicator hProb
        simpa [← h] using hbox
      rw [hval]
      exact huniv.sub hB
  | iUnion f hdisj hfm hf =>
      have hval : (fun a ↦ infinitePi (μ a) (⋃ n, f n))
          = fun a ↦ ∑' n, infinitePi (μ a) (f n) := by
        funext a
        exact measure_iUnion hdisj hfm
      rw [hval]
      exact Measurable.tsum hf

/-- The i.i.d. map `λ ↦ λ^ι` is measurable for the Giry σ-algebra. -/
theorem measurable_infinitePi_const {E : Type*} [MeasurableSpace E] :
    Measurable fun lam : Measure E ↦ infinitePi (fun _ : ι ↦ lam) :=
  measurable_infinitePi fun _ ↦ measurable_id

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **An infinite product measure makes complementary groups of coordinates independent.**  For
any set `Δ` of indices, the σ-algebras `cylinderEvents Δ` and `cylinderEvents Δᶜ` generated by the
coordinates inside and outside `Δ` are independent under `⨂ i, μ i`.  The index type is
arbitrary: no countability is assumed. -/
theorem indep_cylinderEvents_compl_infinitePi (μ : (i : ι) → Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (Δ : Set ι) :
    Indep (cylinderEvents (X := X) Δ) (cylinderEvents (X := X) Δᶜ)
      (Measure.infinitePi μ) :=
  indep_biSup_compl (s := fun i ↦ MeasurableSpace.comap (fun σ : ∀ i, X i ↦ σ i) inferInstance)
    (fun i ↦ (measurable_pi_apply i).comap_le)
    ((iIndepFun_infinitePi (P := μ) (X := fun _ x ↦ x) (fun _ ↦ measurable_id)).iIndep) Δ

end ProbabilityTheory

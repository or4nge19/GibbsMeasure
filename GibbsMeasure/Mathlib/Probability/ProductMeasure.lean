/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Integral.Prod
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

section Resampling

/-! ### Resampling one coordinate of an infinite product measure

Georgii's Remark (1.25) uses the kernels `α_B` attached to a single-site probability measure `α`,
and the proof of Theorem (2.30) rests on the identity `α_{i} α_{S∖(C ∪ {i})} = α_{S∖C}` for
`i ∉ C`.  At the level of the product measure `α^S` this is the statement that resampling one
coordinate from an independent copy does not change the law. -/

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)}
variable (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Resampling a single coordinate of an infinite product of probability measures from an
independent copy leaves the law unchanged. -/
theorem map_update_prod_infinitePi (i : ι) :
    ((infinitePi μ).prod (μ i)).map (fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2)
      = infinitePi μ := by
  classical
  refine eq_infinitePi _ fun s t ht ↦ ?_
  rw [Measure.map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ ↦ ht _)]
  by_cases hi : i ∈ s
  · have hpre : (fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2) ⁻¹' ((s : Set ι).pi t)
        = ((↑(s.erase i) : Set ι).pi t) ×ˢ t i := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.coe_erase,
        Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro h
        refine ⟨fun j hj => ?_, ?_⟩
        · have := h j (by simpa using hj.1)
          rwa [Function.update_of_ne (by simpa using hj.2)] at this
        · have := h i hi
          rwa [Function.update_self] at this
      · rintro ⟨h1, h2⟩ j hj
        by_cases hji : j = i
        · subst hji; rwa [Function.update_self]
        · rw [Function.update_of_ne hji]
          exact h1 j ⟨hj, hji⟩
    rw [hpre, Measure.prod_prod, infinitePi_pi μ (fun j _ => ht j),
      ← Finset.prod_erase_mul s _ hi]
  · have hpre : (fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2) ⁻¹' ((s : Set ι).pi t)
        = ((s : Set ι).pi t) ×ˢ (Set.univ : Set (X i)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Set.mem_univ,
        and_true]
      constructor
      · intro h j hj
        have := h j hj
        rwa [Function.update_of_ne (by rintro rfl; exact hi hj)] at this
      · intro h j hj
        rw [Function.update_of_ne (by rintro rfl; exact hi hj)]
        exact h j hj
    rw [hpre, Measure.prod_prod, infinitePi_pi μ (fun j _ => ht j), measure_univ, mul_one]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Averaging over an infinite product of probability measures may be performed by first
resampling the `i`-th coordinate. -/
theorem integral_infinitePi_update (i : ι) {f : (Π j, X j) → G}
    (hf : Integrable f (infinitePi μ)) :
    ∫ ω, f ω ∂(infinitePi μ)
      = ∫ ω, (∫ e, f (Function.update ω i e) ∂(μ i)) ∂(infinitePi μ) := by
  have hmeas : Measurable (fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2) := by fun_prop
  have hmap := map_update_prod_infinitePi μ i
  have hint : Integrable (fun p : (Π j, X j) × X i ↦ f (Function.update p.1 i p.2))
      ((infinitePi μ).prod (μ i)) :=
    (integrable_map_measure (μ := (infinitePi μ).prod (μ i)) (g := f)
      (f := fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2)
      (by rw [hmap]; exact hf.aestronglyMeasurable) hmeas.aemeasurable).1
      (by rw [hmap]; exact hf)
  have h1 : ∫ ω, f ω ∂(infinitePi μ)
      = ∫ p, f (Function.update p.1 i p.2) ∂((infinitePi μ).prod (μ i)) := by
    conv_lhs => rw [← hmap]
    exact integral_map hmeas.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable)
  rw [h1, integral_prod _ hint]

/-- Averaging over an infinite product of probability measures may be performed by first
resampling the `i`-th coordinate; the resampled coordinate is integrated first. -/
theorem integral_infinitePi_update' (i : ι) {f : (Π j, X j) → G}
    (hf : Integrable f (infinitePi μ)) :
    ∫ ω, f ω ∂(infinitePi μ)
      = ∫ e, (∫ ω, f (Function.update ω i e) ∂(infinitePi μ)) ∂(μ i) := by
  have hmeas : Measurable (fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2) := by fun_prop
  have hmap := map_update_prod_infinitePi μ i
  have hint : Integrable (fun p : (Π j, X j) × X i ↦ f (Function.update p.1 i p.2))
      ((infinitePi μ).prod (μ i)) :=
    (integrable_map_measure (μ := (infinitePi μ).prod (μ i)) (g := f)
      (f := fun p : (Π j, X j) × X i ↦ Function.update p.1 i p.2)
      (by rw [hmap]; exact hf.aestronglyMeasurable) hmeas.aemeasurable).1
      (by rw [hmap]; exact hf)
  have h1 : ∫ ω, f ω ∂(infinitePi μ)
      = ∫ p, f (Function.update p.1 i p.2) ∂((infinitePi μ).prod (μ i)) := by
    conv_lhs => rw [← hmap]
    exact integral_map hmeas.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable)
  rw [h1, integral_prod_symm _ hint]

/-- If `F ω e` does not depend on the `i`-th coordinate of `ω`, then reading the second argument
off the `i`-th coordinate of `ω` has the same effect as averaging it independently. -/
theorem integral_infinitePi_eval_diag (i : ι) {F : (Π j, X j) → X i → G}
    (hF : ∀ ω e x, F (Function.update ω i x) e = F ω e)
    (hint : Integrable (fun ω ↦ F ω (ω i)) (infinitePi μ)) :
    ∫ ω, F ω (ω i) ∂(infinitePi μ) = ∫ ω, (∫ e, F ω e ∂(μ i)) ∂(infinitePi μ) := by
  rw [integral_infinitePi_update μ i hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun e ↦ ?_)
  simp only [Function.update_self]
  exact hF ω e e

/-- The version of `integral_infinitePi_eval_diag` with the independent average taken first. -/
theorem integral_infinitePi_eval_diag' (i : ι) {F : (Π j, X j) → X i → G}
    (hF : ∀ ω e x, F (Function.update ω i x) e = F ω e)
    (hint : Integrable (fun ω ↦ F ω (ω i)) (infinitePi μ)) :
    ∫ ω, F ω (ω i) ∂(infinitePi μ) = ∫ e, (∫ ω, F ω e ∂(infinitePi μ)) ∂(μ i) := by
  rw [integral_infinitePi_update' μ i hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e ↦ ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [Function.update_self]
  exact hF ω e e

omit [DecidableEq ι] in
/-- The `i`-th coordinate of an infinite product of probability measures is distributed
according to `μ i`. -/
theorem integral_infinitePi_eval (i : ι) {g : X i → G} (hg : AEStronglyMeasurable g (μ i)) :
    ∫ ω, g (ω i) ∂(infinitePi μ) = ∫ e, g e ∂(μ i) := by
  conv_rhs => rw [← infinitePi_map_eval μ i]
  exact (integral_map (measurable_pi_apply i).aemeasurable
    (by rwa [infinitePi_map_eval])).symm

end Resampling

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

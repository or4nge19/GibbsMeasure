module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

public section

open scoped ENNReal

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

/-- A family of probability measures on `.generateFrom t` is measurable as soon as `b ↦ μ b s` is
measurable for every `s` in the π-system `t`. -/
theorem measurable_of_isPiSystem_generateFrom
    (t : Set (Set α)) (μ : β → Measure[.generateFrom t] α)
    [∀ b, IsProbabilityMeasure (μ b)]
    (hpi : IsPiSystem t)
    (h : ∀ s ∈ t, Measurable fun b => μ b s) : Measurable μ := by
  let _ : MeasurableSpace α := MeasurableSpace.generateFrom t
  change Measurable (μ : β → Measure α)
  simpa using
    (Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (μ := μ) (S := t) (hgen := rfl) (hpi := hpi) (h_basic := h))

variable {mα : MeasurableSpace α} {s : Set α}

lemma measurable_restrict (hs : MeasurableSet s) : Measurable fun μ : Measure α ↦ μ.restrict s :=
  measurable_of_measurable_coe _ fun t ht ↦ by
    simp_rw [restrict_apply ht]; exact measurable_coe (ht.inter hs)

lemma measurable_setLIntegral {f : α → ℝ≥0∞} (hf : Measurable f) (hs : MeasurableSet s) :
    Measurable fun μ : Measure α ↦ ∫⁻ x in s, f x ∂μ :=
  (measurable_lintegral hf).comp (measurable_restrict hs)

lemma bind_add {β : Type*} {_ : MeasurableSpace β} (μ ν : Measure α) (f : α → Measure β)
    (hf : Measurable f) : (μ + ν).bind f = μ.bind f + ν.bind f := by
  ext s hs
  simp [Measure.bind_apply hs hf.aemeasurable, lintegral_add_measure]

end MeasureTheory.Measure

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

/-- Binding after pushing forward: `(g_* μ) ⋙ f = μ ⋙ (f ∘ g)`. -/
lemma bind_map {μ : Measure α} {g : α → β} {f : β → Measure γ} (hg : Measurable g)
    (hf : Measurable f) : (μ.map g).bind f = μ.bind (f ∘ g) := by
  rw [bind, bind, map_map hf hg]

/-- Pushing forward a bind: `g_* (μ ⋙ f) = μ ⋙ (g_* ∘ f)`. -/
lemma map_bind {μ : Measure α} {f : α → Measure β} {g : β → γ} (hf : Measurable f)
    (hg : Measurable g) : (μ.bind f).map g = μ.bind fun a ↦ (f a).map g := by
  ext s hs
  rw [map_apply hg hs, bind_apply (hg hs) hf.aemeasurable,
    bind_apply (f := fun a ↦ (f a).map g) hs ((measurable_map g hg).comp hf).aemeasurable]
  simp_rw [map_apply hg hs]

end MeasureTheory.Measure

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Binding a finite sum of measures. -/
lemma bind_finset_sum {ι : Type*} (s : Finset ι) (m : ι → Measure α) (f : α → Measure β)
    (hf : Measurable f) : (∑ i ∈ s, m i).bind f = ∑ i ∈ s, (m i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Measure.bind_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.bind_add _ _ _ hf, ih]

end MeasureTheory.Measure

namespace MeasureTheory

section WithDensityBind

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `withDensity` commutes with the Giry `bind`:
`(μ.bind κ).withDensity f = μ.bind fun a ↦ (κ a).withDensity f`.
Intended home: `Mathlib/MeasureTheory/Measure/WithDensity.lean`. -/
lemma Measure.withDensity_bind {μ : Measure α} {κ : α → Measure β} (hκ : Measurable κ)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.bind κ).withDensity f = μ.bind fun a ↦ (κ a).withDensity f := by
  have hκ' : Measurable fun a ↦ (κ a).withDensity f := by
    refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simp_rw [withDensity_apply _ hs, ← lintegral_indicator hs]
    exact (Measure.measurable_lintegral (hf.indicator hs)).comp hκ
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs,
    Measure.lintegral_bind hκ.aemeasurable (hf.indicator hs).aemeasurable,
    Measure.bind_apply hs hκ'.aemeasurable]
  exact lintegral_congr fun a ↦ by rw [withDensity_apply _ hs, lintegral_indicator hs]

end WithDensityBind

section BindAbsolutelyContinuous

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Absolute continuity passes to the Giry `bind`: if `μ ≪ ν` then `μ κ ≪ ν κ`.
Intended home: `Mathlib/MeasureTheory/Measure/GiryMonad.lean`. -/
lemma Measure.AbsolutelyContinuous.bind {μ ν : Measure α} {κ : α → Measure β}
    (h : μ ≪ ν) (hκ : Measurable κ) : μ.bind κ ≪ ν.bind κ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs h0 ↦ ?_
  have hm : Measurable fun a ↦ κ a s := (Measure.measurable_coe hs).comp hκ
  rw [Measure.bind_apply hs hκ.aemeasurable] at h0 ⊢
  exact (lintegral_eq_zero_iff hm).2 (h.ae_eq ((lintegral_eq_zero_iff hm).1 h0))

end BindAbsolutelyContinuous

end MeasureTheory

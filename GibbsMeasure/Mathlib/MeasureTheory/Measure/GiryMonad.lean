module

public import Mathlib.MeasureTheory.Measure.GiryMonad

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

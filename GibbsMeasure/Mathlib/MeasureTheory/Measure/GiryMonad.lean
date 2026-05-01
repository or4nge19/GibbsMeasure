module

public import Mathlib.MeasureTheory.Measure.GiryMonad

public section

open scoped ENNReal

namespace MeasureTheory.Measure
variable {α β : Type*} [MeasurableSpace β]

/--
Measurability of `μ : β → Measure[.generateFrom t] α` when each `μ b` is a probability measure,
assuming `t` is a π-system generating the σ-algebra on `α`.

Without `IsPiSystem t`, the naive “generateFrom induction” predicate is not closed under
intersections, so this π-system hypothesis is genuinely needed.
-/
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

end MeasureTheory.Measure

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

/-- Two-sided version of `MeasureTheory.Measure.ae_ae_of_ae_bind`. -/
theorem ae_bind_iff {β : Type*} {mβ : MeasurableSpace β} {m : Measure α} {f : α → Measure β}
    (hf : Measurable f) {p : β → Prop} (hp : MeasurableSet {b | p b}) :
    (∀ᵐ b ∂m.bind f, p b) ↔ ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b := by
  have hpc : MeasurableSet {b | ¬ p b} := by
    simpa [Set.compl_setOf] using hp.compl
  have hmeas : Measurable fun a ↦ f a {b | ¬ p b} := (measurable_coe hpc).comp hf
  rw [ae_iff, bind_apply hpc hf.aemeasurable, lintegral_eq_zero_iff hmeas]
  simp only [Filter.EventuallyEq, Pi.zero_apply, ae_iff]

end MeasureTheory.Measure

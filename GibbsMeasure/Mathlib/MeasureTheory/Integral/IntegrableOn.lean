module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn

open ENNReal MeasureTheory Integrable

attribute [fun_prop] MeasureTheory.IntegrableOn

namespace MeasureTheory

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {g : α → ℝ≥0∞}

@[fun_prop]
public lemma integrableOn_toReal {s : Set α} (hm : m ≤ m0) (hgm : AEStronglyMeasurable[m] g μ)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hs : MeasurableSet[m] s) (hμs : μ s < ∞) :
    IntegrableOn (fun x ↦ (g x).toReal) s μ := by
  simpa [IntegrableOn] using
    integrable_toReal_of_lintegral_ne_top (μ := μ.restrict s)
      ((hgm.mono hm).aemeasurable.restrict) (hg_int_finite s hs hμs)

end MeasureTheory

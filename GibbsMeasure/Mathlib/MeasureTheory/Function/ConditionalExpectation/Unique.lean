module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique
public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Trim

public section

open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure[m0] α}

/-! **Uniqueness from equality of set Lebesgue integrals on a sub-σ-algebra** -/

theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hfg_eq : ∀ s, @MeasurableSet α m s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  have hfm' : StronglyMeasurable[m] (hfm.mk f) := hfm.stronglyMeasurable_mk
  have hgm' : StronglyMeasurable[m] (hgm.mk g) := hgm.stronglyMeasurable_mk
  have hfg_mk :
      ∀ s, @MeasurableSet α m s → μ s < ∞ →
        ∫⁻ x in s, hfm.mk f x ∂μ = ∫⁻ x in s, hgm.mk g x ∂μ := by
    intro s hs hμs
    rw [← setLIntegral_congr_fun_ae (hm s hs)
          (hfm.ae_eq_mk.symm.mono fun _ hx _ => hx.symm),
      ← setLIntegral_congr_fun_ae (hm s hs)
          (hgm.ae_eq_mk.symm.mono fun _ hx _ => hx.symm)]
    exact hfg_eq s hs hμs
  have hae_mk : hfm.mk f =ᵐ[μ.trim hm] hgm.mk g := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hfm'.measurable hgm'.measurable
      fun s hs hμs ↦ ?_
    rw [setLIntegral_trim hm hfm'.measurable hs, setLIntegral_trim hm hgm'.measurable hs]
    exact hfg_mk s hs (by rwa [← trim_measurableSet_eq hm hs])
  exact hfm.ae_eq_mk.trans ((ae_eq_of_ae_eq_trim (hm := hm) hae_mk).trans hgm.ae_eq_mk.symm)

end MeasureTheory

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

public section

open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

section

/-- If `f` and `g` have matching lower integrals on every `m`-measurable set of finite `μ`-measure,
then the same holds after replacing `f` and `g` by any functions a.e. equal to them. -/
lemma forall_setLIntegral_eq_of_forall_setLIntegral_eq_of_ae
    (hm : m ≤ m0) {f g f' g' : α → ℝ≥0∞}
    (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g')
    (hfg :
      ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f' x ∂μ = ∫⁻ x in s, g' x ∂μ := by
  intro s hs hμs
  calc
    ∫⁻ x in s, f' x ∂μ = ∫⁻ x in s, f x ∂μ := by
      refine setLIntegral_congr_fun_ae (μ := μ) (f := f') (g := f) (hm s hs) ?_
      exact hf.symm.mono fun _ hx _ => hx
    _ = ∫⁻ x in s, g x ∂μ := hfg s hs hμs
    _ = ∫⁻ x in s, g' x ∂μ := by
      refine setLIntegral_congr_fun_ae (μ := μ) (f := g) (g := g') (hm s hs) ?_
      exact hg.mono fun _ hx _ => hx

/-- For `m`-measurable `f`, the lower integral on `s` against `μ.trim hm` agrees with that against
`μ`. -/
lemma setLIntegral_trim_eq_setLIntegral (hm : m ≤ m0) {f : α → ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet[m] s) (hf : Measurable[m] f) :
    ∫⁻ x in s, f x ∂μ.trim hm = ∫⁻ x in s, f x ∂μ := by
  rw [restrict_trim (μ := μ) hm hs]
  simpa using lintegral_trim (μ := μ.restrict s) hm hf

/-- From equality of lower integrals on finite-measure `m`-sets for `μ`, deduce the same for
`μ.trim hm` when the integrands are `m`-measurable. -/
lemma forall_setLIntegral_trim_eq_of_forall_setLIntegral_eq_of_measurable
    (hm : m ≤ m0) {f g : α → ℝ≥0∞} (hf : Measurable[m] f) (hg : Measurable[m] g)
    (hfg :
      ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
    ∀ s, MeasurableSet[m] s → (μ.trim hm) s < ∞ →
      ∫⁻ x in s, f x ∂μ.trim hm = ∫⁻ x in s, g x ∂μ.trim hm := by
  intro s hs hμs_trim
  calc
    ∫⁻ x in s, f x ∂μ.trim hm = ∫⁻ x in s, f x ∂μ := setLIntegral_trim_eq_setLIntegral hm hs hf
    _ = ∫⁻ x in s, g x ∂μ := hfg s hs <| by
      simpa [trim_measurableSet_eq hm hs] using hμs_trim
    _ = ∫⁻ x in s, g x ∂μ.trim hm := (setLIntegral_trim_eq_setLIntegral hm hs hg).symm

end

/-!
## Uniqueness on the ambient measure

This records a variant of `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite` where the
hypothesis is stated using `μ` on `m`-measurable sets of finite `μ`-measure, rather than
`μ.trim hm` on sets of finite `μ.trim hm`-measure.
-/

/-- Two a.e. strongly measurable `ℝ≥0∞` functions that have matching lower integrals on every
`m`-measurable set of finite `μ`-measure are equal `μ`-a.e.

This relaxes the finiteness hypothesis from `μ.trim hm` (as in
`ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`) to `μ`, assuming `SigmaFinite (μ.trim hm)`. -/
theorem ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite' (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {f g : α → ℝ≥0∞}
    (hfg_eq : ∀ s, MeasurableSet[m] s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ)
    (hfm : AEStronglyMeasurable[m] f μ) (hgm : AEStronglyMeasurable[m] g μ) : f =ᵐ[μ] g := by
  set f0 : α → ℝ≥0∞ := hfm.mk f
  set g0 : α → ℝ≥0∞ := hgm.mk g
  have hfg0_trim : f0 =ᵐ[μ.trim hm] g0 :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := μ.trim hm) (f := f0) (g := g0)
      (by simpa [f0] using hfm.measurable_mk)
      (by simpa [g0] using hgm.measurable_mk)
      (forall_setLIntegral_trim_eq_of_forall_setLIntegral_eq_of_measurable hm
        (by simpa [f0] using hfm.measurable_mk)
        (by simpa [g0] using hgm.measurable_mk)
        (forall_setLIntegral_eq_of_forall_setLIntegral_eq_of_ae hm
          (by simpa [f0] using hfm.ae_eq_mk)
          (by simpa [g0] using hgm.ae_eq_mk)
          hfg_eq))
  simpa [f0, g0] using
    hfm.ae_eq_mk.trans ((ae_eq_of_ae_eq_trim (hm := hm) hfg0_trim).trans hgm.ae_eq_mk.symm)

end MeasureTheory

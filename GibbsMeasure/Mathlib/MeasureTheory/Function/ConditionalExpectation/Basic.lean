module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

open scoped ENNReal MeasureTheory

namespace MeasureTheory
variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

section Indicator
variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Set integral of `s.indicator (fun _ ↦ c)` over `t`
is `μ.real (s ∩ t) • c`. -/
lemma setIntegral_indicator_const
    (hs : MeasurableSet s) (t : Set α) (c : E) :
    ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ = μ.real (s ∩ t) • c := by
  rw [integral_indicator_const (μ := μ.restrict t) (s := s) (e := c) (s_meas := hs)]
  rw [measureReal_restrict_apply, Set.inter_comm]
  aesop

/-- Specialization: real-valued constant `1`. -/
lemma setIntegral_indicator_one
    (hs : MeasurableSet s) (t : Set α) :
    ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ = μ.real (s ∩ t) := by
  simp only [integral_indicator_const, measureReal_restrict_apply, smul_eq_mul, mul_one, hs]

end Indicator

section IndicatorIntegrable
variable {E : Type*} [NormedAddCommGroup E]

/-- The indicator of a constant over a measurable set of finite measure is integrable. -/
lemma integrable_indicator_const_of_measure_ne_top
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    Integrable (s.indicator (fun _ : α ↦ c)) μ := by
  refine (integrable_indicator_iff hs).2 ?_
  haveI : IsFiniteMeasure (μ.restrict s) := ⟨by
    simpa only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] using
      measure_lt_top_of_subset (by intro x hx; exact hx : s ⊆ s) hμs⟩
  change Integrable (fun _ : α ↦ c) (μ.restrict s)
  exact integrable_const c

end IndicatorIntegrable

section ENNReal

/-- If the lintegral of `f` is finite, then the integral of `f.toReal` is the `toReal` of the
lintegral. -/
lemma integral_toReal_of_lintegral_ne_top {α} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (h_fin : (∫⁻ a, f a ∂μ) ≠ ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  simpa using integral_toReal hf_meas (ae_lt_top' hf_meas h_fin)

/-- If the lintegral of `f` on `t` is finite, then `f.toReal` is integrable on `t`. -/
lemma integrableOn_toReal_of_lintegral_ne_top {α} {m : MeasurableSpace α} {μ : Measure α}
    {f : α → ℝ≥0∞} {t : Set α} (hf_meas : AEMeasurable f (μ.restrict t))
    (h_fin : ∫⁻ a in t, f a ∂μ ≠ ∞) :
    IntegrableOn (fun a ↦ (f a).toReal) t μ := by
  simpa [IntegrableOn] using
    (integrable_toReal_of_lintegral_ne_top (μ := μ.restrict t) hf_meas h_fin)

namespace AEStronglyMeasurable

/-- Composing an `AEStronglyMeasurable` `ℝ≥0∞`-valued function with `ENNReal.toReal` preserves
`AEStronglyMeasurable`. -/
lemma ennreal_toReal {α} {m m0 : MeasurableSpace α} {μ : Measure[m0] α} {g : α → ℝ≥0∞}
    (hgm : AEStronglyMeasurable[m] g μ) :
    AEStronglyMeasurable[m] (fun a ↦ (g a).toReal) μ := by
  exact hgm.stronglyMeasurable_mk.measurable.ennreal_toReal.aestronglyMeasurable.congr
    (hgm.ae_eq_mk.fun_comp ENNReal.toReal).symm

end AEStronglyMeasurable

/-- If the lintegral of `g` over `m`-measurable finite-measure sets matches `μ (s ∩ t)`, then the
set integral of `g.toReal` over such a set is `μ.real (s ∩ t)`. -/
lemma setIntegral_toReal_eq_measureReal_inter_of_forall_setLIntegral_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s t : Set α}
    (ht : MeasurableSet[m] t) (hμt : μ t < ∞)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
    (hgm : AEStronglyMeasurable[m] g μ) :
    ∫ x in t, (g x).toReal ∂μ = μ.real (s ∩ t) := by
  calc
    ∫ x in t, (g x).toReal ∂μ = (∫⁻ a in t, g a ∂μ).toReal := by
      simpa using
        (integral_toReal_of_lintegral_ne_top (μ := μ.restrict t)
          ((hgm.mono hm).aemeasurable.restrict) (hg_int_finite t ht hμt))
    _ = μ.real (s ∩ t) := by
      simpa [measureReal_def] using congrArg ENNReal.toReal (hg_eq t ht hμt)

/-- If `g.toReal` is a.e. the conditional expectation of `s.indicator 1`, then the lintegral of
`g` over any `m`-measurable set `t` is `μ (s ∩ t)`. -/
lemma measure_inter_eq_setLIntegral_of_toReal_ae_eq_indicator_condExp (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s t : Set α} (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) (ht : MeasurableSet[m] t) (hgm : AEStronglyMeasurable[m] g μ)
    (hg_fin : ∀ᵐ a ∂μ, g a ≠ ∞)
    (h_eq : (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1 | m]) :
    μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  have h_fin_lintegral_g : ∫⁻ a in t, g a ∂μ ≠ ⊤ :=
    ((integrable_toReal_iff (μ := μ.restrict t) ((hgm.mono hm).aemeasurable.restrict))
      (ae_restrict_of_ae hg_fin)).1 <| by
        simpa [IntegrableOn] using
          (integrable_condExp.integrableOn.congr (Filter.EventuallyEq.restrict h_eq).symm :
            IntegrableOn (fun a ↦ (g a).toReal) t μ)
  have := congrArg ENNReal.ofReal <| calc
    (∫⁻ a in t, g a ∂μ).toReal = ∫ x in t, (g x).toReal ∂μ := by
      symm
      simpa using
        (integral_toReal_of_lintegral_ne_top (μ := μ.restrict t)
          ((hgm.mono hm).aemeasurable.restrict) h_fin_lintegral_g)
    _ = ∫ x in t, (μ[s.indicator 1|m]) x ∂μ := by
      simpa using (integral_congr_ae (μ := μ.restrict t) (Filter.EventuallyEq.restrict h_eq))
    _ = ∫ x in t, s.indicator (fun _ : α ↦ (1 : ℝ)) x ∂μ := by
      simpa using
        (setIntegral_condExp (m := m) (m₀ := m0) (μ := μ)
          (f := s.indicator (fun _ : α ↦ (1 : ℝ))) hm
          (by
            simpa using
              (integrable_indicator_const_of_measure_ne_top
                (μ := μ) (s := s) (E := ℝ) (hm s hs) hμs (1 : ℝ)))
          ht)
    _ = μ.real (s ∩ t) := setIntegral_indicator_one (μ := μ) (s := s) (hm s hs) t
  simpa [measureReal_def, ENNReal.ofReal_toReal h_fin_lintegral_g,
    ENNReal.ofReal_toReal
      ((measure_lt_top_of_subset (Set.inter_subset_left : s ∩ t ⊆ s) hμs).ne)] using this.symm

/-- Uniqueness for the specific target `ℝ` given a nonnegative function `g : α → ℝ≥0∞` whose
lintegrals over `m`-measurable sets match `μ (s ∩ t)`. -/
theorem toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
  [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
  (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞)
  (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
  (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t))
  (hgm : AEStronglyMeasurable[m] g μ) :
  (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  refine ae_eq_condExp_of_forall_setIntegral_eq (m := m) (m₀ := m0) (μ := μ)
    (f := s.indicator fun _ : α => (1 : ℝ))
    hm ?_ ?_ ?_ ?_
  · simpa using
      (integrable_indicator_const_of_measure_ne_top
        (μ := μ) (s := s) (E := ℝ) (hm s hs) hμs (1 : ℝ))
  · intro t ht hμt
    simpa using
      (integrableOn_toReal_of_lintegral_ne_top
        (μ := μ) (t := t) (((hgm.mono hm).aemeasurable).restrict) (hg_int_finite t ht hμt))
  · intro t ht hμt
    simpa [setIntegral_indicator_one (μ := μ) (s := s) (hm s hs) t] using
      (setIntegral_toReal_eq_measureReal_inter_of_forall_setLIntegral_eq
        (m := m) (m0 := m0) (μ := μ) (g := g) (s := s) (t := t)
        hm ht hμt hg_int_finite hg_eq hgm)
  · exact AEStronglyMeasurable.ennreal_toReal hgm

/-- Characterization: `g.toReal` equals the conditional expectation of the indicator constant
iff the lintegral of `g` over every `m`-measurable set `t` equals `μ (s ∩ t)`.
We require the natural additional hypothesis that `g ≠ ∞` a.e. (equivalently, `g < ∞` a.e.) so
that these lintegrals are finite. -/
lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
  [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
  (hs : MeasurableSet[m] s) (hμs : μ s ≠ ∞)
  (hgm : AEStronglyMeasurable[m] g μ)
  (hg_fin : ∀ᵐ a ∂μ, g a ≠ ∞) :
  (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1| m] ↔
    ∀ t, MeasurableSet[m] t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  constructor
  · intro h_eq t ht
    exact measure_inter_eq_setLIntegral_of_toReal_ae_eq_indicator_condExp
      (m := m) (m0 := m0) (μ := μ) (g := g) (s := s) (t := t)
      hm hs hμs ht hgm hg_fin h_eq
  · intro h_eq
    refine
      toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq
        (m := m) (m0 := m0) (μ := μ) (g := g) (s := s)
        hm hs hμs
        ?hg_int_finite ?hg_eq hgm
    · intro t ht hμt
      simpa [(h_eq t ht).symm] using
        (measure_lt_top_of_subset (Set.inter_subset_right : s ∩ t ⊆ t) hμt.ne).ne
    · intro t ht _hμt
      simpa using (h_eq t ht).symm

end ENNReal
end MeasureTheory

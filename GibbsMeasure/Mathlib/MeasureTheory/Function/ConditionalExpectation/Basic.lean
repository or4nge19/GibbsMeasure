module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real

public section

open scoped ENNReal
open Classical
open Set

namespace MeasureTheory
variable {α F F' 𝕜 : Type*} {p : ℝ≥0∞} [RCLike 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F'] [CompleteSpace F']
  {m m0 : MeasurableSpace α} {μ : Measure[m0] α} {f g : α → F'} {s : Set α}

--TODO : Generalise to SigmaFinite (μ.trim hm) ?
variable [IsFiniteMeasure μ]

section AuxReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Set integral of `s.indicator (fun _ ↦ c)` over `t` is `μ.real (s ∩ t) • c`. -/
lemma setIntegral_indicator_const (μ : Measure[m0] α)
    (hs : MeasurableSet[m0] s) (t : Set α) (c : E) :
    ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ = μ.real (s ∩ t) • c := by
  have : ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ
        = ∫ x, s.indicator (fun _ : α ↦ c) x ∂(μ.restrict t) := rfl
  calc
    ∫ x in t, s.indicator (fun _ : α ↦ c) x ∂μ
        = ∫ x, s.indicator (fun _ : α ↦ c) x ∂(μ.restrict t) := this
    _ = ∫ x in s, (fun _ : α ↦ c) x ∂(μ.restrict t) := by
          simpa using
            (integral_indicator (μ := μ.restrict t) (s := s)
              (f := fun _ : α ↦ c) hs)
    _ = (μ.restrict t).real s • c := setIntegral_const (μ := μ.restrict t) (s := s) (c := c)
    _ = μ.real (s ∩ t) • c := by
          simp [measureReal_def, Measure.restrict_apply hs]

lemma setIntegral_indicator_one (μ : Measure[m0] α) (hs : MeasurableSet[m0] s) (t : Set α) :
    ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ = μ.real (s ∩ t) := by
  simpa [smul_eq_mul, mul_one] using setIntegral_indicator_const μ hs t (1 : ℝ)

/-- For `f : α → ℝ≥0∞`, if the Lebesgue integral is finite then the Bochner integral of `toReal`
agrees with `toReal` of the Lebesgue integral. -/
lemma integral_toReal_of_lintegral_ne_top {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (h_fin : (∫⁻ a, f a ∂μ) ≠ ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  have h_ae_fin : (∀ᵐ a ∂μ, f a < ∞) := by
    have h_lt : (∫⁻ a, f a ∂μ) < ∞ := by
      have : (∫⁻ a, f a ∂μ) ≤ (∞ : ℝ≥0∞) := le_top
      exact lt_of_le_of_ne this h_fin
    exact ae_lt_top' hf_meas h_fin
  simpa using integral_toReal hf_meas h_ae_fin

end AuxReal

/-- If `g` has the same Lebesgue integral as the indicator of `s` on every `m`-measurable set of
finite measure, then `g.toReal` agrees a.e. with the conditional expectation of that indicator. -/
lemma toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
    (hs_meas : MeasurableSet[m0] s) (hgm : AEStronglyMeasurable[m] g μ)
    (hg_int_finite : ∀ t, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ ≠ ⊤)
    (hg_eq : ∀ t : Set α, MeasurableSet[m] t → μ t < ∞ → ∫⁻ a in t, g a ∂μ = μ (s ∩ t)) :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1|m] := by
  have hf : Integrable (s.indicator fun _ ↦ (1 : ℝ)) μ := by
    rw [integrable_indicator_iff hs_meas]
    letI : IsFiniteMeasure (μ.restrict s) := inferInstance
    simpa [IntegrableOn] using integrable_const (1 : ℝ) (μ := μ.restrict s)
  refine ae_eq_condExp_of_forall_setIntegral_eq (E := ℝ) hm hf
    (fun t ht hμt ↦ integrableOn_toReal hm hgm hg_int_finite ht hμt) (fun t ht hμt ↦ ?_)
    ?_
  · have h_fin_lint : ∫⁻ a, g a ∂μ.restrict t ≠ ⊤ := by
      simpa [Measure.restrict_restrict (hm _ ht)] using hg_int_finite t ht hμt
    have h_lhs :
        ∫ x in t, (g x).toReal ∂μ = (∫⁻ a in t, g a ∂μ).toReal :=
      integral_toReal_of_lintegral_ne_top (μ := μ.restrict t)
        ((hgm.mono hm).aemeasurable.restrict) h_fin_lint
    calc
      ∫ x in t, (g x).toReal ∂μ = (∫⁻ a in t, g a ∂μ).toReal := h_lhs
      _ = (μ (s ∩ t)).toReal := by rw [hg_eq t ht hμt]
      _ = μ.real (s ∩ t) := by simp [measureReal_def]
      _ = ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ :=
        (setIntegral_indicator_one μ hs_meas t).symm
  · exact hgm.stronglyMeasurable_mk.measurable.ennreal_toReal.aestronglyMeasurable.congr
      (hgm.ae_eq_mk.fun_comp ENNReal.toReal).symm

/-- Characterization: `g.toReal` equals the conditional expectation of the indicator constant
iff the lintegral of `g` over every `m`-measurable set `t` equals `μ (s ∩ t)`.

We assume `g` is finite a.e. so that restriction Lebesgue integrals are well-behaved under `toReal`.
-/
lemma toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq (hm : m ≤ m0)
    [SigmaFinite (μ.trim hm)] {g : α → ℝ≥0∞} {s : Set α}
    (hs_meas : MeasurableSet[m0] s) (hs_finite : μ s ≠ ⊤)
    (hgm : AEStronglyMeasurable[m] g μ) (hg_fin : ∀ᵐ a ∂μ, g a ≠ ⊤) :
    (fun a ↦ (g a).toReal) =ᵐ[μ] μ[s.indicator 1| m] ↔
      ∀ t, @MeasurableSet α m t → μ (s ∩ t) = ∫⁻ a in t, g a ∂μ := by
  constructor
  · intro h_eq t ht
    have hOnes : IntegrableOn (fun _ : α => (1 : ℝ)) s μ := by
      letI : IsFiniteMeasure (μ.restrict s) := inferInstance
      simpa [IntegrableOn] using integrable_const (1 : ℝ) (μ := μ.restrict s)
    have h_int : Integrable (s.indicator fun _ : α => (1 : ℝ)) μ :=
      IntegrableOn.integrable_indicator hOnes hs_meas
    have h_int_eq :
        ∫ x in t, (μ[s.indicator (fun _ : α => (1 : ℝ))|m]) x ∂μ
          = ∫ x in t, s.indicator (fun _ : α => (1 : ℝ)) x ∂μ :=
      setIntegral_condExp (m := m) (m₀ := m0) (μ := μ) (f := s.indicator fun _ : α => (1 : ℝ)) hm
        h_int ht
    have h_rhs := setIntegral_indicator_one μ hs_meas t
    have h_eq_restrict :
        (fun x => (g x).toReal) =ᵐ[μ.restrict t] (fun x => (μ[s.indicator 1|m]) x) :=
      ae_restrict_of_ae h_eq
    have h_lhs :
        ∫ x in t, (g x).toReal ∂μ = ∫ x in t, (μ[s.indicator 1|m]) x ∂μ := by
      simpa using (integral_congr_ae (μ := μ.restrict t) h_eq_restrict)
    have h_int_g_toReal_on : IntegrableOn (fun a ↦ (g a).toReal) t μ :=
      (integrable_condExp.integrableOn.congr h_eq_restrict.symm)
    have h_int_g_toReal :
        Integrable (fun a ↦ (g a).toReal) (μ.restrict t) := by
      simpa [IntegrableOn] using h_int_g_toReal_on
    have h_ae_fin : ∀ᵐ a ∂ μ.restrict t, g a ≠ ⊤ :=
      ae_restrict_of_ae hg_fin
    have h_fin_lintegral_g :
        ∫⁻ a, g a ∂(μ.restrict t) ≠ ⊤ :=
      ((integrable_toReal_iff
        (μ := μ.restrict t)
        (((hgm.mono hm).aemeasurable).restrict)) h_ae_fin).1 h_int_g_toReal
    have h_toReal :
        ∫ x in t, (g x).toReal ∂μ = (∫⁻ a in t, g a ∂μ).toReal :=
      integral_toReal_of_lintegral_ne_top (μ := μ.restrict t)
        (((hgm.mono hm).aemeasurable).restrict) h_fin_lintegral_g
    have h_eq_int :
        ∫ x in t, (g x).toReal ∂μ = μ.real (s ∩ t) := by
      simpa [h_rhs] using h_lhs.trans (h_int_eq.trans (by simpa [measureReal_def] using h_rhs))
    have h_left_ne : ∫⁻ a in t, g a ∂μ ≠ ⊤ := h_fin_lintegral_g
    have h_le : μ (s ∩ t) ≤ μ s := by
      have hsubset : s ∩ t ⊆ s := fun x hx => hx.1
      exact measure_mono hsubset
    have h_right_ne : μ (s ∩ t) ≠ ⊤ := by
      intro htop
      have : (⊤ : ℝ≥0∞) ≤ μ s := by simpa [htop] using h_le
      exact hs_finite (top_unique this)
    have h_toReal' :
        (∫⁻ a in t, g a ∂μ).toReal = μ.real (s ∩ t) := by
      simpa [h_toReal] using h_eq_int
    have h_lintegral_eq_measure :
        ∫⁻ a in t, g a ∂μ = μ (s ∩ t) := by
      have := congrArg ENNReal.ofReal h_toReal'
      simpa [measureReal_def, ENNReal.ofReal_toReal h_left_ne, ENNReal.ofReal_toReal h_right_ne]
        using this
    exact h_lintegral_eq_measure.symm
  · intro h_eq
    refine
      toReal_ae_eq_indicator_condExp_of_forall_setLIntegral_eq (m := m) (m0 := m0) (μ := μ)
        (g := g) (s := s) hm hs_meas hgm ?_ ?_
    · intro t ht hμt
      have hsubset : s ∩ t ⊆ t := fun x hx => hx.2
      have hμst_lt : μ (s ∩ t) < ∞ := (measure_mono hsubset).trans_lt hμt
      have h_id : ∫⁻ a in t, g a ∂μ = μ (s ∩ t) := (h_eq t ht).symm
      simpa [h_id] using hμst_lt.ne
    · intro t ht hμt
      simpa using (h_eq t ht).symm

end MeasureTheory

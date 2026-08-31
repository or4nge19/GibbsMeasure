/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pratt's lemma and Scheffé's lemma

The Lebesgue dominated convergence theorem controls `∫ Fᵢ` by a *fixed* integrable bound. Pratt's
lemma relaxes this to a *varying* bound `boundᵢ` which converges, in `L¹` as well as pointwise, to
an integrable limit. Scheffé's lemma is the special case `boundᵢ = ‖Fᵢ‖`: pointwise convergence
together with convergence of the norms upgrades itself to `L¹` convergence.

## Main declarations

* `MeasureTheory.tendsto_integral_norm_sub_zero_of_dominated_convergence`: Pratt's lemma in its
  `L¹` form, `∫ ‖Fᵢ - f‖ → 0`.
* `MeasureTheory.tendsto_integral_of_dominated_convergence_of_tendsto`: Pratt's lemma,
  `∫ Fᵢ → ∫ f`.
* `MeasureTheory.tendsto_integral_norm_sub_zero_of_tendsto_integral_norm`: Scheffé's lemma.
* `MeasureTheory.tendsto_eLpNorm_one_sub_zero_of_tendsto_integral_norm`: Scheffé's lemma, phrased
  with `eLpNorm _ 1`.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory
variable {α E ι : Type*} {m : MeasurableSpace α} {μ : Measure α} {l : Filter ι}
  [NormedAddCommGroup E] {F : ι → α → E} {f : α → E} {bound : ι → α → ℝ} {b : α → ℝ}

/-- **Pratt's lemma**, `L¹` form: if `Fᵢ → f` almost everywhere and `‖Fᵢ‖` is dominated by a family
`boundᵢ` converging to `b` both pointwise and in mean, then `Fᵢ → f` in `L¹`. -/
theorem tendsto_integral_norm_sub_zero_of_dominated_convergence [l.IsCountablyGenerated] [l.NeBot]
    (hF_meas : ∀ i, AEStronglyMeasurable (F i) μ) (hbound : ∀ i, Integrable (bound i) μ)
    (h_bound : ∀ i, ∀ᵐ a ∂μ, ‖F i a‖ ≤ bound i a) (hb : Integrable b μ)
    (hb_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ bound i a) l (𝓝 (b a)))
    (hb_tendsto : Tendsto (fun i ↦ ∫ a, bound i a ∂μ) l (𝓝 (∫ a, b a ∂μ)))
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ F i a) l (𝓝 (f a))) :
    Tendsto (fun i ↦ ∫ a, ‖F i a - f a‖ ∂μ) l (𝓝 0) := by
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have hfb : ∀ᵐ a ∂μ, ‖f a‖ ≤ b a := by
    filter_upwards [hb_lim, h_lim, (ae_all_iff.2 fun n ↦ h_bound (u n))] with a hba hfa hab
    exact le_of_tendsto_of_tendsto' (hfa.norm.comp hu) (hba.comp hu) fun n ↦ hab n
  have hb_nonneg : ∀ᵐ a ∂μ, 0 ≤ b a := by
    filter_upwards [hfb] with a ha using (norm_nonneg _).trans ha
  have hF_int : ∀ i, Integrable (F i) μ := fun i ↦ (hbound i).mono' (hF_meas i) (h_bound i)
  have hf_meas : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae l hF_meas h_lim
  have hf_int : Integrable f μ := hb.mono' hf_meas hfb
  set v : ι → α → ℝ := fun i a ↦ max (b a - bound i a + ‖F i a - f a‖) 0 with hv
  have hv_meas : ∀ i, AEStronglyMeasurable (v i) μ := fun i ↦
    ((hb.1.sub (hbound i).1).add ((hF_int i).1.sub hf_meas).norm).sup aestronglyMeasurable_const
  have hv_bound : ∀ i, ∀ᵐ a ∂μ, ‖v i a‖ ≤ 2 * b a := by
    intro i
    filter_upwards [h_bound i, hfb, hb_nonneg] with a hab hfa hba
    have h₁ : b a - bound i a + ‖F i a - f a‖ ≤ 2 * b a := by
      have := (norm_sub_le (F i a) (f a)).trans (add_le_add hab hfa)
      linarith
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le h₁ (by linarith)
  have hv_int : ∀ i, Integrable (v i) μ := fun i ↦
    (hb.const_mul 2).mono' (hv_meas i) (hv_bound i)
  have hv_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ v i a) l (𝓝 0) := by
    filter_upwards [hb_lim, h_lim] with a hba hfa
    have h : Tendsto (fun i ↦ b a - bound i a + ‖F i a - f a‖) l (𝓝 0) := by
      have h₁ : Tendsto (fun i ↦ b a - bound i a) l (𝓝 (b a - b a)) :=
        tendsto_const_nhds.sub hba
      have h₂ : Tendsto (fun i ↦ ‖F i a - f a‖) l (𝓝 ‖f a - f a‖) :=
        (hfa.sub tendsto_const_nhds).norm
      simpa using h₁.add h₂
    simpa [hv] using h.max (tendsto_const_nhds (x := (0 : ℝ)))
  have hv_tendsto : Tendsto (fun i ↦ ∫ a, v i a ∂μ) l (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (F := v) (f := fun _ ↦ (0 : ℝ))
      (fun a ↦ 2 * b a) (Eventually.of_forall hv_meas) (Eventually.of_forall hv_bound)
      (hb.const_mul 2) hv_lim
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ ↦ (0 : ℝ))
    (h := fun i ↦ ∫ a, v i a ∂μ + (∫ a, bound i a ∂μ - ∫ a, b a ∂μ)) tendsto_const_nhds ?_
    (fun i ↦ integral_nonneg fun a ↦ norm_nonneg _) ?_
  · simpa using hv_tendsto.add (hb_tendsto.sub (tendsto_const_nhds (x := ∫ a, b a ∂μ)))
  · intro i
    have h₁ : Integrable (fun a ↦ b a - bound i a) μ := hb.sub (hbound i)
    have h₂ : Integrable (fun a ↦ ‖F i a - f a‖) μ := ((hF_int i).sub hf_int).norm
    have hle : ∫ a, (b a - bound i a + ‖F i a - f a‖) ∂μ ≤ ∫ a, v i a ∂μ :=
      integral_mono (h₁.add h₂) (hv_int i) fun a ↦ le_max_left _ _
    rw [integral_add h₁ h₂, integral_sub hb (hbound i)] at hle
    linarith

/-- **Pratt's lemma**: if `Fᵢ → f` almost everywhere and `‖Fᵢ‖` is dominated by a family `boundᵢ`
converging to `b` both pointwise and in mean, then `∫ Fᵢ → ∫ f`. -/
theorem tendsto_integral_of_dominated_convergence_of_tendsto [NormedSpace ℝ E]
    [l.IsCountablyGenerated] [l.NeBot]
    (hF_meas : ∀ i, AEStronglyMeasurable (F i) μ) (hbound : ∀ i, Integrable (bound i) μ)
    (h_bound : ∀ i, ∀ᵐ a ∂μ, ‖F i a‖ ≤ bound i a) (hb : Integrable b μ)
    (hb_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ bound i a) l (𝓝 (b a)))
    (hb_tendsto : Tendsto (fun i ↦ ∫ a, bound i a ∂μ) l (𝓝 (∫ a, b a ∂μ)))
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ F i a) l (𝓝 (f a))) :
    Tendsto (fun i ↦ ∫ a, F i a ∂μ) l (𝓝 (∫ a, f a ∂μ)) := by
  have hF_int : ∀ i, Integrable (F i) μ := fun i ↦ (hbound i).mono' (hF_meas i) (h_bound i)
  have hf_meas : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae l hF_meas h_lim
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto
  have hfb : ∀ᵐ a ∂μ, ‖f a‖ ≤ b a := by
    filter_upwards [hb_lim, h_lim, (ae_all_iff.2 fun n ↦ h_bound (u n))] with a hba hfa hab
    exact le_of_tendsto_of_tendsto' (hfa.norm.comp hu) (hba.comp hu) fun n ↦ hab n
  have hf_int : Integrable f μ := hb.mono' hf_meas hfb
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun i ↦ ?_)
    (tendsto_integral_norm_sub_zero_of_dominated_convergence hF_meas hbound h_bound hb hb_lim
      hb_tendsto h_lim)
  rw [← integral_sub (hF_int i) hf_int]
  exact norm_integral_le_integral_norm _

/-- **Scheffé's lemma**: almost everywhere convergence together with convergence of the norms
implies `L¹` convergence. -/
theorem tendsto_integral_norm_sub_zero_of_tendsto_integral_norm [l.IsCountablyGenerated] [l.NeBot]
    (hF_meas : ∀ i, AEStronglyMeasurable (F i) μ) (hF_int : ∀ i, Integrable (F i) μ)
    (hf : Integrable f μ)
    (h_norm : Tendsto (fun i ↦ ∫ a, ‖F i a‖ ∂μ) l (𝓝 (∫ a, ‖f a‖ ∂μ)))
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ F i a) l (𝓝 (f a))) :
    Tendsto (fun i ↦ ∫ a, ‖F i a - f a‖ ∂μ) l (𝓝 0) :=
  tendsto_integral_norm_sub_zero_of_dominated_convergence hF_meas (fun i ↦ (hF_int i).norm)
    (fun _ ↦ .of_forall fun _ ↦ le_rfl) hf.norm
    (h_lim.mono fun _ ha ↦ ha.norm) h_norm h_lim

/-- **Scheffé's lemma**, phrased with `eLpNorm _ 1`. -/
theorem tendsto_eLpNorm_one_sub_zero_of_tendsto_integral_norm [l.IsCountablyGenerated] [l.NeBot]
    (hF_meas : ∀ i, AEStronglyMeasurable (F i) μ) (hF_int : ∀ i, Integrable (F i) μ)
    (hf : Integrable f μ)
    (h_norm : Tendsto (fun i ↦ ∫ a, ‖F i a‖ ∂μ) l (𝓝 (∫ a, ‖f a‖ ∂μ)))
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun i ↦ F i a) l (𝓝 (f a))) :
    Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0) := by
  have h : ∀ i, eLpNorm (F i - f) 1 μ = ENNReal.ofReal (∫ a, ‖F i a - f a‖ ∂μ) := fun i ↦ by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hF_int i).sub hf)]
    rfl
  simp only [h]
  have := (ENNReal.continuous_ofReal.tendsto 0).comp
    (tendsto_integral_norm_sub_zero_of_tendsto_integral_norm hF_meas hF_int hf h_norm h_lim)
  simpa [Function.comp_def] using this

end MeasureTheory

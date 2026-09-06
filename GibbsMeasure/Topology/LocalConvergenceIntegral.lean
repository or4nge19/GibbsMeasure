/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Topology.Subsequence
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Bounded convergence for local convergence of random fields

Georgii's topology of local convergence (4.2) is convergence on the local events `𝓕⁰`. It is a
setwise convergence, not a weak convergence, so it integrates **every bounded local function**,
neither continuity nor any topology on the state space being needed.

* `MeasureTheory.tendsto_integral_of_tendsto_setwise`: real-valued bounded convergence for
  setwise convergence on a sub-σ-algebra, deduced from the `ℝ≥0∞`-valued
  `MeasureTheory.GibbsMeasure.tendsto_lintegral_of_tendsto_setwise` of
  `GibbsMeasure/Topology/Subsequence.lean` by rescaling `f` into `[0,1]`.
* `MeasureTheory.tendsto_integral_complex_of_tendsto_setwise`: the complex-valued form, which is
  what characteristic functions need.
* `MeasureTheory.tendsto_integral_of_tendsto_withLocalConvergence`: if `μ_n → μ` in the topology
  of local convergence then `μ_n(f) → μ(f)` for every bounded `𝓕_Λ`-measurable
  `f : (S → E) → ℂ`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*}

/-- **Bounded convergence for setwise convergence on a sub-σ-algebra**, real-valued form. If a
sequence of probability measures converges setwise on a sub-σ-algebra `a`, then the integrals of
every bounded `a`-measurable real function converge. -/
theorem tendsto_integral_of_tendsto_setwise {a m0 : MeasurableSpace α} (ha : a ≤ m0)
    {ρs : ℕ → @Measure α m0} {ρ : @Measure α m0} (hρs : ∀ k, IsProbabilityMeasure (ρs k))
    (hρ : IsProbabilityMeasure ρ) {f : α → ℝ} (hfm : Measurable[a] f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C)
    (hconv : ∀ B, MeasurableSet[a] B → Tendsto (fun k ↦ ρs k B) atTop (𝓝 (ρ B))) :
    Tendsto (fun k ↦ ∫ x, f x ∂(ρs k)) atTop (𝓝 (∫ x, f x ∂ρ)) := by
  set D : ℝ := |C| + 1 with hD
  have hD0 : 0 < D := by positivity
  have hfD : ∀ x, |f x| ≤ D := fun x ↦ (hC x).trans (by simp only [hD]; linarith [le_abs_self C])
  set g : α → ℝ := fun x ↦ (f x + D) / (2 * D) with hg
  have hgm : Measurable[a] g := (hfm.add measurable_const).div_const _
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ by
    have := (abs_le.1 (hfD x)).1
    exact div_nonneg (by linarith) (by positivity)
  have hg1 : ∀ x, g x ≤ 1 := fun x ↦ by
    have := (abs_le.1 (hfD x)).2
    rw [div_le_one (by positivity)]
    linarith
  set G : α → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (g x) with hG
  have hGm : Measurable[a] G := ENNReal.measurable_ofReal.comp hgm
  have hG1 : ∀ x, G x ≤ 1 := fun x ↦ by
    rw [hG, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (hg1 x)
  have hlim := GibbsMeasure.tendsto_lintegral_of_tendsto_setwise ha hρs hρ hGm hG1 hconv
  -- rewrite the Bochner integral of `f` through the lower integral of `G`
  have hkey : ∀ (σ : @Measure α m0), IsProbabilityMeasure σ →
      ∫ x, f x ∂σ = 2 * D * (∫⁻ x, G x ∂σ).toReal - D := by
    intro σ hσ
    have := hσ
    have hfint : Integrable f σ :=
      Integrable.of_bound (hfm.mono ha le_rfl).aestronglyMeasurable D
        (Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hfD x)
    have hgint : ∫ x, g x ∂σ = (∫⁻ x, G x ∂σ).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0)
        (hgm.mono ha le_rfl).aestronglyMeasurable
    have hgeq : ∫ x, g x ∂σ = (∫ x, f x ∂σ + D) / (2 * D) := by
      rw [hg]
      rw [integral_div, integral_add hfint (integrable_const D), integral_const]
      simp
    rw [← hgint, hgeq]
    field_simp
    ring
  have hfin : ∀ (σ : @Measure α m0), IsProbabilityMeasure σ → ∫⁻ x, G x ∂σ ≠ ⊤ := by
    intro σ hσ
    have := hσ
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∫⁻ x, G x ∂σ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂σ := lintegral_mono hG1
      _ = 1 := by simp
  have htoReal : Tendsto (fun k ↦ (∫⁻ x, G x ∂(ρs k)).toReal) atTop
      (𝓝 ((∫⁻ x, G x ∂ρ).toReal)) :=
    (ENNReal.tendsto_toReal (hfin ρ hρ)).comp hlim
  simp only [fun k ↦ hkey (ρs k) (hρs k), hkey ρ hρ]
  exact (htoReal.const_mul (2 * D)).sub_const D

/-- **Bounded convergence for setwise convergence on a sub-σ-algebra**, complex-valued form. -/
theorem tendsto_integral_complex_of_tendsto_setwise {a m0 : MeasurableSpace α} (ha : a ≤ m0)
    {ρs : ℕ → @Measure α m0} {ρ : @Measure α m0} (hρs : ∀ k, IsProbabilityMeasure (ρs k))
    (hρ : IsProbabilityMeasure ρ) {f : α → ℂ} (hfm : Measurable[a] f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C)
    (hconv : ∀ B, MeasurableSet[a] B → Tendsto (fun k ↦ ρs k B) atTop (𝓝 (ρ B))) :
    Tendsto (fun k ↦ ∫ x, f x ∂(ρs k)) atTop (𝓝 (∫ x, f x ∂ρ)) := by
  have hint : ∀ (σ : @Measure α m0), IsProbabilityMeasure σ → Integrable f σ := by
    intro σ hσ
    have := hσ
    exact Integrable.of_bound (hfm.mono ha le_rfl).aestronglyMeasurable C
      (Eventually.of_forall hC)
  have hre : Tendsto (fun k ↦ ∫ x, (f x).re ∂(ρs k)) atTop (𝓝 (∫ x, (f x).re ∂ρ)) :=
    tendsto_integral_of_tendsto_setwise ha hρs hρ (Complex.measurable_re.comp hfm)
      (fun x ↦ (Complex.abs_re_le_norm (f x)).trans (hC x)) hconv
  have him : Tendsto (fun k ↦ ∫ x, (f x).im ∂(ρs k)) atTop (𝓝 (∫ x, (f x).im ∂ρ)) :=
    tendsto_integral_of_tendsto_setwise ha hρs hρ (Complex.measurable_im.comp hfm)
      (fun x ↦ (Complex.abs_im_le_norm (f x)).trans (hC x)) hconv
  have hsplit : ∀ (σ : @Measure α m0), IsProbabilityMeasure σ →
      ∫ x, f x ∂σ = ((∫ x, (f x).re ∂σ : ℝ) : ℂ) + ((∫ x, (f x).im ∂σ : ℝ) : ℂ) * Complex.I := by
    intro σ hσ
    have := hσ
    have hre' : (∫ x, (f x).re ∂σ) = (∫ x, f x ∂σ).re := by
      simpa using ContinuousLinearMap.integral_comp_comm Complex.reCLM (hint σ hσ)
    have him' : (∫ x, (f x).im ∂σ) = (∫ x, f x ∂σ).im := by
      simpa using ContinuousLinearMap.integral_comp_comm Complex.imCLM (hint σ hσ)
    rw [hre', him']
    exact (Complex.re_add_im _).symm
  simp only [fun k ↦ hsplit (ρs k) (hρs k), hsplit ρ hρ]
  exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul tendsto_const_nhds)

/-! ### Local convergence -/

variable {S E : Type*} [MeasurableSpace E]

/-- **Local convergence integrates bounded local functions.** If `μ_n → μ` in the topology of
local convergence (Georgii (4.2)) then `μ_n(f) → μ(f)` for every bounded `𝓕_Λ`-measurable
`f : (S → E) → ℂ`, `Λ` a finite volume. -/
theorem tendsto_integral_of_tendsto_withLocalConvergence
    {μs : ℕ → WithLocalConvergence S E} {μ : WithLocalConvergence S E}
    (h : Tendsto μs atTop (𝓝 μ)) (Λ : Finset S) {f : (S → E) → ℂ}
    (hfm : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun k ↦ ∫ x, f x ∂((μs k).toMeasure : Measure (S → E))) atTop
      (𝓝 (∫ x, f x ∂(μ.toMeasure : Measure (S → E)))) := by
  refine tendsto_integral_complex_of_tendsto_setwise (cylinderEvents_le_pi)
    (fun k ↦ inferInstance) inferInstance hfm hC fun B hB ↦ ?_
  exact (tendsto_withLocalConvergence_iff.1 h) B (mem_localEvents_of_cylinderEvents Λ hB)

end MeasureTheory

end

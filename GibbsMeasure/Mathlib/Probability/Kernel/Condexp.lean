/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Properness of the conditional expectation kernel, and the conditionally independent self-coupling

`condExpKernel μ m ω` is `μ`-a.s. concentrated on the `m`-fibre of `ω` (`condExpKernel_ae_ae_eq`),
averaging it over `μ` returns `μ`, and the *conditionally independent self-coupling*
`condSelfCoupling μ m = ∫ μ(dω) π(·|ω) × π(·|ω)` has both marginals `μ`, sits on the set where the
two coordinates agree on every `m`-measurable function, and dominates `μ(|f - μ[f|m]|)`
(`lintegral_ofReal_abs_sub_condExp_le`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The conditional expectation kernel is **proper**: for an `m`-measurable map `r` into a space
with measurable diagonal, `condExpKernel μ m ω` is `μ`-almost surely concentrated on the fibre
of `r` through `ω`. -/
theorem condExpKernel_ae_ae_eq [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {β : Type*}
    [MeasurableSpace β] [MeasurableEq β] {r : Ω → β} (hr : Measurable[m] r) :
    ∀ᵐ ω ∂μ, ∀ᵐ ζ ∂(condExpKernel μ m ω), r ζ = r ω := by
  classical
  set D : Set (Ω × Ω) := {p | r p.2 = r p.1} with hD_def
  have hrΩ : Measurable r := hr.mono hm le_rfl
  have hD : MeasurableSet[m.prod mΩ] D :=
    measurableSet_eq_fun (β := β) (hrΩ.comp measurable_snd) (hr.comp measurable_fst)
  have hdiag : ((Function.diag : Ω → Ω × Ω) ⁻¹' D) = Set.univ := by
    ext ω; simp [hD_def, Function.diag]
  have hmeas : Measurable[m] fun ω ↦ condExpKernel μ m ω (Prod.mk ω ⁻¹' D) :=
    Kernel.measurable_kernel_prodMk_left hD
  have hcomp : ∫⁻ ω, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) ∂μ = 1 := by
    have hdiagmeas : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag :=
      Measurable.prodMk (measurable_id'' hm) measurable_id
    have h0 : (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) D = 1 := by
      rw [Measure.map_apply hdiagmeas hD, hdiag, measure_univ]
    rw [← compProd_trim_condExpKernel hm, Measure.compProd_apply hD,
      lintegral_trim hm hmeas] at h0
    exact h0
  have hle : ∀ ω, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) ≤ 1 := fun ω ↦ prob_le_one
  have hμ : ∀ᵐ ω ∂μ, condExpKernel μ m ω (Prod.mk ω ⁻¹' D) = 1 := by
    have hmeas' : Measurable fun ω ↦ condExpKernel μ m ω (Prod.mk ω ⁻¹' D) :=
      hmeas.mono hm le_rfl
    have hsub : ∫⁻ ω, (1 - condExpKernel μ m ω (Prod.mk ω ⁻¹' D)) ∂μ = 0 := by
      rw [lintegral_sub hmeas' (by rw [hcomp]; exact ENNReal.one_ne_top)
        (Eventually.of_forall hle), hcomp, lintegral_const, measure_univ, mul_one, tsub_self]
    filter_upwards [(lintegral_eq_zero_iff (by fun_prop : Measurable fun ω ↦
      1 - condExpKernel μ m ω (Prod.mk ω ⁻¹' D))).1 hsub] with ω hω
    exact le_antisymm (hle ω) (by simpa using tsub_eq_zero_iff_le.1 hω)
  filter_upwards [hμ] with ω hω
  have : (condExpKernel μ m ω) {ζ | r ζ = r ω}ᶜ = 0 := by
    have h1 : Prod.mk ω ⁻¹' D = {ζ | r ζ = r ω} := by ext ζ; simp [hD_def]
    have := prob_compl_eq_zero_iff (μ := condExpKernel μ m ω)
      (s := Prod.mk ω ⁻¹' D) (by rw [h1]; exact measurableSet_eq_fun hrΩ measurable_const)
    rw [h1] at this
    exact this.2 (h1 ▸ hω)
  rwa [ae_iff]

end ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Averaging the conditional expectation kernel over `μ` returns `μ`. -/
theorem lintegral_lintegral_condExpKernel (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, (∫⁻ ζ, g ζ ∂(condExpKernel μ m ω)) ∂μ = ∫⁻ ω, g ω ∂μ := by
  have h1 : Measurable[m] fun ω ↦ ∫⁻ ζ, g ζ ∂(condExpKernel μ m ω) := hg.lintegral_kernel
  rw [← lintegral_trim hm h1, ← Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  congr 1
  exact condExpKernel_comp_trim hm

/-- Averaging the conditional expectation kernel over `μ` returns `μ` (Bochner form). -/
theorem integral_integral_condExpKernel (hm : m ≤ mΩ) {F : Ω → ℝ} (hF : Integrable F μ) :
    ∫ ω, (∫ ζ, F ζ ∂(condExpKernel μ m ω)) ∂μ = ∫ ω, F ω ∂μ := by
  rw [← integral_congr_ae (condExp_ae_eq_integral_condExpKernel hm hF), integral_condExp hm]

/-- **Georgii's `ν̃`** (in the proof of (10.26)): the *conditionally independent self-coupling* of
`μ` given the σ-algebra `m`, `ν̃ = ∫ μ(dω) π(·|ω) × π(·|ω)`, where `π = condExpKernel μ m` is a
regular version of `μ(·|m)`. Both marginals of `ν̃` are `μ`, and `ν̃` sits on the set where the two
coordinates agree on every `m`-measurable function. -/
def condSelfCoupling (μ : Measure Ω) [IsProbabilityMeasure μ] (m' : MeasurableSpace Ω) :
    @Measure (Ω × Ω) (@Prod.instMeasurableSpace Ω Ω mΩ mΩ) :=
  μ.bind fun ω ↦ (condExpKernel (mΩ := mΩ) μ m' ×ₖ condExpKernel (mΩ := mΩ) μ m') ω

lemma aemeasurable_condSelfKernel (hm : m ≤ mΩ) :
    @AEMeasurable Ω (Measure (Ω × Ω)) _ mΩ
      (fun ω ↦ (condExpKernel μ m ×ₖ condExpKernel μ m) ω) μ :=
  (((condExpKernel μ m ×ₖ condExpKernel μ m).measurable).mono hm le_rfl).aemeasurable

theorem lintegral_condSelfCoupling (hm : m ≤ mΩ) {f : Ω × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(condSelfCoupling μ m)
      = ∫⁻ ω, ∫⁻ ζ, ∫⁻ η, f (ζ, η) ∂(condExpKernel μ m ω) ∂(condExpKernel μ m ω) ∂μ := by
  rw [condSelfCoupling,
    Measure.lintegral_bind (aemeasurable_condSelfKernel hm) hf.aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [Kernel.prod_apply, lintegral_prod _ hf.aemeasurable]

theorem lintegral_fst_condSelfCoupling (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p.1 ∂(condSelfCoupling μ m) = ∫⁻ ω, g ω ∂μ := by
  rw [lintegral_condSelfCoupling hm
    (show Measurable fun p : Ω × Ω ↦ g p.1 from hg.comp measurable_fst)]
  have h1 : ∀ ω ζ : Ω, ∫⁻ _ : Ω, g ζ ∂(condExpKernel μ m ω) = g ζ := fun ω ζ ↦ by
    rw [lintegral_const, measure_univ, mul_one]
  simp_rw [h1]
  exact lintegral_lintegral_condExpKernel hm hg

theorem lintegral_snd_condSelfCoupling (hm : m ≤ mΩ) {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p.2 ∂(condSelfCoupling μ m) = ∫⁻ ω, g ω ∂μ := by
  rw [lintegral_condSelfCoupling hm
    (show Measurable fun p : Ω × Ω ↦ g p.2 from hg.comp measurable_snd)]
  have h1 : ∀ ω : Ω, ∫⁻ _ : Ω, (∫⁻ η, g η ∂(condExpKernel μ m ω)) ∂(condExpKernel μ m ω)
      = ∫⁻ η, g η ∂(condExpKernel μ m ω) := fun ω ↦ by
    rw [lintegral_const, measure_univ, mul_one]
  simp_rw [h1]
  exact lintegral_lintegral_condExpKernel hm hg

theorem condSelfCoupling_preimage_fst (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    condSelfCoupling μ m (Prod.fst ⁻¹' A) = μ A := by
  have h : (Prod.fst ⁻¹' A).indicator (1 : Ω × Ω → ℝ≥0∞)
      = fun p : Ω × Ω ↦ A.indicator (1 : Ω → ℝ≥0∞) p.1 :=
    funext fun p ↦ by by_cases hp : p.1 ∈ A <;> simp [Set.indicator, hp]
  rw [← lintegral_indicator_one (measurable_fst hA), h,
    lintegral_fst_condSelfCoupling hm (measurable_one.indicator hA),
    lintegral_indicator_one hA]

theorem condSelfCoupling_preimage_snd (hm : m ≤ mΩ) {A : Set Ω} (hA : MeasurableSet A) :
    condSelfCoupling μ m (Prod.snd ⁻¹' A) = μ A := by
  have h : (Prod.snd ⁻¹' A).indicator (1 : Ω × Ω → ℝ≥0∞)
      = fun p : Ω × Ω ↦ A.indicator (1 : Ω → ℝ≥0∞) p.2 :=
    funext fun p ↦ by by_cases hp : p.2 ∈ A <;> simp [Set.indicator, hp]
  rw [← lintegral_indicator_one (measurable_snd hA), h,
    lintegral_snd_condSelfCoupling hm (measurable_one.indicator hA),
    lintegral_indicator_one hA]

theorem isProbabilityMeasure_condSelfCoupling (hm : m ≤ mΩ) :
    IsProbabilityMeasure (condSelfCoupling μ m) := by
  constructor
  rw [show (Set.univ : Set (Ω × Ω)) = Prod.fst ⁻¹' Set.univ from rfl,
    condSelfCoupling_preimage_fst hm MeasurableSet.univ, measure_univ]

/-- The two coordinates of `ν̃` agree on every `m`-measurable function: the conditionally
independent self-coupling sits on the "same `m`-fibre" set. -/
theorem ae_eq_condSelfCoupling (hm : m ≤ mΩ) {β : Type*} [MeasurableSpace β] [MeasurableEq β]
    {r : Ω → β} (hr : Measurable[m] r) :
    ∀ᵐ p ∂(condSelfCoupling μ m), r p.1 = r p.2 := by
  classical
  have hrΩ : Measurable r := hr.mono hm le_rfl
  set B : Set (Ω × Ω) := {p : Ω × Ω | r p.1 = r p.2}ᶜ with hB_def
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun (hrΩ.comp measurable_fst) (hrΩ.comp measurable_snd)).compl
  have hzero : condSelfCoupling μ m B = 0 := by
    rw [← lintegral_indicator_one hB,
      lintegral_condSelfCoupling hm (measurable_one.indicator hB)]
    have hae : (fun ω ↦ ∫⁻ ζ, ∫⁻ η, B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η)
        ∂(condExpKernel μ m ω) ∂(condExpKernel μ m ω)) =ᵐ[μ] 0 := by
      filter_upwards [condExpKernel_ae_ae_eq hm hr] with ω hω
      have h0 : (fun ζ ↦ ∫⁻ η, B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η)
          ∂(condExpKernel μ m ω)) =ᵐ[condExpKernel μ m ω] 0 := by
        filter_upwards [hω] with ζ hζ
        have h1 : (fun η ↦ B.indicator (1 : Ω × Ω → ℝ≥0∞) (ζ, η))
            =ᵐ[condExpKernel μ m ω] 0 := by
          filter_upwards [hω] with η hη
          have : (ζ, η) ∉ B := by simp [hB_def, hζ, hη]
          simp [Set.indicator_of_notMem this]
        rw [lintegral_congr_ae h1]
        simp
      rw [lintegral_congr_ae h0]
      simp
    rw [lintegral_congr_ae hae]
    simp
  rwa [ae_iff]

/-- **Georgii's estimate in the proof of (10.26)**: `ν(|f - π f|) ≤ ν̃(|f(ζ) - f(η)|)`, where
`π = condExpKernel μ m` and `ν̃` is the conditionally independent self-coupling. -/
theorem lintegral_ofReal_abs_sub_condExp_le (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hfm : StronglyMeasurable f) (hf : Integrable f μ) :
    ∫⁻ ω, ENNReal.ofReal |f ω - (μ[f | m]) ω| ∂μ
      ≤ ∫⁻ p, ENNReal.ofReal |f p.1 - f p.2| ∂(condSelfCoupling μ m) := by
  classical
  set g : Ω → ℝ := fun ω ↦ ∫ ζ, f ζ ∂(condExpKernel μ m ω) with hg_def
  have hgm : StronglyMeasurable[m] g := hfm.integral_condExpKernel
  have hgmeas : Measurable g := (hgm.mono hm).measurable
  have hfmeas : Measurable f := hfm.measurable
  have hstep0 : ∫⁻ ω, ENNReal.ofReal |f ω - (μ[f | m]) ω| ∂μ
      = ∫⁻ ω, ENNReal.ofReal |f ω - g ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExp_ae_eq_integral_condExpKernel hm hf] with ω hω
    rw [hω]
  have hmeas1 : Measurable fun ζ ↦ ENNReal.ofReal |f ζ - g ζ| :=
    ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun ζ ↦ |f ζ - g ζ|)
  have hmeas2 : Measurable fun p : Ω × Ω ↦ ENNReal.ofReal |f p.1 - f p.2| :=
    ENNReal.measurable_ofReal.comp
      (by fun_prop : Measurable fun p : Ω × Ω ↦ |f p.1 - f p.2|)
  rw [hstep0, ← lintegral_lintegral_condExpKernel hm hmeas1,
    lintegral_condSelfCoupling hm hmeas2]
  refine lintegral_mono_ae ?_
  filter_upwards [condExpKernel_ae_ae_eq hm hgm.measurable, hf.condExpKernel_ae]
    with ω hω hωint
  calc ∫⁻ ζ, ENNReal.ofReal |f ζ - g ζ| ∂(condExpKernel μ m ω)
      = ∫⁻ ζ, ENNReal.ofReal |f ζ - g ω| ∂(condExpKernel μ m ω) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hω] with ζ hζ
        rw [hζ]
    _ ≤ ∫⁻ ζ, ∫⁻ η, ENNReal.ofReal |f ζ - f η| ∂(condExpKernel μ m ω)
          ∂(condExpKernel μ m ω) := by
        refine lintegral_mono fun ζ ↦ ?_
        have hfint : Integrable (fun η ↦ f ζ - f η) (condExpKernel μ m ω) :=
          (integrable_const _).sub hωint
        have heq : f ζ - g ω = ∫ η, (f ζ - f η) ∂(condExpKernel μ m ω) := by
          rw [integral_sub (integrable_const _) hωint, integral_const]
          simp [hg_def]
        rw [heq]
        calc ENNReal.ofReal |∫ η, (f ζ - f η) ∂(condExpKernel μ m ω)|
            ≤ ENNReal.ofReal (∫ η, |f ζ - f η| ∂(condExpKernel μ m ω)) := by
              gcongr
              exact abs_integral_le_integral_abs
          _ = ∫⁻ η, ENNReal.ofReal |f ζ - f η| ∂(condExpKernel μ m ω) :=
              ofReal_integral_eq_lintegral_ofReal hfint.abs
                (Eventually.of_forall fun _ ↦ abs_nonneg _)

end ProbabilityTheory

end

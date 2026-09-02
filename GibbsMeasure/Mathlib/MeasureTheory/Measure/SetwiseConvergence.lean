/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.UniformAverage
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Group.Pointwise

/-!
# Setwise limits of measures, and conditional expectation on a trivial σ-algebra

* `condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one`: if a probability measure is trivial
  on a sub-σ-algebra `m`, then `μ[f | m]` is a.e. the integral of `f` — `condExp_bot` for a
  σ-algebra that is trivial only modulo `μ`.
* `tendsto_measureReal_of_isPiSystem_of_le`: setwise convergence of measures dominated by a
  finite measure extends from a generating π-system (and `univ`) to every measurable set, by
  Dynkin's π-λ theorem. This is the Dynkin step of Georgii's Proposition (14.7).
* Real-valued lemmas on `uniformAverage` and the averaged intersections it produces.
-/

@[expose] public section

open Filter Finset Set
open scoped ENNReal Topology symmDiff Pointwise

namespace MeasureTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ### Two lemmas bound for Mathlib -/

/-- If a probability measure `μ` is trivial on a sub-σ-algebra `m` — every `m`-measurable set is
null or co-null — then the conditional expectation `μ[f | m]` is a.e. the constant `∫ f dμ`.
This is `condExp_bot` for a σ-algebra that is trivial only modulo `μ`. -/
theorem condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one {m m₀ : MeasurableSpace Ω}
    (hm : m ≤ m₀) {μ : Measure[m₀] Ω} [IsProbabilityMeasure μ]
    (htriv : ∀ A, MeasurableSet[m] A → μ A = 0 ∨ μ A = 1) (f : Ω → ℝ) :
    μ[f | m] =ᵐ[μ] fun _ ↦ ∫ x, f x ∂μ := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one hm htriv
    (stronglyMeasurable_condExp (m := m) (f := f)).measurable
  have h1 : ∫ x, (μ[f | m]) x ∂μ = ∫ x, f x ∂μ := integral_condExp hm
  rw [integral_congr_ae hc, integral_const, probReal_univ, one_smul] at h1
  rw [← h1]
  exact hc

/-- **Setwise convergence extends from a generating π-system.** If a family of measures `ν i`
dominated by a finite measure `μ` converges setwise to a finite measure `ρ` on the whole space
and on a π-system `C` generating the σ-algebra, then it converges setwise on every measurable
set. The set of such sets is a Dynkin system: complements by subtraction, countable disjoint
unions by dominated convergence of the series (`tendsto_tsum_of_dominated_convergence`). -/
theorem tendsto_measureReal_of_isPiSystem_of_le {ι : Type*} {l : Filter ι} {ν : ι → Measure Ω}
    {ρ μ : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ρ] (hν : ∀ᶠ i in l, ν i ≤ μ)
    {C : Set (Set Ω)} (hgen : m = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (huniv : Tendsto (fun i ↦ (ν i).real univ) l (𝓝 (ρ.real univ)))
    (hC : ∀ s ∈ C, Tendsto (fun i ↦ (ν i).real s) l (𝓝 (ρ.real s))) {s : Set Ω}
    (hs : MeasurableSet s) : Tendsto (fun i ↦ (ν i).real s) l (𝓝 (ρ.real s)) := by
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp only [measureReal_empty]; exact tendsto_const_nhds
  | basic t ht => exact hC t ht
  | compl t htm iht =>
    rw [measureReal_compl htm]
    refine (huniv.sub iht).congr' ?_
    filter_upwards [hν] with i hi
    have := isFiniteMeasure_of_le μ hi
    exact (measureReal_compl htm).symm
  | iUnion f hdisj hfm ihf =>
    have hμ : ∑' n, μ (f n) ≠ ∞ := by
      rw [← measure_iUnion hdisj hfm]
      exact measure_ne_top _ _
    have hsum : Summable fun n ↦ μ.real (f n) := ENNReal.summable_toReal hμ
    have hρ : ρ.real (⋃ n, f n) = ∑' n, ρ.real (f n) := by
      rw [measureReal_def, measure_iUnion hdisj hfm,
        ENNReal.tsum_toReal_eq fun _ ↦ measure_ne_top _ _]
      rfl
    rw [hρ]
    refine (tendsto_tsum_of_dominated_convergence hsum ihf ?_).congr' ?_
    · filter_upwards [hν] with i hi n
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (Measure.le_iff'.1 hi _)
    · filter_upwards [hν] with i hi
      rw [measureReal_def, measure_iUnion hdisj hfm, ENNReal.tsum_toReal_eq fun n ↦
        ((Measure.le_iff'.1 hi _).trans_lt (measure_lt_top _ _)).ne]
      rfl

/-- `uniformAverage_real_apply` without the probability hypothesis: the real value of a uniform
average of measures finite on `A`. -/
lemma uniformAverage_real_apply' {ι : Type*} (ms : ι → Measure Ω) {F : Finset ι} {A : Set Ω}
    (hm : ∀ i ∈ F, ms i A ≠ ∞) :
    (uniformAverage ms F).real A = (F.card : ℝ)⁻¹ * ∑ i ∈ F, (ms i).real A := by
  rw [measureReal_def, uniformAverage_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum hm]
  simp only [measureReal_def]

/-- A uniform average of restrictions of `μ` is dominated by `μ`. -/
lemma uniformAverage_restrict_le {ι : Type*} (μ : Measure Ω) (T : ι → Set Ω) (F : Finset ι) :
    uniformAverage (fun i ↦ μ.restrict (T i)) F ≤ μ := by
  refine Measure.le_iff.2 fun s hs ↦ ?_
  rw [uniformAverage_apply]
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  calc ((F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, μ.restrict (T i) s)
      ≤ (F.card : ℝ≥0∞)⁻¹ * ∑ _i ∈ F, μ s := by
        gcongr with i _
        exact Measure.restrict_le_self
    _ = μ s := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast hF.card_pos.ne') (ENNReal.natCast_ne_top _),
          one_mul]

/-- The real value of a uniform average of restrictions on a measurable set. -/
lemma uniformAverage_restrict_real_apply {ι : Type*} {μ : Measure Ω} [IsFiniteMeasure μ]
    (T : ι → Set Ω) (F : Finset ι) {s : Set Ω} (hs : MeasurableSet s) :
    (uniformAverage (fun i ↦ μ.restrict (T i)) F).real s =
      (F.card : ℝ)⁻¹ * ∑ i ∈ F, μ.real (s ∩ T i) := by
  rw [uniformAverage_real_apply' _ fun i _ ↦ measure_ne_top _ _]
  simp only [measureReal_restrict_apply hs]

/-- Setwise convergence of the averages `|F k|⁻¹ ∑_{i ∈ F k} μ(s ∩ T i)` to `a · μ(s)` extends
from a generating π-system to all measurable `s`, when all `T i` have measure `a`. -/
lemma tendsto_inv_card_mul_sum_measureReal_inter_of_isPiSystem {ι κ : Type*} [Nonempty ι]
    {l : Filter κ} {F : κ → Finset ι} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hne : ∀ᶠ k in l, (F k).Nonempty) {C : Set (Set Ω)}
    (hgen : m = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C) {T : ι → Set Ω} {a : ℝ}
    (ha : ∀ i, μ.real (T i) = a)
    (h : ∀ s ∈ C, Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (s ∩ T i)) l
      (𝓝 (a * μ.real s)))
    {s : Set Ω} (hs : MeasurableSet s) :
    Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, μ.real (s ∩ T i)) l (𝓝 (a * μ.real s)) := by
  have ha0 : 0 ≤ a := (ha (Classical.arbitrary ι)) ▸ measureReal_nonneg
  set ρ : Measure Ω := ENNReal.ofReal a • μ with hρdef
  have hρ : ∀ s, ρ.real s = a * μ.real s := fun s ↦ by
    rw [hρdef, measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal ha0]
    rfl
  have : IsFiniteMeasure ρ := by
    refine ⟨?_⟩
    rw [hρdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hmeasC : ∀ t ∈ C, MeasurableSet t := fun t ht ↦
    hgen ▸ MeasurableSpace.measurableSet_generateFrom ht
  have key := tendsto_measureReal_of_isPiSystem_of_le (l := l)
    (ν := fun k ↦ uniformAverage (fun i ↦ μ.restrict (T i)) (F k)) (ρ := ρ) (μ := μ)
    (Eventually.of_forall fun k ↦ uniformAverage_restrict_le μ T (F k)) hgen hpi ?_ ?_ hs
  · simpa only [uniformAverage_restrict_real_apply T _ hs, hρ] using key
  · rw [hρ, probReal_univ, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hne] with k hk
    rw [uniformAverage_restrict_real_apply T _ .univ]
    simp only [univ_inter, ha, Finset.sum_const, nsmul_eq_mul]
    rw [inv_mul_cancel_left₀ (by exact_mod_cast hk.card_pos.ne')]
  · intro t ht
    simpa only [uniformAverage_restrict_real_apply T _ (hmeasC t ht), hρ] using h t ht

/-! ### Mixing on average for a group action -/

end MeasureTheory

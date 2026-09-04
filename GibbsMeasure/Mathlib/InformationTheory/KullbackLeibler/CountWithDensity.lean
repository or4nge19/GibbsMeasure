/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.InformationTheory.KullbackLeibler.KLFun
public import GibbsMeasure.Mathlib.InformationTheory.RelativeEntropy
public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix

/-!
# Relative entropy of probability vectors on a finite type

A probability vector `p` on a finite type `α` with measurable singletons is the measure
`count.withDensity (ENNReal.ofReal ∘ p)`. For two such vectors `p` and `q` with `q > 0`, the
Kullback–Leibler divergence is the classical relative entropy `∑ x, p x * log (p x / q x)`
(`klDiv_count_withDensity_ofReal`).
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal

namespace InformationTheory

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- `count.withDensity f` is a finite measure on a finite type when `f` is finite. -/
lemma _root_.MeasureTheory.isFiniteMeasure_count_withDensity_of_ne_top {f : α → ℝ≥0∞}
    (hf : ∀ x, f x ≠ ∞) : IsFiniteMeasure (Measure.count.withDensity f) := by
  refine isFiniteMeasure_withDensity ?_
  rw [lintegral_count, tsum_fintype]
  exact (ENNReal.sum_lt_top.2 fun x _ ↦ (hf x).lt_top).ne

/-- **Relative entropy of probability vectors.** For nonnegative `p` and positive `q` on a finite
type with the same total mass, the Kullback–Leibler divergence of the measures with densities `p`
and `q` with respect to counting measure is `∑ x, p x * log (p x / q x)`. -/
theorem klDiv_count_withDensity_ofReal {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpq : ∑ x, p x = ∑ x, q x) :
    klDiv (Measure.count.withDensity fun x ↦ ENNReal.ofReal (p x))
        (Measure.count.withDensity fun x ↦ ENNReal.ofReal (q x))
      = ENNReal.ofReal (∑ x, p x * log (p x / q x)) := by
  have := isFiniteMeasure_count_withDensity_of_ne_top fun x ↦ ENNReal.ofReal_ne_top (r := p x)
  have := isFiniteMeasure_count_withDensity_of_ne_top fun x ↦ ENNReal.ofReal_ne_top (r := q x)
  have hμ : ∀ x, (Measure.count.withDensity fun x ↦ ENNReal.ofReal (p x)).real {x} = p x :=
    fun x ↦ by
      rw [measureReal_def, Measure.count_withDensity_apply_singleton, ENNReal.toReal_ofReal (hp x)]
  have hν : ∀ x, (Measure.count.withDensity fun x ↦ ENNReal.ofReal (q x)).real {x} = q x :=
    fun x ↦ by
      rw [measureReal_def, Measure.count_withDensity_apply_singleton,
        ENNReal.toReal_ofReal (hq x).le]
  have hterm : ∀ x, p x * log (p x / q x) + q x - p x = q x * klFun (p x / q x) := fun x ↦ by
    rw [mul_log_div_eq_mul_klFun_div_add_sub (hq x).ne']
    ring
  rw [klDiv_eq_sum_singleton fun x h ↦ absurd h (by
      rw [Measure.count_withDensity_apply_singleton]
      exact (ENNReal.ofReal_pos.2 (hq x)).ne')]
  simp_rw [hμ, hν, hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦
    mul_nonneg (hq x).le (klFun_nonneg (div_nonneg (hp x) (hq x).le))]
  congr 1
  rw [← sum_mul_log_div_eq_sum_mul_klFun_div (fun x _ ↦ hq x) hpq]

end InformationTheory

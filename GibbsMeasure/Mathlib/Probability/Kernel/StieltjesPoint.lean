/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Kernel.Defs

/-!
# Kernels to `ℝ` from measurable rational CDFs

`ProbabilityTheory.stieltjesOfMeasurableRat` turns a measurable function `f : α → ℚ → ℝ` into a
measurable family of Stieltjes functions. This file provides the missing glue between that
construction and actual probability measures on `ℝ`:

* `ProbabilityTheory.isRatStieltjesPoint_of_forall_eq_real_Iic`: a point where `f` agrees on the
  rationals with the CDF of a probability measure on `ℝ` is a Stieltjes point;
* `ProbabilityTheory.stieltjesOfMeasurableRat_eq_cdf`: at such a point, `stieltjesOfMeasurableRat`
  recovers the CDF of that measure;
* `ProbabilityTheory.kernelOfMeasurableRat`: the probability kernel from `α` to `ℝ` whose CDF is
  `f`, i.e. `stieltjesOfMeasurableRat` packaged as a `Kernel[mα] α ℝ`. The σ-algebra `mα` is an
  explicit argument (as for `ProbabilityTheory.condExpKernel`) so that the kernel can be built
  over a σ-algebra which is not the ambient instance, e.g. a tail σ-algebra;
* `ProbabilityTheory.kernelOfMeasurableRat_eq`: at a point where `f` agrees on the rationals with
  the CDF of a probability measure `ν`, the kernel takes the value `ν`.
-/

@[expose] public section

open MeasureTheory Set Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

variable {α : Type*}

section IsRatStieltjesPoint

variable {f : α → ℚ → ℝ} {a : α}

/-- A function agreeing on the rationals with the CDF of a probability measure on `ℝ` is a
Stieltjes point. -/
lemma isRatStieltjesPoint_of_forall_eq_real_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ q : ℚ, f a q = ν.real (Iic (q : ℝ))) :
    IsRatStieltjesPoint f a := by
  have hf : f a = fun q : ℚ ↦ cdf ν (q : ℝ) := funext fun q ↦ by rw [h, cdf_eq_real]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]; exact fun q r hqr ↦ monotone_cdf ν (by exact_mod_cast hqr)
  · rw [hf]; exact (tendsto_cdf_atTop ν).comp (tendsto_ratCast_atTop_iff.2 tendsto_id)
  · rw [hf]; exact (tendsto_cdf_atBot ν).comp (tendsto_ratCast_atBot_iff.2 tendsto_id)
  · intro t
    rw [hf]
    show ⨅ r : Ioi t, cdf ν ((r : ℚ) : ℝ) = cdf ν (t : ℝ)
    rw [← (cdf ν).iInf_rat_gt_eq (t : ℝ)]
    exact Equiv.iInf_congr
      { toFun := fun r ↦ ⟨r.1, by exact_mod_cast Set.mem_Ioi.1 r.2⟩
        invFun := fun r ↦ ⟨r.1, Set.mem_Ioi.2 (by exact_mod_cast r.2)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } fun _ ↦ rfl

variable [MeasurableSpace α]

/-- At a point where a measurable rational CDF agrees on the rationals with the CDF of a
probability measure `ν` on `ℝ`, `stieltjesOfMeasurableRat` is the CDF of `ν`. -/
lemma stieltjesOfMeasurableRat_eq_cdf (hf : Measurable f) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (h : ∀ q : ℚ, f a q = ν.real (Iic (q : ℝ))) :
    stieltjesOfMeasurableRat f hf a = cdf ν := by
  have hpt : IsRatStieltjesPoint f a := isRatStieltjesPoint_of_forall_eq_real_Iic ν h
  ext x
  rw [← (cdf ν).iInf_rat_gt_eq x]
  change IsMeasurableRatCDF.stieltjesFunctionAux (toRatCDF f) a x = _
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine iInf_congr fun r ↦ ?_
  rw [toRatCDF_of_isRatStieltjesPoint hpt, h, cdf_eq_real]

end IsRatStieltjesPoint

section KernelOfMeasurableRat

/-- The probability kernel from `α` to `ℝ` whose CDF is the measurable rational CDF `f`:
`stieltjesOfMeasurableRat` packaged as a `Kernel[mα]`. The σ-algebra `mα` is an explicit
argument, so that the kernel can be built over a σ-algebra which is not the ambient instance. -/
noncomputable def kernelOfMeasurableRat (mα : MeasurableSpace α) (f : α → ℚ → ℝ)
    (hf : Measurable[mα] f) : Kernel[mα] α ℝ :=
  letI : MeasurableSpace α := mα
  ⟨fun a ↦ (stieltjesOfMeasurableRat f hf a).measure,
    measurable_measure_stieltjesOfMeasurableRat hf⟩

lemma kernelOfMeasurableRat_apply (mα : MeasurableSpace α) (f : α → ℚ → ℝ)
    (hf : Measurable[mα] f) (a : α) :
    kernelOfMeasurableRat mα f hf a = (@stieltjesOfMeasurableRat α mα f hf a).measure := rfl

instance isMarkovKernel_kernelOfMeasurableRat (mα : MeasurableSpace α) (f : α → ℚ → ℝ)
    (hf : Measurable[mα] f) : IsMarkovKernel (kernelOfMeasurableRat mα f hf) :=
  ⟨fun a ↦ ⟨@measure_stieltjesOfMeasurableRat_univ α f mα hf a⟩⟩

/-- At a Stieltjes point of `f`, the kernel `kernelOfMeasurableRat` gives the half-line
`Iic (q : ℝ)` the mass `f a q`. -/
lemma kernelOfMeasurableRat_apply_Iic (mα : MeasurableSpace α) {f : α → ℚ → ℝ}
    (hf : Measurable[mα] f) {a : α} (ha : IsRatStieltjesPoint f a) (q : ℚ) :
    kernelOfMeasurableRat mα f hf a (Iic (q : ℝ)) = ENNReal.ofReal (f a q) := by
  let _ : MeasurableSpace α := mα
  rw [kernelOfMeasurableRat_apply, measure_stieltjesOfMeasurableRat_Iic,
    stieltjesOfMeasurableRat_eq, toRatCDF_of_isRatStieltjesPoint ha]

/-- If a measurable rational CDF agrees at `a` with the CDF of a probability measure `ν` on `ℝ`,
then `kernelOfMeasurableRat` takes the value `ν` at `a`. -/
lemma kernelOfMeasurableRat_eq (mα : MeasurableSpace α) {f : α → ℚ → ℝ} (hf : Measurable[mα] f)
    {a : α} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ q : ℚ, f a q = ν.real (Iic (q : ℝ))) :
    kernelOfMeasurableRat mα f hf a = ν := by
  let _ : MeasurableSpace α := mα
  rw [kernelOfMeasurableRat_apply, stieltjesOfMeasurableRat_eq_cdf hf ν h, measure_cdf]

end KernelOfMeasurableRat

end ProbabilityTheory

end

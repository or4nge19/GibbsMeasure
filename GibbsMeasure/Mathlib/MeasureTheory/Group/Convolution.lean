/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Products and densities for the convolution of measures

Two facts about `MeasureTheory.Measure.mconv` / `MeasureTheory.Measure.conv` which Mathlib does
not have.

## Main results

* `MeasureTheory.Measure.pi_mconv` (additively `MeasureTheory.Measure.pi_conv`): a finite product
  of convolutions is the convolution of the products,
  `∏ᵢ (μ i ∗ ν i) = (∏ᵢ μ i) ∗ (∏ᵢ ν i)`.
* `MeasureTheory.Measure.mconv_apply_univ` (additively `MeasureTheory.Measure.conv_apply_univ`):
  the total mass of a convolution is the product of the total masses.
* `MeasureTheory.Measure.mconv_withDensity` (additively
  `MeasureTheory.Measure.conv_withDensity`): the convolution of an *arbitrary* measure `μ` with a
  measure `ν.withDensity g` absolutely continuous relative to an invariant measure `ν` is again
  absolutely continuous relative to `ν`, with density the convolution `z ↦ ∫⁻ x, g (x⁻¹ * z) ∂μ`
  of `g` with `μ`.  Taking `μ = ν.withDensity f` recovers
  `MeasureTheory.mconv_withDensity_eq_mlconvolution`, which is the only case Mathlib has.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace MeasureTheory.Measure

/-! ### Products -/

section Pi

variable {ι : Type*} [Fintype ι] {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]

/-- **A finite product of convolutions is the convolution of the products.**  Under the
identification `(ι → M × M) ≃ (ι → M) × (ι → M)` of
`MeasurableEquiv.arrowProdEquivProdArrow`, the coordinatewise products of independent pairs are
the product of the coordinatewise products. -/
@[to_additive]
theorem pi_mconv (μ ν : ι → Measure M) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    [∀ i, SigmaFinite (μ i ∗ₘ ν i)] :
    Measure.pi (fun i ↦ μ i ∗ₘ ν i) = (Measure.pi μ) ∗ₘ (Measure.pi ν) := by
  have hmulPi : Measurable fun x : ι → M × M ↦ fun i ↦ (x i).1 * (x i).2 :=
    measurable_pi_lambda _ fun i ↦
      (measurable_fst.comp (measurable_pi_apply i)).mul
        (measurable_snd.comp (measurable_pi_apply i))
  set e := MeasurableEquiv.arrowProdEquivProdArrow M M ι with he
  have hsymm : ((Measure.pi μ).prod (Measure.pi ν)).map e.symm
      = Measure.pi fun i ↦ (μ i).prod (ν i) := by
    rw [← (measurePreserving_arrowProdEquivProdArrow M M ι μ ν).map_eq, e.map_symm_map]
  have hsf : ∀ i, SigmaFinite (((μ i).prod (ν i)).map fun p : M × M ↦ p.1 * p.2) :=
    fun i ↦ inferInstanceAs (SigmaFinite (μ i ∗ₘ ν i))
  have hstep : (Measure.pi fun i ↦ (μ i).prod (ν i)).map (fun x i ↦ (x i).1 * (x i).2)
      = Measure.pi (fun i ↦ μ i ∗ₘ ν i) :=
    Measure.pi_map_pi (μ := fun i ↦ (μ i).prod (ν i)) (f := fun _ (p : M × M) ↦ p.1 * p.2)
      (fun _ ↦ measurable_mul.aemeasurable)
  calc Measure.pi (fun i ↦ μ i ∗ₘ ν i)
      = (Measure.pi fun i ↦ (μ i).prod (ν i)).map (fun x i ↦ (x i).1 * (x i).2) := hstep.symm
    _ = (((Measure.pi μ).prod (Measure.pi ν)).map e.symm).map (fun x i ↦ (x i).1 * (x i).2) := by
        rw [hsymm]
    _ = ((Measure.pi μ).prod (Measure.pi ν)).map
          ((fun x : ι → M × M ↦ fun i ↦ (x i).1 * (x i).2) ∘ e.symm) :=
        Measure.map_map hmulPi e.symm.measurable
    _ = (Measure.pi μ) ∗ₘ (Measure.pi ν) := rfl

end Pi

/-! ### Densities -/

section WithDensity

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **Convolving with an absolutely continuous measure.**  If `ν` is left invariant then
`μ ∗ₘ (ν.withDensity g)` is absolutely continuous relative to `ν`, with density the convolution
`z ↦ ∫⁻ x, g (x⁻¹ * z) ∂μ` of `g` with `μ`.  Nothing is assumed of `μ`; for
`μ = ν.withDensity f` this is `MeasureTheory.mconv_withDensity_eq_mlconvolution`. -/
@[to_additive]
theorem mconv_withDensity (μ ν : Measure G) [SFinite μ] [SFinite ν] [ν.IsMulLeftInvariant]
    {g : G → ℝ≥0∞} (hg : Measurable g) :
    μ ∗ₘ ν.withDensity g = ν.withDensity fun z ↦ ∫⁻ x, g (x⁻¹ * z) ∂μ := by
  have hgxz : Measurable (Function.uncurry fun x z : G ↦ g (x⁻¹ * z)) :=
    hg.comp (measurable_fst.inv.mul measurable_snd)
  have hq : Measurable fun z ↦ ∫⁻ x, g (x⁻¹ * z) ∂μ := hgxz.lintegral_prod_left
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hinner : ∀ x : G, ∫⁻ y, f (x * y) ∂(ν.withDensity g) = ∫⁻ z, g (x⁻¹ * z) * f z ∂ν := by
    intro x
    have hfx : Measurable fun y ↦ f (x * y) := hf.comp (measurable_const_mul x)
    rw [lintegral_withDensity_eq_lintegral_mul _ hg hfx]
    have h := lintegral_mul_left_eq_self (μ := ν) (fun z ↦ g (x⁻¹ * z) * f z) x
    simpa only [Pi.mul_apply, inv_mul_cancel_left] using h
  rw [lintegral_mconv hf, lintegral_withDensity_eq_lintegral_mul _ hq hf]
  simp_rw [hinner]
  rw [lintegral_lintegral_swap (hgxz.mul (hf.comp measurable_snd)).aemeasurable]
  refine lintegral_congr fun z ↦ ?_
  have hgz : Measurable fun x : G ↦ g (x⁻¹ * z) := hg.comp (measurable_inv.mul_const z)
  rw [Pi.mul_apply, lintegral_mul_const _ hgz]

/-- The total mass of a convolution is the product of the total masses. -/
@[to_additive (attr := simp)]
theorem mconv_apply_univ {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
    (μ ν : Measure M) [SFinite ν] : (μ ∗ₘ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [mconv, Measure.map_apply measurable_mul MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

end WithDensity

end MeasureTheory.Measure

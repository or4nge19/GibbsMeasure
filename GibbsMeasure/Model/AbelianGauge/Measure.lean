/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AbelianGauge.Configuration
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import GibbsMeasure.Mathlib.Data.ENNReal.TsumPi
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The quotient measure on the configurations of an abelian lattice gauge field

On a finite lattice `X` the configurations `Configuration e r k` of `AbelianGauge.Configuration`
carry the quotient of Lebesgue measure on the real `k`-cochains times counting measure on the
closed integer `(k + 1)`-cochains, `ν = volume.prod count`: the `MeasureSpace` instance is the
image of `ν` restricted to `[0, r)^{k-cells} × Z^{k+1}(ℤ)`. In the notation of
`AbelianGauge.Configuration` (degree `1`, `r = 2π/q`) this is [Q] (2.4), and the Gaussian bound
below is [Q] (2.6) with the constant of (2.5).

* `volume` integrates as `∑_z ∫_{[0, r)^{k-cells}} Φ(A, z) dA` (`lintegral_eq_tsum`,
  `integral_eq_tsum`): definition (2.4), for measurable `Φ ≥ 0` and for integrable `Φ`.
* For `r > 0` the box `[0, r)^{k-cells} × univ` is a fundamental domain of the integer shifts for
  `ν` (`isAddFundamentalDomain`): each class has a unique representative there
  (`existsUnique_mk_eq`). The shifts preserve `ν` (it is translation invariant), so `volume` is
  the quotient measure of Mathlib for every fundamental domain
  (`addQuotientMeasureEqMeasurePreimage`, `volume_eq_map_restrict`, `lintegral_eq_setLIntegral`).
* The field strength is measurable (`measurable_fieldStrength`) and the Gaussian weight has
  `0 < ∫ e^{-‖F‖²/2} ≤ r^{#k-cells} C^{#(k+1)-cells}`, `C = sup_y ∑_{j ∈ ℤ} e^{-(y + r j)²/2}`
  (`lintegral_exp_neg_sum_sq_fieldStrength_le`, `lintegral_exp_neg_sum_sq_fieldStrength_pos`):
  drop `d z = 0`, and at fixed `A` sum each value of `z` separately
  (`ENNReal.tsum_pi_prod_le_prod_tsum`). With `C ≤ 2 + √(2π) / r`
  (`ENNReal.tsum_ofReal_exp_neg_mul_add_mul_intCast_sq_le`) the weight is integrable
  (`integrable_exp_neg_sum_sq_fieldStrength`) with positive integral.

In `d = 3` with `k = 1` there are `3V` links and `3V` plaquettes on a torus of `V` sites, and the
bound is `(r C)^{3V}`.

## Searches

Mathlib `d13f23b7`: the quotient-measure API (`IsAddFundamentalDomain`,
`AddQuotientMeasureEqMeasurePreimage`, `IsAddFundamentalDomain.addQuotientMeasureEqMeasurePreimage`,
`Measure.instIsAddRightInvariantCount`) is consumed as is; `ZSpan.fundamentalDomain` is for a
lattice acting on a vector space alone, not for the integer shifts acting on both factors, and is
not needed (the box is a product of intervals, `existsUnique_add_zsmul_mem_Ico`).
-/

@[expose] public section

open MeasureTheory CubicalCochain Set Real
open scoped ENNReal

namespace AbelianGauge

variable {X ι : Type*} [AddCommGroup X] [Fintype X] [LinearOrder ι] [Fintype ι] {e : ι → X}
  {r : ℝ} {k : ℕ}

/-- The measure on the configurations, [Q] (2.4): Lebesgue measure on `A ∈ [0, r)^{k-cells}`
times counting measure on the closed integer `z`, carried to the quotient. -/
noncomputable instance : MeasureSpace (Configuration e r k) where
  volume := ((volume.restrict (univ.pi fun _ ↦ Ico 0 r)).prod Measure.count).map
    QuotientAddGroup.mk

theorem volume_eq : (volume : Measure (Configuration e r k)) =
    ((volume.restrict (univ.pi fun _ ↦ Ico 0 r)).prod Measure.count).map QuotientAddGroup.mk :=
  rfl

omit [Fintype X] in
theorem measurable_mk : Measurable (QuotientAddGroup.mk :
    (CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1) → Configuration e r k) :=
  measurable_quotient_mk''

/-! ### Integration over the configurations -/

/-- **[Q] (2.4)** for nonnegative measurable functions:
`∫ Φ = ∑_{z closed} ∫_{[0, r)^{k-cells}} Φ(A, z) dA`. -/
theorem lintegral_eq_tsum {Φ : Configuration e r k → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ c, Φ c = ∑' z : cocycles ℤ e (k + 1),
      ∫⁻ (A : CubicalCell X ι k → ℝ) in univ.pi fun _ ↦ Ico 0 r,
        Φ ((A, z) : Configuration e r k) := by
  rw [volume_eq, lintegral_map hΦ measurable_mk]
  exact (lintegral_prod_symm _ (hΦ.comp measurable_mk).aemeasurable).trans (lintegral_count _)

/-- **[Q] (2.4)** for integrable functions:
`∫ Φ = ∑_{z closed} ∫_{[0, r)^{k-cells}} Φ(A, z) dA`. -/
theorem integral_eq_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Φ : Configuration e r k → E} (hΦ : Integrable Φ) :
    ∫ c, Φ c = ∑' z : cocycles ℤ e (k + 1),
      ∫ (A : CubicalCell X ι k → ℝ) in univ.pi fun _ ↦ Ico 0 r,
        Φ ((A, z) : Configuration e r k) := by
  have h : Integrable (Φ ∘ QuotientAddGroup.mk)
      ((volume.restrict (univ.pi fun _ ↦ Ico 0 r)).prod
        (Measure.count : Measure (cocycles ℤ e (k + 1)))) :=
    hΦ.comp_measurable measurable_mk
  rw [volume_eq, integral_map measurable_mk.aemeasurable hΦ.aestronglyMeasurable]
  refine (integral_prod_symm _ h).trans ((integral_countable h.integral_prod_right).trans ?_)
  simp [measureReal_def]

/-! ### Fundamental domains -/

omit [Fintype X] in
theorem op_integerShift_mem (n : CubicalCell X ι k → ℤ) :
    AddOpposite.op (integerShift e r k n) ∈ (integerShift e r k).range.op :=
  AddSubgroup.mem_op.2 ⟨n, (AddOpposite.unop_op _).symm⟩

/-- **The box `[0, r)^{k-cells} × univ` is a fundamental domain** of the integer shifts, for
Lebesgue measure times counting measure. -/
theorem isAddFundamentalDomain (hr : 0 < r) :
    IsAddFundamentalDomain (integerShift e r k).range.op ((univ.pi fun _ ↦ Ico 0 r) ×ˢ univ)
      ((volume : Measure (CubicalCell X ι k → ℝ)).prod
        (Measure.count : Measure (cocycles ℤ e (k + 1)))) := by
  refine .mk' ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico).prod
    MeasurableSet.univ).nullMeasurableSet fun p ↦ ?_
  obtain ⟨n, hn, hu⟩ := existsUnique_add_mul_mem_Ico hr p.1
  have hvadd : ∀ g : (integerShift e r k).range.op, g +ᵥ p = p + AddOpposite.unop (g : _) :=
    fun _ ↦ rfl
  refine ⟨⟨AddOpposite.op (integerShift e r k n), op_integerShift_mem n⟩, ?_, fun g hg ↦ ?_⟩
  · change p + integerShift e r k n ∈ (univ.pi fun _ ↦ Ico 0 r) ×ˢ univ
    exact ⟨fun b _ ↦ hn b, mem_univ _⟩
  · obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (AddSubgroup.mem_op.1 g.2)
    have hg' : p + integerShift e r k m ∈ (univ.pi fun _ ↦ Ico 0 r) ×ˢ univ := by
      rw [hm, ← hvadd]
      exact hg
    have hmn : m = n := hu m fun b ↦ (mem_prod.1 hg').1 b (mem_univ b)
    refine Subtype.ext ?_
    change (g : _) = AddOpposite.op (integerShift e r k n)
    rw [← hmn, hm, AddOpposite.op_unop]

omit [Fintype X] in
variable (e r k) in
theorem countable_range_integerShift_op [Finite X] : Countable (integerShift e r k).range.op :=
  Function.Surjective.countable (f := fun n : CubicalCell X ι k → ℤ ↦
    (⟨AddOpposite.op (integerShift e r k n), op_integerShift_mem n⟩ :
      (integerShift e r k).range.op))
    fun g ↦ by
      obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (AddSubgroup.mem_op.1 g.2)
      refine ⟨m, Subtype.ext ?_⟩
      change AddOpposite.op (integerShift e r k m) = (g : _)
      rw [hm, AddOpposite.op_unop]

/-- **`volume` is the quotient measure** of Lebesgue measure times counting measure, for every
fundamental domain of the integer shifts: the shifts preserve both factors. -/
theorem addQuotientMeasureEqMeasurePreimage (hr : 0 < r) :
    AddQuotientMeasureEqMeasurePreimage
      ((volume : Measure (CubicalCell X ι k → ℝ)).prod
        (Measure.count : Measure (cocycles ℤ e (k + 1))))
      (volume : Measure (Configuration e r k)) := by
  have : ((volume : Measure (CubicalCell X ι k → ℝ)).prod
      (Measure.count : Measure (cocycles ℤ e (k + 1)))).IsAddRightInvariant :=
    Measure.prod.instIsAddRightInvariant
  have := countable_range_integerShift_op e r k
  refine (isAddFundamentalDomain hr).addQuotientMeasureEqMeasurePreimage ?_
  have h : (volume.restrict (univ.pi fun _ ↦ Ico 0 r)).prod
      (Measure.count : Measure (cocycles ℤ e (k + 1))) =
      ((volume : Measure (CubicalCell X ι k → ℝ)).prod Measure.count).restrict
        ((univ.pi fun _ ↦ Ico 0 r) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [volume_eq, h]
  rfl

/-- **Any fundamental domain may be used**: `volume` is the image of Lebesgue measure times
counting measure restricted to any fundamental domain of the integer shifts. -/
theorem volume_eq_map_restrict (hr : 0 < r)
    {t : Set ((CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1))}
    (ht : IsAddFundamentalDomain (integerShift e r k).range.op t
      ((volume : Measure (CubicalCell X ι k → ℝ)).prod Measure.count)) :
    (volume : Measure (Configuration e r k)) =
      (((volume : Measure (CubicalCell X ι k → ℝ)).prod Measure.count).restrict t).map
        QuotientAddGroup.mk :=
  have := addQuotientMeasureEqMeasurePreimage (e := e) (k := k) hr
  ht.addProjection_respects_measure (volume : Measure (Configuration e r k))

theorem lintegral_eq_setLIntegral (hr : 0 < r)
    {t : Set ((CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1))}
    (ht : IsAddFundamentalDomain (integerShift e r k).range.op t
      ((volume : Measure (CubicalCell X ι k → ℝ)).prod Measure.count))
    {Φ : Configuration e r k → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ c, Φ c =
      ∫⁻ p in t, Φ p ∂((volume : Measure (CubicalCell X ι k → ℝ)).prod Measure.count) := by
  rw [volume_eq_map_restrict hr ht, lintegral_map hΦ measurable_mk]

/-! ### The Gaussian weight of the field strength -/

omit [Fintype X] in
theorem measurable_fieldStrength [Finite X] : Measurable (fieldStrength e r k) := by
  have := Fintype.ofFinite X
  refine measurable_from_quotient.2 ?_
  change Measurable fun p : (CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1) ↦
    coboundary e k p.1 + fun σ ↦ r * ((p.2 : CubicalCell X ι (k + 1) → ℤ) σ : ℝ)
  exact ((coboundary (R := ℝ) e k).continuous_of_finiteDimensional.measurable.comp
    measurable_fst).add
    ((Measurable.of_discrete (f := fun z : cocycles ℤ e (k + 1) ↦
      fun σ ↦ r * ((z : CubicalCell X ι (k + 1) → ℤ) σ : ℝ))).comp measurable_snd)

theorem measurable_exp_neg_sum_sq_fieldStrength : Measurable fun c : Configuration e r k ↦
    ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2)) :=
  ENNReal.measurable_ofReal.comp (measurable_exp.comp ((Finset.measurable_sum _ fun σ _ ↦
    ((measurable_pi_apply σ).comp measurable_fieldStrength).pow_const 2).neg.div_const 2))

omit [AddCommGroup X] [Fintype X] [LinearOrder ι] [Fintype ι] in
/-- **The flux sum at fixed background**: for real `a` on a finite set of cells and any family
`v` of distinct integer cochains (e.g. the closed ones),
`∑_z e^{-∑_σ (a σ + r z σ)²/2} ≤ C^{#cells}`, `C = sup_y ∑_{j ∈ ℤ} e^{-(y + r j)²/2}`: drop the
constraint and sum each cell value separately. -/
theorem tsum_ofReal_exp_neg_sum_add_mul_sq_le {κ ζ : Type*} [Fintype κ] (a : κ → ℝ)
    {v : ζ → κ → ℤ} (hv : Function.Injective v) :
    ∑' z, ENNReal.ofReal (exp (-(∑ σ, (a σ + r * (v z σ : ℝ)) ^ 2) / 2)) ≤
      (⨆ y : ℝ, ∑' j : ℤ, ENNReal.ofReal (exp (-(y + r * j) ^ 2 / 2))) ^ Fintype.card κ := by
  set C := ⨆ y : ℝ, ∑' j : ℤ, ENNReal.ofReal (exp (-(y + r * j) ^ 2 / 2))
  have hprod : ∀ w : κ → ℤ, ENNReal.ofReal (exp (-(∑ σ, (a σ + r * (w σ : ℝ)) ^ 2) / 2)) =
      ∏ σ, ENNReal.ofReal (exp (-(a σ + r * (w σ : ℝ)) ^ 2 / 2)) := fun w ↦ by
    rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (exp_pos _).le, ← exp_sum]
    congr 2
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    simp only [neg_div]
  calc ∑' z, ENNReal.ofReal (exp (-(∑ σ, (a σ + r * (v z σ : ℝ)) ^ 2) / 2))
      ≤ ∑' w : κ → ℤ, ENNReal.ofReal (exp (-(∑ σ, (a σ + r * (w σ : ℝ)) ^ 2) / 2)) :=
        ENNReal.tsum_comp_le_tsum_of_injective hv fun w : κ → ℤ ↦
          ENNReal.ofReal (exp (-(∑ σ, (a σ + r * (w σ : ℝ)) ^ 2) / 2))
    _ = ∑' w : κ → ℤ, ∏ σ, ENNReal.ofReal (exp (-(a σ + r * (w σ : ℝ)) ^ 2 / 2)) := by
        simp only [hprod]
    _ ≤ ∏ σ, ∑' j : ℤ, ENNReal.ofReal (exp (-(a σ + r * j) ^ 2 / 2)) :=
        ENNReal.tsum_pi_prod_le_prod_tsum fun σ (j : ℤ) ↦
          ENNReal.ofReal (exp (-(a σ + r * j) ^ 2 / 2))
    _ ≤ ∏ _σ : κ, C := Finset.prod_le_prod fun σ _ ↦
        le_iSup (fun y : ℝ ↦ ∑' j : ℤ, ENNReal.ofReal (exp (-(y + r * j) ^ 2 / 2))) (a σ)
    _ = C ^ Fintype.card κ := by rw [Finset.prod_const, Finset.card_univ]

/-- **[Q] (2.6), upper bound**: `∫ e^{-‖F‖²/2} ≤ r^{#k-cells} C^{#(k+1)-cells}`,
`C = sup_y ∑_{j ∈ ℤ} e^{-(y + r j)²/2}`. -/
theorem lintegral_exp_neg_sum_sq_fieldStrength_le :
    ∫⁻ c : Configuration e r k, ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2)) ≤
      ENNReal.ofReal r ^ Fintype.card (CubicalCell X ι k) *
        (⨆ y : ℝ, ∑' j : ℤ, ENNReal.ofReal (exp (-(y + r * j) ^ 2 / 2))) ^
          Fintype.card (CubicalCell X ι (k + 1)) := by
  set C := ⨆ y : ℝ, ∑' j : ℤ, ENNReal.ofReal (exp (-(y + r * j) ^ 2 / 2))
  have hΦ := measurable_exp_neg_sum_sq_fieldStrength (e := e) (r := r) (k := k)
  rw [lintegral_eq_tsum hΦ]
  calc ∑' z : cocycles ℤ e (k + 1), ∫⁻ (A : CubicalCell X ι k → ℝ) in univ.pi fun _ ↦ Ico 0 r,
        ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k ((A, z) : Configuration e r k) σ ^ 2) / 2))
      = ∫⁻ (A : CubicalCell X ι k → ℝ) in univ.pi fun _ ↦ Ico 0 r, ∑' z : cocycles ℤ e (k + 1),
        ENNReal.ofReal
          (exp (-(∑ σ, fieldStrength e r k ((A, z) : Configuration e r k) σ ^ 2) / 2)) :=
        (lintegral_tsum fun z ↦
          (hΦ.comp (measurable_mk.comp measurable_prodMk_right)).aemeasurable).symm
    _ ≤ ∫⁻ _ in univ.pi fun _ ↦ Ico 0 r, C ^ Fintype.card (CubicalCell X ι (k + 1)) := by
        refine lintegral_mono fun A ↦ ?_
        simp only [fieldStrength_mk, Pi.add_apply]
        exact tsum_ofReal_exp_neg_sum_add_mul_sq_le (coboundary e k A) Subtype.val_injective
    _ = ENNReal.ofReal r ^ Fintype.card (CubicalCell X ι k) *
          C ^ Fintype.card (CubicalCell X ι (k + 1)) := by
        rw [setLIntegral_const, Real.volume_pi_Ico, mul_comm]
        simp only [sub_zero, Finset.prod_const, Finset.card_univ]

/-- **[Q] (2.5)–(2.6)**: `∫ e^{-‖F‖²/2} ≤ r^{#k-cells} (2 + √(2π) / r)^{#(k+1)-cells}`. -/
theorem lintegral_exp_neg_sum_sq_fieldStrength_le_ofReal (hr : 0 < r) :
    ∫⁻ c : Configuration e r k, ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2)) ≤
      ENNReal.ofReal r ^ Fintype.card (CubicalCell X ι k) *
        ENNReal.ofReal (2 + √(2 * π) / r) ^ Fintype.card (CubicalCell X ι (k + 1)) := by
  refine lintegral_exp_neg_sum_sq_fieldStrength_le.trans ?_
  gcongr
  refine iSup_le fun y ↦ ?_
  have h := ENNReal.tsum_ofReal_exp_neg_mul_add_mul_intCast_sq_le one_half_pos hr y
  have h2 : π / (1 / 2) = 2 * π := by ring
  have h3 : ∀ j : ℤ, -(1 / 2) * (y + r * j) ^ 2 = -(y + r * j) ^ 2 / 2 := fun j ↦ by ring
  simpa only [h2, h3] using h

/-- **The Gaussian weight of the field strength has finite integral.** -/
theorem lintegral_exp_neg_sum_sq_fieldStrength_lt_top (hr : 0 < r) :
    ∫⁻ c : Configuration e r k, ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2)) <
      ∞ :=
  (lintegral_exp_neg_sum_sq_fieldStrength_le_ofReal hr).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top))

/-- **[Q] (2.6), lower bound**: `0 < ∫ e^{-‖F‖²/2}`; the weight is positive and the box has
positive volume. -/
theorem lintegral_exp_neg_sum_sq_fieldStrength_pos (hr : 0 < r) :
    0 < ∫⁻ c : Configuration e r k,
      ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2)) := by
  rw [lintegral_pos_iff_support measurable_exp_neg_sum_sq_fieldStrength]
  have hsupp : Function.support (fun c : Configuration e r k ↦
      ENNReal.ofReal (exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2))) = univ :=
    eq_univ_of_forall fun c ↦ (ENNReal.ofReal_pos.2 (exp_pos _)).ne'
  rw [hsupp, volume_eq, Measure.map_apply measurable_mk MeasurableSet.univ, preimage_univ,
    ← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_pi_Ico]
  refine ENNReal.mul_pos (Finset.prod_ne_zero_iff.2 fun _ _ ↦ ?_) ?_
  · simpa using hr
  · rw [Ne, Measure.count_eq_zero_iff]
    exact univ_nonempty.ne_empty

theorem integrable_exp_neg_sum_sq_fieldStrength (hr : 0 < r) :
    Integrable fun c : Configuration e r k ↦ exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2) := by
  refine ⟨(measurable_exp.comp ((Finset.measurable_sum _ fun σ _ ↦
    ((measurable_pi_apply σ).comp measurable_fieldStrength).pow_const 2).neg.div_const
      2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  exact lintegral_exp_neg_sum_sq_fieldStrength_lt_top hr

/-- **The partition function of the field strength is positive**: `0 < ∫ e^{-‖F‖²/2}`. -/
theorem integral_exp_neg_sum_sq_fieldStrength_pos (hr : 0 < r) :
    0 < ∫ c : Configuration e r k, exp (-(∑ σ, fieldStrength e r k c σ ^ 2) / 2) := by
  rw [← ENNReal.ofReal_pos, ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_sum_sq_fieldStrength hr) (ae_of_all _ fun _ ↦ (exp_pos _).le)]
  exact lintegral_exp_neg_sum_sq_fieldStrength_pos hr

end AbelianGauge

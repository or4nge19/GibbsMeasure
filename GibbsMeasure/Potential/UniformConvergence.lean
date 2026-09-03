/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Existence

/-!
# Uniform convergence of Gibbsian specifications

**Georgii Proposition (4.19)** for absolutely summable potentials: if
`‖H_Λ^{Φⁱ − Φ}‖ → 0` for every finite volume `Λ` (expressed through a bound function
`D : ι → Finset S → ℝ` with `|H_Λ^{Φⁱ} − H_Λ^{Φ}| ≤ D i Λ` pointwise and `D · Λ → 0`, or through
the sup itself), then `γ^{Φⁱ} → γ^{Φ}` uniformly, quantitatively:
`‖γ^{Φⁱ}_Λ f − γ^Φ_Λ f‖ ≤ 2 ‖f‖ (exp (|β| D i Λ) − 1) → 0`.

The conclusion is verbatim the uniform-convergence hypothesis of Georgii (4.17)/(4.22)
(`MeasureTheory.GibbsMeasure.mem_GP_of_tendsto_withLocalConvergence`), so cluster points of
`ν_i γ^{Φⁱ}_{Λ_i}` are Gibbs for `Φ` — the route to the free/periodic boundary conditions of
Georgii (4.20) and to (4.23)(c).

Georgii additionally concludes that the limit potential is λ-admissible; here admissibility is
automatic for `Φ ∈ ℬ` and a probability reference measure
    (`isPremodifierAdmissible_boltzmannFactor`),
and `ℬ`-membership of the limit is assumed since `γ^Φ` is only defined on `ℬ`.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open MeasureTheory.GibbsMeasure
open scoped Topology ENNReal NNReal

noncomputable section

namespace Potential

/-! ### Elementary exponential estimates (Georgii's `|e^{-x} − e^{-y}| ≤ e^{-y}(e^{|x−y|} − 1)`) -/

private lemma abs_exp_sub_one_le (t : ℝ) : |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
  · rw [abs_of_neg ht, abs_of_nonpos (by linarith [Real.exp_lt_one_iff.2 ht] : Real.exp t - 1 ≤ 0)]
    have h1 := Real.add_one_le_exp t
    have h2 := Real.add_one_le_exp (-t)
    linarith

private lemma abs_exp_sub_exp_le (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ Real.exp y * (Real.exp |x - y| - 1) := by
  have h : Real.exp x - Real.exp y = Real.exp y * (Real.exp (x - y) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    ring_nf
  rw [h, abs_mul, abs_of_pos (Real.exp_pos y)]
  exact mul_le_mul_of_nonneg_left (abs_exp_sub_one_le _) (Real.exp_pos y).le

/-! ### The arithmetic core of Georgii's estimate

`|A/Zⁱ − B/Z| ≤ |A| |1/Zⁱ − 1/Z| + |A − B|/Z ≤ 2 ‖f‖ (e^D − 1)`. -/

private lemma abs_div_sub_div_le {A B Z Zi t nf : ℝ}
    (hZ : 0 < Z) (hZi : 0 < Zi)
    (hA : |A| ≤ nf * Zi) (hAB : |A - B| ≤ nf * (t * Z)) (hZZi : |Z - Zi| ≤ t * Z) :
    |A / Zi - B / Z| ≤ 2 * nf * t := by
  have hZ' : Z ≠ 0 := hZ.ne'
  have hZi' : Zi ≠ 0 := hZi.ne'
  have key : A / Zi - B / Z = A * (Z - Zi) / (Zi * Z) + (A - B) / Z := by
    field_simp
    ring
  rw [key]
  have h1 : |A * (Z - Zi) / (Zi * Z)| ≤ nf * t := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hZi hZ), div_le_iff₀ (mul_pos hZi hZ)]
    calc |A| * |Z - Zi| ≤ (nf * Zi) * (t * Z) :=
          mul_le_mul hA hZZi (abs_nonneg _) (le_trans (abs_nonneg A) hA)
      _ = nf * t * (Zi * Z) := by ring
  have h2 : |(A - B) / Z| ≤ nf * t := by
    rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    calc |A - B| ≤ nf * (t * Z) := hAB
      _ = nf * t * Z := by ring
  calc |A * (Z - Zi) / (Zi * Z) + (A - B) / Z|
      ≤ |A * (Z - Zi) / (Zi * Z)| + |(A - B) / Z| := abs_add_le _ _
    _ ≤ nf * t + nf * t := add_le_add h1 h2
    _ = 2 * nf * t := by ring

/-- Georgii's chain, at the level of a fixed probability measure `μ` (which will be the free
kernel `λ_Λ(·|η)`): if the two Boltzmann densities `gi, g` satisfy `|gi − g| ≤ g·t` pointwise,
then the normalized expectations of a bounded observable differ by at most `2·nf·t`. -/
private lemma abs_integral_div_sub_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {g gi F : α → ℝ} {K nf t : ℝ}
    (hgm : Measurable g) (hgim : Measurable gi) (hFm : Measurable F)
    (hgpos : ∀ x, 0 < g x) (hgipos : ∀ x, 0 < gi x)
    (hgK : ∀ x, g x ≤ K) (hgiK : ∀ x, gi x ≤ K)
    (hFnf : ∀ x, |F x| ≤ nf) (ht : 0 ≤ t)
    (hpt : ∀ x, |gi x - g x| ≤ g x * t)
    (hZ : 0 < ∫ x, g x ∂μ) (hZi : 0 < ∫ x, gi x ∂μ) :
    |(∫ x, gi x * F x ∂μ) / (∫ x, gi x ∂μ) - (∫ x, g x * F x ∂μ) / (∫ x, g x ∂μ)|
      ≤ 2 * nf * t := by
  -- integrability of all four integrands
  have hgint : Integrable g μ :=
    Integrable.mono' (integrable_const K) hgm.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_pos (hgpos x)]; exact hgK x)
  have hgiint : Integrable gi μ :=
    Integrable.mono' (integrable_const K) hgim.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_pos (hgipos x)]; exact hgiK x)
  have hgFint : Integrable (fun x ↦ g x * F x) μ :=
    Integrable.mono' (integrable_const (K * nf)) (hgm.mul hFm).aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hgpos x)]
        exact mul_le_mul (hgK x) (hFnf x) (abs_nonneg _) ((hgpos x).le.trans (hgK x)))
  have hgiFint : Integrable (fun x ↦ gi x * F x) μ :=
    Integrable.mono' (integrable_const (K * nf)) (hgim.mul hFm).aestronglyMeasurable
      (.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hgipos x)]
        exact mul_le_mul (hgiK x) (hFnf x) (abs_nonneg _) ((hgipos x).le.trans (hgiK x)))
  -- `|Z − Zⁱ| ≤ t Z` (Georgii: `|Z_Λ^{Φ^α} − Z_Λ^Φ| ≤ Z_Λ^Φ (e^D − 1)`)
  have hZZi : |(∫ x, g x ∂μ) - ∫ x, gi x ∂μ| ≤ t * ∫ x, g x ∂μ := by
    rw [← integral_sub hgint hgiint]
    refine abs_integral_le_integral_abs.trans ?_
    refine le_trans (integral_mono (hgint.sub hgiint).abs (hgint.mul_const t) fun x ↦ ?_) ?_
    · rw [abs_sub_comm]
      exact hpt x
    · rw [integral_mul_const]
      exact le_of_eq (mul_comm _ _)
  -- `|A| ≤ nf · Zⁱ` (Georgii: `|λ_Λ(h^{Φ^α} f)| ≤ ‖f‖ Z^{Φ^α}`)
  have hA : |∫ x, gi x * F x ∂μ| ≤ nf * ∫ x, gi x ∂μ := by
    refine abs_integral_le_integral_abs.trans ?_
    refine le_trans (integral_mono hgiFint.abs (hgiint.mul_const nf) fun x ↦ ?_) ?_
    · rw [abs_mul, abs_of_pos (hgipos x)]
      exact mul_le_mul_of_nonneg_left (hFnf x) (hgipos x).le
    · rw [integral_mul_const]
      exact le_of_eq (mul_comm _ _)
  -- `|A − B| ≤ nf · t · Z` (Georgii: `λ_Λ(|h^{Φ^α} − h^Φ|) ≤ Z^Φ (e^D − 1)`)
  have hAB : |(∫ x, gi x * F x ∂μ) - ∫ x, g x * F x ∂μ| ≤ nf * (t * ∫ x, g x ∂μ) := by
    rw [← integral_sub hgiFint hgFint]
    refine abs_integral_le_integral_abs.trans ?_
    refine le_trans (integral_mono (hgiFint.sub hgFint).abs
      ((hgint.mul_const t).mul_const nf) fun x ↦ ?_) ?_
    · rw [← sub_mul, abs_mul]
      exact mul_le_mul (hpt x) (hFnf x) (abs_nonneg _) (mul_nonneg (hgpos x).le ht)
    · rw [integral_mul_const, integral_mul_const]
      exact le_of_eq (by ring)
  exact abs_div_sub_div_le hZ hZi hA hAB hZZi

/-! ### The real Boltzmann density of an absolutely summable potential -/

variable {S E : Type*} [Countable S] [MeasurableSpace E]

section Bridge

variable {Φ : Potential S E} [Φ.IsPotential] [Φ.IsAbsolutelySummable]
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

private lemma measurable_expB (Λ : Finset S) :
    Measurable fun x : S → E ↦ Real.exp (-β * Φ.hamiltonian Λ x) :=
  (measurable_const.mul (measurable_hamiltonian (Φ := Φ) Λ)).exp

private lemma expB_le (Λ : Finset S) (x : S → E) :
    Real.exp (-β * Φ.hamiltonian Λ x) ≤ Real.exp (|β| * Φ.hamiltonianBound Λ) := by
  refine Real.exp_le_exp.2 ?_
  calc -β * Φ.hamiltonian Λ x ≤ |(-β) * Φ.hamiltonian Λ x| := le_abs_self _
    _ = |β| * |Φ.hamiltonian Λ x| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * Φ.hamiltonianBound Λ :=
        mul_le_mul_of_nonneg_left (abs_hamiltonian_le Λ x) (abs_nonneg _)

private lemma le_expB (Λ : Finset S) (x : S → E) :
    Real.exp (-(|β| * Φ.hamiltonianBound Λ)) ≤ Real.exp (-β * Φ.hamiltonian Λ x) := by
  refine Real.exp_le_exp.2 ?_
  have h : |(-β) * Φ.hamiltonian Λ x| ≤ |β| * Φ.hamiltonianBound Λ := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le Λ x) (abs_nonneg _)
  linarith [neg_abs_le ((-β) * Φ.hamiltonian Λ x)]

private lemma integrable_expB (Λ : Finset S) (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    Integrable (fun x ↦ Real.exp (-β * Φ.hamiltonian Λ x)) μ :=
  Integrable.mono' (integrable_const (Real.exp (|β| * Φ.hamiltonianBound Λ)))
    (measurable_expB (Φ := Φ) β Λ).aestronglyMeasurable
    (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact expB_le (Φ := Φ) β Λ x)

private lemma integral_expB_pos (Λ : Finset S) (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    0 < ∫ x, Real.exp (-β * Φ.hamiltonian Λ x) ∂μ := by
  have h1 : Real.exp (-(|β| * Φ.hamiltonianBound Λ))
      ≤ ∫ x, Real.exp (-β * Φ.hamiltonian Λ x) ∂μ := by
    calc Real.exp (-(|β| * Φ.hamiltonianBound Λ))
        = ∫ _, Real.exp (-(|β| * Φ.hamiltonianBound Λ)) ∂μ := by
          rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      _ ≤ _ := integral_mono (integrable_const _) (integrable_expB (Φ := Φ) β Λ μ)
            fun x ↦ le_expB (Φ := Φ) β Λ x
  exact lt_of_lt_of_le (Real.exp_pos _) h1

/-- The `ℝ≥0∞`-valued partition function `premodifierZ` is `ofReal` of the real one. -/
private lemma premodifierZ_eq_ofReal (Λ : Finset S) (ξ : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ξ
      = ENNReal.ofReal (∫ x, Real.exp (-β * Φ.hamiltonian Λ x)
          ∂(Specification.isssd (S := S) (E := E) ν Λ ξ)) := by
  haveI : IsProbabilityMeasure (Specification.isssd (S := S) (E := E) ν Λ ξ) := inferInstance
  have h : Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ξ
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ x))
          ∂(Specification.isssd (S := S) (E := E) ν Λ ξ) := rfl
  rw [h, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_expB (Φ := Φ) β Λ _) (.of_forall fun x ↦ (Real.exp_pos _).le)]

/-- The Gibbs kernel integrates any observable as the normalized Boltzmann average:
`γ^Φ_Λ f (η) = λ_Λ(e^{-βH} f)(η) / λ_Λ(e^{-βH})(η)`. -/
private lemma integral_gibbs_eq (Λ : Finset S) (η : S → E) (F : (S → E) → ℝ) :
    ∫ x, F x ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η)
      = (∫ x, Real.exp (-β * Φ.hamiltonian Λ x) * F x
          ∂(Specification.isssd (S := S) (E := E) ν Λ η))
        / ∫ x, Real.exp (-β * Φ.hamiltonian Λ x)
            ∂(Specification.isssd (S := S) (E := E) ν Λ η) := by
  classical
  haveI : IsProbabilityMeasure (Specification.isssd (S := S) (E := E) ν Λ η) := inferInstance
  set Zc : ℝ := ∫ x, Real.exp (-β * Φ.hamiltonian Λ x)
      ∂(Specification.isssd (S := S) (E := E) ν Λ η) with hZc
  have hZcpos : 0 < Zc := by rw [hZc]; exact integral_expB_pos (Φ := Φ) β Λ _
  -- a.e. constancy of the partition function under the free kernel
  have hZdep : DependsOn
      (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ)
      ((Λ : Set S)ᶜ) :=
    (Specification.measurable_relZ (γ := Specification.isssd (S := S) (E := E) ν)
      (isPremodifier_boltzmannFactor (Φ := Φ) β).measurable Λ).dependsOn_of_cylinderEvents
  have hZfull : Measurable
      (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ) :=
    (Specification.measurable_relZ (γ := Specification.isssd (S := S) (E := E) ν)
      (isPremodifier_boltzmannFactor (Φ := Φ) β).measurable Λ).mono cylinderEvents_le_pi le_rfl
  have hZae : (fun x ↦ Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ x)
      =ᵐ[Specification.isssd (S := S) (E := E) ν Λ η]
      fun _ ↦ Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η := by
    have hmap : Specification.isssd (S := S) (E := E) ν Λ η
        = Measure.map (juxt (Λ : Set S) η) (Measure.pi fun _ : (Λ : Set S) ↦ ν) := rfl
    have hset : MeasurableSet {x : S → E |
        Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ x
          = Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η} :=
      hZfull (measurableSet_singleton _)
    rw [hmap]
    exact (ae_map_iff Measurable.juxt.aemeasurable hset).2
      (Filter.Eventually.of_forall fun ζ ↦
        hZdep fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi) ζ)
  -- rewrite the Gibbs kernel as a `withDensity` with *constant* normalization
  have hkernel : gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η
      = (Specification.isssd (S := S) (E := E) ν Λ η).withDensity
          fun x ↦ ((Real.exp (-β * Φ.hamiltonian Λ x) / Zc).toNNReal : ℝ≥0∞) := by
    have h0 : gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η
        = (Specification.isssd (S := S) (E := E) ν Λ η).withDensity
            (Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ) := rfl
    rw [h0]
    refine withDensity_congr_ae ?_
    filter_upwards [hZae] with x hx
    have h1 : Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ x
        = ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ x))
            / Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ x := rfl
    rw [h1, hx, premodifierZ_eq_ofReal (Φ := Φ) ν β Λ η, ← hZc,
      ← ENNReal.ofReal_div_of_pos hZcpos]
    rfl
  have hrmeas : Measurable fun x : S → E ↦ (Real.exp (-β * Φ.hamiltonian Λ x) / Zc).toNNReal :=
    ((measurable_expB (Φ := Φ) β Λ).div_const Zc).real_toNNReal
  have hsm : ∀ x : S → E, (Real.exp (-β * Φ.hamiltonian Λ x) / Zc).toNNReal • F x
      = Real.exp (-β * Φ.hamiltonian Λ x) * F x / Zc := fun x ↦ by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (Real.exp_pos _).le hZcpos.le),
      smul_eq_mul, div_mul_eq_mul_div]
  calc ∫ x, F x ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η)
      = ∫ x, (Real.exp (-β * Φ.hamiltonian Λ x) / Zc).toNNReal • F x
          ∂(Specification.isssd (S := S) (E := E) ν Λ η) := by
        rw [hkernel]
        exact integral_withDensity_eq_integral_smul hrmeas F
    _ = ∫ x, Real.exp (-β * Φ.hamiltonian Λ x) * F x / Zc
          ∂(Specification.isssd (S := S) (E := E) ν Λ η) :=
        integral_congr_ae (Filter.Eventually.of_forall hsm)
    _ = (∫ x, Real.exp (-β * Φ.hamiltonian Λ x) * F x
          ∂(Specification.isssd (S := S) (E := E) ν Λ η)) / Zc :=
        integral_div Zc _

end Bridge

/-! ### Georgii (4.19): the quantitative estimate and the limit statement -/

section Main

variable {Ψ Φ : Potential S E} [Ψ.IsPotential] [Ψ.IsAbsolutelySummable]
  [Φ.IsPotential] [Φ.IsAbsolutelySummable]
  (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (4.19), pointwise form.** For each boundary condition `η`,
`|γ^Ψ_Λ f (η) − γ^Φ_Λ f (η)| ≤ 2 nf (e^{|β| D} − 1)` whenever `|H^Ψ_Λ − H^Φ_Λ| ≤ D` and
`|f| ≤ nf` pointwise. -/
private lemma abs_integral_gibbs_sub_le (Λ : Finset S) (η : S → E)
    {F : (S → E) → ℝ} (hFm : Measurable F) {nf : ℝ} (hFnf : ∀ x, |F x| ≤ nf)
    {Dv : ℝ} (hDv : ∀ x, |Ψ.hamiltonian Λ x - Φ.hamiltonian Λ x| ≤ Dv) :
    |(∫ x, F x ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β Λ η))
      - ∫ x, F x ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η)|
      ≤ 2 * nf * (Real.exp (|β| * Dv) - 1) := by
  haveI : IsProbabilityMeasure (Specification.isssd (S := S) (E := E) ν Λ η) := inferInstance
  have hDv0 : 0 ≤ Dv := le_trans (abs_nonneg _) (hDv η)
  rw [integral_gibbs_eq (Φ := Ψ) ν β Λ η F, integral_gibbs_eq (Φ := Φ) ν β Λ η F]
  refine abs_integral_div_sub_le (Specification.isssd (S := S) (E := E) ν Λ η)
    (K := max (Real.exp (|β| * Ψ.hamiltonianBound Λ)) (Real.exp (|β| * Φ.hamiltonianBound Λ)))
    (measurable_expB (Φ := Φ) β Λ) (measurable_expB (Φ := Ψ) β Λ) hFm
    (fun x ↦ Real.exp_pos _) (fun x ↦ Real.exp_pos _)
    (fun x ↦ le_trans (expB_le (Φ := Φ) β Λ x) (le_max_right _ _))
    (fun x ↦ le_trans (expB_le (Φ := Ψ) β Λ x) (le_max_left _ _))
    hFnf (sub_nonneg.2 (Real.one_le_exp (by positivity))) (fun x ↦ ?_)
    (integral_expB_pos (Φ := Φ) β Λ _) (integral_expB_pos (Φ := Ψ) β Λ _)
  -- pointwise density comparison: `|e^{-βH^Ψ} − e^{-βH^Φ}| ≤ e^{-βH^Φ}(e^{|β|D} − 1)`
  refine (abs_exp_sub_exp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  have habs : |(-β * Ψ.hamiltonian Λ x) - (-β * Φ.hamiltonian Λ x)|
      = |β| * |Ψ.hamiltonian Λ x - Φ.hamiltonian Λ x| := by
    rw [show -β * Ψ.hamiltonian Λ x - -β * Φ.hamiltonian Λ x
        = -(β * (Ψ.hamiltonian Λ x - Φ.hamiltonian Λ x)) by ring, abs_neg, abs_mul]
  have hle : |(-β * Ψ.hamiltonian Λ x) - (-β * Φ.hamiltonian Λ x)| ≤ |β| * Dv := by
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hDv x) (abs_nonneg β)
  exact sub_le_sub_right (Real.exp_le_exp.2 hle) 1

/-- **Georgii (4.19), quantitative uniform form.** If the Hamiltonian difference of two
absolutely summable potentials is uniformly bounded by `Dv` in the volume `Λ`, then their
Gibbsian specifications act on any bounded measurable observable within
`2‖f‖(e^{|β| Dv} − 1)` of each other, uniformly in the boundary condition. -/
theorem dist_action_gibbsSpecification_le (Λ : Finset S)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable ⇑f)
    {Dv : ℝ} (hDv : ∀ x, |Ψ.hamiltonian Λ x - Φ.hamiltonian Λ x| ≤ Dv) :
    dist ((gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β).action Λ f)
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)
      ≤ 2 * ‖f‖ * (Real.exp (|β| * Dv) - 1) := by
  have hE : Nonempty (S → E) := ⟨fun _ ↦ Nonempty.some (by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : ν (univ : Set E) = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 h] at h1
    simp at h1)⟩
  obtain ⟨η₀⟩ := hE
  have hDv0 : 0 ≤ Dv := le_trans (abs_nonneg _) (hDv η₀)
  have hC : 0 ≤ 2 * ‖f‖ * (Real.exp (|β| * Dv) - 1) := by
    have h1 : (1 : ℝ) ≤ Real.exp (|β| * Dv) := Real.one_le_exp (by positivity)
    have h2 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
    nlinarith
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le hC fun η ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Specification.action_apply, Specification.action_apply,
    Real.norm_eq_abs]
  exact abs_integral_gibbs_sub_le ν β Λ η hf
    (fun x ↦ by rw [← Real.norm_eq_abs]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero f x)
    hDv

end Main

/-! ### Georgii Proposition (4.19): uniform 𝓛-convergence -/

section Tendsto

variable (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
  {ι : Type*} {l : Filter ι} {Φs : ι → Potential S E} {Φ : Potential S E}
  [∀ i, (Φs i).IsPotential] [∀ i, (Φs i).IsAbsolutelySummable]
  [Φ.IsPotential] [Φ.IsAbsolutelySummable]

/-- **Georgii Proposition (4.19).** If the Hamiltonians of `(Φⁱ)` converge to those of `Φ`
uniformly in each volume, then the Gibbsian specifications converge uniformly in the
𝓛-topology on every bounded measurable observable. -/
theorem tendsto_dist_action_gibbsSpecification
    {D : ι → Finset S → ℝ}
    (hD : ∀ i (Λ : Finset S) (η : S → E),
      |(Φs i).hamiltonian Λ η - Φ.hamiltonian Λ η| ≤ D i Λ)
    (hD0 : ∀ Λ : Finset S, Tendsto (fun i ↦ D i Λ) l (𝓝 0))
    (Λ : Finset S) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable ⇑f) :
    Tendsto (fun i ↦ dist
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β).action Λ f)
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)) l (𝓝 0) := by
  have hbound : ∀ i, dist
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β).action Λ f)
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)
      ≤ 2 * ‖f‖ * (Real.exp (|β| * D i Λ) - 1) := fun i ↦
    dist_action_gibbsSpecification_le ν β Λ hf (hD i Λ)
  have hexp : Tendsto (fun i ↦ Real.exp (|β| * D i Λ) - 1) l (𝓝 0) := by
    have h1 : Tendsto (fun i ↦ |β| * D i Λ) l (𝓝 0) := by
      simpa using (hD0 Λ).const_mul |β|
    have h2 : Tendsto (fun i ↦ Real.exp (|β| * D i Λ)) l (𝓝 1) := by
      simpa [Real.exp_zero, Function.comp_def]
        using (Real.continuous_exp.tendsto 0).comp h1
    simpa using h2.sub_const 1
  refine squeeze_zero (fun i ↦ dist_nonneg) hbound ?_
  simpa using hexp.const_mul (2 * ‖f‖)

/-- **Georgii Proposition (4.19), 𝓛-form.** The conclusion restricted to local observables:
verbatim the `hunif` hypothesis of the repo's Georgii (4.17) and (4.22). -/
theorem tendsto_dist_action_gibbsSpecification_of_mem_localFunctions
    {D : ι → Finset S → ℝ}
    (hD : ∀ i (Λ : Finset S) (η : S → E),
      |(Φs i).hamiltonian Λ η - Φ.hamiltonian Λ η| ≤ D i Λ)
    (hD0 : ∀ Λ : Finset S, Tendsto (fun i ↦ D i Λ) l (𝓝 0)) :
    ∀ (Λ : Finset S) ⦃f : lp (fun _ : S → E ↦ ℝ) ∞⦄, f ∈ localFunctions S E →
      Tendsto (fun i ↦ dist
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β).action Λ f)
        ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)) l (𝓝 0) :=
  fun Λ f hf ↦ tendsto_dist_action_gibbsSpecification ν β hD hD0 Λ
    (measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hf))

/-- **Georgii Proposition (4.19), sup form.** With the hypothesis stated as in Georgii:
`lim_i ⨆_η |H^{Φⁱ}_Λ η − H^Φ_Λ η| = 0` for all `Λ`. The supremum is automatically finite
because absolutely summable potentials have uniformly bounded Hamiltonians (Georgii (2.14)). -/
theorem tendsto_dist_action_gibbsSpecification_of_tendsto_iSup
    (hconv : ∀ Λ : Finset S,
      Tendsto (fun i ↦ ⨆ η, |(Φs i).hamiltonian Λ η - Φ.hamiltonian Λ η|) l (𝓝 0))
    (Λ : Finset S) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable ⇑f) :
    Tendsto (fun i ↦ dist
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν β).action Λ f)
      ((gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).action Λ f)) l (𝓝 0) := by
  refine tendsto_dist_action_gibbsSpecification ν β
    (D := fun i Λ ↦ ⨆ η, |(Φs i).hamiltonian Λ η - Φ.hamiltonian Λ η|) ?_ hconv Λ hf
  intro i Λ' η
  have hbdd : BddAbove (Set.range fun ζ : S → E ↦
      |(Φs i).hamiltonian Λ' ζ - Φ.hamiltonian Λ' ζ|) := by
    refine ⟨(Φs i).hamiltonianBound Λ' + Φ.hamiltonianBound Λ', ?_⟩
    rintro _ ⟨ζ, rfl⟩
    exact (abs_sub _ _).trans (add_le_add (abs_hamiltonian_le _ _) (abs_hamiltonian_le _ _))
  exact le_ciSup hbdd η

end Tendsto

end Potential

end

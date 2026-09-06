/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic

/-!
# The mean ergodic theorem for correlations

Let an additive group `G` act on a finite measure space `(Ω, μ)` by measure-preserving maps, let
`𝓘 = MeasurableSpace.smulInvariants (Multiplicative G) Ω` be the σ-algebra of strictly invariant
events, and let `F : κ → Finset G` be a Følner net along a filter `l`. For a bounded measurable
observable `f : Ω → ℝ`, the Cesàro averages of the *spatial correlations*
`∫ f · (f ∘ (i +ᵥ ·)) dμ` converge:

`|F k|⁻¹ ∑_{i ∈ F k} ∫ f · (f ∘ (i +ᵥ ·)) dμ → ∫ (μ[f | 𝓘])² dμ`.

This is Georgii, *Gibbs Measures and Phase Transitions* (2nd ed.), display (16.23). The proof is
the `L¹` mean ergodic theorem
`MeasureTheory.tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp` (Georgii (14.A5)) — the
average of the translates converges to `μ[f | 𝓘]` in `L¹`, and pairing against the bounded
function `f` is `L¹`-continuous — together with the pull-out property of the conditional
expectation, which turns `∫ f · μ[f | 𝓘] dμ` into `∫ (μ[f | 𝓘])² dμ`.

## Main results

* `MeasureTheory.integral_mul_condExp_self`: `∫ f · μ[f | m] dμ = ∫ (μ[f | m])² dμ` for an
  integrable and a.e. bounded `f`. This is the statement that `μ[· | m]` is a self-adjoint
  idempotent — an orthogonal projection — read on integrals rather than on `L²`, where Mathlib
  records it as `MeasureTheory.inner_condExpL2_left_eq_right`.
* `MeasureTheory.tendsto_integral_mul_inv_card_smul_sum_vadd`: `∫ f · R_k f dμ → ∫ (μ[f | 𝓘])² dμ`
  for the ergodic averages `R_k f = |F k|⁻¹ ∑_{i ∈ F k} f ∘ (i +ᵥ ·)`.
* `MeasureTheory.tendsto_inv_card_sum_integral_mul_vadd`: **Georgii (16.23)**, the same limit
  written as a Cesàro average of the correlations `∫ f · (f ∘ (i +ᵥ ·)) dμ`.

## Hypotheses actually used

Boundedness of `f` is what makes the pairing `g ↦ ∫ f · g dμ` continuous on `L¹`, so that `L¹`
convergence of the ergodic averages suffices; `f ∈ L²` would do as well, at the price of running
the argument through the `L²` theorem. `IsFiniteMeasure μ`, `Countable G` and the Følner
hypotheses are exactly those of the mean ergodic theorem; see the module documentation of
`GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic` for why each is needed.
-/

@[expose] public section

open Filter Finset
open scoped Topology Pointwise symmDiff

namespace MeasureTheory

/-! ### The conditional expectation as an orthogonal projection -/

section CondExp

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → ℝ} {C : ℝ}

/-- **The conditional expectation is an orthogonal projection**, in integral form: for an
integrable, a.e. bounded `f`,

`∫ f · μ[f | m] dμ = ∫ (μ[f | m])² dμ`.

The proof is the pull-out property `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`,
which gives `μ[μ[f | m] · f | m] = (μ[f | m])²`, followed by `MeasureTheory.integral_condExp`.
Mathlib records the corresponding self-adjointness on `L²` as
`MeasureTheory.inner_condExpL2_left_eq_right`. -/
theorem integral_mul_condExp_self (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)
    (hfb : ∀ᵐ ω ∂μ, |f ω| ≤ C) :
    ∫ ω, f ω * (μ[f | m]) ω ∂μ = ∫ ω, ((μ[f | m]) ω) ^ 2 ∂μ := by
  have hfb' : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C := by
    filter_upwards [hfb] with ω hω
    rwa [Real.norm_eq_abs]
  have hb : ∀ᵐ ω ∂μ, ‖(μ[f | m]) ω‖ ≤ C := ae_bdd_norm_condExp_of_ae_bdd_norm hfb'
  have hmul : Integrable ((μ[f | m]) * f) μ :=
    hf.bdd_mul (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable hb
  calc ∫ ω, f ω * (μ[f | m]) ω ∂μ
      = ∫ ω, ((μ[f | m]) * f) ω ∂μ := by simp_rw [Pi.mul_apply, mul_comm]
    _ = ∫ ω, (condExp m μ ((μ[f | m]) * f)) ω ∂μ :=
        (integral_condExp (f := (μ[f | m]) * f) hm).symm
    _ = ∫ ω, ((μ[f | m]) ω) ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [condExp_mul_of_stronglyMeasurable_left stronglyMeasurable_condExp hmul hf]
          with ω hω
        rw [hω, Pi.mul_apply, sq]

end CondExp

/-! ### Correlations of an additive action -/

section Additive

variable {G : Type*} [AddGroup G] [DecidableEq G]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [AddAction G Ω]
  [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [IsFiniteMeasure μ] [Countable G]
  {κ : Type*} {l : Filter κ} {F : κ → Finset G}

omit [DecidableEq G] [VAddInvariantMeasure G Ω μ] [Countable G] in
/-- Every translate of a bounded measurable function is integrable for a finite measure. Unlike
`MeasureTheory.MeasurePreserving.integrable_comp_of_integrable`, this uses no invariance of `μ`. -/
lemma integrable_comp_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ C)
    (i : G) : Integrable (fun ω ↦ f (i +ᵥ ω)) μ :=
  .of_bound (hfm.comp (measurable_const_vadd i)).aestronglyMeasurable C
    (.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hfb (i +ᵥ ω))

omit [DecidableEq G] [VAddInvariantMeasure G Ω μ] [Countable G] in
/-- The correlation `ω ↦ f ω · f (i +ᵥ ω)` of a bounded measurable function is integrable. -/
lemma integrable_mul_comp_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ C)
    (i : G) : Integrable (fun ω ↦ f ω * f (i +ᵥ ω)) μ :=
  (integrable_comp_vadd hfm hfb i).bdd_mul hfm.aestronglyMeasurable
    (.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hfb ω)

omit [DecidableEq G] [VAddInvariantMeasure G Ω μ] [Countable G] in
/-- The ergodic average `|s|⁻¹ ∑_{i ∈ s} f ∘ (i +ᵥ ·)` of a bounded measurable function is
integrable. -/
lemma integrable_inv_card_smul_sum_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f)
    (hfb : ∀ ω, |f ω| ≤ C) (s : Finset G) :
    Integrable (fun ω ↦ (s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) μ := by
  simp only [smul_eq_mul]
  exact (integrable_finsetSum s fun i _ ↦ integrable_comp_vadd hfm hfb i).const_mul _

omit [DecidableEq G] [VAddInvariantMeasure G Ω μ] [Countable G] in
/-- Pairing `f` with the ergodic average over `s` is the average of the correlations: for a
bounded measurable `f`,

`∫ f · (|s|⁻¹ ∑_{i ∈ s} f ∘ (i +ᵥ ·)) dμ = |s|⁻¹ ∑_{i ∈ s} ∫ f · (f ∘ (i +ᵥ ·)) dμ`. -/
lemma integral_mul_inv_card_smul_sum_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f)
    (hfb : ∀ ω, |f ω| ≤ C) (s : Finset G) :
    ∫ ω, f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) ∂μ
      = (s.card : ℝ)⁻¹ * ∑ i ∈ s, ∫ ω, f ω * f (i +ᵥ ω) ∂μ := by
  have h : ∀ ω : Ω, f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω))
      = (s.card : ℝ)⁻¹ * ∑ i ∈ s, f ω * f (i +ᵥ ω) := fun ω ↦ by
    rw [smul_eq_mul, mul_left_comm, Finset.mul_sum]
  simp_rw [h]
  rw [integral_const_mul, integral_finsetSum s fun i _ ↦ integrable_mul_comp_vadd hfm hfb i]

omit [DecidableEq G] [VAddInvariantMeasure G Ω μ] [Countable G] in
/-- Pairing a bounded measurable `f` against an integrable `g` is `L¹`-continuous, with constant
the bound on `f`: the correlation average over `s` differs from `∫ f · g dμ` by at most
`C · ‖|s|⁻¹ ∑_{i ∈ s} f ∘ (i +ᵥ ·) - g‖₁`.

This is the estimate that turns the `L¹` mean ergodic theorem into a statement about
correlations. -/
lemma norm_integral_mul_inv_card_smul_sum_vadd_sub_integral_mul_le {f g : Ω → ℝ} {C : ℝ}
    (hfm : Measurable f) (hfb : ∀ ω, |f ω| ≤ C) (hg : Integrable g μ) (s : Finset G) :
    ‖∫ ω, f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) ∂μ - ∫ ω, f ω * g ω ∂μ‖
      ≤ C * ∫ ω, ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω) - g ω‖ ∂μ := by
  have hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C := .of_forall fun ω ↦ by
    rw [Real.norm_eq_abs]; exact hfb ω
  have hR : Integrable (fun ω ↦ (s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) μ :=
    integrable_inv_card_smul_sum_vadd hfm hfb s
  have h1 : Integrable (fun ω ↦ f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω))) μ :=
    hR.bdd_mul hfm.aestronglyMeasurable hb
  have h2 : Integrable (fun ω ↦ f ω * g ω) μ := hg.bdd_mul hfm.aestronglyMeasurable hb
  rw [← integral_sub h1 h2]
  calc ‖∫ ω, (f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) - f ω * g ω) ∂μ‖
      ≤ ∫ ω, ‖f ω * ((s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω)) - f ω * g ω‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, C * ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω) - g ω‖ ∂μ := by
        refine integral_mono (h1.sub h2).norm (((hR.sub hg).norm).const_mul C) fun ω ↦ ?_
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hfb ω)
          (norm_nonneg _)
    _ = C * ∫ ω, ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, f (i +ᵥ ω) - g ω‖ ∂μ := integral_const_mul _ _

variable (hne : ∀ᶠ k in l, (F k).Nonempty)
  (hF : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
include hne hF

/-- **Georgii (16.23)**, in the form in which it is proved: for a bounded measurable `f` and a
Følner net of finite sets, the pairings of `f` with its ergodic averages converge,

`∫ f · (|F k|⁻¹ ∑_{i ∈ F k} f ∘ (i +ᵥ ·)) dμ → ∫ (μ[f | 𝓘])² dμ`,

where `𝓘` is the invariant σ-algebra `MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
theorem tendsto_integral_mul_inv_card_smul_sum_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f)
    (hfb : ∀ ω, |f ω| ≤ C) :
    Tendsto (fun k ↦ ∫ ω, f ω * (((F k).card : ℝ)⁻¹ • ∑ i ∈ F k, f (i +ᵥ ω)) ∂μ) l
      (𝓝 (∫ ω, ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω) ^ 2 ∂μ)) := by
  have hfi : Integrable f μ :=
    .of_bound hfm.aestronglyMeasurable C (.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs]; exact hfb ω)
  rw [← integral_mul_condExp_self MeasurableSpace.smulInvariants_le hfi (.of_forall hfb),
    ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun k ↦
    norm_integral_mul_inv_card_smul_sum_vadd_sub_integral_mul_le hfm hfb integrable_condExp _) ?_
  simpa using
    (tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp hne hF hfi).const_mul C

/-- **Georgii (16.23), the mean ergodic theorem for correlations.** Let an additive group `G` act
on a finite measure space `(Ω, μ)` by measure-preserving maps and let `F` be a Følner net of
finite subsets of `G`. For a bounded measurable observable `f : Ω → ℝ`, the Cesàro averages of the
spatial correlations of `f` converge to the second moment of `μ[f | 𝓘]`:

`|F k|⁻¹ ∑_{i ∈ F k} ∫ f · (f ∘ (i +ᵥ ·)) dμ → ∫ (μ[f | 𝓘])² dμ`,

where `𝓘 = MeasurableSpace.smulInvariants (Multiplicative G) Ω` is Georgii's σ-algebra (14.2) of
strictly invariant events. -/
theorem tendsto_inv_card_sum_integral_mul_vadd {f : Ω → ℝ} {C : ℝ} (hfm : Measurable f)
    (hfb : ∀ ω, |f ω| ≤ C) :
    Tendsto (fun k ↦ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, ∫ ω, f ω * f (i +ᵥ ω) ∂μ) l
      (𝓝 (∫ ω, ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω) ^ 2 ∂μ)) := by
  simpa only [integral_mul_inv_card_smul_sum_vadd (μ := μ) hfm hfb] using
    tendsto_integral_mul_inv_card_smul_sum_vadd (μ := μ) hne hF hfm hfb

end Additive

end MeasureTheory

end

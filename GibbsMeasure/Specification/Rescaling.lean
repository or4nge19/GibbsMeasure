/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiWithDensity

/-!
# Rescaling the a priori measure of a λ-specification

Georgii, *Gibbs Measures and Phase Transitions*, works throughout with an a priori measure
`λ ∈ 𝓜(E, ℰ)` which is σ-finite with `λ(E) > 0`; the probability case is only a *normalization*,
justified by Remark (1.28)(3): if `λ̃ = r · λ` for a measurable `r > 0`, then

  `ρ̃_Λ(ω) = ρ_Λ(ω) / ∏_{i ∈ Λ} r(ω_i)`

is a `λ̃`-modification with `ρ̃ λ̃_· = ρ λ_·`; and since `λ ∈ 𝓜(E, ℰ)` one may choose `r > 0` with
`λ(r) = 1`, so that every λ-specification is a `λ̃`-specification for a probability measure `λ̃`.

This file formalizes that rescaling and uses it to remove the probability-measure restriction from
the λ-specification layer of `GibbsMeasure/Specification.lean`.

## Main definitions

* `Specification.lambdaWeight r Λ ω = ∏_{i ∈ Λ} r (ω i)`: the weight of Remark (1.28)(3).
* `Specification.rescale r ρ`: Georgii's `ρ̃`.
* `MeasureTheory.Measure.probNormalize`: the probability measure `λ(E)⁻¹ · λ` attached to a finite
  non-zero `λ`.
* `Specification.lambdaSpecification`: **Georgii Definition (1.27) via Remark (1.32)** — the
  λ-specification `(ρ_Λ / λ_Λ ρ_Λ) λ_·` of an admissible pre-modification, bundled as a
  `Specification`, for an arbitrary **σ-finite non-zero** a priori measure.

## Main results

* `MeasureTheory.Measure.exists_measurable_pos_isProbabilityMeasure_withDensity`: Georgii's choice
  of `r > 0` with `λ(r) = 1` for a σ-finite non-zero `λ`.
* `Specification.sigmaFiniteLambdaFun_withDensity`: `λ̃_Λ = (∏_{i ∈ Λ} r(ω_i)) · λ_Λ`, the kernel
  form of Notation (1.26) under rescaling.
* `Specification.isPremodifier_rescale`: `ρ̃` is a premodifier when `ρ` is.
* `Specification.modificationKer_sigmaFiniteLambdaFun_of_withDensity`: **Georgii Remark (1.28)(3)**,
  the invariance `ρ̃ λ̃_· = ρ λ_·`.
* `Specification.modificationKer_sigmaFiniteLambdaFun_of_smul`: the constant-rescaling case, in
  which the normalization already absorbs the constant, so `ρ` need not be modified at all.
* `Specification.isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero`:
  **DLR consistency of a normalized premodifier over an arbitrary σ-finite non-zero a priori
  measure**, obtained from the probability case by the rescaling. This removes the
  `[IsProbabilityMeasure ν]` hypothesis of
  `Specification.IsPremodifier.isConsistent_modificationKer_sigmaFinitePremodifierNorm`.
* `Specification.lambdaSpecification_probNormalize` and
  `Specification.lambdaSpecification_eq_modification_isssd`: the λ-specification of a finite `λ` is
  the λ-specification of `λ(E)⁻¹ · λ`, and for a probability measure it is the normalized
  modification of `Specification.isssd` used elsewhere in this development.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- Lean 4.34's module system does not unfold non-exposed mathlib defs during `isDefEq`.
set_option backward.isDefEq.respectTransparency false

open Finset Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### The rescaling weight of Georgii's Remark (1.28)(3) -/

variable (r : S → E → ℝ≥0∞) in
/-- Georgii, Remark (1.28)(3): the weight `∏_{i ∈ Λ} r_i(ω_i)` by which the reference kernel `λ_Λ`
changes when the a priori measure at site `i` is replaced by `r_i · λ`. Georgii's own rescaling is
the constant family. -/
noncomputable def lambdaWeight (Λ : Finset S) (ω : S → E) : ℝ≥0∞ := ∏ i ∈ Λ, r i (ω i)

variable {r : S → E → ℝ≥0∞}

lemma measurable_lambdaWeight (hr : ∀ i, Measurable (r i)) (Λ : Finset S) :
    Measurable (lambdaWeight (S := S) (E := E) r Λ) :=
  Finset.measurable_prod _ fun i _ ↦ (hr i).comp (measurable_pi_apply i)

lemma lambdaWeight_ne_zero (h0 : ∀ i x, r i x ≠ 0) (Λ : Finset S) (ω : S → E) :
    lambdaWeight (S := S) (E := E) r Λ ω ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _i _ ↦ h0 _ _

lemma lambdaWeight_ne_top (htop : ∀ i x, r i x ≠ ⊤) (Λ : Finset S) (ω : S → E) :
    lambdaWeight (S := S) (E := E) r Λ ω ≠ ⊤ :=
  ENNReal.prod_ne_top fun _i _ ↦ htop _ _

@[simp] lemma lambdaWeight_const (c : ℝ≥0∞) (Λ : Finset S) (ω : S → E) :
    lambdaWeight (S := S) (E := E) (fun _ _ ↦ c) Λ ω = c ^ Λ.card := by
  simp [lambdaWeight]

lemma lambdaWeight_juxt (Λ : Finset S) (η : S → E) (ζ : Λ → E) :
    lambdaWeight (S := S) (E := E) r Λ (juxt (Λ : Set S) η ζ) = ∏ i : Λ, r i (ζ i) := by
  classical
  rw [lambdaWeight, Finset.univ_eq_attach,
    ← Finset.prod_attach Λ (fun i ↦ r i (juxt (Λ : Set S) η ζ i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [juxt_apply_of_mem (show (i : S) ∈ (Λ : Set S) by simp)]
  congr 1

/-- Splitting the weight of a larger volume, when the two configurations agree outside the
smaller one. -/
lemma lambdaWeight_mul_comm_of_subset {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : S → E}
    (h : ∀ s ∉ Λ₁, ζ s = η s) :
    lambdaWeight (S := S) (E := E) r Λ₂ ζ * lambdaWeight (S := S) (E := E) r Λ₁ η =
      lambdaWeight (S := S) (E := E) r Λ₁ ζ * lambdaWeight (S := S) (E := E) r Λ₂ η := by
  classical
  have hsplit : ∀ ω : S → E, lambdaWeight (S := S) (E := E) r Λ₂ ω =
      lambdaWeight (S := S) (E := E) r Λ₁ ω * ∏ i ∈ Λ₂ \ Λ₁, r i (ω i) := by
    intro ω
    rw [lambdaWeight, lambdaWeight, ← Finset.prod_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hΛ]
  have hdiff : (∏ i ∈ Λ₂ \ Λ₁, r i (ζ i)) = ∏ i ∈ Λ₂ \ Λ₁, r i (η i) :=
    Finset.prod_congr rfl fun i hi ↦ by
      rw [h i (Finset.mem_sdiff.1 hi).2]
  rw [hsplit ζ, hsplit η, hdiff]
  ring


/-! ### Rescaling an arbitrary reference specification

Georgii Remark (1.28)(3) does not use the product structure of `λ_Λ`: all it needs is that the
new reference kernels are the old ones with a density that does not depend on the boundary
condition. -/

section RelRescale

variable {γ γ' : Specification S E} {ρ : Finset S → (S → E) → ℝ≥0∞}
  {W : Finset S → (S → E) → ℝ≥0∞}

/-- A constant factor drops out of the normalized density. -/
lemma relNorm_const_mul {c : Finset S → ℝ≥0∞} (hc0 : ∀ Λ, c Λ ≠ 0) (hctop : ∀ Λ, c Λ ≠ ⊤) :
    relNorm γ (fun Λ ω ↦ c Λ * ρ Λ ω) = relNorm γ ρ := by
  funext Λ η
  rw [relNorm, relNorm, relZ, relZ, lintegral_const_mul' _ _ (hctop Λ)]
  exact ENNReal.mul_div_mul_left _ _ (hc0 Λ) (hctop Λ)

/-- **Georgii Remark (1.28)(3), for an arbitrary reference specification.** If `γ'_Λ` is `γ_Λ` with
a boundary-independent density `W_Λ`, then dividing the premodifier by `W` leaves the normalized
specification unchanged. -/
theorem withDensity_relNorm_div (hγ' : ∀ (Λ : Finset S) (η : S → E),
      γ' Λ η = (γ Λ η).withDensity (W Λ))
    (hW : ∀ Λ, Measurable (W Λ)) (hW0 : ∀ Λ ω, W Λ ω ≠ 0) (hWtop : ∀ Λ ω, W Λ ω ≠ ⊤)
    (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) (η : S → E) :
    (γ' Λ η).withDensity (relNorm γ' (fun Λ ω ↦ ρ Λ ω / W Λ ω) Λ)
      = (γ Λ η).withDensity (relNorm γ ρ Λ) := by
  set ρ' : Finset S → (S → E) → ℝ≥0∞ := fun Λ ω ↦ ρ Λ ω / W Λ ω with hρ'
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) := fun Λ ↦ (hρ Λ).div (hW Λ)
  have hcancel : ∀ (Λ : Finset S) (ω : S → E), W Λ ω * ρ' Λ ω = ρ Λ ω := fun Λ ω ↦
    ENNReal.mul_div_cancel (hW0 Λ ω) (hWtop Λ ω)
  have hZ : ∀ ω, relZ γ' ρ' Λ ω = relZ γ ρ Λ ω := by
    intro ω
    rw [relZ, relZ, hγ' Λ ω, lintegral_withDensity_eq_lintegral_mul _ (hW Λ) (hρ'meas Λ)]
    exact lintegral_congr fun x ↦ hcancel Λ x
  rw [hγ' Λ η, ← withDensity_mul _ (hW Λ) (measurable_relNorm (γ := γ') hρ'meas Λ)]
  refine withDensity_congr_ae (.of_forall fun ω ↦ ?_)
  rw [Pi.mul_apply, relNorm, relNorm, hZ ω, mul_div_assoc', hcancel Λ ω]

/-- **Georgii Remark (1.28)(3) against the σ-finite reference kernel.** If the kernels of `γ'` are
those of the a priori measure `lam` times a boundary-independent density `W`, then dividing the
premodifier by `W` gives back the λ-specification of `lam`. -/
theorem withDensity_relNorm_div_sigmaFiniteLambdaFun (lam : Measure E) [SigmaFinite lam]
    {γ' : Specification S E} {W : Finset S → (S → E) → ℝ≥0∞}
    (hγ' : ∀ (Λ : Finset S) (η : S → E),
      γ' Λ η = (sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η).withDensity (W Λ))
    (hW : ∀ Λ, Measurable (W Λ)) (hW0 : ∀ Λ ω, W Λ ω ≠ 0) (hWtop : ∀ Λ ω, W Λ ω ≠ ⊤)
    (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) (η : S → E) :
    (γ' Λ η).withDensity (relNorm γ' (fun Λ ω ↦ ρ Λ ω / W Λ ω) Λ)
      = (sigmaFiniteLambdaFun (S := S) (E := E) lam Λ η).withDensity
          (sigmaFinitePremodifierNorm (S := S) (E := E) lam ρ Λ) := by
  set ρ' : Finset S → (S → E) → ℝ≥0∞ := fun Λ ω ↦ ρ Λ ω / W Λ ω with hρ'
  have hρ'meas : ∀ Λ, Measurable (ρ' Λ) := fun Λ ↦ (hρ Λ).div (hW Λ)
  have hcancel : ∀ (Λ : Finset S) (ω : S → E), W Λ ω * ρ' Λ ω = ρ Λ ω := fun Λ ω ↦
    ENNReal.mul_div_cancel (hW0 Λ ω) (hWtop Λ ω)
  have hZ : ∀ ω, relZ γ' ρ' Λ ω
      = sigmaFiniteLambdaZ (S := S) (E := E) lam ρ Λ ω := by
    intro ω
    rw [relZ, hγ' Λ ω, sigmaFiniteLambdaZ,
      lintegral_withDensity_eq_lintegral_mul _ (hW Λ) (hρ'meas Λ)]
    exact lintegral_congr fun x ↦ hcancel Λ x
  rw [hγ' Λ η, ← withDensity_mul _ (hW Λ) (measurable_relNorm (γ := γ') hρ'meas Λ)]
  refine withDensity_congr_ae (.of_forall fun ω ↦ ?_)
  rw [Pi.mul_apply, relNorm, sigmaFinitePremodifierNorm, hZ ω, mul_div_assoc', hcancel Λ ω]

end RelRescale

/-! ### Rescaling the a priori measure -/

variable {r : E → ℝ≥0∞}

/-- **Georgii, Notation (1.26) and Remark (1.28)(3).** Replacing the a priori measure `ν` by
`r · ν` multiplies the reference kernel `λ_Λ` by the weight `∏_{i ∈ Λ} r(ω_i)`. -/
lemma sigmaFiniteLambdaFun_withDensity (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) [SigmaFinite (ν.withDensity r)] (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) (ν.withDensity r) Λ η =
      (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity
        (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ) := by
  classical
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map]
  have hpi : (Measure.pi fun _ : Λ ↦ ν.withDensity r) =
      (Measure.pi fun _ : Λ ↦ ν).withDensity (fun ζ : Λ → E ↦ ∏ i : Λ, r (ζ i)) :=
    Measure.pi_withDensity (fun _ : Λ ↦ ν) (fun _ ↦ hr)
  have hfun : (fun ζ : Λ → E ↦ ∏ i : Λ, r (ζ i)) =
      fun ζ : Λ → E ↦ lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ (juxt (Λ : Set S) η ζ) :=
    funext fun ζ ↦ (lambdaWeight_juxt (S := S) (E := E) (r := fun _ ↦ r) Λ η ζ).symm
  rw [hpi, hfun, MeasureTheory.map_withDensity_comp (Measure.pi fun _ : Λ ↦ ν)
    (Measurable.juxt (Λ := (Λ : Set S)) (η := η) (𝓔 := mE))
    (measurable_lambdaWeight (S := S) (E := E) (fun _ ↦ hr) Λ)]

/-- Georgii, Remark (1.28)(3): the density family `ρ̃_Λ = ρ_Λ / ∏_{i ∈ Λ} r(ω_i)` associated to the
rescaled a priori measure `r · λ`. -/
noncomputable def rescale (r : E → ℝ≥0∞) (ρ : Finset S → (S → E) → ℝ≥0∞) :
    Finset S → (S → E) → ℝ≥0∞ := fun Λ ω ↦ ρ Λ ω / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω

lemma rescale_apply (r : E → ℝ≥0∞) (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (ω : S → E) :
    rescale (S := S) (E := E) r ρ Λ ω
      = ρ Λ ω / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω := rfl

lemma measurable_rescale (hr : Measurable r) (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Measurable (rescale (S := S) (E := E) r ρ Λ) :=
  (hρ Λ).div (measurable_lambdaWeight (S := S) (E := E) (fun _ ↦ hr) Λ)

/-- **Georgii, Remark (1.28)(3).** `ρ̃ = ρ / ∏ r` is a premodifier whenever `ρ` is, provided the
rescaling function `r` is everywhere positive and finite. -/
lemma isPremodifier_rescale (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    (hρ : IsPremodifier (S := S) (E := E) ρ) :
    IsPremodifier (S := S) (E := E) (rescale (S := S) (E := E) r ρ) where
  measurable Λ := measurable_rescale (S := S) (E := E) hr hρ.measurable Λ
  comm_of_subset := by
    intro Λ₁ Λ₂ ζ η hΛ hrestrict
    have hW := lambdaWeight_mul_comm_of_subset (S := S) (E := E) (r := fun _ ↦ r) hΛ hrestrict
    have hne : ∀ (Λ : Finset S) (ω : S → E),
        lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω ≠ 0 ∧
          lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω ≠ ⊤ :=
      fun Λ ω ↦ ⟨lambdaWeight_ne_zero (S := S) (E := E) (fun _ ↦ h0) Λ ω,
        lambdaWeight_ne_top (S := S) (E := E) (fun _ ↦ htop) Λ ω⟩
    have hinv : (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ ζ)⁻¹ *
          (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ η)⁻¹ =
        (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ ζ)⁻¹ *
          (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ η)⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inl (hne Λ₂ ζ).1) (Or.inl (hne Λ₂ ζ).2),
        ← ENNReal.mul_inv (Or.inl (hne Λ₁ ζ).1) (Or.inl (hne Λ₁ ζ).2), hW]
    simp only [rescale, ENNReal.div_eq_inv_mul]
    calc (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ ζ)⁻¹ * ρ Λ₂ ζ *
            ((lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ η)⁻¹ * ρ Λ₁ η)
        = ((lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ ζ)⁻¹ *
            (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ η)⁻¹) * (ρ Λ₂ ζ * ρ Λ₁ η) := by ring
      _ = ((lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ ζ)⁻¹ *
            (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ η)⁻¹) * (ρ Λ₁ ζ * ρ Λ₂ η) := by
            rw [hinv, hρ.comm_of_subset hΛ hrestrict]
      _ = (lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₁ ζ)⁻¹ * ρ Λ₁ ζ *
            ((lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ₂ η)⁻¹ * ρ Λ₂ η) := by ring

end Specification

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞} {r : E → ℝ≥0∞}

/-! ### Invariance of the λ-specification -/

/-- **Georgii, Remark (1.28)(3), unnormalized form.** Dividing a density by the rescaling weight
compensates exactly for replacing `λ` by `r · λ` in the reference kernel. -/
lemma withDensity_sigmaFiniteLambdaFun_withDensity_div (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] (Λ : Finset S) (η : S → E)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    (sigmaFiniteLambdaFun (S := S) (E := E) (ν.withDensity r) Λ η).withDensity
        (fun ω ↦ f ω / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω)
      = (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity f := by
  rw [sigmaFiniteLambdaFun_withDensity (S := S) (E := E) ν hr Λ η,
    show (fun ω ↦ f ω / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω) =
      f / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ from rfl,
    ← withDensity_mul _ (measurable_lambdaWeight (S := S) (E := E) (fun _ ↦ hr) Λ)
      (hf.div (measurable_lambdaWeight (S := S) (E := E) (fun _ ↦ hr) Λ))]
  congr 1
  funext ω
  simp only [Pi.mul_apply, Pi.div_apply, ENNReal.div_eq_inv_mul, ← mul_assoc]
  rw [ENNReal.mul_inv_cancel (lambdaWeight_ne_zero (S := S) (E := E) (fun _ ↦ h0) Λ ω)
    (lambdaWeight_ne_top (S := S) (E := E) (fun _ ↦ htop) Λ ω), one_mul]

/-- The integral form of `Specification.withDensity_sigmaFiniteLambdaFun_withDensity_div`. -/
lemma lintegral_sigmaFiniteLambdaFun_withDensity_div (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] (Λ : Finset S) (η : S → E)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f ω / lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω
        ∂(sigmaFiniteLambdaFun (S := S) (E := E) (ν.withDensity r) Λ η)
      = ∫⁻ ω, f ω ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  have h := congrArg (fun m : Measure (S → E) ↦ m Set.univ)
    (withDensity_sigmaFiniteLambdaFun_withDensity_div
      (S := S) (E := E) ν hr h0 htop Λ η hf)
  simpa [withDensity_apply _ MeasurableSet.univ] using h

/-- **Georgii, Remark (1.28)(3).** The partition function is unchanged by the rescaling. -/
lemma sigmaFiniteLambdaZ_rescale (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) (ν.withDensity r)
        (rescale (S := S) (E := E) r ρ) Λ η
      = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η :=
  lintegral_sigmaFiniteLambdaFun_withDensity_div
    (S := S) (E := E) ν hr h0 htop Λ η (hρ Λ)

lemma isSigmaFiniteLambdaAdmissible_rescale (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] (hρ : ∀ Λ, Measurable (ρ Λ)) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) (ν.withDensity r)
        (rescale (S := S) (E := E) r ρ)
      ↔ IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ := by
  constructor <;> intro h Λ η <;>
    simpa [sigmaFiniteLambdaZ_rescale (S := S) (E := E) ν hr h0 htop hρ Λ η] using h Λ η

/-- The normalized rescaled density is the rescaling of the normalized density. -/
lemma sigmaFinitePremodifierNorm_rescale (ν : Measure E) [SigmaFinite ν]
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    sigmaFinitePremodifierNorm (S := S) (E := E) (ν.withDensity r)
        (rescale (S := S) (E := E) r ρ) Λ
      = fun ω ↦ sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ ω /
          lambdaWeight (S := S) (E := E) (fun _ ↦ r) Λ ω := by
  funext ω
  rw [sigmaFinitePremodifierNorm, sigmaFinitePremodifierNorm,
    sigmaFiniteLambdaZ_rescale (S := S) (E := E) ν hr h0 htop hρ Λ ω, rescale_apply]
  simp only [ENNReal.div_eq_inv_mul]
  ring

/-- Two modifications with the same density family agree. -/
lemma modificationKer_congr
    (γ : ∀ Λ : Finset S, Kernel[cylinderEvents (Λ : Set S)ᶜ] (S → E) (S → E))
    {ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞} (h : ρ₁ = ρ₂)
    (h₁ : ∀ Λ, Measurable (ρ₁ Λ)) (h₂ : ∀ Λ, Measurable (ρ₂ Λ)) :
    modificationKer γ ρ₁ h₁ = modificationKer γ ρ₂ h₂ := by
  subst h; rfl

/-- **Georgii, Remark (1.28)(3): the λ-specification is unchanged by rescaling the a priori
measure.** If `λ̃ = r · λ` with `r > 0` finite and `ρ̃_Λ = ρ_Λ / ∏_{i ∈ Λ} r(ω_i)`, then
`ρ̃ λ̃_· = ρ λ_·`: the two normalized modifications are the same family of kernels. -/
theorem modificationKer_sigmaFiniteLambdaFun_of_withDensity (ν ν' : Measure E)
    [SigmaFinite ν] [SigmaFinite ν']
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    (hν' : ν' = ν.withDensity r) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hm₁ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν'
      (rescale (S := S) (E := E) r ρ) Λ))
    (hm₂ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ)) :
    modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν')
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν'
          (rescale (S := S) (E := E) r ρ)) hm₁
      = modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ) hm₂ := by
  subst hν'
  funext Λ
  ext η A hA
  rw [modificationKer_apply, modificationKer_apply,
    sigmaFinitePremodifierNorm_rescale (S := S) (E := E) ν hr h0 htop hρ Λ,
    withDensity_sigmaFiniteLambdaFun_withDensity_div (S := S) (E := E) ν hr h0 htop Λ η (hm₂ Λ)]

/-! ### Constant rescaling: reduction to a probability a priori measure -/

/-- Dividing a density family by the constant `c ^ |Λ|` does not change the normalized density. -/
lemma sigmaFinitePremodifierNorm_rescale_const (ν : Measure E) [SigmaFinite ν]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (rescale (S := S) (E := E) (fun _ ↦ c) ρ)
      = sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ := by
  funext Λ ω
  have hd0 : (c ^ Λ.card) ≠ 0 := pow_ne_zero _ hc0
  have hdt : (c ^ Λ.card) ≠ ⊤ := ENNReal.pow_ne_top hct
  have hZ : sigmaFiniteLambdaZ (S := S) (E := E) ν
        (rescale (S := S) (E := E) (fun _ ↦ c) ρ) Λ ω
      = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω * (c ^ Λ.card)⁻¹ := by
    rw [sigmaFiniteLambdaZ, sigmaFiniteLambdaZ]
    simp only [rescale, lambdaWeight_const, div_eq_mul_inv]
    exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hd0)
  rw [sigmaFinitePremodifierNorm, sigmaFinitePremodifierNorm, hZ, rescale_apply,
    lambdaWeight_const, div_eq_mul_inv (ρ Λ ω)]
  exact ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.2 hdt) (ENNReal.inv_ne_top.2 hd0)

/-- **Georgii, Remark (1.28)(3), constant rescaling.** Scaling the a priori measure by a constant
leaves the normalized λ-specification unchanged: the normalization absorbs the constant, so the
density family need not be modified at all. -/
theorem modificationKer_sigmaFiniteLambdaFun_of_smul (ν ν' : Measure E)
    [SigmaFinite ν] [SigmaFinite ν'] {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hν' : ν' = c • ν) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hm₁ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν' ρ Λ))
    (hm₂ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ)) :
    modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν')
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν' ρ) hm₁
      = modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ) hm₂ := by
  have hν'2 : ν' = ν.withDensity (fun _ ↦ c) := by rw [hν', withDensity_const]
  have hcongr := sigmaFinitePremodifierNorm_rescale_const (S := S) (E := E) (ρ := ρ) ν' hc0 hct
  have hm₁' : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν'
      (rescale (S := S) (E := E) (fun _ ↦ c) ρ) Λ) := by
    intro Λ; rw [hcongr]; exact hm₁ Λ
  rw [← modificationKer_congr (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν') hcongr hm₁' hm₁]
  exact modificationKer_sigmaFiniteLambdaFun_of_withDensity (S := S) (E := E) ν ν'
    measurable_const (fun _ ↦ hc0) (fun _ ↦ hct) hν'2 hρ hm₁' hm₂

end Specification

namespace MeasureTheory.Measure

variable {E : Type*} [MeasurableSpace E]

/-- The probability measure obtained from a finite non-zero measure by rescaling its total mass to
`1`. This is the choice of `r` in Georgii's Remark (1.28)(3) in the case of a finite `λ`. -/
noncomputable def probNormalize (ν : Measure E) : Measure E := (ν Set.univ)⁻¹ • ν

lemma probNormalize_def (ν : Measure E) : ν.probNormalize = (ν Set.univ)⁻¹ • ν := rfl

/-- `probNormalize` is Mathlib's conditional probability `ν[|Set.univ]`, so the
`ProbabilityTheory.cond` API applies to it. -/
lemma probNormalize_eq_cond_univ (ν : Measure E) :
    ν.probNormalize = ProbabilityTheory.cond ν Set.univ := by
  rw [probNormalize_def, ProbabilityTheory.cond, Measure.restrict_univ]

instance isProbabilityMeasure_probNormalize (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] :
    IsProbabilityMeasure ν.probNormalize := by
  constructor
  have h0 : ν Set.univ ≠ 0 := by
    simpa using (NeZero.ne ν) ∘ Measure.measure_univ_eq_zero.mp
  rw [probNormalize_def, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 (measure_ne_top ν _)

/-- `ν` is recovered from its normalization by scaling with the total mass. -/
lemma smul_probNormalize (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] :
    ν = (ν Set.univ) • ν.probNormalize := by
  have h0 : ν Set.univ ≠ 0 := by
    simpa using (NeZero.ne ν) ∘ Measure.measure_univ_eq_zero.mp
  rw [probNormalize_def, smul_smul, ENNReal.mul_inv_cancel h0 (measure_ne_top ν _), one_smul]

end MeasureTheory.Measure

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### Scaling the a priori measure -/

lemma sigmaFiniteLambdaFun_of_smul (ν ν' : Measure E) [SigmaFinite ν] [SigmaFinite ν']
    {c : ℝ≥0∞} (hν' : ν' = c • ν) (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν' Λ η
      = c ^ Λ.card • sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η := by
  have h2 : ν' = ν.withDensity (fun _ ↦ c) := by rw [hν', withDensity_const]
  subst h2
  rw [sigmaFiniteLambdaFun_withDensity (S := S) (E := E) ν measurable_const Λ η,
    show lambdaWeight (S := S) (E := E) (fun _ _ ↦ c) Λ = fun _ : S → E ↦ c ^ Λ.card from
      funext fun ω ↦ lambdaWeight_const (S := S) (E := E) c Λ ω,
    withDensity_const]

lemma sigmaFiniteLambdaZ_of_smul (ν ν' : Measure E) [SigmaFinite ν] [SigmaFinite ν']
    {c : ℝ≥0∞} (hν' : ν' = c • ν) (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν' ρ Λ η
      = c ^ Λ.card * sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η := by
  rw [sigmaFiniteLambdaZ, sigmaFiniteLambdaZ,
    sigmaFiniteLambdaFun_of_smul (S := S) (E := E) ν ν' hν' Λ η, lintegral_smul_measure]
  rfl

lemma isSigmaFiniteLambdaAdmissible_of_smul (ν ν' : Measure E) [SigmaFinite ν] [SigmaFinite ν']
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) (hν' : ν' = c • ν) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν' ρ
      ↔ IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ := by
  constructor <;> intro h Λ η <;>
    · have hz := sigmaFiniteLambdaZ_of_smul (S := S) (E := E) (ρ := ρ) ν ν' hν' Λ η
      have h0 : (c ^ Λ.card) ≠ 0 := pow_ne_zero _ hc0
      have ht : (c ^ Λ.card) ≠ ⊤ := ENNReal.pow_ne_top hct
      obtain ⟨ha, hb⟩ := h Λ η
      rw [hz] at *
      refine ⟨?_, ?_⟩ <;> simp_all [ENNReal.mul_eq_top, mul_eq_zero]

end Specification

namespace MeasureTheory.Measure

variable {E : Type*} [MeasurableSpace E]

/-- **Georgii, Remark (1.28)(3): "we can choose a function `r > 0` with `λ(r) = 1` because
`λ ∈ 𝓜(E, ℰ)`."** Every σ-finite non-zero measure becomes a probability measure after
multiplication by an everywhere positive and finite measurable density. -/
theorem exists_measurable_pos_isProbabilityMeasure_withDensity (ν : Measure E) [SigmaFinite ν]
    [NeZero ν] :
    ∃ r : E → ℝ≥0∞, Measurable r ∧ (∀ x, r x ≠ 0) ∧ (∀ x, r x ≠ ⊤) ∧
      IsProbabilityMeasure (ν.withDensity r) := by
  obtain ⟨g, hgpos, hgmeas, hgint⟩ :=
    exists_pos_lintegral_lt_of_sigmaFinite ν (ε := 1) one_ne_zero
  set G : E → ℝ≥0∞ := fun x ↦ (g x : ℝ≥0∞) with hG
  have hGmeas : Measurable G := hgmeas.coe_nnreal_ennreal
  have hG0 : ∀ x, G x ≠ 0 := fun x ↦ by
    simpa [hG, ENNReal.coe_eq_zero] using (hgpos x).ne'
  have hGtop : ∀ x, G x ≠ ⊤ := fun _ ↦ ENNReal.coe_ne_top
  set c : ℝ≥0∞ := ∫⁻ x, G x ∂ν with hc
  have hcTop : c ≠ ⊤ := (lt_of_lt_of_le hgint le_top).ne
  have hc0 : c ≠ 0 := by
    intro h0
    rw [hc, lintegral_eq_zero_iff hGmeas] at h0
    have hset : ν {x : E | ¬ G x = 0} = 0 := by
      simpa using (MeasureTheory.ae_iff.mp h0)
    rw [show {x : E | ¬ G x = 0} = Set.univ from Set.eq_univ_of_forall fun x ↦ hG0 x] at hset
    exact (NeZero.ne ν) (Measure.measure_univ_eq_zero.mp hset)
  refine ⟨fun x ↦ G x / c, hGmeas.div_const c, fun x ↦ ?_, fun x ↦ ?_, ?_⟩
  · exact ENNReal.div_ne_zero.2 ⟨hG0 x, hcTop⟩
  · exact (ENNReal.div_lt_top (hGtop x) hc0).ne
  · constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ x, G x / c ∂ν = (∫⁻ x, G x ∂ν) / c := by
          simp only [div_eq_mul_inv]
          exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)
      _ = 1 := ENNReal.div_self hc0 hcTop

end MeasureTheory.Measure

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-! ### λ-specifications for a finite a priori measure -/

lemma univ_ne_zero_of_neZero (ν : Measure E) [NeZero ν] : ν Set.univ ≠ 0 := by
  simpa using (NeZero.ne ν) ∘ Measure.measure_univ_eq_zero.mp

/-- **Georgii, Remark (1.28)(3) for a finite a priori measure.** The normalized λ-specification of
a premodifier is the same whether it is computed with a finite non-zero `ν` or with the
probability measure obtained from `ν` by rescaling its total mass to `1`. -/
theorem modificationKer_sigmaFiniteLambdaFun_probNormalize (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (hρ : ∀ Λ, Measurable (ρ Λ))
    (hm₁ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ))
    (hm₂ : ∀ Λ, Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν.probNormalize ρ Λ)) :
    modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ) hm₁
      = modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν.probNormalize)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν.probNormalize ρ) hm₂ :=
  modificationKer_sigmaFiniteLambdaFun_of_smul (S := S) (E := E) ν.probNormalize ν
    (univ_ne_zero_of_neZero ν) (measure_ne_top ν _) (Measure.smul_probNormalize ν) hρ hm₁ hm₂

/-- Admissibility of a premodifier is invariant under normalizing the a priori measure. -/
lemma isSigmaFiniteLambdaAdmissible_probNormalize (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν.probNormalize ρ
      ↔ IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ :=
  (isSigmaFiniteLambdaAdmissible_of_smul (S := S) (E := E) (ρ := ρ) ν.probNormalize ν
      (univ_ne_zero_of_neZero ν) (measure_ne_top ν _) (Measure.smul_probNormalize ν)).symm

/-- **Georgii, Remark (1.32) (proved via Proposition (1.30)) together with Remark (1.28)(3).**
The normalized modification of
the reference kernels of *any* σ-finite non-zero a priori measure is consistent. The
probability-measure case is transported along the rescaling `λ̃ = r · λ` with `λ(r) = 1`, whose
existence is `MeasureTheory.Measure.exists_measurable_pos_isProbabilityMeasure_withDensity`. -/
theorem isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    IsConsistent
      (modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
        (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)) := by
  obtain ⟨r, hr, h0, htop, hprob⟩ :=
    Measure.exists_measurable_pos_isProbabilityMeasure_withDensity ν
  have := hprob
  have hρ' : IsPremodifier (S := S) (E := E) (rescale (S := S) (E := E) r ρ) :=
    isPremodifier_rescale (S := S) (E := E) hr h0 htop hρ
  have hZ' : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) (ν.withDensity r)
      (rescale (S := S) (E := E) r ρ) :=
    (isSigmaFiniteLambdaAdmissible_rescale (S := S) (E := E) ν hr h0 htop hρ.measurable).2 hZ
  rw [← modificationKer_sigmaFiniteLambdaFun_of_withDensity (S := S) (E := E) ν
    (ν.withDensity r) hr h0 htop rfl hρ.measurable
    (sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
      (ρ := rescale (S := S) (E := E) r ρ) (ν.withDensity r) hρ')
    (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)]
  exact IsPremodifier.isConsistent_modificationKer_sigmaFinitePremodifierNorm
    (S := S) (E := E) (ρ := rescale (S := S) (E := E) r ρ) (ν := ν.withDensity r) hρ' hZ'

/-- **Georgii, Remark (1.32) for a finite a priori measure.** -/
theorem isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_isFiniteMeasure
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    IsConsistent
      (modificationKer (γ := sigmaFiniteLambdaFun (S := S) (E := E) ν)
        (ρ := sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ)
        (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)) :=
  isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero
    (S := S) (E := E) ν hρ hZ

/-- **Georgii, Definition (1.27) via Remark (1.32).** The λ-specification `(ρ_Λ / λ_Λ ρ_Λ) λ_·`
attached to a pre-modification `ρ` admissible for an arbitrary σ-finite non-zero a priori measure
`ν`, bundled as a `Specification`.

The consistency of the family is the content of
`Specification.isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero`; the underlying
kernels are `Specification.sigmaFinitePremodifierKernel`, whose Markov property and properness
hold for every σ-finite `ν`. -/
noncomputable def lambdaSpecification (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (ρ : Finset S → (S → E) → ℝ≥0∞) (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) : Specification S E where
  toPreSpecification :=
    { toFun := sigmaFinitePremodifierKernel (S := S) (E := E) ν ρ hρ
      isConsistent' :=
        isConsistent_modificationKer_sigmaFinitePremodifierNorm_of_neZero
          (S := S) (E := E) ν hρ hZ }
  isMarkovKernel' := fun Λ ↦
    isMarkovKernel_sigmaFinitePremodifierKernel (S := S) (E := E) (ρ := ρ) ν hρ hZ Λ
  isProper' := fun Λ ↦
    isProper_sigmaFinitePremodifierKernel (S := S) (E := E) (ρ := ρ) ν hρ Λ

@[simp] lemma lambdaSpecification_apply (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (Λ : Finset S) (η : S → E) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ η
      = (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity
        (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ) := rfl

lemma coe_lambdaSpecification (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (Λ : Finset S) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ
      = sigmaFinitePremodifierKernel (S := S) (E := E) ν ρ hρ Λ := rfl

/-- **Georgii, Remark (1.28)(3).** The λ-specification of a finite non-zero a priori measure is the
λ-specification of the associated probability measure. -/
theorem lambdaSpecification_probNormalize (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (hZ' : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν.probNormalize ρ) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
      = lambdaSpecification (S := S) (E := E) ν.probNormalize ρ hρ hZ' := by
  refine Specification.ext fun Λ ↦ ?_
  rw [coe_lambdaSpecification, coe_lambdaSpecification]
  exact congrFun (modificationKer_sigmaFiniteLambdaFun_probNormalize (S := S) (E := E) ν
    hρ.measurable _ _) Λ

end Specification

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- For a probability a priori measure the λ-specification is the normalized modification of the
independent specification `isssd ν`, i.e. `(isssd ν).modification (premodifierNorm ν ρ)`. -/
theorem lambdaSpecification_eq_modification_isssd (ν : Measure E) [IsProbabilityMeasure ν]
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
      = (isssd (S := S) (E := E) ν).modification
        (premodifierNorm (S := S) (E := E) ν ρ)
        (IsPremodifier.isModifier_premodifierNorm (S := S) (E := E) ν hρ
          ((isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible
            (S := S) (E := E) ν ρ).2 hZ)) := by
  refine Specification.ext fun Λ ↦ ?_
  ext η A hA
  rw [lambdaSpecification_apply, modification_apply,
    premodifierNorm_eq_sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ]
  congr 1
  rw [sigmaFiniteLambdaFun_eq_finiteLambdaFun (S := S) (E := E) ν Λ,
    finiteLambdaFun_eq_isssdFun (S := S) (E := E) ν Λ]
  rfl

end Specification

end

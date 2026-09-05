/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.DobrushinUniqueness

/-!
# Georgii §8.2: the covariance estimate under Dobrushin's condition

Georgii's Proposition (8.34) bounds the covariances of the unique Gibbs measure of a
specification satisfying Dobrushin's condition (8.6):
`|μ(fg) − μ(f)μ(g)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`,
where `D(γ) = ∑_{n ≥ 0} C(γ)^n` is Georgii's (8.19) and `δ_i` is the single-site oscillation
(8.14).

Georgii's proof tilts the specification by `g`: `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`, notes
that `μ̃ = g μ` is Gibbs for `γ̃`, and applies the comparison theorem (8.20) with
`b_j = δ_j(g) / 4 γ_j g`.

## Main results

* `MeasureTheory.GibbsMeasure.Dobrushin.unifDist_withDensity_le`: Georgii's elementary estimate
  `‖uα − α‖ ≤ δ(u)/4` for a probability density `u` on a probability space.
* `MeasureTheory.GibbsMeasure.Dobrushin.ofReal_abs_covariance_le`: **Georgii, Proposition
  (8.34)**.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Dobrushin

/-! ### The elementary density estimate `‖uα − α‖ ≤ δ(u)/4` -/

section DensityEstimate

variable {X : Type*} [MeasurableSpace X]

/-- **Georgii, proof of Proposition (8.34)**, the elementary estimate: if `u ≥ 0` is a
probability density with respect to the probability measure `α` whose oscillation is at most `d`,
then `‖uα − α‖ ≤ d/4` in the uniform distance (8.1).

Georgii argues via `α(|u − 1|) ≤ α((u − m)²)^{1/2}`; the argument below is the equivalent
two-block estimate `∫_A u dα − α(A) = α(A) α(Aᶜ) (u|_A − u|_{Aᶜ}) ≤ α(A) α(Aᶜ) d ≤ d/4`. -/
theorem unifDist_withDensity_le (α : Measure X) [IsProbabilityMeasure α] {u : X → ℝ}
    (hum : Measurable u) (hu0 : ∀ x, 0 ≤ u x) {d : ℝ} (hd : ∀ x y, u x - u y ≤ d)
    (hu1 : ∫ x, u x ∂α = 1) :
    unifDist (α.withDensity fun x ↦ ENNReal.ofReal (u x)) α ≤ ENNReal.ofReal (d / 4) := by
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    simp only [not_nonempty_iff] at hX
    have : (univ : Set X) = ∅ := Set.eq_empty_of_isEmpty _
    simpa [this] using measure_univ (μ := α)
  have hd0 : 0 ≤ d := by simpa using hd x₀ x₀
  have hbdd : ∀ x, u x ≤ u x₀ + d := fun x ↦ by linarith [hd x x₀]
  have hint : Integrable u α :=
    ⟨hum.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := |u x₀| + |d|)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]
        calc u x ≤ u x₀ + d := hbdd x
          _ ≤ |u x₀| + |d| := add_le_add (le_abs_self _) (le_abs_self _))⟩
  refine unifDist_le fun A hA ↦ ?_
  have hIA : IntegrableOn u A α := hint.integrableOn
  have hIAc : IntegrableOn u Aᶜ α := hint.integrableOn
  have hcA : IntegrableOn (fun _ : X ↦ (1 : ℝ)) A α := (integrable_const 1).integrableOn
  set t : ℝ := α.real A with ht
  set s : ℝ := α.real Aᶜ with hs
  set p : ℝ := ∫ x in A, u x ∂α with hp
  set q : ℝ := ∫ x in Aᶜ, u x ∂α with hq
  have ht0 : 0 ≤ t := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hts : t + s = 1 := by
    rw [ht, hs, measureReal_add_measureReal_compl hA, measureReal_def, measure_univ,
      ENNReal.toReal_one]
  have hpq : p + q = 1 := by rw [hp, hq, integral_add_compl hA hint, hu1]
  -- `p − t = s p − t q`, and the latter is an integral of an integrand bounded by `s d`.
  have hkey : p - t = s * p - t * q := by linear_combination t * hpq - p * hts
  have hstep : ∀ x, s * u x - q ≤ s * d := by
    intro x
    have hconst : ∫ _y in Aᶜ, u x ∂α = s * u x := by
      rw [setIntegral_const, hs, smul_eq_mul]
    have hsub : s * u x - q = ∫ y in Aᶜ, (u x - u y) ∂α := by
      rw [← hconst, hq, ← integral_sub ((integrable_const (u x)).integrableOn) hIAc]
    rw [hsub]
    calc ∫ y in Aᶜ, (u x - u y) ∂α ≤ ∫ _y in Aᶜ, d ∂α :=
          setIntegral_mono (((integrable_const (u x)).integrableOn).sub hIAc)
            ((integrable_const d).integrableOn)
            (fun y ↦ hd x y)
      _ = s * d := by rw [setIntegral_const, hs, smul_eq_mul]
  have hbound : p - t ≤ d / 4 := by
    have h1 : s * p - t * q = ∫ x in A, (s * u x - q) ∂α := by
      rw [integral_sub (hIA.const_mul s) ((integrable_const q).integrableOn),
        integral_const_mul, setIntegral_const, ← hp, ← ht, smul_eq_mul]
    have h2 : ∫ x in A, (s * u x - q) ∂α ≤ t * (s * d) := by
      calc ∫ x in A, (s * u x - q) ∂α ≤ ∫ _x in A, s * d ∂α :=
            setIntegral_mono ((hIA.const_mul s).sub ((integrable_const q).integrableOn))
              ((integrable_const (s * d)).integrableOn) hstep
        _ = t * (s * d) := by rw [setIntegral_const, ← ht, smul_eq_mul]
    have hts4 : t * s ≤ 1 / 4 := by nlinarith [sq_nonneg (t - s)]
    have h3 : t * (s * d) ≤ d / 4 := by
      calc t * (s * d) = (t * s) * d := by ring
        _ ≤ (1 / 4) * d := by nlinarith
        _ = d / 4 := by ring
    rw [hkey, h1]; exact h2.trans h3
  -- transport the real inequality to `ℝ≥0∞`
  have hwd : (α.withDensity fun x ↦ ENNReal.ofReal (u x)) A = ENNReal.ofReal p := by
    rw [withDensity_apply _ hA, hp,
      ofReal_integral_eq_lintegral_ofReal hIA (Filter.Eventually.of_forall hu0)]
  have hαA : α A = ENNReal.ofReal t := by
    rw [ht, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top α A)]
  rw [hwd, hαA, ← ENNReal.ofReal_sub _ ht0]
  exact ENNReal.ofReal_le_ofReal hbound

end DensityEstimate

end MeasureTheory.GibbsMeasure.Dobrushin

/-! ### Normalizing a single density volume by volume

Georgii, proof of (8.34): `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`. This is
`Specification.relNorm` of the constant family `ρ_Λ = g`, which is a premodifier with a *trivial*
cocycle (1.31), so `Specification.IsPremodifier.isModifier_relNorm` applies without its
resampling hypothesis. -/

namespace Specification

variable {S E : Type*} [MeasurableSpace E] (γ : Specification S E)

/-- **Georgii, Remark (1.32) for a constant premodifier.** If `0 < γ_Λ g < ∞` for every finite
volume `Λ`, then `h_Λ = g / γ_Λ g` is a modifier of `γ`; the cocycle condition (1.31) of
`Specification.IsPremodifier` is trivially satisfied by a family that does not depend on `Λ`, so
unlike `Specification.IsPremodifier.isModifier_relNorm` this needs no resampling hypothesis. -/
theorem isModifier_relNorm_const {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) : γ.IsModifier (relNorm γ fun _ ↦ g) := by
  have hρm : ∀ Λ : Finset S, Measurable ((fun _ : Finset S ↦ g) Λ) := fun _ ↦ hg
  refine (isModifier_iff_ae_eq (γ := γ)).2
    ⟨measurable_relNorm (γ := γ) hρm, lintegral_relNorm (γ := γ) hρm hZ,
      fun Λ₁ Λ₂ hΛ η ↦ .of_forall fun ω ↦ ?_⟩
  have hinner : ∫⁻ ζ, relNorm γ (fun _ ↦ g) Λ₂ ζ ∂(γ Λ₁ ω)
      = (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω := by
    have hae : ∀ᵐ ζ ∂(γ Λ₁ ω), relNorm γ (fun _ ↦ g) Λ₂ ζ
        = (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ζ := by
      filter_upwards [relZ_ae_eq (γ := γ) hρm hΛ ω] with ζ hζ
      rw [relNorm, hζ, ENNReal.div_eq_inv_mul]
    rw [lintegral_congr_ae hae, lintegral_const_mul _ hg]
    rfl
  have hcancel : (relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω = 1 :=
    ENNReal.inv_mul_cancel (hZ Λ₁ ω).1 (hZ Λ₁ ω).2
  show relNorm γ (fun _ ↦ g) Λ₂ ω
      = relNorm γ (fun _ ↦ g) Λ₁ ω * ∫⁻ ζ, relNorm γ (fun _ ↦ g) Λ₂ ζ ∂(γ Λ₁ ω)
  rw [hinner, relNorm, relNorm, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  calc (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ω
      = ((relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω)
          * ((relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ω) := by rw [hcancel, one_mul]
    _ = (relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * g ω
          * ((relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω) := by ring

/-- **Georgii, proof of (8.34):** the specification `γ̃` obtained from `γ` by tilting with the
density `g`, i.e. `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`. -/
noncomputable def tilt {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) : Specification S E :=
  γ.modification (relNorm γ fun _ ↦ g) (isModifier_relNorm_const γ hg hZ)

@[simp] lemma tilt_apply {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) (Λ : Finset S) (η : S → E) :
    γ.tilt hg hZ Λ η = (γ Λ η).withDensity (relNorm γ (fun _ ↦ g) Λ) := rfl

end Specification

namespace MeasureTheory.GibbsMeasure.Dobrushin

/-! ### Georgii's Proposition (8.34): the covariance estimate -/

section Covariance

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {g : (S → E) → ℝ} {m M : ℝ}

variable (γ) in
/-- A strictly positive bounded observable has strictly positive finite partition functions in
every finite volume, so it normalizes to a modifier of `γ`. -/
lemma isRelAdmissible_ofReal (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M) :
    Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ) := by
  refine fun Λ η ↦ ⟨?_, ?_⟩
  · have hle : ENNReal.ofReal m ≤ ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) := by
      calc ENNReal.ofReal m = ∫⁻ _σ, ENNReal.ofReal m ∂(γ Λ η) := by simp
        _ ≤ _ := lintegral_mono fun σ ↦ ENNReal.ofReal_le_ofReal (hmg σ)
    intro h
    rw [show Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) Λ η
      = ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) from rfl] at h
    rw [h, le_zero_iff] at hle
    exact (ENNReal.ofReal_pos.2 hm).ne' hle
  · have hle : ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) ≤ ENNReal.ofReal M :=
      calc ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η)
          ≤ ∫⁻ _σ, ENNReal.ofReal M ∂(γ Λ η) :=
            lintegral_mono fun σ ↦ ENNReal.ofReal_le_ofReal (hgM σ)
        _ = ENNReal.ofReal M := by simp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- A bounded measurable observable is integrable against every finite-volume kernel. -/
lemma integrable_of_bounded (hgm : Measurable g) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (Λ : Finset S) (η : S → E) : Integrable g (γ Λ η) :=
  ⟨hgm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := |m| + |M|)
    (Filter.Eventually.of_forall fun σ ↦ by
      rw [Real.norm_eq_abs]
      rcases abs_cases (g σ) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; calc g σ ≤ M := hgM σ
          _ ≤ |m| + |M| := by
              have := abs_nonneg m; have := le_abs_self M; linarith
      · rw [h]; calc -g σ ≤ -m := by linarith [hmg σ]
          _ ≤ |m| + |M| := by
              have := abs_nonneg M; have := neg_le_abs m; linarith)⟩

variable (γ) in
/-- Georgii's `γ_Λ g` in its two readings: the `ℝ≥0∞`-valued partition function of the density
`ofReal ∘ g` is `ofReal` of the Bochner integral of `g`. -/
lemma relZ_ofReal_eq (hgm : Measurable g) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (hm : 0 < m) (Λ : Finset S) (ω : S → E) :
    Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) Λ ω
      = ENNReal.ofReal (∫ σ, g σ ∂(γ Λ ω)) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded hgm hmg hgM Λ ω)
    (Filter.Eventually.of_forall fun σ ↦ le_trans hm.le (hmg σ))).symm

/-- **Georgii, proof of (8.34):** if `μ` is Gibbs for `γ` in the volume `Λ`, then `μ̃ = g μ` is
Gibbs for the tilted specification `γ̃ = h γ` with `h_Λ = g / γ_Λ g`. Georgii's computation
`μ̃ γ̃_Λ (f) = μ γ_Λ(g γ_Λ(fg)/γ_Λ g) = μ γ_Λ(fg) = μ̃(f)`, in set form. -/
theorem bind_tilt_eq {μ : Measure (S → E)} {ĝ : (S → E) → ℝ≥0∞} (hĝm : Measurable ĝ)
    (hZ : Specification.IsRelAdmissible γ fun _ ↦ ĝ) {Λ : Finset S} (hμ : μ.bind (γ Λ) = μ) :
    (μ.withDensity ĝ).bind (γ.tilt hĝm hZ Λ) = μ.withDensity ĝ := by
  classical
  set Z : (S → E) → ℝ≥0∞ := Specification.relZ γ (fun _ ↦ ĝ) Λ with hZdef
  have hZmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Z :=
    Specification.measurable_relZ (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) Λ
  have hbase : AEMeasurable ((γ Λ : Kernel[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
      (S → E) (S → E)) : (S → E) → Measure (S → E)) μ :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  refine Measure.ext fun A hA ↦ ?_
  set N : (S → E) → ℝ≥0∞ := fun ω ↦ ∫⁻ y in A, ĝ y ∂(γ Λ ω) with hNdef
  have hNmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] N :=
    hĝm.setLIntegral_kernel hA
  have hNm : Measurable N := hNmB.mono cylinderEvents_le_pi le_rfl
  have hkerA : AEMeasurable ((γ.tilt hĝm hZ Λ :
      Kernel[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] (S → E) (S → E)) :
      (S → E) → Measure (S → E)) (μ.withDensity ĝ) :=
    (((γ.tilt hĝm hZ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hcoeA : Measurable fun ω ↦ (γ.tilt hĝm hZ Λ ω) A :=
    (Kernel.measurable_coe (γ.tilt hĝm hZ Λ) hA).mono cylinderEvents_le_pi le_rfl
  have h1 : ∫⁻ ω, (γ.tilt hĝm hZ Λ ω) A ∂(μ.withDensity ĝ)
      = ∫⁻ ω, ((Z ω)⁻¹ * N ω) * ĝ ω ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hĝm hcoeA]
    refine lintegral_congr fun ω ↦ ?_
    rw [Pi.mul_apply, Specification.tilt_apply,
      Specification.withDensity_relNorm_apply (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) hA ω]
    ring
  have h2 : ∫⁻ ω, ((Z ω)⁻¹ * N ω) * ĝ ω ∂μ = ∫⁻ ξ, N ξ ∂μ := by
    conv_lhs => rw [← hμ]
    have hmul : Measurable fun ω ↦ (Z ω)⁻¹ * N ω * ĝ ω :=
      (((hZmB.inv.fun_mul hNmB).mono cylinderEvents_le_pi le_rfl)).fun_mul hĝm
    rw [Measure.lintegral_bind hbase hmul.aemeasurable]
    refine lintegral_congr fun ξ ↦ ?_
    rw [(γ.isProper Λ).lintegral_mul (f := ĝ) (g := fun x ↦ (Z x)⁻¹ * N x)
      cylinderEvents_le_pi hĝm (hZmB.inv.fun_mul hNmB) ξ]
    have hZξ : ∫⁻ x, ĝ x ∂(γ Λ ξ) = Z ξ := rfl
    rw [hZξ]
    calc (Z ξ)⁻¹ * N ξ * Z ξ = ((Z ξ)⁻¹ * Z ξ) * N ξ := by ring
      _ = N ξ := by rw [ENNReal.inv_mul_cancel (hZ Λ ξ).1 (hZ Λ ξ).2, one_mul]
  have h3 : ∫⁻ ξ, N ξ ∂μ = (μ.withDensity ĝ) A := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    have hind : ∀ ξ, N ξ = ∫⁻ y, A.indicator ĝ y ∂(γ Λ ξ) := fun ξ ↦ by
      rw [hNdef, lintegral_indicator hA]
    rw [lintegral_congr hind, ← Measure.lintegral_bind hbase (hĝm.indicator hA).aemeasurable, hμ]
  rw [Measure.bind_apply hA hkerA, h1, h2, h3]

variable [DecidableEq S]

/-- Properness turns an `ℝ≥0∞`-integral against `γ_i(·|ω)` into the integral of the section
`x ↦ f(x ω_{S∖i})` against the projection `γ_i^0(·|ω)` of Georgii (8.4); the `ℝ≥0∞` counterpart
of `MeasureTheory.GibbsMeasure.Dobrushin.integral_eq_integral_proj`. -/
lemma lintegral_eq_lintegral_proj (γ : Specification S E) (i : S) (ω : S → E)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂(γ {i} ω) = ∫⁻ x, f (Function.update ω i x) ∂(proj γ i ω) := by
  have hT : Measurable fun σ : S → E ↦ Function.update ω i (σ i) := measurable_updateAt i ω
  have hU : Measurable fun x : E ↦ Function.update ω i x := measurable_updateOf i ω
  conv_lhs => rw [← map_updateAt_eq γ i ω]
  rw [lintegral_map hf hT, proj,
    lintegral_map (f := fun x ↦ f (Function.update ω i x)) (hf.comp hU) (measurable_pi_apply i)]

/-- **Georgii, proof of (8.34):** the `σ_i`-projection (8.4) of the tilted single-site kernel is
the projection of `γ_i` with the density `x ↦ g(x ω_{S∖i}) / γ_i g(ω)`. -/
theorem proj_tilt_eq {ĝ : (S → E) → ℝ≥0∞} (hĝm : Measurable ĝ)
    (hZ : Specification.IsRelAdmissible γ fun _ ↦ ĝ) (i : S) (ω : S → E) :
    proj (γ.tilt hĝm hZ) i ω
      = (proj γ i ω).withDensity fun x ↦
          ĝ (Function.update ω i x) / Specification.relZ γ (fun _ ↦ ĝ) {i} ω := by
  classical
  set Z : ℝ≥0∞ := Specification.relZ γ (fun _ ↦ ĝ) {i} ω with hZω
  refine Measure.ext fun A hA ↦ ?_
  have hpre : MeasurableSet ((fun σ : S → E ↦ σ i) ⁻¹' A) := hA.preimage (measurable_pi_apply i)
  have hsec : ∫⁻ y in (fun σ : S → E ↦ σ i) ⁻¹' A, ĝ y ∂(γ {i} ω)
      = ∫⁻ x in A, ĝ (Function.update ω i x) ∂(proj γ i ω) := by
    rw [← lintegral_indicator hpre, ← lintegral_indicator hA,
      lintegral_eq_lintegral_proj γ i ω (hĝm.indicator hpre)]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (by simpa using hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (by simpa using hx), Set.indicator_of_notMem hx]
  rw [proj, Measure.map_apply (measurable_pi_apply i) hA, Specification.tilt_apply,
    Specification.withDensity_relNorm_apply (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) hpre ω,
    withDensity_apply _ hA, hsec, ← hZω,
    ← lintegral_const_mul (f := fun x ↦ ĝ (Function.update ω i x)) _
      (hĝm.comp (measurable_updateOf i ω))]
  exact lintegral_congr fun x ↦ ENNReal.div_eq_inv_mul.symm

/-- **Georgii, proof of (8.34):** the function `b_j(ω) = δ_j(g) / 4 γ_j g(ω)` dominates the
uniform distance (8.1) `‖γ_j^0(·|ω) − γ̃_j^0(·|ω)‖` between the single-site projections (8.4) of
`γ` and of its tilt by `g`.

This is Georgii's chain `‖uα − α‖ ≤ δ(u)/4` (`unifDist_withDensity_le`) applied to the section
`u(x) = g(x ω_{S∖j}) / γ_j g(ω)` of the tilting density. -/
theorem unifDist_proj_tilt_le (hgm : Measurable g) (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ)
    (hgM : ∀ σ, g σ ≤ M)
    (hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ)) (i : S) (ω : S → E) :
    unifDist (proj γ i ω) (proj (γ.tilt hgm.ennreal_ofReal hZ) i ω)
      ≤ oscAt g i / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω) := by
  classical
  have hgpos : ∀ σ, 0 < g σ := fun σ ↦ lt_of_lt_of_le hm (hmg σ)
  have habs : ∀ σ, |g σ| ≤ M := fun σ ↦ by rw [abs_of_pos (hgpos σ)]; exact hgM σ
  have hoscne : oscAt g i ≠ ⊤ := oscAt_ne_top_of_bounded habs
  set δ : ℝ := (oscAt g i).toReal with hδdef
  have hδ : oscAt g i = ENNReal.ofReal δ := (ENNReal.ofReal_toReal hoscne).symm
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  set Zr : ℝ := ∫ σ, g σ ∂(γ {i} ω) with hZr
  have hint : Integrable g (γ {i} ω) := integrable_of_bounded (γ := γ) hgm hmg hgM {i} ω
  have hZrpos : 0 < Zr := by
    have hmZ : m ≤ Zr := by
      calc m = ∫ _σ : S → E, m ∂(γ {i} ω) := by simp
        _ ≤ Zr := integral_mono (integrable_const m) hint hmg
    exact lt_of_lt_of_le hm hmZ
  have hZeq : Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω
      = ENNReal.ofReal Zr := relZ_ofReal_eq γ hgm hmg hgM hm {i} ω
  set u : E → ℝ := fun x ↦ g (Function.update ω i x) / Zr with hu
  have hum : Measurable u := (hgm.comp (measurable_updateOf i ω)).div_const _
  have hu0 : ∀ x, 0 ≤ u x := fun x ↦ le_of_lt (div_pos (hgpos _) hZrpos)
  have hsec : ∫ x, g (Function.update ω i x) ∂(proj γ i ω) = Zr :=
    (integral_eq_integral_proj γ i ω hgm).symm
  have hu1 : ∫ x, u x ∂(proj γ i ω) = 1 := by
    rw [hu, integral_div, hsec, div_self hZrpos.ne']
  have hdd : ∀ x y, u x - u y ≤ δ / Zr := by
    intro x y
    have hnum : g (Function.update ω i x) - g (Function.update ω i y) ≤ δ := by
      have hle : ENNReal.ofReal |g (Function.update ω i x) - g (Function.update ω i y)|
          ≤ oscAt g i :=
        le_oscAt fun k hk ↦ by rw [Function.update_of_ne hk, Function.update_of_ne hk]
      have := (ENNReal.ofReal_le_iff_le_toReal hoscne).1 hle
      exact le_trans (le_abs_self _) this
    rw [hu, div_sub_div_same]
    gcongr
  have hproj : proj (γ.tilt hgm.ennreal_ofReal hZ) i ω
      = (proj γ i ω).withDensity fun x ↦ ENNReal.ofReal (u x) := by
    rw [proj_tilt_eq (hĝm := hgm.ennreal_ofReal) hZ i ω]
    refine congrArg _ (funext fun x ↦ ?_)
    rw [hu, ENNReal.ofReal_div_of_pos hZrpos, hZeq]
  have hkey := unifDist_withDensity_le (proj γ i ω) hum hu0 hdd hu1
  rw [unifDist_comm, hproj]
  refine hkey.trans (le_of_eq ?_)
  have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal Zr = ENNReal.ofReal (4 * Zr) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  rw [hZeq, hδ, h4, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

omit [DecidableEq S] in
/-- **Georgii, proof of (8.34):** `μ̃(b_j) = δ_j(g)/4`. Since `μ̃ = g μ`, `μ γ_j = μ` and
`γ_j(g / γ_j g) = 1` by properness, the boundary-dependent normalization integrates out. -/
theorem lintegral_oscAt_div_eq {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hgm : Measurable g) (hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ))
    (j : S) (hμ : μ.bind (γ {j}) = μ) :
    ∫⁻ ω, oscAt g j / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {j} ω)
        ∂(μ.withDensity fun σ ↦ ENNReal.ofReal (g σ)) = oscAt g j / 4 := by
  classical
  have hĝm : Measurable fun σ ↦ ENNReal.ofReal (g σ) := hgm.ennreal_ofReal
  set Z : (S → E) → ℝ≥0∞ := Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {j} with hZdef
  have hZmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((({j} : Finset S) : Set S)ᶜ)] Z :=
    Specification.measurable_relZ (γ := γ) (ρ := fun _ σ ↦ ENNReal.ofReal (g σ))
      (fun _ ↦ hĝm) {j}
  have hZm : Measurable Z := hZmB.mono cylinderEvents_le_pi le_rfl
  have hsplit : ∀ ω, oscAt g j / (4 * Z ω) = (oscAt g j / 4) * (Z ω)⁻¹ := by
    intro ω
    rw [div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc]
  have hprod : Measurable fun ω ↦ (Z ω)⁻¹ * ENNReal.ofReal (g ω) := hZm.inv.fun_mul hĝm
  have hbase : AEMeasurable ((γ {j} : Kernel[cylinderEvents (X := fun _ : S ↦ E)
      ((({j} : Finset S) : Set S)ᶜ)] (S → E) (S → E)) : (S → E) → Measure (S → E)) μ :=
    (((γ {j}).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hone : ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂μ = 1 := by
    conv_lhs => rw [← hμ]
    rw [Measure.lintegral_bind hbase hprod.aemeasurable]
    have hinner : ∀ ξ : S → E,
        ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂(γ {j} ξ) = 1 := by
      intro ξ
      rw [(γ.isProper {j}).lintegral_mul (f := fun σ ↦ ENNReal.ofReal (g σ))
        (g := fun ω ↦ (Z ω)⁻¹) cylinderEvents_le_pi hĝm hZmB.inv ξ]
      exact ENNReal.inv_mul_cancel (hZ {j} ξ).1 (hZ {j} ξ).2
    rw [lintegral_congr hinner, lintegral_one, measure_univ]
  calc ∫⁻ ω, oscAt g j / (4 * Z ω) ∂(μ.withDensity fun σ ↦ ENNReal.ofReal (g σ))
      = ∫⁻ ω, ENNReal.ofReal (g ω) * ((oscAt g j / 4) * (Z ω)⁻¹) ∂μ := by
        rw [lintegral_congr hsplit, lintegral_withDensity_eq_lintegral_mul _ hĝm
          (show Measurable fun ω ↦ oscAt g j / 4 * (Z ω)⁻¹ from
            measurable_const.fun_mul hZm.inv)]
        rfl
    _ = (oscAt g j / 4) * ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂μ := by
        rw [← lintegral_const_mul _ hprod]
        exact lintegral_congr fun ω ↦ by ring
    _ = oscAt g j / 4 := by rw [hone, mul_one]

/-- **Georgii, Proposition (8.34)** for a strictly positive `g` normalized by `μ(g) = 1`:
`|μ(fg) − μ(f)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`. -/
theorem ofReal_abs_integral_mul_sub_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    (hgm : Measurable g) (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (hg1 : ∫ σ, g σ ∂μ = 1) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * g σ ∂μ) - ∫ σ, (f : (S → E) → ℝ) σ ∂μ|
      ≤ (∑' i, interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) / 4 := by
  classical
  have hĝm : Measurable fun σ ↦ ENNReal.ofReal (g σ) := hgm.ennreal_ofReal
  have hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ) :=
    isRelAdmissible_ofReal γ hm hmg hgM
  set ν : Measure (S → E) := μ.withDensity (fun σ ↦ ENNReal.ofReal (g σ)) with hνdef
  have hgint : Integrable g μ := ⟨hgm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := |m| + |M|) (Filter.Eventually.of_forall fun σ ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hm (hmg σ))]
      calc g σ ≤ M := hgM σ
        _ ≤ |m| + |M| := by have := abs_nonneg m; have := le_abs_self M; linarith)⟩
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall fun σ ↦ le_trans hm.le (hmg σ)), hg1, ENNReal.ofReal_one]
  have hν : ∀ i : S, ν.bind (γ.tilt hĝm hZ {i}) = ν := fun i ↦ bind_tilt_eq hĝm hZ (hμ i)
  set b : S → (S → E) → ℝ≥0∞ := fun i ω ↦
    oscAt g i / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω) with hbdef
  have hbm : ∀ i, Measurable (b i) := fun i ↦
    measurable_const.div (measurable_const.mul
      ((Specification.measurable_relZ (γ := γ) (ρ := fun _ σ ↦ ENNReal.ofReal (g σ))
        (fun _ ↦ hĝm) {i}).mono cylinderEvents_le_pi le_rfl))
  have hb : ∀ i ω, unifDist (proj γ i ω) (proj (γ.tilt hĝm hZ) i ω) ≤ b i ω :=
    fun i ω ↦ unifDist_proj_tilt_le hgm hm hmg hgM hZ i ω
  have hcomp := comparison (γ := γ) (γ' := γ.tilt hĝm hZ) (μ := μ) (ν := ν) hγq hd hμ hν hbm hb
  have hbt : ∀ j, (∫⁻ ω, b j ω ∂ν) = 4⁻¹ * oscAt g j := by
    intro j
    rw [hbdef, lintegral_oscAt_div_eq hgm hZ j (hμ j), div_eq_mul_inv, mul_comm]
  have hfun : (fun j ↦ ∫⁻ ω, b j ω ∂ν) = fun j ↦ 4⁻¹ * oscAt g j := funext hbt
  have hest := (hcomp.isEstimate) f hf
  rw [hfun] at hest
  have hνint : ∫ σ, (f : (S → E) → ℝ) σ ∂ν = ∫ σ, (f : (S → E) → ℝ) σ * g σ ∂μ := by
    rw [hνdef, show (fun σ ↦ ENNReal.ofReal (g σ))
        = fun σ ↦ ((Real.toNNReal (g σ) : ℝ≥0) : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hgm.real_toNNReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ ↦ ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_trans hm.le (hmg σ)), mul_comm]
  rw [hνint] at hest
  rw [abs_sub_comm] at hest
  refine hest.trans (le_of_eq ?_)
  calc (∑' i, interdepSeries γ (fun j ↦ 4⁻¹ * oscAt g j) i * oscAt (⇑f) i)
      = ∑' i, 4⁻¹ * (interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) := by
        refine tsum_congr fun i ↦ ?_
        rw [interdepSeries_const_mul, mul_assoc]
    _ = (∑' i, interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) / 4 := by
        rw [ENNReal.tsum_mul_left, div_eq_mul_inv, mul_comm]

end Covariance

/-! ### Georgii, Proposition (8.34) -/

section Prop834

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] {γ : Specification S E}
  {μ : Measure (S → E)}

/-- **Georgii, Proposition (8.34).** If `γ` is quasilocal and satisfies Dobrushin's condition
(8.6) and `μ` is (the unique) Gibbs measure for `γ`, then for all quasilocal observables `f, g`

`|μ(fg) − μ(f)μ(g)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`,

where `D(γ) = ∑_{n≥0} C(γ)^n` is Georgii's (8.19) (`interdepSeries`) and `δ_i` is the single-site
oscillation (8.14).

Georgii's proof, followed here: both sides are invariant under `g ↦ (g + c)/K`, so one may assume
`g > 0` and `μ(g) = 1`; then `μ̃ = g μ` is Gibbs for the tilted specification
`γ̃_Λ = (g/γ_Λ g) γ_Λ` (`Specification.tilt`, `bind_tilt_eq`), whose single-site projections
satisfy `‖γ_j^0(·|ω) − γ̃_j^0(·|ω)‖ ≤ δ_j(g)/4 γ_j g(ω)` (`unifDist_proj_tilt_le`), and the
comparison theorem (8.20) applies with `μ̃(b_j) = δ_j(g)/4` (`lintegral_oscAt_div_eq`). -/
theorem ofReal_abs_covariance_le [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
      ≤ (∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 := by
  classical
  have hgm : Measurable (⇑g) := measurable_of_mem_quasilocalFunctions hg
  have hfm : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  have hgb : ∀ σ, |(g : (S → E) → ℝ) σ| ≤ ‖g‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g σ
  have hfb : ∀ σ, |(f : (S → E) → ℝ) σ| ≤ ‖f‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f σ
  have hgint : Integrable (⇑g) μ := ⟨hgm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hgb σ)⟩
  have hfint : Integrable (⇑f) μ := ⟨hfm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ‖f‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hfb σ)⟩
  have hfgint : Integrable (fun σ ↦ (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ) μ :=
    ⟨(hfm.mul hgm).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ‖f‖ * ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfb σ) (hgb σ) (abs_nonneg _) (norm_nonneg f))⟩
  set c : ℝ := ‖g‖ + 1 with hcdef
  have hnormg : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hlow : ∀ σ, (1 : ℝ) ≤ (g : (S → E) → ℝ) σ + c := fun σ ↦ by
    have h1 := neg_abs_le ((g : (S → E) → ℝ) σ)
    have h2 := hgb σ
    rw [hcdef]; linarith
  have hupp : ∀ σ, (g : (S → E) → ℝ) σ + c ≤ 2 * ‖g‖ + 1 := fun σ ↦ by
    have h2 := (abs_le.1 (hgb σ)).2
    rw [hcdef]; linarith
  have hunivreal : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hIg : |∫ σ, (g : (S → E) → ℝ) σ ∂μ| ≤ ‖g‖ := by
    rw [← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hgb σ)
    rwa [hunivreal, mul_one] at h
  set K : ℝ := (∫ σ, (g : (S → E) → ℝ) σ ∂μ) + c with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have := (abs_le.1 hIg).1; rw [hKdef, hcdef]; linarith
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  set G : (S → E) → ℝ := fun σ ↦ ((g : (S → E) → ℝ) σ + c) / K with hGdef
  have hGm : Measurable G := (hgm.add_const c).div_const K
  have hGlow : ∀ σ, 1 / K ≤ G σ := fun σ ↦ by
    show (1 : ℝ) / K ≤ ((g : (S → E) → ℝ) σ + c) / K
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hlow σ) (inv_nonneg.2 hKpos.le)
  have hGupp : ∀ σ, G σ ≤ (2 * ‖g‖ + 1) / K := fun σ ↦ by
    show ((g : (S → E) → ℝ) σ + c) / K ≤ (2 * ‖g‖ + 1) / K
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hupp σ) (inv_nonneg.2 hKpos.le)
  have hG1 : ∫ σ, G σ ∂μ = 1 := by
    show (∫ σ, ((g : (S → E) → ℝ) σ + c) / K ∂μ) = 1
    rw [integral_div, integral_add hgint (integrable_const c), integral_const, hunivreal,
      one_smul, ← hKdef, div_self hKpos.ne']
  have hmain := ofReal_abs_integral_mul_sub_le (γ := γ) (μ := μ) hγq hd hμ hGm
    (one_div_pos.2 hKpos) hGlow hGupp hG1 hf
  -- rewrite the two sides
  have hfG : ∫ σ, (f : (S → E) → ℝ) σ * G σ ∂μ
      = ((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          + c * ∫ σ, (f : (S → E) → ℝ) σ ∂μ) / K := by
    have hpt : ∀ σ, (f : (S → E) → ℝ) σ * G σ
        = ((f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ + c * (f : (S → E) → ℝ) σ) / K := by
      intro σ; rw [hGdef]; field_simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
      integral_add hfgint (hfint.const_mul c), integral_const_mul]
  have hdiff : (∫ σ, (f : (S → E) → ℝ) σ * G σ ∂μ) - ∫ σ, (f : (S → E) → ℝ) σ ∂μ
      = ((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ) / K := by
    rw [hfG, eq_div_iff hKpos.ne', sub_mul, div_mul_cancel₀ _ hKpos.ne', hKdef]; ring
  have hoscG : ∀ j, oscAt G j = (ENNReal.ofReal K)⁻¹ * oscAt (⇑g) j := by
    intro j
    have hfun : G = fun σ ↦ K⁻¹ * (g : (S → E) → ℝ) σ + c / K := by
      funext σ; rw [hGdef]; field_simp
    rw [hfun, oscAt_affine _ (inv_ne_zero hKpos.ne') _ j,
      abs_of_pos (inv_pos.2 hKpos), ENNReal.ofReal_inv_of_pos hKpos]
  rw [hdiff] at hmain
  -- cancel the factor `K`
  have hRHS : (∑' i, interdepSeries γ (fun j ↦ oscAt G j) i * oscAt (⇑f) i) / 4
      = (ENNReal.ofReal K)⁻¹
        * ((∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4) := by
    have hstep : ∀ i, interdepSeries γ (fun j ↦ oscAt G j) i * oscAt (⇑f) i
        = (ENNReal.ofReal K)⁻¹
          * (interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) := by
      intro i
      rw [funext hoscG, interdepSeries_const_mul, mul_assoc]
    rw [tsum_congr hstep, ENNReal.tsum_mul_left, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  have hLHS : ENNReal.ofReal
      (|((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ) / K|)
      = (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal
          |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
            - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ| := by
    rw [abs_div, abs_of_pos hKpos, ENNReal.ofReal_div_of_pos hKpos, ENNReal.div_eq_inv_mul]
  rw [hLHS, hRHS] at hmain
  have hKne : ENNReal.ofReal K ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.2 hKpos).ne'
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.2 hKne)).1 hmain

/-- **Georgii, Proposition (8.34)**, in the summable form used in his proof of Corollary (8.37):
if `c(γ) ≤ c` then

`|μ(fg) − μ(f)μ(g)| ≤ (sup_j δ_j(g)) (∑_i δ_i(f)) / 4(1 − c)`,

because Dobrushin's condition bounds the row sums of `D(γ)` by `(1 − c)⁻¹`
(`interdepSeries_le`). -/
theorem ofReal_abs_covariance_le_of_iSup [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ) {c : ℝ≥0∞}
    (hc : ∀ i, ∑' j, interdep γ i j ≤ c)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
      ≤ (⨆ j, oscAt (⇑g) j) * (∑' i, oscAt (⇑f) i) / (4 * (1 - c)) := by
  refine (ofReal_abs_covariance_le hγq hd hμ hf hg).trans ?_
  have hrow : ∀ i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i ≤ (⨆ j, oscAt (⇑g) j) / (1 - c) :=
    fun i ↦ interdepSeries_le γ hc (fun j ↦ le_iSup (fun j ↦ oscAt (⇑g) j) j) i
  calc (∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4
      ≤ (∑' i, ((⨆ j, oscAt (⇑g) j) / (1 - c)) * oscAt (⇑f) i) / 4 := by
        gcongr with i
        exact hrow i
    _ = ((⨆ j, oscAt (⇑g) j) / (1 - c)) * (∑' i, oscAt (⇑f) i) / 4 := by
        rw [ENNReal.tsum_mul_left]
    _ = (⨆ j, oscAt (⇑g) j) * (∑' i, oscAt (⇑f) i) / (4 * (1 - c)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ring

end Prop834

end MeasureTheory.GibbsMeasure.Dobrushin

end

end

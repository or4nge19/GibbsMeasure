/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithDensity
public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.Existence

/-!
# Georgii, Theorem (1.33): a specification is determined by its singleton part

Let `λ` be a probability measure on `E` with independent specification `λ_· = isssd λ`
(Georgii allows a σ-finite reference measure and reduces to this case by Remark (1.28)(3)).
Suppose `γ` is a specification such that for each site `i` there is a measurable `ρ_i` with
`0 < ρ_i < ∞` and `γ_{i} = ρ_i λ_{i}`. Then there is a positive `λ`-modification `ρ` with
`γ = ρ λ_·`, `γ` is uniquely determined by its singleton kernels `(γ_{i})_i`, and `𝒢(γ)` is the
set of probability measures `μ` with `μ γ_{i} = μ` for all `i`, equivalently `μ = ρ_i (μ λ_{i})`
for all `i`.

Following Georgii, one constructs by induction on `|Λ|` a positive density `ρ_Λ` from the
singleton densities such that `μ = ρ_Λ (μ λ_Λ)` for every finite measure `μ` invariant under the
singleton kernels `γ_{i}`, `i ∈ Λ`. The auxiliary results are stated for an arbitrary base
specification `lam` satisfying Georgii's identity `lam_Δ lam_Λ = lam_{Δ ∪ Λ}` for disjoint
`Λ, Δ` (`IsDisjointlyConsistent`), and then specialised to `isssd ν`.
-/

@[expose] public section

open ProbabilityTheory Set MeasureTheory ENNReal

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {γ lam : Specification S E} {Λ : Finset S}

/-- A boundary-condition kernel `γ_Λ(·|ω)` composed with a kernel from the same boundary σ-algebra:
`γ_Λ(·|ω) lam_Λ = lam_Λ(·|ω)`. -/
lemma bind_eq_apply (γ lam : Specification S E) (Λ : Finset S) (ω : S → E) :
    (γ Λ ω).bind (lam Λ) = lam Λ ω := by
  ext A hA
  rw [Measure.bind_apply hA ((lam Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable]
  have := γ.lintegral_mul Λ (f := fun _ ↦ 1) (g := fun ξ ↦ lam Λ ξ A) (η₀ := ω) measurable_const
    (Kernel.measurable_coe (lam Λ) hA)
  simpa [lintegral_one] using this

/-- If `γ_Λ = ρ lam_Λ`, then `μ γ_Λ = μ` iff `μ = ρ (μ lam_Λ)`. -/
lemma bind_eq_self_iff_eq_withDensity {ρ : (S → E) → ℝ≥0∞} (hρ : Measurable ρ)
    (h : ∀ η, γ Λ η = (lam Λ η).withDensity ρ) (μ : Measure (S → E)) :
    μ.bind (γ Λ) = μ ↔ μ = (μ.bind (lam Λ)).withDensity ρ := by
  have hfun : (⇑(γ Λ) : (S → E) → Measure (S → E)) = fun η ↦ (lam Λ η).withDensity ρ := funext h
  rw [hfun, Measure.bind_withDensity μ ((lam Λ).measurable.mono cylinderEvents_le_pi le_rfl) hρ,
    eq_comm]

/-- The normalisation `lam_{Λ₁}(ρ₁ ρ₂⁻¹)` appearing in Georgii's proof of (1.33). -/
noncomputable def stepNorm (lam : Specification S E) (Λ₁ : Finset S)
    (ρ₁ ρ₂ : (S → E) → ℝ≥0∞) (ω : S → E) : ℝ≥0∞ :=
  ∫⁻ ζ, ρ₁ ζ * (ρ₂ ζ)⁻¹ ∂(lam Λ₁ ω)

lemma measurable_stepNorm (lam : Specification S E) (Λ₁ : Finset S)
    {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) :
    Measurable (stepNorm lam Λ₁ ρ₁ ρ₂) :=
  ((hρ₁.mul hρ₂.inv).lintegral_kernel (κ := lam Λ₁)).mono cylinderEvents_le_pi le_rfl

/-- The normalisation `lam_{Λ₁}(ρ₁ ρ₂⁻¹)` is positive. -/
lemma stepNorm_ne_zero (lam : Specification S E) (Λ₁ : Finset S)
    {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (h₁0 : ∀ ω, ρ₁ ω ≠ 0) (h₂top : ∀ ω, ρ₂ ω ≠ ⊤) (ω : S → E) :
    stepNorm lam Λ₁ ρ₁ ρ₂ ω ≠ 0 := by
  have hf : Measurable fun ζ ↦ ρ₁ ζ * (ρ₂ ζ)⁻¹ := hρ₁.mul hρ₂.inv
  refine ((lintegral_pos_iff_support hf).2 ?_).ne'
  rw [Function.support_eq_univ fun ζ ↦ mul_ne_zero (h₁0 ζ) (ENNReal.inv_ne_zero.2 (h₂top ζ)),
    measure_univ]
  exact zero_lt_one

/-- The density `ρ_Λ = ρ_{Λ₁} / lam_{Λ₁}(ρ_{Λ₁} ρ_{Λ₂}⁻¹)` (and `1` where the normalisation is
infinite) built in Georgii's proof of (1.33) from `ρ_{Λ₁}` and `ρ_{Λ₂}`. -/
noncomputable def stepDensity (lam : Specification S E) (Λ₁ : Finset S)
    (ρ₁ ρ₂ : (S → E) → ℝ≥0∞) (ω : S → E) : ℝ≥0∞ :=
  if stepNorm lam Λ₁ ρ₁ ρ₂ ω = ⊤ then 1 else ρ₁ ω / stepNorm lam Λ₁ ρ₁ ρ₂ ω

lemma measurable_stepDensity (lam : Specification S E) (Λ₁ : Finset S)
    {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂) :
    Measurable (stepDensity lam Λ₁ ρ₁ ρ₂) :=
  Measurable.ite (measurableSet_eq_fun (measurable_stepNorm lam Λ₁ hρ₁ hρ₂) measurable_const)
    measurable_const (hρ₁.div (measurable_stepNorm lam Λ₁ hρ₁ hρ₂))

lemma stepDensity_ne_zero (lam : Specification S E) (Λ₁ : Finset S)
    {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (h₁0 : ∀ ω, ρ₁ ω ≠ 0) (ω : S → E) :
    stepDensity lam Λ₁ ρ₁ ρ₂ ω ≠ 0 := by
  unfold stepDensity
  split_ifs with h
  · exact one_ne_zero
  · exact (ENNReal.div_pos_iff.2 ⟨h₁0 ω, h⟩).ne'

lemma stepDensity_ne_top (lam : Specification S E) (Λ₁ : Finset S)
    {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (h₁0 : ∀ ω, ρ₁ ω ≠ 0) (h₁top : ∀ ω, ρ₁ ω ≠ ⊤) (h₂top : ∀ ω, ρ₂ ω ≠ ⊤) (ω : S → E) :
    stepDensity lam Λ₁ ρ₁ ρ₂ ω ≠ ⊤ := by
  unfold stepDensity
  split_ifs with h
  · exact ENNReal.one_ne_top
  · exact ENNReal.div_ne_top (h₁top ω) (stepNorm_ne_zero lam Λ₁ hρ₁ hρ₂ h₁0 h₂top ω)

variable [DecidableEq S]

/-- Georgii (1.33), induction step: if `μ = ρ₁ (μ lam_{Λ₁})` and `μ = ρ₂ (μ lam_{Λ₂})` with
`Λ₁, Λ₂` disjoint, then `μ lam_{Λ₁ ∪ Λ₂} = (ρ₁⁻¹ · lam_{Λ₁}(ρ₁ ρ₂⁻¹)) μ`. -/
lemma bind_union_eq_withDensity (hlam : IsDisjointlyConsistent ⇑lam) {Λ₁ Λ₂ : Finset S}
    (hΛ : Disjoint Λ₁ Λ₂) {ρ₁ ρ₂ : (S → E) → ℝ≥0∞} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (h₁0 : ∀ ω, ρ₁ ω ≠ 0) (h₁top : ∀ ω, ρ₁ ω ≠ ⊤) (h₂0 : ∀ ω, ρ₂ ω ≠ 0) (h₂top : ∀ ω, ρ₂ ω ≠ ⊤)
    {μ : Measure (S → E)} (hμ₁ : μ = (μ.bind (lam Λ₁)).withDensity ρ₁)
    (hμ₂ : μ = (μ.bind (lam Λ₂)).withDensity ρ₂) :
    μ.bind (lam (Λ₁ ∪ Λ₂)) =
      μ.withDensity (fun ω ↦ (ρ₁ ω)⁻¹ * ∫⁻ ζ, ρ₁ ζ * (ρ₂ ζ)⁻¹ ∂(lam Λ₁ ω)) := by
  set G : (S → E) → ℝ≥0∞ := fun ω ↦ ∫⁻ ζ, ρ₁ ζ * (ρ₂ ζ)⁻¹ ∂(lam Λ₁ ω) with hG
  have hGmeas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] G := (hρ₁.mul hρ₂.inv).lintegral_kernel
  have hGmeas' : Measurable G := hGmeas.mono cylinderEvents_le_pi le_rfl
  have hlam₁ : Measurable ⇑(lam Λ₁) := (lam Λ₁).measurable.mono cylinderEvents_le_pi le_rfl
  have hlam₂ : Measurable ⇑(lam Λ₂) := (lam Λ₂).measurable.mono cylinderEvents_le_pi le_rfl
  have hlamU : Measurable ⇑(lam (Λ₁ ∪ Λ₂)) :=
    (lam (Λ₁ ∪ Λ₂)).measurable.mono cylinderEvents_le_pi le_rfl
  have hinv₁ : μ.bind (lam Λ₁) = μ.withDensity ρ₁⁻¹ := withDensity_inv_of_eq hρ₁ h₁0 h₁top hμ₁
  have hinv₂ : μ.bind (lam Λ₂) = μ.withDensity ρ₂⁻¹ := withDensity_inv_of_eq hρ₂ h₂0 h₂top hμ₂
  ext A hA
  set F : (S → E) → ℝ≥0∞ := fun ζ ↦ lam Λ₁ ζ A with hF
  have hFmeas : Measurable[cylinderEvents (Λ₁ : Set S)ᶜ] F := Kernel.measurable_coe (lam Λ₁) hA
  have hFmeas' : Measurable F := hFmeas.mono cylinderEvents_le_pi le_rfl
  have hind : Measurable (A.indicator (1 : (S → E) → ℝ≥0∞)) := measurable_one.indicator hA
  have hg₁ : Measurable fun ζ ↦ (ρ₂ ζ)⁻¹ * F ζ := hρ₂.inv.mul hFmeas'
  have hg₂ : Measurable fun ζ ↦ ρ₁ ζ * ((ρ₂ ζ)⁻¹ * F ζ) := hρ₁.mul hg₁
  have hg₃ : Measurable fun ζ ↦ G ζ * A.indicator 1 ζ := hGmeas'.mul hind
  calc μ.bind (lam (Λ₁ ∪ Λ₂)) A
      = ∫⁻ ω, lam (Λ₁ ∪ Λ₂) ω A ∂μ := Measure.bind_apply hA hlamU.aemeasurable
    _ = ∫⁻ ω, ∫⁻ ζ, F ζ ∂(lam Λ₂ ω) ∂μ := by
        refine lintegral_congr fun ω ↦ ?_
        rw [← hlam.bind_eq hΛ ω, Measure.bind_apply hA hlam₁.aemeasurable]
    _ = ∫⁻ ζ, F ζ ∂(μ.bind (lam Λ₂)) :=
        (Measure.lintegral_bind hlam₂.aemeasurable hFmeas'.aemeasurable).symm
    _ = ∫⁻ ζ, (ρ₂ ζ)⁻¹ * F ζ ∂μ := by
        rw [hinv₂, lintegral_withDensity_eq_lintegral_mul _ hρ₂.inv hFmeas']
        rfl
    _ = ∫⁻ ζ, ρ₁ ζ * ((ρ₂ ζ)⁻¹ * F ζ) ∂(μ.bind (lam Λ₁)) := by
        conv_lhs => rw [hμ₁]
        rw [lintegral_withDensity_eq_lintegral_mul _ hρ₁ hg₁]
        rfl
    _ = ∫⁻ ω, ∫⁻ ζ, F ζ * (ρ₁ ζ * (ρ₂ ζ)⁻¹) ∂(lam Λ₁ ω) ∂μ := by
        rw [Measure.lintegral_bind hlam₁.aemeasurable hg₂.aemeasurable]
        exact lintegral_congr fun ω ↦ lintegral_congr fun ζ ↦ by ring
    _ = ∫⁻ ω, F ω * G ω ∂μ :=
        lintegral_congr fun ω ↦ lam.lintegral_mul Λ₁ (hρ₁.mul hρ₂.inv) hFmeas
    _ = ∫⁻ ω, ∫⁻ ζ, G ζ * A.indicator 1 ζ ∂(lam Λ₁ ω) ∂μ := by
        refine lintegral_congr fun ω ↦ ?_
        rw [lam.lintegral_mul Λ₁ hind hGmeas, lintegral_indicator_one hA, mul_comm]
    _ = ∫⁻ ζ, G ζ * A.indicator 1 ζ ∂(μ.bind (lam Λ₁)) :=
        (Measure.lintegral_bind hlam₁.aemeasurable hg₃.aemeasurable).symm
    _ = ∫⁻ ζ, (ρ₁ ζ)⁻¹ * (G ζ * A.indicator 1 ζ) ∂μ := by
        rw [hinv₁, lintegral_withDensity_eq_lintegral_mul _ hρ₁.inv hg₃]
        rfl
    _ = μ.withDensity (fun ω ↦ (ρ₁ ω)⁻¹ * G ω) A := by
        rw [withDensity_apply _ hA, ← lintegral_indicator hA]
        refine lintegral_congr fun ζ ↦ ?_
        by_cases hζ : ζ ∈ A <;> simp [hζ]

/-- Georgii (1.33), induction step: a finite measure `μ` with `μ = ρ₁ (μ lam_{Λ₁})` and
`μ = ρ₂ (μ lam_{Λ₂})`, `Λ₁, Λ₂` disjoint, satisfies `μ = ρ_Λ (μ lam_Λ)` for `Λ = Λ₁ ∪ Λ₂` and the
density `ρ_Λ = stepDensity lam Λ₁ ρ₁ ρ₂`. -/
lemma eq_bind_union_withDensity_stepDensity (hlam : IsDisjointlyConsistent ⇑lam)
    {Λ₁ Λ₂ : Finset S} (hΛ : Disjoint Λ₁ Λ₂) {ρ₁ ρ₂ : (S → E) → ℝ≥0∞}
    (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (h₁0 : ∀ ω, ρ₁ ω ≠ 0) (h₁top : ∀ ω, ρ₁ ω ≠ ⊤) (h₂0 : ∀ ω, ρ₂ ω ≠ 0) (h₂top : ∀ ω, ρ₂ ω ≠ ⊤)
    {μ : Measure (S → E)} [IsFiniteMeasure μ] (hμ₁ : μ = (μ.bind (lam Λ₁)).withDensity ρ₁)
    (hμ₂ : μ = (μ.bind (lam Λ₂)).withDensity ρ₂) :
    μ = (μ.bind (lam (Λ₁ ∪ Λ₂))).withDensity (stepDensity lam Λ₁ ρ₁ ρ₂) := by
  have hGmeas : Measurable (stepNorm lam Λ₁ ρ₁ ρ₂) := measurable_stepNorm lam Λ₁ hρ₁ hρ₂
  have hG0 : ∀ ω, stepNorm lam Λ₁ ρ₁ ρ₂ ω ≠ 0 := stepNorm_ne_zero lam Λ₁ hρ₁ hρ₂ h₁0 h₂top
  have hlamU : Measurable ⇑(lam (Λ₁ ∪ Λ₂)) :=
    (lam (Λ₁ ∪ Λ₂)).measurable.mono cylinderEvents_le_pi le_rfl
  have hbind : μ.bind (lam (Λ₁ ∪ Λ₂)) =
      μ.withDensity (fun ω ↦ (ρ₁ ω)⁻¹ * stepNorm lam Λ₁ ρ₁ ρ₂ ω) :=
    bind_union_eq_withDensity hlam hΛ hρ₁ hρ₂ h₁0 h₁top h₂0 h₂top hμ₁ hμ₂
  have hdens : Measurable fun ω ↦ (ρ₁ ω)⁻¹ * stepNorm lam Λ₁ ρ₁ ρ₂ ω := hρ₁.inv.mul hGmeas
  -- Taking `f = 1`: the density `ρ₁⁻¹ G` is `μ`-integrable, hence `G < ∞` `μ`-a.e.
  have hfin : ∫⁻ ω, (ρ₁ ω)⁻¹ * stepNorm lam Λ₁ ρ₁ ρ₂ ω ∂μ ≠ ⊤ := by
    have h1 : μ.bind (lam (Λ₁ ∪ Λ₂)) univ = μ univ := by
      rw [Measure.bind_apply MeasurableSet.univ hlamU.aemeasurable]
      simp
    rw [hbind, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h1
    rw [h1]
    exact measure_ne_top μ _
  have hae : ∀ᵐ ω ∂μ, stepNorm lam Λ₁ ρ₁ ρ₂ ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hdens hfin] with ω hω hGω
    rw [hGω, ENNReal.mul_top (ENNReal.inv_ne_zero.2 (h₁top ω))] at hω
    exact lt_irrefl _ hω
  rw [hbind, ← withDensity_mul _ hdens (measurable_stepDensity lam Λ₁ hρ₁ hρ₂)]
  refine withDensity_one.symm.trans (withDensity_congr_ae ?_)
  filter_upwards [hae] with ω hω
  simp only [Pi.mul_apply, Pi.one_apply, stepDensity, hω, ↓reduceIte, div_eq_mul_inv]
  calc (1 : ℝ≥0∞)
      = ((ρ₁ ω)⁻¹ * ρ₁ ω) * (stepNorm lam Λ₁ ρ₁ ρ₂ ω * (stepNorm lam Λ₁ ρ₁ ρ₂ ω)⁻¹) := by
        rw [ENNReal.inv_mul_cancel (h₁0 ω) (h₁top ω), ENNReal.mul_inv_cancel (hG0 ω) hω, mul_one]
    _ = (ρ₁ ω)⁻¹ * stepNorm lam Λ₁ ρ₁ ρ₂ ω * (ρ₁ ω * (stepNorm lam Λ₁ ρ₁ ρ₂ ω)⁻¹) := by ring

/-- Georgii (1.33), core construction: from positive singleton densities `ρ_i` with
`γ_{i} = ρ_i lam_{i}`, for every finite `Λ` there is a positive finite density `ρ_Λ` (depending only
on `(ρ_i)_{i ∈ Λ}` and `lam`) such that `μ = ρ_Λ (μ lam_Λ)` for every finite measure `μ` with
`μ γ_{i} = μ` for all `i ∈ Λ`. -/
theorem exists_density_of_singleton (hlam : IsDisjointlyConsistent ⇑lam)
    {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i)) (h0 : ∀ i ω, ρ i ω ≠ 0)
    (htop : ∀ i ω, ρ i ω ≠ ⊤) (hγ : ∀ i η, γ {i} η = (lam {i} η).withDensity (ρ i))
    (Λ : Finset S) :
    ∃ ρΛ : (S → E) → ℝ≥0∞, Measurable ρΛ ∧ (∀ ω, ρΛ ω ≠ 0) ∧ (∀ ω, ρΛ ω ≠ ⊤) ∧
      ∀ μ : Measure (S → E), IsFiniteMeasure μ → (∀ i ∈ Λ, μ.bind (γ {i}) = μ) →
        μ = (μ.bind (lam Λ)).withDensity ρΛ := by
  induction Λ using Finset.induction_on with
  | empty =>
    refine ⟨1, measurable_const, fun _ ↦ one_ne_zero, fun _ ↦ ENNReal.one_ne_top, fun μ _ _ ↦ ?_⟩
    have hd : (⇑(lam ∅) : (S → E) → Measure (S → E)) = Measure.dirac := funext lam.apply_empty
    rw [hd, Measure.bind_dirac, withDensity_one]
  | insert i Λ₀ hi ih =>
    obtain ⟨ρ₀, hρ₀, h₀0, h₀top, hΛ₀⟩ := ih
    refine ⟨stepDensity lam {i} (ρ i) ρ₀, measurable_stepDensity lam {i} (hρ i) hρ₀,
      stepDensity_ne_zero lam {i} (h0 i),
      stepDensity_ne_top lam {i} (hρ i) hρ₀ (h0 i) (htop i) h₀top, fun μ hμ hinv ↦ ?_⟩
    have := hμ
    have hdisj : Disjoint {i} Λ₀ := Finset.disjoint_singleton_left.2 hi
    rw [Finset.insert_eq]
    exact eq_bind_union_withDensity_stepDensity hlam hdisj (hρ i) hρ₀ (h0 i) (htop i) h₀0 h₀top
      ((bind_eq_self_iff_eq_withDensity (hρ i) (hγ i) μ).1 (hinv i (Finset.mem_insert_self i Λ₀)))
      (hΛ₀ μ hμ fun j hj ↦ hinv j (Finset.mem_insert_of_mem hj))

omit [DecidableEq S] in
/-- Georgii (1.33), step 1: if `ρΛ` witnesses `exists_density_of_singleton` for `γ`, then any
specification `γ'` whose singleton kernels on `Λ` agree with those of `γ` has `γ'_Λ = ρΛ lam_Λ`. -/
lemma apply_eq_withDensity_of_forall_bind {ρΛ : (S → E) → ℝ≥0∞}
    (hΛ : ∀ μ : Measure (S → E), IsFiniteMeasure μ → (∀ i ∈ Λ, μ.bind (γ {i}) = μ) →
      μ = (μ.bind (lam Λ)).withDensity ρΛ)
    {γ' : Specification S E} (hγ' : ∀ i ∈ Λ, γ' {i} = γ {i}) (ω : S → E) :
    γ' Λ ω = (lam Λ ω).withDensity ρΛ := by
  have h := hΛ (γ' Λ ω) inferInstance fun i hi ↦ by
    rw [← hγ' i hi]
    exact γ'.bind (Finset.singleton_subset_iff.2 hi) ω
  rwa [bind_eq_apply γ' lam Λ ω] at h

/-- **Georgii (1.33), existence.** A specification whose singleton kernels are positive finite
density changes of those of `lam` is a positive `lam`-modification. -/
theorem exists_isModifier_of_singleton (hlam : IsDisjointlyConsistent ⇑lam)
    {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i)) (h0 : ∀ i ω, ρ i ω ≠ 0)
    (htop : ∀ i ω, ρ i ω ≠ ⊤) (hγ : ∀ i η, γ {i} η = (lam {i} η).withDensity (ρ i)) :
    ∃ ρ' : Finset S → (S → E) → ℝ≥0∞, (∀ Λ ω, ρ' Λ ω ≠ 0) ∧ (∀ Λ ω, ρ' Λ ω ≠ ⊤) ∧
      ∃ hρ' : lam.IsModifier ρ', γ = lam.modification ρ' hρ' := by
  choose ρ' hmeas h0' htop' hK using exists_density_of_singleton hlam hρ h0 htop hγ
  have happly : ∀ Λ ω, γ Λ ω = (lam Λ ω).withDensity (ρ' Λ) := fun Λ ω ↦
    apply_eq_withDensity_of_forall_bind (hK Λ) (fun _ _ ↦ rfl) ω
  have hker : ∀ Λ, modificationKer (⇑lam) ρ' hmeas Λ = γ Λ := fun Λ ↦
    Kernel.ext fun ω ↦ by rw [modificationKer_apply, happly]
  have hmod : lam.IsModifier ρ' :=
    { measurable := hmeas
      isMarkovKernel := fun Λ ↦ by rw [hker]; infer_instance
      isConsistent := by
        have hfun : modificationKer (⇑lam) ρ' hmeas = ⇑γ := funext hker
        rw [hfun]
        exact γ.isConsistent }
  refine ⟨ρ', h0', htop', hmod, Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_⟩
  rw [modification_apply, happly]

/-- **Georgii (1.33), uniqueness.** `γ` is uniquely determined by its singleton kernels
`(γ_{i})_{i ∈ S}` (and `lam`). -/
theorem eq_of_forall_singleton_eq (hlam : IsDisjointlyConsistent ⇑lam)
    {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i)) (h0 : ∀ i ω, ρ i ω ≠ 0)
    (htop : ∀ i ω, ρ i ω ≠ ⊤) (hγ : ∀ i η, γ {i} η = (lam {i} η).withDensity (ρ i))
    {γ' : Specification S E} (hγ' : ∀ i, γ' {i} = γ {i}) : γ' = γ := by
  choose ρ' _ _ _ hK using exists_density_of_singleton hlam hρ h0 htop hγ
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  rw [apply_eq_withDensity_of_forall_bind (hK Λ) (fun i _ ↦ hγ' i) ω,
    apply_eq_withDensity_of_forall_bind (hK Λ) (fun _ _ ↦ rfl) ω]

/-- **Georgii (1.33), Gibbs measures.** `𝒢(γ)` is the set of probability measures invariant
under the singleton kernels: `μ γ_{i} = μ` for all `i`. -/
theorem isGibbsMeasure_iff_forall_singleton_bind_eq (hlam : IsDisjointlyConsistent ⇑lam)
    {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i)) (h0 : ∀ i ω, ρ i ω ≠ 0)
    (htop : ∀ i ω, ρ i ω ≠ ⊤) (hγ : ∀ i η, γ {i} η = (lam {i} η).withDensity (ρ i))
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∀ i, μ.bind (γ {i}) = μ := by
  rw [isGibbsMeasure_iff_forall_bind_eq_of_prob]
  refine ⟨fun h i ↦ h {i}, fun h Λ ↦ ?_⟩
  choose ρ' hmeas _ _ hK using exists_density_of_singleton hlam hρ h0 htop hγ
  rw [bind_eq_self_iff_eq_withDensity (hmeas Λ)
    (apply_eq_withDensity_of_forall_bind (hK Λ) (fun _ _ ↦ rfl))]
  exact hK Λ μ inferInstance fun i _ ↦ h i

/-- **Georgii (1.33), Gibbs measures, density form.** `𝒢(γ)` is the set of probability measures
`μ` with `μ = ρ_i (μ lam_{i})` for all `i`. -/
theorem isGibbsMeasure_iff_forall_eq_withDensity (hlam : IsDisjointlyConsistent ⇑lam)
    {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i)) (h0 : ∀ i ω, ρ i ω ≠ 0)
    (htop : ∀ i ω, ρ i ω ≠ ⊤) (hγ : ∀ i η, γ {i} η = (lam {i} η).withDensity (ρ i))
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∀ i, μ = (μ.bind (lam {i})).withDensity (ρ i) := by
  rw [isGibbsMeasure_iff_forall_singleton_bind_eq hlam hρ h0 htop hγ]
  exact forall_congr' fun i ↦ bind_eq_self_iff_eq_withDensity (hρ i) (hγ i) μ

section ISSSD
variable (ν : Measure E) [IsProbabilityMeasure ν]

omit [DecidableEq S] in
/-- **Georgii, Theorem (1.33)** for the independent specification `λ_· = isssd ν` of a probability
measure `ν` (Georgii's σ-finite `λ` reduces to this case by Remark (1.28)(3)). Suppose that for
each site `i` the singleton kernel `γ_{i}` is `ρ_i λ_{i}` with `ρ_i` measurable and `0 < ρ_i < ∞`.
Then `γ = ρ λ_·` for a positive `λ`-modification `ρ`; `γ` is uniquely determined by `(γ_{i})_i`;
and `𝒢(γ) = {μ ∈ 𝒫(Ω) | μ γ_{i} = μ ∀ i} = {μ ∈ 𝒫(Ω) | μ = ρ_i (μ λ_{i}) ∀ i}`. -/
theorem georgii_1_33 {ρ : S → (S → E) → ℝ≥0∞} (hρ : ∀ i, Measurable (ρ i))
    (h0 : ∀ i ω, ρ i ω ≠ 0) (htop : ∀ i ω, ρ i ω ≠ ⊤)
    (hγ : ∀ i η, γ {i} η = (isssd (S := S) ν {i} η).withDensity (ρ i)) :
    (∃ ρ' : Finset S → (S → E) → ℝ≥0∞, (∀ Λ ω, ρ' Λ ω ≠ 0) ∧ (∀ Λ ω, ρ' Λ ω ≠ ⊤) ∧
      ∃ hρ' : (isssd (S := S) ν).IsModifier ρ', γ = (isssd (S := S) ν).modification ρ' hρ') ∧
    (∀ γ' : Specification S E, (∀ i, γ' {i} = γ {i}) → γ' = γ) ∧
    (∀ μ : Measure (S → E), IsProbabilityMeasure μ →
      (γ.IsGibbsMeasure μ ↔ ∀ i, μ.bind (γ {i}) = μ)) ∧
    (∀ μ : Measure (S → E), IsProbabilityMeasure μ →
      (γ.IsGibbsMeasure μ ↔ ∀ i, μ = (μ.bind (isssd (S := S) ν {i})).withDensity (ρ i))) := by
  classical
  have hlam : IsDisjointlyConsistent ⇑(isssd (S := S) ν) :=
    (isStronglyConsistent_isssd ν).isDisjointlyConsistent
  exact ⟨exists_isModifier_of_singleton hlam hρ h0 htop hγ,
    fun _ hγ' ↦ eq_of_forall_singleton_eq hlam hρ h0 htop hγ hγ',
    fun _ _ ↦ isGibbsMeasure_iff_forall_singleton_bind_eq hlam hρ h0 htop hγ,
    fun _ _ ↦ isGibbsMeasure_iff_forall_eq_withDensity hlam hρ h0 htop hγ⟩

end ISSSD

/-! ## The λ-specification of a σ-finite a priori measure: Georgii (1.33) -/

section SigmaFiniteLambda

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- **Georgii, Remark (1.28)(3) for λ-specifications.** The λ-specification of `ν` and `ρ` is the
λ-specification of the rescaled a priori measure `r · ν` and the rescaled densities. -/
theorem lambdaSpecification_eq_lambdaSpecification_withDensity (ν : Measure E) [SigmaFinite ν]
    [NeZero ν] {r : E → ℝ≥0∞} (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [SigmaFinite (ν.withDensity r)] [NeZero (ν.withDensity r)]
    (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ
      = lambdaSpecification (S := S) (E := E) (ν.withDensity r) (rescale (S := S) (E := E) r ρ)
          (isPremodifier_rescale (S := S) (E := E) hr h0 htop hρ)
          ((isSigmaFiniteLambdaAdmissible_rescale (S := S) (E := E) ν hr h0 htop
            hρ.measurable).2 hZ) := by
  refine Specification.ext fun Λ ↦ ?_
  rw [coe_lambdaSpecification, coe_lambdaSpecification, sigmaFinitePremodifierKernel,
    sigmaFinitePremodifierKernel,
    modificationKer_sigmaFiniteLambdaFun_of_withDensity (S := S) (E := E) ν
      (ν.withDensity r) hr h0 htop rfl hρ.measurable
      (sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := rescale (S := S) (E := E) r ρ) (ν.withDensity r)
        (isPremodifier_rescale (S := S) (E := E) hr h0 htop hρ))
      (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ)]

/-- **Georgii, Remark (1.28)(3) for λ-specifications, at an arbitrary finite volume.** The
λ-specification of a σ-finite non-zero `ν` and `ρ`, evaluated at any `Λ`, is the density change of
the independent specification of the rescaled *probability* measure `r · ν` by the correspondingly
rescaled and normalized density family. Chaining
`lambdaSpecification_eq_lambdaSpecification_withDensity` (Remark (1.28)(3) itself) with
`lambdaSpecification_eq_modification_isssd` (the probability case). -/
theorem lambdaSpecification_eq_isssd_withDensity (ν : Measure E) [SigmaFinite ν]
    [NeZero ν] {r : E → ℝ≥0∞} (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [IsProbabilityMeasure (ν.withDensity r)] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (Λ : Finset S) (η : S → E) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ η
      = (isssd (S := S) (E := E) (ν.withDensity r) Λ η).withDensity
        (premodifierNorm (S := S) (E := E) (ν.withDensity r)
          (rescale (S := S) (E := E) r ρ) Λ) := by
  rw [lambdaSpecification_eq_lambdaSpecification_withDensity (S := S) (E := E) ν hr h0 htop hρ hZ,
    lambdaSpecification_eq_modification_isssd, modification_apply]

/-- The singleton kernels of a λ-specification as density changes of the independent
specification of the rescaled probability measure `r · ν`. -/
lemma lambdaSpecification_singleton_eq_isssd_withDensity (ν : Measure E) [SigmaFinite ν]
    [NeZero ν] {r : E → ℝ≥0∞} (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [IsProbabilityMeasure (ν.withDensity r)] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (i : S) (η : S → E) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ {i} η
      = (isssd (S := S) (E := E) (ν.withDensity r) {i} η).withDensity
        (premodifierNorm (S := S) (E := E) (ν.withDensity r)
          (rescale (S := S) (E := E) r ρ) {i}) :=
  lambdaSpecification_eq_isssd_withDensity (S := S) (E := E) ν hr h0 htop hρ hZ {i} η

lemma premodifierNorm_rescale_ne_zero (ν : Measure E) [SigmaFinite ν] {r : E → ℝ≥0∞}
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [IsProbabilityMeasure (ν.withDensity r)] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hρ0 : ∀ Λ ω, ρ Λ ω ≠ 0)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (Λ : Finset S) (ω : S → E) :
    premodifierNorm (S := S) (E := E) (ν.withDensity r) (rescale (S := S) (E := E) r ρ) Λ ω
      ≠ 0 := by
  have hZ' := (isSigmaFiniteLambdaAdmissible_rescale (S := S) (E := E) ν hr h0 htop
    hρ.measurable).2 hZ
  rw [premodifierNorm_eq_sigmaFinitePremodifierNorm, sigmaFinitePremodifierNorm, rescale_apply]
  refine (ENNReal.div_pos_iff.2 ⟨?_, hZ'.ne_top _ _⟩).ne'
  exact (ENNReal.div_pos_iff.2 ⟨hρ0 _ _,
    lambdaWeight_ne_top (S := S) (E := E) (fun _ ↦ htop) _ _⟩).ne'

lemma premodifierNorm_rescale_ne_top (ν : Measure E) [SigmaFinite ν] {r : E → ℝ≥0∞}
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [IsProbabilityMeasure (ν.withDensity r)] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hρtop : ∀ Λ ω, ρ Λ ω ≠ ⊤)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) (Λ : Finset S) (ω : S → E) :
    premodifierNorm (S := S) (E := E) (ν.withDensity r) (rescale (S := S) (E := E) r ρ) Λ ω
      ≠ ⊤ := by
  have hZ' := (isSigmaFiniteLambdaAdmissible_rescale (S := S) (E := E) ν hr h0 htop
    hρ.measurable).2 hZ
  rw [premodifierNorm_eq_sigmaFinitePremodifierNorm, sigmaFinitePremodifierNorm, rescale_apply]
  intro h
  rcases ENNReal.div_eq_top.1 h with ⟨-, h⟩ | ⟨h, -⟩
  · exact hZ'.ne_zero _ _ h
  · rcases ENNReal.div_eq_top.1 h with ⟨-, h⟩ | ⟨h, -⟩
    · exact lambdaWeight_ne_zero (S := S) (E := E) (fun _ ↦ h0) _ _ h
    · exact hρtop _ _ h

lemma measurable_premodifierNorm_rescale (ν : Measure E) [SigmaFinite ν] {r : E → ℝ≥0∞}
    (hr : Measurable r) (h0 : ∀ x, r x ≠ 0) (htop : ∀ x, r x ≠ ⊤)
    [IsProbabilityMeasure (ν.withDensity r)] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (Λ : Finset S) :
    Measurable (premodifierNorm (S := S) (E := E) (ν.withDensity r)
      (rescale (S := S) (E := E) r ρ) Λ) := by
  rw [premodifierNorm_eq_sigmaFinitePremodifierNorm]
  exact sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ν.withDensity r)
    (isPremodifier_rescale (S := S) (E := E) hr h0 htop hρ) _

/-- **Georgii (1.33) for the λ-specification of a σ-finite a priori measure.** For a positive
finite pre-modification `ρ` admissible for a σ-finite non-zero `ν`, a probability measure `μ` is
a Gibbs measure for `ρλ_·` iff it is invariant under the singleton kernels `ρ_{i} λ_{i}`. -/
theorem lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (h0 : ∀ Λ ω, ρ Λ ω ≠ 0) (htop : ∀ Λ ω, ρ Λ ω ≠ ⊤)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] :
    (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ
      ↔ ∀ i, μ.bind (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ {i}) = μ := by
  classical
  obtain ⟨r, hr, hr0, hrtop, hprob⟩ :=
    Measure.exists_measurable_pos_isProbabilityMeasure_withDensity ν
  exact isGibbsMeasure_iff_forall_singleton_bind_eq
    (lam := isssd (S := S) (E := E) (ν.withDensity r))
    ((isStronglyConsistent_isssd (S := S) (E := E) (ν.withDensity r)).isDisjointlyConsistent)
    (fun i ↦ measurable_premodifierNorm_rescale (S := S) (E := E) ν hr hr0 hrtop hρ {i})
    (fun i ω ↦ premodifierNorm_rescale_ne_zero (S := S) (E := E) ν hr hr0 hrtop hρ h0 hZ {i} ω)
    (fun i ω ↦ premodifierNorm_rescale_ne_top (S := S) (E := E) ν hr hr0 hrtop hρ htop hZ {i} ω)
    (fun i η ↦ lambdaSpecification_singleton_eq_isssd_withDensity (S := S) (E := E) ν hr hr0
      hrtop hρ hZ i η)

/-- **Georgii (1.33), uniqueness, for the λ-specification of a σ-finite a priori measure.** A
specification with the singleton kernels of `ρλ_·` is `ρλ_·`. -/
theorem eq_lambdaSpecification_of_forall_singleton_eq
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (h0 : ∀ Λ ω, ρ Λ ω ≠ 0) (htop : ∀ Λ ω, ρ Λ ω ≠ ⊤)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) {γ' : Specification S E}
    (hγ' : ∀ i, γ' {i} = lambdaSpecification (S := S) (E := E) ν ρ hρ hZ {i}) :
    γ' = lambdaSpecification (S := S) (E := E) ν ρ hρ hZ := by
  classical
  obtain ⟨r, hr, hr0, hrtop, hprob⟩ :=
    Measure.exists_measurable_pos_isProbabilityMeasure_withDensity ν
  exact eq_of_forall_singleton_eq
    (lam := isssd (S := S) (E := E) (ν.withDensity r))
    ((isStronglyConsistent_isssd (S := S) (E := E) (ν.withDensity r)).isDisjointlyConsistent)
    (fun i ↦ measurable_premodifierNorm_rescale (S := S) (E := E) ν hr hr0 hrtop hρ {i})
    (fun i ω ↦ premodifierNorm_rescale_ne_zero (S := S) (E := E) ν hr hr0 hrtop hρ h0 hZ {i} ω)
    (fun i ω ↦ premodifierNorm_rescale_ne_top (S := S) (E := E) ν hr hr0 hrtop hρ htop hZ {i} ω)
    (fun i η ↦ lambdaSpecification_singleton_eq_isssd_withDensity (S := S) (E := E) ν hr hr0
      hrtop hρ hZ i η) hγ'

end SigmaFiniteLambda

end Specification

/-! ### Georgii, Remark (1.28)(2): single-site marginals of Gibbs measures -/

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

/-- `λ_{{i}}(σ_i ∈ B | ω) = λ(B)`: resampling the single site `i` from `λ`. -/
lemma sigmaFiniteLambdaFun_singleton_eval_preimage (i : S) (ω : S → E) {B : Set E}
    (hB : MeasurableSet B) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν {i} ω ((fun ω : S → E ↦ ω i) ⁻¹' B) = ν B := by
  rw [sigmaFiniteLambdaFun_apply_eq_map,
    Measure.map_apply Measurable.juxt (measurable_pi_apply i hB)]
  have hi : i ∈ ({i} : Finset S) := Finset.mem_singleton_self i
  have hset : juxt (({i} : Finset S) : Set S) ω ⁻¹' ((fun ω : S → E ↦ ω i) ⁻¹' B) =
      (MeasurableEquiv.piUnique fun _ : ({i} : Finset S) ↦ E) ⁻¹' B := by
    ext ζ
    simp only [Set.mem_preimage, juxt_apply_of_mem (Finset.mem_coe.2 hi),
      MeasurableEquiv.piUnique_apply]
    rfl
  have hmp := measurePreserving_piUnique fun _ : ({i} : Finset S) ↦ ν
  rw [hset, ← Measure.map_apply hmp.measurable hB, hmp.map_eq]

variable [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifier (S := S) (E := E) ρ)
  (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
include hρ hZ

/-- **Georgii, Remark (1.28)(2), first half.** For a Gibbs measure `μ` of a `λ`-specification
`ρ λ_·`, the single-site marginal `σ_i(μ)` is absolutely continuous with respect to `λ`. -/
theorem map_eval_absolutelyContinuous_of_mem_G {μ : Measure (S → E)}
    (hμ : μ ∈ G (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)) (i : S) :
    μ.map (fun ω ↦ ω i) ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hνB ↦ ?_
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hBm : MeasurableSet ((fun ω : S → E ↦ ω i) ⁻¹' B) := measurable_pi_apply i hB
  have hbind := (isGibbsMeasure_iff_forall_bind_eq.1 hμ.2) {i}
  rw [Measure.map_apply (measurable_pi_apply i) hB]
  conv_lhs => rw [← hbind]
  rw [Measure.bind_apply hBm
    ((lambdaSpecification ν ρ hρ hZ).measurable_kernel_toMeasure {i}).aemeasurable]
  refine (lintegral_eq_zero_iff (measurable_apply_kernel _ {i} hBm)).2
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [Pi.zero_apply, lambdaSpecification_apply]
  rw [withDensity_apply _ hBm, Measure.restrict_eq_zero.2 (by
    rw [sigmaFiniteLambdaFun_singleton_eval_preimage ν i ω hB]; exact hνB), lintegral_zero_measure]

/-- **Georgii, Remark (1.28)(2), second half.** If the densities `ρ_Λ` are strictly positive —
as the Boltzmann factors `e^{-β H_Λ}` of a `λ`-admissible potential are — then `λ` is absolutely
continuous with respect to the single-site marginal `σ_i(μ)` of every Gibbs measure `μ`; together
with the first half, `σ_i(μ)` and `λ` are equivalent. -/
theorem absolutelyContinuous_map_eval_of_mem_G (hρ0 : ∀ (Λ : Finset S) (η : S → E), ρ Λ η ≠ 0)
    {μ : Measure (S → E)} (hμ : μ ∈ G (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ))
    (i : S) : ν ≪ μ.map (fun ω ↦ ω i) := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hμB ↦ ?_
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hae : (ae μ).NeBot := IsProbabilityMeasure.ae_neBot
  have hBm : MeasurableSet ((fun ω : S → E ↦ ω i) ⁻¹' B) := measurable_pi_apply i hB
  have hbind := (isGibbsMeasure_iff_forall_bind_eq.1 hμ.2) {i}
  rw [Measure.map_apply (measurable_pi_apply i) hB] at hμB
  have hμB' : μ.bind ((lambdaSpecification ν ρ hρ hZ) {i}) ((fun ω : S → E ↦ ω i) ⁻¹' B) = 0 :=
    by rwa [hbind]
  rw [Measure.bind_apply hBm
    ((lambdaSpecification ν ρ hρ hZ).measurable_kernel_toMeasure {i}).aemeasurable,
    lintegral_eq_zero_iff (measurable_apply_kernel _ {i} hBm)] at hμB'
  obtain ⟨ω, hω⟩ := hμB'.exists
  simp only [Pi.zero_apply, lambdaSpecification_apply] at hω
  rw [withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E) ν hρ hBm, mul_eq_zero,
    ENNReal.inv_eq_zero] at hω
  rcases hω with hω | hω
  · exact absurd hω (hZ.ne_top _ _)
  · rw [lintegral_eq_zero_iff (hρ.measurable {i}), Filter.EventuallyEq, ae_iff] at hω
    have huniv : {x | ¬ ρ {i} x = (0 : (S → E) → ℝ≥0∞) x} = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ hρ0 _ x
    rw [huniv, Measure.restrict_apply_univ,
      sigmaFiniteLambdaFun_singleton_eval_preimage ν i ω hB] at hω
    exact hω

end Specification

end

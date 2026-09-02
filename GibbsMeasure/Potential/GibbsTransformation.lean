/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Specification.Transformation
public import GibbsMeasure.Potential.FiniteReference
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Transformations of Gibbsian specifications

Georgii Proposition (5.6)(b),(c): the image of a `λ`-modification under a `λ`-preserving
transformation is again one, and `γ^{τ(Φ)} = τ(γ^Φ)`; hence Corollary (5.9)(b): a `τ`-invariant
potential has a `τ`-invariant Gibbsian specification.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace Specification

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
  (τ : Transformation S E)

/-- **Georgii (5.6)(a)** for `isssd`: `τ(λ.)_Λ(· | ω) = λ_Λ(· | ω)` when `τ` is
`λ`-preserving. -/
lemma isssd_map_toFun (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S) (ω : S → E) :
    (isssd ν (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω)).map τ.toFun = isssd ν Λ ω :=
  isssdFun_map_toFun ν τ hτ Λ ω

/-- **Georgii (5.5)** for `λ.`: `λ_Λ(f ∘ τ⁻¹) = λ_{τ_*⁻¹ Λ}(f) ∘ τ⁻¹` when `τ` is
`λ`-preserving. -/
lemma lintegral_isssd_comp_inv (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S)
    (ω : S → E) (f : (S → E) → ℝ≥0∞) :
    ∫⁻ x, f (τ.inv.toFun x) ∂isssd ν Λ ω =
      ∫⁻ x, f x ∂isssd ν (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω) := by
  rw [← isssd_map_toFun ν τ hτ Λ ω]
  have h := lintegral_map_equiv (μ := isssd ν (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω))
    (fun x ↦ f (τ.inv.toFun x)) τ.toMeasurableEquiv
  rw [show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl] at h
  rw [h]
  simp only [τ.inv_toFun_toFun]

/-- **Georgii (5.6)(c), the partition function.** `Z^{τ(ρ)}_Λ = Z^ρ_{τ_*⁻¹ Λ} ∘ τ⁻¹`, i.e.
`Z^{τ(ρ)}_{τ_* Λ} ∘ τ = Z^ρ_Λ`, for the `τ`-image `τ(ρ)_Λ = ρ_{τ_*⁻¹ Λ} ∘ τ⁻¹` of (5.3). -/
lemma premodifierZ_map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) :
    premodifierZ (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      premodifierZ (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) :=
  lintegral_isssd_comp_inv ν τ hτ Λ η _

/-- **Georgii (5.6)(c), normalized densities.** `τ(ρ)/Z^{τ(ρ)} = τ(ρ/Z^ρ)`. -/
lemma premodifierNorm_map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (ρ : Finset S → (S → E) → ℝ≥0∞) (Λ : Finset S) (η : S → E) :
    premodifierNorm (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      premodifierNorm (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := by
  simp only [premodifierNorm, Specification.relNorm, premodifierZ_map ν τ hτ]

/-- `λ`-admissibility (Georgii (2.7)) is transported by (5.3): `Z^{τ(ρ)}_{τ_* Λ} ∘ τ = Z^ρ_Λ`. -/
lemma IsPremodifierAdmissible.map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifierAdmissible (S := S) (E := E) ν ρ) :
    IsPremodifierAdmissible (S := S) (E := E) ν
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := fun Λ η ↦ by
  simp only [premodifierZ_map ν τ hτ]
  exact hρ _ _

/-- The kernels of `τ(ρλ.)` are the `λ.`-kernels with densities `τ(ρ)` (Georgii (5.6)(b)). -/
lemma coe_modification_isssd_map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    ⇑(((isssd (S := S) (E := E) ν).modification ρ hρ).map τ) =
      modificationKer (isssd (S := S) (E := E) ν)
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η))
        (fun Λ ↦ (hρ.measurable (Λ.map τ.sites.symm.toEmbedding)).comp
          τ.inv.measurable_toFun) := by
  funext Λ
  refine Kernel.ext fun ω ↦ ?_
  rw [map_apply, modification_apply, modificationKer_apply,
    show (τ.toFun : (S → E) → (S → E)) = τ.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_withDensity,
    show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl, isssd_map_toFun ν τ hτ]
  rfl

/-- **Georgii (5.6)(b).** `τ(ρ)` is a `λ`-modification when `ρ` is and `τ` is `λ`-preserving. -/
theorem IsModifier.map_isssd (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    (isssd (S := S) (E := E) ν).IsModifier
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) where
  measurable Λ := (hρ.measurable (Λ.map τ.sites.symm.toEmbedding)).comp τ.inv.measurable_toFun
  isMarkovKernel Λ := by
    rw [← congrFun (coe_modification_isssd_map ν τ hτ hρ) Λ]
    infer_instance
  isConsistent := by
    rw [← coe_modification_isssd_map ν τ hτ hρ]
    exact (((isssd ν).modification ρ hρ).map τ).isConsistent

/-- **Georgii (5.6)(b).** `τ(ρ)λ. = τ(ρλ.)` for a `λ`-preserving `τ`. -/
theorem modification_isssd_map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ) :
    ((isssd (S := S) (E := E) ν).modification ρ hρ).map τ =
      (isssd (S := S) (E := E) ν).modification
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) (hρ.map_isssd ν τ hτ) :=
  Specification.ext fun Λ ↦ congrFun (coe_modification_isssd_map ν τ hτ hρ) Λ

/-- Modifying by equal density families gives equal specifications. -/
lemma modification_congr {γ : Specification S E} {ρ ρ' : Finset S → (S → E) → ℝ≥0∞}
    (h : ρ = ρ') (hρ : γ.IsModifier ρ) (hρ' : γ.IsModifier ρ') :
    γ.modification ρ hρ = γ.modification ρ' hρ' := by
  subst h; rfl

end Specification

/-! ### Georgii (5.6)(c) and (5.9)(b): Gibbsian specifications -/

namespace Potential

variable {S E : Type*} [MeasurableSpace E] (τ : Transformation S E) (Φ : Potential S E)

/-- Georgii (5.6)(c) for the Boltzmann factors, in the form of (5.3):
`h^{τ(Φ)}_Λ = h^Φ_{τ_*⁻¹ Λ} ∘ τ⁻¹`. -/
theorem boltzmannFactor_map' (β : ℝ) (Λ : Finset S) (η : S → E) :
    (Potential.map τ Φ).boltzmannFactor β Λ η
      = Φ.boltzmannFactor β (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := by
  rw [boltzmannFactor, boltzmannFactor, hamiltonian_map']

variable (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (5.6)(c).** `ρ^{τ(Φ)} = τ(ρ^Φ)`: the normalized Boltzmann densities of `τ(Φ)` are
the `τ`-image (5.3) of those of `Φ`. -/
theorem premodifierNorm_boltzmannFactor_map (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) :
    Specification.premodifierNorm (S := S) (E := E) ν ((Potential.map τ Φ).boltzmannFactor β) =
      fun Λ η ↦ Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β)
        (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := by
  have h : (Potential.map τ Φ).boltzmannFactor β =
      fun Λ η ↦ Φ.boltzmannFactor β (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) :=
    funext fun Λ ↦ funext fun η ↦ boltzmannFactor_map' τ Φ β Λ η
  funext Λ η
  rw [h, Specification.premodifierNorm_map ν τ hτ]

/-- The Gibbsian specification of Georgii (2.9) depends only on the potential. -/
lemma gibbsSpecification_congr [Countable S] {Φ Ψ : Potential S E} (h : Φ = Ψ)
    [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ] :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β =
      gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β := by
  subst h; rfl

/-- **Georgii (5.6)(c) at the specification level.** `τ(γ^Φ) = γ^{τ(Φ)}` for a `λ`-preserving
`τ` and `Φ ∈ ℬ`. -/
theorem map_gibbsSpecification [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ]
    (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) :
    (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β).map τ =
      gibbsSpecificationOfAbsolutelySummable (Φ := Potential.map τ Φ) ν β := by
  unfold gibbsSpecificationOfAbsolutelySummable
  rw [Specification.modification_isssd_map ν τ hτ]
  exact Specification.modification_congr (premodifierNorm_boltzmannFactor_map τ Φ ν β hτ).symm _ _

/-- **Georgii (5.9)(b).** If `Φ ∈ ℬ` is `τ`-invariant and `τ` is `λ`-preserving then `γ^Φ` is
`τ`-invariant. -/
theorem isInvariant_gibbsSpecification [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ]
    (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (h : Potential.map τ Φ = Φ) :
    Specification.IsInvariant τ (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  (map_gibbsSpecification τ Φ ν β hτ).trans (gibbsSpecification_congr ν β h)

end Potential

/-! ### Georgii (5.6)(a) and (5.5) for a σ-finite a priori measure -/

namespace Specification

open MeasureTheory.GibbsMeasure Transformation

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
  (τ : Transformation S E)

/-- **Georgii (5.6)(a)** for the σ-finite reference kernels of Notation (1.26):
`τ(λ_·)_Λ(· | ω) = λ_{τ_*⁻¹ Λ}(τ⁻¹ · | τ⁻¹ ω) = λ_Λ(· | ω)` when `τ` is `λ`-preserving. -/
lemma sigmaFiniteLambdaFun_map_toFun (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S)
    (ω : S → E) :
    (sigmaFiniteLambdaFun (S := S) (E := E) ν (Λ.map τ.sites.symm.toEmbedding)
      (τ.inv.toFun ω)).map τ.toFun = sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω := by
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map,
    Measure.map_map τ.measurable_toFun Measurable.juxt, τ.toFun_comp_juxt,
    ← Measure.map_map Measurable.juxt (τ.measurePreserving_spin_piCongrLeft hτ Λ).measurable,
    (τ.measurePreserving_spin_piCongrLeft hτ Λ).map_eq]

/-- **Georgii (5.5)** for `λ_·` over a σ-finite `λ`:
`λ_Λ(f ∘ τ⁻¹) = λ_{τ_*⁻¹ Λ}(f) ∘ τ⁻¹` when `τ` is `λ`-preserving. -/
lemma lintegral_sigmaFiniteLambdaFun_comp_inv (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (Λ : Finset S) (ω : S → E) (f : (S → E) → ℝ≥0∞) :
    ∫⁻ x, f (τ.inv.toFun x) ∂sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω =
      ∫⁻ x, f x ∂sigmaFiniteLambdaFun (S := S) (E := E) ν (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun ω) := by
  rw [← sigmaFiniteLambdaFun_map_toFun ν τ hτ Λ ω]
  have h := lintegral_map_equiv (μ := sigmaFiniteLambdaFun (S := S) (E := E) ν
    (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun ω)) (fun x ↦ f (τ.inv.toFun x))
    τ.toMeasurableEquiv
  rw [show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl] at h
  rw [h]
  simp only [τ.inv_toFun_toFun]

end Specification

/-! ### Georgii (5.6)(b),(c) and (5.9)(b) for a σ-finite a priori measure -/

namespace Specification

open MeasureTheory.GibbsMeasure Transformation

variable {S E : Type*} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
  (τ : Transformation S E) (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
  (ρ : Finset S → (S → E) → ℝ≥0∞)
include hτ

/-- **Georgii (5.6)(c), the partition function**, over a σ-finite `λ`:
`Z^{τ(ρ)}_Λ = Z^ρ_{τ_*⁻¹ Λ} ∘ τ⁻¹`. -/
lemma sigmaFiniteLambdaZ_map (Λ : Finset S) (η : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun η) :=
  lintegral_sigmaFiniteLambdaFun_comp_inv ν τ hτ Λ η _

/-- **Georgii (5.6)(c), normalized densities**, over a σ-finite `λ`: `τ(ρ)/Z^{τ(ρ)} = τ(ρ/Z^ρ)`. -/
lemma sigmaFinitePremodifierNorm_map (Λ : Finset S) (η : S → E) :
    sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) Λ η =
      sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ (Λ.map τ.sites.symm.toEmbedding)
        (τ.inv.toFun η) := by
  simp only [sigmaFinitePremodifierNorm, sigmaFiniteLambdaZ_map ν τ hτ]

omit hτ in
/-- The image `τ(ρ)` of a premodifier under a transformation is a premodifier. -/
lemma IsPremodifier.map (hρ : IsPremodifier (S := S) (E := E) ρ) :
    IsPremodifier (S := S) (E := E)
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) where
  measurable Λ := (hρ.measurable _).comp τ.inv.measurable_toFun
  comm_of_subset Λ₁ Λ₂ ζ η hΛ hres := by
    refine hρ.comm_of_subset (Finset.map_subset_map.2 hΛ) fun s hs ↦ ?_
    have hs' : τ.sites s ∉ Λ₁ := by
      rwa [Finset.mem_map_equiv, Equiv.symm_symm] at hs
    simp only [Transformation.inv, Transformation.toFun, Equiv.symm_symm, hres _ hs']

/-- `λ`-admissibility is transported by (5.3) over a σ-finite `λ`. -/
lemma IsSigmaFiniteLambdaAdmissible.map
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := fun Λ η ↦ by
  rw [sigmaFiniteLambdaZ_map ν τ hτ]
  exact hZ _ _

/-- **Georgii (5.6)(b)** over a σ-finite `λ`: `τ(ρ λ_·) = τ(ρ) λ_·` for a `λ`-preserving `τ`. -/
theorem lambdaSpecification_map [NeZero ν] (hρ : IsPremodifier (S := S) (E := E) ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) :
    (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).map τ =
      lambdaSpecification (S := S) (E := E) ν
        (fun Λ η ↦ ρ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)) (hρ.map τ)
        (hZ.map ν τ hτ) := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun ω ↦ ?_
  rw [map_apply, lambdaSpecification_apply, lambdaSpecification_apply,
    show (τ.toFun : (S → E) → (S → E)) = τ.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_withDensity,
    show (τ.toMeasurableEquiv : (S → E) → (S → E)) = τ.toFun from rfl,
    sigmaFiniteLambdaFun_map_toFun ν τ hτ]
  congr 1
  funext x
  exact (sigmaFinitePremodifierNorm_map ν τ hτ ρ Λ x).symm

end Specification

namespace Potential

open MeasureTheory.GibbsMeasure Transformation Specification

variable {S E : Type*} [MeasurableSpace E] (Φ : Potential S E) (β : ℝ) (τ : Transformation S E)

/-- The Boltzmann factors of `τ(Φ)` are the `τ`-image (5.3) of those of `Φ`. -/
lemma boltzmannFactor_map_eq :
    (Potential.map τ Φ).boltzmannFactor β =
      fun Λ η ↦ Φ.boltzmannFactor β (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) :=
  funext fun Λ ↦ funext fun η ↦ boltzmannFactor_map' τ Φ β Λ η

variable (ν : Measure E) [SigmaFinite ν] (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν)
include hτ

/-- `λ`-admissibility of `Φ` transports to `τ(Φ)` for a `λ`-preserving `τ`. -/
lemma isSigmaFiniteLambdaAdmissible_boltzmannFactor_map
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β)) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((Potential.map τ Φ).boltzmannFactor β) := by
  rw [boltzmannFactor_map_eq Φ β τ]
  exact hadm.map ν τ hτ

variable [Countable S] [IsPotential Φ] [IsSummable Φ] [NeZero ν]

/-- **Georgii (5.6)(c) at the specification level, over a σ-finite `λ`.** `τ(γ^Φ) = γ^{τ(Φ)}`
for a `λ`-preserving `τ` and a `λ`-admissible `Φ`; `τ(Φ)` is again `λ`-admissible
(`isSigmaFiniteLambdaAdmissible_boltzmannFactor_map`). -/
theorem map_gibbsSpecificationOfSigmaFiniteAdmissible
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (hadm' : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      ((Potential.map τ Φ).boltzmannFactor β)) :
    (gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm).map τ =
      gibbsSpecificationOfSigmaFiniteAdmissible (Potential.map τ Φ) ν β hadm' := by
  unfold gibbsSpecificationOfSigmaFiniteAdmissible
  rw [Specification.lambdaSpecification_map ν τ hτ]
  exact Specification.lambdaSpecification_congr ν (boltzmannFactor_map_eq Φ β τ).symm _ _ _ _

/-- **Georgii (5.9)(b) over a σ-finite `λ`.** If the `λ`-admissible `Φ` is `τ`-invariant and `τ`
is `λ`-preserving, then `γ^Φ` is `τ`-invariant. -/
theorem isInvariant_gibbsSpecificationOfSigmaFiniteAdmissible
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (h : Potential.map τ Φ = Φ) :
    Specification.IsInvariant τ (gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) := by
  unfold Specification.IsInvariant gibbsSpecificationOfSigmaFiniteAdmissible
  rw [Specification.lambdaSpecification_map ν τ hτ]
  refine Specification.lambdaSpecification_congr ν ?_ _ _ _ _
  rw [← boltzmannFactor_map_eq Φ β τ, h]

end Potential

end

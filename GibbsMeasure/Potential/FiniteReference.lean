/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Potential.Space

/-!
# Gibbsian specifications for a general a priori measure

Georgii's Definition (2.9) attaches a Gibbsian specification to any `λ`-admissible potential and
any a priori measure `λ ∈ 𝓜(E, ℰ)`, and his Theorem (4.23) is stated for an arbitrary **finite**
`λ`, not only for a probability measure. (By (2.14) an absolutely summable potential is
`λ`-admissible *iff* `λ` is finite, so finiteness of `λ` in (4.23) is not a restriction that can be
dropped.) The reduction to the probability case is Remark (1.28)(3), formalized in
`GibbsMeasure/Specification/Rescaling.lean`. This file carries the Gibbsian part of the development
over to that generality.

## Main definitions

* `Potential.gibbsSpecificationOfSigmaFiniteAdmissible`: **Georgii Definition (2.9) verbatim** —
  a `λ`-admissible potential and a σ-finite non-zero a priori measure.
* `Potential.gibbsSpecificationOfFiniteReference`: the specialization to an absolutely summable
  potential and an arbitrary finite non-zero a priori measure.
* `Potential.sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero`: the existing
  `Potential.sigmaFiniteGibbsSpecificationOfAdmissible` with its `[IsProbabilityMeasure ν]`
  hypothesis weakened to `[SigmaFinite ν] [NeZero ν]`.

## Main results

* `Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set`,
  `Potential.gibbsSpecificationOfFiniteReference_apply_set`: the Gibbs kernels in Georgii's explicit
  form `γ_Λ(A|η) = Z_Λ(η)⁻¹ ∫_A e^{-βH_Λ} dλ_Λ(·|η)`.
* `Potential.gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable`:
  rescaling `λ` to a probability measure does not change `γ^Φ`.
* `Potential.GP_gibbsSpecificationOfFiniteReference_nonempty`,
  `Potential.isCompact_setOf_mem_GP_gibbsSpecificationOfFiniteReference`:
  **Georgii Theorem (4.23)(a)** for an arbitrary finite non-zero `λ`.
* `Potential.isCompact_closure_iUnion_setOf_mem_GP_ofFiniteReference` and its per-site form:
  **Georgii Theorem (4.23)(b)**.
* `Potential.BSpace.isClosed_graph_GP_ofFiniteReference`,
  `Potential.BSpace.isClosed_setOf_exists_mem_GP_ofFiniteReference`:
  **Georgii Theorem (4.23)(c), (d)**.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option backward.isDefEq.respectTransparency false

open Finset Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Potential

open Specification MeasureTheory

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E} {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]

omit [Countable S] [IsPotential Φ] in
/-- **Georgii (2.14) ⇒ λ-admissibility for a general finite a priori measure.** An absolutely
summable potential is admissible for every finite non-zero reference measure: the partition
functions are non-zero and finite. This is the probability case transported along the rescaling of
Remark (1.28)(3). -/
theorem isSigmaFiniteLambdaAdmissible_boltzmannFactor (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β) := by
  have h := isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν.probNormalize β
  rw [isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible] at h
  exact (isSigmaFiniteLambdaAdmissible_probNormalize (S := S) (E := E) ν).1 h

/-- **Georgii Definition (2.9), verbatim.** The Gibbsian specification
`γ^Φ_Λ(·|ω) = ρ^Φ_Λ λ_Λ(·|ω)` of a `λ`-admissible potential and a σ-finite non-zero a priori
measure `λ`; `λ`-admissibility is Georgii's condition (2.7) that all partition functions
`Z^Φ_Λ(ω) = λ_Λ h^Φ_Λ(ω)` be finite (and, as `h^Φ > 0`, non-zero). -/
noncomputable def gibbsSpecificationOfSigmaFiniteAdmissible (Ψ : Potential S E) [IsPotential Ψ]
    [IsSummable Ψ] (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor β)) :
    Specification S E :=
  Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor β)
    (isPremodifier_boltzmannFactor (Φ := Ψ) β) hadm

/-- Georgii (2.9): the Gibbs kernels are `Z_Λ(η)⁻¹ e^{-βH_Λ} λ_Λ(·|η)`. -/
theorem gibbsSpecificationOfSigmaFiniteAdmissible_apply_set (Ψ : Potential S E) [IsPotential Ψ]
    [IsSummable Ψ] (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hadm : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor β))
    (Λ : Finset S) (η : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsSpecificationOfSigmaFiniteAdmissible Ψ ν β hadm Λ η A
      = (sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor β) Λ η)⁻¹ *
        ∫⁻ ω in A, Ψ.boltzmannFactor β Λ ω
          ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) :=
  withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E)
    (ρ := Ψ.boltzmannFactor β) ν (isPremodifier_boltzmannFactor (Φ := Ψ) β) hA η

variable (Φ) in
/-- **Georgii Definition (2.9) for an arbitrary finite non-zero a priori measure `λ`.** The
Gibbsian specification `γ^Φ_Λ(·|η) = Z_Λ(η)⁻¹ e^{-βH_Λ} λ_Λ(·|η)` of an absolutely summable
potential, with no normalization assumption on `λ`. -/
noncomputable def gibbsSpecificationOfFiniteReference (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) : Specification S E :=
  gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν β)

/-- The Gibbs kernels of a general finite reference measure, in Georgii's form `ρ_Λ λ_Λ`. -/
@[simp] lemma gibbsSpecificationOfFiniteReference_apply (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) (Λ : Finset S) (η : S → E) :
    gibbsSpecificationOfFiniteReference Φ ν β Λ η
      = (sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η).withDensity
        (sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ) := rfl

/-- **Georgii (2.9), explicit form.** For every finite non-zero a priori measure `λ`,
`γ^Φ_Λ(A|η) = (∫_A e^{-βH_Λ} dλ_Λ(·|η)) / Z_Λ(η)`. -/
theorem gibbsSpecificationOfFiniteReference_apply_set (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) (Λ : Finset S) (η : S → E) {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsSpecificationOfFiniteReference Φ ν β Λ η A
      = (sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η)⁻¹ *
        ∫⁻ ω in A, Φ.boltzmannFactor β Λ ω
          ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := by
  rw [gibbsSpecificationOfFiniteReference_apply]
  exact withDensity_sigmaFinitePremodifierNorm_apply (S := S) (E := E)
    (ρ := Φ.boltzmannFactor β) ν (isPremodifier_boltzmannFactor (Φ := Φ) β) hA η

/-- **Georgii Remark (1.28)(3) for Gibbsian specifications.** The Gibbsian specification of a
finite non-zero a priori measure is the Gibbsian specification of the normalized probability
measure: rescaling `λ` does not change `γ^Φ`. -/
theorem gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    gibbsSpecificationOfFiniteReference Φ ν β
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν.probNormalize β := by
  rw [gibbsSpecificationOfFiniteReference, gibbsSpecificationOfSigmaFiniteAdmissible,
    lambdaSpecification_probNormalize (S := S) (E := E) ν
      (isPremodifier_boltzmannFactor (Φ := Φ) β)
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν β)
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν.probNormalize β),
    lambdaSpecification_eq_modification_isssd (S := S) (E := E) ν.probNormalize
      (isPremodifier_boltzmannFactor (Φ := Φ) β)
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν.probNormalize β)
      (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν.probNormalize β)]
  rfl

/-- For a probability a priori measure the two definitions agree. -/
theorem gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ) :
    gibbsSpecificationOfFiniteReference Φ ν β
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β := by
  rw [gibbsSpecificationOfFiniteReference, gibbsSpecificationOfSigmaFiniteAdmissible,
    lambdaSpecification_eq_modification_isssd (S := S) (E := E) ν
      (isPremodifier_boltzmannFactor (Φ := Φ) β)
      (isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν β)
      (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν β)]
  rfl

/-! ### Removing the probability restriction from the σ-finite Gibbs specification -/

/-- **`Potential.sigmaFiniteGibbsSpecificationOfAdmissible` without the probability restriction.**
The σ-finite-reference Gibbs kernels of a finite-range potential form a specification over *any*
σ-finite non-zero a priori measure, not only over a probability measure. -/
noncomputable def sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero (Ψ : Potential S E)
    [IsFiniteRange Ψ] [IsPotential Ψ] (β : ℝ) (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hZ : IsSigmaFiniteBoltzmannAdmissible (S := S) (E := E) Ψ β ν) : Specification S E :=
  Specification.lambdaSpecification (S := S) (E := E) ν (boltzmannWeight (Φ := Ψ) β)
    (isPremodifier_boltzmannWeight (Φ := Ψ) β) hZ

omit [Countable S] in
lemma sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero_apply (Ψ : Potential S E)
    [IsFiniteRange Ψ] [IsPotential Ψ] (β : ℝ) (ν : Measure E) [SigmaFinite ν] [NeZero ν]
    (hZ : IsSigmaFiniteBoltzmannAdmissible (S := S) (E := E) Ψ β ν) (Λ : Finset S) :
    sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero Ψ β ν hZ Λ
      = sigmaFiniteGibbsKernel (S := S) (E := E) Ψ β ν Λ := rfl

omit [Countable S] in
/-- For a probability a priori measure this is the existing
`Potential.sigmaFiniteGibbsSpecificationOfAdmissible`. -/
lemma sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero_eq (Ψ : Potential S E)
    [IsFiniteRange Ψ] [IsPotential Ψ] (β : ℝ) (ν : Measure E) [IsProbabilityMeasure ν]
    (hZ : IsSigmaFiniteBoltzmannAdmissible (S := S) (E := E) Ψ β ν) :
    sigmaFiniteGibbsSpecificationOfAdmissibleOfNeZero Ψ β ν hZ
      = sigmaFiniteGibbsSpecificationOfAdmissible (S := S) (E := E) Ψ β ν hZ :=
  Specification.ext fun _Λ ↦ rfl

end Potential

namespace Potential

open Specification MeasureTheory MeasureTheory.GibbsMeasure Filter Topology

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E} {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- **Georgii Example (2.25)(ii) for a general finite a priori measure.** -/
theorem isQuasilocal_gibbsSpecificationOfFiniteReference (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) : (gibbsSpecificationOfFiniteReference Φ ν β).IsQuasilocal := by
  rw [gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable]
  exact isQuasilocal_gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν.probNormalize β

/-- **Georgii (4.14)(1) for a general finite a priori measure.** -/
theorem gibbsSpecificationOfFiniteReference_apply_le (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    gibbsSpecificationOfFiniteReference Φ ν β Λ η A ≤
      ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν.probNormalize) A := by
  rw [gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable]
  exact gibbsSpecificationOfAbsolutelySummable_apply_le (Φ := Φ) ν.probNormalize β Λ η hA

variable [StandardBorelSpace E]

/-- **Georgii Theorem (4.23)(a), existence, for a general finite a priori measure.** -/
theorem GP_gibbsSpecificationOfFiniteReference_nonempty (ν : Measure E) [IsFiniteMeasure ν]
    [NeZero ν] (β : ℝ) :
    (GP (S := S) (E := E) (gibbsSpecificationOfFiniteReference Φ ν β)).Nonempty := by
  rw [gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable]
  exact GP_gibbsSpecification_nonempty (Φ := Φ) ν.probNormalize β

/-- **Georgii Theorem (4.23)(a), compactness, for a general finite a priori measure.** -/
theorem isCompact_setOf_mem_GP_gibbsSpecificationOfFiniteReference (ν : Measure E)
    [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    IsCompact {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E) (gibbsSpecificationOfFiniteReference Φ ν β)} := by
  rw [gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable]
  exact isCompact_setOf_mem_GP_gibbsSpecification (Φ := Φ) ν.probNormalize β

/-- **Georgii Theorem (4.23)(b) for a general finite a priori measure.** -/
theorem isCompact_closure_iUnion_setOf_mem_GP_ofFiniteReference {ι : Type*}
    (Φs : ι → Potential S E) [∀ i, IsPotential (Φs i)] [∀ i, IsAbsolutelySummable (Φs i)]
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    {B : Finset S → ℝ} (hB : ∀ i Λ, (Φs i).hamiltonianBound Λ ≤ B Λ) :
    IsCompact (closure (⋃ i, {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E)
        (gibbsSpecificationOfFiniteReference (Φs i) ν β)})) := by
  have hrw : ∀ i, gibbsSpecificationOfFiniteReference (Φs i) ν β
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν.probNormalize β := fun i ↦
    gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable
      (Φ := Φs i) ν β
  simp only [hrw]
  exact isCompact_closure_iUnion_setOf_mem_GP Φs ν.probNormalize β hB

/-- **Georgii Theorem (4.23)(b), per-site form, for a general finite a priori measure.** -/
theorem isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top_ofFiniteReference {ι : Type*}
    (Φs : ι → Potential S E) [∀ i, IsPotential (Φs i)] [∀ i, IsAbsolutelySummable (Φs i)]
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (hb : ∀ a : S, (⨆ i, (Φs i).normAt a) < ⊤) :
    IsCompact (closure (⋃ i, {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E)
        (gibbsSpecificationOfFiniteReference (Φs i) ν β)})) := by
  have hrw : ∀ i, gibbsSpecificationOfFiniteReference (Φs i) ν β
      = gibbsSpecificationOfAbsolutelySummable (Φ := Φs i) ν.probNormalize β := fun i ↦
    gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable
      (Φ := Φs i) ν β
  simp only [hrw]
  exact isCompact_closure_iUnion_setOf_mem_GP_of_iSup_normAt_lt_top Φs ν.probNormalize β hb

end Potential

namespace Potential

open Specification MeasureTheory MeasureTheory.GibbsMeasure Filter Topology

namespace BSpace

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E}
  (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)

/-- The Gibbsian specification of an element of `ℬ` for a general finite non-zero a priori
measure (Georgii Definition (2.9)). -/
noncomputable def gibbsSpecificationOfFiniteReference (Φ : BSpace S E) : Specification S E :=
  Potential.gibbsSpecificationOfFiniteReference (Φ : Potential S E) ν β

lemma gibbsSpecificationOfFiniteReference_eq (Φ : BSpace S E) :
    BSpace.gibbsSpecificationOfFiniteReference ν β Φ
      = BSpace.gibbsSpecification ν.probNormalize β Φ :=
  Potential.gibbsSpecificationOfFiniteReference_eq_gibbsSpecificationOfAbsolutelySummable
    (Φ := (Φ : Potential S E)) ν β

/-- **Georgii Theorem (4.23)(c) for a general finite a priori measure.** -/
theorem isClosed_graph_GP_ofFiniteReference :
    IsClosed {p : BSpace S E × WithLocalConvergence S E |
      p.2.toMeasure ∈ GP (S := S) (E := E)
        (BSpace.gibbsSpecificationOfFiniteReference ν β p.1)} := by
  simp only [gibbsSpecificationOfFiniteReference_eq]
  exact BSpace.isClosed_graph_GP ν.probNormalize β

/-- **Georgii Theorem (4.23)(d) for a general finite a priori measure.** -/
theorem isClosed_setOf_exists_mem_GP_ofFiniteReference [StandardBorelSpace E]
    {F : Set (WithLocalConvergence S E)} (hF : IsClosed F) :
    IsClosed {Φ : BSpace S E | ∃ μ ∈ F,
      μ.toMeasure ∈ GP (S := S) (E := E)
        (BSpace.gibbsSpecificationOfFiniteReference ν β Φ)} := by
  simp only [gibbsSpecificationOfFiniteReference_eq]
  exact BSpace.isClosed_setOf_exists_mem_GP ν.probNormalize β hF

end BSpace

end Potential

end

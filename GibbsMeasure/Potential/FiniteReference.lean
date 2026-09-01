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
* `Potential.exists_mem_quasilocalFunctions_toReal_sigmaFinitePremodifierNorm_boltzmannFactor`:
  **Georgii Example (2.25)(ii)** — the densities `ρ_Λ^Φ` are bounded quasilocal, `ρ_Λ^Φ ∈ 𝓛̄`;
  `Potential.isQuasilocal_gibbsSpecificationOfFiniteReference` is the specification-level
  consequence.
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

omit [Countable S] in
/-- **Georgii Example (2.25)(ii), full conclusion, for a probability a priori measure.** The
density `ρ_Λ^Φ = h_Λ^Φ / Z_Λ^Φ` of the Gibbsian specification of an absolutely summable potential
is itself a bounded quasilocal observable: `ρ_Λ^Φ ∈ 𝓛̄`. The witness is
`h_Λ^Φ · (γ_Λ h_Λ^Φ)⁻¹`, quasilocal because `𝓛̄` is a closed subalgebra containing the Boltzmann
factor and stable under the action of the independent specification. -/
theorem exists_mem_quasilocalFunctions_toReal_premodifierNorm_boltzmannFactor (ν : Measure E)
    [IsProbabilityMeasure ν] (β : ℝ) (Λ : Finset S) :
    ∃ r ∈ quasilocalFunctions S E, ∀ η : S → E,
      (⇑r) η = (premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η).toReal := by
  classical
  set H : lp (fun _ : S → E ↦ ℝ) ∞ := β • Φ.hamiltonianLp Λ with hHdef
  have hH : H ∈ quasilocalFunctions S E :=
    Subalgebra.smul_mem _ (hamiltonianLp_mem_quasilocalFunctions (Φ := Φ) Λ) β
  set h : lp (fun _ : S → E ↦ ℝ) ∞ := boltzmann H with hh
  set Z : lp (fun _ : S → E ↦ ℝ) ∞ := action (isssd ν) Λ h with hZ
  have hZpos : ∀ η, 0 < (⇑Z) η := fun η ↦
    lt_of_lt_of_le (Real.exp_pos _) (le_action_boltzmann H hH Λ η)
  have hZql : Z ∈ quasilocalFunctions S E :=
    (isResampling_isssd ν).isQuasilocal Λ _ (boltzmann_mem_quasilocalFunctions hH)
  have hZmem : (fun η ↦ ((⇑Z) η)⁻¹) ∈ lp (fun _ : S → E ↦ ℝ) ∞ :=
    memℓp_infty ⟨(Real.exp (-‖H‖))⁻¹, by
      rintro _ ⟨η, rfl⟩
      change ‖((⇑Z) η)⁻¹‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hZpos η))]
      exact inv_anti₀ (Real.exp_pos _) (le_action_boltzmann H hH Λ η)⟩
  set W : lp (fun _ : S → E ↦ ℝ) ∞ := ⟨_, hZmem⟩ with hW
  have hWql : W ∈ quasilocalFunctions S E :=
    Subalgebra.inv_mem_lp (Subalgebra.isClosed_topologicalClosure _) hZql
      (Real.exp_pos (-‖H‖)) (le_action_boltzmann H hH Λ) fun _ ↦ rfl
  have hbf : Φ.boltzmannFactor β Λ = fun x ↦ ENNReal.ofReal ((⇑h) x) :=
    congrFun (boltzmannFactor_eq_ofReal_boltzmann (Φ := Φ) β) Λ
  refine ⟨h * W, Subalgebra.mul_mem _ (boltzmann_mem_quasilocalFunctions hH) hWql, fun η ↦ ?_⟩
  have hZof : premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      = ENNReal.ofReal ((⇑Z) η) := by
    rw [hZ, action_apply,
      ofReal_integral_eq_lintegral_ofReal (integrable_boltzmann (γ := isssd ν) hH Λ η)
        (.of_forall fun x ↦ (Real.exp_pos _).le),
      premodifierZ, hbf]
  have hmul : (⇑(h * W)) η = (⇑h) η * ((⇑Z) η)⁻¹ := by
    rw [lp.infty_coeFn_mul]; rfl
  rw [hmul, premodifierNorm, hZof, congrFun hbf η,
    ← ENNReal.ofReal_div_of_pos (hZpos η),
    ENNReal.toReal_ofReal
      ((div_pos (lt_of_lt_of_le (Real.exp_pos (-‖H‖)) (le_boltzmann H η)) (hZpos η)).le),
    div_eq_mul_inv]

omit [Countable S] in
/-- **Georgii Example (2.25)(ii), full conclusion, for a general finite a priori measure.** The
density `ρ_Λ^Φ = h_Λ^Φ / Z_Λ^Φ` of the Gibbsian specification of an absolutely summable potential
with respect to the reference kernel `λ_Λ` of an arbitrary finite non-zero `λ` is a bounded
quasilocal observable: `ρ_Λ^Φ ∈ 𝓛̄`. -/
theorem exists_mem_quasilocalFunctions_toReal_sigmaFinitePremodifierNorm_boltzmannFactor
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) (Λ : Finset S) :
    ∃ r ∈ quasilocalFunctions S E, ∀ η : S → E,
      (⇑r) η = (sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (Φ.boltzmannFactor β) Λ η).toReal := by
  obtain ⟨r, hrmem, hr⟩ :=
    exists_mem_quasilocalFunctions_toReal_premodifierNorm_boltzmannFactor (Φ := Φ)
      ν.probNormalize β Λ
  set a : ℝ≥0∞ := (ν Set.univ) ^ Λ.card with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (univ_ne_zero_of_neZero ν)
  have hat : a ≠ ⊤ := ENNReal.pow_ne_top (measure_ne_top ν _)
  refine ⟨(a.toReal)⁻¹ • r, Subalgebra.smul_mem _ hrmem _, fun η ↦ ?_⟩
  have hZsmul : sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      = a * sigmaFiniteLambdaZ (S := S) (E := E) ν.probNormalize (Φ.boltzmannFactor β) Λ η :=
    sigmaFiniteLambdaZ_of_smul (S := S) (E := E) (ρ := Φ.boltzmannFactor β) ν.probNormalize ν
      (Measure.smul_probNormalize ν) Λ η
  have hnorm : sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      = a⁻¹ * premodifierNorm (S := S) (E := E) ν.probNormalize (Φ.boltzmannFactor β) Λ η := by
    rw [premodifierNorm_eq_sigmaFinitePremodifierNorm, sigmaFinitePremodifierNorm,
      sigmaFinitePremodifierNorm, hZsmul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl ha0) (Or.inl hat), mul_assoc]
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hr η, hnorm, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

omit [Countable S] in
/-- The unbundled form of Georgii Example (2.25)(ii): the density `ρ_Λ^Φ` is quasilocal in the
sense of Georgii (2.22). -/
theorem isQuasilocalFun_toReal_sigmaFinitePremodifierNorm_boltzmannFactor (ν : Measure E)
    [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) (Λ : Finset S) :
    IsQuasilocalFun fun η : S → E ↦
      (sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η).toReal := by
  obtain ⟨r, hrmem, hr⟩ :=
    exists_mem_quasilocalFunctions_toReal_sigmaFinitePremodifierNorm_boltzmannFactor (Φ := Φ)
      ν β Λ
  rw [← funext hr]
  exact (mem_quasilocalFunctions_iff_isQuasilocalFun.1 hrmem).2

/-- **Georgii Example (2.25), specification-level conclusion, for a general finite a priori
measure**, via (2.24)(b): the Gibbsian specification `γ^Φ` is quasilocal. The full conclusion of
Example (2.25)(ii), that the densities themselves are bounded quasilocal (`ρ_Λ^Φ ∈ 𝓛̄`), is
`Potential.exists_mem_quasilocalFunctions_toReal_sigmaFinitePremodifierNorm_boltzmannFactor`. -/
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

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Specification.InhomogeneousReference

/-!
# Existence over per-site a priori measures

Georgii Theorem (4.23)(a) with the single a priori measure `λ` replaced by a family `(λ_i)`, one
probability measure per site: the case needed for the existence half of Theorem (8.39), where the
self-energies `Φ_{i}` absorbed into the reference measure are site-dependent.

Georgii's proof carries over verbatim once the two inputs are stated at the right generality: the
reference specification only has to resample volumes (`Specification.IsResampling`, for
quasilocality) and to forget the boundary condition on inside-volume events
(`Specification.HasFreeMeasure`, for local equicontinuity).

## Main statements

* `Potential.gibbsSpecificationFamily`: Georgii Definition (2.9) over `Specification.isssdFamily`.
* `Potential.GP_gibbsSpecificationFamily_nonempty`: Georgii (4.23)(a).
* `Potential.isCompact_setOf_mem_GP_gibbsSpecificationFamily`: its compactness half.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Topology

noncomputable section

namespace Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]
  (ν : S → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (β : ℝ)

variable (Φ) in
/-- **Georgii Definition (2.9) over a family of a priori measures.** The Gibbsian specification of
an absolutely summable potential relative to `Specification.isssdFamily ν`. -/
def gibbsSpecificationFamily : Specification S E :=
  Specification.premodification (Specification.isssdFamily ν) (Φ.boltzmannFactor β)
    (Specification.isResampling_isssdFamily ν) (isPremodifier_boltzmannFactor (Φ := Φ) β)
    (isRelAdmissible_boltzmannFactor (γ := Specification.isssdFamily ν) β)

lemma gibbsSpecificationFamily_apply (Λ : Finset S) (η : S → E) :
    gibbsSpecificationFamily Φ ν β Λ η
      = (Specification.isssdFamily ν Λ η).withDensity
          (Specification.relNorm (Specification.isssdFamily ν) (Φ.boltzmannFactor β) Λ) := rfl

lemma gibbsSpecificationFamily_const (lam : Measure E) [IsProbabilityMeasure lam] :
    gibbsSpecificationFamily Φ (fun _ ↦ lam) β
      = Φ.gibbsSpecificationOfAbsolutelySummable lam β := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun η ↦ ?_
  rw [gibbsSpecificationFamily_apply, show Specification.isssdFamily (S := S) (E := E)
    (fun _ ↦ lam) = Specification.isssd lam from Specification.isssdFamily_const lam]
  rfl

/-- **Georgii Example (2.25)(ii)** over a family of a priori measures. -/
theorem isQuasilocal_gibbsSpecificationFamily :
    (gibbsSpecificationFamily Φ ν β).IsQuasilocal := by
  rw [gibbsSpecificationFamily, Specification.premodification]
  simp only [boltzmannFactor_eq_ofReal_boltzmann (Φ := Φ) β]
  exact (Specification.isResampling_isssdFamily ν).isQuasilocal_modification_relNorm
    (H := fun Λ ↦ β • Φ.hamiltonianLp Λ)
    (fun Λ ↦ Subalgebra.smul_mem _ (hamiltonianLp_mem_quasilocalFunctions (Φ := Φ) Λ) β) _

/-- **Georgii (4.14)(1)** over a family of a priori measures: on `𝓕_Λ`-events the specification is
dominated by `e^{2|β| ‖Φ‖_Λ}` times the free measure `⨂ i, ν i`. -/
lemma gibbsSpecificationFamily_apply_le (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    gibbsSpecificationFamily Φ ν β Λ η A
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) * Measure.infinitePi ν A := by
  rw [gibbsSpecificationFamily_apply, withDensity_apply _ (cylinderEvents_le_pi _ hA),
    ← Specification.isssdFamily_apply_of_mem_cylinderEvents ν Λ η hA, ← setLIntegral_const]
  exact setLIntegral_mono_ae (by fun_prop)
    (.of_forall fun x _ ↦ relNorm_boltzmannFactor_le (Φ := Φ) β Λ x)

variable (Φ) in
/-- The dominating measures of Georgii (4.14)(1) for the per-site family. -/
def dominatingMeasureFamily (Λ : Finset S) : Measure (S → E) :=
  ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) • Measure.infinitePi ν

instance (Λ : Finset S) : IsFiniteMeasure (dominatingMeasureFamily Φ ν β Λ) := by
  constructor
  rw [dominatingMeasureFamily, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

/-- **Georgii Comment (4.14)(1)** over a family of a priori measures. -/
theorem locallyEquicontinuous_finiteVolumeDistributionsFamily (η : S → E) :
    LocallyEquicontinuous atTop
      (finiteVolumeDistributions (gibbsSpecificationFamily Φ ν β) η) := by
  refine locallyEquicontinuous_of_eventually_boundedOn
    (Specification.hasFreeMeasure_isssdFamily ν)
    (fun _ ↦ Specification.relNorm (Specification.isssdFamily ν) (Φ.boltzmannFactor β))
    (fun _ ↦ (isPremodifier_boltzmannFactor (Φ := Φ) β).isModifier_relNorm
      (Specification.isResampling_isssdFamily ν)
      (isRelAdmissible_boltzmannFactor (γ := Specification.isssdFamily ν) β))
    id tendsto_id (fun _ ↦ ⟨Measure.dirac η, inferInstance⟩) _ (fun Λ ↦ ?_) (fun Λ ε hε ↦ ?_)
  · exact (Subtype.ext (Measure.dirac_bind
      ((gibbsSpecificationFamily Φ ν β).measurable_kernel_toMeasure Λ) η)).symm
  · refine ⟨univ, ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)),
      MeasurableSet.univ, ENNReal.ofReal_ne_top,
      Eventually.of_forall fun a ω _ ↦ relNorm_boltzmannFactor_le (Φ := Φ) β Λ ω, ?_⟩
    have hzero : (fun Λ' : Finset S ↦
        (finiteVolumeDistributions (gibbsSpecificationFamily Φ ν β) η Λ' :
          Measure (S → E)) (univ : Set (S → E))ᶜ) = fun _ ↦ 0 := by
      funext Λ'; simp
    rw [hzero, limsup_const]
    exact hε.le

lemma setOf_mem_GP_gibbsSpecificationFamily_subset_dominatedBy :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (gibbsSpecificationFamily Φ ν β)}
      ⊆ dominatedBy S E (dominatingMeasureFamily Φ ν β) := by
  intro μ hμ Λ A hA
  refine apply_le_of_mem_GP hμ Λ (cylinderEvents_le_pi (X := fun _ : S ↦ E) _ hA) fun ω ↦ ?_
  rw [dominatingMeasureFamily, Measure.smul_apply, smul_eq_mul]
  exact gibbsSpecificationFamily_apply_le ν β Λ ω hA

variable [StandardBorelSpace E]

/-- **Georgii Theorem (4.23)(a), existence, over per-site a priori measures.** -/
theorem GP_gibbsSpecificationFamily_nonempty :
    (GP (S := S) (E := E) (gibbsSpecificationFamily Φ ν β)).Nonempty := by
  obtain ⟨η⟩ : Nonempty (S → E) := by
    rcases isEmpty_or_nonempty S with hS | ⟨⟨i⟩⟩
    · exact ⟨fun i ↦ (hS.false i).elim⟩
    · have : Nonempty E := (ν i).nonempty_of_neZero
      exact ⟨fun _ ↦ Classical.arbitrary E⟩
  obtain ⟨μ, hμ, -⟩ := exists_isLocalThermodynamicLimit_mem_GP
    (isQuasilocal_gibbsSpecificationFamily (Φ := Φ) ν β) η
    (locallyEquicontinuous_finiteVolumeDistributionsFamily (Φ := Φ) ν β η)
  exact ⟨μ, hμ⟩

/-- **Georgii Theorem (4.23)(a), compactness, over per-site a priori measures.** -/
theorem isCompact_setOf_mem_GP_gibbsSpecificationFamily :
    IsCompact {μ : WithLocalConvergence S E |
      μ.toMeasure ∈ GP (S := S) (E := E) (gibbsSpecificationFamily Φ ν β)} :=
  (isCompact_dominatedBy (dominatingMeasureFamily Φ ν β)).of_isClosed_subset
    (isClosed_setOf_mem_GP (isQuasilocal_gibbsSpecificationFamily (Φ := Φ) ν β))
    (setOf_mem_GP_gibbsSpecificationFamily_subset_dominatedBy (Φ := Φ) ν β)

end Potential

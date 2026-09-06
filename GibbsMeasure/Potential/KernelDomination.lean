/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.FiniteReference

/-!
# Domination of a Gibbs kernel by the a priori kernel

A Gibbs kernel `γ^Φ_Λ(·|η) = Z_Λ(η)⁻¹ e^{-βH_Λ} λ_Λ(·|η)` is absolutely continuous with respect
to its a priori kernel `λ_Λ(·|η)`, with a density that is controlled by the *oscillation* of the
Hamiltonian `H_Λ` over the configurations that agree with `η` outside `Λ`: the numerator and the
denominator of the density are integrals of the same Boltzmann factor, and only their ratio
matters.

* `Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le`:
  `γ^Φ_Λ(A|η) ≤ e^c λ_Λ(A|η)` whenever `β (H_Λ(σ') - H_Λ(σ)) ≤ c` for all `σ, σ'` agreeing with
  `η` off `Λ`.

This is the estimate behind every "high temperature" argument that compares a conditional
probability to an a priori probability; the a priori measure is assumed to be a probability
measure, which is the normalisation `λ̃ = λ(E)⁻¹ λ` under which such bounds are stated.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E}

/-- **A Gibbs kernel is dominated by its a priori kernel**, with the constant given by the
oscillation of the Hamiltonian in `Λ`.  If `β (H_Λ(σ') - H_Λ(σ)) ≤ c` for every pair of
configurations `σ, σ'` that agree with the boundary condition `η` outside `Λ`, then

`γ^Φ_Λ(A|η) ≤ e^c λ_Λ(A|η)`

for every measurable `A`.  The proof is the elementary two-step estimate
`e^{-βH_Λ(σ)} ≤ e^c Z_Λ(η)` (integrate `e^{-βH_Λ(σ)} ≤ e^c e^{-βH_Λ(σ')}` in `σ'` against the
probability measure `λ_Λ(·|η)`), followed by `Z_Λ(η)⁻¹ ∫_A e^{-βH_Λ} dλ_Λ ≤ e^c λ_Λ(A|η)`. -/
theorem gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le
    (Ψ : Potential S E) [IsPotential Ψ] [IsSummable Ψ] (ν : Measure E) [IsProbabilityMeasure ν]
    (β : ℝ) (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Ψ.boltzmannFactor β)) (Λ : Finset S) (η : S → E) {c : ℝ}
    (hc : ∀ σ σ' : S → E, (∀ j ∉ Λ, σ j = η j) → (∀ j ∉ Λ, σ' j = η j) →
      β * (Ψ.hamiltonian Λ σ' - Ψ.hamiltonian Λ σ) ≤ c)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsSpecificationOfSigmaFiniteAdmissible Ψ ν β hadm Λ η A
      ≤ ENNReal.ofReal (Real.exp c) *
        Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η A := by
  classical
  set lam := Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η with hlam
  set Z := Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor β) Λ η with hZdef
  set C := ENNReal.ofReal (Real.exp c) with hC
  have hjuxt : Measurable (juxt (Λ := ((Λ : Finset S) : Set S)) η) :=
    Measurable.juxt (Λ := ((Λ : Finset S) : Set S)) (η := η) (𝓔 := mE)
  have hlam_map : lam = Measure.map (juxt (Λ := ((Λ : Finset S) : Set S)) η)
      (Measure.pi fun _ : Λ ↦ ν) := by
    rw [hlam, Specification.sigmaFiniteLambdaFun_apply_eq_map]
  have hbd : ∀ x : ↥Λ → E, ∀ j ∉ Λ, juxt ((Λ : Finset S) : Set S) η x j = η j := fun x j hj ↦
    juxt_apply_of_not_mem (by simpa using hj) x
  -- the Boltzmann factors of two admissible configurations differ by at most `e^c`
  have hpt : ∀ x y : ↥Λ → E,
      Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η x)
        ≤ C * Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η y) := by
    intro x y
    rw [hC, Potential.boltzmannFactor, Potential.boltzmannFactor,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [hc _ _ (hbd x) (hbd y)]))
  -- integrating the comparison in the second variable gives `e^{-βH_Λ} ≤ e^c Z_Λ(η)`
  have hmeas : Measurable fun y : ↥Λ → E ↦
      Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η y) :=
    (Potential.measurable_boltzmannFactor β Λ).comp hjuxt
  have hkey : ∀ x : ↥Λ → E,
      Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η x) ≤ C * Z := by
    intro x
    have hZ : Z = ∫⁻ y : ↥Λ → E, Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η y)
        ∂(Measure.pi fun _ : Λ ↦ ν) := by
      rw [hZdef, Specification.sigmaFiniteLambdaZ, ← hlam, hlam_map,
        lintegral_map (Potential.measurable_boltzmannFactor β Λ) hjuxt]
      rfl
    calc Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η x)
        = ∫⁻ _ : ↥Λ → E, Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η x)
            ∂(Measure.pi fun _ : Λ ↦ ν) := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ y : ↥Λ → E, C * Ψ.boltzmannFactor β Λ (juxt ((Λ : Finset S) : Set S) η y)
            ∂(Measure.pi fun _ : Λ ↦ ν) := lintegral_mono fun y ↦ hpt x y
      _ = C * Z := by rw [lintegral_const_mul _ hmeas, hZ]
  have hae : ∀ᵐ σ ∂lam, Ψ.boltzmannFactor β Λ σ ≤ C * Z := by
    rw [hlam_map]
    refine (ae_map_iff hjuxt.aemeasurable ?_).2 (Filter.Eventually.of_forall hkey)
    exact measurableSet_le (Potential.measurable_boltzmannFactor β Λ) measurable_const
  rw [gibbsSpecificationOfSigmaFiniteAdmissible_apply_set Ψ ν β hadm Λ η hA, ← hlam, ← hZdef]
  calc Z⁻¹ * ∫⁻ σ in A, Ψ.boltzmannFactor β Λ σ ∂lam
      ≤ Z⁻¹ * ∫⁻ _ in A, C * Z ∂lam := by
        gcongr Z⁻¹ * ?_
        exact lintegral_mono_ae (ae_restrict_of_ae hae)
    _ = Z⁻¹ * (C * Z * lam A) := by rw [setLIntegral_const]
    _ = C * lam A := by
        rw [show Z⁻¹ * (C * Z * lam A) = (Z⁻¹ * Z) * (C * lam A) by ring,
          ENNReal.inv_mul_cancel (hadm.ne_zero Λ η) (hadm.ne_top Λ η), one_mul]

end Potential

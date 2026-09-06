/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.ExpTiltComparison
public import GibbsMeasure.Specification.HeisenbergExistence
public import GibbsMeasure.Topology.LocalConvergenceIntegral

/-!
# Georgii, Proposition (20.7), second half: `𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`

`GibbsMeasure.Specification.HeisenbergExistence` proves `𝒢₀(Φ) ≠ ∅` and all the model-specific
inputs of the second half.  This file carries out Georgii's "a glance at the proof of Theorem
(4.17)": every cluster point of the fields `μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0` is a Gibbs measure for the
Gibbsian specification `γ^Φ` of (20.5).

## The two steps

* **Proposition (4.19) restricted to `Ω_t`.**  The elementary two-kernel estimate is
  `MeasureTheory.abs_expTilt_sub_le`
  (`GibbsMeasure/Mathlib/MeasureTheory/Integral/ExpTiltComparison.lean`), a statement about two
  energies on one finite measure space.  Here it is fed with the two finite-volume Gibbs kernels
  in the same volume, at the same boundary condition and over the same a priori measure:
  `toReal_gibbsRatio_eq_div` writes a normalised kernel `Z^{-1} ρ λ_Λ(·|ω)` as a ratio of two
  Bochner integrals over `E^Λ`, and
  `eventually_abs_heisenbergPeriodicGibbsSpec_sub_heisenbergSpecification_le` is the resulting
  `‖(γ_Λ^n 1_A - γ_Λ^Φ 1_A) 1_{Ω_t}‖ → 0`, uniform in the event `A` and in the boundary condition
  `ω ∈ Ω_t`.
* **The `ε`-assembly.**  `heisenbergGZero_subset_heisenbergGibbsMeasures`.  For a local event `A`
  and a volume `Λ`: the DLR equation `μ_n^Φ γ_Λ^n = μ_n^Φ` for `Λ ⊆ Λ(n)` is the consistency of
  `heisenbergPeriodicGibbsSpec` together with
  `heisenbergPeriodicGibbsSpec_latticeBox`; `γ_Λ^m 1_A` is a *local* function because `Φ^m` has
  finite range (`dependsOn_heisenbergPeriodicGibbsSpec_apply`), so local convergence integrates it;
  and `μ(Ω_t^c)`, `μ_n(Ω_t^c)` are uniformly small by (20.6)(iii).

## Deviations from Georgii

* Georgii's `β` is carried inside `J`, so the statement is for the specification at inverse
  temperature `1`; a low-temperature statement is the same theorem applied to `βJ`.
* `Specification.toReal_gibbsRatio_eq_div` is a statement about
  `Specification.sigmaFiniteLambdaFun` and belongs next to it in `GibbsMeasure/Specification.lean`;
  it is proved here because that file is outside the scope of the present change.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### A normalised finite-volume kernel as a ratio of two integrals over `E^Λ` -/

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

/-- **The value of `Z_Λ(ω)^{-1} ρ λ_Λ(·|ω)` as a ratio of two Bochner integrals over `E^Λ`.**
If the density `ρ` restricted to the fibre over `ω` is `ENNReal.ofReal ∘ f` for a nonnegative
measurable `f` on `E^Λ`, then

`(Z_Λ(ω)^{-1} λ_Λ(1_A ρ | ω)).toReal = (∫_{A'} f dλ^Λ) / (∫ f dλ^Λ)`,  `A' = juxt_Λ(ω)^{-1}(A)`.

No finiteness of `Z_Λ(ω)` is needed: both sides are `0` when it is infinite. -/
theorem toReal_gibbsRatio_eq_div (ν : Measure E) [SigmaFinite ν] (Λ : Finset S) (ω : S → E)
    {ρ : (S → E) → ℝ≥0∞} (hρ : Measurable ρ) {f : (Λ → E) → ℝ} (hf : Measurable f)
    (hf0 : ∀ ζ, 0 ≤ f ζ) (hρf : ∀ ζ, ρ (juxt (Λ : Set S) ω ζ) = ENNReal.ofReal (f ζ))
    {A : Set (S → E)} (hA : MeasurableSet A) :
    ((∫⁻ x, ρ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω))⁻¹
        * ∫⁻ x in A, ρ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω)).toReal
      = (∫ ζ in juxt (Λ : Set S) ω ⁻¹' A, f ζ ∂(Measure.pi fun _ : Λ ↦ ν))
        / ∫ ζ, f ζ ∂(Measure.pi fun _ : Λ ↦ ν) := by
  have hjm : Measurable (juxt (Λ := (Λ : Set S)) ω) := Measurable.juxt
  have hmap := sigmaFiniteLambdaFun_apply_eq_map (S := S) (E := E) ν Λ ω
  have hZ : (∫⁻ x, ρ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω))
      = ∫⁻ ζ, ENNReal.ofReal (f ζ) ∂(Measure.pi fun _ : Λ ↦ ν) := by
    rw [hmap, lintegral_map hρ hjm]
    exact lintegral_congr fun ζ ↦ hρf ζ
  have hN : (∫⁻ x in A, ρ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω))
      = ∫⁻ ζ in juxt (Λ : Set S) ω ⁻¹' A, ENNReal.ofReal (f ζ)
          ∂(Measure.pi fun _ : Λ ↦ ν) := by
    rw [hmap, setLIntegral_map hA hρ hjm]
    exact lintegral_congr fun ζ ↦ hρf ζ
  rw [hZ, hN, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← integral_eq_lintegral_of_nonneg_ae (.of_forall hf0) hf.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (.of_forall fun ζ ↦ hf0 ζ)
      hf.aestronglyMeasurable, div_eq_inv_mul]

end Specification

namespace MeasureTheory.GibbsMeasure

/-! ### The Gaussian control `Q(ζ) = ∑_{i ∈ Λ}[1 + |ζ_i|²]` on a block -/

section BlockGaussian

variable {d n : ℕ} {ν : Measure (Fin n → ℝ)}

/-- Measurability of the Gaussian weight of a block. -/
theorem measurable_exp_blockSum (Λ : Finset (Fin d → ℤ)) (a : ℝ) :
    Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦ Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i)) :=
  Real.continuous_exp.measurable.comp
    ((Finset.measurable_sum Finset.univ fun i _ ↦ measurable_const.add
      ((measurable_pi_apply i).dotProduct (measurable_pi_apply i))).const_mul a)

/-- **Georgii (20.3) on a block.**  The Gaussian weight `e^{a ∑_{i ∈ Λ}[1 + |ζ_i|²]}` is
`λ^Λ`-integrable at every rate `a`: the integral factorises over the sites, and each factor is
finite by (20.3). -/
theorem integrable_exp_blockSum [IsFiniteMeasure ν] (hexp : HasExpSqMoments ν)
    (Λ : Finset (Fin d → ℤ)) (a : ℝ) :
    Integrable (fun ζ : ↥Λ → (Fin n → ℝ) ↦ Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i)))
      (Measure.pi fun _ : ↥Λ ↦ ν) := by
  classical
  have hmeas := measurable_exp_blockSum (n := n) Λ a
  have hg : Measurable fun y : Fin n → ℝ ↦ ENNReal.ofReal (Real.exp (a * (1 + y ⬝ᵥ y))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.add (Finset.measurable_sum _ fun c _ ↦
        (measurable_pi_apply c).mul (measurable_pi_apply c))).const_mul a))
  have hprod : ∀ ζ : ↥Λ → (Fin n → ℝ),
      ENNReal.ofReal (Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i)))
        = ∏ i : ↥Λ, ENNReal.ofReal (Real.exp (a * (1 + ζ i ⬝ᵥ ζ i))) := fun ζ ↦ by
    rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ Real.exp_nonneg _]
  have hfin : (∫⁻ ζ, ENNReal.ofReal (Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i)))
      ∂(Measure.pi fun _ : ↥Λ ↦ ν)) ≠ ⊤ := by
    rw [lintegral_congr hprod]
    refine ne_top_of_le_ne_top ?_ (le_of_eq (lintegral_pi_prod (μ := fun _ : ↥Λ ↦ ν)
      (g := fun _ (y : Fin n → ℝ) ↦ ENNReal.ofReal (Real.exp (a * (1 + y ⬝ᵥ y))))
      fun _ ↦ hg))
    refine ENNReal.prod_ne_top fun i _ ↦ ?_
    have hint : Integrable (fun y : Fin n → ℝ ↦ Real.exp (a * (1 + y ⬝ᵥ y))) ν := by
      have hcongr : (fun y : Fin n → ℝ ↦ Real.exp (a * (1 + y ⬝ᵥ y)))
          = fun y ↦ Real.exp a * Real.exp (a * (y ⬝ᵥ y)) := by
        funext y; rw [← Real.exp_add]; ring_nf
      rw [hcongr]
      exact (hexp a).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y ↦ Real.exp_nonneg _)]
    exact ENNReal.ofReal_ne_top
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun ζ ↦ (Real.exp_pos _).le)]
  exact lt_top_iff_ne_top.2 hfin

/-- The product measure over a block of a finite non-zero a priori measure is non-zero. -/
theorem measurePi_ne_zero [IsFiniteMeasure ν] (hν : ν ≠ 0) (Λ : Finset (Fin d → ℤ)) :
    (Measure.pi fun _ : ↥Λ ↦ ν) ≠ 0 := by
  have h : (Measure.pi fun _ : ↥Λ ↦ ν) Set.univ = ∏ _i : ↥Λ, ν Set.univ := by
    rw [← Set.pi_univ Set.univ, Measure.pi_pi]
  refine fun hc ↦ ?_
  rw [hc] at h
  exact (Finset.prod_ne_zero_iff.2 fun _ _ ↦ (Measure.measure_univ_pos.2 hν).ne')
    (h.symm.trans (Measure.coe_zero ▸ rfl))

/-- **Georgii's `δ` of §20.1 on a block.**  The Gaussian weight at a non-positive rate has positive
`λ^Λ`-integral: it is everywhere positive and `λ^Λ ≠ 0`. -/
theorem integral_exp_blockSum_pos [IsFiniteMeasure ν] (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (Λ : Finset (Fin d → ℤ)) (a : ℝ) :
    0 < ∫ ζ : ↥Λ → (Fin n → ℝ), Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))
      ∂(Measure.pi fun _ : ↥Λ ↦ ν) := by
  rw [integral_pos_iff_support_of_nonneg (fun ζ ↦ (Real.exp_pos _).le)
    (integrable_exp_blockSum hexp Λ a)]
  have hsupp : (Function.support fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp (a * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))) = Set.univ :=
    Set.eq_univ_of_forall fun ζ ↦ (Real.exp_pos _).ne'
  rw [hsupp]
  exact Measure.measure_univ_pos.2 (measurePi_ne_zero hν Λ)

end BlockGaussian

/-! ### The two finite-volume kernels as ratios of integrals over `E^Λ` -/

section KernelRatio

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- The block sum `∑_{i ∈ Λ}[1 + |x_i|²]` of a configuration resampled in `Λ` only sees the new
spins. -/
theorem sum_one_add_dotProduct_juxt (Λ : Finset (Fin d → ℤ))
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) (ζ : ↥Λ → (Fin n → ℝ)) :
    ∑ i ∈ Λ, (1 + juxt (Λ : Set (Fin d → ℤ)) ω ζ i ⬝ᵥ juxt (Λ : Set (Fin d → ℤ)) ω ζ i)
      = ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
  set y : (Fin d → ℤ) → (Fin n → ℝ) := juxt (Λ : Set (Fin d → ℤ)) ω ζ with hy
  rw [← Finset.sum_coe_sort Λ fun i ↦ 1 + y i ⬝ᵥ y i]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hyi : y (i : Fin d → ℤ) = ζ i := by
    rw [hy, juxt_apply_of_mem (Finset.mem_coe.mpr i.2) ζ, Subtype.coe_eta]
  rw [hyi]

/-- Resampling inside `Λ` does not leave `Ω_*`. -/
theorem juxt_mem_slowGrowthTailSet {Λ : Finset (Fin d → ℤ)}
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) (ζ : ↥Λ → (Fin n → ℝ)) :
    juxt (Λ : Set (Fin d → ℤ)) ω ζ ∈ slowGrowthTailSet d n :=
  mem_slowGrowthTailSet_of_eqOn_compl
    (fun _i hi ↦ (juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hi) ζ).symm) hω

/-- **The finite-volume kernel of the periodic modification `Φ^n` as a ratio of two integrals over
`E^Λ`.**  This is Georgii's `γ_Λ^n(A|ω) = Z_Λ^n(ω)^{-1} λ_Λ(1_A e^{-H_Λ^{Φ^n}}|ω)` with the
reference measure pushed back to the block. -/
theorem toReal_heisenbergPeriodicGibbsSpec_apply [IsFiniteMeasure ν] [NeZero ν] {L : ℕ}
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1))
    (Λ : Finset (Fin d → ℤ)) (ω : (Fin d → ℤ) → (Fin n → ℝ))
    {A : Set ((Fin d → ℤ) → (Fin n → ℝ))} (hA : MeasurableSet A) :
    (heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm Λ ω A).toReal
      = (∫ ζ in juxt (Λ : Set (Fin d → ℤ)) ω ⁻¹' A,
            Real.exp (-((heisenbergPeriodicPotential n J L).hamiltonian Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) ∂(Measure.pi fun _ : ↥Λ ↦ ν))
        / ∫ ζ, Real.exp (-((heisenbergPeriodicPotential n J L).hamiltonian Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) ∂(Measure.pi fun _ : ↥Λ ↦ ν) := by
  have hpot := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  rw [heisenbergPeriodicGibbsSpec,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set _ _ _ _ _ _ hA,
    Specification.sigmaFiniteLambdaZ]
  have hfmeas : Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp (-((heisenbergPeriodicPotential n J L).hamiltonian Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) :=
    (((Potential.measurable_hamiltonian (Φ := heisenbergPeriodicPotential n J L) Λ).comp
      Measurable.juxt).neg).exp
  refine Specification.toReal_gibbsRatio_eq_div ν Λ ω
    (Potential.measurable_boltzmannFactor 1 Λ)
    (f := fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp (-((heisenbergPeriodicPotential n J L).hamiltonian Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ)))) hfmeas
    (fun ζ ↦ (Real.exp_pos _).le) (fun ζ ↦ ?_) hA
  rw [Potential.boltzmannFactor]
  congr 2
  ring

/-- **The finite-volume kernel of Georgii's (20.5) as a ratio of two integrals over `E^Λ`**, at a
boundary condition in `Ω_*`.  The artificial branch of (20.5) is not seen: resampling inside `Λ`
keeps the configuration in `Ω_*`. -/
theorem toReal_heisenbergSpecification_apply [IsFiniteMeasure ν] [NeZero ν]
    {hexp : HasExpSqMoments ν} {heven : ∀ m, J (-m) = J m} {hJ0 : J 0 = 0}
    {hJ : IsSlowlySummable J} (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n)
    {A : Set ((Fin d → ℤ) → (Fin n → ℝ))} (hA : MeasurableSet A) :
    (heisenbergSpecification J ν 1 hexp heven hJ0 hJ Λ ω A).toReal
      = (∫ ζ in juxt (Λ : Set (Fin d → ℤ)) ω ⁻¹' A,
            Real.exp (-((heisenbergPotential n J).hamiltonian Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) ∂(Measure.pi fun _ : ↥Λ ↦ ν))
        / ∫ ζ, Real.exp (-((heisenbergPotential n J).hamiltonian Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) ∂(Measure.pi fun _ : ↥Λ ↦ ν) := by
  have hρm : Measurable ((heisenbergPotential n J).tailBoltzmannFactor
      (slowGrowthTailSet d n) 1 Λ) :=
    Potential.measurable_tailBoltzmannFactor measurableSet_slowGrowthTailSet
      (isSummableOn_heisenbergPotential heven hJ0 hJ) 1 Λ
  have hpt : ∀ ζ : ↥Λ → (Fin n → ℝ),
      (heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) 1 Λ
          (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
        = ENNReal.ofReal (Real.exp (-((heisenbergPotential n J).hamiltonian Λ
            (juxt (Λ : Set (Fin d → ℤ)) ω ζ)))) := by
    intro ζ
    rw [Potential.tailBoltzmannFactor_of_mem _ _ (juxt_mem_slowGrowthTailSet hω ζ),
      Potential.boltzmannFactor]
    congr 2
    ring
  have hfmeas : Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp (-((heisenbergPotential n J).hamiltonian Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) := by
    have hcomp : Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦
        ((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) 1 Λ
          (juxt (Λ : Set (Fin d → ℤ)) ω ζ)).toReal :=
      (hρm.comp Measurable.juxt).ennreal_toReal
    have heq : (fun ζ : ↥Λ → (Fin n → ℝ) ↦
        ((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) 1 Λ
          (juxt (Λ : Set (Fin d → ℤ)) ω ζ)).toReal)
        = fun ζ : ↥Λ → (Fin n → ℝ) ↦
          Real.exp (-((heisenbergPotential n J).hamiltonian Λ
            (juxt (Λ : Set (Fin d → ℤ)) ω ζ))) := by
      funext ζ
      rw [hpt ζ, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [← heq]
    exact hcomp
  rw [heisenbergSpecification_apply_of_mem Λ hω hA]
  exact Specification.toReal_gibbsRatio_eq_div ν Λ ω hρm
    (f := fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp (-((heisenbergPotential n J).hamiltonian Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ)))) hfmeas
    (fun ζ ↦ (Real.exp_pos _).le) hpt hA

/-- The Hamiltonian of Georgii's (20.1) along a fibre of the resampling map is measurable, even
though it is only defined on `Ω_*`: it is `-log` of the tail Boltzmann factor. -/
theorem measurable_hamiltonian_heisenbergPotential_juxt (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ))
    {ω : (Fin d → ℤ) → (Fin n → ℝ)} (hω : ω ∈ slowGrowthTailSet d n) :
    Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦
      (heisenbergPotential n J).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ) := by
  have hρm : Measurable ((heisenbergPotential n J).tailBoltzmannFactor
      (slowGrowthTailSet d n) 1 Λ) :=
    Potential.measurable_tailBoltzmannFactor measurableSet_slowGrowthTailSet
      (isSummableOn_heisenbergPotential heven hJ0 hJ) 1 Λ
  have hcomp : Measurable fun ζ : ↥Λ → (Fin n → ℝ) ↦
      -Real.log (((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) 1 Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ)).toReal) :=
    (Real.measurable_log.comp (hρm.comp Measurable.juxt).ennreal_toReal).neg
  have heq : (fun ζ : ↥Λ → (Fin n → ℝ) ↦
      -Real.log (((heisenbergPotential n J).tailBoltzmannFactor (slowGrowthTailSet d n) 1 Λ
        (juxt (Λ : Set (Fin d → ℤ)) ω ζ)).toReal))
      = fun ζ : ↥Λ → (Fin n → ℝ) ↦
        (heisenbergPotential n J).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ) := by
    funext ζ
    rw [Potential.tailBoltzmannFactor_of_mem _ _ (juxt_mem_slowGrowthTailSet hω ζ),
      Potential.boltzmannFactor, ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.log_exp]
    ring
  rw [← heq]
  exact hcomp

end KernelRatio

/-! ### Georgii, Proposition (4.19) restricted to `Ω_t` -/

section KernelComparison

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **Georgii's `‖(γ_Λ^n f - γ_Λ^Φ f) 1_{Ω_t}‖ → 0`** in the proof of (20.7): "Mimicking the proof
of Proposition (4.19) and using hypothesis (20.3)".

In a fixed volume `Λ`, at every boundary condition `ω ∈ Ω_t` and on every event `A`, the
finite-volume Gibbs kernel of the periodic modification `Φ^n` and the one of `Φ` itself differ by
at most `ε`, as soon as the cube is large enough.  The convergence is uniform in `ω` and in `A`,
which is exactly what the sup-norm in Georgii's statement asserts.

The two energies are compared through `MeasureTheory.abs_expTilt_sub_le` over the block `E^Λ`, with
the Gaussian control `Q(ζ) = ∑_{i ∈ Λ}[1 + |ζ_i|²]`: `|H_Λ^Φ| ≤ c Q` uniformly over `Ω_t`
(`abs_hamiltonian_heisenbergPotential_le_of_exterior_le`), `|H_Λ^{Φ^n} - H_Λ^Φ| ≤ δ_n Q` with the
null sequence `δ_n` of `tendsto_sum_couplingTail`
(`abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le`), and both `∫ e^{(c+2)Q}` and
`∫ e^{-cQ}` are finite and positive by (20.3) (`integrable_exp_blockSum`,
`integral_exp_blockSum_pos`). -/
theorem eventually_abs_heisenbergPeriodicGibbsSpec_sub_heisenbergSpecification_le
    [IsFiniteMeasure ν] [NeZero ν] (hexp : HasExpSqMoments ν)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J)
    (Λ : Finset (Fin d → ℤ)) {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℕ in atTop, ∀ ω ∈ slowGrowthSet d n t,
      ∀ A : Set ((Fin d → ℤ) → (Fin n → ℝ)), MeasurableSet A →
        |(heisenbergPeriodicGibbsSpec n J L ν hJ.summable heven hJ0
              (isSigmaFiniteLambdaAdmissible_heisenbergPeriodicPotential
                (NeZero.ne ν) hexp hJ.summable heven hJ0) Λ ω A).toReal
            - (heisenbergSpecification J ν 1 hexp heven hJ0 hJ Λ ω A).toReal| ≤ ε := by
  classical
  have hν : ν ≠ 0 := NeZero.ne ν
  have hsum : Summable J := hJ.summable
  -- the uniform rate `c` of the limit energy over `Ω_t`
  set c : ℝ := 2 * ((∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j) * (1 + t)) with hc
  have hD0 : ∀ i : Fin d → ℤ, (0 : ℝ) ≤ ∑' j, |J (i - j)| * slowGrowth j := fun i ↦
    tsum_nonneg fun j ↦ mul_nonneg (abs_nonneg _) (slowGrowth_pos j).le
  have hc0 : 0 ≤ c := by
    have h1 : (0 : ℝ) ≤ ∑ i ∈ Λ, ∑' j, |J (i - j)| * slowGrowth j :=
      Finset.sum_nonneg fun i _ ↦ hD0 i
    rw [hc]; nlinarith
  -- the two Gaussian constants
  set Γ : ℝ := ∫ ζ : ↥Λ → (Fin n → ℝ), Real.exp ((c + 2) * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))
    ∂(Measure.pi fun _ : ↥Λ ↦ ν) with hΓ
  set β : ℝ := ∫ ζ : ↥Λ → (Fin n → ℝ), Real.exp (-(c * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i)))
    ∂(Measure.pi fun _ : ↥Λ ↦ ν) with hβdef
  have hΓint : Integrable (fun ζ : ↥Λ → (Fin n → ℝ) ↦
      Real.exp ((c + 2) * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))) (Measure.pi fun _ : ↥Λ ↦ ν) :=
    integrable_exp_blockSum hexp Λ (c + 2)
  have hΓ0 : 0 ≤ Γ := integral_nonneg fun ζ ↦ (Real.exp_pos _).le
  have hβ : 0 < β := by
    have h := integral_exp_blockSum_pos (ν := ν) hν hexp Λ (-c)
    simpa only [neg_mul, hβdef] using h
  -- Georgii's null sequence
  set δ : ℕ → ℝ := fun L ↦ 4 * (1 + t) * ∑ i ∈ Λ, couplingTail J L i with hδdef
  have hδ0 : ∀ L, 0 ≤ δ L := fun L ↦ by
    have h1 : (0 : ℝ) ≤ ∑ i ∈ Λ, couplingTail J L i :=
      Finset.sum_nonneg fun i _ ↦ couplingTail_nonneg J L i
    rw [hδdef]; nlinarith
  have hδlim : Filter.Tendsto δ atTop (𝓝 0) := tendsto_sum_couplingTail hJ Λ (1 + t)
  have hsmall : ∀ η : ℝ, 0 < η → ∀ᶠ L : ℕ in atTop, δ L ≤ η := by
    intro η hη
    filter_upwards [hδlim (Iio_mem_nhds hη)] with L hL
    exact le_of_lt hL
  have h1 : ∀ᶠ L : ℕ in atTop, δ L ≤ 1 := hsmall 1 one_pos
  have h2 : ∀ᶠ L : ℕ in atTop, δ L * Γ ≤ β / 2 := by
    filter_upwards [hsmall (β / (2 * (Γ + 1))) (by positivity)] with L hL
    have hΓ1 : Γ ≤ Γ + 1 := by linarith
    have := mul_le_mul_of_nonneg_right hL hΓ0
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Γ + 1))] at this
    nlinarith [hδ0 L]
  have h3 : ∀ᶠ L : ℕ in atTop, 4 * Γ * δ L / β ≤ ε := by
    filter_upwards [hsmall (ε * β / (4 * (Γ + 1))) (by positivity)] with L hL
    rw [div_le_iff₀ hβ]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (Γ + 1))] at hL
    nlinarith [hδ0 L]
  have h4 : ∀ᶠ L : ℕ in atTop, Λ ⊆ Potential.latticeBox d L :=
    Potential.tendsto_latticeBox_atTop.eventually (eventually_ge_atTop Λ)
  filter_upwards [h1, h2, h3, h4] with L hδ1 hδΓ hεb hΛ
  intro ω hω A hA
  have hpot := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  have hωΩ : ω ∈ slowGrowthTailSet d n := mem_slowGrowthTailSet_iff.2 ⟨t, hω⟩
  -- the exterior spins of a resampled configuration
  have hext : ∀ (ζ : ↥Λ → (Fin n → ℝ)) (j : Fin d → ℤ), j ∉ Λ →
      Real.sqrt (juxt (Λ : Set (Fin d → ℤ)) ω ζ j ⬝ᵥ juxt (Λ : Set (Fin d → ℤ)) ω ζ j)
        ≤ t * slowGrowth j := by
    intro ζ j hj
    rw [juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hj) ζ]
    have hb : ω j ⬝ᵥ ω j ≤ (t * slowGrowth j) ^ 2 := by have := hω j; nlinarith
    calc Real.sqrt (ω j ⬝ᵥ ω j) ≤ Real.sqrt ((t * slowGrowth j) ^ 2) := Real.sqrt_le_sqrt hb
      _ = t * slowGrowth j := Real.sqrt_sq (mul_nonneg ht (slowGrowth_pos j).le)
  -- the two hypotheses of the comparison
  have hH₂le : ∀ ζ : ↥Λ → (Fin n → ℝ),
      |(heisenbergPotential n J).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ)|
        ≤ c * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
    intro ζ
    have hx := abs_hamiltonian_heisenbergPotential_le_of_exterior_le heven hJ0 hJ Λ ht
      (juxt_mem_slowGrowthTailSet hωΩ ζ) (hext ζ)
    rwa [sum_one_add_dotProduct_juxt, ← hc] at hx
  have hdiffle : ∀ ζ : ↥Λ → (Fin n → ℝ),
      |(heisenbergPeriodicPotential n J L).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
          - (heisenbergPotential n J).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ)|
        ≤ δ L * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
    intro ζ
    have hx := abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le heven hJ0 hJ
      hΛ ht (juxt_mem_slowGrowthTailSet hωΩ ζ) (hext ζ)
    rw [sum_one_add_dotProduct_juxt] at hx
    have hδL : δ L = 4 * (1 + t) * ∑ i ∈ Λ, couplingTail J L i := rfl
    rw [hδL]
    exact hx
  -- the two kernels as ratios and the comparison
  rw [toReal_heisenbergPeriodicGibbsSpec_apply hsum heven hJ0 _ Λ ω hA,
    toReal_heisenbergSpecification_apply Λ hωΩ hA]
  refine le_trans (abs_expTilt_sub_le
    (H₁ := fun ζ : ↥Λ → (Fin n → ℝ) ↦
      (heisenbergPeriodicPotential n J L).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ))
    (H₂ := fun ζ : ↥Λ → (Fin n → ℝ) ↦
      (heisenbergPotential n J).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ))
    (Q := fun ζ : ↥Λ → (Fin n → ℝ) ↦ ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))
    ((Potential.measurable_hamiltonian (Φ := heisenbergPeriodicPotential n J L) Λ).comp
      Measurable.juxt)
    (measurable_hamiltonian_heisenbergPotential_juxt heven hJ0 hJ Λ hωΩ)
    (Finset.measurable_sum Finset.univ fun i _ ↦ measurable_const.add
      ((measurable_pi_apply i).dotProduct (measurable_pi_apply i)))
    hc0 (hδ0 L) hδ1
    (fun ζ ↦ Finset.sum_nonneg fun i _ ↦ by
      have := dotProduct_self_nonneg (ζ i); linarith)
    hH₂le hdiffle hΓint hβ hδΓ (Measurable.juxt hA)) ?_
  exact hεb

end KernelComparison

/-! ### `γ_Λ^n 1_A` is a local function -/

section Locality

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **Georgii's "`γ_Λ^m f ∈ 𝓛`"** in the proof of (20.7).  The periodic modification `Φ^m` has
finite range, so the finite-volume Gibbs kernel `ω ↦ γ_Λ^m(A|ω)` of a `𝓕_Δ`-event `A` depends only
on the spins in `Δ` and in the (finite) union of the interaction supports meeting `Λ`. -/
theorem dependsOn_toReal_heisenbergPeriodicGibbsSpec_apply
    [IsFiniteMeasure ν] [NeZero ν] {L : ℕ} (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1))
    (Λ Δ : Finset (Fin d → ℤ)) {A : Set ((Fin d → ℤ) → (Fin n → ℝ))}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
      (Δ : Set (Fin d → ℤ))] A) :
    DependsOn (fun ω ↦ (heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm Λ ω A).toReal)
      ((Δ ∪ (Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ).biUnion id
        : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)) := by
  classical
  have hpot := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  intro ω ω' h
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hagree : ∀ (ζ : ↥Λ → (Fin n → ℝ)) (i : Fin d → ℤ),
      i ∈ Δ ∪ (Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ).biUnion id →
      juxt (Λ : Set (Fin d → ℤ)) ω ζ i = juxt (Λ : Set (Fin d → ℤ)) ω' ζ i := by
    intro ζ i hi
    by_cases hiΛ : i ∈ Λ
    · rw [juxt_apply_of_mem (Finset.mem_coe.mpr hiΛ) ζ,
        juxt_apply_of_mem (Finset.mem_coe.mpr hiΛ) ζ]
    · rw [juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hiΛ) ζ,
        juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hiΛ) ζ]
      exact h i (Finset.mem_coe.mpr hi)
  have hpre : juxt (Λ : Set (Fin d → ℤ)) ω ⁻¹' A = juxt (Λ : Set (Fin d → ℤ)) ω' ⁻¹' A := by
    ext ζ
    exact mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦
      hagree ζ i (Finset.mem_union_left _ (Finset.mem_coe.1 hi))
  have hH : ∀ ζ : ↥Λ → (Fin n → ℝ),
      (heisenbergPeriodicPotential n J L).hamiltonian Λ (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
        = (heisenbergPeriodicPotential n J L).hamiltonian Λ
            (juxt (Λ : Set (Fin d → ℤ)) ω' ζ) := by
    intro ζ
    rw [Potential.hamiltonian_eq_interactingHamiltonian,
      Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian,
      Potential.interactingHamiltonian]
    refine Finset.sum_congr rfl fun B hB ↦ Potential.IsPotential.eq_of_eqOn fun x hx ↦ ?_
    exact hagree ζ x (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨B, hB, hx⟩))
  change (heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm Λ ω A).toReal
      = (heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm Λ ω' A).toReal
  rw [toReal_heisenbergPeriodicGibbsSpec_apply hsum heven hJ0 hadm Λ ω hAm,
    toReal_heisenbergPeriodicGibbsSpec_apply hsum heven hJ0 hadm Λ ω' hAm, hpre]
  simp only [hH]

/-- The finite-volume Gibbs kernel of the periodic modification, evaluated at a local event, is a
bounded local observable — the form in which Georgii's `γ_Λ^m f ∈ 𝓛` enters the limit. -/
theorem measurable_cylinderEvents_toReal_heisenbergPeriodicGibbsSpec_apply
    [IsFiniteMeasure ν] [NeZero ν] {L : ℕ} (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0)
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1))
    (Λ Δ : Finset (Fin d → ℤ)) {A : Set ((Fin d → ℤ) → (Fin n → ℝ))}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
      (Δ : Set (Fin d → ℤ))] A) :
    Measurable[cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
        ((Δ ∪ (Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ).biUnion id
          : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))]
      fun ω ↦ (heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm Λ ω A).toReal := by
  classical
  have hAm : MeasurableSet A := cylinderEvents_le_pi _ hA
  refine measurable_cylinderEvents_iff_dependsOn.2 ⟨?_, ?_⟩
  · exact ((((heisenbergPeriodicGibbsSpec n J L ν hsum heven hJ0 hadm) Λ).measurable_coe
      hAm).mono cylinderEvents_le_pi le_rfl).ennreal_toReal
  · exact dependsOn_toReal_heisenbergPeriodicGibbsSpec_apply hsum heven hJ0 hadm Λ Δ hA

end Locality

/-! ### Georgii, Proposition (20.7), second half -/

section Inclusion

variable {d n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- A bounded observable which is small on `B` has a small integral, up to the mass of `Bᶜ`.  This
is Georgii's splitting `|μ(γ_Λ^n f - γ_Λ^m f)| ≤ ε + μ(Ω_t^c)` in the proof of (20.7). -/
private theorem abs_integral_le_of_le_on {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    [IsProbabilityMeasure ρ] {g : X → ℝ} (hg : Measurable g) {B : Set X} (hB : MeasurableSet B)
    {a : ℝ} (ha : 0 ≤ a) (hgB : ∀ x ∈ B, |g x| ≤ a) (hg1 : ∀ x, |g x| ≤ 1) :
    |∫ x, g x ∂ρ| ≤ a + (ρ Bᶜ).toReal := by
  have hgint : Integrable g ρ :=
    Integrable.of_bound hg.aestronglyMeasurable 1
      (.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hg1 x)
  have hindint : Integrable (Bᶜ.indicator fun _ ↦ (1 : ℝ)) ρ :=
    (integrable_const (1 : ℝ)).indicator hB.compl
  have hle : ∀ x, |g x| ≤ a + Bᶜ.indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      simpa using hgB x hx
    · rw [Set.indicator_of_mem (by simpa using hx)]
      linarith [hg1 x]
  calc |∫ x, g x ∂ρ| ≤ ∫ x, |g x| ∂ρ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (a + Bᶜ.indicator (fun _ ↦ (1 : ℝ)) x) ∂ρ :=
        integral_mono hgint.abs ((integrable_const a).add hindint) hle
    _ = a + (ρ Bᶜ).toReal := by
        rw [integral_add (integrable_const a) hindint, integral_const,
          integral_indicator_const (1 : ℝ) hB.compl]
        simp [measureReal_def]

/-- **Georgii, Proposition (20.7), second half: `𝒢₀(Φ) ⊆ 𝒢(Φ)`.**  Every cluster point of the
fields `μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0` is a Gibbs measure for the Gibbsian specification (20.5).

Georgii's proof, verbatim.  Fix a volume `Λ` and a local event `A`, and let `ε > 0`.  Choose a
level `t` with `μ(Ω_t) ≥ 1 - ε` and `μ_n(Ω_t) ≥ 1 - ε` for all `n` (Lemma (20.6)(iii)); choose a
cube `m` so large that `‖(γ_Λ^n 1_A - γ_Λ^Φ 1_A) 1_{Ω_t}‖ ≤ ε` for all `n ≥ m`
(`eventually_abs_heisenbergPeriodicGibbsSpec_sub_heisenbergSpecification_le`, Proposition (4.19)
restricted to `Ω_t`).  Then `|μ_n(γ_Λ^n 1_A) - μ_n(γ_Λ^m 1_A)| ≤ 3ε` and
`|μ(γ_Λ^Φ 1_A) - μ(γ_Λ^m 1_A)| ≤ 2ε`, while `μ_n(γ_Λ^n 1_A) = μ_n(A)` by the DLR equation of `γ^n`
and `μ_{n_k}(γ_Λ^m 1_A) → μ(γ_Λ^m 1_A)` because `γ_Λ^m 1_A` is a bounded local function
(`measurable_cylinderEvents_toReal_heisenbergPeriodicGibbsSpec_apply`).  Hence
`|μ(γ_Λ^Φ 1_A) - μ(A)| ≤ 5ε`, and `ε` was arbitrary. -/
theorem heisenbergGZero_subset_heisenbergGibbsMeasures [IsFiniteMeasure ν] [NeZero ν]
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hJ : IsSlowlySummable J) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    {μ : ProbabilityMeasure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))} (hμ : μ ∈ heisenbergGZero J ν) :
    (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
      ∈ heisenbergGibbsMeasures J ν 1 hexp heven hJ0 hJ := by
  classical
  have hν : ν ≠ 0 := NeZero.ne ν
  have hμprob : IsProbabilityMeasure (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := μ.2
  obtain ⟨μs, hμsval, hcp⟩ := id hμ
  -- Georgii (4.15): a convergent subsequence of the fields
  obtain ⟨φ, hφmono, hφconv⟩ := exists_strictMono_tendsto_of_mapClusterPt
    (locallyEquicontinuous_heisenbergPeriodicField hν hexp heven hJ hnd hμsval) hcp
  obtain ⟨γn, hγn⟩ : ∃ γn : ℕ → Specification (Fin (d + 1) → ℤ) (Fin n → ℝ),
      ∀ L, γn L = heisenbergPeriodicGibbsSpec n J L ν hJ.summable heven hJ0
        (isSigmaFiniteLambdaAdmissible_heisenbergPeriodicPotential (NeZero.ne ν) hexp
          hJ.summable heven hJ0) := ⟨_, fun L ↦ rfl⟩
  set γΦ : Specification (Fin (d + 1) → ℤ) (Fin n → ℝ) :=
    heisenbergSpecification J ν 1 hexp heven hJ0 hJ with hγΦ
  -- Lemma (20.6)(iii) for the fields and for the cluster point, with a single constant
  obtain ⟨b₁, hb₁0, hb₁⟩ := exists_forall_heisenbergPeriodicField_zero_tail_le (d := d) (n := n)
    hν hexp hJ.summable heven hnd (a := ((d : ℝ) + 1) + 1 + 1) (by positivity)
  obtain ⟨b₂, hb₂0, hb₂⟩ := exists_forall_tail_le_of_mem_heisenbergGZero (d := d) (n := n)
    hν hexp hJ.summable heven hnd (a := ((d : ℝ) + 1) + 1 + 1) (by positivity)
  set C : ℝ := ∑' i : Fin (d + 1) → ℤ, (max (Real.exp 1) ‖i‖) ^ (-(((d + 1 : ℕ) : ℝ) + 1))
    with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun i ↦
    Real.rpow_nonneg (le_trans (Real.exp_pos 1).le (le_max_left _ _)) _
  set b : ℝ := max b₁ b₂ with hb
  have hb0 : 0 < b := lt_of_lt_of_le hb₁0 (le_max_left _ _)
  have hcast : ((d : ℝ) + 1) + 1 + 1 = (((d + 1 : ℕ) : ℝ) + 1) + 1 := by push_cast; ring
  have hmassL : ∀ (t : ℝ), 1 ≤ t → ∀ L : ℕ,
      (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) (slowGrowthSet (d + 1) n t)ᶜ
        ≤ ENNReal.ofReal (b * C * Real.exp (-(1 * t ^ 2))) := by
    intro t ht L
    rw [hμsval L]
    refine (measure_compl_slowGrowthSet_le (a := 1) (b := b₁) (c := ((d : ℝ) + 1) + 1 + 1)
      one_pos hb₁0.le (by push_cast; linarith) (fun i r ↦ hb₁ L i r) ht).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : b₁ ≤ b := le_max_left _ _
    have h2 : (0 : ℝ) ≤ C * Real.exp (-(1 * t ^ 2)) := by positivity
    nlinarith
  have hmassμ : ∀ (t : ℝ), 1 ≤ t →
      (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) (slowGrowthSet (d + 1) n t)ᶜ
        ≤ ENNReal.ofReal (b * C * Real.exp (-(1 * t ^ 2))) := by
    intro t ht
    refine (measure_compl_slowGrowthSet_le (a := 1) (b := b₂) (c := ((d : ℝ) + 1) + 1 + 1)
      one_pos hb₂0.le (by push_cast; linarith) (fun i r ↦ hb₂ μ hμ i r) ht).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : b₂ ≤ b := le_max_right _ _
    have h2 : (0 : ℝ) ≤ C * Real.exp (-(1 * t ^ 2)) := by positivity
    nlinarith
  -- the Gibbs property, event by event
  refine ⟨hμprob, ?_⟩
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  refine separatesOn_localEvents (Specification.isProbabilityMeasure_bind γΦ Λ _) hμprob
    fun A hA ↦ ?_
  obtain ⟨Δ, hAΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  -- the kernel values, as bounded observables
  set g : ℕ → ((Fin (d + 1) → ℤ) → (Fin n → ℝ)) → ℝ := fun L ω ↦ (γn L Λ ω A).toReal with hg
  set gΦ : ((Fin (d + 1) → ℤ) → (Fin n → ℝ)) → ℝ := fun ω ↦ (γΦ Λ ω A).toReal with hgΦ
  have hgmeas : ∀ L, Measurable (g L) := fun L ↦
    (Specification.measurable_apply_kernel (γn L) Λ hAm).ennreal_toReal
  have hgΦmeas : Measurable gΦ :=
    (Specification.measurable_apply_kernel γΦ Λ hAm).ennreal_toReal
  have hgnn : ∀ L ω, 0 ≤ g L ω := fun L ω ↦ ENNReal.toReal_nonneg
  have hgΦnn : ∀ ω, 0 ≤ gΦ ω := fun ω ↦ ENNReal.toReal_nonneg
  have hgle1 : ∀ L ω, g L ω ≤ 1 := fun L ω ↦
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hgΦle1 : ∀ ω, gΦ ω ≤ 1 := fun ω ↦
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have habsg : ∀ L ω, |g L ω| ≤ 1 := fun L ω ↦ by
    rw [abs_of_nonneg (hgnn L ω)]; exact hgle1 L ω
  have habsgΦ : ∀ ω, |gΦ ω| ≤ 1 := fun ω ↦ by
    rw [abs_of_nonneg (hgΦnn ω)]; exact hgΦle1 ω
  have hgint : ∀ L, Integrable (g L) (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := fun L ↦
    Integrable.of_bound (hgmeas L).aestronglyMeasurable 1
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact habsg L x)
  have hgintL : ∀ L K : ℕ,
      Integrable (g L) (μs K : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := fun L K ↦
    Integrable.of_bound (hgmeas L).aestronglyMeasurable 1
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact habsg L x)
  have hgΦint : Integrable gΦ (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) :=
    Integrable.of_bound hgΦmeas.aestronglyMeasurable 1
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact habsgΦ x)
  -- the two sides, as real numbers
  have hbindReal : ∀ (γ : Specification (Fin (d + 1) → ℤ) (Fin n → ℝ))
      (ρ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))),
      ((ρ.bind (γ Λ)) A).toReal = ∫ ω, (γ Λ ω A).toReal ∂ρ := by
    intro γ ρ
    rw [Measure.bind_apply hAm (Specification.measurable_kernel_toMeasure γ Λ).aemeasurable,
      integral_toReal (Specification.measurable_apply_kernel γ Λ hAm).aemeasurable
        (.of_forall fun ω ↦ lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)]
  have hbp : IsProbabilityMeasure
      (((μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))).bind (γΦ Λ)) :=
    Specification.isProbabilityMeasure_bind γΦ Λ _
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  rw [hbindReal γΦ (μ : Measure _)]
  set X : ℝ := ∫ ω, gΦ ω ∂(μ : Measure _) with hX
  set Y : ℝ := ((μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) A).toReal with hY
  suffices hmain : ∀ ε : ℝ, 0 < ε → |X - Y| ≤ 5 * ε by
    have h0 : |X - Y| ≤ 0 := le_of_forall_pos_le_add fun ε hε ↦ by
      have := hmain (ε / 5) (by positivity); linarith
    have hzero : X - Y = 0 := abs_eq_zero.1 (le_antisymm h0 (abs_nonneg _))
    linarith
  intro ε hε
  -- Georgii's level `t`
  obtain ⟨t, ht1, htε⟩ : ∃ t : ℕ, 1 ≤ t ∧ b * C * Real.exp (-((t : ℝ))) ≤ ε := by
    have hlim : Filter.Tendsto (fun t : ℕ ↦ b * C * Real.exp (-((t : ℝ)))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (b * C)
      simpa using this
    obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 (hlim (Iio_mem_nhds hε))
    exact ⟨max 1 t₀, le_max_left _ _, le_of_lt (ht₀ _ (le_max_right _ _))⟩
  have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have ht0' : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hexpmono : Real.exp (-(1 * (t : ℝ) ^ 2)) ≤ Real.exp (-((t : ℝ))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hbC0 : (0 : ℝ) ≤ b * C := mul_nonneg hb0.le hC0
  have htailL : ∀ L : ℕ,
      ((μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
        (slowGrowthSet (d + 1) n (t : ℝ))ᶜ).toReal ≤ ε := by
    intro L
    refine ENNReal.toReal_le_of_le_ofReal hε.le ((hmassL (t : ℝ) ht1' L).trans
      (ENNReal.ofReal_le_ofReal ?_))
    calc b * C * Real.exp (-(1 * (t : ℝ) ^ 2)) ≤ b * C * Real.exp (-((t : ℝ))) :=
          mul_le_mul_of_nonneg_left hexpmono hbC0
      _ ≤ ε := htε
  have htailμ : ((μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
      (slowGrowthSet (d + 1) n (t : ℝ))ᶜ).toReal ≤ ε := by
    refine ENNReal.toReal_le_of_le_ofReal hε.le ((hmassμ (t : ℝ) ht1').trans
      (ENNReal.ofReal_le_ofReal ?_))
    calc b * C * Real.exp (-(1 * (t : ℝ) ^ 2)) ≤ b * C * Real.exp (-((t : ℝ))) :=
          mul_le_mul_of_nonneg_left hexpmono hbC0
      _ ≤ ε := htε
  -- Georgii's cube `m`
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1
    ((eventually_abs_heisenbergPeriodicGibbsSpec_sub_heisenbergSpecification_le (d := d + 1)
        hexp heven hJ0 hJ Λ ht0' hε).and
      (Potential.tendsto_latticeBox_atTop.eventually (eventually_ge_atTop Λ)))
  have hcompare : ∀ L, m ≤ L → ∀ ω ∈ slowGrowthSet (d + 1) n (t : ℝ),
      |g L ω - gΦ ω| ≤ ε := by
    intro L hL ω hω
    have h := (hm L hL).1 ω hω A hAm
    change |(γn L Λ ω A).toReal - (γΦ Λ ω A).toReal| ≤ ε
    rw [hγn L, hγΦ]
    exact h
  have hcompare' : ∀ L, m ≤ L → ∀ ω ∈ slowGrowthSet (d + 1) n (t : ℝ),
      |gΦ ω - g L ω| ≤ ε := by
    intro L hL ω hω
    rw [abs_sub_comm]
    exact hcompare L hL ω hω
  have hcompare2 : ∀ L, m ≤ L → ∀ ω ∈ slowGrowthSet (d + 1) n (t : ℝ),
      |g m ω - g L ω| ≤ 2 * ε := by
    intro L hL ω hω
    have h1 := hcompare m le_rfl ω hω
    have h2 := hcompare' L hL ω hω
    have h3 : |g m ω - g L ω| ≤ |g m ω - gΦ ω| + |gΦ ω - g L ω| := by
      have h := abs_add_le (g m ω - gΦ ω) (gΦ ω - g L ω)
      rwa [sub_add_sub_cancel] at h
    linarith
  -- the DLR equation of `γ^n`
  have hDLR : ∀ L : ℕ, Λ ⊆ Potential.latticeBox (d + 1) L →
      ∫ ω, g L ω ∂(μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
        = ((μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) A).toReal := by
    intro L hΛ
    have hfield : (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
        = γn L (Potential.latticeBox (d + 1) L) 0 := by
      rw [hμsval L, hγn L,
        heisenbergPeriodicGibbsSpec_latticeBox hJ.summable heven hJ0 _ 0]
      rfl
    have hbind : (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))).bind (γn L Λ)
        = (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := by
      conv_lhs => rw [hfield]
      rw [Specification.bind (γ := γn L) hΛ 0, ← hfield]
    rw [← hbindReal (γn L) (μs L : Measure _), hbind]
  -- the local approximant `γ_Λ^m 1_A` and its limit
  set V : Finset (Fin (d + 1) → ℤ) :=
    Δ ∪ (Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J m) Λ).biUnion id
    with hV
  have hgloc : Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ (Fin n → ℝ))
      (V : Set (Fin (d + 1) → ℤ))] (g m) := by
    change Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ (Fin n → ℝ))
      (V : Set (Fin (d + 1) → ℤ))] fun ω ↦ (γn m Λ ω A).toReal
    rw [hγn m]
    exact measurable_cylinderEvents_toReal_heisenbergPeriodicGibbsSpec_apply
      hJ.summable heven hJ0 _ Λ Δ hAΔ
  have hconvset : ∀ B : Set ((Fin (d + 1) → ℤ) → (Fin n → ℝ)),
      MeasurableSet[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ (Fin n → ℝ))
        (V : Set (Fin (d + 1) → ℤ))] B →
      Filter.Tendsto (fun k ↦ (μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) B) atTop
        (𝓝 ((μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) B)) := by
    intro B hB
    exact tendsto_withLocalConvergence_iff.1 hφconv B (mem_localEvents_of_cylinderEvents V hB)
  have hconvint : Filter.Tendsto
      (fun k ↦ ∫ ω, g m ω ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))) atTop
      (𝓝 (∫ ω, g m ω ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))) :=
    tendsto_integral_of_tendsto_setwise cylinderEvents_le_pi (fun k ↦ (μs (φ k)).2) hμprob
      hgloc (C := 1) (habsg m) hconvset
  have hconvA : Filter.Tendsto
      (fun k ↦ ((μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) A).toReal) atTop
      (𝓝 Y) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_withLocalConvergence_iff.1 hφconv A hA)
  -- assemble
  have hfin : Filter.Tendsto (fun k ↦ 5 * ε
      + |(∫ ω, g m ω ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))
          - ∫ ω, g m ω ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))|
      + |((μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) A).toReal - Y|)
      atTop (𝓝 (5 * ε)) := by
    have h1 : Filter.Tendsto (fun k ↦ |(∫ ω, g m ω ∂(μ : Measure _))
        - ∫ ω, g m ω ∂(μs (φ k) : Measure _)|) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∫ ω, g m ω ∂(μ : Measure _))
        (f := atTop (α := ℕ))).sub hconvint
      simpa using this.abs
    have h2 : Filter.Tendsto (fun k ↦ |((μs (φ k) : Measure _) A).toReal - Y|) atTop (𝓝 0) := by
      have := hconvA.sub (tendsto_const_nhds (x := Y) (f := atTop (α := ℕ)))
      simpa using this.abs
    simpa using (tendsto_const_nhds.add h1).add h2
  refine ge_of_tendsto hfin ?_
  filter_upwards [eventually_ge_atTop m] with k hk
  have hφk : m ≤ φ k := le_trans hk (hφmono.le_apply)
  -- (a) `|X - μ(γ_Λ^m 1_A)| ≤ 2ε`
  have hA1 : |X - ∫ ω, g m ω ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))| ≤ 2 * ε := by
    have hsub : X - ∫ ω, g m ω ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
        = ∫ ω, (gΦ ω - g m ω) ∂(μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := by
      rw [integral_sub hgΦint (hgint m)]
    have hpt1 : ∀ ω ∈ slowGrowthSet (d + 1) n (t : ℝ), |gΦ ω - g m ω| ≤ ε :=
      fun ω hω ↦ hcompare' m le_rfl ω hω
    have hpt2 : ∀ ω, |gΦ ω - g m ω| ≤ 1 := fun ω ↦ by
      rw [abs_le]
      exact ⟨by linarith [hgnn m ω, hgle1 m ω, hgΦnn ω, hgΦle1 ω],
        by linarith [hgnn m ω, hgle1 m ω, hgΦnn ω, hgΦle1 ω]⟩
    rw [hsub]
    refine le_trans (abs_integral_le_of_le_on (g := fun ω ↦ gΦ ω - g m ω)
      (hgΦmeas.sub (hgmeas m)) (measurableSet_slowGrowthSet (t : ℝ)) hε.le hpt1 hpt2) ?_
    linarith [htailμ]
  -- (b) `|μ_n(γ_Λ^m 1_A) - μ_n(A)| ≤ 3ε`
  have hA2 : |(∫ ω, g m ω ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))
      - ((μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) A).toReal| ≤ 3 * ε := by
    rw [← hDLR (φ k) (hm (φ k) hφk).2]
    have hsub : (∫ ω, g m ω ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))))
        - ∫ ω, g (φ k) ω ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
        = ∫ ω, (g m ω - g (φ k) ω)
            ∂(μs (φ k) : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) := by
      rw [integral_sub (hgintL m (φ k)) (hgintL (φ k) (φ k))]
    have hpt1 : ∀ ω ∈ slowGrowthSet (d + 1) n (t : ℝ), |g m ω - g (φ k) ω| ≤ 2 * ε :=
      fun ω hω ↦ hcompare2 (φ k) hφk ω hω
    have hpt2 : ∀ ω, |g m ω - g (φ k) ω| ≤ 1 := fun ω ↦ by
      rw [abs_le]
      exact ⟨by linarith [hgnn m ω, hgle1 m ω, hgnn (φ k) ω, hgle1 (φ k) ω],
        by linarith [hgnn m ω, hgle1 m ω, hgnn (φ k) ω, hgle1 (φ k) ω]⟩
    rw [hsub]
    refine le_trans (abs_integral_le_of_le_on (g := fun ω ↦ g m ω - g (φ k) ω)
      ((hgmeas m).sub (hgmeas (φ k))) (measurableSet_slowGrowthSet (t : ℝ)) (by positivity)
      hpt1 hpt2) ?_
    linarith [htailL (φ k)]
  -- the triangle inequality
  have htri : |X - Y| ≤ |X - ∫ ω, g m ω ∂(μ : Measure _)|
      + |(∫ ω, g m ω ∂(μ : Measure _)) - ∫ ω, g m ω ∂(μs (φ k) : Measure _)|
      + |(∫ ω, g m ω ∂(μs (φ k) : Measure _)) - ((μs (φ k) : Measure _) A).toReal|
      + |((μs (φ k) : Measure _) A).toReal - Y| := by
    have := abs_sub (X - ∫ ω, g m ω ∂(μ : Measure _))
      (Y - ∫ ω, g m ω ∂(μ : Measure _))
    calc |X - Y| ≤ |X - ∫ ω, g m ω ∂(μ : Measure _)|
          + |(∫ ω, g m ω ∂(μ : Measure _)) - Y| := by
          have h := abs_add_le (X - ∫ ω, g m ω ∂(μ : Measure _))
            ((∫ ω, g m ω ∂(μ : Measure _)) - Y)
          simpa using h
      _ ≤ |X - ∫ ω, g m ω ∂(μ : Measure _)|
          + (|(∫ ω, g m ω ∂(μ : Measure _)) - ∫ ω, g m ω ∂(μs (φ k) : Measure _)|
            + |(∫ ω, g m ω ∂(μs (φ k) : Measure _)) - Y|) := by
          have h := abs_add_le ((∫ ω, g m ω ∂(μ : Measure _))
              - ∫ ω, g m ω ∂(μs (φ k) : Measure _))
            ((∫ ω, g m ω ∂(μs (φ k) : Measure _)) - Y)
          simp only [sub_add_sub_cancel] at h
          linarith
      _ ≤ _ := by
          have h := abs_add_le ((∫ ω, g m ω ∂(μs (φ k) : Measure _))
              - ((μs (φ k) : Measure _) A).toReal)
            (((μs (φ k) : Measure _) A).toReal - Y)
          simp only [sub_add_sub_cancel] at h
          linarith
  linarith [hA1, hA2, htri]

/-- **Georgii, Proposition (20.7)**: `∅ ≠ 𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`.

Under (20.3), (20.4) and the reflection positivity of `J` (Definition (17.27)), the set of cluster
points of the Gibbs distributions with periodic boundary condition is non-empty
(`heisenbergGZero_nonempty`), and every one of them is a shift-invariant
(`measurePreserving_shift_of_mem_heisenbergGZero`) Gibbs measure for the Gibbsian specification
(20.5). -/
theorem heisenbergGZero_nonempty_and_subset [IsFiniteMeasure ν] [NeZero ν]
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0)
    (hJ : IsSlowlySummable J) (hnd : ∀ k, IsNonnegDefiniteAt k J) :
    (heisenbergGZero J ν).Nonempty ∧
      ∀ μ ∈ heisenbergGZero J ν,
        (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
            ∈ heisenbergGibbsMeasures J ν 1 hexp heven hJ0 hJ ∧
          ∀ a : Fin (d + 1) → ℤ, MeasurePreserving (shift (Fin n → ℝ) a).toFun
            (μ : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))) μ :=
  ⟨heisenbergGZero_nonempty (NeZero.ne ν) hexp heven hJ hnd,
    fun _μ hμ ↦ ⟨heisenbergGZero_subset_heisenbergGibbsMeasures hexp heven hJ0 hJ hnd hμ,
      fun a ↦ measurePreserving_shift_of_mem_heisenbergGZero hμ a⟩⟩

end Inclusion

end MeasureTheory.GibbsMeasure

end

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.PeriodicGibbsLimits

/-!
# Georgii Proposition (4.19) for a `C`-potential

Georgii's Proposition (4.19) — uniform convergence of the Gibbsian specifications of potentials
whose Hamiltonians converge uniformly in each volume — is
`Potential.tendsto_dist_action_gibbsSpecification` of
`GibbsMeasure/Potential/UniformConvergence.lean`, but only for *absolutely summable* potentials:
its proof normalises the Boltzmann density by the uniform bound `Φ.hamiltonianBound Λ`, which a
`C`-potential with `‖Φ_C‖ = ∞` does not have.  Condition (iv) of Georgii (17.18) allows exactly
that, so §19.2 needs the estimate for the `σ`-finite-admissible Gibbsian specification instead.

This file supplies it.  The route avoids the uniform bound entirely: the *ratio* of two Boltzmann
densities is bounded, hence the two Gibbs kernels dominate each other,

`γ^Ψ_Λ(A|η) ≤ e^{2|β| D} γ^Φ_Λ(A|η)` whenever `|H^Ψ_Λ - H^Φ_Λ| ≤ D`,

and mutually dominating probability measures integrate a bounded observable to within
`2‖f‖(e^{2|β| D} - 1)` of each other.

## Main results

* `Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_abs_hamiltonian_sub_le` — the
  two-sided kernel domination.  Its home is
  `GibbsMeasure/Potential/KernelDomination.lean`, next to
  `Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le`.
* `MeasureTheory.abs_integral_sub_integral_le_of_le_smul` — mutually dominating probability
  measures integrate a bounded function to within `2 nf (c - 1)`.  Its home is
  `Mathlib/MeasureTheory/Integral/…`, next to `MeasureTheory.integral_mono_measure`.
* `Potential.dist_action_gibbsSpecificationOfSigmaFiniteAdmissible_le` and
  `Potential.tendsto_dist_action_gibbsSpecificationOfSigmaFiniteAdmissible` — **Georgii (4.19)**
  for a `σ`-finite-admissible potential.  Their home is
  `GibbsMeasure/Potential/UniformConvergence.lean`.
* `MeasureTheory.GibbsMeasure.abs_hamiltonian_cubePotential_sub_le` — for two `C`-potentials the
  Hamiltonian in `Λ` differs by at most `|cubeInteractingSet Λ| ‖Ψ_C - Φ_C‖`, because a
  `C`-potential has finite range and only the cubes meeting `Λ` contribute.
* `MeasureTheory.GibbsMeasure.tendsto_dist_action_cubeGibbsSpec` — **Georgii (4.19) for
  `C`-potentials**: `‖Φ^i_C - Φ_C‖ → 0` implies `γ^{Φ^i} → γ^Φ` uniformly on local functions,
  which is verbatim the hypothesis `hunif` of
  `MeasureTheory.GibbsMeasure.mem_GP_of_mapClusterPt` (Georgii (4.17)).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Two mutually dominating probability measures -/

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Mutually dominating probability measures integrate a bounded function to within
`2 nf (c - 1)` of each other.**  Shifting `f` by `nf` makes it non-negative and bounded by
`2 nf`; a non-negative integrand is compared through `μ ≤ c • ρ`, and the shift cancels because
both measures are probability measures. -/
theorem abs_integral_sub_integral_le_of_le_smul {μ ρ : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ρ] {c : ℝ≥0∞} (hctop : c ≠ ∞) (hμρ : μ ≤ c • ρ) (hρμ : ρ ≤ c • μ)
    {f : Ω → ℝ} (hf : Measurable f) {nf : ℝ} (hnf : ∀ x, |f x| ≤ nf) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ρ| ≤ 2 * nf * (c.toReal - 1) := by
  have hΩ : Nonempty Ω := μ.nonempty_of_neZero
  have hnf0 : 0 ≤ nf := le_trans (abs_nonneg _) (hnf (Classical.arbitrary Ω))
  have hc1 : 1 ≤ c := by
    have h := Measure.le_iff'.1 hμρ Set.univ
    rwa [measure_univ, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at h
  have hc1R : 1 ≤ c.toReal := by
    have := ENNReal.toReal_mono hctop hc1
    simpa using this
  set g : Ω → ℝ := fun x ↦ f x + nf with hgdef
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ by
    have := abs_le.1 (hnf x); simp only [hgdef]; linarith [this.1]
  have hg2 : ∀ x, g x ≤ 2 * nf := fun x ↦ by
    have := abs_le.1 (hnf x); simp only [hgdef]; linarith [this.2]
  have hgm : Measurable g := hf.add_const nf
  have hfint : ∀ (m : Measure Ω), IsFiniteMeasure m → Integrable f m := fun m _ ↦
    Integrable.mono' (integrable_const nf) hf.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hnf x)
  have hgeq : ∀ (m : Measure Ω) [IsProbabilityMeasure m], ∫ x, g x ∂m = (∫ x, f x ∂m) + nf := by
    intro m _
    rw [hgdef, integral_add (hfint m inferInstance) (integrable_const nf), integral_const,
      measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  have hglint : ∀ (m : Measure Ω) [IsProbabilityMeasure m],
      ∫⁻ x, ENNReal.ofReal (g x) ∂m ≠ ∞ := by
    intro m _
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 * nf)) ENNReal.ofReal_ne_top ?_
    calc ∫⁻ x, ENNReal.ofReal (g x) ∂m ≤ ∫⁻ _, ENNReal.ofReal (2 * nf) ∂m :=
          lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hg2 x)
      _ = ENNReal.ofReal (2 * nf) := by rw [lintegral_const, measure_univ, mul_one]
  have hgtoReal : ∀ (m : Measure Ω) [IsProbabilityMeasure m],
      ∫ x, g x ∂m = (∫⁻ x, ENNReal.ofReal (g x) ∂m).toReal := by
    intro m _
    exact integral_eq_lintegral_of_nonneg_ae (.of_forall hg0) hgm.aestronglyMeasurable
  have hkey : ∀ (m m' : Measure Ω) (_ : IsProbabilityMeasure m) (_ : IsProbabilityMeasure m'),
      m ≤ c • m' → ∫ x, g x ∂m ≤ c.toReal * ∫ x, g x ∂m' := by
    intro m m' hm hm' hle
    have h1 : ∫⁻ x, ENNReal.ofReal (g x) ∂m ≤ c * ∫⁻ x, ENNReal.ofReal (g x) ∂m' := by
      calc ∫⁻ x, ENNReal.ofReal (g x) ∂m ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂(c • m') :=
            lintegral_mono' hle le_rfl
        _ = c * ∫⁻ x, ENNReal.ofReal (g x) ∂m' := by
              rw [lintegral_smul_measure, smul_eq_mul]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top hctop (hglint m')) h1
    rwa [ENNReal.toReal_mul, ← hgtoReal m, ← hgtoReal m'] at h2
  have hbound : ∀ (m : Measure Ω) [IsProbabilityMeasure m], |∫ x, f x ∂m| ≤ nf := by
    intro m _
    have := norm_integral_le_of_norm_le_const (μ := m) (C := nf) (f := f)
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact hnf x)
    rwa [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] at this
  have h1 := hkey μ ρ inferInstance inferInstance hμρ
  have h2 := hkey ρ μ inferInstance inferInstance hρμ
  rw [hgeq μ, hgeq ρ] at h1 h2
  have hbμ := abs_le.1 (hbound μ)
  have hbρ := abs_le.1 (hbound ρ)
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 hc1R) hnf0]

end MeasureTheory

/-! ### Two-sided domination of the Gibbs kernels -/

namespace Potential

open Specification MeasureTheory

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E}

/-- **Two Gibbs kernels whose Hamiltonians differ by at most `D` dominate each other with the
constant `e^{2|β| D}`.**  The Boltzmann densities differ pointwise by the factor `e^{|β| D}`, and
so do the partition functions; the two factors combine in the normalised kernel.

Its home is `GibbsMeasure/Potential/KernelDomination.lean`, next to
`Potential.gibbsSpecificationOfSigmaFiniteAdmissible_le_of_hamiltonian_sub_le`. -/
theorem gibbsSpecificationOfSigmaFiniteAdmissible_le_of_abs_hamiltonian_sub_le
    (Ψ Φ : Potential S E) [IsPotential Ψ] [IsSummable Ψ] [IsPotential Φ] [IsSummable Φ]
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hadmΨ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor β))
    (hadmΦ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (Λ : Finset S) (η : S → E) {D : ℝ}
    (hD : ∀ σ : S → E, |Ψ.hamiltonian Λ σ - Φ.hamiltonian Λ σ| ≤ D)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    gibbsSpecificationOfSigmaFiniteAdmissible Ψ ν β hadmΨ Λ η A
      ≤ ENNReal.ofReal (Real.exp (|β| * D)) * ENNReal.ofReal (Real.exp (|β| * D)) *
        gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadmΦ Λ η A := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|β| * D)) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]; exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hctop : c ≠ ∞ := by rw [hcdef]; exact ENNReal.ofReal_ne_top
  -- the two Boltzmann densities are within a factor `e^{|β| D}` of each other
  have hpt : ∀ (Ψ' Φ' : Potential S E) (_ : IsPotential Ψ') (_ : IsSummable Ψ')
      (_ : IsPotential Φ') (_ : IsSummable Φ'),
      (∀ σ : S → E, |Ψ'.hamiltonian Λ σ - Φ'.hamiltonian Λ σ| ≤ D) →
      ∀ σ : S → E, Ψ'.boltzmannFactor β Λ σ ≤ c * Φ'.boltzmannFactor β Λ σ := by
    intro Ψ' Φ' _ _ _ _ hD' σ
    rw [Potential.boltzmannFactor, Potential.boltzmannFactor, hcdef,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 : |β * (Φ'.hamiltonian Λ σ - Ψ'.hamiltonian Λ σ)| ≤ |β| * D := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact hD' σ) (abs_nonneg β)
    linarith [le_trans (le_abs_self (β * (Φ'.hamiltonian Λ σ - Ψ'.hamiltonian Λ σ))) h1]
  have hDsymm : ∀ σ : S → E, |Φ.hamiltonian Λ σ - Ψ.hamiltonian Λ σ| ≤ D := fun σ ↦ by
    rw [abs_sub_comm]; exact hD σ
  have hptΨ := hpt Ψ Φ inferInstance inferInstance inferInstance inferInstance hD
  have hptΦ := hpt Φ Ψ inferInstance inferInstance inferInstance inferInstance hDsymm
  set lam := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η with hlamdef
  set ZΨ := sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor β) Λ η with hZΨdef
  set ZΦ := sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η with hZΦdef
  -- the numerators
  have hnum : ∫⁻ σ in A, Ψ.boltzmannFactor β Λ σ ∂lam
      ≤ c * ∫⁻ σ in A, Φ.boltzmannFactor β Λ σ ∂lam := by
    calc ∫⁻ σ in A, Ψ.boltzmannFactor β Λ σ ∂lam
        ≤ ∫⁻ σ in A, c * Φ.boltzmannFactor β Λ σ ∂lam := lintegral_mono hptΨ
      _ = c * ∫⁻ σ in A, Φ.boltzmannFactor β Λ σ ∂lam :=
          lintegral_const_mul _ (Potential.measurable_boltzmannFactor β Λ)
  -- the partition functions
  have hZ : ZΦ ≤ c * ZΨ := by
    rw [hZΦdef, hZΨdef, sigmaFiniteLambdaZ, sigmaFiniteLambdaZ, ← hlamdef]
    calc ∫⁻ σ, Φ.boltzmannFactor β Λ σ ∂lam
        ≤ ∫⁻ σ, c * Ψ.boltzmannFactor β Λ σ ∂lam := lintegral_mono hptΦ
      _ = c * ∫⁻ σ, Ψ.boltzmannFactor β Λ σ ∂lam :=
          lintegral_const_mul _ (Potential.measurable_boltzmannFactor β Λ)
  have hZinv : ZΨ⁻¹ ≤ c * ZΦ⁻¹ := by
    have h2 : (c * ZΨ)⁻¹ ≤ ZΦ⁻¹ := ENNReal.inv_le_inv.2 hZ
    rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)] at h2
    calc ZΨ⁻¹ = c * (c⁻¹ * ZΨ⁻¹) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
      _ ≤ c * ZΦ⁻¹ := mul_le_mul' (le_refl c) h2
  rw [gibbsSpecificationOfSigmaFiniteAdmissible_apply_set Ψ ν β hadmΨ Λ η hA,
    gibbsSpecificationOfSigmaFiniteAdmissible_apply_set Φ ν β hadmΦ Λ η hA, ← hlamdef, ← hZΨdef,
    ← hZΦdef]
  calc ZΨ⁻¹ * ∫⁻ σ in A, Ψ.boltzmannFactor β Λ σ ∂lam
      ≤ (c * ZΦ⁻¹) * (c * ∫⁻ σ in A, Φ.boltzmannFactor β Λ σ ∂lam) :=
        mul_le_mul' hZinv hnum
    _ = c * c * (ZΦ⁻¹ * ∫⁻ σ in A, Φ.boltzmannFactor β Λ σ ∂lam) := by ring

end Potential

/-! ### Georgii (4.19) for a `σ`-finite-admissible potential -/

namespace Potential

open Specification MeasureTheory

variable {S E : Type*} [Countable S] {mE : MeasurableSpace E}

/-- **Georgii (4.19), quantitative form, for a `σ`-finite-admissible potential.**  Two Gibbsian
specifications whose Hamiltonians in `Λ` differ by at most `D` act on any bounded observable
within `2‖f‖(e^{2|β| D} - 1)` of each other, uniformly in the boundary condition.

Its home is `GibbsMeasure/Potential/UniformConvergence.lean`, next to
`Potential.dist_action_gibbsSpecification_le`, which is the same statement for absolutely
summable potentials — its proof normalises the Boltzmann density by `Φ.hamiltonianBound Λ`,
which a `C`-potential of Georgii (17.18) need not have. -/
theorem dist_action_gibbsSpecificationOfSigmaFiniteAdmissible_le
    (Ψ Φ : Potential S E) [IsPotential Ψ] [IsSummable Ψ] [IsPotential Φ] [IsSummable Φ]
    (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)
    (hadmΨ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor β))
    (hadmΦ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (Λ : Finset S) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : Measurable ⇑f) {D : ℝ}
    (hD : ∀ σ : S → E, |Ψ.hamiltonian Λ σ - Φ.hamiltonian Λ σ| ≤ D) :
    dist ((gibbsSpecificationOfSigmaFiniteAdmissible Ψ ν β hadmΨ).action Λ f)
        ((gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadmΦ).action Λ f)
      ≤ 2 * ‖f‖ * (Real.exp (2 * (|β| * D)) - 1) := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * (|β| * D))) with hcdef
  have hcsq : ENNReal.ofReal (Real.exp (|β| * D)) * ENNReal.ofReal (Real.exp (|β| * D)) = c := by
    rw [hcdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hctop : c ≠ ∞ := by rw [hcdef]; exact ENNReal.ofReal_ne_top
  have hcR : c.toReal = Real.exp (2 * (|β| * D)) := by
    rw [hcdef, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hDsymm : ∀ σ : S → E, |Φ.hamiltonian Λ σ - Ψ.hamiltonian Λ σ| ≤ D := fun σ ↦ by
    rw [abs_sub_comm]; exact hD σ
  have hE : Nonempty E := ν.nonempty_of_neZero
  have hSE : Nonempty (S → E) := ⟨fun _ ↦ Classical.arbitrary E⟩
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD (Classical.arbitrary _))
  have hC : 0 ≤ 2 * ‖f‖ * (Real.exp (2 * (|β| * D)) - 1) := by
    have h1 : (1 : ℝ) ≤ Real.exp (2 * (|β| * D)) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg f]
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le hC fun η ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, Specification.action_apply, Specification.action_apply,
    Real.norm_eq_abs, ← hcR]
  refine abs_integral_sub_integral_le_of_le_smul hctop ?_ ?_ hf
    (fun x ↦ by rw [← Real.norm_eq_abs]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero f x)
  · refine Measure.le_iff.2 fun A hA ↦ ?_
    rw [Measure.smul_apply, smul_eq_mul, ← hcsq]
    exact gibbsSpecificationOfSigmaFiniteAdmissible_le_of_abs_hamiltonian_sub_le
      Ψ Φ ν β hadmΨ hadmΦ Λ η hD hA
  · refine Measure.le_iff.2 fun A hA ↦ ?_
    rw [Measure.smul_apply, smul_eq_mul, ← hcsq]
    exact gibbsSpecificationOfSigmaFiniteAdmissible_le_of_abs_hamiltonian_sub_le
      Φ Ψ ν β hadmΦ hadmΨ Λ η hDsymm hA

end Potential

/-! ### The Hamiltonian of a `C`-potential depends continuously on the cube interaction -/

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

variable (d) in
/-- The elementary cubes that meet `Λ`: the common finite index set of the Hamiltonians in `Λ` of
all `C`-potentials.  A `C`-potential has finite range, and only these cubes contribute. -/
def cubeInteractingSet (Λ : Finset (Fin d → ℤ)) : Finset (Finset (Fin d → ℤ)) :=
  Λ.biUnion fun x ↦ Finset.univ.image fun c : Fin d → Fin 2 ↦ latticeCube (x - intCubeCast c)

lemma inter_nonempty_of_mem_cubeInteractingSet {Λ : Finset (Fin d → ℤ)}
    {A : Finset (Fin d → ℤ)} (hA : A ∈ cubeInteractingSet d Λ) :
    ((A : Set (Fin d → ℤ)) ∩ (Λ : Set (Fin d → ℤ))).Nonempty := by
  classical
  obtain ⟨x, hx, hA'⟩ := Finset.mem_biUnion.1 hA
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hA'
  refine ⟨x, ?_, by exact_mod_cast hx⟩
  exact_mod_cast mem_latticeCube_iff.2 ⟨c, by ring⟩

lemma interactingSupport_cubePotential_subset {φ : ((Fin d → Fin 2) → E) → ℝ}
    (hφ : Measurable φ) (Λ : Finset (Fin d → ℤ)) :
    Potential.interactingSupport (Φ := cubePotential E φ) Λ ⊆ cubeInteractingSet d Λ := by
  classical
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  intro A hA
  obtain ⟨⟨x, hxA, hxΛ⟩, hΦ⟩ := Potential.mem_interactingSupport.1 hA
  obtain ⟨i, rfl⟩ := cubePotential_ne_zero hΦ
  obtain ⟨c, hc⟩ := latticeCube_sub_intCubeCast (x := x) (i := i) (by exact_mod_cast hxA)
  refine Finset.mem_biUnion.2 ⟨x, by exact_mod_cast hxΛ, ?_⟩
  exact Finset.mem_image.2 ⟨c, Finset.mem_univ c, by rw [hc]⟩

/-- The Hamiltonian in `Λ` of a `C`-potential is the sum of the cube interactions over the cubes
meeting `Λ`, a finite index set that does not depend on the cube interaction. -/
lemma interactingHamiltonian_cubePotential_eq_sum {φ : ((Fin d → Fin 2) → E) → ℝ}
    (hφ : Measurable φ) (Λ : Finset (Fin d → ℤ)) (σ : (Fin d → ℤ) → E) :
    Potential.interactingHamiltonian (Φ := cubePotential E φ) Λ σ
      = ∑ A ∈ cubeInteractingSet d Λ, cubePotential E φ A σ := by
  classical
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  refine Finset.sum_subset (interactingSupport_cubePotential_subset hφ Λ) fun A hA hA' ↦ ?_
  by_contra hne
  exact hA' (Potential.mem_interactingSupport.2
    ⟨inter_nonempty_of_mem_cubeInteractingSet hA, fun h ↦ hne (by rw [h]; rfl)⟩)

/-- The cube interaction of a `C`-potential at a fixed set: at most one elementary cube
contributes, so two `C`-potentials differ there by at most the uniform distance of their cube
interactions. -/
lemma abs_cubePotential_sub_le {ψ φ : ((Fin d → Fin 2) → E) → ℝ} {t : ℝ}
    (ht : ∀ ζ, |ψ ζ - φ ζ| ≤ t) (A : Finset (Fin d → ℤ)) (σ : (Fin d → ℤ) → E) :
    |cubePotential E ψ A σ - cubePotential E φ A σ| ≤ t := by
  classical
  have ht0 : 0 ≤ t := le_trans (abs_nonneg _) (ht (fun _ ↦ σ 0))
  have hcard : (A.filter fun i ↦ latticeCube i = A).card ≤ 1 :=
    Finset.card_le_one.2 fun a ha b hb ↦
      latticeCube_injective ((Finset.mem_filter.1 ha).2.trans (Finset.mem_filter.1 hb).2.symm)
  rw [cubePotential, cubePotential, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ A.filter fun i ↦ latticeCube i = A,
        (ψ (latticeCubeView σ i) - φ (latticeCubeView σ i))|
      ≤ ∑ i ∈ A.filter fun i ↦ latticeCube i = A,
        |ψ (latticeCubeView σ i) - φ (latticeCubeView σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ A.filter fun i ↦ latticeCube i = A, t :=
        Finset.sum_le_sum fun i _ ↦ ht _
    _ = (A.filter fun i ↦ latticeCube i = A).card * t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * t := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) ht0
    _ = t := one_mul t

/-- **The Hamiltonian of a `C`-potential is `|cubeInteractingSet Λ|`-Lipschitz in the uniform
norm of the cube interaction.**  This is what turns Georgii's condition (19.14)(I) —
`‖Ψ^{α_k}_C - Ψ^α_C‖ → 0` — into the hypothesis of Proposition (4.19). -/
theorem abs_hamiltonian_cubePotential_sub_le {ψ φ : ((Fin d → Fin 2) → E) → ℝ}
    (hψ : Measurable ψ) (hφ : Measurable φ) {t : ℝ} (ht : ∀ ζ, |ψ ζ - φ ζ| ≤ t)
    (Λ : Finset (Fin d → ℤ)) (σ : (Fin d → ℤ) → E) :
    |(cubePotential E ψ).hamiltonian Λ σ - (cubePotential E φ).hamiltonian Λ σ|
      ≤ (cubeInteractingSet d Λ).card * t := by
  classical
  have := isPotential_cubePotential (E := E) (φ := ψ) hψ
  have := isPotential_cubePotential (E := E) (φ := φ) hφ
  rw [Potential.hamiltonian_eq_interactingHamiltonian,
    Potential.hamiltonian_eq_interactingHamiltonian,
    interactingHamiltonian_cubePotential_eq_sum hψ, interactingHamiltonian_cubePotential_eq_sum hφ,
    ← Finset.sum_sub_distrib]
  calc |∑ A ∈ cubeInteractingSet d Λ, (cubePotential E ψ A σ - cubePotential E φ A σ)|
      ≤ ∑ A ∈ cubeInteractingSet d Λ, |cubePotential E ψ A σ - cubePotential E φ A σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _A ∈ cubeInteractingSet d Λ, t :=
        Finset.sum_le_sum fun A _ ↦ abs_cubePotential_sub_le ht A σ
    _ = (cubeInteractingSet d Λ).card * t := by rw [Finset.sum_const, nsmul_eq_mul]


/-! ### Georgii (4.19) for `C`-potentials -/

section CubeGibbsSpec

variable {ν : Measure E} [IsProbabilityMeasure ν]

/-- **Georgii, Proposition (4.19), for `C`-potentials.**  If the cube interactions converge
uniformly, `‖Φ^i_C - Φ_C‖ ≤ t i → 0`, then the Gibbsian specifications converge uniformly on
bounded observables: `‖γ^{Φ^i}_Λ f - γ^Φ_Λ f‖ → 0` for every volume `Λ`.

This is verbatim the hypothesis `hunif` of `mem_GP_of_mapClusterPt` (Georgii (4.17)), and it is
what makes a cluster point of Gibbs measures for the potentials `Φ^i` a Gibbs measure for `Φ` —
step (i) of Georgii's Proposition (19.14). -/
theorem tendsto_dist_action_cubeGibbsSpec {ι : Type*} {l : Filter ι}
    {ψs : ι → ((Fin d → Fin 2) → E) → ℝ} {φ : ((Fin d → Fin 2) → E) → ℝ}
    (hψs : ∀ i, Measurable (ψs i)) (hMs : ∀ i, ∃ M : ℝ, ∀ ζ, M ≤ ψs i ζ)
    (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    {t : ι → ℝ} (ht : ∀ i ζ, |ψs i ζ - φ ζ| ≤ t i) (ht0 : Tendsto t l (𝓝 0))
    (Λ : Finset (Fin d → ℤ)) {f : lp (fun _ : (Fin d → ℤ) → E ↦ ℝ) ∞} (hf : Measurable ⇑f) :
    Tendsto (fun i ↦ dist ((cubeGibbsSpec E (ψs i) ν (hψs i) (hMs i)).action Λ f)
      ((cubeGibbsSpec E φ ν hφ hM).action Λ f)) l (𝓝 0) := by
  set K : ℝ := ((cubeInteractingSet d Λ).card : ℝ) with hKdef
  have hbound : ∀ i, dist ((cubeGibbsSpec E (ψs i) ν (hψs i) (hMs i)).action Λ f)
      ((cubeGibbsSpec E φ ν hφ hM).action Λ f)
      ≤ 2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * t i))) - 1) := fun i ↦
    have := isPotential_cubePotential (E := E) (φ := ψs i) (hψs i)
    have := isPotential_cubePotential (E := E) (φ := φ) hφ
    Potential.dist_action_gibbsSpecificationOfSigmaFiniteAdmissible_le
      (cubePotential E (ψs i)) (cubePotential E φ) ν 1
      (isSigmaFiniteLambdaAdmissible_cubePotential (hψs i) (hMs i).choose_spec)
      (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec) Λ hf
      (abs_hamiltonian_cubePotential_sub_le (hψs i) hφ (ht i) Λ)
  refine squeeze_zero (fun i ↦ dist_nonneg) hbound ?_
  have h1 : Tendsto (fun i ↦ 2 * (|(1 : ℝ)| * (K * t i))) l (𝓝 0) := by
    simpa using (ht0.const_mul K).const_mul (2 * |(1 : ℝ)|)
  have h2 : Tendsto (fun i ↦ Real.exp (2 * (|(1 : ℝ)| * (K * t i))) - 1) l (𝓝 0) := by
    have h3 : Tendsto (fun i ↦ Real.exp (2 * (|(1 : ℝ)| * (K * t i)))) l (𝓝 1) := by
      simpa [Real.exp_zero, Function.comp_def] using (Real.continuous_exp.tendsto 0).comp h1
    simpa using h3.sub_const 1
  simpa using h2.const_mul (2 * ‖f‖)


/-- **Georgii, Proposition (4.19), for `C`-potentials**, with the convergence of the cube
interactions stated as "eventually within `ε`, for every `ε > 0`" rather than through a modulus.
This is the form in which Georgii's condition (19.14)(I) delivers it. -/
theorem tendsto_dist_action_cubeGibbsSpec_of_eventually {ι : Type*} {l : Filter ι}
    {ψs : ι → ((Fin d → Fin 2) → E) → ℝ} {φ : ((Fin d → Fin 2) → E) → ℝ}
    (hψs : ∀ i, Measurable (ψs i)) (hMs : ∀ i, ∃ M : ℝ, ∀ ζ, M ≤ ψs i ζ)
    (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    (ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ ζ, |ψs i ζ - φ ζ| ≤ ε)
    (Λ : Finset (Fin d → ℤ)) {f : lp (fun _ : (Fin d → ℤ) → E ↦ ℝ) ∞} (hf : Measurable ⇑f) :
    Tendsto (fun i ↦ dist ((cubeGibbsSpec E (ψs i) ν (hψs i) (hMs i)).action Λ f)
      ((cubeGibbsSpec E φ ν hφ hM).action Λ f)) l (𝓝 0) := by
  set K : ℝ := ((cubeInteractingSet d Λ).card : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  rw [Metric.tendsto_nhds]
  intro δ hδ
  -- choose `ε > 0` so small that `2‖f‖(e^{2Kε} - 1) < δ`
  have hg : Tendsto (fun ε : ℝ ↦ 2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * ε))) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ ↦ 2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * ε))) - 1) := by
      fun_prop
    have h0 : Tendsto (fun ε : ℝ ↦ 2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * ε))) - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * 0))) - 1))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0
  obtain ⟨ε, hεpos, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧
      2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * ε))) - 1) < δ := by
    obtain ⟨ε, hε1, hε2⟩ := ((hg.eventually_lt_const hδ).and self_mem_nhdsWithin).exists
    exact ⟨ε, hε2, hε1⟩
  filter_upwards [ht ε hεpos] with i hi
  have hle : dist ((cubeGibbsSpec E (ψs i) ν (hψs i) (hMs i)).action Λ f)
      ((cubeGibbsSpec E φ ν hφ hM).action Λ f)
      ≤ 2 * ‖f‖ * (Real.exp (2 * (|(1 : ℝ)| * (K * ε))) - 1) :=
    have := isPotential_cubePotential (E := E) (φ := ψs i) (hψs i)
    have := isPotential_cubePotential (E := E) (φ := φ) hφ
    Potential.dist_action_gibbsSpecificationOfSigmaFiniteAdmissible_le
      (cubePotential E (ψs i)) (cubePotential E φ) ν 1
      (isSigmaFiniteLambdaAdmissible_cubePotential (hψs i) (hMs i).choose_spec)
      (isSigmaFiniteLambdaAdmissible_cubePotential hφ hM.choose_spec) Λ hf
      (abs_hamiltonian_cubePotential_sub_le (hψs i) hφ hi Λ)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  exact lt_of_le_of_lt hle hεlt

end CubeGibbsSpec

end MeasureTheory.GibbsMeasure

end

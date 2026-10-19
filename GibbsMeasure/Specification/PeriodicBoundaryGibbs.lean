/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LargeDeviationsUpper

/-!
# The Gibbs distributions with periodic boundary conditions (Georgii §15.5)

Georgii's remark after Theorem (15.45) introduces the Gibbs distributions with *periodic* boundary
conditions,

`°γ^Φ_Λ = exp[−°H^Φ_Λ] λ^Λ / °Z^Φ_Λ`,

where `°H^Φ_Λ` is the Hamiltonian in the cube `Λ` with periodic boundary conditions of Remark
(15.43)(3), and asserts that both inequalities of Theorem (15.45) hold for them, with a *simpler*
proof: `°H^Φ_Λ` is a function of the periodic empirical field `°R_Λ`, namely
`°H^Φ_Λ = |Λ| ⟨°R_Λ, Φ⟩`, so the energy errors (15.25) never enter. Everything downstream of that
remark — Corollary (15.48), Example (15.50) and Corollary (15.58) — is stated for `°γ^Φ_Λ`.

## The objects

* `Potential.periodicBoundaryHamiltonian Φ π Λ ω`, **Georgii Remark (15.43)(3)**: the Hamiltonian
  with periodic boundary conditions `°H^Φ_Λ(ω) = ∑_{i ∈ Λ} f_Φ(θ_{-i} ω^∘_Λ)`, the spatial sum of
  the site energies (15.22) of the periodic continuation `ω^∘_Λ` of `ω_Λ` along the torus
  reduction `π` of `Λ` (Example (4.20)(2), `Potential.IsTorusReduction`). It is defined for an
  arbitrary additive group of sites and an arbitrary potential;
  `Potential.periodicBoundaryHamiltonian_eq_card_mul_specificEnergy` is Georgii's formula
  `°H^Φ_Λ = |Λ| ⟨°R_Λ, Φ⟩` for `Φ ∈ ℬ_Θ`. Georgii *defines* `°H^Φ_Λ` as the Hamiltonian
  `H_Λ^{Φ̃^Λ}` of the periodic modification `Φ̃^Λ` of Example (4.20)(2)
  (`Potential.periodicModification`) and says the formula is "easily checked"; here the formula
  is the definition, since it is the only property of `°H^Φ_Λ` that §15.5 uses.
* `Potential.periodicBoundaryZ ν Φ π Λ`, the partition function `°Z^Φ_Λ = λ^Λ(e^{−°H^Φ_Λ})`, and
  `Potential.logPeriodicBoundaryZ`, its logarithm.
* `Potential.periodicBoundaryGibbs ν Φ π Λ`, **the Gibbs distribution `°γ^Φ_Λ` with periodic
  boundary conditions**: the probability measure `e^{−°H^Φ_Λ} / °Z^Φ_Λ · λ^S` on the configuration
  space `Ω = E^S`. Georgii's `°γ^Φ_Λ` is a measure on `E^Λ` which he "views as a probability
  measure on `(Ω, 𝓕)` with marginal on `E^Λ` as above" without specifying the extension; the
  density `e^{−°H^Φ_Λ}/°Z^Φ_Λ` is `𝓕_Λ`-measurable, so the choice made here — the a priori
  product measure `λ^S` outside `Λ`, exactly as the free part of Georgii's Gibbs kernels is the
  independent specification — has the prescribed marginal
  (`Potential.trim_periodicBoundaryGibbs_eq_withDensity`), and nothing below depends on the
  extension: every event of the form `{°R_Λ ∈ C}` is an event of the volume `Λ`.

## The properties that carry (15.46) and (15.47) for `°γ^Φ_Λ`

* `Potential.le_periodicBoundaryGibbs_apply`: the lower bound
  `°γ^Φ_Λ(A) ≥ e^{−b − log °Z^Φ_Λ} λ^S(A)` on an event `A` on which `°H^Φ_Λ ≤ b`, the periodic
  counterpart of the first inequality in Georgii's proof of (15.47).
* `Potential.relativeEntropyIn_periodicBoundaryGibbs_eq`, Georgii (15.34) for `°γ^Φ_Λ`:
  `𝓗_Λ(μ | °γ^Φ_Λ) = −𝓗_Λ(μ) + μ(°H^Φ_Λ) + log °Z^Φ_Λ`, and
  `Potential.neg_log_periodicBoundaryGibbs_eq`, Step 1 of the proof of (15.46) for `°γ^Φ_Λ`:
  `−log °γ^Φ_Λ(A) = 𝓗_Λ(°γ^A_Λ | λ^S) + °γ^A_Λ(°H^Φ_Λ) + log °Z^Φ_Λ` for the conditional
  distribution `°γ^A_Λ = °γ^Φ_Λ(· | A)` of a `𝓕_Λ`-event `A` of positive probability.
* `Potential.abs_periodicBoundaryHamiltonian_sub_hamiltonian_juxt_le` and
  `Potential.abs_logPeriodicBoundaryZ_sub_logZ_le`: the periodic Hamiltonian and partition
  function are within `3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` of those with any configurational boundary
  condition (Georgii (15.25)); hence `Potential.tendsto_logPeriodicBoundaryZ_div_card`,
  **Georgii (15.31) for `°Z^Φ_Λ`**: `|Λ_n|⁻¹ log °Z^Φ_{Λ_n} → P(Φ)` along boxes all of whose
  sides tend to infinity.
* `MeasureTheory.GibbsMeasure.periodicEmpiricalField_periodicTranslate` and
  `Potential.periodicBoundaryGibbs_preimage_periodicTranslate`: the toroidal shifts
  `θ°_i : ω ↦ θ_{-i} ω^∘_Λ` of Georgii's proof of (15.58) leave `°R_Λ`, hence `°H^Φ_Λ`, hence
  `°γ^Φ_Λ` (on the events of the volume `Λ`) invariant, and
  `Potential.empiricalFieldAverage_periodicBoundaryGibbs_cond_apply`: consequently
  `σ_Λ(°γ^B_Λ °R_Λ) = °γ^B_Λ` for the conditional distributions `°γ^B_Λ = °γ^Φ_Λ(· | {°R_Λ ∈ C})`,
  the identity that closes Georgii's proof of Corollary (15.58).

## Theorem (15.45) for `°γ^Φ_Λ`

* `MeasureTheory.GibbsMeasure.neg_iInf_specificRelativeEntropy_le_liminf_log_periodicBoundaryGibbs`,
  **the lower bound (15.47) for `°γ^Φ_Λ`**, over an arbitrary measurable state space and along
  any sequence of cubes whose side tends to infinity; the input is the window lemma
  `eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem` of
  `GibbsMeasure/Specification/LargeDeviationsLower.lean`, the common core of the two proofs of
  (15.47).
* `MeasureTheory.GibbsMeasure.limsup_log_periodicBoundaryGibbs_div_card_le_closedConvexHull`,
  **the upper bound (15.46) for `°γ^Φ_Λ` with Georgii's `cx̄ C` on the right, over a standard
  Borel state space**, under his hypothesis `C ∈ 𝓔(𝓟_Θ)`, with the exponential form
  `eventually_periodicBoundaryGibbs_setOf_mem_le_of_measurableSet`; and
  `limsup_log_periodicBoundaryGibbs_div_card_le_of_convex`, **the upper bound as Georgii states
  it, with `C̄` on the right**, for a convex `C`, for which `cx̄ C = C̄`.
* `MeasureTheory.GibbsMeasure.limsup_log_periodicBoundaryGibbs_div_card_le`, **the upper bound
  (15.46) for `°γ^Φ_Λ` with `C̄` on the right for a general `C`**, over a finite state space,
  where Georgii's Step 3 is available; the finite-volume input
  `specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le` is Steps 1 and 2 of
  Georgii's proof *without* the energy error, and the cluster-point argument is the common core
  `mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto` of
  `GibbsMeasure/Specification/LargeDeviationsUpper.lean` (all in `MeasureTheory.GibbsMeasure`).
  The module documentation of that file explains why Step 3, and only Step 3, is finite-only.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open InformationTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Georgii Remark (15.43)(3): the Hamiltonian with periodic boundary conditions -/

namespace Potential

section Hamiltonian

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E] {Φ : Potential S E}
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

variable (Φ) in
/-- **Georgii Remark (15.43)(3).** The Hamiltonian in the box `Λ` with periodic boundary
conditions, `°H^Φ_Λ(ω) = ∑_{i ∈ Λ} f_Φ(θ_{-i} ω^∘_Λ)`: the spatial sum over the torus `Λ` of the
site energies (15.22) of the periodic continuation `ω^∘_Λ` of `ω_Λ` along the torus reduction
`π`. For `Φ ∈ ℬ_Θ` this is Georgii's formula `°H^Φ_Λ = |Λ| ⟨°R_Λ, Φ⟩`
(`Potential.periodicBoundaryHamiltonian_eq_card_mul_specificEnergy`). -/
def periodicBoundaryHamiltonian (π : S → S) (Λ : Finset S) (ω : S → E) : ℝ :=
  ∑ i ∈ Λ, Φ.siteEnergy i (periodicExtend π ω)

/-- **Georgii Remark (15.43)(3).** `°H^Φ_Λ = |Λ| ⟨°R_Λ, Φ⟩`: the Hamiltonian with periodic
boundary conditions is `|Λ|` times the specific energy of the periodic empirical field. -/
theorem periodicBoundaryHamiltonian_eq_card_mul_specificEnergy [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant) (π : S → S) (Λ : Finset S) (ω : S → E) :
    Φ.periodicBoundaryHamiltonian π Λ ω
      = (#Λ : ℝ) * Φ.specificEnergy (periodicEmpiricalField E π Λ ω) := by
  rw [specificEnergy_periodicEmpiricalField hΦ π Λ ω, periodicBoundaryHamiltonian]
  rcases Λ.eq_empty_or_nonempty with rfl | hne
  · simp
  · rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hne.card_pos.ne'), one_mul]

/-- **Georgii Remark (15.43)(3).** `|Λ|⁻¹ °H^Φ_Λ = ⟨°R_Λ, Φ⟩`: the periodic Hamiltonian per site
is the specific energy of the periodic empirical field. This is the identity that turns an event
`{|Λ|⁻¹ °H^Ψ_Λ ∈ B}` of Corollary (15.48) into an event `{°R_Λ ∈ e_Ψ⁻¹(B)}` of Theorem (15.45). -/
theorem inv_card_mul_periodicBoundaryHamiltonian_eq [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant) (π : S → S) {Λ : Finset S}
    (hΛ : Λ.Nonempty) (ω : S → E) :
    (#Λ : ℝ)⁻¹ * Φ.periodicBoundaryHamiltonian π Λ ω
      = Φ.specificEnergy (periodicEmpiricalField E π Λ ω) := by
  rw [periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast hΛ.card_pos.ne'), one_mul]

omit [AddCommGroup S] in
/-- `|°H^Φ_Λ| ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
theorem abs_periodicBoundaryHamiltonian_le [IsAbsolutelySummable Φ] (π : S → S) (Λ : Finset S)
    (ω : S → E) :
    |Φ.periodicBoundaryHamiltonian π Λ ω| ≤ Φ.hamiltonianBound Λ := by
  rw [hamiltonianBound, ENNReal.toReal_sum fun i _ ↦ IsAbsolutelySummable.normAt_ne_top i,
    periodicBoundaryHamiltonian]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ ↦ abs_siteEnergy_le i _)

/-- `°H^Φ_Λ` is measurable for the cylinder σ-algebra `𝓕_Λ` of the box itself: the periodic
continuation reads the configuration only in `Λ`. -/
theorem measurable_cylinderEvents_periodicBoundaryHamiltonian [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hπ : IsTorusReduction G Λ π) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      (Φ.periodicBoundaryHamiltonian π Λ) :=
  Finset.measurable_sum _ fun i _ ↦
    (measurable_siteEnergy i).comp (measurable_cylinderEvents_periodicExtend hπ)

theorem measurable_periodicBoundaryHamiltonian [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hπ : IsTorusReduction G Λ π) :
    Measurable (Φ.periodicBoundaryHamiltonian π Λ) :=
  (measurable_cylinderEvents_periodicBoundaryHamiltonian hπ).mono cylinderEvents_le_pi le_rfl

/-- **Georgii's estimate (15.25) between the periodic and a configurational boundary
condition**: `|°H^Φ_Λ(y) − H^Φ_Λ(y_Λ ω_{S∖Λ})| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` for every
boundary condition `ω`. -/
theorem abs_periodicBoundaryHamiltonian_sub_hamiltonian_juxt_le [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant) (hπ : IsTorusReduction G Λ π)
    (hΛ : Λ.Nonempty) (ω y : S → E) :
    |Φ.periodicBoundaryHamiltonian π Λ y - Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ y i)|
      ≤ 3 * Φ.tail Λ Λ := by
  have h := abs_hamiltonian_sub_card_mul_specificEnergy_periodicEmpiricalField_le hΦ hπ hΛ
    (juxt (Λ : Set S) ω fun i ↦ y i)
  rw [show periodicEmpiricalField E π Λ (juxt (Λ : Set S) ω fun i ↦ y i)
      = periodicEmpiricalField E π Λ y by
        rw [periodicEmpiricalField, periodicEmpiricalField, periodicExtend_juxt hπ ω y],
    ← periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ, abs_sub_comm] at h
  exact h

end Hamiltonian

/-! ### The toroidal shifts leave the periodic empirical field invariant -/

end Potential

namespace MeasureTheory.GibbsMeasure

section Torus

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

/-- The periodic continuation of a periodic configuration is itself: `(θ_{-j} ω^∘_Λ)^∘_Λ =
θ_{-j} ω^∘_Λ`. -/
lemma periodicExtend_periodicTranslate (hπ : Potential.IsTorusReduction G Λ π) (j : S)
    (ω : S → E) :
    Potential.periodicExtend π (periodicTranslate E π j ω) = periodicTranslate E π j ω := by
  funext n
  simp only [Potential.periodicExtend, periodicTranslate_apply]
  refine congrArg ω (hπ.reduce_eq _ _ ?_)
  have h : π n + j - (n + j) = π n - n := by abel
  rw [h]
  exact hπ.sub_mem' n

/-- **Georgii, proof of (15.58).** The periodic empirical field is invariant under the toroidal
shifts `θ°_j : ω ↦ θ_{-j} ω^∘_Λ` of `E^Λ`: `°R^{θ°_j ω}_Λ = °R^ω_Λ`. Indeed `°R^{θ°_j ω}_Λ` is
the image of `°R^ω_Λ` under `θ_{-j}`, and `°R^ω_Λ` is shift invariant. -/
theorem periodicEmpiricalField_periodicTranslate (hπ : Potential.IsTorusReduction G Λ π) (j : S)
    (ω : S → E) :
    periodicEmpiricalField E π Λ (periodicTranslate E π j ω) = periodicEmpiricalField E π Λ ω := by
  have hmap : periodicEmpiricalField E π Λ (periodicTranslate E π j ω)
      = (periodicEmpiricalField E π Λ ω).map (shift E (-j)).toFun := by
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.map_apply (shift E (-j)).measurable_toFun hA,
      periodicEmpiricalField_apply _ _ _ ((shift E (-j)).measurable_toFun hA),
      periodicEmpiricalField_apply _ _ _ hA, periodicExtend_periodicTranslate hπ]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ ?_)
    have hcomm : (shift E (-i)).toFun (periodicTranslate E π j ω)
        = (shift E (-j)).toFun ((shift E (-i)).toFun (Potential.periodicExtend π ω)) := by
      funext n
      simp only [periodicTranslate, shift_toFun_apply]
      congr 1
      abel
    rw [hcomm]
    by_cases hm : (shift E (-j)).toFun ((shift E (-i)).toFun (Potential.periodicExtend π ω)) ∈ A
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show _ ∈ (shift E (-j)).toFun ⁻¹' A
        from hm), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show _ ∉ (shift E (-j)).toFun ⁻¹' A
        from hm)]
  rw [hmap, map_shift_periodicEmpiricalField hπ ω (-j)]

/-- The toroidal shift `θ°_j` is a `𝓕_Λ`-measurable map. -/
lemma measurable_cylinderEvents_periodicTranslate (hπ : Potential.IsTorusReduction G Λ π)
    (j : S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] (periodicTranslate E π j) :=
  (shift E (-j)).measurable_toFun.comp (measurable_cylinderEvents_periodicExtend hπ)

/-- The toroidal shift `θ°_j` maps `𝓕_Λ`-measurable functions to `𝓕_Λ`-measurable functions of
`ω_Λ` (it reads `ω` only at sites of `Λ`); in particular the composition of a `𝓕_Λ`-measurable
function with `θ°_j` is again `𝓕_Λ`-measurable, which is all that is used. -/
lemma preimage_periodicTranslate_eq_restrict_preimage (hπ : Potential.IsTorusReduction G Λ π)
    (j : S) {B : Set (Λ → E)} :
    periodicTranslate E π j ⁻¹' (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B)
      = Λ.restrict (π := fun _ : S ↦ E) ⁻¹'
          ((fun x : Λ → E ↦ fun n : Λ ↦ x ⟨π (n + j), hπ.mapsTo _⟩) ⁻¹' B) := by
  ext ω
  simp only [Set.mem_preimage]
  have h : Λ.restrict (π := fun _ : S ↦ E) (periodicTranslate E π j ω)
      = fun n : Λ ↦ Λ.restrict (π := fun _ : S ↦ E) ω ⟨π (n + j), hπ.mapsTo _⟩ := by
    funext n
    simp [Finset.restrict, periodicTranslate_apply]
  rw [h]

/-- The site permutation `n ↦ π (n + j)` of the torus `Λ` induced by the toroidal shift. -/
def torusSiteEquiv (hπ : Potential.IsTorusReduction G Λ π) (j : S) : Λ ≃ Λ where
  toFun n := ⟨π (n + j), hπ.mapsTo _⟩
  invFun n := ⟨π (n - j), hπ.mapsTo _⟩
  left_inv n := by
    refine Subtype.ext (hπ.eq_of_mem_of_sub_mem n.2 ?_)
    change π (n + j) - j - n ∈ G
    have h : π (n + j) - j - n = π (n + j) - (n + j) := by abel
    rw [h]
    exact hπ.sub_mem' _
  right_inv n := by
    refine Subtype.ext (hπ.eq_of_mem_of_sub_mem n.2 ?_)
    change π (n - j) + j - n ∈ G
    have h : π (n - j) + j - n = π (n - j) - (n - j) := by abel
    rw [h]
    exact hπ.sub_mem' _

lemma torusSiteEquiv_apply (hπ : Potential.IsTorusReduction G Λ π) (j : S) (n : Λ) :
    (torusSiteEquiv hπ j n : S) = π (n + j) := rfl

/-- **The a priori product measure is invariant under the toroidal shifts on the events of the
volume `Λ`**: `θ°_j` permutes the coordinates in `Λ`, and `λ^Λ` is permutation invariant. -/
theorem infinitePi_preimage_periodicTranslate (hπ : Potential.IsTorusReduction G Λ π) (j : S)
    (ν : Measure E) [IsProbabilityMeasure ν] {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    (Measure.infinitePi fun _ : S ↦ ν) (periodicTranslate E π j ⁻¹' A)
      = (Measure.infinitePi fun _ : S ↦ ν) A := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  set T' : (Λ → E) → Λ → E := fun x n ↦ x (torusSiteEquiv hπ j n) with hT'
  have hT'm : Measurable T' := Measurable.of_eval fun n ↦ measurable_pi_apply _
  have hpre : periodicTranslate E π j ⁻¹' (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B)
      = Λ.restrict (π := fun _ : S ↦ E) ⁻¹' (T' ⁻¹' B) :=
    preimage_periodicTranslate_eq_restrict_preimage hπ j
  have h1 : (Measure.infinitePi fun _ : S ↦ ν) (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' (T' ⁻¹' B))
      = (Measure.pi fun _ : Λ ↦ ν) (T' ⁻¹' B) := by
    rw [← Measure.infinitePi_map_restrict (μ := fun _ : S ↦ ν) (I := Λ),
      Measure.map_apply (Finset.measurable_restrict Λ) (hT'm hB)]
  have h2 : (Measure.infinitePi fun _ : S ↦ ν) (Λ.restrict (π := fun _ : S ↦ E) ⁻¹' B)
      = (Measure.pi fun _ : Λ ↦ ν) B := by
    rw [← Measure.infinitePi_map_restrict (μ := fun _ : S ↦ ν) (I := Λ),
      Measure.map_apply (Finset.measurable_restrict Λ) hB]
  -- `λ^Λ` is invariant under the permutation `n ↦ π (n + j)` of the coordinates
  have hmp : MeasurePreserving T' (Measure.pi fun _ : Λ ↦ ν) (Measure.pi fun _ : Λ ↦ ν) := by
    have h := (measurePreserving_piCongrLeft (fun _ : Λ ↦ ν) (torusSiteEquiv hπ j)).symm _
    have heq : T' = ⇑(MeasurableEquiv.piCongrLeft (fun _ : Λ ↦ E) (torusSiteEquiv hπ j)).symm := by
      funext x n
      rfl
    rw [heq]
    exact h
  rw [hpre, h1, h2]
  exact hmp.measure_preimage hB.nullMeasurableSet

/-- The toroidal shift `θ°_j` pulls events of the volume `Λ` back to events of the volume `Λ`. -/
lemma measurableSet_cylinderEvents_preimage_periodicTranslate
    (hπ : Potential.IsTorusReduction G Λ π) (j : S) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      (periodicTranslate E π j ⁻¹' A) := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA ⊢
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  refine MeasurableSpace.measurableSet_comap.2 ⟨_, (Measurable.of_eval fun n ↦
    measurable_pi_apply _) hB, (preimage_periodicTranslate_eq_restrict_preimage hπ j).symm⟩

end Torus

end MeasureTheory.GibbsMeasure

/-! ### The Gibbs distribution with periodic boundary conditions -/

namespace Potential

section Gibbs

variable {S E : Type*} [Countable S] [AddCommGroup S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

variable (Φ) in
/-- The partition function with periodic boundary conditions, `°Z^Φ_Λ = λ^Λ(e^{−°H^Φ_Λ})`. -/
def periodicBoundaryZ (π : S → S) (Λ : Finset S) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω))
    ∂(Measure.infinitePi fun _ : S ↦ ν)

variable (Φ) in
/-- `log °Z^Φ_Λ`, the finite-volume pressure with periodic boundary conditions. -/
def logPeriodicBoundaryZ (π : S → S) (Λ : Finset S) : ℝ :=
  Real.log (Φ.periodicBoundaryZ ν π Λ).toReal

variable (Φ) in
/-- The density `e^{−°H^Φ_Λ} / °Z^Φ_Λ` of the Gibbs distribution with periodic boundary
conditions with respect to the a priori product measure `λ^S`. -/
def periodicBoundaryDensity (π : S → S) (Λ : Finset S) (ω : S → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω)) / Φ.periodicBoundaryZ ν π Λ

variable (Φ) in
/-- **Georgii, after Theorem (15.45).** The Gibbs distribution `°γ^Φ_Λ = e^{−°H^Φ_Λ} λ^Λ / °Z^Φ_Λ`
in the box `Λ` with periodic boundary conditions along the torus reduction `π`, as the probability
measure on the configuration space with density `e^{−°H^Φ_Λ} / °Z^Φ_Λ` relative to the a priori
product measure `λ^S`. Its restriction to `𝓕_Λ` is Georgii's measure on `E^Λ`
(`Potential.trim_periodicBoundaryGibbs_eq_withDensity`). -/
def periodicBoundaryGibbs (π : S → S) (Λ : Finset S) : Measure (S → E) :=
  (Measure.infinitePi fun _ : S ↦ ν).withDensity (Φ.periodicBoundaryDensity ν π Λ)

lemma le_periodicBoundaryZ (π : S → S) (Λ : Finset S) :
    ENNReal.ofReal (Real.exp (-Φ.hamiltonianBound Λ)) ≤ Φ.periodicBoundaryZ ν π Λ := by
  rw [periodicBoundaryZ]
  calc ENNReal.ofReal (Real.exp (-Φ.hamiltonianBound Λ))
      = ∫⁻ _, ENNReal.ofReal (Real.exp (-Φ.hamiltonianBound Λ))
          ∂(Measure.infinitePi fun _ : S ↦ ν) := by simp
    _ ≤ _ := lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
        linarith [(abs_le.1 (abs_periodicBoundaryHamiltonian_le (Φ := Φ) π Λ ω)).2]))

lemma periodicBoundaryZ_le (π : S → S) (Λ : Finset S) :
    Φ.periodicBoundaryZ ν π Λ ≤ ENNReal.ofReal (Real.exp (Φ.hamiltonianBound Λ)) := by
  rw [periodicBoundaryZ]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω))
          ∂(Measure.infinitePi fun _ : S ↦ ν)
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (Φ.hamiltonianBound Λ))
          ∂(Measure.infinitePi fun _ : S ↦ ν) :=
        lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
          linarith [(abs_le.1 (abs_periodicBoundaryHamiltonian_le (Φ := Φ) π Λ ω)).1]))
    _ = _ := by simp

lemma periodicBoundaryZ_pos (π : S → S) (Λ : Finset S) : 0 < Φ.periodicBoundaryZ ν π Λ :=
  lt_of_lt_of_le (by simp [Real.exp_pos]) (le_periodicBoundaryZ ν π Λ)

lemma periodicBoundaryZ_ne_top (π : S → S) (Λ : Finset S) : Φ.periodicBoundaryZ ν π Λ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (periodicBoundaryZ_le ν π Λ)

lemma toReal_periodicBoundaryZ_pos (π : S → S) (Λ : Finset S) :
    0 < (Φ.periodicBoundaryZ ν π Λ).toReal :=
  ENNReal.toReal_pos (periodicBoundaryZ_pos ν π Λ).ne' (periodicBoundaryZ_ne_top ν π Λ)

lemma periodicBoundaryDensity_ne_zero (π : S → S) (Λ : Finset S) (ω : S → E) :
    Φ.periodicBoundaryDensity ν π Λ ω ≠ 0 := by
  rw [periodicBoundaryDensity, Ne, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by simp [Real.exp_pos], periodicBoundaryZ_ne_top ν π Λ⟩

lemma periodicBoundaryDensity_ne_top (π : S → S) (Λ : Finset S) (ω : S → E) :
    Φ.periodicBoundaryDensity ν π Λ ω ≠ ⊤ := by
  rw [periodicBoundaryDensity, Ne, ENNReal.div_eq_top, not_or, not_and_or, not_and_or]
  exact ⟨Or.inr (periodicBoundaryZ_pos ν π Λ).ne', Or.inl ENNReal.ofReal_ne_top⟩

lemma measurable_cylinderEvents_periodicBoundaryDensity (hπ : IsTorusReduction G Λ π) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      (Φ.periodicBoundaryDensity ν π Λ) :=
  (((measurable_cylinderEvents_periodicBoundaryHamiltonian hπ).neg.exp).ennreal_ofReal).div
    measurable_const

lemma measurable_periodicBoundaryDensity (hπ : IsTorusReduction G Λ π) :
    Measurable (Φ.periodicBoundaryDensity ν π Λ) :=
  (measurable_cylinderEvents_periodicBoundaryDensity ν hπ).mono cylinderEvents_le_pi le_rfl

/-- `log (e^{−°H^Φ_Λ} / °Z^Φ_Λ) = −°H^Φ_Λ − log °Z^Φ_Λ`. -/
lemma log_toReal_periodicBoundaryDensity (π : S → S) (Λ : Finset S) (ω : S → E) :
    Real.log (Φ.periodicBoundaryDensity ν π Λ ω).toReal
      = -Φ.periodicBoundaryHamiltonian π Λ ω - Φ.logPeriodicBoundaryZ ν π Λ := by
  rw [periodicBoundaryDensity, ENNReal.toReal_div, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_div (Real.exp_ne_zero _) (toReal_periodicBoundaryZ_pos ν π Λ).ne', Real.log_exp,
    logPeriodicBoundaryZ]

lemma abs_log_toReal_periodicBoundaryDensity_le (π : S → S) (Λ : Finset S) (ω : S → E) :
    |Real.log (Φ.periodicBoundaryDensity ν π Λ ω).toReal|
      ≤ Φ.hamiltonianBound Λ + |Φ.logPeriodicBoundaryZ ν π Λ| := by
  rw [log_toReal_periodicBoundaryDensity]
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  rw [abs_neg]
  exact abs_periodicBoundaryHamiltonian_le π Λ ω

/-- `°γ^Φ_Λ(A) = (°Z^Φ_Λ)⁻¹ ∫_A e^{−°H^Φ_Λ} dλ^S`. -/
theorem periodicBoundaryGibbs_apply (π : S → S) (Λ : Finset S) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    Φ.periodicBoundaryGibbs ν π Λ A
      = (Φ.periodicBoundaryZ ν π Λ)⁻¹ * ∫⁻ ω in A,
          ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω))
            ∂(Measure.infinitePi fun _ : S ↦ ν) := by
  rw [periodicBoundaryGibbs, withDensity_apply _ hA]
  simp only [periodicBoundaryDensity, ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (periodicBoundaryZ_pos ν π Λ).ne')]

/-- `°γ^Φ_Λ` is a probability measure. -/
instance isProbabilityMeasure_periodicBoundaryGibbs (π : S → S) (Λ : Finset S) :
    IsProbabilityMeasure (Φ.periodicBoundaryGibbs ν π Λ) where
  measure_univ := by
    have h : ∫⁻ ω in Set.univ, ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω))
        ∂(Measure.infinitePi fun _ : S ↦ ν) = Φ.periodicBoundaryZ ν π Λ := by
      rw [Measure.restrict_univ, periodicBoundaryZ]
    rw [periodicBoundaryGibbs_apply ν π Λ MeasurableSet.univ, h,
      ENNReal.inv_mul_cancel (periodicBoundaryZ_pos ν π Λ).ne' (periodicBoundaryZ_ne_top ν π Λ)]

/-- **The restriction of `°γ^Φ_Λ` to `𝓕_Λ` is Georgii's measure `e^{−°H^Φ_Λ} λ^Λ / °Z^Φ_Λ`**: on the
cylinder σ-algebra of the box it has the density `e^{−°H^Φ_Λ} / °Z^Φ_Λ` relative to `λ^S`. -/
theorem trim_periodicBoundaryGibbs_eq_withDensity (hπ : IsTorusReduction G Λ π) :
    (Φ.periodicBoundaryGibbs ν π Λ).trim
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))
      = ((Measure.infinitePi fun _ : S ↦ ν).trim
          (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))).withDensity
            (Φ.periodicBoundaryDensity ν π Λ) :=
  trim_withDensity _ (measurable_cylinderEvents_periodicBoundaryDensity ν hπ)

/-- **The periodic Gibbs distribution of an event is bounded below by the free measure**, the
periodic counterpart of the first inequality in Georgii's proof of the lower bound (15.47):
`°γ^Φ_Λ(A) ≥ e^{−b − log °Z^Φ_Λ} λ^S(A)` on an event `A` on which `°H^Φ_Λ ≤ b`. -/
theorem le_periodicBoundaryGibbs_apply (π : S → S) (Λ : Finset S) {A : Set (S → E)}
    (hA : MeasurableSet A) {b : ℝ} (hb : ∀ y ∈ A, Φ.periodicBoundaryHamiltonian π Λ y ≤ b) :
    ENNReal.ofReal (Real.exp (-b - Φ.logPeriodicBoundaryZ ν π Λ))
        * (Measure.infinitePi fun _ : S ↦ ν) A
      ≤ Φ.periodicBoundaryGibbs ν π Λ A := by
  have hZR := toReal_periodicBoundaryZ_pos ν (Φ := Φ) π Λ
  rw [periodicBoundaryGibbs_apply ν π Λ hA]
  have hint : ENNReal.ofReal (Real.exp (-b)) * (Measure.infinitePi fun _ : S ↦ ν) A
      ≤ ∫⁻ ω in A, ENNReal.ofReal (Real.exp (-Φ.periodicBoundaryHamiltonian π Λ ω))
          ∂(Measure.infinitePi fun _ : S ↦ ν) := by
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hA fun y hy ↦
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hb y hy]))
  have hexp : Real.exp (-b - Φ.logPeriodicBoundaryZ ν π Λ)
      = ((Φ.periodicBoundaryZ ν π Λ).toReal)⁻¹ * Real.exp (-b) := by
    rw [logPeriodicBoundaryZ, sub_eq_neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hZR]
  have hfac : ENNReal.ofReal (Real.exp (-b - Φ.logPeriodicBoundaryZ ν π Λ))
      = (Φ.periodicBoundaryZ ν π Λ)⁻¹ * ENNReal.ofReal (Real.exp (-b)) := by
    rw [hexp, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hZR,
      ENNReal.ofReal_toReal (periodicBoundaryZ_ne_top ν π Λ)]
  rw [hfac, mul_assoc]
  gcongr

/-- **Georgii (15.34) for the periodic boundary condition.** The relative entropy of `μ` with
respect to `°γ^Φ_Λ` on the cylinder σ-algebra `𝓕_Λ` is
`𝓗_Λ(μ | °γ^Φ_Λ) = −𝓗_Λ(μ) + μ(°H^Φ_Λ) + log °Z^Φ_Λ`. -/
theorem relativeEntropyIn_periodicBoundaryGibbs_eq (hπ : IsTorusReduction G Λ π)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] :
    ((relativeEntropyIn (Λ : Set S) μ (Φ.periodicBoundaryGibbs ν π Λ) : ℝ≥0∞) : EReal)
      = -entropyIn ν (Λ : Set S) μ
        + ((((∫ σ, Φ.periodicBoundaryHamiltonian π Λ σ ∂μ) + Φ.logPeriodicBoundaryZ ν π Λ : ℝ)) :
            EReal) := by
  have hgm := measurable_cylinderEvents_periodicBoundaryDensity (Φ := Φ) ν hπ
  have hden := trim_periodicBoundaryGibbs_eq_withDensity (Φ := Φ) ν hπ
  have hprob : IsProbabilityMeasure
      (((Measure.infinitePi fun _ : S ↦ ν).trim
        (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))).withDensity
          (Φ.periodicBoundaryDensity ν π Λ)) := by
    rw [← hden]; infer_instance
  have hsm : StronglyMeasurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      fun σ ↦ Real.log (Φ.periodicBoundaryDensity ν π Λ σ).toReal :=
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hgm)).stronglyMeasurable
  have hint : Integrable (fun σ ↦ Real.log (Φ.periodicBoundaryDensity ν π Λ σ).toReal)
      (μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S)))) :=
    Integrable.mono' (integrable_const (Φ.hamiltonianBound Λ + |Φ.logPeriodicBoundaryZ ν π Λ|))
      hsm.aestronglyMeasurable
      (.of_forall fun σ ↦ by
        simpa only [Real.norm_eq_abs] using abs_log_toReal_periodicBoundaryDensity_le ν π Λ σ)
  have key := klDiv_withDensity_add_integral_log
    (μ := μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))))
    (lam := (Measure.infinitePi fun _ : S ↦ ν).trim cylinderEvents_le_pi)
    hgm (.of_forall fun σ ↦ periodicBoundaryDensity_ne_zero ν π Λ σ)
    (.of_forall fun σ ↦ periodicBoundaryDensity_ne_top ν π Λ σ) hprob hint
  rw [← hden] at key
  have hHint : Integrable (Φ.periodicBoundaryHamiltonian π Λ) μ :=
    Integrable.of_bound (measurable_periodicBoundaryHamiltonian hπ).aestronglyMeasurable _
      (.of_forall fun σ ↦ by
        rw [Real.norm_eq_abs]; exact abs_periodicBoundaryHamiltonian_le π Λ σ)
  have hI : ∫ σ, Real.log (Φ.periodicBoundaryDensity ν π Λ σ).toReal
      ∂(μ.trim (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))))
      = -((∫ σ, Φ.periodicBoundaryHamiltonian π Λ σ ∂μ) + Φ.logPeriodicBoundaryZ ν π Λ) := by
    rw [← integral_trim _ hsm]
    have hlog : ∀ σ : S → E, Real.log (Φ.periodicBoundaryDensity ν π Λ σ).toReal
        = -(Φ.periodicBoundaryHamiltonian π Λ σ + Φ.logPeriodicBoundaryZ ν π Λ) := fun σ ↦ by
      rw [log_toReal_periodicBoundaryDensity]; ring
    simp only [hlog]
    rw [integral_neg, integral_add hHint (integrable_const _), integral_const]
    simp
  rw [hI] at key
  rw [entropyIn, neg_neg, ← key, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero,
    add_zero]

/-- **Step 1 of Georgii's proof of the upper bound (15.46), for the periodic boundary condition.**
For a `𝓕_Λ`-event `A` of positive `°γ^Φ_Λ`-probability and the conditional distribution
`°γ^A_Λ = °γ^Φ_Λ(· | A)`,
`−log °γ^Φ_Λ(A) = 𝓗_Λ(°γ^A_Λ | λ^S) + °γ^A_Λ(°H^Φ_Λ) + log °Z^Φ_Λ`. -/
theorem neg_log_periodicBoundaryGibbs_eq (hπ : IsTorusReduction G Λ π) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hpos : Φ.periodicBoundaryGibbs ν π Λ A ≠ 0) :
    ((ENNReal.ofReal (-Real.log ((Φ.periodicBoundaryGibbs ν π Λ).real A)) : ℝ≥0∞) : EReal)
      = ((relativeEntropyIn (Λ : Set S) ((Φ.periodicBoundaryGibbs ν π Λ)[|A])
            (Measure.infinitePi fun _ : S ↦ ν) : ℝ≥0∞) : EReal)
        + (((∫ σ, Φ.periodicBoundaryHamiltonian π Λ σ ∂((Φ.periodicBoundaryGibbs ν π Λ)[|A]))
            + Φ.logPeriodicBoundaryZ ν π Λ : ℝ) : EReal) := by
  set γ := Φ.periodicBoundaryGibbs ν π Λ with hγdef
  have hκ : IsProbabilityMeasure (γ[|A]) := cond_isProbabilityMeasure hpos
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  have hcond : relativeEntropyIn (Λ : Set S) (γ[|A]) γ
      = ENNReal.ofReal (-Real.log (γ.real A)) := klDiv_trim_cond_self hle hA hpos
  have h1534 := relativeEntropyIn_periodicBoundaryGibbs_eq (Φ := Φ) ν hπ (μ := γ[|A])
  rw [hcond] at h1534
  rw [h1534, entropyIn, neg_neg]

/-! ### `°Z^Φ_Λ` against `Z^Φ_Λ(ω)`: Georgii (15.31) for the periodic boundary condition -/

omit [AddCommGroup S] in
/-- `Z^Φ_Λ(ω)` as an integral against the a priori product measure `λ^S`. -/
lemma premodifierZ_boltzmannFactor_eq_lintegral_infinitePi (Λ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω
      = ∫⁻ y, ENNReal.ofReal (Real.exp (-Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ y i)))
          ∂(Measure.infinitePi fun _ : S ↦ ν) := by
  change ∫⁻ x, Φ.boltzmannFactor 1 Λ x ∂(Specification.isssd (S := S) (E := E) ν Λ ω) = _
  rw [Specification.isssd_eq_map_juxt_restrict ν Λ ω,
    lintegral_map (measurable_boltzmannFactor (Φ := Φ) 1 Λ)
      ((measurable_cylinderEvents_juxt_restrict (Λ : Set S) ω).mono cylinderEvents_le_pi le_rfl)]
  simp [boltzmannFactor]

/-- **Georgii (15.25) for the partition functions**: `°Z^Φ_Λ ≤ e^{3 r(Λ, Φ)} Z^Φ_Λ(ω)` and
`Z^Φ_Λ(ω) ≤ e^{3 r(Λ, Φ)} °Z^Φ_Λ`, with `r(Λ, Φ) = ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`; hence
`|log °Z^Φ_Λ − log Z^Φ_Λ(ω)| ≤ 3 r(Λ, Φ)` for every boundary condition `ω`. -/
theorem abs_logPeriodicBoundaryZ_sub_logZ_le (hΦ : Φ.IsShiftInvariant)
    (hπ : IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) (ω : S → E) :
    |Φ.logPeriodicBoundaryZ ν π Λ - Φ.logZ ν Λ ω| ≤ 3 * Φ.tail Λ Λ := by
  set t : ℝ := 3 * Φ.tail Λ Λ with ht
  have hZpos := toReal_premodifierZ_boltzmannFactor_pos ν (Φ := Φ) 1 Λ ω
  have hZtop := premodifierZ_boltzmannFactor_ne_top ν (Φ := Φ) 1 Λ ω
  have hoZpos := toReal_periodicBoundaryZ_pos ν (Φ := Φ) π Λ
  have hoZtop := periodicBoundaryZ_ne_top ν (Φ := Φ) π Λ
  have hpt : ∀ y, |Φ.periodicBoundaryHamiltonian π Λ y
      - Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ y i)| ≤ t := fun y ↦
    abs_periodicBoundaryHamiltonian_sub_hamiltonian_juxt_le hΦ hπ hΛ ω y
  -- the two comparisons of the partition functions
  have h1 : Φ.periodicBoundaryZ ν π Λ ≤ ENNReal.ofReal (Real.exp t)
      * Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω := by
    rw [premodifierZ_boltzmannFactor_eq_lintegral_infinitePi, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top, periodicBoundaryZ]
    refine lintegral_mono fun y ↦ ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hpt y)).1]))
  have h2 : Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω
      ≤ ENNReal.ofReal (Real.exp t) * Φ.periodicBoundaryZ ν π Λ := by
    rw [premodifierZ_boltzmannFactor_eq_lintegral_infinitePi, periodicBoundaryZ,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y ↦ ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hpt y)).2]))
  have h1' : (Φ.periodicBoundaryZ ν π Λ).toReal ≤ Real.exp t
      * (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hZtop) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  have h2' : (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω).toReal
      ≤ Real.exp t * (Φ.periodicBoundaryZ ν π Λ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hoZtop) h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  rw [abs_le, logPeriodicBoundaryZ, logZ]
  constructor
  · have := Real.log_le_log hZpos h2'
    rw [Real.log_mul (Real.exp_ne_zero _) hoZpos.ne', Real.log_exp] at this
    linarith
  · have := Real.log_le_log hoZpos h1'
    rw [Real.log_mul (Real.exp_ne_zero _) hZpos.ne', Real.log_exp] at this
    linarith

end Gibbs

/-! ### Georgii (15.31) for the periodic boundary condition on `ℤ^d` -/

section Pressure

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {Φ : Potential (ι → ℤ) E} [IsPotential Φ] [IsAbsolutelySummable Φ]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii Theorem (15.30)(a) / (15.31) for the periodic boundary condition.** For a
shift-invariant `Φ ∈ ℬ` and boxes `Λ_j` all of whose sides tend to infinity, with torus
reductions `π_j`, `|Λ_j|⁻¹ log °Z^Φ_{Λ_j} → P(Φ)`. -/
theorem tendsto_logPeriodicBoundaryZ_div_card (hΦ : Φ.IsShiftInvariant) {κ : Type*}
    {l : Filter κ} {m n : κ → ι → ℤ} (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop)
    {G : κ → AddSubgroup (ι → ℤ)} {π : κ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ j, IsTorusReduction (G j) (Finset.Icc (m j) (n j)) (π j)) :
    Tendsto (fun j ↦ Φ.logPeriodicBoundaryZ ν (π j) (Finset.Icc (m j) (n j))
      / #(Finset.Icc (m j) (n j))) l (𝓝 (Φ.pressure ν)) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  obtain ⟨ω₀⟩ := ‹Nonempty E›
  have hZ := tendsto_logZ_div_card_pressure ν hΦ h fun _ ↦ fun _ ↦ ω₀
  have ht : Tendsto (fun j ↦ 3 * Φ.tail (Finset.Icc (m j) (n j)) (Finset.Icc (m j) (n j))
      / #(Finset.Icc (m j) (n j))) l (𝓝 0) := by
    simpa [mul_div_assoc] using (tendsto_tail_div_card hΦ h).const_mul 3
  have hdiff : Tendsto (fun j ↦ Φ.logPeriodicBoundaryZ ν (π j) (Finset.Icc (m j) (n j))
      / #(Finset.Icc (m j) (n j))
      - Φ.logZ ν (Finset.Icc (m j) (n j)) (fun _ ↦ ω₀) / #(Finset.Icc (m j) (n j))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_le_of_tendsto_sub h] with j hj
    have hne : (Finset.Icc (m j) (n j)).Nonempty := Finset.nonempty_Icc.2 hj
    have hj' : (0 : ℝ) < #(Finset.Icc (m j) (n j)) := by exact_mod_cast hne.card_pos
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hj']
    exact div_le_div_of_nonneg_right
      (abs_logPeriodicBoundaryZ_sub_logZ_le ν hΦ (hπ j) hne _) hj'.le
  simpa using hdiff.add hZ

end Pressure

/-! ### Toroidal invariance of `°γ^Φ_Λ` -/

section Toroidal

variable {S E : Type*} [Countable S] [AddCommGroup S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]
  {G : AddSubgroup S} {Λ : Finset S} {π : S → S}

/-- **Georgii, proof of (15.58).** `°H^Φ_Λ` is invariant under the toroidal shifts. -/
theorem periodicBoundaryHamiltonian_periodicTranslate (hΦ : Φ.IsShiftInvariant)
    (hπ : IsTorusReduction G Λ π) (j : S) (ω : S → E) :
    Φ.periodicBoundaryHamiltonian π Λ (periodicTranslate E π j ω)
      = Φ.periodicBoundaryHamiltonian π Λ ω := by
  rw [periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ,
    periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ,
    periodicEmpiricalField_periodicTranslate hπ]

/-- **Georgii, proof of (15.58).** `°γ^Φ_Λ` is invariant under the toroidal shifts
`θ°_j : ω ↦ θ_{-j} ω^∘_Λ` on the events of the volume `Λ`: `°γ^Φ_Λ(θ°_j ∈ A) = °γ^Φ_Λ(A)` for
`A ∈ 𝓕_Λ`, because `°H^Φ_Λ ∘ θ°_j = °H^Φ_Λ` and `λ^S` is invariant on `𝓕_Λ`. -/
theorem periodicBoundaryGibbs_preimage_periodicTranslate (hΦ : Φ.IsShiftInvariant)
    (hπ : IsTorusReduction G Λ π) (j : S) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    Φ.periodicBoundaryGibbs ν π Λ (periodicTranslate E π j ⁻¹' A)
      = Φ.periodicBoundaryGibbs ν π Λ A := by
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  have hTm := measurable_cylinderEvents_periodicTranslate (E := E) hπ j
  have hAm : MeasurableSet A := hle _ hA
  have hTA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)]
      (periodicTranslate E π j ⁻¹' A) :=
    measurableSet_cylinderEvents_preimage_periodicTranslate hπ j hA
  set ρ := Φ.periodicBoundaryDensity ν π Λ with hρ
  have hρm := measurable_cylinderEvents_periodicBoundaryDensity (Φ := Φ) ν hπ
  have hρT : ∀ ω, ρ (periodicTranslate E π j ω) = ρ ω := fun ω ↦ by
    simp only [hρ, periodicBoundaryDensity, periodicBoundaryHamiltonian_periodicTranslate hΦ hπ]
  -- the a priori measure is invariant on `𝓕_Λ`, hence so is every `𝓕_Λ`-integral
  have hlam : ∀ f : (S → E) → ℝ≥0∞, Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] f →
      ∫⁻ ω, f (periodicTranslate E π j ω) ∂(Measure.infinitePi fun _ : S ↦ ν)
        = ∫⁻ ω, f ω ∂(Measure.infinitePi fun _ : S ↦ ν) := by
    intro f hf
    have htrim : ((Measure.infinitePi fun _ : S ↦ ν).map (periodicTranslate E π j)).trim hle
        = (Measure.infinitePi fun _ : S ↦ ν).trim hle := by
      refine @Measure.ext _ (cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)) _ _ fun B hB ↦ ?_
      rw [trim_measurableSet_eq hle hB, trim_measurableSet_eq hle hB,
        Measure.map_apply (hTm.mono hle le_rfl) (hle _ hB),
        infinitePi_preimage_periodicTranslate hπ j ν hB]
    rw [← lintegral_map (hf.mono hle le_rfl) (hTm.mono hle le_rfl), ← lintegral_trim hle hf,
      htrim, lintegral_trim hle hf]
  rw [periodicBoundaryGibbs, withDensity_apply _ (hle _ hTA), withDensity_apply _ hAm,
    ← lintegral_indicator (hle _ hTA), ← lintegral_indicator hAm]
  have hind : ∀ ω, (periodicTranslate E π j ⁻¹' A).indicator ρ ω
      = A.indicator ρ (periodicTranslate E π j ω) := fun ω ↦ by
    by_cases hω : periodicTranslate E π j ω ∈ A
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (show ω ∈ _ ⁻¹' A from hω), hρT]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ _ ⁻¹' A from hω)]
  rw [show (periodicTranslate E π j ⁻¹' A).indicator ρ
      = fun ω ↦ A.indicator ρ (periodicTranslate E π j ω) from funext hind]
  exact hlam _ (hρm.indicator hA)

/-- The conditional distribution `°γ^Φ_Λ(· | A)` of a toroidally invariant `𝓕_Λ`-event `A` is
again toroidally invariant on the events of the volume `Λ`. -/
theorem periodicBoundaryGibbs_cond_preimage_periodicTranslate (hΦ : Φ.IsShiftInvariant)
    (hπ : IsTorusReduction G Λ π) (j : S) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hAinv : periodicTranslate E π j ⁻¹' A = A) {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] B) :
    ((Φ.periodicBoundaryGibbs ν π Λ)[|A]) (periodicTranslate E π j ⁻¹' B)
      = ((Φ.periodicBoundaryGibbs ν π Λ)[|A]) B := by
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  rw [cond_apply (hle _ hA), cond_apply (hle _ hA), ← hAinv, ← Set.preimage_inter, hAinv,
    periodicBoundaryGibbs_preimage_periodicTranslate ν hΦ hπ j (hA.inter hB)]

/-- **Georgii, last paragraph of the proof of (15.58): `σ_Λ(°γ^B_Λ °R_Λ) = °γ^B_Λ`.** The mean
periodic empirical field of the conditional distribution `°γ^B_Λ = °γ^Φ_Λ(· | A)` of a toroidally
invariant `𝓕_Λ`-event `A` agrees with `°γ^B_Λ` on every event of the volume `Λ`. -/
theorem empiricalFieldAverage_periodicBoundaryGibbs_cond_apply (hΦ : Φ.IsShiftInvariant)
    (hπ : IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hAinv : ∀ j, periodicTranslate E π j ⁻¹' A = A) {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] B) :
    empiricalFieldAverage E π Λ ((Φ.periodicBoundaryGibbs ν π Λ)[|A]) B
      = ((Φ.periodicBoundaryGibbs ν π Λ)[|A]) B := by
  have hle := cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (Λ : Set S))
  rw [empiricalFieldAverage_apply _ _ _ (hle _ hB)]
  simp only [periodicBoundaryGibbs_cond_preimage_periodicTranslate ν hΦ hπ _ hA (hAinv _) hB,
    Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hΛ.card_pos.ne') (by simp), one_mul]

omit [Countable S] in
/-- The event `{°R_Λ ∈ C}` is invariant under the toroidal shifts. -/
theorem preimage_periodicTranslate_setOf_periodicEmpiricalFieldL_mem
    (hπ : IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) (j : S)
    (C : Set (WithLocalConvergence S E)) :
    periodicTranslate E π j ⁻¹' {σ | periodicEmpiricalFieldL π hΛ σ ∈ C}
      = {σ | periodicEmpiricalFieldL π hΛ σ ∈ C} := by
  ext σ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have h : periodicEmpiricalFieldL π hΛ (periodicTranslate E π j σ)
      = periodicEmpiricalFieldL π hΛ σ := by
    unfold periodicEmpiricalFieldL
    congr 1
    exact Subtype.ext (periodicEmpiricalField_periodicTranslate hπ j σ)
  rw [h]

end Toroidal

end Potential

/-! ### Georgii (15.47) for the periodic boundary condition -/

namespace MeasureTheory.GibbsMeasure

section LowerBound

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E]

/-- The `EReal` bookkeeping of (15.47): `log e^{|Λ| r} / |Λ| = r`. -/
private lemma coe_mul_div_natCast_eq (a : ℕ) (ha : a ≠ 0) (z : ℝ) :
    (((a : ℝ) * z : ℝ) : EReal) / ((a : ℕ) : EReal) = (z : EReal) := by
  rw [← EReal.coe_natCast, ← EReal.coe_div]
  congr 1
  field_simp

private lemma neg_add_div_expand (c x S k : ℝ) (hc : c ≠ 0) :
    -x - S / c + k = (-(c * x) - S + c * k) / c := by
  field_simp

/-- **Georgii (15.55) for the periodic boundary condition.** For `ν ∈ C°` with `𝒜(ν|Φ) < ∞` and
every `r < −𝒜(ν|Φ)`, the Gibbs distributions `°γ^Φ_{Λ_n}` with periodic boundary conditions
eventually give the event `{°R_{Λ_n} ∈ C}` probability at least `e^{|Λ_n| r}`.

The proof is the one for the configurational boundary conditions
(`eventually_exists_ofReal_exp_le_gibbsSpecification`) without the energy error (15.25): on the
window `B` of `eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem` the
periodic Hamiltonian is *exactly* `|Λ_n| ⟨°R_{Λ_n}, Φ⟩ < |Λ_n| (⟨ν, Φ⟩ + ε)`, so
`°γ^Φ_{Λ_n}(B) ≥ e^{−|Λ_n| (⟨ν, Φ⟩ + ε) − log °Z^Φ_{Λ_n}} λ^S(B)`, and
`|Λ_n|⁻¹ log °Z^Φ_{Λ_n} → P(Φ)`. -/
theorem eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_periodicEmpiricalField_mem
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    {C : Set (WithLocalConvergence (Fin d → ℤ) E)}
    {ν : Measure ((Fin d → ℤ) → E)} (hν : ν ∈ invariantFields (shiftGroup (Fin d → ℤ) E))
    (hνC : C ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E]
      (WithSetwiseTopology.ofMeasure ⟨ν, hν.1⟩ : WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty)
    {r : ℝ} (hr : (r : EReal) < -Φ.specificRelativeEntropy lam ν) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ) * r))
        ≤ Φ.periodicBoundaryGibbs lam (π n) (Finset.Icc (m n) fun k ↦ m n k + s n)
            {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C} := by
  classical
  have hprobν : IsProbabilityMeasure ν := hν.1
  -- ### Step 0. The excess free energy of `ν` is a finite number `A`, and `r < -A`.
  have hAtop : Φ.specificRelativeEntropy lam ν ≠ ⊤ := by
    intro h; rw [h] at hr; simp at hr
  have hκtop : specificEntropy lam ν ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (specificEntropy_nonpos lam (μ := ν))
  have hκbot : specificEntropy lam ν ≠ ⊥ := by
    intro h
    exact hAtop (by rw [Potential.specificRelativeEntropy, h]; simp)
  set k₀ : ℝ := -(specificEntropy lam ν).toReal with hk₀def
  have hκeq : specificEntropy lam ν = ((-k₀ : ℝ) : EReal) := by
    rw [hk₀def, neg_neg, EReal.coe_toReal hκtop hκbot]
  set A : ℝ := Φ.pressure lam + Φ.specificEnergy ν + k₀ with hAdef
  have hAeq : Φ.specificRelativeEntropy lam ν = ((A : ℝ) : EReal) := by
    rw [Potential.specificRelativeEntropy, hκeq, ← EReal.coe_sub, hAdef]
    congr 1
    ring
  have hrA : r < -A := by
    rw [hAeq, ← EReal.coe_neg] at hr
    exact_mod_cast hr
  set ε : ℝ := (-A - r) / 3 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  -- ### Step 1. The window.
  have hwin := eventually_exists_measurableSet_subset_setOf_periodicEmpiricalField_mem lam
    (Φ := Φ) hν hνC hs hπ hne hκbot hεpos
  -- ### Step 2. The finite-volume chain of inequalities.
  have hkey : ∀ n (B : Set ((Fin d → ℤ) → E)),
      MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] B →
      (∀ y ∈ B, Φ.specificEnergy (periodicEmpiricalField E (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) y) < Φ.specificEnergy ν + ε) →
      ENNReal.ofReal (Real.exp ((#(Finset.Icc (m n) fun k ↦ m n k + s n) : ℝ)
          * ((specificEntropy lam ν).toReal - ε)))
        ≤ (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) B →
      ENNReal.ofReal (Real.exp
          (-((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (Φ.specificEnergy ν + ε))
            - Φ.logPeriodicBoundaryZ lam (π n) (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
            + (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (-k₀ - ε)))
        ≤ Φ.periodicBoundaryGibbs lam (π n) (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) B := by
    intro n B hBmeas hBenergy hBlam
    set Λn : Finset (Fin d → ℤ) := Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ) with hΛn
    set bn : ℝ := (#Λn : ℝ) * (Φ.specificEnergy ν + ε) with hbn
    have hEnergy : ∀ y ∈ B, Φ.periodicBoundaryHamiltonian (π n) Λn y ≤ bn := by
      intro y hy
      rw [Potential.periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ]
      exact mul_le_mul_of_nonneg_left (hBenergy y hy).le (Nat.cast_nonneg _)
    have hA1 := Potential.le_periodicBoundaryGibbs_apply lam (π n) Λn
      (cylinderEvents_le_pi _ hBmeas) hEnergy
    have hexp : Real.exp (-bn - Φ.logPeriodicBoundaryZ lam (π n) Λn + (#Λn : ℝ) * (-k₀ - ε))
        = Real.exp (-bn - Φ.logPeriodicBoundaryZ lam (π n) Λn)
          * Real.exp ((#Λn : ℝ) * (-k₀ - ε)) := by
      rw [Real.exp_add]
    have hk₀ : (specificEntropy lam ν).toReal - ε = -k₀ - ε := by rw [hk₀def, neg_neg]
    calc ENNReal.ofReal (Real.exp (-bn - Φ.logPeriodicBoundaryZ lam (π n) Λn
            + (#Λn : ℝ) * (-k₀ - ε)))
        = ENNReal.ofReal (Real.exp (-bn - Φ.logPeriodicBoundaryZ lam (π n) Λn))
            * ENNReal.ofReal (Real.exp ((#Λn : ℝ) * (-k₀ - ε))) := by
          rw [hexp, ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (-bn - Φ.logPeriodicBoundaryZ lam (π n) Λn))
            * (Measure.infinitePi fun _ : Fin d → ℤ ↦ lam) B := by
          gcongr
          rw [← hk₀]
          exact hBlam
      _ ≤ Φ.periodicBoundaryGibbs lam (π n) Λn B := hA1
  -- ### Step 3. The exponent is eventually at least `|Λ_n| r`.
  have hside : ∀ k, Tendsto (fun n ↦ (fun k' ↦ m n k' + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have hcardpos : ∀ n, (0 : ℝ) < (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) := fun n ↦ by
    exact_mod_cast (hne n).card_pos
  have hZ : Tendsto (fun n ↦ Φ.logPeriodicBoundaryZ lam (π n)
      (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 (Φ.pressure lam)) :=
    Potential.tendsto_logPeriodicBoundaryZ_div_card lam hΦ hside hπ
  set L : ℝ := -(Φ.specificEnergy ν + ε) - Φ.pressure lam + (-k₀ - ε) with hLdef
  have hFlim : Tendsto (fun n ↦
      (-((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (Φ.specificEnergy ν + ε))
        - Φ.logPeriodicBoundaryZ lam (π n) (Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))
        + (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * (-k₀ - ε))
      / (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ)) atTop (𝓝 L) := by
    have h := ((tendsto_const_nhds (x := -(Φ.specificEnergy ν + ε)) (f := atTop (α := ℕ))).sub
      hZ).add (tendsto_const_nhds (x := -k₀ - ε))
    refine h.congr fun n ↦ ?_
    exact neg_add_div_expand _ _ _ _ (hcardpos n).ne'
  have hrL : r < L := by
    rw [hLdef, hAdef] at *
    linarith [hεdef]
  filter_upwards [hwin, hFlim.eventually (lt_mem_nhds hrL)] with n hn hFn
  obtain ⟨B, hBmeas, hBC, hBenergy, hBlam⟩ := hn
  refine le_trans (le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    (hkey n B hBmeas hBenergy hBlam)) (measure_mono hBC)
  have hcardn := hcardpos n
  rw [lt_div_iff₀ hcardn] at hFn
  nlinarith [hFn]

/-- **Georgii (15.47) for the periodic boundary condition.** For `Φ ∈ ℬ_Θ` and any set `C` of
random fields,
`liminf |Λ|⁻¹ log °γ^Φ_Λ(°R_Λ ∈ C) ≥ − inf_{ν ∈ C°} 𝒜(ν|Φ)`
along any sequence of cubes of `ℤ^d` whose side tends to infinity, with arbitrary torus
reductions; `C°` is Georgii's interior of `C` *in* `𝓟_Θ`
(`MeasureTheory.GibbsMeasure.invariantInterior`). Over an arbitrary measurable state space. -/
theorem neg_iInf_specificRelativeEntropy_le_liminf_log_periodicBoundaryGibbs
    (lam : Measure E) [IsProbabilityMeasure lam]
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant)
    (C : Set (WithLocalConvergence (Fin d → ℤ) E))
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop)
    {G' : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G' n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n).Nonempty) :
    -(⨅ ρ ∈ invariantInterior (Fin d → ℤ) E C,
        Φ.specificRelativeEntropy lam (ρ.toMeasure : Measure ((Fin d → ℤ) → E)))
      ≤ liminf (fun n ↦ ENNReal.log (Φ.periodicBoundaryGibbs lam (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {η | periodicEmpiricalFieldL (π n) (hne n) η ∈ C})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n) : EReal)) atTop := by
  rw [EReal.neg_le]
  refine le_iInf₂ fun ρ hρ ↦ ?_
  rw [EReal.neg_le]
  refine EReal.ge_of_forall_gt_iff_ge.1 fun z hz ↦ ?_
  have hev := eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_periodicEmpiricalField_mem
    lam hΦ hρ.1 hρ.2 hs hπ hne hz
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  have hcard : (#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ))) ≠ 0 := (hne n).card_pos.ne'
  have hlog : ENNReal.log (ENNReal.ofReal (Real.exp
      ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
      = (((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z : ℝ) : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  calc (z : EReal)
      = ENNReal.log (ENNReal.ofReal (Real.exp
          ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℝ) * z)))
        / ((#(Finset.Icc (m n) fun k ↦ m n k + (s n : ℤ)) : ℕ) : EReal) := by
        rw [hlog, coe_mul_div_natCast_eq _ hcard]
    _ ≤ _ := by
        refine EReal.div_le_div_right_of_nonneg (Nat.cast_nonneg' _) ?_
        exact ENNReal.log_le_log hn

end LowerBound

/-! ### Georgii (15.46) for the periodic boundary condition -/

section UpperBound

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Steps 1 and 2 of Georgii's proof of the upper bound (15.46) for the periodic boundary
condition**, with no error term: for a box `Λ = ∏_k [a_k, a_k + s_k]` with a torus reduction `π`
and a `𝓕_Λ`-event `A` of positive `°γ^Φ_Λ`-probability, the excess free energy of the randomly
shifted independent-block field `°γ̄^A_Λ` built from `°γ^A_Λ = °γ^Φ_Λ(· | A)` obeys

`𝓀(°γ̄^A_Λ|Φ) ≤ −|Λ|⁻¹ log °γ^Φ_Λ(A) + (P(Φ) − |Λ|⁻¹ log °Z^Φ_Λ)
      + (⟨°γ̄^A_Λ, Φ⟩ − ⟨°γ^A_Λ °R_Λ, Φ⟩)`.

This is Step 1 (`Potential.neg_log_periodicBoundaryGibbs_eq`) together with the *exact*
identity `°γ^A_Λ(°H^Φ_Λ) = |Λ| ⟨°γ^A_Λ °R_Λ, Φ⟩` of Remark (15.43)(3), which is why Georgii says
the proof is simpler for `°γ^Φ_Λ`: the energy errors (15.25) do not appear. -/
theorem specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le
    {Φ : Potential (ι → ℤ) E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant) (a : ι → ℤ) (s : ι → ℕ)
    {G : AddSubgroup (ι → ℤ)} {π : (ι → ℤ) → (ι → ℤ)}
    (hπ : Potential.IsTorusReduction G (Finset.Icc a fun k ↦ a k + s k) π)
    {A : Set ((ι → ℤ) → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
      ((Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : Set (ι → ℤ))] A)
    (hpos : Φ.periodicBoundaryGibbs ν π (Finset.Icc a fun k ↦ a k + s k) A ≠ 0) :
    Φ.specificRelativeEntropy ν (tileAverage (isComplement_Icc a s)
        (((Φ.periodicBoundaryGibbs ν π (Finset.Icc a fun k ↦ a k + s k))[|A]).map
          (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
      ≤ ((-Real.log ((Φ.periodicBoundaryGibbs ν π (Finset.Icc a fun k ↦ a k + s k)).real A)
            / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ)
          + (Φ.pressure ν - Φ.logPeriodicBoundaryZ ν π (Finset.Icc a fun k ↦ a k + s k)
              / (#(Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)) : ℝ))
          + (Φ.specificEnergy (tileAverage (isComplement_Icc a s)
                (((Φ.periodicBoundaryGibbs ν π (Finset.Icc a fun k ↦ a k + s k))[|A]).map
                  (Finset.Icc a fun k ↦ a k + s k : Finset (ι → ℤ)).restrict))
              - Φ.specificEnergy (empiricalFieldAverage E π (Finset.Icc a fun k ↦ a k + s k)
                  ((Φ.periodicBoundaryGibbs ν π (Finset.Icc a fun k ↦ a k + s k))[|A])))
          : ℝ) : EReal) := by
  set Λ : Finset (ι → ℤ) := Finset.Icc a fun k ↦ a k + s k with hΛdef
  set γ := Φ.periodicBoundaryGibbs ν π Λ with hγdef
  have hκ : IsProbabilityMeasure (γ[|A]) := cond_isProbabilityMeasure hpos
  have hstep1 := Potential.neg_log_periodicBoundaryGibbs_eq (Φ := Φ) ν hπ hA hpos
  have hApos : 0 < γ.real A := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  have hq0 : 0 ≤ -Real.log (γ.real A) := by
    rw [neg_nonneg]
    exact Real.log_nonpos hApos.le measureReal_le_one
  rw [EReal.coe_ennreal_ofReal, max_eq_left hq0] at hstep1
  have hRtop : relativeEntropyIn (Λ : Set (ι → ℤ)) (γ[|A])
      (Measure.infinitePi fun _ : ι → ℤ ↦ ν) ≠ ⊤ := by
    intro h
    rw [h, EReal.coe_ennreal_top, EReal.top_add_coe] at hstep1
    exact EReal.coe_ne_top _ hstep1
  rw [← EReal.coe_ennreal_toReal hRtop, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hstep1
  -- the exact energy identity of Remark (15.43)(3)
  have henergy : ∫ σ, Φ.periodicBoundaryHamiltonian π Λ σ ∂(γ[|A])
      = (#Λ : ℝ) * Φ.specificEnergy (empiricalFieldAverage E π Λ (γ[|A])) := by
    rw [specificEnergy_empiricalFieldAverage hΦ π Λ, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun σ ↦
      Potential.periodicBoundaryHamiltonian_eq_card_mul_specificEnergy hΦ π Λ σ)
  refine specificRelativeEntropy_tileAverage_le_of_relativeEntropyIn_add_le ν a s π _ hRtop
    (q := -Real.log (γ.real A)) (L := Φ.logPeriodicBoundaryZ ν π Λ) ?_
  rw [← henergy]
  linarith [hstep1]

variable [Finite E] [MeasurableSingletonClass E]

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Steps 2 and 3 of Georgii's proof of the upper bound (15.46) for the periodic boundary
condition: the cluster point, over a standard Borel state space.** If
`°γ^Φ_{Λ_n}(°R_{Λ_n} ∈ C) > e^{−c|Λ_n|}` for all `n`, there is a shift-invariant random field `μ`
in Georgii's `cx̄ C` with `𝓀(μ|Φ) ≤ c`.

As in the configurational case
(`exists_mem_closedConvexHull_specificRelativeEntropy_le_of_measurableSet`),
the finite-volume bound confines the block fields to one compact sublevel set of the excess free
energy (Georgii's Proposition (15.14)), and the cluster point is a limit along a finer filter. The
hypothesis `hAmeas` is Georgii's `C ∈ 𝓔(𝓟_Θ)`. -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundary_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    (hlt : ∀ n, ENNReal.ofReal (Real.exp (-(c *
          #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))))
        < (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    ∃ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) := by
  classical
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  have hcardpos : ∀ n, (0 : ℝ) < #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) :=
    fun n ↦ by exact_mod_cast (hne n).card_pos
  have hpos : ∀ n, (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n)
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} ≠ 0 := fun n ↦
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos _)) (hlt n).le).ne'
  set κ : ℕ → Measure ((ι → ℤ) → E) := fun n ↦
    ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n))[|
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}] with hκdef
  have hκprob : ∀ n, IsProbabilityMeasure (κ n) := fun n ↦ cond_isProbabilityMeasure (hpos n)
  have hcond : ∀ n, κ n {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}ᶜ = 0 := by
    intro n
    rw [hκdef]
    have hm := cylinderEvents_le_pi (X := fun _ : ι → ℤ ↦ E)
      (Δ := ((Finset.Icc (m n) fun j ↦ m n j + s n : Finset (ι → ℤ)) : Set (ι → ℤ)))
      _ (hAmeas n)
    rw [cond_apply hm, Set.inter_compl_self, measure_empty, mul_zero]
  -- the finite-volume estimate, with the single correction term
  set e : ℕ → ℝ := fun n ↦ (Φ : Potential (ι → ℤ) E).pressure ν
      - (Φ : Potential (ι → ℤ) E).logPeriodicBoundaryZ ν (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) with hedef
  have hM : ∀ n, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
      ≤ ((c + e n + ((Φ : Potential (ι → ℤ) E).specificEnergy
            (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
              ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
          - (Φ : Potential (ι → ℤ) E).specificEnergy
            (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n))) : ℝ)
        : EReal) := by
    intro n
    have hmain := specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le ν hΦ (m n)
      (fun _ ↦ s n) (hπ n) (hAmeas n) (hpos n)
    refine hmain.trans (EReal.coe_le_coe_iff.2 ?_)
    have hq : -Real.log (((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)).real
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) ≤ c := by
      rw [div_le_iff₀ (hcardpos n)]
      have hlt' := (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos _).le
        (measure_ne_top _ _)).1 (hlt n)
      have hlog := Real.log_lt_log (Real.exp_pos _) hlt'
      rw [Real.log_exp] at hlog
      rw [measureReal_def]
      linarith
    rw [hedef]
    linarith
  -- the correction term vanishes
  have hside : ∀ k, Tendsto (fun n ↦ (fun j ↦ m n j + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have he : Tendsto e atTop (𝓝 0) := by
    have hZ := Potential.tendsto_logPeriodicBoundaryZ_div_card (Φ := (Φ : Potential (ι → ℤ) E))
      ν hΦ hside hπ
    have h := (tendsto_const_nhds (x := (Φ : Potential (ι → ℤ) E).pressure ν)).sub hZ
    simpa [hedef] using h
  -- the block fields eventually lie in one compact sublevel set of the excess free energy
  set M : ℝ := c + 1 + 2 * ((Φ : Potential (ι → ℤ) E).normAt 0).toReal with hMdef
  set K : Set (WithLocalConvergence (ι → ℤ) E) :=
    {μ' : WithLocalConvergence (ι → ℤ) E | (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (μ'.toMeasure : Measure ((ι → ℤ) → E)) ≤ (M : EReal)} with hKdef
  have hKcompact : IsCompact K :=
    Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le ν Φ M
  have hmemK : ∀ᶠ n in atTop, blockFieldL (m n) (fun _ ↦ s n) (κ n) ∈ K := by
    filter_upwards [he.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    change (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict))
      ≤ (M : EReal)
    refine (hM n).trans (EReal.coe_le_coe_iff.2 ?_)
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))) :=
      ⟨(hne n).card_pos.ne'⟩
    have h1 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (ι → ℤ) E))
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((κ n).map (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).restrict)))
    have h2 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (ι → ℤ) E))
      (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n) (κ n)))
    rw [hMdef]
    linarith [h1.2, h2.1, hn.le]
  -- a cluster point of the block fields, by compactness of that sublevel set
  obtain ⟨μ, -, hclus⟩ := hKcompact (f := Filter.map
    (fun n ↦ blockFieldL (m n) (fun _ ↦ s n) (κ n)) atTop) (Filter.le_principal_iff.2 hmemK)
  obtain ⟨l, hl, hlne, hlim⟩ := MapClusterPt.exists_le_tendsto hclus
  have hemp : Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n) (κ n)) l (𝓝 μ) :=
    (tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL hs hl hπ hne κ μ).1 hlim
  exact ⟨μ, mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto ν Φ hs hπ hne hl hlne
    κ (.of_forall hcond) (he.mono_left hl) (.of_forall hM) hemp⟩

omit [Finite E] [MeasurableSingletonClass E] in
/-- **The cluster point for the periodic boundary condition under Georgii's `C ∈ 𝓔(𝓟_Θ)`.** -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundary_of_evalEvents
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hC : MeasurableSet[evalEvents (ι → ℤ) E] C)
    (hlt : ∀ n, ENNReal.ofReal (Real.exp (-(c *
          #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))))
        < (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    ∃ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) :=
  exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundary_of_measurableSet
    ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
      (hπ n) (hne n) hC) hlt

/-- **The cluster point for the periodic boundary condition over a finite state space**, where
`{°R_Λ ∈ C}` is a cylinder event for every `C` whatsoever. -/
theorem exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundaryGibbs
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hlt : ∀ n, ENNReal.ofReal (Real.exp (-(c *
          #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)))))
        < (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    ∃ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  exact
    exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundary_of_measurableSet
      ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C) hlt

omit [Finite E] [MeasurableSingletonClass E] in
/-- **The upper bound (15.46) for the periodic boundary condition, in exponential form, with
Georgii's `cx̄ C` on the right, over a standard Borel state space.** If `c` is strictly below the
excess free energy of every shift-invariant random field in `cx̄ C`, then eventually
`°γ^Φ_Λ(°R_Λ ∈ C) ≤ e^{−c |Λ|}`. -/
theorem eventually_periodicBoundaryGibbs_setOf_mem_le_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    (hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E))) :
    ∀ᶠ n in atTop,
      (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}
        ≤ ENNReal.ofReal (Real.exp
            (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))))) := by
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_of_frequently_atTop hcon
  have hlt : ∀ j : ℕ, ENNReal.ofReal (Real.exp (-(c *
        #(Finset.Icc (m (φ j)) fun k ↦ m (φ j) k + s (φ j) : Finset (ι → ℤ)))))
      < (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π (φ j))
          (Finset.Icc (m (φ j)) fun k ↦ m (φ j) k + s (φ j))
          {σ | periodicEmpiricalFieldL (π (φ j)) (hne (φ j)) σ ∈ C} :=
    fun j ↦ not_le.1 (hφP j)
  obtain ⟨μ, hμinv, hμhull, hμle⟩ :=
    exists_mem_closedConvexHull_specificRelativeEntropy_le_periodicBoundary_of_measurableSet ν Φ
      (m := fun j ↦ m (φ j)) (s := fun j ↦ s (φ j)) (hs.comp hφ.tendsto_atTop)
      (G := fun j ↦ G (φ j)) (π := fun j ↦ π (φ j)) (fun j ↦ hπ (φ j)) (fun j ↦ hne (φ j))
      (fun j ↦ hAmeas (φ j)) hlt
  exact absurd hμle (not_le.2 (hc μ hμinv hμhull))

/-- **The upper bound (15.46) for the periodic boundary condition, in exponential form, over a
finite state space.** -/
theorem eventually_periodicBoundaryGibbs_setOf_periodicEmpiricalFieldL_mem_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)} {c : ℝ}
    (hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E))) :
    ∀ᶠ n in atTop,
      (Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}
        ≤ ENNReal.ofReal (Real.exp
            (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ))))) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  exact eventually_periodicBoundaryGibbs_setOf_mem_le_of_measurableSet ν Φ hs hπ hne
    (fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem (hπ n) (hne n) C) hc

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45) for the periodic boundary condition, the upper bound (15.46) with
`cx̄ C` on the right, over a standard Borel state space.**

`limsup_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(°R_Λ ∈ C) ≤ − inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ ∩ cx̄ C}`,

with `cx̄ C` the closed convex hull in the topology of local convergence and `hAmeas` Georgii's
`C ∈ 𝓔(𝓟_Θ)`. Steps 1 and 2 of Georgii's proof in full generality; Step 3 (his (15.54)) is what
would replace `cx̄ C` by `C̄`. -/
theorem limsup_log_periodicBoundaryGibbs_div_card_le_closedConvexHull_of_measurableSet
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C}) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ {μ : WithLocalConvergence (ι → ℤ) E |
          μ ∈ invariantRandomFields (ι → ℤ) E ∧
          evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine le_neg_of_forall_lt fun c hcm ↦ ?_
  have hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := fun μ hμ hμ' ↦
    lt_of_lt_of_le hcm (iInf₂_le μ ⟨hμ, hμ'⟩)
  have hev := eventually_periodicBoundaryGibbs_setOf_mem_le_of_measurableSet ν Φ hs hπ hne
    hAmeas hc
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  exact log_div_natCast_le_neg_of_le_ofReal_exp (hne n).card_pos.ne' hn

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45) for the periodic boundary condition with `cx̄ C` on the right,
under Georgii's hypothesis `C ∈ 𝓔(𝓟_Θ)`.** -/
theorem limsup_log_periodicBoundaryGibbs_div_card_le_closedConvexHull
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : MeasurableSet[evalEvents (ι → ℤ) E] C) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ {μ : WithLocalConvergence (ι → ℤ) E |
          μ ∈ invariantRandomFields (ι → ℤ) E ∧
          evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)},
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) :=
  limsup_log_periodicBoundaryGibbs_div_card_le_closedConvexHull_of_measurableSet ν Φ hs hπ hne
    fun n ↦ measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem_of_evalEvents
      (hπ n) (hne n) hC

omit [Finite E] [MeasurableSingletonClass E] in
/-- **Georgii Theorem (15.45) for the periodic boundary condition and a convex `C`, over a
standard Borel state space.** For a convex `C` Georgii's `cx̄ C` is the closure of `C`, so the
bound takes his own form

`limsup_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(°R_Λ ∈ C) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`

with no finiteness of the state space and no appeal to Choquet theory. -/
theorem limsup_log_periodicBoundaryGibbs_div_card_le_of_convex
    [StandardBorelSpace E] (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
        ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
    (hCconv : Convex ℝ (evalLocalEvents (ι → ℤ) E '' C)) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine (limsup_log_periodicBoundaryGibbs_div_card_le_closedConvexHull_of_measurableSet ν Φ hs
    hπ hne hAmeas).trans (EReal.neg_le_neg_iff.2 (le_iInf₂ fun μ hμ ↦ ?_))
  have hcl : evalLocalEvents (ι → ℤ) E μ ∈ closure (evalLocalEvents (ι → ℤ) E '' C) := by
    have hhull : closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C)
        = closure (evalLocalEvents (ι → ℤ) E '' C) := by
      rw [closedConvexHull_eq_closure_convexHull, hCconv.convexHull_eq]
    exact hhull ▸ hμ.2
  have hμC : μ ∈ closure C := by
    rw [isEmbedding_evalLocalEvents.closure_eq_preimage_closure_image]
    exact hcl
  exact iInf₂_le μ hμC

/-- **Georgii Theorem (15.45), the upper bound (15.46), for the Gibbs distributions with periodic
boundary conditions.** For `Φ ∈ ℬ_Θ` and a set `C ⊆ 𝓟_Θ` of shift-invariant random fields,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(°R_Λ ∈ C) ≤ − inf_{ν ∈ C̄} 𝓀(ν|Φ)`

along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to
infinity, with arbitrary torus reductions `π_n`. Over a finite state space, for the same three
reasons as `limsup_log_iSup_gibbsSpecification_div_card_le`; the finite-volume input is
`specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le`, in which the energy error of
(15.25) is absent. -/
theorem limsup_log_periodicBoundaryGibbs_div_card_le
    (Φ : Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {C : Set (WithLocalConvergence (ι → ℤ) E)}
    (hC : C ⊆ invariantRandomFields (ι → ℤ) E) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ μ ∈ closure C, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine le_neg_iInf_closure_specificRelativeEntropy_of_forall_lt ν Φ hC fun c hcm ↦ ?_
  have hc : ∀ μ : WithLocalConvergence (ι → ℤ) E,
      (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) →
      evalLocalEvents (ι → ℤ) E μ ∈ closedConvexHull ℝ (evalLocalEvents (ι → ℤ) E '' C) →
      (c : EReal) < (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := fun μ hμ hμ' ↦
    lt_of_lt_of_le hcm (iInf₂_le μ ⟨hμ, hμ'⟩)
  have hev := eventually_periodicBoundaryGibbs_setOf_periodicEmpiricalFieldL_mem_le ν Φ hs hπ
    hne hc
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev] with n hn
  exact log_div_natCast_le_neg_of_le_ofReal_exp (hne n).card_pos.ne' hn

end UpperBound

end MeasureTheory.GibbsMeasure

end

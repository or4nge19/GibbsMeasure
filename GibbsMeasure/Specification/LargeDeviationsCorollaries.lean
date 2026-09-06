/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.SelfPotential
public import Mathlib.Probability.Moments.MGFAnalytic
public import GibbsMeasure.Specification.PeriodicBoundaryGibbs

/-!
# Corollary (15.48): large deviations of the periodic Hamiltonians (Georgii §15.5)

Georgii fixes `Φ ∈ ℬ_Θ` and a vector-valued potential `Ψ = (Ψ¹, …, Ψᵏ) ∈ ℬ_Θ^k` and asks for the
probabilities that the `ℝ^k`-valued Hamiltonians `°H^Ψ_Λ = |Λ| ⟨°R_Λ, Ψ⟩` with periodic boundary
conditions take prescribed values. Corollary (15.48) is Theorem (15.45) for the Gibbs
distributions `°γ^Φ_Λ` with periodic boundary conditions
(`GibbsMeasure/Specification/PeriodicBoundaryGibbs.lean`), contracted along the continuous map
`e_Ψ : ν ↦ ⟨ν, Ψ⟩` of `GibbsMeasure/Specification/LargeDeviations.lean`.

## The contraction

The whole content of the passage from (15.46)/(15.47) to (15.48) is that the event

`{ω : |Λ|⁻¹ °H^Ψ_Λ(ω) ∈ B}` **is** the event `{ω : °R^ω_Λ ∈ C}`, `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ`,

by Remark (15.43)(3) (`Potential.inv_card_mul_periodicBoundaryHamiltonian_eq`), together with the
two inclusions Georgii names: `C̄ ⊆ e_Ψ⁻¹(B̄)` and `C° ⊇ e_Ψ⁻¹(B°)`, both from the continuity of
`e_Ψ` (`Potential.BTheta.continuous_energyVec`, Georgii (4.3)(2)) and the closedness of `𝓟_Θ`
(`MeasureTheory.GibbsMeasure.isClosed_setOf_mem_invariantFields`, Georgii (14.1)); the infima are
then regrouped by the fibres of `e_Ψ`
(`Potential.BTheta.iInf_specificRelativeEntropy_eq_iInf_ldRate`).

* `MeasureTheory.GibbsMeasure.limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le`,
  **the first inequality of (15.48)**:
  `limsup |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≤ − inf_{x ∈ B̄} J_Ψ(x|Φ)`, over a finite state
  space and for an arbitrary `B`; and
  `MeasureTheory.GibbsMeasure.limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le_of_convex`,
  the same inequality **over a standard Borel state space for a convex Borel `B`**. There the
  Borel hypothesis on `B` is Georgii's `C ∈ 𝓔(𝓟_Θ)`
  (`MeasureTheory.GibbsMeasure.measurableSet_cylinderEvents_setOf_mem_energyVecPreimage`), and
  convexity of `B` makes `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ` convex
  (`MeasureTheory.GibbsMeasure.convex_image_evalLocalEvents_energyVecPreimage`), so that
  Georgii's `cx̄ C` is `C̄` and Step 3 of the proof of (15.46) — the only step of it that is
  finite-only — is not needed.
* `MeasureTheory.GibbsMeasure.neg_iInf_ldRate_le_liminf_log_periodicBoundaryGibbs_setOf_mem`,
  **the second inequality of (15.48)**:
  `liminf |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≥ − inf_{x ∈ B°} J_Ψ(x|Φ)`.

The remaining assertions of (15.48) — that `J_Ψ(·|Φ)` is convex, has compact level sets, vanishes
exactly on `e_Ψ(𝒢_Θ(Φ))`, and is the Legendre transform (15.49) of `t ↦ P(Φ − t·Ψ)` — are
`Potential.BTheta.ldRate_smul_add_smul_le`, `Potential.BTheta.isCompact_setOf_ldRate_le`,
`Potential.BTheta.ldRate_eq_zero_iff` and `Potential.BTheta.ldRate_eq_iSup` of
`GibbsMeasure/Specification/LargeDeviations.lean`.

## Georgii Example (15.50) and the asymptotics (15.51)

The self-potential `Ψ_{i} = f(σ_i)` of a bounded measurable observable `f : E → ℝ` is
`Potential.site (fun _ ↦ f)` (`GibbsMeasure/Potential/Site.lean`); it lies in `ℬ_Θ` by
`Potential.site_const_mem_BTheta` and is packaged as `Potential.selfPotential`. Its periodic
Hamiltonian per site is Georgii's spatial mean,
`|Λ|⁻¹ °H^Ψ_Λ = M_Λ f = |Λ|⁻¹ ∑_{i ∈ Λ} f(σ_i)`
(`Potential.periodicBoundaryHamiltonian_site` and, vector-valued,
`MeasureTheory.GibbsMeasure.inv_card_mul_periodicBoundaryHamiltonian_selfPotential`), since the
periodic continuation agrees with `ω` on `Λ` itself and the energy density (15.22) of a
single-site potential is the interaction itself (`Potential.siteEnergy_site`).

* `MeasureTheory.GibbsMeasure.tendsto_log_periodicBoundaryGibbs_setOf_le_div_card`, **(15.51)**:
  for a single potential `Ψ ∈ ℬ_Θ` and `a ≥ a⁺ = ∂⁺_{−Ψ}P(Φ)` at which `J_Ψ(·|Φ)` is still finite
  slightly to the right, `|Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ≥ a) → −J_Ψ(a|Φ)`; and
  `MeasureTheory.GibbsMeasure.tendsto_log_periodicBoundaryGibbs_setOf_le_spatialMean_div_card`,
  the same for `M_Λ f`, which is Georgii's display (15.51). Both bounds of (15.48) are applied to
  the half-line `[a, ∞)` and made to meet by `Potential.BTheta.ldRate_le_ldRate_of_le` and
  `Potential.BTheta.iInf_ldRate_Ioi_eq`. The half-line is *convex* and closed, so the
  standard-Borel upper bound
  `limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le_of_convex` suffices and (15.51) holds
  over a **standard Borel** state space, Georgii's own generality.

The shape of `J_Ψ(·|Φ)` that Georgii quotes from Chapter 16 — its minimum `0` is attained exactly
on `[a⁻_{f,Φ}, a⁺_{f,Φ}]`, it is monotone on either side, and it is strictly positive beyond —
is `Potential.BTheta.ldRate_eq_zero_iff_mem_Icc`, `Potential.BTheta.ldRate_le_ldRate_of_le` and
`Potential.BTheta.ldRate_pos` of `GibbsMeasure/Specification/LargeDeviations.lean`.

## Georgii Example (15.50), last sentence: Cramér's theorem

* `Potential.pressure_site`, **the pressure of a single-site potential**: for a bounded measurable
  `g : E → ℝ`, `P(site g) = log λ(e^{−g})`. Its Hamiltonian in `Λ` is `∑_{i ∈ Λ} g(σ_i)`
  (`Potential.hamiltonian_site`), so the partition function factorises,
  `Z^{site g}_Λ(ω) = λ(e^{−g})^{|Λ|}` for *every* boundary condition
  (`Potential.premodifierZ_boltzmannFactor_site`), and the finite-volume pressures are all equal
  to `log λ(e^{−g})`; Theorem (15.30)(a) identifies the limit. In particular `P(0) = 0`
  (`Potential.pressure_zero`).
* `Potential.BTheta.pressure_smul_neg_selfPotential`: `P(−tΨ) = log λ(e^{tf}) = K_f(t)`, the
  cumulant generating function of `f` under `λ`, and
  `Potential.BTheta.rightDirDeriv_pressure_neg_selfPotential`: `∂⁺_{−Ψ}P(0) = λ(f)`, the mean —
  the left endpoint of the interval on which the rate function vanishes, at `Φ = 0`.
* `Potential.BTheta.ldRate_zero_selfPotential_eq_iSup` and, for `k = 1`,
  `Potential.BTheta.ldRate_zero_selfPotential_eq_iSup_real`, **Georgii's displayed formula**
  `J_Ψ(a|0) = sup_{t ∈ ℝ} [ta − log λ(e^{tf})]`: the Legendre formula (15.49) with `P(0) = 0` and
  `P(−tΨ) = log λ(e^{tf})`.
* `Potential.periodicBoundaryGibbs_zero`: `°γ^0_Λ = λ^S`, Georgii's `°γ^0_Λ = λ^Λ`.
* `MeasureTheory.GibbsMeasure.tendsto_log_infinitePi_setOf_le_spatialMean_div_card`,
  **Cramér's theorem**: for `a ≥ λ(f)` and a `b > a` at which the rate is finite,
  `|Λ|⁻¹ log λ^S(M_Λ f ≥ a) → − sup_t [ta − log λ(e^{tf})]`, i.e.
  `λ^S(M_Λ f ≥ a) = exp[−|Λ|(J(a) + o(1))]` — the classical large-deviation asymptotics for the
  empirical means of the i.i.d. family `(f(σ_i))_{i ∈ ℤ^d}` with common law `f(λ)`.

One assertion of Example (15.50) is *not* proved: the finiteness of `J_Ψ(·|Φ)` on
`]a⁻_f, a⁺_f[` (which Georgii also asserts without proof, and which here appears as the
hypothesis `J_Ψ(b|Φ) < ∞` for some `b > a`). See the module documentation of
`GibbsMeasure/Specification/LargeDeviations.lean`.

## Two deviations from Georgii's statement

* Georgii asks for a **Borel** `B ⊆ ℝ^k`, because his `C` must belong to `𝓔(𝓟_Θ)` for `{°R_Λ ∈ C}`
  to be an event. Over the finite state space of the first upper bound, and for the `𝓕_Λ`-events
  used in the lower bound, `{°R_Λ ∈ C}` is measurable for *every* `C`
  (`MeasureTheory.GibbsMeasure.measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`),
  so no hypothesis on `B` is needed there; `B` is an arbitrary set. Over a standard Borel state
  space Georgii's Borel hypothesis is carried, and used.
* The two inequalities are stated separately, at the generality each one has in the tree: the
  upper bound over `ι → ℤ` for a nonempty finite `ι` — over a finite state space for an arbitrary
  `B`, over a standard Borel state space for a convex Borel `B` — and the lower bound over an
  arbitrary measurable state space and over `ℤ^d`. This is the split already made for (15.46) and
  (15.47) themselves.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The event `{|Λ|⁻¹ °H^Ψ_Λ ∈ B}` as an event `{°R_Λ ∈ e_Ψ⁻¹(B)}` -/

section Contraction

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {K : Type*} [Fintype K]

omit [DecidableEq ι] [Fintype K] in
variable (ι E) in
/-- **Georgii's `C = e_Ψ⁻¹(B)`** of the proof of Corollary (15.48), intersected with `𝓟_Θ`: the
event `{°R_Λ ∈ C}` is the event `{|Λ|⁻¹ °H^Ψ_Λ ∈ B}`, by Remark (15.43)(3). -/
theorem setOf_periodicEmpiricalFieldL_mem_energyVecPreimage
    (Ψ : K → Potential.BTheta (ι → ℤ) E) (B : Set (K → ℝ))
    {G : AddSubgroup (ι → ℤ)} {Λ : Finset (ι → ℤ)} {π : (ι → ℤ) → (ι → ℤ)}
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) :
    {ω : (ι → ℤ) → E | periodicEmpiricalFieldL π hΛ ω ∈
        {ρ ∈ invariantRandomFields (ι → ℤ) E |
          Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ B}}
      = {ω : (ι → ℤ) → E | (fun j ↦ (#Λ : ℝ)⁻¹
          * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian π Λ ω) ∈ B} := by
  have : NeZero (#Λ) := ⟨hΛ.card_pos.ne'⟩
  ext ω
  have hinv : periodicEmpiricalFieldL π hΛ ω ∈ invariantRandomFields (ι → ℤ) E :=
    periodicEmpiricalField_mem_invariantFields hπ ω
  have hE : Potential.BTheta.energyVec Ψ
      ((periodicEmpiricalFieldL π hΛ ω).toMeasure : Measure ((ι → ℤ) → E))
      = fun j ↦ (#Λ : ℝ)⁻¹
        * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian π Λ ω := by
    funext j
    rw [Potential.BTheta.energyVec_apply, toMeasure_periodicEmpiricalFieldL,
      Potential.inv_card_mul_periodicBoundaryHamiltonian_eq
        (Potential.BTheta.isShiftInvariant (Ψ j)) π hΛ ω]
  simp only [Set.mem_ofPred_eq, hE]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hinv, h⟩⟩

end Contraction

/-! ### Georgii Corollary (15.48), the upper bound -/

section Upper

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  {K : Type*} [Fintype K] (ν : Measure E) [IsProbabilityMeasure ν] [Finite E]
  [MeasurableSingletonClass E]

/-- **Georgii Corollary (15.48), the first inequality.** For `Φ ∈ ℬ_Θ`, a vector-valued potential
`Ψ ∈ ℬ_Θ^k` and an arbitrary `B ⊆ ℝ^k`,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≤ − inf_{x ∈ B̄} J_Ψ(x|Φ)`,

along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to
infinity, with arbitrary torus reductions.

This is the upper bound (15.46) for `°γ^Φ_Λ`
(`limsup_log_periodicBoundaryGibbs_div_card_le`) applied to `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ`, together with
Georgii's inclusion `C̄ ⊆ e_Ψ⁻¹(B̄)`: `𝓟_Θ` is closed and `e_Ψ` is continuous, so a limit of
elements of `C` is shift invariant and has `⟨·, Ψ⟩ ∈ B̄`, whence `𝓀(·|Φ) ≥ J_Ψ(⟨·, Ψ⟩|Φ)`. -/
theorem limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le
    (Φ : Potential.BTheta (ι → ℤ) E) (Ψ : K → Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    (B : Set (K → ℝ)) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {ω | (fun j ↦ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : ℝ)⁻¹
                * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian (π n)
                    (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ x ∈ closure B, Potential.BTheta.ldRate ν Φ Ψ x := by
  classical
  set C : Set (WithLocalConvergence (ι → ℤ) E) :=
    {ρ ∈ invariantRandomFields (ι → ℤ) E |
      Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ B} with hCdef
  have hCsub : C ⊆ invariantRandomFields (ι → ℤ) E := fun _ hρ ↦ hρ.1
  have hmain := limsup_log_periodicBoundaryGibbs_div_card_le ν Φ hs hπ hne hCsub
  -- the events agree, by Remark (15.43)(3)
  have hev : ∀ n, {ω : (ι → ℤ) → E | periodicEmpiricalFieldL (π n) (hne n) ω ∈ C}
      = {ω : (ι → ℤ) → E | (fun j ↦
          (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : ℝ)⁻¹
            * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B} := fun n ↦
    setOf_periodicEmpiricalFieldL_mem_energyVecPreimage ι E Ψ B (hπ n) (hne n)
  simp only [hev] at hmain
  refine hmain.trans (EReal.neg_le_neg_iff.2 (le_iInf₂ fun ρ hρ ↦ ?_))
  -- `C̄ ⊆ e_Ψ⁻¹(B̄)`: `𝓟_Θ` is closed and `e_Ψ` is continuous
  have hinv : (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) :=
    (isClosed_setOf_mem_invariantFields (shiftGroup (ι → ℤ) E)).closure_subset_iff.2 hCsub hρ
  have hB : Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ closure B := by
    have himg := image_closure_subset_closure_image
      (Potential.BTheta.continuous_energyVec Ψ) (Set.mem_image_of_mem _ hρ)
    refine closure_mono ?_ himg
    rintro x ⟨σ, hσ, rfl⟩
    exact hσ.2
  exact (iInf₂_le _ hB).trans (Potential.BTheta.ldRate_le hinv rfl)

end Upper

/-! ### Georgii Corollary (15.48), the upper bound over a standard Borel state space -/

section UpperStandardBorel

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace E]
  {K : Type*} [Fintype K] (ν : Measure E) [IsProbabilityMeasure ν]

omit [DecidableEq ι] [Nonempty ι] [Fintype K] ν in
/-- **Georgii's `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ` lies in `𝓔(𝓟_Θ)`, in the form in which the upper bound
(15.46) consumes it.** For a Borel `B ⊆ ℝ^k` the event `{°R_Λ ∈ C}` is a cylinder event of the
box `Λ`, because it *is* the event `{|Λ|⁻¹ °H^Ψ_Λ ∈ B}` (Remark (15.43)(3),
`setOf_periodicEmpiricalFieldL_mem_energyVecPreimage`) and the periodic Hamiltonians are
`𝓕_Λ`-measurable (`Potential.measurable_cylinderEvents_periodicBoundaryHamiltonian`). This is what
makes Georgii's Borel hypothesis on `B` the right one over an infinite state space. -/
theorem measurableSet_cylinderEvents_setOf_mem_energyVecPreimage
    (Ψ : K → Potential.BTheta (ι → ℤ) E) {B : Set (K → ℝ)} (hB : MeasurableSet B)
    {G : AddSubgroup (ι → ℤ)} {Λ : Finset (ι → ℤ)} {π : (ι → ℤ) → (ι → ℤ)}
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) :
    MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Λ : Set (ι → ℤ))]
      {ω : (ι → ℤ) → E | periodicEmpiricalFieldL π hΛ ω ∈
        {ρ ∈ invariantRandomFields (ι → ℤ) E |
          Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ B}} := by
  rw [setOf_periodicEmpiricalFieldL_mem_energyVecPreimage ι E Ψ B hπ hΛ]
  letI : MeasurableSpace ((ι → ℤ) → E) :=
    cylinderEvents (X := fun _ : ι → ℤ ↦ E) (Λ : Set (ι → ℤ))
  have hmeas : Measurable
      fun ω : (ι → ℤ) → E ↦ fun j ↦ (#Λ : ℝ)⁻¹
        * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian π Λ ω :=
    measurable_pi_iff.2 fun j ↦
      (Potential.measurable_cylinderEvents_periodicBoundaryHamiltonian
        (Φ := (Ψ j : Potential (ι → ℤ) E)) hπ).const_mul _
  exact hmeas hB

omit [DecidableEq ι] [Nonempty ι] [Fintype K] ν in
/-- **`e_Ψ⁻¹(B) ∩ 𝓟_Θ` is convex when `B` is.** `𝓟_Θ` is stable under mixtures
(`smul_add_smul_mem_invariantFields`) and `e_Ψ` is affine
(`Potential.specificEnergy_smul_add_smul`), so the constraint set is convex; convexity is read,
as Georgii's `cx̄` is, in the ambient space `𝓕⁰ → ℝ` through the evaluation embedding. -/
theorem convex_image_evalLocalEvents_energyVecPreimage
    (Ψ : K → Potential.BTheta (ι → ℤ) E) {B : Set (K → ℝ)} (hB : Convex ℝ B) :
    Convex ℝ (evalLocalEvents (ι → ℤ) E ''
      {ρ ∈ invariantRandomFields (ι → ℤ) E |
        Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ B}) := by
  refine WithSetwiseTopology.convex_image_evalReal ?_
  rintro μ ⟨hμinv, hμB⟩ ρ ⟨hρinv, hρB⟩ a b ha hb hab
  have hst : a.toNNReal + b.toNNReal = 1 := by
    rw [← Real.toNNReal_add ha hb, hab, Real.toNNReal_one]
  have hmix := smul_add_smul_mem_invariantFields hμinv hρinv hst
  have hsmul : (a.toNNReal : ℝ≥0) • (μ.toMeasure : Measure ((ι → ℤ) → E))
        + (b.toNNReal : ℝ≥0) • (ρ.toMeasure : Measure ((ι → ℤ) → E))
      = ENNReal.ofReal a • (μ.toMeasure : Measure ((ι → ℤ) → E))
        + ENNReal.ofReal b • (ρ.toMeasure : Measure ((ι → ℤ) → E)) := by
    rw [ENNReal.smul_def, ENNReal.smul_def]; rfl
  refine ⟨⟨⟨_, hmix.1⟩⟩, ⟨hmix, ?_⟩, hsmul⟩
  have henergy : Potential.BTheta.energyVec Ψ
      ((a.toNNReal : ℝ≥0) • (μ.toMeasure : Measure ((ι → ℤ) → E))
        + (b.toNNReal : ℝ≥0) • (ρ.toMeasure : Measure ((ι → ℤ) → E)))
      = a • Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((ι → ℤ) → E))
        + b • Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) := by
    funext j
    rw [Potential.BTheta.energyVec_apply, Potential.specificEnergy_smul_add_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Potential.BTheta.energyVec_apply,
      Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
  have hmem : Potential.BTheta.energyVec Ψ
      ((a.toNNReal : ℝ≥0) • (μ.toMeasure : Measure ((ι → ℤ) → E))
        + (b.toNNReal : ℝ≥0) • (ρ.toMeasure : Measure ((ι → ℤ) → E))) ∈ B := by
    rw [henergy]
    exact hB hμB hρB ha hb hab
  exact hmem

variable [StandardBorelSpace E]

/-- **Georgii Corollary (15.48), the first inequality, over a standard Borel state space and for a
convex Borel `B`.** For `Φ ∈ ℬ_Θ`, a vector-valued potential `Ψ ∈ ℬ_Θ^k` and a *convex Borel*
`B ⊆ ℝ^k`,

`limsup_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≤ − inf_{x ∈ B̄} J_Ψ(x|Φ)`,

along any sequence of cubes `Λ_n = [m_n, m_n + s_n]^d` of `ℤ^d` whose side lengths tend to
infinity, with arbitrary torus reductions.

Georgii's Borel hypothesis on `B` is what makes `{°R_Λ ∈ C}` an event
(`measurableSet_cylinderEvents_setOf_mem_energyVecPreimage`); *convexity* of `B` is what makes
`C = e_Ψ⁻¹(B) ∩ 𝓟_Θ` convex, so that Georgii's `cx̄ C` is `C̄` and his Step 3 — the only step of
the proof of (15.46) that is not available over an infinite state space — is not needed. The rest
is exactly Georgii's argument: `C̄ ⊆ e_Ψ⁻¹(B̄)` by the continuity of `e_Ψ` and the closedness of
`𝓟_Θ`, and then `𝓀(·|Φ) ≥ J_Ψ(⟨·, Ψ⟩|Φ)`. -/
theorem limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le_of_convex
    (Φ : Potential.BTheta (ι → ℤ) E) (Ψ : K → Potential.BTheta (ι → ℤ) E)
    {m : ℕ → ι → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (ι → ℤ)} {π : ℕ → (ι → ℤ) → (ι → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)).Nonempty)
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) (hBc : Convex ℝ B) :
    Filter.limsup (fun n ↦ ENNReal.log ((Φ : Potential (ι → ℤ) E).periodicBoundaryGibbs ν (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {ω | (fun j ↦ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : ℝ)⁻¹
                * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian (π n)
                    (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B})
        / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : EReal)) atTop
      ≤ -⨅ x ∈ closure B, Potential.BTheta.ldRate ν Φ Ψ x := by
  classical
  set C : Set (WithLocalConvergence (ι → ℤ) E) :=
    {ρ ∈ invariantRandomFields (ι → ℤ) E |
      Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ B} with hCdef
  have hCsub : C ⊆ invariantRandomFields (ι → ℤ) E := fun _ hρ ↦ hρ.1
  have hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ E)
      ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : Set (ι → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ C} := fun n ↦
    measurableSet_cylinderEvents_setOf_mem_energyVecPreimage Ψ hBm (hπ n) (hne n)
  have hmain := limsup_log_periodicBoundaryGibbs_div_card_le_of_convex ν Φ hs hπ hne hAmeas
    (convex_image_evalLocalEvents_energyVecPreimage Ψ hBc)
  -- the events agree, by Remark (15.43)(3)
  have hev : ∀ n, {ω : (ι → ℤ) → E | periodicEmpiricalFieldL (π n) (hne n) ω ∈ C}
      = {ω : (ι → ℤ) → E | (fun j ↦
          (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (ι → ℤ)) : ℝ)⁻¹
            * (Ψ j : Potential (ι → ℤ) E).periodicBoundaryHamiltonian (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B} := fun n ↦
    setOf_periodicEmpiricalFieldL_mem_energyVecPreimage ι E Ψ B (hπ n) (hne n)
  simp only [hev] at hmain
  refine hmain.trans (EReal.neg_le_neg_iff.2 (le_iInf₂ fun ρ hρ ↦ ?_))
  -- `C̄ ⊆ e_Ψ⁻¹(B̄)`: `𝓟_Θ` is closed and `e_Ψ` is continuous
  have hinv : (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) :=
    (isClosed_setOf_mem_invariantFields (shiftGroup (ι → ℤ) E)).closure_subset_iff.2 hCsub hρ
  have hB : Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((ι → ℤ) → E)) ∈ closure B := by
    have himg := image_closure_subset_closure_image
      (Potential.BTheta.continuous_energyVec Ψ) (Set.mem_image_of_mem _ hρ)
    refine closure_mono ?_ himg
    rintro x ⟨σ, hσ, rfl⟩
    exact hσ.2
  exact (iInf₂_le _ hB).trans (Potential.BTheta.ldRate_le hinv rfl)

end UpperStandardBorel

/-! ### Georgii Corollary (15.48), the lower bound -/

section Lower

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E] {K : Type*} [Fintype K]

/-- **Georgii Corollary (15.48), the second inequality.** For `Φ ∈ ℬ_Θ`, a vector-valued potential
`Ψ ∈ ℬ_Θ^k` and an arbitrary `B ⊆ ℝ^k`,

`liminf_{|Λ| → ∞} |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≥ − inf_{x ∈ B°} J_Ψ(x|Φ)`,

along any sequence of cubes of `ℤ^d` whose side lengths tend to infinity, with arbitrary torus
reductions, over an arbitrary measurable state space.

This is the lower bound (15.47) for `°γ^Φ_Λ`
(`neg_iInf_specificRelativeEntropy_le_liminf_log_periodicBoundaryGibbs`) applied to
`C = e_Ψ⁻¹(B) ∩ 𝓟_Θ`, together with Georgii's inclusion `C° ⊇ e_Ψ⁻¹(B°)`: `e_Ψ⁻¹(B°)` is open by
continuity, so every shift-invariant `μ` with `⟨μ, Ψ⟩ ∈ B°` lies in the interior of `C` relative
to `𝓟_Θ`. The infimum over `𝓟_Θ ∩ e_Ψ⁻¹(B°)` is then regrouped by the fibres of `e_Ψ`
(`Potential.BTheta.iInf_specificRelativeEntropy_eq_iInf_ldRate`). -/
theorem neg_iInf_ldRate_le_liminf_log_periodicBoundaryGibbs_setOf_mem
    (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    (B : Set (K → ℝ)) :
    -(⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x)
      ≤ liminf (fun n ↦ ENNReal.log ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {ω | (fun j ↦ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
                * (Ψ j : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
                    (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : EReal)) atTop := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
  set C : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    {ρ ∈ invariantRandomFields (Fin d → ℤ) E |
      Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ B} with hCdef
  have hmain := neg_iInf_specificRelativeEntropy_le_liminf_log_periodicBoundaryGibbs lam
    (Φ := (Φ : Potential (Fin d → ℤ) E)) (Potential.BTheta.isShiftInvariant Φ) C hs hπ hne
  have hev : ∀ n, {ω : (Fin d → ℤ) → E | periodicEmpiricalFieldL (π n) (hne n) ω ∈ C}
      = {ω : (Fin d → ℤ) → E | (fun j ↦
          (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
            * (Ψ j : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B} := fun n ↦
    setOf_periodicEmpiricalFieldL_mem_energyVecPreimage (Fin d) E Ψ B (hπ n) (hne n)
  simp only [hev] at hmain
  refine le_trans (EReal.neg_le_neg_iff.2 ?_) hmain
  -- `C° ⊇ e_Ψ⁻¹(B°)`, then regroup the infimum by the fibres of `e_Ψ`
  rw [← Potential.BTheta.iInf_specificRelativeEntropy_eq_iInf_ldRate Φ Ψ (interior B)]
  refine le_iInf₂ fun μ hμ ↦ ?_
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  set ρ : WithLocalConvergence (Fin d → ℤ) E := WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩ with hρdef
  have hcoe : (ρ.toMeasure : Measure ((Fin d → ℤ) → E)) = μ := rfl
  set V : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    (fun σ : WithLocalConvergence (Fin d → ℤ) E ↦
      Potential.BTheta.energyVec Ψ (σ.toMeasure : Measure ((Fin d → ℤ) → E))) ⁻¹'
        interior B with hVdef
  have hVopen : IsOpen V :=
    (Potential.BTheta.continuous_energyVec Ψ).isOpen_preimage _ isOpen_interior
  have hmem : ρ ∈ invariantInterior (Fin d → ℤ) E C := by
    refine ⟨by rw [Set.mem_ofPred_eq, hcoe]; exact hμ.1,
      mem_nhdsWithin.2 ⟨V, hVopen, ?_, ?_⟩⟩
    · rw [hVdef, Set.mem_preimage, hcoe]; exact hμ.2
    · rintro σ ⟨hσ1, hσ2⟩
      exact ⟨hσ2, interior_subset hσ1⟩
  exact (iInf₂_le ρ hmem).trans_eq (by rw [hcoe])

end Lower

end MeasureTheory.GibbsMeasure


/-! ### Georgii Example (15.50): the self-potentials and the spatial means `M_Λ f` -/

namespace Potential

section SelfPotential

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] [Countable S]

omit [Countable S] in
/-- **The energy density (15.22) of a single-site potential** is the interaction itself:
`f_{site g} ∘ θ_{-i} = g i (η i)`, because `{i}` is the only volume containing `i` that carries a
nonzero interaction, and `|{i}|⁻¹ = 1`. -/
theorem siteEnergy_site (g : S → E → ℝ) (i : S) (η : S → E) :
    (site g).siteEnergy i η = g i (η i) := by
  rw [siteEnergy]
  refine (tsum_eq_single {i} fun A hA ↦ ?_).trans ?_
  · by_cases hiA : i ∈ A
    · rw [siteEnergyTerms_of_mem hiA, site_eq_zero_of_mem_of_ne g hiA hA]
      simp
    · exact siteEnergyTerms_of_not_mem hiA η
  · rw [siteEnergyTerms_of_mem (Finset.mem_singleton_self i), site_singleton]
    simp

/-- **Georgii Example (15.50).** The Hamiltonian with periodic boundary conditions of a
self-potential is `°H^Ψ_Λ = ∑_{i ∈ Λ} f(σ_i)`: the periodic continuation `ω^∘_Λ` agrees with `ω`
on `Λ` itself (`Potential.IsTorusReduction.eq_self`), and the energy density of a single-site
potential reads the configuration at one site only. -/
theorem periodicBoundaryHamiltonian_site [AddCommGroup S] (f : E → ℝ)
    {G : AddSubgroup S} {Λ : Finset S} {π : S → S} (hπ : IsTorusReduction G Λ π) (ω : S → E) :
    (site fun _ : S ↦ f).periodicBoundaryHamiltonian π Λ ω = ∑ i ∈ Λ, f (ω i) := by
  rw [periodicBoundaryHamiltonian]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [siteEnergy_site]
  exact congrArg f (congrArg ω (hπ.eq_self i hi))

omit [Countable S] in
/-- A bounded measurable observable `f : E → ℝ` gives a self-potential in Georgii's `ℬ_Θ`
(15.21): it is absolutely summable (`Potential.isAbsolutelySummable_site`), vanishes on the empty
volume, is a potential (`Potential.isPotential_site`) and is shift invariant
(`Potential.isShiftInvariant_site`). -/
theorem site_const_mem_BTheta [AddGroup S] {f : E → ℝ} (hf : Measurable f) {c : ℝ}
    (hb : ∀ x, |f x| ≤ c) : (site fun _ : S ↦ f) ∈ BTheta S E :=
  ⟨⟨isAbsolutelySummable_site fun _ x ↦ hb x,
      funext fun η ↦ by simp [site_apply, siteTerms],
      isPotential_site fun _ ↦ hf⟩,
    isShiftInvariant_site f⟩

variable (S) in
/-- **Georgii Example (15.50).** The *self-potential* `Ψ_{i} = f(σ_i)` of a bounded measurable
observable `f : E → ℝ`, as an element of Georgii's Banach space `ℬ_Θ`. -/
def selfPotential [AddGroup S] {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hb : ∀ x, |f x| ≤ c) :
    BTheta S E :=
  ⟨site fun _ : S ↦ f, site_const_mem_BTheta hf hb⟩

@[simp] lemma coe_selfPotential [AddGroup S] {f : E → ℝ} (hf : Measurable f) {c : ℝ}
    (hb : ∀ x, |f x| ≤ c) :
    (selfPotential S hf hb : Potential S E) = site fun _ : S ↦ f := rfl

end SelfPotential

/-! ### The pressure of a self-potential, Georgii Example (15.50) at `Φ = 0` -/

section SitePressure

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] [Countable S]

/-- **The partition function of a single-site potential factorises.** For `Φ = site g` with a
bounded measurable `g : E → ℝ`, `Z^Φ_Λ(ω) = λ(e^{−g})^{|Λ|}` for every boundary condition `ω`:
the Hamiltonian in `Λ` is `∑_{i ∈ Λ} g(σ_i)` (`Potential.hamiltonian_site`), which does not see
the boundary condition, and the a priori measure in `Λ` is the product `λ^Λ`. -/
theorem premodifierZ_boltzmannFactor_site (ν : Measure E) [IsProbabilityMeasure ν]
    {g : E → ℝ} (hg : Measurable g) {c : ℝ} (hb : ∀ x, |g x| ≤ c) (Λ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν ((site fun _ : S ↦ g).boltzmannFactor 1) Λ ω
      = ENNReal.ofReal ((∫ x, Real.exp (-g x) ∂ν) ^ (#Λ)) := by
  have hpot : IsPotential (site fun _ : S ↦ g) := isPotential_site fun _ ↦ hg
  have hmeas : Measurable ((site fun _ : S ↦ g).boltzmannFactor 1 Λ) :=
    measurable_boltzmannFactor (Φ := site fun _ : S ↦ g) 1 Λ
  rw [Specification.premodifierZ, Specification.relZ, Specification.lintegral_isssd_eq Λ ω hmeas]
  have hint : ∀ ζ : Λ → E, (site fun _ : S ↦ g).boltzmannFactor 1 Λ (juxt (Λ : Set S) ω ζ)
      = ENNReal.ofReal (∏ i : Λ, Real.exp (-g (ζ i))) := by
    intro ζ
    have hsum : ∑ x : Λ, -g (ζ x) = -1 * ∑ i ∈ Λ, g (juxt (Λ : Set S) ω ζ i) := by
      rw [neg_one_mul, ← Finset.sum_coe_sort Λ (fun i ↦ g (juxt (Λ : Set S) ω ζ i)),
        ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [juxt_apply_of_mem i.2, Subtype.coe_eta]
    rw [boltzmannFactor, hamiltonian_site, ← Real.exp_sum, hsum]
  rw [lintegral_congr hint]
  have hmeasφ : Measurable fun x : E ↦ Real.exp (-g x) := hg.neg.exp
  have hintφ : Integrable (fun x : E ↦ Real.exp (-g x)) ν :=
    Integrable.of_bound hmeasφ.aestronglyMeasurable (Real.exp c) (.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (by linarith [abs_le.1 (hb x)]))
  have hprod : Integrable (fun ζ : Λ → E ↦ ∏ i : Λ, Real.exp (-g (ζ i)))
      (Measure.pi fun _ : Λ ↦ ν) := Integrable.fintype_prod fun _ ↦ hintφ
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (.of_forall fun ζ ↦ Finset.prod_nonneg fun i _ ↦ (Real.exp_pos _).le)]
  congr 1
  rw [MeasureTheory.integral_fintype_prod_eq_pow (ι := Λ) (fun x : E ↦ Real.exp (-g x)),
    Fintype.card_coe]

/-- **The finite-volume pressure of a single-site potential** is `|Λ| log λ(e^{−g})`, whatever the
boundary condition. -/
theorem logZ_site (ν : Measure E) [IsProbabilityMeasure ν]
    {g : E → ℝ} (hg : Measurable g) {c : ℝ} (hb : ∀ x, |g x| ≤ c) (Λ : Finset S) (ω : S → E) :
    (site fun _ : S ↦ g).logZ ν Λ ω = #Λ * Real.log (∫ x, Real.exp (-g x) ∂ν) := by
  rw [logZ, premodifierZ_boltzmannFactor_site ν hg hb Λ ω,
    ENNReal.toReal_ofReal (pow_nonneg (integral_nonneg fun x ↦ (Real.exp_pos _).le) _),
    Real.log_pow]

omit [Countable S] in
/-- A single-site potential built from the zero interaction is the zero potential. -/
@[simp] lemma site_zero : (site fun _ : S ↦ (0 : E → ℝ)) = (0 : Potential S E) := by
  funext A η
  simp [site_apply, siteTerms]

end SitePressure

section SitePressureLattice

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]

/-- **The pressure of a self-potential**, Georgii Example (15.50) at `Φ = 0`:
`P(site g) = log λ(e^{−g})`. The finite-volume pressures `|Λ|⁻¹ log Z^{site g}_Λ(ω)` are all
equal to `log λ(e^{−g})` (`Potential.logZ_site`), and by Theorem (15.30)(a) they converge to
`P(site g)`. -/
theorem pressure_site (ν : Measure E) [IsProbabilityMeasure ν]
    {g : E → ℝ} (hg : Measurable g) {c : ℝ} (hb : ∀ x, |g x| ≤ c) :
    (site fun _ : ι → ℤ ↦ g).pressure ν = Real.log (∫ x, Real.exp (-g x) ∂ν) := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hpot : IsPotential (site fun _ : ι → ℤ ↦ g) := isPotential_site fun _ ↦ hg
  have hsum : IsAbsolutelySummable (site fun _ : ι → ℤ ↦ g) :=
    isAbsolutelySummable_site fun _ x ↦ hb x
  have hshift : (site fun _ : ι → ℤ ↦ g).IsShiftInvariant := isShiftInvariant_site g
  have hlim := tendsto_logZ_div_card_pressure (Φ := site fun _ : ι → ℤ ↦ g) ν hshift
    tendsto_sub_atTop_cube (fun _ : ℕ ↦ (Classical.arbitrary ((ι → ℤ) → E)))
  refine tendsto_nhds_unique hlim ?_
  refine tendsto_const_nhds.congr fun N ↦ ?_
  have hcard : (0 : ℝ) < #(Finset.Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) := by
    exact_mod_cast (Finset.nonempty_Icc.2 (show (fun _ : ι ↦ (0 : ℤ)) ≤ fun _ ↦ (N : ℤ) from
      fun _ ↦ Int.natCast_nonneg N)).card_pos
  rw [logZ_site ν hg hb, mul_comm, mul_div_assoc, div_self hcard.ne', mul_one]

/-- The pressure of the zero potential relative to an a priori *probability* measure is `0`. -/
@[simp] theorem pressure_zero (ν : Measure E) [IsProbabilityMeasure ν] :
    (0 : Potential (ι → ℤ) E).pressure ν = 0 := by
  have h := pressure_site (ι := ι) ν (g := (0 : E → ℝ)) measurable_const
    (c := 0) (fun x ↦ by simp)
  rw [site_zero] at h
  simpa using h

end SitePressureLattice

/-! ### Linearity of `site`, and the zero potential -/

section SiteLinear

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] {K : Type*} [Fintype K]

omit [DecidableEq S] in
/-- A finite sum of potentials is evaluated termwise. (Intended home:
`GibbsMeasure/Potential/Space.lean`, next to `Potential.add_apply`.) -/
lemma sum_apply {α : Type*} (s : Finset α) (F : α → Potential S E) (A : Finset S) (η : S → E) :
    (∑ a ∈ s, F a) A η = ∑ a ∈ s, F a A η := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

/-- `site` is additive-inverse preserving in the interaction: `−site f = site (−f)`. -/
lemma site_neg (f : S → E → ℝ) : -(site f) = site fun i x ↦ -(f i x) := by
  funext A η
  simp only [neg_apply, site_apply, siteTerms, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by by_cases h : A = {i} <;> simp [h]

/-- `site` is homogeneous in the interaction: `c • site f = site (c f)`. -/
lemma smul_site (c : ℝ) (f : S → E → ℝ) : c • site f = site fun i x ↦ c * f i x := by
  funext A η
  simp only [smul_apply, site_apply, siteTerms, Finset.mul_sum, mul_ite, mul_zero]

/-- **`site` is linear in the interaction**: a linear combination `t · f = ∑ⱼ tⱼ fʲ` of bounded
observables gives the linear combination of the corresponding self-potentials. -/
theorem sum_smul_site (t : K → ℝ) (f : K → E → ℝ) :
    ∑ j, t j • (site fun _ : S ↦ f j) = site fun _ : S ↦ fun x ↦ ∑ j, t j * f j x := by
  funext A η
  rw [sum_apply]
  simp only [smul_apply, site_apply, siteTerms, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : A = {i} <;> simp [h]

end SiteLinear

section ZeroPotential

variable {S E : Type*} [Countable S] [AddCommGroup S] [MeasurableSpace E]

omit [Countable S] [AddCommGroup S] in
@[simp] lemma siteEnergy_zero (i : S) (η : S → E) : (0 : Potential S E).siteEnergy i η = 0 := by
  simp [siteEnergy, siteEnergyTerms]

omit [Countable S] [AddCommGroup S] in
@[simp] lemma periodicBoundaryHamiltonian_zero (π : S → S) (Λ : Finset S) (ω : S → E) :
    (0 : Potential S E).periodicBoundaryHamiltonian π Λ ω = 0 := by
  simp [periodicBoundaryHamiltonian]

@[simp] theorem periodicBoundaryZ_zero (ν : Measure E) [IsProbabilityMeasure ν]
    (π : S → S) (Λ : Finset S) : (0 : Potential S E).periodicBoundaryZ ν π Λ = 1 := by
  simp [periodicBoundaryZ]

/-- **Georgii Example (15.50) at `Φ = 0`.** With no interaction the Gibbs distribution with
periodic boundary conditions is the a priori product measure: `°γ^0_Λ = λ^S`, which is Georgii's
`°γ^0_Λ = λ^Λ` read on the whole configuration space. -/
@[simp] theorem periodicBoundaryGibbs_zero (ν : Measure E) [IsProbabilityMeasure ν]
    (π : S → S) (Λ : Finset S) :
    (0 : Potential S E).periodicBoundaryGibbs ν π Λ = Measure.infinitePi fun _ : S ↦ ν := by
  rw [periodicBoundaryGibbs, show (0 : Potential S E).periodicBoundaryDensity ν π Λ = 1 from
    funext fun ω ↦ by simp [periodicBoundaryDensity], withDensity_one]

end ZeroPotential

/-! ### Georgii Example (15.50), last sentence: Cramér's rate function -/

namespace BTheta

section Cramer

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {K : Type*} [Fintype K]

omit [DecidableEq ι] in
/-- The tilted vector-valued self-potential `t · Ψ` of `Ψʲ_{i} = fʲ(σ_i)` is the self-potential
of `t · f = ∑ⱼ tⱼ fʲ`. -/
theorem coe_dotPotential_selfPotential {f : K → E → ℝ} (hf : ∀ j, Measurable (f j))
    {c : K → ℝ} (hb : ∀ j x, |f j x| ≤ c j) (t : K → ℝ) :
    ((dotPotential t (fun j ↦ selfPotential (ι → ℤ) (hf j) (hb j)) : BTheta (ι → ℤ) E)
        : Potential (ι → ℤ) E)
      = site fun _ : ι → ℤ ↦ fun x ↦ ∑ j, t j * f j x := by
  rw [dotPotential, ← sum_smul_site (S := ι → ℤ) t f]
  push_cast
  rfl

/-- **Georgii Example (15.50), the pressure of a tilted self-potential at `Φ = 0`:**
`P(−t·Ψ) = log λ(e^{t·f})`. This is `Potential.pressure_site` for the single-site potential
`(−t·f)(σ_i)`. -/
theorem pressure_zero_sub_dotPotential_selfPotential (lam : Measure E) [IsProbabilityMeasure lam]
    {f : K → E → ℝ} (hf : ∀ j, Measurable (f j)) {c : K → ℝ} (hb : ∀ j x, |f j x| ≤ c j)
    (t : K → ℝ) :
    (((0 : BTheta (ι → ℤ) E) - dotPotential t
          (fun j ↦ selfPotential (ι → ℤ) (hf j) (hb j)) : BTheta (ι → ℤ) E)
        : Potential (ι → ℤ) E).pressure lam
      = Real.log (∫ y, Real.exp (∑ j, t j * f j y) ∂lam) := by
  have hcoe : (((0 : BTheta (ι → ℤ) E) - dotPotential t
        (fun j ↦ selfPotential (ι → ℤ) (hf j) (hb j)) : BTheta (ι → ℤ) E)
      : Potential (ι → ℤ) E) = site fun _ : ι → ℤ ↦ fun x ↦ -∑ j, t j * f j x := by
    rw [zero_sub, Submodule.coe_neg, coe_dotPotential_selfPotential hf hb, site_neg]
  rw [hcoe, pressure_site lam (g := fun x ↦ -∑ j, t j * f j x)
    (by fun_prop) (c := ∑ j, |t j| * c j) (fun x ↦ ?_)]
  · simp
  · rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb j x) (abs_nonneg _)

variable [StandardBorelSpace E]

/-- **Georgii Example (15.50), last sentence: Cramér's rate function.** For the vector-valued
self-potential `Ψʲ_{i} = fʲ(σ_i)` of bounded measurable observables `f¹, …, fᵏ : E → ℝ` and for
the *free* potential `Φ = 0`, the rate function (15.49) is the Legendre transform of the
cumulant generating function of `f` under the a priori measure `λ`:

`J_Ψ(x|0) = sup_{t ∈ ℝ^k} [t·x − log λ(e^{t·f})]`.

This is the Legendre formula (15.49) (`Potential.BTheta.ldRate_eq_iSup`) together with
`P(0) = 0` (`Potential.pressure_zero`) and `P(−t·Ψ) = log λ(e^{t·f})`
(`Potential.BTheta.pressure_zero_sub_dotPotential_selfPotential`). -/
theorem ldRate_zero_selfPotential_eq_iSup (lam : Measure E) [IsProbabilityMeasure lam]
    {f : K → E → ℝ} (hf : ∀ j, Measurable (f j)) {c : K → ℝ} (hb : ∀ j x, |f j x| ≤ c j)
    (x : K → ℝ) :
    ldRate lam (0 : BTheta (ι → ℤ) E) (fun j ↦ selfPotential (ι → ℤ) (hf j) (hb j)) x
      = ⨆ t : K → ℝ, (((∑ j, t j * x j)
          - Real.log (∫ y, Real.exp (∑ j, t j * f j y) ∂lam) : ℝ) : EReal) := by
  rw [ldRate_eq_iSup]
  refine iSup_congr fun t ↦ ?_
  rw [pressure_zero_sub_dotPotential_selfPotential lam hf hb t]
  norm_num [Submodule.coe_zero, Potential.pressure_zero]

omit [StandardBorelSpace E] in
/-- **The pressure of a tilted self-potential is the cumulant generating function of `f`:**
`P(−t Ψ) = log λ(e^{tf}) = K_f(t)`. -/
theorem pressure_smul_neg_selfPotential (lam : Measure E) [IsProbabilityMeasure lam]
    {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hb : ∀ x, |f x| ≤ c) (t : ℝ) :
    pressure lam (t • (-(Potential.selfPotential (ι → ℤ) hf hb))) = ProbabilityTheory.cgf f lam t
    := by
  have hcoe : ((t • (-(Potential.selfPotential (ι → ℤ) hf hb)) : BTheta (ι → ℤ) E)
      : Potential (ι → ℤ) E) = site fun _ : ι → ℤ ↦ fun x ↦ -(t * f x) := by
    rw [Submodule.coe_smul, Submodule.coe_neg, Potential.coe_selfPotential, site_neg, smul_site]
    exact congrArg site (funext fun _ ↦ funext fun x ↦ by ring)
  rw [pressure_apply, hcoe,
    pressure_site lam (g := fun x ↦ -(t * f x)) (by fun_prop) (c := |t| * c) (fun x ↦ ?_)]
  · rw [ProbabilityTheory.cgf, ProbabilityTheory.mgf,
      integral_congr_ae (.of_forall fun x ↦ by rw [neg_neg])]
  · rw [abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

/-- **Georgii Example (15.50): the left endpoint `a⁺_{f,0} = ∂⁺_{−Ψ}P(0)` at `Φ = 0` is the
`λ`-mean of `f`.** Indeed `t ↦ P(−tΨ)` is the cumulant generating function `K_f` of `f` under
`λ` (`Potential.BTheta.pressure_smul_neg_selfPotential`), `K_f(0) = 0`, and `K_f` is analytic at
`0` with `K_f'(0) = λ(f)` because `f` is bounded, so the whole real line is in the interior of
the integrability set of `e^{tf}` (`ProbabilityTheory.deriv_cgf_zero`). -/
theorem rightDirDeriv_pressure_neg_selfPotential (lam : Measure E) [IsProbabilityMeasure lam]
    {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hb : ∀ x, |f x| ≤ c) :
    rightDirDeriv (pressure lam) (0 : BTheta (ι → ℤ) E)
        (-(Potential.selfPotential (ι → ℤ) hf hb)) = ∫ x, f x ∂lam := by
  have hint : ∀ t : ℝ, Integrable (fun x ↦ Real.exp (t * f x)) lam := by
    intro t
    refine Integrable.of_bound ((measurable_const.mul hf).exp).aestronglyMeasurable
      (Real.exp (|t| * c)) (.of_forall fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    calc t * f x ≤ |t * f x| := le_abs_self _
      _ = |t| * |f x| := abs_mul _ _
      _ ≤ |t| * c := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  have hIES : ProbabilityTheory.integrableExpSet f lam = Set.univ :=
    Set.eq_univ_of_forall fun t ↦ hint t
  have hmem : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet f lam) := by
    rw [hIES]; simp
  have hderiv : HasDerivAt (ProbabilityTheory.cgf f lam) (∫ x, f x ∂lam) 0 := by
    have h := (ProbabilityTheory.analyticAt_cgf hmem).differentiableAt.hasDerivAt
    have hone : (lam.real Set.univ) = 1 := by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]
    rwa [ProbabilityTheory.deriv_cgf_zero hmem, hone, div_one] at h
  have hcgf0 : ProbabilityTheory.cgf f lam 0 = 0 := by
    simp [ProbabilityTheory.cgf, ProbabilityTheory.mgf]
  have hslope : Tendsto (fun t : ℝ ↦ ProbabilityTheory.cgf f lam t / t) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, f x ∂lam)) := by
    have h := (hasDerivAt_iff_tendsto_slope.1 hderiv).mono_left
      (nhdsWithin_mono 0 (fun x hx ↦ ne_of_gt hx))
    refine h.congr fun t ↦ ?_
    rw [slope_def_field, hcgf0]
    simp [div_eq_inv_mul]
  have hdir := tendsto_dirSlope_rightDirDeriv_pressure lam (0 : BTheta (ι → ℤ) E)
    (-(Potential.selfPotential (ι → ℤ) hf hb))
  have heq : dirSlope (pressure lam) (0 : BTheta (ι → ℤ) E)
      (-(Potential.selfPotential (ι → ℤ) hf hb))
      = fun t : ℝ ↦ ProbabilityTheory.cgf f lam t / t := by
    funext t
    rw [dirSlope, zero_add, pressure_smul_neg_selfPotential lam hf hb t, pressure_apply,
      Submodule.coe_zero, Potential.pressure_zero, sub_zero]
  rw [heq] at hdir
  exact tendsto_nhds_unique hdir hslope

/-- **Georgii Example (15.50), last sentence, as he writes it** (`k = 1`):

`J_Ψ(a|0) = sup_{t ∈ ℝ} [ta − log λ(e^{tf})]`,

the classical Cramér rate function of the real random variable `f` under `λ`. -/
theorem ldRate_zero_selfPotential_eq_iSup_real [Unique K] (lam : Measure E)
    [IsProbabilityMeasure lam] {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hb : ∀ x, |f x| ≤ c)
    (a : ℝ) :
    ldRate lam (0 : BTheta (ι → ℤ) E) (fun _ : K ↦ selfPotential (ι → ℤ) hf hb) (fun _ ↦ a)
      = ⨆ t : ℝ, ((t * a - Real.log (∫ y, Real.exp (t * f y) ∂lam) : ℝ) : EReal) := by
  rw [ldRate_zero_selfPotential_eq_iSup lam (f := fun _ : K ↦ f) (fun _ ↦ hf)
    (c := fun _ ↦ c) (fun _ ↦ hb)]
  rw [← (Equiv.funUnique K ℝ).symm.iSup_comp (g := fun t : K → ℝ ↦
    (((∑ j, t j * a) - Real.log (∫ y, Real.exp (∑ j, t j * f y) ∂lam) : ℝ) : EReal))]
  refine iSup_congr fun t ↦ ?_
  simp [Equiv.funUnique, Finset.univ_unique]

end Cramer

end BTheta

end Potential

namespace MeasureTheory.GibbsMeasure

section SpatialMean

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {K : Type*} [Fintype K]

omit [DecidableEq ι] in
/-- **Georgii Example (15.50).** For a family of self-potentials `Ψʲ_{i} = fʲ(σ_i)`, the vector
`|Λ|⁻¹ °H^Ψ_Λ` is the vector of spatial means `M_Λ fʲ = |Λ|⁻¹ ∑_{i ∈ Λ} fʲ(σ_i)`. -/
theorem inv_card_mul_periodicBoundaryHamiltonian_selfPotential
    {f : K → E → ℝ} (hf : ∀ j, Measurable (f j)) {c : K → ℝ} (hb : ∀ j x, |f j x| ≤ c j)
    {G : AddSubgroup (ι → ℤ)} {Λ : Finset (ι → ℤ)} {π : (ι → ℤ) → (ι → ℤ)}
    (hπ : Potential.IsTorusReduction G Λ π) (ω : (ι → ℤ) → E) :
    (fun j ↦ (#Λ : ℝ)⁻¹ * (Potential.selfPotential (ι → ℤ) (hf j) (hb j) :
        Potential (ι → ℤ) E).periodicBoundaryHamiltonian π Λ ω)
      = fun j ↦ (#Λ : ℝ)⁻¹ * ∑ i ∈ Λ, f j (ω i) := by
  funext j
  rw [Potential.coe_selfPotential, Potential.periodicBoundaryHamiltonian_site (f := f j) hπ]

end SpatialMean



/-! ### Georgii (15.51): the exact exponential rate of a one-sided deviation -/

section OneSided

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E] [Finite E]
  [MeasurableSingletonClass E] [StandardBorelSpace E] {K : Type*} [Fintype K] [Unique K]

omit [Finite E] [MeasurableSingletonClass E] in
open Potential.BTheta in
/-- **Georgii (15.51).** For a single potential `Ψ ∈ ℬ_Θ` (Georgii's `k = 1`), a level `a` at or
above the right endpoint `a⁺ = ∂⁺_{−Ψ}P(Φ)` of the interval on which `J_Ψ(·|Φ)` vanishes, and a
point `b > a` at which `J_Ψ(·|Φ)` is still finite,

`|Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ≥ a) → − J_Ψ(a|Φ)`,

i.e. `°γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ≥ a) = exp[−|Λ|(J_Ψ(a|Φ) + o(1))]`, along any sequence of cubes of `ℤ^d`
whose side lengths tend to infinity, with arbitrary torus reductions.

Both bounds of Corollary (15.48) are applied to the half-line `B = [a, ∞)`, which is closed with
interior `(a, ∞)`; the two infima agree because `J_Ψ(·|Φ)` is nondecreasing on `[a⁺, ∞)`
(`Potential.BTheta.ldRate_le_ldRate_of_le`) and right-continuous at `a`
(`Potential.BTheta.iInf_ldRate_Ioi_eq`), the latter being exactly what the hypothesis
`J_Ψ(b|Φ) < ∞` for some `b > a` provides.

Georgii states (15.51) for the self-potential `Ψ_{i} = f(σ_i)`, where `|Λ|⁻¹ °H^Ψ_Λ = M_Λ f`
(`MeasureTheory.GibbsMeasure.inv_card_mul_periodicBoundaryHamiltonian_selfPotential`), for
`a⁺_{f,Φ} < a < a⁺_f`, `a⁺_f` the supremum of the support of `f(λ)`; the finiteness of
`J_Ψ(·|Φ)` on `]a⁻_f, a⁺_f[` — which is what supplies the point `b` — is asserted there without
proof and is a hypothesis here. -/
theorem tendsto_log_periodicBoundaryGibbs_setOf_le_div_card
    (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {a b : ℝ} (ha : rightDirDeriv (pressure lam) Φ (-Ψ default) ≤ a) (hab : a < b)
    (hb : ldRate lam Φ Ψ (fun _ ↦ b) ≠ ⊤) :
    Tendsto (fun n ↦ ENNReal.log ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {ω | a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
                * (Ψ default : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
                    (Finset.Icc (m n) fun k ↦ m n k + s n) ω})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : EReal)) atTop
        (𝓝 (-ldRate lam Φ Ψ fun _ ↦ a)) := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
  set B : Set (K → ℝ) := {x : K → ℝ | a ≤ x default} with hBdef
  -- the event `{|Λ|⁻¹ °H^Ψ_Λ ≥ a}` is the event `{|Λ|⁻¹ °H^Ψ_Λ ∈ B}` of Corollary (15.48)
  have hset : ∀ n, {ω : (Fin d → ℤ) → E |
        (fun j ↦ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
          * (Ψ j : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
              (Finset.Icc (m n) fun k ↦ m n k + s n) ω) ∈ B}
      = {ω : (Fin d → ℤ) → E |
        a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
          * (Ψ default : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
              (Finset.Icc (m n) fun k ↦ m n k + s n) ω} := fun n ↦ rfl
  -- `B` is closed with interior `(a, ∞)`
  have hBclosed : IsClosed B := isClosed_Ici.preimage (continuous_apply default)
  have hBint : interior B = {x : K → ℝ | a < x default} := by
    have hpre : B = (Homeomorph.funUnique K ℝ) ⁻¹' Set.Ici a := rfl
    rw [hpre, ← (Homeomorph.funUnique K ℝ).preimage_interior, interior_Ici]
    rfl
  -- both infima are `J_Ψ(a|Φ)`
  have hinfB : ⨅ x ∈ closure B, ldRate lam Φ Ψ x = ldRate lam Φ Ψ fun _ ↦ a := by
    have hmem : (fun _ : K ↦ a) ∈ B := by rw [hBdef]; exact Set.mem_ofPred.2 le_rfl
    rw [hBclosed.closure_eq]
    exact le_antisymm (iInf₂_le (fun _ : K ↦ a) hmem)
      (le_iInf₂ fun x hx ↦ ldRate_le_ldRate_of_le Φ Ψ ha hx)
  have hinfInt : ⨅ x ∈ interior B, ldRate lam Φ Ψ x = ldRate lam Φ Ψ fun _ ↦ a := by
    rw [hBint]
    exact iInf_ldRate_Ioi_eq Φ Ψ ha hab hb
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · have hlow := neg_iInf_ldRate_le_liminf_log_periodicBoundaryGibbs_setOf_mem lam Φ Ψ hs hπ hne B
    rw [hinfInt] at hlow
    simpa only [hset] using hlow
  · have hBconv : Convex ℝ B := fun x hx y hy p q hp hq hpq ↦ by
      have hx' : a ≤ x default := hx
      have hy' : a ≤ y default := hy
      show a ≤ (p • x + q • y) default
      have : (p • x + q • y) default = p * x default + q * y default := rfl
      rw [this]
      have h1 : p * a ≤ p * x default := mul_le_mul_of_nonneg_left hx' hp
      have h2 : q * a ≤ q * y default := mul_le_mul_of_nonneg_left hy' hq
      have h3 : p * a + q * a = a := by rw [← add_mul, hpq, one_mul]
      linarith
    have hup := limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le_of_convex lam Φ Ψ hs hπ hne
      hBclosed.measurableSet hBconv
    rw [hinfB] at hup
    simpa only [hset] using hup

omit [Finite E] [MeasurableSingletonClass E] in
open Potential.BTheta in
/-- **Georgii (15.51)** as he states it, for the self-potential `Ψ_{i} = f(σ_i)` of a bounded
measurable observable `f : E → ℝ`, whose periodic Hamiltonian per site is the spatial mean
`M_Λ f = |Λ|⁻¹ ∑_{i ∈ Λ} f(σ_i)`:

`°γ^Φ_Λ(M_Λ f ≥ a) = exp[−|Λ| (J_Ψ(a|Φ) + o(1))]`.

Georgii's hypotheses are `a⁺_{f,Φ} < a < a⁺_f`, with `a⁺_{f,Φ} = ∂⁺_{−Ψ}P(Φ)` and `a⁺_f` the
supremum of the support of `f(λ)`; `a < a⁺_f` enters only through the finiteness of `J_Ψ(·|Φ)`
somewhere strictly above `a`, which is the hypothesis `hb` here (Georgii asserts the finiteness
of `J_Ψ(·|Φ)` on `]a⁻_f, a⁺_f[` without proof). Under his strict inequality `a⁺_{f,Φ} < a` the
limit is moreover *strictly negative* (`Potential.BTheta.ldRate_pos`), so that
`0 < J_Ψ(a|Φ) < ∞` as he states. -/
theorem tendsto_log_periodicBoundaryGibbs_setOf_le_spatialMean_div_card
    (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E)
    {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hbd : ∀ x, |f x| ≤ c)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {a b : ℝ}
    (ha : rightDirDeriv (pressure lam) Φ
      (-(fun _ : K ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) default) ≤ a)
    (hab : a < b)
    (hb : ldRate lam Φ (fun _ : K ↦ Potential.selfPotential (Fin d → ℤ) hf hbd)
      (fun _ ↦ b) ≠ ⊤) :
    Tendsto (fun n ↦ ENNReal.log ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n)
            {ω | a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
                * ∑ i ∈ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)), f (ω i)})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : EReal)) atTop
        (𝓝 (-ldRate lam Φ (fun _ : K ↦ Potential.selfPotential (Fin d → ℤ) hf hbd)
          fun _ ↦ a)) := by
  have hev := tendsto_log_periodicBoundaryGibbs_setOf_le_div_card lam Φ
    (fun _ : K ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) hs hπ hne ha hab hb
  have hset : ∀ n : ℕ,
      {ω : (Fin d → ℤ) → E |
          a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
            * ((fun _ : K ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) default :
                Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian (π n)
                  (Finset.Icc (m n) fun k ↦ m n k + s n) ω}
        = {ω : (Fin d → ℤ) → E |
          a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
            * ∑ i ∈ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)), f (ω i)} :=
    fun n ↦ Set.ext fun ω ↦ by
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Potential.coe_selfPotential,
        Potential.periodicBoundaryHamiltonian_site (f := f) (hπ n)]
  simpa only [hset] using hev

end OneSided

/-! ### Georgii Example (15.50), last sentence: Cramér's theorem -/

section Cramer

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
  {K : Type*} [Fintype K] [Unique K]

open Potential.BTheta in
/-- **Cramér's theorem, Georgii Example (15.50), last sentence.** For `Φ = 0` the Gibbs
distribution with periodic boundary conditions is the a priori product measure `λ^S`
(`Potential.periodicBoundaryGibbs_zero`), the spatial means `M_Λ f = |Λ|⁻¹ ∑_{i ∈ Λ} f(σ_i)` are
the empirical means of the i.i.d. family `(f(σ_i))_{i ∈ ℤ^d}` with common law `f(λ)`, and the
rate function is the classical Cramér rate
`J_Ψ(a|0) = sup_{t ∈ ℝ} [ta − log λ(e^{tf})]`
(`Potential.BTheta.ldRate_zero_selfPotential_eq_iSup_real`). So (15.51) reads

`λ^S(M_Λ f ≥ a) = exp[−|Λ| (sup_t [ta − log λ(e^{tf})] + o(1))]`

along any sequence of cubes of `ℤ^d` whose side lengths tend to infinity.

The hypotheses are Georgii's, transported to `Φ = 0`: `a` is at or above the right endpoint
`∂⁺_{−Ψ}P(0)` of the interval on which the rate vanishes (that endpoint is the `λ`-mean of `f`),
and the rate is finite somewhere strictly above `a`. -/
theorem tendsto_log_infinitePi_setOf_le_spatialMean_div_card
    (lam : Measure E) [IsProbabilityMeasure lam]
    {f : E → ℝ} (hf : Measurable f) {c : ℝ} (hbd : ∀ x, |f x| ≤ c)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {a b : ℝ}
    (ha : ∫ x, f x ∂lam ≤ a) (hab : a < b)
    (hb : (⨆ t : ℝ, ((t * b - Real.log (∫ y, Real.exp (t * f y) ∂lam) : ℝ) : EReal)) ≠ ⊤) :
    Tendsto (fun n ↦ ENNReal.log ((Measure.infinitePi fun _ : Fin d → ℤ ↦ lam)
            {ω | a ≤ (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ)⁻¹
                * ∑ i ∈ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)), f (ω i)})
          / (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : EReal)) atTop
        (𝓝 (-⨆ t : ℝ, ((t * a - Real.log (∫ y, Real.exp (t * f y) ∂lam) : ℝ) : EReal))) := by
  have ha' : rightDirDeriv (pressure lam) (0 : Potential.BTheta (Fin d → ℤ) E)
      (-(fun _ : Unit ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) default) ≤ a := by
    rw [show (-(fun _ : Unit ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) default)
        = -(Potential.selfPotential (Fin d → ℤ) hf hbd) from rfl,
      rightDirDeriv_pressure_neg_selfPotential lam hf hbd]
    exact ha
  have hb' : ldRate lam (0 : Potential.BTheta (Fin d → ℤ) E)
      (fun _ : Unit ↦ Potential.selfPotential (Fin d → ℤ) hf hbd) (fun _ ↦ b) ≠ ⊤ := by
    rw [ldRate_zero_selfPotential_eq_iSup_real lam hf hbd b]
    exact hb
  have h := tendsto_log_periodicBoundaryGibbs_setOf_le_spatialMean_div_card lam
    (0 : Potential.BTheta (Fin d → ℤ) E) hf hbd hs hπ hne ha' hab hb'
  rw [ldRate_zero_selfPotential_eq_iSup_real lam hf hbd a] at h
  simpa only [Submodule.coe_zero, Potential.periodicBoundaryGibbs_zero] using h

end Cramer

end MeasureTheory.GibbsMeasure

end

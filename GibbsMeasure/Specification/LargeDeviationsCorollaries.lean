/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.SelfPotential
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
  `limsup |Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) ≤ − inf_{x ∈ B̄} J_Ψ(x|Φ)`.
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
  `Potential.BTheta.iInf_ldRate_Ioi_eq`.

The shape of `J_Ψ(·|Φ)` that Georgii quotes from Chapter 16 — its minimum `0` is attained exactly
on `[a⁻_{f,Φ}, a⁺_{f,Φ}]`, it is monotone on either side, and it is strictly positive beyond —
is `Potential.BTheta.ldRate_eq_zero_iff_mem_Icc`, `Potential.BTheta.ldRate_le_ldRate_of_le` and
`Potential.BTheta.ldRate_pos` of `GibbsMeasure/Specification/LargeDeviations.lean`.

Two assertions of Example (15.50) are *not* proved: the finiteness of `J_Ψ(·|Φ)` on
`]a⁻_f, a⁺_f[` (which Georgii also asserts without proof, and which here appears as the
hypothesis `J_Ψ(b|Φ) < ∞` for some `b > a`), and the Cramér formula
`J_Ψ(a|0) = sup_t [ta − log λ(e^{tf})]`, for which the pressure of a self-potential,
`P(−tΨ) = log λ(e^{tf})`, is still missing. See the module documentation of
`GibbsMeasure/Specification/LargeDeviations.lean`.

## Two deviations from Georgii's statement

* Georgii asks for a **Borel** `B ⊆ ℝ^k`, because his `C` must belong to `𝓔(𝓟_Θ)` for `{°R_Λ ∈ C}`
  to be an event. Over the finite state space of the upper bound, and for the `𝓕_Λ`-events used in
  the lower bound, `{°R_Λ ∈ C}` is measurable for *every* `C`
  (`MeasureTheory.GibbsMeasure.measurableSet_cylinderEvents_setOf_periodicEmpiricalFieldL_mem`),
  so no hypothesis on `B` is needed here; `B` is an arbitrary set.
* The two inequalities are stated separately, at the generality each one has in the tree: the
  upper bound over a finite state space and over `ι → ℤ` for a nonempty finite `ι`, the lower
  bound over an arbitrary measurable state space and over `ℤ^d`. This is the split already made
  for (15.46) and (15.47) themselves.
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
  · have hup := limsup_log_periodicBoundaryGibbs_setOf_mem_div_card_le lam Φ Ψ hs hπ hne B
    rw [hinfB] at hup
    simpa only [hset] using hup

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

end MeasureTheory.GibbsMeasure

end

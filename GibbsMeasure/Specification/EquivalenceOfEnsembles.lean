/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LargeDeviationsCorollaries

/-!
# Corollary (15.58): the equivalence of ensembles (Georgii §15.5)

Georgii's last result of §15.5 identifies the infinite-volume limits of the *microcanonical* Gibbs
distributions

`°γ^{Φ|Ψ,B}_Λ = °γ^Φ_Λ(· | |Λ|⁻¹ °H^Ψ_Λ ∈ B)`  (15.57)

— the Gibbs distributions with periodic boundary conditions conditioned on a prescribed value of
the specific `Ψ`-energy — as *grand canonical* Gibbs measures of a tilted potential:

**(15.58)** *Let `Φ ∈ ℬ_Θ` and `Ψ ∈ ℬ_Θ^k` be such that `t ↦ P(Φ + t·Ψ)` is strictly convex, let
`B ⊆ ℝ^k` be convex with `B° ∩ D_{Ψ|Φ} ≠ ∅`, and let `B̄_min ∩ D°_{Ψ|Φ} ≠ ∅`. Then there is a
unique `t ∈ ℝ^k` with `∅ ≠ clust_{Λ↑S} °γ^{Φ|Ψ,B}_Λ ⊆ 𝒢_Θ(Φ − t·Ψ)`, and `t` is the constant
value of the gradient of `J_Ψ(·|Φ)` on `B̄_min ∩ D°_{Ψ|Φ}`.*

## Main statements

* `MeasureTheory.GibbsMeasure.periodicBoundaryGibbsCond`, **Georgii (15.57)**.
* `MeasureTheory.GibbsMeasure.eventually_isProbabilityMeasure_periodicBoundaryGibbsCond`:
  Georgii's "in view of (15.47) the conditional probabilities are eventually well defined".
* `MeasureTheory.GibbsMeasure.mem_closure_and_specificRelativeEntropy_le_of_tendsto`, the
  **minimum free energy principle**: every limit of the microcanonical fields along a finer filter
  is shift invariant, has specific `Ψ`-energy in `B̄`, and has excess free energy at most
  `m_B = inf_{B̄} J_Ψ(·|Φ)` — hence is a *minimiser* of the free energy under the constraint.
* `MeasureTheory.GibbsMeasure.exists_mapClusterPt_periodicBoundaryGibbsCond`: the **cluster-point
  half**, `clust_{Λ↑S} °γ^{Φ|Ψ,B}_Λ ≠ ∅`.
* `MeasureTheory.GibbsMeasure.exists_subgradient_and_mapClusterPt_subset_invariantG` and its
  `∃!` form `…existsUnique_subgradient_and_mapClusterPt_subset_invariantG`: **Corollary (15.58)**.

## The proof

Georgii's argument, in his order.

* `energyVecPreimage Ψ B` is his `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ`, and the microcanonical event
  `{|Λ|⁻¹ °H^Ψ_Λ ∈ B}` *is* the event `{°R_Λ ∈ C}` by Remark (15.43)(3)
  (`setOf_periodicEmpiricalFieldL_mem_energyVecPreimage`).
* **(15.59)**, `inf_{B̄} J = inf_{B°} J < ∞`, is
  `Potential.BTheta.iInf_ldRate_interior_eq_iInf_closure`. It makes both bounds of Theorem (15.45)
  meet at `m_B`, so `−|Λ|⁻¹ log °γ^Φ_Λ(|Λ|⁻¹ °H^Ψ_Λ ∈ B) → m_B`; only the *lower* bound (15.47)
  is used here, through its exponential form
  `eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_energyVecPreimage`.
* Steps 1 and 2 of the proof of (15.46) for the periodic boundary condition
  (`specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le`) then bound the excess free
  energy of the independent-block field of `°γ^{Φ|Ψ,B}_Λ` by `m_B + ε + o(1)`
  (`eventually_specificRelativeEntropy_tileAverage_periodicBoundaryGibbsCond_le`). Since the
  sublevel sets of `𝓀(·|Φ)` are compact (Proposition (15.14)), the block fields have a cluster
  point; and the cluster-point machinery of Step 2
  (`mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto`) shows that every limit lies in
  `cx̄ C` with `𝓀(·|Φ) ≤ m_B + ε`, hence — letting `ε ↓ 0` — in `𝓜_{C,Φ}`.
* **Georgii's last paragraph**, `σ_Λ(°γ^B_Λ °R_Λ) = °γ^B_Λ`: the microcanonical event is invariant
  under the toroidal shifts, so `°γ^{Φ|Ψ,B}_Λ` and its mean empirical field agree on every event
  of the volume `Λ` (`Potential.empiricalFieldAverage_periodicBoundaryGibbs_cond_apply`). Along a
  sequence of cubes *exhausting* `ℤ^d` every local event is eventually an event of `Λ_n`, so the
  two sequences have the same cluster points
  (`tendsto_ofMeasure_periodicBoundaryGibbsCond_iff`). This is where Georgii's `Λ ↑ S` is used,
  and it is carried as the hypothesis `hexh`.
* **(15.60)**, that a constrained minimiser is a Gibbs measure of the tilted potential, is
  `Potential.BTheta.subset_invariantG_sub_dotPotential`; the Lagrange multiplier `t` is the
  subgradient of `J_Ψ(·|Φ)` at a point of `B̄_min ∩ D°_{Ψ|Φ}`
  (`Potential.BTheta.exists_subgradient_ldRate`), it is the *same* at every point of `B̄_min`
  (`Potential.BTheta.subgradient_ldRate_of_isMinOn`, Georgii's midpoint computation), and it is
  unique (`Potential.BTheta.subgradient_ldRate_unique`, from the strict convexity of the
  pressure). Georgii obtains `t` from Rockafellar's differentiability of a convex function on the
  interior of its essential domain; the existence and uniqueness of the subgradient is what his
  proof consumes, and that is what is proved, in
  `GibbsMeasure/Specification/LargeDeviations.lean`.

## Deviations from Georgii's statement

* Georgii's `°γ^{Φ|Ψ,B}_Λ` is a measure on `E^Λ`; here it is the conditioning of the measure
  `°γ^Φ_Λ` on the whole configuration space (`Potential.periodicBoundaryGibbs`), whose `𝓕_Λ`-
  marginal is his. Cluster points are taken in the topology of local convergence.
* The state space is standard Borel, Georgii's standing hypothesis in §15.5. The topology of local
  convergence is then not first countable, so a cluster point is a limit along a finer filter and
  not along a subsequence; every intermediate statement is filter-wise.
* `hprob`, that the microcanonical distributions are probability measures, is carried as a
  hypothesis. Georgii says they are "eventually well defined"; that is
  `eventually_isProbabilityMeasure_periodicBoundaryGibbsCond`, and one passes to a tail of the
  sequence of cubes, which changes no cluster point.
* `Λ_n ↑ ℤ^d` is the hypothesis `hexh`. Everything except the identification of the cluster points
  of `°γ^{Φ|Ψ,B}_{Λ_n}` with those of its mean empirical fields holds along an arbitrary sequence
  of cubes whose side lengths tend to infinity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

section Ensembles

variable {d : ℕ} [NeZero d] {E : Type*} [MeasurableSpace E]
  {K : Type*} [Fintype K]

/-- Georgii's `C = e_Ψ⁻¹(B) ∩ 𝓟_Θ`, the set of shift-invariant random fields whose specific
`Ψ`-energy lies in `B`. -/
def energyVecPreimage (Ψ : K → Potential.BTheta (Fin d → ℤ) E) (B : Set (K → ℝ)) :
    Set (WithLocalConvergence (Fin d → ℤ) E) :=
  {ρ ∈ invariantRandomFields (Fin d → ℤ) E |
    Potential.BTheta.energyVec Ψ (ρ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ B}

variable [StandardBorelSpace E]

omit [Fintype K] [StandardBorelSpace E] in
/-- **The exponential form of the lower bound (15.47) for the microcanonical event.** For every
`c` strictly above `inf_{B°} J_Ψ(·|Φ)` the microcanonical event eventually has `°γ^Φ_Λ`-probability
at least `e^{−c|Λ|}`. -/
theorem eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_energyVecPreimage
    (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} {c : ℝ}
    (hc : ⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x < (c : EReal)) :
    ∀ᶠ n in atTop, ENNReal.ofReal (Real.exp
        (-(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))))
      ≤ (Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
          {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B} := by
  classical
  rw [← Potential.BTheta.iInf_specificRelativeEntropy_eq_iInf_ldRate Φ Ψ (interior B)] at hc
  simp only [iInf_lt_iff] at hc
  obtain ⟨μ, hμ, hμc⟩ := hc
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  set ρ : WithLocalConvergence (Fin d → ℤ) E := WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩ with hρdef
  have hcoe : (ρ.toMeasure : Measure ((Fin d → ℤ) → E)) = μ := rfl
  set V : Set (WithLocalConvergence (Fin d → ℤ) E) :=
    (fun σ : WithLocalConvergence (Fin d → ℤ) E ↦
      Potential.BTheta.energyVec Ψ (σ.toMeasure : Measure ((Fin d → ℤ) → E))) ⁻¹'
        interior B with hVdef
  have hVopen : IsOpen V :=
    (Potential.BTheta.continuous_energyVec Ψ).isOpen_preimage _ isOpen_interior
  have hνC : energyVecPreimage Ψ B ∈ 𝓝[invariantRandomFields (Fin d → ℤ) E] ρ := by
    refine mem_nhdsWithin.2 ⟨V, hVopen, ?_, ?_⟩
    · rw [hVdef, Set.mem_preimage, hcoe]; exact hμ.2
    · rintro σ ⟨hσ1, hσ2⟩
      exact ⟨hσ2, interior_subset hσ1⟩
  have hr : ((-c : ℝ) : EReal) < -(Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam μ := by
    rw [EReal.coe_neg, EReal.neg_lt_neg_iff]
    exact hμc
  have hev := eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_periodicEmpiricalField_mem
    lam (Φ := (Φ : Potential (Fin d → ℤ) E)) (Potential.BTheta.isShiftInvariant Φ) hμ.1 hνC
    hs hπ hne hr
  filter_upwards [hev] with n hn
  have heq : (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : ℝ) * (-c)
      = -(c * #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ))) := by ring
  rwa [heq] at hn

/-- **Georgii (15.57).** The *microcanonical* Gibbs distribution
`°γ^{Φ|Ψ,B}_Λ = °γ^Φ_Λ(· | |Λ|⁻¹ °H^Ψ_Λ ∈ B)`. -/
abbrev periodicBoundaryGibbsCond (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    (π : (Fin d → ℤ) → (Fin d → ℤ)) (Λ : Finset (Fin d → ℤ)) (B : Set (K → ℝ)) :
    Measure ((Fin d → ℤ) → E) :=
  ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam π Λ)[|
    {ω | (fun j ↦ (#Λ : ℝ)⁻¹
        * (Ψ j : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian π Λ ω) ∈ B}]

omit [NeZero d] [Fintype K] [StandardBorelSpace E] in
/-- The microcanonical distribution conditions on the event `{°R_Λ ∈ C}` of Theorem (15.45). -/
theorem periodicBoundaryGibbsCond_eq (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    {G : AddSubgroup (Fin d → ℤ)} {Λ : Finset (Fin d → ℤ)} {π : (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : Potential.IsTorusReduction G Λ π) (hΛ : Λ.Nonempty) (B : Set (K → ℝ)) :
    periodicBoundaryGibbsCond lam Φ Ψ π Λ B
      = ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam π Λ)[|
          {σ | periodicEmpiricalFieldL π hΛ σ ∈ energyVecPreimage Ψ B}] := by
  have h : {σ : (Fin d → ℤ) → E | periodicEmpiricalFieldL π hΛ σ ∈ energyVecPreimage Ψ B}
      = {ω : (Fin d → ℤ) → E | (fun j ↦ (#Λ : ℝ)⁻¹
        * (Ψ j : Potential (Fin d → ℤ) E).periodicBoundaryHamiltonian π Λ ω) ∈ B} :=
    setOf_periodicEmpiricalFieldL_mem_energyVecPreimage (Fin d) E Ψ B hπ hΛ
  rw [periodicBoundaryGibbsCond, h]

omit [NeZero d] [Fintype K] [StandardBorelSpace E] in
/-- **Georgii, last paragraph of the proof of (15.58).** Along an exhausting sequence of cubes the
microcanonical distributions `°γ^{Φ|Ψ,B}_{Λ_n}` and their mean empirical fields
`°γ^{Φ|Ψ,B}_{Λ_n} °R_{Λ_n}` have the same limits in the topology of local convergence: on the
events of the volume `Λ_n` they are *equal*, by the invariance of the microcanonical event under
the toroidal shifts (`Potential.empiricalFieldAverage_periodicBoundaryGibbs_cond_apply`), and
every local event is an event of `Λ_n` for `n` large. -/
theorem tendsto_ofMeasure_periodicBoundaryGibbsCond_iff
    (lam : Measure E) [IsProbabilityMeasure lam]
    (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
    {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
    {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} (hBm : MeasurableSet B)
    (hexh : ∀ Δ : Finset (Fin d → ℤ), ∀ᶠ n in atTop,
      Δ ⊆ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))
    [hprob : ∀ n, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)]
    {l : Filter ℕ} (hl : l ≤ atTop) (μ : WithLocalConvergence (Fin d → ℤ) E) :
    Tendsto (fun n ↦ (WithSetwiseTopology.ofMeasure
        ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
          WithLocalConvergence (Fin d → ℤ) E)) l (𝓝 μ) ↔
      Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n)
        (periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B)) l (𝓝 μ) := by
  refine tendsto_withLocalConvergence_iff_of_eventually_eq (fun A hA ↦ ?_) μ
  obtain ⟨Δ, hΔ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  filter_upwards [hl (hexh Δ)] with n hn
  have hAn : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))] A :=
    cylinderEvents_mono (by exact_mod_cast hn) _ hΔ
  have hcond := Potential.empiricalFieldAverage_periodicBoundaryGibbs_cond_apply
    (Φ := (Φ : Potential (Fin d → ℤ) E)) lam (Potential.BTheta.isShiftInvariant Φ) (hπ n)
    (hne n)
    (measurableSet_cylinderEvents_setOf_mem_energyVecPreimage Ψ hBm (hπ n) (hne n))
    (fun j ↦ Potential.preimage_periodicTranslate_setOf_periodicEmpiricalFieldL_mem
      (hπ n) (hne n) j _) hAn
  change (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B) A
    = empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n)
        (periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B) A
  rw [periodicBoundaryGibbsCond_eq lam Φ Ψ (hπ n) (hne n) B]
  exact hcond.symm

section MinimumFreeEnergy

variable (lam : Measure E) [IsProbabilityMeasure lam]
  (Φ : Potential.BTheta (Fin d → ℤ) E) (Ψ : K → Potential.BTheta (Fin d → ℤ) E)
  {m : ℕ → Fin d → ℤ} {s : ℕ → ℕ}
  {G : ℕ → AddSubgroup (Fin d → ℤ)} {π : ℕ → (Fin d → ℤ) → (Fin d → ℤ)}

omit [Fintype K] [StandardBorelSpace E] in
/-- The finite-volume estimate of Steps 1 and 2 for the microcanonical distributions: if `c`
exceeds `inf_{B°} J_Ψ(·|Φ)`, then eventually the excess free energy of the independent-block field
built from `°γ^{Φ|Ψ,B}_Λ` is at most `c` plus the two correction terms of Georgii's Step 2. -/
theorem eventually_specificRelativeEntropy_tileAverage_periodicBoundaryGibbsCond_le
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) {c : ℝ}
    (hlt : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x) < (c : EReal)) :
    ∀ᶠ n in atTop, (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
        (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
          ((periodicBoundaryGibbsCond lam Φ Ψ (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n) B).map
              (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).restrict))
      ≤ ((c + ((Φ : Potential (Fin d → ℤ) E).pressure lam
            - (Φ : Potential (Fin d → ℤ) E).logPeriodicBoundaryZ lam (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n)
              / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))
          + ((Φ : Potential (Fin d → ℤ) E).specificEnergy
            (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
              ((periodicBoundaryGibbsCond lam Φ Ψ (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n) B).map
                  (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).restrict))
          - (Φ : Potential (Fin d → ℤ) E).specificEnergy
            (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n)
              (periodicBoundaryGibbsCond lam Φ Ψ (π n)
                (Finset.Icc (m n) fun k ↦ m n k + s n) B))) : ℝ) : EReal) := by
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  have hAeq : ∀ n, periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B
      = ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n))[|
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B}] :=
    fun n ↦ periodicBoundaryGibbsCond_eq lam Φ Ψ (hπ n) (hne n) B
  have hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B} := fun n ↦
    measurableSet_cylinderEvents_setOf_mem_energyVecPreimage Ψ hBm (hπ n) (hne n)
  filter_upwards [eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_energyVecPreimage
    lam Φ Ψ hs hπ hne hlt] with n hn
  have hposn : (Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n)
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B} ≠ 0 := by
    refine fun hcon ↦ ?_
    rw [hcon, le_zero_iff, ENNReal.ofReal_eq_zero] at hn
    exact absurd hn (not_le.2 (Real.exp_pos _))
  have hcard : (0 : ℝ) < #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) := by
    exact_mod_cast (hne n).card_pos
  have hbound : -Real.log (((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n)).real
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B})
      / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) ≤ c := by
    rw [div_le_iff₀ hcard]
    have hle := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hn
    have hlogle := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hlogle
    rw [measureReal_def]
    linarith
  have hmain := specificRelativeEntropy_tileAverage_periodicBoundaryGibbs_cond_le lam hΦ
    (m n) (fun _ ↦ s n) (hπ n) (hAmeas n) hposn
  rw [← hAeq n] at hmain
  refine hmain.trans (EReal.coe_le_coe_iff.2 ?_)
  linarith

omit [Fintype K] in
/-- **Georgii's "minimum free energy principle", the analytic core of Corollary (15.58).**
Every limit of the microcanonical fields `°γ^{Φ|Ψ,B}_{Λ_n}` along a finer filter is a
shift-invariant random field with specific `Ψ`-energy in `B̄` whose excess free energy is at most
`m_B = inf_{B̄} J_Ψ(·|Φ)` — that is, a minimiser of the free energy under the constraint. -/
theorem mem_closure_and_specificRelativeEntropy_le_of_tendsto
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {x₀ : K → ℝ} (hx₀B : x₀ ∈ interior B)
    (hx₀ : Potential.BTheta.ldRate lam Φ Ψ x₀ ≠ ⊤)
    [hprob : ∀ n, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)]
    {l : Filter ℕ} (hl : l ≤ atTop) (hlne : l.NeBot)
    {μ : WithLocalConvergence (Fin d → ℤ) E}
    (hlim : Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n)
      (periodicBoundaryGibbsCond lam Φ Ψ (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) B)) l (𝓝 μ)) :
    (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E) ∧
      Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ closure B ∧
      (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
          (μ.toMeasure : Measure ((Fin d → ℤ) → E))
        ≤ ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  have hAeq : ∀ n, periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B
      = ((Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n))[|
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B}] :=
    fun n ↦ periodicBoundaryGibbsCond_eq lam Φ Ψ (hπ n) (hne n) B
  have hAmeas : ∀ n, MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ E)
      ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))]
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B} := fun n ↦
    measurableSet_cylinderEvents_setOf_mem_energyVecPreimage Ψ hBm (hπ n) (hne n)
  -- `m_B` is a real number
  have hmBint : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x)
      = ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x :=
    Potential.BTheta.iInf_ldRate_interior_eq_iInf_closure Φ Ψ hBc hx₀B hx₀
  have hmBtop : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (iInf₂_le x₀ (interior_subset.trans subset_closure hx₀B))
  have hmBnn : (0 : EReal) ≤ ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x :=
    le_iInf₂ fun x _ ↦ Potential.BTheta.ldRate_nonneg
  have hmBbot : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊥ := fun hcon ↦ by
    rw [hcon] at hmBnn; simp at hmBnn
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) = (r : EReal) :=
    ⟨_, (EReal.coe_toReal hmBtop hmBbot).symm⟩
  -- the vanishing correction term
  have hside : ∀ k, Tendsto (fun n ↦ (fun j ↦ m n j + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have hetend : Tendsto (fun n ↦ (Φ : Potential (Fin d → ℤ) E).pressure lam
      - (Φ : Potential (Fin d → ℤ) E).logPeriodicBoundaryZ lam (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ))) atTop (𝓝 0) := by
    have hZ := Potential.tendsto_logPeriodicBoundaryZ_div_card
      (Φ := (Φ : Potential (Fin d → ℤ) E)) lam hΦ hside hπ
    simpa using (tendsto_const_nhds
      (x := (Φ : Potential (Fin d → ℤ) E).pressure lam)).sub hZ
  -- the finite-volume estimate at level `r + ε`
  have hstep : ∀ ε : ℝ, 0 < ε →
      (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantFields (shiftGroup (Fin d → ℤ) E) ∧
      evalLocalEvents (Fin d → ℤ) E μ ∈
        closedConvexHull ℝ (evalLocalEvents (Fin d → ℤ) E '' energyVecPreimage Ψ B) ∧
      (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
        (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ≤ ((r + ε : ℝ) : EReal) := by
    intro ε hε
    have hlt : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x) < ((r + ε : ℝ) : EReal) := by
      rw [hmBint, hr]
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    have hM := (eventually_specificRelativeEntropy_tileAverage_periodicBoundaryGibbsCond_le
      lam Φ Ψ hs hπ hne hBm hlt).filter_mono hl
    have hcond : ∀ᶠ n in l, (periodicBoundaryGibbsCond lam Φ Ψ (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) B)
        {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B}ᶜ = 0 := by
      refine .of_forall fun n ↦ ?_
      rw [hAeq n]
      have hm := cylinderEvents_le_pi (X := fun _ : Fin d → ℤ ↦ E)
        (Δ := ((Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)))
        _ (hAmeas n)
      rw [cond_apply hm, Set.inter_compl_self, measure_empty, mul_zero]
    exact mem_closedConvexHull_and_specificRelativeEntropy_le_of_tendsto lam Φ hs hπ hne hl hlne
      _ hcond (hetend.mono_left hl) hM hlim
  obtain ⟨hinv, hhull, -⟩ := hstep 1 one_pos
  refine ⟨hinv, ?_, ?_⟩
  · -- `μ ∈ C̄`, hence `⟨μ, Ψ⟩ ∈ B̄`
    have hcl : evalLocalEvents (Fin d → ℤ) E μ
        ∈ closure (evalLocalEvents (Fin d → ℤ) E '' energyVecPreimage Ψ B) := by
      have hhullc : closedConvexHull ℝ (evalLocalEvents (Fin d → ℤ) E '' energyVecPreimage Ψ B)
          = closure (evalLocalEvents (Fin d → ℤ) E '' energyVecPreimage Ψ B) := by
        have hconvC : Convex ℝ (evalLocalEvents (Fin d → ℤ) E '' energyVecPreimage Ψ B) :=
          convex_image_evalLocalEvents_energyVecPreimage Ψ hBc
        rw [closedConvexHull_eq_closure_convexHull, hconvC.convexHull_eq]
      exact hhullc ▸ hhull
    have hμC : μ ∈ closure (energyVecPreimage Ψ B) := by
      rw [isEmbedding_evalLocalEvents.closure_eq_preimage_closure_image]
      exact hcl
    have himg := image_closure_subset_closure_image
      (Potential.BTheta.continuous_energyVec Ψ) (Set.mem_image_of_mem _ hμC)
    refine closure_mono ?_ himg
    rintro x ⟨σ, hσ, rfl⟩
    exact hσ.2
  · rw [hr]
    by_contra hgt
    push Not at hgt
    obtain ⟨c', hrc', hc'⟩ := EReal.exists_between_coe_real hgt
    have hrc'R : r < c' := by exact_mod_cast hrc'
    obtain ⟨-, -, hle⟩ := hstep (c' - r) (by linarith)
    rw [show r + (c' - r) = c' by ring] at hle
    exact absurd hle (not_le.2 hc')

omit [Fintype K] in
/-- **Georgii's "the sequence `(°γ̄^B_Λ)` admits at least one cluster point".** The
independent-block fields of the microcanonical distributions eventually lie in one *compact*
sublevel set of the excess free energy (Proposition (15.14)), so they have a cluster point; by
the last paragraph of Georgii's proof of (15.58) it is a cluster point of the microcanonical
distributions themselves. -/
theorem exists_mapClusterPt_periodicBoundaryGibbsCond
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    {x₀ : K → ℝ} (hx₀B : x₀ ∈ interior B)
    (hx₀ : Potential.BTheta.ldRate lam Φ Ψ x₀ ≠ ⊤)
    (hexh : ∀ Δ : Finset (Fin d → ℤ), ∀ᶠ n in atTop,
      Δ ⊆ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))
    [hprob : ∀ n, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)] :
    ∃ μ : WithLocalConvergence (Fin d → ℤ) E,
      MapClusterPt μ atTop fun n ↦ (WithSetwiseTopology.ofMeasure
        ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
        WithLocalConvergence (Fin d → ℤ) E) := by
  classical
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
  have hΦ := Potential.BTheta.isShiftInvariant Φ
  have hmBint : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x)
      = ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x :=
    Potential.BTheta.iInf_ldRate_interior_eq_iInf_closure Φ Ψ hBc hx₀B hx₀
  have hmBtop : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (iInf₂_le x₀ (interior_subset.trans subset_closure hx₀B))
  have hmBnn : (0 : EReal) ≤ ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x :=
    le_iInf₂ fun x _ ↦ Potential.BTheta.ldRate_nonneg
  have hmBbot : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊥ := fun hcon ↦ by
    rw [hcon] at hmBnn; simp at hmBnn
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) = (r : EReal) :=
    ⟨_, (EReal.coe_toReal hmBtop hmBbot).symm⟩
  have hlt : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x) < ((r + 1 : ℝ) : EReal) := by
    rw [hmBint, hr]
    exact EReal.coe_lt_coe_iff.2 (by linarith)
  have hside : ∀ k, Tendsto (fun n ↦ (fun j ↦ m n j + (s n : ℤ)) k - m n k) atTop atTop := by
    intro k
    have h : Tendsto (fun n ↦ ((s n : ℤ))) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
    simpa using h
  have hetend : Tendsto (fun n ↦ (Φ : Potential (Fin d → ℤ) E).pressure lam
      - (Φ : Potential (Fin d → ℤ) E).logPeriodicBoundaryZ lam (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n)
        / #(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ))) atTop (𝓝 0) := by
    have hZ := Potential.tendsto_logPeriodicBoundaryZ_div_card
      (Φ := (Φ : Potential (Fin d → ℤ) E)) lam hΦ hside hπ
    simpa using (tendsto_const_nhds
      (x := (Φ : Potential (Fin d → ℤ) E).pressure lam)).sub hZ
  set M : ℝ := r + 1 + 1 + 2 * ((Φ : Potential (Fin d → ℤ) E).normAt 0).toReal with hM
  have hKcompact : IsCompact {μ' : WithLocalConvergence (Fin d → ℤ) E |
      (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
        (μ'.toMeasure : Measure ((Fin d → ℤ) → E)) ≤ (M : EReal)} :=
    Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le lam Φ M
  have hmemK : ∀ᶠ n in atTop, blockFieldL (m n) (fun _ ↦ s n)
      (periodicBoundaryGibbsCond lam Φ Ψ (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) B)
      ∈ {μ' : WithLocalConvergence (Fin d → ℤ) E |
        (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
          (μ'.toMeasure : Measure ((Fin d → ℤ) → E)) ≤ (M : EReal)} := by
    filter_upwards [eventually_specificRelativeEntropy_tileAverage_periodicBoundaryGibbsCond_le
      lam Φ Ψ hs hπ hne hBm hlt,
      hetend.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn hen
    refine hn.trans (EReal.coe_le_coe_iff.2 ?_)
    have : NeZero (#(Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ))) :=
      ⟨(hne n).card_pos.ne'⟩
    have h1 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (Fin d → ℤ) E))
      (tileAverage (isComplement_Icc (m n) fun _ ↦ s n)
        ((periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B).map
            (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).restrict)))
    have h2 := abs_le.1 (Potential.abs_specificEnergy_le (Φ := (Φ : Potential (Fin d → ℤ) E))
      (empiricalFieldAverage E (π n) (Finset.Icc (m n) fun k ↦ m n k + s n)
        (periodicBoundaryGibbsCond lam Φ Ψ (π n)
          (Finset.Icc (m n) fun k ↦ m n k + s n) B)))
    rw [hM]
    linarith [h1.2, h2.1, hen.le]
  obtain ⟨μ, -, hclus⟩ := hKcompact (f := Filter.map (fun n ↦ blockFieldL (m n) (fun _ ↦ s n)
    (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)) atTop) (Filter.le_principal_iff.2 hmemK)
  obtain ⟨l, hl, hlne, hlim⟩ := MapClusterPt.exists_le_tendsto hclus
  have hemp : Tendsto (fun n ↦ empiricalFieldAverageL (π n) (hne n)
      (periodicBoundaryGibbsCond lam Φ Ψ (π n)
        (Finset.Icc (m n) fun k ↦ m n k + s n) B)) l (𝓝 μ) :=
    (tendsto_blockFieldL_iff_tendsto_empiricalFieldAverageL hs hl hπ hne _ μ).1 hlim
  have hcondlim := (tendsto_ofMeasure_periodicBoundaryGibbsCond_iff lam Φ Ψ hπ hne hBm hexh
    hl μ).2 hemp
  exact ⟨μ, (hlne.map _).mono (le_inf hcondlim (Filter.map_mono hl))⟩

/-- **Georgii Corollary (15.58): the equivalence of ensembles.** -/
theorem exists_subgradient_and_mapClusterPt_subset_invariantG
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    (hexh : ∀ Δ : Finset (Fin d → ℤ), ∀ᶠ n in atTop,
      Δ ⊆ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    (hP : StrictConvexOn ℝ Set.univ fun t : K → ℝ ↦
      ((Φ - Potential.BTheta.dotPotential t Ψ : Potential.BTheta (Fin d → ℤ) E) :
        Potential (Fin d → ℤ) E).pressure lam)
    {x₀ : K → ℝ} (hx₀B : x₀ ∈ interior B)
    (hx₀ : Potential.BTheta.ldRate lam Φ Ψ x₀ ≠ ⊤)
    {a : K → ℝ} (haB : a ∈ closure B)
    (haD : a ∈ interior {z : K → ℝ | Potential.BTheta.ldRate lam Φ Ψ z ≠ ⊤})
    (ham : Potential.BTheta.ldRate lam Φ Ψ a
      = ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x)
    [hprob : ∀ n, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)] :
    ∃ t : K → ℝ,
      (∀ y : K → ℝ, Potential.BTheta.ldRate lam Φ Ψ a
          + ((∑ j, t j * (y j - a j) : ℝ) : EReal) ≤ Potential.BTheta.ldRate lam Φ Ψ y) ∧
      (∃ μ : WithLocalConvergence (Fin d → ℤ) E,
        MapClusterPt μ atTop fun n ↦ (WithSetwiseTopology.ofMeasure
          ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
          WithLocalConvergence (Fin d → ℤ) E)) ∧
      (∀ μ : WithLocalConvergence (Fin d → ℤ) E,
        (MapClusterPt μ atTop fun n ↦ (WithSetwiseTopology.ofMeasure
          ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
          WithLocalConvergence (Fin d → ℤ) E)) →
        (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantG
          (Potential.gibbsSpecificationOfAbsolutelySummable
            (Φ := ((Φ - Potential.BTheta.dotPotential t Ψ :
              Potential.BTheta (Fin d → ℤ) E) : Potential (Fin d → ℤ) E)) lam 1)
          (shiftGroup (Fin d → ℤ) E)) := by
  classical
  have hmBtop : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (iInf₂_le x₀ (interior_subset.trans subset_closure hx₀B))
  have hmBnn : (0 : EReal) ≤ ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x :=
    le_iInf₂ fun x _ ↦ Potential.BTheta.ldRate_nonneg
  have hmBbot : (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) ≠ ⊥ := fun hcon ↦ by
    rw [hcon] at hmBnn; simp at hmBnn
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x) = (r : EReal) :=
    ⟨_, (EReal.coe_toReal hmBtop hmBbot).symm⟩
  have hminV : ∀ z ∈ closure B, (r : EReal) ≤ Potential.BTheta.ldRate lam Φ Ψ z := fun z hz ↦ by
    rw [← hr]; exact iInf₂_le z hz
  have ham' : Potential.BTheta.ldRate lam Φ Ψ a = (r : EReal) := by rw [ham, hr]
  obtain ⟨t, ht⟩ := Potential.BTheta.exists_subgradient_ldRate Φ Ψ haD
  refine ⟨t, ht, exists_mapClusterPt_periodicBoundaryGibbsCond lam Φ Ψ hs hπ hne hBm hBc hx₀B
    hx₀ hexh, ?_⟩
  intro μ hμ
  obtain ⟨l, hl, hlne, hlim⟩ := MapClusterPt.exists_le_tendsto hμ
  have hemp := (tendsto_ofMeasure_periodicBoundaryGibbsCond_iff lam Φ Ψ hπ hne hBm hexh
    hl μ).1 hlim
  obtain ⟨hinv, hEB, hkle⟩ := mem_closure_and_specificRelativeEntropy_le_of_tendsto lam Φ Ψ hs hπ
    hne hBm hBc hx₀B hx₀ hl hlne hemp
  have hJle : Potential.BTheta.ldRate lam Φ Ψ
      (Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((Fin d → ℤ) → E)))
      ≤ (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
        (μ.toMeasure : Measure ((Fin d → ℤ) → E)) :=
    Potential.BTheta.ldRate_le hinv rfl
  have hJeq : Potential.BTheta.ldRate lam Φ Ψ
      (Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((Fin d → ℤ) → E))) = (r : EReal) :=
    le_antisymm (hJle.trans (hkle.trans_eq hr)) (hminV _ hEB)
  have hkeq : (Φ : Potential (Fin d → ℤ) E).specificRelativeEntropy lam
      (μ.toMeasure : Measure ((Fin d → ℤ) → E))
      = Potential.BTheta.ldRate lam Φ Ψ
        (Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((Fin d → ℤ) → E))) :=
    le_antisymm (by rw [hJeq]; exact hkle.trans_eq hr) hJle
  have hcst := Potential.BTheta.subgradient_ldRate_of_isMinOn Φ Ψ hP hBc.closure hminV haB haD
    ham' ht hEB hJeq
  refine Potential.BTheta.subset_invariantG_sub_dotPotential Φ Ψ
    (D := {Potential.BTheta.energyVec Ψ (μ.toMeasure : Measure ((Fin d → ℤ) → E))}) t
    (fun y₀ hy₀ y ↦ ?_) ⟨hinv, rfl, hkeq⟩
  rw [Set.mem_singleton_iff] at hy₀
  subst hy₀
  exact hcst y

omit [Fintype K] [StandardBorelSpace E] in
/-- **Georgii, after (15.57): the microcanonical distributions are eventually well defined.**
If `inf_{B°} J_Ψ(·|Φ) < ∞` then the microcanonical event has positive `°γ^Φ_Λ`-probability for
all large cubes, by the lower bound (15.47). -/
theorem eventually_isProbabilityMeasure_periodicBoundaryGibbsCond
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    {B : Set (K → ℝ)} {c : ℝ}
    (hlt : (⨅ x ∈ interior B, Potential.BTheta.ldRate lam Φ Ψ x) < (c : EReal)) :
    ∀ᶠ n in atTop, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B) := by
  filter_upwards [eventually_ofReal_exp_le_periodicBoundaryGibbs_setOf_energyVecPreimage
    lam Φ Ψ hs hπ hne hlt] with n hn
  have hposn : (Φ : Potential (Fin d → ℤ) E).periodicBoundaryGibbs lam (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n)
      {σ | periodicEmpiricalFieldL (π n) (hne n) σ ∈ energyVecPreimage Ψ B} ≠ 0 := by
    refine fun hcon ↦ ?_
    rw [hcon, le_zero_iff, ENNReal.ofReal_eq_zero] at hn
    exact absurd hn (not_le.2 (Real.exp_pos _))
  rw [periodicBoundaryGibbsCond_eq lam Φ Ψ (hπ n) (hne n) B]
  exact cond_isProbabilityMeasure hposn

/-- **Georgii Corollary (15.58) as he states it:** *there is a unique `t`* with
`∅ ≠ clust_{Λ↑S} °γ^{Φ|Ψ,B}_Λ ⊆ 𝒢_Θ(Φ − t·Ψ)`, namely the gradient of `J_Ψ(·|Φ)` at any point
of `B̄_min ∩ D°_{Ψ|Φ}`. -/
theorem existsUnique_subgradient_and_mapClusterPt_subset_invariantG
    (hs : Tendsto s atTop atTop)
    (hπ : ∀ n, Potential.IsTorusReduction (G n) (Finset.Icc (m n) fun k ↦ m n k + s n) (π n))
    (hne : ∀ n, (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)).Nonempty)
    (hexh : ∀ Δ : Finset (Fin d → ℤ), ∀ᶠ n in atTop,
      Δ ⊆ (Finset.Icc (m n) fun k ↦ m n k + s n : Finset (Fin d → ℤ)))
    {B : Set (K → ℝ)} (hBm : MeasurableSet B) (hBc : Convex ℝ B)
    (hP : StrictConvexOn ℝ Set.univ fun t : K → ℝ ↦
      ((Φ - Potential.BTheta.dotPotential t Ψ : Potential.BTheta (Fin d → ℤ) E) :
        Potential (Fin d → ℤ) E).pressure lam)
    {x₀ : K → ℝ} (hx₀B : x₀ ∈ interior B)
    (hx₀ : Potential.BTheta.ldRate lam Φ Ψ x₀ ≠ ⊤)
    {a : K → ℝ} (haB : a ∈ closure B)
    (haD : a ∈ interior {z : K → ℝ | Potential.BTheta.ldRate lam Φ Ψ z ≠ ⊤})
    (ham : Potential.BTheta.ldRate lam Φ Ψ a
      = ⨅ x ∈ closure B, Potential.BTheta.ldRate lam Φ Ψ x)
    [hprob : ∀ n, IsProbabilityMeasure (periodicBoundaryGibbsCond lam Φ Ψ (π n)
      (Finset.Icc (m n) fun k ↦ m n k + s n) B)] :
    ∃! t : K → ℝ,
      (∀ y : K → ℝ, Potential.BTheta.ldRate lam Φ Ψ a
          + ((∑ j, t j * (y j - a j) : ℝ) : EReal) ≤ Potential.BTheta.ldRate lam Φ Ψ y) ∧
      (∃ μ : WithLocalConvergence (Fin d → ℤ) E,
        MapClusterPt μ atTop fun n ↦ (WithSetwiseTopology.ofMeasure
          ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
          WithLocalConvergence (Fin d → ℤ) E)) ∧
      (∀ μ : WithLocalConvergence (Fin d → ℤ) E,
        (MapClusterPt μ atTop fun n ↦ (WithSetwiseTopology.ofMeasure
          ⟨periodicBoundaryGibbsCond lam Φ Ψ (π n)
            (Finset.Icc (m n) fun k ↦ m n k + s n) B, hprob n⟩ :
          WithLocalConvergence (Fin d → ℤ) E)) →
        (μ.toMeasure : Measure ((Fin d → ℤ) → E)) ∈ invariantG
          (Potential.gibbsSpecificationOfAbsolutelySummable
            (Φ := ((Φ - Potential.BTheta.dotPotential t Ψ :
              Potential.BTheta (Fin d → ℤ) E) : Potential (Fin d → ℤ) E)) lam 1)
          (shiftGroup (Fin d → ℤ) E)) := by
  obtain ⟨t, ht, hex, hsub⟩ := exists_subgradient_and_mapClusterPt_subset_invariantG
    lam Φ Ψ hs hπ hne hexh hBm hBc hP hx₀B hx₀ haB haD ham
  have hatop : Potential.BTheta.ldRate lam Φ Ψ a ≠ ⊤ :=
    mem_of_mem_nhds (mem_interior_iff_mem_nhds.1 haD)
  refine ⟨t, ⟨ht, hex, hsub⟩, fun t' ht' ↦ ?_⟩
  exact Potential.BTheta.subgradient_ldRate_unique Φ Ψ hP hatop ht'.1 ht

end MinimumFreeEnergy

end Ensembles

end MeasureTheory.GibbsMeasure

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Subadditive.Cubes
public import GibbsMeasure.Potential.GibbsTransformation
public import GibbsMeasure.Potential.Periodic
public import GibbsMeasure.Specification.Ergodicity

/-!
# Specific energy and the pressure (Georgii §15.3)

Throughout, `Φ` is an absolutely summable potential (`Potential.IsAbsolutelySummable`, Georgii's
`ℬ`), and for the lattice results it is shift invariant (`Potential.IsShiftInvariant`, Georgii's
`ℬ_Θ`) on `S = ℤ^d`, spelled `ι → ℤ` for a finite type `ι`. Georgii's norm
`‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖` (15.21) is `Φ.normAt 0` (Georgii (2.12) at the origin).

## Main definitions

* `Potential.siteEnergy Φ i = ∑_{A ∋ i} |A|⁻¹ Φ_A` and `Potential.energyDensity Φ = siteEnergy Φ 0`,
  Georgii's `f_Φ` (15.22); for a shift-invariant potential `siteEnergy Φ i = f_Φ ∘ θ_{-i}`
  (`Potential.IsShiftInvariant.siteEnergy_eq`).
* `Potential.specificEnergy Φ μ = μ(f_Φ)`, Georgii's specific energy `⟨μ, Φ⟩` (15.24), (15.27).
* `Potential.couplingWeight Φ Λ Δ = ∑_{A ∩ Λ ≠ ∅, A ∩ Δ ≠ ∅} ‖Φ_A‖`, the interactions coupling
  two volumes.
* `Potential.logZ ν Φ Λ ω = log Z^Φ_Λ(ω)` and `Potential.logSupZ ν Φ Λ = log sup_ω Z^Φ_Λ(ω)`,
  the finite-volume pressures; `Potential.pressureTerm ν Φ Λ = logSupZ Λ + ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`
  is the corrected, exactly subadditive version.
* `Potential.pressure ν Φ`, Georgii's pressure `P(Φ)` (15.31), (15.36), defined as the infimum
  of `|Δ|⁻¹ pressureTerm Δ` over boxes, in the manner of Mathlib's `Subadditive.lim`.

## Main results

* `Potential.abs_siteEnergy_le`: `‖f_Φ‖ ≤ ‖Φ‖₀`, and `Potential.measurable_siteEnergy`.
* `Potential.abs_sum_siteEnergy_sub_hamiltonian_le`
  (`Potential.abs_sum_energyDensity_shift_sub_hamiltonian_le` in Georgii's spelling): the
  finite-volume boundary estimate behind Georgii (15.25),
  `|∑_{i ∈ Λ} f_Φ ∘ θ_{-i} − H_Λ| ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. The right-hand side is half of
  Georgii's `r(Λ, Φ)`; it is `Potential.tail Λ Λ` of `FreeBoundary.lean`.
* `Potential.tendsto_tail_div_card` and
  `Potential.tendsto_iSup_abs_sum_siteEnergy_sub_hamiltonian_div_card`: **Georgii's estimate
  (15.25)** on `ℤ^d`, the boundary term is `o(|Λ|)` along boxes all of whose sides tend to
  infinity, uniformly in the configuration.
* `Potential.tendsto_integral_hamiltonian_div_card`,
  `Potential.tendsto_integral_hamiltonian_juxt_div_card`: **Georgii Theorem (15.23)**, both
  limits, for `μ ∈ 𝓟_Θ` (`invariantFields (shiftGroup _ E)`), with the finite-volume bounds
  `Potential.abs_integral_hamiltonian_sub_le`, `Potential.abs_integral_hamiltonian_juxt_sub_le`.
* `Potential.abs_specificEnergy_sub_le`: **Georgii Remark (15.26)(2)**, `⟨μ, ·⟩` is
  `1`-Lipschitz for `‖·‖₀`, uniformly in `μ`.
* `Potential.hamiltonian_union_add_tsum_eq`: inclusion–exclusion for the Hamiltonian,
  `H_{Λ ∪ Δ} + ∑_{A meets Λ and Δ} Φ_A = H_Λ + H_Δ`.
* `Potential.premodifierZ_boltzmannFactor_union_le`: the factorization estimate
  `Z_{Λ ∪ Δ}(ω) ≤ e^{c(Λ, Δ)} (sup_η Z_Λ(η)) Z_Δ(ω)`; `Potential.pressureTerm_union_le`, its
  consequence `a(Λ ∪ Δ) ≤ a(Λ) + a(Δ)` for disjoint `Λ, Δ`.
* `Potential.abs_logZ_le`: `‖log Z_Λ‖ ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ`, Georgii's finiteness argument in the
  proof of (15.30); `Potential.abs_pressure_le`: `|P(Φ)| ≤ ‖Φ‖₀`.
* `Potential.tendsto_logZ_div_card_pressure`: **Georgii Theorem (15.30)(a)**: for boxes `Λ_j`
  all of whose sides tend to infinity and any boundary conditions `ω_j`,
  `|Λ_j|⁻¹ log Z_{Λ_j}(ω_j) → P(Φ)`; `Potential.tendsto_logZ_div_card_pressure_cube` is the
  statement for cubes with `|Λ_n| → ∞`.
* `Potential.abs_logZ_sub_logZ_le`, `Potential.logZ_smul_add_smul_le`: the finite-volume pressure
  is `1`-Lipschitz in `Φ` for `∑_{i ∈ Λ} ‖·‖ᵢ` and convex (Hölder's inequality).
* `Potential.abs_pressure_sub_le`, `Potential.pressure_smul_add_smul_le`,
  `Potential.convexOn_pressure`: **Georgii Proposition (16.1)(a)**, `P` is `1`-Lipschitz for
  `‖·‖₀` and convex on `ℬ_Θ`. These are the parts of Chapter 16 whose proofs use only the
  finite-volume estimates of this section.

## Proof of the existence of the pressure

Georgii proves (15.30)(a) indirectly, through the specific entropy of §15.2 and Lemma (15.28);
he remarks that a direct proof exists (Israel, *Convexity in the Theory of Lattice Gases*,
Theorem I.2.3). The direct proof is the one formalized here, via Georgii's own Lemma (15.11)
(`BoxSubadditive.tendsto_div_card_of_bddBelow`): the function
`a(Λ) = log sup_ω Z_Λ(ω) + ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` is translation invariant and *exactly*
subadditive on disjoint volumes, because the coupling term `∑_{A meets Λ and Δ} ‖Φ_A‖` in
`log Z_{Λ ∪ Δ} ≤ log Z_Λ + log Z_Δ + c(Λ, Δ)` is absorbed by the tail correction
(`Potential.couplingWeight_add_tailWeight_union_le`). The correction, and the dependence of
`log Z_Λ(ω)` on the boundary condition `ω` (`Potential.abs_logZ_sub_pressureTerm_le`), are both
`o(|Λ|)` by the estimate (15.25), so every `|Λ_j|⁻¹ log Z_{Λ_j}(ω_j)` has the same limit
`P(Φ) = inf_Δ |Δ|⁻¹ a(Δ)`.

The a priori measure `λ` is a probability measure `ν` here, as in Georgii's proofs ("we can
assume that `λ ∈ 𝓟(E, ℰ)`"). For a finite `λ`, `Z^λ_Λ = λ(E)^{|Λ|} Z^{λ/λ(E)}_Λ`
(`Specification.sigmaFiniteLambdaZ_of_smul`), so the pressure for `λ` is `P + log λ(E)`.

Not in this file: Lemma (15.28), Theorem (15.30)(b), (15.32)–(15.35) are statements about the
specific entropy `𝓀(μ)` of Theorem (15.12) and the relative entropy `𝓗_Λ(μ | ν γ_Λ)`, which are
not yet formalized; they are the variational principle proper (§15.4). Remark (15.26)(1) is the
ergodic theorem (14.A8), also not formalized.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Topology
open scoped ENNReal Topology

noncomputable section

/-! ### The energy density (Georgii (15.22)) -/

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ Ψ : Potential S E}

variable (Φ) in
/-- The terms `|A|⁻¹ Φ_A`, `A ∋ i`, of the energy density at the site `i`, extended by zero. -/
def siteEnergyTerms (i : S) (η : S → E) : Finset S → ℝ :=
  {A : Finset S | i ∈ A}.indicator fun A ↦ (#A : ℝ)⁻¹ * Φ A η

variable (Φ) in
/-- Georgii (15.22) at the site `i`: `∑_{A ∋ i} |A|⁻¹ Φ_A`. For a shift-invariant potential
this is `f_Φ ∘ θ_{-i}` (`Potential.IsShiftInvariant.siteEnergy_eq`). -/
def siteEnergy (i : S) (η : S → E) : ℝ := ∑' A, Φ.siteEnergyTerms i η A

variable (Φ) in
/-- **Georgii (15.22).** The energy density `f_Φ = ∑_{A ∋ 0} |A|⁻¹ Φ_A`. -/
abbrev energyDensity [Zero S] : (S → E) → ℝ := Φ.siteEnergy 0

lemma siteEnergyTerms_of_mem {i : S} {A : Finset S} (hA : i ∈ A) (η : S → E) :
    Φ.siteEnergyTerms i η A = (#A : ℝ)⁻¹ * Φ A η :=
  Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hA) _

lemma siteEnergyTerms_of_not_mem {i : S} {A : Finset S} (hA : i ∉ A) (η : S → E) :
    Φ.siteEnergyTerms i η A = 0 :=
  Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hA) _

lemma enorm_siteEnergyTerms_le (i : S) (η : S → E) (A : Finset S) :
    ‖Φ.siteEnergyTerms i η A‖ₑ
      ≤ {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases hA : i ∈ A
  · rw [siteEnergyTerms_of_mem hA,
      Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hA), enorm_mul]
    have hinv : ‖(#A : ℝ)⁻¹‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
      exact ENNReal.ofReal_le_one.2
        (inv_le_one_of_one_le₀ (by exact_mod_cast (card_pos.2 ⟨i, hA⟩)))
    calc ‖(#A : ℝ)⁻¹‖ₑ * ‖Φ A η‖ₑ ≤ 1 * ‖Φ A η‖ₑ := by gcongr
      _ ≤ ⨆ η, ‖Φ A η‖ₑ := by rw [one_mul]; exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η
  · rw [siteEnergyTerms_of_not_mem hA]
    simp

lemma tsum_enorm_siteEnergyTerms_le (i : S) (η : S → E) :
    ∑' A, ‖Φ.siteEnergyTerms i η A‖ₑ ≤ Φ.normAt i :=
  ENNReal.tsum_le_tsum (enorm_siteEnergyTerms_le i η)

lemma summable_siteEnergyTerms [IsAbsolutelySummable Φ] (i : S) (η : S → E) :
    Summable (Φ.siteEnergyTerms i η) :=
  Summable.of_enorm (ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top i)
    (tsum_enorm_siteEnergyTerms_le i η))

/-- `‖f_Φ‖ ≤ ‖Φ‖₀`, at every site. -/
theorem enorm_siteEnergy_le [IsAbsolutelySummable Φ] (i : S) (η : S → E) :
    ‖Φ.siteEnergy i η‖ₑ ≤ Φ.normAt i :=
  le_trans enorm_tsum_le_tsum_enorm (tsum_enorm_siteEnergyTerms_le i η)

/-- **Georgii, after (15.22):** `‖f_Φ‖ ≤ ‖Φ‖₀`. -/
theorem abs_siteEnergy_le [IsAbsolutelySummable Φ] (i : S) (η : S → E) :
    |Φ.siteEnergy i η| ≤ (Φ.normAt i).toReal := by
  have h := enorm_siteEnergy_le (Φ := Φ) i η
  rw [← ENNReal.toReal_le_toReal (by simp) (IsAbsolutelySummable.normAt_ne_top i)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

lemma measurable_sum_siteEnergyTerms [IsPotential Φ] (i : S) (s : Finset (Finset S)) :
    Measurable fun η : S → E ↦ ∑ A ∈ s, Φ.siteEnergyTerms i η A := by
  refine Finset.measurable_sum _ fun A _ ↦ ?_
  by_cases hA : i ∈ A
  · simp only [siteEnergyTerms_of_mem hA]
    exact ((IsPotential.measurable (Φ := Φ) A).mono cylinderEvents_le_pi le_rfl).const_mul _
  · simp only [siteEnergyTerms_of_not_mem hA]
    exact measurable_const

/-- **Georgii, after (15.22):** `f_Φ` is measurable (indeed `f_Φ ∈ 𝓛`). -/
theorem measurable_siteEnergy [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] (i : S) :
    Measurable (Φ.siteEnergy i) :=
  measurable_of_tendsto_metrizable' atTop (fun s ↦ measurable_sum_siteEnergyTerms (Φ := Φ) i s)
    (tendsto_pi_nhds.2 fun η ↦ (summable_siteEnergyTerms i η).hasSum)

/-! #### Linearity in the potential -/

lemma siteEnergyTerms_add (i : S) (η : S → E) :
    (Φ + Ψ).siteEnergyTerms i η = Φ.siteEnergyTerms i η + Ψ.siteEnergyTerms i η := by
  funext A
  by_cases hA : i ∈ A
  · simp only [Pi.add_apply, siteEnergyTerms_of_mem hA, add_apply]; ring
  · simp [siteEnergyTerms_of_not_mem hA]

lemma siteEnergyTerms_sub (i : S) (η : S → E) :
    (Φ - Ψ).siteEnergyTerms i η = Φ.siteEnergyTerms i η - Ψ.siteEnergyTerms i η := by
  funext A
  by_cases hA : i ∈ A
  · simp only [Pi.sub_apply, siteEnergyTerms_of_mem hA, sub_apply]; ring
  · simp [siteEnergyTerms_of_not_mem hA]

lemma siteEnergyTerms_smul (c : ℝ) (i : S) (η : S → E) :
    (c • Φ).siteEnergyTerms i η = c • Φ.siteEnergyTerms i η := by
  funext A
  by_cases hA : i ∈ A
  · simp only [Pi.smul_apply, siteEnergyTerms_of_mem hA, smul_apply, smul_eq_mul]; ring
  · simp [siteEnergyTerms_of_not_mem hA]

lemma siteEnergy_add [IsAbsolutelySummable Φ] [IsAbsolutelySummable Ψ] (i : S) (η : S → E) :
    (Φ + Ψ).siteEnergy i η = Φ.siteEnergy i η + Ψ.siteEnergy i η := by
  rw [siteEnergy, siteEnergyTerms_add]
  exact (summable_siteEnergyTerms i η).tsum_add (summable_siteEnergyTerms i η)

lemma siteEnergy_sub [IsAbsolutelySummable Φ] [IsAbsolutelySummable Ψ] (i : S) (η : S → E) :
    (Φ - Ψ).siteEnergy i η = Φ.siteEnergy i η - Ψ.siteEnergy i η := by
  rw [siteEnergy, siteEnergyTerms_sub]
  exact (summable_siteEnergyTerms i η).tsum_sub (summable_siteEnergyTerms i η)

lemma siteEnergy_smul (c : ℝ) (i : S) (η : S → E) :
    (c • Φ).siteEnergy i η = c * Φ.siteEnergy i η := by
  rw [siteEnergy, siteEnergyTerms_smul, siteEnergy, ← tsum_mul_left]
  rfl

/-! #### The finite-volume boundary estimate behind Georgii (15.25) -/

section BoundaryEstimate

variable [DecidableEq S]

lemma sum_siteEnergyTerms (Λ : Finset S) (η : S → E) (A : Finset S) :
    ∑ i ∈ Λ, Φ.siteEnergyTerms i η A = (#(A ∩ Λ) : ℝ) / #A * Φ A η := by
  have h : ∀ i, Φ.siteEnergyTerms i η A = if i ∈ A then (#A : ℝ)⁻¹ * Φ A η else 0 := fun i ↦ by
    by_cases hi : i ∈ A
    · simp [siteEnergyTerms_of_mem hi, hi]
    · simp [siteEnergyTerms_of_not_mem hi, hi]
  simp_rw [h]
  rw [sum_ite_mem, sum_const, nsmul_eq_mul, inter_comm, div_eq_mul_inv]
  ring

lemma enorm_card_inter_div_mul_le (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖(#(A ∩ Λ) : ℝ) / #A * Φ A η‖ₑ ≤ Φ.termNorm Λ A := by
  by_cases hd : Disjoint A Λ
  · rw [disjoint_iff_inter_eq_empty.1 hd, termNorm_of_disjoint hd]
    simp
  · rw [termNorm_of_not_disjoint hd, enorm_mul]
    have hc : ‖(#(A ∩ Λ) : ℝ) / #A‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity)]
      exact ENNReal.ofReal_le_one.2
        (div_le_one_of_le₀ (by exact_mod_cast card_le_card inter_subset_left) (by positivity))
    calc ‖(#(A ∩ Λ) : ℝ) / #A‖ₑ * ‖Φ A η‖ₑ ≤ 1 * ‖Φ A η‖ₑ := by gcongr
      _ ≤ ⨆ η, ‖Φ A η‖ₑ := by rw [one_mul]; exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η

lemma summable_card_inter_div_mul [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Summable fun A : Finset S ↦ (#(A ∩ Λ) : ℝ) / #A * Φ A η :=
  Summable.of_enorm (ne_top_of_le_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ)
    (ENNReal.tsum_le_tsum (enorm_card_inter_div_mul_le Λ η)))

/-- `∑_{i ∈ Λ} ∑_{A ∋ i} |A|⁻¹ Φ_A = ∑_A (|A ∩ Λ| / |A|) Φ_A`. -/
lemma sum_siteEnergy [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    ∑ i ∈ Λ, Φ.siteEnergy i η = ∑' A : Finset S, (#(A ∩ Λ) : ℝ) / #A * Φ A η := by
  simp only [siteEnergy]
  rw [← Summable.tsum_finsetSum fun i _ ↦ summable_siteEnergyTerms (Φ := Φ) i η]
  exact tsum_congr fun A ↦ sum_siteEnergyTerms Λ η A

/-- The terms of `∑_{i ∈ Λ} f_Φ ∘ θ_{-i} − H_Λ` are dominated by the tail indicator family of
`Potential.tailWeight Λ Λ`. -/
lemma enorm_card_inter_div_mul_sub_hamiltonianTerms_le (Λ : Finset S) (η : S → E)
    (A : Finset S) :
    ‖(#(A ∩ Λ) : ℝ) / #A * Φ A η - Φ.hamiltonianTerms Λ η A‖ₑ
      ≤ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases hd : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint hd, disjoint_iff_inter_eq_empty.1 hd]
    simp
  · rw [hamiltonianTerms_of_not_disjoint hd]
    obtain ⟨x, hxA, -⟩ := not_disjoint_iff.1 hd
    have hA : (0 : ℝ) < #A := by exact_mod_cast card_pos.2 ⟨x, hxA⟩
    by_cases hsub : A ⊆ Λ
    · rw [inter_eq_left.2 hsub, div_self hA.ne', one_mul, sub_self]
      simp
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from
        ⟨hd, hsub⟩), ← sub_one_mul, enorm_mul]
      have hc : ‖(#(A ∩ Λ) : ℝ) / #A - 1‖ₑ ≤ 1 := by
        rw [Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_one.2 (abs_le.2 ⟨?_, ?_⟩)
        · have : (0 : ℝ) ≤ #(A ∩ Λ) / #A := by positivity
          linarith
        · have : (#(A ∩ Λ) : ℝ) / #A ≤ 1 :=
            div_le_one_of_le₀ (by exact_mod_cast card_le_card inter_subset_left) hA.le
          linarith
      calc ‖(#(A ∩ Λ) : ℝ) / #A - 1‖ₑ * ‖Φ A η‖ₑ ≤ 1 * ‖Φ A η‖ₑ := by gcongr
        _ ≤ ⨆ η, ‖Φ A η‖ₑ := by rw [one_mul]; exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η

/-- **The finite-volume boundary estimate behind Georgii (15.25), enorm form.**
`‖∑_{i ∈ Λ} ∑_{A ∋ i} |A|⁻¹ Φ_A − H_Λ‖ₑ ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
theorem enorm_sum_siteEnergy_sub_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S)
    (η : S → E) :
    ‖∑ i ∈ Λ, Φ.siteEnergy i η - Φ.hamiltonian Λ η‖ₑ ≤ Φ.tailWeight Λ Λ := by
  rw [sum_siteEnergy, hamiltonian_eq_tsum,
    ← (summable_card_inter_div_mul Λ η).tsum_sub (summable_hamiltonianTerms Λ η)]
  exact le_trans enorm_tsum_le_tsum_enorm
    (ENNReal.tsum_le_tsum (enorm_card_inter_div_mul_sub_hamiltonianTerms_le Λ η))

/-- **The finite-volume boundary estimate behind Georgii (15.25).** For every finite volume `Λ`
and every configuration, `|∑_{i ∈ Λ} ∑_{A ∋ i} |A|⁻¹ Φ_A − H_Λ| ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`.
For a shift-invariant potential the left-hand side is Georgii's
`|∑_{i ∈ Λ} f_Φ ∘ θ_{-i} − H_Λ|`; the right-hand side is half of Georgii's bound
`r(Λ, Φ) = 2 ∑_{i ∈ Λ} ∑_{A ∋ i, A ⊄ Λ} ‖Φ_A‖`. -/
theorem abs_sum_siteEnergy_sub_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S)
    (η : S → E) :
    |∑ i ∈ Λ, Φ.siteEnergy i η - Φ.hamiltonian Λ η| ≤ Φ.tail Λ Λ := by
  have h := enorm_sum_siteEnergy_sub_hamiltonian_le (Φ := Φ) Λ η
  rw [← ENNReal.toReal_le_toReal (by simp) (tailWeight_ne_top (Φ := Φ) Λ Λ)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), tail] using h

end BoundaryEstimate

/-! #### Changing the boundary condition -/

lemma enorm_hamiltonianTerms_sub_le_of_eqOn [IsPotential Φ] (Λ : Finset S) {η ζ : S → E}
    (h : ∀ i ∈ Λ, η i = ζ i) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A - Φ.hamiltonianTerms Λ ζ A‖ₑ
      ≤ 2 * {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases hd : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint hd, hamiltonianTerms_of_disjoint hd]
    simp
  · rw [hamiltonianTerms_of_not_disjoint hd, hamiltonianTerms_of_not_disjoint hd]
    by_cases hsub : A ⊆ Λ
    · rw [IsPotential.eq_of_eqOn (Φ := Φ) fun x hx ↦ h x (hsub hx), sub_self]
      simp
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from
        ⟨hd, hsub⟩), two_mul]
      exact enorm_sub_le.trans
        (add_le_add (le_iSup (fun η ↦ ‖Φ A η‖ₑ) η) (le_iSup (fun η ↦ ‖Φ A η‖ₑ) ζ))

/-- **Georgii, in the proof of (15.28), enorm form.** Two configurations agreeing on `Λ` have
Hamiltonians in `Λ` differing by at most `2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
theorem enorm_hamiltonian_sub_le_of_eqOn [IsPotential Φ] [IsAbsolutelySummable Φ]
    (Λ : Finset S) {η ζ : S → E} (h : ∀ i ∈ Λ, η i = ζ i) :
    ‖Φ.hamiltonian Λ η - Φ.hamiltonian Λ ζ‖ₑ ≤ 2 * Φ.tailWeight Λ Λ := by
  rw [hamiltonian_eq_tsum, hamiltonian_eq_tsum,
    ← (summable_hamiltonianTerms Λ η).tsum_sub (summable_hamiltonianTerms Λ ζ), tailWeight,
    ← ENNReal.tsum_mul_left]
  exact le_trans enorm_tsum_le_tsum_enorm
    (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_sub_le_of_eqOn Λ h))

/-- **Georgii, in the proof of (15.28).** `|H_Λ(η_Λ ζ_{S∖Λ}) − H_Λ(η_Λ ω_{S∖Λ})| ≤ r(Λ, Φ)`,
with `r(Λ, Φ)` sharpened to `2 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
theorem abs_hamiltonian_sub_le_of_eqOn [IsPotential Φ] [IsAbsolutelySummable Φ]
    (Λ : Finset S) {η ζ : S → E} (h : ∀ i ∈ Λ, η i = ζ i) :
    |Φ.hamiltonian Λ η - Φ.hamiltonian Λ ζ| ≤ 2 * Φ.tail Λ Λ := by
  have h := enorm_hamiltonian_sub_le_of_eqOn (Φ := Φ) Λ h
  rw [← ENNReal.toReal_le_toReal (by simp)
    (ENNReal.mul_ne_top (by simp) (tailWeight_ne_top (Φ := Φ) Λ Λ))] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), tail,
    ENNReal.toReal_mul] using h

/-! #### Inclusion–exclusion for the Hamiltonian, and the coupling between two volumes -/

variable (Φ) in
/-- The interactions coupling two volumes: `∑_{A ∩ Λ ≠ ∅, A ∩ Δ ≠ ∅} ‖Φ_A‖`. -/
def couplingWeight (Λ Δ : Finset S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

lemma couplingWeight_le_tsum_termNorm (Λ Δ : Finset S) :
    Φ.couplingWeight Λ Δ ≤ ∑' A : Finset S, Φ.termNorm Λ A := by
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hA : A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}
  · rw [Set.indicator_of_mem hA, termNorm_of_not_disjoint hA.1]
  · rw [Set.indicator_of_notMem hA]
    exact zero_le

lemma couplingWeight_ne_top [IsAbsolutelySummable Φ] (Λ Δ : Finset S) :
    Φ.couplingWeight Λ Δ ≠ ⊤ :=
  ne_top_of_le_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) (couplingWeight_le_tsum_termNorm Λ Δ)

/-- The coupling terms are dominated by the coupling weight. -/
lemma tsum_enorm_indicator_coupling_le (Λ Δ : Finset S) (η : S → E) :
    ∑' A : Finset S,
      ‖{A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A‖ₑ
      ≤ Φ.couplingWeight Λ Δ := by
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hA : A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
    simp

lemma summable_indicator_coupling [IsAbsolutelySummable Φ] (Λ Δ : Finset S) (η : S → E) :
    Summable fun A : Finset S ↦
      {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A :=
  Summable.of_enorm (ne_top_of_le_ne_top (couplingWeight_ne_top (Φ := Φ) Λ Δ)
    (tsum_enorm_indicator_coupling_le Λ Δ η))

/-- The coupling term is bounded by the coupling weight. -/
lemma enorm_tsum_indicator_coupling_le (Λ Δ : Finset S) (η : S → E) :
    ‖∑' A : Finset S,
      {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A‖ₑ
      ≤ Φ.couplingWeight Λ Δ :=
  le_trans enorm_tsum_le_tsum_enorm (tsum_enorm_indicator_coupling_le Λ Δ η)

lemma abs_tsum_indicator_coupling_le [IsAbsolutelySummable Φ] (Λ Δ : Finset S) (η : S → E) :
    |∑' A : Finset S,
      {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A|
      ≤ (Φ.couplingWeight Λ Δ).toReal := by
  have h := enorm_tsum_indicator_coupling_le (Φ := Φ) Λ Δ η
  rw [← ENNReal.toReal_le_toReal (by simp) (couplingWeight_ne_top (Φ := Φ) Λ Δ)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

section InclusionExclusion

variable [DecidableEq S]

lemma hamiltonianTerms_union_add_indicator (Λ Δ : Finset S) (η : S → E) (A : Finset S) :
    Φ.hamiltonianTerms (Λ ∪ Δ) η A
        + {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A
      = Φ.hamiltonianTerms Λ η A + Φ.hamiltonianTerms Δ η A := by
  by_cases h₁ : Disjoint A Λ <;> by_cases h₂ : Disjoint A Δ
  · rw [hamiltonianTerms_of_disjoint (disjoint_union_right.2 ⟨h₁, h₂⟩),
      hamiltonianTerms_of_disjoint h₁, hamiltonianTerms_of_disjoint h₂,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.1 h₁)]
  · rw [hamiltonianTerms_of_not_disjoint fun h ↦ h₂ (disjoint_union_right.1 h).2,
      hamiltonianTerms_of_disjoint h₁, hamiltonianTerms_of_not_disjoint h₂,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.1 h₁)]
    simp
  · rw [hamiltonianTerms_of_not_disjoint fun h ↦ h₁ (disjoint_union_right.1 h).1,
      hamiltonianTerms_of_not_disjoint h₁, hamiltonianTerms_of_disjoint h₂,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.2 h₂)]
  · rw [hamiltonianTerms_of_not_disjoint fun h ↦ h₁ (disjoint_union_right.1 h).1,
      hamiltonianTerms_of_not_disjoint h₁, hamiltonianTerms_of_not_disjoint h₂,
      Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        ⟨h₁, h₂⟩)]

/-- **Inclusion–exclusion for the Hamiltonian.**
`H_{Λ ∪ Δ} + ∑_{A ∩ Λ ≠ ∅, A ∩ Δ ≠ ∅} Φ_A = H_Λ + H_Δ`. -/
theorem hamiltonian_union_add_tsum_eq [IsAbsolutelySummable Φ] (Λ Δ : Finset S) (η : S → E) :
    Φ.hamiltonian (Λ ∪ Δ) η
        + ∑' A : Finset S,
            {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator (fun A ↦ Φ A η) A
      = Φ.hamiltonian Λ η + Φ.hamiltonian Δ η := by
  rw [hamiltonian_eq_tsum, hamiltonian_eq_tsum, hamiltonian_eq_tsum,
    ← (summable_hamiltonianTerms (Λ ∪ Δ) η).tsum_add (summable_indicator_coupling Λ Δ η),
    ← (summable_hamiltonianTerms Λ η).tsum_add (summable_hamiltonianTerms Δ η)]
  exact tsum_congr fun A ↦ hamiltonianTerms_union_add_indicator Λ Δ η A

/-- Termwise: on disjoint volumes, the tail correction absorbs the coupling. -/
lemma indicator_coupling_add_indicator_tail_union_le {Λ Δ : Finset S} (h : Disjoint Λ Δ)
    (f : Finset S → ℝ≥0∞) (A : Finset S) :
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ}.indicator f A
        + {A : Finset S | ¬ Disjoint A (Λ ∪ Δ) ∧ ¬ A ⊆ Λ ∪ Δ}.indicator f A
      ≤ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}.indicator f A
        + {A : Finset S | ¬ Disjoint A Δ ∧ ¬ A ⊆ Δ}.indicator f A := by
  by_cases h₁ : Disjoint A Λ <;> by_cases h₂ : Disjoint A Δ
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.1 h₁),
      Set.indicator_of_notMem
        (show A ∉ {A : Finset S | ¬ Disjoint A (Λ ∪ Δ) ∧ ¬ A ⊆ Λ ∪ Δ} from
          fun h ↦ h.1 (disjoint_union_right.2 ⟨h₁, h₂⟩))]
    simp
  · -- `A` meets only `Δ`
    rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.1 h₁), zero_add,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from
        fun h ↦ h.1 h₁), zero_add]
    by_cases hu : A ∈ {A : Finset S | ¬ Disjoint A (Λ ∪ Δ) ∧ ¬ A ⊆ Λ ∪ Δ}
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
        (show A ∈ {A : Finset S | ¬ Disjoint A Δ ∧ ¬ A ⊆ Δ} from
          ⟨h₂, fun hs ↦ hu.2 (hs.trans subset_union_right)⟩)]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  · -- `A` meets only `Λ`
    rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        fun h ↦ h.2 h₂), zero_add,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Δ ∧ ¬ A ⊆ Δ} from
        fun h ↦ h.1 h₂), add_zero]
    by_cases hu : A ∈ {A : Finset S | ¬ Disjoint A (Λ ∪ Δ) ∧ ¬ A ⊆ Λ ∪ Δ}
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem
        (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from
          ⟨h₁, fun hs ↦ hu.2 (hs.trans subset_union_left)⟩)]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le
  · -- `A` meets both: then `A ⊄ Λ` and `A ⊄ Δ`
    obtain ⟨x, hxA, hxΔ⟩ := not_disjoint_iff.1 h₂
    obtain ⟨y, hyA, hyΛ⟩ := not_disjoint_iff.1 h₁
    have hsΛ : ¬ A ⊆ Λ := fun hs ↦ disjoint_left.1 h (hs hxA) hxΔ
    have hsΔ : ¬ A ⊆ Δ := fun hs ↦ disjoint_left.1 h hyΛ (hs hyA)
    rw [Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ Disjoint A Δ} from
        ⟨h₁, h₂⟩),
      Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ} from ⟨h₁, hsΛ⟩),
      Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Δ ∧ ¬ A ⊆ Δ} from ⟨h₂, hsΔ⟩)]
    refine add_le_add le_rfl ?_
    by_cases hu : A ∈ {A : Finset S | ¬ Disjoint A (Λ ∪ Δ) ∧ ¬ A ⊆ Λ ∪ Δ}
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      exact zero_le

/-- **The tail correction absorbs the coupling.** For disjoint `Λ, Δ`,
`∑_{A meets Λ and Δ} ‖Φ_A‖ + ∑_{A ∩ (Λ ∪ Δ) ≠ ∅, A ⊄ Λ ∪ Δ} ‖Φ_A‖
  ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖ + ∑_{A ∩ Δ ≠ ∅, A ⊄ Δ} ‖Φ_A‖`. -/
theorem couplingWeight_add_tailWeight_union_le {Λ Δ : Finset S} (h : Disjoint Λ Δ) :
    Φ.couplingWeight Λ Δ + Φ.tailWeight (Λ ∪ Δ) (Λ ∪ Δ)
      ≤ Φ.tailWeight Λ Λ + Φ.tailWeight Δ Δ := by
  simp only [couplingWeight, tailWeight, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun A ↦ indicator_coupling_add_indicator_tail_union_le h _ A

end InclusionExclusion

/-! ### The partition function of a union of volumes -/

section PartitionFunction

variable [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]

lemma iSup_premodifierZ_boltzmannFactor_le (β : ℝ) (Λ : Finset S) :
    ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω
      ≤ ENNReal.ofReal (Real.exp (|β| * Φ.hamiltonianBound Λ)) :=
  iSup_le fun ω ↦ premodifierZ_boltzmannFactor_le (Φ := Φ) ν β Λ ω

lemma iSup_premodifierZ_boltzmannFactor_ne_top (β : ℝ) (Λ : Finset S) :
    ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_premodifierZ_boltzmannFactor_le ν β Λ)

lemma le_iSup_premodifierZ_boltzmannFactor (β : ℝ) (Λ : Finset S) :
    ENNReal.ofReal (Real.exp (-(|β| * Φ.hamiltonianBound Λ)))
      ≤ ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  exact (le_premodifierZ_boltzmannFactor (Φ := Φ) ν β Λ (Classical.arbitrary _)).trans
    (le_iSup _ _)

lemma iSup_premodifierZ_boltzmannFactor_ne_zero (β : ℝ) (Λ : Finset S) :
    ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by simp [Real.exp_pos]) (le_iSup_premodifierZ_boltzmannFactor ν β Λ))

/-- The inner factor is dominated by `e^{c(Λ, Δ)} h_Δ`. -/
lemma ofReal_exp_neg_hamiltonian_union_sub_le [DecidableEq S] (Λ Δ : Finset S) (η : S → E) :
    ENNReal.ofReal (Real.exp (-(Φ.hamiltonian (Λ ∪ Δ) η - Φ.hamiltonian Λ η)))
      ≤ ENNReal.ofReal (Real.exp (Φ.couplingWeight Λ Δ).toReal) * Φ.boltzmannFactor 1 Δ η := by
  have hie := hamiltonian_union_add_tsum_eq (Φ := Φ) Λ Δ η
  have hc := (abs_le.1 (abs_tsum_indicator_coupling_le (Φ := Φ) Λ Δ η)).2
  rw [boltzmannFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  linarith

variable [Countable S] [IsPotential Φ]

/-- Strong consistency of the independent specification (Georgii (1.25)), integrated:
`Z_{Λ ∪ Δ}(ω) = ∫ λ_Δ(dη | ω) ∫ λ_Λ(dζ | η) h_{Λ ∪ Δ}(ζ)`. -/
lemma premodifierZ_boltzmannFactor_union_eq [DecidableEq S] (Λ Δ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) (Λ ∪ Δ) ω
      = ∫⁻ η, ∫⁻ ζ, Φ.boltzmannFactor 1 (Λ ∪ Δ) ζ ∂(Specification.isssd ν Λ η)
          ∂(Specification.isssd ν Δ ω) := by
  have hcomp := congrArg (fun κ ↦ κ ω) (Specification.isssdFun_comp_isssdFun (S := S) (E := E) ν Λ Δ)
  simp only [Kernel.comap_apply, id] at hcomp
  change ∫⁻ x, Φ.boltzmannFactor 1 (Λ ∪ Δ) x ∂(Specification.isssdFun ν (Λ ∪ Δ) ω) = _
  rw [← hcomp, Kernel.lintegral_comp _ _ _ (measurable_boltzmannFactor (Φ := Φ) 1 (Λ ∪ Δ))]
  rfl

/-- Georgii (2.6) under the inner resampling: `λ_Λ(h_{Λ ∪ Δ} | η) = e^{-(H_{Λ ∪ Δ} - H_Λ)(η)} Z_Λ(η)`. -/
lemma lintegral_boltzmannFactor_union_isssd_eq [DecidableEq S] (Λ Δ : Finset S) (η : S → E) :
    ∫⁻ ζ, Φ.boltzmannFactor 1 (Λ ∪ Δ) ζ ∂(Specification.isssd ν Λ η)
      = ENNReal.ofReal (Real.exp (-(Φ.hamiltonian (Λ ∪ Δ) η - Φ.hamiltonian Λ η)))
          * Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η := by
  rw [Specification.lintegral_isssd_eq Λ η (measurable_boltzmannFactor (Φ := Φ) 1 (Λ ∪ Δ)),
    Specification.premodifierZ, Specification.relZ,
    Specification.lintegral_isssd_eq Λ η (measurable_boltzmannFactor (Φ := Φ) 1 Λ),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ ↦ ?_
  have h := hamiltonian_sub_eq_of_subset_eqOn_compl (Φ := Φ) (η := η)
    (ζ := juxt (Λ : Set S) η ζ) (subset_union_left (s₂ := Δ))
    fun s hs ↦ juxt_apply_of_not_mem (by simpa using hs) ζ
  rw [boltzmannFactor, boltzmannFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  linarith

/-- **The factorization estimate for the partition function.**
`Z_{Λ ∪ Δ}(ω) ≤ e^{c(Λ, Δ)} (sup_η Z_Λ(η)) Z_Δ(ω)`, where
`c(Λ, Δ) = ∑_{A ∩ Λ ≠ ∅, A ∩ Δ ≠ ∅} ‖Φ_A‖` is the coupling between the two volumes. -/
theorem premodifierZ_boltzmannFactor_union_le [DecidableEq S] (Λ Δ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) (Λ ∪ Δ) ω
      ≤ ENNReal.ofReal (Real.exp (Φ.couplingWeight Λ Δ).toReal)
          * (⨆ η, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η)
          * Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Δ ω := by
  rw [premodifierZ_boltzmannFactor_union_eq]
  calc ∫⁻ η, ∫⁻ ζ, Φ.boltzmannFactor 1 (Λ ∪ Δ) ζ ∂(Specification.isssd ν Λ η)
          ∂(Specification.isssd ν Δ ω)
      = ∫⁻ η, ENNReal.ofReal (Real.exp (-(Φ.hamiltonian (Λ ∪ Δ) η - Φ.hamiltonian Λ η)))
          * Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η
          ∂(Specification.isssd ν Δ ω) :=
        lintegral_congr fun η ↦ lintegral_boltzmannFactor_union_isssd_eq ν Λ Δ η
    _ ≤ ∫⁻ η, (ENNReal.ofReal (Real.exp (Φ.couplingWeight Λ Δ).toReal)
          * ⨆ η, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η)
          * Φ.boltzmannFactor 1 Δ η ∂(Specification.isssd ν Δ ω) := by
        refine lintegral_mono fun η ↦ ?_
        calc _ ≤ (ENNReal.ofReal (Real.exp (Φ.couplingWeight Λ Δ).toReal)
              * Φ.boltzmannFactor 1 Δ η)
              * ⨆ η, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η :=
              mul_le_mul' (ofReal_exp_neg_hamiltonian_union_sub_le Λ Δ η) (le_iSup _ η)
          _ = _ := by ring
    _ = _ := by
        rw [lintegral_const_mul' _ _
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (iSup_premodifierZ_boltzmannFactor_ne_top ν 1 Λ))]
        rfl

end PartitionFunction

/-! ### Translation invariance under the shift -/

section Shift

variable [AddCommGroup S]

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii (5.6)(c) for the shift.** `Z_{Λ + j}(θ_j ω) = Z_Λ(ω)` for a shift-invariant
potential. -/
lemma premodifierZ_boltzmannFactor_translate (hΦ : Φ.IsShiftInvariant) (β : ℝ) (j : S)
    (Λ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) (translate Λ j)
        ((shift E j).toFun ω)
      = Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω := by
  have h := Specification.premodifierZ_map ν (shift E j) (measurePreserving_shift_spin ν j)
    (Φ.boltzmannFactor β) (translate Λ j) ((shift E j).toFun ω)
  have hfun : (fun Λ η ↦ Φ.boltzmannFactor β (Λ.map (shift E j).sites.symm.toEmbedding)
      ((shift E j).inv.toFun η)) = Φ.boltzmannFactor β := by
    funext Λ η
    rw [← boltzmannFactor_map', hΦ j]
  rw [hfun] at h
  rw [h, (shift E j).inv_toFun_toFun ω]
  congr 1
  exact Finset.map_symm_map (shift E j).sites Λ

lemma iSup_premodifierZ_boltzmannFactor_translate (hΦ : Φ.IsShiftInvariant) (β : ℝ) (j : S)
    (Λ : Finset S) :
    ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) (translate Λ j) ω
      = ⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω := by
  rw [← (shift E j).toMeasurableEquiv.toEquiv.iSup_comp (g := fun ω ↦
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) (translate Λ j) ω)]
  exact iSup_congr fun ω ↦ premodifierZ_boltzmannFactor_translate ν hΦ β j Λ ω

/-- The tail of a shift-invariant potential is translation invariant. -/
lemma tailWeight_translate (hΦ : Φ.IsShiftInvariant) (Δ Λ : Finset S) (j : S) :
    Φ.tailWeight (translate Δ j) (translate Λ j) = Φ.tailWeight Δ Λ := by
  unfold tailWeight
  rw [← (Equiv.addRight j).finsetOrderIso.toEquiv.tsum_eq]
  refine tsum_congr fun A ↦ ?_
  change {B : Finset S | ¬ Disjoint B (translate Λ j) ∧ ¬ B ⊆ translate Δ j}.indicator
    (fun B ↦ ⨆ η, ‖Φ B η‖ₑ) (translate A j) = _
  have hmem : (¬ Disjoint (translate A j) (translate Λ j) ∧ ¬ translate A j ⊆ translate Δ j)
      ↔ (¬ Disjoint A Λ ∧ ¬ A ⊆ Δ) := by
    simp only [translate, Finset.disjoint_map, Finset.map_subset_map]
  by_cases hA : A ∈ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}
  · rw [Set.indicator_of_mem (show translate A j ∈
        {B : Finset S | ¬ Disjoint B (translate Λ j) ∧ ¬ B ⊆ translate Δ j} from hmem.2 hA),
      Set.indicator_of_mem hA, iSup_enorm_translate hΦ]
  · rw [Set.indicator_of_notMem (show translate A j ∉
        {B : Finset S | ¬ Disjoint B (translate Λ j) ∧ ¬ B ⊆ translate Δ j} from mt hmem.1 hA),
      Set.indicator_of_notMem hA]

lemma tail_translate (hΦ : Φ.IsShiftInvariant) (Δ Λ : Finset S) (j : S) :
    Φ.tail (translate Δ j) (translate Λ j) = Φ.tail Δ Λ := by
  rw [tail, tail, tailWeight_translate hΦ]

end Shift

/-! ### Georgii's estimate (15.25) on the lattice `ℤ^d` -/

section TailEstimate

/-- `∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖ ≤ ∑_{i ∈ Λ} ∑_{A ∋ i, A ⊄ Λ} ‖Φ_A‖`. -/
lemma tailWeight_self_le_sum (Λ : Finset S) : Φ.tailWeight Λ Λ ≤ ∑ i ∈ Λ, Φ.tailWeight Λ {i} := by
  unfold tailWeight
  rw [← Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hA : A ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Λ}
  · rw [Set.indicator_of_mem hA]
    obtain ⟨x, hxA, hxΛ⟩ := not_disjoint_iff.1 hA.1
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i ↦
      {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Λ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A)
      (fun _ _ ↦ zero_le) hxΛ)
    rw [Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A {x} ∧ ¬ A ⊆ Λ} from
      ⟨by simpa [disjoint_singleton_right] using hxA, hA.2⟩)]
  · rw [Set.indicator_of_notMem hA]
    exact zero_le

/-- The tail beyond a larger volume is smaller. -/
lemma tailWeight_anti {Δ Δ' : Finset S} (h : Δ ⊆ Δ') (Λ : Finset S) :
    Φ.tailWeight Δ' Λ ≤ Φ.tailWeight Δ Λ :=
  ENNReal.tsum_le_tsum fun A ↦ Set.indicator_le_indicator_of_subset
    (fun B (hB : B ∈ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ'}) ↦
      (⟨hB.1, fun hs ↦ hB.2 (hs.trans h)⟩ : B ∈ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}))
    (fun _ ↦ zero_le) A

/-- `∑_{A ∋ i, A ⊄ Δ} ‖Φ_A‖ ≤ ‖Φ‖ᵢ`. -/
lemma tailWeight_singleton_le_normAt (Δ : Finset S) (i : S) : Φ.tailWeight Δ {i} ≤ Φ.normAt i :=
  (tailWeight_le_tsum_termNorm Δ {i}).trans (by simpa using tsum_termNorm_le (Φ := Φ) {i})

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Translating a box is `Finset.image (· + i)` (the spelling of `BoxSubadditive`) as well as
`Potential.translate` (the spelling of Georgii (5.8)). -/
lemma image_add_right_eq_translate (Λ : Finset (ι → ℤ)) (i : ι → ℤ) :
    Λ.image (· + i) = translate Λ i := by
  rw [translate, Finset.map_eq_image]
  rfl

/-- Every finite set of sites lies in a cube centred at the origin. -/
lemma exists_subset_Icc_const (Δ₀ : Finset (ι → ℤ)) :
    ∃ R : ℕ, Δ₀ ⊆ Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) := by
  refine ⟨Δ₀.sup fun x ↦ ∑ k, (x k).natAbs, fun x hx ↦ ?_⟩
  have hle : ∀ k, (x k).natAbs ≤ Δ₀.sup fun x ↦ ∑ k, (x k).natAbs := fun k ↦
    (Finset.single_le_sum (f := fun k ↦ (x k).natAbs) (fun _ _ ↦ Nat.zero_le _) (mem_univ k)).trans
      (Finset.le_sup (f := fun x ↦ ∑ k, (x k).natAbs) hx)
  rw [mem_Icc]
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩ <;> · have := hle k; beta_reduce; omega

/-- A site of the interior `∏ₖ [mₖ + R, nₖ − R]` carries a translate of the cube of radius `R`
inside `∏ₖ [mₖ, nₖ]`. -/
lemma translate_Icc_const_subset {m n i : ι → ℤ} {R : ℕ}
    (hi : i ∈ Icc (fun k ↦ m k + R) (fun k ↦ n k - R)) :
    translate (Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) i ⊆ Icc m n := by
  intro x hx
  rw [mem_translate, mem_Icc] at hx
  rw [mem_Icc] at hi ⊢
  refine ⟨fun k ↦ ?_, fun k ↦ ?_⟩
  · have h1 : -(R : ℤ) ≤ x k - i k := hx.1 k
    have h3 : m k + R ≤ i k := hi.1 k
    show m k ≤ x k
    omega
  · have h2 : x k - i k ≤ R := hx.2 k
    have h4 : i k ≤ n k - R := hi.2 k
    show x k ≤ n k
    omega

lemma Icc_add_sub_subset (m n : ι → ℤ) (R : ℕ) :
    Icc (fun k ↦ m k + R) (fun k ↦ n k - R) ⊆ Icc m n :=
  Icc_subset_Icc (fun k ↦ by simp) (fun k ↦ by simp)

variable {Φ : Potential (ι → ℤ) E}

/-- **Georgii, in the proof of (15.25).** For a shift-invariant potential and a box
`Λ = ∏ₖ [mₖ, nₖ]`, with `Δ` the cube of radius `R` and `I = ∏ₖ [mₖ + R, nₖ − R]` the sites `i`
with `Δ + i ⊆ Λ`:
`∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖ ≤ |Λ| ∑_{A ∋ 0, A ⊄ Δ} ‖Φ_A‖ + |Λ ∖ I| ‖Φ‖₀`. -/
theorem tailWeight_Icc_le (hΦ : Φ.IsShiftInvariant) (m n : ι → ℤ) (R : ℕ) :
    Φ.tailWeight (Icc m n) (Icc m n)
      ≤ #(Icc m n) * Φ.tailWeight (Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) {0}
        + #(Icc m n \ Icc (fun k ↦ m k + R) (fun k ↦ n k - R)) * Φ.normAt 0 := by
  set Λ := Icc m n with hΛ
  set I := Icc (fun k ↦ m k + R) (fun k ↦ n k - R) with hI
  set C := Icc (fun _ : ι ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ)) with hC
  refine (tailWeight_self_le_sum Λ).trans ?_
  rw [← Finset.sum_sdiff (Icc_add_sub_subset m n R), add_comm]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ I, Φ.tailWeight Λ {i} ≤ ∑ i ∈ I, Φ.tailWeight C {0} := by
          refine Finset.sum_le_sum fun i hi ↦ ?_
          calc Φ.tailWeight Λ {i} ≤ Φ.tailWeight (translate C i) {i} :=
                tailWeight_anti (translate_Icc_const_subset hi) {i}
            _ = Φ.tailWeight C {0} := by
                have h := tailWeight_translate hΦ C {0} i
                rwa [show translate ({0} : Finset (ι → ℤ)) i = {i} by simp [translate]] at h
      _ = #I * Φ.tailWeight C {0} := by rw [sum_const, nsmul_eq_mul]
      _ ≤ #Λ * Φ.tailWeight C {0} := by
          gcongr
          exact Icc_add_sub_subset m n R
  · calc ∑ i ∈ Λ \ I, Φ.tailWeight Λ {i} ≤ ∑ i ∈ Λ \ I, Φ.normAt 0 :=
          Finset.sum_le_sum fun i _ ↦
            (tailWeight_singleton_le_normAt Λ i).trans_eq (hΦ.normAt_eq i)
      _ = #(Λ \ I) * Φ.normAt 0 := by rw [sum_const, nsmul_eq_mul]

/-- The real form of `Potential.tailWeight_Icc_le`. -/
theorem tail_Icc_le [IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant) (m n : ι → ℤ) (R : ℕ) :
    Φ.tail (Icc m n) (Icc m n)
      ≤ #(Icc m n) * Φ.tail (Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) {0}
        + #(Icc m n \ Icc (fun k ↦ m k + R) (fun k ↦ n k - R)) * (Φ.normAt 0).toReal := by
  have h := tailWeight_Icc_le hΦ m n R
  have hne : #(Icc m n) * Φ.tailWeight (Icc (fun _ ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) {0}
      + #(Icc m n \ Icc (fun k ↦ m k + R) (fun k ↦ n k - R)) * Φ.normAt 0 ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (tailWeight_ne_top _ _),
      ENNReal.mul_ne_top (by simp) (IsAbsolutelySummable.normAt_ne_top 0)⟩
  have := ENNReal.toReal_mono hne h
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (tailWeight_ne_top _ _))
    (ENNReal.mul_ne_top (by simp) (IsAbsolutelySummable.normAt_ne_top 0)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at this

/-- **Georgii, the estimate (15.25).** For a shift-invariant `Φ ∈ ℬ`, the boundary term
`∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` is `o(|Λ|)` along boxes all of whose sides tend to infinity. -/
theorem tendsto_tail_div_card [IsAbsolutelySummable Φ] (hΦ : Φ.IsShiftInvariant) {κ : Type*}
    {l : Filter κ} {m n : κ → ι → ℤ} (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j)) / #(Icc (m j) (n j))) l
      (𝓝 0) := by
  set N := (Φ.normAt 0).toReal
  have hbox : ∀ᶠ j in l, m j ≤ n j :=
    eventually_all.2 fun k ↦ ((h k).eventually_ge_atTop 0).mono fun _ hj ↦ by
      simpa [sub_nonneg] using hj
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R : ℕ, Φ.tail (Icc (fun _ : ι ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) {0} < ε / 2 := by
    obtain ⟨Δ₀, hΔ₀⟩ := Filter.eventually_atTop.1
      ((tendsto_tail_atTop (Φ := Φ) {0}).eventually (gt_mem_nhds (half_pos hε)))
    obtain ⟨R, hR⟩ := exists_subset_Icc_const Δ₀
    exact ⟨R, hΔ₀ _ hR⟩
  set t := Φ.tail (Icc (fun _ : ι ↦ -(R : ℤ)) (fun _ ↦ (R : ℤ))) {0}
  set ρ : κ → ℝ := fun j ↦ (#(Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R)) : ℝ) / #(Icc (m j) (n j))
  have hρ : Tendsto ρ l (𝓝 1) := Finset.tendsto_card_Icc_div_card_Icc h R
  have hsmall : ∀ᶠ j in l, N * (1 - ρ j) < ε / 2 := by
    have : Tendsto (fun j ↦ N * (1 - ρ j)) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := N)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hρ)
    exact this.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hbox, hsmall] with j hj hjs
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (tail_nonneg _ _) (Nat.cast_nonneg _))]
  have hcard : (0 : ℝ) < #(Icc (m j) (n j)) := by exact_mod_cast (nonempty_Icc.2 hj).card_pos
  have hI := Icc_add_sub_subset (m j) (n j) R
  have hsd : (#(Icc (m j) (n j) \ Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R)) : ℝ)
      = #(Icc (m j) (n j)) - #(Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R)) := by
    have := card_sdiff_add_card_eq_card hI
    have h' : ((#(Icc (m j) (n j) \ Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R))
        + #(Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R)) : ℕ) : ℝ) = #(Icc (m j) (n j)) := by
      exact_mod_cast this
    push_cast at h'
    linarith
  have hest := tail_Icc_le hΦ (m j) (n j) R
  rw [hsd] at hest
  have e : ((#(Icc (m j) (n j)) : ℝ) - #(Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R))) * N
      = #(Icc (m j) (n j)) * (N * (1 - ρ j)) := by
    simp only [ρ]
    field_simp
  rw [div_lt_iff₀ hcard]
  calc Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j))
      ≤ #(Icc (m j) (n j)) * t
        + ((#(Icc (m j) (n j)) : ℝ) - #(Icc (fun k ↦ m j k + R) (fun k ↦ n j k - R))) * N := hest
    _ = #(Icc (m j) (n j)) * (t + N * (1 - ρ j)) := by rw [e]; ring
    _ < #(Icc (m j) (n j)) * ε := mul_lt_mul_of_pos_left (by linarith) hcard
    _ = ε * #(Icc (m j) (n j)) := mul_comm _ _

end TailEstimate

/-! ### The site energy is the shifted energy density -/

section SiteEnergyShift

variable [AddCommGroup S]

/-- **Georgii (15.22) at a site.** For a shift-invariant potential,
`∑_{A ∋ i} |A|⁻¹ Φ_A = f_Φ ∘ θ_{-i}`. -/
lemma IsShiftInvariant.siteEnergy_eq (hΦ : Φ.IsShiftInvariant) (i : S) (η : S → E) :
    Φ.siteEnergy i η = Φ.energyDensity ((shift E (-i)).toFun η) := by
  unfold energyDensity siteEnergy
  rw [← (Equiv.addRight i).finsetOrderIso.toEquiv.tsum_eq]
  refine tsum_congr fun A ↦ ?_
  change Φ.siteEnergyTerms i η (translate A i) = Φ.siteEnergyTerms 0 ((shift E (-i)).toFun η) A
  by_cases hA : 0 ∈ A
  · have hi : i ∈ translate A i := by simpa using hA
    rw [siteEnergyTerms_of_mem hi, siteEnergyTerms_of_mem hA, hΦ.translate_apply i A η,
      Finset.card_map]
    congr 2
    funext k
    simp [sub_neg_eq_add]
  · have hi : i ∉ translate A i := by simpa using hA
    rw [siteEnergyTerms_of_not_mem hi, siteEnergyTerms_of_not_mem hA]

/-- **Georgii (15.25), the finite-volume estimate in Georgii's own spelling.**
`|∑_{i ∈ Λ} f_Φ ∘ θ_{-i} − H_Λ| ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
theorem abs_sum_energyDensity_shift_sub_hamiltonian_le [DecidableEq S] [IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant) (Λ : Finset S) (η : S → E) :
    |∑ i ∈ Λ, Φ.energyDensity ((shift E (-i)).toFun η) - Φ.hamiltonian Λ η| ≤ Φ.tail Λ Λ := by
  simp_rw [← hΦ.siteEnergy_eq]
  exact abs_sum_siteEnergy_sub_hamiltonian_le Λ η

end SiteEnergyShift

/-! ### The specific energy (Georgii (15.24), (15.27)) -/

section SpecificEnergy

variable (Φ) in
/-- **Georgii (15.24), (15.27).** The specific (internal) energy per site
`⟨μ, Φ⟩ = μ(f_Φ)` of `μ` relative to `Φ`. -/
def specificEnergy [Zero S] (μ : Measure (S → E)) : ℝ := ∫ η, Φ.energyDensity η ∂μ

variable [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ]

lemma integrable_siteEnergy (i : S) (μ : Measure (S → E)) [IsFiniteMeasure μ] :
    Integrable (Φ.siteEnergy i) μ :=
  Integrable.of_bound (measurable_siteEnergy i).aestronglyMeasurable _
    (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact abs_siteEnergy_le i η)

lemma integrable_hamiltonian (Λ : Finset S) (μ : Measure (S → E)) [IsFiniteMeasure μ] :
    Integrable (Φ.hamiltonian Λ) μ :=
  Integrable.of_bound (measurable_hamiltonian Λ).aestronglyMeasurable _
    (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact abs_hamiltonian_le Λ η)

/-- `H_Λ(σ_Λ ω_{S∖Λ})`, as a function of `σ`, is integrable. -/
lemma integrable_hamiltonian_juxt (Λ : Finset S) (ω : S → E) (μ : Measure (S → E))
    [IsFiniteMeasure μ] :
    Integrable (fun σ ↦ Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i)) μ := by
  have hmeas : Measurable fun σ : S → E ↦ Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) :=
    (measurable_hamiltonian Λ).comp
      (Measurable.juxt.comp (measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : S)))
  exact Integrable.of_bound hmeas.aestronglyMeasurable _
    (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact abs_hamiltonian_le Λ _)

/-- **Georgii Remark (15.26)(2).** The specific energy is `1`-Lipschitz in the potential for
`‖·‖₀`, uniformly in `μ`: `|⟨μ, Φ⟩ − ⟨μ, Ψ⟩| ≤ ‖Φ − Ψ‖₀`. -/
theorem abs_specificEnergy_sub_le [Zero S] [IsPotential Ψ] [IsAbsolutelySummable Ψ]
    (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    |Φ.specificEnergy μ - Ψ.specificEnergy μ| ≤ ((Φ - Ψ).normAt 0).toReal := by
  have : IsAbsolutelySummable (Φ - Ψ) := IsAbsolutelySummable.sub ‹_› ‹_›
  rw [specificEnergy, specificEnergy,
    ← integral_sub (integrable_siteEnergy 0 μ) (integrable_siteEnergy 0 μ)]
  have h : ∀ η, Φ.energyDensity η - Ψ.energyDensity η = (Φ - Ψ).energyDensity η :=
    fun η ↦ (siteEnergy_sub 0 η).symm
  simp_rw [h]
  calc |∫ η, (Φ - Ψ).energyDensity η ∂μ| = ‖∫ η, (Φ - Ψ).energyDensity η ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ((Φ - Ψ).normAt 0).toReal * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun η ↦ by
          rw [Real.norm_eq_abs]; exact abs_siteEnergy_le 0 η)
    _ = ((Φ - Ψ).normAt 0).toReal := by simp

variable [AddCommGroup S]

omit [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ] in
/-- For a shift-invariant potential and a shift-invariant measure, `μ(f_Φ ∘ θ_{-i}) = μ(f_Φ)`. -/
lemma integral_siteEnergy_of_measurePreserving_shift {μ : Measure (S → E)}
    (hΦ : Φ.IsShiftInvariant) (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (i : S) :
    ∫ η, Φ.siteEnergy i η ∂μ = Φ.specificEnergy μ := by
  simp_rw [hΦ.siteEnergy_eq i]
  exact (hμ (-i)).integral_comp' (f := (shift E (-i)).toMeasurableEquiv) Φ.energyDensity

/-- **Georgii, first line of the proof of (15.23):** `μ(f_Φ) = |Λ|⁻¹ μ(∑_{i ∈ Λ} f_Φ ∘ θ_{-i})`,
as `μ(∑_{i ∈ Λ} f_Φ ∘ θ_{-i}) = |Λ| μ(f_Φ)`. -/
lemma integral_sum_siteEnergy_of_measurePreserving_shift {μ : Measure (S → E)}
    [IsFiniteMeasure μ] (hΦ : Φ.IsShiftInvariant)
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Finset S) :
    ∫ η, ∑ i ∈ Λ, Φ.siteEnergy i η ∂μ = #Λ * Φ.specificEnergy μ := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_siteEnergy i μ]
  simp_rw [integral_siteEnergy_of_measurePreserving_shift hΦ hμ]
  rw [sum_const, nsmul_eq_mul]

/-- **Georgii (15.23), finite-volume form:** `|μ(H_Λ) − |Λ| μ(f_Φ)| ≤ ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`
for a shift-invariant probability measure `μ`. -/
theorem abs_integral_hamiltonian_sub_le [DecidableEq S] {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hΦ : Φ.IsShiftInvariant)
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Finset S) :
    |(∫ η, Φ.hamiltonian Λ η ∂μ) - #Λ * Φ.specificEnergy μ| ≤ Φ.tail Λ Λ := by
  rw [← integral_sum_siteEnergy_of_measurePreserving_shift hΦ hμ,
    ← integral_sub (integrable_hamiltonian Λ μ)
      (integrable_finsetSum _ fun i _ ↦ integrable_siteEnergy i μ)]
  calc |∫ η, Φ.hamiltonian Λ η - ∑ i ∈ Λ, Φ.siteEnergy i η ∂μ|
      = ‖∫ η, Φ.hamiltonian Λ η - ∑ i ∈ Λ, Φ.siteEnergy i η ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ Φ.tail Λ Λ * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun η ↦ by
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact abs_sum_siteEnergy_sub_hamiltonian_le Λ η)
    _ = Φ.tail Λ Λ := by simp

/-- **Georgii (15.23), finite-volume form with boundary condition:**
`|μ(H_Λ(σ_Λ ω_{S∖Λ})) − |Λ| μ(f_Φ)| ≤ 3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` for a shift-invariant
probability measure `μ`. -/
theorem abs_integral_hamiltonian_juxt_sub_le [DecidableEq S] {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hΦ : Φ.IsShiftInvariant)
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (Λ : Finset S) (ω : S → E) :
    |(∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂μ) - #Λ * Φ.specificEnergy μ|
      ≤ 3 * Φ.tail Λ Λ := by
  have h1 := abs_integral_hamiltonian_sub_le hΦ hμ Λ
  have h2 : |(∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂μ)
      - ∫ η, Φ.hamiltonian Λ η ∂μ| ≤ 2 * Φ.tail Λ Λ := by
    rw [← integral_sub (integrable_hamiltonian_juxt Λ ω μ) (integrable_hamiltonian Λ μ)]
    calc _ = ‖∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) - Φ.hamiltonian Λ σ ∂μ‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ 2 * Φ.tail Λ Λ * μ.real Set.univ :=
          norm_integral_le_of_norm_le_const (.of_forall fun σ ↦ by
            rw [Real.norm_eq_abs]
            exact abs_hamiltonian_sub_le_of_eqOn Λ fun i hi ↦ juxt_apply_of_mem hi _)
      _ = 2 * Φ.tail Λ Λ := by simp
  calc _ = |((∫ σ, Φ.hamiltonian Λ (juxt (Λ : Set S) ω fun i ↦ σ i) ∂μ)
        - ∫ η, Φ.hamiltonian Λ η ∂μ) + ((∫ η, Φ.hamiltonian Λ η ∂μ) - #Λ * Φ.specificEnergy μ)| :=
        by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * Φ.tail Λ Λ + Φ.tail Λ Λ := add_le_add h2 h1
    _ = 3 * Φ.tail Λ Λ := by ring

end SpecificEnergy

/-! ### Georgii Theorem (15.23) on the lattice `ℤ^d` -/

section SpecificEnergyLimit

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Potential (ι → ℤ) E}
  {κ : Type*} {l : Filter κ} {m n : κ → ι → ℤ}

/-- A ratio whose numerator is within `t j = o(|Λ_j|)` of `|Λ_j| c` tends to `c`. -/
lemma tendsto_div_card_of_abs_sub_le {u t : κ → ℝ} {c : ℝ}
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop)
    (hle : ∀ j, |u j - #(Icc (m j) (n j)) * c| ≤ t j)
    (ht : Tendsto (fun j ↦ t j / #(Icc (m j) (n j))) l (𝓝 0)) :
    Tendsto (fun j ↦ u j / #(Icc (m j) (n j))) l (𝓝 c) := by
  have : Tendsto (fun j ↦ u j / #(Icc (m j) (n j)) - c) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_le_of_tendsto_sub h] with j hj
    have hj' : (0 : ℝ) < #(Icc (m j) (n j)) := by
      exact_mod_cast (nonempty_Icc.2 hj).card_pos
    rw [Real.norm_eq_abs, show u j / #(Icc (m j) (n j)) - c
        = (u j - #(Icc (m j) (n j)) * c) / #(Icc (m j) (n j)) by field_simp,
      abs_div, abs_of_pos hj']
    exact div_le_div_of_nonneg_right (hle j) hj'.le
  simpa using this.add_const c

/-- **Georgii, the estimate (15.25) as stated:** `sup_ω |∑_{i ∈ Λ} f_Φ ∘ θ_{-i} − H_Λ(ω)|` is
`o(|Λ|)` along boxes all of whose sides tend to infinity. -/
theorem tendsto_iSup_abs_sum_siteEnergy_sub_hamiltonian_div_card [IsAbsolutelySummable Φ]
    (hΦ : Φ.IsShiftInvariant) (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ (⨆ ω, |∑ i ∈ Icc (m j) (n j), Φ.siteEnergy i ω
      - Φ.hamiltonian (Icc (m j) (n j)) ω|) / #(Icc (m j) (n j))) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ div_nonneg (Real.iSup_nonneg fun _ ↦ abs_nonneg _) (Nat.cast_nonneg _))
    (fun _ ↦ div_le_div_of_nonneg_right
      (Real.iSup_le (fun ω ↦ abs_sum_siteEnergy_sub_hamiltonian_le _ ω) (tail_nonneg _ _))
      (Nat.cast_nonneg _))
    (tendsto_tail_div_card hΦ h)

variable [IsPotential Φ] [IsAbsolutelySummable Φ] {μ : Measure ((ι → ℤ) → E)}

/-- **Georgii Theorem (15.23), first limit.** For `μ ∈ 𝓟_Θ` and boxes `Λ_j` all of whose sides
tend to infinity, `|Λ_j|⁻¹ μ(H_{Λ_j}) → μ(f_Φ)`. -/
theorem tendsto_integral_hamiltonian_div_card (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ (∫ η, Φ.hamiltonian (Icc (m j) (n j)) η ∂μ) / #(Icc (m j) (n j))) l
      (𝓝 (Φ.specificEnergy μ)) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  exact tendsto_div_card_of_abs_sub_le h (fun j ↦ abs_integral_hamiltonian_sub_le hΦ hpres _)
    (tendsto_tail_div_card hΦ h)

/-- **Georgii Theorem (15.23), second limit.** For `μ ∈ 𝓟_Θ`, boxes `Λ_j` all of whose sides
tend to infinity and arbitrary boundary conditions `ω_j`,
`|Λ_j|⁻¹ μ(H_{Λ_j}(σ_{Λ_j} (ω_j)_{S ∖ Λ_j})) → μ(f_Φ)`. -/
theorem tendsto_integral_hamiltonian_juxt_div_card (hΦ : Φ.IsShiftInvariant)
    (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) (ω : κ → (ι → ℤ) → E) :
    Tendsto (fun j ↦ (∫ σ, Φ.hamiltonian (Icc (m j) (n j))
      (juxt (Icc (m j) (n j) : Set (ι → ℤ)) (ω j) fun i ↦ σ i) ∂μ) / #(Icc (m j) (n j))) l
      (𝓝 (Φ.specificEnergy μ)) := by
  obtain ⟨hprob, hpres⟩ := mem_invariantFields_shiftGroup.1 hμ
  refine tendsto_div_card_of_abs_sub_le h
    (fun j ↦ abs_integral_hamiltonian_juxt_sub_le hΦ hpres _ (ω j)) ?_
  simpa [mul_div_assoc] using (tendsto_tail_div_card hΦ h).const_mul 3

end SpecificEnergyLimit

/-! ### The finite-volume pressure `log Z_Λ` -/

section FiniteVolumePressure

variable (ν : Measure E) [IsProbabilityMeasure ν]

variable (Φ) in
/-- The finite-volume pressure `log Z^Φ_Λ(ω)` with boundary condition `ω`, the quantity of
Georgii (15.31) before the limit. -/
def logZ (Λ : Finset S) (ω : S → E) : ℝ :=
  Real.log (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω).toReal

variable (Φ) in
/-- The finite-volume pressure with the worst boundary condition, `log sup_ω Z^Φ_Λ(ω)`. -/
def logSupZ (Λ : Finset S) : ℝ :=
  Real.log (⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω).toReal

variable (Φ) in
/-- The corrected finite-volume pressure
`a(Λ) = log sup_ω Z^Φ_Λ(ω) + ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`, which is *exactly* subadditive on
disjoint volumes (`Potential.pressureTerm_union_le`) and differs from `log Z_Λ(ω)` by at most
`3 ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖` (`Potential.abs_logZ_sub_pressureTerm_le`). -/
def pressureTerm (Λ : Finset S) : ℝ := Φ.logSupZ ν Λ + Φ.tail Λ Λ

variable [IsAbsolutelySummable Φ]

lemma toReal_premodifierZ_boltzmannFactor_pos (β : ℝ) (Λ : Finset S) (ω : S → E) :
    0 < (Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω).toReal :=
  ENNReal.toReal_pos (premodifierZ_boltzmannFactor_pos ν β Λ ω).ne'
    (premodifierZ_boltzmannFactor_ne_top ν β Λ ω)

lemma toReal_iSup_premodifierZ_boltzmannFactor_pos (β : ℝ) (Λ : Finset S) :
    0 < (⨆ ω, Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω).toReal :=
  ENNReal.toReal_pos (iSup_premodifierZ_boltzmannFactor_ne_zero ν β Λ)
    (iSup_premodifierZ_boltzmannFactor_ne_top ν β Λ)

lemma logZ_le_logSupZ (Λ : Finset S) (ω : S → E) : Φ.logZ ν Λ ω ≤ Φ.logSupZ ν Λ :=
  Real.log_le_log (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω)
    (ENNReal.toReal_mono (iSup_premodifierZ_boltzmannFactor_ne_top ν 1 Λ) (le_iSup _ ω))

/-- **Georgii, in the proof of (15.30):** `‖log Z_Λ‖ ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ` (for a probability
a priori measure, the term `|Λ| |log λ(E)|` vanishes). -/
theorem abs_logZ_le (Λ : Finset S) (ω : S → E) : |Φ.logZ ν Λ ω| ≤ Φ.hamiltonianBound Λ := by
  rw [abs_le, logZ, Real.le_log_iff_exp_le (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω),
    Real.log_le_iff_le_exp (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω)]
  constructor
  · have h := ENNReal.toReal_mono (premodifierZ_boltzmannFactor_ne_top ν (Φ := Φ) 1 Λ ω)
      (le_premodifierZ_boltzmannFactor ν (Φ := Φ) 1 Λ ω)
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le, abs_one, one_mul] at h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (premodifierZ_boltzmannFactor_le ν (Φ := Φ) 1 Λ ω)
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le, abs_one, one_mul] at h

theorem abs_logSupZ_le (Λ : Finset S) : |Φ.logSupZ ν Λ| ≤ Φ.hamiltonianBound Λ := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  rw [abs_le]
  constructor
  · exact ((abs_le.1 (abs_logZ_le ν (Φ := Φ) Λ (Classical.arbitrary _))).1).trans
      (logZ_le_logSupZ ν Λ _)
  · rw [logSupZ, Real.log_le_iff_le_exp (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 Λ)]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (iSup_premodifierZ_boltzmannFactor_le ν (Φ := Φ) 1 Λ)
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le, abs_one, one_mul] at h

variable [Countable S] [IsPotential Φ]

/-- **Georgii, in the proof of (15.28):** the partition function depends on the boundary
condition at most through the tail, `Z_Λ(η) ≤ e^{2 t(Λ)} Z_Λ(ω)` with
`t(Λ) = ∑_{A ∩ Λ ≠ ∅, A ⊄ Λ} ‖Φ_A‖`. -/
lemma premodifierZ_boltzmannFactor_le_exp_mul (Λ : Finset S) (η ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ η
      ≤ ENNReal.ofReal (Real.exp (2 * Φ.tail Λ Λ))
          * Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω := by
  simp only [Specification.premodifierZ, Specification.relZ]
  rw [Specification.lintegral_isssd_eq Λ η (measurable_boltzmannFactor (Φ := Φ) 1 Λ),
    Specification.lintegral_isssd_eq Λ ω (measurable_boltzmannFactor (Φ := Φ) 1 Λ),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ζ ↦ ?_
  rw [boltzmannFactor, boltzmannFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h := (abs_le.1 (abs_hamiltonian_sub_le_of_eqOn (Φ := Φ) Λ (η := juxt (Λ : Set S) η ζ)
    (ζ := juxt (Λ : Set S) ω ζ) fun i hi ↦ by
      rw [juxt_apply_of_mem hi, juxt_apply_of_mem hi])).1
  linarith

/-- `log sup_η Z_Λ(η) ≤ log Z_Λ(ω) + 2 t(Λ)`. -/
lemma logSupZ_le_logZ_add (Λ : Finset S) (ω : S → E) :
    Φ.logSupZ ν Λ ≤ Φ.logZ ν Λ ω + 2 * Φ.tail Λ Λ := by
  have hsup := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (premodifierZ_boltzmannFactor_ne_top ν 1 Λ ω))
    (iSup_le fun η ↦ premodifierZ_boltzmannFactor_le_exp_mul ν (Φ := Φ) Λ η ω)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hsup
  rw [logSupZ, logZ, add_comm, ← Real.log_exp (2 * Φ.tail Λ Λ),
    ← Real.log_mul (Real.exp_pos _).ne' (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω).ne']
  exact Real.log_le_log (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 Λ) hsup

/-- `log Z_Λ(ω)` is within `3 t(Λ)` of the corrected finite-volume pressure `a(Λ)`. -/
theorem abs_logZ_sub_pressureTerm_le (Λ : Finset S) (ω : S → E) :
    |Φ.logZ ν Λ ω - Φ.pressureTerm ν Λ| ≤ 3 * Φ.tail Λ Λ := by
  have h1 := logZ_le_logSupZ ν (Φ := Φ) Λ ω
  have h2 := logSupZ_le_logZ_add ν (Φ := Φ) Λ ω
  have h3 := tail_nonneg (Φ := Φ) Λ Λ
  rw [abs_le, pressureTerm]
  constructor <;> linarith

/-- **Subadditivity of the finite-volume pressure up to the coupling:**
`log sup Z_{Λ ∪ Δ} ≤ c(Λ, Δ) + log sup Z_Λ + log sup Z_Δ`. -/
theorem logSupZ_union_le [DecidableEq S] (Λ Δ : Finset S) :
    Φ.logSupZ ν (Λ ∪ Δ) ≤ (Φ.couplingWeight Λ Δ).toReal + Φ.logSupZ ν Λ + Φ.logSupZ ν Δ := by
  have hsup := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (iSup_premodifierZ_boltzmannFactor_ne_top ν 1 Λ))
      (iSup_premodifierZ_boltzmannFactor_ne_top ν 1 Δ))
    (iSup_le fun ω ↦ (premodifierZ_boltzmannFactor_union_le ν (Φ := Φ) Λ Δ ω).trans
      (mul_le_mul' le_rfl (le_iSup _ ω)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hsup
  rw [logSupZ, logSupZ, logSupZ, ← Real.log_exp (Φ.couplingWeight Λ Δ).toReal,
    ← Real.log_mul (Real.exp_pos _).ne' (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 Λ).ne',
    ← Real.log_mul (mul_pos (Real.exp_pos _)
      (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 Λ)).ne'
      (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 Δ).ne']
  exact Real.log_le_log (toReal_iSup_premodifierZ_boltzmannFactor_pos ν 1 (Λ ∪ Δ)) hsup

/-- **Exact subadditivity of the corrected finite-volume pressure on disjoint volumes:**
`a(Λ ∪ Δ) ≤ a(Λ) + a(Δ)`, because the coupling `c(Λ, Δ)` is absorbed by the tails. -/
theorem pressureTerm_union_le [DecidableEq S] {Λ Δ : Finset S} (h : Disjoint Λ Δ) :
    Φ.pressureTerm ν (Λ ∪ Δ) ≤ Φ.pressureTerm ν Λ + Φ.pressureTerm ν Δ := by
  have h1 := logSupZ_union_le ν (Φ := Φ) Λ Δ
  have h2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨tailWeight_ne_top (Φ := Φ) Λ Λ, tailWeight_ne_top (Φ := Φ) Δ Δ⟩)
    (couplingWeight_add_tailWeight_union_le (Φ := Φ) h)
  rw [ENNReal.toReal_add (couplingWeight_ne_top _ _) (tailWeight_ne_top _ _),
    ENNReal.toReal_add (tailWeight_ne_top _ _) (tailWeight_ne_top _ _)] at h2
  simp only [pressureTerm, tail]
  linarith

end FiniteVolumePressure

/-! ### Georgii Theorem (15.30)(a): the pressure on the lattice `ℤ^d` -/

section Pressure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {Φ : Potential (ι → ℤ) E} (ν : Measure E) [IsProbabilityMeasure ν]

variable (Φ) in
/-- **Georgii (15.31), (15.36): the pressure** (specific Gibbs free energy) of a shift-invariant
absolutely summable potential, defined as `inf_Δ |Δ|⁻¹ a(Δ)` over the boxes `Δ ∈ 𝒮_□`, where
`a(Δ) = log sup_ω Z_Δ(ω) + ∑_{A ∩ Δ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` (`Potential.pressureTerm`), in the manner
of Mathlib's `Subadditive.lim`. By **Theorem (15.30)(a)**,
`Potential.tendsto_logZ_div_card_pressure`, this is the limit `lim |Λ_n|⁻¹ log Z_{Λ_n}(ω_n)`
along boxes all of whose sides tend to infinity, for any boundary conditions `ω_n`. -/
def pressure : ℝ :=
  sInf ((fun Δ ↦ Φ.pressureTerm ν Δ / #Δ) '' {Δ : Finset (ι → ℤ) | Δ.IsBox})

variable [IsPotential Φ] [IsAbsolutelySummable Φ]

/-- The corrected finite-volume pressure satisfies Georgii's (15.11)(i)–(ii). -/
theorem boxSubadditive_pressureTerm (hΦ : Φ.IsShiftInvariant) :
    BoxSubadditive (Φ.pressureTerm ν) where
  image_add_right Λ _ i := by
    rw [image_add_right_eq_translate, pressureTerm, pressureTerm, logSupZ, logSupZ,
      iSup_premodifierZ_boltzmannFactor_translate ν hΦ 1 i Λ, tail_translate hΦ]
  union_le _ _ _ _ hd _ := pressureTerm_union_le ν hd

omit [IsPotential Φ] in
/-- `|Δ|⁻¹ a(Δ) ≥ -‖Φ‖₀` on boxes. -/
lemma neg_le_pressureTerm_div_card (hΦ : Φ.IsShiftInvariant) {Δ : Finset (ι → ℤ)}
    (hΔ : Δ.IsBox) : -(Φ.normAt 0).toReal ≤ Φ.pressureTerm ν Δ / #Δ := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hcard : (0 : ℝ) < #Δ := by exact_mod_cast hΔ.card_pos
  rw [le_div_iff₀ hcard]
  have h1 := (abs_le.1 (abs_logZ_le ν (Φ := Φ) Δ (Classical.arbitrary _))).1
  have h2 := logZ_le_logSupZ ν (Φ := Φ) Δ (Classical.arbitrary _)
  have h3 := tail_nonneg (Φ := Φ) Δ Δ
  rw [hΦ.hamiltonianBound_eq] at h1
  rw [pressureTerm]
  linarith

omit [IsPotential Φ] in
/-- `P(Φ) ≤ |Δ|⁻¹ a(Δ)` for every box `Δ`. -/
lemma pressure_le_pressureTerm_div_card (hΦ : Φ.IsShiftInvariant) {Δ : Finset (ι → ℤ)}
    (hΔ : Δ.IsBox) : Φ.pressure ν ≤ Φ.pressureTerm ν Δ / #Δ :=
  csInf_le ⟨_, by rintro _ ⟨Δ', hΔ', rfl⟩; exact neg_le_pressureTerm_div_card ν hΦ hΔ'⟩
    ⟨Δ, hΔ, rfl⟩

variable {κ : Type*} {l : Filter κ} {m n : κ → ι → ℤ}

/-- **Georgii Theorem (15.30)(a), corrected form (Lemma (15.11) applied to `a`).** -/
theorem tendsto_pressureTerm_div_card (hΦ : Φ.IsShiftInvariant)
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ Φ.pressureTerm ν (Icc (m j) (n j)) / #(Icc (m j) (n j))) l
      (𝓝 (Φ.pressure ν)) :=
  (boxSubadditive_pressureTerm ν hΦ).tendsto_div_card_of_bddBelow
    ⟨_, by rintro _ ⟨Δ, hΔ, rfl⟩; exact neg_le_pressureTerm_div_card ν hΦ hΔ⟩ h

/-- **Georgii Theorem (15.30)(a).** For a shift-invariant `Φ ∈ ℬ`, boxes `Λ_j` all of whose sides
tend to infinity, and arbitrary boundary conditions `ω_j`,
`|Λ_j|⁻¹ log Z_{Λ_j}(ω_j) → P(Φ)`: the limit exists and depends only on `Φ` (and `λ`). -/
theorem tendsto_logZ_div_card_pressure (hΦ : Φ.IsShiftInvariant)
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) (ω : κ → (ι → ℤ) → E) :
    Tendsto (fun j ↦ Φ.logZ ν (Icc (m j) (n j)) (ω j) / #(Icc (m j) (n j))) l
      (𝓝 (Φ.pressure ν)) := by
  have hP := tendsto_pressureTerm_div_card ν hΦ h
  have ht : Tendsto (fun j ↦ 3 * Φ.tail (Icc (m j) (n j)) (Icc (m j) (n j))
      / #(Icc (m j) (n j))) l (𝓝 0) := by
    simpa [mul_div_assoc] using (tendsto_tail_div_card hΦ h).const_mul 3
  have hdiff : Tendsto (fun j ↦ Φ.logZ ν (Icc (m j) (n j)) (ω j) / #(Icc (m j) (n j))
      - Φ.pressureTerm ν (Icc (m j) (n j)) / #(Icc (m j) (n j))) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_le_of_tendsto_sub h] with j hj
    have hj' : (0 : ℝ) < #(Icc (m j) (n j)) := by
      exact_mod_cast (nonempty_Icc.2 hj).card_pos
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hj']
    exact div_le_div_of_nonneg_right (abs_logZ_sub_pressureTerm_le ν _ _) hj'.le
  simpa using hdiff.add hP

/-- **Georgii Theorem (15.30)(a) as stated**, for a sequence of cubes `Λ_n` with `|Λ_n| → ∞`. -/
theorem tendsto_logZ_div_card_pressure_cube (hΦ : Φ.IsShiftInvariant) {s : κ → ℕ}
    (hs : Tendsto (fun j ↦ #(Icc (m j) fun k ↦ m j k + s j)) l atTop) (ω : κ → (ι → ℤ) → E) :
    Tendsto (fun j ↦ Φ.logZ ν (Icc (m j) fun k ↦ m j k + s j) (ω j)
      / #(Icc (m j) fun k ↦ m j k + s j)) l (𝓝 (Φ.pressure ν)) :=
  tendsto_logZ_div_card_pressure ν hΦ (Finset.tendsto_sub_atTop_of_tendsto_card_Icc_cube hs) ω

omit [Fintype ι] [DecidableEq ι] in
/-- The standard cubes `[0, N]^d`, `N → ∞`, along which the pressure is computed. -/
lemma tendsto_sub_atTop_cube (k : ι) :
    Tendsto (fun N : ℕ ↦ (fun _ : ι ↦ (N : ℤ)) k - (fun _ : ι ↦ (0 : ℤ)) k) atTop atTop := by
  simpa using tendsto_natCast_atTop_atTop (R := ℤ)

/-- **Georgii, in the proof of (15.30):** `|P(Φ)| ≤ ‖Φ‖₀`. -/
theorem abs_pressure_le (hΦ : Φ.IsShiftInvariant) : |Φ.pressure ν| ≤ (Φ.normAt 0).toReal := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hlim := tendsto_logZ_div_card_pressure ν hΦ tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  refine le_of_tendsto' hlim.abs fun N ↦ ?_
  have hcard : (0 : ℝ) < #(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) := by
    exact_mod_cast (nonempty_Icc.2 (show (fun _ : ι ↦ (0 : ℤ)) ≤ fun _ ↦ (N : ℤ) from
      fun _ ↦ Int.natCast_nonneg N)).card_pos
  rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard, mul_comm, ← hΦ.hamiltonianBound_eq]
  exact abs_logZ_le ν _ _

end Pressure

/-! ### Lipschitz continuity and convexity of the finite-volume pressure -/

section FiniteVolumeConvexity

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- The Boltzmann factor of a combination of potentials is the product of the Boltzmann
factors: `h^{aΦ + bΨ} = h^Φ_a h^Ψ_b`. -/
lemma boltzmannFactor_smul_add_smul [IsSummable Φ] [IsSummable Ψ] (a b : ℝ) (Λ : Finset S)
    (σ : S → E) :
    (a • Φ + b • Ψ).boltzmannFactor 1 Λ σ = Φ.boltzmannFactor a Λ σ * Ψ.boltzmannFactor b Λ σ := by
  simp only [boltzmannFactor, hamiltonian_add, hamiltonian_smul]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

variable [IsAbsolutelySummable Φ] [IsAbsolutelySummable Ψ]

/-- `Z^Φ_Λ(ω) ≤ e^{∑_{i ∈ Λ} ‖Φ − Ψ‖ᵢ} Z^Ψ_Λ(ω)`. -/
lemma premodifierZ_boltzmannFactor_le_exp_hamiltonianBound_mul (Λ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω
      ≤ ENNReal.ofReal (Real.exp ((Φ - Ψ).hamiltonianBound Λ))
          * Specification.premodifierZ (S := S) (E := E) ν (Ψ.boltzmannFactor 1) Λ ω := by
  simp only [Specification.premodifierZ, Specification.relZ]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun σ ↦ ?_
  rw [boltzmannFactor, boltzmannFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h := (abs_le.1 (abs_hamiltonian_sub_le Φ Ψ Λ σ)).1
  linarith

/-- `log Z^Φ_Λ(ω) − log Z^Ψ_Λ(ω) ≤ ∑_{i ∈ Λ} ‖Φ − Ψ‖ᵢ`. -/
theorem logZ_sub_logZ_le (Λ : Finset S) (ω : S → E) :
    Φ.logZ ν Λ ω - Ψ.logZ ν Λ ω ≤ (Φ - Ψ).hamiltonianBound Λ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (premodifierZ_boltzmannFactor_ne_top ν (Φ := Ψ) 1 Λ ω))
    (premodifierZ_boltzmannFactor_le_exp_hamiltonianBound_mul ν (Φ := Φ) (Ψ := Ψ) Λ ω)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  rw [sub_le_iff_le_add, logZ, logZ, ← Real.log_exp ((Φ - Ψ).hamiltonianBound Λ),
    ← Real.log_mul (Real.exp_pos _).ne' (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω).ne']
  exact Real.log_le_log (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω) h

/-- **Lipschitz continuity of the finite-volume pressure:**
`|log Z^Φ_Λ(ω) − log Z^Ψ_Λ(ω)| ≤ ∑_{i ∈ Λ} ‖Φ − Ψ‖ᵢ`. -/
theorem abs_logZ_sub_logZ_le (Λ : Finset S) (ω : S → E) :
    |Φ.logZ ν Λ ω - Ψ.logZ ν Λ ω| ≤ (Φ - Ψ).hamiltonianBound Λ := by
  have h₁ := logZ_sub_logZ_le ν (Φ := Φ) (Ψ := Ψ) Λ ω
  have h₂ := logZ_sub_logZ_le ν (Φ := Ψ) (Ψ := Φ) Λ ω
  rw [show Ψ - Φ = -(Φ - Ψ) by rw [neg_sub], hamiltonianBound_neg] at h₂
  exact abs_le.2 ⟨by linarith, h₁⟩

variable [Countable S] [IsPotential Φ] [IsPotential Ψ]

/-- **Hölder's inequality for the partition function:**
`Z^{aΦ + bΨ}_Λ(ω) ≤ Z^Φ_Λ(ω)^a Z^Ψ_Λ(ω)^b` for `a, b > 0` with `a + b = 1`. -/
lemma premodifierZ_boltzmannFactor_smul_add_smul_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (Λ : Finset S) (ω : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν ((a • Φ + b • Ψ).boltzmannFactor 1) Λ ω
      ≤ Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω ^ a
          * Specification.premodifierZ (S := S) (E := E) ν (Ψ.boltzmannFactor 1) Λ ω ^ b := by
  have hpq : (1 / a).HolderConjugate (1 / b) :=
    Real.holderConjugate_iff.2 ⟨one_lt_one_div ha (by linarith),
      by simp [hab]⟩
  simp only [Specification.premodifierZ, Specification.relZ]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (Specification.isssd (S := S) (E := E) ν Λ ω) hpq
    (measurable_boltzmannFactor (Φ := Φ) a Λ).aemeasurable
    (measurable_boltzmannFactor (Φ := Ψ) b Λ).aemeasurable
  simp only [Pi.mul_apply, boltzmannFactor_rpow _ (one_div_pos.2 ha).le,
    boltzmannFactor_rpow _ (one_div_pos.2 hb).le, mul_one_div_cancel ha.ne',
    mul_one_div_cancel hb.ne', one_div_one_div] at h
  simpa only [boltzmannFactor_smul_add_smul] using h

/-- **Convexity of the finite-volume pressure:**
`log Z^{aΦ + bΨ}_Λ(ω) ≤ a log Z^Φ_Λ(ω) + b log Z^Ψ_Λ(ω)` for `a, b > 0` with `a + b = 1`. -/
theorem logZ_smul_add_smul_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (Λ : Finset S) (ω : S → E) :
    (a • Φ + b • Ψ).logZ ν Λ ω ≤ a * Φ.logZ ν Λ ω + b * Ψ.logZ ν Λ ω := by
  have : IsAbsolutelySummable (a • Φ + b • Ψ) :=
    (IsAbsolutelySummable.smul a ‹_›).add (IsAbsolutelySummable.smul b ‹_›)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg ha.le (premodifierZ_boltzmannFactor_ne_top ν (Φ := Φ) 1 Λ ω))
      (ENNReal.rpow_ne_top_of_nonneg hb.le (premodifierZ_boltzmannFactor_ne_top ν (Φ := Ψ) 1 Λ ω)))
    (premodifierZ_boltzmannFactor_smul_add_smul_le ν (Φ := Φ) (Ψ := Ψ) ha hb hab Λ ω)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h
  rw [logZ, logZ, logZ, ← Real.log_rpow (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω),
    ← Real.log_rpow (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω),
    ← Real.log_mul (Real.rpow_pos_of_pos (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω) _).ne'
      (Real.rpow_pos_of_pos (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω) _).ne']
  exact Real.log_le_log (toReal_premodifierZ_boltzmannFactor_pos ν 1 Λ ω) h

end FiniteVolumeConvexity

/-! ### Lipschitz continuity and convexity of the pressure (Georgii Proposition (16.1)) -/

section Convexity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ Ψ : Potential (ι → ℤ) E}
  (ν : Measure E) [IsProbabilityMeasure ν]
  [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ]

/-- **Georgii Proposition (16.1)(a), Lipschitz continuity:** `|P(Φ) − P(Ψ)| ≤ ‖Φ − Ψ‖₀`. -/
theorem abs_pressure_sub_le (hΦ : Φ.IsShiftInvariant) (hΨ : Ψ.IsShiftInvariant) :
    |Φ.pressure ν - Ψ.pressure ν| ≤ ((Φ - Ψ).normAt 0).toReal := by
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have hlimΦ := tendsto_logZ_div_card_pressure ν hΦ tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  have hlimΨ := tendsto_logZ_div_card_pressure ν hΨ tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  refine le_of_tendsto' (hlimΦ.sub hlimΨ).abs fun N ↦ ?_
  have hcard : (0 : ℝ) < #(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) := by
    exact_mod_cast (nonempty_Icc.2 (show (fun _ : ι ↦ (0 : ℤ)) ≤ fun _ ↦ (N : ℤ) from
      fun _ ↦ Int.natCast_nonneg N)).card_pos
  rw [← sub_div, abs_div, abs_of_pos hcard, div_le_iff₀ hcard, mul_comm,
    ← (hΦ.sub hΨ).hamiltonianBound_eq]
  exact abs_logZ_sub_logZ_le ν _ _

/-- **Georgii Proposition (16.1)(a), convexity:** `P(aΦ + bΨ) ≤ a P(Φ) + b P(Ψ)` for
`a, b ≥ 0` with `a + b = 1`. -/
theorem pressure_smul_add_smul_le (hΦ : Φ.IsShiftInvariant) (hΨ : Ψ.IsShiftInvariant)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • Φ + b • Ψ).pressure ν ≤ a * Φ.pressure ν + b * Ψ.pressure ν := by
  rcases ha.eq_or_lt with rfl | ha
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb
  · obtain rfl : a = 1 := by linarith
    simp
  have : Nonempty E := Measure.nonempty_of_neZero ν
  have : IsAbsolutelySummable (a • Φ + b • Ψ) :=
    (IsAbsolutelySummable.smul a ‹_›).add (IsAbsolutelySummable.smul b ‹_›)
  have hmix : (a • Φ + b • Ψ).IsShiftInvariant := (hΦ.smul a).add (hΨ.smul b)
  have hlim := tendsto_logZ_div_card_pressure ν hmix tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  have hlimΦ := tendsto_logZ_div_card_pressure ν hΦ tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  have hlimΨ := tendsto_logZ_div_card_pressure ν hΨ tendsto_sub_atTop_cube
    (fun _ ↦ Classical.arbitrary _)
  refine le_of_tendsto_of_tendsto' hlim ((hlimΦ.const_mul a).add (hlimΨ.const_mul b)) fun N ↦ ?_
  have hcard : (0 : ℝ) < #(Icc (fun _ : ι ↦ (0 : ℤ)) fun _ ↦ (N : ℤ)) := by
    exact_mod_cast (nonempty_Icc.2 (show (fun _ : ι ↦ (0 : ℤ)) ≤ fun _ ↦ (N : ℤ) from
      fun _ ↦ Int.natCast_nonneg N)).card_pos
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  exact div_le_div_of_nonneg_right (logZ_smul_add_smul_le ν ha hb hab _ _) hcard.le

omit [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ] in
/-- **Georgii Proposition (16.1)(a).** The pressure is a convex function on the shift-invariant
potentials of `ℬ` (Georgii's `ℬ_Θ`). -/
theorem convexOn_pressure :
    ConvexOn ℝ {Φ : Potential (ι → ℤ) E | Φ.IsShiftInvariant ∧ Φ.IsAbsolutelySummable ∧ IsPotential Φ}
      fun Φ ↦ Φ.pressure ν := by
  refine ⟨?_, ?_⟩
  · intro Φ hΦ Ψ hΨ a b ha hb hab
    have := hΦ.2.2
    have := hΨ.2.2
    exact ⟨(hΦ.1.smul a).add (hΨ.1.smul b), (hΦ.2.1.smul a).add (hΨ.2.1.smul b), inferInstance⟩
  · intro Φ hΦ Ψ hΨ a b ha hb hab
    have := hΦ.2.2
    have := hΨ.2.2
    have := hΦ.2.1
    have := hΨ.2.1
    exact pressure_smul_add_smul_le ν hΦ.1 hΨ.1 ha hb hab

end Convexity

end Potential

end

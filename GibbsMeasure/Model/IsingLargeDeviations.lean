/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Specification.LargeDeviations

/-!
# The Ising model as a worked instance of §15.5 and §16.2

The objects of Georgii §15.5 and Chapter 16 — the Banach space `ℬ_Θ` of shift-invariant
absolutely summable potentials (15.21), the Dobrushin region `𝒟 = {‖Φ‖ < 1}` of (8.36)/§16.2, and
the rate function `J_Ψ(·|Φ)` of (15.49) — are stated for an abstract potential. This file exhibits
the `ℤ^d` Ising potential as a *nonzero* member of all three, so that none of them is vacuous
beyond the zero potential.

## Main results

* `MeasureTheory.GibbsMeasure.isingPotential_mem_BTheta` and
  `MeasureTheory.GibbsMeasure.isingBTheta`: the `ℤ^d` Ising potential
  `Φ_{i} = -h σ_i`, `Φ_{i,j} = -J σ_i σ_j` (Georgii (2.16)/(2.17), coefficients (3.13)) lies in
  Georgii's `ℬ_Θ`; it is absolutely summable because the graph is locally finite and `|σ| ≤ 1`,
  and shift invariant by Georgii (5.8). `MeasureTheory.GibbsMeasure.isingBTheta_ne_zero`: it is
  nonzero as soon as the external field `h` is, at every `d` — including `d = 0`, where `ℤ^d` is a
  single site.
* `MeasureTheory.GibbsMeasure.cardNormAt_isingPotential_of_zero_coupling`, the centrepiece:
  the norm (8.36) of the **pure external field** `Φ_{i} = -h σ_i` on an arbitrary graph is
  `‖Φ‖ᵢ' = ∑_{A ∋ i} |A| ‖Φ_A‖ = |h|`, at every site. With `J = 0` only the singletons carry an
  interaction, `|{i}| = 1`, and `‖Φ_{i}‖ = sup_η |−h σ(η i)| = |h|` because the spin takes the
  values `±1`. This is the only computation of Georgii's norm (8.36) in the library.
* `MeasureTheory.GibbsMeasure.isingBTheta_mem_dobrushinRegion` and
  `MeasureTheory.GibbsMeasure.exists_ne_zero_mem_dobrushinRegion`: consequently, for
  `0 < |h| < 1` the pure-field Ising potential is a **nonzero** element of Georgii's region `𝒟`
  (`Potential.BTheta.dobrushinRegion`), so Corollary (16.17) — the one-sided directional
  derivatives of the pressure agree on `𝒟` — has content. `𝒟` is *strictly smaller* than the
  Ising region where Dobrushin's condition (8.8) holds, since
  `Dobrushin.interactionStrength_le_two_mul_cardNormAt`; the sharp `tanh` form (8.9)(2)/(8.10)
  for the Ising model is `GibbsMeasure/Model/IsingDobrushin.lean`. §16.2 uses (8.36) rather than
  (8.8) because (8.36) is a *norm* on `ℬ_Θ`.
* `MeasureTheory.GibbsMeasure.exists_ldRate_isingBTheta_eq_zero`: the rate function (15.49) of
  the Ising potential is not identically `+∞` — it vanishes at the specific `Ψ`-energy of a
  shift-invariant Ising Gibbs measure, which exists by Georgii (4.23)(a) and (5.16). This is
  `Potential.BTheta.exists_ldRate_eq_zero` at `ν = uniformSpinMeasure`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Potential Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii's norm (8.36) of the pure external field -/

section CardNorm

variable {S : Type*} (G : SimpleGraph S) (J h : ℝ)

/-- With no coupling, only the singleton interactions of the Ising potential survive: `Φ_A = 0`
whenever `|A| ≠ 1`, since the pair term carries the factor `J = 0`. -/
lemma isingPotential_apply_of_zero_coupling_of_card_ne_one {A : Finset S} (hA : A.card ≠ 1)
    (η : S → Bool) : isingPotential G 0 h A η = 0 := by
  simp only [isingPotential]
  by_cases hp : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
  · rw [Potential.nearestNeighbourPair_apply_pair hp]; ring
  · exact Potential.nearestNeighbourPair_apply_eq_zero hA hp η

/-- The sup-norm of the one-point interaction of the Ising potential is `|h|`, at every site and
for every coupling: `Φ_{i}(η) = −h σ(η i)` and the spin `σ` takes the values `±1`. -/
lemma iSup_enorm_isingPotential_singleton (i : S) :
    ⨆ η : S → Bool, ‖isingPotential G J h {i} η‖ₑ = ENNReal.ofReal |h| := by
  have hval : ∀ η : S → Bool, ‖isingPotential G J h {i} η‖ₑ = ENNReal.ofReal |h| := by
    intro η
    simp only [isingPotential]
    rw [Potential.nearestNeighbourPair_apply_card_one (by simp), Real.enorm_eq_ofReal_abs,
      Finset.sum_singleton, abs_mul, abs_neg]
    congr 1
    cases hb : η i <;> simp [spin]
  simp [hval]

/-- **Georgii's norm (8.36) of the pure external field.** The potential `Φ_{i} = −h σ_i` with no
coupling has `‖Φ‖ᵢ' = ∑_{A ∋ i} |A| ‖Φ_A‖ = |h|` at every site `i` of every graph: the only
interaction containing `i` is `{i}`, of cardinality `1` and sup-norm `|h|`. -/
theorem cardNormAt_isingPotential_of_zero_coupling (i : S) :
    Dobrushin.cardNormAt (isingPotential G 0 h) i = ENNReal.ofReal |h| := by
  have hdef : Dobrushin.cardNormAt (isingPotential G 0 h) i
      = ∑' A : Finset S, {A : Finset S | i ∈ A}.indicator
          (fun A ↦ (A.card : ℝ≥0∞) * ⨆ η, ‖isingPotential G 0 h A η‖ₑ) A := rfl
  rw [hdef, tsum_eq_single ({i} : Finset S)]
  · rw [Set.indicator_of_mem (show ({i} : Finset S) ∈ {A : Finset S | i ∈ A} by simp),
      iSup_enorm_isingPotential_singleton, Finset.card_singleton]
    simp
  · intro A hA
    by_cases h0 : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h0)]
      have hcard : A.card ≠ 1 := by
        intro hc
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
        exact hA (by simpa using (Finset.mem_singleton.1 h0).symm)
      simp [isingPotential_apply_of_zero_coupling_of_card_ne_one G h hcard]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from h0) _

end CardNorm

/-! ### The Ising potential as an element of `ℬ_Θ` -/

section BTheta

variable (d : ℕ) (J h : ℝ)

/-- **The `ℤ^d` Ising potential lies in Georgii's `ℬ_Θ`** (15.21): it is absolutely summable
(the lattice is locally finite and `|σ| ≤ 1`) and shift invariant (Georgii (5.8)). -/
theorem isingPotential_mem_BTheta :
    isingPotential (latticeGraph d) J h ∈ Potential.BTheta (Fin d → ℤ) Bool :=
  ⟨⟨inferInstance, Potential.nearestNeighbourPair_empty _ _ _ _, inferInstance⟩,
    isingPotential_isShiftInvariant J h⟩

/-- The `ℤ^d` Ising potential as an element of Georgii's Banach space `ℬ_Θ`. -/
def isingBTheta : Potential.BTheta (Fin d → ℤ) Bool :=
  ⟨isingPotential (latticeGraph d) J h, isingPotential_mem_BTheta d J h⟩

@[simp] lemma coe_isingBTheta :
    (isingBTheta d J h : Potential (Fin d → ℤ) Bool) = isingPotential (latticeGraph d) J h := rfl

variable {d J h}

/-- `ℬ_Θ` over `ℤ^d` is nontrivial: a nonzero external field gives a nonzero potential, since
`Φ_{0}(η) = −h σ(η 0) = ∓h`. No hypothesis on `d` is needed — for `d = 0` the site set `ℤ^0` is a
single point, and `{0}` is still a one-point interaction. -/
theorem isingBTheta_ne_zero (hh : h ≠ 0) : isingBTheta d J h ≠ 0 := by
  intro hzero
  have hval : isingPotential (latticeGraph d) J h {0} (fun _ ↦ true) = 0 :=
    congrArg (fun Φ : Potential.BTheta (Fin d → ℤ) Bool ↦
      (Φ : Potential (Fin d → ℤ) Bool) {0} (fun _ ↦ true)) hzero
  rw [show isingPotential (latticeGraph d) J h
        = Potential.nearestNeighbourPair (latticeGraph d) J h spin from rfl,
    Potential.nearestNeighbourPair_apply_card_one (by simp)] at hval
  simp [spin] at hval
  exact hh hval

end BTheta

/-! ### Georgii's region `𝒟` contains a nonzero potential -/

section DobrushinRegion

variable {d : ℕ} {h : ℝ}

/-- **Georgii's region `𝒟` of (8.36)/§16.2 is not just the zero potential.** The pure external
field `Φ_{i} = −h σ_i` on `ℤ^d` has `‖Φ‖ = |h|` by
`MeasureTheory.GibbsMeasure.cardNormAt_isingPotential_of_zero_coupling`, so it lies in `𝒟` as
soon as `|h| < 1`. -/
theorem isingBTheta_mem_dobrushinRegion (hh : |h| < 1) :
    isingBTheta d 0 h ∈ Potential.BTheta.dobrushinRegion (Fin d) Bool := by
  rw [Potential.BTheta.mem_dobrushinRegion_iff, coe_isingBTheta,
    cardNormAt_isingPotential_of_zero_coupling]
  exact ENNReal.ofReal_lt_one.2 hh

variable (d) in
/-- Georgii's region `𝒟` contains a **nonzero** potential, so
`Potential.BTheta.leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_of_mem_dobrushinRegion`
(Corollary (16.17)) is not vacuous: take the pure external field with `h = 1/2`. -/
theorem exists_ne_zero_mem_dobrushinRegion :
    ∃ Φ : Potential.BTheta (Fin d → ℤ) Bool,
      Φ ∈ Potential.BTheta.dobrushinRegion (Fin d) Bool ∧ Φ ≠ 0 :=
  ⟨isingBTheta d 0 2⁻¹, isingBTheta_mem_dobrushinRegion (by rw [abs_of_pos] <;> norm_num),
    isingBTheta_ne_zero (by norm_num)⟩

end DobrushinRegion

/-! ### The rate function (15.49) of the Ising potential is not identically `+∞` -/

section LDRate

variable {K : Type*} (d : ℕ) (J h : ℝ)

/-- **Georgii Corollary (15.48) for the Ising model.** The rate function
`J_Ψ(·|Φ) = inf {𝓀(·|Φ) : ⟨·, Ψ⟩ = x}` of (15.49) attached to the `ℤ^d` Ising potential and the
uniform a-priori spin measure vanishes somewhere, hence is not identically `+∞`: the shift-
invariant Ising Gibbs measures are nonempty (Georgii (4.23)(a) and (5.16)) and `𝓀(·|Φ)` vanishes
on them (Corollary (15.35)). -/
theorem exists_ldRate_isingBTheta_eq_zero (Ψ : K → Potential.BTheta (Fin d → ℤ) Bool) :
    ∃ x : K → ℝ,
      Potential.BTheta.ldRate uniformSpinMeasure (isingBTheta d J h) Ψ x = 0 :=
  Potential.BTheta.exists_ldRate_eq_zero uniformSpinMeasure (isingBTheta d J h) Ψ

end LDRate

end MeasureTheory.GibbsMeasure

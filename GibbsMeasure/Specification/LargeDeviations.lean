/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.LargeDeviations.Basic
public import GibbsMeasure.Mathlib.Topology.Semicontinuity.EReal
public import GibbsMeasure.Specification.PhaseTransition

/-!
# Large deviations and the equivalence of ensembles (Georgii §15.5)

Throughout, `S = ℤ^d` is spelled `ι → ℤ` for a finite type `ι`, `λ` is an a priori *probability*
measure `ν` on `E`, and potentials live in Georgii's Banach space `ℬ_Θ`
(`Potential.BTheta (ι → ℤ) E`, `Specification/TangentFunctional.lean`). The inputs are §15.2
(`Specification/SpecificEntropy.lean`), §15.3 (`Specification/Pressure.lean`) and §15.4
(`Specification/VariationalPrinciple.lean`); the model-free large deviation vocabulary is
`GibbsMeasure/Mathlib/Probability/LargeDeviations/Basic.lean`.

## Main definitions

* `Potential.BTheta.energyVec Ψ μ = ⟨μ, Ψ⟩ ∈ ℝ^k`, Georgii's continuous map `e_Ψ` of (15.48).
* `Potential.BTheta.dotPotential t Ψ = t · Ψ ∈ ℬ_Θ`.
* `Potential.BTheta.ldRate ν Φ Ψ x`, **Georgii (15.49)**: the rate function
  `J_Ψ(x|Φ) = inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ, ⟨ν, Ψ⟩ = x}`.

## Main results

* `Potential.BTheta.specificRelativeEntropy_sub_dotPotential_add`, Georgii's identity in the proof
  of (15.49): for `μ ∈ 𝓟_Θ` with `⟨μ, Ψ⟩ = x`,
  `𝓀(μ|Φ − t·Ψ) + (P(Φ) + t·x − P(Φ − t·Ψ)) = 𝓀(μ|Φ)`. Everything in this file is a consequence
  of it.
* `Potential.BTheta.coe_le_ldRate`, **Georgii (15.49), the elementary half of the Legendre
  duality**: `t·x − P(Φ − t·Ψ) + P(Φ) ≤ J_Ψ(x|Φ)` for every `t ∈ ℝ^k`. The reverse inequality is
  *not* proved here: Georgii deduces it from the Hahn–Banach theorem together with
  **Theorem (16.13)**, that every tangent functional of the pressure is of the form `⟨μ, ·⟩` for
  some `μ ∈ 𝓟_Θ`, which is not in this library (see "Not proved here" below).
* `Potential.BTheta.ldRate_nonneg`, `Potential.BTheta.ldRate_eq_zero_of_mem_invariantG`, and
  `Potential.BTheta.ldRate_eq_zero_iff` (standard Borel `E`): `J_Ψ(·|Φ) ≥ 0` and
  `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`, the last assertion of **Corollary (15.48)**. The `→` direction
  uses the compactness of the level sets below.
* `Potential.BTheta.isClosed_setOf_specificRelativeEntropy_le`,
  `Potential.BTheta.isCompact_setOf_specificRelativeEntropy_le`: **Georgii's remark after
  Theorem (15.45)**, the level sets `{𝓀(·|Φ) ≤ c}` are compact in the topology of local
  convergence, because `𝓀` is upper semicontinuous with compact level sets (15.14) and `⟨·, Φ⟩`
  is bounded and continuous. Hence `Potential.BTheta.exists_specificRelativeEntropy_eq_iInf`: the
  infimum of `𝓀(·|Φ)` over a closed set of shift-invariant random fields is attained as soon as
  it is finite — the remark Georgii makes about the right-hand side of (15.46) — and
  `Potential.BTheta.iInf_specificRelativeEntropy_ne_zero_of_disjoint`: it is strictly positive as
  soon as the closed set misses `𝒢_Θ(Φ)`, by the variational principle (15.39).
* `Potential.BTheta.mem_invariantG_sub_dotPotential_of_isMinOn`, **Georgii (15.60)**, the
  *equivalence of ensembles*: if `μ ∈ 𝓟_Θ` minimises `𝓀(·|Φ)` among the shift-invariant random
  fields with `⟨·, Ψ⟩ = x`, and if `t` is a subgradient of `J_Ψ(·|Φ)` at `x`, then
  `μ ∈ 𝒢_Θ(Φ − t·Ψ)`. In particular every cluster point of the microcanonical distributions is a
  grand-canonical Gibbs measure for the tilted potential.
  `Potential.BTheta.subset_invariantG_sub_dotPotential` is the same statement in Georgii's set
  form `𝓜_{C,Φ} = e_Ψ⁻¹(B̄_min) ⊆ 𝒢_Θ(Φ − t·Ψ)`.

## Not proved here

**Theorem (15.45)** itself — the large deviation principle (15.46), (15.47) for the periodic
empirical field `°R_Λ` of Definition (15.41) — is *not* proved in this file, and neither is its
contraction **Corollary (15.48)** or **Example (15.50)**. Two inputs Georgii uses are absent from
this library and from Mathlib, and neither is a matter of bookkeeping:

* the **Shannon–McMillan(–Breiman) theorem** `ν(| |Λ|⁻¹ log f_Λ + 𝓀(ν)|) → 0` for an ergodic `ν`
  (Georgii cites Krengel, *Ergodic Theorems*, Thm 9.2.4), which is what makes the set `A_Λ` in
  the proof of (15.47) typical. `grep McMillan`/`ShannonMcMillan` finds nothing in either tree;
* **Phelps, Choquet theory, Prop. 1.2 and Lemma 9.7** — the barycentric representation of a point
  of the closed convex hull of `C` by a measure carried by `C̄` — which is Step 3 of the proof of
  (15.46), the passage from `cx̄ C` to `C̄`. Mathlib has no Choquet theory.

A third input, **Proposition (15.52)** (`𝓀` of the randomly shifted independent-block measure
`γ̄ = |Λ|⁻¹ ∑_{j ∈ Λ} θ_{-j}(∏_i θ_{-pi}(γ))` equals `|Λ|⁻¹ 𝓗_Λ(γ)`), *is* within reach: the
measure is `MeasureTheory.GibbsMeasure.tileAverage` of
`GibbsMeasure/Specification/ErgodicDense.lean` (Georgii's proof of (14.12)), and only the entropy
computation is missing. It is not attempted here.

What §15.5 asserts *besides* (15.45) — the properties of the rate function (15.49), the
compactness of the level sets, the identification of `{J_Ψ = 0}` with `e_Ψ(𝒢_Θ(Φ))`, and the
minimum free energy principle (15.60) that carries the equivalence of ensembles — does not use
either missing input, and is proved here in full.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Topology

noncomputable section

namespace Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {K : Type*} [Fintype K]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-! ### Georgii (15.48): the vector-valued specific energy `e_Ψ` -/

/-- **Georgii, before (15.48).** The continuous map `e_Ψ : ν ↦ ⟨ν, Ψ⟩` from `𝓟_Θ` to `ℝ^k`
attached to a vector-valued potential `Ψ = (Ψ¹, …, Ψᵏ) ∈ ℬ_Θ^k`. -/
def energyVec (Ψ : K → BTheta (ι → ℤ) E) (μ : Measure ((ι → ℤ) → E)) : K → ℝ :=
  fun j ↦ (Ψ j : Potential (ι → ℤ) E).specificEnergy μ

/-- **Georgii, before (15.48).** The inner product `t · Ψ = ∑ⱼ tⱼ Ψʲ ∈ ℬ_Θ`. -/
def dotPotential (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E) : BTheta (ι → ℤ) E := ∑ j, t j • Ψ j

variable {ν}

omit [Fintype ι] [DecidableEq ι] [Fintype K] in
lemma energyVec_apply (Ψ : K → BTheta (ι → ℤ) E) (μ : Measure ((ι → ℤ) → E)) (j : K) :
    energyVec Ψ μ j = (Ψ j : Potential (ι → ℤ) E).specificEnergy μ := rfl

omit [DecidableEq ι] [Fintype K] in
/-- The specific energy of a finite linear combination of potentials. -/
lemma specificEnergy_sum (s : Finset K) (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E)
    (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    ((∑ j ∈ s, t j • Ψ j : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = ∑ j ∈ s, t j * (Ψ j : Potential (ι → ℤ) E).specificEnergy μ := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, Submodule.coe_zero]
      simp [Potential.specificEnergy, Potential.energyDensity, Potential.siteEnergy,
        Potential.siteEnergyTerms]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Submodule.coe_add, specificEnergy_add,
        Submodule.coe_smul, specificEnergy_smul, ih]

omit [DecidableEq ι] in
/-- `⟨μ, t·Ψ⟩ = ∑ⱼ tⱼ ⟨μ, Ψʲ⟩`. -/
lemma specificEnergy_dotPotential (t : K → ℝ) (Ψ : K → BTheta (ι → ℤ) E)
    (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    ((dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = ∑ j, t j * energyVec Ψ μ j :=
  specificEnergy_sum Finset.univ t Ψ μ

/-! ### The identity behind (15.49) -/

variable (ν) in
/-- **Georgii, first display of the proof of (15.49).** For a shift-invariant random field `μ`
with `⟨μ, Ψ⟩ = x`, `𝓀(μ|Φ) = 𝓀(μ|Φ − t·Ψ) + t·x − P(Φ − t·Ψ) + P(Φ)`. Written additively so that
it holds also when `𝓀(μ) = −∞`, i.e. when both specific relative entropies are `+∞`. -/
theorem specificRelativeEntropy_sub_dotPotential_add (Φ : BTheta (ι → ℤ) E)
    (Ψ : K → BTheta (ι → ℤ) E) (t : K → ℝ) {μ : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure μ] :
    ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + (((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * energyVec Ψ μ j
          - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
              Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      = (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ := by
  set Φ' : BTheta (ι → ℤ) E := Φ - dotPotential t Ψ with hΦ'
  have hcoe : ((Φ' : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)
      = (Φ : Potential (ι → ℤ) E) - ((dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E) := by rw [hΦ', Submodule.coe_sub]
  have henergy : ((Φ' : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E).specificEnergy μ
      = (Φ : Potential (ι → ℤ) E).specificEnergy μ - ∑ j, t j * energyVec Ψ μ j := by
    rw [hcoe, specificEnergy_sub, specificEnergy_dotPotential]
  have key : ∀ (a b : ℝ) (h : EReal),
      (a : EReal) - h + (b : EReal) = ((a + b : ℝ) : EReal) - h := by
    intro a b h
    rw [sub_eq_add_neg, sub_eq_add_neg, EReal.coe_add, add_right_comm]
  rw [specificRelativeEntropy, specificRelativeEntropy, key, henergy]
  congr 2
  ring

/-! ### Georgii (15.49): the rate function `J_Ψ(·|Φ)` -/

variable (ν) in
/-- **Georgii (15.49).** The rate function of the vector-valued potential `Ψ` for the potential
`Φ`: `J_Ψ(x|Φ) = inf {𝓀(ν|Φ) : ν ∈ 𝓟_Θ, ⟨ν, Ψ⟩ = x}`, the contraction of the excess free energy
functional `𝓀(·|Φ)` along `e_Ψ`. -/
def ldRate (Φ : BTheta (ι → ℤ) E) (Ψ : K → BTheta (ι → ℤ) E) (x : K → ℝ) : EReal :=
  ⨅ μ ∈ {μ : Measure ((ι → ℤ) → E) | μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      energyVec Ψ μ = x}, (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ

variable {Φ : BTheta (ι → ℤ) E} {Ψ : K → BTheta (ι → ℤ) E} {x : K → ℝ}

omit [Fintype K] in
lemma ldRate_le {μ : Measure ((ι → ℤ) → E)} (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (hx : energyVec Ψ μ = x) :
    ldRate ν Φ Ψ x ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ :=
  iInf₂_le μ ⟨hμ, hx⟩

omit [Fintype K] in
/-- **Georgii Corollary (15.35)** contracted: the rate function is nonnegative. -/
theorem ldRate_nonneg : 0 ≤ ldRate ν Φ Ψ x := by
  refine le_iInf₂ fun μ hμ ↦ ?_
  have : IsProbabilityMeasure μ := hμ.1.1
  exact specificRelativeEntropy_nonneg ν (isShiftInvariant Φ) hμ.1

/-- **Georgii (15.49), the elementary inequality.** For every `t ∈ ℝ^k`,
`t·x − P(Φ − t·Ψ) + P(Φ) ≤ J_Ψ(x|Φ)`: the Legendre–Fenchel transform of `t ↦ P(Φ − t·Ψ)` is a
lower bound for the rate function. -/
theorem coe_le_ldRate (t : K → ℝ) :
    (((∑ j, t j * x j) - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
        Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      ≤ ldRate ν Φ Ψ x := by
  refine le_iInf₂ fun μ hμ ↦ ?_
  have : IsProbabilityMeasure μ := hμ.1.1
  have hid := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := μ)
  rw [hμ.2] at hid
  rw [← hid]
  have hnn : 0 ≤ ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
      Potential (ι → ℤ) E).specificRelativeEntropy ν μ :=
    specificRelativeEntropy_nonneg ν (isShiftInvariant (Φ - dotPotential t Ψ)) hμ.1
  calc (((∑ j, t j * x j) - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
          Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).pressure ν : ℝ) : EReal)
      = 0 + (((Φ : Potential (ι → ℤ) E).pressure ν + ∑ j, t j * x j
          - ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) :
            Potential (ι → ℤ) E).pressure ν : ℝ) : EReal) := by
        rw [zero_add]; congr 1; ring
    _ ≤ _ := by gcongr

omit [Fintype K] in
/-- **Georgii Corollary (15.35)** contracted: if a shift-invariant Gibbs measure has
`⟨μ, Ψ⟩ = x`, then `J_Ψ(x|Φ) = 0`. -/
theorem ldRate_eq_zero_of_mem_invariantG {μ : Measure ((ι → ℤ) → E)}
    (hμ : μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E))
    (hx : energyVec Ψ μ = x) :
    ldRate ν Φ Ψ x = 0 :=
  le_antisymm
    ((ldRate_le hμ.2 hx).trans_eq
      (specificRelativeEntropy_eq_zero_of_mem_invariantG ν (isShiftInvariant Φ) hμ))
    ldRate_nonneg

/-! ### Georgii's remark after (15.45): the level sets of `𝓀(·|Φ)` are compact -/

omit [Fintype K] in
/-- `𝓀(μ|Φ) ≤ c` is `P(Φ) + ⟨μ, Φ⟩ − c ≤ 𝓀(μ)`, written without `EReal` subtraction. -/
lemma specificRelativeEntropy_le_coe_iff {μ : Measure ((ι → ℤ) → E)} {c : ℝ} :
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ ≤ (c : EReal) ↔
      (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ - c
        : ℝ) : EReal) ≤ specificEntropy ν μ := by
  rw [specificRelativeEntropy]
  set a : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ
  have hne : specificEntropy ν μ ≠ ⊤ := specificEntropy_ne_top ν
  induction h : specificEntropy ν μ using EReal.rec with
  | bot =>
      simp only [EReal.sub_bot (EReal.coe_ne_bot _), le_bot_iff, top_le_iff]
      exact iff_of_false (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
  | coe r =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro <;> linarith
  | top => exact absurd h hne

omit [Fintype K] in
/-- The excess free energy is never `−∞`: it is at least `P(Φ) + ⟨μ, Φ⟩`, because `𝓀(μ) ≤ 0`. -/
lemma coe_le_specificRelativeEntropy (μ : Measure ((ι → ℤ) → E)) :
    (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy μ : ℝ)
        : EReal) ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ := by
  rw [specificRelativeEntropy, sub_eq_add_neg]
  nth_rewrite 1 [← add_zero (((Φ : Potential (ι → ℤ) E).pressure ν
    + (Φ : Potential (ι → ℤ) E).specificEnergy μ : ℝ) : EReal)]
  gcongr
  simpa using EReal.neg_le_neg_iff.2 (specificEntropy_nonpos ν (μ := μ))

omit [Fintype ι] [Fintype K] [DecidableEq ι] in
/-- **Georgii Remark (15.26)(2)** at `Ψ = 0`: `|⟨μ, Φ⟩| ≤ ‖Φ‖₀`. (Missing from
`Specification/Pressure.lean`, whose `Potential.abs_specificEnergy_sub_le` is the two-potential
form.) -/
lemma abs_specificEnergy_le (μ : Measure ((ι → ℤ) → E)) [IsProbabilityMeasure μ] :
    |(Φ : Potential (ι → ℤ) E).specificEnergy μ|
      ≤ (((Φ : Potential (ι → ℤ) E)).normAt 0).toReal := by
  rw [Potential.specificEnergy]
  calc |∫ η, (Φ : Potential (ι → ℤ) E).energyDensity η ∂μ|
      = ‖∫ η, (Φ : Potential (ι → ℤ) E).energyDensity η ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ (((Φ : Potential (ι → ℤ) E)).normAt 0).toReal * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun η ↦ by
          rw [Real.norm_eq_abs]; exact Potential.abs_siteEnergy_le 0 η)
    _ = (((Φ : Potential (ι → ℤ) E)).normAt 0).toReal := by simp

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** The sublevel sets `{𝓀(·|Φ) ≤ c}` of the excess
free energy functional are closed in the topology of local convergence: `𝓀` is upper
semicontinuous (15.14) and `⟨·, Φ⟩` is continuous. -/
theorem isClosed_setOf_specificRelativeEntropy_le (c : ℝ) :
    IsClosed {μ : WithLocalConvergence (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)} := by
  have hset : {μ : WithLocalConvergence (ι → ℤ) E |
        (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
          (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)}
      = {μ : WithLocalConvergence (ι → ℤ) E |
        (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy
            (μ.toMeasure : Measure ((ι → ℤ) → E)) - c : ℝ) : EReal)
          ≤ specificEntropy ν (μ.toMeasure : Measure ((ι → ℤ) → E))} := by
    ext μ; exact specificRelativeEntropy_le_coe_iff
  rw [hset]
  exact UpperSemicontinuous.isClosed_setOf_coe_le
    (((continuous_specificEnergy (Φ := (Φ : Potential (ι → ℤ) E))).const_add _).sub
      continuous_const)
    (upperSemicontinuous_specificEntropy ν)

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** Over a standard Borel state space the sublevel
sets `{𝓀(·|Φ) ≤ c}` are compact: they are closed, and contained in the compact level set
`{𝓀 ≥ P(Φ) − ‖Φ‖₀ − c}` of the specific entropy (Proposition (15.14)). -/
theorem isCompact_setOf_specificRelativeEntropy_le [StandardBorelSpace E] (c : ℝ) :
    IsCompact {μ : WithLocalConvergence (ι → ℤ) E |
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) ≤ (c : EReal)} := by
  refine IsCompact.of_isClosed_subset
    (isCompact_setOf_le_specificEntropy ν ((Φ : Potential (ι → ℤ) E).pressure ν
      - (((Φ : Potential (ι → ℤ) E)).normAt 0).toReal - c))
    (isClosed_setOf_specificRelativeEntropy_le ν Φ c) fun μ hμ ↦ ?_
  have h1 : (((Φ : Potential (ι → ℤ) E).pressure ν + (Φ : Potential (ι → ℤ) E).specificEnergy
      (μ.toMeasure : Measure ((ι → ℤ) → E)) - c : ℝ) : EReal)
      ≤ specificEntropy ν (μ.toMeasure : Measure ((ι → ℤ) → E)) :=
    specificRelativeEntropy_le_coe_iff.1 hμ
  have h2 := abs_le.1 (abs_specificEnergy_le (Φ := Φ) (μ.toMeasure : Measure ((ι → ℤ) → E)))
  exact le_trans (EReal.coe_le_coe_iff.2 (by linarith [h2.1])) h1

variable (ν Φ) in
omit [Fintype K] in
/-- **Georgii, remark after Theorem (15.45).** The excess free energy functional `𝓀(·|Φ)` is
lower semicontinuous for the topology of local convergence. -/
theorem lowerSemicontinuous_specificRelativeEntropy :
    LowerSemicontinuous fun μ : WithLocalConvergence (ι → ℤ) E ↦
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot =>
      convert isClosed_empty
      ext μ
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, le_bot_iff]
      intro hcon
      exact absurd (hcon ▸ coe_le_specificRelativeEntropy
        (Φ := Φ) (μ.toMeasure : Measure ((ι → ℤ) → E))) (by simp)
  | coe c => exact isClosed_setOf_specificRelativeEntropy_le ν Φ c
  | top => simp

/-! ### Georgii, remark after (15.45): the infimum of `𝓀(·|Φ)` is attained -/

variable (Ψ x) in
/-- The index set of the rate function `J_Ψ(x|Φ)`, as a subset of the space of random fields with
the topology of local convergence. -/
def constraintSet : Set (WithLocalConvergence (ι → ℤ) E) :=
  {μ | (μ.toMeasure : Measure ((ι → ℤ) → E)) ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
    energyVec Ψ (μ.toMeasure : Measure ((ι → ℤ) → E)) = x}

omit [Fintype ι] [DecidableEq ι] [Fintype K] in
variable (Ψ x) in
/-- `e_Ψ` is continuous and `𝓟_Θ` is closed, so the constraint set of (15.49) is closed. -/
theorem isClosed_constraintSet : IsClosed (constraintSet Ψ x) := by
  have hset : constraintSet (ι := ι) (E := E) Ψ x
      = {μ : WithLocalConvergence (ι → ℤ) E | ∀ τ ∈ shiftGroup (ι → ℤ) E,
          MeasurePreserving τ.toFun (μ.toMeasure : Measure ((ι → ℤ) → E)) μ.toMeasure}
        ∩ ⋂ j : K, {μ : WithLocalConvergence (ι → ℤ) E |
          (Ψ j : Potential (ι → ℤ) E).specificEnergy
            (μ.toMeasure : Measure ((ι → ℤ) → E)) = x j} := by
    ext μ
    simp only [constraintSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      mem_invariantFields_iff, funext_iff, energyVec]
    exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨inferInstance, h.1⟩, h.2⟩⟩
  rw [hset]
  refine (isClosed_setOf_forall_measurePreserving _).inter (isClosed_iInter fun j ↦ ?_)
  exact isClosed_eq (continuous_specificEnergy (Φ := (Ψ j : Potential (ι → ℤ) E)))
    continuous_const

omit [Fintype K] in
variable (Φ Ψ x) in
/-- The rate function (15.49) as an infimum over the constraint set inside the space of random
fields with the topology of local convergence. -/
theorem ldRate_eq_iInf_constraintSet :
    ldRate ν Φ Ψ x = ⨅ μ ∈ constraintSet (ι := ι) (E := E) Ψ x,
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
        (μ.toMeasure : Measure ((ι → ℤ) → E)) := by
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ldRate_le hμ.1 hμ.2) (le_iInf₂ fun μ hμ ↦ ?_)
  have hprob : IsProbabilityMeasure μ := hμ.1.1
  set μ' : WithLocalConvergence (ι → ℤ) E := WithSetwiseTopology.ofMeasure ⟨μ, hprob⟩ with hμ'def
  have hcoe : (μ'.toMeasure : Measure ((ι → ℤ) → E)) = μ := rfl
  have hmemC : μ' ∈ constraintSet (ι := ι) (E := E) Ψ x := by
    refine ⟨?_, ?_⟩ <;> rw [hcoe]
    exacts [hμ.1, hμ.2]
  exact (iInf₂_le μ' hmemC).trans_eq (by rw [hcoe])

variable [StandardBorelSpace E]

variable (Φ Ψ x) in
/-- **Georgii, remark after Theorem (15.45).** The infimum defining the rate function
`J_Ψ(x|Φ)` is attained as soon as it is finite, because the sublevel sets of `𝓀(·|Φ)` are compact
and `𝓀(·|Φ)` is lower semicontinuous. -/
theorem exists_specificRelativeEntropy_eq_ldRate (hfin : ldRate ν Φ Ψ x ≠ ⊤) :
    ∃ μ : Measure ((ι → ℤ) → E), μ ∈ invariantFields (shiftGroup (ι → ℤ) E) ∧
      energyVec Ψ μ = x ∧
      (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = ldRate ν Φ Ψ x := by
  set F : WithLocalConvergence (ι → ℤ) E → EReal := fun μ ↦
    (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν
      (μ.toMeasure : Measure ((ι → ℤ) → E)) with hF
  set C : Set (WithLocalConvergence (ι → ℤ) E) := constraintSet (ι := ι) (E := E) Ψ x with hC
  have hJ : ldRate ν Φ Ψ x = ⨅ μ ∈ C, F μ := ldRate_eq_iInf_constraintSet Φ Ψ x
  -- a real level strictly above the infimum
  obtain ⟨q, hq1, -⟩ := EReal.lt_iff_exists_rat_btwn.1 (lt_top_iff_ne_top.2 hfin)
  set c : ℝ := (q : ℝ) with hc
  rw [hJ] at hq1
  obtain ⟨μ₀, hμ₀⟩ := iInf_lt_iff.1 hq1
  obtain ⟨hμ₀C, hμ₀c⟩ := iInf_lt_iff.1 hμ₀
  -- the compact piece of the constraint set below that level
  set K : Set (WithLocalConvergence (ι → ℤ) E) := {μ | F μ ≤ (c : EReal)} ∩ C with hK
  have hKcompact : IsCompact K :=
    (isCompact_setOf_specificRelativeEntropy_le ν Φ c).inter_right (isClosed_constraintSet Ψ x)
  have hKne : K.Nonempty := ⟨μ₀, hμ₀c.le, hμ₀C⟩
  obtain ⟨μ₁, hμ₁K, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hKne hKcompact
    ((lowerSemicontinuous_specificRelativeEntropy ν Φ).lowerSemicontinuousOn K)
  refine ⟨(μ₁.toMeasure : Measure ((ι → ℤ) → E)), hμ₁K.2.1, hμ₁K.2.2, ?_⟩
  rw [hJ]
  refine le_antisymm (le_iInf₂ fun μ hμ ↦ ?_) (iInf₂_le μ₁ hμ₁K.2)
  by_cases hle : F μ ≤ (c : EReal)
  · exact hmin ⟨hle, hμ⟩
  · exact le_trans hμ₁K.1 (le_of_lt (not_le.1 hle))

variable (Φ Ψ x) in
/-- **Georgii Corollary (15.48), last assertion**: `{J_Ψ(·|Φ) = 0} = e_Ψ(𝒢_Θ(Φ))`. The rate
function vanishes at `x` exactly when some shift-invariant Gibbs measure has specific
`Ψ`-energy `x`; this is the variational principle (15.39) together with the attainment of the
infimum. -/
theorem ldRate_eq_zero_iff :
    ldRate ν Φ Ψ x = 0 ↔ ∃ μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := (Φ : Potential (ι → ℤ) E)) ν 1) (shiftGroup (ι → ℤ) E), energyVec Ψ μ = x := by
  refine ⟨fun h ↦ ?_, fun ⟨μ, hμ, hx⟩ ↦ ldRate_eq_zero_of_mem_invariantG hμ hx⟩
  obtain ⟨μ, hμinv, hμx, hμ0⟩ := exists_specificRelativeEntropy_eq_ldRate Φ Ψ x
    (by rw [h]; exact EReal.zero_ne_top)
  have : IsProbabilityMeasure μ := hμinv.1
  rw [h] at hμ0
  exact ⟨μ, mem_invariantG_of_specificRelativeEntropy_eq_zero' ν (isShiftInvariant Φ) hμinv hμ0,
    hμx⟩

/-! ### Georgii (15.60): the minimum free energy principle and the equivalence of ensembles -/

/-- **Georgii (15.60).** Let `μ ∈ 𝓟_Θ` minimise the excess free energy `𝓀(·|Φ)` among the
shift-invariant random fields with the same specific `Ψ`-energy `x = ⟨μ, Ψ⟩`, i.e.
`𝓀(μ|Φ) = J_Ψ(x|Φ)`, and let `t ∈ ℝ^k` be a subgradient of the convex rate function
`J_Ψ(·|Φ)` at `x`. Then `μ ∈ 𝒢_Θ(Φ − t·Ψ)`.

This is the *equivalence of ensembles*: the constrained (microcanonical) minimisers of the free
energy are the unconstrained (grand canonical) Gibbs measures of the potential tilted by the
Lagrange multiplier `t`. Combined with Georgii's Theorem (15.45) — not available here — every
cluster point of `°γ^{Φ|Ψ,B}_Λ` is such a minimiser, which is his Corollary (15.58).

The proof is Georgii's, with the differentiability of `J_Ψ(·|Φ)` at `x` replaced by the
subgradient inequality it produces: for a Gibbs measure `ρ ∈ 𝒢_Θ(Φ − t·Ψ)`, which exists over a
standard Borel state space, the subgradient inequality at `y = ⟨ρ, Ψ⟩` and the identity
`𝓀(·|Φ) = 𝓀(·|Φ − t·Ψ) + t·⟨·, Ψ⟩ − P(Φ − t·Ψ) + P(Φ)` give
`𝓀(μ|Φ − t·Ψ) ≤ 𝓀(ρ|Φ − t·Ψ) = 0`; the variational principle (15.39) then puts `μ` in
`𝒢_Θ(Φ − t·Ψ)`. -/
theorem mem_invariantG_sub_dotPotential_of_isMinOn {μ : Measure ((ι → ℤ) → E)}
    [IsProbabilityMeasure μ] (hμ : μ ∈ invariantFields (shiftGroup (ι → ℤ) E)) (t : K → ℝ)
    (hmin : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      = ldRate ν Φ Ψ (energyVec Ψ μ))
    (ht : ∀ y : K → ℝ, ldRate ν Φ Ψ (energyVec Ψ μ)
      + ((∑ j, t j * (y j - energyVec Ψ μ j) : ℝ) : EReal) ≤ ldRate ν Φ Ψ y) :
    μ ∈ invariantG (gibbsSpecificationOfAbsolutelySummable
      (Φ := ((Φ - dotPotential t Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)) ν 1)
      (shiftGroup (ι → ℤ) E) := by
  set Φ' : BTheta (ι → ℤ) E := Φ - dotPotential t Ψ with hΦ'
  set x : K → ℝ := energyVec Ψ μ with hx
  -- a shift-invariant Gibbs measure for the tilted potential exists
  obtain ⟨ρ, hρ⟩ := invariantG_gibbsSpecification_shiftGroup_nonempty
    (Φ := (Φ' : Potential (ι → ℤ) E)) ν 1 (isShiftInvariant Φ')
  have hρprob : IsProbabilityMeasure ρ := hρ.1.1
  set y : K → ℝ := energyVec Ψ ρ with hy
  -- Georgii's identity for `μ` and for `ρ`
  have hidμ := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := μ)
  have hidρ := specificRelativeEntropy_sub_dotPotential_add ν Φ Ψ t (μ := ρ)
  have hρ0 : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν ρ = 0 :=
    specificRelativeEntropy_eq_zero_of_mem_invariantG ν (isShiftInvariant Φ') hρ
  -- the subgradient inequality at `y`, together with the minimality of `μ`
  have hsub : (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + ((∑ j, t j * (y j - x j) : ℝ) : EReal)
      ≤ (Φ : Potential (ι → ℤ) E).specificRelativeEntropy ν ρ := by
    rw [hmin]
    exact (ht y).trans (ldRate_le hρ.2 rfl)
  rw [← hidμ, ← hidρ, hρ0, zero_add] at hsub
  -- cancel the real constants
  have hsum : (∑ j, t j * (y j - x j) : ℝ) = (∑ j, t j * y j) - ∑ j, t j * x j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  set P : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν with hP
  set P' : ℝ := (Φ' : Potential (ι → ℤ) E).pressure ν with hP'
  have hcollapse : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ
      + ((P + ∑ j, t j * y j - P' : ℝ) : EReal)
      ≤ (0 : EReal) + ((P + ∑ j, t j * y j - P' : ℝ) : EReal) := by
    rw [zero_add]
    refine le_trans (le_of_eq ?_) hsub
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    rw [hsum]
    ring
  have h0 : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ ≤ 0 :=
    (EReal.addLECancellable_coe _).add_le_add_iff_right.1 hcollapse
  have h0' : (Φ' : Potential (ι → ℤ) E).specificRelativeEntropy ν μ = 0 :=
    le_antisymm h0 (specificRelativeEntropy_nonneg ν (isShiftInvariant Φ') hμ)
  exact mem_invariantG_of_specificRelativeEntropy_eq_zero' ν (isShiftInvariant Φ') hμ h0'

end Potential.BTheta

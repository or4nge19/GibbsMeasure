/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Model.IsingDobrushin
public import GibbsMeasure.Specification.LargeDeviations

/-!
# The Ising model as a worked instance of §15.5 and §16.2

The objects of Georgii §15.5 and Chapter 16 — the Banach space `ℬ_Θ` of shift-invariant
absolutely summable potentials (15.21), the Dobrushin region `𝒟 = {‖Φ‖ < 1}` of (8.36)/§16.2, and
the rate function `J_Ψ(·|Φ)` of (15.49) — are stated for an abstract potential. This file exhibits
the `ℤ^d` Ising potential as a member of all three **at a nonzero coupling**, and instantiates
Corollary (16.17) and Corollary (8.37) there: the derivative of the pressure in the external
field is the magnetisation, and its second derivative is the summed spin-spin covariance — the
susceptibility.

## Main results

* `MeasureTheory.GibbsMeasure.isingPotential_mem_BTheta` and
  `MeasureTheory.GibbsMeasure.isingBTheta`: the `ℤ^d` Ising potential
  `Φ_{i} = -h σ_i`, `Φ_{i,j} = -J σ_i σ_j` (Georgii (2.16)/(2.17), coefficients (3.13)) lies in
  Georgii's `ℬ_Θ`; it is absolutely summable because the graph is locally finite and `|σ| ≤ 1`,
  and shift invariant by Georgii (5.8). `MeasureTheory.GibbsMeasure.isingBTheta_ne_zero`: it is
  nonzero as soon as the external field `h` is, at every `d` — including `d = 0`, where `ℤ^d` is a
  single site.
* `MeasureTheory.GibbsMeasure.cardNormAt_isingPotential`, the centrepiece: **Georgii's norm
  (8.36) of the Ising potential** on an arbitrary locally finite graph,
  `‖Φ‖ᵢ' = ∑_{A ∋ i} |A| ‖Φ_A‖ = |h| + 2 deg(i) |J|`, at every site. Only the singleton `{i}` and
  the `deg(i)` bonds at `i` carry an interaction; `|{i}| = 1` with `‖Φ_{i}‖ = |h|` and
  `|{i,j}| = 2` with `‖Φ_{i,j}‖ = |J|`, because the spin takes the values `±1`. On `ℤ^d` this is
  `‖Φ‖ = |h| + 4d|J|` (`cardNormAt_isingPotential_latticeGraph`, using
  `card_neighborFinset_latticeGraph : deg = 2d`).
  `MeasureTheory.GibbsMeasure.cardNormAt_isingPotential_of_zero_coupling` is the pure-field case
  `‖Φ‖ᵢ' = |h|` on an *arbitrary* graph, with no local finiteness.
* `MeasureTheory.GibbsMeasure.isingBTheta_mem_dobrushinRegion` and
  `MeasureTheory.GibbsMeasure.exists_ne_zero_mem_dobrushinRegion`: consequently the Ising
  potential is an element of Georgii's region `𝒟` (`Potential.BTheta.dobrushinRegion`) as soon as
  `|h| + 4d|J| < 1`, and a **nonzero** one as soon as `h ≠ 0`.
* `MeasureTheory.GibbsMeasure.leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta` and
  `..._field`: **Corollary (16.17), first derivative**, at the Ising potential. The pressure is
  Gateaux differentiable at `Φ^{J,h}` for `|h| + 4d|J| < 1`, with
  `∂/∂t P(Φ^{J,h} + tΨ)|_{t=0} = −⟨μ, Ψ⟩` for the unique shift-invariant Ising Gibbs measure `μ`;
  in the direction of the external field this is `∂P/∂h = μ(σ_0)`, the magnetisation.
* `MeasureTheory.GibbsMeasure.hasDerivAt_pressure_isingBTheta_field`: the field derivative as a
  genuine two-sided derivative, `HasDerivAt (fun t ↦ P(Φ^{J,h+t})) (μ(σ_0)) 0`.
* `MeasureTheory.GibbsMeasure.hasDerivAt_rightDirDeriv_pressure_isingBTheta` and `..._field`:
  **Corollary (16.17), second derivative**: `∂²P/∂h² = ∑_k cov_μ(σ_0, σ_k)`, the susceptibility.
* `MeasureTheory.GibbsMeasure.exists_hasDerivAt_integral_isingGibbsMeasure_field`:
  **Corollary (8.37)** at the Ising potential — the fluctuation–response identity
  `∂/∂h μ_h(g) = ∑_k cov_{μ_h}(g, σ_k)` for a bounded quasilocal observable `g` with
  `∑_i δ_i(g) < ∞`, on a field interval kept inside `𝒟`.
* `MeasureTheory.GibbsMeasure.exists_ldRate_isingBTheta_eq_zero`: the rate function (15.49) of
  the Ising potential is not identically `+∞` — it vanishes at the specific `Ψ`-energy of a
  shift-invariant Ising Gibbs measure, which exists by Georgii (4.23)(a) and (5.16). This is
  `Potential.BTheta.exists_ldRate_eq_zero` at `ν = uniformSpinMeasure`.

## `𝒟` against Dobrushin's condition (8.8)

The two criteria are not the same, and neither is a restatement of the other. For the `ℤ^d` Ising
model at `β = 1`:

* Georgii's region `𝒟` of (8.36) asks `|h| + 4d|J| < 1`;
* Proposition (8.8) as computed in `GibbsMeasure/Model/IsingDobrushin.lean`
  (`Dobrushin.isDobrushin_isingSpecification`) asks `4d|J| < 2`, i.e. `2d|J| < 1`;
* its `tanh` sharpening (8.9)(2)/(8.10) (`Dobrushin.isDobrushin_isingSpecification_tanh`) asks
  `2d tanh|J| < 1`.

So `𝒟` is *strictly* the smallest of the three: it loses a factor `2` in the coupling
(`Dobrushin.interactionStrength_le_two_mul_cardNormAt` is the general reason) and, unlike (8.8),
it charges the external field, which the interaction strength `∑_{A ∋ i} (|A| − 1) δ(Φ_A)` of
(8.8) ignores because the singleton terms have `|A| − 1 = 0`. That `|h| + 4d|J| < 1` implies
(8.8) is `MeasureTheory.GibbsMeasure.isDobrushin_isingSpecification_of_cardNormAt_lt_one`.
§16.2 nevertheless uses (8.36) rather than (8.8), because (8.36) is a *norm* on `ℬ̃_Θ`: it is what
keeps a whole segment `Φ + tΨ`, `|t| ≤ t₀`, inside the uniqueness region, which is what the
differentiation of (8.37)/(16.17) needs.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Potential Set
open scoped ENNReal ProbabilityTheory

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

/-- The sup-norm of a bond interaction of the Ising potential is `|J|`, at every edge and for
every field: `Φ_{i,j}(η) = −J σ(η i) σ(η j)` and the spin `σ` takes the values `±1`, so the
product is `±1`. -/
lemma iSup_enorm_isingPotential_pair [DecidableEq S] {i j : S} (hij : G.Adj i j) :
    ⨆ η : S → Bool, ‖isingPotential G J h {i, j} η‖ₑ = ENNReal.ofReal |J| := by
  have hedge : ({i, j} : Finset S).card = 2 ∧
      ∃ a ∈ ({i, j} : Finset S), ∃ b ∈ ({i, j} : Finset S), G.Adj a b :=
    ⟨Finset.card_pair hij.ne, i, by simp, j, by simp, hij⟩
  have hval : ∀ η : S → Bool, ‖isingPotential G J h {i, j} η‖ₑ = ENNReal.ofReal |J| := by
    intro η
    have habs : |isingPotential G J h {i, j} η| = |J| := by
      rw [isingPotential, Potential.nearestNeighbourPair_apply_pair hedge,
        Finset.prod_pair hij.ne, abs_mul, abs_neg]
      cases hb : η i <;> cases hc : η j <;> simp [spin]
    rw [Real.enorm_eq_ofReal_abs, habs]
  simp [hval]

/-- **Georgii's norm (8.36) of the Ising potential.** On any locally finite graph,
`‖Φ‖ᵢ' = ∑_{A ∋ i} |A| ‖Φ_A‖ = |h| + 2 deg(i) |J|` at every site `i`: the interactions containing
`i` are the singleton `{i}`, of cardinality `1` and sup-norm `|h|`, and the `deg(i)` bonds
`{i, j}`, of cardinality `2` and sup-norm `|J|`. Both sup-norms are exact because the spin takes
the values `±1`. -/
theorem cardNormAt_isingPotential [G.LocallyFinite] (i : S) :
    Dobrushin.cardNormAt (isingPotential G J h) i
      = ENNReal.ofReal (|h| + 2 * ((G.neighborFinset i).card : ℝ) * |J|) := by
  classical
  have hdef : Dobrushin.cardNormAt (isingPotential G J h) i
      = ∑' A : Finset S, {A : Finset S | i ∈ A}.indicator
          (fun A ↦ (A.card : ℝ≥0∞) * ⨆ η, ‖isingPotential G J h A η‖ₑ) A := rfl
  -- only `{i}` and the bonds at `i` contribute
  have hzero : ∀ A ∉ insert ({i} : Finset S)
      ((G.neighborFinset i).image fun j ↦ ({i, j} : Finset S)),
      {A : Finset S | i ∈ A}.indicator
        (fun A ↦ (A.card : ℝ≥0∞) * ⨆ η, ‖isingPotential G J h A η‖ₑ) A = 0 := by
    intro A hA
    by_cases hiA : i ∈ A
    swap
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA) _
    rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
    by_cases hc1 : A.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc1
      rw [Finset.mem_singleton] at hiA
      subst hiA
      exact absurd (Finset.mem_insert_self _ _) hA
    by_cases hc2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
    · obtain ⟨j, hij, rfl⟩ := Dobrushin.isingPotential_support G hiA hc2
      exact absurd (Finset.mem_insert_of_mem (Finset.mem_image.2
        ⟨j, (SimpleGraph.mem_neighborFinset G i j).2 hij, rfl⟩)) hA
    · have hΦ0 : isingPotential G J h A = 0 :=
        funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero hc1 hc2 η
      simp [hΦ0]
  have hnotmem : ({i} : Finset S) ∉ (G.neighborFinset i).image fun j ↦ ({i, j} : Finset S) := by
    intro hmem
    obtain ⟨j, hj, hij⟩ := Finset.mem_image.1 hmem
    have hne : i ≠ j := ((SimpleGraph.mem_neighborFinset G i j).1 hj).ne
    have hcard := congrArg Finset.card hij
    rw [Finset.card_pair hne, Finset.card_singleton] at hcard
    omega
  have hinjOn : Set.InjOn (fun j ↦ ({i, j} : Finset S)) (G.neighborFinset i) := by
    intro a ha b _ hab
    have hia : i ≠ a := ((SimpleGraph.mem_neighborFinset G i a).1 (Finset.mem_coe.1 ha)).ne
    have hab' : ({i, a} : Finset S) = {i, b} := hab
    have hmem : a ∈ ({i, b} : Finset S) := hab' ▸ (by simp : a ∈ ({i, a} : Finset S))
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | hab'
    · exact absurd rfl hia
    · exact hab'
  -- the singleton term is `1 · |h|`, each bond term is `2 · |J|`
  have hsingle : {A : Finset S | i ∈ A}.indicator
      (fun A ↦ (A.card : ℝ≥0∞) * ⨆ η, ‖isingPotential G J h A η‖ₑ) {i}
      = ENNReal.ofReal |h| := by
    rw [Set.indicator_of_mem (show ({i} : Finset S) ∈ {A : Finset S | i ∈ A} by simp),
      Finset.card_singleton, iSup_enorm_isingPotential_singleton]
    simp
  have hpair : ∀ j ∈ G.neighborFinset i, {A : Finset S | i ∈ A}.indicator
      (fun A ↦ (A.card : ℝ≥0∞) * ⨆ η, ‖isingPotential G J h A η‖ₑ) {i, j}
      = 2 * ENNReal.ofReal |J| := by
    intro j hj
    have hij : G.Adj i j := (SimpleGraph.mem_neighborFinset G i j).1 hj
    rw [Set.indicator_of_mem (show ({i, j} : Finset S) ∈ {A : Finset S | i ∈ A} by simp),
      Finset.card_pair hij.ne, iSup_enorm_isingPotential_pair G J h hij]
    norm_num
  rw [hdef, tsum_eq_sum hzero, Finset.sum_insert hnotmem, Finset.sum_image hinjOn, hsingle,
    Finset.sum_congr rfl hpair, Finset.sum_const, nsmul_eq_mul,
    ENNReal.ofReal_add (abs_nonneg h) (by positivity),
    show (2 : ℝ) * ((G.neighborFinset i).card : ℝ) * |J|
      = ((G.neighborFinset i).card : ℝ) * (2 * |J|) from by ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- **Georgii's norm (8.36) of the pure external field.** The potential `Φ_{i} = −h σ_i` with no
coupling has `‖Φ‖ᵢ' = ∑_{A ∋ i} |A| ‖Φ_A‖ = |h|` at every site `i` of every graph: the only
interaction containing `i` is `{i}`, of cardinality `1` and sup-norm `|h|`. This is
`cardNormAt_isingPotential` at `J = 0`, but on an arbitrary — not necessarily locally finite —
graph. -/
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

/-- **Georgii's energy density (15.22) of the pure external field**: `f_Φ = ∑_{A ∋ i} |A|⁻¹ Φ_A
= −h σ_i`, the only interaction containing `i` being the singleton `{i}`. -/
lemma siteEnergy_isingPotential_of_zero_coupling (i : S) (η : S → Bool) :
    (isingPotential G 0 h).siteEnergy i η = -h * spin (η i) := by
  rw [Potential.siteEnergy, tsum_eq_single ({i} : Finset S)]
  · rw [Potential.siteEnergyTerms_of_mem (Finset.mem_singleton_self i), Finset.card_singleton,
      isingPotential, Potential.nearestNeighbourPair_apply_card_one (Finset.card_singleton i),
      Finset.sum_singleton]
    norm_num
  · intro A hA
    by_cases h0 : i ∈ A
    · have hcard : A.card ≠ 1 := by
        intro hc
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
        exact hA (by simpa using (Finset.mem_singleton.1 h0).symm)
      rw [Potential.siteEnergyTerms_of_mem h0,
        isingPotential_apply_of_zero_coupling_of_card_ne_one G h hcard, mul_zero]
    · exact Potential.siteEnergyTerms_of_not_mem h0 η

/-- **Georgii's specific energy (15.24) of the pure external field**: `⟨μ, Φ⟩ = μ(f_Φ) =
−h μ(σ_0)`, so `−⟨μ, Φ^{0,1}⟩` is the magnetisation `μ(σ_0)`. -/
lemma specificEnergy_isingPotential_of_zero_coupling [Zero S] (μ : Measure (S → Bool)) :
    (isingPotential G 0 h).specificEnergy μ = -h * ∫ σ, spin (σ 0) ∂μ := by
  rw [Potential.specificEnergy]
  simp_rw [Potential.energyDensity, siteEnergy_isingPotential_of_zero_coupling]
  exact integral_const_mul _ _

end CardNorm

/-! ### The norm (8.36) of the `ℤ^d` Ising potential -/

section Lattice

variable (d : ℕ) (J h : ℝ)

/-- **Georgii's norm (8.36) of the `ℤ^d` Ising potential**: `‖Φ‖ = |h| + 4d|J|`, at every site.
Each site of `ℤ^d` carries the one-point interaction `−h σ_i` of norm `|h|` and lies on exactly
`2d` bonds (`card_neighborFinset_latticeGraph`), each contributing `|{i,j}| ‖Φ_{i,j}‖ = 2|J|`. -/
theorem cardNormAt_isingPotential_latticeGraph (i : Fin d → ℤ) :
    Dobrushin.cardNormAt (isingPotential (latticeGraph d) J h) i
      = ENNReal.ofReal (|h| + 4 * d * |J|) := by
  rw [cardNormAt_isingPotential, card_neighborFinset_latticeGraph]
  congr 1
  push_cast
  ring

end Lattice

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

/-- The Gibbsian specification of the `ℬ_Θ`-element `isingBTheta d J h` is the Ising
specification: `isingSpecification` is by definition the Gibbsian specification of the Ising
potential with the uniform a priori spin measure. -/
lemma gibbsSpecificationOfAbsolutelySummable_isingBTheta (β : ℝ) :
    Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (isingBTheta d J h : Potential (Fin d → ℤ) Bool)) uniformSpinMeasure β
      = isingSpecification (latticeGraph d) J h β := rfl

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

variable (d J h) in
/-- **The external field as a direction of `ℬ_Θ`.** `Φ^{J,h} + t Φ^{0,1} = Φ^{J,h+t}`: moving
along the pure-field direction `Φ^{0,1}_{i} = −σ_i` of `ℬ_Θ` is exactly changing the external
field. -/
@[simp] lemma isingBTheta_add_smul_field (t : ℝ) :
    isingBTheta d J h + t • isingBTheta d 0 1 = isingBTheta d J (h + t) :=
  Subtype.ext (isingPotential_add_smul_field (latticeGraph d) J h t)

end BTheta

/-! ### Georgii's region `𝒟` contains a nonzero potential -/

section DobrushinRegion

variable {d : ℕ} {J h : ℝ}

/-- **The `ℤ^d` Ising potential lies in Georgii's region `𝒟` of (8.36)/§16.2 whenever
`|h| + 4d|J| < 1`**, by the computation `‖Φ‖ = |h| + 4d|J|` of
`MeasureTheory.GibbsMeasure.cardNormAt_isingPotential_latticeGraph`. The pure external field
`Φ_{i} = −h σ_i` is the case `J = 0`, where the condition is Georgii's `‖Φ‖ = |h| < 1`. -/
theorem isingBTheta_mem_dobrushinRegion (hJh : |h| + 4 * d * |J| < 1) :
    isingBTheta d J h ∈ Potential.BTheta.dobrushinRegion (Fin d) Bool := by
  rw [Potential.BTheta.mem_dobrushinRegion_iff, coe_isingBTheta,
    cardNormAt_isingPotential_latticeGraph]
  exact ENNReal.ofReal_lt_one.2 hJh

variable (d) in
/-- Georgii's region `𝒟` contains a **nonzero** potential, so
`Potential.BTheta.leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_of_mem_dobrushinRegion`
(Corollary (16.17)) is not vacuous: take the pure external field with `h = 1/2`. -/
theorem exists_ne_zero_mem_dobrushinRegion :
    ∃ Φ : Potential.BTheta (Fin d → ℤ) Bool,
      Φ ∈ Potential.BTheta.dobrushinRegion (Fin d) Bool ∧ Φ ≠ 0 :=
  ⟨isingBTheta d 0 2⁻¹,
    isingBTheta_mem_dobrushinRegion (by rw [abs_zero, mul_zero, add_zero, abs_of_pos] <;> norm_num),
    isingBTheta_ne_zero (by norm_num)⟩

/-- **Georgii's region `𝒟` is strictly inside the Ising region of Dobrushin's condition (8.8).**
`|h| + 4d|J| < 1` forces `4d|J| < 2`, which is the hypothesis of
`MeasureTheory.GibbsMeasure.Dobrushin.isDobrushin_isingSpecification` at `β = 1`; that hypothesis
is the weaker `2d|J| < 1` and does not constrain the field at all, and (8.9)(2)/(8.10)
(`Dobrushin.isDobrushin_isingSpecification_tanh`, `2d tanh|J| < 1`) is weaker still. The loss of
the factor `2` is `Dobrushin.interactionStrength_le_two_mul_cardNormAt`, and the spurious `|h|` is
the singleton term, which the interaction strength of (8.8) discards because `|A| − 1 = 0`. -/
theorem isDobrushin_isingSpecification_of_cardNormAt_lt_one (hJh : |h| + 4 * d * |J| < 1) :
    Dobrushin.IsDobrushin (isingSpecification (latticeGraph d) J h 1) := by
  refine Dobrushin.isDobrushin_isingSpecification d J h 1 ?_
  have h0 : (0 : ℝ) ≤ |h| := abs_nonneg h
  rw [one_mul]
  linarith

end DobrushinRegion

/-! ### Georgii Corollary (16.17) for the Ising model: the pressure in the external field -/

section Pressure

variable {d : ℕ} {J h : ℝ}

/-- **Georgii Corollary (16.17), the first-derivative formula, for the `ℤ^d` Ising model.**
At a coupling and field with `|h| + 4d|J| < 1` — i.e. inside Georgii's region `𝒟`, by
`isingBTheta_mem_dobrushinRegion` — the Ising model has a unique shift-invariant Gibbs measure
`μ`, and the pressure is Gateaux differentiable at `Φ^{J,h}`: the two one-sided directional
derivatives agree, and equal `−⟨μ, Ψ⟩` in every direction `Ψ ∈ ℬ_Θ`. -/
theorem leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta (hJh : |h| + 4 * d * |J| < 1) :
    ∃ μ : Measure ((Fin d → ℤ) → Bool),
      invariantG (isingSpecification (latticeGraph d) J h 1)
          (shiftGroup (Fin d → ℤ) Bool) = {μ} ∧
        ∀ Ψ : Potential.BTheta (Fin d → ℤ) Bool,
          leftDirDeriv (Potential.BTheta.pressure uniformSpinMeasure) (isingBTheta d J h) Ψ
              = -(Ψ : Potential (Fin d → ℤ) Bool).specificEnergy μ ∧
            rightDirDeriv (Potential.BTheta.pressure uniformSpinMeasure) (isingBTheta d J h) Ψ
              = -(Ψ : Potential (Fin d → ℤ) Bool).specificEnergy μ := by
  rw [← gibbsSpecificationOfAbsolutelySummable_isingBTheta d J h 1]
  exact Potential.BTheta.leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_of_mem_dobrushinRegion
    uniformSpinMeasure (isingBTheta_mem_dobrushinRegion hJh)

/-- **`∂P/∂h` is the magnetisation.** Corollary (16.17) in the direction of the external field
`Φ^{0,1}_{i} = −σ_i`, along which `Φ^{J,h} + tΦ^{0,1} = Φ^{J,h+t}`
(`isingBTheta_add_smul_field`): both one-sided derivatives of the pressure in the field equal
`μ(σ_0)`, the magnetisation of the unique shift-invariant Ising Gibbs measure. The sign is
Georgii's: `⟨μ, Φ^{0,1}⟩ = μ(f_{Φ^{0,1}}) = −μ(σ_0)` since the energy density of the field
potential is `−σ_0`. -/
theorem leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta_field
    (hJh : |h| + 4 * d * |J| < 1) :
    ∃ μ : Measure ((Fin d → ℤ) → Bool),
      invariantG (isingSpecification (latticeGraph d) J h 1)
          (shiftGroup (Fin d → ℤ) Bool) = {μ} ∧
        leftDirDeriv (Potential.BTheta.pressure uniformSpinMeasure) (isingBTheta d J h)
            (isingBTheta d 0 1) = ∫ σ, spin (σ 0) ∂μ ∧
          rightDirDeriv (Potential.BTheta.pressure uniformSpinMeasure) (isingBTheta d J h)
            (isingBTheta d 0 1) = ∫ σ, spin (σ 0) ∂μ := by
  obtain ⟨μ, hμ, hdir⟩ := leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta hJh
  obtain ⟨hL, hR⟩ := hdir (isingBTheta d 0 1)
  have hE : -((isingBTheta d 0 1 : Potential (Fin d → ℤ) Bool).specificEnergy μ)
      = ∫ σ, spin (σ 0) ∂μ := by
    rw [coe_isingBTheta, specificEnergy_isingPotential_of_zero_coupling]
    ring
  exact ⟨μ, hμ, hL.trans hE, hR.trans hE⟩

/-- **`∂P/∂h` is the magnetisation, as a genuine derivative.** For `|h| + 4d|J| < 1` the pressure
of the `ℤ^d` Ising model is differentiable in the external field at `h`:
`∂/∂t P(Φ^{J,h+t})|_{t=0} = μ(σ_0)`, the magnetisation of the unique shift-invariant Ising Gibbs
measure. This is `hasDerivAt_pressure_isingBTheta` along the pure-field direction `Φ^{0,1}`, whose
segment `Φ^{J,h} + tΦ^{0,1}` is the field segment `Φ^{J,h+t}` (`isingBTheta_add_smul_field`);
`leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta_field` is the same statement in terms
of the two one-sided directional derivatives of (16.2). -/
theorem hasDerivAt_pressure_isingBTheta_field (hJh : |h| + 4 * d * |J| < 1) :
    ∃ μ : Measure ((Fin d → ℤ) → Bool),
      invariantG (isingSpecification (latticeGraph d) J h 1)
          (shiftGroup (Fin d → ℤ) Bool) = {μ} ∧
        HasDerivAt (fun t : ℝ ↦ Potential.BTheta.pressure uniformSpinMeasure
            (isingBTheta d J (h + t))) (∫ σ, spin (σ 0) ∂μ) 0 := by
  rw [← gibbsSpecificationOfAbsolutelySummable_isingBTheta d J h 1]
  obtain ⟨μ, hμ, hderiv⟩ := Potential.BTheta.hasDerivAt_pressure_of_mem_dobrushinRegion
    uniformSpinMeasure (isingBTheta_mem_dobrushinRegion hJh)
  refine ⟨μ, hμ, ?_⟩
  have hE : -((isingBTheta d 0 1 : Potential (Fin d → ℤ) Bool).specificEnergy μ)
      = ∫ σ, spin (σ 0) ∂μ := by
    rw [coe_isingBTheta, specificEnergy_isingPotential_of_zero_coupling]
    ring
  have h1 := hderiv (isingBTheta d 0 1)
  rw [hE] at h1
  simpa only [isingBTheta_add_smul_field] using h1

/-- **Georgii Corollary (16.17), the second-derivative formula, for the `ℤ^d` Ising model.**
Differentiating the field derivative of the pressure once more: for `|h| + 4d|J| < 1` the map
`t ↦ ∂⁺_{Ψ'} P(Φ^{J,h+t})` is differentiable at `t = 0`, with derivative
`−∑_k cov_μ(f_{Ψ'}, σ_k)`. The outer direction is the external field, whose norm (8.36) is
finite — that is what keeps a whole field interval inside `𝒟`; the inner direction `Ψ'` is an
arbitrary element of `ℬ_Θ`. -/
theorem hasDerivAt_rightDirDeriv_pressure_isingBTheta (hJh : |h| + 4 * d * |J| < 1)
    (Ψ' : Potential.BTheta (Fin d → ℤ) Bool) :
    ∃ μ : Measure ((Fin d → ℤ) → Bool),
      invariantG (isingSpecification (latticeGraph d) J h 1)
          (shiftGroup (Fin d → ℤ) Bool) = {μ} ∧
        HasDerivAt (fun t : ℝ ↦ rightDirDeriv (Potential.BTheta.pressure uniformSpinMeasure)
            (isingBTheta d J (h + t)) Ψ')
          (-∑' k : Fin d → ℤ,
            cov[(Ψ' : Potential (Fin d → ℤ) Bool).siteEnergy 0, fun σ ↦ spin (σ k); μ]) 0 := by
  rw [← gibbsSpecificationOfAbsolutelySummable_isingBTheta d J h 1]
  obtain ⟨μ, hμ, hderiv⟩ :=
    Potential.BTheta.hasDerivAt_rightDirDeriv_pressure_of_mem_dobrushinRegion uniformSpinMeasure
      (isingBTheta_mem_dobrushinRegion hJh) (Ψ := isingBTheta d 0 1)
      (by rw [coe_isingBTheta, cardNormAt_isingPotential_of_zero_coupling]; simp) Ψ'
  refine ⟨μ, hμ, ?_⟩
  have hcov : ∀ k : Fin d → ℤ,
      cov[(Ψ' : Potential (Fin d → ℤ) Bool).siteEnergy 0,
          (isingBTheta d 0 1 : Potential (Fin d → ℤ) Bool).siteEnergy k; μ]
        = -cov[(Ψ' : Potential (Fin d → ℤ) Bool).siteEnergy 0, fun σ ↦ spin (σ k); μ] := by
    intro k
    rw [show (isingBTheta d 0 1 : Potential (Fin d → ℤ) Bool).siteEnergy k
        = fun σ ↦ -spin (σ k) from funext fun σ ↦ by
          rw [coe_isingBTheta, siteEnergy_isingPotential_of_zero_coupling]; ring]
    exact ProbabilityTheory.covariance_fun_neg_right
  simp only [isingBTheta_add_smul_field] at hderiv
  rwa [tsum_congr hcov, tsum_neg] at hderiv

/-- **`∂²P/∂h²` is the susceptibility.** Corollary (16.17) with the external field in both
directions: `t ↦ ∂⁺_h P(Φ^{J,h+t})` — the magnetisation, by
`leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_isingBTheta_field` — is differentiable at `t = 0`
with derivative `∑_k cov_μ(σ_0, σ_k)`, the summed spin-spin covariance. -/
theorem hasDerivAt_rightDirDeriv_pressure_isingBTheta_field (hJh : |h| + 4 * d * |J| < 1) :
    ∃ μ : Measure ((Fin d → ℤ) → Bool),
      invariantG (isingSpecification (latticeGraph d) J h 1)
          (shiftGroup (Fin d → ℤ) Bool) = {μ} ∧
        HasDerivAt (fun t : ℝ ↦ rightDirDeriv (Potential.BTheta.pressure uniformSpinMeasure)
            (isingBTheta d J (h + t)) (isingBTheta d 0 1))
          (∑' k : Fin d → ℤ, cov[fun σ ↦ spin (σ 0), fun σ ↦ spin (σ k); μ]) 0 := by
  obtain ⟨μ, hμ, hderiv⟩ := hasDerivAt_rightDirDeriv_pressure_isingBTheta hJh (isingBTheta d 0 1)
  refine ⟨μ, hμ, ?_⟩
  have h0 : (isingBTheta d 0 1 : Potential (Fin d → ℤ) Bool).siteEnergy 0
      = fun σ ↦ -spin (σ 0) := funext fun σ ↦ by
    rw [coe_isingBTheta, siteEnergy_isingPotential_of_zero_coupling]; ring
  rw [h0] at hderiv
  have hcov : ∀ k : Fin d → ℤ, cov[fun σ ↦ -spin (σ 0), fun σ ↦ spin (σ k); μ]
      = -cov[fun σ ↦ spin (σ 0), fun σ ↦ spin (σ k); μ] :=
    fun _ ↦ ProbabilityTheory.covariance_fun_neg_left
  rwa [tsum_congr hcov, tsum_neg, neg_neg] at hderiv

end Pressure

/-! ### Georgii Corollary (8.37) for the Ising model: response to the external field -/

section FieldResponse

variable {d : ℕ} {J h : ℝ}

/-- **Georgii Corollary (8.37) for the `ℤ^d` Ising model: the fluctuation–response identity.**
Let `|h| + 4d|J| + t₀ < 1`, so that the whole field interval `[h − t₀, h + t₀]` lies inside
Georgii's region `𝒟`. Then the Ising model has a (unique) Gibbs measure `μ_s` at every field
`h + s`, and for a bounded quasilocal observable `g` with `∑_i δ_i(g) < ∞` the mean `μ_s(g)` is
differentiable in the field at every `|t| < t₀`, with

`∂/∂s μ_{h+s}(g)|_{s=t} = ∑_k cov_{μ_{h+t}}(g, σ_k)`.

This is `Dobrushin.hasDerivAt_integral_gibbsMeasure_add_smul` along the field direction
`Φ^{0,1}`, whose site energy is `f_{Φ^{0,1}} ∘ θ_{−k} = −σ_k`; Georgii's minus sign is absorbed
by that of the energy density. The family `μ` is produced by Theorem (8.7) over the standard
Borel state space `Bool` (`Dobrushin.existsUnique_mem_GP_of_isDobrushin_of_standardBorel`), so
the statement is not conditional on a family being given. -/
theorem exists_hasDerivAt_integral_isingGibbsMeasure_field {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hJh : |h| + 4 * d * |J| + t₀ < 1)
    {g : lp (fun _ : (Fin d → ℤ) → Bool ↦ ℝ) ∞}
    (hg : g ∈ quasilocalFunctions (Fin d → ℤ) Bool)
    (hgsum : ∑' i : Fin d → ℤ, Dobrushin.oscAt (⇑g) i ≠ ⊤) :
    ∃ μ : ℝ → Measure ((Fin d → ℤ) → Bool), (∀ s, IsProbabilityMeasure (μ s)) ∧
      (∀ s, Specification.IsGibbsMeasure
        (isingSpecification (latticeGraph d) J (h + s) 1) (μ s)) ∧
      ∀ t : ℝ, |t| < t₀ →
        HasDerivAt (fun s : ℝ ↦ ∫ σ, (g : ((Fin d → ℤ) → Bool) → ℝ) σ ∂(μ s))
          (∑' k : Fin d → ℤ,
            cov[(g : ((Fin d → ℤ) → Bool) → ℝ), fun σ ↦ spin (σ k); μ t]) t := by
  classical
  -- Dobrushin's condition holds at every field along the segment
  have h4 : 4 * (d : ℝ) * |J| < 2 := by
    have h0 : (0 : ℝ) ≤ |h| := abs_nonneg h
    linarith
  have hdob : ∀ s : ℝ, Dobrushin.IsDobrushin (isingSpecification (latticeGraph d) J (h + s) 1) :=
    fun s ↦ Dobrushin.isDobrushin_isingSpecification d J (h + s) 1 (by rwa [one_mul])
  have hex : ∀ s : ℝ, ∃ m : Measure ((Fin d → ℤ) → Bool), IsProbabilityMeasure m ∧
      Specification.IsGibbsMeasure (isingSpecification (latticeGraph d) J (h + s) 1) m := by
    intro s
    obtain ⟨m, hm, -⟩ := Dobrushin.existsUnique_mem_GP_of_isDobrushin_of_standardBorel
      (hdob s).isQuasilocal (hdob s)
    exact ⟨(m : Measure ((Fin d → ℤ) → Bool)), m.2, hm⟩
  choose μ hprob hgibbs using hex
  refine ⟨μ, hprob, hgibbs, fun t ht ↦ ?_⟩
  -- the segment of potentials is the Ising potential at the shifted field
  have hspec : ∀ s : ℝ, Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := isingPotential (latticeGraph d) J h + s • isingPotential (latticeGraph d) 0 1)
      uniformSpinMeasure 1 = isingSpecification (latticeGraph d) J (h + s) 1 := by
    have hcongr : ∀ (Φ Φ' : Potential (Fin d → ℤ) Bool) [Potential.IsPotential Φ]
        [Potential.IsAbsolutelySummable Φ] [Potential.IsPotential Φ']
        [Potential.IsAbsolutelySummable Φ'], Φ = Φ' →
        Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) uniformSpinMeasure 1
          = Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ') uniformSpinMeasure 1 := by
      rintro Φ Φ' _ _ _ _ rfl
      rfl
    exact fun s ↦ hcongr _ _ (isingPotential_add_smul_field (latticeGraph d) J h s)
  have hbind : ∀ s : ℝ, |s| ≤ t₀ → ∀ i : Fin d → ℤ,
      (μ s).bind (Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := isingPotential (latticeGraph d) J h + s • isingPotential (latticeGraph d) 0 1)
        uniformSpinMeasure 1 {i}) = μ s := by
    intro s _ i
    have := hprob s
    rw [hspec s]
    exact (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 (hgibbs s)) {i}
  have hab : ENNReal.ofReal (|h| + 4 * d * |J|) + ENNReal.ofReal t₀ * 1 < 1 := by
    rw [mul_one, ← ENNReal.ofReal_add (by positivity) ht₀.le]
    exact ENNReal.ofReal_lt_one.2 hJh
  have h837 := Dobrushin.hasDerivAt_integral_gibbsMeasure_add_smul
    (Φ := isingPotential (latticeGraph d) J h) (Ψ := isingPotential (latticeGraph d) 0 1)
    (a := ENNReal.ofReal (|h| + 4 * d * |J|)) (b := 1) uniformSpinMeasure ht₀
    (fun i ↦ le_of_eq (cardNormAt_isingPotential_latticeGraph d J h i))
    (fun i ↦ le_of_eq (by rw [cardNormAt_isingPotential_of_zero_coupling]; simp))
    hab hg hgsum hprob hbind ht
  have hcov : ∀ k : Fin d → ℤ,
      cov[(g : ((Fin d → ℤ) → Bool) → ℝ),
          (isingPotential (latticeGraph d) 0 1).siteEnergy k; μ t]
        = -cov[(g : ((Fin d → ℤ) → Bool) → ℝ), fun σ ↦ spin (σ k); μ t] := by
    intro k
    rw [show (isingPotential (latticeGraph d) 0 1).siteEnergy k = fun σ ↦ -spin (σ k) from
      funext fun σ ↦ by rw [siteEnergy_isingPotential_of_zero_coupling]; ring]
    exact ProbabilityTheory.covariance_fun_neg_right
  rwa [tsum_congr hcov, tsum_neg, neg_neg] at h837

end FieldResponse

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

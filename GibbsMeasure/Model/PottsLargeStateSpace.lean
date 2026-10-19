/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PottsOceans
public import GibbsMeasure.Model.SpernerPhaseTransition
public import GibbsMeasure.Specification.PhaseTransition

/-!
# Georgii §19.3.2: Potts' model with a large state space

Georgii, *Gibbs Measures and Phase Transitions*, §19.3.2 — Lemma (19.24), Lemma (19.25) and
Theorem (19.23).

Georgii writes `E = {1, …, N}` for the state space; here it is `ZMod (N + 2)`, so that Georgii's
`N` is `N + 2` throughout, and his standing hypothesis `N > 2` is `1 ≤ N`.  The potential is the
Potts cube potential of `GibbsMeasure/Model/PottsOceans.lean` (`pottsCube`) at the Kronecker
weight `φ = -1_{\{0\}}` (`pottsDelta`); that is exactly Georgii (19.21),
`Φ_C = - ∑_{\{i,j\} ⊆ C, |i - j| = 1} δ(σ_i, σ_j)`.

## Main results

### `C`-potentials in Georgii's `ℬ_Θ` (general; intended home `Specification/PeriodicGibbsLimits`)

* `isAbsolutelySummable_cubePotential`, `mem_BTheta_cubePotential`, `cubeBTheta` — a `C`-potential
  with bounded cube interaction is an element of the Banach space `ℬ_Θ` on which the pressure of
  §15.3 and the tangent functionals of §16.1 live.
* `siteEnergy_cubePotential` — **Georgii (15.22)** for a `C`-potential; and
  `specificEnergy_cubePotential` — **Georgii (15.27)**: `⟨μ, Φ⟩ = μ(Φ_C)` for shift-invariant `μ`.
* `cubeGibbsSpec_eq_gibbsSpecificationOfAbsolutelySummable` and
  `mem_invariantG_of_isGibbsMeasure_cubeGibbsSpec` — the bridge from `𝒢₀(Φ)` of §18.1 to the
  `𝒢_Θ(Φ)` of §16.2.

### The pressure along a ray (general; intended home `Specification/PhaseTransition`)

* `pressure_smul_add_smul_lt_of_not_isEquivalent` — **Corollary (16.15)** in the form Georgii's
  Step 1 uses: `P` is *strictly* convex between two non-equivalent potentials.
* `rightDirDeriv_pressure_smul`, `leftDirDeriv_pressure_smul` — `∂±F_Φ(β)` as directional
  derivatives of `P` at `βΦ` in the direction `Φ/4`.
* `leftDirDeriv_le_le_rightDirDeriv_iff`, `exists_leftDirDeriv_le_le_rightDirDeriv`,
  `eq_of_strictConvexOn_of_forall_le` — one-variable convex analysis (intended home
  `GibbsMeasure/Mathlib/Analysis/Convex/TangentFunctional.lean`).

### Lemma (19.24)

* `pottsF` — **Georgii (19.22)**, `F_Φ(β) = P(βΦ)/4`; `convexOn_pottsF` and
  `strictConvexOn_pottsF` are Georgii's Step 1 (the potentials `βΦ` are pairwise non-equivalent,
  `not_isEquivalent_smul_pottsBTheta`).
* `leftDirDeriv_pottsF_le_le_rightDirDeriv` — **Step 2**: `∂₋F_Φ(β) ≤ μ(σ_i = σ_j) ≤ ∂₊F_Φ(β)`
  for every `r₀`-invariant `μ ∈ 𝒢_Θ(βΦ)` and `|i - j| = 1`, through (16.6)(1), (16.14) and
  `specificEnergy_pottsBTheta` (Georgii's `-⟨μ, Φ⟩ = 4 μ(σ_i = σ_j)`).
* `leftDirDeriv_pottsF_lt_half`, `eventually_half_lt_rightDirDeriv_pottsF` — **Step 3**.
* `existsUnique_pottsBeta`, `pottsBeta`, `pottsBeta_pos`, `measureReal_setOf_eq_lt_half`,
  `half_lt_measureReal_setOf_eq` — **Lemma (19.24)** in full.

### Lemma (19.25), Steps 1 and 2

* `pottsM`, `exists_mem_pottsM`, `pottsSq_of_mem_pottsM` — **Step 1**: the seven excitation
  classes cover `E^C ∖ Ḡ` (patterns with exactly three equal bonds are impossible), with
  `Φ_C = -1` on `M_1, …, M_4` and `Φ_C = -2` on `M_5, M_6, M_7`.
* `periodicGibbsDist_pow_le_prod`, `periodicGibbsDist_forall_mem_le_pow`,
  `forall_mem_latticeCubeView_le_pow` — **Step 2**: Corollary (17.17) for a *family* of classes,
  and its passage to `𝒢₀(Φ)`.  These are general and belong next to
  `MeasureTheory.GibbsMeasure.periodicGibbsDist_pow_le_pow`.
* `forall_notMem_latticePattern_pottsGBar_le` — **Lemma (19.25)** modulo Steps 3–5:
  `μ(D ∩ V(Ḡ, ·) = ∅) ≤ (7c)^{|D|}` for every `c` dominating the seven torus quantities
  `°γ_{Λ(n)}^{βΦ}(A_k)^{1/|Λ(n)|}` eventually in `n`.

### Theorem (19.23)

* `isPStablePartition_pottsPair` — Georgii's stable partition `\{G_0, G\}` of `Ḡ`.
* `exists_gibbsMeasure_pottsCeiling` — **(I)**: the chaotic phase `μ_0 = μ(· | ξ⁰(G_0, ·) ≠ ∅)`
  with `μ_0(ξ⁰(G_0, ·) ≠ ∅) = 1` and `μ_0(0 ∈ ξ⁰(G_0, ·)) ≥ 1 - ε_N`, `ε_N = 8 z(t_N)`.
* `exists_gibbsMeasure_family_potts` — **(II)**: the `N` ordered phases `μ_1, …, μ_N`, mutually
  singular, shift invariant, permuted into one another by the transformations of `E`.
* `isSymmetry_pottsPerm`, `image_pottsPerm_pottsG`, `preimage_pottsPerm_pottsCeiling`,
  `preimage_planeRot_pottsCeiling`, `image_planeRot_pottsG`, `preimage_cubeRefl_pottsCeiling`,
  `image_cubeRefl_pottsG` — the symmetry clauses: `r_0`, `r_1`, `r_2` and all permutations of `E`.
* `leftDirDeriv_lt_rightDirDeriv_pottsF` — the consequence stated after the theorem: a chaotic
  and an ordered phase at the same `β`, with `ε < 1/2`, force `∂₋F_Φ(β) < ∂₊F_Φ(β)`, i.e. a
  first order phase transition.

## What is *not* here

**Steps 3–5 of Georgii's proof of Lemma (19.25)** — the counting estimates `t_{N,k} ≤ N^{-1/4}`
for the seven classes — are not formalised.  They are the hypothesis `hc` of
`forall_notMem_latticePattern_pottsGBar_le` and the hypothesis `hcb` of the two theorems of
(19.23); with them, `t_N = 7 N^{-1/4}` and `ε_N = 8 z(7 N^{-1/4})`.  Georgii's five counting
bounds have been checked by hand and are correct as stated:

`|A_1| < N^{n + 2n²}`, `|B_1| = N^{1 + 4n² - (n+1)²}`, `|A_5| < 4^n N^{n + n²}`,
`|B_5| = N^{1 + 2n(n-1)}`, `|A_7| < 2 N^{2n}`,

as are the resulting ratios `|A_1|/|B_1| < N^{3n - n²}`, `|A_5|/|B_5| < 4^n N^{3n - n²}` and
`|A_7|/|B_5| < 2 N^{4n - 2n²}`.  What is missing is their Lean proof: the structure lemmas ("`ω`
is constant on every even row", "…on every odd column", Georgii's two bits `a, b` for `M_5`, and
"`ω` is constant on each row or on each column" for `M_7`) on the torus `(ℤ/2n)²`, the resulting
cardinality bounds, and `°γ_Λ(A) ≤ |A|/|B|`.

**Part (III)** of Theorem (19.23), the persistence of the `N + 1` phases at `β = β_N`, is not
formalised either: Georgii obtains it from Example (4.11)(2) as a cluster point of
`μ_n ∈ 𝒢₀((β_N - 1/n)Φ)`, which needs the local-convergence compactness argument of
`GibbsMeasure/Specification/CubePotentialConvergence.lean` applied along `β ↑ β_N`.
-/

@[expose] public section

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-!
## `C`-potentials as elements of Georgii's `ℬ_Θ`

A `C`-potential with a bounded cube interaction is absolutely summable and shift invariant, so it
is an element of the Banach space `ℬ_Θ` on which the pressure of §15.3 and the tangent
functionals of §16.1 live.  These lemmas are general; their intended home is
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`, next to `cubePotential`.
-/

section CubeBTheta

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {φ : ((Fin d → Fin 2) → E) → ℝ}

/-- The interaction terms of a `C`-potential are bounded by `|A| ‖Φ_C‖`.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
lemma abs_cubePotential_le {c : ℝ} (hb : ∀ ζ, |φ ζ| ≤ c) (A : Finset (Fin d → ℤ))
    (η : (Fin d → ℤ) → E) : |cubePotential E φ A η| ≤ #A * c := by
  classical
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hb fun _ ↦ η 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ A.filter fun i ↦ latticeCube i = A, |φ (latticeCubeView η i)|
      ≤ ∑ _i ∈ A.filter fun i ↦ latticeCube i = A, c :=
        Finset.sum_le_sum fun i _ ↦ hb _
    _ = #(A.filter fun i ↦ latticeCube i = A) * c := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ #A * c :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Finset.card_filter_le _ _)) hc

/-- **A `C`-potential with bounded cube interaction is absolutely summable.**  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem isAbsolutelySummable_cubePotential (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) :
    Potential.IsAbsolutelySummable (cubePotential E φ) := by
  obtain ⟨c, hc⟩ := hb
  refine Potential.IsAbsolutelySummable.of_isFiniteRange fun A ↦ ?_
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (#A * c)) ENNReal.ofReal_ne_top ?_
  refine iSup_le fun η ↦ ?_
  rw [← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (abs_cubePotential_le hc A η)

/-- **A `C`-potential with bounded cube interaction is an element of Georgii's `ℬ_Θ`.**  Intended
home: `GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem mem_BTheta_cubePotential (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) (hφ : Measurable φ) :
    cubePotential E φ ∈ Potential.BTheta (Fin d → ℤ) E :=
  ⟨⟨isAbsolutelySummable_cubePotential hb,
    cubePotential_eq_zero_of_forall fun i hi ↦
      Finset.notMem_empty i (hi ▸ self_mem_latticeCube i),
    isPotential_cubePotential hφ⟩,
    isShiftInvariant_cubePotential⟩

variable (E φ) in
/-- **A `C`-potential with bounded cube interaction, as an element of Georgii's `ℬ_Θ`.**  Intended
home: `GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
def cubeBTheta (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) (hφ : Measurable φ) :
    Potential.BTheta (Fin d → ℤ) E :=
  ⟨cubePotential E φ, mem_BTheta_cubePotential hb hφ⟩

@[simp] lemma coe_cubeBTheta (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) (hφ : Measurable φ) :
    (cubeBTheta E φ hb hφ : Potential (Fin d → ℤ) E) = cubePotential E φ := rfl

/-- Scaling a `C`-potential scales its cube interaction.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
lemma smul_cubePotential (c : ℝ) :
    c • cubePotential E φ = cubePotential E fun ζ ↦ c * φ ζ := by
  classical
  funext A η
  show c * cubePotential E φ A η = _
  simp only [cubePotential, Finset.mul_sum]

/-- **A bounded `C`-potential over a discrete state space has continuous interactions**, hence
continuous Hamiltonians.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
lemma continuous_cubePotential_apply [TopologicalSpace E] [DiscreteTopology E]
    (A : Finset (Fin d → ℤ)) : Continuous (cubePotential E φ A) := by
  classical
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (continuous_of_discreteTopology (α := (Fin d → Fin 2) → E)).comp
    (continuous_pi fun c ↦ continuous_apply _)

/-- An elementary cube has `2^d` sites.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
lemma card_latticeCube (i : Fin d → ℤ) : #(latticeCube i) = 2 ^ d := by
  classical
  rw [latticeCube, Finset.card_image_of_injective _ (fun c c' h ↦ intCubeCast_injective
    (by simpa using h)), Finset.card_univ, Fintype.card_pi]
  simp

/-- **Georgii (15.22) for a `C`-potential**: the energy density at the site `i` is the average of
the `2^d` cube interactions of the elementary cubes containing `i`.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem siteEnergy_cubePotential (i : Fin d → ℤ) (η : (Fin d → ℤ) → E) :
    (cubePotential E φ).siteEnergy i η
      = ∑ c : Fin d → Fin 2, ((2 ^ d : ℕ) : ℝ)⁻¹ * φ (latticeCubeView η (i - intCubeCast c)) := by
  classical
  have hzero : ∀ A ∉ Finset.univ.image fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c),
      (cubePotential E φ).siteEnergyTerms i η A = 0 := by
    intro A hA
    by_cases hi : i ∈ A
    · rw [Potential.siteEnergyTerms_of_mem hi]
      refine mul_eq_zero_of_right _ (congrFun (cubePotential_eq_zero_of_forall fun j hj ↦ ?_) η)
      obtain ⟨c, rfl⟩ :=
        exists_eq_latticeCube_sub_intCubeCast (show i ∈ latticeCube j by rw [hj]; exact hi)
      exact hA (hj ▸ Finset.mem_image_of_mem
        (fun c : Fin d → Fin 2 ↦ latticeCube (i - intCubeCast c)) (Finset.mem_univ c))
    · exact Potential.siteEnergyTerms_of_not_mem hi η
  rw [Potential.siteEnergy, tsum_eq_sum hzero,
    Finset.sum_image fun c _ c' _ h ↦ latticeCube_sub_intCubeCast_injective i h]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Potential.siteEnergyTerms_of_mem (mem_latticeCube_sub_intCubeCast i c),
    cubePotential_latticeCube, card_latticeCube]

/-- **Georgii (15.27) for a `C`-potential**: the specific energy of a shift-invariant random field
relative to a `C`-potential is `⟨μ, Φ⟩ = μ(Φ_C)`.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem specificEnergy_cubePotential (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) (hφ : Measurable φ)
    {μ : Measure ((Fin d → ℤ) → E)} [IsProbabilityMeasure μ]
    (hμ : ∀ j, MeasurePreserving (shift E j).toFun μ μ) :
    (cubePotential E φ).specificEnergy μ = ∫ η, φ (latticeCubeView η 0) ∂μ := by
  classical
  have hpot := isPotential_cubePotential (E := E) (φ := φ) hφ
  have hsum := isAbsolutelySummable_cubePotential (E := E) (φ := φ) hb
  have hmeas : ∀ j : Fin d → ℤ, Measurable fun η : (Fin d → ℤ) → E ↦
      φ (latticeCubeView η j) := fun j ↦
    hφ.comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _)
  have hbdd : ∀ j : Fin d → ℤ,
      Integrable (fun η : (Fin d → ℤ) → E ↦ φ (latticeCubeView η j)) μ := by
    obtain ⟨c, hc⟩ := hb
    exact fun j ↦ Integrable.of_bound (hmeas j).aestronglyMeasurable c
      (.of_forall fun η ↦ by rw [Real.norm_eq_abs]; exact hc _)
  -- shifting moves the cube view
  have hshift : ∀ j : Fin d → ℤ, ∫ η, φ (latticeCubeView η j) ∂μ
      = ∫ η, φ (latticeCubeView η 0) ∂μ := by
    intro j
    have hcomp : ∀ η : (Fin d → ℤ) → E,
        φ (latticeCubeView ((shift E (-j)).toFun η) 0) = φ (latticeCubeView η j) := by
      intro η
      congr 1
      funext c
      simp [latticeCubeView, shift_toFun_apply, sub_neg_eq_add, add_comm]
    have := (hμ (-j)).integral_comp' (f := (shift E (-j)).toMeasurableEquiv)
      (fun η ↦ φ (latticeCubeView η 0))
    rw [← this]
    exact integral_congr_ae (.of_forall fun η ↦ (hcomp η).symm)
  rw [Potential.specificEnergy]
  have : ∀ η : (Fin d → ℤ) → E, (cubePotential E φ).energyDensity η
      = ∑ c : Fin d → Fin 2, ((2 ^ d : ℕ) : ℝ)⁻¹ * φ (latticeCubeView η (0 - intCubeCast c)) :=
    fun η ↦ siteEnergy_cubePotential 0 η
  simp_rw [this]
  rw [integral_finsetSum _ fun c _ ↦ (hbdd _).const_mul _]
  simp_rw [integral_const_mul, hshift]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
  rw [← mul_assoc]
  norm_num

variable {ν : Measure E} [IsProbabilityMeasure ν]

omit [MeasurableSpace E] in
/-- Two equal absolutely summable potentials have the same Gibbsian specification.  Intended home:
`GibbsMeasure/Potential/Summable.lean`. -/
lemma gibbsSpecificationOfAbsolutelySummable_congr {S F : Type*} [MeasurableSpace F] [Countable S]
    {P Q : Potential S F} (h : P = Q) [Potential.IsPotential P] [Potential.IsAbsolutelySummable P]
    [Potential.IsPotential Q] [Potential.IsAbsolutelySummable Q]
    (ρ : Measure F) [IsProbabilityMeasure ρ] (β : ℝ) :
    Potential.gibbsSpecificationOfAbsolutelySummable (Φ := P) ρ β
      = Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Q) ρ β := by
  subst h
  rfl

/-- **The Gibbsian specification of a bounded `C`-potential is the Gibbsian specification of the
corresponding element of `ℬ_Θ`.**  The `σ`-finite-admissible construction of
`GibbsMeasure/Potential/FiniteReference.lean` and the absolutely summable one of
`GibbsMeasure/Potential/Summable.lean` agree over a probability a priori measure.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem cubeGibbsSpec_eq_gibbsSpecificationOfAbsolutelySummable
    (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c) (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) :
    cubeGibbsSpec E φ ν hφ hM
      = Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (cubeBTheta E φ hb hφ : Potential (Fin d → ℤ) E)) ν 1 := by
  have hpot := isPotential_cubePotential (E := E) (φ := φ) hφ
  have habs := isAbsolutelySummable_cubePotential (E := E) (φ := φ) hb
  rw [← Potential.gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure]
  rfl

/-- Every shift-invariant Gibbs measure of a bounded `C`-potential is an element of Georgii's
`𝒢_Θ(Φ)` for the corresponding potential of `ℬ_Θ`.  Intended home:
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`. -/
theorem mem_invariantG_of_isGibbsMeasure_cubeGibbsSpec (hb : ∃ c : ℝ, ∀ ζ, |φ ζ| ≤ c)
    (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ) {μ : Measure ((Fin d → ℤ) → E)}
    [IsProbabilityMeasure μ] (hg : Specification.IsGibbsMeasure (cubeGibbsSpec E φ ν hφ hM) μ)
    (hs : ∀ a : Fin d → ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    μ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := (cubeBTheta E φ hb hφ : Potential (Fin d → ℤ) E)) ν 1) (shiftGroup (Fin d → ℤ) E) := by
  refine mem_invariantG.2 ⟨inferInstance, ?_, ?_⟩
  · rwa [← cubeGibbsSpec_eq_gibbsSpecificationOfAbsolutelySummable hb hφ hM]
  · refine smulInvariantMeasure_iff_forall_measurePreserving.2 ?_
    rintro τ ⟨a, rfl⟩
    exact hs a

end CubeBTheta

/-!
## The pressure along a ray of `ℬ_Θ`

Georgii's `F_Φ(β) = P(βΦ)/4` of (19.22) is the pressure restricted to the ray `ℝ Φ` and divided
by the number `4` of nearest-neighbour bonds in the unit square.  The two lemmas below express
its one-sided derivatives (16.2) as directional derivatives of `P` at `βΦ` in the direction
`Φ/4`, and give the strict convexity of `P` between two non-equivalent potentials.
-/

section Ray

open Potential Potential.BTheta

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  {ν : Measure E} [IsProbabilityMeasure ν]

/-- **Georgii Corollary (16.15), the form his proof of (19.24) uses.**  The pressure is *strictly*
convex between two potentials which are **not** equivalent in the sense of Definition (2.33).
Georgii's (16.15)(b) is the special case of two distinct `α`-normalized potentials, and its proof
in the tree (`Potential.BTheta.pressure_smul_add_smul_lt_of_isNormalized`) factors through exactly
this statement.  Intended home: `GibbsMeasure/Specification/PhaseTransition.lean`. -/
theorem pressure_smul_add_smul_lt_of_not_isEquivalent [StandardBorelSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] [ν.IsOpenPosMeasure]
    {Φ Ψ : BTheta (ι → ℤ) E}
    (hcont : ∀ Λ : Finset (ι → ℤ),
      Continuous (((Φ : Potential (ι → ℤ) E) - (Ψ : Potential (ι → ℤ) E)).hamiltonian Λ))
    (hne : ¬ Potential.IsEquivalent (Φ : Potential (ι → ℤ) E) (Ψ : Potential (ι → ℤ) E))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    pressure ν (t • Φ + (1 - t) • Ψ) < t * pressure ν Φ + (1 - t) * pressure ν Ψ := by
  have hconv : pressure ν (t • Φ + (1 - t) • Ψ) ≤ t * pressure ν Φ + (1 - t) * pressure ν Ψ :=
    (BTheta.convexOn_pressure ν).2 (Set.mem_univ Φ) (Set.mem_univ Ψ) ht0.le (by linarith) (by ring)
  rcases lt_or_eq_of_le hconv with h | h
  · exact h
  refine absurd ?_ hne
  obtain ⟨L, hL⟩ := subgradientAt_pressure_nonempty ν (t • Φ + (1 - t) • Ψ)
  obtain ⟨hLΦ, hLΨ⟩ := mem_subgradientAt_pressure_of_pressure_eq ν ht0 ht1 h hL
  exact (isEquivalent_iff_forall_pressure_smul_add_smul_eq ν hcont).2
    ((exists_mem_subgradientAt_pressure_inter_iff ν).1 ⟨L, hLΦ, hLΨ⟩)

/-- The difference quotients of `β ↦ P(βΦ)/K` at `β` in the direction `1` are exactly the
difference quotients of `P` at `βΦ` in the direction `K⁻¹Φ`, reparametrised by `t ↦ t/K`. -/
lemma dirSlope_pressure_smul (Φ : BTheta (ι → ℤ) E) {K : ℝ} (hK : 0 < K) (β t : ℝ) :
    dirSlope (pressure ν) (β • Φ) (K⁻¹ • Φ) t
      = dirSlope (fun b ↦ pressure ν (b • Φ) / K) β 1 (t / K) := by
  have h1 : (β : ℝ) + t * K⁻¹ = β + t / K * 1 := by field_simp
  simp only [dirSlope, smul_smul, ← add_smul, smul_eq_mul, h1]
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hK' : K ≠ 0 := hK.ne'
  field_simp

/-- The two families of difference quotients have the same range on any set of steps invariant
under `t ↦ t/K`; in particular on `Ioi 0` and on `Iio 0`. -/
lemma image_dirSlope_pressure_smul (Φ : BTheta (ι → ℤ) E) {K : ℝ} (hK : 0 < K) (β : ℝ)
    {s : Set ℝ} (hs : ∀ t : ℝ, t ∈ s ↔ t / K ∈ s) :
    dirSlope (pressure ν) (β • Φ) (K⁻¹ • Φ) '' s
      = dirSlope (fun b ↦ pressure ν (b • Φ) / K) β 1 '' s := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t / K, (hs t).1 ht, (dirSlope_pressure_smul Φ hK β t).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨K * t, (hs (K * t)).2 ?_, ?_⟩
    · rwa [mul_div_cancel_left₀ _ hK.ne']
    · rw [dirSlope_pressure_smul Φ hK β (K * t), mul_div_cancel_left₀ _ hK.ne']

lemma rightDirDeriv_pressure_smul (Φ : BTheta (ι → ℤ) E) {K : ℝ} (hK : 0 < K) (β : ℝ) :
    rightDirDeriv (pressure ν) (β • Φ) (K⁻¹ • Φ)
      = rightDirDeriv (fun b ↦ pressure ν (b • Φ) / K) β 1 :=
  congrArg sInf (image_dirSlope_pressure_smul Φ hK β fun t ↦ by
    simp only [Set.mem_Ioi]
    refine ⟨fun ht ↦ div_pos ht hK, fun ht ↦ ?_⟩
    have h := mul_pos ht hK
    rwa [div_mul_cancel₀ _ hK.ne'] at h)

lemma leftDirDeriv_pressure_smul (Φ : BTheta (ι → ℤ) E) {K : ℝ} (hK : 0 < K) (β : ℝ) :
    leftDirDeriv (pressure ν) (β • Φ) (K⁻¹ • Φ)
      = leftDirDeriv (fun b ↦ pressure ν (b • Φ) / K) β 1 :=
  congrArg sSup (image_dirSlope_pressure_smul Φ hK β fun t ↦ by
    simp only [Set.mem_Iio]
    refine ⟨fun ht ↦ div_neg_of_neg_of_pos ht hK, fun ht ↦ ?_⟩
    have h := mul_neg_of_neg_of_pos ht hK
    rwa [div_mul_cancel₀ _ hK.ne'] at h)

end Ray

/-!
## Georgii (19.21): the Potts model in the plane

`E = ZMod (N + 2)` is Georgii's `{1, …, N}` (so his `N` is `N + 2 ≥ 3` here), `λ` is the
normalised counting measure, and `Φ` is the `C`-potential with
`Φ_C = -∑_{\{i,j\} ⊆ C, |i-j| = 1} δ(σ_i, σ_j)`.
-/

section PottsSetup

variable {N : ℕ}

/-- **Georgii's Kronecker function** as a bond weight: `pottsDelta (x - y) = -δ(x, y)`.  The
Potts cube interaction (19.21) is `pottsCube pottsDelta 2`. -/
def pottsDelta (n : ZMod (N + 2)) : ℝ := if n = 0 then -1 else 0

@[simp] lemma pottsDelta_zero : pottsDelta (0 : ZMod (N + 2)) = -1 := by simp [pottsDelta]

lemma pottsDelta_sub (x y : ZMod (N + 2)) :
    pottsDelta (x - y) = if x = y then -1 else 0 := by
  simp [pottsDelta, sub_eq_zero]

lemma pottsDelta_sub_comm (x y : ZMod (N + 2)) : pottsDelta (x - y) = pottsDelta (y - x) := by
  rw [pottsDelta_sub, pottsDelta_sub]
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

lemma pottsDelta_mem (n : ZMod (N + 2)) : pottsDelta n = -1 ∨ pottsDelta n = 0 := by
  by_cases h : n = 0 <;> simp [pottsDelta, h]

lemma neg_one_le_pottsDelta (n : ZMod (N + 2)) : -1 ≤ pottsDelta n := by
  rcases pottsDelta_mem n with h | h
  · rw [h]
  · rw [h]; norm_num

lemma pottsDelta_nonpos (n : ZMod (N + 2)) : pottsDelta n ≤ 0 := by
  rcases pottsDelta_mem n with h | h
  · rw [h]; norm_num
  · rw [h]

/-- Georgii's hypothesis `φ(n) > φ(0)` for `n ≠ 0` in (18.32), for the Kronecker weight. -/
lemma pottsDelta_lt (n : ZMod (N + 2)) (hn : n ≠ 0) :
    pottsDelta (0 : ZMod (N + 2)) < pottsDelta n := by
  simp [pottsDelta, hn]

variable (N) in
/-- **Georgii (19.21)**: the Potts cube interaction
`Φ_C = -∑_{\{i,j\} ⊆ C, |i-j| = 1} δ(σ_i, σ_j)` on `E = ZMod (N + 2)`. -/
abbrev pottsSq : ((Fin 2 → Fin 2) → ZMod (N + 2)) → ℝ := pottsCube pottsDelta 2

variable (N) in
/-- Georgii's a priori measure `λ`: the counting measure on `E`, normalised. -/
abbrev pottsNu : Measure (ZMod (N + 2)) := uniformOn (Set.univ : Set (ZMod (N + 2)))

/-- **Georgii (19.21) at the four bonds of the unit square.** -/
lemma pottsSq_apply (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsSq N ζ
      = pottsDelta (ζ (sqCorner 0 0) - ζ (sqCorner 1 0))
        + pottsDelta (ζ (sqCorner 0 1) - ζ (sqCorner 1 1))
        + pottsDelta (ζ (sqCorner 0 0) - ζ (sqCorner 0 1))
        + pottsDelta (ζ (sqCorner 1 0) - ζ (sqCorner 1 1)) :=
  cubeBondSum_two (fun x y ↦ pottsDelta_sub_comm x y) ζ

lemma pottsSq_nonpos (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : pottsSq N ζ ≤ 0 := by
  rw [pottsSq_apply]
  have h := pottsDelta_nonpos (N := N)
  linarith [h (ζ (sqCorner 0 0) - ζ (sqCorner 1 0)), h (ζ (sqCorner 0 1) - ζ (sqCorner 1 1)),
    h (ζ (sqCorner 0 0) - ζ (sqCorner 0 1)), h (ζ (sqCorner 1 0) - ζ (sqCorner 1 1))]

lemma neg_four_le_pottsSq (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : -4 ≤ pottsSq N ζ := by
  rw [pottsSq_apply]
  have h := neg_one_le_pottsDelta (N := N)
  linarith [h (ζ (sqCorner 0 0) - ζ (sqCorner 1 0)), h (ζ (sqCorner 0 1) - ζ (sqCorner 1 1)),
    h (ζ (sqCorner 0 0) - ζ (sqCorner 0 1)), h (ζ (sqCorner 1 0) - ζ (sqCorner 1 1))]

lemma abs_pottsSq_le (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : |pottsSq N ζ| ≤ 4 :=
  abs_le.2 ⟨neg_four_le_pottsSq ζ, le_trans (pottsSq_nonpos ζ) (by norm_num)⟩

lemma pottsSq_bddAbove : ∃ c : ℝ, ∀ ζ, |pottsSq N ζ| ≤ c := ⟨4, abs_pottsSq_le⟩

lemma pottsSq_bddBelow : ∃ M : ℝ, ∀ ζ, M ≤ pottsSq N ζ := ⟨-4, neg_four_le_pottsSq⟩

lemma measurable_pottsSq : Measurable (pottsSq N) := measurable_pottsCube

lemma pottsSq_cubeRefl (k : Fin 2) (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsSq N (cubeRefl (ZMod (N + 2)) k ζ) = pottsSq N ζ := pottsCube_cubeRefl k ζ

/-- **Georgii's local ground states of (19.21)**: the constant configurations `(nn/nn)`. -/
theorem pottsSq_eq_neg_four_iff (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsSq N ζ = -4 ↔ ∃ x, ζ = fun _ ↦ x := by
  have h := pottsCube_eq_iff (φ := pottsDelta (N := N)) pottsDelta_lt ζ
  rw [pottsDelta_zero] at h
  rw [show (-4 : ℝ) = 4 * (-1) by norm_num]
  exact h


end PottsSetup

/-!
## Georgii (19.22) and Lemma (19.24): the threshold `β_N`
-/

section PottsPressure

variable {N : ℕ}

/-- The discrete topology on the finite state space `E`.  It is used only to invoke Georgii's
Theorem (2.34) through Corollary (16.15)(a). -/
local instance pottsTopologicalSpace : TopologicalSpace (ZMod (N + 2)) := ⊥

local instance pottsDiscreteTopology : DiscreteTopology (ZMod (N + 2)) := ⟨rfl⟩

local instance pottsOpensMeasurableSpace : OpensMeasurableSpace (ZMod (N + 2)) :=
  ⟨by rw [borel_eq_top_of_discrete]; exact fun s _ ↦ MeasurableSet.of_discrete⟩

/-- Georgii's a priori measure charges every nonempty set. -/
local instance pottsIsOpenPosMeasure : (pottsNu N).IsOpenPosMeasure :=
  ⟨fun U _ hne h0 ↦ by
    obtain ⟨x, hx⟩ := hne
    exact uniformOn_univ_singleton_ne_zero x
      (measure_mono_null (Set.singleton_subset_iff.2 hx) h0)⟩

variable (N) in
/-- The Potts cube interaction (19.21) as an element of Georgii's `ℬ_Θ`. -/
def pottsBTheta : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2)) :=
  cubeBTheta (ZMod (N + 2)) (pottsSq N) pottsSq_bddAbove measurable_pottsSq

@[simp] lemma coe_pottsBTheta :
    (pottsBTheta N : Potential (Fin 2 → ℤ) (ZMod (N + 2)))
      = cubePotential (ZMod (N + 2)) (pottsSq N) := rfl

lemma coe_smul_pottsBTheta (β : ℝ) :
    ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))
      = cubePotential (ZMod (N + 2)) fun ζ ↦ β * pottsSq N ζ := by
  rw [Submodule.coe_smul, coe_pottsBTheta, smul_cubePotential]

variable (N) in
/-- **Georgii (19.22)**: `F_Φ(β) = P(βΦ)/4`, the pressure of the Potts model along the ray `ℝΦ`,
normalised by the number `4` of nearest-neighbour bonds of the unit square. -/
def pottsF (β : ℝ) : ℝ := Potential.BTheta.pressure (pottsNu N) (β • pottsBTheta N) / 4

/-- **Georgii, the sentence after (19.22)**: `F_Φ` is convex, by Proposition (16.1). -/
theorem convexOn_pottsF : ConvexOn ℝ (Set.univ : Set ℝ) (pottsF N) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab ↦ ?_⟩
  have h := (Potential.BTheta.convexOn_pressure (pottsNu N)).2
    (Set.mem_univ (x • pottsBTheta N)) (Set.mem_univ (y • pottsBTheta N)) ha hb hab
  simp only [pottsF, smul_eq_mul] at h ⊢
  rw [show (a * x + b * y) • pottsBTheta N
      = a • (x • pottsBTheta N) + b • (y • pottsBTheta N) by module]
  linarith

/-! ### Georgii, Step 1: `F_Φ` is strictly convex -/

/-- The single-site Hamiltonian of the Potts model at the origin, as a function of the
configuration: `∑_{c ∈ C} Φ_C ∘ θ_{-(0 - c)}`. -/
lemma hamiltonian_smul_pottsBTheta_singleton (β : ℝ) (σ : (Fin 2 → ℤ) → ZMod (N + 2)) :
    ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2))).hamiltonian {0} σ
      = β * ∑ c : Fin 2 → Fin 2, pottsSq N (latticeCubeView σ (0 - intCubeCast c)) := by
  rw [coe_smul_pottsBTheta, hamiltonian_cubePotential_singleton, Finset.mul_sum]

/-- **Georgii, Step 1 of the proof of (19.24): the potentials `βΦ`, `β ≥ 0`, are pairwise
non-equivalent.**  Georgii argues through the equivalent normalized pair potential `Ψ` and
Theorem (2.35).  Here it is immediate: the single-site Hamiltonian `H_{\{0\}}^Φ` takes the value
`-16` at the constant configuration `0` and a strictly larger value at the configuration which
differs from it only at the origin, so `H_{\{0\}}^{(β - β')Φ}` is not `𝓣_{\{0\}}`-measurable
unless `β = β'`. -/
theorem not_isEquivalent_smul_pottsBTheta {β β' : ℝ} (hββ' : β ≠ β') :
    ¬ Potential.IsEquivalent
      ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))
      ((β' • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2))) := by
  classical
  haveI : Fact (1 < N + 2) := ⟨by omega⟩
  intro h
  set σ : (Fin 2 → ℤ) → ZMod (N + 2) := fun _ ↦ 0 with hσ
  set σ' : (Fin 2 → ℤ) → ZMod (N + 2) := fun j ↦ if j = 0 then 1 else 0 with hσ'
  -- the two configurations agree off the origin
  have hagree : ∀ j ∈ ((({0} : Finset (Fin 2 → ℤ)) : Set (Fin 2 → ℤ))ᶜ), σ j = σ' j := by
    intro j hj
    have hj0 : j ≠ 0 := by simpa using hj
    simp [hσ, hσ', hj0]
  have hdep := (measurable_cylinderEvents_iff_dependsOn.1 (h {0})).2 hagree
  -- the two single-site Hamiltonians
  have hH : ∀ τ : (Fin 2 → ℤ) → ZMod (N + 2),
      ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) -
          (β' • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
          Potential (Fin 2 → ℤ) (ZMod (N + 2))).hamiltonian {0} τ
        = (β - β') * ∑ c : Fin 2 → Fin 2, pottsSq N (latticeCubeView τ (0 - intCubeCast c)) := by
    intro τ
    rw [Potential.hamiltonian_sub, hamiltonian_smul_pottsBTheta_singleton,
      hamiltonian_smul_pottsBTheta_singleton, sub_mul]
  rw [hH σ, hH σ'] at hdep
  have hne : (β - β') ≠ 0 := sub_ne_zero.2 hββ'
  have hsum := mul_left_cancel₀ hne hdep
  -- the constant configuration has all four cube energies equal to `-4`
  have hσval : ∀ c : Fin 2 → Fin 2, pottsSq N (latticeCubeView σ (0 - intCubeCast c)) = -4 := by
    intro c
    refine (pottsSq_eq_neg_four_iff _).2 ⟨0, ?_⟩
    funext c'
    simp [hσ]
  -- the perturbed configuration has a strictly larger energy in the cube based at the origin
  have hview : ∀ c c' : Fin 2 → Fin 2,
      latticeCubeView σ' (0 - intCubeCast c) c' = if c' = c then 1 else 0 := by
    intro c c'
    have habel : (0 : Fin 2 → ℤ) - intCubeCast c + intCubeCast c'
        = intCubeCast c' - intCubeCast c := by abel
    have hzero : (0 : Fin 2 → ℤ) - intCubeCast c + intCubeCast c' = 0 ↔ c' = c := by
      rw [habel, sub_eq_zero]
      exact ⟨fun hh ↦ intCubeCast_injective hh, fun hh ↦ by rw [hh]⟩
    show (if (0 : Fin 2 → ℤ) - intCubeCast c + intCubeCast c' = 0 then (1 : ZMod (N + 2)) else 0)
      = if c' = c then 1 else 0
    by_cases hc : c' = c
    · rw [if_pos hc, if_pos (hzero.2 hc)]
    · rw [if_neg hc, if_neg (fun hcon ↦ hc (hzero.1 hcon))]
  have hnonconst : ¬ ∃ x : ZMod (N + 2),
      latticeCubeView σ' (0 - intCubeCast (0 : Fin 2 → Fin 2)) = fun _ ↦ x := by
    rintro ⟨x, hx⟩
    have h1 : latticeCubeView σ' (0 - intCubeCast (0 : Fin 2 → Fin 2)) 0 = 1 := by
      rw [hview 0 0, if_pos rfl]
    have h2 : latticeCubeView σ' (0 - intCubeCast (0 : Fin 2 → Fin 2)) (sqCorner 1 0) = 0 := by
      refine (hview 0 (sqCorner 1 0)).trans (if_neg ?_)
      intro hcon
      have := congrFun hcon 0
      simp at this
    rw [hx] at h1 h2
    exact one_ne_zero (h1.symm.trans h2)
  have hstrict : (-4 : ℝ) < pottsSq N (latticeCubeView σ' (0 - intCubeCast (0 : Fin 2 → Fin 2))) :=
    lt_of_le_of_ne (neg_four_le_pottsSq _) fun hcon ↦
      hnonconst ((pottsSq_eq_neg_four_iff _).1 hcon.symm)
  have hlt : ∑ c : Fin 2 → Fin 2, pottsSq N (latticeCubeView σ (0 - intCubeCast c))
      < ∑ c : Fin 2 → Fin 2, pottsSq N (latticeCubeView σ' (0 - intCubeCast c)) := by
    refine Finset.sum_lt_sum (fun c _ ↦ ?_) ⟨0, Finset.mem_univ _, ?_⟩
    · rw [hσval c]
      exact neg_four_le_pottsSq _
    · rw [hσval 0]
      exact hstrict
  exact absurd hsum hlt.ne

/-- **Georgii, Step 1 of the proof of (19.24): `F_Φ` is strictly convex.**  By Corollary (16.15)
the pressure is strictly convex between two non-equivalent potentials, and the potentials `βΦ`
are pairwise non-equivalent (`not_isEquivalent_smul_pottsBTheta`). -/
theorem strictConvexOn_pottsF : StrictConvexOn ℝ (Set.univ : Set ℝ) (pottsF N) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab ↦ ?_⟩
  have hcont : ∀ Λ : Finset (Fin 2 → ℤ),
      Continuous ((((x • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
          Potential (Fin 2 → ℤ) (ZMod (N + 2)))
        - ((y • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
          Potential (Fin 2 → ℤ) (ZMod (N + 2)))).hamiltonian Λ) := by
    intro Λ
    have hX : (((x • pottsBTheta N - y • pottsBTheta N :
          Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
          Potential (Fin 2 → ℤ) (ZMod (N + 2))))
        = ((x • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
            Potential (Fin 2 → ℤ) (ZMod (N + 2)))
          - ((y • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
            Potential (Fin 2 → ℤ) (ZMod (N + 2))) := by
      rw [Submodule.coe_sub]
    rw [← hX]
    refine Potential.continuous_hamiltonian_of_isUniformlyConvergent
      Potential.isUniformlyConvergent_of_isAbsolutelySummable (fun A ↦ ?_) Λ
    rw [hX, coe_smul_pottsBTheta, coe_smul_pottsBTheta]
    exact (continuous_cubePotential_apply A).sub (continuous_cubePotential_apply A)
  have h := pressure_smul_add_smul_lt_of_not_isEquivalent (ν := pottsNu N) hcont
    (not_isEquivalent_smul_pottsBTheta hxy) ha (by linarith)
  have hb' : (1 : ℝ) - a = b := by linarith
  rw [hb'] at h
  simp only [pottsF, smul_eq_mul]
  rw [show (a * x + b * y) • pottsBTheta N
      = a • (x • pottsBTheta N) + b • (y • pottsBTheta N) by module]
  linarith

/-! ### Georgii, Step 2: the one-sided derivatives bracket `μ(σ_i = σ_j)` -/

/-- The `μ`-probability that the two spins of a bond agree.  Georgii writes `μ(σ_i = σ_j)`. -/
lemma measurableSet_setOf_eq_apply (a b : Fin 2 → ℤ) :
    MeasurableSet {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω a = ω b} :=
  measurableSet_eq_fun (measurable_pi_apply a) (measurable_pi_apply b)

lemma integral_pottsDelta_sub (a b : Fin 2 → ℤ)
    {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))} [IsProbabilityMeasure μ] :
    ∫ η, pottsDelta (η a - η b) ∂μ = -μ.real {ω | ω a = ω b} := by
  have hfun : (fun η : (Fin 2 → ℤ) → ZMod (N + 2) ↦ pottsDelta (η a - η b))
      = fun η ↦ -Set.indicator {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω a = ω b} 1 η := by
    funext η
    rw [pottsDelta_sub]
    by_cases h : η a = η b
    · rw [if_pos h, Set.indicator_of_mem (show η ∈ {ω | ω a = ω b} from h)]
      norm_num
    · rw [if_neg h, Set.indicator_of_notMem (show η ∉ {ω | ω a = ω b} from h)]
      norm_num
  rw [hfun, integral_neg, integral_indicator_one (measurableSet_setOf_eq_apply a b)]

/-- Shift invariance moves a bond to any translate of it. -/
lemma measureReal_setOf_eq_apply_shift {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))}
    (hs : ∀ c : Fin 2 → ℤ, MeasurePreserving (shift (ZMod (N + 2)) c).toFun μ μ)
    (a b c : Fin 2 → ℤ) :
    μ.real {ω | ω (a + c) = ω (b + c)} = μ.real {ω | ω a = ω b} := by
  have hpre : (shift (ZMod (N + 2)) c).toFun ⁻¹' {ω | ω (a + c) = ω (b + c)}
      = {ω | ω a = ω b} := by
    ext ω
    simp
  have h := (hs c).measure_preimage (measurableSet_setOf_eq_apply (a + c) (b + c)).nullMeasurableSet
  rw [hpre] at h
  rw [Measure.real, Measure.real, h]

/-! #### The two nearest-neighbour directions -/

/-- The unit vector `e_1` of `ℤ^2`, as the corner `(1,0)` of the unit square. -/
abbrev pottsE1 : Fin 2 → ℤ := intCubeCast (sqCorner 1 0)

/-- The unit vector `e_2` of `ℤ^2`, as the corner `(0,1)` of the unit square. -/
abbrev pottsE2 : Fin 2 → ℤ := intCubeCast (sqCorner 0 1)

lemma intCubeCast_sqCorner_zero_zero : intCubeCast (sqCorner 0 0) = (0 : Fin 2 → ℤ) := by
  funext k; fin_cases k <;> simp [intCubeCast]

lemma intCubeCast_sqCorner_one_one :
    intCubeCast (sqCorner 1 1) = pottsE1 + pottsE2 := by
  funext k; fin_cases k <;> simp [intCubeCast]

lemma planeRotSite_zero_eq : CubeTransformation.planeRotSite (0 : Fin 2 → ℤ) = pottsE2 := by
  funext k; fin_cases k <;> simp [intCubeCast]

lemma planeRotSite_pottsE1_eq :
    CubeTransformation.planeRotSite (pottsE1) = (0 : Fin 2 → ℤ) := by
  funext k
  fin_cases k <;>
    simp [CubeTransformation.planeRotSite_zero, CubeTransformation.planeRotSite_one, intCubeCast]

/-- **The rotation `r₀` exchanges the two lattice directions**: an `r₀`-invariant random field
gives the same probability to the two nearest-neighbour bonds at the origin. -/
theorem measureReal_setOf_eq_apply_planeRot {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))}
    (hr : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun μ μ) :
    μ.real {ω | ω 0 = ω (pottsE1)} = μ.real {ω | ω 0 = ω (pottsE2)} := by
  have hpre : ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice
        (ZMod (N + 2))).toFun ⁻¹' {ω | ω 0 = ω (pottsE1)}
      = {ω | ω 0 = ω (pottsE2)} := by
    ext ω
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      CubeTransformation.planeRot_onLattice_toFun_apply,
      CubeTransformation.planeRot_onLattice_toFun_apply, planeRotSite_zero_eq,
      planeRotSite_pottsE1_eq]
    exact eq_comm
  have h := hr.measure_preimage
    (measurableSet_setOf_eq_apply (0 : Fin 2 → ℤ) (pottsE1)).nullMeasurableSet
  rw [hpre] at h
  rw [Measure.real, Measure.real, h]

/-- **Georgii, Step 2 of the proof of (19.24), the identity (15.27)**: for an `r₀`-invariant
shift-invariant random field, `-⟨μ, Φ⟩ = -μ(Φ_C) = 4 μ(σ_i = σ_j)` whenever `|i - j| = 1`. -/
theorem specificEnergy_pottsBTheta {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))}
    [IsProbabilityMeasure μ]
    (hs : ∀ c : Fin 2 → ℤ, MeasurePreserving (shift (ZMod (N + 2)) c).toFun μ μ)
    (hr : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun μ μ) :
    ((pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2))).specificEnergy μ
      = -4 * μ.real {ω | ω 0 = ω (pottsE1)} := by
  classical
  rw [coe_pottsBTheta, specificEnergy_cubePotential pottsSq_bddAbove measurable_pottsSq hs]
  have hview : ∀ (η : (Fin 2 → ℤ) → ZMod (N + 2)) (c : Fin 2 → Fin 2),
      latticeCubeView η 0 c = η (intCubeCast c) := fun η c ↦ by
    rw [latticeCubeView_apply, zero_add]
  have hsplit : ∀ η : (Fin 2 → ℤ) → ZMod (N + 2), pottsSq N (latticeCubeView η 0)
      = pottsDelta (η 0 - η (pottsE1)) + pottsDelta (η (pottsE2) - η (pottsE1 + pottsE2))
        + pottsDelta (η 0 - η (pottsE2)) + pottsDelta (η (pottsE1) - η (pottsE1 + pottsE2))
        := by
    intro η
    rw [pottsSq_apply, hview, hview, hview, hview, intCubeCast_sqCorner_zero_zero,
      intCubeCast_sqCorner_one_one]
  simp only [hsplit]
  have hint : ∀ a b : Fin 2 → ℤ,
      Integrable (fun η : (Fin 2 → ℤ) → ZMod (N + 2) ↦ pottsDelta (η a - η b)) μ := by
    intro a b
    refine Integrable.of_bound (Measurable.aestronglyMeasurable (by fun_prop)) 1
      (.of_forall fun η ↦ ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨neg_one_le_pottsDelta _, le_trans (pottsDelta_nonpos _) zero_le_one⟩
  have i1 := hint (0 : Fin 2 → ℤ) pottsE1
  have i2 := hint pottsE2 (pottsE1 + pottsE2)
  have i3 := hint (0 : Fin 2 → ℤ) pottsE2
  have i4 := hint pottsE1 (pottsE1 + pottsE2)
  have i12 : Integrable (fun η : (Fin 2 → ℤ) → ZMod (N + 2) ↦
      pottsDelta (η 0 - η pottsE1) + pottsDelta (η pottsE2 - η (pottsE1 + pottsE2))) μ := i1.add i2
  have i123 : Integrable (fun η : (Fin 2 → ℤ) → ZMod (N + 2) ↦
      pottsDelta (η 0 - η pottsE1) + pottsDelta (η pottsE2 - η (pottsE1 + pottsE2))
        + pottsDelta (η 0 - η pottsE2)) μ := i12.add i3
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_pottsDelta_sub, integral_pottsDelta_sub, integral_pottsDelta_sub,
    integral_pottsDelta_sub]
  have h2 : μ.real {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω (pottsE2) = ω (pottsE1 + pottsE2)}
      = μ.real {ω | ω 0 = ω (pottsE1)} := by
    have := measureReal_setOf_eq_apply_shift hs (0 : Fin 2 → ℤ) (pottsE1) (pottsE2)
    rwa [zero_add] at this
  have h4 : μ.real {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω (pottsE1) = ω (pottsE1 + pottsE2)}
      = μ.real {ω | ω 0 = ω (pottsE2)} := by
    have := measureReal_setOf_eq_apply_shift hs (0 : Fin 2 → ℤ) (pottsE2) (pottsE1)
    rw [zero_add, show pottsE2 + pottsE1 = pottsE1 + pottsE2 by abel] at this
    exact this
  rw [h2, h4, measureReal_setOf_eq_apply_planeRot hr]
  ring

lemma pottsF_eq :
    pottsF N = fun b ↦ Potential.BTheta.pressure (pottsNu N) (b • pottsBTheta N) / 4 := rfl

/-- **Georgii, Step 2 of the proof of Lemma (19.24).**  Remark (16.6)(1) combined with Theorem
(16.14) and (15.27): for every `β ∈ ℝ`, every `r₀`-invariant `μ ∈ 𝒢_Θ(βΦ)` and every pair of
sites at distance `1`,

`∂₋F_Φ(β) ≤ μ(σ_i = σ_j) ≤ ∂₊F_Φ(β)`. -/
theorem leftDirDeriv_pottsF_le_le_rightDirDeriv (β : ℝ)
    {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))} [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
      (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))))
    (hr : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun μ μ) :
    leftDirDeriv (pottsF N) β 1 ≤ μ.real {ω | ω 0 = ω pottsE1} ∧
      μ.real {ω | ω 0 = ω pottsE1} ≤ rightDirDeriv (pottsF N) β 1 := by
  obtain ⟨-, hs⟩ := mem_invariantFields_shiftGroup.1 hμ.2
  have hL := Potential.BTheta.mem_subgradientAt_pressure_of_mem_invariantG (pottsNu N) hμ
  have hval : Potential.BTheta.specificEnergyFunctional μ
      ((4 : ℝ)⁻¹ • pottsBTheta N) = μ.real {ω | ω 0 = ω pottsE1} := by
    rw [Potential.BTheta.specificEnergyFunctional_apply, Submodule.coe_smul,
      Potential.specificEnergy_smul, specificEnergy_pottsBTheta hs hr]
    ring
  have h2 := ConvexOn.le_rightDirDeriv_of_mem_subgradientAt hL ((4 : ℝ)⁻¹ • pottsBTheta N)
  have h1 := (Potential.BTheta.convexOn_pressure (pottsNu N)).leftDirDeriv_le_of_mem_subgradientAt
    hL ((4 : ℝ)⁻¹ • pottsBTheta N)
  rw [hval] at h1 h2
  rw [rightDirDeriv_pressure_smul (pottsBTheta N) (by norm_num : (0 : ℝ) < 4) β] at h2
  rw [leftDirDeriv_pressure_smul (pottsBTheta N) (by norm_num : (0 : ℝ) < 4) β] at h1
  exact ⟨h1, h2⟩

end PottsPressure

/-!
## One-variable convex analysis

The three lemmas below are statements about an arbitrary convex function of one real variable.
Intended home: `GibbsMeasure/Mathlib/Analysis/Convex/TangentFunctional.lean`.
-/

section ConvexReal

variable {f : ℝ → ℝ}

/-- **`∂₋f(x) ≤ c ≤ ∂₊f(x)` says exactly that `x` minimizes `y ↦ f y - c y`.** -/
theorem leftDirDeriv_le_le_rightDirDeriv_iff (hf : ConvexOn ℝ (Set.univ : Set ℝ) f) (x c : ℝ) :
    (leftDirDeriv f x 1 ≤ c ∧ c ≤ rightDirDeriv f x 1) ↔ ∀ y, f x - c * x ≤ f y - c * y := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨L, hL, hL1⟩ := hf.exists_mem_subgradientAt_apply_eq x 1 ⟨h1, h2⟩
    intro y
    have h := hL (y - x)
    rw [show x + (y - x) = y by ring] at h
    have hLy : L (y - x) = c * (y - x) := by
      have hsm : L ((y - x) • (1 : ℝ)) = (y - x) • L 1 := map_smul L _ _
      simpa [hL1, mul_comm] using hsm
    rw [hLy] at h
    linarith
  · intro h
    set L : ℝ →ₗ[ℝ] ℝ := c • LinearMap.id with hLdef
    have hLy : ∀ y : ℝ, L y = c * y := fun y ↦ by simp [hLdef]
    have hL : L ∈ subgradientAt f x := by
      intro y
      have hy := h (x + y)
      rw [hLy]
      have : c * (x + y) = c * x + c * y := by ring
      linarith [hy, this]
    have hL1 : L 1 = c := by rw [hLy]; ring
    refine ⟨?_, ?_⟩
    · have := hf.leftDirDeriv_le_of_mem_subgradientAt hL 1
      rwa [hL1] at this
    · have := ConvexOn.le_rightDirDeriv_of_mem_subgradientAt hL 1
      rwa [hL1] at this

/-- To the left of a point where `∂₋f < c`, the function `f - c·` is strictly larger. -/
theorem lt_sub_of_leftDirDeriv_lt (hf : ConvexOn ℝ (Set.univ : Set ℝ) f) {a c : ℝ}
    (ha : leftDirDeriv f a 1 < c) {y : ℝ} (hy : y < a) : f a - c * a < f y - c * y := by
  have hslope := hf.dirSlope_le_leftDirDeriv a 1 (t := y - a) (by linarith)
  rw [dirSlope, show a + (y - a) • (1 : ℝ) = y by simp] at hslope
  have h : (f y - f a) / (y - a) < c := lt_of_le_of_lt hslope ha
  have hneg : y - a < 0 := by linarith
  have := (div_lt_iff_of_neg hneg).1 h
  linarith

/-- To the right of a point where `c < ∂₊f`, the function `f - c·` is strictly larger. -/
theorem lt_sub_of_lt_rightDirDeriv (hf : ConvexOn ℝ (Set.univ : Set ℝ) f) {b c : ℝ}
    (hb : c < rightDirDeriv f b 1) {y : ℝ} (hy : b < y) : f b - c * b < f y - c * y := by
  have hslope := hf.rightDirDeriv_le_dirSlope b 1 (t := y - b) (by linarith)
  rw [dirSlope, show b + (y - b) • (1 : ℝ) = y by simp] at hslope
  have h : c < (f y - f b) / (y - b) := lt_of_lt_of_le hb hslope
  have hpos : 0 < y - b := by linarith
  have := (lt_div_iff₀ hpos).1 h
  linarith

/-- **Existence of a point at which `c` is a subgradient.**  If `∂₋f(a) < c` and `c < ∂₊f(b)`
for some `a ≤ b`, then the continuous convex function `f - c·` attains its minimum on `[a, b]`,
and that minimum is global. -/
theorem exists_leftDirDeriv_le_le_rightDirDeriv (hf : ConvexOn ℝ (Set.univ : Set ℝ) f)
    (hcont : Continuous f) {a b c : ℝ} (hab : a ≤ b) (ha : leftDirDeriv f a 1 < c)
    (hb : c < rightDirDeriv f b 1) :
    ∃ x ∈ Set.Icc a b, leftDirDeriv f x 1 ≤ c ∧ c ≤ rightDirDeriv f x 1 := by
  set g : ℝ → ℝ := fun y ↦ f y - c * y with hg
  have hgcont : Continuous g := hcont.sub (continuous_const.mul continuous_id)
  obtain ⟨x, hxmem, hxmin⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_isMinOn ⟨a, Set.left_mem_Icc.2 hab⟩
      hgcont.continuousOn
  refine ⟨x, hxmem, (leftDirDeriv_le_le_rightDirDeriv_iff hf x c).2 fun y ↦ ?_⟩
  rcases lt_trichotomy y a with hy | hy | hy
  · exact le_trans (hxmin (Set.left_mem_Icc.2 hab)) (lt_sub_of_leftDirDeriv_lt hf ha hy).le
  · exact hy ▸ hxmin (Set.left_mem_Icc.2 hab)
  rcases le_or_gt y b with hyb | hyb
  · exact hxmin ⟨hy.le, hyb⟩
  · exact le_trans (hxmin (Set.right_mem_Icc.2 hab)) (lt_sub_of_lt_rightDirDeriv hf hb hyb).le

/-- **Uniqueness of the point at which `c` is a subgradient**, for a strictly convex function. -/
theorem eq_of_strictConvexOn_of_forall_le (hf : StrictConvexOn ℝ (Set.univ : Set ℝ) f) {c : ℝ}
    {x x' : ℝ} (hx : ∀ y, f x - c * x ≤ f y - c * y) (hx' : ∀ y, f x' - c * x' ≤ f y - c * y) :
    x = x' := by
  by_contra hne
  have hmid := hf.2 (Set.mem_univ x) (Set.mem_univ x') hne
    (show (0 : ℝ) < 2⁻¹ by norm_num) (show (0 : ℝ) < 2⁻¹ by norm_num)
    (show (2 : ℝ)⁻¹ + 2⁻¹ = 1 by norm_num)
  have h1 := hx ((2 : ℝ)⁻¹ • x + (2 : ℝ)⁻¹ • x')
  have h2 := hx' x
  have h3 := hx x'
  simp only [smul_eq_mul] at hmid h1
  nlinarith [h1, h2, h3, hmid]

end ConvexReal

/-!
## Georgii, Step 3 of the proof of Lemma (19.24)
-/

section PottsBeta

variable {N : ℕ}

lemma measurable_smul_pottsSq (β : ℝ) : Measurable fun ζ ↦ β * pottsSq N ζ :=
  measurable_pottsSq.const_mul β

lemma smul_pottsSq_bddBelow (β : ℝ) : ∀ ζ, -(|β| * 4) ≤ β * pottsSq N ζ := by
  intro ζ
  have h : |β * pottsSq N ζ| ≤ |β| * 4 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_pottsSq_le ζ) (abs_nonneg β)
  exact (abs_le.1 h).1

lemma smul_pottsSq_bddAbove (β : ℝ) : ∃ c : ℝ, ∀ ζ, |β * pottsSq N ζ| ≤ c := by
  refine ⟨|β| * 4, fun ζ ↦ ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_pottsSq_le ζ) (abs_nonneg β)

lemma smul_pottsSq_bddBelow' (β : ℝ) : ∃ M : ℝ, ∀ ζ, M ≤ β * pottsSq N ζ :=
  ⟨_, smul_pottsSq_bddBelow β⟩

lemma smul_pottsSq_cubeRefl (β : ℝ) (k : Fin 2) (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    β * pottsSq N (cubeRefl (ZMod (N + 2)) k ζ) = β * pottsSq N ζ := by
  rw [pottsSq_cubeRefl]

/-- **Georgii, Proposition (18.12) for the Potts model**: `𝒢₀(βΦ) ≠ ∅`. -/
theorem exists_mem_GZero_potts (β : ℝ) :
    (GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N)).Nonempty :=
  GZero_nonempty (d := 1) (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow β)
    (fun k ζ ↦ smul_pottsSq_cubeRefl β k ζ) (isCubeConfining_univ_of_finite _ _) fun _ ↦ 0

/-- **Georgii's `r₀ ∈ I_{C,λ}(βΦ)`**: the quarter turn of the unit square is a symmetry of the
Potts cube interaction. -/
theorem isSymmetry_planeRot_smul_pottsSq (β : ℝ) :
    (CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).IsSymmetry
      (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) := by
  refine CubeTransformation.IsSymmetry.of_apply_onCube (fun k ζ ↦ smul_pottsSq_cubeRefl β k ζ)
    (fun c ↦ ?_) (fun ζ ↦ ?_)
  · exact MeasurePreserving.id _
  · exact congrArg (fun t ↦ β * t)
      (cubeBondSum_onCube_of_spin_refl _ (fun c ↦ rfl) ζ)

/-- **Georgii, Remark (18.22) for `r₀`**: every `μ ∈ 𝒢₀(βΦ)` is invariant under the rotation. -/
theorem measurePreserving_planeRot_of_mem_GZero (β : ℝ)
    {μ : ProbabilityMeasure ((Fin 2 → ℤ) → ZMod (N + 2))}
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N)) :
    MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun
      (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) μ :=
  (isSymmetry_planeRot_smul_pottsSq β).measurePreserving_onLattice_of_mem_GZero
    (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β) hμ

/-- Every `μ ∈ 𝒢₀(βΦ)` is a shift-invariant Gibbs measure for `βΦ` in the sense of `ℬ_Θ`. -/
theorem mem_invariantG_of_mem_GZero_potts (β : ℝ)
    {μ : ProbabilityMeasure ((Fin 2 → ℤ) → ZMod (N + 2))}
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N)) :
    (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) ∈
      invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
          Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
        (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))) := by
  have hb := smul_pottsSq_bddAbove (N := N) β
  have hφ := measurable_smul_pottsSq (N := N) β
  have hM := smul_pottsSq_bddBelow' (N := N) β
  have h := mem_invariantG_of_isGibbsMeasure_cubeGibbsSpec (ν := pottsNu N) hb hφ hM
    (mem_GP_of_mem_GZero hφ hM hμ) (measurePreserving_shift_of_mem_GZero hφ hμ)
  haveI hpot : Potential.IsPotential (cubePotential (ZMod (N + 2)) fun ζ ↦ β * pottsSq N ζ) :=
    isPotential_cubePotential hφ
  haveI hsum :
      Potential.IsAbsolutelySummable (cubePotential (ZMod (N + 2)) fun ζ ↦ β * pottsSq N ζ) :=
    isAbsolutelySummable_cubePotential hb
  rwa [gibbsSpecificationOfAbsolutelySummable_congr (coe_smul_pottsBTheta (N := N) β)
    (pottsNu N) 1]

/-- **The a priori kernel at a single site reads off the a priori probability of the neighbouring
spin**: `λ_{\{i\}}(σ_i = σ_j | η) = λ(\{η_j\})` for `j ≠ i`.  Intended home:
`GibbsMeasure/Specification/CubePotentialSingleSite.lean`. -/
lemma sigmaFiniteLambdaFun_singleton_setOf_eq {S F : Type*} [MeasurableSpace F]
    [MeasurableSingletonClass F] [Countable F] [DecidableEq S] (ρ : Measure F)
    [IsProbabilityMeasure ρ] (i j : S) (hij : j ≠ i) (η : S → F) :
    Specification.sigmaFiniteLambdaFun (S := S) (E := F) ρ {i} η {σ | σ i = σ j} = ρ {η j} := by
  have hset : MeasurableSet {σ : S → F | σ i = σ j} :=
    measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
  have hset' : MeasurableSet ((fun σ : S → F ↦ σ i) ⁻¹' {η j}) :=
    (measurable_pi_apply i) (measurableSet_singleton _)
  have hjuxt : Measurable (juxt (Λ := ((({i} : Finset S) : Set S))) η) :=
    Measurable.juxt (Λ := ((({i} : Finset S)) : Set S)) (η := η) (𝓔 := ‹MeasurableSpace F›)
  have hj : j ∉ ((({i} : Finset S) : Set S)) := by simpa using hij
  have hpre : (juxt (Λ := ((({i} : Finset S) : Set S))) η) ⁻¹' {σ | σ i = σ j}
      = (juxt (Λ := ((({i} : Finset S) : Set S))) η) ⁻¹' ((fun σ : S → F ↦ σ i) ⁻¹' {η j}) := by
    ext x
    simp [juxt_apply_of_not_mem hj]
  rw [Specification.sigmaFiniteLambdaFun_apply_eq_map, Measure.map_apply hjuxt hset, hpre,
    ← Measure.map_apply hjuxt hset', ← Specification.sigmaFiniteLambdaFun_apply_eq_map]
  exact Specification.sigmaFiniteLambdaFun_singleton_apply_preimage_eval ρ i η
    (measurableSet_singleton _)

lemma pottsNu_singleton (x : ZMod (N + 2)) : pottsNu N {x} = ((N : ℝ≥0∞) + 2)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, ZMod.card]
  push_cast
  rw [one_div]

lemma pottsE1_ne_zero : pottsE1 ≠ (0 : Fin 2 → ℤ) := by
  intro h
  have := congrFun h 0
  simp [intCubeCast] at this

/-- **The one-corner oscillation of the Potts cube interaction** is at most `4β`: `Φ_C` takes
values in `[-4, 0]`. -/
lemma smul_pottsSq_sub_le {β : ℝ} (hβ : 0 ≤ β) (ζ ζ' : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    β * pottsSq N ζ - β * pottsSq N ζ' ≤ 4 * β := by
  have h1 := pottsSq_nonpos (N := N) ζ
  have h2 := neg_four_le_pottsSq (N := N) ζ'
  nlinarith

/-- **The high-temperature bound on the bond probability.**  For a Gibbs measure of `βΦ` with
`β ≥ 0`, the single-site kernel is dominated by the a priori measure with Boltzmann constant
`e^{2^d κ} = e^{16β}` (`cubeGibbsSpec_singleton_apply_le` with the one-corner oscillation
`κ = 4β`), so `μ(σ_0 = σ_{e_1}) ≤ e^{16β}/(N+2)`. -/
theorem measure_setOf_eq_le_of_isGibbsMeasure {β : ℝ} (hβ : 0 ≤ β)
    {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))} [IsProbabilityMeasure μ]
    (hg : Specification.IsGibbsMeasure
      (cubeGibbsSpec (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N)
        (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β)) μ) :
    μ {ω | ω 0 = ω pottsE1} ≤ ENNReal.ofReal (Real.exp (16 * β)) * ((N : ℝ≥0∞) + 2)⁻¹ := by
  classical
  set γ := cubeGibbsSpec (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N)
    (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β) with hγ
  have hA : MeasurableSet {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1} :=
    measurableSet_setOf_eq_apply _ _
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq.1 hg) {0}
  have hμA : μ {ω | ω 0 = ω pottsE1} = ∫⁻ η, γ {0} η {ω | ω 0 = ω pottsE1} ∂μ := by
    conv_lhs => rw [← hbind]
    exact Measure.bind_apply hA
      ((γ {0}).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hbound : ∀ η : (Fin 2 → ℤ) → ZMod (N + 2), γ {0} η {ω | ω 0 = ω pottsE1}
      ≤ ENNReal.ofReal (Real.exp (16 * β)) * ((N : ℝ≥0∞) + 2)⁻¹ := by
    intro η
    have h := cubeGibbsSpec_singleton_apply_le (ν := pottsNu N) (measurable_smul_pottsSq β)
      (smul_pottsSq_bddBelow' β)
      (κ := 4 * β) (fun ζ ζ' c _ ↦ smul_pottsSq_sub_le hβ ζ ζ') (0 : Fin 2 → ℤ) η hA
    rw [sigmaFiniteLambdaFun_singleton_setOf_eq (pottsNu N) (0 : Fin 2 → ℤ) pottsE1
      pottsE1_ne_zero η, pottsNu_singleton] at h
    have hexp : Real.exp ((2 : ℝ) ^ (2 : ℕ) * (4 * β)) = Real.exp (16 * β) := by
      norm_num
      ring
    rw [hexp] at h
    exact h
  rw [hμA]
  calc ∫⁻ η, γ {0} η {ω | ω 0 = ω pottsE1} ∂μ
      ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (16 * β)) * ((N : ℝ≥0∞) + 2)⁻¹ ∂μ :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (Real.exp (16 * β)) * ((N : ℝ≥0∞) + 2)⁻¹ := by
        rw [lintegral_const, measure_univ, mul_one]

/-- **Georgii, Step 3 of the proof of (19.24), first half.**  At the small inverse temperature
`β = 1/64` the single-site estimate gives `μ(σ_0 = σ_{e_1}) ≤ e^{1/4}/(N+2) ≤ 4/9 < 1/2` for every
`μ ∈ 𝒢₀(βΦ)`; Georgii uses `β = 0`, where the value is exactly `1/N`, but a positive `β` is what
makes `β_N > 0`.  The hypothesis `1 ≤ N`, i.e. at least three states, is Georgii's `N > 2`. -/
theorem leftDirDeriv_pottsF_lt_half (hN : 1 ≤ N) :
    leftDirDeriv (pottsF N) ((64 : ℝ)⁻¹) 1 < 1 / 2 := by
  obtain ⟨μ, hμ⟩ := exists_mem_GZero_potts (N := N) ((64 : ℝ)⁻¹)
  have hstep2 := (leftDirDeriv_pottsF_le_le_rightDirDeriv ((64 : ℝ)⁻¹)
    (mem_invariantG_of_mem_GZero_potts _ hμ) (measurePreserving_planeRot_of_mem_GZero _ hμ)).1
  refine lt_of_le_of_lt hstep2 ?_
  have hle : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) {ω | ω 0 = ω pottsE1}
      ≤ ENNReal.ofReal (Real.exp (16 * (64 : ℝ)⁻¹)) * ((N : ℝ≥0∞) + 2)⁻¹ :=
    measure_setOf_eq_le_of_isGibbsMeasure (by norm_num)
      (mem_GP_of_mem_GZero (measurable_smul_pottsSq _) (smul_pottsSq_bddBelow' _) hμ)
  -- `e^{1/4} ≤ 4/3`
  have hexp : Real.exp (16 * (64 : ℝ)⁻¹) ≤ 4 / 3 := by
    have h1 : (3 : ℝ) / 4 ≤ Real.exp (-(16 * (64 : ℝ)⁻¹)) := by
      have := Real.add_one_le_exp (-(16 * (64 : ℝ)⁻¹))
      norm_num at this ⊢
      linarith
    have h2 : Real.exp (16 * (64 : ℝ)⁻¹) * Real.exp (-(16 * (64 : ℝ)⁻¹)) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (16 * (64 : ℝ)⁻¹), Real.exp_pos (-(16 * (64 : ℝ)⁻¹))]
  have hNle : ((N : ℝ) + 2)⁻¹ ≤ 1 / 3 := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) + 2 := by
      have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    rw [one_div]
    exact inv_anti₀ (by norm_num) h3
  have htop : ENNReal.ofReal (Real.exp (16 * (64 : ℝ)⁻¹)) * ((N : ℝ≥0∞) + 2)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  have hcast : (((N : ℝ≥0∞) + 2)⁻¹).toReal = ((N : ℝ) + 2)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp)]
    simp
  rw [hcast] at hreal
  have hpos : (0 : ℝ) < Real.exp (16 * (64 : ℝ)⁻¹) := Real.exp_pos _
  have hinvpos : (0 : ℝ) < ((N : ℝ) + 2)⁻¹ := by positivity
  calc (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real {ω | ω 0 = ω pottsE1}
      ≤ Real.exp (16 * (64 : ℝ)⁻¹) * ((N : ℝ) + 2)⁻¹ := hreal
    _ ≤ (4 / 3) * (1 / 3) := by
        exact mul_le_mul hexp hNle hinvpos.le (by norm_num)
    _ < 1 / 2 := by norm_num

/-- **Georgii's local ground states of (19.21)**: for a small `ε > 0` the local `ε`-ground states
of the Potts cube interaction are constant configurations. -/
theorem exists_pos_localGroundStates_subset_potts :
    ∃ ε > 0, localGroundStates (pottsSq N) (pottsNu N) ε ⊆ ⋃ n, pottsG (N := N) n :=
  exists_pos_localGroundStates_subset_pottsG pottsDelta_lt

/-- A site of `V(G_ε(Φ), ω)` sees a constant elementary cube, so the two spins of any of its
bonds agree. -/
theorem eq_of_mem_latticePattern_localGroundStates {ε : ℝ}
    (hGε : localGroundStates (pottsSq N) (pottsNu N) ε ⊆ ⋃ n, pottsG (N := N) n)
    {ω : (Fin 2 → ℤ) → ZMod (N + 2)}
    (hω : (0 : Fin 2 → ℤ) ∈ latticePattern (ZMod (N + 2))
      (localGroundStates (pottsSq N) (pottsNu N) ε) ω) :
    ω 0 = ω pottsE1 := by
  rw [mem_latticePattern_of_isRSymmetric
    (isRSymmetric_localGroundStates pottsSq_cubeRefl ε)] at hω
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hGε hω)
  have h : latticeCubeView ω 0 = fun _ ↦ n := hn
  have h0 := congrFun h (sqCorner 0 0)
  have h1 := congrFun h (sqCorner 1 0)
  rw [latticeCubeView_apply, zero_add, intCubeCast_sqCorner_zero_zero] at h0
  rw [latticeCubeView_apply, zero_add] at h1
  rw [h0, h1]

/-- **Georgii, Step 3 of the proof of (19.24), second half.**  By (18.10) with `D = {0}` and
Remark (18.9)(4), `μ(σ_0 = σ_{e_1}) ≥ μ(0 ∈ V(G_ε(Φ), ·)) ≥ 1 - t(G_ε(Φ), βΦ) → 1`, so
`∂₊F_Φ(β) > 1/2` for all large `β`. -/
theorem eventually_half_lt_rightDirDeriv_pottsF :
    ∀ᶠ β : ℝ in atTop, 1 / 2 < rightDirDeriv (pottsF N) β 1 := by
  classical
  obtain ⟨ε, hε, hGε⟩ := exists_pos_localGroundStates_subset_potts (N := N)
  have ht := tendsto_patternWeight_smul_atTop (ν := pottsNu N) measurable_pottsSq
    (neg_four_le_pottsSq (N := N)) hε
  filter_upwards [ht.eventually_lt_const (show (0 : ℝ≥0∞) < 1 / 2 by norm_num)] with β hβt
  obtain ⟨μ, hμ⟩ := exists_mem_GZero_potts (N := N) β
  refine lt_of_lt_of_le ?_ (leftDirDeriv_pottsF_le_le_rightDirDeriv β
    (mem_invariantG_of_mem_GZero_potts _ hμ) (measurePreserving_planeRot_of_mem_GZero _ hμ)).2
  set G : Set ((Fin 2 → Fin 2) → ZMod (N + 2)) := localGroundStates (pottsSq N) (pottsNu N) ε
    with hG
  set V : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Fin 2 → ℤ) ∈ latticePattern (ZMod (N + 2)) G ω} with hV
  have hGmeas : MeasurableSet G := measurableSet_localGroundStates measurable_pottsSq ε
  have hVmeas : MeasurableSet V := measurableSet_setOf_mem_latticePattern hGmeas 0
  have hbound : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) Vᶜ
      ≤ patternWeight (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) G := by
    have h := forall_notMem_latticePattern_le_patternWeight (d := 1)
      (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow β)
      (fun k ζ ↦ smul_pottsSq_cubeRefl β k ζ) hGmeas
      (isRSymmetric_localGroundStates pottsSq_cubeRefl ε) hμ {0}
    have hrw : {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ∀ i ∈ ({0} : Finset (Fin 2 → ℤ)),
        i ∉ latticePattern (ZMod (N + 2)) G ω} = Vᶜ := by
      ext ω
      simp [hV]
    rw [hrw] at h
    simpa using h
  have httop : patternWeight (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) G ≠ ⊤ :=
    (hβt.trans_le le_top).ne
  have hVc : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real Vᶜ < 1 / 2 := by
    have h1 := ENNReal.toReal_mono httop hbound
    refine lt_of_le_of_lt h1 ?_
    have := (ENNReal.toReal_lt_toReal httop (by norm_num)).2 hβt
    simpa using this
  have hsub : V ⊆ {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1} := fun ω hω ↦
    eq_of_mem_latticePattern_localGroundStates hGε hω
  have hVreal : (1 : ℝ) / 2 < (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real V := by
    have h := measureReal_add_measureReal_compl (μ := (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))))
      hVmeas
    have huniv : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real Set.univ = 1 := by
      rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv] at h
    linarith
  exact lt_of_lt_of_le hVreal (measureReal_mono hsub)

/-- `F_Φ` is continuous: the pressure is `1`-Lipschitz on `ℬ_Θ` (Proposition (16.1)). -/
lemma continuous_pottsF : Continuous (pottsF N) := by
  have h1 : Continuous fun β : ℝ ↦ β • pottsBTheta N := continuous_id.smul continuous_const
  exact (((Potential.BTheta.lipschitzWith_pressure (pottsNu N)).continuous).comp h1).div_const 4

lemma rightDirDeriv_pottsF_le_leftDirDeriv {x y : ℝ} (h : x < y) :
    rightDirDeriv (pottsF N) x 1 ≤ leftDirDeriv (pottsF N) y 1 := by
  have := convexOn_pottsF (N := N) |>.rightDirDeriv_le_leftDirDeriv_of_lt (0 : ℝ) 1 h
  simpa using this

/-- **Georgii, Lemma (19.24), first assertion**: there is exactly one `β_N` with
`∂₋F_Φ(β_N) ≤ 1/2 ≤ ∂₊F_Φ(β_N)`. -/
theorem existsUnique_pottsBeta (hN : 1 ≤ N) :
    ∃! β : ℝ, leftDirDeriv (pottsF N) β 1 ≤ 1 / 2 ∧ 1 / 2 ≤ rightDirDeriv (pottsF N) β 1 := by
  obtain ⟨b, hb1, hb2⟩ := ((eventually_half_lt_rightDirDeriv_pottsF (N := N)).and
    (eventually_ge_atTop ((64 : ℝ)⁻¹))).exists
  obtain ⟨x, -, hx⟩ := exists_leftDirDeriv_le_le_rightDirDeriv convexOn_pottsF continuous_pottsF
    hb2 (leftDirDeriv_pottsF_lt_half hN) hb1
  refine ⟨x, hx, fun y hy ↦ ?_⟩
  exact eq_of_strictConvexOn_of_forall_le strictConvexOn_pottsF
    ((leftDirDeriv_le_le_rightDirDeriv_iff convexOn_pottsF y (1 / 2)).1 hy)
    ((leftDirDeriv_le_le_rightDirDeriv_iff convexOn_pottsF x (1 / 2)).1 hx)

variable (N) in
/-- **Georgii's threshold `β_N`** of Lemma (19.24). -/
def pottsBeta (hN : 1 ≤ N) : ℝ := (existsUnique_pottsBeta hN).choose

theorem pottsBeta_spec (hN : 1 ≤ N) :
    leftDirDeriv (pottsF N) (pottsBeta N hN) 1 ≤ 1 / 2 ∧
      1 / 2 ≤ rightDirDeriv (pottsF N) (pottsBeta N hN) 1 :=
  (existsUnique_pottsBeta hN).choose_spec.1

theorem pottsBeta_unique (hN : 1 ≤ N) {β : ℝ}
    (hβ : leftDirDeriv (pottsF N) β 1 ≤ 1 / 2 ∧ 1 / 2 ≤ rightDirDeriv (pottsF N) β 1) :
    β = pottsBeta N hN :=
  (existsUnique_pottsBeta hN).choose_spec.2 β hβ

/-- **Georgii, Lemma (19.24)**: `0 < β_N`.  Indeed `∂₋F_Φ(1/64) < 1/2`, so `F_Φ - ·/2` is
strictly decreasing on `(-∞, 1/64]`, and its minimum `β_N` is at least `1/64`. -/
theorem pottsBeta_pos (hN : 1 ≤ N) : 0 < pottsBeta N hN := by
  have hmin := (leftDirDeriv_le_le_rightDirDeriv_iff convexOn_pottsF (pottsBeta N hN) (1 / 2)).1
    (pottsBeta_spec hN)
  by_contra hcon
  have hlt : pottsBeta N hN < (64 : ℝ)⁻¹ := by
    push_neg at hcon
    linarith
  have := lt_sub_of_leftDirDeriv_lt convexOn_pottsF (leftDirDeriv_pottsF_lt_half hN) hlt
  linarith [hmin ((64 : ℝ)⁻¹)]

/-- **Georgii, Lemma (19.24)**: below `β_N` the right derivative of `F_Φ` is `< 1/2`. -/
theorem rightDirDeriv_pottsF_lt_half (hN : 1 ≤ N) {β : ℝ} (hβ : β < pottsBeta N hN) :
    rightDirDeriv (pottsF N) β 1 < 1 / 2 := by
  by_contra hcon
  push_neg at hcon
  have h1 : rightDirDeriv (pottsF N) β 1 ≤ 1 / 2 :=
    (rightDirDeriv_pottsF_le_leftDirDeriv hβ).trans (pottsBeta_spec hN).1
  have h2 : leftDirDeriv (pottsF N) β 1 ≤ 1 / 2 :=
    (ConvexOn.leftDirDeriv_le_rightDirDeriv convexOn_pottsF β 1).trans h1
  exact absurd (pottsBeta_unique hN ⟨h2, hcon⟩) hβ.ne

/-- **Georgii, Lemma (19.24)**: above `β_N` the left derivative of `F_Φ` is `> 1/2`. -/
theorem half_lt_leftDirDeriv_pottsF (hN : 1 ≤ N) {β : ℝ} (hβ : pottsBeta N hN < β) :
    1 / 2 < leftDirDeriv (pottsF N) β 1 := by
  by_contra hcon
  push_neg at hcon
  have h1 : 1 / 2 ≤ leftDirDeriv (pottsF N) β 1 :=
    (pottsBeta_spec hN).2.trans (rightDirDeriv_pottsF_le_leftDirDeriv hβ)
  have h2 : 1 / 2 ≤ rightDirDeriv (pottsF N) β 1 :=
    h1.trans (ConvexOn.leftDirDeriv_le_rightDirDeriv convexOn_pottsF β 1)
  exact absurd (pottsBeta_unique hN ⟨hcon, h2⟩) hβ.ne'

/-- **Georgii, Lemma (19.24), second assertion**: if `0 ≤ β < β_N` then `μ(σ_i = σ_j) < 1/2` for
every `r₀`-invariant `μ ∈ 𝒢_Θ(βΦ)` and every nearest-neighbour pair `i, j`. -/
theorem measureReal_setOf_eq_lt_half (hN : 1 ≤ N) {β : ℝ} (hβ : β < pottsBeta N hN)
    {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))} [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
      (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))))
    (hr : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun μ μ) :
    μ.real {ω | ω 0 = ω pottsE1} < 1 / 2 :=
  lt_of_le_of_lt (leftDirDeriv_pottsF_le_le_rightDirDeriv β hμ hr).2
    (rightDirDeriv_pottsF_lt_half hN hβ)

/-- **Georgii, Lemma (19.24), third assertion**: if `β > β_N` then `μ(σ_i = σ_j) > 1/2` for every
`r₀`-invariant `μ ∈ 𝒢_Θ(βΦ)` and every nearest-neighbour pair `i, j`. -/
theorem half_lt_measureReal_setOf_eq (hN : 1 ≤ N) {β : ℝ} (hβ : pottsBeta N hN < β)
    {μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))} [IsProbabilityMeasure μ]
    (hμ : μ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
      (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))))
    (hr : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun μ μ) :
    1 / 2 < μ.real {ω | ω 0 = ω pottsE1} :=
  lt_of_lt_of_le (half_lt_leftDirDeriv_pottsF hN hβ)
    (leftDirDeriv_pottsF_le_le_rightDirDeriv β hμ hr).1

end PottsBeta

/-!
## Georgii, Step 1 of the proof of Lemma (19.25): the seven excitation classes

Georgii's excitation pattern of a configuration `ω` of the unit square is the quadruple
`π(ω) = (δ(ω_{00}, ω_{10}), δ(ω_{10}, ω_{11}), δ(ω_{11}, ω_{01}), δ(ω_{01}, ω_{00}))`
of Kronecker symbols of its four bonds, read cyclically.  The local ground states `G` are
`π = (1,1,1,1)`, the local ceiling states `G_0` are `π = (0,0,0,0)`, and `Ḡ = G ∪ G_0`.  Patterns
with exactly three ones are impossible, so `E^C ∖ Ḡ` splits into the seven classes `M_1, …, M_7`.
-/

section Classes

variable {N : ℕ}

/-- The bottom bond `\{(0,0), (1,0)\}` of the unit square carries equal spins. -/
abbrev pottsBotEq (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : Prop :=
  ζ (sqCorner 0 0) = ζ (sqCorner 1 0)

/-- The right bond `\{(1,0), (1,1)\}` of the unit square carries equal spins. -/
abbrev pottsRightEq (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : Prop :=
  ζ (sqCorner 1 0) = ζ (sqCorner 1 1)

/-- The top bond `\{(0,1), (1,1)\}` of the unit square carries equal spins. -/
abbrev pottsTopEq (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : Prop :=
  ζ (sqCorner 0 1) = ζ (sqCorner 1 1)

/-- The left bond `\{(0,0), (0,1)\}` of the unit square carries equal spins. -/
abbrev pottsLeftEq (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) : Prop :=
  ζ (sqCorner 0 0) = ζ (sqCorner 0 1)

/-- **Georgii's `Φ_C` in terms of the excitation pattern**: `Φ_C = -(number of equal bonds)`. -/
lemma pottsSq_eq_neg_card (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    pottsSq N ζ = -((if pottsBotEq ζ then (1 : ℝ) else 0) + (if pottsTopEq ζ then 1 else 0)
      + (if pottsLeftEq ζ then 1 else 0) + (if pottsRightEq ζ then 1 else 0)) := by
  rw [pottsSq_apply, pottsDelta_sub, pottsDelta_sub, pottsDelta_sub, pottsDelta_sub]
  split_ifs <;> ring

/-- The energy of a configuration of the unit square from the values of its four bond
indicators. -/
lemma pottsSq_eq_neg_sum {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} {b t l r : ℝ}
    (hb : (if pottsBotEq ζ then (1 : ℝ) else 0) = b)
    (ht : (if pottsTopEq ζ then (1 : ℝ) else 0) = t)
    (hl : (if pottsLeftEq ζ then (1 : ℝ) else 0) = l)
    (hr : (if pottsRightEq ζ then (1 : ℝ) else 0) = r) :
    pottsSq N ζ = -(b + t + l + r) := by
  rw [pottsSq_eq_neg_card, hb, ht, hl, hr]

/-! ### Georgii, "excitation patterns with three one's are impossible" -/

lemma pottsLeftEq_of_three {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} (h1 : pottsBotEq ζ)
    (h2 : pottsRightEq ζ) (h3 : pottsTopEq ζ) : pottsLeftEq ζ :=
  h1.trans (h2.trans h3.symm)

lemma pottsBotEq_of_three {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} (h2 : pottsRightEq ζ)
    (h3 : pottsTopEq ζ) (h4 : pottsLeftEq ζ) : pottsBotEq ζ :=
  h4.trans (h3.trans h2.symm)

lemma pottsRightEq_of_three {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} (h1 : pottsBotEq ζ)
    (h3 : pottsTopEq ζ) (h4 : pottsLeftEq ζ) : pottsRightEq ζ :=
  h1.symm.trans (h4.trans h3)

lemma pottsTopEq_of_three {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} (h1 : pottsBotEq ζ)
    (h2 : pottsRightEq ζ) (h4 : pottsLeftEq ζ) : pottsTopEq ζ :=
  h4.symm.trans (h1.trans h2)

/-! ### `G`, `G_0` and `Ḡ` -/

variable (N) in
/-- **Georgii's `G = G_1 ∪ ⋯ ∪ G_N`**: the local ground states of the Potts cube interaction, the
constant configurations `(nn/nn)`. -/
def pottsGround : Set ((Fin 2 → Fin 2) → ZMod (N + 2)) := ⋃ n, pottsG (N := N) n

variable (N) in
/-- **Georgii's `G_0`**: the local ceiling states, the configurations all of whose four bonds are
excited. -/
def pottsCeiling : Set ((Fin 2 → Fin 2) → ZMod (N + 2)) :=
  {ζ | ¬ pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ}

variable (N) in
/-- **Georgii's `Ḡ = G_0 ∪ G`**. -/
def pottsGBar : Set ((Fin 2 → Fin 2) → ZMod (N + 2)) := pottsCeiling N ∪ pottsGround N

lemma mem_pottsGround_iff (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) :
    ζ ∈ pottsGround N ↔ pottsBotEq ζ ∧ pottsRightEq ζ ∧ pottsTopEq ζ ∧ pottsLeftEq ζ := by
  constructor
  · rintro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    have hz : ζ = fun _ ↦ n := hn
    subst hz
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, -, h4⟩
    exact Set.mem_iUnion.2 ⟨ζ (sqCorner 0 0),
      Set.mem_singleton_iff.2 (funext_sqCorner rfl h1.symm h4.symm (h2.symm.trans h1.symm))⟩

/-! ### Georgii's seven classes `M_1, …, M_7` -/

variable (N) in
/-- **Georgii's classes `M_1, …, M_7`** of configurations of the unit square with a prescribed
excitation pattern.  In the cyclic order (bottom, right, top, left) of (19.25),
`M_1 = \{π = (1,0,0,0)\}` and `M_2, M_3, M_4` are its rotations; `M_5 = \{π = (1,1,0,0)` or
`(0,1,1,0)\}`, `M_6 = r_0^2 M_5`, and `M_7 = \{π = (1,0,1,0)` or `(0,1,0,1)\}`.  The index here is
`Fin 7`, i.e. Georgii's `k - 1`. -/
def pottsM : Fin 7 → Set ((Fin 2 → Fin 2) → ZMod (N + 2))
  | 0 => {ζ | pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ}
  | 1 => {ζ | ¬ pottsBotEq ζ ∧ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ}
  | 2 => {ζ | ¬ pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ}
  | 3 => {ζ | ¬ pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ pottsLeftEq ζ}
  | 4 => {ζ | (pottsBotEq ζ ∧ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ) ∨
      (¬ pottsBotEq ζ ∧ pottsRightEq ζ ∧ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ)}
  | 5 => {ζ | (¬ pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ pottsTopEq ζ ∧ pottsLeftEq ζ) ∨
      (pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ pottsLeftEq ζ)}
  | 6 => {ζ | (pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ) ∨
      (¬ pottsBotEq ζ ∧ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ pottsLeftEq ζ)}

/-- **Georgii, Step 1 of the proof of (19.25)**: the seven classes cover `E^C ∖ Ḡ`.  The only
excitation patterns which do not occur are those with exactly three equal bonds. -/
theorem exists_mem_pottsM {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)} (hζ : ζ ∉ pottsGBar N) :
    ∃ k : Fin 7, ζ ∈ pottsM N k := by
  classical
  have hG : ¬ (pottsBotEq ζ ∧ pottsRightEq ζ ∧ pottsTopEq ζ ∧ pottsLeftEq ζ) := fun h ↦
    hζ (Or.inr ((mem_pottsGround_iff ζ).2 h))
  have hC : ¬ (¬ pottsBotEq ζ ∧ ¬ pottsRightEq ζ ∧ ¬ pottsTopEq ζ ∧ ¬ pottsLeftEq ζ) := fun h ↦
    hζ (Or.inl h)
  by_cases h1 : pottsBotEq ζ <;> by_cases h2 : pottsRightEq ζ <;>
    by_cases h3 : pottsTopEq ζ <;> by_cases h4 : pottsLeftEq ζ
  · exact absurd ⟨h1, h2, h3, h4⟩ hG
  · exact absurd (pottsLeftEq_of_three h1 h2 h3) h4
  · exact absurd (pottsTopEq_of_three h1 h2 h4) h3
  · exact ⟨4, Or.inl ⟨h1, h2, h3, h4⟩⟩
  · exact absurd (pottsRightEq_of_three h1 h3 h4) h2
  · exact ⟨6, Or.inl ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨5, Or.inr ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨0, ⟨h1, h2, h3, h4⟩⟩
  · exact absurd (pottsBotEq_of_three h2 h3 h4) h1
  · exact ⟨4, Or.inr ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨6, Or.inr ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨1, ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨5, Or.inl ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨2, ⟨h1, h2, h3, h4⟩⟩
  · exact ⟨3, ⟨h1, h2, h3, h4⟩⟩
  · exact absurd ⟨h1, h2, h3, h4⟩ hC

/-- **Georgii, Step 1**: `Φ_C = -1` on `M_1, …, M_4` and `Φ_C = -2` on `M_5, M_6, M_7`. -/
theorem pottsSq_of_mem_pottsM {k : Fin 7} {ζ : (Fin 2 → Fin 2) → ZMod (N + 2)}
    (hζ : ζ ∈ pottsM N k) : pottsSq N ζ = if (k : ℕ) < 4 then -1 else -2 := by
  fin_cases k
  · obtain ⟨h1, h2, h3, h4⟩ := hζ
    rw [pottsSq_eq_neg_sum (if_pos h1) (if_neg h3) (if_neg h4) (if_neg h2)]
    norm_num
  · obtain ⟨h1, h2, h3, h4⟩ := hζ
    rw [pottsSq_eq_neg_sum (if_neg h1) (if_neg h3) (if_neg h4) (if_pos h2)]
    norm_num
  · obtain ⟨h1, h2, h3, h4⟩ := hζ
    rw [pottsSq_eq_neg_sum (if_neg h1) (if_pos h3) (if_neg h4) (if_neg h2)]
    norm_num
  · obtain ⟨h1, h2, h3, h4⟩ := hζ
    rw [pottsSq_eq_neg_sum (if_neg h1) (if_neg h3) (if_pos h4) (if_neg h2)]
    norm_num
  · rcases hζ with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [pottsSq_eq_neg_sum (if_pos h1) (if_neg h3) (if_neg h4) (if_pos h2)]
      norm_num
    · rw [pottsSq_eq_neg_sum (if_neg h1) (if_pos h3) (if_neg h4) (if_pos h2)]
      norm_num
  · rcases hζ with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [pottsSq_eq_neg_sum (if_neg h1) (if_pos h3) (if_pos h4) (if_neg h2)]
      norm_num
    · rw [pottsSq_eq_neg_sum (if_pos h1) (if_neg h3) (if_pos h4) (if_neg h2)]
      norm_num
  · rcases hζ with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · rw [pottsSq_eq_neg_sum (if_pos h1) (if_pos h3) (if_neg h4) (if_neg h2)]
      norm_num
    · rw [pottsSq_eq_neg_sum (if_neg h1) (if_neg h3) (if_pos h4) (if_pos h2)]
      norm_num

end Classes

/-!
## Georgii, Step 2 of the proof of Lemma (19.25): the chessboard estimate for a family of classes

Georgii applies Corollary (17.17) to the family `f_i = 1_{M_{φ(i)}}`, `i ∈ D`, `f_i = 1`
otherwise.  Because the classes differ from site to site, the right-hand side of the chessboard
estimate is a *product* of the seven "all cubes in `M_k`" probabilities `°γ_Λ^Φ(A_k)` rather than
a power of a single one.  The lemmas below are general — they say nothing about the Potts model —
and their intended home is `GibbsMeasure/Specification/PatternPercolation.lean` and
`GibbsMeasure/Specification/PeriodicGibbsLimits.lean`.
-/

section ChessboardFamily

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ι : Type*}
  {φ : ((Fin (d + 1) → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]

section Torus

variable {N : ℕ} [NeZero N]

omit [MeasurableSpace E] in
/-- The product of the indicators of a *family* of patterns over a finite set of cubes is the
indicator of the event that every cube shows its own pattern. -/
lemma prod_cubeInd_cubeView_family (W : ι → Set ((Fin (d + 1) → Fin 2) → E))
    (ψ : (Fin (d + 1) → ZMod (2 * N)) → ι) (s : Finset (Fin (d + 1) → ZMod (2 * N)))
    (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    ∏ i ∈ s, cubeInd (W (ψ i)) (cubeView ω i)
      = Set.indicator {ω' | ∀ i ∈ s, cubeView ω' i ∈ W (ψ i)} (fun _ ↦ (1 : ℝ)) ω := by
  classical
  by_cases h : ∀ i ∈ s, cubeView ω i ∈ W (ψ i)
  · rw [Set.indicator_of_mem (show ω ∈ {ω' | ∀ i ∈ s, cubeView ω' i ∈ W (ψ i)} from h)]
    exact Finset.prod_eq_one fun i hi ↦ by rw [cubeInd_apply, if_pos (h i hi)]
  · rw [Set.indicator_of_notMem (show ω ∉ {ω' | ∀ i ∈ s, cubeView ω' i ∈ W (ψ i)} from h)]
    push_neg at h
    obtain ⟨i, hi, hnot⟩ := h
    exact Finset.prod_eq_zero hi (by rw [cubeInd_apply, if_neg hnot])

lemma measurableSet_forall_cubeView_mem_family {W : ι → Set ((Fin (d + 1) → Fin 2) → E)}
    (hW : ∀ k, MeasurableSet (W k)) (ψ : (Fin (d + 1) → ZMod (2 * N)) → ι)
    (s : Finset (Fin (d + 1) → ZMod (2 * N))) :
    MeasurableSet {ω : (Fin (d + 1) → ZMod (2 * N)) → E | ∀ i ∈ s, cubeView ω i ∈ W (ψ i)} := by
  have hrw : {ω : (Fin (d + 1) → ZMod (2 * N)) → E | ∀ i ∈ s, cubeView ω i ∈ W (ψ i)}
      = ⋂ i ∈ s, (fun ω ↦ cubeView ω i) ⁻¹' W (ψ i) := by ext ω; simp
  rw [hrw]
  exact MeasurableSet.biInter s.countable_toSet fun i _ ↦
    (hW (ψ i)).preimage ((measurable_pi_apply i).comp measurable_cubeView)

/-- **Georgii's event `A_k(n)`** as an indicator product: every elementary cube of the torus,
read through the reflection `r^i`, shows the pattern `B`. -/
lemma prod_cubeInd_tauPow_cubeView (B : Set ((Fin (d + 1) → Fin 2) → E))
    (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    ∏ i, cubeInd B (tauPow (cubeRefl E) i (cubeView ω i))
      = Set.indicator {ω' | ∀ i, tauPow (cubeRefl E) i (cubeView ω' i) ∈ B}
        (fun _ ↦ (1 : ℝ)) ω := by
  classical
  by_cases h : ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ B
  · rw [Set.indicator_of_mem
      (show ω ∈ {ω' | ∀ i, tauPow (cubeRefl E) i (cubeView ω' i) ∈ B} from h)]
    exact Finset.prod_eq_one fun i _ ↦ by rw [cubeInd_apply, if_pos (h i)]
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω' | ∀ i, tauPow (cubeRefl E) i (cubeView ω' i) ∈ B} from h)]
    push_neg at h
    obtain ⟨i, hnot⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cubeInd_apply, if_neg hnot])

lemma measurableSet_forall_tauPow_cubeView_mem {B : Set ((Fin (d + 1) → Fin 2) → E)}
    (hB : MeasurableSet B) :
    MeasurableSet {ω : (Fin (d + 1) → ZMod (2 * N)) → E |
      ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ B} := by
  have hrw : {ω : (Fin (d + 1) → ZMod (2 * N)) → E |
        ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ B}
      = ⋂ i, (fun ω ↦ tauPow (cubeRefl E) i (cubeView ω i)) ⁻¹' B := by ext ω; simp
  rw [hrw]
  exact MeasurableSet.iInter fun i ↦
    hB.preimage ((measurable_tauPow (cubeRefl E) i).comp
      ((measurable_pi_apply i).comp measurable_cubeView))

/-- **Georgii, Step 2 of the proof of (19.25)**: Corollary (17.17) applied to `°γ_Λ^Φ` with the
family `f_i = 1_{M_{φ(i)}}` for `i ∈ D` and `f_i = 1` otherwise.  The right-hand side is the
product over `j ∈ D` of the probabilities of Georgii's events `A_{φ(j)}`. -/
theorem periodicGibbsDist_pow_le_prod (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    {W : ι → Set ((Fin (d + 1) → Fin 2) → E)} (hW : ∀ k, MeasurableSet (W k))
    (D : Finset (Fin (d + 1) → ZMod (2 * N))) (ψ : (Fin (d + 1) → ZMod (2 * N)) → ι) :
    periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ W (ψ i)}
        ^ ((2 * N) ^ (d + 1))
      ≤ ∏ j ∈ D, periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W (ψ j)} := by
  classical
  have hprob := isProbabilityMeasure_periodicGibbsDist (N := N) (d := d + 1) (ν := ν)
    (IsProbabilityMeasure.ne_zero ν) hφ hM
  set f : (Fin (d + 1) → ZMod (2 * N)) → ((Fin (d + 1) → Fin 2) → E) → ℝ :=
    fun i ↦ if i ∈ D then cubeInd (W (ψ i)) else fun _ ↦ 1 with hf
  have hfD : ∀ i ∈ D, f i = cubeInd (W (ψ i)) := fun i hi ↦ by rw [hf]; simp [hi]
  have hfout : ∀ i ∉ D, f i = fun _ ↦ 1 := fun i hi ↦ by rw [hf]; simp [hi]
  have hfm : ∀ i, Measurable (f i) := by
    intro i
    by_cases hi : i ∈ D
    · rw [hfD i hi]; exact measurable_cubeInd (hW (ψ i))
    · rw [hfout i hi]; exact measurable_const
  have hfC : ∀ i ζ, |f i ζ| ≤ 1 := by
    intro i ζ
    by_cases hi : i ∈ D
    · rw [hfD i hi]; exact abs_cubeInd_le_one _ ζ
    · rw [hfout i hi]; simp
  have hcb := abs_integral_prod_cubeView_pow_le_periodicGibbsDist (N := N) (d := d)
    (IsProbabilityMeasure.ne_zero ν) hφ hM hφk hfm hfC
  have hL : ∫ ω, ∏ i, f i (cubeView ω i) ∂(periodicGibbsDist E φ ν (N := N))
      = (periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ W (ψ i)}).toReal := by
    have hprodeq : (fun ω : (Fin (d + 1) → ZMod (2 * N)) → E ↦ ∏ i, f i (cubeView ω i))
        = Set.indicator {ω | ∀ i ∈ D, cubeView ω i ∈ W (ψ i)} (fun _ ↦ (1 : ℝ)) := by
      funext ω
      rw [← prod_cubeInd_cubeView_family W ψ D ω,
        ← Finset.prod_subset (Finset.subset_univ D) (fun i _ hi ↦ by rw [hfout i hi])]
      exact Finset.prod_congr rfl fun i hi ↦ by rw [hfD i hi]
    rw [hprodeq, integral_indicator_one_eq _ (measurableSet_forall_cubeView_mem_family hW ψ D)]
  have hR : ∏ j, (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
        ∂(periodicGibbsDist E φ ν (N := N)))
      = ∏ j ∈ D, (periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W (ψ j)}).toReal := by
    have hout : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1) → ZMod (2 * N))), j ∉ D →
        (∫ ω, ∏ i, f j (tauPow (cubeRefl E) i (cubeView ω i))
          ∂(periodicGibbsDist E φ ν (N := N))) = 1 := by
      intro j _ hj
      rw [hfout j hj]
      simp
    rw [← Finset.prod_subset (Finset.subset_univ D) hout]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [hfD j hj]
    simp only [prod_cubeInd_tauPow_cubeView (W (ψ j))]
    exact integral_indicator_one_eq _ (measurableSet_forall_tauPow_cubeView_mem (hW (ψ j)))
  rw [hL, hR, abs_of_nonneg ENNReal.toReal_nonneg] at hcb
  refine (ENNReal.toReal_le_toReal (ENNReal.pow_ne_top (measure_ne_top _ _))
    (by exact ENNReal.prod_ne_top fun j _ ↦ measure_ne_top _ _)).1 ?_
  rw [ENNReal.toReal_pow, ENNReal.toReal_prod]
  exact hcb

/-- **Georgii, Step 2 of the proof of (19.25) on the torus**: if each of the events `A_k` has
`°γ_Λ^Φ`-probability at most `c^{|Λ|}`, then the event that each cube based in `D` shows its own
prescribed pattern has probability at most `c^{|D|}`. -/
theorem periodicGibbsDist_forall_mem_le_pow (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    {W : ι → Set ((Fin (d + 1) → Fin 2) → E)} (hW : ∀ k, MeasurableSet (W k))
    (D : Finset (Fin (d + 1) → ZMod (2 * N))) (ψ : (Fin (d + 1) → ZMod (2 * N)) → ι) {c : ℝ≥0∞}
    (hc : ∀ k, periodicGibbsDist E φ ν (N := N)
      {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W k} ≤ c ^ ((2 * N) ^ (d + 1))) :
    periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ W (ψ i)} ≤ c ^ D.card := by
  have hn : (2 * N) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by have := NeZero.ne N; omega)
  refine ENNReal.le_of_pow_le_pow_left' hn ?_
  calc periodicGibbsDist E φ ν (N := N) {ω | ∀ i ∈ D, cubeView ω i ∈ W (ψ i)}
        ^ ((2 * N) ^ (d + 1))
      ≤ ∏ j ∈ D, periodicGibbsDist E φ ν (N := N)
          {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W (ψ j)} :=
        periodicGibbsDist_pow_le_prod hφ hM hφk hW D ψ
    _ ≤ ∏ _j ∈ D, c ^ ((2 * N) ^ (d + 1)) := Finset.prod_le_prod fun j _ ↦ hc (ψ j)
    _ = (c ^ D.card) ^ ((2 * N) ^ (d + 1)) := by
        rw [Finset.prod_const, ← pow_mul, ← pow_mul, mul_comm]

end Torus

/-! ### From the torus to `ℤ^d` -/

section LatticeTransfer

variable {W : ι → Set ((Fin (d + 1) → Fin 2) → E)}

lemma torusToLattice_latticeToTorus_of_mem {n : ℕ} {i : Fin (d + 1) → ℤ}
    (hi : i ∈ periodicCube (d + 1) n) : torusToLattice n (latticeToTorus n i) = i :=
  latticeToTorus_injOn_latticeBox (torusToLattice_mem _) (Finset.mem_coe.2 hi)
    (latticeToTorus_torusToLattice _)

omit [MeasurableSpace E] in
lemma latticeCubeView_periodicPullback {n : ℕ} (ζ : (Fin (d + 1) → ZMod (2 * (n + 1))) → E)
    (i : Fin (d + 1) → ℤ) :
    latticeCubeView (periodicPullback n ζ) i = cubeView ζ (latticeToTorus n i) := by
  funext c
  simp [latticeCubeView, cubeView, latticeToTorus_add]

/-- **The event that each cube based in `D` shows its own pattern is a local event.** -/
lemma measurableSet_cylinderEvents_forall_mem_latticeCubeView (hW : ∀ k, MeasurableSet (W k))
    {Δ : Set (Fin (d + 1) → ℤ)} (D : Finset (Fin (d + 1) → ℤ)) (ψ : (Fin (d + 1) → ℤ) → ι)
    (h : ∀ i ∈ D, ∀ c, i + intCubeCast c ∈ Δ) :
    MeasurableSet[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ E) Δ]
      {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)} := by
  classical
  set B : Set (↥(D : Finset (Fin (d + 1) → ℤ)) → ((Fin (d + 1) → Fin 2) → E)) :=
    {x | ∀ i : ↥(D : Finset (Fin (d + 1) → ℤ)), x i ∈ W (ψ i.1)} with hB
  have hBmeas : MeasurableSet B := by
    have hBi : B = ⋂ i : ↥(D : Finset (Fin (d + 1) → ℤ)),
        ((fun x : ↥(D : Finset (Fin (d + 1) → ℤ)) → ((Fin (d + 1) → Fin 2) → E) ↦ x i) ⁻¹'
          W (ψ i.1)) := by
      ext x; simp [hB]
    rw [hBi]
    exact MeasurableSet.iInter fun i ↦ (measurable_pi_apply i) (hW (ψ i.1))
  have hmap : Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ℤ ↦ E) Δ]
      fun ω : (Fin (d + 1) → ℤ) → E ↦
        (fun i : ↥(D : Finset (Fin (d + 1) → ℤ)) ↦ latticeCubeView ω i.1) := by
    refine Measurable.cylinderEvents_of_dependsOn ?_ ?_
    · exact Measurable.of_eval fun _ ↦
        Measurable.of_eval fun _ ↦ measurable_pi_apply _
    · intro x y hxy
      funext i c
      exact hxy _ (h i.1 i.2 c)
  have hEq : {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)}
      = (fun ω : (Fin (d + 1) → ℤ) → E ↦
          (fun i : ↥(D : Finset (Fin (d + 1) → ℤ)) ↦ latticeCubeView ω i.1)) ⁻¹' B := by
    ext ω
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨fun hh i ↦ hh i.1 i.2, fun hh i hi ↦ hh ⟨i, hi⟩⟩
  rw [hEq]
  exact hmap hBmeas

lemma forall_mem_latticeCubeView_mem_localEvents (hW : ∀ k, MeasurableSet (W k))
    (D : Finset (Fin (d + 1) → ℤ)) (ψ : (Fin (d + 1) → ℤ) → ι) :
    {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)}
      ∈ localEvents (Fin (d + 1) → ℤ) E :=
  mem_localEvents_of_cylinderEvents (cubeSupport D)
    (measurableSet_cylinderEvents_forall_mem_latticeCubeView hW D ψ
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))

/-- **Georgii, Step 2 for the `2N`-periodic field on `ℤ^d`.** -/
theorem periodicGibbsPeriodicField_forall_mem_le_pow (hφ : Measurable φ) {M : ℝ}
    (hM : ∀ ζ, M ≤ φ ζ) (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ)
    (hW : ∀ k, MeasurableSet (W k)) {n : ℕ} {D : Finset (Fin (d + 1) → ℤ)}
    (hD : D ⊆ periodicCube (d + 1) n) (ψ : (Fin (d + 1) → ℤ) → ι) {c : ℝ≥0∞}
    (hc : ∀ k, periodicGibbsDist E φ ν (N := n + 1)
      {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W k} ≤ c ^ ((2 * (n + 1)) ^ (d + 1))) :
    periodicGibbsPeriodicField E φ ν n {ω | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)}
      ≤ c ^ D.card := by
  classical
  set D' : Finset (Fin (d + 1) → ZMod (2 * (n + 1))) := D.image (latticeToTorus n) with hD'def
  have hcard : D'.card = D.card :=
    Finset.card_image_of_injOn fun i hi j hj hij ↦
      latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 (hD hi)) (Finset.mem_coe.2 (hD hj)) hij
  have hAm : MeasurableSet {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)} :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_forall_mem_latticeCubeView hW D ψ
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c))
  have hpre : periodicPullback (E := E) n ⁻¹'
      {ω : (Fin (d + 1) → ℤ) → E | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)}
      = {ζ | ∀ j ∈ D', cubeView ζ j ∈ W (ψ (torusToLattice n j))} := by
    ext ζ
    constructor
    · intro hh j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      rw [torusToLattice_latticeToTorus_of_mem (hD hi), ← latticeCubeView_periodicPullback ζ i]
      exact hh i hi
    · intro hh i hi
      have hj : latticeToTorus n i ∈ D' := Finset.mem_image.2 ⟨i, hi, rfl⟩
      have := hh _ hj
      rw [torusToLattice_latticeToTorus_of_mem (hD hi)] at this
      rw [latticeCubeView_periodicPullback ζ i]
      exact this
  rw [periodicGibbsPeriodicField,
    Measure.map_apply (measurable_periodicPullback (E := E) (d := d + 1) (n := n)) hAm, hpre,
    ← hcard]
  exact periodicGibbsDist_forall_mem_le_pow hφ hM hφk hW D' _ hc

/-- **Georgii, Step 2 for `°γ_{Λ(N)}^Φ × δ_ω`.** -/
theorem periodicGibbsField_forall_mem_le_pow (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ) (hW : ∀ k, MeasurableSet (W k))
    {n : ℕ} {D : Finset (Fin (d + 1) → ℤ)} (hn : D ∪ cubeSupport D ⊆ periodicCube (d + 1) n)
    (ψ : (Fin (d + 1) → ℤ) → ι) {c : ℝ≥0∞}
    (hc : ∀ k, periodicGibbsDist E φ ν (N := n + 1)
      {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W k} ≤ c ^ ((2 * (n + 1)) ^ (d + 1)))
    (ω : (Fin (d + 1) → ℤ) → E) :
    periodicGibbsField E φ ν n ω {ω' | ∀ i ∈ D, latticeCubeView ω' i ∈ W (ψ i)}
      ≤ c ^ D.card := by
  have hDsub : D ⊆ periodicCube (d + 1) n :=
    Finset.Subset.trans Finset.subset_union_left hn
  have hSsub : (cubeSupport D : Set (Fin (d + 1) → ℤ))
      ⊆ (periodicCube (d + 1) n : Set (Fin (d + 1) → ℤ)) := by
    exact_mod_cast Finset.Subset.trans Finset.subset_union_right hn
  rw [periodicGibbsField_apply_of_cylinderEvents n ω ((cylinderEvents_mono hSsub) _
    (measurableSet_cylinderEvents_forall_mem_latticeCubeView hW D ψ
      fun _ hi c ↦ Finset.mem_coe.2 (mem_cubeSupport hi c)))]
  exact periodicGibbsPeriodicField_forall_mem_le_pow hφ hM hφk hW hDsub ψ hc

/-- **Georgii, Step 2 of the proof of Lemma (19.25)**: for `μ ∈ 𝒢₀(Φ)`, a finite family `(W_k)`
of measurable patterns and a prescription `ψ` of one pattern per site,

`μ(σ_{C+i} ∈ W_{ψ(i)} for all i ∈ D) ≤ c^{|D|}`,

whenever `°γ_{Λ(n)}^Φ(A_k) ≤ c^{|Λ(n)|}` for every `k`, eventually in `n`. -/
theorem forall_mem_latticeCubeView_le_pow (hφ : Measurable φ) {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hφk : ∀ (k : Fin (d + 1)) ζ, φ (cubeRefl E k ζ) = φ ζ) (hW : ∀ k, MeasurableSet (W k))
    {μ : ProbabilityMeasure ((Fin (d + 1) → ℤ) → E)} (hμ : μ ∈ GZero E φ ν)
    (D : Finset (Fin (d + 1) → ℤ)) (ψ : (Fin (d + 1) → ℤ) → ι) {c : ℝ≥0∞}
    (hc : ∀ᶠ n : ℕ in atTop, ∀ k, periodicGibbsDist E φ ν (N := n + 1)
      {ω | ∀ i, tauPow (cubeRefl E) i (cubeView ω i) ∈ W k} ≤ c ^ ((2 * (n + 1)) ^ (d + 1))) :
    (μ : Measure ((Fin (d + 1) → ℤ) → E))
        {ω | ∀ i ∈ D, latticeCubeView ω i ∈ W (ψ i)} ≤ c ^ D.card := by
  classical
  obtain ⟨μs, hμs, hcp⟩ := hμ
  refine eval_le_of_mapClusterPt (forall_mem_latticeCubeView_mem_localEvents hW D ψ) hcp ?_
  filter_upwards [hc, Potential.tendsto_latticeBox_atTop.eventually
    (eventually_ge_atTop (D ∪ cubeSupport D))] with n hcn hn
  obtain ⟨ω, hω⟩ := hμs n
  rw [hω]
  exact periodicGibbsField_forall_mem_le_pow hφ hM hφk hW hn ψ hcn ω

end LatticeTransfer

end ChessboardFamily

/-!
## Georgii, Lemma (19.25): the estimate `μ(D ∩ V(Ḡ, ·) = ∅) ≤ t_N^{|D|}`

Steps 1 and 2 of Georgii's proof.  The remaining input — Steps 3 to 5, the counting estimates
`t_{N,k} ≤ N^{-1/4}` for the seven classes — enters as the hypothesis `hc` below.
-/

section Lemma1925

variable {N : ℕ}

lemma measurableSet_pottsCeiling : MeasurableSet (pottsCeiling N) := by
  classical
  exact MeasurableSet.of_discrete

lemma measurableSet_pottsGround : MeasurableSet (pottsGround N) :=
  MeasurableSet.iUnion fun n ↦ measurableSet_pottsG n

lemma measurableSet_pottsGBar : MeasurableSet (pottsGBar N) :=
  measurableSet_pottsCeiling.union measurableSet_pottsGround

lemma measurableSet_pottsM (k : Fin 7) : MeasurableSet (pottsM N k) := by
  classical
  exact MeasurableSet.of_discrete

lemma isRSymmetric_pottsCeiling : IsRSymmetric (ZMod (N + 2)) (pottsCeiling N) := by
  intro k
  ext ζ
  rcases fin_two_eq_zero_or_one k with rfl | rfl <;>
    simp only [Set.mem_preimage, pottsCeiling, Set.mem_ofPred_eq, pottsBotEq, pottsRightEq,
      pottsTopEq, pottsLeftEq, cubeRefl_apply, cubeSiteRefl_zero_sqCorner,
      cubeSiteRefl_one_sqCorner, show (0 : Fin 2) + 1 = 1 from rfl,
      show (1 : Fin 2) + 1 = 0 from rfl] <;>
    (constructor <;> rintro ⟨a, b, c, d⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
      first
        | exact a h | exact a h.symm | exact b h | exact b h.symm
        | exact c h | exact c h.symm | exact d h | exact d h.symm)

lemma isRSymmetric_pottsGround : IsRSymmetric (ZMod (N + 2)) (pottsGround N) :=
  isRSymmetric_iUnion fun n ↦ isRSymmetric_pottsG n

lemma isRSymmetric_pottsGBar : IsRSymmetric (ZMod (N + 2)) (pottsGBar N) := by
  intro k
  rw [pottsGBar, Set.preimage_union, isRSymmetric_pottsCeiling k, isRSymmetric_pottsGround k]

/-- **Georgii, Lemma (19.25)**, modulo the counting estimates of his Steps 3–5.  For every
`μ ∈ 𝒢₀(βΦ)`, every finite `D` and every `c` which dominates the seven torus quantities
`°γ_{Λ(n)}^{βΦ}(A_k)^{1/|Λ(n)|}` eventually in `n`,

`μ(D ∩ V(Ḡ, ·) = ∅) ≤ (7c)^{|D|}`.

With `c = N^{-1/4}` this is Georgii's `t_N = 7 N^{-1/4}`. -/
theorem forall_notMem_latticePattern_pottsGBar_le {β : ℝ}
    {μ : ProbabilityMeasure ((Fin 2 → ℤ) → ZMod (N + 2))}
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (D : Finset (Fin 2 → ℤ)) {c : ℝ≥0∞}
    (hc : ∀ᶠ n : ℕ in atTop, ∀ k : Fin 7,
      periodicGibbsDist (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) (N := n + 1)
        {ω | ∀ i, tauPow (cubeRefl (ZMod (N + 2))) i (cubeView ω i) ∈ pottsM N k}
          ≤ c ^ ((2 * (n + 1)) ^ 2)) :
    (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
        {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ (7 * c) ^ D.card := by
  classical
  have hev : {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω}
      = {ω | ∀ i ∈ D, latticeCubeView ω i ∉ pottsGBar N} := by
    ext ω
    exact forall_congr' fun i ↦ imp_congr_right fun _ ↦
      not_congr (mem_latticePattern_of_isRSymmetric isRSymmetric_pottsGBar ω i)
  set ex : ((↥(D : Finset (Fin 2 → ℤ))) → Fin 7) → (Fin 2 → ℤ) → Fin 7 :=
    fun ψ i ↦ if h : i ∈ D then ψ ⟨i, h⟩ else 0 with hex
  set S : ((↥(D : Finset (Fin 2 → ℤ))) → Fin 7) → Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    fun ψ ↦ {ω | ∀ i ∈ D, latticeCubeView ω i ∈ pottsM N (ex ψ i)} with hS
  have hcover : {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ∀ i ∈ D, latticeCubeView ω i ∉ pottsGBar N}
      ⊆ ⋃ ψ ∈ (Finset.univ : Finset ((↥(D : Finset (Fin 2 → ℤ))) → Fin 7)), S ψ := by
    intro ω hω
    choose f hf using fun i : ↥(D : Finset (Fin 2 → ℤ)) ↦ exists_mem_pottsM (hω i.1 i.2)
    refine Set.mem_iUnion₂.2 ⟨f, Finset.mem_univ f, fun i hi ↦ ?_⟩
    have hexf : ex f i = f ⟨i, hi⟩ := by rw [hex]; exact dif_pos hi
    rw [hexf]
    exact hf ⟨i, hi⟩
  rw [hev]
  refine le_trans (measure_mono hcover) (le_trans (measure_biUnion_finset_le _ _) ?_)
  have hbound : ∀ ψ ∈ (Finset.univ : Finset ((↥(D : Finset (Fin 2 → ℤ))) → Fin 7)),
      (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) (S ψ) ≤ c ^ D.card := fun ψ _ ↦
    forall_mem_latticeCubeView_le_pow (d := 1) (measurable_smul_pottsSq β)
      (smul_pottsSq_bddBelow β) (fun k ζ ↦ smul_pottsSq_cubeRefl β k ζ)
      (fun k ↦ measurableSet_pottsM k) hμ D (ex ψ) hc
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_coe,
    Fintype.card_fin, mul_pow]
  norm_num

end Lemma1925

/-!
## Georgii (19.26): the proof of Theorem (19.23)

Georgii's stable partition `\{G_0, G\}` of `Ḡ`, and the conditional measures `μ(· | ξ⁰(G_0, ·) ≠ ∅)`
and `μ(· | ξ⁰(G, ·) ≠ ∅)`.
-/

section Theorem1923

variable {N : ℕ}

/-- **Georgii's partition `\{G_0, G\}` of `Ḡ`**, the local ceiling states and the local ground
states. -/
def pottsPair : Fin 2 → Set ((Fin 2 → Fin 2) → ZMod (N + 2))
  | 0 => pottsCeiling N
  | 1 => pottsGround N

@[simp] lemma pottsPair_zero : pottsPair (N := N) 0 = pottsCeiling N := rfl

@[simp] lemma pottsPair_one : pottsPair (N := N) 1 = pottsGround N := rfl

lemma iUnion_pottsPair : (⋃ n, pottsPair (N := N) n) = pottsGBar N := by
  ext ζ
  constructor
  · rintro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    rcases fin_two_eq_zero_or_one n with rfl | rfl
    · exact Or.inl hn
    · exact Or.inr hn
  · rintro (h | h)
    · exact Set.mem_iUnion.2 ⟨0, h⟩
    · exact Set.mem_iUnion.2 ⟨1, h⟩

lemma measurableSet_pottsPair (n : Fin 2) : MeasurableSet (pottsPair (N := N) n) := by
  rcases fin_two_eq_zero_or_one n with rfl | rfl
  · exact measurableSet_pottsCeiling
  · exact measurableSet_pottsGround

/-- **Georgii's stability of `\{G_0, G\}`**: a face of the unit square is a bond, and its two
spins agree throughout `G` and differ throughout `G_0`. -/
theorem isPStablePartition_pottsPair :
    IsPStablePartition (pottsSq N) (pottsNu N) Set.univ (pottsPair (N := N)) where
  exists_localGroundStates_subset := by
    obtain ⟨ε, hε, hsub⟩ := exists_pos_localGroundStates_subset_potts (N := N)
    exact ⟨ε, hε, hsub.trans (Set.subset_iUnion (pottsPair (N := N)) 1)⟩
  pairwise_disjoint_faceRestrict := by
    intro k _ a
    have key : ∀ ζ ζ' : (Fin 2 → Fin 2) → ZMod (N + 2), ζ ∈ pottsCeiling N →
        ζ' ∈ pottsGround N → faceRestrict (ZMod (N + 2)) k a ζ
          ≠ faceRestrict (ZMod (N + 2)) k a ζ' := by
      intro ζ ζ' hζ hζ' heq
      obtain ⟨g1, g2, g3, g4⟩ := (mem_pottsGround_iff ζ').1 hζ'
      obtain ⟨c1, c2, c3, c4⟩ := hζ
      have hval : ∀ (c : Fin 2 → Fin 2) (hc : c k = a), ζ c = ζ' c := fun c hc ↦
        congrFun heq ⟨c, hc⟩
      rcases fin_two_eq_zero_or_one k with rfl | rfl <;>
        rcases fin_two_eq_zero_or_one a with rfl | rfl
      · exact c4 ((hval (sqCorner 0 0) rfl).trans (g4.trans (hval (sqCorner 0 1) rfl).symm))
      · exact c2 ((hval (sqCorner 1 0) rfl).trans (g2.trans (hval (sqCorner 1 1) rfl).symm))
      · exact c1 ((hval (sqCorner 0 0) rfl).trans (g1.trans (hval (sqCorner 1 0) rfl).symm))
      · exact c3 ((hval (sqCorner 0 1) rfl).trans (g3.trans (hval (sqCorner 1 1) rfl).symm))
    intro m n hmn
    rcases fin_two_eq_zero_or_one m with rfl | rfl <;> rcases fin_two_eq_zero_or_one n with rfl | rfl
    · exact absurd rfl hmn
    · rintro U hU hU' x hx
      obtain ⟨ζ, hζ, rfl⟩ := hU hx
      obtain ⟨ζ', hζ', heq⟩ := hU' hx
      exact absurd heq.symm (key ζ ζ' hζ hζ')
    · rintro U hU hU' x hx
      obtain ⟨ζ, hζ, rfl⟩ := hU hx
      obtain ⟨ζ', hζ', heq⟩ := hU' hx
      exact absurd heq (key ζ' ζ hζ' hζ)
    · exact absurd rfl hmn

/-! ### The core estimate of Georgii (19.26) -/

variable {β : ℝ} {t : ℝ≥0∞} {μ : ProbabilityMeasure ((Fin 2 → ℤ) → ZMod (N + 2))}

/-- **Georgii (19.26), the first display**: from Lemma (19.25) and Lemmas (18.14), (18.16),
`μ(0 ∈ ξ⁰(Ḡ, ·)) ≥ 1 - ε_N/2` with `ε_N = 8 z(t_N)`. -/
theorem le_measure_mem_latticeOceanPart_pottsGBar
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (hcb : ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ t ^ D.card) :
    1 - 4 * Peierls.crossingBound t ≤ (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} :=
  le_measure_mem_latticeOceanPart_of_forall_le_pow (ν := pottsNu N) measurableSet_pottsGBar
    isRSymmetric_pottsGBar
    (isQuasiGibbsianWith_of_mem_GZero (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β) hμ)
    (measurePreserving_shift_of_mem_GZero (measurable_smul_pottsSq β) hμ) hcb

/-- **Georgii (19.26)**: on the event that the origin lies in the ocean of `Ḡ` and its two spins
along `e_1` differ, the origin lies in the ocean of the local *ceiling* states.  This is the
stability of the partition `\{G_0, G\}`. -/
theorem mem_latticeOceanPart_pottsCeiling_of {ω : (Fin 2 → ℤ) → ZMod (N + 2)}
    (h1 : (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω)
    (h2 : ω 0 ≠ ω pottsE1) :
    (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω := by
  have hU := (isPStablePartition_pottsPair (N := N)).setOf_mem_latticeOceanPart_iUnion_eq
    (0 : Peierls.Site)
  rw [iUnion_pottsPair] at hU
  have h1' : ω ∈ {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
      (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} := h1
  rw [hU] at h1'
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h1'
  rcases fin_two_eq_zero_or_one n with rfl | rfl
  · exact hn
  · exfalso
    have hpat : (0 : Peierls.Site) ∈ latticePattern (ZMod (N + 2)) (pottsGround N) ω :=
      SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hn)
    rw [mem_latticePattern_of_isRSymmetric isRSymmetric_pottsGround] at hpat
    obtain ⟨h1b, -, -, -⟩ := (mem_pottsGround_iff _).1 hpat
    have hb : ω (0 + intCubeCast (sqCorner 0 0)) = ω (0 + intCubeCast (sqCorner 1 0)) := h1b
    rw [zero_add, zero_add, intCubeCast_sqCorner_zero_zero] at hb
    exact h2 hb

/-- **Georgii (19.26), Step 1, the second display**: `μ(0 ∈ ξ⁰(G_0, ·)) ≥ (1 - ε_N)/2`. -/
theorem le_measureReal_mem_latticeOceanPart_pottsCeiling
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (hcb : ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ t ^ D.card)
    (hhalf : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real {ω | ω 0 = ω pottsE1} ≤ 1 / 2)
    (hz : 8 * (Peierls.crossingBound t).toReal < 1) :
    (1 - 8 * (Peierls.crossingBound t).toReal) / 2
      ≤ (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real
        {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω} := by
  classical
  set ρ := (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) with hρ
  set z := (Peierls.crossingBound t).toReal with hzdef
  have hzne : Peierls.crossingBound t ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (Peierls.crossingBound_le_one t)
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  set X : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} with hX
  set C : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω} with hC
  set Y : Set ((Fin 2 → ℤ) → ZMod (N + 2)) := {ω | ω 0 = ω pottsE1}ᶜ with hY
  -- the ocean bound in real form
  have hXbound : 1 - 4 * z ≤ ρ.real X := by
    have h := le_measure_mem_latticeOceanPart_pottsGBar hμ hcb
    have hle : 4 * Peierls.crossingBound t ≤ 1 := by
      rw [← ENNReal.ofReal_toReal hzne, ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h2 := ENNReal.toReal_mono (measure_ne_top ρ X) h
    rwa [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_mul, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] at h2
  -- the bond bound
  have hYmeas : MeasurableSet Y := (measurableSet_setOf_eq_apply _ _).compl
  have hYbound : (1 : ℝ) / 2 ≤ ρ.real Y := by
    have h := measureReal_add_measureReal_compl (μ := ρ) (measurableSet_setOf_eq_apply
      (0 : Fin 2 → ℤ) pottsE1)
    have huniv : ρ.real Set.univ = 1 := by rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv] at h
    rw [hY]
    linarith
  -- the intersection
  have hinter : (1 : ℝ) / 2 - 4 * z ≤ ρ.real (X ∩ Y) := by
    have h := measureReal_union_add_inter (μ := ρ) (s := X) (t := Y) hYmeas
    have hle1 : ρ.real (X ∪ Y) ≤ 1 := by
      have := measureReal_mono (μ := ρ) (Set.subset_univ (X ∪ Y))
      rwa [show ρ.real Set.univ = 1 by rw [Measure.real, measure_univ, ENNReal.toReal_one]] at this
    linarith
  have hsub : X ∩ Y ⊆ C := fun ω hω ↦ mem_latticeOceanPart_pottsCeiling_of hω.1 hω.2
  have := measureReal_mono (μ := ρ) hsub
  linarith

/-- **Georgii (19.26), Step 1**: `μ(ξ⁰(G_0, ·) ≠ ∅) ≤ μ(0 ∈ ξ⁰(G_0, ·)) + μ(0 ∉ ξ⁰(Ḡ, ·))`. -/
theorem setOf_latticeOceanPart_pottsCeiling_nonempty_subset :
    {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        (latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω).Nonempty}
      ⊆ {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω}
        ∪ {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω}ᶜ := by
  intro ω hω
  by_cases hX : (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω
  · refine Or.inl ?_
    have hn : (latticeOceanPart (ZMod (N + 2)) (pottsPair (N := N) 0) ω).Nonempty := hω
    have heq := (isPStablePartition_pottsPair (N := N)).latticeOceanPart_iUnion_eq hn
    rw [iUnion_pottsPair, pottsPair_zero] at heq
    rw [Set.mem_ofPred_eq, ← heq]
    exact hX
  · exact Or.inr hX

/-- **Georgii, Theorem (19.23)(I)**, from Lemma (19.25).  For a `μ ∈ 𝒢₀(βΦ)` satisfying the
chessboard estimate of (19.25) with weight `t` and the bond bound `μ(σ_i = σ_j) ≤ 1/2` of
Lemma (19.24), the conditional measure `μ_0 = μ(· | ξ⁰(G_0, ·) ≠ ∅)` is a Gibbs measure for
`βΦ` which lives on the percolation event of the local ceiling states and satisfies
`μ_0(0 ∈ ξ⁰(G_0, ·)) ≥ 1 - ε_N`, `ε_N = 8 z(t)`.  It inherits every symmetry of `βΦ` — in
particular `r_0`, `r_1`, `r_2`, the shifts and all permutations of `E` — which preserves `G_0`. -/
theorem exists_gibbsMeasure_pottsCeiling
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (hcb : ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ t ^ D.card)
    (hhalf : (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real {ω | ω 0 = ω pottsE1} ≤ 1 / 2)
    (hz : 8 * (Peierls.crossingBound t).toReal < 1) :
    ∃ ρ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)), IsProbabilityMeasure ρ ∧
      Specification.IsGibbsMeasure (cubeGibbsSpec (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ)
        (pottsNu N) (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β)) ρ ∧
      ρ {ω | (latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω).Nonempty} = 1 ∧
      1 - 8 * (Peierls.crossingBound t).toReal ≤ ρ.real
        {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω} ∧
      (∀ a : Fin 2 → ℤ, MeasurePreserving (shift (ZMod (N + 2)) a).toFun ρ ρ) ∧
      (∀ τ : CubeTransformation (ZMod (N + 2)) 2,
        τ.IsSymmetry (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) →
        τ.onCube.toFun ⁻¹' pottsCeiling N = pottsCeiling N →
        MeasurePreserving (τ.onLattice (ZMod (N + 2))).toFun ρ ρ) := by
  classical
  set σm := (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) with hσm
  set z := (Peierls.crossingBound t).toReal with hzdef
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  set X : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} with hX
  set C : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω} with hC
  set A : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω).Nonempty} with hA
  have hAmeas : MeasurableSet A := measurableSet_setOf_latticeOceanPart_nonempty
    measurableSet_pottsCeiling
  have hXmeas : MeasurableSet X := measurableSet_setOf_mem_latticeOceanPart measurableSet_pottsGBar 0
  have hCA : C ⊆ A := fun ω hω ↦ ⟨0, hω⟩
  have hCbound := le_measureReal_mem_latticeOceanPart_pottsCeiling hμ hcb hhalf hz
  have hCpos : 0 < σm.real C := lt_of_lt_of_le (by linarith) hCbound
  have hApos : σm A ≠ 0 := by
    intro h0
    have : σm.real C = 0 := by
      have := measure_mono_null hCA h0
      rw [Measure.real, this, ENNReal.toReal_zero]
    linarith
  -- `μ(A) ≤ μ(C) + 4z`
  have hXbound : 1 - 4 * z ≤ σm.real X := by
    have h := le_measure_mem_latticeOceanPart_pottsGBar hμ hcb
    have hle : 4 * Peierls.crossingBound t ≤ 1 := by
      have hzne : Peierls.crossingBound t ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.one_ne_top (Peierls.crossingBound_le_one t)
      rw [← ENNReal.ofReal_toReal hzne, ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h2 := ENNReal.toReal_mono (measure_ne_top σm X) h
    rwa [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_mul, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] at h2
  have hAle : σm.real A ≤ σm.real C + 4 * z := by
    have h1 := measureReal_mono (μ := σm) setOf_latticeOceanPart_pottsCeiling_nonempty_subset
    have h2 := measureReal_union_le (μ := σm) C Xᶜ
    have h3 := measureReal_add_measureReal_compl (μ := σm) hXmeas
    have huniv : σm.real Set.univ = 1 := by rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv] at h3
    linarith
  -- the conditional measure
  have hprob : IsProbabilityMeasure (σm[|A]) := cond_isProbabilityMeasure hApos
  refine ⟨σm[|A], hprob, ?_, ?_, ?_, ?_, ?_⟩
  · exact isGibbsMeasure_cond_of_tail σm
      (mem_GP_of_mem_GZero (measurable_smul_pottsSq β) (smul_pottsSq_bddBelow' β) hμ)
      (tail_measurableSet_setOf_latticeOceanPart_nonempty measurableSet_pottsCeiling) hApos
  · exact cond_apply_self hApos (measure_ne_top _ _)
  · have hcond : (σm[|A]) C = (σm A)⁻¹ * σm C := by
      rw [cond_apply hAmeas, Set.inter_eq_self_of_subset_right hCA]
    have hAreal : 0 < σm.real A := lt_of_lt_of_le hCpos (measureReal_mono (μ := σm) hCA)
    have hreal : (σm[|A]).real C = (σm.real A)⁻¹ * σm.real C := by
      rw [Measure.real, hcond, ENNReal.toReal_mul, ENNReal.toReal_inv]
      rfl
    rw [hreal, inv_mul_eq_div, le_div_iff₀ hAreal]
    nlinarith [hCbound, hAle, hz0, hz]
  · intro a
    exact (measurePreserving_shift_of_mem_GZero (measurable_smul_pottsSq β) hμ a).cond_of_preimage_eq
      hAmeas (by
        rw [preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow,
          (isRSymmetric_pottsCeiling).preimage_tauPow])
  · intro τ hτ hpre
    exact (hτ.measurePreserving_onLattice_of_mem_GZero (measurable_smul_pottsSq β)
      (smul_pottsSq_bddBelow' β) hμ).cond_of_preimage_eq hAmeas (by
        rw [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre])

/-! ### Georgii (19.26), Step 2: the `N` ordered phases -/

/-- The ground-state counterpart of `mem_latticeOceanPart_pottsCeiling_of`. -/
theorem mem_latticeOceanPart_pottsGround_of {ω : (Fin 2 → ℤ) → ZMod (N + 2)}
    (h1 : (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω)
    (h2 : ω 0 = ω pottsE1) :
    (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGround N) ω := by
  have hU := (isPStablePartition_pottsPair (N := N)).setOf_mem_latticeOceanPart_iUnion_eq
    (0 : Peierls.Site)
  rw [iUnion_pottsPair] at hU
  have h1' : ω ∈ {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
      (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} := h1
  rw [hU] at h1'
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h1'
  rcases fin_two_eq_zero_or_one n with rfl | rfl
  · exfalso
    have hpat : (0 : Peierls.Site) ∈ latticePattern (ZMod (N + 2)) (pottsCeiling N) ω :=
      SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset hn)
    rw [mem_latticePattern_of_isRSymmetric isRSymmetric_pottsCeiling] at hpat
    obtain ⟨c1, -, -, -⟩ := hpat
    refine c1 ?_
    have hb : ω (0 + intCubeCast (sqCorner 0 0)) = ω (0 + intCubeCast (sqCorner 1 0)) := by
      rw [zero_add, zero_add, intCubeCast_sqCorner_zero_zero]
      exact h2
    exact hb
  · exact hn

/-- **Georgii (19.26), Step 2**: `μ(0 ∈ ξ⁰(G, ·)) ≥ (1 - ε_N)/2` when `μ(σ_i = σ_j) ≥ 1/2`. -/
theorem le_measureReal_mem_latticeOceanPart_pottsGround
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (hcb : ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ t ^ D.card)
    (hhalf : 1 / 2 ≤ (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real {ω | ω 0 = ω pottsE1})
    (hz : 8 * (Peierls.crossingBound t).toReal < 1) :
    (1 - 8 * (Peierls.crossingBound t).toReal) / 2
      ≤ (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real
        {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGround N) ω} := by
  classical
  set ρ := (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) with hρ
  set z := (Peierls.crossingBound t).toReal with hzdef
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  set X : Set ((Fin 2 → ℤ) → ZMod (N + 2)) :=
    {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGBar N) ω} with hX
  set Y : Set ((Fin 2 → ℤ) → ZMod (N + 2)) := {ω | ω 0 = ω pottsE1} with hY
  have hXbound : 1 - 4 * z ≤ ρ.real X := by
    have h := le_measure_mem_latticeOceanPart_pottsGBar hμ hcb
    have hzne : Peierls.crossingBound t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (Peierls.crossingBound_le_one t)
    have hle : 4 * Peierls.crossingBound t ≤ 1 := by
      rw [← ENNReal.ofReal_toReal hzne, ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have h2 := ENNReal.toReal_mono (measure_ne_top ρ X) h
    rwa [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_mul, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] at h2
  have hYmeas : MeasurableSet Y := measurableSet_setOf_eq_apply _ _
  have hinter : (1 : ℝ) / 2 - 4 * z ≤ ρ.real (X ∩ Y) := by
    have h := measureReal_union_add_inter (μ := ρ) (s := X) (t := Y) hYmeas
    have hle1 : ρ.real (X ∪ Y) ≤ 1 := by
      have := measureReal_mono (μ := ρ) (Set.subset_univ (X ∪ Y))
      rwa [show ρ.real Set.univ = 1 by rw [Measure.real, measure_univ, ENNReal.toReal_one]] at this
    linarith
  have hsub : X ∩ Y ⊆ {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
      (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGround N) ω} :=
    fun ω hω ↦ mem_latticeOceanPart_pottsGround_of hω.1 hω.2
  have := measureReal_mono (μ := ρ) hsub
  linarith

lemma iUnion_pottsG : (⋃ n, pottsG (N := N) n) = pottsGround N := rfl

/-- **Georgii, Theorem (19.23)(II)**, from Lemma (19.25).  For a `μ ∈ 𝒢₀(βΦ)` satisfying the
chessboard estimate of (19.25) with weight `t` and the bond bound `μ(σ_i = σ_j) ≥ 1/2` of Lemma
(19.24), the argument of Theorem (18.25) decomposes `μ` into `N` mutually singular shift-invariant
Gibbs measures `μ_1, …, μ_N` for `βΦ`, the `n`-th carried by the percolation event of the ground
state `(nn/nn)`, permuted into one another by the transformations of `E`, and each invariant
under every symmetry of `βΦ` preserving its ground state — in particular under `r_0`, `r_1`,
`r_2`. -/
theorem exists_gibbsMeasure_family_potts
    (hμ : μ ∈ GZero (ZMod (N + 2)) (fun ζ ↦ β * pottsSq N ζ) (pottsNu N))
    (hcb : ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2)))
      {ω | ∀ i ∈ D, i ∉ latticePattern (ZMod (N + 2)) (pottsGBar N) ω} ≤ t ^ D.card)
    (hhalf : 1 / 2 ≤ (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))).real {ω | ω 0 = ω pottsE1})
    (hz : 8 * (Peierls.crossingBound t).toReal < 1) :
    ∃ ρ : ZMod (N + 2) → Measure ((Fin 2 → ℤ) → ZMod (N + 2)),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (ZMod (N + 2))
        (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) (measurable_smul_pottsSq β)
        (smul_pottsSq_bddBelow' β)) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart (ZMod (N + 2)) (pottsG n) ω).Nonempty} = 1) ∧
      (∀ n, (1 - 8 * (Peierls.crossingBound t).toReal) / 2 ≤ (ρ n).real
        {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsG n) ω}) ∧
      (∀ (n : ZMod (N + 2)) (a : Fin 2 → ℤ),
        MeasurePreserving (shift (ZMod (N + 2)) a).toFun (ρ n) (ρ n)) ∧
      (∀ (n : ZMod (N + 2)) (τ : CubeTransformation (ZMod (N + 2)) 2),
        τ.IsSymmetry (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) →
        τ.onCube.toFun '' pottsG n = pottsG n →
        MeasurePreserving (τ.onLattice (ZMod (N + 2))).toFun (ρ n) (ρ n)) ∧
      (∀ m n : ZMod (N + 2), (ρ m).map
        ((pottsShift (n - m)).onLattice (ZMod (N + 2))).toFun = ρ n) := by
  classical
  set σm := (μ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))) with hσm
  have hGbound := le_measureReal_mem_latticeOceanPart_pottsGround hμ hcb hhalf hz
  have hpos : 0 < σm {ω | (latticeOceanPart (ZMod (N + 2)) (⋃ n, pottsG (N := N) n) ω).Nonempty} := by
    rw [pos_iff_ne_zero]
    intro h0
    have hsub : {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGround N) ω}
        ⊆ {ω | (latticeOceanPart (ZMod (N + 2)) (⋃ n, pottsG (N := N) n) ω).Nonempty} :=
      fun ω hω ↦ ⟨0, hω⟩
    have := measure_mono_null hsub h0
    rw [show σm.real {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsGround N) ω} = 0 by
      rw [Measure.real, this, ENNReal.toReal_zero]] at hGbound
    linarith
  obtain ⟨ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_gibbsMeasure_family (φ₀ := pottsSq N) (measurable_smul_pottsSq β)
      (smul_pottsSq_bddBelow' β) (isPStablePartition_pottsG pottsDelta_lt)
      ((isPhiSymmetric_pottsG (φ := pottsDelta)).const_mul pottsSq_cubeRefl β)
      measurableSet_pottsG hμ hpos
  refine ⟨ρ, h1, h2, h3, h4, h5, fun n ↦ ?_, fun n a ↦ h7 n a
      ((isRSymmetric_pottsG n).preimage_tauPow _), fun n τ hτ hG ↦ h8 n τ hτ hG, fun m n ↦ ?_⟩
  · have hprob := h1 n
    have := ENNReal.toReal_mono (measure_ne_top (ρ n) _) (h6 n)
    rw [iUnion_pottsG] at this
    exact le_trans hGbound this
  · refine h9 m n _ ((isSymmetry_pottsShift (n - m)).const_mul pottsSq_cubeRefl β) ?_
    rw [pottsG, pottsG, Set.image_singleton]
    congr 1
    funext c
    rw [onCube_pottsShift_apply]
    ring

/-! ### The symmetries `r_0`, `r_1`, `r_2` and the permutations of `E` -/

lemma planeRot_onCube_sqCorner (ζ : (Fin 2 → Fin 2) → ZMod (N + 2)) (a b : Fin 2) :
    (CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onCube.toFun ζ (sqCorner a b)
      = ζ (sqCorner b (a + 1)) := by
  rw [CubeTransformation.planeRot_onCube_toFun_apply]
  congr 1
  funext l
  fin_cases l <;> simp

/-- **`r_0` preserves the local ceiling states**: the quarter turn permutes the four bonds of the
unit square cyclically. -/
lemma preimage_planeRot_pottsCeiling :
    (CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onCube.toFun ⁻¹' pottsCeiling N
      = pottsCeiling N := by
  ext ζ
  simp only [Set.mem_preimage, pottsCeiling, Set.mem_ofPred_eq, pottsBotEq, pottsRightEq,
    pottsTopEq, pottsLeftEq, planeRot_onCube_sqCorner, show (0 : Fin 2) + 1 = 1 from rfl,
    show (1 : Fin 2) + 1 = 0 from rfl]
  constructor <;> rintro ⟨a, b, c, d⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    first
      | exact a h | exact a h.symm | exact b h | exact b h.symm
      | exact c h | exact c h.symm | exact d h | exact d h.symm

/-- **`r_0` fixes each ground state**: a constant configuration is fixed by a purely spatial cube
transformation. -/
lemma image_planeRot_pottsG (n : ZMod (N + 2)) :
    (CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onCube.toFun '' pottsG n
      = pottsG n := by
  have h : (CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onCube.toFun (fun _ ↦ n)
      = fun _ ↦ n := by funext c; rfl
  rw [pottsG, Set.image_singleton, h]

/-- **`r_k` fixes each ground state.** -/
lemma image_cubeRefl_pottsG (k : Fin 2) (n : ZMod (N + 2)) :
    (CubeTransformation.refl (E := ZMod (N + 2)) k).onCube.toFun '' pottsG n = pottsG n := by
  have h : (CubeTransformation.refl (E := ZMod (N + 2)) k).onCube.toFun (fun _ ↦ n)
      = fun _ ↦ n := by funext c; rfl
  rw [pottsG, Set.image_singleton, h]

/-- **`r_k` preserves the local ceiling states.** -/
lemma preimage_cubeRefl_pottsCeiling (k : Fin 2) :
    (CubeTransformation.refl (E := ZMod (N + 2)) k).onCube.toFun ⁻¹' pottsCeiling N
      = pottsCeiling N := by
  rw [CubeTransformation.refl_onCube_toFun]
  exact isRSymmetric_pottsCeiling k

set_option linter.unusedFintypeInType false in
/-- **Every bijection of a finite state space preserves the normalised counting measure.**
Intended home: `GibbsMeasure/Model/PottsOceans.lean`, next to
`measurePreserving_addLeft_uniformOn`. -/
lemma measurePreserving_uniformOn_of_equiv {F : Type*} [Fintype F] [MeasurableSpace F]
    [MeasurableSingletonClass F] (e : F ≃ᵐ F) :
    MeasurePreserving e (uniformOn (Set.univ : Set F)) (uniformOn (Set.univ : Set F)) := by
  refine ⟨e.measurable, Measure.ext fun s hs ↦ ?_⟩
  rw [Measure.map_apply e.measurable hs, uniformOn_univ, uniformOn_univ]
  congr 1
  calc Measure.count (e ⁻¹' s)
      = Measure.count (e '' (e ⁻¹' s)) := (Measure.count_injective_image e.injective _).symm
    _ = Measure.count s := by rw [Set.image_preimage_eq s e.surjective]

/-- **Georgii's transformations `ω → (π ω_i)_i` for an arbitrary permutation `π` of `E`.** -/
abbrev pottsPerm (e : ZMod (N + 2) ≃ᵐ ZMod (N + 2)) : CubeTransformation (ZMod (N + 2)) 2 :=
  CubeTransformation.pureSpin fun _ ↦ e

/-- **Every permutation of `E` is a symmetry of the Potts cube interaction.** -/
theorem isSymmetry_pottsPerm (e : ZMod (N + 2) ≃ᵐ ZMod (N + 2)) (β : ℝ) :
    (pottsPerm e).IsSymmetry (fun ζ ↦ β * pottsSq N ζ) (pottsNu N) := by
  refine CubeTransformation.IsSymmetry.of_apply_onCube (fun k ζ ↦ smul_pottsSq_cubeRefl β k ζ)
    (fun c ↦ measurePreserving_uniformOn_of_equiv e) (fun ζ ↦ ?_)
  refine congrArg (fun r ↦ β * r) ?_
  refine cubeBondSum_onCube _ (fun c c' _ x y ↦ ?_) ζ
  change pottsDelta (e x - e y) = pottsDelta (x - y)
  rw [pottsDelta_sub, pottsDelta_sub]
  by_cases h : x = y
  · simp [h]
  · simp [h]

/-- **A permutation of `E` carries the ground state `(mm/mm)` to `(π(m) π(m)/π(m) π(m))`**:
Georgii's "`μ_m` is transformed into `μ_n` by each permutation of `E` which sends `m` to `n`". -/
lemma image_pottsPerm_pottsG (e : ZMod (N + 2) ≃ᵐ ZMod (N + 2)) (n : ZMod (N + 2)) :
    (pottsPerm e).onCube.toFun '' pottsG n = pottsG (e n) := by
  have h : (pottsPerm e).onCube.toFun (fun _ ↦ n) = fun _ ↦ e n := by funext c; rfl
  rw [pottsG, pottsG, Set.image_singleton, h]

/-- **A permutation of `E` preserves the local ceiling states.** -/
lemma preimage_pottsPerm_pottsCeiling (e : ZMod (N + 2) ≃ᵐ ZMod (N + 2)) :
    (pottsPerm e).onCube.toFun ⁻¹' pottsCeiling N = pottsCeiling N := by
  ext ζ
  have happ : ∀ c, (pottsPerm e).onCube.toFun ζ c = e (ζ c) := fun c ↦ by
    rw [CubeTransformation.pureSpin_onCube_toFun_apply]
  simp only [Set.mem_preimage, pottsCeiling, Set.mem_ofPred_eq, pottsBotEq, pottsRightEq,
    pottsTopEq, pottsLeftEq, happ]
  constructor <;> rintro ⟨a, b, c, d⟩ <;>
    exact ⟨fun h ↦ a (by first | exact congrArg e h | exact e.injective h),
      fun h ↦ b (by first | exact congrArg e h | exact e.injective h),
      fun h ↦ c (by first | exact congrArg e h | exact e.injective h),
      fun h ↦ d (by first | exact congrArg e h | exact e.injective h)⟩

/-! ### The first-order transition -/

/-- On the percolation event of the local ceiling states the two spins of a bond at the origin
differ. -/
lemma ne_of_mem_latticeOceanPart_pottsCeiling {ω : (Fin 2 → ℤ) → ZMod (N + 2)}
    (h : (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω) :
    ω 0 ≠ ω pottsE1 := by
  have hpat : (0 : Peierls.Site) ∈ latticePattern (ZMod (N + 2)) (pottsCeiling N) ω :=
    SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset h)
  rw [mem_latticePattern_of_isRSymmetric isRSymmetric_pottsCeiling] at hpat
  obtain ⟨c1, -, -, -⟩ := hpat
  intro hcon
  refine c1 ?_
  have hb : ω (0 + intCubeCast (sqCorner 0 0)) = ω (0 + intCubeCast (sqCorner 1 0)) := by
    rw [zero_add, zero_add, intCubeCast_sqCorner_zero_zero]
    exact hcon
  exact hb

/-- On the percolation event of a ground state the two spins of a bond at the origin agree. -/
lemma eq_of_mem_latticeOceanPart_pottsG {n : ZMod (N + 2)} {ω : (Fin 2 → ℤ) → ZMod (N + 2)}
    (h : (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsG n) ω) :
    ω 0 = ω pottsE1 := by
  have hpat : (0 : Peierls.Site) ∈ latticePattern (ZMod (N + 2)) (pottsG n) ω :=
    SimpleGraph.infiniteClusters_subset (SimpleGraph.oceanPart_subset h)
  rw [mem_latticePattern_of_isRSymmetric (isRSymmetric_pottsG n)] at hpat
  have hz : latticeCubeView ω 0 = fun _ ↦ n := hpat
  have h0 := congrFun hz (sqCorner 0 0)
  have h1 := congrFun hz (sqCorner 1 0)
  rw [latticeCubeView_apply, zero_add, intCubeCast_sqCorner_zero_zero] at h0
  rw [latticeCubeView_apply, zero_add] at h1
  rw [h0, h1]

/-- **Georgii, the paragraph after Theorem (19.23)**: a chaotic phase and an ordered phase at the
same inverse temperature `β` force `∂₋F_Φ(β) < ∂₊F_Φ(β)`, provided `ε < 1/2`.  Georgii applies
this at `β = β_N` with `ε = ε_N`, where Theorem (19.23)(III) produces both types of phase; the
conclusion is the discontinuity of the first derivative of the pressure, i.e. a first order
phase transition. -/
theorem leftDirDeriv_lt_rightDirDeriv_pottsF {β ε : ℝ} (hε : ε < 1 / 2)
    {ρ₀ ρ₁ : Measure ((Fin 2 → ℤ) → ZMod (N + 2))}
    [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ρ₁]
    (h0G : ρ₀ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
      (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))))
    (h0r : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun ρ₀ ρ₀)
    (h0 : 1 - ε ≤ ρ₀.real
      {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω})
    (h1G : ρ₁ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
      (Φ := ((β • pottsBTheta N : Potential.BTheta (Fin 2 → ℤ) (ZMod (N + 2))) :
        Potential (Fin 2 → ℤ) (ZMod (N + 2)))) (pottsNu N) 1)
      (shiftGroup (Fin 2 → ℤ) (ZMod (N + 2))))
    (h1r : MeasurePreserving
      ((CubeTransformation.planeRot (E := ZMod (N + 2)) (d := 0)).onLattice _).toFun ρ₁ ρ₁)
    {n : ZMod (N + 2)}
    (h1 : 1 - ε ≤ ρ₁.real
      {ω | (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsG n) ω}) :
    leftDirDeriv (pottsF N) β 1 < rightDirDeriv (pottsF N) β 1 := by
  have hmeas := measurableSet_setOf_eq_apply (N := N) (0 : Fin 2 → ℤ) pottsE1
  -- the chaotic phase has few equal bonds
  have hchaos : ρ₀.real {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1} ≤ ε := by
    have hsub : {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsCeiling N) ω}
        ⊆ {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1}ᶜ :=
      fun ω hω ↦ ne_of_mem_latticeOceanPart_pottsCeiling hω
    have hmono := measureReal_mono (μ := ρ₀) hsub
    have hcompl := measureReal_add_measureReal_compl (μ := ρ₀) hmeas
    have huniv : ρ₀.real Set.univ = 1 := by rw [Measure.real, measure_univ, ENNReal.toReal_one]
    rw [huniv] at hcompl
    linarith
  -- the ordered phase has many equal bonds
  have horder : 1 - ε ≤ ρ₁.real {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1} := by
    have hsub : {ω : (Fin 2 → ℤ) → ZMod (N + 2) |
        (0 : Peierls.Site) ∈ latticeOceanPart (ZMod (N + 2)) (pottsG n) ω}
        ⊆ {ω : (Fin 2 → ℤ) → ZMod (N + 2) | ω 0 = ω pottsE1} :=
      fun ω hω ↦ eq_of_mem_latticeOceanPart_pottsG hω
    exact le_trans h1 (measureReal_mono (μ := ρ₁) hsub)
  have hl := (leftDirDeriv_pottsF_le_le_rightDirDeriv β h0G h0r).1
  have hr := (leftDirDeriv_pottsF_le_le_rightDirDeriv β h1G h1r).2
  linarith

end Theorem1923

end MeasureTheory.GibbsMeasure

end

end

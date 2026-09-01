/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Singleton
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PerronFrobenius
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.Doeblin
public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Model.Ising

/-!
# Georgii (3.5), (3.9) and (3.15): Markov chains as Gibbs measures on `ℤ`

For a finite state space, the positive homogeneous Markov specifications on `ℤ` are exactly the
Gibbsian specifications of the homogeneous nearest-neighbour potentials, and each has the
stationary Markov chain `μ_P` as its unique Gibbs measure. The one-dimensional Ising model is the
instance `E = Bool`, `Φ_{i,i+1} = -J σ_i σ_{i+1}`, `Φ_{i} = -h σ_i`.
-/

@[expose] public section

/-!
## Setup and contents

Sites `ℤ`, finite state space `E`, reference measure the uniform probability measure on `E`.
Georgii uses counting measure on `E`; by Remark (1.28)(3) the Gibbs measures are the same, and the
repo works with a probability reference measure.

This file proves Georgii's Theorem (3.5): the map `P ↦ γ_P`, realised here as the Gibbsian
specification of the potential `-log P`, is a bijection from the positive stochastic matrices onto
the positive homogeneous Markov specifications on `ℤ`, and `𝒢(γ_P) = {μ_P}` where `μ_P` is the
stationary Markov chain with transition matrix `P`. Georgii's defining equation (3.6), which reads
`γ_Λ(σ_Λ = ζ|ω) = μ_P(σ_Λ = ζ|σ_{∂Λ} = ω_{∂Λ})`, is proved in full as
`markovSpecification_apply_cyl_eq_cond`: for every finite `Λ ⊆ ℤ` and *every* boundary condition
`ω`, with `∂Λ` the two-sided boundary of (3.4) (`boundary`) and the right-hand side the
elementary conditional probability `ProbabilityTheory.cond` (the conditioning event has positive
measure by `stationaryChain_cyl_pos`). Its explicit form (3.8)(1) is formalised for interval
volumes.

## The specification and its potential

* `markovPotential P`: the homogeneous nearest-neighbour potential `Φ_{i,i+1} = -log P(σ_i,
σ_{i+1})`
  of Corollary (3.9), with the instances `IsPotential`, `IsFiniteRange`, `IsAbsolutelySummable`.
* `markovSpecification P`: its Gibbsian specification (Georgii (3.6), Corollary (3.9)).
* `markovSpecification_Icc_apply_cyl`, `markovSpecification_Icc_apply_cyl_of_subset`: the
  finite-volume formula of Comment (3.8)(1), for an interval `Λ` inside an interval `Δ`.
* `markovSpecification_singleton_apply`: the determining function (3.11) of `markovSpecification P`.
* `bondsOf`, `hamiltonian_eq_sum_bondsOf`, `boltzmannFactor_eq_prod_bondsOf`: the Hamiltonian and
  the Boltzmann factor of an arbitrary finite volume as a sum/product over the bonds meeting it.

## Uniqueness (Georgii's step 5)

* `tendsto_markovSpecification_Icc_apply_cyl`: the Doeblin limit.
* `isGibbsMeasure_apply_cyl`, `eq_of_isGibbsMeasure`: `𝒢(γ_P)` has at most one element.

## The correspondence `γ ↔ P` (Georgii's steps 2–4)

* `matrixOfDetFun`, `matrixOfDetFun_markovDeterminingFun`, `markovSpecification_injOn`:
  formula (3.7) and the injectivity of `P ↦ γ` (step 2).
* `markovDeterminingFun_of_eq_312`: `(3.12) ⇒ (3.11)` (step 3).
* `eq_312_of_isPositiveHomogeneousMarkovWith`: equation (3.12) from the consistency of `γ` on
  `{1, 2}` (step 4).
* `exists_matrix_eq_markovSpecification`: surjectivity of `P ↦ γ`.

## Existence: the stationary Markov chain (Georgii's step 1)

* `stationaryChain P hP hpos`: the stationary Markov chain `μ_P` of (3.3), built as a projective
  limit of its finite-dimensional distributions.
* `markovChain_cylinder`: Georgii (3.3), the cylinder probabilities of `μ_P`.
* `isGibbsMeasure_markovSpecification_stationaryChain`: `μ_P ∈ 𝒢(γ_P)`.

## The full theorem

* `boundary`: the two-sided boundary `∂Λ` of Georgii (3.4).
* `markovSpecification_apply_cyl_eq_cond`: **Georgii (3.6)** — for every finite `Λ` and every
  boundary condition `ω`, `γ_Λ(σ_Λ = ζ|ω) = μ_P(σ_Λ = ζ | σ_{∂Λ} = ω_{∂Λ})`.
* `isCondExp_markovSpecification_stationaryChain`: `γ_Λ` is a version of the conditional
  distribution of `μ_P` given the exterior of `Λ`.
* `gibbsMeasure_eq_singleton`: `𝒢(markovSpecification P) = {μ_P}`.
* `georgii_3_5`: the packaged statement of Theorem (3.5).

## Homogeneous nearest-neighbour potentials and Corollary (3.9)

* `homogeneousNNPotential φ₁ φ₂`: Georgii's homogeneous nearest-neighbour potential
  `Φ_{i} = φ₁(σ_i)`, `Φ_{i,i+1} = φ₂(σ_i, σ_{i+1})`, `Φ_A = 0` otherwise, with the instances
  `IsPotential`, `IsFiniteRange`, `IsAbsolutelySummable`; `homogeneousNNSpecification φ₁ φ₂ β` is
  its Gibbsian specification at inverse temperature `β`.
* `homogeneousNNDeterminingFun`, `isPositiveHomogeneousMarkovWith_homogeneousNNSpecification`:
  **the converse half of Corollary (3.9)** — the Gibbsian specification of a homogeneous
  nearest-neighbour potential is a positive homogeneous Markov specification, with determining
  function `g(x,y,z) = e^{-β(φ₁(y) + φ₂(x,y) + φ₂(y,z))}` normalised over `y`.
* `markovPotential_eq_homogeneousNNPotential`, `homogeneousNNSpecification_neg_log`: the forward
  half — `γ_P` is Gibbsian for the homogeneous nearest-neighbour potential `-log P`.
* `isPositiveHomogeneousMarkov_iff_exists_homogeneousNNSpecification`: **Corollary (3.9)**.
* `determiningFun_unique`, `eq_of_isPositiveHomogeneousMarkovWith`: **Comment (3.2)** — a positive
  homogeneous Markov specification is determined by its determining function.
* `homogeneousNNSpecification_smul`: `β·Φ` is again a homogeneous nearest-neighbour potential.
* `exists_markovSpecification_eq_homogeneousNNSpecification`,
  `existsUnique_isGibbsMeasure_homogeneousNNSpecification`: Theorem (3.5) for an arbitrary
  homogeneous nearest-neighbour potential.

## Example (3.15): the one-dimensional Ising model

* `chainGraph`: the nearest-neighbour graph of `ℤ`; `isingPotential_chainGraph`,
  `isingSpecification_chainGraph`: the Ising potential (3.13) of `GibbsMeasure/Model/Ising.lean`
  is the homogeneous nearest-neighbour potential `φ₁ = -h σ`, `φ₂ = -J σ σ`.
* `isingChainDetFun`, `homogeneousNNDeterminingFun_ising`: **Georgii (3.14)**.
* `isingChainQ`, `detQ_isingChainDetFun`: Georgii's matrix `Q` for the Ising chain.
* `isingChainPerronRoot`, `isingChainPerronRoot_char`, `perronRoot_isingChainQ`:
  **Georgii (3.16)** — `q_{J,h} = e^{-h}(cosh h + sqrt(e^{-4J} + sinh² h))` is the
  Perron–Frobenius eigenvalue of `Q`.
* `isingChainP`, `matrixOfDetFun_isingChainDetFun`: **Georgii (3.17)** — formula (3.7) produces
  the transition matrix `P_{J,h}`.
* `isingSpecification_chainGraph_eq_markovSpecification`,
  `gibbsMeasure_isingSpecification_chainGraph`,
  `existsUnique_isGibbsMeasure_isingSpecification_chainGraph`: **Georgii (3.15)** —
  `𝒢(β Φ^{J,h}) = 𝒢(Φ^{βJ,βh}) = {μ_{βJ,βh}}`.
* `isingChainStationary`, `stationaryDist_isingChainP`: **Georgii (3.18)**.
* `integral_spin_stationaryChain_isingChainP`: **Georgii (3.19)** — the magnetisation
  `μ_{J,h}(σ_i) = sinh h / sqrt(e^{-4J} + sinh² h)`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

section Correspondence
open Finset Filter Topology Matrix

/-! ### The homogeneous nearest-neighbour potential of a matrix (Corollary (3.9)) -/

/-- The bond `{i, i+1}` determines `i`. -/
lemma pair_succ_inj {i j : ℤ} (h : ({i, i + 1} : Finset ℤ) = {j, j + 1}) : i = j := by
  have h1 : i ∈ ({j, j + 1} : Finset ℤ) := h ▸ Finset.mem_insert_self i {i + 1}
  have h2 : j ∈ ({i, i + 1} : Finset ℤ) := h.symm ▸ Finset.mem_insert_self j {j + 1}
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  omega

/-! ### The boundary of a finite volume (Georgii (3.4)) -/

/-- Georgii (3.4): the boundary `∂Λ = {i ∈ ℤ ∖ Λ : |i - j| = 1 for some j ∈ Λ}` of a finite
volume `Λ ⊆ ℤ`. -/
def boundary (Λ : Finset ℤ) : Finset ℤ := (Λ.image (· + 1) ∪ Λ.image (· - 1)) \ Λ

lemma mem_boundary {Λ : Finset ℤ} {i : ℤ} :
    i ∈ boundary Λ ↔ i ∉ Λ ∧ ∃ j ∈ Λ, |i - j| = 1 := by
  simp only [boundary, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩, hi⟩ <;>
      exact ⟨hi, j, hj, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩
  · rintro ⟨hi, j, hj, habs⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs
    refine ⟨?_, hi⟩
    rcases habs with h | h
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, hj, by omega⟩

lemma disjoint_boundary (Λ : Finset ℤ) : Disjoint Λ (boundary Λ) :=
  Finset.disjoint_sdiff

lemma succ_mem_union_boundary {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ Λ) :
    i + 1 ∈ Λ ∪ boundary Λ := by
  by_cases h : i + 1 ∈ Λ
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (mem_boundary.2 ⟨h, i, hi, by
      rw [show i + 1 - i = (1 : ℤ) by omega, abs_one]⟩)

lemma pred_mem_union_boundary {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ Λ) :
    i - 1 ∈ Λ ∪ boundary Λ := by
  by_cases h : i - 1 ∈ Λ
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (mem_boundary.2 ⟨h, i, hi, by
      rw [show i - 1 - i = (-1 : ℤ) by omega, abs_neg, abs_one]⟩)

/-- The boundary of an interval is the two-point set of Georgii (3.8)(1). -/
lemma boundary_Icc {a b : ℤ} (hab : a ≤ b) :
    boundary (Finset.Icc a b) = {a - 1, b + 1} := by
  ext i
  rw [mem_boundary]
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, j, hj, habs⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs
    omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, a, ⟨le_rfl, hab⟩, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩
    · exact ⟨by omega, b, ⟨hab, le_rfl⟩, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩

/-- The left endpoints of the bonds `{j, j + 1}` meeting a finite volume `Λ ⊆ ℤ`. -/
def bondsOf (Λ : Finset ℤ) : Finset ℤ := Λ ∪ Λ.image (· - 1)

lemma mem_bondsOf {Λ : Finset ℤ} {j : ℤ} : j ∈ bondsOf Λ ↔ j ∈ Λ ∨ j + 1 ∈ Λ := by
  simp only [bondsOf, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨k, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hk)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨j + 1, h, by omega⟩

lemma bondsOf_Icc {a b : ℤ} (hab : a ≤ b) :
    bondsOf (Finset.Icc a b) = Finset.Ico (a - 1) (b + 1) := by
  ext j
  rw [mem_bondsOf]
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

open Classical in
/-- Georgii, Corollary (3.9): the homogeneous nearest-neighbour potential of a matrix `P`:
`Φ_{{i,i+1}}(σ) = -log P(σ_i, σ_{i+1})`, and `Φ_A = 0` for every other `A`. -/
def markovPotential (P : Matrix E E ℝ) : Potential ℤ E := fun A σ ↦
  if h : ∃ i : ℤ, A = {i, i + 1} then -Real.log (P (σ h.choose) (σ (h.choose + 1))) else 0

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma markovPotential_pair (P : Matrix E E ℝ) (i : ℤ) (σ : ℤ → E) :
    markovPotential P {i, i + 1} σ = -Real.log (P (σ i) (σ (i + 1))) := by
  have h : ∃ j, ({i, i + 1} : Finset ℤ) = {j, j + 1} := ⟨i, rfl⟩
  have hi : i = h.choose := pair_succ_inj h.choose_spec
  simp only [markovPotential, dite_eq_left h]
  rw [← hi]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma markovPotential_of_not_pair (P : Matrix E E ℝ) {A : Finset ℤ} (h : ¬ ∃ i, A = {i, i + 1})
    (σ : ℤ → E) : markovPotential P A σ = 0 := by
  simp only [markovPotential, dite_eq_right h]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma exists_pair_of_markovPotential_ne_zero (P : Matrix E E ℝ) {A : Finset ℤ}
    (h : markovPotential P A ≠ 0) : ∃ i, A = {i, i + 1} := by
  by_contra hA
  exact h (funext fun σ ↦ markovPotential_of_not_pair P hA σ)

instance isPotential_markovPotential (P : Matrix E E ℝ) : (markovPotential P).IsPotential where
  measurable A := by
    by_cases h : ∃ i, A = {i, i + 1}
    · obtain ⟨i, rfl⟩ := h
      have hf : markovPotential P {i, i + 1} = fun σ ↦ -Real.log (P (σ i) (σ (i + 1))) :=
        funext fun σ ↦ markovPotential_pair P i σ
      rw [hf]
      have hi : Measurable[cylinderEvents (({i, i + 1} : Finset ℤ) : Set ℤ)]
          fun σ : ℤ → E ↦ σ i := measurable_cylinderEvent_apply (by simp)
      have hi1 : Measurable[cylinderEvents (({i, i + 1} : Finset ℤ) : Set ℤ)]
          fun σ : ℤ → E ↦ σ (i + 1) := measurable_cylinderEvent_apply (by simp)
      exact (measurable_of_finite (fun p : E × E ↦ -Real.log (P p.1 p.2))).comp
        (f := fun σ : ℤ → E ↦ (σ i, σ (i + 1))) (hi.prodMk hi1)
    · have hf : markovPotential P A = fun _ ↦ 0 := funext fun σ ↦ markovPotential_of_not_pair P h σ
      rw [hf]
      exact measurable_const

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- A nonzero interaction term containing `i` is a bond at `i`, hence lies in `Icc (i-1) (i+1)`. -/
lemma subset_Icc_of_markovPotential_ne_zero (P : Matrix E E ℝ) {i : ℤ} {A : Finset ℤ}
    (hiA : i ∈ A) (hΦ : markovPotential P A ≠ 0) : A ⊆ Finset.Icc (i - 1) (i + 1) := by
  obtain ⟨j, rfl⟩ := exists_pair_of_markovPotential_ne_zero P hΦ
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hiA hk
  simp only [Finset.mem_Icc]
  omega

instance isFiniteRange_markovPotential (P : Matrix E E ℝ) : (markovPotential P).IsFiniteRange :=
  ⟨fun i ↦ ⟨Finset.Icc (i - 1) (i + 1),
    fun _ hiA hΦ ↦ subset_Icc_of_markovPotential_ne_zero P hiA hΦ⟩⟩

/-- A uniform bound on the interaction terms of `markovPotential P`. -/
def logBound (P : Matrix E E ℝ) : ℝ := ∑ x, ∑ y, |Real.log (P x y)|

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma logBound_nonneg (P : Matrix E E ℝ) : 0 ≤ logBound P :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma abs_markovPotential_le (P : Matrix E E ℝ) (A : Finset ℤ) (σ : ℤ → E) :
    |markovPotential P A σ| ≤ logBound P := by
  by_cases h : ∃ i, A = {i, i + 1}
  · obtain ⟨i, rfl⟩ := h
    rw [markovPotential_pair, abs_neg]
    calc |Real.log (P (σ i) (σ (i + 1)))| ≤ ∑ y, |Real.log (P (σ i) y)| :=
          Finset.single_le_sum (f := fun y ↦ |Real.log (P (σ i) y)|) (fun _ _ ↦ abs_nonneg _)
            (Finset.mem_univ _)
      _ ≤ ∑ x, ∑ y, |Real.log (P x y)| :=
          Finset.single_le_sum (f := fun x ↦ ∑ y, |Real.log (P x y)|)
            (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)
  · rw [markovPotential_of_not_pair P h, abs_zero]
    exact logBound_nonneg P

instance isAbsolutelySummable_markovPotential (P : Matrix E E ℝ) :
    (markovPotential P).IsAbsolutelySummable := by
  refine ⟨fun i ↦ ?_⟩
  have hsupp : ∀ A : Finset ℤ, A ∉ (Finset.Icc (i - 1) (i + 1)).powerset →
      ({A : Finset ℤ | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖markovPotential P A η‖ₑ)) A = 0 := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | i ∈ A} from hiA)]
      have hΦ0 : markovPotential P A = 0 := by
        by_contra hΦ
        exact hA (subset_Icc_of_markovPotential_ne_zero P hiA hΦ)
      refine le_antisymm (iSup_le fun η ↦ ?_) zero_le
      simp [hΦ0]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | i ∈ A} from hiA) _
  have htsum : (markovPotential P).normAt i =
      ∑ A ∈ (Finset.Icc (i - 1) (i + 1)).powerset,
        ({A : Finset ℤ | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖markovPotential P A η‖ₑ)) A :=
    tsum_eq_sum hsupp
  rw [htsum]
  refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
  calc ({A : Finset ℤ | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖markovPotential P A η‖ₑ)) A
      ≤ ⨆ η, ‖markovPotential P A η‖ₑ := Set.indicator_le_self _ _ A
    _ ≤ ENNReal.ofReal (logBound P) := iSup_le fun η ↦ by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_markovPotential_le P A η)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The Gibbsian specification of `markovPotential P` (Georgii (3.6), Corollary (3.9)) for a
positive stochastic matrix `P`, with the uniform probability measure on `E` as reference measure
(Georgii's counting measure gives the same Gibbs measures by Remark (1.28)(3)). -/
def markovSpecification (P : Matrix E E ℝ) : Specification ℤ E :=
  Potential.gibbsSpecificationOfAbsolutelySummable (Φ := markovPotential P)
    (uniformOn (Set.univ : Set E)) 1

/-! ### Integrals against the independent kernel over finitely many sites -/

/-- The cylinder event `{σ_Λ = η_Λ}`. -/
def cyl (Λ : Finset ℤ) (η : ℤ → E) : Set (ℤ → E) := {σ | ∀ k ∈ Λ, σ k = η k}

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma mem_cyl {Λ : Finset ℤ} {η σ : ℤ → E} : σ ∈ cyl Λ η ↔ ∀ k ∈ Λ, σ k = η k := Iff.rfl

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma cyl_eq_pi (Λ : Finset ℤ) (η : ℤ → E) : cyl Λ η = (Λ : Set ℤ).pi fun k ↦ {η k} := by
  ext σ
  simp [cyl, Set.mem_pi]

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_cyl (Λ : Finset ℤ) (η : ℤ → E) : MeasurableSet (cyl Λ η) := by
  rw [cyl_eq_pi]
  exact measurableSet_finset_pi Λ _ fun _ ↦ measurableSet_singleton _

omit [DecidableEq E] [Nonempty E] in
lemma uniformOn_univ_singleton (x : E) :
    uniformOn (Set.univ : Set E) {x} = (Fintype.card E : ℝ≥0∞)⁻¹ := by
  rw [uniformOn_univ, Measure.count_singleton, one_div]

omit [DecidableEq E] in
/-- `∫⁻ f d(isssd ν Λ ω)` as a finite sum over the configurations in `Λ`. -/
lemma lintegral_isssd_eq_sum (Λ : Finset ℤ) (ω : ℤ → E) {f : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ σ, f σ ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω)
      = ∑ ζ : Λ → E, f (juxt (Λ : Set ℤ) ω ζ) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ Λ.card := by
  rw [show Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω
      = Measure.map (juxt (Λ : Set ℤ) ω) (Measure.pi fun _ : Λ ↦ uniformOn (Set.univ : Set E))
      from rfl, lintegral_map hf Measurable.juxt, lintegral_fintype]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  congr 1
  rw [← Set.univ_pi_singleton ζ, Measure.pi_pi]
  simp only [uniformOn_univ_singleton, Finset.prod_const, Finset.card_univ,
    Finset.coe_sort_coe, Fintype.card_coe]

omit [DecidableEq E] in
/-- The single-site independent kernel averages over the value at the site. -/
lemma lintegral_isssd_singleton (i : ℤ) (ω : ℤ → E) {f : (ℤ → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂(Specification.isssd (uniformOn (Set.univ : Set E)) {i} ω)
      = (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ y, f (Function.update ω i y) := by
  rw [lintegral_isssd_eq_sum _ _ hf, Finset.card_singleton, pow_one, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.funUnique (({i} : Finset ℤ)) E) _ _ fun ζ ↦ ?_
  rw [mul_comm]
  congr 2
  funext k
  by_cases hk : k = i
  · subst hk
    rw [juxt_apply_of_mem (by simp), Function.update_self]
    rfl
  · rw [juxt_apply_of_not_mem (by simpa using hk), Function.update_of_ne hk]

omit [DecidableEq E] in
/-- Configurations in the support of `isssd ν Λ ω` agree with `ω` off `Λ`. -/
lemma lintegral_isssd_congr (Λ : Finset ℤ) (ω : ℤ → E) {f g : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (h : ∀ σ, (∀ k ∉ Λ, σ k = ω k) → f σ = g σ) :
    ∫⁻ σ, f σ ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω)
      = ∫⁻ σ, g σ ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω) := by
  rw [lintegral_isssd_eq_sum _ _ hf, lintegral_isssd_eq_sum _ _ hg]
  exact Finset.sum_congr rfl fun ζ _ ↦ by rw [h _ (juxt_agree_on_compl Λ ω ζ)]

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- The independent kernel only depends on the boundary condition off `Λ`. -/
lemma isssd_congr (Λ : Finset ℤ) {ω ω' : ℤ → E} (h : ∀ k ∉ Λ, ω' k = ω k) :
    Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω'
      = Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω := by
  rw [show Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω'
      = Measure.map (juxt (Λ : Set ℤ) ω') (Measure.pi fun _ : Λ ↦ uniformOn (Set.univ : Set E))
      from rfl, show Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω
      = Measure.map (juxt (Λ : Set ℤ) ω) (Measure.pi fun _ : Λ ↦ uniformOn (Set.univ : Set E))
      from rfl]
  congr 1
  funext ζ k
  by_cases hk : k ∈ Λ
  · rw [juxt_apply_of_mem (by simpa using hk), juxt_apply_of_mem (by simpa using hk)]
  · rw [juxt_apply_of_not_mem (by simpa using hk), juxt_apply_of_not_mem (by simpa using hk),
      h k hk]

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Strong consistency of the independent specification: adding a site. -/
lemma isssd_insert (i : ℤ) (Λ : Finset ℤ) (ω : ℤ → E) :
    Specification.isssd (uniformOn (Set.univ : Set E)) (insert i Λ) ω
      = (Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω).bind
          (Specification.isssd (uniformOn (Set.univ : Set E)) {i}) := by
  rw [Finset.insert_eq]
  exact (IsStronglyConsistent.bind_eq (Specification.isStronglyConsistent_isssd _) {i} Λ ω).symm

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Strong consistency of the independent specification: splitting the volume. -/
lemma isssd_union (Λ₁ Λ₂ : Finset ℤ) (ω : ℤ → E) :
    Specification.isssd (uniformOn (Set.univ : Set E)) (Λ₁ ∪ Λ₂) ω
      = (Specification.isssd (uniformOn (Set.univ : Set E)) Λ₂ ω).bind
          (Specification.isssd (uniformOn (Set.univ : Set E)) Λ₁) :=
  (IsStronglyConsistent.bind_eq (Specification.isStronglyConsistent_isssd _) Λ₁ Λ₂ ω).symm

omit [DecidableEq E] [MeasurableSingletonClass E] in
lemma measurable_isssd (Λ : Finset ℤ) :
    Measurable (Specification.isssd (uniformOn (Set.univ : Set E)) Λ) :=
  (Specification.isssd (uniformOn (Set.univ : Set E)) Λ).measurable.mono cylinderEvents_le_pi
    le_rfl

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- `Measure.lintegral_bind` for the independent kernels. -/
lemma lintegral_isssd_bind (Λ₁ Λ₂ : Finset ℤ) (ω : ℤ → E) {f : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ σ, f σ ∂((Specification.isssd (uniformOn (Set.univ : Set E)) Λ₂ ω).bind
        (Specification.isssd (uniformOn (Set.univ : Set E)) Λ₁))
      = ∫⁻ σ, ∫⁻ σ', f σ' ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ₁ σ)
          ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ₂ ω) :=
  Measure.lintegral_bind (measurable_isssd Λ₁).aemeasurable hf.aemeasurable


/-! ### Path weights of a matrix -/

variable {P : Matrix E E ℝ}

/-- The product of transition weights along the bonds `{j, j+1}`, `a ≤ j < c`. -/
def pathWeight (P : Matrix E E ℝ) (a c : ℤ) (σ : ℤ → E) : ℝ :=
  ∏ j ∈ Finset.Ico a c, P (σ j) (σ (j + 1))

@[simp] lemma pathWeight_self (a : ℤ) (σ : ℤ → E) : pathWeight P a a σ = 1 := by
  simp [pathWeight]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_of_le {a c : ℤ} (h : c ≤ a) (σ : ℤ → E) : pathWeight P a c σ = 1 := by
  rw [pathWeight, Finset.Ico_eq_empty (by omega), Finset.prod_empty]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_single (a : ℤ) (σ : ℤ → E) :
    pathWeight P a (a + 1) σ = P (σ a) (σ (a + 1)) := by
  rw [pathWeight, show Finset.Ico a (a + 1) = {a} by ext k; simp; omega, Finset.prod_singleton]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_pair {a c : ℤ} (h : c = a + 1) (σ : ℤ → E) :
    pathWeight P a c σ = P (σ a) (σ c) := by
  subst h
  exact pathWeight_single a σ

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_split {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (σ : ℤ → E) :
    pathWeight P a c σ = pathWeight P a b σ * pathWeight P b c σ := by
  rw [pathWeight, ← Finset.Ico_union_Ico_eq_Ico hab hbc,
    Finset.prod_union (Finset.Ico_disjoint_Ico_consecutive a b c)]
  rfl

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_succ_top {a c : ℤ} (h : a ≤ c) (σ : ℤ → E) :
    pathWeight P a (c + 1) σ = pathWeight P a c σ * P (σ c) (σ (c + 1)) := by
  rw [pathWeight_split h (by omega), pathWeight_single]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_congr {a c : ℤ} {σ σ' : ℤ → E} (h : ∀ k ∈ Finset.Icc a c, σ k = σ' k) :
    pathWeight P a c σ = pathWeight P a c σ' := by
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Ico] at hj
  rw [h j (Finset.mem_Icc.2 (by omega)), h (j + 1) (Finset.mem_Icc.2 (by omega))]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_nonneg (hpos : ∀ x y, 0 < P x y) (a c : ℤ) (σ : ℤ → E) :
    0 ≤ pathWeight P a c σ :=
  Finset.prod_nonneg fun _ _ ↦ (hpos _ _).le

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_pos (hpos : ∀ x y, 0 < P x y) (a c : ℤ) (σ : ℤ → E) :
    0 < pathWeight P a c σ :=
  Finset.prod_pos fun _ _ ↦ hpos _ _

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pathWeight_le_one (hP : P ∈ Matrix.rowStochastic ℝ E)
    (a c : ℤ) (σ : ℤ → E) : pathWeight P a c σ ≤ 1 :=
  Finset.prod_le_one (fun _ _ ↦ Matrix.nonneg_of_mem_rowStochastic hP)
    (fun _ _ ↦ Matrix.le_one_of_mem_rowStochastic hP)

omit [DecidableEq E] [Nonempty E] in
lemma measurable_pathWeight (P : Matrix E E ℝ) (a c : ℤ) :
    Measurable fun σ : ℤ → E ↦ pathWeight P a c σ :=
  Finset.measurable_prod _ fun j _ ↦
    (measurable_of_finite (fun p : E × E ↦ P p.1 p.2)).comp
      (f := fun σ : ℤ → E ↦ (σ j, σ (j + 1)))
      ((measurable_pi_apply j).prodMk (measurable_pi_apply (j + 1)))

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Entries of positive powers of an entrywise positive matrix are positive. -/
lemma pow_apply_pos (hpos : ∀ x y, 0 < P x y) : ∀ (n : ℕ) (x y : E), 0 < (P ^ (n + 1)) x y := by
  intro n
  induction n with
  | zero => simpa using hpos
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_pos (fun z _ ↦ mul_pos (ih x z) (hpos z y)) Finset.univ_nonempty

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma sum_pow_mul (P : Matrix E E ℝ) (m : ℕ) (x y : E) :
    ∑ z, (P ^ m) x z * P z y = (P ^ (m + 1)) x y := by
  rw [pow_succ, Matrix.mul_apply]

/-! ### The Hamiltonian and Boltzmann factor of a finite volume -/

/-- The bond `{i, i + 1}` meets `Λ` when `i ∈ bondsOf Λ`. -/
lemma not_disjoint_pair_bondsOf {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ bondsOf Λ) :
    ¬ Disjoint ({i, i + 1} : Finset ℤ) Λ := by
  rw [Finset.not_disjoint_iff]
  rcases mem_bondsOf.1 hi with h | h
  · exact ⟨i, by simp, h⟩
  · exact ⟨i + 1, by simp, h⟩

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Hamiltonian of `markovPotential P` on a finite volume `Λ` is the sum of the bond
energies `-log P(σ_j, σ_{j+1})` over the bonds meeting `Λ`. -/
lemma hamiltonian_eq_sum_bondsOf (P : Matrix E E ℝ) (Λ : Finset ℤ) (σ : ℤ → E) :
    (markovPotential P).hamiltonian Λ σ
      = ∑ j ∈ bondsOf Λ, -Real.log (P (σ j) (σ (j + 1))) := by
  rw [Potential.hamiltonian_eq_tsum,
    tsum_eq_sum (s := (bondsOf Λ).image fun i ↦ ({i, i + 1} : Finset ℤ)) (fun A hA ↦ ?_)]
  · rw [Finset.sum_image fun i _ j _ h ↦ pair_succ_inj h]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Potential.hamiltonianTerms_of_not_disjoint (not_disjoint_pair_bondsOf hi),
      markovPotential_pair]
  · by_cases hd : Disjoint A Λ
    · exact Potential.hamiltonianTerms_of_disjoint hd σ
    · rw [Potential.hamiltonianTerms_of_not_disjoint hd]
      by_cases hpair : ∃ i, A = {i, i + 1}
      · obtain ⟨i, rfl⟩ := hpair
        exfalso
        refine hA (Finset.mem_image.2 ⟨i, mem_bondsOf.2 ?_, rfl⟩)
        obtain ⟨k, hk1, hk2⟩ := Finset.not_disjoint_iff.1 hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk1
        rcases hk1 with rfl | rfl
        · exact Or.inl hk2
        · exact Or.inr hk2
      · exact markovPotential_of_not_pair P hpair σ

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Hamiltonian of `markovPotential P` on the interval `[a, a+n]` is the sum of the bond
energies `-log P(σ_j, σ_{j+1})`, `a - 1 ≤ j ≤ a + n`. -/
lemma hamiltonian_Icc (P : Matrix E E ℝ) (a : ℤ) (n : ℕ) (σ : ℤ → E) :
    (markovPotential P).hamiltonian (Finset.Icc a (a + n)) σ
      = ∑ j ∈ Finset.Ico (a - 1) (a + n + 1), -Real.log (P (σ j) (σ (j + 1))) := by
  rw [hamiltonian_eq_sum_bondsOf, bondsOf_Icc (by omega : a ≤ a + (n : ℤ))]

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Boltzmann factor of `markovPotential P` on a finite volume `Λ` is the product of the
transition weights over the bonds meeting `Λ`. -/
lemma boltzmannFactor_eq_prod_bondsOf (hpos : ∀ x y, 0 < P x y) (Λ : Finset ℤ) (σ : ℤ → E) :
    (markovPotential P).boltzmannFactor 1 Λ σ
      = ENNReal.ofReal (∏ j ∈ bondsOf Λ, P (σ j) (σ (j + 1))) := by
  rw [Potential.boltzmannFactor, hamiltonian_eq_sum_bondsOf]
  congr 1
  rw [show -(1 : ℝ) * ∑ j ∈ bondsOf Λ, -Real.log (P (σ j) (σ (j + 1)))
      = ∑ j ∈ bondsOf Λ, Real.log (P (σ j) (σ (j + 1))) by
    rw [neg_one_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ neg_neg _]
  rw [Real.exp_sum]
  exact Finset.prod_congr rfl fun j _ ↦ Real.exp_log (hpos _ _)

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Boltzmann factor of `markovPotential P` on `[a, a+n]` is the path weight. -/
lemma boltzmannFactor_Icc (hpos : ∀ x y, 0 < P x y) (a : ℤ) (n : ℕ) (σ : ℤ → E) :
    (markovPotential P).boltzmannFactor 1 (Finset.Icc a (a + n)) σ
      = ENNReal.ofReal (pathWeight P (a - 1) (a + n + 1) σ) := by
  rw [boltzmannFactor_eq_prod_bondsOf hpos, bondsOf_Icc (by omega : a ≤ a + (n : ℤ)), pathWeight]



/-! ### The master integral: path weights against the independent kernel -/

omit [DecidableEq E] [Nonempty E] in
/-- Boundary-decorated path weights are measurable in the configuration. -/
lemma measurable_ofReal_pathWeight (P : Matrix E E ℝ) (x : E) (g : E → ℝ) (d u v c : ℤ) :
    Measurable fun σ : ℤ → E ↦
      ENNReal.ofReal (P x (σ d) * pathWeight P u v σ * g (σ c)) :=
  ((((measurable_of_finite (fun e : E ↦ P x e)).comp (measurable_pi_apply d)).mul
      (measurable_pathWeight P u v)).mul
    ((measurable_of_finite g).comp (measurable_pi_apply c))).ennreal_ofReal

/-- Integrating a path weight with boundary decorations over the independent kernel on `[a, b]`,
`b = a + n`, contracts the path into a matrix power (the engine behind Comment (3.8)(1)). -/
lemma lintegral_isssd_pathWeight (hpos : ∀ x y, 0 < P x y) :
    ∀ (n : ℕ) (a b : ℤ), b = a + n → ∀ (x : E) (g : E → ℝ), (∀ z, 0 ≤ g z) → ∀ ω : ℤ → E,
    ∫⁻ σ, ENNReal.ofReal (P x (σ a) * pathWeight P a b σ * g (σ b))
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc a b) ω)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (n + 1)
          * ENNReal.ofReal (∑ z, (P ^ (n + 1)) x z * g z) := by
  -- Induction on the length `n` of the interval. The successor step splits off the top site
  -- `a + n + 1` and integrates it out, which replaces `g` by `G w = ∑ z, P w z * g z`; the
  -- induction hypothesis on `[a, a + n]` then raises the matrix power by one.
  intro n
  induction n with
  | zero =>
    intro a b hb x g hg ω
    have hb' : a = b := by omega
    subst hb'
    rw [Finset.Icc_self,
      lintegral_isssd_singleton a ω (measurable_ofReal_pathWeight P x g a a a a)]
    have hterm : ∀ y : E,
        ENNReal.ofReal (P x ((Function.update ω a y) a) * pathWeight P a a (Function.update ω a y)
            * g ((Function.update ω a y) a))
          = ENNReal.ofReal (P x y * g y) := by
      intro y
      rw [Function.update_self, pathWeight_self, mul_one]
    rw [Fintype.sum_congr _ _ hterm,
      ← ENNReal.ofReal_sum_of_nonneg fun z _ ↦ mul_nonneg (hpos _ _).le (hg z)]
    simp only [zero_add, pow_one]
  | succ n ih =>
    intro a b hb x g hg ω
    have hb' : b = a + (n : ℤ) + 1 := by omega
    clear hb
    subst hb'
    set G : E → ℝ := fun w ↦ ∑ z, P w z * g z with hGdef
    have hG : ∀ w, 0 ≤ G w := fun w ↦
      Finset.sum_nonneg fun z _ ↦ mul_nonneg (hpos _ _).le (hg z)
    have hins : Finset.Icc a (a + (n : ℤ) + 1)
        = insert (a + (n : ℤ) + 1) (Finset.Icc a (a + (n : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hins, isssd_insert, lintegral_isssd_bind _ _ _
      (measurable_ofReal_pathWeight P x g a a (a + (n : ℤ) + 1) (a + (n : ℤ) + 1))]
    have hinner : ∀ σ : ℤ → E,
        ∫⁻ σ', ENNReal.ofReal
            (P x (σ' a) * pathWeight P a (a + (n : ℤ) + 1) σ' * g (σ' (a + (n : ℤ) + 1)))
          ∂(Specification.isssd (uniformOn (Set.univ : Set E)) {a + (n : ℤ) + 1} σ)
        = (Fintype.card E : ℝ≥0∞)⁻¹
            * ENNReal.ofReal (P x (σ a) * pathWeight P a (a + (n : ℤ)) σ * G (σ (a + (n : ℤ)))) := by
      intro σ
      rw [lintegral_isssd_singleton _ σ
        (measurable_ofReal_pathWeight P x g a a (a + (n : ℤ) + 1) (a + (n : ℤ) + 1))]
      congr 1
      have hterm : ∀ z : E,
          ENNReal.ofReal (P x ((Function.update σ (a + (n : ℤ) + 1) z) a)
              * pathWeight P a (a + (n : ℤ) + 1) (Function.update σ (a + (n : ℤ) + 1) z)
              * g ((Function.update σ (a + (n : ℤ) + 1) z) (a + (n : ℤ) + 1)))
            = ENNReal.ofReal (P x (σ a) * pathWeight P a (a + (n : ℤ)) σ
                * (P (σ (a + (n : ℤ))) z * g z)) := by
        intro z
        congr 1
        rw [Function.update_of_ne (by omega), Function.update_self,
          pathWeight_succ_top (by omega),
          Function.update_of_ne (by omega : a + (n : ℤ) ≠ a + (n : ℤ) + 1),
          Function.update_self,
          pathWeight_congr (σ' := σ) fun k hk ↦ Function.update_of_ne
            (by rw [Finset.mem_Icc] at hk; omega) _ _]
        ring
      rw [Fintype.sum_congr _ _ hterm,
        ← ENNReal.ofReal_sum_of_nonneg fun z _ ↦
          mul_nonneg (mul_nonneg (hpos _ _).le (pathWeight_nonneg hpos _ _ _))
            (mul_nonneg (hpos _ _).le (hg z))]
      simp only [hGdef, ← Finset.mul_sum]
    rw [lintegral_congr hinner,
      lintegral_const_mul _ (measurable_ofReal_pathWeight P x G a a (a + (n : ℤ)) (a + (n : ℤ))),
      ih a (a + (n : ℤ)) rfl x G hG ω, ← mul_assoc, ← pow_succ']
    congr 2
    calc ∑ w, (P ^ (n + 1)) x w * G w
        = ∑ w, ∑ z, (P ^ (n + 1)) x w * (P w z * g z) := by
          simp only [hGdef, Finset.mul_sum]
      _ = ∑ z, ∑ w, (P ^ (n + 1)) x w * (P w z * g z) := Finset.sum_comm
      _ = ∑ z, (P ^ (n + 1 + 1)) x z * g z := by
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          rw [← sum_pow_mul P (n + 1) x z, Finset.sum_mul]
          exact Finset.sum_congr rfl fun w _ ↦ by ring

/-! ### The partition function on an interval -/

/-- The partition function of `markovPotential P` on `[a, b]`, `b = a + n`, is the matrix element
`(P^{n+2})(ω_{a-1}, ω_{b+1})` up to the volume factor of the uniform reference measure. -/
lemma premodifierZ_Icc (hpos : ∀ x y, 0 < P x y) {n : ℕ} {a b : ℤ} (hb : b = a + n)
    (ω : ℤ → E) :
    Specification.premodifierZ (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1) (Finset.Icc a b) ω
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (n + 1)
          * ENNReal.ofReal ((P ^ (n + 2)) (ω (a - 1)) (ω (b + 1))) := by
  have hcongr : ∀ σ : ℤ → E, (∀ k ∉ Finset.Icc a b, σ k = ω k) →
      (markovPotential P).boltzmannFactor 1 (Finset.Icc a b) σ
        = ENNReal.ofReal (P (ω (a - 1)) (σ a) * pathWeight P a b σ * P (σ b) (ω (b + 1))) := by
    intro σ hσ
    rw [show Finset.Icc a b = Finset.Icc a (a + (n : ℤ)) by rw [hb],
      boltzmannFactor_Icc hpos, show a + (n : ℤ) = b by omega,
      pathWeight_split (show a - 1 ≤ a by omega) (show a ≤ b + 1 by omega),
      pathWeight_split (show a ≤ b by omega) (show b ≤ b + 1 by omega),
      pathWeight_pair (show a = (a - 1) + 1 by omega),
      pathWeight_pair (show b + 1 = b + 1 by rfl),
      hσ (a - 1) (by simp only [Finset.mem_Icc]; omega),
      hσ (b + 1) (by simp only [Finset.mem_Icc]; omega)]
    congr 1
    ring
  rw [Specification.premodifierZ, Specification.relZ,
    lintegral_isssd_congr _ _ (Potential.measurable_boltzmannFactor 1 _)
      (measurable_ofReal_pathWeight P (ω (a - 1)) (fun z ↦ P z (ω (b + 1))) a a b b) hcongr]
  have hkey := lintegral_isssd_pathWeight hpos n a b hb (ω (a - 1))
    (fun z ↦ P z (ω (b + 1))) (fun z ↦ (hpos _ _).le) ω
  rw [hkey]
  congr 2

/-! ### Integrals over a single matching configuration -/

/-- The configuration equal to `ζ` on `Λ` and to `σ` elsewhere — `Finset.piecewise`. -/
abbrev overwrite (Λ : Finset ℤ) (ζ σ : ℤ → E) : ℤ → E := Λ.piecewise ζ σ

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma overwrite_apply_of_mem {Λ : Finset ℤ} {k : ℤ} (hk : k ∈ Λ) (ζ σ : ℤ → E) :
    overwrite Λ ζ σ k = ζ k := Λ.piecewise_eq_of_mem _ _ hk

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma overwrite_apply_of_notMem {Λ : Finset ℤ} {k : ℤ} (hk : k ∉ Λ) (ζ σ : ℤ → E) :
    overwrite Λ ζ σ k = σ k := Λ.piecewise_eq_of_notMem _ _ hk

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Cylinders over disjoint volumes intersect in the cylinder of the overwritten
configuration. -/
lemma cyl_inter_cyl {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint Λ₁ Λ₂) (ω ζ : ℤ → E) :
    cyl Λ₁ ω ∩ cyl Λ₂ ζ = cyl (Λ₁ ∪ Λ₂) (overwrite Λ₂ ζ ω) := by
  ext σ
  simp only [Set.mem_inter_iff, mem_cyl, Finset.mem_union]
  constructor
  · rintro ⟨h₁, h₂⟩ k hk
    rcases hk with hk | hk
    · rw [overwrite_apply_of_notMem (Finset.disjoint_left.1 h hk)]
      exact h₁ k hk
    · rw [overwrite_apply_of_mem hk]
      exact h₂ k hk
  · intro hσ
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · have := hσ k (Or.inl hk)
      rwa [overwrite_apply_of_notMem (Finset.disjoint_left.1 h hk)] at this
    · have := hσ k (Or.inr hk)
      rwa [overwrite_apply_of_mem hk] at this

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Overwriting on `Λ` only reads the base configuration off `Λ`. -/
lemma overwrite_juxt (Λ : Finset ℤ) (ζ ω : ℤ → E) (ξ : Λ → E) :
    overwrite Λ ζ (juxt (Λ : Set ℤ) ω ξ) = overwrite Λ ζ ω := by
  funext k
  by_cases hk : k ∈ Λ
  · rw [overwrite_apply_of_mem hk, overwrite_apply_of_mem hk]
  · rw [overwrite_apply_of_notMem hk, overwrite_apply_of_notMem hk,
      juxt_apply_of_not_mem (by simpa using hk)]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `juxt` commutes with updating a site outside the pinned volume: `_root_.juxt_update_of_notMem`
at `S = ℤ`. -/
lemma juxt_update_of_notMem {Γ : Finset ℤ} {i : ℤ} (hi : i ∉ Γ) (τ : ℤ → E) (y : E)
    (ξ : Γ → E) :
    juxt (Γ : Set ℤ) (Function.update τ i y) ξ
      = Function.update (juxt (Γ : Set ℤ) τ ξ) i y :=
  _root_.juxt_update_of_notMem (by simpa using hi) τ y ξ
omit [DecidableEq E] in
/-- Only the configuration matching `ζ` on `Λ` contributes to an integral over `cyl Λ ζ`. -/
lemma lintegral_isssd_indicator_cyl (Λ : Finset ℤ) (ζ σ₀ : ℤ → E) {f : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ σ, (cyl Λ ζ).indicator f σ
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ σ₀)
      = f (overwrite Λ ζ σ₀) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ Λ.card := by
  rw [lintegral_isssd_eq_sum Λ σ₀ (hf.indicator (measurableSet_cyl Λ ζ))]
  refine Eq.trans (Fintype.sum_eq_single (fun k : (Λ : Set ℤ) ↦ ζ k.1) fun ξ hξ ↦ ?_) ?_
  · rw [Set.indicator_of_notMem, zero_mul]
    intro hmem
    refine hξ (funext fun k ↦ ?_)
    have := hmem k.1 (by simpa using k.2)
    rwa [juxt_apply_of_mem k.2] at this
  · have hjuxt : juxt (Λ : Set ℤ) σ₀ (fun k : (Λ : Set ℤ) ↦ ζ k.1) = overwrite Λ ζ σ₀ := by
      funext k
      by_cases hk : k ∈ Λ
      · rw [juxt_apply_of_mem (by simpa using hk), overwrite_apply_of_mem hk]
      · rw [juxt_apply_of_not_mem (by simpa using hk), overwrite_apply_of_notMem hk]
    rw [hjuxt, Set.indicator_of_mem]
    intro k hk
    rw [overwrite_apply_of_mem hk]

omit [DecidableEq E] in
/-- Evaluating `markovSpecification` on a `𝓕`-event: unnormalised Boltzmann integral over the
event, divided by the partition function at the boundary condition. -/
lemma markovSpecification_apply_eq (Λ : Finset ℤ) (ω : ℤ → E)
    {A : Set (ℤ → E)} (hA : MeasurableSet A) :
    markovSpecification P Λ ω A
      = (∫⁻ σ, A.indicator ((markovPotential P).boltzmannFactor 1 Λ) σ
            ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω))
        * (Specification.premodifierZ (uniformOn (Set.univ : Set E))
            ((markovPotential P).boltzmannFactor 1) Λ ω)⁻¹ := by
  have hb : Measurable ((markovPotential P).boltzmannFactor 1 Λ) :=
    Potential.measurable_boltzmannFactor 1 Λ
  have hZ : Measurable (Specification.premodifierZ (uniformOn (Set.univ : Set E))
      ((markovPotential P).boltzmannFactor 1) Λ) :=
    (Specification.measurable_relZ (γ := Specification.isssd (uniformOn (Set.univ : Set E)))
      (Potential.isPremodifier_boltzmannFactor 1).measurable Λ).mono
      cylinderEvents_le_pi le_rfl
  have happly : markovSpecification P Λ ω A
      = ∫⁻ σ, A.indicator (fun σ' ↦ (markovPotential P).boltzmannFactor 1 Λ σ'
          / Specification.premodifierZ (uniformOn (Set.univ : Set E))
              ((markovPotential P).boltzmannFactor 1) Λ σ') σ
          ∂(Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω) := by
    rw [show markovSpecification P Λ ω
        = (Specification.isssd (uniformOn (Set.univ : Set E)) Λ ω).withDensity
            (Specification.premodifierNorm (uniformOn (Set.univ : Set E))
              ((markovPotential P).boltzmannFactor 1) Λ) from rfl,
      withDensity_apply _ hA, ← lintegral_indicator hA]
    rfl
  have hcong := lintegral_isssd_congr Λ ω
    (f := fun σ ↦ A.indicator (fun σ' ↦ (markovPotential P).boltzmannFactor 1 Λ σ'
      / Specification.premodifierZ (uniformOn (Set.univ : Set E))
          ((markovPotential P).boltzmannFactor 1) Λ σ') σ)
    (g := fun σ ↦ A.indicator ((markovPotential P).boltzmannFactor 1 Λ) σ
      * (Specification.premodifierZ (uniformOn (Set.univ : Set E))
          ((markovPotential P).boltzmannFactor 1) Λ ω)⁻¹)
    ((hb.div hZ).indicator hA) ((hb.indicator hA).mul_const _) (fun σ hσ ↦ ?_)
  · rw [happly, hcong, lintegral_mul_const _ (hb.indicator hA)]
  · have hZconst : Specification.premodifierZ (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1) Λ σ
        = Specification.premodifierZ (uniformOn (Set.univ : Set E))
            ((markovPotential P).boltzmannFactor 1) Λ ω := by
      rw [Specification.premodifierZ, Specification.premodifierZ, Specification.relZ,
        Specification.relZ, isssd_congr Λ hσ]
    by_cases hmem : σ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hZconst, div_eq_mul_inv]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]

/-! ### The finite-volume formula on an interval (Comment (3.8)(1), single block) -/

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma card_inv_ne_zero : ((Fintype.card E : ℝ≥0∞))⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma card_inv_ne_top : ((Fintype.card E : ℝ≥0∞))⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.2 (by simpa using Fintype.card_ne_zero (α := E))

/-- Cancellation `(x c) (c y)⁻¹ = x y⁻¹` in `ℝ≥0∞` for `c ≠ 0, ⊤`. -/
lemma mul_mul_inv_cancel {x y c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    (x * c) * (c * y)⁻¹ = x * y⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop),
    show x * c * (c⁻¹ * y⁻¹) = x * y⁻¹ * (c * c⁻¹) by ring,
    ENNReal.mul_inv_cancel hc0 hctop, mul_one]

/-- **Georgii, Comment (3.8)(1), single interval.** The `markovSpecification` of an interval
cylinder pinned on the whole interval `[a, b]`, `b = a + n`: the product of the transition
weights along `[a-1, b+1]`, normalised by `(P^{n+2})(ω_{a-1}, ω_{b+1})`. -/
theorem markovSpecification_Icc_apply_cyl (hpos : ∀ x y, 0 < P x y) {n : ℕ} {a b : ℤ}
    (hb : b = a + n) (ω η : ℤ → E) (hη : ∀ k ∉ Finset.Icc a b, η k = ω k) :
    markovSpecification P (Finset.Icc a b) ω (cyl (Finset.Icc a b) η)
      = ENNReal.ofReal (pathWeight P (a - 1) (b + 1) η
          / (P ^ (n + 2)) (ω (a - 1)) (ω (b + 1))) := by
  have hover : overwrite (Finset.Icc a b) η ω = η := by
    funext k
    by_cases hk : k ∈ Finset.Icc a b
    · rw [overwrite_apply_of_mem hk]
    · rw [overwrite_apply_of_notMem hk, hη k hk]
  have hcard : (Finset.Icc a b).card = n + 1 := by
    rw [Int.card_Icc]
    omega
  rw [markovSpecification_apply_eq _ ω (measurableSet_cyl _ _),
    lintegral_isssd_indicator_cyl _ _ _ (Potential.measurable_boltzmannFactor 1 _),
    premodifierZ_Icc hpos hb ω, hover, hcard,
    show Finset.Icc a b = Finset.Icc a (a + (n : ℤ)) by rw [hb],
    boltzmannFactor_Icc hpos, show a + (n : ℤ) = b by omega,
    mul_mul_inv_cancel (pow_ne_zero _ card_inv_ne_zero) (ENNReal.pow_ne_top card_inv_ne_top),
    ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (pow_apply_pos hpos (n + 1) _ _)]

/-! ### Block integrals for the interval-in-interval formula -/

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma measurable_update_left (l : ℤ) (c : E) :
    Measurable fun σ : ℤ → E ↦ Function.update σ l c := by
  refine measurable_pi_iff.2 fun k ↦ ?_
  by_cases hk : k = l
  · subst hk
    simp only [Function.update_self]
    exact measurable_const
  · simp only [Function.update_of_ne hk]
    exact measurable_pi_apply k

omit [DecidableEq E] [Nonempty E] in
lemma measurable_ofReal_pathWeight_update (P : Matrix E E ℝ) (u v l : ℤ) (c : E) :
    Measurable fun σ : ℤ → E ↦ ENNReal.ofReal (pathWeight P u v (Function.update σ l c)) :=
  ((measurable_pathWeight P u v).comp (measurable_update_left l c)).ennreal_ofReal

/-- Left-block integral: summing the configurations on `[a, l-1]`, `l - 1 = a + p`, against a path
pinned to `ζ l` at `l` yields `(P^{p+2})(ω_{a-1}, ζ_l)`. -/
lemma lintegral_isssd_left_block (hpos : ∀ x y, 0 < P x y) {p : ℕ} {a l : ℤ}
    (hl : l - 1 = a + p) (ζ ω : ℤ → E) :
    ∫⁻ σ, ENNReal.ofReal (pathWeight P (a - 1) l (Function.update σ l (ζ l)))
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc a (l - 1)) ω)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1)
          * ENNReal.ofReal ((P ^ (p + 2)) (ω (a - 1)) (ζ l)) := by
  have hcongr : ∀ σ : ℤ → E, (∀ k ∉ Finset.Icc a (l - 1), σ k = ω k) →
      ENNReal.ofReal (pathWeight P (a - 1) l (Function.update σ l (ζ l)))
        = ENNReal.ofReal (P (ω (a - 1)) (σ a) * pathWeight P a (l - 1) σ * P (σ (l - 1)) (ζ l)) := by
    intro σ hσ
    rw [pathWeight_split (show a - 1 ≤ a by omega) (show a ≤ l by omega),
      pathWeight_split (show a ≤ l - 1 by omega) (show l - 1 ≤ l by omega),
      pathWeight_pair (show a = (a - 1) + 1 by omega),
      pathWeight_pair (show l = (l - 1) + 1 by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self,
      pathWeight_congr (σ' := σ) fun k hk ↦ Function.update_of_ne
        (by rw [Finset.mem_Icc] at hk; omega) _ _,
      hσ (a - 1) (by simp only [Finset.mem_Icc]; omega)]
    congr 1
    ring
  rw [lintegral_isssd_congr _ _ (measurable_ofReal_pathWeight_update P (a - 1) l l (ζ l))
      (measurable_ofReal_pathWeight P (ω (a - 1)) (fun z ↦ P z (ζ l)) a a (l - 1) (l - 1)) hcongr]
  have hkey := lintegral_isssd_pathWeight hpos p a (l - 1) hl (ω (a - 1))
    (fun z ↦ P z (ζ l)) (fun z ↦ (hpos _ _).le) ω
  rw [hkey]
  congr 2

/-- Right-block integral: summing the configurations on `[m+1, b]`, `b = m + 1 + q`, against a
path pinned to `ζ m` at `m` yields `(P^{q+2})(ζ_m, ω_{b+1})`. -/
lemma lintegral_isssd_right_block (hpos : ∀ x y, 0 < P x y) {q : ℕ} {m b : ℤ}
    (hb : b = m + 1 + q) (ζ ω : ℤ → E) :
    ∫⁻ σ, ENNReal.ofReal (pathWeight P m (b + 1) (Function.update σ m (ζ m)))
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc (m + 1) b) ω)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
          * ENNReal.ofReal ((P ^ (q + 2)) (ζ m) (ω (b + 1))) := by
  have hcongr : ∀ σ : ℤ → E, (∀ k ∉ Finset.Icc (m + 1) b, σ k = ω k) →
      ENNReal.ofReal (pathWeight P m (b + 1) (Function.update σ m (ζ m)))
        = ENNReal.ofReal (P (ζ m) (σ (m + 1)) * pathWeight P (m + 1) b σ
            * P (σ b) (ω (b + 1))) := by
    intro σ hσ
    rw [pathWeight_split (show m ≤ m + 1 by omega) (show m + 1 ≤ b + 1 by omega),
      pathWeight_split (show m + 1 ≤ b by omega) (show b ≤ b + 1 by omega),
      pathWeight_single m, pathWeight_pair (show b + 1 = b + 1 from rfl),
      Function.update_self, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      pathWeight_congr (σ' := σ) fun k hk ↦ Function.update_of_ne
        (by rw [Finset.mem_Icc] at hk; omega) _ _,
      hσ (b + 1) (by simp only [Finset.mem_Icc]; omega)]
    congr 1
    ring
  rw [lintegral_isssd_congr _ _ (measurable_ofReal_pathWeight_update P m (b + 1) m (ζ m))
      (measurable_ofReal_pathWeight P (ζ m) (fun z ↦ P z (ω (b + 1))) (m + 1) (m + 1) b b) hcongr]
  have hkey := lintegral_isssd_pathWeight hpos q (m + 1) b hb (ζ m)
    (fun z ↦ P z (ω (b + 1))) (fun z ↦ (hpos _ _).le) ω
  rw [hkey]
  congr 2


/-- Left-block integral, unpinned form: on the support of `isssd ν (Icc a (l-1)) τ` the value at
`l` is `τ l`. -/
lemma lintegral_isssd_left_block' (hpos : ∀ x y, 0 < P x y) {p : ℕ} {a l : ℤ}
    (hl : l - 1 = a + p) (τ : ℤ → E) :
    ∫⁻ σ, ENNReal.ofReal (pathWeight P (a - 1) l σ)
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc a (l - 1)) τ)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1)
          * ENNReal.ofReal ((P ^ (p + 2)) (τ (a - 1)) (τ l)) := by
  rw [← lintegral_isssd_left_block hpos hl τ τ]
  refine lintegral_isssd_congr _ _ ((measurable_pathWeight P (a - 1) l).ennreal_ofReal)
    (measurable_ofReal_pathWeight_update P (a - 1) l l (τ l)) fun σ hσ ↦ ?_
  have hup : Function.update σ l (τ l) = σ :=
    Function.update_eq_self_iff.2 (hσ l (by simp only [Finset.mem_Icc]; omega)).symm
  rw [hup]

/-- Right-block integral, unpinned form: on the support of `isssd ν (Icc (m+1) b) τ` the value at
`m` is `τ m`. -/
lemma lintegral_isssd_right_block' (hpos : ∀ x y, 0 < P x y) {q : ℕ} {m b : ℤ}
    (hb : b = m + 1 + q) (τ : ℤ → E) :
    ∫⁻ σ, ENNReal.ofReal (pathWeight P m (b + 1) σ)
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc (m + 1) b) τ)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
          * ENNReal.ofReal ((P ^ (q + 2)) (τ m) (τ (b + 1))) := by
  rw [← lintegral_isssd_right_block hpos hb τ τ]
  refine lintegral_isssd_congr _ _ ((measurable_pathWeight P m (b + 1)).ennreal_ofReal)
    (measurable_ofReal_pathWeight_update P m (b + 1) m (τ m)) fun σ hσ ↦ ?_
  have hup : Function.update σ m (τ m) = σ :=
    Function.update_eq_self_iff.2 (hσ m (by simp only [Finset.mem_Icc]; omega)).symm
  rw [hup]

omit [DecidableEq E] [Nonempty E] in
/-- Matrix entries evaluated along a configuration are measurable. -/
lemma measurable_ofReal_apply_apply (M : Matrix E E ℝ) (u v : ℤ) :
    Measurable fun σ : ℤ → E ↦ ENNReal.ofReal (M (σ u) (σ v)) :=
  ((measurable_of_finite fun p : E × E ↦ M p.1 p.2).comp
    (f := fun σ : ℤ → E ↦ (σ u, σ v))
    ((measurable_pi_apply u).prodMk (measurable_pi_apply v))).ennreal_ofReal

/-- Integrating the full path weight over the two outer blocks `[a, l-1]` and `[m+1, b]` of the
interval `[a, b]` contracts each block into a matrix power (Comment (3.8)(1)). -/
lemma lintegral_isssd_outer_blocks (hpos : ∀ x y, 0 < P x y) {a b l m : ℤ} {p q : ℕ}
    (hl : l - 1 = a + p) (hb : b = m + 1 + q) (hlm : l ≤ m) (σ : ℤ → E) :
    ∫⁻ σ', ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ')
        ∂(Specification.isssd (uniformOn (Set.univ : Set E))
            (Finset.Icc a (l - 1) ∪ Finset.Icc (m + 1) b) σ)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
          * ENNReal.ofReal ((P ^ (p + 2)) (σ (a - 1)) (σ l) * pathWeight P l m σ
              * (P ^ (q + 2)) (σ m) (σ (b + 1))) := by
  have hinner : ∀ τ : ℤ → E,
      ∫⁻ σ', ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ')
          ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc a (l - 1)) τ)
        = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1)
            * (ENNReal.ofReal ((P ^ (p + 2)) (τ (a - 1)) (τ l))
              * ENNReal.ofReal (pathWeight P l (b + 1) τ)) := by
    intro τ
    have hcongr : ∀ σ' : ℤ → E, (∀ k ∉ Finset.Icc a (l - 1), σ' k = τ k) →
        ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ')
          = ENNReal.ofReal (pathWeight P (a - 1) l σ')
            * ENNReal.ofReal (pathWeight P l (b + 1) τ) := by
      intro σ' hσ'
      rw [pathWeight_split (show a - 1 ≤ l by omega) (show l ≤ b + 1 by omega),
        ← ENNReal.ofReal_mul (pathWeight_nonneg hpos _ _ _)]
      congr 2
      exact pathWeight_congr fun k hk ↦ hσ' k (by
        rw [Finset.mem_Icc] at hk ⊢
        omega)
    have hmulc : Measurable fun σ' : ℤ → E ↦ ENNReal.ofReal (pathWeight P (a - 1) l σ')
        * ENNReal.ofReal (pathWeight P l (b + 1) τ) :=
      ((measurable_pathWeight P (a - 1) l).ennreal_ofReal).mul_const _
    rw [lintegral_isssd_congr _ _ ((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal)
        hmulc hcongr,
      lintegral_mul_const _ ((measurable_pathWeight P (a - 1) l).ennreal_ofReal),
      lintegral_isssd_left_block' hpos hl τ, mul_assoc]
  have hmul1 : Measurable fun τ : ℤ → E ↦
      ENNReal.ofReal ((P ^ (p + 2)) (τ (a - 1)) (τ l))
        * ENNReal.ofReal (pathWeight P l (b + 1) τ) :=
    (measurable_ofReal_apply_apply (P ^ (p + 2)) (a - 1) l).mul
      ((measurable_pathWeight P l (b + 1)).ennreal_ofReal)
  have hmul2 : Measurable fun τ : ℤ → E ↦
      ENNReal.ofReal ((P ^ (p + 2)) (σ (a - 1)) (σ l) * pathWeight P l m σ)
        * ENNReal.ofReal (pathWeight P m (b + 1) τ) :=
    ((measurable_pathWeight P m (b + 1)).ennreal_ofReal).const_mul _
  rw [isssd_union, lintegral_isssd_bind _ _ _
      ((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal), lintegral_congr hinner,
    lintegral_const_mul _ hmul1]
  have hcongr2 : ∀ τ : ℤ → E, (∀ k ∉ Finset.Icc (m + 1) b, τ k = σ k) →
      ENNReal.ofReal ((P ^ (p + 2)) (τ (a - 1)) (τ l)) * ENNReal.ofReal (pathWeight P l (b + 1) τ)
        = ENNReal.ofReal ((P ^ (p + 2)) (σ (a - 1)) (σ l) * pathWeight P l m σ)
          * ENNReal.ofReal (pathWeight P m (b + 1) τ) := by
    intro τ hτ
    rw [hτ (a - 1) (by simp only [Finset.mem_Icc]; omega),
      hτ l (by simp only [Finset.mem_Icc]; omega),
      pathWeight_split (show l ≤ m by omega) (show m ≤ b + 1 by omega),
      pathWeight_congr (a := l) (c := m) (σ' := σ)
        (fun k hk ↦ hτ k (by rw [Finset.mem_Icc] at hk ⊢; omega)),
      ← ENNReal.ofReal_mul (pow_apply_pos hpos (p + 1) _ _).le,
      ← ENNReal.ofReal_mul (mul_nonneg (pow_apply_pos hpos (p + 1) _ _).le
        (pathWeight_nonneg hpos _ _ _)), mul_assoc]
  rw [lintegral_isssd_congr _ _ hmul1 hmul2 hcongr2,
    lintegral_const_mul _ ((measurable_pathWeight P m (b + 1)).ennreal_ofReal),
    lintegral_isssd_right_block' hpos hb σ]
  have hnn : (0 : ℝ) ≤ (P ^ (p + 2)) (σ (a - 1)) (σ l) * pathWeight P l m σ :=
    mul_nonneg (pow_apply_pos hpos (p + 1) _ _).le (pathWeight_nonneg hpos _ _ _)
  rw [ENNReal.ofReal_mul hnn]
  ring


/-! ### The finite-volume formula for an interval inside an interval (Comment (3.8)(1)) -/

/-- **Georgii, Comment (3.8)(1).** For the interval `Λ = [l, m]` sitting inside the interval
`Δ = [a, b]` with `l - 1 = a + p` and `b = m + 1 + q` (so `Δ` contains at least one site on each
side of `Λ`), the specification of the cylinder
`{σ_Λ = ζ_Λ}` is
`P^{p+2}(ω_{a-1}, ζ_l) P(ζ_l, ζ_{l+1}) ⋯ P(ζ_{m-1}, ζ_m) P^{q+2}(ζ_m, ω_{b+1})
  / P^{d+p+q+4}(ω_{a-1}, ω_{b+1})`, where `m = l + d`. -/
theorem markovSpecification_Icc_apply_cyl_of_subset (hpos : ∀ x y, 0 < P x y)
    {a b l m : ℤ} {d p q : ℕ} (hm : m = l + d) (hl : l - 1 = a + p) (hb : b = m + 1 + q)
    (ζ ω : ℤ → E) :
    markovSpecification P (Finset.Icc a b) ω (cyl (Finset.Icc l m) ζ)
      = ENNReal.ofReal ((P ^ (p + 2)) (ω (a - 1)) (ζ l) * pathWeight P l m ζ
          * (P ^ (q + 2)) (ζ m) (ω (b + 1))
          / (P ^ (d + p + q + 4)) (ω (a - 1)) (ω (b + 1))) := by
  have hlm : l ≤ m := by omega
  have hab : b = a + ((d + p + q + 2 : ℕ) : ℤ) := by push_cast; omega
  -- The Boltzmann factor on `Δ` is the path weight along `[a-1, b+1]`.
  have hbolt : ∀ σ : ℤ → E, (markovPotential P).boltzmannFactor 1 (Finset.Icc a b) σ
      = ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ) := by
    intro σ
    have h := boltzmannFactor_Icc (P := P) hpos a (d + p + q + 2) σ
    rw [← hab] at h
    exact h
  have hboltfun : (markovPotential P).boltzmannFactor 1 (Finset.Icc a b)
      = fun σ ↦ ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ) := funext hbolt
  -- Split `Δ` into the two outer blocks and `Λ`.
  have hsplit : Finset.Icc a b
      = (Finset.Icc a (l - 1) ∪ Finset.Icc (m + 1) b) ∪ Finset.Icc l m := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  -- The value of the outer-block integral, as a measurable function of the middle configuration.
  set F : (ℤ → E) → ℝ≥0∞ := fun σ ↦ (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1)
    * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
    * ENNReal.ofReal ((P ^ (p + 2)) (σ (a - 1)) (σ l) * pathWeight P l m σ
        * (P ^ (q + 2)) (σ m) (σ (b + 1))) with hFdef
  have hFmeas : Measurable F := by
    refine Measurable.const_mul ?_ _
    refine ((((measurable_of_finite fun p' : E × E ↦ (P ^ (p + 2)) p'.1 p'.2).comp
      (f := fun σ : ℤ → E ↦ (σ (a - 1), σ l))
      ((measurable_pi_apply (a - 1)).prodMk (measurable_pi_apply l))).mul
        (measurable_pathWeight P l m)).mul
      (((measurable_of_finite fun p' : E × E ↦ (P ^ (q + 2)) p'.1 p'.2).comp
        (f := fun σ : ℤ → E ↦ (σ m, σ (b + 1)))
        ((measurable_pi_apply m).prodMk (measurable_pi_apply (b + 1)))))).ennreal_ofReal
  have hFeq : ∀ σ : ℤ → E, ∫⁻ σ', ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ')
      ∂(Specification.isssd (uniformOn (Set.univ : Set E))
          (Finset.Icc a (l - 1) ∪ Finset.Icc (m + 1) b) σ) = F σ :=
    fun σ ↦ lintegral_isssd_outer_blocks hpos hl hb hlm σ
  -- The numerator.
  have hnum : ∫⁻ σ, (cyl (Finset.Icc l m) ζ).indicator
        ((markovPotential P).boltzmannFactor 1 (Finset.Icc a b)) σ
        ∂(Specification.isssd (uniformOn (Set.univ : Set E)) (Finset.Icc a b) ω)
      = F (overwrite (Finset.Icc l m) ζ ω) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (d + 1) := by
    rw [hboltfun, hsplit, isssd_union,
      lintegral_isssd_bind _ _ _
        (((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal).indicator
          (measurableSet_cyl _ _))]
    have hinner : ∀ σ : ℤ → E,
        ∫⁻ σ', (cyl (Finset.Icc l m) ζ).indicator
            (fun σ'' ↦ ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ'')) σ'
          ∂(Specification.isssd (uniformOn (Set.univ : Set E))
              (Finset.Icc a (l - 1) ∪ Finset.Icc (m + 1) b) σ)
          = (cyl (Finset.Icc l m) ζ).indicator F σ := by
      intro σ
      have hcongr : ∀ σ' : ℤ → E,
          (∀ k ∉ Finset.Icc a (l - 1) ∪ Finset.Icc (m + 1) b, σ' k = σ k) →
          (cyl (Finset.Icc l m) ζ).indicator
              (fun σ'' ↦ ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ'')) σ'
            = (cyl (Finset.Icc l m) ζ).indicator (fun _ ↦ (1 : ℝ≥0∞)) σ
              * ENNReal.ofReal (pathWeight P (a - 1) (b + 1) σ') := by
        intro σ' hσ'
        have hagree : ∀ k ∈ Finset.Icc l m, σ' k = σ k := fun k hk ↦ hσ' k (by
          simp only [Finset.mem_union, Finset.mem_Icc] at hk ⊢
          omega)
        have hiff : σ' ∈ cyl (Finset.Icc l m) ζ ↔ σ ∈ cyl (Finset.Icc l m) ζ := by
          constructor
          · exact fun h k hk ↦ (hagree k hk) ▸ h k hk
          · exact fun h k hk ↦ (hagree k hk).trans (h k hk)
        by_cases hmem : σ ∈ cyl (Finset.Icc l m) ζ
        · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem, one_mul]
        · rw [Set.indicator_of_notMem (fun h ↦ hmem (hiff.1 h)),
            Set.indicator_of_notMem hmem, zero_mul]
      rw [lintegral_isssd_congr _ _
          (((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal).indicator
            (measurableSet_cyl _ _))
          (((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal).const_mul _) hcongr,
        lintegral_const_mul _ ((measurable_pathWeight P (a - 1) (b + 1)).ennreal_ofReal),
        hFeq σ]
      by_cases hmem : σ ∈ cyl (Finset.Icc l m) ζ
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
    rw [lintegral_congr hinner, lintegral_isssd_indicator_cyl _ _ _ hFmeas]
    congr 2
    rw [Int.card_Icc]
    omega
  -- Evaluate `F` at the overwritten configuration.
  have hover : ∀ k ∈ Finset.Icc l m, overwrite (Finset.Icc l m) ζ ω k = ζ k :=
    fun k hk ↦ overwrite_apply_of_mem hk _ _
  have hFval : F (overwrite (Finset.Icc l m) ζ ω)
      = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
        * ENNReal.ofReal ((P ^ (p + 2)) (ω (a - 1)) (ζ l) * pathWeight P l m ζ
            * (P ^ (q + 2)) (ζ m) (ω (b + 1))) := by
    rw [hFdef]
    simp only
    rw [overwrite_apply_of_notMem (by simp only [Finset.mem_Icc]; omega),
      overwrite_apply_of_mem (by simp only [Finset.mem_Icc]; omega),
      overwrite_apply_of_mem (show m ∈ Finset.Icc l m by simp only [Finset.mem_Icc]; omega),
      overwrite_apply_of_notMem (show b + 1 ∉ Finset.Icc l m by
        simp only [Finset.mem_Icc]; omega),
      pathWeight_congr (a := l) (c := m) (σ' := ζ) hover]
  -- Assemble.
  rw [markovSpecification_apply_eq _ ω (measurableSet_cyl _ _), hnum, hFval,
    premodifierZ_Icc hpos hab ω]
  have hpow : (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
      * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (d + 1) = (Fintype.card E : ℝ≥0∞)⁻¹ ^ (d + p + q + 2 + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [show (Fintype.card E : ℝ≥0∞)⁻¹ ^ (p + 1) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (q + 1)
        * ENNReal.ofReal ((P ^ (p + 2)) (ω (a - 1)) (ζ l) * pathWeight P l m ζ
            * (P ^ (q + 2)) (ζ m) (ω (b + 1))) * (Fintype.card E : ℝ≥0∞)⁻¹ ^ (d + 1)
      = ENNReal.ofReal ((P ^ (p + 2)) (ω (a - 1)) (ζ l) * pathWeight P l m ζ
            * (P ^ (q + 2)) (ζ m) (ω (b + 1)))
        * ((Fintype.card E : ℝ≥0∞)⁻¹ ^ (d + p + q + 2 + 1)) by rw [← hpow]; ring,
    mul_mul_inv_cancel (pow_ne_zero _ card_inv_ne_zero) (ENNReal.pow_ne_top card_inv_ne_top),
    ← div_eq_mul_inv,
    ← ENNReal.ofReal_div_of_pos (pow_apply_pos hpos (d + p + q + 3) _ _)]


/-! ### The Doeblin limit (Georgii, step 5 of the proof of (3.5)) -/

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- A single geometric rate for the Doeblin estimate `|(P^k)(x,y) - α y| ≤ 2 ρ^k`, uniform in
`x` and `y` (Georgii, Appendix 3.A). -/
lemma exists_doeblin_bound (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)
    {α : E → ℝ} (hα : α ∈ stdSimplex ℝ E) (hαP : α ᵥ* P = α) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (x y : E) (k : ℕ), |(P ^ k) x y - α y| ≤ 2 * ρ ^ k := by
  obtain ⟨ε, hε0, hε⟩ := Matrix.exists_pos_le_of_pos P hpos
  refine ⟨1 - Fintype.card E * ε, Matrix.one_sub_card_mul_nonneg P hP hε,
    Matrix.one_sub_card_mul_lt_one hε0, fun x y k ↦ ?_⟩
  have h := Matrix.abs_pow_apply_sub_le P hP hε hα hαP x y k
  linarith

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The stationary distribution of a positive stochastic matrix is bounded below by a positive
constant (Georgii (3.3): `α_P ∈ ]0, 1[^E`). -/
lemma exists_pos_le_stationary (hpos : ∀ x y, 0 < P x y) {α : E → ℝ}
    (hα : α ∈ stdSimplex ℝ E) (hαP : α ᵥ* P = α) : ∃ c : ℝ, 0 < c ∧ ∀ y, c ≤ α y := by
  obtain ⟨y₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset E) α Finset.univ_nonempty
  exact ⟨α y₀, Matrix.pos_of_vecMul_eq_self P hpos hα hαP y₀,
    fun y ↦ hmin y (Finset.mem_univ y)⟩

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The ratio limit of Georgii's step 5: if `A k → β u`, `B k` and `D k` both approximate
`β (v k)` at the geometric rate `ρ ^ k`, and `β` is bounded below by `c > 0`, then
`A k B k / D k → β u`, even though `v k` may vary with `k`. -/
lemma tendsto_doeblin_ratio {ρ c : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc0 : 0 < c)
    {β : E → ℝ} (hc : ∀ z, c ≤ β z) {A B D : ℕ → ℝ} {u : E} {v : ℕ → E}
    (hAb : ∀ k, |A k - β u| ≤ 2 * ρ ^ k) (hA1 : ∀ k, |A k| ≤ 1)
    (hBb : ∀ k, |B k - β (v k)| ≤ 2 * ρ ^ k) (hDb : ∀ k, |D k - β (v k)| ≤ 2 * ρ ^ k) :
    Filter.Tendsto (fun k ↦ A k * B k / D k) Filter.atTop (𝓝 (β u)) := by
  have hpow0 : Filter.Tendsto (fun k : ℕ ↦ ρ ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hglim : Filter.Tendsto (fun k : ℕ ↦ 8 * ρ ^ k / c + 2 * ρ ^ k) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ ↦ 8 * ρ ^ k / c) Filter.atTop (𝓝 0) := by
      simpa using (hpow0.const_mul (8 : ℝ)).div_const c
    have h2 : Filter.Tendsto (fun k : ℕ ↦ 2 * ρ ^ k) Filter.atTop (𝓝 0) := by
      simpa using hpow0.const_mul (2 : ℝ)
    simpa using h1.add h2
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  refine squeeze_zero' (Filter.Eventually.of_forall fun k ↦ abs_nonneg _) ?_ hglim
  filter_upwards [hpow0.eventually (Iio_mem_nhds (show (0 : ℝ) < c / 4 by positivity))]
    with k hk
  have hk' : ρ ^ k < c / 4 := hk
  have hDge : c / 2 ≤ D k := by
    have h1 := abs_le.1 (hDb k)
    have h2 := hc (v k)
    linarith
  have hDpos : 0 < D k := lt_of_lt_of_le (by positivity) hDge
  have hBD : |B k - D k| ≤ 4 * ρ ^ k := by
    have h1 := abs_le.1 (hBb k)
    have h2 := abs_le.1 (hDb k)
    rw [abs_le]
    constructor <;> linarith
  have hratio : |B k / D k - 1| ≤ 8 * ρ ^ k / c := by
    have heq : B k / D k - 1 = (B k - D k) / D k := by field_simp
    rw [heq, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    have h8 : (0 : ℝ) ≤ 8 * ρ ^ k / c := by positivity
    have hval : 8 * ρ ^ k / c * (c / 2) = 4 * ρ ^ k := by field_simp; ring
    have hmul : 8 * ρ ^ k / c * (c / 2) ≤ 8 * ρ ^ k / c * D k :=
      mul_le_mul_of_nonneg_left hDge h8
    linarith
  have hsplit : A k * B k / D k - β u = A k * (B k / D k - 1) + (A k - β u) := by ring
  rw [hsplit]
  calc |A k * (B k / D k - 1) + (A k - β u)|
      ≤ |A k * (B k / D k - 1)| + |A k - β u| := abs_add_le _ _
    _ = |A k| * |B k / D k - 1| + |A k - β u| := by rw [abs_mul]
    _ ≤ 1 * (8 * ρ ^ k / c) + 2 * ρ ^ k := by
        have h1 : |A k| * |B k / D k - 1| ≤ 1 * (8 * ρ ^ k / c) :=
          mul_le_mul (hA1 k) hratio (abs_nonneg _) zero_le_one
        linarith [hAb k]
    _ = 8 * ρ ^ k / c + 2 * ρ ^ k := by ring

/-- **Georgii, step 5 of the proof of (3.5).** With `Λ = [l, m]` fixed and
`Δ(k) = [l - 1 - k, m + 1 + k] ↑ ℤ`, the finite-volume probabilities of the cylinder
`{σ_Λ = ζ_Λ}` converge to `α(ζ_l) P(ζ_l, ζ_{l+1}) ⋯ P(ζ_{m-1}, ζ_m)`, for every boundary
condition `ω`. -/
theorem tendsto_markovSpecification_Icc_apply_cyl (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) {α : E → ℝ} (hα : α ∈ stdSimplex ℝ E) (hαP : α ᵥ* P = α)
    {l m : ℤ} {d : ℕ} (hm : m = l + d) (ζ ω : ℤ → E) :
    Filter.Tendsto (fun k : ℕ ↦ markovSpecification P
        (Finset.Icc (l - 1 - (k : ℤ)) (m + 1 + (k : ℤ))) ω (cyl (Finset.Icc l m) ζ))
      Filter.atTop (𝓝 (ENNReal.ofReal (α (ζ l) * pathWeight P l m ζ))) := by
  obtain ⟨ρ, hρ0, hρ1, hbd⟩ := exists_doeblin_bound hP hpos hα hαP
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_stationary (P := P) hpos hα hαP
  have hshrink : ∀ (u v : E) (n k : ℕ), k ≤ n → |(P ^ n) u v - α v| ≤ 2 * ρ ^ k := by
    intro u v n k hk
    refine (hbd u v n).trans ?_
    have := pow_le_pow_of_le_one hρ0 hρ1.le hk
    linarith
  have hreal : Filter.Tendsto (fun k : ℕ ↦
      (P ^ (k + 2)) (ω (l - 1 - (k : ℤ) - 1)) (ζ l)
        * (P ^ (k + 2)) (ζ m) (ω (m + 1 + (k : ℤ) + 1))
        / (P ^ (d + k + k + 4)) (ω (l - 1 - (k : ℤ) - 1)) (ω (m + 1 + (k : ℤ) + 1)))
      Filter.atTop (𝓝 (α (ζ l))) := by
    refine tendsto_doeblin_ratio hρ0 hρ1 hc0 hc
      (A := fun k ↦ (P ^ (k + 2)) (ω (l - 1 - (k : ℤ) - 1)) (ζ l))
      (B := fun k ↦ (P ^ (k + 2)) (ζ m) (ω (m + 1 + (k : ℤ) + 1)))
      (D := fun k ↦ (P ^ (d + k + k + 4)) (ω (l - 1 - (k : ℤ) - 1)) (ω (m + 1 + (k : ℤ) + 1)))
      (u := ζ l) (v := fun k ↦ ω (m + 1 + (k : ℤ) + 1))
      (fun k ↦ hshrink _ _ _ _ (by omega)) (fun k ↦ ?_)
      (fun k ↦ hshrink _ _ _ _ (by omega)) (fun k ↦ hshrink _ _ _ _ (by omega))
    rw [abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic (pow_mem hP (k + 2)))]
    exact Matrix.le_one_of_mem_rowStochastic (pow_mem hP (k + 2))
  have hmul := hreal.mul_const (pathWeight P l m ζ)
  have hofReal := ENNReal.tendsto_ofReal hmul
  refine Filter.Tendsto.congr (fun k ↦ ?_) hofReal
  rw [markovSpecification_Icc_apply_cyl_of_subset (p := k) (q := k) hpos hm (by omega) (by omega)
    ζ ω]
  congr 1
  ring

/-! ### Uniqueness of the Gibbs measure (Georgii, step 5) -/

/-- **Georgii, step 5 of the proof of (3.5).** Every Gibbs measure of `markovSpecification P`
has the interval marginals of the stationary Markov chain with transition matrix `P` (3.3). -/
theorem isGibbsMeasure_apply_cyl (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)
    {α : E → ℝ} (hα : α ∈ stdSimplex ℝ E) (hαP : α ᵥ* P = α)
    {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : (markovSpecification P).IsGibbsMeasure μ) {l m : ℤ} {d : ℕ} (hm : m = l + d)
    (ζ : ℤ → E) :
    μ (cyl (Finset.Icc l m) ζ) = ENNReal.ofReal (α (ζ l) * pathWeight P l m ζ) := by
  have hbind : ∀ Δ : Finset ℤ, μ.bind (markovSpecification P Δ) = μ :=
    Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ
  have hmeasF : ∀ Δ : Finset ℤ, Measurable fun ω ↦
      markovSpecification P Δ ω (cyl (Finset.Icc l m) ζ) := fun Δ ↦
    (Kernel.measurable_coe _ (measurableSet_cyl _ _)).mono cylinderEvents_le_pi le_rfl
  have heq : ∀ k : ℕ, ∫⁻ ω, markovSpecification P
      (Finset.Icc (l - 1 - (k : ℤ)) (m + 1 + (k : ℤ))) ω (cyl (Finset.Icc l m) ζ) ∂μ
      = μ (cyl (Finset.Icc l m) ζ) := by
    intro k
    rw [← Measure.bind_apply (measurableSet_cyl _ _)
      ((markovSpecification P (Finset.Icc (l - 1 - (k : ℤ)) (m + 1 + (k : ℤ)))).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable, hbind]
  have hlim : Filter.Tendsto (fun k : ℕ ↦ ∫⁻ ω, markovSpecification P
      (Finset.Icc (l - 1 - (k : ℤ)) (m + 1 + (k : ℤ))) ω (cyl (Finset.Icc l m) ζ) ∂μ)
      Filter.atTop
      (𝓝 (∫⁻ _ω : ℤ → E, ENNReal.ofReal (α (ζ l) * pathWeight P l m ζ) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1) (fun k ↦ hmeasF _)
      (fun k ↦ Filter.Eventually.of_forall fun ω ↦ prob_le_one) (by simp)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    exact tendsto_markovSpecification_Icc_apply_cyl hP hpos hα hαP hm ζ ω
  rw [lintegral_const, measure_univ, mul_one] at hlim
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ μ (cyl (Finset.Icc l m) ζ)) Filter.atTop
      (𝓝 (ENNReal.ofReal (α (ζ l) * pathWeight P l m ζ))) := Filter.Tendsto.congr heq hlim
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-! ### The π-system of cylinder events -/

variable (E) in
/-- The collection of cylinder events `{σ_Λ = η_Λ}` with `Λ` finite. -/
def cylinders : Set (Set (ℤ → E)) := {A | ∃ (Λ : Finset ℤ) (η : ℤ → E), A = cyl Λ η}

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma isPiSystem_cylinders : IsPiSystem (cylinders E) := by
  rintro s ⟨Λ₁, η₁, rfl⟩ t ⟨Λ₂, η₂, rfl⟩ ⟨σ, hσ₁, hσ₂⟩
  refine ⟨Λ₁ ∪ Λ₂, σ, ?_⟩
  ext τ
  simp only [Set.mem_inter_iff, cyl, Set.mem_ofPred_eq, Finset.mem_union]
  constructor
  · rintro ⟨h1, h2⟩ k (hk | hk)
    · rw [h1 k hk, hσ₁ k hk]
    · rw [h2 k hk, hσ₂ k hk]
  · exact fun h ↦ ⟨fun k hk ↦ (h k (Or.inl hk)).trans (hσ₁ k hk),
      fun k hk ↦ (h k (Or.inr hk)).trans (hσ₂ k hk)⟩

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma univ_mem_cylinders : (Set.univ : Set (ℤ → E)) ∈ cylinders E := by
  obtain ⟨e⟩ := ‹Nonempty E›
  refine ⟨∅, fun _ ↦ e, ?_⟩
  ext σ
  simp [cyl]

omit [DecidableEq E] [Nonempty E] in
lemma generateFrom_cylinders :
    (inferInstance : MeasurableSpace (ℤ → E)) = MeasurableSpace.generateFrom (cylinders E) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine iSup_le fun i ↦ ?_
    rintro _ ⟨s, hs, rfl⟩
    have hset : (fun σ : ℤ → E ↦ σ i) ⁻¹' s = ⋃ x ∈ s, cyl {i} (fun _ ↦ x) := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_iUnion, cyl, Set.mem_ofPred_eq, Finset.mem_singleton,
        exists_prop]
      refine ⟨fun h ↦ ⟨σ i, h, fun k hk ↦ by rw [hk]⟩, ?_⟩
      rintro ⟨x, hx, h⟩
      rw [h i rfl]
      exact hx
    rw [hset]
    exact MeasurableSet.biUnion (Set.toFinite s).countable fun x _ ↦
      MeasurableSpace.measurableSet_generateFrom ⟨{i}, fun _ ↦ x, rfl⟩
  · rintro _ ⟨Λ, η, rfl⟩
    exact measurableSet_cyl Λ η

omit [DecidableEq E] in
/-- Two probability measures on `ℤ → E` agreeing on all cylinder events are equal. -/
lemma ext_of_forall_cyl {μ μ' : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (h : ∀ (Λ : Finset ℤ) (η : ℤ → E), μ (cyl Λ η) = μ' (cyl Λ η)) : μ = μ' := by
  refine Measure.ext_of_generateFrom_of_iUnion_univ (cylinders E) generateFrom_cylinders
    isPiSystem_cylinders univ_mem_cylinders (by simp) ?_
  rintro _ ⟨Λ, η, rfl⟩
  exact h Λ η

/-! ### From interval cylinders to arbitrary cylinders -/

/-- The configuration `η` modified on `Δ \ Λ` by `ξ`. -/
def fillOutside (Δ Λ : Finset ℤ) (η : ℤ → E) (ξ : ↥(Δ \ Λ) → E) : ℤ → E :=
  fun k ↦ if h : k ∈ Δ \ Λ then ξ ⟨k, h⟩ else η k

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- A cylinder on `Λ` is the disjoint union of the cylinders on a larger volume `Δ`. -/
lemma cyl_eq_iUnion (Δ Λ : Finset ℤ) (hΛ : Λ ⊆ Δ) (η : ℤ → E) :
    cyl Λ η = ⋃ ξ : ↥(Δ \ Λ) → E, cyl Δ (fillOutside Δ Λ η ξ) := by
  ext σ
  simp only [Set.mem_iUnion, cyl, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ⟨fun j ↦ σ j.1, fun k hk ↦ ?_⟩, ?_⟩
  · rw [fillOutside]
    by_cases hk' : k ∈ Δ \ Λ
    · rw [dite_eq_left hk']
    · rw [dite_eq_right hk']
      exact h k (by
        rw [Finset.mem_sdiff] at hk'
        exact by_contra fun hcon ↦ hk' ⟨hk, hcon⟩)
  · rintro ⟨ξ, hξ⟩ k hk
    have hkΔ : k ∈ Δ := hΛ hk
    have := hξ k hkΔ
    rw [this, fillOutside, dite_eq_right (by simp [Finset.mem_sdiff, hk])]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pairwise_disjoint_cyl_fillOutside (Δ Λ : Finset ℤ) (η : ℤ → E) :
    Pairwise (Function.onFun Disjoint fun ξ : ↥(Δ \ Λ) → E ↦ cyl Δ (fillOutside Δ Λ η ξ)) := by
  intro ξ ξ' hne
  refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne (funext fun j ↦ ?_)
  have h1 := hσ j.1 (Finset.mem_sdiff.1 j.2).1
  have h2 := hσ' j.1 (Finset.mem_sdiff.1 j.2).1
  rw [fillOutside, dite_eq_left j.2] at h1
  rw [fillOutside, dite_eq_left j.2] at h2
  rw [← h1, ← h2]

omit [DecidableEq E] [Nonempty E] in
/-- Decomposing a cylinder over the configurations on a disjoint finite volume `Λ₁`:
`μ(σ_{Λ₂} = ω_{Λ₂}) = ∑_{ξ ∈ E^{Λ₁}} μ(σ_{Λ₁} = ξ, σ_{Λ₂} = ω_{Λ₂})`. -/
lemma measure_cyl_eq_sum_juxt (μ : Measure (ℤ → E)) {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint Λ₁ Λ₂)
    (ω : ℤ → E) :
    μ (cyl Λ₂ ω) = ∑ ξ : Λ₁ → E, μ (cyl (Λ₁ ∪ Λ₂) (juxt (Λ₁ : Set ℤ) ω ξ)) := by
  have hdecomp : cyl Λ₂ ω = ⋃ ξ : Λ₁ → E, cyl (Λ₁ ∪ Λ₂) (juxt (Λ₁ : Set ℤ) ω ξ) := by
    ext σ
    simp only [Set.mem_iUnion, mem_cyl]
    constructor
    · intro hσ
      refine ⟨fun k ↦ σ k.1, fun k hk ↦ ?_⟩
      rcases Finset.mem_union.1 hk with hk₁ | hk₂
      · rw [juxt_apply_of_mem (by simpa using hk₁)]
      · rw [juxt_apply_of_not_mem (by simpa using Finset.disjoint_right.1 h hk₂)]
        exact hσ k hk₂
    · rintro ⟨ξ, hξ⟩ k hk
      rw [hξ k (Finset.mem_union_right _ hk),
        juxt_apply_of_not_mem (by simpa using Finset.disjoint_right.1 h hk)]
  have hdisj : Pairwise (Function.onFun Disjoint fun ξ : Λ₁ → E ↦
      cyl (Λ₁ ∪ Λ₂) (juxt (Λ₁ : Set ℤ) ω ξ)) := by
    intro ξ ξ' hne
    refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne (funext fun k ↦ ?_)
    have hmem : k.1 ∈ Λ₁ ∪ Λ₂ := Finset.mem_union_left _ k.2
    have h1 := hσ k.1 hmem
    have h2 := hσ' k.1 hmem
    rw [juxt_apply_of_mem (Finset.mem_coe.2 k.2)] at h1 h2
    exact h1.symm.trans h2
  rw [hdecomp, measure_iUnion hdisj fun ξ ↦ measurableSet_cyl _ _, tsum_fintype]

omit [DecidableEq E] [Nonempty E] in
/-- Two measures agreeing on all interval cylinders agree on all cylinders. -/
lemma measure_cyl_eq_of_forall_Icc {μ μ' : Measure (ℤ → E)}
    (h : ∀ (l : ℤ) (d : ℕ) (ζ : ℤ → E),
      μ (cyl (Finset.Icc l (l + d)) ζ) = μ' (cyl (Finset.Icc l (l + d)) ζ))
    (Λ : Finset ℤ) (η : ℤ → E) : μ (cyl Λ η) = μ' (cyl Λ η) := by
  obtain ⟨l, d, hΛ⟩ : ∃ (l : ℤ) (d : ℕ), Λ ⊆ Finset.Icc l (l + (d : ℤ)) := by
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    · refine ⟨Λ.min' hne, (Λ.max' hne - Λ.min' hne).toNat, fun k hk ↦ ?_⟩
      have h1 := Λ.min'_le k hk
      have h2 := Λ.le_max' k hk
      have h3 : Λ.min' hne ≤ Λ.max' hne := Λ.min'_le _ (Λ.max'_mem hne)
      rw [Finset.mem_Icc, Int.toNat_of_nonneg (by omega)]
      omega
  set Δ : Finset ℤ := Finset.Icc l (l + (d : ℤ)) with hΔ
  rw [cyl_eq_iUnion Δ Λ hΛ η,
    measure_iUnion (pairwise_disjoint_cyl_fillOutside Δ Λ η)
      (fun ξ ↦ measurableSet_cyl _ _),
    measure_iUnion (pairwise_disjoint_cyl_fillOutside Δ Λ η)
      (fun ξ ↦ measurableSet_cyl _ _)]
  exact tsum_congr fun ξ ↦ h l d _

/-- **Georgii, Theorem (3.5), uniqueness.** Any two Gibbs measures of `markovSpecification P`
coincide: `𝒢(γ)` contains at most one element (Georgii's step 5). -/
theorem eq_of_isGibbsMeasure (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)
    {μ μ' : Measure (ℤ → E)} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : (markovSpecification P).IsGibbsMeasure μ)
    (hμ' : (markovSpecification P).IsGibbsMeasure μ') : μ = μ' := by
  obtain ⟨α, hα, hαP⟩ := Matrix.exists_stationary P hP hpos
  refine ext_of_forall_cyl (measure_cyl_eq_of_forall_Icc fun l d ζ ↦ ?_)
  rw [isGibbsMeasure_apply_cyl hP hpos hα hαP hμ (m := l + (d : ℤ)) rfl ζ,
    isGibbsMeasure_apply_cyl hP hpos hα hαP hμ' (m := l + (d : ℤ)) rfl ζ]

/-! ### The determining function of `markovSpecification P` (Georgii (3.11)) -/

variable (P) in
/-- Georgii (3.11): the determining function `g(x,y,z) = P(x,y) P(y,z) / P²(x,z)` of the
specification of a positive stochastic matrix `P`. -/
def markovDeterminingFun (x y z : E) : ℝ := P x y * P y z / (P ^ 2) x z

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma markovDeterminingFun_pos (hpos : ∀ x y, 0 < P x y) (x y z : E) :
    0 < markovDeterminingFun P x y z :=
  div_pos (mul_pos (hpos _ _) (hpos _ _)) (pow_apply_pos hpos 1 _ _)

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma sum_markovDeterminingFun (hpos : ∀ x y, 0 < P x y) (x z : E) :
    ∑ y, markovDeterminingFun P x y z = 1 := by
  simp only [markovDeterminingFun]
  rw [← Finset.sum_div, show ∑ y, P x y * P y z = (P ^ 2) x z by
    rw [pow_two, Matrix.mul_apply]]
  exact div_self (pow_apply_pos hpos 1 x z).ne'

/-- **Georgii (3.11).** The singleton kernels of `markovSpecification P` are given by the
determining function `g(x,y,z) = P(x,y) P(y,z) / P²(x,z)`, so `markovSpecification P` is a
positive homogeneous Markov specification in the sense of Georgii (3.1). -/
theorem markovSpecification_singleton_apply (hpos : ∀ x y, 0 < P x y) (i : ℤ) (y : E)
    (ω : ℤ → E) :
    markovSpecification P {i} ω {σ : ℤ → E | σ i = y}
      = ENNReal.ofReal (markovDeterminingFun P (ω (i - 1)) y (ω (i + 1))) := by
  have hset : {σ : ℤ → E | σ i = y} = cyl (Finset.Icc i i) (Function.update ω i y) := by
    ext σ
    simp [cyl, Finset.Icc_self, Function.update_self]
  have hη : ∀ k ∉ Finset.Icc i i, Function.update ω i y k = ω k := by
    intro k hk
    rw [Finset.Icc_self, Finset.mem_singleton] at hk
    exact Function.update_of_ne hk _ _
  rw [show ({i} : Finset ℤ) = Finset.Icc i i from (Finset.Icc_self i).symm, hset,
    markovSpecification_Icc_apply_cyl hpos (n := 0) (by omega) ω _ hη, markovDeterminingFun]
  congr 1
  rw [pathWeight_split (show i - 1 ≤ i by omega) (show i ≤ i + 1 by omega),
    pathWeight_pair (show i = i - 1 + 1 by omega), pathWeight_single i,
    Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-! ### The matrix attached to a determining function (Georgii (3.7)) -/

variable (E) in
/-- Georgii (3.7): the auxiliary matrix `Q(x,y) = g(a,x,y)/g(a,a,y)` of a determining function
`g` and a reference state `a`. -/
def detQ (g : E → E → E → ℝ) (a : E) : Matrix E E ℝ := Matrix.of fun x y ↦ g a x y / g a a y

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma detQ_pos {g : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z) (a : E) (x y : E) :
    0 < detQ E g a x y := div_pos (hg _ _ _) (hg _ _ _)

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma detQ_self (g : E → E → E → ℝ) (hg : ∀ x y z, 0 < g x y z) (a z : E) :
    detQ E g a a z = 1 := div_self (hg a a z).ne'

variable (E) in
/-- Georgii (3.7): `P(x,y) = Q(x,y) r(y) / (q r(x))`, where `q` is the Perron root and `r` the
Perron eigenvector of `Q`. -/
noncomputable def matrixOfDetFun (g : E → E → E → ℝ) (hg : ∀ x y z, 0 < g x y z) (a : E) :
    Matrix E E ℝ :=
  Matrix.of fun x y ↦ detQ E g a x y * Matrix.perronVector (detQ E g a) (detQ_pos hg a) y
    / (Matrix.perronRoot (detQ E g a) (detQ_pos hg a)
        * Matrix.perronVector (detQ E g a) (detQ_pos hg a) x)

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma matrixOfDetFun_pos {g : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z) (a : E) (x y : E) :
    0 < matrixOfDetFun E g hg a x y :=
  div_pos (mul_pos (detQ_pos hg a x y) (Matrix.perronVector_pos _ (detQ_pos hg a) y))
    (mul_pos (Matrix.perronRoot_pos _ (detQ_pos hg a))
      (Matrix.perronVector_pos _ (detQ_pos hg a) x))

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma matrixOfDetFun_mem_rowStochastic {g : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z) (a : E) :
    matrixOfDetFun E g hg a ∈ Matrix.rowStochastic ℝ E := by
  refine Matrix.mem_rowStochastic_iff_sum.2
    ⟨fun x y ↦ (matrixOfDetFun_pos hg a x y).le, fun x ↦ ?_⟩
  have hv := Matrix.mulVec_perronVector (detQ E g a) (detQ_pos hg a)
  have hvx : 0 < Matrix.perronVector (detQ E g a) (detQ_pos hg a) x :=
    Matrix.perronVector_pos _ (detQ_pos hg a) x
  have hq : 0 < Matrix.perronRoot (detQ E g a) (detQ_pos hg a) :=
    Matrix.perronRoot_pos _ (detQ_pos hg a)
  have hsum : ∑ y, detQ E g a x y * Matrix.perronVector (detQ E g a) (detQ_pos hg a) y
      = Matrix.perronRoot (detQ E g a) (detQ_pos hg a)
        * Matrix.perronVector (detQ E g a) (detQ_pos hg a) x := by
    have := congrFun hv x
    simpa [Matrix.mulVec, dotProduct] using this
  have hden : (0 : ℝ) < Matrix.perronRoot (detQ E g a) (detQ_pos hg a)
      * Matrix.perronVector (detQ E g a) (detQ_pos hg a) x := mul_pos hq hvx
  simp only [matrixOfDetFun, Matrix.of_apply, ← Finset.sum_div, hsum]
  exact div_self hden.ne'

/-! ### Recovering `P` from its determining function (Georgii, step 2) -/

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma matrixOfDetFun_congr {g g' : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z)
    (hg' : ∀ x y z, 0 < g' x y z) (a : E) (h : g = g') :
    matrixOfDetFun E g hg a = matrixOfDetFun E g' hg' a := by
  subst h
  rfl

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Georgii (3.7): a positive eigenvector of `Q` determines the matrix `P` built from `g`. -/
lemma matrixOfDetFun_eq_of_eigen {g : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z) (a : E)
    {q : ℝ} (hq : 0 < q) {r : E → ℝ} (hr : ∀ x, 0 < r x)
    (heigen : detQ E g a *ᵥ r = q • r) {M : Matrix E E ℝ}
    (hM : ∀ x y, detQ E g a x y * r y = q * r x * M x y) :
    matrixOfDetFun E g hg a = M := by
  have hQpos : ∀ x y, 0 < detQ E g a x y := detQ_pos hg a
  have hqroot : q = Matrix.perronRoot (detQ E g a) hQpos :=
    Matrix.eq_perronRoot_of_pos_eigenvector _ hQpos hr heigen
  have hvpos : ∀ x, 0 < Matrix.perronVector (detQ E g a) hQpos x :=
    Matrix.perronVector_pos _ hQpos
  obtain ⟨c, hc⟩ : ∃ c : ℝ, r = c • Matrix.perronVector (detQ E g a) hQpos :=
    Matrix.exists_eq_smul_perronVector _ hQpos (by rw [← hqroot]; exact heigen)
  have hc0 : 0 < c := by
    obtain ⟨x⟩ := ‹Nonempty E›
    have h1 := hr x
    rw [hc] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    by_contra hcon
    push_neg at hcon
    nlinarith [hvpos x]
  ext x y
  have h1 := hM x y
  rw [hc] at h1
  simp only [Pi.smul_apply, smul_eq_mul] at h1
  have h2 : c * (detQ E g a x y * Matrix.perronVector (detQ E g a) hQpos y)
      = c * (q * Matrix.perronVector (detQ E g a) hQpos x * M x y) := by linear_combination h1
  have h3 := mul_left_cancel₀ hc0.ne' h2
  have hqne : q ≠ 0 := hq.ne'
  have hvne : Matrix.perronVector (detQ E g a) hQpos x ≠ 0 := (hvpos x).ne'
  simp only [matrixOfDetFun, Matrix.of_apply]
  rw [← hqroot, h3]
  field_simp

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma detQ_markovDeterminingFun (hpos : ∀ x y, 0 < P x y) (a x y : E) :
    detQ E (markovDeterminingFun P) a x y = P a x * P x y / (P a a * P a y) := by
  have h1 : (P ^ 2) a y ≠ 0 := (pow_apply_pos hpos 1 a y).ne'
  have h2 : P a a ≠ 0 := (hpos a a).ne'
  have h3 : P a y ≠ 0 := (hpos a y).ne'
  simp only [detQ, Matrix.of_apply, markovDeterminingFun]
  field_simp

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- **Georgii, step 2 of the proof of (3.5).** A positive stochastic matrix `P` is recovered from
its determining function by formula (3.7); in particular `ℓ : P ↦ γ` is injective. -/
theorem matrixOfDetFun_markovDeterminingFun (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) (a : E) :
    matrixOfDetFun E (markovDeterminingFun P) (markovDeterminingFun_pos hpos) a = P := by
  have hM : ∀ x y, detQ E (markovDeterminingFun P) a x y * P a y
      = (P a a)⁻¹ * P a x * P x y := by
    intro x y
    rw [detQ_markovDeterminingFun hpos]
    have h2 : P a a ≠ 0 := (hpos a a).ne'
    have h3 : P a y ≠ 0 := (hpos a y).ne'
    field_simp
  have heigen : detQ E (markovDeterminingFun P) a *ᵥ (fun x ↦ P a x)
      = (P a a)⁻¹ • (fun x ↦ P a x) := by
    funext x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun y _ ↦ hM x y, ← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic hP x, mul_one]
  exact matrixOfDetFun_eq_of_eigen _ a (inv_pos.2 (hpos a a)) (fun x ↦ hpos a x) heigen hM

/-- **Georgii, Theorem (3.5), injectivity.** Two positive stochastic matrices with the same
Markov specification are equal. -/
theorem markovSpecification_injOn {P' : Matrix E E ℝ} (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) (hP' : P' ∈ Matrix.rowStochastic ℝ E) (hpos' : ∀ x y, 0 < P' x y)
    (h : markovSpecification P = markovSpecification P') : P = P' := by
  obtain ⟨a⟩ := ‹Nonempty E›
  have hgg : markovDeterminingFun P = markovDeterminingFun P' := by
    funext x y z
    have h1 := markovSpecification_singleton_apply hpos 0 y (fun k ↦ if k = -1 then x else z)
    have h2 := markovSpecification_singleton_apply hpos' 0 y (fun k ↦ if k = -1 then x else z)
    rw [h] at h1
    have h3 := h1.symm.trans h2
    have hx : (if (0 : ℤ) - 1 = -1 then x else z) = x := by norm_num
    have hz : (if (0 : ℤ) + 1 = -1 then x else z) = z := by norm_num
    simp only [hx, hz] at h3
    exact (ENNReal.ofReal_eq_ofReal_iff (markovDeterminingFun_pos hpos x y z).le
      (markovDeterminingFun_pos hpos' x y z).le).1 h3
  calc P = matrixOfDetFun E (markovDeterminingFun P) (markovDeterminingFun_pos hpos) a :=
        (matrixOfDetFun_markovDeterminingFun hP hpos a).symm
    _ = matrixOfDetFun E (markovDeterminingFun P') (markovDeterminingFun_pos hpos') a :=
        matrixOfDetFun_congr _ _ a hgg
    _ = P' := matrixOfDetFun_markovDeterminingFun hP' hpos' a

/-! ### Georgii's equation (3.12) implies (3.11) (step 3) -/

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- **Georgii, step 3 of the proof of (3.5).** If the normalised positive function `g` satisfies
(3.12), then `g` is the determining function (3.11) of every matrix of the shape
`M x y = Q x y * v y / (q * v x)` built from the auxiliary matrix `Q = detQ E g a`, a positive
scalar `q` and a positive vector `v`; taking for `q`, `v` the Perron root and eigenvector of `Q`
gives the matrix `P` of (3.7). -/
theorem markovDeterminingFun_of_eq_312 {g : E → E → E → ℝ} (hg : ∀ x y z, 0 < g x y z)
    (hnorm : ∀ x z, ∑ y, g x y z = 1) (a : E) {q : ℝ} (hq : 0 < q) {v : E → ℝ}
    (hv : ∀ x, 0 < v x) {M : Matrix E E ℝ}
    (hMdef : ∀ x y, M x y = detQ E g a x y * v y / (q * v x))
    (h312 : ∀ x y z, g x y z / g x a z * (g a x a / g a a a)
      = g a x y / g a a y * (g a y z / g a a z)) :
    markovDeterminingFun M = g := by
  have hQ : ∀ x y, 0 < detQ E g a x y := detQ_pos hg a
  have hMpos : ∀ x y, 0 < M x y := fun x y ↦ by
    rw [hMdef x y]
    exact div_pos (mul_pos (hQ x y) (hv y)) (mul_pos hq (hv x))
  have hM2 : ∀ x z, (M ^ 2) x z = ∑ y, M x y * M y z := fun x z ↦ by
    rw [pow_two, Matrix.mul_apply]
  have hM2pos : ∀ x z, 0 < (M ^ 2) x z := fun x z ↦ by
    rw [hM2]
    exact Finset.sum_pos (fun y _ ↦ mul_pos (hMpos _ _) (hMpos _ _)) Finset.univ_nonempty
  have hstar : ∀ x y z, g x y z * detQ E g a x a
      = g x a z * (detQ E g a x y * detQ E g a y z) := by
    intro x y z
    have hne : g x a z ≠ 0 := (hg x a z).ne'
    simp only [detQ, Matrix.of_apply]
    calc g x y z * (g a x a / g a a a)
        = g x y z / g x a z * (g a x a / g a a a) * g x a z := by field_simp
      _ = g a x y / g a a y * (g a y z / g a a z) * g x a z := by rw [h312 x y z]
      _ = g x a z * (g a x y / g a a y * (g a y z / g a a z)) := by ring
  have hprod : ∀ x y z, M x y * M y z * (q ^ 2 * v x)
      = detQ E g a x y * detQ E g a y z * v z := by
    intro x y z
    have h1 : q ≠ 0 := hq.ne'
    have h2 : v x ≠ 0 := (hv x).ne'
    have h3 : v y ≠ 0 := (hv y).ne'
    rw [hMdef x y, hMdef y z]
    field_simp
  have hprodA : ∀ x z, M x a * M a z * (q ^ 2 * v x) = detQ E g a x a * v z := by
    intro x z
    rw [hprod x a z, detQ_self g hg a z, mul_one]
  have hkey1 : ∀ x y z, g x y z * (M x a * M a z) = g x a z * (M x y * M y z) := by
    intro x y z
    have hc : (0 : ℝ) < q ^ 2 * v x := mul_pos (pow_pos hq 2) (hv x)
    have e1 : g x y z * (M x a * M a z) * (q ^ 2 * v x)
        = g x y z * (detQ E g a x a * v z) := by linear_combination g x y z * hprodA x z
    have e2 : g x a z * (M x y * M y z) * (q ^ 2 * v x)
        = g x a z * (detQ E g a x y * detQ E g a y z * v z) := by
      linear_combination g x a z * hprod x y z
    have e3 : g x y z * (detQ E g a x a * v z)
        = g x a z * (detQ E g a x y * detQ E g a y z * v z) := by
      linear_combination v z * hstar x y z
    exact mul_right_cancel₀ hc.ne' (e1.trans (e3.trans e2.symm))
  have hnorm2 : ∀ x z, M x a * M a z = g x a z * (M ^ 2) x z := by
    intro x z
    have hsum := Finset.sum_congr rfl fun y (_ : y ∈ (Finset.univ : Finset E)) ↦ hkey1 x y z
    rw [← Finset.sum_mul, hnorm x z, one_mul, ← Finset.mul_sum, ← hM2 x z] at hsum
    exact hsum
  funext x y z
  simp only [markovDeterminingFun]
  rw [div_eq_iff (hM2pos x z).ne']
  have h1 := hkey1 x y z
  rw [hnorm2 x z] at h1
  have h3 : g x a z * (g x y z * (M ^ 2) x z) = g x a z * (M x y * M y z) := by
    linear_combination h1
  exact (mul_left_cancel₀ (hg x a z).ne' h3).symm

/-! ### Positive homogeneous Markov specifications (Georgii (3.1)) -/

/-- Georgii (3.1): `γ` is a positive homogeneous Markov specification with determining function
`g` if `γ_{i}(σ_i = y|ω) = g(ω_{i-1}, y, ω_{i+1})` for a strictly positive `g` on `E³`. -/
structure IsPositiveHomogeneousMarkovWith (γ : Specification ℤ E) (g : E → E → E → ℝ) :
    Prop where
  /-- The determining function is strictly positive. -/
  pos : ∀ x y z, 0 < g x y z
  /-- The singleton kernels are given by `g`. -/
  singleton_apply : ∀ (i : ℤ) (y : E) (ω : ℤ → E),
    γ {i} ω {σ : ℤ → E | σ i = y} = ENNReal.ofReal (g (ω (i - 1)) y (ω (i + 1)))

/-- Georgii (3.1): a positive homogeneous Markov specification on `ℤ`. -/
def IsPositiveHomogeneousMarkov (γ : Specification ℤ E) : Prop :=
  ∃ g : E → E → E → ℝ, IsPositiveHomogeneousMarkovWith γ g

/-- `markovSpecification P` is a positive homogeneous Markov specification with determining
function `g(x,y,z) = P(x,y) P(y,z) / P²(x,z)` (Georgii (3.11)). -/
theorem isPositiveHomogeneousMarkovWith_markovSpecification (hpos : ∀ x y, 0 < P x y) :
    IsPositiveHomogeneousMarkovWith (markovSpecification P) (markovDeterminingFun P) where
  pos := markovDeterminingFun_pos hpos
  singleton_apply := markovSpecification_singleton_apply hpos

theorem isPositiveHomogeneousMarkov_markovSpecification (hpos : ∀ x y, 0 < P x y) :
    IsPositiveHomogeneousMarkov (markovSpecification P) :=
  ⟨_, isPositiveHomogeneousMarkovWith_markovSpecification hpos⟩

/-! ### A specification is determined by its singleton kernels (Georgii (1.33)) -/

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_cyl_cylinderEvents {Δ : Set ℤ} {Λ : Finset ℤ} (hΛ : ↑Λ ⊆ Δ) (η : ℤ → E) :
    MeasurableSet[cylinderEvents Δ] (cyl Λ η) := by
  have hrw : cyl Λ η = ⋂ k ∈ Λ, {σ : ℤ → E | σ k = η k} := by
    ext σ
    simp [cyl]
  rw [hrw]
  refine Finset.measurableSet_biInter _ fun k hk ↦ ?_
  exact (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (hΛ hk))
    (measurableSet_singleton (η k))

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_eq_apply (i : ℤ) (y : E) : MeasurableSet {σ : ℤ → E | σ i = y} := by
  have hrw : {σ : ℤ → E | σ i = y} = (fun σ : ℤ → E ↦ σ i) ⁻¹' {y} := rfl
  rw [hrw]
  exact (measurable_pi_apply i) (measurableSet_singleton y)

/-- Two specifications whose singleton kernel at `i` gives the same mass to each event
`{σ_i = y}` have the same singleton kernel at `i`. -/
lemma singleton_eq_of_forall_apply (γ γ' : Specification ℤ E) (i : ℤ)
    (h : ∀ (y : E) (ω : ℤ → E),
      γ {i} ω {σ : ℤ → E | σ i = y} = γ' {i} ω {σ : ℤ → E | σ i = y}) :
    γ {i} = γ' {i} := by
  refine Kernel.ext fun ω ↦ ext_of_forall_cyl fun Λ η ↦ ?_
  by_cases hi : i ∈ Λ
  · have hsplit : cyl Λ η = {σ : ℤ → E | σ i = η i} ∩ cyl (Λ.erase i) η := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, cyl, Finset.mem_erase]
      refine ⟨fun hσ ↦ ⟨hσ i hi, fun k hk ↦ hσ k hk.2⟩, ?_⟩
      rintro ⟨h1, h2⟩ k hk
      by_cases hki : k = i
      · rw [hki]; exact h1
      · exact h2 k ⟨hki, hk⟩
    have hB : MeasurableSet[cylinderEvents ((({i} : Finset ℤ) : Set ℤ)ᶜ)] (cyl (Λ.erase i) η) := by
      refine measurableSet_cyl_cylinderEvents (fun k hk ↦ ?_) η
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.coe_singleton, Set.mem_singleton_iff,
        Set.mem_compl_iff] at hk ⊢
      exact hk.2
    rw [hsplit, γ.isProper.inter_eq_indicator_mul {i} (measurableSet_eq_apply i (η i)) hB ω,
      γ'.isProper.inter_eq_indicator_mul {i} (measurableSet_eq_apply i (η i)) hB ω, h (η i) ω]
  · have hB : MeasurableSet[cylinderEvents ((({i} : Finset ℤ) : Set ℤ)ᶜ)] (cyl Λ η) := by
      refine measurableSet_cyl_cylinderEvents (fun k hk ↦ ?_) η
      simp only [Finset.mem_coe] at hk
      simp only [Finset.coe_singleton, Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      exact hi hk
    have key : ∀ δ : Specification ℤ E, δ {i} ω (cyl Λ η) = (cyl Λ η).indicator 1 ω := by
      intro δ
      have hδ := δ.isProper.inter_eq_indicator_mul {i} MeasurableSet.univ hB ω
      rw [Set.univ_inter, measure_univ, mul_one] at hδ
      exact hδ
    rw [key γ, key γ']

omit [DecidableEq E] in
/-- The singleton kernels of `markovSpecification P` as densities against `isssd ν`. -/
lemma markovSpecification_eq_withDensity (Λ : Finset ℤ) (η : ℤ → E) :
    markovSpecification P Λ η
      = (Specification.isssd (uniformOn (Set.univ : Set E)) Λ η).withDensity
          (Specification.premodifierNorm (uniformOn (Set.univ : Set E))
            ((markovPotential P).boltzmannFactor 1) Λ) := rfl

/-- **Georgii (1.33) for `markovSpecification P`.** A specification with the same singleton
kernels as `markovSpecification P` equals it. -/
theorem eq_markovSpecification_of_forall_singleton
    {γ : Specification ℤ E} (hγ : ∀ i : ℤ, γ {i} = markovSpecification P {i}) :
    γ = markovSpecification P := by
  have hadm := Potential.isPremodifierAdmissible_boltzmannFactor (Φ := markovPotential P)
    (uniformOn (Set.univ : Set E)) 1
  refine Specification.eq_of_forall_singleton_eq
    (Specification.isStronglyConsistent_isssd (S := ℤ)
      (uniformOn (Set.univ : Set E))).isDisjointlyConsistent
    (ρ := fun i ↦ Specification.premodifierNorm (uniformOn (Set.univ : Set E))
      ((markovPotential P).boltzmannFactor 1) {i})
    (fun i ↦ Specification.measurable_relNorm
      (γ := Specification.isssd (uniformOn (Set.univ : Set E)))
      (Potential.isPremodifier_boltzmannFactor 1).measurable {i})
    (fun i ω ↦ ?_) (fun i ω ↦ ?_) (fun i η ↦ markovSpecification_eq_withDensity {i} η) hγ
  · rw [Specification.premodifierNorm, Specification.relNorm]
    refine ENNReal.div_ne_zero.2 ⟨(Potential.boltzmannFactor_pos 1 _ _).ne', ?_⟩
    exact (hadm ({i} : Finset ℤ) ω).2
  · rw [Specification.premodifierNorm, Specification.relNorm]
    intro hcon
    rw [ENNReal.div_eq_top] at hcon
    rcases hcon with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact (hadm ({i} : Finset ℤ) ω).1 h2
    · exact Potential.boltzmannFactor_ne_top 1 _ _ h1

/-- **Georgii, step 4 of the proof of (3.5), conclusion.** A positive homogeneous Markov
specification whose determining function is (3.11) for `P` equals `markovSpecification P`. -/
theorem eq_markovSpecification_of_determiningFun (hpos : ∀ x y, 0 < P x y)
    {γ : Specification ℤ E} {g : E → E → E → ℝ} (hγ : IsPositiveHomogeneousMarkovWith γ g)
    (hgP : g = markovDeterminingFun P) : γ = markovSpecification P := by
  refine eq_markovSpecification_of_forall_singleton fun i ↦ ?_
  refine singleton_eq_of_forall_apply γ _ i fun y ω ↦ ?_
  rw [hγ.singleton_apply i y ω, markovSpecification_singleton_apply hpos i y ω, hgP]

/-! ### Georgii's equation (3.12) from the consistency of `γ` on `{1, 2}` (step 4) -/

omit [Fintype E] [DecidableEq E] [Nonempty E] in
/-- A proper kernel is concentrated on the configurations agreeing with `ω` off `Λ`. -/
lemma specification_ae_eq (γ : Specification ℤ E) (Λ : Finset ℤ) (ω : ℤ → E) {k : ℤ}
    (hk : k ∉ Λ) : ∀ᵐ ξ ∂(γ Λ ω), ξ k = ω k := by
  have hB : MeasurableSet[cylinderEvents ((Λ : Set ℤ)ᶜ)] {σ : ℤ → E | σ k = ω k} :=
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simpa using hk))
      (measurableSet_singleton (ω k))
  have h1 := γ.isProper.inter_eq_indicator_mul Λ MeasurableSet.univ hB ω
  rw [Set.univ_inter, measure_univ, mul_one,
    Set.indicator_of_mem (show ω ∈ {σ : ℤ → E | σ k = ω k} from rfl), Pi.one_apply] at h1
  rw [MeasureTheory.ae_iff]
  have hcompl : {ξ : ℤ → E | ¬ ξ k = ω k} = ({σ : ℤ → E | σ k = ω k})ᶜ := rfl
  rw [hcompl, measure_compl (cylinderEvents_le_pi _ hB) (measure_ne_top _ _), h1, measure_univ,
    tsub_self]

omit [DecidableEq E] [Nonempty E] in
lemma measure_eq_sum_inter (μ : Measure (ℤ → E)) (i j : ℤ) (y : E) :
    μ {σ : ℤ → E | σ j = y} = ∑ u, μ ({σ : ℤ → E | σ i = u} ∩ {σ : ℤ → E | σ j = y}) := by
  have hrw : {σ : ℤ → E | σ j = y}
      = ⋃ u, ({σ : ℤ → E | σ i = u} ∩ {σ : ℤ → E | σ j = y}) := by
    ext σ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨σ i, rfl, h⟩, fun h ↦ h.choose_spec.2⟩
  have hdisj : Pairwise (Function.onFun Disjoint
      fun u : E ↦ ({σ : ℤ → E | σ i = u} ∩ {σ : ℤ → E | σ j = y})) := by
    intro u u' huu'
    refine Set.disjoint_left.2 fun σ hσ hσ' ↦ huu' ?_
    rw [← hσ.1, ← hσ'.1]
  have hmeas : ∀ u : E,
      MeasurableSet ({σ : ℤ → E | σ i = u} ∩ {σ : ℤ → E | σ j = y}) :=
    fun u ↦ (measurableSet_eq_apply i u).inter (measurableSet_eq_apply j y)
  conv_lhs => rw [hrw]
  rw [measure_iUnion hdisj hmeas, tsum_fintype]

omit [DecidableEq E] [Nonempty E] in
lemma measure_univ_eq_sum (μ : Measure (ℤ → E)) [IsProbabilityMeasure μ] (j : ℤ) :
    ∑ y, μ {σ : ℤ → E | σ j = y} = 1 := by
  have hrw : (Set.univ : Set (ℤ → E)) = ⋃ y, {σ : ℤ → E | σ j = y} := by
    ext σ
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    exact ⟨σ j, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun y : E ↦ {σ : ℤ → E | σ j = y}) := by
    intro y y' hyy'
    refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hyy' ?_
    rw [← hσ, ← hσ']
  have hmeas : ∀ y : E, MeasurableSet {σ : ℤ → E | σ j = y} := measurableSet_eq_apply j
  have := measure_univ (μ := μ)
  rw [hrw, measure_iUnion hdisj hmeas, tsum_fintype] at this
  exact this

omit [DecidableEq E] [Nonempty E] in
/-- The determining function of a positive homogeneous Markov specification is normalised. -/
lemma sum_determiningFun_eq_one {γ : Specification ℤ E} {g : E → E → E → ℝ}
    (hγ : IsPositiveHomogeneousMarkovWith γ g) (x z : E) : ∑ y, g x y z = 1 := by
  have hω : ∀ k : ℤ, (fun k : ℤ ↦ if k = -1 then x else z) k = if k = -1 then x else z :=
    fun _ ↦ rfl
  have hx : (if (0 : ℤ) - 1 = -1 then x else z) = x := by norm_num
  have hz : (if (0 : ℤ) + 1 = -1 then x else z) = z := by norm_num
  have hsum := measure_univ_eq_sum (γ ({0} : Finset ℤ) (fun k : ℤ ↦ if k = -1 then x else z)) 0
  simp only [hγ.singleton_apply 0 _ (fun k : ℤ ↦ if k = -1 then x else z), hx, hz] at hsum
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ (hγ.pos x y z).le] at hsum
  have h1 : ENNReal.ofReal (∑ y, g x y z) = ENNReal.ofReal 1 := by
    rw [hsum, ENNReal.ofReal_one]
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun y _ ↦ (hγ.pos x y z).le)
    zero_le_one).1 h1

/-- **Georgii, step 4 of the proof of (3.5).** The determining function of a positive homogeneous
Markov specification satisfies equation (3.12). The proof evaluates `γ_{1,2}` on the events
`[xy] = {σ_1 = x, σ_2 = y}` with a boundary condition `ω_0 = a`, `ω_3 = z`, and uses the two
consistency identities `γ_{1,2} = γ_{1,2} γ_{1} = γ_{1,2} γ_{2}`. -/
theorem eq_312_of_isPositiveHomogeneousMarkovWith {γ : Specification ℤ E} {g : E → E → E → ℝ}
    (hγ : IsPositiveHomogeneousMarkovWith γ g) (a : E) (x₀ y₀ z : E) :
    g x₀ y₀ z / g x₀ a z * (g a x₀ a / g a a a)
      = g a x₀ y₀ / g a a y₀ * (g a y₀ z / g a a z) := by
  classical
  set ω : ℤ → E := fun k ↦ if k = 0 then a else z with hωdef
  have hω0 : ω 0 = a := by simp [hωdef]
  have hω3 : ω 3 = z := by norm_num [hωdef]
  set b : E → E → ℝ≥0∞ :=
    fun x y ↦ γ ({1, 2} : Finset ℤ) ω ({σ : ℤ → E | σ 1 = x} ∩ {σ : ℤ → E | σ 2 = y}) with hbdef
  have hsub1 : ({1} : Finset ℤ) ⊆ ({1, 2} : Finset ℤ) := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hsub2 : ({2} : Finset ℤ) ⊆ ({1, 2} : Finset ℤ) := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [hk]
  have hB1 : ∀ y : E, MeasurableSet[cylinderEvents ((({1} : Finset ℤ) : Set ℤ)ᶜ)]
      {σ : ℤ → E | σ 2 = y} := fun y ↦
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by norm_num))
      (measurableSet_singleton y)
  have hB2 : ∀ x : E, MeasurableSet[cylinderEvents ((({2} : Finset ℤ) : Set ℤ)ᶜ)]
      {σ : ℤ → E | σ 1 = x} := fun x ↦
    (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by norm_num))
      (measurableSet_singleton x)
  -- Consistency with `γ_{1}` (Georgii's `[xy] = g(a,x,y) ∑_u [uy]`).
  have hF1 : ∀ x y : E, b x y
      = ENNReal.ofReal (g a x y) * γ ({1, 2} : Finset ℤ) ω {σ : ℤ → E | σ 2 = y} := by
    intro x y
    have hbind : b x y = ∫⁻ ξ, γ ({1} : Finset ℤ) ξ
        ({σ : ℤ → E | σ 1 = x} ∩ {σ : ℤ → E | σ 2 = y}) ∂(γ ({1, 2} : Finset ℤ) ω) := by
      rw [hbdef]
      conv_lhs => rw [← γ.bind hsub1 ω]
      exact Measure.bind_apply ((measurableSet_eq_apply 1 x).inter (measurableSet_eq_apply 2 y))
        ((γ ({1} : Finset ℤ)).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
    have hint : ∀ ξ : ℤ → E, γ ({1} : Finset ℤ) ξ
        ({σ : ℤ → E | σ 1 = x} ∩ {σ : ℤ → E | σ 2 = y})
        = ({σ : ℤ → E | σ 2 = y}).indicator 1 ξ * ENNReal.ofReal (g (ξ 0) x (ξ 2)) := by
      intro ξ
      rw [γ.isProper.inter_eq_indicator_mul {1} (measurableSet_eq_apply 1 x) (hB1 y) ξ,
        hγ.singleton_apply 1 x ξ]
      norm_num
    have hae : ∀ᵐ ξ ∂(γ ({1, 2} : Finset ℤ) ω), ξ 0 = ω 0 :=
      specification_ae_eq γ _ ω (by decide)
    have hstep : ∫⁻ ξ, ({σ : ℤ → E | σ 2 = y}).indicator 1 ξ * ENNReal.ofReal (g (ξ 0) x (ξ 2))
        ∂(γ ({1, 2} : Finset ℤ) ω)
        = ∫⁻ ξ, ({σ : ℤ → E | σ 2 = y}).indicator
            (fun _ ↦ ENNReal.ofReal (g a x y)) ξ ∂(γ ({1, 2} : Finset ℤ) ω) := by
      refine lintegral_congr_ae (hae.mono fun ξ hξ ↦ ?_)
      show ({σ : ℤ → E | σ 2 = y}).indicator 1 ξ * ENNReal.ofReal (g (ξ 0) x (ξ 2))
        = ({σ : ℤ → E | σ 2 = y}).indicator (fun _ ↦ ENNReal.ofReal (g a x y)) ξ
      by_cases hmem : ξ ∈ {σ : ℤ → E | σ 2 = y}
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Pi.one_apply, one_mul, hξ, hω0,
          show ξ 2 = y from hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
    rw [hbind, lintegral_congr hint, hstep,
      lintegral_indicator_const (measurableSet_eq_apply 2 y)]
  -- Consistency with `γ_{2}` (Georgii's `[xy] = g(x,y,z) ∑_v [xv]`).
  have hF2 : ∀ x y : E, b x y
      = ENNReal.ofReal (g x y z) * γ ({1, 2} : Finset ℤ) ω {σ : ℤ → E | σ 1 = x} := by
    intro x y
    have hbind : b x y = ∫⁻ ξ, γ ({2} : Finset ℤ) ξ
        ({σ : ℤ → E | σ 1 = x} ∩ {σ : ℤ → E | σ 2 = y}) ∂(γ ({1, 2} : Finset ℤ) ω) := by
      rw [hbdef]
      conv_lhs => rw [← γ.bind hsub2 ω]
      exact Measure.bind_apply ((measurableSet_eq_apply 1 x).inter (measurableSet_eq_apply 2 y))
        ((γ ({2} : Finset ℤ)).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
    have hint : ∀ ξ : ℤ → E, γ ({2} : Finset ℤ) ξ
        ({σ : ℤ → E | σ 1 = x} ∩ {σ : ℤ → E | σ 2 = y})
        = ({σ : ℤ → E | σ 1 = x}).indicator 1 ξ * ENNReal.ofReal (g (ξ 1) y (ξ 3)) := by
      intro ξ
      rw [Set.inter_comm,
        γ.isProper.inter_eq_indicator_mul {2} (measurableSet_eq_apply 2 y) (hB2 x) ξ,
        hγ.singleton_apply 2 y ξ]
      norm_num
    have hae : ∀ᵐ ξ ∂(γ ({1, 2} : Finset ℤ) ω), ξ 3 = ω 3 :=
      specification_ae_eq γ _ ω (by decide)
    have hstep : ∫⁻ ξ, ({σ : ℤ → E | σ 1 = x}).indicator 1 ξ * ENNReal.ofReal (g (ξ 1) y (ξ 3))
        ∂(γ ({1, 2} : Finset ℤ) ω)
        = ∫⁻ ξ, ({σ : ℤ → E | σ 1 = x}).indicator
            (fun _ ↦ ENNReal.ofReal (g x y z)) ξ ∂(γ ({1, 2} : Finset ℤ) ω) := by
      refine lintegral_congr_ae (hae.mono fun ξ hξ ↦ ?_)
      show ({σ : ℤ → E | σ 1 = x}).indicator 1 ξ * ENNReal.ofReal (g (ξ 1) y (ξ 3))
        = ({σ : ℤ → E | σ 1 = x}).indicator (fun _ ↦ ENNReal.ofReal (g x y z)) ξ
      by_cases hmem : ξ ∈ {σ : ℤ → E | σ 1 = x}
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Pi.one_apply, one_mul, hξ, hω3,
          show ξ 1 = x from hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
    rw [hbind, lintegral_congr hint, hstep,
      lintegral_indicator_const (measurableSet_eq_apply 1 x)]
  -- Real-valued versions.
  set R : E → ℝ := fun y ↦ (γ ({1, 2} : Finset ℤ) ω {σ : ℤ → E | σ 2 = y}).toReal with hRdef
  set K : E → ℝ := fun x ↦ (γ ({1, 2} : Finset ℤ) ω {σ : ℤ → E | σ 1 = x}).toReal with hKdef
  set c : E → E → ℝ := fun x y ↦ (b x y).toReal with hcdef
  have hc1 : ∀ x y, c x y = g a x y * R y := by
    intro x y
    rw [hcdef, hRdef]
    simp only
    rw [hF1 x y, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hγ.pos a x y).le]
  have hc2 : ∀ x y, c x y = g x y z * K x := by
    intro x y
    rw [hcdef, hKdef]
    simp only
    rw [hF2 x y, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hγ.pos x y z).le]
  have hRsum : ∀ y, R y = ∑ u, c u y := by
    intro y
    rw [hRdef]
    simp only
    rw [measure_eq_sum_inter _ 1 2 y,
      ENNReal.toReal_sum fun u _ ↦ measure_ne_top _ _]
  have hKsum : ∀ x, K x = ∑ v, c x v := by
    intro x
    rw [hKdef]
    simp only
    rw [measure_eq_sum_inter _ 2 1 x, ENNReal.toReal_sum fun v _ ↦ measure_ne_top _ _]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [hcdef]; simp only; rw [Set.inter_comm]
  have hKnonneg : ∀ x, 0 ≤ K x := fun x ↦ ENNReal.toReal_nonneg
  have hKtot : ∑ x, K x = 1 := by
    have h := measure_univ_eq_sum (γ ({1, 2} : Finset ℤ) ω) 1
    have h2 : ((∑ x, γ ({1, 2} : Finset ℤ) ω {σ : ℤ → E | σ 1 = x}) : ℝ≥0∞).toReal
        = (1 : ℝ≥0∞).toReal := by rw [h]
    rwa [ENNReal.toReal_sum fun x _ ↦ measure_ne_top _ _, ENNReal.toReal_one] at h2
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, 0 < K x₁ := by
    by_contra hcon
    push_neg at hcon
    have : ∑ x, K x = 0 :=
      Finset.sum_eq_zero fun x _ ↦ le_antisymm (hcon x) (hKnonneg x)
    rw [hKtot] at this
    exact one_ne_zero this
  have hRpos : ∀ y, 0 < R y := by
    intro y
    rw [hRsum y]
    refine Finset.sum_pos' (fun u _ ↦ ?_) ⟨x₁, Finset.mem_univ _, ?_⟩
    · rw [hc2 u y]
      exact mul_nonneg (hγ.pos u y z).le (hKnonneg u)
    · rw [hc2 x₁ y]
      exact mul_pos (hγ.pos x₁ y z) hx₁
  have hKpos : ∀ x, 0 < K x := by
    intro x
    rw [hKsum x]
    refine Finset.sum_pos (fun v _ ↦ ?_) Finset.univ_nonempty
    rw [hc1 x v]
    exact mul_pos (hγ.pos a x v) (hRpos v)
  have hcpos : ∀ x y, 0 < c x y := by
    intro x y
    rw [hc1 x y]
    exact mul_pos (hγ.pos a x y) (hRpos y)
  -- Georgii's ratios.
  have hratio1 : ∀ x y y', g x y z / g x y' z = c x y / c x y' := by
    intro x y y'
    rw [hc2 x y, hc2 x y']
    rw [mul_div_mul_right _ _ (hKpos x).ne']
  have hratio2 : ∀ x x' y, g a x y / g a x' y = c x y / c x' y := by
    intro x x' y
    rw [hc1 x y, hc1 x' y]
    rw [mul_div_mul_right _ _ (hRpos y).ne']
  rw [hratio1 x₀ y₀ a, hratio2 x₀ a a, hratio2 x₀ a y₀, hratio1 a y₀ a]
  have h1 : c x₀ a ≠ 0 := (hcpos x₀ a).ne'
  have h2 : c a a ≠ 0 := (hcpos a a).ne'
  have h3 : c a y₀ ≠ 0 := (hcpos a y₀).ne'
  field_simp

/-! ### The correspondence `γ ↔ P` (Georgii, Theorem (3.5)) -/

/-- **Georgii, Theorem (3.5), surjectivity of `ℓ : P ↦ γ`.** Every positive homogeneous Markov
specification on `ℤ` is the Gibbsian specification of a positive stochastic matrix `P`, which is
computed from the determining function by formula (3.7). -/
theorem exists_matrix_eq_markovSpecification {γ : Specification ℤ E}
    (hγ : IsPositiveHomogeneousMarkov γ) :
    ∃ (P : Matrix E E ℝ) (_hP : P ∈ Matrix.rowStochastic ℝ E) (_hpos : ∀ x y, 0 < P x y),
      γ = markovSpecification P := by
  obtain ⟨g, hg⟩ := hγ
  obtain ⟨a⟩ := ‹Nonempty E›
  refine ⟨matrixOfDetFun E g hg.pos a, matrixOfDetFun_mem_rowStochastic hg.pos a,
    matrixOfDetFun_pos hg.pos a, ?_⟩
  have hgP : g = markovDeterminingFun (matrixOfDetFun E g hg.pos a) :=
    (markovDeterminingFun_of_eq_312 hg.pos (fun x z ↦ sum_determiningFun_eq_one hg x z) a
      (Matrix.perronRoot_pos (detQ E g a) (detQ_pos hg.pos a))
      (Matrix.perronVector_pos (detQ E g a) (detQ_pos hg.pos a))
      (fun x y ↦ rfl) (eq_312_of_isPositiveHomogeneousMarkovWith hg a)).symm
  exact eq_markovSpecification_of_determiningFun (P := matrixOfDetFun E g hg.pos a)
    (matrixOfDetFun_pos hg.pos a) hg hgP

end Correspondence

/-!
## Existence: the stationary Markov chain `μ_P` (Georgii's step 1)

The remaining sections build the stationary Markov chain `μ_P` of (3.3) as a projective limit of
its finite-dimensional distributions and show that `μ_P ∈ 𝒢(markovSpecification P)`.
-/

/-! ### The singleton Boltzmann factor and the independent kernel on a singleton -/

section Singleton
variable (P : Matrix E E ℝ)

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Hamiltonian of `markovPotential P` in the singleton `{i}` consists of the two bonds
`{i-1, i}` and `{i, i+1}`. -/
lemma hamiltonian_singleton (i : ℤ) (σ : ℤ → E) :
    (markovPotential P).hamiltonian {i} σ =
      -Real.log (P (σ (i - 1)) (σ i)) - Real.log (P (σ i) (σ (i + 1))) := by
  rw [Potential.hamiltonian_eq_tsum]
  have hne : ({i - 1, i} : Finset ℤ) ≠ {i, i + 1} := by
    intro h
    have h' : ({i - 1, i - 1 + 1} : Finset ℤ) = {i, i + 1} := by
      rw [sub_add_cancel]; exact h
    have := pair_succ_inj h'
    omega
  have hsupp : ∀ A ∉ ({({i - 1, i} : Finset ℤ), {i, i + 1}} : Finset (Finset ℤ)),
      (markovPotential P).hamiltonianTerms {i} σ A = 0 := by
    intro A hA
    by_cases hd : Disjoint A {i}
    · exact Potential.hamiltonianTerms_of_disjoint hd σ
    · rw [Potential.hamiltonianTerms_of_not_disjoint hd σ]
      by_cases h : ∃ j : ℤ, A = {j, j + 1}
      · exfalso
        obtain ⟨j, rfl⟩ := h
        have hiA : i ∈ ({j, j + 1} : Finset ℤ) := by
          obtain ⟨a, ha, ha'⟩ := Finset.not_disjoint_iff.1 hd
          rw [Finset.mem_singleton] at ha'
          exact ha' ▸ ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
        rcases hiA with rfl | rfl
        · exact hA (by simp)
        · exact hA (by simp)
      · exact markovPotential_of_not_pair P h σ
  rw [tsum_eq_sum hsupp, Finset.sum_pair hne,
    Potential.hamiltonianTerms_of_not_disjoint (by simp) σ,
    Potential.hamiltonianTerms_of_not_disjoint (by simp) σ]
  have e1 : ({i - 1, i} : Finset ℤ) = {i - 1, i - 1 + 1} := by simp
  rw [e1, markovPotential_pair, markovPotential_pair, sub_add_cancel]
  ring

/-- The Boltzmann factor of `markovPotential P` in `{i}` at inverse temperature `1` is
`P(σ_{i-1}, σ_i) P(σ_i, σ_{i+1})`. -/
lemma boltzmannFactor_singleton (hpos : ∀ x y, 0 < P x y) (i : ℤ) (σ : ℤ → E) :
    (markovPotential P).boltzmannFactor 1 {i} σ =
      ENNReal.ofReal (P (σ (i - 1)) (σ i) * P (σ i) (σ (i + 1))) := by
  rw [Potential.boltzmannFactor, hamiltonian_singleton]
  congr 1
  have h1 := hpos (σ (i - 1)) (σ i)
  have h2 := hpos (σ i) (σ (i + 1))
  rw [show -(1 : ℝ) * (-Real.log (P (σ (i - 1)) (σ i)) - Real.log (P (σ i) (σ (i + 1)))) =
      Real.log (P (σ (i - 1)) (σ i)) + Real.log (P (σ i) (σ (i + 1))) by ring,
    Real.exp_add, Real.exp_log h1, Real.exp_log h2]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The independent kernel on a singleton resamples the single coordinate: `λ_{i}(·|ω)` is the
image of `ν` under `x ↦ update ω i x`. -/
lemma isssd_singleton_eq_map (ν : Measure E) [IsProbabilityMeasure ν] (i : ℤ) (ω : ℤ → E) :
    Specification.isssd (S := ℤ) ν {i} ω = ν.map (Function.update ω i) := by
  have hpi : (Measure.pi fun _ : (({i} : Finset ℤ) : Type) ↦ ν) =
      ν.map (MeasurableEquiv.funUnique (({i} : Finset ℤ) : Type) E).symm :=
    ((measurePreserving_funUnique ν _).symm _).map_eq.symm
  show Measure.map (juxt (({i} : Finset ℤ) : Set ℤ) ω)
    (Measure.pi fun _ : (({i} : Finset ℤ) : Type) ↦ ν) = _
  rw [hpi, Measure.map_map Measurable.juxt (MeasurableEquiv.measurable _)]
  congr 1
  funext y j
  simp only [Function.comp_apply, MeasurableEquiv.funUnique_symm_apply, Function.update_apply]
  by_cases hj : j = i
  · subst hj
    simp [juxt, uniqueElim_const]
  · simp [juxt, hj]

end Singleton

/-! ### Finite configurations: extension and cylinder sums -/

section CylSum

/-- Extend a configuration on a finite volume `Λ` to a full configuration, by an arbitrary
fixed value off `Λ`. -/
def extendBy (Λ : Finset ℤ) (x : Π _k : Λ, E) : ℤ → E := fun i ↦
  if h : i ∈ Λ then x ⟨i, h⟩ else Classical.arbitrary E

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma extendBy_of_mem {Λ : Finset ℤ} {i : ℤ} (x : Π _k : Λ, E) (h : i ∈ Λ) :
    extendBy Λ x i = x ⟨i, h⟩ := dite_eq_left h

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma extendBy_of_notMem {Λ : Finset ℤ} {i : ℤ} (x : Π _k : Λ, E) (h : i ∉ Λ) :
    extendBy Λ x i = Classical.arbitrary E := dite_eq_right h

@[simp] lemma restrict_extendBy (Λ : Finset ℤ) (x : Π _k : Λ, E) :
    Λ.restrict (extendBy Λ x) = x := by
  funext k
  exact dite_eq_left k.2

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma restrict_update_of_notMem {Λ : Finset ℤ} {j : ℤ} (h : j ∉ Λ) (σ : ℤ → E) (z : E) :
    Λ.restrict (Function.update σ j z) = Λ.restrict σ := by
  funext k
  exact Function.update_of_ne (ne_of_mem_of_not_mem k.2 h) z σ

/-- The sum of `G` over all configurations supported on the finite volume `Δ`. -/
def cylSum (Δ : Finset ℤ) (G : (ℤ → E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ x : Π _k : Δ, E, G (extendBy Δ x)

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_congr {Δ₁ Δ₂ : Finset ℤ} (h : Δ₁ = Δ₂) (G : (ℤ → E) → ℝ≥0∞) :
    cylSum Δ₁ G = cylSum Δ₂ G := by subst h; rfl

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_congr_fun {Δ : Finset ℤ} {G₁ G₂ : (ℤ → E) → ℝ≥0∞} (h : ∀ σ, G₁ σ = G₂ σ) :
    cylSum Δ G₁ = cylSum Δ G₂ :=
  Finset.sum_congr rfl fun _ _ ↦ h _

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_sum {ι : Type*} (Δ : Finset ℤ) (s : Finset ι) (H : ι → (ℤ → E) → ℝ≥0∞) :
    cylSum Δ (fun σ ↦ ∑ z ∈ s, H z σ) = ∑ z ∈ s, cylSum Δ (H z) :=
  Finset.sum_comm

/-- Splitting off the coordinate `j` of a dependent product over `insert j Δ`. -/
def insertPiEquiv (Δ : Finset ℤ) (j : ℤ) (hj : j ∉ Δ) :
    (Π _k : (insert j Δ : Finset ℤ), E) ≃ (Π _k : Δ, E) × E where
  toFun x := (fun k ↦ x ⟨↑k, Finset.mem_insert_of_mem k.2⟩, x ⟨j, Finset.mem_insert_self j Δ⟩)
  invFun p := fun k ↦ if h : (k : ℤ) ∈ Δ then p.1 ⟨↑k, h⟩ else p.2
  left_inv x := by
    funext k
    obtain ⟨k, hk⟩ := k
    by_cases h : k ∈ Δ
    · simp only [dite_eq_left h]
    · have hkj : k = j := by
        rcases Finset.mem_insert.1 hk with h' | h'
        · exact h'
        · exact absurd h' h
      subst hkj
      simp only [dite_eq_right h]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext k
      exact dite_eq_left k.2
    · exact dite_eq_right hj

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma extendBy_insertPiEquiv_symm {Δ : Finset ℤ} {j : ℤ} (hj : j ∉ Δ) (y : Π _k : Δ, E) (z : E) :
    extendBy (insert j Δ) ((insertPiEquiv Δ j hj).symm (y, z))
      = Function.update (extendBy Δ y) j z := by
  funext i
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, extendBy_of_mem _ (Finset.mem_insert_self i Δ)]
    exact dite_eq_right hj
  · rw [Function.update_of_ne hij]
    by_cases hiΔ : i ∈ Δ
    · rw [extendBy_of_mem _ (Finset.mem_insert_of_mem hiΔ), extendBy_of_mem _ hiΔ]
      exact dite_eq_left hiΔ
    · have hins : i ∉ insert j Δ := by simp [hij, hiΔ]
      rw [extendBy_of_notMem _ hins, extendBy_of_notMem _ hiΔ]

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_insert {Δ : Finset ℤ} {j : ℤ} (hj : j ∉ Δ) (G : (ℤ → E) → ℝ≥0∞) :
    cylSum (insert j Δ) G = ∑ z : E, cylSum Δ fun σ ↦ G (Function.update σ j z) := by
  rw [cylSum, ← Equiv.sum_comp (insertPiEquiv Δ j hj).symm
    (fun x ↦ G (extendBy (insert j Δ) x)), Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ Finset.sum_congr rfl fun y _ ↦ ?_
  rw [extendBy_insertPiEquiv_symm hj y z]

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_empty (G : (ℤ → E) → ℝ≥0∞) :
    cylSum ∅ G = G (fun _ ↦ Classical.arbitrary E) := by
  have : IsEmpty ((∅ : Finset ℤ) : Type) := ⟨fun k ↦ absurd k.2 (Finset.notMem_empty _)⟩
  have : Unique (Π _k : ((∅ : Finset ℤ) : Type), E) := Pi.uniqueOfIsEmpty _
  rw [cylSum, Fintype.sum_unique (fun x : Π _k : ((∅ : Finset ℤ) : Type), E ↦
    G (extendBy ∅ x))]
  congr 1

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma cylSum_singleton (j : ℤ) (G : (ℤ → E) → ℝ≥0∞) :
    cylSum {j} G = ∑ z : E, G (Function.update (fun _ ↦ Classical.arbitrary E) j z) := by
  have h : ({j} : Finset ℤ) = insert j ∅ := rfl
  rw [cylSum_congr h, cylSum_insert (Finset.notMem_empty j)]
  exact Finset.sum_congr rfl fun z _ ↦ by rw [cylSum_empty]

/-- Collapse a cylinder sum against the indicator of a single configuration. -/
lemma cylSum_mul_indicator_singleton (Δ : Finset ℤ) (F : (ℤ → E) → ℝ≥0∞) (x : Π _k : Δ, E) :
    cylSum Δ (fun σ ↦ F σ * ({x} : Set (Π _k : Δ, E)).indicator 1 (Δ.restrict σ))
      = F (extendBy Δ x) := by
  rw [cylSum]
  have h : ∀ y : Π _k : Δ, E,
      F (extendBy Δ y) * ({x} : Set (Π _k : Δ, E)).indicator 1 (Δ.restrict (extendBy Δ y))
        = if y = x then F (extendBy Δ y) else 0 := by
    intro y
    rw [restrict_extendBy]
    by_cases h : y = x
    · simp [h]
    · simp [Set.indicator_of_notMem, h]
  rw [Finset.sum_congr rfl fun y _ ↦ h y,
    Finset.sum_ite_eq' Finset.univ x (fun y ↦ F (extendBy Δ y))]
  simp

end CylSum


/-! ### The weights of the stationary chain (Georgii (3.3)) -/

section ChainWeight
variable (P : Matrix E E ℝ) (α : E → ℝ)

/-- The weight `α(σ_a) P(σ_a, σ_{a+1}) ⋯ P(σ_{b-1}, σ_b)` of a configuration on `[a, b]`
(Georgii (3.3)). -/
def chainWeight (a b : ℤ) (σ : ℤ → E) : ℝ :=
  α (σ a) * ∏ k ∈ Finset.Ico a b, P (σ k) (σ (k + 1))

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma chainWeight_nonneg (hPnn : ∀ x y, 0 ≤ P x y) (hαnn : ∀ x, 0 ≤ α x) (a b : ℤ)
    (σ : ℤ → E) : 0 ≤ chainWeight P α a b σ :=
  mul_nonneg (hαnn _) (Finset.prod_nonneg fun _ _ ↦ hPnn _ _)

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma chainWeight_congr {a b : ℤ} (hab : a ≤ b) {σ τ : ℤ → E}
    (h : ∀ k ∈ Finset.Icc a b, σ k = τ k) :
    chainWeight P α a b σ = chainWeight P α a b τ := by
  rw [chainWeight, chainWeight, h a (by simp [Finset.mem_Icc]; omega),
    Finset.prod_congr rfl fun k hk ↦ ?_]
  simp only [Finset.mem_Ico] at hk
  rw [h k (by simp [Finset.mem_Icc]; omega), h (k + 1) (by simp [Finset.mem_Icc]; omega)]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma chainWeight_update_right {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) (z : E) :
    chainWeight P α a (b + 1) (Function.update σ (b + 1) z)
      = chainWeight P α a b σ * P (σ b) z := by
  have hIco : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  rw [chainWeight, chainWeight, hIco,
    Finset.prod_insert (by simp only [Finset.mem_Ico]; omega),
    Function.update_of_ne (by omega : (b : ℤ) ≠ b + 1), Function.update_self,
    Function.update_of_ne (by omega : (a : ℤ) ≠ b + 1),
    Finset.prod_congr rfl fun k hk ↦ ?_]
  · ring
  · simp only [Finset.mem_Ico] at hk
    rw [Function.update_of_ne (by omega : (k : ℤ) ≠ b + 1),
      Function.update_of_ne (by omega : (k + 1 : ℤ) ≠ b + 1)]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma chainWeight_update_left {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) (z : E) :
    chainWeight P α (a - 1) b (Function.update σ (a - 1) z)
      = α z * P z (σ a) * ∏ k ∈ Finset.Ico a b, P (σ k) (σ (k + 1)) := by
  have hIco : Finset.Ico (a - 1) b = insert (a - 1) (Finset.Ico a b) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have ha1 : (a - 1 + 1 : ℤ) = a := by omega
  rw [chainWeight, hIco, Finset.prod_insert (by simp only [Finset.mem_Ico]; omega), ha1,
    Function.update_self, Function.update_of_ne (by omega : (a : ℤ) ≠ a - 1),
    Finset.prod_congr rfl fun k hk ↦ ?_]
  · ring
  · simp only [Finset.mem_Ico] at hk
    rw [Function.update_of_ne (by omega : (k : ℤ) ≠ a - 1),
      Function.update_of_ne (by omega : (k + 1 : ℤ) ≠ a - 1)]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The interior factorisation of the chain weight: the two bonds at `i` split off. -/
lemma chainWeight_eq_middle {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) :
    chainWeight P α a b σ
      = α (σ a) * (P (σ (i - 1)) (σ i) * (P (σ i) (σ (i + 1))
          * ∏ k ∈ ((Finset.Ico a b).erase (i - 1)).erase i, P (σ k) (σ (k + 1)))) := by
  have h1 : (i - 1 : ℤ) ∈ Finset.Ico a b := by simp only [Finset.mem_Ico]; omega
  have h2 : i ∈ (Finset.Ico a b).erase (i - 1) := by
    simp only [Finset.mem_erase, Finset.mem_Ico]; omega
  have hi1 : (i - 1 + 1 : ℤ) = i := by omega
  rw [chainWeight, ← Finset.mul_prod_erase _ _ h1, ← Finset.mul_prod_erase _ _ h2, hi1]

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The interior factorisation of the chain weight after resampling the coordinate `i`. -/
lemma chainWeight_update_middle {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) (z : E) :
    chainWeight P α a b (Function.update σ i z)
      = α (σ a) * (P (σ (i - 1)) z * (P z (σ (i + 1))
          * ∏ k ∈ ((Finset.Ico a b).erase (i - 1)).erase i, P (σ k) (σ (k + 1)))) := by
  rw [chainWeight_eq_middle P α hai hib,
    Function.update_of_ne (by omega : (a : ℤ) ≠ i),
    Function.update_of_ne (by omega : (i - 1 : ℤ) ≠ i), Function.update_self,
    Function.update_of_ne (by omega : (i + 1 : ℤ) ≠ i),
    Finset.prod_congr rfl fun k hk ↦ ?_]
  simp only [Finset.mem_erase] at hk
  rw [Function.update_of_ne hk.1, Function.update_of_ne (fun h ↦ hk.2.1 (by omega))]

end ChainWeight


/-! ### Finite-volume distributions of the chain -/

section ChainAux
variable (P : Matrix E E ℝ) (α : E → ℝ)

open scoped Matrix

/-- The auxiliary finite-volume measure of the chain on `[a, b]`: the sum of Dirac masses at
the configurations supported on `[a, b]`, weighted by `chainWeight` (Georgii (3.3)). -/
def chainAux (a b : ℤ) : Measure (ℤ → E) :=
  ∑ x : Π _k : (Finset.Icc a b : Finset ℤ), E,
    ENNReal.ofReal (chainWeight P α a b (extendBy (Finset.Icc a b) x)) •
      Measure.dirac (extendBy (Finset.Icc a b) x)

omit [DecidableEq E] [MeasurableSingletonClass E] in
lemma chainAux_apply {a b : ℤ} {S : Set (ℤ → E)} (hS : MeasurableSet S) :
    chainAux P α a b S
      = cylSum (Finset.Icc a b)
          (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * S.indicator 1 σ) := by
  rw [chainAux, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]

variable {P} {α}
variable (hPnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hαnn : ∀ x, 0 ≤ α x)
  (hstat : α ᵥ* P = α)

include hPnn hrow hαnn in
/-- Dropping the right endpoint of the interval (`∑_y P(x, y) = 1`). -/
lemma cylSum_chainWeight_insert_right {a b : ℤ} (hab : a ≤ b) {G : (ℤ → E) → ℝ≥0∞}
    (hG : ∀ σ z, G (Function.update σ (b + 1) z) = G σ) :
    cylSum (Finset.Icc a (b + 1)) (fun σ ↦ ENNReal.ofReal (chainWeight P α a (b + 1) σ) * G σ)
      = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ) := by
  have hIcc : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [cylSum_congr hIcc, cylSum_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [← cylSum_sum (Finset.Icc a b) Finset.univ
    (fun z σ ↦ ENNReal.ofReal (chainWeight P α a (b + 1) (Function.update σ (b + 1) z))
      * G (Function.update σ (b + 1) z))]
  refine cylSum_congr_fun fun σ ↦ ?_
  have hz : ∀ z : E,
      ENNReal.ofReal (chainWeight P α a (b + 1) (Function.update σ (b + 1) z))
          * G (Function.update σ (b + 1) z)
        = ENNReal.ofReal (chainWeight P α a b σ * P (σ b) z) * G σ := fun z ↦ by
    rw [chainWeight_update_right P α hab, hG]
  rw [Finset.sum_congr rfl fun z _ ↦ hz z, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg fun z _ ↦
      mul_nonneg (chainWeight_nonneg P α hPnn hαnn a b σ) (hPnn _ _),
    ← Finset.mul_sum, hrow, mul_one]

include hPnn hrow hαnn hstat in
/-- Dropping the left endpoint of the interval (stationarity `α P = α`). -/
lemma cylSum_chainWeight_insert_left {a b : ℤ} (hab : a ≤ b) {G : (ℤ → E) → ℝ≥0∞}
    (hG : ∀ σ z, G (Function.update σ (a - 1) z) = G σ) :
    cylSum (Finset.Icc (a - 1) b) (fun σ ↦ ENNReal.ofReal (chainWeight P α (a - 1) b σ) * G σ)
      = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ) := by
  have hIcc : Finset.Icc (a - 1) b = insert (a - 1) (Finset.Icc a b) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [cylSum_congr hIcc, cylSum_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [← cylSum_sum (Finset.Icc a b) Finset.univ
    (fun z σ ↦ ENNReal.ofReal (chainWeight P α (a - 1) b (Function.update σ (a - 1) z))
      * G (Function.update σ (a - 1) z))]
  refine cylSum_congr_fun fun σ ↦ ?_
  have hz : ∀ z : E,
      ENNReal.ofReal (chainWeight P α (a - 1) b (Function.update σ (a - 1) z))
          * G (Function.update σ (a - 1) z)
        = ENNReal.ofReal (α z * P z (σ a) * ∏ k ∈ Finset.Ico a b, P (σ k) (σ (k + 1)))
            * G σ := fun z ↦ by
    rw [chainWeight_update_left P α hab, hG]
  rw [Finset.sum_congr rfl fun z _ ↦ hz z, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg fun z _ ↦
      mul_nonneg (mul_nonneg (hαnn _) (hPnn _ _)) (Finset.prod_nonneg fun _ _ ↦ hPnn _ _)]
  congr 2
  have hsum : ∑ z, α z * P z (σ a) = α (σ a) := by
    have h := congrFun hstat (σ a)
    rw [← h]
    simp [Matrix.vecMul, dotProduct]
  rw [chainWeight, ← hsum, Finset.sum_mul]

include hPnn hrow hαnn hstat in
/-- Growing the interval does not change cylinder sums against functions supported in the
smaller interval. -/
lemma cylSum_chainWeight_grow {a b a' b' : ℤ} (hab : a ≤ b) (ha' : a' ≤ a) (hb' : b ≤ b')
    {G : (ℤ → E) → ℝ≥0∞}
    (hG : ∀ j ∉ Finset.Icc a b, ∀ σ z, G (Function.update σ j z) = G σ) :
    cylSum (Finset.Icc a' b') (fun σ ↦ ENNReal.ofReal (chainWeight P α a' b' σ) * G σ)
      = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ) := by
  have hright : ∀ n : ℕ,
      cylSum (Finset.Icc a (b + n)) (fun σ ↦ ENNReal.ofReal (chainWeight P α a (b + n) σ) * G σ)
        = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have h1 : (b + (n + 1 : ℕ) : ℤ) = (b + n) + 1 := by push_cast; ring
        rw [h1, cylSum_chainWeight_insert_right hPnn hrow hαnn (by omega)
          (fun σ z ↦ hG _ (by simp only [Finset.mem_Icc]; omega) σ z)]
        exact ih
  have hleft : ∀ (m : ℕ) (b'' : ℤ), b ≤ b'' →
      (cylSum (Finset.Icc a b'') (fun σ ↦ ENNReal.ofReal (chainWeight P α a b'' σ) * G σ)
        = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ)) →
      cylSum (Finset.Icc (a - m) b'')
          (fun σ ↦ ENNReal.ofReal (chainWeight P α (a - m) b'' σ) * G σ)
        = cylSum (Finset.Icc a b) (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * G σ) := by
    intro m
    induction m with
    | zero => intro b'' _ h; simpa using h
    | succ m ih =>
        intro b'' hb'' h
        have h1 : (a - (m + 1 : ℕ) : ℤ) = (a - m) - 1 := by push_cast; ring
        rw [h1, cylSum_chainWeight_insert_left hPnn hrow hαnn hstat (by omega)
          (fun σ z ↦ hG _ (by simp only [Finset.mem_Icc]; omega) σ z)]
        exact ih b'' hb'' h
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b' = b + n := ⟨(b' - b).toNat, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a' = a - m := ⟨(a - a').toNat, by omega⟩
  exact hleft m (b + n) (by omega) (hright n)

include hPnn hrow hαnn hstat in
/-- Cylinder consistency of the auxiliary measures: on a cylinder event over `Λ`, all
intervals containing `Λ` give the same value. -/
lemma chainAux_restrict_congr {a b a' b' : ℤ} (hab : a ≤ b) (ha'b' : a' ≤ b') {Λ : Finset ℤ}
    (hΛ : Λ ⊆ Finset.Icc a b) (hΛ' : Λ ⊆ Finset.Icc a' b') {A : Set (Π _k : Λ, E)}
    (hA : MeasurableSet A) :
    chainAux P α a b (Λ.restrict ⁻¹' A) = chainAux P α a' b' (Λ.restrict ⁻¹' A) := by
  have hpre : MeasurableSet (Λ.restrict ⁻¹' A : Set (ℤ → E)) :=
    Finset.measurable_restrict Λ hA
  rw [chainAux_apply P α hpre, chainAux_apply P α hpre]
  have hGinv : ∀ (Δ : Finset ℤ), Λ ⊆ Δ → ∀ j ∉ Δ, ∀ (σ : ℤ → E) (z : E),
      (Λ.restrict ⁻¹' A).indicator (1 : (ℤ → E) → ℝ≥0∞) (Function.update σ j z)
        = (Λ.restrict ⁻¹' A).indicator 1 σ := by
    intro Δ hΛΔ j hj σ z
    classical
    have hjΛ : j ∉ Λ := fun hjΛ ↦ hj (hΛΔ hjΛ)
    have hmem : Function.update σ j z ∈ Λ.restrict ⁻¹' A ↔ σ ∈ Λ.restrict ⁻¹' A := by
      simp only [Set.mem_preimage, restrict_update_of_notMem hjΛ]
    rw [Set.indicator_apply, Set.indicator_apply, if_congr hmem rfl rfl]
    simp
  have h1 := cylSum_chainWeight_grow hPnn hrow hαnn hstat hab
    (min_le_left a a') (le_max_left b b') (G := (Λ.restrict ⁻¹' A).indicator 1)
    (hGinv (Finset.Icc a b) hΛ)
  have h2 := cylSum_chainWeight_grow hPnn hrow hαnn hstat ha'b'
    (min_le_right a a') (le_max_right b b') (G := (Λ.restrict ⁻¹' A).indicator 1)
    (hGinv (Finset.Icc a' b') hΛ')
  rw [← h1, ← h2]

include hPnn hrow hαnn hstat in
/-- The auxiliary measures are probability measures (`hsum : ∑ x, α x = 1`). -/
lemma chainAux_univ (hsum : ∑ x, α x = 1) {a b : ℤ} (hab : a ≤ b) :
    chainAux P α a b Set.univ = 1 := by
  rw [chainAux_apply P α MeasurableSet.univ]
  have h1 : cylSum (Finset.Icc a b)
      (fun σ ↦ ENNReal.ofReal (chainWeight P α a b σ) * Set.univ.indicator 1 σ)
        = cylSum (Finset.Icc a a)
          (fun σ ↦ ENNReal.ofReal (chainWeight P α a a σ) * Set.univ.indicator 1 σ) :=
    cylSum_chainWeight_grow hPnn hrow hαnn hstat le_rfl le_rfl hab
      (G := Set.univ.indicator 1) (fun _ _ _ _ ↦ by simp)
  rw [h1, cylSum_congr (Finset.Icc_self a), cylSum_singleton]
  have h2 : ∀ z : E,
      ENNReal.ofReal
          (chainWeight P α a a (Function.update (fun _ ↦ Classical.arbitrary E) a z))
        * Set.univ.indicator 1 (Function.update (fun _ ↦ Classical.arbitrary E) a z)
      = ENNReal.ofReal (α z) := by
    intro z
    rw [chainWeight, Finset.Ico_self, Finset.prod_empty, Function.update_self, mul_one]
    simp
  rw [Finset.sum_congr rfl fun z _ ↦ h2 z, ← ENNReal.ofReal_sum_of_nonneg fun z _ ↦ hαnn z,
    hsum, ENNReal.ofReal_one]

end ChainAux


/-! ### The projective family of finite-dimensional distributions -/

section FinDist
variable (P : Matrix E E ℝ) (α : E → ℝ)

open scoped Matrix

/-- A symmetric interval bound for a finite volume: `Λ ⊆ [-boundOf Λ, boundOf Λ]`. -/
def boundOf (Λ : Finset ℤ) : ℤ := ((Λ.sup fun i ↦ i.natAbs : ℕ) : ℤ)

lemma boundOf_nonneg (Λ : Finset ℤ) : 0 ≤ boundOf Λ := Int.natCast_nonneg _

lemma subset_Icc_boundOf (Λ : Finset ℤ) : Λ ⊆ Finset.Icc (-boundOf Λ) (boundOf Λ) := by
  intro i hi
  have h := Finset.le_sup (f := fun j : ℤ ↦ j.natAbs) hi
  simp only [Finset.mem_Icc, boundOf]
  omega

/-- The finite-dimensional distribution of the stationary chain on the volume `Λ`
(Georgii (3.3)): restrict the interval measure of any interval containing `Λ` to `Λ`. -/
def finDist (Λ : Finset ℤ) : Measure (Π _k : Λ, E) :=
  (chainAux P α (-boundOf Λ) (boundOf Λ)).map Λ.restrict

omit [DecidableEq E] [MeasurableSingletonClass E] in
lemma finDist_apply {Λ : Finset ℤ} {A : Set (Π _k : Λ, E)} (hA : MeasurableSet A) :
    finDist P α Λ A = chainAux P α (-boundOf Λ) (boundOf Λ) (Λ.restrict ⁻¹' A) :=
  Measure.map_apply (Finset.measurable_restrict Λ) hA

variable {P α}
variable (hPnn : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1) (hαnn : ∀ x, 0 ≤ α x)
  (hstat : α ᵥ* P = α)

include hPnn hrow hαnn hstat in
lemma finDist_eq_chainAux {Λ : Finset ℤ} {a b : ℤ} (hab : a ≤ b) (hΛ : Λ ⊆ Finset.Icc a b)
    {A : Set (Π _k : Λ, E)} (hA : MeasurableSet A) :
    finDist P α Λ A = chainAux P α a b (Λ.restrict ⁻¹' A) := by
  rw [finDist_apply P α hA]
  exact chainAux_restrict_congr hPnn hrow hαnn hstat
    (by have := boundOf_nonneg Λ; omega) hab (subset_Icc_boundOf Λ) hΛ hA

include hPnn hrow hαnn hstat in
/-- The finite-dimensional distributions form a projective family. -/
lemma isProjectiveMeasureFamily_finDist :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ E) (finDist P α) := by
  intro I J hJI
  refine Measure.ext fun A hA ↦ ?_
  have hIab : (-boundOf I : ℤ) ≤ boundOf I := by have := boundOf_nonneg I; omega
  have h1 : finDist P α J A = chainAux P α (-boundOf I) (boundOf I) (J.restrict ⁻¹' A) :=
    finDist_eq_chainAux hPnn hrow hαnn hstat hIab (hJI.trans (subset_Icc_boundOf I)) hA
  have h3 : (I.restrict ⁻¹' (Finset.restrict₂ (π := fun _ : ℤ ↦ E) hJI ⁻¹' A) : Set (ℤ → E))
      = J.restrict ⁻¹' A := by
    rw [← Set.preimage_comp, Finset.restrict₂_comp_restrict]
  have h4 : Measure.map (Finset.restrict₂ (π := fun _ : ℤ ↦ E) hJI) (finDist P α I) A
      = chainAux P α (-boundOf I) (boundOf I) (J.restrict ⁻¹' A) := by
    rw [Measure.map_apply (Finset.measurable_restrict₂ (X := fun _ : ℤ ↦ E) hJI) hA,
      finDist_eq_chainAux hPnn hrow hαnn hstat hIab (subset_Icc_boundOf I)
        (Finset.measurable_restrict₂ (X := fun _ : ℤ ↦ E) hJI hA), h3]
  exact h1.trans h4.symm

include hPnn hrow hαnn hstat in
lemma isProbabilityMeasure_finDist (hsum : ∑ x, α x = 1) (Λ : Finset ℤ) :
    IsProbabilityMeasure (finDist P α Λ) := by
  constructor
  rw [finDist_apply P α MeasurableSet.univ, Set.preimage_univ]
  exact chainAux_univ hPnn hrow hαnn hstat hsum (by have := boundOf_nonneg Λ; omega)

end FinDist


/-! ### The stationary Markov chain `μ_P` (Georgii (3.3)) -/

section StationaryChain
variable (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

open scoped Matrix

/-- The stationary distribution `α_P` of a positive stochastic matrix (Georgii (3.3),
Appendix 3.A). -/
def stationaryDist : E → ℝ := (Matrix.exists_stationary P hP hpos).choose

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma stationaryDist_mem_stdSimplex : stationaryDist P hP hpos ∈ stdSimplex ℝ E :=
  (Matrix.exists_stationary P hP hpos).choose_spec.1

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma vecMul_stationaryDist : stationaryDist P hP hpos ᵥ* P = stationaryDist P hP hpos :=
  (Matrix.exists_stationary P hP hpos).choose_spec.2

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma stationaryDist_pos (y : E) : 0 < stationaryDist P hP hpos y :=
  Matrix.pos_of_vecMul_eq_self P hpos (stationaryDist_mem_stdSimplex P hP hpos)
    (vecMul_stationaryDist P hP hpos) y

lemma exists_stationaryChain :
    ∃ μ : Measure (ℤ → E), IsProjectiveLimit μ (finDist P (stationaryDist P hP hpos)) := by
  have : ∀ Λ : Finset ℤ, IsFiniteMeasure (finDist P (stationaryDist P hP hpos) Λ) := fun Λ ↦
    haveI := isProbabilityMeasure_finDist (fun x y ↦ (hpos x y).le)
      (fun x ↦ Matrix.sum_row_of_mem_rowStochastic hP x)
      (stationaryDist_mem_stdSimplex P hP hpos).1 (vecMul_stationaryDist P hP hpos)
      (stationaryDist_mem_stdSimplex P hP hpos).2 Λ
    inferInstance
  exact exists_isProjectiveLimit_of_standardBorel
    (isProjectiveMeasureFamily_finDist (fun x y ↦ (hpos x y).le)
      (fun x ↦ Matrix.sum_row_of_mem_rowStochastic hP x)
      (stationaryDist_mem_stdSimplex P hP hpos).1 (vecMul_stationaryDist P hP hpos))

/-- Georgii (3.3): the distribution `μ_P` of the unique stationary Markov chain with
transition matrix `P`, obtained from its finite-dimensional distributions by the Kolmogorov
extension theorem. -/
def stationaryChain : Measure (ℤ → E) := (exists_stationaryChain P hP hpos).choose

lemma isProjectiveLimit_stationaryChain :
    IsProjectiveLimit (stationaryChain P hP hpos) (finDist P (stationaryDist P hP hpos)) :=
  (exists_stationaryChain P hP hpos).choose_spec

lemma isProbabilityMeasure_stationaryChain :
    IsProbabilityMeasure (stationaryChain P hP hpos) := by
  constructor
  have h := isProjectiveLimit_stationaryChain P hP hpos (∅ : Finset ℤ)
  have := isProbabilityMeasure_finDist (P := P) (α := stationaryDist P hP hpos)
    (fun x y ↦ (hpos x y).le) (fun x ↦ Matrix.sum_row_of_mem_rowStochastic hP x)
    (stationaryDist_mem_stdSimplex P hP hpos).1 (vecMul_stationaryDist P hP hpos)
    (stationaryDist_mem_stdSimplex P hP hpos).2 (∅ : Finset ℤ)
  calc stationaryChain P hP hpos Set.univ
      = ((stationaryChain P hP hpos).map (∅ : Finset ℤ).restrict) Set.univ := by
        rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) _)
          MeasurableSet.univ, Set.preimage_univ]
    _ = finDist P (stationaryDist P hP hpos) ∅ Set.univ := by rw [h]
    _ = 1 := measure_univ

/-- On a cylinder event over `Λ ⊆ [a, b]`, the chain `μ_P` is computed by the interval
measure `chainAux`. -/
lemma stationaryChain_restrict_preimage {a b : ℤ} (hab : a ≤ b) {Λ : Finset ℤ}
    (hΛ : Λ ⊆ Finset.Icc a b) {A : Set (Π _k : Λ, E)} (hA : MeasurableSet A) :
    stationaryChain P hP hpos (Λ.restrict ⁻¹' A)
      = chainAux P (stationaryDist P hP hpos) a b (Λ.restrict ⁻¹' A) := by
  have h := isProjectiveLimit_stationaryChain P hP hpos Λ
  calc stationaryChain P hP hpos (Λ.restrict ⁻¹' A)
      = ((stationaryChain P hP hpos).map Λ.restrict) A :=
        (Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) Λ) hA).symm
    _ = finDist P (stationaryDist P hP hpos) Λ A := by rw [h]
    _ = chainAux P (stationaryDist P hP hpos) a b (Λ.restrict ⁻¹' A) :=
        finDist_eq_chainAux (fun x y ↦ (hpos x y).le)
          (fun x ↦ Matrix.sum_row_of_mem_rowStochastic hP x)
          (stationaryDist_mem_stdSimplex P hP hpos).1 (vecMul_stationaryDist P hP hpos)
          hab hΛ hA

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma indicator_preimage_restrict (Λ : Finset ℤ) (A : Set (Π _k : Λ, E)) (σ : ℤ → E) :
    (Λ.restrict ⁻¹' A).indicator (1 : (ℤ → E) → ℝ≥0∞) σ = A.indicator 1 (Λ.restrict σ) := by
  classical
  simp [Set.indicator_apply, Set.mem_preimage]

/-- The chain measure of a one-point cylinder over an interval. -/
lemma stationaryChain_intervalCylinder {a b : ℤ} (hab : a ≤ b)
    (x : Π _k : (Finset.Icc a b : Finset ℤ), E) :
    stationaryChain P hP hpos ((Finset.Icc a b).restrict ⁻¹' {x})
      = ENNReal.ofReal
          (chainWeight P (stationaryDist P hP hpos) a b (extendBy (Finset.Icc a b) x)) := by
  rw [stationaryChain_restrict_preimage P hP hpos hab subset_rfl (measurableSet_singleton x),
    chainAux_apply _ _ (Finset.measurable_restrict _ (measurableSet_singleton x)),
    cylSum_congr_fun fun σ ↦ by
      rw [indicator_preimage_restrict (Finset.Icc a b) {x} σ],
    cylSum_mul_indicator_singleton]

/-- **Georgii (3.3)**: the finite-dimensional distributions of `μ_P` on intervals:
`μ_P(σ_a = x_a, …, σ_b = x_b) = α_P(x_a) P(x_a, x_{a+1}) ⋯ P(x_{b-1}, x_b)`. -/
theorem markovChain_cylinder {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) :
    stationaryChain P hP hpos {τ : ℤ → E | ∀ k ∈ Finset.Icc a b, τ k = σ k}
      = ENNReal.ofReal (stationaryDist P hP hpos (σ a)
          * ∏ k ∈ Finset.Ico a b, P (σ k) (σ (k + 1))) := by
  have hset : {τ : ℤ → E | ∀ k ∈ Finset.Icc a b, τ k = σ k}
      = (Finset.Icc a b).restrict ⁻¹'
          ({(Finset.Icc a b).restrict σ} : Set (Π _k : (Finset.Icc a b : Finset ℤ), E)) := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
    constructor
    · intro h k
      exact h ↑k k.2
    · intro h k hk
      exact h ⟨k, hk⟩
  rw [hset, stationaryChain_intervalCylinder P hP hpos hab]
  congr 1
  exact chainWeight_congr P _ hab fun k hk ↦ by rw [extendBy_of_mem _ hk]; rfl

/-- Every cylinder event has positive `μ_P`-measure: `α_P` and `P` are strictly positive. -/
lemma stationaryChain_cyl_pos (Λ : Finset ℤ) (ω : ℤ → E) :
    0 < stationaryChain P hP hpos (cyl Λ ω) := by
  obtain ⟨a, b, hab, hΛ⟩ : ∃ a b : ℤ, a ≤ b ∧ Λ ⊆ Finset.Icc a b := by
    refine ⟨-boundOf Λ, boundOf Λ, ?_, subset_Icc_boundOf Λ⟩
    have := boundOf_nonneg Λ
    omega
  calc (0 : ℝ≥0∞)
      < ENNReal.ofReal (chainWeight P (stationaryDist P hP hpos) a b ω) := by
        rw [ENNReal.ofReal_pos]
        exact mul_pos (stationaryDist_pos P hP hpos _)
          (Finset.prod_pos fun _ _ ↦ hpos _ _)
    _ = stationaryChain P hP hpos (cyl (Finset.Icc a b) ω) :=
        (markovChain_cylinder P hP hpos hab ω).symm
    _ ≤ stationaryChain P hP hpos (cyl Λ ω) :=
        measure_mono fun σ hσ k hk ↦ hσ k (hΛ hk)

end StationaryChain

/-! ### The singleton densities of the Markov specification with respect to `isssd ν` -/

section Density
variable (P : Matrix E E ℝ)

/-- The partition function of the Boltzmann factor in the singleton `{i}` is
`P²(ω_{i-1}, ω_{i+1}) / |E|`. -/
lemma premodifierZ_singleton (hpos : ∀ x y, 0 < P x y) (i : ℤ) (ω : ℤ → E) :
    Specification.premodifierZ (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1) {i} ω
      = ENNReal.ofReal ((P ^ 2) (ω (i - 1)) (ω (i + 1))) * (Fintype.card E : ℝ≥0∞)⁻¹ := by
  set ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞ := (markovPotential P).boltzmannFactor 1 with hρ
  have hpre : Specification.IsPremodifier ρ := Potential.isPremodifier_boltzmannFactor 1
  have hupd : Measurable (Function.update ω i) := measurable_update ω
  set c : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹ with hc
  have hρi : ∀ x : E, ρ {i} (Function.update ω i x) =
      ENNReal.ofReal (P (ω (i - 1)) x * P x (ω (i + 1))) := by
    intro x
    rw [hρ, boltzmannFactor_singleton P hpos, Function.update_self,
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hνx : ∀ x : E, (uniformOn (Set.univ : Set E)) {x} = c := by
    intro x
    rw [uniformOn_univ, Measure.count_singleton, one_div]

  rw [Specification.premodifierZ, Specification.relZ, isssd_singleton_eq_map,
    lintegral_map (hpre.measurable {i}) hupd, lintegral_fintype]
  simp_rw [hρi, hνx]
  rw [← Finset.sum_mul, pow_two, Matrix.mul_apply,
    ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ mul_nonneg (hpos _ _).le (hpos _ _).le)]

/-- The density of the singleton kernel `γ_{i}` of the Markov specification with respect to the
independent specification `λ_{i} = isssd ν`. -/
def markovSingletonDensity (P : Matrix E E ℝ) (i : ℤ) : (ℤ → E) → ℝ≥0∞ :=
  Specification.premodifierNorm (uniformOn (Set.univ : Set E))
    ((markovPotential P).boltzmannFactor 1) {i}

omit [DecidableEq E] in
/-- The singleton kernels of the Markov specification are density changes of `isssd ν`. -/
lemma markovSpecification_singleton_eq_withDensity (i : ℤ) (η : ℤ → E) :
    markovSpecification P {i} η =
      (Specification.isssd (S := ℤ) (uniformOn (Set.univ : Set E)) {i} η).withDensity
        (markovSingletonDensity P i) := by
  unfold markovSpecification Potential.gibbsSpecificationOfAbsolutelySummable
  exact Specification.modification_apply _ _ _ _ _

omit [DecidableEq E] in
lemma measurable_markovSingletonDensity (i : ℤ) : Measurable (markovSingletonDensity P i) :=
  Specification.measurable_relNorm (γ := Specification.isssd (uniformOn (Set.univ : Set E)))
    (Potential.isPremodifier_boltzmannFactor 1).measurable {i}

/-- The singleton density is `ρ_i(σ) = |E| · g(σ_{i-1}, σ_i, σ_{i+1})` with `g` as in (3.11). -/
lemma markovSingletonDensity_eq (hpos : ∀ x y, 0 < P x y) (i : ℤ) (ω : ℤ → E) :
    markovSingletonDensity P i ω
      = ENNReal.ofReal (markovDeterminingFun P (ω (i - 1)) (ω i) (ω (i + 1))) * (Fintype.card E : ℝ≥0∞) := by
  have hD0 : ENNReal.ofReal ((P ^ 2) (ω (i - 1)) (ω (i + 1))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_apply_pos hpos 1 _ _)).ne'
  have hDtop : ENNReal.ofReal ((P ^ 2) (ω (i - 1)) (ω (i + 1))) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [markovSingletonDensity, show Specification.premodifierNorm (uniformOn (Set.univ : Set E))
        ((markovPotential P).boltzmannFactor 1) {i} ω
      = (markovPotential P).boltzmannFactor 1 {i} ω
        / Specification.premodifierZ (uniformOn (Set.univ : Set E))
            ((markovPotential P).boltzmannFactor 1) {i} ω from rfl,
    premodifierZ_singleton P hpos, boltzmannFactor_singleton P hpos, markovDeterminingFun,
    ENNReal.ofReal_div_of_pos (pow_apply_pos hpos 1 _ _), ENNReal.div_eq_inv_mul,
    ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hD0) (Or.inl hDtop), inv_inv]
  ring

lemma markovSingletonDensity_ne_zero (hpos : ∀ x y, 0 < P x y) (i : ℤ) (ω : ℤ → E) :
    markovSingletonDensity P i ω ≠ 0 := by
  rw [markovSingletonDensity_eq P hpos]
  exact mul_ne_zero (ENNReal.ofReal_pos.2 (markovDeterminingFun_pos hpos _ _ _)).ne'
    (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

lemma markovSingletonDensity_ne_top (hpos : ∀ x y, 0 < P x y) (i : ℤ) (ω : ℤ → E) :
    markovSingletonDensity P i ω ≠ ⊤ := by
  rw [markovSingletonDensity_eq P hpos]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)

end Density

/-! ### Interval cylinders determine a probability measure on `ℤ → E` -/

section Cylinders

/-- The cylinder event fixing a configuration on the interval `[a, b]`. -/
def intervalCylinder (a b : ℤ) (σ : ℤ → E) : Set (ℤ → E) :=
  {τ : ℤ → E | ∀ k ∈ Finset.Icc a b, τ k = σ k}

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma mem_intervalCylinder {a b : ℤ} {σ τ : ℤ → E} :
    τ ∈ intervalCylinder a b σ ↔ ∀ k ∈ Finset.Icc a b, τ k = σ k := Iff.rfl

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_intervalCylinder (a b : ℤ) (σ : ℤ → E) :
    MeasurableSet (intervalCylinder a b σ) := by
  have h : intervalCylinder a b σ
      = ⋂ k : ℤ, ⋂ _ : k ∈ Finset.Icc a b, (fun τ : ℤ → E ↦ τ k) ⁻¹' {σ k} := by
    ext τ; simp [intervalCylinder]
  rw [h]
  exact MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun _ ↦
    (measurable_pi_apply k) (measurableSet_singleton _)

/-- The interval cylinders whose interval contains the site `c` in its interior. -/
def centredCylinders (c : ℤ) : Set (Set (ℤ → E)) :=
  {S : Set (ℤ → E) | ∃ (a b : ℤ) (σ : ℤ → E), a < c ∧ c < b ∧ S = intervalCylinder a b σ}

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The centred interval cylinders form a π-system: two of them either are disjoint or intersect
in the cylinder over the union of the two (overlapping) intervals. -/
lemma isPiSystem_centredCylinders (c : ℤ) : IsPiSystem (centredCylinders (E := E) c) := by
  rintro S₁ ⟨a₁, b₁, σ₁, ha₁, hb₁, rfl⟩ S₂ ⟨a₂, b₂, σ₂, ha₂, hb₂, rfl⟩ ⟨τ₀, hτ₁, hτ₂⟩
  refine ⟨min a₁ a₂, max b₁ b₂, τ₀, by omega, by omega, ?_⟩
  ext τ
  simp only [Set.mem_inter_iff, intervalCylinder, Set.mem_ofPred_eq, Finset.mem_Icc]
  simp only [intervalCylinder, Set.mem_ofPred_eq, Finset.mem_Icc] at hτ₁ hτ₂
  constructor
  · rintro ⟨h1, h2⟩ k hk
    rcases le_or_gt k c with hkc | hkc
    · rcases le_or_gt a₁ k with hk1 | hk1
      · rw [h1 k ⟨hk1, by omega⟩, hτ₁ k ⟨hk1, by omega⟩]
      · rw [h2 k ⟨by omega, by omega⟩, hτ₂ k ⟨by omega, by omega⟩]
    · rcases le_or_gt k b₁ with hk1 | hk1
      · rw [h1 k ⟨by omega, hk1⟩, hτ₁ k ⟨by omega, hk1⟩]
      · rw [h2 k ⟨by omega, by omega⟩, hτ₂ k ⟨by omega, by omega⟩]
  · intro h
    constructor
    · intro k hk
      rw [h k ⟨by omega, by omega⟩, ← hτ₁ k hk]
    · intro k hk
      rw [h k ⟨by omega, by omega⟩, ← hτ₂ k hk]

omit [DecidableEq E] in
/-- The centred interval cylinders generate the product σ-algebra on `ℤ → E`. -/
lemma generateFrom_centredCylinders (c : ℤ) :
    (inferInstance : MeasurableSpace (ℤ → E))
      = MeasurableSpace.generateFrom (centredCylinders (E := E) c) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · have key : ∀ k : ℤ,
        Measurable[MeasurableSpace.generateFrom (centredCylinders (E := E) c)]
          fun τ : ℤ → E ↦ τ k := by
      intro k
      refine @measurable_to_countable' E (ℤ → E) _ _
        (MeasurableSpace.generateFrom (centredCylinders (E := E) c)) _ fun e ↦ ?_
      set a : ℤ := min k c - 1 with ha
      set b : ℤ := max k c + 1 with hb
      have hac : a < c := by simp only [ha]; omega
      have hcb : c < b := by simp only [hb]; omega
      have hk : k ∈ Finset.Icc a b := by simp only [Finset.mem_Icc, ha, hb]; omega
      have hset : (fun τ : ℤ → E ↦ τ k) ⁻¹' {e}
          = ⋃ x ∈ {x : Π _j : (Finset.Icc a b : Finset ℤ), E | x ⟨k, hk⟩ = e},
              intervalCylinder a b (extendBy (Finset.Icc a b) x) := by
        ext τ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_ofPred_eq,
          intervalCylinder, exists_prop]
        constructor
        · intro hτ
          refine ⟨(Finset.Icc a b).restrict τ, hτ, fun j hj ↦ ?_⟩
          rw [extendBy_of_mem _ hj]
          rfl
        · rintro ⟨x, hx, hτ⟩
          rw [hτ k hk, extendBy_of_mem _ hk, hx]
      rw [hset]
      refine MeasurableSet.biUnion (Set.to_countable _) fun x _ ↦ ?_
      exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, _, hac, hcb, rfl⟩
    have hle : (⨆ k : ℤ, MeasurableSpace.comap (fun τ : ℤ → E ↦ τ k) inferInstance)
        ≤ MeasurableSpace.generateFrom (centredCylinders (E := E) c) :=
      iSup_le fun k ↦ (key k).comap_le
    exact hle
  · rintro S ⟨a, b, σ, -, -, rfl⟩
    exact measurableSet_intervalCylinder a b σ

omit [DecidableEq E] in
/-- Two probability measures on `ℤ → E` agreeing on all interval cylinders whose interval contains
a fixed site `c` in its interior are equal. -/
lemma ext_of_centredCylinders {μ₁ μ₂ : Measure (ℤ → E)} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (c : ℤ)
    (h : ∀ a b : ℤ, a < c → c < b → ∀ σ : ℤ → E,
      μ₁ (intervalCylinder a b σ) = μ₂ (intervalCylinder a b σ)) :
    μ₁ = μ₂ :=
  MeasureTheory.ext_of_generate_finite _ (generateFrom_centredCylinders c)
    (isPiSystem_centredCylinders c)
    (by rintro S ⟨a, b, σ, ha, hb, rfl⟩; exact h a b ha hb σ)
    (by rw [measure_univ, measure_univ])

end Cylinders

/-! ### Punctured cylinders -/

section Punctured

/-- The cylinder over `[a, b]` with the coordinate at the site `i` left free. -/
def puncturedCylinder (a b i : ℤ) (σ : ℤ → E) : Set (ℤ → E) :=
  {τ : ℤ → E | ∀ k ∈ (Finset.Icc a b).erase i, τ k = σ k}

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma intervalCylinder_eq_inter {a b i : ℤ} (hi : i ∈ Finset.Icc a b) (σ : ℤ → E) :
    intervalCylinder a b σ = {τ : ℤ → E | τ i = σ i} ∩ puncturedCylinder a b i σ := by
  ext τ
  simp only [intervalCylinder, puncturedCylinder, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Finset.mem_erase]
  constructor
  · intro h
    exact ⟨h i hi, fun k hk ↦ h k hk.2⟩
  · rintro ⟨h1, h2⟩ k hk
    by_cases hki : k = i
    · rw [hki]; exact h1
    · exact h2 k ⟨hki, hk⟩

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_cylinderEvents_puncturedCylinder (a b i : ℤ) (σ : ℤ → E) :
    MeasurableSet[cylinderEvents ((({i} : Finset ℤ) : Set ℤ)ᶜ)] (puncturedCylinder a b i σ) := by
  have h : puncturedCylinder a b i σ
      = ⋂ k : ℤ, ⋂ _ : k ∈ (Finset.Icc a b).erase i, (fun τ : ℤ → E ↦ τ k) ⁻¹' {σ k} := by
    ext τ; simp [puncturedCylinder]
  rw [h]
  refine MeasurableSet.iInter fun k ↦ MeasurableSet.iInter fun hk ↦ ?_
  have hki : k ≠ i := (Finset.mem_erase.1 hk).1
  exact measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E)
    (Δ := ((({i} : Finset ℤ) : Set ℤ)ᶜ)) (by simpa using hki) (measurableSet_singleton _)

omit [Fintype E] [DecidableEq E] [Nonempty E] in
lemma measurableSet_puncturedCylinder (a b i : ℤ) (σ : ℤ → E) :
    MeasurableSet (puncturedCylinder a b i σ) :=
  cylinderEvents_le_pi _ (measurableSet_cylinderEvents_puncturedCylinder a b i σ)

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Summing the free coordinate recovers the punctured cylinder. -/
lemma puncturedCylinder_eq_iUnion {a b i : ℤ} (σ : ℤ → E) :
    puncturedCylinder a b i σ = ⋃ y : E, intervalCylinder a b (Function.update σ i y) := by
  ext τ
  simp only [puncturedCylinder, intervalCylinder, Set.mem_ofPred_eq, Set.mem_iUnion,
    Finset.mem_erase]
  constructor
  · intro h
    refine ⟨τ i, fun k hk ↦ ?_⟩
    by_cases hki : k = i
    · rw [hki, Function.update_self]
    · rw [Function.update_of_ne hki]
      exact h k ⟨hki, hk⟩
  · rintro ⟨y, hy⟩ k hk
    have h := hy k hk.2
    rwa [Function.update_of_ne hk.1] at h

omit [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma pairwise_disjoint_intervalCylinder_update {a b i : ℤ} (hi : i ∈ Finset.Icc a b)
    (σ : ℤ → E) :
    Pairwise (Function.onFun Disjoint
      fun y : E ↦ intervalCylinder a b (Function.update σ i y)) := by
  intro y y' hyy'
  rw [Function.onFun, Set.disjoint_left]
  rintro τ hτ hτ'
  have h1 := hτ i hi
  have h2 := hτ' i hi
  rw [Function.update_self] at h1 h2
  exact hyy' (h1.symm.trans h2)

omit [DecidableEq E] [Nonempty E] in
/-- The measure of a punctured cylinder is the sum of the measures of the interval cylinders
obtained by filling in the free coordinate. -/
lemma measure_puncturedCylinder (μ : Measure (ℤ → E)) {a b i : ℤ} (hi : i ∈ Finset.Icc a b)
    (σ : ℤ → E) :
    μ (puncturedCylinder a b i σ) = ∑ y : E, μ (intervalCylinder a b (Function.update σ i y)) := by
  rw [puncturedCylinder_eq_iUnion, measure_iUnion
    (pairwise_disjoint_intervalCylinder_update hi σ)
    (fun y ↦ measurableSet_intervalCylinder a b _), tsum_fintype]

end Punctured

/-! ### `μ_P` is a Gibbs measure for `markovSpecification P` (Georgii (3.5), step 1) -/

section ChainSum
variable (P : Matrix E E ℝ) (α : E → ℝ)

open scoped Matrix

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Summing the chain weight over the free coordinate at an interior site `i` replaces the two
bonds at `i` by the two-step transition probability `P²` (Chapman–Kolmogorov). -/
lemma sum_chainWeight_update {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) :
    ∑ y : E, chainWeight P α a b (Function.update σ i y)
      = α (σ a) * ((P ^ 2) (σ (i - 1)) (σ (i + 1))
          * ∏ k ∈ ((Finset.Ico a b).erase (i - 1)).erase i, P (σ k) (σ (k + 1))) := by
  have h : ∀ y : E, chainWeight P α a b (Function.update σ i y)
      = α (σ a) * ((P (σ (i - 1)) y * P y (σ (i + 1)))
          * ∏ k ∈ ((Finset.Ico a b).erase (i - 1)).erase i, P (σ k) (σ (k + 1))) := by
    intro y
    rw [chainWeight_update_middle P α hai hib]
    ring
  rw [Finset.sum_congr rfl fun y _ ↦ h y, ← Finset.mul_sum, ← Finset.sum_mul, ← Matrix.mul_apply,
    ← pow_two]

end ChainSum

section GibbsChain
variable (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

open scoped Matrix

/-- **The three-point identity behind step 1 of the proof of Georgii (3.5)**:
`μ_P(σ_{[a,b]} = ζ) = g(ζ_{i-1}, ζ_i, ζ_{i+1}) μ_P(σ_{[a,b] ∖ {i}} = ζ)` for `a < i < b`. -/
lemma stationaryChain_intervalCylinder_eq {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) :
    stationaryChain P hP hpos (intervalCylinder a b σ)
      = ENNReal.ofReal (markovDeterminingFun P (σ (i - 1)) (σ i) (σ (i + 1)))
          * stationaryChain P hP hpos (puncturedCylinder a b i σ) := by
  have hab : a ≤ b := by omega
  have hi : i ∈ Finset.Icc a b := by simp only [Finset.mem_Icc]; omega
  have hne : (P ^ 2) (σ (i - 1)) (σ (i + 1)) ≠ 0 := (pow_apply_pos hpos 1 _ _).ne'
  have hαnn : ∀ x, 0 ≤ stationaryDist P hP hpos x := fun x ↦ (stationaryDist_pos P hP hpos x).le
  have hcw : ∀ τ : ℤ → E, stationaryChain P hP hpos (intervalCylinder a b τ)
      = ENNReal.ofReal (chainWeight P (stationaryDist P hP hpos) a b τ) :=
    fun τ ↦ markovChain_cylinder P hP hpos hab τ
  rw [hcw σ, chainWeight_eq_middle P (stationaryDist P hP hpos) hai hib,
    measure_puncturedCylinder _ hi]
  simp_rw [hcw]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ ↦ chainWeight_nonneg P (stationaryDist P hP hpos)
      (fun x y ↦ (hpos x y).le) hαnn a b _),
    sum_chainWeight_update P (stationaryDist P hP hpos) hai hib,
    ← ENNReal.ofReal_mul (markovDeterminingFun_pos hpos _ _ _).le]
  congr 1
  rw [markovDeterminingFun, div_mul_eq_mul_div, eq_div_iff hne]
  ring

/-- Step 1 of the proof of Georgii (3.5): `μ_P γ_{i}` and `μ_P` agree on interval cylinders whose
interval contains `i` in its interior. -/
lemma lintegral_markovSpecification_singleton_intervalCylinder {i a b : ℤ}
    (hai : a < i) (hib : i < b) (σ : ℤ → E) :
    ∫⁻ ω, markovSpecification P {i} ω (intervalCylinder a b σ) ∂(stationaryChain P hP hpos)
      = stationaryChain P hP hpos (intervalCylinder a b σ) := by
  have hi : i ∈ Finset.Icc a b := by simp only [Finset.mem_Icc]; omega
  have hA : MeasurableSet {τ : ℤ → E | τ i = σ i} := by
    exact (measurableSet_singleton (σ i)).preimage (measurable_pi_apply i)
  have hB := measurableSet_cylinderEvents_puncturedCylinder a b i σ
  have hkey : ∀ ω : ℤ → E, markovSpecification P {i} ω (intervalCylinder a b σ)
      = (puncturedCylinder a b i σ).indicator 1 ω
          * ENNReal.ofReal (markovDeterminingFun P (σ (i - 1)) (σ i) (σ (i + 1))) := by
    intro ω
    rw [intervalCylinder_eq_inter hi,
      (markovSpecification P).isProper.inter_eq_indicator_mul {i} hA hB ω,
      markovSpecification_singleton_apply hpos i (σ i) ω]
    by_cases hω : ω ∈ puncturedCylinder a b i σ
    · have h1 : ω (i - 1) = σ (i - 1) :=
        hω (i - 1) (by simp only [Finset.mem_erase, Finset.mem_Icc]; omega)
      have h2 : ω (i + 1) = σ (i + 1) :=
        hω (i + 1) (by simp only [Finset.mem_erase, Finset.mem_Icc]; omega)
      rw [h1, h2]
    · rw [Set.indicator_of_notMem hω]
      simp
  simp_rw [hkey]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator_one (measurableSet_puncturedCylinder a b i σ),
    stationaryChain_intervalCylinder_eq P hP hpos hai hib σ, mul_comm]

end GibbsChain

section GibbsMeasure
variable (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

/-- `μ_P` is invariant under every singleton kernel of `markovSpecification P`. -/
lemma stationaryChain_bind_markovSpecification_singleton (i : ℤ) :
    (⇑(markovSpecification P {i})) ∘ₘ (stationaryChain P hP hpos)
      = stationaryChain P hP hpos := by
  have := isProbabilityMeasure_stationaryChain P hP hpos
  have hmeas : AEMeasurable (⇑(markovSpecification P {i})) (stationaryChain P hP hpos) :=
    ((markovSpecification P {i}).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  have : IsProbabilityMeasure
      ((⇑(markovSpecification P {i})) ∘ₘ (stationaryChain P hP hpos)) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hmeas]
    simp
  refine ext_of_centredCylinders i fun a b hai hib σ ↦ ?_
  rw [Measure.bind_apply (measurableSet_intervalCylinder a b σ) hmeas]
  exact lintegral_markovSpecification_singleton_intervalCylinder P hP hpos hai hib σ

/-- **Georgii (3.5), step 1.** The stationary Markov chain `μ_P` of a positive stochastic matrix
`P` is a Gibbs measure for the Markov specification `γ = markovSpecification P`. -/
theorem isGibbsMeasure_markovSpecification_stationaryChain :
    (markovSpecification P).IsGibbsMeasure (stationaryChain P hP hpos) := by
  have := isProbabilityMeasure_stationaryChain P hP hpos
  rw [Specification.isGibbsMeasure_iff_forall_singleton_bind_eq
      (lam := Specification.isssd (S := ℤ) (uniformOn (Set.univ : Set E)))
      ((Specification.isStronglyConsistent_isssd _).isDisjointlyConsistent)
      (ρ := fun i ↦ markovSingletonDensity P i)
      (fun i ↦ measurable_markovSingletonDensity P i)
      (fun i ω ↦ markovSingletonDensity_ne_zero P hpos i ω)
      (fun i ω ↦ markovSingletonDensity_ne_top P hpos i ω)
      (fun i η ↦ markovSpecification_singleton_eq_withDensity P i η)]
  exact fun i ↦ stationaryChain_bind_markovSpecification_singleton P hP hpos i

end GibbsMeasure

/-! ### Georgii (3.6): conditioning on the boundary `∂Λ` -/

section BoundaryCond
variable (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

/-- **Single-site exchange.** Resampling one site `i ∈ Λ` of a cylinder over `Λ ∪ ∂Λ` changes
its `μ_P`-measure by the ratio of the Boltzmann factors of `Λ`: since `∂Λ` contains both
neighbours of every site of `Λ`, the two bonds at `i` are the only factors of the chain weight
that move. -/
lemma stationaryChain_cyl_update_mul_boltzmannFactor {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ Λ)
    (τ : ℤ → E) (y : E) :
    stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (Function.update τ i y))
        * (markovPotential P).boltzmannFactor 1 Λ τ
      = stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) τ)
        * (markovPotential P).boltzmannFactor 1 Λ (Function.update τ i y) := by
  classical
  set Δ := Λ ∪ boundary Λ with hΔdef
  have hiΔ : i ∈ Δ := Finset.mem_union_left _ hi
  have him : i - 1 ∈ Δ := pred_mem_union_boundary hi
  have hip : i + 1 ∈ Δ := succ_mem_union_boundary hi
  obtain ⟨a, b, hsub, hai, hib⟩ : ∃ a b : ℤ, Δ ⊆ Finset.Icc a b ∧ a < i ∧ i < b := by
    refine ⟨-boundOf Δ, boundOf Δ, subset_Icc_boundOf Δ, ?_, ?_⟩
    · have h1 := Finset.mem_Icc.1 (subset_Icc_boundOf Δ him)
      omega
    · have h2 := Finset.mem_Icc.1 (subset_Icc_boundOf Δ hip)
      omega
  have hab : a ≤ b := by omega
  set α := stationaryDist P hP hpos with hα
  have hαnn : ∀ x, 0 ≤ α x := fun x ↦ (stationaryDist_pos P hP hpos x).le
  set Γ := Finset.Icc a b \ Δ with hΓdef
  have hΓdisj : Disjoint Γ Δ := Finset.sdiff_disjoint
  have hΓΔ : Γ ∪ Δ = Finset.Icc a b := Finset.sdiff_union_of_subset hsub
  have hiΓ : i ∉ Γ := fun h ↦ (Finset.mem_sdiff.1 h).2 hiΔ
  have hdec : ∀ σ : ℤ → E, stationaryChain P hP hpos (cyl Δ σ)
      = ∑ ξ : Γ → E,
          stationaryChain P hP hpos (cyl (Finset.Icc a b) (juxt (Γ : Set ℤ) σ ξ)) := by
    intro σ
    rw [measure_cyl_eq_sum_juxt _ hΓdisj σ]
    exact Finset.sum_congr rfl fun ξ _ ↦ by rw [hΓΔ]
  have hcyl : ∀ ρ : ℤ → E, stationaryChain P hP hpos (cyl (Finset.Icc a b) ρ)
      = ENNReal.ofReal (chainWeight P α a b ρ) := fun ρ ↦ markovChain_cylinder P hP hpos hab ρ
  -- the Boltzmann factors, split at the two bonds at `i`
  have hbondm : i - 1 ∈ bondsOf Λ :=
    mem_bondsOf.2 (Or.inr (by rw [show i - 1 + 1 = i by omega]; exact hi))
  have hbond : i ∈ bondsOf Λ := mem_bondsOf.2 (Or.inl hi)
  set R : ℝ := ∏ j ∈ ((bondsOf Λ).erase (i - 1)).erase i, P (τ j) (τ (j + 1)) with hRdef
  have hsplit : ∀ σ : ℤ → E, ∏ j ∈ bondsOf Λ, P (σ j) (σ (j + 1))
      = P (σ (i - 1)) (σ i) * (P (σ i) (σ (i + 1))
          * ∏ j ∈ ((bondsOf Λ).erase (i - 1)).erase i, P (σ j) (σ (j + 1))) := by
    intro σ
    rw [← Finset.mul_prod_erase _ _ hbondm,
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨by omega, hbond⟩),
      show i - 1 + 1 = i by omega]
  have hrest : ∏ j ∈ ((bondsOf Λ).erase (i - 1)).erase i,
      P (Function.update τ i y j) (Function.update τ i y (j + 1)) = R := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    simp only [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1, Function.update_of_ne (fun h ↦ hj.2.1 (by omega))]
  have hboltzτ : (markovPotential P).boltzmannFactor 1 Λ τ
      = ENNReal.ofReal (P (τ (i - 1)) (τ i) * P (τ i) (τ (i + 1)) * R) := by
    rw [boltzmannFactor_eq_prod_bondsOf hpos, hsplit τ, ← hRdef, mul_assoc]
  have hboltzupd : (markovPotential P).boltzmannFactor 1 Λ (Function.update τ i y)
      = ENNReal.ofReal (P (τ (i - 1)) y * P y (τ (i + 1)) * R) := by
    rw [boltzmannFactor_eq_prod_bondsOf hpos, hsplit (Function.update τ i y),
      Function.update_of_ne (by omega : i - 1 ≠ i), Function.update_self,
      Function.update_of_ne (by omega : i + 1 ≠ i), hrest, mul_assoc]
  have hkey : ∀ ξ : Γ → E,
      stationaryChain P hP hpos
          (cyl (Finset.Icc a b) (juxt (Γ : Set ℤ) (Function.update τ i y) ξ))
        * ENNReal.ofReal (P (τ (i - 1)) (τ i) * P (τ i) (τ (i + 1)))
      = stationaryChain P hP hpos (cyl (Finset.Icc a b) (juxt (Γ : Set ℤ) τ ξ))
        * ENNReal.ofReal (P (τ (i - 1)) y * P y (τ (i + 1))) := by
    intro ξ
    have himΓ : i - 1 ∉ Γ := fun h ↦ (Finset.mem_sdiff.1 h).2 him
    have hipΓ : i + 1 ∉ Γ := fun h ↦ (Finset.mem_sdiff.1 h).2 hip
    have hρm : juxt (Γ : Set ℤ) τ ξ (i - 1) = τ (i - 1) :=
      juxt_apply_of_not_mem (Finset.mem_coe.not.mpr himΓ) ξ
    have hρi : juxt (Γ : Set ℤ) τ ξ i = τ i :=
      juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hiΓ) ξ
    have hρp : juxt (Γ : Set ℤ) τ ξ (i + 1) = τ (i + 1) :=
      juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hipΓ) ξ
    rw [juxt_update_of_notMem hiΓ, hcyl, hcyl,
      ← ENNReal.ofReal_mul (chainWeight_nonneg P α (fun x y ↦ (hpos x y).le) hαnn a b _),
      ← ENNReal.ofReal_mul (chainWeight_nonneg P α (fun x y ↦ (hpos x y).le) hαnn a b _)]
    congr 1
    rw [chainWeight_update_middle P α hai hib, chainWeight_eq_middle P α hai hib,
      hρm, hρi, hρp]
    ring
  rw [hdec, hdec, hboltzτ, hboltzupd,
    show P (τ (i - 1)) (τ i) * P (τ i) (τ (i + 1)) * R
      = (P (τ (i - 1)) (τ i) * P (τ i) (τ (i + 1))) * R by ring,
    show P (τ (i - 1)) y * P y (τ (i + 1)) * R
      = (P (τ (i - 1)) y * P y (τ (i + 1))) * R by ring,
    ENNReal.ofReal_mul (mul_nonneg (hpos _ _).le (hpos _ _).le),
    ENNReal.ofReal_mul (mul_nonneg (hpos _ _).le (hpos _ _).le),
    ← mul_assoc, ← mul_assoc]
  congr 1
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ξ _ ↦ hkey ξ

/-- **Exchange lemma.** Two configurations agreeing off `Λ` have cylinder `μ_P`-measures over
`Λ ∪ ∂Λ` proportional to their Boltzmann factors on `Λ`: iterate the single-site exchange over
the sites of `Λ`. -/
lemma stationaryChain_cyl_overwrite_mul_boltzmannFactor (Λ : Finset ℤ) (ζ τ : ℤ → E) :
    stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (overwrite Λ ζ τ))
        * (markovPotential P).boltzmannFactor 1 Λ τ
      = stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) τ)
        * (markovPotential P).boltzmannFactor 1 Λ (overwrite Λ ζ τ) := by
  suffices h : ∀ s : Finset ℤ, s ⊆ Λ →
      stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (overwrite s ζ τ))
          * (markovPotential P).boltzmannFactor 1 Λ τ
        = stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) τ)
          * (markovPotential P).boltzmannFactor 1 Λ (overwrite s ζ τ) from h Λ subset_rfl
  intro s
  induction s using Finset.induction with
  | empty =>
      intro _
      rw [show overwrite (∅ : Finset ℤ) ζ τ = τ from Finset.piecewise_empty ζ τ]
  | insert i s his ih =>
      intro hsub
      have hiΛ : i ∈ Λ := hsub (Finset.mem_insert_self i s)
      have hihs := ih ((Finset.subset_insert i s).trans hsub)
      have hover_insert : overwrite (insert i s) ζ τ
          = Function.update (overwrite s ζ τ) i (ζ i) := Finset.piecewise_insert s ζ τ i
      have hstep := stationaryChain_cyl_update_mul_boltzmannFactor P hP hpos hiΛ
        (overwrite s ζ τ) (ζ i)
      have hB0 : (markovPotential P).boltzmannFactor 1 Λ (overwrite s ζ τ) ≠ 0 :=
        (Potential.boltzmannFactor_pos 1 Λ _).ne'
      have hBtop : (markovPotential P).boltzmannFactor 1 Λ (overwrite s ζ τ) ≠ ⊤ :=
        Potential.boltzmannFactor_ne_top 1 Λ _
      rw [hover_insert, ← ENNReal.mul_left_inj hB0 hBtop, mul_right_comm, hstep,
        mul_right_comm, hihs, mul_right_comm]

/-- **Georgii (3.6).** For every finite volume `Λ ⊆ ℤ`, every configuration `ζ`, and every —
not merely almost every — boundary condition `ω`, the Markov specification is the elementary
conditional probability of the stationary chain `μ_P` given the values on the boundary `∂Λ` of
(3.4): `γ_Λ(σ_Λ = ζ | ω) = μ_P(σ_Λ = ζ | σ_{∂Λ} = ω_{∂Λ})`. The conditioning event has
positive measure by `stationaryChain_cyl_pos`; for an interval `Λ = [a, b]` the boundary is
`{a - 1, b + 1}` (`boundary_Icc`) and the right-hand side is evaluated by Comment (3.8)(1). -/
theorem markovSpecification_apply_cyl_eq_cond (Λ : Finset ℤ) (ζ ω : ℤ → E) :
    markovSpecification P Λ ω (cyl Λ ζ)
      = (stationaryChain P hP hpos)[cyl Λ ζ | cyl (boundary Λ) ω] := by
  have hprob := isProbabilityMeasure_stationaryChain P hP hpos
  -- the left-hand side as a ratio of Boltzmann weights
  have hLHS : markovSpecification P Λ ω (cyl Λ ζ)
      = (markovPotential P).boltzmannFactor 1 Λ (overwrite Λ ζ ω)
        * (∑ ξ : Λ → E,
            (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ))⁻¹ := by
    rw [markovSpecification_apply_eq Λ ω (measurableSet_cyl Λ ζ),
      lintegral_isssd_indicator_cyl Λ ζ ω (Potential.measurable_boltzmannFactor 1 Λ),
      Specification.premodifierZ, Specification.relZ,
      lintegral_isssd_eq_sum Λ ω (Potential.measurable_boltzmannFactor 1 Λ),
      ← Finset.sum_mul,
      mul_comm (∑ ξ : Λ → E,
        (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ)) _,
      mul_mul_inv_cancel (pow_ne_zero _ card_inv_ne_zero) (ENNReal.pow_ne_top card_inv_ne_top)]
  -- the exchange relation, summed over the configurations in `Λ`
  have hrel : stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (overwrite Λ ζ ω))
        * (∑ ξ : Λ → E, (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ))
      = stationaryChain P hP hpos (cyl (boundary Λ) ω)
        * (markovPotential P).boltzmannFactor 1 Λ (overwrite Λ ζ ω) := by
    rw [measure_cyl_eq_sum_juxt (stationaryChain P hP hpos) (disjoint_boundary Λ) ω,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ξ _ ↦ ?_
    have h := stationaryChain_cyl_overwrite_mul_boltzmannFactor P hP hpos Λ ζ
      (juxt (Λ : Set ℤ) ω ξ)
    rwa [overwrite_juxt] at h
  -- assemble
  have h1 : stationaryChain P hP hpos (cyl (boundary Λ) ω) ≠ 0 :=
    (stationaryChain_cyl_pos P hP hpos _ ω).ne'
  have h2 : stationaryChain P hP hpos (cyl (boundary Λ) ω) ≠ ⊤ := measure_ne_top _ _
  have h3 : (∑ ξ : Λ → E,
      (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ)) ≠ 0 := by
    intro hzero
    exact (Potential.boltzmannFactor_pos 1 Λ
        (juxt (Λ : Set ℤ) ω fun _ ↦ Classical.arbitrary E)).ne'
      (Finset.sum_eq_zero_iff.1 hzero _ (Finset.mem_univ _))
  have h4 : (∑ ξ : Λ → E,
      (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun ξ _ ↦ Potential.boltzmannFactor_ne_top 1 Λ _
  rw [hLHS, ProbabilityTheory.cond_apply (measurableSet_cyl _ _),
    cyl_inter_cyl (disjoint_boundary Λ).symm ω ζ, Finset.union_comm (boundary Λ) Λ]
  calc (markovPotential P).boltzmannFactor 1 Λ (overwrite Λ ζ ω)
        * (∑ ξ : Λ → E, (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ))⁻¹
      = (stationaryChain P hP hpos (cyl (boundary Λ) ω))⁻¹
          * stationaryChain P hP hpos (cyl (boundary Λ) ω)
          * (markovPotential P).boltzmannFactor 1 Λ (overwrite Λ ζ ω)
          * (∑ ξ : Λ → E, (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ))⁻¹ := by
        rw [ENNReal.inv_mul_cancel h1 h2, one_mul]
    _ = (stationaryChain P hP hpos (cyl (boundary Λ) ω))⁻¹
          * (stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (overwrite Λ ζ ω))
            * (∑ ξ : Λ → E, (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ)))
          * (∑ ξ : Λ → E, (markovPotential P).boltzmannFactor 1 Λ (juxt (Λ : Set ℤ) ω ξ))⁻¹ := by
        rw [mul_assoc (stationaryChain P hP hpos (cyl (boundary Λ) ω))⁻¹, ← hrel]
    _ = (stationaryChain P hP hpos (cyl (boundary Λ) ω))⁻¹
          * stationaryChain P hP hpos (cyl (Λ ∪ boundary Λ) (overwrite Λ ζ ω)) := by
        rw [mul_assoc, mul_assoc, ENNReal.mul_inv_cancel h3 h4, mul_one]

end BoundaryCond

/-! ### Georgii, Theorem (3.5): `𝒢(γ_P) = {μ_P}` -/

/-- The DLR property of the stationary chain, volume by volume: `γ_Λ` is a version of the
conditional distribution of `μ_P` given the *whole exterior* σ-algebra `𝓕_{Λᶜ}`, `μ_P`-a.e. This
is the definitional projection of `isGibbsMeasure_markovSpecification_stationaryChain`. Georgii's
(3.6), which conditions on the boundary `∂Λ` of (3.4) and holds for every `ω`, is
`markovSpecification_apply_cyl_eq_cond`. -/
theorem isCondExp_markovSpecification_stationaryChain (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) (Λ : Finset ℤ) :
    (markovSpecification P Λ).IsCondExp (stationaryChain P hP hpos) :=
  isGibbsMeasure_markovSpecification_stationaryChain P hP hpos Λ

/-- **Georgii, Theorem (3.5).** For a positive stochastic matrix `P` the Markov specification
`γ_P = markovSpecification P` has exactly one Gibbs measure, namely the stationary Markov chain
`μ_P` of (3.3): `𝒢(γ_P) = {μ_P}`.  Existence is
`isGibbsMeasure_markovSpecification_stationaryChain` (step 1), uniqueness is
`eq_of_isGibbsMeasure` (step 5). -/
theorem gibbsMeasure_eq_singleton (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    GibbsMeasure.G (markovSpecification P) = {stationaryChain P hP hpos} := by
  have := isProbabilityMeasure_stationaryChain P hP hpos
  ext μ
  rw [GibbsMeasure.G.mem_iff, Set.mem_singleton_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := h.1
    exact eq_of_isGibbsMeasure hP hpos h.2
      (isGibbsMeasure_markovSpecification_stationaryChain P hP hpos)
  · subst h
    exact ⟨isProbabilityMeasure_stationaryChain P hP hpos,
      isGibbsMeasure_markovSpecification_stationaryChain P hP hpos⟩


/-- **Georgii Example (7.15), first half.** The stationary chain is extreme in `𝒢(γ_P)` — it is
the unique element. -/
theorem stationaryChain_mem_extremePoints_G (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) :
    stationaryChain P hP hpos
      ∈ (GibbsMeasure.G (markovSpecification P)).extremePoints ENNReal := by
  rw [gibbsMeasure_eq_singleton P hP hpos, extremePoints_singleton]
  rfl

/-- **Georgii Example (7.15).** The unique Gibbs measure of a positive homogeneous Markov
specification is trivial on the tail σ-algebra: uniqueness gives extremality, and Theorem
(7.7)(a) gives tail triviality. -/
theorem forall_tail_stationaryChain_eq_zero_or_one (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) :
    ∀ A, MeasurableSet[@GibbsMeasure.tailSigmaAlgebra ℤ E _] A →
      stationaryChain P hP hpos A = 0 ∨ stationaryChain P hP hpos A = 1 :=
  GibbsMeasure.tailTrivial_of_mem_extremePoints_G
    (stationaryChain_mem_extremePoints_G P hP hpos)
/-- **Georgii, Theorem (3.5).** The Markov specification of a positive stochastic matrix has a
unique Gibbs measure, the stationary Markov chain `μ_P` of (3.3). -/
theorem existsUnique_isGibbsMeasure (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    ∃! μ : Measure (ℤ → E),
      IsProbabilityMeasure μ ∧ (markovSpecification P).IsGibbsMeasure μ := by
  have := isProbabilityMeasure_stationaryChain P hP hpos
  refine ⟨stationaryChain P hP hpos,
    ⟨isProbabilityMeasure_stationaryChain P hP hpos,
      isGibbsMeasure_markovSpecification_stationaryChain P hP hpos⟩, fun μ hμ ↦ ?_⟩
  have := hμ.1
  exact eq_of_isGibbsMeasure hP hpos hμ.2
    (isGibbsMeasure_markovSpecification_stationaryChain P hP hpos)

/-- **Georgii, Theorem (3.5).** The map `ℓ : P ↦ markovSpecification P` is a bijection from the
positive stochastic matrices on the finite set `E` onto the positive homogeneous Markov
specifications on `ℤ`, and every `markovSpecification P` has exactly one Gibbs measure, namely the
stationary Markov chain `μ_P` of (3.3):

* `ℓ` maps into the positive homogeneous Markov specifications, and `𝒢(ℓ P) = {μ_P}`;
* `ℓ` is onto — formula (3.7) computes `P` from the determining function `g` of `γ`;
* `ℓ` is injective. -/
theorem georgii_3_5 :
    (∀ (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y),
        IsPositiveHomogeneousMarkov (markovSpecification P) ∧
        GibbsMeasure.G (markovSpecification P) = {stationaryChain P hP hpos}) ∧
      (∀ γ : Specification ℤ E, IsPositiveHomogeneousMarkov γ →
        ∃ (P : Matrix E E ℝ) (_hP : P ∈ Matrix.rowStochastic ℝ E) (_hpos : ∀ x y, 0 < P x y),
          γ = markovSpecification P) ∧
      (∀ (P P' : Matrix E E ℝ) (_hP : P ∈ Matrix.rowStochastic ℝ E)
        (_hpos : ∀ x y, 0 < P x y) (_hP' : P' ∈ Matrix.rowStochastic ℝ E)
        (_hpos' : ∀ x y, 0 < P' x y),
        markovSpecification P = markovSpecification P' → P = P') :=
  ⟨fun P hP hpos ↦ ⟨isPositiveHomogeneousMarkov_markovSpecification hpos,
      gibbsMeasure_eq_singleton P hP hpos⟩,
    fun _ hγ ↦ exists_matrix_eq_markovSpecification hγ,
    fun _ _ hP hpos hP' hpos' h ↦ markovSpecification_injOn hP hpos hP' hpos' h⟩

/-!
## Corollary (3.9) and Example (3.15)

Homogeneous nearest-neighbour potentials on `ℤ`, Corollary (3.9) in both directions, and the
one-dimensional Ising model of Example (3.15).
-/

section HomogeneousNearestNeighbour
open Finset Filter Topology Matrix
open scoped Matrix



/-- A singleton of `ℤ` is not a bond. -/
lemma not_exists_pair_singleton (i : ℤ) : ¬ ∃ j : ℤ, ({i} : Finset ℤ) = {j, j + 1} := by
  rintro ⟨j, hj⟩
  have h1 : (j : ℤ) ∈ ({i} : Finset ℤ) := by rw [hj]; simp
  have h2 : (j + 1 : ℤ) ∈ ({i} : Finset ℤ) := by rw [hj]; simp
  simp only [Finset.mem_singleton] at h1 h2
  omega

open Classical in
/-- Georgii, before Corollary (3.9): the **homogeneous nearest-neighbour potential** on `ℤ`
with self-energy `φ₁` and bond energy `φ₂`:
`Φ_{i}(σ) = φ₁(σ_i)`, `Φ_{i,i+1}(σ) = φ₂(σ_i, σ_{i+1})`, and `Φ_A = 0` for every other `A`. -/
def homogeneousNNPotential (φ₁ : E → ℝ) (φ₂ : E → E → ℝ) : Potential ℤ E := fun A σ ↦
  if h : ∃ i : ℤ, A = {i, i + 1} then φ₂ (σ h.choose) (σ (h.choose + 1))
  else if h' : ∃ i : ℤ, A = {i} then φ₁ (σ h'.choose) else 0

variable (φ₁ : E → ℝ) (φ₂ : E → E → ℝ)

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
@[simp] lemma homogeneousNNPotential_pair (i : ℤ) (σ : ℤ → E) :
    homogeneousNNPotential φ₁ φ₂ {i, i + 1} σ = φ₂ (σ i) (σ (i + 1)) := by
  have h : ∃ j, ({i, i + 1} : Finset ℤ) = {j, j + 1} := ⟨i, rfl⟩
  have hi : i = h.choose := pair_succ_inj h.choose_spec
  simp only [homogeneousNNPotential, dite_eq_left h]
  rw [← hi]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
@[simp] lemma homogeneousNNPotential_singleton (i : ℤ) (σ : ℤ → E) :
    homogeneousNNPotential φ₁ φ₂ {i} σ = φ₁ (σ i) := by
  have h' : ∃ j, ({i} : Finset ℤ) = {j} := ⟨i, rfl⟩
  have hi : i = h'.choose := by
    have := h'.choose_spec
    rwa [Finset.singleton_inj] at this
  simp only [homogeneousNNPotential, dite_eq_right (not_exists_pair_singleton i),
    dite_eq_left h']
  rw [← hi]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma homogeneousNNPotential_of_not {A : Finset ℤ} (hA : ¬ ∃ i : ℤ, A = {i, i + 1})
    (hA' : ¬ ∃ i : ℤ, A = {i}) (σ : ℤ → E) : homogeneousNNPotential φ₁ φ₂ A σ = 0 := by
  simp only [homogeneousNNPotential, dite_eq_right hA, dite_eq_right hA']

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The interaction supports of a homogeneous nearest-neighbour potential are the sites and the
bonds. -/
lemma exists_of_homogeneousNNPotential_ne_zero {A : Finset ℤ}
    (h : homogeneousNNPotential φ₁ φ₂ A ≠ 0) :
    (∃ i : ℤ, A = {i, i + 1}) ∨ ∃ i : ℤ, A = {i} := by
  by_contra hcon
  rw [not_or] at hcon
  exact h (funext fun σ ↦ homogeneousNNPotential_of_not φ₁ φ₂ hcon.1 hcon.2 σ)

instance isPotential_homogeneousNNPotential :
    (homogeneousNNPotential φ₁ φ₂).IsPotential where
  measurable A := by
    by_cases h : ∃ i : ℤ, A = {i, i + 1}
    · obtain ⟨i, rfl⟩ := h
      have hf : homogeneousNNPotential φ₁ φ₂ {i, i + 1}
          = fun σ ↦ φ₂ (σ i) (σ (i + 1)) := funext fun σ ↦ homogeneousNNPotential_pair φ₁ φ₂ i σ
      rw [hf]
      have hi : Measurable[cylinderEvents (({i, i + 1} : Finset ℤ) : Set ℤ)]
          fun σ : ℤ → E ↦ σ i := measurable_cylinderEvent_apply (by simp)
      have hi1 : Measurable[cylinderEvents (({i, i + 1} : Finset ℤ) : Set ℤ)]
          fun σ : ℤ → E ↦ σ (i + 1) := measurable_cylinderEvent_apply (by simp)
      exact (measurable_of_finite (fun p : E × E ↦ φ₂ p.1 p.2)).comp
        (f := fun σ : ℤ → E ↦ (σ i, σ (i + 1))) (hi.prodMk hi1)
    · by_cases h' : ∃ i : ℤ, A = {i}
      · obtain ⟨i, rfl⟩ := h'
        have hf : homogeneousNNPotential φ₁ φ₂ {i} = fun σ ↦ φ₁ (σ i) :=
          funext fun σ ↦ homogeneousNNPotential_singleton φ₁ φ₂ i σ
        rw [hf]
        exact (measurable_of_finite φ₁).comp
          (measurable_cylinderEvent_apply (X := fun _ : ℤ ↦ E) (by simp))
      · have hf : homogeneousNNPotential φ₁ φ₂ A = fun _ ↦ 0 :=
          funext fun σ ↦ homogeneousNNPotential_of_not φ₁ φ₂ h h' σ
        rw [hf]
        exact measurable_const

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- A nonzero interaction term containing `i` lies in `[i-1, i+1]`. -/
lemma subset_Icc_of_homogeneousNNPotential_ne_zero {i : ℤ} {A : Finset ℤ}
    (hiA : i ∈ A) (hΦ : homogeneousNNPotential φ₁ φ₂ A ≠ 0) : A ⊆ Finset.Icc (i - 1) (i + 1) := by
  rcases exists_of_homogeneousNNPotential_ne_zero φ₁ φ₂ hΦ with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    intro k hk <;>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hiA hk <;>
    simp only [Finset.mem_Icc] <;> omega

instance isFiniteRange_homogeneousNNPotential :
    (homogeneousNNPotential φ₁ φ₂).IsFiniteRange :=
  ⟨fun i ↦ ⟨Finset.Icc (i - 1) (i + 1),
    fun _ hiA hΦ ↦ subset_Icc_of_homogeneousNNPotential_ne_zero φ₁ φ₂ hiA hΦ⟩⟩

variable (E) in
/-- A uniform bound on the interaction terms of `homogeneousNNPotential φ₁ φ₂`. -/
def homogeneousNNBound (φ₁ : E → ℝ) (φ₂ : E → E → ℝ) : ℝ := ∑ x, |φ₁ x| + ∑ x, ∑ y, |φ₂ x y|

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
lemma homogeneousNNBound_nonneg : 0 ≤ homogeneousNNBound E φ₁ φ₂ :=
  add_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
lemma abs_homogeneousNNPotential_le (A : Finset ℤ) (σ : ℤ → E) :
    |homogeneousNNPotential φ₁ φ₂ A σ| ≤ homogeneousNNBound E φ₁ φ₂ := by
  have h1 : (0:ℝ) ≤ ∑ x, |φ₁ x| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have h2 : (0:ℝ) ≤ ∑ x, ∑ y, |φ₂ x y| :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  by_cases h : ∃ i : ℤ, A = {i, i + 1}
  · obtain ⟨i, rfl⟩ := h
    rw [homogeneousNNPotential_pair]
    have : |φ₂ (σ i) (σ (i + 1))| ≤ ∑ x, ∑ y, |φ₂ x y| :=
      le_trans (Finset.single_le_sum (f := fun y ↦ |φ₂ (σ i) y|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ _))
        (Finset.single_le_sum (f := fun x ↦ ∑ y, |φ₂ x y|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _))
    simp only [homogeneousNNBound]; linarith
  · by_cases h' : ∃ i : ℤ, A = {i}
    · obtain ⟨i, rfl⟩ := h'
      rw [homogeneousNNPotential_singleton]
      have : |φ₁ (σ i)| ≤ ∑ x, |φ₁ x| :=
        Finset.single_le_sum (f := fun x ↦ |φ₁ x|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ _)
      simp only [homogeneousNNBound]; linarith
    · rw [homogeneousNNPotential_of_not φ₁ φ₂ h h', abs_zero]
      exact homogeneousNNBound_nonneg φ₁ φ₂

instance isAbsolutelySummable_homogeneousNNPotential :
    (homogeneousNNPotential φ₁ φ₂).IsAbsolutelySummable := by
  refine ⟨fun i ↦ ?_⟩
  have hsupp : ∀ A : Finset ℤ, A ∉ (Finset.Icc (i - 1) (i + 1)).powerset →
      ({A : Finset ℤ | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖homogeneousNNPotential φ₁ φ₂ A η‖ₑ)) A = 0 := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | i ∈ A} from hiA)]
      have hΦ0 : homogeneousNNPotential φ₁ φ₂ A = 0 := by
        by_contra hΦ
        exact hA (subset_Icc_of_homogeneousNNPotential_ne_zero φ₁ φ₂ hiA hΦ)
      refine le_antisymm (iSup_le fun η ↦ ?_) zero_le
      simp [hΦ0]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | i ∈ A} from hiA) _
  rw [show (homogeneousNNPotential φ₁ φ₂).normAt i =
      ∑ A ∈ (Finset.Icc (i - 1) (i + 1)).powerset,
        ({A : Finset ℤ | i ∈ A}.indicator
          (fun A ↦ ⨆ η, ‖homogeneousNNPotential φ₁ φ₂ A η‖ₑ)) A from tsum_eq_sum hsupp]
  refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
  calc ({A : Finset ℤ | i ∈ A}.indicator
          (fun A ↦ ⨆ η, ‖homogeneousNNPotential φ₁ φ₂ A η‖ₑ)) A
      ≤ ⨆ η, ‖homogeneousNNPotential φ₁ φ₂ A η‖ₑ := Set.indicator_le_self _ _ A
    _ ≤ ENNReal.ofReal (homogeneousNNBound E φ₁ φ₂) := iSup_le fun η ↦ by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_homogeneousNNPotential_le φ₁ φ₂ A η)
    _ < ⊤ := ENNReal.ofReal_lt_top



/-! ### Singleton kernels of a Gibbsian specification -/

/-- The singleton kernels of the Gibbsian specification of an absolutely summable potential,
computed from the single-site Boltzmann weights: if `Φ`'s Boltzmann factor in `{i}` is
`w x` at the configuration `ω` updated to `x` at `i`, then `γ_{i}(σ_i = y|ω) = w y / ∑_x w x`. -/
lemma gibbsSpecification_singleton_apply_of_boltzmannFactor
    (Φ : Potential ℤ E) [Φ.IsPotential] [Φ.IsAbsolutelySummable] (β : ℝ) (i : ℤ) (ω : ℤ → E)
    {w : E → ℝ} (hw : ∀ x, 0 < w x)
    (hb : ∀ x, Φ.boltzmannFactor β {i} (Function.update ω i x) = ENNReal.ofReal (w x)) (y : E) :
    Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) (uniformOn (Set.univ : Set E)) β
        {i} ω {σ : ℤ → E | σ i = y} = ENNReal.ofReal (w y / ∑ x, w x) := by
  classical
  set ν : Measure E := uniformOn (Set.univ : Set E) with hν
  set ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞ := Φ.boltzmannFactor β with hρ
  have hmeasρ : Measurable (ρ {i}) := Potential.measurable_boltzmannFactor β {i}
  have hsumpos : 0 < ∑ x, w x := Finset.sum_pos (fun x _ ↦ hw x) Finset.univ_nonempty
  -- the partition function in `{i}` does not depend on the value at `i`
  have hZ : ∀ x : E, Specification.premodifierZ ν ρ {i} (Function.update ω i x)
      = (Fintype.card E : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ x, w x) := by
    intro x
    have hcongr : Specification.isssd (S := ℤ) ν {i} (Function.update ω i x)
        = Specification.isssd (S := ℤ) ν {i} ω :=
      isssd_congr {i} (fun k hk ↦ Function.update_of_ne (by simpa using hk) _ _)
    show ∫⁻ σ, ρ {i} σ ∂(Specification.isssd (S := ℤ) ν {i} (Function.update ω i x)) = _
    rw [hcongr, lintegral_isssd_singleton i ω hmeasρ]
    congr 1
    rw [Finset.sum_congr rfl fun x _ ↦ hb x,
      ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ (hw x).le]
  -- the density at the updated configuration
  have hdens : ∀ x : E, Specification.premodifierNorm ν ρ {i} (Function.update ω i x)
      = ENNReal.ofReal (w x) / ((Fintype.card E : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ x, w x)) := by
    intro x
    show ρ {i} (Function.update ω i x) / Specification.premodifierZ ν ρ {i}
      (Function.update ω i x) = _
    rw [hZ x, hb x]
  have hSmeas : MeasurableSet {σ : ℤ → E | σ i = y} := measurableSet_eq_apply i y
  have hfmeas : Measurable (Specification.premodifierNorm ν ρ {i}) :=
    Specification.measurable_relNorm (γ := Specification.isssd (S := ℤ) ν)
      (Potential.isPremodifier_boltzmannFactor β).measurable {i}
  have hstep : Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β {i} ω
        {σ : ℤ → E | σ i = y}
      = ∫⁻ σ, ({σ : ℤ → E | σ i = y}.indicator
          (Specification.premodifierNorm ν ρ {i})) σ ∂(Specification.isssd (S := ℤ) ν {i} ω) := by
    rw [show Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β {i} ω
        = (Specification.isssd (S := ℤ) ν {i} ω).withDensity
            (Specification.premodifierNorm ν ρ {i}) from
      Specification.modification_apply _ _ _ _ _, withDensity_apply _ hSmeas,
      lintegral_indicator hSmeas]
  rw [hstep, lintegral_isssd_singleton i ω (hfmeas.indicator hSmeas)]
  have hind : ∀ x : E, ({σ : ℤ → E | σ i = y}.indicator
      (Specification.premodifierNorm ν ρ {i})) (Function.update ω i x)
      = if x = y then
          ENNReal.ofReal (w y) / ((Fintype.card E : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ x, w x))
        else 0 := by
    intro x
    by_cases hxy : x = y
    · subst hxy
      rw [Set.indicator_of_mem (by simp), hdens x]
      simp
    · rw [Set.indicator_of_notMem (by simp [hxy])]
      simp [hxy]
  rw [Finset.sum_congr rfl fun x _ ↦ hind x, Finset.sum_ite_eq' Finset.univ y
    (fun _ ↦ ENNReal.ofReal (w y) / ((Fintype.card E : ℝ≥0∞)⁻¹ * ENNReal.ofReal (∑ x, w x)))]
  simp only [Finset.mem_univ, ite_true]
  have hc0 : (Fintype.card E : ℝ≥0∞)⁻¹ ≠ 0 := card_inv_ne_zero (E := E)
  have hctop : (Fintype.card E : ℝ≥0∞)⁻¹ ≠ ⊤ := card_inv_ne_top (E := E)
  have hs0 : ENNReal.ofReal (∑ x, w x) ≠ 0 := (ENNReal.ofReal_pos.2 hsumpos).ne'
  have hstop : ENNReal.ofReal (∑ x, w x) ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ a b d : ℝ≥0∞, d ≠ 0 → d ≠ ⊤ → d * (a / (d * b)) = a / b := by
    intro a b d hd0 hdtop
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdtop),
      show d * (d⁻¹ * b⁻¹ * a) = d * d⁻¹ * (b⁻¹ * a) by ring,
      ENNReal.mul_inv_cancel hd0 hdtop, one_mul, ← ENNReal.div_eq_inv_mul]
  rw [key _ _ _ hc0 hctop, ENNReal.ofReal_div_of_pos hsumpos]


/-! ### The Gibbsian specification of a homogeneous nearest-neighbour potential -/

/-- The Gibbsian specification of the homogeneous nearest-neighbour potential `(φ₁, φ₂)` at
inverse temperature `β`, with the uniform probability measure on `E` as reference measure. -/
def homogeneousNNSpecification (φ₁ : E → ℝ) (φ₂ : E → E → ℝ) (β : ℝ) : Specification ℤ E :=
  Potential.gibbsSpecificationOfAbsolutelySummable (Φ := homogeneousNNPotential φ₁ φ₂)
    (uniformOn (Set.univ : Set E)) β

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Hamiltonian of a homogeneous nearest-neighbour potential in a singleton consists of the
site term and the two bonds at the site. -/
lemma hamiltonian_homogeneousNNPotential_singleton (i : ℤ) (σ : ℤ → E) :
    (homogeneousNNPotential φ₁ φ₂).hamiltonian {i} σ
      = φ₁ (σ i) + φ₂ (σ (i - 1)) (σ i) + φ₂ (σ i) (σ (i + 1)) := by
  classical
  rw [Potential.hamiltonian_eq_tsum]
  have hcard1 : ({i - 1, i} : Finset ℤ).card = 2 := Finset.card_pair (by omega)
  have hcard2 : ({i, i + 1} : Finset ℤ).card = 2 := Finset.card_pair (by omega)
  have hne1 : ({i - 1, i} : Finset ℤ) ≠ {i, i + 1} := fun h ↦ by
    have h' : ({i - 1, i - 1 + 1} : Finset ℤ) = {i, i + 1} := by rw [sub_add_cancel]; exact h
    have := pair_succ_inj h'
    omega
  have hne2 : ({i - 1, i} : Finset ℤ) ≠ {i} := fun h ↦ by
    rw [h, Finset.card_singleton] at hcard1; omega
  have hne3 : ({i, i + 1} : Finset ℤ) ≠ {i} := fun h ↦ by
    rw [h, Finset.card_singleton] at hcard2; omega
  have hsupp : ∀ A ∉ ({({i - 1, i} : Finset ℤ), {i, i + 1}, {i}} : Finset (Finset ℤ)),
      (homogeneousNNPotential φ₁ φ₂).hamiltonianTerms {i} σ A = 0 := by
    intro A hA
    by_cases hd : Disjoint A {i}
    · exact Potential.hamiltonianTerms_of_disjoint hd σ
    · rw [Potential.hamiltonianTerms_of_not_disjoint hd σ]
      have hiA : i ∈ A := by
        obtain ⟨a, ha, ha'⟩ := Finset.not_disjoint_iff.1 hd
        rw [Finset.mem_singleton] at ha'
        exact ha' ▸ ha
      by_cases hb : ∃ j : ℤ, A = {j, j + 1}
      · exfalso
        obtain ⟨j, rfl⟩ := hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiA
        rcases hiA with rfl | hij
        · exact hA (by simp)
        · have : j = i - 1 := by omega
          subst this
          exact hA (by simp [sub_add_cancel])
      · by_cases hs : ∃ j : ℤ, A = {j}
        · exfalso
          obtain ⟨j, rfl⟩ := hs
          rw [Finset.mem_singleton] at hiA
          subst hiA
          exact hA (by simp)
        · exact homogeneousNNPotential_of_not φ₁ φ₂ hb hs σ
  rw [tsum_eq_sum hsupp, Finset.sum_insert (by simp [hne1, hne2]),
    Finset.sum_insert (by simp [hne3]), Finset.sum_singleton,
    Potential.hamiltonianTerms_of_not_disjoint (by simp) σ,
    Potential.hamiltonianTerms_of_not_disjoint (by simp) σ,
    Potential.hamiltonianTerms_of_not_disjoint (by simp) σ,
    show ({i - 1, i} : Finset ℤ) = {i - 1, i - 1 + 1} by rw [sub_add_cancel],
    homogeneousNNPotential_pair, homogeneousNNPotential_pair, homogeneousNNPotential_singleton,
    sub_add_cancel]
  ring

/-! ### The determining function of a homogeneous nearest-neighbour specification -/

/-- Georgii (3.1) for a homogeneous nearest-neighbour potential: the determining function of
`homogeneousNNSpecification φ₁ φ₂ β` is the single-site Boltzmann weight
`exp(-β(φ₁(y) + φ₂(x,y) + φ₂(y,z)))`, normalised over `y`. -/
def homogeneousNNDeterminingFun (φ₁ : E → ℝ) (φ₂ : E → E → ℝ) (β : ℝ) (x y z : E) : ℝ :=
  Real.exp (-β * (φ₁ y + φ₂ x y + φ₂ y z)) / ∑ u, Real.exp (-β * (φ₁ u + φ₂ x u + φ₂ u z))

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma homogeneousNNDeterminingFun_pos (β : ℝ) (x y z : E) :
    0 < homogeneousNNDeterminingFun φ₁ φ₂ β x y z :=
  div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty)

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma sum_homogeneousNNDeterminingFun (β : ℝ) (x z : E) :
    ∑ y, homogeneousNNDeterminingFun φ₁ φ₂ β x y z = 1 := by
  simp only [homogeneousNNDeterminingFun]
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty).ne'

omit [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The single-site Boltzmann factor of a homogeneous nearest-neighbour potential. -/
lemma boltzmannFactor_homogeneousNNPotential_singleton (β : ℝ) (i : ℤ) (ω : ℤ → E) (x : E) :
    (homogeneousNNPotential φ₁ φ₂).boltzmannFactor β {i} (Function.update ω i x)
      = ENNReal.ofReal (Real.exp (-β * (φ₁ x + φ₂ (ω (i - 1)) x + φ₂ x (ω (i + 1))))) := by
  rw [Potential.boltzmannFactor, hamiltonian_homogeneousNNPotential_singleton,
    Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- **Georgii (3.9), the converse direction.** The Gibbsian specification of a homogeneous
nearest-neighbour potential on `ℤ` is a positive homogeneous Markov specification in the sense
of Georgii (3.1), with determining function `homogeneousNNDeterminingFun φ₁ φ₂ β`. -/
theorem isPositiveHomogeneousMarkovWith_homogeneousNNSpecification (β : ℝ) :
    IsPositiveHomogeneousMarkovWith (homogeneousNNSpecification φ₁ φ₂ β)
      (homogeneousNNDeterminingFun φ₁ φ₂ β) where
  pos := homogeneousNNDeterminingFun_pos φ₁ φ₂ β
  singleton_apply i y ω :=
    gibbsSpecification_singleton_apply_of_boltzmannFactor (homogeneousNNPotential φ₁ φ₂) β i ω
      (w := fun x ↦ Real.exp (-β * (φ₁ x + φ₂ (ω (i - 1)) x + φ₂ x (ω (i + 1)))))
      (fun _ ↦ Real.exp_pos _)
      (boltzmannFactor_homogeneousNNPotential_singleton φ₁ φ₂ β i ω) y

theorem isPositiveHomogeneousMarkov_homogeneousNNSpecification (β : ℝ) :
    IsPositiveHomogeneousMarkov (homogeneousNNSpecification φ₁ φ₂ β) :=
  ⟨_, isPositiveHomogeneousMarkovWith_homogeneousNNSpecification φ₁ φ₂ β⟩

/-! ### Georgii, Comment (3.2): a positive homogeneous Markov specification is determined by `g` -/

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- **Georgii, Comment (3.2).** The determining function of a positive homogeneous Markov
specification is unique. -/
lemma determiningFun_unique {γ : Specification ℤ E} {g g' : E → E → E → ℝ}
    (hg : IsPositiveHomogeneousMarkovWith γ g) (hg' : IsPositiveHomogeneousMarkovWith γ g') :
    g = g' := by
  funext x y z
  have h1 := hg.singleton_apply 0 y (fun k ↦ if k = -1 then x else z)
  have h2 := hg'.singleton_apply 0 y (fun k ↦ if k = -1 then x else z)
  have h3 := h1.symm.trans h2
  have hx : (if (0 : ℤ) - 1 = -1 then x else z) = x := by norm_num
  have hz : (if (0 : ℤ) + 1 = -1 then x else z) = z := by norm_num
  simp only [hx, hz] at h3
  exact (ENNReal.ofReal_eq_ofReal_iff (hg.pos x y z).le (hg'.pos x y z).le).1 h3

/-- **Georgii, Comment (3.2)**, via Theorem (1.33): two positive homogeneous Markov specifications
with the same determining function are equal. -/
theorem eq_of_isPositiveHomogeneousMarkovWith {γ γ' : Specification ℤ E} {g : E → E → E → ℝ}
    (hγ : IsPositiveHomogeneousMarkovWith γ g) (hγ' : IsPositiveHomogeneousMarkovWith γ' g) :
    γ = γ' := by
  obtain ⟨P, hP, hpos, rfl⟩ := exists_matrix_eq_markovSpecification (γ := γ) ⟨g, hγ⟩
  exact (eq_markovSpecification_of_determiningFun hpos hγ'
    (determiningFun_unique hγ (isPositiveHomogeneousMarkovWith_markovSpecification hpos))).symm

omit [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The inverse temperature can be absorbed into the potential: `β·(φ₁, φ₂)` has the same
determining function at `β = 1` as `(φ₁, φ₂)` at `β`. -/
lemma homogeneousNNDeterminingFun_smul (β : ℝ) :
    homogeneousNNDeterminingFun φ₁ φ₂ β
      = homogeneousNNDeterminingFun (fun x ↦ β * φ₁ x) (fun x y ↦ β * φ₂ x y) 1 := by
  funext x y z
  have he : ∀ u : E, Real.exp (-β * (φ₁ u + φ₂ x u + φ₂ u z))
      = Real.exp (-(1 : ℝ) * (β * φ₁ u + β * φ₂ x u + β * φ₂ u z)) := fun u ↦ by
    congr 1
    ring
  simp only [homogeneousNNDeterminingFun, he]

/-- **Georgii (2.35)/(3.9) for the inverse temperature.** `β Φ` is again a homogeneous
nearest-neighbour potential, so every `homogeneousNNSpecification φ₁ φ₂ β` is a
`homogeneousNNSpecification _ _ 1`. -/
theorem homogeneousNNSpecification_smul (β : ℝ) :
    homogeneousNNSpecification φ₁ φ₂ β
      = homogeneousNNSpecification (fun x ↦ β * φ₁ x) (fun x y ↦ β * φ₂ x y) 1 := by
  refine eq_of_isPositiveHomogeneousMarkovWith
    (isPositiveHomogeneousMarkovWith_homogeneousNNSpecification φ₁ φ₂ β) ?_
  have hg := isPositiveHomogeneousMarkovWith_homogeneousNNSpecification
    (fun x ↦ β * φ₁ x) (fun x y ↦ β * φ₂ x y) 1
  rwa [← homogeneousNNDeterminingFun_smul φ₁ φ₂ β] at hg

/-! ### Georgii, Corollary (3.9) -/

variable {P : Matrix E E ℝ}

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- **Georgii, Corollary (3.9), forward direction, at the level of potentials.** The potential
`Φ_{i,i+1} = -log P(σ_i, σ_{i+1})` of a positive stochastic matrix is the homogeneous
nearest-neighbour potential with vanishing self-energy and bond energy `-log P`. -/
lemma markovPotential_eq_homogeneousNNPotential (P : Matrix E E ℝ) :
    markovPotential P
      = homogeneousNNPotential (fun _ ↦ (0 : ℝ)) (fun x y ↦ -Real.log (P x y)) := by
  funext A σ
  by_cases hb : ∃ i : ℤ, A = {i, i + 1}
  · obtain ⟨i, rfl⟩ := hb
    rw [markovPotential_pair, homogeneousNNPotential_pair]
  · by_cases hs : ∃ i : ℤ, A = {i}
    · obtain ⟨i, rfl⟩ := hs
      rw [markovPotential_of_not_pair P (not_exists_pair_singleton i),
        homogeneousNNPotential_singleton]
    · rw [markovPotential_of_not_pair P hb, homogeneousNNPotential_of_not _ _ hb hs]

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The determining function of the homogeneous nearest-neighbour potential `-log P` is
Georgii's (3.11). -/
lemma homogeneousNNDeterminingFun_neg_log (hpos : ∀ x y, 0 < P x y) :
    homogeneousNNDeterminingFun (fun _ ↦ (0 : ℝ)) (fun x y ↦ -Real.log (P x y)) 1
      = markovDeterminingFun P := by
  have hexp : ∀ x y z : E,
      Real.exp (-(1 : ℝ) * ((0 : ℝ) + -Real.log (P x y) + -Real.log (P y z))) = P x y * P y z := by
    intro x y z
    rw [show -(1 : ℝ) * ((0 : ℝ) + -Real.log (P x y) + -Real.log (P y z))
        = Real.log (P x y) + Real.log (P y z) by ring, Real.exp_add,
      Real.exp_log (hpos x y), Real.exp_log (hpos y z)]
  funext x y z
  simp only [homogeneousNNDeterminingFun, markovDeterminingFun, hexp]
  rw [pow_two, Matrix.mul_apply]

/-- **Georgii, Corollary (3.9), forward direction.** The Markov specification of a positive
stochastic matrix `P` is the Gibbsian specification of the homogeneous nearest-neighbour
potential `Φ_{i,i+1} = -log P(σ_i, σ_{i+1})`. -/
theorem homogeneousNNSpecification_neg_log (hpos : ∀ x y, 0 < P x y) :
    homogeneousNNSpecification (fun _ ↦ (0 : ℝ)) (fun x y ↦ -Real.log (P x y)) 1
      = markovSpecification P :=
  eq_markovSpecification_of_determiningFun hpos
    (isPositiveHomogeneousMarkovWith_homogeneousNNSpecification _ _ 1)
    (homogeneousNNDeterminingFun_neg_log hpos)

/-- **Georgii, Corollary (3.9).** A specification on `ℤ` with finite state space is a positive
homogeneous Markov specification (Georgii (3.1)) if and only if it is Gibbsian for a homogeneous
nearest-neighbour potential, i.e. one of the form `Φ_{i} = φ₁(σ_i)`,
`Φ_{i,i+1} = φ₂(σ_i, σ_{i+1})`. -/
theorem isPositiveHomogeneousMarkov_iff_exists_homogeneousNNSpecification (γ : Specification ℤ E) :
    IsPositiveHomogeneousMarkov γ ↔
      ∃ (φ₁ : E → ℝ) (φ₂ : E → E → ℝ), γ = homogeneousNNSpecification φ₁ φ₂ 1 := by
  refine ⟨fun hγ ↦ ?_, ?_⟩
  · obtain ⟨P, hP, hpos, rfl⟩ := exists_matrix_eq_markovSpecification hγ
    exact ⟨fun _ ↦ 0, fun x y ↦ -Real.log (P x y), (homogeneousNNSpecification_neg_log hpos).symm⟩
  · rintro ⟨φ₁, φ₂, rfl⟩
    exact isPositiveHomogeneousMarkov_homogeneousNNSpecification φ₁ φ₂ 1

/-- **Georgii (3.5) for homogeneous nearest-neighbour potentials.** The Gibbsian specification of
a homogeneous nearest-neighbour potential on `ℤ` is the Markov specification of a positive
stochastic matrix `P` — the one computed from its determining function by formula (3.7) — and its
set of Gibbs measures is the singleton `{μ_P}`. -/
theorem exists_markovSpecification_eq_homogeneousNNSpecification (β : ℝ) :
    ∃ (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y),
      homogeneousNNSpecification φ₁ φ₂ β = markovSpecification P ∧
        GibbsMeasure.G (homogeneousNNSpecification φ₁ φ₂ β) = {stationaryChain P hP hpos} := by
  obtain ⟨P, hP, hpos, hγ⟩ := exists_matrix_eq_markovSpecification
    (isPositiveHomogeneousMarkov_homogeneousNNSpecification φ₁ φ₂ β)
  exact ⟨P, hP, hpos, hγ, by rw [hγ]; exact gibbsMeasure_eq_singleton P hP hpos⟩

/-- **Georgii (3.5) for homogeneous nearest-neighbour potentials**: existence and uniqueness of
the Gibbs measure. -/
theorem existsUnique_isGibbsMeasure_homogeneousNNSpecification (β : ℝ) :
    ∃! μ : Measure (ℤ → E),
      IsProbabilityMeasure μ ∧ (homogeneousNNSpecification φ₁ φ₂ β).IsGibbsMeasure μ := by
  obtain ⟨P, hP, hpos, hγ, -⟩ :=
    exists_markovSpecification_eq_homogeneousNNSpecification φ₁ φ₂ β
  rw [hγ]
  exact existsUnique_isGibbsMeasure P hP hpos

/-!
## Georgii Example (3.15): the one-dimensional Ising model

The Ising potential (3.13) `Φ_{i,i+1} = -J σ_i σ_{i+1}`, `Φ_{i} = -h σ_i` on the nearest-neighbour
graph of `ℤ` is a homogeneous nearest-neighbour potential, so Corollary (3.9) and Theorem (3.5)
apply: its Gibbsian specification is the Markov specification of an explicit positive stochastic
matrix `P_{J,h}`, and `𝒢(Φ^{J,h}) = {μ_{J,h}}`.
-/

/-- The nearest-neighbour graph on `ℤ`: `i ~ j` iff `|i - j| = 1`. This is the `d = 1` lattice
graph of `GibbsMeasure/Model/Ising.lean` transported along `Fin 1 → ℤ ≃ ℤ`; the parameter set of
Chapter 3 is `ℤ` itself. -/
def chainGraph : SimpleGraph ℤ where
  Adj i j := |i - j| = 1
  symm := ⟨fun i j h ↦ by
    have h' : |i - j| = 1 := h
    have : |j - i| = 1 := by rw [show j - i = -(i - j) by ring, abs_neg]; exact h'
    exact this⟩
  loopless := ⟨fun i h ↦ by
    have h' : |i - i| = 1 := h
    simp at h'⟩

lemma chainGraph_adj_iff {i j : ℤ} : chainGraph.Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  constructor
  · intro hij
    have h : |i - j| = 1 := hij
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h
    omega
  · intro h
    have h' : |i - j| = 1 := by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega
    exact h'

lemma chainGraph_adj_succ (i : ℤ) : chainGraph.Adj i (i + 1) :=
  chainGraph_adj_iff.2 (Or.inl rfl)

noncomputable instance : chainGraph.LocallyFinite := fun v ↦
  Set.Finite.fintype <| (Set.finite_range (fun b : Bool ↦ if b then v + 1 else v - 1)).subset <| by
    rintro y hy
    rcases chainGraph_adj_iff.1 hy with rfl | h
    · exact ⟨true, by simp⟩
    · exact ⟨false, by simp; omega⟩

/-- **Georgii (3.13).** The one-dimensional Ising potential is the homogeneous nearest-neighbour
potential with self-energy `φ₁(x) = -h σ(x)` and bond energy `φ₂(x,y) = -J σ(x) σ(y)`. -/
theorem isingPotential_chainGraph (J h : ℝ) :
    isingPotential chainGraph J h
      = homogeneousNNPotential (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) := by
  funext A σ
  by_cases hb : ∃ i : ℤ, A = {i, i + 1}
  · obtain ⟨i, rfl⟩ := hb
    have hcard : ({i, i + 1} : Finset ℤ).card = 2 := Finset.card_pair (by omega)
    rw [homogeneousNNPotential_pair,
      show isingPotential chainGraph J h {i, i + 1} σ
        = Potential.nearestNeighbourPair chainGraph J h spin {i, i + 1} σ from rfl,
      Potential.nearestNeighbourPair_apply_pair
        ⟨hcard, i, by simp, i + 1, by simp, chainGraph_adj_succ i⟩,
      Finset.prod_pair (by omega : i ≠ i + 1)]
  · by_cases hs : ∃ i : ℤ, A = {i}
    · obtain ⟨i, rfl⟩ := hs
      rw [homogeneousNNPotential_singleton,
        show isingPotential chainGraph J h {i} σ
          = Potential.nearestNeighbourPair chainGraph J h spin {i} σ from rfl,
        Potential.nearestNeighbourPair_apply_card_one (Finset.card_singleton i),
        Finset.sum_singleton]
    · have h1 : ¬ A.card = 1 := fun hc ↦ hs (Finset.card_eq_one.1 hc)
      have h2 : ¬ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, chainGraph.Adj i j) := by
        rintro ⟨hcard, i, hiA, j, hjA, hij⟩
        have hAij : ({i, j} : Finset ℤ) = A :=
          Finset.eq_of_subset_of_card_le
            (by
              intro x hx
              rcases Finset.mem_insert.1 hx with rfl | hx
              · exact hiA
              · rw [Finset.mem_singleton] at hx; exact hx ▸ hjA)
            (le_of_eq (by rw [hcard, Finset.card_pair hij.ne]))
        rcases chainGraph_adj_iff.1 hij with rfl | rfl
        · exact hb ⟨i, hAij.symm⟩
        · exact hb ⟨j, by rw [← hAij, Finset.pair_comm]⟩
      rw [homogeneousNNPotential_of_not _ _ hb hs,
        show isingPotential chainGraph J h A σ
          = Potential.nearestNeighbourPair chainGraph J h spin A σ from rfl,
        Potential.nearestNeighbourPair_apply_eq_zero h1 h2]

/-- **Georgii (3.13)/(3.15).** The Ising specification on `ℤ` at inverse temperature `β` is the
Gibbsian specification of a homogeneous nearest-neighbour potential. -/
theorem isingSpecification_chainGraph (J h β : ℝ) :
    isingSpecification chainGraph J h β
      = homogeneousNNSpecification (fun b ↦ -h * spin b)
          (fun x y ↦ -J * (spin x * spin y)) β := by
  rw [isingSpecification, Potential.gibbsSpecification_congr uniformSpinMeasure β
      (isingPotential_chainGraph J h), homogeneousNNSpecification]
  simp only [uniformSpinMeasure_eq_uniformOn]

/-! ### The determining function (3.14) of the Ising chain -/

/-- **Georgii (3.14).** The determining function of the one-dimensional Ising specification with
interaction `J` and external field `h`:
`g(x,y,z) = e^{σ_y (h + J σ_x + J σ_z)} / 2 cosh(h + J σ_x + J σ_z)`. -/
def isingChainDetFun (J h : ℝ) (x y z : Bool) : ℝ :=
  Real.exp (spin y * (h + J * spin x + J * spin z))
    / (2 * Real.cosh (h + J * spin x + J * spin z))

lemma isingChainDetFun_pos (J h : ℝ) (x y z : Bool) : 0 < isingChainDetFun J h x y z :=
  div_pos (Real.exp_pos _) (by positivity)

lemma sum_isingChainDetFun (J h : ℝ) (x z : Bool) : ∑ y, isingChainDetFun J h x y z = 1 := by
  simp only [isingChainDetFun, ← Finset.sum_div]
  rw [Fintype.sum_bool]
  have hc : 2 * Real.cosh (h + J * spin x + J * spin z)
      = Real.exp (h + J * spin x + J * spin z) + Real.exp (-(h + J * spin x + J * spin z)) := by
    rw [Real.cosh_eq]; ring
  rw [hc]
  have h1 : Real.exp (spin true * (h + J * spin x + J * spin z))
      = Real.exp (h + J * spin x + J * spin z) := by norm_num [spin]
  have h2 : Real.exp (spin false * (h + J * spin x + J * spin z))
      = Real.exp (-(h + J * spin x + J * spin z)) := by
    congr 1; simp [spin]
  rw [h1, h2]
  exact div_self (by positivity)

/-- **Georgii (3.14).** The determining function of the Gibbsian specification of the
one-dimensional Ising potential at inverse temperature `β` is that of the Ising potential with
interaction `βJ` and external field `βh`. -/
theorem homogeneousNNDeterminingFun_ising (J h β : ℝ) :
    homogeneousNNDeterminingFun (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) β
      = isingChainDetFun (β * J) (β * h) := by
  funext x y z
  have hf : ∀ u : Bool,
      Real.exp (-β * ((-h * spin u) + (-J * (spin x * spin u)) + (-J * (spin u * spin z))))
        = Real.exp (spin u * (β * h + β * J * spin x + β * J * spin z)) := by
    intro u; congr 1; ring
  have hden : ∑ u : Bool,
      Real.exp (-β * ((-h * spin u) + (-J * (spin x * spin u)) + (-J * (spin u * spin z))))
        = 2 * Real.cosh (β * h + β * J * spin x + β * J * spin z) := by
    rw [Finset.sum_congr rfl fun u _ ↦ hf u, Fintype.sum_bool, Real.cosh_eq]
    have h1 : Real.exp (spin true * (β * h + β * J * spin x + β * J * spin z))
        = Real.exp (β * h + β * J * spin x + β * J * spin z) := by norm_num [spin]
    have h2 : Real.exp (spin false * (β * h + β * J * spin x + β * J * spin z))
        = Real.exp (-(β * h + β * J * spin x + β * J * spin z)) := by
      congr 1; simp [spin]
    rw [h1, h2]; ring
  simp only [homogeneousNNDeterminingFun, isingChainDetFun]
  rw [hf y, hden]

/-! ### Georgii (3.16): the Perron–Frobenius eigenvalue of the Ising chain -/

/-- **Georgii (3.16).** The Perron–Frobenius eigenvalue of Georgii's matrix `Q` for the
one-dimensional Ising model: `q_{J,h} = e^{-h}(cosh h + sqrt(e^{-4J} + sinh² h))`. -/
def isingChainPerronRoot (J h : ℝ) : ℝ :=
  Real.exp (-h) * (Real.cosh h + Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2))

lemma isingChainSqrt_sq (J h : ℝ) :
    Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) ^ 2
      = Real.exp (-(4 * J)) + Real.sinh h ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma isingChainSqrt_pos (J h : ℝ) : 0 < Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) :=
  Real.sqrt_pos.2 (by positivity)

/-- The square root in (3.16) strictly dominates `|sinh h|`, since `e^{-4J} > 0`. -/
lemma abs_sinh_lt_isingChainSqrt (J h : ℝ) :
    |Real.sinh h| < Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) := by
  have hE : 0 < Real.exp (-(4 * J)) := Real.exp_pos _
  have hs := isingChainSqrt_sq J h
  have hspos := isingChainSqrt_pos J h
  nlinarith [sq_abs (Real.sinh h), abs_nonneg (Real.sinh h)]

lemma isingChainPerronRoot_pos (J h : ℝ) : 0 < isingChainPerronRoot J h :=
  mul_pos (Real.exp_pos _) (by
    have := Real.cosh_pos h
    have := isingChainSqrt_pos J h
    linarith)

/-- `q_{J,h} > 1`: the Perron root of `Q` exceeds `Q(+,+) = 1`. -/
lemma one_lt_isingChainPerronRoot (J h : ℝ) : 1 < isingChainPerronRoot J h := by
  have hb : 0 < Real.exp (-h) := Real.exp_pos _
  have hab : Real.exp h * Real.exp (-h) = 1 := by
    rw [← Real.exp_add]; simp
  have hcosh : Real.cosh h = (Real.exp h + Real.exp (-h)) / 2 := Real.cosh_eq h
  have hsinh : Real.sinh h = (Real.exp h - Real.exp (-h)) / 2 := Real.sinh_eq h
  have hlt : Real.sinh h < Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) :=
    lt_of_le_of_lt (le_abs_self _) (abs_sinh_lt_isingChainSqrt J h)
  simp only [isingChainPerronRoot]
  nlinarith

/-- `q_{J,h} > e^{-2h} = Q(-,-)`. -/
lemma exp_lt_isingChainPerronRoot (J h : ℝ) :
    Real.exp (-(2 * h)) < isingChainPerronRoot J h := by
  have hb : 0 < Real.exp (-h) := Real.exp_pos _
  have hb2 : Real.exp (-(2 * h)) = Real.exp (-h) * Real.exp (-h) := by
    rw [← Real.exp_add]; ring_nf
  have hab : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  have hcosh : Real.cosh h = (Real.exp h + Real.exp (-h)) / 2 := Real.cosh_eq h
  have hsinh : Real.sinh h = (Real.exp h - Real.exp (-h)) / 2 := Real.sinh_eq h
  have hlt : -Real.sinh h < Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) :=
    lt_of_le_of_lt (neg_le_abs _) (abs_sinh_lt_isingChainSqrt J h)
  simp only [isingChainPerronRoot]
  nlinarith

/-- **Georgii's characteristic equation for (3.16)**: `(e^{-2h} - q)(1 - q) = e^{-2h-4J}`. -/
theorem isingChainPerronRoot_char (J h : ℝ) :
    (isingChainPerronRoot J h - 1) * (isingChainPerronRoot J h - Real.exp (-(2 * h)))
      = Real.exp (-(2 * h)) * Real.exp (-(4 * J)) := by
  set a := Real.exp h with ha
  set b := Real.exp (-h) with hb
  set s := Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) with hsdef
  have hab : a * b = 1 := by rw [ha, hb, ← Real.exp_add]; simp
  have hb2 : Real.exp (-(2 * h)) = b * b := by rw [hb, ← Real.exp_add]; ring_nf
  have hs' : s ^ 2 = Real.exp (-(4 * J)) + ((a - b) / 2) ^ 2 := by
    rw [hsdef, isingChainSqrt_sq, Real.sinh_eq, ha, hb]
  have hcosh : Real.cosh h = (a + b) / 2 := by rw [Real.cosh_eq, ha, hb]
  simp only [isingChainPerronRoot, hcosh, hb2]
  linear_combination ((a * b - b ^ 2) / 2 + b * s) * hab + b ^ 2 * hs'

/-! ### Georgii (3.7)/(3.17): the matrix `Q` and the transition matrix of the Ising chain -/

/-- **Georgii (3.7) for the Ising chain.** The auxiliary matrix `Q(x,y) = g(+,x,y)/g(+,+,y)` of
the determining function (3.14) at the reference state `a = +`:
`Q(x,y) = e^{(σ_x - 1)(h + J + J σ_y)}`, i.e. `Q(+,·) = (1, 1)` and
`Q(-,·) = (e^{-2h}, e^{-2h-4J})`. -/
def isingChainQ (J h : ℝ) : Matrix Bool Bool ℝ :=
  Matrix.of fun x y ↦ Real.exp ((spin x - 1) * (h + J + J * spin y))

lemma isingChainQ_pos (J h : ℝ) (x y : Bool) : 0 < isingChainQ J h x y := Real.exp_pos _

@[simp] lemma isingChainQ_true (J h : ℝ) (y : Bool) : isingChainQ J h true y = 1 := by
  simp [isingChainQ, spin]

lemma isingChainQ_false_false (J h : ℝ) : isingChainQ J h false false = Real.exp (-(2 * h)) := by
  simp only [isingChainQ, Matrix.of_apply]
  congr 1
  simp [spin]
  ring

lemma isingChainQ_false_true (J h : ℝ) :
    isingChainQ J h false true = Real.exp (-(2 * h)) * Real.exp (-(4 * J)) := by
  simp only [isingChainQ, Matrix.of_apply]
  rw [← Real.exp_add]
  congr 1
  simp [spin]
  ring

/-- The matrix `Q` of Georgii (3.7) computed from the determining function (3.14). -/
theorem detQ_isingChainDetFun (J h : ℝ) :
    detQ Bool (isingChainDetFun J h) true = isingChainQ J h := by
  have key : ∀ u v c : ℝ, c ≠ 0 → Real.exp u / c / (Real.exp v / c) = Real.exp (u - v) := by
    intro u v c hc
    rw [Real.exp_sub]
    field_simp
  ext x y
  have ht : h + J * spin true + J * spin y = h + J + J * spin y := by simp [spin]
  have hc : (2 * Real.cosh (h + J + J * spin y)) ≠ 0 := by positivity
  simp only [detQ, Matrix.of_apply, isingChainQ, isingChainDetFun, ht]
  rw [key _ _ _ hc]
  congr 1
  cases x <;> cases y <;> simp [spin] <;> ring

/-- Georgii (3.7) for the Ising chain: the strictly positive right eigenvector of `Q` for its
Perron root `q_{J,h}`, normalised by `r(+) = 1`; then `r(-) = q_{J,h} - 1`. -/
def isingChainPerronVector (J h : ℝ) : Bool → ℝ :=
  fun b ↦ if b then 1 else isingChainPerronRoot J h - 1

@[simp] lemma isingChainPerronVector_true (J h : ℝ) : isingChainPerronVector J h true = 1 := rfl

@[simp] lemma isingChainPerronVector_false (J h : ℝ) :
    isingChainPerronVector J h false = isingChainPerronRoot J h - 1 := rfl

lemma isingChainPerronVector_pos (J h : ℝ) (x : Bool) : 0 < isingChainPerronVector J h x := by
  cases x
  · simpa [isingChainPerronVector] using sub_pos.2 (one_lt_isingChainPerronRoot J h)
  · simp [isingChainPerronVector]

/-- **Georgii (3.17).** The transition matrix of the one-dimensional Ising model with interaction
`J` and external field `h`:
`P(+,+) = q⁻¹`, `P(+,-) = 1 - q⁻¹`, `P(-,-) = e^{-2h} q⁻¹`, `P(-,+) = 1 - e^{-2h} q⁻¹`,
with `q = q_{J,h}` the Perron root (3.16). -/
def isingChainP (J h : ℝ) : Matrix Bool Bool ℝ := Matrix.of fun x y ↦
  if x then (if y then (isingChainPerronRoot J h)⁻¹ else 1 - (isingChainPerronRoot J h)⁻¹)
  else (if y then 1 - Real.exp (-(2 * h)) * (isingChainPerronRoot J h)⁻¹
        else Real.exp (-(2 * h)) * (isingChainPerronRoot J h)⁻¹)

@[simp] lemma isingChainP_true_true (J h : ℝ) :
    isingChainP J h true true = (isingChainPerronRoot J h)⁻¹ := rfl

@[simp] lemma isingChainP_true_false (J h : ℝ) :
    isingChainP J h true false = 1 - (isingChainPerronRoot J h)⁻¹ := rfl

@[simp] lemma isingChainP_false_false (J h : ℝ) :
    isingChainP J h false false
      = Real.exp (-(2 * h)) * (isingChainPerronRoot J h)⁻¹ := rfl

@[simp] lemma isingChainP_false_true (J h : ℝ) :
    isingChainP J h false true
      = 1 - Real.exp (-(2 * h)) * (isingChainPerronRoot J h)⁻¹ := rfl

lemma isingChainP_pos (J h : ℝ) (x y : Bool) : 0 < isingChainP J h x y := by
  have hq : 0 < isingChainPerronRoot J h := isingChainPerronRoot_pos J h
  have h1 : 1 < isingChainPerronRoot J h := one_lt_isingChainPerronRoot J h
  have h2 : Real.exp (-(2 * h)) < isingChainPerronRoot J h := exp_lt_isingChainPerronRoot J h
  cases x <;> cases y <;>
    simp only [isingChainP_true_true, isingChainP_true_false,
      isingChainP_false_false, isingChainP_false_true]
  · exact mul_pos (Real.exp_pos _) (inv_pos.2 hq)
  · rw [sub_pos, ← lt_div_iff₀ (by positivity), one_div]
    simpa [inv_inv] using h2
  · rw [sub_pos]
    simpa using (inv_lt_one_iff₀).2 (Or.inr h1)
  · exact inv_pos.2 hq

lemma isingChainP_mem_rowStochastic (J h : ℝ) :
    isingChainP J h ∈ Matrix.rowStochastic ℝ Bool := by
  refine Matrix.mem_rowStochastic_iff_sum.2 ⟨fun x y ↦ (isingChainP_pos J h x y).le, ?_⟩
  intro x
  rw [Fintype.sum_bool]
  cases x <;> simp

/-- Georgii (3.7): the defining relation `Q(x,y) r(y) = q r(x) P(x,y)` of the transition matrix
of the Ising chain. -/
theorem isingChainQ_mul_perronVector (J h : ℝ) (x y : Bool) :
    isingChainQ J h x y * isingChainPerronVector J h y
      = isingChainPerronRoot J h * isingChainPerronVector J h x * isingChainP J h x y := by
  have hq : 0 < isingChainPerronRoot J h := isingChainPerronRoot_pos J h
  have hchar := isingChainPerronRoot_char J h
  cases x <;> cases y <;>
    simp only [isingChainQ_true, isingChainQ_false_false, isingChainQ_false_true,
      isingChainPerronVector_true, isingChainPerronVector_false, isingChainP_true_true,
      isingChainP_true_false, isingChainP_false_false, isingChainP_false_true] <;>
    field_simp
  nlinarith [hchar]

/-- `(q_{J,h}, r)` is an eigenpair of Georgii's matrix `Q` for the Ising chain. -/
theorem isingChainQ_mulVec (J h : ℝ) :
    isingChainQ J h *ᵥ isingChainPerronVector J h
      = isingChainPerronRoot J h • isingChainPerronVector J h := by
  have hchar := isingChainPerronRoot_char J h
  funext x
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Fintype.sum_bool]
  cases x <;>
    simp only [isingChainQ_true, isingChainQ_false_false, isingChainQ_false_true,
      isingChainPerronVector_true, isingChainPerronVector_false] <;> nlinarith [hchar]

/-! ### Georgii (3.15): the unique Gibbs measure of the one-dimensional Ising model -/

/-- The Ising specification on `ℤ` at `β = 1` has the determining function (3.14). -/
lemma isPositiveHomogeneousMarkovWith_isingChainDetFun (J h : ℝ) :
    IsPositiveHomogeneousMarkovWith
      (homogeneousNNSpecification (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) 1)
      (isingChainDetFun J h) := by
  have hg := isPositiveHomogeneousMarkovWith_homogeneousNNSpecification
    (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) 1
  rwa [homogeneousNNDeterminingFun_ising J h 1, one_mul, one_mul] at hg

/-- **Georgii (3.11) for the Ising chain.** The determining function (3.11) of the transition
matrix (3.17) is the Ising determining function (3.14): `P_{J,h}` is indeed the matrix that
formula (3.7) attaches to `g`. -/
theorem markovDeterminingFun_isingChainP (J h : ℝ) :
    markovDeterminingFun (isingChainP J h) = isingChainDetFun J h := by
  refine markovDeterminingFun_of_eq_312 (isingChainDetFun_pos J h) (sum_isingChainDetFun J h)
    true (isingChainPerronRoot_pos J h) (isingChainPerronVector_pos J h) ?_
    (eq_312_of_isPositiveHomogeneousMarkovWith
      (isPositiveHomogeneousMarkovWith_isingChainDetFun J h) true)
  intro x y
  have hqv : isingChainPerronRoot J h * isingChainPerronVector J h x ≠ 0 :=
    (mul_pos (isingChainPerronRoot_pos J h) (isingChainPerronVector_pos J h x)).ne'
  rw [detQ_isingChainDetFun, eq_div_iff hqv, isingChainQ_mul_perronVector]
  ring

/-- **Georgii (3.7)/(3.17).** Formula (3.7), applied to the Ising determining function (3.14) at
the reference state `a = +`, produces exactly the transition matrix (3.17). -/
theorem matrixOfDetFun_isingChainDetFun (J h : ℝ) :
    matrixOfDetFun Bool (isingChainDetFun J h) (isingChainDetFun_pos J h) true
      = isingChainP J h :=
  matrixOfDetFun_eq_of_eigen (isingChainDetFun_pos J h) true (isingChainPerronRoot_pos J h)
    (isingChainPerronVector_pos J h)
    (by rw [detQ_isingChainDetFun]; exact isingChainQ_mulVec J h)
    (fun x y ↦ by rw [detQ_isingChainDetFun]; exact isingChainQ_mul_perronVector J h x y)

/-- **Georgii (3.16).** `q_{J,h}` is the Perron–Frobenius eigenvalue of Georgii's matrix `Q`. -/
theorem perronRoot_isingChainQ (J h : ℝ) :
    Matrix.perronRoot (isingChainQ J h) (isingChainQ_pos J h) = isingChainPerronRoot J h :=
  (Matrix.eq_perronRoot_of_pos_eigenvector (isingChainQ J h) (isingChainQ_pos J h)
    (isingChainPerronVector_pos J h) (isingChainQ_mulVec J h)).symm

/-- **Georgii (3.15).** The Gibbsian specification of the one-dimensional Ising potential
`Φ^{J,h}` at inverse temperature `β` is the Markov specification of the transition matrix
`P_{βJ,βh}` of (3.17): `β Φ^{J,h} = Φ^{βJ,βh}`. -/
theorem isingSpecification_chainGraph_eq_markovSpecification (J h β : ℝ) :
    isingSpecification chainGraph J h β
      = markovSpecification (isingChainP (β * J) (β * h)) := by
  have hγ : IsPositiveHomogeneousMarkovWith
      (homogeneousNNSpecification (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) β)
      (isingChainDetFun (β * J) (β * h)) := by
    have hg := isPositiveHomogeneousMarkovWith_homogeneousNNSpecification
      (fun b ↦ -h * spin b) (fun x y ↦ -J * (spin x * spin y)) β
    rwa [homogeneousNNDeterminingFun_ising J h β] at hg
  rw [isingSpecification_chainGraph]
  exact eq_markovSpecification_of_determiningFun (isingChainP_pos (β * J) (β * h)) hγ
    (markovDeterminingFun_isingChainP (β * J) (β * h)).symm

/-- **Georgii (3.15).** `𝒢(Φ^{βJ,βh}) = {μ_{βJ,βh}}`: the one-dimensional Ising model has, at
every coupling, external field and inverse temperature, exactly one Gibbs measure, the stationary
Markov chain with transition matrix `P_{βJ,βh}` of (3.17). -/
theorem gibbsMeasure_isingSpecification_chainGraph (J h β : ℝ) :
    GibbsMeasure.G (isingSpecification chainGraph J h β)
      = {stationaryChain (isingChainP (β * J) (β * h))
          (isingChainP_mem_rowStochastic (β * J) (β * h))
          (isingChainP_pos (β * J) (β * h))} := by
  rw [isingSpecification_chainGraph_eq_markovSpecification]
  exact gibbsMeasure_eq_singleton _ _ _

/-- **Georgii (3.15).** Existence and uniqueness of the Gibbs measure of the one-dimensional
Ising model. -/
theorem existsUnique_isGibbsMeasure_isingSpecification_chainGraph (J h β : ℝ) :
    ∃! μ : Measure (ℤ → Bool),
      IsProbabilityMeasure μ ∧ (isingSpecification chainGraph J h β).IsGibbsMeasure μ := by
  rw [isingSpecification_chainGraph_eq_markovSpecification]
  exact existsUnique_isGibbsMeasure _ (isingChainP_mem_rowStochastic (β * J) (β * h))
    (isingChainP_pos (β * J) (β * h))

/-! ### The one-dimensional distributions of `μ_P`, and integrals of single-site observables -/

section OneDim
variable (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

/-- The one-dimensional marginals of the stationary chain are the stationary distribution:
`μ_P(σ_i = x) = α_P(x)`. -/
theorem stationaryChain_apply_eq_stationaryDist (i : ℤ) (x : E) :
    stationaryChain P hP hpos {σ : ℤ → E | σ i = x}
      = ENNReal.ofReal (stationaryDist P hP hpos x) := by
  have h := markovChain_cylinder P hP hpos (le_refl i) (fun _ ↦ x)
  have hset : {τ : ℤ → E | ∀ k ∈ Finset.Icc i i, τ k = x} = {σ : ℤ → E | σ i = x} := by
    ext τ
    simp [Finset.Icc_self]
  rw [hset] at h
  simpa using h

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The uniqueness of the stationary distribution: a probability vector fixed by `ᵥ* P` is
`α_P`. -/
theorem stationaryDist_eq_of_vecMul {α : E → ℝ} (hα : α ᵥ* P = α) (hsum : ∑ x, α x = 1) :
    stationaryDist P hP hpos = α :=
  Matrix.eq_of_vecMul_eq_of_sum_eq P hP hpos (vecMul_stationaryDist P hP hpos) hα
    (((stationaryDist_mem_stdSimplex P hP hpos).2).trans hsum.symm)

/-- The expectation of a single-site observable under the stationary chain. -/
theorem integral_stationaryChain_apply (i : ℤ) (f : E → ℝ) :
    ∫ σ, f (σ i) ∂(stationaryChain P hP hpos) = ∑ x, stationaryDist P hP hpos x * f x := by
  have hprob := isProbabilityMeasure_stationaryChain P hP hpos
  have hmeas : Measurable (fun σ : ℤ → E ↦ σ i) := measurable_pi_apply i
  have hmap : IsProbabilityMeasure ((stationaryChain P hP hpos).map (fun σ : ℤ → E ↦ σ i)) := by
    refine ⟨?_⟩
    rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, measure_univ]
  rw [← integral_map hmeas.aemeasurable (Measurable.of_discrete (f := f)).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hx : ((stationaryChain P hP hpos).map (fun σ : ℤ → E ↦ σ i)) {x}
      = ENNReal.ofReal (stationaryDist P hP hpos x) := by
    rw [Measure.map_apply hmeas (measurableSet_singleton x)]
    exact stationaryChain_apply_eq_stationaryDist P hP hpos i x
  rw [measureReal_def, hx, ENNReal.toReal_ofReal (stationaryDist_pos P hP hpos x).le, smul_eq_mul]

end OneDim

/-! ### Georgii (3.18)/(3.19): the stationary distribution and the magnetisation -/

/-- **Georgii (3.18).** The stationary distribution of the Ising transition matrix (3.17):
`α_{P_{J,h}}(σ) = ½(1 + σ sinh h / sqrt(e^{-4J} + sinh² h))`. -/
def isingChainStationary (J h : ℝ) : Bool → ℝ := fun b ↦
  (1 + spin b * Real.sinh h / Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2)) / 2

lemma sum_isingChainStationary (J h : ℝ) : ∑ b, isingChainStationary J h b = 1 := by
  rw [Fintype.sum_bool]
  simp only [isingChainStationary, spin]
  norm_num
  ring

lemma isingChainStationary_pos (J h : ℝ) (b : Bool) : 0 < isingChainStationary J h b := by
  have hs := isingChainSqrt_pos J h
  have habs := abs_sinh_lt_isingChainSqrt J h
  have hlt : |Real.sinh h| / Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) < 1 :=
    (div_lt_one hs).2 habs
  have hkey : |spin b * Real.sinh h
      / Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2)| < 1 := by
    rw [abs_div, abs_mul, abs_of_pos hs]
    have hspin : |spin b| = 1 := by cases b <;> simp [spin]
    rw [hspin, one_mul]
    exact hlt
  have := neg_lt_of_abs_lt hkey
  simp only [isingChainStationary]
  linarith

/-- The relation behind (3.18): `(s - sinh h)(q - e^{-2h}) = (q - 1)(s + sinh h)`, where `s` is
the square root of (3.16). -/
theorem isingChainStationary_key (J h : ℝ) :
    (Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) - Real.sinh h)
        * (isingChainPerronRoot J h - Real.exp (-(2 * h)))
      = (isingChainPerronRoot J h - 1)
        * (Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) + Real.sinh h) := by
  set s := Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) with hsdef
  have hab : Real.exp h * Real.exp (-h) = 1 := by rw [← Real.exp_add]; simp
  have hb2 : Real.exp (-(2 * h)) = Real.exp (-h) * Real.exp (-h) := by
    rw [← Real.exp_add]; ring_nf
  have hq2 : 2 * isingChainPerronRoot J h
      = 1 + Real.exp (-(2 * h)) + 2 * Real.exp (-h) * s := by
    simp only [isingChainPerronRoot, Real.cosh_eq, ← hsdef]
    rw [hb2]
    linear_combination hab
  have hSe : 2 * Real.exp (-h) * Real.sinh h = 1 - Real.exp (-(2 * h)) := by
    rw [Real.sinh_eq, hb2]
    linear_combination hab
  linear_combination (-s) * hSe + (-Real.sinh h) * hq2

theorem vecMul_isingChainStationary (J h : ℝ) :
    isingChainStationary J h ᵥ* isingChainP J h = isingChainStationary J h := by
  have hq : 0 < isingChainPerronRoot J h := isingChainPerronRoot_pos J h
  have hs : 0 < Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) := isingChainSqrt_pos J h
  have hkey := isingChainStationary_key J h
  funext y
  simp only [Matrix.vecMul, dotProduct, Fintype.sum_bool, isingChainStationary, spin]
  cases y
  · norm_num
    field_simp
    linear_combination (-1 : ℝ) * hkey
  · norm_num
    field_simp
    linear_combination hkey

/-- **Georgii (3.18).** -/
theorem stationaryDist_isingChainP (J h : ℝ) :
    stationaryDist (isingChainP J h) (isingChainP_mem_rowStochastic J h)
        (isingChainP_pos J h) = isingChainStationary J h :=
  stationaryDist_eq_of_vecMul _ _ _ (vecMul_isingChainStationary J h)
    (sum_isingChainStationary J h)

/-- **Georgii (3.19).** The magnetisation of the one-dimensional Ising model:
`μ_{J,h}(σ_i) = sinh h / sqrt(e^{-4J} + sinh² h)` at every site `i`. -/
theorem integral_spin_stationaryChain_isingChainP (J h : ℝ) (i : ℤ) :
    ∫ σ, spin (σ i) ∂(stationaryChain (isingChainP J h)
        (isingChainP_mem_rowStochastic J h) (isingChainP_pos J h))
      = Real.sinh h / Real.sqrt (Real.exp (-(4 * J)) + Real.sinh h ^ 2) := by
  rw [integral_stationaryChain_apply, stationaryDist_isingChainP, Fintype.sum_bool]
  simp only [isingChainStationary, spin]
  norm_num
  ring

end HomogeneousNearestNeighbour

end MeasureTheory.GibbsMeasure.Markov

end

end

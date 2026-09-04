/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.MarkovChain
public import GibbsMeasure.Model.MarkovChainInt
public import GibbsMeasure.Specification.Reindex

/-!
# Georgii (3.5) on the site set `ℤ^1`

Georgii's Example (15.40) applies the thermodynamic formalism of Chapter 15, stated on `ℤ^d`, to
the Markov chains of Chapter 3, stated on `ℤ`. The identification is the bijection
`ℤ ≃ (Unit → ℤ)`, `(Equiv.funUnique Unit ℤ).symm`, and this file transports Theorem (3.5) along
it using `Specification.reindex`:

* `markovSpecification_reindex`: the Gibbsian specification of the reindexed Markov potential is
  the reindexed Markov specification;
* `gibbsMeasure_reindex_eq_singleton`: **Georgii (3.5) on `ℤ^1`**, `𝒢(γ) = {μ_P ∘ (· ∘ e.symm)⁻¹}`;
* `isShiftInvariant_markovPotential_reindex`, `stationaryChain_mem_invariantFields_shiftGroup`,
  `invariantG_reindex_eq_singleton`: the reindexed potential lies in `ℬ_Θ` and the reindexed chain
  is the unique shift-invariant Gibbs measure, `𝒢_Θ(γ) = {μ_P ∘ (· ∘ e.symm)⁻¹}` on `ℤ^1` — the
  hypotheses `μ_Q ∈ 𝓟_Θ` and `Φ ∈ ℬ_Θ` of (15.40).
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

/-- The bijection `ℤ ≃ ℤ^1` of Georgii (15.40) is additive. -/
lemma coe_addEquiv_funUnique_symm :
    ((AddEquiv.funUnique Unit ℤ).symm : ℤ ≃ (Unit → ℤ)) = (Equiv.funUnique Unit ℤ).symm :=
  Equiv.ext fun _ ↦ rfl

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Along `ℤ ≃ ℤ^1`, the shift `θ_j` of `ℤ` corresponds to the shift `θ_{(j)}` of `ℤ^1`. -/
lemma reindex_shift_funUnique (j : ℤ) :
    (shift E j).reindex (Equiv.funUnique Unit ℤ).symm = shift E (fun _ : Unit ↦ j) := by
  rw [← coe_addEquiv_funUnique_symm, Transformation.reindex_shift]
  rfl

omit [DecidableEq E] in
/-- The Gibbsian specification of the Markov potential reindexed to `ℤ^1` is the reindexed
Markov specification of Georgii (3.6). -/
theorem markovSpecification_reindex (P : Matrix E E ℝ) :
    Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm)
        (uniformOn (Set.univ : Set E)) 1 =
      (markovSpecification P).reindex (Equiv.funUnique Unit ℤ).symm :=
  Potential.gibbsSpecificationOfAbsolutelySummable_reindex _ _ _ _

/-- **Georgii (3.5) on `ℤ^1`.** The Gibbsian specification of the reindexed Markov potential has the
reindexed stationary chain as its unique Gibbs measure. -/
theorem gibbsMeasure_reindex_eq_singleton (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    G (Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm)
        (uniformOn (Set.univ : Set E)) 1) =
      {(stationaryChain P hP hpos).map
        (MeasurableEquiv.arrowCongr' (Equiv.funUnique Unit ℤ).symm (MeasurableEquiv.refl E))} := by
  rw [markovSpecification_reindex, ← image_G_reindex, gibbsMeasure_eq_singleton P hP hpos,
    Set.image_singleton]

omit [Fintype E] [DecidableEq E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Markov potential reindexed to `ℤ^1` is shift-invariant: `Φ ∈ ℬ_Θ` in Georgii (15.40). -/
theorem isShiftInvariant_markovPotential_reindex (P : Matrix E E ℝ) :
    ((markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm).IsShiftInvariant := by
  rw [← coe_addEquiv_funUnique_symm]
  exact (isShiftInvariant_markovPotential P).reindex (AddEquiv.funUnique Unit ℤ).symm

/-- The stationary chain `μ_P` is shift-invariant on `ℤ` (Georgii (5.11) for the shift group):
`μ_P ∈ 𝓟_Θ`. -/
theorem stationaryChain_mem_invariantFields_shiftGroup (P : Matrix E E ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y) :
    stationaryChain P hP hpos ∈ invariantFields (shiftGroup ℤ E) := by
  rw [mem_invariantFields_iff]
  refine ⟨isProbabilityMeasure_stationaryChain P hP hpos, ?_⟩
  rintro _ ⟨j, rfl⟩
  have hinv : Specification.IsInvariant (shift E j) (markovSpecification P) :=
    Potential.isInvariant_shift_gibbsSpecification (isShiftInvariant_markovPotential P) _ 1 j
  have hμ : stationaryChain P hP hpos ∈ G (markovSpecification P) := by
    rw [gibbsMeasure_eq_singleton P hP hpos]
    exact Set.mem_singleton _
  have h := Specification.map_mem_G_map (shift E j) hμ
  rw [show (markovSpecification P).map (shift E j) = markovSpecification P from hinv,
    gibbsMeasure_eq_singleton P hP hpos, Set.mem_singleton_iff] at h
  exact ⟨(shift E j).measurable_toFun, h⟩

/-- `μ_P ∈ 𝒢_Θ(γ_P)`: the stationary chain is a shift-invariant Gibbs measure on `ℤ`. -/
theorem stationaryChain_mem_invariantG (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    stationaryChain P hP hpos ∈ invariantG (markovSpecification P) (shiftGroup ℤ E) :=
  ⟨by rw [gibbsMeasure_eq_singleton P hP hpos]; exact Set.mem_singleton _,
    stationaryChain_mem_invariantFields_shiftGroup P hP hpos⟩

/-- **Georgii (3.5) and (15.40) on `ℤ^1`, shift-invariant form.** The reindexed stationary chain
is the unique shift-invariant Gibbs measure of the reindexed Markov potential:
`𝒢_Θ(Φ) = {μ_P ∘ (· ∘ e.symm)⁻¹}`. -/
theorem invariantG_reindex_eq_singleton (P : Matrix E E ℝ) (hP : P ∈ Matrix.rowStochastic ℝ E)
    (hpos : ∀ x y, 0 < P x y) :
    invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
        (Φ := (markovPotential P).reindex (Equiv.funUnique Unit ℤ).symm)
        (uniformOn (Set.univ : Set E)) 1) (shiftGroup (Unit → ℤ) E) =
      {(stationaryChain P hP hpos).map
        (MeasurableEquiv.arrowCongr' (Equiv.funUnique Unit ℤ).symm (MeasurableEquiv.refl E))} := by
  rw [markovSpecification_reindex, ← coe_addEquiv_funUnique_symm,
    ← image_invariantG_shiftGroup_reindex (AddEquiv.funUnique Unit ℤ).symm]
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨μ, hμ, rfl⟩
    rw [Set.mem_singleton_iff]
    have : μ = stationaryChain P hP hpos := by
      have := invariantG_subset_G hμ
      rwa [gibbsMeasure_eq_singleton P hP hpos, Set.mem_singleton_iff] at this
    rw [this]
  · rw [Set.singleton_subset_iff]
    exact ⟨_, stationaryChain_mem_invariantG P hP hpos, rfl⟩

end MeasureTheory.GibbsMeasure.Markov

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Nearest-neighbour pair potentials on a graph

The nearest-neighbour pair potential (Georgii (2.16)/(2.17), with the coefficients of formula
(3.13)) of a graph `G` with coupling `J`, external field `h` and
spin observable `σ : E → ℝ`: `Φ_{i} = -h·σ(η i)`, `Φ_{i,j} = -J·σ(η i)·σ(η j)` on edges, and `0`
otherwise. For a measurable bounded `σ` and a locally finite graph it is an absolutely summable
potential, so the whole Gibbsian theory of `ℬ` applies (Ising models are the instance
`σ = ±1` over `E = Bool`, see `GibbsMeasure/Model/Ising.lean`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section


namespace Potential

variable {S E : Type*} [MeasurableSpace E]

/-! ### B1: the nearest-neighbour pair potential on a graph -/

open Classical in
/-- The nearest-neighbour pair potential of a graph `G` with coupling `J`, external field `h`
and spin observable `σ`:
`Φ_{i} = -h·σ(η i)`, `Φ_{i,j} = -J·σ(η i)·σ(η j)` on edges `{i, j}` of `G`, and `0` otherwise.
The sum/product over `A` make the definition independent of any enumeration of `A`. -/
noncomputable def nearestNeighbourPair (G : SimpleGraph S) (J h : ℝ) (σ : E → ℝ) :
    Potential S E := fun A η ↦
  if A.card = 1 then -h * ∑ i ∈ A, σ (η i)
  else if A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j then -J * ∏ i ∈ A, σ (η i)
  else 0

lemma nearestNeighbourPair_apply_card_one {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h1 : A.card = 1) (η : S → E) :
    nearestNeighbourPair G J h σ A η = -h * ∑ i ∈ A, σ (η i) := by
  simp only [nearestNeighbourPair, ite_eq_left h1]

lemma nearestNeighbourPair_apply_pair {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j) (η : S → E) :
    nearestNeighbourPair G J h σ A η = -J * ∏ i ∈ A, σ (η i) := by
  have h1 : ¬ A.card = 1 := by omega
  simp only [nearestNeighbourPair, ite_eq_right h1, ite_eq_left h2]

lemma nearestNeighbourPair_apply_eq_zero {G : SimpleGraph S} {J h : ℝ} {σ : E → ℝ}
    {A : Finset S} (h1 : ¬ A.card = 1)
    (h2 : ¬ (A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j)) (η : S → E) :
    nearestNeighbourPair G J h σ A η = 0 := by
  simp only [nearestNeighbourPair, ite_eq_right h1, ite_eq_right h2]

/-- Nearest-neighbour potentials have no `∅`-interaction (Georgii indexes potentials by nonempty
sets). -/
@[simp] lemma nearestNeighbourPair_empty (G : SimpleGraph S) (J h : ℝ) (σ : E → ℝ) :
    nearestNeighbourPair G J h σ ∅ = 0 :=
  funext fun η ↦ nearestNeighbourPair_apply_eq_zero (by simp) (by simp) η

/-! ### B2: measurability (`IsPotential`) -/

lemma isPotential_nearestNeighbourPair (G : SimpleGraph S) (J h : ℝ) {σ : E → ℝ}
    (hσ : Measurable σ) : IsPotential (nearestNeighbourPair G J h σ) := by
  constructor
  intro Δ
  by_cases h1 : Δ.card = 1
  · have hval : nearestNeighbourPair G J h σ Δ = fun η ↦ -h * ∑ i ∈ Δ, σ (η i) :=
      funext fun η ↦ nearestNeighbourPair_apply_card_one h1 η
    rw [hval]
    exact (Finset.measurable_sum Δ fun i hi ↦
      hσ.comp (measurable_cylinderEvent_apply (Finset.mem_coe.2 hi))).const_mul (-h)
  · by_cases h2 : Δ.card = 2 ∧ ∃ i ∈ Δ, ∃ j ∈ Δ, G.Adj i j
    · have hval : nearestNeighbourPair G J h σ Δ = fun η ↦ -J * ∏ i ∈ Δ, σ (η i) :=
        funext fun η ↦ nearestNeighbourPair_apply_pair h2 η
      rw [hval]
      exact (Finset.measurable_prod Δ fun i hi ↦
        hσ.comp (measurable_cylinderEvent_apply (Finset.mem_coe.2 hi))).const_mul (-J)
    · have hval : nearestNeighbourPair G J h σ Δ = fun _ ↦ 0 :=
        funext fun η ↦ nearestNeighbourPair_apply_eq_zero h1 h2 η
      rw [hval]
      exact measurable_const

/-! ### B3: finite range (`IsFiniteRange`) -/

/-- On a locally finite graph, a nonzero interaction support containing `i` is either `{i}`
or an edge at `i`; in both cases it lies in `insert i (G.neighborFinset i)`. -/
lemma subset_of_nearestNeighbourPair_ne_zero [DecidableEq S] (G : SimpleGraph S)
    [G.LocallyFinite] {J h : ℝ} {σ : E → ℝ} {i : S} {A : Finset S}
    (hiA : i ∈ A) (hΦ : nearestNeighbourPair G J h σ A ≠ 0) :
    A ⊆ insert i (G.neighborFinset i) := by
  by_cases h1 : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
    rw [Finset.mem_singleton] at hiA
    subst hiA
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_insert_self _ _
  · by_cases h2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
    · obtain ⟨hcard, a, haA, b, hbA, hab⟩ := h2
      have hAab : ({a, b} : Finset S) = A := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact haA
          · rw [Finset.mem_singleton] at hx
            subst hx
            exact hbA
        · exact le_of_eq (by rw [hcard, Finset.card_pair hab.ne])
      intro x hx
      rw [← hAab] at hx hiA
      rcases Finset.mem_insert.1 hiA with rfl | hi'
      · -- `i = a`
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact Finset.mem_insert_of_mem (by simpa using hab)
      · -- `i = b`
        rw [Finset.mem_singleton] at hi'
        subst hi'
        rcases Finset.mem_insert.1 hx with rfl | hx'
        · exact Finset.mem_insert_of_mem (by simpa using hab.symm)
        · rw [Finset.mem_singleton] at hx'
          subst hx'
          exact Finset.mem_insert_self _ _
    · exact absurd (funext fun η ↦ by
        simpa using nearestNeighbourPair_apply_eq_zero (G := G) (J := J) (h := h) (σ := σ)
          h1 h2 η) hΦ

lemma isFiniteRange_nearestNeighbourPair (G : SimpleGraph S) [G.LocallyFinite]
    (J h : ℝ) (σ : E → ℝ) : IsFiniteRange (nearestNeighbourPair G J h σ) := by
  classical
  exact ⟨fun i ↦ ⟨insert i (G.neighborFinset i),
    fun A hiA hΦ ↦ subset_of_nearestNeighbourPair_ne_zero G hiA hΦ⟩⟩

/-! ### B4: absolute summability (`IsAbsolutelySummable`) from a bounded spin observable -/

/-- A uniform bound on all interaction terms of the pair potential, from a bound on the spin
observable. The `|c|`s make the bound valid without a nonnegativity hypothesis on `c`. -/
lemma abs_nearestNeighbourPair_apply_le (G : SimpleGraph S) (J h : ℝ) {σ : E → ℝ} {c : ℝ}
    (hb : ∀ x, |σ x| ≤ c) (A : Finset S) (η : S → E) :
    |nearestNeighbourPair G J h σ A η| ≤ |h| * |c| + |J| * (c * c) := by
  have hcc : 0 ≤ c * c := mul_self_nonneg c
  by_cases h1 : A.card = 1
  · rw [nearestNeighbourPair_apply_card_one h1, abs_mul, abs_neg]
    have hsum : |∑ i ∈ A, σ (η i)| ≤ |c| := by
      calc |∑ i ∈ A, σ (η i)| ≤ ∑ i ∈ A, |σ (η i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ A, |c| := Finset.sum_le_sum fun i _ ↦ (hb (η i)).trans (le_abs_self c)
        _ = |c| := by rw [Finset.sum_const, h1, one_smul]
    calc |h| * |∑ i ∈ A, σ (η i)| ≤ |h| * |c| :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg h)
      _ ≤ |h| * |c| + |J| * (c * c) :=
          le_add_of_nonneg_right (mul_nonneg (abs_nonneg J) hcc)
  · by_cases h2 : A.card = 2 ∧ ∃ i ∈ A, ∃ j ∈ A, G.Adj i j
    · rw [nearestNeighbourPair_apply_pair h2, abs_mul, abs_neg]
      have hprod : |∏ i ∈ A, σ (η i)| ≤ c * c := by
        calc |∏ i ∈ A, σ (η i)| = ∏ i ∈ A, |σ (η i)| := Finset.abs_prod _ _
          _ ≤ ∏ _i ∈ A, |c| := Finset.prod_le_prod (fun i _ ↦ abs_nonneg _)
              (fun i _ ↦ (hb (η i)).trans (le_abs_self c))
          _ = |c| ^ A.card := Finset.prod_const _
          _ = |c| * |c| := by rw [h2.1, pow_two]
          _ = c * c := abs_mul_abs_self c
      calc |J| * |∏ i ∈ A, σ (η i)| ≤ |J| * (c * c) :=
            mul_le_mul_of_nonneg_left hprod (abs_nonneg J)
        _ ≤ |h| * |c| + |J| * (c * c) :=
            le_add_of_nonneg_left (mul_nonneg (abs_nonneg h) (abs_nonneg c))
    · rw [nearestNeighbourPair_apply_eq_zero h1 h2, abs_zero]
      exact add_nonneg (mul_nonneg (abs_nonneg h) (abs_nonneg c))
        (mul_nonneg (abs_nonneg J) hcc)

lemma isAbsolutelySummable_nearestNeighbourPair (G : SimpleGraph S) [G.LocallyFinite]
    (J h : ℝ) {σ : E → ℝ} {c : ℝ} (hb : ∀ x, |σ x| ≤ c) :
    IsAbsolutelySummable (nearestNeighbourPair G J h σ) := by
  classical
  refine ⟨fun i ↦ ?_⟩
  -- Only supports inside `insert i (G.neighborFinset i)` contribute.
  have hsupp : ∀ A : Finset S, A ∉ (insert i (G.neighborFinset i)).powerset →
      ({A : Finset S | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A = 0 := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
      have hΦ0 : nearestNeighbourPair G J h σ A = 0 := by
        by_contra hΦ
        exact hA (subset_of_nearestNeighbourPair_ne_zero G hiA hΦ)
      refine le_antisymm (iSup_le fun η ↦ ?_) zero_le
      simp [hΦ0]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA) _
  have htsum : (nearestNeighbourPair G J h σ).normAt i =
      ∑ A ∈ (insert i (G.neighborFinset i)).powerset,
        ({A : Finset S | i ∈ A}.indicator
          (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A :=
    tsum_eq_sum hsupp
  rw [htsum]
  refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
  calc ({A : Finset S | i ∈ A}.indicator
        (fun A ↦ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ)) A
      ≤ ⨆ η, ‖nearestNeighbourPair G J h σ A η‖ₑ := Set.indicator_le_self _ _ A
    _ ≤ ENNReal.ofReal (|h| * |c| + |J| * (c * c)) := iSup_le fun η ↦ by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (abs_nearestNeighbourPair_apply_le G J h hb A η)
    _ < ⊤ := ENNReal.ofReal_lt_top

end Potential
end

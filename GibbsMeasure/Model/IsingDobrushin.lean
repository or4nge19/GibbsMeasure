/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.Ising
public import GibbsMeasure.Specification.Dobrushin

/-!
# Dobrushin's condition for the `ℤ^d` Ising model

Georgii's Proposition (8.8) and its `tanh` sharpening, Example (8.9)(2)/(8.10), applied to the
nearest-neighbour Ising potential.

## Main results

* `MeasureTheory.GibbsMeasure.Dobrushin.isDobrushin_isingSpecification`: `4d|βJ| < 2` implies
  Dobrushin's condition.
* `MeasureTheory.GibbsMeasure.Dobrushin.isDobrushin_isingSpecification_tanh`: the sharper
  `2d tanh|βJ| < 1`, Georgii's (8.10) at nearest neighbours.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Dobrushin


section Ising

variable {S : Type*} [DecidableEq S]

omit [DecidableEq S] in
/-- On an edge, the Ising interaction term has modulus at most `|J|`. -/
lemma abs_isingPotential_pair_le (G : SimpleGraph S) (J h : ℝ) {A : Finset S}
    (h2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b) (η : S → Bool) :
    |isingPotential G J h A η| ≤ |J| := by
  rw [isingPotential, Potential.nearestNeighbourPair_apply_pair h2, abs_mul, abs_neg]
  have hprod : |∏ k ∈ A, spin (η k)| ≤ 1 := by
    rw [Finset.abs_prod]
    calc ∏ k ∈ A, |spin (η k)| ≤ ∏ _k ∈ A, (1:ℝ) :=
          Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun k _ ↦ abs_spin_le (η k))
      _ = 1 := by simp
  exact mul_le_of_le_one_right (abs_nonneg J) hprod

omit [DecidableEq S] in
/-- Georgii's `δ(Φ_A) = 2|J|` for an Ising bond, as an upper bound. -/
lemma osc_isingPotential_le (G : SimpleGraph S) (J h : ℝ) {A : Finset S}
    (h2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b) :
    osc (isingPotential G J h A) ≤ ENNReal.ofReal (2 * |J|) := by
  refine osc_le fun ζ η ↦ ENNReal.ofReal_le_ofReal ?_
  obtain ⟨hζ1, hζ2⟩ := abs_le.1 (abs_isingPotential_pair_le G J h h2 ζ)
  obtain ⟨hη1, hη2⟩ := abs_le.1 (abs_isingPotential_pair_le G J h h2 η)
  rw [abs_le]
  constructor <;> linarith

/-- An interaction support of the Ising potential with a nonzero term and two sites is an
edge `{i, j}` at `i`. -/
lemma isingPotential_support (G : SimpleGraph S) {A : Finset S} {i : S}
    (hiA : i ∈ A) (h2 : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b) :
    ∃ j, G.Adj i j ∧ A = {i, j} := by
  obtain ⟨hcard, a, haA, b, hbA, hab⟩ := h2
  have herase : (A.erase i).card = 1 := by rw [Finset.card_erase_of_mem hiA, hcard]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 herase
  have hAeq : A = {i, j} := by
    rw [← Finset.insert_erase hiA, hj]
  have hmem : ∀ x ∈ A, x = i ∨ x = j := by
    intro x hx
    rw [hAeq] at hx
    simpa using hx
  refine ⟨j, ?_, hAeq⟩
  rcases hmem a haA with ha | ha <;> rcases hmem b hbA with hb | hb
  · exact absurd (ha.trans hb.symm) hab.ne
  · rw [← ha, ← hb]; exact hab
  · rw [← hb, ← ha]; exact hab.symm
  · exact absurd (ha.trans hb.symm) hab.ne

omit [DecidableEq S] in
/-- **Georgii (8.8) for the Ising model.** `∑_{A ∋ i} (|A| − 1) δ(Φ_A) ≤ deg(i) · 2|J|`. -/
lemma interactionStrength_isingPotential_le (G : SimpleGraph S) [G.LocallyFinite] (J h : ℝ)
    (i : S) :
    interactionStrength (isingPotential G J h) i
      ≤ ((G.neighborFinset i).card : ℝ≥0∞) * ENNReal.ofReal (2 * |J|) := by
  classical
  set T : Finset (Finset S) := (G.neighborFinset i).image (fun j ↦ ({i, j} : Finset S)) with hT
  set f : Finset S → ℝ≥0∞ := fun A ↦ {A : Finset S | i ∈ A}.indicator
    (fun A ↦ ((A.card - 1 : ℕ) : ℝ≥0∞) * osc (isingPotential G J h A)) A with hf
  have hzero : ∀ A : Finset S, A ∉ T → f A = 0 := by
    intro A hA
    simp only [hf]
    by_cases hiA : i ∈ A
    swap
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA) _
    rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
    by_cases hcard : A.card = 1
    · rw [hcard]; simp
    by_cases hedge : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
    · obtain ⟨j, hij, rfl⟩ := isingPotential_support G hiA hedge
      exact absurd (Finset.mem_image.2 ⟨j, (SimpleGraph.mem_neighborFinset G i j).2 hij, rfl⟩) hA
    · have hΦ0 : isingPotential G J h A = 0 :=
        funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero hcard hedge η
      have hosc0 : osc (0 : (S → Bool) → ℝ) = 0 := by
        refine le_antisymm (osc_le fun _ _ ↦ ?_) bot_le
        simp
      rw [hΦ0, hosc0, mul_zero]
  have hterm : ∀ A ∈ T, f A ≤ ENNReal.ofReal (2 * |J|) := by
    intro A hA
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hA
    have hij : G.Adj i j := (SimpleGraph.mem_neighborFinset G i j).1 hj
    have hcard : ({i, j} : Finset S).card = 2 := Finset.card_pair hij.ne
    have hedge : ({i, j} : Finset S).card = 2 ∧
        ∃ a ∈ ({i, j} : Finset S), ∃ b ∈ ({i, j} : Finset S), G.Adj a b :=
      ⟨hcard, i, by simp, j, by simp, hij⟩
    simp only [hf]
    rw [Set.indicator_of_mem (show ({i, j} : Finset S) ∈ {A : Finset S | i ∈ A} by simp), hcard]
    simpa using osc_isingPotential_le G J h hedge
  rw [interactionStrength, ← hf, tsum_eq_sum hzero]
  calc ∑ A ∈ T, f A ≤ T.card • ENNReal.ofReal (2 * |J|) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = (T.card : ℝ≥0∞) * ENNReal.ofReal (2 * |J|) := by rw [nsmul_eq_mul]
    _ ≤ ((G.neighborFinset i).card : ℝ≥0∞) * ENNReal.ofReal (2 * |J|) := by
        gcongr
        exact_mod_cast Finset.card_image_le

omit [DecidableEq S] in
/-- For the Ising potential the only interaction term containing two distinct sites is the bond
`{i, j}`, so `∑_{A ⊇ {i,j}} δ(Φ_A) ≤ 2|J|` on an edge. -/
lemma pairStrength_isingPotential_le (G : SimpleGraph S) (J h : ℝ) {i j : S} (hij : G.Adj i j) :
    pairStrength (isingPotential G J h) i j ≤ ENNReal.ofReal (2 * |J|) := by
  classical
  set f : Finset S → ℝ≥0∞ := fun A ↦ {A : Finset S | i ∈ A ∧ j ∈ A}.indicator
    (fun A ↦ osc (isingPotential G J h A)) A with hf
  have hzero : ∀ A : Finset S, A ∉ ({({i, j} : Finset S)} : Finset (Finset S)) → f A = 0 := by
    intro A hA
    simp only [hf]
    by_cases hmem : i ∈ A ∧ j ∈ A
    swap
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A ∧ j ∈ A} from hmem) _
    rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A ∧ j ∈ A} from hmem)]
    by_cases hcard : A.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hcard
      simp only [Finset.mem_singleton] at hmem
      exact absurd (hmem.1.trans hmem.2.symm) hij.ne
    by_cases hedge : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
    · obtain ⟨k, hik, hAeq⟩ := isingPotential_support G hmem.1 hedge
      have hkj : k = j := by
        have : j ∈ ({i, k} : Finset S) := hAeq ▸ hmem.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · exact absurd h.symm hij.ne
        · exact h.symm
      exact absurd (by simp [hAeq, hkj]) hA
    · have hΦ0 : isingPotential G J h A = 0 :=
        funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero hcard hedge η
      have hosc0 : osc (0 : (S → Bool) → ℝ) = 0 := by
        refine le_antisymm (osc_le fun _ _ ↦ ?_) bot_le
        simp
      rw [hΦ0, hosc0]
  have hcard2 : ({i, j} : Finset S).card = 2 := Finset.card_pair hij.ne
  have hedge2 : ({i, j} : Finset S).card = 2 ∧
      ∃ a ∈ ({i, j} : Finset S), ∃ b ∈ ({i, j} : Finset S), G.Adj a b :=
    ⟨hcard2, i, by simp, j, by simp, hij⟩
  rw [pairStrength, ← hf, tsum_eq_sum hzero, Finset.sum_singleton]
  simp only [hf]
  rw [Set.indicator_of_mem (show ({i, j} : Finset S) ∈ {A : Finset S | i ∈ A ∧ j ∈ A} by simp)]
  simpa using osc_isingPotential_le G J h hedge2

omit [DecidableEq S] in
/-- Off the edges of `G` two distinct sites share no interaction term. -/
lemma pairStrength_isingPotential_eq_zero (G : SimpleGraph S) (J h : ℝ) {i j : S}
    (hne : i ≠ j) (hij : ¬ G.Adj i j) :
    pairStrength (isingPotential G J h) i j = 0 := by
  classical
  refine ENNReal.tsum_eq_zero.2 fun A ↦ ?_
  by_cases hmem : i ∈ A ∧ j ∈ A
  swap
  · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A ∧ j ∈ A} from hmem) _
  rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A ∧ j ∈ A} from hmem)]
  by_cases hcard : A.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hcard
    simp only [Finset.mem_singleton] at hmem
    exact absurd (hmem.1.trans hmem.2.symm) hne
  by_cases hedge : A.card = 2 ∧ ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
  · obtain ⟨k, hik, hAeq⟩ := isingPotential_support G hmem.1 hedge
    have hkj : k = j := by
      have : j ∈ ({i, k} : Finset S) := hAeq ▸ hmem.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact absurd h.symm hne
      · exact h.symm
    exact absurd (hkj ▸ hik) hij
  · have hΦ0 : isingPotential G J h A = 0 :=
      funext fun η ↦ Potential.nearestNeighbourPair_apply_eq_zero hcard hedge η
    rw [hΦ0]
    refine le_antisymm (osc_le fun _ _ ↦ ?_) bot_le
    simp

/-- Each site of `ℤ^d` has at most `2d` nearest neighbours. -/
lemma card_neighborFinset_latticeGraph_le (d : ℕ) (v : Fin d → ℤ) :
    ((latticeGraph d).neighborFinset v).card ≤ 2 * d := by
  classical
  set g : Fin d × Bool → (Fin d → ℤ) :=
    fun p ↦ Function.update v p.1 (v p.1 + if p.2 then (1:ℤ) else -1) with hg
  have hsub : (latticeGraph d).neighborFinset v ⊆ Finset.image g Finset.univ := by
    intro y hy
    have hadj : (latticeGraph d).Adj v y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
    obtain ⟨j, t, ht, rfl⟩ := latticeGraph_adj_decomp hadj
    rcases ht with rfl | rfl
    · exact Finset.mem_image.2 ⟨(j, true), Finset.mem_univ _, by simp [hg]⟩
    · exact Finset.mem_image.2 ⟨(j, false), Finset.mem_univ _, by simp [hg]⟩
  calc ((latticeGraph d).neighborFinset v).card ≤ (Finset.image g Finset.univ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ, mul_comm]

/-- **Dobrushin's condition for the `ℤ^d` Ising model at high temperature**: Georgii's
Proposition (8.8) applied to the nearest-neighbour spin potential of Example (8.9)(2), using
only that example's computation `δ(Φ_A) = 2|J(A)|`. Each of the `2d` bonds at a site
contributes `(|A| − 1) δ(Φ_A) = 2|βJ|`, so `∑_{A ∋ i} (|A| − 1) δ((βΦ)_A) ≤ 4d|βJ| < 2`. The
sharper criterion (8.10) of Example (8.9)(2), here `2d tanh |βJ| < 1`, is
`isDobrushin_isingSpecification_tanh`. -/
theorem isDobrushin_isingSpecification (d : ℕ) (J h β : ℝ) (hβ : 4 * d * |β * J| < 2) :
    IsDobrushin (isingSpecification (latticeGraph d) J h β) := by
  classical
  have hb : (0:ℝ) ≤ |β| := abs_nonneg β
  rw [isingSpecification]
  refine isDobrushin_gibbsSpecification (Φ := isingPotential (latticeGraph d) J h)
    uniformSpinMeasure β (c := ENNReal.ofReal (4 * d * |β * J|)) ?_ ?_
  · rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    exact hβ
  · intro i
    have h2 : (((latticeGraph d).neighborFinset i).card : ℝ≥0∞) ≤ ((2 * d : ℕ) : ℝ≥0∞) := by
      exact_mod_cast card_neighborFinset_latticeGraph_le d i
    calc ENNReal.ofReal |β| * interactionStrength (isingPotential (latticeGraph d) J h) i
        ≤ ENNReal.ofReal |β| *
            ((((latticeGraph d).neighborFinset i).card : ℝ≥0∞)
              * ENNReal.ofReal (2 * |J|)) := by
          gcongr
          exact interactionStrength_isingPotential_le (latticeGraph d) J h i
      _ ≤ ENNReal.ofReal |β| * (((2 * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * |J|)) := by gcongr
      _ = ENNReal.ofReal (4 * d * |β * J|) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hb]
          congr 1
          push_cast
          rw [abs_mul]
          ring

/-- **Georgii, Example (8.9)(2) for the `ℤ^d` Ising model.** Dobrushin's condition holds as soon
as `2d · tanh|βJ| < 1`. This is Georgii's (8.10) specialised to nearest neighbours, and since
`tanh x < x` for `x > 0` it is strictly weaker than the hypothesis `4d|βJ| < 2` of
`isDobrushin_isingSpecification`: at `d = 2, J = 1` it gives uniqueness for
`β < artanh (1/4) ≈ 0.2554` rather than `β < 1/4`. -/
theorem isDobrushin_isingSpecification_tanh (d : ℕ) (J h β : ℝ)
    (hβ : 2 * d * Real.tanh |β * J| < 1) :
    IsDobrushin (isingSpecification (latticeGraph d) J h β) := by
  classical
  set G := latticeGraph d with hG
  set t : ℝ := Real.tanh |β * J| with ht
  have ht0 : 0 ≤ t := Real.tanh_nonneg (abs_nonneg _)
  rw [isingSpecification]
  refine isDobrushin_gibbsSpecification_of_tanh (Φ := isingPotential G J h)
    uniformSpinMeasure β (c := ENNReal.ofReal (2 * d * t))
    (by rwa [show (1:ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
      ENNReal.ofReal_lt_ofReal_iff (by norm_num)]) (fun i ↦ ?_)
  -- only the neighbours of `i` contribute
  set f : (Fin d → ℤ) → ℝ≥0∞ := fun j ↦ {j : Fin d → ℤ | j ≠ i}.indicator
    (fun j ↦ ENNReal.ofReal
      (Real.tanh (|β| * (pairStrength (isingPotential G J h) i j).toReal / 2))) j with hf
  have hzero : ∀ j : Fin d → ℤ, j ∉ G.neighborFinset i → f j = 0 := by
    intro j hj
    simp only [hf]
    by_cases hji : j = i
    · exact Set.indicator_of_notMem (show j ∉ {k : Fin d → ℤ | k ≠ i} by simp [hji]) _
    rw [Set.indicator_of_mem (show j ∈ {j : Fin d → ℤ | j ≠ i} from hji)]
    have hadj : ¬ G.Adj i j := fun hadj ↦ hj ((SimpleGraph.mem_neighborFinset G i j).2 hadj)
    rw [pairStrength_isingPotential_eq_zero G J h (Ne.symm hji) hadj]
    simp
  have hterm : ∀ j ∈ G.neighborFinset i, f j ≤ ENNReal.ofReal t := by
    intro j hj
    have hadj : G.Adj i j := (SimpleGraph.mem_neighborFinset G i j).1 hj
    simp only [hf]
    by_cases hji : j = i
    · rw [Set.indicator_of_notMem (show j ∉ {k : Fin d → ℤ | k ≠ i} by simp [hji])]
      exact zero_le
    rw [Set.indicator_of_mem (show j ∈ {j : Fin d → ℤ | j ≠ i} from hji)]
    refine ENNReal.ofReal_le_ofReal (Real.tanh_le_tanh_of_le ?_)
    have hP := pairStrength_isingPotential_le G J h hadj
    have hPreal : (pairStrength (isingPotential G J h) i j).toReal ≤ 2 * |J| :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hP
    calc |β| * (pairStrength (isingPotential G J h) i j).toReal / 2
        ≤ |β| * (2 * |J|) / 2 := by
          have : (0:ℝ) ≤ |β| := abs_nonneg β
          nlinarith [ENNReal.toReal_nonneg (a := pairStrength (isingPotential G J h) i j)]
      _ = |β * J| := by rw [abs_mul]; ring
  calc ∑' j : Fin d → ℤ, f j = ∑ j ∈ G.neighborFinset i, f j := tsum_eq_sum hzero
    _ ≤ (G.neighborFinset i).card • ENNReal.ofReal t :=
        Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ((G.neighborFinset i).card : ℝ≥0∞) * ENNReal.ofReal t := by rw [nsmul_eq_mul]
    _ ≤ (((2 * d : ℕ)) : ℝ≥0∞) * ENNReal.ofReal t := by
        gcongr
        exact_mod_cast card_neighborFinset_latticeGraph_le d i
    _ = ENNReal.ofReal (2 * d * t) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        ring

end Ising

end MeasureTheory.GibbsMeasure.Dobrushin

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# A set of uniformly positive scalar products

A measure on `ι → ℝ` (`ι` finite) which charges the complement of the origin charges a set on
which the scalar product is bounded away from zero: there are a measurable `U` with `μ U ≠ 0`
and a `u > 0` with `u ≤ x ⬝ᵥ y` for all `x, y ∈ U`.

The proof covers `{0}ᶜ` by the countably many closed boxes `B(q, ρ)` with rational centre and
radius whose radius is small compared to their distance from the origin.  On such a box

`x ⬝ᵥ y ≥ ∑_c q_c² - 2ρ ∑_c |q_c| - card ι · ρ²`,

which is positive by the choice of boxes; one of the boxes must be charged.

## Main results

* `MeasureTheory.exists_forall_le_dotProduct_of_measure_ne_zero`
* `Measurable.dotProduct`
-/

@[expose] public section

open Matrix Set

namespace MeasureTheory

variable {ι : Type*}

/-- The scalar product of two measurable `ι → ℝ`-valued functions is measurable. -/
lemma _root_.Measurable.dotProduct [Fintype ι] {α : Type*} [MeasurableSpace α]
    {f g : α → (ι → ℝ)}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a ↦ f a ⬝ᵥ g a :=
  Finset.measurable_sum _ fun c _ ↦
    ((measurable_pi_apply c).comp hf).mul ((measurable_pi_apply c).comp hg)

namespace PositiveDotProduct

/-- The closed sup-norm box of radius `ρ` around the rational point `q`. -/
def ratBox (q : ι → ℚ) (ρ : ℚ) : Set (ι → ℝ) :=
  {x | ∀ c, |x c - (q c : ℝ)| ≤ (ρ : ℝ)}

lemma measurableSet_ratBox [Countable ι] (q : ι → ℚ) (ρ : ℚ) : MeasurableSet (ratBox q ρ) := by
  have h : ratBox q ρ
      = ⋂ c, (fun x : ι → ℝ ↦ x c) ⁻¹' Set.Icc ((q c : ℝ) - ρ) ((q c : ℝ) + ρ) := by
    ext x
    simp only [ratBox, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc,
      abs_le]
    exact forall_congr' fun c ↦ by constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [h]
  exact MeasurableSet.iInter fun c ↦ (measurable_pi_apply c) measurableSet_Icc

/-- The lower bound for the scalar product on the box `B(q, ρ)`. -/
def boxBound [Fintype ι] (q : ι → ℚ) (ρ : ℚ) : ℝ :=
  (∑ c, ((q c : ℝ)) ^ 2) - 2 * (ρ : ℝ) * (∑ c, |(q c : ℝ)|) - Fintype.card ι * (ρ : ℝ) ^ 2

/-- The scalar product of two points of `B(q, ρ)` is at least `boxBound q ρ`. -/
lemma boxBound_le_dotProduct [Fintype ι] {q : ι → ℚ} {ρ : ℚ} {x y : ι → ℝ}
    (hx : x ∈ ratBox q ρ) (hy : y ∈ ratBox q ρ) : boxBound q ρ ≤ x ⬝ᵥ y := by
  have key : ∀ c, ((q c : ℝ)) ^ 2 - 2 * (ρ : ℝ) * |(q c : ℝ)| - (ρ : ℝ) ^ 2 ≤ x c * y c := by
    intro c
    have hxc : |x c - (q c : ℝ)| ≤ (ρ : ℝ) := hx c
    have hyc : |y c - (q c : ℝ)| ≤ (ρ : ℝ) := hy c
    have hqt : -(|(q c : ℝ)| * (ρ : ℝ)) ≤ (q c : ℝ) * (y c - (q c : ℝ)) :=
      neg_le_of_abs_le (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left hyc (abs_nonneg _))
    have hsq : -(|(q c : ℝ)| * (ρ : ℝ)) ≤ (x c - (q c : ℝ)) * (q c : ℝ) :=
      neg_le_of_abs_le (by
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_left hxc (abs_nonneg _))
    have hst : -((ρ : ℝ) ^ 2) ≤ (x c - (q c : ℝ)) * (y c - (q c : ℝ)) :=
      neg_le_of_abs_le (by
        rw [abs_mul, sq]
        exact mul_le_mul hxc hyc (abs_nonneg _) (abs_nonneg _ |>.trans hxc))
    nlinarith [hqt, hsq, hst]
  have hsum : ∑ c, (((q c : ℝ)) ^ 2 - 2 * (ρ : ℝ) * |(q c : ℝ)| - (ρ : ℝ) ^ 2)
      = boxBound q ρ := by
    rw [boxBound, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc boxBound q ρ = ∑ c, (((q c : ℝ)) ^ 2 - 2 * (ρ : ℝ) * |(q c : ℝ)| - (ρ : ℝ) ^ 2) :=
        hsum.symm
    _ ≤ ∑ c, x c * y c := Finset.sum_le_sum fun c _ ↦ key c
    _ = x ⬝ᵥ y := rfl

/-- Every point other than the origin lies in a box on which the scalar product is positive. -/
lemma exists_mem_ratBox_boxBound_pos [Fintype ι] {x : ι → ℝ} (hx : x ≠ 0) :
    ∃ (q : ι → ℚ) (ρ : ℚ), 0 < boxBound q ρ ∧ x ∈ ratBox q ρ := by
  set S : ℝ := ∑ c, (x c) ^ 2 with hS
  set L : ℝ := ∑ c, |x c| with hL
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun c _ ↦ abs_nonneg _
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hSpos : 0 < S := by
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hx
    have hc' : x c ≠ 0 := hc
    exact Finset.sum_pos' (fun c _ ↦ sq_nonneg _) ⟨c, Finset.mem_univ c, by positivity⟩
  set K : ℝ := 6 * L + 8 * Fintype.card ι + 1 with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨δ, hδ0, hδlt⟩ : ∃ δ : ℚ, (0 : ℝ) < δ ∧ (δ : ℝ) < min 1 (S / K) :=
    exists_rat_btwn (lt_min zero_lt_one (div_pos hSpos hKpos))
  have hδ1 : (δ : ℝ) ≤ 1 := (lt_min_iff.1 hδlt).1.le
  have hδK : K * (δ : ℝ) < S := by
    have := (lt_min_iff.1 hδlt).2
    calc K * (δ : ℝ) < K * (S / K) := by nlinarith
      _ = S := by field_simp
  have hδmain : 6 * L * (δ : ℝ) + 8 * Fintype.card ι * (δ : ℝ) ^ 2 < S := by
    have hsq : (δ : ℝ) ^ 2 ≤ (δ : ℝ) := by nlinarith
    nlinarith
  have hq : ∀ c : ι, ∃ r : ℚ, |x c - (r : ℝ)| < (δ : ℝ) := fun c ↦ exists_rat_near _ hδ0
  choose q hqx using hq
  refine ⟨q, 2 * δ, ?_, fun c ↦ ?_⟩
  · -- the two elementary estimates
    have hq2 : S - 2 * L * (δ : ℝ) ≤ ∑ c, ((q c : ℝ)) ^ 2 := by
      have hpt : ∀ c, (x c) ^ 2 - 2 * |x c| * (δ : ℝ) ≤ ((q c : ℝ)) ^ 2 := fun c ↦ by
        have h1 : x c * (x c - (q c : ℝ)) ≤ |x c| * (δ : ℝ) :=
          calc x c * (x c - (q c : ℝ)) ≤ |x c * (x c - (q c : ℝ))| := le_abs_self _
            _ = |x c| * |x c - (q c : ℝ)| := abs_mul _ _
            _ ≤ |x c| * (δ : ℝ) := mul_le_mul_of_nonneg_left (hqx c).le (abs_nonneg _)
        nlinarith [h1, sq_nonneg (x c - (q c : ℝ))]
      have hexp : ∑ c, ((x c) ^ 2 - 2 * |x c| * (δ : ℝ))
          = (∑ c, (x c) ^ 2) - 2 * (∑ c, |x c|) * (δ : ℝ) := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum, Finset.sum_mul]
      calc S - 2 * L * (δ : ℝ) = ∑ c, ((x c) ^ 2 - 2 * |x c| * (δ : ℝ)) := hexp.symm
        _ ≤ ∑ c, ((q c : ℝ)) ^ 2 := Finset.sum_le_sum fun c _ ↦ hpt c
    have hq1 : ∑ c, |(q c : ℝ)| ≤ L + Fintype.card ι * (δ : ℝ) := by
      have hpt : ∀ c, |(q c : ℝ)| ≤ |x c| + (δ : ℝ) := fun c ↦ by
        have h := abs_le.1 (hqx c).le
        exact abs_le.2 ⟨by linarith [neg_abs_le (x c), h.2], by linarith [le_abs_self (x c), h.1]⟩
      calc ∑ c, |(q c : ℝ)| ≤ ∑ c, (|x c| + (δ : ℝ)) := Finset.sum_le_sum fun c _ ↦ hpt c
        _ = L + Fintype.card ι * (δ : ℝ) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hρ : ((2 * δ : ℚ) : ℝ) = 2 * (δ : ℝ) := by push_cast; ring
    rw [boxBound, hρ]
    nlinarith [hq2, hq1, hδ0.le, hLnn, hcard]
  · have hρ : ((2 * δ : ℚ) : ℝ) = 2 * (δ : ℝ) := by push_cast; ring
    rw [hρ]
    linarith [(hqx c).le, hδ0.le]

end PositiveDotProduct

open PositiveDotProduct in
/-- **A measure charging `{0}ᶜ` charges a set of uniformly positive scalar products.**

If a measure `μ` on `ι → ℝ` (`ι` finite) gives positive mass to the complement of the origin,
then there are a measurable set `U` with `μ U ≠ 0` and a constant `u > 0` such that
`u ≤ x ⬝ᵥ y` for all `x, y ∈ U`.

No invariance, regularity or finiteness assumption on `μ` is needed. -/
theorem exists_forall_le_dotProduct_of_measure_ne_zero [Fintype ι] {μ : Measure (ι → ℝ)}
    (hμ : μ {x : ι → ℝ | x ≠ 0} ≠ 0) :
    ∃ (U : Set (ι → ℝ)) (u : ℝ), MeasurableSet U ∧ μ U ≠ 0 ∧ 0 < u ∧
      ∀ x ∈ U, ∀ y ∈ U, u ≤ x ⬝ᵥ y := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : (ι → ℚ) × ℚ,
      μ (if 0 < boxBound p.1 p.2 then ratBox p.1 p.2 else ∅) ≠ 0 := by
    by_contra hcon
    have hall : ∀ p : (ι → ℚ) × ℚ,
        μ (if 0 < boxBound p.1 p.2 then ratBox p.1 p.2 else ∅) = 0 :=
      fun p ↦ not_not.1 fun h ↦ hcon ⟨p, h⟩
    refine hμ (measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null hall))
    obtain ⟨q, ρ, hpos, hmem⟩ := exists_mem_ratBox_boxBound_pos (x := x) hx
    exact Set.mem_iUnion.2 ⟨⟨q, ρ⟩, by simpa [hpos] using hmem⟩
  have hpos : 0 < boxBound p.1 p.2 := by
    by_contra h
    simp [h] at hp
  exact ⟨ratBox p.1 p.2, boxBound p.1 p.2, measurableSet_ratBox _ _, by simpa [hpos] using hp,
    hpos, fun x hx y hy ↦ boxBound_le_dotProduct hx hy⟩

end MeasureTheory

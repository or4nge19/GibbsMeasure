/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

/-!
# Product sums over a finite power in `ℝ≥0∞`

`∑'_{d : ι → α} ∏_{i} w (d i) = (∑'_x w x)^{|ι|}` for a finite index type: every finite subsum is
dominated by one over a box `Fintype.piFinset`, which factorises by `Finset.prod_univ_sum`.

Only the `≤` direction is proved, which is what a partition-function bound needs; note that no
countability or measurability hypothesis is required, `ℝ≥0∞`-valued sums being unconditional.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- **A product sum over a finite power is dominated by the power of the sum.** -/
theorem tsum_pi_prod_le {ι : Type*} [Fintype ι] {α : Type*} (w : α → ℝ≥0∞) :
    ∑' d : ι → α, ∏ i : ι, w (d i) ≤ (∑' x, w x) ^ Fintype.card ι := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  set t : Finset α := s.biUnion fun d ↦ Finset.image d Finset.univ with ht
  have hsub : s ⊆ Fintype.piFinset fun _ : ι ↦ t := fun d hd ↦
    Fintype.mem_piFinset.2 fun i ↦ Finset.mem_biUnion.2
      ⟨d, hd, Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩⟩
  calc ∑ d ∈ s, ∏ i : ι, w (d i)
      ≤ ∑ d ∈ Fintype.piFinset fun _ : ι ↦ t, ∏ i : ι, w (d i) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∏ _i : ι, ∑ x ∈ t, w x :=
        (Finset.prod_univ_sum (fun _ : ι ↦ t) (fun _ (x : α) ↦ w x)).symm
    _ ≤ ∏ _i : ι, ∑' x, w x := Finset.prod_le_prod' fun i _ ↦ ENNReal.sum_le_tsum t
    _ = (∑' x, w x) ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

end ENNReal

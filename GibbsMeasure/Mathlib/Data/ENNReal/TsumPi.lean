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

`∑'_{d : ∀ i, α i} ∏_{i} w i (d i) ≤ ∏_{i} ∑'_x w i x` for a finite index type
(`tsum_pi_prod_le_prod_tsum`): every finite subsum is dominated by one over a box
`Fintype.piFinset`, which factorises by `Finset.prod_univ_sum`. For one weight `w` on all
factors this is `(∑'_x w x)^{|ι|}` (`tsum_pi_prod_le`).

Only the `≤` direction is proved, which is what a partition-function bound needs; note that no
countability or measurability hypothesis is required, `ℝ≥0∞`-valued sums being unconditional.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- **A sum of products over a finite product is dominated by the product of the sums.** -/
theorem tsum_pi_prod_le_prod_tsum {ι : Type*} [Fintype ι] {α : ι → Type*}
    (w : ∀ i, α i → ℝ≥0∞) : ∑' d : ∀ i, α i, ∏ i, w i (d i) ≤ ∏ i, ∑' x, w i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  set t : ∀ i, Finset (α i) := fun i ↦ s.image fun d ↦ d i with ht
  have hsub : s ⊆ Fintype.piFinset t := fun d hd ↦
    Fintype.mem_piFinset.2 fun i ↦ Finset.mem_image.2 ⟨d, hd, rfl⟩
  calc ∑ d ∈ s, ∏ i, w i (d i)
      ≤ ∑ d ∈ Fintype.piFinset t, ∏ i, w i (d i) := Finset.sum_le_sum_of_subset hsub
    _ = ∏ i, ∑ x ∈ t i, w i x := (Finset.prod_univ_sum t w).symm
    _ ≤ ∏ i, ∑' x, w i x := Finset.prod_le_prod fun i _ ↦ ENNReal.sum_le_tsum (t i)

/-- **A product sum over a finite power is dominated by the power of the sum.** -/
theorem tsum_pi_prod_le {ι : Type*} [Fintype ι] {α : Type*} (w : α → ℝ≥0∞) :
    ∑' d : ι → α, ∏ i : ι, w (d i) ≤ (∑' x, w x) ^ Fintype.card ι :=
  (tsum_pi_prod_le_prod_tsum fun _ ↦ w).trans_eq (by rw [Finset.prod_const, Finset.card_univ])

end ENNReal

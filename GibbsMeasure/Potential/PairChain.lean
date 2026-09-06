/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Pair

/-!
# The Hamiltonian of a nearest-neighbour pair potential on `ℕ`

A pair potential `Φ = pair φ` on the half-line `S = ℕ` is *nearest-neighbour* when
`φ_{ij} = 0` unless `j = i + 1`.  In an initial interval `Λ_N = {0, …, N-1} = Finset.range N`
only the bonds `{i, i+1}` with `i < N` matter — the bond `{N-1, N}` leaving the volume included,
the bond `{N, N+1}` excluded — so the Hamiltonian is the finite sum

`H_{Λ_N}(σ) = ∑_{i < N} φ_{i,i+1}(σ_i, σ_{i+1})`.

This is the identity behind every transfer-matrix computation on a chain (Georgii §6.1, and the
two-layer chain of Example (9.15)).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Potential

variable {E : Type*} [MeasurableSpace E] {φ : ℕ → ℕ → E → E → ℝ}

/-- The bonds meeting the initial interval `Λ_N = {0, …, N-1}` are exactly the `{i, i+1}` with
`i < N`: the boundary bond `{N-1, N}` meets it, the bond `{N, N+1}` does not. -/
lemma not_disjoint_pair_range {i N : ℕ} (hi : i < N) :
    ¬ Disjoint ({i, i + 1} : Finset ℕ) (Finset.range N) :=
  Finset.not_disjoint_iff.2 ⟨i, Finset.mem_insert_self _ _, Finset.mem_range.2 hi⟩

/-- **The Hamiltonian of a nearest-neighbour pair potential on `ℕ` in an initial interval.**
If `φ_{ij}` vanishes unless `j = i + 1`, then
`H_{Λ_N}(σ) = ∑_{i < N} φ_{i,i+1}(σ_i, σ_{i+1})` for `Λ_N = Finset.range N`. -/
theorem hamiltonian_pair_range [IsAbsolutelySummable (pair φ)]
    (hφ : ∀ i j, j ≠ i + 1 → ∀ x y, φ i j x y = 0) (N : ℕ) (σ : ℕ → E) :
    (pair φ).hamiltonian (Finset.range N) σ
      = ∑ i ∈ Finset.range N, φ i (i + 1) (σ i) (σ (i + 1)) := by
  classical
  set g : ℕ → ℕ → ℝ := fun i j ↦
    if ¬ Disjoint ({i, j} : Finset ℕ) (Finset.range N) then φ i j (σ i) (σ j) else 0 with hg
  have hterms : ∀ A : Finset ℕ,
      (pair φ).hamiltonianTerms (Finset.range N) σ A = pairTerms g A :=
    fun A ↦ hamiltonianTerms_pair φ (Finset.range N) σ A
  rw [hamiltonian_eq_tsum, tsum_congr hterms, tsum_pairTerms]
  have hzero : ∀ q : ℕ × ℕ, q ∉ (Finset.range N).image (fun i ↦ (i, i + 1)) →
      (if q.1 < q.2 then g q.1 q.2 else 0) = 0 := by
    rintro ⟨a, b⟩ hq
    simp only
    split_ifs with hab
    · rw [hg]
      simp only
      by_cases hd : Disjoint ({a, b} : Finset ℕ) (Finset.range N)
      · rw [ite_eq_right (not_not.2 hd)]
      · rw [ite_eq_left hd]
        by_cases hb : b = a + 1
        · subst hb
          refine absurd (Finset.mem_image.2 ⟨a, Finset.mem_range.2 ?_, rfl⟩) hq
          obtain ⟨x, hx, hxN⟩ := Finset.not_disjoint_iff.1 hd
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_range] at hxN
          rcases hx with rfl | rfl <;> omega
        · exact hφ a b hb _ _
    · rfl
  rw [tsum_eq_sum hzero, Finset.sum_image (by intro i _ j _ h; simpa using h)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [hg]
  rw [ite_eq_left (Nat.lt_succ_self i),
    ite_eq_left (not_disjoint_pair_range (Finset.mem_range.1 hi))]

end Potential

end

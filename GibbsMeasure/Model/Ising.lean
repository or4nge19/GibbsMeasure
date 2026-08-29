/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Potential.NearestNeighbour

/-!
# The Ising model, and existence of its Gibbs measures

The Ising potential over `Bool` spins on a graph — the nearest-neighbour pair potential of
Georgii (2.16)/(2.17) with the coefficients of formula (3.13): `Φ_{i} = -h σ_i`,
`Φ_{i,j} = -J σ_i σ_j` on edges (wiki: `ising_potential`) — its Gibbsian specification with
uniform a-priori spin measure, and, as instances of Georgii Theorem (4.23)(a), **existence** and
**compactness** of the set of Ising Gibbs measures on any countable locally finite graph, in
particular on the lattice `ℤ^d`.

What is *not* proved here: uniqueness on `ℤ` (Georgii (3.15), from Theorem (3.5) via the transfer matrix)
and non-uniqueness on `ℤ^d`, `d ≥ 2`, at low temperature (Georgii Theorem (6.9), the ± phases);
the compact set below is not known (in this development) to be a simplex — that is the
representation theory of Chapter 7.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### B5: the Ising model over `Bool` spins -/

/-- The `±1` spin observable on `Bool`. -/
def spin : Bool → ℝ := fun b ↦ if b then 1 else -1

lemma measurable_spin : Measurable spin := Measurable.of_discrete

lemma abs_spin_le (b : Bool) : |spin b| ≤ 1 := by cases b <;> simp [spin]

/-- The Ising potential on a graph `G` with coupling `J` and external field `h`. -/
noncomputable def isingPotential {S : Type*} (G : SimpleGraph S) (J h : ℝ) :
    Potential S Bool :=
  Potential.nearestNeighbourPair G J h spin

instance {S : Type*} (G : SimpleGraph S) (J h : ℝ) :
    Potential.IsPotential (isingPotential G J h) :=
  Potential.isPotential_nearestNeighbourPair G J h measurable_spin

instance {S : Type*} (G : SimpleGraph S) [G.LocallyFinite] (J h : ℝ) :
    Potential.IsFiniteRange (isingPotential G J h) :=
  Potential.isFiniteRange_nearestNeighbourPair G J h spin

instance {S : Type*} (G : SimpleGraph S) [G.LocallyFinite] (J h : ℝ) :
    Potential.IsAbsolutelySummable (isingPotential G J h) :=
  Potential.isAbsolutelySummable_nearestNeighbourPair G J h abs_spin_le

/-- The uniform a-priori single-spin measure on `Bool`. -/
noncomputable def uniformSpinMeasure : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance : IsProbabilityMeasure uniformSpinMeasure := by
  refine ⟨?_⟩
  have hcount : Measure.count (Set.univ : Set Bool) = 2 := by
    rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
    norm_num
  show ((2 : ℝ≥0∞)⁻¹ • Measure.count) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul, hcount,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- `uniformSpinMeasure` is Mathlib's uniform distribution on `Bool`. -/
lemma uniformSpinMeasure_eq_uniformOn :
    uniformSpinMeasure = ProbabilityTheory.uniformOn (Set.univ : Set Bool) := by
  rw [ProbabilityTheory.uniformOn, ProbabilityTheory.cond, Measure.restrict_univ,
    uniformSpinMeasure]
  congr 1
  rw [Measure.count_univ, ENat.card_eq_coe_fintype_card, Fintype.card_bool]
  norm_num

/-! ### B6: the Ising Gibbsian specification and Georgii (4.23)(a) -/

/-- The Ising Gibbsian specification of a locally finite graph at inverse temperature `β`,
with uniform a-priori spin measure. -/
noncomputable def isingSpecification {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) : Specification S Bool :=
  Potential.gibbsSpecificationOfAbsolutelySummable (Φ := isingPotential G J h)
    uniformSpinMeasure β

/-- **Existence of Ising Gibbs measures** (Georgii (4.23)(a) for the Ising model):
on any countable, locally finite graph, at every coupling, external field and inverse
temperature, the set of Gibbs measures for the Ising specification is nonempty. -/
theorem isingGibbsMeasure_nonempty {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) :
    (GP (S := S) (E := Bool) (isingSpecification G J h β)).Nonempty :=
  Potential.GP_gibbsSpecification_nonempty (Φ := isingPotential G J h) uniformSpinMeasure β

/-- **Compactness of the set of Ising Gibbs measures** in the topology of local convergence. -/
theorem isCompact_setOf_isingGibbsMeasure {S : Type*} [Countable S] (G : SimpleGraph S)
    [G.LocallyFinite] (J h β : ℝ) :
    IsCompact {μ : WithLocalConvergence S Bool |
      μ.toMeasure ∈ GP (S := S) (E := Bool) (isingSpecification G J h β)} :=
  Potential.isCompact_setOf_mem_GP_gibbsSpecification uniformSpinMeasure β

/-! ### B7: the `ℤ^d` lattice -/

/-- The nearest-neighbour graph on `ℤ^d`: two points are adjacent iff their `ℓ¹` distance
is `1`. (This forces `x ≠ y`.) -/
def latticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj x y := ∑ i, (x i - y i).natAbs = 1
  symm := ⟨fun x y hxy ↦ by
    rw [← hxy]
    exact Finset.sum_congr rfl fun i _ ↦ by omega⟩
  loopless := ⟨fun x hx ↦ by simp at hx⟩

/-- An `ℓ¹`-neighbour of `x` is `x` shifted by `±1` in exactly one coordinate. -/
private lemma latticeGraph_adj_decomp {d : ℕ} {x y : Fin d → ℤ}
    (hxy : (latticeGraph d).Adj x y) :
    ∃ (j : Fin d) (s : ℤ), (s = 1 ∨ s = -1) ∧ y = Function.update x j (x j + s) := by
  classical
  have h1 : ∑ i, (x i - y i).natAbs = 1 := hxy
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (by rw [h1]; exact one_ne_zero)
  have hj1 : (x j - y j).natAbs = 1 := by
    have hle : (x j - y j).natAbs ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun i ↦ (x i - y i).natAbs)
        (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have herase : ∑ i ∈ Finset.univ.erase j, (x i - y i).natAbs = 0 := by
    have hadd := Finset.add_sum_erase Finset.univ (fun i ↦ (x i - y i).natAbs)
      (Finset.mem_univ j)
    omega
  have hrest : ∀ k, k ≠ j → y k = x k := by
    intro k hk
    have hle : (x k - y k).natAbs ≤ ∑ i ∈ Finset.univ.erase j, (x i - y i).natAbs :=
      Finset.single_le_sum (f := fun i ↦ (x i - y i).natAbs)
        (fun i _ ↦ Nat.zero_le _) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    omega
  refine ⟨j, y j - x j, by omega, funext fun k ↦ ?_⟩
  rcases eq_or_ne k j with rfl | hk
  · rw [Function.update_self]
    ring
  · rw [Function.update_of_ne hk]
    exact hrest k hk

/-- `ℤ^d` is locally finite: each point has (at most) `2d` neighbours. -/
noncomputable instance (d : ℕ) : (latticeGraph d).LocallyFinite := fun v ↦
  Set.Finite.fintype <| (Set.finite_range
      (fun p : Fin d × Bool ↦
        Function.update v p.1 (v p.1 + if p.2 then (1 : ℤ) else -1))).subset <| by
    rintro y hy
    obtain ⟨j, s, hs, rfl⟩ := latticeGraph_adj_decomp hy
    rcases hs with rfl | rfl
    · exact ⟨(j, true), by simp⟩
    · exact ⟨(j, false), by simp⟩

/-- **Existence of Gibbs measures for the `ℤ^d` Ising model**, for every coupling, external
field and inverse temperature. -/
theorem latticeIsingGibbsMeasure_nonempty (d : ℕ) (J h β : ℝ) :
    (GP (S := Fin d → ℤ) (E := Bool)
      (isingSpecification (latticeGraph d) J h β)).Nonempty :=
  isingGibbsMeasure_nonempty (latticeGraph d) J h β

/-- **Compactness of the set of `ℤ^d` Ising Gibbs measures** in the topology of local
convergence. -/
theorem isCompact_setOf_latticeIsingGibbsMeasure (d : ℕ) (J h β : ℝ) :
    IsCompact {μ : WithLocalConvergence (Fin d → ℤ) Bool |
      μ.toMeasure ∈ GP (S := Fin d → ℤ) (E := Bool)
        (isingSpecification (latticeGraph d) J h β)} :=
  isCompact_setOf_isingGibbsMeasure (latticeGraph d) J h β

end MeasureTheory.GibbsMeasure

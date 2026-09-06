/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Extracting a linearly independent subfamily from a spanning family

`Mathlib.LinearAlgebra.LinearIndependent.Lemmas` extracts a linearly independent subfamily of a
family `v : ι → V` spanning the same submodule, but indexed by an anonymous type. In a
finite-dimensional space that index type has `finrank K V` elements, so the subfamily can be
re-indexed by `Fin n` for any `n` with `finrank K V = n`. This is the form in which the extraction
is used: "a matrix of rank `r` has `r` linearly independent rows".

## Main results

* `exists_linearIndependent_comp_of_span_eq_top`: a spanning family in an `n`-dimensional space
  has a linearly independent subfamily indexed by `Fin n`.
* `Matrix.det_ne_zero_iff_span_range_row_eq_top`: a square matrix over a field is nonsingular
  exactly when its rows span the whole space.
* `Submodule.span_eq_top_iff_forall_sum_mul_eq_zero`: dually, a family of vectors of `ι → K`
  (`ι` finite) spans exactly when no nonzero covector annihilates it.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function Set Submodule

section Extract

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- **Extraction of a basis from a spanning family.** If `v : ι → V` spans an `n`-dimensional
space then `n` of its members, indexed by `Fin n`, are linearly independent (and hence a basis). -/
theorem exists_linearIndependent_comp_of_span_eq_top [FiniteDimensional K V] {ι : Type*} {n : ℕ}
    (hn : Module.finrank K V = n) (v : ι → V) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ w : Fin n → ι, LinearIndependent K (v ∘ w) := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' K v
  rw [hv] at hspan
  let b : Module.Basis κ K V := Module.Basis.mk hli hspan.ge
  have : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = n := by
    rw [← Module.finrank_eq_card_basis b, hn]
  refine ⟨a ∘ (Fintype.equivFinOfCardEq hcard).symm, ?_⟩
  exact hli.comp _ (Fintype.equivFinOfCardEq hcard).symm.injective

/-- A linearly independent family indexed by `Fin n` in an `n`-dimensional space spans it. -/
theorem span_range_eq_top_of_linearIndependent_of_finrank_eq [FiniteDimensional K V] {n : ℕ}
    (hn : Module.finrank K V = n) {v : Fin n → V} (hv : LinearIndependent K v) :
    Submodule.span K (Set.range v) = ⊤ :=
  hv.span_eq_top_of_card_eq_finrank' (by simp [hn])

section Covector

variable {K ι : Type*} [Field K] [Fintype ι]

/-- The linear functional `v ↦ ∑ i, b i * v i` on `ι → K` attached to a covector `b`. -/
private noncomputable def covectorMap (b : ι → K) : (ι → K) →ₗ[K] K :=
  ∑ i, b i • LinearMap.proj i

private lemma covectorMap_apply (b v : ι → K) : covectorMap b v = ∑ i, b i * v i := by
  simp [covectorMap]

/-- **A spanning criterion in `ι → K` by covectors.** A set `S` of vectors of `ι → K`, `ι` finite,
spans the whole space if and only if the only covector annihilating it is zero: every linear
functional on `ι → K` is of the form `v ↦ ∑ i, b i * v i`, so this says that the annihilator of `S`
is trivial. -/
theorem Submodule.span_eq_top_iff_forall_sum_mul_eq_zero {S : Set (ι → K)} :
    Submodule.span K S = ⊤ ↔ ∀ b : ι → K, (∀ v ∈ S, ∑ i, b i * v i = 0) → b = 0 := by
  classical
  constructor
  · intro htop b hb
    have hker : Submodule.span K S ≤ LinearMap.ker (covectorMap b) :=
      Submodule.span_le.2 fun v hv ↦ by
        show v ∈ LinearMap.ker (covectorMap b)
        simpa only [LinearMap.mem_ker, covectorMap_apply] using hb v hv
    refine funext fun j ↦ ?_
    have hj : covectorMap b (Pi.single j 1) = 0 := by
      simpa only [LinearMap.mem_ker] using hker (htop ▸ Submodule.mem_top)
    rw [covectorMap_apply] at hj
    simpa [Pi.single_apply, Finset.sum_ite_eq'] using hj
  · intro h
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
      (lt_top_iff_ne_top.2 hne) inferInstance
    set b : ι → K := fun i ↦ φ fun j ↦ if i = j then 1 else 0 with hb
    have hφb : ∀ v : ι → K, φ v = ∑ i, b i * v i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, mul_comm]
    have hb0 : b = 0 := by
      refine h b fun v hv ↦ ?_
      have hmem : φ v ∈ (Submodule.span K S).map φ := ⟨v, Submodule.subset_span hv, rfl⟩
      rw [hφ, Submodule.mem_bot] at hmem
      rw [← hφb v, hmem]
    exact hφ0 (LinearMap.ext fun v ↦ by rw [hφb v, hb0]; simp)

/-- A nonzero covector annihilating a family of vectors of `ι → K` prevents it from spanning. -/
theorem Submodule.span_ne_top_of_forall_sum_mul_eq_zero {S : Set (ι → K)} {b : ι → K}
    (hb : b ≠ 0) (h : ∀ v ∈ S, ∑ i, b i * v i = 0) : Submodule.span K S ≠ ⊤ :=
  fun htop ↦ hb (Submodule.span_eq_top_iff_forall_sum_mul_eq_zero.1 htop b h)

end Covector

end Extract

namespace Matrix

variable {K m : Type*} [Field K] [Fintype m] [DecidableEq m]

/-- A square matrix over a field is nonsingular exactly when its rows span the whole space:
Georgii's "well-known theorem of linear algebra", that a matrix of full rank has a full set of
linearly independent rows, in the form in which it is used. -/
theorem det_ne_zero_iff_span_range_row_eq_top {A : Matrix m m K} :
    A.det ≠ 0 ↔ Submodule.span K (Set.range A.row) = ⊤ := by
  have hcard : Fintype.card m = Module.finrank K (m → K) := by
    simp [Module.finrank_fintype_fun_eq_card]
  have key : LinearIndependent K A.row ↔ A.det ≠ 0 :=
    linearIndependent_rows_iff_isUnit.trans ((isUnit_iff_isUnit_det A).trans isUnit_iff_ne_zero)
  exact key.symm.trans ⟨fun h ↦ h.span_eq_top_of_card_eq_finrank' hcard,
    fun h ↦ linearIndependent_of_top_le_span_of_card_eq_finrank h.ge hcard⟩

end Matrix

end

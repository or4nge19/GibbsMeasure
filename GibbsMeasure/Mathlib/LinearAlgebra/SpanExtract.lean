/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
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

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Subgroups of a lattice are ranges of homomorphisms from `ℤ^m`

A subgroup `H` of a finitely generated torsion-free abelian group `A` — a subgroup of a lattice —
is again finitely generated and torsion-free, hence free of some finite rank `m`
(`Module.free_of_finite_type_torsion_free'` over the principal ideal domain `ℤ`).  Choosing a
basis turns the inclusion `H ↪ A` into a homomorphism `ℤ^m →+ A` whose range is exactly `H`.

This is the shape in which a subgroup of `ℤ^d` becomes usable as an *index group*: `ℤ^m` carries
the cubes as an increasing regular Følner sequence, while a subgroup of `ℤ^d` carries no such
sequence on the nose.
-/

@[expose] public section

namespace AddSubgroup

/-- **A subgroup of a lattice is the range of a homomorphism from `ℤ^m`.**  For a finitely
generated torsion-free abelian group `A` and a subgroup `H ≤ A` there are `m : ℕ` and
`f : ℤ^m →+ A` with `Set.range f = H`: the submodule `H` is free of rank `m` over `ℤ`, and `f` is
the composition of the coordinate isomorphism `ℤ^m ≃ₗ H` with the inclusion `H ↪ A`. -/
theorem exists_addMonoidHom_fin_range_eq {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    [NoZeroSMulDivisors ℤ A] (H : AddSubgroup A) :
    ∃ (m : ℕ) (f : (Fin m → ℤ) →+ A), Set.range ⇑f = (H : Set A) := by
  classical
  set M : Submodule ℤ A := AddSubgroup.toIntSubmodule H with hM
  set b := Module.finBasis ℤ M with hb
  refine ⟨Module.finrank ℤ M,
    ((M.subtype).comp (b.equivFun.symm : (Fin (Module.finrank ℤ M) → ℤ) →ₗ[ℤ] M)).toAddMonoidHom,
    Set.ext fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨c, rfl⟩
    exact (b.equivFun.symm c).2
  · intro hx
    exact ⟨b.equivFun ⟨x, hx⟩, by simp⟩

end AddSubgroup

end

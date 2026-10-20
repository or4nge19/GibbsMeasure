/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Finiteness of semidirect products

`N ⋊[φ] G` is in bijection with `N × G` (`SemidirectProduct.equivProd`), so it is finite, and
carries a `Fintype` structure, when `N` and `G` do. For example the signed permutations
`(ι → ℤˣ) ⋊ Perm ι` of a finite type are a `Fintype`, which matrices indexed by them need.

Searched (pin `d13f23b7`): `Mathlib/GroupTheory/SemidirectProduct.lean` has `equivProd` and
`card` (`Nat.card`), but no `Fintype` or `Finite` instance (`#synth Finite (SignedPerm (Fin 3))`
fails).
-/

@[expose] public section

namespace SemidirectProduct

variable {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}

instance [Fintype N] [Fintype G] : Fintype (N ⋊[φ] G) :=
  Fintype.ofEquiv _ equivProd.symm

instance [Finite N] [Finite G] : Finite (N ⋊[φ] G) :=
  .of_equiv _ equivProd.symm

end SemidirectProduct

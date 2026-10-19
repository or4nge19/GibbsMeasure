/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Basic
public import GibbsMeasure.Mathlib.LinearAlgebra.ExteriorAlgebra.Berezin

/-!
# Total cochains are coordinates in the exterior algebra

For an ordered basis `b : Basis ι R M`, the coordinates `x ↦ b.ExteriorAlgebra.repr x` identify
`ExteriorAlgebra R M` with the functions `Finset ι → R` on which `CubicalCochain` works. In these
coordinates, left multiplication by the generator `ι R (b j)` is `wedge j` and the left Grassmann
derivative `contractLeft (b.coord j)` is `contract j` (`wedge_repr`, `contract_repr`). The
anticommutation relations of `wedge` and `contract` are therefore those of the exterior algebra,
and a total cochain at a site is an element of `ExteriorAlgebra R (ι → R)` in its standard basis.
-/

@[expose] public section

open Module Finset

namespace CubicalCochain

variable {ι R M : Type*} [LinearOrder ι] [CommRing R] [AddCommGroup M] [Module R M]
  (b : Basis ι R M)

/-- `wedge j` is left multiplication by the generator `b j`, in the coordinates of the basis
`b.ExteriorAlgebra`. -/
theorem wedge_repr (j : ι) (x : ExteriorAlgebra R M) :
    wedge j ⇑(b.ExteriorAlgebra.repr x) =
      ⇑(b.ExteriorAlgebra.repr (ExteriorAlgebra.ι R (b j) * x)) := by
  have key : wedge j ∘ₗ (Finsupp.lcoeFun ∘ₗ b.ExteriorAlgebra.repr.toLinearMap) =
      Finsupp.lcoeFun ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ
        LinearMap.mulLeft R (ExteriorAlgebra.ι R (b j)) := by
    refine b.ExteriorAlgebra.ext fun s ↦ funext fun J ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self,
      Finsupp.lcoeFun_apply, LinearMap.mulLeft_apply, ExteriorAlgebra.ι_mul_basis, wedge_apply,
      Finsupp.single_apply]
    by_cases hj : j ∈ s
    · simp only [hj, ite_true, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with hJ hs <;> simp_all
    · simp only [hj, ite_false, map_smul, Basis.repr_self, Finsupp.coe_smul, Pi.smul_apply,
        Finsupp.single_apply, smul_eq_mul]
      by_cases hJ : J = insert j s
      · subst hJ
        simp [erase_insert hj, filter_insert]
      · rw [ite_eq_right (Ne.symm hJ)]
        split_ifs with hjJ hs
        · exact absurd (hs ▸ (insert_erase hjJ).symm) hJ
        · simp
        · simp
  exact congrArg (· x) key

/-- `contract j` is the left Grassmann derivative `contractLeft (b.coord j)`, in the coordinates
of the basis `b.ExteriorAlgebra`. -/
theorem contract_repr (j : ι) (x : ExteriorAlgebra R M) :
    contract j ⇑(b.ExteriorAlgebra.repr x) =
      ⇑(b.ExteriorAlgebra.repr (CliffordAlgebra.contractLeft (b.coord j) x)) := by
  have key : contract j ∘ₗ (Finsupp.lcoeFun ∘ₗ b.ExteriorAlgebra.repr.toLinearMap) =
      Finsupp.lcoeFun ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ
        CliffordAlgebra.contractLeft (b.coord j) := by
    refine b.ExteriorAlgebra.ext fun s ↦ funext fun J ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self,
      Finsupp.lcoeFun_apply, ExteriorAlgebra.contractLeft_basis, contract_apply,
      Finsupp.single_apply]
    by_cases hj : j ∈ s
    · simp only [hj, ite_true, map_smul, Basis.repr_self, Finsupp.coe_smul, Pi.smul_apply,
        Finsupp.single_apply, smul_eq_mul]
      by_cases hJ : J = s.erase j
      · subst hJ
        have hfilter : ({i ∈ s.erase j | i < j} : Finset ι) = {i ∈ s | i < j} := by
          ext i
          simp only [mem_filter, mem_erase]
          exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨h.2.ne, h.1⟩, h.2⟩⟩
        simp [insert_erase hj, hfilter]
      · rw [ite_eq_right (Ne.symm hJ)]
        split_ifs with hjJ hs
        · simp
        · exact absurd (hs ▸ (erase_insert hjJ).symm) hJ
        · simp
    · simp only [hj, ite_false, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      split_ifs with hjJ hs
      · rfl
      · exact absurd (hs ▸ mem_insert_self j J) hj
      · simp
  exact congrArg (· x) key

end CubicalCochain

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AbelianGauge.Configuration
public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Torus

/-!
# Flux sectors of an abelian lattice gauge field on the product tori

On the product torus `∏ ℤ/nᵢ` (unit steps `Pi.single i 1`; the coordinate tori `C(n₁, n₂, n₃)`)
the flux sector of a configuration `(A, z)` is the vector of periods of `z`, its sums over the
coordinate `(k + 1)`-tori (`CubicalCochain.periods`); in degree `1`, the integer fluxes through
the coordinate two-tori. The integer shifts change `z` by an exact cochain, whose periods vanish,
so the sector is well defined (`fluxSector`).

* **Flux quantization**: the periods of the field strength are `r` times the sector, through
  every parallel subtorus (`periods_fieldStrength`); in degree `1` with `r = 2π/q`, the flux of
  `F` through each coordinate two-torus is an integer multiple of `2π/q`.
* **Flux decomposition**: every closed integer cochain is `d v` plus the seam cochain of its
  periods (`CubicalCochain.exists_eq_coboundary_add_seam`), so every configuration has a
  representative whose flux is the seam cochain of its sector (`exists_mk_eq_seam`); every
  sector occurs (`fluxSector_surjective`), and the configurations of the trivial sector are those
  with a real potential and no flux (`fluxSector_eq_zero_iff`).

The general tori `ℤᵈ ⧸ Γ` (the diagonal tori of the chamber regularization) need the cohomology
of `ℤᵈ ⧸ Γ` by periods over `Γ`, which `CubicalCochain.Torus` proves for the product tori only.
-/

@[expose] public section

open CubicalCochain

namespace AbelianGauge

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {n : ι → ℕ} [∀ i, NeZero (n i)] {r : ℝ}
  {k : ℕ}

variable (n r k) in
/-- **The flux sector** of a configuration on the product torus: the periods `periods 0 z` of its
flux, the sums of `z` over the coordinate `(k + 1)`-tori. Well defined because exact cochains
have no periods. -/
def fluxSector :
    Configuration (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) r k →+
      (Set.powersetCard ι (k + 1) → ℤ) :=
  QuotientAddGroup.lift _
    ((periods 0).toAddMonoidHom.comp
      ((cocycles ℤ _ (k + 1)).subtype.toAddMonoidHom.comp (AddMonoidHom.snd _ _)))
    (by
      rintro _ ⟨m, rfl⟩
      refine AddMonoidHom.mem_ker.2 ?_
      change periods 0
        ((integerShift _ r k m).2 : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → ℤ) = 0
      rw [integerShift_apply, NegMemClass.coe_neg, map_neg, periods_coboundary, neg_zero])

@[simp]
theorem fluxSector_mk (A : CubicalCell (∀ i, ZMod (n i)) ι k → ℝ)
    (z : cocycles ℤ (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) (k + 1)) :
    fluxSector n r k ((A, z) : Configuration _ r k) =
      periods 0 (z : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → ℤ) :=
  rfl

/-- **Flux quantization**: the periods of the field strength, through every parallel coordinate
`(k + 1)`-torus, are `r` times the flux sector. -/
theorem periods_fieldStrength (x : ∀ i, ZMod (n i))
    (c : Configuration (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) r k) :
    periods x (fieldStrength _ r k c) = fun I ↦ r * fluxSector n r k c I := by
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨A, z⟩ := p
    rw [fieldStrength_mk, map_add, periods_coboundary, zero_add, fluxSector_mk,
      ← periods_eq_of_mem_cocycles z.2 x]
    ext I
    simp [periods_apply, Finset.mul_sum]

/-- **Flux decomposition**: every configuration has a representative whose flux is the seam
cochain of its flux sector. -/
theorem exists_mk_eq_seam
    (c : Configuration (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) r k) :
    ∃ A : CubicalCell (∀ i, ZMod (n i)) ι k → ℝ,
      c = ((A, (⟨seam (fluxSector n r k c), mem_cocycles_iff.2 (coboundary_seam _)⟩ :
        cocycles ℤ (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) (k + 1))) :
          Configuration _ r k) := by
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨A, z⟩ := p
    obtain ⟨v, hv⟩ := exists_eq_coboundary_add_seam (mem_cocycles_iff.1 z.2)
    refine ⟨A + fun b ↦ r * v b, QuotientAddGroup.eq.2 ⟨v, Prod.ext ?_ (Subtype.ext ?_)⟩⟩
    · ext b
      simp
    · change -coboundary _ k v = -(z : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → ℤ) +
        seam (periods 0 (z : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → ℤ))
      set S := seam (periods 0 (z : CubicalCell (∀ i, ZMod (n i)) ι (k + 1) → ℤ))
      rw [hv]
      abel

/-- Every flux sector occurs: `(0, seam w)` has sector `w`. -/
theorem fluxSector_surjective : Function.Surjective (fluxSector n r k (ι := ι)) := fun w ↦
  ⟨(((0 : CubicalCell (∀ i, ZMod (n i)) ι k → ℝ), (⟨seam w,
    mem_cocycles_iff.2 (coboundary_seam w)⟩ :
      cocycles ℤ (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) (k + 1))) :
        Configuration _ r k), periods_seam 0 w⟩

/-- **The trivial flux sector**: a configuration has vanishing fluxes exactly when it is a real
potential with no integer flux. -/
theorem fluxSector_eq_zero_iff
    (c : Configuration (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) r k) :
    fluxSector n r k c = 0 ↔ ∃ A : CubicalCell (∀ i, ZMod (n i)) ι k → ℝ,
      c = ((A, (0 : cocycles ℤ (fun i : ι ↦ (Pi.single i 1 : ∀ i, ZMod (n i))) (k + 1))) :
        Configuration _ r k) := by
  constructor
  · intro h
    obtain ⟨A, hA⟩ := exists_mk_eq_seam c
    refine ⟨A, hA.trans (congrArg _ (Prod.ext rfl (Subtype.ext ?_)))⟩
    simp [h]
  · rintro ⟨A, rfl⟩
    simp

end AbelianGauge

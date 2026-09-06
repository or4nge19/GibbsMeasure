/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The finite dual group of a discrete torus, and orthogonality of its characters

The `N`-torsion subgroup of the torus `UnitAddTorus ι = (ℝ/ℤ)^ι` is the image of `(ZMod N)^ι`
under the coordinatewise map `ZMod.toAddCircle`, `k ↦ (k_c/N)_c`.  It is the dual group of the
discrete torus `(ZMod N)^ι`, and the exponential monomials `UnitAddTorus.mFourier m` restrict to
its characters.

This file identifies that restriction with Mathlib's standard additive character
`ZMod.stdAddChar` and proves the orthogonality relation

`∑_{k ∈ (ZMod N)^ι} mFourier m (k/N) = |(ZMod N)^ι| · 1_{m ≡ 0 mod N}`,

which is the inversion formula for the discrete Fourier transform on `(ZMod N)^ι`.

## Main results

* `ZMod.toUnitAddTorus` — the injective homomorphism `(ZMod N)^ι →+ UnitAddTorus ι`;
  `ZMod.range_toUnitAddTorus` identifies its range with the `N`-torsion subgroup
  `{x | (N : ℤ) • x = 0}`.
* `UnitAddTorus.mFourier_toAddCircle` — one coordinate: `fourier n (j/N) = stdAddChar (n j)`.
* `UnitAddTorus.mFourierZModAddChar` — the restriction of `mFourier m` to the torsion, as an
  `AddChar ((ZMod N)^ι) ℂ`, and `UnitAddTorus.mFourierZModAddChar_eq_zero_iff` — it is trivial
  exactly when `m ≡ 0 mod N`.
* `UnitAddTorus.sum_mFourier_toUnitAddTorus` — **the orthogonality relation**.

## Implementation notes

`Mathlib.Analysis.Fourier.AddCircleMulti` defines `mFourier` but says nothing about torsion
points; `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar` defines `ZMod.toAddCircle`,
`ZMod.toCircle` and `ZMod.stdAddChar` but says nothing about `mFourier`.  This file is the
bridge, so its natural upstream home is `Mathlib/Analysis/Fourier/AddCircleMulti.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset UnitAddTorus
open scoped ComplexConjugate

noncomputable section

/-! ### One coordinate -/

namespace UnitAddTorus

/-- **A monomial is multiplicative in the point**: `fourier n (x + y) = fourier n x · fourier n y`.
Mathlib's `fourier_add` is the multiplicativity in the *index*. -/
theorem fourier_add_apply {T : ℝ} (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `fourier n` is trivial at the origin. -/
theorem fourier_zero_apply {T : ℝ} (n : ℤ) : fourier n (0 : AddCircle T) = 1 :=
  fourier_eval_zero n

/-- **The monomials of the circle at an `N`-torsion point are the standard characters of
`ZMod N`**: `fourier n (j / N) = stdAddChar (n · j)`. -/
theorem mFourier_toAddCircle {N : ℕ} [NeZero N] (n : ℤ) (j : ZMod N) :
    fourier n (ZMod.toAddCircle j) = ZMod.stdAddChar ((n : ZMod N) * j) := by
  have hz : (n : ZMod N) * j = n • j := (zsmul_eq_mul j n).symm
  rw [ZMod.stdAddChar_apply, hz, fourier_apply, ← map_zsmul ZMod.toAddCircle n j]
  rfl

/-- A monomial of the torus is trivial at the origin. -/
theorem mFourier_zero_apply {ι : Type*} [Fintype ι] (m : ι → ℤ) :
    mFourier m (0 : UnitAddTorus ι) = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk]
  exact Finset.prod_eq_one fun c _ ↦ fourier_zero_apply _

/-- **A monomial of the torus is multiplicative in the point.** -/
theorem mFourier_add_apply {ι : Type*} [Fintype ι] (m : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier m (x + y) = mFourier m x * mFourier m y := by
  simp only [mFourier, ContinuousMap.coe_mk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ ↦ fourier_add_apply _ _ _

end UnitAddTorus

/-! ### The torsion subgroup as the dual of a discrete torus -/

namespace ZMod

variable {ι : Type*} {N : ℕ} [NeZero N]

/-- **The `N`-torsion of the torus as the dual of the discrete torus.**  The homomorphism
`(ZMod N)^ι →+ UnitAddTorus ι` sending `k` to `(k_c / N)_c`, coordinatewise `ZMod.toAddCircle`. -/
def toUnitAddTorus : (ι → ZMod N) →+ UnitAddTorus ι :=
  AddMonoidHom.mk' (fun k c ↦ toAddCircle (k c)) fun a b ↦ funext fun c ↦ by
    simp [map_add]

@[simp] theorem toUnitAddTorus_apply (k : ι → ZMod N) (c : ι) :
    toUnitAddTorus k c = toAddCircle (k c) := rfl

theorem toUnitAddTorus_injective : Function.Injective (toUnitAddTorus (ι := ι) (N := N)) :=
  fun _ _ h ↦ funext fun c ↦ toAddCircle_injective N (congrFun h c)

/-- Every point in the image of `toUnitAddTorus` is `N`-torsion. -/
@[simp] theorem zsmul_toUnitAddTorus (k : ι → ZMod N) :
    (N : ℤ) • toUnitAddTorus k = 0 := by
  refine funext fun c ↦ ?_
  have hz : (N : ℤ) • k c = 0 := by simp [zsmul_eq_mul]
  have hc : ((N : ℤ) • toUnitAddTorus k) c = toAddCircle ((N : ℤ) • k c) := by
    rw [Pi.smul_apply, toUnitAddTorus_apply, map_zsmul]
  rw [hc, hz, map_zero, Pi.zero_apply]

/-- **The range of `toUnitAddTorus` is the `N`-torsion subgroup of the torus.**  This is Georgii's
`G_Λ`, the group of `N`-th roots of unity in each coordinate. -/
theorem range_toUnitAddTorus :
    Set.range (toUnitAddTorus (ι := ι) (N := N))
      = {x : UnitAddTorus ι | (N : ℤ) • x = 0} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨k, rfl⟩
    exact zsmul_toUnitAddTorus k
  · intro x hx
    have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
    have hcoord : ∀ c : ι, ∃ j : ZMod N, toAddCircle j = x c := by
      intro c
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (x c)
      have hxc : (N : ℤ) • x c = 0 := congrFun hx c
      rw [← hr, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at hxc
      obtain ⟨j, hj⟩ := hxc
      refine ⟨(j : ZMod N), ?_⟩
      rw [toAddCircle_intCast, ← hr]
      congr 1
      have hjr : (j : ℝ) = (N : ℝ) * r := by
        simpa [zsmul_eq_mul] using hj
      rw [div_eq_iff hN.ne']
      linarith
    choose j hj using hcoord
    exact ⟨j, funext fun c ↦ hj c⟩

end ZMod

/-! ### Orthogonality -/

namespace UnitAddTorus

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

variable (N) in
/-- **The restriction of the monomial `mFourier m` to the `N`-torsion of the torus**, as a
character of the finite group `(ZMod N)^ι`. -/
def mFourierZModAddChar (m : ι → ℤ) : AddChar (ι → ZMod N) ℂ where
  toFun k := mFourier m (ZMod.toUnitAddTorus k)
  map_zero_eq_one' := by rw [map_zero]; exact mFourier_zero_apply m
  map_add_eq_mul' a b := by rw [map_add]; exact mFourier_add_apply m _ _

@[simp] theorem mFourierZModAddChar_apply (m : ι → ℤ) (k : ι → ZMod N) :
    mFourierZModAddChar N m k = mFourier m (ZMod.toUnitAddTorus k) := rfl

/-- **The character attached to `m` is trivial exactly when `m ≡ 0 mod N`.** -/
theorem mFourierZModAddChar_eq_zero_iff (m : ι → ℤ) :
    mFourierZModAddChar N m = 0 ↔ (fun c ↦ ((m c : ℤ) : ZMod N)) = 0 := by
  classical
  constructor
  · intro h
    refine funext fun c ↦ ?_
    change ((m c : ℤ) : ZMod N) = 0
    have hk := congrFun (congrArg DFunLike.coe h) (Pi.single c (1 : ZMod N))
    simp only [mFourierZModAddChar_apply, AddChar.zero_apply] at hk
    have hprod : mFourier m (ZMod.toUnitAddTorus (Pi.single c (1 : ZMod N)))
        = fourier (m c) (ZMod.toAddCircle (1 : ZMod N)) := by
      simp only [mFourier, ContinuousMap.coe_mk, ZMod.toUnitAddTorus_apply]
      rw [Finset.prod_eq_single c]
      · rw [Pi.single_eq_same]
      · intro c' _ hc'
        rw [Pi.single_eq_of_ne hc', map_zero, fourier_zero_apply]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    rw [hprod, mFourier_toAddCircle, mul_one] at hk
    have := ZMod.injective_stdAddChar (N := N)
      (by rw [hk, AddChar.map_zero_eq_one] : ZMod.stdAddChar ((m c : ℤ) : ZMod N)
        = ZMod.stdAddChar (0 : ZMod N))
    simpa using this
  · intro h
    refine AddChar.ext _ _ fun k ↦ ?_
    simp only [mFourierZModAddChar_apply, AddChar.zero_apply, mFourier,
      ContinuousMap.coe_mk, ZMod.toUnitAddTorus_apply]
    refine Finset.prod_eq_one fun c _ ↦ ?_
    rw [mFourier_toAddCircle, congrFun h c]
    simp

/-- **Orthogonality of the characters of the finite dual group `G_Λ`.**

`∑_{k ∈ (ZMod N)^ι} mFourier m (k/N) = |(ZMod N)^ι|` if `m ≡ 0 mod N`, and `0` otherwise.

This is the inversion formula for the discrete Fourier transform on `(ZMod N)^ι`. -/
theorem sum_mFourier_toUnitAddTorus [DecidableEq ι] (m : ι → ℤ) :
    (∑ k : ι → ZMod N, mFourier m (ZMod.toUnitAddTorus k))
      = if (fun c ↦ ((m c : ℤ) : ZMod N)) = 0 then (Fintype.card (ι → ZMod N) : ℂ) else 0 := by
  classical
  have h := AddChar.sum_eq_ite (mFourierZModAddChar N m)
  simp only [mFourierZModAddChar_apply] at h
  rw [h]
  by_cases hm : (fun c ↦ ((m c : ℤ) : ZMod N)) = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hm),
      ite_eq_left_of_eq_true _ _ (eq_true ((mFourierZModAddChar_eq_zero_iff m).2 hm))]
  · have hm' : ¬ mFourierZModAddChar N m = 0 :=
      fun hh ↦ hm ((mFourierZModAddChar_eq_zero_iff m).1 hh)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hm),
      ite_eq_right_of_eq_false _ _ (eq_false hm')]

end UnitAddTorus

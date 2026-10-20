/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.AlgebraicTopology.CubicalCochain.Cohomology
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Configurations of an abelian lattice gauge field with integer fluxes

Let `X` be an abelian group with unit steps `e : ι → X` (`CubicalCochain`): `ℤᵈ`, a product
torus `∏ ℤ/nᵢ`, any torus `ℤᵈ ⧸ Γ`. Fix `r > 0`, the period of the potential (`r = 2π/q` for a
charge `q`). A configuration in degree `k` is a pair `(A, z)` of a real `k`-cochain and a
*closed* integer `(k + 1)`-cochain, modulo the integer shifts
`(A, z) ∼ (A + r n, z - d n)`, `n` an integer `k`-cochain (`integerShift`, `Configuration`).
In degree `k = 1`, `A` is the photon potential on the links and `z` an integer flux on the
plaquettes, with no restriction on its flux through the torus.

Transcription of the photon configuration space (degree `k = 1`, `X = ℤ³ ⧸ Γ`, `r = r_q = 2π/q`):

* (2.2) `Conf(Γ) = {(A, z) : A ∈ C¹(Γ), z ∈ C²(Γ; ℤ), dz = 0} / ∼`,
  `(A, z) ∼ (A + (2π/q) k, z − dk)`, `k ∈ C¹(Γ; ℤ)`.
* (2.3) `F = dA + (2π/q) z`, `u_b = exp(i q A(b))`; both are independent of the representative,
  and `dF = 0`.
* (2.4) each class has a unique representative with `A(b) ∈ [0, r_q)` at every link; the
  measure on `Conf(Γ)` is `∫ Φ = ∑_{z ∈ C²(Γ;ℤ), dz = 0} ∫_{[0, r_q)^{3V}} Φ(A, z) dA`, for
  nonnegative measurable and for absolutely integrable `Φ`; any measurable fundamental domain
  may be used instead, the changes of representative preserving Lebesgue measure in `A` and
  counting measure in `z`.
* (2.5) `C_q(ε) = sup_{y ∈ ℝ} ∑_{j ∈ ℤ} e^{-ε (y + r_q j)²} ≤ 2 + (q / 2π) √(π / ε)`.
* (2.6) `0 < ∫_{Conf(Γ)} e^{-‖F‖² / 2} ≤ (r_q C_q)^{3V}`, `C_q = C_q(1/2)`: drop `dz = 0` and
  sum each plaquette value of `z` separately at fixed `A`.

This file is the group-theoretic part, (2.2), (2.3) and the representative of (2.4); the measure,
(2.4)–(2.6), is `AbelianGauge.Measure`, the flux sectors on product tori `AbelianGauge.FluxSector`.

## Main definitions

* `AbelianGauge.integerShift e r k`: `n ↦ (r n, -d n)`.
* `AbelianGauge.Configuration e r k`: the quotient of `C^k(ℝ) × Z^{k+1}(ℤ)` by the integer
  shifts.
* `AbelianGauge.fieldStrength e r k`: `F = d A + r z`.
* `AbelianGauge.phase e r k`: `A mod r ∈ AddCircle r` on each cell; `AddCircle.toCircle` of it
  is the link phase `u_b = exp (2πi A(b) / r)`.

## Main results

* `coboundary_fieldStrength`: `d F = 0`.
* `fieldStrength_add_mk_coboundary`: `F` is invariant under `A ↦ A + d χ`, `χ` real.
* `injective_phase_prod_fieldStrength`: a configuration is determined by its phases and its
  field strength.
* `existsUnique_mk_eq`: every configuration has a unique representative with
  `A(b) ∈ [0, r)` on every cell.
-/

@[expose] public section

open CubicalCochain

namespace AbelianGauge

variable {X ι : Type*} [AddCommGroup X] [LinearOrder ι] [Fintype ι]

/-- The integer shift `n ↦ (r n, -d n)` of a real `k`-cochain and a closed integer
`(k + 1)`-cochain, `n` an integer `k`-cochain. -/
def integerShift (e : ι → X) (r : ℝ) (k : ℕ) :
    (CubicalCell X ι k → ℤ) →+ (CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1) where
  toFun n := (fun b ↦ r * n b, -⟨coboundary e k n, mem_cocycles_iff.2 (coboundary_coboundary n)⟩)
  map_zero' := Prod.ext (funext fun _ ↦ by simp) (Subtype.ext (by simp))
  map_add' n m := Prod.ext (funext fun _ ↦ by simp [mul_add])
    (Subtype.ext (by
      simp only [Prod.snd_add, map_add, Submodule.coe_neg, Submodule.coe_add, neg_add]))

/-- The configurations in degree `k`: a real `k`-cochain `A` and a closed integer
`(k + 1)`-cochain `z`, modulo the integer shifts `(A, z) ∼ (A + r n, z - d n)`. -/
abbrev Configuration (e : ι → X) (r : ℝ) (k : ℕ) : Type _ :=
  ((CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1)) ⧸ (integerShift e r k).range

variable {e : ι → X} {r : ℝ} {k : ℕ}

@[simp]
theorem integerShift_apply (n : CubicalCell X ι k → ℤ) :
    integerShift e r k n =
      (fun b ↦ r * n b, -⟨coboundary e k n, mem_cocycles_iff.2 (coboundary_coboundary n)⟩) :=
  rfl

/-- The real image of an integer coboundary is the coboundary of the real image. -/
theorem coboundary_intCast (u : CubicalCell X ι k → ℤ) :
    coboundary e k (fun b ↦ (u b : ℝ)) = fun σ ↦ ((coboundary e k u σ : ℤ) : ℝ) :=
  coboundary_map (Int.castRingHom ℝ) u

theorem coboundary_mul_intCast (u : CubicalCell X ι k → ℤ) :
    coboundary e k (fun b ↦ r * u b) = fun σ ↦ r * ((coboundary e k u σ : ℤ) : ℝ) := by
  have h : (fun b ↦ r * (u b : ℝ)) = r • fun b ↦ (u b : ℝ) := rfl
  rw [h, map_smul, coboundary_intCast]
  rfl

/-! ### The field strength -/

variable (e r k) in
/-- **The field strength** `F = d A + r z`: well defined because
`d (r n) + r (-d n) = 0`. -/
def fieldStrength : Configuration e r k →+ CubicalCell X ι (k + 1) → ℝ :=
  QuotientAddGroup.lift _
    { toFun p := coboundary e k p.1 + fun σ ↦ r * (p.2 : CubicalCell X ι (k + 1) → ℤ) σ
      map_zero' := by ext; simp
      map_add' p q := by ext σ; simp only [Prod.fst_add, map_add, Prod.snd_add,
        Submodule.coe_add, Pi.add_apply, Int.cast_add]; ring }
    (by
      rintro _ ⟨n, rfl⟩
      ext σ
      simp [coboundary_mul_intCast])

@[simp]
theorem fieldStrength_mk (A : CubicalCell X ι k → ℝ) (z : cocycles ℤ e (k + 1)) :
    fieldStrength e r k ((A, z) : Configuration e r k) =
      coboundary e k A + fun σ ↦ r * (z : CubicalCell X ι (k + 1) → ℤ) σ :=
  rfl

/-- **`d F = 0`**: `d d A = 0` and `z` is closed. -/
@[simp]
theorem coboundary_fieldStrength (c : Configuration e r k) :
    coboundary e (k + 1) (fieldStrength e r k c) = 0 := by
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨A, z⟩ := p
    rw [fieldStrength_mk, map_add, coboundary_coboundary, zero_add, coboundary_mul_intCast,
      mem_cocycles_iff.1 z.2]
    ext σ
    simp

theorem fieldStrength_mem_cocycles (c : Configuration e r k) :
    fieldStrength e r k c ∈ cocycles ℝ e (k + 1) :=
  coboundary_fieldStrength c

/-- **Gauge invariance**: shifting the potential by the coboundary of a real cochain does not
change the field strength. -/
@[simp]
theorem fieldStrength_add_mk_coboundary (c : Configuration e r (k + 1))
    (χ : CubicalCell X ι k → ℝ) :
    fieldStrength e r (k + 1) (c + ↑(coboundary e k χ, (0 : cocycles ℤ e (k + 1 + 1)))) =
      fieldStrength e r (k + 1) c := by
  ext σ
  simp

/-! ### The phases -/

variable (e r k) in
/-- **The phases** `A mod r` on the cells: well defined because `r n ∈ r ℤ`. For `k = 1` they
are the link phases: `AddCircle.toCircle` sends `A(b) mod r` to `exp (2πi A(b) / r)`
(`AddCircle.toCircle_apply_mk`), which is `exp (i q A(b))` for `r = 2π/q`. -/
def phase : Configuration e r k →+ CubicalCell X ι k → AddCircle r :=
  QuotientAddGroup.lift _
    ((AddMonoidHom.pi fun b ↦ (QuotientAddGroup.mk' _).comp (Pi.evalAddMonoidHom _ b)).comp
      (AddMonoidHom.fst _ _))
    (by
      rintro _ ⟨n, rfl⟩
      refine AddMonoidHom.mem_ker.2 (funext fun b ↦ ?_)
      exact (AddCircle.coe_eq_zero_iff r).2 ⟨n b, by
        change (n b : ℤ) • r = r * (n b : ℝ)
        rw [zsmul_eq_mul, mul_comm]⟩)

@[simp]
theorem phase_mk (A : CubicalCell X ι k → ℝ) (z : cocycles ℤ e (k + 1)) :
    phase e r k ((A, z) : Configuration e r k) = fun b ↦ (A b : AddCircle r) :=
  rfl

/-- **A configuration is determined by its phases and its field strength**: if `A ∈ r ℤ` on
every cell, `A = r n`, and `d A + r z = 0` forces `z = -d n`. -/
theorem injective_phase_prod_fieldStrength (hr : r ≠ 0) :
    Function.Injective ((phase e r k).prod (fieldStrength e r k)) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨A, z⟩ := p
    rw [AddMonoidHom.prod_apply, Prod.mk_eq_zero, phase_mk, fieldStrength_mk] at hc
    obtain ⟨hph, hF⟩ := hc
    choose n hn using fun b ↦ (AddCircle.coe_eq_zero_iff r).1 (congrFun hph b)
    have hA : A = fun b ↦ r * n b := funext fun b ↦ by rw [← hn b, zsmul_eq_mul, mul_comm]
    subst hA
    rw [QuotientAddGroup.eq_zero_iff]
    refine ⟨n, Prod.ext rfl (Subtype.ext (funext fun σ ↦ ?_))⟩
    have h := congrFun hF σ
    rw [coboundary_mul_intCast, Pi.add_apply, Pi.zero_apply, ← mul_add] at h
    have h' : ((coboundary e k n σ + (z : CubicalCell X ι (k + 1) → ℤ) σ : ℤ) : ℝ) = 0 := by
      push_cast
      exact (mul_eq_zero.1 h).resolve_left hr
    simp only [integerShift_apply, NegMemClass.coe_neg, Pi.neg_apply]
    have := Int.cast_eq_zero.1 h'
    omega

/-! ### The representative in `[0, r)` -/

omit [AddCommGroup X] [LinearOrder ι] [Fintype ι] in
/-- Each real cochain has a unique integer shift into `[0, r)` on every cell. -/
theorem existsUnique_add_mul_mem_Ico (hr : 0 < r) (A : CubicalCell X ι k → ℝ) :
    ∃! n : CubicalCell X ι k → ℤ, ∀ b, A b + r * n b ∈ Set.Ico 0 r := by
  have h b := existsUnique_add_zsmul_mem_Ico hr (A b) 0
  simp only [zero_add, zsmul_eq_mul] at h
  choose n hn hu using h
  refine ⟨n, fun b ↦ by simpa [mul_comm] using hn b, fun m hm ↦ funext fun b ↦ hu b (m b) ?_⟩
  simpa [mul_comm] using hm b

/-- **The representative in `[0, r)`**: every configuration has a unique representative
`(A, z)` with `A(b) ∈ [0, r)` on every cell. -/
theorem existsUnique_mk_eq (hr : 0 < r) (c : Configuration e r k) :
    ∃! p : (CubicalCell X ι k → ℝ) × cocycles ℤ e (k + 1),
      (∀ b, p.1 b ∈ Set.Ico 0 r) ∧ (p : Configuration e r k) = c := by
  induction c using QuotientAddGroup.induction_on with
  | H p =>
    obtain ⟨n, hn, -⟩ := existsUnique_add_mul_mem_Ico hr p.1
    refine ⟨p + integerShift e r k n, ⟨fun b ↦ hn b, ?_⟩, ?_⟩
    · rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).2
        (AddMonoidHom.mem_range.2 ⟨n, rfl⟩), add_zero]
    · rintro q ⟨hq, hqp⟩
      obtain ⟨m, hm⟩ := QuotientAddGroup.eq.1 hqp
      have hp : p + integerShift e r k n = q + integerShift e r k (m + n) := by
        rw [map_add, hm]
        abel
      obtain ⟨n₀, -, hu⟩ := existsUnique_add_mul_mem_Ico hr q.1
      have h0 : m + n = 0 := by
        refine (hu (m + n) fun b ↦ ?_).trans (hu 0 fun b ↦ by simpa using hq b).symm
        have hb := congrArg (fun p ↦ p.1 b) hp
        simp only [Prod.fst_add, Pi.add_apply, integerShift_apply, Int.cast_add] at hb
        convert hn b using 1
        simpa only [Pi.add_apply, Int.cast_add] using hb.symm
      rw [hp, h0, map_zero, add_zero]

end AbelianGauge

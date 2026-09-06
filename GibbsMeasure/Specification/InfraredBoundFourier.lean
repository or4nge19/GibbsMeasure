/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiSeries
public import GibbsMeasure.Specification.HeisenbergClusterPoints

/-!
# Georgii §20.2: the Fourier transform of the coupling, (20.9) and (20.10)

Georgii's dual group of `S = ℤ^d` is `G = K^d`, `K` the complex unit circle, and the Fourier
transform of the coupling `J` of (20.1) is

`Ĵ(z) = ∑_{i ∈ ℤ^d} z^i J(i)`  `(z ∈ G)`.  (20.9)

Here `G` is Mathlib's `UnitAddTorus (Fin d) = (ℝ/ℤ)^d` and the character `z ↦ z^i` is
`UnitAddTorus.mFourier i`, so that Georgii's `z^i` is `mFourier i x` and his neutral element
`1 = (1, …, 1)` is `0`.  Writing the torus additively is the only difference from the book.

## Main results

* `MeasureTheory.GibbsMeasure.couplingFourier` — **Georgii (20.9)**, `Ĵ`, as a **real**-valued
  function: Georgii's "Since `J` is even and summable, `Ĵ` is real and continuous".  Realness is
  `ofReal_couplingFourier` (which needs `J` even only) and continuity is
  `continuous_couplingFourier` (which needs `J` summable only).  `couplingFourier_zero` is
  `Ĵ(1) = ∑_i J(i) = ‖J‖₀`, the value at Georgii's neutral element, and
  `abs_couplingFourier_le` is `|Ĵ| ≤ ‖J‖₀`.
* `tsum_mul_mFourier_eq_sum_periodizedCoupling` and
  `couplingFourier_eq_sum_latticeBox` — **Georgii (20.10)**: on the dual `G_Λ` of the discrete
  torus `Λ = (ℤ/2N)^d` — the `2N`-torsion points of `G`, i.e. the `2N`-th roots of unity in each
  coordinate — the transform of `J` is the *finite* sum `∑_{i ∈ Λ} z^i J_Λ(i)` of the periodised
  coupling (17.25).  The proof is the fibrewise decomposition of `ℤ^d` over the torus together
  with the fact that `z^i` depends only on `i mod 2N` when `z ∈ G_Λ`
  (`mFourier_zsmul_eq_one`).

## Conventions

* The cube is `Λ(N) = Potential.latticeBox d L = [-N, N)^d` with `N = L + 1`, as everywhere in
  this development; `Potential.intBoxLen L = 2N` is the period, so Georgii's `G_Λ` is
  `{x | (2N : ℤ) • x = 0}`.
* `couplingFourier` is defined as the real part of the (a priori complex) series.  For an even
  `J` — Georgii's standing hypothesis in (20.1) — the series is real and the real part is no
  loss (`ofReal_couplingFourier`); for a general summable `J` the definition still makes sense
  and (20.10) is stated for the complex series itself, so that nothing depends on the choice.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d : ℕ} {J : (Fin d → ℤ) → ℝ}

/-! ### Georgii (20.9): the Fourier transform of the coupling -/

section Definition

/-- The complex coefficients of Georgii's series (20.9) are summable when `J` is. -/
theorem summable_ofReal_of_summable (hsum : Summable J) :
    Summable fun i : Fin d → ℤ ↦ (J i : ℂ) :=
  Summable.of_norm_bounded hsum.abs fun i ↦ by simp

variable (J) in
/-- **Georgii (20.9).**  The Fourier transform `Ĵ(z) = ∑_{i ∈ ℤ^d} z^i J(i)` of the coupling of
(20.1), on the dual group `G = (ℝ/ℤ)^d` of `ℤ^d`.  Georgii's `z^i` is the character
`UnitAddTorus.mFourier i` and his neutral element `1` is `0`.

`Ĵ` is *real*: the series has real coefficients and `J` is even, so it is invariant under
conjugation (`ofReal_couplingFourier`).  Taking the real part in the definition makes that
manifest without carrying the evenness hypothesis in every statement. -/
def couplingFourier (x : UnitAddTorus (Fin d)) : ℝ :=
  (∑' i : Fin d → ℤ, (J i : ℂ) * mFourier i x).re

/-- **Georgii: "Since `J` is even and summable, `Ĵ` is real"**. -/
theorem ofReal_couplingFourier (heven : ∀ m, J (-m) = J m) (x : UnitAddTorus (Fin d)) :
    ((couplingFourier J x : ℝ) : ℂ) = ∑' i : Fin d → ℤ, (J i : ℂ) * mFourier i x := by
  refine Complex.conj_eq_iff_re.1 ?_
  rw [conj_tsum_mul_mFourier (fun n ↦ by simp)]
  exact tsum_congr fun i ↦ by rw [heven i]

/-- **Georgii: "Since `J` is even and summable, `Ĵ` is … continuous"**.  Continuity needs only
summability. -/
theorem continuous_couplingFourier (hsum : Summable J) :
    Continuous (couplingFourier J) :=
  Complex.continuous_re.comp (continuous_tsum_mul_mFourier (summable_ofReal_of_summable hsum))

/-- `|Ĵ| ≤ ‖J‖₀`. -/
theorem abs_couplingFourier_le (hsum : Summable J) (x : UnitAddTorus (Fin d)) :
    |couplingFourier J x| ≤ ∑' i : Fin d → ℤ, |J i| := by
  refine le_trans (Complex.abs_re_le_norm _) ?_
  refine le_trans (norm_tsum_mul_mFourier_le (summable_ofReal_of_summable hsum) x) ?_
  exact le_of_eq (tsum_congr fun i ↦ by simp)

/-- **Georgii's `Ĵ(1) = ‖J‖₀`.**  The value of the transform at the neutral element of `G` — the
constant configuration `z = (1, …, 1)`, which is `0` in additive notation — is `∑_i J(i)`. -/
theorem couplingFourier_zero :
    couplingFourier J (0 : UnitAddTorus (Fin d)) = ∑' i : Fin d → ℤ, J i := by
  have h : ∀ i : Fin d → ℤ, (J i : ℂ) * mFourier i (0 : UnitAddTorus (Fin d)) = (J i : ℂ) := by
    intro i
    rw [show mFourier i (0 : UnitAddTorus (Fin d)) = 1 from ?_, mul_one]
    simp only [mFourier, ContinuousMap.coe_mk]
    exact Finset.prod_eq_one fun c _ ↦ by simp
  rw [couplingFourier, tsum_congr h, ← Complex.ofReal_tsum, Complex.ofReal_re]

end Definition

/-! ### Georgii (20.10): the transform on the dual of the discrete torus -/

section DiscreteDual

/-- The canonical reduction used in `periodizedCoupling_eq_tsum_ite` is `latticeToTorus`. -/
private lemma coe_eq_latticeToTorus {L : ℕ} (m : Fin d → ℤ) :
    (fun c ↦ ((m c : ℤ) : ZMod (2 * (L + 1)))) = latticeToTorus L m := rfl

/-- **A character of `G_Λ` does not see the period.**  If `x` is killed by the period `P` — for
`P = 2N` this says that `x` is one of Georgii's `2N`-th roots of unity in each coordinate, i.e.
`x ∈ G_Λ` — then `x^{P r} = 1` for every `r ∈ ℤ^d`. -/
theorem mFourier_zsmul_eq_one {x : UnitAddTorus (Fin d)} {P : ℤ} (hx : P • x = 0)
    (r : Fin d → ℤ) : mFourier (P • r) x = 1 := by
  have h : ∀ c : Fin d, fourier ((P • r) c) (x c) = 1 := by
    intro c
    have hxc : P • x c = 0 := by
      have hc := congrFun hx c
      simpa using hc
    rw [Pi.smul_apply, smul_eq_mul, fourier_apply, mul_comm, mul_zsmul, hxc, smul_zero]
    exact fourier_zero'
  simp only [mFourier, ContinuousMap.coe_mk, h, Finset.prod_const_one]

/-- **The characters of `G_Λ` are functions on the discrete torus.**  If `x ∈ G_Λ` then `z^i`
depends on `i` only through its class modulo `2N`. -/
theorem mFourier_congr_of_latticeToTorus_eq {L : ℕ} {x : UnitAddTorus (Fin d)}
    (hx : Potential.intBoxLen L • x = 0) {m m' : Fin d → ℤ}
    (h : latticeToTorus L m = latticeToTorus L m') : mFourier m x = mFourier m' x := by
  obtain ⟨r, hr⟩ := Potential.mem_piPeriods_const_iff.1 ((latticeToTorus_eq_iff m m').1 h)
  have hm : m = m' + Potential.intBoxLen L • r := by
    rw [← hr]; abel
  rw [hm, mFourier_add, mFourier_zsmul_eq_one hx r, mul_one]

/-- **Georgii (20.10).**  On the dual `G_Λ` of the discrete torus `Λ = (ℤ/2N)^d` — the points of
`G` killed by the period `2N` — the transform (20.9) of `J` is the finite sum of the periodised
coupling (17.25) against the same characters:

`Ĵ(z) = ∑_{i ∈ Λ} z^i J_Λ(i)`  for `z ∈ G_Λ`.

The sum is written over the torus, each class represented by its point of the cube `Λ(N)`;
`couplingFourier_eq_sum_latticeBox` is Georgii's form, the sum over the cube. -/
theorem tsum_mul_mFourier_eq_sum_periodizedCoupling (hsum : Summable J) (L : ℕ)
    {x : UnitAddTorus (Fin d)} (hx : Potential.intBoxLen L • x = 0) :
    ∑' i : Fin d → ℤ, (J i : ℂ) * mFourier i x
      = ∑ v : Fin d → ZMod (2 * (L + 1)),
          (periodizedCoupling (L + 1) J v : ℂ) * mFourier (torusToLattice L v) x := by
  classical
  -- the fibres of `ℤ^d → Λ` partition the series
  have hsummable : ∀ v : Fin d → ZMod (2 * (L + 1)), Summable fun m : Fin d → ℤ ↦
      (if latticeToTorus L m = v then (J m : ℂ) * mFourier m x else 0) := by
    intro v
    refine Summable.of_norm_bounded hsum.abs fun m ↦ ?_
    by_cases h : latticeToTorus L m = v <;> simp [h]
  have hsplit : ∑' m : Fin d → ℤ, (J m : ℂ) * mFourier m x
      = ∑ v : Fin d → ZMod (2 * (L + 1)), ∑' m : Fin d → ℤ,
          (if latticeToTorus L m = v then (J m : ℂ) * mFourier m x else 0) := by
    rw [← Summable.tsum_finsetSum fun v _ ↦ hsummable v]
    exact tsum_congr fun m ↦ by simp [Finset.sum_ite_eq]
  rw [hsplit]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  -- on the fibre of `v` the character is constant, equal to its value at the representative
  have hchar : ∀ m : Fin d → ℤ, latticeToTorus L m = v →
      mFourier m x = mFourier (torusToLattice L v) x := by
    intro m hm
    refine mFourier_congr_of_latticeToTorus_eq hx ?_
    rw [hm, latticeToTorus_torusToLattice]
  have hfac : ∀ m : Fin d → ℤ,
      (if latticeToTorus L m = v then (J m : ℂ) * mFourier m x else 0)
        = mFourier (torusToLattice L v) x * (if latticeToTorus L m = v then (J m : ℂ) else 0) := by
    intro m
    split_ifs with h
    · rw [hchar m h]; ring
    · rw [mul_zero]
  have hsum2 : Summable fun m : Fin d → ℤ ↦ (if latticeToTorus L m = v then (J m : ℂ) else 0) := by
    refine Summable.of_norm_bounded hsum.abs fun m ↦ ?_
    by_cases h : latticeToTorus L m = v <;> simp [h]
  rw [tsum_congr hfac, hsum2.tsum_mul_left, mul_comm]
  congr 1
  rw [periodizedCoupling_eq_tsum_ite]
  simp only [coe_eq_latticeToTorus (L := L)]
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun m ↦ ?_
  by_cases h : latticeToTorus L m = v <;> simp [h]

/-- **Georgii (20.10), as he writes it**: the sum over the cube `Λ(N)`. -/
theorem couplingFourier_eq_sum_latticeBox (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (L : ℕ)
    {x : UnitAddTorus (Fin d)} (hx : Potential.intBoxLen L • x = 0) :
    ((couplingFourier J x : ℝ) : ℂ)
      = ∑ i ∈ Potential.latticeBox d L,
          (periodizedCoupling (L + 1) J (latticeToTorus L i) : ℂ) * mFourier i x := by
  classical
  rw [ofReal_couplingFourier heven, tsum_mul_mFourier_eq_sum_periodizedCoupling hsum L hx,
    ← sum_latticeBox_comp_latticeToTorus (n := L) (fun v ↦
      (periodizedCoupling (L + 1) J v : ℂ) * mFourier (torusToLattice L v) x)]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  congr 1
  refine mFourier_congr_of_latticeToTorus_eq hx ?_
  rw [latticeToTorus_torusToLattice]

end DiscreteDual

end MeasureTheory.GibbsMeasure

end

end

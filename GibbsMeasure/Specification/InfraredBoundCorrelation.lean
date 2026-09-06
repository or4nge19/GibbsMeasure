/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.InfraredBoundFourier

/-!
# Georgii (20.11): the Fourier transform of the correlation function, and `0 ≤ C_Λ^Φ`

Georgii's (20.11) is the Fourier transform

`C_Λ^Φ(z) = ∑_{i ∈ Λ} z^i °γ_Λ^Φ(σ_0 · σ_i)`,  `z ∈ G_Λ`,

of the correlation function of the Gibbs distribution in the cube `Λ = Λ(N)` with periodic
boundary condition.  Over an unbounded state space the correlations exist by Lemma (20.6)(ii),
which is `integrable_dotProduct_heisenbergPeriodicGibbsDist` in
`GibbsMeasure.Specification.InfraredBound`.

## Main results

* `MeasureTheory.GibbsMeasure.correlationFourier` — **Georgii (20.11)**.  As for `couplingFourier`
  the definition takes the real part: `C_Λ^Φ` is real, because `°γ_Λ^Φ(σ_0 · σ_i)` is invariant
  under `i ↦ -i` and `z^{-i} = conj(z^i)`.  `correlationFourier_eq_sum` is the definition with the
  real part carried out.
* `card_mul_correlationFourier_eq_sum_integral` — **the identity in Georgii's proof of (20.12)**:

  `|Λ| C_Λ^Φ(z) = ∑_{ℓ = 1}^N °γ_Λ^Φ(|∑_{i ∈ Λ} σ_{i,ℓ} z^i|²)`.

  It is the translation invariance of `°γ_Λ^Φ` on the torus
  (`measurePreserving_shift_heisenbergPeriodicGibbsDist`) together with the multiplicativity of
  the characters of `G_Λ` on the discrete torus.
* `correlationFourier_nonneg` — **the first half of Proposition (20.12)**, `0 ≤ C_Λ^Φ(z)`, for
  every `z ∈ G_Λ`.  Unlike the upper bound it needs neither reflection positivity nor Gaussian
  domination: it is the positivity of a squared modulus.

## Where the rest of (20.12)–(20.15) lives

* **Lemma (20.13)** (Gaussian domination), `°γ_Λ^Φ(f_Λ^Φ(ζ, ·)) ≤ °γ_Λ^Φ(f_Λ^Φ(0, ·)) = 1`, is
  `MeasureTheory.GibbsMeasure.integral_heisenbergShiftFactor_le_one` in
  `GibbsMeasure.Specification.GaussianDomination`, under the hypothesis `IsGaussianDominating`
  (the same inequality read off the a priori measure).  That hypothesis is discharged there for
  an `λ` equivalent to Lebesgue measure (`isGaussianDominating_of_eq_withDensity`), which is
  Georgii's first case; his three further approximation steps, which extend it to a general
  finite `λ` — in particular to the surface measure on a sphere — are not formalised.
* **(20.14)** is `integral_sq_heisenbergShiftPairing_le` and **Proposition (20.12)**, upper half,
  is `correlationFourier_le`, both in `GibbsMeasure.Specification.InfraredBoundTheorem`.
* **Theorem (20.15)** is not formalised; see the module documentation of
  `GibbsMeasure.Specification.InfraredBoundTheorem` for the exact remaining inputs.

## Conventions

The cube is `Λ(N) = Potential.latticeBox (d+1) L`, `N = L + 1`, and the discrete torus is
`(ℤ/2N)^{d+1}`; Georgii's `G_Λ` is `{x : (ℝ/ℤ)^{d+1} | (2N : ℤ) • x = 0}` and his `z^i` is
`UnitAddTorus.mFourier i x`.  The sum (20.11) is written over the torus rather than over the cube:
the two agree because the summand only sees `i` modulo `2N` (`mFourier_congr_of_latticeToTorus_eq`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {d L n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-! ### The characters of `G_Λ` as characters of the discrete torus -/

section Characters

variable {x : UnitAddTorus (Fin (d + 1))}

/-- **A character of `G_Λ` is multiplicative on the discrete torus.** -/
theorem mFourier_torusToLattice_add (hx : Potential.intBoxLen L • x = 0)
    (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    mFourier (torusToLattice L (i + j)) x
      = mFourier (torusToLattice L i) x * mFourier (torusToLattice L j) x := by
  rw [← mFourier_add]
  refine mFourier_congr_of_latticeToTorus_eq hx ?_
  rw [latticeToTorus_torusToLattice, latticeToTorus_add, latticeToTorus_torusToLattice,
    latticeToTorus_torusToLattice]

/-- **The conjugate of a character of `G_Λ` is its inverse**, on the discrete torus:
`z^i \overline{z^j} = z^{i-j}`. -/
theorem mFourier_torusToLattice_mul_conj (hx : Potential.intBoxLen L • x = 0)
    (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    mFourier (torusToLattice L i) x * conj (mFourier (torusToLattice L j) x)
      = mFourier (torusToLattice L (i - j)) x := by
  rw [← mFourier_sub]
  refine mFourier_congr_of_latticeToTorus_eq hx ?_
  rw [latticeToTorus_sub, latticeToTorus_torusToLattice, latticeToTorus_torusToLattice,
    latticeToTorus_torusToLattice]

end Characters

/-! ### Georgii (20.11) -/

section Definition

variable (L n J ν) in
/-- **Georgii (20.11).**  The Fourier transform

`C_Λ^Φ(z) = ∑_{i ∈ Λ} z^i °γ_Λ^Φ(σ_0 · σ_i)`

of the correlation function of the Gibbs distribution in the cube `Λ = Λ(N)` with periodic
boundary condition.  The sum is over the discrete torus; on `G_Λ` the summand depends on `i` only
through its class modulo `2N`, so this is Georgii's sum over the cube.

As for `couplingFourier` the real part is taken in the definition: `C_Λ^Φ` is real
(`card_mul_correlationFourier_eq_sum_integral` exhibits it as a sum of squared moduli), and
carrying the complex value would only add casts. -/
def correlationFourier (x : UnitAddTorus (Fin (d + 1))) : ℝ :=
  (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
    ((∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) : ℝ) : ℂ)
      * mFourier (torusToLattice L i) x).re

/-- (20.11) with the real part carried out. -/
theorem correlationFourier_eq_sum (x : UnitAddTorus (Fin (d + 1))) :
    correlationFourier L n J ν x
      = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        (∫ ω, ω 0 ⬝ᵥ ω i ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
          * (mFourier (torusToLattice L i) x).re := by
  rw [correlationFourier, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Complex.re_ofReal_mul _ _

/-- **Georgii (20.11), as he writes it**: the sum over the cube `Λ(N)`.  On `G_Λ` the summand of
(20.11) depends on the site only through its class modulo `2N`, so the sum over the torus and the
sum over the cube agree. -/
theorem correlationFourier_eq_sum_latticeBox {x : UnitAddTorus (Fin (d + 1))}
    (hx : Potential.intBoxLen L • x = 0) :
    correlationFourier L n J ν x
      = ∑ i ∈ Potential.latticeBox (d + 1) L,
        (∫ ω, ω 0 ⬝ᵥ ω (latticeToTorus L i) ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
          * (mFourier i x).re := by
  classical
  rw [correlationFourier_eq_sum, ← sum_latticeBox_comp_latticeToTorus (n := L) fun v ↦
    (∫ ω, ω 0 ⬝ᵥ ω v ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
      * (mFourier (torusToLattice L v) x).re]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine congrArg _ (congrArg Complex.re ?_)
  refine mFourier_congr_of_latticeToTorus_eq hx ?_
  rw [latticeToTorus_torusToLattice]

end Definition

/-! ### The identity `|Λ| C_Λ^Φ(z) = ∑_ℓ °γ_Λ^Φ(|∑_i σ_{i,ℓ} z^i|²)` -/

section Positivity

variable [IsFiniteMeasure ν]

/-- **Translation invariance of `°γ_Λ^Φ` on the torus**: the two-point correlation depends only on
the difference of the two sites.  No hypothesis on `J` or on `λ` is needed — the periodic Gibbs
distribution is shift invariant by construction
(`measurePreserving_shift_heisenbergPeriodicGibbsDist`). -/
theorem integral_dotProduct_heisenbergPeriodicGibbsDist_sub
    (i j : Fin (d + 1) → ZMod (2 * (L + 1))) :
    (∫ ω, ω i ⬝ᵥ ω j ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
      = ∫ ω, ω 0 ⬝ᵥ ω (i - j) ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
  have hmp := measurePreserving_shift_heisenbergPeriodicGibbsDist
    (N := L + 1) (n := n) (J := J) ν j
  have hg : Measurable fun ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ) ↦ ω i ⬝ᵥ ω j :=
    (measurable_pi_apply i).dotProduct (measurable_pi_apply j)
  have h := integral_map (μ := heisenbergPeriodicGibbsDist (L + 1) n J ν)
    (φ := (shift (Fin n → ℝ) j).toFun) (f := fun ω ↦ ω i ⬝ᵥ ω j)
    (shift (Fin n → ℝ) j).measurable_toFun.aemeasurable
    (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable)
  rw [hmp.map_eq] at h
  rw [h]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp only [shift_toFun_apply, sub_self]
  exact dotProduct_comm _ _

/-- **The identity in Georgii's proof of Proposition (20.12).**

`|Λ| C_Λ^Φ(z) = ∑_{ℓ = 1}^N °γ_Λ^Φ(|∑_{i ∈ Λ} σ_{i,ℓ} z^i|²)`  for `z ∈ G_Λ`.

Georgii's two computations, in one: `°γ_Λ^Φ(|∑_i σ_{i,ℓ} z^i|²) = ∑_{i,j} z^{i-j}
°γ_Λ^Φ(σ_{i,ℓ}σ_{j,ℓ})`, and translation invariance of `°γ_Λ^Φ` on the torus turns the double sum
into `|Λ|` copies of the single sum. -/
theorem card_mul_correlationFourier_eq_sum_integral (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    {x : UnitAddTorus (Fin (d + 1))} (hx : Potential.intBoxLen L • x = 0) :
    (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ) * correlationFourier L n J ν x
      = ∑ l : Fin n, ∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2
          ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
  classical
  have hint := integrable_exp_heisenbergExponent (N := L + 1) (d := d + 1) (J := J) hexp hsum
  have hprob := isProbabilityMeasure_heisenbergPeriodicGibbsDist hν hint
  have htail := fun a (ha : 0 < a) ↦
    exists_forall_heisenbergPeriodicGibbsDist_tail_le (N := L + 1) (d := d) (n := n)
      hν hexp hsum heven hnd ha
  -- integrability
  have hintmul : ∀ (i j : Fin (d + 1) → ZMod (2 * (L + 1))) (l : Fin n),
      Integrable (fun ω ↦ ω i l * ω j l) (heisenbergPeriodicGibbsDist (L + 1) n J ν) :=
    fun i j l ↦ integrable_mul_apply_of_tail htail i j l
  have hintdot : ∀ i j : Fin (d + 1) → ZMod (2 * (L + 1)),
      Integrable (fun ω ↦ ω i ⬝ᵥ ω j) (heisenbergPeriodicGibbsDist (L + 1) n J ν) :=
    fun i j ↦ integrable_dotProduct_of_tail htail i j
  -- the pointwise expansion of the squared modulus
  have hptwise : ∀ (l : Fin n) (ω : (Fin (d + 1) → ZMod (2 * (L + 1))) → (Fin n → ℝ)),
      ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
          ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2
        = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (ω i l * ω j l) * (mFourier (torusToLattice L (i - j)) x).re := by
    intro l ω
    have hc : ((‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2 : ℝ) : ℂ)
        = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l * ω j l : ℝ) : ℂ) * mFourier (torusToLattice L (i - j)) x := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, Complex.conj_ofReal, ← mFourier_torusToLattice_mul_conj hx i j]
      push_cast
      ring
    have hre := congrArg Complex.re hc
    simpa only [Complex.ofReal_re, Complex.re_sum, Complex.re_ofReal_mul] using hre
  -- integrate the expansion
  have hstep : ∀ l : Fin n,
      (∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
            ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2
          ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
        = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
            (mFourier (torusToLattice L (i - j)) x).re
              * ∫ ω, ω i l * ω j l ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
    intro l
    rw [integral_congr_ae (.of_forall fun ω ↦ hptwise l ω),
      integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
        ((hintmul i j l).mul_const _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ ((hintmul i j l).mul_const _)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [integral_mul_const, mul_comm]
  -- sum over the coordinates
  have hdot : ∀ i j : Fin (d + 1) → ZMod (2 * (L + 1)),
      (∑ l : Fin n, ∫ ω, ω i l * ω j l ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
        = ∫ ω, ω i ⬝ᵥ ω j ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
    intro i j
    rw [← integral_finsetSum _ fun l _ ↦ hintmul i j l]
    exact integral_congr_ae (.of_forall fun ω ↦ rfl)
  -- assemble the right-hand side
  have hRHS : (∑ l : Fin n, ∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
          ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2
        ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
      = ∑ i : Fin (d + 1) → ZMod (2 * (L + 1)), ∑ j : Fin (d + 1) → ZMod (2 * (L + 1)),
          (mFourier (torusToLattice L (i - j)) x).re
            * ∫ ω, ω 0 ⬝ᵥ ω (i - j) ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) := by
    rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) ↦ hstep l, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.mul_sum, hdot i j,
      integral_dotProduct_heisenbergPeriodicGibbsDist_sub i j]
  rw [hRHS]
  -- reindex the double sum
  have hreindex : ∀ j : Fin (d + 1) → ZMod (2 * (L + 1)),
      (∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        (mFourier (torusToLattice L (i - j)) x).re
          * ∫ ω, ω 0 ⬝ᵥ ω (i - j) ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν))
        = ∑ k : Fin (d + 1) → ZMod (2 * (L + 1)),
          (mFourier (torusToLattice L k) x).re
            * ∫ ω, ω 0 ⬝ᵥ ω k ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) :=
    fun j ↦ Equiv.sum_comp (Equiv.subRight j) fun k ↦
      (mFourier (torusToLattice L k) x).re
        * ∫ ω, ω 0 ⬝ᵥ ω k ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν)
  rw [Finset.sum_comm, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hreindex j,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, correlationFourier_eq_sum]
  refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ mul_comm _ _)

/-- **The first half of Georgii, Proposition (20.12)**: `0 ≤ C_Λ^Φ(z)` for every `z ∈ G_Λ`.

Unlike the upper bound of (20.12) this needs neither reflection positivity nor Gaussian
domination: by `card_mul_correlationFourier_eq_sum_integral`, `|Λ| C_Λ^Φ(z)` is a sum of integrals
of squared moduli. -/
theorem correlationFourier_nonneg (hν : ν ≠ 0) (hexp : HasExpSqMoments ν) (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hnd : ∀ k, IsNonnegDefiniteAt k J)
    {x : UnitAddTorus (Fin (d + 1))} (hx : Potential.intBoxLen L • x = 0) :
    0 ≤ correlationFourier L n J ν x := by
  have hcard : (0 : ℝ) < (Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) : ℝ) := by
    have : 0 < Fintype.card (Fin (d + 1) → ZMod (2 * (L + 1))) :=
      Fintype.card_pos_iff.2 ⟨0⟩
    exact_mod_cast this
  have hkey := card_mul_correlationFourier_eq_sum_integral hν hexp hsum heven hnd hx
  have hnn : 0 ≤ ∑ l : Fin n, ∫ ω, ‖∑ i : Fin (d + 1) → ZMod (2 * (L + 1)),
        ((ω i l : ℝ) : ℂ) * mFourier (torusToLattice L i) x‖ ^ 2
      ∂(heisenbergPeriodicGibbsDist (L + 1) n J ν) :=
    Finset.sum_nonneg fun l _ ↦ integral_nonneg fun ω ↦ by positivity
  nlinarith [hkey, hnn, hcard]

end Positivity

end MeasureTheory.GibbsMeasure

end

end

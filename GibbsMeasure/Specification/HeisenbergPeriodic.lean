/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PosSemidefFactor
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.CircleCharacter
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.BoxAverage
public import Mathlib.Algebra.Order.Star.Real
public import GibbsMeasure.Potential
public import GibbsMeasure.Specification.PeriodicGibbs

/-!
# Georgii §17.2: Heisenberg potentials and `r_k`-positivity, (17.22)–(17.32)

Georgii's second family of reflection positive periodic Gibbs distributions.  The spins take
values in `ℝ^n`, the interaction is the Heisenberg pair potential (17.22)
`Φ_{{i,j}} = -J(i-j) σ_i · σ_j`, and the reflection is `r_k` — the reflection (17.5) in a plane
*between* the sites, for which the product measure `λ^Λ` is already positive
(`isReflectionPositive_siteEquiv_pi` in `GibbsMeasure.Specification.PeriodicGibbs`).

## The potential and its periodic Gibbs distribution, (17.22)–(17.25)

* `heisenbergPotential`: **Georgii (17.22)**, the Heisenberg pair potential on `ℤ^d`, as a
  `Potential (Fin d → ℤ) (Fin n → ℝ)`.  `heisenbergPotential_pair`,
  `heisenbergPotential_singleton` and `heisenbergPotential_of_forall_ne` are its values, and
  `isPotential_heisenbergPotential` is Georgii (2.2)(i).  Georgii's (17.23) is the hypothesis
  `Summable J`, which enters the theorems below.  Absolute summability in the sense of the space
  `ℬ` (2.11) is *not* asserted: over an unbounded spin space the sup-norm `‖Φ_{{i,j}}‖` of (2.12)
  is a supremum over all of `(ℝ^n)^{ℤ^d}` and is infinite whenever `J(i-j) ≠ 0`.  Georgii does not
  claim it either; his standing hypotheses in §17.2 are (17.23) and the finiteness of `°Z_Λ^Φ`.
* `periodizedCoupling`: **Georgii (17.25)**, `J_Λ(m) = ∑_{ℓ ∈ ℤ^d} J(m + 2Nℓ)` as a function on
  the torus `Λ = (ℤ/2N)^d`; it does not depend on the lift (`periodizedCoupling_eq_tsum`), it is
  even when `J` is (`periodizedCoupling_neg`), and it inherits the invariance of `J` under the
  flip of the `k`-th coordinate (`periodizedCoupling_flipTorus`).
* `heisenbergExponent`, `heisenbergPeriodicGibbs`, `heisenbergPeriodicGibbsDist`:
  **Georgii (17.24)**, the density `exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i · σ_j]` relative to `λ^Λ`, and
  the measures it defines.  As in `GibbsMeasure.Specification.PeriodicGibbs` for the
  `C`-potentials of (17.18), the Gibbs distribution with periodic boundary condition is *defined*
  by its density, which is Georgii's Example (4.20)(2) computation.
  `heisenbergExponent_eq_offDiag_add_diag` isolates the diagonal of Georgii's double sum: it is
  the self-energy `½ J_Λ(0) |σ_i|²` of a site interacting with its own translates.

## Nonnegative definiteness relative to `r_k`, (17.27)–(17.28)

* `repCharacter`, `IsNonnegDefiniteAt`: **Georgii (17.27)**, the bounded semicharacters
  `i ↦ x^{i_k-1} ∏_{c ≠ k} z_c^{i_c}` and the existence of a finite representing measure `α` on
  `]-1, 1[ × K^{d-1}` with `J i = ∫ α x^{i_k-1} ∏_{c≠k} z_c^{i_c}` for `i_k ≥ 1`.  The circle is
  parametrised by its angle, so `α` lives on `ℝ × ℝ^d` and is carried by `|x| < 1`.
* `IsNonnegDefiniteAt.nonneg_of_odd`, `IsNonnegDefiniteAt.neg_one_zpow`,
  `IsNonnegDefiniteAt.mul`: **Georgii, Comments (17.28)(3) and (17.28)(2)**.
* `IsNonnegDefiniteAt.flipCoord_eq`: nonnegative definiteness relative to `r_k` forces `J` to be
  invariant under the sign flip of the `k`-th coordinate.  Georgii uses this silently in the proof
  of (17.29) when he writes the exponent as `h + h∘r_k + H`; it does not follow from evenness
  alone (the function on `ℤ²` supported on `±(1,1)` is a counterexample).
* `isNonnegDefiniteAt_of_prod`: a representing measure of the product form `ρ ⊗ σ`, which is the
  shape of all of Georgii's Examples (17.30)–(17.32).

**Not formalised.**  Georgii's Comment (17.28)(1) — that (17.27) is *equivalent* to the
nonnegativity of all the sums `∑_{i,j} z_i z̄_j J(i_1+j_1-1, i_2-j_2, …)` — is a citation of
Berg–Maserick (1984) combined with the Herglotz lemma, proved neither in the book nor here.  Only
the direction that is used, (17.27) ⟹ `r_k`-positivity, is proved.

## Theorem (17.29)

* `crossingMatrix`: `M(i, j) = J_Λ(r_k i - j)` on `Λ_{+,k} × Λ_{+,k}`, extended by zero; Georgii's
  `H`, the part of the exponent coupling the two halves of the torus, is
  `∑_{i,j} M(i,j) σ_{r_k i} · σ_j` (`heisenbergExponent_eq_add`, which is his decomposition
  `h + h∘r_k + H`).
* `isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef`: `r_k`-positivity of `°Z_Λ^Φ °γ_Λ^Φ`
  whenever `M` is positive semidefinite, by the Gram factorisation
  (`Matrix.PosSemidef.exists_sum_mul`) and the finite-sum form of Lemma (17.26),
  `isReflectionPositive_siteEquiv_withDensity_sum`.
* `IsNonnegDefiniteAt.posSemidef_crossingMatrix`: **the analytic core of (17.29)**.  Georgii sums
  the `k`-direction of the periodisation as two geometric series (`tsum_J_axis_shift`), which
  produces his factor `(1 - x^{2N})⁻¹` (`integrable_resolvent` is his estimate
  `∑_{t ≥ 0} ∫ α x^{2Nt} = ∑_{t ≥ 0} J(1 + 2Nt, 0, …, 0) < ∞`), and regularises the transverse
  directions by the Cesàro average over `-L ≤ ℓ, ℓ' ≤ L`, which turns `∑_{ℓ,ℓ'} z^{2N(ℓ-ℓ')}` into
  `|∑_ℓ z^{2Nℓ}|²`.  Here `heisVecPos`, `heisVecNeg` are his `h_{(0,x,z)}`, `h_{(1,x,z)}`,
  `tsum_J_crossing_eq_integral` is the Gram identity for a single pair of sites,
  `sum_tsum_J_crossing_nonneg` is the Gram bound for a box, and the limit `L → ∞` is
  `Summable.tendsto_boxAverage_sub`.

  **Deviation from the book (an improvement, not an erratum).**  Georgii takes the limit
  `L → ∞` at the level of the measures `μ_{Λ,L}`, for which he needs convergence in variational
  distance.  Here it is taken at the level of the crossing matrix, where it is just the closedness
  of the quadratic-form condition; the measures never have to be compared.
* `isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt` and
  `isReflectionPositive_heisenbergPeriodicGibbsDist_of_isNonnegDefiniteAt`:
  **Georgii, Theorem (17.29)** as stated, for `°Z_Λ^Φ °γ_Λ^Φ` and for `°γ_Λ^Φ`.

## Examples

* **(17.30)** Ferromagnetic nearest-neighbour potentials.  `isNonnegDefiniteAt_of_nearestNeighbour`
  is Georgii's representing measure `J(e_k) δ_0 × ν^{d-1}`; only `0 ≤ J(e_k)` is needed, since
  `i_k ≥ 1` already forces `i = e_k` on the support of a nearest-neighbour `J`.
  `isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour` is the conclusion, obtained
  directly from `posSemidef_crossingMatrix_nearestNeighbour`: for a nearest-neighbour coupling the
  crossing matrix is *diagonal* with nonnegative entries
  (`crossingMatrix_eq_zero_of_nearestNeighbour`), so no appeal to (17.29) is needed.
* **(17.31)** Next-nearest neighbour potentials.  `isNonnegDefiniteAt_of_nextNearestNeighbour`
  is Georgii's representing measure `δ_0(dz_k) [A + B ∑_{c ≠ k}(z_c + z̄_c)] ∏_{c ≠ k} ν(dz_c)`;
  the hypothesis `A ≥ 2(d-1)|B|` is exactly what makes that density nonnegative, and
  `integral_cos_mul_exp_sum_int_mul_I` computes its Fourier coefficients.
  `isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour` is the conclusion.
* **(17.32)** Long range potentials, `d = 1`.  `isNonnegDefiniteAt_rpow`: `J(i) = β |i|^{-a}` with
  `β ≥ 0`, `a > 0` is nonnegative definite relative to `r_0`, with Georgii's representing measure
  `β` times the image of the gamma distribution under `s ↦ e^{-s}` (`gammaWeight`,
  `integral_pow_map_exp_neg`).

## Not formalised

* Georgii's Comment (17.28)(1), the Berg–Maserick converse (see above).
* The case `d = 2` of Example (17.32), which needs the Fourier transform of the Cauchy kernel and
  the substitution `s = (1 + t²(1 + ℓ²/k²))^{1/2}` on top of the case `d = 1` and Comment
  (17.28)(2) (`IsNonnegDefiniteAt.mul`, which *is* proved).
* The *necessity* halves of (17.30) and (17.31) — that `°γ_Λ^Φ` fails to be `r_k`-positive when
  `J(e_k) < 0`, resp. when `A < 2(d-1)|B|`.  Georgii proves them by evaluating
  `°Z_Λ^Φ °γ_Λ^Φ(f f^*)` at an explicit `f` for the two-point a priori measure `λ = δ_1 + δ_{-1}`.
  A remark on the constant: the value is `4 sinh[C J(u)]` with `C = 2(2N)^{d-1}`, not `(2N)^{d-1}`
  as printed in the book — on the torus the plane of `r_k` is met by *two* interfaces, and each
  contributes `(2N)^{d-1}` bonds.  Only the sign of the constant matters for Georgii's conclusion.
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii (17.25): the periodised coupling -/

section Periodize

variable {d : ℕ}

/-- The canonical lift of a torus site to `ℤ^d`, with coordinates in `{0, …, 2N-1}`. -/
def torusLift (N : ℕ) (z : Fin d → ZMod (2 * N)) : Fin d → ℤ := fun c ↦ ((z c).val : ℤ)

variable {N : ℕ} {J : (Fin d → ℤ) → ℝ}

/-- Translating the base point of the sum `∑_ℓ J(m + 2Nℓ)` by a multiple of `2N` does not change
it: the summation index is reindexed by a translation of `ℤ^d`. -/
lemma tsum_add_zsmul_left (J : (Fin d → ℤ) → ℝ) (N : ℕ) (m t : Fin d → ℤ) :
    ∑' ℓ : Fin d → ℤ, J (m + (2 * N : ℤ) • t + (2 * N : ℤ) • ℓ)
      = ∑' ℓ : Fin d → ℤ, J (m + (2 * N : ℤ) • ℓ) := by
  have key : ∀ ℓ : Fin d → ℤ, m + (2 * N : ℤ) • t + (2 * N : ℤ) • ℓ
      = m + (2 * N : ℤ) • (ℓ + t) := by
    intro ℓ; rw [smul_add]; abel
  simp only [key]
  exact Equiv.tsum_eq (Equiv.addRight t) fun ℓ : Fin d → ℤ ↦ J (m + (2 * N : ℤ) • ℓ)

/-- **Georgii (17.25).**  The periodised coupling `J_Λ(k) = ∑_{ℓ ∈ ℤ^d} J(k + 2Nℓ)`, viewed as a
function on the torus `Λ = (ℤ/2N)^d`.  It is defined through the canonical lift, and
`periodizedCoupling_eq_tsum` shows that any other lift gives the same value. -/
def periodizedCoupling (N : ℕ) (J : (Fin d → ℤ) → ℝ) (z : Fin d → ZMod (2 * N)) : ℝ :=
  ∑' ℓ : Fin d → ℤ, J (torusLift N z + (2 * N : ℤ) • ℓ)

variable [NeZero N]

/-- **The periodised coupling does not depend on the lift.** -/
lemma periodizedCoupling_eq_tsum {m : Fin d → ℤ} {z : Fin d → ZMod (2 * N)}
    (hm : ∀ c, ((m c : ℤ) : ZMod (2 * N)) = z c) :
    periodizedCoupling N J z = ∑' ℓ : Fin d → ℤ, J (m + (2 * N : ℤ) • ℓ) := by
  have hdvd : ∀ c, ((2 * N : ℕ) : ℤ) ∣ (m c - torusLift N z c) := by
    intro c
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [torusLift, hm c]
    simp [ZMod.natCast_val, ZMod.intCast_cast]
  choose t ht using fun c ↦ (hdvd c)
  have hmt : m = torusLift N z + (2 * N : ℤ) • t := by
    funext c
    have := ht c
    push_cast at this ⊢
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    omega
  rw [periodizedCoupling, ← tsum_add_zsmul_left J N (torusLift N z) t, ← hmt]

variable [NeZero N]

@[simp] lemma intCast_torusLift (z : Fin d → ZMod (2 * N)) (c : Fin d) :
    ((torusLift N z c : ℤ) : ZMod (2 * N)) = z c := by
  simp [torusLift, ZMod.natCast_val, ZMod.intCast_cast]

/-- **`J_Λ` is even when `J` is** (Georgii's standing hypothesis (17.23)). -/
lemma periodizedCoupling_neg (heven : ∀ m, J (-m) = J m) (z : Fin d → ZMod (2 * N)) :
    periodizedCoupling N J (-z) = periodizedCoupling N J z := by
  rw [periodizedCoupling_eq_tsum (J := J) (m := -(torusLift N z)) (z := -z) (by intro c; simp),
    periodizedCoupling]
  have key : ∀ ℓ : Fin d → ℤ, J (-torusLift N z + (2 * N : ℤ) • ℓ)
      = J (torusLift N z + (2 * N : ℤ) • (-ℓ)) := by
    intro ℓ
    rw [← heven (torusLift N z + (2 * N : ℤ) • (-ℓ))]
    congr 1
    simp only [smul_neg, neg_add, neg_neg]
  simp only [key]
  exact Equiv.tsum_eq (Equiv.neg _) fun ℓ ↦ J (torusLift N z + (2 * N : ℤ) • ℓ)

end Periodize

/-! ### Georgii (17.22)–(17.23): the Heisenberg potential on `ℤ^d`

Georgii's Heisenberg potentials are the shift-invariant pair potentials
`Φ_{{i,j}} = -J(i-j) σ_i · σ_j` with an even, absolutely summable `J` vanishing at the origin.
They are *not* absolutely summable in the sense of Georgii's space `ℬ` (2.11) when the spin space
is unbounded: `‖Φ_{{i,j}}‖ = sup_σ |J(i-j) σ_i · σ_j| = ∞` as soon as `J(i-j) ≠ 0`.  Georgii does
not claim they are; his standing assumption in §17.2 is only (17.23), `∑_m |J(m)| < ∞`, together
with the finiteness of `°Z_Λ^Φ`. -/

section HeisenbergPotential

variable {d n : ℕ} {J : (Fin d → ℤ) → ℝ}

variable (n) in
/-- **Georgii (17.22).**  The shift-invariant Heisenberg pair potential
`Φ_{{i,j}}(σ) = -J(i-j) σ_i · σ_j` on `ℤ^d`, with spins in `ℝ^n`, and `Φ_A = 0` for every `A`
which is not a pair.  It is written as a symmetric double sum over `A`: no ordering of `ℤ^d` is
needed, and `Φ_A` is manifestly a function of the coordinates in `A`. -/
def heisenbergPotential (J : (Fin d → ℤ) → ℝ) : Potential (Fin d → ℤ) (Fin n → ℝ) :=
  fun A ω ↦ -(∑ i ∈ A, ∑ j ∈ A, if A = {i, j} then J (i - j) * (ω i ⬝ᵥ ω j) else 0) / 2

/-- The Heisenberg potential vanishes on every interaction support which is not a pair. -/
lemma heisenbergPotential_of_forall_ne {A : Finset (Fin d → ℤ)}
    (h : ∀ i j, A ≠ ({i, j} : Finset (Fin d → ℤ))) (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPotential n J A ω = 0 := by
  classical
  rw [heisenbergPotential]
  rw [Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ if_neg (h i j)]
  simp

/-- **Georgii (17.22) on a pair.**  For two distinct sites the interaction is
`-J(i-j) σ_i · σ_j`; the two orderings of the pair contribute equally because `J` is even. -/
lemma heisenbergPotential_pair (heven : ∀ m, J (-m) = J m) {i j : Fin d → ℤ} (hij : i ≠ j)
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    heisenbergPotential n J {i, j} ω = -(J (i - j) * (ω i ⬝ᵥ ω j)) := by
  classical
  have hsing : ∀ a : Fin d → ℤ, ({i, j} : Finset (Fin d → ℤ)) ≠ {a, a} := by
    intro a h
    have hi : i ∈ ({a, a} : Finset (Fin d → ℤ)) := h ▸ Finset.mem_insert_self i {j}
    have hj : j ∈ ({a, a} : Finset (Fin d → ℤ)) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hi hj
    exact hij (hi.trans hj.symm)
  have hji : J (j - i) = J (i - j) := by rw [← heven (i - j)]; congr 1; abel
  rw [heisenbergPotential, Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij,
    if_neg (hsing i), if_neg (hsing j), if_pos rfl, if_pos (Finset.pair_comm i j),
    hji, dotProduct_comm (ω j) (ω i)]
  ring

/-- The Heisenberg potential has no one-body part: `J 0 = 0` is Georgii's normalisation. -/
lemma heisenbergPotential_singleton (hJ0 : J 0 = 0) (i : Fin d → ℤ)
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) : heisenbergPotential n J {i} ω = 0 := by
  classical
  rw [heisenbergPotential, Finset.sum_singleton, Finset.sum_singleton]
  simp [hJ0]

instance isPotential_heisenbergPotential : Potential.IsPotential (heisenbergPotential n J) where
  measurable A := by
    classical
    let _ : MeasurableSpace ((Fin d → ℤ) → (Fin n → ℝ)) :=
      cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ)) (A : Set (Fin d → ℤ))
    refine Measurable.div_const (Measurable.neg (Finset.measurable_sum _ fun i hi ↦
      Finset.measurable_sum _ fun j hj ↦ ?_)) 2
    by_cases h : A = ({i, j} : Finset (Fin d → ℤ))
    · simp only [if_pos h]
      refine Measurable.const_mul ?_ _
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun c _ ↦ Measurable.mul ?_ ?_
      · exact (measurable_pi_apply c).comp
          (measurable_cylinderEvent_apply (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ)) hi)
      · exact (measurable_pi_apply c).comp
          (measurable_cylinderEvent_apply (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ)) hj)
    · simp only [if_neg h]
      exact measurable_const

end HeisenbergPotential

/-! ### The reflection of a single coordinate

Georgii's proof of (17.29) writes the exponent as `h + h∘r_k + H`, which silently uses that
`J_Λ` is invariant under the sign flip of the `k`-th coordinate: the two halves of the
Hamiltonian are mirror images of one another only then.  Evenness of `J` alone does not give
this — `J` supported on `±(1,1) ⊂ ℤ^2` is even and is not invariant under flipping the first
coordinate — but nonnegative definiteness relative to `r_k` does, see
`IsNonnegDefiniteAt.flipCoord_eq`. -/

section Flip

variable {d : ℕ} (k : Fin d)

/-- The sign flip of the `k`-th coordinate of `ℤ^d`. -/
def flipCoord (m : Fin d → ℤ) : Fin d → ℤ := Function.update m k (-(m k))

variable {k}

@[simp] lemma flipCoord_self (m : Fin d → ℤ) : flipCoord k m k = -(m k) := by
  simp [flipCoord]

@[simp] lemma flipCoord_of_ne {c : Fin d} (h : c ≠ k) (m : Fin d → ℤ) :
    flipCoord k m c = m c := by
  simp [flipCoord, h]

@[simp] lemma flipCoord_flipCoord (m : Fin d → ℤ) : flipCoord k (flipCoord k m) = m := by
  funext c
  by_cases h : c = k <;> simp [h]

lemma flipCoord_add (m m' : Fin d → ℤ) :
    flipCoord k (m + m') = flipCoord k m + flipCoord k m' := by
  funext c
  by_cases h : c = k <;> simp [h] <;> ring

lemma flipCoord_zsmul (a : ℤ) (m : Fin d → ℤ) : flipCoord k (a • m) = a • flipCoord k m := by
  funext c
  by_cases h : c = k <;> simp [h]

variable (k) in
/-- The sign flip of the `k`-th coordinate as an involution of `ℤ^d`. -/
def flipCoordEquiv : (Fin d → ℤ) ≃ (Fin d → ℤ) where
  toFun := flipCoord k
  invFun := flipCoord k
  left_inv := flipCoord_flipCoord
  right_inv := flipCoord_flipCoord

@[simp] lemma flipCoordEquiv_apply (m : Fin d → ℤ) : flipCoordEquiv k m = flipCoord k m := rfl

/-- The sign flip of the `k`-th coordinate of the torus. -/
def flipTorus {N : ℕ} (k : Fin d) (z : Fin d → ZMod (2 * N)) : Fin d → ZMod (2 * N) :=
  Function.update z k (-(z k))

variable {N : ℕ} {J : (Fin d → ℤ) → ℝ} [NeZero N]

/-- **`J_Λ` inherits the invariance of `J` under the flip of the `k`-th coordinate.** -/
lemma periodizedCoupling_flipTorus (hflip : ∀ m, J (flipCoord k m) = J m)
    (z : Fin d → ZMod (2 * N)) :
    periodizedCoupling N J (flipTorus k z) = periodizedCoupling N J z := by
  have hlift : ∀ c, ((flipCoord k (torusLift N z) c : ℤ) : ZMod (2 * N)) = flipTorus k z c := by
    intro c
    by_cases h : c = k
    · subst h; simp [flipTorus]
    · simp [flipTorus, Function.update_of_ne h, h]
  rw [periodizedCoupling_eq_tsum (J := J) (m := flipCoord k (torusLift N z)) hlift,
    periodizedCoupling]
  have key : ∀ ℓ : Fin d → ℤ, J (flipCoord k (torusLift N z) + (2 * N : ℤ) • ℓ)
      = J (torusLift N z + (2 * N : ℤ) • flipCoord k ℓ) := by
    intro ℓ
    rw [← hflip (torusLift N z + (2 * N : ℤ) • flipCoord k ℓ), flipCoord_add,
      flipCoord_zsmul, flipCoord_flipCoord]
  simp only [key]
  exact Equiv.tsum_eq (flipCoordEquiv k) fun ℓ ↦ J (torusLift N z + (2 * N : ℤ) • ℓ)

end Flip

/-! ### Georgii (17.27): nonnegative definiteness relative to `r_k` -/

section NonnegDefinite

variable {d : ℕ} {k : Fin d} {J : (Fin d → ℤ) → ℝ}

variable (k) in
/-- **Georgii's bounded semicharacters, (17.27)–(17.28)(1).**  The function
`i ↦ x^{i_k - 1} ∏_{c ≠ k} z_c^{i_c}` on `ℕ × ℤ^{d-1}`, with `x ∈ ]-1, 1[` and `z_c` on the unit
circle.  The circle is parametrised by its angle, so the parameter is a pair `p = (x, θ)` and
`z_c^{i_c}` is `exp(i · i_c · θ_c)`; the `k`-th angle is never used. -/
def repCharacter (i : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) : ℂ :=
  (p.1 : ℂ) ^ (i k - 1).toNat *
    Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (p.2 c : ℂ))

lemma continuous_repCharacter (i : Fin d → ℤ) : Continuous (repCharacter k i) := by
  refine Continuous.mul (Continuous.pow (Complex.continuous_ofReal.comp continuous_fst) _)
    (Complex.continuous_exp.comp (continuous_const.mul ?_))
  exact continuous_finsetSum _ fun c _ ↦ continuous_const.mul
    (Complex.continuous_ofReal.comp ((continuous_apply c).comp continuous_snd))

variable (k J) in
/-- **Georgii (17.27).**  An even function `J : ℤ^d → ℝ` is *nonnegative definite relative to
`r_k`* if there is a finite measure `α` on `]-1, 1[ × K^{d-1}` — with `K` the unit circle in `ℂ` —
which *represents* `J`, in that

`J i = ∫ α(dx, dz) x^{i_k - 1} ∏_{c ≠ k} z_c^{i_c}`

for every `i ∈ ℤ^d` with `i_k ≥ 1`.  (Only `i_k ≥ 1` is constrained; the values of `J` on
`i_k = 0` are free, and evenness determines them on `i_k ≤ -1`.)

The circle is parametrised by its angle (see `repCharacter`), so `α` lives on `ℝ × ℝ^d` and is
carried by `|x| < 1`.  This is the same class of representing measures: pushing a measure on
`]-1, 1[ × K^{d-1}` forward along a branch of the argument, and back along `θ ↦ e^{iθ}`, are
inverse operations on the represented functions.

Georgii's Comment (17.28)(1) — that this is equivalent to the nonnegativity of all the sums
`∑_{i,j} z_i z̄_j J(i_1 + j_1 - 1, i_2 - j_2, …)` — is a citation of Berg–Maserick (1984)
combined with the Herglotz lemma, and is not proved in the book; it is not proved here either.
The direction that is used is the one below: a representing measure makes the crossing form of
the reflection nonnegative. -/
def IsNonnegDefiniteAt : Prop :=
  ∃ α : Measure (ℝ × (Fin d → ℝ)), IsFiniteMeasure α ∧ (∀ᵐ p ∂α, |p.1| < 1) ∧
    ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α

/-- The set `{|x| < 1}` carrying a representing measure is measurable. -/
lemma measurableSet_abs_fst_lt_one :
    MeasurableSet {p : ℝ × (Fin d → ℝ) | |p.1| < 1} := by
  have hset : {p : ℝ × (Fin d → ℝ) | |p.1| < 1} = {p | ‖p.1‖ < 1} := by
    ext p; simp [Real.norm_eq_abs]
  rw [hset]
  exact measurableSet_lt measurable_fst.norm measurable_const

/-- **The representing character at the reversed index is the conjugate character.**  Reversing
all transverse indices `i_c`, `c ≠ k`, and keeping `i_k`, conjugates
`x^{i_k-1} ∏_{c ≠ k} z_c^{i_c}`, because `x` is real and `|z_c| = 1`. -/
lemma repCharacter_update_eq_conj (i : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) :
    repCharacter k (Function.update (-i) k (i k)) p
      = (starRingEnd ℂ) (repCharacter k i p) := by
  set S : ℝ := ∑ c ∈ Finset.univ.erase k, (i c : ℝ) * p.2 c with hS
  have hR : ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (p.2 c : ℂ) = ((S : ℝ) : ℂ) := by
    rw [hS, Complex.ofReal_sum]
    push_cast
    rfl
  have hL : ∑ c ∈ Finset.univ.erase k, ((Function.update (-i) k (i k)) c : ℂ) * (p.2 c : ℂ)
      = ((-S : ℝ) : ℂ) := by
    have hterm : ∀ c ∈ Finset.univ.erase k,
        ((Function.update (-i) k (i k)) c : ℂ) * (p.2 c : ℂ)
          = -((i c : ℂ) * (p.2 c : ℂ)) := by
      intro c hc
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hc)]
      simp only [Pi.neg_apply, Int.cast_neg]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, hR, ← Complex.ofReal_neg]
  rw [repCharacter, repCharacter, Function.update_self, hL, hR, map_mul, map_pow,
    Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg]
  ring_nf

/-- **Nonnegative definiteness relative to `r_k` forces invariance under the flip of the `k`-th
coordinate.**  Georgii's proof of (17.29) writes the exponent as `h + h∘r_k + H` with
`h = ½ ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) σ_i·σ_j`; that `h ∘ r_k` is the corresponding sum over
`Λ_{-,k}` is exactly this invariance, which he does not comment on.  It is a genuine consequence
of (17.27) and not of evenness alone: the function on `ℤ^2` supported on `±(1,1)` is even and is
not invariant under flipping the first coordinate. -/
theorem IsNonnegDefiniteAt.flipCoord_eq (hnd : IsNonnegDefiniteAt k J)
    (heven : ∀ m, J (-m) = J m) (m : Fin d → ℤ) : J (flipCoord k m) = J m := by
  obtain ⟨α, hαfin, -, hrep⟩ := hnd
  have main : ∀ i : Fin d → ℤ, 1 ≤ i k → J (flipCoord k i) = J i := by
    intro i hi
    have hupd : -(flipCoord k i) = Function.update (-i) k (i k) := by
      funext c
      by_cases h : c = k
      · subst h; simp [flipCoord]
      · simp [flipCoord, h, Function.update_of_ne h]
    have hk : (Function.update (-i) k (i k)) k = i k := by simp
    have h1 : (J (Function.update (-i) k (i k)) : ℂ) = (starRingEnd ℂ) (J i : ℂ) := by
      rw [hrep _ (by rw [hk]; exact hi), hrep i hi, ← integral_conj]
      exact integral_congr_ae
        (Filter.Eventually.of_forall fun p ↦ repCharacter_update_eq_conj i p)
    have h3 : J (Function.update (-i) k (i k)) = J i := by
      have h2 : (J (Function.update (-i) k (i k)) : ℂ) = (J i : ℂ) := by
        rw [h1, Complex.conj_ofReal]
      exact_mod_cast h2
    rw [← heven (flipCoord k i), hupd, h3]
  rcases lt_trichotomy (m k) 0 with hm | hm | hm
  · have h1 : 1 ≤ (flipCoord k m) k := by simp only [flipCoord_self]; omega
    have := main _ h1
    rwa [flipCoord_flipCoord, eq_comm] at this
  · have : flipCoord k m = m := by
      funext c
      by_cases h : c = k
      · subst h; simp [flipCoord, hm]
      · simp [flipCoord, h]
    rw [this]
  · exact main m (by omega)

/-! ### Georgii, Comments (17.28) -/

/-- **Georgii, Comment (17.28)(3), first part.**  A function that is nonnegative definite relative
to `r_k` is ferromagnetic along the `k`-th axis at odd distances: `J i ≥ 0` whenever `i` is
supported on the `k`-th axis and `i_k` is odd and positive, because the representing character is
then the even power `x^{i_k - 1} ≥ 0`. -/
theorem IsNonnegDefiniteAt.nonneg_of_odd (hnd : IsNonnegDefiniteAt k J) {i : Fin d → ℤ}
    (hi : 1 ≤ i k) (hodd : Odd (i k)) (hax : ∀ c, c ≠ k → i c = 0) : 0 ≤ J i := by
  obtain ⟨α, hαfin, -, hrep⟩ := hnd
  have hchar : ∀ p : ℝ × (Fin d → ℝ),
      repCharacter k i p = ((p.1 ^ (i k - 1).toNat : ℝ) : ℂ) := by
    intro p
    have hz : ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (p.2 c : ℂ) = 0 :=
      Finset.sum_eq_zero fun c hc ↦ by rw [hax c (Finset.ne_of_mem_erase hc)]; simp
    rw [repCharacter, hz]
    simp
  have h : (J i : ℂ) = ((∫ p, p.1 ^ (i k - 1).toNat ∂α : ℝ) : ℂ) := by
    rw [hrep i hi, funext hchar]
    exact integral_complex_ofReal
  have hJ : J i = ∫ p, p.1 ^ (i k - 1).toNat ∂α := by exact_mod_cast h
  obtain ⟨t, ht⟩ := hodd
  have heven : Even (i k - 1).toNat := ⟨t.toNat, by omega⟩
  rw [hJ]
  exact integral_nonneg fun p ↦ heven.pow_nonneg _

/-- **Georgii, Comment (17.28)(3), last part.**  If `J` is nonnegative definite relative to `r_k`
then so is `i ↦ -(-1)^{i_k} J i`; its representing measure is the reflection `x ↦ -x` of the
representing measure of `J`. -/
theorem IsNonnegDefiniteAt.neg_one_zpow (hnd : IsNonnegDefiniteAt k J) :
    IsNonnegDefiniteAt k fun i ↦ -(-1 : ℝ) ^ (i k) * J i := by
  obtain ⟨α, hαfin, hsupp, hrep⟩ := hnd
  set Φ : (ℝ × (Fin d → ℝ)) → (ℝ × (Fin d → ℝ)) := fun p ↦ (-p.1, p.2) with hΦ
  have hΦm : Measurable Φ := (measurable_fst.neg).prodMk measurable_snd
  refine ⟨Measure.map Φ α, inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hΦm.aemeasurable measurableSet_abs_fst_lt_one]
    filter_upwards [hsupp] with p hp
    simpa [hΦ] using hp
  · intro i hi
    have hint : ∫ p, repCharacter k i p ∂(Measure.map Φ α)
        = ∫ p, repCharacter k i (Φ p) ∂α :=
      integral_map hΦm.aemeasurable (continuous_repCharacter i).aestronglyMeasurable
    have hpt : ∀ p, repCharacter k i (Φ p)
        = ((-1 : ℂ)) ^ (i k - 1).toNat * repCharacter k i p := by
      intro p
      rw [repCharacter, repCharacter, hΦ]
      push_cast
      ring
    have hsign : -(-1 : ℝ) ^ (i k) = (-1 : ℝ) ^ ((i k - 1).toNat) := by
      set M := (i k - 1).toNat with hMdef
      have hM : i k = (M : ℤ) + 1 := by omega
      rw [hM, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0) (M : ℤ) 1, zpow_one, zpow_natCast]
      ring
    show ((-(-1 : ℝ) ^ (i k) * J i : ℝ) : ℂ) = _
    rw [hint, funext hpt, integral_const_mul, ← hrep i hi, hsign]
    push_cast
    ring

/-- **Georgii, Comment (17.28)(2).**  A product of two functions that are nonnegative definite
relative to `r_k` is nonnegative definite relative to `r_k`: the representing measure of the
product is the image of the product of the representing measures under
`(x, z, x', z') ↦ (x x', z z')`. -/
theorem IsNonnegDefiniteAt.mul {J' : (Fin d → ℤ) → ℝ} (hJ : IsNonnegDefiniteAt k J)
    (hJ' : IsNonnegDefiniteAt k J') : IsNonnegDefiniteAt k fun i ↦ J i * J' i := by
  obtain ⟨α, hαfin, hα, hrep⟩ := hJ
  obtain ⟨β, hβfin, hβ, hrep'⟩ := hJ'
  set Ψ : (ℝ × (Fin d → ℝ)) × (ℝ × (Fin d → ℝ)) → ℝ × (Fin d → ℝ) :=
    fun q ↦ (q.1.1 * q.2.1, q.1.2 + q.2.2) with hΨ
  have hΨm : Measurable Ψ :=
    ((measurable_fst.comp measurable_fst).mul (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_snd.comp measurable_fst).add (measurable_snd.comp measurable_snd))
  refine ⟨Measure.map Ψ (α.prod β), inferInstance, ?_, ?_⟩
  · rw [ae_map_iff hΨm.aemeasurable measurableSet_abs_fst_lt_one]
    have h1 : ∀ᵐ q ∂(α.prod β), |q.1.1| < 1 := by
      refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
      · exact measurable_fst measurableSet_abs_fst_lt_one
      · filter_upwards [hα] with p hp
        exact Filter.Eventually.of_forall fun _ ↦ hp
    have h2 : ∀ᵐ q ∂(α.prod β), |q.2.1| < 1 := by
      refine (Measure.ae_prod_iff_ae_ae ?_).2 ?_
      · exact measurable_snd measurableSet_abs_fst_lt_one
      · exact Filter.Eventually.of_forall fun _ ↦ hβ
    filter_upwards [h1, h2] with q hq1 hq2
    show |(Ψ q).1| < 1
    rw [hΨ]
    simp only [abs_mul]
    calc |q.1.1| * |q.2.1| ≤ |q.1.1| * 1 := mul_le_mul_of_nonneg_left hq2.le (abs_nonneg _)
      _ < 1 := by simpa using hq1
  · intro i hi
    have hint : ∫ p, repCharacter k i p ∂(Measure.map Ψ (α.prod β))
        = ∫ q, repCharacter k i (Ψ q) ∂(α.prod β) :=
      integral_map hΨm.aemeasurable (continuous_repCharacter i).aestronglyMeasurable
    have hpt : ∀ q, repCharacter k i (Ψ q) = repCharacter k i q.1 * repCharacter k i q.2 := by
      intro q
      have hsum : Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * ((q.1.2 + q.2.2) c : ℂ)
          = Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (q.1.2 c : ℂ)
            + Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (q.2.2 c : ℂ) := by
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun c _ ↦ ?_
        simp only [Pi.add_apply, Complex.ofReal_add]
        ring
      have hexp : Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k,
            (i c : ℂ) * ((q.1.2 + q.2.2) c : ℂ))
          = Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (q.1.2 c : ℂ))
            * Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (q.2.2 c : ℂ)) := by
        rw [← Complex.exp_add, hsum]
      rw [repCharacter, repCharacter, repCharacter, hΨ]
      simp only [Complex.ofReal_mul, mul_pow]
      rw [hexp]
      ring
    show ((J i * J' i : ℝ) : ℂ) = _
    rw [hint, funext hpt, integral_prod_mul, ← hrep i hi, ← hrep' i hi]
    push_cast
    ring

/-! #### Representing measures which are products of a radial and an angular part

All of Georgii's Examples (17.30)–(17.32) exhibit a representing measure of the product form
`α(dx, dz) = ρ(dx) ⊗ σ(dz)`, so that the represented function factorises into a radial moment
sequence and a Fourier coefficient of the angular part. -/

section ProductRepresentation

/-- **A product representing measure.**  If `ρ` is a finite measure on `]-1, 1[` and `σ` a finite
measure on the angles such that

`J i = (∫ x^{i_k - 1} ρ(dx)) · (∫ ∏_{c ≠ k} z_c^{i_c} σ(dz))`  for all `i` with `i_k ≥ 1`,

then `J` is nonnegative definite relative to `r_k`, with representing measure `ρ ⊗ σ`. -/
lemma isNonnegDefiniteAt_of_prod {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ∀ᵐ x ∂ρ, |x| < 1)
    {σ : Measure (Fin d → ℝ)} [IsFiniteMeasure σ]
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k →
      (J i : ℂ) = (∫ x, (x : ℂ) ^ (i k - 1).toNat ∂ρ) *
        ∫ θ, Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (θ c : ℂ)) ∂σ) :
    IsNonnegDefiniteAt k J := by
  refine ⟨ρ.prod σ, inferInstance, ?_, fun i hi ↦ ?_⟩
  · refine (Measure.ae_prod_iff_ae_ae measurableSet_abs_fst_lt_one).2 ?_
    filter_upwards [hρ] with x hx
    exact Filter.Eventually.of_forall fun _ ↦ hx
  · rw [hJ i hi]
    exact (integral_prod_mul (μ := ρ) (ν := σ) (fun x ↦ (x : ℂ) ^ (i k - 1).toNat)
      (fun θ ↦ Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k,
        (i c : ℂ) * (θ c : ℂ)))).symm

/-- The Dirac measure at `0` is a radial measure carried by `]-1, 1[`, and its moments are
`∫ x^m δ_0(dx) = [m = 0]`: it selects the nearest-neighbour distance `i_k = 1`. -/
lemma integral_pow_dirac_zero (m : ℕ) :
    ∫ x, (x : ℂ) ^ m ∂(Measure.dirac (0 : ℝ)) = if m = 0 then 1 else 0 := by
  rw [integral_dirac]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · simp [zero_pow hm.ne', hm.ne']

/-! #### Georgii, Example (17.30): the representing measure of a nearest-neighbour coupling

Georgii's `α = J(e_k) δ_0 × ν^{d-1}`: the Dirac mass at the radial value `0` selects the distance
`i_k = 1` along the `k`-axis, and the Haar measure of the circle in each transverse direction
kills every nonzero transverse frequency. -/

/-- **Georgii, Example (17.30).**  A coupling supported on the nearest-neighbour bonds and
nonnegative on the bond along the `k`-axis is nonnegative definite relative to `r_k`.  Only
`0 ≤ J(e_k)` is needed: the values of `J` on the other nearest-neighbour bonds are irrelevant,
because `i_k ≥ 1` already forces `i = e_k` on the support of `J`. -/
theorem isNonnegDefiniteAt_of_nearestNeighbour
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (hpos : 0 ≤ J (Pi.single k 1)) : IsNonnegDefiniteAt k J := by
  classical
  set ρ : Measure ℝ := ENNReal.ofReal (J (Pi.single k 1)) • Measure.dirac (0 : ℝ) with hρdef
  haveI : IsFiniteMeasure ρ := by
    constructor
    rw [hρdef, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  refine isNonnegDefiniteAt_of_prod (ρ := ρ) ?_ (σ := Measure.pi fun _ : Fin d ↦ angleProbability)
    ?_
  · refine (Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal (J (Pi.single k 1)))
      le_rfl) ?_
    simpa using Filter.Eventually.of_forall (fun x ↦ (by norm_num : |(0 : ℝ)| < 1))
  · intro i hi
    have hrad : ∫ x, (x : ℂ) ^ (i k - 1).toNat ∂ρ
        = (J (Pi.single k 1) : ℂ) * (if (i k - 1).toNat = 0 then 1 else 0) := by
      rw [hρdef, integral_smul_measure, integral_pow_dirac_zero, ENNReal.toReal_ofReal hpos]
      simp [Complex.real_smul]
    rw [hrad, integral_exp_sum_int_mul_I]
    by_cases hsingle : i = Pi.single k 1
    · have h1 : (i k - 1).toNat = 0 := by rw [hsingle]; simp
      have h2 : ∀ c ∈ Finset.univ.erase k, i c = 0 := fun c hc ↦ by
        rw [hsingle, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hc)]
      rw [if_pos h1, if_pos h2, hsingle]
      ring
    · have hzero : J i = 0 := by
        refine hsupp i fun hcard ↦ hsingle ?_
        have hik : 1 ≤ (i k).natAbs := by omega
        have hle : (i k).natAbs ≤ ∑ c, (i c).natAbs :=
          Finset.single_le_sum (f := fun c ↦ (i c).natAbs) (fun c _ ↦ Nat.zero_le _)
            (Finset.mem_univ k)
        have hik1 : (i k).natAbs = 1 := by omega
        have hother : ∀ c, c ≠ k → i c = 0 := by
          intro c hc
          have hsum : (i c).natAbs + (i k).natAbs ≤ ∑ c', (i c').natAbs := by
            have := Finset.add_sum_erase Finset.univ (fun c' ↦ (i c').natAbs) (Finset.mem_univ c)
            have hmem : k ∈ Finset.univ.erase c := Finset.mem_erase.2 ⟨Ne.symm hc, Finset.mem_univ k⟩
            have hle2 : (i k).natAbs ≤ ∑ c' ∈ Finset.univ.erase c, (i c').natAbs :=
              Finset.single_le_sum (f := fun c' ↦ (i c').natAbs) (fun _ _ ↦ Nat.zero_le _) hmem
            omega
          have : (i c).natAbs = 0 := by omega
          omega
        funext c
        by_cases hc : c = k
        · subst hc
          rw [Pi.single_eq_same]
          omega
        · rw [hother c hc, Pi.single_eq_of_ne hc]
      rw [hzero]
      by_cases h1 : (i k - 1).toNat = 0
      · have h2 : ¬ ∀ c ∈ Finset.univ.erase k, i c = 0 := by
          intro hall
          refine hsingle (funext fun c ↦ ?_)
          by_cases hc : c = k
          · subst hc; rw [Pi.single_eq_same]; omega
          · rw [hall c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩), Pi.single_eq_of_ne hc]
        rw [if_neg h2]
        simp
      · rw [if_neg h1]
        simp


/-! #### Georgii, Example (17.32): long range potentials in dimension one

For `d = 1` the transverse directions are absent, so a representing measure is just a finite
measure on `]-1, 1[` whose moments are the values of `J` on `ℕ`.  From
`Γ(a) = ∫_0^∞ e^{-s} s^{a-1} ds` one gets `m^{-a} = Γ(a)^{-1} ∫_0^∞ e^{-ms} s^{a-1} ds` for
`m ≥ 1`, so the representing measure of `J(i) = β |i|^{-a}` is `β` times the image of the gamma
distribution under `s ↦ e^{-s}`, which is carried by `]0, 1[`.

Georgii's case `d = 2` combines this with a Cauchy-kernel identity and Comment (17.28)(2); it is
not formalised here. -/

section LongRange

/-- The gamma weight `e^{-s} s^{a-1} ds` on `]0, ∞[`, a finite measure on `ℝ` of total mass
`Γ(a)`.

This is `Real.Gamma a • ProbabilityTheory.gammaMeasure a 1`; the unnormalised form is used here
because the normalisation cancels against Georgii's `Γ(a)^{-1}` in the moment identity
`integral_pow_map_exp_neg`. -/
noncomputable def gammaWeight (a : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    fun s ↦ (Real.exp (-s) * s ^ (a - 1)).toNNReal

variable {a : ℝ}

lemma measurable_gammaDensity :
    Measurable fun s : ℝ ↦ (Real.exp (-s) * s ^ (a - 1)).toNNReal := by fun_prop

/-- Integration against the gamma weight. -/
lemma integral_gammaWeight (g : ℝ → ℝ) :
    ∫ s, g s ∂(gammaWeight a) = ∫ s in Set.Ioi (0 : ℝ), Real.exp (-s) * s ^ (a - 1) * g s := by
  rw [gammaWeight, integral_withDensity_eq_integral_smul measurable_gammaDensity]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
  have hpos : (0 : ℝ) ≤ Real.exp (-s) * s ^ (a - 1) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ hpos]

lemma isFiniteMeasure_gammaWeight (ha : 0 < a) : IsFiniteMeasure (gammaWeight a) := by
  constructor
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun s : ℝ ↦ Real.exp (-s) * s ^ (a - 1) := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun s hs ↦
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hs) _)
  have h : gammaWeight a Set.univ
      = ∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s) * s ^ (a - 1)) := by
    rw [gammaWeight, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  rw [h, ← ofReal_integral_eq_lintegral_ofReal (Real.GammaIntegral_convergent ha) hnn]
  exact ENNReal.ofReal_lt_top

/-- The image of the gamma weight under `s ↦ e^{-s}` is carried by `]0, 1[`. -/
lemma ae_abs_lt_one_map_exp_neg :
    ∀ᵐ x ∂(Measure.map (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a)), |x| < 1 := by
  have hset : MeasurableSet {x : ℝ | |x| < 1} :=
    measurableSet_lt (by fun_prop : Measurable fun x : ℝ ↦ |x|) measurable_const
  rw [ae_map_iff (by fun_prop : Measurable fun s : ℝ ↦ Real.exp (-s)).aemeasurable hset]
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))), |Real.exp (-s)| < 1 := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs ↦ ?_
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by simpa using hs)
  exact (withDensity_absolutelyContinuous _ _) hae

/-- **Georgii's identity `m^{-a} = Γ(a)^{-1} ∫_0^∞ e^{-ms} s^{a-1} ds`**, as the moment sequence
of the image of the gamma weight under `s ↦ e^{-s}`. -/
lemma integral_pow_map_exp_neg (ha : 0 < a) (m : ℕ) :
    ∫ x, x ^ m ∂(Measure.map (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a))
      = (1 / ((m : ℝ) + 1)) ^ a * Real.Gamma a := by
  rw [integral_map (by fun_prop : Measurable fun s : ℝ ↦ Real.exp (-s)).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ ↦ x ^ m) _), integral_gammaWeight,
    ← Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
  rw [mul_comm (Real.exp (-s)) (s ^ (a - 1)), mul_assoc]
  congr 1
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- **Georgii, Example (17.32) in dimension one.**  A coupling `J` on `ℤ` whose values at the
positive integers are `β m^{-a}`, with `β ≥ 0` and `a > 0`, is nonnegative definite relative to
the unique reflection `r_0`.  (Georgii's hypothesis is `a > d = 1`; that is what makes `J`
absolutely summable, (17.23), and is not needed for the representation itself.) -/
theorem isNonnegDefiniteAt_rpow (ha : 0 < a) {β : ℝ} (hβ : 0 ≤ β)
    {J₁ : (Fin 1 → ℤ) → ℝ} (hJ : ∀ i : Fin 1 → ℤ, 1 ≤ i 0 → J₁ i = β * ((i 0 : ℝ)) ^ (-a)) :
    IsNonnegDefiniteAt (0 : Fin 1) J₁ := by
  classical
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hmeasexp : Measurable fun s : ℝ ↦ Real.exp (-s) := by fun_prop
  have hfin : IsFiniteMeasure (gammaWeight a) := isFiniteMeasure_gammaWeight ha
  have hfinmap : IsFiniteMeasure (Measure.map (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a)) := by
    constructor
    rw [Measure.map_apply hmeasexp MeasurableSet.univ]
    exact measure_lt_top _ _
  set ρ : Measure ℝ := ENNReal.ofReal (β / Real.Gamma a) •
    Measure.map (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a) with hρdef
  have hfinρ : IsFiniteMeasure ρ := by
    constructor
    rw [hρdef, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  refine isNonnegDefiniteAt_of_prod (ρ := ρ) ?_ (σ := Measure.dirac (0 : Fin 1 → ℝ)) ?_
  · exact (Measure.absolutelyContinuous_of_le_smul (μ := Measure.map
      (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a)) le_rfl) ae_abs_lt_one_map_exp_neg
  · intro i hi
    have hipos : (0 : ℝ) < (i 0 : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i 0)
    have hz : (((i 0 - 1).toNat : ℕ) : ℤ) = i 0 - 1 := Int.toNat_of_nonneg (by omega)
    have hm' : (((i 0 - 1).toNat : ℕ) : ℝ) + 1 = (i 0 : ℝ) := by
      have h : (((i 0 - 1).toNat : ℕ) : ℝ) = (i 0 : ℝ) - 1 := by exact_mod_cast hz
      rw [h]; ring
    have hang : ∫ θ : Fin 1 → ℝ,
        Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase (0 : Fin 1), (i c : ℂ) * (θ c : ℂ))
          ∂(Measure.dirac (0 : Fin 1 → ℝ)) = 1 := by
      rw [integral_dirac]
      simp
    have hreal : ∫ x, x ^ (i 0 - 1).toNat ∂ρ = J₁ i := by
      rw [hρdef, integral_smul_measure, integral_pow_map_exp_neg ha,
        ENNReal.toReal_ofReal (div_nonneg hβ hΓ.le), smul_eq_mul, hJ i hi, hm', one_div,
        Real.inv_rpow hipos.le, ← Real.rpow_neg hipos.le]
      field_simp
    have hcast : ∫ x, (x : ℂ) ^ (i 0 - 1).toNat ∂ρ
        = ((∫ x, x ^ (i 0 - 1).toNat ∂ρ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by push_cast; ring)
    rw [hang, mul_one, hcast, hreal]

end LongRange


/-! #### Georgii, Example (17.31): next-nearest neighbour potentials

Georgii's representing measure is `δ_0(dz_k) [a + b ∑_{c ≠ k} (z_c + z̄_c)] ∏_{c ≠ k} ν(dz_c)`.
Its angular part is the Haar measure of the torus weighted by `a + b ∑_{c ≠ k} 2 cos θ_c`, a
nonnegative density exactly when `a ≥ 2(d-1)|b|`; its nonzero Fourier coefficients are the
constant one, worth `a`, and the `±1` coefficients in a single transverse direction, worth `b`. -/

section NextNearest

/-- **The character integral with one cosine factor.**  Replacing one factor of the product of
characters by a cosine-weighted one selects the frequencies `±1` in that direction. -/
lemma integral_cos_mul_exp_sum_int_mul_I {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (m : ι → ℤ) {e : ι} (he : e ∈ s) :
    (∫ θ : ι → ℝ, (2 * Real.cos (θ e) : ℂ) *
        Complex.exp (Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ))
        ∂(Measure.pi fun _ : ι ↦ angleProbability))
      = if (m e = 1 ∨ m e = -1) ∧ ∀ c ∈ s, c ≠ e → m c = 0 then 1 else 0 := by
  classical
  set m' : ι → ℤ := fun c ↦ if c ∈ s then m c else 0 with hm'
  have hexp : ∀ θ : ι → ℝ, Complex.exp (Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ))
      = ∏ c : ι, Complex.exp ((m' c : ℂ) * (θ c : ℂ) * Complex.I) := by
    intro θ
    have hsub : ∑ c ∈ s, ((m' c : ℂ) * (θ c : ℂ) * Complex.I)
        = ∑ c : ι, ((m' c : ℂ) * (θ c : ℂ) * Complex.I) :=
      Finset.sum_subset (Finset.subset_univ s) fun c _ hcs ↦ by simp [hm', hcs]
    have hs : ∑ c ∈ s, ((m' c : ℂ) * (θ c : ℂ) * Complex.I)
        = Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      simp only [hm', if_pos hc]
      ring
    rw [← Complex.exp_sum, ← hsub, hs]
  set g : ι → ℝ → ℂ := fun c x ↦ if c = e then (2 * Real.cos x : ℂ) *
      Complex.exp ((m' c : ℂ) * (x : ℂ) * Complex.I)
    else Complex.exp ((m' c : ℂ) * (x : ℂ) * Complex.I) with hgdef
  have hprod : ∀ θ : ι → ℝ, (2 * Real.cos (θ e) : ℂ) *
      Complex.exp (Complex.I * ∑ c ∈ s, (m c : ℂ) * (θ c : ℂ)) = ∏ c : ι, g c (θ c) := by
    intro θ
    rw [hexp θ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ e),
      ← Finset.mul_prod_erase _ (fun c ↦ g c (θ c)) (Finset.mem_univ e)]
    have hge : g e (θ e) = (2 * Real.cos (θ e) : ℂ)
        * Complex.exp ((m' e : ℂ) * (θ e : ℂ) * Complex.I) := by simp [hgdef]
    have hgc : ∀ c ∈ Finset.univ.erase e, g c (θ c)
        = Complex.exp ((m' c : ℂ) * (θ c : ℂ) * Complex.I) := fun c hc ↦ by
      simp [hgdef, Finset.ne_of_mem_erase hc]
    rw [hge, Finset.prod_congr rfl hgc]
    ring
  simp_rw [hprod]
  rw [integral_fintype_prod_eq_prod g]
  have hge : ∫ x, g e x ∂angleProbability = if m e = 1 ∨ m e = -1 then (1 : ℂ) else 0 := by
    have : ∀ x : ℝ, g e x = (2 * Real.cos x : ℂ)
        * Complex.exp ((m e : ℂ) * (x : ℂ) * Complex.I) := fun x ↦ by
      simp [hgdef, hm', he]
    rw [funext this, integral_cos_mul_exp_int_mul_I]
  have hgc : ∀ c ∈ Finset.univ.erase e,
      ∫ x, g c x ∂angleProbability = if m' c = 0 then (1 : ℂ) else 0 := by
    intro c hc
    have : ∀ x : ℝ, g c x = Complex.exp ((m' c : ℂ) * (x : ℂ) * Complex.I) := fun x ↦ by
      simp [hgdef, Finset.ne_of_mem_erase hc]
    rw [funext this, integral_exp_int_mul_I]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e), hge, Finset.prod_congr rfl hgc]
  by_cases h1 : m e = 1 ∨ m e = -1
  · rw [if_pos h1, one_mul]
    by_cases h2 : ∀ c ∈ s, c ≠ e → m c = 0
    · rw [if_pos ⟨h1, h2⟩]
      refine Finset.prod_eq_one fun c hc ↦ ?_
      have : m' c = 0 := by
        by_cases hcs : c ∈ s
        · simp [hm', hcs, h2 c hcs (Finset.ne_of_mem_erase hc)]
        · simp [hm', hcs]
      simp [this]
    · rw [if_neg (fun h ↦ h2 h.2)]
      push Not at h2
      obtain ⟨c, hcs, hce, hc0⟩ := h2
      refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hce, Finset.mem_univ c⟩) ?_
      have : m' c ≠ 0 := by simp [hm', hcs, hc0]
      simp [this]
  · rw [if_neg h1, if_neg (fun h ↦ h1 h.1), zero_mul]

/-- **Georgii, Example (17.31).**  Let `J` be a next-nearest neighbour coupling: `J(i) = A` when
`|i|² = 1`, `J(i) = B` when `|i|² = 2` and `J(i) = 0` when `|i|² > 2`.  If `A ≥ 2(d-1)|B|` then
`J` is nonnegative definite relative to `r_k`, with Georgii's representing measure
`δ_0(dz_k) [A + B ∑_{c ≠ k}(z_c + z̄_c)] ∏_{c ≠ k} ν(dz_c)`; the hypothesis is exactly what makes
that density nonnegative. -/
theorem isNonnegDefiniteAt_of_nextNearestNeighbour {A B : ℝ}
    (hAB : 2 * ((d : ℝ) - 1) * |B| ≤ A)
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) :
    IsNonnegDefiniteAt k J := by
  classical
  have hd0 : 0 < d := k.pos
  have hcardR : ((Finset.univ.erase k).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hd0]
    simp
  -- the angular density is nonnegative and bounded
  have hbound : ∀ θ : Fin d → ℝ,
      |B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)| ≤ 2 * ((d : ℝ) - 1) * |B| := by
    intro θ
    have habs : |∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)| ≤ 2 * ((d : ℝ) - 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ e ∈ Finset.univ.erase k, |2 * Real.cos (θ e)|
          ≤ ∑ _e ∈ Finset.univ.erase k, (2 : ℝ) := by
            refine Finset.sum_le_sum fun e _ ↦ ?_
            rw [abs_mul, abs_two]
            nlinarith [Real.abs_cos_le_one (θ e), abs_nonneg (Real.cos (θ e))]
        _ = ((Finset.univ.erase k).card : ℝ) * 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = 2 * ((d : ℝ) - 1) := by rw [hcardR]; ring
    rw [abs_mul]
    nlinarith [abs_nonneg B, abs_nonneg (∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e))]
  have hDnn : ∀ θ : Fin d → ℝ,
      0 ≤ A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e) := fun θ ↦ by
    have := abs_le.1 (hbound θ)
    linarith [this.1]
  have hDle : ∀ θ : Fin d → ℝ,
      A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)
        ≤ A + 2 * ((d : ℝ) - 1) * |B| := fun θ ↦ by
    have := abs_le.1 (hbound θ)
    linarith [this.2]
  have hdmeas : Measurable fun θ : Fin d → ℝ ↦
      (A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)).toNNReal := by fun_prop
  set σ : Measure (Fin d → ℝ) := (Measure.pi fun _ : Fin d ↦ angleProbability).withDensity
    fun θ ↦ (A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)).toNNReal with hσdef
  have hfinσ : IsFiniteMeasure σ := by
    constructor
    have hle : σ Set.univ ≤ ENNReal.ofReal (A + 2 * ((d : ℝ) - 1) * |B|) := by
      rw [hσdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      calc ∫⁻ θ, ((A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e)).toNNReal : ℝ≥0∞)
            ∂(Measure.pi fun _ : Fin d ↦ angleProbability)
          ≤ ∫⁻ _θ : Fin d → ℝ, ENNReal.ofReal (A + 2 * ((d : ℝ) - 1) * |B|)
              ∂(Measure.pi fun _ : Fin d ↦ angleProbability) :=
            lintegral_mono fun θ ↦ ENNReal.ofReal_le_ofReal (hDle θ)
        _ = ENNReal.ofReal (A + 2 * ((d : ℝ) - 1) * |B|) := by
            rw [lintegral_const, measure_univ, mul_one]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  -- integration against `σ`
  have hσint : ∀ f : (Fin d → ℝ) → ℂ,
      ∫ θ, f θ ∂σ = ∫ θ, ((A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e) : ℝ) : ℂ) * f θ
        ∂(Measure.pi fun _ : Fin d ↦ angleProbability) := by
    intro f
    rw [hσdef, integral_withDensity_eq_integral_smul hdmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ ↦ ?_)
    show (_ : ℝ≥0) • f θ = _
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hDnn θ), Complex.real_smul]
  -- the two families of bounded integrands
  have hcont : ∀ m : Fin d → ℤ, Continuous fun θ : Fin d → ℝ ↦
      Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ)) := by
    intro m
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact continuous_finsetSum _ fun c _ ↦ continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_apply c))
  have hnorm : ∀ (m : Fin d → ℤ) (θ : Fin d → ℝ),
      ‖Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ))‖ = 1 := by
    intro m θ
    have hsum : ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ)
        = ((∑ c ∈ Finset.univ.erase k, (m c : ℝ) * θ c : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; push_cast; rfl
    rw [hsum, Complex.norm_exp]
    simp
  have hchar : ∀ m : Fin d → ℤ, Integrable (fun θ : Fin d → ℝ ↦
      Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ)))
      (Measure.pi fun _ : Fin d ↦ angleProbability) := by
    intro m
    refine (integrable_const (1 : ℝ)).mono' (hcont m).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ ↦ ?_)
    rw [hnorm m θ]
  have hcoschar : ∀ (m : Fin d → ℤ) (e : Fin d), Integrable (fun θ : Fin d → ℝ ↦
      (2 * Real.cos (θ e) : ℂ) *
        Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ)))
      (Measure.pi fun _ : Fin d ↦ angleProbability) := by
    intro m e
    refine (integrable_const (2 : ℝ)).mono'
      (((continuous_const.mul (Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_apply e)))).mul (hcont m)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun θ ↦ ?_)
    rw [norm_mul, hnorm m θ, mul_one]
    have h2 : (2 * Real.cos (θ e) : ℂ) = ((2 * Real.cos (θ e) : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    nlinarith [Real.abs_cos_le_one (θ e), abs_nonneg (Real.cos (θ e))]
  have hang : ∀ m : Fin d → ℤ,
      ∫ θ, Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ)) ∂σ
        = (A : ℂ) * (if ∀ c ∈ Finset.univ.erase k, m c = 0 then 1 else 0)
          + (B : ℂ) * ∑ e ∈ Finset.univ.erase k,
              (if (m e = 1 ∨ m e = -1) ∧ ∀ c ∈ Finset.univ.erase k, c ≠ e → m c = 0
                then 1 else 0) := by
    intro m
    rw [hσint]
    have hpt : ∀ θ : Fin d → ℝ,
        ((A + B * ∑ e ∈ Finset.univ.erase k, 2 * Real.cos (θ e) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (θ c : ℂ))
          = (A : ℂ) * Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k,
                (m c : ℂ) * (θ c : ℂ))
            + (B : ℂ) * ∑ e ∈ Finset.univ.erase k, ((2 * Real.cos (θ e) : ℂ) *
                Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k,
                  (m c : ℂ) * (θ c : ℂ))) := by
      intro θ
      rw [← Finset.sum_mul, ← mul_assoc]
      push_cast
      ring
    rw [funext hpt, integral_add ((hchar m).const_mul _)
      ((integrable_finset_sum _ fun e _ ↦ hcoschar m e).const_mul _),
      integral_const_mul, integral_const_mul, integral_finsetSum _ fun e _ ↦ hcoschar m e,
      integral_exp_sum_int_mul_I,
      Finset.sum_congr rfl fun e he ↦ integral_cos_mul_exp_sum_int_mul_I
        (Finset.univ.erase k) m he]
    congr!
  -- the representing measure
  have hset : MeasurableSet {x : ℝ | |x| < 1} :=
    measurableSet_lt (by fun_prop : Measurable fun x : ℝ ↦ |x|) measurable_const
  refine isNonnegDefiniteAt_of_prod (ρ := Measure.dirac (0 : ℝ)) ?_ (σ := σ) ?_
  · rw [ae_dirac_iff hset]
    norm_num
  · intro i hi
    have hsqnn : ∀ (T : Finset (Fin d)), ∑ c ∈ T, i c ^ 2 ≤ ∑ c, i c ^ 2 :=
      fun T ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
        fun c _ _ ↦ sq_nonneg _
    rw [integral_pow_dirac_zero, hang i]
    by_cases hik : i k = 1
    · rw [ite_eq_left (show (i k - 1).toNat = 0 by omega), one_mul]
      by_cases hall : ∀ c ∈ Finset.univ.erase k, i c = 0
      · have hi1 : i = Pi.single k 1 := by
          funext c
          by_cases hc : c = k
          · subst hc; rw [hik, Pi.single_eq_same]
          · rw [hall c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩), Pi.single_eq_of_ne hc]
        have hsq : (∑ c, i c ^ 2) = 1 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hik,
            Finset.sum_eq_zero fun c hc ↦ by rw [hall c hc]; ring]
          ring
        have hzero : ∀ e ∈ Finset.univ.erase k,
            (if (i e = 1 ∨ i e = -1) ∧ ∀ c ∈ Finset.univ.erase k, c ≠ e → i c = 0
              then (1 : ℂ) else 0) = 0 := by
          intro e he
          refine ite_eq_right (fun h ↦ ?_)
          have := hall e he
          rcases h.1 with h1 | h1 <;> omega
        rw [hJ1 i hsq, ite_eq_left hall, Finset.sum_congr rfl hzero, Finset.sum_const_zero]
        push_cast
        ring
      · push Not at hall
        obtain ⟨e, he, hne⟩ := hall
        by_cases hone : (i e = 1 ∨ i e = -1) ∧ ∀ c ∈ Finset.univ.erase k, c ≠ e → i c = 0
        · have hsq : (∑ c, i c ^ 2) = 2 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hik,
              ← Finset.add_sum_erase _ _ he,
              Finset.sum_eq_zero fun c hc ↦ by
                rw [hone.2 c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc)]; ring]
            have h1 : i e ^ 2 = 1 := by rcases hone.1 with h | h <;> rw [h] <;> ring
            rw [h1]
            ring
          have hnotall : ¬ ∀ c ∈ Finset.univ.erase k, i c = 0 := fun h ↦ hne (h e he)
          rw [hJ2 i hsq, ite_eq_right hnotall,
            Finset.sum_eq_single e (fun e' he' hne' ↦ ?_) (fun h ↦ absurd he h), ite_eq_left hone]
          · push_cast; ring
          · refine ite_eq_right (fun h ↦ ?_)
            exact hne (h.2 e he (Ne.symm hne'))
        · have hbig : 2 < ∑ c, i c ^ 2 := by
            have hk1 : i k ^ 2 = 1 := by rw [hik]; ring
            have htrans : 2 ≤ ∑ c ∈ Finset.univ.erase k, i c ^ 2 := by
              by_cases h1 : i e = 1 ∨ i e = -1
              · have h2 : ¬ ∀ c ∈ Finset.univ.erase k, c ≠ e → i c = 0 := fun h ↦ hone ⟨h1, h⟩
                push Not at h2
                obtain ⟨c, hc, hce, hc0⟩ := h2
                have hsub : i e ^ 2 + i c ^ 2 ≤ ∑ c' ∈ Finset.univ.erase k, i c' ^ 2 := by
                  rw [← Finset.add_sum_erase _ _ he]
                  have : i c ^ 2 ≤ ∑ c' ∈ (Finset.univ.erase k).erase e, i c' ^ 2 :=
                    Finset.single_le_sum (f := fun c' ↦ i c' ^ 2) (fun _ _ ↦ sq_nonneg _)
                      (Finset.mem_erase.2 ⟨hce, hc⟩)
                  omega
                have h3 : i e ^ 2 = 1 := by rcases h1 with h | h <;> rw [h] <;> ring
                have h4 : 1 ≤ i c ^ 2 := by
                  rcases lt_trichotomy (i c) 0 with h | h | h
                  · nlinarith
                  · exact absurd h hc0
                  · nlinarith
                omega
              · have h2 : 2 ≤ |i e| := by
                  rcases lt_trichotomy (i e) 0 with h | h | h
                  · have : i e ≠ -1 := fun hh ↦ h1 (Or.inr hh)
                    rw [abs_of_neg h]; omega
                  · exact absurd h hne
                  · have : i e ≠ 1 := fun hh ↦ h1 (Or.inl hh)
                    rw [abs_of_pos h]; omega
                have h3 : 4 ≤ i e ^ 2 := by nlinarith [abs_nonneg (i e), sq_abs (i e)]
                have h4 : i e ^ 2 ≤ ∑ c ∈ Finset.univ.erase k, i c ^ 2 :=
                  Finset.single_le_sum (f := fun c ↦ i c ^ 2) (fun _ _ ↦ sq_nonneg _) he
                omega
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk1]
            omega
          have hnotall : ¬ ∀ c ∈ Finset.univ.erase k, i c = 0 := fun h ↦ hne (h e he)
          have hzero : ∀ e' ∈ Finset.univ.erase k,
              (if (i e' = 1 ∨ i e' = -1) ∧ ∀ c ∈ Finset.univ.erase k, c ≠ e' → i c = 0
                then (1 : ℂ) else 0) = 0 := by
            intro e' he'
            refine ite_eq_right (fun h ↦ ?_)
            have hee : e = e' := by
              by_contra hcon
              exact hne (h.2 e he hcon)
            exact hone (hee ▸ h)
          rw [hJ0 i hbig, ite_eq_right hnotall, Finset.sum_congr rfl hzero,
            Finset.sum_const_zero]
          push_cast
          ring
    · have hbig : 2 < ∑ c, i c ^ 2 := by
        have h4 : 4 ≤ i k ^ 2 := by nlinarith [(by omega : (2 : ℤ) ≤ i k)]
        have h5 : i k ^ 2 ≤ ∑ c, i c ^ 2 :=
          Finset.single_le_sum (f := fun c ↦ i c ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ k)
        omega
      rw [hJ0 i hbig, ite_eq_right (show (i k - 1).toNat ≠ 0 by omega)]
      push_cast
      ring

end NextNearest


end ProductRepresentation

end NonnegDefinite

/-! ### The transverse character, and summation along the `k`-direction

Georgii's proof of (17.29) sums the representation (17.27) along the `k`-direction of the
periodisation `J_Λ`.  The transverse part `∏_{c ≠ k} z_c^{m_c}` of the semicharacter is untouched
by that summation, and the `k`-direction contributes two geometric series — Georgii's `k ≥ 0` and
`k < 0` halves, the second obtained from evenness of `J`. -/

section Transverse

variable {d : ℕ} {k : Fin d}

variable (k) in
/-- The transverse part `∏_{c ≠ k} z_c^{m_c}` of the semicharacter `repCharacter`. -/
def transCharacter (m : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) : ℂ :=
  Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (p.2 c : ℂ))

lemma repCharacter_eq_mul (i : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) :
    repCharacter k i p = (p.1 : ℂ) ^ (i k - 1).toNat * transCharacter k i p := rfl

lemma continuous_transCharacter (m : Fin d → ℤ) : Continuous (transCharacter k m) := by
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact continuous_finsetSum _ fun c _ ↦ continuous_const.mul
    (Complex.continuous_ofReal.comp ((continuous_apply c).comp continuous_snd))

@[simp] lemma norm_transCharacter (m : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) :
    ‖transCharacter k m p‖ = 1 := by
  have hre : (Complex.I * ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (p.2 c : ℂ)).re = 0 := by
    have hsum : ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (p.2 c : ℂ)
        = ((∑ c ∈ Finset.univ.erase k, (m c : ℝ) * p.2 c : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; push_cast; rfl
    rw [hsum]
    simp
  rw [transCharacter, Complex.norm_exp, hre, Real.exp_zero]

lemma transCharacter_congr {m m' : Fin d → ℤ} (h : ∀ c, c ≠ k → m c = m' c)
    (p : ℝ × (Fin d → ℝ)) : transCharacter k m p = transCharacter k m' p := by
  rw [transCharacter, transCharacter]
  congr 2
  exact Finset.sum_congr rfl fun c hc ↦ by rw [h c (Finset.ne_of_mem_erase hc)]

@[simp] lemma transCharacter_add_single (m : Fin d → ℤ) (x : ℤ) (p : ℝ × (Fin d → ℝ)) :
    transCharacter k (m + Pi.single k x) p = transCharacter k m p :=
  (transCharacter_congr (fun c hc ↦ by simp [Pi.single_eq_of_ne hc]) p).symm

lemma transCharacter_neg (m : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) :
    transCharacter k (-m) p = (starRingEnd ℂ) (transCharacter k m p) := by
  have hsum : ∑ c ∈ Finset.univ.erase k, ((-m) c : ℂ) * (p.2 c : ℂ)
      = -((∑ c ∈ Finset.univ.erase k, (m c : ℝ) * p.2 c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [Pi.neg_apply, Int.cast_neg]
    push_cast
    ring
  have hsum' : ∑ c ∈ Finset.univ.erase k, (m c : ℂ) * (p.2 c : ℂ)
      = ((∑ c ∈ Finset.univ.erase k, (m c : ℝ) * p.2 c : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]; push_cast; rfl
  rw [transCharacter, transCharacter, hsum, hsum', ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring_nf

lemma transCharacter_add (m m' : Fin d → ℤ) (p : ℝ × (Fin d → ℝ)) :
    transCharacter k (m + m') p = transCharacter k m p * transCharacter k m' p := by
  rw [transCharacter, transCharacter, transCharacter, ← Complex.exp_add, ← mul_add,
    ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Pi.add_apply, Int.cast_add]
  ring

end Transverse

/-! ### Georgii (17.24): the Gibbs distribution of a Heisenberg potential, and its splitting -/

section Heisenberg

variable {d N n : ℕ} [NeZero N] {J : (Fin d → ℤ) → ℝ} {k : Fin d}

variable (N k) in
/-- Georgii's positive half `Λ_{+,k}` as a `Finset`. -/
def torusPosAtFinset : Finset (Fin d → ZMod (2 * N)) :=
  Finset.univ.filter fun i ↦ (i k).val < N

@[simp] lemma mem_torusPosAtFinset {i : Fin d → ZMod (2 * N)} :
    i ∈ torusPosAtFinset N k ↔ (i k).val < N := by
  simp [torusPosAtFinset]

variable (N n J) in
/-- **Georgii (17.24), the exponent.**  `½ ∑_{i, j ∈ Λ} J_Λ(i - j) σ_i · σ_j`, the negative of the
Hamiltonian in the torus `Λ` with periodic boundary condition for the Heisenberg potential
(17.22).  The diagonal terms `i = j` are included, as in Georgii; they contribute the self-energy
`½ J_Λ(0) |σ_i|²` coming from the translates of a site other than itself. -/
def heisenbergExponent (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  (∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)) / 2

/-- **Georgii (17.24): what the diagonal of the double sum is.**  The exponent of (17.24) is the
sum of the periodised pair interactions `J_Λ(i-j) σ_i · σ_j` over ordered pairs of *distinct*
torus sites, halved, plus the self-energy `½ J_Λ(0) |σ_i|²` of each site interacting with its own
translates.  So (17.24) is minus the energy of the configuration in the torus for the Heisenberg
potential (17.22), the diagonal accounting exactly for the interaction of a site with its
translates. -/
theorem heisenbergExponent_eq_offDiag_add_diag (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergExponent N n J ω
      = (∑ i, ∑ j ∈ Finset.univ.erase i, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)) / 2
        + (∑ i, periodizedCoupling N J 0 * (ω i ⬝ᵥ ω i)) / 2 := by
  classical
  rw [heisenbergExponent, ← add_div, ← Finset.sum_add_distrib]
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i), sub_self]

variable (N n J k) in
/-- Georgii's `h` in the proof of (17.29): the part of the exponent (17.24) carried by the
positive half `Λ_{+,k}`. -/
def heisenbergHalf (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
    periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)) / 2

variable (N J k) in
/-- **The crossing matrix** `M(i, j) = J_Λ(r_k i - j)` of the reflection `r_k`, indexed by the
torus and extended by zero off `Λ_{+,k} × Λ_{+,k}`.  Georgii's `H`, the part of the exponent that
couples the two halves of the torus, is `∑_{i, j} M(i, j) σ_{r_k i} · σ_j`
(`heisenbergExponent_eq_add`), and `r_k`-positivity of `°γ_Λ^Φ` follows as soon as `M` is
positive semidefinite (`isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef`). -/
def crossingMatrix : Matrix (Fin d → ZMod (2 * N)) (Fin d → ZMod (2 * N)) ℝ :=
  fun i j ↦ if (i k).val < N ∧ (j k).val < N then
    periodizedCoupling N J (torusReflAt N k i - j) else 0

lemma crossingMatrix_of_mem {i j : Fin d → ZMod (2 * N)} (hi : (i k).val < N)
    (hj : (j k).val < N) :
    crossingMatrix N J k i j = periodizedCoupling N J (torusReflAt N k i - j) := by
  simp [crossingMatrix, hi, hj]

lemma crossingMatrix_eq_zero {i j : Fin d → ZMod (2 * N)} (h : ¬ ((i k).val < N ∧ (j k).val < N)) :
    crossingMatrix N J k i j = 0 := by
  simp [crossingMatrix, h]

/-- The reflection `r_k` turns the difference of two sites into its `k`-th coordinate flip. -/
lemma torusReflAt_sub_torusReflAt (i j : Fin d → ZMod (2 * N)) :
    torusReflAt N k i - torusReflAt N k j = flipTorus k (i - j) := by
  funext c
  by_cases h : c = k
  · subst h
    simp only [Pi.sub_apply, torusReflAt_apply_self, flipTorus, Function.update_self]
    ring
  · simp only [Pi.sub_apply, torusReflAt_apply_of_ne h, flipTorus, Function.update_of_ne h]

/-- `J_Λ` is invariant under `i - j ↦ r_k i - r_k j` when `J` is flip invariant: this is what
makes the two halves of the periodic Hamiltonian mirror images of one another. -/
lemma periodizedCoupling_torusReflAt_sub (hflip : ∀ m, J (flipCoord k m) = J m)
    (i j : Fin d → ZMod (2 * N)) :
    periodizedCoupling N J (torusReflAt N k i - torusReflAt N k j)
      = periodizedCoupling N J (i - j) := by
  rw [torusReflAt_sub_torusReflAt, periodizedCoupling_flipTorus hflip]

lemma periodizedCoupling_sub_comm (heven : ∀ m, J (-m) = J m) (i j : Fin d → ZMod (2 * N)) :
    periodizedCoupling N J (j - i) = periodizedCoupling N J (i - j) := by
  rw [show j - i = -(i - j) by ring, periodizedCoupling_neg heven]

/-- **Georgii, proof of (17.29): the splitting of the exponent.**  The exponent (17.24) is
`h + h ∘ r_k + H`, where `h` is the part carried by the positive half and
`H = ∑_{i, j} M(i, j) σ_{r_k i} · σ_j` is the interaction across the plane of the reflection. -/
theorem heisenbergExponent_eq_add (heven : ∀ m, J (-m) = J m)
    (hflip : ∀ m, J (flipCoord k m) = J m)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergExponent N n J ω
      = heisenbergHalf N n J k ω + heisenbergHalf N n J k (ω ∘ torusReflAt N k)
        + ∑ i, ∑ j, crossingMatrix N J k i j * (ω (torusReflAt N k i) ⬝ᵥ ω j) := by
  classical
  set r := torusReflAt N k with hr
  set F : (Fin d → ZMod (2 * N)) → (Fin d → ZMod (2 * N)) → ℝ :=
    fun i j ↦ periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) with hF
  have hFapply : ∀ i j, F i j = periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) := fun _ _ ↦ rfl
  have hFsymm : ∀ i j, F i j = F j i := by
    intro i j
    rw [hFapply, hFapply, periodizedCoupling_sub_comm heven j i, dotProduct_comm]
  set P : Finset (Fin d → ZMod (2 * N)) := Finset.univ.filter fun i ↦ (i k).val < N with hP
  set Q : Finset (Fin d → ZMod (2 * N)) := Finset.univ.filter fun i ↦ ¬ ((i k).val < N) with hQ
  have hE : heisenbergExponent N n J ω = (∑ i, ∑ j, F i j) / 2 := rfl
  have hh1 : heisenbergHalf N n J k ω = (∑ i ∈ P, ∑ j ∈ P, F i j) / 2 := rfl
  have hh2 : heisenbergHalf N n J k (ω ∘ r)
      = (∑ i ∈ P, ∑ j ∈ P,
          periodizedCoupling N J (i - j) * ((ω ∘ r) i ⬝ᵥ (ω ∘ r) j)) / 2 := rfl
  -- the four blocks
  have hsplit : ∀ f : (Fin d → ZMod (2 * N)) → ℝ, ∑ i, f i = (∑ i ∈ P, f i) + ∑ i ∈ Q, f i :=
    fun f ↦ (Finset.sum_filter_add_sum_filter_not Finset.univ _ f).symm
  have hblocks : ∑ i, ∑ j, F i j
      = ((∑ i ∈ P, ∑ j ∈ P, F i j) + ∑ i ∈ Q, ∑ j ∈ P, F i j)
        + ((∑ i ∈ P, ∑ j ∈ Q, F i j) + ∑ i ∈ Q, ∑ j ∈ Q, F i j) := by
    rw [Finset.sum_congr rfl fun i _ ↦ hsplit (F i), Finset.sum_add_distrib,
      hsplit fun i ↦ ∑ j ∈ P, F i j, hsplit fun i ↦ ∑ j ∈ Q, F i j]
  -- the reflection is a bijection from the positive to the negative half
  have hPQ : ∀ i : Fin d → ZMod (2 * N), i ∈ P ↔ r i ∈ Q := by
    intro i
    simp only [hP, hQ, Finset.mem_filter, Finset.mem_univ, true_and, hr]
    have h := torusPosAt_iff_torusReflAt_notMem (k := k) (i := i)
    simpa only [mem_torusPosAt] using h
  have hQsum : ∀ f : (Fin d → ZMod (2 * N)) → ℝ, ∑ i ∈ Q, f i = ∑ i ∈ P, f (r i) :=
    fun f ↦ (Finset.sum_equiv r hPQ fun i _ ↦ rfl).symm
  have hQQ : ∑ i ∈ Q, ∑ j ∈ Q, F i j = ∑ i ∈ P, ∑ j ∈ P, F (r i) (r j) := by
    rw [hQsum fun i ↦ ∑ j ∈ Q, F i j]
    exact Finset.sum_congr rfl fun i _ ↦ hQsum fun j ↦ F (r i) j
  have hQP : ∑ i ∈ Q, ∑ j ∈ P, F i j = ∑ i ∈ P, ∑ j ∈ Q, F i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hFsymm j i
  -- the reflected half is `h ∘ r_k`
  have hhalfr : ∑ i ∈ P, ∑ j ∈ P, F (r i) (r j)
      = ∑ i ∈ P, ∑ j ∈ P, periodizedCoupling N J (i - j) * ((ω ∘ r) i ⬝ᵥ (ω ∘ r) j) := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hFapply]
    simp only [Function.comp_apply, hr]
    rw [periodizedCoupling_torusReflAt_sub hflip]
  -- the crossing block
  have hcross : ∑ i, ∑ j, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j)
      = ∑ i ∈ Q, ∑ j ∈ P, F i j := by
    have h1 : ∑ i, ∑ j, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j)
        = ∑ i ∈ P, ∑ j ∈ P, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j) := by
      rw [hsplit fun i ↦ ∑ j, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j)]
      have hz : ∑ i ∈ Q, ∑ j, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j) = 0 := by
        refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun j _ ↦ ?_
        rw [hQ, Finset.mem_filter] at hi
        rw [crossingMatrix_eq_zero (fun h ↦ hi.2 h.1), zero_mul]
      rw [hz, add_zero]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hsplit fun j ↦ crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j)]
      have hz' : ∑ j ∈ Q, crossingMatrix N J k i j * (ω (r i) ⬝ᵥ ω j) = 0 := by
        refine Finset.sum_eq_zero fun j hj ↦ ?_
        rw [hQ, Finset.mem_filter] at hj
        rw [crossingMatrix_eq_zero (fun h ↦ hj.2 h.2), zero_mul]
      rw [hz', add_zero]
    rw [h1, hQsum fun i ↦ ∑ j ∈ P, F i j]
    refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
    rw [hP, Finset.mem_filter] at hi hj
    rw [crossingMatrix_of_mem hi.2 hj.2, hFapply, hr]
  rw [hE, hh1, hh2, hblocks, ← hQP, hQQ, hhalfr, hcross]
  ring

/-! ### The crossing index: the canonical lift of `r_k i - j` -/

variable (N k) in
/-- The canonical lift of `r_k i - j` to `ℤ^d` for two sites `i, j` of the positive half: its
`k`-th coordinate is `2N - 1 - i_k - j_k`, which is Georgii's `u + u' - 1` and lies in
`{1, …, 2N - 1}`, and its transverse coordinates are the differences of the canonical lifts. -/
def crossingIndex (i j : Fin d → ZMod (2 * N)) : Fin d → ℤ :=
  fun c ↦ if c = k then (2 * N : ℤ) - 1 - ((i k).val : ℤ) - ((j k).val : ℤ)
    else ((i c).val : ℤ) - ((j c).val : ℤ)

@[simp] lemma crossingIndex_self (i j : Fin d → ZMod (2 * N)) :
    crossingIndex N k i j k = (2 * N : ℤ) - 1 - ((i k).val : ℤ) - ((j k).val : ℤ) := by
  simp [crossingIndex]

@[simp] lemma crossingIndex_of_ne {c : Fin d} (h : c ≠ k) (i j : Fin d → ZMod (2 * N)) :
    crossingIndex N k i j c = ((i c).val : ℤ) - ((j c).val : ℤ) := by
  simp [crossingIndex, h]

lemma crossingIndex_cast (i j : Fin d → ZMod (2 * N)) (c : Fin d) :
    ((crossingIndex N k i j c : ℤ) : ZMod (2 * N)) = (torusReflAt N k i - j) c := by
  by_cases h : c = k
  · subst h
    rw [crossingIndex_self]
    push_cast
    have h2N : ((N : ZMod (2 * N)) * 2) = 0 := by
      have h := ZMod.natCast_self (2 * N)
      push_cast at h
      linear_combination h
    simp only [Pi.sub_apply, torusReflAt_apply_self, ZMod.natCast_val, ZMod.cast_id]
    linear_combination h2N
  · rw [crossingIndex_of_ne h]
    push_cast
    simp only [Pi.sub_apply, torusReflAt_apply_of_ne h, ZMod.natCast_val, ZMod.cast_id]

lemma crossingMatrix_eq_tsum {i j : Fin d → ZMod (2 * N)} (hi : (i k).val < N)
    (hj : (j k).val < N) :
    crossingMatrix N J k i j = ∑' ℓ : Fin d → ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • ℓ) := by
  rw [crossingMatrix_of_mem hi hj]
  exact periodizedCoupling_eq_tsum (crossingIndex_cast i j)

lemma one_le_crossingIndex_self {i j : Fin d → ZMod (2 * N)} (hi : (i k).val < N)
    (hj : (j k).val < N) : 1 ≤ crossingIndex N k i j k := by
  rw [crossingIndex_self]
  have h1 : ((i k).val : ℤ) < (N : ℤ) := by exact_mod_cast hi
  have h2 : ((j k).val : ℤ) < (N : ℤ) := by exact_mod_cast hj
  linarith

lemma crossingIndex_self_le (i j : Fin d → ZMod (2 * N)) :
    crossingIndex N k i j k ≤ (2 * N : ℤ) - 1 := by
  rw [crossingIndex_self]
  have h1 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  have h2 : (0 : ℤ) ≤ ((j k).val : ℤ) := Int.natCast_nonneg _
  linarith

lemma abs_crossingIndex_of_ne_lt {c : Fin d} (h : c ≠ k) (i j : Fin d → ZMod (2 * N)) :
    |crossingIndex N k i j c| < (2 * N : ℤ) := by
  rw [crossingIndex_of_ne h]
  have h1 : ((i c).val : ℤ) < (2 * N : ℤ) := by exact_mod_cast ZMod.val_lt (i c)
  have h2 : ((j c).val : ℤ) < (2 * N : ℤ) := by exact_mod_cast ZMod.val_lt (j c)
  have h3 : (0 : ℤ) ≤ ((i c).val : ℤ) := Int.natCast_nonneg _
  have h4 : (0 : ℤ) ≤ ((j c).val : ℤ) := Int.natCast_nonneg _
  rw [abs_lt]
  constructor <;> linarith

/-- Two sites of the positive half with the same canonical lifts are equal. -/
lemma eq_of_crossingIndex_eq_zero {i j : Fin d → ZMod (2 * N)}
    (h : ∀ c, c ≠ k → (i c).val = (j c).val) (hk : (i k).val = (j k).val) : i = j := by
  funext c
  by_cases hc : c = k
  · subst hc; exact ZMod.val_injective _ hk
  · exact ZMod.val_injective _ (h c hc)

/-! ### The Gibbs distribution (17.24) and its `r_k`-positivity from a positive semidefinite
crossing matrix -/

variable (N n J) in
/-- **Georgii (17.24).**  The Gibbs distribution in the torus `Λ` with periodic boundary
condition for the Heisenberg potential (17.22), *before* normalisation: the measure with density
`exp[½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i · σ_j]` relative to `λ^Λ`.  Georgii's `°Z_Λ^Φ` is its total mass,
assumed finite. -/
def heisenbergPeriodicGibbs (ν : Measure (Fin n → ℝ)) :
    Measure ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :=
  (Measure.pi fun _ ↦ ν).withDensity fun ω ↦
    ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))

variable (N n J) in
/-- Georgii's `°γ_Λ^Φ` for a Heisenberg potential: the normalisation of (17.24). -/
def heisenbergPeriodicGibbsDist (ν : Measure (Fin n → ℝ)) :
    Measure ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :=
  (heisenbergPeriodicGibbs N n J ν univ)⁻¹ • heisenbergPeriodicGibbs N n J ν

omit [NeZero N] in
lemma measurable_torusSpinApply (i : Fin d → ZMod (2 * N)) (c : Fin n) :
    Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ ω i c :=
  (measurable_pi_apply c).comp (measurable_pi_apply i)

lemma measurable_dotProduct_apply (i j : Fin d → ZMod (2 * N)) :
    Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦ (ω i ⬝ᵥ ω j) := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun c _ ↦ (measurable_torusSpinApply i c).mul (measurable_torusSpinApply j c)

lemma measurable_heisenbergExponent :
    Measurable (heisenbergExponent N n J (d := d)) :=
  (Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (measurable_dotProduct_apply i j).const_mul _).div_const _

lemma measurable_heisenbergHalf :
    Measurable (heisenbergHalf N n J k (d := d)) :=
  (Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (measurable_dotProduct_apply i j).const_mul _).div_const _

lemma dependsOn_heisenbergHalf :
    DependsOn (heisenbergHalf N n J k (d := d)) (torusPosAt N k) := by
  intro ω ω' h
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_)
  rw [mem_torusPosAtFinset] at hi hj
  rw [h i (mem_torusPosAt.2 hi), h j (mem_torusPosAt.2 hj)]

/-- **`r_k`-positivity of the Heisenberg periodic Gibbs distribution from a positive semidefinite
crossing matrix.**  The exponent (17.24) splits as `h + h∘r_k + ∑_{i,j} M(i,j) σ_{r_k i}·σ_j`
(`heisenbergExponent_eq_add`); when `M = Bᵀ B` the crossing part is
`∑_{a, c} g_{a,c} · g_{a,c}∘r_k` with `g_{a,c}(σ) = ∑_j B(a,j) (σ_j)_c`, and Lemma (17.26) in its
finite-sum form applies.  The `g_{a,c}` are linear in the spins and hence unbounded, which is why
`isReflectionPositive_siteEquiv_withDensity_sum` is stated with a dominating function and an
integrability hypothesis — Georgii's `°Z_Λ^Φ < ∞`. -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef
    (heven : ∀ m, J (-m) = J m) (hflip : ∀ m, J (flipCoord k m) = J m)
    (hpsd : (crossingMatrix N J k).PosSemidef)
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) := by
  classical
  obtain ⟨B, hB⟩ := hpsd.exists_sum_mul
  -- `B` has no columns outside the positive half, because `M` vanishes there
  have hB0 : ∀ (a j : Fin d → ZMod (2 * N)), ¬ ((j k).val < N) → B a j = 0 := by
    intro a j hj
    have h : ∑ a' : Fin d → ZMod (2 * N), B a' j * B a' j = 0 := by
      rw [← hB j j]
      exact crossingMatrix_eq_zero fun h ↦ hj h.1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun a' _ ↦ mul_self_nonneg (B a' j)).1 h a
      (Finset.mem_univ a)
    exact mul_self_eq_zero.1 this
  set g : ((Fin d → ZMod (2 * N)) × Fin n) → ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ :=
    fun w ω ↦ ∑ j, B w.1 j * ω j w.2 with hg
  have hgm : ∀ w, Measurable (g w) := fun w ↦
    Finset.measurable_sum _ fun j _ ↦ (measurable_torusSpinApply j w.2).const_mul _
  have hgdep : ∀ w, DependsOn (g w) (torusPosAt N k) := by
    intro w ω ω' hωω'
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hj : (j k).val < N
    · rw [hωω' j (mem_torusPosAt.2 hj)]
    · rw [hB0 _ _ hj, zero_mul, zero_mul]
  -- the crossing part of the exponent is the sum of the squares `g_w · g_w ∘ r_k`
  set T : ((Fin d → ZMod (2 * N)) × Fin n) → (Fin d → ZMod (2 * N)) → (Fin d → ZMod (2 * N)) →
      ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ :=
    fun w i j ω ↦ (B w.1 i * ω (torusReflAt N k i) w.2) * (B w.1 j * ω j w.2) with hT
  have hcross : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
      ∑ w, g w ω * g w (ω ∘ torusReflAt N k)
        = ∑ i, ∑ j, crossingMatrix N J k i j * (ω (torusReflAt N k i) ⬝ᵥ ω j) := by
    intro ω
    have step1 : ∀ w, g w ω * g w (ω ∘ torusReflAt N k) = ∑ i, ∑ j, T w i j ω := by
      intro w
      rw [hg, hT]
      simp only [Function.comp_apply]
      rw [mul_comm]
      exact Finset.sum_mul_sum Finset.univ Finset.univ
        (fun i ↦ B w.1 i * ω (torusReflAt N k i) w.2) (fun j ↦ B w.1 j * ω j w.2)
    have step4 : ∀ i j, ∑ w, T w i j ω
        = crossingMatrix N J k i j * (ω (torusReflAt N k i) ⬝ᵥ ω j) := by
      intro i j
      rw [hT, hB i j, dotProduct, Fintype.sum_prod_type]
      simp only []
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
    calc ∑ w, g w ω * g w (ω ∘ torusReflAt N k)
        = ∑ w, ∑ i, ∑ j, T w i j ω := Finset.sum_congr rfl fun w _ ↦ step1 w
      _ = ∑ i, ∑ w, ∑ j, T w i j ω := Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ w, T w i j ω :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
      _ = ∑ i, ∑ j, crossingMatrix N J k i j * (ω (torusReflAt N k i) ⬝ᵥ ω j) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ step4 i j
  -- a measurable dominating function for `h` and the `g_w`
  set φ : ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ :=
    fun ω ↦ |heisenbergHalf N n J k ω| + ∑ w, |g w ω| with hφ
  have habs : ∀ f : ((Fin d → ZMod (2 * N)) → (Fin n → ℝ)) → ℝ, Measurable f →
      Measurable fun ω ↦ |f ω| := fun f hf ↦ by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hφm : Measurable φ :=
    (habs _ measurable_heisenbergHalf).add
      (Finset.measurable_sum _ fun w _ ↦ habs _ (hgm w))
  have hφdep : DependsOn φ (torusPosAt N k) := by
    intro ω ω' hωω'
    rw [hφ]
    simp only []
    rw [dependsOn_heisenbergHalf hωω']
    exact congrArg _ (Finset.sum_congr rfl fun w _ ↦ congrArg _ (hgdep w hωω'))
  have hgsum : ∀ ω, (0 : ℝ) ≤ ∑ w, |g w ω| :=
    fun ω ↦ Finset.sum_nonneg fun w _ ↦ abs_nonneg _
  have hhφ : ∀ ω, |heisenbergHalf N n J k ω| ≤ φ ω := fun ω ↦ by
    rw [hφ]; simpa using hgsum ω
  have hgφ : ∀ w ω, |g w ω| ≤ φ ω := by
    intro w ω
    rw [hφ]
    have h1 : |g w ω| ≤ ∑ w', |g w' ω| :=
      Finset.single_le_sum (f := fun w' ↦ |g w' ω|) (fun w' _ ↦ abs_nonneg _) (Finset.mem_univ w)
    have h2 : (0 : ℝ) ≤ |heisenbergHalf N n J k ω| := abs_nonneg _
    linarith
  -- rewrite the density in the form of (17.26)
  have hdensity : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ),
      Real.exp (heisenbergExponent N n J ω)
        = Real.exp (heisenbergHalf N n J k ω
            + heisenbergHalf N n J k (ω ∘ torusReflAt N k)
            + ∑ w, g w ω * g w (ω ∘ torusReflAt N k)) := by
    intro ω
    rw [heisenbergExponent_eq_add heven hflip ω, hcross ω]
  rw [heisenbergPeriodicGibbs]
  simp only [hdensity]
  refine isReflectionPositive_siteEquiv_withDensity_sum ν k hφm hφdep measurable_heisenbergHalf
    dependsOn_heisenbergHalf hhφ hgm hgdep hgφ ?_
  simpa only [← hdensity] using hint

/-! ### Georgii, Theorem (17.29): a representing measure makes the crossing matrix positive
semidefinite

Georgii's proof of (17.29) substitutes the representation (17.27) into
`M(i, j) = J_Λ(r_k i - j) = ∑_{ℓ ∈ ℤ^d} J(crossingIndex(i, j) + 2Nℓ)` and sums the `k`-direction
of the periodisation as two geometric series — his `k ≥ 0` and `k < 0` halves, the second obtained
from the evenness of `J`.  The transverse directions cannot be summed term by term, because
`∑_s z^{2Ns}` diverges; Georgii regularises them by the Cesàro average `J_{Λ,L}` over
`-L ≤ ℓ, ℓ' ≤ L`, which replaces `∑_{ℓ, ℓ'} z^{2N(ℓ - ℓ')}` by `|∑_ℓ z^{2Nℓ}|²`, and then lets
`L → ∞`.  Here that limit is taken at the level of the crossing matrix, where it is the closedness
of the quadratic form condition, rather than at the level of the measures `μ_{Λ,L}` (where
Georgii needs convergence in variational distance). -/

section NonnegDefiniteCrossing

variable (k) in
/-- The lift of a `k`-index `t` and a transverse index `s ∈ ℤ^{d-1}` to `ℤ^d`.

This is `(Equiv.funSplitAt k ℤ).symm (t, s)`; it is spelled out because Mathlib's `Equiv.piSplitAt`
is stated for a dependent family, so its `invFun` carries an `Eq.rec` which blocks the `rfl` proofs
of `splitIndex_self` and `splitIndex_of_ne`. -/
def splitIndex (t : ℤ) (s : {c : Fin d // c ≠ k} → ℤ) : Fin d → ℤ :=
  fun c ↦ if h : c = k then t else s ⟨c, h⟩

variable (k) in
/-- Splitting off the `k`-th coordinate identifies `ℤ^{d-1} × ℤ` with `ℤ^d`. -/
def splitIndexEquiv : (({c : Fin d // c ≠ k} → ℤ) × ℤ) ≃ (Fin d → ℤ) where
  toFun q := splitIndex k q.2 q.1
  invFun m := (fun c ↦ m c, m k)
  left_inv q := by
    refine Prod.ext ?_ ?_
    · funext c
      simp only [splitIndex, dif_neg c.2, Subtype.coe_eta]
    · simp [splitIndex]
  right_inv m := by
    funext c
    by_cases h : c = k
    · subst h; simp [splitIndex]
    · simp [splitIndex, h]

omit [NeZero N] in
@[simp] lemma splitIndexEquiv_apply (q : ({c : Fin d // c ≠ k} → ℤ) × ℤ) :
    splitIndexEquiv k q = splitIndex k q.2 q.1 := rfl

omit [NeZero N] in
@[simp] lemma splitIndex_self (t : ℤ) (s : {c : Fin d // c ≠ k} → ℤ) :
    splitIndex k t s k = t := by simp [splitIndex]

omit [NeZero N] in
@[simp] lemma splitIndex_of_ne {c : Fin d} (h : c ≠ k) (t : ℤ)
    (s : {c : Fin d // c ≠ k} → ℤ) : splitIndex k t s c = s ⟨c, h⟩ := by
  simp [splitIndex, h]

omit [NeZero N] in
/-- Reindexing a sum over `ℤ^d` by the splitting of the `k`-th coordinate. -/
lemma tsum_splitIndex {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (f : (Fin d → ℤ) → M) :
    ∑' m : Fin d → ℤ, f m
      = ∑' q : ({c : Fin d // c ≠ k} → ℤ) × ℤ, f (splitIndex k q.2 q.1) :=
  ((splitIndexEquiv k).tsum_eq f).symm

/-! #### The moments of a representing measure along the `k`-axis

Georgii's justification for interchanging the summation over the `k`-direction with the
integration over `α` is that `∑_{t ≥ 0} ∫ α(dx, dz) x^{2Nt} = ∑_{t ≥ 0} J(1 + 2Nt, 0, …, 0)`,
which is finite by (17.23).  The same estimate makes the resolvent `(1 - x^{2N})⁻¹` integrable. -/

section Moments

variable {α : Measure (ℝ × (Fin d → ℝ))}

omit [NeZero N] in
/-- The representing character of the axis index `(1 + 2Nt) e_k` is the even power `x^{2Nt}`. -/
lemma repCharacter_single (t : ℕ) (p : ℝ × (Fin d → ℝ)) :
    repCharacter k (Pi.single k (1 + 2 * (N : ℤ) * t)) p = ((p.1 ^ (2 * N * t) : ℝ) : ℂ) := by
  have hz : ∑ c ∈ Finset.univ.erase k,
      ((Pi.single k (1 + 2 * (N : ℤ) * t) : Fin d → ℤ) c : ℂ) * (p.2 c : ℂ) = 0 := by
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hc)]
    simp
  have hcast : (1 + 2 * (N : ℤ) * t - 1) = ((2 * N * t : ℕ) : ℤ) := by push_cast; ring
  have hk : ((Pi.single k (1 + 2 * (N : ℤ) * t) : Fin d → ℤ) k - 1).toNat = 2 * N * t := by
    rw [Pi.single_eq_same, hcast, Int.toNat_natCast]
  rw [repCharacter, hz, hk]
  push_cast
  simp

omit [NeZero N] in
/-- Integrability of a power of the first coordinate, from `|x| < 1` and finiteness of `α`. -/
lemma integrable_pow_fst [IsFiniteMeasure α] (hα : ∀ᵐ p ∂α, |p.1| < 1) (m : ℕ) :
    Integrable (fun p : ℝ × (Fin d → ℝ) ↦ p.1 ^ m) α := by
  refine ⟨(measurable_fst.pow_const m).aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_const (1 : ℝ)).mono ?_
  filter_upwards [hα] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_one]
  exact pow_le_one₀ (abs_nonneg _) hp.le

omit [NeZero N] in
/-- **The even moments of a representing measure are values of `J` on the `k`-axis.** -/
lemma integral_pow_fst
    (hrep : ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α) (t : ℕ) :
    ∫ p, p.1 ^ (2 * N * t) ∂α = J (Pi.single k (1 + 2 * (N : ℤ) * t)) := by
  have hi : 1 ≤ (Pi.single k (1 + 2 * (N : ℤ) * t) : Fin d → ℤ) k := by
    rw [Pi.single_eq_same]
    have : (0 : ℤ) ≤ 2 * (N : ℤ) * t := by positivity
    omega
  have h := hrep (Pi.single k (1 + 2 * (N : ℤ) * t)) hi
  rw [funext (repCharacter_single (N := N) (k := k) t), integral_complex_ofReal] at h
  exact_mod_cast h.symm

omit [NeZero N] in
/-- The `k`-axis moments are nonnegative, being integrals of even powers. -/
lemma integral_pow_fst_nonneg (t : ℕ) : 0 ≤ ∫ p, p.1 ^ (2 * N * t) ∂α := by
  have h : Even (2 * N * t) := ⟨N * t, by ring⟩
  exact integral_nonneg fun p ↦ h.pow_nonneg _

/-- The moment sequence is summable, by Georgii (17.23). -/
lemma summable_axis (hsum : Summable J) :
    Summable fun t : ℕ ↦ J (Pi.single k (1 + 2 * (N : ℤ) * t)) := by
  have hN : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine hsum.comp_injective fun t t' h ↦ ?_
  have h1 := congrFun h k
  simp only [Pi.single_eq_same] at h1
  have h2 : (2 * (N : ℤ)) * t = (2 * (N : ℤ)) * t' := by linarith
  have h3 : (t : ℤ) = (t' : ℤ) := mul_left_cancel₀ (by omega) h2
  exact_mod_cast h3

end Moments

/-! #### Georgii's resolvent `(1 - x^{2N})⁻¹`

Summing the geometric series `∑_{t ≥ 0} x^{2Nt}` in the `k`-direction produces the factor
`(1 - x^{2N})⁻¹` of Georgii's measure `m`.  Its integrability against a representing measure is
his estimate `∑_{k ≥ 0} ∫ α(dx, dz) x^{2Nk} = ∑_{k ≥ 0} J(1 + 2Nk, 0) < ∞`. -/

section Resolvent

variable {α : Measure (ℝ × (Fin d → ℝ))}

omit [NeZero N] in
lemma pow_two_mul_nonneg (x : ℝ) : 0 ≤ x ^ (2 * N) := by
  have h : Even (2 * N) := ⟨N, by ring⟩
  exact h.pow_nonneg x

lemma pow_two_mul_lt_one {x : ℝ} (hx : |x| < 1) : x ^ (2 * N) < 1 := by
  have hne : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have h : x ^ (2 * N) ≤ |x| ^ (2 * N) := by rw [← abs_pow]; exact le_abs_self _
  exact h.trans_lt (pow_lt_one₀ (abs_nonneg _) hx hne)

lemma hasSum_pow_two_mul {x : ℝ} (hx : |x| < 1) :
    HasSum (fun t : ℕ ↦ x ^ (2 * N * t)) (1 - x ^ (2 * N))⁻¹ := by
  have h := hasSum_geometric_of_lt_one (pow_two_mul_nonneg (N := N) x) (pow_two_mul_lt_one hx)
  simpa [pow_mul] using h

lemma hasSum_pow_two_mul_complex {x : ℝ} (hx : |x| < 1) :
    HasSum (fun t : ℕ ↦ (x : ℂ) ^ (2 * N * t)) (1 - (x : ℂ) ^ (2 * N))⁻¹ := by
  have hne : 2 * N ≠ 0 := by have := NeZero.ne N; omega
  have hnorm : ‖(x : ℂ) ^ (2 * N)‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_lt_one₀ (abs_nonneg _) hx hne
  simpa [pow_mul] using hasSum_geometric_of_norm_lt_one hnorm

/-- **The resolvent is integrable against a representing measure.**  Georgii's estimate
`∑_{t ≥ 0} ∫ α(dx, dz) x^{2Nt} = ∑_{t ≥ 0} J(1 + 2Nt, 0, …, 0) < ∞`. -/
lemma integrable_resolvent [IsFiniteMeasure α] (hα : ∀ᵐ p ∂α, |p.1| < 1)
    (hrep : ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α)
    (hsum : Summable J) :
    Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - p.1 ^ (2 * N))⁻¹) α := by
  have hmeas : Measurable fun p : ℝ × (Fin d → ℝ) ↦ (1 - p.1 ^ (2 * N))⁻¹ :=
    (measurable_const.sub (measurable_fst.pow_const _)).inv
  have hJnn : ∀ t : ℕ, 0 ≤ J (Pi.single k (1 + 2 * (N : ℤ) * t)) := fun t ↦ by
    rw [← integral_pow_fst (α := α) hrep t]
    exact integral_pow_fst_nonneg t
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have step1 : ∫⁻ p, ‖(1 - p.1 ^ (2 * N))⁻¹‖ₑ ∂α
      = ∫⁻ p, ∑' t : ℕ, ENNReal.ofReal (p.1 ^ (2 * N * t)) ∂α := by
    refine lintegral_congr_ae ?_
    filter_upwards [hα] with p hp
    have hnn : ∀ t : ℕ, (0 : ℝ) ≤ p.1 ^ (2 * N * t) := fun t ↦ by
      have h : Even (2 * N * t) := ⟨N * t, by ring⟩
      exact h.pow_nonneg _
    have hs := hasSum_pow_two_mul (N := N) hp
    have hres : (0 : ℝ) ≤ (1 - p.1 ^ (2 * N))⁻¹ :=
      inv_nonneg.2 (by linarith [pow_two_mul_lt_one (N := N) hp])
    rw [Real.enorm_eq_ofReal hres, ← hs.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg hnn hs.summable]
  have step2 : ∫⁻ p, ∑' t : ℕ, ENNReal.ofReal (p.1 ^ (2 * N * t)) ∂α
      = ∑' t : ℕ, ENNReal.ofReal (J (Pi.single k (1 + 2 * (N : ℤ) * t))) := by
    rw [lintegral_tsum fun t ↦ (measurable_fst.pow_const _).ennreal_ofReal.aemeasurable]
    refine tsum_congr fun t ↦ ?_
    have hev : Even (2 * N * t) := ⟨N * t, by ring⟩
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pow_fst hα _)
      (Filter.Eventually.of_forall fun p ↦ hev.pow_nonneg _),
      integral_pow_fst (α := α) hrep t]
  rw [step1, step2, ← ENNReal.ofReal_tsum_of_nonneg hJnn (summable_axis hsum)]
  exact ENNReal.ofReal_lt_top

end Resolvent

/-! #### Georgii's vectors `h_{(0,x,z)}` and `h_{(1,x,z)}`

The two families of functions in Georgii's proof of (17.29), read off site by site: the crossing
interaction of a single pair `(i, j)` of sites of the positive half is
`h_{(0)}(i) \overline{h_{(0)}(j)} + h_{(1)}(i) \overline{h_{(1)}(j)}`, integrated against
`(1 - x^{2N})⁻¹ α`. -/

section HeisVec

variable {α : Measure (ℝ × (Fin d → ℝ))}

variable (N k) in
/-- Georgii's `h_{(0,x,z)}` at a single site: `x^{u_i - 1} z^{v_i + 2Nℓ}`, where `u_i - 1` is
`N - 1 - i_k` in the coordinates of this file. -/
noncomputable def heisVecPos (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ)
    (p : ℝ × (Fin d → ℝ)) : ℂ :=
  (p.1 : ℂ) ^ (N - 1 - (i k).val) *
    transCharacter k (torusLift N i + (2 * N : ℤ) • splitIndex k 0 ℓ) p

variable (N k) in
/-- Georgii's `h_{(1,x,z)}` at a single site: `x^{N - u_i} z̄^{v_i + 2Nℓ}`, where `N - u_i` is
`i_k` in the coordinates of this file. -/
noncomputable def heisVecNeg (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ)
    (p : ℝ × (Fin d → ℝ)) : ℂ :=
  (p.1 : ℂ) ^ ((i k).val) *
    (starRingEnd ℂ) (transCharacter k (torusLift N i + (2 * N : ℤ) • splitIndex k 0 ℓ) p)

/-- **The transverse character of the crossing index factorises.**  This is what makes the
crossing interaction a Gram form in Georgii's vectors. -/
lemma transCharacter_crossing (i j : Fin d → ZMod (2 * N))
    (ℓ ℓ' : {c : Fin d // c ≠ k} → ℤ) (t : ℤ) (p : ℝ × (Fin d → ℝ)) :
    transCharacter k (torusLift N i + (2 * N : ℤ) • splitIndex k 0 ℓ) p
        * (starRingEnd ℂ) (transCharacter k (torusLift N j + (2 * N : ℤ) • splitIndex k 0 ℓ') p)
      = transCharacter k (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t (ℓ - ℓ')) p := by
  rw [← transCharacter_neg, ← transCharacter_add]
  refine transCharacter_congr (fun c hc ↦ ?_) p
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, torusLift,
    splitIndex_of_ne hc, Pi.sub_apply]
  rw [crossingIndex_of_ne hc]
  ring

omit [NeZero N] in
/-- The complex resolvent is the cast of the real one. -/
lemma resolvent_ofReal (x : ℝ) : (1 - (x : ℂ) ^ (2 * N))⁻¹ = (((1 - x ^ (2 * N))⁻¹ : ℝ) : ℂ) := by
  push_cast
  ring

/-- A boundedly dominated measurable function times the resolvent is integrable. -/
lemma integrable_resolvent_mul (hα : ∀ᵐ p ∂α, |p.1| < 1)
    (hres : Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - p.1 ^ (2 * N))⁻¹) α)
    {C : ℝ} {g : ℝ × (Fin d → ℝ) → ℂ} (hg : AEStronglyMeasurable g α)
    (hgb : ∀ᵐ p ∂α, ‖g p‖ ≤ C) :
    Integrable (fun p ↦ (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ * g p) α := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × (Fin d → ℝ) ↦ (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ * g p) α :=
    (((Complex.continuous_ofReal.measurable.comp measurable_fst).pow_const _).const_sub
      1).inv.aestronglyMeasurable.mul hg
  refine ⟨hmeas, (hres.const_mul |C|).2.mono ?_⟩
  filter_upwards [hα, hgb] with p hp hgp
  have hlt : p.1 ^ (2 * N) < 1 := pow_two_mul_lt_one hp
  have hnn : (0 : ℝ) ≤ (1 - p.1 ^ (2 * N))⁻¹ := inv_nonneg.2 (by linarith)
  have hnormres : ‖(1 - (p.1 : ℂ) ^ (2 * N))⁻¹‖ = (1 - p.1 ^ (2 * N))⁻¹ := by
    rw [resolvent_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  have hCnn : (0 : ℝ) ≤ |C| * (1 - p.1 ^ (2 * N))⁻¹ := mul_nonneg (abs_nonneg _) hnn
  rw [norm_mul, hnormres, Real.norm_eq_abs, abs_of_nonneg hCnn]
  calc (1 - p.1 ^ (2 * N))⁻¹ * ‖g p‖ ≤ (1 - p.1 ^ (2 * N))⁻¹ * |C| :=
        mul_le_mul_of_nonneg_left (hgp.trans (le_abs_self C)) hnn
    _ = |C| * (1 - p.1 ^ (2 * N))⁻¹ := mul_comm _ _

end HeisVec

/-! #### The two geometric series of Georgii's proof of (17.29)

Georgii sums the `k`-direction of the periodisation `∑_{t ∈ ℤ} J(idx + 2Nt e_k)` in two halves.
For `t ≥ 0` the `k`-coordinate `u + u' - 1 + 2Nt` is already positive and the representation
(17.27) applies directly; for `t < 0` he first flips the sign using the evenness of `J`.  The two
halves give the two geometric series `∑_{t ≥ 0} x^{u+u'-2+2Nt}` and `∑_{t ≥ 0} x^{2N-u-u'+2Nt}`,
i.e. Georgii's `x^{u+u'-2}(1-x^{2N})⁻¹` and `x^{2N-u-u'}(1-x^{2N})⁻¹`. -/

section AxisSum

variable {α : Measure (ℝ × (Fin d → ℝ))}

/-- **The `k`-direction of Georgii's proof of (17.29).**  If `idx` has `k`-coordinate `a + b + 1`
with `a, b < N` — Georgii's `u + u' - 1` with `a = u - 1`, `b = u' - 1` — then the periodisation of
`J` along the `k`-axis through `idx` is the integral against `(1 - x^{2N})⁻¹ α` of
`x^{a+b} z^{idx} + x^{(N-1-a)+(N-1-b)} z̄^{idx}`. -/
lemma tsum_J_axis_shift [IsFiniteMeasure α] (hα : ∀ᵐ p ∂α, |p.1| < 1)
    (hrep : ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (idx : Fin d → ℤ) {a b : ℕ} (ha : a < N) (hb : b < N)
    (hidxk : idx k = (a : ℤ) + (b : ℤ) + 1) :
    ((∑' t : ℤ, J (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ)
      = ∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
          ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p
            + (p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
              * (starRingEnd ℂ) (transCharacter k idx p)) ∂α := by
  classical
  have hres : Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - p.1 ^ (2 * N))⁻¹) α :=
    integrable_resolvent hα hrep hsum
  -- the shifted index: the `k`-coordinate moves, the transverse ones do not
  have hshiftk : ∀ t : ℤ, (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) k
      = (a : ℤ) + (b : ℤ) + 1 + 2 * (N : ℤ) * t := by
    intro t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, hidxk]
    ring
  have htrans : ∀ (t : ℤ) (p : ℝ × (Fin d → ℝ)),
      transCharacter k (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) p = transCharacter k idx p := by
    intro t p
    refine transCharacter_congr (fun c hc ↦ ?_) p
    simp [Pi.single_eq_of_ne hc]
  -- summability of the axis family
  have hNZ : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hinj : Function.Injective fun t : ℤ ↦ idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ) := by
    intro t t' h
    have h1 : (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) k
        = (idx + ((2 * N : ℤ) * t') • (Pi.single k 1 : Fin d → ℤ)) k := congrFun h k
    rw [hshiftk, hshiftk] at h1
    have h2 : 2 * (N : ℤ) * t = 2 * (N : ℤ) * t' := by linarith
    exact mul_left_cancel₀ (by omega) h2
  have hsummable : Summable fun t : ℤ ↦ J (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) :=
    hsum.comp_injective hinj
  -- the two integrals
  have hbdPos : ∀ᵐ p ∂α, ‖(p.1 : ℂ) ^ (a + b) * transCharacter k idx p‖ ≤ 1 := by
    filter_upwards [hα] with p hp
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_transCharacter, mul_one]
    exact pow_le_one₀ (abs_nonneg _) hp.le
  have hbdNeg : ∀ᵐ p ∂α, ‖(p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
      * (starRingEnd ℂ) (transCharacter k idx p)‖ ≤ 1 := by
    filter_upwards [hα] with p hp
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
      norm_transCharacter, mul_one]
    exact pow_le_one₀ (abs_nonneg _) hp.le
  have hIpos : Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
      ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p)) α :=
    integrable_resolvent_mul hα hres
      ((((Complex.continuous_ofReal.comp continuous_fst).pow _).mul
        (continuous_transCharacter idx)).aestronglyMeasurable) hbdPos
  have hIneg : Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
      ((p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
        * (starRingEnd ℂ) (transCharacter k idx p))) α :=
    integrable_resolvent_mul hα hres
      ((((Complex.continuous_ofReal.comp continuous_fst).pow _).mul
        (Complex.continuous_conj.comp (continuous_transCharacter idx))).aestronglyMeasurable) hbdNeg
  -- Georgii's `k ≥ 0` half
  have hposJ : ∀ t : ℕ,
      ((J (idx + ((2 * N : ℤ) * (t : ℤ)) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ)
        = ∫ p, (p.1 : ℂ) ^ (a + b + 2 * N * t) * transCharacter k idx p ∂α := by
    intro t
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 2 * N * t = M := ⟨_, rfl⟩
    have hMZ : (M : ℤ) = 2 * (N : ℤ) * (t : ℤ) := by rw [← hM]; push_cast; ring
    have h1 : (1 : ℤ) ≤ (idx + ((2 * N : ℤ) * (t : ℤ)) • (Pi.single k 1 : Fin d → ℤ)) k := by
      rw [hshiftk]; omega
    have h2 : ((idx + ((2 * N : ℤ) * (t : ℤ)) • (Pi.single k 1 : Fin d → ℤ)) k - 1).toNat = a + b + 2 * N * t := by
      rw [hshiftk, hM]; omega
    rw [hrep _ h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    rw [repCharacter_eq_mul, h2, htrans]
  have hposHS : HasSum
      (fun t : ℕ ↦ ∫ p, (p.1 : ℂ) ^ (a + b + 2 * N * t) * transCharacter k idx p ∂α)
      (∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹
        * ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p) ∂α) := by
    refine hasSum_integral_of_dominated_convergence (fun t p ↦ |p.1| ^ (2 * N * t)) ?_ ?_ ?_ ?_ ?_
    · exact fun t ↦ (((Complex.continuous_ofReal.comp continuous_fst).pow _).mul
        (continuous_transCharacter idx)).aestronglyMeasurable
    · intro t
      filter_upwards [hα] with p hp
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_transCharacter, mul_one]
      exact pow_le_pow_of_le_one (abs_nonneg _) hp.le (by omega)
    · filter_upwards [hα] with p hp
      exact (hasSum_pow_two_mul (N := N) (x := |p.1|) (by rwa [abs_abs])).summable
    · refine hres.congr ?_
      filter_upwards [hα] with p hp
      have h1 : |p.1| ^ (2 * N) = p.1 ^ (2 * N) := by
        rw [← abs_pow, abs_of_nonneg (pow_two_mul_nonneg (N := N) p.1)]
      rw [(hasSum_pow_two_mul (N := N) (x := |p.1|) (by rwa [abs_abs])).tsum_eq, h1]
    · filter_upwards [hα] with p hp
      have h := (hasSum_pow_two_mul_complex (N := N) hp).mul_left
        ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p)
      have heq : (fun t : ℕ ↦ (p.1 : ℂ) ^ (a + b + 2 * N * t) * transCharacter k idx p)
          = fun t : ℕ ↦ ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p) * (p.1 : ℂ) ^ (2 * N * t) := by
        funext t; rw [pow_add]; ring
      rw [heq, mul_comm ((1 - (p.1 : ℂ) ^ (2 * N))⁻¹)]
      exact h
  -- Georgii's `k < 0` half, obtained from the evenness of `J`
  have hnegJ : ∀ t : ℕ,
      ((J (idx + ((2 * N : ℤ) * (-((t : ℤ) + 1))) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ)
        = ∫ p, (p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b) + 2 * N * t)
            * (starRingEnd ℂ) (transCharacter k idx p) ∂α := by
    intro t
    obtain ⟨M, hM⟩ : ∃ M : ℕ, 2 * N * t = M := ⟨_, rfl⟩
    have hMZ : (M : ℤ) = 2 * (N : ℤ) * (t : ℤ) := by rw [← hM]; push_cast; ring
    have hk : (idx + ((2 * N : ℤ) * (-((t : ℤ) + 1))) • (Pi.single k 1 : Fin d → ℤ)) k
        = (a : ℤ) + (b : ℤ) + 1 - 2 * (N : ℤ) * (t : ℤ) - 2 * (N : ℤ) := by
      rw [hshiftk]; ring
    have h1 : (1 : ℤ) ≤ (-(idx + ((2 * N : ℤ) * (-((t : ℤ) + 1))) • (Pi.single k 1 : Fin d → ℤ))) k := by
      simp only [Pi.neg_apply, hk]; omega
    have h2 : ((-(idx + ((2 * N : ℤ) * (-((t : ℤ) + 1))) • (Pi.single k 1 : Fin d → ℤ))) k - 1).toNat
        = N - 1 - a + (N - 1 - b) + 2 * N * t := by
      simp only [Pi.neg_apply, hk]
      rw [hM]; omega
    rw [← heven (idx + ((2 * N : ℤ) * (-((t : ℤ) + 1))) • (Pi.single k 1 : Fin d → ℤ)), hrep _ h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    rw [repCharacter_eq_mul, h2, transCharacter_neg, htrans]
  have hnegHS : HasSum
      (fun t : ℕ ↦ ∫ p, (p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b) + 2 * N * t)
        * (starRingEnd ℂ) (transCharacter k idx p) ∂α)
      (∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹
        * ((p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
          * (starRingEnd ℂ) (transCharacter k idx p)) ∂α) := by
    refine hasSum_integral_of_dominated_convergence (fun t p ↦ |p.1| ^ (2 * N * t)) ?_ ?_ ?_ ?_ ?_
    · exact fun t ↦ (((Complex.continuous_ofReal.comp continuous_fst).pow _).mul
        (Complex.continuous_conj.comp (continuous_transCharacter idx))).aestronglyMeasurable
    · intro t
      filter_upwards [hα] with p hp
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
        norm_transCharacter, mul_one]
      exact pow_le_pow_of_le_one (abs_nonneg _) hp.le (by omega)
    · filter_upwards [hα] with p hp
      exact (hasSum_pow_two_mul (N := N) (x := |p.1|) (by rwa [abs_abs])).summable
    · refine hres.congr ?_
      filter_upwards [hα] with p hp
      have h1 : |p.1| ^ (2 * N) = p.1 ^ (2 * N) := by
        rw [← abs_pow, abs_of_nonneg (pow_two_mul_nonneg (N := N) p.1)]
      rw [(hasSum_pow_two_mul (N := N) (x := |p.1|) (by rwa [abs_abs])).tsum_eq, h1]
    · filter_upwards [hα] with p hp
      have h := (hasSum_pow_two_mul_complex (N := N) hp).mul_left
        ((p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b)) * (starRingEnd ℂ) (transCharacter k idx p))
      have heq : (fun t : ℕ ↦ (p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b) + 2 * N * t)
            * (starRingEnd ℂ) (transCharacter k idx p))
          = fun t : ℕ ↦ ((p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
            * (starRingEnd ℂ) (transCharacter k idx p)) * (p.1 : ℂ) ^ (2 * N * t) := by
        funext t; rw [pow_add]; ring
      rw [heq, mul_comm ((1 - (p.1 : ℂ) ^ (2 * N))⁻¹)]
      exact h
  -- assemble the two halves
  have htot : HasSum (fun t : ℤ ↦ ((J (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ))
      ((∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹
          * ((p.1 : ℂ) ^ (a + b) * transCharacter k idx p) ∂α)
        + ∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹
          * ((p.1 : ℂ) ^ (N - 1 - a + (N - 1 - b))
            * (starRingEnd ℂ) (transCharacter k idx p)) ∂α) :=
    HasSum.of_nat_of_neg_add_one (by simpa only [hposJ] using hposHS)
      (by simpa only [hnegJ] using hnegHS)
  have hcast : HasSum (fun t : ℤ ↦ ((J (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ))
      ((∑' t : ℤ, J (idx + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) : ℝ) : ℂ) := by
    exact Complex.hasSum_ofReal.2 hsummable.hasSum
  rw [← htot.unique hcast, ← integral_add hIpos hIneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  ring

end AxisSum

/-! #### The Gram form of Georgii's vectors -/

section Gram

variable {α : Measure (ℝ × (Fin d → ℝ))}

lemma norm_heisVecPos_le {p : ℝ × (Fin d → ℝ)} (hp : |p.1| ≤ 1)
    (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ) :
    ‖heisVecPos N k i ℓ p‖ ≤ 1 := by
  rw [heisVecPos, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_transCharacter,
    mul_one]
  exact pow_le_one₀ (abs_nonneg _) hp

lemma norm_heisVecNeg_le {p : ℝ × (Fin d → ℝ)} (hp : |p.1| ≤ 1)
    (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ) :
    ‖heisVecNeg N k i ℓ p‖ ≤ 1 := by
  rw [heisVecNeg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
    norm_transCharacter, mul_one]
  exact pow_le_one₀ (abs_nonneg _) hp

lemma continuous_heisVecPos (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ) :
    Continuous (heisVecPos N k i ℓ) :=
  ((Complex.continuous_ofReal.comp continuous_fst).pow _).mul (continuous_transCharacter _)

lemma continuous_heisVecNeg (i : Fin d → ZMod (2 * N)) (ℓ : {c : Fin d // c ≠ k} → ℤ) :
    Continuous (heisVecNeg N k i ℓ) :=
  ((Complex.continuous_ofReal.comp continuous_fst).pow _).mul
    (Complex.continuous_conj.comp (continuous_transCharacter _))

/-- **Georgii's crossing form is a Gram form.**  For two sites of the positive half and two
transverse shifts, the `k`-periodised crossing coupling is
`h_{(0)}(i,ℓ) conj h_{(0)}(j,ℓ') + h_{(1)}(i,ℓ) conj h_{(1)}(j,ℓ')` integrated against
`(1 - x^{2N})⁻¹ α`. -/
lemma tsum_J_crossing_eq_integral [IsFiniteMeasure α] (hα : ∀ᵐ p ∂α, |p.1| < 1)
    (hrep : ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    {i j : Fin d → ZMod (2 * N)} (hi : (i k).val < N) (hj : (j k).val < N)
    (ℓ ℓ' : {c : Fin d // c ≠ k} → ℤ) :
    ((∑' t : ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t (ℓ - ℓ')) : ℝ) : ℂ)
      = ∫ p, (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
          (heisVecPos N k i ℓ p * (starRingEnd ℂ) (heisVecPos N k j ℓ' p)
            + heisVecNeg N k i ℓ p * (starRingEnd ℂ) (heisVecNeg N k j ℓ' p)) ∂α := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hshift : ∀ t : ℤ, crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t (ℓ - ℓ')
      = (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k 0 (ℓ - ℓ'))
        + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ) := by
    intro t
    funext c
    by_cases h : c = k
    · subst h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, splitIndex_self, Pi.single_eq_same]
      ring
    · simp [splitIndex_of_ne h, Pi.single_eq_of_ne h]
  have hrw : (∑' t : ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t (ℓ - ℓ')))
      = ∑' t : ℤ, J ((crossingIndex N k i j + (2 * N : ℤ) • splitIndex k 0 (ℓ - ℓ'))
          + ((2 * N : ℤ) * t) • (Pi.single k 1 : Fin d → ℤ)) :=
    tsum_congr fun t ↦ by rw [hshift t]
  have hidxk : (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k 0 (ℓ - ℓ')) k
      = ((N - 1 - (i k).val : ℕ) : ℤ) + ((N - 1 - (j k).val : ℕ) : ℤ) + 1 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, crossingIndex_self, splitIndex_self]
    omega
  rw [hrw, tsum_J_axis_shift hα hrep hsum heven _ (by omega) (by omega) hidxk]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
  dsimp only
  have hNa : N - 1 - (N - 1 - (i k).val) = (i k).val := by omega
  have hNb : N - 1 - (N - 1 - (j k).val) = (j k).val := by omega
  rw [hNa, hNb]
  have hcross := transCharacter_crossing (N := N) i j ℓ ℓ' 0 p
  have h1 : heisVecPos N k i ℓ p * (starRingEnd ℂ) (heisVecPos N k j ℓ' p)
      = (p.1 : ℂ) ^ (N - 1 - (i k).val + (N - 1 - (j k).val))
        * transCharacter k (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k 0 (ℓ - ℓ')) p := by
    rw [heisVecPos, heisVecPos, map_mul, map_pow, Complex.conj_ofReal, pow_add, ← hcross]
    ring
  have h2 : heisVecNeg N k i ℓ p * (starRingEnd ℂ) (heisVecNeg N k j ℓ' p)
      = (p.1 : ℂ) ^ ((i k).val + (j k).val)
        * (starRingEnd ℂ)
          (transCharacter k (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k 0 (ℓ - ℓ')) p) := by
    rw [heisVecNeg, heisVecNeg, map_mul, map_pow, Complex.conj_ofReal, pow_add, ← hcross, map_mul]
    simp only [Complex.conj_conj]
    ring
  rw [h1, h2]

omit [NeZero N] in
/-- The Gram identity for Georgii's first family of vectors. -/
lemma sum_mul_conj_heisVecPos
    (W : Finset ((Fin d → ZMod (2 * N)) × ({c : Fin d // c ≠ k} → ℤ)))
    (x : (Fin d → ZMod (2 * N)) → ℝ) (p : ℝ × (Fin d → ℝ)) :
    ∑ w ∈ W, ∑ w' ∈ W, (x w.1 : ℂ) * (x w'.1 : ℂ) *
        (heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p))
      = ((Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecPos N k w.1 w.2 p) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun w' _ ↦ ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

omit [NeZero N] in
/-- The Gram identity for Georgii's second family of vectors. -/
lemma sum_mul_conj_heisVecNeg
    (W : Finset ((Fin d → ZMod (2 * N)) × ({c : Fin d // c ≠ k} → ℤ)))
    (x : (Fin d → ZMod (2 * N)) → ℝ) (p : ℝ × (Fin d → ℝ)) :
    ∑ w ∈ W, ∑ w' ∈ W, (x w.1 : ℂ) * (x w'.1 : ℂ) *
        (heisVecNeg N k w.1 w.2 p * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p))
      = ((Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecNeg N k w.1 w.2 p) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ Finset.sum_congr rfl fun w' _ ↦ ?_
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- **The Gram bound.**  For any finite family of (site, transverse shift) pairs with sites in the
positive half and any real weights, the associated quadratic form of the `k`-periodised crossing
coupling is nonnegative: it is the integral against `α` of
`(1 - x^{2N})⁻¹ (|∑ c h_{(0)}|² + |∑ c h_{(1)}|²)`. -/
lemma sum_tsum_J_crossing_nonneg [IsFiniteMeasure α] (hα : ∀ᵐ p ∂α, |p.1| < 1)
    (hrep : ∀ i : Fin d → ℤ, 1 ≤ i k → (J i : ℂ) = ∫ p, repCharacter k i p ∂α)
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (W : Finset ((Fin d → ZMod (2 * N)) × ({c : Fin d // c ≠ k} → ℤ)))
    (hW : ∀ w ∈ W, (w.1 k).val < N) (x : (Fin d → ZMod (2 * N)) → ℝ) :
    0 ≤ ∑ w ∈ W, ∑ w' ∈ W, x w.1 * x w'.1 *
        ∑' t : ℤ, J (crossingIndex N k w.1 w'.1 + (2 * N : ℤ) • splitIndex k t (w.2 - w'.2)) := by
  classical
  have hres : Integrable (fun p : ℝ × (Fin d → ℝ) ↦ (1 - p.1 ^ (2 * N))⁻¹) α :=
    integrable_resolvent hα hrep hsum
  -- the integral that the quadratic form equals
  have hInonneg : 0 ≤ ∫ p, (1 - p.1 ^ (2 * N))⁻¹ *
      (Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecPos N k w.1 w.2 p)
        + Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecNeg N k w.1 w.2 p)) ∂α := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hα] with p hp
    have h1 : p.1 ^ (2 * N) < 1 := pow_two_mul_lt_one hp
    exact mul_nonneg (inv_nonneg.2 (by linarith))
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  -- integrability of each term of the double sum
  have hint : ∀ w ∈ W, ∀ w' ∈ W, Integrable (fun p : ℝ × (Fin d → ℝ) ↦
      (x w.1 : ℂ) * (x w'.1 : ℂ) * ((1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
        (heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)
          + heisVecNeg N k w.1 w.2 p * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p)))) α := by
    intro w _ w' _
    refine Integrable.const_mul ?_ _
    refine integrable_resolvent_mul (C := 2) hα hres ?_ ?_
    · exact (((continuous_heisVecPos w.1 w.2).mul
        (Complex.continuous_conj.comp (continuous_heisVecPos w'.1 w'.2))).add
        ((continuous_heisVecNeg w.1 w.2).mul
          (Complex.continuous_conj.comp
            (continuous_heisVecNeg w'.1 w'.2)))).aestronglyMeasurable
    · filter_upwards [hα] with p hp
      have h1 : ‖heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)‖ ≤ 1 := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_one₀ (norm_heisVecPos_le hp.le _ _) (norm_nonneg _)
          (norm_heisVecPos_le hp.le _ _)
      have h2 : ‖heisVecNeg N k w.1 w.2 p * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p)‖ ≤ 1 := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_one₀ (norm_heisVecNeg_le hp.le _ _) (norm_nonneg _)
          (norm_heisVecNeg_le hp.le _ _)
      calc ‖heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)
              + heisVecNeg N k w.1 w.2 p * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p)‖
          ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 := by linarith
  -- the quadratic form is that integral
  have hkey : ((∑ w ∈ W, ∑ w' ∈ W, x w.1 * x w'.1 *
      ∑' t : ℤ, J (crossingIndex N k w.1 w'.1
        + (2 * N : ℤ) • splitIndex k t (w.2 - w'.2)) : ℝ) : ℂ)
      = ((∫ p, (1 - p.1 ^ (2 * N))⁻¹ *
          (Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecPos N k w.1 w.2 p)
            + Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecNeg N k w.1 w.2 p)) ∂α : ℝ) : ℂ) := by
    push_cast [-Complex.ofReal_tsum]
    have hterm : ∀ w ∈ W, ∀ w' ∈ W,
        (x w.1 : ℂ) * (x w'.1 : ℂ) * ((∑' t : ℤ, J (crossingIndex N k w.1 w'.1
            + (2 * N : ℤ) • splitIndex k t (w.2 - w'.2)) : ℝ) : ℂ)
          = ∫ p, (x w.1 : ℂ) * (x w'.1 : ℂ) * ((1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
              (heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)
                + heisVecNeg N k w.1 w.2 p
                  * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p))) ∂α := by
      intro w hw w' hw'
      rw [tsum_J_crossing_eq_integral hα hrep hsum heven (hW w hw) (hW w' hw'),
        integral_const_mul]
    rw [Finset.sum_congr rfl fun w hw ↦ Finset.sum_congr rfl fun w' hw' ↦ hterm w hw w' hw']
    rw [Finset.sum_congr rfl fun w hw ↦
      (integral_finset_sum W fun w' hw' ↦ hint w hw w' hw').symm]
    rw [← integral_finset_sum W fun w hw ↦
      integrable_finset_sum W fun w' hw' ↦ hint w hw w' hw']
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    have hsplit : ∀ w w' : (Fin d → ZMod (2 * N)) × ({c : Fin d // c ≠ k} → ℤ),
        (x w.1 : ℂ) * (x w'.1 : ℂ) * ((1 - (p.1 : ℂ) ^ (2 * N))⁻¹ *
            (heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)
              + heisVecNeg N k w.1 w.2 p * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p)))
          = (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ * ((x w.1 : ℂ) * (x w'.1 : ℂ)
                * (heisVecPos N k w.1 w.2 p * (starRingEnd ℂ) (heisVecPos N k w'.1 w'.2 p)))
            + (1 - (p.1 : ℂ) ^ (2 * N))⁻¹ * ((x w.1 : ℂ) * (x w'.1 : ℂ)
                * (heisVecNeg N k w.1 w.2 p
                  * (starRingEnd ℂ) (heisVecNeg N k w'.1 w'.2 p))) := fun w w' ↦ by ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_mul_conj_heisVecPos, sum_mul_conj_heisVecNeg, resolvent_ofReal]
    push_cast
    ring
  have hreal : (∑ w ∈ W, ∑ w' ∈ W, x w.1 * x w'.1 *
      ∑' t : ℤ, J (crossingIndex N k w.1 w'.1 + (2 * N : ℤ) • splitIndex k t (w.2 - w'.2)))
      = ∫ p, (1 - p.1 ^ (2 * N))⁻¹ *
          (Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecPos N k w.1 w.2 p)
            + Complex.normSq (∑ w ∈ W, (x w.1 : ℂ) * heisVecNeg N k w.1 w.2 p)) ∂α := by
    exact_mod_cast hkey
  rw [hreal]
  exact hInonneg

end Gram

/-! #### Georgii, Theorem (17.29) -/

section PosSemidef

/-- **The crossing matrix is symmetric.**  `J_Λ(r_k j - i)` is obtained from `J_Λ(r_k i - j)` by
negating the transverse coordinates, which is the composition of the two invariances of `J_Λ`:
evenness and the flip of the `k`-th coordinate. -/
lemma crossingMatrix_comm (heven : ∀ m, J (-m) = J m) (hflip : ∀ m, J (flipCoord k m) = J m)
    (i j : Fin d → ZMod (2 * N)) :
    crossingMatrix N J k j i = crossingMatrix N J k i j := by
  by_cases hi : (i k).val < N
  · by_cases hj : (j k).val < N
    · rw [crossingMatrix_of_mem hj hi, crossingMatrix_of_mem hi hj]
      have h : torusReflAt N k j - i = flipTorus k (-(torusReflAt N k i - j)) := by
        funext c
        by_cases hc : c = k
        · subst hc
          simp only [Pi.sub_apply, torusReflAt_apply_self, flipTorus, Function.update_self,
            Pi.neg_apply]
          ring
        · simp only [Pi.sub_apply, torusReflAt_apply_of_ne hc, flipTorus,
            Function.update_of_ne hc, Pi.neg_apply]
          ring
      rw [h, periodizedCoupling_flipTorus hflip, periodizedCoupling_neg heven]
    · rw [crossingMatrix_eq_zero fun h ↦ hj h.1, crossingMatrix_eq_zero fun h ↦ hj h.2]
  · rw [crossingMatrix_eq_zero fun h ↦ hi h.2, crossingMatrix_eq_zero fun h ↦ hi h.1]

/-- The splitting of `ℤ^d` is injective on the shifted crossing index. -/
lemma injective_crossingIndex_add_splitIndex (i j : Fin d → ZMod (2 * N)) :
    Function.Injective fun q : ({c : Fin d // c ≠ k} → ℤ) × ℤ ↦
      crossingIndex N k i j + (2 * N : ℤ) • splitIndex k q.2 q.1 := by
  have hNZ : (2 * (N : ℤ)) ≠ 0 := by
    have : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    omega
  intro q q' h
  have h1 : (2 * N : ℤ) • splitIndex k q.2 q.1 = (2 * N : ℤ) • splitIndex k q'.2 q'.1 :=
    add_left_cancel h
  have h2 : splitIndex k q.2 q.1 = splitIndex k q'.2 q'.1 := by
    funext c
    have hc := congrFun h1 c
    simp only [Pi.smul_apply, smul_eq_mul] at hc
    exact mul_left_cancel₀ hNZ hc
  exact (splitIndexEquiv k).injective h2

/-- **The crossing matrix as an iterated sum.**  Splitting the periodisation index into its
`k`-component and its transverse component. -/
lemma hasSum_tsum_crossing (hsum : Summable J) {i j : Fin d → ZMod (2 * N)}
    (hi : (i k).val < N) (hj : (j k).val < N) :
    HasSum (fun s : {c : Fin d // c ≠ k} → ℤ ↦
        ∑' t : ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t s))
      (crossingMatrix N J k i j) := by
  have hq : Summable fun q : ({c : Fin d // c ≠ k} → ℤ) × ℤ ↦
      J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k q.2 q.1) :=
    hsum.comp_injective (injective_crossingIndex_add_splitIndex i j)
  have hval : (∑' q : ({c : Fin d // c ≠ k} → ℤ) × ℤ,
      J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k q.2 q.1))
      = crossingMatrix N J k i j := by
    rw [crossingMatrix_eq_tsum hi hj]
    exact (tsum_splitIndex (k := k) fun m ↦ J (crossingIndex N k i j + (2 * N : ℤ) • m)).symm
  have h := hq.hasSum.prod_fiberwise fun s ↦ (hq.prod_factor s).hasSum
  rwa [hval] at h

omit [NeZero N] in
/-- Reordering the four-fold sum: the transverse box average of a quadratic form over the positive
half is the quadratic form of the pairs (site, transverse shift). -/
lemma sum_sub_box_eq_sum_product (P : Finset (Fin d → ZMod (2 * N)))
    (B : Finset ({c : Fin d // c ≠ k} → ℤ))
    (T : (Fin d → ZMod (2 * N)) → (Fin d → ZMod (2 * N)) →
      ({c : Fin d // c ≠ k} → ℤ) → ℝ) (x : (Fin d → ZMod (2 * N)) → ℝ) :
    (∑ ℓ ∈ B, ∑ ℓ' ∈ B, ∑ i ∈ P, ∑ j ∈ P, x i * x j * T i j (ℓ - ℓ'))
      = ∑ w ∈ P ×ˢ B, ∑ w' ∈ P ×ˢ B, x w.1 * x w'.1 * T w.1 w'.1 (w.2 - w'.2) := by
  rw [Finset.sum_product' P B fun i ℓ ↦
    ∑ w' ∈ P ×ˢ B, x i * x w'.1 * T i w'.1 (ℓ - w'.2)]
  calc ∑ ℓ ∈ B, ∑ ℓ' ∈ B, ∑ i ∈ P, ∑ j ∈ P, x i * x j * T i j (ℓ - ℓ')
      = ∑ ℓ ∈ B, ∑ i ∈ P, ∑ ℓ' ∈ B, ∑ j ∈ P, x i * x j * T i j (ℓ - ℓ') :=
        Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_comm
    _ = ∑ i ∈ P, ∑ ℓ ∈ B, ∑ ℓ' ∈ B, ∑ j ∈ P, x i * x j * T i j (ℓ - ℓ') := Finset.sum_comm
    _ = ∑ i ∈ P, ∑ ℓ ∈ B, ∑ j ∈ P, ∑ ℓ' ∈ B, x i * x j * T i j (ℓ - ℓ') :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun ℓ _ ↦ Finset.sum_comm
    _ = ∑ i ∈ P, ∑ ℓ ∈ B, ∑ w' ∈ P ×ˢ B, x i * x w'.1 * T i w'.1 (ℓ - w'.2) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun ℓ _ ↦
          (Finset.sum_product' P B fun j ℓ' ↦ x i * x j * T i j (ℓ - ℓ')).symm

/-- **Georgii, Theorem (17.29), the linear-algebra half.**  If `J` is even, absolutely summable
(17.23) and nonnegative definite relative to `r_k` (17.27), then the crossing matrix
`M(i, j) = J_Λ(r_k i - j)` is positive semidefinite.

The quadratic form `∑ x_i x_j M(i, j)` is the limit of the Cesàro (Fejér) box averages of the
transverse periodisation, each of which is a Gram form by `sum_tsum_J_crossing_nonneg`; positivity
survives the limit. -/
theorem IsNonnegDefiniteAt.posSemidef_crossingMatrix (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hnd : IsNonnegDefiniteAt k J) :
    (crossingMatrix N J k).PosSemidef := by
  classical
  obtain ⟨α, hαfin, hα, hrep⟩ := hnd
  have hflip : ∀ m, J (flipCoord k m) = J m :=
    IsNonnegDefiniteAt.flipCoord_eq ⟨α, hαfin, hα, hrep⟩ heven
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · show (crossingMatrix N J k)ᴴ = crossingMatrix N J k
    ext i j
    simpa using crossingMatrix_comm heven hflip i j
  -- the quadratic form, restricted to the positive half
  set P : Finset (Fin d → ZMod (2 * N)) := torusPosAtFinset N k with hP
  have hmemP : ∀ i, i ∈ P ↔ (i k).val < N := fun i ↦ mem_torusPosAtFinset
  have hdot : star x ⬝ᵥ (crossingMatrix N J k *ᵥ x)
      = ∑ i ∈ P, ∑ j ∈ P, x i * x j * crossingMatrix N J k i j := by
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ P) fun i _ hi ↦ ?_]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) fun j _ hj ↦ ?_]
      · exact Finset.sum_congr rfl fun j _ ↦ by ring
      · rw [crossingMatrix_eq_zero fun h ↦ (hmemP j).not.1 hj h.2]
        ring
    · refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [crossingMatrix_eq_zero fun h ↦ (hmemP i).not.1 hi h.1]
      ring
  rw [hdot]
  -- the transverse Cesàro averages
  set R : ({c : Fin d // c ≠ k} → ℤ) → ℝ := fun s ↦ ∑ i ∈ P, ∑ j ∈ P, x i * x j *
    ∑' t : ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t s) with hR
  have hRsum : HasSum R (∑ i ∈ P, ∑ j ∈ P, x i * x j * crossingMatrix N J k i j) :=
    hasSum_sum fun i hi ↦ hasSum_sum fun j hj ↦
      (hasSum_tsum_crossing hsum ((hmemP i).1 hi) ((hmemP j).1 hj)).mul_left _
  have hlim := hRsum.summable.tendsto_boxAverage_sub
  rw [hRsum.tsum_eq] at hlim
  refine ge_of_tendsto' hlim fun L ↦ ?_
  -- each box average is a Gram form, hence nonnegative
  refine mul_nonneg (by positivity) ?_
  set B : Finset ({c : Fin d // c ≠ k} → ℤ) :=
    Fintype.piFinset fun _ : {c : Fin d // c ≠ k} ↦ Finset.Ico (0 : ℤ) (L : ℤ) with hB
  have hkey : ∑ ℓ ∈ B, ∑ ℓ' ∈ B, R (ℓ - ℓ')
      = ∑ w ∈ P ×ˢ B, ∑ w' ∈ P ×ˢ B, x w.1 * x w'.1 *
          ∑' t : ℤ, J (crossingIndex N k w.1 w'.1
            + (2 * N : ℤ) • splitIndex k t (w.2 - w'.2)) :=
    sum_sub_box_eq_sum_product P B
      (fun i j s ↦ ∑' t : ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • splitIndex k t s)) x
  rw [hkey]
  exact sum_tsum_J_crossing_nonneg hα hrep hsum heven _
    (fun w hw ↦ (hmemP w.1).1 (Finset.mem_product.1 hw).1) x

/-- **Georgii, Theorem (17.29).**  Let `Φ` be a Heisenberg potential (17.22) whose coupling `J`
is even, absolutely summable (17.23) and nonnegative definite relative to `r_k` (17.27).  Then the
Gibbs distribution in the torus `Λ` with periodic boundary condition is `r_k`-positive.

The hypothesis `hint` is Georgii's standing assumption that `°Z_Λ^Φ` is finite. -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : IsNonnegDefiniteAt k J)
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) :=
  isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef heven (hnd.flipCoord_eq heven)
    (hnd.posSemidef_crossingMatrix hsum heven) ν hint

/-- **Georgii, Theorem (17.29)** for the normalised distribution `°γ_Λ^Φ`. -/
theorem isReflectionPositive_heisenbergPeriodicGibbsDist_of_isNonnegDefiniteAt
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m) (hnd : IsNonnegDefiniteAt k J)
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbsDist N n J ν) :=
  (isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt hsum heven hnd ν hint).smul _

end PosSemidef

end NonnegDefiniteCrossing

/-! ### Georgii, Example (17.30): ferromagnetic nearest-neighbour potentials

A `J` supported on the nearest-neighbour bonds `|i| = 1` — here `∑_c |i_c| = 1` — and nonnegative
there makes the crossing matrix *diagonal* with nonnegative entries: on the torus the only bonds
that cross the plane of `r_k` join `i` to `r_k i` for `i_k ∈ {0, N-1}`.  So `°γ_Λ^Φ` is
`r_k`-positive for every `k`, with no appeal to Theorem (17.29).  Georgii deduces this from
(17.29) with the representing measure `J(e_1) δ_0 × ν^{d-1}`; the direct argument is the same
sum-of-squares decomposition of the Hamiltonian, with a diagonal `B`. -/

lemma periodizedCoupling_nonneg (hpos : ∀ m, 0 ≤ J m) (z : Fin d → ZMod (2 * N)) :
    0 ≤ periodizedCoupling N J z :=
  tsum_nonneg fun _ ↦ hpos _

lemma crossingMatrix_nonneg (hpos : ∀ m, 0 ≤ J m) (i j : Fin d → ZMod (2 * N)) :
    0 ≤ crossingMatrix N J k i j := by
  rw [crossingMatrix]
  split
  · exact periodizedCoupling_nonneg hpos _
  · exact le_rfl

lemma sum_natAbs_flipCoord (m : Fin d → ℤ) :
    ∑ c, ((flipCoord k m) c).natAbs = ∑ c, (m c).natAbs := by
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  by_cases h : c = k
  · subst h; simp
  · simp [h]

/-- A nearest-neighbour coupling is invariant under the flip of any coordinate: the only vectors
in its support are `± e_c`, and flipping the `k`-th coordinate either fixes them or negates
them. -/
lemma flipCoord_eq_of_nearestNeighbour
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (heven : ∀ m, J (-m) = J m) (m : Fin d → ℤ) : J (flipCoord k m) = J m := by
  by_cases hk : m k = 0
  · have : flipCoord k m = m := by
      funext c
      by_cases h : c = k <;> simp [flipCoord, h, hk]
    rw [this]
  · by_cases hs : ∑ c, (m c).natAbs = 1
    · have hone : (m k).natAbs = 1 := by
        have hle : (m k).natAbs ≤ ∑ c, (m c).natAbs :=
          Finset.single_le_sum (f := fun c ↦ (m c).natAbs) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ k)
        rw [hs] at hle
        omega
      have hrest : ∀ c, c ≠ k → m c = 0 := by
        intro c hc
        have hsplit : ∑ c' ∈ Finset.univ.erase k, (m c').natAbs + (m k).natAbs
            = ∑ c', (m c').natAbs := Finset.sum_erase_add _ _ (Finset.mem_univ k)
        rw [hs, hone] at hsplit
        have hz : ∑ c' ∈ Finset.univ.erase k, (m c').natAbs = 0 := by omega
        have := (Finset.sum_eq_zero_iff.1 hz) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩)
        omega
      have hm : flipCoord k m = -m := by
        funext c
        by_cases h : c = k
        · subst h; simp [flipCoord]
        · simp [flipCoord, h, hrest c h]
      rw [hm, heven]
    · rw [hsupp _ hs, hsupp _ (by rwa [sum_natAbs_flipCoord])]

/-- **The crossing matrix of a nearest-neighbour coupling is diagonal.**  A bond `i → j` of the
torus that survives the reflection must have `i_c = j_c` for `c ≠ k` and `i_k = j_k ∈ {0, N-1}`,
because the `k`-th coordinate `2N - 1 - i_k - j_k` of the crossing index lies in `{1, …, 2N-1}`
and can only be `±1` modulo `2N`. -/
theorem crossingMatrix_eq_zero_of_nearestNeighbour
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    {i j : Fin d → ZMod (2 * N)} (hi : (i k).val < N) (hj : (j k).val < N) (hij : i ≠ j) :
    crossingMatrix N J k i j = 0 := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : ((i k).val : ℤ) < (N : ℤ) := by exact_mod_cast hi
  have hb : ((j k).val : ℤ) < (N : ℤ) := by exact_mod_cast hj
  have ha0 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ ((j k).val : ℤ) := Int.natCast_nonneg _
  rw [crossingMatrix_eq_tsum hi hj]
  have hzero : ∀ ℓ : Fin d → ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • ℓ) = 0 := by
    intro ℓ
    refine hsupp _ fun hsum ↦ hij ?_
    set x : Fin d → ℤ := crossingIndex N k i j + (2 * N : ℤ) • ℓ with hxdef
    have hxk : x k = (2 * N : ℤ) - 1 - ((i k).val : ℤ) - ((j k).val : ℤ) + (2 * N : ℤ) * ℓ k := by
      simp [hxdef, crossingIndex_self]
    have hxc : ∀ c, c ≠ k →
        x c = ((i c).val : ℤ) - ((j c).val : ℤ) + (2 * N : ℤ) * ℓ c := by
      intro c hc
      simp [hxdef, crossingIndex_of_ne hc]
    -- the `k`-th entry is nonzero
    have hxk0 : x k ≠ 0 := by
      intro h0
      rw [hxk] at h0
      have h1 : ((i k).val : ℤ) + ((j k).val : ℤ) = (2 * N : ℤ) * (1 + ℓ k) - 1 := by linarith
      have h2 : (1 : ℤ) ≤ (2 * N : ℤ) * (1 + ℓ k) := by linarith
      have h3 : (2 * N : ℤ) * (1 + ℓ k) ≤ (2 * N : ℤ) - 1 := by linarith
      have h4 : (1 : ℤ) ≤ 1 + ℓ k := by nlinarith
      nlinarith
    -- hence it has absolute value one, and every other entry vanishes
    have hone : (x k).natAbs = 1 := by
      have hle : (x k).natAbs ≤ ∑ c, (x c).natAbs :=
        Finset.single_le_sum (f := fun c ↦ (x c).natAbs) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ k)
      rw [hsum] at hle
      have : (x k).natAbs ≠ 0 := fun h ↦ hxk0 (Int.natAbs_eq_zero.1 h)
      omega
    have hrest : ∀ c, c ≠ k → x c = 0 := by
      intro c hc
      have hsplit : ∑ c' ∈ Finset.univ.erase k, (x c').natAbs + (x k).natAbs
          = ∑ c', (x c').natAbs := Finset.sum_erase_add _ _ (Finset.mem_univ k)
      rw [hsum, hone] at hsplit
      have hz : ∑ c' ∈ Finset.univ.erase k, (x c').natAbs = 0 := by omega
      have := (Finset.sum_eq_zero_iff.1 hz) c (Finset.mem_erase.2 ⟨hc, Finset.mem_univ c⟩)
      exact Int.natAbs_eq_zero.1 this
    -- the transverse coordinates agree
    have htrans : ∀ c, c ≠ k → (i c).val = (j c).val := by
      intro c hc
      have h0 := hrest c hc
      rw [hxc c hc] at h0
      have hic : ((i c).val : ℤ) < (2 * N : ℤ) := by exact_mod_cast ZMod.val_lt (i c)
      have hjc : ((j c).val : ℤ) < (2 * N : ℤ) := by exact_mod_cast ZMod.val_lt (j c)
      have hic0 : (0 : ℤ) ≤ ((i c).val : ℤ) := Int.natCast_nonneg _
      have hjc0 : (0 : ℤ) ≤ ((j c).val : ℤ) := Int.natCast_nonneg _
      have hlc : ℓ c = 0 := by
        rcases lt_trichotomy (ℓ c) 0 with h | h | h
        · exfalso; nlinarith
        · exact h
        · exfalso; nlinarith
      rw [hlc] at h0
      have : ((i c).val : ℤ) = ((j c).val : ℤ) := by linarith
      exact_mod_cast this
    -- and so do the `k`-th ones
    have hkk : (i k).val = (j k).val := by
      have hpm : x k = 1 ∨ x k = -1 := by
        rcases Int.natAbs_eq (x k) with h | h <;> rw [hone] at h <;> simp [h]
      have key : ((i k).val : ℤ) = ((j k).val : ℤ) := by
        rcases hpm with h | h
        · rw [hxk] at h
          have h1 : ((i k).val : ℤ) + ((j k).val : ℤ)
              = (2 * N : ℤ) * (1 + ℓ k) - 2 := by linarith
          have h2 : (2 : ℤ) ≤ (2 * N : ℤ) * (1 + ℓ k) := by linarith
          have h3 : (2 * N : ℤ) * (1 + ℓ k) ≤ (2 * N : ℤ) := by linarith
          have h4 : (1 : ℤ) ≤ 1 + ℓ k := by nlinarith
          have h5 : 1 + ℓ k ≤ 1 := by nlinarith
          have h6 : 1 + ℓ k = 1 := le_antisymm h5 h4
          rw [h6] at h1
          linarith
        · rw [hxk] at h
          have h1 : ((i k).val : ℤ) + ((j k).val : ℤ) = (2 * N : ℤ) * (1 + ℓ k) := by linarith
          have h2 : (0 : ℤ) ≤ (2 * N : ℤ) * (1 + ℓ k) := by linarith
          have h3 : (2 * N : ℤ) * (1 + ℓ k) ≤ (2 * N : ℤ) - 2 := by linarith
          have h4 : (0 : ℤ) ≤ 1 + ℓ k := by nlinarith
          have h5 : 1 + ℓ k ≤ 0 := by nlinarith
          have h6 : 1 + ℓ k = 0 := le_antisymm h5 h4
          rw [h6] at h1
          linarith
      exact_mod_cast key
    exact eq_of_crossingIndex_eq_zero htrans hkk
  calc ∑' ℓ : Fin d → ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • ℓ)
      = ∑' _ : Fin d → ℤ, (0 : ℝ) := tsum_congr hzero
    _ = 0 := tsum_zero

/-- **The crossing matrix of a ferromagnetic nearest-neighbour coupling is positive
semidefinite**, being diagonal with nonnegative entries. -/
theorem posSemidef_crossingMatrix_nearestNeighbour
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0) (hpos : ∀ m, 0 ≤ J m) :
    (crossingMatrix N J k).PosSemidef := by
  classical
  have hdiag : crossingMatrix N J k
      = Matrix.diagonal fun i ↦ crossingMatrix N J k i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : (i k).val < N
      · by_cases hj : (j k).val < N
        · exact crossingMatrix_eq_zero_of_nearestNeighbour hsupp hi hj hij
        · exact crossingMatrix_eq_zero fun h ↦ hj h.2
      · exact crossingMatrix_eq_zero fun h ↦ hi h.1
  rw [hdiag]
  exact Matrix.PosSemidef.diagonal fun i ↦ crossingMatrix_nonneg hpos i i

/-- **Georgii, Example (17.30).**  For a ferromagnetic nearest-neighbour Heisenberg potential —
`J` even, supported on the bonds `|i| = 1` and nonnegative — the Gibbs distribution in the torus
with periodic boundary condition is `r_k`-positive, for every direction `k`. -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour
    (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0) (hpos : ∀ m, 0 ≤ J m)
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) :=
  isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef heven
    (flipCoord_eq_of_nearestNeighbour hsupp heven)
    (posSemidef_crossingMatrix_nearestNeighbour hsupp hpos) ν hint

/-- **Georgii, Example (17.31).**  For a next-nearest neighbour Heisenberg potential — `J(i) = A`
if `|i|² = 1`, `B` if `|i|² = 2`, `0` if `|i|² > 2` — with `A ≥ 2(d-1)|B|`, the Gibbs distribution
in the torus with periodic boundary condition is `r_k`-positive, in every direction `k`.

Georgii's remark that *no* restriction on `A` and `B` is needed for `r̂_k`-positivity is
`isReflectionPositive_hatReflection_periodicGibbs` (Theorem (17.21)) applied to the equivalent
`C`-potential of Comment (17.19)(2). -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour {A B : ℝ}
    (hsum : Summable J) (heven : ∀ m, J (-m) = J m)
    (hAB : 2 * ((d : ℝ) - 1) * |B| ≤ A)
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) :=
  isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt hsum heven
    (isNonnegDefiniteAt_of_nextNearestNeighbour hAB hJ1 hJ2 hJ0) ν hint

end Heisenberg

end MeasureTheory.GibbsMeasure

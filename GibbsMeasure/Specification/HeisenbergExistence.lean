/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Integral.MarginalComparison
public import GibbsMeasure.Specification.HeisenbergClusterPoints
public import GibbsMeasure.Specification.NetEquicontinuity

/-!
# Georgii, Proposition (20.7): `𝒢₀(Φ) ≠ ∅`

`GibbsMeasure.Specification.HeisenbergClusterPoints` builds Georgii's fields
`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_{0_{S∖Λ(n)}}` of §20.1, their set of cluster points `𝒢₀(Φ)`, Lemma (20.6)
for both, and the shift invariance of `𝒢₀(Φ)`.  This file proves the **first half of
Proposition (20.7)**, `𝒢₀(Φ) ≠ ∅`, and the two computations that Georgii's proof of the second half
`𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)` rests on.

## `𝒢₀(Φ) ≠ ∅`

Georgii's proof is: "A straightforward calculation shows that
`limsup_n sup_{ω ∈ Ω_t} ρ_Λ^n(ω) < ∞` for all `Λ ∈ 𝒮` and `t ≥ 1`. Lemma (20.6)(iii) therefore
implies that the sequence `(μ_n^Φ)` satisfies the hypotheses of Theorem (4.12)."  Here:

* `MeasureTheory.GibbsMeasure.blockEnergyBound` and
  `abs_heisenbergExponent_sub_updateFinset_zero_le` — the **energy of a block `P` of the torus**:
  zeroing the spins of `P` changes the exponent of (17.24) by at most
  `∑_{i ∈ P} |σ_i| ∑_{j ∈ Λ} |J_Λ(i-j)| |σ_j|`.
* `blockEnergyBound_le_of_mem_torusSlowGrowthSet` and
  `blockEnergyBound_le_of_mem_torusSlowGrowthSetOff` — the **two estimates on that energy**, over
  `Ω_t` and over its exterior part.  Both constants depend only on the *representatives* in
  `Λ(N)` of the sites of the block, so they do not see the cube; this is the uniformity in `n`,
  and it is exactly where (20.4) enters, through
  `sum_abs_periodizedCoupling_mul_slowGrowth_le`.
* `heisenbergPeriodicGibbsDist_inter_torusSlowGrowthSet_le` — **Georgii's density bound on the
  torus**: `°γ_Λ^Φ(A ∩ Ω_t) ≤ e^κ δ(c)^{-|P|} λ^P(A_P)` for `A ∈ 𝓕_P`.  It is proved directly on
  the explicit density (17.24), by resampling the block `P`
  (`MeasureTheory.const_mul_lintegral_le_of_lmarginal`); the exterior integral, which is where the
  cube enters, cancels between the upper bound on `Ω_t` and the Gaussian lower bound.  No
  finite-volume Gibbs *specification* for the periodic modification is needed.
* `heisenbergPeriodicField_inter_slowGrowthSet_le` — the same bound **on `ℤ^d`, for `μ_n^Φ`**, with
  the two constants written out in terms of `Λ`, `t` and `J` only.
* `locallyEquicontinuous_of_eventually_measure_inter_le` in
  `GibbsMeasure.Specification.NetEquicontinuity` — **Theorem (4.12) in the form its proof uses**:
  a bound `μₐ(A ∩ B) ≤ κ(A)` on `𝓕_Λ` for a finite measure `κ`, plus `limsup μₐ(Bᶜ) ≤ ε`.
  Georgii's own statement is derived from it, and it is what makes (4.12) applicable to the fields
  `μ_n^Φ`, which are not presented as `νₐ γ^a_{Λₐ}`.
* `heisenbergGZero_nonempty` — **Georgii, Proposition (20.7), first half**.

## Towards `𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`: Georgii's `Φ^n` and `H_Λ^{Φ^n - Φ}`

* `hamiltonian_heisenbergPeriodicPotential_eq_sub` — **`H_Λ^{Φ^n}` is the block energy of the
  torus** for every volume `Λ` inside the cube:
  `H_Λ^{Φ^n}(σ) = E(σ with the block zeroed) - E(σ)`.  Georgii's (2.6)
  (`Potential.hamiltonian_sub_eq_of_mem`) reduces `Λ` to the cube, where the Hamiltonian is minus
  the exponent of (17.24).
* `exists_abs_hamiltonian_heisenbergPeriodicPotential_le` and
  `isSigmaFiniteLambdaAdmissible_heisenbergPeriodicPotential` — **Georgii's `Φ^n` is
  `λ`-admissible**: `0 < Z_Λ^{Φ^n}(ω) < ∞` in every volume and at every boundary condition.  So
  `heisenbergPeriodicGibbsSpec` is a genuine specification `γ^n`, and Georgii's
  `μ_n^Φ = γ_{Λ(n)}^n(·|0)` (`heisenbergPeriodicGibbsSpec_latticeBox`) satisfies the DLR equation
  `μ_n^Φ γ_Λ^n = μ_n^Φ` for every `Λ ⊆ Λ(n)` by consistency.
* `couplingTail`, `sum_abs_periodizedCoupling_sub_mul_slowGrowth_le` and `tendsto_couplingTail` —
  **Georgii's "By (20.4) and a short calculation, we can find a null sequence `(δ_n)`"**.  The
  `α`-weighted periodisation error `∑_{j ∈ Λ(N)} |J_{Λ(N)}(i-j) - J(i-j)| α(j)` is at most the
  `α`-weighted tail `∑_{m ∉ Λ(N)} |J(i-m)| α(m)` of the coupling, which tends to `0`.  The proof
  is the fibre decomposition, with `norm_le_norm_of_latticeToTorus_eq` supplying `α(j) ≤ α(m)`
  for `m ≡ j`, `j ∈ Λ(N)`.
* `couplingDiff`, `abs_hamiltonian_heisenbergPeriodicPotential_sub_le` and
  `abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le` — **Georgii's
  `sup_{ω ∈ Ω_t} |H_Λ^{Φ^n - Φ}(ζ ω_{S∖Λ})| ≤ δ_n ∑_{i∈Λ}[1 + |ζ_i|²]`**, with the explicit null
  sequence `δ_n = 4(1+t) ∑_{i ∈ Λ} ∑_{m ∉ Λ(n)} |J(i-m)| α(m)` (`tendsto_sum_couplingTail`).  Only
  the exterior spins are constrained, as in Georgii's statement, where `ζ ∈ E^Λ` is arbitrary.  The
  interaction terms of `Φ^n - Φ` are a pair family with the inhomogeneous coefficient
  `couplingDiff`, and `abs_tsum_le_of_pairBound` together with `sum_mul_tsum_le_of_exterior_le` of
  `GibbsMeasure.Specification.HeisenbergSpecification` — the general form of the majorant
  argument behind `abs_hamiltonian_heisenbergPotential_le_of_exterior_le` — bound their sum.

## `𝒢₀(Φ) ⊆ 𝒢_Θ(Φ)`

The shift invariance of `𝒢₀(Φ)` is `measurePreserving_shift_of_mem_heisenbergGZero`
(`HeisenbergClusterPoints`), and `𝒢₀(Φ) ⊆ 𝒢(Φ)` is
`heisenbergGZero_subset_heisenbergGibbsMeasures` in
`GibbsMeasure.Specification.HeisenbergGibbsInclusion`, which takes its two model-specific inputs
from this file:

1. **Proposition (4.19) restricted to `Ω_t`**, `‖(γ_Λ^n f - γ_Λ^Φ f) 1_{Ω_t}‖ → 0`.  In the form
   used it is a statement about two finite-volume Gibbs kernels in the same volume with the same
   boundary condition and the same a priori measure (`MeasureTheory.abs_expTilt_sub_le`): writing
   `Q(v) = ∑_{i ∈ Λ}[1 + |v_i|²]`, `K_i(A) = ∫_A e^{-H_i} dλ^Λ / ∫ e^{-H_i} dλ^Λ`, if
   `|H₂| ≤ c Q` and `|H₁ - H₂| ≤ δ Q` with `0 ≤ δ ≤ 1`, then
   `|K₁(A) - K₂(A)| ≤ 4 Γ δ / β` as soon as `δ Γ ≤ β/2`, where
   `β = ∫ e^{-cQ} dλ^Λ > 0` and `Γ = ∫ e^{(c+2)Q} dλ^Λ < ∞` by (20.3).  Its two hypotheses are
   `|H_Λ^Φ| ≤ c Q` uniformly over `Ω_t`
   (`abs_hamiltonian_heisenbergPotential_le_of_exterior_le`) and
   `|H_Λ^{Φ^n} - H_Λ^Φ| ≤ δ_n Q`
   (`abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le`).
2. **The `ε`-assembly**, which uses `locallyEquicontinuous_heisenbergPeriodicField` below through
   Georgii (4.15) (`MeasureTheory.GibbsMeasure.exists_strictMono_tendsto_of_mapClusterPt`), the
   DLR equation `μ_n^Φ γ_Λ^n = μ_n^Φ` (consistency of `heisenbergPeriodicGibbsSpec` and
   `heisenbergPeriodicGibbsSpec_latticeBox`), and the finite range of `Φ^m`, which makes
   `γ_Λ^m 1_A` a bounded local function.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Matrix MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The energy of a block of sites of the torus -/

section BlockEnergy

variable {d N : ℕ} [NeZero N] {n : ℕ} {J : (Fin d → ℤ) → ℝ}

variable (N n J) in
/-- **The energy of the block `P`**: the bound

`∑_{i ∈ P} |σ_i| ∑_{j ∈ Λ} |J_Λ(i-j)| |σ_j|`

for the part of Georgii's exponent (17.24) which is destroyed by setting the spins in `P` to
zero.  It is the torus form of the Hamiltonian `H_P^{Φ^n}` of the periodic modification in the
volume `P`. -/
def blockEnergyBound (P : Finset (Fin d → ZMod (2 * N)))
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : ℝ :=
  ∑ i ∈ P, Real.sqrt (ζ i ⬝ᵥ ζ i)
    * ∑ j, |periodizedCoupling N J (i - j)| * Real.sqrt (ζ j ⬝ᵥ ζ j)

lemma blockEnergyBound_nonneg (P : Finset (Fin d → ZMod (2 * N)))
    (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) : 0 ≤ blockEnergyBound N n J P ζ :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Real.sqrt_nonneg _)
    (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))

/-- **The energy of a block, in Georgii's exponent (17.24).**  Zeroing the spins on a block `P`
of the torus changes the exponent of (17.24) by at most `blockEnergyBound`.  This is the estimate
that makes the finite-volume conditional densities of `°γ_Λ^Φ` in a *fixed* volume `P` bounded
uniformly in the cube: nothing on the right-hand side sees the cube except through the periodised
coupling, whose `α`-weighted row sums are dominated by those of `J` itself
(`sum_abs_periodizedCoupling_mul_slowGrowth_le`). -/
theorem abs_heisenbergExponent_sub_updateFinset_zero_le (heven : ∀ m, J (-m) = J m)
    (P : Finset (Fin d → ZMod (2 * N))) (ζ : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    |heisenbergExponent N n J ζ
        - heisenbergExponent N n J (Function.updateFinset ζ P 0)|
      ≤ blockEnergyBound N n J P ζ := by
  classical
  set ζ0 : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) := Function.updateFinset ζ P 0 with hζ0def
  set s : (Fin d → ZMod (2 * N)) → ℝ := fun k ↦ Real.sqrt (ζ k ⬝ᵥ ζ k) with hsdef
  have hs0 : ∀ k, 0 ≤ s k := fun k ↦ Real.sqrt_nonneg _
  have hζ0 : ∀ k, ζ0 k = if k ∈ P then 0 else ζ k := by
    intro k
    by_cases hk : k ∈ P <;> simp [hζ0def, Function.updateFinset, hk]
  -- the spin lengths of the zeroed configuration, and of the difference
  have hdiffs : ∀ k, Real.sqrt ((ζ k - ζ0 k) ⬝ᵥ (ζ k - ζ0 k)) = if k ∈ P then s k else 0 := by
    intro k
    by_cases hk : k ∈ P <;> simp [hζ0, hk, hsdef]
  have hζ0s : ∀ k, Real.sqrt (ζ0 k ⬝ᵥ ζ0 k) ≤ s k := by
    intro k
    by_cases hk : k ∈ P
    · simp [hζ0, hk, hs0 k]
    · simp [hζ0, hk, hsdef]
  -- the difference of the exponents as a double sum
  have hdiff : heisenbergExponent N n J ζ - heisenbergExponent N n J ζ0
      = (∑ i, ∑ j, periodizedCoupling N J (i - j) * (ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j)) / 2 := by
    rw [heisenbergExponent, heisenbergExponent, ← sub_div]
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
  -- the pointwise estimate
  have hpt : ∀ i j, |periodizedCoupling N J (i - j) * (ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j)|
      ≤ |periodizedCoupling N J (i - j)| * ((if i ∈ P then s i else 0) * s j)
        + |periodizedCoupling N J (i - j)| * (s i * (if j ∈ P then s j else 0)) := by
    intro i j
    have hsplit : ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j
        = (ζ i - ζ0 i) ⬝ᵥ ζ j + ζ0 i ⬝ᵥ (ζ j - ζ0 j) := by
      rw [sub_dotProduct, dotProduct_sub]; ring
    have h1 : |(ζ i - ζ0 i) ⬝ᵥ ζ j| ≤ (if i ∈ P then s i else 0) * s j := by
      have := Matrix.abs_dotProduct_le_sqrt_mul_sqrt (ζ i - ζ0 i) (ζ j)
      rwa [hdiffs i] at this
    have h2 : |ζ0 i ⬝ᵥ (ζ j - ζ0 j)| ≤ s i * (if j ∈ P then s j else 0) := by
      have h := Matrix.abs_dotProduct_le_sqrt_mul_sqrt (ζ0 i) (ζ j - ζ0 j)
      rw [hdiffs j] at h
      refine h.trans (mul_le_mul_of_nonneg_right (hζ0s i) ?_)
      by_cases hj : j ∈ P <;> simp [hj, hs0 j]
    rw [abs_mul, hsplit]
    calc |periodizedCoupling N J (i - j)| * |(ζ i - ζ0 i) ⬝ᵥ ζ j + ζ0 i ⬝ᵥ (ζ j - ζ0 j)|
        ≤ |periodizedCoupling N J (i - j)|
            * (|(ζ i - ζ0 i) ⬝ᵥ ζ j| + |ζ0 i ⬝ᵥ (ζ j - ζ0 j)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ |periodizedCoupling N J (i - j)|
            * ((if i ∈ P then s i else 0) * s j + s i * (if j ∈ P then s j else 0)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) (abs_nonneg _)
      _ = _ := by ring
  -- the two halves of the double sum
  have hhalf1 : ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * ((if i ∈ P then s i else 0) * s j)
      = blockEnergyBound N n J P ζ := by
    rw [blockEnergyBound]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ i ∈ P)]
    have h2 : ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ P),
        ∑ j, |periodizedCoupling N J (i - j)| * ((if i ∈ P then s i else 0) * s j) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by
        simp only [Finset.mem_filter] at hi
        simp [hi.2]
    rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by simp only [hi, ite_true, hsdef]; ring
  have hhalf2 : ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * (s i * (if j ∈ P then s j else 0))
      = blockEnergyBound N n J P ζ := by
    rw [Finset.sum_comm, blockEnergyBound]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j ↦ j ∈ P)]
    have h2 : ∑ j ∈ Finset.univ.filter (fun j ↦ j ∉ P),
        ∑ i, |periodizedCoupling N J (i - j)| * (s i * (if j ∈ P then s j else 0)) = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by
        simp only [Finset.mem_filter] at hj
        simp [hj.2]
    rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsym : |periodizedCoupling N J (i - j)| = |periodizedCoupling N J (j - i)| := by
      rw [show j - i = -(i - j) by abel, periodizedCoupling_neg heven]
    simp only [hj, ite_true, hsym, hsdef]
    ring
  rw [hdiff, abs_div, abs_two]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc |∑ i, ∑ j, periodizedCoupling N J (i - j) * (ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j)|
      ≤ ∑ i, |∑ j, periodizedCoupling N J (i - j) * (ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |periodizedCoupling N J (i - j) * (ζ i ⬝ᵥ ζ j - ζ0 i ⬝ᵥ ζ0 j)| :=
        Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (|periodizedCoupling N J (i - j)| * ((if i ∈ P then s i else 0) * s j)
          + |periodizedCoupling N J (i - j)| * (s i * (if j ∈ P then s j else 0))) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
    _ = blockEnergyBound N n J P ζ * 2 := by
        simp only [Finset.sum_add_distrib]
        rw [hhalf1, hhalf2]; ring

end BlockEnergy

/-! ### Georgii's `Ω_t` on the torus -/

section TorusSlowGrowth

variable {d L n : ℕ} {J : (Fin d → ℤ) → ℝ}

variable (L n) in
/-- **Georgii's `Ω_t`, read on the torus** through the fundamental domain `Λ(N)`: the spin at a
torus site is compared with `t α(i)` at the representative `i ∈ Λ(N)` of that site. -/
def torusSlowGrowthSet (t : ℝ) : Set ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :=
  {ζ | ∀ k, ζ k ⬝ᵥ ζ k ≤ t ^ 2 * slowGrowth (torusToLattice L k) ^ 2}

variable (L n) in
/-- The part of `Ω_t` carried by the torus sites *outside* a block `P`: the condition that
survives when the spins in `P` are resampled. -/
def torusSlowGrowthSetOff (P : Finset (Fin d → ZMod (2 * (L + 1)))) (t : ℝ) :
    Set ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :=
  {ζ | ∀ k ∉ P, ζ k ⬝ᵥ ζ k ≤ t ^ 2 * slowGrowth (torusToLattice L k) ^ 2}

lemma torusSlowGrowthSet_subset_off (P : Finset (Fin d → ZMod (2 * (L + 1)))) (t : ℝ) :
    torusSlowGrowthSet L n t ⊆ torusSlowGrowthSetOff L n P t :=
  fun _ hζ k _ ↦ hζ k

lemma measurableSet_torusSlowGrowthSet (t : ℝ) :
    MeasurableSet (torusSlowGrowthSet L n (d := d) t) := by
  have h : torusSlowGrowthSet L n (d := d) t
      = ⋂ k, {ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ) |
          ζ k ⬝ᵥ ζ k ≤ t ^ 2 * slowGrowth (torusToLattice L k) ^ 2} := by
    ext ζ; simp [torusSlowGrowthSet]
  rw [h]
  exact MeasurableSet.iInter fun k ↦
    measurableSet_le ((measurable_pi_apply k).dotProduct (measurable_pi_apply k)) measurable_const

/-- The spin lengths of a slowly increasing torus configuration. -/
lemma sqrt_dotProduct_le_of_mem_torusSlowGrowthSet {t : ℝ} (ht : 0 ≤ t)
    {ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)} (hζ : ζ ∈ torusSlowGrowthSet L n t)
    (k : Fin d → ZMod (2 * (L + 1))) :
    Real.sqrt (ζ k ⬝ᵥ ζ k) ≤ t * slowGrowth (torusToLattice L k) := by
  have hsq : ζ k ⬝ᵥ ζ k ≤ (t * slowGrowth (torusToLattice L k)) ^ 2 := by
    have := hζ k; nlinarith
  calc Real.sqrt (ζ k ⬝ᵥ ζ k) ≤ Real.sqrt ((t * slowGrowth (torusToLattice L k)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = t * slowGrowth (torusToLattice L k) :=
        Real.sqrt_sq (mul_nonneg ht (slowGrowth_pos _).le)

/-- **Georgii's uniform bound on the block energy over `Ω_t`.**  On the slowly increasing
configurations the energy of a block `P` is bounded by a constant which depends only on the
*representatives* of the sites of `P` in `Λ(N)` — not otherwise on the cube.  This is the
uniformity in `n` of Georgii's `limsup_n sup_{ω ∈ Ω_t} ρ_Λ^n(ω) < ∞` in the proof of (20.7); it
rests on (20.4) through `sum_abs_periodizedCoupling_mul_slowGrowth_le`. -/
theorem blockEnergyBound_le_of_mem_torusSlowGrowthSet (hJ : IsSlowlySummable J)
    (P : Finset (Fin d → ZMod (2 * (L + 1)))) {t : ℝ} (ht : 0 ≤ t)
    {ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)} (hζ : ζ ∈ torusSlowGrowthSet L n t) :
    blockEnergyBound (L + 1) n J P ζ
      ≤ t ^ 2 * ∑ i ∈ P, slowGrowth (torusToLattice L i)
          * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k := by
  classical
  have hs := sqrt_dotProduct_le_of_mem_torusSlowGrowthSet ht hζ
  have hrow : ∀ i : Fin d → ZMod (2 * (L + 1)),
      ∑ j, |periodizedCoupling (L + 1) J (i - j)| * Real.sqrt (ζ j ⬝ᵥ ζ j)
        ≤ t * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k := by
    intro i
    have hdom := sum_abs_periodizedCoupling_mul_slowGrowth_le hJ L (torusToLattice L i)
    rw [latticeToTorus_torusToLattice] at hdom
    calc ∑ j, |periodizedCoupling (L + 1) J (i - j)| * Real.sqrt (ζ j ⬝ᵥ ζ j)
        ≤ ∑ j, |periodizedCoupling (L + 1) J (i - j)|
            * (t * slowGrowth (torusToLattice L j)) :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hs j) (abs_nonneg _)
      _ = t * ∑ j, |periodizedCoupling (L + 1) J (i - j)| * slowGrowth (torusToLattice L j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ t * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k :=
          mul_le_mul_of_nonneg_left hdom ht
  rw [blockEnergyBound, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have h1 : Real.sqrt (ζ i ⬝ᵥ ζ i) ≤ t * slowGrowth (torusToLattice L i) := hs i
  have h2 := hrow i
  have hinner0 : (0 : ℝ) ≤ ∑ j, |periodizedCoupling (L + 1) J (i - j)| * Real.sqrt (ζ j ⬝ᵥ ζ j) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (ζ i ⬝ᵥ ζ i)
        * ∑ j, |periodizedCoupling (L + 1) J (i - j)| * Real.sqrt (ζ j ⬝ᵥ ζ j)
      ≤ (t * slowGrowth (torusToLattice L i))
          * (t * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k) :=
        mul_le_mul h1 h2 hinner0 (mul_nonneg ht (slowGrowth_pos _).le)
    _ = t ^ 2 * (slowGrowth (torusToLattice L i)
          * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k) := by ring

/-- **The block energy off `Ω_t` is at most quadratic in the resampled spins.**  With only the
*exterior* of the block constrained, the energy of the block grows at most like
`c ∑_{i ∈ P}[1 + |σ_i|²]` — Georgii's estimate `|H_Λ^Φ(ω)| ≤ c(ω_{S∖Λ}) ∑_{i∈Λ}[1 + |ω_i|²]` of
§20.1, on the torus and uniformly in the cube.  Together with (20.3) it is what bounds the
partition function of the block from below. -/
theorem blockEnergyBound_le_of_exterior_le (hsum : Summable J)
    (P : Finset (Fin d → ZMod (2 * (L + 1))))
    {ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)} {β : (Fin d → ZMod (2 * (L + 1))) → ℝ}
    (hβ0 : ∀ v, 0 ≤ β v) (hβ : ∀ v ∉ P, Real.sqrt (ζ v ⬝ᵥ ζ v) ≤ β v) :
    blockEnergyBound (L + 1) n J P ζ
      ≤ ((∑' m, |J m|)
          + ∑ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v)
        * ∑ i ∈ P, (1 + ζ i ⬝ᵥ ζ i) := by
  classical
  set c : (Fin d → ZMod (2 * (L + 1))) → ℝ := fun z ↦ |periodizedCoupling (L + 1) J z| with hc
  have hc0 : ∀ z, 0 ≤ c z := fun z ↦ abs_nonneg _
  set s : (Fin d → ZMod (2 * (L + 1))) → ℝ := fun k ↦ Real.sqrt (ζ k ⬝ᵥ ζ k) with hs
  have hs0 : ∀ k, 0 ≤ s k := fun k ↦ Real.sqrt_nonneg _
  have hssq : ∀ k, s k ^ 2 = ζ k ⬝ᵥ ζ k := fun k ↦ Real.sq_sqrt (dotProduct_self_nonneg _)
  set M : ℝ := ∑ u ∈ P, ∑ v ∈ Pᶜ, c (u - v) * β v with hM
  have hMu : ∀ u ∈ P, ∑ v ∈ Pᶜ, c (u - v) * β v ≤ M :=
    fun u hu ↦ Finset.single_le_sum
      (fun u' _ ↦ Finset.sum_nonneg fun v _ ↦ mul_nonneg (hc0 _) (hβ0 v)) hu
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦ mul_nonneg (hc0 _) (hβ0 v)
  have hnorm0 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
  have hsplit : ∀ u, ∑ v, c (u - v) * s v
      = (∑ v ∈ P, c (u - v) * s v) + ∑ v ∈ Pᶜ, c (u - v) * s v := fun u ↦
    (Finset.sum_add_sum_compl P _).symm
  have hrowbd : ∀ u, ∑ v ∈ P, c (u - v) ≤ ∑' m, |J m| := fun u ↦
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P) fun v _ _ ↦ hc0 _)
      (sum_abs_periodizedCoupling_sub_le hsum u)
  have hcolbd : ∀ v, ∑ u ∈ P, c (u - v) ≤ ∑' m, |J m| := fun v ↦
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P) fun u _ _ ↦ hc0 _)
      (sum_abs_periodizedCoupling_sub_le' hsum v)
  -- the interior part
  have hA : ∑ u ∈ P, s u * ∑ v ∈ P, c (u - v) * s v
      ≤ (∑' m, |J m|) * ∑ u ∈ P, s u ^ 2 := by
    have key : ∑ u ∈ P, s u * ∑ v ∈ P, c (u - v) * s v
        = ∑ u ∈ P, ∑ v ∈ P, c (u - v) * (s u * s v) := by
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ ↦ by ring
    have hbd : ∑ u ∈ P, ∑ v ∈ P, c (u - v) * (s u * s v)
        ≤ ∑ u ∈ P, ∑ v ∈ P, (c (u - v) * s u ^ 2 / 2 + c (u - v) * s v ^ 2 / 2) := by
      refine Finset.sum_le_sum fun u _ ↦ Finset.sum_le_sum fun v _ ↦ ?_
      nlinarith [sq_nonneg (s u - s v), hc0 (u - v)]
    have erow : ∀ u, ∑ v ∈ P, c (u - v) * s u ^ 2 / 2
        = s u ^ 2 * (∑ v ∈ P, c (u - v)) / 2 := by
      intro u
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun v _ ↦ by ring
    have ecol : ∀ v, ∑ u ∈ P, c (u - v) * s v ^ 2 / 2
        = s v ^ 2 * (∑ u ∈ P, c (u - v)) / 2 := by
      intro v
      rw [Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun u _ ↦ by ring
    have esplit : ∑ u ∈ P, ∑ v ∈ P, (c (u - v) * s u ^ 2 / 2 + c (u - v) * s v ^ 2 / 2)
        = ∑ u ∈ P, s u ^ 2 * (∑ v ∈ P, c (u - v)) / 2
          + ∑ v ∈ P, s v ^ 2 * (∑ u ∈ P, c (u - v)) / 2 := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun u _ ↦ erow u
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun v _ ↦ ecol v
    have h1 : ∑ u ∈ P, s u ^ 2 * (∑ v ∈ P, c (u - v)) / 2
        ≤ ((∑' m, |J m|) * ∑ u ∈ P, s u ^ 2) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_le_sum fun u _ ↦ ?_
      have := mul_le_mul_of_nonneg_left (hrowbd u) (sq_nonneg (s u))
      linarith
    have h2 : ∑ v ∈ P, s v ^ 2 * (∑ u ∈ P, c (u - v)) / 2
        ≤ ((∑' m, |J m|) * ∑ u ∈ P, s u ^ 2) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_le_sum fun v _ ↦ ?_
      have := mul_le_mul_of_nonneg_left (hcolbd v) (sq_nonneg (s v))
      linarith
    rw [key]
    refine hbd.trans ?_
    rw [esplit]
    linarith
  -- the exterior part
  have hB : ∑ u ∈ P, s u * ∑ v ∈ Pᶜ, c (u - v) * s v ≤ M * ∑ u ∈ P, (1 + s u ^ 2) := by
    have hstep : ∀ u ∈ P, s u * ∑ v ∈ Pᶜ, c (u - v) * s v ≤ M * (1 + s u ^ 2) := by
      intro u hu
      have hout : ∑ v ∈ Pᶜ, c (u - v) * s v ≤ M := by
        refine le_trans (Finset.sum_le_sum fun v hv ↦ ?_) (hMu u hu)
        exact mul_le_mul_of_nonneg_left (hβ v (Finset.mem_compl.1 hv)) (hc0 _)
      have hout0 : (0 : ℝ) ≤ ∑ v ∈ Pᶜ, c (u - v) * s v :=
        Finset.sum_nonneg fun v _ ↦ mul_nonneg (hc0 _) (hs0 v)
      have hsu : s u ≤ 1 + s u ^ 2 := by nlinarith [sq_nonneg (s u - 1), hs0 u]
      calc s u * ∑ v ∈ Pᶜ, c (u - v) * s v ≤ s u * M :=
            mul_le_mul_of_nonneg_left hout (hs0 u)
        _ ≤ (1 + s u ^ 2) * M := mul_le_mul_of_nonneg_right hsu hM0
        _ = M * (1 + s u ^ 2) := by ring
    calc ∑ u ∈ P, s u * ∑ v ∈ Pᶜ, c (u - v) * s v ≤ ∑ u ∈ P, M * (1 + s u ^ 2) :=
          Finset.sum_le_sum hstep
      _ = M * ∑ u ∈ P, (1 + s u ^ 2) := (Finset.mul_sum P (fun u ↦ 1 + s u ^ 2) M).symm
  -- putting the two halves together
  have hsq0 : ∑ u ∈ P, s u ^ 2 ≤ ∑ u ∈ P, (1 + s u ^ 2) :=
    Finset.sum_le_sum fun u _ ↦ by linarith
  have hsum0 : (0 : ℝ) ≤ ∑ u ∈ P, (1 + s u ^ 2) :=
    Finset.sum_nonneg fun u _ ↦ by positivity
  have hkey : blockEnergyBound (L + 1) n J P ζ
      ≤ (∑' m, |J m|) * ∑ u ∈ P, s u ^ 2 + M * ∑ u ∈ P, (1 + s u ^ 2) := by
    rw [blockEnergyBound]
    have hrewrite : ∑ u ∈ P, s u * ∑ v, c (u - v) * s v
        = ∑ u ∈ P, s u * ∑ v ∈ P, c (u - v) * s v
          + ∑ u ∈ P, s u * ∑ v ∈ Pᶜ, c (u - v) * s v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ ↦ by rw [hsplit u]; ring
    simp only [hs, hc] at hrewrite ⊢
    rw [hrewrite]
    linarith [hA, hB]
  have hfin : (∑' m, |J m|) * ∑ u ∈ P, s u ^ 2 + M * ∑ u ∈ P, (1 + s u ^ 2)
      ≤ ((∑' m, |J m|) + M) * ∑ u ∈ P, (1 + s u ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsq0 hnorm0
    nlinarith
  have hrw : ∑ u ∈ P, (1 + s u ^ 2) = ∑ u ∈ P, (1 + ζ u ⬝ᵥ ζ u) :=
    Finset.sum_congr rfl fun u _ ↦ by rw [hssq u]
  rw [← hrw, hM]
  exact hkey.trans hfin

/-- **The block energy off `Ω_t` is at most quadratic in the resampled spins.**  With only the
*exterior* of the block constrained, the energy of a block grows at most like
`c ∑_{i ∈ P}[1 + |σ_i|²]` — Georgii's estimate `|H_Λ^Φ(ω)| ≤ c(ω_{S∖Λ}) ∑_{i∈Λ}[1 + |ω_i|²]` of
§20.1, on the torus and uniformly in the cube.  Together with (20.3) it is what bounds the
partition function of a block from below. -/
theorem blockEnergyBound_le_of_mem_torusSlowGrowthSetOff (hJ : IsSlowlySummable J)
    (P : Finset (Fin d → ZMod (2 * (L + 1)))) {t : ℝ} (ht : 0 ≤ t)
    {ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)}
    (hζ : ζ ∈ torusSlowGrowthSetOff L n P t) :
    blockEnergyBound (L + 1) n J P ζ
      ≤ ((∑' m, |J m|) + t * ∑ i ∈ P, ∑' k, |J (torusToLattice L i - k)| * slowGrowth k)
        * ∑ i ∈ P, (1 + ζ i ⬝ᵥ ζ i) := by
  classical
  set β : (Fin d → ZMod (2 * (L + 1))) → ℝ := fun v ↦ t * slowGrowth (torusToLattice L v) with hβdef
  have hβ0 : ∀ v, 0 ≤ β v := fun v ↦ mul_nonneg ht (slowGrowth_pos _).le
  have hβ : ∀ v ∉ P, Real.sqrt (ζ v ⬝ᵥ ζ v) ≤ β v := by
    intro v hv
    have hsq : ζ v ⬝ᵥ ζ v ≤ (t * slowGrowth (torusToLattice L v)) ^ 2 := by
      have := hζ v hv; nlinarith
    calc Real.sqrt (ζ v ⬝ᵥ ζ v) ≤ Real.sqrt ((t * slowGrowth (torusToLattice L v)) ^ 2) :=
          Real.sqrt_le_sqrt hsq
      _ = β v := Real.sqrt_sq (hβ0 v)
  refine (blockEnergyBound_le_of_exterior_le hJ.summable P hβ0 hβ).trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.sum_nonneg fun i _ ↦ by
      have := dotProduct_self_nonneg (ζ i); linarith)
  have hrow : ∀ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v
      ≤ t * ∑' k, |J (torusToLattice L u - k)| * slowGrowth k := by
    intro u _
    have hdom := sum_abs_periodizedCoupling_mul_slowGrowth_le hJ L (torusToLattice L u)
    rw [latticeToTorus_torusToLattice] at hdom
    calc ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v
        ≤ ∑ v, |periodizedCoupling (L + 1) J (u - v)| * β v :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun v _ _ ↦
            mul_nonneg (abs_nonneg _) (hβ0 v)
      _ = t * ∑ v, |periodizedCoupling (L + 1) J (u - v)| * slowGrowth (torusToLattice L v) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ ↦ by rw [hβdef]; ring
      _ ≤ t * ∑' k, |J (torusToLattice L u - k)| * slowGrowth k :=
          mul_le_mul_of_nonneg_left hdom ht
  have hle : ∑ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v
      ≤ ∑ u ∈ P, t * ∑' k, |J (torusToLattice L u - k)| * slowGrowth k :=
    Finset.sum_le_sum hrow
  rw [← Finset.mul_sum] at hle
  linarith

end TorusSlowGrowth

/-! ### Georgii's uniform density bound on the torus -/

section TorusDensityBound

variable {d L n : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- Georgii's `δ` of the proof of (20.6), at the rate `c`: the one-site weight
`∫ λ(dx) e^{-c(1 + |x|²)}`, which is positive because `λ ≠ 0` and at most `λ(E)` because the
integrand is at most `1`. -/
theorem lintegral_exp_neg_pos [IsFiniteMeasure ν] (hν : ν ≠ 0) (c : ℝ) :
    0 < ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) ∂ν := by
  have hmeas : Measurable fun y : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_const.add (Finset.measurable_sum _ fun cc _ ↦
        (measurable_pi_apply cc).mul (measurable_pi_apply cc))).const_mul c).neg))
  rw [lintegral_pos_iff_support hmeas]
  have hsupp : Function.support (fun y : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y))))) = Set.univ :=
    Set.eq_univ_of_forall fun y ↦ by
      simp [Function.mem_support, Real.exp_pos _]
  rw [hsupp]
  exact Measure.measure_univ_pos.2 hν

theorem lintegral_exp_neg_le [IsFiniteMeasure ν] {c : ℝ} (hc : 0 ≤ c) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) ∂ν) ≤ ν Set.univ := by
  calc (∫⁻ y, ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) ∂ν) ≤ ∫⁻ _y, 1 ∂ν := by
        refine lintegral_mono fun y ↦ ?_
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2
          (by nlinarith [dotProduct_self_nonneg y]))
    _ = ν Set.univ := by simp

/-- **The uniform density bound of Georgii's proof of Proposition (20.7).**  For a *fixed* block
`P` of the torus, a bound `κ` on the energy of the block over `Ω_t`, and a bound `c` on its growth
rate off `Ω_t`, the Gibbs distribution with periodic boundary condition satisfies

`°γ_Λ^Φ(A ∩ Ω_t) ≤ e^κ δ(c)^{-|P|} λ^P(A_P)`  for every `A ∈ 𝓕_P`,

with `δ(c) = ∫ λ(dx) e^{-c(1+|x|²)}`.  Nothing on the right-hand side depends on the cube except
through `κ`, `c` and `|P|`; this is what Georgii's `limsup_n sup_{ω ∈ Ω_t} ρ_Λ^n(ω) < ∞` supplies
to Theorem (4.12).

The proof is Georgii's, carried out directly on the explicit density (17.24): resample the block
`P` (`MeasureTheory.const_mul_lintegral_le_of_lmarginal`), bound the resampled density above on
`Ω_t` by `e^κ` times its value at the zero block, and below — for the *same* exterior — by the
Gaussian weight `δ(c)^{|P|}` times the same value.  The exterior integral, which is where the
cube enters, cancels between the two bounds. -/
theorem heisenbergPeriodicGibbsDist_inter_torusSlowGrowthSet_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hsum : Summable J)
    (P : Finset (Fin d → ZMod (2 * (L + 1)))) {t κ c : ℝ} (hc : 0 ≤ c)
    (hκ : ∀ ζ ∈ torusSlowGrowthSet L n t, blockEnergyBound (L + 1) n J P ζ ≤ κ)
    (hcbd : ∀ ζ ∈ torusSlowGrowthSetOff L n P t,
      blockEnergyBound (L + 1) n J P ζ ≤ c * ∑ i ∈ P, (1 + ζ i ⬝ᵥ ζ i))
    (ζ₀ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ))
    {A : Set ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ))}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ZMod (2 * (L + 1)) ↦ (Fin n → ℝ))
      (P : Set (Fin d → ZMod (2 * (L + 1))))] A) :
    heisenbergPeriodicGibbsDist (L + 1) n J ν (A ∩ torusSlowGrowthSet L n t)
      ≤ ENNReal.ofReal (Real.exp κ)
          * (Measure.pi fun _ : ↥P ↦ ν) (Function.updateFinset ζ₀ P ⁻¹' A)
          / (∫⁻ y, ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) ∂ν) ^ P.card := by
  classical
  -- notation
  set g : ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) → ℝ≥0∞ :=
    fun ζ ↦ ENNReal.ofReal (Real.exp (heisenbergExponent (L + 1) n J ζ)) with hg
  have hgmeas : Measurable g :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      measurable_heisenbergExponent)
  have hgtop : ∀ ζ, g ζ ≠ ∞ := fun ζ ↦ by rw [hg]; exact ENNReal.ofReal_ne_top
  set X : Set ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) := A ∩ torusSlowGrowthSet L n t with hX
  have hAmeas : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hXmeas : MeasurableSet X := hAmeas.inter (measurableSet_torusSlowGrowthSet t)
  set δ : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) ∂ν with hδ
  have hδ0 : δ ≠ 0 := (lintegral_exp_neg_pos hν c).ne'
  have hδtop : δ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν Set.univ) (lintegral_exp_neg_le hc)
  set mA : ℝ≥0∞ := (Measure.pi fun _ : ↥P ↦ ν) (Function.updateFinset ζ₀ P ⁻¹' A) with hmA
  have hmAtop : mA ≠ ∞ := measure_ne_top _ _
  set m : ℝ≥0∞ := ENNReal.ofReal (Real.exp κ) * mA with hm
  have hmtop : m ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmAtop
  set cc : ℝ≥0∞ := δ ^ P.card with hcc
  have hcc0 : cc ≠ 0 := pow_ne_zero _ hδ0
  have hcctop : cc ≠ ∞ := ENNReal.pow_ne_top hδtop
  -- the "exterior" weight
  set w : ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) → ℝ≥0∞ :=
    fun ζ ↦ (torusSlowGrowthSetOff L n P t).indicator
      (fun ζ' ↦ g (Function.updateFinset ζ' P 0)) ζ with hw
  have hw_mem : ∀ ζ ∈ torusSlowGrowthSetOff L n P t,
      w ζ = g (Function.updateFinset ζ P 0) := fun ζ hζ ↦ Set.indicator_of_mem hζ _
  have hw_notMem : ∀ ζ ∉ torusSlowGrowthSetOff L n P t, w ζ = 0 :=
    fun ζ hζ ↦ Set.indicator_of_notMem hζ _
  have hwtop : ∀ ζ, w ζ ≠ ∞ := by
    intro ζ
    by_cases hζ : ζ ∈ torusSlowGrowthSetOff L n P t
    · rw [hw_mem ζ hζ]; exact hgtop _
    · rw [hw_notMem ζ hζ]; exact ENNReal.zero_ne_top
  -- the exponent comparison at a fixed exterior
  have hzero : ∀ (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) (u : ↥P → (Fin n → ℝ)),
      Function.updateFinset (Function.updateFinset ζ P u) P 0 = Function.updateFinset ζ P 0 :=
    fun ζ u ↦ Function.updateFinset_updateFinset_of_subset (le_refl P) ζ u 0
  have hagree : ∀ (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) (u : ↥P → (Fin n → ℝ))
      (k : Fin d → ZMod (2 * (L + 1))), k ∉ P → Function.updateFinset ζ P u k = ζ k :=
    fun ζ u k hk ↦ by simp [Function.updateFinset, hk]
  have hoff : ∀ (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) (u : ↥P → (Fin n → ℝ)),
      (Function.updateFinset ζ P u ∈ torusSlowGrowthSetOff L n P t
        ↔ ζ ∈ torusSlowGrowthSetOff L n P t) := by
    intro ζ u
    constructor
    · intro h k hk
      have hk' := h k hk
      rwa [hagree ζ u k hk] at hk'
    · intro h k hk
      rw [hagree ζ u k hk]
      exact h k hk
  -- (a) the upper bound on the block
  have hupper : ∀ (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)),
      ∫⁻ u, X.indicator g (Function.updateFinset ζ P u) ∂(Measure.pi fun _ : ↥P ↦ ν)
        ≤ m * w ζ := by
    intro ζ
    have hpt : ∀ u : ↥P → (Fin n → ℝ),
        X.indicator g (Function.updateFinset ζ P u)
          ≤ (Function.updateFinset ζ₀ P ⁻¹' A).indicator
              (fun _ ↦ ENNReal.ofReal (Real.exp κ) * w ζ) u := by
      intro u
      by_cases hmem : Function.updateFinset ζ P u ∈ X
      · have hAmem : Function.updateFinset ζ P u ∈ A := hmem.1
        have hΩ : Function.updateFinset ζ P u ∈ torusSlowGrowthSet L n t := hmem.2
        have hoffζ : ζ ∈ torusSlowGrowthSetOff L n P t :=
          (hoff ζ u).1 (torusSlowGrowthSet_subset_off P t hΩ)
        have huA : u ∈ Function.updateFinset ζ₀ P ⁻¹' A := by
          refine (mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ ?_).1 hAmem
          have hiP : i ∈ P := by simpa using hi
          simp [Function.updateFinset, hiP]
        have hgle : g (Function.updateFinset ζ P u)
            ≤ ENNReal.ofReal (Real.exp κ) * g (Function.updateFinset ζ P 0) := by
          have hb := abs_heisenbergExponent_sub_updateFinset_zero_le heven P
            (Function.updateFinset ζ P u)
          rw [hzero ζ u] at hb
          have h1 := (abs_le.1 hb).2
          have h2 := hκ _ hΩ
          rw [hg]
          simp only
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem huA, hw_mem ζ hoffζ]
        exact hgle
      · rw [Set.indicator_of_notMem hmem]
        exact zero_le
    have hmeasA : MeasurableSet (Function.updateFinset ζ₀ P ⁻¹' A) :=
      measurable_updateFinset hAmeas
    calc ∫⁻ u, X.indicator g (Function.updateFinset ζ P u) ∂(Measure.pi fun _ : ↥P ↦ ν)
        ≤ ∫⁻ u, (Function.updateFinset ζ₀ P ⁻¹' A).indicator
            (fun _ ↦ ENNReal.ofReal (Real.exp κ) * w ζ) u
            ∂(Measure.pi fun _ : ↥P ↦ ν) := lintegral_mono hpt
      _ = m * w ζ := by
          rw [lintegral_indicator_const hmeasA, hm, hmA]
          ring
  -- (b) the lower bound on the block
  have hlower : ∀ (ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)),
      cc * w ζ ≤ ∫⁻ u, g (Function.updateFinset ζ P u) ∂(Measure.pi fun _ : ↥P ↦ ν) := by
    intro ζ
    by_cases hoffζ : ζ ∈ torusSlowGrowthSetOff L n P t
    · have hpt : ∀ u : ↥P → (Fin n → ℝ),
          (∏ i : ↥P, ENNReal.ofReal (Real.exp (-(c * (1 + u i ⬝ᵥ u i)))))
              * g (Function.updateFinset ζ P 0)
            ≤ g (Function.updateFinset ζ P u) := by
        intro u
        have hb := abs_heisenbergExponent_sub_updateFinset_zero_le heven P
          (Function.updateFinset ζ P u)
        rw [hzero ζ u] at hb
        have hmemoff : Function.updateFinset ζ P u ∈ torusSlowGrowthSetOff L n P t :=
          (hoff ζ u).2 hoffζ
        have hbc := hcbd _ hmemoff
        have hsumeq : ∑ i ∈ P, (1 + (Function.updateFinset ζ P u) i
              ⬝ᵥ (Function.updateFinset ζ P u) i)
            = ∑ i : ↥P, (1 + u i ⬝ᵥ u i) := by
          rw [← Finset.sum_coe_sort P fun i ↦ 1 + (Function.updateFinset ζ P u) i
            ⬝ᵥ (Function.updateFinset ζ P u) i]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hui : (Function.updateFinset ζ P u) (i : Fin d → ZMod (2 * (L + 1))) = u i := by
            simp [Function.updateFinset, i.2]
          rw [hui]
        rw [hsumeq] at hbc
        have h1 := (abs_le.1 hb).1
        have hprod : (∏ i : ↥P, ENNReal.ofReal (Real.exp (-(c * (1 + u i ⬝ᵥ u i)))))
            = ENNReal.ofReal (Real.exp (-(c * ∑ i : ↥P, (1 + u i ⬝ᵥ u i)))) := by
          rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ Real.exp_nonneg _, ← Real.exp_sum]
          congr 1
          simp [Finset.mul_sum]
        rw [hprod, hg]
        simp only
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
      have hmeasfac : ∀ _i : ↥P, Measurable fun y : Fin n → ℝ ↦
          ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y)))) := fun _ ↦
        ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
          (((measurable_const.add (Finset.measurable_sum _ fun cc _ ↦
            (measurable_pi_apply cc).mul (measurable_pi_apply cc))).const_mul c).neg))
      calc cc * w ζ = cc * g (Function.updateFinset ζ P 0) := by rw [hw_mem ζ hoffζ]
        _ = ∫⁻ u, (∏ i : ↥P, ENNReal.ofReal (Real.exp (-(c * (1 + u i ⬝ᵥ u i)))))
              * g (Function.updateFinset ζ P 0) ∂(Measure.pi fun _ : ↥P ↦ ν) := by
            rw [lintegral_mul_const' _ _ (hgtop _),
              lintegral_pi_prod (μ := fun _ : ↥P ↦ ν)
                (g := fun _ (y : Fin n → ℝ) ↦
                  ENNReal.ofReal (Real.exp (-(c * (1 + y ⬝ᵥ y))))) hmeasfac,
              hcc, hδ, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
        _ ≤ ∫⁻ u, g (Function.updateFinset ζ P u) ∂(Measure.pi fun _ : ↥P ↦ ν) :=
            lintegral_mono hpt
    · rw [hw_notMem ζ hoffζ, mul_zero]
      exact zero_le
  -- the marginal comparison
  have hmain : cc * ∫⁻ ζ, X.indicator g ζ ∂(Measure.pi fun _ : Fin d → ZMod (2 * (L + 1)) ↦ ν)
      ≤ m * ∫⁻ ζ, g ζ ∂(Measure.pi fun _ : Fin d → ZMod (2 * (L + 1)) ↦ ν) := by
    refine const_mul_lintegral_le_of_lmarginal (fun _ ↦ ν) P
      (hgmeas.indicator hXmeas) hgmeas hcctop hmtop fun ζ ↦ ?_
    calc cc * (∫⋯∫⁻_P, X.indicator g ∂(fun _ ↦ ν)) ζ ≤ cc * (m * w ζ) :=
          mul_le_mul' le_rfl (hupper ζ)
      _ = m * (cc * w ζ) := by ring
      _ ≤ m * (∫⋯∫⁻_P, g ∂(fun _ ↦ ν)) ζ := mul_le_mul' le_rfl (hlower ζ)
  -- rewriting both sides as measures
  have hZ : heisenbergPeriodicGibbs (L + 1) n J ν Set.univ
      = ∫⁻ ζ, g ζ ∂(Measure.pi fun _ : Fin d → ZMod (2 * (L + 1)) ↦ ν) := by
    rw [heisenbergPeriodicGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hnum : heisenbergPeriodicGibbs (L + 1) n J ν X
      = ∫⁻ ζ, X.indicator g ζ ∂(Measure.pi fun _ : Fin d → ZMod (2 * (L + 1)) ↦ ν) := by
    rw [heisenbergPeriodicGibbs, withDensity_apply _ hXmeas, lintegral_indicator hXmeas]
  have hint := integrable_exp_heisenbergExponent (N := L + 1) (d := d) (J := J) hexp hsum
  have hZfin : IsFiniteMeasure (heisenbergPeriodicGibbs (L + 1) n J ν) :=
    isFiniteMeasure_heisenbergPeriodicGibbs hint
  have hZpos : 0 < heisenbergPeriodicGibbs (L + 1) n J ν Set.univ :=
    heisenbergPeriodicGibbs_univ_pos hν
  have hZtop : heisenbergPeriodicGibbs (L + 1) n J ν Set.univ ≠ ∞ := measure_ne_top _ _
  rw [← hZ, ← hnum] at hmain
  have hnum_le : heisenbergPeriodicGibbs (L + 1) n J ν X
      ≤ cc⁻¹ * (m * heisenbergPeriodicGibbs (L + 1) n J ν Set.univ) := by
    calc heisenbergPeriodicGibbs (L + 1) n J ν X
        = cc⁻¹ * (cc * heisenbergPeriodicGibbs (L + 1) n J ν X) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hcc0 hcctop, one_mul]
      _ ≤ cc⁻¹ * (m * heisenbergPeriodicGibbs (L + 1) n J ν Set.univ) :=
          mul_le_mul' le_rfl hmain
  rw [heisenbergPeriodicGibbsDist, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.div_eq_inv_mul]
  calc (heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)⁻¹
        * heisenbergPeriodicGibbs (L + 1) n J ν X
      ≤ (heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)⁻¹
        * (cc⁻¹ * (m * heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)) :=
        mul_le_mul' le_rfl hnum_le
    _ = cc⁻¹ * m := by
        rw [show (heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)⁻¹
              * (cc⁻¹ * (m * heisenbergPeriodicGibbs (L + 1) n J ν Set.univ))
            = (cc⁻¹ * m) * ((heisenbergPeriodicGibbs (L + 1) n J ν Set.univ)⁻¹
              * heisenbergPeriodicGibbs (L + 1) n J ν Set.univ) by ring,
          ENNReal.inv_mul_cancel hZpos.ne' hZtop, mul_one]

end TorusDensityBound

/-! ### The density bound on `ℤ^d`, for Georgii's fields `μ_n^Φ` -/

section Transfer

variable {d n L : ℕ} {J : (Fin d → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- On the cube `Λ(N)` the representative of the reduction of a site is the site itself. -/
lemma torusToLattice_latticeToTorus {i : Fin d → ℤ} (hi : i ∈ Potential.latticeBox d L) :
    torusToLattice L (latticeToTorus L i) = i :=
  latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 (torusToLattice_mem _))
    (Finset.mem_coe.2 hi) (latticeToTorus_torusToLattice _)

/-- **`Ω_t` pulls back to its torus form.**  The field `μ_n^Φ` sees `Ω_t` only through the spins in
the cube, where the periodic continuation reads the torus configuration; outside the cube the spins
vanish and the condition is vacuous. -/
lemma preimage_periodicJuxt_zero_slowGrowthSet {t : ℝ} :
    periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹' (slowGrowthSet d n t)
      = torusSlowGrowthSet L n t := by
  ext ζ
  simp only [Set.mem_preimage, slowGrowthSet, torusSlowGrowthSet, Set.mem_ofPred_eq]
  constructor
  · intro h k
    have hk := h (torusToLattice L k)
    rwa [periodicJuxt_apply_of_mem ζ (torusToLattice_mem k),
      latticeToTorus_torusToLattice] at hk
  · intro h i
    by_cases hi : i ∈ periodicCube d L
    · rw [periodicJuxt_apply_of_mem ζ hi]
      have hki := h (latticeToTorus L i)
      rwa [torusToLattice_latticeToTorus hi] at hki
    · rw [periodicJuxt_apply_of_notMem ζ hi]
      simp only [Pi.zero_apply, zero_dotProduct]
      positivity

/-- **The periodic continuation transports the finite-volume σ-algebras.**  For a volume `Λ` inside
the cube, an event of `𝓕_Λ` on `ℤ^d` pulls back to an event of `𝓕_{Λ mod 2N}` on the torus. -/
lemma measurable_periodicJuxt_cylinderEvents {Λ : Finset (Fin d → ℤ)}
    (hΛ : Λ ⊆ Potential.latticeBox d L) (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    Measurable[cylinderEvents (X := fun _ : Fin d → ZMod (2 * (L + 1)) ↦ (Fin n → ℝ))
        ((Λ.image (latticeToTorus L) : Finset (Fin d → ZMod (2 * (L + 1))))
          : Set (Fin d → ZMod (2 * (L + 1)))),
      cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ)) (Λ : Set (Fin d → ℤ))]
      (periodicJuxt (Fin n → ℝ) L ω) := by
  classical
  let _ : MeasurableSpace ((Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) :=
    cylinderEvents (X := fun _ : Fin d → ZMod (2 * (L + 1)) ↦ (Fin n → ℝ))
      ((Λ.image (latticeToTorus L) : Finset (Fin d → ZMod (2 * (L + 1))))
        : Set (Fin d → ZMod (2 * (L + 1))))
  rw [measurable_iff_comap_le,
    cylinderEvents_eq_comap_domRestrict (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
      (Λ : Set (Fin d → ℤ)), MeasurableSpace.comap_comp]
  refine Measurable.comap_le (measurable_pi_lambda _ fun j ↦ ?_)
  have hjΛ : (j : Fin d → ℤ) ∈ Λ := j.2
  have hjcube : (j : Fin d → ℤ) ∈ Potential.latticeBox d L := hΛ hjΛ
  have hjP : latticeToTorus L (j : Fin d → ℤ)
      ∈ ((Λ.image (latticeToTorus L) : Finset (Fin d → ZMod (2 * (L + 1))))
        : Set (Fin d → ZMod (2 * (L + 1)))) := by
    simpa using Finset.mem_image_of_mem (latticeToTorus L) hjΛ
  have heq : ∀ ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ),
      ((Λ : Set (Fin d → ℤ)).domRestrict ∘ periodicJuxt (Fin n → ℝ) L ω) ζ j
        = ζ (latticeToTorus L (j : Fin d → ℤ)) :=
    fun ζ ↦ periodicJuxt_apply_of_mem ζ hjcube
  simp only [heq]
  exact measurable_cylinderEvent_apply (X := fun _ : Fin d → ZMod (2 * (L + 1)) ↦ (Fin n → ℝ)) hjP

/-- **Georgii's density bound for the fields `μ_n^Φ`, on `ℤ^d` and uniformly in the cube.**
For every finite volume `Λ`, every `t` and every `A ∈ 𝓕_Λ`,

`μ_n^Φ(A ∩ Ω_t) ≤ e^{κ(Λ,t)} δ(c(Λ,t))^{-|Λ|} λ^Λ(A_Λ)`   for every cube containing `Λ`,

with the two constants

`κ(Λ,t) = t² ∑_{i ∈ Λ} α(i) ∑_k |J(i-k)| α(k)`,
`c(Λ,t) = ‖J‖₀ + t ∑_{i ∈ Λ} ∑_k |J(i-k)| α(k)`,

which depend on `J`, `Λ` and `t` alone.  This is exactly Georgii's
`limsup_n sup_{ω ∈ Ω_t} ρ_Λ^n(ω) < ∞` in the proof of (20.7), in the form Theorem (4.12) uses it,
and it is where hypothesis (20.4) is needed. -/
theorem heisenbergPeriodicField_inter_slowGrowthSet_le [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ : IsSlowlySummable J)
    {Λ : Finset (Fin d → ℤ)} (hΛ : Λ ⊆ Potential.latticeBox d L) {t : ℝ} (ht : 0 ≤ t)
    {A : Set ((Fin d → ℤ) → (Fin n → ℝ))}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Fin d → ℤ ↦ (Fin n → ℝ))
      (Λ : Set (Fin d → ℤ))] A) :
    heisenbergPeriodicField J ν L 0 (A ∩ slowGrowthSet d n t)
      ≤ ENNReal.ofReal (Real.exp (t ^ 2 * ∑ i ∈ Λ, slowGrowth i
            * ∑' k, |J (i - k)| * slowGrowth k))
          * (Measure.pi fun _ : ↥Λ ↦ ν)
              (Function.updateFinset (0 : (Fin d → ℤ) → (Fin n → ℝ)) Λ ⁻¹' A)
          / (∫⁻ y, ENNReal.ofReal (Real.exp (-(((∑' m, |J m|)
              + t * ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k) * (1 + y ⬝ᵥ y)))) ∂ν) ^ Λ.card := by
  classical
  have hsum : Summable J := hJ.summable
  set P : Finset (Fin d → ZMod (2 * (L + 1))) := Λ.image (latticeToTorus L) with hP
  have hinjOn : Set.InjOn (latticeToTorus L) (Λ : Set (Fin d → ℤ)) := fun i hi j hj h ↦
    latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 (hΛ (Finset.mem_coe.1 hi)))
      (Finset.mem_coe.2 (hΛ (Finset.mem_coe.1 hj))) h
  have hcard : P.card = Λ.card := Finset.card_image_of_injOn hinjOn
  -- the two sums over the block are sums over `Λ`
  have hsumrep : ∀ f : (Fin d → ℤ) → ℝ, ∑ i ∈ P, f (torusToLattice L i) = ∑ i ∈ Λ, f i := by
    intro f
    rw [hP, Finset.sum_image fun i hi j hj h ↦ hinjOn (Finset.mem_coe.2 hi) (Finset.mem_coe.2 hj) h]
    exact Finset.sum_congr rfl fun i hi ↦ by rw [torusToLattice_latticeToTorus (hΛ hi)]
  have hκeq : ∑ i ∈ P, slowGrowth (torusToLattice L i)
        * ∑' k, |J (torusToLattice L i - k)| * slowGrowth k
      = ∑ i ∈ Λ, slowGrowth i * ∑' k, |J (i - k)| * slowGrowth k :=
    hsumrep fun i ↦ slowGrowth i * ∑' k, |J (i - k)| * slowGrowth k
  have hceq : ∑ i ∈ P, ∑' k, |J (torusToLattice L i - k)| * slowGrowth k
      = ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k :=
    hsumrep fun i ↦ ∑' k, |J (i - k)| * slowGrowth k
  set κ : ℝ := t ^ 2 * ∑ i ∈ Λ, slowGrowth i * ∑' k, |J (i - k)| * slowGrowth k with hκ
  set c : ℝ := (∑' m, |J m|) + t * ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k with hcdef
  have hc0 : 0 ≤ c := by
    have h1 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
    have h2 : (0 : ℝ) ≤ ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k :=
      Finset.sum_nonneg fun i _ ↦ tsum_nonneg fun k ↦
        mul_nonneg (abs_nonneg _) (slowGrowth_pos k).le
    rw [hcdef]; positivity
  -- the hypotheses of the torus estimate
  have hκbd : ∀ ζ ∈ torusSlowGrowthSet L n t, blockEnergyBound (L + 1) n J P ζ ≤ κ := by
    intro ζ hζ
    have h := blockEnergyBound_le_of_mem_torusSlowGrowthSet (n := n) hJ P ht hζ
    rwa [hκeq] at h
  have hcbd : ∀ ζ ∈ torusSlowGrowthSetOff L n P t,
      blockEnergyBound (L + 1) n J P ζ ≤ c * ∑ i ∈ P, (1 + ζ i ⬝ᵥ ζ i) := by
    intro ζ hζ
    have h := blockEnergyBound_le_of_mem_torusSlowGrowthSetOff (n := n) hJ P ht hζ
    rwa [hceq] at h
  -- the event, on the torus
  have hAmeas : MeasurableSet A := cylinderEvents_le_pi _ hA
  have hXmeas : MeasurableSet (A ∩ slowGrowthSet d n t) :=
    hAmeas.inter (measurableSet_slowGrowthSet t)
  have hApre : MeasurableSet[cylinderEvents
      (X := fun _ : Fin d → ZMod (2 * (L + 1)) ↦ (Fin n → ℝ))
      (P : Set (Fin d → ZMod (2 * (L + 1))))]
      (periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹' A) :=
    measurable_periodicJuxt_cylinderEvents hΛ 0 hA
  have hpre : periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹'
        (A ∩ slowGrowthSet d n t)
      = (periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹' A)
        ∩ torusSlowGrowthSet L n t := by
    rw [Set.preimage_inter, preimage_periodicJuxt_zero_slowGrowthSet]
  -- the reindexing of the block measure
  have hbij : Function.Bijective
      (fun i : ↥Λ ↦ (⟨latticeToTorus L (i : Fin d → ℤ),
        Finset.mem_image_of_mem _ i.2⟩ : ↥P)) := by
    constructor
    · intro i j hij
      have h : latticeToTorus L (i : Fin d → ℤ) = latticeToTorus L (j : Fin d → ℤ) :=
        congrArg Subtype.val hij
      exact Subtype.ext (hinjOn (Finset.mem_coe.2 i.2) (Finset.mem_coe.2 j.2) h)
    · rintro ⟨z, hz⟩
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
      exact ⟨⟨i, hi⟩, rfl⟩
  set e : ↥Λ ≃ ↥P := Equiv.ofBijective _ hbij with he
  have hpreim : (MeasurableEquiv.piCongrLeft (fun _ : ↥P ↦ (Fin n → ℝ)) e) ⁻¹'
        (Function.updateFinset (0 : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) P ⁻¹'
          (periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹' A))
      = Function.updateFinset (0 : (Fin d → ℤ) → (Fin n → ℝ)) Λ ⁻¹' A := by
    ext v
    simp only [Set.mem_preimage]
    refine mem_congr_of_measurableSet_cylinderEvents hA fun i hi ↦ ?_
    have hiΛ : i ∈ Λ := by simpa using hi
    have hicube : i ∈ Potential.latticeBox d L := hΛ hiΛ
    have hiP : latticeToTorus L i ∈ P := Finset.mem_image_of_mem _ hiΛ
    rw [periodicJuxt_apply_of_mem _ hicube]
    have h1 : Function.updateFinset (0 : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) P
          ((MeasurableEquiv.piCongrLeft (fun _ : ↥P ↦ (Fin n → ℝ)) e) v)
          (latticeToTorus L i)
        = ((MeasurableEquiv.piCongrLeft (fun _ : ↥P ↦ (Fin n → ℝ)) e) v)
            ⟨latticeToTorus L i, hiP⟩ := by
      simp [Function.updateFinset, hiP]
    have h2 : Function.updateFinset (0 : (Fin d → ℤ) → (Fin n → ℝ)) Λ v i = v ⟨i, hiΛ⟩ := by
      simp [Function.updateFinset, hiΛ]
    rw [h1, h2]
    have h3 : (⟨latticeToTorus L i, hiP⟩ : ↥P) = e ⟨i, hiΛ⟩ := rfl
    rw [h3]
    exact Equiv.piCongrLeft_apply_apply (fun _ : ↥P ↦ (Fin n → ℝ)) e v ⟨i, hiΛ⟩
  have hmeq : (Measure.pi fun _ : ↥P ↦ ν)
        (Function.updateFinset (0 : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) P ⁻¹'
          (periodicJuxt (Fin n → ℝ) L (0 : (Fin d → ℤ) → (Fin n → ℝ)) ⁻¹' A))
      = (Measure.pi fun _ : ↥Λ ↦ ν)
        (Function.updateFinset (0 : (Fin d → ℤ) → (Fin n → ℝ)) Λ ⁻¹' A) := by
    rw [← hpreim, (measurePreserving_piCongrLeft (fun _ : ↥P ↦ ν) e).measure_preimage_equiv]
  have htorus := heisenbergPeriodicGibbsDist_inter_torusSlowGrowthSet_le (ν := ν) hν hexp heven
    hsum P (t := t) hc0 hκbd hcbd (0 : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ)) hApre
  rw [heisenbergPeriodicField, Measure.map_apply (measurable_periodicJuxt L 0) hXmeas, hpre]
  refine htorus.trans (le_of_eq ?_)
  rw [hcard, hmeq]

end Transfer

/-! ### Georgii's `Φ^n`: its Hamiltonian in a volume inside the cube -/

section PeriodicHamiltonian

variable {d n L : ℕ} {J : (Fin d → ℤ) → ℝ}

/-- A torus site lies in the block `Λ mod 2N` exactly when its representative lies in `Λ`. -/
lemma mem_image_latticeToTorus_iff {Λ : Finset (Fin d → ℤ)}
    (hΛ : Λ ⊆ Potential.latticeBox d L) (v : Fin d → ZMod (2 * (L + 1))) :
    v ∈ Λ.image (latticeToTorus L) ↔ torusToLattice L v ∈ Λ := by
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hv
    rwa [torusToLattice_latticeToTorus (hΛ hi)]
  · intro hv
    exact Finset.mem_image.2 ⟨torusToLattice L v, hv, latticeToTorus_torusToLattice v⟩

/-- **The Hamiltonian of `Φ^n` in a volume `Λ` vanishes when the spins in `Λ` do.**  Every
interaction support meeting `Λ` is a pair or a singleton of the cube, and carries a spin at a site
of `Λ` as a factor. -/
lemma hamiltonian_heisenbergPeriodicPotential_eq_zero (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (Λ : Finset (Fin d → ℤ))
    {y : (Fin d → ℤ) → (Fin n → ℝ)} (hy : ∀ i ∈ Λ, y i = 0) :
    (heisenbergPeriodicPotential n J L).hamiltonian Λ y = 0 := by
  classical
  rw [Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian]
  refine Finset.sum_eq_zero fun A hA ↦ ?_
  obtain ⟨⟨a, haA, haΛ⟩, -⟩ := Potential.mem_interactingSupport.1 hA
  have haA' : a ∈ A := haA
  have haΛ' : a ∈ Λ := haΛ
  by_cases hsub : A ⊆ Potential.latticeBox d L
  · by_cases hpair : ∃ x z : Fin d → ℤ, A = ({x, z} : Finset (Fin d → ℤ))
    · obtain ⟨x, z, rfl⟩ := hpair
      have hx : x ∈ Potential.latticeBox d L := hsub (Finset.mem_insert_self x {z})
      have hz : z ∈ Potential.latticeBox d L :=
        hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self z))
      by_cases hxz : x = z
      · subst hxz
        have hxΛ : x ∈ Λ := by
          have hax : a = x := by simpa using haA'
          exact hax ▸ haΛ'
        rw [Finset.pair_eq_singleton,
          heisenbergPeriodicPotential_singleton hsum heven hJ0 hx y, hy x hxΛ]
        simp
      · have hzero : y x ⬝ᵥ y z = 0 := by
          have : a = x ∨ a = z := by simpa using haA'
          rcases this with rfl | rfl
          · rw [hy a haΛ', zero_dotProduct]
          · rw [hy a haΛ', dotProduct_zero]
        rw [heisenbergPeriodicPotential_pair heven hx hz hxz y, hzero]
        simp
    · push Not at hpair
      exact heisenbergPeriodicPotential_of_forall_ne (fun x z ↦ hpair x z) y
  · have h0 := Potential.periodicModification_of_not_subset (Φ := heisenbergPotential n J)
      (anchor := Potential.lexAnchor) (Potential.isTorusReduction_latticeTorus d L) hsub
    exact congrFun h0 y

/-- **Georgii's `H_Λ^{Φ^n}` is the block energy of the torus.**  For a volume `Λ` inside the cube,
the Hamiltonian of the periodic modification `Φ^n` is the amount by which zeroing the spins of `Λ`
changes the exponent of (17.24):

`H_Λ^{Φ^n}(σ) = E(σ with the block zeroed) - E(σ)`,   `E = ½ ∑_{i,j ∈ Λ(N)} J_Λ(i-j) σ_i·σ_j`.

Georgii's (2.6) (`Potential.hamiltonian_sub_eq_of_mem`) reduces the sub-volume `Λ` to the cube,
where the Hamiltonian *is* minus the exponent
(`interactingHamiltonian_heisenbergPeriodicPotential`), and the Hamiltonian in `Λ` of the zeroed
configuration vanishes. -/
theorem hamiltonian_heisenbergPeriodicPotential_eq_sub (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) {Λ : Finset (Fin d → ℤ)}
    (hΛ : Λ ⊆ Potential.latticeBox d L) (x : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisenbergPeriodicPotential n J L).hamiltonian Λ x
      = heisenbergExponent (L + 1) n J (Function.updateFinset
            (fun v ↦ x (torusToLattice L v)) (Λ.image (latticeToTorus L)) 0)
        - heisenbergExponent (L + 1) n J (fun v ↦ x (torusToLattice L v)) := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  set x0 : (Fin d → ℤ) → (Fin n → ℝ) := Function.updateFinset x Λ 0 with hx0
  have hx0mem : ∀ i ∈ Λ, x0 i = 0 := fun i hi ↦ by simp [hx0, Function.updateFinset, hi]
  have hx0out : ∀ i ∉ Λ, x0 i = x i := fun i hi ↦ by simp [hx0, Function.updateFinset, hi]
  -- the Hamiltonian in the cube, at an arbitrary configuration
  have hcube : ∀ y : (Fin d → ℤ) → (Fin n → ℝ),
      (heisenbergPeriodicPotential n J L).hamiltonian (Potential.latticeBox d L) y
        = -heisenbergExponent (L + 1) n J (fun v ↦ y (torusToLattice L v)) := by
    intro y
    rw [Potential.hamiltonian_eq_interactingHamiltonian]
    exact interactingHamiltonian_heisenbergPeriodicPotential hsum heven hJ0 _ y
      fun i hi ↦ by rw [torusToLattice_latticeToTorus hi]
  -- Georgii (2.6)
  have hsub := Potential.hamiltonian_sub_eq_of_mem
    (Φ := heisenbergPeriodicPotential n J L) (Ω₀ := Set.univ)
    (Potential.IsSummable.isSummableOn) hΛ (Set.mem_univ x) (Set.mem_univ x0)
    fun i hi ↦ (hx0out i hi).symm
  have hzero := hamiltonian_heisenbergPeriodicPotential_eq_zero (L := L) hsum heven hJ0 Λ hx0mem
  -- the zeroed configuration, read on the torus
  have htorus : (fun v ↦ x0 (torusToLattice L v))
      = Function.updateFinset (fun v ↦ x (torusToLattice L v)) (Λ.image (latticeToTorus L)) 0 := by
    funext v
    by_cases hv : v ∈ Λ.image (latticeToTorus L)
    · have hrep : torusToLattice L v ∈ Λ := (mem_image_latticeToTorus_iff hΛ v).1 hv
      simp [Function.updateFinset, hv, hx0mem _ hrep]
    · have hrep : torusToLattice L v ∉ Λ := fun hc ↦
        hv ((mem_image_latticeToTorus_iff hΛ v).2 hc)
      simp [Function.updateFinset, hv, hx0out _ hrep]
  rw [hcube x, hcube x0, hzero] at hsub
  rw [← htorus]
  linarith [hsub]

/-- **Georgii's estimate `|H_Λ^{Φ}(ω)| ≤ c(ω_{S∖Λ}) ∑_{i∈Λ}[1 + |ω_i|²]`, for the periodic
modification `Φ^n` and an *arbitrary* volume.**  The constant depends on the boundary condition
only through the exterior, as Georgii's notation records; over the cube the Hamiltonian is the
block energy of the torus (`hamiltonian_heisenbergPeriodicPotential_eq_sub`), and outside it the
potential vanishes. -/
theorem exists_abs_hamiltonian_heisenbergPeriodicPotential_le (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (Λ : Finset (Fin d → ℤ))
    (ω : (Fin d → ℤ) → (Fin n → ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : (Fin d → ℤ) → (Fin n → ℝ), (∀ i ∉ Λ, x i = ω i) →
      |(heisenbergPeriodicPotential n J L).hamiltonian Λ x| ≤ K * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  set Λ' : Finset (Fin d → ℤ) := Λ ∩ Potential.latticeBox d L with hΛ'
  have hΛ'sub : Λ' ⊆ Potential.latticeBox d L := Finset.inter_subset_right
  have hΛ'sub' : Λ' ⊆ Λ := Finset.inter_subset_left
  set P : Finset (Fin d → ZMod (2 * (L + 1))) := Λ'.image (latticeToTorus L) with hP
  -- the interaction supports meeting `Λ` are the ones meeting `Λ'`
  have hsupp : Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ
      = Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ' := by
    refine Finset.ext fun A ↦ ?_
    simp only [Potential.mem_interactingSupport]
    constructor
    · rintro ⟨⟨a, haA, haΛ⟩, hne⟩
      have hAsub : A ⊆ Potential.latticeBox d L := by
        by_contra hc
        exact hne (Potential.periodicModification_of_not_subset
          (Potential.isTorusReduction_latticeTorus d L) hc)
      exact ⟨⟨a, haA, Finset.mem_inter.2 ⟨haΛ, hAsub haA⟩⟩, hne⟩
    · rintro ⟨⟨a, haA, haΛ'⟩, hne⟩
      exact ⟨⟨a, haA, hΛ'sub' haΛ'⟩, hne⟩
  have hHeq : ∀ y : (Fin d → ℤ) → (Fin n → ℝ),
      (heisenbergPeriodicPotential n J L).hamiltonian Λ y
        = (heisenbergPeriodicPotential n J L).hamiltonian Λ' y := by
    intro y
    rw [Potential.hamiltonian_eq_interactingHamiltonian,
      Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian,
      Potential.interactingHamiltonian, hsupp]
  -- the exterior bound supplied by the boundary condition
  set β : (Fin d → ZMod (2 * (L + 1))) → ℝ :=
    fun v ↦ Real.sqrt (ω (torusToLattice L v) ⬝ᵥ ω (torusToLattice L v)) with hβdef
  have hβ0 : ∀ v, 0 ≤ β v := fun v ↦ Real.sqrt_nonneg _
  refine ⟨(∑' m, |J m|)
      + ∑ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v, ?_, fun x hx ↦ ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
    have h2 : (0 : ℝ) ≤ ∑ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v :=
      Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦
        mul_nonneg (abs_nonneg _) (hβ0 v)
    linarith
  set ζ : (Fin d → ZMod (2 * (L + 1))) → (Fin n → ℝ) := fun v ↦ x (torusToLattice L v) with hζdef
  -- outside the block the configuration is the boundary condition
  have hβ : ∀ v ∉ P, Real.sqrt (ζ v ⬝ᵥ ζ v) ≤ β v := by
    intro v hv
    have hrep : torusToLattice L v ∉ Λ' :=
      fun hc ↦ hv ((mem_image_latticeToTorus_iff hΛ'sub v).2 hc)
    have hrepΛ : torusToLattice L v ∉ Λ := fun hc ↦
      hrep (Finset.mem_inter.2 ⟨hc, torusToLattice_mem v⟩)
    rw [hζdef, hβdef]
    simp only [hx _ hrepΛ]
    exact le_rfl
  -- the block sum, read on the lattice
  have hsumeq : ∑ u ∈ P, (1 + ζ u ⬝ᵥ ζ u) = ∑ i ∈ Λ', (1 + x i ⬝ᵥ x i) := by
    rw [hP, Finset.sum_image fun i hi j hj h ↦
      latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 (hΛ'sub hi))
        (Finset.mem_coe.2 (hΛ'sub hj)) h]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [hζdef]; simp only [torusToLattice_latticeToTorus (hΛ'sub hi)]
  have hmono : ∑ i ∈ Λ', (1 + x i ⬝ᵥ x i) ≤ ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hΛ'sub' fun i _ _ ↦ by
      have := dotProduct_self_nonneg (x i); linarith
  have hbound := blockEnergyBound_le_of_exterior_le (n := n) hsum P hβ0 hβ
  rw [hsumeq] at hbound
  have habs : |(heisenbergPeriodicPotential n J L).hamiltonian Λ x|
      ≤ blockEnergyBound (L + 1) n J P ζ := by
    rw [hHeq x, hamiltonian_heisenbergPeriodicPotential_eq_sub hsum heven hJ0 hΛ'sub x, ← hP,
      ← hζdef, ← abs_neg]
    simpa using abs_heisenbergExponent_sub_updateFinset_zero_le heven P ζ
  refine habs.trans (hbound.trans ?_)
  refine mul_le_mul_of_nonneg_left hmono ?_
  have h1 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ u ∈ P, ∑ v ∈ Pᶜ, |periodizedCoupling (L + 1) J (u - v)| * β v :=
    Finset.sum_nonneg fun u _ ↦ Finset.sum_nonneg fun v _ ↦ mul_nonneg (abs_nonneg _) (hβ0 v)
  linarith

/-- **Georgii's standing `λ`-admissibility for the periodic modification `Φ^n`.**  The partition
functions `Z_Λ^{Φ^n}(ω)` are finite and non-zero in *every* volume and at *every* boundary
condition: the Hamiltonian is bounded by `K(ω) ∑_{i∈Λ}[1 + |σ_i|²]`
(`exists_abs_hamiltonian_heisenbergPeriodicPotential_le`) and (20.3) makes both Gaussian bounds
integrable.  This is what turns Georgii's `Φ^n` into a genuine Gibbsian specification `γ^n`. -/
theorem isSigmaFiniteLambdaAdmissible_heisenbergPeriodicPotential {ν : Measure (Fin n → ℝ)}
    [IsFiniteMeasure ν] (hν : ν ≠ 0) (hexp : HasExpSqMoments ν) (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := Fin d → ℤ) (E := Fin n → ℝ) ν
      ((heisenbergPeriodicPotential n J L).boltzmannFactor 1) := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  intro Λ ω
  obtain ⟨K, hK0, hK⟩ :=
    exists_abs_hamiltonian_heisenbergPeriodicPotential_le (L := L) hsum heven hJ0 Λ ω
  have hρmeas : Measurable ((heisenbergPeriodicPotential n J L).boltzmannFactor 1 Λ) :=
    Potential.measurable_boltzmannFactor 1 Λ
  have hmeasg : ∀ σ : ℝ, Measurable fun y : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (σ * (1 + y ⬝ᵥ y))) := fun σ ↦
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_const.add (Finset.measurable_sum _ fun c _ ↦
        (measurable_pi_apply c).mul (measurable_pi_apply c))).const_mul _))
  -- the two-sided bound on the Boltzmann factor
  have hbd : ∀ ζ : ↥Λ → (Fin n → ℝ),
      (∏ i : ↥Λ, ENNReal.ofReal (Real.exp (-(K * (1 + ζ i ⬝ᵥ ζ i)))))
          ≤ (heisenbergPeriodicPotential n J L).boltzmannFactor 1 Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
        ∧ (heisenbergPeriodicPotential n J L).boltzmannFactor 1 Λ
              (juxt (Λ : Set (Fin d → ℤ)) ω ζ)
          ≤ ∏ i : ↥Λ, ENNReal.ofReal (Real.exp (K * (1 + ζ i ⬝ᵥ ζ i))) := by
    intro ζ
    set y : (Fin d → ℤ) → (Fin n → ℝ) := juxt (Λ : Set (Fin d → ℤ)) ω ζ with hy
    have hagree : ∀ i ∉ Λ, y i = ω i := fun i hi ↦
      juxt_apply_of_not_mem (Finset.mem_coe.not.mpr hi) ζ
    have hsumeq : ∑ i ∈ Λ, (1 + y i ⬝ᵥ y i) = ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i) := by
      rw [← Finset.sum_coe_sort Λ fun i ↦ 1 + y i ⬝ᵥ y i]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hyi : y (i : Fin d → ℤ) = ζ i := by
        rw [hy, juxt_apply_of_mem (Finset.mem_coe.mpr i.2) ζ, Subtype.coe_eta]
      rw [hyi]
    have hHam := hK y hagree
    rw [hsumeq] at hHam
    have habs := abs_le.1 hHam
    have hprodpos : ∀ σ : ℝ, (∏ i : ↥Λ, ENNReal.ofReal (Real.exp (σ * (1 + ζ i ⬝ᵥ ζ i))))
        = ENNReal.ofReal (Real.exp (σ * ∑ i : ↥Λ, (1 + ζ i ⬝ᵥ ζ i))) := by
      intro σ
      rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg fun i _ ↦ Real.exp_nonneg _]
    constructor
    · rw [Potential.boltzmannFactor,
        show (∏ i : ↥Λ, ENNReal.ofReal (Real.exp (-(K * (1 + ζ i ⬝ᵥ ζ i)))))
          = ∏ i : ↥Λ, ENNReal.ofReal (Real.exp ((-K) * (1 + ζ i ⬝ᵥ ζ i))) from
        Finset.prod_congr rfl fun i _ ↦ by ring_nf, hprodpos (-K)]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [habs.1, habs.2]))
    · rw [Potential.boltzmannFactor, hprodpos K]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith [habs.1, habs.2]))
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hρmeas Measurable.juxt]
  constructor
  · -- `Z_Λ ≠ 0`
    have hlow : (∫⁻ y : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(K * (1 + y ⬝ᵥ y)))) ∂ν) ^
        Fintype.card ↥Λ
        ≤ ∫⁻ ζ, (heisenbergPeriodicPotential n J L).boltzmannFactor 1 Λ
            (juxt (Λ : Set (Fin d → ℤ)) ω ζ) ∂(Measure.pi fun _ : ↥Λ ↦ ν) := by
      refine le_trans (le_of_eq ?_) (lintegral_mono fun ζ ↦ (hbd ζ).1)
      have hm : Measurable fun y : Fin n → ℝ ↦
          ENNReal.ofReal (Real.exp (-(K * (1 + y ⬝ᵥ y)))) := by
        have := hmeasg (-K)
        simpa only [neg_mul] using this
      rw [lintegral_pi_prod (μ := fun _ : ↥Λ ↦ ν)
        (g := fun _ (y : Fin n → ℝ) ↦ ENNReal.ofReal (Real.exp (-(K * (1 + y ⬝ᵥ y)))))
        fun _ ↦ hm]
      rw [Finset.prod_const, Finset.card_univ]
    exact fun hc ↦ (pow_ne_zero _ (lintegral_exp_neg_pos hν K).ne')
      (le_antisymm (hc ▸ hlow) zero_le)
  · -- `Z_Λ ≠ ⊤`
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ζ ↦ (hbd ζ).2)
    refine ne_top_of_le_ne_top ?_ (le_of_eq (lintegral_pi_prod (μ := fun _ : ↥Λ ↦ ν)
      (g := fun _ (y : Fin n → ℝ) ↦ ENNReal.ofReal (Real.exp (K * (1 + y ⬝ᵥ y))))
      fun _ ↦ hmeasg K))
    refine ENNReal.prod_ne_top fun i _ ↦ ?_
    have hint : Integrable (fun y : Fin n → ℝ ↦ Real.exp (K * (1 + y ⬝ᵥ y))) ν := by
      have hcongr : (fun y : Fin n → ℝ ↦ Real.exp (K * (1 + y ⬝ᵥ y)))
          = fun y ↦ Real.exp K * Real.exp (K * (y ⬝ᵥ y)) := by
        funext y; rw [← Real.exp_add]; ring_nf
      rw [hcongr]
      exact (hexp K).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y ↦ Real.exp_nonneg _)]
    exact ENNReal.ofReal_ne_top

end PeriodicHamiltonian



/-! ### Georgii's null sequence `(δ_n)`: the periodisation error -/

section PeriodisationError

variable {d : ℕ} {J : (Fin d → ℤ) → ℝ}

variable (J) in
/-- **Georgii's `δ_n`**: the `α`-weighted tail `∑_{m ∉ Λ(N)} |J(i-m)| α(m)` of the coupling
outside the cube, seen from the site `i`.  Hypothesis (20.4) makes it finite, and it tends to `0`
as the cube grows (`tendsto_couplingTail`). -/
def couplingTail (J : (Fin d → ℤ) → ℝ) (L : ℕ) (i : Fin d → ℤ) : ℝ :=
  ∑' k : Fin d → ℤ,
    ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator
      (fun m ↦ |J (i - m)| * slowGrowth m) k

lemma couplingTail_nonneg (J : (Fin d → ℤ) → ℝ) (L : ℕ) (i : Fin d → ℤ) :
    0 ≤ couplingTail J L i := by
  refine tsum_nonneg fun k ↦ ?_
  by_cases hk : k ∈ ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ)
  · rw [Set.indicator_of_mem hk]
    exact mul_nonneg (abs_nonneg _) (slowGrowth_pos k).le
  · rw [Set.indicator_of_notMem hk]

/-- **The periodised coupling as a fibre sum, in the translated variable.**
`J_Λ(i-j) = ∑_{k ≡ j} J(i-k)`. -/
lemma periodizedCoupling_sub_eq_tsum_ite (L : ℕ) (i j : Fin d → ℤ) :
    periodizedCoupling (L + 1) J (latticeToTorus L (i - j))
      = ∑' k : Fin d → ℤ, (if latticeToTorus L k = latticeToTorus L j then J (i - k) else 0) := by
  rw [periodizedCoupling_eq_tsum_ite,
    ← (Equiv.subLeft i).tsum_eq (fun m : Fin d → ℤ ↦
      if (fun c ↦ ((m c : ℤ) : ZMod (2 * (L + 1)))) = latticeToTorus L (i - j) then J m else 0)]
  refine tsum_congr fun k ↦ ?_
  have hb : (fun c ↦ (((i - k) c : ℤ) : ZMod (2 * (L + 1)))) = latticeToTorus L (i - k) := rfl
  rw [Equiv.subLeft_apply, hb, latticeToTorus_sub, latticeToTorus_sub]
  exact if_congr sub_right_inj rfl rfl

/-- **The periodisation error at one bond.**  `|J_Λ(i-j) - J(i-j)|` is at most the sum of `|J|`
over the *other* points of the fibre of `j`. -/
lemma abs_periodizedCoupling_sub_le (hsum : Summable J) (L : ℕ) (i j : Fin d → ℤ) :
    |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)|
      ≤ ∑' k : Fin d → ℤ,
          (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then |J (i - k)| else 0) := by
  have hJsub : Summable fun k : Fin d → ℤ ↦ |J (i - k)| :=
    hsum.abs.comp_injective (Equiv.subLeft i).injective
  set f : (Fin d → ℤ) → ℝ :=
    fun k ↦ if latticeToTorus L k = latticeToTorus L j then J (i - k) else 0 with hf
  have hfabs : ∀ k, |f k| ≤ |J (i - k)| := by
    intro k
    by_cases h : latticeToTorus L k = latticeToTorus L j
    · simp [hf, h]
    · simp [hf, h, abs_nonneg]
  have hfsum : Summable f :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun k ↦ abs_nonneg _) hfabs hJsub)
  have hfj : f j = J (i - j) := by simp [hf]
  have hsplit : (∑' k, f k) - J (i - j) = ∑' k, (if k = j then 0 else f k) := by
    rw [hfsum.tsum_eq_add_tsum_ite j, hfj]; ring
  have hnorm : Summable fun k : Fin d → ℤ ↦ ‖(if k = j then 0 else f k)‖ := by
    refine Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) (fun k ↦ ?_) hJsub
    by_cases h : k = j
    · simp [h]
    · simpa [h, Real.norm_eq_abs] using hfabs k
  rw [periodizedCoupling_sub_eq_tsum_ite, ← hf, hsplit, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans (le_of_eq (tsum_congr fun k ↦ ?_))
  by_cases h : k = j
  · simp [h]
  · by_cases h2 : latticeToTorus L k = latticeToTorus L j <;>
      simp [hf, h, h2, Real.norm_eq_abs]

/-- **Georgii's "By (20.4) and a short calculation" in the proof of (20.7).**  The `α`-weighted
periodisation error of the coupling over the cube is at most the `α`-weighted tail of `J` outside
the cube:

`∑_{j ∈ Λ(N)} |J_{Λ(N)}(i-j) - J(i-j)| α(j) ≤ ∑_{m ∉ Λ(N)} |J(i-m)| α(m)`.

The proof is the fibre decomposition: the sites of the fibre of a `j ∈ Λ(N)` other than `j` itself
are exactly the sites `m ∉ Λ(N)` with `m ≡ j`, and `α(j) ≤ α(m)` there because the representative
in the cube is the shortest point of its fibre (`norm_le_norm_of_latticeToTorus_eq`). -/
theorem sum_abs_periodizedCoupling_sub_mul_slowGrowth_le (hJ : IsSlowlySummable J) (L : ℕ)
    (i : Fin d → ℤ) :
    ∑ j ∈ Potential.latticeBox d L,
        |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| * slowGrowth j
      ≤ couplingTail J L i := by
  set g : (Fin d → ℤ) → ℝ := fun m ↦ |J (i - m)| * slowGrowth m with hg
  have hgsum : Summable g := hJ.summable_sub' i
  have hg0 : ∀ m, 0 ≤ g m := fun m ↦ mul_nonneg (abs_nonneg _) (slowGrowth_pos m).le
  have hfibsum : ∀ j : Fin d → ℤ, Summable fun k : Fin d → ℤ ↦
      (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0) := by
    intro j
    refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_) hgsum <;>
      by_cases h : latticeToTorus L k = latticeToTorus L j ∧ k ≠ j <;> simp [h, hg0 k]
  -- the termwise bound, with `α` transported to the fibre
  have hterm : ∀ j ∈ Potential.latticeBox d L,
      |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| * slowGrowth j
        ≤ ∑' k : Fin d → ℤ,
            (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0) := by
    intro j hj
    have hsummand : Summable fun k : Fin d → ℤ ↦
        (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then |J (i - k)| else 0) := by
      refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ ?_)
        (hJ.summable.abs.comp_injective (Equiv.subLeft i).injective) <;>
        by_cases h : latticeToTorus L k = latticeToTorus L j ∧ k ≠ j <;> simp [h]
    calc |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| * slowGrowth j
        ≤ (∑' k : Fin d → ℤ,
            (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then |J (i - k)| else 0))
              * slowGrowth j :=
          mul_le_mul_of_nonneg_right (abs_periodizedCoupling_sub_le hJ.summable L i j)
            (slowGrowth_pos j).le
      _ = ∑' k : Fin d → ℤ,
            (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then |J (i - k)| else 0)
              * slowGrowth j := tsum_mul_right.symm
      _ ≤ ∑' k : Fin d → ℤ,
            (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0) := by
          refine Summable.tsum_le_tsum (fun k ↦ ?_) (hsummand.mul_right _) (hfibsum j)
          by_cases h : latticeToTorus L k = latticeToTorus L j ∧ k ≠ j
          · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true h), hg]
            exact mul_le_mul_of_nonneg_left
              (slowGrowth_le_slowGrowth (norm_le_norm_of_latticeToTorus_eq hj h.1)) (abs_nonneg _)
          · rw [ite_eq_right_of_eq_false _ _ (eq_false h),
              ite_eq_right_of_eq_false _ _ (eq_false h), zero_mul]
  -- at a fixed `k` exactly one site of the cube contributes, and only when `k ∉ Λ(N)`
  have hinner : ∀ k : Fin d → ℤ, ∑ j ∈ Potential.latticeBox d L,
        (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0)
      = ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator g k := by
    intro k
    set r : Fin d → ℤ := torusToLattice L (latticeToTorus L k) with hr
    have hrep : r ∈ Potential.latticeBox d L := torusToLattice_mem _
    have hrtorus : latticeToTorus L r = latticeToTorus L k := latticeToTorus_torusToLattice _
    have hsingle : ∑ j ∈ Potential.latticeBox d L,
        (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0)
        = if latticeToTorus L k = latticeToTorus L r ∧ k ≠ r then g k else 0 := by
      refine Finset.sum_eq_single r (fun j hj hjne ↦ ?_) (fun hcon ↦ absurd hrep hcon)
      refine ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hjne ?_)
      exact latticeToTorus_injOn_latticeBox (Finset.mem_coe.2 hj) (Finset.mem_coe.2 hrep)
        (by rw [← h.1, hrtorus])
    rw [hsingle]
    by_cases hk : k ∈ Potential.latticeBox d L
    · have hrk : r = k := torusToLattice_latticeToTorus hk
      rw [Set.indicator_of_notMem (by simp [hk]),
        ite_eq_right_of_eq_false _ _ (eq_false (by rintro ⟨-, hne⟩; exact hne hrk.symm))]
    · rw [Set.indicator_of_mem (by simp [hk]),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨hrtorus.symm, fun hc ↦ hk (hc ▸ hrep)⟩)]
  calc ∑ j ∈ Potential.latticeBox d L,
        |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| * slowGrowth j
      ≤ ∑ j ∈ Potential.latticeBox d L, ∑' k : Fin d → ℤ,
          (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑' k : Fin d → ℤ, ∑ j ∈ Potential.latticeBox d L,
          (if latticeToTorus L k = latticeToTorus L j ∧ k ≠ j then g k else 0) :=
        (Summable.tsum_finsetSum fun j _ ↦ hfibsum j).symm
    _ = couplingTail J L i := tsum_congr hinner

/-- **Georgii's null sequence `(δ_n)`.**  The `α`-weighted tail of the coupling outside the cube
tends to `0`; by `sum_abs_periodizedCoupling_sub_mul_slowGrowth_le` it dominates the periodisation
error of the coupling as well.  This is the only place where (20.4) — rather than (20.2) — is
needed to compare Georgii's `Φ^n` with `Φ`. -/
theorem tendsto_couplingTail (hJ : IsSlowlySummable J) (i : Fin d → ℤ) :
    Filter.Tendsto (fun L : ℕ ↦ couplingTail J L i) atTop (𝓝 0) := by
  set g : (Fin d → ℤ) → ℝ := fun m ↦ |J (i - m)| * slowGrowth m with hg
  have hgsum : Summable g := hJ.summable_sub' i
  -- the tail is the total sum minus the sum over the cube
  have hsplit : ∀ L : ℕ,
      couplingTail J L i = (∑' k, g k) - ∑ m ∈ Potential.latticeBox d L, g m := by
    intro L
    have hin : Summable fun k ↦ ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator g k :=
      hgsum.indicator _
    have hout : Summable fun k ↦ ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator g k :=
      hgsum.indicator _
    have hfin : ∑' k, ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator g k
        = ∑ m ∈ Potential.latticeBox d L, g m := by
      rw [tsum_eq_sum (s := Potential.latticeBox d L)
        fun k hk ↦ Set.indicator_of_notMem (by simpa using hk) _]
      exact Finset.sum_congr rfl fun k hk ↦ Set.indicator_of_mem (by simpa using hk) _
    have htotal : ∑' k, g k
        = (∑' k, ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator g k)
          + ∑' k, ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator g k := by
      rw [← hin.tsum_add hout]
      exact tsum_congr fun k ↦ (congrFun (Set.indicator_self_add_compl _ g) k).symm
    rw [couplingTail, htotal, hfin]
    ring
  simp only [hsplit]
  have hsum : Filter.Tendsto (fun L : ℕ ↦ ∑ m ∈ Potential.latticeBox d L, g m) atTop
      (𝓝 (∑' k, g k)) := hgsum.hasSum.comp Potential.tendsto_latticeBox_atTop
  have := (tendsto_const_nhds (x := ∑' k, g k) (α := ℕ) (f := atTop)).sub hsum
  simpa using this

end PeriodisationError

/-! ### Georgii's `H_Λ^{Φ^n - Φ}` -/

section HamiltonianComparison

variable {d n L : ℕ} {J : (Fin d → ℤ) → ℝ}

/-- **The pair coefficient of Georgii's `Φ^n - Φ`**: `J_{Λ(n)}(i-j) - J(i-j)` on the bonds of the
cube, and `J(i-j)` on the bonds that leave it — where `Φ^n` vanishes and only `Φ` contributes. -/
def couplingDiff (J : (Fin d → ℤ) → ℝ) (L : ℕ) (i j : Fin d → ℤ) : ℝ :=
  if i ∈ Potential.latticeBox d L ∧ j ∈ Potential.latticeBox d L then
    |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)|
  else |J (i - j)|

lemma couplingDiff_nonneg (i j : Fin d → ℤ) : 0 ≤ couplingDiff J L i j := by
  rw [couplingDiff]; split_ifs <;> exact abs_nonneg _

lemma couplingDiff_symm (heven : ∀ m, J (-m) = J m) (i j : Fin d → ℤ) :
    couplingDiff J L i j = couplingDiff J L j i := by
  have hJ : J (j - i) = J (i - j) := by rw [show j - i = -(i - j) by abel, heven]
  have hJL : periodizedCoupling (L + 1) J (latticeToTorus L (j - i))
      = periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) := by
    rw [show latticeToTorus L (j - i) = -latticeToTorus L (i - j) by
      rw [latticeToTorus_sub, latticeToTorus_sub]; abel, periodizedCoupling_neg heven]
  rw [couplingDiff, couplingDiff, hJ, hJL]
  exact if_congr and_comm rfl rfl

/-- The `α`-weighted rows of the coefficient of `Φ^n - Φ` are summable: over the cube the sum is
finite, and off it the coefficient is `J` itself. -/
lemma summable_couplingDiff_mul_slowGrowth (hJ : IsSlowlySummable J) (i : Fin d → ℤ) :
    Summable fun j ↦ couplingDiff J L i j * slowGrowth j := by
  classical
  have hfin : Summable fun j ↦ ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator
      (fun j ↦ couplingDiff J L i j * slowGrowth j) j :=
    summable_of_ne_finset_zero (s := Potential.latticeBox d L) fun j hj ↦
      Set.indicator_of_notMem (by simpa using hj) _
  refine Summable.of_nonneg_of_le (fun j ↦ ?_) (fun j ↦ ?_) (hfin.add (hJ.summable_sub' i))
  · exact mul_nonneg (couplingDiff_nonneg i j) (slowGrowth_pos j).le
  · by_cases hj : j ∈ Potential.latticeBox d L
    · rw [Set.indicator_of_mem (by simpa using hj)]
      have : (0 : ℝ) ≤ |J (i - j)| * slowGrowth j :=
        mul_nonneg (abs_nonneg _) (slowGrowth_pos j).le
      linarith
    · rw [Set.indicator_of_notMem (by simpa using hj), zero_add, couplingDiff,
        ite_eq_right_of_eq_false _ _ (eq_false (by tauto))]

/-- **Georgii's `δ_n`, at a site of the cube.**  The `α`-weighted row of the coefficient of
`Φ^n - Φ` is at most twice the `α`-weighted tail of `J` outside the cube: the bonds inside the cube
contribute the periodisation error (`sum_abs_periodizedCoupling_sub_mul_slowGrowth_le`), the bonds
leaving it contribute the tail itself. -/
theorem tsum_couplingDiff_mul_slowGrowth_le (hJ : IsSlowlySummable J)
    {i : Fin d → ℤ} (hi : i ∈ Potential.latticeBox d L) :
    ∑' j, couplingDiff J L i j * slowGrowth j ≤ 2 * couplingTail J L i := by
  classical
  set f : (Fin d → ℤ) → ℝ := fun j ↦ couplingDiff J L i j * slowGrowth j with hf
  have hfsum : Summable f := summable_couplingDiff_mul_slowGrowth hJ i
  have hin : Summable fun j ↦ ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator f j :=
    hfsum.indicator _
  have hout : Summable fun j ↦ ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator f j :=
    hfsum.indicator _
  have hsplit : ∑' j, f j
      = (∑' j, ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator f j)
        + ∑' j, ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator f j := by
    rw [← hin.tsum_add hout]
    exact tsum_congr fun j ↦ (congrFun (Set.indicator_self_add_compl _ f) j).symm
  have hinner : ∑' j, ((Potential.latticeBox d L : Set (Fin d → ℤ))).indicator f j
      = ∑ j ∈ Potential.latticeBox d L,
        |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| * slowGrowth j := by
    rw [tsum_eq_sum (s := Potential.latticeBox d L)
      fun j hj ↦ Set.indicator_of_notMem (by simpa using hj) _]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [Set.indicator_of_mem (by simpa using hj), hf]
    simp only [couplingDiff, ite_eq_left_of_eq_true _ _
      (eq_true (⟨hi, hj⟩ : i ∈ Potential.latticeBox d L ∧ j ∈ Potential.latticeBox d L))]
  have houter : ∑' j, ((Potential.latticeBox d L : Set (Fin d → ℤ))ᶜ).indicator f j
      = couplingTail J L i := by
    rw [couplingTail]
    refine tsum_congr fun j ↦ ?_
    by_cases hj : j ∈ Potential.latticeBox d L
    · rw [Set.indicator_of_notMem (by simp [hj]), Set.indicator_of_notMem (by simp [hj])]
    · rw [Set.indicator_of_mem (by simp [hj]), Set.indicator_of_mem (by simp [hj]), hf]
      simp only [couplingDiff, ite_eq_right_of_eq_false _ _ (eq_false
        (by tauto : ¬ (i ∈ Potential.latticeBox d L ∧ j ∈ Potential.latticeBox d L)))]
  have hbd := sum_abs_periodizedCoupling_sub_mul_slowGrowth_le hJ L i
  rw [hf] at hsplit
  rw [hsplit, hinner, houter]
  linarith

/-- The interaction terms of `Φ^n` in a volume are supported on the (finite) interacting
support. -/
lemma hamiltonianTerms_heisenbergPeriodicPotential_eq_zero (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) {Λ A : Finset (Fin d → ℤ)}
    (hA : A ∉ Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ)
    (x : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x A = 0 := by
  classical
  have := isPotential_heisenbergPeriodicPotential (n := n) hsum heven hJ0 L
  by_cases hdisj : Disjoint A Λ
  · exact Potential.hamiltonianTerms_of_disjoint hdisj x
  · rw [Potential.hamiltonianTerms_of_not_disjoint hdisj x]
    obtain ⟨a, ha⟩ := Finset.not_disjoint_iff_nonempty_inter.1 hdisj
    have hnonempty : ((A : Set (Fin d → ℤ)) ∩ (Λ : Set (Fin d → ℤ))).Nonempty := by
      obtain ⟨haA, haΛ⟩ := Finset.mem_inter.1 ha
      exact ⟨a, by simpa using haA, by simpa using haΛ⟩
    have hne : ¬ (heisenbergPeriodicPotential n J L) A ≠ 0 := fun hc ↦
      hA (Potential.mem_interactingSupport.2 ⟨hnonempty, hc⟩)
    rw [not_not] at hne
    exact congrFun hne x

lemma summable_abs_hamiltonianTerms_heisenbergPeriodicPotential (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (Λ : Finset (Fin d → ℤ))
    (x : (Fin d → ℤ) → (Fin n → ℝ)) :
    Summable fun A ↦ |(heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x A| := by
  classical
  refine summable_of_ne_finset_zero
    (s := Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ) fun A hA ↦ ?_
  rw [hamiltonianTerms_heisenbergPeriodicPotential_eq_zero hsum heven hJ0 hA x, abs_zero]

/-- The Hamiltonian of `Φ^n` is the unconditional sum of its interaction terms. -/
lemma hamiltonian_heisenbergPeriodicPotential_eq_tsum (hsum : Summable J)
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (Λ : Finset (Fin d → ℤ))
    (x : (Fin d → ℤ) → (Fin n → ℝ)) :
    (heisenbergPeriodicPotential n J L).hamiltonian Λ x
      = ∑' A, (heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x A := by
  classical
  rw [Potential.hamiltonian_eq_interactingHamiltonian, Potential.interactingHamiltonian,
    tsum_eq_sum (s := Potential.interactingSupport (Φ := heisenbergPeriodicPotential n J L) Λ)
      fun A hA ↦ hamiltonianTerms_heisenbergPeriodicPotential_eq_zero hsum heven hJ0 hA x]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  obtain ⟨a, haA, haΛ⟩ := (Potential.mem_interactingSupport.1 hA).1
  have hdisj : ¬ Disjoint A Λ :=
    Finset.not_disjoint_iff_nonempty_inter.2
      ⟨a, Finset.mem_inter.2 ⟨by simpa using haA, by simpa using haΛ⟩⟩
  rw [Potential.hamiltonianTerms_of_not_disjoint hdisj x]

/-- **Georgii's `H_Λ^{Φ^n - Φ}`.**  The Hamiltonians of the periodic modification and of the
Heisenberg potential itself differ, in every volume and at every slowly increasing configuration,
by at most the pair majorant of the coefficient `couplingDiff`. -/
theorem abs_hamiltonian_heisenbergPeriodicPotential_sub_le (heven : ∀ m, J (-m) = J m)
    (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ))
    {x : (Fin d → ℤ) → (Fin n → ℝ)} (hx : x ∈ slowGrowthTailSet d n) :
    |(heisenbergPeriodicPotential n J L).hamiltonian Λ x
        - (heisenbergPotential n J).hamiltonian Λ x|
      ≤ 2 * ∑ i ∈ Λ, Real.sqrt (x i ⬝ᵥ x i)
          * ∑' j, couplingDiff J L i j * Real.sqrt (x j ⬝ᵥ x j) := by
  classical
  have hsum : Summable J := hJ.summable
  obtain ⟨t, ht0, ht⟩ := exists_nonneg_sqrt_dotProduct_le_of_mem_slowGrowthTailSet hx
  set s : (Fin d → ℤ) → ℝ := fun i ↦ Real.sqrt (x i ⬝ᵥ x i) with hs
  have hs0 : ∀ i, 0 ≤ s i := fun i ↦ Real.sqrt_nonneg _
  set T : Finset (Fin d → ℤ) → ℝ := fun A ↦
    (heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x A
      - (heisenbergPotential n J).hamiltonianTerms Λ x A with hT
  have habs₁ := summable_abs_hamiltonianTerms_heisenbergPeriodicPotential
    (L := L) hsum heven hJ0 Λ x
  have habs₂ := summable_abs_hamiltonianTerms_heisenbergPotential heven hJ0 hJ Λ hx
  have hTabs : Summable fun A ↦ |T A| := by
    refine Summable.of_nonneg_of_le (fun A ↦ abs_nonneg _) (fun A ↦ ?_) (habs₁.add habs₂)
    exact abs_sub _ _
  -- the difference of the two Hamiltonians is the sum of the difference of the terms
  have hdiff : (heisenbergPeriodicPotential n J L).hamiltonian Λ x
      - (heisenbergPotential n J).hamiltonian Λ x = ∑' A, T A := by
    rw [hamiltonian_heisenbergPeriodicPotential_eq_tsum hsum heven hJ0 Λ x,
      hamiltonian_heisenbergPotential_eq_tsum heven hJ0 hJ Λ hx, hT]
    exact ((Summable.of_abs habs₁).tsum_sub (Summable.of_abs habs₂)).symm
  -- the summability of the rows of `couplingDiff`
  have hsummable : ∀ i, Summable fun j ↦ couplingDiff J L i j * s j := by
    intro i
    refine Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (couplingDiff_nonneg i j) (hs0 j))
      (fun j ↦ ?_) ((summable_couplingDiff_mul_slowGrowth (L := L) hJ i).mul_left t)
    have := ht j
    calc couplingDiff J L i j * s j ≤ couplingDiff J L i j * (t * slowGrowth j) :=
          mul_le_mul_of_nonneg_left this (couplingDiff_nonneg i j)
      _ = t * (couplingDiff J L i j * slowGrowth j) := by ring
  -- the pointwise pair bound
  have hbound : ∀ i j : Fin d → ℤ, |T ({i, j} : Finset (Fin d → ℤ))|
      ≤ couplingDiff J L i j * (s i * s j) := by
    intro i j
    have hnn : (0 : ℝ) ≤ couplingDiff J L i j * (s i * s j) :=
      mul_nonneg (couplingDiff_nonneg i j) (mul_nonneg (hs0 i) (hs0 j))
    by_cases hdisj : Disjoint ({i, j} : Finset (Fin d → ℤ)) Λ
    · rw [hT]
      simp only [Potential.hamiltonianTerms_of_disjoint hdisj, sub_self, abs_zero]
      exact hnn
    rw [hT]
    simp only [Potential.hamiltonianTerms_of_not_disjoint hdisj]
    by_cases hcube : i ∈ Potential.latticeBox d L ∧ j ∈ Potential.latticeBox d L
    · by_cases hij : i = j
      · subst hij
        rw [Finset.pair_eq_singleton,
          heisenbergPeriodicPotential_singleton hsum heven hJ0 hcube.1 x,
          heisenbergPotential_singleton hJ0 i x, sub_zero, abs_div, abs_neg, abs_mul, abs_two]
        have hcd : couplingDiff J L i i
            = |periodizedCoupling (L + 1) J 0 - J 0| := by
          rw [couplingDiff, ite_eq_left_of_eq_true _ _ (eq_true hcube), sub_self,
            latticeToTorus_zero]
        have hsq : |x i ⬝ᵥ x i| = s i * s i := by
          have hms : s i * s i = x i ⬝ᵥ x i := Real.mul_self_sqrt (dotProduct_self_nonneg (x i))
          rw [hms, abs_of_nonneg (dotProduct_self_nonneg _)]
        rw [hcd, hJ0, sub_zero, hsq]
        have h2 : (0 : ℝ) ≤ |periodizedCoupling (L + 1) J 0| * (s i * s i) :=
          mul_nonneg (abs_nonneg _) (mul_nonneg (hs0 i) (hs0 i))
        linarith
      · have hcd : couplingDiff J L i j
            = |periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j)| := by
          rw [couplingDiff, ite_eq_left_of_eq_true _ _ (eq_true hcube)]
        rw [heisenbergPeriodicPotential_pair heven hcube.1 hcube.2 hij x,
          heisenbergPotential_pair heven hij x,
          show -(periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) * (x i ⬝ᵥ x j))
              - -(J (i - j) * (x i ⬝ᵥ x j))
            = -((periodizedCoupling (L + 1) J (latticeToTorus L (i - j)) - J (i - j))
              * (x i ⬝ᵥ x j)) by ring, abs_neg, abs_mul, hcd]
        exact mul_le_mul_of_nonneg_left (abs_dotProduct_le_sqrt_mul_sqrt (x i) (x j))
          (abs_nonneg _)
    · have hnotsub : ¬ ({i, j} : Finset (Fin d → ℤ)) ⊆ Potential.latticeBox d L := by
        intro hc
        exact hcube ⟨hc (Finset.mem_insert_self i {j}),
          hc (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))⟩
      have hzero : heisenbergPeriodicPotential n J L ({i, j} : Finset (Fin d → ℤ)) x = 0 :=
        congrFun (Potential.periodicModification_of_not_subset
          (Potential.isTorusReduction_latticeTorus d L) hnotsub) x
      have hcd : couplingDiff J L i j = |J (i - j)| := by
        rw [couplingDiff, ite_eq_right_of_eq_false _ _ (eq_false hcube)]
      rw [hzero, zero_sub, abs_neg, hcd]
      by_cases hij : i = j
      · subst hij
        rw [Finset.pair_eq_singleton, heisenbergPotential_singleton hJ0 i x, abs_zero]
        exact mul_nonneg (abs_nonneg _) (mul_nonneg (hs0 i) (hs0 i))
      · rw [heisenbergPotential_pair heven hij x, abs_neg, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_dotProduct_le_sqrt_mul_sqrt (x i) (x j))
          (abs_nonneg _)
  rw [hdiff]
  refine abs_tsum_le_of_pairBound hTabs (fun A hA ↦ ?_) (fun i j hdisj ↦ ?_)
    (couplingDiff_nonneg) (couplingDiff_symm heven) hs0 hsummable hbound
  · change (heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x A
        - (heisenbergPotential n J).hamiltonianTerms Λ x A = 0
    have h1 : heisenbergPeriodicPotential n J L A = 0 := funext fun σ ↦
      heisenbergPeriodicPotential_of_forall_ne (fun p q ↦ hA p q) σ
    have h2 : heisenbergPotential n J A = 0 := funext fun σ ↦
      heisenbergPotential_of_forall_ne (fun p q ↦ hA p q) σ
    by_cases hdisj : Disjoint A Λ
    · simp only [Potential.hamiltonianTerms_of_disjoint hdisj, sub_self]
    · rw [Potential.hamiltonianTerms_of_not_disjoint hdisj,
        Potential.hamiltonianTerms_of_not_disjoint hdisj, h1, h2]
      simp
  · change (heisenbergPeriodicPotential n J L).hamiltonianTerms Λ x ({i, j} : Finset (Fin d → ℤ))
        - (heisenbergPotential n J).hamiltonianTerms Λ x ({i, j} : Finset (Fin d → ℤ)) = 0
    simp only [Potential.hamiltonianTerms_of_disjoint hdisj, sub_self]

/-- **Georgii's `sup_{ω ∈ Ω_t} |H_Λ^{Φ^n - Φ}(ζ ω_{S∖Λ})| ≤ δ_n ∑_{i ∈ Λ}[1 + |ζ_i|²]`** in the
proof of (20.7), with the explicit null sequence
`δ_n = 4(1+t) ∑_{i ∈ Λ} ∑_{m ∉ Λ(n)} |J(i-m)| α(m)` supplied by `tendsto_sum_couplingTail`.

Only the *exterior* spins are constrained — `|x_j| ≤ t α(j)` for `j ∉ Λ` — as in Georgii's
statement, where `ζ ∈ E^Λ` is arbitrary and only `ω ∈ Ω_t` is assumed; this is what makes the
estimate usable inside the partition functions of the two kernels.  The interior bonds are
symmetrised and the exterior bonds absorbed by `sum_mul_tsum_le_of_exterior_le`, whose row bound is
`tsum_couplingDiff_mul_slowGrowth_le`. -/
theorem abs_hamiltonian_heisenbergPeriodicPotential_sub_le_of_exterior_le
    (heven : ∀ m, J (-m) = J m) (hJ0 : J 0 = 0) (hJ : IsSlowlySummable J)
    {Λ : Finset (Fin d → ℤ)} (hΛ : Λ ⊆ Potential.latticeBox d L) {t : ℝ} (ht : 0 ≤ t)
    {x : (Fin d → ℤ) → (Fin n → ℝ)} (hxΩ : x ∈ slowGrowthTailSet d n)
    (hext : ∀ j ∉ Λ, Real.sqrt (x j ⬝ᵥ x j) ≤ t * slowGrowth j) :
    |(heisenbergPeriodicPotential n J L).hamiltonian Λ x
        - (heisenbergPotential n J).hamiltonian Λ x|
      ≤ (4 * (1 + t) * ∑ i ∈ Λ, couplingTail J L i) * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by
  classical
  set R : ℝ := 2 * ∑ i ∈ Λ, couplingTail J L i with hR
  have hct0 : ∀ i, 0 ≤ couplingTail J L i := couplingTail_nonneg J L
  have hR0 : (0 : ℝ) ≤ R := by
    have : (0 : ℝ) ≤ ∑ i ∈ Λ, couplingTail J L i := Finset.sum_nonneg fun i _ ↦ hct0 i
    rw [hR]; linarith
  have hrow : ∀ i ∈ Λ, ∑' j, couplingDiff J L i j * slowGrowth j ≤ R := by
    intro i hi
    refine (tsum_couplingDiff_mul_slowGrowth_le hJ (hΛ hi)).trans ?_
    have := Finset.single_le_sum (f := fun k ↦ couplingTail J L k) (fun k _ ↦ hct0 k) hi
    rw [hR]; linarith
  have hkey := sum_mul_tsum_le_of_exterior_le (Λ := Λ) (c := couplingDiff J L)
    (s := fun i ↦ Real.sqrt (x i ⬝ᵥ x i)) (a := slowGrowth) (t := t) (R := R)
    couplingDiff_nonneg (couplingDiff_symm heven) (fun i ↦ Real.sqrt_nonneg _)
    one_le_slowGrowth ht hR0 (fun i ↦ summable_couplingDiff_mul_slowGrowth hJ i) hrow hext
  have hsq : ∀ i : Fin d → ℤ, Real.sqrt (x i ⬝ᵥ x i) ^ 2 = x i ⬝ᵥ x i := fun i ↦
    Real.sq_sqrt (dotProduct_self_nonneg _)
  simp only [hsq] at hkey
  calc |(heisenbergPeriodicPotential n J L).hamiltonian Λ x
          - (heisenbergPotential n J).hamiltonian Λ x|
      ≤ 2 * ∑ i ∈ Λ, Real.sqrt (x i ⬝ᵥ x i)
          * ∑' j, couplingDiff J L i j * Real.sqrt (x j ⬝ᵥ x j) :=
        abs_hamiltonian_heisenbergPeriodicPotential_sub_le heven hJ0 hJ Λ hxΩ
    _ ≤ 2 * (R * (1 + t) * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i)) := by linarith
    _ = (4 * (1 + t) * ∑ i ∈ Λ, couplingTail J L i) * ∑ i ∈ Λ, (1 + x i ⬝ᵥ x i) := by
        rw [hR]; ring

/-- **Georgii's `(δ_n)` is a null sequence.** -/
theorem tendsto_sum_couplingTail (hJ : IsSlowlySummable J) (Λ : Finset (Fin d → ℤ)) (t : ℝ) :
    Filter.Tendsto (fun L : ℕ ↦ 4 * t * ∑ i ∈ Λ, couplingTail J L i) atTop (𝓝 0) := by
  have hsum : Filter.Tendsto (fun L : ℕ ↦ ∑ i ∈ Λ, couplingTail J L i) atTop (𝓝 0) := by
    have := tendsto_finsetSum Λ fun i (_ : i ∈ Λ) ↦ tendsto_couplingTail hJ i
    simpa using this
  simpa using hsum.const_mul (4 * t)

end HamiltonianComparison




/-! ### Georgii, Proposition (20.7)(b): `𝒢₀(Φ) ≠ ∅` -/

section Nonempty

variable {d n : ℕ} {J : (Fin (d + 1) → ℤ) → ℝ} {ν : Measure (Fin n → ℝ)}

/-- **Georgii's "the sequence `(μ_n^Φ)` satisfies the hypotheses of Theorem (4.12)"** in the proof
of (20.7).  The fields `μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0` are locally equicontinuous: their masses on the
events of a fixed volume are uniformly small when the reference mass is, because the density bound
`heisenbergPeriodicField_inter_slowGrowthSet_le` holds uniformly in the cube on `Ω_t` and
Lemma (20.6)(iii) makes `Ω_t^c` uniformly negligible.

This is the hypothesis both of Proposition (4.9) — which gives `𝒢₀(Φ) ≠ ∅`
(`heisenbergGZero_nonempty`) — and of Proposition (4.15), which extracts from a cluster point a
convergent *subsequence* and is what the proof of `𝒢₀(Φ) ⊆ 𝒢(Φ)` uses. -/
theorem locallyEquicontinuous_heisenbergPeriodicField [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hexp : HasExpSqMoments ν) (heven : ∀ m, J (-m) = J m) (hJ : IsSlowlySummable J)
    (hnd : ∀ k, IsNonnegDefiniteAt k J)
    {μs : ℕ → ProbabilityMeasure ((Fin (d + 1) → ℤ) → (Fin n → ℝ))}
    (hμsval : ∀ L, (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
      = heisenbergPeriodicField J ν L 0) :
    LocallyEquicontinuous atTop μs := by
  classical
  have hsum : Summable J := hJ.summable
  -- Lemma (20.6)(iii), uniformly in the cube
  obtain ⟨b, hb0, hb⟩ := exists_forall_heisenbergPeriodicField_zero_tail_le (d := d) (n := n)
    hν hexp hsum heven hnd (a := ((d : ℝ) + 1) + 1 + 1) (by positivity)
  set C : ℝ := ∑' i : Fin (d + 1) → ℤ, (max (Real.exp 1) ‖i‖) ^ (-(((d + 1 : ℕ) : ℝ) + 1))
    with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun i ↦
    Real.rpow_nonneg (le_trans (Real.exp_pos 1).le (le_max_left _ _)) _
  have hmass : ∀ (t : ℝ), 1 ≤ t → ∀ L : ℕ,
      heisenbergPeriodicField J ν L 0 (slowGrowthSet (d + 1) n t)ᶜ
        ≤ ENNReal.ofReal (b * C * Real.exp (-(1 * t ^ 2))) := by
    intro t ht L
    refine measure_compl_slowGrowthSet_le (a := 1) (b := b)
      (c := ((d : ℝ) + 1) + 1 + 1) one_pos hb0.le ?_ (fun i r ↦ hb L i r) ht
    push_cast
    linarith
  -- Theorem (4.12)
  refine locallyEquicontinuous_of_eventually_measure_inter_le (μs := μs) (l := atTop)
    fun Λ ε hε ↦ ?_
  -- choose `t` so that `μ_n(Ω_t^c) ≤ ε` for every cube
  have hlim : Filter.Tendsto
      (fun t : ℕ ↦ ENNReal.ofReal (b * C * Real.exp (-((t : ℝ))))) atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun t : ℕ ↦ b * C * Real.exp (-((t : ℝ)))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (b * C)
      simpa using this
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using h2
  obtain ⟨t, ht1, htε⟩ : ∃ t : ℕ, 1 ≤ t ∧
      ENNReal.ofReal (b * C * Real.exp (-((t : ℝ)))) ≤ ε := by
    obtain ⟨t₀, ht₀⟩ := (Filter.eventually_atTop.1
      ((ENNReal.tendsto_nhds_zero.1 hlim) ε hε)).imp fun _ h ↦ h
    exact ⟨max 1 t₀, le_max_left _ _, ht₀ _ (le_max_right _ _)⟩
  have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have ht0' : (0 : ℝ) ≤ (t : ℝ) := by positivity
  -- the dominating measure supplied by the density bound
  set κnum : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((t : ℝ) ^ 2
    * ∑ i ∈ Λ, slowGrowth i * ∑' k, |J (i - k)| * slowGrowth k)) with hκnum
  set cc : ℝ := (∑' m, |J m|) + (t : ℝ) * ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k with hccdef
  have hcc0 : 0 ≤ cc := by
    have h1 : (0 : ℝ) ≤ ∑' m, |J m| := tsum_nonneg fun m ↦ abs_nonneg _
    have h2 : (0 : ℝ) ≤ ∑ i ∈ Λ, ∑' k, |J (i - k)| * slowGrowth k :=
      Finset.sum_nonneg fun i _ ↦ tsum_nonneg fun k ↦
        mul_nonneg (abs_nonneg _) (slowGrowth_pos k).le
    rw [hccdef]; positivity
  set δden : ℝ≥0∞ := (∫⁻ y, ENNReal.ofReal (Real.exp (-(cc * (1 + y ⬝ᵥ y)))) ∂ν) ^ Λ.card
    with hδden
  have hδden0 : δden ≠ 0 := pow_ne_zero _ (lintegral_exp_neg_pos hν cc).ne'
  set κm : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)) :=
    (κnum / δden) • ((Measure.pi fun _ : ↥Λ ↦ ν).map
      (Function.updateFinset (0 : (Fin (d + 1) → ℤ) → (Fin n → ℝ)) Λ)) with hκm
  have hmapmeas : Measurable
      (Function.updateFinset (0 : (Fin (d + 1) → ℤ) → (Fin n → ℝ)) Λ) :=
    measurable_updateFinset
  have hκmtop : κm Set.univ ≠ ∞ := by
    rw [hκm, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hmapmeas MeasurableSet.univ, Set.preimage_univ]
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top hδden0)
      (measure_ne_top _ _)
  refine ⟨slowGrowthSet (d + 1) n (t : ℝ), κm, measurableSet_slowGrowthSet _, hκmtop, ?_, ?_⟩
  · filter_upwards [Potential.tendsto_latticeBox_atTop.eventually
      (eventually_ge_atTop Λ)] with L hL A hAcyl
    have hΛL : Λ ⊆ Potential.latticeBox (d + 1) L := hL
    have hAmeas : MeasurableSet A := cylinderEvents_le_pi _ hAcyl
    have hbound := heisenbergPeriodicField_inter_slowGrowthSet_le (ν := ν) hν hexp heven hJ
      hΛL ht0' hAcyl
    rw [hμsval L]
    refine hbound.trans (le_of_eq ?_)
    rw [hκm, Measure.smul_apply, smul_eq_mul, Measure.map_apply hmapmeas hAmeas,
      div_eq_mul_inv, div_eq_mul_inv, ← hκnum, ← hδden]
    exact mul_right_comm _ _ _
  · refine limsup_le_of_le (h := Filter.Eventually.of_forall fun L ↦ ?_)
    rw [hμsval L]
    refine (hmass (t : ℝ) ht1' L).trans (le_trans (ENNReal.ofReal_le_ofReal ?_) htε)
    have hexpmono : Real.exp (-(1 * (t : ℝ) ^ 2)) ≤ Real.exp (-((t : ℝ))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have hbC : (0 : ℝ) ≤ b * C := mul_nonneg hb0.le hC0
    exact mul_le_mul_of_nonneg_left hexpmono hbC

/-- **Georgii, Proposition (20.7), first half: `𝒢₀(Φ) ≠ ∅`.**  The sequence of fields
`μ_n^Φ = °γ_{Λ(n)}^Φ × δ_0` has a cluster point in the topology of local convergence.

Georgii's proof, verbatim: Lemma (20.6)(iii) makes the mass outside `Ω_t` uniformly small, the
"straightforward calculation" `limsup_n sup_{ω ∈ Ω_t} ρ_Λ^n(ω) < ∞` is
`heisenbergPeriodicField_inter_slowGrowthSet_le`, Theorem (4.12)
(`locallyEquicontinuous_of_eventually_measure_inter_le`) gives local equicontinuity
(`locallyEquicontinuous_heisenbergPeriodicField`) and Proposition (4.9)
(`exists_mapClusterPt_of_locallyEquicontinuous`) the cluster point. -/
theorem heisenbergGZero_nonempty [IsFiniteMeasure ν] (hν : ν ≠ 0) (hexp : HasExpSqMoments ν)
    (heven : ∀ m, J (-m) = J m) (hJ : IsSlowlySummable J) (hnd : ∀ k, IsNonnegDefiniteAt k J) :
    (heisenbergGZero J ν).Nonempty := by
  classical
  have hprob : ∀ L : ℕ, IsProbabilityMeasure (heisenbergPeriodicField J ν L 0) := fun L ↦
    isProbabilityMeasure_heisenbergPeriodicField hν hexp hJ.summable L 0
  set μs : ℕ → ProbabilityMeasure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)) :=
    fun L ↦ ⟨heisenbergPeriodicField J ν L 0, hprob L⟩ with hμs
  have hμsval : ∀ L, (μs L : Measure ((Fin (d + 1) → ℤ) → (Fin n → ℝ)))
      = heisenbergPeriodicField J ν L 0 := fun L ↦ rfl
  -- Proposition (4.9)
  obtain ⟨m, hm⟩ := exists_mapClusterPt_of_locallyEquicontinuous
    (μs := fun L ↦ (WithSetwiseTopology.ofMeasure (μs L)
      : WithLocalConvergence (Fin (d + 1) → ℤ) (Fin n → ℝ)))
    (locallyEquicontinuous_heisenbergPeriodicField hν hexp heven hJ hnd hμsval)
  exact ⟨m.toMeasure, μs, hμsval, hm⟩

end Nonempty

end MeasureTheory.GibbsMeasure

end

end

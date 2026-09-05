/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.PSeries.Euclidean
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ExpNegAbs
public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import GibbsMeasure.Mathlib.Data.Fintype.Fiber
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.PosSemidefFactor
public import GibbsMeasure.Mathlib.LinearAlgebra.Matrix.DotProductReal
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.PSeries
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.CircleCharacter
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.BoxAverage
public import Mathlib.Algebra.Order.Star.Real
public import GibbsMeasure.Potential
public import GibbsMeasure.Potential.Summable
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
  `ℬ` (2.11) *fails*, and this is a theorem, not a caveat: over the unbounded spin space `ℝ^n`
  the sup-norm `‖Φ_{{i,j}}‖` of (2.12) is a supremum over all of `(ℝ^n)^{ℤ^d}` and is infinite
  whenever `J(i-j) ≠ 0` (`iSup_enorm_heisenbergPotential_pair_eq_top`), so
  `not_isAbsolutelySummable_heisenbergPotential`.  Georgii does not claim (2.11) either; his
  standing hypotheses in §17.2 are (17.23) and the finiteness of `°Z_Λ^Φ`.  The consequence is
  that *none* of the general Example (4.20)(2) machinery of `GibbsMeasure.Potential.Periodic`
  applies to `heisenbergPotential`: `Potential.isPotential_periodicModification`,
  `Potential.isAbsolutelySummable_periodicModification` and
  `Potential.abs_hamiltonian_periodicModification_sub_le` are all conditioned on
  `IsAbsolutelySummable`.  See "Not formalised" below for what this costs.
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
  crossing matrix is *diagonal* (`crossingMatrix_eq_zero_of_nearestNeighbour`) with entries
  `J(e_k)` times the number of interfaces the site sees (`crossingMatrix_diag_nearestNeighbour`),
  so no appeal to (17.29) is needed.  Only `0 ≤ J(e_k)` is assumed, not `J ≥ 0`: a coupling may
  be antiferromagnetic in the directions transverse to `k` and still give an `r_k`-positive
  `°γ_Λ^Φ` — for instance `J(e_0) = 1`, `J(e_1) = -1` on `ℤ²` is `r_0`-positive.
* **(17.31)** Next-nearest neighbour potentials.  `isNonnegDefiniteAt_of_nextNearestNeighbour`
  is Georgii's representing measure `δ_0(dz_k) [A + B ∑_{c ≠ k}(z_c + z̄_c)] ∏_{c ≠ k} ν(dz_c)`;
  the hypothesis `A ≥ 2(d-1)|B|` is exactly what makes that density nonnegative, and
  `integral_cos_mul_exp_sum_int_mul_I` computes its Fourier coefficients.
  `isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour` is the conclusion.
  `le_of_isNonnegDefiniteAt_nextNearestNeighbour` is the converse — `A ≥ 2(d-1)|B|` is also
  *necessary* for nonnegative definiteness, by evaluating the crossing form at the `±1` patterns
  `q_χ` — so that `isNonnegDefiniteAt_nextNearestNeighbour_iff` is an equivalence.
* **(17.32)** Long range potentials.  `isNonnegDefiniteAt_rpow` is the radial factor in any
  dimension: `J(i) = β i_k^{-a}` for `i_k ≥ 1`, with `β ≥ 0` and `a > 0`, is nonnegative definite
  relative to `r_k`, with Georgii's representing measure `β Γ(a)⁻¹` times the image of the gamma
  distribution under `s ↦ e^{-s}` (`gammaWeight`, `integral_pow_map_exp_neg`); for `d = 1` this
  is his case 1).  For `d = 2`, his case 2), `isNonnegDefiniteAt_longRange_two`: `J(i) = β |i|^{-a}`
  on `ℤ²` is nonnegative definite relative to `r_0` and `r_1` for every `a > 1` (Georgii assumes
  `a > 2`, which is the summability (17.23) and is not needed for the representation).  The proof
  is his, in three steps:
  * `isNonnegDefiniteAt_cauchyMixture`: a mixture `i ↦ ∫ ν(dx) x i_k/(i_c² + x² i_k²)` of Cauchy
    kernels in a transverse direction `c`, with `ν` finite on `[1, ∞)`, is nonnegative definite;
    its representing measure is the image of `½ e^{-x|u|} ν(dx) du` under
    `(x, u) ↦ (e^{-x|u|}, u e_c)`.  This is his "measure kernel `s ↦ π^s`", integrated against `ν`
    once and for all.  The Fourier transform he quotes is
    `MeasureTheory.integral_exp_mul_I_mul_exp_neg_mul_abs`
    (`GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ExpNegAbs`), the transform of the two-sided
    exponential `e^{-a|u|}`, which is the direction actually used; the transform of the Cauchy
    density itself is not needed.
  * `integral_cauchyMixing`: his substitution `(k² + ℓ²)^{-a/2} = k^{1-a} ∫ p(ds) sk/(ℓ² + s²k²)`
    for `1 < a < 2`, with `p` the image of `w^{-a/2}(1 + w)^{-1/2} dw` under `w ↦ √(1 + w)`
    (`cauchyMixing`, his `p(ds)` up to the constant `c(a)` = `cauchyMixingConst`).  In the variable
    `w = s² - 1` his change of variables is the dilation `integral_rpow_div_add_Ioi`
    (`GibbsMeasure.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`).
  * `isNonnegDefiniteAt_sq_add_sq_rpow`: the product of the radial factor and the Cauchy mixture
    by Comment (17.28)(2) (`IsNonnegDefiniteAt.mul`) for `1 < a < 2`; `a = 2` is a single Cauchy
    kernel (`isNonnegDefiniteAt_sq_add_sq_inv`); `a > 2` reduces to `1 < a/n < 2` by
    `IsNonnegDefiniteAt.pow`, exactly as in the book.

  `isReflectionPositive_heisenbergPeriodicGibbs_longRange_one` is Georgii's conclusion for
  `d = 1` and `a > 1`, and `isReflectionPositive_heisenbergPeriodicGibbs_longRange_two` his
  conclusion for `d = 2` and `a > 2`, the absolute summability (17.23) being
  `Real.summable_abs_int_rpow` resp. `summable_sum_sq_rpow_fin_two`
  (`GibbsMeasure.Mathlib.Analysis.PSeries.Euclidean`).

## The necessity halves of (17.30) and (17.31)

Georgii's converses are proved for the two-point a priori measure `λ = δ_1 + δ_{-1}`
(`twoPointMeasure`, so `n = 1` and the spins are `±1`).

* `patternSet`, `patternConfig`, `patternTest`: Georgii's test function
  `f = e^{-h} σ_u 1_{σ_i = σ_u for all i ∈ Λ_{+,k}}` attached to a `±1` pattern `q` on
  `Λ_{+,k}`, with the prefactor `e^{-h}` dropped — on the configurations that carry `λ^Λ` and
  satisfy the indicator, `h` is a *constant*, and dropping it is what keeps `f` bounded, as
  Georgii's `𝒜_{+,k}` requires.
* `integral_patternTest_mul_comp_heisenbergPeriodicGibbs`: **the mechanism**,
  `°Z_Λ^Φ °γ_Λ^Φ(f f^*) = 4 e^{S} sinh⟨q, M q⟩` with `S = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) q_i q_j` and
  `M` the crossing matrix.  Only four configurations survive the product of the two indicators
  (`mem_patternSet_and_comp_iff`), and `λ^Λ` gives each of them mass one
  (`pi_twoPointMeasure_singleton`).
* `not_isReflectionPositive_heisenbergPeriodicGibbs_of_crossing_neg`: any `±1` vector `q` with
  `⟨q, M q⟩ < 0` refutes `r_k`-positivity.  This is the converse of
  `isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef`.
* **(17.30), necessity.**  `crossingMatrix_diag_nearestNeighbour` and
  `dotProduct_one_crossingMatrix_nearestNeighbour` compute `⟨1, M 1⟩ = 2 (2N)^{d-1} J(e_k)`;
  `integral_patternTest_mul_comp_nearestNeighbour` and
  `integral_georgiiTest_mul_comp_nearestNeighbour` are the value of the reflection form, and
  `not_isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour` is Georgii's conclusion.

  **Two errata to Example (17.30).**  (i) The constant is `2(2N)^{d-1}`, not `(2N)^{d-1}`: on the
  torus the plane of `r_k` is met by *two* interfaces — between the layers `i_k = N-1` and
  `i_k = N`, and between `i_k = 2N-1` and `i_k = 0` — and each carries `(2N)^{d-1}` bonds.
  (ii) The displayed middle expression `∑_{x,y=±1} exp[C J(u) x y]` is `4 cosh[C J(u)]`, not
  `4 sinh`; the factor `σ_u σ_{r_k u} = x y` coming from `f f^*` is missing from it.  The final
  value `4 sinh` is correct.  Only the sign of the constant matters for Georgii's conclusion.
* **The crossing form as a sum over bonds.**  `dotProduct_crossingMatrix_mulVec_eq_tsum`: for
  an absolutely summable `J` and any `q`, `⟨q, M q⟩ = ∑_{m ∈ ℤ^d} J(m) w_q(m)`, where `w_q(m)`
  (`crossingWeight`) is the `q`-weighted number of copies of the bond `m` that join `Λ_{-,k}` to
  `Λ_{+,k}`.  This unfolds the periodisation (`periodizedCoupling_eq_tsum_ite`) and is how both
  necessity computations are organised.  A bond with `m_k = 0` never crosses the plane
  (`crossingWeight_of_apply_eq_zero`); for the `±1` patterns `q_χ(i) = ∏_{c ≠ k} χ_c^{i_c}`
  (`transversePattern`), a bond with `m_k = ±1` crosses once from each of the `(2N)^{d-1}` sites
  of one layer, with the sign `∏_{c ≠ k} χ_c^{|m_c|}` (`crossingWeight_transversePattern`).
* **(17.31), necessity, and an erratum.**  Georgii refutes `r_k`-positivity for `A < 2(d-1)|B|`
  "by looking at the same function `f` and also at `f̃ = e^{-h} σ_u 1_{σ_i = -(-1)^{i_k} σ_u}`".
  The second test function *cannot* work as printed: `even_val_add_val_of_crossingMatrix_ne_zero`
  shows that a bond crossing the plane of `r_k` joins `r_k i` to `j` with `i_k = j_k`, so an
  alternation in the direction `k` cancels, and `dotProduct_neg_one_pow_crossingMatrix` /
  `integral_patternTest_neg_one_pow_mul_comp` prove that `f̃` has exactly the same hyperbolic sine
  as `f`, for *every* next-nearest neighbour coupling.  Georgii's `i_k` must be read as an
  alternation in the directions *transverse* to `k`, and with that reading his argument is
  correct: `dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour` computes
  `⟨q_χ, M q_χ⟩ = 2(2N)^{d-1}(A + 2B ∑_{c ≠ k} χ_c)`, so the constant pattern `χ = 1` (his `f`)
  refutes positivity when `A < -2(d-1)B` and the fully alternating one `χ = -1` (the corrected
  `f̃`) when `A < 2(d-1)B`; `integral_patternTest_transversePattern_mul_comp_nextNearestNeighbour`
  is the value of the reflection form, `4 e^{S_χ} sinh[2(2N)^{d-1}(A + 2B ∑_{c≠k} χ_c)]`, and
  `not_isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour` is the conclusion.
  (The same factor `2` as in (17.30) is missing from the constant Georgii's `f` would produce.)

## Invariance, normalisation, and the a priori bounds used in Chapter 20

The last section of the file collects what the chessboard estimate (17.11) and Georgii's §20.1
need from `°γ_Λ^Φ`, and is the reason `GibbsMeasure.Specification.InfraredBound` can be short.

* `sum_periodizedCoupling`, `sum_abs_periodizedCoupling_le` and the two `_sub` variants: the row
  and column sums of the periodised coupling matrix, `∑_{j ∈ Λ} |J_Λ(i-j)| ≤ ‖J‖₀`.
* `abs_heisenbergExponent_le`: `|½ ∑_{i,j} J_Λ(i-j) σ_i·σ_j| ≤ ½‖J‖₀ ∑_i |σ_i|²`, Georgii's
  estimate at the start of the proof of (20.6) with the sharper constant `½‖J‖₀`;
  `le_heisenbergExponent_of_le` and `heisenbergExponent_le_of_le` are its two-sided versions on
  configurations with prescribed pairwise scalar products, which is what Lemma (20.8) uses.
* `heisenbergExponent_shift`, `heisenbergExponent_torusReflAt` and the four
  `measurePreserving_*_heisenbergPeriodicGibbs(Dist)` theorems: `Λ`-periodicity (Georgii's remark
  after (17.20)) and `r_k`-invariance, the two hypotheses of (17.11) besides `r_k`-positivity.
* `isFiniteMeasure_heisenbergPeriodicGibbs`, `heisenbergPeriodicGibbs_univ_pos` and
  `isProbabilityMeasure_heisenbergPeriodicGibbsDist`: `0 < °Z_Λ^Φ < ∞`.
* `heisenbergPeriodicGibbs_forall_mem_le`, `le_heisenbergPeriodicGibbs_univ`,
  `heisenbergPeriodicGibbs_forall_mem_le_pow` and `le_heisenbergPeriodicGibbs_univ_pow`: the four
  `|Λ|`-th power bounds on `°Z_Λ^Φ °γ_Λ^Φ(A^Λ)` and on `°Z_Λ^Φ` that Georgii uses in (20.6) and
  (20.8) — uniform on `A^Λ` in the first pair, one-site products in the second.

## Not formalised

* Georgii's Comment (17.28)(1), the Berg–Maserick converse (see above).  It is a citation, proved
  neither in the book nor here.  For the functions actually used in §17.2 there is no short route:
  every application in (17.30)–(17.32) goes the *easy* way (exhibit `α`), and the only place the
  converse would be needed is to show a given `J` is *not* nonnegative definite — which
  `IsNonnegDefiniteAt.nonneg_of_odd` already does in the cases Georgii uses.
* The Fourier transform of the Cauchy density, `∫_ℝ cos(tx)/(1 + x²) dx = π e^{-|t|}`, which
  Georgii quotes in Example (17.32).  Only the converse direction — the transform of `e^{-a|x|}`
  is the Cauchy kernel, `MeasureTheory.integral_exp_mul_I_mul_exp_neg_mul_abs` — is used, and
  only that is proved.
* The closed form of Georgii's constant `c(a)` in Example (17.32) (a Beta integral); only
  `0 < c(a) < ∞` is needed (`integral_rpow_div_one_add_Ioi_pos`,
  `integrableOn_rpow_div_one_add_Ioi`), and that is proved.
* **The identification of (17.24) with the periodic modification of `heisenbergPotential`.**
  `heisenbergPeriodicGibbs` is *defined* by the density (17.24) and by
  `interactingHamiltonian_heisenbergPeriodicGibbs`-style computation it is not yet identified
  with `γ^{Φ̃^Λ}_Λ(·|ω)` for `Φ̃^Λ = Potential.periodicModification (heisenbergPotential n J)`,
  Georgii's Example (4.20)(2).  The obstruction is *not* the statement — Georgii's own `Φ^n` in
  the proof of (20.7) is exactly `Φ̃^Λ` and the computation is

  `Φ̃^Λ_{{i,j}} = -J_Λ(i-j) σ_i·σ_j` (`i ≠ j`),   `Φ̃^Λ_{{i}} = -½ J_Λ(0) |σ_i|²`,

  which sums over `Λ` to minus `heisenbergExponent` — but the *route*: the representatives
  `ℛ(A)` of (4.20)(2) form an infinite set here (all period translates of a bond), so the
  defining `tsum` converges only because of (17.23), and every general lemma about
  `periodicModification` in `GibbsMeasure.Potential.Periodic` is conditioned on
  `IsAbsolutelySummable`, which `not_isAbsolutelySummable_heisenbergPotential` shows is false.
  What is needed is a direct enumeration of `ℛ({i,j})` and `ℛ({i})`: for a relative period
  `r ∈ 2Nℤ^d` exactly one translate of the bond `{i, j + r}` has its `lexAnchor` in the box, and
  for a singleton the representatives are the bonds `{i, i + r}` with `r` lex-positive — which is
  where the factor `½` on the diagonal of (17.24) comes from.  The extra hypothesis this needs is
  exactly `Summable J`, i.e. Georgii's (17.23).
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

/-- **The periodised coupling as a sum over the fibre of the projection `ℤ^d → (ℤ/2N)^d`.**
`J_Λ(z) = ∑_{m ∈ ℤ^d, m ≡ z} J(m)`: the lift `ℓ ↦ lift z + 2Nℓ` is a bijection of `ℤ^d` onto the
fibre of `z`. -/
lemma periodizedCoupling_eq_tsum_ite (z : Fin d → ZMod (2 * N)) :
    periodizedCoupling N J z
      = ∑' m : Fin d → ℤ, if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then J m else 0 := by
  classical
  set g : (Fin d → ℤ) → (Fin d → ℤ) := fun ℓ ↦ torusLift N z + (2 * N : ℤ) • ℓ with hg
  have h2N : (2 * N : ℤ) ≠ 0 := by have := NeZero.ne N; omega
  have hinj : Function.Injective g := by
    intro ℓ ℓ' h
    funext c
    have := congrFun h c
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ h2N (by linarith)
  have hcast : ∀ ℓ : Fin d → ℤ, (fun c ↦ ((g ℓ c : ℤ) : ZMod (2 * N))) = z := by
    intro ℓ
    funext c
    have h0 : ((2 * N : ℤ) : ZMod (2 * N)) = 0 := by
      have h := ZMod.natCast_self (2 * N)
      exact_mod_cast h
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul,
      intCast_torusLift, h0, zero_mul, add_zero]
  have hsupp : Function.support
      (fun m : Fin d → ℤ ↦ if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then J m else 0)
        ⊆ Set.range g := by
    intro m hm
    have hmz : (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z := by
      by_contra h
      exact hm (by simp [h])
    have hdvd : ∀ c, ((2 * N : ℕ) : ℤ) ∣ (m c - torusLift N z c) := by
      intro c
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast [torusLift, congrFun hmz c]
      simp [ZMod.natCast_val]
    choose t ht using fun c ↦ (hdvd c)
    refine ⟨t, ?_⟩
    funext c
    have := ht c
    simp only [hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast at this
    linarith
  rw [periodizedCoupling, ← hinj.tsum_eq hsupp]
  exact tsum_congr fun ℓ ↦ by rw [ite_eq_left (hcast ℓ)]

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

/-! ### The Heisenberg potential is not absolutely summable over an unbounded spin space -/

/-- **The sup-norm (2.12) of a Heisenberg pair interaction is infinite** when the spin space is
the whole of `ℝ^n`, `n ≥ 1`: the constant configuration with spins `t e_0` gives the pair
interaction the value `-J(i-j) t²`, which is unbounded in `t`. -/
theorem iSup_enorm_heisenbergPotential_pair_eq_top (hn : 0 < n) (heven : ∀ m, J (-m) = J m)
    {i j : Fin d → ℤ} (hij : i ≠ j) (hJ : J (i - j) ≠ 0) :
    ⨆ ω : (Fin d → ℤ) → (Fin n → ℝ), ‖heisenbergPotential n J {i, j} ω‖ₑ = ⊤ := by
  classical
  have hJpos : 0 < |J (i - j)| := abs_pos.2 hJ
  refine iSup_eq_top.2 fun b hb ↦ ?_
  set t : ℝ := Real.sqrt ((b.toReal + 1) / |J (i - j)|) with ht
  set ω : (Fin d → ℤ) → (Fin n → ℝ) :=
    fun _ c ↦ if c = ⟨0, hn⟩ then t else 0 with hω
  have hdot : ω i ⬝ᵥ ω j = t ^ 2 := by
    rw [dotProduct]
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · simp [hω, sq]
    · intro c _ hc
      simp [hω, hc]
    · intro h
      exact absurd (Finset.mem_univ (⟨0, hn⟩ : Fin n)) h
  have ht2 : t ^ 2 = (b.toReal + 1) / |J (i - j)| := by
    rw [ht, Real.sq_sqrt]
    positivity
  have hval : ‖heisenbergPotential n J {i, j} ω‖ₑ = ENNReal.ofReal (b.toReal + 1) := by
    rw [heisenbergPotential_pair heven hij ω, hdot, Real.enorm_eq_ofReal_abs, abs_neg, abs_mul,
      abs_of_nonneg (sq_nonneg t), ht2]
    congr 1
    field_simp
  refine ⟨ω, ?_⟩
  rw [hval]
  calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne).symm
    _ < ENNReal.ofReal (b.toReal + 1) := by
        refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.2 (by linarith)

/-- **The Heisenberg potential is not absolutely summable** (Georgii (2.11)) as soon as the spin
space is unbounded (`n ≥ 1`) and `J` does not vanish identically off the origin.

This is why none of the general theory of Georgii's Example (4.20)(2) in
`GibbsMeasure.Potential.Periodic` applies to it: `Potential.isPotential_periodicModification`,
`Potential.isAbsolutelySummable_periodicModification` and
`Potential.abs_hamiltonian_periodicModification_sub_le` all require `IsAbsolutelySummable`.
Georgii does not claim (2.11) either; his standing hypotheses in §17.2 are the summability
(17.23) of `J` and the finiteness of `°Z_Λ^Φ`. -/
theorem not_isAbsolutelySummable_heisenbergPotential (hn : 0 < n) (heven : ∀ m, J (-m) = J m)
    (hJ : ∃ m : Fin d → ℤ, m ≠ 0 ∧ J m ≠ 0) :
    ¬ Potential.IsAbsolutelySummable (heisenbergPotential n J) := by
  classical
  obtain ⟨m, hm0, hmJ⟩ := hJ
  intro hsum
  have hmem : ({m, 0} : Finset (Fin d → ℤ))
      ∈ {A : Finset (Fin d → ℤ) | (0 : Fin d → ℤ) ∈ A} :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hterm : ⨆ ω : (Fin d → ℤ) → (Fin n → ℝ), ‖heisenbergPotential n J {m, 0} ω‖ₑ = ⊤ :=
    iSup_enorm_heisenbergPotential_pair_eq_top hn heven hm0 (by simpa using hmJ)
  refine hsum.normAt_ne_top (0 : Fin d → ℤ) (top_le_iff.1 ?_)
  calc (⊤ : ℝ≥0∞) = {A : Finset (Fin d → ℤ) | (0 : Fin d → ℤ) ∈ A}.indicator
        (fun A ↦ ⨆ ω : (Fin d → ℤ) → (Fin n → ℝ), ‖heisenbergPotential n J A ω‖ₑ)
        ({m, 0} : Finset (Fin d → ℤ)) := by
        rw [Set.indicator_of_mem hmem, hterm]
    _ ≤ Potential.normAt (heisenbergPotential n J) 0 := ENNReal.le_tsum _

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

/-- Nonnegative definiteness relative to `r_k` only sees the values of `J` on `{i_k ≥ 1}`. -/
lemma IsNonnegDefiniteAt.congr {J' : (Fin d → ℤ) → ℝ} (h : IsNonnegDefiniteAt k J)
    (hJJ' : ∀ i : Fin d → ℤ, 1 ≤ i k → J i = J' i) : IsNonnegDefiniteAt k J' := by
  obtain ⟨α, hα, hsupp, hrep⟩ := h
  exact ⟨α, hα, hsupp, fun i hi ↦ by rw [← hJJ' i hi]; exact hrep i hi⟩

/-- A nonnegative multiple of a function that is nonnegative definite relative to `r_k` is
nonnegative definite relative to `r_k`: scale the representing measure. -/
lemma IsNonnegDefiniteAt.const_mul {β : ℝ} (hβ : 0 ≤ β) (h : IsNonnegDefiniteAt k J) :
    IsNonnegDefiniteAt k fun i ↦ β * J i := by
  obtain ⟨α, hα, hsupp, hrep⟩ := h
  refine ⟨ENNReal.ofReal β • α, ⟨?_⟩, ?_, fun i hi ↦ ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · exact Measure.ae_smul_measure hsupp _
  · rw [integral_smul_measure, ENNReal.toReal_ofReal hβ, ← hrep i hi, Complex.real_smul]
    push_cast
    rfl

/-- **Georgii, Comment (17.28)(2), iterated.**  The positive powers of a function that is
nonnegative definite relative to `r_k` are nonnegative definite relative to `r_k`. -/
lemma IsNonnegDefiniteAt.pow (h : IsNonnegDefiniteAt k J) :
    ∀ n : ℕ, IsNonnegDefiniteAt k fun i ↦ J i ^ (n + 1)
  | 0 => by simpa using h
  | n + 1 => ((h.pow n).mul h).congr fun i _ ↦ by simp [pow_succ]

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


/-! #### Georgii, Example (17.32): long range potentials, the radial factor

From `Γ(a) = ∫_0^∞ e^{-s} s^{a-1} ds` one gets `m^{-a} = Γ(a)^{-1} ∫_0^∞ e^{-ms} s^{a-1} ds` for
`m ≥ 1`, so a function of `i_k` alone, `J(i) = β i_k^{-a}`, is represented by `β Γ(a)⁻¹` times the
image of the gamma weight under `s ↦ e^{-s}` — carried by `]0, 1[` — in the radial variable, and
by the Dirac mass at the trivial character in the transverse variables.  For `d = 1` this is
Georgii's case 1) of Example (17.32), the whole of `J(i) = β |i|^{-a}`; for `d = 2` it is the factor
`k^{1-a}` of his case 2), which is completed below (`isNonnegDefiniteAt_longRange_two`). -/

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

/-- **Georgii, Example (17.32), the radial factor in any dimension.**  A coupling whose value at
`i` with `i_k ≥ 1` is `β i_k^{-a}`, with `β ≥ 0` and `a > 0` — and arbitrary dependence on nothing
else — is nonnegative definite relative to `r_k`, with representing measure `β Γ(a)⁻¹` times the
image of the gamma weight under `s ↦ e^{-s}`, in the radial variable, and the Dirac mass at the
trivial character in the transverse variables. -/
theorem isNonnegDefiniteAt_rpow {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k → J i = β * ((i k : ℝ)) ^ (-a)) :
    IsNonnegDefiniteAt k J := by
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
  refine isNonnegDefiniteAt_of_prod (ρ := ρ) ?_ (σ := Measure.dirac (0 : Fin d → ℝ)) ?_
  · exact (Measure.absolutelyContinuous_of_le_smul (μ := Measure.map
      (fun s : ℝ ↦ Real.exp (-s)) (gammaWeight a)) le_rfl) ae_abs_lt_one_map_exp_neg
  · intro i hi
    have hipos : (0 : ℝ) < (i k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i k)
    have hz : (((i k - 1).toNat : ℕ) : ℤ) = i k - 1 := Int.toNat_of_nonneg (by omega)
    have hm' : (((i k - 1).toNat : ℕ) : ℝ) + 1 = (i k : ℝ) := by
      have h : (((i k - 1).toNat : ℕ) : ℝ) = (i k : ℝ) - 1 := by exact_mod_cast hz
      rw [h]; ring
    have hang : ∫ θ : Fin d → ℝ,
        Complex.exp (Complex.I * ∑ c ∈ Finset.univ.erase k, (i c : ℂ) * (θ c : ℂ))
          ∂(Measure.dirac (0 : Fin d → ℝ)) = 1 := by
      rw [integral_dirac]
      simp
    have hreal : ∫ x, x ^ (i k - 1).toNat ∂ρ = J i := by
      rw [hρdef, integral_smul_measure, integral_pow_map_exp_neg ha,
        ENNReal.toReal_ofReal (div_nonneg hβ hΓ.le), smul_eq_mul, hJ i hi, hm', one_div,
        Real.inv_rpow hipos.le, ← Real.rpow_neg hipos.le]
      field_simp
    have hcast : ∫ x, (x : ℂ) ^ (i k - 1).toNat ∂ρ
        = ((∫ x, x ^ (i k - 1).toNat ∂ρ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by push_cast; ring)
    rw [hang, mul_one, hcast, hreal]

end LongRange

/-! ### Mixtures of Cauchy kernels -/

/-- `∫_ℝ ½ e^{-a|u|} du = 1/a` in `ℝ≥0∞`. -/
lemma lintegral_ofReal_exp_neg_mul_abs_div_two {a : ℝ} (ha : 0 < a) :
    ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-(a * |u|)) / 2) = ENNReal.ofReal (1 / a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_abs ha).div_const 2)
    (Filter.Eventually.of_forall fun u ↦ by positivity), integral_div,
    integral_exp_neg_mul_abs ha]
  congr 1
  field_simp

/-- The mass of `½ e^{-x s |u|} ν(dx) du` is at most `ν(ℝ)` when `ν` is carried by `[1, ∞)` and
`s ≥ 1`. -/
lemma lintegral_prod_ofReal_exp_neg_mul_abs_div_two_le (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ x ∂ν, 1 ≤ x) {s : ℝ} (hs : 1 ≤ s) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(p.1 * s * |p.2|)) / 2) ∂(ν.prod volume)
      ≤ ν Set.univ := by
  have hmeas : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (Real.exp (-(p.1 * s * |p.2|)) / 2) := by
    fun_prop
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine le_trans (lintegral_mono_ae (g := fun _ ↦ (1 : ℝ≥0∞)) ?_) (by rw [lintegral_const, one_mul])
  filter_upwards [hν] with x hx
  have hxs : 0 < x * s := by positivity
  rw [lintegral_ofReal_exp_neg_mul_abs_div_two hxs]
  exact ENNReal.ofReal_le_one.2 (by rw [div_le_one hxs]; nlinarith)

/-- **A mixture of Cauchy kernels is nonnegative definite relative to `r_k`.**  Let `c ≠ k` be a
transverse direction and `ν` a finite measure on `[1, ∞)`.  The function

`J(i) = ∫ ν(dx) x i_k / (i_c² + x² i_k²)`

is nonnegative definite relative to `r_k`.  Its representing measure is the image of
`½ e^{-x|u|} ν(dx) du` under `(x, u) ↦ (e^{-x|u|}, u e_c)`: by the Fourier transform of the
two-sided exponential (`integral_exp_mul_I_mul_exp_neg_mul_abs`),
`x i_k/(i_c² + x² i_k²) = ½ ∫ e^{i u i_c} e^{-x i_k |u|} du`, and `e^{-x i_k |u|}` is the power
`(e^{-x|u|})^{i_k - 1}` times the density `e^{-x|u|}`.

This is Georgii's "measure kernel `s ↦ π^s`" in Example (17.32), with the kernel integrated
against `ν` once and for all. -/
theorem isNonnegDefiniteAt_cauchyMixture {c : Fin d} (hck : c ≠ k) (ν : Measure ℝ)
    [IsFiniteMeasure ν] (hν : ∀ᵐ x ∂ν, 1 ≤ x)
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k →
      J i = ∫ x, x * (i k : ℝ) / ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2) ∂ν) :
    IsNonnegDefiniteAt k J := by
  classical
  set ρ : ℝ × ℝ → ℝ := fun p ↦ Real.exp (-(p.1 * |p.2|)) / 2 with hρ
  have hρm : Measurable ρ := by fun_prop
  have hρnn : ∀ p, 0 ≤ ρ p := fun p ↦ by positivity
  set base : Measure (ℝ × ℝ) :=
    (ν.prod volume).withDensity fun p ↦ ((ρ p).toNNReal : ℝ≥0∞) with hbase
  set Φ : ℝ × ℝ → ℝ × (Fin d → ℝ) :=
    fun p ↦ (Real.exp (-(p.1 * |p.2|)), Pi.single c p.2) with hΦ
  have hsingle : Continuous fun u : ℝ ↦ (Pi.single c u : Fin d → ℝ) := by
    refine continuous_pi fun c' ↦ ?_
    simp only [Pi.single_apply]
    split_ifs <;> fun_prop
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk ?_ (hsingle.comp continuous_snd)
    fun_prop
  have hΦm : Measurable Φ := hΦc.measurable
  have hae : ∀ᵐ p ∂(ν.prod (volume : Measure ℝ)), 1 ≤ p.1 ∧ p.2 ≠ 0 := by
    have hmeasS : MeasurableSet {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.2 ≠ 0} :=
      (measurableSet_le measurable_const measurable_fst).inter
        ((measurableSet_singleton (0 : ℝ)).compl.preimage measurable_snd)
    rw [Measure.ae_prod_iff_ae_ae hmeasS]
    filter_upwards [hν] with x hx
    have h0 : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with u hu
    exact ⟨hx, hu⟩
  have hbase_ae : ∀ᵐ p ∂base, 1 ≤ p.1 ∧ p.2 ≠ 0 := (withDensity_absolutelyContinuous _ _) hae
  refine ⟨Measure.map Φ base, ⟨?_⟩, ?_, fun i hi ↦ ?_⟩
  · -- finiteness
    rw [Measure.map_apply hΦm MeasurableSet.univ, Set.preimage_univ, hbase,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    refine lt_of_le_of_lt ?_ (measure_lt_top ν Set.univ)
    have := lintegral_prod_ofReal_exp_neg_mul_abs_div_two_le ν hν (s := 1) le_rfl
    simpa [hρ, ENNReal.ofReal] using this
  · -- carried by `|x| < 1`
    rw [ae_map_iff hΦm.aemeasurable measurableSet_abs_fst_lt_one]
    filter_upwards [hbase_ae] with p hp
    show |Real.exp (-(p.1 * |p.2|))| < 1
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    have : 0 < |p.2| := abs_pos.2 hp.2
    nlinarith
  · -- the representation
    have hik : (0 : ℝ) < (i k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i k)
    have hik1 : (1 : ℝ) ≤ (i k : ℝ) := by exact_mod_cast hi
    set n := (i k - 1).toNat with hn
    have hn1 : ((n : ℕ) : ℝ) + 1 = (i k : ℝ) := by
      have hz : ((n : ℕ) : ℤ) = i k - 1 := Int.toNat_of_nonneg (by omega)
      have h' : ((n : ℕ) : ℝ) = (i k : ℝ) - 1 := by exact_mod_cast hz
      rw [h']; ring
    set F : ℝ × ℝ → ℂ := fun p ↦ (ρ p : ℂ) * repCharacter k i (Φ p) with hF
    have hFeq : ∀ p : ℝ × ℝ, F p = (1 / 2 : ℂ) * (Complex.exp ((i c : ℝ) * p.2 * Complex.I)
        * (Real.exp (-(p.1 * (i k : ℝ) * |p.2|)) : ℂ)) := by
      intro p
      have hsum : ∑ c' ∈ Finset.univ.erase k, (i c' : ℂ) * (((Pi.single c p.2 : Fin d → ℝ) c' : ℝ) : ℂ)
          = (i c : ℂ) * (p.2 : ℂ) := by
        rw [Finset.sum_eq_single c (fun c' _ hc' ↦ by simp [Pi.single_eq_of_ne hc'])
          (fun h ↦ absurd (Finset.mem_erase.2 ⟨hck, Finset.mem_univ c⟩) h)]
        simp
      have hexp : Real.exp (-(p.1 * |p.2|)) ^ n * Real.exp (-(p.1 * |p.2|))
          = Real.exp (-(p.1 * (i k : ℝ) * |p.2|)) := by
        rw [← pow_succ, ← Real.exp_nat_mul]
        congr 1
        push_cast
        rw [hn1]
        ring
      have hexpc : Complex.exp (Complex.I * ((i c : ℂ) * (p.2 : ℂ)))
          = Complex.exp (((i c : ℝ) : ℂ) * (p.2 : ℂ) * Complex.I) := by
        congr 1
        push_cast
        ring
      simp only [hF, hρ, repCharacter, hΦ, hsum, hexpc]
      rw [← hexp]
      push_cast
      ring
    have hFm : Measurable F :=
      (Complex.measurable_ofReal.comp hρm).mul ((continuous_repCharacter i).measurable.comp hΦm)
    have hFint : Integrable F (ν.prod volume) := by
      refine ⟨hFm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt ?_ (measure_lt_top ν Set.univ)
      have hnorm : ∀ p : ℝ × ℝ, ‖F p‖ₑ = ENNReal.ofReal (Real.exp (-(p.1 * (i k : ℝ) * |p.2|)) / 2) := by
        intro p
        rw [← ofReal_norm, hFeq]
        congr 1
        rw [norm_mul, norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        norm_num
        ring
      simp_rw [hnorm]
      exact lintegral_prod_ofReal_exp_neg_mul_abs_div_two_le ν hν hik1
    calc (J i : ℂ) = ((∫ x, x * (i k : ℝ) / ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2) ∂ν : ℝ) : ℂ) := by
          rw [hJ i hi]
      _ = ∫ x, ((x * (i k : ℝ) / ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2) : ℝ) : ℂ) ∂ν :=
          integral_complex_ofReal.symm
      _ = ∫ x, ∫ u, F (x, u) ∂volume ∂ν := by
          refine integral_congr_ae ?_
          filter_upwards [hν] with x hx
          have hxk : 0 < x * (i k : ℝ) := by positivity
          simp_rw [hFeq]
          rw [integral_const_mul, integral_exp_mul_I_mul_exp_neg_mul_abs hxk (i c : ℝ)]
          push_cast
          have hne : ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2 : ℂ) ≠ 0 := by
            have : (0 : ℝ) < (i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2 := by positivity
            exact_mod_cast this.ne'
          field_simp
          ring
      _ = ∫ p, F p ∂(ν.prod volume) := (integral_prod F hFint).symm
      _ = ∫ p, repCharacter k i (Φ p) ∂base := by
          rw [hbase, integral_withDensity_eq_integral_smul hρm.real_toNNReal]
          refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
          simp only [hF, NNReal.smul_def, Real.coe_toNNReal _ (hρnn p), Complex.real_smul]
      _ = ∫ p, repCharacter k i p ∂(Measure.map Φ base) :=
          (integral_map hΦm.aemeasurable (continuous_repCharacter i).aestronglyMeasurable).symm

/-! ### Georgii, Example (17.32) in dimension two -/

section LongRangeTwo

variable (a : ℝ)

/-- **Georgii's constant `c(a)` in Example (17.32)**, `∫_0^∞ w^{-a/2}/(1 + w) dw`.  Georgii
writes it as `∫_0^∞ t^{1-a}/(1 + t²) dt`, which is the same number after `w = t²`. -/
def cauchyMixingConst : ℝ := ∫ w in Ioi (0 : ℝ), w ^ (-(a / 2)) / (1 + w)

/-- The weight `w^{-a/2} (1 + w)^{-1/2} dw` on `(0, ∞)`; its image under `w ↦ √(1 + w)` is
Georgii's `p(ds)` of Example (17.32) up to the normalisation `c(a)`. -/
def cauchyMixingWeight : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    fun w ↦ ENNReal.ofReal (w ^ (-(a / 2)) * (1 + w) ^ (-(1 / 2 : ℝ)))

/-- **Georgii's mixing measure `p(ds)` of Example (17.32)**, up to the normalisation `c(a)`:
the image of `cauchyMixingWeight a` under `w ↦ √(1 + w)`, a finite measure on `[1, ∞)`.

Georgii parametrises it by `s ∈ [1, ∞)` with the density `c(a)^{-1}(s² - 1)^{-a/2} ds`; the
variable `w = s² - 1` is used here because in it his substitution
`s = (1 + t²(1 + ℓ²/k²))^{1/2}` becomes the *linear* change of variables `w ↦ (k² + ℓ²) w / k²`
(`integral_rpow_div_add_Ioi`). -/
def cauchyMixing : Measure ℝ :=
  Measure.map (fun w : ℝ ↦ Real.sqrt (1 + w)) (cauchyMixingWeight a)

variable {a}

lemma measurable_cauchyMixingDensity :
    Measurable fun w : ℝ ↦ w ^ (-(a / 2)) * (1 + w) ^ (-(1 / 2 : ℝ)) := by fun_prop

lemma isFiniteMeasure_cauchyMixingWeight (ha₁ : 1 < a) (ha₂ : a < 2) :
    IsFiniteMeasure (cauchyMixingWeight a) :=
  isFiniteMeasure_withDensity_ofReal
    (integrableOn_rpow_mul_one_add_rpow_Ioi (by linarith) (by linarith)).hasFiniteIntegral

lemma isFiniteMeasure_cauchyMixing (ha₁ : 1 < a) (ha₂ : a < 2) :
    IsFiniteMeasure (cauchyMixing a) :=
  haveI := isFiniteMeasure_cauchyMixingWeight ha₁ ha₂
  Measure.isFiniteMeasure_map _ _

/-- Georgii's mixing measure is carried by `[1, ∞)`. -/
lemma ae_one_le_cauchyMixing : ∀ᵐ x ∂(cauchyMixing a), 1 ≤ x := by
  rw [cauchyMixing, ae_map_iff (by fun_prop : Measurable fun w : ℝ ↦ Real.sqrt (1 + w)).aemeasurable
    (measurableSet_Ici (a := (1 : ℝ)))]
  have h : ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))), 1 ≤ Real.sqrt (1 + w) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun w hw ↦ Real.one_le_sqrt.2 (by linarith [mem_Ioi.1 hw])
  exact (withDensity_absolutelyContinuous _ _) h

/-- **Georgii's substitution in Example (17.32).**  For `1 < a < 2`, `K > 0` and any `L`,

`∫ p(dx) x K/(L² + x² K²) = K^{a-1} c(a) (K² + L²)^{-a/2}`,

which is his `(k² + ℓ²)^{-a/2} = k^{1-a} ∫ p(ds) sk/(ℓ² + s²k²)` (with `p` carrying the
normalisation `c(a)⁻¹`).  In the variable `w = s² - 1` the substitution is the dilation
`w ↦ (K² + L²) w / K²` of `integral_rpow_div_add_Ioi`. -/
lemma integral_cauchyMixing (ha₁ : 1 < a) (ha₂ : a < 2) {K L : ℝ} (hK : 0 < K) :
    ∫ x, x * K / (L ^ 2 + x ^ 2 * K ^ 2) ∂(cauchyMixing a)
      = K ^ (a - 1) * cauchyMixingConst a * (K ^ 2 + L ^ 2) ^ (-(a / 2)) := by
  have hmeas : Measurable fun w : ℝ ↦ Real.sqrt (1 + w) := by fun_prop
  have hS : 0 < K ^ 2 + L ^ 2 := by positivity
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  set κ := (K ^ 2 + L ^ 2) / K ^ 2 with hκ
  have hκpos : 0 < κ := by positivity
  have hw : cauchyMixingWeight a = (volume.restrict (Ioi (0 : ℝ))).withDensity
      fun w ↦ (((w ^ (-(a / 2)) * (1 + w) ^ (-(1 / 2 : ℝ))).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [cauchyMixing, integral_map hmeas.aemeasurable
    (by fun_prop : Measurable fun x : ℝ ↦ x * K / (L ^ 2 + x ^ 2 * K ^ 2)).aestronglyMeasurable, hw,
    integral_withDensity_eq_integral_smul measurable_cauchyMixingDensity.real_toNNReal]
  have hpt : EqOn
      (fun w : ℝ ↦ ((w ^ (-(a / 2)) * (1 + w) ^ (-(1 / 2 : ℝ))).toNNReal : ℝ≥0) •
        (Real.sqrt (1 + w) * K / (L ^ 2 + Real.sqrt (1 + w) ^ 2 * K ^ 2)))
      (fun w : ℝ ↦ (1 / K) * (w ^ (-(a / 2)) / (κ + w))) (Ioi 0) := by
    intro w hw
    have hw0 : 0 < w := hw
    have h1w : 0 < 1 + w := by linarith
    have hne : (1 + w) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos h1w _).ne'
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (by positivity), Real.sq_sqrt h1w.le, Real.sqrt_eq_rpow,
      Real.rpow_neg h1w.le, hκ]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_rpow_div_add_Ioi hκpos, hκ, Real.div_rpow hS.le hK2.le]
  have hK2a : (K ^ 2 : ℝ) ^ (-(a / 2)) = (K ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le, ← Real.rpow_neg hK.le]
    congr 1
    push_cast
    ring
  rw [hK2a, Real.rpow_sub_one hK.ne', cauchyMixingConst]
  have hKa : K ^ a ≠ 0 := (Real.rpow_pos_of_pos hK a).ne'
  field_simp

/-- **Georgii, Example (17.32), the case `1 < a < 2`.**  The function
`i ↦ (i_k² + i_c²)^{-a/2}` (`c ≠ k`) is nonnegative definite relative to `r_k`: it is the product
of the radial factor `c(a)⁻¹ i_k^{-(a-1)}` (`isNonnegDefiniteAt_rpow`) and the Cauchy mixture
`∫ p(dx) x i_k/(i_c² + x² i_k²)` (`isNonnegDefiniteAt_cauchyMixture`), by the substitution
`integral_cauchyMixing`. -/
theorem isNonnegDefiniteAt_sq_add_sq_rpow_of_lt {c : Fin d} (hck : c ≠ k) {a : ℝ}
    (ha₁ : 1 < a) (ha₂ : a < 2)
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k → J i = ((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2) ^ (-(a / 2))) :
    IsNonnegDefiniteAt k J := by
  have hC : 0 < cauchyMixingConst a :=
    integral_rpow_div_one_add_Ioi_pos (by linarith) (by linarith)
  have := isFiniteMeasure_cauchyMixing ha₁ ha₂
  have h1 : IsNonnegDefiniteAt k fun i : Fin d → ℤ ↦
      (1 / cauchyMixingConst a) * (i k : ℝ) ^ (-(a - 1)) :=
    isNonnegDefiniteAt_rpow (by linarith) (by positivity) fun _ _ ↦ rfl
  have h2 : IsNonnegDefiniteAt k fun i : Fin d → ℤ ↦
      ∫ x, x * (i k : ℝ) / ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2) ∂(cauchyMixing a) :=
    isNonnegDefiniteAt_cauchyMixture hck _ ae_one_le_cauchyMixing fun _ _ ↦ rfl
  refine (h1.mul h2).congr fun i hi ↦ ?_
  have hik : (0 : ℝ) < (i k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i k)
  rw [hJ i hi, integral_cauchyMixing ha₁ ha₂ hik, Real.rpow_neg hik.le]
  have hKa : (i k : ℝ) ^ (a - 1) ≠ 0 := (Real.rpow_pos_of_pos hik _).ne'
  field_simp

/-- **Georgii, Example (17.32), the case `a = 2`.**  `i ↦ (i_k² + i_c²)⁻¹` is the product of
`i_k⁻¹` and the single Cauchy kernel `i_k/(i_c² + i_k²)`. -/
theorem isNonnegDefiniteAt_sq_add_sq_inv {c : Fin d} (hck : c ≠ k)
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k → J i = ((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2)⁻¹) :
    IsNonnegDefiniteAt k J := by
  have h1 : IsNonnegDefiniteAt k fun i : Fin d → ℤ ↦ (1 : ℝ) * (i k : ℝ) ^ (-(1 : ℝ)) :=
    isNonnegDefiniteAt_rpow one_pos zero_le_one fun _ _ ↦ rfl
  have h2 : IsNonnegDefiniteAt k fun i : Fin d → ℤ ↦
      ∫ x, x * (i k : ℝ) / ((i c : ℝ) ^ 2 + x ^ 2 * (i k : ℝ) ^ 2) ∂(Measure.dirac (1 : ℝ)) :=
    isNonnegDefiniteAt_cauchyMixture hck _ (by simp) fun _ _ ↦ rfl
  refine (h1.mul h2).congr fun i hi ↦ ?_
  have hik : (0 : ℝ) < (i k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i k)
  rw [hJ i hi, integral_dirac, Real.rpow_neg_one]
  field_simp
  ring

/-- **Georgii, Example (17.32), the analytic core in any dimension.**  For `a > 1`, `β ≥ 0` and a
transverse direction `c ≠ k`, the function `i ↦ β (i_k² + i_c²)^{-a/2}` is nonnegative definite
relative to `r_k`.  For `1 < a < 2` this is the Cauchy-mixture representation
`isNonnegDefiniteAt_sq_add_sq_rpow_of_lt`; for `a = 2` it is `isNonnegDefiniteAt_sq_add_sq_inv`;
and for `a > 2` it follows from the case `1 < a/n < 2`, `n = ⌊a/2⌋ + 1`, by Comment (17.28)(2)
(`IsNonnegDefiniteAt.pow`), exactly as Georgii reduces to `1 < a < 2`.

Georgii's hypothesis is `a > d = 2`, which is what makes `J` absolutely summable (17.23); the
representation itself only needs `a > 1`. -/
theorem isNonnegDefiniteAt_sq_add_sq_rpow {c : Fin d} (hck : c ≠ k) {a : ℝ} (ha : 1 < a)
    {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ i : Fin d → ℤ, 1 ≤ i k →
      J i = β * ((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2) ^ (-(a / 2))) :
    IsNonnegDefiniteAt k J := by
  suffices h : IsNonnegDefiniteAt k fun i : Fin d → ℤ ↦
      ((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2) ^ (-(a / 2)) from
    (h.const_mul hβ).congr fun i hi ↦ (hJ i hi).symm
  rcases lt_trichotomy a 2 with h2 | h2 | h2
  · exact isNonnegDefiniteAt_sq_add_sq_rpow_of_lt hck ha h2 fun _ _ ↦ rfl
  · subst h2
    refine (isNonnegDefiniteAt_sq_add_sq_inv hck fun _ _ ↦ rfl).congr fun i _ ↦ ?_
    rw [show -(2 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  · set n := ⌊a / 2⌋₊ with hn
    have hn1 : a / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hn2 : (n : ℝ) ≤ a / 2 := Nat.floor_le (by linarith)
    have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set a' := a / ((n : ℝ) + 1) with ha'
    have ha'1 : 1 < a' := by rw [ha', lt_div_iff₀ hnpos]; linarith
    have ha'2 : a' < 2 := by rw [ha', div_lt_iff₀ hnpos]; linarith
    have h := (isNonnegDefiniteAt_sq_add_sq_rpow_of_lt hck ha'1 ha'2
      (J := fun i : Fin d → ℤ ↦ ((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2) ^ (-(a' / 2))) fun _ _ ↦ rfl).pow n
    refine h.congr fun i _ ↦ ?_
    rw [← Real.rpow_natCast (((i k : ℝ) ^ 2 + (i c : ℝ) ^ 2) ^ (-(a' / 2))) (n + 1),
      ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    rw [ha']
    field_simp

/-- **Georgii, Example (17.32) in dimension two.**  On `ℤ²`, the long range coupling
`J(i) = β |i|^{-a}` with `β ≥ 0` and `a > 1` is nonnegative definite relative to both reflections
`r_0` and `r_1`.  (Georgii assumes `a > d = 2`, the condition for absolute summability.) -/
theorem isNonnegDefiniteAt_longRange_two {J : (Fin 2 → ℤ) → ℝ} (k : Fin 2) {a : ℝ} (ha : 1 < a)
    {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ i : Fin 2 → ℤ, 1 ≤ i k → J i = β * (∑ c, (i c : ℝ) ^ 2) ^ (-(a / 2))) :
    IsNonnegDefiniteAt k J := by
  have hne : k + 1 ≠ k := by fin_cases k <;> decide
  have hall : ∀ x k : Fin 2, x = k ∨ x = k + 1 := by decide
  refine isNonnegDefiniteAt_sq_add_sq_rpow (c := k + 1) hne ha hβ fun i hi ↦ ?_
  rw [hJ i hi, Finset.sum_eq_add_of_mem k (k + 1) (Finset.mem_univ _) (Finset.mem_univ _)
    hne.symm fun x _ hx ↦ (hall x k).elim (fun h ↦ absurd h hx.1) fun h ↦ absurd h hx.2]

end LongRangeTwo

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

/-- **The diagonal of the crossing matrix of a nearest-neighbour coupling.**  On the torus, a
nearest-neighbour bond crosses the plane of `r_k` exactly at the two interfaces produced by the
periodic boundary condition: between the layers `i_k = N-1` and `i_k = N`, and between `i_k = 2N-1`
and `i_k = 0`.  A site of the positive half therefore sees a crossing bond iff `i_k ∈ {0, N-1}`,
and it then contributes `J(e_k)`.  (For `N = 1` the two conditions coincide and the site sees
both interfaces.) -/
theorem crossingMatrix_diag_nearestNeighbour (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (i : Fin d → ZMod (2 * N)) :
    crossingMatrix N J k i i
      = (if (i k).val = N - 1 then J (Pi.single k 1) else 0)
        + (if (i k).val = 0 then J (Pi.single k 1) else 0) := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hi : (i k).val < N
  swap
  · rw [crossingMatrix_eq_zero (fun h ↦ hi h.1)]
    have h1 : (i k).val ≠ N - 1 := by omega
    have h2 : (i k).val ≠ 0 := by omega
    simp [h1, h2]
  -- the crossing index along the diagonal
  set a : ℕ := (i k).val with ha
  have halt : a < N := hi
  have hidx : ∀ ℓ : Fin d → ℤ, ∀ c, c ≠ k →
      (crossingIndex N k i i + (2 * N : ℤ) • ℓ) c = (2 * N : ℤ) * ℓ c := by
    intro ℓ c hc
    simp [crossingIndex_of_ne hc]
  have hidxk : ∀ ℓ : Fin d → ℤ,
      (crossingIndex N k i i + (2 * N : ℤ) • ℓ) k
        = (2 * N : ℤ) - 1 - 2 * (a : ℤ) + (2 * N : ℤ) * ℓ k := by
    intro ℓ
    simp only [Pi.add_apply, Pi.smul_apply, crossingIndex_self, smul_eq_mul, ha]
    ring
  -- the natural-absolute-value sum, when the transverse coordinates vanish
  have hsum_of : ∀ (x : Fin d → ℤ), (∀ c, c ≠ k → x c = 0) →
      ∑ c, (x c).natAbs = (x k).natAbs := by
    intro x hx
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), Finset.sum_eq_zero, zero_add]
    intro c hc
    rw [hx c (Finset.ne_of_mem_erase hc)]
    rfl
  -- outside `{0, -e_k}` the summand vanishes
  have hzero : ∀ ℓ : Fin d → ℤ, ℓ ∉ ({0, -(Pi.single k 1)} : Finset (Fin d → ℤ)) →
      J (crossingIndex N k i i + (2 * N : ℤ) • ℓ) = 0 := by
    intro ℓ hℓ
    set x := crossingIndex N k i i + (2 * N : ℤ) • ℓ with hx
    refine hsupp _ fun hs ↦ hℓ ?_
    -- every transverse `ℓ c` vanishes
    have htr : ∀ c, c ≠ k → ℓ c = 0 := by
      intro c hc
      by_contra hne
      have h1 : (x c).natAbs ≤ ∑ c', (x c').natAbs :=
        Finset.single_le_sum (f := fun c' ↦ (x c').natAbs) (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ c)
      rw [hs] at h1
      rw [hx, hidx ℓ c hc] at h1
      have hmul : ((2 * N : ℤ) * ℓ c).natAbs = 2 * N * (ℓ c).natAbs := by
        rw [Int.natAbs_mul]
        congr 1
      rw [hmul] at h1
      have hne1 : 1 ≤ (ℓ c).natAbs :=
        Nat.one_le_iff_ne_zero.2 fun h ↦ hne (Int.natAbs_eq_zero.1 h)
      have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      have hle : 2 * N ≤ 2 * N * (ℓ c).natAbs := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have hxc : ∀ c, c ≠ k → x c = 0 := by
      intro c hc; rw [hx, hidx ℓ c hc, htr c hc, mul_zero]
    have hxk : (x k).natAbs = 1 := by rw [← hsum_of x hxc, hs]
    have hval : x k = 1 ∨ x k = -1 := by omega
    have hxkv : x k = (2 * N : ℤ) - 1 - 2 * (a : ℤ) + (2 * N : ℤ) * ℓ k := hidxk ℓ
    have haZ : (a : ℤ) < (N : ℤ) := by exact_mod_cast halt
    have haZ0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg _
    have hNZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
    have hlk : ℓ k = 0 ∨ ℓ k = -1 := by
      rcases hval with h | h
      · left; rw [hxkv] at h; nlinarith [h]
      · right; rw [hxkv] at h; nlinarith [h]
    -- so `ℓ` is `0` or `-e_k`
    have hfin : ℓ = 0 ∨ ℓ = -(Pi.single k 1) := by
      rcases hlk with h | h
      · left
        funext c
        by_cases hc : c = k
        · subst hc; simpa using h
        · simpa using htr c hc
      · right
        funext c
        by_cases hc : c = k
        · subst hc; simp [h]
        · simp [hc, htr c hc]
    rcases hfin with h | h <;> simp [h]
  rw [crossingMatrix_eq_tsum hi hi, tsum_eq_sum hzero,
    Finset.sum_pair (show (0 : Fin d → ℤ) ≠ -(Pi.single k 1) by
      intro h
      have := congrFun h k
      simp at this)]
  have haZ : (a : ℤ) < (N : ℤ) := by exact_mod_cast halt
  have haZ0 : (0 : ℤ) ≤ (a : ℤ) := Int.natCast_nonneg _
  have hNZ : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  congr 1
  · -- the term `ℓ = 0`: the interface between the layers `N-1` and `N`
    set x := crossingIndex N k i i + (2 * N : ℤ) • (0 : Fin d → ℤ) with hx
    have hxc : ∀ c, c ≠ k → x c = 0 := by intro c hc; rw [hx, hidx _ c hc]; simp
    have hxk : x k = (2 * N : ℤ) - 1 - 2 * (a : ℤ) := by rw [hx, hidxk]; simp
    split_ifs with hcase
    · have haN : (a : ℤ) = (N : ℤ) - 1 := by omega
      have hxe : x = Pi.single k 1 := by
        funext c
        by_cases hc : c = k
        · subst hc
          rw [hxk, haN, Pi.single_eq_same]
          ring
        · rw [hxc c hc, Pi.single_eq_of_ne hc]
      rw [hxe]
    · refine hsupp _ ?_
      rw [hsum_of x hxc, hxk]
      have h1 : (a : ℤ) < (N : ℤ) - 1 := by omega
      omega
  · -- the term `ℓ = -e_k`: the interface produced by the periodic boundary condition
    set x := crossingIndex N k i i + (2 * N : ℤ) • (-(Pi.single k 1) : Fin d → ℤ) with hx
    have hxc : ∀ c, c ≠ k → x c = 0 := by
      intro c hc; rw [hx, hidx _ c hc]; simp [hc]
    have hxk : x k = -1 - 2 * (a : ℤ) := by
      rw [hx, hidxk]
      simp only [Pi.neg_apply, Pi.single_eq_same]
      ring
    split_ifs with hcase
    · have haN : (a : ℤ) = 0 := by omega
      have hxe : x = -(Pi.single k 1) := by
        funext c
        by_cases hc : c = k
        · subst hc
          rw [hxk, haN, Pi.neg_apply, Pi.single_eq_same]
          ring
        · rw [hxc c hc, Pi.neg_apply, Pi.single_eq_of_ne hc]
          ring
      rw [hxe, heven]
    · refine hsupp _ ?_
      rw [hsum_of x hxc, hxk]
      have h1 : (1 : ℤ) ≤ (a : ℤ) := by omega
      omega

/-- **The crossing matrix of a ferromagnetic nearest-neighbour coupling is positive
semidefinite**, being diagonal with nonnegative entries.

Only the nonnegativity of the single coupling `J(e_k)` in the direction of the reflection is
needed, not `J ≥ 0`: by `crossingMatrix_diag_nearestNeighbour` the diagonal entries are
`J(e_k)` times the number of interfaces the site sees. -/
theorem posSemidef_crossingMatrix_nearestNeighbour (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (hJk : 0 ≤ J (Pi.single k 1)) :
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
  refine Matrix.PosSemidef.diagonal fun i ↦ ?_
  rw [crossingMatrix_diag_nearestNeighbour heven hsupp i]
  positivity

/-- **Georgii, Example (17.30).**  For a ferromagnetic nearest-neighbour Heisenberg potential —
`J` even, supported on the bonds `|i| = 1` and nonnegative — the Gibbs distribution in the torus
with periodic boundary condition is `r_k`-positive, for every direction `k`. -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour
    (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (hJk : 0 ≤ J (Pi.single k 1))
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) :=
  isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef heven
    (flipCoord_eq_of_nearestNeighbour hsupp heven)
    (posSemidef_crossingMatrix_nearestNeighbour heven hsupp hJk) ν hint

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

/-- **Georgii, Example (17.32), the case `d = 1`.**  For the long-range coupling
`J(i) = β |i|^{-a}` on `ℤ` with `β ≥ 0` and `a > 1` — `a > d` being Georgii's summability
(17.23) — the Gibbs distribution in the torus with periodic boundary condition is `r_0`-positive.

The representing measure is the one of `isNonnegDefiniteAt_rpow`: the image of the gamma
distribution `Γ(a)^{-1} e^{-s} s^{a-1} ds` under `s ↦ e^{-s}`, which is Georgii's case 1). -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_longRange_one {J : (Fin 1 → ℤ) → ℝ}
    (k : Fin 1) {a : ℝ} (ha : 1 < a) {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ i : Fin 1 → ℤ, i ≠ 0 → J i = β * |(i 0 : ℝ)| ^ (-a))
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin 1 → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) := by
  have hk : k = 0 := Subsingleton.elim k 0
  subst hk
  -- (17.23): the comparison series on `ℤ`, transported along `(Fin 1 → ℤ) ≃ ℤ`.
  have hcomp : Summable fun i : Fin 1 → ℤ ↦ β * |(i 0 : ℝ)| ^ (-a) := by
    have hiff := Equiv.summable_iff (f := fun z : ℤ ↦ β * |(z : ℝ)| ^ (-a))
      (Equiv.funUnique (Fin 1) ℤ)
    exact hiff.2 ((Real.summable_abs_int_rpow ha).mul_left β)
  have hsum : Summable J := by
    refine Summable.of_norm_bounded_eventually hcomp ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : Fin 1 → ℤ)).subset fun i hi ↦ ?_
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi ⊢
    by_contra hi0
    exact hi (by rw [hJ i hi0, Real.norm_eq_abs, abs_of_nonneg (by positivity)])
  have heven : ∀ m, J (-m) = J m := by
    intro m
    by_cases hm : m = 0
    · rw [hm, neg_zero]
    · rw [hJ (-m) (neg_ne_zero.2 hm), hJ m hm]
      simp
  refine isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt hsum heven
    (isNonnegDefiniteAt_rpow (a := a) (by linarith) hβ fun i hi ↦ ?_) ν hint
  have hne : i ≠ 0 := fun h ↦ by simp [h] at hi
  have hipos : (0 : ℝ) < ((i 0 : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < i 0)
  rw [hJ i hne, abs_of_pos hipos]

/-- **Georgii, Example (17.32) for `d = 2`.**  For the long range Heisenberg potential on `ℤ²`
with coupling `J(i) = β |i|^{-a}`, `β ≥ 0`, `a > 2`, the Gibbs distribution in the torus with
periodic boundary condition is `r_k`-positive for both `k`.  The absolute summability (17.23) is
`summable_sum_sq_rpow_fin_two`; the hypothesis `hint` is Georgii's standing assumption that
`°Z_Λ^Φ` is finite. -/
theorem isReflectionPositive_heisenbergPeriodicGibbs_longRange_two {J : (Fin 2 → ℤ) → ℝ}
    (k : Fin 2) {a : ℝ} (ha : 2 < a) {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ i : Fin 2 → ℤ, i ≠ 0 → J i = β * (∑ c, (i c : ℝ) ^ 2) ^ (-(a / 2)))
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin 2 → ZMod (2 * N) ↦ ν)) :
    IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin n → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N n J ν) := by
  have hsum : Summable J := by
    refine Summable.of_norm_bounded_eventually
      (g := fun i : Fin 2 → ℤ ↦ β * (∑ c, (i c : ℝ) ^ 2) ^ (-(a / 2)))
      ((summable_sum_sq_rpow_fin_two ha).mul_left β) ?_
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton (0 : Fin 2 → ℤ)).subset fun i hi ↦ ?_
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi ⊢
    by_contra hi0
    apply hi
    rw [hJ i hi0, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have heven : ∀ m, J (-m) = J m := by
    intro m
    by_cases hm : m = 0
    · rw [hm, neg_zero]
    · rw [hJ (-m) (neg_ne_zero.2 hm), hJ m hm]
      simp
  refine isReflectionPositive_heisenbergPeriodicGibbs_of_isNonnegDefiniteAt hsum heven
    (isNonnegDefiniteAt_longRange_two k (by linarith) hβ fun i hi ↦ hJ i ?_) ν hint
  rintro rfl
  simp at hi

/-! ### Georgii, Examples (17.30) and (17.31): the necessity halves

Georgii shows that the conditions of Examples (17.30) and (17.31) are not merely sufficient for
`r_k`-positivity but necessary, by evaluating `°Z_Λ^Φ °γ_Λ^Φ(f f^*)` at an explicit `f` for the
two-point a priori measure `λ = δ_1 + δ_{-1}` (so `n = 1` and the spins are `±1`).

The mechanism is `integral_patternTest_mul_comp_heisenbergPeriodicGibbs`: for a `±1` pattern `q`
on `Λ_{+,k}`, the test function that selects the two configurations following `± q` on `Λ_{+,k}`
has reflection form `4 e^{S} sinh⟨q, M q⟩`, where `M` is the crossing matrix.  So *any* `±1`
vector on which the quadratic form of `M` is negative refutes `r_k`-positivity — a converse to
`isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef`.
-/


/-- **Georgii's a priori measure in the necessity halves of Examples (17.30) and (17.31).**
The two-point measure `λ = δ_1 + δ_{-1}` on the one-dimensional spin space `ℝ^1`. -/
def twoPointMeasure : Measure (Fin 1 → ℝ) :=
  Measure.dirac (fun _ ↦ 1) + Measure.dirac (fun _ ↦ -1)

instance : IsFiniteMeasure (twoPointMeasure) := by
  constructor
  simp [twoPointMeasure]

/-- A one-dimensional spin is determined by its single coordinate. -/
lemma fin_one_ext_iff (u v : Fin 1 → ℝ) : u = v ↔ u 0 = v 0 :=
  ⟨fun h ↦ by rw [h], fun h ↦ funext fun c ↦ by rw [Subsingleton.elim c 0, h]⟩

lemma twoPointMeasure_singleton {v : Fin 1 → ℝ} (hv : v 0 = 1 ∨ v 0 = -1) :
    twoPointMeasure {v} = 1 := by
  have h1 : ((fun _ ↦ 1 : Fin 1 → ℝ) ∈ ({v} : Set (Fin 1 → ℝ))) ↔ v 0 = 1 := by
    rw [Set.mem_singleton_iff, fin_one_ext_iff, eq_comm]
  have h2 : ((fun _ ↦ -1 : Fin 1 → ℝ) ∈ ({v} : Set (Fin 1 → ℝ))) ↔ v 0 = -1 := by
    rw [Set.mem_singleton_iff, fin_one_ext_iff, eq_comm]
  rw [twoPointMeasure, Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply]
  rcases hv with hv | hv
  · rw [Set.indicator_of_mem (h1.2 hv), Set.indicator_of_notMem (fun h ↦ by
      have := h2.1 h; rw [hv] at this; norm_num at this)]
    simp
  · rw [Set.indicator_of_notMem (fun h ↦ by
      have := h1.1 h; rw [hv] at this; norm_num at this), Set.indicator_of_mem (h2.2 hv)]
    simp

lemma pi_twoPointMeasure_singleton {ι : Type*} [Fintype ι] (ω : ι → (Fin 1 → ℝ))
    (hω : ∀ i, ω i 0 = 1 ∨ ω i 0 = -1) :
    (Measure.pi fun _ : ι ↦ twoPointMeasure) {ω} = 1 := by
  have hsing : ({ω} : Set (ι → (Fin 1 → ℝ))) = Set.univ.pi fun i ↦ {ω i} := by
    ext x
    simp [Set.mem_pi, funext_iff, eq_comm, Set.mem_singleton_iff]
  rw [hsing, Measure.pi_pi]
  simp [twoPointMeasure_singleton (hω _)]

variable (N k) in
/-- The configurations of the torus whose spins follow the pattern `q` on the positive half
`Λ_{+,k}`.  Georgii's event `{σ_i = σ_u for all i ∈ Λ_{+,k}}` of Example (17.30) is the case
of a constant `q`. -/
def patternSet (q : (Fin d → ZMod (2 * N)) → ℝ) :
    Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) :=
  {ω | ∀ i, (i k).val < N → ω i 0 = q i}

variable (N k) in
/-- The configuration of the torus which follows the pattern `q` with overall sign `x` on the
positive half `Λ_{+,k}` and the *mirror* pattern with overall sign `y` on the negative half. -/
def patternConfig (q : (Fin d → ZMod (2 * N)) → ℝ) (x y : ℝ) :
    (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ) :=
  fun i _ ↦ if (i k).val < N then x * q i else y * q (torusReflAt N k i)

variable (N k) in
/-- **Georgii's test function `f` in the necessity halves of Examples (17.30) and (17.31)**, up to
a positive constant: the difference of the indicators of the two configurations of `Λ_{+,k}` which
follow the pattern `q` and `-q`.

Georgii writes `f = e^{-h} σ_u 1_{σ_i = σ_u for all i ∈ Λ_{+,k}}`.  On the two-point
configurations that carry `λ^Λ` for `λ = δ_1 + δ_{-1}`, the factor `σ_u ∈ {1, -1}` distinguishes
the two constant configurations — which is what the difference of indicators does — and `e^{-h}`
is a positive constant, since `h` is a quadratic form evaluated at spins of modulus one.  Dropping
it keeps `f` *bounded*, as Georgii's `𝒜_{+,k}` requires; `e^{-h}` is unbounded on the ambient
space `(ℝ^1)^Λ`. -/
def patternTest (q : (Fin d → ZMod (2 * N)) → ℝ) :
    ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) → ℝ :=
  fun ω ↦ (patternSet N k q).indicator (fun _ ↦ (1 : ℝ)) ω
    - (patternSet N k (-q)).indicator (fun _ ↦ (1 : ℝ)) ω

lemma torusReflAt_val_lt_of_not_lt {i : Fin d → ZMod (2 * N)} (hi : ¬ ((i k).val < N)) :
    ((torusReflAt N k i) k).val < N := by
  have h := torusPosAt_iff_torusReflAt_notMem (N := N) k (torusReflAt N k i)
  rw [torusReflAt_torusReflAt] at h
  simpa only [mem_torusPosAt, not_lt, not_le] using h.2 (by simpa using hi)

lemma not_torusReflAt_val_lt {i : Fin d → ZMod (2 * N)} (hi : (i k).val < N) :
    ¬ (((torusReflAt N k i) k).val < N) := by
  have h := torusPosAt_iff_torusReflAt_notMem (N := N) k i
  simpa only [mem_torusPosAt] using h.1 hi

omit [NeZero N] in
lemma patternConfig_of_lt {q : (Fin d → ZMod (2 * N)) → ℝ} {x y : ℝ}
    {i : Fin d → ZMod (2 * N)} (hi : (i k).val < N) :
    patternConfig N k q x y i 0 = x * q i := by
  simp only [patternConfig]
  split_ifs
  rfl

omit [NeZero N] in
lemma patternConfig_of_not_lt {q : (Fin d → ZMod (2 * N)) → ℝ} {x y : ℝ}
    {i : Fin d → ZMod (2 * N)} (hi : ¬ ((i k).val < N)) :
    patternConfig N k q x y i 0 = y * q (torusReflAt N k i) := by
  simp only [patternConfig]
  split_ifs
  rfl

lemma patternConfig_torusReflAt {q : (Fin d → ZMod (2 * N)) → ℝ} {x y : ℝ}
    {i : Fin d → ZMod (2 * N)} (hi : (i k).val < N) :
    patternConfig N k q x y (torusReflAt N k i) 0 = y * q i := by
  rw [patternConfig_of_not_lt (not_torusReflAt_val_lt hi), torusReflAt_torusReflAt]

/-- **The two halves of the pattern determine the configuration.**  A configuration which follows
the pattern `x q` on `Λ_{+,k}` and whose reflection follows `y q` on `Λ_{+,k}` is exactly
`patternConfig q x y`; this is the point of Georgii's choice of `f`, and it is what turns the
reflection form into a sum of four terms. -/
lemma mem_patternSet_and_comp_iff (q : (Fin d → ZMod (2 * N)) → ℝ) (x y : ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) :
    (ω ∈ patternSet N k (x • q) ∧ (ω ∘ torusReflAt N k) ∈ patternSet N k (y • q))
      ↔ ω = patternConfig N k q x y := by
  constructor
  · rintro ⟨h1, h2⟩
    funext i
    rw [fin_one_ext_iff]
    by_cases hi : (i k).val < N
    · rw [h1 i hi, patternConfig_of_lt hi]
      rfl
    · have hri := torusReflAt_val_lt_of_not_lt (k := k) hi
      have := h2 (torusReflAt N k i) hri
      simp only [Function.comp_apply, torusReflAt_torusReflAt, Pi.smul_apply, smul_eq_mul] at this
      rw [this, patternConfig_of_not_lt hi]
  · rintro rfl
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [patternConfig_of_lt hi]; rfl
    · simp only [Function.comp_apply]
      rw [patternConfig_torusReflAt hi]
      rfl

lemma indicator_mul_indicator_comp (q : (Fin d → ZMod (2 * N)) → ℝ) (x y : ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) :
    (patternSet N k (x • q)).indicator (fun _ ↦ (1 : ℝ)) ω
        * (patternSet N k (y • q)).indicator (fun _ ↦ (1 : ℝ)) (ω ∘ torusReflAt N k)
      = ({patternConfig N k q x y} :
          Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω := by
  classical
  have hmem : ω ∈ ({patternConfig N k q x y} :
        Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))) ↔
      (ω ∈ patternSet N k (x • q) ∧ (ω ∘ torusReflAt N k) ∈ patternSet N k (y • q)) := by
    rw [Set.mem_singleton_iff]
    exact (mem_patternSet_and_comp_iff (N := N) (k := k) q x y ω).symm
  by_cases h1 : ω ∈ patternSet N k (x • q)
  · by_cases h2 : (ω ∘ torusReflAt N k) ∈ patternSet N k (y • q)
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2,
        Set.indicator_of_mem (hmem.2 ⟨h1, h2⟩)]
      norm_num
    · rw [Set.indicator_of_notMem h2, mul_zero,
        Set.indicator_of_notMem (fun h ↦ h2 (hmem.1 h).2)]
  · rw [Set.indicator_of_notMem h1, zero_mul,
      Set.indicator_of_notMem (fun h ↦ h1 (hmem.1 h).1)]

lemma dotProduct_fin_one (u v : Fin 1 → ℝ) : u ⬝ᵥ v = u 0 * v 0 := by
  simp [dotProduct]

lemma heisenbergHalf_patternConfig (q : (Fin d → ZMod (2 * N)) → ℝ) {x y : ℝ}
    (hx : x * x = 1) :
    heisenbergHalf N 1 J k (patternConfig N k q x y)
      = (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
          periodizedCoupling N J (i - j) * q i * q j) / 2 := by
  rw [heisenbergHalf]
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_)
  rw [mem_torusPosAtFinset] at hi hj
  rw [dotProduct_fin_one, patternConfig_of_lt hi, patternConfig_of_lt hj]
  calc periodizedCoupling N J (i - j) * (x * q i * (x * q j))
      = periodizedCoupling N J (i - j) * q i * q j * (x * x) := by ring
    _ = periodizedCoupling N J (i - j) * q i * q j := by rw [hx, mul_one]

lemma heisenbergHalf_patternConfig_comp (q : (Fin d → ZMod (2 * N)) → ℝ) {x y : ℝ}
    (hy : y * y = 1) :
    heisenbergHalf N 1 J k (patternConfig N k q x y ∘ torusReflAt N k)
      = (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
          periodizedCoupling N J (i - j) * q i * q j) / 2 := by
  rw [heisenbergHalf]
  refine congrArg (· / 2) (Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_)
  rw [mem_torusPosAtFinset] at hi hj
  simp only [Function.comp_apply]
  rw [dotProduct_fin_one, patternConfig_torusReflAt hi, patternConfig_torusReflAt hj]
  calc periodizedCoupling N J (i - j) * (y * q i * (y * q j))
      = periodizedCoupling N J (i - j) * q i * q j * (y * y) := by ring
    _ = periodizedCoupling N J (i - j) * q i * q j := by rw [hy, mul_one]

lemma crossing_patternConfig (q : (Fin d → ZMod (2 * N)) → ℝ) (x y : ℝ) :
    ∑ i, ∑ j, crossingMatrix N J k i j *
        (patternConfig N k q x y (torusReflAt N k i) ⬝ᵥ patternConfig N k q x y j)
      = x * y * (q ⬝ᵥ crossingMatrix N J k *ᵥ q) := by
  rw [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hij : (i k).val < N ∧ (j k).val < N
  · rw [dotProduct_fin_one, patternConfig_torusReflAt hij.1, patternConfig_of_lt hij.2]
    ring
  · rw [crossingMatrix_eq_zero hij]; ring

/-- **The exponent (17.24) at a two-valued pattern configuration.**  On the configuration which
follows the pattern `q` with sign `x` on `Λ_{+,k}` and its mirror image with sign `y` on
`Λ_{-,k}`, the exponent `h + h∘r_k + H` of Georgii's decomposition is the *constant*
`∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) q_i q_j` plus `x y` times the crossing form of `q`.  The two halves
contribute the same amount because `x² = y² = 1`; only the crossing term remembers the relative
sign of the two halves, and that is what makes the reflection form a hyperbolic sine. -/
lemma heisenbergExponent_patternConfig (heven : ∀ m, J (-m) = J m)
    (hflip : ∀ m, J (flipCoord k m) = J m) (q : (Fin d → ZMod (2 * N)) → ℝ) {x y : ℝ}
    (hx : x * x = 1) (hy : y * y = 1) :
    heisenbergExponent N 1 J (patternConfig N k q x y)
      = (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
            periodizedCoupling N J (i - j) * q i * q j)
        + x * y * (q ⬝ᵥ crossingMatrix N J k *ᵥ q) := by
  rw [heisenbergExponent_eq_add heven hflip, heisenbergHalf_patternConfig q hx,
    heisenbergHalf_patternConfig_comp q hy, crossing_patternConfig]
  ring

omit [NeZero N] in
lemma patternConfig_eq_one_or {q : (Fin d → ZMod (2 * N)) → ℝ}
    (hq : ∀ i, q i = 1 ∨ q i = -1) {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (i : Fin d → ZMod (2 * N)) :
    patternConfig N k q x y i 0 = 1 ∨ patternConfig N k q x y i 0 = -1 := by
  by_cases hi : (i k).val < N
  · rw [patternConfig_of_lt hi]
    rcases hx with hx | hx <;> rcases hq i with h | h <;> rw [hx, h] <;> norm_num
  · rw [patternConfig_of_not_lt hi]
    rcases hy with hy | hy <;> rcases hq (torusReflAt N k i) with h | h <;> rw [hy, h] <;> norm_num

/-- **The product `f f*` for Georgii's test function is a sum of four point masses.**  The event
that `ω` follows the pattern `± q` on `Λ_{+,k}` *and* that its reflection does too pins `ω` down
completely; so `f · f∘r_k` is supported on the four configurations `patternConfig q (±1) (±1)`,
with the sign of the product of the two overall signs. -/
lemma patternTest_mul_comp (q : (Fin d → ZMod (2 * N)) → ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) :
    patternTest N k q ω * patternTest N k q (ω ∘ torusReflAt N k)
      = ({patternConfig N k q 1 1} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω
        - ({patternConfig N k q 1 (-1)} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω
        - ({patternConfig N k q (-1) 1} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω
        + ({patternConfig N k q (-1) (-1)} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω := by
  have e11 := indicator_mul_indicator_comp (N := N) (k := k) q 1 1 ω
  have e1m := indicator_mul_indicator_comp (N := N) (k := k) q 1 (-1) ω
  have em1 := indicator_mul_indicator_comp (N := N) (k := k) q (-1) 1 ω
  have emm := indicator_mul_indicator_comp (N := N) (k := k) q (-1) (-1) ω
  simp only [one_smul, neg_one_smul] at e11 e1m em1 emm
  simp only [patternTest]
  rw [sub_mul, mul_sub, mul_sub, e11, e1m, em1, emm]
  ring

/-- **The reflection form of Georgii's test function, pointwise.**  Multiplying the four point
masses of `patternTest_mul_comp` by the density `exp[(17.24)]` evaluates the exponent at each of
the four configurations, where it is the constant `S = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) q_i q_j` plus
`± ⟨q, M q⟩`. -/
lemma exp_mul_patternTest_mul_comp (heven : ∀ m, J (-m) = J m)
    (hflip : ∀ m, J (flipCoord k m) = J m) (q : (Fin d → ZMod (2 * N)) → ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) :
    Real.exp (heisenbergExponent N 1 J ω)
        * (patternTest N k q ω * patternTest N k q (ω ∘ torusReflAt N k))
      = ({patternConfig N k q 1 1} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator
            (fun _ ↦ Real.exp ((∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j) * q i * q j)
                + q ⬝ᵥ crossingMatrix N J k *ᵥ q)) ω
        - ({patternConfig N k q 1 (-1)} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator
            (fun _ ↦ Real.exp ((∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j) * q i * q j)
                - q ⬝ᵥ crossingMatrix N J k *ᵥ q)) ω
        - ({patternConfig N k q (-1) 1} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator
            (fun _ ↦ Real.exp ((∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j) * q i * q j)
                - q ⬝ᵥ crossingMatrix N J k *ᵥ q)) ω
        + ({patternConfig N k q (-1) (-1)} :
            Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator
            (fun _ ↦ Real.exp ((∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j) * q i * q j)
                + q ⬝ᵥ crossingMatrix N J k *ᵥ q)) ω := by
  have key : ∀ a : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ),
      Real.exp (heisenbergExponent N 1 J ω)
          * ({a} : Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator (fun _ ↦ (1 : ℝ)) ω
        = ({a} : Set ((Fin d → ZMod (2 * N)) → (Fin 1 → ℝ))).indicator
            (fun _ ↦ Real.exp (heisenbergExponent N 1 J a)) ω := by
    intro a
    by_cases h : ω = a
    · subst h; simp
    · rw [Set.indicator_of_notMem (by simpa using h),
        Set.indicator_of_notMem (by simpa using h), mul_zero]
  rw [patternTest_mul_comp, mul_add, mul_sub, mul_sub, key, key, key, key,
    heisenbergExponent_patternConfig heven hflip q (by norm_num) (by norm_num),
    heisenbergExponent_patternConfig heven hflip q (by norm_num) (by norm_num),
    heisenbergExponent_patternConfig heven hflip q (by norm_num) (by norm_num),
    heisenbergExponent_patternConfig heven hflip q (by norm_num) (by norm_num)]
  norm_num [sub_eq_add_neg]

/-- The integral of a point mass at a two-valued configuration against `λ^Λ` is its value:
`λ^Λ` gives mass one to every configuration with values in `{1, -1}`. -/
lemma integral_indicator_singleton_twoPoint {ι : Type*} [Fintype ι] (a : ι → (Fin 1 → ℝ))
    (ha : ∀ i, a i 0 = 1 ∨ a i 0 = -1) (c : ℝ) :
    ∫ ω, ({a} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c) ω
        ∂(Measure.pi fun _ : ι ↦ twoPointMeasure) = c := by
  rw [integral_indicator_const c (measurableSet_singleton a), measureReal_def,
    pi_twoPointMeasure_singleton a ha]
  simp

lemma integrable_indicator_singleton_twoPoint {ι : Type*} [Fintype ι] (a : ι → (Fin 1 → ℝ))
    (c : ℝ) :
    Integrable (fun ω ↦ ({a} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c) ω)
      (Measure.pi fun _ : ι ↦ twoPointMeasure) :=
  (integrable_const c).indicator (measurableSet_singleton a)

/-- The alternating sum of four point masses at two-valued configurations integrates to the
alternating sum of their weights. -/
lemma integral_indicator_singleton_twoPoint_four {ι : Type*} [Fintype ι]
    (a₁ a₂ a₃ a₄ : ι → (Fin 1 → ℝ)) (c₁ c₂ c₃ c₄ : ℝ)
    (h₁ : ∀ i, a₁ i 0 = 1 ∨ a₁ i 0 = -1) (h₂ : ∀ i, a₂ i 0 = 1 ∨ a₂ i 0 = -1)
    (h₃ : ∀ i, a₃ i 0 = 1 ∨ a₃ i 0 = -1) (h₄ : ∀ i, a₄ i 0 = 1 ∨ a₄ i 0 = -1) :
    ∫ ω, (({a₁} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₁) ω
          - ({a₂} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₂) ω
          - ({a₃} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₃) ω
          + ({a₄} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₄) ω)
        ∂(Measure.pi fun _ : ι ↦ twoPointMeasure)
      = c₁ - c₂ - c₃ + c₄ := by
  rw [integral_add
      (f := fun ω ↦ ({a₁} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₁) ω
        - ({a₂} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₂) ω
        - ({a₃} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₃) ω)
      (g := fun ω ↦ ({a₄} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₄) ω)
      (((integrable_indicator_singleton_twoPoint a₁ c₁).sub
        (integrable_indicator_singleton_twoPoint a₂ c₂)).sub
        (integrable_indicator_singleton_twoPoint a₃ c₃))
      (integrable_indicator_singleton_twoPoint a₄ c₄),
    integral_sub
      (f := fun ω ↦ ({a₁} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₁) ω
        - ({a₂} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₂) ω)
      (g := fun ω ↦ ({a₃} : Set (ι → (Fin 1 → ℝ))).indicator (fun _ ↦ c₃) ω)
      ((integrable_indicator_singleton_twoPoint a₁ c₁).sub
        (integrable_indicator_singleton_twoPoint a₂ c₂))
      (integrable_indicator_singleton_twoPoint a₃ c₃),
    integral_sub (integrable_indicator_singleton_twoPoint a₁ c₁)
      (integrable_indicator_singleton_twoPoint a₂ c₂),
    integral_indicator_singleton_twoPoint a₁ h₁, integral_indicator_singleton_twoPoint a₂ h₂,
    integral_indicator_singleton_twoPoint a₃ h₃, integral_indicator_singleton_twoPoint a₄ h₄]

/-- **Georgii's computation in the necessity halves of Examples (17.30) and (17.31).**  For the
two-point a priori measure `λ = δ_1 + δ_{-1}` and Georgii's test function `f` attached to a `±1`
pattern `q` on `Λ_{+,k}`,

`°Z_Λ^Φ °γ_Λ^Φ(f f^*) = 4 e^{S} sinh⟨q, M q⟩`,

where `S = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) q_i q_j` and `M` is the crossing matrix.  Georgii's `e^{-h}`
factor is exactly `e^{-S/2}` on the four configurations that survive, so his statement is the
present one with the factor `e^{S}` cancelled; since `e^{S} > 0` the sign is the same either way.

Georgii states the value as `4 sinh[(2N)^{d-1} J(u)]` in Example (17.30).  Two corrections: the
middle expression `∑_{x,y = ±1} exp[(2N)^{d-1}J(u) x y]` is `4 cosh`, not `4 sinh` — the factor
`σ_u σ_{r_k u} = x y` coming from `f f^*` is missing from it — and the constant is `2(2N)^{d-1}`,
not `(2N)^{d-1}`: see `sum_crossingMatrix_nearestNeighbour`. -/
theorem integral_patternTest_mul_comp_heisenbergPeriodicGibbs
    (heven : ∀ m, J (-m) = J m) (hflip : ∀ m, J (flipCoord k m) = J m)
    (q : (Fin d → ZMod (2 * N)) → ℝ) (hq : ∀ i, q i = 1 ∨ q i = -1) :
    ∫ ω, patternTest N k q ω * patternTest N k q (ω ∘ torusReflAt N k)
        ∂(heisenbergPeriodicGibbs N 1 J twoPointMeasure)
      = 4 * Real.exp (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
            periodizedCoupling N J (i - j) * q i * q j)
        * Real.sinh (q ⬝ᵥ crossingMatrix N J k *ᵥ q) := by
  classical
  have hdens : (fun ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ) ↦
        ENNReal.ofReal (Real.exp (heisenbergExponent N 1 J ω)))
      = fun ω ↦ ((Real.toNNReal (Real.exp (heisenbergExponent N 1 J ω)) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [heisenbergPeriodicGibbs, hdens,
    integral_withDensity_eq_integral_smul measurable_heisenbergExponent.exp.real_toNNReal]
  have hpt : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ),
      Real.toNNReal (Real.exp (heisenbergExponent N 1 J ω)) •
          (patternTest N k q ω * patternTest N k q (ω ∘ torusReflAt N k))
        = Real.exp (heisenbergExponent N 1 J ω) *
          (patternTest N k q ω * patternTest N k q (ω ∘ torusReflAt N k)) := by
    intro ω
    rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), smul_eq_mul]
  simp only [hpt, exp_mul_patternTest_mul_comp heven hflip q]
  rw [integral_indicator_singleton_twoPoint_four _ _ _ _ _ _ _ _
    (patternConfig_eq_one_or hq (Or.inl rfl) (Or.inl rfl))
    (patternConfig_eq_one_or hq (Or.inl rfl) (Or.inr rfl))
    (patternConfig_eq_one_or hq (Or.inr rfl) (Or.inl rfl))
    (patternConfig_eq_one_or hq (Or.inr rfl) (Or.inr rfl))]
  have hc : Real.exp (q ⬝ᵥ crossingMatrix N J k *ᵥ q) ≠ 0 := Real.exp_ne_zero _
  rw [Real.sinh_eq, Real.exp_add, Real.exp_sub, Real.exp_neg]
  field_simp
  ring

lemma measurableSet_patternSet (q : (Fin d → ZMod (2 * N)) → ℝ) :
    MeasurableSet (patternSet N k q) := by
  have hrw : patternSet N k q
      = ⋂ i ∈ {i : Fin d → ZMod (2 * N) | (i k).val < N},
          {ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ) | ω i 0 = q i} := by
    ext ω; simp [patternSet]
  rw [hrw]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ ↦
    (measurable_torusSpinApply (n := 1) i 0) (measurableSet_singleton (q i))

lemma measurable_patternTest (q : (Fin d → ZMod (2 * N)) → ℝ) :
    Measurable (patternTest N k q) :=
  (measurable_const.indicator (measurableSet_patternSet q)).sub
    (measurable_const.indicator (measurableSet_patternSet (-q)))

omit [NeZero N] in
lemma dependsOn_patternTest (q : (Fin d → ZMod (2 * N)) → ℝ) :
    DependsOn (patternTest N k q) (torusPosAt N k) := by
  intro ω ω' h
  have hmem : ∀ p : (Fin d → ZMod (2 * N)) → ℝ, ω ∈ patternSet N k p ↔ ω' ∈ patternSet N k p := by
    intro p
    constructor
    · exact fun hω i hi ↦ by rw [← h i (mem_torusPosAt.2 hi)]; exact hω i hi
    · exact fun hω i hi ↦ by rw [h i (mem_torusPosAt.2 hi)]; exact hω i hi
  have hind : ∀ p : (Fin d → ZMod (2 * N)) → ℝ,
      (patternSet N k p).indicator (fun _ ↦ (1 : ℝ)) ω
        = (patternSet N k p).indicator (fun _ ↦ (1 : ℝ)) ω' := by
    intro p
    by_cases hc : ω ∈ patternSet N k p
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem ((hmem p).1 hc)]
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem fun hh ↦ hc ((hmem p).2 hh)]
  simp only [patternTest, hind]

omit [NeZero N] in
lemma abs_patternTest_le_one (q : (Fin d → ZMod (2 * N)) → ℝ)
    (ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ)) : |patternTest N k q ω| ≤ 1 := by
  classical
  simp only [patternTest, Set.indicator_apply]
  split_ifs <;> norm_num

lemma measurable_cylinderEvents_patternTest (q : (Fin d → ZMod (2 * N)) → ℝ) :
    Measurable[cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ (Fin 1 → ℝ))
      (torusPosAt N k)] (patternTest N k q) :=
  measurable_cylinderEvents_iff_dependsOn.2 ⟨measurable_patternTest q, dependsOn_patternTest q⟩

/-- **The necessity criterion of Georgii's Examples (17.30) and (17.31).**  If some `±1` pattern
`q` on the torus makes the crossing form `⟨q, M q⟩` of the crossing matrix negative, then the
periodic Gibbs distribution of the Heisenberg potential (17.22) for the two-point a priori
measure `λ = δ_1 + δ_{-1}` fails to be `r_k`-positive.

Compare `isReflectionPositive_heisenbergPeriodicGibbs_of_posSemidef`: positive semidefiniteness
of `M` is sufficient, and this shows that the *quadratic form* of `M` being nonnegative on `±1`
vectors is already necessary. -/
theorem not_isReflectionPositive_heisenbergPeriodicGibbs_of_crossing_neg
    (heven : ∀ m, J (-m) = J m) (hflip : ∀ m, J (flipCoord k m) = J m)
    (q : (Fin d → ZMod (2 * N)) → ℝ) (hq : ∀ i, q i = 1 ∨ q i = -1)
    (hneg : q ⬝ᵥ crossingMatrix N J k *ᵥ q < 0) :
    ¬ IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin 1 → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N 1 J twoPointMeasure) := by
  intro hpos
  have h := hpos (patternTest N k q) (measurable_cylinderEvents_patternTest q)
    ⟨1, abs_patternTest_le_one q⟩
  simp only [siteEquiv_torusReflAt_toFun] at h
  rw [integral_patternTest_mul_comp_heisenbergPeriodicGibbs heven hflip q hq] at h
  have hs : Real.sinh (q ⬝ᵥ crossingMatrix N J k *ᵥ q) < 0 := by
    rw [Real.sinh_eq]
    have hlt : Real.exp (q ⬝ᵥ crossingMatrix N J k *ᵥ q)
        < Real.exp (-(q ⬝ᵥ crossingMatrix N J k *ᵥ q)) := Real.exp_lt_exp.2 (by linarith)
    linarith
  nlinarith [Real.exp_pos (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
    periodizedCoupling N J (i - j) * q i * q j)]

/-! ### Counting the sites of a hyperplane of the torus -/

/-- A layer `{i : i_k = v}` of the torus carries `(2N)^{d-1}` sites. -/
lemma sum_ite_torus_coord (v : ZMod (2 * N)) (c : ℝ) :
    ∑ i : Fin d → ZMod (2 * N), (if i k = v then c else 0)
      = (((2 * N) ^ (d - 1) : ℕ) : ℝ) * c := by
  classical
  have : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
  rw [Finset.sum_ite_eval_eq k v c, ZMod.card, Fintype.card_fin, nsmul_eq_mul]

/-! ### Georgii, Example (17.30): the crossing sum of a nearest-neighbour coupling -/

/-- **Georgii, Example (17.30): the crossing form of the constant pattern.**  For a
nearest-neighbour coupling the crossing matrix is diagonal, and its diagonal is `J(e_k)` at the
sites of the two interfaces `i_k ∈ {0, N-1}`, each of which carries `(2N)^{d-1}` sites.  Hence

`⟨1, M 1⟩ = 2 (2N)^{d-1} J(e_k)`.

**Erratum to Georgii, Example (17.30).**  He prints the constant `(2N)^{d-1}`.  The factor `2` is
missing: on the torus the plane of `r_k` is met by *two* interfaces — the one between the layers
`i_k = N-1` and `i_k = N`, and the one between `i_k = 2N-1` and `i_k = 0` created by the periodic
boundary condition — and each carries `(2N)^{d-1}` bonds.  Only the sign of the constant matters
for his conclusion. -/
theorem dotProduct_one_crossingMatrix_nearestNeighbour (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0) :
    (fun _ ↦ (1 : ℝ)) ⬝ᵥ crossingMatrix N J k *ᵥ (fun _ ↦ (1 : ℝ))
      = 2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * J (Pi.single k 1) := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hdiag : ∀ i : Fin d → ZMod (2 * N),
      (fun _ ↦ (1 : ℝ)) i * (crossingMatrix N J k *ᵥ (fun _ ↦ (1 : ℝ))) i
        = crossingMatrix N J k i i := by
    intro i
    rw [one_mul, Matrix.mulVec, dotProduct,
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ mul_one (crossingMatrix N J k i j)]
    refine Finset.sum_eq_single i (fun j _ hj ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)
    by_cases hi : (i k).val < N
    · by_cases hjj : (j k).val < N
      · exact crossingMatrix_eq_zero_of_nearestNeighbour hsupp hi hjj (Ne.symm hj)
      · exact crossingMatrix_eq_zero fun h ↦ hjj h.2
    · exact crossingMatrix_eq_zero fun h ↦ hi h.1
  rw [dotProduct, Finset.sum_congr rfl fun i _ ↦ hdiag i,
    Finset.sum_congr rfl fun i _ ↦ crossingMatrix_diag_nearestNeighbour heven hsupp i,
    Finset.sum_add_distrib]
  have hval : ∀ (z : ZMod (2 * N)) (t : ℕ), t < 2 * N → (z.val = t ↔ z = (t : ZMod (2 * N))) := by
    have : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩
    intro z t ht
    exact ⟨fun h ↦ by rw [← h]; simp, fun h ↦ by rw [h]; exact ZMod.val_natCast_of_lt ht⟩
  have hc1 : ∀ i : Fin d → ZMod (2 * N),
      ((i k).val = N - 1) ↔ i k = ((N - 1 : ℕ) : ZMod (2 * N)) :=
    fun i ↦ hval (i k) _ (by omega)
  have hc2 : ∀ i : Fin d → ZMod (2 * N), ((i k).val = 0) ↔ i k = ((0 : ℕ) : ZMod (2 * N)) :=
    fun i ↦ hval (i k) _ (by omega)
  simp only [hc1, hc2]
  rw [sum_ite_torus_coord _ (J (Pi.single k 1)), sum_ite_torus_coord _ (J (Pi.single k 1))]
  ring

/-- **Georgii, Example (17.30): the value of the reflection form at his test function.**  For a
nearest-neighbour coupling and the two-point a priori measure,

`°Z_Λ^Φ °γ_Λ^Φ(f f^*) = 4 e^{S} sinh[2 (2N)^{d-1} J(e_k)]`,

with `S = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j)`.  Georgii's prefactor `e^{-h}` cancels the `e^S`
(`integral_georgiiTest_mul_comp_nearestNeighbour`). -/
theorem integral_patternTest_mul_comp_nearestNeighbour (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0) :
    ∫ ω, patternTest N k (fun _ ↦ (1 : ℝ)) ω
          * patternTest N k (fun _ ↦ (1 : ℝ)) (ω ∘ torusReflAt N k)
        ∂(heisenbergPeriodicGibbs N 1 J twoPointMeasure)
      = 4 * Real.exp (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
            periodizedCoupling N J (i - j))
        * Real.sinh (2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * J (Pi.single k 1)) := by
  rw [integral_patternTest_mul_comp_heisenbergPeriodicGibbs heven
      (flipCoord_eq_of_nearestNeighbour hsupp heven) (fun _ ↦ (1 : ℝ)) (fun _ ↦ Or.inl rfl),
    dotProduct_one_crossingMatrix_nearestNeighbour heven hsupp]
  norm_num

/-- **Georgii's displayed value in Example (17.30).**  Georgii's own test function is
`f = e^{-h} σ_u 1_{σ_i = σ_u for all i ∈ Λ_{+,k}}` with
`h = ∑_{{i,j} ⊂ Λ_{+,k}} J_Λ(i-j) σ_i σ_j`.  On the configurations that carry `λ^Λ` and satisfy
the indicator, `h` is the constant `S/2` with `S = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j)` (the diagonal of
the double sum contributes `J_Λ(0) = 0` for a nearest-neighbour `J`), so his `f` is the bounded
function below, and

`°Z_Λ^Φ °γ_Λ^Φ(f f^*) = 4 sinh[2 (2N)^{d-1} J(e_k)]`,

which is Georgii's formula with the corrected constant. -/
theorem integral_georgiiTest_mul_comp_nearestNeighbour (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0) :
    ∫ ω, (Real.exp (-(∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j)) / 2) * patternTest N k (fun _ ↦ (1 : ℝ)) ω)
          * (Real.exp (-(∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
              periodizedCoupling N J (i - j)) / 2)
            * patternTest N k (fun _ ↦ (1 : ℝ)) (ω ∘ torusReflAt N k))
        ∂(heisenbergPeriodicGibbs N 1 J twoPointMeasure)
      = 4 * Real.sinh (2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * J (Pi.single k 1)) := by
  set S := ∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
    periodizedCoupling N J (i - j) with hS
  have hrw : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin 1 → ℝ),
      (Real.exp (-S / 2) * patternTest N k (fun _ ↦ (1 : ℝ)) ω)
          * (Real.exp (-S / 2) * patternTest N k (fun _ ↦ (1 : ℝ)) (ω ∘ torusReflAt N k))
        = Real.exp (-S) * (patternTest N k (fun _ ↦ (1 : ℝ)) ω
            * patternTest N k (fun _ ↦ (1 : ℝ)) (ω ∘ torusReflAt N k)) := by
    intro ω
    rw [show Real.exp (-S) = Real.exp (-S / 2) * Real.exp (-S / 2) by
      rw [← Real.exp_add]; ring_nf]
    ring
  simp only [hrw]
  rw [integral_const_mul, integral_patternTest_mul_comp_nearestNeighbour heven hsupp,
    ← hS]
  have hexp : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add]; simp
  rw [show Real.exp (-S) * (4 * Real.exp S
      * Real.sinh (2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * J (Pi.single k 1)))
    = (Real.exp (-S) * Real.exp S)
      * (4 * Real.sinh (2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * J (Pi.single k 1))) by ring,
    hexp, one_mul]

/-- **Georgii, Example (17.30), the necessity half.**  If the nearest-neighbour coupling is
*antiferromagnetic* in the direction `k` — `J(e_k) < 0` — then the Gibbs distribution in the torus
with periodic boundary condition for the two-point a priori measure `λ = δ_1 + δ_{-1}` is *not*
`r_k`-positive.  Together with `isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour`
this makes `0 ≤ J(e_k)` necessary as well as sufficient. -/
theorem not_isReflectionPositive_heisenbergPeriodicGibbs_nearestNeighbour
    (heven : ∀ m, J (-m) = J m)
    (hsupp : ∀ m : Fin d → ℤ, (∑ c, (m c).natAbs) ≠ 1 → J m = 0)
    (hneg : J (Pi.single k 1) < 0) :
    ¬ IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin 1 → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N 1 J twoPointMeasure) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine not_isReflectionPositive_heisenbergPeriodicGibbs_of_crossing_neg heven
    (flipCoord_eq_of_nearestNeighbour hsupp heven) (fun _ ↦ (1 : ℝ)) (fun _ ↦ Or.inl rfl) ?_
  rw [dotProduct_one_crossingMatrix_nearestNeighbour heven hsupp]
  have hpos : (0 : ℝ) < (((2 * N) ^ (d - 1) : ℕ) : ℝ) := by
    have : 0 < (2 * N) ^ (d - 1) := Nat.pow_pos (by omega)
    exact_mod_cast this
  nlinarith


/-! ### Georgii, Example (17.31): why his second test function cannot work

Georgii's Example (17.31) refutes `r_k`-positivity for `A < 2(d-1)|B|` "by looking at the same
function `f` and also at `f̃ = e^{-h} σ_u 1_{σ_i = -(-1)^{i_k} σ_u}`".  The alternation in the
direction `k` is however invisible to the reflection form, for every next-nearest neighbour
coupling: see `integral_patternTest_neg_one_pow_mul_comp`.
-/


/-- **A bond that crosses the plane of `r_k` has a nonzero component in the direction `k`.**
The `k`-th coordinate of the crossing index of two sites of `Λ_{+,k}` is `2N - 1 - i_k - j_k`,
which lies in `{1, …, 2N-1}` and is therefore never `0` modulo `2N`. -/
lemma crossingIndex_add_apply_ne_zero {i j : Fin d → ZMod (2 * N)}
    (hi : (i k).val < N) (hj : (j k).val < N) (ℓ : Fin d → ℤ) :
    (crossingIndex N k i j + (2 * N : ℤ) • ℓ) k ≠ 0 := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : ((i k).val : ℤ) < (N : ℤ) := by exact_mod_cast hi
  have hb : ((j k).val : ℤ) < (N : ℤ) := by exact_mod_cast hj
  have ha0 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ ((j k).val : ℤ) := Int.natCast_nonneg _
  have hxk : (crossingIndex N k i j + (2 * N : ℤ) • ℓ) k
      = (2 * N : ℤ) - 1 - ((i k).val : ℤ) - ((j k).val : ℤ) + (2 * N : ℤ) * ℓ k := by
    simp [crossingIndex_self]
  rw [hxk]
  intro h0
  have h1 : ((i k).val : ℤ) + ((j k).val : ℤ) = (2 * N : ℤ) * (1 + ℓ k) - 1 := by linarith
  have h2 : (1 : ℤ) ≤ (2 * N : ℤ) * (1 + ℓ k) := by linarith
  have h3 : (2 * N : ℤ) * (1 + ℓ k) ≤ (2 * N : ℤ) - 1 := by linarith
  have h4 : (1 : ℤ) ≤ 1 + ℓ k := by nlinarith
  nlinarith

/-- **The `k`-parity of the two ends of a crossing bond is the same.**  If the crossing matrix
entry `M(i, j)` is nonzero for a coupling supported on `{∑_c m_c² ≤ 2}` — that is, if some bond of
the potential joins `r_k i` to `j` — then `i_k + j_k` is even.

This is why an alternation in the direction `k` is invisible to the reflection form: the plane of
`r_k` lies *between* two layers of equal index `i_k = j_k`. -/
lemma even_val_add_val_of_crossingMatrix_ne_zero
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    {i j : Fin d → ZMod (2 * N)} (hne : crossingMatrix N J k i j ≠ 0) :
    Even ((i k).val + (j k).val) := by
  classical
  by_cases hij : (i k).val < N ∧ (j k).val < N
  swap
  · exact absurd (crossingMatrix_eq_zero hij) hne
  obtain ⟨hi, hj⟩ := hij
  rw [crossingMatrix_eq_tsum hi hj] at hne
  -- some term of the periodisation is nonzero
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Fin d → ℤ, J (crossingIndex N k i j + (2 * N : ℤ) • ℓ) ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hne (by rw [tsum_congr h, tsum_zero])
  set x := crossingIndex N k i j + (2 * N : ℤ) • ℓ with hx
  -- that term lies in the ball `∑ x_c² ≤ 2`, so `x_k = ±1`
  have hball : (∑ c, x c ^ 2) ≤ 2 := by
    by_contra h
    exact hℓ (hJ0 x (not_le.1 h))
  have hle : x k ^ 2 ≤ 2 :=
    le_trans (Finset.single_le_sum (f := fun c ↦ x c ^ 2)
      (fun c _ ↦ sq_nonneg (x c)) (Finset.mem_univ k)) hball
  have hne0 : x k ≠ 0 := crossingIndex_add_apply_ne_zero hi hj ℓ
  have hpm : x k = 1 ∨ x k = -1 := by
    have h1 : x k ≤ 1 := by nlinarith [sq_nonneg (x k - 1)]
    have h2 : -1 ≤ x k := by nlinarith [sq_nonneg (x k + 1)]
    omega
  -- and `x_k = ±1` forces `i_k + j_k` to be even
  have hxk : x k = (2 * N : ℤ) - 1 - ((i k).val : ℤ) - ((j k).val : ℤ) + (2 * N : ℤ) * ℓ k := by
    simp [hx, crossingIndex_self]
  obtain ⟨r, hr⟩ : ∃ r : ℤ, ((i k).val : ℤ) + ((j k).val : ℤ) = 2 * r := by
    rcases hpm with h | h <;> rw [hxk] at h
    · exact ⟨(N : ℤ) - 1 + (N : ℤ) * ℓ k, by linarith⟩
    · exact ⟨(N : ℤ) + (N : ℤ) * ℓ k, by linarith⟩
  refine Nat.even_iff.2 ?_
  omega

/-- **The alternation in the direction `k` is invisible to the crossing form.**  For every
coupling supported on the next-nearest neighbour bonds `∑_c m_c² ≤ 2`, the `±1` pattern
`i ↦ (-1)^{i_k}` gives the crossing form the *same* value as the constant pattern `1`. -/
theorem dotProduct_neg_one_pow_crossingMatrix
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) :
    (fun i : Fin d → ZMod (2 * N) ↦ (-1 : ℝ) ^ (i k).val) ⬝ᵥ
        crossingMatrix N J k *ᵥ (fun i : Fin d → ZMod (2 * N) ↦ (-1 : ℝ) ^ (i k).val)
      = (fun _ ↦ (1 : ℝ)) ⬝ᵥ crossingMatrix N J k *ᵥ (fun _ ↦ (1 : ℝ)) := by
  classical
  simp only [dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : crossingMatrix N J k i j = 0
  · rw [h]; ring
  · have hev := even_val_add_val_of_crossingMatrix_ne_zero hJ0 h
    have hone : ((-1 : ℝ) ^ (i k).val) * ((-1 : ℝ) ^ (j k).val) = 1 := by
      rw [← pow_add]
      exact hev.neg_one_pow
    calc (-1 : ℝ) ^ (i k).val * (crossingMatrix N J k i j * (-1 : ℝ) ^ (j k).val)
        = ((-1 : ℝ) ^ (i k).val * (-1 : ℝ) ^ (j k).val) * crossingMatrix N J k i j := by ring
      _ = 1 * (crossingMatrix N J k i j * 1) := by rw [hone]; ring

omit [NeZero N] in
lemma neg_one_pow_val_eq_one_or (i : Fin d → ZMod (2 * N)) :
    (-1 : ℝ) ^ (i k).val = 1 ∨ (-1 : ℝ) ^ (i k).val = -1 := by
  rcases Nat.even_or_odd (i k).val with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

/-- **Erratum to Georgii, Example (17.31).**  His second test function
`f̃ = e^{-h} σ_u 1_{σ_i = -(-1)^{i_k} σ_u for all i ∈ Λ_{+,k}}`, which alternates in the direction
`k`, has the *same* hyperbolic sine as his first test function `f`: the two reflection forms
differ only by the positive factor `e^{S_p - S_1}`, so `f̃` detects exactly what `f` detects and
nothing more.

The reason is `even_val_add_val_of_crossingMatrix_ne_zero`: on the torus the plane of `r_k` lies
*between* two layers, and a bond that crosses it joins `r_k i` to `j` with `i_k = j_k`; the two
`k`-parities cancel.  Georgii's `i_k` must therefore be read as an alternation in the directions
*transverse* to `k` — with which the crossing form of a next-nearest neighbour coupling becomes
`2(2N)^{d-1}(A - 2(d-1)B)` instead of `2(2N)^{d-1}(A + 2(d-1)B)`. -/
theorem integral_patternTest_neg_one_pow_mul_comp (heven : ∀ m, J (-m) = J m)
    (hflip : ∀ m, J (flipCoord k m) = J m)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) :
    ∫ ω, patternTest N k (fun i ↦ (-1 : ℝ) ^ (i k).val) ω
          * patternTest N k (fun i ↦ (-1 : ℝ) ^ (i k).val) (ω ∘ torusReflAt N k)
        ∂(heisenbergPeriodicGibbs N 1 J twoPointMeasure)
      = 4 * Real.exp (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
            periodizedCoupling N J (i - j) * (-1 : ℝ) ^ (i k).val * (-1 : ℝ) ^ (j k).val)
        * Real.sinh ((fun _ ↦ (1 : ℝ)) ⬝ᵥ crossingMatrix N J k *ᵥ (fun _ ↦ (1 : ℝ))) := by
  rw [integral_patternTest_mul_comp_heisenbergPeriodicGibbs heven hflip
      (fun i ↦ (-1 : ℝ) ^ (i k).val) (fun i ↦ neg_one_pow_val_eq_one_or i),
    dotProduct_neg_one_pow_crossingMatrix hJ0]

variable (N k) in
/-- **The weight of a bond in the crossing form.**  For a bond `m ∈ ℤ^d` and a function `q` on the
torus, `∑_{i ∈ Λ_{+,k}, r_k i - m ∈ Λ_{+,k}} q_i q_{r_k i - m}`: the number of copies of the bond
`m`, read on the torus, that join a site of `Λ_{-,k}` to a site of `Λ_{+,k}`, each weighted by the
values of `q` at its two ends.  The crossing form is `∑_m J(m) ×` this weight
(`dotProduct_crossingMatrix_mulVec_eq_tsum`). -/
def crossingWeight (q : (Fin d → ZMod (2 * N)) → ℝ) (m : Fin d → ℤ) : ℝ :=
  ∑ i ∈ torusPosAtFinset N k,
    if torusReflAt N k i - (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) ∈ torusPosAtFinset N k
      then q i * q (torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) else 0

/-- **The crossing form is a sum over bonds.**  For an absolutely summable coupling,
`⟨q, M q⟩ = ∑_{m ∈ ℤ^d} J(m) · w_q(m)`, where `w_q(m)` is the weight `crossingWeight` of the bond
`m`: unfolding the periodisation `J_Λ = ∑_ℓ J(· + 2Nℓ)` turns the double sum over the torus into
a sum over the bonds of `ℤ^d` that cross the plane of `r_k`. -/
theorem dotProduct_crossingMatrix_mulVec_eq_tsum (hsum : Summable J)
    (q : (Fin d → ZMod (2 * N)) → ℝ) :
    q ⬝ᵥ crossingMatrix N J k *ᵥ q = ∑' m : Fin d → ℤ, J m * crossingWeight N k q m := by
  classical
  have hfib : ∀ z : Fin d → ZMod (2 * N), Summable fun m : Fin d → ℤ ↦
      if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then J m else 0 := by
    intro z
    have : (fun m : Fin d → ℤ ↦ if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then J m else 0)
        = Set.indicator {m | (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z} J := by
      funext m
      simp [Set.indicator_apply]
    rw [this]
    exact hsum.indicator _
  have h1 : q ⬝ᵥ crossingMatrix N J k *ᵥ q
      = ∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
          periodizedCoupling N J (torusReflAt N k i - j) * (q i * q j) := by
    simp only [dotProduct, Matrix.mulVec, torusPosAtFinset, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hi : (i k).val < N
    · rw [ite_eq_left hi]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : (j k).val < N
      · rw [ite_eq_left hj, crossingMatrix_of_mem hi hj]; ring
      · rw [ite_eq_right hj, crossingMatrix_eq_zero (fun h ↦ hj h.2)]; ring
    · rw [ite_eq_right hi]
      exact Finset.sum_eq_zero fun j _ ↦ by
        rw [crossingMatrix_eq_zero (fun h ↦ hi h.1)]; ring
  have hS : ∀ i j : Fin d → ZMod (2 * N), Summable fun m : Fin d → ℤ ↦
      (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = torusReflAt N k i - j then J m else 0)
        * (q i * q j) :=
    fun i j ↦ (hfib _).mul_right _
  have h2 : ∀ i j : Fin d → ZMod (2 * N),
      periodizedCoupling N J (torusReflAt N k i - j) * (q i * q j)
        = ∑' m : Fin d → ℤ,
          (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = torusReflAt N k i - j then J m else 0)
            * (q i * q j) := by
    intro i j
    rw [periodizedCoupling_eq_tsum_ite, tsum_mul_right]
  have h3 : ∀ i : Fin d → ZMod (2 * N),
      ∑ j ∈ torusPosAtFinset N k, ∑' m : Fin d → ℤ,
          (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = torusReflAt N k i - j then J m else 0)
            * (q i * q j)
        = ∑' m : Fin d → ℤ, ∑ j ∈ torusPosAtFinset N k,
          (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = torusReflAt N k i - j then J m else 0)
            * (q i * q j) :=
    fun i ↦ (Summable.tsum_finsetSum fun j _ ↦ hS i j).symm
  rw [h1]
  simp_rw [h2, h3]
  rw [← Summable.tsum_finsetSum fun i _ ↦ summable_sum fun j _ ↦ hS i j]
  refine tsum_congr fun m ↦ ?_
  rw [crossingWeight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hiff : ∀ j : Fin d → ZMod (2 * N),
      ((fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = torusReflAt N k i - j)
        ↔ (j = torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) := by
    intro j
    rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq, add_comm]
  simp only [hiff, ite_mul, zero_mul, Finset.sum_ite_eq', mul_ite, mul_zero]

/-! ### The crossing weight of a short bond -/

/-- The `k`-th coordinate of `r_k i - m` on the torus, as a residue modulo `2N`. -/
lemma val_torusReflAt_sub_cast_apply_self (i : Fin d → ZMod (2 * N)) (m : Fin d → ℤ) :
    (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ)
      = (-1 - ((i k).val : ℤ) - m k) % (2 * N : ℤ) := by
  have h : (torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k
      = ((-1 - ((i k).val : ℤ) - m k : ℤ) : ZMod (2 * N)) := by
    simp only [Pi.sub_apply, torusReflAt_apply_self]
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h, ZMod.val_intCast]
  push_cast
  rfl

/-- **A bond with `m_k = 0` never crosses the plane of `r_k`.** -/
lemma torusReflAt_sub_cast_notMem_of_eq_zero {i : Fin d → ZMod (2 * N)} (hi : (i k).val < N)
    {m : Fin d → ℤ} (hm : m k = 0) :
    torusReflAt N k i - (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) ∉ torusPosAtFinset N k := by
  rw [mem_torusPosAtFinset, not_lt]
  have h := val_torusReflAt_sub_cast_apply_self (k := k) i m
  rw [hm, sub_zero] at h
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : ((i k).val : ℤ) < N := by exact_mod_cast hi
  have ha0 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  have hmod : (-1 - ((i k).val : ℤ)) % (2 * N : ℤ) = -1 - ((i k).val : ℤ) + 2 * N := by
    rw [← Int.add_mul_emod_self_left (a := -1 - ((i k).val : ℤ)) (b := (2 * N : ℤ)) (c := 1),
      mul_one]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  have : (N : ℤ) ≤ (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ) := by
    rw [h, hmod]; linarith
  exact_mod_cast this

/-- **A bond with `m_k = 1` crosses the plane of `r_k` from `i ∈ Λ_{+,k}` iff `i_k = N - 1`.** -/
lemma torusReflAt_sub_cast_mem_iff_of_eq_one {i : Fin d → ZMod (2 * N)} (hi : (i k).val < N)
    {m : Fin d → ℤ} (hm : m k = 1) :
    torusReflAt N k i - (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) ∈ torusPosAtFinset N k
      ↔ (i k).val = N - 1 := by
  rw [mem_torusPosAtFinset]
  have h := val_torusReflAt_sub_cast_apply_self (k := k) i m
  rw [hm] at h
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : ((i k).val : ℤ) < N := by exact_mod_cast hi
  have ha0 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  have hmod : (-1 - ((i k).val : ℤ) - 1) % (2 * N : ℤ) = -1 - ((i k).val : ℤ) - 1 + 2 * N := by
    rw [← Int.add_mul_emod_self_left (a := -1 - ((i k).val : ℤ) - 1) (b := (2 * N : ℤ)) (c := 1),
      mul_one]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  constructor
  · intro hlt
    have : (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ) < N := by
      exact_mod_cast hlt
    rw [h, hmod] at this
    omega
  · intro heq
    have : (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ) < N := by
      rw [h, hmod]; omega
    exact_mod_cast this

/-- **A bond with `m_k = -1` crosses the plane of `r_k` from `i ∈ Λ_{+,k}` iff `i_k = 0`.** -/
lemma torusReflAt_sub_cast_mem_iff_of_eq_neg_one {i : Fin d → ZMod (2 * N)}
    (hi : (i k).val < N) {m : Fin d → ℤ} (hm : m k = -1) :
    torusReflAt N k i - (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) ∈ torusPosAtFinset N k
      ↔ (i k).val = 0 := by
  rw [mem_torusPosAtFinset]
  have h := val_torusReflAt_sub_cast_apply_self (k := k) i m
  rw [hm, show (-1 - ((i k).val : ℤ) - (-1)) = -((i k).val : ℤ) by ring] at h
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : ((i k).val : ℤ) < N := by exact_mod_cast hi
  have ha0 : (0 : ℤ) ≤ ((i k).val : ℤ) := Int.natCast_nonneg _
  by_cases hz : (i k).val = 0
  · have h0 : (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ) = 0 := by
      rw [h, hz]; simp
    have : ((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val = 0 := by
      exact_mod_cast h0
    rw [this]
    exact ⟨fun _ ↦ hz, fun _ ↦ Nat.pos_of_ne_zero (NeZero.ne N)⟩
  · have hz' : (1 : ℤ) ≤ ((i k).val : ℤ) := by
      have : 0 < (i k).val := Nat.pos_of_ne_zero hz
      exact_mod_cast this
    have hmod : (-((i k).val : ℤ)) % (2 * N : ℤ) = -((i k).val : ℤ) + 2 * N := by
      rw [← Int.add_mul_emod_self_left (a := -((i k).val : ℤ)) (b := (2 * N : ℤ)) (c := 1),
        mul_one]
      exact Int.emod_eq_of_lt (by linarith) (by linarith)
    constructor
    · intro hlt
      have : (((torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N))) k).val : ℤ) < N := by
        exact_mod_cast hlt
      rw [h, hmod] at this
      omega
    · intro heq
      exact absurd heq hz

/-- `z.val + (z - t).val ≡ t (mod 2)` in `ℤ/2N`: the parity of a residue and of its translate by
`t` differ by the parity of `t`, because `2N` is even. -/
lemma even_val_add_val_sub_intCast_iff (z : ZMod (2 * N)) (t : ℤ) :
    Even (z.val + (z - (t : ZMod (2 * N))).val) ↔ Even t := by
  have h : (((z - (t : ZMod (2 * N))).val : ℕ) : ℤ) = ((z.val : ℤ) - t) % (2 * N : ℤ) := by
    have : z - (t : ZMod (2 * N)) = (((z.val : ℤ) - t : ℤ) : ZMod (2 * N)) := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_intCast]
    push_cast
    rfl
  have h2 : (((z.val : ℤ) - t) % (2 * N : ℤ)) % 2 = ((z.val : ℤ) - t) % 2 :=
    Int.emod_emod_of_dvd _ ⟨N, rfl⟩
  rw [← Int.even_coe_nat, Int.even_iff, Int.even_iff]
  push_cast
  rw [h]
  omega

/-- For `x = ±1`, `x ^ a = x ^ b` as soon as `a` and `b` have the same parity. -/
lemma pow_eq_pow_of_even_iff {x : ℝ} (hx : x = 1 ∨ x = -1) {a b : ℕ}
    (h : Even a ↔ Even b) : x ^ a = x ^ b := by
  rcases hx with rfl | rfl
  · simp
  · rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, (h.1 ha).neg_one_pow]
    · have hb : Odd b := by
        rcases Nat.even_or_odd b with hb | hb
        · exact absurd (h.2 hb) (Nat.not_even_iff_odd.2 ha)
        · exact hb
      rw [ha.neg_one_pow, hb.neg_one_pow]

variable (N k) in
/-- **The `±1` patterns of Examples (17.30)–(17.31).**  For signs `χ_c ∈ {1, -1}` in the
directions `c ≠ k` transverse to the reflection, the configuration `i ↦ ∏_{c ≠ k} χ_c^{i_c}` of
the torus: constant along `k`, and alternating along each direction `c` with `χ_c = -1`.  With
`χ = 1` it is the constant pattern of Georgii's test function `f`; with `χ = -1` it is the pattern
which his second test function `f̃` in Example (17.31) must be read to carry. -/
def transversePattern (χ : Fin d → ℝ) (i : Fin d → ZMod (2 * N)) : ℝ :=
  ∏ c ∈ Finset.univ.erase k, χ c ^ (i c).val

omit [NeZero N] in
lemma transversePattern_eq_one_or {χ : Fin d → ℝ} (hχ : ∀ c, χ c = 1 ∨ χ c = -1)
    (i : Fin d → ZMod (2 * N)) :
    transversePattern N k χ i = 1 ∨ transversePattern N k χ i = -1 := by
  refine Finset.prod_induction _ (fun x ↦ x = 1 ∨ x = -1) ?_ (Or.inl rfl) fun c _ ↦ ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · rcases hχ c with h | h
    · rw [h, one_pow]; exact Or.inl rfl
    · rw [h]; exact neg_one_pow_eq_or ℝ _

omit [NeZero N] in
@[simp] lemma transversePattern_one (i : Fin d → ZMod (2 * N)) :
    transversePattern N k (fun _ ↦ (1 : ℝ)) i = 1 := by
  simp [transversePattern]

/-- **The product of the pattern at the two ends of a bond depends only on the bond.**  For the
pattern `q_χ`, `q_χ(i) q_χ(r_k i - m) = ∏_{c ≠ k} χ_c^{|m_c|}`: along each transverse direction
the two ends differ by `m_c`, and only its parity matters. -/
lemma transversePattern_mul_transversePattern_sub {χ : Fin d → ℝ}
    (hχ : ∀ c, χ c = 1 ∨ χ c = -1) (i : Fin d → ZMod (2 * N)) (m : Fin d → ℤ) :
    transversePattern N k χ i
        * transversePattern N k χ (torusReflAt N k i - fun c ↦ ((m c : ℤ) : ZMod (2 * N)))
      = ∏ c ∈ Finset.univ.erase k, χ c ^ (m c).natAbs := by
  rw [transversePattern, transversePattern, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c hc ↦ ?_
  have hck : c ≠ k := Finset.ne_of_mem_erase hc
  rw [← pow_add, Pi.sub_apply, torusReflAt_apply_of_ne hck]
  exact pow_eq_pow_of_even_iff (hχ c)
    ((even_val_add_val_sub_intCast_iff (i c) (m c)).trans Int.natAbs_even.symm)

lemma crossingWeight_of_apply_eq_zero (q : (Fin d → ZMod (2 * N)) → ℝ) {m : Fin d → ℤ}
    (hm : m k = 0) : crossingWeight N k q m = 0 :=
  Finset.sum_eq_zero fun _ hi ↦
    ite_eq_right (torusReflAt_sub_cast_notMem_of_eq_zero (mem_torusPosAtFinset.1 hi) hm)

/-- **The crossing weight of a bond with `m_k = ±1` under a `±1` pattern.**  Such a bond crosses
the plane of `r_k` exactly once from each of the `(2N)^{d-1}` sites of one layer, and each crossing
carries the sign `∏_{c ≠ k} χ_c^{|m_c|}`. -/
theorem crossingWeight_transversePattern {χ : Fin d → ℝ} (hχ : ∀ c, χ c = 1 ∨ χ c = -1)
    {m : Fin d → ℤ} (hm : m k = 1 ∨ m k = -1) :
    crossingWeight N k (transversePattern N k χ) m
      = (((2 * N) ^ (d - 1) : ℕ) : ℝ) * ∏ c ∈ Finset.univ.erase k, χ c ^ (m c).natAbs := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set K := ∏ c ∈ Finset.univ.erase k, χ c ^ (m c).natAbs with hK
  obtain ⟨v, hv, hcond⟩ : ∃ v : ℕ, v < N ∧ ∀ i : Fin d → ZMod (2 * N), (i k).val < N →
      (torusReflAt N k i - (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) ∈ torusPosAtFinset N k
        ↔ (i k).val = v) := by
    rcases hm with hm | hm
    · exact ⟨N - 1, by omega, fun i hi ↦ torusReflAt_sub_cast_mem_iff_of_eq_one hi hm⟩
    · exact ⟨0, hN, fun i hi ↦ torusReflAt_sub_cast_mem_iff_of_eq_neg_one hi hm⟩
  calc crossingWeight N k (transversePattern N k χ) m
      = ∑ i ∈ torusPosAtFinset N k, if (i k).val = v then K else 0 := by
        rw [crossingWeight]
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        rw [transversePattern_mul_transversePattern_sub hχ]
        exact if_congr (hcond i (mem_torusPosAtFinset.1 hi)) rfl rfl
    _ = ∑ i : Fin d → ZMod (2 * N), if i k = (v : ZMod (2 * N)) then K else 0 := by
        rw [torusPosAtFinset, Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hiv : (i k).val = v
        · rw [ite_eq_left (by omega), ite_eq_left hiv,
            ite_eq_left (by rw [← hiv, ZMod.natCast_zmod_val])]
        · have : i k ≠ (v : ZMod (2 * N)) := fun h ↦
            hiv (by rw [h, ZMod.val_natCast_of_lt (by omega)])
          rw [ite_eq_right this]
          split_ifs <;> rfl
    _ = _ := by rw [sum_ite_torus_coord]

/-! ### Georgii, Example (17.31): the crossing form of a next-nearest neighbour coupling -/

/-- A next-nearest neighbour coupling is even. -/
lemma even_of_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) (m : Fin d → ℤ) : J (-m) = J m := by
  have hs : ∑ c, (-m) c ^ 2 = ∑ c, m c ^ 2 := Finset.sum_congr rfl fun c _ ↦ by simp
  rcases lt_trichotomy (∑ c, m c ^ 2) 2 with h | h | h
  · rcases Nat.lt_or_ge 1 (∑ c, m c ^ 2).toNat with h1 | h1
    · omega
    · have h0 : ∑ c, m c ^ 2 = 0 ∨ ∑ c, m c ^ 2 = 1 := by
        have hnn : 0 ≤ ∑ c, m c ^ 2 := Finset.sum_nonneg fun c _ ↦ sq_nonneg _
        omega
      rcases h0 with h0 | h0
      · have hm : m = 0 := by
          funext c
          have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ sq_nonneg (m c)).1 h0 c
            (Finset.mem_univ c)
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
        rw [hm, neg_zero]
      · rw [hJ1 _ (hs.trans h0), hJ1 _ h0]
  · rw [hJ2 _ (hs.trans h), hJ2 _ h]
  · rw [hJ0 _ (hs ▸ h), hJ0 _ h]

/-- A next-nearest neighbour coupling is invariant under the flip of any coordinate. -/
lemma flipCoord_eq_of_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) (m : Fin d → ℤ) :
    J (flipCoord k m) = J m := by
  have hs : ∑ c, (flipCoord k m) c ^ 2 = ∑ c, m c ^ 2 := by
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    by_cases hc : c = k
    · subst hc; simp [flipCoord]
    · simp [flipCoord, hc]
  rcases lt_trichotomy (∑ c, m c ^ 2) 2 with h | h | h
  · have hnn : 0 ≤ ∑ c, m c ^ 2 := Finset.sum_nonneg fun c _ ↦ sq_nonneg _
    have h0 : ∑ c, m c ^ 2 = 0 ∨ ∑ c, m c ^ 2 = 1 := by omega
    rcases h0 with h0 | h0
    · have hm : m = 0 := by
        funext c
        have := (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ sq_nonneg (m c)).1 h0 c
          (Finset.mem_univ c)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      have : flipCoord k m = m := by
        rw [hm]; funext c; by_cases hc : c = k
        · subst hc; simp [flipCoord]
        · simp [flipCoord, hc]
      rw [this]
    · rw [hJ1 _ (hs.trans h0), hJ1 _ h0]
  · rw [hJ2 _ (hs.trans h), hJ2 _ h]
  · rw [hJ0 _ (hs ▸ h), hJ0 _ h]

/-- A next-nearest neighbour coupling is (absolutely) summable: it vanishes off the box
`{-1, 0, 1}^d`. -/
lemma summable_of_nextNearestNeighbour
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) : Summable J := by
  classical
  refine summable_of_ne_finset_zero (s := Fintype.piFinset fun _ ↦ ({-1, 0, 1} : Finset ℤ))
    fun m hm ↦ hJ0 m ?_
  rw [Fintype.mem_piFinset] at hm
  push Not at hm
  obtain ⟨c, hc⟩ := hm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have h4 : 4 ≤ m c ^ 2 := by
    rcases le_or_gt (m c) (-2) with h | h
    · nlinarith
    · have : 2 ≤ m c := by omega
      nlinarith
  have hle : m c ^ 2 ≤ ∑ c', m c' ^ 2 :=
    Finset.single_le_sum (f := fun c' ↦ m c' ^ 2) (fun c' _ ↦ sq_nonneg (m c')) (Finset.mem_univ c)
  omega

/-- **The sum of squares of an axis bond.** -/
lemma sum_sq_smul_single (t : ℤ) : ∑ c, (t • (Pi.single k (1 : ℤ) : Fin d → ℤ)) c ^ 2 = t ^ 2 := by
  classical
  rw [Finset.sum_eq_single k (fun c _ hc ↦ by simp [Pi.single_eq_of_ne hc])
    (fun h ↦ absurd (Finset.mem_univ k) h)]
  simp

/-- **The sum of squares of a diagonal bond.** -/
lemma sum_sq_smul_single_add_smul_single {c : Fin d} (hck : c ≠ k) (s t : ℤ) :
    ∑ c', (s • (Pi.single k (1 : ℤ) : Fin d → ℤ) + t • (Pi.single c (1 : ℤ) : Fin d → ℤ)) c' ^ 2
      = s ^ 2 + t ^ 2 := by
  classical
  rw [Finset.sum_eq_add k c (Ne.symm hck)
    (fun c' _ hc' ↦ by simp [Pi.single_eq_of_ne hc'.1, Pi.single_eq_of_ne hc'.2])
    (fun h ↦ absurd (Finset.mem_univ k) h) (fun h ↦ absurd (Finset.mem_univ c) h)]
  simp [Pi.single_eq_of_ne hck, Pi.single_eq_of_ne (Ne.symm hck)]

/-- **Georgii, Example (17.31): the crossing form of a next-nearest neighbour coupling, as a sum
over bonds.**  For the pattern `q_χ`,

`∑_m J(m) w_{q_χ}(m) = 2 (2N)^{d-1} (A + 2B ∑_{c ≠ k} χ_c)`.

Only the bonds with `m_k = ±1` cross the plane of `r_k` (`crossingWeight_of_apply_eq_zero`), and
among those only `±e_k` (weight `A`, sign `+1`) and `±e_k ± e_c`, `c ≠ k` (weight `B`, sign
`χ_c`) carry a nonzero coupling. -/
theorem tsum_mul_crossingWeight_transversePattern_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    {χ : Fin d → ℝ} (hχ : ∀ c, χ c = 1 ∨ χ c = -1) :
    ∑' m : Fin d → ℤ, J m * crossingWeight N k (transversePattern N k χ) m
      = 2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * (A + 2 * B * ∑ c ∈ Finset.univ.erase k, χ c) := by
  classical
  set q := transversePattern N k χ with hq
  set e : Fin d → (Fin d → ℤ) := fun c ↦ Pi.single c (1 : ℤ) with he
  set F₁ : Finset (Fin d → ℤ) := ({1, -1} : Finset ℤ).image (fun t ↦ t • e k) with hF₁
  set F₂ : Finset (Fin d → ℤ) :=
    ((({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ)) ×ˢ Finset.univ.erase k).image
      (fun p ↦ p.1.1 • e k + p.1.2 • e p.2) with hF₂
  have hsq : ∀ m : Fin d → ℤ, ∀ c, 0 ≤ m c ^ 2 := fun m c ↦ sq_nonneg _
  -- the values of `J` and of the crossing weight on the two kinds of bonds
  have hJA : ∀ t : ℤ, t = 1 ∨ t = -1 → J (t • e k) = A := by
    intro t ht
    refine hJ1 _ ?_
    rw [he, sum_sq_smul_single]
    rcases ht with rfl | rfl <;> norm_num
  have hJB : ∀ (s t : ℤ) (c : Fin d), s = 1 ∨ s = -1 → t = 1 ∨ t = -1 → c ≠ k →
      J (s • e k + t • e c) = B := by
    intro s t c hs ht hck
    refine hJ2 _ ?_
    rw [he, sum_sq_smul_single_add_smul_single hck]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num
  have hwA : ∀ t : ℤ, t = 1 ∨ t = -1 →
      crossingWeight N k q (t • e k) = (((2 * N) ^ (d - 1) : ℕ) : ℝ) := by
    intro t ht
    rw [hq, crossingWeight_transversePattern hχ (by simpa [he] using ht)]
    rw [Finset.prod_eq_one fun c hc ↦ ?_, mul_one]
    simp [he, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hc)]
  have hwB : ∀ (s t : ℤ) (c : Fin d), s = 1 ∨ s = -1 → t = 1 ∨ t = -1 → c ≠ k →
      crossingWeight N k q (s • e k + t • e c) = (((2 * N) ^ (d - 1) : ℕ) : ℝ) * χ c := by
    intro s t c hs ht hck
    rw [hq, crossingWeight_transversePattern hχ
      (by simpa [he, Pi.single_eq_of_ne (Ne.symm hck)] using hs)]
    congr 1
    rw [Finset.prod_eq_single c (fun c' hc' hne ↦ ?_) (fun h ↦ absurd
      (Finset.mem_erase.2 ⟨hck, Finset.mem_univ c⟩) h)]
    · have : (s • e k + t • e c) c = t := by
        simp [he, Pi.single_eq_of_ne hck]
      rw [this]
      rcases ht with rfl | rfl <;> simp
    · simp [he, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hc'), Pi.single_eq_of_ne hne]
  -- the support of the summand
  have hsupp : ∀ m ∉ F₁ ∪ F₂, J m * crossingWeight N k q m = 0 := by
    intro m hm
    by_contra hne
    have hJm : J m ≠ 0 := fun h ↦ hne (by rw [h, zero_mul])
    have hcw : crossingWeight N k q m ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
    have hle : ∑ c, m c ^ 2 ≤ 2 := by
      by_contra h
      exact hJm (hJ0 m (not_le.1 h))
    have hmk : m k ≠ 0 := fun h ↦ hcw (crossingWeight_of_apply_eq_zero q h)
    have hmk1 : m k = 1 ∨ m k = -1 := by
      have h1 : m k ^ 2 ≤ 2 :=
        le_trans (Finset.single_le_sum (f := fun c ↦ m c ^ 2) (fun c _ ↦ hsq m c)
          (Finset.mem_univ k)) hle
      have h2 : m k ≤ 1 := by nlinarith
      have h3 : -1 ≤ m k := by nlinarith
      omega
    have hmk2 : m k ^ 2 = 1 := by rcases hmk1 with h | h <;> rw [h] <;> norm_num
    have hsplit := Finset.add_sum_erase Finset.univ (fun c ↦ m c ^ 2) (Finset.mem_univ k)
    have htr : ∑ c ∈ Finset.univ.erase k, m c ^ 2 ≤ 1 := by linarith
    apply hm
    by_cases hall : ∀ c, c ≠ k → m c = 0
    · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨m k, by simpa using hmk1, ?_⟩)
      funext c
      by_cases hc : c = k
      · subst hc; simp [he]
      · simp [he, Pi.single_eq_of_ne hc, hall c hc]
    · push Not at hall
      obtain ⟨c, hck, hc0⟩ := hall
      have hc1 : m c ^ 2 = 1 := by
        have h1 : 0 < m c ^ 2 := by positivity
        have h2 : m c ^ 2 ≤ ∑ c' ∈ Finset.univ.erase k, m c' ^ 2 :=
          Finset.single_le_sum (f := fun c' ↦ m c' ^ 2) (fun c' _ ↦ hsq m c')
            (Finset.mem_erase.2 ⟨hck, Finset.mem_univ c⟩)
        linarith
      have hmc1 : m c = 1 ∨ m c = -1 := by
        have h2 : m c ≤ 1 := by nlinarith
        have h3 : -1 ≤ m c := by nlinarith
        omega
      have hrest : ∀ c', c' ≠ k → c' ≠ c → m c' = 0 := by
        intro c' hc'k hc'c
        have hsplit' := Finset.add_sum_erase (Finset.univ.erase k) (fun c ↦ m c ^ 2)
          (Finset.mem_erase.2 ⟨hck, Finset.mem_univ c⟩)
        have h3 : m c' ^ 2 ≤ ∑ c'' ∈ (Finset.univ.erase k).erase c, m c'' ^ 2 :=
          Finset.single_le_sum (f := fun c'' ↦ m c'' ^ 2) (fun c'' _ ↦ hsq m c'')
            (Finset.mem_erase.2 ⟨hc'c, Finset.mem_erase.2 ⟨hc'k, Finset.mem_univ c'⟩⟩)
        have h4 : m c' ^ 2 ≤ 0 := by linarith
        nlinarith [sq_nonneg (m c')]
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨((m k, m c), c), ?_, ?_⟩)
      · simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase,
          Finset.mem_univ, and_true]
        exact ⟨⟨hmk1, hmc1⟩, hck⟩
      · funext c'
        by_cases h1 : c' = k
        · subst h1; simp [he, Pi.single_eq_of_ne (Ne.symm hck)]
        · by_cases h2 : c' = c
          · subst h2; simp [he, Pi.single_eq_of_ne h1]
          · simp [he, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, hrest c' h1 h2]
  -- the two families of bonds are disjoint and injectively parametrised
  have hdisj : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1 h2
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase,
      Finset.mem_univ, and_true] at hp
    have := congrFun hpm p.2
    simp [he, Pi.single_eq_of_ne hp.2] at this
    rcases hp.1.2 with h | h <;> rw [h] at this <;> norm_num at this
  have hinj₁ : Set.InjOn (fun t : ℤ ↦ t • e k) ↑({1, -1} : Finset ℤ) := by
    intro t _ t' _ h
    have := congrFun h k
    simpa [he] using this
  have hinj₂ : Set.InjOn (fun p : (ℤ × ℤ) × Fin d ↦ p.1.1 • e k + p.1.2 • e p.2)
      ↑((({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ)) ×ˢ Finset.univ.erase k) := by
    intro p hp p' hp' h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, and_true] at hp hp'
    have hk := congrFun h k
    have hc := congrFun h p.2
    simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hp.2), Pi.single_eq_of_ne (Ne.symm hp'.2), mul_one, mul_zero,
      add_zero] at hk
    simp only [he, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hp.2, mul_one, mul_zero, zero_add, Pi.single_apply] at hc
    have hne : p.1.2 ≠ 0 := by rcases hp.1.2 with h | h <;> rw [h] <;> norm_num
    by_cases hpp : p.2 = p'.2
    · rw [ite_eq_left hpp, mul_one] at hc
      exact Prod.ext (Prod.ext hk hc) hpp
    · rw [ite_eq_right hpp, mul_zero] at hc
      exact absurd hc hne
  -- assemble
  rw [tsum_eq_sum hsupp, Finset.sum_union hdisj, hF₁, hF₂, Finset.sum_image hinj₁,
    Finset.sum_image hinj₂, Finset.sum_product, Finset.sum_product]
  have hpair : ∀ f : ℤ → ℝ, ∑ t ∈ ({1, -1} : Finset ℤ), f t = f 1 + f (-1) := fun f ↦
    Finset.sum_pair (by norm_num)
  rw [hpair, hJA 1 (Or.inl rfl), hJA (-1) (Or.inr rfl), hwA 1 (Or.inl rfl),
    hwA (-1) (Or.inr rfl), hpair, hpair, hpair]
  have hB : ∀ (s t : ℤ), s = 1 ∨ s = -1 → t = 1 ∨ t = -1 →
      ∑ c ∈ Finset.univ.erase k, J (s • e k + t • e c) * crossingWeight N k q (s • e k + t • e c)
        = B * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * ∑ c ∈ Finset.univ.erase k, χ c := by
    intro s t hs ht
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    rw [hJB s t c hs ht (Finset.ne_of_mem_erase hc), hwB s t c hs ht (Finset.ne_of_mem_erase hc)]
    ring
  rw [hB 1 1 (Or.inl rfl) (Or.inl rfl), hB 1 (-1) (Or.inl rfl) (Or.inr rfl),
    hB (-1) 1 (Or.inr rfl) (Or.inl rfl), hB (-1) (-1) (Or.inr rfl) (Or.inr rfl)]
  ring

/-- **Georgii, Example (17.31): the crossing form of the `±1` patterns.**  For the next-nearest
neighbour coupling and the pattern `q_χ = ∏_{c ≠ k} χ_c^{i_c}`,

`⟨q_χ, M q_χ⟩ = 2 (2N)^{d-1} (A + 2B ∑_{c ≠ k} χ_c)`.

With `χ = 1` this is `2(2N)^{d-1}(A + 2(d-1)B)`, and with `χ = -1` it is
`2(2N)^{d-1}(A - 2(d-1)B)`. -/
theorem dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    {χ : Fin d → ℝ} (hχ : ∀ c, χ c = 1 ∨ χ c = -1) :
    transversePattern N k χ ⬝ᵥ crossingMatrix N J k *ᵥ transversePattern N k χ
      = 2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ) * (A + 2 * B * ∑ c ∈ Finset.univ.erase k, χ c) := by
  rw [dotProduct_crossingMatrix_mulVec_eq_tsum (summable_of_nextNearestNeighbour hJ0),
    tsum_mul_crossingWeight_transversePattern_nextNearestNeighbour hJ1 hJ2 hJ0 hχ]


/-- **Georgii, Example (17.31): `A ≥ 2(d-1)|B|` is *necessary* for nonnegative definiteness.**

The crossing form of the `±1` pattern `q_χ` is `2(2N)^{d-1}(A + 2B ∑_{c ≠ k} χ_c)`
(`dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour`), and nonnegative
definiteness relative to `r_k` makes the crossing matrix positive semidefinite
(`IsNonnegDefiniteAt.posSemidef_crossingMatrix`, the analytic core of (17.29)).  Taking `χ = 1`
and `χ = -1` gives `A + 2(d-1)B ≥ 0` and `A - 2(d-1)B ≥ 0`.

Together with `isNonnegDefiniteAt_of_nextNearestNeighbour` this is
`isNonnegDefiniteAt_nextNearestNeighbour_iff`.  Note that the argument is purely algebraic: it
does not go through the reflection form of any measure. -/
theorem le_of_isNonnegDefiniteAt_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    (hnd : IsNonnegDefiniteAt k J) :
    2 * ((d : ℝ) - 1) * |B| ≤ A := by
  classical
  have hd0 : 0 < d := k.pos
  have hcardR : ((Finset.univ.erase k).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hd0]
    simp
  have hpsd : (crossingMatrix 1 J k).PosSemidef :=
    hnd.posSemidef_crossingMatrix (summable_of_nextNearestNeighbour hJ0)
      (even_of_nextNearestNeighbour hJ1 hJ2 hJ0)
  have hform : ∀ χ : Fin d → ℝ, (∀ c, χ c = 1 ∨ χ c = -1) →
      0 ≤ 2 * (((2 * 1) ^ (d - 1) : ℕ) : ℝ)
        * (A + 2 * B * ∑ c ∈ Finset.univ.erase k, χ c) := by
    intro χ hχ
    rw [← dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour hJ1 hJ2 hJ0 hχ]
    simpa using hpsd.dotProduct_mulVec_nonneg (transversePattern 1 k χ)
  have hC : (0 : ℝ) < 2 * (((2 * 1) ^ (d - 1) : ℕ) : ℝ) := by positivity
  have h1 := hform (fun _ ↦ 1) fun _ ↦ Or.inl rfl
  have h2 := hform (fun _ ↦ -1) fun _ ↦ Or.inr rfl
  rw [Finset.sum_const, nsmul_eq_mul, hcardR] at h1 h2
  rcases le_or_gt 0 B with hB | hB
  · rw [abs_of_nonneg hB]; nlinarith
  · rw [abs_of_neg hB]; nlinarith

/-- **Georgii, Example (17.31), both directions.**  A next-nearest neighbour coupling
`J(i) = A` for `|i|² = 1`, `B` for `|i|² = 2`, `0` beyond, is nonnegative definite relative to
`r_k` **iff** `A ≥ 2(d-1)|B|`. -/
theorem isNonnegDefiniteAt_nextNearestNeighbour_iff {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) :
    IsNonnegDefiniteAt k J ↔ 2 * ((d : ℝ) - 1) * |B| ≤ A :=
  ⟨le_of_isNonnegDefiniteAt_nextNearestNeighbour hJ1 hJ2 hJ0,
    fun h ↦ isNonnegDefiniteAt_of_nextNearestNeighbour h hJ1 hJ2 hJ0⟩

/-- **Georgii, Example (17.31): the value of the reflection form at the `±1` patterns.**  For the
next-nearest neighbour coupling, the two-point a priori measure and the pattern `q_χ`,

`°Z_Λ^Φ °γ_Λ^Φ(f_χ f_χ^*) = 4 e^{S_χ} sinh[2 (2N)^{d-1} (A + 2B ∑_{c ≠ k} χ_c)]`,

with `S_χ = ∑_{i,j ∈ Λ_{+,k}} J_Λ(i-j) q_χ(i) q_χ(j)`.  Georgii's `f` is `χ = 1`; his `f̃`, read
with the alternation in the transverse directions, is `χ = -1`. -/
theorem integral_patternTest_transversePattern_mul_comp_nextNearestNeighbour {A B : ℝ}
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0)
    {χ : Fin d → ℝ} (hχ : ∀ c, χ c = 1 ∨ χ c = -1) :
    ∫ ω, patternTest N k (transversePattern N k χ) ω
          * patternTest N k (transversePattern N k χ) (ω ∘ torusReflAt N k)
        ∂(heisenbergPeriodicGibbs N 1 J twoPointMeasure)
      = 4 * Real.exp (∑ i ∈ torusPosAtFinset N k, ∑ j ∈ torusPosAtFinset N k,
            periodizedCoupling N J (i - j) * transversePattern N k χ i * transversePattern N k χ j)
        * Real.sinh (2 * (((2 * N) ^ (d - 1) : ℕ) : ℝ)
            * (A + 2 * B * ∑ c ∈ Finset.univ.erase k, χ c)) := by
  rw [integral_patternTest_mul_comp_heisenbergPeriodicGibbs (even_of_nextNearestNeighbour hJ1 hJ2 hJ0)
    (flipCoord_eq_of_nextNearestNeighbour hJ1 hJ2 hJ0) _ (transversePattern_eq_one_or hχ),
    dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour hJ1 hJ2 hJ0 hχ]

/-- **Georgii, Example (17.31), the necessity half.**  If `A < 2(d-1)|B|` then the Gibbs
distribution in the torus with periodic boundary condition of the next-nearest neighbour
Heisenberg potential, for the two-point a priori measure `λ = δ_1 + δ_{-1}`, is *not*
`r_k`-positive.  Together with `isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour`
this makes `A ≥ 2(d-1)|B|` necessary as well as sufficient.

The refuting pattern is Georgii's constant one, `χ = 1`, when `B < 0` (crossing form
`2(2N)^{d-1}(A + 2(d-1)B) < 0`), and the pattern alternating in every direction transverse to `k`,
`χ = -1`, when `B ≥ 0` (crossing form `2(2N)^{d-1}(A - 2(d-1)B) < 0`).  The second is what
Georgii's `f̃` must be read to be; see `integral_patternTest_neg_one_pow_mul_comp` for why the
alternation along `k` that he prints cannot work. -/
theorem not_isReflectionPositive_heisenbergPeriodicGibbs_nextNearestNeighbour {A B : ℝ}
    (hAB : A < 2 * ((d : ℝ) - 1) * |B|)
    (hJ1 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 1 → J m = A)
    (hJ2 : ∀ m : Fin d → ℤ, (∑ c, m c ^ 2) = 2 → J m = B)
    (hJ0 : ∀ m : Fin d → ℤ, 2 < (∑ c, m c ^ 2) → J m = 0) :
    ¬ IsReflectionPositive (torusPosAt N k) (siteEquiv (Fin 1 → ℝ) (torusReflAt N k))
      (heisenbergPeriodicGibbs N 1 J twoPointMeasure) := by
  have hd0 : 0 < d := k.pos
  have hcardR : ((Finset.univ.erase k).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hd0]
    simp
  have hpos : (0 : ℝ) < (((2 * N) ^ (d - 1) : ℕ) : ℝ) := by
    have : 0 < (2 * N) ^ (d - 1) := Nat.pow_pos (by have := NeZero.ne N; omega)
    exact_mod_cast this
  obtain ⟨χ, hχ, hneg⟩ : ∃ χ : Fin d → ℝ, (∀ c, χ c = 1 ∨ χ c = -1) ∧
      A + 2 * B * ∑ c ∈ Finset.univ.erase k, χ c < 0 := by
    rcases le_or_gt 0 B with hB | hB
    · refine ⟨fun _ ↦ -1, fun _ ↦ Or.inr rfl, ?_⟩
      rw [Finset.sum_const, nsmul_eq_mul, hcardR, abs_of_nonneg hB] at *
      linarith
    · refine ⟨fun _ ↦ 1, fun _ ↦ Or.inl rfl, ?_⟩
      rw [Finset.sum_const, nsmul_eq_mul, hcardR, abs_of_neg hB] at *
      linarith
  refine not_isReflectionPositive_heisenbergPeriodicGibbs_of_crossing_neg
    (even_of_nextNearestNeighbour hJ1 hJ2 hJ0) (flipCoord_eq_of_nextNearestNeighbour hJ1 hJ2 hJ0)
    (transversePattern N k χ) (transversePattern_eq_one_or hχ) ?_
  rw [dotProduct_transversePattern_crossingMatrix_nextNearestNeighbour hJ1 hJ2 hJ0 hχ]
  exact mul_neg_of_pos_of_neg (by positivity) hneg

/-! ### Invariance, normalisation, and the a priori bounds of Georgii §20.1

The hypotheses of the chessboard estimate (17.11) for the reflections `r_k` — `Λ`-periodicity,
`r_k`-invariance, `r_k`-positivity and `0 < °Z_Λ^Φ < ∞` — for the Heisenberg periodic Gibbs
distribution, together with the elementary bounds on the exponent (17.24) that Georgii uses in
the proofs of Lemmas (20.6) and (20.8).  Georgii's `‖J‖₀` of (20.2) is `∑' m, |J m|`. -/

section AprioriBounds

variable {ν : Measure (Fin n → ℝ)}

/-! #### Summing the periodised coupling over the torus -/

variable (N) in
/-- The fibres of the projection `ℤ^d → Λ` partition `ℤ^d`, so summing a fibrewise sum over the
torus recovers the sum over `ℤ^d`. -/
lemma sum_tsum_ite_torus {g : (Fin d → ℤ) → ℝ} (hg : Summable g) :
    ∑ z : Fin d → ZMod (2 * N), ∑' m : Fin d → ℤ,
        (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then g m else 0)
      = ∑' m : Fin d → ℤ, g m := by
  classical
  have hsummable : ∀ z : Fin d → ZMod (2 * N), Summable fun m : Fin d → ℤ ↦
      if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then g m else 0 := fun z ↦
    Summable.of_norm_bounded hg.abs fun m ↦ by
      by_cases h : (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z <;> simp [h]
  rw [← Summable.tsum_finsetSum fun z _ ↦ hsummable z]
  exact tsum_congr fun m ↦ by simp [Finset.sum_ite_eq]

/-- **`∑_{z ∈ Λ} J_Λ(z) = ∑_{m ∈ ℤ^d} J(m)`.** -/
lemma sum_periodizedCoupling (hsum : Summable J) :
    ∑ z : Fin d → ZMod (2 * N), periodizedCoupling N J z = ∑' m, J m := by
  simp only [periodizedCoupling_eq_tsum_ite]
  exact sum_tsum_ite_torus N hsum

/-- **`∑_{z ∈ Λ} |J_Λ(z)| ≤ ‖J‖₀`**, Georgii (20.2). -/
lemma sum_abs_periodizedCoupling_le (hsum : Summable J) :
    ∑ z : Fin d → ZMod (2 * N), |periodizedCoupling N J z| ≤ ∑' m, |J m| := by
  classical
  have habs : Summable fun m : Fin d → ℤ ↦ |J m| := hsum.abs
  have hstep : ∀ z : Fin d → ZMod (2 * N), |periodizedCoupling N J z|
      ≤ ∑' m : Fin d → ℤ, (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then |J m| else 0) := by
    intro z
    rw [periodizedCoupling_eq_tsum_ite, ← Real.norm_eq_abs]
    have hb : Summable fun m : Fin d → ℤ ↦
        ‖(if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then J m else 0)‖ :=
      Summable.of_norm_bounded habs fun m ↦ by
        by_cases h : (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z <;> simp [h]
    refine (norm_tsum_le_tsum_norm hb).trans (le_of_eq (tsum_congr fun m ↦ ?_))
    by_cases h : (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z <;> simp [h]
  calc ∑ z : Fin d → ZMod (2 * N), |periodizedCoupling N J z|
      ≤ ∑ z : Fin d → ZMod (2 * N), ∑' m : Fin d → ℤ,
          (if (fun c ↦ ((m c : ℤ) : ZMod (2 * N))) = z then |J m| else 0) :=
        Finset.sum_le_sum fun z _ ↦ hstep z
    _ = ∑' m, |J m| := sum_tsum_ite_torus N habs

/-- `∑_{j ∈ Λ} |J_Λ(i-j)| ≤ ‖J‖₀`: the row sums of the periodised coupling matrix. -/
lemma sum_abs_periodizedCoupling_sub_le (hsum : Summable J) (i : Fin d → ZMod (2 * N)) :
    ∑ j : Fin d → ZMod (2 * N), |periodizedCoupling N J (i - j)| ≤ ∑' m, |J m| := by
  have h : ∑ j : Fin d → ZMod (2 * N), |periodizedCoupling N J (i - j)|
      = ∑ z : Fin d → ZMod (2 * N), |periodizedCoupling N J z| :=
    Fintype.sum_equiv (Equiv.subLeft i) _ _ fun j ↦ by simp
  rw [h]
  exact sum_abs_periodizedCoupling_le hsum

/-- `∑_{i ∈ Λ} |J_Λ(i-j)| ≤ ‖J‖₀`: the column sums of the periodised coupling matrix. -/
lemma sum_abs_periodizedCoupling_sub_le' (hsum : Summable J) (j : Fin d → ZMod (2 * N)) :
    ∑ i : Fin d → ZMod (2 * N), |periodizedCoupling N J (i - j)| ≤ ∑' m, |J m| := by
  have h : ∑ i : Fin d → ZMod (2 * N), |periodizedCoupling N J (i - j)|
      = ∑ z : Fin d → ZMod (2 * N), |periodizedCoupling N J z| :=
    Fintype.sum_equiv (Equiv.subRight j) _ _ fun i ↦ by simp
  rw [h]
  exact sum_abs_periodizedCoupling_le hsum

/-- `∑_{j ∈ Λ} J_Λ(i-j) = ∑_{m ∈ ℤ^d} J(m)`. -/
lemma sum_periodizedCoupling_sub (hsum : Summable J) (i : Fin d → ZMod (2 * N)) :
    ∑ j : Fin d → ZMod (2 * N), periodizedCoupling N J (i - j) = ∑' m, J m := by
  have h : ∑ j : Fin d → ZMod (2 * N), periodizedCoupling N J (i - j)
      = ∑ z : Fin d → ZMod (2 * N), periodizedCoupling N J z :=
    Fintype.sum_equiv (Equiv.subLeft i) _ _ fun j ↦ by simp
  rw [h]
  exact sum_periodizedCoupling hsum

/-! #### Bounds on the exponent (17.24) -/

/-- **Georgii's estimate at the start of the proof of (20.6).**
`|½ ∑_{i,j ∈ Λ} J_Λ(i-j) σ_i·σ_j| ≤ ½ ‖J‖₀ ∑_{i ∈ Λ} |σ_i|²`, with `‖J‖₀ = ∑_m |J(m)|` the
norm (20.2).  (Georgii states it with `‖J‖₀` in place of `½‖J‖₀`, using
`|x·y| ≤ |x|² + |y|²` where the sharper `2|x·y| ≤ |x|² + |y|²` is available.) -/
lemma abs_heisenbergExponent_le (hsum : Summable J)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    |heisenbergExponent N n J ω| ≤ (∑' m, |J m|) / 2 * ∑ i, (ω i ⬝ᵥ ω i) := by
  classical
  set a : (Fin d → ZMod (2 * N)) → ℝ := fun i ↦ ω i ⬝ᵥ ω i with ha
  have hanonneg : ∀ i, 0 ≤ a i := fun i ↦ Matrix.dotProduct_self_nonneg _
  have hpt : ∀ i j, |periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)|
      ≤ |periodizedCoupling N J (i - j)| * a i / 2
        + |periodizedCoupling N J (i - j)| * a j / 2 := by
    intro i j
    rw [abs_mul]
    have h := Matrix.two_mul_abs_dotProduct_le (ω i) (ω j)
    have hc : (0 : ℝ) ≤ |periodizedCoupling N J (i - j)| := abs_nonneg _
    have hmul : |periodizedCoupling N J (i - j)| * |ω i ⬝ᵥ ω j|
        ≤ |periodizedCoupling N J (i - j)| * ((a i + a j) / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hc
      simp only [ha]
      linarith
    linarith
  have hrow : ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * a i / 2
      ≤ (∑' m, |J m|) * (∑ i, a i) / 2 := by
    have hstep : ∀ i : Fin d → ZMod (2 * N),
        ∑ j, |periodizedCoupling N J (i - j)| * a i / 2 ≤ (∑' m, |J m|) * a i / 2 := by
      intro i
      have : ∑ j, |periodizedCoupling N J (i - j)| * a i / 2
          = (∑ j, |periodizedCoupling N J (i - j)|) * a i / 2 := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [this]
      have := sum_abs_periodizedCoupling_sub_le hsum i
      have hai := hanonneg i
      nlinarith
    calc ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * a i / 2
        ≤ ∑ i, (∑' m, |J m|) * a i / 2 := Finset.sum_le_sum fun i _ ↦ hstep i
      _ = (∑' m, |J m|) * (∑ i, a i) / 2 := by
          rw [Finset.mul_sum, Finset.sum_div]
  have hcol : ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * a j / 2
      ≤ (∑' m, |J m|) * (∑ i, a i) / 2 := by
    rw [Finset.sum_comm]
    have hstep : ∀ j : Fin d → ZMod (2 * N),
        ∑ i, |periodizedCoupling N J (i - j)| * a j / 2 ≤ (∑' m, |J m|) * a j / 2 := by
      intro j
      have : ∑ i, |periodizedCoupling N J (i - j)| * a j / 2
          = (∑ i, |periodizedCoupling N J (i - j)|) * a j / 2 := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [this]
      have := sum_abs_periodizedCoupling_sub_le' hsum j
      have haj := hanonneg j
      nlinarith
    calc ∑ j, ∑ i, |periodizedCoupling N J (i - j)| * a j / 2
        ≤ ∑ j, (∑' m, |J m|) * a j / 2 := Finset.sum_le_sum fun j _ ↦ hstep j
      _ = (∑' m, |J m|) * (∑ i, a i) / 2 := by
          rw [Finset.mul_sum, Finset.sum_div]
  have hmain : |∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)|
      ≤ (∑' m, |J m|) * ∑ i, a i := by
    calc |∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)|
        ≤ ∑ i, |∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)| :=
          Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (|periodizedCoupling N J (i - j)| * a i / 2
            + |periodizedCoupling N J (i - j)| * a j / 2) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
      _ = (∑ i, ∑ j, |periodizedCoupling N J (i - j)| * a i / 2)
            + ∑ i, ∑ j, |periodizedCoupling N J (i - j)| * a j / 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_add_distrib
      _ ≤ (∑' m, |J m|) * ∑ i, a i := by linarith
  rw [heisenbergExponent, abs_div]
  rw [show |(2 : ℝ)| = 2 from abs_of_pos two_pos]
  linarith

/-- **The exponent (17.24) is at least `½ |Λ| u ∑_m J(m)`** on configurations whose spins have
pairwise scalar products at least `u`, when `J ≥ 0`.  This is the lower bound on `°Z_Λ^Φ` in the
proof of Georgii's Lemma (20.8). -/
lemma le_heisenbergExponent_of_le (hsum : Summable J) (hJ : ∀ m, 0 ≤ J m) {u : ℝ}
    {ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)} (hω : ∀ i j, u ≤ ω i ⬝ᵥ ω j) :
    ((2 * N) ^ d : ℕ) * (u * ∑' m, J m) / 2 ≤ heisenbergExponent N n J ω := by
  have hstep : ∀ i : Fin d → ZMod (2 * N),
      u * ∑' m, J m ≤ ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) := by
    intro i
    calc u * ∑' m, J m = ∑ j, periodizedCoupling N J (i - j) * u := by
          rw [← Finset.sum_mul, sum_periodizedCoupling_sub hsum i, mul_comm]
      _ ≤ ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) :=
          Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (hω i j) (periodizedCoupling_nonneg hJ _)
  have hsum' : ((2 * N) ^ d : ℕ) * (u * ∑' m, J m)
      ≤ ∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) := by
    calc ((2 * N) ^ d : ℕ) * (u * ∑' m, J m)
        = ∑ _i : Fin d → ZMod (2 * N), u * ∑' m, J m := by
          rw [Finset.sum_const, Finset.card_univ, card_pi_zmod, nsmul_eq_mul]
      _ ≤ ∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) :=
          Finset.sum_le_sum fun i _ ↦ hstep i
  rw [heisenbergExponent]
  linarith

/-- **The exponent (17.24) is at most `½ |Λ| v ∑_m J(m)`** on configurations whose spins have
pairwise scalar products at most `v`, when `J ≥ 0`.  This is the upper bound on the numerator in
the proof of Georgii's Lemma (20.8). -/
lemma heisenbergExponent_le_of_le (hsum : Summable J) (hJ : ∀ m, 0 ≤ J m) {v : ℝ}
    {ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)} (hω : ∀ i j, ω i ⬝ᵥ ω j ≤ v) :
    heisenbergExponent N n J ω ≤ ((2 * N) ^ d : ℕ) * (v * ∑' m, J m) / 2 := by
  have hstep : ∀ i : Fin d → ZMod (2 * N),
      ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j) ≤ v * ∑' m, J m := by
    intro i
    calc ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)
        ≤ ∑ j, periodizedCoupling N J (i - j) * v :=
          Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_left (hω i j) (periodizedCoupling_nonneg hJ _)
      _ = v * ∑' m, J m := by
          rw [← Finset.sum_mul, sum_periodizedCoupling_sub hsum i, mul_comm]
  have hsum' : ∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)
      ≤ ((2 * N) ^ d : ℕ) * (v * ∑' m, J m) := by
    calc ∑ i, ∑ j, periodizedCoupling N J (i - j) * (ω i ⬝ᵥ ω j)
        ≤ ∑ _i : Fin d → ZMod (2 * N), v * ∑' m, J m :=
          Finset.sum_le_sum fun i _ ↦ hstep i
      _ = ((2 * N) ^ d : ℕ) * (v * ∑' m, J m) := by
          rw [Finset.sum_const, Finset.card_univ, card_pi_zmod, nsmul_eq_mul]
  rw [heisenbergExponent]
  linarith


/-! #### `Λ`-periodicity, `r_k`-invariance and normalisation of `°γ_Λ^Φ` -/

lemma measurable_heisenbergDensity :
    Measurable fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω)) :=
  ENNReal.measurable_ofReal.comp measurable_heisenbergExponent.exp

/-- **The exponent (17.24) is shift invariant**: `J_Λ(i-j)` depends on the two sites only through
their difference. -/
lemma heisenbergExponent_shift (t : Fin d → ZMod (2 * N))
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergExponent N n J ((shift (Fin n → ℝ) t).toFun ω) = heisenbergExponent N n J ω := by
  simp only [heisenbergExponent, shift_toFun_apply]
  congr 1
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ fun i ↦ ?_
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ fun j ↦ ?_
  have h : i - j = (i - t) - (j - t) := by abel
  simp only [Equiv.subRight_apply]
  rw [h]

/-- **The exponent (17.24) is `r_k`-invariant** when `J` is invariant under the flip of the `k`-th
coordinate; by `IsNonnegDefiniteAt.flipCoord_eq` that is automatic under Georgii's hypothesis of
(17.29). -/
lemma heisenbergExponent_torusReflAt (hflip : ∀ m, J (flipCoord k m) = J m)
    (ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ)) :
    heisenbergExponent N n J ((siteEquiv (Fin n → ℝ) (torusReflAt N k)).toFun ω)
      = heisenbergExponent N n J ω := by
  simp only [heisenbergExponent, siteEquiv_torusReflAt_toFun, Function.comp_apply]
  congr 1
  refine Fintype.sum_equiv (torusReflAt N k) _ _ fun i ↦ ?_
  refine Fintype.sum_equiv (torusReflAt N k) _ _ fun j ↦ ?_
  rw [periodizedCoupling_torusReflAt_sub hflip]

/-- **Georgii, remark after (17.20): `°γ_Λ^Φ` is `Λ`-periodic.** -/
theorem measurePreserving_shift_heisenbergPeriodicGibbs (ν : Measure (Fin n → ℝ)) [SigmaFinite ν]
    (t : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift (Fin n → ℝ) t).toFun (heisenbergPeriodicGibbs N n J ν)
      (heisenbergPeriodicGibbs N n J ν) :=
  (measurePreserving_siteEquiv_pi (Equiv.addRight t) ν).withDensity_of_comp_eq
    measurable_heisenbergDensity fun ω ↦
      congrArg (fun x ↦ ENNReal.ofReal (Real.exp x)) (heisenbergExponent_shift t ω)

/-- **`°γ_Λ^Φ` is `r_k`-invariant**, the hypothesis that makes the Cauchy–Schwarz inequality
(17.8) — and hence the chessboard estimate (17.11) — available for it. -/
theorem measurePreserving_siteEquiv_torusReflAt_heisenbergPeriodicGibbs
    (hflip : ∀ m, J (flipCoord k m) = J m) (ν : Measure (Fin n → ℝ)) [SigmaFinite ν] :
    MeasurePreserving (siteEquiv (Fin n → ℝ) (torusReflAt N k)).toFun
      (heisenbergPeriodicGibbs N n J ν) (heisenbergPeriodicGibbs N n J ν) :=
  (measurePreserving_siteEquiv_pi (torusReflAt N k) ν).withDensity_of_comp_eq
    measurable_heisenbergDensity fun ω ↦
      congrArg (fun x ↦ ENNReal.ofReal (Real.exp x)) (heisenbergExponent_torusReflAt hflip ω)

/-- Georgii's `°Z_Λ^Φ < ∞`, his standing hypothesis in (17.24). -/
lemma isFiniteMeasure_heisenbergPeriodicGibbs
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsFiniteMeasure (heisenbergPeriodicGibbs N n J ν) :=
  isFiniteMeasure_withDensity
    (((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ ↦ (Real.exp_nonneg _))).1 hint.hasFiniteIntegral).ne)

omit [NeZero N] in
/-- The event that every spin lies in `A` is the cylinder `A^Λ`. -/
lemma forall_mem_eq_univ_pi (A : Set (Fin n → ℝ)) :
    {ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) | ∀ i, ω i ∈ A} = Set.univ.pi fun _ ↦ A := by
  ext ω; simp

lemma heisenbergPeriodicGibbs_apply {S : Set ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))}
    (hS : MeasurableSet S) :
    heisenbergPeriodicGibbs N n J ν S
      = ∫⁻ ω in S, ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) :=
  withDensity_apply _ hS

/-- **A uniform upper bound on the exponent bounds `°Z_Λ^Φ °γ_Λ^Φ(A^Λ)`.** -/
lemma heisenbergPeriodicGibbs_forall_mem_le [SigmaFinite ν] {A : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) {M : ℝ}
    (hM : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ), (∀ i, ω i ∈ A) →
      heisenbergExponent N n J ω ≤ M) :
    heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A}
      ≤ ENNReal.ofReal (Real.exp M) * ν A ^ ((2 * N) ^ d) := by
  rw [forall_mem_eq_univ_pi, heisenbergPeriodicGibbs_apply (MeasurableSet.univ_pi fun _ ↦ hA)]
  calc ∫⁻ ω in Set.univ.pi fun _ ↦ A, ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)
      ≤ ∫⁻ _ in Set.univ.pi fun _ ↦ A, ENNReal.ofReal (Real.exp M)
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
        refine setLIntegral_mono' (MeasurableSet.univ_pi fun _ ↦ hA) fun ω hω ↦ ?_
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hM ω (by simpa using hω)))
    _ = ENNReal.ofReal (Real.exp M)
          * (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) (Set.univ.pi fun _ ↦ A) :=
        setLIntegral_const _ _
    _ = ENNReal.ofReal (Real.exp M) * ν A ^ ((2 * N) ^ d) := by
        rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, card_pi_zmod]

/-- **A uniform lower bound on the exponent bounds `°Z_Λ^Φ` from below.** -/
lemma le_heisenbergPeriodicGibbs_univ [SigmaFinite ν] {U : Set (Fin n → ℝ)}
    (hU : MeasurableSet U) {M : ℝ}
    (hM : ∀ ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ), (∀ i, ω i ∈ U) →
      M ≤ heisenbergExponent N n J ω) :
    ENNReal.ofReal (Real.exp M) * ν U ^ ((2 * N) ^ d)
      ≤ heisenbergPeriodicGibbs N n J ν Set.univ := by
  rw [heisenbergPeriodicGibbs_apply MeasurableSet.univ, Measure.restrict_univ]
  calc ENNReal.ofReal (Real.exp M) * ν U ^ ((2 * N) ^ d)
      = ∫⁻ _ in Set.univ.pi fun _ ↦ U, ENNReal.ofReal (Real.exp M)
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
        rw [setLIntegral_const, Measure.pi_pi, Finset.prod_const, Finset.card_univ, card_pi_zmod]
    _ ≤ ∫⁻ ω in Set.univ.pi fun _ ↦ U,
          ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
        refine setLIntegral_mono' (MeasurableSet.univ_pi fun _ ↦ hU) fun ω hω ↦ ?_
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hM ω (by simpa using hω)))
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) :=
        setLIntegral_le_lintegral _ _

/-- **Georgii's product bound in the proof of (20.6).**  Since the exponent (17.24) is at most
`½‖J‖₀ ∑_i |σ_i|²`, the mass that `°Z_Λ^Φ °γ_Λ^Φ` gives to `A^Λ` is at most the `|Λ|`-th power of
the one-site integral `∫_A exp(½‖J‖₀ |x|²) λ(dx)`. -/
lemma heisenbergPeriodicGibbs_forall_mem_le_pow [SigmaFinite ν] (hsum : Summable J)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    heisenbergPeriodicGibbs N n J ν {ω | ∀ i, ω i ∈ A}
      ≤ (∫⁻ x in A, ENNReal.ofReal (Real.exp ((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) ∂ν)
          ^ ((2 * N) ^ d) := by
  have hg : Measurable fun x : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp ((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp ?_)
    exact (Finset.measurable_sum _ fun c _ ↦
      (measurable_pi_apply c).mul (measurable_pi_apply c)).const_mul _
  rw [forall_mem_eq_univ_pi, heisenbergPeriodicGibbs_apply (MeasurableSet.univ_pi fun _ ↦ hA),
    Measure.restrict_pi_pi]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν.restrict A)
      ≤ ∫⁻ ω, ∏ i, ENNReal.ofReal (Real.exp ((∑' m, |J m|) / 2 * (ω i ⬝ᵥ ω i)))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν.restrict A) := by
        refine lintegral_mono fun ω ↦ ?_
        rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_nonneg _), ← Real.exp_sum]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h := abs_heisenbergExponent_le hsum ω
        rw [← Finset.mul_sum]
        exact (le_abs_self _).trans h
    _ = ∏ _i : Fin d → ZMod (2 * N),
          ∫⁻ x, ENNReal.ofReal (Real.exp ((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) ∂(ν.restrict A) :=
        lintegral_pi_prod _ fun _ ↦ hg
    _ = (∫⁻ x in A, ENNReal.ofReal (Real.exp ((∑' m, |J m|) / 2 * (x ⬝ᵥ x))) ∂ν)
          ^ ((2 * N) ^ d) := by
        rw [Finset.prod_const, Finset.card_univ, card_pi_zmod]

/-- **Georgii's lower bound `°Z_Λ^Φ ≥ δ^{|Λ|}` in the proof of (20.6)**, with
`δ = ∫ exp(-½‖J‖₀ |x|²) λ(dx)`: the exponent (17.24) is at least `-½‖J‖₀ ∑_i |σ_i|²`. -/
lemma le_heisenbergPeriodicGibbs_univ_pow [SigmaFinite ν] (hsum : Summable J) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x)))) ∂ν) ^ ((2 * N) ^ d)
      ≤ heisenbergPeriodicGibbs N n J ν Set.univ := by
  have hg : Measurable fun x : Fin n → ℝ ↦
      ENNReal.ofReal (Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x)))) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp ?_)
    exact ((Finset.measurable_sum _ fun c _ ↦
      (measurable_pi_apply c).mul (measurable_pi_apply c)).const_mul _).neg
  rw [heisenbergPeriodicGibbs_apply MeasurableSet.univ, Measure.restrict_univ]
  calc (∫⁻ x, ENNReal.ofReal (Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x)))) ∂ν) ^ ((2 * N) ^ d)
      = ∏ _i : Fin d → ZMod (2 * N),
          ∫⁻ x, ENNReal.ofReal (Real.exp (-((∑' m, |J m|) / 2 * (x ⬝ᵥ x)))) ∂ν := by
        rw [Finset.prod_const, Finset.card_univ, card_pi_zmod]
    _ = ∫⁻ ω, ∏ i, ENNReal.ofReal (Real.exp (-((∑' m, |J m|) / 2 * (ω i ⬝ᵥ ω i))))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) :=
        (lintegral_pi_prod _ fun _ ↦ hg).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))
          ∂(Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν) := by
        refine lintegral_mono fun ω ↦ ?_
        rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_nonneg _), ← Real.exp_sum]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have h := abs_heisenbergExponent_le hsum ω
        have hneg : ∑ i, -((∑' m, |J m|) / 2 * (ω i ⬝ᵥ ω i))
            = -((∑' m, |J m|) / 2 * ∑ i, (ω i ⬝ᵥ ω i)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        rw [hneg]
        have := abs_le.1 h
        linarith [this.1]

/-- Georgii's `°Z_Λ^Φ > 0`: the a priori measure is nonzero and the density is everywhere
positive. -/
lemma heisenbergPeriodicGibbs_univ_pos [SigmaFinite ν] (hν : ν ≠ 0) :
    0 < heisenbergPeriodicGibbs N n J ν
      (Set.univ : Set ((Fin d → ZMod (2 * N)) → (Fin n → ℝ))) := by
  rw [heisenbergPeriodicGibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_pos_iff_support measurable_heisenbergDensity]
  have hsupp : Function.support (fun ω : (Fin d → ZMod (2 * N)) → (Fin n → ℝ) ↦
      ENNReal.ofReal (Real.exp (heisenbergExponent N n J ω))) = Set.univ :=
    Set.eq_univ_of_forall fun ω ↦ (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  rw [hsupp, Measure.pi_univ]
  exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦
    (Measure.measure_univ_pos.2 hν).ne')

/-- `°γ_Λ^Φ` is a probability measure as soon as `0 < °Z_Λ^Φ < ∞`. -/
theorem isProbabilityMeasure_heisenbergPeriodicGibbsDist [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hint : Integrable (fun ω ↦ Real.exp (heisenbergExponent N n J ω))
      (Measure.pi fun _ : Fin d → ZMod (2 * N) ↦ ν)) :
    IsProbabilityMeasure (heisenbergPeriodicGibbsDist N n J ν) := by
  have := isFiniteMeasure_heisenbergPeriodicGibbs (ν := ν) hint
  constructor
  rw [heisenbergPeriodicGibbsDist, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (heisenbergPeriodicGibbs_univ_pos hν).ne' (measure_ne_top _ _)

/-- `°γ_Λ^Φ` is `Λ`-periodic. -/
theorem measurePreserving_shift_heisenbergPeriodicGibbsDist (ν : Measure (Fin n → ℝ))
    [SigmaFinite ν] (t : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift (Fin n → ℝ) t).toFun (heisenbergPeriodicGibbsDist N n J ν)
      (heisenbergPeriodicGibbsDist N n J ν) := by
  rw [heisenbergPeriodicGibbsDist]
  exact (measurePreserving_shift_heisenbergPeriodicGibbs ν t).smul_measure _

/-- `°γ_Λ^Φ` is `r_k`-invariant. -/
theorem measurePreserving_siteEquiv_torusReflAt_heisenbergPeriodicGibbsDist
    (hflip : ∀ m, J (flipCoord k m) = J m) (ν : Measure (Fin n → ℝ)) [SigmaFinite ν] :
    MeasurePreserving (siteEquiv (Fin n → ℝ) (torusReflAt N k)).toFun
      (heisenbergPeriodicGibbsDist N n J ν) (heisenbergPeriodicGibbsDist N n J ν) := by
  rw [heisenbergPeriodicGibbsDist]
  exact (measurePreserving_siteEquiv_torusReflAt_heisenbergPeriodicGibbs hflip ν).smul_measure _

end AprioriBounds

end Heisenberg

end MeasureTheory.GibbsMeasure

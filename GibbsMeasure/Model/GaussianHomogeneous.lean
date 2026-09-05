/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianGibbs
public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiHerglotz
public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiMeasure
public import GibbsMeasure.Mathlib.Analysis.Fourier.AddCircleMultiSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Georgii §13.3: the homogeneous case

Georgii's §13.3 specialises §13.2 to `S = ℤ^d` and to *homogeneous* data: `J(i,j) = J'(j - i)` for
an even `J' : S → ℝ` and `h_j = h'` a constant. (Georgii writes `J(i,j) = J'(i-j)`; for the even
`J'` he assumes throughout, the two readings agree.) Nothing in the elementary part of the section
uses the lattice structure of `ℤ^d` beyond the group law, so everything here is stated for an
arbitrary countable abelian group `S` (`ℤ^d` is the instance Georgii cares about); the
`[LinearOrder S]` assumption is only the one already required to form
`Potential.gaussianSpecification`, and is unrelated to the group structure.

Two hypotheses are carried throughout that Georgii does not state in §13.3, because
`Potential.gaussianSpecification` needs them to *exist*: `J` has **finite range**
(`hFin : {n | J' n ≠ 0}.Finite`) and every `𝒥_Λ` is positive definite (`hPD`). Georgii assumes only
absolute summability (13.34) in Theorems (13.36), (13.40)–(13.42); finite range enters because the
proof of Theorem (13.22) in `GibbsMeasure/Model/GaussianGibbs.lean` is run for finite range only,
where Georgii's Corollary (13.A6) is not needed. Every statement below that mentions `γ^{J,h}`
therefore has `hFin` among its hypotheses, and Georgii's examples (13.43) do have finite range.

## Main definitions

* `Potential.homogeneousCoupling J'`: **Georgii's homogeneous `J`**, `J(i,j) = J'(j - i)`.
* `Potential.fourierHomogeneousCoupling J'`: **Georgii's Fourier transform (13.35)**,
  `Ĵ(z) = ∑_{n ∈ ℤ^d} z^n J(n)`, a continuous function on the dual group `G = K^d`. Its value at
  the identity, `Ĵ(1) = ∑_n J(n)`, is the plain `tsum ∑' k, J' k`, and the elementary part of the
  section — which needs only that value — is stated on an arbitrary countable abelian group,
  without reference to `Ĵ`.
* `Potential.spectralCovariance J'`: **Georgii (13.37)**, `C(i,j) = ∫_G z^{j-i} Ĵ(z)⁻¹ dz`.
* `Potential.harmonicCrystalCoupling d β`: **Georgii Example (13.43)**, `J(0) = β`,
  `J(±e_ℓ) = -β/(2d)`, `J = 0` otherwise.

## Main results

### Elementary part, on an arbitrary countable abelian group

* `Potential.symm_homogeneousCoupling`, `Potential.finite_setOf_homogeneousCoupling_ne_zero`: an
  even `J'` gives a symmetric `J`, and a finitely supported `J'` gives a `J` of finite row support
  — the two standing hypotheses of `Potential.gaussianSpecification`.
* `Potential.const_mem_gaussianMeanSet_iff`: **the constants in `M_{J,h}`.** For `J'` absolutely
  summable (Georgii (13.34)) and `h ≡ h'`, the constant configuration `ω ≡ c` lies in `M_{J,h}` if
  and only if `h' + Ĵ(1) c = 0`. This is the computation behind Georgii's two remarks in the
  discussion following Corollary (13.40): "if `Ĵ(1) ≠ 0` then `M_{J,h}` contains a constant
  element, namely `m = (-h/Ĵ(1))_{i ∈ S}`" (`Potential.const_mem_gaussianMeanSet_of_tsum_ne_zero`,
  `Potential.nonempty_gaussianMeanSet_of_tsum_ne_zero`) and "if `h ≠ 0` and `Ĵ(1) = 0` then
  `M_{J,h}` cannot contain a constant element"
  (`Potential.not_const_mem_gaussianMeanSet_of_tsum_eq_zero`).
* `Potential.const_mem_gaussianMeanSubmodule_of_tsum_eq_zero`: if `Ĵ(1) = ∑_{i ∈ S} J(i) = 0` then
  **all** constant configurations lie in `M_{J,0}`. This is the hypothesis Georgii verifies in
  Examples (13.29), (13.30) and (13.43) (`∑_j J(i,j) = 0`) before invoking Remark (13.23).
* `Potential.isInvariant_spinTranslation_const_of_tsum_eq_zero` and
  `Potential.map_add_const_isGibbsMeasure_of_tsum_eq_zero`: **the continuous symmetry
  `ω ↦ (ω_i + t)_{i ∈ S}` of `γ^{J,h}`** when `Ĵ(1) = 0`, and the resulting invariance of
  `𝒢(γ^{J,h})`. This is Georgii's "`γ^{J,h}` exhibits the continuous symmetry
  `ω → (ω_i + t)_{i ∈ S}`" in Examples (13.29), (13.30) and (13.43), obtained from Remark
  (13.23)(c) (`Potential.isInvariant_spinTranslation_gaussianSpecification`).
* `Potential.nonempty_G_homogeneousCoupling_of_bddAbove`: Georgii Theorem (13.26) in the
  homogeneous finite-range case — if `Ĵ(1) ≠ 0` (so `M_{J,h} ≠ ∅`) and `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞`,
  then `𝒢(γ^{J,h}) ≠ ∅`.

### Fourier analysis on `S = ℤ^d`

The dual group `G = K^d` is Mathlib's `UnitAddTorus d = d → ℝ/ℤ`, Georgii's character `z^n` is
`UnitAddTorus.mFourier n z = exp(2πi ⟨n, z⟩)`, and `dz` is `volume`. The Fourier theory of the
`d`-dimensional torus used here — the monomials, their orthonormality, Stone–Weierstrass, the
Fourier coefficients — is Mathlib's `Mathlib/Analysis/Fourier/AddCircleMulti.lean`, extended in
`GibbsMeasure/Mathlib/Analysis/Fourier/AddCircleMultiSeries.lean` by the facts about
absolutely summable trigonometric series and Toeplitz forms that Georgii's arguments need.

* `Potential.fourierHomogeneousCoupling`: **Georgii (13.35)**, `Ĵ(z) = ∑_{n ∈ ℤ^d} z^n J(n)`,
  with its continuity, reality for even `J`, value `Ĵ(1) = ∑_n J(n)`
  (`Potential.fourierHomogeneousCoupling_zero`), and Fourier coefficients
  (`Potential.mFourierCoeff_fourierHomogeneousCoupling`).
* `Potential.dotProduct_gaussianCouplingMatrix_homogeneousCoupling_mulVec` and
  `Potential.sum_sum_conj_mul_homogeneousCoupling`: **Georgii's identity in the proof of
  (13.A8)**, `∑_{i,j} u_i J(i-j) ū_j = ∫_G |∑_j u_j z^j|² Ĵ(z) dz`, for real and for complex `u`.
* `Potential.posSemidef_gaussianCouplingMatrix_homogeneousCoupling`,
  `Potential.re_fourierHomogeneousCoupling_nonneg_of_posSemidef` and
  `Potential.posSemidef_gaussianCouplingMatrix_homogeneousCoupling_iff`: **Georgii Proposition
  (13.A8)** for nonnegative definiteness — every `𝒥_Λ` is nonnegative definite **iff** `Ĵ ≥ 0`.
  The converse is Georgii's Stone–Weierstrass argument, run on the negative part `Ĵ⁻`.
* `Potential.posDef_gaussianCouplingMatrix_homogeneousCoupling` and
  `Potential.posDef_gaussianCouplingMatrix_homogeneousCoupling_iff`: **Georgii Proposition (13.A8)
  as he states it** — `J` is positive definite **iff** `Ĵ ≥ 0` and `Ĵ` is not identically zero.
  Georgii's step "`|g|²` can only vanish on a null set" is
  `UnitAddTorus.sum_mul_mFourier_eq_zero_of_eqOn_zero` in
  `GibbsMeasure/Mathlib/Analysis/Fourier/AddCircleMultiSeries.lean`: a trigonometric polynomial
  vanishing on a non-empty open subset of `G` vanishes identically, because read on `ℝ^d` through
  `p ↦ (p_ℓ mod 1)_ℓ` it is a real-analytic function on a connected space.
  `Potential.posDef_gaussianCouplingMatrix_homogeneousCoupling_of_lintegral_inv_ne_top` is the
  form used in Theorem (13.36), where `∫_G Ĵ⁻¹ dz < ∞` supplies `Ĵ ≠ 0` almost everywhere.
* `Potential.spectralCovariance`: **Georgii (13.37)**, `C(i,j) = ∫_G z^{j-i} Ĵ(z)⁻¹ dz`; it is
  symmetric (`Potential.spectralCovariance_symm`), nonnegative definite
  (`Potential.posSemidef_covMatrix_spectralCovariance`) and inverts `J`,
  `∑_j J(j-i) C(j,k) = δ_{ik}` (`Potential.tsum_homogeneousCoupling_mul_spectralCovariance`).
* `Potential.isGibbsMeasure_map_add_gaussianField_spectralCovariance` and
  `Potential.nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top`: **Georgii Theorem (13.36),
  the sufficiency half**, with Georgii's witness: if `Ĵ ≥ 0`, `∫_G Ĵ(z)⁻¹ dz < ∞` and
  `M_{J,h} ≠ ∅`, then `μ_C * δ_m ∈ 𝒢(γ^{J,h})` for every `m ∈ M_{J,h}`, where `μ_C` is the
  centred Gauss field with the covariance (13.37).
* `Potential.two_mul_sub_dotProduct_gaussianCouplingMatrix_le_integral_inv`,
  `Potential.gaussianCovEntry_le_integral_inv` and
  `Potential.bddAbove_gaussianCovEntry_of_lintegral_inv_ne_top`: **Georgii's condition (13.27) in
  spectral form.** Completing the square in the Fourier picture,
  `2 x_i - ∑_{j,k ∈ Λ} x_j J(j-k) x_k = ∫_G Ĵ⁻¹ - ∫_G |∑_j x_j z^j - z^i Ĵ⁻¹|² Ĵ ≤ ∫_G Ĵ⁻¹`, and
  the left-hand side has supremum `𝒥_Λ⁻¹(i,i)`
  (`MeasureTheory.GibbsMeasure.exists_dotProduct_mulVec_eq_gaussianCovEntry`); hence
  `sup_Λ 𝒥_Λ⁻¹(i,i) ≤ ∫_G Ĵ(z)⁻¹ dz`, so spectral integrability implies (13.27).
* `Potential.re_mFourier_mem_gaussianMeanSubmodule`, `Potential.re_mFourier_ne_zero`,
  `Potential.abs_re_mFourier_le_one` and
  `Potential.isInvariant_spinTranslation_re_mFourier`: **Georgii's Step 2 in the proof of Remark
  (13.39)**, in the form used by Corollary (13.40) and by the discussion preceding Corollary
  (13.41): a root `z ∈ G` of `Ĵ` gives the bounded non-zero element `m = (Re z^i)_{i ∈ S}` of
  `M_{J,0}`, hence a continuous symmetry `(τ^{t m})_{t ∈ ℝ}` of `γ^{J,h}`.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_pos` and
  `Potential.nonempty_G_homogeneousCoupling_of_pos`: **Georgii's remark preceding Corollary
  (13.40)** — if `Ĵ` has no root in `G` then `Ĵ⁻¹` is bounded, hence integrable, and
  `𝒢(γ^{J,h}) ≠ ∅` for every constant `h`.

### Georgii Corollary (13.42): the spectral description of the Gaussian Gibbs measures

* `Potential.spectralCovarianceOfMeasure`: **Georgii (13.38)**, the covariance function
  `C(i,j) = ∫_G z^{j-i} α(dz)` of the centred Gauss field with spectral measure `α`; it is
  symmetric and nonnegative definite (`Potential.posSemidef_covMatrix_spectralCovarianceOfMeasure`).
* `Potential.spectralMeasure`: Georgii's measure `Ĵ(z)⁻¹ dz` with his convention `1/0 = ∞`;
  `Potential.spectralCovariance_eq_spectralCovarianceOfMeasure` identifies (13.37) with (13.38)
  at `α = Ĵ⁻¹ dz`.
* `Potential.tsum_homogeneousCoupling_mul_spectralCovarianceOfMeasure`:
  `∑_j J(j-i) C(j,k) = ∫_G Ĵ(z) Re z^{k-i} α(dz)`, the computation behind (13.42).
* `Potential.withDensity_ofReal_re_fourier_eq_volume_iff` and
  `Potential.withDensity_ofReal_re_fourier_eq_volume_iff_exists`: for a finite `α` invariant under
  `z ↦ -z`, the covariance (13.38) inverts `J` in the sense of Theorem (13.22) **iff**
  `Ĵ(z) α(dz) = dz`, **iff** `α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`.
* `Potential.isGibbsMeasure_gaussianField_spectralCovarianceOfMeasure_iff`: **Corollary (13.42)**
  for the Gauss field attached to a given spectral measure, and
  `Potential.isGibbsMeasure_iff_exists_spectralMeasure_decomposition`: **Corollary (13.42) as
  Georgii states it**, for an arbitrary centred Gauss field with homogeneous covariance, the
  spectral measure being supplied by Herglotz's lemma.
* `Potential.exists_spectralCovarianceOfMeasure_eq`: **Proposition (13.A9)** in the homogeneous
  setting — every nonnegative definite `c : ℤ^d → ℝ` is `n ↦ ∫_G z^n α(dz)` for a finite `α` on
  `G`, necessarily invariant under `z ↦ -z`. The general statement is
  `UnitAddTorus.exists_isFiniteMeasure_integral_mFourier_eq` in
  `GibbsMeasure/Mathlib/Analysis/Fourier/AddCircleMultiHerglotz.lean`, and the uniqueness of `α`
  — which Georgii also asserts — is `UnitAddTorus.ext_of_integral_mFourier_eq` in
  `GibbsMeasure/Mathlib/Analysis/Fourier/AddCircleMultiMeasure.lean`.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_isGibbsMeasure`: **the
  necessity half of Theorem (13.36) for Gaussian Gibbs measures** — if a centred Gauss field with
  homogeneous covariance is a Gibbs measure for `γ^{J,0}` then `∫_G Ĵ(z)⁻¹ dz < ∞`, because its
  spectral measure dominates `Ĵ⁻¹ dz` and is finite.
* `Potential.not_countable_gaussianMeanSet_zero_homogeneousCoupling` and
  `Potential.not_countable_gaussianMeanSet_homogeneousCoupling`: **Georgii's conclusion in Remark
  (13.39)** — a root of `Ĵ` on `G` makes `M_{J,0}`, and every non-empty `M_{J,h}`, uncountable.

### Georgii Example (13.43): the harmonic crystal

* `Potential.harmonicCrystalCoupling`: `J(0) = β`, `J(±e_ℓ) = -β/(2d)`, `J = 0` otherwise, with
  its evenness, finite range, summability, transform
  `Re Ĵ(z_p) = (β/d) ∑_ℓ (1 - cos 2π p_ℓ) ≥ 0` and `Ĵ(1) = ∑_n J(n) = 0`. (Georgii's displayed
  `J̃(p) = 2β ∑_ℓ (1 - cos π p_ℓ)` is `2d` times the transform of the `J` he has just written
  down; the value computed here is the one his own `J` has, in Mathlib's normalisation
  `z_p = (e^{2πi p_1}, …)` of the torus, i.e. at `p_Georgii = 2p`. The factor is harmless: only
  the positivity and the order of vanishing at `p = 0` are used.)
* `Potential.posDef_gaussianCouplingMatrix_harmonicCrystalCoupling`: by (13.A8), `𝒥_Λ` is
  positive definite **in every dimension** (`Ĵ ≥ 0` and `Ĵ(-1, …, -1) = 2β ≠ 0`), so `γ^{J,0}` is
  defined also for `d ≤ 2`, where Georgii asserts `𝒢(γ^{J,0}) = ∅`.
* `Potential.isInvariant_spinTranslation_const_harmonicCrystalCoupling`: the continuous symmetry
  `ω ↦ (ω_i + t)_{i ∈ S}`, from `Ĵ(1) = 0`.
* `Potential.mul_sq_norm_le_re_fourierHomogeneousCoupling_harmonicCrystalCoupling`: Georgii's
  estimate `Ĵ(z_p) ≥ (8β/d)|p|²` on the fundamental cube — his `4β|p|²` up to the same two
  factors — from Jordan's inequality.
* `Potential.lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_top` and
  `Potential.nonempty_G_harmonicCrystalCoupling`: for `d ≥ 3`, `∫_G Ĵ(z)⁻¹ dz < ∞` — because
  `|p|^{-2}` is integrable on a ball of `ℝ^d` when `d > 2` — hence `𝒢(γ^{J,0}) ≠ ∅`: a set of
  Gibbs measures permuted by the continuous symmetry.

## What is *not* proved here, and why

* **Theorem (13.36), the necessity half for a general Gibbs measure** (`𝒢(γ^{J,h}) ≠ ∅` implies
  `M_{J,h} ≠ ∅` and `∫_G Ĵ⁻¹ dz < ∞`), and with it the descriptions of `𝒢(γ^{J,h})` and
  `𝒢_Θ(γ^{J,h})` as `{μ_C * ν}`. Georgii's Step 2 uses Theorem (13.24) — the identification of
  `ex 𝒢(γ^{J,h})`, which is open in `GibbsMeasure/Model/GaussianGibbs.lean` because it needs
  Theorem (7.12) and Proposition (13.A5). What (13.A9) *does* give without (13.24) is the
  necessity of `∫_G Ĵ⁻¹ dz < ∞` for a **Gaussian** Gibbs measure with homogeneous covariance,
  proved above as
  `Potential.lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_isGibbsMeasure`. The
  convolution representation `𝒢(γ^{J,h}) = {μ_C * ν}` genuinely needs (13.24) and is open.
* **Remark (13.39)**: part 1 (finite range implies `M_{J,h} ≠ ∅`, via a non-vanishing partial
  derivative of the real-analytic `p ↦ Ĵ(z_p)` at the origin) and part 2 (a root of the Laurent
  polynomial `Ĵ` in `(ℂ ∖ {0})^d`, by the fundamental theorem of algebra) both need analytic
  input about `Ĵ` off the torus. What Georgii actually uses downstream — a root *on* `G` gives a
  bounded non-zero element of `M_{J,0}`, hence an uncountable `M_{J,h}` — is proved, as
  `Potential.re_mFourier_mem_gaussianMeanSubmodule` and
  `Potential.not_countable_gaussianMeanSet_homogeneousCoupling`.
* **Corollary (13.40)**: the extremality half needs Corollary (7.4) and Corollary (7.28) for the
  transported measures `φ(α)` on `M_{J,0}`, and the uniqueness half is the necessity of (13.36).
  The two remarks Georgii appends to it — `{μ ∈ 𝒢(γ^{J,0}) : sup_i μ(|σ_i|) < ∞} = {μ_C}` when
  `Ĵ` has no root, and `𝒢(γ^{J,0}) = {μ_C}` for `J(i) ∼ c|i|^{-a}` — rest on Wiener's `1/f`
  theorem and on Dobrushin (1980), which Georgii quotes rather than proves; neither the Banach
  algebra input nor the conclusions are in the tree. What *is* proved of the discussion preceding
  (13.40) is `Ĵ > 0 ⟹ Ĵ⁻¹ bounded ⟹ 𝒢(γ^{J,h}) ≠ ∅`
  (`Potential.nonempty_G_homogeneousCoupling_of_pos`) and the two statements about constant
  elements of `M_{J,h}`; the third one — if `h ≠ 0` and `Ĵ(1) = 0` then `𝒢_Θ(γ^{J,h})` contains
  no `μ` with `μ(|σ_0|) < ∞` — needs the shift-invariance of `μ` and is not proved.
* **Corollary (13.41)** and hence `𝒢(γ^{J,h}) = ∅` for the harmonic crystal in `d ≤ 2`. Two
  separate things are missing. (i) The analytic content of (13.41) is `∫_G Ĵ⁻¹ dz = ∞`; for the
  harmonic crystal this is `Ĵ(z_p) ≤ 2π²β |p|²` together with the divergence of `∫ |p|^{-2} dp`
  on a cube of `ℝ^d` for `d ≤ 2` — Mathlib has the convergent half
  (`integrableOn_ball_of_norm_le_rpow`, used above for `d ≥ 3`) but not the divergent one, and
  the general `J` of (13.41) needs in addition Georgii's `grad Ĵ(q) = 0` argument. (ii) The step
  from `∫_G Ĵ⁻¹ dz = ∞` to `𝒢 = ∅` is exactly the necessity half of (13.36), which is open; what
  (i) *would* give at once, through
  `Potential.lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_isGibbsMeasure`, is that no
  centred Gauss field with homogeneous covariance is a Gibbs measure for `γ^{J,0}`.
  Georgii's alternative route — Corollary (9.24)
  applied to the dissipative symmetry `(τ^{t m})`, which *is* in the tree as
  `MeasureTheory.GibbsMeasure.G_eq_empty_of_logDecay_of_dissipative` — is stated for the Gibbs
  specification of a pair potential relative to a `σ`-finite a priori measure, and the
  identification of `γ^{J,0}` with such a specification (Georgii's Proposition (13.13) in its
  density form, `ρ_Λ = Z_Λ^{-1} exp[-(β/2d) ∑_{|i-j|=1} (ω_i - ω_j)²]`) is not in the tree.
* **The `Θ`-decoration of Corollary (13.42)**. The corollary itself is proved above, in the form
  `μ ∈ 𝒢(γ^{J,0}) ↔ α = Ĵ⁻¹ dz + α₀`; Georgii states it for `𝒢_Θ(γ^{J,0})`, and the missing step
  is only that a centred Gauss field with homogeneous covariance is shift-invariant (Georgii's
  "recall that a centred Gauss field is shift-invariant iff its covariance function is
  homogeneous"). That is a statement about the *measure* alone, independent of `γ`: it needs the
  pushforward of `ProbabilityTheory.gaussianField` along a coordinate reindexing, which is not in
  the tree, and `MeasureTheory.GibbsMeasure.invariantG` is therefore not mentioned in this file.
  Since `𝒢_Θ ⊆ 𝒢`, the "only if" half of Georgii's (13.42) is subsumed by what is proved here.
* **Examples (13.44), (13.45)** (long-range `J(i) = -β|i|^{-a}` in `d = 1` and `d = 2`): only the
  positivity and integrability estimates would be new relative to (13.43), but they are genuinely
  different computations and are not attempted here.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Function MeasureTheory ProbabilityTheory Matrix Set

noncomputable section

namespace Potential

variable {S : Type*} [AddCommGroup S]

/-- **Georgii §13.3: the homogeneous coupling.** `J(i,j) = J'(j - i)` for `J' : S → ℝ`. Georgii
writes `J` for both; here the one-argument function keeps its own name. -/
def homogeneousCoupling (J' : S → ℝ) : S → S → ℝ := fun i j ↦ J' (j - i)

@[simp] lemma homogeneousCoupling_apply (J' : S → ℝ) (i j : S) :
    homogeneousCoupling J' i j = J' (j - i) := rfl

/-- An even `J'` gives a symmetric coupling — the hypothesis `hSymm` of
`Potential.gaussianSpecification`. -/
lemma symm_homogeneousCoupling {J' : S → ℝ} (hEven : ∀ k : S, J' (-k) = J' k) (i j : S) :
    homogeneousCoupling J' i j = homogeneousCoupling J' j i := by
  simp only [homogeneousCoupling]
  rw [← hEven (j - i), neg_sub]

/-- A finitely supported `J'` gives a coupling of finite row support — the hypothesis `hFin` of
`Potential.gaussianSpecification`, i.e. Georgii's finite range. -/
lemma finite_setOf_homogeneousCoupling_ne_zero {J' : S → ℝ} (hFin : {k : S | J' k ≠ 0}.Finite)
    (i : S) : {j : S | homogeneousCoupling J' i j ≠ 0}.Finite := by
  have hpre : {j : S | homogeneousCoupling J' i j ≠ 0}
      = (fun j : S ↦ j - i) ⁻¹' {k : S | J' k ≠ 0} := rfl
  rw [hpre]
  have hinj : Function.Injective (fun j : S ↦ j - i) := fun a b hab ↦ by
    simpa [sub_left_inj] using hab
  exact hFin.preimage hinj.injOn

/-! ### Constant configurations and `M_{J,h}` -/

section Constants

variable {J' : S → ℝ}

/-- Reindexing `j ↦ j - i` turns the `i`-th row sum of a homogeneous coupling against a constant
configuration into `Ĵ(1) c = (∑_{k ∈ S} J'(k)) c`. -/
lemma tsum_homogeneousCoupling_const (c : ℝ) (i : S) :
    ∑' j : S, homogeneousCoupling J' i j * c = (∑' k : S, J' k) * c := by
  have := (Equiv.subRight i).tsum_eq (fun k : S ↦ J' k * c)
  simpa [homogeneousCoupling, tsum_mul_right] using this

/-- A constant configuration lies in `Ω_J` as soon as `J'` is absolutely summable (Georgii
(13.34)). -/
lemma const_mem_gaussianConvergenceSet (hJ' : Summable fun k : S ↦ |J' k|) (c : ℝ) :
    (fun _ : S ↦ c) ∈ gaussianConvergenceSet (homogeneousCoupling J') := by
  intro i
  have hre := (Equiv.subRight i).summable_iff (f := fun k : S ↦ |J' k| * |c|)
  have : (fun j : S ↦ |homogeneousCoupling J' i j * c|)
      = fun j : S ↦ |J' ((Equiv.subRight i) j)| * |c| := by
    funext j
    simp [homogeneousCoupling, abs_mul]
  rw [this]
  exact hre.2 (hJ'.mul_right _)

/-- **The constants in `M_{J,h}` for homogeneous data.** For `J'` absolutely summable and the
constant external field `h ≡ h'`, the constant configuration `ω ≡ c` lies in `M_{J,h}` if and only
if `h' + Ĵ(1) c = 0`, where `Ĵ(1) = ∑_{k ∈ S} J'(k)` is the Fourier transform (13.35) at `z = 1`.
-/
theorem const_mem_gaussianMeanSet_iff (hJ' : Summable fun k : S ↦ |J' k|) (h' c : ℝ) :
    (fun _ : S ↦ c) ∈ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h')
      ↔ h' + (∑' k : S, J' k) * c = 0 := by
  classical
  refine ⟨fun hm ↦ ?_, fun hc ↦ ⟨const_mem_gaussianConvergenceSet hJ' c, fun i ↦ ?_⟩⟩
  · obtain ⟨i⟩ : Nonempty S := ⟨0⟩
    have := hm.2 i
    rwa [tsum_homogeneousCoupling_const c i] at this
  · rw [tsum_homogeneousCoupling_const c i]
    exact hc

/-- **Georgii's remark preceding Corollary (13.40)**: if `Ĵ(1) ≠ 0` then `M_{J,h}` contains the
constant element `m = (-h'/Ĵ(1))_{i ∈ S}`. -/
theorem const_mem_gaussianMeanSet_of_tsum_ne_zero (hJ' : Summable fun k : S ↦ |J' k|)
    (hne : (∑' k : S, J' k) ≠ 0) (h' : ℝ) :
    (fun _ : S ↦ -h' / ∑' k : S, J' k)
      ∈ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h') := by
  rw [const_mem_gaussianMeanSet_iff hJ']
  field_simp
  ring

/-- `M_{J,h} ≠ ∅` for homogeneous data with `Ĵ(1) ≠ 0`. -/
theorem nonempty_gaussianMeanSet_of_tsum_ne_zero (hJ' : Summable fun k : S ↦ |J' k|)
    (hne : (∑' k : S, J' k) ≠ 0) (h' : ℝ) :
    (gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h')).Nonempty :=
  ⟨_, const_mem_gaussianMeanSet_of_tsum_ne_zero hJ' hne h'⟩

/-- **Georgii's hypothesis in Examples (13.29), (13.30) and (13.43)**: if `Ĵ(1) = ∑_{k ∈ S} J'(k)`
vanishes then *every* constant configuration lies in `M_{J,0}`. -/
theorem const_mem_gaussianMeanSubmodule_of_tsum_eq_zero (hJ' : Summable fun k : S ↦ |J' k|)
    (hzero : (∑' k : S, J' k) = 0) (c : ℝ) :
    (fun _ : S ↦ c) ∈ gaussianMeanSubmodule (homogeneousCoupling J') := by
  rw [mem_gaussianMeanSubmodule_iff]
  exact (const_mem_gaussianMeanSet_iff (J' := J') hJ' 0 c).2 (by rw [hzero]; ring)

/-- **Georgii's remark preceding Corollary (13.40)**: if `h' ≠ 0` and `Ĵ(1) = 0` then `M_{J,h}`
contains no constant element. -/
theorem not_const_mem_gaussianMeanSet_of_tsum_eq_zero (hJ' : Summable fun k : S ↦ |J' k|)
    (hzero : (∑' k : S, J' k) = 0) {h' : ℝ} (hh' : h' ≠ 0) (c : ℝ) :
    (fun _ : S ↦ c) ∉ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h') := by
  rw [const_mem_gaussianMeanSet_iff hJ', hzero]
  simpa using hh'

end Constants

/-! ### The continuous symmetry `ω ↦ ω + t` when `Ĵ(1) = 0` -/

section Symmetry

variable [Countable S] [LinearOrder S] {J' : S → ℝ}
  (hSymm : ∀ i j, homogeneousCoupling J' i j = homogeneousCoupling J' j i)
  (hFin : ∀ i, {j : S | homogeneousCoupling J' i j ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset S, (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)

include hSymm hFin hPD in
/-- **The continuous symmetry of a homogeneous Gaussian specification with `Ĵ(1) = 0`.** For every
`t ∈ ℝ` the spin translation `τ^{t·1} : ω ↦ (ω_i + t)_{i ∈ S}` is a symmetry of `γ^{J,h}`. This is
Remark (13.23)(c) applied to the constant element `t·1 ∈ M_{J,0}` produced by
`Potential.const_mem_gaussianMeanSubmodule_of_tsum_eq_zero`; it is the continuous symmetry Georgii
exhibits in Examples (13.29), (13.30) and (13.43). -/
theorem isInvariant_spinTranslation_const_of_tsum_eq_zero
    (hJ' : Summable fun k : S ↦ |J' k|) (hzero : (∑' k : S, J' k) = 0) (h : S → ℝ) (t : ℝ) :
    Specification.IsInvariant
      (MeasureTheory.GibbsMeasure.spinTranslation (fun _ : S ↦ t))
      (gaussianSpecification (homogeneousCoupling J') h hSymm hFin hPD 1 one_pos) :=
  isInvariant_spinTranslation_gaussianSpecification _ hSymm hFin hPD 1 one_pos h
    (const_mem_gaussianMeanSubmodule_of_tsum_eq_zero hJ' hzero t)

include hSymm hFin hPD in
/-- **`𝒢(γ^{J,h})` is preserved by `ω ↦ ω + t` when `Ĵ(1) = 0`.** -/
theorem map_add_const_isGibbsMeasure_of_tsum_eq_zero
    (hJ' : Summable fun k : S ↦ |J' k|) (hzero : (∑' k : S, J' k) = 0) (h : S → ℝ) (t : ℝ)
    {μ : Measure (S → ℝ)} [IsProbabilityMeasure μ]
    (hμ : (gaussianSpecification (homogeneousCoupling J') h hSymm hFin hPD 1
      one_pos).IsGibbsMeasure μ) :
    (gaussianSpecification (homogeneousCoupling J') h hSymm hFin hPD 1
      one_pos).IsGibbsMeasure (μ.map fun x ↦ x + fun _ : S ↦ t) :=
  map_add_isGibbsMeasure_of_mem_gaussianMeanSubmodule _ hSymm hFin hPD 1 one_pos h
    (const_mem_gaussianMeanSubmodule_of_tsum_eq_zero hJ' hzero t) hμ

include hSymm hFin hPD in
/-- **Georgii Theorem (13.26) for homogeneous data of finite range.** If `Ĵ(1) ≠ 0` — so that
`M_{J,h} ≠ ∅` by `Potential.nonempty_gaussianMeanSet_of_tsum_ne_zero` — and Georgii's condition
(13.27) `sup_Λ 𝒥_Λ⁻¹(i,i) < ∞` holds, then `𝒢(γ^{J,h}) ≠ ∅`. -/
theorem nonempty_G_homogeneousCoupling_of_bddAbove
    (hJ' : Summable fun k : S ↦ |J' k|) (hne : (∑' k : S, J' k) ≠ 0)
    (h27 : ∀ i : S, BddAbove (Set.range fun Λ : Finset S ↦
      MeasureTheory.GibbsMeasure.gaussianCovEntry (homogeneousCoupling J') Λ i i))
    (h' : ℝ) :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J')
      (fun _ ↦ h') hSymm hFin hPD 1 one_pos)).Nonempty :=
  MeasureTheory.GibbsMeasure.nonempty_G_gaussianSpecification_of_bddAbove hSymm hFin hPD h27
    (nonempty_gaussianMeanSet_of_tsum_ne_zero hJ' hne h')

end Symmetry

/-! ### Georgii §13.3 on `ℤ^d`: the Fourier transform (13.35) and the spectral covariance (13.37)

From here on `S = ℤ^d`, i.e. `d → ℤ` for a finite type `d`, and the dual group `G = K^d` is
Mathlib's `UnitAddTorus d = d → ℝ/ℤ`, with Georgii's character `z^n` written additively as
`UnitAddTorus.mFourier n z = exp(2πi ⟨n, z⟩)` and the normalised Haar measure `dz` as `volume`
(the local instances below are those of `Mathlib/Analysis/Fourier/AddCircleMulti.lean`). -/

section Fourier

open UnitAddTorus
open scoped ENNReal

/-- Normalised Haar measure on `ℝ/ℤ`, as in `Mathlib/Analysis/Fourier/AddCircleMulti.lean`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- **Georgii (13.35), the Fourier transform of a homogeneous coupling**:
`Ĵ(z) = ∑_{n ∈ ℤ^d} z^n J(n)`, a function on the torus `G = K^d`; here `z^n = mFourier n z`. -/
def fourierHomogeneousCoupling (J' : (d → ℤ) → ℝ) (z : UnitAddTorus d) : ℂ :=
  ∑' n, (J' n : ℂ) * mFourier n z

variable {J' : (d → ℤ) → ℝ}

omit [Fintype d] in
lemma summable_ofReal_of_summable_abs (hJ' : Summable fun n ↦ |J' n|) :
    Summable fun n ↦ (J' n : ℂ) :=
  Complex.summable_ofReal.2 hJ'.of_abs

/-- `Ĵ` is continuous under (13.34). -/
lemma continuous_fourierHomogeneousCoupling (hJ' : Summable fun n ↦ |J' n|) :
    Continuous (fourierHomogeneousCoupling J') :=
  continuous_tsum_mul_mFourier (summable_ofReal_of_summable_abs hJ')

/-- For even `J'`, `Ĵ` is real: `conj Ĵ = Ĵ`. -/
lemma conj_fourierHomogeneousCoupling (hEven : ∀ n, J' (-n) = J' n) (z : UnitAddTorus d) :
    (starRingEnd ℂ) (fourierHomogeneousCoupling J' z) = fourierHomogeneousCoupling J' z := by
  unfold fourierHomogeneousCoupling
  rw [conj_tsum_mul_mFourier fun n ↦ Complex.conj_ofReal _]
  simp [hEven]

/-- For even `J'`, `Ĵ = Re Ĵ`. -/
lemma ofReal_re_fourierHomogeneousCoupling (hEven : ∀ n, J' (-n) = J' n) (z : UnitAddTorus d) :
    ((fourierHomogeneousCoupling J' z).re : ℂ) = fourierHomogeneousCoupling J' z :=
  Complex.conj_eq_iff_re.1 (conj_fourierHomogeneousCoupling hEven z)

/-- `Ĵ(1) = ∑_{n} J(n)`: the value at the identity of the torus is the plain sum. -/
lemma fourierHomogeneousCoupling_zero :
    fourierHomogeneousCoupling J' 0 = ((∑' n, J' n : ℝ) : ℂ) := by
  simp [fourierHomogeneousCoupling, mFourier, Complex.ofReal_tsum]

/-- The Fourier coefficients of `Ĵ` are the values of `J'` (Fourier inversion on `ℓ¹`). -/
lemma mFourierCoeff_fourierHomogeneousCoupling (hJ' : Summable fun n ↦ |J' n|) (m : d → ℤ) :
    mFourierCoeff (fourierHomogeneousCoupling J') m = J' m :=
  mFourierCoeff_tsum_mul_mFourier (summable_ofReal_of_summable_abs hJ') m

/-- The Fourier coefficients of the real function `Re Ĵ` are the values of `J'`. -/
lemma mFourierCoeff_re_fourierHomogeneousCoupling (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n) (m : d → ℤ) :
    mFourierCoeff (fun z ↦ ((fourierHomogeneousCoupling J' z).re : ℂ)) m = J' m := by
  simp_rw [ofReal_re_fourierHomogeneousCoupling hEven]
  exact mFourierCoeff_fourierHomogeneousCoupling hJ' m

omit [Fintype d] in
/-- The quadratic form of a covariance-type matrix at `x : Λ → ℝ`, written as a double sum over
`Λ` of the extension of `x` by zero. -/
lemma dotProduct_covMatrix_mulVec_eq_sum (C : (d → ℤ) → (d → ℤ) → ℝ) (Λ : Finset (d → ℤ))
    (x : Λ → ℝ) :
    x ⬝ᵥ (ProbabilityTheory.covMatrix C Λ) *ᵥ x
      = ∑ i ∈ Λ, ∑ j ∈ Λ, Function.extend Subtype.val x 0 i * Function.extend Subtype.val x 0 j
          * C i j := by
  rw [← Finset.sum_coe_sort Λ]
  simp only [← Finset.sum_coe_sort Λ (fun j ↦ _ * Function.extend Subtype.val x 0 j * C _ j),
    Subtype.val_injective.extend_apply]
  simp only [dotProduct, mulVec, ProbabilityTheory.covMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- **Georgii's identity in the proof of (13.A8)**: for a homogeneous coupling,
`∑_{i,j ∈ Λ} x_i J(i,j) x_j = ∫ |∑_{j ∈ Λ} x_j z^j|² Ĵ(z) dz`. -/
theorem dotProduct_gaussianCouplingMatrix_homogeneousCoupling_mulVec
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n) (Λ : Finset (d → ℤ))
    (x : Λ → ℝ) :
    x ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') Λ) *ᵥ x
      = ∫ z, Complex.normSq (∑ j ∈ Λ,
          ((Function.extend Subtype.val x 0 : (d → ℤ) → ℝ) j : ℂ) * mFourier j z)
          * (fourierHomogeneousCoupling J' z).re := by
  have hint : Integrable fun z ↦ (fourierHomogeneousCoupling J' z).re :=
    (Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ'))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [gaussianCouplingMatrix, dotProduct_covMatrix_mulVec_eq_sum,
    ← sum_sum_mul_re_mFourierCoeff_sub hint]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mFourierCoeff_re_fourierHomogeneousCoupling hJ' hEven, homogeneousCoupling_apply,
    ← hEven, neg_sub]
  simp

/-- **Georgii (13.A8), "if", nonnegative form**: if `Ĵ ≥ 0` then every `𝒥_Λ` is nonnegative
definite. -/
theorem posSemidef_gaussianCouplingMatrix_homogeneousCoupling
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) (Λ : Finset (d → ℤ)) :
    (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · refine Matrix.IsHermitian.ext fun a b ↦ ?_
    simpa using symm_homogeneousCoupling hEven b.1 a.1
  · rw [star_trivial, dotProduct_gaussianCouplingMatrix_homogeneousCoupling_mulVec hJ' hEven]
    exact integral_nonneg fun z ↦ mul_nonneg (Complex.normSq_nonneg _) (hpos z)

/-- **Georgii (13.A8), "if"**: if `Ĵ ≥ 0` and `Ĵ` is not identically zero on the torus then `J`
is positive definite, i.e. every `𝒥_Λ` is positive definite. Georgii's proof: the quadratic form
of `𝒥_Λ` at `x` is `∫_G |∑_j x_j z^j|² Ĵ dz`, which vanishes only if the trigonometric polynomial
`∑_j x_j z^j` vanishes on the non-empty open set `{Ĵ ≠ 0}` — hence, by
`UnitAddTorus.sum_mul_mFourier_eq_zero_of_eqOn_zero`, everywhere. -/
theorem posDef_gaussianCouplingMatrix_homogeneousCoupling
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hne : ∃ z, (fourierHomogeneousCoupling J' z).re ≠ 0) (Λ : Finset (d → ℤ)) :
    (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef := by
  have hpsd := posSemidef_gaussianCouplingMatrix_homogeneousCoupling hJ' hEven hpos Λ
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hpsd.1, fun x hx ↦ ?_⟩
  refine lt_of_le_of_ne ((Matrix.posSemidef_iff_dotProduct_mulVec.1 hpsd).2 x) fun h0 ↦ hx ?_
  rw [star_trivial, gaussianCouplingMatrix, dotProduct_covMatrix_mulVec_eq_sum] at h0
  have hcont : Continuous fun z ↦ (fourierHomogeneousCoupling J' z).re :=
    Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ')
  have hgne : (fun z ↦ (fourierHomogeneousCoupling J' z).re) ≠ 0 := by
    obtain ⟨z₀, hz₀⟩ := hne
    exact fun hcon ↦ hz₀ (congrFun hcon z₀)
  have h0' : ∑ i ∈ Λ, ∑ j ∈ Λ, Function.extend Subtype.val x 0 i * Function.extend Subtype.val x 0 j
      * (mFourierCoeff (fun z ↦ ((fourierHomogeneousCoupling J' z).re : ℂ)) (i - j)).re = 0 := by
    refine (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_).trans h0.symm
    rw [mFourierCoeff_re_fourierHomogeneousCoupling hJ' hEven, homogeneousCoupling_apply,
      ← hEven, neg_sub]
    simp
  have := eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero_of_continuous hcont hpos hgne Λ _ h0'
  funext a
  simpa [Subtype.val_injective.extend_apply] using this a.1 a.2

/-! ### Georgii Proposition (13.A8): positive definiteness of `J` versus `Ĵ ≥ 0` -/

section PosDefIff

/-- `|Ĵ| ≤ ∑_{n ∈ S} |J(n)|`. -/
lemma abs_re_fourierHomogeneousCoupling_le (hJ' : Summable fun n ↦ |J' n|) (z : UnitAddTorus d) :
    |(fourierHomogeneousCoupling J' z).re| ≤ ∑' n, |J' n| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [fourierHomogeneousCoupling]
  refine (norm_tsum_mul_mFourier_le (summable_ofReal_of_summable_abs hJ') z).trans_eq ?_
  exact tsum_congr fun n ↦ by simp

/-- `Ĵ` is continuous on the compact torus, hence integrable. -/
lemma integrable_re_fourierHomogeneousCoupling (hJ' : Summable fun n ↦ |J' n|) :
    Integrable fun z ↦ (fourierHomogeneousCoupling J' z).re :=
  (Complex.continuous_re.comp
    (continuous_fourierHomogeneousCoupling hJ')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit [Fintype d] in
/-- **The Toeplitz form of a homogeneous coupling at a real vector is the quadratic form of
`𝒥_I`**: `∑_{i, j ∈ I} a_i a_j J(i - j) = a ⬝ᵥ 𝒥_I *ᵥ a`. -/
lemma dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum (hEven : ∀ n, J' (-n) = J' n)
    (I : Finset (d → ℤ)) (a : (d → ℤ) → ℝ) :
    (fun i : I ↦ a i.1) ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') I) *ᵥ
        (fun i : I ↦ a i.1)
      = ∑ i ∈ I, ∑ j ∈ I, a i * a j * J' (i - j) := by
  classical
  have hx : ∀ i ∈ I, Function.extend Subtype.val (fun i : I ↦ a i.1) 0 i = a i := fun i hi ↦ by
    simpa using Subtype.val_injective.extend_apply (fun i : I ↦ a i.1) 0 ⟨i, hi⟩
  rw [gaussianCouplingMatrix, dotProduct_covMatrix_mulVec_eq_sum]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [hx i hi, hx j hj, homogeneousCoupling_apply, ← neg_sub i j, hEven]

omit [Fintype d] in
/-- If every `𝒥_Λ` is nonnegative definite then `∑_{i, j ∈ I} a_i a_j J(i - j) ≥ 0`. -/
lemma sum_sum_mul_homogeneousCoupling_nonneg (hEven : ∀ n, J' (-n) = J' n)
    (hPSD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosSemidef)
    (I : Finset (d → ℤ)) (a : (d → ℤ) → ℝ) :
    0 ≤ ∑ i ∈ I, ∑ j ∈ I, a i * a j * J' (i - j) := by
  rw [← dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum hEven]
  simpa using (Matrix.posSemidef_iff_dotProduct_mulVec.1 (hPSD I)).2 fun i : I ↦ a i.1

/-- **Georgii's identity in the proof of (13.A8), complex form**: for a finitely supported
`u : ℤᵈ → ℂ`, `∑_{i, j} ū_i u_j J(i - j) = ∫_G |∑_j u_j z^j|² Ĵ(z) dz`. -/
lemma sum_sum_conj_mul_homogeneousCoupling (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n) (I : Finset (d → ℤ)) (u : (d → ℤ) → ℂ) :
    ∑ i ∈ I, ∑ j ∈ I, (starRingEnd ℂ) (u i) * u j * ((J' (i - j) : ℝ) : ℂ)
      = ((∫ z, Complex.normSq (∑ j ∈ I, u j * mFourier j z)
          * (fourierHomogeneousCoupling J' z).re : ℝ) : ℂ) := by
  have h1 : ∀ i j : d → ℤ, ((J' (i - j) : ℝ) : ℂ)
      = mFourierCoeff (fun z ↦ (((fourierHomogeneousCoupling J' z).re : ℝ) : ℂ)) (i - j) :=
    fun i j ↦ (mFourierCoeff_re_fourierHomogeneousCoupling hJ' hEven _).symm
  simp_rw [h1]
  rw [sum_sum_conj_mul_mFourierCoeff_sub (integrable_re_fourierHomogeneousCoupling hJ')]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]

/-- **The Toeplitz form of a homogeneous coupling at a complex vector splits.** Since `J` is
real, `∫_G |∑_j u_j z^j|² Ĵ(z) dz` is the sum of the quadratic forms of `𝒥_I` at `Re u` and at
`Im u`. -/
lemma integral_normSq_mul_re_fourierHomogeneousCoupling_eq (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n) (I : Finset (d → ℤ)) (u : (d → ℤ) → ℂ) :
    ∫ z, Complex.normSq (∑ j ∈ I, u j * mFourier j z) * (fourierHomogeneousCoupling J' z).re
      = (fun j : I ↦ (u j.1).re) ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') I) *ᵥ
          (fun j : I ↦ (u j.1).re)
        + (fun j : I ↦ (u j.1).im) ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') I) *ᵥ
          (fun j : I ↦ (u j.1).im) := by
  have hkey := congrArg Complex.re (sum_sum_conj_mul_homogeneousCoupling hJ' hEven I u)
  rw [Complex.ofReal_re] at hkey
  simp only [Complex.re_sum] at hkey
  have hre := dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum (J' := J') hEven I
    fun i ↦ (u i).re
  have him := dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum (J' := J') hEven I
    fun i ↦ (u i).im
  rw [← hkey, hre, him]
  have hterm : ∀ i j : d → ℤ, ((starRingEnd ℂ) (u i) * u j * ((J' (i - j) : ℝ) : ℂ)).re
      = (u i).re * (u j).re * J' (i - j) + (u i).im * (u j).im * J' (i - j) := by
    intro i j
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [hterm, Finset.sum_add_distrib]

/-- **The Toeplitz form of a homogeneous coupling at a complex vector is nonnegative** when every
`𝒥_Λ` is nonnegative definite. -/
lemma integral_normSq_mul_re_fourierHomogeneousCoupling_nonneg (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n)
    (hPSD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosSemidef)
    (I : Finset (d → ℤ)) (u : (d → ℤ) → ℂ) :
    0 ≤ ∫ z, Complex.normSq (∑ j ∈ I, u j * mFourier j z)
        * (fourierHomogeneousCoupling J' z).re := by
  have hre := dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum (J' := J') hEven I
    fun i ↦ (u i).re
  have him := dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum (J' := J') hEven I
    fun i ↦ (u i).im
  rw [integral_normSq_mul_re_fourierHomogeneousCoupling_eq hJ' hEven, hre, him]
  exact add_nonneg (sum_sum_mul_homogeneousCoupling_nonneg hEven hPSD I fun i ↦ (u i).re)
    (sum_sum_mul_homogeneousCoupling_nonneg hEven hPSD I fun i ↦ (u i).im)

/-- **The variational bound for `𝒥_I⁻¹(i,i)` in the Fourier picture, complex form.** For a
trigonometric polynomial `∑_{j ∈ I} c_j z^j` with `i ∈ I`,
`2 Re c_i - ∫_G |∑_j c_j z^j|² Ĵ dz ≤ 𝒥_I⁻¹(i,i)`: the imaginary part of `c` only lowers the
left-hand side, and for real coefficients this is
`MeasureTheory.GibbsMeasure.two_mul_sub_dotProduct_mulVec_le_gaussianCovEntry`. -/
theorem two_mul_re_sub_integral_normSq_le_gaussianCovEntry [LinearOrder (d → ℤ)]
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (I : Finset (d → ℤ)) (u : (d → ℤ) → ℂ) {i : d → ℤ} (hi : i ∈ I) :
    2 * (u i).re - ∫ z, Complex.normSq (∑ j ∈ I, u j * mFourier j z)
        * (fourierHomogeneousCoupling J' z).re
      ≤ MeasureTheory.GibbsMeasure.gaussianCovEntry (homogeneousCoupling J') I i i := by
  rw [integral_normSq_mul_re_fourierHomogeneousCoupling_eq hJ' hEven]
  have him : 0 ≤ (fun j : I ↦ (u j.1).im) ⬝ᵥ
      (gaussianCouplingMatrix (homogeneousCoupling J') I) *ᵥ fun j : I ↦ (u j.1).im := by
    simpa using (hPD I).posSemidef.dotProduct_mulVec_nonneg fun j : I ↦ (u j.1).im
  have hre := MeasureTheory.GibbsMeasure.two_mul_sub_dotProduct_mulVec_le_gaussianCovEntry
    (hPD I) hi fun j : I ↦ (u j.1).re
  simp only at hre
  linarith

/-- **Georgii Proposition (13.A8), "only if"**: if `J` is nonnegative definite — every `𝒥_Λ` is —
then its Fourier transform is nonnegative everywhere on `G`.

Georgii's proof: `∑_{i,j} u_i J(i-j) ū_j = ∫ |g|² Ĵ` for every trigonometric polynomial `g`
(`sum_sum_conj_mul_homogeneousCoupling`); by Stone–Weierstrass
(`UnitAddTorus.exists_norm_sub_sum_mul_mFourier_le`) the functions `|g|²` approximate uniformly
the square of any continuous function, in particular the negative part `Ĵ⁻`, whence
`∫ (Ĵ⁻)² Ĵ ≥ 0`; but that integrand is `-(Ĵ⁻)³ ≤ 0`, so `Ĵ⁻` vanishes a.e. and, being
continuous, everywhere. -/
theorem re_fourierHomogeneousCoupling_nonneg_of_posSemidef (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n)
    (hPSD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosSemidef)
    (z : UnitAddTorus d) : 0 ≤ (fourierHomogeneousCoupling J' z).re := by
  set B : ℝ := ∑' n, |J' n| with hBdef
  have hB0 : 0 ≤ B := tsum_nonneg fun n ↦ abs_nonneg _
  set Jh : UnitAddTorus d → ℝ := fun z ↦ (fourierHomogeneousCoupling J' z).re with hJhdef
  have hJhcont : Continuous Jh :=
    Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ')
  have hJhbd : ∀ z, |Jh z| ≤ B := abs_re_fourierHomogeneousCoupling_le hJ'
  set f : UnitAddTorus d → ℝ := fun z ↦ Real.sqrt (max (-(Jh z)) 0) with hfdef
  have hfcont : Continuous f := Real.continuous_sqrt.comp (hJhcont.neg.max continuous_const)
  have hfnn : ∀ z, 0 ≤ f z := fun z ↦ Real.sqrt_nonneg _
  have hfsq : ∀ z, f z ^ 2 = max (-(Jh z)) 0 := fun z ↦ Real.sq_sqrt (le_max_right _ _)
  have hfle : ∀ z, f z ≤ Real.sqrt B := fun z ↦ Real.sqrt_le_sqrt (by
    rcases le_or_gt (-(Jh z)) 0 with h | h
    · simpa [max_eq_right h] using hB0
    · rw [max_eq_left h.le]
      exact (neg_le_abs _).trans (hJhbd z))
  have hintf : Integrable fun z ↦ f z ^ 2 * Jh z :=
    ((hfcont.pow 2).mul hJhcont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hstep : 0 ≤ ∫ z, f z ^ 2 * Jh z := by
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    set C : ℝ := (2 * Real.sqrt B + 1) * B + 1 with hCdef
    have hCpos : 0 < C := by
      have : (0 : ℝ) ≤ (2 * Real.sqrt B + 1) * B :=
        mul_nonneg (by positivity) hB0
      simp only [hCdef]; linarith
    set ε : ℝ := min 1 (δ / C) with hεdef
    have hε : 0 < ε := lt_min one_pos (div_pos hδ hCpos)
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hεC : ε ≤ δ / C := min_le_right _ _
    obtain ⟨I, c, hc⟩ := UnitAddTorus.exists_norm_sub_sum_mul_mFourier_le
      (ContinuousMap.mk (fun z ↦ ((f z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hfcont)) hε
    set P : UnitAddTorus d → ℂ := fun z ↦ ∑ j ∈ I, c j * mFourier j z with hPdef
    have hcP : ∀ z, ‖((f z : ℝ) : ℂ) - P z‖ ≤ ε := hc
    have hbd : ∀ z, |Complex.normSq (P z) - f z ^ 2| ≤ ε * (2 * Real.sqrt B + ε) := by
      intro z
      have h1 : ‖((f z : ℝ) : ℂ)‖ = f z := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfnn z)]
      have hd : ‖P z - ((f z : ℝ) : ℂ)‖ ≤ ε := by
        rw [← norm_neg]; simpa using hcP z
      have h2 : ‖P z‖ ≤ f z + ε := by
        calc ‖P z‖ = ‖((f z : ℝ) : ℂ) + (P z - ((f z : ℝ) : ℂ))‖ := by congr 1; ring
          _ ≤ ‖((f z : ℝ) : ℂ)‖ + ‖P z - ((f z : ℝ) : ℂ)‖ := norm_add_le _ _
          _ ≤ f z + ε := by rw [h1]; linarith
      have habs : |‖P z‖ - f z| ≤ ε := by
        rw [← h1]
        exact (abs_norm_sub_norm_le _ _).trans hd
      have hsq : Complex.normSq (P z) - f z ^ 2 = (‖P z‖ - f z) * (‖P z‖ + f z) := by
        rw [Complex.normSq_eq_norm_sq]; ring
      rw [hsq, abs_mul]
      refine mul_le_mul habs ?_ (abs_nonneg _) hε.le
      rw [abs_of_nonneg (by positivity)]
      have := hfle z
      linarith
    have hintP : Integrable fun z ↦ Complex.normSq (P z) * Jh z :=
      UnitAddTorus.integrable_normSq_sum_mul_mFourier_mul
        (integrable_re_fourierHomogeneousCoupling hJ') I c
    have hnonneg : 0 ≤ ∫ z, Complex.normSq (P z) * Jh z :=
      integral_normSq_mul_re_fourierHomogeneousCoupling_nonneg hJ' hEven hPSD I c
    have hsplit : ∫ z, (Complex.normSq (P z) - f z ^ 2) * Jh z
        = (∫ z, Complex.normSq (P z) * Jh z) - ∫ z, f z ^ 2 * Jh z := by
      simp_rw [sub_mul]
      exact integral_sub hintP hintf
    have hbound : ‖∫ z, (Complex.normSq (P z) - f z ^ 2) * Jh z‖
        ≤ ε * (2 * Real.sqrt B + ε) * B := by
      refine (norm_integral_le_of_norm_le_const
        (C := ε * (2 * Real.sqrt B + ε) * B) ?_).trans_eq ?_
      · filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbd z) (hJhbd z) (abs_nonneg _) (by positivity)
      · simp
    have hδbound : ε * (2 * Real.sqrt B + ε) * B ≤ δ := by
      have hb : (2 * Real.sqrt B + ε) * B ≤ C := by
        simp only [hCdef]
        nlinarith [hB0, hε1, Real.sqrt_nonneg B]
      have h1 : ε * (2 * Real.sqrt B + ε) * B ≤ ε * C := by
        calc ε * (2 * Real.sqrt B + ε) * B = ε * ((2 * Real.sqrt B + ε) * B) := by ring
          _ ≤ ε * C := mul_le_mul_of_nonneg_left hb hε.le
      have h2 : ε * C ≤ δ := by
        have := mul_le_mul_of_nonneg_right hεC hCpos.le
        rwa [div_mul_cancel₀ _ hCpos.ne'] at this
      linarith
    have : (∫ z, Complex.normSq (P z) * Jh z) - ∫ z, f z ^ 2 * Jh z ≤ δ := by
      rw [← hsplit]
      exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hbound).trans hδbound)
    linarith
  have hle0 : ∀ z, f z ^ 2 * Jh z ≤ 0 := fun z ↦ by
    rw [hfsq]
    rcases le_or_gt 0 (Jh z) with h | h
    · rw [max_eq_right (by linarith)]; simp
    · rw [max_eq_left (by linarith)]; nlinarith
  have hzero : ∫ z, f z ^ 2 * Jh z = 0 :=
    le_antisymm (integral_nonpos hle0) hstep
  have haenn : (fun z ↦ -(f z ^ 2 * Jh z)) =ᵐ[volume] fun _ ↦ (0 : ℝ) := by
    refine (integral_eq_zero_iff_of_nonneg_ae ?_ hintf.neg).1 ?_
    · exact Filter.Eventually.of_forall fun z ↦ by simpa using neg_nonneg.2 (hle0 z)
    · simp only [Pi.neg_apply]
      rw [integral_neg, hzero, neg_zero]
  have heq : (fun z ↦ -(f z ^ 2 * Jh z)) = fun _ ↦ (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq volume (((hfcont.pow 2).mul hJhcont).neg) continuous_const).1 haenn
  have hz : f z ^ 2 * Jh z = 0 := by
    have := congrFun heq z
    simpa using this
  by_contra hneg
  replace hneg : Jh z < 0 := lt_of_not_ge hneg
  rw [hfsq, max_eq_left (by linarith : (0 : ℝ) ≤ -(Jh z))] at hz
  nlinarith

/-- **Georgii Proposition (13.A8)** for nonnegative definiteness: an even absolutely summable
`J : ℤᵈ → ℝ` has all its coupling matrices `𝒥_Λ` nonnegative definite if and only if `Ĵ ≥ 0`. -/
theorem posSemidef_gaussianCouplingMatrix_homogeneousCoupling_iff (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n) :
    (∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosSemidef)
      ↔ ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re :=
  ⟨fun h z ↦ re_fourierHomogeneousCoupling_nonneg_of_posSemidef hJ' hEven h z,
    fun h Λ ↦ posSemidef_gaussianCouplingMatrix_homogeneousCoupling hJ' hEven h Λ⟩

/-- **Georgii Proposition (13.A8), "only if"** as he states it, for positive definiteness. -/
theorem re_fourierHomogeneousCoupling_nonneg_of_posDef (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (z : UnitAddTorus d) : 0 ≤ (fourierHomogeneousCoupling J' z).re :=
  re_fourierHomogeneousCoupling_nonneg_of_posSemidef hJ' hEven (fun Λ ↦ (hPD Λ).posSemidef) z

/-- **Georgii Proposition (13.A8)**, as he states it: an even absolutely summable `J : ℤᵈ → ℝ` is
positive definite — every `𝒥_Λ` is positive definite — **iff** `Ĵ` is nonnegative and not
identically zero. -/
theorem posDef_gaussianCouplingMatrix_homogeneousCoupling_iff (hJ' : Summable fun n ↦ |J' n|)
    (hEven : ∀ n, J' (-n) = J' n) :
    (∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
      ↔ (∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
          ∧ ∃ z, (fourierHomogeneousCoupling J' z).re ≠ 0 := by
  refine ⟨fun hPD ↦ ⟨fun z ↦ re_fourierHomogeneousCoupling_nonneg_of_posDef hJ' hEven hPD z, ?_⟩,
    fun h Λ ↦ posDef_gaussianCouplingMatrix_homogeneousCoupling hJ' hEven h.1 h.2 Λ⟩
  -- if `Ĵ ≡ 0` then `J' = 0`, and the `1 × 1` matrix `𝒥_{{0}} = (J'(0))` is not positive definite
  by_contra hcon
  have hzero : ∀ z, (fourierHomogeneousCoupling J' z).re = 0 :=
    fun z ↦ not_not.1 fun hz ↦ hcon ⟨z, hz⟩
  have hJ0 : J' 0 = 0 := by
    have hco := mFourierCoeff_re_fourierHomogeneousCoupling hJ' hEven 0
    rw [show (fun z ↦ (((fourierHomogeneousCoupling J' z).re : ℝ) : ℂ))
        = fun _ : UnitAddTorus d ↦ (0 : ℂ) from funext fun z ↦ by rw [hzero z]; norm_num,
      mFourierCoeff_const] at hco
    simpa using hco.symm
  have hx : (fun _ : ({0} : Finset (d → ℤ)) ↦ (1 : ℝ)) ≠ 0 := fun hzero ↦ by
    simpa using congrFun hzero ⟨0, by simp⟩
  have hlt := (Matrix.posDef_iff_dotProduct_mulVec.1 (hPD {0})).2 hx
  rw [star_trivial,
    dotProduct_gaussianCouplingMatrix_homogeneousCoupling_eq_sum hEven {0} fun _ ↦ (1 : ℝ)] at hlt
  simp only [Finset.sum_singleton, sub_self, one_mul, mul_one] at hlt
  exact absurd hJ0 hlt.ne'

end PosDefIff

/-- **Georgii (13.37), the spectral covariance**: `C(i,j) = ∫_G z^{j-i} Ĵ(z)⁻¹ dz`, i.e. the
`(i - j)`-th Fourier coefficient of `Ĵ⁻¹` (with the real-number convention `0⁻¹ = 0`; the set
`{Ĵ = 0}` is null whenever `∫ Ĵ⁻¹ dz < ∞`, so nothing is lost). -/
def spectralCovariance (J' : (d → ℤ) → ℝ) (i j : d → ℤ) : ℝ :=
  (mFourierCoeff (fun z ↦ ((((fourierHomogeneousCoupling J' z).re)⁻¹ : ℝ) : ℂ)) (i - j)).re

/-- `C` is symmetric. -/
lemma spectralCovariance_symm (i j : d → ℤ) :
    spectralCovariance J' i j = spectralCovariance J' j i := by
  unfold spectralCovariance
  rw [← neg_sub j i, re_mFourierCoeff_ofReal_neg]

/-- The `i`-th coefficient of a trigonometric polynomial as a Fourier integral:
`∫_G (∑_{j ∈ Λ} x_j z^j) \bar z^i dz = x_i` for `i ∈ Λ`. -/
lemma integral_re_sum_mul_mFourier_mul_conj (Λ : Finset (d → ℤ)) (x : (d → ℤ) → ℝ) {i : d → ℤ}
    (hi : i ∈ Λ) :
    ∫ z, ((∑ j ∈ Λ, ((x j : ℝ) : ℂ) * mFourier j z) * (starRingEnd ℂ) (mFourier i z)).re
      = x i := by
  have hpt : ∀ z : UnitAddTorus d,
      ((∑ j ∈ Λ, ((x j : ℝ) : ℂ) * mFourier j z) * (starRingEnd ℂ) (mFourier i z)).re
        = ∑ j ∈ Λ, x j * (mFourier (j - i) z).re := by
    intro z
    rw [Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_assoc, ← mFourier_sub]
    simp [Complex.mul_re]
  simp_rw [hpt]
  rw [integral_finsetSum Λ fun j _ ↦
    (show Integrable fun z : UnitAddTorus d ↦ x j * (mFourier (j - i) z).re from
      (continuous_const.mul (Complex.continuous_re.comp
        (mFourier (j - i)).continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_const_mul, integral_re_mFourier]
  refine (Finset.sum_eq_single i (fun j _ hji ↦ ?_) (fun hcon ↦ absurd hi hcon)).trans ?_
  · rw [ite_eq_right (fun hc ↦ hji (by simpa [sub_eq_zero] using hc)), mul_zero]
  · simp

section Integrable

variable (hJ' : Summable fun n ↦ |J' n|)
  (hint : ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞)
include hJ' hint

/-- Under `∫ Ĵ⁻¹ dz < ∞` (with `1/0 = ∞`), `Ĵ > 0` almost everywhere. -/
lemma ae_pos_re_fourierHomogeneousCoupling :
    ∀ᵐ z ∂volume, 0 < (fourierHomogeneousCoupling J' z).re :=
  ae_pos_of_lintegral_inv_ofReal_ne_top
    (Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ')).measurable.aemeasurable
    hint

/-- Under `∫ Ĵ⁻¹ dz < ∞`, `Ĵ⁻¹` is integrable. -/
lemma integrable_inv_re_fourierHomogeneousCoupling :
    Integrable fun z ↦ ((fourierHomogeneousCoupling J' z).re)⁻¹ :=
  integrable_inv_of_lintegral_inv_ofReal_ne_top
    (Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ')).measurable.aemeasurable
    hint

/-- `Ĵ · Ĵ⁻¹ = 1` almost everywhere. -/
lemma fourierHomogeneousCoupling_mul_inv_ae_eq_one (hEven : ∀ n, J' (-n) = J' n) :
    (fun z ↦ fourierHomogeneousCoupling J' z
        * ((((fourierHomogeneousCoupling J' z).re)⁻¹ : ℝ) : ℂ))
      =ᵐ[volume] fun _ ↦ (1 : ℂ) := by
  filter_upwards [ae_pos_re_fourierHomogeneousCoupling hJ' hint] with z hz
  nth_rw 1 [← ofReal_re_fourierHomogeneousCoupling hEven]
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hz.ne', Complex.ofReal_one]

/-- **The spectral covariance is nonnegative definite** (Georgii: "`C` is symmetric and positive
definite"). -/
theorem posSemidef_covMatrix_spectralCovariance
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) (I : Finset (d → ℤ)) :
    (ProbabilityTheory.covMatrix (spectralCovariance J') I).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · refine Matrix.IsHermitian.ext fun a b ↦ ?_
    simpa using spectralCovariance_symm (J' := J') b.1 a.1
  · rw [star_trivial, dotProduct_covMatrix_mulVec_eq_sum]
    simp only [spectralCovariance]
    exact sum_sum_mul_re_mFourierCoeff_sub_nonneg
      (integrable_inv_re_fourierHomogeneousCoupling hJ' hint)
      (Filter.Eventually.of_forall fun z ↦ inv_nonneg.2 (hpos z)) I _

/-- **Georgii's computation in Step 1 of the proof of (13.36)**: the spectral covariance inverts
`J`, `∑_{j} J(j - i) C(j, k) = δ_{ik}`. -/
theorem tsum_homogeneousCoupling_mul_spectralCovariance (hEven : ∀ n, J' (-n) = J' n)
    (i k : d → ℤ) :
    ∑' j, homogeneousCoupling J' i j * spectralCovariance J' j k = if i = k then 1 else 0 := by
  set g : UnitAddTorus d → ℂ := fun z ↦ ((((fourierHomogeneousCoupling J' z).re)⁻¹ : ℝ) : ℂ)
    with hg
  have hgint : Integrable g := (integrable_inv_re_fourierHomogeneousCoupling hJ' hint).ofReal
  have hsum : Summable fun j ↦ ((J' (j - i) : ℝ) : ℂ) * mFourierCoeff g (j - k) := by
    refine Summable.of_norm_bounded (g := fun j ↦ |J' (j - i)| * ∫ z, ‖g z‖) ?_ fun j ↦ ?_
    · exact ((Equiv.subRight i).summable_iff.2 hJ').mul_right _
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_mFourierCoeff_le _) (abs_nonneg _)
  have hre : ∑' j, homogeneousCoupling J' i j * spectralCovariance J' j k
      = (∑' j, ((J' (j - i) : ℝ) : ℂ) * mFourierCoeff g (j - k)).re := by
    rw [Complex.re_tsum hsum]
    simp [homogeneousCoupling, spectralCovariance, hg]
  have hre2 : ∑' j, ((J' (j - i) : ℝ) : ℂ) * mFourierCoeff g (j - k)
      = ∑' n, ((J' n : ℝ) : ℂ) * mFourierCoeff g ((i - k) - n) := by
    rw [← (Equiv.subLeft i).tsum_eq]
    refine tsum_congr fun n ↦ ?_
    simp only [Equiv.subLeft_apply, sub_sub_cancel_left, hEven]
    congr 2
    abel
  rw [hre, hre2, ← mFourierCoeff_tsum_mul_mFourier_mul (summable_ofReal_of_summable_abs hJ') hgint]
  change (mFourierCoeff (fun x ↦ fourierHomogeneousCoupling J' x
    * ((((fourierHomogeneousCoupling J' x).re)⁻¹ : ℝ) : ℂ)) (i - k)).re = _
  rw [mFourierCoeff_congr_ae (fourierHomogeneousCoupling_mul_inv_ae_eq_one hJ' hint hEven),
    mFourierCoeff_const]
  simp only [sub_eq_zero]
  split_ifs <;> simp

/-- **Georgii (13.A8), "if", in the form used by Theorem (13.36)**: if `Ĵ ≥ 0` and
`∫ Ĵ⁻¹ dz < ∞` (with `1/0 = ∞`) then every `𝒥_Λ` is positive definite. -/
theorem posDef_gaussianCouplingMatrix_homogeneousCoupling_of_lintegral_inv_ne_top
    (hEven : ∀ n, J' (-n) = J' n) (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (Λ : Finset (d → ℤ)) : (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef := by
  obtain ⟨z₀, hz₀⟩ := ((ae_pos_re_fourierHomogeneousCoupling hJ' hint).mono
    fun _ hz ↦ hz.ne').exists
  exact posDef_gaussianCouplingMatrix_homogeneousCoupling hJ' hEven hpos ⟨z₀, hz₀⟩ Λ

/-! #### Georgii's condition (13.27) in spectral form -/

/-- **The variational bound behind Georgii's condition (13.27).** For every finite `Λ`, every
`i ∈ Λ` and every `x : Λ → ℝ`,
`2 x_i - ∑_{j,k ∈ Λ} x_j J(j - k) x_k ≤ ∫_G Ĵ(z)⁻¹ dz`.

Completing the square: the difference of the two sides is
`∫_G |∑_{j ∈ Λ} x_j z^j - z^i Ĵ(z)⁻¹|² Ĵ(z) dz ≥ 0`, where `Ĵ Ĵ⁻¹ = 1` almost everywhere by
`Potential.ae_pos_re_fourierHomogeneousCoupling`. -/
theorem two_mul_sub_dotProduct_gaussianCouplingMatrix_le_integral_inv
    (hEven : ∀ n, J' (-n) = J' n) (Λ : Finset (d → ℤ)) (x : Λ → ℝ) {i : d → ℤ} (hi : i ∈ Λ) :
    2 * x ⟨i, hi⟩ - x ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') Λ) *ᵥ x
      ≤ ∫ z, ((fourierHomogeneousCoupling J' z).re)⁻¹ := by
  classical
  set Jh : UnitAddTorus d → ℝ := fun z ↦ (fourierHomogeneousCoupling J' z).re with hJhdef
  set F : UnitAddTorus d → ℝ := fun z ↦ (Jh z)⁻¹ with hFdef
  set xe : (d → ℤ) → ℝ := Function.extend Subtype.val x 0 with hxedef
  set P : UnitAddTorus d → ℂ := fun z ↦ ∑ j ∈ Λ, ((xe j : ℝ) : ℂ) * mFourier j z with hPdef
  have hxei : xe i = x ⟨i, hi⟩ := by
    simpa [hxedef] using Subtype.val_injective.extend_apply x 0 ⟨i, hi⟩
  have hquad : x ⬝ᵥ (gaussianCouplingMatrix (homogeneousCoupling J') Λ) *ᵥ x
      = ∫ z, Complex.normSq (P z) * Jh z :=
    dotProduct_gaussianCouplingMatrix_homogeneousCoupling_mulVec hJ' hEven Λ x
  have hlin : ∫ z, (P z * (starRingEnd ℂ) (mFourier i z)).re = x ⟨i, hi⟩ := by
    rw [← hxei]
    exact integral_re_sum_mul_mFourier_mul_conj Λ xe hi
  have hPcont : Continuous P :=
    continuous_finsetSum _ fun j _ ↦ continuous_const.mul (mFourier j).continuous
  have hInormSq : Integrable fun z ↦ Complex.normSq (P z) * Jh z :=
    UnitAddTorus.integrable_normSq_sum_mul_mFourier_mul
      (integrable_re_fourierHomogeneousCoupling hJ') Λ fun j ↦ ((xe j : ℝ) : ℂ)
  have hIF : Integrable F := integrable_inv_re_fourierHomogeneousCoupling hJ' hint
  have hIlin : Integrable fun z ↦ (P z * (starRingEnd ℂ) (mFourier i z)).re :=
    (Complex.continuous_re.comp (hPcont.mul (Complex.continuous_conj.comp
      (mFourier i).continuous))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hnn : (0 : UnitAddTorus d → ℝ) ≤ᵐ[volume] fun z ↦ Complex.normSq (P z) * Jh z + F z
      - 2 * (P z * (starRingEnd ℂ) (mFourier i z)).re := by
    filter_upwards [ae_pos_re_fourierHomogeneousCoupling hJ' hint] with z hz
    have hFz : F z * Jh z = 1 := inv_mul_cancel₀ hz.ne'
    have hnormB : Complex.normSq (mFourier i z * ((F z : ℝ) : ℂ)) = F z * F z := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal]
      simp [Complex.normSq_eq_norm_sq, norm_mFourier_apply]
    have hcross : (P z * (starRingEnd ℂ) (mFourier i z * ((F z : ℝ) : ℂ))).re
        = F z * (P z * (starRingEnd ℂ) (mFourier i z)).re := by
      rw [map_mul, Complex.conj_ofReal,
        show P z * ((starRingEnd ℂ) (mFourier i z) * ((F z : ℝ) : ℂ))
          = ((F z : ℝ) : ℂ) * (P z * (starRingEnd ℂ) (mFourier i z)) by ring]
      simp [Complex.mul_re]
    have key : 0 ≤ Complex.normSq (P z - mFourier i z * ((F z : ℝ) : ℂ)) * Jh z :=
      mul_nonneg (Complex.normSq_nonneg _) hz.le
    refine le_trans key (le_of_eq ?_)
    rw [Complex.normSq_sub, hnormB, hcross]
    linear_combination (F z - 2 * (P z * (starRingEnd ℂ) (mFourier i z)).re) * hFz
  have hnonneg : 0 ≤ ∫ z, Complex.normSq (P z) * Jh z + F z
      - 2 * (P z * (starRingEnd ℂ) (mFourier i z)).re := integral_nonneg_of_ae hnn
  have hIsum : Integrable fun z : UnitAddTorus d ↦ Complex.normSq (P z) * Jh z + F z :=
    hInormSq.add hIF
  have hIlin2 : Integrable fun z : UnitAddTorus d ↦
      2 * (P z * (starRingEnd ℂ) (mFourier i z)).re := hIlin.const_mul 2
  rw [integral_sub hIsum hIlin2, integral_add hInormSq hIF, integral_const_mul, hlin] at hnonneg
  rw [hquad]
  linarith

/-- **Georgii's condition (13.27) from the spectral integrability of `Ĵ⁻¹`.** Every diagonal entry
`𝒥_Λ⁻¹(i,i)` of the inverse of a coupling matrix is at most `∫_G Ĵ(z)⁻¹ dz`; in particular the
suprema in (13.27) are finite. -/
theorem gaussianCovEntry_le_integral_inv [LinearOrder (d → ℤ)] (hEven : ∀ n, J' (-n) = J' n)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (Λ : Finset (d → ℤ)) (i : d → ℤ) :
    MeasureTheory.GibbsMeasure.gaussianCovEntry (homogeneousCoupling J') Λ i i
      ≤ ∫ z, ((fourierHomogeneousCoupling J' z).re)⁻¹ := by
  by_cases hi : i ∈ Λ
  · obtain ⟨x, hx⟩ :=
      MeasureTheory.GibbsMeasure.exists_dotProduct_mulVec_eq_gaussianCovEntry (hPD Λ) hi
    rw [← hx]
    exact two_mul_sub_dotProduct_gaussianCouplingMatrix_le_integral_inv hJ' hint hEven Λ x hi
  · rw [MeasureTheory.GibbsMeasure.gaussianCovEntry_of_notMem_left hi]
    exact integral_nonneg fun z ↦ inv_nonneg.2 (hpos z)

/-- **Georgii's condition (13.27)** holds for a homogeneous coupling as soon as `Ĵ ≥ 0` and
`∫_G Ĵ(z)⁻¹ dz < ∞`: the map `Λ ↦ 𝒥_Λ⁻¹(i,i)` is bounded above, uniformly in `Λ`. -/
theorem bddAbove_gaussianCovEntry_of_lintegral_inv_ne_top [LinearOrder (d → ℤ)]
    (hEven : ∀ n, J' (-n) = J' n)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (i : d → ℤ) :
    BddAbove (Set.range fun Λ : Finset (d → ℤ) ↦
      MeasureTheory.GibbsMeasure.gaussianCovEntry (homogeneousCoupling J') Λ i i) := by
  refine ⟨∫ z, ((fourierHomogeneousCoupling J' z).re)⁻¹, ?_⟩
  rintro _ ⟨Λ, rfl⟩
  exact gaussianCovEntry_le_integral_inv hJ' hint hEven hpos hPD Λ i

section Existence

variable [LinearOrder (d → ℤ)] (hEven : ∀ n, J' (-n) = J' n) (hFin : {n | J' n ≠ 0}.Finite)
  (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
  (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
include hEven hFin hPD hpos

/-- **Georgii Theorem (13.36), Step 1, with its witness (13.37)**: if `Ĵ ≥ 0` and
`∫_G Ĵ(z)⁻¹ dz < ∞`, then for every `m ∈ M_{J,h}` the translate `μ_C * δ_m` of the centred Gauss
field `μ_C` with the spectral covariance `C(i,j) = ∫_G z^{j-i} Ĵ(z)⁻¹ dz` is a Gibbs measure for
`γ^{J,h}`. (Finite range of `J'` is the standing hypothesis of `Potential.gaussianSpecification`,
not of Georgii's theorem, which only needs (13.34).) -/
theorem isGibbsMeasure_map_add_gaussianField_spectralCovariance {h : ℝ} {m : (d → ℤ) → ℝ}
    (hm : m ∈ gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h)) :
    (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ h) (symm_homogeneousCoupling hEven)
      (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos).IsGibbsMeasure
      ((ProbabilityTheory.gaussianField (spectralCovariance J')
        (posSemidef_covMatrix_spectralCovariance hJ' hint hpos)).map fun x ↦ x + m) := by
  refine MeasureTheory.GibbsMeasure.isGibbsMeasure_map_add_of_centered_of_isInverse
    (finite_setOf_homogeneousCoupling_ne_zero hFin)
    (ProbabilityTheory.isGaussianProcess_gaussianField _) ?_ (symm_homogeneousCoupling hEven) hPD
    (ProbabilityTheory.integral_eval_gaussianField _) hm
  intro i k
  simpa only [ProbabilityTheory.covariance_eval_gaussianField] using
    tsum_homogeneousCoupling_mul_spectralCovariance hJ' hint hEven i k

/-- **Georgii Theorem (13.36), the sufficiency half**: for a homogeneous `J` with `Ĵ ≥ 0`, if
`M_{J,h} ≠ ∅` and `∫_G Ĵ(z)⁻¹ dz < ∞` then `𝒢(γ^{J,h}) ≠ ∅`. -/
theorem nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top {h : ℝ}
    (hM : (gaussianMeanSet (homogeneousCoupling J') (fun _ ↦ h)).Nonempty) :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ h)
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1
      one_pos)).Nonempty := by
  obtain ⟨m, hm⟩ := hM
  exact ⟨_, Measure.isProbabilityMeasure_map (measurable_add_const m).aemeasurable,
    isGibbsMeasure_map_add_gaussianField_spectralCovariance hJ' hint hEven hFin hPD hpos hm⟩

end Existence

end Integrable

/-! ### The roots of `Ĵ` in `G` and the elements of `M_{J,0}` -/

section Roots

/-- For an even `J` the transform `Ĵ` is real, so it vanishes exactly where its real part does. -/
lemma fourierHomogeneousCoupling_eq_zero_iff (hEven : ∀ n, J' (-n) = J' n)
    (z : UnitAddTorus d) :
    fourierHomogeneousCoupling J' z = 0 ↔ (fourierHomogeneousCoupling J' z).re = 0 := by
  refine ⟨fun h ↦ by rw [h]; simp, fun h ↦ ?_⟩
  rw [← ofReal_re_fourierHomogeneousCoupling hEven, h, Complex.ofReal_zero]

/-- `|Re z^i| ≤ 1`: the configuration `(Re z^i)_{i ∈ S}` is bounded. -/
lemma abs_re_mFourier_le_one (n : d → ℤ) (z : UnitAddTorus d) : |(mFourier n z).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans_eq (norm_mFourier_apply n z)

/-- Shifting the argument of an absolutely summable trigonometric series multiplies it by a
monomial: `∑_{j ∈ S} J(j - i) z^j = z^i Ĵ(z)`. -/
lemma tsum_ofReal_sub_mul_mFourier (z : UnitAddTorus d) (i : d → ℤ) :
    ∑' j : d → ℤ, ((J' (j - i) : ℝ) : ℂ) * mFourier j z
      = mFourier i z * fourierHomogeneousCoupling J' z := by
  rw [← (Equiv.addRight i).tsum_eq fun j : d → ℤ ↦ ((J' (j - i) : ℝ) : ℂ) * mFourier j z,
    fourierHomogeneousCoupling, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right, mFourier_add]
  ring

/-- **Georgii's Step 2 in the proof of Remark (13.39)**: a root `z ∈ G` of `Ĵ` produces the
element `m = (Re z^i)_{i ∈ S}` of `M_{J,0}`, because
`∑_{j ∈ S} J(j - i) m_j = Re(z^i Ĵ(z)) = 0` for every `i ∈ S`. Since `m_0 = 1`, this element is
non-zero, and by `Potential.abs_re_mFourier_le_one` it is bounded. -/
theorem re_mFourier_mem_gaussianMeanSubmodule (hJ' : Summable fun n ↦ |J' n|)
    {z : UnitAddTorus d} (hz : fourierHomogeneousCoupling J' z = 0) :
    (fun i ↦ (mFourier i z).re) ∈ gaussianMeanSubmodule (homogeneousCoupling J') := by
  have hsum : ∀ i : d → ℤ, Summable fun j : d → ℤ ↦ |J' (j - i)| := fun i ↦
    (Equiv.subRight i).summable_iff.2 hJ'
  rw [mem_gaussianMeanSubmodule_iff]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · refine Summable.of_nonneg_of_le (fun j ↦ abs_nonneg _) (fun j ↦ ?_) (hsum i)
    rw [homogeneousCoupling_apply, abs_mul]
    calc |J' (j - i)| * |(mFourier j z).re| ≤ |J' (j - i)| * 1 := by
          gcongr
          exact abs_re_mFourier_le_one j z
      _ = |J' (j - i)| := mul_one _
  · have hc : Summable fun j : d → ℤ ↦ ((J' (j - i) : ℝ) : ℂ) * mFourier j z := by
      refine Summable.of_norm_bounded (g := fun j ↦ |J' (j - i)|) (hsum i) fun j ↦ ?_
      simp
    have hre : ∑' j, homogeneousCoupling J' i j * (mFourier j z).re
        = (∑' j : d → ℤ, ((J' (j - i) : ℝ) : ℂ) * mFourier j z).re := by
      rw [Complex.re_tsum hc]
      exact tsum_congr fun j ↦ by simp [homogeneousCoupling]
    simp only [Pi.zero_apply, zero_add]
    rw [hre, tsum_ofReal_sub_mul_mFourier, hz, mul_zero, Complex.zero_re]

/-- The element `(Re z^i)_{i ∈ S}` of `M_{J,0}` is non-zero: its value at `i = 0` is `1`. -/
lemma re_mFourier_ne_zero (z : UnitAddTorus d) : (fun i ↦ (mFourier i z).re) ≠ 0 := by
  intro hcon
  have h0 : ((mFourier (0 : d → ℤ)) z).re = 0 := congrFun hcon (0 : d → ℤ)
  rw [mFourier_zero, ContinuousMap.one_apply, Complex.one_re] at h0
  exact one_ne_zero h0

/-- **Georgii's conclusion in Remark (13.39), for a homogeneous `J`**: a root `z ∈ G` of `Ĵ`
makes `M_{J,0}` uncountable, since `m = (Re z^i)_{i ∈ S}` is a non-zero element of the linear
space `M_{J,0}`. -/
theorem not_countable_gaussianMeanSet_zero_homogeneousCoupling (hJ' : Summable fun n ↦ |J' n|)
    {z : UnitAddTorus d} (hz : fourierHomogeneousCoupling J' z = 0) :
    ¬ (gaussianMeanSet (homogeneousCoupling J') 0).Countable :=
  not_countable_gaussianMeanSet_zero _ (re_mFourier_mem_gaussianMeanSubmodule hJ' hz)
    (re_mFourier_ne_zero z)

/-- **Georgii's conclusion in Remark (13.39)**: a root `z ∈ G` of `Ĵ` makes every non-empty
`M_{J,h}` uncountable, `M_{J,h}` being a coset of `M_{J,0}`. -/
theorem not_countable_gaussianMeanSet_homogeneousCoupling (hJ' : Summable fun n ↦ |J' n|)
    {z : UnitAddTorus d} (hz : fourierHomogeneousCoupling J' z = 0) {h m₀ : (d → ℤ) → ℝ}
    (hm₀ : m₀ ∈ gaussianMeanSet (homogeneousCoupling J') h) :
    ¬ (gaussianMeanSet (homogeneousCoupling J') h).Countable :=
  not_countable_gaussianMeanSet _ hm₀ (re_mFourier_mem_gaussianMeanSubmodule hJ' hz)
    (re_mFourier_ne_zero z)

/-- **A root of `Ĵ` gives a continuous symmetry of `γ^{J,h}`.** If `Ĵ(z) = 0` then, by Remark
(13.23)(c), the one-parameter group `τ^{t m}` of spin translations along the bounded non-zero
element `m = (Re z^i)_{i ∈ S}` of `M_{J,0}` leaves `γ^{J,h}` invariant, for every `h`. -/
theorem isInvariant_spinTranslation_re_mFourier [LinearOrder (d → ℤ)]
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    {z : UnitAddTorus d} (hz : fourierHomogeneousCoupling J' z = 0) (h : (d → ℤ) → ℝ) (t : ℝ) :
    Specification.IsInvariant
      (MeasureTheory.GibbsMeasure.spinTranslation (t • fun i ↦ (mFourier i z).re))
      (gaussianSpecification (homogeneousCoupling J') h (symm_homogeneousCoupling hEven)
        (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos) :=
  isInvariant_spinTranslation_gaussianSpecification _ (symm_homogeneousCoupling hEven)
    (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1 one_pos h
    ((gaussianMeanSubmodule (homogeneousCoupling J')).smul_mem t
      (re_mFourier_mem_gaussianMeanSubmodule hJ' hz))

end Roots

/-! ### `Ĵ` without roots: `Ĵ⁻¹` is bounded, so `𝒢(γ^{J,h}) ≠ ∅` -/

section NoRoot

/-- **Georgii's remark preceding Corollary (13.40)**: "if `Ĵ ≠ 0` on `G` then the continuity of
`Ĵ` implies that `Ĵ⁻¹` is bounded and therefore integrable." -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_pos
    (hJ' : Summable fun n ↦ |J' n|)
    (hpos : ∀ z, 0 < (fourierHomogeneousCoupling J' z).re) :
    ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞ := by
  obtain ⟨z₀, -, hz₀⟩ := (isCompact_univ (X := UnitAddTorus d)).exists_isMinOn
    Set.univ_nonempty (Complex.continuous_re.comp
      (continuous_fourierHomogeneousCoupling hJ')).continuousOn
  have hmin : ∀ z, (fourierHomogeneousCoupling J' z₀).re ≤ (fourierHomogeneousCoupling J' z).re :=
    fun z ↦ isMinOn_iff.1 hz₀ z (Set.mem_univ z)
  have hb : ∀ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹
      ≤ (ENNReal.ofReal (fourierHomogeneousCoupling J' z₀).re)⁻¹ :=
    fun z ↦ ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hmin z))
  have hle : ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹
      ≤ (ENNReal.ofReal (fourierHomogeneousCoupling J' z₀).re)⁻¹ := by
    calc ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹
        ≤ ∫⁻ _ : UnitAddTorus d, (ENNReal.ofReal (fourierHomogeneousCoupling J' z₀).re)⁻¹ :=
          lintegral_mono hb
      _ = (ENNReal.ofReal (fourierHomogeneousCoupling J' z₀).re)⁻¹ := by
          rw [lintegral_const, measure_univ, mul_one]
  refine ne_top_of_le_ne_top ?_ hle
  rw [ENNReal.inv_ne_top, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact hpos z₀

/-- **Georgii's remark preceding Corollary (13.40)**: if `Ĵ` has no root in `G` then
`𝒢(γ^{J,h}) ≠ ∅` for every constant external field `h`, because `Ĵ(1) = ∑_n J(n) ≠ 0` puts the
constant `-h/Ĵ(1)` in `M_{J,h}` and `Ĵ⁻¹` is bounded. -/
theorem nonempty_G_homogeneousCoupling_of_pos [LinearOrder (d → ℤ)]
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 < (fourierHomogeneousCoupling J' z).re) (h : ℝ) :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ h)
      (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin) hPD 1
      one_pos)).Nonempty := by
  have hne : (∑' n, J' n) ≠ 0 := by
    have h0 := hpos 0
    rw [fourierHomogeneousCoupling_zero, Complex.ofReal_re] at h0
    exact h0.ne'
  exact nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top hJ'
    (lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_pos hJ' hpos) hEven hFin hPD
    (fun z ↦ (hpos z).le) (nonempty_gaussianMeanSet_of_tsum_ne_zero hJ' hne h)

end NoRoot

/-! ### Georgii Corollary (13.42): the spectral measure of a Gaussian Gibbs measure

A centred Gauss field on `ℤ^d` is shift-invariant if and only if its covariance function `C` is
homogeneous, and then `C(i,j) = ∫_G z^{j-i} α(dz)` (Georgii (13.38)) for a unique finite measure
`α` on the dual group `G`, *the spectral measure* of the field. The results in this section are
stated for the centred Gauss field attached to a given finite spectral measure `α`; the section
`Georgii Proposition (13.A9) applied` below removes that parametrisation using Herglotz's lemma
(`UnitAddTorus.exists_isFiniteMeasure_integral_mFourier_eq`), and reaches Corollary (13.42) for an
arbitrary centred Gauss field with homogeneous covariance. Since a real, even, nonnegative
definite `C` forces `α` to be invariant under `z ↦ -z` (its Fourier–Stieltjes coefficients are then
real and even, and `UnitAddTorus.ext_of_integral_mFourier_eq` identifies `α` with its reflection),
that invariance is carried as a hypothesis here.

The content of Corollary (13.42) is then
`isGibbsMeasure_gaussianField_spectralCovarianceOfMeasure_iff`:
`μ_α ∈ 𝒢(γ^{J,0})` if and only if `α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`.
-/

section Spectral

/-- `ite` does not depend on the `Decidable` instance used to elaborate it. -/
private lemma ite_eq_ite_of_subsingleton {P : Prop} (h1 h2 : Decidable P) (a b : ℝ) :
    @ite ℝ P h1 a b = @ite ℝ P h2 a b := by rw [Subsingleton.elim h1 h2]


/-- Georgii (13.38). -/
def spectralCovarianceOfMeasure (α : Measure (UnitAddTorus d)) (i j : d → ℤ) : ℝ :=
  ∫ z, (mFourier (j - i) z).re ∂α

variable {α : Measure (UnitAddTorus d)}

lemma spectralCovarianceOfMeasure_symm (i j : d → ℤ) :
    spectralCovarianceOfMeasure α i j = spectralCovarianceOfMeasure α j i := by
  have h : ∀ z : UnitAddTorus d, (mFourier (i - j) z).re = (mFourier (j - i) z).re := fun z ↦ by
    rw [← neg_sub j i, mFourier_neg, Complex.conj_re]
  simp only [spectralCovarianceOfMeasure, h]

lemma sum_sum_mul_re_mFourier_sub (I : Finset (d → ℤ)) (x : (d → ℤ) → ℝ) (z : UnitAddTorus d) :
    ∑ i ∈ I, ∑ j ∈ I, x i * x j * (mFourier (j - i) z).re
      = Complex.normSq (∑ j ∈ I, ((x j : ℝ) : ℂ) * mFourier j z) := by
  have hkey : ((Complex.normSq (∑ j ∈ I, ((x j : ℝ) : ℂ) * mFourier j z) : ℝ) : ℂ)
      = ∑ i ∈ I, ∑ j ∈ I, ((x i * x j : ℝ) : ℂ) * mFourier (j - i) z := by
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, Complex.conj_ofReal, mFourier_sub]
    push_cast
    ring
  have hre := congrArg Complex.re hkey
  rw [Complex.ofReal_re] at hre
  rw [hre, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Complex.re_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [Complex.mul_re]

/-- The covariance function attached to a finite spectral measure is nonnegative definite. -/
theorem posSemidef_covMatrix_spectralCovarianceOfMeasure [IsFiniteMeasure α]
    (I : Finset (d → ℤ)) :
    (ProbabilityTheory.covMatrix (spectralCovarianceOfMeasure α) I).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x ↦ ?_⟩
  · exact Matrix.IsHermitian.ext fun a b ↦ by
      simpa using spectralCovarianceOfMeasure_symm (α := α) b.1 a.1
  · rw [star_trivial, dotProduct_covMatrix_mulVec_eq_sum]
    set xe : (d → ℤ) → ℝ := Function.extend Subtype.val x 0 with hxe
    have hint : ∀ i j : d → ℤ, Integrable
        (fun z ↦ xe i * xe j * (mFourier (j - i) z).re) α :=
      fun i j ↦ (integrable_re_mFourier α (j - i)).const_mul _
    have hswap : ∑ i ∈ I, ∑ j ∈ I, xe i * xe j * spectralCovarianceOfMeasure α i j
        = ∫ z, ∑ i ∈ I, ∑ j ∈ I, xe i * xe j * (mFourier (j - i) z).re ∂α := by
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum _ fun j _ ↦ hint i j]
      exact Finset.sum_congr rfl fun j _ ↦ (integral_const_mul _ _).symm
    rw [hswap]
    refine integral_nonneg fun z ↦ ?_
    rw [sum_sum_mul_re_mFourier_sub]
    exact Complex.normSq_nonneg _

/-- The pointwise identity behind Georgii's computation: for an absolutely summable even `J'`,
`∑_{n} J'(n) Re(z^{m-n}) = Ĵ(z) Re(z^m)`. -/
lemma tsum_mul_re_mFourier_sub (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (m : d → ℤ) (z : UnitAddTorus d) :
    ∑' n : d → ℤ, J' n * (mFourier (m - n) z).re
      = (fourierHomogeneousCoupling J' z).re * (mFourier m z).re := by
  have hsum : Summable fun n : d → ℤ ↦ ((J' n : ℝ) : ℂ) * mFourier (m - n) z := by
    refine Summable.of_norm_bounded (g := fun n ↦ |J' n|) hJ' fun n ↦ ?_
    simp
  have hcplx : ∑' n : d → ℤ, ((J' n : ℝ) : ℂ) * mFourier (m - n) z
      = mFourier m z * fourierHomogeneousCoupling J' z := by
    have hpt : ∀ n : d → ℤ, ((J' n : ℝ) : ℂ) * mFourier (m - n) z
        = mFourier m z * (((J' (-n) : ℝ) : ℂ) * mFourier (-n) z) := by
      intro n
      rw [sub_eq_add_neg, mFourier_add, hEven]
      ring
    have hneg : ∑' n : d → ℤ, ((J' (-n) : ℝ) : ℂ) * mFourier (-n) z
        = ∑' n : d → ℤ, ((J' n : ℝ) : ℂ) * mFourier n z := by
      simpa using (Equiv.neg (d → ℤ)).tsum_eq
        fun n : d → ℤ ↦ ((J' n : ℝ) : ℂ) * mFourier n z
    simp_rw [hpt]
    rw [tsum_mul_left, hneg]
    rfl
  have hre := congrArg Complex.re hcplx
  rw [Complex.re_tsum hsum] at hre
  rw [show (∑' n : d → ℤ, (((J' n : ℝ) : ℂ) * mFourier (m - n) z).re)
      = ∑' n : d → ℤ, J' n * (mFourier (m - n) z).re from tsum_congr fun n ↦ by
        simp [Complex.mul_re]] at hre
  rw [hre, ← ofReal_re_fourierHomogeneousCoupling hEven]
  simp [Complex.mul_re, mul_comm]

/-- **Georgii's computation in the proof of Corollary (13.42)**: the covariance function of the
centred Gauss field with spectral measure `α` satisfies
`∑_j J(j - i) C(j,k) = ∫_G Ĵ(z) Re z^{k-i} α(dz)`. -/
theorem tsum_homogeneousCoupling_mul_spectralCovarianceOfMeasure [IsFiniteMeasure α]
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n) (i k : d → ℤ) :
    ∑' j, homogeneousCoupling J' i j * spectralCovarianceOfMeasure α j k
      = ∫ z, (fourierHomogeneousCoupling J' z).re * (mFourier (k - i) z).re ∂α := by
  have hreindex : ∑' j, homogeneousCoupling J' i j * spectralCovarianceOfMeasure α j k
      = ∑' n : d → ℤ, ∫ z, J' n * (mFourier ((k - i) - n) z).re ∂α := by
    rw [← (Equiv.addRight i).tsum_eq
      fun j : d → ℤ ↦ homogeneousCoupling J' i j * spectralCovarianceOfMeasure α j k]
    refine tsum_congr fun n ↦ ?_
    rw [integral_const_mul]
    simp only [Equiv.coe_addRight, homogeneousCoupling_apply, add_sub_cancel_right,
      spectralCovarianceOfMeasure]
    congr 2
    abel
  rw [hreindex]
  have hmeas : ∀ n : d → ℤ, AEStronglyMeasurable
      (fun z ↦ J' n * (mFourier ((k - i) - n) z).re) α :=
    fun n ↦ (integrable_re_mFourier α ((k - i) - n)).const_mul _ |>.aestronglyMeasurable
  have hfin : ∑' n : d → ℤ, ∫⁻ z, ‖J' n * (mFourier ((k - i) - n) z).re‖ₑ ∂α ≠ ∞ := by
    have hbd : ∀ n : d → ℤ, ∫⁻ z, ‖J' n * (mFourier ((k - i) - n) z).re‖ₑ ∂α
        ≤ ENNReal.ofReal |J' n| * α Set.univ := by
      intro n
      calc ∫⁻ z, ‖J' n * (mFourier ((k - i) - n) z).re‖ₑ ∂α
          ≤ ∫⁻ _ : UnitAddTorus d, ENNReal.ofReal |J' n| ∂α := by
            refine lintegral_mono fun z ↦ ?_
            rw [← ofReal_norm]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [Real.norm_eq_abs, abs_mul]
            calc |J' n| * |(mFourier ((k - i) - n) z).re| ≤ |J' n| * 1 := by
                  gcongr
                  exact abs_re_mFourier_le_one _ z
              _ = |J' n| := mul_one _
        _ = ENNReal.ofReal |J' n| * α Set.univ := by rw [lintegral_const]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbd)
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ (measure_ne_top α _)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ abs_nonneg _) hJ']
    exact ENNReal.ofReal_ne_top
  rw [← integral_tsum hmeas hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  exact tsum_mul_re_mFourier_sub hJ' hEven (k - i) z

/-! ### The criterion `Ĵ(z) α(dz) = dz` -/

section Criterion

variable [IsFiniteMeasure α]

/-- For an even `J'` the transform `Ĵ` is an even function on `G`. -/
lemma fourierHomogeneousCoupling_neg (hEven : ∀ n, J' (-n) = J' n) (z : UnitAddTorus d) :
    fourierHomogeneousCoupling J' (-z) = fourierHomogeneousCoupling J' z := by
  have hneg : ∑' n : d → ℤ, ((J' (-n) : ℝ) : ℂ) * mFourier (-n) z
      = ∑' n : d → ℤ, ((J' n : ℝ) : ℂ) * mFourier n z := by
    simpa using (Equiv.neg (d → ℤ)).tsum_eq fun n : d → ℤ ↦ ((J' n : ℝ) : ℂ) * mFourier n z
  calc fourierHomogeneousCoupling J' (-z)
      = ∑' n : d → ℤ, ((J' (-n) : ℝ) : ℂ) * mFourier (-n) z := by
        refine tsum_congr fun n ↦ ?_
        rw [hEven, mFourier_apply_neg]
    _ = fourierHomogeneousCoupling J' z := hneg

-- `Fintype d` is invisible in the statement but supplies the `BorelSpace (UnitAddTorus d)` and
-- `CompactSpace (UnitAddTorus d)` instances used in the proof.
set_option linter.unusedFintypeInType false in
/-- Every continuous function on the (compact) torus is integrable against a finite measure. -/
private lemma integrable_of_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : UnitAddTorus d → F} (hg : Continuous g) : Integrable g α :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

variable (hJ' : Summable fun n ↦ |J' n|)
include hJ'

lemma continuous_re_fourierHomogeneousCoupling :
    Continuous fun z ↦ (fourierHomogeneousCoupling J' z).re :=
  Complex.continuous_re.comp (continuous_fourierHomogeneousCoupling hJ')

/-- **Reality of `∫_G Ĵ(z) z^n α(dz)` for a spectral measure invariant under `z ↦ -z`.** -/
lemma integral_ofReal_re_fourier_mul_mFourier (hEven : ∀ n, J' (-n) = J' n)
    (hsymm : Measure.map (fun z : UnitAddTorus d ↦ -z) α = α) (n : d → ℤ) :
    ∫ z, (((fourierHomogeneousCoupling J' z).re : ℝ) : ℂ) * mFourier n z ∂α
      = ((∫ z, (fourierHomogeneousCoupling J' z).re * (mFourier n z).re ∂α : ℝ) : ℂ) := by
  set Jh : UnitAddTorus d → ℝ := fun z ↦ (fourierHomogeneousCoupling J' z).re with hJh
  have hJhc : Continuous Jh := continuous_re_fourierHomogeneousCoupling hJ'
  have hI : Integrable (fun z ↦ ((Jh z : ℝ) : ℂ) * mFourier n z) α :=
    integrable_of_continuous ((Complex.continuous_ofReal.comp hJhc).mul (mFourier n).continuous)
  -- the imaginary part vanishes by the symmetry `z ↦ -z`
  have hodd : ∀ z : UnitAddTorus d, Jh (-z) * (mFourier n (-z)).im = -(Jh z * (mFourier n z).im) :=
    fun z ↦ by
      simp only [hJh]
      rw [fourierHomogeneousCoupling_neg hEven, mFourier_apply_neg, mFourier_neg, Complex.conj_im]
      ring
  have him0 : ∫ z, Jh z * (mFourier n z).im ∂α = 0 := by
    set g : UnitAddTorus d → ℝ := fun z ↦ Jh z * (mFourier n z).im with hg
    have hgc : Continuous g := hJhc.mul (Complex.continuous_im.comp (mFourier n).continuous)
    have hstep : ∫ z, g z ∂α = ∫ z, g (-z) ∂α := by
      conv_lhs => rw [← hsymm]
      exact integral_map measurable_neg.aemeasurable hgc.aestronglyMeasurable
    rw [show (fun z : UnitAddTorus d ↦ g (-z)) = fun z ↦ -g z from funext hodd,
      integral_neg] at hstep
    linarith [hstep]
  have hre := Complex.reCLM.integral_comp_comm hI
  have him := Complex.imCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, ← hre]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by
      simp [hJh, Complex.mul_re])
  · rw [Complex.ofReal_im, ← him, ← him0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by
      simp [hJh, Complex.mul_im])

/-- The measure `Ĵ(z) α(dz)` is finite. -/
lemma isFiniteMeasure_withDensity_ofReal_re_fourier :
    IsFiniteMeasure (α.withDensity fun z ↦
      ENNReal.ofReal (fourierHomogeneousCoupling J' z).re) := by
  refine isFiniteMeasure_withDensity (ne_top_of_le_ne_top ?_
    (lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal
      ((le_abs_self _).trans (abs_re_fourierHomogeneousCoupling_le hJ' z))))
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top α _)

/-- **The criterion of Georgii Corollary (13.42).** For a finite spectral measure `α` on `G`
invariant under `z ↦ -z`, the covariance function `C(i,j) = ∫_G z^{j-i} α(dz)` is an inverse of a
homogeneous `J` in the sense of Theorem (13.22) if and only if `Ĵ(z) α(dz) = dz`. -/
theorem withDensity_ofReal_re_fourier_eq_volume_iff (hEven : ∀ n, J' (-n) = J' n)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hsymm : Measure.map (fun z : UnitAddTorus d ↦ -z) α = α) :
    (α.withDensity fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re) = volume
      ↔ ∀ i k : d → ℤ, ∑' j, homogeneousCoupling J' i j * spectralCovarianceOfMeasure α j k
          = if i = k then 1 else 0 := by
  have hfin := isFiniteMeasure_withDensity_ofReal_re_fourier (α := α) hJ'
  have hJdmeas : Measurable fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re :=
    (continuous_re_fourierHomogeneousCoupling hJ').measurable.ennreal_ofReal
  -- the Fourier–Stieltjes coefficients of `Ĵ α`
  have hcoeff : ∀ n : d → ℤ,
      ∫ z, mFourier n z ∂(α.withDensity fun z ↦
        ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)
      = ((∫ z, (fourierHomogeneousCoupling J' z).re * (mFourier n z).re ∂α : ℝ) : ℂ) := by
    intro n
    rw [integral_withDensity_eq_integral_toReal_smul hJdmeas
      (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top),
      ← integral_ofReal_re_fourier_mul_mFourier hJ' hEven hsymm n]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hpos z), Complex.real_smul]
  -- the criterion, first in terms of the coefficients
  have hstep : (α.withDensity fun z ↦
        ENNReal.ofReal (fourierHomogeneousCoupling J' z).re) = volume
      ↔ ∀ n : d → ℤ, ∫ z, (fourierHomogeneousCoupling J' z).re * (mFourier n z).re ∂α
          = if n = 0 then 1 else 0 := by
    constructor
    · intro hEq n
      have hn := hcoeff n
      rw [hEq, integral_mFourier] at hn
      rw [← Complex.ofReal_inj, ← hn]
      split_ifs <;> simp
    · intro hn
      refine ext_of_integral_mFourier_eq fun n ↦ ?_
      rw [hcoeff n, integral_mFourier, hn n]
      split_ifs <;> simp
  rw [hstep]
  constructor
  · intro hn i k
    rw [tsum_homogeneousCoupling_mul_spectralCovarianceOfMeasure hJ' hEven, hn (k - i)]
    by_cases hik : i = k
    · simp [hik]
    · simp [hik, sub_ne_zero.2 (Ne.symm hik)]
  · intro hik n
    have hn := hik 0 n
    rw [tsum_homogeneousCoupling_mul_spectralCovarianceOfMeasure hJ' hEven, sub_zero] at hn
    rw [hn]
    by_cases h0 : n = 0
    · simp [h0]
    · simp [h0, Ne.symm h0]

end Criterion

/-! ### Georgii Corollary (13.42) -/

section Georgii1342

/-- **Georgii's measure `Ĵ(z)⁻¹ dz`** on the dual group `G`, with Georgii's convention `1/0 = ∞`
(so a *finite* `Ĵ⁻¹ dz` forces `Ĵ ≠ 0` almost everywhere). -/
def spectralMeasure (J' : (d → ℤ) → ℝ) : Measure (UnitAddTorus d) :=
  volume.withDensity fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹

/-- `Ĵ · Ĵ⁻¹` is the indicator of `{Ĵ ≠ 0}` (Georgii's convention `1/0 = ∞`). -/
private lemma mul_inv_ofReal_re_fourier
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) :
    ((fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)
        * fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹)
      = {z | (fourierHomogeneousCoupling J' z).re ≠ 0}.indicator 1 := by
  funext z
  rcases eq_or_lt_of_le (hpos z) with h | h
  · simp [← h]
  · have hz : ENNReal.ofReal (fourierHomogeneousCoupling J' z).re ≠ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using not_le.2 h
    simp [h.ne', ENNReal.mul_inv_cancel hz ENNReal.ofReal_ne_top]

variable (hJ' : Summable fun n ↦ |J' n|)
include hJ'

/-- **Georgii's decomposition of the spectral measure, Corollary (13.42).** For a finite `α`,
`Ĵ(z) α(dz) = dz` if and only if `α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`. -/
theorem withDensity_ofReal_re_fourier_eq_volume_iff_exists [IsFiniteMeasure α]
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re) :
    (α.withDensity fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re) = volume
      ↔ ∃ α₀ : Measure (UnitAddTorus d),
          α₀ {z | (fourierHomogeneousCoupling J' z).re ≠ 0} = 0 ∧ α = spectralMeasure J' + α₀ := by
  have hJhc : Continuous fun z ↦ (fourierHomogeneousCoupling J' z).re :=
    continuous_re_fourierHomogeneousCoupling hJ'
  have hJdmeas : Measurable fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re :=
    hJhc.measurable.ennreal_ofReal
  have hJdinv : Measurable fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ :=
    hJdmeas.inv
  have hmeas : MeasurableSet {z : UnitAddTorus d | (fourierHomogeneousCoupling J' z).re ≠ 0} :=
    hJhc.measurable (measurableSet_singleton (0 : ℝ)).compl
  constructor
  · intro hEq
    refine ⟨α.restrict {z | (fourierHomogeneousCoupling J' z).re ≠ 0}ᶜ, ?_, ?_⟩
    · rw [Measure.restrict_apply hmeas, Set.inter_compl_self, measure_empty]
    · have hrestr : α.restrict {z | (fourierHomogeneousCoupling J' z).re ≠ 0}
          = spectralMeasure J' := by
        rw [spectralMeasure, ← hEq, ← withDensity_mul _ hJdmeas hJdinv,
          mul_inv_ofReal_re_fourier hpos, withDensity_indicator_one hmeas]
      rw [← hrestr]
      exact (Measure.restrict_add_restrict_compl (μ := α) hmeas).symm
  · rintro ⟨α₀, hα₀, rfl⟩
    have hvol0 : volume {z : UnitAddTorus d | (fourierHomogeneousCoupling J' z).re ≠ 0}ᶜ = 0 := by
      by_contra hcon
      have hinf : spectralMeasure J' {z | (fourierHomogeneousCoupling J' z).re ≠ 0}ᶜ = ∞ := by
        rw [spectralMeasure, withDensity_apply _ hmeas.compl]
        have hpt : ∀ z ∈ {z : UnitAddTorus d | (fourierHomogeneousCoupling J' z).re ≠ 0}ᶜ,
            (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ = ∞ := by
          intro z hz
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hz
          simp [hz]
        rw [setLIntegral_congr_fun hmeas.compl hpt, setLIntegral_const]
        simpa using ENNReal.top_mul hcon
      have hle : spectralMeasure J' {z | (fourierHomogeneousCoupling J' z).re ≠ 0}ᶜ
          ≤ (spectralMeasure J' + α₀) Set.univ := le_trans
            (measure_mono (Set.subset_univ _)) (Measure.le_add_right le_rfl _)
      rw [hinf] at hle
      exact (measure_ne_top (spectralMeasure J' + α₀) Set.univ) (top_le_iff.1 hle)
    rw [withDensity_add_measure]
    have hα₀0 : α₀.withDensity
        (fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re) = 0 := by
      rw [withDensity_congr_ae (g := 0) ?_, withDensity_zero]
      refine Filter.Eventually.mono (compl_mem_ae_iff.2 hα₀) fun z hz ↦ ?_
      simp only [Set.mem_ofPred_eq, not_not] at hz
      simp [hz]
    rw [hα₀0, add_zero, spectralMeasure, ← withDensity_mul _ hJdinv hJdmeas,
      show ((fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹)
          * fun z ↦ ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)
        = {z | (fourierHomogeneousCoupling J' z).re ≠ 0}.indicator 1 from by
        rw [mul_comm]; exact mul_inv_ofReal_re_fourier hpos,
      withDensity_indicator_one hmeas]
    exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hvol0)

variable [LinearOrder (d → ℤ)]

/-- **Georgii Corollary (13.42).** Let `J : ℤ^d → ℝ` be even, absolutely summable and of finite
range, with `Ĵ ≥ 0` and every `𝒥_Λ` positive definite, and let `α` be a finite measure on the dual
group `G` invariant under `z ↦ -z` — that is, the spectral measure of a *centred, shift-invariant*
Gauss field `μ`, whose covariance function is then `C(i,j) = ∫_G z^{j-i} α(dz)` (Georgii (13.38)).
Then `μ ∈ 𝒢(γ^{J,0})` if and only if

`α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`,

equivalently `Ĵ(z) α(dz) = dz`.

The proof is Georgii's: by Theorem (13.22) — here `MeasureTheory.GibbsMeasure.georgii_13_22_iff`,
whose mean condition `0 ∈ M_{J,0}` is automatic — `μ ∈ 𝒢(γ^{J,0})` iff `C` inverts `J`, and
`∑_j J(j-i) C(j,k) = ∫_G Ĵ(z) z^{k-i} α(dz)`; since the trigonometric polynomials are dense
(`UnitAddTorus.ext_of_integral_mFourier_eq`), this equals `δ_{ik}` for all `i, k` iff `Ĵ α` is
the Haar measure. -/
theorem isGibbsMeasure_gaussianField_spectralCovarianceOfMeasure_iff [IsFiniteMeasure α]
    (hEven : ∀ n, J' (-n) = J' n) (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    (hsymm : Measure.map (fun z : UnitAddTorus d ↦ -z) α = α) :
    (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
        (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin)
        hPD 1 one_pos).IsGibbsMeasure
        (ProbabilityTheory.gaussianField (spectralCovarianceOfMeasure α)
          fun I ↦ posSemidef_covMatrix_spectralCovarianceOfMeasure I)
      ↔ ∃ α₀ : Measure (UnitAddTorus d),
          α₀ {z | (fourierHomogeneousCoupling J' z).re ≠ 0} = 0 ∧ α = spectralMeasure J' + α₀ := by
  rw [← withDensity_ofReal_re_fourier_eq_volume_iff_exists hJ' hpos,
    withDensity_ofReal_re_fourier_eq_volume_iff hJ' hEven hpos hsymm,
    MeasureTheory.GibbsMeasure.georgii_13_22_iff _ _ _
      (ProbabilityTheory.isGaussianProcess_gaussianField _)]
  simp only [ProbabilityTheory.covariance_eval_gaussianField,
    ProbabilityTheory.integral_eval_gaussianField]
  -- the two sides differ only in the `Decidable (i = k)` instance
  constructor
  · rintro ⟨-, h⟩ i k
    exact (h i k).trans (ite_eq_ite_of_subsingleton _ _ 1 0)
  · intro h
    refine ⟨(gaussianMeanSubmodule (homogeneousCoupling J')).zero_mem, fun i k ↦ ?_⟩
    exact (h i k).trans (ite_eq_ite_of_subsingleton _ _ 1 0)

end Georgii1342

/-! ### Consistency with the spectral covariance (13.37) -/

section Consistency

variable (hJ' : Summable fun n ↦ |J' n|)
  (hint : ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞)
include hJ' hint

omit hJ' in
/-- Under `∫_G Ĵ⁻¹ dz < ∞`, Georgii's measure `Ĵ⁻¹ dz` is finite. -/
theorem isFiniteMeasure_spectralMeasure : IsFiniteMeasure (spectralMeasure J') :=
  isFiniteMeasure_withDensity hint

/-- **The two spectral covariances agree.** Georgii's (13.37), `C(i,j) = ∫_G z^{j-i} Ĵ(z)⁻¹ dz`,
is the covariance function (13.38) of the measure `Ĵ⁻¹ dz`. -/
theorem spectralCovariance_eq_spectralCovarianceOfMeasure (i j : d → ℤ) :
    spectralCovariance J' i j = spectralCovarianceOfMeasure (spectralMeasure J') i j := by
  have hJdinv : Measurable fun z ↦ (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ :=
    (Complex.continuous_re.comp
      (continuous_fourierHomogeneousCoupling hJ')).measurable.ennreal_ofReal.inv
  have hlt : ∀ᵐ z : UnitAddTorus d ∂volume,
      (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ < ∞ := by
    filter_upwards [ae_pos_re_fourierHomogeneousCoupling hJ' hint] with z hz
    simpa [ENNReal.inv_lt_top, ENNReal.ofReal_pos] using hz
  rw [spectralCovarianceOfMeasure, spectralMeasure,
    integral_withDensity_eq_integral_toReal_smul hJdinv hlt]
  have hpt : ∀ᵐ z : UnitAddTorus d ∂volume,
      ((ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹).toReal
          • (mFourier (j - i) z).re
        = (mFourier (j - i) z).re * ((fourierHomogeneousCoupling J' z).re)⁻¹ := by
    filter_upwards [ae_pos_re_fourierHomogeneousCoupling hJ' hint] with z hz
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hz.le, smul_eq_mul, mul_comm]
  rw [integral_congr_ae hpt, spectralCovariance, mFourierCoeff, ← neg_sub j i, neg_neg]
  have hI : Integrable (fun z : UnitAddTorus d ↦
      mFourier (j - i) z • (((((fourierHomogeneousCoupling J' z).re)⁻¹ : ℝ) : ℂ))) := by
    simp only [smul_eq_mul]
    exact Integrable.bdd_mul (c := 1)
      ((integrable_inv_re_fourierHomogeneousCoupling hJ' hint).ofReal)
      (mFourier (j - i)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by simp)
  have hre := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp [Complex.mul_re]

end Consistency

/-! ### Georgii Proposition (13.A9) applied: Corollary (13.42) for an arbitrary Gauss field

Herglotz's lemma — `UnitAddTorus.exists_isFiniteMeasure_integral_mFourier_eq` in
`GibbsMeasure/Mathlib/Analysis/Fourier/AddCircleMultiHerglotz.lean` — turns a homogeneous
nonnegative definite covariance function into a spectral measure, so the results above apply to
*every* centred Gauss field with homogeneous covariance, which is Georgii's Corollary (13.42) as
stated. -/

section HerglotzApplication

variable {c : (d → ℤ) → ℝ}

omit [Fintype d] in
/-- A nonnegative definite `c : ℤ^d → ℝ` gives a nonnegative definite homogeneous covariance
function `C(i,j) = c(j - i)`; the two conditions differ by a transpose. -/
theorem posSemidef_covMatrix_homogeneousCoupling
    (hc : ∀ I : Finset (d → ℤ), (Matrix.of fun a b : I ↦ c (a.1 - b.1)).PosSemidef)
    (I : Finset (d → ℤ)) :
    (ProbabilityTheory.covMatrix (homogeneousCoupling c) I).PosSemidef := by
  have h : ProbabilityTheory.covMatrix (homogeneousCoupling c) I
      = (Matrix.of fun a b : I ↦ c (a.1 - b.1))ᵀ := rfl
  rw [h]
  exact (hc I).transpose

omit [Fintype d] in
/-- Conversely, a homogeneous covariance function of a Gauss field has nonnegative definite
Toeplitz matrices. -/
theorem posSemidef_toeplitz_of_isGaussianProcess {μ : Measure ((d → ℤ) → ℝ)}
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : (d → ℤ) → ℝ) ↦ ω i) μ)
    (hcov : ∀ i j, cov[fun ω : (d → ℤ) → ℝ ↦ ω i, fun ω : (d → ℤ) → ℝ ↦ ω j; μ] = c (j - i))
    (I : Finset (d → ℤ)) : (Matrix.of fun a b : I ↦ c (a.1 - b.1)).PosSemidef := by
  have hsub : (Matrix.of fun a b : I ↦
      cov[fun ω : (d → ℤ) → ℝ ↦ ω a.1, fun ω : (d → ℤ) → ℝ ↦ ω b.1; μ]).PosSemidef :=
    Matrix.PosSemidef.submatrix
      (MeasureTheory.GibbsMeasure.posSemidef_covar_of_isGaussianProcess hμ)
      fun a : I ↦ (a : d → ℤ)
  have h2 : (Matrix.of fun a b : I ↦
      cov[fun ω : (d → ℤ) → ℝ ↦ ω b.1, fun ω : (d → ℤ) → ℝ ↦ ω a.1; μ]).PosSemidef :=
    hsub.transpose
  have hEq : (Matrix.of fun a b : I ↦ c (a.1 - b.1))
      = Matrix.of fun a b : I ↦
          cov[fun ω : (d → ℤ) → ℝ ↦ ω b.1, fun ω : (d → ℤ) → ℝ ↦ ω a.1; μ] := by
    funext a b
    exact (hcov b.1 a.1).symm
  rw [hEq]
  exact h2

/-- **Georgii Proposition (13.A9) in the homogeneous setting.** A nonnegative definite
`c : ℤ^d → ℝ` is the Fourier–Stieltjes transform of a finite measure `α` on `G`, necessarily
invariant under `z ↦ -z`; `α` is the spectral measure of the centred Gauss field with covariance
`C(i,j) = c(j - i)`, in the sense of Georgii (13.38). -/
theorem exists_spectralCovarianceOfMeasure_eq
    (hc : ∀ I : Finset (d → ℤ), (Matrix.of fun a b : I ↦ c (a.1 - b.1)).PosSemidef) :
    ∃ α : Measure (UnitAddTorus d), IsFiniteMeasure α ∧
      Measure.map (fun z : UnitAddTorus d ↦ -z) α = α ∧
      (∀ n, ∫ z, mFourier n z ∂α = (c n : ℂ)) ∧
      spectralCovarianceOfMeasure α = homogeneousCoupling c := by
  obtain ⟨α, hαfin, hα⟩ := UnitAddTorus.exists_isFiniteMeasure_integral_mFourier_eq hc
  have := hαfin
  have hmapfin : IsFiniteMeasure (Measure.map (fun z : UnitAddTorus d ↦ -z) α) := by
    constructor
    rw [Measure.map_apply measurable_neg MeasurableSet.univ]
    exact measure_lt_top α _
  refine ⟨α, hαfin, ?_, hα, ?_⟩
  · refine ext_of_integral_mFourier_eq fun n ↦ ?_
    rw [integral_map measurable_neg.aemeasurable (mFourier n).continuous.aestronglyMeasurable]
    have hpt : ∀ z : UnitAddTorus d, mFourier n (-z) = mFourier (-n) z := fun z ↦ mFourier_apply_neg
    simp_rw [hpt]
    rw [hα (-n), hα n, UnitAddTorus.even_of_posSemidef_toeplitz hc n]
  · funext i j
    have hre := Complex.reCLM.integral_comp_comm (UnitAddTorus.integrable_mFourier α (j - i))
    simp only [Complex.reCLM_apply] at hre
    rw [spectralCovarianceOfMeasure, hre, hα (j - i), Complex.ofReal_re]
    rfl

variable [LinearOrder (d → ℤ)]

/-- **Georgii Corollary (13.42).** Let `μ` be a centred Gauss field on `ℤ^d` with *homogeneous*
covariance `cov[σ_i, σ_j] = c(j - i)` — by Georgii's remark preceding (13.42) these are exactly
the shift-invariant centred Gauss fields. Then `μ ∈ 𝒢(γ^{J,0})` if and only if the spectral
measure `α` of `μ`, the finite measure on `G` with `c(n) = ∫_G z^n α(dz)` supplied by Herglotz's
lemma, decomposes as `α(dz) = Ĵ(z)⁻¹ dz + α₀(dz)` with `α₀` carried by `{Ĵ = 0}`.

Georgii states the corollary for `𝒢_Θ(γ^{J,0})`; since `𝒢_Θ ⊆ 𝒢`, the version proved here is his
"only if" and slightly more than his "if". Turning it into his statement is the one missing step
recorded in the module docstring: that a centred Gauss field with homogeneous covariance is
shift-invariant. -/
theorem isGibbsMeasure_iff_exists_spectralMeasure_decomposition
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    {μ : Measure ((d → ℤ) → ℝ)}
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : (d → ℤ) → ℝ) ↦ ω i) μ)
    (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : (d → ℤ) → ℝ ↦ ω i, fun ω : (d → ℤ) → ℝ ↦ ω j; μ] = c (j - i)) :
    (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
        (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin)
        hPD 1 one_pos).IsGibbsMeasure μ
      ↔ ∃ α : Measure (UnitAddTorus d), IsFiniteMeasure α ∧
          (∀ n, ∫ z, mFourier n z ∂α = (c n : ℂ)) ∧
          ∃ α₀ : Measure (UnitAddTorus d),
            α₀ {z | (fourierHomogeneousCoupling J' z).re ≠ 0} = 0
              ∧ α = spectralMeasure J' + α₀ := by
  obtain ⟨α, hαfin, hαsymm, hαcoeff, hαC⟩ :=
    exists_spectralCovarianceOfMeasure_eq (posSemidef_toeplitz_of_isGaussianProcess hμ hcov)
  have := hαfin
  have hμeq : μ = ProbabilityTheory.gaussianField (spectralCovarianceOfMeasure α)
      fun I ↦ posSemidef_covMatrix_spectralCovarianceOfMeasure I := by
    have hP := hμ.isProbabilityMeasure
    refine ProbabilityTheory.eq_gaussianField _ hμ hmean fun i j ↦ ?_
    rw [hcov i j, hαC]
    rfl
  have hiff := isGibbsMeasure_gaussianField_spectralCovarianceOfMeasure_iff
    (α := α) hJ' hEven hFin hPD hpos hαsymm
  constructor
  · intro hG
    rw [hμeq] at hG
    exact ⟨α, hαfin, hαcoeff, hiff.1 hG⟩
  · rintro ⟨α', hα'fin, hα'coeff, hdec⟩
    have := hα'fin
    have hαα' : α' = α := ext_of_integral_mFourier_eq fun n ↦ by rw [hα'coeff, hαcoeff]
    rw [hμeq]
    exact hiff.2 (hαα' ▸ hdec)

/-- **The necessity half of Georgii Theorem (13.36), for a Gaussian Gibbs measure with homogeneous
covariance.** If a centred Gauss field with homogeneous covariance is a Gibbs measure for
`γ^{J,0}`, then `∫_G Ĵ(z)⁻¹ dz < ∞` (Georgii's convention `1/0 = ∞`): the spectral measure of the
field dominates `Ĵ⁻¹ dz` and is finite. -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_ne_top_of_isGibbsMeasure
    (hJ' : Summable fun n ↦ |J' n|) (hEven : ∀ n, J' (-n) = J' n)
    (hFin : {n : d → ℤ | J' n ≠ 0}.Finite)
    (hPD : ∀ Λ : Finset (d → ℤ), (gaussianCouplingMatrix (homogeneousCoupling J') Λ).PosDef)
    (hpos : ∀ z, 0 ≤ (fourierHomogeneousCoupling J' z).re)
    {μ : Measure ((d → ℤ) → ℝ)}
    (hμ : ProbabilityTheory.IsGaussianProcess (fun i (ω : (d → ℤ) → ℝ) ↦ ω i) μ)
    (hmean : ∀ i, ∫ ω, ω i ∂μ = 0)
    (hcov : ∀ i j, cov[fun ω : (d → ℤ) → ℝ ↦ ω i, fun ω : (d → ℤ) → ℝ ↦ ω j; μ] = c (j - i))
    (hG : (gaussianSpecification (homogeneousCoupling J') (fun _ ↦ (0 : ℝ))
        (symm_homogeneousCoupling hEven) (finite_setOf_homogeneousCoupling_ne_zero hFin)
        hPD 1 one_pos).IsGibbsMeasure μ) :
    ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ ≠ ∞ := by
  obtain ⟨α, hαfin, -, α₀, -, hdec⟩ :=
    (isGibbsMeasure_iff_exists_spectralMeasure_decomposition hJ' hEven hFin hPD hpos hμ hmean
      hcov).1 hG
  have := hαfin
  have hmass : spectralMeasure J' Set.univ
      = ∫⁻ z, (ENNReal.ofReal (fourierHomogeneousCoupling J' z).re)⁻¹ := by
    rw [spectralMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hle : spectralMeasure J' Set.univ ≤ α Set.univ := by
    rw [hdec]
    exact le_add_right le_rfl
  rw [← hmass]
  exact ne_top_of_le_ne_top (measure_ne_top α Set.univ) hle

end HerglotzApplication

end Spectral

/-! ### Georgii Example (13.43): the harmonic crystal -/

section HarmonicCrystal

variable [DecidableEq d]

variable (d) in
/-- **Georgii Example (13.43), the harmonic crystal**: `J(0) = β`, `J(±e_ℓ) = -β/(2d)` for the
`2d` unit vectors, `J = 0` otherwise, written as
`β·[n = 0] - β/(2d)·∑_ℓ ([n = e_ℓ] + [n = -e_ℓ])`. -/
def harmonicCrystalCoupling (β : ℝ) (n : d → ℤ) : ℝ :=
  β * (if n = 0 then 1 else 0)
    - β / (2 * Fintype.card d) * ∑ ℓ, ((if n = Pi.single ℓ 1 then 1 else 0)
      + (if n = -Pi.single ℓ 1 then 1 else 0))

variable {β : ℝ}

lemma harmonicCrystalCoupling_neg (n : d → ℤ) :
    harmonicCrystalCoupling d β (-n) = harmonicCrystalCoupling d β n := by
  simp only [harmonicCrystalCoupling, neg_eq_iff_eq_neg, neg_neg, neg_zero]
  congr 2
  exact Finset.sum_congr rfl fun ℓ _ ↦ add_comm _ _

/-- `∑_{n} (if n = a then 1 else 0) * f n = f a`, as a `HasSum`. -/
lemma hasSum_ite_eq_mul {α : Type*} [NonAssocSemiring α] [TopologicalSpace α]
    {ι : Type*} [DecidableEq ι] (a : ι) (f : ι → α) :
    HasSum (fun n ↦ (if n = a then (1 : α) else 0) * f n) (f a) := by
  convert hasSum_ite_eq a (f a) using 1
  funext n
  split_ifs with h <;> simp [h]

omit [DecidableEq d] in
/-- The trigonometric series of the harmonic crystal, as a `HasSum`: `∑_n J(n) z^n = β - β/(2d) ∑_ℓ
(z_ℓ + z_ℓ⁻¹)`. -/
lemma hasSum_harmonicCrystalCoupling_mul_mFourier [DecidableEq d] (z : UnitAddTorus d) :
    HasSum (fun n ↦ (harmonicCrystalCoupling d β n : ℂ) * mFourier n z)
      (β - β / (2 * Fintype.card d)
        * ∑ ℓ, (fourier 1 (z ℓ) + (starRingEnd ℂ) (fourier 1 (z ℓ)))) := by
  have h0 := hasSum_ite_eq_mul (α := ℂ) (0 : d → ℤ) (fun n ↦ mFourier n z)
  have h1 : ∀ ℓ : d, HasSum (fun n ↦ ((if n = Pi.single ℓ 1 then (1 : ℂ) else 0)
      + (if n = -Pi.single ℓ 1 then 1 else 0)) * mFourier n z)
      (fourier 1 (z ℓ) + (starRingEnd ℂ) (fourier 1 (z ℓ))) := fun ℓ ↦ by
    have := (hasSum_ite_eq_mul (α := ℂ) (Pi.single ℓ 1) (fun n ↦ mFourier n z)).add
      (hasSum_ite_eq_mul (α := ℂ) (-Pi.single ℓ 1) (fun n ↦ mFourier n z))
    simp only [mFourier_single, mFourier_neg] at this
    have heq : (fun n ↦ ((if n = Pi.single ℓ 1 then (1 : ℂ) else 0)
          + (if n = -Pi.single ℓ 1 then 1 else 0)) * mFourier n z)
        = fun n ↦ (if n = Pi.single ℓ 1 then (1 : ℂ) else 0) * mFourier n z
          + (if n = -Pi.single ℓ 1 then (1 : ℂ) else 0) * mFourier n z := by
      funext n; ring
    rw [heq]
    exact this
  have h2 := (h0.mul_left (β : ℂ)).sub ((hasSum_sum fun ℓ (_ : ℓ ∈ Finset.univ) ↦ h1 ℓ).mul_left
    ((β : ℂ) / (2 * Fintype.card d)))
  simp only [mFourier_zero, ContinuousMap.one_apply, mul_one] at h2
  have heq : (fun n ↦ (harmonicCrystalCoupling d β n : ℂ) * mFourier n z)
      = fun n ↦ (β : ℂ) * ((if n = 0 then (1 : ℂ) else 0) * mFourier n z)
        - (β : ℂ) / (2 * Fintype.card d) * ∑ ℓ, ((if n = Pi.single ℓ 1 then (1 : ℂ) else 0)
            + (if n = -Pi.single ℓ 1 then 1 else 0)) * mFourier n z := by
    funext n
    simp only [harmonicCrystalCoupling]
    push_cast [apply_ite ((↑) : ℝ → ℂ)]
    rw [sub_mul, mul_assoc, mul_assoc, Finset.sum_mul]
  rw [heq]
  exact h2

/-- **The Fourier transform of the harmonic crystal**, real part: `Re Ĵ(z) = β - β/d ∑_ℓ Re z_ℓ`.
-/
lemma re_fourierHomogeneousCoupling_harmonicCrystalCoupling (z : UnitAddTorus d) :
    (fourierHomogeneousCoupling (harmonicCrystalCoupling d β) z).re
      = β - β / Fintype.card d * ∑ ℓ, (fourier 1 (z ℓ)).re := by
  rw [fourierHomogeneousCoupling, (hasSum_harmonicCrystalCoupling_mul_mFourier z).tsum_eq]
  have h2 : ∑ ℓ, (fourier 1 (z ℓ) + (starRingEnd ℂ) (fourier 1 (z ℓ)))
      = 2 * ∑ ℓ, (((fourier 1 (z ℓ)).re : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓ _ ↦ by rw [Complex.add_conj]; push_cast; ring
  rw [h2]
  have key : ((β : ℂ) - (β : ℂ) / (2 * (Fintype.card d : ℂ))
        * (2 * ∑ ℓ, (((fourier 1 (z ℓ)).re : ℝ) : ℂ)))
      = ((β - β / Fintype.card d * ∑ ℓ, (fourier 1 (z ℓ)).re : ℝ) : ℂ) := by
    push_cast
    rcases eq_or_ne (Fintype.card d : ℂ) 0 with hd | hd
    · rw [hd]; simp
    · congr 1
      field_simp
  rw [key, Complex.ofReal_re]

/-- `Re Ĵ(z_p) = β/d ∑_ℓ (1 - cos 2π p_ℓ)` for `z_p = (p_ℓ mod 1)_ℓ`; Georgii's display in (13.43)
(with his `p ∈ ]-1, 1]` and `e^{iπp}` replaced by `p ∈ ]-1/2, 1/2]` and `e^{2πip}`). -/
lemma re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe [Nonempty d] (p : d → ℝ) :
    (fourierHomogeneousCoupling (harmonicCrystalCoupling d β)
        (fun ℓ ↦ (p ℓ : UnitAddCircle))).re
      = β / Fintype.card d * ∑ ℓ, (1 - Real.cos (2 * Real.pi * p ℓ)) := by
  rw [re_fourierHomogeneousCoupling_harmonicCrystalCoupling]
  have hre : ∀ ℓ, (fourier 1 ((p ℓ : ℝ) : UnitAddCircle)).re = Real.cos (2 * Real.pi * p ℓ) := by
    intro ℓ
    rw [fourier_coe_apply, ← Complex.exp_ofReal_mul_I_re]
    congr 2
    push_cast
    ring
  simp only [hre, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  have hd : (Fintype.card d : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- `Ĵ ≥ 0` for the harmonic crystal (`β > 0`). -/
lemma re_fourierHomogeneousCoupling_harmonicCrystalCoupling_nonneg [Nonempty d] (hβ : 0 < β)
    (z : UnitAddTorus d) : 0 ≤ (fourierHomogeneousCoupling (harmonicCrystalCoupling d β) z).re := by
  obtain ⟨p, rfl⟩ := UnitAddTorus.exists_eq_coe z
  rw [re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe]
  exact mul_nonneg (div_nonneg hβ.le (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun ℓ _ ↦ sub_nonneg.2 (Real.cos_le_one _))

/-- `Ĵ(1) = 0` for the harmonic crystal: `∑_n J(n) = 0`. -/
lemma tsum_harmonicCrystalCoupling [Nonempty d] : ∑' n, harmonicCrystalCoupling d β n = 0 := by
  have h := re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe (β := β) (fun _ : d ↦ (0 : ℝ))
  have h0 : (fun ℓ : d ↦ ((0 : ℝ) : UnitAddCircle)) = (0 : UnitAddTorus d) := by
    funext ℓ; simp
  rw [h0, fourierHomogeneousCoupling_zero, Complex.ofReal_re] at h
  simpa using h

/-- The harmonic crystal coupling is absolutely summable (it has finite range). -/
lemma summable_abs_harmonicCrystalCoupling : Summable fun n ↦ |harmonicCrystalCoupling d β n| := by
  refine Summable.abs ?_
  have h := (hasSum_ite_eq (0 : d → ℤ) (1 : ℝ)).mul_left β |>.sub
    ((hasSum_sum fun ℓ (_ : ℓ ∈ Finset.univ) ↦
      (hasSum_ite_eq (Pi.single ℓ 1) (1 : ℝ)).add (hasSum_ite_eq (-Pi.single ℓ 1) (1 : ℝ))).mul_left
      (β / (2 * Fintype.card d)))
  exact h.summable

/-- The harmonic crystal coupling has finite range. -/
lemma finite_setOf_harmonicCrystalCoupling_ne_zero :
    {n : d → ℤ | harmonicCrystalCoupling d β n ≠ 0}.Finite := by
  refine (Set.finite_singleton (0 : d → ℤ) |>.union
    ((Set.finite_range fun ℓ : d ↦ Pi.single ℓ (1 : ℤ)).union
      (Set.finite_range fun ℓ : d ↦ -Pi.single ℓ (1 : ℤ)))).subset ?_
  intro n hn
  by_contra hmem
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_range, not_or, not_exists] at hmem
  apply hn
  simp only [harmonicCrystalCoupling, ite_eq_right hmem.1]
  have : ∀ ℓ : d, ((if n = Pi.single ℓ 1 then (1 : ℝ) else 0)
      + (if n = -Pi.single ℓ 1 then 1 else 0)) = 0 := fun ℓ ↦ by
    rw [ite_eq_right (fun h ↦ hmem.2.1 ℓ h.symm), ite_eq_right (fun h ↦ hmem.2.2 ℓ h.symm),
      add_zero]
  simp [this]

/-- `Ĵ ≢ 0` for the harmonic crystal: at the point `z = (-1, …, -1)` of the torus,
`Ĵ(z) = 2β > 0`. -/
lemma re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_zero [Nonempty d] (hβ : 0 < β) :
    ∃ z, (fourierHomogeneousCoupling (harmonicCrystalCoupling d β) z).re ≠ 0 := by
  refine ⟨fun _ ↦ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle), ?_⟩
  rw [re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe (p := fun _ ↦ (1 : ℝ) / 2)]
  have hpi : 2 * Real.pi * ((1 : ℝ) / 2) = Real.pi := by ring
  have hcard : (Fintype.card d : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [hpi, Real.cos_pi, sub_neg_eq_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  positivity

/-- **The harmonic crystal is positive definite in every dimension**, Georgii (13.A8): `Ĵ ≥ 0`
and `Ĵ(-1, …, -1) = 2β ≠ 0`, so every `𝒥_Λ` is positive definite. This discharges the standing
hypothesis `hPD` of `Potential.gaussianSpecification` for this model — in particular `γ^{J,0}` is
defined also for `d ≤ 2`, where Georgii's Corollary (13.41) asserts `𝒢(γ^{J,0}) = ∅`. -/
theorem posDef_gaussianCouplingMatrix_harmonicCrystalCoupling [Nonempty d] (hβ : 0 < β)
    (Λ : Finset (d → ℤ)) :
    (gaussianCouplingMatrix (homogeneousCoupling (harmonicCrystalCoupling d β)) Λ).PosDef :=
  posDef_gaussianCouplingMatrix_homogeneousCoupling summable_abs_harmonicCrystalCoupling
    harmonicCrystalCoupling_neg (re_fourierHomogeneousCoupling_harmonicCrystalCoupling_nonneg hβ)
    (re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_zero hβ) Λ

/-! #### `d ≥ 3`: `Ĵ⁻¹` is integrable and `𝒢(γ^{J,0}) ≠ ∅` -/

omit [Fintype d] [DecidableEq d] in
/-- `8 t² ≤ 1 - cos 2πt` for `|t| ≤ 1/2`; this is Jordan's inequality for `cos`
(`Real.cos_le_one_sub_mul_cos_sq`) evaluated at `2πt`, and it is an equality at `t = ±1/2`. -/
lemma eight_mul_sq_le_one_sub_cos (t : ℝ) (ht : |t| ≤ 1 / 2) :
    8 * t ^ 2 ≤ 1 - Real.cos (2 * Real.pi * t) := by
  have hpi := Real.pi_pos
  have habs : |2 * Real.pi * t| ≤ Real.pi := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    nlinarith [abs_nonneg t]
  have h := Real.cos_le_one_sub_mul_cos_sq habs
  have hexp : 2 / Real.pi ^ 2 * (2 * Real.pi * t) ^ 2 = 8 * t ^ 2 := by
    field_simp
    ring
  rw [hexp] at h
  linarith

omit [DecidableEq d] in
/-- On `ℝ^d` with the supremum norm, `‖x‖² ≤ ∑_ℓ x_ℓ²`. -/
lemma sq_norm_le_sum_sq (x : d → ℝ) : ‖x‖ ^ 2 ≤ ∑ ℓ, x ℓ ^ 2 := by
  have hs : 0 ≤ ∑ ℓ, x ℓ ^ 2 := Finset.sum_nonneg fun ℓ _ ↦ sq_nonneg _
  have h1 : ‖x‖ ≤ Real.sqrt (∑ ℓ, x ℓ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun ℓ ↦ ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ ℓ))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ ℓ, x ℓ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) h1 2
    _ = ∑ ℓ, x ℓ ^ 2 := Real.sq_sqrt hs

/-- **Georgii's estimate in Example (13.43)**: `Ĵ(z_p) ≥ (8β/d) |p|²` for `p` in the fundamental
cube `]-1/2, 1/2]^d`, where `|·|` is the supremum norm of `ℝ^d`. (Georgii writes
`Ĵ(p) ≥ 4β|p|²` for the Euclidean norm and his normalisation of the characters.) -/
lemma mul_sq_norm_le_re_fourierHomogeneousCoupling_harmonicCrystalCoupling [Nonempty d]
    (hβ : 0 < β) (x : d → ℝ) (hx : ∀ ℓ, |x ℓ| ≤ 1 / 2) :
    8 * β / Fintype.card d * ‖x‖ ^ 2
      ≤ (fourierHomogeneousCoupling (harmonicCrystalCoupling d β)
          (fun ℓ ↦ ((x ℓ : ℝ) : UnitAddCircle))).re := by
  rw [re_fourierHomogeneousCoupling_harmonicCrystalCoupling_coe]
  have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have h1 : 8 * ∑ ℓ, x ℓ ^ 2 ≤ ∑ ℓ, (1 - Real.cos (2 * Real.pi * x ℓ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ℓ _ ↦ eight_mul_sq_le_one_sub_cos (x ℓ) (hx ℓ)
  have h2 : ‖x‖ ^ 2 ≤ ∑ ℓ, x ℓ ^ 2 := sq_norm_le_sum_sq x
  have hbd : 0 < β / Fintype.card d := by positivity
  calc 8 * β / Fintype.card d * ‖x‖ ^ 2 = β / Fintype.card d * (8 * ‖x‖ ^ 2) := by ring
    _ ≤ β / Fintype.card d * (8 * ∑ ℓ, x ℓ ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hbd.le
    _ ≤ β / Fintype.card d * ∑ ℓ, (1 - Real.cos (2 * Real.pi * x ℓ)) :=
        mul_le_mul_of_nonneg_left h1 hbd.le

/-- The finiteness of `∫ Ĵ⁻¹` over any measurable piece of the fundamental cube, from the estimate
`Ĵ(z_p) ≥ (8β/d)|p|²` and the integrability of `|p|^{-2}` over a ball of `ℝ^d` when `d ≥ 3`. -/
lemma setLIntegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_top [Nonempty d]
    (hβ : 0 < β) (hd : 3 ≤ Fintype.card d) {S : Set (d → ℝ)} (hSmeas : MeasurableSet S)
    (hS : ∀ y ∈ S, ∀ ℓ, |y ℓ| ≤ 1 / 2) :
    ∫⁻ y in S, (ENNReal.ofReal (fourierHomogeneousCoupling (harmonicCrystalCoupling d β)
      (fun ℓ ↦ ((y ℓ : ℝ) : UnitAddCircle))).re)⁻¹ ≠ ∞ := by
  have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast Fintype.card_pos
  have hc : 0 < 8 * β / Fintype.card d := by positivity
  have hSsub : S ⊆ Metric.ball (0 : d → ℝ) 1 := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      fun ℓ ↦ ?_) (by norm_num)
    rw [Real.norm_eq_abs]
    exact hS y hy ℓ
  have hfr : (2 : ℝ) < Module.finrank ℝ (d → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact_mod_cast lt_of_lt_of_le (by norm_num) hd
  have hmeas : AEStronglyMeasurable
      (fun y : d → ℝ ↦ (8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹) volume :=
    ((continuous_const.mul (continuous_norm.pow 2)).measurable.inv).aestronglyMeasurable
  have hball : IntegrableOn
      (fun y : d → ℝ ↦ (8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹) (Metric.ball 0 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow
      (C := (8 * β / Fintype.card d)⁻¹) (α := 2) ?_ hfr ?_ hmeas
    · rw [Module.finrank_fintype_fun_eq_card]; omega
    · refine Filter.Eventually.of_forall fun y ↦ ?_
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · have hy0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy
        have hrp : ‖y‖ ^ (-2 : ℝ) = (‖y‖ ^ (2 : ℕ))⁻¹ := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (norm_nonneg y),
            Real.rpow_natCast]
        rw [hrp, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv]
  have hSInt : IntegrableOn
      (fun y : d → ℝ ↦ (8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹) S volume := hball.mono_set hSsub
  have hnn : 0 ≤ᵐ[volume.restrict S]
      fun y : d → ℝ ↦ (8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹ := by
    filter_upwards with y
    simp only [Pi.zero_apply]
    positivity
  have hfin : ∫⁻ y in S, ENNReal.ofReal ((8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hnn).1 hSInt.2
  have hae0 : ∀ᵐ y ∂(volume : Measure (d → ℝ)), y ≠ 0 := by
    rw [ae_iff]
    simp
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_) hfin)
  filter_upwards [ae_restrict_mem hSmeas, ae_restrict_of_ae hae0] with y hyS hy0
  have hy1 : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
  have hcpos : 0 < 8 * β / Fintype.card d * ‖y‖ ^ 2 := by positivity
  calc (ENNReal.ofReal (fourierHomogeneousCoupling (harmonicCrystalCoupling d β)
        (fun ℓ ↦ ((y ℓ : ℝ) : UnitAddCircle))).re)⁻¹
      ≤ (ENNReal.ofReal (8 * β / Fintype.card d * ‖y‖ ^ 2))⁻¹ :=
        ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal
          (mul_sq_norm_le_re_fourierHomogeneousCoupling_harmonicCrystalCoupling hβ y
            (hS y hyS)))
    _ = ENNReal.ofReal ((8 * β / Fintype.card d * ‖y‖ ^ 2)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos hcpos).symm

/-- **Georgii Example (13.43) for `d ≥ 3`**: `∫_G Ĵ(z)⁻¹ dz < ∞` for the harmonic crystal. -/
theorem lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_top [Nonempty d]
    (hβ : 0 < β) (hd : 3 ≤ Fintype.card d) :
    ∫⁻ z, (ENNReal.ofReal
      (fourierHomogeneousCoupling (harmonicCrystalCoupling d β) z).re)⁻¹ ≠ ∞ := by
  rw [UnitAddTorus.lintegral_preimage _ fun _ : d ↦ (-(1 : ℝ) / 2)]
  refine setLIntegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_top hβ hd
    ?_ ?_
  · have he : {y : d → ℝ | ∀ i, y i ∈ Set.Ioc ((fun _ : d ↦ -(1 : ℝ) / 2) i)
        ((fun _ : d ↦ -(1 : ℝ) / 2) i + 1)}
        = Set.univ.pi fun _ : d ↦ Set.Ioc (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) := by
      ext y
      simp
    rw [he]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc
  · intro y hy ℓ
    have hy' := hy ℓ
    simp only [Set.mem_Ioc] at hy'
    rw [abs_le]
    constructor <;> linarith [hy'.1, hy'.2]

/-- **Georgii Example (13.43) for `d ≥ 3`**: the harmonic crystal has Gibbs measures. Combined
with `Potential.isInvariant_spinTranslation_const_harmonicCrystalCoupling` — the continuous
symmetry `ω ↦ (ω_i + t)_i` coming from `Ĵ(1) = 0` — and with
`Potential.map_add_const_isGibbsMeasure_of_tsum_eq_zero`, every element of `𝒢(γ^{J,0})` is one of
a one-parameter family of Gibbs measures, none of which is invariant under the symmetry group. -/
theorem nonempty_G_harmonicCrystalCoupling [Nonempty d] [LinearOrder (d → ℤ)]
    (hβ : 0 < β) (hd : 3 ≤ Fintype.card d) :
    (MeasureTheory.GibbsMeasure.G (gaussianSpecification
      (homogeneousCoupling (harmonicCrystalCoupling d β)) (fun _ ↦ (0 : ℝ))
      (symm_homogeneousCoupling harmonicCrystalCoupling_neg)
      (finite_setOf_homogeneousCoupling_ne_zero finite_setOf_harmonicCrystalCoupling_ne_zero)
      (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ) 1 one_pos)).Nonempty :=
  nonempty_G_homogeneousCoupling_of_lintegral_inv_ne_top summable_abs_harmonicCrystalCoupling
    (lintegral_inv_re_fourierHomogeneousCoupling_harmonicCrystalCoupling_ne_top hβ hd)
    harmonicCrystalCoupling_neg finite_setOf_harmonicCrystalCoupling_ne_zero
    (posDef_gaussianCouplingMatrix_harmonicCrystalCoupling hβ)
    (re_fourierHomogeneousCoupling_harmonicCrystalCoupling_nonneg hβ)
    ⟨fun _ ↦ 0,
      (const_mem_gaussianMeanSet_iff summable_abs_harmonicCrystalCoupling 0 0).2 (by ring)⟩

/-- **The constant shifts are symmetries of the harmonic crystal**, Georgii (13.43): since
`Ĵ(1) = 0`, `M_{J,0}` contains all constants and `ω ↦ (ω_i + t)_i` is a symmetry of `γ^{J,0}`. -/
theorem isInvariant_spinTranslation_const_harmonicCrystalCoupling [Nonempty d]
    [LinearOrder (d → ℤ)]
    (hPD : ∀ Λ : Finset (d → ℤ),
      (gaussianCouplingMatrix (homogeneousCoupling (harmonicCrystalCoupling d β)) Λ).PosDef)
    (h : (d → ℤ) → ℝ) (t : ℝ) :
    Specification.IsInvariant
      (MeasureTheory.GibbsMeasure.spinTranslation (fun _ : d → ℤ ↦ t))
      (gaussianSpecification (homogeneousCoupling (harmonicCrystalCoupling d β)) h
        (symm_homogeneousCoupling harmonicCrystalCoupling_neg)
        (finite_setOf_homogeneousCoupling_ne_zero finite_setOf_harmonicCrystalCoupling_ne_zero)
        hPD 1 one_pos) :=
  isInvariant_spinTranslation_const_of_tsum_eq_zero _ _ hPD summable_abs_harmonicCrystalCoupling
    tsum_harmonicCrystalCoupling h t

end HarmonicCrystal

end Fourier

end Potential

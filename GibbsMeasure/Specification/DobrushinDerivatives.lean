/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import GibbsMeasure.Mathlib.Analysis.Calculus.TiltedIntegral
public import GibbsMeasure.Specification.DobrushinUniqueness
public import GibbsMeasure.Specification.Pressure
public import Mathlib.Probability.Moments.Covariance

/-!
# Georgii §8.2: the covariance estimate and the derivative of the Gibbs measure

Georgii's Proposition (8.34) bounds the covariances of the unique Gibbs measure of a
specification satisfying Dobrushin's condition (8.6):
`|μ(fg) − μ(f)μ(g)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`,
where `D(γ) = ∑_{n ≥ 0} C(γ)^n` is Georgii's (8.19) and `δ_i` is the single-site oscillation
(8.14).

Georgii's proof tilts the specification by `g`: `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`, notes
that `μ̃ = g μ` is Gibbs for `γ̃`, and applies the comparison theorem (8.20) with
`b_j = δ_j(g) / 4 γ_j g`.

Corollary (8.37) is the second application: for `Φ` in the region `𝒟 = {‖Φ‖' < 1}` of (8.36),
a direction `Ψ` and a bounded quasilocal `g` with `∑_i δ_i(g) < ∞`, the map `t ↦ μ_{Φ+tΨ}(g)`
is differentiable near `0`, with derivative `−∑_k ⟨f_Ψ ∘ θ_{−k}, g⟩_{μ_{Φ+tΨ}}`. The proof
exchanges `Λ ↑ S` with `∂/∂t`: at finite volume the derivative is the covariance
`−⟨H^Ψ_Λ, g⟩_{γ_Λ(·|ω)}` (the exponential tilt of `GibbsMeasure/Mathlib/Analysis/Calculus/`
`TiltedIntegral.lean`), the finite-volume Gibbs distributions converge by (8.23), and the
convergence of the derivatives is uniform in `t` because (8.34) is applied against a single
majorant of the interdependence matrices of the whole segment `Φ + tΨ`, `|t| ≤ t₀`.

## Main definitions

* `MeasureTheory.GibbsMeasure.Dobrushin.tilt`: the specification `γ̃ = h γ` obtained by
  normalising a single positive bounded density volume by volume, Georgii's tilt in the proof of
  (8.34).
* `MeasureTheory.GibbsMeasure.Dobrushin.hamiltonianLp`, `hamiltonianRemLp`: the Hamiltonian
  `H^Φ_Λ` and its boundary part `H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}` as bounded quasilocal
  observables (`hamiltonianLp_mem_quasilocalFunctions`,
  `hamiltonianRemLp_mem_quasilocalFunctions`).

## Main results

* `MeasureTheory.GibbsMeasure.Dobrushin.unifDist_withDensity_le`: Georgii's elementary estimate
  `‖uα − α‖ ≤ δ(u)/4` for a probability density `u` on a probability space.
* `MeasureTheory.GibbsMeasure.Dobrushin.ofReal_abs_covariance_le`: **Georgii, Proposition
  (8.34)**; `ofReal_abs_covariance_le_of_iSup` is Georgii's own `sup`-form, and
  `ofReal_abs_covariance_le_matSeries`, `ofReal_abs_covariance_apply_le_matSeries` state it
  against a majorant `C ≥ C(γ)` of the interdependence matrix, at infinite and at finite volume.
  `ofReal_abs_covariance_le_matSeries'` and `ofReal_abs_covariance_apply_le_matSeries'` are the
  same bounds written with `ProbabilityTheory.covariance` (`covariance_eq_integral_mul_sub`).
* `MeasureTheory.GibbsMeasure.Dobrushin.gibbsSpecificationOfAbsolutelySummable_eq_tilted`: a
  finite-volume Gibbs distribution is the exponential tilt of the free measure by `−β H^Φ_Λ`;
  `hasDerivAt_integral_gibbsSpecification` is the resulting finite-volume derivative
  `∂/∂t γ^{Φ+tΨ}_Λ(g|ω) = −⟨H^Ψ_Λ, g⟩^t_Λ` of Georgii's proof of (8.37).
* `MeasureTheory.GibbsMeasure.Dobrushin.oscAt_hamiltonian_sub_sum_siteEnergy_le`,
  `tsum_oscAt_siteEnergy_le`, `tsum_oscAt_siteEnergy_le'`: Georgii's two oscillation estimates
  `δ_j(H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}) ≤ 2 ∑_{A ∋ j, A ⊄ Λ} ‖Ψ_A‖` and
  `∑_k δ_j(f_Ψ ∘ θ_{−k}) ≤ 2‖Ψ‖_j`.
* `MeasureTheory.GibbsMeasure.Dobrushin.tendsto_bound_hamiltonianRemLp`,
  `tendsto_bound_tsum_compl_siteEnergy`: Georgii's `T₁ → 0` and `T₃ → 0`, uniformly in the
  potential along the segment.
* `MeasureTheory.GibbsMeasure.Dobrushin.covariance_hamiltonian_eq_add_sum_siteEnergy`,
  `tsum_ite_ofReal_abs_covariance_siteEnergy_le`, `summable_norm_covariance_siteEnergy` and
  `ofReal_abs_covariance_hamiltonian_sub_tsum_le`: the decomposition of `⟨H^Ψ_Λ, g⟩` and the
  resulting `T₁ + T₂ + 2T₃` estimate for `⟨H^Ψ_Λ, g⟩_{γ_Λ(·|ω)} − ∑_k ⟨f_Ψ ∘ θ_{−k}, g⟩_μ`.
* `MeasureTheory.GibbsMeasure.Dobrushin.hasDerivAt_integral_gibbsMeasure_add_smul`:
  **Georgii, Corollary (8.37)**, in the form Georgii proves: the directional derivative formula
  `∂/∂t μ_{Φ+tΨ}(g) = −∑_k ⟨f_Ψ ∘ θ_{−k}, g⟩_{μ_{Φ+tΨ}}`, valid at every `|t| < t₀`.

## Scope

Georgii's Corollary (8.37) opens with the assertion that `Φ ↦ μ_Φ(g)` is *continuously*
differentiable on `𝒟` as a function on the Banach space `ℬ̃_Θ` of (8.36); his proof establishes
the displayed directional-derivative formula and nothing more. Only that formula is proved here
(for every base point of the segment, hence on a neighbourhood of `0`). The norm-continuity of
`Φ ↦ (Ψ ↦ ∂_Ψ μ_Φ(g))` — equivalently, a modulus of continuity for `Φ ↦ μ_Φ` on `𝒟` — is not
established by Georgii's argument and is not claimed here; Georgii's Corollary (16.17), the only
consumer of (8.37) in the book, uses the directional formula alone.

The statement below is also free of Georgii's homogeneity assumptions: `S` is an arbitrary
countable site set, and the region `𝒟` is entered through the site-uniform bounds
`‖Φ‖'ᵢ ≤ a`, `‖Ψ‖'ᵢ ≤ b` with `a + t₀ b < 1`. On `S = ℤ^d` with shift-invariant potentials
these are Georgii's `‖Φ‖ + t₀‖Ψ‖ < 1` (`Dobrushin.cardNormAt_eq_of_isShiftInvariant`). The a
priori measure is a probability measure rather than Georgii's finite `λ`; the two give the same
specification, since the normalisation cancels between numerator and partition function.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal NNReal Topology
open ENNReal (matIter matIter_zero matIter_succ matIter_le matIter_mono_matrix
  matIter_mono_vec matIter_add matIter_const_mul matIter_tsum matSeries le_matSeries matSeries_le
  matSeries_mono_matrix matSeries_mono_vec matSeries_add matSeries_const_mul matSeries_tsum
  matEntry matSeries_eq_tsum_matEntry tsum_matEntry_le tsum_le_card_mul_add tsum_ite_compl_eq
  exists_tsum_ite_compl_le tendsto_tsum_mul_of_tendsto matTail matTail_antitone
  matTail_mono_matrix exists_matIter_compl_le tendsto_matTail tendsto_tsum_matSeries_mul
  tendsto_tsum_matTail_mul)

noncomputable section

namespace MeasureTheory.GibbsMeasure.Dobrushin

/-! ### The elementary density estimate `‖uα − α‖ ≤ δ(u)/4` -/

section DensityEstimate

variable {X : Type*} [MeasurableSpace X]

/-- **Georgii, proof of Proposition (8.34)**, the elementary estimate: if `u ≥ 0` is a
probability density with respect to the probability measure `α` whose oscillation is at most `d`,
then `‖uα − α‖ ≤ d/4` in the uniform distance (8.1).

Georgii argues via `α(|u − 1|) ≤ α((u − m)²)^{1/2}`; the argument below is the equivalent
two-block estimate `∫_A u dα − α(A) = α(A) α(Aᶜ) (u|_A − u|_{Aᶜ}) ≤ α(A) α(Aᶜ) d ≤ d/4`. -/
theorem unifDist_withDensity_le (α : Measure X) [IsProbabilityMeasure α] {u : X → ℝ}
    (hum : Measurable u) (hu0 : ∀ x, 0 ≤ u x) {d : ℝ} (hd : ∀ x y, u x - u y ≤ d)
    (hu1 : ∫ x, u x ∂α = 1) :
    unifDist (α.withDensity fun x ↦ ENNReal.ofReal (u x)) α ≤ ENNReal.ofReal (d / 4) := by
  obtain ⟨x₀⟩ : Nonempty X := by
    by_contra hX
    simp only [not_nonempty_iff] at hX
    have : (univ : Set X) = ∅ := Set.eq_empty_of_isEmpty _
    simpa [this] using measure_univ (μ := α)
  have hd0 : 0 ≤ d := by simpa using hd x₀ x₀
  have hbdd : ∀ x, u x ≤ u x₀ + d := fun x ↦ by linarith [hd x x₀]
  have hint : Integrable u α :=
    ⟨hum.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := |u x₀| + |d|)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]
        calc u x ≤ u x₀ + d := hbdd x
          _ ≤ |u x₀| + |d| := add_le_add (le_abs_self _) (le_abs_self _))⟩
  refine unifDist_le fun A hA ↦ ?_
  have hIA : IntegrableOn u A α := hint.integrableOn
  have hIAc : IntegrableOn u Aᶜ α := hint.integrableOn
  have hcA : IntegrableOn (fun _ : X ↦ (1 : ℝ)) A α := (integrable_const 1).integrableOn
  set t : ℝ := α.real A with ht
  set s : ℝ := α.real Aᶜ with hs
  set p : ℝ := ∫ x in A, u x ∂α with hp
  set q : ℝ := ∫ x in Aᶜ, u x ∂α with hq
  have ht0 : 0 ≤ t := measureReal_nonneg
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hts : t + s = 1 := by
    rw [ht, hs, measureReal_add_measureReal_compl hA, measureReal_def, measure_univ,
      ENNReal.toReal_one]
  have hpq : p + q = 1 := by rw [hp, hq, integral_add_compl hA hint, hu1]
  -- `p − t = s p − t q`, and the latter is an integral of an integrand bounded by `s d`.
  have hkey : p - t = s * p - t * q := by linear_combination t * hpq - p * hts
  have hstep : ∀ x, s * u x - q ≤ s * d := by
    intro x
    have hconst : ∫ _y in Aᶜ, u x ∂α = s * u x := by
      rw [setIntegral_const, hs, smul_eq_mul]
    have hsub : s * u x - q = ∫ y in Aᶜ, (u x - u y) ∂α := by
      rw [← hconst, hq, ← integral_sub ((integrable_const (u x)).integrableOn) hIAc]
    rw [hsub]
    calc ∫ y in Aᶜ, (u x - u y) ∂α ≤ ∫ _y in Aᶜ, d ∂α :=
          setIntegral_mono (((integrable_const (u x)).integrableOn).sub hIAc)
            ((integrable_const d).integrableOn)
            (fun y ↦ hd x y)
      _ = s * d := by rw [setIntegral_const, hs, smul_eq_mul]
  have hbound : p - t ≤ d / 4 := by
    have h1 : s * p - t * q = ∫ x in A, (s * u x - q) ∂α := by
      rw [integral_sub (hIA.const_mul s) ((integrable_const q).integrableOn),
        integral_const_mul, setIntegral_const, ← hp, ← ht, smul_eq_mul]
    have h2 : ∫ x in A, (s * u x - q) ∂α ≤ t * (s * d) := by
      calc ∫ x in A, (s * u x - q) ∂α ≤ ∫ _x in A, s * d ∂α :=
            setIntegral_mono ((hIA.const_mul s).sub ((integrable_const q).integrableOn))
              ((integrable_const (s * d)).integrableOn) hstep
        _ = t * (s * d) := by rw [setIntegral_const, ← ht, smul_eq_mul]
    have hts4 : t * s ≤ 1 / 4 := by nlinarith [sq_nonneg (t - s)]
    have h3 : t * (s * d) ≤ d / 4 := by
      calc t * (s * d) = (t * s) * d := by ring
        _ ≤ (1 / 4) * d := by nlinarith
        _ = d / 4 := by ring
    rw [hkey, h1]; exact h2.trans h3
  -- transport the real inequality to `ℝ≥0∞`
  have hwd : (α.withDensity fun x ↦ ENNReal.ofReal (u x)) A = ENNReal.ofReal p := by
    rw [withDensity_apply _ hA, hp,
      ofReal_integral_eq_lintegral_ofReal hIA (Filter.Eventually.of_forall hu0)]
  have hαA : α A = ENNReal.ofReal t := by
    rw [ht, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top α A)]
  rw [hwd, hαA, ← ENNReal.ofReal_sub _ ht0]
  exact ENNReal.ofReal_le_ofReal hbound

end DensityEstimate

end MeasureTheory.GibbsMeasure.Dobrushin

/-! ### Normalizing a single density volume by volume

Georgii, proof of (8.34): `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`. This is
`Specification.relNorm` of the constant family `ρ_Λ = g`, which is a premodifier with a *trivial*
cocycle (1.31), so `Specification.IsPremodifier.isModifier_relNorm` applies without its
resampling hypothesis. -/

namespace Specification

variable {S E : Type*} [MeasurableSpace E] (γ : Specification S E)

/-- **Georgii, Remark (1.32) for a constant premodifier.** If `0 < γ_Λ g < ∞` for every finite
volume `Λ`, then `h_Λ = g / γ_Λ g` is a modifier of `γ`; the cocycle condition (1.31) of
`Specification.IsPremodifier` is trivially satisfied by a family that does not depend on `Λ`, so
unlike `Specification.IsPremodifier.isModifier_relNorm` this needs no resampling hypothesis. -/
theorem isModifier_relNorm_const {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) : γ.IsModifier (relNorm γ fun _ ↦ g) := by
  have hρm : ∀ Λ : Finset S, Measurable ((fun _ : Finset S ↦ g) Λ) := fun _ ↦ hg
  refine (isModifier_iff_ae_eq (γ := γ)).2
    ⟨measurable_relNorm (γ := γ) hρm, lintegral_relNorm (γ := γ) hρm hZ,
      fun Λ₁ Λ₂ hΛ η ↦ .of_forall fun ω ↦ ?_⟩
  have hinner : ∫⁻ ζ, relNorm γ (fun _ ↦ g) Λ₂ ζ ∂(γ Λ₁ ω)
      = (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω := by
    have hae : ∀ᵐ ζ ∂(γ Λ₁ ω), relNorm γ (fun _ ↦ g) Λ₂ ζ
        = (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ζ := by
      filter_upwards [relZ_ae_eq (γ := γ) hρm hΛ ω] with ζ hζ
      rw [relNorm, hζ, ENNReal.div_eq_inv_mul]
    rw [lintegral_congr_ae hae, lintegral_const_mul _ hg]
    rfl
  have hcancel : (relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω = 1 :=
    ENNReal.inv_mul_cancel (hZ Λ₁ ω).1 (hZ Λ₁ ω).2
  show relNorm γ (fun _ ↦ g) Λ₂ ω
      = relNorm γ (fun _ ↦ g) Λ₁ ω * ∫⁻ ζ, relNorm γ (fun _ ↦ g) Λ₂ ζ ∂(γ Λ₁ ω)
  rw [hinner, relNorm, relNorm, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  calc (relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ω
      = ((relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω)
          * ((relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * g ω) := by rw [hcancel, one_mul]
    _ = (relZ γ (fun _ ↦ g) Λ₁ ω)⁻¹ * g ω
          * ((relZ γ (fun _ ↦ g) Λ₂ ω)⁻¹ * relZ γ (fun _ ↦ g) Λ₁ ω) := by ring

/-- **Georgii, proof of (8.34):** the specification `γ̃` obtained from `γ` by tilting with the
density `g`, i.e. `γ̃_Λ = h_Λ γ_Λ` with `h_Λ = g / γ_Λ g`. -/
noncomputable def tilt {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) : Specification S E :=
  γ.modification (relNorm γ fun _ ↦ g) (isModifier_relNorm_const γ hg hZ)

@[simp] lemma tilt_apply {g : (S → E) → ℝ≥0∞} (hg : Measurable g)
    (hZ : IsRelAdmissible γ fun _ ↦ g) (Λ : Finset S) (η : S → E) :
    γ.tilt hg hZ Λ η = (γ Λ η).withDensity (relNorm γ (fun _ ↦ g) Λ) := rfl

end Specification

namespace MeasureTheory.GibbsMeasure.Dobrushin

/-! ### Georgii's Proposition (8.34): the covariance estimate -/

section Covariance

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {g : (S → E) → ℝ} {m M : ℝ}

variable (γ) in
/-- A strictly positive bounded observable has strictly positive finite partition functions in
every finite volume, so it normalizes to a modifier of `γ`. -/
lemma isRelAdmissible_ofReal (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M) :
    Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ) := by
  refine fun Λ η ↦ ⟨?_, ?_⟩
  · have hle : ENNReal.ofReal m ≤ ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) := by
      calc ENNReal.ofReal m = ∫⁻ _σ, ENNReal.ofReal m ∂(γ Λ η) := by simp
        _ ≤ _ := lintegral_mono fun σ ↦ ENNReal.ofReal_le_ofReal (hmg σ)
    intro h
    rw [show Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) Λ η
      = ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) from rfl] at h
    rw [h, le_zero_iff] at hle
    exact (ENNReal.ofReal_pos.2 hm).ne' hle
  · have hle : ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η) ≤ ENNReal.ofReal M :=
      calc ∫⁻ σ, ENNReal.ofReal (g σ) ∂(γ Λ η)
          ≤ ∫⁻ _σ, ENNReal.ofReal M ∂(γ Λ η) :=
            lintegral_mono fun σ ↦ ENNReal.ofReal_le_ofReal (hgM σ)
        _ = ENNReal.ofReal M := by simp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- A bounded measurable observable is integrable against every finite-volume kernel. -/
lemma integrable_of_bounded (hgm : Measurable g) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (Λ : Finset S) (η : S → E) : Integrable g (γ Λ η) :=
  ⟨hgm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := |m| + |M|)
    (Filter.Eventually.of_forall fun σ ↦ by
      rw [Real.norm_eq_abs]
      rcases abs_cases (g σ) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; calc g σ ≤ M := hgM σ
          _ ≤ |m| + |M| := by
              have := abs_nonneg m; have := le_abs_self M; linarith
      · rw [h]; calc -g σ ≤ -m := by linarith [hmg σ]
          _ ≤ |m| + |M| := by
              have := abs_nonneg M; have := neg_le_abs m; linarith)⟩

variable (γ) in
/-- Georgii's `γ_Λ g` in its two readings: the `ℝ≥0∞`-valued partition function of the density
`ofReal ∘ g` is `ofReal` of the Bochner integral of `g`. -/
lemma relZ_ofReal_eq (hgm : Measurable g) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (hm : 0 < m) (Λ : Finset S) (ω : S → E) :
    Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) Λ ω
      = ENNReal.ofReal (∫ σ, g σ ∂(γ Λ ω)) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded hgm hmg hgM Λ ω)
    (Filter.Eventually.of_forall fun σ ↦ le_trans hm.le (hmg σ))).symm

/-- **Georgii, proof of (8.34):** if `μ` is Gibbs for `γ` in the volume `Λ`, then `μ̃ = g μ` is
Gibbs for the tilted specification `γ̃ = h γ` with `h_Λ = g / γ_Λ g`. Georgii's computation
`μ̃ γ̃_Λ (f) = μ γ_Λ(g γ_Λ(fg)/γ_Λ g) = μ γ_Λ(fg) = μ̃(f)`, in set form. -/
theorem bind_tilt_eq {μ : Measure (S → E)} {ĝ : (S → E) → ℝ≥0∞} (hĝm : Measurable ĝ)
    (hZ : Specification.IsRelAdmissible γ fun _ ↦ ĝ) {Λ : Finset S} (hμ : μ.bind (γ Λ) = μ) :
    (μ.withDensity ĝ).bind (γ.tilt hĝm hZ Λ) = μ.withDensity ĝ := by
  classical
  set Z : (S → E) → ℝ≥0∞ := Specification.relZ γ (fun _ ↦ ĝ) Λ with hZdef
  have hZmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Z :=
    Specification.measurable_relZ (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) Λ
  have hbase : AEMeasurable ((γ Λ : Kernel[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
      (S → E) (S → E)) : (S → E) → Measure (S → E)) μ :=
    (((γ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  refine Measure.ext fun A hA ↦ ?_
  set N : (S → E) → ℝ≥0∞ := fun ω ↦ ∫⁻ y in A, ĝ y ∂(γ Λ ω) with hNdef
  have hNmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] N :=
    hĝm.setLIntegral_kernel hA
  have hNm : Measurable N := hNmB.mono cylinderEvents_le_pi le_rfl
  have hkerA : AEMeasurable ((γ.tilt hĝm hZ Λ :
      Kernel[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] (S → E) (S → E)) :
      (S → E) → Measure (S → E)) (μ.withDensity ĝ) :=
    (((γ.tilt hĝm hZ Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hcoeA : Measurable fun ω ↦ (γ.tilt hĝm hZ Λ ω) A :=
    (Kernel.measurable_coe (γ.tilt hĝm hZ Λ) hA).mono cylinderEvents_le_pi le_rfl
  have h1 : ∫⁻ ω, (γ.tilt hĝm hZ Λ ω) A ∂(μ.withDensity ĝ)
      = ∫⁻ ω, ((Z ω)⁻¹ * N ω) * ĝ ω ∂μ := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hĝm hcoeA]
    refine lintegral_congr fun ω ↦ ?_
    rw [Pi.mul_apply, Specification.tilt_apply,
      Specification.withDensity_relNorm_apply (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) hA ω]
    ring
  have h2 : ∫⁻ ω, ((Z ω)⁻¹ * N ω) * ĝ ω ∂μ = ∫⁻ ξ, N ξ ∂μ := by
    conv_lhs => rw [← hμ]
    have hmul : Measurable fun ω ↦ (Z ω)⁻¹ * N ω * ĝ ω :=
      (((hZmB.inv.fun_mul hNmB).mono cylinderEvents_le_pi le_rfl)).fun_mul hĝm
    rw [Measure.lintegral_bind hbase hmul.aemeasurable]
    refine lintegral_congr fun ξ ↦ ?_
    rw [(γ.isProper Λ).lintegral_mul (f := ĝ) (g := fun x ↦ (Z x)⁻¹ * N x)
      cylinderEvents_le_pi hĝm (hZmB.inv.fun_mul hNmB) ξ]
    have hZξ : ∫⁻ x, ĝ x ∂(γ Λ ξ) = Z ξ := rfl
    rw [hZξ]
    calc (Z ξ)⁻¹ * N ξ * Z ξ = ((Z ξ)⁻¹ * Z ξ) * N ξ := by ring
      _ = N ξ := by rw [ENNReal.inv_mul_cancel (hZ Λ ξ).1 (hZ Λ ξ).2, one_mul]
  have h3 : ∫⁻ ξ, N ξ ∂μ = (μ.withDensity ĝ) A := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    have hind : ∀ ξ, N ξ = ∫⁻ y, A.indicator ĝ y ∂(γ Λ ξ) := fun ξ ↦ by
      rw [hNdef, lintegral_indicator hA]
    rw [lintegral_congr hind, ← Measure.lintegral_bind hbase (hĝm.indicator hA).aemeasurable, hμ]
  rw [Measure.bind_apply hA hkerA, h1, h2, h3]

variable [DecidableEq S]

/-- Properness turns an `ℝ≥0∞`-integral against `γ_i(·|ω)` into the integral of the section
`x ↦ f(x ω_{S∖i})` against the projection `γ_i^0(·|ω)` of Georgii (8.4); the `ℝ≥0∞` counterpart
of `MeasureTheory.GibbsMeasure.Dobrushin.integral_eq_integral_proj`. -/
lemma lintegral_eq_lintegral_proj (γ : Specification S E) (i : S) (ω : S → E)
    {f : (S → E) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ σ, f σ ∂(γ {i} ω) = ∫⁻ x, f (Function.update ω i x) ∂(proj γ i ω) := by
  have hT : Measurable fun σ : S → E ↦ Function.update ω i (σ i) := measurable_updateAt i ω
  have hU : Measurable fun x : E ↦ Function.update ω i x := measurable_updateOf i ω
  conv_lhs => rw [← map_updateAt_eq γ i ω]
  rw [lintegral_map hf hT, proj,
    lintegral_map (f := fun x ↦ f (Function.update ω i x)) (hf.comp hU) (measurable_pi_apply i)]

/-- **Georgii, proof of (8.34):** the `σ_i`-projection (8.4) of the tilted single-site kernel is
the projection of `γ_i` with the density `x ↦ g(x ω_{S∖i}) / γ_i g(ω)`. -/
theorem proj_tilt_eq {ĝ : (S → E) → ℝ≥0∞} (hĝm : Measurable ĝ)
    (hZ : Specification.IsRelAdmissible γ fun _ ↦ ĝ) (i : S) (ω : S → E) :
    proj (γ.tilt hĝm hZ) i ω
      = (proj γ i ω).withDensity fun x ↦
          ĝ (Function.update ω i x) / Specification.relZ γ (fun _ ↦ ĝ) {i} ω := by
  classical
  set Z : ℝ≥0∞ := Specification.relZ γ (fun _ ↦ ĝ) {i} ω with hZω
  refine Measure.ext fun A hA ↦ ?_
  have hpre : MeasurableSet ((fun σ : S → E ↦ σ i) ⁻¹' A) := hA.preimage (measurable_pi_apply i)
  have hsec : ∫⁻ y in (fun σ : S → E ↦ σ i) ⁻¹' A, ĝ y ∂(γ {i} ω)
      = ∫⁻ x in A, ĝ (Function.update ω i x) ∂(proj γ i ω) := by
    rw [← lintegral_indicator hpre, ← lintegral_indicator hA,
      lintegral_eq_lintegral_proj γ i ω (hĝm.indicator hpre)]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem (by simpa using hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (by simpa using hx), Set.indicator_of_notMem hx]
  rw [proj, Measure.map_apply (measurable_pi_apply i) hA, Specification.tilt_apply,
    Specification.withDensity_relNorm_apply (γ := γ) (ρ := fun _ ↦ ĝ) (fun _ ↦ hĝm) hpre ω,
    withDensity_apply _ hA, hsec, ← hZω,
    ← lintegral_const_mul (f := fun x ↦ ĝ (Function.update ω i x)) _
      (hĝm.comp (measurable_updateOf i ω))]
  exact lintegral_congr fun x ↦ ENNReal.div_eq_inv_mul.symm

/-- **Georgii, proof of (8.34):** the function `b_j(ω) = δ_j(g) / 4 γ_j g(ω)` dominates the
uniform distance (8.1) `‖γ_j^0(·|ω) − γ̃_j^0(·|ω)‖` between the single-site projections (8.4) of
`γ` and of its tilt by `g`.

This is Georgii's chain `‖uα − α‖ ≤ δ(u)/4` (`unifDist_withDensity_le`) applied to the section
`u(x) = g(x ω_{S∖j}) / γ_j g(ω)` of the tilting density. -/
theorem unifDist_proj_tilt_le (hgm : Measurable g) (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ)
    (hgM : ∀ σ, g σ ≤ M)
    (hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ)) (i : S) (ω : S → E) :
    unifDist (proj γ i ω) (proj (γ.tilt hgm.ennreal_ofReal hZ) i ω)
      ≤ oscAt g i / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω) := by
  classical
  have hgpos : ∀ σ, 0 < g σ := fun σ ↦ lt_of_lt_of_le hm (hmg σ)
  have habs : ∀ σ, |g σ| ≤ M := fun σ ↦ by rw [abs_of_pos (hgpos σ)]; exact hgM σ
  have hoscne : oscAt g i ≠ ⊤ := oscAt_ne_top_of_bounded habs
  set δ : ℝ := (oscAt g i).toReal with hδdef
  have hδ : oscAt g i = ENNReal.ofReal δ := (ENNReal.ofReal_toReal hoscne).symm
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  set Zr : ℝ := ∫ σ, g σ ∂(γ {i} ω) with hZr
  have hint : Integrable g (γ {i} ω) := integrable_of_bounded (γ := γ) hgm hmg hgM {i} ω
  have hZrpos : 0 < Zr := by
    have hmZ : m ≤ Zr := by
      calc m = ∫ _σ : S → E, m ∂(γ {i} ω) := by simp
        _ ≤ Zr := integral_mono (integrable_const m) hint hmg
    exact lt_of_lt_of_le hm hmZ
  have hZeq : Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω
      = ENNReal.ofReal Zr := relZ_ofReal_eq γ hgm hmg hgM hm {i} ω
  set u : E → ℝ := fun x ↦ g (Function.update ω i x) / Zr with hu
  have hum : Measurable u := (hgm.comp (measurable_updateOf i ω)).div_const _
  have hu0 : ∀ x, 0 ≤ u x := fun x ↦ le_of_lt (div_pos (hgpos _) hZrpos)
  have hsec : ∫ x, g (Function.update ω i x) ∂(proj γ i ω) = Zr :=
    (integral_eq_integral_proj γ i ω hgm).symm
  have hu1 : ∫ x, u x ∂(proj γ i ω) = 1 := by
    rw [hu, integral_div, hsec, div_self hZrpos.ne']
  have hdd : ∀ x y, u x - u y ≤ δ / Zr := by
    intro x y
    have hnum : g (Function.update ω i x) - g (Function.update ω i y) ≤ δ := by
      have hle : ENNReal.ofReal |g (Function.update ω i x) - g (Function.update ω i y)|
          ≤ oscAt g i :=
        le_oscAt fun k hk ↦ by rw [Function.update_of_ne hk, Function.update_of_ne hk]
      have := (ENNReal.ofReal_le_iff_le_toReal hoscne).1 hle
      exact le_trans (le_abs_self _) this
    rw [hu, div_sub_div_same]
    gcongr
  have hproj : proj (γ.tilt hgm.ennreal_ofReal hZ) i ω
      = (proj γ i ω).withDensity fun x ↦ ENNReal.ofReal (u x) := by
    rw [proj_tilt_eq (hĝm := hgm.ennreal_ofReal) hZ i ω]
    refine congrArg _ (funext fun x ↦ ?_)
    rw [hu, ENNReal.ofReal_div_of_pos hZrpos, hZeq]
  have hkey := unifDist_withDensity_le (proj γ i ω) hum hu0 hdd hu1
  rw [unifDist_comm, hproj]
  refine hkey.trans (le_of_eq ?_)
  have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal Zr = ENNReal.ofReal (4 * Zr) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  rw [hZeq, hδ, h4, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

omit [DecidableEq S] in
/-- **Georgii, proof of (8.34):** `μ̃(b_j) = δ_j(g)/4`. Since `μ̃ = g μ`, `μ γ_j = μ` and
`γ_j(g / γ_j g) = 1` by properness, the boundary-dependent normalization integrates out. -/
theorem lintegral_oscAt_div_eq {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hgm : Measurable g) (hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ))
    (j : S) (hμ : μ.bind (γ {j}) = μ) :
    ∫⁻ ω, oscAt g j / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {j} ω)
        ∂(μ.withDensity fun σ ↦ ENNReal.ofReal (g σ)) = oscAt g j / 4 := by
  classical
  have hĝm : Measurable fun σ ↦ ENNReal.ofReal (g σ) := hgm.ennreal_ofReal
  set Z : (S → E) → ℝ≥0∞ := Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {j} with hZdef
  have hZmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((({j} : Finset S) : Set S)ᶜ)] Z :=
    Specification.measurable_relZ (γ := γ) (ρ := fun _ σ ↦ ENNReal.ofReal (g σ))
      (fun _ ↦ hĝm) {j}
  have hZm : Measurable Z := hZmB.mono cylinderEvents_le_pi le_rfl
  have hsplit : ∀ ω, oscAt g j / (4 * Z ω) = (oscAt g j / 4) * (Z ω)⁻¹ := by
    intro ω
    rw [div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_assoc]
  have hprod : Measurable fun ω ↦ (Z ω)⁻¹ * ENNReal.ofReal (g ω) := hZm.inv.fun_mul hĝm
  have hbase : AEMeasurable ((γ {j} : Kernel[cylinderEvents (X := fun _ : S ↦ E)
      ((({j} : Finset S) : Set S)ᶜ)] (S → E) (S → E)) : (S → E) → Measure (S → E)) μ :=
    (((γ {j}).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hone : ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂μ = 1 := by
    conv_lhs => rw [← hμ]
    rw [Measure.lintegral_bind hbase hprod.aemeasurable]
    have hinner : ∀ ξ : S → E,
        ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂(γ {j} ξ) = 1 := by
      intro ξ
      rw [(γ.isProper {j}).lintegral_mul (f := fun σ ↦ ENNReal.ofReal (g σ))
        (g := fun ω ↦ (Z ω)⁻¹) cylinderEvents_le_pi hĝm hZmB.inv ξ]
      exact ENNReal.inv_mul_cancel (hZ {j} ξ).1 (hZ {j} ξ).2
    rw [lintegral_congr hinner, lintegral_one, measure_univ]
  calc ∫⁻ ω, oscAt g j / (4 * Z ω) ∂(μ.withDensity fun σ ↦ ENNReal.ofReal (g σ))
      = ∫⁻ ω, ENNReal.ofReal (g ω) * ((oscAt g j / 4) * (Z ω)⁻¹) ∂μ := by
        rw [lintegral_congr hsplit, lintegral_withDensity_eq_lintegral_mul _ hĝm
          (show Measurable fun ω ↦ oscAt g j / 4 * (Z ω)⁻¹ from
            measurable_const.fun_mul hZm.inv)]
        rfl
    _ = (oscAt g j / 4) * ∫⁻ ω, (Z ω)⁻¹ * ENNReal.ofReal (g ω) ∂μ := by
        rw [← lintegral_const_mul _ hprod]
        exact lintegral_congr fun ω ↦ by ring
    _ = oscAt g j / 4 := by rw [hone, mul_one]

/-- **Georgii, Proposition (8.34)** for a strictly positive `g` normalized by `μ(g) = 1`:
`|μ(fg) − μ(f)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`. -/
theorem ofReal_abs_integral_mul_sub_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    (hgm : Measurable g) (hm : 0 < m) (hmg : ∀ σ, m ≤ g σ) (hgM : ∀ σ, g σ ≤ M)
    (hg1 : ∫ σ, g σ ∂μ = 1) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * g σ ∂μ) - ∫ σ, (f : (S → E) → ℝ) σ ∂μ|
      ≤ (∑' i, interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) / 4 := by
  classical
  have hĝm : Measurable fun σ ↦ ENNReal.ofReal (g σ) := hgm.ennreal_ofReal
  have hZ : Specification.IsRelAdmissible γ fun _ σ ↦ ENNReal.ofReal (g σ) :=
    isRelAdmissible_ofReal γ hm hmg hgM
  set ν : Measure (S → E) := μ.withDensity (fun σ ↦ ENNReal.ofReal (g σ)) with hνdef
  have hgint : Integrable g μ := ⟨hgm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := |m| + |M|) (Filter.Eventually.of_forall fun σ ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hm (hmg σ))]
      calc g σ ≤ M := hgM σ
        _ ≤ |m| + |M| := by have := abs_nonneg m; have := le_abs_self M; linarith)⟩
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hgint
        (Filter.Eventually.of_forall fun σ ↦ le_trans hm.le (hmg σ)), hg1, ENNReal.ofReal_one]
  have hν : ∀ i : S, ν.bind (γ.tilt hĝm hZ {i}) = ν := fun i ↦ bind_tilt_eq hĝm hZ (hμ i)
  set b : S → (S → E) → ℝ≥0∞ := fun i ω ↦
    oscAt g i / (4 * Specification.relZ γ (fun _ σ ↦ ENNReal.ofReal (g σ)) {i} ω) with hbdef
  have hbm : ∀ i, Measurable (b i) := fun i ↦
    measurable_const.div (measurable_const.mul
      ((Specification.measurable_relZ (γ := γ) (ρ := fun _ σ ↦ ENNReal.ofReal (g σ))
        (fun _ ↦ hĝm) {i}).mono cylinderEvents_le_pi le_rfl))
  have hb : ∀ i ω, unifDist (proj γ i ω) (proj (γ.tilt hĝm hZ) i ω) ≤ b i ω :=
    fun i ω ↦ unifDist_proj_tilt_le hgm hm hmg hgM hZ i ω
  have hcomp := comparison (γ := γ) (γ' := γ.tilt hĝm hZ) (μ := μ) (ν := ν) hγq hd hμ hν hbm hb
  have hbt : ∀ j, (∫⁻ ω, b j ω ∂ν) = 4⁻¹ * oscAt g j := by
    intro j
    rw [hbdef, lintegral_oscAt_div_eq hgm hZ j (hμ j), div_eq_mul_inv, mul_comm]
  have hfun : (fun j ↦ ∫⁻ ω, b j ω ∂ν) = fun j ↦ 4⁻¹ * oscAt g j := funext hbt
  have hest := (hcomp.isEstimate) f hf
  rw [hfun] at hest
  have hνint : ∫ σ, (f : (S → E) → ℝ) σ ∂ν = ∫ σ, (f : (S → E) → ℝ) σ * g σ ∂μ := by
    rw [hνdef, show (fun σ ↦ ENNReal.ofReal (g σ))
        = fun σ ↦ ((Real.toNNReal (g σ) : ℝ≥0) : ℝ≥0∞) from rfl,
      integral_withDensity_eq_integral_smul hgm.real_toNNReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ ↦ ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_trans hm.le (hmg σ)), mul_comm]
  rw [hνint] at hest
  rw [abs_sub_comm] at hest
  refine hest.trans (le_of_eq ?_)
  calc (∑' i, interdepSeries γ (fun j ↦ 4⁻¹ * oscAt g j) i * oscAt (⇑f) i)
      = ∑' i, 4⁻¹ * (interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) := by
        refine tsum_congr fun i ↦ ?_
        rw [interdepSeries_const_mul, mul_assoc]
    _ = (∑' i, interdepSeries γ (fun j ↦ oscAt g j) i * oscAt (⇑f) i) / 4 := by
        rw [ENNReal.tsum_mul_left, div_eq_mul_inv, mul_comm]

end Covariance

/-! ### Georgii, Proposition (8.34) -/

section Prop834

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] {γ : Specification S E}
  {μ : Measure (S → E)}

/-- **Georgii, Proposition (8.34).** If `γ` is quasilocal and satisfies Dobrushin's condition
(8.6) and `μ` is (the unique) Gibbs measure for `γ`, then for all quasilocal observables `f, g`

`|μ(fg) − μ(f)μ(g)| ≤ ¼ ∑_{i,j} δ_i(f) D_{ij}(γ) δ_j(g)`,

where `D(γ) = ∑_{n≥0} C(γ)^n` is Georgii's (8.19) (`interdepSeries`) and `δ_i` is the single-site
oscillation (8.14).

Georgii's proof, followed here: both sides are invariant under `g ↦ (g + c)/K`, so one may assume
`g > 0` and `μ(g) = 1`; then `μ̃ = g μ` is Gibbs for the tilted specification
`γ̃_Λ = (g/γ_Λ g) γ_Λ` (`Specification.tilt`, `bind_tilt_eq`), whose single-site projections
satisfy `‖γ_j^0(·|ω) − γ̃_j^0(·|ω)‖ ≤ δ_j(g)/4 γ_j g(ω)` (`unifDist_proj_tilt_le`), and the
comparison theorem (8.20) applies with `μ̃(b_j) = δ_j(g)/4` (`lintegral_oscAt_div_eq`). -/
theorem ofReal_abs_covariance_le [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
      ≤ (∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 := by
  classical
  have hgm : Measurable (⇑g) := measurable_of_mem_quasilocalFunctions hg
  have hfm : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  have hgb : ∀ σ, |(g : (S → E) → ℝ) σ| ≤ ‖g‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g σ
  have hfb : ∀ σ, |(f : (S → E) → ℝ) σ| ≤ ‖f‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f σ
  have hgint : Integrable (⇑g) μ := ⟨hgm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hgb σ)⟩
  have hfint : Integrable (⇑f) μ := ⟨hfm.aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ‖f‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hfb σ)⟩
  have hfgint : Integrable (fun σ ↦ (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ) μ :=
    ⟨(hfm.mul hgm).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := ‖f‖ * ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hfb σ) (hgb σ) (abs_nonneg _) (norm_nonneg f))⟩
  set c : ℝ := ‖g‖ + 1 with hcdef
  have hnormg : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
  have hlow : ∀ σ, (1 : ℝ) ≤ (g : (S → E) → ℝ) σ + c := fun σ ↦ by
    have h1 := neg_abs_le ((g : (S → E) → ℝ) σ)
    have h2 := hgb σ
    rw [hcdef]; linarith
  have hupp : ∀ σ, (g : (S → E) → ℝ) σ + c ≤ 2 * ‖g‖ + 1 := fun σ ↦ by
    have h2 := (abs_le.1 (hgb σ)).2
    rw [hcdef]; linarith
  have hunivreal : μ.real Set.univ = 1 := by rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hIg : |∫ σ, (g : (S → E) → ℝ) σ ∂μ| ≤ ‖g‖ := by
    rw [← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖g‖)
      (Filter.Eventually.of_forall fun σ ↦ by rw [Real.norm_eq_abs]; exact hgb σ)
    rwa [hunivreal, mul_one] at h
  set K : ℝ := (∫ σ, (g : (S → E) → ℝ) σ ∂μ) + c with hKdef
  have hK1 : (1 : ℝ) ≤ K := by
    have := (abs_le.1 hIg).1; rw [hKdef, hcdef]; linarith
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  set G : (S → E) → ℝ := fun σ ↦ ((g : (S → E) → ℝ) σ + c) / K with hGdef
  have hGm : Measurable G := (hgm.add_const c).div_const K
  have hGlow : ∀ σ, 1 / K ≤ G σ := fun σ ↦ by
    show (1 : ℝ) / K ≤ ((g : (S → E) → ℝ) σ + c) / K
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hlow σ) (inv_nonneg.2 hKpos.le)
  have hGupp : ∀ σ, G σ ≤ (2 * ‖g‖ + 1) / K := fun σ ↦ by
    show ((g : (S → E) → ℝ) σ + c) / K ≤ (2 * ‖g‖ + 1) / K
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hupp σ) (inv_nonneg.2 hKpos.le)
  have hG1 : ∫ σ, G σ ∂μ = 1 := by
    show (∫ σ, ((g : (S → E) → ℝ) σ + c) / K ∂μ) = 1
    rw [integral_div, integral_add hgint (integrable_const c), integral_const, hunivreal,
      one_smul, ← hKdef, div_self hKpos.ne']
  have hmain := ofReal_abs_integral_mul_sub_le (γ := γ) (μ := μ) hγq hd hμ hGm
    (one_div_pos.2 hKpos) hGlow hGupp hG1 hf
  -- rewrite the two sides
  have hfG : ∫ σ, (f : (S → E) → ℝ) σ * G σ ∂μ
      = ((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          + c * ∫ σ, (f : (S → E) → ℝ) σ ∂μ) / K := by
    have hpt : ∀ σ, (f : (S → E) → ℝ) σ * G σ
        = ((f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ + c * (f : (S → E) → ℝ) σ) / K := by
      intro σ; rw [hGdef]; field_simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
      integral_add hfgint (hfint.const_mul c), integral_const_mul]
  have hdiff : (∫ σ, (f : (S → E) → ℝ) σ * G σ ∂μ) - ∫ σ, (f : (S → E) → ℝ) σ ∂μ
      = ((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ) / K := by
    rw [hfG, eq_div_iff hKpos.ne', sub_mul, div_mul_cancel₀ _ hKpos.ne', hKdef]; ring
  have hoscG : ∀ j, oscAt G j = (ENNReal.ofReal K)⁻¹ * oscAt (⇑g) j := by
    intro j
    have hfun : G = fun σ ↦ K⁻¹ * (g : (S → E) → ℝ) σ + c / K := by
      funext σ; rw [hGdef]; field_simp
    rw [hfun, oscAt_affine _ (inv_ne_zero hKpos.ne') _ j,
      abs_of_pos (inv_pos.2 hKpos), ENNReal.ofReal_inv_of_pos hKpos]
  rw [hdiff] at hmain
  -- cancel the factor `K`
  have hRHS : (∑' i, interdepSeries γ (fun j ↦ oscAt G j) i * oscAt (⇑f) i) / 4
      = (ENNReal.ofReal K)⁻¹
        * ((∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4) := by
    have hstep : ∀ i, interdepSeries γ (fun j ↦ oscAt G j) i * oscAt (⇑f) i
        = (ENNReal.ofReal K)⁻¹
          * (interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) := by
      intro i
      rw [funext hoscG, interdepSeries_const_mul, mul_assoc]
    rw [tsum_congr hstep, ENNReal.tsum_mul_left, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  have hLHS : ENNReal.ofReal
      (|((∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
          - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ) / K|)
      = (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal
          |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
            - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ| := by
    rw [abs_div, abs_of_pos hKpos, ENNReal.ofReal_div_of_pos hKpos, ENNReal.div_eq_inv_mul]
  rw [hLHS, hRHS] at hmain
  have hKne : ENNReal.ofReal K ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.2 hKpos).ne'
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.2 hKne)).1 hmain

/-- **Georgii, Proposition (8.34)**, in the summable form used in his proof of Corollary (8.37):
if `c(γ) ≤ c` then

`|μ(fg) − μ(f)μ(g)| ≤ (sup_j δ_j(g)) (∑_i δ_i(f)) / 4(1 − c)`,

because Dobrushin's condition bounds the row sums of `D(γ)` by `(1 − c)⁻¹`
(`interdepSeries_le`). -/
theorem ofReal_abs_covariance_le_of_iSup [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ) {c : ℝ≥0∞}
    (hc : ∀ i, ∑' j, interdep γ i j ≤ c)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
      ≤ (⨆ j, oscAt (⇑g) j) * (∑' i, oscAt (⇑f) i) / (4 * (1 - c)) := by
  refine (ofReal_abs_covariance_le hγq hd hμ hf hg).trans ?_
  have hrow : ∀ i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i ≤ (⨆ j, oscAt (⇑g) j) / (1 - c) :=
    fun i ↦ interdepSeries_le γ hc (fun j ↦ le_iSup (fun j ↦ oscAt (⇑g) j) j) i
  calc (∑' i, interdepSeries γ (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4
      ≤ (∑' i, ((⨆ j, oscAt (⇑g) j) / (1 - c)) * oscAt (⇑f) i) / 4 := by
        gcongr with i
        exact hrow i
    _ = ((⨆ j, oscAt (⇑g) j) / (1 - c)) * (∑' i, oscAt (⇑f) i) / 4 := by
        rw [ENNReal.tsum_mul_left]
    _ = (⨆ j, oscAt (⇑g) j) * (∑' i, oscAt (⇑f) i) / (4 * (1 - c)) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        ring

/-! #### (8.34) against a `t`-uniform majorant of the interdependence matrix

Georgii's proof of Corollary (8.37) applies (8.34) with the matrix `D_ij = sup_{|t| ≤ t₀}
D_ij(γ^{Φ+tΨ})`, dominated by `matSeries C` for any entrywise majorant `C` of the interdependence
matrices; and it applies it both to the unique Gibbs measure and, through Lemma (8.22)(ii), to
the finite-volume distributions `γ_Λ(·|ω)`. -/

/-- **Georgii, Proposition (8.34)** against an entrywise majorant `C ≥ C(γ)` of the
interdependence matrix. -/
theorem ofReal_abs_covariance_le_matSeries [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ) {C : S → S → ℝ≥0∞}
    (hC : ∀ i j, interdep γ i j ≤ C i j)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂μ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂μ) * ∫ σ, (g : (S → E) → ℝ) σ ∂μ|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 := by
  refine (ofReal_abs_covariance_le hγq hd hμ hf hg).trans ?_
  gcongr with i
  exact matSeries_mono_matrix hC _ i

/-- **Georgii, Proposition (8.34) at finite volume**, through Lemma (8.22)(ii): `γ_Λ(·|ω)` is the
unique Gibbs measure of the conditioned specification `γ^{(Λ,ω)}`, whose interdependence matrix
is dominated by that of `γ`, so the same covariance estimate holds for it — with the *same*
matrix, uniformly in `Λ` and `ω`. -/
theorem ofReal_abs_covariance_apply_le_matSeries (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    {C : S → S → ℝ≥0∞} (hC : ∀ i j, interdep γ i j ≤ C i j) (Λ : Finset S) (ω : S → E)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |(∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂(γ Λ ω))
        - (∫ σ, (f : (S → E) → ℝ) σ ∂(γ Λ ω)) * ∫ σ, (g : (S → E) → ℝ) σ ∂(γ Λ ω)|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 :=
  ofReal_abs_covariance_le_matSeries (γ := condSpec γ Λ ω) (isQuasilocal_condSpec hγq Λ ω)
    (isDobrushin_condSpec hd Λ ω) (fun i ↦ bind_condSpec_eq γ Λ ω {i})
    (fun i j ↦ (interdep_condSpec_le γ Λ ω i j).trans (hC i j)) hf hg

end Prop834

/-! ### Georgii Corollary (8.37): the finite-volume derivative in the potential

The local step of Georgii's Corollary (8.37) is the identity
`γ^{βΦ}_Λ(·|ω) = (λ_Λ ⊗ δ_ω).tilted (−β H^Φ_Λ)`: a finite-volume Gibbs distribution is the
exponential tilt of the free measure by the Hamiltonian. Differentiating under the integral sign
(`MeasureTheory.hasDerivAt_integral_tilted_add_mul`) then gives Georgii's displayed formula
`∂/∂t γ^{Φ+tΨ}_Λ(g|ω) = −⟨H^Ψ_Λ, g⟩^t_Λ`, where `⟨·,·⟩^t_Λ` is the covariance under
`γ^{Φ+tΨ}_Λ(·|ω)`.

The tilt identity is a statement about `Potential.gibbsSpecificationOfAbsolutelySummable`, and
belongs next to that definition in `GibbsMeasure/Potential/Summable.lean`; it is placed here
because it is the entry point of §8.2's differentiation.
-/

section FiniteVolumeDerivative

open Potential Specification

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ Ψ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν]

variable (Φ) in
omit [Countable S] [IsPotential Φ] in
/-- The Hamiltonian over a finite volume is bounded by `Potential.hamiltonianBound`. -/
lemma abs_neg_mul_hamiltonian_le (β : ℝ) (Λ : Finset S) (σ : S → E) :
    |-β * Φ.hamiltonian Λ σ| ≤ |β| * Φ.hamiltonianBound Λ := by
  rw [abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le Λ σ) (abs_nonneg β)

variable (Φ) in
/-- `exp(−β H^Φ_Λ)` is integrable against any probability measure: it is measurable and
bounded. -/
lemma integrable_exp_neg_mul_hamiltonian (β : ℝ) (Λ : Finset S) {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] :
    Integrable (fun σ ↦ Real.exp (-β * Φ.hamiltonian Λ σ)) μ :=
  integrable_of_forall_abs_le
    ((measurable_const.mul (measurable_hamiltonian (Φ := Φ) Λ)).exp)
    (C := Real.exp (|β| * Φ.hamiltonianBound Λ)) fun σ ↦ by
      rw [Real.abs_exp]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_neg_mul_hamiltonian_le Φ β Λ σ))

/-- **The finite-volume Gibbs distribution is an exponential tilt.** For an absolutely summable
potential and a probability spin distribution,
`γ^{βΦ}_Λ(·|ω) = (λ_Λ ⊗ δ_ω).tilted (−β H^Φ_Λ)`, where `λ_Λ ⊗ δ_ω = Specification.isssd ν Λ ω`
is Georgii's free measure with boundary condition `ω`. -/
theorem gibbsSpecificationOfAbsolutelySummable_eq_tilted (β : ℝ) (Λ : Finset S) (ω : S → E) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ ω
      = (isssd (S := S) (E := E) ν Λ ω).tilted fun σ ↦ -β * Φ.hamiltonian Λ σ := by
  have hint : Integrable (fun σ ↦ Real.exp (-β * Φ.hamiltonian Λ σ))
      (isssd (S := S) (E := E) ν Λ ω) := integrable_exp_neg_mul_hamiltonian Φ β Λ
  have hZpos : 0 < ∫ σ, Real.exp (-β * Φ.hamiltonian Λ σ) ∂(isssd (S := S) (E := E) ν Λ ω) :=
    integral_exp_pos hint
  have hZ : premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ ω
      = ENNReal.ofReal (∫ σ, Real.exp (-β * Φ.hamiltonian Λ σ)
          ∂(isssd (S := S) (E := E) ν Λ ω)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun σ ↦ (Real.exp_pos _).le)]
    rfl
  refine Measure.ext fun A hA ↦ ?_
  rw [gibbsSpecificationOfAbsolutelySummable, Specification.modification_apply,
    withDensity_premodifierNorm_apply ν (isPremodifier_boltzmannFactor (Φ := Φ) β) hA ω, hZ,
    tilted_apply' _ _ hA]
  have hpt : ∀ a : S → E,
      ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ a)
          / ∫ x, Real.exp (-β * Φ.hamiltonian Λ x) ∂(isssd (S := S) (E := E) ν Λ ω))
        = (ENNReal.ofReal (∫ x, Real.exp (-β * Φ.hamiltonian Λ x)
            ∂(isssd (S := S) (E := E) ν Λ ω)))⁻¹ * Φ.boltzmannFactor β Λ a := by
    intro a
    rw [ENNReal.ofReal_div_of_pos hZpos, ENNReal.div_eq_inv_mul]
    rfl
  rw [lintegral_congr hpt, lintegral_const_mul _ (measurable_boltzmannFactor (Φ := Φ) β Λ)]

variable (Φ) in
/-- The Gibbs specification of `Φ + tΨ` is the free measure tilted along the line
`t ↦ −H^Φ_Λ − t H^Ψ_Λ`. -/
lemma gibbsSpecification_add_smul_eq_tilted (Ψ : Potential S E) [IsPotential Ψ]
    [IsAbsolutelySummable Ψ] (Λ : Finset S) (ω : S → E) (t : ℝ) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ + t • Ψ) ν 1 Λ ω
      = (isssd (S := S) (E := E) ν Λ ω).tilted
          fun σ ↦ -Φ.hamiltonian Λ σ + t * -Ψ.hamiltonian Λ σ := by
  rw [gibbsSpecificationOfAbsolutelySummable_eq_tilted ν 1 Λ ω]
  congr 1 with σ
  rw [hamiltonian_add, hamiltonian_smul]
  ring

variable (Φ) in
/-- **Georgii, in the proof of Corollary (8.37).** The finite-volume Gibbs expectation of a
bounded measurable observable is differentiable in the potential direction, with

`∂/∂t γ^{Φ+tΨ}_Λ(g|ω) = −⟨H^Ψ_Λ, g⟩^t_Λ`,

the covariance of the Hamiltonian `H^Ψ_Λ` and `g` under `γ^{Φ+tΨ}_Λ(·|ω)`. Both sides are
finite because `H^Ψ_Λ` and `g` are bounded; the proof differentiates numerator and denominator
of the tilt under the integral sign. -/
theorem hasDerivAt_integral_gibbsSpecification (Ψ : Potential S E) [IsPotential Ψ]
    [IsAbsolutelySummable Ψ] {g : (S → E) → ℝ} (hg : Measurable g) {Cg : ℝ}
    (hgb : ∀ σ, |g σ| ≤ Cg) (Λ : Finset S) (ω : S → E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ∫ σ, g σ ∂(gibbsSpecificationOfAbsolutelySummable
        (Φ := Φ + s • Ψ) ν 1 Λ ω))
      (-((∫ σ, g σ * Ψ.hamiltonian Λ σ
            ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + t • Ψ) ν 1 Λ ω))
          - (∫ σ, g σ ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + t • Ψ) ν 1 Λ ω))
            * ∫ σ, Ψ.hamiltonian Λ σ
                ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + t • Ψ) ν 1 Λ ω))) t := by
  have hu : Measurable fun σ : S → E ↦ -Φ.hamiltonian Λ σ :=
    (measurable_hamiltonian (Φ := Φ) Λ).neg
  have hv : Measurable fun σ : S → E ↦ -Ψ.hamiltonian Λ σ :=
    (measurable_hamiltonian (Φ := Ψ) Λ).neg
  have hub : ∀ σ, |-Φ.hamiltonian Λ σ| ≤ Φ.hamiltonianBound Λ := fun σ ↦ by
    rw [abs_neg]; exact abs_hamiltonian_le Λ σ
  have hvb : ∀ σ, |-Ψ.hamiltonian Λ σ| ≤ Ψ.hamiltonianBound Λ := fun σ ↦ by
    rw [abs_neg]; exact abs_hamiltonian_le Λ σ
  have hmain := hasDerivAt_integral_tilted_add_mul (μ := isssd (S := S) (E := E) ν Λ ω)
    hu hv hg hub hvb hgb t
  simp only [← gibbsSpecification_add_smul_eq_tilted (Φ := Φ) (ν := ν) (Ψ := Ψ) Λ ω]
    at hmain
  refine hmain.congr_deriv ?_
  rw [show (fun σ : S → E ↦ g σ * -Ψ.hamiltonian Λ σ)
      = fun σ : S → E ↦ -(g σ * Ψ.hamiltonian Λ σ) from funext fun σ ↦ by ring,
    integral_neg, integral_neg]
  ring


end FiniteVolumeDerivative

/-! ### The Hamiltonian as a bounded quasilocal observable

`H^Φ_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` is a uniformly convergent sum of local observables, hence bounded and
quasilocal; this is what lets Proposition (8.34) be applied to it in Georgii's estimate of `T₁`
in the proof of Corollary (8.37). The construction copies `Potential.siteEnergyLp`.
-/

section HamiltonianLp

open Potential

variable {S E : Type*} [Countable S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]

variable (Φ) in
/-- The term `Φ_A` of the Hamiltonian `H^Φ_Λ`, as a bounded observable. -/
def hamiltonianTermLp (Λ A : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ Φ.hamiltonianTerms Λ η A, memℓp_infty ⟨(Φ.termNorm Λ A).toReal, by
    rintro _ ⟨η, rfl⟩
    have h := enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
    rw [← ENNReal.toReal_le_toReal (by simp) (termNorm_ne_top (Φ := Φ) Λ A)] at h
    simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
      using h⟩⟩

omit [Countable S] [IsPotential Φ] in
lemma norm_hamiltonianTermLp_le (Λ A : Finset S) :
    ‖hamiltonianTermLp Φ Λ A‖ ≤ (Φ.termNorm Λ A).toReal := by
  refine lp.norm_le_of_forall_le ENNReal.toReal_nonneg fun η ↦ ?_
  have h := enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
  rw [← ENNReal.toReal_le_toReal (by simp) (termNorm_ne_top (Φ := Φ) Λ A)] at h
  simpa [hamiltonianTermLp, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _),
    Real.norm_eq_abs] using h

omit [Countable S] [IsPotential Φ] in
lemma summable_hamiltonianTermLp (Λ : Finset S) : Summable (hamiltonianTermLp Φ Λ) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun A ↦ norm_nonneg _)
    (fun A ↦ norm_hamiltonianTermLp_le (Φ := Φ) Λ A) ?_)
  exact ENNReal.summable_toReal (tsum_termNorm_ne_top (Φ := Φ) Λ)

omit [Countable S] in
lemma hamiltonianTermLp_mem_localFunctionsOn (Λ A : Finset S) :
    hamiltonianTermLp Φ Λ A ∈ localFunctionsOn S E A := by
  change Measurable[cylinderEvents (X := fun _ : S ↦ E) (A : Set S)]
    (fun η ↦ Φ.hamiltonianTerms Λ η A)
  by_cases h : Disjoint A Λ
  · simp only [hamiltonianTerms_of_disjoint h]
    exact measurable_const
  · simp only [hamiltonianTerms_of_not_disjoint h]
    exact IsPotential.measurable (Φ := Φ) A

variable (Φ) in
/-- Georgii's Hamiltonian `H^Φ_Λ` as a bounded observable. -/
def hamiltonianLp (Λ : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨Φ.hamiltonian Λ, memℓp_infty ⟨Φ.hamiltonianBound Λ, by
    rintro _ ⟨η, rfl⟩
    show ‖Φ.hamiltonian Λ η‖ ≤ Φ.hamiltonianBound Λ
    rw [Real.norm_eq_abs]
    exact abs_hamiltonian_le (Φ := Φ) Λ η⟩⟩

omit [Countable S] [IsPotential Φ] in
@[simp] lemma coeFn_hamiltonianLp (Λ : Finset S) :
    ⇑(hamiltonianLp Φ Λ) = Φ.hamiltonian Λ := rfl

omit [Countable S] [IsPotential Φ] in
lemma hasSum_hamiltonianTermLp (Λ : Finset S) :
    HasSum (hamiltonianTermLp Φ Λ) (hamiltonianLp Φ Λ) := by
  obtain ⟨T, hT⟩ := summable_hamiltonianTermLp (Φ := Φ) Λ
  have hpt : ∀ η : S → E, (T : (S → E) → ℝ) η = Φ.hamiltonian Λ η := by
    intro η
    have h1 : HasSum (fun A ↦ (hamiltonianTermLp Φ Λ A : (S → E) → ℝ) η)
        ((T : (S → E) → ℝ) η) := by
      refine (lp.tendsto_apply_of_tendsto hT η).congr fun s ↦ ?_
      simp only [hamiltonianTermLp, lp.coeFn_sum]
      exact Finset.sum_apply _ _ _
    rw [hamiltonian_eq_tsum (Φ := Φ) Λ η]
    exact h1.unique (summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum
  have hTeq : T = hamiltonianLp Φ Λ := lp.ext (funext hpt)
  exact hTeq ▸ hT

omit [Countable S] in
/-- **Georgii (2.14)/(2.20).** The Hamiltonian of an absolutely summable potential over a finite
volume is a bounded quasilocal observable. -/
theorem hamiltonianLp_mem_quasilocalFunctions (Λ : Finset S) :
    hamiltonianLp Φ Λ ∈ quasilocalFunctions S E := by
  refine (Subalgebra.isClosed_topologicalClosure (localFunctions S E)).mem_of_tendsto
    (hasSum_hamiltonianTermLp (Φ := Φ) Λ) (.of_forall fun s ↦ ?_)
  exact Subalgebra.sum_mem _ fun A _ ↦ localFunctions_le_quasilocalFunctions
    (mem_localFunctions.2 ⟨A, hamiltonianTermLp_mem_localFunctionsOn (Φ := Φ) Λ A⟩)

end HamiltonianLp

/-! ### Georgii's `T₁` estimate: the boundary part of the Hamiltonian

Georgii's proof of Corollary (8.37) compares the Hamiltonian `H^Ψ_Λ` with the sum
`∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}` of the energy densities `Potential.siteEnergy` (15.22) over `Λ`. Their
difference is `∑_{A ∩ Λ ≠ ∅} (|A ∖ Λ| / |A|) Ψ_A`, which oscillates at the site `j` by at most
`2 ∑_{A ∋ j, A ⊄ Λ} ‖Ψ_A‖ = 2 ‖Ψ‖(Λ, {j})`, a quantity that vanishes as `Λ ↑ S`
(`Potential.tendsto_tailWeight_atTop`).
-/

section BoundaryOscillation

open Potential

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] {Φ : Potential S E}
  [IsPotential Φ] [IsAbsolutelySummable Φ]

omit [Countable S] [IsAbsolutelySummable Φ] in
/-- The terms of `H^Φ_Λ − ∑_{k ∈ Λ} f_Φ ∘ θ_{−k}` oscillate at the site `j` by at most `2‖Φ_A‖`,
and only when `j ∈ A` and `A ⊄ Λ`. -/
lemma oscAt_hamiltonianTerms_sub_le (Λ : Finset S) (j : S) (A : Finset S) :
    oscAt (fun η ↦ Φ.hamiltonianTerms Λ η A
        - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η) j
      ≤ 2 * {B : Finset S | ¬ Disjoint B ({j} : Finset S) ∧ ¬ B ⊆ Λ}.indicator
          (fun B ↦ ⨆ η, ‖Φ B η‖ₑ) A := by
  classical
  have hzero : ∀ (hd : Disjoint A Λ) (η : S → E),
      Φ.hamiltonianTerms Λ η A - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η = 0 := by
    intro hd η
    rw [hamiltonianTerms_of_disjoint hd, Finset.disjoint_iff_inter_eq_empty.1 hd]
    simp
  by_cases hj : j ∈ A
  · by_cases hsub : A ⊆ Λ
    · have hd : ¬ Disjoint A Λ := by
        rw [Finset.not_disjoint_iff]; exact ⟨j, hj, hsub hj⟩
      have hcard : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
      have hfun : (fun η ↦ Φ.hamiltonianTerms Λ η A
          - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η) = fun _ ↦ (0 : ℝ) := by
        funext η
        rw [hamiltonianTerms_of_not_disjoint hd, Finset.inter_eq_left.2 hsub,
          div_self hcard.ne', one_mul, sub_self]
      rw [hfun, oscAt_const]
      exact bot_le
    · rw [Set.indicator_of_mem
        (show A ∈ {B : Finset S | ¬ Disjoint B ({j} : Finset S) ∧ ¬ B ⊆ Λ} from
          ⟨by simpa using hj, hsub⟩)]
      by_cases hd : Disjoint A Λ
      · rw [funext (hzero hd), oscAt_const]
        exact bot_le
      · have hcard : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨j, hj⟩
        have hfun : (fun η ↦ Φ.hamiltonianTerms Λ η A
            - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η)
            = fun η ↦ (1 - ((A ∩ Λ).card : ℝ) / (A.card : ℝ)) * Φ A η := by
          funext η
          rw [hamiltonianTerms_of_not_disjoint hd]
          ring
        have hc : |1 - ((A ∩ Λ).card : ℝ) / (A.card : ℝ)| ≤ 1 := by
          have h0 : (0 : ℝ) ≤ ((A ∩ Λ).card : ℝ) / (A.card : ℝ) := by positivity
          have h1 : ((A ∩ Λ).card : ℝ) / (A.card : ℝ) ≤ 1 :=
            div_le_one_of_le₀
              (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left) hcard.le
          rw [abs_le]; constructor <;> linarith
        rw [hfun]
        refine (oscAt_const_mul_le _ (Φ A) j).trans ?_
        calc ENNReal.ofReal |1 - ((A ∩ Λ).card : ℝ) / (A.card : ℝ)| * oscAt (Φ A) j
            ≤ 1 * osc (Φ A) := mul_le_mul' (ENNReal.ofReal_le_one.2 hc) oscAt_le_osc
          _ ≤ 2 * ⨆ η, ‖Φ A η‖ₑ := by rw [one_mul]; exact osc_le_two_mul_iSup _
  · have hdep : DependsOn (fun η ↦ Φ.hamiltonianTerms Λ η A
        - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η) (A : Set S) := by
      intro η ζ hηζ
      dsimp only
      by_cases hd : Disjoint A Λ
      · rw [hzero hd, hzero hd]
      · rw [hamiltonianTerms_of_not_disjoint hd, hamiltonianTerms_of_not_disjoint hd,
          IsPotential.dependsOn (Φ := Φ) A hηζ]
    rw [oscAt_eq_zero_of_dependsOn hdep (by simpa using hj)]
    exact bot_le

omit [Countable S] in
/-- **Georgii, in the proof of Corollary (8.37).** The difference between the Hamiltonian in `Λ`
and the sum over `Λ` of the energy densities `f_Φ ∘ θ_{−k}` (15.22) oscillates at each site `j`
by at most `2 ∑_{A ∋ j, A ⊄ Λ} ‖Φ_A‖`. -/
theorem oscAt_hamiltonian_sub_sum_siteEnergy_le (Λ : Finset S) (j : S) :
    oscAt (fun η ↦ Φ.hamiltonian Λ η - ∑ k ∈ Λ, Φ.siteEnergy k η) j
      ≤ 2 * Φ.tailWeight Λ {j} := by
  have hsummable : ∀ η : S → E, Summable fun A : Finset S ↦
      Φ.hamiltonianTerms Λ η A - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η := fun η ↦
    (summable_hamiltonianTerms (Φ := Φ) Λ η).sub (summable_card_inter_div_mul (Φ := Φ) Λ η)
  have hfun : (fun η ↦ Φ.hamiltonian Λ η - ∑ k ∈ Λ, Φ.siteEnergy k η)
      = fun η ↦ ∑' A : Finset S,
          (Φ.hamiltonianTerms Λ η A - ((A ∩ Λ).card : ℝ) / (A.card : ℝ) * Φ A η) := by
    funext η
    rw [hamiltonian_eq_tsum (Φ := Φ) Λ η, sum_siteEnergy (Φ := Φ) Λ η,
      (summable_hamiltonianTerms (Φ := Φ) Λ η).tsum_sub
        (summable_card_inter_div_mul (Φ := Φ) Λ η)]
  rw [hfun]
  refine (oscAt_tsum_le _ hsummable j).trans ?_
  rw [tailWeight, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun A ↦ oscAt_hamiltonianTerms_sub_le (Φ := Φ) Λ j A

/-! ### The oscillations of the energy densities

Georgii's `∑_k δ_k(f_Ψ) ≤ 2 ∑_k ∑_{A ⊇ {0,k}} |A|⁻¹ ‖Ψ_A‖ = 2 ‖Ψ‖₀`, in the two forms needed for
`T₂` and `T₃`: the single-site oscillations of one energy density `f_Φ ∘ θ_{−k}` are summable
over the sites, and so are the oscillations at one site of all the energy densities.
-/

omit [Countable S] [IsAbsolutelySummable Φ] in
/-- The term `|A|⁻¹ Φ_A` of the energy density at `k` oscillates at `j` only when `A` contains
both sites, and then by at most `|A|⁻¹ δ(Φ_A)`. -/
lemma oscAt_siteEnergyTerms_le (k j : S) (A : Finset S) :
    oscAt (fun η ↦ Φ.siteEnergyTerms k η A) j
      ≤ {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A := by
  have hdep : DependsOn (fun η ↦ Φ.siteEnergyTerms k η A) (A : Set S) := by
    intro η ζ hηζ
    dsimp only
    by_cases hk : k ∈ A
    · rw [siteEnergyTerms_of_mem hk, siteEnergyTerms_of_mem hk,
        IsPotential.dependsOn (Φ := Φ) A hηζ]
    · rw [siteEnergyTerms_of_not_mem hk, siteEnergyTerms_of_not_mem hk]
  by_cases hk : k ∈ A
  · by_cases hj : j ∈ A
    · rw [Set.indicator_of_mem
        (show A ∈ {B : Finset S | k ∈ B ∧ j ∈ B} from ⟨hk, hj⟩)]
      simp only [siteEnergyTerms_of_mem hk]
      refine (oscAt_const_mul_le _ (Φ A) j).trans ?_
      have hcard : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨k, hk⟩
      have hinv : ENNReal.ofReal |((A.card : ℝ))⁻¹| = ((A.card : ℝ≥0∞))⁻¹ := by
        rw [abs_of_nonneg (by positivity), ENNReal.ofReal_inv_of_pos hcard,
          ENNReal.ofReal_natCast]
      rw [hinv]
      exact mul_le_mul' le_rfl oscAt_le_osc
    · rw [oscAt_eq_zero_of_dependsOn hdep (by simpa using hj)]
      exact bot_le
  · simp only [siteEnergyTerms_of_not_mem hk, oscAt_const]
    exact bot_le

omit [Countable S] in
/-- `δ_j(f_Φ ∘ θ_{−k}) ≤ ∑_{A ⊇ {k,j}} |A|⁻¹ δ(Φ_A)`. -/
lemma oscAt_siteEnergy_le (k j : S) :
    oscAt (Φ.siteEnergy k) j
      ≤ ∑' A : Finset S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A :=
  (oscAt_tsum_le (fun A η ↦ Φ.siteEnergyTerms k η A)
      (fun η ↦ summable_siteEnergyTerms (Φ := Φ) k η) j).trans
    (ENNReal.tsum_le_tsum fun A ↦ oscAt_siteEnergyTerms_le (Φ := Φ) k j A)

/-- Summing `∑_{A ⊇ {k,j}} |A|⁻¹ δ(Φ_A)` over the second site telescopes the factor `|A|⁻¹`. -/
lemma tsum_indicator_pair_le {S E : Type*} [DecidableEq S] (Φ : Finset S → (S → E) → ℝ)
    (k : S) (A : Finset S) :
    ∑' j : S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
        (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A
      ≤ {B : Finset S | k ∈ B}.indicator (fun B ↦ 2 * ⨆ η, ‖Φ B η‖ₑ) A := by
  classical
  by_cases hk : k ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | k ∈ B} from hk)]
    have hpt : ∀ j : S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
        (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A
        = if j ∈ A then ((A.card : ℝ≥0∞))⁻¹ * osc (Φ A) else 0 := by
      intro j
      by_cases hj : j ∈ A
      · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | k ∈ B ∧ j ∈ B} from ⟨hk, hj⟩)]
        simp [hj]
      · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | k ∈ B ∧ j ∈ B} from
          fun h ↦ hj h.2)]
        simp [hj]
    have hcard : (A.card : ℝ≥0∞) ≠ 0 := by
      simpa using (Finset.card_pos.2 ⟨k, hk⟩).ne'
    calc ∑' j : S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
            (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A
        = ∑' j : S, (if j ∈ A then ((A.card : ℝ≥0∞))⁻¹ * osc (Φ A) else 0) := tsum_congr hpt
      _ = (A.card : ℝ≥0∞) * (((A.card : ℝ≥0∞))⁻¹ * osc (Φ A)) := by
          rw [tsum_eq_sum (s := A) fun b hb ↦ by simp [hb], Finset.sum_ite_mem,
            Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
      _ = osc (Φ A) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hcard (by simp), one_mul]
      _ ≤ 2 * ⨆ η, ‖Φ A η‖ₑ := osc_le_two_mul_iSup _
  · have hpt : ∀ j : S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
        (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A = 0 := fun j ↦
      Set.indicator_of_notMem (fun h ↦ hk h.1) _
    rw [tsum_congr hpt, tsum_zero]
    exact bot_le

omit [Countable S] [IsAbsolutelySummable Φ] [IsPotential Φ] in
lemma tsum_indicator_mem_eq_two_mul_normAt (k : S) :
    ∑' A : Finset S, {B : Finset S | k ∈ B}.indicator (fun B ↦ 2 * ⨆ η, ‖Φ B η‖ₑ) A
      = 2 * Φ.normAt k := by
  rw [Potential.normAt, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun A ↦ ?_
  by_cases h : k ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | k ∈ B} from h),
      Set.indicator_of_mem (show A ∈ {B : Finset S | k ∈ B} from h)]
  · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | k ∈ B} from h),
      Set.indicator_of_notMem (show A ∉ {B : Finset S | k ∈ B} from h), mul_zero]

omit [Countable S] in
/-- **Georgii, in the proof of Corollary (8.37):** `∑_j δ_j(f_Φ ∘ θ_{−k}) ≤ 2 ‖Φ‖_k`. -/
theorem tsum_oscAt_siteEnergy_le (k : S) :
    ∑' j : S, oscAt (Φ.siteEnergy k) j ≤ 2 * Φ.normAt k := by
  calc ∑' j : S, oscAt (Φ.siteEnergy k) j
      ≤ ∑' j : S, ∑' A : Finset S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A :=
        ENNReal.tsum_le_tsum fun j ↦ oscAt_siteEnergy_le (Φ := Φ) k j
    _ = ∑' A : Finset S, ∑' j : S, {B : Finset S | k ∈ B ∧ j ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A := ENNReal.tsum_comm
    _ ≤ ∑' A : Finset S, {B : Finset S | k ∈ B}.indicator
          (fun B ↦ 2 * ⨆ η, ‖Φ B η‖ₑ) A :=
        ENNReal.tsum_le_tsum fun A ↦ tsum_indicator_pair_le Φ k A
    _ = 2 * Φ.normAt k := tsum_indicator_mem_eq_two_mul_normAt (Φ := Φ) k

omit [Countable S] in
/-- **Georgii, in the proof of Corollary (8.37):** `∑_k δ_j(f_Φ ∘ θ_{−k}) ≤ 2 ‖Φ‖_j`; this is
what makes the tail `∑_{k ∉ Δ} |⟨f_Φ ∘ θ_{−k}, g⟩|` of Georgii's `T₃` small. -/
theorem tsum_oscAt_siteEnergy_le' (j : S) :
    ∑' k : S, oscAt (Φ.siteEnergy k) j ≤ 2 * Φ.normAt j := by
  have hset : ∀ k : S, {B : Finset S | k ∈ B ∧ j ∈ B} = {B : Finset S | j ∈ B ∧ k ∈ B} :=
    fun k ↦ Set.ext fun B ↦ and_comm
  calc ∑' k : S, oscAt (Φ.siteEnergy k) j
      ≤ ∑' k : S, ∑' A : Finset S, {B : Finset S | j ∈ B ∧ k ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A :=
        ENNReal.tsum_le_tsum fun k ↦ (hset k ▸ oscAt_siteEnergy_le (Φ := Φ) k j)
    _ = ∑' A : Finset S, ∑' k : S, {B : Finset S | j ∈ B ∧ k ∈ B}.indicator
          (fun B ↦ ((B.card : ℝ≥0∞))⁻¹ * osc (Φ B)) A := ENNReal.tsum_comm
    _ ≤ ∑' A : Finset S, {B : Finset S | j ∈ B}.indicator
          (fun B ↦ 2 * ⨆ η, ‖Φ B η‖ₑ) A :=
        ENNReal.tsum_le_tsum fun A ↦ tsum_indicator_pair_le Φ j A
    _ = 2 * Φ.normAt j := tsum_indicator_mem_eq_two_mul_normAt (Φ := Φ) j

end BoundaryOscillation

/-! ### Georgii's `T₁`: the boundary part of the Hamiltonian is negligible

`H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}` is a bounded quasilocal observable whose covariance with `g`,
estimated by Proposition (8.34) against a fixed majorant `C` of the interdependence matrices,
tends to `0` as `Λ ↑ S` — uniformly in the potential along the segment, because the majorant does
not depend on it.
-/

section BoundaryTerm

open Potential

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] {Ψ : Potential S E}
  [IsPotential Ψ] [IsAbsolutelySummable Ψ]

variable (Ψ) in
/-- Georgii's `H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}`, the boundary part of the Hamiltonian, as a
bounded observable. -/
def hamiltonianRemLp (Λ : Finset S) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  hamiltonianLp Ψ Λ - ∑ k ∈ Λ, Ψ.siteEnergyLp k

omit [Countable S] [DecidableEq S] [IsPotential Ψ] in
lemma coeFn_hamiltonianRemLp (Λ : Finset S) :
    ⇑(hamiltonianRemLp Ψ Λ) = fun η ↦ Ψ.hamiltonian Λ η - ∑ k ∈ Λ, Ψ.siteEnergy k η := by
  funext η
  rw [hamiltonianRemLp, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [coeFn_hamiltonianLp, coeFn_siteEnergyLp]

omit [Countable S] [DecidableEq S] in
lemma hamiltonianRemLp_mem_quasilocalFunctions (Λ : Finset S) :
    hamiltonianRemLp Ψ Λ ∈ quasilocalFunctions S E :=
  Subalgebra.sub_mem _ (hamiltonianLp_mem_quasilocalFunctions Λ)
    (Subalgebra.sum_mem _ fun k _ ↦ siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k)

omit [Countable S] in
/-- Georgii's oscillation bound for the boundary part: `δ_j(H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k})
≤ 2 ∑_{A ∋ j, A ⊄ Λ} ‖Ψ_A‖`. -/
lemma oscAt_hamiltonianRemLp_le (Λ : Finset S) (j : S) :
    oscAt (⇑(hamiltonianRemLp Ψ Λ)) j ≤ 2 * Ψ.tailWeight Λ {j} := by
  rw [coeFn_hamiltonianRemLp]
  exact oscAt_hamiltonian_sub_sum_siteEnergy_le (Φ := Ψ) Λ j

omit [Countable S] in
lemma oscAt_hamiltonianRemLp_le_normAt (Λ : Finset S) (j : S) :
    oscAt (⇑(hamiltonianRemLp Ψ Λ)) j ≤ 2 * Ψ.normAt j :=
  (oscAt_hamiltonianRemLp_le Λ j).trans
    (mul_le_mul' le_rfl (tailWeight_singleton_le_normAt (Φ := Ψ) Λ j))

omit [Countable S] in
/-- The oscillation of the boundary part at a fixed site vanishes as `Λ ↑ S`. -/
lemma tendsto_oscAt_hamiltonianRemLp (j : S) :
    Tendsto (fun Λ : Finset S ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.1 (tendsto_tailWeight_atTop (Φ := Ψ) {j})
    (ε / 2) (ENNReal.half_pos hε.ne')] with Λ hΛ
  calc oscAt (⇑(hamiltonianRemLp Ψ Λ)) j ≤ 2 * Ψ.tailWeight Λ {j} :=
        oscAt_hamiltonianRemLp_le Λ j
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)

end BoundaryTerm

/-! ### Georgii's `⟨·,·⟩` as Mathlib's covariance

Georgii writes `⟨f, g⟩_ρ = ρ(fg) − ρ(f)ρ(g)`; this is `ProbabilityTheory.covariance`, whose
bilinearity is what organises the decomposition of `⟨H^Ψ_Λ, g⟩` in the proof of Corollary (8.37).
-/

section Covariance

variable {S E : Type*} [MeasurableSpace E] {ρ : Measure (S → E)}
  {f g : lp (fun _ : S → E ↦ ℝ) ∞}

/-- A bounded quasilocal observable is square integrable against a finite measure. -/
lemma memLp_two_of_mem_quasilocalFunctions [IsFiniteMeasure ρ]
    (hf : f ∈ quasilocalFunctions S E) : MemLp (⇑f) 2 ρ :=
  MemLp.of_bound (measurable_of_mem_quasilocalFunctions hf).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun σ ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f σ)

/-- Georgii's `⟨f, g⟩_ρ = ρ(fg) − ρ(f)ρ(g)` is the covariance of `f` and `g` under `ρ`. -/
lemma covariance_eq_integral_mul_sub [IsProbabilityMeasure ρ]
    (hf : f ∈ quasilocalFunctions S E) (hg : g ∈ quasilocalFunctions S E) :
    cov[(f : (S → E) → ℝ), (g : (S → E) → ℝ); ρ]
      = (∫ σ, (f : (S → E) → ℝ) σ * (g : (S → E) → ℝ) σ ∂ρ)
        - (∫ σ, (f : (S → E) → ℝ) σ ∂ρ) * ∫ σ, (g : (S → E) → ℝ) σ ∂ρ :=
  covariance_eq_sub (memLp_two_of_mem_quasilocalFunctions hf)
    (memLp_two_of_mem_quasilocalFunctions hg)

end Covariance

/-! ### Proposition (8.34) in covariance form -/

section Prop834Cov

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S] {γ : Specification S E}
  {μ : Measure (S → E)} {C : S → S → ℝ≥0∞}

/-- **Georgii, Proposition (8.34)**, in covariance form and against a majorant `C ≥ C(γ)`. -/
theorem ofReal_abs_covariance_le_matSeries' [IsProbabilityMeasure μ] (hγq : γ.IsQuasilocal)
    (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    (hC : ∀ i j, interdep γ i j ≤ C i j)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |cov[(f : (S → E) → ℝ), (g : (S → E) → ℝ); μ]|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 := by
  rw [covariance_eq_integral_mul_sub hf hg]
  exact ofReal_abs_covariance_le_matSeries hγq hd hμ hC hf hg

/-- **Georgii, Proposition (8.34) at finite volume**, in covariance form. -/
theorem ofReal_abs_covariance_apply_le_matSeries' (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ)
    (hC : ∀ i j, interdep γ i j ≤ C i j) (Λ : Finset S) (ω : S → E)
    {f g : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E)
    (hg : g ∈ quasilocalFunctions S E) :
    ENNReal.ofReal |cov[(f : (S → E) → ℝ), (g : (S → E) → ℝ); γ Λ ω]|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑g) j) i * oscAt (⇑f) i) / 4 := by
  rw [covariance_eq_integral_mul_sub hf hg]
  exact ofReal_abs_covariance_apply_le_matSeries hγq hd hC Λ ω hf hg

end Prop834Cov

/-! ### The three vanishing bounds of Georgii's proof of Corollary (8.37)

`T₁`, `T₂`, `T₃` are all controlled by `t`-independent quantities, because the covariance
estimate (8.34) is applied against a single majorant `C` of the interdependence matrices along
the segment `Φ + tΨ`, `|t| ≤ t₀`.
-/

section Vanishing

open Potential

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] {Ψ : Potential S E}
  [IsPotential Ψ] [IsAbsolutelySummable Ψ] {C : S → S → ℝ≥0∞} {b c : ℝ≥0∞}
  {g : lp (fun _ : S → E ↦ ℝ) ∞}

omit [Countable S] in
/-- **Georgii's `T₁ → 0`.** The covariance bound (8.34) for the boundary part
`H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}` against `g` vanishes as `Λ ↑ S`. -/
theorem tendsto_bound_hamiltonianRemLp (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c)
    (hb : ∀ j, Ψ.normAt j ≤ b) (hbtop : b ≠ ⊤) (hgsum : ∑' i, oscAt (⇑g) i ≠ ⊤) :
    Tendsto (fun Λ : Finset S ↦
        ∑' i, matSeries C (fun j ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) i * oscAt (⇑g) i)
      atTop (𝓝 0) :=
  tendsto_tsum_matSeries_mul hc1 hc (M := 2 * b) (ENNReal.mul_ne_top (by norm_num) hbtop)
    (fun Λ j ↦ (oscAt_hamiltonianRemLp_le_normAt Λ j).trans (mul_le_mul' le_rfl (hb j)))
    (fun j ↦ tendsto_oscAt_hamiltonianRemLp j) hgsum

omit [Countable S] in
lemma tsum_oscAt_siteEnergy_ne_top (hb : ∀ j, Ψ.normAt j ≤ b) (hbtop : b ≠ ⊤) (j : S) :
    ∑' k : S, oscAt (Ψ.siteEnergy k) j ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hbtop)
    ((tsum_oscAt_siteEnergy_le' (Φ := Ψ) j).trans (mul_le_mul' le_rfl (hb j)))

omit [Countable S] in
/-- The tail `∑_{k ∉ Δ} δ_j(f_Ψ ∘ θ_{−k})` vanishes as `Δ ↑ S`. -/
lemma tendsto_tsum_ite_oscAt_siteEnergy (hb : ∀ j, Ψ.normAt j ≤ b) (hbtop : b ≠ ⊤) (j : S) :
    Tendsto (fun Δ : Finset S ↦
        ∑' k : S, (if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j)) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_tsum_compl_atTop_zero
    (f := fun k : S ↦ oscAt (Ψ.siteEnergy k) j) (tsum_oscAt_siteEnergy_ne_top hb hbtop j)
  exact h.congr fun Δ ↦ (tsum_ite_compl_eq _ Δ).symm

/-- **Georgii's `T₃ → 0`.** The covariance bound (8.34) summed over the sites outside a finite
volume `Δ` vanishes as `Δ ↑ S`; this is Georgii's `∑_k δ_k(f_Ψ) ≤ 2‖Ψ‖₀ < ∞`. -/
theorem tendsto_bound_tsum_compl_siteEnergy (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c)
    (hb : ∀ j, Ψ.normAt j ≤ b) (hbtop : b ≠ ⊤) (hgsum : ∑' i, oscAt (⇑g) i ≠ ⊤) :
    Tendsto (fun Δ : Finset S ↦
        ∑' i, matSeries C
            (fun j ↦ ∑' k : S, (if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j)) i
          * oscAt (⇑g) i) atTop (𝓝 0) :=
  tendsto_tsum_matSeries_mul hc1 hc (M := 2 * b) (ENNReal.mul_ne_top (by norm_num) hbtop)
    (fun Δ j ↦ le_trans (ENNReal.tsum_le_tsum fun k ↦ by split <;> simp)
      ((tsum_oscAt_siteEnergy_le' (Φ := Ψ) j).trans (mul_le_mul' le_rfl (hb j))))
    (fun j ↦ tendsto_tsum_ite_oscAt_siteEnergy hb hbtop j) hgsum

end Vanishing


/-! ### Georgii Corollary (8.37): differentiating the Gibbs measure in the potential

Georgii fixes a potential `Φ` in the region `𝒟 = {‖Φ‖' < 1}` of (8.36), a direction `Ψ`, and an
observable `g` with `∑_i δ_i(g) < ∞`, and shows that `t ↦ μ_{Φ+tΨ}(g)` is differentiable near `0`
with

`∂/∂t μ_{Φ+tΨ}(g) = −∑_{k ∈ S} ⟨f_Ψ ∘ θ_{−k}, g⟩_{μ_{Φ+tΨ}}`,

the sum of the covariances of `g` with the energy densities (15.22) of `Ψ`.

The proof exchanges the two limits `Λ ↑ S` and `∂/∂t`. At finite volume the derivative *is* a
covariance, `∂/∂t γ^{Φ+tΨ}_Λ(g|ω) = −⟨H^Ψ_Λ, g⟩^t_Λ`
(`hasDerivAt_integral_gibbsSpecification`), and `γ^{Φ+tΨ}_Λ(g|ω) → μ_{Φ+tΨ}(g)` by (8.23)
(`isEstimate_finiteVolume`). The exchange is legitimate because the derivatives converge
*uniformly* in `t`: for a finite `Δ ⊆ Λ`,

`⟨H^Ψ_Λ, g⟩_{γ_Λ} − ∑_k ⟨f^k, g⟩_μ = ⟨H^Ψ_Λ − ∑_{k ∈ Λ} f^k, g⟩_{γ_Λ}`
`  + ∑_{k ∈ Δ} (⟨f^k, g⟩_{γ_Λ} − ⟨f^k, g⟩_μ) + ∑_{k ∈ Λ∖Δ} ⟨f^k, g⟩_{γ_Λ} − ∑_{k ∉ Δ} ⟨f^k, g⟩_μ`

(Georgii's `T₁`, `T₂` and twice `T₃`), and every term is estimated by Proposition (8.34) against
the *single* majorant `C` of the interdependence matrices of the whole segment
(`exists_forall_interdep_gibbsSpecification_add_smul_le`), hence uniformly in `t`.
-/

section Corollary837

open Potential Specification

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E] {Ψ : Potential S E}
  [IsPotential Ψ] [IsAbsolutelySummable Ψ] {C : S → S → ℝ≥0∞} {b c : ℝ≥0∞}
  {g : lp (fun _ : S → E ↦ ℝ) ∞} {ρ : Measure (S → E)}

omit [Countable S] [DecidableEq S] in
/-- **Georgii, in the proof of Corollary (8.37).** The covariance of an observable with the
Hamiltonian of a finite volume splits into the boundary part `H^Ψ_Λ − ∑_{k ∈ Λ} f_Ψ ∘ θ_{−k}` and
the energy densities inside the volume. -/
lemma covariance_hamiltonian_eq_add_sum_siteEnergy [IsProbabilityMeasure ρ]
    (hg : g ∈ quasilocalFunctions S E) (Λ : Finset S) :
    cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ; ρ]
      = cov[(g : (S → E) → ℝ), ⇑(hamiltonianRemLp Ψ Λ); ρ]
        + ∑ k ∈ Λ, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ] := by
  have hgL : MemLp (⇑g) 2 ρ := memLp_two_of_mem_quasilocalFunctions hg
  have hrem : MemLp (⇑(hamiltonianRemLp Ψ Λ)) 2 ρ :=
    memLp_two_of_mem_quasilocalFunctions (hamiltonianRemLp_mem_quasilocalFunctions Λ)
  have hk : ∀ k ∈ Λ, MemLp (Ψ.siteEnergy k) 2 ρ := fun k _ ↦
    memLp_two_of_mem_quasilocalFunctions (siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k)
  have hsplit : Ψ.hamiltonian Λ = ⇑(hamiltonianRemLp Ψ Λ) + ∑ k ∈ Λ, Ψ.siteEnergy k := by
    rw [coeFn_hamiltonianRemLp]
    funext η
    simp
  rw [hsplit, covariance_add_right hgL hrem (memLp_finsetSum' Λ hk),
    covariance_sum_right' hk hgL]

omit [Countable S] in
/-- **Georgii's `T₃` estimate.** The covariances of `g` with the energy densities of the sites
outside a finite set `Δ`, summed, are bounded by Proposition (8.34) applied to the vector
`j ↦ ∑_{k ∉ Δ} δ_j(f_Ψ ∘ θ_{−k})`. -/
lemma tsum_ite_ofReal_abs_covariance_siteEnergy_le
    (hρ : ∀ f : lp (fun _ : S → E ↦ ℝ) ∞, f ∈ quasilocalFunctions S E →
      ENNReal.ofReal |cov[(g : (S → E) → ℝ), (f : (S → E) → ℝ); ρ]|
        ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑f) j) i * oscAt (⇑g) i) / 4)
    (Δ : Finset S) :
    ∑' k : S, (if k ∈ Δ then 0
        else ENNReal.ofReal |cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ]|)
      ≤ (∑' i, matSeries C
          (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
          * oscAt (⇑g) i) / 4 := by
  have hstep : ∀ k : S,
      (if k ∈ Δ then 0 else ENNReal.ofReal |cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ]|)
        ≤ (∑' i, matSeries C
            (fun j ↦ if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4 := by
    intro k
    by_cases hk : k ∈ Δ
    · simp [hk]
    · simpa only [ite_eq_right hk, coeFn_siteEnergyLp] using
        hρ (Ψ.siteEnergyLp k) (siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k)
  calc ∑' k : S, (if k ∈ Δ then 0
        else ENNReal.ofReal |cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ]|)
      ≤ ∑' k : S, (∑' i, matSeries C
          (fun j ↦ if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4 :=
        ENNReal.tsum_le_tsum hstep
    _ = (∑' k : S, ∑' i, matSeries C
          (fun j ↦ if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4 := by
        simp_rw [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
    _ = _ := by rw [ENNReal.tsum_tsum_matSeries_mul]

omit [Countable S] [DecidableEq S] in
/-- **Georgii, in the proof of Corollary (8.37).** The covariance series
`∑_k ⟨f_Ψ ∘ θ_{−k}, g⟩` converges absolutely: Proposition (8.34) bounds its terms by a
convergent series, because `∑_k δ_j(f_Ψ ∘ θ_{−k}) ≤ 2‖Ψ‖_j` and `∑_i δ_i(g) < ∞`. -/
lemma summable_norm_covariance_siteEnergy (hc1 : c < 1) (hc : ∀ i, ∑' j, C i j ≤ c)
    (hb : ∀ j, Ψ.normAt j ≤ b) (hbtop : b ≠ ⊤) (hgsum : ∑' i, oscAt (⇑g) i ≠ ⊤)
    (hρ : ∀ f : lp (fun _ : S → E ↦ ℝ) ∞, f ∈ quasilocalFunctions S E →
      ENNReal.ofReal |cov[(g : (S → E) → ℝ), (f : (S → E) → ℝ); ρ]|
        ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑f) j) i * oscAt (⇑g) i) / 4) :
    Summable fun k : S ↦ ‖cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ]‖ := by
  classical
  have hle : ∑' k : S, ENNReal.ofReal |cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; ρ]|
      ≤ (∑' i, matSeries C (fun j ↦ ∑' k : S, oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4 := by
    simpa using tsum_ite_ofReal_abs_covariance_siteEnergy_le (Ψ := Ψ) (C := C) hρ ∅
  have hfin : (∑' i, matSeries C (fun j ↦ ∑' k : S, oscAt (Ψ.siteEnergy k) j) i
      * oscAt (⇑g) i) / 4 ≠ ⊤ := by
    refine (ENNReal.div_ne_top ?_ (by norm_num))
    refine ENNReal.tsum_matSeries_mul_ne_top hc1 hc (M := 2 * b)
      (ENNReal.mul_ne_top (by norm_num) hbtop) (fun j ↦ ?_) hgsum
    exact (tsum_oscAt_siteEnergy_le' (Φ := Ψ) j).trans (mul_le_mul' le_rfl (hb j))
  have hsum := ENNReal.summable_toReal (ne_top_of_le_ne_top hfin hle)
  refine hsum.congr fun k ↦ ?_
  rw [ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]

omit [Countable S] in
/-- **Georgii's `T₁ + T₂ + 2T₃` estimate** in the proof of Corollary (8.37). For a finite
`Δ ⊆ Λ`, the difference between the finite-volume covariance `⟨H^Ψ_Λ, g⟩_{γ_Λ(·|ω)}` and the
infinite-volume series `∑_k ⟨f_Ψ ∘ θ_{−k}, g⟩_μ` is bounded by the sum of

* Georgii's `T₁`: Proposition (8.34) applied to the boundary part of the Hamiltonian;
* Georgii's `T₂`: the estimate (8.23) for the pair `γ_Λ(·|ω)`, `μ` on the sites of `Δ`;
* twice Georgii's `T₃`: Proposition (8.34) applied to the energy densities outside `Δ`, once
  under `γ_Λ(·|ω)` and once under `μ`.

All three bounds are expressed through the majorant `C ≥ C(γ)`, so they do not see `γ` itself. -/
lemma ofReal_abs_covariance_hamiltonian_sub_tsum_le {γ : Specification S E}
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hγq : γ.IsQuasilocal) (hd : IsDobrushin γ) (hμ : ∀ i : S, μ.bind (γ {i}) = μ)
    (hC : ∀ i j, interdep γ i j ≤ C i j) (hg : g ∈ quasilocalFunctions S E)
    (hsum : Summable fun k : S ↦ ‖cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ]‖)
    {Δ Λ : Finset S} (hΔΛ : Δ ⊆ Λ) (ω : S → E) :
    ENNReal.ofReal |cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ; γ Λ ω]
        - ∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ]|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) i * oscAt (⇑g) i) / 4
        + ∑ k ∈ Δ, (2 * ENNReal.ofReal ‖g‖ * ∑' j, matTail C Λ j * oscAt (Ψ.siteEnergy k) j
            + 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖ * ∑' j, matTail C Λ j * oscAt (⇑g) j)
        + 2 * ((∑' i, matSeries C
            (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
            * oscAt (⇑g) i) / 4) := by
  classical
  set F : S → ℝ := fun k ↦ cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ] with hFdef
  set G : S → ℝ := fun k ↦ cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; γ Λ ω] with hGdef
  have hFs : Summable F := hsum.of_norm
  have h1 : Summable fun k ↦ if k ∈ Δ then F k else 0 :=
    summable_of_ne_finset_zero (s := Δ) fun k hk ↦ by simp [hk]
  have h2 : Summable fun k ↦ if k ∈ Δ then 0 else F k := by
    refine (hFs.sub h1).congr fun k ↦ ?_
    by_cases hk : k ∈ Δ <;> simp [hk]
  have hYsplit : ∑' k, F k = (∑ k ∈ Δ, F k) + ∑' k, (if k ∈ Δ then 0 else F k) := by
    have hpt : ∀ k, (if k ∈ Δ then F k else 0) + (if k ∈ Δ then 0 else F k) = F k := fun k ↦ by
      by_cases hk : k ∈ Δ <;> simp [hk]
    rw [← tsum_congr hpt, h1.tsum_add h2, tsum_eq_sum (s := Δ) (fun k hk ↦ by simp [hk])]
    congr 1
    exact Finset.sum_congr rfl fun k hk ↦ by simp [hk]
  have hid : cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ; γ Λ ω] - ∑' k, F k
      = cov[(g : (S → E) → ℝ), ⇑(hamiltonianRemLp Ψ Λ); γ Λ ω]
        + (∑ k ∈ Δ, (G k - F k)) + (∑ k ∈ Λ \ Δ, G k)
        + -∑' k, (if k ∈ Δ then 0 else F k) := by
    rw [covariance_hamiltonian_eq_add_sum_siteEnergy hg Λ, hYsplit,
      ← Finset.sum_sdiff hΔΛ (f := G), Finset.sum_sub_distrib]
    ring
  -- `T₁`
  have hT₁ : ENNReal.ofReal |cov[(g : (S → E) → ℝ), ⇑(hamiltonianRemLp Ψ Λ); γ Λ ω]|
      ≤ (∑' i, matSeries C (fun j ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) i * oscAt (⇑g) i) / 4 :=
    ofReal_abs_covariance_apply_le_matSeries' hγq hd hC Λ ω hg
      (hamiltonianRemLp_mem_quasilocalFunctions Λ)
  -- `T₂`
  have hT₂ : ENNReal.ofReal |∑ k ∈ Δ, (G k - F k)|
      ≤ ∑ k ∈ Δ, (2 * ENNReal.ofReal ‖g‖ * ∑' j, matTail C Λ j * oscAt (Ψ.siteEnergy k) j
          + 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖ * ∑' j, matTail C Λ j * oscAt (⇑g) j) := by
    have hest := isEstimate_finiteVolume hγq hd hμ Λ ω
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _))
      (le_of_eq (ENNReal.ofReal_sum_of_nonneg fun k _ ↦ abs_nonneg _)))
      (Finset.sum_le_sum fun k _ ↦ ?_)
    have hk := hest.ofReal_abs_covariance_sub_le hg
      (siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k)
    rw [← covariance_eq_integral_mul_sub hg (siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k),
      ← covariance_eq_integral_mul_sub hg (siteEnergyLp_mem_quasilocalFunctions (Φ := Ψ) k)]
      at hk
    refine hk.trans (add_le_add (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j ↦ ?_))
      (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j ↦ ?_))) <;>
      exact mul_le_mul' (interdepTail_le_matTail hC Λ j) le_rfl
  -- `T₃`, under the finite-volume Gibbs distribution
  have hT₃γ : ∑' k : S, (if k ∈ Δ then 0 else ENNReal.ofReal |G k|)
      ≤ (∑' i, matSeries C
          (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
          * oscAt (⇑g) i) / 4 :=
    tsum_ite_ofReal_abs_covariance_siteEnergy_le
      (fun f hf ↦ ofReal_abs_covariance_apply_le_matSeries' hγq hd hC Λ ω hg hf) Δ
  -- `T₃`, under the Gibbs measure
  have hT₃μ : ∑' k : S, (if k ∈ Δ then 0 else ENNReal.ofReal |F k|)
      ≤ (∑' i, matSeries C
          (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
          * oscAt (⇑g) i) / 4 :=
    tsum_ite_ofReal_abs_covariance_siteEnergy_le
      (fun f hf ↦ ofReal_abs_covariance_le_matSeries' hγq hd hμ hC hg hf) Δ
  have hT₃γ' : ENNReal.ofReal |∑ k ∈ Λ \ Δ, G k|
      ≤ (∑' i, matSeries C
          (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
          * oscAt (⇑g) i) / 4 := by
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _))
      (le_of_eq (ENNReal.ofReal_sum_of_nonneg fun k _ ↦ abs_nonneg _))) (le_trans ?_ hT₃γ)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk ↦ ?_))
      (ENNReal.sum_le_tsum (Λ \ Δ))
    rw [ite_eq_right (Finset.mem_sdiff.1 hk).2]
  have habs2 : Summable fun k : S ↦ |if k ∈ Δ then 0 else F k| := by
    refine Summable.of_nonneg_of_le (fun k ↦ abs_nonneg _) (fun k ↦ ?_) hsum
    by_cases hk : k ∈ Δ
    · simp [hk]
    · simp only [hFdef, ite_eq_right hk, Real.norm_eq_abs, le_refl]
  have hT₃μ' : ENNReal.ofReal |-∑' k, (if k ∈ Δ then 0 else F k)|
      ≤ (∑' i, matSeries C
          (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i
          * oscAt (⇑g) i) / 4 := by
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_)
      (le_of_eq (ENNReal.ofReal_tsum_of_nonneg (fun k ↦ abs_nonneg _) habs2)))
      (le_trans (ENNReal.tsum_le_tsum fun k ↦ ?_) hT₃μ)
    · rw [abs_neg]
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun k ↦ if k ∈ Δ then 0 else F k)
          (by simpa only [Real.norm_eq_abs] using habs2)
    · by_cases hk : k ∈ Δ <;> simp [hk]
  rw [hid]
  set A := cov[(g : (S → E) → ℝ), ⇑(hamiltonianRemLp Ψ Λ); γ Λ ω] with hAdef
  set B := ∑ k ∈ Δ, (G k - F k) with hBdef
  set D := ∑ k ∈ Λ \ Δ, G k with hDdef
  set K := -∑' k : S, (if k ∈ Δ then 0 else F k) with hKdef
  set T₁ := (∑' i, matSeries C (fun j ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) i * oscAt (⇑g) i) / 4
    with hT₁def
  set T₂ := ∑ k ∈ Δ, (2 * ENNReal.ofReal ‖g‖ * ∑' j, matTail C Λ j * oscAt (Ψ.siteEnergy k) j
      + 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖ * ∑' j, matTail C Λ j * oscAt (⇑g) j) with hT₂def
  set T₃ := (∑' i, matSeries C
      (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4
    with hT₃def
  have habs : |A + B + D + K| ≤ |A| + |B| + |D| + |K| :=
    calc |A + B + D + K| ≤ |A + B + D| + |K| := abs_add_le _ _
      _ ≤ |A + B| + |D| + |K| := by gcongr; exact abs_add_le _ _
      _ ≤ |A| + |B| + |D| + |K| := by gcongr; exact abs_add_le _ _
  calc ENNReal.ofReal |A + B + D + K|
      ≤ ENNReal.ofReal (|A| + |B| + |D| + |K|) := ENNReal.ofReal_le_ofReal habs
    _ = ENNReal.ofReal |A| + ENNReal.ofReal |B| + ENNReal.ofReal |D|
          + ENNReal.ofReal |K| := by
        rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (by positivity) (abs_nonneg _),
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ ≤ T₁ + T₂ + T₃ + T₃ := add_le_add (add_le_add (add_le_add hT₁ hT₂) hT₃γ') hT₃μ'
    _ = T₁ + T₂ + 2 * T₃ := by rw [add_assoc, ← two_mul]

variable {Φ : Potential S E}

omit [DecidableEq S] in
/-- **Georgii, Corollary (8.37).** Let `Φ`, `Ψ` be absolutely summable potentials whose norms
(8.36) satisfy `‖Φ‖' ≤ a`, `‖Ψ‖' ≤ b` at every site with `a + t₀ b < 1` for some `t₀ > 0`, let
`λ = ν` be a probability measure on the state space, and let `g` be a bounded quasilocal
observable with `∑_i δ_i(g) < ∞`. If `μ s` is a Gibbs measure for `Φ + sΨ` for every `|s| ≤ t₀`,
then `s ↦ μ_s(g)` is differentiable at every `|t| < t₀` and

`∂/∂t μ_{Φ+tΨ}(g) = −∑_{k ∈ S} ⟨f_Ψ ∘ θ_{−k}, g⟩_{μ_{Φ+tΨ}}`.

Under Dobrushin's condition — which `a + t₀ b < 1` guarantees along the whole segment — the
family `μ` is unique, so this really is the derivative of Georgii's `Φ ↦ μ_Φ(g)`; over a
standard Borel state space such a family also exists
(`existsUnique_mem_GP_of_isDobrushin_of_standardBorel`).

The proof follows Georgii: the derivative at finite volume is a covariance, the finite-volume
Gibbs distributions converge to `μ_s` by (8.23), and the convergence of the derivatives is
uniform in `s` by the `T₁ + T₂ + 2T₃` estimate
`ofReal_abs_covariance_hamiltonian_sub_tsum_le`, whose three parts vanish by
`tendsto_bound_hamiltonianRemLp`, `ENNReal.tendsto_tsum_matTail_mul` and
`tendsto_bound_tsum_compl_siteEnergy`. -/
theorem hasDerivAt_integral_gibbsMeasure_add_smul [IsPotential Φ] [IsAbsolutelySummable Φ]
    (ν : Measure E) [IsProbabilityMeasure ν] {a : ℝ≥0∞} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hΦ : ∀ i, cardNormAt Φ i ≤ a) (hΨ : ∀ i, cardNormAt Ψ i ≤ b)
    (hab : a + ENNReal.ofReal t₀ * b < 1)
    (hg : g ∈ quasilocalFunctions S E) (hgsum : ∑' i, oscAt (⇑g) i ≠ ⊤)
    {μ : ℝ → Measure (S → E)} (hprob : ∀ s, IsProbabilityMeasure (μ s))
    (hμ : ∀ s, |s| ≤ t₀ → ∀ i : S,
      (μ s).bind (gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 {i}) = μ s)
    {t : ℝ} (ht : |t| < t₀) :
    HasDerivAt (fun s : ℝ ↦ ∫ σ, (g : (S → E) → ℝ) σ ∂(μ s))
      (-∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ t]) t := by
  classical
  have := hprob t
  obtain ⟨ω⟩ : Nonempty (S → E) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have huniv : (Set.univ : Set (S → E)) = ∅ := Set.eq_empty_of_isEmpty _
    simpa [huniv] using measure_univ (μ := μ t)
  obtain ⟨C, hCrow, hCle⟩ :=
    exists_forall_interdep_gibbsSpecification_add_smul_le (Φ := Φ) (Ψ := Ψ) ν (t₀ := t₀) hΦ hΨ
  have hbtop : b ≠ ⊤ := by
    rintro rfl
    rw [ENNReal.mul_top (by simpa using ht₀)] at hab
    simp at hab
  have hb : ∀ j, Ψ.normAt j ≤ b := fun j ↦ (normAt_le_cardNormAt Ψ j).trans (hΨ j)
  have hcard : ∀ s : ℝ, |s| ≤ t₀ →
      ∀ i, cardNormAt (Φ + s • Ψ) i ≤ a + ENNReal.ofReal t₀ * b := by
    intro s hs i
    refine (cardNormAt_add_le Φ (s • Ψ) i).trans (add_le_add (hΦ i) ?_)
    rw [cardNormAt_smul]
    exact mul_le_mul' (by rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal hs) (hΨ i)
  have hdob : ∀ s : ℝ, |s| ≤ t₀ →
      IsDobrushin (gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1) := fun s hs ↦
    isDobrushin_gibbsSpecification_of_cardNormAt_le (Φ := Φ + s • Ψ) ν hab (hcard s hs)
  have hsum : ∀ s : ℝ, |s| ≤ t₀ →
      Summable fun k : S ↦ ‖cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ s]‖ := by
    intro s hs
    have := hprob s
    exact summable_norm_covariance_siteEnergy hab hCrow hb hbtop hgsum
      (fun f hf ↦ ofReal_abs_covariance_le_matSeries' (hdob s hs).isQuasilocal (hdob s hs)
        (hμ s hs) (hCle s hs) hg hf)
  -- the finite-volume derivative
  have hgm : Measurable (g : (S → E) → ℝ) := measurable_of_mem_quasilocalFunctions hg
  have hgb : ∀ σ, |(g : (S → E) → ℝ) σ| ≤ ‖g‖ := fun σ ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero g σ
  have hderiv : ∀ (Λ : Finset S) (s : ℝ), HasDerivAt
      (fun r : ℝ ↦ ∫ σ, (g : (S → E) → ℝ) σ
        ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + r • Ψ) ν 1 Λ ω))
      (-cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ;
        gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω]) s := by
    intro Λ s
    have hcov := covariance_eq_integral_mul_sub
      (ρ := gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω) hg
      (hamiltonianLp_mem_quasilocalFunctions (Φ := Ψ) Λ)
    rw [coeFn_hamiltonianLp] at hcov
    rw [hcov]
    exact hasDerivAt_integral_gibbsSpecification (Φ := Φ) (ν := ν) (Ψ := Ψ) hgm hgb Λ ω s
  -- convergence of the finite-volume Gibbs distributions
  have hconv : ∀ s : ℝ, |s| ≤ t₀ →
      Tendsto (fun Λ : Finset S ↦ ∫ σ, (g : (S → E) → ℝ) σ
        ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω))
        atTop (𝓝 (∫ σ, (g : (S → E) → ℝ) σ ∂(μ s))) := by
    intro s hs
    have := hprob s
    have hR : Tendsto (fun Λ : Finset S ↦ (∑' j, matTail C Λ j * oscAt (⇑g) j).toReal)
        atTop (𝓝 0) := by
      have h := ENNReal.tendsto_tsum_matTail_mul (C := C) hab hCrow hgsum
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal (by simp)).comp h
    have hbnd : ∀ Λ : Finset S,
        |(∫ σ, (g : (S → E) → ℝ) σ
            ∂(gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω))
          - ∫ σ, (g : (S → E) → ℝ) σ ∂(μ s)|
          ≤ (∑' j, matTail C Λ j * oscAt (⇑g) j).toReal := by
      intro Λ
      have hest := isEstimate_finiteVolume (hdob s hs).isQuasilocal (hdob s hs) (hμ s hs) Λ ω g hg
      rw [← ENNReal.ofReal_le_iff_le_toReal
        (ENNReal.tsum_matTail_mul_ne_top hab hCrow Λ hgsum)]
      exact hest.trans (ENNReal.tsum_le_tsum fun j ↦
        mul_le_mul' (interdepTail_le_matTail (hCle s hs) Λ j) le_rfl)
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun Λ ↦ by rw [Real.dist_eq]; exact hbnd Λ) hR
  -- the three vanishing bounds
  have hquarter : ∀ u : Finset S → ℝ≥0∞, Tendsto u atTop (𝓝 0) →
      Tendsto (fun x ↦ u x / 4) atTop (𝓝 0) := by
    intro u hu
    have h := ENNReal.Tendsto.mul_const (b := (4 : ℝ≥0∞)⁻¹) hu (Or.inr (by simp))
    simpa [div_eq_mul_inv] using h
  have hT₁t : Tendsto (fun Λ : Finset S ↦ (∑' i, matSeries C
      (fun j ↦ oscAt (⇑(hamiltonianRemLp Ψ Λ)) j) i * oscAt (⇑g) i) / 4) atTop (𝓝 0) :=
    hquarter _ (tendsto_bound_hamiltonianRemLp hab hCrow hb hbtop hgsum)
  have hT₃t : Tendsto (fun Δ : Finset S ↦ 2 * ((∑' i, matSeries C
      (fun j ↦ ∑' k : S, if k ∈ Δ then 0 else oscAt (Ψ.siteEnergy k) j) i * oscAt (⇑g) i) / 4))
      atTop (𝓝 0) := by
    have h := hquarter _ (tendsto_bound_tsum_compl_siteEnergy hab hCrow hb hbtop hgsum)
    simpa using ENNReal.Tendsto.const_mul (a := 2) h (Or.inr (by norm_num))
  have hT₂t : ∀ Δ : Finset S, Tendsto (fun Λ : Finset S ↦
      ∑ k ∈ Δ, (2 * ENNReal.ofReal ‖g‖ * ∑' j, matTail C Λ j * oscAt (Ψ.siteEnergy k) j
        + 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖ * ∑' j, matTail C Λ j * oscAt (⇑g) j))
      atTop (𝓝 0) := by
    intro Δ
    have hone : ∀ k ∈ Δ, Tendsto (fun Λ : Finset S ↦
        2 * ENNReal.ofReal ‖g‖ * ∑' j, matTail C Λ j * oscAt (Ψ.siteEnergy k) j
          + 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖ * ∑' j, matTail C Λ j * oscAt (⇑g) j)
        atTop (𝓝 0) := by
      intro k _
      have hk1 : ∑' j : S, oscAt (Ψ.siteEnergy k) j ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hbtop)
          ((tsum_oscAt_siteEnergy_le (Φ := Ψ) k).trans (mul_le_mul' le_rfl (hb k)))
      have h1 := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal ‖g‖)
        (ENNReal.tendsto_tsum_matTail_mul hab hCrow hk1)
        (Or.inr (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
      have h2 := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal ‖Ψ.siteEnergyLp k‖)
        (ENNReal.tendsto_tsum_matTail_mul hab hCrow hgsum)
        (Or.inr (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))
      simpa using h1.add h2
    simpa using tendsto_finsetSum (a := fun _ : S ↦ (0 : ℝ≥0∞)) Δ hone
  -- uniform convergence of the derivatives on `(-t₀, t₀)`
  have huc : TendstoUniformlyOn
      (fun (Λ : Finset S) (s : ℝ) ↦ -cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ;
          gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω])
      (fun s : ℝ ↦ -∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ s])
      atTop (Set.Ioo (-t₀) t₀) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨Δ, hΔ⟩ := ((ENNReal.tendsto_nhds_zero.1 hT₃t) _ hεpos).exists
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hT₁t) _ hεpos,
      (ENNReal.tendsto_nhds_zero.1 (hT₂t Δ)) _ hεpos,
      eventually_ge_atTop Δ] with Λ h1 h2 h3 s hs
    have hsabs : |s| ≤ t₀ := (abs_lt.2 ⟨hs.1, hs.2⟩).le
    have := hprob s
    have hbig := ofReal_abs_covariance_hamiltonian_sub_tsum_le
      (hdob s hsabs).isQuasilocal (hdob s hsabs) (hμ s hsabs) (hCle s hsabs) hg
      (hsum s hsabs) h3 ω
    have hle : ENNReal.ofReal
        |cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ;
            gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω]
          - ∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ s]|
        ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
      hbig.trans (add_le_add (add_le_add h1 h2) hΔ)
    rw [Real.dist_eq, show (-∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ s])
        - -cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ;
            gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω]
        = cov[(g : (S → E) → ℝ), Ψ.hamiltonian Λ;
            gibbsSpecificationOfAbsolutelySummable (Φ := Φ + s • Ψ) ν 1 Λ ω]
          - ∑' k : S, cov[(g : (S → E) → ℝ), Ψ.siteEnergy k; μ s] from by ring]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hle
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
    linarith
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo huc
    (Eventually.of_forall fun Λ s _ ↦ hderiv Λ s)
    (fun s hs ↦ hconv s (abs_lt.2 ⟨hs.1, hs.2⟩).le) (abs_lt.1 ht)

end Corollary837
end MeasureTheory.GibbsMeasure.Dobrushin

end

end

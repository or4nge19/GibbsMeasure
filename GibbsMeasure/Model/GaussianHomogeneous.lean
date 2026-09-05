/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianGibbs

/-!
# Georgii §13.3: the homogeneous case

Georgii's §13.3 specialises §13.2 to `S = ℤ^d` and to *homogeneous* data: `J(i,j) = J'(j - i)` for
an even `J' : S → ℝ` and `h_j = h'` a constant. Nothing in the elementary part of the section uses
the lattice structure of `ℤ^d` beyond the group law, so everything here is stated for an arbitrary
countable abelian group `S` (`ℤ^d` is the instance Georgii cares about); the `[LinearOrder S]`
assumption is only the one already required to form `Potential.gaussianSpecification`, and is
unrelated to the group structure.

## Main definitions

* `Potential.homogeneousCoupling J'`: **Georgii's homogeneous `J`**, `J(i,j) = J'(j - i)`.

Georgii's Fourier transform (13.35), `Ĵ(z) = ∑_{i ∈ S} z^i J(i)`, is *not* defined here; only its
value at `z = 1`, `Ĵ(1) = ∑_{i ∈ S} J(i)`, occurs below, and it occurs as the plain `tsum`
`∑' k, J' k`.

## Main results

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

## What is *not* proved here, and why

Georgii's Theorem (13.36) (`𝒢(γ^{J,h}) ≠ ∅` iff `M_{J,h} ≠ ∅` and `∫_G Ĵ(z)⁻¹ dz < ∞`) and its
corollaries (13.40)–(13.42), together with Remark (13.39) and Examples (13.43)–(13.45), are not
proved. They rest on Fourier analysis on the dual group `G = K^d` of `S = ℤ^d`, which is not
developed in this tree: the Fourier transform (13.35) of an absolutely summable `J : ℤ^d → ℝ` as a
continuous function on `G`, Proposition (13.A8) (`J` is positive definite iff `Ĵ ≥ 0` and
`Ĵ ≢ 0`), and Proposition (13.A9) (Herglotz: a nonnegative definite even `C : ℤ^d → ℂ` is the
Fourier–Stieltjes transform of a finite measure on `G`). Mathlib has the one-dimensional Fourier
theory of `AddCircle T` but not the `d`-dimensional torus character theory these need. The
necessity half of (13.36) additionally needs Theorem (13.24), which is itself open (see
`GibbsMeasure/Model/GaussianGibbs.lean`).
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

end Potential

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.GaussianSpecification

/-!
# Georgii Definition (13.18): the Gaussian specification of an infinite-range coupling

Georgii's Definition (13.18) attaches a specification `γ^{J,h}` to *any* symmetric positive
definite `J : S × S → ℝ` and any `h ∈ Ω = ℝ^S`, with no finite-range assumption. The point of the
definition is that for an infinite-range `J` the Hamiltonian

`H_Λ^{J,h}(ζ_Λ ω_{S∖Λ}) = ∑_{i ∈ Λ} h_i ζ_i + ½ ∑_{i,j ∈ Λ} J(i,j) ζ_i ζ_j
  + ∑_{i ∈ Λ} ζ_i ∑_{j ∉ Λ} J(i,j) ω_j`

only exists for boundary conditions `ω` in the convergence set `Ω_J` of (13.9); Georgii says so
explicitly: "If `J` has infinite range then the Hamiltonians `H_Λ^{J,h}(ω)` do not exist for all
`ω ∈ Ω`. Thus `Φ^{J,h}` is not a potential in the strict sense of Definition (2.2)." Since `Ω_J`
is tail measurable, "the definitions of `γ^{J,h}` on `Ω_J` and `Ω ∖ Ω_J` do not affect each
other", and (13.18) glues the Gibbsian formula on `Ω_J` to the Dirac reference `δ_{0_Λ ω_{S∖Λ}}`
off it.

This file carries that out. The Gibbsian branch is taken in the *closed form* Georgii proves in
Proposition (13.13): `γ_Λ^{J,h}(·|ω)` is the Gaussian field with covariance `𝒥_Λ⁻¹` on `Λ` and
mean `m(Λ,ω) = -𝒥_Λ⁻¹ (h|_Λ + (∑_{j ∉ Λ} J(i,j) ω_j)_{i ∈ Λ})`, the boundary field now being an
honest `tsum`.

## Why this is a new file and not a generalisation of `Potential.gaussianSpecification`

`Potential.gaussianSpecification` (`GibbsMeasure/Model/GaussianField.lean`) is
`gibbsSpecificationOfSigmaFiniteAdmissible` applied to the *potential* `Potential.gaussianPotential
J h` (Georgii (13.11)). Its consistency comes from the general Gibbsian machinery, whose Hamiltonian
`∑_{A ∩ Λ ≠ ∅} Φ_A` is a `Finset.sum` over `interactingSupport Λ` and therefore *requires*
`IsFiniteRange`. Georgii's own text says that `Φ^{J,h}` is not a potential when `J` has infinite
range, so `gaussianSpecification`'s hypotheses cannot be weakened in place: the object simply is
not the Gibbs specification of a potential any more. What is done instead is what the task
requires of the alternative: the infinite-range object is defined here directly, and
`Potential.gaussianInfiniteRangeSpecification_eq_gaussianSpecification` proves it *equal* to
`Potential.gaussianSpecification` whenever `J` does have finite row support. There is one object
with two presentations, and every existing downstream use of `gaussianSpecification` is untouched.

## Main definitions

* `Potential.gaussianTsumBoundaryField J Λ ω i`: Georgii's boundary field
  `∑_{j ∉ Λ} J(i,j) ω_j` as a `tsum`. It converges exactly on `Ω_J`
  (`Potential.summable_ite_notMem_of_mem_gaussianConvergenceSet`), and for finite range it is the
  finite sum `Potential.gaussianBoundaryField`
  (`Potential.gaussianTsumBoundaryField_eq_gaussianBoundaryField`).
* `Potential.gaussianTsumMean J h Λ ω`: Georgii's mean `m(Λ,ω) = -𝒥_Λ⁻¹(h|_Λ + boundary field)`
  of (13.13), for infinite range.
* `Potential.gaussianInfiniteRangeMeasure J h hPD β Λ ω`: the measure of Definition (13.18):
  the `juxt`-pushforward of the Gaussian with precision `β 𝒥_Λ` and mean `m(Λ,ω)` if `ω ∈ Ω_J`,
  and `δ_{0_Λ ω_{S∖Λ}}` otherwise.
* `Potential.gaussianInfiniteRangeSpecification J h hSymm hPD β hβ`: **Georgii Definition
  (13.18)**, the resulting `Specification S ℝ`.

## Main results

* `Potential.isConsistent_gaussianInfiniteRangeFun`: **`γ^{J,h}` is a specification**. Georgii
  disposes of this in one sentence ("the same arguments as in Proposition (2.5) and Remark (1.32)
  show that `γ^{J,h}` is indeed a specification"); the proof here is the honest one, and it is a
  *reduction to the finite-range case* rather than a second run of the Gibbsian machinery. Fix
  `Λ ⊆ Δ`. Off `Ω_J` both kernels are the Dirac reference, and `Ω_J` is invariant under changing
  the configuration on a finite set (`Potential.gaussianConvergenceSet_congr`), so the two branches
  never mix. On `Ω_J`, truncate `J` to `Δ` (`Potential.truncateCoupling J Δ`, equal to `J` on
  `Δ × Δ`, to the identity elsewhere, so of finite row support and still with all `𝒥_Γ` positive
  definite, `Potential.posDef_gaussianCouplingMatrix_truncateCoupling`) and shift the external
  field to `Potential.truncateField J h Δ ω = (h_i + ∑_{j ∉ Δ} J(i,j)ω_j)_{i}` on `Δ`. The
  identity `Potential.gaussianTsumBoundaryField_eq_add_sum_sdiff` — the boundary field of `Λ`
  splits into the boundary field of `Δ` plus the finite sum over `Δ ∖ Λ` — says exactly that the
  truncated *finite-range* data reproduce both kernels on the relevant set of configurations
  (`Potential.gaussianInfiniteRangeMeasure_eq_gaussianSpecification_truncate`), and the
  consistency of `Potential.gaussianSpecification` for the truncated data concludes.
* `Potential.gaussianInfiniteRangeSpecification_eq_gaussianSpecification`: for `J` of finite row
  support the two presentations agree.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false


open Finset Function MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal NNReal

noncomputable section

namespace Potential

/-! ## Georgii's boundary field `∑_{j ∉ Λ} J(i,j) ω_j` as a convergent series -/

section BoundaryField

variable {S : Type*} [LinearOrder S] (J : S → S → ℝ)

/-- **Georgii's boundary field for a general `J`** (the inner sum of `a_i(Λ,ω)` in the proof of
Proposition (13.13)): `∑_{j ∉ Λ} J(i,j) ω_j`, as a genuine `tsum`. It converges absolutely exactly
when `ω ∈ Ω_J` (13.9). -/
def gaussianTsumBoundaryField (J : S → S → ℝ) (Λ : Finset S) (ω : S → ℝ) (i : S) : ℝ :=
  ∑' j, if j ∈ Λ then 0 else J i j * ω j

/-- On `Ω_J` the boundary field is an absolutely convergent series: it differs from
`j ↦ J(i,j) ω_j` only on the finite set `Λ`. -/
theorem summable_ite_notMem_of_mem_gaussianConvergenceSet (J : S → S → ℝ) {ω : S → ℝ}
    (hω : ω ∈ gaussianConvergenceSet J) (Λ : Finset S) (i : S) :
    Summable fun j ↦ if j ∈ Λ then (0 : ℝ) else J i j * ω j := by
  refine (summable_congr_cofinite (f := fun j ↦ if j ∈ Λ then (0 : ℝ) else J i j * ω j)
    (g := fun j ↦ J i j * ω j) ?_).2 (summable_gaussianConvergenceSet J hω i)
  have hsub : {j : S | ¬ (if j ∈ Λ then (0 : ℝ) else J i j * ω j) = J i j * ω j} ⊆ (Λ : Set S) := by
    intro j hj
    by_contra hjΛ
    have hjΛ' : j ∉ Λ := by simpa using hjΛ
    exact hj (by simp [hjΛ'])
  exact Filter.eventuallyEq_of_mem ((Λ.finite_toSet.subset hsub).compl_mem_cofinite)
    fun j hj ↦ not_not.mp hj

/-- **For `J` of finite row support the series is Georgii's finite sum**: the boundary field of
`GibbsMeasure/Model/GaussianField.lean`. -/
theorem gaussianTsumBoundaryField_eq_gaussianBoundaryField (J : S → S → ℝ)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ) (i : S) :
    gaussianTsumBoundaryField J Λ ω i = gaussianBoundaryField J hFin Λ ω i := by
  classical
  have hzero : ∀ j ∉ (hFin i).toFinset \ Λ, (if j ∈ Λ then (0 : ℝ) else J i j * ω j) = 0 := by
    intro j hj
    rw [Finset.mem_sdiff, not_and_or, not_not] at hj
    rcases hj with hj | hj
    · have hJ : J i j = 0 := by
        by_contra hne
        exact hj ((hFin i).mem_toFinset.2 hne)
      simp [hJ]
    · simp [hj]
  rw [gaussianTsumBoundaryField, tsum_eq_sum (s := (hFin i).toFinset \ Λ) hzero,
    gaussianBoundaryField]
  exact Finset.sum_congr rfl fun j hj ↦ by simp [(Finset.mem_sdiff.1 hj).2]

/-- The boundary field sees the configuration only off `Λ`. -/
theorem dependsOn_gaussianTsumBoundaryField (J : S → S → ℝ) (Λ : Finset S) (i : S) :
    DependsOn (fun ω : S → ℝ ↦ gaussianTsumBoundaryField J Λ ω i) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  refine tsum_congr fun j ↦ ?_
  by_cases hj : j ∈ Λ
  · simp [hj]
  · simp only [hj, if_false, hωω' j (by simpa using hj)]

/-- **The boundary field of `Λ` splits at an intermediate volume `Δ ⊇ Λ`**: on `Ω_J`,
`∑_{j ∉ Λ} J(i,j) ω_j = ∑_{j ∉ Δ} J(i,j) ω_j + ∑_{j ∈ Δ ∖ Λ} J(i,j) ω_j`. This is the only place
where the convergence of the series is used in the proof that (13.18) is a specification, and it
is what makes the truncated finite-range data reproduce the infinite-range kernels. -/
theorem gaussianTsumBoundaryField_eq_add_sum_sdiff (J : S → S → ℝ) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) {ω : S → ℝ} (hω : ω ∈ gaussianConvergenceSet J) (i : S) :
    gaussianTsumBoundaryField J Λ ω i =
      gaussianTsumBoundaryField J Δ ω i + ∑ j ∈ Δ \ Λ, J i j * ω j := by
  classical
  have hsplit : ∀ j : S, (if j ∈ Λ then (0 : ℝ) else J i j * ω j) =
      (if j ∈ Δ then (0 : ℝ) else J i j * ω j) + (if j ∈ Δ \ Λ then J i j * ω j else 0) := by
    intro j
    by_cases hjΛ : j ∈ Λ
    · simp [hjΛ, hΛΔ hjΛ, Finset.mem_sdiff]
    · by_cases hjΔ : j ∈ Δ
      · simp [hjΛ, hjΔ, Finset.mem_sdiff]
      · simp [hjΛ, hjΔ, Finset.mem_sdiff]
  have hlast : ∑' j : S, (if j ∈ Δ \ Λ then J i j * ω j else 0) = ∑ j ∈ Δ \ Λ, J i j * ω j := by
    refine (tsum_eq_sum (s := Δ \ Λ) fun j hj ↦ by simp [hj]).trans
      (Finset.sum_congr rfl fun j hj ↦ by simp [hj])
  have hsummable : Summable fun j : S ↦ if j ∈ Δ \ Λ then J i j * ω j else 0 :=
    summable_of_ne_finset_zero (s := Δ \ Λ) fun j hj ↦ by simp [hj]
  rw [gaussianTsumBoundaryField, gaussianTsumBoundaryField, funext hsplit,
    Summable.tsum_add (summable_ite_notMem_of_mem_gaussianConvergenceSet J hω Δ i) hsummable,
    hlast]

end BoundaryField

/-! ## Truncating the coupling to a finite volume

The proof that (13.18) is a specification reduces the infinite-range kernels, on the set of
configurations that matters, to the finite-range ones of `Potential.gaussianSpecification`. The
finite-range datum is `J` truncated to `Δ × Δ` — the identity off it, so that the truncation is
still symmetric, of finite row support, and positive definite at every finite volume. -/

section Truncate

variable {S : Type*} [LinearOrder S]

/-- Splitting a sum over `Γ` at a second finite set `Δ`. -/
private lemma sum_inter_add_sum_sdiff {M : Type*} [AddCommMonoid M] (Γ Δ : Finset S) (f : S → M) :
    ∑ i ∈ Γ ∩ Δ, f i + ∑ i ∈ Γ \ Δ, f i = ∑ i ∈ Γ, f i := by
  classical
  rw [← Finset.filter_mem_eq_inter, Finset.sdiff_eq_filter]
  exact Finset.sum_filter_add_sum_filter_not Γ (· ∈ Δ) f

/-- The quadratic form of `𝒥_Γ` at the restriction to `Γ` of a configuration `X : S → ℝ`, as a
double sum over `Γ`. Intended home: `GibbsMeasure/Model/GaussianField.lean`, next to the private
`dotProduct_mulVec_gaussianCouplingMatrix_eq_sum`, of which this is the `juxt`-free form. -/
theorem dotProduct_mulVec_gaussianCouplingMatrix_eq_sum_restrict (J : S → S → ℝ) (Γ : Finset S)
    (X : S → ℝ) :
    (fun i : Γ ↦ X i.1) ⬝ᵥ (gaussianCouplingMatrix J Γ) *ᵥ (fun i : Γ ↦ X i.1) =
      ∑ i ∈ Γ, ∑ j ∈ Γ, X i * J i j * X j := by
  simp only [dotProduct, Matrix.mulVec, gaussianCouplingMatrix_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort Γ]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_coe_sort Γ]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The truncation of `J` at a finite volume `Δ`**: `J` on `Δ × Δ`, the identity matrix off it.

It is symmetric when `J` is (`Potential.symm_truncateCoupling`), always of finite row support
(`Potential.finite_setOf_truncateCoupling_ne_zero`), and every `𝒥_Γ` stays positive definite
(`Potential.posDef_gaussianCouplingMatrix_truncateCoupling`) — so `Potential.gaussianSpecification`
is available for it. -/
def truncateCoupling (J : S → S → ℝ) (Δ : Finset S) : S → S → ℝ :=
  fun i j ↦ if i ∈ Δ ∧ j ∈ Δ then J i j else if i = j then 1 else 0

@[simp] lemma truncateCoupling_apply_of_mem (J : S → S → ℝ) {Δ : Finset S} {i j : S}
    (hi : i ∈ Δ) (hj : j ∈ Δ) : truncateCoupling J Δ i j = J i j := by
  simp [truncateCoupling, hi, hj]

lemma truncateCoupling_apply_of_notMem_left (J : S → S → ℝ) {Δ : Finset S} {i : S} (hi : i ∉ Δ)
    (j : S) : truncateCoupling J Δ i j = if i = j then 1 else 0 := by
  simp [truncateCoupling, hi]

lemma truncateCoupling_apply_of_notMem_right (J : S → S → ℝ) {Δ : Finset S} {i j : S}
    (hi : i ∈ Δ) (hj : j ∉ Δ) : truncateCoupling J Δ i j = 0 := by
  have hij : i ≠ j := fun hc ↦ hj (hc ▸ hi)
  simp [truncateCoupling, hj, hij]

theorem symm_truncateCoupling {J : S → S → ℝ} (hSymm : ∀ i j, J i j = J j i) (Δ : Finset S)
    (i j : S) : truncateCoupling J Δ i j = truncateCoupling J Δ j i := by
  by_cases hi : i ∈ Δ <;> by_cases hj : j ∈ Δ
  · rw [truncateCoupling_apply_of_mem J hi hj, truncateCoupling_apply_of_mem J hj hi, hSymm]
  · rw [truncateCoupling_apply_of_notMem_right J hi hj,
      truncateCoupling_apply_of_notMem_left J hj i, if_neg (fun hc : j = i ↦ hj (hc ▸ hi))]
  · rw [truncateCoupling_apply_of_notMem_right J hj hi,
      truncateCoupling_apply_of_notMem_left J hi j, if_neg (fun hc : i = j ↦ hi (hc ▸ hj))]
  · rw [truncateCoupling_apply_of_notMem_left J hi j, truncateCoupling_apply_of_notMem_left J hj i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

theorem finite_setOf_truncateCoupling_ne_zero (J : S → S → ℝ) (Δ : Finset S) (i : S) :
    {j : S | truncateCoupling J Δ i j ≠ 0}.Finite := by
  refine (Δ.finite_toSet.insert i).subset fun j hj ↦ ?_
  by_cases hjΔ : j ∈ Δ
  · exact Set.mem_insert_of_mem _ hjΔ
  · by_cases hiΔ : i ∈ Δ
    · exact absurd (truncateCoupling_apply_of_notMem_right J hiΔ hjΔ) hj
    · rw [Set.mem_setOf_eq, truncateCoupling_apply_of_notMem_left J hiΔ j] at hj
      by_cases hij : i = j
      · exact hij ▸ Set.mem_insert _ _
      · exact absurd (by simp [hij]) hj

/-- **Every finite-volume coupling matrix of the truncation is positive definite.** In the basis
`Γ = (Γ ∩ Δ) ⊍ (Γ ∖ Δ)` the matrix `𝒥_Γ` of `truncateCoupling J Δ` is block diagonal, with blocks
`𝒥_{Γ ∩ Δ}` (positive definite by hypothesis) and the identity; concretely, its quadratic form is
`∑_{i,j ∈ Γ ∩ Δ} x_i J(i,j) x_j + ∑_{i ∈ Γ ∖ Δ} x_i²`, and a non-zero `x` makes one of the two
summands positive and the other nonnegative. -/
theorem posDef_gaussianCouplingMatrix_truncateCoupling {J : S → S → ℝ}
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) (Δ Γ : Finset S) :
    (gaussianCouplingMatrix (truncateCoupling J Δ) Γ).PosDef := by
  classical
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx ↦ ?_⟩
  · refine Matrix.IsHermitian.ext fun i j ↦ ?_
    simpa [gaussianCouplingMatrix_apply] using symm_truncateCoupling hSymm Δ j.1 i.1
  set X : S → ℝ := fun s ↦ if hs : s ∈ Γ then x ⟨s, hs⟩ else 0 with hXdef
  have hxX : x = fun i : Γ ↦ X i.1 := by
    funext i
    simp [hXdef, i.2]
  have hinner : ∀ i ∈ Γ ∩ Δ, ∑ j ∈ Γ, X i * truncateCoupling J Δ i j * X j =
      ∑ j ∈ Γ ∩ Δ, X i * J i j * X j := by
    intro i hi
    have hiΔ : i ∈ Δ := (Finset.mem_inter.1 hi).2
    rw [← sum_inter_add_sum_sdiff Γ Δ (fun j ↦ X i * truncateCoupling J Δ i j * X j)]
    have h2 : ∑ j ∈ Γ \ Δ, X i * truncateCoupling J Δ i j * X j = 0 :=
      Finset.sum_eq_zero fun j hj ↦ by
        rw [truncateCoupling_apply_of_notMem_right J hiΔ (Finset.mem_sdiff.1 hj).2]; ring
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [truncateCoupling_apply_of_mem J hiΔ (Finset.mem_inter.1 hj).2]
  have houter : ∀ i ∈ Γ \ Δ, ∑ j ∈ Γ, X i * truncateCoupling J Δ i j * X j = X i ^ 2 := by
    intro i hi
    have hiΓ : i ∈ Γ := (Finset.mem_sdiff.1 hi).1
    have hiΔ : i ∉ Δ := (Finset.mem_sdiff.1 hi).2
    rw [Finset.sum_eq_single i (fun j hj hji ↦ by
        rw [truncateCoupling_apply_of_notMem_left J hiΔ j]
        simp [Ne.symm hji]) (fun hc ↦ absurd hiΓ hc)]
    rw [truncateCoupling_apply_of_notMem_left J hiΔ i]
    simp
    ring
  have hquad : star x ⬝ᵥ (gaussianCouplingMatrix (truncateCoupling J Δ) Γ) *ᵥ x =
      (fun i : (Γ ∩ Δ : Finset S) ↦ X i.1) ⬝ᵥ (gaussianCouplingMatrix J (Γ ∩ Δ)) *ᵥ
          (fun i : (Γ ∩ Δ : Finset S) ↦ X i.1) + ∑ i ∈ Γ \ Δ, X i ^ 2 := by
    rw [star_trivial, hxX, dotProduct_mulVec_gaussianCouplingMatrix_eq_sum_restrict,
      dotProduct_mulVec_gaussianCouplingMatrix_eq_sum_restrict,
      ← sum_inter_add_sum_sdiff Γ Δ
        (fun i ↦ ∑ j ∈ Γ, X i * truncateCoupling J Δ i j * X j),
      Finset.sum_congr rfl hinner, Finset.sum_congr rfl houter]
  rw [hquad]
  by_cases hY : (fun i : (Γ ∩ Δ : Finset S) ↦ X i.1) = 0
  · have hfirst : (fun i : (Γ ∩ Δ : Finset S) ↦ X i.1) ⬝ᵥ
        (gaussianCouplingMatrix J (Γ ∩ Δ)) *ᵥ (fun i : (Γ ∩ Δ : Finset S) ↦ X i.1) = 0 := by
      rw [hY]; simp
    rw [hfirst, zero_add]
    obtain ⟨i, hi⟩ : ∃ i : Γ, x i ≠ 0 := by
      by_contra hc
      exact hx (funext fun i ↦ by simpa using not_not.1 (not_exists.1 hc i))
    have hiΔ : (i : S) ∉ Δ := by
      intro hiΔ
      have := congrFun hY ⟨i.1, Finset.mem_inter.2 ⟨i.2, hiΔ⟩⟩
      simp only [Pi.zero_apply] at this
      exact hi (by rw [hxX]; exact this)
    refine Finset.sum_pos' (fun j _ ↦ sq_nonneg _)
      ⟨i.1, Finset.mem_sdiff.2 ⟨i.2, hiΔ⟩, ?_⟩
    have : X i.1 ≠ 0 := fun hc ↦ hi (by rw [hxX]; exact hc)
    positivity
  · have hfirst := ((Matrix.posDef_iff_dotProduct_mulVec).1 (hPD (Γ ∩ Δ))).2 hY
    rw [star_trivial] at hfirst
    have hsecond : (0 : ℝ) ≤ ∑ i ∈ Γ \ Δ, X i ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    linarith

end Truncate

/-! ## Georgii's mean (13.13) for an infinite-range coupling

`m(Λ,ω) = -𝒥_Λ⁻¹ (h|_Λ + (∑_{j ∉ Λ} J(i,j) ω_j)_{i ∈ Λ})`, with the boundary field the convergent
series of `Potential.gaussianTsumBoundaryField`. A real `tsum` is not a measurable function of a
parameter in general — it is defined to be `0` off the summability set — so the measurability of
`ω ↦ m(Λ,ω)`, which the kernel of (13.18) needs, is obtained from the *measurable surrogate*
`Potential.gaussianBoundaryFieldAux`, which agrees with it on `Ω_J`. -/

section Mean

variable {S : Type*} [Countable S] [LinearOrder S]

/-- **Georgii's mean of (13.13) for a general `J`**: `m(Λ,ω) = -𝒥_Λ⁻¹ (h|_Λ + boundary field)`,
the boundary field being the convergent series `∑_{j ∉ Λ} J(i,j) ω_j`. -/
def gaussianTsumMean (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) (ω : S → ℝ) : Λ → ℝ :=
  -((gaussianCouplingMatrix J Λ)⁻¹ *ᵥ fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ω i.1)

/-- For `J` of finite row support, Georgii's mean is the finite-range
`Potential.gaussianMean`. -/
theorem gaussianTsumMean_eq_gaussianMean (J : S → S → ℝ) (h : S → ℝ)
    (hFin : ∀ i, {j : S | J i j ≠ 0}.Finite) (Λ : Finset S) (ω : S → ℝ) :
    gaussianTsumMean J h Λ ω = gaussianMean J h hFin Λ ω := by
  have harg : (fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ω i.1) =
      fun i : Λ ↦ h i.1 + gaussianBoundaryField J hFin Λ ω i.1 :=
    funext fun i ↦ by rw [gaussianTsumBoundaryField_eq_gaussianBoundaryField J hFin]
  rw [gaussianTsumMean, gaussianMean, harg]

/-- The measurable surrogate for the boundary field: the difference of the `toReal`s of the
`ℝ≥0∞`-series of the positive and negative parts of `j ↦ [j ∉ Λ] J(i,j) ω_j`. It is
`cylinderEvents Λᶜ`-measurable in `ω` unconditionally, and agrees with the boundary field on
`Ω_J` (`Potential.gaussianBoundaryFieldAux_eq`). -/
def gaussianBoundaryFieldAux (J : S → S → ℝ) (Λ : Finset S) (ω : S → ℝ) (i : S) : ℝ :=
  (∑' j, ENNReal.ofReal (if j ∈ Λ then 0 else J i j * ω j)).toReal -
    (∑' j, ENNReal.ofReal (-(if j ∈ Λ then (0 : ℝ) else J i j * ω j))).toReal

omit [Countable S] in
theorem gaussianBoundaryFieldAux_eq (J : S → S → ℝ) (Λ : Finset S) {ω : S → ℝ}
    (hω : ω ∈ gaussianConvergenceSet J) (i : S) :
    gaussianBoundaryFieldAux J Λ ω i = gaussianTsumBoundaryField J Λ ω i :=
  ((summable_ite_notMem_of_mem_gaussianConvergenceSet J hω Λ i).tsum_eq_toReal_tsum_ofReal_sub).symm

theorem measurable_gaussianBoundaryFieldAux (J : S → S → ℝ) (Λ : Finset S) (i : S) :
    Measurable fun ω : S → ℝ ↦ gaussianBoundaryFieldAux J Λ ω i := by
  have hterm : ∀ j : S, Measurable fun ω : S → ℝ ↦ (if j ∈ Λ then (0 : ℝ) else J i j * ω j) := by
    intro j
    by_cases hj : j ∈ Λ
    · have hc : (fun ω : S → ℝ ↦ (if j ∈ Λ then (0 : ℝ) else J i j * ω j)) = fun _ ↦ 0 :=
        funext fun ω ↦ by simp [hj]
      rw [hc]
      exact measurable_const
    · have hc : (fun ω : S → ℝ ↦ (if j ∈ Λ then (0 : ℝ) else J i j * ω j)) =
          fun ω ↦ J i j * ω j := funext fun ω ↦ by simp [hj]
      rw [hc]
      exact (measurable_pi_apply j).const_mul _
  exact (MeasureTheory.measurable_toReal_tsum_ofReal hterm).sub
    (MeasureTheory.measurable_toReal_tsum_ofReal fun j ↦ (hterm j).neg)

omit [Countable S] in
/-- The boundary field surrogate depends on the boundary condition only through its restriction to
`Λᶜ`: every term of the series with `j ∈ Λ` has been set to `0`. -/
theorem dependsOn_gaussianBoundaryFieldAux (J : S → S → ℝ) (Λ : Finset S) (i : S) :
    DependsOn (fun ω : S → ℝ ↦ gaussianBoundaryFieldAux J Λ ω i) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  have hterm : ∀ j : S, (if j ∈ Λ then (0 : ℝ) else J i j * ω j) =
      (if j ∈ Λ then (0 : ℝ) else J i j * ω' j) := by
    intro j
    by_cases hj : j ∈ Λ
    · simp [hj]
    · simp only [hj, if_false, hωω' j (by simpa using hj)]
  simp only [gaussianBoundaryFieldAux, hterm]

/-- The measurable surrogate for Georgii's mean: `-𝒥_Λ⁻¹ (h|_Λ + boundary-field surrogate)`. -/
def gaussianMeanAux (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) (ω : S → ℝ) : Λ → ℝ :=
  -((gaussianCouplingMatrix J Λ)⁻¹ *ᵥ fun i : Λ ↦ h i.1 + gaussianBoundaryFieldAux J Λ ω i.1)

omit [Countable S] in
theorem gaussianMeanAux_eq (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) {ω : S → ℝ}
    (hω : ω ∈ gaussianConvergenceSet J) :
    gaussianMeanAux J h Λ ω = gaussianTsumMean J h Λ ω := by
  have harg : (fun i : Λ ↦ h i.1 + gaussianBoundaryFieldAux J Λ ω i.1) =
      fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ω i.1 :=
    funext fun i ↦ by rw [gaussianBoundaryFieldAux_eq J Λ hω]
  rw [gaussianMeanAux, gaussianTsumMean, harg]

theorem measurable_gaussianMeanAux (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) (i : Λ) :
    Measurable fun ω : S → ℝ ↦ gaussianMeanAux J h Λ ω i := by
  have hrw : (fun ω : S → ℝ ↦ gaussianMeanAux J h Λ ω i) = fun ω ↦
      -∑ j : Λ, (gaussianCouplingMatrix J Λ)⁻¹ i j *
        (h j.1 + gaussianBoundaryFieldAux J Λ ω j.1) := rfl
  rw [hrw]
  exact (Finset.measurable_fun_sum Finset.univ fun j _ ↦
    ((measurable_gaussianBoundaryFieldAux J Λ j.1).const_add (h j.1)).const_mul
      ((gaussianCouplingMatrix J Λ)⁻¹ i j)).neg

omit [Countable S] in
theorem dependsOn_gaussianMeanAux (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) :
    DependsOn (fun ω : S → ℝ ↦ gaussianMeanAux J h Λ ω) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  have harg : (fun i : Λ ↦ h i.1 + gaussianBoundaryFieldAux J Λ ω i.1) =
      fun i : Λ ↦ h i.1 + gaussianBoundaryFieldAux J Λ ω' i.1 :=
    funext fun i ↦ congrArg (fun t ↦ h i.1 + t)
      (dependsOn_gaussianBoundaryFieldAux J Λ i.1 hωω')
  simp only [gaussianMeanAux, harg]

end Mean

/-! ## Georgii Definition (13.18): the specification `γ^{J,h}` -/

section Kernel

variable {S : Type*} [Countable S] [LinearOrder S]

open scoped Classical in
/-- **Georgii Definition (13.18)**, the finite-volume measure:
`γ_Λ^{J,h}(·|ω) = Z_Λ^{J,h}(ω)⁻¹ λ_Λ(1_A exp(-H_Λ^{J,h})|ω)` for `ω ∈ Ω_J`, and
`δ_{0_Λ ω_{S∖Λ}}(A)` otherwise.

The Gibbsian branch is taken in the closed form of Proposition (13.13) — for `ω ∈ Ω_J` the
Hamiltonian is `H_Λ(ζ_Λ ω_{Λᶜ}) = ½ ζᵀ 𝒥_Λ ζ + a(Λ,ω) ⬝ᵥ ζ` and completing the square identifies
the normalised Boltzmann factor with the Gaussian density of precision `β 𝒥_Λ` and mean
`m(Λ,ω) = -𝒥_Λ⁻¹ a(Λ,ω)` — which is what makes the definition available at all for an
infinite-range `J`, where the Hamiltonian itself is not a `Finset.sum`. For finite range the two
readings agree: `Potential.gaussianInfiniteRangeSpecification_eq_gaussianSpecification`. -/
def gaussianInfiniteRangeMeasure (J : S → S → ℝ) (h : S → ℝ) (β : ℝ) (Λ : Finset S)
    (ω : S → ℝ) : Measure (S → ℝ) :=
  if ω ∈ gaussianConvergenceSet J then
    (multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (gaussianTsumMean J h Λ ω)).map
      (juxt (Λ : Set S) ω)
  else Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → ℝ))

theorem gaussianInfiniteRangeMeasure_of_mem (J : S → S → ℝ) (h : S → ℝ) (β : ℝ) (Λ : Finset S)
    {ω : S → ℝ} (hω : ω ∈ gaussianConvergenceSet J) :
    gaussianInfiniteRangeMeasure J h β Λ ω =
      (multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (gaussianTsumMean J h Λ ω)).map
        (juxt (Λ : Set S) ω) := by
  rw [gaussianInfiniteRangeMeasure, if_pos hω]

theorem gaussianInfiniteRangeMeasure_of_notMem (J : S → S → ℝ) (h : S → ℝ) (β : ℝ) (Λ : Finset S)
    {ω : S → ℝ} (hω : ω ∉ gaussianConvergenceSet J) :
    gaussianInfiniteRangeMeasure J h β Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → ℝ)) := by
  rw [gaussianInfiniteRangeMeasure, if_neg hω]

theorem isProbabilityMeasure_gaussianInfiniteRangeMeasure (J : S → S → ℝ) (h : S → ℝ) {β : ℝ}
    (hPD : ∀ Λ : Finset S, (gaussianCouplingMatrix J Λ).PosDef) (hβ : 0 < β) (Λ : Finset S)
    (ω : S → ℝ) : IsProbabilityMeasure (gaussianInfiniteRangeMeasure J h β Λ ω) := by
  by_cases hω : ω ∈ gaussianConvergenceSet J
  · have : IsProbabilityMeasure
        (multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (gaussianTsumMean J h Λ ω)) :=
      isProbabilityMeasure_multivariateGaussianPi ((hPD Λ).smul hβ) _
    rw [gaussianInfiniteRangeMeasure_of_mem J h β Λ hω]
    exact Measure.isProbabilityMeasure_map
      (Measurable.juxt (Λ := (Λ : Set S)) (η := ω)).aemeasurable
  · rw [gaussianInfiniteRangeMeasure_of_notMem J h β Λ hω]
    infer_instance

omit [Countable S] in
theorem dependsOn_gaussianTsumMean (J : S → S → ℝ) (h : S → ℝ) (Λ : Finset S) :
    DependsOn (gaussianTsumMean J h Λ) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  have hterm : ∀ i : S, gaussianTsumBoundaryField J Λ ω i = gaussianTsumBoundaryField J Λ ω' i := by
    intro i
    refine tsum_congr fun j ↦ ?_
    by_cases hj : j ∈ Λ
    · simp [hj]
    · simp only [hj, if_false, hωω' j (by simpa using hj)]
  have harg : (fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ω i.1) =
      fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ω' i.1 :=
    funext fun i ↦ by rw [hterm i.1]
  simp only [gaussianTsumMean, harg]

/-- The boundary condition enters `γ_Λ^{J,h}(·|ω)` only through `ω|_{Λᶜ}`. -/
theorem dependsOn_gaussianInfiniteRangeMeasure (J : S → S → ℝ) (h : S → ℝ) (β : ℝ)
    (Λ : Finset S) : DependsOn (gaussianInfiniteRangeMeasure J h β Λ) ((Λ : Set S)ᶜ) := by
  intro ω ω' hωω'
  have hjuxt : ∀ ζ : Λ → ℝ, juxt (Λ : Set S) ω ζ = juxt (Λ : Set S) ω' ζ := by
    intro ζ
    funext x
    by_cases hx : x ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hx, juxt_apply_of_mem hx]
    · rw [juxt_apply_of_not_mem hx, juxt_apply_of_not_mem hx, hωω' x hx]
  have hΩ := gaussianConvergenceSet_congr J (Λ := Λ) hωω'
  by_cases hω : ω ∈ gaussianConvergenceSet J
  · rw [gaussianInfiniteRangeMeasure_of_mem J h β Λ hω,
      gaussianInfiniteRangeMeasure_of_mem J h β Λ (hΩ.1 hω),
      dependsOn_gaussianTsumMean J h Λ hωω', funext hjuxt]
  · rw [gaussianInfiniteRangeMeasure_of_notMem J h β Λ hω,
      gaussianInfiniteRangeMeasure_of_notMem J h β Λ (fun hc ↦ hω (hΩ.2 hc)), hjuxt]

omit [Countable S] in
/-- The `juxt`-pushforward of a multivariate Gaussian, evaluated at a measurable set, as a
`lintegral` against the *centred* Gaussian — a measure that does not depend on the boundary
condition. This is what makes `ω ↦ γ_Λ^{J,h}(A|ω)` measurable. -/
theorem map_juxt_multivariateGaussianPi_apply {Λ : Finset S}
    (P : Matrix Λ Λ ℝ) (m : Λ → ℝ) (ω : S → ℝ) {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    ((multivariateGaussianPi P m).map (juxt (Λ : Set S) ω)) A =
      ∫⁻ ζ, A.indicator 1 (juxt (Λ : Set S) ω (ζ + m)) ∂(multivariateGaussianPi P 0) := by
  have hadd : Measurable fun ζ : Λ → ℝ ↦ ζ + m := measurable_id.add_const m
  have hjx : Measurable (juxt (Λ : Set S) ω) := Measurable.juxt
  have hshift : multivariateGaussianPi P m = (multivariateGaussianPi P 0).map (· + m) := by
    rw [multivariateGaussianPi_map_add_right, zero_add]
  rw [hshift, Measure.map_map hjx hadd, Measure.map_apply (hjx.comp hadd) hA,
    ← lintegral_indicator_one ((hjx.comp hadd) hA)]
  exact lintegral_congr fun ζ ↦ by
    by_cases hζ : juxt (Λ : Set S) ω (ζ + m) ∈ A <;> simp [Set.indicator, hζ, Function.comp_def]

theorem measurable_gaussianInfiniteRangeMeasure (J : S → S → ℝ) (h : S → ℝ) {β : ℝ}
    (hPD : ∀ Λ : Finset S, (gaussianCouplingMatrix J Λ).PosDef) (hβ : 0 < β) (Λ : Finset S) :
    Measurable (gaussianInfiniteRangeMeasure J h β Λ) := by
  classical
  have : IsProbabilityMeasure
      (multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (0 : Λ → ℝ)) :=
    isProbabilityMeasure_multivariateGaussianPi ((hPD Λ).smul hβ) 0
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  have hjuxtm : Measurable fun p : (S → ℝ) × (Λ → ℝ) ↦
      juxt (Λ : Set S) p.1 (p.2 + gaussianMeanAux J h Λ p.1) := by
    refine Measurable.of_eval fun i ↦ ?_
    by_cases hi : i ∈ (Λ : Set S)
    · simp only [juxt_apply_of_mem hi, Pi.add_apply]
      exact ((measurable_pi_apply (⟨i, hi⟩ : Λ)).comp measurable_snd).add
        ((measurable_gaussianMeanAux J h Λ ⟨i, hi⟩).comp measurable_fst)
    · simp only [juxt_apply_of_not_mem hi]
      exact (measurable_pi_apply i).comp measurable_fst
  have hrw : (fun ω ↦ gaussianInfiniteRangeMeasure J h β Λ ω A) =
      Set.piecewise (gaussianConvergenceSet J)
        (fun ω ↦ ∫⁻ ζ, A.indicator 1 (juxt (Λ : Set S) ω (ζ + gaussianMeanAux J h Λ ω))
          ∂(multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (0 : Λ → ℝ)))
        (fun ω ↦ A.indicator 1 (juxt (Λ : Set S) ω (0 : Λ → ℝ))) := by
    funext ω
    by_cases hω : ω ∈ gaussianConvergenceSet J
    · rw [Set.piecewise_eq_of_mem _ _ _ hω, gaussianInfiniteRangeMeasure_of_mem J h β Λ hω,
        map_juxt_multivariateGaussianPi_apply _ _ ω hA, gaussianMeanAux_eq J h Λ hω]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω, gaussianInfiniteRangeMeasure_of_notMem J h β Λ hω,
        Measure.dirac_apply' _ hA]
  rw [hrw]
  refine Measurable.piecewise (measurableSet_gaussianConvergenceSet J) ?_ ?_
  · exact ((measurable_one.indicator hA).comp hjuxtm).lintegral_prod_right'
  · exact (measurable_one.indicator hA).comp (measurable_juxt_boundary (0 : Λ → ℝ))

end Kernel

/-! ## Reduction to the finite-range case

Fix `Λ ⊆ Δ` and a boundary condition `ω ∈ Ω_J`. On the configurations agreeing with `ω` off `Δ` —
the only ones `γ_Δ^{J,h}(·|ω)` charges — the infinite-range kernels at the volumes `Λ` and `Δ`
coincide with the *finite-range* kernels of `Potential.gaussianSpecification` for the truncated
coupling `truncateCoupling J Δ` and the shifted external field `truncateField J h Δ ω`. -/

section Reduction

variable {S : Type*} [Countable S] [LinearOrder S]

/-- The external field that carries the boundary interaction of `Δ`:
`h_i + ∑_{j ∉ Δ} J(i,j) ω_j`. -/
def truncateField (J : S → S → ℝ) (h : S → ℝ) (Δ : Finset S) (ω : S → ℝ) : S → ℝ :=
  fun i ↦ h i + gaussianTsumBoundaryField J Δ ω i

omit [Countable S] in
theorem gaussianCouplingMatrix_truncateCoupling_of_subset (J : S → S → ℝ) {Λ Δ : Finset S}
    (hΛΔ : Λ ⊆ Δ) : gaussianCouplingMatrix (truncateCoupling J Δ) Λ = gaussianCouplingMatrix J Λ :=
  Matrix.ext fun i j ↦ truncateCoupling_apply_of_mem J (hΛΔ i.2) (hΛΔ j.2)

omit [Countable S] in
/-- The boundary field of the truncated coupling at a volume `Λ ⊆ Δ` is the *finite* sum over
`Δ ∖ Λ`: the truncation kills every interaction leaving `Δ`. -/
theorem gaussianTsumBoundaryField_truncateCoupling (J : S → S → ℝ) {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ)
    (ζ : S → ℝ) {i : S} (hi : i ∈ Δ) :
    gaussianTsumBoundaryField (truncateCoupling J Δ) Λ ζ i = ∑ j ∈ Δ \ Λ, J i j * ζ j := by
  classical
  have hzero : ∀ j ∉ Δ \ Λ,
      (if j ∈ Λ then (0 : ℝ) else truncateCoupling J Δ i j * ζ j) = 0 := by
    intro j hj
    rw [Finset.mem_sdiff, not_and_or, not_not] at hj
    rcases hj with hj | hj
    · rw [truncateCoupling_apply_of_notMem_right J hi hj]
      simp
    · simp [hj]
  rw [gaussianTsumBoundaryField, tsum_eq_sum (s := Δ \ Λ) hzero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [truncateCoupling_apply_of_mem J hi (Finset.mem_sdiff.1 hj).1,
    if_neg (Finset.mem_sdiff.1 hj).2]

omit [Countable S] in
/-- The boundary field of `Δ` sees only the configuration off `Δ`. -/
theorem gaussianTsumBoundaryField_congr_of_eqOn_compl (J : S → S → ℝ) {Δ : Finset S}
    {ω ζ : S → ℝ} (hζω : ∀ i ∉ Δ, ζ i = ω i) (i : S) :
    gaussianTsumBoundaryField J Δ ζ i = gaussianTsumBoundaryField J Δ ω i :=
  dependsOn_gaussianTsumBoundaryField J Δ i fun j hj ↦ hζω j (by simpa using hj)

/-- **The infinite-range mean at a volume `Λ ⊆ Δ` is the truncated one.** This is Georgii's
boundary-field splitting `∑_{j ∉ Λ} = ∑_{j ∉ Δ} + ∑_{j ∈ Δ ∖ Λ}` in the form the consistency
proof needs. -/
theorem gaussianTsumMean_truncate (J : S → S → ℝ) (h : S → ℝ) {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ)
    {ω ζ : S → ℝ} (hζΩ : ζ ∈ gaussianConvergenceSet J) (hζω : ∀ i ∉ Δ, ζ i = ω i) :
    gaussianTsumMean (truncateCoupling J Δ) (truncateField J h Δ ω) Λ ζ =
      gaussianTsumMean J h Λ ζ := by
  have harg : (fun i : Λ ↦ truncateField J h Δ ω i.1 +
        gaussianTsumBoundaryField (truncateCoupling J Δ) Λ ζ i.1) =
      fun i : Λ ↦ h i.1 + gaussianTsumBoundaryField J Λ ζ i.1 := by
    funext i
    rw [truncateField, gaussianTsumBoundaryField_truncateCoupling J hΛΔ ζ (hΛΔ i.2),
      gaussianTsumBoundaryField_eq_add_sum_sdiff J hΛΔ hζΩ i.1,
      gaussianTsumBoundaryField_congr_of_eqOn_compl J hζω i.1]
    ring
  rw [gaussianTsumMean, gaussianTsumMean, harg,
    gaussianCouplingMatrix_truncateCoupling_of_subset J hΛΔ]

/-- **The infinite-range kernel at a volume `Λ ⊆ Δ`, at a boundary condition agreeing with `ω` off
`Δ`, is a finite-range kernel**: the one of `Potential.gaussianSpecification` for the truncated
coupling and the shifted external field. -/
theorem gaussianInfiniteRangeMeasure_eq_gaussianSpecification_truncate (J : S → S → ℝ) (h : S → ℝ)
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) {ω ζ : S → ℝ} (hζΩ : ζ ∈ gaussianConvergenceSet J)
    (hζω : ∀ i ∉ Δ, ζ i = ω i) :
    gaussianInfiniteRangeMeasure J h β Λ ζ =
      gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
        (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
        (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Λ ζ := by
  rw [gaussianInfiniteRangeMeasure_of_mem J h β Λ hζΩ, gaussianSpecification_apply,
    ← gaussianTsumMean_eq_gaussianMean, gaussianTsumMean_truncate J h hΛΔ hζΩ hζω,
    gaussianCouplingMatrix_truncateCoupling_of_subset J hΛΔ]

end Reduction

/-! ## Georgii Definition (13.18): `γ^{J,h}` is a specification -/

/-- Consistency of a specification, read at one boundary condition and one measurable set:
`∫ γ_Λ(A|ζ) γ_Δ(dζ|ω) = γ_Δ(A|ω)` for `Λ ⊆ Δ`. Intended home:
`GibbsMeasure/Specification.lean`, next to `Specification.IsConsistent`. -/
theorem _root_.Specification.lintegral_apply_of_subset {S E : Type*} [MeasurableSpace E]
    (γ : Specification S E) {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) (ω : S → E) {A : Set (S → E)}
    (hA : MeasurableSet A) : ∫⁻ ζ, γ Λ ζ A ∂(γ Δ ω) = γ Δ ω A := by
  have h1 := γ.isConsistent hΛΔ
  have h2 := congrArg (fun κ : Kernel[cylinderEvents ((Δ : Set S)ᶜ)] (S → E) (S → E) ↦ κ ω A) h1
  rwa [Kernel.comp_apply' _ _ _ hA] at h2

section IsSpecification

variable {S : Type*} [Countable S] [LinearOrder S]

open scoped Classical in
/-- The law of the spins *inside* `Λ` under `γ_Λ^{J,h}(·|ω)`, before juxtaposition with the
boundary condition: the Gaussian with precision `β 𝒥_Λ` and mean `m(Λ,ω)` on `Ω_J`, the Dirac mass
at `0` off it. -/
def gaussianInfiniteRangeInner (J : S → S → ℝ) (h : S → ℝ) (β : ℝ) (Λ : Finset S) (ω : S → ℝ) :
    Measure (Λ → ℝ) :=
  if ω ∈ gaussianConvergenceSet J then
    multivariateGaussianPi (β • gaussianCouplingMatrix J Λ) (gaussianTsumMean J h Λ ω)
  else Measure.dirac (0 : Λ → ℝ)

/-- Both branches of (13.18) are `juxt`-pushforwards: the Dirac branch is the pushforward of the
Dirac mass at the zero configuration on `Λ`. -/
theorem gaussianInfiniteRangeMeasure_eq_map (J : S → S → ℝ) (h : S → ℝ) (β : ℝ) (Λ : Finset S)
    (ω : S → ℝ) :
    gaussianInfiniteRangeMeasure J h β Λ ω =
      (gaussianInfiniteRangeInner J h β Λ ω).map (juxt (Λ : Set S) ω) := by
  by_cases hω : ω ∈ gaussianConvergenceSet J
  · rw [gaussianInfiniteRangeMeasure_of_mem J h β Λ hω, gaussianInfiniteRangeInner, if_pos hω]
  · rw [gaussianInfiniteRangeMeasure_of_notMem J h β Λ hω, gaussianInfiniteRangeInner, if_neg hω,
      Measure.map_dirac' (Measurable.juxt (Λ := (Λ : Set S)) (η := ω)) (0 : Λ → ℝ)]

/-- **Georgii Definition (13.18)**, as a kernel from the boundary condition to the configuration
space, measurable for the outside-volume σ-algebra. -/
def gaussianInfiniteRangeFun (J : S → S → ℝ) (h : S → ℝ)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    (Λ : Finset S) : Kernel[cylinderEvents ((Λ : Set S)ᶜ)] (S → ℝ) (S → ℝ) :=
  @Kernel.mk _ _ (_) _ (gaussianInfiniteRangeMeasure J h β Λ)
    ((measurable_gaussianInfiniteRangeMeasure J h hPD hβ Λ).cylinderEvents_of_dependsOn
      (dependsOn_gaussianInfiniteRangeMeasure J h β Λ))

@[simp] lemma gaussianInfiniteRangeFun_apply (J : S → S → ℝ) (h : S → ℝ)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    (Λ : Finset S) (ω : S → ℝ) :
    gaussianInfiniteRangeFun J h hPD hβ Λ ω = gaussianInfiniteRangeMeasure J h β Λ ω := rfl

lemma isMarkovKernel_gaussianInfiniteRangeFun (J : S → S → ℝ) (h : S → ℝ)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    (Λ : Finset S) : IsMarkovKernel (gaussianInfiniteRangeFun J h hPD hβ Λ) :=
  ⟨fun ω ↦ isProbabilityMeasure_gaussianInfiniteRangeMeasure J h hPD hβ Λ ω⟩

/-- **`γ_Λ^{J,h}` is proper**: it is a `juxt`-pushforward, so it fixes the configuration off `Λ`.
Georgii's Remark (1.32). -/
lemma isProper_gaussianInfiniteRangeFun (J : S → S → ℝ) (h : S → ℝ)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    (Λ : Finset S) : (gaussianInfiniteRangeFun J h hPD hβ Λ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB ω
  rw [gaussianInfiniteRangeFun_apply, gaussianInfiniteRangeMeasure_eq_map]
  set Δc : Set S := ((Λ : Set S)ᶜ) with hΔc
  have hBcomap : MeasurableSet[MeasurableSpace.comap
      (Set.domRestrict Δc) (inferInstance : MeasurableSpace (Δc → ℝ))] B := by
    rw [← MeasureTheory.cylinderEvents_eq_comap_restrict (S := S) (E := ℝ) (Δ := Δc)]
    exact hB
  rcases hBcomap with ⟨C, hC, rfl⟩
  exact Specification.map_juxt_inter_restrict_compl_preimage_of_measure
    (S := S) (E := ℝ) (Λ := Λ) (gaussianInfiniteRangeInner J h β Λ ω) hA hC ω

/-- **Pointwise consistency of (13.18) on the convergence set.** For `ω ∈ Ω_J` every configuration
that `γ_Δ^{J,h}(·|ω)` charges agrees with `ω` off `Δ`, and there both `γ_Λ^{J,h}` and `γ_Δ^{J,h}`
are the kernels of `Potential.gaussianSpecification` for the truncated coupling and the shifted
external field; the Gibbsian consistency of the latter is then quoted verbatim. -/
theorem lintegral_gaussianInfiniteRangeMeasure_of_mem (J : S → S → ℝ) (h : S → ℝ)
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) {ω : S → ℝ} (hω : ω ∈ gaussianConvergenceSet J)
    {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ ζ, gaussianInfiniteRangeMeasure J h β Λ ζ A ∂(gaussianInfiniteRangeMeasure J h β Δ ω) =
      gaussianInfiniteRangeMeasure J h β Δ ω A := by
  have hmeasf : Measurable fun ζ : S → ℝ ↦ gaussianInfiniteRangeMeasure J h β Λ ζ A :=
    (Measure.measurable_coe hA).comp (measurable_gaussianInfiniteRangeMeasure J h hPD hβ Λ)
  have hmeasg : Measurable fun ζ : S → ℝ ↦
      gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
        (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
        (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Λ ζ A :=
    (Kernel.measurable_coe _ hA).mono cylinderEvents_le_pi le_rfl
  have hΔ : gaussianInfiniteRangeMeasure J h β Δ ω =
      gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
        (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
        (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Δ ω :=
    gaussianInfiniteRangeMeasure_eq_gaussianSpecification_truncate J h hSymm hPD hβ
      (Finset.Subset.refl Δ) hω (fun i _ ↦ rfl)
  have hpt : ∀ ζ' : Δ → ℝ,
      gaussianInfiniteRangeMeasure J h β Λ (juxt (Δ : Set S) ω ζ') A =
        gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
          (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
          (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Λ
          (juxt (Δ : Set S) ω ζ') A := by
    intro ζ'
    have hζω : ∀ i ∉ Δ, juxt (Δ : Set S) ω ζ' i = ω i := fun i hi ↦
      juxt_apply_of_not_mem (by simpa using hi) ζ'
    have hζΩ : juxt (Δ : Set S) ω ζ' ∈ gaussianConvergenceSet J :=
      (gaussianConvergenceSet_congr J (Λ := Δ) fun i hi ↦ (hζω i (by simpa using hi)).symm).1 hω
    rw [gaussianInfiniteRangeMeasure_eq_gaussianSpecification_truncate J h hSymm hPD hβ hΛΔ
      hζΩ hζω]
  have hstep : ∫⁻ ζ, gaussianInfiniteRangeMeasure J h β Λ ζ A
        ∂(gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
          (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
          (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Δ ω) =
      ∫⁻ ζ, gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
            (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
            (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Λ ζ A
        ∂(gaussianSpecification (truncateCoupling J Δ) (truncateField J h Δ ω)
          (symm_truncateCoupling hSymm Δ) (finite_setOf_truncateCoupling_ne_zero J Δ)
          (posDef_gaussianCouplingMatrix_truncateCoupling hSymm hPD Δ) β hβ Δ ω) := by
    rw [gaussianSpecification_apply, lintegral_map hmeasf Measurable.juxt,
      lintegral_map hmeasg Measurable.juxt]
    exact lintegral_congr hpt
  rw [hΔ, hstep]
  exact Specification.lintegral_apply_of_subset _ hΛΔ ω hA

/-- **Pointwise consistency of (13.18) off the convergence set**, where both kernels are the Dirac
reference: `δ_{0_Λ (0_Δ ω)_{S∖Λ}} = δ_{0_Δ ω_{S∖Δ}}` for `Λ ⊆ Δ`. -/
theorem lintegral_gaussianInfiniteRangeMeasure_of_notMem (J : S → S → ℝ) (h : S → ℝ)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    {Λ Δ : Finset S} (hΛΔ : Λ ⊆ Δ) {ω : S → ℝ} (hω : ω ∉ gaussianConvergenceSet J)
    {A : Set (S → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ ζ, gaussianInfiniteRangeMeasure J h β Λ ζ A ∂(gaussianInfiniteRangeMeasure J h β Δ ω) =
      gaussianInfiniteRangeMeasure J h β Δ ω A := by
  have hmeasf : Measurable fun ζ : S → ℝ ↦ gaussianInfiniteRangeMeasure J h β Λ ζ A :=
    (Measure.measurable_coe hA).comp (measurable_gaussianInfiniteRangeMeasure J h hPD hβ Λ)
  have hnot : juxt (Δ : Set S) ω (0 : Δ → ℝ) ∉ gaussianConvergenceSet J := fun hc ↦
    hω ((gaussianConvergenceSet_congr J (Λ := Δ)
      (fun i hi ↦ (juxt_apply_of_not_mem hi (0 : Δ → ℝ)).symm)).2 hc)
  rw [gaussianInfiniteRangeMeasure_of_notMem J h β Δ hω, lintegral_dirac' _ hmeasf,
    gaussianInfiniteRangeMeasure_of_notMem J h β Λ hnot,
    Specification.juxt_juxt_zero_of_subset hΛΔ]

/-- **Georgii Definition (13.18): `γ^{J,h}` is consistent.** Georgii disposes of this in one
sentence ("the same arguments as in Proposition (2.5) and Remark (1.32) show that `γ^{J,h}` is
indeed a specification"). The proof here is a reduction to the finite-range case. Off `Ω_J` both
kernels are the Dirac reference and `Ω_J` is invariant under finite modifications
(`Potential.gaussianConvergenceSet_congr`), so the branches never mix; on `Ω_J`, every
configuration `γ_Δ^{J,h}(·|ω)` charges agrees with `ω` off `Δ`, and there both kernels are those of
`Potential.gaussianSpecification` for the truncated data
(`Potential.gaussianInfiniteRangeMeasure_eq_gaussianSpecification_truncate`), whose consistency is
the Gibbsian one. -/
theorem isConsistent_gaussianInfiniteRangeFun (J : S → S → ℝ) (h : S → ℝ)
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β) :
    IsConsistent (gaussianInfiniteRangeFun J h hPD hβ) := by
  intro Λ Δ hΛΔ
  ext ω A hA
  rw [Kernel.comp_apply' _ _ _ hA]
  have hcomap : ∀ ζ : S → ℝ,
      ((gaussianInfiniteRangeFun J h hPD hβ Λ).comap id cylinderEvents_le_pi) ζ A =
        gaussianInfiniteRangeMeasure J h β Λ ζ A := fun _ ↦ rfl
  simp only [hcomap, gaussianInfiniteRangeFun_apply]
  by_cases hω : ω ∈ gaussianConvergenceSet J
  · exact lintegral_gaussianInfiniteRangeMeasure_of_mem J h hSymm hPD hβ hΛΔ hω hA
  · exact lintegral_gaussianInfiniteRangeMeasure_of_notMem J h hPD hβ hΛΔ hω hA

/-- The raw family of (13.18) before bundling the Markov and properness hypotheses. -/
def gaussianInfiniteRangePre (J : S → S → ℝ) (h : S → ℝ) (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β) :
    PreSpecification S ℝ where
  toFun := gaussianInfiniteRangeFun J h hPD hβ
  isConsistent' := isConsistent_gaussianInfiniteRangeFun J h hSymm hPD hβ

/-- **Georgii Definition (13.18)**: the Gaussian specification `γ^{J,h}` of a symmetric positive
definite `J` — *no finite-range hypothesis* — and an external field `h ∈ Ω`, at inverse
temperature `β`. On the convergence set `Ω_J` of (13.9) it is the Gibbsian specification of the
quadratic potential `Φ^{J,h}` of (13.11), whose Hamiltonian exists there because the boundary field
`∑_{j ∉ Λ} J(i,j) ω_j` converges; off `Ω_J` it is the Dirac reference `δ_{0_Λ ω_{S∖Λ}}`. -/
def gaussianInfiniteRangeSpecification (J : S → S → ℝ) (h : S → ℝ)
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β) :
    Specification S ℝ where
  toPreSpecification := gaussianInfiniteRangePre J h hSymm hPD hβ
  isMarkovKernel' := isMarkovKernel_gaussianInfiniteRangeFun J h hPD hβ
  isProper' := isProper_gaussianInfiniteRangeFun J h hPD hβ

@[simp] lemma gaussianInfiniteRangeSpecification_apply (J : S → S → ℝ) (h : S → ℝ)
    (hSymm : ∀ i j, J i j = J j i)
    (hPD : ∀ Γ : Finset S, (gaussianCouplingMatrix J Γ).PosDef) {β : ℝ} (hβ : 0 < β)
    (Λ : Finset S) (ω : S → ℝ) :
    gaussianInfiniteRangeSpecification J h hSymm hPD hβ Λ ω =
      gaussianInfiniteRangeMeasure J h β Λ ω := rfl

end IsSpecification

end Potential

end

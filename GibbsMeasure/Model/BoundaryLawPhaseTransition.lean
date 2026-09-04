/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLawUniqueness

/-!
# Entrance laws, and the criterion for phase transition used in Georgii §11.2–§11.4

Sites `ℤ`, a countable state space `E`, counting measure, a positive matrix `Q` with finite
powers (Georgii (11.1)), and its specification `γ^Q = transferSpecification Q hQ`
(`GibbsMeasure/Model/BoundaryLaw.lean`).

Georgii's three examples of phase transition (§11.2 Spitzer–Cox, §11.3 Kalikow, §11.4 Spitzer)
all follow the same route: exhibit a boundary law `{ℓ_i, r_i}` for `Q` whose one-site marginals
`ℓ_i r_i` genuinely depend on `i`; then the measure (11.10) it defines is a Gibbs measure for
`γ^Q` (Theorem (11.9)(a)) which is *not* shift invariant, and Corollary (11.14)(b), (c)
(`infinite_extremePoints_G_of_exists_not_mem_invariantG`) turns that into `|ex 𝒢(Q)| = ∞`.
This file isolates that route, together with the *entrance law* half of it: for a stochastic `Q`
a family of probability vectors `α_i` with `α_i Q = α_{i+1}` is a boundary law with `r_i ≡ 1`.

## Main declarations

* `MeasureTheory.GibbsMeasure.Markov.IsEntranceLaw Q α`: Georgii's entrance law — probability
  vectors `α_i > 0` (`i ∈ ℤ`) with `α_i Q = α_{i+1}`.
* `MeasureTheory.GibbsMeasure.Markov.IsEntranceLaw.isBoundaryLaw`: for a *stochastic* `Q`, an
  entrance law is a boundary law with `r_i ≡ 1` (Georgii uses this in §11.3 and §11.4). It
  generalises `isBoundaryLaw_const`, the case `α_i = α` constant.
* `MeasureTheory.GibbsMeasure.Markov.IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_self`:
  the one-site marginal of (11.10) is `μ(σ_i = x) = ℓ_i(x) r_i(x)`.
* `MeasureTheory.GibbsMeasure.Markov.IsBoundaryLaw.map_shift_ne_of_marginal_ne`,
  `MeasureTheory.GibbsMeasure.Markov.not_mem_invariantG_boundaryLawMeasure_of_marginal_ne`:
  two different one-site marginals make the measure (11.10) fail to be shift invariant.
* `MeasureTheory.GibbsMeasure.Markov.infinite_extremePoints_G_of_boundaryLaw_marginal_ne`:
  **the phase-transition criterion**. If `Q` is a transfer matrix carrying a boundary law with
  `ℓ_i(x) r_i(x) ≠ ℓ_j(x) r_j(x)` for some `i, j, x`, then `ex 𝒢(γ^Q)` is infinite. In
  particular `𝒢(γ^Q)` is not a singleton (`not_subsingleton_G_of_boundaryLaw_marginal_ne`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

/-! ## Entrance laws -/

section EntranceLaw

variable {Q : E → E → ℝ≥0∞} {α : ℤ → E → ℝ≥0∞}

/-- **Georgii's entrance law** for a stochastic matrix `Q` (§11.3, §11.4): a family `{α_i}` of
strictly positive probability vectors on `E`, indexed by `i ∈ ℤ`, with `α_i Q = α_{i+1}`. -/
structure IsEntranceLaw (Q : E → E → ℝ≥0∞) (α : ℤ → E → ℝ≥0∞) : Prop where
  /-- Each `α_i` is strictly positive. -/
  pos : ∀ i x, 0 < α i x
  /-- Each `α_i` is a probability vector. -/
  tsum_eq_one : ∀ i, ∑' x, α i x = 1
  /-- `α_i Q = α_{i+1}`. -/
  step : ∀ i y, ∑' x, α i x * Q x y = α (i + 1) y

namespace IsEntranceLaw

variable (h : IsEntranceLaw Q α)
include h

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma ne_top (i : ℤ) (x : E) : α i x ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (by rw [h.tsum_eq_one i]; exact ENNReal.one_ne_top) x

/-- An entrance law for a stochastic matrix `Q` is a boundary law with `r_i ≡ 1`: this is how
Georgii turns the entrance laws of §11.3 and §11.4 into Gibbs measures through Theorem
(11.9)(a). The case `α_i = α` constant is `isBoundaryLaw_const`. -/
lemma isBoundaryLaw (hQ1 : ∀ x, ∑' y, Q x y = 1) : IsBoundaryLaw Q α (fun _ _ ↦ 1) :=
  IsBoundaryLaw.of_tsum h.pos h.ne_top (fun _ _ ↦ one_pos) (fun _ _ ↦ ENNReal.one_ne_top)
    h.step (fun _ x ↦ by simpa only [mul_one] using hQ1 x)
    (fun i ↦ by simpa only [mul_one] using h.tsum_eq_one i)

end IsEntranceLaw

end EntranceLaw

/-! ## One-site marginals of the measure (11.10) -/

section Marginal

variable {Q : E → E → ℝ≥0∞} {ℓ r : ℤ → E → ℝ≥0∞} [Nonempty E] (hbl : IsBoundaryLaw Q ℓ r)
include hbl

/-- The one-site marginal of the measure (11.10): `μ(σ_i = x) = ℓ_i(x) r_i(x)`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_self (i : ℤ) (σ : ℤ → E) :
    boundaryLawMeasure hbl (intervalCylinder i i σ) = ℓ i (σ i) * r i (σ i) := by
  rw [hbl.boundaryLawMeasure_intervalCylinder le_rfl σ, pathProd_self, mul_one]

/-- If two one-site marginals of the measure (11.10) differ, the shift by their distance moves
it. -/
theorem IsBoundaryLaw.map_shift_ne_of_marginal_ne {i j : ℤ} {x : E}
    (h : ℓ i x * r i x ≠ ℓ j x * r j x) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E (i - j)).toFun
      ≠ boundaryLawMeasure hbl := by
  intro heq
  refine h ?_
  have h1 : boundaryLawMeasure (hbl.shift (i - j)) (intervalCylinder i i fun _ ↦ x)
      = boundaryLawMeasure hbl (intervalCylinder i i fun _ ↦ x) := by
    rw [← hbl.boundaryLawMeasure_map_shift (i - j), heq]
  rw [(hbl.shift (i - j)).boundaryLawMeasure_intervalCylinder_self i (fun _ ↦ x),
    hbl.boundaryLawMeasure_intervalCylinder_self i (fun _ ↦ x),
    show i - (i - j) = j by ring] at h1
  exact h1.symm

variable (hQ : IsTransferMatrix Q)
include hQ

/-- The measure (11.10) of a boundary law with two different one-site marginals is a Gibbs
measure for `γ^Q` which is not shift invariant. -/
theorem not_mem_invariantG_boundaryLawMeasure_of_marginal_ne {i j : ℤ} {x : E}
    (h : ℓ i x * r i x ≠ ℓ j x * r j x) :
    boundaryLawMeasure hbl
      ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := fun hmem ↦
  hbl.map_shift_ne_of_marginal_ne h
    ((mem_invariantFields_shiftGroup.1 hmem.2).2 (i - j)).map_eq

/-- **The phase-transition criterion behind Georgii §11.2–§11.4.** If a transfer matrix `Q`
carries a boundary law whose one-site marginals `ℓ_i r_i` are not all equal, then `ex 𝒢(γ^Q)` is
infinite: `Q` exhibits a phase transition. -/
theorem infinite_extremePoints_G_of_boundaryLaw_marginal_ne {i j : ℤ} {x : E}
    (h : ℓ i x * r i x ≠ ℓ j x * r j x) :
    ((G (transferSpecification Q hQ)).extremePoints ℝ≥0∞).Infinite :=
  infinite_extremePoints_G_of_exists_not_mem_invariantG Q hQ
    ⟨inferInstance, isGibbsMeasure_transferSpecification_boundaryLawMeasure hQ hbl⟩
    (not_mem_invariantG_boundaryLawMeasure_of_marginal_ne hbl hQ h)

/-- Under the hypothesis of `infinite_extremePoints_G_of_boundaryLaw_marginal_ne` the set of
Gibbs measures for `γ^Q` is not a singleton: there is a phase transition. -/
theorem not_subsingleton_G_of_boundaryLaw_marginal_ne {i j : ℤ} {x : E}
    (h : ℓ i x * r i x ≠ ℓ j x * r j x) :
    ¬ (G (transferSpecification Q hQ)).Subsingleton := fun hsub ↦
  infinite_extremePoints_G_of_boundaryLaw_marginal_ne hbl hQ h
    ((hsub.anti extremePoints_subset).finite)

end Marginal

end MeasureTheory.GibbsMeasure.Markov

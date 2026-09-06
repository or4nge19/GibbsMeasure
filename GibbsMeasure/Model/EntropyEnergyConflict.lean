/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SpernerPhaseTransition

/-!
# Georgii §19.3.1: competing potential wells, and a phase transition at a definite temperature

Georgii, *Gibbs Measures and Phase Transitions*, §19.3.1, Theorem (19.16), together with the
part of Comment (18.11) that it uses.

All the phase transitions of Chapters 18 and 19 so far came from a degeneracy of the ground
states and occurred at *all* sufficiently low temperatures.  Theorem (19.16) is different: the
cube interaction has `N + 1` wells, one of which (`W_0`) is deeper but much *thinner* than the
others, so that energy prefers `W_0` while entropy prefers `W_1, …, W_N`; at one definite
inverse temperature `β*` the two effects balance and a `W_0`-phase coexists with `N` further
phases.  This is the mechanism of a first order phase transition.

## Main results

* `MeasureTheory.GibbsMeasure.rectCost_le_of_abs_sub_le` and
  `MeasureTheory.GibbsMeasure.rectPatternWeight_le_of_abs_sub_le` — **Georgii, Remark
  (18.9)(3) for the rectangle weight `t̃(G, Φ)` of Comment (18.11)**: a uniform perturbation of
  size `η` of the cube interaction multiplies `t̃(G, Φ)` by at most `e^{2η}`.
* `MeasureTheory.GibbsMeasure.rectPatternWeight_le_of_ae_le` — the estimate of `t̃(G, Φ)` by a
  single rectangle, which is how Steps 1 and 2 of Georgii's proof of (19.16) use `t̃`.
* `MeasureTheory.GibbsMeasure.exists_correspondence_of_weight_le` and
  `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_family_of_weight_le` — **Proposition
  (19.14)** for an arbitrary *Peierls weight* `w`, i.e. any family of weights that satisfies
  the chessboard estimate (18.10), Remark (18.9)(3) and the confinement bound of (18.12).
  `t(G, Φ)` is one such weight, `t̃(G, Φ)` is another, and Georgii applies (19.14) to `t̃` in
  the proof of (19.16) ("with `G_n = W_n` and `t̃(·, ·)` instead of `t(·, ·)`").
* `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_family_of_rectPatternWeight_le` — (19.14)
  and (19.13) chained, with `t̃` in place of `t`.
* `MeasureTheory.GibbsMeasure.IsCompetingWells` — Georgii's assumption **(A)** = (A1)–(A3).
* `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_family_isCompetingWells` — **Theorem
  (19.16)**.

## `t` and `t̃` are not comparable

Georgii's Comment (18.11) says that the conclusion of Lemma (18.10) *remains true* with

`t̃(G, Φ) = exp[-λ-inf_{E^C∖G} Φ_C] λ^C(E^C∖G)^{1/|C|} inf_R exp[λ-sup_R Φ_C]/λ^C(R)^{1/|C|}`

(the infimum over rectangles `R = ∏_{c ∈ C} R_c`) in place of `t(G, Φ)`; it does *not* claim
an inequality between the two, and there is none.  Both weights have the same first two
factors up to the normalisation `e^{m_Φ}`, and by Remark (18.9)(2) the third factors are

`e^{m_Φ} inf_{δ>0} e^δ/λ^C(G_δ(Φ)) = inf_{M : λ^C(M) > 0} e^{λ-sup_M Φ_C}/λ^C(M)`  and
`inf_R e^{λ-sup_R Φ_C}/λ^C(R)^{1/|C|}`.

The rectangle infimum ranges over fewer sets, which makes it larger, but its denominator
carries the extra power `1/|C|`, which (as `λ^C` is a probability measure) makes each of its
terms smaller.  Neither effect dominates.

*`t̃ < t`.*  Let `Φ_C = 0` on a rectangle `R_0 = ∏_c I` with `λ(I) = ε`, and `Φ_C = K` off
`R_0` with `K` large.  Then `R_0` is admissible for both infima and gives the terms
`λ^C(R_0)^{-1/|C|} = ε^{-1}` for `t̃` and `λ^C(R_0)^{-1} = ε^{-|C|}` for `t`; every other
set contributes at least `e^K`, so for large `K` the third factor of `t̃` is `ε^{-1}` and that
of `t` is `ε^{-|C|}`.

*`t < t̃`.*  Take `|C| = 2`, `E = [0, 1]` with Lebesgue measure, `Φ_C(x, y) = 0` if
`|x - y| < ε` and `= K` otherwise.  The band `M = {|x - y| < ε}` has `λ^C(M) ≈ 2ε` and gives
the `t`-term `1/(2ε)`; but a rectangle `R = R_0 × R_1` on which `Φ_C` vanishes almost
everywhere satisfies `λ(R_0) + λ(R_1) ≤ 2ε`, hence `λ^C(R)^{1/2} ≤ ε`, so for large `K` every
`t̃`-term is at least `1/ε`.

Consequently (19.14) has to be reproved with `t̃`, which is what
`exists_correspondence_of_weight_le` does once and for all for any weight satisfying the three
properties of `t` that its proof uses.

## Deviations from Georgii

* Georgii writes `λ^C(V)^{1/4}` throughout the proof of (19.16), and in the displayed
  conditions (19.17) and (19.18); `1/4 = 1/|C|` is right only for `d = 2`.  Since the ambient
  chapter is written for all `d ≥ 2` — and since §18.1 is, too — the exponent here is `1/|C|`,
  and `d = 2` is fixed only because Propositions (19.13) and (19.14) live in the plane.  With
  `d = 2` the two readings agree.
* Georgii's `λ-inf` and `λ-sup` are essential infima and suprema, so his assumption (A) is a
  family of `λ^C`-almost everywhere statements; `IsCompetingWells` states them that way.  His
  remark that (A) implies `G_ε(Φ^h) ⊆ W_0` for `0 < ε < a` is therefore true only up to a
  `λ^C`-null set, and the *pointwise* inclusion required by Definition (18.23)(a)(i) is
  supplied here — as it may be, since (19.13) leaves the potential of the stable partition
  free — by the indicator of `E^C ∖ (W_0 ∪ ⋯ ∪ W_N)`; see
  `isPStablePartition_of_isCompetingWells`.
* Only the inequalities `λ-inf_{W_0} Φ^h_C ≥ 0` and `λ-inf_{W_n} Φ^h_C ≥ a + h_n` of (A1) are
  assumed, not Georgii's equalities: the reverse halves say that the wells are no deeper than
  claimed and are used nowhere in the proof.  This weakens the hypothesis, and it is what the
  examples (19.19), (19.20) have to verify anyway.
* The family `(Φ^h)` is taken as a function of *all* `h ∈ ℝ^N`, measurable, bounded and
  reflection invariant at every `h`; Georgii's family is indexed by `∂ℝ_+^N` only.  Nothing is
  lost: a family on `∂ℝ_+^N` extends to `ℝ^N` (say by `Φ^h := Φ^0` off `∂ℝ_+^N`), and
  assumption (A) and the continuity hypothesis are imposed at `h ∈ ∂ℝ_+^N` only.  This matches
  the convention of Propositions (19.13), (19.14) in the tree, whose families are indexed by
  all of `ℝ^{N+1}` and constrained on the simplex.
* Georgii's Proposition (19.14) is stated in the tree relative to the simplex and with the
  denominator of (19.13)(iii) cleared; both conventions are inherited here.
* Georgii's `β* ∈ [β₀, β₁]` mentions the `β₁` his Step 2 constructs; here `β₁` is part of the
  conclusion, existentially quantified with `β₀ < β₁`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Pointwise Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E]

/-! ### Georgii, Remark (18.9)(3) for the rectangle weight of Comment (18.11) -/

section RectPerturbation

variable {d : ℕ} {φ ψ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {η : ℝ}

omit [IsProbabilityMeasure ν] in
/-- **The third factor of Georgii's `t̃(G, Φ)` under a uniform perturbation.**  If
`‖Ψ_C - Φ_C‖ ≤ η` then `inf_R e^{λ-sup_R Ψ_C}/λ^C(R)^{1/|C|} ≤ e^η inf_R
e^{λ-sup_R Φ_C}/λ^C(R)^{1/|C|}`: a rectangle admissible for `Φ` at the level `b` is
admissible for `Ψ` at the level `b + η`.

Intended home: `GibbsMeasure/Specification/PatternPercolation.lean`, next to `rectCost`. -/
theorem rectCost_le_of_abs_sub_le (hd : ∀ ζ, |ψ ζ - φ ζ| ≤ η) :
    rectCost ψ ν ≤ ENNReal.ofReal (Real.exp η) * rectCost φ ν := by
  rw [rectCost, rectCost, ENNReal.mul_iInf (fun h ↦ absurd h ENNReal.ofReal_ne_top)]
  refine le_iInf fun p ↦ ?_
  have hp : ∀ᵐ ζ ∂((cubeMeasure d ν).restrict (Set.univ.pi p.1.1)), ψ ζ ≤ p.1.2 + η := by
    filter_upwards [p.2] with ζ hζ
    have := (abs_le.1 (hd ζ)).2
    linarith
  refine le_trans (iInf_le (fun q : RectBound ψ ν ↦ ENNReal.ofReal (Real.exp q.1.2)
    / cubeMeasure d ν (Set.univ.pi q.1.1) ^ ((2 ^ d : ℝ)⁻¹))
    (⟨(p.1.1, p.1.2 + η), hp⟩ : RectBound ψ ν)) (le_of_eq ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← Real.exp_add, add_comm η p.1.2]

/-- **Georgii, Remark (18.9)(3) for the weight `t̃(G, Φ)` of Comment (18.11).**  A uniform
perturbation of the cube interaction of size `η` multiplies `t̃(G, Φ)` by at most `e^{2η}`;
upper semicontinuity of `t̃(G, ·)` follows by letting `η → 0`.  (The corresponding factor for
`t(G, Φ)` is `e^{4η}`: `t` has to move `m_Φ` as well.)

Intended home: `GibbsMeasure/Specification/PatternPercolation.lean`. -/
theorem rectPatternWeight_le_of_abs_sub_le {M : ℝ} (hM : ∀ ζ, M ≤ φ ζ)
    (hd : ∀ ζ, |ψ ζ - φ ζ| ≤ η) (G : Set ((Fin d → Fin 2) → E)) :
    rectPatternWeight ψ ν G ≤ ENNReal.ofReal (Real.exp (2 * η)) * rectPatternWeight φ ν G := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  by_cases hGc : cubeMeasure d ν Gᶜ = 0
  · rw [rectPatternWeight, hGc, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  have hfirst : ENNReal.ofReal (Real.exp (-energyOutside ψ ν G))
      ≤ ENNReal.ofReal (Real.exp η) * ENNReal.ofReal (Real.exp (-energyOutside φ ν G)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      have := energyOutside_le_add (ν := ν) hM hd hGc
      linarith))
  calc rectPatternWeight ψ ν G
      ≤ ENNReal.ofReal (Real.exp η) * ENNReal.ofReal (Real.exp (-energyOutside φ ν G))
          * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
          * (ENNReal.ofReal (Real.exp η) * rectCost φ ν) :=
        mul_le_mul' (mul_le_mul' hfirst le_rfl) (rectCost_le_of_abs_sub_le hd)
    _ = ENNReal.ofReal (Real.exp (2 * η)) * rectPatternWeight φ ν G := by
        rw [rectPatternWeight, show ENNReal.ofReal (Real.exp (2 * η))
          = ENNReal.ofReal (Real.exp η) * ENNReal.ofReal (Real.exp η) by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            congr 2
            ring]
        ring

omit [IsProbabilityMeasure ν] in
/-- **A single rectangle bounds `t̃(G, Φ)`.**  If `A ≤ Φ_C` `λ^C`-a.e. off `G` and `Φ_C ≤ b`
`λ^C`-a.e. on the rectangle `R`, then

`t̃(G, Φ) ≤ e^{b - A} λ^C(E^C ∖ G)^{1/|C|} / λ^C(R)^{1/|C|}`.

This is how Steps 1 and 2 of Georgii's proof of (19.16) use `t̃`: the wells `V_n` are the
rectangles, and the barrier (A2) resp. the depths (A1) give `A`.

Intended home: `GibbsMeasure/Specification/PatternPercolation.lean`. -/
theorem rectPatternWeight_le_of_ae_le {G : Set ((Fin d → Fin 2) → E)} {A b : ℝ}
    (hA : ∀ᵐ ζ ∂((cubeMeasure d ν).restrict Gᶜ), A ≤ φ ζ)
    {R : (Fin d → Fin 2) → Set E}
    (hb : ∀ᵐ ζ ∂((cubeMeasure d ν).restrict (Set.univ.pi R)), φ ζ ≤ b) :
    rectPatternWeight φ ν G
      ≤ ENNReal.ofReal (Real.exp (b - A)) * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
        / cubeMeasure d ν (Set.univ.pi R) ^ ((2 ^ d : ℝ)⁻¹) := by
  have hp : (0 : ℝ) < (2 ^ d : ℝ)⁻¹ := inv_pos.2 (pow_pos two_pos d)
  by_cases hGc : cubeMeasure d ν Gᶜ = 0
  · rw [rectPatternWeight, hGc, ENNReal.zero_rpow_of_pos hp, mul_zero, zero_mul]
    exact zero_le
  have hz : NeZero ((cubeMeasure d ν).restrict Gᶜ) := by
    refine ⟨fun hc ↦ hGc ?_⟩
    rw [← Measure.restrict_apply_univ, hc, Measure.coe_zero, Pi.zero_apply]
  have hAle : A ≤ energyOutside φ ν G :=
    le_essInf_of_ae_le _ hA (isCoboundedUnder_ge_ae φ)
  calc rectPatternWeight φ ν G
      ≤ ENNReal.ofReal (Real.exp (-A)) * cubeMeasure d ν Gᶜ ^ ((2 ^ d : ℝ)⁻¹)
          * (ENNReal.ofReal (Real.exp b)
            / cubeMeasure d ν (Set.univ.pi R) ^ ((2 ^ d : ℝ)⁻¹)) := by
        refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.2 (by linarith))) le_rfl) ?_
        exact iInf_le (fun q : RectBound φ ν ↦ ENNReal.ofReal (Real.exp q.1.2)
          / cubeMeasure d ν (Set.univ.pi q.1.1) ^ ((2 ^ d : ℝ)⁻¹)) ⟨(R, b), hb⟩
    _ = _ := by
        simp only [div_eq_mul_inv]
        rw [show ENNReal.ofReal (Real.exp (b - A))
          = ENNReal.ofReal (Real.exp (-A)) * ENNReal.ofReal (Real.exp b) by
            rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
            congr 2
            ring]
        ring

end RectPerturbation


/-! ### Georgii, Proposition (19.14) for an arbitrary Peierls weight -/

section Weight

open Peierls

variable [StandardBorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {ψ : (Fin (N + 1) → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ} {K : ℕ → Set E} {t : ℝ≥0∞}
  {w : (Fin (N + 1) → ℝ) → Set ((Fin 2 → Fin 2) → E) → ℝ≥0∞}

/-- Upper semicontinuity in the limit: a quantity below `e^{4ε} c` for every `ε > 0` is below
`c`.  (A copy of the private helper of `GibbsMeasure/Model/SpernerPhaseTransition.lean`.) -/
private lemma le_of_forall_exp_mul_le' {a c : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ENNReal.ofReal (Real.exp (4 * ε)) * c) : a ≤ c := by
  have hcont : Continuous fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have h1 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε))) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (Real.exp (4 * (0 : ℝ))))) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h0
  have h2 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) * c) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have h3 : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (Real.exp (4 * ε)) * c) (𝓝[>] (0 : ℝ))
        (𝓝 (1 * c)) := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    simpa using h3
  exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun ε hε ↦ h ε hε)

/-- **Georgii, Proposition (19.14) for an arbitrary Peierls weight.**  Georgii states (19.14)
for his weight `t(G, Φ)` of (18.8), but applies it in the proof of Theorem (19.16) to the
rectangle weight `t̃(G, Φ)` of Comment (18.11) ("with `G_n = W_n` and `t̃(·, ·)` instead of
`t(·, ·)`"), and the two weights are not comparable.  Only three properties of the weight are
used, and they are the hypotheses `hwP`, `hwS`, `hwT` here:

* `hwP` — **the chessboard estimate (18.10)**: `μ(D ∩ V(W, ·) = ∅) ≤ w(W)^{|D|}` for every
  `r`-symmetric `W ∈ ℰ^C` and every `μ ∈ 𝒢₀(Ψ^α)`;
* `hwS` — **Remark (18.9)(3)**: `w(·)` is upper semicontinuous in the parameter, in the
  quantitative form that a uniform perturbation of size `ε` multiplies it by at most `e^{4ε}`;
* `hwT` — **the confinement bound in the proof of (18.12)**: `w(K_ℓ^C) → 0` as `ℓ → ∞`.

The weight `t(G, Φ)` satisfies the three by `forall_notMem_latticePattern_le_patternWeight`,
`patternWeight_le_of_abs_sub_le` and `tendsto_patternWeight_cubePi`, so
`exists_correspondence_of_patternWeight_le` is the instance `w = t`; the infimum `t ⊓ t̃`
satisfies them too, and that instance is
`exists_gibbsMeasure_family_of_rectPatternWeight_le` below.

Under Georgii's conditions

* (I) `α ↦ Ψ^α_C` is continuous in the uniform norm along the simplex;
* (II) `w(G) ≤ t` for all `α`, where `G = G_0 ∪ ⋯ ∪ G_N`;
* (III) `(N+1) w(E^C ∖ G_n) < 1 - t` whenever `α(n) = 0`,

Georgii's correspondence `Γ(α)` satisfies the hypotheses (i), (ii) (with `c = 4 z(t)`) and
(iii) of Proposition (19.13).

Intended home: `GibbsMeasure/Model/SpernerPhaseTransition.lean`, in place of
`exists_correspondence_of_patternWeight_le`, of which it is the generalisation. -/
theorem exists_correspondence_of_weight_le
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n))
    (hψmeas : ∀ α, Measurable (ψ α)) (hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψ α ζ)
    (hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψ α (cubeRefl E k ζ) = ψ α ζ)
    (hKconf : ∀ α, IsCubeConfining (ψ α) ν K)
    (hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψ α' ζ - ψ α ζ| ≤ ε)
    (hwP : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ W : Set ((Fin 2 → Fin 2) → E),
      MeasurableSet W → IsRSymmetric E W → ∀ μ ∈ GZero E (ψ α) ν,
      ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | ∀ i ∈ D, i ∉ latticePattern E W ω} ≤ w α W ^ D.card)
    (hwS : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ (W : Set ((Fin 2 → Fin 2) → E)) (ε : ℝ), 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α,
        w α' W ≤ ENNReal.ofReal (Real.exp (4 * ε)) * w α W)
    (hwT : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      Tendsto (fun ℓ ↦ w α (cubePi 2 E (K ℓ))) atTop (𝓝 0))
    (hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), w α (⋃ m, G m) ≤ t)
    (hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * w α (G n)ᶜ < 1 - t) :
    ∃ Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E)),
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), (Γ α).Nonempty) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
        Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α))
          (μ : Measure ((Fin 2 → ℤ) → E))) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α, ∀ a : Fin 2 → ℤ,
        MeasurePreserving (shift E a).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
      IsCountablyCompact {p : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E |
        p.1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ p.2.toMeasure ∈ Γ p.1} ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
        1 - 4 * crossingBound t
          ≤ (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticeOceanPart E (⋃ m, G m) ω}) ∧
      (∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 → ∀ μ ∈ Γ α,
        ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticePattern E (G n) ω}
          < (μ : Measure ((Fin 2 → ℤ) → E))
            {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}) ∧
      (∀ (τ : CubeTransformation E 2),
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ μ ∈ Γ α,
          MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ) := by
  classical
  have hE : Nonempty E := ν.nonempty_of_neZero
  have hGU : MeasurableSet (⋃ m, G m) := MeasurableSet.iUnion hGmeas
  have hGUsym : IsRSymmetric E (⋃ m, G m) := isRSymmetric_iUnion hGsym
  set Γ : (Fin (N + 1) → ℝ) → Set (ProbabilityMeasure ((Fin 2 → ℤ) → E)) := fun α ↦
    {μ | Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α))
          (μ : Measure ((Fin 2 → ℤ) → E)) ∧
      (∀ a : Fin 2 → ℤ, MeasurePreserving (shift E a).toFun
          (μ : Measure ((Fin 2 → ℤ) → E)) μ) ∧
      (∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | ∀ i ∈ D, i ∉ latticePattern E (⋃ m, G m) ω} ≤ t ^ D.card) ∧
      (∀ (n : Fin (N + 1)) (i : Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | i ∈ latticePattern E (G n) ω} ≤ w α (G n)ᶜ) ∧
      (∀ (ℓ : ℕ) (i : Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | i ∉ latticePattern E (cubePi 2 E (K ℓ)) ω}
            ≤ w α (cubePi 2 E (K ℓ))) ∧
      (∀ τ : CubeTransformation E 2,
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        MeasurePreserving (τ.onLattice E).toFun (μ : Measure ((Fin 2 → ℤ) → E)) μ)} with hΓdef
  -- Georgii: `𝒢₀(Ψ^α) ⊆ Γ(α)`
  have hGZero : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      ∀ μ ∈ GZero E (ψ α) ν, μ ∈ Γ α := by
    intro α hα μ hμ
    refine ⟨mem_GP_of_mem_GZero (hψmeas α) (hψM α) hμ,
      fun a ↦ measurePreserving_shift_of_mem_GZero (hψmeas α) hμ a, fun D ↦ ?_,
      fun n i ↦ ?_, fun ℓ i ↦ ?_, fun τ hτ ↦ ?_⟩
    · refine le_trans (hwP α hα _ hGU hGUsym μ hμ D) ?_
      exact pow_le_pow_left' (hII α hα) D.card
    · have h := hwP α hα _ (hGmeas n).compl (isRSymmetric_compl (hGsym n)) μ hμ {i}
      rwa [setOf_forall_notMem_latticePattern_compl, Finset.card_singleton, pow_one] at h
    · have h := hwP α hα _ (measurableSet_cubePi ((hKconf α).measurableSet ℓ))
        isRSymmetric_cubePi μ hμ {i}
      rw [Finset.card_singleton, pow_one] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext ω
      simp
    · exact (hτ α hα).measurePreserving_onLattice_of_mem_GZero (hψmeas α) (hψM α) hμ
  refine ⟨Γ, fun α hα ↦ ?_, fun α _ μ hμ ↦ hμ.1, fun α _ μ hμ ↦ hμ.2.1, ?_,
    fun α hα μ hμ ↦ ?_, fun α hα n hαn μ hμ ↦ ?_, fun τ hτ α hα μ hμ ↦ hμ.2.2.2.2.2 τ hτ⟩
  · -- non-emptiness, Georgii's `Γ(α) ⊇ 𝒢₀(Ψ^α) ≠ ∅` (Proposition (18.12))
    obtain ⟨μ, hμ⟩ := GZero_nonempty (d := 1) (ν := ν) (hψmeas α) (hψM α).choose_spec
      (hψrefl α) (hKconf α) (fun _ ↦ Classical.arbitrary E)
    exact ⟨μ, hGZero α hα μ hμ⟩
  · -- (i): countable compactness
    rw [isCountablyCompact_iff_seq_clusterPt]
    intro p hp
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hp
    set q : ℕ → (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E :=
      fun k ↦ p (k + k₀) with hqdef
    have hq : ∀ k, (q k).1 ∈ stdSimplex ℝ (Fin (N + 1)) ∧ (q k).2.toMeasure ∈ Γ (q k).1 :=
      fun k ↦ hk₀ (k + k₀) (Nat.le_add_left k₀ k)
    obtain ⟨α, hα, ex, hexmono, hexlim⟩ :=
      (isCompact_stdSimplex ℝ (Fin (N + 1))).tendsto_subseq (fun k ↦ (hq k).1)
    set βs : ℕ → Fin (N + 1) → ℝ := fun j ↦ (q (ex j)).1 with hβsdef
    set ms : ℕ → ProbabilityMeasure ((Fin 2 → ℤ) → E) := fun j ↦ (q (ex j)).2.toMeasure with hmsdef
    have hβlim : Tendsto βs atTop (𝓝 α) := hexlim
    have hmsΓ : ∀ j, ms j ∈ Γ (βs j) := fun j ↦ (hq (ex j)).2
    -- Georgii's condition (I) along the subsequence
    have hβlim' : Tendsto βs atTop (𝓝[stdSimplex ℝ (Fin (N + 1))] α) :=
      tendsto_nhdsWithin_iff.2 ⟨hβlim, Eventually.of_forall fun j ↦ (hq (ex j)).1⟩
    have hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ ζ, |ψ (βs j) ζ - ψ α ζ| ≤ ε :=
      fun ε hε ↦ hβlim'.eventually (hI α hα ε hε)
    have hMα : ∀ ζ, (hψM α).choose ≤ ψ α ζ := (hψM α).choose_spec
    -- the semicontinuity (18.9)(3) along the subsequence
    have hsemi : ∀ (W : Set ((Fin 2 → Fin 2) → E)) (ε : ℝ), 0 < ε → ∀ᶠ j in atTop,
        w (βs j) W ≤ ENNReal.ofReal (Real.exp (4 * ε)) * w α W :=
      fun W ε hε ↦ hβlim'.eventually (hwS α hα W ε hε)
    have : ∀ j, Potential.IsPotential (cubePotential E (ψ (βs j))) :=
      fun j ↦ isPotential_cubePotential (hψmeas _)
    have hadm : ∀ j, Specification.IsPremodifierAdmissible (S := Fin 2 → ℤ) (E := E) ν
        ((cubePotential E (ψ (βs j))).boltzmannFactor 1) := fun j ↦
      (Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible ν _).2
        (isSigmaFiniteLambdaAdmissible_cubePotential (hψmeas _) (hψM (βs j)).choose_spec)
    -- Georgii's Corollary (4.13)
    have hle : LocallyEquicontinuous atTop ms := by
      refine Potential.locallyEquicontinuous_of_confinement_hamiltonian
        (fun j ↦ cubePotential E (ψ (βs j))) ν 1 hadm (fun j ↦ periodicCube 2 j)
        Potential.tendsto_latticeBox_atTop ms ms ?_ K (fun ℓ ↦ (hKconf α).measurableSet ℓ)
        (fun ℓ ↦ (hKconf α).measure_pos ℓ) ?_ ?_
      · intro j
        have hspec : cubeGibbsSpec E (ψ (βs j)) ν (hψmeas _) (hψM (βs j))
            = (Specification.isssd (S := Fin 2 → ℤ) (E := E) ν).modification
              (Specification.premodifierNorm ν
                ((cubePotential E (ψ (βs j))).boltzmannFactor 1))
              (Specification.IsPremodifier.isModifier_premodifierNorm ν
                (Potential.isPremodifier_boltzmannFactor
                  (Φ := cubePotential E (ψ (βs j))) 1) (hadm j)) :=
          Specification.lambdaSpecification_eq_modification_isssd ν
            (Potential.isPremodifier_boltzmannFactor (Φ := cubePotential E (ψ (βs j))) 1)
            (isSigmaFiniteLambdaAdmissible_cubePotential (hψmeas _) (hψM (βs j)).choose_spec)
        rw [← hspec]
        exact (Subtype.ext (Specification.isGibbsMeasure_iff_forall_bind_eq.1
          (hmsΓ j).1 (periodicCube 2 j))).symm
      · -- Georgii's hypothesis (ii)
        intro i
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          (hwT α hα)
          (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun ℓ ↦ ?_)
        refine le_of_forall_exp_mul_le' fun ε hε ↦ ?_
        refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [hsemi (cubePi 2 E (K ℓ)) ε hε] with j hj
        refine le_trans (le_trans (measure_mono ?_) ((hmsΓ j).2.2.2.2.1 ℓ i)) hj
        exact fun ω hω hc ↦ hω (mem_of_mem_latticePattern_cubePi hc)
      · -- Georgii's hypothesis (iii)
        intro Λ
        refine ⟨Λ ∪ (cubeInteractingSet 2 Λ).biUnion id, Finset.subset_union_left, fun ℓ ↦ ?_⟩
        obtain ⟨cα, hcα⟩ := (hKconf α).bddOn ℓ
        refine ⟨(Potential.interactingSupport (Φ := cubePotential E (ψ α)) Λ).card * cα
          + (cubeInteractingSet 2 Λ).card * 1, ?_⟩
        have hpotα : Potential.IsPotential (cubePotential E (ψ α)) :=
          isPotential_cubePotential (hψmeas α)
        filter_upwards [hunif 1 one_pos] with j hj ω hω
        have hωsub : ∀ i ∈ hamSupport (ψ α) Λ, ω i ∈ K ℓ := by
          intro i hi
          refine hω i ?_
          rcases Finset.mem_union.1 hi with h | h
          · exact Finset.mem_union_left _ h
          · obtain ⟨A, hA, hiA⟩ := Finset.mem_biUnion.1 h
            refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨A, ?_, hiA⟩)
            exact interactingSupport_cubePotential_subset (hψmeas α) Λ hA
        have h1 : |(cubePotential E (ψ α)).hamiltonian Λ ω|
            ≤ (Potential.interactingSupport (Φ := cubePotential E (ψ α)) Λ).card * cα := by
          rw [Potential.hamiltonian_eq_interactingHamiltonian]
          exact abs_interactingHamiltonian_cubePotential_le (d := 1) hcα Λ hωsub
        have h2 := abs_hamiltonian_cubePotential_sub_le (hψmeas (βs j)) (hψmeas α) hj Λ ω
        have h3 := abs_sub_abs_le_abs_sub ((cubePotential E (ψ (βs j))).hamiltonian Λ ω)
          ((cubePotential E (ψ α)).hamiltonian Λ ω)
        calc |(cubePotential E (ψ (βs j))).hamiltonian Λ ω|
            ≤ |(cubePotential E (ψ α)).hamiltonian Λ ω|
              + |(cubePotential E (ψ (βs j))).hamiltonian Λ ω
                - (cubePotential E (ψ α)).hamiltonian Λ ω| := by linarith
          _ ≤ _ := by linarith
    obtain ⟨m, hm⟩ := exists_mapClusterPt_of_locallyEquicontinuous
      (μs := fun j ↦ (WithSetwiseTopology.ofMeasure (ms j) : WithLocalConvergence _ E)) hle
    -- the pair `(α, m)` is a cluster point of the original sequence
    have heq : (fun j ↦ ((βs j),
        (WithSetwiseTopology.ofMeasure (ms j) : WithLocalConvergence (Fin 2 → ℤ) E)))
        = q ∘ ex := rfl
    have hpairsub : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
        atTop (q ∘ ex) := heq ▸ hβlim.mapClusterPt_prod hm
    have hpair : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
        atTop p := by
      have h1 : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
          atTop q := MapClusterPt.of_comp hexmono.tendsto_atTop hpairsub
      have h2 : MapClusterPt ((α, m) : (Fin (N + 1) → ℝ) × WithLocalConvergence (Fin 2 → ℤ) E)
          atTop (p ∘ fun k ↦ k + k₀) := h1
      exact MapClusterPt.of_comp (tendsto_add_atTop_nat k₀) h2
    refine ⟨(α, m), ⟨hα, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpair⟩
    · -- the cluster point is a Gibbs measure for `Ψ^α` (Georgii (4.19) and (4.17))
      refine mem_GP_of_mapClusterPt (l := atTop)
        (isQuasilocal_cubeGibbsSpec (hψmeas α) (hψM α))
        (γs := fun j ↦ cubeGibbsSpec E (ψ (βs j)) ν (hψmeas _) (hψM (βs j)))
        (Λs := fun j ↦ periodicCube 2 j) (νs := ms) Potential.tendsto_latticeBox_atTop
        (fun Λ f hf ↦ tendsto_dist_action_cubeGibbsSpec_of_eventually (ν := ν)
          (fun j ↦ hψmeas _) (fun j ↦ hψM (βs j)) (hψmeas α) (hψM α) hunif Λ
          (measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hf))) ?_
      refine hm.congrFun ?_
      filter_upwards with j
      exact congrArg WithSetwiseTopology.ofMeasure
        (Subtype.ext (Specification.isGibbsMeasure_iff_forall_bind_eq.1
          (hmsΓ j).1 (periodicCube 2 j))).symm
    · -- shift invariance
      intro a
      exact measurePreserving_of_mapClusterPt (shift E a).measurable_toFun
        (fun A hA ↦ (shift E a).preimage_mem_localEvents hA) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.1 a)
    · -- the chessboard estimate
      intro D
      exact eval_le_of_mapClusterPt (forall_notMem_latticePattern_mem_localEvents hGU D) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.2.1 D)
    · -- the bound by `t(E^C ∖ G_n, Ψ^α)`
      intro n i
      refine le_of_forall_exp_mul_le' fun ε hε ↦ ?_
      refine eval_le_of_mapClusterPt
        (setOf_mem_latticePattern_mem_localEvents (hGmeas n) i) hm ?_
      filter_upwards [hsemi (G n)ᶜ ε hε] with j hj
      exact le_trans ((hmsΓ j).2.2.2.1 n i) hj
    · -- the bound by `t(K_ℓ^C, Ψ^α)`
      intro ℓ i
      refine le_of_forall_exp_mul_le' fun ε hε ↦ ?_
      refine eval_le_of_mapClusterPt
        (setOf_notMem_latticePattern_mem_localEvents
          (measurableSet_cubePi ((hKconf α).measurableSet ℓ)) i) hm ?_
      filter_upwards [hsemi (cubePi 2 E (K ℓ)) ε hε] with j hj
      exact le_trans ((hmsΓ j).2.2.2.2.1 ℓ i) hj
    · -- the common symmetries
      intro τ hτ
      exact measurePreserving_of_mapClusterPt (τ.onLattice E).measurable_toFun
        (fun A hA ↦ (τ.onLattice E).preimage_mem_localEvents hA) hm
        (Eventually.of_forall fun j ↦ (hmsΓ j).2.2.2.2.2 τ hτ)
  · -- (ii): Theorem (18.17) from the chessboard estimate
    exact le_measure_mem_latticeOceanPart_of_forall_le_pow (ν := ν) hGU hGUsym
      (isQuasiGibbsianWith_of_isGibbsMeasure_cubeGibbsSpec (hψmeas α) (hψM α) hμ.1)
      hμ.2.1 hμ.2.2.1
  · -- (iii): condition (III)
    have h1 : (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        ≤ w α (G n)ᶜ := hμ.2.2.2.1 n 0
    have h2 : (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}ᶜ ≤ t := by
      have h := hμ.2.2.1 {(0 : Fin 2 → ℤ)}
      rw [Finset.card_singleton, pow_one] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ext ω
      simp
    have h3 : 1 - t ≤ (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω} := by
      rw [tsub_le_iff_right]
      calc (1 : ℝ≥0∞)
          = (μ : Measure ((Fin 2 → ℤ) → E)) {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}
            + (μ : Measure ((Fin 2 → ℤ) → E))
              {ω | (0 : Site) ∈ latticePattern E (⋃ m, G m) ω}ᶜ := by
            rw [measure_add_measure_compl
              (measurableSet_setOf_mem_latticePattern hGU 0), measure_univ]
        _ ≤ _ := by gcongr
    calc ((N : ℝ≥0∞) + 1) * (μ : Measure ((Fin 2 → ℤ) → E))
          {ω | (0 : Site) ∈ latticePattern E (G n) ω}
        ≤ ((N : ℝ≥0∞) + 1) * w α (G n)ᶜ := by gcongr
      _ < 1 - t := hIII α hα n hαn
      _ ≤ _ := h3

/-- **Georgii, Propositions (19.13) and (19.14) together, for an arbitrary Peierls weight.**
Under Georgii's conditions (I), (II) and (III) on a family `(Ψ^α)_{α ∈ 𝒫_N}` of `C`-potentials
over a standard Borel state space, together with his `4(N+1) z(t) < 1`, there is a parameter
`α*` for which `Ψ^{α*}` has `N + 1` mutually singular shift-invariant Gibbs measures
`μ_0, …, μ_N`, the `n`-th living on the event that the pattern `G_n` percolates and giving the
origin's membership of that ocean probability at least `1 - 4(N+1) z(t)`; and `μ_n` is
invariant under every common symmetry of the family that fixes `G_n`.

Intended home: `GibbsMeasure/Model/SpernerPhaseTransition.lean`, in place of
`exists_gibbsMeasure_family_of_patternWeight_le`. -/
theorem exists_gibbsMeasure_family_of_weight_le
    {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n))
    (hψmeas : ∀ α, Measurable (ψ α)) (hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψ α ζ)
    (hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψ α (cubeRefl E k ζ) = ψ α ζ)
    (hKconf : ∀ α, IsCubeConfining (ψ α) ν K)
    (hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψ α' ζ - ψ α ζ| ≤ ε)
    (hwP : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ W : Set ((Fin 2 → Fin 2) → E),
      MeasurableSet W → IsRSymmetric E W → ∀ μ ∈ GZero E (ψ α) ν,
      ∀ D : Finset (Fin 2 → ℤ), (μ : Measure ((Fin 2 → ℤ) → E))
        {ω | ∀ i ∈ D, i ∉ latticePattern E W ω} ≤ w α W ^ D.card)
    (hwS : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ (W : Set ((Fin 2 → Fin 2) → E)) (ε : ℝ), 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α,
        w α' W ≤ ENNReal.ofReal (Real.exp (4 * ε)) * w α W)
    (hwT : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      Tendsto (fun ℓ ↦ w α (cubePi 2 E (K ℓ))) atTop (𝓝 0))
    (hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), w α (⋃ m, G m) ≤ t)
    (hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * w α (G n)ᶜ < 1 - t)
    (hz : ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) < 1) :
    ∃ α ∈ stdSimplex ℝ (Fin (N + 1)), ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α)) (ρ n)) ∧
      (∀ (n : Fin (N + 1)) (a : Fin 2 → ℤ),
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - ((N : ℝ≥0∞) + 1) * (4 * crossingBound t)
        ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        τ.onCube.toFun '' G n = G n →
        MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) := by
  obtain ⟨Γ, hΓne, hΓgibbs, hΓshift, hcc, hii, hiii, hτ⟩ :=
    exists_correspondence_of_weight_le hGmeas hGsym hψmeas hψM hψrefl hKconf hI hwP hwS hwT
      hII hIII
  have hK0 : ((N : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hKtop : ((N : ℝ≥0∞) + 1) ≠ ∞ := by simp
  have hc : 4 * crossingBound t < ((N : ℝ≥0∞) + 1)⁻¹ := by
    by_contra hcon
    rw [not_lt] at hcon
    have h2 : ((N : ℝ≥0∞) + 1) * ((N : ℝ≥0∞) + 1)⁻¹
        ≤ ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) := mul_le_mul' le_rfl hcon
    rw [ENNReal.mul_inv_cancel hK0 hKtop] at h2
    exact absurd hz (not_lt.2 h2)
  obtain ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_gibbsMeasure_family_of_isCountablyCompact (γ := fun α ↦
      cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α)) hpart hGmeas hGsym hΓne hΓgibbs hΓshift hcc
      hc hii hiii
  exact ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7,
    fun n τ hτsym hGτ ↦ h8 n τ (fun β hβ μ hμ ↦ hτ τ hτsym β hβ μ hμ) hGτ⟩

end Weight

/-! ### Georgii, Propositions (19.13) and (19.14) with the rectangle weight of (18.11) -/

section RectWeight

open Peierls

variable [StandardBorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν] {N : ℕ}
  {G : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {ψ : (Fin (N + 1) → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ} {K : ℕ → Set E} {t : ℝ≥0∞}

/-- **Georgii, Propositions (19.13) and (19.14), with the rectangle weight `t̃(G, Φ)` of
Comment (18.11) in place of `t(G, Φ)`** — which is how the proof of Theorem (19.16) uses them.

The weight fed to `exists_gibbsMeasure_family_of_weight_le` is `t(·, Ψ^α) ⊓ t̃(·, Ψ^α)`: the
chessboard estimate (18.10) and Comment (18.11) both hold, so their minimum is a Peierls
weight; Remark (18.9)(3) holds for both with the constants `e^{4ε}` and `e^{2ε}`; and the
confinement bound `w(K_ℓ^C) → 0` comes from the `t`-half, so no rectangle has to be exhibited
inside `K_ℓ^C`.  Conditions (II) and (III) are then required only of the `t̃`-half.

Intended home: `GibbsMeasure/Model/SpernerPhaseTransition.lean`. -/
theorem exists_gibbsMeasure_family_of_rectPatternWeight_le
    {φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} (hpart : IsPStablePartition φ₀ ν Set.univ G)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hGsym : ∀ n, IsRSymmetric E (G n))
    (hψmeas : ∀ α, Measurable (ψ α)) (hψM : ∀ α, ∃ M : ℝ, ∀ ζ, M ≤ ψ α ζ)
    (hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ, ψ α (cubeRefl E k ζ) = ψ α ζ)
    (hKconf : ∀ α, IsCubeConfining (ψ α) ν K)
    (hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ, |ψ α' ζ - ψ α ζ| ≤ ε)
    (hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), rectPatternWeight (ψ α) ν (⋃ m, G m) ≤ t)
    (hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1) * rectPatternWeight (ψ α) ν (G n)ᶜ < 1 - t)
    (hz : ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) < 1) :
    ∃ α ∈ stdSimplex ℝ (Fin (N + 1)), ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
      (∀ n, IsProbabilityMeasure (ρ n)) ∧
      (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec E (ψ α) ν (hψmeas α) (hψM α)) (ρ n)) ∧
      (∀ (n : Fin (N + 1)) (a : Fin 2 → ℤ),
        MeasurePreserving (shift E a).toFun (ρ n) (ρ n)) ∧
      (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
      (∀ n, ρ n {ω | (latticeOceanPart E (G n) ω).Nonempty} = 1) ∧
      (∀ n, 1 - ((N : ℝ≥0∞) + 1) * (4 * crossingBound t)
        ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (G n) ω}) ∧
      (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
        (∀ α' ∈ stdSimplex ℝ (Fin (N + 1)), τ.IsSymmetry (ψ α') ν) →
        τ.onCube.toFun '' G n = G n →
        MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) := by
  refine exists_gibbsMeasure_family_of_weight_le
    (w := fun α W ↦ patternWeight (ψ α) ν W ⊓ rectPatternWeight (ψ α) ν W)
    hpart hGmeas hGsym hψmeas hψM hψrefl
    hKconf hI (fun α hα W hW hWsym μ hμ D ↦ ?_) (fun α hα W ε hε ↦ ?_) (fun α hα ↦ ?_)
    (fun α hα ↦ le_trans inf_le_right (hII α hα))
    (fun α hα n hαn ↦ lt_of_le_of_lt (by gcongr; exact inf_le_right) (hIII α hα n hαn)) hz
  · -- the chessboard estimate (18.10) and Comment (18.11)
    show (μ : Measure ((Fin 2 → ℤ) → E)) {ω | ∀ i ∈ D, i ∉ latticePattern E W ω}
      ≤ (patternWeight (ψ α) ν W ⊓ rectPatternWeight (ψ α) ν W) ^ D.card
    have h1 := forall_notMem_latticePattern_le_patternWeight (d := 1) (hψmeas α)
      (hψM α).choose_spec (hψrefl α) hW hWsym hμ D
    have h2 := forall_notMem_latticePattern_le_rectPatternWeight (d := 1) (hψmeas α)
      (hψM α).choose_spec (hψrefl α) hW hWsym hμ D
    rcases le_total (patternWeight (ψ α) ν W) (rectPatternWeight (ψ α) ν W) with h | h
    · rwa [inf_eq_left.2 h]
    · rwa [inf_eq_right.2 h]
  · -- Remark (18.9)(3) for both weights
    filter_upwards [hI α hα ε hε] with α' hα'
    show patternWeight (ψ α') ν W ⊓ rectPatternWeight (ψ α') ν W
      ≤ ENNReal.ofReal (Real.exp (4 * ε))
        * (patternWeight (ψ α) ν W ⊓ rectPatternWeight (ψ α) ν W)
    have hMα : ∀ ζ, (hψM α).choose ≤ ψ α ζ := (hψM α).choose_spec
    have h1 : patternWeight (ψ α') ν W
        ≤ ENNReal.ofReal (Real.exp (4 * ε)) * patternWeight (ψ α) ν W :=
      patternWeight_le_of_abs_sub_le hMα hε.le hα' W
    have h2 : rectPatternWeight (ψ α') ν W
        ≤ ENNReal.ofReal (Real.exp (4 * ε)) * rectPatternWeight (ψ α) ν W := by
      refine le_trans (rectPatternWeight_le_of_abs_sub_le hMα hα' W)
        (mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl)
      linarith
    rcases le_total (patternWeight (ψ α) ν W) (rectPatternWeight (ψ α) ν W) with h | h
    · rw [inf_eq_left.2 h]
      exact le_trans inf_le_left h1
    · rw [inf_eq_right.2 h]
      exact le_trans inf_le_right h2
  · -- the confinement bound of (18.12), from the `t`-half
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_patternWeight_cubePi (hψM α).choose_spec (hKconf α))
      (Eventually.of_forall fun _ ↦ zero_le) (Eventually.of_forall fun ℓ ↦ inf_le_left)

end RectWeight

/-! ### Georgii (19.16), Step 3: the map from the simplex to `(β, h)` -/

section Parametrisation

variable {N : ℕ} [NeZero N] {β₀ β₁ : ℝ} {α : Fin (N + 1) → ℝ}

variable (β₀ β₁) in
/-- **Georgii's `β(α)`** of Step 3 of the proof of Theorem (19.16):
`β(α) = β₀ + (β₁ - β₀) α(0) / max_{0 ≤ k ≤ N} α(k)`.  It equals `β₀` where `α(0) = 0` and
`β₁` where `α(0)` is the strict maximum, and it takes values in `[β₀, β₁]`. -/
def wellTemperature (α : Fin (N + 1) → ℝ) : ℝ :=
  β₀ + (β₁ - β₀) * α 0 / Finset.univ.sup' Finset.univ_nonempty α

variable (β₁) in
/-- **Georgii's `h(α)`** of Step 3 of the proof of Theorem (19.16):
`h_n(α) = β₁ (max_{1 ≤ k ≤ N} α(k) - α(n)) / max_{0 ≤ k ≤ N} α(k)` for `1 ≤ n ≤ N`.  It takes
values in `∂ℝ_+^N ∩ [0, β₁]^N`, and equals `β₁` at a coordinate `n` with `α(n) = 0` unless
`α(0)` is the strict maximum — in which case `β(α) = β₁` instead. -/
def wellField (α : Fin (N + 1) → ℝ) (n : Fin N) : ℝ :=
  β₁ * (Finset.univ.sup' Finset.univ_nonempty (fun k : Fin N ↦ α k.succ) - α n.succ)
    / Finset.univ.sup' Finset.univ_nonempty α

/-- The maximum over the last `N` coordinates is at most the maximum over all of them. -/
lemma sup'_succ_le_sup' :
    Finset.univ.sup' Finset.univ_nonempty (fun k : Fin N ↦ α k.succ)
      ≤ Finset.univ.sup' Finset.univ_nonempty α :=
  Finset.sup'_le _ _ fun k _ ↦ le_sup'_apply k.succ

/-- The maximum over all coordinates is either `α(0)` or the maximum over the last `N`. -/
lemma sup'_eq_zero_or_sup'_succ :
    Finset.univ.sup' Finset.univ_nonempty α = α 0 ∨
      Finset.univ.sup' Finset.univ_nonempty α
        = Finset.univ.sup' Finset.univ_nonempty (fun k : Fin N ↦ α k.succ) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (N + 1))) α
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j, rfl⟩
  · exact Or.inl hk
  · exact Or.inr (le_antisymm
      (hk.le.trans (Finset.le_sup' (fun k : Fin N ↦ α k.succ) (Finset.mem_univ j)))
      sup'_succ_le_sup')

omit [NeZero N] in
lemma wellTemperature_mem_Icc (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (h01 : β₀ ≤ β₁) :
    wellTemperature β₀ β₁ α ∈ Set.Icc β₀ β₁ := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  have h0 : 0 ≤ α 0 / Finset.univ.sup' Finset.univ_nonempty α :=
    div_nonneg (hα.1 0) hs.le
  have h1 : α 0 / Finset.univ.sup' Finset.univ_nonempty α ≤ 1 :=
    (div_le_one hs).2 (le_sup'_apply 0)
  constructor
  · simp only [wellTemperature, mul_div_assoc]
    nlinarith
  · simp only [wellTemperature, mul_div_assoc]
    nlinarith

omit [NeZero N] in
/-- **Georgii's (i)**: `β(α) = β₀` when `α(0) = 0`. -/
lemma wellTemperature_of_apply_zero (h : α 0 = 0) : wellTemperature β₀ β₁ α = β₀ := by
  simp [wellTemperature, h]

lemma wellField_nonneg (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (hβ₁ : 0 ≤ β₁) (n : Fin N) :
    0 ≤ wellField β₁ α n := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  refine div_nonneg (mul_nonneg hβ₁ (sub_nonneg.2 ?_)) hs.le
  exact Finset.le_sup' (fun k : Fin N ↦ α k.succ) (Finset.mem_univ n)

lemma wellField_le (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (hβ₁ : 0 ≤ β₁) (n : Fin N) :
    wellField β₁ α n ≤ β₁ := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  rw [wellField, div_le_iff₀ hs]
  have h1 : Finset.univ.sup' Finset.univ_nonempty (fun k : Fin N ↦ α k.succ) - α n.succ
      ≤ Finset.univ.sup' Finset.univ_nonempty α := by
    have := sup'_succ_le_sup' (α := α)
    have := hα.1 n.succ
    linarith
  nlinarith

/-- **Georgii's `h(α) ∈ ∂ℝ_+^N`**: `h(α)` vanishes at a coordinate where `α` is largest among
`α(1), …, α(N)`. -/
lemma wellField_mem_nonnegBoundary (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) (hβ₁ : 0 ≤ β₁) :
    wellField β₁ α ∈ nonnegBoundary (Fin N) := by
  refine ⟨wellField_nonneg hα hβ₁, ?_⟩
  obtain ⟨n, -, hn⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin N)) (fun k : Fin N ↦ α k.succ)
  exact ⟨n, by simp [wellField, ← hn]⟩

/-- **Georgii's (ii)**: `β(α) ∨ h_n(α) = β₁` when `α(n) = 0`, `1 ≤ n ≤ N`. -/
lemma wellTemperature_eq_or_wellField_eq (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) {n : Fin N}
    (hn : α n.succ = 0) :
    wellTemperature β₀ β₁ α = β₁ ∨ wellField β₁ α n = β₁ := by
  have hs := sup'_pos_of_mem_stdSimplex hα
  rcases sup'_eq_zero_or_sup'_succ (α := α) with h | h
  · refine Or.inl ?_
    rw [wellTemperature, ← h, mul_div_assoc, div_self hs.ne', mul_one]
    ring
  · refine Or.inr ?_
    rw [wellField, hn, sub_zero, ← h, mul_div_assoc, div_self hs.ne', mul_one]

omit [NeZero N] in
lemma continuousAt_wellTemperature (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) :
    ContinuousAt (wellTemperature β₀ β₁) α := by
  have hs : Continuous fun β : Fin (N + 1) → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty β :=
    Continuous.finset_sup'_apply _ fun i _ ↦ continuous_apply i
  exact continuousAt_const.add
    ((continuousAt_const.mul (continuous_apply 0).continuousAt).div hs.continuousAt
      (sup'_pos_of_mem_stdSimplex hα).ne')

lemma continuousAt_wellField (hα : α ∈ stdSimplex ℝ (Fin (N + 1))) :
    ContinuousAt (wellField β₁) α := by
  have hs : Continuous fun β : Fin (N + 1) → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty β :=
    Continuous.finset_sup'_apply _ fun i _ ↦ continuous_apply i
  have hs1 : Continuous fun β : Fin (N + 1) → ℝ ↦
      Finset.univ.sup' Finset.univ_nonempty (fun k : Fin N ↦ β k.succ) :=
    Continuous.finset_sup'_apply _ fun i _ ↦ continuous_apply i.succ
  refine continuousAt_pi.2 fun n ↦ ?_
  exact (continuousAt_const.mul (hs1.continuousAt.sub (continuous_apply n.succ).continuousAt)).div
    hs.continuousAt (sup'_pos_of_mem_stdSimplex hα).ne'

end Parametrisation

/-! ### Georgii, assumption (A) of §19.3.1 -/

section CompetingWells

variable {N : ℕ} [NeZero N] {Φ : (Fin N → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ}
  {ν : Measure E} [IsProbabilityMeasure ν]
  {W : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {V : Fin (N + 1) → (Fin 2 → Fin 2) → Set E} {a b c δ : ℝ}

variable (Φ ν W V a b c δ) in
/-- **Georgii, assumption (A) of §19.3.1.**  The cube interactions `Φ^h_C`, `h ∈ ∂ℝ_+^N`, form
`N + 1` wells `W_0, …, W_N`, one of which (`W_0`) is deeper than the others; each `W_n`
contains a rectangle `V_n` of positive `λ^C`-measure on which `Φ^h_C` is essentially bounded
just above the bottom of the well.

* **(A1) Shape of the wells.**  `λ-inf_{W_0} Φ^h_C = 0`, `λ-inf_{W_n} Φ^h_C = a + h_n`
  (`1 ≤ n ≤ N`), `λ-sup_{V_0} Φ^h_C ≤ δ` and `λ-sup_{V_n} Φ^h_C ≤ a + h_n + c`.
* **(A2) Barrier between the wells.**  `λ-inf_{E^C ∖ W} Φ^h_C ≥ b`, where
  `W = W_0 ∪ ⋯ ∪ W_N`.
* **(A3) Stability of the wells.**  For each face `F` of `C` the projections `σ_F(W_n)` are
  pairwise disjoint — Georgii's condition (18.23)(a)(ii).

Georgii's `λ-inf` and `λ-sup` are essential infima and suprema relative to `λ^C`, so (A1),
(A2) are `λ^C`-almost everywhere statements; they are recorded here in that form, and only the
inequalities `λ-inf ≥` are kept, since the reverse inequalities in (A1) are not used.  The
constants satisfy `0 < a < b`, `0 < c` and `0 < δ < a`.

Of the constraints on the constants, Theorem (19.16) uses only `δ < a` — the interior `V_0` of
the deep well lies strictly below the bottoms of the others — together with `a + c < b`, which
its condition (19.17) already forces; `0 < a`, `a < b`, `0 < c` and `0 < δ` are kept because
they are part of Georgii's assumption (A) and of what makes the picture a family of wells
(they are, for instance, what gives `G_ε(Φ^h) ⊆ W_0` for `0 < ε < a`). -/
structure IsCompetingWells : Prop where
  /-- The wells are measurable. -/
  measurableSet : ∀ n, MeasurableSet (W n)
  /-- The wells are `r`-symmetric. -/
  isRSymmetric : ∀ n, IsRSymmetric E (W n)
  /-- `V_n ⊆ W_n`. -/
  pi_subset : ∀ n, Set.univ.pi (V n) ⊆ W n
  /-- `λ^C(V_n) > 0`. -/
  measure_pi_pos : ∀ n, 0 < cubeMeasure 2 ν (Set.univ.pi (V n))
  /-- `0 < a`. -/
  a_pos : 0 < a
  /-- `a < b`. -/
  a_lt_b : a < b
  /-- `0 < c`. -/
  c_pos : 0 < c
  /-- `0 < δ`. -/
  delta_pos : 0 < δ
  /-- `δ < a`. -/
  delta_lt_a : δ < a
  /-- (A1), `λ-inf_{W_0} Φ^h_C ≥ 0`. -/
  zero_le_on_well_zero : ∀ h ∈ nonnegBoundary (Fin N),
    ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (W 0)), 0 ≤ Φ h ζ
  /-- (A1), `λ-inf_{W_n} Φ^h_C ≥ a + h_n`. -/
  le_on_well_succ : ∀ h ∈ nonnegBoundary (Fin N), ∀ n : Fin N,
    ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (W n.succ)), a + h n ≤ Φ h ζ
  /-- (A1), `λ-sup_{V_0} Φ^h_C ≤ δ`. -/
  le_delta_on_rect_zero : ∀ h ∈ nonnegBoundary (Fin N),
    ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (Set.univ.pi (V 0))), Φ h ζ ≤ δ
  /-- (A1), `λ-sup_{V_n} Φ^h_C ≤ a + h_n + c`. -/
  le_on_rect_succ : ∀ h ∈ nonnegBoundary (Fin N), ∀ n : Fin N,
    ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (Set.univ.pi (V n.succ))), Φ h ζ ≤ a + h n + c
  /-- (A2), `λ-inf_{E^C ∖ W} Φ^h_C ≥ b`. -/
  barrier : ∀ h ∈ nonnegBoundary (Fin N),
    ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (⋃ n, W n)ᶜ), b ≤ Φ h ζ
  /-- (A3), Georgii's (18.23)(a)(ii). -/
  pairwise_disjoint_faceRestrict : ∀ (k : Fin 2) (i : Fin 2),
    Pairwise fun m n ↦ Disjoint (faceRestrict E k i '' W m) (faceRestrict E k i '' W n)

omit [NeZero N] [IsProbabilityMeasure ν] in
lemma IsCompetingWells.measure_iUnion_pos (hA : IsCompetingWells Φ ν W V a b c δ) :
    0 < cubeMeasure 2 ν (⋃ n, W n) :=
  lt_of_lt_of_le (hA.measure_pi_pos 0)
    (measure_mono ((hA.pi_subset 0).trans (Set.subset_iUnion W 0)))

omit [NeZero N] in
/-- **The wells are a stable partition (18.23)(a).**  Assumption (A3) is (18.23)(a)(ii)
verbatim; (18.23)(a)(i) — that the local `ε`-ground states of a potential are contained in the
union of the members — is certified here by the indicator of `E^C ∖ ⋃_n W_n`, whose local
`ε`-ground states are exactly `⋃_n W_n` for `0 < ε < 1`.

Georgii instead appeals to his remark that (A) implies `G_ε(Φ^h) ⊆ W_0` for `0 < ε < a`; since
his `λ-inf` is an *essential* infimum, that inclusion holds only up to a `λ^C`-null set, while
(18.23)(a)(i) is a genuine inclusion.  Proposition (19.13) leaves the potential of the stable
partition free — it enters only through the disjointness of the percolation events — so the
indicator does the job with no loss. -/
theorem isPStablePartition_of_isCompetingWells (hA : IsCompetingWells Φ ν W V a b c δ) :
    IsPStablePartition ((⋃ n, W n)ᶜ.indicator fun _ ↦ (1 : ℝ)) ν Set.univ W where
  exists_localGroundStates_subset := by
    set φ₀ : ((Fin 2 → Fin 2) → E) → ℝ := (⋃ n, W n)ᶜ.indicator fun _ ↦ (1 : ℝ) with hφ₀
    have hnonneg : ∀ ζ, (0 : ℝ) ≤ φ₀ ζ :=
      fun ζ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) ζ
    have hval : ∀ ζ, ζ ∈ ⋃ n, W n → φ₀ ζ = 0 := by
      intro ζ hζ
      rw [hφ₀, Set.indicator_of_notMem (by simpa using hζ)]
    have hval' : ∀ ζ, ζ ∉ ⋃ n, W n → φ₀ ζ = 1 := by
      intro ζ hζ
      rw [hφ₀, Set.indicator_of_mem hζ]
    -- the sublevel sets of `φ₀`
    have hset : {c : ℝ | cubeMeasure 2 ν {ζ | φ₀ ζ ≤ c} = 0} = Set.Iio 0 := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_Iio]
      constructor
      · intro hr
        by_contra hcon
        rw [not_lt] at hcon
        refine absurd hr (ne_of_gt (lt_of_lt_of_le hA.measure_iUnion_pos (measure_mono ?_)))
        exact fun ζ hζ ↦ by simpa [hval ζ hζ] using hcon
      · intro hr
        convert measure_empty (μ := cubeMeasure 2 ν)
        exact Set.eq_empty_of_forall_notMem fun ζ hζ ↦
          absurd (le_trans (hnonneg ζ) hζ) (not_le.2 hr)
    have hE0 : localGroundEnergy φ₀ ν = 0 := by
      rw [localGroundEnergy_eq_sSup (M := 0) hnonneg, hset]
      exact csSup_Iio
    refine ⟨1 / 2, by norm_num, fun ζ hζ ↦ ?_⟩
    by_contra hcon
    rw [mem_localGroundStates, hE0, zero_add, hval' ζ hcon] at hζ
    norm_num at hζ
  pairwise_disjoint_faceRestrict := fun k _ i ↦ hA.pairwise_disjoint_faceRestrict k i

end CompetingWells

/-! ### Georgii (19.16), Steps 1 and 2: the estimates of `t̃` under assumption (A) -/

section Estimates

variable {N : ℕ} [NeZero N] {Φ : (Fin N → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ}
  {ν : Measure E} [IsProbabilityMeasure ν]
  {W : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {V : Fin (N + 1) → (Fin 2 → Fin 2) → Set E} {a b c δ : ℝ}

/-- The infimum of a family indexed by a finite non-empty type is attained.

Intended home: Mathlib, next to `Finite.exists_min`. -/
lemma exists_iInf_eq {ι : Type*} {α : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    (f : ι → α) : ∃ i, ⨅ j, f j = f i := by
  obtain ⟨i, hi⟩ := Finite.exists_min f
  exact ⟨i, le_antisymm (iInf_le f i) (le_iInf hi)⟩

/-- Georgii's `min_{1 ≤ n ≤ N} λ^C(V_n)^{1/|C|}` is positive. -/
lemma IsCompetingWells.iInf_rect_pos (hA : IsCompetingWells Φ ν W V a b c δ) :
    0 < ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹) := by
  obtain ⟨n, hn⟩ :=
    exists_iInf_eq fun n : Fin N ↦ cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹)
  rw [hn]
  exact ENNReal.rpow_pos (hA.measure_pi_pos n.succ) (measure_ne_top _ _)

variable (ν V) in
/-- Georgii's `min_{1 ≤ n ≤ N} λ^C(V_n)^{1/|C|}` is at most `1`, hence finite: `λ^C` is a
probability measure. -/
lemma iInf_rect_le_one :
    (⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹)) ≤ 1 :=
  le_trans (iInf_le _ (Classical.arbitrary (Fin N)))
    (ENNReal.rpow_le_one prob_le_one (by positivity))

omit [NeZero N] in
/-- **Georgii's Step 2, first display**: for `β > 0` and `h ∈ ∂ℝ_+^N`,
`t̃(W, βΦ^h) ≤ e^{-β(b - a - c)} / min_{1 ≤ n ≤ N} λ^C(V_n)^{1/|C|}`.

The barrier (A2) supplies the exponent `-βb` of the first factor of `t̃`, and the well `V_n` at
a coordinate where `h` vanishes — such a coordinate exists because `h ∈ ∂ℝ_+^N` — supplies the
rectangle: `λ-sup_{V_n} βΦ^h_C ≤ β(a + c)`. -/
theorem IsCompetingWells.rectPatternWeight_iUnion_le (hA : IsCompetingWells Φ ν W V a b c δ)
    {h : Fin N → ℝ} (hh : h ∈ nonnegBoundary (Fin N)) {β : ℝ} (hβ : 0 < β) :
    rectPatternWeight (fun ζ ↦ β * Φ h ζ) ν (⋃ n, W n)
      ≤ ENNReal.ofReal (Real.exp (-(β * (b - a - c))))
        / ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹) := by
  obtain ⟨n₀, hn₀⟩ := hh.2
  have hA1 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (⋃ n, W n)ᶜ), β * b ≤ β * Φ h ζ := by
    filter_upwards [hA.barrier h hh] with ζ hζ
    exact mul_le_mul_of_nonneg_left hζ hβ.le
  have hA2 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (Set.univ.pi (V n₀.succ))),
      β * Φ h ζ ≤ β * (a + c) := by
    filter_upwards [hA.le_on_rect_succ h hh n₀] with ζ hζ
    rw [hn₀, add_zero] at hζ
    exact mul_le_mul_of_nonneg_left hζ hβ.le
  refine le_trans (rectPatternWeight_le_of_ae_le hA1 hA2) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul' ?_ (ENNReal.inv_le_inv.2 (iInf_le _ n₀))
  rw [show β * (a + c) - β * b = -(β * (b - a - c)) by ring]
  exact le_of_le_of_eq
    (mul_le_mul' le_rfl (ENNReal.rpow_le_one prob_le_one (by positivity))) (mul_one _)

omit [NeZero N] [IsProbabilityMeasure ν] in
/-- **Georgii's Step 2, second display**: for `β > 0` and `h ∈ ∂ℝ_+^N`,
`t̃(E^C ∖ W_0, βΦ^h) ≤ e^{β(a+c)} λ^C(W_0)^{1/|C|} / min_{1 ≤ n ≤ N} λ^C(V_n)^{1/|C|}`.

Here `λ-inf_{W_0} βΦ^h_C ≥ 0` — the deep well costs nothing — so the whole of the estimate is
carried by the *thinness* `λ^C(W_0)^{1/|C|}` of `W_0`. -/
theorem IsCompetingWells.rectPatternWeight_compl_zero_le
    (hA : IsCompetingWells Φ ν W V a b c δ) {h : Fin N → ℝ} (hh : h ∈ nonnegBoundary (Fin N))
    {β : ℝ} (hβ : 0 < β) :
    rectPatternWeight (fun ζ ↦ β * Φ h ζ) ν (W 0)ᶜ
      ≤ ENNReal.ofReal (Real.exp (β * (a + c))) * cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹)
        / ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹) := by
  obtain ⟨n₀, hn₀⟩ := hh.2
  have hA1 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (W 0)ᶜᶜ), (0 : ℝ) ≤ β * Φ h ζ := by
    rw [compl_compl]
    filter_upwards [hA.zero_le_on_well_zero h hh] with ζ hζ
    exact mul_nonneg hβ.le hζ
  have hA2 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (Set.univ.pi (V n₀.succ))),
      β * Φ h ζ ≤ β * (a + c) := by
    filter_upwards [hA.le_on_rect_succ h hh n₀] with ζ hζ
    rw [hn₀, add_zero] at hζ
    exact mul_le_mul_of_nonneg_left hζ hβ.le
  refine le_trans (rectPatternWeight_le_of_ae_le hA1 hA2) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, compl_compl, sub_zero]
  exact mul_le_mul' le_rfl (ENNReal.inv_le_inv.2 (iInf_le _ n₀))

omit [NeZero N] in
/-- **Georgii's Step 2, third display**: for `β > 0`, `h ∈ ∂ℝ_+^N` and `1 ≤ n ≤ N`,
`t̃(E^C ∖ W_n, βΦ^h) ≤ e^{-β(a + h_n - δ)} / λ^C(V_0)^{1/|C|}`.

The depth `a + h_n` of the `n`-th well and the shallow rectangle `V_0` in the deep well, on
which `λ-sup βΦ^h_C ≤ βδ`, give the exponent `-β(a + h_n - δ)`, which is negative because
`δ < a`. -/
theorem IsCompetingWells.rectPatternWeight_compl_succ_le
    (hA : IsCompetingWells Φ ν W V a b c δ) {h : Fin N → ℝ} (hh : h ∈ nonnegBoundary (Fin N))
    {β : ℝ} (hβ : 0 < β) (n : Fin N) :
    rectPatternWeight (fun ζ ↦ β * Φ h ζ) ν (W n.succ)ᶜ
      ≤ ENNReal.ofReal (Real.exp (-(β * (a + h n - δ))))
        / cubeMeasure 2 ν (Set.univ.pi (V 0)) ^ ((2 ^ 2 : ℝ)⁻¹) := by
  have hA1 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (W n.succ)ᶜᶜ), β * (a + h n) ≤ β * Φ h ζ := by
    rw [compl_compl]
    filter_upwards [hA.le_on_well_succ h hh n] with ζ hζ
    exact mul_le_mul_of_nonneg_left hζ hβ.le
  have hA2 : ∀ᵐ ζ ∂((cubeMeasure 2 ν).restrict (Set.univ.pi (V 0))), β * Φ h ζ ≤ β * δ := by
    filter_upwards [hA.le_delta_on_rect_zero h hh] with ζ hζ
    exact mul_le_mul_of_nonneg_left hζ hβ.le
  refine le_trans (rectPatternWeight_le_of_ae_le hA1 hA2) ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, compl_compl,
    show β * δ - β * (a + h n) = -(β * (a + h n - δ)) by ring]
  exact mul_le_mul' (le_of_le_of_eq
    (mul_le_mul' le_rfl (ENNReal.rpow_le_one prob_le_one (by positivity))) (mul_one _)) le_rfl

end Estimates


/-! ### Georgii, Theorem (19.16) -/

section Theorem1916

open Peierls

variable [StandardBorelSpace E] {N : ℕ} [NeZero N]
  {Φ : (Fin N → ℝ) → ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {W : Fin (N + 1) → Set ((Fin 2 → Fin 2) → E)}
  {V : Fin (N + 1) → (Fin 2 → Fin 2) → Set E} {a b c δ : ℝ} {t : ℝ≥0∞} {β₀ : ℝ}

/-- **Georgii, Theorem (19.16).**  Let `(E, ℰ)` be standard Borel with a finite a priori
measure, here normalised to a probability measure `λ`, and let `(Φ^h)_{h ∈ ∂ℝ_+^N}` be a family
of bounded `C`-potentials on `ℤ^2` depending continuously on `h` in the sup-norm.  Suppose the
wells `W_0, …, W_N` and the rectangles `V_0, …, V_N` satisfy Georgii's assumption (A), suppose
`4(N+1) z(t) < 1`, and suppose `b` is large enough and `λ^C(W_0)` small enough that (19.17) and
(19.18) hold at the fixed `β₀ > 0`.

Then there are a parameter `h* ∈ ∂ℝ_+^N` and an inverse temperature `β* ∈ [β₀, β₁]` — so in
particular `β* > 0` — such that `β*Φ^{h*}` has `N + 1` mutually singular shift-invariant Gibbs
measures `μ_0, …, μ_N`, the `n`-th carried by the event that the pattern `W_n` percolates in
the plane; consequently `|ex 𝒢_Θ(β*Φ^{h*})| ≥ N + 1`.  Each `μ_n` is invariant under every
`τ ∈ ⋂ {I_{C,λ}(Φ^h) : h ∈ ∂ℝ_+^N}` with `τ W_n = W_n`.

The upper end `β₁` of the temperature interval is produced by the proof (Georgii's Step 2) and
is therefore existentially quantified.

Georgii's conditions (19.17) and (19.18) read

`e^{-β₀ b} ≤ t e^{-β₀(a+c)} min_{1≤n≤N} λ^C(V_n)^{1/|C|} / λ(E)`,
`λ^C(W_0)^{1/|C|} < (N+1)^{-1} e^{-β₀(a+c)} (1-t) min_{1≤n≤N} λ^C(V_n)^{1/|C|}`;

`λ(E) = 1` here, and Georgii's `1/4` is `1/|C| = 1/2^d`, which for the `d = 2` of Chapters 18
and 19 is his `1/4`. -/
theorem exists_gibbsMeasure_family_isCompetingWells
    (hΦmeas : ∀ h, Measurable (Φ h)) (hΦbdd : ∀ h, ∃ B : ℝ, ∀ ζ, |Φ h ζ| ≤ B)
    (hΦrefl : ∀ (h : Fin N → ℝ) (k : Fin 2) ζ, Φ h (cubeRefl E k ζ) = Φ h ζ)
    (hΦcont : ∀ h ∈ nonnegBoundary (Fin N), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ h' in 𝓝[nonnegBoundary (Fin N)] h, ∀ ζ, |Φ h' ζ - Φ h ζ| ≤ ε)
    (hA : IsCompetingWells Φ ν W V a b c δ)
    (htz : ((N : ℝ≥0∞) + 1) * (4 * crossingBound t) < 1) (hβ₀ : 0 < β₀)
    (h1917 : ENNReal.ofReal (Real.exp (-(β₀ * b)))
      ≤ t * ENNReal.ofReal (Real.exp (-(β₀ * (a + c))))
        * ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹))
    (h1918 : cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹)
      < ((N : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * (1 - t)
        * ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹)) :
    ∃ β₁ : ℝ, β₀ < β₁ ∧ ∃ h ∈ nonnegBoundary (Fin N), ∃ β ∈ Set.Icc β₀ β₁,
      ∀ (hmeas : Measurable fun ζ ↦ β * Φ h ζ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ β * Φ h ζ),
      ∃ ρ : Fin (N + 1) → Measure ((Fin 2 → ℤ) → E),
        (∀ n, IsProbabilityMeasure (ρ n)) ∧
        (∀ n, Specification.IsGibbsMeasure
          (cubeGibbsSpec E (fun ζ ↦ β * Φ h ζ) ν hmeas hM) (ρ n)) ∧
        (∀ (n : Fin (N + 1)) (x : Fin 2 → ℤ),
          MeasurePreserving (shift E x).toFun (ρ n) (ρ n)) ∧
        (Pairwise fun m n ↦ (ρ m).MutuallySingular (ρ n)) ∧ Function.Injective ρ ∧
        (∀ n, ρ n {ω | (latticeOceanPart E (W n) ω).Nonempty} = 1) ∧
        (∀ n, 1 - ((N : ℝ≥0∞) + 1) * (4 * crossingBound t)
          ≤ ρ n {ω | (0 : Site) ∈ latticeOceanPart E (W n) ω}) ∧
        (∀ (n : Fin (N + 1)) (τ : CubeTransformation E 2),
          (∀ h' ∈ nonnegBoundary (Fin N), τ.IsSymmetry (Φ h') ν) →
          τ.onCube.toFun '' W n = W n →
          MeasurePreserving (τ.onLattice E).toFun (ρ n) (ρ n)) ∧
        ((N + 1 : ℕ) : ℕ∞) ≤ ((invariantG (cubeGibbsSpec E (fun ζ ↦ β * Φ h ζ) ν hmeas hM)
          (shiftGroup (Fin 2 → ℤ) E)).extremePoints ℝ≥0∞).encard := by
  classical
  set Mn : ℝ≥0∞ := ⨅ n : Fin N, cubeMeasure 2 ν (Set.univ.pi (V n.succ)) ^ ((2 ^ 2 : ℝ)⁻¹)
    with hMndef
  set v₀ : ℝ≥0∞ := cubeMeasure 2 ν (Set.univ.pi (V 0)) ^ ((2 ^ 2 : ℝ)⁻¹) with hv₀def
  have hMn0 : Mn ≠ 0 := hA.iInf_rect_pos.ne'
  have hMntop : Mn ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (iInf_rect_le_one ν V)
  have hv₀0 : v₀ ≠ 0 :=
    (ENNReal.rpow_pos (hA.measure_pi_pos 0) (measure_ne_top _ _)).ne'
  have hv₀top : v₀ ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.rpow_le_one prob_le_one (by positivity))
  have hN0 : ((N : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hNtop : ((N : ℝ≥0∞) + 1) ≠ ∞ := by simp
  -- Georgii's `t < 1`
  have hK1 : (1 : ℝ≥0∞) ≤ (N : ℝ≥0∞) + 1 := le_add_self
  have hz1 : crossingBound t < 1 := by
    refine lt_of_le_of_lt (le_trans ?_ (le_mul_of_one_le_left zero_le hK1)) htz
    exact le_mul_of_one_le_left zero_le (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have ht1 : t < 1 := lt_of_le_of_lt (le_crossingBound hz1) hz1
  have ht0' : (0 : ℝ≥0∞) < 1 - t := tsub_pos_of_lt ht1
  -- `e^{-x} e^{x} = 1`
  have hcancel : ∀ x : ℝ, ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (Real.exp x) = 1 := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  -- Georgii's (19.17) forces `a + c < b`
  have hbac : a + c < b := by
    by_contra hcon
    rw [not_lt] at hcon
    have hle : ENNReal.ofReal (Real.exp (-(β₀ * (a + c))))
        ≤ ENNReal.ofReal (Real.exp (-(β₀ * b))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
    have h2 : (1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(β₀ * (a + c))))
        ≤ t * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) := by
      rw [one_mul]
      refine hle.trans (h1917.trans ?_)
      calc t * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * Mn
          ≤ t * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * 1 :=
            mul_le_mul' le_rfl (iInf_rect_le_one ν V)
        _ = _ := mul_one _
    have := (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      ENNReal.ofReal_ne_top).1 h2
    exact absurd ht1 (not_lt.2 this)
  -- Georgii's (19.17) in the form used in Step 2
  have hkey17 : ENNReal.ofReal (Real.exp (-(β₀ * (b - a - c)))) ≤ t * Mn := by
    have h := mul_le_mul' h1917 (le_refl (ENNReal.ofReal (Real.exp (β₀ * (a + c)))))
    calc ENNReal.ofReal (Real.exp (-(β₀ * (b - a - c))))
        = ENNReal.ofReal (Real.exp (-(β₀ * b))) * ENNReal.ofReal (Real.exp (β₀ * (a + c))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
          congr 2
          ring
      _ ≤ t * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * Mn
            * ENNReal.ofReal (Real.exp (β₀ * (a + c))) := h
      _ = t * Mn * (ENNReal.ofReal (Real.exp (-(β₀ * (a + c))))
            * ENNReal.ofReal (Real.exp (β₀ * (a + c)))) := by ring
      _ = t * Mn := by rw [hcancel, mul_one]
  -- Georgii's (19.18) in the form used in Step 2
  have hkey18 : ((N : ℝ≥0∞) + 1)
      * (ENNReal.ofReal (Real.exp (β₀ * (a + c)))
        * cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹) / Mn) < 1 - t := by
    set X : ℝ≥0∞ := ENNReal.ofReal (Real.exp (β₀ * (a + c))) with hXdef
    have hX0 : X ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hXtop : X ≠ ∞ := ENNReal.ofReal_ne_top
    set Kc : ℝ≥0∞ := ((N : ℝ≥0∞) + 1) * X * Mn⁻¹ with hKcdef
    have hKc0 : Kc ≠ 0 :=
      mul_ne_zero (mul_ne_zero hN0 hX0) (ENNReal.inv_ne_zero.2 hMntop)
    have hKctop : Kc ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hNtop hXtop) (ENNReal.inv_ne_top.2 hMn0)
    have hrw : ((N : ℝ≥0∞) + 1) * (X * cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹) / Mn)
        = Kc * cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹) := by
      rw [hKcdef, div_eq_mul_inv]
      ring
    rw [hrw]
    calc Kc * cubeMeasure 2 ν (W 0) ^ ((2 ^ 2 : ℝ)⁻¹)
        < Kc * (((N : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * (1 - t)
            * Mn) := ENNReal.mul_lt_mul_right hKc0 hKctop h1918
      _ = (((N : ℝ≥0∞) + 1) * ((N : ℝ≥0∞) + 1)⁻¹)
            * (ENNReal.ofReal (Real.exp (-(β₀ * (a + c)))) * X) * (Mn⁻¹ * Mn) * (1 - t) := by
          rw [hKcdef]
          ring
      _ = 1 - t := by
          rw [ENNReal.mul_inv_cancel hN0 hNtop, hcancel, ENNReal.inv_mul_cancel hMn0 hMntop,
            one_mul, one_mul, one_mul]
  -- Georgii's `β₁`: the wells `W_n`, `n ≥ 1`, and the barrier decay at the common rate
  -- `min (a - δ) β₀ > 0`
  set rr : ℝ := min (a - δ) β₀ with hrrdef
  have hrr0 : 0 < rr := lt_min (by linarith [hA.delta_lt_a]) hβ₀
  set u : ℝ≥0∞ := (1 - t) * v₀ * ((N : ℝ≥0∞) + 1)⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero ht0'.ne' hv₀0) (ENNReal.inv_ne_zero.2 hNtop)
  obtain ⟨x, hx0, hxu⟩ := exists_between (pos_iff_ne_zero.2 hu0)
  have hxtop : x ≠ ∞ := ne_top_of_lt hxu
  have hr0 : 0 < x.toReal := ENNReal.toReal_pos hx0.ne' hxtop
  have hlim : Tendsto (fun β : ℝ ↦ Real.exp (-(β * rr))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.atTop_mul_const hrr0 Filter.tendsto_id))
  obtain ⟨β₁, hβ₁r, hβ₁gt⟩ :=
    ((hlim.eventually (gt_mem_nhds hr0)).and (eventually_gt_atTop β₀)).exists
  have hβ₁pos : 0 < β₁ := lt_trans hβ₀ hβ₁gt
  have hβ₁key : ENNReal.ofReal (Real.exp (-(β₁ * rr))) < u :=
    calc ENNReal.ofReal (Real.exp (-(β₁ * rr))) < ENNReal.ofReal x.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hr0).2 hβ₁r
      _ = x := ENNReal.ofReal_toReal hxtop
      _ < u := hxu
  -- Georgii's `t̃(E^C ∖ W_n, βΦ^h) < (1-t)/(N+1)` when `β = β₁` or `h_n = β₁`, `β ≥ β₀`
  have hkeyβ₁ : ∀ (β : ℝ) (h : Fin N → ℝ) (n : Fin N), β₀ ≤ β → (∀ k, 0 ≤ h k) →
      (β = β₁ ∨ h n = β₁) →
      ((N : ℝ≥0∞) + 1) * (ENNReal.ofReal (Real.exp (-(β * (a + h n - δ)))) / v₀) < 1 - t := by
    intro β h n hβ hh0 hcase
    have hadelta : 0 < a - δ := by linarith [hA.delta_lt_a]
    have hexp : Real.exp (-(β * (a + h n - δ))) ≤ Real.exp (-(β₁ * rr)) := by
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      rcases hcase with rfl | hcase
      · have h1 : rr ≤ a - δ := min_le_left _ _
        nlinarith [hh0 n]
      · rw [hcase]
        have h1 : rr ≤ β₀ := min_le_right _ _
        nlinarith [hβ₀]
    have hZ : ENNReal.ofReal (Real.exp (-(β * (a + h n - δ)))) < u :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hexp) hβ₁key
    have hfac0 : ((N : ℝ≥0∞) + 1) * v₀⁻¹ ≠ 0 := mul_ne_zero hN0 (ENNReal.inv_ne_zero.2 hv₀top)
    have hfactop : ((N : ℝ≥0∞) + 1) * v₀⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top hNtop (ENNReal.inv_ne_top.2 hv₀0)
    calc ((N : ℝ≥0∞) + 1) * (ENNReal.ofReal (Real.exp (-(β * (a + h n - δ)))) / v₀)
        = ((N : ℝ≥0∞) + 1) * v₀⁻¹ * ENNReal.ofReal (Real.exp (-(β * (a + h n - δ)))) := by
          rw [div_eq_mul_inv]
          ring
      _ < ((N : ℝ≥0∞) + 1) * v₀⁻¹ * u := ENNReal.mul_lt_mul_right hfac0 hfactop hZ
      _ = 1 - t := by
          rw [hudef, show ((N : ℝ≥0∞) + 1) * v₀⁻¹ * ((1 - t) * v₀ * ((N : ℝ≥0∞) + 1)⁻¹)
              = (((N : ℝ≥0∞) + 1) * ((N : ℝ≥0∞) + 1)⁻¹) * (v₀⁻¹ * v₀) * (1 - t) by ring,
            ENNReal.mul_inv_cancel hN0 hNtop, ENNReal.inv_mul_cancel hv₀0 hv₀top,
            one_mul, one_mul]
  -- Georgii's Step 3: the family `Ψ^α = β(α) Φ^{h(α)}`
  have hψbdd : ∀ α : Fin (N + 1) → ℝ,
      ∃ B : ℝ, ∀ ζ, |wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ| ≤ B := by
    intro α
    obtain ⟨B, hB⟩ := hΦbdd (wellField β₁ α)
    refine ⟨|wellTemperature β₀ β₁ α| * B, fun ζ ↦ ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB ζ) (abs_nonneg _)
  have hψmeas : ∀ α : Fin (N + 1) → ℝ,
      Measurable fun ζ ↦ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ :=
    fun α ↦ (hΦmeas _).const_mul _
  have hψM : ∀ α : Fin (N + 1) → ℝ,
      ∃ M : ℝ, ∀ ζ, M ≤ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ := by
    intro α
    obtain ⟨B, hB⟩ := hψbdd α
    exact ⟨-B, fun ζ ↦ neg_le_of_abs_le (hB ζ)⟩
  have hψrefl : ∀ (α : Fin (N + 1) → ℝ) (k : Fin 2) ζ,
      wellTemperature β₀ β₁ α * Φ (wellField β₁ α) (cubeRefl E k ζ)
        = wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ := by
    intro α k ζ
    rw [hΦrefl]
  have hKconf : ∀ α : Fin (N + 1) → ℝ,
      IsCubeConfining (fun ζ ↦ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ) ν
        (fun _ ↦ (Set.univ : Set E)) := fun α ↦ isCubeConfining_univ (hψbdd α)
  -- Georgii's hypothesis (19.14)(I)
  have hI : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ ε : ℝ, 0 < ε →
      ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α, ∀ ζ,
        |wellTemperature β₀ β₁ α' * Φ (wellField β₁ α') ζ
          - wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ| ≤ ε := by
    intro α hα ε hε
    obtain ⟨B, hB⟩ := hΦbdd (wellField β₁ α)
    have hB' : ∀ ζ, |Φ (wellField β₁ α) ζ| ≤ |B| := fun ζ ↦ (hB ζ).trans (le_abs_self B)
    have hden : (0 : ℝ) < |B| + 1 + β₁ := by positivity
    set η : ℝ := min 1 (ε / (|B| + 1 + β₁)) with hηdef
    have hη0 : 0 < η := lt_min one_pos (div_pos hε hden)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η * (|B| + 1 + β₁) ≤ ε := by
      have h2 : η ≤ ε / (|B| + 1 + β₁) := min_le_right _ _
      calc η * (|B| + 1 + β₁) ≤ ε / (|B| + 1 + β₁) * (|B| + 1 + β₁) := by nlinarith
        _ = ε := div_mul_cancel₀ _ hden.ne'
    have hwf : Tendsto (wellField β₁) (𝓝[stdSimplex ℝ (Fin (N + 1))] α)
        (𝓝[nonnegBoundary (Fin N)] (wellField β₁ α)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_wellField hα).continuousWithinAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with α' hα'
      exact wellField_mem_nonnegBoundary hα' hβ₁pos.le
    have hβcont : ∀ᶠ α' in 𝓝[stdSimplex ℝ (Fin (N + 1))] α,
        |wellTemperature β₀ β₁ α' - wellTemperature β₀ β₁ α| ≤ η := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      have h : wellTemperature β₀ β₁ ⁻¹'
          Metric.closedBall (wellTemperature β₀ β₁ α) η ∈ 𝓝 α :=
        (continuousAt_wellTemperature (β₀ := β₀) (β₁ := β₁) hα)
          (Metric.closedBall_mem_nhds (wellTemperature β₀ β₁ α) hη0)
      filter_upwards [h] with α' hα'
      simpa [Real.dist_eq] using hα'
    have hβr := wellTemperature_mem_Icc (β₀ := β₀) hα hβ₁gt.le
    have hq0 : 0 ≤ wellTemperature β₀ β₁ α := le_trans hβ₀.le hβr.1
    filter_upwards [hβcont,
      hwf.eventually (hΦcont _ (wellField_mem_nonnegBoundary hα hβ₁pos.le) η hη0)] with α' hβ' hΦ'
    intro ζ
    have h1 : |Φ (wellField β₁ α') ζ| ≤ |B| + η := by
      have h2 := abs_sub_abs_le_abs_sub (Φ (wellField β₁ α') ζ) (Φ (wellField β₁ α) ζ)
      have h3 := hΦ' ζ
      have h4 := hB' ζ
      linarith
    have e1 : wellTemperature β₀ β₁ α' * Φ (wellField β₁ α') ζ
          - wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ
        = (wellTemperature β₀ β₁ α' - wellTemperature β₀ β₁ α) * Φ (wellField β₁ α') ζ
          + wellTemperature β₀ β₁ α
            * (Φ (wellField β₁ α') ζ - Φ (wellField β₁ α) ζ) := by ring
    rw [e1]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hq0]
    have hA1 : |wellTemperature β₀ β₁ α' - wellTemperature β₀ β₁ α| * |Φ (wellField β₁ α') ζ|
        ≤ η * (|B| + η) :=
      mul_le_mul hβ' h1 (abs_nonneg _) hη0.le
    have hA2 : wellTemperature β₀ β₁ α * |Φ (wellField β₁ α') ζ - Φ (wellField β₁ α) ζ|
        ≤ β₁ * η := mul_le_mul hβr.2 (hΦ' ζ) (abs_nonneg _) hβ₁pos.le
    nlinarith [abs_nonneg B]
  -- Georgii's hypothesis (19.14)(II)
  have hII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)),
      rectPatternWeight (fun ζ ↦ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ) ν
        (⋃ n, W n) ≤ t := by
    intro α hα
    have hβr := wellTemperature_mem_Icc (β₀ := β₀) hα hβ₁gt.le
    have hβpos : 0 < wellTemperature β₀ β₁ α := lt_of_lt_of_le hβ₀ hβr.1
    refine le_trans (hA.rectPatternWeight_iUnion_le
      (wellField_mem_nonnegBoundary hα hβ₁pos.le) hβpos) ?_
    rw [ENNReal.div_le_iff hMn0 hMntop]
    refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hkey17
    have hpos : 0 < b - a - c := by linarith
    nlinarith [hβr.1]
  -- Georgii's hypothesis (19.14)(III)
  have hIII : ∀ α ∈ stdSimplex ℝ (Fin (N + 1)), ∀ n : Fin (N + 1), α n = 0 →
      ((N : ℝ≥0∞) + 1)
        * rectPatternWeight (fun ζ ↦ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ) ν
          (W n)ᶜ < 1 - t := by
    intro α hα n hαn
    have hβr := wellTemperature_mem_Icc (β₀ := β₀) hα hβ₁gt.le
    have hβpos : 0 < wellTemperature β₀ β₁ α := lt_of_lt_of_le hβ₀ hβr.1
    have hh := wellField_mem_nonnegBoundary hα hβ₁pos.le
    rcases Fin.eq_zero_or_eq_succ n with rfl | ⟨j, rfl⟩
    · rw [wellTemperature_of_apply_zero hαn]
      exact lt_of_le_of_lt
        (mul_le_mul' le_rfl (hA.rectPatternWeight_compl_zero_le hh hβ₀)) hkey18
    · refine lt_of_le_of_lt
        (mul_le_mul' le_rfl (hA.rectPatternWeight_compl_succ_le hh hβpos j)) ?_
      exact hkeyβ₁ _ _ j hβr.1 (fun k ↦ wellField_nonneg hα hβ₁pos.le k)
        (wellTemperature_eq_or_wellField_eq (β₀ := β₀) hα hαn)
  -- Georgii's Propositions (19.14) and (19.13)
  obtain ⟨α, hα, ρ, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    exists_gibbsMeasure_family_of_rectPatternWeight_le
      (ψ := fun α ζ ↦ wellTemperature β₀ β₁ α * Φ (wellField β₁ α) ζ)
      (K := fun _ ↦ (Set.univ : Set E))
      (isPStablePartition_of_isCompetingWells hA) hA.measurableSet hA.isRSymmetric
      hψmeas hψM hψrefl hKconf hI hII hIII htz
  refine ⟨β₁, hβ₁gt, wellField β₁ α, wellField_mem_nonnegBoundary hα hβ₁pos.le,
    wellTemperature β₀ β₁ α, wellTemperature_mem_Icc hα hβ₁gt.le,
    fun hmeas hM ↦ ⟨ρ, h1, h2, h3, h4, h5, h6, h7, fun n τ hτ hWτ ↦ ?_, ?_⟩⟩
  · refine h8 n τ (fun α' hα' ↦ ?_) hWτ
    have hs := hτ (wellField β₁ α') (wellField_mem_nonnegBoundary hα' hβ₁pos.le)
    exact CubeTransformation.IsSymmetry.of_apply_onCube (fun k ζ ↦ hψrefl α' k ζ)
      hs.measurePreserving_spin (fun ζ ↦ by rw [hs.apply_onCube])
  · exact le_encard_extremePoints_of_latticeOceanPart
      (isPStablePartition_of_isCompetingWells hA) hA.measurableSet h1 h2 h3 h6

end Theorem1916

end MeasureTheory.GibbsMeasure

end

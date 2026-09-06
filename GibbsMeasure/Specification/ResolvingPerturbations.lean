/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.LocalGroundStates

/-!
# Georgii §19.1, (19.1)–(19.5): perturbations that resolve a degenerate ground state

Georgii, *Gibbs Measures and Phase Transitions*, §19.1.  A `C`-potential `Φ` with a stable
partition `{G_1, …, G_N}` of its local ground states (Definition (18.23)(a), the structure
`MeasureTheory.GibbsMeasure.IsPStablePartition`) need not be `Φ`-symmetric, and then Theorem
(18.25) does not apply: the sets `G_n` may be at different energetic disadvantages, and only
some of them will actually carry a Gibbs measure.  Georgii restores the balance by perturbing
`Φ` inside an `(N-1)`-dimensional family.  This file is the *setting* of that argument, up to
and including Comment (19.5)(1); Theorem (19.6) itself is proved in §19.2 by a fixed point
argument which is not available here — see the last section of this docstring.

## Main definitions and results

* `localGroundEnergyOn` is Georgii's `λ-inf_M Φ_C` for an arbitrary `M ⊆ E^C`; it specialises
  to `localGroundEnergy` (18.1) at `M = E^C` and to `energyOutside` at `M = Gᶜ`.  Its home is
  `GibbsMeasure/Specification/LocalGroundStates.lean`, next to `energyOutside`, of which it is
  the general form.  `localGroundEnergyOn_iUnion` is the fact that `λ-inf` over a finite union
  is the minimum of the `λ-inf`s, which is what makes Georgii's `g` of (19.3) computable.
* `AttainsGroundEnergy` is **Georgii (19.1)**, `λ-inf_{G_n} Φ_C = m_Φ`, stated in the form he
  immediately gives it — `λ^C(G_n ∩ G_ε(Φ)) > 0` for all `ε > 0` — because the essential
  infimum over a `λ^C`-null set is a junk value in `ℝ`, so the two forms agree only once
  `λ^C(G_n) > 0` is known.  `attainsGroundEnergy_iff` is that equivalence.
* `perturb` is **Georgii (19.2)**, `Φ^h = Φ + ∑_{n<N} h_n Φ^n`, and `groundEnergyGap` is
  **Georgii (19.3)**, `g_n(h) = λ-inf_{G_n} Φ^h_C - λ-inf_G Φ^h_C`; `perturbGap` is `g` as a
  function of `h`.  `nonnegBoundary` is his `∂ℝ_+^N` (indeed the topological frontier of the
  positive octant, `nonnegBoundary_eq_frontier`); `perturbGap_mem_nonnegBoundary` and
  `continuous_perturbGap` are the two assertions of the sentence after (19.3), and
  `perturbGap_zero` is his `g(0) = 0` under (19.1).  Continuity rests on the fact that
  `λ-inf_M` is `1`-Lipschitz in the uniform norm of the interaction
  (`abs_localGroundEnergyOn_sub_le`).
* `Resolves` is **Definition (19.4)**: the potentials `Φ^1, …, Φ^{N-1}` resolve the partition
  if on some neighbourhood `U` of the origin (i) `g` is a homeomorphism onto a neighbourhood of
  the origin in `∂ℝ_+^N`, and (ii) `inf_{h ∈ U} λ^C(G_δ(Φ^h)) > 0` for every `δ > 0`.
* `resolves_of_const_on` is **Comment (19.5)(1)**: bounded `Φ^1, …, Φ^{N-1}` with `Φ^n_C`
  constant on `G_n` and equal to a *different* constant on `G ∖ G_n` resolve the partition.
  Its ingredients are, in Georgii's order, `localGroundEnergyOn_perturb_const_on`
  (`λ-inf_{G_n} Φ^h_C = m_Φ + h_n δ_n + ∑_k h_k c_k`), `groundEnergyGap_perturb_const_on`
  (`g(h) = (h_n δ_n - min_k h_k δ_k)_n`), `gapHomeomorph` (`g` is a homeomorphism of `ℝ^{N-1}`
  onto `∂ℝ_+^N`, with the inverse `g^{-1}(z) = ((z_n - z_N) δ_n^{-1})_{n<N}` Georgii writes
  down), and `localGroundStates_perturb_inter_eq` (`G_δ(Φ^h) ∩ G_n = G_δ(Φ) ∩ G_n`, the
  identity behind (19.4)(ii)).
* `exists_measure_localGroundStates_pos_of_finite` is **Comment (19.5)(2)**, first sentence:
  over a finite state space with an a priori measure of full support, condition (19.4)(ii) holds
  for every family of potentials at once.  The second sentence of (19.5)(2) — the metric
  criterion, for which Georgii writes only "this can be proved in a similar manner" — is not
  formalised.

## Georgii's indices

Georgii numbers the partition `1, …, N` and the perturbations `1, …, N-1`.  Here the partition
is indexed by `Fin (N + 1)` and the perturbations by `Fin N`, embedded by `Fin.castSucc`; his
convention `h_N = 0` in Comment (19.5)(1) is `Fin.snoc _ 0`.  In particular `N = 0` — a single
set `G_0` and no perturbation at all — is allowed and degenerate, exactly as `N = 1` is for
Georgii.

## Theorem (19.6)

Georgii proves Theorem (19.6) in §19.2 through Propositions (19.13) and (19.14), and the
combinatorial heart of that proof is Lemma (19.12): *a closed cover `K_1, …, K_N` of the
simplex `𝒫_N` of probability vectors with `K_n ∩ {α : α(n) = 0} = ∅` has
`⋂_n K_n ≠ ∅`* — the Knaster–Kuratowski–Mazurkiewicz lemma, which Georgii derives from
Sperner's lemma in his Appendix 19.A.  Mathlib has neither Sperner's lemma nor Brouwer's fixed
point theorem; both Sperner's lemma (on Kuhn's triangulation of the simplex,
`Sperner.odd_card_panchromaticCells` in `GibbsMeasure/Mathlib/Combinatorics/Sperner.lean`) and
Lemma (19.12) (`nonempty_iInter_of_isClosed_of_stdSimplex_subset_iUnion` in
`GibbsMeasure/Mathlib/Topology/KKM.lean`) are now in this library, so what remains of (19.6) is
the assembly of Propositions (19.13)--(19.15).  Nothing else in §19.1 depends on it.
Corollary (19.7) is `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_refinement` of
`GibbsMeasure/Model/GroundStateRefinement.lean`, proved from the properties of the measures
`μ_n` that Georgii's proof of it actually uses — so from the *conclusion* of (19.6) rather than
from the theorem.  Example (19.8), the Blume–Capel model, is
`GibbsMeasure/Model/BlumeCapel.lean`, complete except for that same conclusion.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {d : ℕ}

/-! ### `λ-inf` over a subset of `E^C`

Georgii's `λ-inf_M Φ_C` for an arbitrary `M ⊆ E^C`.  Everything in this section belongs next to
`energyOutside` in `GibbsMeasure/Specification/LocalGroundStates.lean`. -/

section EnergyOn

variable (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)

/-- **Georgii's `λ-inf_M Φ_C`**: the essential infimum of the cube interaction over a set `M` of
cube configurations, relative to the a priori measure `λ^C`.  It is `localGroundEnergy` (18.1) at
`M = E^C` and `energyOutside` at `M = Gᶜ`.

Beware that this is a genuine essential infimum only when `λ^C(M) > 0`; over a null set Mathlib's
`essInf` returns the junk value of `ℝ` instead of Georgii's `+∞`. -/
def localGroundEnergyOn (M : Set ((Fin d → Fin 2) → E)) : ℝ :=
  essInf φ ((cubeMeasure d ν).restrict M)

variable {φ ν}

@[simp] lemma localGroundEnergyOn_univ :
    localGroundEnergyOn φ ν univ = localGroundEnergy φ ν := by
  rw [localGroundEnergyOn, Measure.restrict_univ, localGroundEnergy]

lemma energyOutside_eq_localGroundEnergyOn (G : Set ((Fin d → Fin 2) → E)) :
    energyOutside φ ν G = localGroundEnergyOn φ ν Gᶜ := rfl

lemma neZero_restrict_of_measure_ne_zero {M : Set ((Fin d → Fin 2) → E)}
    (hM : cubeMeasure d ν M ≠ 0) : NeZero ((cubeMeasure d ν).restrict M) :=
  ⟨fun h ↦ hM (Measure.restrict_eq_zero.1 h)⟩

variable {M₀ : ℝ} {M M' : Set ((Fin d → Fin 2) → E)}

/-- On `M`, the interaction is almost everywhere at least `λ-inf_M Φ_C`. -/
theorem ae_localGroundEnergyOn_le (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (M : Set ((Fin d → Fin 2) → E)) :
    ∀ᵐ ζ ∂(cubeMeasure d ν).restrict M, localGroundEnergyOn φ ν M ≤ φ ζ :=
  ae_essInf_le (isBoundedUnder_ge_ae (Eventually.of_forall hM₀))

/-- Restricting to a smaller set can only raise the essential infimum: `λ-inf_M Φ_C` is
antitone in `M` (as long as the smaller set is not null, where the value is junk). -/
theorem localGroundEnergyOn_le_of_subset (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (hMM' : M ⊆ M')
    (hM : cubeMeasure d ν M ≠ 0) :
    localGroundEnergyOn φ ν M' ≤ localGroundEnergyOn φ ν M := by
  have := neZero_restrict_of_measure_ne_zero hM
  exact essInf_antitone_measure
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hMM' le_rfl))
    (isBoundedUnder_ge_ae (Eventually.of_forall hM₀)) (isCoboundedUnder_ge_ae _)

/-- `m_Φ ≤ λ-inf_M Φ_C` for every non-null `M`. -/
theorem localGroundEnergy_le_localGroundEnergyOn (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hM : cubeMeasure d ν M ≠ 0) : localGroundEnergy φ ν ≤ localGroundEnergyOn φ ν M := by
  simpa using localGroundEnergyOn_le_of_subset hM₀ (subset_univ M) hM

/-- If `Φ_C ≤ c` on a non-null part of `M` then `λ-inf_M Φ_C ≤ c`. -/
theorem localGroundEnergyOn_le_of_measure_ne_zero (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    {c : ℝ} (h : cubeMeasure d ν (M ∩ {ζ | φ ζ ≤ c}) ≠ 0) : localGroundEnergyOn φ ν M ≤ c := by
  by_contra hc
  rw [not_le] at hc
  have hae : ∀ᵐ ζ ∂(cubeMeasure d ν).restrict M, ¬ φ ζ ≤ c := by
    filter_upwards [ae_localGroundEnergyOn_le (φ := φ) (ν := ν) hM₀ M] with ζ hζ
    exact not_le.2 (lt_of_lt_of_le hc hζ)
  rw [ae_iff, Measure.restrict_apply (by simpa using measurableSet_le hφ measurable_const)] at hae
  exact h (by simpa [inter_comm] using hae)

/-- If `λ-inf_M Φ_C < c` then `Φ_C ≤ c` on a non-null part of `M`. -/
theorem measure_inter_ne_zero_of_localGroundEnergyOn_lt (hφ : Measurable φ)
    (hM : cubeMeasure d ν M ≠ 0) {c : ℝ} (hc : localGroundEnergyOn φ ν M < c) :
    cubeMeasure d ν (M ∩ {ζ | φ ζ ≤ c}) ≠ 0 := by
  have := neZero_restrict_of_measure_ne_zero hM
  intro h0
  have hz : (cubeMeasure d ν).restrict M {ζ | φ ζ ≤ c} = 0 := by
    rw [Measure.restrict_apply (by simpa using measurableSet_le hφ measurable_const)]
    simpa [inter_comm] using h0
  have hae : ∀ᵐ ζ ∂(cubeMeasure d ν).restrict M, c ≤ φ ζ := by
    rw [ae_iff]
    refine measure_mono_null (fun ζ hζ ↦ ?_) hz
    simp only [Set.mem_ofPred_eq, not_le] at hζ ⊢
    exact hζ.le
  exact absurd (le_essInf_of_ae_le c hae (isCoboundedUnder_ge_ae _)) (not_le.2 hc)

/-- **`λ-inf` over a finite union is the minimum of the `λ-inf`s.**  This is what turns
Georgii's `λ-inf_G Φ^h_C` of (19.3) into `min_n λ-inf_{G_n} Φ^h_C`. -/
theorem localGroundEnergyOn_iUnion {ι : Type*} [Finite ι] [Nonempty ι] (hφ : Measurable φ)
    (hM₀ : ∀ ζ, M₀ ≤ φ ζ) {M : ι → Set ((Fin d → Fin 2) → E)}
    (hMpos : ∀ i, cubeMeasure d ν (M i) ≠ 0) :
    localGroundEnergyOn φ ν (⋃ i, M i) = ⨅ i, localGroundEnergyOn φ ν (M i) := by
  classical
  have hUne : cubeMeasure d ν (⋃ i, M i) ≠ 0 := fun h ↦
    hMpos (Classical.arbitrary ι)
      (measure_mono_null (subset_iUnion M (Classical.arbitrary ι)) h)
  have := neZero_restrict_of_measure_ne_zero hUne
  set c : ℝ := ⨅ i, localGroundEnergyOn φ ν (M i) with hc
  refine le_antisymm (le_ciInf fun i ↦ ?_) ?_
  · exact localGroundEnergyOn_le_of_subset hM₀ (subset_iUnion M i) (hMpos i)
  · have key : ∀ i, cubeMeasure d ν ({ζ | φ ζ < c} ∩ M i) = 0 := by
      intro i
      have h1 : (cubeMeasure d ν).restrict (M i) {ζ | φ ζ < c} = 0 := by
        have hai := ae_localGroundEnergyOn_le (φ := φ) (ν := ν) hM₀ (M i)
        rw [ae_iff] at hai
        refine measure_mono_null (fun ζ hζ ↦ ?_) hai
        simp only [Set.mem_ofPred_eq, not_le] at hζ ⊢
        exact lt_of_lt_of_le hζ (ciInf_le (Finite.bddBelow_range _) i)
      rwa [Measure.restrict_apply (by simpa using measurableSet_lt hφ measurable_const)] at h1
    have hnull : cubeMeasure d ν ({ζ | φ ζ < c} ∩ ⋃ i, M i) = 0 := by
      rw [inter_iUnion]
      exact measure_iUnion_null key
    have hae : ∀ᵐ ζ ∂(cubeMeasure d ν).restrict (⋃ i, M i), c ≤ φ ζ := by
      rw [ae_iff]
      simp only [not_le]
      rw [Measure.restrict_apply (by simpa using measurableSet_lt hφ measurable_const)]
      exact hnull
    exact le_essInf_of_ae_le c hae (isCoboundedUnder_ge_ae _)

/-- The `λ-inf` over a finite union is attained by one of the members. -/
theorem exists_localGroundEnergyOn_iUnion_eq {ι : Type*} [Finite ι] [Nonempty ι]
    (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ) {M : ι → Set ((Fin d → Fin 2) → E)}
    (hMpos : ∀ i, cubeMeasure d ν (M i) ≠ 0) :
    ∃ i, localGroundEnergyOn φ ν (⋃ j, M j) = localGroundEnergyOn φ ν (M i) := by
  obtain ⟨i, hi⟩ := Finite.exists_min fun j ↦ localGroundEnergyOn φ ν (M j)
  refine ⟨i, ?_⟩
  rw [localGroundEnergyOn_iUnion hφ hM₀ hMpos]
  exact le_antisymm (ciInf_le (Finite.bddBelow_range _) i) (le_ciInf hi)

end EnergyOn

/-! ### Georgii (19.1): the sets of the partition attain the ground state energy -/

section Balanced

variable (φ : ((Fin d → Fin 2) → E) → ℝ) (ν : Measure E)

/-- **Georgii (19.1).**  A set `M ⊆ E^C` *attains the local ground state energy* of the
`C`-potential `Φ` if `λ^C(M ∩ G_ε(Φ)) > 0` for every `ε > 0`; equivalently, by
`attainsGroundEnergy_iff`, if `λ^C(M) > 0` and `λ-inf_M Φ_C = m_Φ`.

Georgii writes the condition as `λ-inf_{G_n} Φ_C = m_Φ` and reads it off as the displayed
positivity; "in other words, none of the sets `G_n` is at an energetic disadvantage".  The
positivity is taken here as the definition because the essential infimum of a real function over
a null set is a junk value, so the two forms are equivalent only once `λ^C(M) > 0` is known. -/
def AttainsGroundEnergy (M : Set ((Fin d → Fin 2) → E)) : Prop :=
  ∀ ε : ℝ, 0 < ε → 0 < cubeMeasure d ν (M ∩ localGroundStates φ ν ε)

variable {φ ν} {M : Set ((Fin d → Fin 2) → E)}

theorem AttainsGroundEnergy.measure_pos (h : AttainsGroundEnergy φ ν M) :
    0 < cubeMeasure d ν M :=
  lt_of_lt_of_le (h 1 one_pos) (measure_mono inter_subset_left)

variable {M₀ : ℝ}

/-- **Georgii (19.1) as he writes it**: `λ-inf_M Φ_C = m_Φ`. -/
theorem AttainsGroundEnergy.localGroundEnergyOn_eq (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (h : AttainsGroundEnergy φ ν M) : localGroundEnergyOn φ ν M = localGroundEnergy φ ν := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_)
    (localGroundEnergy_le_localGroundEnergyOn hM₀ h.measure_pos.ne')
  exact localGroundEnergyOn_le_of_measure_ne_zero hφ hM₀ (h ε hε).ne'

/-- **Georgii (19.1), the two forms are equivalent.** -/
theorem attainsGroundEnergy_iff (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ) :
    AttainsGroundEnergy φ ν M ↔
      0 < cubeMeasure d ν M ∧ localGroundEnergyOn φ ν M = localGroundEnergy φ ν := by
  refine ⟨fun h ↦ ⟨h.measure_pos, h.localGroundEnergyOn_eq hφ hM₀⟩, fun ⟨hpos, heq⟩ ε hε ↦ ?_⟩
  rw [pos_iff_ne_zero]
  exact measure_inter_ne_zero_of_localGroundEnergyOn_lt hφ hpos.ne'
    (by rw [heq]; linarith)

end Balanced

/-! ### Georgii (19.2): the perturbed potentials `Φ^h` -/

section Perturbation

variable {N : ℕ} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}
  {Ψ : Fin N → ((Fin d → Fin 2) → E) → ℝ} {b h h' : Fin N → ℝ}

omit [MeasurableSpace E] in
variable (φ Ψ) in
/-- **Georgii (19.2).**  The `(N-1)`-dimensional family of perturbations
`Φ^h = Φ + ∑_{n<N} h_n Φ^n` of a `C`-potential `Φ`, read off on the cube interactions.  The
perturbing potentials are indexed by `Fin N` and the partition they will resolve by
`Fin (N + 1)`, so `N` is Georgii's `N - 1`. -/
def perturb (h : Fin N → ℝ) : ((Fin d → Fin 2) → E) → ℝ := fun ζ ↦ φ ζ + ∑ k, h k * Ψ k ζ

omit [MeasurableSpace E] in
@[simp] lemma perturb_apply (h : Fin N → ℝ) (ζ : (Fin d → Fin 2) → E) :
    perturb φ Ψ h ζ = φ ζ + ∑ k, h k * Ψ k ζ := rfl

omit [MeasurableSpace E] in
@[simp] lemma perturb_zero : perturb φ Ψ 0 = φ := by
  funext ζ; simp [perturb]

lemma measurable_perturb (hφ : Measurable φ) (hΨ : ∀ k, Measurable (Ψ k)) (h : Fin N → ℝ) :
    Measurable (perturb φ Ψ h) :=
  hφ.add (Finset.measurable_sum _ fun k _ ↦ (hΨ k).const_mul _)

omit [MeasurableSpace E] in
/-- The perturbation moves the cube interaction by at most `∑_k |h_k| ‖Φ^k_C‖`; this is the
boundedness of `Φ^1, …, Φ^{N-1}` that Georgii uses throughout §19.1. -/
lemma abs_perturb_sub_perturb_le (hb : ∀ k ζ, |Ψ k ζ| ≤ b k) (ζ : (Fin d → Fin 2) → E) :
    |perturb φ Ψ h ζ - perturb φ Ψ h' ζ| ≤ ∑ k, |h k - h' k| * b k := by
  have hsub : perturb φ Ψ h ζ - perturb φ Ψ h' ζ = ∑ k, (h k - h' k) * Ψ k ζ := by
    simp only [perturb_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hb k ζ) (abs_nonneg _)

omit [MeasurableSpace E] in
lemma abs_perturb_sub_le (hb : ∀ k ζ, |Ψ k ζ| ≤ b k) (ζ : (Fin d → Fin 2) → E) :
    |perturb φ Ψ h ζ - φ ζ| ≤ ∑ k, |h k| * b k := by
  simpa using abs_perturb_sub_perturb_le (φ := φ) (Ψ := Ψ) (h := h) (h' := 0) hb ζ

omit [MeasurableSpace E] in
/-- A perturbed potential is bounded below whenever `Φ` is. -/
lemma perturb_lower_bound {M₀ : ℝ} (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (ζ : (Fin d → Fin 2) → E) : M₀ - ∑ k, |h k| * b k ≤ perturb φ Ψ h ζ := by
  have h1 := (abs_le.1 (abs_perturb_sub_le (φ := φ) (Ψ := Ψ) (h := h) hb ζ)).1
  have h2 := hM₀ ζ
  linarith

/-- **`λ-inf_M` is `1`-Lipschitz in the uniform norm of the interaction.**  The `M = E^C` case is
`localGroundEnergy_le_add` and the `M = Gᶜ` case is `energyOutside_le_add`, both in
`GibbsMeasure/Specification/LocalGroundStates.lean`. -/
theorem abs_localGroundEnergyOn_sub_le {ψ ψ' : ((Fin d → Fin 2) → E) → ℝ} {M₀ M₀' η : ℝ}
    (hψ : ∀ ζ, M₀ ≤ ψ ζ) (hψ' : ∀ ζ, M₀' ≤ ψ' ζ) (hd : ∀ ζ, |ψ ζ - ψ' ζ| ≤ η)
    {M : Set ((Fin d → Fin 2) → E)} (hM : cubeMeasure d ν M ≠ 0) :
    |localGroundEnergyOn ψ ν M - localGroundEnergyOn ψ' ν M| ≤ η := by
  have : NeZero ((cubeMeasure d ν).restrict M) := neZero_restrict_of_measure_ne_zero hM
  rw [abs_sub_le_iff]
  simp only [localGroundEnergyOn]
  refine ⟨sub_le_iff_le_add'.2 (essInf_le_essInf_add (μ := (cubeMeasure d ν).restrict M)
      (Eventually.of_forall hψ) (Eventually.of_forall hψ') ?_),
    sub_le_iff_le_add'.2 (essInf_le_essInf_add (μ := (cubeMeasure d ν).restrict M)
      (Eventually.of_forall hψ') (Eventually.of_forall hψ) ?_)⟩
  · exact Eventually.of_forall fun ζ ↦ by linarith [(abs_le.1 (hd ζ)).2]
  · exact Eventually.of_forall fun ζ ↦ by linarith [(abs_le.1 (hd ζ)).1]

/-- **Georgii's "`g` is a continuous mapping"**, one set at a time: `h ↦ λ-inf_M Φ^h_C` is
Lipschitz, hence continuous, with constant `∑_k ‖Φ^k_C‖`. -/
theorem continuous_localGroundEnergyOn_perturb {M₀ : ℝ} (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hb : ∀ k ζ, |Ψ k ζ| ≤ b k) (hb0 : ∀ k, 0 ≤ b k) {M : Set ((Fin d → Fin 2) → E)}
    (hM : cubeMeasure d ν M ≠ 0) :
    Continuous fun h : Fin N → ℝ ↦ localGroundEnergyOn (perturb φ Ψ h) ν M := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨∑ k, b k, Finset.sum_nonneg fun k _ ↦ hb0 k⟩)
    fun h h' ↦ ?_).continuous
  refine (abs_localGroundEnergyOn_sub_le (ν := ν)
    (perturb_lower_bound hM₀ hb) (perturb_lower_bound hM₀ hb)
    (fun ζ ↦ abs_perturb_sub_perturb_le hb ζ) hM).trans ?_
  refine (Finset.sum_le_sum fun k _ ↦ ?_).trans_eq (Finset.sum_mul ..).symm
  rw [mul_comm (b k)]
  exact mul_le_mul_of_nonneg_right
    (by simpa [Real.dist_eq] using dist_le_pi_dist h h' k) (hb0 k)

end Perturbation

/-! ### Georgii (19.3): the vector `g(h)` of energetic disadvantages -/

section Gap

variable (ι : Type*) in
/-- **Georgii's `∂ℝ_+^N`**, the boundary of the positive octant: the vectors with non-negative
entries at least one of which vanishes.  For a finite index this is literally the topological
frontier of the octant, `nonnegBoundary_eq_frontier`. -/
def nonnegBoundary : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ ∃ i, z i = 0}

variable {ι : Type*}

@[simp] lemma mem_nonnegBoundary {z : ι → ℝ} :
    z ∈ nonnegBoundary ι ↔ (∀ i, 0 ≤ z i) ∧ ∃ i, z i = 0 := Iff.rfl

lemma zero_mem_nonnegBoundary [Nonempty ι] : (0 : ι → ℝ) ∈ nonnegBoundary ι :=
  ⟨fun _ ↦ le_rfl, ⟨Classical.arbitrary ι, rfl⟩⟩

/-- Georgii's notation is justified: `∂ℝ_+^N` really is the frontier of the positive octant. -/
lemma nonnegBoundary_eq_frontier [Finite ι] :
    nonnegBoundary ι = frontier {z : ι → ℝ | ∀ i, 0 ≤ z i} := by
  have hset : {z : ι → ℝ | ∀ i, 0 ≤ z i} = Set.univ.pi fun _ : ι ↦ Ici (0 : ℝ) := by
    ext z; simp [Pi.le_def]
  have hclosed : IsClosed {z : ι → ℝ | ∀ i, 0 ≤ z i} := by
    rw [hset]; exact isClosed_set_pi fun _ _ ↦ isClosed_Ici
  rw [frontier, hclosed.closure_eq, hset, interior_pi_set Set.finite_univ]
  ext z
  simp only [mem_nonnegBoundary, Set.mem_sdiff, Set.mem_pi, Set.mem_univ, forall_const,
    interior_Ici, Set.mem_Ici, Set.mem_Ioi, not_forall, not_lt]
  constructor
  · rintro ⟨hz, i, hi⟩
    exact ⟨hz, ⟨i, by simp [hi]⟩⟩
  · rintro ⟨hz, i, hi⟩
    exact ⟨hz, ⟨i, le_antisymm hi (hz i)⟩⟩

variable {ψ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} {G : ι → Set ((Fin d → Fin 2) → E)}

variable (ψ ν G) in
/-- **Georgii (19.3).**  The energetic disadvantage of the member `G_n` of the partition:
`g_n = λ-inf_{G_n} Φ_C - λ-inf_G Φ_C`, where `G = G_1 ∪ ⋯ ∪ G_N`. -/
def groundEnergyGap (n : ι) : ℝ :=
  localGroundEnergyOn ψ ν (G n) - localGroundEnergyOn ψ ν (⋃ m, G m)

variable {M₀ : ℝ}

lemma groundEnergyGap_nonneg (hψ : ∀ ζ, M₀ ≤ ψ ζ) {n : ι} (hG : cubeMeasure d ν (G n) ≠ 0) :
    0 ≤ groundEnergyGap ψ ν G n :=
  sub_nonneg.2 (localGroundEnergyOn_le_of_subset hψ (subset_iUnion G n) hG)

lemma exists_groundEnergyGap_eq_zero [Finite ι] [Nonempty ι] (hψ : Measurable ψ)
    (hψM : ∀ ζ, M₀ ≤ ψ ζ) (hG : ∀ n, cubeMeasure d ν (G n) ≠ 0) :
    ∃ n, groundEnergyGap ψ ν G n = 0 := by
  obtain ⟨n, hn⟩ := exists_localGroundEnergyOn_iUnion_eq hψ hψM hG
  exact ⟨n, by rw [groundEnergyGap, hn, sub_self]⟩

/-- **Georgii's "`g` maps into `∂ℝ_+^N`"**, the sentence after (19.3). -/
theorem groundEnergyGap_mem_nonnegBoundary [Finite ι] [Nonempty ι] (hψ : Measurable ψ)
    (hψM : ∀ ζ, M₀ ≤ ψ ζ) (hG : ∀ n, cubeMeasure d ν (G n) ≠ 0) :
    groundEnergyGap ψ ν G ∈ nonnegBoundary ι :=
  ⟨fun n ↦ groundEnergyGap_nonneg hψM (hG n), exists_groundEnergyGap_eq_zero hψ hψM hG⟩

/-- **Georgii's `g(0) = 0`**: assumption (19.1) says exactly that no member of the partition is
at an energetic disadvantage for the unperturbed potential. -/
theorem groundEnergyGap_eq_zero [Finite ι] [Nonempty ι] (hψ : Measurable ψ)
    (hψM : ∀ ζ, M₀ ≤ ψ ζ) (h : ∀ n, AttainsGroundEnergy ψ ν (G n)) :
    groundEnergyGap ψ ν G = 0 := by
  have hGpos : ∀ n, cubeMeasure d ν (G n) ≠ 0 := fun n ↦ (h n).measure_pos.ne'
  have hUnion : localGroundEnergyOn ψ ν (⋃ m, G m) = localGroundEnergy ψ ν := by
    rw [localGroundEnergyOn_iUnion hψ hψM hGpos]
    have : ∀ m, localGroundEnergyOn ψ ν (G m) = localGroundEnergy ψ ν :=
      fun m ↦ (h m).localGroundEnergyOn_eq hψ hψM
    simp [this]
  funext n
  rw [groundEnergyGap, hUnion, (h n).localGroundEnergyOn_eq hψ hψM, sub_self]
  rfl

end Gap

/-! ### Georgii, Definition (19.4): potentials that resolve the partition -/

section Resolve

variable {N : ℕ} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E}
  {Ψ : Fin N → ((Fin d → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin d → Fin 2) → E)}
  {b : Fin N → ℝ} {M₀ : ℝ}

variable (φ ν Ψ G) in
/-- Georgii's map `g` of (19.3), as a function of the perturbation parameter `h`. -/
def perturbGap (h : Fin N → ℝ) : Fin (N + 1) → ℝ := groundEnergyGap (perturb φ Ψ h) ν G

lemma measure_iUnion_ne_zero_of_forall (hGpos : ∀ n, cubeMeasure d ν (G n) ≠ 0) :
    cubeMeasure d ν (⋃ n, G n) ≠ 0 :=
  fun h0 ↦ hGpos 0 (measure_mono_null (Set.subset_iUnion G 0) h0)

/-- **Georgii's "`g` is a continuous mapping from `ℝ^{N-1}` to `∂ℝ_+^N`"**, the sentence after
(19.3): continuity. -/
theorem continuous_perturbGap (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hb0 : ∀ k, 0 ≤ b k) (hGpos : ∀ n, cubeMeasure d ν (G n) ≠ 0) :
    Continuous (perturbGap φ ν Ψ G) := by
  apply continuous_pi
  intro n
  simp only [perturbGap, groundEnergyGap]
  exact (continuous_localGroundEnergyOn_perturb hM₀ hb hb0 (hGpos n)).sub
    (continuous_localGroundEnergyOn_perturb hM₀ hb hb0 (measure_iUnion_ne_zero_of_forall hGpos))

/-- **Georgii's "`g` is a mapping to `∂ℝ_+^N`"**, the sentence after (19.3): the image. -/
theorem perturbGap_mem_nonnegBoundary (hφ : Measurable φ) (hΨm : ∀ k, Measurable (Ψ k))
    (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGpos : ∀ n, cubeMeasure d ν (G n) ≠ 0) (h : Fin N → ℝ) :
    perturbGap φ ν Ψ G h ∈ nonnegBoundary (Fin (N + 1)) :=
  groundEnergyGap_mem_nonnegBoundary (measurable_perturb hφ hΨm h)
    (perturb_lower_bound hM₀ hb) hGpos

/-- **Georgii's `g(0) = 0`**: assumption (19.1) says exactly that the unperturbed potential
puts no member of the partition at an energetic disadvantage. -/
theorem perturbGap_zero (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) : perturbGap φ ν Ψ G 0 = 0 := by
  rw [perturbGap, perturb_zero]
  exact groundEnergyGap_eq_zero hφ hM₀ h191

variable (φ ν Ψ G) in
/-- **Georgii, Definition (19.4)**, on a fixed neighbourhood `U` of the origin: the bounded
`C`-potentials `Φ^1, …, Φ^{N-1}` *resolve* the partition `{G_1, …, G_N}` on `U` if

* (i) `g` is a homeomorphism from `U` onto a neighbourhood of the origin in `∂ℝ_+^N` — here:
  the image `g(U)` is a neighbourhood of the origin *within* `∂ℝ_+^N`, and `g` has a continuous
  left inverse on it, which together with the continuity of `g` (`continuous_perturbGap`, which
  is automatic from the boundedness of the `Φ^n` and so is not a field here) is exactly
  Georgii's condition; and
* (ii) `inf_{h ∈ U} λ^C(G_δ(Φ^h)) > 0` for every `δ > 0`. -/
structure ResolvesOn (U : Set (Fin N → ℝ)) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `U` is a neighbourhood of the origin. -/
  zero_mem : (0 : Fin N → ℝ) ∈ U
  /-- Georgii (19.4)(i), first half: `g(U)` is a neighbourhood of the origin in `∂ℝ_+^N`. -/
  image_mem_nhdsWithin :
    perturbGap φ ν Ψ G '' U ∈ 𝓝[nonnegBoundary (Fin (N + 1))] (0 : Fin (N + 1) → ℝ)
  /-- Georgii (19.4)(i), second half: `g` restricted to `U` has a continuous inverse. -/
  exists_continuousOn_leftInverse : ∃ γ : (Fin (N + 1) → ℝ) → (Fin N → ℝ),
    ContinuousOn γ (perturbGap φ ν Ψ G '' U) ∧ ∀ h ∈ U, γ (perturbGap φ ν Ψ G h) = h
  /-- Georgii (19.4)(ii): `inf_{h ∈ U} λ^C(G_δ(Φ^h)) > 0` for all `δ > 0`. -/
  exists_measure_localGroundStates_pos : ∀ δ : ℝ, 0 < δ → ∃ c : ℝ≥0∞, 0 < c ∧
    ∀ h ∈ U, c ≤ cubeMeasure d ν (localGroundStates (perturb φ Ψ h) ν δ)

variable (φ ν Ψ G) in
/-- **Georgii, Definition (19.4).**  The bounded `C`-potentials `Φ^1, …, Φ^{N-1}` *resolve* the
partition `{G_1, …, G_N}` of the local ground states of `Φ`. -/
def Resolves : Prop := ∃ U, ResolvesOn φ ν Ψ G U

end Resolve

/-! ### Georgii, Comment (19.5)(1): the affine model of `g`

Georgii's device: take `Φ^n_C` constant on `G_n` and equal to a *different* constant on
`G ∖ G_n`.  Then `g` is the explicit piecewise affine map `h ↦ (h_n δ_n - min_k h_k δ_k)_n`,
which is a homeomorphism of `ℝ^{N-1}` onto the whole of `∂ℝ_+^N`. -/

section GapModel

variable {N : ℕ} {jump : Fin N → ℝ} {h : Fin N → ℝ}

private lemma ciInf_add_const {ι : Type*} [Finite ι] [Nonempty ι] (f : ι → ℝ) (a : ℝ) :
    ⨅ i, (f i + a) = (⨅ i, f i) + a := by
  obtain ⟨j, hj⟩ := Finite.exists_min f
  have h1 : (⨅ i, f i) = f j := le_antisymm (ciInf_le (Finite.bddBelow_range _) j) (le_ciInf hj)
  have h2 : (⨅ i, (f i + a)) = f j + a :=
    le_antisymm (ciInf_le (Finite.bddBelow_range _) j) (le_ciInf fun i ↦ by linarith [hj i])
  rw [h1, h2]

lemma ciInf_eq_zero_of_mem_nonnegBoundary {ι : Type*} [Finite ι] [Nonempty ι] {z : ι → ℝ}
    (hz : z ∈ nonnegBoundary ι) : ⨅ i, z i = 0 := by
  obtain ⟨hnn, i, hi⟩ := hz
  exact le_antisymm (hi ▸ ciInf_le (Finite.bddBelow_range _) i) (le_ciInf hnn)

variable (jump) in
/-- Georgii's vector `(h_n δ_n)_{1 ≤ n ≤ N}` of Comment (19.5)(1), with his convention
`h_N = 0`. -/
def jumpVector (h : Fin N → ℝ) : Fin (N + 1) → ℝ := Fin.snoc (fun k ↦ h k * jump k) 0

@[simp] lemma jumpVector_castSucc (k : Fin N) :
    jumpVector jump h k.castSucc = h k * jump k := Fin.snoc_castSucc ..

@[simp] lemma jumpVector_last : jumpVector jump h (Fin.last N) = 0 := Fin.snoc_last ..

@[simp] lemma jumpVector_zero : jumpVector jump (0 : Fin N → ℝ) = 0 := by
  funext n
  induction n using Fin.lastCases with
  | last => simp
  | cast k => simp

variable (jump) in
/-- **Georgii's `g` of Comment (19.5)(1)**: `h ↦ (h_n δ_n - min_{1 ≤ k ≤ N} h_k δ_k)_n`, with
`h_N δ_N = 0`. -/
def gapModel (h : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  fun n ↦ jumpVector jump h n - ⨅ m, jumpVector jump h m

variable (jump) in
/-- **Georgii's `g^{-1}(z) = ((z_n - z_N) δ_n^{-1})_{1 ≤ n < N}`** of Comment (19.5)(1). -/
def gapModelInv (z : Fin (N + 1) → ℝ) : Fin N → ℝ :=
  fun k ↦ (z k.castSucc - z (Fin.last N)) / jump k

lemma gapModel_apply (n : Fin (N + 1)) :
    gapModel jump h n = jumpVector jump h n - ⨅ m, jumpVector jump h m := rfl

@[simp] lemma gapModel_zero : gapModel jump (0 : Fin N → ℝ) = 0 := by
  funext n
  simp [gapModel]

/-- `g` maps into `∂ℝ_+^N`. -/
theorem gapModel_mem_nonnegBoundary (h : Fin N → ℝ) :
    gapModel jump h ∈ nonnegBoundary (Fin (N + 1)) := by
  obtain ⟨j, hj⟩ := Finite.exists_min (jumpVector jump h)
  refine ⟨fun n ↦ sub_nonneg.2 (ciInf_le (Finite.bddBelow_range _) n), ⟨j, ?_⟩⟩
  rw [gapModel_apply, le_antisymm (ciInf_le (Finite.bddBelow_range _) j) (le_ciInf hj), sub_self]

theorem gapModelInv_gapModel (hjump : ∀ k, jump k ≠ 0) (h : Fin N → ℝ) :
    gapModelInv jump (gapModel jump h) = h := by
  funext k
  rw [gapModelInv, gapModel_apply, gapModel_apply, jumpVector_castSucc, jumpVector_last,
    show (h k * jump k - ⨅ m, jumpVector jump h m) - (0 - ⨅ m, jumpVector jump h m)
      = h k * jump k from by ring]
  rw [mul_div_assoc, div_self (hjump k), mul_one]

theorem gapModel_gapModelInv (hjump : ∀ k, jump k ≠ 0) {z : Fin (N + 1) → ℝ}
    (hz : z ∈ nonnegBoundary (Fin (N + 1))) : gapModel jump (gapModelInv jump z) = z := by
  have hvec : ∀ n, jumpVector jump (gapModelInv jump z) n = z n - z (Fin.last N) := by
    intro n
    induction n using Fin.lastCases with
    | last => simp
    | cast k => rw [jumpVector_castSucc, gapModelInv, div_mul_cancel₀ _ (hjump k)]
  funext n
  rw [gapModel_apply, hvec n]
  have hinf : (⨅ m, jumpVector jump (gapModelInv jump z) m) = -z (Fin.last N) := by
    calc (⨅ m, jumpVector jump (gapModelInv jump z) m)
        = ⨅ m, (z m + -z (Fin.last N)) := by simp only [hvec, sub_eq_add_neg]
      _ = (⨅ m, z m) + -z (Fin.last N) := ciInf_add_const _ _
      _ = -z (Fin.last N) := by rw [ciInf_eq_zero_of_mem_nonnegBoundary hz, zero_add]
  rw [hinf]
  ring

theorem continuous_jumpVector_apply (n : Fin (N + 1)) :
    Continuous fun h : Fin N → ℝ ↦ jumpVector jump h n := by
  induction n using Fin.lastCases with
  | last =>
    simp only [jumpVector_last]
    exact continuous_const
  | cast k =>
    simp only [jumpVector_castSucc]
    exact (continuous_apply k).mul continuous_const

theorem continuous_gapModel : Continuous (gapModel jump) := by
  refine continuous_pi fun n ↦ (continuous_jumpVector_apply n).sub ?_
  have heq : (fun h : Fin N → ℝ ↦ ⨅ m, jumpVector jump h m)
      = fun h ↦ Finset.univ.inf' Finset.univ_nonempty fun m ↦ jumpVector jump h m := by
    funext h
    rw [Finset.inf'_univ_eq_ciInf]
  rw [heq]
  exact Continuous.finset_inf'_apply _ fun m _ ↦ continuous_jumpVector_apply m

theorem continuous_gapModelInv : Continuous (gapModelInv jump) := by
  apply continuous_pi
  intro k
  simp only [gapModelInv]
  exact ((continuous_apply (Fin.castSucc k)).sub
    (continuous_apply (Fin.last N))).div_const _

variable (jump) in
/-- **Georgii, Comment (19.5)(1)**: with `Φ^n_C` constant on `G_n` and equal to a different
constant on `G ∖ G_n`, the map `g` of (19.3) is the homeomorphism
`h ↦ (h_n δ_n - min_k h_k δ_k)_n` of `ℝ^{N-1}` onto the whole of `∂ℝ_+^N`, with inverse
`z ↦ ((z_n - z_N) δ_n^{-1})_{n < N}`. -/
def gapHomeomorph (hjump : ∀ k, jump k ≠ 0) :
    (Fin N → ℝ) ≃ₜ nonnegBoundary (Fin (N + 1)) where
  toFun h := ⟨gapModel jump h, gapModel_mem_nonnegBoundary h⟩
  invFun z := gapModelInv jump z.1
  left_inv h := gapModelInv_gapModel hjump h
  right_inv z := Subtype.ext (gapModel_gapModelInv hjump z.2)
  continuous_toFun := continuous_gapModel.subtype_mk _
  continuous_invFun := continuous_gapModelInv.comp continuous_subtype_val

@[simp] lemma coe_gapHomeomorph (hjump : ∀ k, jump k ≠ 0) (h : Fin N → ℝ) :
    ((gapHomeomorph jump hjump h : nonnegBoundary (Fin (N + 1))) : Fin (N + 1) → ℝ)
      = gapModel jump h := rfl

end GapModel

/-! ### Georgii, Comment (19.5)(1): the construction of resolving potentials -/

section ConstOn

variable {N : ℕ} {φ : ((Fin d → Fin 2) → E) → ℝ} {ν : Measure E} [IsProbabilityMeasure ν]
  {Ψ : Fin N → ((Fin d → Fin 2) → E) → ℝ} {G : Fin (N + 1) → Set ((Fin d → Fin 2) → E)}
  {b c jump h : Fin N → ℝ} {M₀ ε : ℝ}

omit [MeasurableSpace E] in
/-- **Georgii, Comment (19.5)(1), the first display**: `Φ^h_C - Φ_C` is constant on each member
of the partition, with the value `∑_k h_k c_k + h_n δ_n` (and `h_N δ_N = 0`). -/
theorem perturb_eq_of_mem (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    {n : Fin (N + 1)} {ζ : (Fin d → Fin 2) → E} (hζ : ζ ∈ G n) (h : Fin N → ℝ) :
    perturb φ Ψ h ζ = φ ζ + ((∑ k, h k * c k) + jumpVector jump h n) := by
  classical
  have hterm : ∀ k ∈ Finset.univ,
      h k * Ψ k ζ = h k * c k + (if n = k.castSucc then h k * jump k else 0) := by
    intro k _
    split_ifs with hk
    · subst hk
      rw [hon k ζ hζ]
      ring
    · rw [hoff k ζ ⟨Set.mem_iUnion.2 ⟨n, hζ⟩, Set.disjoint_left.1 (hdisj hk) hζ⟩]
      ring
  have hsum : ∑ k, (if n = k.castSucc then h k * jump k else 0) = jumpVector jump h n := by
    induction n using Fin.lastCases with
    | last =>
      have hne : ∀ k : Fin N, ¬ (Fin.last N = k.castSucc) :=
        fun k hk ↦ (Fin.castSucc_lt_last k).ne hk.symm
      simp [hne]
    | cast j =>
      rw [jumpVector_castSucc, Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        split_ifs with hc
        · exact absurd (Fin.castSucc_injective _ hc).symm hk
        · rfl
      · intro hj
        exact absurd (Finset.mem_univ j) hj
  rw [perturb_apply, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hsum]

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Comment (19.5)(1)**: `λ-inf_{G_n} Φ^h_C = m_Φ + h_n δ_n + ∑_k h_k c_k`. -/
theorem localGroundEnergyOn_perturb_const_on (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) (h : Fin N → ℝ) (n : Fin (N + 1)) :
    localGroundEnergyOn (perturb φ Ψ h) ν (G n)
      = localGroundEnergy φ ν + ((∑ k, h k * c k) + jumpVector jump h n) := by
  have hGne : cubeMeasure d ν (G n) ≠ 0 := (h191 n).measure_pos.ne'
  have hNZ : NeZero ((cubeMeasure d ν).restrict (G n)) := neZero_restrict_of_measure_ne_zero hGne
  have hcongr : ∀ᵐ ζ ∂(cubeMeasure d ν).restrict (G n),
      perturb φ Ψ h ζ = φ ζ + ((∑ k, h k * c k) + jumpVector jump h n) := by
    filter_upwards [ae_restrict_mem (hGmeas n)] with ζ hζ
    exact perturb_eq_of_mem hdisj hon hoff hζ h
  rw [localGroundEnergyOn, essInf_congr_ae hcongr,
    essInf_add_const (Eventually.of_forall hM₀) _]
  rw [show essInf φ ((cubeMeasure d ν).restrict (G n)) = localGroundEnergyOn φ ν (G n) from rfl,
    (h191 n).localGroundEnergyOn_eq hφ hM₀]

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Comment (19.5)(1)**: `λ-inf_G Φ^h_C = m_Φ + min_k h_k δ_k + ∑_k h_k c_k`. -/
theorem localGroundEnergyOn_perturb_iUnion_const_on (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hΨm : ∀ k, Measurable (Ψ k)) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) (h : Fin N → ℝ) :
    localGroundEnergyOn (perturb φ Ψ h) ν (⋃ n, G n)
      = localGroundEnergy φ ν + ((∑ k, h k * c k) + ⨅ n, jumpVector jump h n) := by
  rw [localGroundEnergyOn_iUnion (measurable_perturb hφ hΨm h) (perturb_lower_bound hM₀ hb)
    (fun n ↦ (h191 n).measure_pos.ne')]
  simp only [localGroundEnergyOn_perturb_const_on (c := c) (jump := jump) hφ hM₀ hGmeas hdisj
    hon hoff h191 h]
  rw [show (fun n : Fin (N + 1) ↦ localGroundEnergy φ ν +
      ((∑ k, h k * c k) + jumpVector jump h n))
      = fun n ↦ jumpVector jump h n + (localGroundEnergy φ ν + ∑ k, h k * c k) from by
    funext n; ring, ciInf_add_const]
  ring

omit [IsProbabilityMeasure ν] in
/-- **Georgii, Comment (19.5)(1), the second display**: `g(h) = (h_n δ_n - min_k h_k δ_k)_n`. -/
theorem perturbGap_eq_gapModel (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hΨm : ∀ k, Measurable (Ψ k)) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) (h : Fin N → ℝ) :
    perturbGap φ ν Ψ G h = gapModel jump h := by
  funext n
  rw [perturbGap, groundEnergyGap,
    localGroundEnergyOn_perturb_const_on (c := c) (jump := jump) hφ hM₀ hGmeas hdisj hon hoff
      h191 h n,
    localGroundEnergyOn_perturb_iUnion_const_on (c := c) (jump := jump) hφ hM₀ hΨm hb hGmeas
      hdisj hon hoff h191 h, gapModel_apply]
  ring

/-! Georgii's verification of condition (19.4)(ii). -/

/-- **Georgii, Comment (19.5)(1)**: for a perturbation smaller than `ε/2`, where `ε` is small
enough that `G_ε(Φ) ⊆ G`, the perturbed potential still attains its ground state energy on
`G = G_1 ∪ ⋯ ∪ G_N`: `λ-inf_G Φ^h_C = m_{Φ^h}`.

This uses only assumption (19.1) and the boundedness of the perturbations, not the special
shape of `Φ^1, …, Φ^{N-1}`. -/
theorem localGroundEnergyOn_perturb_iUnion_eq_localGroundEnergy (hφ : Measurable φ)
    (hM₀ : ∀ ζ, M₀ ≤ φ ζ) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k) (hGmeas : ∀ n, MeasurableSet (G n))
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n))
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) (hh : ∑ k, |h k| * b k < ε / 2) :
    localGroundEnergyOn (perturb φ Ψ h) ν (⋃ n, G n) = localGroundEnergy (perturb φ Ψ h) ν := by
  have hSmeas : MeasurableSet (⋃ n, G n) := MeasurableSet.iUnion hGmeas
  have hSpos : cubeMeasure d ν (⋃ n, G n) ≠ 0 := fun h0 ↦
    (h191 0).measure_pos.ne' (measure_mono_null (Set.subset_iUnion G 0) h0)
  have hψM : ∀ ζ, M₀ - ∑ k, |h k| * b k ≤ perturb φ Ψ h ζ := perturb_lower_bound hM₀ hb
  have hSφ : localGroundEnergyOn φ ν (⋃ n, G n) = localGroundEnergy φ ν := by
    rw [localGroundEnergyOn_iUnion hφ hM₀ (fun n ↦ (h191 n).measure_pos.ne')]
    simp [fun n ↦ (h191 n).localGroundEnergyOn_eq hφ hM₀]
  have hupper : localGroundEnergyOn (perturb φ Ψ h) ν (⋃ n, G n)
      ≤ localGroundEnergy φ ν + ε / 2 := by
    have hlip := abs_localGroundEnergyOn_sub_le (ν := ν) (M := ⋃ n, G n) hψM hM₀
      (fun ζ ↦ (abs_perturb_sub_le hb ζ).trans hh.le) hSpos
    have := (abs_le.1 hlip).2
    rw [hSφ] at this
    linarith
  refine le_antisymm ?_ (localGroundEnergy_le_localGroundEnergyOn hψM hSpos)
  refine le_essInf_of_ae_le _ ?_ (isCoboundedUnder_ge_ae _)
  have h1 : ∀ᵐ ζ ∂cubeMeasure d ν, ζ ∈ (⋃ n, G n) →
      localGroundEnergyOn (perturb φ Ψ h) ν (⋃ n, G n) ≤ perturb φ Ψ h ζ := by
    rw [← ae_restrict_iff' hSmeas]
    exact ae_localGroundEnergyOn_le hψM _
  filter_upwards [h1] with ζ hζ
  by_cases hmem : ζ ∈ ⋃ n, G n
  · exact hζ hmem
  · have hφζ : localGroundEnergy φ ν + ε < φ ζ := by
      by_contra hcon
      exact hmem (hGε (not_lt.1 hcon))
    have hd := (abs_le.1 (abs_perturb_sub_le (φ := φ) (Ψ := Ψ) (h := h) hb ζ)).1
    linarith

/-- **Georgii, Comment (19.5)(1)**: `G_δ(Φ^h) ∩ G_n = G_δ(Φ) ∩ G_n` for any member `G_n` which
carries no energetic disadvantage under `Φ^h`.  This is the identity behind (19.4)(ii). -/
theorem localGroundStates_perturb_inter_eq (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (h191 : ∀ n, AttainsGroundEnergy φ ν (G n))
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) (hh : ∑ k, |h k| * b k < ε / 2)
    {n : Fin (N + 1)} (hgap : perturbGap φ ν Ψ G h n = 0) (δ : ℝ) :
    localGroundStates (perturb φ Ψ h) ν δ ∩ G n = localGroundStates φ ν δ ∩ G n := by
  set A : ℝ := (∑ k, h k * c k) + jumpVector jump h n with hA
  have hmn : localGroundEnergy (perturb φ Ψ h) ν = localGroundEnergy φ ν + A := by
    rw [← localGroundEnergyOn_perturb_iUnion_eq_localGroundEnergy (Ψ := Ψ) hφ hM₀ hb hGmeas
      h191 hGε hh]
    have : localGroundEnergyOn (perturb φ Ψ h) ν (G n)
        - localGroundEnergyOn (perturb φ Ψ h) ν (⋃ m, G m) = 0 := hgap
    rw [← sub_eq_zero.1 this,
      localGroundEnergyOn_perturb_const_on (c := c) (jump := jump) hφ hM₀ hGmeas hdisj hon hoff
        h191 h n]
  ext ζ
  simp only [Set.mem_inter_iff, mem_localGroundStates, and_congr_left_iff]
  intro hζ
  rw [perturb_eq_of_mem hdisj hon hoff hζ h, hmn]
  constructor <;> intro hle <;> linarith

/-- **Georgii, Comment (19.5)(1).**  Bounded `C`-potentials `Φ^1, …, Φ^{N-1}` whose cube
interactions satisfy `Φ^n_C = c_n + δ_n` on `G_n` and `Φ^n_C = c_n` on `G ∖ G_n`, with
`δ_n ≠ 0`, resolve the partition `{G_1, …, G_N}` — on the explicit neighbourhood
`U = {h : ∑_k |h_k| ‖Φ^k_C‖ < ε/2}` of the origin, where `ε > 0` is small enough that
`G_ε(Φ) ⊆ G`.

Georgii's proof, in his order: `g` is the affine model `gapModel`
(`perturbGap_eq_gapModel`), which is a homeomorphism of `ℝ^{N-1}` onto the whole of `∂ℝ_+^N`
(`gapHomeomorph`), so (19.4)(i) holds on every open neighbourhood of the origin; and for
(19.4)(ii), the perturbed potential still attains its ground state energy on `G`
(`localGroundEnergyOn_perturb_iUnion_eq_localGroundEnergy`), so on the member `G_n` with
`g_n(h) = 0` its local `δ`-ground states are those of `Φ`
(`localGroundStates_perturb_inter_eq`), whence
`λ^C(G_δ(Φ^h)) ≥ min_n λ^C(G_δ(Φ) ∩ G_n) > 0` by (19.1). -/
theorem resolvesOn_of_const_on (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hΨm : ∀ k, Measurable (Ψ k)) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (hjump : ∀ k, jump k ≠ 0) (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) :
    ResolvesOn φ ν Ψ G {h : Fin N → ℝ | ∑ k, |h k| * b k < ε / 2} := by
  have hgapfun : perturbGap φ ν Ψ G = gapModel jump := by
    funext h
    exact perturbGap_eq_gapModel (c := c) hφ hM₀ hΨm hb hGmeas hdisj hon hoff h191 h
  have hcont : Continuous fun h : Fin N → ℝ ↦ ∑ k, |h k| * b k :=
    continuous_finsetSum _ fun k _ ↦ ((continuous_apply k).abs).mul continuous_const
  have hUopen : IsOpen {h : Fin N → ℝ | ∑ k, |h k| * b k < ε / 2} :=
    isOpen_lt hcont continuous_const
  have hU0 : (0 : Fin N → ℝ) ∈ {h : Fin N → ℝ | ∑ k, |h k| * b k < ε / 2} := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, abs_zero, zero_mul, Finset.sum_const_zero]
    linarith
  refine ⟨hUopen, hU0, ?_, ?_, ?_⟩
  · rw [hgapfun]
    have hpre : (Subtype.val : nonnegBoundary (Fin (N + 1)) → (Fin (N + 1) → ℝ)) ⁻¹'
        (gapModel jump '' {h : Fin N → ℝ | ∑ k, |h k| * b k < ε / 2})
          = gapHomeomorph jump hjump '' {h : Fin N → ℝ | ∑ k, |h k| * b k < ε / 2} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_image]
      exact ⟨fun ⟨w, hw, hwz⟩ ↦ ⟨w, hw, Subtype.ext hwz⟩,
        fun ⟨w, hw, hwz⟩ ↦ ⟨w, hw, by rw [← hwz]; rfl⟩⟩
    rw [nhdsWithin_eq_map_subtype_coe zero_mem_nonnegBoundary, Filter.mem_map, hpre]
    exact ((gapHomeomorph jump hjump).isOpen_image.2 hUopen).mem_nhds
      ⟨0, hU0, Subtype.ext (by simp)⟩
  · refine ⟨gapModelInv jump, continuous_gapModelInv.continuousOn, fun h _ ↦ ?_⟩
    rw [hgapfun]
    exact gapModelInv_gapModel hjump h
  · intro δ hδ
    obtain ⟨m₀, hm₀⟩ := Finite.exists_min fun m : Fin (N + 1) ↦
      cubeMeasure d ν (localGroundStates φ ν δ ∩ G m)
    refine ⟨cubeMeasure d ν (localGroundStates φ ν δ ∩ G m₀), ?_, fun h hh ↦ ?_⟩
    · rw [Set.inter_comm]
      exact h191 m₀ δ hδ
    · obtain ⟨n, hn⟩ := exists_groundEnergyGap_eq_zero (measurable_perturb hφ hΨm h)
        (perturb_lower_bound hM₀ hb) (fun n ↦ (h191 n).measure_pos.ne')
      calc cubeMeasure d ν (localGroundStates φ ν δ ∩ G m₀)
          ≤ cubeMeasure d ν (localGroundStates φ ν δ ∩ G n) := hm₀ n
        _ = cubeMeasure d ν (localGroundStates (perturb φ Ψ h) ν δ ∩ G n) := by
            rw [localGroundStates_perturb_inter_eq (c := c) (jump := jump) hφ hM₀ hb hGmeas
              hdisj hon hoff h191 hGε hh hn δ]
        _ ≤ cubeMeasure d ν (localGroundStates (perturb φ Ψ h) ν δ) :=
            measure_mono Set.inter_subset_left

/-- **Georgii, Comment (19.5)(1)**, as the statement that Definition (19.4) holds. -/
theorem resolves_of_const_on (hφ : Measurable φ) (hM₀ : ∀ ζ, M₀ ≤ φ ζ)
    (hΨm : ∀ k, Measurable (Ψ k)) (hb : ∀ k ζ, |Ψ k ζ| ≤ b k)
    (hGmeas : ∀ n, MeasurableSet (G n)) (hdisj : Pairwise (Function.onFun Disjoint G))
    (hon : ∀ k, ∀ ζ ∈ G k.castSucc, Ψ k ζ = c k + jump k)
    (hoff : ∀ k, ∀ ζ ∈ (⋃ m, G m) \ G k.castSucc, Ψ k ζ = c k)
    (hjump : ∀ k, jump k ≠ 0) (h191 : ∀ n, AttainsGroundEnergy φ ν (G n)) (hε : 0 < ε)
    (hGε : localGroundStates φ ν ε ⊆ ⋃ n, G n) :
    Resolves φ ν Ψ G :=
  ⟨_, resolvesOn_of_const_on (c := c) (jump := jump) hφ hM₀ hΨm hb hGmeas hdisj hon hoff
    hjump h191 hε hGε⟩

end ConstOn

/-! ### Georgii, Comment (19.5)(2): a finite state space -/

/-- **Georgii, Comment (19.5)(2), first sentence.**  Condition (19.4)(ii) is trivially satisfied
when `E` is finite and `λ` is counting measure — indeed for *every* family of cube interactions,
with the uniform bound `(min_x λ̃{x})^{|C|}`: the local `δ`-ground states of a cube interaction
are never empty, and over a finite state space with an a priori measure of full support every
non-empty set of cube configurations has at least that much `λ^C`-measure. -/
theorem exists_measure_localGroundStates_pos_of_finite {E : Type*} [MeasurableSpace E] [Finite E]
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : ∀ x : E, ν {x} ≠ 0) (d : ℕ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ (ψ : ((Fin d → Fin 2) → E) → ℝ) (δ : ℝ), 0 < δ →
      c ≤ cubeMeasure d ν (localGroundStates ψ ν δ) := by
  have : Nonempty E := ν.nonempty_of_neZero
  obtain ⟨x₀, hx₀⟩ := Finite.exists_min fun x : E ↦ ν {x}
  refine ⟨ν {x₀} ^ (2 ^ d), pos_iff_ne_zero.2 (pow_ne_zero _ (hν x₀)), fun ψ δ hδ ↦ ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ζ, M ≤ ψ ζ := by
    obtain ⟨ζ₀, hζ₀⟩ := Finite.exists_min ψ
    exact ⟨ψ ζ₀, hζ₀⟩
  obtain ⟨a, ha⟩ : (localGroundStates ψ ν δ).Nonempty :=
    nonempty_of_measure_ne_zero (measure_localGroundStates_pos hM hδ).ne'
  refine le_trans ?_ (measure_mono (Set.singleton_subset_iff.2 ha))
  rw [← Set.univ_pi_singleton a, cubeMeasure, Measure.pi_pi]
  calc ν {x₀} ^ (2 ^ d) = ∏ _c : Fin d → Fin 2, ν {x₀} := by
        rw [Finset.prod_const, Finset.card_univ]
        congr 1
        simp
    _ ≤ ∏ c : Fin d → Fin 2, ν {a c} := Finset.prod_le_prod' fun c _ ↦ hx₀ (a c)

end MeasureTheory.GibbsMeasure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.BoundaryLaw
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import GibbsMeasure.Model.MarkovChainInt
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.ExtremeDecomposition
public import GibbsMeasure.Specification.MarkovIntUniqueness

/-!
# Georgii §11.1, from Theorem (11.9)(b) on: Markov chains in `𝒢(Q)`, shift invariance, and the
periodicity argument of Theorem (11.15)

Sites `ℤ`, a countable state space `E`, counting measure, a positive matrix `Q` with finite
powers (Georgii (11.1)), its specification `γ^Q = transferSpecification Q hQ`, and the boundary
laws `{ℓ_i, r_i}` of Definition (11.8) with their measures (11.10) (`boundaryLawMeasure`).

## Main declarations

* `isMarkovChain_ofMatrix_of_forall_intervalCylinder`,
`IsMarkovChain.measure_intervalCylinder_succ`:
  on a countable state space, `μ` is a Markov chain with transition matrices `p_i` (Definition
  (10.4)) iff `μ(σ_a = x_a, …, σ_{b+1} = x_{b+1}) = μ(σ_a = x_a, …, σ_b = x_b) p_{b+1}(x_b,
      x_{b+1})`.
* `transitionMatrix Q r i` — **Georgii (11.11)**, `P_i(x, y) = Q(x, y) r_i(y) / r_{i-1}(x)`;
  `IsBoundaryLaw.isMarkovChain_boundaryLawMeasure`: the measure (11.10) of a boundary law is a
  Markov chain with these transition matrices (the "Markov chain" clause of Theorem (11.9)(a)).
* `IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure` — **Georgii Theorem (11.9)(b)**:
  every Markov chain `μ ∈ 𝒢(Q)` is the measure (11.10) of a boundary law for `Q`, whose right
  vectors satisfy (11.11); `IsMarkovChain.mul_mul_eq_of_isGibbsMeasure` is the identity **(11.12)**.
* `IsBoundaryLaw.boundaryLawMeasure_map_shift`: the shift `θ_j(μ)` of the measure of a boundary
  law is the measure of the shifted boundary law `{ℓ_{i-j}, r_{i-j}}`;
  `IsBoundaryLaw.boundaryLawMeasure_map_shift_eq_self_of_periodic`: if `ℓ_{i-p} = c ℓ_i` and
  `r_{i+p} = c r_i` then `θ_p(μ) = μ`.
* `IsBoundaryLaw.tsum_left_mul_pow`, `IsBoundaryLaw.tsum_pow_mul_right`: `ℓ_i Q^n = ℓ_{i+n}` and
  `Q^n r_{i+n} = r_i`.
* `isBoundaryLaw_const`, `stationaryChain_mem_invariantG` — the "if" half of **Georgii Theorem
  (11.13)**: if `Q ~ P` for a positive stochastic matrix `P` with an invariant probability vector
  `α` (Georgii: `P` positive recurrent), then Georgii's `μ_P` — the measure of the boundary law
  `ℓ_i = α`, `r_i = 1` — is a shift-invariant Gibbs measure for `γ^Q`, and a Markov chain with
  transition matrix `P`; in particular `𝒢_Θ(Q) ≠ ∅`.
* `IsBoundaryLaw.mul_left_sub_lt`, `IsBoundaryLaw.mul_right_add_lt` — **Georgii (11.16)**.
* `IsBoundaryLaw.boundaryLawMeasure_map_shift_eq_self_of_mem_extremePoints` — **the argument of
  Georgii Theorem (11.15)**: if `inf_x Q^p(x, x) > 0` and the measure `μ` of a boundary law is
  extreme in `𝒢(Q)`, then `θ_p(μ) = μ`. Georgii applies this to an arbitrary `μ ∈ ex 𝒢(Q)`
  through Theorem (11.9)(c), which rests on Theorem (10.21) (§10.2, not in the library); the
  hypothesis "`μ` is the measure of a boundary law" is exactly what (11.9)(c) would supply.
* `exists_pos_lt_pow_factorial_apply_of_le_sum`: Georgii's inequality
  `inf_x Q^{N!}(x, x) ≥ N^{-N!} (inf_x ∑_{n=1}^N 1 ∧ Q^n(x, x))^{N!}`, the first display in the
  proof of (11.15); `ProbabilityTheory.Kernel.pow_apply_singleton_mul_le` is the
  supermultiplicativity `κ^m(x,x) κ^n(x,x) ≤ κ^{m+n}(x,x)` noted after (11.6), for any kernel
  on a countable space.
* `lazy_stochastic`, `le_lazy_apply_self`, `tsum_mul_lazy`, `lazy_isTransferMatrix`,
  `iInf_lazy_apply_self_pos`, `boundaryLawMeasure_const_lazy_mem_invariantG` — **Georgii Comment
  (11.18)(1)**: `Q = tP + (1 - t)I` is a transfer matrix with `inf_x Q(x, x) ≥ 1 - t > 0` and the
  same invariant vectors as `P`, so `Q` satisfies both hypotheses that Corollary (11.17) combines:
  the existence hypothesis of Theorem (11.13) and the periodicity hypothesis of Theorem
  (11.15)/(11.16) at `p = 1`. (Corollary (11.17) itself is not provable here; see below.)

## What is not here, and exactly why

**Theorem (11.9)(c)** (a representing boundary law for every `μ ∈ ex 𝒢(Q)`), the **"only if" half
and the uniqueness clause of Theorem (11.13)**, **Corollary (11.14)**, **Theorem (11.15)** for an
arbitrary extreme point of `𝒢(Q)` (only the case where `μ` is already known to be the measure of a
boundary law is proved above), **Corollary (11.17)**, **Comment (11.18)(3)** and **Corollary
(11.19)** all go, in Georgii's own proof, through Theorem (10.21) and Theorem (10.35) applied to
`γ^Q` — via Example (10.24)(2), i.e. with `ρ = transferWeight Q` as the Markovian λ-modification.
None of these are here, and the obstruction is more precise than "§10.2–10.3 is not imported":

`GibbsMeasure/Specification/MarkovIntChains.lean` and `GibbsMeasure/Specification/
MarkovIntUniqueness.lean` prove Theorems (10.21), (10.25) and (10.35) — `Specification.
IsIrreducibleInt`, `exists_isMarkovChain_of_measurePreserving_shift`,
`eq_of_isGibbsMeasure_of_measurePreserving_shift` — **only for a *probability* a priori measure
`ν`** (`variable {ν : Measure E} [IsProbabilityMeasure ν]` fixed for those files). `γ^Q` is built
from `Measure.count`, which is a probability measure only when `E` is finite (already Theorem
(3.5)'s territory). For infinite countable `E` this is a genuine type mismatch, not a missing
`import`: `IsIrreducibleInt (Measure.count) (transferWeight Q)` does not even typecheck.

The bridge is Georgii's own aside before (10.13) — "we may assume `λ ∈ 𝒫(E, 𝓔)`" — which
`MarkovIntUniqueness.lean`'s docstring already flags as unformalized (its "Example (10.24)(2)"
paragraph, gaps (a) and (b)). Contrary to what that docstring suggests, gap (b) (aperiodicity ⇒
eventual positivity, Breiman) is *not* needed here: `IsTransferMatrix.pos` already gives
`Q(x, y) > 0` for **every** pair, so the witnessing integer in Definition (10.23) can be taken to
be the constant `1`. What remains, concretely, is gap (a): a genuine construction, not merely
book-keeping. The measure-theoretic engine for it already exists —
`GibbsMeasure/Specification/Rescaling.lean` has
`MeasureTheory.Measure.exists_measurable_pos_isProbabilityMeasure_withDensity` (a positive
measurable `r : E → ℝ≥0∞` with `(Measure.count).withDensity r` a probability measure, for any
countable `E`), `Specification.rescale r ρ` (`ρ̃_Λ(ω) = ρ_Λ(ω) / ∏_{i ∈ Λ} r(ω_i)`) and
`Specification.modificationKer_sigmaFiniteLambdaFun_of_withDensity` (`ρ̃ · (count.withDensity r)_· =
ρ · count_·`, i.e. `transferSpecification Q hQ` is *unchanged* by the rescaling) — but nobody has
yet checked that `Specification.IsMarkovianInt`, `Specification.IsHomogeneousInt` and
`Specification.IsIrreducibleInt` survive `rescale r`. `IsMarkovianInt` and `IsHomogeneousInt`
transfer for free (the extra factor `∏_{i ∈ Λ} r(ω_i)` for `Λ = Finset.Ioo i k` is itself
`cylinderEvents (Set.Icc i k)`-measurable, and does not involve the `ℤ`-index at all, so it does
not disturb (10.23)'s shift-covariance). `IsIrreducibleInt (count.withDensity r) (rescale r
(transferWeight Q))` is the real remaining construction: with `n(N) ≡ 1` (justified by strict
positivity as above), `C_N` a monotone exhaustion of the countable `E` by finite sets, and
`h_N(x) := (inf_{y, y' ∈ C_N} Q(y, x) Q(x, y')) / r(x)` (finite infimum of positive reals, hence
positive), the defining inequality of (10.23) becomes exactly `transferWeight_singleton` — this is
plausible but unproved. Even granting it, identifying the transition kernel `P` produced by
(10.25) with a matrix equivalent to `Q` (Georgii's own hand-wave to "Theorem (2.34)", or the direct
computation quoted in the proof of (11.13)) is a *second*, independent gap: it needs that two
boundary laws for `Q` representing the *same* measure are proportional by a single constant, which
is not a corollary of anything already proved in `GibbsMeasure/Model/BoundaryLaw.lean` or this
file (the construction in `IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure` produces *one*
boundary law, not a proof that any other representation of the same measure is a scalar multiple
of it).

Comment (11.18)(2) is a free-standing numerical remark (a lower bound `C^{-1} ≤ Q(x,y)/(u(x)v(y))
≤ C` forces `∑_x ∑_{n ≤ N} Q^n(x,x) < ∞`, hence cannot coexist with the hypothesis of (11.15) when
`E` is infinite) that does not depend on Corollary (11.17)'s statement and could be formalized
independently of the gap above; it is not attempted here for lack of time, not for a mathematical
reason.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

/-! ## Positivity of cylinder probabilities under `γ^Q` -/

section Positivity

variable [Nonempty E] {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q)
include hQ

/-- `γ^Q_Λ(σ_Λ = σ_Λ | ω)` for an arbitrary configuration `σ`: the transfer weight of `σ_Λ ω_{Λᶜ}`
over the partition function `Z_Λ(ω)`. -/
lemma transferSpecification_apply_cyl' (Λ : Finset ℤ) (ω σ : ℤ → E) :
    transferSpecification Q hQ Λ ω (cyl Λ σ)
      = transferWeight Q Λ (juxt (Λ : Set ℤ) ω (Λ.restrict σ))
          / Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
              Λ ω := by
  rw [transferSpecification_apply Q hQ Λ ω (measurableSet_cyl Λ σ),
    setLIntegral_lambdaCount_cyl' Λ ω σ (measurable_transferWeight Q Λ), ENNReal.div_eq_inv_mul]

/-- Georgii's positivity: `γ^Q_Λ(σ_Λ = σ_Λ | ω) > 0` for all `Λ`, `ω`, `σ`. -/
lemma transferSpecification_cyl_pos (Λ : Finset ℤ) (ω σ : ℤ → E) :
    0 < transferSpecification Q hQ Λ ω (cyl Λ σ) := by
  rw [transferSpecification_apply_cyl' hQ]
  exact ENNReal.div_pos (transferWeight_pos Q hQ.pos _ _).ne'
    (hQ.isSigmaFiniteLambdaAdmissible Λ ω).2

/-- Every Gibbs measure for `γ^Q` charges every cylinder: `μ(σ_Λ = σ_Λ) > 0`. -/
lemma measure_cyl_pos_of_isGibbsMeasure {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : (transferSpecification Q hQ).IsGibbsMeasure μ) (Λ : Finset ℤ) (σ : ℤ → E) :
    0 < μ (cyl Λ σ) := by
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ) Λ
  have hmeas : Measurable (transferSpecification Q hQ Λ) :=
    (transferSpecification Q hQ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  have hf : Measurable fun ω ↦ transferSpecification Q hQ Λ ω (cyl Λ σ) :=
    ((transferSpecification Q hQ Λ).measurable_coe (measurableSet_cyl Λ σ)).mono
      cylinderEvents_le_pi le_rfl
  have hsupp : Function.support (fun ω ↦ transferSpecification Q hQ Λ ω (cyl Λ σ)) = univ :=
    Function.support_eq_univ fun ω ↦ (transferSpecification_cyl_pos hQ Λ ω σ).ne'
  rw [← hbind, Measure.bind_apply (measurableSet_cyl Λ σ) hmeas.aemeasurable,
    lintegral_pos_iff_support hf, hsupp, measure_univ]
  exact one_pos

lemma measure_intervalCylinder_pos_of_isGibbsMeasure {μ : Measure (ℤ → E)}
    [IsProbabilityMeasure μ] (hμ : (transferSpecification Q hQ).IsGibbsMeasure μ) (a b : ℤ)
    (σ : ℤ → E) : 0 < μ (intervalCylinder a b σ) := by
  rw [intervalCylinder_eq_cyl]
  exact measure_cyl_pos_of_isGibbsMeasure hQ hμ (Finset.Icc a b) σ

end Positivity

/-! ## Markov chains on a countable state space, in terms of interval cylinders -/

section CountableChain

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intervalCylinder_self (a : ℤ) (σ : ℤ → E) :
    intervalCylinder a a σ = (fun τ : ℤ → E ↦ τ a) ⁻¹' {σ a} := by
  ext τ
  rw [mem_intervalCylinder]
  simp

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma intervalCylinder_succ_eq_inter {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) :
    intervalCylinder a (b + 1) σ
      = (fun τ : ℤ → E ↦ τ (b + 1)) ⁻¹' {σ (b + 1)} ∩ intervalCylinder a b σ := by
  ext τ
  simp only [mem_intervalCylinder, mem_inter_iff, mem_preimage, mem_singleton_iff, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨h _ ⟨by omega, le_rfl⟩, fun k hk ↦ h k ⟨hk.1, by omega⟩⟩
  · rintro ⟨h1, h2⟩ k hk
    by_cases hkb : k = b + 1
    · subst hkb; exact h1
    · exact h2 k ⟨hk.1, by omega⟩

omit [Countable E] in
lemma measurableSet_cylinderEvents_intervalCylinder {V : Set ℤ} {a b : ℤ}
    (h : Set.Icc a b ⊆ V) (σ : ℤ → E) :
    MeasurableSet[cylinderEvents V] (intervalCylinder a b σ) := by
  rw [intervalCylinder_eq_cyl]
  exact measurableSet_cylinderEvents_cyl (Δ := Finset.Icc a b) (by simpa using h) σ

/-- The measure of the whole space is the sum of the point masses (countable `E`). -/
lemma measure_univ_eq_tsum_singleton (ν : Measure E) : ν univ = ∑' x, ν {x} := by
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton ν univ MeasurableSet.univ]
  simp

variable {μ : Measure (ℤ → E)} {P : ℤ → Kernel E E}

omit [Countable E] in
/-- The one-step recursion of a Markov chain on interval cylinders:
`μ(σ_a = x_a, …, σ_{b+1} = x_{b+1}) = μ(σ_a = x_a, …, σ_b = x_b) P_{b+1}(x_b, {x_{b+1}})`. -/
theorem IsMarkovChain.measure_intervalCylinder_succ [∀ k, IsMarkovKernel (P k)]
    (hμ : IsMarkovChain P μ) {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) :
    μ (intervalCylinder a (b + 1) σ)
      = μ (intervalCylinder a b σ) * P (b + 1) (σ b) {σ (b + 1)} := by
  have := hμ.isProbabilityMeasure
  have ht : MeasurableSet[cylinderEvents (Set.Iio (b + 1))] (intervalCylinder a b σ) :=
    measurableSet_cylinderEvents_intervalCylinder
      (fun k hk ↦ by simp only [mem_Icc] at hk; simp only [mem_Iio]; omega) σ
  rw [intervalCylinder_succ_eq_inter hab,
    hμ.measure_preimage_inter (b + 1) (measurableSet_singleton _) ht,
    show b + 1 - 1 = b by ring,
    setLIntegral_congr_fun (measurableSet_intervalCylinder a b σ)
      (g := fun _ ↦ P (b + 1) (σ b) {σ (b + 1)})
      (fun τ hτ ↦ by rw [mem_intervalCylinder.1 hτ b (Finset.mem_Icc.2 ⟨hab, le_rfl⟩)]),
    setLIntegral_const, mul_comm]

/-- On a countable state space, a probability measure whose interval-cylinder probabilities
satisfy the one-step recursion of a stochastic family `p_i` is a Markov chain with transition
kernels `ofMatrix (p i)` (Georgii (10.4)(i) ⇒ (ii), in coordinates). -/
theorem isMarkovChain_ofMatrix_of_forall_intervalCylinder [Nonempty E] [IsProbabilityMeasure μ]
    {p : ℤ → E → E → ℝ≥0∞} (hp : ∀ i x, ∑' y, p i x y = 1)
    (h : ∀ a b : ℤ, a ≤ b → ∀ σ : ℤ → E,
      μ (intervalCylinder a (b + 1) σ) = μ (intervalCylinder a b σ) * p (b + 1) (σ b) (σ (b + 1))) :
    IsMarkovChain (fun i ↦ Kernel.ofMatrix (p i)) μ := by
  classical
  have hK : ∀ k, IsMarkovKernel (Kernel.ofMatrix (p k)) := fun k ↦
    Kernel.isMarkovKernel_ofMatrix _ (hp k)
  rw [isMarkovChain_iff_forall_measure_inter]
  intro i A hA t ht
  have hg : Measurable fun σ : ℤ → E ↦ Kernel.ofMatrix (p i) (σ (i - 1)) A :=
    (Kernel.measurable_coe _ hA).comp (measurable_pi_apply _)
  -- the identity on point cylinders over `[i - n - 1, i - 1]`
  have core : ∀ (n : ℕ) (η : ℤ → E),
      μ ((fun σ ↦ σ i) ⁻¹' A ∩ cyl (Finset.Icc (i - n - 1) (i - 1)) η)
        = ∫⁻ σ in cyl (Finset.Icc (i - n - 1) (i - 1)) η,
            Kernel.ofMatrix (p i) (σ (i - 1)) A ∂μ := by
    intro n η
    set W := Finset.Icc (i - n - 1) (i - 1) with hW
    have hiW : i ∉ W := by simp [hW]
    have hi1W : i - 1 ∈ W := by simp [hW]
    have hins : insert i W = Finset.Icc (i - n - 1) i := by
      ext j; simp only [hW, Finset.mem_insert, Finset.mem_Icc]; omega
    have hdecomp : (fun σ ↦ σ i) ⁻¹' A ∩ cyl W η
        = ⋃ y : E, if y ∈ A then cyl (insert i W) (Function.update η i y) else ∅ := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, mem_cyl]
      constructor
      · rintro ⟨hσA, hσ⟩
        refine ⟨σ i, ?_⟩
        rw [ite_eq_left hσA]
        refine mem_cyl.2 fun k hk ↦ ?_
        rcases Finset.mem_insert.1 hk with rfl | hk
        · simp
        · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hiW), hσ k hk]
      · rintro ⟨y, hy⟩
        split_ifs at hy with hyA
        · have hi := mem_cyl.1 hy i (Finset.mem_insert_self _ _)
          rw [Function.update_self] at hi
          refine ⟨hi ▸ hyA, fun k hk ↦ ?_⟩
          rw [mem_cyl.1 hy k (Finset.mem_insert_of_mem hk),
            Function.update_of_ne (ne_of_mem_of_not_mem hk hiW)]
        · exact absurd hy (Set.notMem_empty σ)
    have hdisj : Pairwise (Function.onFun Disjoint fun y : E ↦
        if y ∈ A then cyl (insert i W) (Function.update η i y) else ∅) := by
      intro y y' hne
      simp only [Function.onFun]
      split_ifs
      · refine Set.disjoint_left.2 fun σ hσ hσ' ↦ hne ?_
        have h1 := mem_cyl.1 hσ i (Finset.mem_insert_self _ _)
        have h2 := mem_cyl.1 hσ' i (Finset.mem_insert_self _ _)
        simp only [Function.update_self] at h1 h2
        exact h1.symm.trans h2
      all_goals simp
    have hcyl : ∀ y, μ (cyl (insert i W) (Function.update η i y))
        = μ (cyl W η) * p i (η (i - 1)) y := by
      intro y
      have h1 := h (i - n - 1) (i - 1) (by omega) (Function.update η i y)
      rw [show i - 1 + 1 = i by ring, Function.update_self,
        Function.update_of_ne (show i - 1 ≠ i by omega)] at h1
      have hc : intervalCylinder (i - n - 1) (i - 1) (Function.update η i y) = cyl W η :=
        (intervalCylinder_eq_cyl _ _ _).trans
          (cyl_congr fun k hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hiW) _ _)
      rw [hc] at h1
      rw [hins, ← intervalCylinder_eq_cyl (i - n - 1) i (Function.update η i y), h1]
    rw [hdecomp, measure_iUnion hdisj (fun y ↦ by
      split_ifs
      · exact measurableSet_cyl _ _
      · exact MeasurableSet.empty)]
    rw [setLIntegral_congr_fun (measurableSet_cyl W η)
      (g := fun _ ↦ Kernel.ofMatrix (p i) (η (i - 1)) A)
      (fun σ hσ ↦ by rw [mem_cyl.1 hσ (i - 1) hi1W]), setLIntegral_const,
      Kernel.ofMatrix_apply_set (p i) (η (i - 1)) A, tsum_subtype A, mul_comm,
      ← ENNReal.tsum_mul_left]
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y ∈ A
    · rw [ite_eq_left hy, Set.indicator_of_mem hy, hcyl]
    · rw [ite_eq_right hy, Set.indicator_of_notMem hy, measure_empty, mul_zero]
  -- rectangles are disjoint unions of point cylinders
  have hrect : ∀ (n : ℕ) (B : ℤ → Set E), (∀ k, MeasurableSet (B k)) →
      μ ((fun σ ↦ σ i) ⁻¹' A ∩ rect (Finset.Icc (i - n - 1) (i - 1)) B)
        = ∫⁻ σ in rect (Finset.Icc (i - n - 1) (i - 1)) B,
            Kernel.ofMatrix (p i) (σ (i - 1)) A ∂μ := by
    intro n B _
    rw [rect_eq_iUnion_cyl, Set.inter_iUnion, measure_iUnion (fun ξ ξ' hne ↦
        (pairwise_disjoint_ite_cyl _ B hne).mono Set.inter_subset_right Set.inter_subset_right)
      (fun ξ ↦ (measurable_pi_apply i hA).inter (by
        split_ifs
        · exact measurableSet_cyl _ _
        · exact MeasurableSet.empty)),
      lintegral_iUnion (fun ξ ↦ by
        split_ifs
        · exact measurableSet_cyl _ _
        · exact MeasurableSet.empty) (pairwise_disjoint_ite_cyl _ B)]
    refine tsum_congr fun ξ ↦ ?_
    split_ifs
    · exact core n _
    · simp
  -- the π-λ argument over the rectangles generating `𝓕_{]-∞,i[}`
  have := ext_on_measurableSpace_of_generate_finite (MeasurableSpace.pi)
    (μ := μ.restrict ((fun σ : ℤ → E ↦ σ i) ⁻¹' A))
    (ν := μ.withDensity fun σ : ℤ → E ↦ Kernel.ofMatrix (p i) (σ (i - 1)) A)
    (rectangles E fun n ↦ Finset.Icc (i - n - 1) (i - 1)) ?_ cylinderEvents_le_pi
    (cylinderEvents_Iio_eq_generateFrom i) (isPiSystem_rectangles (monotone_Icc_left' i)) ?_ ht
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _
      (cylinderEvents_le_pi _ ht), Set.inter_comm] at this
    exact this
  · rintro _ ⟨m, B', hB', rfl⟩
    rw [Measure.restrict_apply' (measurable_pi_apply i hA),
      withDensity_apply _ (measurableSet_rect hB'), Set.inter_comm]
    exact hrect m B' hB'
  · rw [Measure.restrict_apply' (measurable_pi_apply i hA), withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ, Set.univ_inter]
    have := hrect 0 (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)
    have huniv : rect (Finset.Icc (i - (0 : ℕ) - 1) (i - 1)) (fun _ : ℤ ↦ (Set.univ : Set E))
        = Set.univ := by ext; simp [rect]
    rw [huniv, Set.inter_univ, Measure.restrict_univ] at this
    exact this

end CountableChain

/-! ## Georgii (11.11): the transition matrices of a boundary law -/

section TransitionMatrix

variable (Q : E → E → ℝ≥0∞) (r : ℤ → E → ℝ≥0∞)

/-- **Georgii (11.11).** The transition matrix `P_i(x, y) = Q(x, y) r_i(y) / r_{i-1}(x)` of the
Markov chain defined by a boundary law `{ℓ_i, r_i}`. -/
def transitionMatrix (i : ℤ) (x y : E) : ℝ≥0∞ := Q x y * r i y / r (i - 1) x

variable {Q r} {ℓ : ℤ → E → ℝ≥0∞} (hbl : IsBoundaryLaw Q ℓ r)
include hbl

lemma IsBoundaryLaw.transitionMatrix_mul (i : ℤ) (x y : E) :
    transitionMatrix Q r i x y * r (i - 1) x = Q x y * r i y := by
  rw [transitionMatrix, ENNReal.div_mul_cancel (hbl.right_pos _ _).ne' (hbl.right_ne_top _ _)]

/-- `P_i` is stochastic: `∑_y P_i(x, y) = 1`, from `Q r_i = r_{i-1}`. -/
lemma IsBoundaryLaw.tsum_transitionMatrix (i : ℤ) (x : E) :
    ∑' y, transitionMatrix Q r i x y = 1 := by
  simp_rw [transitionMatrix, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right, hbl.tsum_mul_right,
    ENNReal.mul_inv_cancel (hbl.right_pos _ _).ne' (hbl.right_ne_top _ _)]

lemma IsBoundaryLaw.isMarkovKernel_ofMatrix_transitionMatrix (i : ℤ) :
    IsMarkovKernel (Kernel.ofMatrix (transitionMatrix Q r i)) :=
  Kernel.isMarkovKernel_ofMatrix _ (hbl.tsum_transitionMatrix i)

variable [Nonempty E]

/-- The one-step recursion (11.10) for the measure of a boundary law. -/
lemma IsBoundaryLaw.boundaryLawMeasure_intervalCylinder_succ {a b : ℤ} (hab : a ≤ b)
    (σ : ℤ → E) :
    boundaryLawMeasure hbl (intervalCylinder a (b + 1) σ)
      = boundaryLawMeasure hbl (intervalCylinder a b σ)
          * transitionMatrix Q r (b + 1) (σ b) (σ (b + 1)) := by
  rw [hbl.boundaryLawMeasure_intervalCylinder (by omega), hbl.boundaryLawMeasure_intervalCylinder
      hab,
    pathProd_succ_top Q hab]
  calc ℓ a (σ a) * (pathProd Q a b σ * Q (σ b) (σ (b + 1))) * r (b + 1) (σ (b + 1))
      = ℓ a (σ a) * pathProd Q a b σ * (Q (σ b) (σ (b + 1)) * r (b + 1) (σ (b + 1))) := by ring
    _ = ℓ a (σ a) * pathProd Q a b σ
          * (transitionMatrix Q r (b + 1) (σ b) (σ (b + 1)) * r (b + 1 - 1) (σ b)) := by
        rw [hbl.transitionMatrix_mul]
    _ = _ := by rw [add_sub_cancel_right]; ring

/-- **Georgii Theorem (11.9)(a), the Markov chain clause.** The measure (11.10) of a boundary law
is a Markov chain with the transition matrices (11.11). -/
theorem IsBoundaryLaw.isMarkovChain_boundaryLawMeasure :
    IsMarkovChain (fun i ↦ Kernel.ofMatrix (transitionMatrix Q r i)) (boundaryLawMeasure hbl) :=
  isMarkovChain_ofMatrix_of_forall_intervalCylinder hbl.tsum_transitionMatrix
    fun _ _ hab σ ↦ hbl.boundaryLawMeasure_intervalCylinder_succ hab σ

end TransitionMatrix

/-! ## Georgii Theorem (11.9)(b): every Markov chain in `𝒢(Q)` comes from a boundary law -/

section IntProd

/-- A positive finite sequence `c` indexed by `ℤ` has a positive finite "running product" `q`
with `q i = q (i - 1) * c i` for all `i` (Georgii's normalising constants `q_i` in the proof of
(11.9)(b)). -/
lemma exists_int_prod (c : ℤ → ℝ≥0∞) (h0 : ∀ i, c i ≠ 0) (ht : ∀ i, c i ≠ ⊤) :
    ∃ q : ℤ → ℝ≥0∞, (∀ i, q i ≠ 0) ∧ (∀ i, q i ≠ ⊤) ∧ ∀ i, q i = q (i - 1) * c i := by
  classical
  let q : ℤ → ℝ≥0∞ := fun i ↦ if 0 ≤ i then ∏ k ∈ Finset.range i.toNat, c (k + 1)
    else (∏ k ∈ Finset.range (-i).toNat, c (-k))⁻¹
  have hq0 : ∀ i, q i ≠ 0 := fun i ↦ by
    simp only [q]
    split_ifs
    · exact Finset.prod_ne_zero_iff.2 fun k _ ↦ h0 _
    · exact ENNReal.inv_ne_zero.2 (ENNReal.prod_lt_top fun k _ ↦ (ht _).lt_top).ne
  have hqt : ∀ i, q i ≠ ⊤ := fun i ↦ by
    simp only [q]
    split_ifs
    · exact (ENNReal.prod_lt_top fun k _ ↦ (ht _).lt_top).ne
    · exact ENNReal.inv_ne_top.2 (Finset.prod_ne_zero_iff.2 fun k _ ↦ h0 _)
  refine ⟨q, hq0, hqt, fun i ↦ ?_⟩
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have h1 : ¬ 0 ≤ i := by omega
    have h2 : ¬ 0 ≤ i - 1 := by omega
    have hn : (-(i - 1)).toNat = (-i).toNat + 1 := by omega
    have hc : ((-i).toNat : ℤ) = -i := by omega
    simp only [q, h1, h2, ite_false, hn, Finset.prod_range_succ, hc, neg_neg]
    rw [ENNReal.mul_inv (Or.inl (Finset.prod_ne_zero_iff.2 fun k _ ↦ h0 _)) (Or.inr (h0 i)),
      mul_assoc, ENNReal.inv_mul_cancel (h0 i) (ht i), mul_one]
  · have h2 : ¬ (0 : ℤ) ≤ -1 := by omega
    rw [zero_sub]
    simp only [q, le_refl, ite_true, h2, ite_false, Int.toNat_zero, Finset.range_zero,
      Finset.prod_empty, neg_neg, Int.toNat_one, Finset.range_one, Finset.prod_singleton,
      Nat.cast_zero, neg_zero]
    rw [ENNReal.inv_mul_cancel (h0 0) (ht 0)]
  · have h1 : 0 ≤ i := hi.le
    have h2 : 0 ≤ i - 1 := by omega
    have hn : i.toNat = (i - 1).toNat + 1 := by omega
    have hc : ((i - 1).toNat : ℤ) + 1 = i := by omega
    simp only [q, h1, h2, ite_true, hn, Finset.prod_range_succ, hc]

end IntProd

section ConverseChain

variable [Nonempty E] {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q)
  {μ : Measure (ℤ → E)} {P : ℤ → Kernel E E} [∀ k, IsMarkovKernel (P k)]
  (hμ : IsMarkovChain P μ)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
lemma puncturedCylinder_succ_self (i : ℤ) (σ : ℤ → E) :
    puncturedCylinder i (i + 1) i σ = (fun τ : ℤ → E ↦ τ (i + 1)) ⁻¹' {σ (i + 1)} := by
  ext τ
  simp only [mem_puncturedCylinder, Finset.mem_erase, Finset.mem_Icc, mem_preimage,
    mem_singleton_iff]
  constructor
  · intro h
    exact h (i + 1) ⟨by omega, by omega, le_rfl⟩
  · intro h k hk
    obtain rfl : k = i + 1 := by omega
    exact h

include hμ

omit [Countable E] [Nonempty E] in
/-- Two-site cylinders of a Markov chain: `μ(σ_{i-1} = x, σ_i = y) = μ(σ_{i-1} = x) P_i(x, {y})`. -/
lemma IsMarkovChain.measure_intervalCylinder_pred (i : ℤ) (σ : ℤ → E) :
    μ (intervalCylinder (i - 1) i σ)
      = μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {σ (i - 1)}) * P i (σ (i - 1)) {σ i} := by
  have := hμ.measure_intervalCylinder_succ (a := i - 1) (b := i - 1) le_rfl σ
  rwa [sub_add_cancel, intervalCylinder_self] at this

omit [Countable E] [Nonempty E] in
/-- Three-site cylinders of a Markov chain. -/
lemma IsMarkovChain.measure_intervalCylinder_pred_succ (i : ℤ) (σ : ℤ → E) :
    μ (intervalCylinder (i - 1) (i + 1) σ)
      = μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {σ (i - 1)}) * P i (σ (i - 1)) {σ i}
          * P (i + 1) (σ i) {σ (i + 1)} := by
  rw [hμ.measure_intervalCylinder_succ (by omega) σ, hμ.measure_intervalCylinder_pred]

omit [Nonempty E] in
/-- `∑_x μ(σ_i = x) P_{i+1}(x, {y}) = μ(σ_{i+1} = y)` for a Markov chain (countable `E`). -/
lemma IsMarkovChain.tsum_measure_preimage_mul (i : ℤ) (y : E) :
    ∑' x, μ ((fun τ : ℤ → E ↦ τ i) ⁻¹' {x}) * P (i + 1) x {y}
      = μ ((fun τ : ℤ → E ↦ τ (i + 1)) ⁻¹' {y}) := by
  have := hμ.isProbabilityMeasure
  set σ : ℤ → E := fun _ ↦ y with hσ
  have hi : i ∈ Finset.Icc i (i + 1) := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have h := measure_puncturedCylinder_tsum μ hi σ
  rw [puncturedCylinder_succ_self] at h
  simp only [hσ] at h
  rw [h]
  refine tsum_congr fun x ↦ ?_
  rw [hμ.measure_intervalCylinder_succ le_rfl, intervalCylinder_self, Function.update_self,
    Function.update_of_ne (show i + 1 ≠ i by omega)]

variable (hG : (transferSpecification Q hQ).IsGibbsMeasure μ)
include hQ hG

omit [∀ k, IsMarkovKernel (P k)] in
/-- Single-site marginals of a Gibbs measure for `γ^Q` are positive. -/
lemma IsMarkovChain.measure_preimage_singleton_pos (i : ℤ) (x : E) :
    0 < μ ((fun τ : ℤ → E ↦ τ i) ⁻¹' {x}) := by
  have := hμ.isProbabilityMeasure
  have h := measure_intervalCylinder_pos_of_isGibbsMeasure hQ hG i i (fun _ ↦ x)
  rwa [intervalCylinder_self] at h

/-- The transition matrices of a Markov chain in `𝒢(Q)` are positive (Georgii, proof of
(11.9)(b)). -/
lemma IsMarkovChain.kernel_singleton_pos (i : ℤ) (x y : E) : 0 < P i x {y} := by
  have := hμ.isProbabilityMeasure
  have h := measure_intervalCylinder_pos_of_isGibbsMeasure hQ hG (i - 1) i
    (Function.update (fun _ ↦ y) (i - 1) x)
  rw [hμ.measure_intervalCylinder_pred, Function.update_self,
    Function.update_of_ne (show i ≠ i - 1 by omega), ENNReal.mul_pos_iff] at h
  exact h.2

/-- **Georgii (11.12)**, division-free: for a Markov chain `μ ∈ 𝒢(Q)` with transition matrices
`P_i`, `P_i(x, y) P_{i+1}(y, z) Q²(x, z) = Q(x, y) Q(y, z) (P_i P_{i+1})(x, z)`; Georgii's form
`P_i(x, y) P_{i+1}(y, z) / (P_i P_{i+1})(x, z) = Q(x, y) Q(y, z) / Q²(x, z)` follows by dividing
by the positive finite `Q²(x, z) (P_i P_{i+1})(x, z)`. -/
theorem IsMarkovChain.mul_mul_eq_of_isGibbsMeasure (i : ℤ) (x y z : E) :
    P i x {y} * P (i + 1) y {z} * (Kernel.ofMatrix Q ^ 2) x {z}
      = Q x y * Q y z * (P (i + 1) ∘ₖ P i) x {z} := by
  have := hμ.isProbabilityMeasure
  set σ := tripleConfig i x y z with hσ
  have hσ1 : σ (i - 1) = x := by simp [hσ, tripleConfig]
  have hσ2 : σ i = y := by simp [hσ, tripleConfig, show i ≠ i - 1 by omega]
  have hσ3 : σ (i + 1) = z := by
    simp [hσ, tripleConfig, show i + 1 ≠ i - 1 by omega, show i + 1 ≠ i by omega]
  have hi : i ∈ Finset.Icc (i - 1) (i + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  -- the Gibbs property at `Λ = {i}` on the three-site cylinder
  have hbind := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hG) {i}
  have hmeas : Measurable (transferSpecification Q hQ {i}) :=
    (transferSpecification Q hQ {i}).measurable.mono cylinderEvents_le_pi le_rfl
  have key : μ (intervalCylinder (i - 1) (i + 1) σ)
      = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z}
          * μ (puncturedCylinder (i - 1) (i + 1) i σ) := by
    conv_lhs => rw [← hbind]
    rw [Measure.bind_apply (measurableSet_intervalCylinder _ _ _) hmeas.aemeasurable]
    simp_rw [transferSpecification_singleton_apply_intervalCylinder Q hQ
      (show i - 1 < i by omega) (show i < i + 1 by omega) σ]
    rw [lintegral_indicator (measurableSet_puncturedCylinder _ _ _ _), setLIntegral_const, hσ1,
      hσ2, hσ3, mul_comm]
  rw [measure_puncturedCylinder_tsum μ hi σ] at key
  simp_rw [hμ.measure_intervalCylinder_pred_succ, Function.update_self,
    Function.update_of_ne (show i - 1 ≠ i by omega), Function.update_of_ne (show i + 1 ≠ i by
        omega),
    hσ1, hσ2, hσ3] at key
  have hre : ∀ y', μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * P i x {y'} * P (i + 1) y' {z}
      = μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * (P i x {y'} * P (i + 1) y' {z}) :=
    fun y' ↦ by ring
  simp_rw [hre, ENNReal.tsum_mul_left, ← Kernel.comp_apply_eq_tsum _ _ _ (measurableSet_singleton
      z)]
    at key
  have hm0 : μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) ≠ 0 :=
    (hμ.measure_preimage_singleton_pos hQ hG (i - 1) x).ne'
  have hmt : μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) ≠ ⊤ := measure_ne_top _ _
  have hQ2 : (Kernel.ofMatrix Q ^ 2) x {z} ≠ 0 := (hQ.pow_two_pos x z).ne'
  have hQ2t : (Kernel.ofMatrix Q ^ 2) x {z} ≠ ⊤ := hQ.pow_two_ne_top x z
  refine (ENNReal.mul_right_inj hm0 hmt).1 ?_
  calc μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * (P i x {y} * P (i + 1) y {z}
        * (Kernel.ofMatrix Q ^ 2) x {z})
      = μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * (P i x {y} * P (i + 1) y {z})
          * (Kernel.ofMatrix Q ^ 2) x {z} := by ring
    _ = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z}
          * (μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * (P (i + 1) ∘ₖ P i) x {z})
          * (Kernel.ofMatrix Q ^ 2) x {z} := by rw [key]
    _ = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z} * (Kernel.ofMatrix Q ^ 2) x {z}
          * (μ ((fun τ : ℤ → E ↦ τ (i - 1)) ⁻¹' {x}) * (P (i + 1) ∘ₖ P i) x {z}) := by ring
    _ = _ := by rw [ENNReal.div_mul_cancel hQ2 hQ2t]; ring

/-- **Georgii Theorem (11.9)(b).** Every Markov chain `μ ∈ 𝒢(Q)` is the measure (11.10) of a
boundary law `{ℓ_i, r_i}` for `Q`, and its transition matrices are given by (11.11):
`P_i(x, y) r_{i-1}(x) = Q(x, y) r_i(y)`. -/
theorem IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure :
    ∃ (ℓ r : ℤ → E → ℝ≥0∞) (hbl : IsBoundaryLaw Q ℓ r), μ = boundaryLawMeasure hbl ∧
      ∀ i x y, P i x {y} * r (i - 1) x = Q x y * r i y := by
  have hprob := hμ.isProbabilityMeasure
  obtain ⟨a⟩ := ‹Nonempty E›
  -- notation
  set m : ℤ → E → ℝ≥0∞ := fun i x ↦ μ ((fun τ : ℤ → E ↦ τ i) ⁻¹' {x}) with hm
  set S : ℤ → E → E → ℝ≥0∞ := fun i x z ↦ (P (i + 1) ∘ₖ P i) x {z} with hS
  have hp0 : ∀ i x y, P i x {y} ≠ 0 := fun i x y ↦ (hμ.kernel_singleton_pos hQ hG i x y).ne'
  have hpt : ∀ i x y, P i x {y} ≠ ⊤ := fun i x y ↦ measure_ne_top _ _
  have hp1 : ∀ i x, ∑' y, P i x {y} = 1 := fun i x ↦ by
    rw [← measure_univ_eq_tsum_singleton, measure_univ]
  have hS0 : ∀ i x z, S i x z ≠ 0 := fun i x z ↦ by
    simp only [hS]
    rw [Kernel.comp_apply_eq_tsum _ _ _ (measurableSet_singleton z)]
    exact (lt_of_lt_of_le (ENNReal.mul_pos (hp0 i x x) (hp0 (i + 1) x z)) (ENNReal.le_tsum x)).ne'
  have hSt : ∀ i x z, S i x z ≠ ⊤ := fun i x z ↦ measure_ne_top _ _
  have hm0 : ∀ i x, m i x ≠ 0 := fun i x ↦ (hμ.measure_preimage_singleton_pos hQ hG i x).ne'
  have hmt : ∀ i x, m i x ≠ ⊤ := fun i x ↦ measure_ne_top _ _
  have hQ0 : ∀ x y, Q x y ≠ 0 := fun x y ↦ (hQ.pos x y).ne'
  have hQ2 : ∀ x z, (Kernel.ofMatrix Q ^ 2) x {z} ≠ 0 := fun x z ↦ (hQ.pow_two_pos x z).ne'
  have hQ2t : ∀ x z, (Kernel.ofMatrix Q ^ 2) x {z} ≠ ⊤ := fun x z ↦ hQ.pow_two_ne_top x z
  -- (11.12)
  have h1112 : ∀ i x y z, P i x {y} * P (i + 1) y {z} * (Kernel.ofMatrix Q ^ 2) x {z}
      = Q x y * Q y z * S i x z := fun i x y z ↦ hμ.mul_mul_eq_of_isGibbsMeasure hQ hG i x y z
  -- the constants `q_i` with `q_i / q_{i-1} = P_{i+1}(a, a) / Q(a, a)`
  obtain ⟨q, hq0, hqt, hq⟩ := exists_int_prod (fun i ↦ P (i + 1) a {a} / Q a a)
    (fun i ↦ ENNReal.div_ne_zero.2 ⟨hp0 _ _ _, hQ.ne_top a a⟩)
    (fun i ↦ ENNReal.div_ne_top (hpt _ _ _) (hQ0 a a))
  have hq' : ∀ i, q (i + 1) * Q a a = q i * P (i + 2) a {a} := fun i ↦ by
    rw [hq (i + 1), add_sub_cancel_right, mul_assoc,
      ENNReal.div_mul_cancel (hQ0 a a) (hQ.ne_top a a), show i + 1 + 1 = i + 2 by ring]
  -- the right vectors `r_i(x) = q_{i+1} Q²(x, a) / (P_{i+1} P_{i+2})(x, a)`
  set r : ℤ → E → ℝ≥0∞ := fun i x ↦ q (i + 1) * (Kernel.ofMatrix Q ^ 2) x {a} / S (i + 1) x a
    with hr
  have hr0 : ∀ i x, r i x ≠ 0 := fun i x ↦
    ENNReal.div_ne_zero.2 ⟨mul_ne_zero (hq0 _) (hQ2 x a), hSt _ _ _⟩
  have hrt : ∀ i x, r i x ≠ ⊤ := fun i x ↦
    ENNReal.div_ne_top (ENNReal.mul_ne_top (hqt _) (hQ2t x a)) (hS0 _ _ _)
  -- (11.11)
  have h1111 : ∀ i x y, P i x {y} * r (i - 1) x = Q x y * r i y := by
    intro i x y
    simp only [hr, sub_add_cancel]
    rw [mul_div_assoc', mul_div_assoc',
      ENNReal.div_eq_div_iff (hS0 _ _ _) (hSt _ _ _) (hS0 _ _ _) (hSt _ _ _)]
    have E1 := h1112 i x y a
    have E2 := h1112 (i + 1) y a a
    rw [show i + 1 + 1 = i + 2 by ring] at E2
    have E3 := hq' i
    have hM0 : P (i + 1) y {a} * Q a a ≠ 0 := mul_ne_zero (hp0 _ _ _) (hQ0 a a)
    have hMt : P (i + 1) y {a} * Q a a ≠ ⊤ := ENNReal.mul_ne_top (hpt _ _ _) (hQ.ne_top a a)
    refine (ENNReal.mul_right_inj hM0 hMt).1 ?_
    calc P (i + 1) y {a} * Q a a
          * (S (i + 1) y a * (P i x {y} * (q i * (Kernel.ofMatrix Q ^ 2) x {a})))
        = q i * S (i + 1) y a * Q a a
            * (P i x {y} * P (i + 1) y {a} * (Kernel.ofMatrix Q ^ 2) x {a}) := by ring
      _ = q i * S (i + 1) y a * Q a a * (Q x y * Q y a * S i x a) := by rw [E1]
      _ = S i x a * Q x y * q i * (Q y a * Q a a * S (i + 1) y a) := by ring
      _ = S i x a * Q x y * q i * (P (i + 1) y {a} * P (i + 2) a {a}
            * (Kernel.ofMatrix Q ^ 2) y {a}) := by rw [E2]
      _ = S i x a * Q x y * P (i + 1) y {a} * (Kernel.ofMatrix Q ^ 2) y {a}
            * (q i * P (i + 2) a {a}) := by ring
      _ = S i x a * Q x y * P (i + 1) y {a} * (Kernel.ofMatrix Q ^ 2) y {a}
            * (q (i + 1) * Q a a) := by rw [E3]
      _ = _ := by ring
  -- `Q r_i = r_{i-1}`
  have hQr : ∀ i x, ∑' y, Q x y * r i y = r (i - 1) x := fun i x ↦ by
    simp_rw [← h1111 i x]
    rw [ENNReal.tsum_mul_right, hp1, one_mul]
  -- the left vectors `ℓ_i(x) = μ(σ_i = x) / r_i(x)`
  set ℓ : ℤ → E → ℝ≥0∞ := fun i x ↦ m i x / r i x with hℓ
  have hℓr : ∀ i x, ℓ i x * r i x = m i x := fun i x ↦
    ENNReal.div_mul_cancel (hr0 i x) (hrt i x)
  have hm1 : ∀ i, ∑' x, m i x = 1 := fun i ↦ by
    have : IsProbabilityMeasure (μ.map fun τ : ℤ → E ↦ τ i) :=
      Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
    simp only [hm]
    simp_rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton _)]
    rw [← measure_univ_eq_tsum_singleton, measure_univ]
  have hℓQ : ∀ i y, ∑' x, ℓ i x * Q x y = ℓ (i + 1) y := fun i y ↦ by
    simp only [hℓ]
    rw [ENNReal.eq_div_iff (hr0 _ _) (hrt _ _), ← ENNReal.tsum_mul_left]
    have hsum : ∑' x, m i x * P (i + 1) x {y} = m (i + 1) y := hμ.tsum_measure_preimage_mul i y
    rw [← hsum]
    refine tsum_congr fun x ↦ ?_
    have h := h1111 (i + 1) x y
    rw [add_sub_cancel_right] at h
    calc r (i + 1) y * (m i x / r i x * Q x y)
        = m i x / r i x * (Q x y * r (i + 1) y) := by ring
      _ = m i x / r i x * (P (i + 1) x {y} * r i x) := by rw [h]
      _ = m i x / r i x * r i x * P (i + 1) x {y} := by ring
      _ = m i x * P (i + 1) x {y} := by rw [ENNReal.div_mul_cancel (hr0 i x) (hrt i x)]
  have hbl : IsBoundaryLaw Q ℓ r := IsBoundaryLaw.of_tsum
    (fun i x ↦ pos_iff_ne_zero.2 (ENNReal.div_ne_zero.2 ⟨hm0 i x, hrt i x⟩))
    (fun i x ↦ ENNReal.div_ne_top (hmt i x) (hr0 i x))
    (fun i x ↦ pos_iff_ne_zero.2 (hr0 i x)) hrt hℓQ hQr (fun i ↦ by simp_rw [hℓr]; exact hm1 i)
  refine ⟨ℓ, r, hbl, ?_, h1111⟩
  refine hbl.eq_boundaryLawMeasure_of_forall_intervalCylinder fun a b hab σ ↦ ?_
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [intervalCylinder_self, pathProd_self, mul_one, hℓr]
  | succ n ih =>
    have h := h1111 (a + n + 1) (σ (a + n)) (σ (a + n + 1))
    rw [add_sub_cancel_right] at h
    rw [show a + ((n + 1 : ℕ) : ℤ) = a + n + 1 by push_cast; ring,
      hμ.measure_intervalCylinder_succ (by omega), ih (by omega), pathProd_succ_top Q (by omega)]
    calc ℓ a (σ a) * pathProd Q a (a + n) σ * r (a + n) (σ (a + n))
          * P (a + n + 1) (σ (a + n)) {σ (a + n + 1)}
        = ℓ a (σ a) * pathProd Q a (a + n) σ
            * (P (a + n + 1) (σ (a + n)) {σ (a + n + 1)} * r (a + n) (σ (a + n))) := by ring
      _ = _ := by rw [h]; ring

end ConverseChain

/-! ## Shifts of boundary laws -/

section Shift

variable {Q : E → E → ℝ≥0∞} {ℓ r : ℤ → E → ℝ≥0∞}

omit [Countable E] [MeasurableSingletonClass E] in
/-- The preimage of an interval cylinder under the shift `θ_j`, `(θ_j ω)_i = ω_{i-j}`. -/
lemma shift_preimage_intervalCylinder (j a b : ℤ) (σ : ℤ → E) :
    (GibbsMeasure.shift E j).toFun ⁻¹' intervalCylinder a b σ
      = intervalCylinder (a - j) (b - j) fun k ↦ σ (k + j) := by
  ext ω
  simp only [mem_preimage, mem_intervalCylinder, shift_toFun_apply, Finset.mem_Icc]
  constructor
  · intro h k hk
    have := h (k + j) ⟨by omega, by omega⟩
    rwa [add_sub_cancel_right] at this
  · intro h k hk
    have := h (k - j) ⟨by omega, by omega⟩
    rwa [sub_add_cancel] at this

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_shift (Q : E → E → ℝ≥0∞) (j a b : ℤ) (σ : ℤ → E) :
    pathProd Q (a - j) (b - j) (fun k ↦ σ (k + j)) = pathProd Q a b σ := by
  simp only [pathProd]
  have h := Finset.prod_Ico_add' (fun k ↦ Q (σ k) (σ (k + 1))) (a - j) (b - j) j
  simp only [sub_add_cancel] at h
  rw [← h]
  exact Finset.prod_congr rfl fun k _ ↦ by simp only [add_right_comm k 1 j]

/-- The shift of a boundary law: `{ℓ_{i-j}, r_{i-j}}` is again a boundary law. -/
lemma IsBoundaryLaw.shift (hbl : IsBoundaryLaw Q ℓ r) (j : ℤ) :
    IsBoundaryLaw Q (fun i ↦ ℓ (i - j)) (fun i ↦ r (i - j)) :=
  IsBoundaryLaw.of_tsum (fun _ _ ↦ hbl.left_pos _ _) (fun _ _ ↦ hbl.left_ne_top _ _)
    (fun _ _ ↦ hbl.right_pos _ _) (fun _ _ ↦ hbl.right_ne_top _ _)
    (fun i y ↦ by rw [hbl.tsum_left_mul, show i - j + 1 = i + 1 - j by ring])
    (fun i x ↦ by rw [hbl.tsum_mul_right, show i - j - 1 = i - 1 - j by ring])
    (fun _ ↦ hbl.tsum_left_mul_right _)

variable [Nonempty E] (hbl : IsBoundaryLaw Q ℓ r)
include hbl

/-- The shift `θ_j(μ)` of the measure (11.10) of a boundary law is the measure of the shifted
boundary law `{ℓ_{i-j}, r_{i-j}}`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_map_shift (j : ℤ) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E j).toFun = boundaryLawMeasure (hbl.shift
        j) := by
  have : IsProbabilityMeasure ((boundaryLawMeasure hbl).map (GibbsMeasure.shift E j).toFun) :=
    Measure.isProbabilityMeasure_map (GibbsMeasure.shift E j).measurable_toFun.aemeasurable
  refine (hbl.shift j).eq_boundaryLawMeasure_of_forall_intervalCylinder fun a b hab σ ↦ ?_
  rw [Measure.map_apply (GibbsMeasure.shift E j).measurable_toFun (measurableSet_intervalCylinder
      a b σ),
    shift_preimage_intervalCylinder, hbl.boundaryLawMeasure_intervalCylinder (by omega),
    pathProd_shift]
  simp only [sub_add_cancel]

/-- If `ℓ_{i-p} = c ℓ_i` and `r_{i+p} = c r_i` for all `i`, then the measure of the boundary law
is `θ_p`-invariant (the last step in Georgii's proof of (11.15)). -/
theorem IsBoundaryLaw.boundaryLawMeasure_map_shift_eq_self_of_periodic {p : ℤ} {c : ℝ≥0∞}
    (hℓ : ∀ i x, ℓ (i - p) x = c * ℓ i x) (hr : ∀ i x, r (i + p) x = c * r i x) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E p).toFun = boundaryLawMeasure hbl := by
  rw [hbl.boundaryLawMeasure_map_shift]
  refine hbl.eq_boundaryLawMeasure_of_forall_intervalCylinder fun a b hab σ ↦ ?_
  rw [(hbl.shift p).boundaryLawMeasure_intervalCylinder hab]
  have hr' := hr (b - p) (σ b)
  rw [sub_add_cancel] at hr'
  rw [hℓ, hr']
  ring

/-- A boundary law constant in `i` defines a shift-invariant measure: Georgii's `μ_P`, and every
`ℓ_i = ℓ`, `r_i = r`, is in `𝓟_Θ`. -/
theorem IsBoundaryLaw.mem_invariantFields_shiftGroup_of_const (hℓ : ∀ i j x, ℓ i x = ℓ j x)
    (hr : ∀ i j x, r i x = r j x) :
    boundaryLawMeasure hbl ∈ invariantFields (shiftGroup ℤ E) :=
  mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun j ↦ ⟨(GibbsMeasure.shift E
      j).measurable_toFun,
    hbl.boundaryLawMeasure_map_shift_eq_self_of_periodic (c := 1)
      (fun i x ↦ by rw [one_mul, hℓ]) (fun i x ↦ by rw [one_mul, hr])⟩⟩

end Shift

/-! ## Two boundary laws representing the same measure are proportional -/

section Proportionality

variable [Nonempty E] {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q)
  {ℓ r ℓ' r' : ℤ → E → ℝ≥0∞} (hbl : IsBoundaryLaw Q ℓ r) (hbl' : IsBoundaryLaw Q ℓ' r')
include hQ hbl hbl'

/-- **The proportionality underlying Georgii's identification, in the proof of Theorem (11.13),
of the transition matrix produced by (10.25) with a matrix equivalent to `Q`.** If two boundary
laws `{ℓ_i, r_i}` and `{ℓ'_i, r'_i}` for a positive transfer matrix `Q` have the same measure
(11.10), they are proportional by a single constant `c` independent of `i`: `ℓ_i = c ℓ'_i` and
`r'_i = c r_i` for all `i`, with `0 < c < ∞`.

Derived from the cylinder probabilities (11.10) at intervals of length one (`ℓ_i r_i = ℓ'_i r'_i`,
Georgii's `μ(σ_i = x)`) and length two (`ℓ_i(x) Q(x,y) r_{i+1}(y) = ℓ'_i(x) Q(x,y) r'_{i+1}(y)`,
`μ(σ_i = x, σ_{i+1} = y)`): the length-two identity separates variables into a factor of `x` and a
factor of `y`, forcing both to be independent of `i`'s companion coordinate and hence equal to a
constant `C_i` depending only on `i`; the length-one identity then forces `C_i = C_{i-1}` for every
`i`, so `C` is itself constant. -/
theorem IsBoundaryLaw.exists_const_of_boundaryLawMeasure_eq
    (heq : boundaryLawMeasure hbl = boundaryLawMeasure hbl') :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ (∀ i x, ℓ i x = c * ℓ' i x) ∧ ∀ i x, r' i x = c * r i x := by
  obtain ⟨x₀⟩ := ‹Nonempty E›
  -- (11.10) at length one
  have hA : ∀ i x, ℓ i x * r i x = ℓ' i x * r' i x := by
    intro i x
    have e1 : boundaryLawMeasure hbl (intervalCylinder i i (fun _ ↦ x)) = ℓ i x * r i x := by
      rw [hbl.boundaryLawMeasure_intervalCylinder le_rfl, pathProd_self, mul_one]
    have e2 : boundaryLawMeasure hbl' (intervalCylinder i i (fun _ ↦ x)) = ℓ' i x * r' i x := by
      rw [hbl'.boundaryLawMeasure_intervalCylinder le_rfl, pathProd_self, mul_one]
    rw [← e1, ← e2, heq]
  -- (11.10) at length two
  have hB : ∀ i x y, ℓ i x * r (i + 1) y = ℓ' i x * r' (i + 1) y := by
    intro i x y
    set σ : ℤ → E := Function.update (fun _ ↦ x) (i + 1) y with hσdef
    have hσi : σ i = x := Function.update_of_ne (by omega) _ _
    have hσi1 : σ (i + 1) = y := Function.update_self _ _ _
    have e1 : boundaryLawMeasure hbl (intervalCylinder i (i + 1) σ)
        = ℓ i x * Q x y * r (i + 1) y := by
      rw [hbl.boundaryLawMeasure_intervalCylinder (by omega), pathProd_succ, hσi, hσi1]
    have e2 : boundaryLawMeasure hbl' (intervalCylinder i (i + 1) σ)
        = ℓ' i x * Q x y * r' (i + 1) y := by
      rw [hbl'.boundaryLawMeasure_intervalCylinder (by omega), pathProd_succ, hσi, hσi1]
    have hB0 : ℓ i x * Q x y * r (i + 1) y = ℓ' i x * Q x y * r' (i + 1) y := by
      rw [← e1, ← e2, heq]
    have hQxy0 : Q x y ≠ 0 := (hQ.pos x y).ne'
    have hQxyt : Q x y ≠ ⊤ := hQ.ne_top x y
    rw [mul_right_comm (ℓ i x), mul_right_comm (ℓ' i x)] at hB0
    exact (ENNReal.mul_left_inj hQxy0 hQxyt).1 hB0
  -- the constant `C i = r'_{i+1}(x₀) / r_{i+1}(x₀)`, separating `x` from `y` in `hB`
  set C : ℤ → ℝ≥0∞ := fun i ↦ r' (i + 1) x₀ / r (i + 1) x₀ with hCdef
  have hCpos : ∀ i, 0 < C i := fun i ↦
    ENNReal.div_pos (hbl'.right_pos _ _).ne' (hbl.right_ne_top _ _)
  have hCne : ∀ i, C i ≠ ⊤ := fun i ↦
    ENNReal.div_ne_top (hbl'.right_ne_top _ _) (hbl.right_pos _ _).ne'
  have hℓeq : ∀ i x, ℓ i x = C i * ℓ' i x := by
    intro i x
    have hr0 : r (i + 1) x₀ ≠ 0 := (hbl.right_pos _ _).ne'
    have hrt : r (i + 1) x₀ ≠ ⊤ := hbl.right_ne_top _ _
    have h := hB i x x₀
    rw [mul_comm (ℓ i x)] at h
    have heq2 : ℓ i x = (ℓ' i x * r' (i + 1) x₀) / r (i + 1) x₀ := (ENNReal.eq_div_iff hr0 hrt).2 h
    simp only [hCdef, div_eq_mul_inv]
    rw [heq2, div_eq_mul_inv]
    ring
  have hreq : ∀ i y, r' (i + 1) y = C i * r (i + 1) y := by
    intro i y
    have h := hB i x₀ y
    rw [hℓeq i x₀] at h
    have hne0 : ℓ' i x₀ ≠ 0 := (hbl'.left_pos _ _).ne'
    have hnet : ℓ' i x₀ ≠ ⊤ := hbl'.left_ne_top _ _
    rw [show C i * ℓ' i x₀ * r (i + 1) y = ℓ' i x₀ * (C i * r (i + 1) y) by ring] at h
    exact ((ENNReal.mul_right_inj hne0 hnet).1 h).symm
  -- `C` does not depend on `i`
  have hstep : ∀ i, C (i + 1) = C i := by
    intro i
    have hA' := hA (i + 1) x₀
    rw [hℓeq (i + 1) x₀, hreq i x₀] at hA'
    have hne0 : ℓ' (i + 1) x₀ * r (i + 1) x₀ ≠ 0 :=
      mul_ne_zero (hbl'.left_pos _ _).ne' (hbl.right_pos _ _).ne'
    have hnet : ℓ' (i + 1) x₀ * r (i + 1) x₀ ≠ ⊤ :=
      ENNReal.mul_ne_top (hbl'.left_ne_top _ _) (hbl.right_ne_top _ _)
    rw [show C (i + 1) * ℓ' (i + 1) x₀ * r (i + 1) x₀
          = (ℓ' (i + 1) x₀ * r (i + 1) x₀) * C (i + 1) by ring,
      show ℓ' (i + 1) x₀ * (C i * r (i + 1) x₀) = (ℓ' (i + 1) x₀ * r (i + 1) x₀) * C i by
        ring] at hA'
    exact (ENNReal.mul_right_inj hne0 hnet).1 hA'
  have hCconst : ∀ i, C i = C 0 := by
    intro i
    induction i using Int.induction_on with
    | zero => rfl
    | succ i ih => rw [hstep i, ih]
    | pred i ih =>
      rw [← ih, ← hstep (-(i : ℤ) - 1)]
      simp only [sub_add_cancel]
  refine ⟨C 0, hCpos 0, hCne 0, fun i x ↦ ?_, fun i x ↦ ?_⟩
  · rw [hℓeq i x, hCconst i]
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by ring⟩
    rw [hreq j x, hCconst j]

end Proportionality

/-! ## Georgii Theorem (11.13), the existence half: positive recurrent `P ~ Q` gives `μ_P ∈ 𝒢_Θ(Q)`
-/

section Stationary

variable {P : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1)
include hpos hP

/-- A positive stochastic matrix is a transfer matrix: its powers are stochastic, hence finite. -/
lemma isTransferMatrix_of_stochastic : IsTransferMatrix P where
  pos := hpos
  pow_ne_top n _ _ := by
    have := Kernel.isMarkovKernel_ofMatrix P hP
    have := Kernel.isFiniteKernel_pow (Kernel.ofMatrix P) (n + 1)
    exact measure_ne_top _ _

variable {α : E → ℝ≥0∞} (hα0 : ∀ x, 0 < α x) (hαt : ∀ x, α x ≠ ⊤) (hα1 : ∑' x, α x = 1)
  (hαP : ∀ y, ∑' x, α x * P x y = α y)
include hα0 hαt hα1 hαP

omit hpos in
/-- **Georgii, before (11.13).** An invariant probability vector `α` of a positive stochastic
matrix `P`, with `r_i ≡ 1`, is a boundary law for `P`. -/
lemma isBoundaryLaw_const : IsBoundaryLaw P (fun _ ↦ α) (fun _ _ ↦ 1) :=
  IsBoundaryLaw.of_tsum (fun _ x ↦ hα0 x) (fun _ x ↦ hαt x) (fun _ _ ↦ one_pos)
    (fun _ _ ↦ ENNReal.one_ne_top) (fun _ y ↦ hαP y)
    (fun _ x ↦ by simp_rw [mul_one]; exact hP x) (fun _ ↦ by simp_rw [mul_one]; exact hα1)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] hpos hP hα0 hαt hα1 hαP in
lemma transitionMatrix_one (i : ℤ) : transitionMatrix P (fun _ _ ↦ 1) i = P := by
  funext x y
  simp [transitionMatrix]

variable [Nonempty E]

omit hpos in
/-- **Georgii's `μ_P`** is a Markov chain with transition matrix `P`. -/
theorem isMarkovChain_boundaryLawMeasure_const :
    IsMarkovChain (fun _ ↦ Kernel.ofMatrix P)
      (boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP)) := by
  have := (isBoundaryLaw_const hP hα0 hαt hα1 hαP).isMarkovChain_boundaryLawMeasure
  simpa only [transitionMatrix_one] using this

/-- **Georgii Theorem (11.13), the existence half.** If `Q ~ P` (`γ^Q = γ^P`) for a positive
stochastic matrix `P` with an invariant probability vector `α` (Georgii: `P` positive recurrent),
then Georgii's `μ_P` — the measure of the boundary law `ℓ_i = α`, `r_i = 1` — is a shift-invariant
Gibbs measure for `γ^Q`: `μ_P ∈ 𝒢_Θ(Q)`. -/
theorem boundaryLawMeasure_const_mem_invariantG {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q)
    (heq : transferSpecification Q hQ
      = transferSpecification P (isTransferMatrix_of_stochastic hpos hP)) :
    boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP)
      ∈ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [heq]
    exact isGibbsMeasure_transferSpecification_boundaryLawMeasure _ _
  · exact (isBoundaryLaw_const hP hα0 hαt hα1 hαP).mem_invariantFields_shiftGroup_of_const
      (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- **Georgii Theorem (11.13), the existence half, in the form (11.5).** If
`P(x, y) = Q(x, y) r(y) / (q r(x))` for a positive stochastic `P` with an invariant probability
vector, then `𝒢_Θ(Q) ≠ ∅`. -/
theorem invariantG_nonempty_of_rel {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q) {q : ℝ≥0∞}
    {r : E → ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ⊤)
    (hPQ : ∀ x y, P x y = Q x y * r y / (q * r x)) :
    (invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)).Nonempty :=
  ⟨_, boundaryLawMeasure_const_mem_invariantG hpos hP hα0 hαt hα1 hαP hQ
    (transferSpecification_eq_of_rel (isTransferMatrix_of_stochastic hpos hP) hQ hq0 hqt hr0 hrt
      hPQ).symm⟩

end Stationary

/-! ## Georgii (11.16) and the periodicity argument of Theorem (11.15) -/

section Periodicity

variable (Q : E → E → ℝ≥0∞)

/-- **Georgii's inequality in the proof of (11.15).** If `inf_x ∑_{n=1}^N Q^n(x, x) > 0` then
`inf_x Q^{N!}(x, x) > 0`: for `p = N!`, `Q^p(x, x) ≥ (1 ∧ ε/N)^p` for every `x`. -/
theorem exists_pos_lt_pow_factorial_apply_of_le_sum {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞}
    (hε : 0 < ε) (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    ∃ δ, 0 < δ ∧ ∀ x, δ < (Kernel.ofMatrix Q ^ N.factorial) x {x} := by
  set η : ℝ≥0∞ := min 1 (ε / N) with hη
  have hη0 : η ≠ 0 :=
    (lt_min one_pos (ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top N))).ne'
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηt : η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hη1
  refine ⟨η ^ N.factorial / 2, ENNReal.half_pos (pow_ne_zero _ hη0), fun x ↦ ?_⟩
  refine (ENNReal.half_lt_self (pow_ne_zero _ hη0) (ENNReal.pow_ne_top hηt)).trans_le ?_
  obtain ⟨n, hn, hnx⟩ : ∃ n ∈ Finset.Icc 1 N, ε / N ≤ (Kernel.ofMatrix Q ^ n) x {x} := by
    by_contra hcon
    push Not at hcon
    have hlt := ENNReal.sum_lt_sum_of_nonempty (Finset.nonempty_Icc.2 hN) hcon
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, show N + 1 - 1 = N by omega,
      ENNReal.mul_div_cancel (Nat.cast_ne_zero.2 hN.ne') (ENNReal.natCast_ne_top N)] at hlt
    exact absurd (h x) (not_le.2 hlt)
  rw [Finset.mem_Icc] at hn
  obtain ⟨k, hk⟩ : n ∣ N.factorial := Nat.dvd_factorial hn.1 hn.2
  have hkN : k ≤ N.factorial := Nat.le_of_dvd (Nat.factorial_pos N) ⟨n, by rw [hk, mul_comm]⟩
  calc η ^ N.factorial ≤ η ^ k := pow_le_pow_of_le_one zero_le hη1 hkN
    _ ≤ (Kernel.ofMatrix Q ^ n) x {x} ^ k :=
        pow_le_pow_left' ((min_le_right _ _).trans hnx) k
    _ ≤ (Kernel.ofMatrix Q ^ (k * n)) x {x} := (Kernel.ofMatrix Q).pow_le_pow_mul_apply_singleton
        k n x
    _ = _ := by rw [hk, mul_comm]

variable {Q} {ℓ r : ℤ → E → ℝ≥0∞} (hbl : IsBoundaryLaw Q ℓ r)
include hbl

/-- `ℓ_i Q^n = ℓ_{i+n}`. -/
lemma IsBoundaryLaw.tsum_left_mul_pow (n : ℕ) (i : ℤ) (y : E) :
    ∑' x, ℓ i x * (Kernel.ofMatrix Q ^ n) x {y} = ℓ (i + n) y := by
  induction n generalizing y with
  | zero =>
    simp only [Kernel.pow_zero_apply_singleton]
    rw [tsum_eq_single y fun x hx ↦ by
      rw [Set.indicator_of_notMem fun h ↦ hx (Set.mem_singleton_iff.1 h), mul_zero]]
    rw [Set.indicator_of_mem (mem_singleton y), Pi.one_apply, mul_one, Nat.cast_zero, add_zero]
  | succ n ih =>
    simp_rw [Kernel.ofMatrix_pow_succ'_apply_singleton, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    simp_rw [← mul_assoc, ENNReal.tsum_mul_right, ih]
    rw [hbl.tsum_left_mul, show i + n + 1 = i + ((n + 1 : ℕ) : ℤ) by push_cast; ring]

/-- `Q^n r_{i+n} = r_i`. -/
lemma IsBoundaryLaw.tsum_pow_mul_right (n : ℕ) (i : ℤ) (x : E) :
    ∑' y, (Kernel.ofMatrix Q ^ n) x {y} * r (i + n) y = r i x := by
  induction n generalizing i x with
  | zero =>
    simp only [Kernel.pow_zero_apply_singleton]
    rw [tsum_eq_single x fun y hy ↦ by
      rw [Set.indicator_of_notMem fun h ↦ hy (Set.mem_singleton_iff.1 h).symm, zero_mul]]
    rw [Set.indicator_of_mem (mem_singleton x), Pi.one_apply, one_mul, Nat.cast_zero, add_zero]
  | succ n ih =>
    simp_rw [Kernel.ofMatrix_pow_succ_apply_singleton, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    simp_rw [mul_assoc, ENNReal.tsum_mul_left]
    have : ∀ b, ∑' y, (Kernel.ofMatrix Q ^ n) b {y} * r (i + ((n + 1 : ℕ) : ℤ)) y
        = r (i + 1) b := fun b ↦ by
      rw [show i + ((n + 1 : ℕ) : ℤ) = i + 1 + n by push_cast; ring]
      exact ih (i + 1) b
    simp_rw [this]
    exact hbl.tsum_mul_right_succ i x

/-- **Georgii (11.16), left.** If `δ < Q^p(x, x)` for all `x`, then `δ ℓ_{i-p} < ℓ_i`. -/
lemma IsBoundaryLaw.mul_left_sub_lt {p : ℕ} {δ : ℝ≥0∞}
    (hδ : ∀ x, δ < (Kernel.ofMatrix Q ^ p) x {x}) (i : ℤ) (x : E) :
    δ * ℓ (i - p) x < ℓ i x := by
  have h := hbl.tsum_left_mul_pow p (i - p) x
  rw [sub_add_cancel] at h
  calc δ * ℓ (i - p) x = ℓ (i - p) x * δ := mul_comm _ _
    _ < ℓ (i - p) x * (Kernel.ofMatrix Q ^ p) x {x} :=
        ENNReal.mul_lt_mul_right (hbl.left_pos _ _).ne' (hbl.left_ne_top _ _) (hδ x)
    _ ≤ ∑' z, ℓ (i - p) z * (Kernel.ofMatrix Q ^ p) z {x} := ENNReal.le_tsum x
    _ = ℓ i x := h

/-- **Georgii (11.16), right.** If `δ < Q^p(x, x)` for all `x`, then `δ r_{i+p} < r_i`. -/
lemma IsBoundaryLaw.mul_right_add_lt {p : ℕ} {δ : ℝ≥0∞}
    (hδ : ∀ x, δ < (Kernel.ofMatrix Q ^ p) x {x}) (i : ℤ) (x : E) :
    δ * r (i + p) x < r i x := by
  have h := hbl.tsum_pow_mul_right p i x
  calc δ * r (i + p) x < (Kernel.ofMatrix Q ^ p) x {x} * r (i + p) x :=
        ENNReal.mul_lt_mul_left (hbl.right_pos _ _).ne' (hbl.right_ne_top _ _) (hδ x)
    _ ≤ ∑' y, (Kernel.ofMatrix Q ^ p) x {y} * r (i + p) y := ENNReal.le_tsum x
    _ = r i x := h

/-- `ℓ_i r_{i+p} = ℓ_{i-1} r_{i-1+p}`: the constant `c` of Georgii's proof of (11.15). -/
lemma IsBoundaryLaw.tsum_left_mul_right_add_succ (p : ℕ) (i : ℤ) :
    ∑' x, ℓ (i + 1) x * r (i + 1 + p) x = ∑' x, ℓ i x * r (i + p) x := by
  simp_rw [← hbl.tsum_left_mul i, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  have : ∀ z, ∑' x, Q z x * r (i + 1 + p) x = r (i + p) z := fun z ↦ by
    rw [show i + 1 + p = i + p + 1 by ring]
    exact hbl.tsum_mul_right_succ _ _
  simp_rw [this]

lemma IsBoundaryLaw.tsum_left_mul_right_add_eq (p : ℕ) (i : ℤ) :
    ∑' x, ℓ i x * r (i + p) x = ∑' x, ℓ 0 x * r (0 + p) x := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [hbl.tsum_left_mul_right_add_succ, ih]
  | pred i ih =>
    rw [← ih, ← hbl.tsum_left_mul_right_add_succ p (-(i : ℤ) - 1)]
    simp only [sub_add_cancel]

variable [Nonempty E] (hQ : IsTransferMatrix Q)
include hQ

/-- **The argument of Georgii Theorem (11.15).** Let `μ` be the measure (11.10) of a boundary law
`{ℓ_i, r_i}` for `Q`, extreme in `𝒢(Q)`, and let `δ > 0` satisfy `δ < Q^p(x, x)` for all `x`
(`inf_x Q^p(x, x) > 0`). Then `ℓ_{i-p} = c ℓ_i` and `r_{i+p} = c r_i` for the constant
`c = ℓ_i r_{i+p}`, and hence `θ_p(μ) = μ`.

Georgii applies this to every `μ ∈ ex 𝒢(Q)`, which Theorem (11.9)(c) — resting on Theorem
(10.21) — represents by a boundary law; that representation is the hypothesis here. -/
theorem IsBoundaryLaw.boundaryLawMeasure_map_shift_eq_self_of_mem_extremePoints
    (hext : boundaryLawMeasure hbl ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞)
    {p : ℕ} {δ : ℝ≥0∞} (hδ0 : 0 < δ) (hδ : ∀ x, δ < (Kernel.ofMatrix Q ^ p) x {x}) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E (p : ℤ)).toFun = boundaryLawMeasure hbl := by
  obtain ⟨x₀⟩ := ‹Nonempty E›
  -- the constant `c = ℓ_i r_{i+p}`
  set c : ℝ≥0∞ := ∑' x, ℓ 0 x * r (0 + p) x with hc
  have hci : ∀ i, ∑' x, ℓ i x * r (i + p) x = c := fun i ↦ hbl.tsum_left_mul_right_add_eq p i
  have hci' : ∀ i, ∑' x, ℓ (i - p) x * r i x = c := fun i ↦ by
    have := hci (i - p)
    rwa [sub_add_cancel] at this
  have hc0 : c ≠ 0 := by
    rw [← hci 0]
    exact (lt_of_lt_of_le (ENNReal.mul_pos (hbl.left_pos _ _).ne' (hbl.right_pos _ _).ne')
      (ENNReal.le_tsum x₀)).ne'
  -- `0 < cδ < 1`
  have hlt : ∀ x, ℓ 0 x * (δ * r (0 + p) x) < ℓ 0 x * r 0 x := fun x ↦
    ENNReal.mul_lt_mul_right (hbl.left_pos _ _).ne' (hbl.left_ne_top _ _)
      (hbl.mul_right_add_lt hδ 0 x)
  have hcδ : c * δ < 1 := by
    have hre : ∀ x, ℓ 0 x * r (0 + p) x * δ = ℓ 0 x * (δ * r (0 + p) x) := fun x ↦ by ring
    rw [← hci 0, ← hbl.tsum_left_mul_right 0, ← ENNReal.tsum_mul_right]
    simp_rw [hre]
    refine ENNReal.tsum_lt_tsum (i := x₀) ?_ (fun x ↦ (hlt x).le) (hlt x₀)
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [← hbl.tsum_left_mul_right 0]
    exact ENNReal.tsum_le_tsum fun x ↦ (hlt x).le
  have hct : c ≠ ⊤ := fun h ↦ by
    rw [h, ENNReal.top_mul hδ0.ne'] at hcδ
    exact absurd hcδ (not_lt.2 le_top)
  set t : ℝ≥0∞ := c * δ with ht
  have ht0 : t ≠ 0 := mul_ne_zero hc0 hδ0.ne'
  have hδt : δ ≠ ⊤ := (hδ x₀).ne_top
  have htt : t ≠ ⊤ := ENNReal.mul_ne_top hct hδt
  have h1t0 : 1 - t ≠ 0 := (tsub_pos_of_lt hcδ).ne'
  have h1tt : 1 - t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hsum : t + (1 - t) = 1 := add_tsub_cancel_of_le hcδ.le
  have hδℓ : ∀ i x, δ * ℓ (i - p) x ≤ ℓ i x := fun i x ↦ (hbl.mul_left_sub_lt hδ i x).le
  have hδr : ∀ i x, δ * r (i + p) x ≤ r i x := fun i x ↦ (hbl.mul_right_add_lt hδ i x).le
  -- the four boundary laws of Georgii's proof
  have hbl1 : IsBoundaryLaw Q (fun i x ↦ ℓ (i - p) x / c) r := by
    refine IsBoundaryLaw.of_tsum
      (fun i x ↦ ENNReal.div_pos (hbl.left_pos _ _).ne' hct)
      (fun i x ↦ ENNReal.div_ne_top (hbl.left_ne_top _ _) hc0) hbl.right_pos hbl.right_ne_top
      (fun i y ↦ ?_) hbl.tsum_mul_right fun i ↦ ?_
    · simp_rw [div_eq_mul_inv, mul_right_comm _ c⁻¹]
      rw [ENNReal.tsum_mul_right, hbl.tsum_left_mul, show i - p + 1 = i + 1 - p by ring]
    · simp_rw [div_eq_mul_inv, mul_right_comm _ c⁻¹]
      rw [ENNReal.tsum_mul_right, hci', ENNReal.mul_inv_cancel hc0 hct]
  have hbl2 : IsBoundaryLaw Q (fun i x ↦ (ℓ i x - δ * ℓ (i - p) x) / (1 - t)) r := by
    refine IsBoundaryLaw.of_tsum
      (fun i x ↦ ENNReal.div_pos (tsub_pos_of_lt (hbl.mul_left_sub_lt hδ i x)).ne' h1tt)
      (fun i x ↦ ENNReal.div_ne_top (ne_top_of_le_ne_top (hbl.left_ne_top i x) tsub_le_self)
        h1t0) hbl.right_pos hbl.right_ne_top (fun i y ↦ ?_) hbl.tsum_mul_right fun i ↦ ?_
    · simp_rw [div_eq_mul_inv, mul_right_comm _ (1 - t)⁻¹]
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp_rw [ENNReal.sub_mul fun _ _ ↦ hQ.ne_top _ y]
      rw [ENNReal.tsum_tsub (fun x ↦ mul_le_mul' (hδℓ i x) le_rfl) ?_]
      · simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left, hbl.tsum_left_mul, hbl.tsum_left_mul,
          show i - p + 1 = i + 1 - p by ring]
      · simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left, hbl.tsum_left_mul]
        exact ENNReal.mul_ne_top hδt (hbl.left_ne_top _ _)
    · simp_rw [div_eq_mul_inv, mul_right_comm _ (1 - t)⁻¹]
      rw [ENNReal.tsum_mul_right]
      simp_rw [ENNReal.sub_mul fun _ _ ↦ hbl.right_ne_top i _]
      rw [ENNReal.tsum_tsub (fun x ↦ mul_le_mul' (hδℓ i x) le_rfl) ?_]
      · simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left, hbl.tsum_left_mul_right, hci', mul_comm δ c,
          ENNReal.mul_inv_cancel h1t0 h1tt]
      · simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left, hci']
        exact ENNReal.mul_ne_top hδt hct
  have hbl3 : IsBoundaryLaw Q ℓ (fun i x ↦ r (i + p) x / c) := by
    refine IsBoundaryLaw.of_tsum hbl.left_pos hbl.left_ne_top
      (fun i x ↦ ENNReal.div_pos (hbl.right_pos _ _).ne' hct)
      (fun i x ↦ ENNReal.div_ne_top (hbl.right_ne_top _ _) hc0) hbl.tsum_left_mul
      (fun i x ↦ ?_) fun i ↦ ?_
    · simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right, hbl.tsum_mul_right, show i + p - 1 = i - 1 + p by ring]
    · simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right, hci, ENNReal.mul_inv_cancel hc0 hct]
  have hbl4 : IsBoundaryLaw Q ℓ (fun i x ↦ (r i x - δ * r (i + p) x) / (1 - t)) := by
    refine IsBoundaryLaw.of_tsum hbl.left_pos hbl.left_ne_top
      (fun i x ↦ ENNReal.div_pos (tsub_pos_of_lt (hbl.mul_right_add_lt hδ i x)).ne' h1tt)
      (fun i x ↦ ENNReal.div_ne_top (ne_top_of_le_ne_top (hbl.right_ne_top i x) tsub_le_self)
        h1t0) hbl.tsum_left_mul (fun i x ↦ ?_) fun i ↦ ?_
    · simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      congr 1
      simp_rw [ENNReal.mul_sub fun _ _ ↦ hQ.ne_top x _]
      rw [ENNReal.tsum_tsub (fun y ↦ mul_le_mul' le_rfl (hδr i y)) ?_]
      · simp_rw [mul_left_comm (Q x _) δ]
        rw [ENNReal.tsum_mul_left, hbl.tsum_mul_right, hbl.tsum_mul_right,
          show i + p - 1 = i - 1 + p by ring]
      · simp_rw [mul_left_comm (Q x _) δ]
        rw [ENNReal.tsum_mul_left, hbl.tsum_mul_right]
        exact ENNReal.mul_ne_top hδt (hbl.right_ne_top _ _)
    · simp_rw [div_eq_mul_inv, ← mul_assoc]
      rw [ENNReal.tsum_mul_right]
      simp_rw [ENNReal.mul_sub fun _ _ ↦ hbl.left_ne_top i _]
      rw [ENNReal.tsum_tsub (fun x ↦ mul_le_mul' le_rfl (hδr i x)) ?_]
      · simp_rw [mul_left_comm (ℓ i _) δ]
        rw [ENNReal.tsum_mul_left, hbl.tsum_left_mul_right, hci, mul_comm δ c,
          ENNReal.mul_inv_cancel h1t0 h1tt]
      · simp_rw [mul_left_comm (ℓ i _) δ]
        rw [ENNReal.tsum_mul_left, hci]
        exact ENNReal.mul_ne_top hδt hct
  -- membership in `𝒢(Q)`
  have hG : ∀ {ℓ' r' : ℤ → E → ℝ≥0∞} (h : IsBoundaryLaw Q ℓ' r'),
      boundaryLawMeasure h ∈ G (transferSpecification Q hQ) := fun h ↦
    ⟨inferInstance, isGibbsMeasure_transferSpecification_boundaryLawMeasure hQ h⟩
  -- the convex decompositions `μ = t μ' + (1 - t) μ''`
  have hconv : ∀ {ℓ₁ ℓ₂ r₁ r₂ : ℤ → E → ℝ≥0∞} (h₁ : IsBoundaryLaw Q ℓ₁ r₁)
      (h₂ : IsBoundaryLaw Q ℓ₂ r₂),
      (∀ a b σ, t * (ℓ₁ a (σ a) * pathProd Q a b σ * r₁ b (σ b))
        + (1 - t) * (ℓ₂ a (σ a) * pathProd Q a b σ * r₂ b (σ b))
        = ℓ a (σ a) * pathProd Q a b σ * r b (σ b)) →
      boundaryLawMeasure hbl ∈ openSegment ℝ≥0∞ (boundaryLawMeasure h₁) (boundaryLawMeasure h₂)
          := by
    intro ℓ₁ ℓ₂ r₁ r₂ h₁ h₂ hcyl
    refine ⟨t, 1 - t, pos_iff_ne_zero.2 ht0, pos_iff_ne_zero.2 h1t0, hsum, ?_⟩
    have : IsProbabilityMeasure (t • boundaryLawMeasure h₁ + (1 - t) • boundaryLawMeasure h₂) :=
      ⟨by simp [hsum]⟩
    refine ext_of_centredCylinders 0 fun a b ha hb σ ↦ ?_
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      hbl.boundaryLawMeasure_intervalCylinder (by omega),
      h₁.boundaryLawMeasure_intervalCylinder (by omega),
      h₂.boundaryLawMeasure_intervalCylinder (by omega)]
    exact hcyl a b σ
  have e1 : ∀ a x, t * (ℓ (a - p) x / c) = δ * ℓ (a - p) x := fun a x ↦ by
    rw [ht, mul_comm c δ, mul_assoc, ENNReal.mul_div_cancel hc0 hct]
  have e2 : ∀ a x, t * (r (a + p) x / c) = δ * r (a + p) x := fun a x ↦ by
    rw [ht, mul_comm c δ, mul_assoc, ENNReal.mul_div_cancel hc0 hct]
  have hseg12 := hconv hbl1 hbl2 fun a b σ ↦ by
    calc t * (ℓ (a - p) (σ a) / c * pathProd Q a b σ * r b (σ b))
          + (1 - t) * ((ℓ a (σ a) - δ * ℓ (a - p) (σ a)) / (1 - t) * pathProd Q a b σ * r b (σ b))
        = (t * (ℓ (a - p) (σ a) / c)
            + (1 - t) * ((ℓ a (σ a) - δ * ℓ (a - p) (σ a)) / (1 - t)))
            * pathProd Q a b σ * r b (σ b) := by ring
      _ = (δ * ℓ (a - p) (σ a) + (ℓ a (σ a) - δ * ℓ (a - p) (σ a)))
            * pathProd Q a b σ * r b (σ b) := by
          rw [e1, ENNReal.mul_div_cancel h1t0 h1tt]
      _ = _ := by rw [add_tsub_cancel_of_le (hδℓ a (σ a))]
  have hseg34 := hconv hbl3 hbl4 fun a b σ ↦ by
    calc t * (ℓ a (σ a) * pathProd Q a b σ * (r (b + p) (σ b) / c))
          + (1 - t) * (ℓ a (σ a) * pathProd Q a b σ * ((r b (σ b) - δ * r (b + p) (σ b)) / (1 - t)))
        = ℓ a (σ a) * pathProd Q a b σ * (t * (r (b + p) (σ b) / c)
            + (1 - t) * ((r b (σ b) - δ * r (b + p) (σ b)) / (1 - t))) := by ring
      _ = ℓ a (σ a) * pathProd Q a b σ
            * (δ * r (b + p) (σ b) + (r b (σ b) - δ * r (b + p) (σ b))) := by
          rw [e2, ENNReal.mul_div_cancel h1t0 h1tt]
      _ = _ := by rw [add_tsub_cancel_of_le (hδr b (σ b))]
  -- extremality forces `μ' = μ`
  obtain ⟨h1, -⟩ := (mem_extremePoints.1 hext).2 _ (hG hbl1) _ (hG hbl2) hseg12
  obtain ⟨h3, -⟩ := (mem_extremePoints.1 hext).2 _ (hG hbl3) _ (hG hbl4) hseg34
  have hℓper : ∀ i x, ℓ (i - p) x = c * ℓ i x := fun i x ↦ by
    have h : boundaryLawMeasure hbl1 (intervalCylinder i i fun _ ↦ x)
        = boundaryLawMeasure hbl (intervalCylinder i i fun _ ↦ x) := by rw [h1]
    rw [hbl1.boundaryLawMeasure_intervalCylinder le_rfl,
      hbl.boundaryLawMeasure_intervalCylinder le_rfl, pathProd_self, mul_one, mul_one] at h
    have h' := (ENNReal.mul_left_inj (hbl.right_pos i x).ne' (hbl.right_ne_top i x)).1 h
    exact ((ENNReal.eq_div_iff hc0 hct).1 h'.symm).symm
  have hrper : ∀ i x, r (i + p) x = c * r i x := fun i x ↦ by
    have h : boundaryLawMeasure hbl3 (intervalCylinder i i fun _ ↦ x)
        = boundaryLawMeasure hbl (intervalCylinder i i fun _ ↦ x) := by rw [h3]
    rw [hbl3.boundaryLawMeasure_intervalCylinder le_rfl,
      hbl.boundaryLawMeasure_intervalCylinder le_rfl, pathProd_self, mul_one] at h
    have h' := (ENNReal.mul_right_inj (hbl.left_pos i x).ne' (hbl.left_ne_top i x)).1 h
    exact ((ENNReal.eq_div_iff hc0 hct).1 h'.symm).symm
  exact hbl.boundaryLawMeasure_map_shift_eq_self_of_periodic hℓper hrper

/-- **The argument of Georgii Theorem (11.15)**, with the hypothesis in Georgii's form
`inf_x Q^p(x, x) > 0`. -/
theorem IsBoundaryLaw.boundaryLawMeasure_map_shift_eq_self_of_iInf_pos
    (hext : boundaryLawMeasure hbl ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞)
    {p : ℕ} (hp : 0 < ⨅ x, (Kernel.ofMatrix Q ^ p) x {x}) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E (p : ℤ)).toFun = boundaryLawMeasure hbl := by
  obtain ⟨x₀⟩ := ‹Nonempty E›
  have hne : (⨅ x, (Kernel.ofMatrix Q ^ p) x {x}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (iInf_le _ x₀)
    cases p with
    | zero => rw [Kernel.pow_zero_apply_singleton]; simp
    | succ p => exact hQ.pow_ne_top p x₀ x₀
  refine hbl.boundaryLawMeasure_map_shift_eq_self_of_mem_extremePoints hQ hext
    (ENNReal.half_pos hp.ne') fun x ↦ (ENNReal.half_lt_self hp.ne' hne).trans_le (iInf_le _ x)

/-- **The argument of Georgii Theorem (11.15)**, with Georgii's stated hypothesis
`inf_x ∑_{n=1}^N Q^n(x, x) > 0`: the measure of a boundary law which is extreme in `𝒢(Q)` is
`θ_{N!}`-invariant. -/
theorem IsBoundaryLaw.boundaryLawMeasure_map_shift_factorial_eq_self
    (hext : boundaryLawMeasure hbl ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞)
    {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    (boundaryLawMeasure hbl).map (GibbsMeasure.shift E (N.factorial : ℤ)).toFun
      = boundaryLawMeasure hbl := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_pos_lt_pow_factorial_apply_of_le_sum Q hN hε h
  exact hbl.boundaryLawMeasure_map_shift_eq_self_of_mem_extremePoints hQ hext hδ0 hδ

end Periodicity

/-! ## Georgii Comment (11.18)(1): lazy chains `Q = tP + (1 - t)I` -/

section Lazy

variable {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}

/-- The lazy matrix `Q = tP + (1 - t)I` of Georgii Comment (11.18)(1). -/
def lazy (P : E → E → ℝ≥0∞) (t : ℝ≥0∞) (x y : E) : ℝ≥0∞ :=
  t * P x y + (1 - t) * ({y} : Set E).indicator 1 x

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma lazy_pos (hpos : ∀ x y, 0 < P x y) (ht : t ≠ 0) (x y : E) : 0 < lazy P t x y :=
  add_pos_of_left (ENNReal.mul_pos ht (hpos x y).ne') _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- `inf_x Q(x, x) ≥ 1 - t` for `Q = tP + (1 - t)I`. -/
lemma le_lazy_apply_self (x : E) : 1 - t ≤ lazy P t x x := by
  simp [lazy]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- `Q = tP + (1 - t)I` is stochastic when `P` is and `t ≤ 1`. -/
lemma lazy_stochastic (hP : ∀ x, ∑' y, P x y = 1) (ht : t ≤ 1) (x : E) :
    ∑' y, lazy P t x y = 1 := by
  simp only [lazy]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hP,
    tsum_eq_single x fun y hy ↦ by simp [Ne.symm hy]]
  simp [add_tsub_cancel_of_le ht]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- An invariant vector of `P` is invariant for `Q = tP + (1 - t)I`. -/
lemma tsum_mul_lazy {α : E → ℝ≥0∞} (hαP : ∀ y, ∑' x, α x * P x y = α y) (ht : t ≤ 1) (y : E) :
    ∑' x, α x * lazy P t x y = α y := by
  simp only [lazy, mul_add]
  rw [ENNReal.tsum_add]
  simp_rw [mul_left_comm (α _) t, mul_left_comm (α _) (1 - t)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hαP, tsum_eq_single y fun x hx ↦ by simp [hx]]
  simp [← add_mul, add_tsub_cancel_of_le ht]

end Lazy

/-! ## Georgii Comment (11.18)(1): `Q = tP + (1 - t)I` satisfies the hypotheses of Theorem (11.13)
(existence half) and of Theorem (11.15)/(11.16) at `p = 1`

Comment (11.18)(1) asserts that "the uniqueness condition of Corollary (11.17) certainly holds
whenever `Q = tP + (1-t)I` with `0 < t < 1` and `P` a positive recurrent positive stochastic
matrix". Corollary (11.17) itself (`𝒢(Q) = {μ_P}` or `𝒢(Q) = ∅`) is **not** in this file: its
proof needs the "only if" half of Theorem (11.13) — see the module docstring for exactly what
that half needs and why it is not here. What Comment (11.18)(1) actually *certifies* about `Q`,
and what is proved below, is that `Q` satisfies the two hypotheses that feed into (11.17): the
existence hypothesis of Theorem (11.13) (`Q` equivalent to a positive recurrent positive
stochastic matrix — here, trivially, to itself) and the periodicity hypothesis of Theorem
(11.15)/(11.16), `inf_x Q(x, x) > 0`, at `p = 1`. -/

section Lazy

variable [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞} (hpos : ∀ x y, 0 < P x y)
  (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1)
include hpos hP ht0 ht1

omit [Nonempty E] in
/-- **Georgii Comment (11.18)(1), first clause.** For `0 < t < 1` and a positive stochastic `P`,
`Q = tP + (1 - t)I` is again a transfer matrix. -/
theorem lazy_isTransferMatrix : IsTransferMatrix (lazy P t) :=
  isTransferMatrix_of_stochastic (lazy_pos hpos ht0) (lazy_stochastic hP ht1.le)

omit [Nonempty E] hpos hP ht0 in
/-- **Georgii Comment (11.18)(1), periodicity clause.** `inf_x Q(x, x) ≥ 1 - t > 0`: the
hypothesis of Theorem (11.15)/(11.16) at `p = 1` (with `N = 1` in Georgii's stated form
`inf_x ∑_{n=1}^N Q^n(x, x) > 0`). -/
theorem iInf_lazy_apply_self_pos :
    0 < ⨅ x, (Kernel.ofMatrix (lazy P t) ^ 1) x {x} :=
  lt_of_lt_of_le (tsub_pos_of_lt ht1) (le_iInf fun x ↦ by
    rw [Kernel.ofMatrix_pow_one_apply_singleton]; exact le_lazy_apply_self x)

variable {α : E → ℝ≥0∞} (hα0 : ∀ x, 0 < α x) (hαt : ∀ x, α x ≠ ⊤) (hα1 : ∑' x, α x = 1)
  (hαP : ∀ y, ∑' x, α x * P x y = α y)
include hα0 hαt hα1 hαP

/-- **Georgii Comment (11.18)(1), existence clause.** An invariant probability vector `α` of `P`
is also invariant for `Q = tP + (1 - t)I`, so Georgii's `μ_Q` lies in `𝒢_Θ(Q)` by the existence
half of Theorem (11.13) (`boundaryLawMeasure_const_mem_invariantG`). Together with
`lazy_isTransferMatrix` and `iInf_lazy_apply_self_pos`, this assembles the whole content of
Comment (11.18)(1) that does not require the "only if" half of Theorem (11.13). -/
theorem boundaryLawMeasure_const_lazy_mem_invariantG :
    boundaryLawMeasure (isBoundaryLaw_const (lazy_stochastic hP ht1.le) hα0 hαt hα1
        (tsum_mul_lazy hαP ht1.le))
      ∈ invariantG (transferSpecification (lazy P t) (lazy_isTransferMatrix hpos hP ht0 ht1))
        (shiftGroup ℤ E) :=
  boundaryLawMeasure_const_mem_invariantG (lazy_pos hpos ht0) (lazy_stochastic hP ht1.le) hα0 hαt
    hα1 (tsum_mul_lazy hαP ht1.le) (lazy_isTransferMatrix hpos hP ht0 ht1) rfl

end Lazy

/-! ## Obstruction (i): `γ^Q` as the λ-specification of a probability measure

`transferSpecification Q hQ` is the λ-specification of *counting* measure (`Model/BoundaryLaw.
lean`), while Chapter 10's Markov theory (`Specification.IsMarkovianInt`,
`Specification.IsHomogeneousInt`, `Specification.IsIrreducibleInt`, Theorem (10.35)
`MeasureTheory.GibbsMeasure.Markov.eq_of_isGibbsMeasure_of_measurePreserving_shift`,
`Specification/MarkovIntUniqueness.lean`) is stated for a `λ`-modification of a *probability*
measure `ν`. Georgii's own aside before (10.13), "we may assume `λ ∈ 𝒫(E, 𝓔)`", bridges the two:
`Specification/Rescaling.lean`'s `MeasureTheory.Measure.
exists_measurable_pos_isProbabilityMeasure_withDensity` supplies a positive measurable `r` with
`count.withDensity r` a probability measure, and `Specification.
lambdaSpecification_eq_isssd_withDensity` (Remark (1.28)(3), generalized here from its singleton
case) identifies `γ^Q` with the `isssd`-density form Chapter 10 expects, unchanged as a
specification. -/

section MarkovBridge

variable [Nonempty E]

/-- **Georgii, aside before (10.13).** A fixed choice of the positive measurable density that
turns counting measure on the countable `E` into a probability measure (Georgii's `r` with
`λ(r) = 1`). -/
noncomputable def countProbDensity : E → ℝ≥0∞ :=
  (Measure.exists_measurable_pos_isProbabilityMeasure_withDensity
    (Measure.count : Measure E)).choose

lemma measurable_countProbDensity : Measurable (countProbDensity (E := E)) :=
  (Measure.exists_measurable_pos_isProbabilityMeasure_withDensity
    (Measure.count : Measure E)).choose_spec.1

lemma countProbDensity_ne_zero (x : E) : countProbDensity (E := E) x ≠ 0 :=
  (Measure.exists_measurable_pos_isProbabilityMeasure_withDensity
    (Measure.count : Measure E)).choose_spec.2.1 x

lemma countProbDensity_ne_top (x : E) : countProbDensity (E := E) x ≠ ⊤ :=
  (Measure.exists_measurable_pos_isProbabilityMeasure_withDensity
    (Measure.count : Measure E)).choose_spec.2.2.1 x

instance isProbabilityMeasure_count_withDensity_countProbDensity :
    IsProbabilityMeasure ((Measure.count : Measure E).withDensity (countProbDensity (E := E))) :=
  (Measure.exists_measurable_pos_isProbabilityMeasure_withDensity
    (Measure.count : Measure E)).choose_spec.2.2.2

/-- **Georgii's rescaled probability a priori measure `λ̃ = r · count`** for counting measure on a
countable `E`. An `abbrev` (not a `def`): it is definitionally, and for typeclass search
transparently, `count.withDensity (countProbDensity E)`, so `isProbabilityMeasure_count_
withDensity_countProbDensity` already supplies `IsProbabilityMeasure (countProb E)`. -/
noncomputable abbrev countProb : Measure E :=
  (Measure.count : Measure E).withDensity (countProbDensity (E := E))

lemma countProb_def :
    countProb (E := E) = (Measure.count : Measure E).withDensity (countProbDensity (E := E)) :=
  rfl

/-- **Georgii's rescaled Markovian λ-modification `ρ̃`** for `γ^Q`, Remark (1.28)(3): the
normalized density of `Specification.rescale (countProbDensity E) (transferWeight Q)` against
`countProb`. -/
noncomputable def rescaledTransferDensity (Q : E → E → ℝ≥0∞) :
    Finset ℤ → (ℤ → E) → ℝ≥0∞ :=
  Specification.premodifierNorm (countProb (E := E))
    (Specification.rescale (countProbDensity (E := E)) (transferWeight Q))

variable (Q : E → E → ℝ≥0∞) (hQ : IsTransferMatrix Q)

lemma measurable_rescaledTransferDensity (Λ : Finset ℤ) :
    Measurable (rescaledTransferDensity Q Λ) := by
  rw [rescaledTransferDensity, Specification.premodifierNorm_eq_sigmaFinitePremodifierNorm]
  exact Specification.sigmaFinitePremodifierNorm_measurable (countProb (E := E))
    (Specification.isPremodifier_rescale measurable_countProbDensity countProbDensity_ne_zero
      countProbDensity_ne_top (isPremodifier_transferWeight Q)) Λ

/-- **Obstruction (i), first bullet.** `γ^Q = transferSpecification Q hQ` is the λ-specification
of the *probability* measure `countProb`, with Markovian density `rescaledTransferDensity Q`. -/
theorem transferSpecification_eq_isssd_withDensity (Λ : Finset ℤ) (η : ℤ → E) :
    transferSpecification Q hQ Λ η
      = (Specification.isssd (S := ℤ) (E := E) (countProb (E := E)) Λ η).withDensity
          (rescaledTransferDensity Q Λ) := by
  unfold transferSpecification rescaledTransferDensity countProb
  rw [Specification.lambdaSpecification_eq_lambdaSpecification_withDensity (S := ℤ) (E := E)
      Measure.count measurable_countProbDensity countProbDensity_ne_zero countProbDensity_ne_top
      (isPremodifier_transferWeight Q) hQ.isSigmaFiniteLambdaAdmissible,
    Specification.lambdaSpecification_eq_modification_isssd, Specification.modification_apply]

/-! ### Obstruction (i), second and third bullets: `rescaledTransferDensity Q` is Markovian and
homogeneous -/

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] [Nonempty E] hQ in
/-- The bonds meeting the open interval `]i, k[` are exactly `[i, k[`. -/
lemma bondsOf_Ioo {i k : ℤ} (hik : i + 1 < k) : bondsOf (Finset.Ioo i k) = Finset.Ico i k := by
  ext j
  rw [mem_bondsOf]
  simp only [Finset.mem_Ioo, Finset.mem_Ico]
  omega

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] [Nonempty E] hQ in
/-- The transfer weight of the open interval `]i, k[` is the bond product over `[i, k[`. -/
lemma transferWeight_Ioo {i k : ℤ} (hik : i + 1 < k) (σ : ℤ → E) :
    transferWeight Q (Finset.Ioo i k) σ = pathProd Q i k σ := by
  rw [transferWeight, bondsOf_Ioo hik]; rfl

omit [Nonempty E] hQ in
/-- **Georgii (11.2), the partition function of an open interval.** `Z_{]i,k[}(ω) =
Q^{k-i}(ω_i, ω_k)`. -/
lemma sigmaFiniteLambdaZ_transferWeight_Ioo {i k : ℤ} (hik : i + 1 < k) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
        (Finset.Ioo i k) ω
      = (Kernel.ofMatrix Q ^ (k - i).toNat) (ω i) {ω k} := by
  have hΛ : Finset.Ioo i k = Finset.Icc (i + 1) (k - 1) := by
    ext j
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  have he1 : i + 1 - 1 = i := by omega
  have he2 : k - 1 + 1 = k := by omega
  have he3 : (k - 1 - (i + 1) + 2).toNat = (k - i).toNat := by omega
  rw [hΛ, sigmaFiniteLambdaZ_transferWeight_Icc Q (by omega : i + 1 ≤ k - 1), he1, he2, he3]

omit [Nonempty E] in
/-- Two coordinate evaluations, composed with an arbitrary function of a countable state space,
are cylinder-events measurable on any set containing both coordinates. -/
lemma measurable_cylinderEvents_pair {Δ : Set ℤ} (g : E → E → ℝ≥0∞) {j l : ℤ}
    (hj : j ∈ Δ) (hl : l ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : ℤ → E ↦ g (σ j) (σ l)) :=
  (measurable_of_countable fun p : E × E ↦ g p.1 p.2).comp
    (f := fun σ : ℤ → E ↦ (σ j, σ l))
    ((measurable_cylinderEvent_apply hj).prodMk (measurable_cylinderEvent_apply hl))

omit [Nonempty E] hQ in
lemma measurable_cylinderEvents_transferWeight_Ioo {i k : ℤ} (hik : i + 1 < k) :
    Measurable[cylinderEvents (Set.Icc i k)] fun ω : ℤ → E ↦
      transferWeight Q (Finset.Ioo i k) ω := by
  have h : (fun ω : ℤ → E ↦ transferWeight Q (Finset.Ioo i k) ω)
      = fun ω ↦ ∏ j ∈ Finset.Ico i k, Q (ω j) (ω (j + 1)) := funext (transferWeight_Ioo Q hik)
  rw [h]
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  simp only [Finset.mem_Ico] at hj
  have hj1 : j ∈ Set.Icc i k := Set.mem_Icc.2 (by omega)
  have hj2 : j + 1 ∈ Set.Icc i k := Set.mem_Icc.2 (by omega)
  exact measurable_cylinderEvents_pair Q hj1 hj2

lemma measurable_cylinderEvents_lambdaWeight_countProbDensity {Δ : Set ℤ} {Λ : Finset ℤ}
    (hΛ : (Λ : Set ℤ) ⊆ Δ) :
    Measurable[cylinderEvents Δ] fun ω : ℤ → E ↦
      Specification.lambdaWeight (S := ℤ) (E := E) (fun _ ↦ countProbDensity (E := E)) Λ ω := by
  refine Finset.measurable_prod _ fun j hj ↦ ?_
  exact (measurable_of_countable (countProbDensity (E := E))).comp
    (measurable_cylinderEvent_apply (hΛ (Finset.mem_coe.2 hj)))

omit [Nonempty E] hQ in
lemma measurable_cylinderEvents_sigmaFiniteLambdaZ_transferWeight_Ioo {i k : ℤ}
    (hik : i + 1 < k) :
    Measurable[cylinderEvents (Set.Icc i k)] fun ω : ℤ → E ↦
      Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
        (Finset.Ioo i k) ω := by
  have h : (fun ω : ℤ → E ↦ Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count
        (transferWeight Q) (Finset.Ioo i k) ω)
      = fun ω ↦ (Kernel.ofMatrix Q ^ (k - i).toNat) (ω i) {ω k} :=
    funext (sigmaFiniteLambdaZ_transferWeight_Ioo Q hik)
  rw [h]
  have hi : i ∈ Set.Icc i k := Set.mem_Icc.2 (by omega)
  have hk : k ∈ Set.Icc i k := Set.mem_Icc.2 (by omega)
  exact measurable_cylinderEvents_pair (fun x y ↦ (Kernel.ofMatrix Q ^ (k - i).toNat) x {y}) hi hk

omit hQ in
/-- The unfolded form of `rescaledTransferDensity`, in terms of the unrescaled transfer weight,
the counting-measure partition function, and the rescaling weight of `countProbDensity`. -/
lemma rescaledTransferDensity_apply (Λ : Finset ℤ) (ω : ℤ → E) :
    rescaledTransferDensity Q Λ ω
      = (transferWeight Q Λ ω / Specification.lambdaWeight (S := ℤ) (E := E)
            (fun _ ↦ countProbDensity (E := E)) Λ ω)
          / Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count
              (transferWeight Q) Λ ω := by
  unfold rescaledTransferDensity countProb
  rw [Specification.premodifierNorm_eq_sigmaFinitePremodifierNorm,
    Specification.sigmaFinitePremodifierNorm, Specification.rescale_apply,
    Specification.sigmaFiniteLambdaZ_rescale Measure.count measurable_countProbDensity
      countProbDensity_ne_zero countProbDensity_ne_top (fun Λ ↦ measurable_transferWeight Q Λ)]

omit hQ in
/-- **Obstruction (i), second bullet.** `rescaledTransferDensity Q` is Markovian
(`Specification.IsMarkovianInt`): a genuine construction from the closed forms of the transfer
weight and the counting-measure partition function of an open interval. -/
theorem isMarkovianInt_rescaledTransferDensity :
    Specification.IsMarkovianInt (rescaledTransferDensity Q) := by
  intro i k hik
  have h : rescaledTransferDensity Q (Finset.Ioo i k) = fun ω ↦
      (transferWeight Q (Finset.Ioo i k) ω / Specification.lambdaWeight (S := ℤ) (E := E)
            (fun _ ↦ countProbDensity (E := E)) (Finset.Ioo i k) ω)
        / Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count
            (transferWeight Q) (Finset.Ioo i k) ω :=
    funext (rescaledTransferDensity_apply Q (Finset.Ioo i k))
  rw [h]
  have hsub : (Finset.Ioo i k : Set ℤ) ⊆ Set.Icc i k := fun x hx ↦ by
    rw [Finset.mem_coe, Finset.mem_Ioo] at hx
    exact Set.mem_Icc.2 (by omega)
  exact ((measurable_cylinderEvents_transferWeight_Ioo Q hik).div
      (measurable_cylinderEvents_lambdaWeight_countProbDensity hsub)).div
    (measurable_cylinderEvents_sigmaFiniteLambdaZ_transferWeight_Ioo Q hik)

end MarkovBridge

end MeasureTheory.GibbsMeasure.Markov

end

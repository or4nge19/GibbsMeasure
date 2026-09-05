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
public import GibbsMeasure.Specification.ExtremeCorollaries
public import GibbsMeasure.Specification.ExtremeDecomposition
public import GibbsMeasure.Specification.InvariantDecomposition
public import GibbsMeasure.Specification.MarkovIntUniqueness

/-!
# Georgii §11.1, from Theorem (11.9)(b) on: Markov chains in `𝒢(Q)`, boundary laws for extreme
points, Corollaries (11.14) and (11.17), and Theorem (11.15) in full

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
* `ofMatrix_lazy_pow_apply_singleton`, `lazy_convergenceNorm_le`,
  `one_le_lazy_convergenceNorm_of_convergenceNorm_eq_one`,
  `lazy_convergenceNorm_eq_one_of_convergenceNorm_eq_one`,
  `isPositiveRecurrent_ofMatrix_of_isPositiveRecurrent_lazy`,
  `eq_empty_G_lazy_of_not_isPositiveRecurrent` — **Georgii Comment (11.18)(3), in full**: the
  binomial identity for `Q = tP + (1-t)I`, the resulting `L(Q) = tL(P) + (1-t)` (both directions),
  hence `L(P) = 1 ⟹ L(Q) = 1`, and the non-existence conclusion `𝒢(γ^Q) = ∅` when `P` is a positive
  stochastic matrix with `L(P) = 1` that is not positive recurrent. See the docstring above
  `Georgii Comment (11.18)(3)` (after `end MarkovBridge`, further down this file) for the argument
  in full.
* **Obstruction (i) resolved.** `countProbDensity`, `countProb`, `rescaledTransferDensity Q`
  (Georgii's rescaled probability a priori measure and Markovian λ-modification, Remark (1.28)(3)),
  `transferSpecification_eq_isssd_withDensity` (`γ^Q = (isssd countProb Λ ·).withDensity
  (rescaledTransferDensity Q Λ)`), `isMarkovianInt_rescaledTransferDensity`,
  `isHomogeneousInt_rescaledTransferDensity` (**Specification.IsHomogeneousInt**, for *every*
  finite volume, via the shift-covariance of `transferWeight`, of the constant
  `countProbDensity`-weight (elementary `Finset` combinatorics on `bondsOf`), and of the
  counting-measure partition function `sigmaFiniteLambdaFun`/`sigmaFiniteLambdaZ` — the last via
  the same juxtaposition/reindexing argument that gives `isssd` its shift-equivariance
  (`MeasureTheory.GibbsMeasure.Transformation.toFun_comp_juxt`,
  `.measurePreserving_spin_piCongrLeft`, which need only `[SigmaFinite ν]`, not
  `[IsProbabilityMeasure ν]`) — and `isIrreducibleInt_rescaledTransferDensity` (**Specification.
  IsIrreducibleInt**, Georgii's Definition (10.23), with `n(N) ≡ 1` since `Q > 0` everywhere;
  a special case of `isIrreducibleInt_rescaledTransferDensity_of_eventually`, see the next bullet).
* `marginalDensity_rescaledTransferDensity_Ioo`,
  `isIrreducibleInt_rescaledTransferDensity_of_eventually`,
  `isIrreducibleInt_rescaledTransferDensity_of_isAperiodic` — **Georgii Example (10.24)(2)**, as
  stated: for a stochastic `P` on the countable `E` that is irreducible and aperiodic, the
  Markovian `λ`-modification `ρ` of Example (10.3) with `p_j = P` (here `rescaledTransferDensity
  P`, Georgii's `ρ` after his reduction to the probability a priori measure `countProb`) is
  irreducible in the sense of (10.23), with `C_N := countExhaustion N` a finite exhaustion built
  from a fixed enumeration `enumE : ℕ → E`, `n(N)` a step count beyond which `P^n > 0` on
  `C_N × C_N`, and the witness `irreducibleWitness P (n N) N x := (inf_{y, z ∈ C_N} P^n(y, x)
  P^n(x, z) / P^{2n}(y, z)) / countProbDensity(x)`; the marginal density
  `ρ^0_{]-n,n[}(ω) = P^n(ω_{-n}, ω_0) P^n(ω_0, ω_n) / (countProbDensity(ω_0) P^{2n}(ω_{-n}, ω_n))`
  is Georgii's second display. Georgii's cited input (Breiman, Ch. 7) — an aperiodic irreducible
  `P` has `P^n(x, y) > 0` for all large `n` — is `ProbabilityTheory.Kernel.period`,
  `Kernel.IsAperiodic` and `Kernel.eventually_pow_apply_singleton_pos`
  (`GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix/Recurrence.lean`).
* `mem_extremePoints_G_transferSpecification_of_measurePreserving_shift`,
  `eq_of_isGibbsMeasure_transferSpecification_of_measurePreserving_shift`,
  `exists_isMarkovChain_transferSpecification_of_measurePreserving_shift` — **Georgii Theorems
  (10.35) and (10.25), instantiated at `γ^Q`**: every shift-invariant Gibbs measure for `γ^Q` is
  extreme in `𝒢(γ^Q)`; `𝒢_Θ(γ^Q)` is a subsingleton (unconditionally, not only when it is known to
  come from a boundary law); every shift-invariant Gibbs measure for `γ^Q` is a Markov chain for a
  *single* transition kernel.
* `Kernel.isIrreducible_count_ofMatrix_of_forall_pos`,
  `exists_transferMatrix_equiv_and_isPositiveRecurrent_of_invariantG_nonempty` — **Georgii Theorem
  (11.13), the "only if" half**: if `𝒢_Θ(γ^Q) ≠ ∅`, `Q` is equivalent, in the sense of (11.5), to
  a positive recurrent stochastic matrix. See below for exactly how this closes the gaps the
  previous version of this docstring recorded, and what remains.
* `exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints` — **Georgii Theorem
  (11.9)(c)**, representation clause: every `μ ∈ ex 𝒢(Q)` is the measure of a boundary law.
* `isInvariant_shift_transferSpecification`, `mem_G_map_shift_of_mem_G`,
  `mem_extremePoints_G_map_shift_of_mem_extremePoints` — shift-covariance of `γ^Q` as a
  specification, and Remarks (5.10)/(7.2) for it.
* `map_shift_eq_self_of_map_shift_eq_of_mem_G` — **Georgii Corollary (11.14)(a)**, in full
  generality, by a Cesàro-averaging argument (see the module doc above `section
  CorollaryOneOneFourteenA`) that needs no `Q^p` subsampling.
* `eq_singleton_boundaryLawMeasure_const_or_infinite_extremePoints_G`,
  `eq_empty_G_or_infinite_extremePoints_G` — **Georgii Corollary (11.14)(b), (c)**.
* `G_eq_invariantG_of_forall_le_sum` — **Georgii Theorem (11.15)**, for a general extreme point.
* `eq_singleton_boundaryLawMeasure_const_G_of_forall_le_sum`, `eq_empty_G_of_forall_le_sum` —
  **Georgii Corollary (11.17)**, both halves.

## Georgii Theorem (11.13), in full, and what is not here

Both directions are now in the library, each as its own theorem (an explicit `iff` packaging the
two together is not — see below):

* **"if"**: `stationaryChain_mem_invariantG` / `invariantG_nonempty_of_rel` (`Q ~ P` for a positive
  stochastic `P` with an invariant probability vector `α` gives `𝒢_Θ(γ^Q) ≠ ∅`).
* **"only if"**: `exists_transferMatrix_equiv_and_isPositiveRecurrent_of_invariantG_nonempty`
  (`𝒢_Θ(γ^Q) ≠ ∅` gives `Q ~ P` for a positive recurrent stochastic `P`).
* **uniqueness**: `eq_of_isGibbsMeasure_transferSpecification_of_measurePreserving_shift` shows
  `𝒢_Θ(γ^Q)` is a subsingleton *unconditionally* (not merely "if non-empty"), which is the
  uniqueness clause of (11.13) together with more.

The genuine mathematical content of the "only if" direction turned out to need **less** than the
previous version of this docstring anticipated. It expected a hard rigidity argument: Theorem
(10.25) supplies a single transition kernel `P` for `μ ∈ 𝒢_Θ(γ^Q)`; Theorem (11.9)(b)
(`IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure`, already in this file before this
revision) represents `μ` by a boundary law `{ℓ_i, r_i}` for `Q` with `P(x, y) r_{i-1}(x) =
Q(x, y) r_i(y)` for *every* `i`; identifying `P` with a matrix equivalent to `Q` in the fixed,
`i`-independent sense of (11.5) seemed to need the sequence `r_i` itself to be (eventually)
`i`-independent, which in turn looked like it would need a cocycle-rigidity argument on the
constants `c_j` relating `{ℓ_i, r_i}` to its shift `{ℓ_{i-j}, r_{i-j}}` (both representing `μ`,
since `μ` is shift-invariant): `j ↦ c_j` is a homomorphism `ℤ → (0, ∞)`, and ruling out `c_j ≠ 1`
looked like the missing ingredient. **It is not needed.** The (11.11) relation is used at the
*single* index `i = 0` only: `P(x, y) r_{-1}(x) = Q(x, y) r_0(y)`, and the *single* proportionality
constant `c := c_1` (`IsBoundaryLaw.exists_const_of_boundaryLawMeasure_eq` applied once, at the
shift `j = 1`, using only `θ_1(μ) = μ`) gives `r_{-1}(x) = c \, r_0(x)` directly, which turns the
`i = 0` relation into exactly `P(x, y) = Q(x, y) r_0(y) / (c \, r_0(x))` — Georgii's (11.5), with
`q := c`, `r := r_0`. No homomorphism, no rigidity, no case on `c_j`. Positive recurrence of `P` is
comparatively routine given the library already in the tree:
`IsMarkovChain.kernel_singleton_pos` gives `P(x, y) > 0` for every pair, hence `Kernel.ofMatrix P`
is irreducible for counting measure (`Kernel.isIrreducible_count_ofMatrix_of_forall_pos`, new,
    general:
belongs upstream next to `ProbabilityTheory.Kernel.isRecurrent_of_invariant` in
`GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix/Recurrence.lean`); the shift-invariant
marginal `α(x) := μ(σ_0 = x)` is an invariant probability measure for `P`
(`IsMarkovChain.tsum_measure_preimage_mul` plus shift-invariance of the marginals,
`map_eval_eq_of_measurePreserving_shift`); and `isRecurrent_of_invariant`, already in
`Recurrence.lean`, does the rest.

**What genuinely remains** of Theorem (11.13) itself:

* An explicit `iff` combining `invariantG_nonempty_of_rel` and
  `exists_transferMatrix_equiv_and_isPositiveRecurrent_of_invariantG_nonempty` into one
  biconditional statement. This is bookkeeping, not new mathematics: the only missing step is
  extracting, from an arbitrary `IsPositiveRecurrent (Kernel.ofMatrix P)`'s invariant probability
  measure `μ`, the *positivity* `∀ x, 0 < μ {x}` that `invariantG_nonempty_of_rel`'s hypothesis
  `hα0` demands (from `P` positive everywhere plus `Invariant.apply_singleton_eq_tsum`,
  `μ {y} ≥ P z y \cdot μ {z}` for a single `z` with `μ {z} > 0`, itself from `μ ≠ 0` on a countable
  space) — routine, not attempted for lack of time.

## Theorem (11.9)(c) through Corollary (11.17): all now in the library

* **Theorem (11.9)(c), representation clause**:
  `exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints` — every `μ ∈ ex 𝒢(Q)` is the
  measure of a boundary law, via Theorem (10.21) (`exists_isMarkovChain_of_mem_extremePoints`,
  already in `MarkovIntChains.lean`) instantiated at `γ^Q` through
  `transferSpecification_eq_isssd_withDensity` / `measurable_rescaledTransferDensity` /
  `isMarkovianInt_rescaledTransferDensity`, then Theorem (11.9)(b). Georgii's quantitative
  "moreover" clause (the explicit limit formula for `ℓ_i`, `r_i`) is not proved: it is not needed
  for anything below. `map_shift_factorial_eq_self_of_mem_extremePoints` packages the immediate
  consequence: every extreme point satisfies `θ_{N!}(μ) = μ` under Georgii's hypothesis.
* **Shift-covariance of `γ^Q` as a specification** (`isInvariant_shift_transferSpecification`,
  from `transferSpecification_map_transl`, assembled from the shift-covariance of `transferWeight`,
  `sigmaFiniteLambdaZ`, and `sigmaFiniteLambdaFun` already used for
  `isHomogeneousInt_rescaledTransferDensity`, but there never combined into the covariance of the
  *specification itself*): gives Remark (5.10) for `γ^Q` (`mem_G_map_shift_of_mem_G`) and Remark
  (7.2) for `γ^Q` (`mem_extremePoints_G_map_shift_of_mem_extremePoints`), neither available for a
  general `transferSpecification` before this file.
* **Corollary (11.14)(a)** (`map_shift_eq_self_of_map_shift_eq_of_mem_G`): if `θ_i(μ) = θ_j(μ)`
  for `μ ∈ 𝒢(Q)` and `i ≠ j`, then `θ_a(μ) = μ` for every `a`. Georgii's own proof subsamples `Q`
  to `Q^p` and identifies the law of `(σ_{pi})_i` as a Gibbs measure for `γ^{Q^p}`; the proof here
  takes a shorter route through convexity alone (Cesàro-averaging the `θ_k(μ)`, `0 ≤ k < p`, using
  only `centerMass_mem_G` — a finite-average form of convexity of `𝒢(Q)` from `add_smul_mem_G` —
  the shift-covariance above, and Theorem (10.35) already generalised to `γ^Q`
  (`mem_extremePoints_G_transferSpecification_of_measurePreserving_shift`); see the module
  docstring immediately above `section CorollaryOneOneFourteenA` for the argument in full. No
  `Q^p` machinery, no subsampling map, and no second instantiation of Theorem (10.21) is needed.
* **Corollary (11.14)(b), (c)** (`eq_singleton_boundaryLawMeasure_const_or_infinite_
  extremePoints_G`, `eq_empty_G_or_infinite_extremePoints_G`): via Theorem (7.26)
  (`exists_mem_extremePoints_G_not_mem_invariantG_of_exists_not_mem_invariantG`, using
  `join_mem_invariantFields` to show an extreme point escaping `𝒢_Θ(Q)` exists whenever some
  Gibbs measure does), Corollary (11.14)(a) in the contrapositive
  (`injective_map_shift_of_not_mem_invariantG`), and Remark (7.2)
  (`infinite_extremePoints_G_of_exists_not_mem_invariantG`).
* **Theorem (11.15), general extreme point** (`G_eq_invariantG_of_forall_le_sum`): the same
  "escape" argument as (11.14)(b), (c) run in the contrapositive
  (`G_eq_invariantG_of_extremePoints_G_subset_invariantG`), fed by (11.9)(c)'s periodicity
  consequence and (11.14)(a).
* **Corollary (11.17)**, both halves (`eq_singleton_boundaryLawMeasure_const_G_of_forall_le_sum`,
  `eq_empty_G_of_forall_le_sum`): Theorem (11.15) combined with Theorem (11.13), packaged as the
  set equalities `invariantG_eq_singleton_boundaryLawMeasure_const` /
  `invariantG_eq_empty_of_not_exists_isPositiveRecurrent`.

## Continued elsewhere

**Corollary (11.19)** (`𝒢(Q) = ∅` for a translation invariant `Q` with `∑_x Q(0,x) < ∞`) and
**Comment (11.18)(2)** (the bounded ratio `C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` gives `|𝒢(γ^Q)| = 1`,
and excludes the uniqueness condition of Corollary (11.17) on an infinite `E`) are proved in
`GibbsMeasure/Model/BoundaryLawExamples.lean`, which is where Theorem (8.39)
(`GibbsMeasure/Specification/OneDimensionalUniqueness.lean`) may be imported.
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
/-- The transfer weight of the open interval `]i, k[` is the bond product over `[i, k[`. -/
lemma transferWeight_Ioo {i k : ℤ} (hik : i + 1 < k) (σ : ℤ → E) :
    transferWeight Q (Finset.Ioo i k) σ = pathProd Q i k σ :=
  Specification.chainDensity_Ioo_eq_prod_Ico hik σ

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

/-! ### Obstruction (i), fourth bullet: `rescaledTransferDensity Q` is homogeneous

`IsHomogeneousInt` quantifies over *every* finite `Λ : Finset ℤ`, not only intervals, so this needs
shift-covariance of `transferWeight`, of the constant `countProbDensity`-weight, and of the
counting-measure partition function `sigmaFiniteLambdaZ`, each for an arbitrary volume. The first
two are elementary `Finset` combinatorics on `bondsOf`. The third is not: `sigmaFiniteLambdaZ`
is built from `Specification.sigmaFiniteLambdaFun`, an s-finite reference kernel assembled from
`Kernel.sum`/`sfiniteSeq`, and *that* is shift-covariant for the same structural reason `isssd` is
(`Specification.isssdFun_map_toFun`, `GibbsMeasure/Specification/Transformation.lean`) —
`Specification.sigmaFiniteLambdaFun_apply_eq_map` identifies it with `Measure.map (juxt Λ η)
(Measure.pi fun _ ↦ ν)`, the same closed form `isssdFun_apply` gives for probability `ν`, and the
juxtaposition/reindexing lemmas of `MeasureTheory.GibbsMeasure.Transformation`
(`toFun_comp_juxt`, `measurePreserving_spin_piCongrLeft`) need only `[SigmaFinite ν]`, not
`[IsProbabilityMeasure ν]`. -/

section Homogeneous

variable (Q : E → E → ℝ≥0∞)

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `transferWeight Q` is shift-covariant for every finite volume, not merely intervals:
`ρ^Q_{Λ+a}(ω) = ρ^Q_Λ(θ_{-a} ω)`. -/
lemma transferWeight_image_add (Λ : Finset ℤ) (a : ℤ) (ω : ℤ → E) :
    transferWeight Q (Λ.image (· + a)) ω = transferWeight Q Λ (transl E a ω) := by
  rw [transferWeight_eq_prod_bondsOf, transferWeight_eq_prod_bondsOf, bondsOf_image_add,
    Finset.prod_image fun x _ y _ h ↦ by omega]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have h1 : transl E a ω k = ω (k + a) := transl_apply a ω k
  have h2 : transl E a ω (k + 1) = ω (k + a + 1) := by
    rw [transl_apply]; congr 1; ring
  rw [h1, h2]

/-- The constant `countProbDensity`-weight is shift-covariant for every finite volume. -/
lemma lambdaWeight_countProbDensity_image_add (Λ : Finset ℤ) (a : ℤ) (ω : ℤ → E) :
    Specification.lambdaWeight (S := ℤ) (E := E) (fun _ ↦ countProbDensity (E := E))
        (Λ.image (· + a)) ω
      = Specification.lambdaWeight (S := ℤ) (E := E) (fun _ ↦ countProbDensity (E := E)) Λ
          (transl E a ω) := by
  unfold Specification.lambdaWeight
  rw [Finset.prod_image fun x _ y _ h ↦ by omega]
  exact Finset.prod_congr rfl fun k _ ↦ by rw [transl_apply]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `(shift E (-a)).sites.symm y = y + a`: the site part of `θ_{-a}` inverted. -/
lemma shift_neg_sites_symm_apply (a y : ℤ) : (shift E (-a)).sites.symm y = y + a := by
  have h : (shift E (-a)).sites (y + a) = y := by
    rw [show (shift E (-a)).sites = Equiv.addRight (-a) from rfl, Equiv.coe_addRight]
    ring
  exact ((shift E (-a)).sites.symm_apply_eq).2 h.symm

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
lemma map_shift_neg_sites_symm_toEmbedding (Λ : Finset ℤ) (a : ℤ) :
    Λ.map (shift E (-a)).sites.symm.toEmbedding = Λ.image (· + a) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_image, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (shift_neg_sites_symm_apply a k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, shift_neg_sites_symm_apply a k⟩

omit [Nonempty E] in
/-- **Shift-covariance of the σ-finite counting reference kernel**, for every finite volume.
`sigmaFiniteLambdaZ` for counting measure is built from `Kernel.sum` over `sfiniteSeq`
(`Specification.sigmaFiniteLambdaFun`), which the closed form `sigmaFiniteLambdaFun_apply_eq_map`
identifies with `Measure.map (juxt Λ η) (Measure.pi fun _ ↦ ν)` — the same shape `isssdFun` has for
a probability measure, so the same reindexing argument
(`MeasureTheory.GibbsMeasure.Transformation.toFun_comp_juxt`,
`.measurePreserving_spin_piCongrLeft`) applies, `SigmaFinite ν` being all it needs. -/
lemma sigmaFiniteLambdaFun_count_map_transl_aux (a : ℤ) (Λ : Finset ℤ) (ζ : ℤ → E) :
    (Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count
        (Λ.map (shift E (-a)).sites.symm.toEmbedding) ((shift E (-a)).inv.toFun ζ)).map
        (shift E (-a)).toFun
      = Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count Λ ζ := by
  have hτ : ∀ i : ℤ, MeasurePreserving ((shift E (-a)).spin i) (Measure.count : Measure E)
      (Measure.count : Measure E) := fun i ↦ measurePreserving_shift_spin Measure.count (-a) i
  simp only [Specification.sigmaFiniteLambdaFun_apply_eq_map]
  rw [Measure.map_map (shift E (-a)).measurable_toFun Measurable.juxt,
    (shift E (-a)).toFun_comp_juxt,
    ← Measure.map_map Measurable.juxt
      ((shift E (-a)).measurePreserving_spin_piCongrLeft hτ Λ).measurable,
    ((shift E (-a)).measurePreserving_spin_piCongrLeft hτ Λ).map_eq]

omit [Nonempty E] in
/-- **Shift-covariance of `sigmaFiniteLambdaZ` for counting measure**, at every finite volume:
`Z_{Λ+a}(ω) = Z_Λ(θ_{-a} ω)` in the pushforward sense that makes `Georgii's `ρ^Q`, integrated
against it, shift-covariant too (`transferWeight_image_add`). -/
lemma sigmaFiniteLambdaFun_count_map_transl (a : ℤ) (Λ : Finset ℤ) (ω : ℤ → E) :
    (Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count (Λ.image (· + a))
        ω).map (transl E a)
      = Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count Λ (transl E a ω) := by
  have hΛ : Λ.map (shift E (-a)).sites.symm.toEmbedding = Λ.image (· + a) :=
    map_shift_neg_sites_symm_toEmbedding Λ a
  have hfun : (shift E (-a)).toFun = transl E a := by
    funext η i
    rw [shift_toFun_apply, transl_apply, sub_neg_eq_add]
  have hinv : (shift E (-a)).inv.toFun (transl E a ω) = ω := by
    funext i
    rw [shift_inv_toFun_apply, transl_apply]
    congr 1
    ring
  have key := sigmaFiniteLambdaFun_count_map_transl_aux a Λ (transl E a ω)
  rwa [hΛ, hfun, hinv] at key

omit [Nonempty E] in
/-- **Shift-covariance of the counting-measure partition function of `transferWeight Q`**, at
every finite volume: `Z^Q_{Λ+a}(ω) = Z^Q_Λ(θ_{-a} ω)`. -/
lemma sigmaFiniteLambdaZ_transferWeight_image_add (Λ : Finset ℤ) (a : ℤ) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
        (Λ.image (· + a)) ω
      = Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q) Λ
          (transl E a ω) := by
  unfold Specification.sigmaFiniteLambdaZ
  rw [lintegral_congr fun x ↦ transferWeight_image_add Q Λ a x,
    ← lintegral_map (measurable_transferWeight Q Λ) (measurable_transl a),
    sigmaFiniteLambdaFun_count_map_transl]

/-- **Obstruction (i), fourth bullet.** `rescaledTransferDensity Q` is homogeneous
(`Specification.IsHomogeneousInt`), for *every* finite volume `Λ`, not only intervals. -/
theorem isHomogeneousInt_rescaledTransferDensity :
    Specification.IsHomogeneousInt (rescaledTransferDensity Q) := by
  intro Λ a ω
  have heq : (fun i ↦ ω (i + a)) = transl E a ω := funext fun i ↦ (transl_apply a ω i).symm
  rw [heq, rescaledTransferDensity_apply, rescaledTransferDensity_apply,
    transferWeight_image_add, lambdaWeight_countProbDensity_image_add,
    sigmaFiniteLambdaZ_transferWeight_image_add]

end Homogeneous

/-! ### Obstruction (i), fifth bullet, and Georgii's Example (10.24)(2): irreducibility

Georgii's Definition (10.23) for `γ^Q`, in the general form
`isIrreducibleInt_rescaledTransferDensity_of_eventually`: if all powers `P^n` are finite and
`P^n(x, y) > 0` for all large `n` (for each pair `x, y`), then `rescaledTransferDensity P` is
irreducible, with `C_N ↑ E` a finite exhaustion built from a fixed enumeration of the countable
`E`, `n(N) ≥ 1` any step count with `P^{n(N)} > 0` on `C_N × C_N`, and Georgii's witness
`h_N(x) = (inf_{y, z ∈ C_N} P^n(y, x) P^n(x, z) / P^{2n}(y, z)) / countProbDensity(x)`, a finite
infimum of positive finite reals. The defining inequality of (10.23) is the explicit marginal
density `marginalDensity_rescaledTransferDensity_Ioo`, Georgii's second display in (10.24)(2),
computed from the partition functions (11.2) of the two blocks `]-n, 0[` and `]0, n[`.

Two instances: a transfer matrix (11.1) (`isIrreducibleInt_rescaledTransferDensity`, where
`Q > 0` lets `n(N) ≡ 1`), and **Georgii's Example (10.24)(2)** itself
(`isIrreducibleInt_rescaledTransferDensity_of_isAperiodic`): a stochastic `P` that is irreducible
and aperiodic, via `ProbabilityTheory.Kernel.eventually_pow_apply_singleton_pos`. -/

section Irreducible

open scoped Classical

/-- A fixed enumeration `ℕ → E` of the countable, nonempty state space. -/
noncomputable def enumE : ℕ → E := (exists_surjective_nat E).choose

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma surjective_enumE : Function.Surjective (enumE (E := E)) :=
  (exists_surjective_nat E).choose_spec

/-- **Georgii's finite exhaustion `C_N`** of Definition (10.23): the image of the first `N`
values of a fixed enumeration of `E`. -/
noncomputable def countExhaustion (N : ℕ) : Finset E := (Finset.range N).image (enumE (E := E))

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma countExhaustion_mono : Monotone (countExhaustion (E := E)) := by
  intro N N' hNN'
  apply Finset.image_subset_image
  intro k hk
  simp only [Finset.mem_range] at hk ⊢
  omega

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma iUnion_countExhaustion_eq_univ :
    ⋃ N, (countExhaustion (E := E) N : Set E) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨n, hn⟩ := surjective_enumE x
  refine Set.mem_iUnion.2 ⟨n + 1, ?_⟩
  rw [countExhaustion, Finset.coe_image]
  exact ⟨n, by simp, hn⟩

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma countExhaustion_nonempty {N : ℕ} (hN : 1 ≤ N) :
    (countExhaustion (E := E) N).Nonempty :=
  ⟨enumE 0, by rw [countExhaustion]; exact Finset.mem_image_of_mem _ (Finset.mem_range.2 (by
    omega))⟩

omit [Nonempty E] in
/-- Integrating the transfer weight of `]-n, n[` over the interior sites other than `0` with
respect to the counting kernel gives `P^n(ω_{-n}, ω_0) P^n(ω_0, ω_n)`. -/
lemma lintegral_lambdaCount_transferWeight_Ioo_erase (P : E → E → ℝ≥0∞) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℤ → E) :
    ∫⁻ ζ, transferWeight P (Finset.Ioo (-(n : ℤ)) n) ζ
        ∂(Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count
          ((Finset.Ioo (-(n : ℤ)) n).erase 0) ω)
      = (Kernel.ofMatrix P ^ n) (ω (-(n : ℤ))) {ω 0} * (Kernel.ofMatrix P ^ n) (ω 0) {ω n} := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    have hΛ : (Finset.Ioo (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).erase 0 = ∅ := by
      ext k
      simp only [Nat.cast_one, Finset.mem_erase, Finset.mem_Ioo, Finset.notMem_empty, iff_false]
      omega
    have hΛ' : Finset.Ioo (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = ({0} : Finset ℤ) := by
      ext k
      simp only [Nat.cast_one, Finset.mem_Ioo, Finset.mem_singleton]
      omega
    rw [hΛ, lintegral_lambdaCount_empty ω (measurable_transferWeight P _), hΛ',
      transferWeight_singleton]
    simp
  · set A := Finset.Icc (-(n : ℤ) + 1) (-1) with hA
    set B := Finset.Icc 1 ((n : ℤ) - 1) with hB
    have hAB : (Finset.Ioo (-(n : ℤ)) n).erase 0 = A ∪ B := by
      ext k
      simp only [hA, hB, Finset.mem_erase, Finset.mem_Ioo, Finset.mem_union, Finset.mem_Icc]
      omega
    have hbA : bondsOf A = Finset.Ico (-(n : ℤ)) 0 := by
      rw [hA, bondsOf_Icc (by omega)]
      congr 1; ring
    have hbB : bondsOf B = Finset.Ico 0 (n : ℤ) := by
      rw [hB, bondsOf_Icc (by omega)]
      congr 1; ring
    have hdisj : Disjoint (bondsOf A) (bondsOf B) := by
      rw [hbA, hbB]
      refine Finset.disjoint_left.2 fun k hk hk' ↦ ?_
      simp only [Finset.mem_Ico] at hk hk'
      omega
    have hW : transferWeight P (Finset.Ioo (-(n : ℤ)) n) = transferWeight P (A ∪ B) := by
      funext σ
      rw [transferWeight_eq_prod_bondsOf, transferWeight_eq_prod_bondsOf, bondsOf_union,
        bondsOf_Ioo (by omega), hbA, hbB]
      congr 1
      ext k
      simp only [Finset.mem_Ico, Finset.mem_union]
      omega
    rw [hAB, hW, ← Specification.sigmaFiniteLambdaZ,
      sigmaFiniteLambdaZ_transferWeight_union P hdisj, hA, hB,
      sigmaFiniteLambdaZ_transferWeight_Icc P (by omega),
      sigmaFiniteLambdaZ_transferWeight_Icc P (by omega)]
    have e1 : (-1 - (-(n : ℤ) + 1) + 2).toNat = n := by omega
    have e2 : ((n : ℤ) - 1 - 1 + 2).toNat = n := by omega
    have e3 : -(n : ℤ) + 1 - 1 = -(n : ℤ) := by ring
    have e4 : (-1 : ℤ) + 1 = 0 := by ring
    have e5 : (1 : ℤ) - 1 = 0 := by ring
    have e6 : (n : ℤ) - 1 + 1 = n := by ring
    rw [e1, e2, e3, e4, e5, e6]

/-- **Georgii (10.12) for `γ^Q`**, the marginal density of the site `0` in `]-n, n[`:
`ρ̃^0_{]-n,n[}(ω) = P^n(ω_{-n}, ω_0) P^n(ω_0, ω_n) / (r(ω_0) P^{2n}(ω_{-n}, ω_n))`, the second
display of Georgii's Example (10.24)(2), after the rescaling by `countProbDensity`. -/
lemma marginalDensity_rescaledTransferDensity_Ioo (P : E → E → ℝ≥0∞) {n : ℕ} (hn : 1 ≤ n)
    (ω : ℤ → E) :
    Specification.marginalDensity (S := ℤ) (E := E) (countProb (E := E))
        (rescaledTransferDensity P) (Finset.Ioo (-(n : ℤ)) n) 0 ω
      = (Kernel.ofMatrix P ^ n) (ω (-(n : ℤ))) {ω 0} * (Kernel.ofMatrix P ^ n) (ω 0) {ω n}
          / countProbDensity (ω 0) / (Kernel.ofMatrix P ^ (2 * n)) (ω (-(n : ℤ))) {ω n} := by
  set Λ := Finset.Ioo (-(n : ℤ)) n with hΛ
  have h0Λ : (0 : ℤ) ∈ Λ := by
    rw [hΛ, Finset.mem_Ioo]
    omega
  have hik : -(n : ℤ) + 1 < n := by omega
  set r := countProbDensity (E := E) with hr
  set LW := Specification.lambdaWeight (S := ℤ) (E := E) (fun _ ↦ r) with hLW
  have hZ : ∀ σ : ℤ → E, (∀ j ∉ Λ.erase 0, σ j = ω j) →
      Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight P) Λ σ
        = (Kernel.ofMatrix P ^ (2 * n)) (ω (-(n : ℤ))) {ω n} := by
    intro σ hσ
    rw [hΛ, sigmaFiniteLambdaZ_transferWeight_Ioo P hik, hσ _ (by simp [hΛ]),
      hσ _ (by simp [hΛ]), show ((n : ℤ) - -(n : ℤ)).toNat = 2 * n by omega]
  have hLWΛ : ∀ σ : ℤ → E, (∀ j ∉ Λ.erase 0, σ j = ω j) →
      LW Λ σ = r (ω 0) * LW (Λ.erase 0) σ := by
    intro σ hσ
    rw [hLW, Specification.lambdaWeight, Specification.lambdaWeight,
      ← Finset.mul_prod_erase Λ _ h0Λ, hσ 0 (by simp)]
  have hmeas : Measurable fun σ : ℤ → E ↦ transferWeight P Λ σ / LW (Λ.erase 0) σ :=
    (measurable_transferWeight P Λ).div (Specification.measurable_lambdaWeight (S := ℤ) (E := E)
      (fun _ ↦ measurable_countProbDensity) _)
  rw [Specification.marginalDensity, lintegral_isssd_congr_of_eqOn ω
    (measurable_rescaledTransferDensity P Λ) ((hmeas.div measurable_const).div measurable_const)
    (G := fun σ ↦ transferWeight P Λ σ / LW (Λ.erase 0) σ / r (ω 0)
      / (Kernel.ofMatrix P ^ (2 * n)) (ω (-(n : ℤ))) {ω n}) (fun σ hσ ↦ ?_)]
  · have hmeas' : Measurable fun σ : ℤ → E ↦ transferWeight P Λ σ * (LW (Λ.erase 0) σ)⁻¹ :=
      (measurable_transferWeight P Λ).mul (Specification.measurable_lambdaWeight (S := ℤ) (E := E)
        (fun _ ↦ measurable_countProbDensity) _).inv
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const (f := fun σ ↦ transferWeight P Λ σ * (LW (Λ.erase 0) σ)⁻¹
        * (r (ω 0))⁻¹) _ (hmeas'.mul measurable_const),
      lintegral_mul_const (f := fun σ ↦ transferWeight P Λ σ * (LW (Λ.erase 0) σ)⁻¹) _ hmeas']
    congr 2
    have hk : Specification.isssd (S := ℤ) (E := E) (countProb (E := E)) (Λ.erase 0) ω
        = Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) (countProb (E := E))
          (Λ.erase 0) ω :=
      (congr_arg (fun κ : Kernel[cylinderEvents ((Λ.erase 0 : Finset ℤ) : Set ℤ)ᶜ] (ℤ → E) (ℤ → E)
        ↦ κ ω) (Specification.sigmaFiniteLambdaFun_eq_isssdFun (Λ.erase 0))).symm
    simp_rw [← div_eq_mul_inv]
    rw [hk, hLW, hr]
    have hdiv := Specification.lintegral_sigmaFiniteLambdaFun_withDensity_div (S := ℤ) (E := E)
      Measure.count measurable_countProbDensity countProbDensity_ne_zero countProbDensity_ne_top
      (Λ.erase 0) ω (measurable_transferWeight P Λ)
    refine hdiv.trans ?_
    rw [hΛ, lintegral_lambdaCount_transferWeight_Ioo_erase P hn ω]
  · rw [rescaledTransferDensity_apply, hZ σ hσ, ← hLW, hLWΛ σ hσ]
    congr 1
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv
      (Or.inr (Specification.lambdaWeight_ne_top (S := ℤ) (E := E) (fun _ ↦ countProbDensity_ne_top)
        _ _))
      (Or.inr (Specification.lambdaWeight_ne_zero (S := ℤ) (E := E)
        (fun _ ↦ countProbDensity_ne_zero) _ _))]
    ring


/-- **Georgii's witness `h_N`** of Definition (10.23) for `γ^Q`, with `n` steps:
`h_N(x) = (inf_{y, z ∈ C_N} P^n(y, x) P^n(x, z) / P^{2n}(y, z)) / countProbDensity(x)`, a finite
infimum over the finite exhaustion `countExhaustion N` (`⊤` if `N = 0`). Georgii's indicator
`1_{C_N}(x)` is not needed: the infimum is already dominated by the term of any pair
`y, z ∈ C_N`, whatever `x` is. -/
noncomputable def irreducibleWitness (P : E → E → ℝ≥0∞) (n N : ℕ) (x : E) : ℝ≥0∞ :=
  ((countExhaustion (E := E) N).inf fun y ↦ (countExhaustion (E := E) N).inf fun z ↦
      (Kernel.ofMatrix P ^ n) y {x} * (Kernel.ofMatrix P ^ n) x {z}
        / (Kernel.ofMatrix P ^ (2 * n)) y {z})
    / countProbDensity x

lemma measurable_irreducibleWitness (P : E → E → ℝ≥0∞) (n N : ℕ) :
    Measurable (irreducibleWitness P n N) :=
  measurable_of_countable _

/-- `h_N(x) > 0` for `x ∈ C_N` as soon as `P^n > 0` on `C_N × C_N` and `P^{2n} < ∞`. -/
lemma irreducibleWitness_pos (P : E → E → ℝ≥0∞) {n N : ℕ} (hN : 1 ≤ N)
    (hpos : ∀ y ∈ countExhaustion (E := E) N, ∀ z ∈ countExhaustion (E := E) N,
      0 < (Kernel.ofMatrix P ^ n) y {z})
    (hfin : ∀ y z : E, (Kernel.ofMatrix P ^ (2 * n)) y {z} ≠ ⊤) {x : E}
    (hx : x ∈ countExhaustion (E := E) N) : 0 < irreducibleWitness P n N x := by
  have hne := countExhaustion_nonempty (E := E) hN
  have hpos' : 0 < (countExhaustion (E := E) N).inf fun y ↦ (countExhaustion (E := E) N).inf
      fun z ↦ (Kernel.ofMatrix P ^ n) y {x} * (Kernel.ofMatrix P ^ n) x {z}
        / (Kernel.ofMatrix P ^ (2 * n)) y {z} := by
    rw [← Finset.inf'_eq_inf hne]
    refine (Finset.lt_inf'_iff hne).2 fun y hy ↦ ?_
    rw [← Finset.inf'_eq_inf hne]
    refine (Finset.lt_inf'_iff hne).2 fun z hz ↦ ?_
    exact ENNReal.div_pos (mul_ne_zero (hpos y hy x hx).ne' (hpos x hx z hz).ne') (hfin y z)
  exact ENNReal.div_pos hpos'.ne' (countProbDensity_ne_top x)

/-- **Georgii, Definition (10.23) for `γ^Q`, the general form of Example (10.24)(2).** If all
powers of `P` are finite and, for every pair of states, `P^n(x, y) > 0` for all large `n`, then
`rescaledTransferDensity P` is irreducible: `C_N` is the finite exhaustion `countExhaustion N`,
`n(N)` is any `n ≥ 1` with `P^n > 0` on `C_N × C_N` (hence also `P^{2n} > 0` there), and `h_N`
is `irreducibleWitness P (n N) N`. -/
theorem isIrreducibleInt_rescaledTransferDensity_of_eventually (P : E → E → ℝ≥0∞)
    (hfin : ∀ (n : ℕ) (x y : E), (Kernel.ofMatrix P ^ n) x {y} ≠ ⊤)
    (hev : ∀ x y : E, ∀ᶠ n in Filter.atTop, 0 < (Kernel.ofMatrix P ^ n) x {y}) :
    Specification.IsIrreducibleInt (countProb (E := E)) (rescaledTransferDensity P) := by
  have hN : ∀ N : ℕ, ∃ n : ℕ, 1 ≤ n ∧ ∀ y ∈ countExhaustion (E := E) N,
      ∀ z ∈ countExhaustion (E := E) N, 0 < (Kernel.ofMatrix P ^ n) y {z} := by
    intro N
    have h : ∀ᶠ n in Filter.atTop, ∀ y ∈ countExhaustion (E := E) N,
        ∀ z ∈ countExhaustion (E := E) N, 0 < (Kernel.ofMatrix P ^ n) y {z} := by
      rw [Filter.eventually_all_finset]
      intro y _
      rw [Filter.eventually_all_finset]
      intro z _
      exact hev y z
    exact ((Filter.eventually_ge_atTop 1).and h).exists
  choose n hn1 hnpos using hN
  refine ⟨fun N ↦ (countExhaustion (E := E) N : Set E), n, fun N ↦ irreducibleWitness P (n N) N,
    fun N ↦ Set.Countable.measurableSet (countExhaustion (E := E) N).countable_toSet,
    fun _ _ hNN' ↦ Finset.coe_subset.2 (countExhaustion_mono hNN'),
    iUnion_countExhaustion_eq_univ, fun N ↦ measurable_irreducibleWitness P (n N) N, hn1, ?_, ?_⟩
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hx : enumE (E := E) 0 ∈ countExhaustion (E := E) N :=
      Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))
    refine lt_of_lt_of_le ?_
      (Kernel.mul_apply_singleton_le_lintegral (countProb (E := E)) _ (enumE 0))
    refine ENNReal.mul_pos
      (irreducibleWitness_pos P hN (hnpos N) (fun y z ↦ hfin _ y z) hx).ne' ?_
    rw [countProb_def, Measure.count_withDensity_apply_singleton]
    exact countProbDensity_ne_zero _
  · intro N ω h1 h2
    rw [marginalDensity_rescaledTransferDensity_Ioo P (hn1 N) ω]
    have hstep : (countExhaustion (E := E) N).inf (fun y ↦ (countExhaustion (E := E) N).inf
          fun z ↦ (Kernel.ofMatrix P ^ n N) y {ω 0} * (Kernel.ofMatrix P ^ n N) (ω 0) {z}
            / (Kernel.ofMatrix P ^ (2 * n N)) y {z})
        ≤ (Kernel.ofMatrix P ^ n N) (ω (-(n N : ℤ))) {ω 0}
            * (Kernel.ofMatrix P ^ n N) (ω 0) {ω (n N)}
            / (Kernel.ofMatrix P ^ (2 * n N)) (ω (-(n N : ℤ))) {ω (n N)} :=
      (Finset.inf_le h1).trans (Finset.inf_le h2)
    calc irreducibleWitness P (n N) N (ω 0)
        = (countExhaustion (E := E) N).inf (fun y ↦ (countExhaustion (E := E) N).inf
              fun z ↦ (Kernel.ofMatrix P ^ n N) y {ω 0} * (Kernel.ofMatrix P ^ n N) (ω 0) {z}
                / (Kernel.ofMatrix P ^ (2 * n N)) y {z})
            / countProbDensity (ω 0) := rfl
      _ ≤ ((Kernel.ofMatrix P ^ n N) (ω (-(n N : ℤ))) {ω 0}
            * (Kernel.ofMatrix P ^ n N) (ω 0) {ω (n N)}
            / (Kernel.ofMatrix P ^ (2 * n N)) (ω (-(n N : ℤ))) {ω (n N)})
            / countProbDensity (ω 0) := ENNReal.div_le_div hstep le_rfl
      _ = (Kernel.ofMatrix P ^ n N) (ω (-(n N : ℤ))) {ω 0}
            * (Kernel.ofMatrix P ^ n N) (ω 0) {ω (n N)} / countProbDensity (ω 0)
            / (Kernel.ofMatrix P ^ (2 * n N)) (ω (-(n N : ℤ))) {ω (n N)} := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          ring

include hQ in
/-- **Georgii Definition (10.23) for a transfer matrix (11.1).** `rescaledTransferDensity Q` is
irreducible for the probability measure `countProb`: `Q > 0` everywhere, so every power is
positive and Georgii's `n(N)` may be taken to be `1`. -/
theorem isIrreducibleInt_rescaledTransferDensity :
    Specification.IsIrreducibleInt (countProb (E := E)) (rescaledTransferDensity Q) :=
  isIrreducibleInt_rescaledTransferDensity_of_eventually Q
    (fun n x y ↦ by
      cases n with
      | zero =>
        rw [Kernel.pow_zero_apply_singleton]
        exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (Set.indicator_le_self' (fun _ _ ↦ zero_le_one) x)
      | succ n => exact hQ.pow_ne_top n x y)
    (fun x y ↦ (Filter.eventually_ge_atTop 1).mono fun n hn ↦ by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      exact hQ.pow_pos m x y)

/-- **Georgii, Example (10.24)(2).** Let `E` be countable, `λ` counting measure, `P` a
stochastic matrix on `E` and `ρ` the Markovian `λ`-modification of Example (10.3) built from
`p_j = P`: `ρ_{]i,k[}(ω) = ∏_{j=i+1}^k P(ω_{j-1}, ω_j) / P^{k-i}(ω_i, ω_k)`. If `P` is
irreducible and aperiodic, then `ρ` is irreducible in the sense of Definition (10.23).

Here `ρ` is `rescaledTransferDensity P`: Georgii's `ρ` after his reduction (before (10.13)) to
the probability a priori measure `countProb = countProbDensity · count`, which multiplies the
densities by `∏ countProbDensity(ω_j)⁻¹` (Remark (1.28)(3)); the `n(N)`-step marginal density
is `marginalDensity_rescaledTransferDensity_Ioo`, Georgii's second display. Georgii's
"well-known" input — an aperiodic irreducible `P` has `P^n(x, y) > 0` for all `n ≥ n(x, y)`,
cited from Breiman — is `ProbabilityTheory.Kernel.eventually_pow_apply_singleton_pos`. Where
`P^{k-i}(ω_i, ω_k) = 0` Georgii leaves `ρ` undefined; here the `ℝ≥0∞`-division makes it `0`, and
the irreducibility bound is unaffected since `n(N)` is chosen so that `P^{n(N)}` and
`P^{2n(N)}` are positive on `C_N`. -/
theorem isIrreducibleInt_rescaledTransferDensity_of_isAperiodic (P : E → E → ℝ≥0∞)
    (hP : ∀ x, ∑' y, P x y = 1)
    [Kernel.IsIrreducible Measure.count (Kernel.ofMatrix P)]
    (haper : (Kernel.ofMatrix P).IsAperiodic) :
    Specification.IsIrreducibleInt (countProb (E := E)) (rescaledTransferDensity P) := by
  have := Kernel.isMarkovKernel_ofMatrix P hP
  exact isIrreducibleInt_rescaledTransferDensity_of_eventually P
    (fun n x y ↦ (prob_le_one.trans_lt ENNReal.one_lt_top).ne)
    (fun x y ↦ Kernel.eventually_pow_apply_singleton_pos haper x y)

end Irreducible

/-! ### Georgii Theorem (10.35) for `γ^Q`: at most one shift-invariant Gibbs measure

`E` is `StandardBorelSpace` automatically: `[Countable E] [MeasurableSingletonClass E]` gives
`DiscreteMeasurableSpace E` (`MeasurableSingletonClass.toDiscreteMeasurableSpace`), and
`DiscreteMeasurableSpace` on a countable type gives `StandardBorelSpace`
(`standardBorelSpace_of_discreteMeasurableSpace`); no extra hypothesis is needed. -/

section TheoremOneOThreeFive

/-- **Georgii Theorem (10.35), `𝒢_Θ(γ^Q) ⊆ ex 𝒢(γ^Q)`, instantiated at `γ^Q`.** Every
shift-invariant Gibbs measure for `γ^Q = transferSpecification Q hQ` is extreme in `𝒢(γ^Q)`. -/
theorem mem_extremePoints_G_transferSpecification_of_measurePreserving_shift
    {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : (transferSpecification Q hQ).IsGibbsMeasure μ)
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    μ ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ :=
  mem_extremePoints_G_of_measurePreserving_shift (transferSpecification_eq_isssd_withDensity Q hQ)
    (measurable_rescaledTransferDensity Q) (isMarkovianInt_rescaledTransferDensity Q)
    (isHomogeneousInt_rescaledTransferDensity Q) (isIrreducibleInt_rescaledTransferDensity Q hQ)
    hμ hshift

/-- **Georgii Theorem (10.25), instantiated at `γ^Q`.** Every shift-invariant Gibbs measure for
`γ^Q` is a Markov chain for a *single* transition kernel `P(x, ·) = p(x, ·) · countProb`. -/
theorem exists_isMarkovChain_transferSpecification_of_measurePreserving_shift
    {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : (transferSpecification Q hQ).IsGibbsMeasure μ)
    (hshift : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ μ) :
    ∃ (p : E → E → ℝ≥0∞) (P : Kernel E E), Measurable (Function.uncurry p) ∧
      (∀ x, P x = (countProb (E := E)).withDensity (p x)) ∧ IsMarkovKernel P ∧
      IsMarkovChain (fun _ ↦ P) μ :=
  exists_isMarkovChain_of_measurePreserving_shift (transferSpecification_eq_isssd_withDensity Q hQ)
    (measurable_rescaledTransferDensity Q) (isMarkovianInt_rescaledTransferDensity Q)
    (isHomogeneousInt_rescaledTransferDensity Q) (isIrreducibleInt_rescaledTransferDensity Q hQ)
    hμ hshift

/-- **Georgii Theorem (10.35), instantiated at `γ^Q`.** `𝒢_Θ(γ^Q)` is a subsingleton: any two
shift-invariant Gibbs measures for `γ^Q = transferSpecification Q hQ` coincide. -/
theorem eq_of_isGibbsMeasure_transferSpecification_of_measurePreserving_shift
    {μ₁ μ₂ : Measure (ℤ → E)} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁ : (transferSpecification Q hQ).IsGibbsMeasure μ₁)
    (hμ₂ : (transferSpecification Q hQ).IsGibbsMeasure μ₂)
    (hshift₁ : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ₁ μ₁)
    (hshift₂ : ∀ a : ℤ, MeasurePreserving (shift E a).toFun μ₂ μ₂) :
    μ₁ = μ₂ :=
  eq_of_isGibbsMeasure_of_measurePreserving_shift (transferSpecification_eq_isssd_withDensity Q hQ)
    (measurable_rescaledTransferDensity Q) (isMarkovianInt_rescaledTransferDensity Q)
    (isHomogeneousInt_rescaledTransferDensity Q) (isIrreducibleInt_rescaledTransferDensity Q hQ)
    hμ₁ hμ₂ hshift₁ hshift₂

end TheoremOneOThreeFive

/-! ### Georgii Theorem (11.13), the "only if" half

If `𝒢_Θ(γ^Q) ≠ ∅`, take `μ` in it. Theorem (10.25) (just instantiated) supplies a *single* Markov
transition kernel `P` for `μ`; Theorem (11.9)(b) (`IsMarkovChain.
exists_isBoundaryLaw_eq_boundaryLawMeasure`, already in this file) represents `μ` as the measure
of a boundary law `{ℓ_i, r_i}` for `Q` with `P(x, y) r_{i-1}(x) = Q(x, y) r_i(y)` for *every* `i`.
Because `μ` is shift-invariant, `θ_1(μ) = μ`, so the shifted boundary law `{ℓ_{i-1}, r_{i-1}}` also
represents `μ`; the proportionality lemma (`IsBoundaryLaw.exists_const_of_boundaryLawMeasure_eq`,
already in this file) gives a single constant `c` with `r_{i-1}(x) = c · r_i(x)` for every `i` —
in particular at `i = 0` — which turns the (11.11) relation at `i = 0` directly into Georgii's
(11.5) equivalence `P(x, y) = Q(x, y) r(y) / (q r(x))` with `q := c`, `r := r_0`. No cocycle/
rigidity argument on the constants `c_j` (`j ↦ c_j` a homomorphism `ℤ → (0, ∞)`) is needed: a
single application of the proportionality lemma, at the single shift `j = 1`, already produces the
(11.5) data.

`P` is positive recurrent: `IsMarkovChain.kernel_singleton_pos` gives `P(x, y) > 0` for every pair
(so `Kernel.ofMatrix P` is irreducible for counting measure, `isIrreducible_count_ofMatrix_of_
forall_pos`), and the shift-invariant marginal `α(x) := μ(σ_0 = x)` is an invariant probability
vector for `P` (`IsMarkovChain.tsum_measure_preimage_mul` plus the shift-invariance of the
marginals), so `isRecurrent_of_invariant` applies. -/

section OnlyIf

/-- **Georgii Theorem (11.13), the "only if" half.** If `𝒢_Θ(γ^Q)` is non-empty, `Q` is
equivalent, in the sense of (11.5), to a positive recurrent stochastic matrix `P`. -/
theorem exists_transferMatrix_equiv_and_isPositiveRecurrent_of_invariantG_nonempty
    (hne : (invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)).Nonempty) :
    ∃ (P : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧ (∀ x, 0 < r x) ∧
      (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = Q x y * r y / (q * r x)) ∧ (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P) := by
  obtain ⟨μ, ⟨hprob, hGibbs⟩, hinv⟩ := hne
  have := hprob
  obtain ⟨-, hshift⟩ := mem_invariantFields_shiftGroup.1 hinv
  obtain ⟨p, Pk, hpmeas, hPapply, hPmarkov, hchain⟩ :=
    exists_isMarkovChain_transferSpecification_of_measurePreserving_shift Q hQ hGibbs hshift
  have hmarkovP : ∀ k : ℤ, IsMarkovKernel ((fun _ : ℤ ↦ Pk) k) := fun _ ↦ hPmarkov
  -- **(11.9)(b)**: `μ` is the measure of a boundary law for `Q`, with the (11.11) relation.
  obtain ⟨ℓ, r, hbl, hμeq, hrel⟩ :=
    hchain.exists_isBoundaryLaw_eq_boundaryLawMeasure (Q := Q) hQ hGibbs
  -- shift-invariance of `μ` transports to the boundary law: `θ_1(μ) = μ` gives the same measure
  -- for the shift `{ℓ_{i-1}, r_{i-1}}`.
  have hshift1 : (boundaryLawMeasure hbl).map (shift E (1 : ℤ)).toFun = boundaryLawMeasure hbl := by
    have h := hshift 1
    rw [hμeq] at h
    exact h.2
  have heqshift : boundaryLawMeasure hbl = boundaryLawMeasure (hbl.shift 1) := by
    rw [← hbl.boundaryLawMeasure_map_shift 1, hshift1]
  -- the proportionality lemma, at the single shift `j = 1`.
  obtain ⟨c, hc0, hct, hℓc, hrc⟩ :=
    hbl.exists_const_of_boundaryLawMeasure_eq hQ (hbl.shift 1) heqshift
  -- `r_{-1}(x) = c · r_0(x)`, from the proportionality at `i = 0`.
  have hr1 : ∀ x, r (-1) x = c * r 0 x := fun x ↦ hrc 0 x
  -- Georgii's (11.5) data: `q := c`, the transfer matrix `P x y := Pk x {y}`.
  set P : E → E → ℝ≥0∞ := fun x y ↦ Pk x {y} with hP_def
  have hPQ : ∀ x y, P x y = Q x y * r 0 y / (c * r 0 x) := by
    intro x y
    have h11 : Pk x {y} * r (-1) x = Q x y * r 0 y := by
      have h := hrel 0 x y
      rwa [show (0 : ℤ) - 1 = -1 by ring] at h
    rw [hr1 x] at h11
    change Pk x {y} = Q x y * r 0 y / (c * r 0 x)
    refine (ENNReal.eq_div_iff (mul_ne_zero hc0.ne' (hbl.right_pos 0 x).ne')
      (ENNReal.mul_ne_top hct (hbl.right_ne_top 0 x))).2 ?_
    rw [mul_comm]
    exact h11
  have hPpos : ∀ x y, 0 < P x y := fun x y ↦ hchain.kernel_singleton_pos hQ hGibbs 0 x y
  have hofP : Kernel.ofMatrix P = Pk := Kernel.ofMatrix_entries Pk
  have hmarkovOfP : IsMarkovKernel (Kernel.ofMatrix P) := by rw [hofP]; exact hPmarkov
  have hirrP := Kernel.isIrreducible_count_ofMatrix_of_forall_pos hPpos
  -- the invariant marginal `α(x) = μ(σ_0 = x)`
  have hαprob : IsProbabilityMeasure (μ.map (fun ω : ℤ → E ↦ ω 0)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable
  have hmarg := map_eval_eq_of_measurePreserving_shift hshift
  have hinvP : (Kernel.ofMatrix P).Invariant (μ.map (fun ω : ℤ → E ↦ ω 0)) := by
    change (μ.map (fun ω : ℤ → E ↦ ω 0)).bind (Kernel.ofMatrix P) = μ.map (fun ω : ℤ → E ↦ ω 0)
    refine Measure.ext_of_singleton fun y ↦ ?_
    rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.ofMatrix P).aemeasurable,
      MeasureTheory.lintegral_countable']
    have hstep := hchain.tsum_measure_preimage_mul 0 y
    simp only [zero_add] at hstep
    have hx0 : ∀ x, μ ((fun τ : ℤ → E ↦ τ (0 : ℤ)) ⁻¹' {x})
        = (μ.map (fun ω : ℤ → E ↦ ω 0)) {x} := fun x ↦
      (Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton x)).symm
    have hy1 : μ ((fun τ : ℤ → E ↦ τ (1 : ℤ)) ⁻¹' {y})
        = (μ.map (fun ω : ℤ → E ↦ ω 0)) {y} := by
      rw [← Measure.map_apply (measurable_pi_apply 1) (measurableSet_singleton y), hmarg 1]
    simp only [hx0] at hstep
    rw [hy1] at hstep
    refine (tsum_congr fun x ↦ ?_).trans hstep
    rw [Kernel.ofMatrix_apply_singleton, hP_def, mul_comm]
  have hPstoch : ∀ x, ∑' y, P x y = 1 := fun x ↦ by
    have h1 : ∑' y, P x y = ∑' y, Pk x {y} := rfl
    rw [h1, ← measure_univ_eq_tsum_singleton (Pk x)]
    exact measure_univ
  refine ⟨P, c, r 0, hc0, hct, fun x ↦ hbl.right_pos 0 x, fun x ↦ hbl.right_ne_top 0 x, hPQ,
    hPstoch, Kernel.isRecurrent_of_invariant hinvP, μ.map (fun ω : ℤ → E ↦ ω 0),
    Measure.isProbabilityMeasure_map (measurable_pi_apply 0).aemeasurable, hinvP⟩

end OnlyIf

/-! ### Georgii Theorem (11.9)(c): a representing boundary law for every extreme point

Theorem (10.21) (`exists_isMarkovChain_of_mem_extremePoints`, already in `MarkovIntChains.lean`)
applies to `γ^Q = transferSpecification Q hQ` through `transferSpecification_eq_isssd_withDensity`,
`measurable_rescaledTransferDensity`, and `isMarkovianInt_rescaledTransferDensity` (irreducibility
and homogeneity are not needed for this half of (10.21), only the Markovian `λ`-modification
structure): every extreme `μ ∈ ex 𝒢(Q)` is a Markov chain. Theorem (11.9)(b)
(`IsMarkovChain.exists_isBoundaryLaw_eq_boundaryLawMeasure`, already in this file) then represents
it by a boundary law for `Q`. Georgii's "moreover" clause of (11.9)(c) — the explicit limit
formula `ℓ_i(x)/ℓ_0(a) = lim_n Q^{n+i}(x_n,x)/Q^n(x_n,a)` along a sequence `x_n → -∞` (and
similarly for `r_i`) — is not proved here: it is a quantitative refinement of the representation
below (via the backward martingale theorem and the left-tail triviality already used inside
Theorem (10.21)'s own proof), not needed for Theorem (11.15). -/

section ExtremePointsBoundaryLaw

/-- **Georgii Theorem (11.9)(c), representation clause.** Every `μ ∈ ex 𝒢(Q)` is the measure
(11.10) of a boundary law for `Q`. -/
theorem exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints
    {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞) :
    ∃ (ℓ r : ℤ → E → ℝ≥0∞) (hbl : IsBoundaryLaw Q ℓ r), μ = boundaryLawMeasure hbl := by
  obtain ⟨_p, P, -, -, hPmarkov, -, hchain⟩ :=
    exists_isMarkovChain_of_mem_extremePoints (transferSpecification_eq_isssd_withDensity Q hQ)
      (measurable_rescaledTransferDensity Q) (isMarkovianInt_rescaledTransferDensity Q) hμ
  have : ∀ k, IsMarkovKernel (P k) := hPmarkov
  obtain ⟨ℓ, r, hbl, hμeq, -⟩ :=
    hchain.exists_isBoundaryLaw_eq_boundaryLawMeasure (Q := Q) hQ hμ.1.2
  exact ⟨ℓ, r, hbl, hμeq⟩

/-- **A first consequence of Theorem (11.9)(c): periodicity of every extreme point.** If
`inf_x ∑_{n=1}^N Q^n(x,x) > 0` then every `μ ∈ ex 𝒢(Q)` satisfies `θ_{N!}(μ) = μ` — Georgii's own
reduction in the proof of Theorem (11.15), applied through the boundary law representing `μ`
supplied by (11.9)(c) above and the periodicity argument
`IsBoundaryLaw.boundaryLawMeasure_map_shift_factorial_eq_self`. -/
theorem map_shift_factorial_eq_self_of_mem_extremePoints
    {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞)
    {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    μ.map (GibbsMeasure.shift E (N.factorial : ℤ)).toFun = μ := by
  obtain ⟨ℓ, r, hbl, rfl⟩ :=
    exists_isBoundaryLaw_boundaryLawMeasure_eq_of_mem_extremePoints Q hQ hμ
  exact hbl.boundaryLawMeasure_map_shift_factorial_eq_self hQ hμ hN hε h

end ExtremePointsBoundaryLaw

/-! ### Shift-covariance of `γ^Q`: Georgii's implicit homogeneity, and Remarks (5.10)/(7.2) for it

Georgii calls `γ^Q` "homogeneous" from the outset (the matrix `Q` does not depend on position);
in this library that is the kernel-level statement `Specification.IsInvariant (shift E a)
(transferSpecification Q hQ)` for every `a : ℤ`, assembled here from the shift-covariance of
`transferWeight` (`transferWeight_image_add`), of the counting-measure partition function
(`sigmaFiniteLambdaZ_transferWeight_image_add`), and of the σ-finite reference kernel itself
(`sigmaFiniteLambdaFun_count_map_transl`) — all three already proved above for
`isHomogeneousInt_rescaledTransferDensity`, but there only combined into the covariance of the
*density* `rescaledTransferDensity Q`, not of the full specification `γ^Q` as a kernel. This is
the input Corollary (11.14)(a) needs for Remark (5.10) (`θ_a(μ) ∈ 𝒢(Q)` whenever `μ ∈ 𝒢(Q)`) and
Remark (7.2) (`θ_a` preserves extreme points), neither of which is otherwise available for
`transferSpecification`. -/

section ShiftCovariance

/-- **Shift-covariance of `γ^Q` as a specification**, in terms of `transl E a = θ_{-a}`:
`γ^Q_Λ(θ_{-a} ω) = (γ^Q_{Λ+a} ω).map θ_{-a}`. -/
theorem transferSpecification_map_transl (Λ : Finset ℤ) (a : ℤ) (ω : ℤ → E) :
    transferSpecification Q hQ Λ (transl E a ω)
      = (transferSpecification Q hQ (Λ.image (· + a)) ω).map (transl E a) := by
  refine Measure.ext fun A hA ↦ ?_
  have hA' : MeasurableSet ((transl E a) ⁻¹' A) := (measurable_transl a) hA
  rw [Measure.map_apply (measurable_transl a) hA,
    transferSpecification_apply Q hQ Λ (transl E a ω) hA,
    transferSpecification_apply Q hQ (Λ.image (· + a)) ω hA',
    ← sigmaFiniteLambdaFun_count_map_transl a Λ ω,
    setLIntegral_map hA (measurable_transferWeight Q Λ) (measurable_transl a),
    sigmaFiniteLambdaZ_transferWeight_image_add Q Λ a ω,
    setLIntegral_congr_fun hA' (fun ζ (_ : ζ ∈ (transl E a) ⁻¹' A) ↦
      (transferWeight_image_add Q Λ a ζ).symm)]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `transl E (-a) = θ_a` in coordinates. -/
lemma transl_neg_eq_shift_toFun (a : ℤ) : transl E (-a) = (shift E a).toFun := by
  funext ω i
  rw [transl_apply, shift_toFun_apply, sub_eq_add_neg]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
lemma finset_map_shift_sites_toEmbedding (Λ : Finset ℤ) (a : ℤ) :
    Λ.map (shift E a).sites.toEmbedding = Λ.image (· + a) := by
  rw [Finset.map_eq_image]
  rfl

include hQ in
/-- **Georgii's homogeneity of `γ^Q`, as `Specification.IsInvariant`.** `θ_a` is a symmetry of
`γ^Q` for every `a : ℤ`. -/
theorem isInvariant_shift_transferSpecification (a : ℤ) :
    Specification.IsInvariant (shift E a) (transferSpecification Q hQ) := by
  rw [Specification.isInvariant_iff]
  intro Λ ω
  rw [finset_map_shift_sites_toEmbedding, ← transl_neg_eq_shift_toFun a]
  have key := transferSpecification_map_transl Q hQ (Λ.image (· + a)) (-a) ω
  have himg : (Λ.image (· + a)).image (· + (-a)) = Λ := by
    rw [Finset.image_image]
    simp
  rw [himg] at key
  exact key.symm

include hQ in
/-- **Georgii, Remark (5.10) for `γ^Q`.** If `μ ∈ 𝒢(Q)` then `θ_a(μ) ∈ 𝒢(Q)` for every `a : ℤ`. -/
theorem mem_G_map_shift_of_mem_G (a : ℤ) {μ : Measure (ℤ → E)}
    (hμ : μ ∈ G (transferSpecification Q hQ)) :
    μ.map (shift E a).toFun ∈ G (transferSpecification Q hQ) :=
  map_mem_G (isInvariant_shift_transferSpecification Q hQ a) hμ

include hQ in
/-- **Georgii, Remark (7.2) for `γ^Q`.** If `μ ∈ ex 𝒢(Q)` then `θ_a(μ) ∈ ex 𝒢(Q)` for every
`a : ℤ`. -/
theorem mem_extremePoints_G_map_shift_of_mem_extremePoints (a : ℤ) {μ : Measure (ℤ → E)}
    (hμ : μ ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞) :
    μ.map (shift E a).toFun ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ :=
  map_mem_extremePoints_G (isInvariant_shift_transferSpecification Q hQ a) hμ

end ShiftCovariance

/-! ### Georgii Corollary (11.14)(a): periodicity forces shift-invariance

Georgii's own proof goes through subsampling `Q` to `Q^p` and identifying the law of
`(σ_{pi})_{i∈ℤ}` as a Gibbs measure for `γ^{Q^p}`. The argument below reaches the same conclusion
by a shorter route through convexity, using only facts already in this file:

If `θ_i(μ) = θ_j(μ)` for `i ≠ j`, put `p := |i - j| ≥ 1`; then `θ_p(μ) = μ`. Consider the
Cesàro average `ν := p⁻¹ ∑_{k=0}^{p-1} θ_k(μ)`. Since `𝒢(Q)` is closed under (finite, equal-weight)
convex combinations (`centerMass_mem_G`, from `add_smul_mem_G`) and each `θ_k(μ) ∈ 𝒢(Q)` (Remark
(5.10), `mem_G_map_shift_of_mem_G`), `ν ∈ 𝒢(Q)`. Because `θ_p(μ) = μ` re-indexes the cyclic sum
into itself, `θ_1(ν) = ν`; iterating (`map_shift_eq_self_of_map_shift_one_eq_self`) gives `θ_a(ν) =
ν` for every `a`, so `ν ∈ 𝒢_Θ(Q)` and, by Theorem (10.35) (already generalised to `γ^Q` in this
file, `mem_extremePoints_G_transferSpecification_of_measurePreserving_shift`), `ν ∈ ex 𝒢(Q)`.
Peeling the last term off the Cesàro sum exhibits `ν` itself as a two-point convex combination of
`θ_{p-1}(μ) ∈ 𝒢(Q)` and the average of the other `p - 1` terms `∈ 𝒢(Q)`; extremality of `ν` forces
`θ_{p-1}(μ) = ν`. Since `ν` is `θ`-invariant, so is `θ_{p-1}(μ)`, and undoing the shift by `p - 1`
(using `θ_p(μ) = μ`) shows `μ = θ_{p-1}(μ)` is `θ`-invariant too. -/

section CorollaryOneOneFourteenA

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- `θ_0 = id`. -/
lemma map_shift_zero_toFun (μ : Measure (ℤ → E)) : μ.map (shift E (0 : ℤ)).toFun = μ := by
  have h : (shift E (0 : ℤ)).toFun = id := by
    funext ω i
    rw [shift_toFun_apply, sub_zero]
    rfl
  rw [h, Measure.map_id]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Pushforward composes additively along the shift group: `θ_b(θ_a(μ)) = θ_{a+b}(μ)`. -/
lemma map_shift_add_toFun (μ : Measure (ℤ → E)) (a b : ℤ) :
    (μ.map (shift E a).toFun).map (shift E b).toFun = μ.map (shift E (a + b)).toFun := by
  rw [Measure.map_map (shift E b).measurable_toFun (shift E a).measurable_toFun,
    shift_toFun_comp_shift_toFun, add_comm b a]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- If `ν` is invariant under `θ_1` it is invariant under every `θ_a`. -/
lemma map_shift_eq_self_of_map_shift_one_eq_self {ν : Measure (ℤ → E)}
    (h1 : ν.map (shift E (1 : ℤ)).toFun = ν) (a : ℤ) : ν.map (shift E a).toFun = ν := by
  have hm1 : ν.map (shift E (-1 : ℤ)).toFun = ν := by
    have key := congrArg (fun μ ↦ μ.map (shift E (-1 : ℤ)).toFun) h1
    rw [map_shift_add_toFun, show (1 : ℤ) + (-1) = 0 by ring, map_shift_zero_toFun] at key
    exact key.symm
  induction a using Int.induction_on with
  | zero => exact map_shift_zero_toFun ν
  | succ i ih => rw [← map_shift_add_toFun, ih, h1]
  | pred i ih =>
    rw [show (-(i : ℤ) - 1) = (-(i : ℤ)) + (-1) by ring, ← map_shift_add_toFun, ih, hm1]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Pushforward along a fixed shift commutes with finite sums of measures. -/
lemma map_shift_finset_sum (a : ℤ) {ι : Type*} (s : Finset ι) (x : ι → Measure (ℤ → E)) :
    (∑ k ∈ s, x k).map (shift E a).toFun = ∑ k ∈ s, (x k).map (shift E a).toFun := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hnotmem ih =>
    rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem,
      Measure.map_add _ _ (shift E a).measurable_toFun, ih]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The two-term convex split of an equal-weighted Cesàro average of `n + 1` terms. -/
lemma centerMass_succ_eq {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Measure (ℤ → E)) :
    ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range (n + 1), x k
      = ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, x k)
        + ((1 : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • x n := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hcast : ((n + 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) + 1 := by push_cast; ring
  have hscalar : (n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1) * (n : ℝ≥0∞)⁻¹ = ((n : ℝ≥0∞) + 1)⁻¹ := by
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n),
      one_mul]
  have ha : ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, x k)
      = ((n : ℝ≥0∞) + 1)⁻¹ • ∑ k ∈ Finset.range n, x k := by
    rw [smul_smul, hscalar]
  have hb : ((1 : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • x n = ((n : ℝ≥0∞) + 1)⁻¹ • x n := by
    rw [one_div]
  rw [Finset.sum_range_succ, smul_add, hcast, ha, hb]

/-- **`𝒢(Q)` is closed under equal-weighted Cesàro averages of any finite positive size.** -/
theorem centerMass_mem_G {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Measure (ℤ → E))
    (hx : ∀ k, x k ∈ G (transferSpecification Q hQ)) :
    (n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, x k ∈ G (transferSpecification Q hQ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_one, Nat.cast_one, inv_one, one_smul]
    exact hx 0
  | succ n hn ih =>
    rw [centerMass_succ_eq hn]
    refine add_smul_mem_G ih (hx n) ?_
    rw [ENNReal.div_add_div_same, ENNReal.div_self (by positivity) (by finiteness)]

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The Cesàro-average identity underlying the shift-invariance of `ν` in the proof of
Corollary (11.14)(a): if `θ_p(μ) = μ` then re-indexing the cyclic sum
`∑_{k<p} θ_{k+1}(μ) = ∑_{k<p} θ_k(μ)`. -/
lemma sum_range_map_shift_succ_eq {μ : Measure (ℤ → E)} {p : ℕ} (hp1 : 1 ≤ p)
    (hp : μ.map (shift E (p : ℤ)).toFun = μ) :
    ∑ k ∈ Finset.range p, μ.map (shift E (((k + 1 : ℕ) : ℤ))).toFun
      = ∑ k ∈ Finset.range p, μ.map (shift E (k : ℤ)).toFun := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have hf0 : μ.map (shift E (((0 : ℕ) : ℤ))).toFun = μ := by
    simpa using map_shift_zero_toFun μ
  rw [Finset.sum_range_succ (fun k : ℕ ↦ μ.map (shift E (((k + 1 : ℕ) : ℤ))).toFun) n,
    Finset.sum_range_succ' (fun k : ℕ ↦ μ.map (shift E (k : ℤ)).toFun) n, hp, hf0]

include hQ in
/-- **Georgii, Corollary (11.14)(a).** For `μ ∈ 𝒢(Q)`: either `μ` is shift-invariant, or its
translates `θ_i(μ)` (`i ∈ ℤ`) are pairwise distinct. Equivalently, in the contrapositive form used
here: if `θ_i(μ) = θ_j(μ)` for some `i ≠ j`, then `θ_a(μ) = μ` for every `a : ℤ`. -/
theorem map_shift_eq_self_of_map_shift_eq_of_mem_G {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification Q hQ)) {i j : ℤ} (hij : i ≠ j)
    (heq : μ.map (shift E i).toFun = μ.map (shift E j).toFun) (a : ℤ) :
    μ.map (shift E a).toFun = μ := by
  set p : ℕ := (i - j).natAbs with hpdef
  have hpne : i - j ≠ 0 := sub_ne_zero.2 hij
  have hp1 : 1 ≤ p := by rw [hpdef]; omega
  have hp : μ.map (shift E (p : ℤ)).toFun = μ := by
    rcases le_total 0 (i - j) with hnn | hnp
    · have hcast : (p : ℤ) = i - j := by rw [hpdef, Int.natAbs_of_nonneg hnn]
      rw [hcast]
      have key := congrArg (fun ν ↦ ν.map (shift E (-j)).toFun) heq
      rwa [map_shift_add_toFun, map_shift_add_toFun, show i + (-j) = i - j by ring,
        show j + (-j) = 0 by ring, map_shift_zero_toFun] at key
    · have hnatabs : (i - j).natAbs = (j - i).natAbs := by
        rw [← Int.natAbs_neg (i - j)]; congr 1; ring
      have hcast : (p : ℤ) = j - i := by
        rw [hpdef, hnatabs, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ j - i)]
      rw [hcast]
      have key := congrArg (fun ν ↦ ν.map (shift E (-i)).toFun) heq
      rw [map_shift_add_toFun, map_shift_add_toFun, show i + (-i) = 0 by ring,
        show j + (-i) = j - i by ring, map_shift_zero_toFun] at key
      exact key.symm
  set f : ℕ → Measure (ℤ → E) := fun k ↦ μ.map (shift E (k : ℤ)).toFun with hfdef
  have hf0 : f 0 = μ := by rw [hfdef]; exact map_shift_zero_toFun μ
  have hfp : f p = μ := hp
  suffices hfin : ∀ b : ℤ, μ.map (shift E b).toFun = μ from hfin a
  rcases eq_or_lt_of_le hp1 with hp1' | hp2
  · -- `p = 1`: `μ` is itself invariant under `θ_1`.
    refine map_shift_eq_self_of_map_shift_one_eq_self ?_
    have hp1'' : (1 : ℤ) = (p : ℤ) := by exact_mod_cast hp1'
    rw [hp1'']
    exact hfp
  · -- `p ≥ 2`: the Cesàro-average argument.
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
    have hn1 : 1 ≤ n := by omega
    set ν : Measure (ℤ → E) := (p : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range p, f k with hνdef
    have hνG : ν ∈ G (transferSpecification Q hQ) :=
      centerMass_mem_G Q hQ hp1 f fun k ↦ mem_G_map_shift_of_mem_G Q hQ (k : ℤ) hμ
    have hνprob : IsProbabilityMeasure ν := ((G.mem_iff ν).1 hνG).1
    have hνGibbs : (transferSpecification Q hQ).IsGibbsMeasure ν := ((G.mem_iff ν).1 hνG).2
    have hνshift1 : ν.map (shift E (1 : ℤ)).toFun = ν := by
      rw [hνdef, Measure.map_smul, map_shift_finset_sum]
      congr 1
      have hstep : ∀ k : ℕ, (f k).map (shift E (1 : ℤ)).toFun
          = μ.map (shift E (((k + 1 : ℕ) : ℤ))).toFun := by
        intro k
        have hcast : (k : ℤ) + 1 = (((k + 1 : ℕ)) : ℤ) := by push_cast; ring
        change (μ.map (shift E (k : ℤ)).toFun).map (shift E (1 : ℤ)).toFun = _
        rw [map_shift_add_toFun, hcast]
      rw [Finset.sum_congr rfl fun k _ ↦ hstep k]
      exact sum_range_map_shift_succ_eq hp1 hfp
    have hνshiftall : ∀ b : ℤ, ν.map (shift E b).toFun = ν :=
      map_shift_eq_self_of_map_shift_one_eq_self hνshift1
    have hνext : ν ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ := by
      have := hνprob
      exact mem_extremePoints_G_transferSpecification_of_measurePreserving_shift Q hQ hνGibbs
        (fun b ↦ ⟨(shift E b).measurable_toFun, hνshiftall b⟩)
    -- Peel the last term `f n = f (p - 1)` off the Cesàro sum.
    have hsplit : ν = ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, f k)
        + ((1 : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) • f n := by
      rw [hνdef, hn, centerMass_succ_eq hn1]
    have hTG : ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, f k) ∈ G (transferSpecification Q hQ) :=
      centerMass_mem_G Q hQ hn1 f fun k ↦ mem_G_map_shift_of_mem_G Q hQ (k : ℤ) hμ
    have hfnG : f n ∈ G (transferSpecification Q hQ) :=
      mem_G_map_shift_of_mem_G Q hQ (n : ℤ) hμ
    have hwsum : ((n : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) + ((1 : ℝ≥0∞) / ((n : ℝ≥0∞) + 1)) = 1 := by
      rw [ENNReal.div_add_div_same, ENNReal.div_self (by positivity) (by finiteness)]
    have hb1 : (n : ℝ≥0∞) + 1 ≠ ⊤ := by finiteness
    have hn0' : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hseg : ν ∈ openSegment ℝ≥0∞ ((n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, f k) (f n) :=
      ⟨_, _, ENNReal.div_pos hn0' hb1, ENNReal.div_pos one_ne_zero hb1, hwsum, hsplit.symm⟩
    obtain ⟨-, hfnν⟩ := (mem_extremePoints.1 hνext).2 _ hTG _ hfnG hseg
    -- `f n = ν` is `θ`-invariant; undo the shift by `n` (recall `p = n + 1` and `θ_p(μ) = μ`).
    have hfnshift : ∀ b : ℤ, (f n).map (shift E b).toFun = f n := by
      rw [hfnν]; exact hνshiftall
    have keyshift : μ = f n := by
      have h1 := hfnshift (-(n : ℤ))
      change (μ.map (shift E (n : ℤ)).toFun).map (shift E (-(n : ℤ))).toFun
        = μ.map (shift E (n : ℤ)).toFun at h1
      rw [map_shift_add_toFun, show (n : ℤ) + (-(n : ℤ)) = 0 by ring,
        map_shift_zero_toFun] at h1
      exact h1
    intro b
    rw [keyshift]
    exact hfnshift b

end CorollaryOneOneFourteenA

/-! ### Georgii Corollary (11.14)(b), (c): phase transition or uniqueness

If `G(γ^Q) \ 𝒢_Θ(Q)` is non-empty, some *extreme* point escapes `𝒢_Θ(Q)` too — Georgii's use of
Theorem (7.26): the weight `w_{μ₀}` of any `μ₀ ∈ G(Q) \ 𝒢_Θ(Q)` is carried by `ex 𝒢(Q)`, and if
every extreme point were `Θ`-invariant, the barycentre `μ₀ = ∫ ν w_{μ₀}(dν)` would be too
(`join_mem_invariantFields`), contradicting `μ₀ ∉ 𝒢_Θ(Q)`. Combined with Corollary (11.14)(a)
(giving pairwise-distinct translates of such an extreme point) and Remark (7.2)
(`mem_extremePoints_G_map_shift_of_mem_extremePoints`, already proved: translates of an extreme
point are extreme), this yields an injection `ℤ ↪ ex 𝒢(Q)`, so `|ex 𝒢(Q)| = ∞`. -/

section CorollaryOneOneFourteenBC

include hQ in
/-- If `G(Q) \ 𝒢_Θ(Q)` is non-empty, so is `ex 𝒢(Q) \ 𝒢_Θ(Q)` — Georgii's use of Theorem (7.26)
in the proof of Corollary (11.14)(b), (c). -/
theorem exists_mem_extremePoints_G_not_mem_invariantG_of_exists_not_mem_invariantG
    {μ₀ : Measure (ℤ → E)} (hμ₀G : μ₀ ∈ G (transferSpecification Q hQ))
    (hμ₀ : μ₀ ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)) :
    ∃ μ, μ ∈ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ ∧
      μ ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := by
  by_contra hcon
  push Not at hcon
  have := hμ₀G.1
  have hGne : (G (transferSpecification Q hQ)).Nonempty := ⟨μ₀, hμ₀G⟩
  have hsub : (invariantFields (shiftGroup ℤ E) : Set (Measure (ℤ → E)))ᶜ ⊆
      ((G (transferSpecification Q hQ)).extremePoints ℝ≥0∞)ᶜ :=
    compl_subset_compl.2 fun ν hν ↦ invariantG_subset_invariantFields (hcon ν hν)
  have hwc : (weightOf hGne μ₀) ((invariantFields (shiftGroup ℤ E))ᶜ) = 0 :=
    measure_mono_null hsub (weightOf_extremePoints_compl hGne hμ₀G)
  have hjoin := join_mem_invariantFields (weightOf hGne μ₀) hwc
  rw [join_weightOf hGne hμ₀G] at hjoin
  exact hμ₀ ⟨hμ₀G, hjoin⟩

include hQ in
/-- If `μ ∈ 𝒢(Q)` is not `Θ`-invariant, its translates `θ_i(μ)` are pairwise distinct — the
contrapositive of Corollary (11.14)(a). -/
theorem injective_map_shift_of_not_mem_invariantG {μ : Measure (ℤ → E)} [IsProbabilityMeasure μ]
    (hμ : μ ∈ G (transferSpecification Q hQ))
    (hnotinv : μ ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)) :
    Function.Injective (fun i : ℤ ↦ μ.map (shift E i).toFun) := by
  intro i j hij
  by_contra hne
  refine hnotinv ⟨hμ, mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun a ↦
    ⟨(shift E a).measurable_toFun, ?_⟩⟩⟩
  exact map_shift_eq_self_of_map_shift_eq_of_mem_G Q hQ hμ hne hij a

include hQ in
/-- If some `μ₀ ∈ 𝒢(Q)` is not `Θ`-invariant, then `ex 𝒢(Q)` is infinite — the shared conclusion
of Corollary (11.14)(b), (c). -/
theorem infinite_extremePoints_G_of_exists_not_mem_invariantG {μ₀ : Measure (ℤ → E)}
    (hμ₀G : μ₀ ∈ G (transferSpecification Q hQ))
    (hμ₀ : μ₀ ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)) :
    ((G (transferSpecification Q hQ)).extremePoints ℝ≥0∞).Infinite := by
  obtain ⟨μ, hμext, hμninv⟩ :=
    exists_mem_extremePoints_G_not_mem_invariantG_of_exists_not_mem_invariantG Q hQ hμ₀G hμ₀
  have hμprob : IsProbabilityMeasure μ := hμext.1.1
  have hinj := injective_map_shift_of_not_mem_invariantG Q hQ hμext.1 hμninv
  have hrange : Set.range (fun i : ℤ ↦ μ.map (shift E i).toFun)
      ⊆ (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ := by
    rintro _ ⟨i, rfl⟩
    exact mem_extremePoints_G_map_shift_of_mem_extremePoints Q hQ i hμext
  exact Set.Infinite.mono hrange (Set.infinite_range_of_injective hinj)

include hQ in
/-- **Georgii, Theorem (11.13), packaged as a set equality.** The `Θ`-invariant Gibbs measures for
`γ^Q` are exactly `{μ_P}` when `Q ~ P` for a positive recurrent stochastic matrix `P` with positive
entries. -/
theorem invariantG_eq_singleton_boundaryLawMeasure_const
    {P : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1)
    {α : E → ℝ≥0∞} (hα0 : ∀ x, 0 < α x) (hαt : ∀ x, α x ≠ ⊤) (hα1 : ∑' x, α x = 1)
    (hαP : ∀ y, ∑' x, α x * P x y = α y)
    (heq : transferSpecification Q hQ
      = transferSpecification P (isTransferMatrix_of_stochastic hpos hP)) :
    invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)
      = {boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP)} := by
  set μP := boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP) with hμPdef
  have hμPinv : μP ∈ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) :=
    boundaryLawMeasure_const_mem_invariantG hpos hP hα0 hαt hα1 hαP hQ heq
  ext ν
  constructor
  · rintro ⟨⟨hνprob, hνGibbs⟩, hνinv⟩
    have := hνprob
    have hμPGibbs : (transferSpecification Q hQ).IsGibbsMeasure μP := hμPinv.1.2
    have hνshift := (mem_invariantFields_shiftGroup.1 hνinv).2
    have hμPshift := (mem_invariantFields_shiftGroup.1 hμPinv.2).2
    exact Set.mem_singleton_iff.2
      (eq_of_isGibbsMeasure_transferSpecification_of_measurePreserving_shift Q hQ hνGibbs
        hμPGibbs hνshift hμPshift)
  · rintro rfl
    exact hμPinv

include hQ in
/-- **Georgii, Theorem (11.13), "only if" half, packaged as a set equality.** The `Θ`-invariant
Gibbs measures for `γ^Q` are empty when `Q` is not equivalent to any positive recurrent stochastic
matrix with positive entries. -/
theorem invariantG_eq_empty_of_not_exists_isPositiveRecurrent
    (hnotequiv : ¬ ∃ (P : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = Q x y * r y / (q * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P)) :
    invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) = ∅ := by
  by_contra hne
  obtain ⟨ν, hν⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨P, q, r, hq0, hqt, hr0, hrt, hPQ, hPstoch, hposrec⟩ :=
    exists_transferMatrix_equiv_and_isPositiveRecurrent_of_invariantG_nonempty Q hQ ⟨ν, hν⟩
  exact hnotequiv ⟨P, q, r, hq0, hqt, hr0, hrt, hPQ, hPstoch, hposrec⟩

include hQ in
/-- **Georgii, Corollary (11.14)(b).** If `Q ~ P` for a positive recurrent stochastic matrix `P`
with positive entries (`P` stochastic with invariant probability vector `α`), then either
`𝒢(Q) = {μ_P}` or `|ex 𝒢(Q)| = ∞`. -/
theorem eq_singleton_boundaryLawMeasure_const_or_infinite_extremePoints_G
    {P : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1)
    {α : E → ℝ≥0∞} (hα0 : ∀ x, 0 < α x) (hαt : ∀ x, α x ≠ ⊤) (hα1 : ∑' x, α x = 1)
    (hαP : ∀ y, ∑' x, α x * P x y = α y)
    (heq : transferSpecification Q hQ
      = transferSpecification P (isTransferMatrix_of_stochastic hpos hP)) :
    G (transferSpecification Q hQ)
        = {boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP)}
      ∨ ((G (transferSpecification Q hQ)).extremePoints ℝ≥0∞).Infinite := by
  set μP := boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP) with hμPdef
  have hinvsingle := invariantG_eq_singleton_boundaryLawMeasure_const Q hQ hpos hP hα0 hαt hα1 hαP
    heq
  have hμPG : μP ∈ G (transferSpecification Q hQ) :=
    (hinvsingle ▸ Set.mem_singleton μP : μP ∈ invariantG _ _).1
  rcases eq_or_ne (G (transferSpecification Q hQ)) {μP} with heqG | hneG
  · exact Or.inl heqG
  · refine Or.inr ?_
    have hex : ∃ μ₀ ∈ G (transferSpecification Q hQ),
        μ₀ ∉ invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := by
      by_contra hcon
      push Not at hcon
      refine hneG (Set.Subset.antisymm (fun ν hν ↦ ?_) (fun ν hν ↦ ?_))
      · rw [hinvsingle] at hcon; exact hcon ν hν
      · rw [Set.mem_singleton_iff.1 hν]; exact hμPG
    obtain ⟨μ₀, hμ₀G, hμ₀⟩ := hex
    exact infinite_extremePoints_G_of_exists_not_mem_invariantG Q hQ hμ₀G hμ₀

include hQ in
/-- **Georgii, Corollary (11.14)(c).** If `Q` is not equivalent to any positive recurrent
stochastic matrix with positive entries, then either `𝒢(Q) = ∅` or `|ex 𝒢(Q)| = ∞`. -/
theorem eq_empty_G_or_infinite_extremePoints_G
    (hnotequiv : ¬ ∃ (P : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = Q x y * r y / (q * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P)) :
    G (transferSpecification Q hQ) = ∅
      ∨ ((G (transferSpecification Q hQ)).extremePoints ℝ≥0∞).Infinite := by
  rcases Set.eq_empty_or_nonempty (G (transferSpecification Q hQ)) with hempty | ⟨μ₀, hμ₀⟩
  · exact Or.inl hempty
  · exact Or.inr (infinite_extremePoints_G_of_exists_not_mem_invariantG Q hQ hμ₀
      (by rw [invariantG_eq_empty_of_not_exists_isPositiveRecurrent Q hQ hnotequiv]
          exact Set.notMem_empty μ₀))

end CorollaryOneOneFourteenBC

/-! ### Georgii Theorem (11.15), general extreme point, and Corollary (11.17)

`ex 𝒢(Q) ⊆ 𝒢_Θ(Q)` (from the periodicity `θ_{N!}(μ) = μ` of every extreme point, Corollary
(11.14)(a), and `N! ≠ 0`) together with Theorem (7.26) (every `μ ∈ 𝒢(Q)` is a barycentre of `ex
𝒢(Q)`) gives `𝒢(Q) = 𝒢_Θ(Q)` — the same "escape" argument as Corollary (11.14)(b), (c), run in the
contrapositive. Corollary (11.17) then combines this with Theorem (11.13)
(`invariantG_eq_singleton_boundaryLawMeasure_const`,
`invariantG_eq_empty_of_not_exists_isPositiveRecurrent`, both already proved above). -/

section TheoremOneOneFifteen

include hQ in
/-- If every extreme point of `𝒢(Q)` is `Θ`-invariant, then `𝒢(Q) = 𝒢_Θ(Q)` — the contrapositive
of `exists_mem_extremePoints_G_not_mem_invariantG_of_exists_not_mem_invariantG`, combined with
`invariantG_subset_G`. -/
theorem G_eq_invariantG_of_extremePoints_G_subset_invariantG
    (hsub : (G (transferSpecification Q hQ)).extremePoints ℝ≥0∞ ⊆
      invariantG (transferSpecification Q hQ) (shiftGroup ℤ E)) :
    G (transferSpecification Q hQ) = invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := by
  refine Set.Subset.antisymm (fun μ₀ hμ₀G ↦ ?_) invariantG_subset_G
  by_contra hμ₀
  obtain ⟨μ, hμext, hμninv⟩ :=
    exists_mem_extremePoints_G_not_mem_invariantG_of_exists_not_mem_invariantG Q hQ hμ₀G hμ₀
  exact hμninv (hsub hμext)

include hQ in
/-- **Georgii, Theorem (11.15), for a general extreme point.** If
`inf_x ∑_{n=1}^N Q^n(x,x) > 0` for some `N ≥ 1`, then `𝒢(Q) = 𝒢_Θ(Q)`. -/
theorem G_eq_invariantG_of_forall_le_sum {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    G (transferSpecification Q hQ) = invariantG (transferSpecification Q hQ) (shiftGroup ℤ E) := by
  refine G_eq_invariantG_of_extremePoints_G_subset_invariantG Q hQ fun μ hμ ↦ ?_
  have hμprob : IsProbabilityMeasure μ := hμ.1.1
  have hμG : μ ∈ G (transferSpecification Q hQ) := hμ.1
  have hper : μ.map (shift E (N.factorial : ℤ)).toFun = μ :=
    map_shift_factorial_eq_self_of_mem_extremePoints Q hQ hμ hN hε h
  have hne : (N.factorial : ℤ) ≠ (0 : ℤ) := Int.natCast_ne_zero.2 (Nat.factorial_ne_zero N)
  have heq0 : μ.map (shift E (N.factorial : ℤ)).toFun = μ.map (shift E (0 : ℤ)).toFun :=
    hper.trans (map_shift_zero_toFun μ).symm
  have hshift : ∀ a : ℤ, μ.map (shift E a).toFun = μ := fun a ↦
    map_shift_eq_self_of_map_shift_eq_of_mem_G Q hQ hμG hne heq0 a
  exact ⟨hμG, mem_invariantFields_shiftGroup.2 ⟨inferInstance, fun a ↦
    ⟨(shift E a).measurable_toFun, hshift a⟩⟩⟩

include hQ in
/-- **Georgii, Corollary (11.17), existence-uniqueness half.** If `Q ~ P` for a positive recurrent
stochastic matrix `P` with positive entries, and `inf_x ∑_{n=1}^N Q^n(x,x) > 0` for some `N ≥ 1`,
then `𝒢(Q) = {μ_P}`. -/
theorem eq_singleton_boundaryLawMeasure_const_G_of_forall_le_sum
    {P : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1)
    {α : E → ℝ≥0∞} (hα0 : ∀ x, 0 < α x) (hαt : ∀ x, α x ≠ ⊤) (hα1 : ∑' x, α x = 1)
    (hαP : ∀ y, ∑' x, α x * P x y = α y)
    (heq : transferSpecification Q hQ
      = transferSpecification P (isTransferMatrix_of_stochastic hpos hP))
    {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    G (transferSpecification Q hQ)
      = {boundaryLawMeasure (isBoundaryLaw_const hP hα0 hαt hα1 hαP)} := by
  rw [G_eq_invariantG_of_forall_le_sum Q hQ hN hε h,
    invariantG_eq_singleton_boundaryLawMeasure_const Q hQ hpos hP hα0 hαt hα1 hαP heq]

include hQ in
/-- **Georgii, Corollary (11.17), non-existence half.** If `Q` is not equivalent to any positive
recurrent stochastic matrix with positive entries, and `inf_x ∑_{n=1}^N Q^n(x,x) > 0` for some
`N ≥ 1`, then `𝒢(Q) = ∅`. -/
theorem eq_empty_G_of_forall_le_sum
    (hnotequiv : ¬ ∃ (P : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = Q x y * r y / (q * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧
      ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P))
    {N : ℕ} (hN : 0 < N) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x}) :
    G (transferSpecification Q hQ) = ∅ := by
  rw [G_eq_invariantG_of_forall_le_sum Q hQ hN hε h,
    invariantG_eq_empty_of_not_exists_isPositiveRecurrent Q hQ hnotequiv]

end TheoremOneOneFifteen

end MarkovBridge

/-! ## Georgii Comment (11.18)(3): `L(Q) = tL(P) + (1-t)` for `Q = tP + (1-t)I`, and non-existence

The binomial identity `Q^n(x,x) = ∑_k C(n,k) t^k (1-t)^{n-k} P^k(x,x)`
    (`ofMatrix_lazy_pow_apply_singleton`,
proved by induction on `n` via Pascal's rule — the intended Mathlib home is next to
`Kernel.ofMatrix` in `GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix.lean`, stated for a
general commuting pair rather than specifically for `lazy`) feeds two purely analytic facts about
`convergenceNorm` (intended Mathlib home: `GibbsMeasure/Mathlib/Probability/Kernel/
CountableMatrix/Recurrence.lean`, as genuine generalizations of Vere-Jones' remark after (11.6)):

* `lazy_convergenceNorm_le`: `L(Q) ≤ tL(P) + (1-t)`, unconditionally (only needs `P` stochastic).
  The eventual bound `eventually_lazy_pow_le_of_lt_convergenceNorm` behind it splits `Q^n(x,x)`
  into finitely many "junk" terms `k < k₀` (crudely bounded by `n^{k₀}(1-t)^{n-k₀}`, itself
  exponentially dominated by any target rate via the elementary transfer lemma
  `ENNReal.eventually_pow_le_pow_of_one_lt` from the real-analysis fact
  `tendsto_pow_const_div_const_pow_of_one_lt`) and the "bulk" `k ≥ k₀`, bounded via the ordinary
  binomial theorem (`add_pow`) for real numbers once `P^k(x,x) ≤ (L+δ)^k` eventually.
* `one_le_lazy_convergenceNorm_of_convergenceNorm_eq_one`: if `L(P) = 1`, `L(Q) ≥ 1`, by the dual
  argument (needs `P` positive, for Fekete's lemma `tendsto_convergenceNorm_of_forall_pos` to give
  a genuine limit rather than a limsup) through `eventually_le_lazy_pow_of_lt_convergenceNorm`.

Together (`lazy_convergenceNorm_eq_one_of_convergenceNorm_eq_one`): `L(P) = 1 ⟹ L(Q) = 1`. This is
exactly the hypothesis `isPositiveRecurrent_of_apply_eq_mul_div` (Recurrence.lean) needs to rule
out `Q` being equivalent to a positive recurrent matrix once `Q` itself is known not to be
positive recurrent; `isPositiveRecurrent_ofMatrix_of_isPositiveRecurrent_lazy` supplies that last
fact (an invariant probability measure of `Q = tP + (1-t)I` is already `P`-invariant, since
`t ≠ 0`). `eq_empty_G_lazy_of_not_isPositiveRecurrent` assembles all of this into **Georgii Comment
(11.18)(3)**: for `Q = tP + (1-t)I`, `0 < t < 1`, `P` a positive stochastic matrix with `L(P) = 1`
which is *not* positive recurrent (Georgii's "null recurrent or transient"), `𝒢(γ^Q) = ∅`.
Combined with the existence half already in the file (`boundaryLawMeasure_const_lazy_mem_
invariantG`, `eq_singleton_boundaryLawMeasure_const_G_of_forall_le_sum`), both halves of Comment
(11.18)(3) are now proved. The general formula also reproves Comment (11.18)(1) directly (no need
for the separate `t = 1` degenerate check Georgii's own remark makes for finite `E`).
-/


theorem ENNReal_add_le_of_two_mul_le_of_two_mul_le {a b c : ℝ≥0∞} (h1 : 2 * a ≤ c) (h2 : 2 * b ≤
    c) :
    a + b ≤ c := by
  have h : (a + b) * 2 ≤ c * 2 := by
    rw [add_mul]
    calc a * 2 + b * 2 ≤ c + c := by
          rw [mul_comm a 2, mul_comm b 2]
          exact add_le_add h1 h2
      _ = c * 2 := by ring
  exact (ENNReal.mul_le_mul_iff_left (a := a + b) (b := c) (c := 2) (by norm_num) (by norm_num)).1 h

theorem ofMatrix_lazy_pow_apply_singleton {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] (P : E → E → ℝ≥0∞) (t : ℝ≥0∞) (n : ℕ) (a c : E) :
    (Kernel.ofMatrix (lazy P t) ^ n) a {c}
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
          * (Kernel.ofMatrix P ^ k) a {c} := by
  induction n generalizing a c with
  | zero =>
    simp
  | succ n ih =>
    rw [Kernel.ofMatrix_pow_succ'_apply_singleton]
    have hrw : ∀ b, (Kernel.ofMatrix (lazy P t) ^ n) a {b} * lazy P t b c
        = ∑ k ∈ Finset.range (n + 1),
            (t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}
              * P b c)
            + (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}))) := by
      intro b
      rw [ih a b, Finset.sum_mul]
      congr 1
      ext k
      simp only [lazy]
      ring
    simp_rw [hrw]
    rw [Summable.tsum_finsetSum (fun k _ => ENNReal.summable)]
    have hterm : ∀ k, ∑' b,
          (t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}
              * P b c)
            + (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b})))
        = (n.choose k : ℝ≥0∞) * t ^ (k+1) * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ (k+1)) a {c}
          + (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k + 1) * (Kernel.ofMatrix P ^ k) a {c} := by
      intro k
      rw [ENNReal.tsum_add]
      congr 1
      · have step : ∀ i, t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
              * (Kernel.ofMatrix P ^ k) a {i} * P i c)
            = (t * (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k))
              * ((Kernel.ofMatrix P ^ k) a {i} * P i c) := by
          intro i; ring
        simp_rw [step, ENNReal.tsum_mul_left,
          ← Kernel.ofMatrix_pow_succ'_apply_singleton P k a c]
        ring
      · have step : ∀ b, (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}))
            = ((1 - t) * (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k))
              * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b * (Kernel.ofMatrix P ^ k) a {b}) := by
          intro b; ring
        simp_rw [step, ENNReal.tsum_mul_left]
        have hcol : ∑' b, ({c} : Set E).indicator (1 : E → ℝ≥0∞) b * (Kernel.ofMatrix P ^ k) a {b}
            = (Kernel.ofMatrix P ^ k) a {c} := by
          rw [tsum_eq_single c (fun b hb => by simp [Set.indicator_of_notMem, hb])]
          simp
        rw [hcol]
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    set A := ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ≥0∞) * t ^ (k + 1) * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ (k + 1)) a {c}
      with hA
    set B := ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k + 1) * (Kernel.ofMatrix P ^ k) a {c}
      with hB
    have hCA : ∀ i ∈ Finset.range (n + 1),
        ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c}
          = (n.choose i : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c}
            + (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      intro i _
      have hp : ((n + 1).choose (i + 1) : ℝ≥0∞) = (n.choose i : ℝ≥0∞) + (n.choose (i + 1) : ℝ≥0∞) := by
        rw [← Nat.cast_add, Nat.choose_succ_succ' n i]
      rw [hp]; ring
    have hCstep : ∑ i ∈ Finset.range (n + 1),
          ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c}
        = A + ∑ i ∈ Finset.range (n + 1),
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      rw [Finset.sum_congr rfl hCA, Finset.sum_add_distrib, hA]
    have hfront : ∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose j : ℝ≥0∞) * t ^ j * (1 - t) ^ (n + 1 - j) * (Kernel.ofMatrix P ^ j) a {c}
        = (∑ i ∈ Finset.range (n + 1),
              ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n + 1 - (i + 1))
                * (Kernel.ofMatrix P ^ (i + 1)) a {c})
          + ((n + 1).choose 0 : ℝ≥0∞) * t ^ 0 * (1 - t) ^ (n + 1 - 0) * (Kernel.ofMatrix P ^ 0) a {c} :=
      Finset.sum_range_succ' _ (n + 1)
    have hexp : ∀ i ∈ Finset.range (n + 1),
        ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n + 1 - (i + 1))
            * (Kernel.ofMatrix P ^ (i + 1)) a {c}
          = ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.1 hi
      have hexp : n + 1 - (i + 1) = n - i := by omega
      rw [hexp]
    rw [Finset.sum_congr rfl hexp] at hfront
    have hf0 : ((n + 1).choose 0 : ℝ≥0∞) * t ^ 0 * (1 - t) ^ (n + 1 - 0) * (Kernel.ofMatrix P ^ 0) a {c}
        = (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by simp
    rw [hf0] at hfront
    have hS12 : (∑ i ∈ Finset.range (n + 1),
          (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c})
        = ∑ i ∈ Finset.range n,
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      rw [Finset.sum_range_succ]
      have hz : (n.choose (n + 1) : ℝ≥0∞) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      ring
    have hBdecomp : B = (∑ i ∈ Finset.range n,
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c})
          + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by
      rw [hB, Finset.sum_range_succ']
      have hexp2 : ∀ i ∈ Finset.range n,
          (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - (i + 1) + 1) * (Kernel.ofMatrix P ^ (i + 1)) a {c}
            = (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
        intro i hi
        have hi' : i < n := Finset.mem_range.1 hi
        have he : n - (i + 1) + 1 = n - i := by omega
        rw [he]
      rw [Finset.sum_congr rfl hexp2]
      simp
    calc A + B = A + ((∑ i ∈ Finset.range n,
              (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c}) := by rw [hBdecomp]
      _ = (A + ∑ i ∈ Finset.range (n + 1),
              (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by rw [hS12]; ring
      _ = (∑ i ∈ Finset.range (n + 1),
              ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i) * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by rw [← hCstep]
      _ = ∑ j ∈ Finset.range (n + 1 + 1),
            ((n + 1).choose j : ℝ≥0∞) * t ^ j * (1 - t) ^ (n + 1 - j) * (Kernel.ofMatrix P ^ j) a {c} := hfront.symm


open Filter Topology ProbabilityTheory in
/-- **Helper U**: the eventual upper bound `Q^n(x,x) ≤ (t*(L+δ)+(1-t)+ε)^n` for a lazy chain,
from the binomial identity plus the fact that finitely many "junk" terms of small `k` are
exponentially dominated by a slightly larger geometric rate. -/
theorem eventually_lazy_pow_le_of_lt_convergenceNorm {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E)
    {δ ε : ℝ≥0∞} (hδ0 : 0 < δ) (hδt : δ ≠ ⊤) (hε0 : 0 < ε) (hεt : ε ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop,
      (Kernel.ofMatrix (lazy P t) ^ n) x {x}
        ≤ (t * (Kernel.convergenceNorm (Kernel.ofMatrix P) x + δ) + (1 - t) + ε) ^ n := by
  have hMP : ProbabilityTheory.IsMarkovKernel (Kernel.ofMatrix P) := Kernel.isMarkovKernel_ofMatrix P hP
  set L := Kernel.convergenceNorm (Kernel.ofMatrix P) x with hLdef
  set ρ := t * (L + δ) + (1 - t) with hρdef
  have ht1' : t ≠ ⊤ := ht1.ne_top
  have h1t0 : (0:ℝ≥0∞) < 1 - t := tsub_pos_of_lt ht1
  have h1tt : (1:ℝ≥0∞) - t ≠ ⊤ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  have hρpos : 0 < ρ := lt_of_lt_of_le h1t0 (by rw [hρdef]; exact le_add_self)
  have hρtop : ρ ≠ ⊤ := by
    rw [hρdef]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ht1' (by
      have : L ≤ 1 := Kernel.convergenceNorm_le_one
      exact ENNReal.add_ne_top.2 ⟨this.trans_lt ENNReal.one_lt_top |>.ne, hδt⟩), h1tt⟩
  -- Step 1: eventually a_k < (L+δ)^k.
  have hLne : L ≠ ⊤ := (Kernel.convergenceNorm_le_one (κ := Kernel.ofMatrix P)).trans_lt
    ENNReal.one_lt_top |>.ne
  obtain ⟨k0, hk0⟩ := eventually_atTop.1
    (Kernel.eventually_lt_pow_of_convergenceNorm_lt (κ := Kernel.ofMatrix P) (x := x)
      (show L < L + δ from ENNReal.lt_add_right hLne hδ0.ne'))
  -- Step 2: a_k ≤ 1 for every k.
  have ha_le_one : ∀ k, (Kernel.ofMatrix P ^ k) x {x} ≤ 1 := fun k ↦ by
    have hprob : ProbabilityTheory.IsMarkovKernel (Kernel.ofMatrix P ^ k) := inferInstance
    have hmono := measure_mono (μ := (Kernel.ofMatrix P ^ k) x) (Set.subset_univ ({x} : Set E))
    rwa [measure_univ] at hmono
  -- Step 3: ρ < ρ + ε, and the ratio ρ/(ρ+ε) < 1.
  have hρlt : ρ < ρ + ε := ENNReal.lt_add_right hρtop hε0.ne'
  have hρge1t : 1 - t ≤ ρ := by rw [hρdef]; exact le_add_self
  have h1tlt : 1 - t < ρ + ε := lt_of_le_of_lt hρge1t hρlt
  have hρepstop : ρ + ε ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hρtop, hεt⟩
  have hρepspos : 0 < ρ + ε := hρpos.trans_le le_self_add
  have hbulk_ratio : ∀ᶠ n : ℕ in atTop, 2 * ρ ^ n ≤ (ρ + ε) ^ n := by
    have hratio : ρ / (ρ + ε) < 1 :=
      (ENNReal.div_lt_iff (Or.inl hρepspos.ne') (Or.inl hρepstop)).2 (by rw [one_mul]; exact hρlt)
    have heq : ρ = ρ / (ρ + ε) * (ρ + ε) := (ENNReal.div_mul_cancel hρepspos.ne' hρepstop).symm
    have hpow : ∀ n : ℕ, ρ ^ n = (ρ / (ρ + ε)) ^ n * (ρ + ε) ^ n := fun n ↦ by
      rw [← mul_pow, ← heq]
    have htwohalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]
    have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
    have hev : ∀ᶠ n : ℕ in atTop, (ρ / (ρ + ε)) ^ n < 1 / 2 :=
      (tendsto_order.1 htend).2 _ (by norm_num)
    filter_upwards [hev] with n hn
    rw [hpow n, ← mul_assoc]
    calc 2 * (ρ / (ρ + ε)) ^ n * (ρ + ε) ^ n
        ≤ 1 * (ρ + ε) ^ n := by
          gcongr
          calc 2 * (ρ / (ρ + ε)) ^ n ≤ 2 * (1 / 2) := by gcongr
            _ = 1 := htwohalf
      _ = (ρ + ε) ^ n := one_mul _
  -- Step 4: the junk terms `k < k0` are exponentially dominated.
  have hr'1 : 1 - t < (ρ + ε) := h1tlt
  have hr' : 1 < (ρ + ε) / (1 - t) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl h1t0.ne') (Or.inl h1tt)).2 (by rw [one_mul]; exact hr'1)
  set r' := (ρ + ε) / (1 - t) with hr'def
  have hr'eq : r' * (1 - t) = ρ + ε := ENNReal.div_mul_cancel h1t0.ne' h1tt
  have hCk0 : ((1 - t) ^ k0 : ℝ≥0∞) ≠ 0 := pow_ne_zero k0 h1t0.ne'
  have hCk0t : ((1 - t) ^ k0 : ℝ≥0∞) ≠ ⊤ := (ENNReal.pow_ne_top h1tt)
  set C := (k0 : ℝ≥0∞) * ((1 - t) ^ k0)⁻¹ with hCdef
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.2 hCk0)
  have hjunk_eq : ∀ n : ℕ, k0 ≤ n →
      (1 - t) ^ (n - k0) = (1 - t) ^ n * ((1 - t) ^ k0)⁻¹ := by
    intro n hn
    have hpa : (1 - t) ^ (n - k0) * (1 - t) ^ k0 = (1 - t) ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [← hpa, mul_assoc, ENNReal.mul_inv_cancel hCk0 hCk0t, mul_one]
  have hev2C : ∀ᶠ n : ℕ in atTop, 2 * C ≤ (n : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hCtop)
    exact eventually_atTop.2 ⟨N, fun n hn ↦ hN.le.trans (by exact_mod_cast hn)⟩
  have hevcore : ∀ᶠ n : ℕ in atTop, (n : ℝ≥0∞) ^ (k0 + 1) ≤ r' ^ n :=
    ENNReal.eventually_pow_le_pow_of_one_lt hr' (k0 + 1)
  have hevk0 : ∀ᶠ n : ℕ in atTop, k0 ≤ n := eventually_ge_atTop k0
  filter_upwards [hbulk_ratio, hev2C, hevcore, hevk0] with n hbulk h2C hcore hk0n
  rw [ofMatrix_lazy_pow_apply_singleton]
  set F : ℕ → ℝ≥0∞ := fun k ↦
    (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) x {x} with hFdef
  have hsplit : ∑ k ∈ Finset.range (n + 1), F k
      = (∑ k ∈ Finset.range k0, F k) + (∑ k ∈ Finset.Ico k0 (n + 1), F k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive F (Nat.zero_le k0) (by omega)).symm
  -- Junk bound.
  have hjunk_term : ∀ k ∈ Finset.range k0, F k ≤ (n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0) := by
    intro k hk
    have hk' : k < k0 := Finset.mem_range.1 hk
    have hnpos : 1 ≤ n := by omega
    have h1 : (n.choose k : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ k0 := by
      calc (n.choose k : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ k := by exact_mod_cast Nat.choose_le_pow n k
        _ ≤ (n : ℝ≥0∞) ^ k0 := pow_le_pow_right₀ (by exact_mod_cast hnpos) hk'.le
    have h2 : (1 - t) ^ (n - k) ≤ (1 - t) ^ (n - k0) :=
      pow_le_pow_of_le_one bot_le tsub_le_self (by omega)
    calc F k = (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) x {x} := rfl
      _ ≤ (n : ℝ≥0∞) ^ k0 * 1 * (1 - t) ^ (n - k0) * 1 := by
          gcongr
          · exact pow_le_one₀ bot_le ht1.le
          · exact ha_le_one k
      _ = (n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0) := by ring
  have hjunk_sum : (∑ k ∈ Finset.range k0, F k) ≤ (k0 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0)) := by
    calc (∑ k ∈ Finset.range k0, F k) ≤ ∑ k ∈ Finset.range k0, (n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0) :=
          Finset.sum_le_sum hjunk_term
      _ = (k0 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjunk_C : (k0 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k0 * (1 - t) ^ (n - k0)) = C * (n : ℝ≥0∞) ^ k0 * (1 - t) ^ n := by
    rw [hjunk_eq n hk0n, hCdef]
    ring
  have hjunk2 : 2 * (∑ k ∈ Finset.range k0, F k) ≤ (ρ + ε) ^ n := by
    calc 2 * (∑ k ∈ Finset.range k0, F k)
        ≤ 2 * (C * (n : ℝ≥0∞) ^ k0 * (1 - t) ^ n) := by
          rw [← hjunk_C]; gcongr
      _ = ((n : ℝ≥0∞) ^ k0 * (2 * C)) * (1 - t) ^ n := by ring
      _ ≤ ((n : ℝ≥0∞) ^ k0 * (n : ℝ≥0∞)) * (1 - t) ^ n := by
          gcongr
      _ = (n : ℝ≥0∞) ^ (k0 + 1) * (1 - t) ^ n := by rw [pow_succ]
      _ ≤ r' ^ n * (1 - t) ^ n := by gcongr
      _ = (r' * (1 - t)) ^ n := (mul_pow r' (1 - t) n).symm
      _ = (ρ + ε) ^ n := by rw [hr'eq]
  -- Bulk bound.
  have hbulk_term : ∀ k ∈ Finset.Ico k0 (n + 1), F k
      ≤ (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k) := by
    intro k hk
    have hk' : k0 ≤ k := (Finset.mem_Ico.1 hk).1
    have := (hk0 k hk').le
    calc F k = (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) x {x} := rfl
      _ ≤ (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (L + δ) ^ k := by gcongr
      _ = (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k) := by rw [mul_pow]; ring
  have hbulk_sum : (∑ k ∈ Finset.Ico k0 (n + 1), F k)
      ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k) := by
    calc (∑ k ∈ Finset.Ico k0 (n + 1), F k)
        ≤ ∑ k ∈ Finset.Ico k0 (n + 1), (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k) :=
          Finset.sum_le_sum hbulk_term
      _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            rw [Finset.mem_Ico] at hk
            exact Finset.mem_range.2 hk.2
          · intro k _ _
            positivity
  have hbulk_eq : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * (t * (L + δ)) ^ k * (1 - t) ^ (n - k)
      = ρ ^ n := by
    rw [hρdef, add_pow (t * (L + δ)) (1 - t) n]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcancel : (∑ k ∈ Finset.range k0, F k) + ρ ^ n ≤ (ρ + ε) ^ n := by
    have h : ((∑ k ∈ Finset.range k0, F k) + ρ ^ n) * 2 ≤ (ρ + ε) ^ n * 2 := by
      rw [add_mul]
      calc (∑ k ∈ Finset.range k0, F k) * 2 + ρ ^ n * 2
          ≤ (ρ + ε) ^ n + (ρ + ε) ^ n := by
            rw [mul_comm (∑ k ∈ Finset.range k0, F k) 2, mul_comm (ρ ^ n) 2]
            exact add_le_add hjunk2 hbulk
        _ = (ρ + ε) ^ n * 2 := by ring
    exact (ENNReal.mul_le_mul_iff_left (a := (∑ k ∈ Finset.range k0, F k) + ρ ^ n) (b := (ρ + ε) ^ n)
      (c := 2) (by norm_num) (by norm_num)).1 h
  calc ∑ k ∈ Finset.range (n + 1), F k
      = (∑ k ∈ Finset.range k0, F k) + (∑ k ∈ Finset.Ico k0 (n + 1), F k) := hsplit
    _ ≤ (∑ k ∈ Finset.range k0, F k) + ρ ^ n := by
        gcongr
        rw [← hbulk_eq]; exact hbulk_sum
    _ ≤ (ρ + ε) ^ n := hcancel



open Filter Topology ProbabilityTheory in
theorem lazy_convergenceNorm_le {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E) :
    Kernel.convergenceNorm (Kernel.ofMatrix (lazy P t)) x
      ≤ t * Kernel.convergenceNorm (Kernel.ofMatrix P) x + (1 - t) := by
  set L := Kernel.convergenceNorm (Kernel.ofMatrix P) x with hLdef
  refine ENNReal.le_of_forall_pos_le_add fun ε0 hε0 _ ↦ ?_
  have hδpos : 0 < (ε0 : ℝ≥0∞) / 2 := ENNReal.div_pos (by exact_mod_cast hε0.ne') (by norm_num)
  have hδtop : (ε0 : ℝ≥0∞) / 2 ≠ ⊤ := ENNReal.div_ne_top ENNReal.coe_ne_top (by norm_num)
  have hkey := eventually_lazy_pow_le_of_lt_convergenceNorm (P := P) hP ht0 ht1 x
    (δ := (ε0 : ℝ≥0∞) / 2) (ε := (ε0 : ℝ≥0∞) / 2) hδpos hδtop hδpos hδtop
  have htarget_le : t * (L + (ε0 : ℝ≥0∞) / 2) + (1 - t) + (ε0 : ℝ≥0∞) / 2
      ≤ t * L + (1 - t) + (ε0 : ℝ≥0∞) := by
    have h1 : t * (L + (ε0 : ℝ≥0∞) / 2) ≤ t * L + (ε0 : ℝ≥0∞) / 2 := by
      have h2 : t * ((ε0 : ℝ≥0∞) / 2) ≤ (ε0 : ℝ≥0∞) / 2 := by
        calc t * ((ε0 : ℝ≥0∞) / 2) ≤ 1 * ((ε0 : ℝ≥0∞) / 2) := by gcongr
          _ = (ε0 : ℝ≥0∞) / 2 := one_mul _
      calc t * (L + (ε0 : ℝ≥0∞) / 2) = t * L + t * ((ε0 : ℝ≥0∞) / 2) := by ring
        _ ≤ t * L + (ε0 : ℝ≥0∞) / 2 := by gcongr
    calc t * (L + (ε0 : ℝ≥0∞) / 2) + (1 - t) + (ε0 : ℝ≥0∞) / 2
        ≤ (t * L + (ε0 : ℝ≥0∞) / 2) + (1 - t) + (ε0 : ℝ≥0∞) / 2 := by gcongr
      _ = (t * L + (1 - t)) + ((ε0 : ℝ≥0∞) / 2 + (ε0 : ℝ≥0∞) / 2) := by ring
      _ = (t * L + (1 - t)) + (ε0 : ℝ≥0∞) := by rw [ENNReal.add_halves]
  exact (Kernel.convergenceNorm_le_of_eventually hkey).trans htarget_le

open Filter Topology ProbabilityTheory in
/-- **Helper L**: the eventual lower bound `(t*(L-δ)+(1-t)-ε)^n ≤ Q^n(x,x)` for a lazy chain,
dual to Helper U. -/
theorem eventually_le_lazy_pow_of_lt_convergenceNorm {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E)
    {δ ε : ℝ≥0∞} (hδ0 : 0 < δ) (hε0 : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (t * (Kernel.convergenceNorm (Kernel.ofMatrix P) x - δ) + (1 - t) - ε) ^ n
        ≤ (Kernel.ofMatrix (lazy P t) ^ n) x {x} := by
  have hMP : ProbabilityTheory.IsMarkovKernel (Kernel.ofMatrix P) := Kernel.isMarkovKernel_ofMatrix P hP
  set L := Kernel.convergenceNorm (Kernel.ofMatrix P) x with hLdef
  set ρ' := t * (L - δ) + (1 - t) with hρ'def
  have ht1' : t ≠ ⊤ := ht1.ne_top
  have h1t0 : (0 : ℝ≥0∞) < 1 - t := tsub_pos_of_lt ht1
  have h1tt : (1 : ℝ≥0∞) - t ≠ ⊤ := (tsub_le_self.trans_lt ENNReal.one_lt_top).ne
  have hρ'ge : 1 - t ≤ ρ' := by rw [hρ'def]; exact le_add_self
  have hρ'top : ρ' ≠ ⊤ := by
    rw [hρ'def]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ht1'
      ((tsub_le_self.trans (Kernel.convergenceNorm_le_one (κ := Kernel.ofMatrix P))).trans_lt
        ENNReal.one_lt_top).ne, h1tt⟩
  -- Trivial degenerate case: `L - δ = 0`, handled by the single `k = 0` term.
  rcases eq_or_ne (L - δ) 0 with hLδ0 | hLδ0
  · have hρ'eq : ρ' = 1 - t := by rw [hρ'def, hLδ0, mul_zero, zero_add]
    refine eventually_atTop.2 ⟨0, fun n _ ↦ ?_⟩
    have hterm0 : (n.choose 0 : ℝ≥0∞) * t ^ 0 * (1 - t) ^ (n - 0) * (Kernel.ofMatrix P ^ 0) x {x}
        = (1 - t) ^ n := by
      rw [Kernel.pow_zero_apply_singleton]
      simp
    have hone : (Kernel.ofMatrix (lazy P t) ^ n) x {x} ≥ (1 - t) ^ n := by
      rw [ofMatrix_lazy_pow_apply_singleton, ← hterm0]
      exact Finset.single_le_sum (f := fun k ↦ (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
          * (Kernel.ofMatrix P ^ k) x {x}) (fun k _ ↦ by positivity) (Finset.mem_range.2 (by omega))
    calc (ρ' - ε) ^ n ≤ (1 - t) ^ n := by
          rw [hρ'eq]; exact pow_le_pow_left' tsub_le_self n
      _ ≤ _ := hone
  -- Main case: `L - δ ≠ 0`, i.e. `δ < L`.
  have hδL : δ < L := by
    by_contra h; push Not at h; exact hLδ0 (tsub_eq_zero_of_le h)
  have hLpos : 0 < L := lt_of_le_of_lt bot_le hδL
  have hLne : L ≠ ⊤ := (Kernel.convergenceNorm_le_one (κ := Kernel.ofMatrix P)).trans_lt
    ENNReal.one_lt_top |>.ne
  have hLδltL : L - δ < L := ENNReal.sub_lt_self hLne hLpos.ne' hδ0.ne'
  have hρ'gt : 1 - t < ρ' := by
    rw [hρ'def]
    have : 0 < t * (L - δ) := ENNReal.mul_pos ht0 (tsub_pos_iff_lt.2 hδL).ne'
    calc (1 - t : ℝ≥0∞) = 0 + (1 - t) := (zero_add _).symm
      _ < t * (L - δ) + (1 - t) := by gcongr
  have hρ'pos : 0 < ρ' := h1t0.trans_le hρ'ge
  -- eventually `(L - δ)^k < a_k`, via genuine tendsto (Fekete, uses positivity of `P`).
  have hpos' : ∀ a b : E, 0 < (Kernel.ofMatrix P a) {b} := fun a b ↦ by
    rw [Kernel.ofMatrix_apply_singleton]; exact hpos a b
  have htend := Kernel.tendsto_convergenceNorm_of_forall_pos hpos' x
  have hev1 : ∀ᶠ k : ℕ in atTop, L - δ < ((Kernel.ofMatrix P ^ k) x {x}) ^ ((k : ℝ)⁻¹) :=
    (tendsto_order.1 htend).1 (L - δ) hLδltL
  have hev2 : ∀ᶠ k : ℕ in atTop, (L - δ) ^ k < (Kernel.ofMatrix P ^ k) x {x} := by
    filter_upwards [hev1, eventually_ge_atTop 1] with k hk hk1
    have := (ENNReal.lt_rpow_inv_iff (Nat.cast_pos.2 hk1)).1 hk
    rwa [ENNReal.rpow_natCast] at this
  obtain ⟨k1, hk1⟩ := eventually_atTop.1 hev2
  -- Ratio for the junk terms.
  have hr''1 : 1 - t < ρ' := hρ'gt
  have hr'' : 1 < ρ' / (1 - t) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl h1t0.ne') (Or.inl h1tt)).2 (by rw [one_mul]; exact hr''1)
  set r'' := ρ' / (1 - t) with hr''def
  have hr''eq : r'' * (1 - t) = ρ' := ENNReal.div_mul_cancel h1t0.ne' h1tt
  have hCk1 : ((1 - t) ^ k1 : ℝ≥0∞) ≠ 0 := pow_ne_zero k1 h1t0.ne'
  have hCk1t : ((1 - t) ^ k1 : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top h1tt
  set C' := (k1 : ℝ≥0∞) * ((1 - t) ^ k1)⁻¹ with hC'def
  have hC'top : C' ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.2 hCk1)
  have hjunk'_eq : ∀ n : ℕ, k1 ≤ n → (1 - t) ^ (n - k1) = (1 - t) ^ n * ((1 - t) ^ k1)⁻¹ := by
    intro n hn
    have hpa : (1 - t) ^ (n - k1) * (1 - t) ^ k1 = (1 - t) ^ n := by
      rw [← pow_add]; congr 1; omega
    rw [← hpa, mul_assoc, ENNReal.mul_inv_cancel hCk1 hCk1t, mul_one]
  have hev2C' : ∀ᶠ n : ℕ in atTop, 2 * C' ≤ (n : ℝ≥0∞) := by
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.mul_ne_top (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hC'top)
    exact eventually_atTop.2 ⟨N, fun n hn ↦ hN.le.trans (by exact_mod_cast hn)⟩
  have hevcore' : ∀ᶠ n : ℕ in atTop, (n : ℝ≥0∞) ^ (k1 + 1) ≤ r'' ^ n :=
    ENNReal.eventually_pow_le_pow_of_one_lt hr'' (k1 + 1)
  have hevk1 : ∀ᶠ n : ℕ in atTop, k1 ≤ n := eventually_ge_atTop k1
  have hbulk_ratio' : ∀ᶠ n : ℕ in atTop, 2 * (ρ' - ε) ^ n ≤ ρ' ^ n := by
    have hratio : (ρ' - ε) / ρ' < 1 :=
      (ENNReal.div_lt_iff (Or.inl hρ'pos.ne') (Or.inl hρ'top)).2 (by
        rw [one_mul]; exact ENNReal.sub_lt_self hρ'top hρ'pos.ne' hε0.ne')
    have heq : ρ' - ε = (ρ' - ε) / ρ' * ρ' := (ENNReal.div_mul_cancel hρ'pos.ne' hρ'top).symm
    have hpow : ∀ n : ℕ, (ρ' - ε) ^ n = ((ρ' - ε) / ρ') ^ n * ρ' ^ n := fun n ↦ by
      rw [← mul_pow, ← heq]
    have htwohalf : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      rw [ENNReal.mul_div_cancel' (by norm_num) (by norm_num)]
    have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
    have hev : ∀ᶠ n : ℕ in atTop, ((ρ' - ε) / ρ') ^ n < 1 / 2 :=
      (tendsto_order.1 htend).2 _ (by norm_num)
    filter_upwards [hev] with n hn
    rw [hpow n, ← mul_assoc]
    calc 2 * ((ρ' - ε) / ρ') ^ n * ρ' ^ n
        ≤ 1 * ρ' ^ n := by
          gcongr
          calc 2 * ((ρ' - ε) / ρ') ^ n ≤ 2 * (1 / 2) := by gcongr
            _ = 1 := htwohalf
      _ = ρ' ^ n := one_mul _
  filter_upwards [hbulk_ratio', hev2C', hevcore', hevk1] with n hbulk h2C hcore hk1n
  rw [ofMatrix_lazy_pow_apply_singleton]
  set F : ℕ → ℝ≥0∞ := fun k ↦
    (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) x {x} with hFdef
  set G : ℕ → ℝ≥0∞ := fun k ↦
    (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (L - δ) ^ k with hGdef
  have hsplitG : ∑ k ∈ Finset.range (n + 1), G k
      = (∑ k ∈ Finset.range k1, G k) + (∑ k ∈ Finset.Ico k1 (n + 1), G k) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive G (Nat.zero_le k1) (by omega)).symm
  have hGeq : ∑ k ∈ Finset.range (n + 1), G k = ρ' ^ n := by
    rw [hGdef, hρ'def, add_pow (t * (L - δ)) (1 - t) n]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]; ring
  -- Junk' bound (identical shape to the upper-bound proof).
  have hjunk'_term : ∀ k ∈ Finset.range k1, G k ≤ (n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1) := by
    intro k hk
    have hk' : k < k1 := Finset.mem_range.1 hk
    have hnpos : 1 ≤ n := by omega
    have h1 : (n.choose k : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ k1 := by
      calc (n.choose k : ℝ≥0∞) ≤ (n : ℝ≥0∞) ^ k := by exact_mod_cast Nat.choose_le_pow n k
        _ ≤ (n : ℝ≥0∞) ^ k1 := pow_le_pow_right₀ (by exact_mod_cast hnpos) hk'.le
    have h2 : (1 - t) ^ (n - k) ≤ (1 - t) ^ (n - k1) :=
      pow_le_pow_of_le_one bot_le tsub_le_self (by omega)
    have hLδ1 : (L - δ) ^ k ≤ 1 := pow_le_one₀ bot_le
      (tsub_le_self.trans (Kernel.convergenceNorm_le_one (κ := Kernel.ofMatrix P)))
    calc G k = (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (L - δ) ^ k := rfl
      _ ≤ (n : ℝ≥0∞) ^ k1 * 1 * (1 - t) ^ (n - k1) * 1 := by
          gcongr
          exact pow_le_one₀ bot_le ht1.le
      _ = (n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1) := by ring
  have hjunk'_sum : (∑ k ∈ Finset.range k1, G k) ≤ (k1 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1)) := by
    calc (∑ k ∈ Finset.range k1, G k) ≤ ∑ k ∈ Finset.range k1, (n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1) :=
          Finset.sum_le_sum hjunk'_term
      _ = (k1 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hjunk'_C : (k1 : ℝ≥0∞) * ((n : ℝ≥0∞) ^ k1 * (1 - t) ^ (n - k1))
      = C' * (n : ℝ≥0∞) ^ k1 * (1 - t) ^ n := by
    rw [hjunk'_eq n hk1n, hC'def]; ring
  have hjunk'2 : 2 * (∑ k ∈ Finset.range k1, G k) ≤ ρ' ^ n := by
    calc 2 * (∑ k ∈ Finset.range k1, G k)
        ≤ 2 * (C' * (n : ℝ≥0∞) ^ k1 * (1 - t) ^ n) := by
          rw [← hjunk'_C]; gcongr
      _ = ((n : ℝ≥0∞) ^ k1 * (2 * C')) * (1 - t) ^ n := by ring
      _ ≤ ((n : ℝ≥0∞) ^ k1 * (n : ℝ≥0∞)) * (1 - t) ^ n := by gcongr
      _ = (n : ℝ≥0∞) ^ (k1 + 1) * (1 - t) ^ n := by rw [pow_succ]
      _ ≤ r'' ^ n * (1 - t) ^ n := by gcongr
      _ = (r'' * (1 - t)) ^ n := (mul_pow r'' (1 - t) n).symm
      _ = ρ' ^ n := by rw [hr''eq]
  have hbulk_term : ∀ k ∈ Finset.Ico k1 (n + 1), G k ≤ F k := by
    intro k hk
    have hk' : k1 ≤ k := (Finset.mem_Ico.1 hk).1
    have hpow : (L - δ) ^ k ≤ (Kernel.ofMatrix P ^ k) x {x} := (hk1 k hk').le
    calc G k = (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (L - δ) ^ k := rfl
      _ ≤ (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) x {x} := by gcongr
      _ = F k := rfl
  have hbulk_lower : (∑ k ∈ Finset.Ico k1 (n + 1), G k) ≤ ∑ k ∈ Finset.Ico k1 (n + 1), F k :=
    Finset.sum_le_sum hbulk_term
  have hcancel : (∑ k ∈ Finset.range k1, G k) + (ρ' - ε) ^ n ≤ ρ' ^ n :=
    ENNReal_add_le_of_two_mul_le_of_two_mul_le hjunk'2 hbulk
  have hGrange_ne_top : (∑ k ∈ Finset.range k1, G k) ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.2 fun k _ ↦ ?_).ne
    have h1 : (n.choose k : ℝ≥0∞) ≠ ⊤ := by simp
    have h2 : (t ^ k : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ht1'
    have h3 : ((1 - t) ^ (n - k) : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top h1tt
    have h4 : ((L - δ) ^ k : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top
      (tsub_le_self.trans (Kernel.convergenceNorm_le_one (κ := Kernel.ofMatrix P)) |>.trans_lt
        ENNReal.one_lt_top).ne
    rw [hGdef]
    exact (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h1 h2) h3) h4).lt_top
  have hkey : (ρ' - ε) ^ n ≤ ρ' ^ n - (∑ k ∈ Finset.range k1, G k) :=
    ENNReal.le_sub_of_add_le_left hGrange_ne_top hcancel
  have hGsplit_le : ρ' ^ n - (∑ k ∈ Finset.range k1, G k) ≤ ∑ k ∈ Finset.Ico k1 (n + 1), G k := by
    rw [← hGeq, hsplitG, ENNReal.add_sub_cancel_left hGrange_ne_top]
  calc (ρ' - ε) ^ n ≤ ρ' ^ n - (∑ k ∈ Finset.range k1, G k) := hkey
    _ ≤ ∑ k ∈ Finset.Ico k1 (n + 1), G k := hGsplit_le
    _ ≤ ∑ k ∈ Finset.Ico k1 (n + 1), F k := hbulk_lower
    _ ≤ ∑ k ∈ Finset.range (n + 1), F k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk; rw [Finset.mem_Ico] at hk; exact Finset.mem_range.2 hk.2
        · intro k _ _; positivity


theorem ENNReal_sub_add_sub_eq {a b c : ℝ≥0∞} (hb : b ≠ ⊤) (h1 : b ≤ a) (h2 : a ≤ c) :
    (a - b) + (c - a) = c - b := by
  have hsum : (a - b) + (c - a) + b = c := by
    rw [add_right_comm, tsub_add_cancel_of_le h1, add_tsub_cancel_of_le h2]
  exact ENNReal.eq_sub_of_add_eq hb hsum

open Filter Topology ProbabilityTheory in
/-- If `L(P) = 1`, then `L(lazy P t) ≥ 1`, hence (combined with `lazy_convergenceNorm_le`,
which gives `≤ 1` when `L(P) = 1`) `L(lazy P t) = 1`. -/
theorem one_le_lazy_convergenceNorm_of_convergenceNorm_eq_one {E : Type*} [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E)
    (hL1 : Kernel.convergenceNorm (Kernel.ofMatrix P) x = 1) :
    1 ≤ Kernel.convergenceNorm (Kernel.ofMatrix (lazy P t)) x := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  set ε0 := 1 - a with hε0def
  have hε0pos : 0 < ε0 := tsub_pos_of_lt ha
  have hε0le1 : ε0 ≤ 1 := tsub_le_self
  set δ := ε0 / 2 with hδdef
  have hδpos : 0 < δ := ENNReal.div_pos hε0pos.ne' (by norm_num)
  have hkey := eventually_le_lazy_pow_of_lt_convergenceNorm hpos hP ht0 ht1 x
    (δ := δ) (ε := δ) hδpos hδpos
  rw [hL1] at hkey
  have hδle1 : δ ≤ 1 := ENNReal.half_le_self.trans hε0le1
  have hδtop : δ ≠ ⊤ := (hδle1.trans_lt ENNReal.one_lt_top).ne
  have htδt : t * δ ≤ t := by
    calc t * δ ≤ t * 1 := by gcongr
      _ = t := mul_one _
  have htδδ : t * δ ≤ δ := by
    calc t * δ ≤ 1 * δ := by gcongr
      _ = δ := one_mul _
  have htδtop : t * δ ≠ ⊤ := ENNReal.mul_ne_top ht1.ne_top hδtop
  have hmul : t * (1 - δ) = t - t * δ := by
    rw [ENNReal.mul_sub (fun _ _ ↦ ht1.ne_top), mul_one]
  have hident : t * (1 - δ) + (1 - t) = 1 - t * δ := by
    rw [hmul]
    exact ENNReal_sub_add_sub_eq htδtop htδt ht1.le
  have htarget_ge : a ≤ t * (1 - δ) + (1 - t) - δ := by
    rw [hident, tsub_tsub]
    have h2δ : t * δ + δ ≤ ε0 := by
      calc t * δ + δ ≤ δ + δ := by gcongr
        _ = ε0 := by rw [hδdef, ENNReal.add_halves]
    calc a = 1 - (1 - a) := (ENNReal.sub_sub_cancel (by norm_num) ha.le).symm
      _ = 1 - ε0 := by rw [hε0def]
      _ ≤ 1 - (t * δ + δ) := tsub_le_tsub_left h2δ 1
  refine Kernel.le_convergenceNorm_of_frequently (Filter.Eventually.frequently (hkey.mono fun n hn ↦ ?_))
  calc a ^ n ≤ (t * (1 - δ) + (1 - t) - δ) ^ n := by gcongr
    _ ≤ _ := hn

theorem lazy_convergenceNorm_eq_one_of_convergenceNorm_eq_one {E : Type*} [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E)
    (hL1 : Kernel.convergenceNorm (Kernel.ofMatrix P) x = 1) :
    Kernel.convergenceNorm (Kernel.ofMatrix (lazy P t)) x = 1 := by
  refine le_antisymm ?_ (one_le_lazy_convergenceNorm_of_convergenceNorm_eq_one hpos hP ht0 ht1 x hL1)
  have := lazy_convergenceNorm_le (P := P) hP ht0 ht1 x
  rwa [hL1, mul_one, add_tsub_cancel_of_le ht1.le] at this

open ProbabilityTheory in
/-- If an invariant probability measure of `Q = lazy P t` exists, its restriction gives one for
`P` too: `μ Q = μ` forces `μ P = μ`, since `Q = tP + (1-t)I` and `t ≠ 0`. -/
theorem isPositiveRecurrent_ofMatrix_of_isPositiveRecurrent_lazy {E : Type*} [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1)
    (hpos : ∀ x y, 0 < P x y)
    (hposrecQ : ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix (lazy P t))) :
    ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P) := by
  obtain ⟨hrecQ, μ, hμprob, hμinvQ⟩ := hposrecQ
  have hkey : ∀ b : E, ∑' a, μ {a} * P a b = μ {b} := by
    intro b
    have h1 : μ {b} = ∑' a, (Kernel.ofMatrix (lazy P t)) a {b} * μ {a} :=
      hμinvQ.apply_singleton_eq_tsum b
    simp only [Kernel.ofMatrix_apply_singleton, lazy] at h1
    have h2 : ∑' a, (t * P a b + (1 - t) * ({b} : Set E).indicator (1 : E → ℝ≥0∞) a) * μ {a}
        = t * (∑' a, P a b * μ {a}) + (1 - t) * μ {b} := by
      have hstep : ∀ a, (t * P a b + (1 - t) * ({b} : Set E).indicator (1 : E → ℝ≥0∞) a) * μ {a}
          = t * (P a b * μ {a}) + (1 - t) * (({b} : Set E).indicator (1 : E → ℝ≥0∞) a * μ {a}) := by
        intro a; ring
      simp_rw [hstep]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      congr 2
      rw [tsum_eq_single b (fun a ha ↦ by simp [Set.indicator_of_notMem, ha])]
      simp
    rw [h2] at h1
    have h3 : t * μ {b} = t * (∑' a, P a b * μ {a}) := by
      have hne : (1 - t) * μ {b} ≠ ⊤ :=
        ENNReal.mul_ne_top (tsub_le_self.trans_lt ENNReal.one_lt_top).ne (measure_ne_top μ _)
      have h4 : (1 - t) * μ {b} + t * μ {b} = (1 - t) * μ {b} + t * (∑' a, P a b * μ {a}) := by
        calc (1 - t) * μ {b} + t * μ {b} = μ {b} := by
              rw [← add_mul, tsub_add_cancel_of_le ht1.le, one_mul]
          _ = t * (∑' a, P a b * μ {a}) + (1 - t) * μ {b} := h1
          _ = (1 - t) * μ {b} + t * (∑' a, P a b * μ {a}) := by ring
      exact (ENNReal.add_right_inj hne).1 h4
    have h5 : μ {b} = ∑' a, P a b * μ {a} := (ENNReal.mul_right_inj ht0 ht1.ne_top).1 h3
    rw [h5]
    exact tsum_congr fun a ↦ mul_comm _ _
  have hinvP : (Kernel.ofMatrix P).Invariant μ :=
    Measure.ext_of_singleton fun b ↦ by
      rw [Kernel.bind_ofMatrix_apply_singleton]; exact hkey b
  have hMP : ProbabilityTheory.IsMarkovKernel (Kernel.ofMatrix P) := Kernel.isMarkovKernel_ofMatrix P hP
  have hirr : ProbabilityTheory.Kernel.IsIrreducible (Measure.count : Measure E) (Kernel.ofMatrix P) :=
    Kernel.isIrreducible_count_ofMatrix_of_forall_pos hpos
  exact ⟨Kernel.isRecurrent_of_invariant hinvP, μ, hμprob, hinvP⟩

open ProbabilityTheory in
/-- **Georgii Comment (11.18)(3), non-existence half.** For `Q = tP + (1-t)I` with `0 < t < 1`
and `P` a positive stochastic matrix with `L(P) = 1` which is not positive recurrent (i.e. `P` is
null recurrent or transient), `𝒢(γ^Q) = ∅`. -/
theorem eq_empty_G_lazy_of_not_isPositiveRecurrent {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] [Nonempty E] {P : E → E → ℝ≥0∞} {t : ℝ≥0∞}
    (hpos : ∀ x y, 0 < P x y) (hP : ∀ x, ∑' y, P x y = 1) (ht0 : t ≠ 0) (ht1 : t < 1) (x : E)
    (hL1 : Kernel.convergenceNorm (Kernel.ofMatrix P) x = 1)
    (hnotpos : ¬ ProbabilityTheory.Kernel.IsPositiveRecurrent (Kernel.ofMatrix P)) :
    G (transferSpecification (lazy P t) (lazy_isTransferMatrix hpos hP ht0 ht1)) = ∅ := by
  have hQ := lazy_isTransferMatrix hpos hP ht0 ht1
  have hnotequiv : ¬ ∃ (R : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, R x y = lazy P t x y * r y / (q * r x)) ∧
      (∀ x, ∑' y, R x y = 1) ∧ Kernel.IsPositiveRecurrent (Kernel.ofMatrix R) := by
    rintro ⟨R, q, r, hq0, hqt, hr0, hrt, hRQ, hRstoch, hRposrec⟩
    have hRpos : ∀ x y, 0 < R x y := fun x y ↦ by
      rw [hRQ]
      exact ENNReal.div_pos (ENNReal.mul_pos (hQ.pos x y).ne' (hr0 y).ne').ne'
        (ENNReal.mul_ne_top hqt (hrt x))
    have hRirr : Kernel.IsIrreducible (Measure.count : Measure E) (Kernel.ofMatrix R) :=
      Kernel.isIrreducible_count_ofMatrix_of_forall_pos hRpos
    have hMR : IsMarkovKernel (Kernel.ofMatrix R) := Kernel.isMarkovKernel_ofMatrix R hRstoch
    have hMQ : IsMarkovKernel (Kernel.ofMatrix (lazy P t)) :=
      Kernel.isMarkovKernel_ofMatrix _ (lazy_stochastic hP ht1.le)
    have hLQ1 : Kernel.convergenceNorm (Kernel.ofMatrix (lazy P t)) x = 1 :=
      lazy_convergenceNorm_eq_one_of_convergenceNorm_eq_one hpos hP ht0 ht1 x hL1
    have hRQ' : ∀ x y, (Kernel.ofMatrix R) x {y}
        = (Kernel.ofMatrix (lazy P t)) x {y} * r y / (q * r x) := fun x y ↦ by
      rw [Kernel.ofMatrix_apply_singleton, Kernel.ofMatrix_apply_singleton]; exact hRQ x y
    have hposrecQ : Kernel.IsPositiveRecurrent (Kernel.ofMatrix (lazy P t)) :=
      Kernel.isPositiveRecurrent_of_apply_eq_mul_div hq0.ne' hqt (fun x ↦ (hr0 x).ne') hrt hRQ' hLQ1 hRposrec
    exact hnotpos (isPositiveRecurrent_ofMatrix_of_isPositiveRecurrent_lazy hP ht0 ht1 hpos hposrecQ)
  refine eq_empty_G_of_forall_le_sum (lazy P t) hQ hnotequiv (N := 1) one_pos
    (ε := 1 - t) (tsub_pos_of_lt ht1) fun y ↦ ?_
  rw [Finset.Icc_self, Finset.sum_singleton, pow_one, Kernel.ofMatrix_apply_singleton]
  exact le_lazy_apply_self y


end MeasureTheory.GibbsMeasure.Markov

end

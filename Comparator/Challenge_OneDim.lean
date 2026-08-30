import Comparator.Defs_OneDim

/-!
# Comparator challenge: uniqueness in one dimension (Georgii, Section 8.3)

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Proposition (8.38), Theorem (8.39) and
Comments (8.41).

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_OneDim`, whose transitive imports are `Comparator.Defs` and
`Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library whose
theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `outside`, `tail`,
`IsSpecification`, `IsGibbs`, `IsLocalEvent`, …) is defined in `Comparator/Defs.lean`, and
Georgii's Section 8.3 (`osc`, `IsPotential`, `hamiltonian`, `gibbsKernel`, `IsUniformlyDominated`,
`oscSpan`, `HasBoundedBoundary`, …) in `Comparator/Defs_OneDim.lean`; both module docstrings
contain the dictionary.

## What is and is not claimed

* Proposition (8.38) is stated for an **arbitrary** specification on an arbitrary countable
  parameter set — that is the general theorem, and the reusable one.
* Theorem (8.39), **first half** (`|𝓖(Φ)| ≤ 1`), is stated at Georgii's own hypotheses: a
  potential in the sense of Definition (2.2) — summable in the sense of Convention (2.1), **not**
  absolutely summable — over an arbitrary σ-finite non-zero `λ`-admissible a priori measure.
* Theorem (8.39), **second half** (`|𝓖(Φ)| = 1`), needs existence, i.e. Theorem (4.23)(a), which
  is available only for an absolutely summable potential over a probability a priori measure and a
  standard Borel state space.  It is stated at exactly those hypotheses and no weaker ones.
* Comment (8.41)(2) is the headline application: uniqueness for pair interactions decaying like
  `n^{-p}` with `p > 2`, far past nearest-neighbour.  Nothing is claimed for `p ≤ 2`, where
  Georgii records that a phase transition can occur.

## Main statements

* `subsingleton_isGibbs_of_isUniformlyDominated`: **Georgii, Proposition (8.38)**.
* `exists_isSpecification_isUniformlyDominated`: a witness that the hypothesis of (8.38) is
  realized by a genuine specification.
* `hasBoundedBoundary_int`, `hasBoundedBoundary_nat`: the chain structures of `ℤ` and `ℕ`;
  witnesses that the hypothesis of (8.39) is non-empty.
* `subsingleton_isGibbs_of_iSup_oscSpan_ne_top`: **Georgii, Theorem (8.39)**, first half.
* `existsUnique_isGibbs_of_iSup_oscSpan_ne_top`: **Georgii, Theorem (8.39)**, second half.
* `subsingleton_isGibbs_of_pair_rpow_le`, `existsUnique_isGibbs_of_pair_rpow_le`: **Georgii,
  Comment (8.41)(2)**.
* `exists_potential_of_forall_hypotheses`: a witness that all of the above hypotheses are jointly
  satisfiable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace OneDimChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## The theorems -/

/-- **Georgii, Proposition (8.38).** Let `γ` be *any* specification.  If there is a constant
`c > 0` such that every cylinder event `A` admits a finite volume `Λ` with
`γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all boundary conditions `ζ, η`, then `|𝓖(γ)| ≤ 1`.

No structure whatsoever is assumed on the parameter set beyond countability: this is the general
uniqueness criterion from which the one-dimensional Theorem (8.39) is deduced. -/
theorem subsingleton_isGibbs_of_isUniformlyDominated [Countable S]
    (γ : Finset S → Config S E → Measure (Config S E)) (hγ : IsSpecification γ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hdom : IsUniformlyDominated γ c) :
    {μ : Measure (Config S E) | IsGibbs γ μ}.Subsingleton := by
  sorry

/-- **Non-vacuity of Proposition (8.38).** Its hypothesis is realized by a genuine specification:
the Gibbsian specification of the zero potential over a probability a priori measure — the
*independent* specification, which resamples the spins inside `Λ` from `λ` — is uniformly
dominated with the constant `c = 1`.  For a `Δ`-local event `A` the volume `Δ` itself works, since
`γ_Δ(A|ω)` then does not depend on the boundary condition `ω` at all. -/
theorem exists_isSpecification_isUniformlyDominated (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    ∃ γ : Finset ℤ → Config ℤ E → Measure (Config ℤ E),
      IsSpecification γ ∧ IsUniformlyDominated γ 1 ∧
      ∀ (Λ : Finset ℤ) (ω : Config ℤ E), γ Λ ω = freeMeasure lam Λ ω := by
  sorry

/-- **Georgii's chain structure for `S = ℤ`.** The integers are exhausted by the intervals
`]−n, n]`, each of which has the two boundary sites `−n` and `n`.  This is a *witness* that the
hypothesis `HasBoundedBoundary` of Theorem (8.39) below is not empty. -/
theorem hasBoundedBoundary_int : HasBoundedBoundary ℤ 2 := by
  sorry

/-- **Georgii's chain structure for `S = ℕ`.** The natural numbers are exhausted by the intervals
`[0, n]`, each of which has the single boundary site `n`.  This is a second *witness* that the
hypothesis `HasBoundedBoundary` of Theorem (8.39) below is not empty. -/
theorem hasBoundedBoundary_nat : HasBoundedBoundary ℕ 1 := by
  sorry

/-- **Georgii, Theorem (8.39), first half**, at Georgii's own hypotheses: `S` carries a chain
structure (`HasBoundedBoundary`, satisfied by `ℤ` with `m = 2` and by `ℕ` with `m = 1`), `Φ` is a
potential in the sense of Definition (2.2) — merely summable in the sense of Convention (2.1), and
*not* assumed absolutely summable — `λ` is an arbitrary σ-finite non-zero a priori measure for
which `Φ` is `λ`-admissible, and condition (8.40) holds:
`sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞`.  Then `|𝓖(Φ)| ≤ 1`. -/
theorem subsingleton_isGibbs_of_iSup_oscSpan_ne_top [Countable S] [Preorder S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    (Φ : Finset S → Config S E → ℝ) (hΦ : IsPotential Φ)
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hadm : IsAdmissible Φ lam β) (h840 : (⨆ i : S, oscSpan Φ i) ≠ ⊤) :
    {μ : Measure (Config S E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  sorry

/-- **Georgii, Theorem (8.39), second half.** Existence rests on Theorem (4.23)(a), which is
available only for an absolutely summable potential over a *finite* a priori measure and a
standard Borel state space; the statement is made at exactly those hypotheses and no weaker ones.
Under them, and under condition (8.40), the potential has *exactly one* Gibbs measure. -/
theorem existsUnique_isGibbs_of_iSup_oscSpan_ne_top [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : (⨆ i : ℤ, oscSpan Φ i) ≠ ⊤) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  sorry

/-- **Georgii, Comment (8.41)(2): uniqueness far past nearest-neighbour interactions.** A
shift-invariant pair potential on `ℤ` whose two-point oscillations decay as
`δ(Φ_{{0,n}}) ≤ c n^{-p}` with `p > 2` has at most one Gibbs measure.  (Georgii's model case is
`Φ_{{i,j}} = |i − j|^{-p} φ(σ_i, σ_j)` with `φ` bounded, for which `δ(Φ_{{0,n}}) = n^{-p} δ(φ)`.)

The hypotheses are stated as conditions on the oscillations alone, so no relation between `Φ` and
a particular `φ` is presumed. -/
theorem subsingleton_isGibbs_of_pair_rpow_le
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    {μ : Measure (Config ℤ E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  sorry

/-- **The capstone.** Over a standard Borel state space, a shift-invariant absolutely summable
pair potential on `ℤ` with `δ(Φ_{{0,n}}) ≤ c n^{-p}` and `p > 2` has *exactly one* Gibbs measure:
Georgii's Theorem (8.39) together with Comment (8.41)(2) and the existence Theorem (4.23)(a). -/
theorem existsUnique_isGibbs_of_pair_rpow_le [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  sorry

/-- **Non-vacuity.** The hypotheses assembled above are jointly satisfiable: the zero potential is
a potential in the sense of Definition (2.2), is absolutely summable, is `λ`-admissible over any
probability a priori measure, satisfies condition (8.40), and satisfies the shift-invariance,
pair and decay hypotheses of Comment (8.41)(2).  Its Gibbsian specification is the *independent*
specification `λ_Λ(·|ω)`, not a degenerate one. -/
theorem exists_potential_of_forall_hypotheses (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    ∃ Φ : Finset ℤ → Config ℤ E → ℝ,
      IsPotential Φ ∧ IsAbsolutelySummable Φ ∧ IsAdmissible Φ lam β ∧
      (⨆ i : ℤ, oscSpan Φ i) ≠ ⊤ ∧
      (∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A)) ∧
      (∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0) ∧
      (∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (1 * (n : ℝ) ^ (-(3 : ℝ)))) ∧
      ∀ (Λ : Finset ℤ) (ω : Config ℤ E), gibbsKernel Φ lam β Λ ω = freeMeasure lam Λ ω := by
  sorry

end OneDimChallenge

end

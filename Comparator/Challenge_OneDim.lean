import Comparator.Defs_OneDim

/-!
# Comparator challenge: uniqueness in one dimension (Georgii, Section 8.3)

Georgii's Proposition (8.38), Theorem (8.39) and Comments (8.41).

Proposition (8.38) is stated for an arbitrary specification on an arbitrary countable parameter
set.  The first half of Theorem (8.39) is stated at Georgii's own hypotheses: a potential in the
sense of Definition (2.2) — summable in the sense of Convention (2.1), *not* absolutely summable —
over an arbitrary σ-finite non-zero `λ`-admissible a priori measure.  The second half needs
existence, i.e. Theorem (4.23)(a), available only for an absolutely summable potential over a
probability a priori measure on a standard Borel state space, and is stated at exactly those
hypotheses.  Nothing is claimed for the pair decay exponent `p ≤ 2`, where Georgii records that a
phase transition can occur.

## Main statements

* `subsingleton_isGibbs_of_isUniformlyDominated`: Proposition (8.38)
* `hasBoundedBoundary_int`, `hasBoundedBoundary_nat`: the chain structures of `ℤ` and `ℕ`
* `subsingleton_isGibbs_of_iSup_oscSpan_ne_top`: Theorem (8.39), first half
* `existsUnique_isGibbs_of_iSup_oscSpan_ne_top`: Theorem (8.39), second half
* `subsingleton_isGibbs_of_pair_rpow_le`, `existsUnique_isGibbs_of_pair_rpow_le`: Comment (8.41)(2)
* `exists_isSpecification_isUniformlyDominated`, `exists_potential_of_forall_hypotheses`:
  witnesses that the hypotheses above are jointly satisfiable

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Section 8.3
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

/-- **Georgii, Proposition (8.38)**: a specification `γ` for which every cylinder event `A` admits
a volume `Λ` with `γ_Λ(A|ζ) ≥ c γ_Λ(A|η)` for all `ζ, η` and some `c > 0` has at most one Gibbs
measure.  Nothing beyond countability is assumed of the parameter set. -/
theorem subsingleton_isGibbs_of_isUniformlyDominated [Countable S]
    (γ : Finset S → Config S E → Measure (Config S E)) (hγ : IsSpecification γ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hdom : IsUniformlyDominated γ c) :
    {μ : Measure (Config S E) | IsGibbs γ μ}.Subsingleton := by
  sorry

/-- Non-vacuity of Proposition (8.38): the independent specification is a genuine specification
satisfying its hypothesis with `c = 1`. -/
theorem exists_isSpecification_isUniformlyDominated (lam : Measure E) [IsProbabilityMeasure lam]
    (β : ℝ) :
    ∃ γ : Finset ℤ → Config ℤ E → Measure (Config ℤ E),
      IsSpecification γ ∧ IsUniformlyDominated γ 1 ∧
      ∀ (Λ : Finset ℤ) (ω : Config ℤ E), γ Λ ω = freeMeasure lam Λ ω := by
  sorry

/-- The integers are exhausted by the intervals `]−n, n]`, each with the two boundary sites `−n`
and `n`. -/
theorem hasBoundedBoundary_int : HasBoundedBoundary ℤ 2 := by
  sorry

/-- The naturals are exhausted by the intervals `[0, n]`, each with the single boundary site
`n`. -/
theorem hasBoundedBoundary_nat : HasBoundedBoundary ℕ 1 := by
  sorry

/-- **Georgii, Theorem (8.39), first half**: on a parameter set with a chain structure, a
potential in the sense of Definition (2.2) — merely summable in the sense of Convention (2.1) —
that is `λ`-admissible over a σ-finite non-zero `λ` and satisfies condition (8.40)
`sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞` has at most one Gibbs measure. -/
theorem subsingleton_isGibbs_of_iSup_oscSpan_ne_top [Countable S] [Preorder S] {m : ℕ}
    (hexh : HasBoundedBoundary S m)
    (Φ : Finset S → Config S E → ℝ) (hΦ : IsPotential Φ)
    (lam : Measure E) [SigmaFinite lam] [NeZero lam] (β : ℝ)
    (hadm : IsAdmissible Φ lam β) (h840 : (⨆ i : S, oscSpan Φ i) ≠ ⊤) :
    {μ : Measure (Config S E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  sorry

/-- **Georgii, Theorem (8.39), second half**: under condition (8.40) the potential has exactly one
Gibbs measure.  Existence rests on Theorem (4.23)(a), available only for an absolutely summable
potential over a finite a priori measure on a standard Borel state space, so the statement is made
at exactly those hypotheses and no weaker ones. -/
theorem existsUnique_isGibbs_of_iSup_oscSpan_ne_top [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (h840 : (⨆ i : ℤ, oscSpan Φ i) ≠ ⊤) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  sorry

/-- **Georgii, Comment (8.41)(2)**: a shift-invariant pair potential on `ℤ` whose two-point
oscillations decay as `δ(Φ_{{0,n}}) ≤ c n^{-p}` with `p > 2` has at most one Gibbs measure.  The
hypotheses are conditions on the oscillations alone, so no relation between `Φ` and a particular
`φ` is presumed. -/
theorem subsingleton_isGibbs_of_pair_rpow_le
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    {μ : Measure (Config ℤ E) | IsGibbs (gibbsKernel Φ lam β) μ}.Subsingleton := by
  sorry

/-- **Georgii, Theorem (8.39) with Comment (8.41)(2)**: over a standard Borel state space, a
shift-invariant absolutely summable pair potential on `ℤ` with `δ(Φ_{{0,n}}) ≤ c n^{-p}` and
`p > 2` has exactly one Gibbs measure. -/
theorem existsUnique_isGibbs_of_pair_rpow_le [StandardBorelSpace E]
    (Φ : Finset ℤ → Config ℤ E → ℝ) (hΦ : IsPotential Φ) (habs : IsAbsolutelySummable Φ)
    (lam : Measure E) [IsProbabilityMeasure lam] (β : ℝ)
    (hshift : ∀ (n : ℤ) (A : Finset ℤ), osc (Φ (shiftFinset n A)) = osc (Φ A))
    (hpair : ∀ A : Finset ℤ, (∀ a b : ℤ, a < b → A ≠ {a, b}) → osc (Φ A) = 0)
    {c p : ℝ} (hp : 2 < p)
    (hbd : ∀ n : ℕ, 0 < n → osc (Φ {0, (n : ℤ)}) ≤ ENNReal.ofReal (c * (n : ℝ) ^ (-p))) :
    ∃! μ : Measure (Config ℤ E), IsGibbs (gibbsKernel Φ lam β) μ := by
  sorry

/-- Non-vacuity: the zero potential satisfies every hypothesis assembled above at once, and its
Gibbsian specification is the independent specification `λ_Λ(·|ω)`, not a degenerate one. -/
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

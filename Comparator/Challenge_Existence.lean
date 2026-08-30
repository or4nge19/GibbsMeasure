import Comparator.Defs_Existence

/-!
# Comparator challenge: existence and compactness of Gibbs measures (Georgii (4.22), (4.23))

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Theorem (4.22) and Theorem (4.23)(a),
(b).

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_Existence`, whose transitive imports are `Comparator.Defs` and
`Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library whose
theorems are being certified.  The Mathlib-only vocabulary (`Config`, `outside`, `tail`,
`IsSpecification`, `IsGibbs`, `localTopology`, …) is defined in `Comparator/Defs.lean` and the
absolutely summable potentials, the Hamiltonian and the Gibbsian specification in
`Comparator/Defs_Existence.lean`; both module docstrings contain the dictionary.

## The a priori measure

Georgii states Theorem (4.23) for an arbitrary **finite** a priori measure
`λ ∈ 𝓜(E, ℰ)` — a finite, non-zero, but *not* normalized single-spin measure — and his (2.14)
shows that this is exactly the right hypothesis: a potential `Φ ∈ ℬ` is `λ`-admissible if and only
if `λ` is finite.  Accordingly the hypothesis below is `[IsFiniteMeasure ν] [NeZero ν]`, which is
Georgii's `λ ∈ 𝓜(E, ℰ)` finite verbatim.

Nothing renormalizes `λ` behind the scenes: `partitionFunction` (Georgii (2.7)) is the integral of
the Boltzmann factor against the un-normalized `λ_Λ^ω`, whose total mass is `λ(E)^{|Λ|}` and not
`1` (`freeMeasure_univ`), and `gibbsKernel` (Georgii (2.9)) divides by that partition function.
The `λ(E)^{|Λ|}` occurring in the numerator and in the denominator therefore cancel, which is what
makes the un-normalized statement equivalent to the normalized one; that cancellation is recorded
in `Comparator/Defs_Existence.lean` as `gibbsKernel_apply`, `gibbsKernel_smul` and
`gibbsKernel_probNormalize`, and it is Georgii's Remark (1.28)(3).

## Main statements

* `isSpecification_gibbsKernel`: **Georgii (2.9)/(2.10)**, the family `γ^Φ` really is a
  specification in the sense of the preamble (proper Markov kernels from `𝓣_Λ`, consistent).
* `exists_isGibbs_gibbsKernel`: **Georgii Theorem (4.22)**, over a standard Borel state space and
  for an absolutely summable potential, `𝓖(γ^Φ) ≠ ∅`.
* `isCompact_setOf_isGibbs_gibbsKernel`: **Georgii Theorem (4.23)(a)**, `𝓖(γ^Φ)` is compact in the
  topology of local convergence.
* `exists_isCompact_superset_iUnion_setOf_isGibbs`: **Georgii Theorem (4.23)(b)**, for a family of
  absolutely summable potentials that is bounded in the sense `sup_i ‖Φ_i‖_a < ∞` for every site
  `a`, the union `⋃_i 𝒢(Φ_i)` is relatively compact in the topology of local convergence, i.e. it
  is contained in a locally compact set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## The theorems -/

/-- **Georgii (2.9)/(2.10).** The Gibbsian specification of an absolutely summable potential really
is a specification in the sense of the preamble: a consistent family of proper probability kernels
from the exterior σ-algebra `𝓣_Λ`.  The a priori measure is an arbitrary finite non-zero
`λ ∈ 𝓜(E, ℰ)`, as in Georgii's Definition (2.9); by (2.14) finiteness is exactly `λ`-admissibility
of `Φ ∈ ℬ`. -/
theorem isSpecification_gibbsKernel [Countable S] (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    IsSpecification (gibbsKernel Φ ν β) :=
  sorry

/-- **Georgii, Theorem (4.22).** Over a standard Borel state space, and for an absolutely summable
potential and a finite non-zero a priori measure, the set of Gibbs measures of the Gibbsian
specification is non-empty. -/
theorem exists_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    ∃ μ : Measure (Config S E), IsGibbs (gibbsKernel Φ ν β) μ :=
  sorry

/-- **Georgii, Theorem (4.23)(a).** For a standard Borel `(E, ℰ)` and a finite `λ ∈ 𝓜(E, ℰ)`, the
set of Gibbs measures of an absolutely summable potential is compact in the topology of local
convergence. -/
theorem isCompact_setOf_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology {μ | IsGibbs (gibbsKernel Φ ν β) μ} :=
  sorry

/-- **Georgii, Theorem (4.23)(b).** If a family `(Φ_i)` of absolutely summable potentials is
bounded in `ℬ`, i.e. `sup_i ‖Φ_i‖_a < ∞` for every site `a`, then the union of the corresponding
sets of Gibbs measures — taken with respect to one and the same finite `λ ∈ 𝓜(E, ℰ)` — is
relatively compact in the topology of local convergence: it is contained in a compact set of
probability measures. -/
theorem exists_isCompact_superset_iUnion_setOf_isGibbs [Countable S] [StandardBorelSpace E]
    {ι : Type*} (Φs : ι → Finset S → Config S E → ℝ)
    (hΦs : ∀ i, IsAbsolutelySummablePotential (Φs i))
    (hbdd : ∀ a : S, (⨆ i, potentialNormAt (Φs i) a) < ⊤)
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    ∃ K : Set (Measure (Config S E)), @IsCompact (Measure (Config S E)) localTopology K ∧
      (∀ μ ∈ K, IsProbabilityMeasure μ) ∧
      (⋃ i, {μ : Measure (Config S E) | IsGibbs (gibbsKernel (Φs i) ν β) μ}) ⊆ K :=
  sorry

end GibbsChallenge

end

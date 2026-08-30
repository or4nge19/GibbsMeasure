import Comparator.Defs_MarkovChain

/-!
# Comparator challenge: Markov chains as Gibbs measures on `ℤ` (Georgii, Theorem (3.5))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_MarkovChain`, whose transitive imports are `Comparator.Defs`
and `Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library
whose theorems are being certified.  The shared Mathlib-only vocabulary (`Config`,
`IsSpecification`, `IsGibbs`, …) is defined in `Comparator/Defs.lean`, and `determiningFun` and
`cylinder` in `Comparator/Defs_MarkovChain.lean`; both module docstrings contain the dictionary.

## Main statements

* `georgii_3_5_markovChain`: for a strictly positive stochastic matrix `P` on a finite state
  space `E`, **every** specification on `ℤ` whose singleton kernels are
  `γ_{i}(σ_i = y | ω) = P(ω_{i-1}, y) P(y, ω_{i+1}) / P²(ω_{i-1}, ω_{i+1})`
  has exactly one Gibbs measure, and that Gibbs measure is the stationary Markov chain: its
  cylinder probabilities are
  `μ(σ_a = x_a, …, σ_{a+n} = x_{a+n}) = α(x_a) P(x_a, x_{a+1}) ⋯ P(x_{a+n-1}, x_{a+n})`
  for the (strictly positive) stationary distribution `α` of `P`.
* `georgii_3_5_uniqueness`: the uniqueness half, packaged as `∃!`.
* `exists_isSpecification_determiningFun`: **non-vacuity**, a specification with the prescribed
  singleton kernels really exists, so the two theorems above are not statements about an empty
  class of specifications.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace MarkovChainChallenge

open GibbsChallenge

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [Nonempty E]

/-- **Georgii, Theorem (3.5).** Let `E` be a finite state space and `P` a stochastic matrix on `E`
with all entries strictly positive. Let `γ` be *any* specification on the parameter set `ℤ` whose
singleton kernels are given by Georgii's determining function (3.11),
`γ_{i}(σ_i = y | ω) = P(ω_{i-1}, y) P(y, ω_{i+1}) / P²(ω_{i-1}, ω_{i+1})`.

Then `γ` has **exactly one** Gibbs measure `μ`, and `μ` is the stationary Markov chain `μ_P` with
transition matrix `P`: there is a strictly positive probability vector `α` on `E`, invariant under
`P`, such that the cylinder probabilities of `μ` are

`μ(σ_a = x_a, …, σ_{a+n} = x_{a+n}) = α(x_a) P(x_a, x_{a+1}) ⋯ P(x_{a+n-1}, x_{a+n})`. -/
theorem georgii_3_5_markovChain (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1)
    (γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E))
    (hγ : IsSpecification γ)
    (hsingle : ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
      γ {i} ω {σ : Config ℤ E | σ i = y}
        = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1)))) :
    ∃ (μ : MeasureTheory.Measure (Config ℤ E)) (α : E → ℝ),
      (∀ y, 0 < α y) ∧
      (∑ y, α y = 1) ∧
      (∀ y, ∑ x, α x * P x y = α y) ∧
      (∀ (a : ℤ) (n : ℕ) (x : Config ℤ E),
        μ (cylinder a (a + n) x)
          = ENNReal.ofReal (α (x a) * ∏ k ∈ Finset.range n, P (x (a + k)) (x (a + k + 1)))) ∧
      (∀ ν : MeasureTheory.Measure (Config ℤ E), IsGibbs γ ν ↔ ν = μ) :=
  sorry

/-- **Georgii, Theorem (3.5), the uniqueness half.** A specification on `ℤ` whose singleton kernels
come from a strictly positive stochastic matrix `P` via (3.11) has exactly one Gibbs measure. -/
theorem georgii_3_5_uniqueness (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1)
    (γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E))
    (hγ : IsSpecification γ)
    (hsingle : ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
      γ {i} ω {σ : Config ℤ E | σ i = y}
        = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1)))) :
    ∃! μ : MeasureTheory.Measure (Config ℤ E), IsGibbs γ μ :=
  sorry

/-- **Non-vacuity of Theorem (3.5).** For every strictly positive stochastic matrix `P` on a finite
state space there really is a specification on `ℤ` whose singleton kernels are given by Georgii's
determining function (3.11).  So the hypotheses of `georgii_3_5_markovChain` and
`georgii_3_5_uniqueness` are satisfiable, and those theorems are not statements about an empty
class of specifications. -/
theorem exists_isSpecification_determiningFun (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1) :
    ∃ γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E), IsSpecification γ ∧
      ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
        γ {i} ω {σ : Config ℤ E | σ i = y}
          = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1))) :=
  sorry

end MarkovChainChallenge

end

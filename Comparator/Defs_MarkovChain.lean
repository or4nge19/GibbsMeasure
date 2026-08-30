import Comparator.Defs

/-!
# Definitions: the determining function of a Markov chain on `ℤ` (Georgii (3.11))

This module extends the shared preamble `Comparator.Defs` with the two notions specific to
Georgii's Theorem (3.5): the determining function `g(x,y,z) = P(x,y)P(y,z)/P²(x,z)` of (3.11) and
the interval cylinder events.  It holds the definitions used by
`Comparator/Challenge_MarkovChain.lean` and `Comparator/Solution_MarkovChain.lean`.

**It imports `Comparator.Defs` — which imports `Mathlib` and nothing else — and nothing further.**
Everything is spelled out from first principles: the configuration space `Config ℤ E = ℤ → E`, the
notion of a specification (`IsSpecification`, from the preamble), the DLR equations (`IsGibbs`,
from the preamble), and here the determining function and the cylinder events.

## Dictionary

| Georgii | here |
| --- | --- |
| stochastic matrix `P` with `P(x,y) > 0` | `P : E → E → ℝ`, `hstoch`, `hpos` |
| `g(x,y,z) = P(x,y)P(y,z)/P²(x,z)`, (3.11) | `determiningFun P` |
| positive homogeneous Markov specification, (3.1) | `IsSpecification γ` + `hsingle` |
| `α_P`, the stationary distribution, (3.3) | the `α` produced by the theorem |
| `μ_P(σ_a = x_a, …, σ_b = x_b)`, (3.3) | `μ (cylinder a b x)` |
| `𝒢(γ) = {μ_P}` | the final `∀ ν, IsGibbs γ ν ↔ ν = μ` |
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

/-- **Georgii (3.11).** The determining function of a strictly positive stochastic matrix `P`:
`g(x, y, z) = P(x,y) P(y,z) / P²(x,z)`, where the two-step transition probability `P²(x,z)` is
written out as the sum `∑ w, P(x,w) P(w,z)`. -/
def determiningFun (P : E → E → ℝ) (x y z : E) : ℝ := P x y * P y z / ∑ w, P x w * P w z

/-- The interval cylinder event `{σ_a = x_a, …, σ_b = x_b}`. -/
def cylinder (a b : ℤ) (x : Config ℤ E) : Set (Config ℤ E) := {τ | ∀ k ∈ Finset.Icc a b, τ k = x k}

end MarkovChainChallenge

end

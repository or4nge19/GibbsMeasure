import Comparator.Defs

/-!
# Markov chains as Gibbs measures on `ℤ`: definitions

The two notions specific to Georgii's Theorem (3.5), on top of the shared preamble.

## Main definitions

* `determiningFun`: Georgii (3.11), the determining function `g(x,y,z) = P(x,y)P(y,z)/P²(x,z)` of
  a strictly positive stochastic matrix `P`.
* `cylinder`: the interval cylinder event `{σ_a = x_a, …, σ_b = x_b}`.
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

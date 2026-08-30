import Comparator.Defs_MarkovChain

/-!
# Markov chains as Gibbs measures on `ℤ` (Georgii, Theorem (3.5))

## Main statements

* `georgii_3_5_markovChain`: Georgii (3.5), a specification on `ℤ` whose singleton kernels come
  from a strictly positive stochastic matrix `P` via (3.11) has exactly one Gibbs measure, the
  stationary Markov chain with transition matrix `P`.
* `georgii_3_5_uniqueness`: the uniqueness half, packaged as `∃!`.
* `exists_isSpecification_determiningFun`: non-vacuity — such a specification exists.
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

/-- **Georgii, Theorem (3.5)**: for a strictly positive stochastic matrix `P` on a finite state
space `E`, *any* specification `γ` on `ℤ` whose singleton kernels are given by the determining
function (3.11), `γ_{i}(σ_i = y | ω) = P(ω_{i-1}, y) P(y, ω_{i+1}) / P²(ω_{i-1}, ω_{i+1})`, has
exactly one Gibbs measure, namely the stationary Markov chain `μ_P`: for the strictly positive
`P`-invariant probability vector `α`,
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

/-- **Non-vacuity of Theorem (3.5)**: for every strictly positive stochastic matrix `P` on a
finite state space there really is a specification on `ℤ` whose singleton kernels are given by the
determining function (3.11). -/
theorem exists_isSpecification_determiningFun (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1) :
    ∃ γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E), IsSpecification γ ∧
      ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
        γ {i} ω {σ : Config ℤ E | σ i = y}
          = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1))) :=
  sorry

end MarkovChainChallenge

end

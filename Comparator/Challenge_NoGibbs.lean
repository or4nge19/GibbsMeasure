import Comparator.Defs_NoGibbs

/-!
# Comparator challenge: Georgii Example (4.16) — a specification with no Gibbs measure

The single-particle family `gamma` is a genuine specification yet has no Gibbs measure at all on a
countably infinite site set: the single particle escapes to infinity.  So the existence theorems
(4.17) / (4.22) really do need a hypothesis beyond "specification", and indeed `gamma` is not
quasilocal.  The infinitude of `S` is essential.

## Main statements

* `isSpecification_gamma`: `gamma` is proper, consistent, and a probability kernel from `𝓣_Λ`
* `not_isGibbs_gamma`: `𝓖(γ) = ∅`
* `one_le_oscOutside_gamma`, `not_isQuasilocal_gamma`: `gamma` is not quasilocal, with an explicit
  witness
* `isGibbs_spikeMeasure_of_finite`: on a finite site set the same formulas do have a Gibbs measure

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Example (4.16)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

namespace SingleParticle

variable {S : Type*} [Countable S] [DecidableEq S]

/-! ### The statements -/

/-- **Georgii (4.16) is a specification**: proper, consistent, and each `γ_Λ(A|·)` is a
`𝓣_Λ`-measurable probability kernel. -/
theorem isSpecification_gamma : IsSpecification (gamma (S := S)) := by
  sorry

/-- **Georgii (4.16) has no Gibbs measure**: `𝓖(γ) = ∅` on a countably infinite site set. -/
theorem not_isGibbs_gamma [Infinite S] (μ : Measure (Config S Bool)) :
    ¬ IsGibbs (gamma (S := S)) μ := by
  sorry

/-- The explicit witness of non-quasilocality: `ω ↦ γ_{a}(σ_a = 1 | ω)` is the indicator of
`{ω = 0 off {a}}`, whose oscillation off every finite volume is at least `1`. -/
theorem one_le_oscOutside_gamma [Infinite S] (a : S) (Δ : Finset S) :
    1 ≤ oscOutside Δ fun ω => (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal := by
  sorry

/-- **Georgii, Example (4.16)** is not quasilocal; with `isSpecification_gamma` and
`not_isGibbs_gamma` this shows quasilocality cannot be dropped from the existence theorems (4.17)
and (4.22). -/
theorem not_isQuasilocal_gamma [Infinite S] : ¬ IsQuasilocal (gamma (S := S)) := by
  sorry

/-- Infinitude of `S` is essential: on a finite site set the same formulas do have a Gibbs
measure, the uniform distribution on the one-particle configurations. -/
theorem isGibbs_spikeMeasure_of_finite {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] :
    IsGibbs (gamma (S := S)) (spikeMeasure (Finset.univ : Finset S)) := by
  sorry

end SingleParticle

end GibbsChallenge

end

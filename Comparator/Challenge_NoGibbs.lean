import Comparator.Defs_NoGibbs

/-!
# Comparator challenge: Georgii Example (4.16) — a specification with no Gibbs measure

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_NoGibbs`, whose transitive imports are `Comparator.Defs` and
`Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library whose
theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `outside`, `tail`,
`IsSpecification`, `IsGibbs`, …) is defined in `Comparator/Defs.lean`, and quasilocality together
with Georgii's single-particle kernels (`oscOutside`, `IsQuasilocal`, `spike`, `spikeMeasure`,
`gamma`, …) in `Comparator/Defs_NoGibbs.lean`; both module docstrings describe them.

## Main statements

The single-particle family `gamma` is a genuine specification — proper, consistent, and each
`γ_Λ` is a probability kernel from the external σ-algebra `𝓣_Λ` (`isSpecification_gamma`) — yet it
has **no** Gibbs measure at all (`not_isGibbs_gamma`): the single particle "escapes to infinity".
So the existence theorems (4.17) / (4.22) really do need a hypothesis beyond "specification": this
`γ` is **not quasilocal** (`not_isQuasilocal_gamma`), witnessed explicitly by
`one_le_oscOutside_gamma`.

The infinitude of `S` is essential: for a finite `S` the very same formulas define a specification
whose uniform distribution on the `|S|` one-particle configurations *is* a Gibbs measure
(`isGibbs_spikeMeasure_of_finite`).
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

/-- The explicit witness of non-quasilocality: for the local observable `1_{σ_a = 1}` the function
`ω ↦ γ_{a}(σ_a = 1 | ω)` is the indicator of `{ω = 0 off {a}}`, whose oscillation off **every**
finite volume `Δ` is `1`. -/
theorem one_le_oscOutside_gamma [Infinite S] (a : S) (Δ : Finset S) :
    1 ≤ oscOutside Δ fun ω => (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal := by
  sorry

/-- **Georgii (4.16) is not quasilocal.** Together with `isSpecification_gamma` and
`not_isGibbs_gamma` this shows that quasilocality cannot be dropped from the existence theorems
(4.17) and (4.22). -/
theorem not_isQuasilocal_gamma [Infinite S] : ¬ IsQuasilocal (gamma (S := S)) := by
  sorry

/-- **Infinitude of `S` is essential.** On a finite site set the same formulas do have a Gibbs
measure, namely the uniform distribution on the one-particle configurations. -/
theorem isGibbs_spikeMeasure_of_finite {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] :
    IsGibbs (gamma (S := S)) (spikeMeasure (Finset.univ : Finset S)) := by
  sorry

end SingleParticle

end GibbsChallenge

end

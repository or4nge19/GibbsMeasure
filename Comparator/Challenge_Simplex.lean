import Comparator.Defs_Simplex

/-!
# Comparator challenge: the simplex of Gibbs measures (Georgii, Theorems (7.7)(a) and (7.26))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_Simplex`, whose transitive imports are `Comparator.Defs` and
`Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library whose
theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `outside`, `tail`,
`IsSpecification`, `IsGibbs`, …) is defined in `Comparator/Defs.lean`, and `GibbsSet`,
`IsExtremeIn`, `IsTailTrivialOn` in `Comparator/Defs_Simplex.lean`; both module docstrings contain
the dictionary.

## Main statements

* `isExtremeIn_iff_isTailTrivialOn`: **Georgii, Theorem (7.7)(a).** For a specification `γ` over a
  countable parameter set, a Gibbs measure is extreme in `𝓖(γ)` **iff** it is trivial on the tail
  σ-algebra.
* `exists_isExtremeIn`: **Georgii, Theorem (7.26), first half.** Over a standard Borel state space,
  `𝓖(γ) ≠ ∅` implies `ex 𝓖(γ) ≠ ∅`.
* `existsUnique_weight_isExtremeIn`: **Georgii, Theorem (7.26), second half.** Every `μ ∈ 𝓖(γ)` is
  the barycentre of a *unique* probability weight `w` concentrated on `ex 𝓖(γ)`.
* `georgii_7_26`: the two halves packaged together.
* `mutuallySingular_of_isExtremeIn`: **Georgii, Theorem (7.7)(d).** Distinct extreme Gibbs
  measures are mutually singular.
* `le_encard_setOf_isExtremeIn_iff`: **Georgii, Corollary (7.29).** `𝓖(γ)` has at least `N`
  extreme points iff it contains `N` measures which are linearly independent over `ℝ≥0∞`.
* `gibbsSet_indepSpec_nonempty`: **non-degeneracy.** The hypotheses of `georgii_7_26` are
  satisfiable: the independent specification of the preamble, over a standard Borel state
  space, has a nonempty set of Gibbs measures, so the decomposition theorem says something.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section Simplex

variable {S E : Type*} [MeasurableSpace E]

/-! ### Georgii, Theorem (7.7)(a) -/

/-- **Georgii, Theorem (7.7)(a).** Let `γ` be a specification on `E^S` with `S` countable. A Gibbs
measure `μ ∈ 𝓖(γ)` is an *extreme point* of `𝓖(γ)` if and only if it is *trivial on the tail
σ-algebra*. -/
theorem isExtremeIn_iff_isTailTrivialOn [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    IsExtremeIn (GibbsSet γ) μ ↔ IsTailTrivialOn μ :=
  sorry

/-! ### Georgii, Theorem (7.26) -/

/-- **Georgii, Theorem (7.26), first half.** Over a standard Borel state space and a countable
parameter set, if a specification admits at least one Gibbs measure then it admits at least one
*extreme* Gibbs measure. -/
theorem exists_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    ∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν :=
  sorry

/-- **Georgii, Theorem (7.26), second half: the extremal decomposition.** Over a standard Borel
state space and a countable parameter set, every Gibbs measure `μ` is the barycentre
`μ = ∫ ν w(dν)` of a **unique** probability measure `w` on the space of measures which is
concentrated on the set of extreme Gibbs measures. -/
theorem existsUnique_weight_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    ∃! w : Measure (Measure (Config S E)),
      IsProbabilityMeasure w ∧
        w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
        Measure.join w = μ :=
  sorry

/-- **Georgii, Theorem (7.26)**, both halves together: over a standard Borel state space and a
countable parameter set, a nonempty set of Gibbs measures is a simplex whose extreme points are
nonempty and represent every one of its elements uniquely. -/
theorem georgii_7_26 [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    (∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν) ∧
      ∀ μ ∈ GibbsSet γ, ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
          Measure.join w = μ :=
  sorry

/-! ### Georgii, Theorem (7.7)(d) and Corollary (7.29) -/

/-- **Georgii, Theorem (7.7)(d).** Two *distinct* extreme Gibbs measures are mutually singular:
they are carried by disjoint measurable sets. -/
theorem mutuallySingular_of_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ ν : Measure (Config S E)} (hμ : IsExtremeIn (GibbsSet γ) μ)
    (hν : IsExtremeIn (GibbsSet γ) ν) (hne : μ ≠ ν) :
    μ.MutuallySingular ν :=
  sorry

/-- **Georgii, Corollary (7.29).** For a specification with at least one Gibbs measure, the number
of *extreme* Gibbs measures is at least `N` if and only if `𝓖(γ)` contains `N` measures which are
linearly independent over `ℝ≥0∞`. -/
theorem le_encard_setOf_isExtremeIn_iff [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) (N : ℕ) :
    (N : ℕ∞) ≤ {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}.encard ↔
      ∃ μ : Fin N → Measure (Config S E), (∀ i, IsGibbs γ (μ i)) ∧ LinearIndependent ℝ≥0∞ μ :=
  sorry

/-! ### Non-degeneracy -/

/-- **Non-degeneracy: the hypotheses above are not vacuous.** For a single-spin distribution `ν` on
a standard Borel state space and an arbitrary — in particular infinite — parameter set `S`, the
independent specification `indepSpec ν` of the preamble has a nonempty set of Gibbs measures — the
infinite product measure `ν^S` is one — and hence, by `georgii_7_26`, a nonempty set of *extreme*
Gibbs measures, each Gibbs measure being the barycentre of a unique weight carried by them. -/
theorem gibbsSet_indepSpec_nonempty [Countable S] [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : S ↦ ν) ∈ GibbsSet (indepSpec (S := S) ν) ∧
      (∃ ρ : Measure (Config S E), IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ) ∧
      ∀ μ ∈ GibbsSet (indepSpec (S := S) ν), ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ρ : Measure (Config S E) | IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ}ᶜ = 0 ∧
          Measure.join w = μ :=
  sorry

end Simplex

end GibbsChallenge

end

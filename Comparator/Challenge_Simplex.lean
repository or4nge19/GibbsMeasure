import Comparator.Defs_Simplex

/-!
# The simplex of Gibbs measures

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Theorems (7.7) and (7.26).

## Main statements

* `isExtremeIn_iff_isTailTrivialOn`: Georgii (7.7)(a), a Gibbs measure is extreme in `𝓖(γ)` iff it
  is tail-trivial
* `exists_isExtremeIn`: Georgii (7.26), `𝓖(γ) ≠ ∅` implies `ex 𝓖(γ) ≠ ∅`
* `existsUnique_weight_isExtremeIn`: Georgii (7.26), every `μ ∈ 𝓖(γ)` is the barycentre of a unique
  weight concentrated on `ex 𝓖(γ)`
* `georgii_7_26`: the two halves packaged together
* `mutuallySingular_of_isExtremeIn`: Georgii (7.7)(d), distinct extreme Gibbs measures are mutually
  singular
* `le_encard_setOf_isExtremeIn_iff`: Georgii (7.29), `𝓖(γ)` has at least `N` extreme points iff it
  contains `N` measures linearly independent over `ℝ≥0∞`
* `gibbsSet_indepSpec_nonempty`: the hypotheses above are satisfiable
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

/-- **Georgii (7.7)(a)**: a Gibbs measure is an extreme point of `𝓖(γ)` iff it is trivial on the
tail σ-algebra. -/
theorem isExtremeIn_iff_isTailTrivialOn [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    IsExtremeIn (GibbsSet γ) μ ↔ IsTailTrivialOn μ :=
  sorry

/-! ### Georgii, Theorem (7.26) -/

/-- **Georgii (7.26)**, first half: over a standard Borel state space, a specification admitting a
Gibbs measure admits an extreme one. -/
theorem exists_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    ∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν :=
  sorry

/-- **Georgii (7.26)**, second half, the extremal decomposition: every Gibbs measure `μ` is the
barycentre `μ = ∫ ν w(dν)` of a unique probability weight `w` concentrated on `ex 𝓖(γ)`. -/
theorem existsUnique_weight_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    ∃! w : Measure (Measure (Config S E)),
      IsProbabilityMeasure w ∧
        w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
        Measure.join w = μ :=
  sorry

/-- **Georgii (7.26)**, both halves: a nonempty `𝓖(γ)` is a simplex, with nonempty extreme set
representing each of its elements uniquely. -/
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

/-- **Georgii (7.7)(d)**: distinct extreme Gibbs measures are mutually singular. -/
theorem mutuallySingular_of_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ ν : Measure (Config S E)} (hμ : IsExtremeIn (GibbsSet γ) μ)
    (hν : IsExtremeIn (GibbsSet γ) ν) (hne : μ ≠ ν) :
    μ.MutuallySingular ν :=
  sorry

/-- **Georgii (7.29)**: `𝓖(γ)` has at least `N` extreme points iff it contains `N` measures that
are linearly independent over `ℝ≥0∞`. -/
theorem le_encard_setOf_isExtremeIn_iff [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) (N : ℕ) :
    (N : ℕ∞) ≤ {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}.encard ↔
      ∃ μ : Fin N → Measure (Config S E), (∀ i, IsGibbs γ (μ i)) ∧ LinearIndependent ℝ≥0∞ μ :=
  sorry

/-! ### Non-degeneracy -/

/-- Non-degeneracy: the independent specification `indepSpec ν` has `ν^S` as a Gibbs measure, so
the hypotheses of `georgii_7_26` are satisfiable even for infinite `S`. -/
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

import Comparator.Defs_DeFinetti
import GibbsMeasure

/-!
# Comparator challenge: de Finetti's theorem (Georgii, Examples (7.16), (7.17), (7.31))

The Hewitt–Savage zero-one law, the identification of the extreme exchangeable measures with the
i.i.d. product measures, and de Finetti's theorem in the version of Dynkin: over a standard Borel
state space, every exchangeable probability measure on `E^ℕ` is the mixture of i.i.d. product
measures under a unique probability weight on `𝒫(E, ℰ)`.

## Main statements

* `hewittSavage_zero_one`: Georgii (7.17), the zero-one law of Hewitt and Savage
* `mem_extremePoints_iff_exists_iid`: Georgii (7.17), `ex 𝒫_I` = the i.i.d. product measures —
  the substantial half holds over an **arbitrary** state space
* `existsUnique_iidMix`: Georgii (7.31), de Finetti's theorem in the version of Dynkin
* `isExchangeable_iidMix`: non-vacuity — every mixture of i.i.d. products is exchangeable

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Sections 7.2–7.3
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace DeFinettiChallenge

open GibbsChallenge GibbsChallenge.DeFinetti

variable {E : Type*} [MeasurableSpace E]

/-! ## The bridge -/

namespace Bridge

open MeasureTheory.GibbsMeasure

theorem permute_eq (σ : Equiv.Perm ℕ) :
    DeFinetti.permute (E := E) σ = MeasureTheory.GibbsMeasure.permute σ := rfl

theorem mem_finitaryPerm_iff {σ : Equiv.Perm ℕ} :
    σ ∈ DeFinetti.finitaryPerm ↔ σ ∈ MeasureTheory.GibbsMeasure.finitaryPerm := Iff.rfl

theorem isExchangeable_iff {μ : Measure (Config ℕ E)} :
    DeFinetti.IsExchangeable μ ↔ MeasureTheory.GibbsMeasure.IsExchangeable μ := Iff.rfl

theorem isSymmetric_iff {A : Set (Config ℕ E)} :
    DeFinetti.IsSymmetric A ↔ MeasurableSet[symmetricSigmaAlgebra E] A := by
  rw [measurableSet_symmetricSigmaAlgebra_iff]
  constructor
  · rintro ⟨hmeas, hinv⟩ n
    exact measurableSet_symmSub_iff.2
      ⟨hmeas, fun σ hσ ↦ hinv σ (mem_finitaryPerm_iff.2 (finPerm_le_finitaryPerm n hσ))⟩
  · intro h
    refine ⟨(measurableSet_symmSub_iff.1 (h 0)).1, fun σ hσ ↦ ?_⟩
    obtain ⟨n, hn⟩ := mem_finitaryPerm_iff.1 hσ
    exact (measurableSet_symmSub_iff.1 (h n)).2 σ hn

theorem exchangeableSet_eq :
    {μ : Measure (Config ℕ E) | IsProbabilityMeasure μ ∧ DeFinetti.IsExchangeable μ}
      = (exchangeableSpec E).invariant := by
  rw [exchangeableSpec_invariant]
  rfl

theorem iidMix_eq (m : Measure (Measure E)) :
    iidMix m = m.bind fun lam ↦ Measure.infinitePi fun _ : ℕ ↦ lam := rfl

end Bridge

/-! ## The theorems -/

/-- **The Hewitt–Savage zero-one law (Georgii (7.17))**: an i.i.d. product measure gives every
symmetric event probability zero or one. -/
theorem hewittSavage_zero_one (ν : Measure E) [IsProbabilityMeasure ν] {A : Set (Config ℕ E)}
    (hA : IsSymmetric A) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) A = 0 ∨ Measure.infinitePi (fun _ : ℕ ↦ ν) A = 1 :=
  MeasureTheory.GibbsMeasure.measure_symmetric_eq_zero_or_one (Bridge.isSymmetric_iff.1 hA)

/-- **Georgii (7.17)**: the extreme points of the exchangeable probability measures are exactly
the i.i.d. product measures.  The state space is arbitrary. -/
theorem mem_extremePoints_iff_exists_iid (μ : Measure (Config ℕ E)) :
    μ ∈ Set.extremePoints ℝ≥0∞ {μ : Measure (Config ℕ E) |
        IsProbabilityMeasure μ ∧ IsExchangeable μ} ↔
      ∃ lam : Measure E, IsProbabilityMeasure lam
        ∧ μ = Measure.infinitePi fun _ : ℕ ↦ lam := by
  rw [Bridge.exchangeableSet_eq]
  exact MeasureTheory.GibbsMeasure.mem_extremePoints_exchangeable_iff

/-- **Georgii (7.31): de Finetti's theorem in the version of Dynkin.** Over a standard Borel
state space, every exchangeable probability measure on `E^ℕ` is the mixture `∫ λ^ℕ m(dλ)` of
i.i.d. product measures under a unique probability weight `m` carried by `𝒫(E, ℰ)`. -/
theorem existsUnique_iidMix [StandardBorelSpace E] [Nonempty E] (μ : Measure (Config ℕ E))
    [IsProbabilityMeasure μ] (hμ : IsExchangeable μ) :
    ∃! m : Measure (Measure E), IsProbabilityMeasure m
      ∧ m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0
      ∧ iidMix m = μ :=
  MeasureTheory.GibbsMeasure.existsUnique_mixing_of_isExchangeable
    (Bridge.isExchangeable_iff.1 hμ)

/-- Non-vacuity: the mixture of i.i.d. products under any weight carried by the probability
measures is exchangeable, so the representation of `existsUnique_iidMix` characterises
exchangeability. -/
theorem isExchangeable_iidMix (m : Measure (Measure E))
    (hm : m {lam : Measure E | IsProbabilityMeasure lam}ᶜ = 0) :
    IsExchangeable (iidMix m) :=
  Bridge.isExchangeable_iff.2
    (MeasureTheory.GibbsMeasure.isExchangeable_bind_infinitePi hm)

end DeFinettiChallenge

end

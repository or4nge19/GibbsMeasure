import Comparator.Defs_Representation

/-!
# The Gibbs representation theorem

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Theorem (2.30) and its converse.

## Main statements

* `existsUnique_gasPotential`: Georgii (2.30), a positive quasilocal normalized pre-modification is
  the `λ`-modification of a unique `λ`-admissible gas potential with the given vacuum state
* `eq_of_isGasPotential`: the uniqueness half in isolation
* `isPreModification_boltzmann`: Georgii (2.5)
* `lambdaInt_gibbsModification_eq_one`, `isPreModification_gibbsModification`: Georgii (2.8),
  (1.32), the converse direction — quasilocality apart, the families `ρ` admitted by (2.30) are
  exactly the `λ`-modifications of `λ`-admissible potentials
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

namespace Representation

variable {S E : Type*} [Countable S] [DecidableEq S] [MeasurableSpace E]

/-! ### The statements -/

/-- **Georgii (2.30)**, the Gibbs representation theorem: a positive quasilocal pre-modification
`ρ` with `λ_Λ ρ_Λ = 1` is, for each vacuum state `a ∈ E`, the `λ`-modification of a unique
`λ`-admissible gas potential `Φ^a` with vacuum state `a`.

Uniqueness is asserted on Georgii's index set `𝒮 = {A : 0 < |A| < ∞}`, the value at `A = ∅`
entering no Hamiltonian.  `Φ^a` is claimed to be a potential in the sense of (2.2) and nothing
more: not absolutely summable (2.11), not even uniformly convergent — Georgii gets a uniformly
convergent representative only when `log ρ_Λ` is bounded, and absolute summability is the separate
Kozlov–Sullivan theorem, not proved in §2.3. -/
theorem existsUnique_gasPotential (ν : Measure E) [SigmaFinite ν]
    (ρ : Finset S → Config S E → ℝ≥0∞) (hρ : IsPreModification ρ) (hpos : IsPositive ρ)
    (hql : ∀ Λ : Finset S, IsQuasilocalFun fun η => (ρ Λ η).toReal)
    (hnorm : ∀ (Λ : Finset S) (η : Config S E), lambdaInt ν Λ (ρ Λ) η = 1) (a : E) :
    ∃ Φ : Potential S E, IsPotential Φ ∧ IsGasPotential a Φ ∧ IsAdmissible ν Φ ∧
      (∀ (Λ : Finset S) (η : Config S E), gibbsModification ν Φ Λ η = ρ Λ η) ∧
      ∀ Ψ : Potential S E, IsPotential Ψ → IsGasPotential a Ψ → IsAdmissible ν Ψ →
        (∀ (Λ : Finset S) (η : Config S E), gibbsModification ν Ψ Λ η = ρ Λ η) →
        ∀ A : Finset S, A.Nonempty → ∀ η : Config S E, Ψ A η = Φ A η := by
  sorry

/-- **Georgii (2.30)**, the uniqueness half (his step 5): two `λ`-admissible gas potentials with the
same vacuum state defining the same `λ`-modification agree on every non-empty support. -/
theorem eq_of_isGasPotential (ν : Measure E) [SigmaFinite ν] {a : E} {Φ Ψ : Potential S E}
    (hΦ : IsPotential Φ) (hΨ : IsPotential Ψ)
    (hΦgas : IsGasPotential a Φ) (hΨgas : IsGasPotential a Ψ)
    (hΦadm : IsAdmissible ν Φ) (hΨadm : IsAdmissible ν Ψ)
    (heq : ∀ (Λ : Finset S) (η : Config S E),
      gibbsModification ν Φ Λ η = gibbsModification ν Ψ Λ η)
    {A : Finset S} (hA : A.Nonempty) (η : Config S E) : Φ A η = Ψ A η := by
  sorry

/-- **Georgii (2.5)**: the Boltzmann factors `h^Φ_Λ = exp(-H^Φ_Λ)` of a potential form a positive
pre-modification. -/
theorem isPreModification_boltzmann {Φ : Potential S E} (hΦ : IsPotential Φ) :
    IsPreModification (boltzmann Φ) ∧ IsPositive (boltzmann Φ) := by
  sorry

/-- **Georgii (2.8), (1.32)**: the `λ`-modification `ρ^Φ` of a `λ`-admissible potential is
normalized, `λ_Λ ρ^Φ_Λ = 1` for every finite volume `Λ`. -/
theorem lambdaInt_gibbsModification_eq_one (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) (Λ : Finset S) (η : Config S E) :
    lambdaInt ν Λ (gibbsModification ν Φ Λ) η = 1 := by
  sorry

/-- **Georgii (2.5) and (1.32)**, the converse direction of (2.30): the `λ`-modification
`ρ^Φ = h^Φ / Z^Φ` of a `λ`-admissible potential is itself a positive pre-modification. -/
theorem isPreModification_gibbsModification (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) :
    IsPreModification (gibbsModification ν Φ) ∧ IsPositive (gibbsModification ν Φ) := by
  sorry

end Representation

end GibbsChallenge

end

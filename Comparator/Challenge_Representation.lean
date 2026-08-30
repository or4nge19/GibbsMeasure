import Comparator.Defs_Representation

/-!
# Comparator challenge: Georgii Theorem (2.30) — the Gibbs representation theorem

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_Representation`, whose transitive imports are `Comparator.Defs`
and `Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library
whose theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `inside`,
`outside`, …) is defined in `Comparator/Defs.lean`, and the vocabulary of §§1.3, 2.1–2.3
(`lambdaInt`, `IsPreModification`, `IsPositive`, `IsQuasilocalFun`, `Potential`, `IsPotential`,
`hamiltonian`, `boltzmann`, `partitionFunction`, `IsAdmissible`, `gibbsModification`,
`IsGasPotential`) in `Comparator/Defs_Representation.lean`; both module docstrings describe them.

## Main statements

`existsUnique_gasPotential` is Georgii's **Gibbs representation theorem (2.30)**: a positive
quasilocal pre-modification `ρ` normalized by `λ_Λ ρ_Λ = 1` is, for each choice of a vacuum state
`a ∈ E`, the `λ`-modification `ρ^{Φ^a}` of a *unique* `λ`-admissible gas potential `Φ^a` with
vacuum state `a`.  `eq_of_isGasPotential` is its uniqueness half in isolation.

`isPreModification_boltzmann` (Georgii (2.5)), `lambdaInt_gibbsModification_eq_one` and
`isPreModification_gibbsModification` (Georgii (2.8), (1.32)) are the converse direction: the
Boltzmann factors of a potential form a positive pre-modification, and the `λ`-modification
`ρ^Φ = h^Φ / Z^Φ` of a `λ`-admissible potential is again a positive pre-modification, normalized by
`λ_Λ ρ^Φ_Λ = 1`.  So — quasilocality apart — the families `ρ` admitted by (2.30) are exactly the
`λ`-modifications of `λ`-admissible potentials.
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

/-- **Georgii, Theorem (2.30): the Gibbs representation theorem.**

Let `λ = ν` be an a priori measure on the single-spin space `(E, 𝓔)`, and let `ρ = (ρ_Λ)` be a
positive quasilocal pre-modification with `λ_Λ ρ_Λ = 1` for every finite volume `Λ`.  Then for each
`a ∈ E` there is a **unique** `λ`-admissible **gas potential** `Φ^a` with vacuum state `a` such
that `ρ = ρ^{Φ^a}`.

Uniqueness is asserted on Georgii's index set `𝒮 = {A : 0 < |A| < ∞}`: the value of a potential at
`A = ∅` enters no Hamiltonian and is therefore not determined by `ρ`.

Note what is **not** claimed.  `Φ^a` is a potential in the sense of Georgii (2.2) — its
Hamiltonians exist as limits of the partial sums (2.13) — and nothing more.  It is **not** asserted
to be absolutely summable (2.11), nor even uniformly convergent: Georgii obtains a uniformly
convergent representative only under the extra hypothesis that `log ρ_Λ` be bounded, and the
statement that every quasilocal specification comes from an absolutely summable potential is the
separate Kozlov–Sullivan theorem, which Georgii does not prove in §2.3. -/
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

/-- **Georgii (2.30), the uniqueness half** (his step 5).  Two `λ`-admissible gas potentials with
the same vacuum state `a` which define the same `λ`-modification agree on every non-empty
interaction support. -/
theorem eq_of_isGasPotential (ν : Measure E) [SigmaFinite ν] {a : E} {Φ Ψ : Potential S E}
    (hΦ : IsPotential Φ) (hΨ : IsPotential Ψ)
    (hΦgas : IsGasPotential a Φ) (hΨgas : IsGasPotential a Ψ)
    (hΦadm : IsAdmissible ν Φ) (hΨadm : IsAdmissible ν Ψ)
    (heq : ∀ (Λ : Finset S) (η : Config S E),
      gibbsModification ν Φ Λ η = gibbsModification ν Ψ Λ η)
    {A : Finset S} (hA : A.Nonempty) (η : Config S E) : Φ A η = Ψ A η := by
  sorry

/-- **Georgii, Proposition (2.5)**: the Boltzmann factors `h^Φ_Λ = exp(-H^Φ_Λ)` of a potential
form a *positive* pre-modification. -/
theorem isPreModification_boltzmann {Φ : Potential S E} (hΦ : IsPotential Φ) :
    IsPreModification (boltzmann Φ) ∧ IsPositive (boltzmann Φ) := by
  sorry

/-- **Georgii (2.8), (1.32)**: the `λ`-modification `ρ^Φ` of a `λ`-admissible potential is
normalized, `λ_Λ ρ^Φ_Λ = 1` for every finite volume `Λ`. -/
theorem lambdaInt_gibbsModification_eq_one (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) (Λ : Finset S) (η : Config S E) :
    lambdaInt ν Λ (gibbsModification ν Φ Λ) η = 1 := by
  sorry

/-- **Georgii (2.5) and (1.32) combined**, the converse direction of Theorem (2.30): the
`λ`-modification `ρ^Φ = h^Φ / Z^Φ` of a `λ`-admissible potential is itself a positive
pre-modification.  Together with `lambdaInt_gibbsModification_eq_one` this says that the families
`ρ` fed to Theorem (2.30) are — quasilocality apart — exactly the `λ`-modifications of
`λ`-admissible potentials, so its hypotheses are not vacuous. -/
theorem isPreModification_gibbsModification (ν : Measure E) [SigmaFinite ν] {Φ : Potential S E}
    (hΦ : IsPotential Φ) (hadm : IsAdmissible ν Φ) :
    IsPreModification (gibbsModification ν Φ) ∧ IsPositive (gibbsModification ν Φ) := by
  sorry

end Representation

end GibbsChallenge

end

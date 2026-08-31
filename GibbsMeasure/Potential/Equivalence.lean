/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.GibbsRepresentation
public import GibbsMeasure.Specification.Rescaling

/-!
# Georgii §2.4: equivalence of potentials

Two potentials are equivalent when the Hamiltonian of their difference does not depend on the
configuration inside the volume. Equivalent potentials define the same Gibbsian specification, so
a potential may be replaced by any convenient representative of its class.

## Main declarations

* `Potential.IsEquivalent`: Georgii, Definition (2.33).
* `Potential.sigmaFinitePremodifierNorm_eq_of_isEquivalent`: Georgii (2.34), (i) ⇒ (ii).
* `Potential.lambdaSpecification_eq_of_isEquivalent`: Georgii (2.34), (i) ⇒ (iii).

The converse (2.34), (ii) ⇒ (i) is
`Potential.dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Potential

variable {S E : Type*} {mE : MeasurableSpace E} [Countable S] [DecidableEq S]
  {Φ Ψ : Potential S E}

/-- **Georgii, Definition (2.33).** `Φ` and `Ψ` are *equivalent* if for every finite volume `Λ`
the Hamiltonian `H_Λ^{Φ-Ψ}` is `𝓣_Λ`-measurable, i.e. depends on the configuration outside `Λ`
only. -/
def IsEquivalent (Φ Ψ : Potential S E) : Prop :=
  ∀ Λ : Finset S, Measurable[cylinderEvents ((Λ : Set S))ᶜ] ((Φ - Ψ).hamiltonian Λ)

namespace IsEquivalent

omit [Countable S] in
@[refl] protected lemma refl [IsSummable Φ] : IsEquivalent Φ Φ := fun Λ ↦ by
  have h : (Φ - Φ).hamiltonian Λ = fun _ ↦ 0 := by
    funext η
    simpa using hamiltonian_sub' (Φ := Φ) (Ψ := Φ) Λ η
  rw [h]
  exact measurable_const

omit [Countable S] in
protected lemma symm [IsSummable Φ] [IsSummable Ψ] (h : IsEquivalent Φ Ψ) :
    IsEquivalent Ψ Φ := fun Λ ↦ by
  have hne : (Ψ - Φ).hamiltonian Λ = fun η ↦ -((Φ - Ψ).hamiltonian Λ η) := by
    funext η
    rw [hamiltonian_sub' (Φ := Ψ) (Ψ := Φ) Λ η, hamiltonian_sub' (Φ := Φ) (Ψ := Ψ) Λ η]
    ring
  rw [hne]
  exact (h Λ).neg

omit [Countable S] in
protected lemma trans {Θ : Potential S E} [IsSummable Φ] [IsSummable Ψ] [IsSummable Θ]
    (h₁ : IsEquivalent Φ Ψ) (h₂ : IsEquivalent Ψ Θ) : IsEquivalent Φ Θ := fun Λ ↦ by
  have hadd : (Φ - Θ).hamiltonian Λ
      = fun η ↦ (Φ - Ψ).hamiltonian Λ η + (Ψ - Θ).hamiltonian Λ η := by
    funext η
    rw [hamiltonian_sub' (Φ := Φ) (Ψ := Θ) Λ η, hamiltonian_sub' (Φ := Φ) (Ψ := Ψ) Λ η,
      hamiltonian_sub' (Φ := Ψ) (Ψ := Θ) Λ η]
    ring
  rw [hadd]
  exact (h₁ Λ).add (h₂ Λ)

end IsEquivalent

omit [Countable S] in
/-- The Boltzmann factor of a difference of potentials splits off multiplicatively. -/
lemma boltzmannFactor_eq_mul_sub [IsSummable Φ] [IsSummable Ψ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η
      = (Φ - Ψ).boltzmannFactor β Λ η * Ψ.boltzmannFactor β Λ η := by
  have hsub := hamiltonian_sub' (Φ := Φ) (Ψ := Ψ) Λ η
  rw [boltzmannFactor, boltzmannFactor, boltzmannFactor,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [hsub]
  ring

omit [Countable S] in
/-- The Boltzmann factor of an equivalent difference is measurable outside the volume. -/
lemma measurable_boltzmannFactor_sub_of_isEquivalent (h : IsEquivalent Φ Ψ) (β : ℝ)
    (Λ : Finset S) :
    Measurable[cylinderEvents ((Λ : Set S))ᶜ] ((Φ - Ψ).boltzmannFactor β Λ) :=
  ((measurable_const.mul (h Λ)).exp).ennreal_ofReal

variable (ν : Measure E) [SigmaFinite ν]

/-- **Georgii (2.34), (i) ⇒ (ii).** Equivalent potentials have the same normalized Gibbs density:
`h_Λ^{Φ-Ψ}` is `𝓣_Λ`-measurable, so properness pulls it out of the partition function, where it
cancels against the same factor in the numerator. -/
theorem sigmaFinitePremodifierNorm_eq_of_isEquivalent [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ] (h : IsEquivalent Φ Ψ) (β : ℝ) :
    Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor β) := by
  funext Λ η
  set g : (S → E) → ℝ≥0∞ := (Φ - Ψ).boltzmannFactor β Λ with hg
  have hgmeas : Measurable[cylinderEvents ((Λ : Set S))ᶜ] g :=
    measurable_boltzmannFactor_sub_of_isEquivalent h β Λ
  have hgne : g η ≠ 0 := by
    simp [hg, boltzmannFactor, ENNReal.ofReal_ne_zero_iff, Real.exp_pos]
  have hgtop : g η ≠ ⊤ := by simp [hg, boltzmannFactor]
  -- the partition function factors
  have hZ : Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      = g η * Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor β) Λ η := by
    rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ]
    rw [show (fun x ↦ Φ.boltzmannFactor β Λ x) = fun x ↦ g x * Ψ.boltzmannFactor β Λ x from
      funext fun x ↦ boltzmannFactor_eq_mul_sub (Φ := Φ) (Ψ := Ψ) β Λ x]
    exact (Specification.isProper_sigmaFiniteLambdaFun (S := S) (E := E) ν Λ).lintegral_mul
      cylinderEvents_le_pi (measurable_boltzmannFactor (Φ := Ψ) β Λ) hgmeas η
  rw [Specification.sigmaFinitePremodifierNorm, Specification.sigmaFinitePremodifierNorm, hZ,
    boltzmannFactor_eq_mul_sub (Φ := Φ) (Ψ := Ψ) β Λ η]
  exact ENNReal.mul_div_mul_left _ _ hgne hgtop

/-- **Georgii (2.34), (i) ⇒ (iii).** Equivalent potentials define the same λ-specification. This
is what licenses replacing a potential by a convenient representative of its class — for instance
one normalized so that `‖Φ_A‖ = δ(Φ_A)/2`, as in the proof of Theorem (8.39). -/
theorem lambdaSpecification_eq_of_isEquivalent [NeZero ν] [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ] (h : IsEquivalent Φ Ψ) (β : ℝ)
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β)}
    {hZΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor β)}
    {hZΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Ψ.boltzmannFactor β)} :
    Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor β) hρΦ hZΦ
      = Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor β) hρΨ hZΨ := by
  refine Specification.ext fun Λ ↦ Kernel.ext fun η ↦ ?_
  rw [Specification.lambdaSpecification_apply, Specification.lambdaSpecification_apply,
    sigmaFinitePremodifierNorm_eq_of_isEquivalent ν h β]

end Potential

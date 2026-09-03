/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Topology.MetricSpace.DependsOn
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
* `Potential.centre`, `Potential.oscNormAt`: recentring a potential, and the per-site total
  oscillation `∑_{A ∋ i} δ(Φ_A)`, finite exactly when some recentring of `Φ` is absolutely
  summable (`Potential.isAbsolutelySummable_centre_iff`). Finiteness is sufficient, not necessary,
  for the class of `Φ` to meet `ℬ`.

The converse (2.34), (ii) ⇒ (i) — in `DependsOn` form, and at inverse temperature `β = 1` — is
`Potential.dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq`; with
`measurable_hamiltonian` and `Measurable.cylinderEvents_of_dependsOn` it upgrades to
`IsEquivalent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Potential

variable {S E : Type*} {mE : MeasurableSpace E} [Countable S] {Φ Ψ : Potential S E}

/-- **Georgii, Definition (2.33).** `Φ` and `Ψ` are *equivalent* if for every finite volume `Λ`
the Hamiltonian `H_Λ^{Φ-Ψ}` is `𝓣_Λ`-measurable, i.e. depends on the configuration outside `Λ`
only.

The predicate is stated for raw families: where the series for `H_Λ^{Φ-Ψ}` diverges, `hamiltonian`
takes the junk value `0` and the condition holds vacuously. It carries Georgii's meaning under
`IsSummable Φ` and `IsSummable Ψ` (which give `IsSummable (Φ - Ψ)`, `isSummable_sub`), matching the
standing hypothesis (2.2)(ii) of Definition (2.33). -/
def IsEquivalent (Φ Ψ : Potential S E) : Prop :=
  ∀ Λ : Finset S, Measurable[cylinderEvents ((Λ : Set S))ᶜ] ((Φ - Ψ).hamiltonian Λ)

namespace IsEquivalent

omit [Countable S] in
@[refl] protected lemma refl [IsSummable Φ] : IsEquivalent Φ Φ := fun Λ ↦ by
  classical
  have h : (Φ - Φ).hamiltonian Λ = fun _ ↦ 0 := by
    funext η
    simpa using hamiltonian_sub Φ Φ Λ η
  rw [h]
  exact measurable_const

omit [Countable S] in
protected lemma symm [IsSummable Φ] [IsSummable Ψ] (h : IsEquivalent Φ Ψ) :
    IsEquivalent Ψ Φ := fun Λ ↦ by
  classical
  have hne : (Ψ - Φ).hamiltonian Λ = fun η ↦ -((Φ - Ψ).hamiltonian Λ η) := by
    funext η
    rw [hamiltonian_sub Ψ Φ Λ η, hamiltonian_sub Φ Ψ Λ η]
    ring
  rw [hne]
  exact (h Λ).neg

omit [Countable S] in
protected lemma trans {Θ : Potential S E} [IsSummable Φ] [IsSummable Ψ] [IsSummable Θ]
    (h₁ : IsEquivalent Φ Ψ) (h₂ : IsEquivalent Ψ Θ) : IsEquivalent Φ Θ := fun Λ ↦ by
  classical
  have hadd : (Φ - Θ).hamiltonian Λ
      = fun η ↦ (Φ - Ψ).hamiltonian Λ η + (Ψ - Θ).hamiltonian Λ η := by
    funext η
    rw [hamiltonian_sub Φ Θ Λ η, hamiltonian_sub Φ Ψ Λ η,
      hamiltonian_sub Ψ Θ Λ η]
    ring
  rw [hadd]
  exact (h₁ Λ).add (h₂ Λ)

end IsEquivalent

omit [Countable S] in
/-- The Boltzmann factor of a difference of potentials splits off multiplicatively. -/
lemma boltzmannFactor_eq_mul_sub [IsSummable Φ] [IsSummable Ψ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η
      = (Φ - Ψ).boltzmannFactor β Λ η * Ψ.boltzmannFactor β Λ η := by
  classical
  have hsub := hamiltonian_sub Φ Ψ Λ η
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
    simp [hg, boltzmannFactor, Real.exp_pos]
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

/-! ### Recentring, and the oscillation seminorm -/

section Centring
omit [Countable S]

variable (Φ) in
/-- `∑_{A ∋ i} δ(Φ_A)`, the total oscillation at `i` of the interaction terms containing `i`.
Adding constants to the `Φ_A` leaves it unchanged (`Potential.oscNormAt_centre`), so unlike
`Potential.normAt` it sees only the interaction. -/
noncomputable def oscNormAt (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {A : Finset S | i ∈ A}.indicator (fun A ↦ _root_.oscOutside (∅ : Set S) (Φ A)) A

variable (Φ) in
/-- `Φ` recentred at `η₀`: the potential whose terms are `Φ_A - Φ_A(η₀)`. -/
def centre (η₀ : S → E) : Potential S E := fun A η ↦ Φ A η - Φ A η₀

@[simp] lemma centre_apply (η₀ : S → E) (A : Finset S) (η : S → E) :
    Φ.centre η₀ A η = Φ A η - Φ A η₀ := rfl

lemma hamiltonianTerms_centre (η₀ : S → E) (Λ : Finset S) (η : S → E) :
    (Φ.centre η₀).hamiltonianTerms Λ η = Φ.hamiltonianTerms Λ η - Φ.hamiltonianTerms Λ η₀ := by
  funext A
  by_cases h : Disjoint A Λ <;>
    simp [hamiltonianTerms, h]

instance instIsPotentialCentre [IsPotential Φ] (η₀ : S → E) : IsPotential (Φ.centre η₀) :=
  ⟨fun Δ ↦ (IsPotential.measurable (Φ := Φ) Δ).sub measurable_const⟩

instance instIsSummableCentre [IsSummable Φ] (η₀ : S → E) : IsSummable (Φ.centre η₀) :=
  ⟨fun Λ η ↦ by
    rw [hamiltonianTerms_centre]
    exact (IsSummable.summable (Φ := Φ) Λ η).sub (IsSummable.summable (Φ := Φ) Λ η₀)⟩

/-- Recentring changes the Hamiltonian by the constant `H_Λ^Φ(η₀)`. -/
lemma hamiltonian_sub_centre (η₀ : S → E) (Λ : Finset S) (η : S → E) :
    (Φ - Φ.centre η₀).hamiltonian Λ η = Φ.hamiltonian Λ η₀ := by
  rw [hamiltonian, hamiltonian]
  congr 1
  funext A
  by_cases h : Disjoint A Λ <;>
    simp [hamiltonianTerms, h]

/-- Recentring stays inside the equivalence class of Georgii (2.33). -/
lemma isEquivalent_centre (η₀ : S → E) : IsEquivalent Φ (Φ.centre η₀) := fun Λ ↦ by
  rw [show (Φ - Φ.centre η₀).hamiltonian Λ = fun _ ↦ Φ.hamiltonian Λ η₀ from
    funext (hamiltonian_sub_centre η₀ Λ)]
  exact measurable_const

lemma oscOutside_centre (η₀ : S → E) (A : Finset S) :
    _root_.oscOutside (∅ : Set S) (Φ.centre η₀ A) = _root_.oscOutside (∅ : Set S) (Φ A) := by
  simp only [_root_.oscOutside, centre_apply, edist_eq_enorm_sub, sub_sub_sub_cancel_right]

@[simp] lemma oscNormAt_centre (η₀ : S → E) (i : S) : (Φ.centre η₀).oscNormAt i = Φ.oscNormAt i
    := by
  simp only [oscNormAt, oscOutside_centre]

/-- Centring makes `‖·‖ᵢ` collapse onto the oscillation: this is the point of the normalisation
Georgii performs at the start of the proof of Theorem (8.39). -/
lemma normAt_centre_le (η₀ : S → E) (i : S) : (Φ.centre η₀).normAt i ≤ Φ.oscNormAt i := by
  rw [normAt, oscNormAt]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h : A ∈ ({A : Finset S | i ∈ A} : Set (Finset S))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact iSup_le fun η ↦ by
      rw [centre_apply, ← edist_eq_enorm_sub]; exact le_oscOutside (by simp)
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]

lemma oscNormAt_le_two_mul_normAt (i : S) : Φ.oscNormAt i ≤ 2 * Φ.normAt i := by
  rw [oscNormAt, normAt, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h : A ∈ ({A : Finset S | i ∈ A} : Set (Finset S))
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    refine oscOutside_le fun ζ η _ ↦ ?_
    rw [edist_eq_enorm_sub, two_mul]
    exact enorm_sub_le.trans
      (add_le_add (le_iSup (fun η ↦ ‖Φ A η‖ₑ) ζ) (le_iSup (fun η ↦ ‖Φ A η‖ₑ) η))
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma oscNormAt_ne_top [Φ.IsAbsolutelySummable] (i : S) : Φ.oscNormAt i ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (IsAbsolutelySummable.normAt_ne_top i))
    (oscNormAt_le_two_mul_normAt i)

/-- **Recentring criterion** (cf. the normalisation `‖Φ_A‖ = δ(Φ_A)/2` in the proof of Georgii
Theorem (8.39); §2.4 states no oscillation criterion). Some recentring `Φ.centre η₀` of `Φ` is
absolutely summable iff the total oscillation `∑_{A ∋ i} δ(Φ_A)` is finite at every site; since
`Φ.centre η₀` is equivalent to `Φ` (`isEquivalent_centre`), the class of `Φ` then meets `ℬ`.
The converse for the whole equivalence class fails: for `Φ_{{0,1}} η = f (η 0)`,
`Φ_{{0,2}} η = -f (η 0)` with `f` unbounded and all other terms `0`, `Φ` is equivalent to the zero
potential of `ℬ` while `Φ.oscNormAt 0 = ⊤`. -/
theorem isAbsolutelySummable_centre_iff [Nonempty E] :
    (∃ η₀ : S → E, (Φ.centre η₀).IsAbsolutelySummable) ↔ ∀ i, Φ.oscNormAt i ≠ ⊤ := by
  refine ⟨fun ⟨η₀, _⟩ i ↦ ?_, fun h ↦ ⟨fun _ ↦ Classical.arbitrary E, ⟨fun i ↦
    ne_top_of_le_ne_top (h i) (normAt_centre_le _ i)⟩⟩⟩
  rw [← oscNormAt_centre (Φ := Φ) η₀ i]
  exact oscNormAt_ne_top i

end Centring

end Potential

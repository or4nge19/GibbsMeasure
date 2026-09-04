/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Topology.MetricSpace.DependsOn
public import GibbsMeasure.Potential.FiniteReference
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

* `Potential.isEquivalent_of_sigmaFinitePremodifierNorm_eq` and
  `Potential.isEquivalent_iff_sigmaFinitePremodifierNorm_eq`: Georgii (2.34), (ii) ⇒ (i) and
  hence (i) ⇔ (ii). The `DependsOn` form is
  `Potential.dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq`.
* `Potential.isUniformlyConvergent_of_isAbsolutelySummable`: Georgii, (2.11) ⇒ (2.13) — an
  absolutely summable potential is uniformly convergent, so the uniform-convergence hypothesis of
  (2.34) and (2.35) is automatic on `Potential.absolutelySummable`.
* `Potential.continuous_hamiltonian_of_isUniformlyConvergent`: a uniformly convergent potential
  with continuous interactions has continuous Hamiltonians — the continuity input Georgii uses in
  (2.34).
* `Potential.isEquivalent_of_lambdaSpecification_eq`,
  `Potential.isEquivalent_iff_lambdaSpecification_eq`: Georgii (2.34), (iii) ⇒ (i) and (i) ⇔ (iii),
  for an everywhere dense a priori measure (`MeasureTheory.Measure.IsOpenPosMeasure`) and
  continuous `H_Λ^{Φ-Ψ}`.
* `Potential.isOpenPosMeasure_of_isGibbsMeasure`: Georgii, Remark (1.28)(2) — a Gibbs measure of a
  λ-specification with positive density is everywhere dense as soon as `λ` is.
* `Potential.isEquivalent_of_isGibbsMeasure`,
  `Potential.isEquivalent_iff_exists_common_isGibbsMeasure`,
  `Potential.isEquivalent_of_isGibbsMeasure_gibbsSpecification`: Georgii (2.34), (iv) ⇒ (i) and
  (i) ⇔ (iv) under `𝒢(Φ) ∪ 𝒢(Ψ) ≠ ∅`.
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

/-! ### Georgii (2.34): the converse implications

The direct implications (i) ⇒ (ii) ⇒ (iii) are above. Here we close the circle: (ii) ⇒ (i) is
already available in `DependsOn` form from `Potential.dependsOn_hamiltonian_sub_of_`
`sigmaFinitePremodifierNorm_eq`, and (iii) ⇒ (ii) and (iv) ⇒ (i) need Georgii's topological
hypotheses — a topology on `E` whose Borel sets are `𝓔`, an *everywhere dense* a priori measure
(`MeasureTheory.Measure.IsOpenPosMeasure`), and continuity of `H_Λ^{Φ-Ψ}`. -/

/-! ### Continuity of the Hamiltonians

Georgii states (2.34) (iii) ⇒ (ii) and (iv) ⇒ (i) under continuity of the interactions
`Φ_A - Ψ_A`; in the proof of (iv) ⇒ (i) he notes that what is actually used is that
`H_Λ^{Φ-Ψ}` is a *uniform* limit of continuous functions, "and thereby continuous". Continuity of
the individual interactions alone does not give continuity of the sum, so uniform convergence
(Georgii (2.13)) is recorded as a hypothesis wherever the Hamiltonian has to be continuous. -/

/-! ### Georgii (2.11) ⇒ (2.13): absolute summability gives uniform convergence -/

omit [Countable S] in
/-- **Georgii, (2.11) ⇒ (2.13).** An absolutely summable potential is uniformly convergent.

The tail `∑_{A ⊄ Δ, A ∩ Λ ≠ ∅} ‖Φ_A‖` of the Hamiltonian series in `Λ` is bounded by a quantity
that does not depend on the configuration, so the partial Hamiltonians converge uniformly. This
is what makes the uniform-convergence hypothesis of Georgii (2.34) and (2.35) automatic on
`Potential.absolutelySummable`, hence on `Potential.BTheta`. -/
theorem isUniformlyConvergent_of_isAbsolutelySummable [Φ.IsAbsolutelySummable] :
    IsUniformlyConvergent Φ := by
  classical
  intro Λ ε hε
  obtain ⟨F, hF⟩ :=
    ((tendsto_order.1 (ENNReal.tendsto_tsum_compl_atTop_zero
      (tsum_termNorm_ne_top (Φ := Φ) Λ))).2 _ (ENNReal.ofReal_pos.2 hε)).exists
  refine ⟨F.sup id, fun Δ hΔ η ↦ ?_⟩
  have hsub : ∀ A : Finset S, A ∉ Δ.powerset → A ∉ F := fun A hA hAF ↦
    hA (Finset.mem_powerset.2 ((Finset.le_sup (f := id) hAF).trans hΔ))
  have hs : Summable (Φ.hamiltonianTerms Λ η) := summable_hamiltonianTerms Λ η
  have key : ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A - Φ.hamiltonian Λ η
      = -∑' A : ↑((Δ.powerset : Set (Finset S))ᶜ), Φ.hamiltonianTerms Λ η A := by
    rw [hamiltonian_eq_tsum (Φ := Φ) Λ η, ← hs.sum_add_tsum_compl (s := Δ.powerset)]
    ring
  rw [key, abs_neg, ← ENNReal.ofReal_le_ofReal_iff hε.le, ← Real.enorm_eq_ofReal_abs]
  have hF' : ∑' A : ↑((F : Set (Finset S))ᶜ), Φ.termNorm Λ A < ENNReal.ofReal ε := hF
  refine le_trans enorm_tsum_le_tsum_enorm (le_trans ?_ hF'.le)
  rw [tsum_subtype ((Δ.powerset : Set (Finset S))ᶜ) fun A ↦ ‖Φ.hamiltonianTerms Λ η A‖ₑ,
    tsum_subtype ((F : Set (Finset S))ᶜ) (Φ.termNorm Λ)]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases hA : A ∈ ((Δ.powerset : Set (Finset S))ᶜ)
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show A ∈ ((F : Set (Finset S))ᶜ) from hsub A (by simpa using hA))]
    exact enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
  · rw [Set.indicator_of_notMem hA]
    exact bot_le

section Continuity

variable [TopologicalSpace E]

omit [Countable S] in
/-- The partial Hamiltonians `∑_{A ⊆ Δ, A ∩ Λ ≠ ∅} Φ_A` of a potential with continuous
interactions are continuous. -/
lemma continuous_sum_hamiltonianTerms (hc : ∀ A : Finset S, Continuous (Φ A))
    (Λ Δ : Finset S) :
    Continuous fun η : S → E ↦ ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A := by
  classical
  refine continuous_finsetSum _ fun A _ ↦ ?_
  by_cases hA : Disjoint A Λ
  · simpa only [hamiltonianTerms_of_disjoint hA] using continuous_const
  · simpa only [hamiltonianTerms_of_not_disjoint hA] using hc A

omit [Countable S] in
/-- **A uniformly convergent potential with continuous interactions has continuous Hamiltonians.**
This is the continuity input to Georgii (2.34), (iii) ⇒ (ii) and (iv) ⇒ (i). -/
theorem continuous_hamiltonian_of_isUniformlyConvergent [IsSummable Φ]
    (hu : IsUniformlyConvergent Φ) (hc : ∀ A : Finset S, Continuous (Φ A)) (Λ : Finset S) :
    Continuous (Φ.hamiltonian Λ) := by
  classical
  set F : Finset S → (S → E) → ℝ :=
    fun Δ η ↦ ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A with hF
  have hTU : TendstoUniformly F (Φ.hamiltonian Λ) (Filter.atTop : Filter (Finset S)) := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨Δ₀, hΔ₀⟩ := hu Λ (half_pos hε)
    filter_upwards [Filter.eventually_ge_atTop Δ₀] with Δ hΔ η
    have h := hΔ₀ Δ hΔ η
    rw [Real.dist_eq, abs_sub_comm]
    linarith [half_lt_self hε]
  exact hTU.continuous (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun Δ ↦ continuous_sum_hamiltonianTerms hc Λ Δ))

end Continuity


section Converse

/-- **Georgii (2.34), (ii) ⇒ (i).** Two `λ`-admissible potentials which define the same
`λ`-modification are equivalent in the sense of Definition (2.33). This is
`Potential.dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq` upgraded from `DependsOn`
to `𝓣_Λ`-measurability by `Measurable.cylinderEvents_of_dependsOn`. -/
theorem isEquivalent_of_sigmaFinitePremodifierNorm_eq [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    (heq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1)) :
    IsEquivalent Φ Ψ := by
  have : IsPotential (Φ - Ψ) := isPotential_sub
  have : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  exact fun Λ ↦ (measurable_hamiltonian (Φ := Φ - Ψ) Λ).cylinderEvents_of_dependsOn
    (dependsOn_hamiltonian_sub_of_sigmaFinitePremodifierNorm_eq ν hΦ hΨ heq Λ)

/-- **Georgii (2.34), (i) ⇔ (ii).** For `λ`-admissible potentials, equivalence of potentials is
exactly equality of the associated `λ`-modifications. -/
theorem isEquivalent_iff_sigmaFinitePremodifierNorm_eq [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)) :
    IsEquivalent Φ Ψ ↔
      Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1)
        = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Ψ.boltzmannFactor 1) :=
  ⟨fun h ↦ sigmaFinitePremodifierNorm_eq_of_isEquivalent ν h 1,
    isEquivalent_of_sigmaFinitePremodifierNorm_eq ν hΦ hΨ⟩

omit [Countable S] in
/-- The pointwise form of `Potential.hamiltonian_sub_eq_log_sigmaFiniteLambdaZ`: wherever the two
normalized densities agree, `H_Λ^{Φ-Ψ} = log(Z_Λ^Ψ/Z_Λ^Φ)`. -/
lemma hamiltonian_sub_eq_log_sigmaFiniteLambdaZ_of_apply_eq [IsSummable Φ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    {Λ : Finset S} {ω : S → E}
    (h : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω
      = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (Ψ.boltzmannFactor 1) Λ ω) :
    (Φ - Ψ).hamiltonian Λ ω
      = Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ ω).toReal
        - Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ ω).toReal := by
  set ZΦ := Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ ω
    with hZΦ
  set ZΨ := Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Ψ.boltzmannFactor 1) Λ ω
    with hZΨ
  have hZΦpos : (0 : ℝ) < ZΦ.toReal := ENNReal.toReal_pos (hΦ Λ ω).1 (hΦ Λ ω).2
  have hZΨpos : (0 : ℝ) < ZΨ.toReal := ENNReal.toReal_pos (hΨ Λ ω).1 (hΨ Λ ω).2
  have hquot : Φ.boltzmannFactor 1 Λ ω / ZΦ = Ψ.boltzmannFactor 1 Λ ω / ZΨ := by
    simpa [Specification.sigmaFinitePremodifierNorm, hZΦ, hZΨ] using h
  have hreal : Real.exp (-1 * Φ.hamiltonian Λ ω) / ZΦ.toReal
      = Real.exp (-1 * Ψ.hamiltonian Λ ω) / ZΨ.toReal := by
    have h2 := congrArg ENNReal.toReal hquot
    rwa [ENNReal.toReal_div, ENNReal.toReal_div, toReal_boltzmannFactor,
      toReal_boltzmannFactor] at h2
  have hlog := congrArg Real.log hreal
  rw [Real.log_div (Real.exp_ne_zero _) hZΦpos.ne', Real.log_div (Real.exp_ne_zero _) hZΨpos.ne',
    Real.log_exp, Real.log_exp] at hlog
  rw [hamiltonian_sub Φ Ψ Λ ω]
  linarith

omit [SigmaFinite ν] in
/-- **Georgii (2.34), (i) ⇒ (iii)** for the Gibbsian specification of an absolutely summable
potential and a probability a priori measure: equivalent potentials have the same `γ^Φ`, hence
the same Gibbs measures. -/
theorem gibbsSpecificationOfAbsolutelySummable_eq_of_isEquivalent [IsProbabilityMeasure ν]
    [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ]
    (h : IsEquivalent Φ Ψ) (β : ℝ) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β
      = gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν β := by
  rw [← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Φ) ν β,
    ← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Ψ) ν β]
  exact lambdaSpecification_eq_of_isEquivalent ν h β
    (hZΦ := isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν β)
    (hZΨ := isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Ψ) ν β)

end Converse

/-! ### Georgii (2.34) under his topological hypotheses

`λ` *everywhere dense* is `MeasureTheory.Measure.IsOpenPosMeasure`; the `𝓔 = Borel` hypothesis
enters only through the requirement that the continuous functions in play be measurable, which is
already part of `IsPotential`. Georgii's second countability of the topology is not needed: the
finite-volume product `λ^Λ` is everywhere dense for any topology on `E`
(`MeasureTheory.Measure.pi.isOpenPosMeasure`). -/

section Dense

variable [TopologicalSpace E]

omit [Countable S] in
/-- Juxtaposition is continuous for the product topologies. (An observation about `juxt`; it
belongs next to `juxt` in `GibbsMeasure/Prereqs/Juxt.lean`.) -/
lemma continuous_juxt {Λ : Set S} (η : S → E) : Continuous (juxt Λ η) := by
  refine continuous_pi fun x ↦ ?_
  by_cases hx : x ∈ Λ
  · simpa only [juxt_apply_of_mem hx] using continuous_apply (⟨x, hx⟩ : Λ)
  · simpa only [juxt_apply_of_not_mem hx] using continuous_const

omit [Countable S] in
/-- The boundary configuration enters `juxt` continuously. (An observation about `juxt`; it
belongs next to `juxt` in `GibbsMeasure/Prereqs/Juxt.lean`.) -/
lemma continuous_juxt_boundary {Λ : Set S} (ζ : ↥Λ → E) :
    Continuous fun η : S → E ↦ juxt Λ η ζ := by
  refine continuous_pi fun x ↦ ?_
  by_cases hx : x ∈ Λ
  · simpa only [juxt_apply_of_mem hx] using continuous_const
  · simpa only [juxt_apply_of_not_mem hx] using continuous_apply x

variable [ν.IsOpenPosMeasure]

/-- **The core of Georgii's density argument in (2.34).** If the two normalized densities agree
`λ_Λ(·|ω)`-almost everywhere and `H_Λ^{Φ-Ψ}` is continuous, then `H_Λ^{Φ-Ψ}` equals
`log(Z_Λ^Ψ(ω)/Z_Λ^Φ(ω))` at *every* configuration that agrees with `ω` off `Λ`: the exceptional
set is open, and an everywhere dense `λ` has no nonempty open null set. -/
lemma hamiltonian_sub_juxt_eq_log_sigmaFiniteLambdaZ [IsPotential Φ] [IsSummable Φ]
    [IsPotential Ψ] [IsSummable Ψ]
    (hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1))
    (hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1))
    {Λ : Finset S} (hcont : Continuous ((Φ - Ψ).hamiltonian Λ)) {ω : S → E}
    (hz : Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω
        {y | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
              (Φ.boltzmannFactor 1) Λ y
            ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
              (Ψ.boltzmannFactor 1) Λ y} = 0)
    (ζ : ↥(Λ : Set S) → E) :
    (Φ - Ψ).hamiltonian Λ (juxt (Λ : Set S) ω ζ)
      = Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ ω).toReal
        - Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ ω).toReal := by
  classical
  have hPsub : IsPotential (Φ - Ψ) := isPotential_sub
  have hSsub : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  set c : ℝ := Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
      (Ψ.boltzmannFactor 1) Λ ω).toReal
    - Real.log (Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν
      (Φ.boltzmannFactor 1) Λ ω).toReal with hc
  set N : Set (S → E) :=
    {y | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ y
      ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (Ψ.boltzmannFactor 1) Λ y} with hNdef
  have hNmeas : MeasurableSet N :=
    (measurableSet_eq_fun
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Φ.boltzmannFactor 1) ν (isPremodifier_boltzmannFactor (Φ := Φ) 1) Λ)
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Ψ.boltzmannFactor 1) ν (isPremodifier_boltzmannFactor (Φ := Ψ) 1) Λ)).compl
  have hpre : (Measure.pi fun _ : Λ ↦ ν) (juxt (Λ : Set S) ω ⁻¹' N) = 0 := by
    rw [← Measure.map_apply (Measurable.juxt (Λ := (Λ : Set S)) (η := ω) (𝓔 := mE)) hNmeas,
      ← Specification.sigmaFiniteLambdaFun_apply_eq_map ν Λ ω]
    exact hz
  set U : Set (↥(Λ : Set S) → E) :=
    {ξ | (Φ - Ψ).hamiltonian Λ (juxt (Λ : Set S) ω ξ) ≠ c} with hUdef
  have hUopen : IsOpen U :=
    isOpen_ne_fun (hcont.comp (continuous_juxt (Λ := (Λ : Set S)) ω)) continuous_const
  have hsub : U ⊆ juxt (Λ : Set S) ω ⁻¹' N := by
    intro ξ hξ
    by_contra hmem
    refine hξ ?_
    have hEq : Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (Φ.boltzmannFactor 1) Λ (juxt (Λ : Set S) ω ξ)
        = Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (Ψ.boltzmannFactor 1) Λ (juxt (Λ : Set S) ω ξ) := by
      simpa [hNdef, Set.mem_preimage] using hmem
    have hζx : ∀ s ∉ Λ, juxt (Λ : Set S) ω ξ s = ω s := fun s hs ↦ by
      rw [juxt_apply_of_not_mem (by simpa using hs)]
    rw [hamiltonian_sub_eq_log_sigmaFiniteLambdaZ_of_apply_eq ν hΦ hΨ hEq,
      Specification.sigmaFiniteLambdaZ_congr_of_eqOn_compl (ρ := Ψ.boltzmannFactor 1) ν
        (measurable_boltzmannFactor (Φ := Ψ) 1 Λ) hζx,
      Specification.sigmaFiniteLambdaZ_congr_of_eqOn_compl (ρ := Φ.boltzmannFactor 1) ν
        (measurable_boltzmannFactor (Φ := Φ) 1 Λ) hζx]
  have hUempty : U = ∅ :=
    hUopen.eq_empty_of_measure_zero (measure_mono_null hsub hpre)
  by_contra hne
  exact absurd (hUempty ▸ (show ζ ∈ U from hne)) (Set.notMem_empty ζ)

/-- **Georgii (2.34), (iii) ⇒ (i)**, and hence (iii) ⇒ (ii) by `sigmaFinitePremodifierNorm_eq_`
`of_isEquivalent`.

If two `λ`-admissible potentials define the same λ-specification, and the Hamiltonians of their
difference are continuous, then they are equivalent. Georgii's argument: `γ_Λ^Φ(·|ω) =
γ_Λ^Ψ(·|ω)` forces `λ^Λ(A_Λ) = 0` for the set `A_Λ` of interior configurations at which the two
densities differ; `A_Λ` is open because `H_Λ^{Φ-Ψ}` is continuous and the partition functions do
not depend on the interior, and `λ^Λ` is everywhere dense, so `A_Λ = ∅`. -/
theorem isEquivalent_of_lambdaSpecification_eq [NeZero ν]
    [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hcont : ∀ Λ : Finset S, Continuous ((Φ - Ψ).hamiltonian Λ))
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor 1)}
    {hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor 1)}
    {hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)}
    (heq : Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1) hρΦ hΦ
      = Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1) hρΨ hΨ) :
    IsEquivalent Φ Ψ := by
  classical
  have hPsub : IsPotential (Φ - Ψ) := isPotential_sub
  have hSsub : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  refine fun Λ ↦ (measurable_hamiltonian (Φ := Φ - Ψ) Λ).cylinderEvents_of_dependsOn ?_
  intro x y hxy
  have hz : Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ x
      {z | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ z
          ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ z} = 0 := by
    have h0 : (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ x).withDensity
          (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor 1) Λ)
        = (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ x).withDensity
          (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ) := by
      have h := congrArg (fun γ : Specification S E ↦ γ Λ x) heq
      simpa only [Specification.lambdaSpecification_apply] using h
    have hone : ∫⁻ z, Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (Φ.boltzmannFactor 1) Λ z ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ x)
          = 1 := by
      have h1 : Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1)
          hρΦ hΦ Λ x Set.univ = 1 := measure_univ
      rwa [Specification.lambdaSpecification_apply, withDensity_apply _ MeasurableSet.univ,
        setLIntegral_univ] at h1
    exact ae_iff.1 ((withDensity_eq_iff
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Φ.boltzmannFactor 1) ν hρΦ Λ).aemeasurable
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Ψ.boltzmannFactor 1) ν hρΨ Λ).aemeasurable
      (by rw [hone]; exact ENNReal.one_ne_top)).1 h0)
  have key := hamiltonian_sub_juxt_eq_log_sigmaFiniteLambdaZ ν hΦ hΨ (hcont Λ) hz
  have hx : juxt (Λ : Set S) x (fun i ↦ x (i : S)) = x := by
    funext s
    by_cases hs : s ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hs]
    · rw [juxt_apply_of_not_mem hs]
  have hy : juxt (Λ : Set S) x (fun i ↦ y (i : S)) = y := by
    funext s
    by_cases hs : s ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hs]
    · rw [juxt_apply_of_not_mem hs]
      exact hxy s (by simpa using hs)
  rw [← hx, ← hy, key, key]


variable [OpensMeasurableSpace E]

omit [Countable S] [TopologicalSpace E] [ν.IsOpenPosMeasure] [OpensMeasurableSpace E] in
/-- The normalized density of an admissible premodifier with everywhere positive weights is
everywhere positive. -/
lemma sigmaFinitePremodifierNorm_ne_zero {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (hpos : ∀ Λ ω, ρ Λ ω ≠ 0) (Λ : Finset S) (ω : S → E) :
    Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ ω ≠ 0 := by
  rw [Specification.sigmaFinitePremodifierNorm, Ne, ENNReal.div_eq_zero_iff]
  exact fun h ↦ h.elim (hpos Λ ω) (hZ Λ ω).2

omit [Countable S] in
/-- **Georgii, Remark (1.28)(2).** If the a priori measure `λ` is everywhere dense, so is every
Gibbs measure of a λ-specification whose density is everywhere positive: a nonempty open set
contains a nonempty open cylinder `C` over a finite volume `Λ`, and `γ_Λ(C|ω) > 0` for *every*
boundary condition `ω`, because `λ^Λ` charges the corresponding nonempty open box. -/
theorem isOpenPosMeasure_of_isGibbsMeasure [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    {hρ : Specification.IsPremodifier (S := S) (E := E) ρ}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ}
    (hpos : ∀ Λ ω, ρ Λ ω ≠ 0) {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ) :
    μ.IsOpenPosMeasure := by
  classical
  set γ := Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ with hγ
  refine ⟨fun U hU hUne ↦ ?_⟩
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨I, u, hu, hIU⟩ := isOpen_pi_iff.1 hU x hxU
  set C : Set (S → E) := (I : Set S).pi u with hC
  have hCmeas : MeasurableSet C :=
    MeasurableSet.pi I.countable_toSet fun a ha ↦ ((hu a (by simpa using ha)).1).measurableSet
  -- every finite-volume kernel charges `C`, uniformly in the boundary condition
  have hker : ∀ ω : S → E, γ I ω C ≠ 0 := by
    intro ω
    have hopen : IsOpen (juxt (I : Set S) ω ⁻¹' C) :=
      (isOpen_set_pi I.finite_toSet fun a ha ↦ (hu a (by simpa using ha)).1).preimage
        (continuous_juxt (Λ := (I : Set S)) ω)
    have hne : (juxt (I : Set S) ω ⁻¹' C).Nonempty := by
      refine ⟨fun i ↦ x (i : S), fun a ha ↦ ?_⟩
      rw [juxt_apply_of_mem (show a ∈ (I : Set S) from ha)]
      exact (hu a (by simpa using ha)).2
    have hkappa : Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν I ω C ≠ 0 := by
      rw [Specification.sigmaFiniteLambdaFun_apply_eq_map ν I ω,
        Measure.map_apply (Measurable.juxt (Λ := (I : Set S)) (η := ω) (𝓔 := mE)) hCmeas]
      exact (hopen.measure_pos _ hne).ne'
    rw [hγ, Specification.lambdaSpecification_apply, withDensity_apply _ hCmeas]
    intro hzero
    rw [setLIntegral_eq_zero_iff hCmeas
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E) (ρ := ρ) ν hρ I)]
      at hzero
    have h1 := ae_iff.1 hzero
    have h2 : {y : S → E | ¬ (y ∈ C →
        Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ I y = 0)} = C := by
      ext y
      simp only [Set.mem_ofPred_eq, not_imp]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, sigmaFinitePremodifierNorm_ne_zero ν hZ hpos I y⟩⟩
    rw [h2] at h1
    exact hkappa h1
  -- integrate over `μ`
  have hbind : μ.bind (γ I) = μ := (Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμ) I
  have hμC : μ C = ∫⁻ ω, γ I ω C ∂μ := by
    conv_lhs => rw [← hbind]
    exact Measure.bind_apply hCmeas
      ((γ I).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  have hCpos : μ C ≠ 0 := by
    rw [hμC]
    intro hzero
    have hae : ∀ᵐ ω ∂μ, γ I ω C = 0 := by
      have := (lintegral_eq_zero_iff ((Kernel.measurable_coe (γ I) hCmeas).mono
        cylinderEvents_le_pi le_rfl)).1 hzero
      filter_upwards [this] with ω hω using hω
    have h1 := ae_iff.1 hae
    have h2 : {ω : S → E | ¬ (γ I ω C = 0)} = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ hker ω
    rw [h2, measure_univ] at h1
    exact one_ne_zero h1
  exact fun hzero ↦ hCpos (measure_mono_null hIU hzero)

omit [Countable S] [TopologicalSpace E] [ν.IsOpenPosMeasure] [OpensMeasurableSpace E] in
/-- `μ γ_Λ = ρ_Λ · (μ λ_Λ)`: a λ-specification acts on a measure by resampling with the reference
kernel and then multiplying by the density. -/
lemma bind_lambdaSpecification_eq_withDensity [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hρ : Specification.IsPremodifier (S := S) (E := E) ρ)
    (hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ)
    (μ : Measure (S → E)) (Λ : Finset S) :
    μ.bind (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ)
      = (μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)).withDensity
          (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ) := by
  have hκ : AEMeasurable (fun ω ↦ Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω) μ :=
    ((Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ).measurable.mono
      cylinderEvents_le_pi le_rfl).aemeasurable
  have hρm := Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
    (ρ := ρ) ν hρ Λ
  ext A hA
  rw [Measure.bind_apply hA
      ((Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ).measurable.mono
        cylinderEvents_le_pi le_rfl).aemeasurable,
    withDensity_apply _ hA, ← lintegral_indicator hA,
    Measure.lintegral_bind hκ (hρm.indicator hA).aemeasurable]
  refine lintegral_congr fun ω ↦ ?_
  rw [lintegral_indicator hA, ← withDensity_apply _ hA,
    Specification.lambdaSpecification_apply]

/-- **Georgii (2.34), (iv) ⇒ (i).** If some probability measure is a Gibbs measure for the
λ-specifications of both potentials, and the Hamiltonians of their difference are continuous,
then the potentials are equivalent.

Georgii's argument: `ρ_Λ^Φ = ρ_Λ^Ψ` `μλ_Λ`-almost surely, so for `μ`-almost every boundary
condition `ω` the two densities agree `λ_Λ(·|ω)`-almost surely, and hence — the exceptional set
being open and `λ` everywhere dense — at *every* configuration agreeing with `ω` off `Λ`. Thus
`H_Λ^{Φ-Ψ}(ζω) = H_Λ^{Φ-Ψ}(ξω)` for `μ`-almost every `ω`; the two sides are continuous in `ω` and
`μ` is everywhere dense (`Potential.isOpenPosMeasure_of_isGibbsMeasure`), so the identity holds
for every `ω`. -/
theorem isEquivalent_of_isGibbsMeasure [NeZero ν]
    [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hcont : ∀ Λ : Finset S, Continuous ((Φ - Ψ).hamiltonian Λ))
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor 1)}
    {hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor 1)}
    {hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)}
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμΦ : (Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      hρΦ hΦ).IsGibbsMeasure μ)
    (hμΨ : (Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1)
      hρΨ hΨ).IsGibbsMeasure μ) :
    IsEquivalent Φ Ψ := by
  classical
  have hopen : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_isGibbsMeasure ν (fun Λ ω ↦ (boltzmannFactor_pos 1 Λ ω).ne') hμΦ
  have hPsub : IsPotential (Φ - Ψ) := isPotential_sub
  have hSsub : IsSummable (Φ - Ψ) := isSummable_sub Φ Ψ
  refine fun Λ ↦ (measurable_hamiltonian (Φ := Φ - Ψ) Λ).cylinderEvents_of_dependsOn ?_
  intro x y hxy
  have hNmeas : MeasurableSet
      {z : S → E | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ z
          ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ z} :=
    (measurableSet_eq_fun
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Φ.boltzmannFactor 1) ν hρΦ Λ)
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Ψ.boltzmannFactor 1) ν hρΨ Λ)).compl
  have hbΦ : (μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)).withDensity
      (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (Φ.boltzmannFactor 1) Λ) = μ := by
    rw [← bind_lambdaSpecification_eq_withDensity ν hρΦ hΦ μ Λ]
    exact (Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμΦ) Λ
  have hbΨ : (μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)).withDensity
      (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
        (Ψ.boltzmannFactor 1) Λ) = μ := by
    rw [← bind_lambdaSpecification_eq_withDensity ν hρΨ hΨ μ Λ]
    exact (Specification.isGibbsMeasure_iff_forall_bind_eq.1 hμΨ) Λ
  have hone : ∫⁻ z, Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
      (Φ.boltzmannFactor 1) Λ z
      ∂(μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)) = 1 := by
    have h1 : (μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)).withDensity
        (Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
          (Φ.boltzmannFactor 1) Λ) Set.univ = 1 := by
      rw [hbΦ]; exact measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h1
  have hmN : (μ.bind (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ))
      {z : S → E | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ z
          ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ z} = 0 :=
    ae_iff.1 ((withDensity_eq_iff
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Φ.boltzmannFactor 1) ν hρΦ Λ).aemeasurable
      (Specification.sigmaFinitePremodifierNorm_measurable (S := S) (E := E)
        (ρ := Ψ.boltzmannFactor 1) ν hρΨ Λ).aemeasurable
      (by rw [hone]; exact ENNReal.one_ne_top)).1 (hbΦ.trans hbΨ.symm))
  have hae : ∀ᵐ ω ∂μ, Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω
      {z : S → E | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Φ.boltzmannFactor 1) Λ z
          ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
            (Ψ.boltzmannFactor 1) Λ z} = 0 := by
    have h0 : ∫⁻ ω, Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω
        {z : S → E | Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
              (Φ.boltzmannFactor 1) Λ z
            ≠ Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν
              (Ψ.boltzmannFactor 1) Λ z} ∂μ = 0 := by
      rw [← Measure.bind_apply hNmeas
        ((Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ).measurable.mono
          cylinderEvents_le_pi le_rfl).aemeasurable]
      exact hmN
    filter_upwards [(lintegral_eq_zero_iff
      ((Kernel.measurable_coe (Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
        hNmeas).mono cylinderEvents_le_pi le_rfl)).1 h0] with ω hω using hω
  have hg : (fun ω : S → E ↦ (Φ - Ψ).hamiltonian Λ
        (juxt (Λ : Set S) ω (fun i ↦ x (i : S))))
      = fun ω : S → E ↦ (Φ - Ψ).hamiltonian Λ (juxt (Λ : Set S) ω (fun i ↦ y (i : S))) := by
    refine (Continuous.ae_eq_iff_eq μ ((hcont Λ).comp (continuous_juxt_boundary _))
      ((hcont Λ).comp (continuous_juxt_boundary _))).1 ?_
    filter_upwards [hae] with ω hω
    simp only [Function.comp_apply]
    rw [hamiltonian_sub_juxt_eq_log_sigmaFiniteLambdaZ ν hΦ hΨ (hcont Λ) hω,
      hamiltonian_sub_juxt_eq_log_sigmaFiniteLambdaZ ν hΦ hΨ (hcont Λ) hω]
  have hx : juxt (Λ : Set S) x (fun i ↦ x (i : S)) = x := by
    funext s
    by_cases hs : s ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hs]
    · rw [juxt_apply_of_not_mem hs]
  have hy : juxt (Λ : Set S) x (fun i ↦ y (i : S)) = y := by
    funext s
    by_cases hs : s ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hs]
    · rw [juxt_apply_of_not_mem hs]
      exact hxy s (by simpa using hs)
  have h := congrFun hg x
  rwa [hx, hy] at h

omit [OpensMeasurableSpace E] in
/-- **Georgii (2.34), (i) ⇔ (iii)** under his topological hypotheses. -/
theorem isEquivalent_iff_lambdaSpecification_eq [NeZero ν]
    [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hcont : ∀ Λ : Finset S, Continuous ((Φ - Ψ).hamiltonian Λ))
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor 1)}
    {hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor 1)}
    {hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)} :
    IsEquivalent Φ Ψ ↔
      Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1) hρΦ hΦ
        = Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1) hρΨ hΨ :=
  ⟨fun h ↦ lambdaSpecification_eq_of_isEquivalent ν h 1,
    isEquivalent_of_lambdaSpecification_eq ν hcont⟩

omit [TopologicalSpace E] [ν.IsOpenPosMeasure] [OpensMeasurableSpace E] in
/-- Equivalent potentials have the same Gibbs measures; this is `𝒢(Φ) = 𝒢(Ψ)`, the trivial half
of Georgii (2.34), (iii) ⇒ (iv). -/
theorem isGibbsMeasure_of_isEquivalent [NeZero ν]
    [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ] (h : IsEquivalent Φ Ψ)
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor 1)}
    {hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor 1)}
    {hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)}
    {μ : Measure (S → E)}
    (hμ : (Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1)
      hρΦ hΦ).IsGibbsMeasure μ) :
    (Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1)
      hρΨ hΨ).IsGibbsMeasure μ := by
  rwa [← lambdaSpecification_eq_of_isEquivalent (Φ := Φ) (Ψ := Ψ) ν h 1]

/-- **Georgii (2.34), (i) ⇔ (iv).** Under the hypothesis `𝒢(Φ) ∪ 𝒢(Ψ) ≠ ∅` — here: some
probability measure is a Gibbs measure for one of the two λ-specifications — the two potentials
are equivalent exactly when they have a *common* Gibbs measure. -/
theorem isEquivalent_iff_exists_common_isGibbsMeasure [NeZero ν]
    [IsPotential Φ] [IsSummable Φ] [IsPotential Ψ] [IsSummable Ψ]
    (hcont : ∀ Λ : Finset S, Continuous ((Φ - Ψ).hamiltonian Λ))
    {hρΦ : Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor 1)}
    {hΦ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor 1)}
    {hρΨ : Specification.IsPremodifier (S := S) (E := E) (Ψ.boltzmannFactor 1)}
    {hΨ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (Ψ.boltzmannFactor 1)}
    (hex : ∃ μ : Measure (S → E), IsProbabilityMeasure μ ∧
      ((Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1)
          hρΦ hΦ).IsGibbsMeasure μ ∨
        (Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1)
          hρΨ hΨ).IsGibbsMeasure μ)) :
    IsEquivalent Φ Ψ ↔ ∃ μ : Measure (S → E), IsProbabilityMeasure μ ∧
      (Specification.lambdaSpecification (S := S) (E := E) ν (Φ.boltzmannFactor 1)
          hρΦ hΦ).IsGibbsMeasure μ ∧
      (Specification.lambdaSpecification (S := S) (E := E) ν (Ψ.boltzmannFactor 1)
          hρΨ hΨ).IsGibbsMeasure μ := by
  refine ⟨fun h ↦ ?_, fun ⟨μ, hp, hμΦ, hμΨ⟩ ↦ ?_⟩
  · obtain ⟨μ, hp, hμ⟩ := hex
    refine ⟨μ, hp, ?_, ?_⟩
    · exact hμ.elim id fun hμΨ ↦ isGibbsMeasure_of_isEquivalent ν h.symm hμΨ
    · exact hμ.elim (fun hμΦ ↦ isGibbsMeasure_of_isEquivalent ν h hμΦ) id
  · exact isEquivalent_of_isGibbsMeasure ν hcont hμΦ hμΨ

omit [SigmaFinite ν] in
/-- **Georgii (2.34), (iv) ⇒ (i)** for the Gibbsian specification of an absolutely summable
potential and a probability a priori measure. -/
theorem isEquivalent_of_isGibbsMeasure_gibbsSpecification [IsProbabilityMeasure ν]
    [IsPotential Φ] [IsAbsolutelySummable Φ] [IsPotential Ψ] [IsAbsolutelySummable Ψ]
    (hcont : ∀ Λ : Finset S, Continuous ((Φ - Ψ).hamiltonian Λ))
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμΦ : (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν 1).IsGibbsMeasure μ)
    (hμΨ : (gibbsSpecificationOfAbsolutelySummable (Φ := Ψ) ν 1).IsGibbsMeasure μ) :
    IsEquivalent Φ Ψ := by
  rw [← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Φ) ν 1] at hμΦ
  rw [← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Ψ) ν 1] at hμΨ
  exact isEquivalent_of_isGibbsMeasure ν hcont
    (hΦ := isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Φ) ν 1)
    (hΨ := isSigmaFiniteLambdaAdmissible_boltzmannFactor (Φ := Ψ) ν 1) hμΦ hμΨ

end Dense

end Potential

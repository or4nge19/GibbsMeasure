/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable
public import GibbsMeasure.Specification.TailGluedSpecification

/-!
# Potentials whose Hamiltonian series converges only on a tail event

Georgii's Definition (2.2)(ii) asks the Hamiltonian series `H_Λ^Φ = ∑_{A ∩ Λ ≠ ∅} Φ_A` to converge
for *every* configuration; that is `Potential.IsSummable` in
`GibbsMeasure.Potential.Summable`.  Two of his constructions violate it — the Gaussian
specification (13.18) and the Heisenberg specification (20.5) over an unbounded state space — and
in both he replaces the requirement by convergence on a **tail-measurable** set `Ω_*`, defining the
specification to be a Dirac mass off `Ω_*`.

This file is that construction, for an arbitrary potential.  It combines
`Potential.hamiltonian` (Georgii (2.3)) with the gluing of
`GibbsMeasure.Specification.TailGluedSpecification`.

## Main declarations

* `Potential.IsSummableOn`: **Georgii (2.2)(ii) on a set of configurations**.
* `Potential.hamiltonian_sub_eq_of_mem`: **Georgii (2.6) on `Ω_*`** — for `Λ₁ ⊆ Λ₂` and two
  configurations of `Ω_*` agreeing off `Λ₁`, the Hamiltonian differences `H_{Λ₂} - H_{Λ₁}` agree.
* `Potential.tailBoltzmannFactor`: Georgii's `h_Λ^Φ = e^{-βH_Λ^Φ}` of (2.4) on `Ω_*`, completed by
  `1` off it, with `Potential.measurable_tailBoltzmannFactor` and
  `Potential.isPremodifierOn_tailBoltzmannFactor` (**Georgii Proposition (2.5) on `Ω_*`**).
* `Potential.tailGibbsSpecification`: **Georgii (13.18)/(20.5)** — the specification
  `γ_Λ^Φ(A|ω) = Z_Λ^Φ(ω)⁻¹ λ_Λ(1_A h_Λ^Φ|ω)` for `ω ∈ Ω_*` and `δ_{0_Λ ω_{S∖Λ}}(A)` otherwise,
  together with `tailGibbsSpecification_apply_of_mem`, `tailGibbsSpecification_apply_of_notMem`
  and `Potential.measure_eq_one_of_isGibbsMeasure_tailGibbsSpecification` (**Georgii (13.19)**).

## Why the completion by `1`, and not the Hamiltonian itself

`Potential.hamiltonian` is total: `∑'` of a non-summable family is `0`, so `H_Λ^Φ(ω)` has a value
for every `ω`.  What is *not* available off `Ω_*` is its measurability — the proof of
`Potential.measurable_hamiltonian` exhibits `H_Λ^Φ` as a pointwise limit of the partial sums, and
that limit exists only where the series converges.  `tailBoltzmannFactor` is therefore defined as
the piecewise function, whose measurability is the same limit argument carried out inside
`Set.piecewise` (`measurable_tailBoltzmannFactor`).  Off `Ω_*` its value is irrelevant: the gluing
of `Specification.gibbsOnTailSet` overwrites the whole kernel there by a Dirac mass.

## Hypotheses, against Georgii

* Georgii's a priori measure `λ ∈ 𝓜(E, ℰ)` is σ-finite; as in
  `Specification.gibbsOnTailSet`, the completion by `1` needs `λ` finite and non-zero.
* Countability of `S` is used for the measurability of the Boltzmann factor, exactly as in
  `Potential.measurable_hamiltonian`; Georgii's `S` is countable throughout.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped Topology ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} {Λ Λ₁ Λ₂ : Finset S}
  {Ω₀ : Set (S → E)}

/-! ### Georgii (2.2)(ii) and (2.6) on a set of configurations -/

variable (Φ Ω₀) in
/-- **Georgii, Definition (2.2)(ii), on a set of configurations.**  The Hamiltonian series
`H_Λ^Φ = ∑_{A ∩ Λ ≠ ∅} Φ_A` converges, in the sense of Convention (2.1), for every finite volume
and every boundary condition in `Ω₀`. -/
def IsSummableOn : Prop :=
  ∀ (Λ : Finset S) (η : S → E), η ∈ Ω₀ →
    Summable (Φ.hamiltonianTerms Λ η) (SummationFilter.volume S)

lemma IsSummableOn.hasSum (h : IsSummableOn Φ Ω₀) (Λ : Finset S) {η : S → E} (hη : η ∈ Ω₀) :
    HasSum (Φ.hamiltonianTerms Λ η) (Φ.hamiltonian Λ η) (SummationFilter.volume S) :=
  (h Λ η hη).hasSum

lemma IsSummable.isSummableOn [IsSummable Φ] : IsSummableOn Φ Ω₀ :=
  fun Λ η _ ↦ IsSummable.summable Λ η

/-- **Georgii (2.6) on `Ω₀`.**  For `Λ₁ ⊆ Λ₂` and two configurations of `Ω₀` which agree off `Λ₁`,
the differences `H_{Λ₂}^Φ - H_{Λ₁}^Φ` agree: every interaction term surviving the difference is
disjoint from `Λ₁`, hence depends only on the coordinates outside `Λ₁`.

This is the pointwise form of `Potential.dependsOn_hamiltonian_sub`, which assumes convergence
everywhere. -/
theorem hamiltonian_sub_eq_of_mem [IsPotential Φ] (h : IsSummableOn Φ Ω₀) (hΛ : Λ₁ ⊆ Λ₂)
    {ζ η : S → E} (hζ : ζ ∈ Ω₀) (hη : η ∈ Ω₀) (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) :
    Φ.hamiltonian Λ₂ ζ - Φ.hamiltonian Λ₁ ζ = Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η := by
  have hsζ := (h.hasSum Λ₂ hζ).sub (h.hasSum Λ₁ hζ)
  have hsη := (h.hasSum Λ₂ hη).sub (h.hasSum Λ₁ hη)
  have hEq : (fun A ↦ Φ.hamiltonianTerms Λ₂ ζ A - Φ.hamiltonianTerms Λ₁ ζ A)
      = fun A ↦ Φ.hamiltonianTerms Λ₂ η A - Φ.hamiltonianTerms Λ₁ η A := by
    funext A
    have e₁ : Φ.hamiltonianTerms Λ₂ ζ A - Φ.hamiltonianTerms Λ₁ ζ A
        = ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A ζ) A :=
      congrFun (hamiltonianTerms_sub (Φ := Φ) hΛ ζ) A
    have e₂ : Φ.hamiltonianTerms Λ₂ η A - Φ.hamiltonianTerms Λ₁ η A
        = ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A :=
      congrFun (hamiltonianTerms_sub (Φ := Φ) hΛ η) A
    rw [e₁, e₂]
    by_cases hA : A ∈ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}
    · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
      exact dependsOn_of_disjoint (Φ := Φ) hA.2 fun i hi ↦ hrestrict i (by simpa using hi)
    · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]
  exact hsζ.unique (by rwa [← hEq] at hsη)

/-! ### Georgii (2.4) and (2.5) on a tail event -/

variable (Φ Ω₀) in
/-- **Georgii's Boltzmann factor (2.4) on `Ω_*`**: `h_Λ^Φ = e^{-βH_Λ^Φ}` where the Hamiltonian
series converges, and `1` elsewhere.  The value off `Ω_*` is immaterial — the gluing of
`Specification.gibbsOnTailSet` replaces the whole kernel there — but it must be *some* measurable
admissible completion, and `1` is the simplest. -/
def tailBoltzmannFactor (β : ℝ) (Λ : Finset S) : (S → E) → ℝ≥0∞ :=
  open scoped Classical in Ω₀.piecewise (Φ.boltzmannFactor β Λ) 1

@[simp] lemma tailBoltzmannFactor_of_mem (β : ℝ) (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) :
    Φ.tailBoltzmannFactor Ω₀ β Λ ω = Φ.boltzmannFactor β Λ ω := by
  classical
  simpa [tailBoltzmannFactor] using
    Set.piecewise_eq_of_mem Ω₀ (Φ.boltzmannFactor β Λ) 1 hω

@[simp] lemma tailBoltzmannFactor_of_notMem (β : ℝ) (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    Φ.tailBoltzmannFactor Ω₀ β Λ ω = 1 := by
  classical
  simpa [tailBoltzmannFactor] using
    Set.piecewise_eq_of_notMem Ω₀ (Φ.boltzmannFactor β Λ) 1 hω

lemma tailBoltzmannFactor_pos (β : ℝ) (Λ : Finset S) (ω : S → E) :
    0 < Φ.tailBoltzmannFactor Ω₀ β Λ ω := by
  by_cases hω : ω ∈ Ω₀
  · rw [tailBoltzmannFactor_of_mem _ _ hω]; exact boltzmannFactor_pos _ _ _
  · rw [tailBoltzmannFactor_of_notMem _ _ hω]; exact one_pos

lemma tailBoltzmannFactor_ne_top (β : ℝ) (Λ : Finset S) (ω : S → E) :
    Φ.tailBoltzmannFactor Ω₀ β Λ ω ≠ ⊤ := by
  by_cases hω : ω ∈ Ω₀
  · rw [tailBoltzmannFactor_of_mem _ _ hω]; exact boltzmannFactor_ne_top _ _ _
  · rw [tailBoltzmannFactor_of_notMem _ _ hω]; exact ENNReal.one_ne_top

/-- The Boltzmann factor of a potential whose Hamiltonian series converges on a measurable set
`Ω₀`, completed by `1` off `Ω₀`, is measurable.  Georgii's `H_Λ^Φ` is a pointwise limit of its
partial sums *on* `Ω₀`; the limit is taken inside `Set.piecewise`. -/
theorem measurable_tailBoltzmannFactor [Countable S] [IsPotential Φ]
    (hΩmeas : MeasurableSet Ω₀) (h : IsSummableOn Φ Ω₀) (β : ℝ) (Λ : Finset S) :
    Measurable (Φ.tailBoltzmannFactor Ω₀ β Λ) := by
  classical
  refine measurable_of_tendsto_metrizable' (SummationFilter.volume S).filter
    (f := fun s : Finset (Finset S) ↦ Ω₀.piecewise
      (fun η ↦ ENNReal.ofReal (Real.exp (-β * ∑ A ∈ s, Φ.hamiltonianTerms Λ η A)))
      (1 : (S → E) → ℝ≥0∞))
    (fun s ↦ Measurable.piecewise hΩmeas
      (((measurable_const.mul (measurable_sum_hamiltonianTerms (Φ := Φ) Λ s)).exp).ennreal_ofReal)
      measurable_one)
    (tendsto_pi_nhds.2 fun η ↦ ?_)
  by_cases hη : η ∈ Ω₀
  · have hlim : Tendsto (fun s : Finset (Finset S) ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A)
        (SummationFilter.volume S).filter (𝓝 (Φ.hamiltonian Λ η)) := h.hasSum Λ hη
    have hcont : Continuous fun x : ℝ ↦ ENNReal.ofReal (Real.exp (-β * x)) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hcomp := (hcont.tendsto (Φ.hamiltonian Λ η)).comp hlim
    simpa [Set.piecewise_eq_of_mem Ω₀ _ _ hη, tailBoltzmannFactor, boltzmannFactor,
      Function.comp_def] using hcomp
  · simp [Set.piecewise_eq_of_notMem Ω₀ _ _ hη, tailBoltzmannFactor]

/-- **Georgii, Proposition (2.5), on a tail event.**  The Boltzmann factors of a potential whose
Hamiltonian series converges on a tail-measurable set `Ω_*` are a pre-modification *on* `Ω_*`. -/
theorem isPremodifierOn_tailBoltzmannFactor [Countable S] [IsPotential Φ]
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (h : IsSummableOn Φ Ω₀) (β : ℝ) :
    Specification.IsPremodifierOn (Φ.tailBoltzmannFactor Ω₀ β) Ω₀ where
  measurable Λ :=
    measurable_tailBoltzmannFactor
      (cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀))
      h β Λ
  comm_of_subset Λ₁ Λ₂ ζ η hΛ hζ hη hrestrict := by
    rw [tailBoltzmannFactor_of_mem _ _ hζ, tailBoltzmannFactor_of_mem _ _ hη,
      tailBoltzmannFactor_of_mem _ _ hζ, tailBoltzmannFactor_of_mem _ _ hη]
    have hH := hamiltonian_sub_eq_of_mem (Φ := Φ) h hΛ hζ hη hrestrict
    have hsum : Φ.hamiltonian Λ₂ ζ + Φ.hamiltonian Λ₁ η
        = Φ.hamiltonian Λ₁ ζ + Φ.hamiltonian Λ₂ η := by linarith
    simp only [boltzmannFactor, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    linear_combination (-β) * hsum

/-! ### Georgii (13.18)/(20.5): the Gibbsian specification of `Φ` on `Ω_*` -/

section Specification

variable {ν : Measure E} [IsFiniteMeasure ν] [NeZero ν]

variable (Φ Ω₀ ν) in
/-- **Georgii, Definition (13.18) and (20.5).**  The Gibbsian specification of a potential whose
Hamiltonian series converges on the tail event `Ω_*` and whose partition functions are finite and
non-zero there:

`γ_Λ^Φ(A | ω) = Z_Λ^Φ(ω)⁻¹ λ_Λ(1_A h_Λ^Φ | ω)` for `ω ∈ Ω_*`,  `δ_{0_Λ ω_{S∖Λ}}(A)` otherwise.

Georgii's `β` is absorbed into `Φ` in his notation; it is kept explicit here, as in
`Potential.boltzmannFactor`. -/
def tailGibbsSpecification [Countable S] [IsPotential Φ] [Zero E] (β : ℝ)
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (h : IsSummableOn Φ Ω₀)
    (hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
      Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.tailBoltzmannFactor Ω₀ β) Λ ω ≠ ⊤) :
    Specification S E :=
  Specification.gibbsOnTailSet ν (Φ.tailBoltzmannFactor Ω₀ β) Ω₀ hΩ₀
    (isPremodifierOn_tailBoltzmannFactor hΩ₀ h β)
    fun Λ ω hω ↦
      ⟨Specification.sigmaFiniteLambdaZ_ne_zero_of_pos Λ
        ((isPremodifierOn_tailBoltzmannFactor hΩ₀ h β).measurable Λ)
        (fun x ↦ tailBoltzmannFactor_pos β Λ x) ω,
      hZ Λ ω hω⟩

variable [Countable S] [IsPotential Φ] [Zero E] {β : ℝ}
  {hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀} {h : IsSummableOn Φ Ω₀}
  {hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
    Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.tailBoltzmannFactor Ω₀ β) Λ ω ≠ ⊤}

/-- **The Gibbsian branch of (13.18)/(20.5).** -/
theorem tailGibbsSpecification_apply_of_mem (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    tailGibbsSpecification Φ Ω₀ ν β hΩ₀ h hZ Λ ω A
      = (∫⁻ x, Φ.tailBoltzmannFactor Ω₀ β Λ x
            ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω))⁻¹
        * ∫⁻ x in A, Φ.tailBoltzmannFactor Ω₀ β Λ x
            ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω) :=
  Specification.gibbsOnTailSet_apply_of_mem Λ hω hA

/-- **The artificial branch of (13.18)/(20.5).** -/
theorem tailGibbsSpecification_apply_of_notMem (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    tailGibbsSpecification Φ Ω₀ ν β hΩ₀ h hZ Λ ω
      = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) :=
  Specification.gibbsOnTailSet_apply_of_notMem Λ hω

/-- **Georgii (13.19) for (13.18)/(20.5).**  `μ(Ω_*) = 1` for every `μ ∈ 𝒢(γ^Φ)`: "the artificial
part of the definition of `γ^Φ` has no effect on the associated class of Gibbs measures". -/
theorem measure_eq_one_of_isGibbsMeasure_tailGibbsSpecification
    (hE : MeasurableSet ({(0 : E)} : Set E)) (h0 : (0 : S → E) ∈ Ω₀)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (tailGibbsSpecification Φ Ω₀ ν β hΩ₀ h hZ).IsGibbsMeasure μ) :
    μ Ω₀ = 1 :=
  Specification.measure_eq_one_of_isGibbsMeasure_gibbsOnTailSet hE h0 hμ

end Specification

end Potential

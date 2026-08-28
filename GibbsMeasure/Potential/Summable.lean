/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential
public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.Volume
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Potentials and their Hamiltonians

Georgii's Definition (2.2) of an interaction potential: each `Φ A` is `𝓕_A`-measurable
(`Potential.IsPotential`) and the Hamiltonian series `H_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` converges in the sense
of Convention (2.1) (`Potential.IsSummable`).

`Potential.IsLocallyFinitary` is the special case in which the series has finite support.

## Main results

* `Potential.dependsOn_hamiltonian_sub`: Georgii (2.6).
* `Potential.isPremodifier_boltzmannFactor`: Georgii Proposition (2.5).
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] {Φ : Potential S E} {Λ Λ₁ Λ₂ : Finset S}

/-- The interaction terms entering the Hamiltonian in `Λ`, extended by zero. -/
def hamiltonianTerms (Φ : Potential S E) (Λ : Finset S) (η : S → E) : Finset S → ℝ :=
  {A | ¬ Disjoint A Λ}.indicator fun A ↦ Φ A η

lemma hamiltonianTerms_of_not_disjoint (h : ¬ Disjoint Λ₁ Λ) (η : S → E) :
    Φ.hamiltonianTerms Λ η Λ₁ = Φ Λ₁ η := Set.indicator_of_mem h _

lemma hamiltonianTerms_of_disjoint (h : Disjoint Λ₁ Λ) (η : S → E) :
    Φ.hamiltonianTerms Λ η Λ₁ = 0 := Set.indicator_of_notMem (by simpa using h) _

/-- Georgii, Definition (2.2)(ii). -/
class IsSummable (Φ : Potential S E) : Prop where
  summable (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) (SummationFilter.volume S)

/-- Georgii, eq. (2.3). -/
def hamiltonian (Φ : Potential S E) (Λ : Finset S) (η : S → E) : ℝ :=
  ∑'[SummationFilter.volume S] A, Φ.hamiltonianTerms Λ η A

lemma hasSum_hamiltonian [IsSummable Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (Φ.hamiltonian Λ η) (SummationFilter.volume S) :=
  (IsSummable.summable Λ η).hasSum

/-- Unconditional summability of the interaction terms suffices; Georgii (2.11) ⇒ (2.2)(ii). -/
lemma IsSummable.of_summable (h : ∀ (Λ : Finset S) (η : S → E), Summable (Φ.hamiltonianTerms Λ η)) :
    IsSummable Φ where
  summable Λ η := (h Λ η).volume

/-! ### The locally finitary case -/

lemma hamiltonianTerms_eq_zero_of_notMem_interactingSupport [IsLocallyFinitary Φ]
    (η : S → E) {A : Finset S} (hA : A ∉ interactingSupport (Φ := Φ) Λ) :
    Φ.hamiltonianTerms Λ η A = 0 := by
  by_cases hdisj : Disjoint A Λ
  · exact hamiltonianTerms_of_disjoint hdisj η
  · obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hdisj
    have hne : ((A : Set S) ∩ (Λ : Set S)).Nonempty := ⟨x, by simpa using hxA, by simpa using hxΛ⟩
    have : Φ A = 0 := by
      by_contra hΦ
      exact hA ((mem_interactingSupport (Φ := Φ)).2 ⟨hne, hΦ⟩)
    simp [hamiltonianTerms, this]

lemma hasSum_interactingHamiltonian [IsLocallyFinitary Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (interactingHamiltonian (Φ := Φ) Λ η)
      (SummationFilter.volume S) := by
  have h : HasSum (Φ.hamiltonianTerms Λ η)
      (∑ A ∈ interactingSupport (Φ := Φ) Λ, Φ.hamiltonianTerms Λ η A) :=
    hasSum_sum_of_ne_finset_zero fun A hA ↦
      hamiltonianTerms_eq_zero_of_notMem_interactingSupport (Φ := Φ) η hA
  have hsum : (∑ A ∈ interactingSupport (Φ := Φ) Λ, Φ.hamiltonianTerms Λ η A)
      = interactingHamiltonian (Φ := Φ) Λ η := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    obtain ⟨⟨x, hxA, hxΛ⟩, -⟩ := (mem_interactingSupport (Φ := Φ)).1 hA
    exact hamiltonianTerms_of_not_disjoint
      (Finset.not_disjoint_iff.2 ⟨x, by simpa using hxA, by simpa using hxΛ⟩) η
  exact hsum ▸ h.volume

instance (priority := 100) IsLocallyFinitary.isSummable [IsLocallyFinitary Φ] : IsSummable Φ where
  summable Λ η := ⟨_, hasSum_interactingHamiltonian (Φ := Φ) Λ η⟩

@[simp] lemma hamiltonian_eq_interactingHamiltonian [IsLocallyFinitary Φ]
    (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = interactingHamiltonian (Φ := Φ) Λ η :=
  (hasSum_interactingHamiltonian (Φ := Φ) Λ η).tsum_eq

/-! ### Georgii (2.6) -/

/-- The terms of `H_Λ₂ - H_Λ₁`, for `Λ₁ ⊆ Λ₂`; Georgii (2.6). -/
lemma hamiltonianTerms_sub (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonianTerms Λ₂ η - Φ.hamiltonianTerms Λ₁ η
      = {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η := by
  funext A
  by_cases h₁ : Disjoint A Λ₁
  · by_cases h₂ : Disjoint A Λ₂
    · simp [hamiltonianTerms, Set.indicator_of_notMem, h₁, h₂, not_not]
    · rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_disjoint h₁,
        Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
          ⟨h₂, h₁⟩), sub_zero]
  · have h₂ : ¬ Disjoint A Λ₂ := fun h ↦ h₁ (h.mono_right hΛ)
    rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_not_disjoint h₁,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
        fun h ↦ h₁ h.2), sub_self]

/-- An interaction term disjoint from `Λ` depends only on the coordinates outside `Λ`. -/
lemma dependsOn_of_disjoint [IsPotential Φ] {A : Finset S} (hA : Disjoint A Λ) :
    DependsOn (Φ A) ((Λ : Set S)ᶜ) :=
  ((IsPotential.measurable (Φ := Φ) A).dependsOn_of_cylinderEvents).mono fun x hx hxΛ ↦
    (Finset.disjoint_left.1 hA (by simpa using hx)) (by simpa using hxΛ)

lemma dependsOn_sum_hamiltonianTerms_sub [IsPotential Φ] (Λ₁ Λ₂ : Finset S)
    (s : Finset (Finset S)) :
    DependsOn (fun η ↦ ∑ A ∈ s,
      ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A)
      ((Λ₁ : Set S)ᶜ) := by
  refine DependsOn.sum fun A _ x y hxy ↦ ?_
  by_cases hA : ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁
  · have hmem : A ∈ {B : Finset S | ¬ Disjoint B Λ₂ ∧ Disjoint B Λ₁} := hA
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    exact dependsOn_of_disjoint (Φ := Φ) hA.2 hxy
  · have hmem : A ∉ {B : Finset S | ¬ Disjoint B Λ₂ ∧ Disjoint B Λ₁} := hA
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **Georgii (2.6).** For `Λ₁ ⊆ Λ₂` the Hamiltonian difference is `𝓕_{Λ₁ᶜ}`-measurable. -/
theorem dependsOn_hamiltonian_sub [IsPotential Φ] [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) :
    DependsOn (fun η ↦ Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) ((Λ₁ : Set S)ᶜ) := by
  refine DependsOn.of_tendsto (l := (SummationFilter.volume S).filter)
    (F := fun s η ↦ ∑ A ∈ s,
      ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A)
    (fun s ↦ dependsOn_sum_hamiltonianTerms_sub (Φ := Φ) Λ₁ Λ₂ s) fun η ↦ ?_
  have h := (hasSum_hamiltonian (Φ := Φ) Λ₂ η).sub (hasSum_hamiltonian (Φ := Φ) Λ₁ η)
  have heq : ∀ A, Φ.hamiltonianTerms Λ₂ η A - Φ.hamiltonianTerms Λ₁ η A
      = ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A :=
    fun A ↦ congrFun (hamiltonianTerms_sub (Φ := Φ) hΛ η) A
  simpa only [HasSum, heq] using h

theorem hamiltonian_sub_eq_of_subset_eqOn_compl [IsPotential Φ] [IsSummable Φ] {η ζ : S → E}
    (hΛ : Λ₁ ⊆ Λ₂) (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) :
    Φ.hamiltonian Λ₁ η - Φ.hamiltonian Λ₁ ζ = Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₂ ζ := by
  have h := dependsOn_hamiltonian_sub (Φ := Φ) hΛ (x := ζ) (y := η)
    fun i hi ↦ hrestrict i (by simpa using hi)
  linarith [h]

/-! ### Georgii Proposition (2.5) -/

lemma measurable_sum_hamiltonianTerms [IsPotential Φ] (Λ : Finset S) (s : Finset (Finset S)) :
    Measurable fun η : S → E ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A := by
  refine Finset.measurable_sum _ fun A _ ↦ ?_
  by_cases hA : Disjoint A Λ
  · simpa only [hamiltonianTerms_of_disjoint hA] using measurable_const (a := (0 : ℝ))
  · simpa only [hamiltonianTerms_of_not_disjoint hA] using
      (IsPotential.measurable (Φ := Φ) A).mono cylinderEvents_le_pi le_rfl

lemma measurable_hamiltonian [Countable S] [IsPotential Φ] [IsSummable Φ] (Λ : Finset S) :
    Measurable (Φ.hamiltonian Λ) :=
  measurable_of_tendsto_metrizable' (SummationFilter.volume S).filter
    (fun s ↦ measurable_sum_hamiltonianTerms (Φ := Φ) Λ s)
    (tendsto_pi_nhds.2 fun η ↦ hasSum_hamiltonian (Φ := Φ) Λ η)

/-- Georgii, eq. (2.4). -/
def boltzmannFactor (Φ : Potential S E) (β : ℝ) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ η))

lemma measurable_boltzmannFactor [Countable S] [IsPotential Φ] [IsSummable Φ]
    (β : ℝ) (Λ : Finset S) : Measurable (Φ.boltzmannFactor β Λ) :=
  ((measurable_const.mul (measurable_hamiltonian (Φ := Φ) Λ)).exp).ennreal_ofReal

lemma boltzmannFactor_pos (β : ℝ) (Λ : Finset S) (η : S → E) : 0 < Φ.boltzmannFactor β Λ η := by
  simpa [boltzmannFactor] using Real.exp_pos (-β * Φ.hamiltonian Λ η)

lemma boltzmannFactor_ne_top (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η ≠ ⊤ := by simp [boltzmannFactor]

private lemma ofReal_exp_mul_comm {a b c d : ℝ} (h : a + b = c + d) :
    ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b)
      = ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp d) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add, h]

/-- **Georgii, Proposition (2.5).** The Boltzmann factors of a potential form a positive
pre-modification. -/
theorem isPremodifier_boltzmannFactor [Countable S] [IsPotential Φ] [IsSummable Φ] (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) where
  measurable Λ := measurable_boltzmannFactor (Φ := Φ) β Λ
  comm_of_subset {Λ₁ Λ₂ ζ η} hΛ hrestrict := by
    have hH := hamiltonian_sub_eq_of_subset_eqOn_compl (Φ := Φ) hΛ hrestrict
    refine ofReal_exp_mul_comm ?_
    have hsum : Φ.hamiltonian Λ₂ ζ + Φ.hamiltonian Λ₁ η
        = Φ.hamiltonian Λ₁ ζ + Φ.hamiltonian Λ₂ η := by linarith
    linear_combination (-β) * hsum

@[simp] lemma boltzmannFactor_eq_boltzmannWeight [DecidableEq S] [IsLocallyFinitary Φ]
    (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η = boltzmannWeight (Φ := Φ) β Λ η := by
  rw [boltzmannFactor, boltzmannWeight, hamiltonian_eq_interactingHamiltonian]

end Potential

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
(`Potential.IsPotential`) and the Hamiltonian series `H_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` converges in the
sense
of Convention (2.1) (`Potential.IsSummable`).

`Potential.IsFiniteRange` is the special case in which the series has finite support.

## Main results

* `Potential.dependsOn_hamiltonian_sub`: Georgii (2.6).
* `Potential.isPremodifier_boltzmannFactor`: Georgii Proposition (2.5).
* `Potential.IsAbsolutelySummable`: absolute summability, Georgii (2.11), with `‖Φ‖ᵢ` of (2.12); it
  implies `IsSummable` and bounds the Hamiltonian by Georgii (2.14). The space `ℬ` itself is the
  submodule `Potential.absolutelySummable` in `GibbsMeasure/Potential/Space.lean`.
* `Potential.gibbsSpecificationOfAbsolutelySummable`: Georgii Definition (2.9) for `Φ ∈ ℬ`.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
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

/-- Unconditional summability of the interaction terms suffices. -/
lemma IsSummable.of_summable (h : ∀ (Λ : Finset S) (η : S → E), Summable (Φ.hamiltonianTerms Λ η)) :
    IsSummable Φ where
  summable Λ η := (h Λ η).volume

/-! ### The locally finitary case -/

lemma hamiltonianTerms_eq_zero_of_notMem_interactingSupport [IsFiniteRange Φ]
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

lemma hasSum_interactingHamiltonian [IsFiniteRange Φ] (Λ : Finset S) (η : S → E) :
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

instance (priority := 100) IsFiniteRange.isSummable [IsFiniteRange Φ] : IsSummable Φ where
  summable Λ η := ⟨_, hasSum_interactingHamiltonian (Φ := Φ) Λ η⟩

@[simp] lemma hamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
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

/-- **Georgii (2.6).** For `Λ₁ ⊆ Λ₂` the Hamiltonian difference depends only on the coordinates
outside `Λ₁` — the `DependsOn` half of Georgii's `𝓣_{Λ₁}`-measurability. Full
`cylinderEvents (Λ₁ : Set S)ᶜ`-measurability follows for countable `S` by combining this with
`measurable_hamiltonian` (`Measurable.cylinderEvents_of_dependsOn`). -/
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

/-- **Georgii, Proposition (2.5).** The Boltzmann factors of a potential form a pre-modification.
The positivity in Georgii's statement is not part of `Specification.IsPremodifier`; it is the
separate lemma `Potential.boltzmannFactor_pos`. -/
theorem isPremodifier_boltzmannFactor [Countable S] [IsPotential Φ] [IsSummable Φ] (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) where
  measurable Λ := measurable_boltzmannFactor (Φ := Φ) β Λ
  comm_of_subset {Λ₁ Λ₂ ζ η} hΛ hrestrict := by
    have hH := hamiltonian_sub_eq_of_subset_eqOn_compl (Φ := Φ) hΛ hrestrict
    refine ofReal_exp_mul_comm ?_
    have hsum : Φ.hamiltonian Λ₂ ζ + Φ.hamiltonian Λ₁ η
        = Φ.hamiltonian Λ₁ ζ + Φ.hamiltonian Λ₂ η := by linarith
    linear_combination (-β) * hsum

@[simp] lemma boltzmannFactor_eq_boltzmannWeight [DecidableEq S] [IsFiniteRange Φ]
    (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η = boltzmannWeight (Φ := Φ) β Λ η := by
  rw [boltzmannFactor, boltzmannWeight, hamiltonian_eq_interactingHamiltonian]

/-! ### Absolutely summable potentials -/

/-- Georgii (2.12): `‖Φ‖ᵢ`, the total sup-norm of the interaction terms containing `i`. -/
def normAt (Φ : Potential S E) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

/-- Georgii (2.11): `Φ` is absolutely summable. -/
class IsAbsolutelySummable (Φ : Potential S E) : Prop where
  normAt_ne_top (i : S) : Φ.normAt i ≠ ⊤

variable (Φ) in
/-- The sup-norms of the interaction terms entering `H_Λ`, extended by zero. -/
def termNorm (Λ : Finset S) : Finset S → ℝ≥0∞ :=
  {A : Finset S | ¬ Disjoint A Λ}.indicator fun A ↦ ⨆ η, ‖Φ A η‖ₑ

lemma enorm_hamiltonianTerms_le_termNorm (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ Φ.termNorm Λ A := by
  by_cases h : Disjoint A Λ
  · have hnm : A ∉ {B : Finset S | ¬ Disjoint B Λ} := by simpa using h
    simp [hamiltonianTerms_of_disjoint h, termNorm, Set.indicator_of_notMem hnm]
  · rw [hamiltonianTerms_of_not_disjoint h, termNorm,
      Set.indicator_of_mem (show A ∈ {B : Finset S | ¬ Disjoint B Λ} from h)]
    exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η

lemma termNorm_le_sum (Λ : Finset S) (A : Finset S) :
    Φ.termNorm Λ A ≤ ∑ i ∈ Λ, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases h : Disjoint A Λ
  · have hnm : A ∉ {B : Finset S | ¬ Disjoint B Λ} := by simpa using h
    simp [termNorm, Set.indicator_of_notMem hnm]
  · obtain ⟨i, hiA, hiΛ⟩ := Finset.not_disjoint_iff.1 h
    refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦
      {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A) (fun _ _ ↦ bot_le) hiΛ)
    rw [termNorm, Set.indicator_of_mem (show A ∈ {B : Finset S | ¬ Disjoint B Λ} from h),
      Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hiA)]

lemma tsum_termNorm_le (Λ : Finset S) : ∑' A : Finset S, Φ.termNorm Λ A ≤ ∑ i ∈ Λ, Φ.normAt i := by
  refine le_trans (ENNReal.tsum_le_tsum (termNorm_le_sum (Φ := Φ) Λ)) ?_
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  exact le_of_eq (Finset.sum_congr rfl fun i _ ↦ rfl)

lemma sum_normAt_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    (∑ i ∈ Λ, Φ.normAt i) ≠ ⊤ :=
  (ENNReal.sum_lt_top.2 fun i _ ↦
    lt_top_iff_ne_top.2 (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)).ne

lemma tsum_termNorm_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ∑' A : Finset S, Φ.termNorm Λ A ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (tsum_termNorm_le (Φ := Φ) Λ)
    (lt_top_iff_ne_top.2 (sum_normAt_ne_top (Φ := Φ) Λ)))

lemma termNorm_ne_top [IsAbsolutelySummable Φ] (Λ A : Finset S) : Φ.termNorm Λ A ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) A

/-- The total variation of the Hamiltonian series in `Λ` is bounded by `∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
lemma tsum_enorm_hamiltonianTerms_le (Λ : Finset S) (η : S → E) :
    ∑' A : Finset S, ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  le_trans (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η))
    (tsum_termNorm_le (Φ := Φ) Λ)

/-- **Georgii (2.11) ⇒ (2.2)(ii).** An absolutely summable potential is summable. -/
lemma summable_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) := by
  exact Summable.of_enorm (ne_of_lt (lt_of_le_of_lt (tsum_enorm_hamiltonianTerms_le Λ η)
    (lt_top_iff_ne_top.2 (sum_normAt_ne_top (Φ := Φ) Λ))))

instance (priority := 100) IsAbsolutelySummable.isSummable [IsAbsolutelySummable Φ] :
    IsSummable Φ where
  summable Λ η := (summable_hamiltonianTerms (Φ := Φ) Λ η).volume

/-- The Hamiltonian of an absolutely summable potential is the unconditional sum. -/
lemma hamiltonian_eq_tsum [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = ∑' A : Finset S, Φ.hamiltonianTerms Λ η A :=
  ((summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum.volume).tsum_eq

/-- **Georgii (2.14).** `‖H_Λ^Φ‖ ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
theorem enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i := by
  rw [hamiltonian_eq_tsum (Φ := Φ) Λ η]
  exact le_trans enorm_tsum_le_tsum_enorm (tsum_enorm_hamiltonianTerms_le Λ η)

/-- **Georgii (2.14)** in sup-norm form. -/
theorem iSup_enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ⨆ η, ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  iSup_le fun η ↦ enorm_hamiltonian_le (Φ := Φ) Λ η

/-! ### The Gibbsian specification of an absolutely summable potential -/

/-- Georgii (2.14) in real form. -/
lemma abs_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    |Φ.hamiltonian Λ η| ≤ (∑ i ∈ Λ, Φ.normAt i).toReal := by
  have h := enorm_hamiltonian_le (Φ := Φ) Λ η
  rw [← ENNReal.toReal_le_toReal (by simp) (sum_normAt_ne_top (Φ := Φ) Λ)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

variable (Φ) in
/-- The uniform bound `∑_{i ∈ Λ} ‖Φ‖ᵢ` on the Hamiltonian in `Λ`, as a real number. -/
def hamiltonianBound (Λ : Finset S) : ℝ := (∑ i ∈ Λ, Φ.normAt i).toReal

lemma boltzmannFactor_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η ≤ ENNReal.ofReal (Real.exp (|β| * Φ.hamiltonianBound Λ)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  calc -β * Φ.hamiltonian Λ η ≤ |(-β) * Φ.hamiltonian Λ η| := le_abs_self _
    _ = |β| * |Φ.hamiltonian Λ η| := by rw [abs_mul, abs_neg]
    _ ≤ |β| * Φ.hamiltonianBound Λ := by
        exact mul_le_mul_of_nonneg_left (abs_hamiltonian_le Λ η) (abs_nonneg _)

lemma le_boltzmannFactor [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    ENNReal.ofReal (Real.exp (-(|β| * Φ.hamiltonianBound Λ))) ≤ Φ.boltzmannFactor β Λ η := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h : -(|β| * Φ.hamiltonianBound Λ) ≤ -|(-β) * Φ.hamiltonian Λ η| := by
    rw [abs_mul, abs_neg]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (abs_hamiltonian_le Λ η) (abs_nonneg _))
  exact h.trans (neg_abs_le _)

section RelativeBounds

variable {γ : Specification S E}

/-- Upper bound `Z_Λ ≤ e^{|β| ∑_{i ∈ Λ} ‖Φ‖ᵢ}` on the partition function relative to any
reference specification. -/
lemma relZ_boltzmannFactor_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Specification.relZ γ (Φ.boltzmannFactor β) Λ η
      ≤ ENNReal.ofReal (Real.exp (|β| * Φ.hamiltonianBound Λ)) := by
  refine le_trans (lintegral_mono fun x ↦ boltzmannFactor_le (Φ := Φ) β Λ x) ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- Lower bound `e^{-|β| ∑_{i ∈ Λ} ‖Φ‖ᵢ} ≤ Z_Λ` on the partition function. -/
lemma le_relZ_boltzmannFactor [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    ENNReal.ofReal (Real.exp (-(|β| * Φ.hamiltonianBound Λ)))
      ≤ Specification.relZ γ (Φ.boltzmannFactor β) Λ η := by
  refine le_trans ?_ (lintegral_mono fun x ↦ le_boltzmannFactor (Φ := Φ) β Λ x)
  rw [lintegral_const, measure_univ, mul_one]

/-- **Georgii (2.14) ⇒ λ-admissibility.** An absolutely summable potential is admissible relative
to every reference specification: the partition functions are finite and non-zero. -/
theorem isRelAdmissible_boltzmannFactor [IsAbsolutelySummable Φ] (β : ℝ) :
    Specification.IsRelAdmissible γ (Φ.boltzmannFactor β) := by
  intro Λ η
  refine ⟨fun h0 ↦ ?_, fun htop ↦ ?_⟩
  · have hge := le_relZ_boltzmannFactor (Φ := Φ) (γ := γ) β Λ η
    rw [h0] at hge
    exact absurd (le_antisymm hge bot_le).symm (by simp [Real.exp_pos])
  · have hle := relZ_boltzmannFactor_le (Φ := Φ) (γ := γ) β Λ η
    rw [htop] at hle
    exact absurd (top_le_iff.1 hle) (by simp)

/-- The normalized Boltzmann density is uniformly bounded:
`ρ_Λ = h_Λ/Z_Λ ≤ e^{2|β| ∑_{i ∈ Λ} ‖Φ‖ᵢ}` (Georgii (4.14)(1), the domination input to the
existence theorem (4.23)). -/
lemma relNorm_boltzmannFactor_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) :
    Specification.relNorm γ (Φ.boltzmannFactor β) Λ η
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) := by
  rw [Specification.relNorm]
  refine le_trans (ENNReal.div_le_div (boltzmannFactor_le (Φ := Φ) β Λ η)
    (le_relZ_boltzmannFactor (Φ := Φ) β Λ η)) ?_
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (le_of_eq ?_))
  ring

end RelativeBounds

variable (ν : Measure E) [IsProbabilityMeasure ν]

lemma premodifierZ_boltzmannFactor_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S)
    (η : S → E) :
    Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      ≤ ENNReal.ofReal (Real.exp (|β| * Φ.hamiltonianBound Λ)) :=
  relZ_boltzmannFactor_le (γ := Specification.isssd ν) β Λ η

lemma le_premodifierZ_boltzmannFactor [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S)
    (η : S → E) :
    ENNReal.ofReal (Real.exp (-(|β| * Φ.hamiltonianBound Λ)))
      ≤ Specification.premodifierZ (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η :=
  le_relZ_boltzmannFactor (γ := Specification.isssd ν) β Λ η

theorem isPremodifierAdmissible_boltzmannFactor [IsAbsolutelySummable Φ] (β : ℝ) :
    Specification.IsPremodifierAdmissible (S := S) (E := E) ν (Φ.boltzmannFactor β) :=
  isRelAdmissible_boltzmannFactor (γ := Specification.isssd ν) β

lemma premodifierNorm_boltzmannFactor_le [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S)
    (η : S → E) :
    Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β) Λ η
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) :=
  relNorm_boltzmannFactor_le (γ := Specification.isssd ν) β Λ η

/-- **Georgii Definition (2.9) for `Φ ∈ ℬ`.** The Gibbsian specification of an absolutely summable
potential and a single-spin probability measure. -/
def gibbsSpecificationOfAbsolutelySummable [Countable S] [IsPotential Φ] [IsAbsolutelySummable Φ]
    (β : ℝ) : Specification S E :=
  (Specification.isssd (S := S) (E := E) ν).modification
    (Specification.premodifierNorm (S := S) (E := E) ν (Φ.boltzmannFactor β))
    (Specification.IsPremodifier.isModifier_premodifierNorm (ν := ν)
      (isPremodifier_boltzmannFactor (Φ := Φ) β)
      (isPremodifierAdmissible_boltzmannFactor (Φ := Φ) ν β))

/-- **Domination of the Gibbsian specification** (the estimate behind Georgii (4.23)(a): the bound
in the proof of Corollary (4.13) with Comment (4.14)(1), as in `relNorm_boltzmannFactor_le`). On
`𝓕_Λ`-events, the Gibbsian specification of an absolutely summable potential is dominated by a
constant multiple of the free measure `ν^S`. -/
lemma gibbsSpecificationOfAbsolutelySummable_apply_le [Countable S] [IsPotential Φ]
    [IsAbsolutelySummable Φ] (β : ℝ) (Λ : Finset S) (η : S → E) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (Λ : Set S)] A) :
    gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η A ≤
      ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A := by
  calc gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β Λ η A
      ≤ ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) *
        Specification.isssd (S := S) (E := E) ν Λ η A :=
      Specification.modification_apply_le _ _ _ Λ η (cylinderEvents_le_pi _ hA)
        fun ω ↦ premodifierNorm_boltzmannFactor_le (Φ := Φ) ν β Λ ω
    _ = ENNReal.ofReal (Real.exp (2 * |β| * Φ.hamiltonianBound Λ)) *
        Measure.infinitePi (fun _ : S ↦ ν) A := by
      rw [Specification.isssd_apply_of_mem_cylinderEvents ν Λ η hA]

/-! ### Georgii (2.13): uniform convergence of the Hamiltonians -/

section UniformlyConvergent

/-- **Georgii (2.13).** A potential is *uniformly convergent* when for every finite volume `Λ`
the partial Hamiltonians `H^Φ_{Λ,Δ} = ∑_{A ⊆ Δ, A ∩ Λ ≠ ∅} Φ_A` converge to `H^Φ_Λ` uniformly
in the configuration. -/
def IsUniformlyConvergent (Φ : Potential S E) : Prop :=
  ∀ (Λ : Finset S) ⦃ε : ℝ⦄, 0 < ε → ∃ Δ₀ : Finset S, ∀ Δ : Finset S, Δ₀ ⊆ Δ → ∀ η : S → E,
    |(∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A) - Φ.hamiltonian Λ η| ≤ ε

end UniformlyConvergent

/-- The Hamiltonian of the empty volume vanishes. -/
lemma hamiltonian_empty (Φ : Potential S E)
    (η : S → E) : Φ.hamiltonian ∅ η = 0 := by
  unfold hamiltonian
  have : Φ.hamiltonianTerms ∅ η = 0 :=
    funext fun A ↦ hamiltonianTerms_of_disjoint (Finset.disjoint_empty_right A) η
  rw [this]
  exact tsum_zero

/-- `H_{Λ₁ ∪ Λ₂} = H_{Λ₂} + ∑_{A ∩ Λ₁ ≠ ∅, A ∩ Λ₂ = ∅} Φ_A`, for an absolutely summable
potential. -/
lemma hamiltonian_union_eq_add_tsum [DecidableEq S] [IsAbsolutelySummable Φ] (Λ₁ Λ₂ : Finset S) (η : S → E) :
    Φ.hamiltonian (Λ₁ ∪ Λ₂) η = Φ.hamiltonian Λ₂ η +
      ∑' A : Finset S, (if Disjoint A Λ₂ then Φ.hamiltonianTerms Λ₁ η A else 0) := by
  rw [hamiltonian_eq_tsum, hamiltonian_eq_tsum]
  have hind : (fun A : Finset S ↦ if Disjoint A Λ₂ then Φ.hamiltonianTerms Λ₁ η A else 0) =
      {A : Finset S | Disjoint A Λ₂}.indicator (Φ.hamiltonianTerms Λ₁ η) := by
    funext A
    rw [Set.indicator_apply]
    congr
  have hs : Summable fun A : Finset S ↦
      if Disjoint A Λ₂ then Φ.hamiltonianTerms Λ₁ η A else 0 := by
    rw [hind]
    exact (summable_hamiltonianTerms Λ₁ η).indicator _
  rw [← (summable_hamiltonianTerms Λ₂ η).tsum_add hs]
  refine tsum_congr fun A ↦ ?_
  by_cases h2 : Disjoint A Λ₂
  · rw [hamiltonianTerms_of_disjoint h2, ite_eq_left h2, zero_add]
    by_cases h1 : Disjoint A Λ₁
    · rw [hamiltonianTerms_of_disjoint h1, hamiltonianTerms_of_disjoint (Finset.disjoint_union_right.2 ⟨h1, h2⟩)]
    · rw [hamiltonianTerms_of_not_disjoint h1, hamiltonianTerms_of_not_disjoint
        (fun h ↦ h1 (Finset.disjoint_union_right.1 h).1)]
  · rw [hamiltonianTerms_of_not_disjoint h2, ite_eq_right h2, add_zero,
      hamiltonianTerms_of_not_disjoint (fun h ↦ h2 (Finset.disjoint_union_right.1 h).2)]

end Potential

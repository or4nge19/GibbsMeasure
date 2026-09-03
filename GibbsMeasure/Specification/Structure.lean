/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.Order.Filter.CountableSeparatingOn
public import GibbsMeasure.Mathlib.Probability.TailTriviality

/-!
# The Gibbs state space: probability measures, convexity, and the tail σ-algebra (Georgii, Ch. 7)

This file sets up the objects used in the structural analysis of Gibbs measures:
- `GP γ`: the set of Gibbs **probability measures** for a specification `γ`, and its convexity
  (`ProbabilityMeasure.convexCombo`, `convexCombo_mem_GP`);
- `tailSigmaAlgebra`: the tail σ-algebra `𝓣` on the configuration space;
- `IsTailTrivial`: tail triviality, together with the a.e. constancy of tail-measurable functions
  under a tail-trivial measure (`IsTailTrivial.ae_eq_const_of_measurable`).
-/

@[expose] public section

open Set

namespace MeasureTheory

open scoped ENNReal

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### The Gibbs state space as a subset of `ProbabilityMeasure` -/

/-- The set of Gibbs **probability** measures for a specification `γ`. -/
def GP (γ : Specification S E) : Set (ProbabilityMeasure (S → E)) :=
  {μ | Specification.IsGibbsMeasure (S := S) (E := E) γ (μ : Measure (S → E))}

/-! ### Convexity (binary convex combinations) -/

namespace ProbabilityMeasure

open unitInterval

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Binary convex combination of probability measures, with weight `p` on `μ` and `1-p` on `ν`. -/
noncomputable def convexCombo (p : I) (μ ν : ProbabilityMeasure Ω) : ProbabilityMeasure Ω :=
  ⟨toNNReal p • (μ : Measure Ω) + toNNReal (σ p) • (ν : Measure Ω), by
    infer_instance⟩

@[simp] lemma coe_convexCombo (p : I) (μ ν : ProbabilityMeasure Ω) :
    ((convexCombo (p := p) μ ν : ProbabilityMeasure Ω) : Measure Ω) =
      toNNReal p • (μ : Measure Ω) + toNNReal (σ p) • (ν : Measure Ω) :=
  rfl

end ProbabilityMeasure


lemma convexCombo_mem_GP (γ : Specification S E)
    (μ ν : ProbabilityMeasure (S → E)) (hμ : μ ∈ GP γ) (hν : ν ∈ GP γ) (p : unitInterval) :
    ProbabilityMeasure.convexCombo (p := p) μ ν ∈ GP γ := by
  -- Use the fixed-point characterization `μ.bind (γ Λ) = μ`.
  have hμ' :
      ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
    have : γ.IsGibbsMeasure (μ : Measure (S → E)) := hμ
    simpa [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (S := S) (E := E) (γ := γ)]
        using this
  have hν' :
      ∀ Λ : Finset S, (ν : Measure (S → E)).bind (γ Λ) = (ν : Measure (S → E)) := by
    have : γ.IsGibbsMeasure (ν : Measure (S → E)) := hν
    simpa [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (S := S) (E := E) (γ := γ)]
        using this
  have hfix :
      ∀ Λ : Finset S,
        ((ProbabilityMeasure.convexCombo (Ω := (S → E)) (p := p) μ ν :
            ProbabilityMeasure (S → E)) :
              Measure (S → E)).bind (γ Λ)
          =
          ((ProbabilityMeasure.convexCombo (Ω := (S → E)) (p := p) μ ν :
              ProbabilityMeasure (S → E)) :
              Measure (S → E)) := by
    intro Λ
    have hmeas : Measurable (γ Λ) :=
      (ProbabilityTheory.Kernel.measurable (γ Λ)).mono
        (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))
        le_rfl
    simp [ProbabilityMeasure.coe_convexCombo]
    rw [Measure.bind_add (μ := unitInterval.toNNReal p • (μ : Measure (S → E)))
      (ν := unitInterval.toNNReal (unitInterval.symm p) • (ν : Measure (S → E)))
      (f := γ Λ) hmeas]
    rw [Measure.bind_smul (unitInterval.toNNReal p) (μ : Measure (S → E)) (γ Λ)]
    rw [Measure.bind_smul (unitInterval.toNNReal (unitInterval.symm p))
      (ν : Measure (S → E)) (γ Λ)]
    simp [hμ' Λ, hν' Λ]
  have : γ.IsGibbsMeasure
      ((ProbabilityMeasure.convexCombo (Ω := (S → E)) (p := p) μ ν :
          ProbabilityMeasure (S → E)) :
        Measure (S → E)) := by
    simpa [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (S := S) (E := E) (γ := γ)]
        using hfix
  exact this

/-! ### Tail σ-algebra -/

/-- The **tail σ-algebra** `𝓣`: information at infinity, defined as the infimum of the
σ-algebras `cylinderEvents (Λᶜ)` over finite volumes `Λ`. -/
@[reducible]
def tailSigmaAlgebra (S E : Type*) [MeasurableSpace E] : MeasurableSpace (S → E) :=
  ⨅ (Λ : Finset S), cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)

notation "𝓣" => tailSigmaAlgebra

/-- Tail-triviality: every tail event has probability `0` or `1`. -/
def IsTailTrivial (μ : ProbabilityMeasure (S → E)) : Prop :=
  ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A →
    (μ : Measure (S → E)) A = 0 ∨ (μ : Measure (S → E)) A = 1

/-- **Georgii (7.9).** A probability measure on a configuration space over a countable set of sites
is trivial on the tail σ-algebra `𝓣` if and only if it is asymptotically independent of the
exterior σ-algebras `𝓕_{Λᶜ}`: for every event `A` and every `ε > 0`, all large enough finite
volumes `Λ` satisfy `|μ(A ∩ B) - μ(A) μ(B)| ≤ ε` for every `B ∈ 𝓕_{Λᶜ}`. -/
theorem forall_tail_measure_eq_zero_or_one_iff [Countable S] {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] :
    (∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1) ↔
      ∀ A, MeasurableSet A → ∀ ε : ℝ, 0 < ε → ∀ᶠ Λ : Finset S in Filter.atTop,
        ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B →
          |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ ε :=
  MeasureTheory.forall_measure_eq_zero_or_one_iInf_iff_of_directed
    (fun _ _ h ↦ cylinderEvents_mono (Set.compl_subset_compl.2 (by exact_mod_cast h)))
    fun _ ↦ cylinderEvents_le_pi

/-- `IsTailTrivial` in the form of Georgii (7.9). -/
theorem isTailTrivial_iff_asymptotically_independent [Countable S]
    (μ : ProbabilityMeasure (S → E)) :
    IsTailTrivial μ ↔
      ∀ A, MeasurableSet A → ∀ ε : ℝ, 0 < ε → ∀ᶠ Λ : Finset S in Filter.atTop,
        ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B →
          |((μ : Measure (S → E)) (A ∩ B)).toReal
            - ((μ : Measure (S → E)) A).toReal * ((μ : Measure (S → E)) B).toReal| ≤ ε :=
  forall_tail_measure_eq_zero_or_one_iff

namespace IsTailTrivial

open Filter

variable {μ : ProbabilityMeasure (S → E)}

/-- A tail-trivial probability measure makes every **tail-measurable** function into a countably
separated measurable space a.e. constant. -/
theorem ae_eq_const_of_measurable {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X]
    [Nonempty X]
    (hμ : IsTailTrivial (S := S) (E := E) μ) {f : (S → E) → X}
    (hf : Measurable[@tailSigmaAlgebra S E _] f) :
    ∃ c : X, f =ᵐ[(μ : Measure (S → E))] fun _ => c := by
  have hDich :
      ∀ U : Set X, MeasurableSet U →
        (∀ᵐ ω ∂(μ : Measure (S → E)), f ω ∈ U) ∨
          (∀ᵐ ω ∂(μ : Measure (S → E)), f ω ∉ U) := by
    intro U hU
    have hpre_tail : MeasurableSet[@tailSigmaAlgebra S E _] (f ⁻¹' U) := hf hU
    have hpre_pi :
        MeasurableSet (f ⁻¹' U) := by
      have hle_tail_pi :
          (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi := by
        refine le_trans
          (iInf_le (fun Λ : Finset S =>
            cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) (∅ : Finset S)) ?_
        simp
      exact hle_tail_pi _ hpre_tail
    have hprob : (μ : Measure (S → E)) (f ⁻¹' U) = 0 ∨ (μ : Measure (S → E)) (f ⁻¹' U) = 1 :=
      hμ (f ⁻¹' U) hpre_tail
    rcases hprob with h0 | h1
    · right
      have : (∀ᵐ ω ∂(μ : Measure (S → E)), ¬ f ω ∈ U) := by
        have : (μ : Measure (S → E)) {ω | ¬ (¬ f ω ∈ U)} = 0 := by
          convert h0
          ext ω
          simp [Set.mem_preimage]
        simpa [ae_iff] using this
      exact this
    · left
      have hcompl0 : (μ : Measure (S → E)) (f ⁻¹' U)ᶜ = 0 :=
        (prob_compl_eq_zero_iff (μ := (μ : Measure (S → E))) hpre_pi).2 h1
      have : (∀ᵐ ω ∂(μ : Measure (S → E)), f ω ∈ U) := by
        have : (μ : Measure (S → E)) {ω | ¬ f ω ∈ U} = 0 := by
          simpa [Set.preimage, Set.compl_def] using hcompl0
        simpa [ae_iff] using this
      exact this
  have : ∃ c : X, f =ᶠ[ae (μ : Measure (S → E))] fun _ => c :=
    Filter.exists_eventuallyEq_const_of_forall_separating (l := ae (μ : Measure (S → E)))
      (f := f) (p := MeasurableSet) (β := X) (fun U hU => by
        simpa using (hDich U hU))
  rcases this with ⟨c, hc⟩
  exact ⟨c, hc⟩

/-!
`MeasureTheory.AEMeasurable` is tied to the *ambient* measurable space on the domain.  In our use
case, we want “a.e. equal to a `𝓣`-measurable function” measured w.r.t. `μ`. We state that
condition explicitly.
-/

/-- If `f` is a.e. equal (w.r.t. `μ`) to a **tail-measurable** function, then it is a.e. constant
under a tail-trivial measure. -/
theorem ae_eq_const_of_ae_eq_measurable {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablySeparated X] [Nonempty X]
    (hμ : IsTailTrivial (S := S) (E := E) μ) {f : (S → E) → X}
    (hf : ∃ g : (S → E) → X, Measurable[@tailSigmaAlgebra S E _] g ∧
      f =ᵐ[(μ : Measure (S → E))] g) :
    ∃ c : X, f =ᵐ[(μ : Measure (S → E))] fun _ => c := by
  rcases hf with ⟨g, hg, hfg⟩
  rcases ae_eq_const_of_measurable (S := S) (E := E) (μ := μ) hμ (f := g) hg with ⟨c, hgc⟩
  refine ⟨c, hfg.trans ?_⟩
  simpa using hgc

end IsTailTrivial

end GibbsMeasure

end MeasureTheory

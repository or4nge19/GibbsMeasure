/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Structure
public import Mathlib.Probability.Independence.ZeroOne
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Kolmogorov's zero–one law for the tail σ-algebra

The tail σ-algebra `𝓣 = ⨅ Λ, 𝓕_{Λᶜ}` of a configuration space is the `limsup` of the coordinate
σ-algebras along the cofinite filter (`tailSigmaAlgebra_eq_limsup_cofinite`), so Mathlib's
filter-indexed Kolmogorov zero–one law applies to any independent product: every tail event of
`Measure.infinitePi μs` has probability `0` or `1`
(`forall_tail_measure_eq_zero_or_one_infinitePi`), over an arbitrary site set and state space.

This is the standard source of tail-trivial — hence extreme, by Georgii (7.7) — Gibbs measures,
and the engine behind the Blackwell–Dubins non-existence of proper regular conditional
distributions given `𝓣`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- The tail σ-algebra is the `limsup` of the coordinate σ-algebras along the cofinite filter. -/
lemma tailSigmaAlgebra_eq_limsup_cofinite :
    (tailSigmaAlgebra S E : MeasurableSpace (S → E)) =
      Filter.limsup
        (fun i : S ↦ MeasurableSpace.comap (fun σ : S → E ↦ σ i) inferInstance)
        Filter.cofinite := by
  rw [limsup_eq_iInf_iSup]
  rw [tailSigmaAlgebra]
  apply le_antisymm
  · refine le_iInf₂ fun U hU ↦ ?_
    rw [Filter.mem_cofinite] at hU
    refine (iInf_le _ hU.toFinset).trans ?_
    rw [cylinderEvents]
    refine iSup₂_le fun i hi ↦ ?_
    have hiU : i ∈ U := by
      by_contra h
      exact hi (by simpa using h)
    exact le_iSup₂_of_le i hiU le_rfl
  · refine le_iInf fun Λ ↦ ?_
    have hmem : ((Λ : Set S)ᶜ : Set S) ∈ (Filter.cofinite : Filter S) := by
      rw [Filter.mem_cofinite, compl_compl]
      exact Λ.finite_toSet
    refine (iInf₂_le _ hmem).trans ?_
    rw [cylinderEvents]

/-- **Kolmogorov's zero–one law for the tail σ-algebra of a product measure.** Over an arbitrary
site set, every tail event of an independent product of probability measures has probability
`0` or `1`. -/
theorem forall_tail_measure_eq_zero_or_one_infinitePi (μs : S → Measure E)
    [∀ i, IsProbabilityMeasure (μs i)] {A : Set (S → E)}
    (hA : MeasurableSet[tailSigmaAlgebra S E] A) :
    Measure.infinitePi μs A = 0 ∨ Measure.infinitePi μs A = 1 := by
  have h_indep : iIndep
      (fun i : S ↦ MeasurableSpace.comap (fun σ : S → E ↦ σ i) inferInstance)
      (Measure.infinitePi μs) :=
    (iIndepFun_infinitePi (P := μs) (X := fun _ x ↦ x) (fun _ ↦ measurable_id)).iIndep
  refine measure_zero_or_one_of_measurableSet_limsup
    (s := fun i : S ↦ MeasurableSpace.comap (fun σ : S → E ↦ σ i) inferInstance)
    (f := Filter.cofinite) (p := fun t : Set S ↦ t.Finite)
    (ns := fun Λ : Finset S ↦ (Λ : Set S))
    (fun i ↦ (measurable_pi_apply i).comap_le)
    h_indep
    (fun t ht ↦ by rwa [Filter.mem_cofinite, compl_compl])
    (fun Λ₁ Λ₂ ↦ by
      classical
      exact ⟨Λ₁ ∪ Λ₂, fun x hx ↦ by simp [hx], fun x hx ↦ by simp [hx]⟩)
    (fun Λ ↦ Λ.finite_toSet)
    (fun i ↦ ⟨{i}, by simp⟩)
    (by rwa [← tailSigmaAlgebra_eq_limsup_cofinite])


/-- The independent product of probability measures is tail trivial. -/
theorem isTailTrivial_infinitePi (μs : S → Measure E) [∀ i, IsProbabilityMeasure (μs i)] :
    IsTailTrivial (⟨Measure.infinitePi μs, inferInstance⟩ : ProbabilityMeasure (S → E)) :=
  fun _A hA ↦ forall_tail_measure_eq_zero_or_one_infinitePi μs hA

end MeasureTheory.GibbsMeasure

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Additivity of the Kullback–Leibler divergence over independent coordinates

The Kullback–Leibler divergence of two product measures is the sum of the divergences of the
factors. Mathlib has the chain rule `klDiv_compProd_eq_add` for composition-products of a measure
with a kernel; the product of two measures is the special case of a constant kernel, and iterating
it over a finite index type gives the `Measure.pi` statement.

## Main statements

* `InformationTheory.klDiv_map_measurableEquiv`: the divergence is invariant under a measurable
  equivalence (both data processing inequalities `klDiv_map_le`).
* `InformationTheory.klDiv_prod`: `𝓗(μ₁ ⊗ μ₂ | ν₁ ⊗ ν₂) = 𝓗(μ₁ | ν₁) + 𝓗(μ₂ | ν₂)`.
* `InformationTheory.klDiv_pi`: `𝓗(⨂ᵢ μᵢ | ⨂ᵢ νᵢ) = ∑ᵢ 𝓗(μᵢ | νᵢ)` over a finite index type,
  and `InformationTheory.klDiv_pi_const` for a constant family.

All the statements are for probability measures. For merely finite measures they are false:
`klDiv` carries the normalising correction `ν(univ) − μ(univ)`, and
`∫ llr (μ₁ ⊗ μ₂) (ν₁ ⊗ ν₂) d(μ₁ ⊗ μ₂) = μ₂(univ) ∫ llr μ₁ ν₁ dμ₁ + μ₁(univ) ∫ llr μ₂ ν₂ dμ₂`
is not additive unless the total masses are `1`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

/-- **The Kullback–Leibler divergence is invariant under a measurable equivalence.** Both
inequalities are the data processing inequality `klDiv_map_le`, for `e` and for `e.symm`. -/
lemma klDiv_map_measurableEquiv {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have hfin : ∀ ρ : Measure α, IsFiniteMeasure ρ → IsFiniteMeasure (ρ.map e) := fun ρ _ ↦
    Measure.isFiniteMeasure_map ρ e
  have hback : ∀ ρ : Measure α, (ρ.map e).map e.symm = ρ := fun ρ ↦ by
    rw [Measure.map_map e.symm.measurable e.measurable]
    simp
  have := hfin μ ‹_›
  have := hfin ν ‹_›
  refine le_antisymm (klDiv_map_le _ _ e.measurable) ?_
  calc klDiv μ ν = klDiv ((μ.map e).map e.symm) ((ν.map e).map e.symm) := by rw [hback, hback]
    _ ≤ klDiv (μ.map e) (ν.map e) := klDiv_map_le _ _ e.symm.measurable

/-- The Kullback–Leibler divergence is unchanged by a measure-preserving measurable equivalence. -/
lemma klDiv_of_measurePreserving_measurableEquiv {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μ ν : Measure α} {μ' ν' : Measure β} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (e : α ≃ᵐ β) (hμ : MeasurePreserving e μ μ')
    (hν : MeasurePreserving e ν ν') :
    klDiv μ' ν' = klDiv μ ν := by
  rw [← hμ.map_eq, ← hν.map_eq, klDiv_map_measurableEquiv]

section Prod

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The divergence between two products with the same first factor is the divergence between the
second factors. This is `klDiv_compProd_left` read through `Measure.prod_swap`. -/
lemma klDiv_prod_left (μ : Measure α) (ν₁ ν₂ : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂ := by
  have hswap : ∀ ρ : Measure β, IsProbabilityMeasure ρ →
      (μ.prod ρ).map (MeasurableEquiv.prodComm (α := α) (β := β)) = ρ.prod μ := fun ρ _ ↦ by
    rw [show ⇑(MeasurableEquiv.prodComm (α := α) (β := β)) = Prod.swap from rfl,
      Measure.prod_swap]
  calc klDiv (μ.prod ν₁) (μ.prod ν₂)
      = klDiv ((μ.prod ν₁).map (MeasurableEquiv.prodComm (α := α) (β := β)))
          ((μ.prod ν₂).map (MeasurableEquiv.prodComm (α := α) (β := β))) :=
        (klDiv_map_measurableEquiv _ _ _).symm
    _ = klDiv (ν₁.prod μ) (ν₂.prod μ) := by rw [hswap ν₁ ‹_›, hswap ν₂ ‹_›]
    _ = klDiv ν₁ ν₂ := by
        rw [← Measure.compProd_const (μ := ν₁) (ν := μ), ← Measure.compProd_const (μ := ν₂)
          (ν := μ), klDiv_compProd_left]

/-- **Additivity of the Kullback–Leibler divergence over a product of two factors**: for
probability measures, `𝓗(μ₁ ⊗ μ₂ | ν₁ ⊗ ν₂) = 𝓗(μ₁ | ν₁) + 𝓗(μ₂ | ν₂)`. -/
theorem klDiv_prod (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  have h : klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) := by
    rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂), ← Measure.compProd_const (μ := ν₁) (ν := ν₂),
      ← Measure.compProd_const (μ := μ₁) (ν := ν₂), klDiv_compProd_eq_add]
  rw [h, klDiv_prod_left]

end Prod

section Pi

universe u

private theorem klDiv_pi_fin : ∀ (n : ℕ) {α : Fin n → Type u} [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)],
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  intro n
  induction n with
  | zero =>
      intro α _ μ ν _ _
      rw [Measure.pi_of_empty μ isEmptyElim, Measure.pi_of_empty ν isEmptyElim]
      simp
  | succ n ih =>
      intro α _ μ ν _ _
      have hμ := measurePreserving_piFinSuccAbove μ 0
      have hν := measurePreserving_piFinSuccAbove ν 0
      rw [← klDiv_of_measurePreserving_measurableEquiv (MeasurableEquiv.piFinSuccAbove α 0) hμ hν,
        klDiv_prod, ih (fun j ↦ μ ((0 : Fin (n + 1)).succAbove j))
          (fun j ↦ ν ((0 : Fin (n + 1)).succAbove j)),
        ← Fin.sum_univ_succAbove (fun i ↦ klDiv (μ i) (ν i)) 0]

/-- **Additivity of the Kullback–Leibler divergence over a finite product**: for families of
probability measures indexed by a finite type, `𝓗(⨂ᵢ μᵢ | ⨂ᵢ νᵢ) = ∑ᵢ 𝓗(μᵢ | νᵢ)`. -/
theorem klDiv_pi {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hμ := measurePreserving_piCongrLeft (α := α) μ e.symm
  have hν := measurePreserving_piCongrLeft (α := α) ν e.symm
  rw [klDiv_of_measurePreserving_measurableEquiv (MeasurableEquiv.piCongrLeft α e.symm) hμ hν,
    klDiv_pi_fin _ (fun j ↦ μ (e.symm j)) (fun j ↦ ν (e.symm j))]
  exact Equiv.sum_comp e.symm fun i ↦ klDiv (μ i) (ν i)

/-- **Additivity of the Kullback–Leibler divergence over `n` independent copies**: for probability
measures, `𝓗(μ^n | ν^n) = n 𝓗(μ | ν)`. -/
theorem klDiv_pi_const {ι α : Type*} [Fintype ι] {mα : MeasurableSpace α} (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi fun _ : ι ↦ μ) (Measure.pi fun _ : ι ↦ ν)
      = (Fintype.card ι : ℝ≥0∞) * klDiv μ ν := by
  rw [klDiv_pi (fun _ : ι ↦ μ) fun _ : ι ↦ ν, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Pi

end InformationTheory

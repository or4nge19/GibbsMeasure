/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Sections, and zero-one laws, for a product measure over sub-σ-algebras

Mathlib's product-measure API (`MeasureTheory.Measure.prod_apply`,
`MeasureTheory.measurable_measure_prodMk_left`) is stated for the *ambient* σ-algebras of the two
factors. What it says is really a statement about an arbitrary pair of σ-algebras
`m₁ : MeasurableSpace X`, `m₂ : MeasurableSpace Y` and their product `m₁.prod m₂`, because
`Prod.instMeasurableSpace` *is* `MeasurableSpace.prod`. This file records the sub-σ-algebra form
of the section lemmas, and the zero-one law they give for a product measure.

* `MeasurableSpace.prod_le_prod`: the product of σ-algebras is monotone in both arguments.
* `MeasureTheory.measurableSet_preimage_prodMk_left`: the `x`-section of an `m₁.prod m₂`-measurable
  set is `m₂`-measurable.
* `MeasureTheory.measurable_measure_preimage_prodMk_left`: for an s-finite `ν`, the section measure
  `x ↦ ν (Prod.mk x ⁻¹' s)` of an `m₁.prod 𝔜`-measurable set is `m₁`-measurable.
* `MeasureTheory.Measure.prod_apply_eq_zero_or_one`: **a product of two probability measures, each
  obeying a zero-one law on a sub-σ-algebra, obeys the zero-one law on the product of those
  sub-σ-algebras.**
* `MeasureTheory.Measure.prod_apply_eq_zero_or_one_iInf`: the version for two *families* of
  sub-σ-algebras, with the conclusion on `⨅ i, ⨅ j, (m₁ i).prod (m₂ j)`. This is strictly stronger
  than the previous item applied to the two infima, because
  `(⨅ i, m₁ i).prod (⨅ j, m₂ j) ≤ ⨅ i, ⨅ j, (m₁ i).prod (m₂ j)` and that inequality is in general
  strict: an infimum of product σ-algebras is bigger than the product of the infima. The `iInf`
  form is what tail σ-algebras need: a tail σ-algebra is an infimum of σ-algebras, and the tail
  σ-algebra of a product of two such spaces is an infimum of *products* of them, not the product
  of the two infima.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped ENNReal

namespace MeasurableSpace

variable {α β : Type*}

/-- The product of measurable spaces is monotone in both arguments. -/
lemma prod_le_prod {m₁ m₁' : MeasurableSpace α} {m₂ m₂' : MeasurableSpace β} (h₁ : m₁ ≤ m₁')
    (h₂ : m₂ ≤ m₂') : m₁.prod m₂ ≤ m₁'.prod m₂' :=
  sup_le_sup (comap_mono h₁) (comap_mono h₂)

end MeasurableSpace

namespace MeasureTheory

variable {X Y : Type*}

/-! ### Sections over sub-σ-algebras -/

/-- The `x`-section of a set measurable for a product `m₁.prod m₂` of two σ-algebras is
`m₂`-measurable: this is `measurable_prodMk_left` at σ-algebras that need not be the ambient
ones. -/
theorem measurableSet_preimage_prodMk_left {m₁ : MeasurableSpace X} {m₂ : MeasurableSpace Y}
    {s : Set (X × Y)} (hs : MeasurableSet[m₁.prod m₂] s) (x : X) :
    MeasurableSet[m₂] (Prod.mk x ⁻¹' s) :=
  @measurable_prodMk_left X Y m₁ m₂ x _ hs

/-- For an s-finite measure `ν` on `Y`, the section measure `x ↦ ν (Prod.mk x ⁻¹' s)` of a set
measurable for `m₁.prod mY` is measurable for the sub-σ-algebra `m₁`: this is
`measurable_measure_prodMk_left` at a σ-algebra on `X` that need not be the ambient one. -/
theorem measurable_measure_preimage_prodMk_left {m₁ : MeasurableSpace X} [mY : MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν] {s : Set (X × Y)} (hs : MeasurableSet[m₁.prod mY] s) :
    Measurable[m₁] fun x ↦ ν (Prod.mk x ⁻¹' s) :=
  @measurable_measure_prodMk_left X Y m₁ mY ν _ s hs

/-! ### Zero-one laws -/

section iInf

variable [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **Zero-one law for a product measure, over two families of sub-σ-algebras.**

If a probability measure `μ` on `X` is trivial on `⨅ i, m₁ i` and a probability measure `ν` on `Y`
is trivial on `⨅ j, m₂ j`, then `μ ⊗ ν` is trivial on `⨅ i, ⨅ j, (m₁ i).prod (m₂ j)`.

A set `s` in that infimum has all its `x`-sections in `⨅ j, m₂ j`, so
`ν (Prod.mk x ⁻¹' s) ∈ {0, 1}` for every `x`; the section measure
`x ↦ ν (Prod.mk x ⁻¹' s)` is measurable for every `m₁ i`, hence for `⨅ i, m₁ i`; being
`{0,1}`-valued it is the indicator of a set `T` in `⨅ i, m₁ i`, and Fubini gives
`(μ ⊗ ν) s = μ T ∈ {0, 1}`.

This is *not* the same as triviality on `(⨅ i, m₁ i).prod (⨅ j, m₂ j)`, which is in general a
strictly smaller σ-algebra. -/
theorem Measure.prod_apply_eq_zero_or_one_iInf {ι κ : Sort*} [Nonempty ι] [Nonempty κ]
    {m₁ : ι → MeasurableSpace X} {m₂ : κ → MeasurableSpace Y}
    (h₁ : ∀ i, m₁ i ≤ mX) (h₂ : ∀ j, m₂ j ≤ mY)
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ A, MeasurableSet[⨅ i, m₁ i] A → μ A = 0 ∨ μ A = 1)
    (hν : ∀ B, MeasurableSet[⨅ j, m₂ j] B → ν B = 0 ∨ ν B = 1)
    {s : Set (X × Y)} (hs : MeasurableSet[⨅ i, ⨅ j, (m₁ i).prod (m₂ j)] s) :
    μ.prod ν s = 0 ∨ μ.prod ν s = 1 := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hs' : ∀ i j, MeasurableSet[(m₁ i).prod (m₂ j)] s := fun i j ↦
    MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hs i) j
  -- Every section of `s` lies in `⨅ j, m₂ j`, so `ν` gives it mass `0` or `1`.
  have hsec : ∀ x, MeasurableSet[⨅ j, m₂ j] (Prod.mk x ⁻¹' s) := fun x ↦
    MeasurableSpace.measurableSet_iInf.2 fun j ↦ measurableSet_preimage_prodMk_left (hs' i₀ j) x
  -- The section measure is measurable for every `m₁ i`, hence for `⨅ i, m₁ i`.
  have hmeas : Measurable[⨅ i, m₁ i] fun x ↦ ν (Prod.mk x ⁻¹' s) :=
    (measurable_iInf_iff_forall _).2 fun i ↦
      measurable_measure_preimage_prodMk_left ν
        (MeasurableSpace.prod_le_prod le_rfl (h₂ j₀) _ (hs' i j₀))
  set T : Set X := {x | ν (Prod.mk x ⁻¹' s) = 1} with hT
  have hTiInf : MeasurableSet[⨅ i, m₁ i] T := hmeas (measurableSet_singleton 1)
  have hTamb : MeasurableSet T := le_trans (iInf_le _ i₀) (h₁ i₀) _ hTiInf
  have hval : ∀ x, ν (Prod.mk x ⁻¹' s) = T.indicator 1 x := by
    intro x
    rcases hν _ (hsec x) with h0 | h1
    · rw [h0, Set.indicator_of_notMem (by simp [hT, h0])]
    · rw [h1, Set.indicator_of_mem (by simp [hT, h1])]; rfl
  have hsm : MeasurableSet s := MeasurableSpace.prod_le_prod (h₁ i₀) (h₂ j₀) _ (hs' i₀ j₀)
  have hint : μ.prod ν s = μ T := by
    rw [Measure.prod_apply hsm]
    simp_rw [hval]
    exact lintegral_indicator_one hTamb
  rw [hint]
  exact hμ T hTiInf

end iInf

section Plain

variable {m₁ : MeasurableSpace X} {m₂ : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **Zero-one law for a product measure.** If a probability measure `μ` on `X` is trivial on a
sub-σ-algebra `m₁` and a probability measure `ν` on `Y` is trivial on a sub-σ-algebra `m₂`, then
`μ ⊗ ν` is trivial on `m₁.prod m₂`. -/
theorem Measure.prod_apply_eq_zero_or_one (h₁ : m₁ ≤ mX) (h₂ : m₂ ≤ mY)
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ A, MeasurableSet[m₁] A → μ A = 0 ∨ μ A = 1)
    (hν : ∀ B, MeasurableSet[m₂] B → ν B = 0 ∨ ν B = 1)
    {s : Set (X × Y)} (hs : MeasurableSet[m₁.prod m₂] s) :
    μ.prod ν s = 0 ∨ μ.prod ν s = 1 :=
  Measure.prod_apply_eq_zero_or_one_iInf (m₁ := fun _ : Unit ↦ m₁) (m₂ := fun _ : Unit ↦ m₂)
    (fun _ ↦ h₁) (fun _ ↦ h₂)
    (fun A hA ↦ hμ A (by rwa [iInf_const] at hA))
    (fun B hB ↦ hν B (by rwa [iInf_const] at hB))
    (by rw [iInf_const, iInf_const]; exact hs)

end Plain

end MeasureTheory

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Reindexing a product of copies of a measure along a bijection

`MeasureTheory.map_comp_equiv_pi` is `MeasureTheory.measurePreserving_piCongrLeft` for a constant
family, in the form in which it is used: precomposition with a bijection of the index type
carries `μ^κ` to `μ^ι`.  Unlike the version for a mere injection, no finiteness of `μ` is needed,
because no coordinate is integrated out.
-/

@[expose] public section

namespace MeasureTheory

variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]

/-- **Reindexing a finite product of copies of a σ-finite measure along a bijection.** -/
theorem map_comp_equiv_pi (μ : Measure X) [SigmaFinite μ] (e : ι ≃ κ) :
    (Measure.pi fun _ : κ ↦ μ).map (fun ζ : κ → X ↦ ζ ∘ e) = Measure.pi fun _ : ι ↦ μ := by
  have hfun : (fun ζ : κ → X ↦ ζ ∘ e)
      = ⇑(MeasurableEquiv.piCongrLeft (fun _ : κ ↦ X) e).symm := by
    funext ζ i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
  rw [hfun]
  exact (measurePreserving_piCongrLeft (fun _ : κ ↦ μ) e).symm.map_eq

end MeasureTheory

end

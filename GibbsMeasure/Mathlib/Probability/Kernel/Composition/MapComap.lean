/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# `Kernel.map` after `Kernel.comap`
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {δ : Type*} {mδ : MeasurableSpace δ}

lemma coe_map_comap (κ : Kernel α β) {g : γ → α} (hg : Measurable g) {f : β → δ}
    (hf : Measurable f) : ⇑((κ.comap g hg).map f) = fun c ↦ (κ (g c)).map f :=
  funext fun c ↦ by rw [map_apply _ hf, comap_apply]

end ProbabilityTheory.Kernel

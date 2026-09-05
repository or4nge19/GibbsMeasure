/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A probability measure which is a product measure is the product of its marginals

If a probability measure `ρ` on `α × β` is of the form `μ.prod ν` for *some* finite measures
`μ`, `ν`, then `ρ = ρ.fst.prod ρ.snd`: the two marginals are `ρ.fst = ν(univ) • μ` and
`ρ.snd = μ(univ) • ν`, and `μ(univ) ν(univ) = ρ(univ) = 1`. This is the statement behind
"`X` and `Y` are independent iff the law of `(X, Y)` is a product measure".

The lemma sits next to `MeasureTheory.Measure.prod_smul_right`, which lives in Mathlib's
`WithDensity` file because the instance `SFinite (c • ν)` is defined there.
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A probability measure on a product which is *some* product measure is the product of its two
marginals. -/
theorem eq_fst_prod_snd_of_eq_prod {ρ : Measure (α × β)} [IsProbabilityMeasure ρ]
    {μ : Measure α} {ν : Measure β} [SFinite ν] (h : ρ = μ.prod ν) : ρ = ρ.fst.prod ρ.snd := by
  have hmass : μ Set.univ * ν Set.univ = 1 := by
    rw [← prod_prod, Set.univ_prod_univ, ← h, measure_univ]
  subst h
  rw [fst, snd, map_fst_prod, map_snd_prod, prod_smul_left, prod_smul_right, smul_smul,
    mul_comm, hmass, one_smul]

end MeasureTheory.Measure

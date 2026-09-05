/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Algebra.Order.Group.Action.Synonym
public import Mathlib.MeasureTheory.Group.Action

/-!
# Measurable actions by order synonyms

The order synonyms `Mᵒᵈ` and `Lex M` of an acting monoid `M` carry the same action on a
measurable space `α` as `M` does (`Mathlib/Algebra/Order/Group/Action/Synonym.lean`), so they
also act measurably, and preserve exactly the same measures. These are the measure-theoretic
companions of the instances in that file; they cannot live there, since it is an algebra file.
-/

@[expose] public section

open MeasureTheory

variable {M α : Type*} [MeasurableSpace α]

namespace OrderDual

@[to_additive]
instance instMeasurableConstSMul [SMul M α] [MeasurableConstSMul M α] :
    MeasurableConstSMul Mᵒᵈ α := inferInstanceAs (MeasurableConstSMul M α)

@[to_additive]
instance instSMulInvariantMeasure [SMul M α] {μ : Measure α} [SMulInvariantMeasure M α μ] :
    SMulInvariantMeasure Mᵒᵈ α μ := inferInstanceAs (SMulInvariantMeasure M α μ)

end OrderDual

namespace Lex

@[to_additive]
instance instMeasurableConstSMul [SMul M α] [MeasurableConstSMul M α] :
    MeasurableConstSMul (Lex M) α := inferInstanceAs (MeasurableConstSMul M α)

@[to_additive]
instance instSMulInvariantMeasure [SMul M α] {μ : Measure α} [SMulInvariantMeasure M α μ] :
    SMulInvariantMeasure (Lex M) α μ := inferInstanceAs (SMulInvariantMeasure M α μ)

end Lex

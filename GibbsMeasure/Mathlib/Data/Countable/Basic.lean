/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.Countable.Basic
public import Mathlib.Order.Lex

/-!
# `Lex α` is countable when `α` is
-/

@[expose] public section

/-- `Lex α` is countable when `α` is. Intended home: `Mathlib/Data/Countable/Basic.lean`. -/
instance Lex.instCountable {α : Type*} [Countable α] : Countable (Lex α) := ‹Countable α›

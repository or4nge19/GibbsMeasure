/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable

/-!
# Ground states, Georgii Definition (6.18)

A configuration `ω` is a *ground state* of a potential `Ψ` when no finite perturbation of `ω`
lowers the energy: `H_Λ^Ψ(ω) ≤ H_Λ^Ψ(ζ)` whenever `Λ` is finite and `ζ = ω` off `Λ`.
Georgii's staircases (6.19) are the motivating non-constant examples
(`GibbsMeasure/Model/RandomStaircase.lean`).
-/

@[expose] public section

namespace Potential

/-- **Georgii Definition (6.18).** A configuration `ω` is a *ground state* of the potential `Ψ`
when every finite perturbation of `ω` has at least the energy of `ω`: `H_Λ^Ψ(ζ) ≥ H_Λ^Ψ(ω)`
whenever `Λ` is finite and `ζ = ω` off `Λ`.

This is weaker than minimising every interaction term `Ψ_A`; Georgii's staircases (6.19) are
ground states in this sense without being constant. -/
def IsGroundState {S E : Type*} [MeasurableSpace E] (Ψ : Potential S E) (ω : S → E) : Prop :=
  ∀ (Λ : Finset S) (ζ : S → E), (∀ i ∉ Λ, ζ i = ω i) → Ψ.hamiltonian Λ ω ≤ Ψ.hamiltonian Λ ζ

end Potential

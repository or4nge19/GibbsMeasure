import Comparator.Defs_Ising

/-!
# Comparator challenge: the two-dimensional Ising phase transition (Georgii, Theorem (6.9))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).

**Its only import is `Comparator.Defs_Ising`, which in turn imports `Mathlib` and nothing else.**
In particular nothing here depends on the `GibbsMeasure` library whose theorem is being certified:
every notion appearing in the final statements — the lattice `ℤ²`, the spin variables, the
nearest-neighbour bonds, the Hamiltonian, the finite-volume Gibbs distribution, the DLR equation,
the lattice shifts — is spelled out from first principles using only `Mathlib` in
`Comparator/Defs_Ising.lean`, whose module docstring contains the dictionary. A skeptical reader
can check each definition by eye against the physics without having to trust anything else.

## Main statements

* `ising_phase_transition`: **Georgii, Theorem (6.9), the "in particular" half.** At all
  sufficiently low temperatures the two-dimensional Ising ferromagnet has two distinct
  shift-invariant Gibbs measures, exchanged by the global spin flip, with strictly negative
  respectively strictly positive spontaneous magnetisation.
* `ising_uniqueness_at_high_temperature`: the Dobrushin half, stated only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace IsingChallenge

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), the "in particular" half: the two-dimensional Ising phase
transition.** There is an inverse temperature `β₀` such that for every `β ≥ β₀` the two-dimensional
Ising ferromagnet admits two *distinct* Gibbs measures `μ₊` and `μ₋`, both invariant under all
lattice translations, exchanged by the global spin flip, and exhibiting spontaneous magnetisation:
the expected spin at the origin is strictly negative under `μ₋` and strictly positive under `μ₊`. -/
theorem ising_phase_transition :
    ∃ β₀ : ℝ, ∀ β ≥ β₀, ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      μp ≠ μm ∧
      (∀ j : Site, μp.map (shift j) = μp) ∧
      (∀ j : Site, μm.map (shift j) = μm) ∧
      μm = μp.map (fun σ i ↦ !σ i) ∧
      ∫ σ, spin (σ 0) ∂μm < 0 ∧
      0 < ∫ σ, spin (σ 0) ∂μp :=
  sorry

/-- **The Dobrushin half: uniqueness at high temperature.** When the inverse temperature is small
enough — Dobrushin's condition holds for the two-dimensional Ising model as soon as `β < 1 / 4`,
since every site has four neighbours — the Gibbs measure is unique. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

end IsingChallenge

end

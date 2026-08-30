import Comparator.Defs_Ising

/-!
# Comparator challenge: the two-dimensional Ising phase transition (Georgii, Theorem (6.9))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).

**Its only import is `Comparator.Defs_Ising`, which in turn imports `Mathlib` and nothing else.**
In particular nothing here depends on the `GibbsMeasure` library whose theorems are being
certified: every notion appearing in the final statements — the lattice `ℤ²`, the spin variables,
the nearest-neighbour bonds, the Hamiltonian, the finite-volume Gibbs distribution, the DLR
equation, the lattice shifts, the local events, the critical inverse temperature — is spelled out
from first principles using only `Mathlib` in `Comparator/Defs_Ising.lean`, whose module docstring
contains the dictionary. A skeptical reader can check each definition by eye against the physics
without having to trust anything else.

## Main statements

* `ising_phase_transition`: **Georgii, Theorem (6.9), the "in particular" half**, at the explicit
  threshold `β ≥ log 3`: two distinct shift-invariant Gibbs measures, spin-flip conjugate, with
  spontaneous magnetisations of opposite sign.
* `quarter_le_betaC`, `betaC_le_log_three`, `ising_existsUnique_gibbs_of_lt_betaC`,
  `ising_nonuniqueness_of_betaC_lt`: the critical inverse temperature `β_c` of `Defs_Ising` is a
  genuine threshold, `1/4 ≤ β_c ≤ log 3`, with uniqueness strictly below and non-uniqueness
  strictly above. Nothing is claimed at `β = β_c`.
* `ising_uniqueness_at_high_temperature`, `ising_uniqueness_of_lt_quarter`: uniqueness below
  `β_c`, and its Dobrushin corollary below `1/4`.
* `ising_plus_minus_phases`: the plus and minus phases as genuine local limits of the
  finite-volume distributions with constant boundary conditions, sandwiching every Gibbs measure.
* `ising_lebowitz_martin_lof`: the Lebowitz–Martin-Löf/Ruelle criterion `|𝒢(βΦ)| > 1 ↔ m*(β) > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace IsingChallenge

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), the "in particular" half, at the explicit threshold `log 3`.**
For every inverse temperature `β ≥ log 3` the two-dimensional Ising ferromagnet admits two
*distinct* Gibbs measures `μ₊` and `μ₋`, both invariant under all lattice translations, exchanged
by the global spin flip, and exhibiting spontaneous magnetisation: the expected spin at the origin
is strictly negative under `μ₋` and strictly positive under `μ₊`. -/
theorem ising_phase_transition (β : ℝ) (hβ : Real.log 3 ≤ β) :
    ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      μp ≠ μm ∧
      (∀ j : Site, μp.map (shift j) = μp) ∧
      (∀ j : Site, μm.map (shift j) = μm) ∧
      μm = μp.map (fun σ i ↦ !σ i) ∧
      ∫ σ, spin (σ 0) ∂μm < 0 ∧
      0 < ∫ σ, spin (σ 0) ∂μp :=
  sorry

/-- **`β_c ≥ 1/4`** — Dobrushin's uniqueness condition, Georgii (8.7) with (8.8). -/
theorem quarter_le_betaC : (1 : ℝ) / 4 ≤ betaC :=
  sorry

/-- **`β_c ≤ log 3`** — the Peierls argument at Georgii's own contour count. -/
theorem betaC_le_log_three : betaC ≤ Real.log 3 :=
  sorry

/-- **Uniqueness strictly below the critical inverse temperature.** For every `0 ≤ β < β_c` there
is exactly one Gibbs measure. -/
theorem ising_existsUnique_gibbs_of_lt_betaC (β : ℝ) (hβ₀ : 0 ≤ β) (hβ : β < betaC) :
    ∃! μ : Measure Config, IsGibbs β μ :=
  sorry

/-- **Non-uniqueness strictly above the critical inverse temperature.** For every `β > β_c` there
are two distinct Gibbs measures. -/
theorem ising_nonuniqueness_of_betaC_lt (β : ℝ) (hβ : betaC < β) :
    ∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν :=
  sorry

/-- **Uniqueness at high temperature**, up to the critical inverse temperature. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < betaC → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

/-- **The Dobrushin bound.** Dobrushin's condition holds for the two-dimensional Ising model as
soon as `β < 1 / 4`, since every site has four neighbours; a fortiori the Gibbs measure is then
unique. -/
theorem ising_uniqueness_of_lt_quarter :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

/-- **The plus and minus phases as genuine limits** (Georgii, Section 6.2, after (6.9)). For every
`β ≥ 0` the finite-volume Gibbs distributions with the all-`+` boundary condition converge, on
every local event, to a Gibbs measure `μ₊`, and those with the all-`-` boundary condition converge
to a Gibbs measure `μ₋`; every Gibbs measure `μ` is sandwiched between them in the stochastic
order, `μ₋ ≤ μ ≤ μ₊` on measurable increasing events. -/
theorem ising_plus_minus_phases (β : ℝ) (hβ : 0 ≤ β) :
    ∃ μp μm : Measure Config,
      IsGibbs β μp ∧
      IsGibbs β μm ∧
      (∀ A : Set Config, IsLocal A →
        Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A)
          Filter.atTop (nhds (μp A))) ∧
      (∀ A : Set Config, IsLocal A →
        Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ false) A)
          Filter.atTop (nhds (μm A))) ∧
      (∀ μ : Measure Config, IsGibbs β μ →
        ∀ A : Set Config, MeasurableSet A → IsUpperSet A → μ A ≤ μp A) ∧
      (∀ μ : Measure Config, IsGibbs β μ →
        ∀ A : Set Config, MeasurableSet A → IsUpperSet A → μm A ≤ μ A) :=
  sorry

/-- **The Lebowitz–Martin-Löf/Ruelle criterion** (Georgii, Section 6.2, the paragraph after (6.9),
where it is cited without proof). For `β ≥ 0` the two-dimensional Ising ferromagnet has more than
one Gibbs measure if and only if the spontaneous magnetisation is strictly positive, i.e. the
expected spin at the origin under the plus phase `μ₊` is strictly positive. Here `μ₊` is pinned
down by being the limit of the finite-volume distributions with all-`+` boundary condition; such a
measure exists by `ising_plus_minus_phases`. -/
theorem ising_lebowitz_martin_lof (β : ℝ) (hβ : 0 ≤ β) (μp : Measure Config)
    (hμp : ∀ A : Set Config, IsLocal A →
      Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A)
        Filter.atTop (nhds (μp A))) :
    (∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν)
      ↔ 0 < ∫ σ, spin (σ 0) ∂μp :=
  sorry

end IsingChallenge

end

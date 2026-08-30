import Comparator.Defs_Ising

/-!
# Comparator challenge: the two-dimensional Ising phase transition

Georgii, Theorem (6.9), stated over the from-scratch definitions of `Comparator.Defs_Ising`.

## Main statements

* `ising_phase_transition`: **Georgii (6.9)**, the "in particular" half, at the explicit threshold
  `β ≥ log 3`.
* `quarter_le_betaC`, `betaC_le_log_three`, `ising_existsUnique_gibbs_of_lt_betaC`,
  `ising_nonuniqueness_of_betaC_lt`: `betaC` is a genuine threshold, `1/4 ≤ β_c ≤ log 3`, with
  uniqueness strictly below and non-uniqueness strictly above. Nothing is claimed at `β = β_c`.
* `ising_uniqueness_at_high_temperature`, `ising_uniqueness_of_lt_quarter`: uniqueness below `β_c`
  and its Dobrushin corollary below `1/4`.
* `ising_plus_minus_phases`: the plus and minus phases as local limits of the finite-volume
  distributions with constant boundary conditions, sandwiching every Gibbs measure.
* `ising_lebowitz_martin_lof`: the Lebowitz–Martin-Löf/Ruelle criterion `|𝒢(βΦ)| > 1 ↔ m*(β) > 0`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace IsingChallenge

/-! ### The theorems -/

/-- **Georgii (6.9)**, the "in particular" half at the explicit threshold `log 3`: for `β ≥ log 3`
the two-dimensional Ising ferromagnet admits two distinct shift-invariant Gibbs measures, exchanged
by the global spin flip, with spontaneous magnetisations of opposite sign. -/
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

/-- **Georgii (8.7) with (8.8)**, Dobrushin's uniqueness condition: `β_c ≥ 1/4`. -/
theorem quarter_le_betaC : (1 : ℝ) / 4 ≤ betaC :=
  sorry

/-- `β_c ≤ log 3`, by the Peierls argument at Georgii's own contour count. -/
theorem betaC_le_log_three : betaC ≤ Real.log 3 :=
  sorry

/-- For every `0 ≤ β < β_c` there is exactly one Gibbs measure. -/
theorem ising_existsUnique_gibbs_of_lt_betaC (β : ℝ) (hβ₀ : 0 ≤ β) (hβ : β < betaC) :
    ∃! μ : Measure Config, IsGibbs β μ :=
  sorry

/-- For every `β > β_c` there are two distinct Gibbs measures. -/
theorem ising_nonuniqueness_of_betaC_lt (β : ℝ) (hβ : betaC < β) :
    ∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν :=
  sorry

/-- Uniqueness at high temperature, up to the critical inverse temperature. -/
theorem ising_uniqueness_at_high_temperature :
    ∀ β : ℝ, 0 ≤ β → β < betaC → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

/-- **Georgii (8.7) with (8.8)**: since every site has four neighbours, Dobrushin's condition
holds as soon as `β < 1 / 4`, so the Gibbs measure is then unique. -/
theorem ising_uniqueness_of_lt_quarter :
    ∀ β : ℝ, 0 ≤ β → β < 1 / 4 → ∀ μ ν : Measure Config, IsGibbs β μ → IsGibbs β ν → μ = ν :=
  sorry

/-- **Georgii, Section 6.2, after (6.9)**: for `β ≥ 0` the finite-volume Gibbs distributions with
constant boundary conditions converge on every local event to Gibbs measures `μ₊` and `μ₋`, which
sandwich every Gibbs measure in the stochastic order. -/
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

/-- **Georgii, Section 6.2** (the Lebowitz–Martin-Löf/Ruelle criterion, cited there without
proof): for `β ≥ 0` the model has more than one Gibbs measure iff the spontaneous magnetisation is
strictly positive. Here `μ₊` is pinned down as the all-`+` local limit, which exists by
`ising_plus_minus_phases`. -/
theorem ising_lebowitz_martin_lof (β : ℝ) (hβ : 0 ≤ β) (μp : Measure Config)
    (hμp : ∀ A : Set Config, IsLocal A →
      Filter.Tendsto (fun Λ : Finset Site ↦ gibbsMeasure β Λ (fun _ ↦ true) A)
        Filter.atTop (nhds (μp A))) :
    (∃ μ ν : Measure Config, IsGibbs β μ ∧ IsGibbs β ν ∧ μ ≠ ν)
      ↔ 0 < ∫ σ, spin (σ 0) ∂μp :=
  sorry

end IsingChallenge

end

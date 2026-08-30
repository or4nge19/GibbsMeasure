import Comparator.Defs_LowTemperature

/-!
# Comparator challenge: Georgii Theorem (6.9), first assertion — the low-temperature limit

The first assertion of Georgii's Theorem (6.9) for the two-dimensional Ising ferromagnet:
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`.  (`Comparator/Challenge.lean`
states only the second, "in particular", assertion.)

Because `sInf ∅ = 0` by convention in `ℝ`, a statement about `d(F, ν)` alone could be satisfied
vacuously; `ising_low_temperature_limit` therefore asserts the content of Georgii's proof
directly, exhibiting shift-invariant Gibbs measures `μ₊^β, μ₋^β ∈ 𝒢_Θ(βΦ)` converging locally to
`δ₊` and `δ₋`.

## Main statements

* `ising_low_temperature_limit`: Theorem (6.9), first assertion, in the form established by
  Georgii's proof
* `ising_low_temperature_localDistSet`: the same in the displayed form
* `ising_low_temperature_peierls`: the quantitative Peierls estimate
  `|μ_±^β(A) − δ_±(A)| ≤ |Λ| r(β)` for `Λ`-local `A` and `β ≥ 8 log 2`, with `r(β) → 0`

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Theorem (6.9)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

noncomputable section

namespace IsingChallenge

/-! ### The theorems -/

/-- **Georgii, Theorem (6.9), first assertion**, in the form produced by Georgii's proof: there
are families `β ↦ μ₊^β`, `β ↦ μ₋^β` of shift-invariant Gibbs measures of the two-dimensional Ising
ferromagnet with `μ₊^β → δ₊` and `μ₋^β → δ₋` as `β → ∞`, both in the topology of local convergence
(4.2) and in every metric `d` of Remark (4.3)(3) built from a sequence of local events. -/
theorem ising_low_temperature_limit :
    ∃ μp μm : ℝ → Measure Config,
      (∀ β : ℝ, μp β ∈ shiftInvariantGibbs β) ∧
      (∀ β : ℝ, μm β ∈ shiftInvariantGibbs β) ∧
      TendstoLocally μp atTop (Measure.dirac fun _ : Site ↦ true) ∧
      TendstoLocally μm atTop (Measure.dirac fun _ : Site ↦ false) ∧
      (∀ A : ℕ → Set Config, (∀ n : ℕ, IsLocalEvent (A n)) →
        Tendsto (fun β : ℝ ↦ localDist A (μp β) (Measure.dirac fun _ : Site ↦ true))
            atTop (𝓝 0) ∧
          Tendsto (fun β : ℝ ↦ localDist A (μm β) (Measure.dirac fun _ : Site ↦ false))
            atTop (𝓝 0)) :=
  sorry

/-- **Georgii, Theorem (6.9), first assertion**, in the displayed form
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`, for the metric `d` of Remark
(4.3)(3) built from an arbitrary sequence `A` of local events. -/
theorem ising_low_temperature_localDistSet (A : ℕ → Set Config)
    (hA : ∀ n : ℕ, IsLocalEvent (A n)) :
    Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ true)) atTop (𝓝 0) ∧
      Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ false)) atTop (𝓝 0) :=
  sorry

/-- **Georgii, Theorem (6.9), first assertion** in quantitative form: shift-invariant Gibbs
measures `μ₊^β, μ₋^β` with `|μ_±^β(A) − δ_±(A)| ≤ |Λ| r(β)` for `β ≥ 8 log 2` and every `Λ`-local
`A`, where `r(β)` is `peierlsBound` and `r(β) → 0`.  `8 log 2` and the constant inside
`peierlsBound` are what this development proves; they are not sharp, and nothing is asserted about
the critical inverse temperature. -/
theorem ising_low_temperature_peierls :
    Tendsto (fun β : ℝ ↦ (peierlsBound β).toReal) atTop (𝓝 0) ∧
      ∃ μp μm : ℝ → Measure Config,
        (∀ β : ℝ, μp β ∈ shiftInvariantGibbs β) ∧
        (∀ β : ℝ, μm β ∈ shiftInvariantGibbs β) ∧
        (∀ β : ℝ, 8 * Real.log 2 ≤ β → ∀ (Λ : Finset Site) (A : Set Config), MeasurableSet A →
          (∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) →
            |(μp β A).toReal
                - (((Measure.dirac fun _ : Site ↦ true) : Measure Config) A).toReal|
              ≤ Λ.card * (peierlsBound β).toReal) ∧
        ∀ β : ℝ, 8 * Real.log 2 ≤ β → ∀ (Λ : Finset Site) (A : Set Config), MeasurableSet A →
          (∀ ζ ζ' : Config, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A)) →
            |(μm β A).toReal
                - (((Measure.dirac fun _ : Site ↦ false) : Measure Config) A).toReal|
              ≤ Λ.card * (peierlsBound β).toReal := by
  sorry

end IsingChallenge

end

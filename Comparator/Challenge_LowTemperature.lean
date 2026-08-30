import Comparator.Defs_LowTemperature

/-!
# Comparator challenge: Georgii Theorem (6.9), first assertion — the low-temperature limit

This is the *challenge* file for the **first** assertion of Georgii, *Gibbs Measures and Phase
Transitions*, 2nd ed., Theorem (6.9):
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`
for the two-dimensional Ising ferromagnet, where `d` is a metric for the topology of local
convergence and `𝒢_Θ(βΦ)` is the set of shift-invariant Gibbs measures.
(`Comparator/Challenge.lean` of this repository states only the *second* assertion, the
"in particular" half.)

Its only import is `Comparator.Defs_LowTemperature`, whose transitive imports are
`Comparator.Defs`, `Comparator.Defs_Ising` and `Mathlib` and nothing else; in particular nothing
here depends on the `GibbsMeasure` library whose theorems are being certified.  The shared
Mathlib-only vocabulary is in `Comparator/Defs.lean`, the two-dimensional Ising model in
`Comparator/Defs_Ising.lean` (shared verbatim with `Comparator/Challenge.lean`), and Georgii's
metric of Remark (4.3)(3) in `Comparator/Defs_LowTemperature.lean`; the three module docstrings
contain the dictionary.

## Design note

Because `sInf ∅ = 0` by convention in `ℝ`, a statement about `d(F, ν)` alone could conceivably be
satisfied vacuously.  `ising_low_temperature_limit` therefore asserts the content of Georgii's
proof directly: it *exhibits* shift-invariant Gibbs measures `μ₊^β, μ₋^β ∈ 𝒢_Θ(βΦ)` converging
locally (in the sense of `Comparator.Defs`'s `TendstoLocally`, which is Georgii's (4.2) verbatim,
and in the sense of `localDist`) to `δ₊` and `δ₋`.  The displayed form
`lim_β d(𝒢_Θ(βΦ), δ_±) = 0` is then `ising_low_temperature_localDistSet`.

## Main statements

* `ising_low_temperature_limit`: **Georgii, Theorem (6.9), first assertion**, in the form
  established by Georgii's proof.
* `ising_low_temperature_localDistSet`: the same, in the displayed form
  `lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`.
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

/-- **Georgii, Theorem (6.9), first assertion**, in the form produced by Georgii's proof: at low
temperature the shift-invariant Gibbs measures of the two-dimensional Ising ferromagnet are
attracted by the two ground states.

Explicitly, there are families `β ↦ μ₊^β` and `β ↦ μ₋^β` of *shift-invariant Gibbs measures* for
the two-dimensional Ising ferromagnet at inverse temperature `β` such that, as `β → ∞`,
`μ₊^β → δ₊` and `μ₋^β → δ₋` in the topology of local convergence (Georgii (4.2)), equivalently
`d(μ₊^β, δ₊) → 0` and `d(μ₋^β, δ₋) → 0` for Georgii's metric `d` of Remark (4.3)(3) — here for
*every* metric obtained from a sequence of local events, in particular for every enumeration of
the algebra `𝓕⁰`. -/
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
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`,
where `d` is Georgii's metric of Remark (4.3)(3) for the topology of local convergence — built
here from an arbitrary sequence `A` of local events, so that the statement covers every such
metric — and `𝒢_Θ(βΦ)` is the set of shift-invariant Gibbs measures of the two-dimensional Ising
ferromagnet at inverse temperature `β`. -/
theorem ising_low_temperature_localDistSet (A : ℕ → Set Config)
    (hA : ∀ n : ℕ, IsLocalEvent (A n)) :
    Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ true)) atTop (𝓝 0) ∧
      Tendsto (fun β : ℝ ↦ localDistSet A (shiftInvariantGibbs β)
        (Measure.dirac fun _ : Site ↦ false)) atTop (𝓝 0) :=
  sorry

end IsingChallenge

end

import Comparator.Defs_Sharpness

/-!
# Comparator challenge: Georgii, Example (2.27) — Dobrushin's condition needs quasilocality

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_Sharpness`, whose transitive imports are
`Comparator.Defs_Dobrushin`, `Comparator.Defs` and `Mathlib` and nothing else; in particular
nothing here depends on the `GibbsMeasure` library whose theorems are being certified. The shared
Mathlib-only vocabulary (`Config`, `IsSpecification`, `IsGibbs`, …) is defined in
`Comparator/Defs.lean`, Georgii's Section 8.1 (`unifDist`, `proj`, `interdep`, `IsQuasilocalSpec`,
`IsDobrushin`) in `Comparator/Defs_Dobrushin.lean`, and the Bernoulli measures `λ^x`, `μ^x` of
Example (2.27) in `Comparator/Defs_Sharpness.lean`; all three module docstrings contain the
dictionary.

## What is at stake

`Comparator/Challenge_Dobrushin.lean` states Georgii's Theorem (8.7): a specification satisfying
Dobrushin's condition of weak dependence (8.6) has at most one Gibbs measure. Condition (8.6) is a
conjunction: `γ` is quasilocal, **and** `c(γ) = sup_i ∑_j C_ij(γ) < 1`. It is fair to ask whether
the first conjunct does any work. Georgii's Example (2.27) answers that it does.

Take `E = {0,1}`, `S = ℕ`, and glue the independent specifications of the Bernoulli measures `λ^x`
along the *tail* function `ξ = liminf_n n⁻¹ ∑_{i<n} σ_i`, as in Remark (2.26). A single-site
change of the boundary condition changes neither `ξ` nor the resulting single-spin law, so
`C_ij(γ) = 0` for all `i, j` and `c(γ) = 0`; and yet every Bernoulli random field `μ^x`,
`x ∈ [0,1]`, is a Gibbs measure for `γ`, so `𝓖(γ)` is uncountable.

Both statements below are *sharpness* statements. Neither contradicts (8.7): the specification
they produce is not quasilocal, hence does not satisfy (8.6). What they show is that the
quasilocality conjunct of (8.6) cannot be removed — with it removed, (8.7) would assert that this
uncountable `𝓖(γ)` has at most one element.

## Main statements

* `exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec`: **Georgii, Example (2.27)**.
* `not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one`: the same example read against Theorem
  (8.7).

## What is *not* claimed

Georgii also identifies `𝓖(γ)` exactly, as `{∫ w(dx) μ^x : w ∈ 𝓟([0,1])}`, i.e. as the set of all
exchangeable random fields. That identification rests on de Finetti's theorem, which Georgii
proves separately at Example (7.31); it is not formalised in the library and is not claimed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace SharpnessChallenge

open GibbsChallenge DobrushinChallenge

/-! ## The theorems -/

/-- **Georgii, Example (2.27)**, the sharpness of Dobrushin's condition (8.6): there is a
specification `γ` on `Ω = {0,1}^ℕ` whose interdependence matrix vanishes identically, so that
`c(γ) = 0 < 1`, which has *every* Bernoulli random field `μ^x`, `x ∈ [0,1]`, among its Gibbs
measures — in particular `𝓖(γ)` is uncountable — and which is **not** quasilocal.

This does not contradict Dobrushin's uniqueness theorem (8.7), and the last conjunct says exactly
why: `γ` fails Dobrushin's condition (8.6), and it fails it *only* through the quasilocality
conjunct. What the statement does show is that the quasilocality conjunct of (8.6) cannot be
dropped: with it removed, (8.7) would assert that this `𝓖(γ)` is a singleton. -/
theorem exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ (∀ i j, interdep γ i j = 0) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, IsGibbs γ (bernoulliField x)) ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Countable ∧
        ¬ IsQuasilocalSpec γ ∧ ¬ IsDobrushin γ := by
  sorry

/-- **Georgii, Example (2.27)**, stated against Theorem (8.7): the second conjunct of Dobrushin's
condition (8.6), `c(γ) = sup_i ∑_j C_ij(γ) < 1`, does **not** by itself imply that `𝓖(γ)` has at
most one element. So the quasilocality conjunct of (8.6) is not decorative: dropping it from the
hypothesis of `DobrushinChallenge.subsingleton_isGibbs_of_isDobrushin` would make that theorem
false. -/
theorem not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ ⨆ i, ∑' j, interdep γ i j < 1 ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Subsingleton := by
  sorry

end SharpnessChallenge

end

import Comparator.Defs_Sharpness

/-!
# Georgii, Example (2.27): Dobrushin's condition needs quasilocality

Dobrushin's condition (8.6) is a conjunction: `γ` is quasilocal **and**
`c(γ) = sup_i ∑_j C_ij(γ) < 1`. Georgii's Example (2.27) glues the independent specifications of
the Bernoulli measures `λ^x` on `{0,1}^ℕ` along the tail function `ξ = liminf_n n⁻¹ ∑_{i<n} σ_i`,
producing a non-quasilocal specification with `c(γ) = 0` whose Gibbs measures include every `μ^x`,
`x ∈ [0,1]`. Neither statement below contradicts Theorem (8.7); together they show that its
quasilocality hypothesis cannot be dropped.

Not claimed: Georgii's exact identification of `𝓖(γ)` with the exchangeable random fields, which
rests on de Finetti's theorem (Example (7.31)) and is not formalised in the library.

## Main statements

* `exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec`: Georgii, Example (2.27).
* `not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one`: the same example read against Theorem
  (8.7).
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

/-- **Georgii, Example (2.27)**: there is a specification `γ` on `Ω = {0,1}^ℕ` whose
interdependence matrix vanishes identically, which has every Bernoulli random field `μ^x`,
`x ∈ [0,1]`, among its Gibbs measures — so `𝓖(γ)` is uncountable — and which is **not**
quasilocal. It fails Dobrushin's condition (8.6) only through the quasilocality conjunct, which is
therefore not droppable from Theorem (8.7). -/
theorem exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ (∀ i j, interdep γ i j = 0) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, IsGibbs γ (bernoulliField x)) ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Countable ∧
        ¬ IsQuasilocalSpec γ ∧ ¬ IsDobrushin γ := by
  sorry

/-- **Georgii, Example (2.27)**, stated against Theorem (8.7): the second conjunct of Dobrushin's
condition, `c(γ) = sup_i ∑_j C_ij(γ) < 1`, does not by itself imply that `𝓖(γ)` has at most one
element. -/
theorem not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ ⨆ i, ∑' j, interdep γ i j < 1 ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Subsingleton := by
  sorry

end SharpnessChallenge

end

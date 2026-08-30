import Comparator.Defs_Sharpness

/-! # Challenge: Georgii Example (2.27) -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace SharpnessChallenge

open GibbsChallenge DobrushinChallenge

theorem exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ (∀ i j, interdep γ i j = 0) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, IsGibbs γ (bernoulliField x)) ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Countable ∧
        ¬ IsQuasilocalSpec γ ∧ ¬ IsDobrushin γ := by
  sorry

theorem not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ ⨆ i, ∑' j, interdep γ i j < 1 ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Subsingleton := by
  sorry

end SharpnessChallenge

end

import Comparator.Defs_Dobrushin

/-!
# Comparator challenge: Dobrushin's uniqueness theorem (Georgii, Theorem (8.7))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_Dobrushin`, whose transitive imports are `Comparator.Defs` and
`Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library whose
theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `outside`, `tail`,
`IsSpecification`, `IsGibbs`, …) is defined in `Comparator/Defs.lean`, and Georgii's Section 8.1
(`unifDist`, `proj`, `interdep`, `IsDobrushin`, `oscAt`, `interdepSeries`, …) in
`Comparator/Defs_Dobrushin.lean`; both module docstrings contain the dictionary.

## Main statements

* `subsingleton_isGibbs_of_isDobrushin`: **Georgii, Theorem (8.7)**. If the specification `γ`
  satisfies Dobrushin's condition of weak dependence then `𝓖(γ)` contains at most one element.
* `ofReal_abs_integral_sub_le_interdepSeries`: **Georgii, Theorem (8.20)**, the Dobrushin
  comparison theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace DobrushinChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## The theorems -/

/-- **Georgii, Theorem (8.7)**: a specification satisfying Dobrushin's condition of weak
dependence has *at most one* Gibbs measure, i.e. `|𝓖(γ)| ≤ 1`. -/
theorem subsingleton_isGibbs_of_isDobrushin
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    {μ : Measure (Config S E) | IsGibbs γ μ}.Subsingleton := by
  sorry

/-- **Georgii, Theorem (8.20)**, the Dobrushin comparison theorem: if `γ` satisfies Dobrushin's
condition, `μ ∈ 𝓖(γ)`, `ν ∈ 𝓖(γ')`, and `b_i` dominates `‖γ_i^0(·|ω) − γ'^0_i(·|ω)‖`, then for
every local observable `f`
`|μ(f) − ν(f)| ≤ ∑_{i,j} δ_i(f) D_ij(γ) ν(b_j)`. -/
theorem ofReal_abs_integral_sub_le_interdepSeries
    (γ γ' : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hγ' : IsSpecification γ') (hd : IsDobrushin γ)
    (μ ν : Measure (Config S E)) (hμ : IsGibbs γ μ) (hν : IsGibbs γ' ν)
    (b : S → Config S E → ℝ≥0∞) (hbm : ∀ i, Measurable (b i))
    (hb : ∀ (i : S) (ω : Config S E), unifDist (proj γ i ω) (proj γ' i ω) ≤ b i ω)
    (f : Config S E → ℝ) (hf : IsLocalFn f) :
    ENNReal.ofReal |(∫ σ, f σ ∂μ) - ∫ σ, f σ ∂ν|
      ≤ ∑' i, interdepSeries γ (fun j ↦ ∫⁻ ω, b j ω ∂ν) i * oscAt f i := by
  sorry

end DobrushinChallenge

end

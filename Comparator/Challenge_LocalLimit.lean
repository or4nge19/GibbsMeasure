import Comparator.Defs_LocalLimit

/-!
# Comparator challenge: local limits of extreme Gibbs measures (Georgii, Theorem (7.12))

Georgii's Theorem (7.12), parts (a) and (c).

## Main statements

* `georgii_7_12_a`, `georgii_7_12_a_measure`: Theorem (7.12)(a), for bounded measurable functions
  and for measurable events
* `georgii_7_12_c`: Theorem (7.12)(c), over an *arbitrary* measurable state space, with one single
  full-measure set of boundary conditions serving all volumes at once
* `georgii_7_12_c_tendstoLocally`: the consequence Georgii draws from (c), convergence in the
  topology of local convergence
* `exists_isLambdaSpec_isExtremeGibbs`: non-degeneracy — the independent specification is a
  λ-specification with `ρ ≡ 1` whose Gibbs measure `ν^S` is extreme

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Theorem (7.12)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section LocalLimit

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii, Theorem (7.12)(a)**: for an extreme Gibbs measure `μ` of `γ` and an increasing
cofinal sequence of volumes, `γ_{Λ n} f → μ(f)` `μ`-almost surely, for every bounded measurable
`f`. -/
theorem georgii_7_12_a [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {f : Config S E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (nhds (∫ x, f x ∂μ)) :=
  sorry

/-- **Georgii, Theorem (7.12)(a)** in the form used for the tail-triviality argument:
`γ_{Λ n}(A | ω) → μ(A)` for `μ`-almost every `ω`, for every measurable event `A`. -/
theorem georgii_7_12_a_measure [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {A : Set (Config S E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ γ (Λ n) ω A) atTop (nhds (μ A)) :=
  sorry

/-- **Georgii, Theorem (7.12)(c)**: for a λ-specification over an arbitrary measurable state space
and `μ ∈ ex 𝓖(γ)`, `sup {|γ_{Λ n}(A | ω) − μ(A)| : A ∈ 𝓕_Δ} → 0` for every finite volume `Δ`, for
`μ`-almost every `ω` — one single full-measure set of `ω`'s serving all volumes at once. -/
theorem georgii_7_12_c [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Tendsto (fun n ↦ tvOn Δ (γ (Λ n) ω) μ) atTop (nhds 0) :=
  sorry

/-- **Georgii, Theorem (7.12)(c)**, the conclusion drawn from the total-variation estimate:
`γ_{Λ n}(· | ω) → μ` in the topology of local convergence of (4.2), for `μ`-almost every `ω`. -/
theorem georgii_7_12_c_tendstoLocally [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, TendstoLocally (fun n ↦ γ (Λ n) ω) atTop μ :=
  sorry

/-- Non-degeneracy of the hypotheses of `georgii_7_12_c`: the independent specification is a
λ-specification with density `ρ ≡ 1`, and its Gibbs measure `ν^S` is extreme. -/
theorem exists_isLambdaSpec_isExtremeGibbs [Countable S] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsLambdaSpec ν (fun _ _ ↦ 1) (indepSpec (S := S) ν) ∧
      IsExtremeGibbs (indepSpec (S := S) ν) (Measure.infinitePi fun _ : S ↦ ν) :=
  sorry

end LocalLimit

end GibbsChallenge

end

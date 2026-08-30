import Comparator.Defs_LocalLimit

/-!
# Comparator challenge: local limits of extreme Gibbs measures (Georgii, Theorem (7.12))

This file is the *challenge* file for [comparator](https://github.com/leanprover/comparator).
Its only import is `Comparator.Defs_LocalLimit`, whose transitive imports are `Comparator.Defs`
and `Mathlib` and nothing else; in particular nothing here depends on the `GibbsMeasure` library
whose theorems are being certified.  The shared Mathlib-only vocabulary (`Config`, `inside`,
`outside`, `tail`, `IsSpecification`, `IsGibbs`, `indepSpec`, `TendstoLocally`, …) is defined in
`Comparator/Defs.lean`, and `IsExtremeGibbs`, `IsLambdaSpec`, `tvOn` in
`Comparator/Defs_LocalLimit.lean`; both module docstrings contain the dictionary.

## Main statements

* `georgii_7_12_a`: **Georgii, Theorem (7.12)(a).** For an extreme Gibbs measure `μ` of a
  specification `γ` and an increasing cofinal sequence of volumes `(Λ n)`, `γ_{Λ n} f → μ(f)`
  `μ`-almost surely, for every bounded measurable `f`.
* `georgii_7_12_a_measure`: the same in the form `γ_{Λ n}(A | ω) → μ(A)` for every measurable
  event `A`.
* `georgii_7_12_c`: **Georgii, Theorem (7.12)(c).** For a λ-specification `γ = ρ λ` over an
  *arbitrary* measurable state space and `μ ∈ ex 𝓖(γ)`, for `μ`-almost every boundary condition
  `ω` — one single full-measure set of `ω`'s serving all volumes at once — the finite-volume Gibbs
  distributions `γ_{Λ n}(· | ω)` converge to `μ` **in total variation on the events of every finite
  volume `Δ`**.
* `georgii_7_12_c_tendstoLocally`: the consequence Georgii draws from (c), that
  `γ_{Λ n}(· | ω) → μ` in the topology of local convergence for `μ`-almost every `ω`.
* `exists_isLambdaSpec_isExtremeGibbs`: **non-degeneracy.** The hypotheses of `georgii_7_12_c` are
  satisfiable: the independent specification of the preamble is a λ-specification with density
  `ρ ≡ 1`, and its (unique) Gibbs measure `ν^S` is extreme.
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

/-- **Georgii, Theorem (7.12)(a).**  Let `γ` be a specification, let `μ` be an *extreme* Gibbs
measure of `γ`, and let `(Λ n)` be an increasing cofinal sequence of finite volumes.  Then for
every bounded measurable `f : Ω → ℝ` the finite-volume expectations `γ_{Λ n} f` converge to `μ(f)`,
for `μ`-almost every boundary condition. -/
theorem georgii_7_12_a [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {f : Config S E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (nhds (∫ x, f x ∂μ)) :=
  sorry

/-- **Georgii, Theorem (7.12)(a)**, in the form used for the tail-triviality argument: for an
extreme Gibbs measure `μ` and an increasing cofinal sequence of volumes, `γ_{Λ n}(A | ω) → μ(A)`
for `μ`-almost every `ω`, for every measurable event `A`. -/
theorem georgii_7_12_a_measure [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {A : Set (Config S E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ γ (Λ n) ω A) atTop (nhds (μ A)) :=
  sorry

/-- **Georgii, Theorem (7.12)(c).**  Let `ν` be a single-spin distribution on an *arbitrary*
measurable state space `E`, let `γ = ρ λ` be a λ-specification in the sense of Georgii (1.27), let
`μ` be an *extreme* Gibbs measure of `γ`, and let `(Λ n)` be an increasing cofinal sequence of
finite volumes.  Then for `μ`-almost every boundary condition `ω` — one single full-measure set of
`ω`'s serving *all* finite volumes at once — and for every finite volume `Δ`, the finite-volume
Gibbs distribution `γ_{Λ n}(· | ω)` converges to `μ` in total variation on the events of `Δ`:

`sup {|γ_{Λ n}(A | ω) - μ(A)| : A ∈ 𝓕_Δ} → 0`. -/
theorem georgii_7_12_c [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Tendsto (fun n ↦ tvOn Δ (γ (Λ n) ω) μ) atTop (nhds 0) :=
  sorry

/-- **Georgii, Theorem (7.12)(c)**, the conclusion Georgii draws from the total-variation estimate:
for `μ`-almost every boundary condition `ω`, the finite-volume Gibbs distributions
`γ_{Λ n}(· | ω)` converge to `μ` in the topology of local convergence of Georgii (4.2). -/
theorem georgii_7_12_c_tendstoLocally [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, TendstoLocally (fun n ↦ γ (Λ n) ω) atTop μ :=
  sorry

/-- **Non-degeneracy: the hypotheses of `georgii_7_12_c` are not vacuous.**  For a single-spin
distribution `ν` on an arbitrary measurable state space and an arbitrary — in particular infinite —
countable parameter set `S`, the independent specification `indepSpec ν` of the preamble is a
λ-specification with density `ρ ≡ 1`, and its Gibbs measure `ν^S` is extreme. -/
theorem exists_isLambdaSpec_isExtremeGibbs [Countable S] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsLambdaSpec ν (fun _ _ ↦ 1) (indepSpec (S := S) ν) ∧
      IsExtremeGibbs (indepSpec (S := S) ν) (Measure.infinitePi fun _ : S ↦ ν) :=
  sorry

end LocalLimit

end GibbsChallenge

end

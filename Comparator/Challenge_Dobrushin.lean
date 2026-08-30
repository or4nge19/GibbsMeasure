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
* `existsUnique_isGibbs_of_isDobrushin`: **Georgii, Theorem (8.7)** in full. Over a standard Borel
  state space Dobrushin's condition gives *existence as well as* uniqueness: `|𝓖(γ)| = 1`.
* `ofReal_abs_toReal_sub_le_interdepTail`: **Georgii (8.23)**, the Cauchy estimate: for a
  `Λ`-local event `A` and `Δ ⊆ Δ'` the finite-volume Gibbs distributions with a common boundary
  condition satisfy `|γ_Δ(A|ω) − γ_{Δ'}(A|ω)| ≤ ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_ij(γ)`.
* `tendsto_interdepTail`: **Georgii (8.23)**, the error term of that estimate tends to `0` as
  `Δ ↑ S`.  Together the two say that the net `(γ_Δ(·|ω))_Δ` is Cauchy on every local event, which
  is what turns Dobrushin's uniqueness theorem into a *construction* of the Gibbs measure.
* `exists_isGibbs_tendstoLocally_of_isDobrushin`: **Georgii (8.23)** itself — the unique Gibbs
  measure is the local limit of the finite-volume Gibbs distributions, for every boundary
  condition.
* `isDobrushin_indepSpec`: **non-vacuity.** Dobrushin's condition is satisfiable — the independent
  specification of the preamble satisfies it, with `c(γ) = 0`.
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

/-- **Georgii, Theorem (8.7), in full.** Over a standard Borel state space, a specification
satisfying Dobrushin's condition of weak dependence has *exactly one* Gibbs measure: Dobrushin's
condition gives existence as well as uniqueness. -/
theorem existsUnique_isGibbs_of_isDobrushin [Nonempty E] [StandardBorelSpace E]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    ∃! μ : Measure (Config S E), IsGibbs γ μ := by
  sorry

/-- **Georgii (8.23), the Cauchy estimate.** Fix a boundary condition `ω`. For a `Λ`-local event
`A` and finite volumes `Δ ⊆ Δ'`, the finite-volume Gibbs distributions differ by at most the tail
of Dobrushin's series:
`|γ_Δ(A|ω) − γ_{Δ'}(A|ω)| ≤ ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_ij(γ)`. -/
theorem ofReal_abs_toReal_sub_le_interdepTail [DecidableEq S]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) {Λ Δ Δ' : Finset S} (hΔ : Δ ⊆ Δ')
    (ω : Config S E) {A : Set (Config S E)} (hA : MeasurableSet[inside Λ] A) :
    ENNReal.ofReal |(γ Δ ω A).toReal - (γ Δ' ω A).toReal| ≤ ∑ i ∈ Λ, interdepTail γ Δ i := by
  sorry

/-- **Georgii (8.23).** Under Dobrushin's condition the error term of the Cauchy estimate tends to
`0` as the volume `Δ` exhausts `S`; this is the finiteness `∑_j D_ij(γ) < ∞`.  Together with
`ofReal_abs_toReal_sub_le_interdepTail` it says that the net of finite-volume Gibbs distributions
with a fixed boundary condition is Cauchy on every local event. -/
theorem tendsto_interdepTail [DecidableEq S]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) (i : S) :
    Tendsto (fun Δ : Finset S ↦ interdepTail γ Δ i) atTop (nhds 0) := by
  sorry

/-- **Georgii (8.23): Dobrushin's condition *constructs* the Gibbs measure.** Over a standard
Borel state space a specification satisfying Dobrushin's condition has exactly one Gibbs measure
`μ`, and for **every** boundary condition `ω` the net of finite-volume Gibbs distributions
`(γ_Δ(·|ω))_{Δ ∈ 𝓢}` converges to `μ` in the topology of local convergence, Georgii (4.2).  This
is what the Cauchy estimate `ofReal_abs_toReal_sub_le_interdepTail` is for. -/
theorem exists_isGibbs_tendstoLocally_of_isDobrushin [DecidableEq S] [Nonempty E]
    [StandardBorelSpace E] (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    ∃ μ : Measure (Config S E), IsGibbs γ μ ∧
      (∀ ν : Measure (Config S E), IsGibbs γ ν → ν = μ) ∧
      ∀ ω : Config S E, TendstoLocally (fun Δ : Finset S ↦ γ Δ ω) atTop μ := by
  sorry

/-- **Non-vacuity: Dobrushin's condition is satisfiable.** For a single-spin distribution `ν` on a
standard Borel state space, and an arbitrary — in particular infinite — site set `S`, the
independent specification of the preamble is a specification satisfying Dobrushin's condition:
its interdependence matrix vanishes identically, so `c(γ) = 0 < 1`.  Consequently its Gibbs
measures are exactly the single product measure `ν^S`, and the finite-volume Gibbs distributions
converge locally to `ν^S` from every boundary condition. -/
theorem isDobrushin_indepSpec [DecidableEq S] [StandardBorelSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsSpecification (indepSpec (S := S) ν) ∧ IsDobrushin (indepSpec (S := S) ν) ∧
      (∀ i j : S, interdep (indepSpec (S := S) ν) i j = 0) ∧
      (∀ μ : Measure (Config S E),
        IsGibbs (indepSpec (S := S) ν) μ ↔ μ = Measure.infinitePi fun _ : S ↦ ν) ∧
      ∀ ω : Config S E, TendstoLocally (fun Δ : Finset S ↦ indepSpec ν Δ ω) atTop
        (Measure.infinitePi fun _ : S ↦ ν) := by
  sorry

end DobrushinChallenge

end

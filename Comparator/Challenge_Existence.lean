import Comparator.Defs_Existence

/-!
# Existence and compactness of Gibbs measures

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Theorems (4.22) and (4.23).

The a priori measure is an arbitrary finite non-zero `λ ∈ 𝓜(E, ℰ)`, hypothesised as
`[IsFiniteMeasure ν] [NeZero ν]`; by Georgii (2.14) finiteness is exactly `λ`-admissibility of a
potential `Φ ∈ ℬ`, and nothing renormalizes `λ` behind the scenes.

## Main statements

* `isSpecification_gibbsKernel`: Georgii (2.5), (1.32), (2.9), `γ^Φ` is a specification
* `exists_isGibbs_gibbsKernel`: Georgii (4.23)(a) via (4.22), `𝓖(γ^Φ) ≠ ∅`
* `isCompact_setOf_isGibbs_gibbsKernel`: Georgii (4.23)(a), `𝓖(γ^Φ)` is compact
* `exists_isCompact_superset_iUnion_setOf_isGibbs`: Georgii (4.23)(b), `⋃ᵢ 𝒢(Φᵢ)` is relatively
  compact for a bounded family
* `isGibbs_of_tendsto_potentialNormAt_of_tendstoLocally`: Georgii (4.23)(c), the graph of `Φ ↦ 𝒢(Φ)`
  is closed
* `exists_mem_isGibbs_of_tendsto_potentialNormAt`: Georgii (4.23)(d), `Φ ↦ 𝒢(Φ)` is upper
  semicontinuous
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## The theorems -/

/-- **Georgii (2.5), (1.32), (2.9)**: the Gibbsian specification of an absolutely summable
potential is a specification, i.e. a consistent family of proper probability kernels from
`𝓣_Λ`. -/
theorem isSpecification_gibbsKernel [Countable S] (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    IsSpecification (gibbsKernel Φ ν β) :=
  sorry

/-- **Georgii (4.23)(a), via (4.22)**: over a standard Borel state space, the set of Gibbs
measures of the Gibbsian specification of an absolutely summable potential is non-empty. -/
theorem exists_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    ∃ μ : Measure (Config S E), IsGibbs (gibbsKernel Φ ν β) μ :=
  sorry

/-- **Georgii (4.23)(a)**: the set of Gibbs measures of an absolutely summable potential is compact
in the topology of local convergence. -/
theorem isCompact_setOf_isGibbs_gibbsKernel [Countable S] [StandardBorelSpace E]
    (Φ : Finset S → Config S E → ℝ)
    (hΦ : IsAbsolutelySummablePotential Φ) (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν]
    (β : ℝ) :
    @IsCompact (Measure (Config S E)) localTopology {μ | IsGibbs (gibbsKernel Φ ν β) μ} :=
  sorry

/-- **Georgii (4.23)(b)**: if `sup_i ‖Φ_i‖_a < ∞` for every site `a`, then `⋃_i 𝒢(Φ_i)`, taken with
respect to one and the same a priori measure, is relatively compact in the topology of local
convergence. -/
theorem exists_isCompact_superset_iUnion_setOf_isGibbs [Countable S] [StandardBorelSpace E]
    {ι : Type*} (Φs : ι → Finset S → Config S E → ℝ)
    (hΦs : ∀ i, IsAbsolutelySummablePotential (Φs i))
    (hbdd : ∀ a : S, (⨆ i, potentialNormAt (Φs i) a) < ⊤)
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ) :
    ∃ K : Set (Measure (Config S E)), @IsCompact (Measure (Config S E)) localTopology K ∧
      (∀ μ ∈ K, IsProbabilityMeasure μ) ∧
      (⋃ i, {μ : Measure (Config S E) | IsGibbs (gibbsKernel (Φs i) ν β) μ}) ⊆ K :=
  sorry

/-- **Georgii (4.23)(c)**: the graph `{(Φ, μ) : μ ∈ 𝒢(Φ)}` is closed, in net form — if `Φ_x → Φ`
in `ℬ` and `μ_x ∈ 𝒢(Φ_x)` converges locally to a probability measure `μ`, then `μ ∈ 𝒢(Φ)`.  As
Georgii remarks, this does not need the state space to be standard Borel. -/
theorem isGibbs_of_tendsto_potentialNormAt_of_tendstoLocally [Countable S] {ι : Type*}
    {l : Filter ι} [l.NeBot] (Φs : ι → Finset S → Config S E → ℝ)
    (Φ : Finset S → Config S E → ℝ) (hΦs : ∀ x, IsAbsolutelySummablePotential (Φs x))
    (hΦ : IsAbsolutelySummablePotential Φ)
    (hconv : ∀ a : S,
      Tendsto (fun x ↦ potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a) l (nhds 0))
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (μs : ι → Measure (Config S E)) (hμs : ∀ x, IsGibbs (gibbsKernel (Φs x) ν β) (μs x))
    (μ : Measure (Config S E)) (hμ : IsProbabilityMeasure μ)
    (hloc : TendstoLocally μs l μ) :
    IsGibbs (gibbsKernel Φ ν β) μ := by
  sorry

/-- **Georgii (4.23)(d)**: the Gibbs correspondence is upper semicontinuous, i.e.
`𝒢⁻¹(F) = {Φ : 𝒢(Φ) ∩ F ≠ ∅}` is closed for every `F` closed in the topology of local
convergence. -/
theorem exists_mem_isGibbs_of_tendsto_potentialNormAt [Countable S] [StandardBorelSpace E]
    {ι : Type*} {l : Filter ι} [l.NeBot] (Φs : ι → Finset S → Config S E → ℝ)
    (Φ : Finset S → Config S E → ℝ) (hΦs : ∀ x, IsAbsolutelySummablePotential (Φs x))
    (hΦ : IsAbsolutelySummablePotential Φ)
    (hconv : ∀ a : S,
      Tendsto (fun x ↦ potentialNormAt (fun A ω ↦ Φs x A ω - Φ A ω) a) l (nhds 0))
    (ν : Measure E) [IsFiniteMeasure ν] [NeZero ν] (β : ℝ)
    (F : Set (Measure (Config S E))) (hF : @IsClosed (Measure (Config S E)) localTopology F)
    (hmeet : ∀ x, ∃ ρ ∈ F, IsGibbs (gibbsKernel (Φs x) ν β) ρ) :
    ∃ ρ ∈ F, IsGibbs (gibbsKernel Φ ν β) ρ := by
  sorry

end GibbsChallenge

end

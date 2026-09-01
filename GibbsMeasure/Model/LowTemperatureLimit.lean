/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.CriticalTemperature
public import GibbsMeasure.Topology.Metrizable
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Georgii Theorem (6.9), first half: the low-temperature limit

Georgii Remark (4.3)(3) gives a metric for the topology of local convergence when the state
space is finite; with it, the Peierls bound of `GibbsMeasure/Model/PhaseTransition.lean` yields
the first assertion of Theorem (6.9): the set of shift-invariant Gibbs measures of the
two-dimensional Ising ferromagnet approaches each of the two ground states as the temperature
tends to zero,
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ_±) = 0`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Topology

noncomputable section


namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E]

/-! ## M1. Georgii Remark (4.3)(3): a metric for the topology of local convergence -/

/-- Georgii's algebra `𝓕⁰` of local events is nonempty. -/
lemma nonempty_localEvents : (localEvents S E).Nonempty :=
  ⟨∅, mem_localEvents_iff_exists_finsetRestrict_preimage.2
    ⟨∅, ∅, MeasurableSet.empty, (Set.preimage_empty).symm⟩⟩

variable (S E) in
/-- An enumeration `(A_n)_{n ≥ 0}` of Georgii's countable algebra `𝓕⁰` of local events. -/
def localEnum [Countable S] [Finite E] : ℕ → Set (S → E) :=
  ((countable_localEvents (S := S) (E := E)).exists_eq_range nonempty_localEvents).choose

variable (S E) in
lemma localEvents_eq_range_localEnum [Countable S] [Finite E] :
    localEvents S E = Set.range (localEnum S E) :=
  ((countable_localEvents (S := S) (E := E)).exists_eq_range nonempty_localEvents).choose_spec

lemma localEnum_mem [Countable S] [Finite E] (n : ℕ) : localEnum S E n ∈ localEvents S E := by
  rw [localEvents_eq_range_localEnum]; exact Set.mem_range_self n

lemma exists_localEnum_eq [Countable S] [Finite E] {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    ∃ n, localEnum S E n = A := by
  rw [localEvents_eq_range_localEnum] at hA; exact hA

lemma abs_measureReal_sub_le_one (μ ν : ProbabilityMeasure (S → E)) (A : Set (S → E)) :
    |(μ : Measure (S → E)).real A - (ν : Measure (S → E)).real A| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor
  · have h1 : (μ : Measure (S → E)).real A ≤ 1 := measureReal_le_one
    have h2 : (0 : ℝ) ≤ (ν : Measure (S → E)).real A := measureReal_nonneg
    linarith
  · have h1 : (ν : Measure (S → E)).real A ≤ 1 := measureReal_le_one
    have h2 : (0 : ℝ) ≤ (μ : Measure (S → E)).real A := measureReal_nonneg
    linarith

variable [Countable S] [Finite E]

/-- A metric for the topology of local convergence:
`d(μ, ν) = ∑_{n ≥ 1} 2⁻ⁿ |μ(A_n) − ν(A_n)|`, where `(A_n)` enumerates the countable algebra
`𝓕⁰` of local events.  Georgii Remark (4.3)(3) records metrisability for finite `E` with the
different choice `d(μ,ν) = ∑_{n≥1} 2⁻ⁿ ∑_{ζ ∈ E^{Λ(n)}} |μ(σ_{Λ(n)} = ζ) − ν(σ_{Λ(n)} = ζ)|`
along a cofinal sequence `(Λ(n))`; Theorem (6.9) is stated for any metric of the 𝓛-topology. -/
def localDist (μ ν : ProbabilityMeasure (S → E)) : ℝ :=
  ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) *
    |(μ : Measure (S → E)).real (localEnum S E n) - (ν : Measure (S → E)).real (localEnum S E n)|

lemma summable_geom_half : Summable (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ (n + 1)) := by
  have h : Summable (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [pow_succ] using h.mul_right ((2 : ℝ)⁻¹)

lemma localDist_summand_nonneg (μ ν : ProbabilityMeasure (S → E)) (n : ℕ) :
    0 ≤ (2 : ℝ)⁻¹ ^ (n + 1) *
      |(μ : Measure (S → E)).real (localEnum S E n) -
        (ν : Measure (S → E)).real (localEnum S E n)| := by positivity

lemma localDist_summand_le (μ ν : ProbabilityMeasure (S → E)) (n : ℕ) :
    (2 : ℝ)⁻¹ ^ (n + 1) *
      |(μ : Measure (S → E)).real (localEnum S E n) -
        (ν : Measure (S → E)).real (localEnum S E n)| ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  nth_rewrite 2 [← mul_one ((2 : ℝ)⁻¹ ^ (n + 1))]
  exact mul_le_mul_of_nonneg_left (abs_measureReal_sub_le_one μ ν _) (by positivity)

lemma summable_localDist (μ ν : ProbabilityMeasure (S → E)) :
    Summable (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ (n + 1) *
      |(μ : Measure (S → E)).real (localEnum S E n) -
        (ν : Measure (S → E)).real (localEnum S E n)|) :=
  Summable.of_nonneg_of_le (localDist_summand_nonneg μ ν) (localDist_summand_le μ ν)
    summable_geom_half

lemma localDist_nonneg (μ ν : ProbabilityMeasure (S → E)) : 0 ≤ localDist μ ν :=
  tsum_nonneg (localDist_summand_nonneg μ ν)

lemma localDist_self (μ : ProbabilityMeasure (S → E)) : localDist μ μ = 0 := by
  simp [localDist]

lemma localDist_comm (μ ν : ProbabilityMeasure (S → E)) : localDist μ ν = localDist ν μ := by
  simp only [localDist]
  exact tsum_congr fun n ↦ by rw [abs_sub_comm]

lemma localDist_triangle (μ ν ρ : ProbabilityMeasure (S → E)) :
    localDist μ ρ ≤ localDist μ ν + localDist ν ρ := by
  rw [localDist, localDist, localDist, ← (summable_localDist μ ν).tsum_add (summable_localDist ν ρ)]
  refine (summable_localDist μ ρ).tsum_le_tsum (fun n ↦ ?_)
    ((summable_localDist μ ν).add (summable_localDist ν ρ))
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_sub_le _ _ _

/-- Each term of the series is controlled by the distance. -/
lemma abs_measureReal_sub_le_localDist (μ ν : ProbabilityMeasure (S → E)) (n : ℕ) :
    |(μ : Measure (S → E)).real (localEnum S E n) -
        (ν : Measure (S → E)).real (localEnum S E n)| ≤ 2 ^ (n + 1) * localDist μ ν := by
  have h := (summable_localDist μ ν).le_tsum n (fun j _ ↦ localDist_summand_nonneg μ ν j)
  have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  calc |(μ : Measure (S → E)).real (localEnum S E n) -
        (ν : Measure (S → E)).real (localEnum S E n)|
      = 2 ^ (n + 1) * ((2 : ℝ)⁻¹ ^ (n + 1) *
        |(μ : Measure (S → E)).real (localEnum S E n) -
          (ν : Measure (S → E)).real (localEnum S E n)|) := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
    _ ≤ 2 ^ (n + 1) * localDist μ ν := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt h2)

end MeasureTheory

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E] [Countable S] [Finite E]

omit [Countable S] [Finite E] in
/-- For probability measures, `ℝ≥0∞`-valued and `ℝ`-valued convergence on a set agree. -/
lemma tendsto_measure_iff_tendsto_measureReal {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} (A : Set (S → E)) :
    Tendsto (fun i ↦ ((μs i : Measure (S → E))) A) l (𝓝 ((μ : Measure (S → E)) A)) ↔
      Tendsto (fun i ↦ ((μs i : Measure (S → E))).real A) l
        (𝓝 ((μ : Measure (S → E)).real A)) := by
  have key : ∀ m : ProbabilityMeasure (S → E),
      ENNReal.ofReal ((m : Measure (S → E)).real A) = (m : Measure (S → E)) A := by
    intro m
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  constructor
  · intro h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  · intro h
    have h2 := ENNReal.tendsto_ofReal h
    simpa only [key] using h2

omit [Countable S] [Finite E] in
/-- **Georgii (4.2)/(4.3)(3).** Local convergence, tested by the real-valued evaluations. -/
lemma tendsto_withLocalConvergence_iff_real {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    Tendsto (fun i ↦ (WithSetwiseTopology.ofMeasure (μs i) : WithLocalConvergence S E)) l
        (𝓝 (WithSetwiseTopology.ofMeasure μ)) ↔
      ∀ A ∈ localEvents S E, Tendsto (fun i ↦ ((μs i : Measure (S → E))).real A) l
        (𝓝 ((μ : Measure (S → E)).real A)) := by
  rw [tendsto_withLocalConvergence_iff]
  exact forall₂_congr fun A _ ↦ tendsto_measure_iff_tendsto_measureReal A

/-- **Georgii Remark (4.3)(3): `localDist` induces the topology of local convergence.**
A net of random fields converges locally iff its `localDist`-distance to the limit tends to `0`. -/
theorem tendsto_withLocalConvergence_iff_tendsto_localDist {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {μ : ProbabilityMeasure (S → E)} :
    Tendsto (fun i ↦ (WithSetwiseTopology.ofMeasure (μs i) : WithLocalConvergence S E)) l
        (𝓝 (WithSetwiseTopology.ofMeasure μ)) ↔
      Tendsto (fun i ↦ localDist (μs i) μ) l (𝓝 0) := by
  rw [tendsto_withLocalConvergence_iff_real]
  constructor
  · intro h
    have hterm : ∀ n : ℕ, Tendsto (fun i ↦ (2 : ℝ)⁻¹ ^ (n + 1) *
        |((μs i : Measure (S → E))).real (localEnum S E n) -
          ((μ : Measure (S → E))).real (localEnum S E n)|) l (𝓝 0) := by
      intro n
      have h1 := h _ (localEnum_mem n)
      have h2 : Tendsto (fun i ↦ |((μs i : Measure (S → E))).real (localEnum S E n) -
          ((μ : Measure (S → E))).real (localEnum S E n)|) l (𝓝 0) := by
        simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.1 h1
      simpa using h2.const_mul ((2 : ℝ)⁻¹ ^ (n + 1))
    have hbd : ∀ᶠ i in l, ∀ n : ℕ, ‖(2 : ℝ)⁻¹ ^ (n + 1) *
        |((μs i : Measure (S → E))).real (localEnum S E n) -
          ((μ : Measure (S → E))).real (localEnum S E n)|‖ ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
      refine Eventually.of_forall fun i n ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (localDist_summand_nonneg _ _ _)]
      exact localDist_summand_le _ _ _
    have := tendsto_tsum_of_dominated_convergence summable_geom_half hterm hbd
    simpa [localDist] using this
  · intro h A hA
    obtain ⟨n, rfl⟩ := exists_localEnum_eq hA
    rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq]
    refine squeeze_zero (fun i ↦ abs_nonneg _)
      (fun i ↦ abs_measureReal_sub_le_localDist (μs i) μ n) ?_
    simpa using h.const_mul ((2 : ℝ) ^ (n + 1))

/-- **Georgii Remark (4.3)(3): `localDist` is a metric.** -/
theorem localDist_eq_zero_iff {μ ν : ProbabilityMeasure (S → E)} :
    localDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ localDist_self μ⟩
  have hzero : ∀ n : ℕ, ((μ : Measure (S → E))).real (localEnum S E n)
      = ((ν : Measure (S → E))).real (localEnum S E n) := by
    intro n
    have h1 := abs_measureReal_sub_le_localDist μ ν n
    rw [h, mul_zero] at h1
    have := abs_nonneg (((μ : Measure (S → E))).real (localEnum S E n) -
      ((ν : Measure (S → E))).real (localEnum S E n))
    have h2 : |((μ : Measure (S → E))).real (localEnum S E n) -
        ((ν : Measure (S → E))).real (localEnum S E n)| = 0 := le_antisymm h1 this
    have := abs_eq_zero.1 h2
    linarith
  have hset : ∀ A ∈ localEvents S E, (μ : Measure (S → E)) A = (ν : Measure (S → E)) A := by
    intro A hA
    obtain ⟨n, rfl⟩ := exists_localEnum_eq hA
    have := hzero n
    rw [measureReal_def, measureReal_def] at this
    rw [← ENNReal.ofReal_toReal (measure_ne_top (μ : Measure (S → E)) (localEnum S E n)),
      ← ENNReal.ofReal_toReal (measure_ne_top (ν : Measure (S → E)) (localEnum S E n)), this]
  exact ProbabilityMeasure.toMeasure_injective
    (separatesOn_localEvents μ.2 ν.2 hset)

end MeasureTheory

namespace MeasureTheory

variable {S E : Type*} [MeasurableSpace E] [Countable S] [Finite E]

/-! ### Georgii's distance `d(F, μ)` from a set of random fields to a random field -/

/-- **Georgii's `d(𝒢, μ)`**: the `localDist`-distance from a set `F` of random fields to a
random field `μ`.

The infimum is over the subtype `↥F`, not `⨅ ν ∈ F`: in `ℝ` the latter is
`⨅ ν, ⨅ (_ : ν ∈ F), …`, whose term at any `ν ∉ F` is `sInf ∅ = 0`, so it would collapse to `0`
whenever some probability measure lies outside `F`. `le_localDistSet` pins the definition down from
below and fails for that reading. -/
def localDistSet (F : Set (ProbabilityMeasure (S → E))) (μ : ProbabilityMeasure (S → E)) : ℝ :=
  ⨅ ν : F, localDist (ν : ProbabilityMeasure (S → E)) μ

lemma localDistSet_nonneg (F : Set (ProbabilityMeasure (S → E)))
    (μ : ProbabilityMeasure (S → E)) : 0 ≤ localDistSet F μ :=
  Real.iInf_nonneg fun ν ↦ localDist_nonneg _ μ

lemma localDistSet_le {F : Set (ProbabilityMeasure (S → E))} {μ ν : ProbabilityMeasure (S → E)}
    (hν : ν ∈ F) : localDistSet F μ ≤ localDist ν μ :=
  ciInf_le ⟨0, by rintro x ⟨ν', rfl⟩; exact localDist_nonneg _ μ⟩ (⟨ν, hν⟩ : F)

/-- A lower bound for `d(F, μ)`, which is what makes the definition informative: it fails for the
`⨅ ν ∈ F` reading. -/
lemma le_localDistSet {F : Set (ProbabilityMeasure (S → E))} {μ : ProbabilityMeasure (S → E)}
    {c : ℝ} (hF : F.Nonempty) (h : ∀ ν ∈ F, c ≤ localDist ν μ) : c ≤ localDistSet F μ := by
  have : Nonempty F := hF.to_subtype
  exact le_ciInf fun ν ↦ h ν ν.2

end MeasureTheory

namespace MeasureTheory

/-! ### `localDist` as a genuine `MetricSpace` on `WithLocalConvergence S E` -/

variable {S E : Type*} [MeasurableSpace E] [Countable S] [Finite E]

/-- The characterisation of local convergence by `localDist`, on `WithLocalConvergence S E`. -/
theorem tendsto_withLocalConvergence_iff_localDist {ι : Type*} {l : Filter ι}
    {νs : ι → WithLocalConvergence S E} {ν : WithLocalConvergence S E} :
    Tendsto νs l (𝓝 ν) ↔
      Tendsto (fun i ↦ localDist (νs i).toMeasure ν.toMeasure) l (𝓝 0) :=
  tendsto_withLocalConvergence_iff_tendsto_localDist
    (μs := fun i ↦ (νs i).toMeasure) (μ := ν.toMeasure)

/-- `localDist` as a pseudometric structure (with its own, a priori different, topology). -/
@[instance_reducible] def localPseudoMetricAux : PseudoMetricSpace (WithLocalConvergence S E) where
  dist μ ν := localDist μ.toMeasure ν.toMeasure
  dist_self _ := localDist_self _
  dist_comm _ _ := localDist_comm _ _
  dist_triangle _ _ _ := localDist_triangle _ _ _

lemma tendsto_localPseudoMetricAux_iff {ι : Type*} (l : Filter ι)
    (f : ι → WithLocalConvergence S E) (x : WithLocalConvergence S E) :
    @Tendsto _ _ f l
        (@nhds _ (localPseudoMetricAux (S := S) (E := E)).toUniformSpace.toTopologicalSpace x) ↔
      Tendsto (fun i ↦ localDist (f i).toMeasure x.toMeasure) l (𝓝 0) :=
  @tendsto_iff_dist_tendsto_zero _ _ localPseudoMetricAux f l x

/-- **Georgii Remark (4.3)(3).** The topology induced by `localDist` *is* the topology of local
convergence. -/
theorem localPseudoMetricAux_toTopologicalSpace :
    (localPseudoMetricAux (S := S) (E := E)).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (WithLocalConvergence S E)) := by
  refine TopologicalSpace.ext_nhds fun x ↦ le_antisymm ?_ ?_
  · exact tendsto_withLocalConvergence_iff_localDist.2
      ((tendsto_localPseudoMetricAux_iff _ id x).1 tendsto_id)
  · exact (tendsto_localPseudoMetricAux_iff _ id x).2
      (tendsto_withLocalConvergence_iff_localDist.1 tendsto_id)

/-- **Georgii Remark (4.3)(3).** `localDist` is a metric for the topology of local convergence:
the space of random fields over a countable site set and a finite state space is a metric space,
with `d(μ, ν) = ∑_{n ≥ 1} 2⁻ⁿ |μ(A_n) − ν(A_n)|`. -/
@[instance_reducible] def localMetricSpace : MetricSpace (WithLocalConvergence S E) :=
  { localPseudoMetricAux.replaceTopology localPseudoMetricAux_toTopologicalSpace.symm with
    eq_of_dist_eq_zero := fun h ↦
      WithSetwiseTopology.toMeasure_injective (localDist_eq_zero_iff.1 h) }

lemma dist_localMetricSpace (μ ν : WithLocalConvergence S E) :
    @dist _ (localMetricSpace (S := S) (E := E)).toDist μ ν = localDist μ.toMeasure ν.toMeasure :=
  rfl

end MeasureTheory

namespace MeasureTheory

/-! ## M3. Georgii (6.9): the quantitative estimate `|μ⁺(f) − δ₊(f)| ≤ 2‖f‖ |Λ| r(β)` -/

variable {S E : Type*} [MeasurableSpace E]

lemma measurableSet_ne_apply [MeasurableSingletonClass E] (ω : S → E) (a : S) :
    MeasurableSet {ζ : S → E | ζ a ≠ ω a} := by
  have h : {ζ : S → E | ζ a ≠ ω a} = (fun ζ : S → E ↦ ζ a) ⁻¹' {ω a}ᶜ := by
    ext ζ; simp
  rw [h]
  exact (measurable_pi_apply a) (measurableSet_singleton (ω a)).compl

/-- The Dirac measure at `ω`, as a random field. -/
def diracProb (ω : S → E) : ProbabilityMeasure (S → E) := ⟨Measure.dirac ω, inferInstance⟩

@[simp] lemma diracProb_toMeasure (ω : S → E) :
    (diracProb ω : Measure (S → E)) = Measure.dirac ω := rfl

/-- **Georgii (6.9), the key estimate.** If `μ` puts mass at most `c` on `{σ_a ≠ ω_a}` for every
site `a` of a finite volume `Λ`, then `μ` and `δ_ω` differ by at most `|Λ| c` on every event
determined by the coordinates in `Λ`. This is Georgii's
`|μ⁺(f) − δ₊(f)| ≤ 2‖f‖ μ⁺(σ_Λ ≠ ω⁺_Λ) ≤ 2‖f‖ |Λ| r(β)` for `f = 1_A`. -/
theorem abs_measureReal_sub_dirac_le {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {ω : S → E} {c : ℝ} {Λ : Finset S} {A : Set (S → E)} (hA : MeasurableSet A)
    (hdep : ∀ ζ ζ' : S → E, (∀ a ∈ Λ, ζ a = ζ' a) → (ζ ∈ A ↔ ζ' ∈ A))
    (hc : ∀ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} ≤ c) :
    |μ.real A - (Measure.dirac ω).real A| ≤ Λ.card * c := by
  classical
  set G : Set (S → E) := {ζ : S → E | ∀ a ∈ Λ, ζ a = ω a} with hGdef
  have hGc : Gᶜ = ⋃ a ∈ Λ, {ζ : S → E | ζ a ≠ ω a} := by
    ext ζ
    simp [hGdef]
  have hGcle : μ.real Gᶜ ≤ Λ.card * c := by
    rw [hGc]
    calc μ.real (⋃ a ∈ Λ, {ζ : S → E | ζ a ≠ ω a})
        ≤ ∑ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} := measureReal_biUnion_finset_le _ _
      _ ≤ Λ.card • c := Finset.sum_le_card_nsmul _ _ _ hc
      _ = Λ.card * c := by rw [nsmul_eq_mul]
  by_cases hω : ω ∈ A
  · have hGA : G ⊆ A := fun ζ hζ ↦ (hdep ζ ω hζ).2 hω
    have hdirac : (Measure.dirac ω).real A = 1 := by
      simp [measureReal_def, Measure.dirac_apply' ω hA, hω]
    have hcompl : μ.real Aᶜ ≤ μ.real Gᶜ := measureReal_mono (compl_subset_compl.2 hGA)
    have hsum : μ.real A + μ.real Aᶜ = 1 := by
      rw [measureReal_add_measureReal_compl hA]
      simp [measureReal_def]
    rw [hdirac, abs_of_nonpos (by linarith [measureReal_le_one (μ := μ) (s := A)])]
    linarith
  · have hAG : A ⊆ Gᶜ := by
      intro ζ hζ
      simp only [Set.mem_compl_iff]
      intro hζG
      exact hω ((hdep ζ ω hζG).1 hζ)
    have hdirac : (Measure.dirac ω).real A = 0 := by
      simp [measureReal_def, Measure.dirac_apply' ω hA, hω]
    have hle : μ.real A ≤ μ.real Gᶜ := measureReal_mono hAG
    rw [hdirac, sub_zero, abs_of_nonneg measureReal_nonneg]
    linarith

/-- Georgii (6.9): every local event `A ∈ 𝓕⁰` has a finite volume `|Λ|` which controls the
difference between a random field and a Dirac measure, uniformly in the per-site bound `c`. -/
theorem exists_const_abs_measureReal_sub_dirac_le [Countable S] [Finite E] {ω : S → E}
    {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (μ : Measure (S → E)) (_ : IsProbabilityMeasure μ) (c : ℝ),
      (∀ a : S, μ.real {ζ : S → E | ζ a ≠ ω a} ≤ c) →
        |μ.real A - (Measure.dirac ω).real A| ≤ κ * c := by
  obtain ⟨Λ, B, hB, rfl⟩ := mem_localEvents_iff_exists_finsetRestrict_preimage.1 hA
  refine ⟨Λ.card, Nat.cast_nonneg _, fun μ hμ c hc ↦ ?_⟩
  refine abs_measureReal_sub_dirac_le ((Finset.measurable_restrict Λ) hB) (fun ζ ζ' hζ ↦ ?_)
    (fun a _ ↦ hc a)
  have : Λ.restrict ζ = Λ.restrict ζ' := funext fun i ↦ hζ i.1 i.2
  simp only [Set.mem_preimage, this]

end MeasureTheory

namespace MeasureTheory

/-! ### Georgii (6.9): `μ(σ_Λ ≠ ω_Λ) ≤ |Λ| c`, and the estimate for local functions -/

variable {S E : Type*} [MeasurableSpace E]

omit [MeasurableSpace E] in
lemma setOf_exists_ne_eq_iUnion (ω : S → E) (Λ : Finset S) :
    {ζ : S → E | ∃ a ∈ Λ, ζ a ≠ ω a} = ⋃ a ∈ Λ, {ζ : S → E | ζ a ≠ ω a} := by
  ext ζ; simp

/-- **Georgii (6.9)**: `μ(σ_Λ ≠ ω_Λ) ≤ ∑_{a ∈ Λ} μ(σ_a ≠ ω_a) ≤ |Λ| c`. -/
theorem measure_exists_ne_le {μ : Measure (S → E)} {ω : S → E} {c : ℝ≥0∞} (Λ : Finset S)
    (hc : ∀ a ∈ Λ, μ {ζ : S → E | ζ a ≠ ω a} ≤ c) :
    μ {ζ : S → E | ∃ a ∈ Λ, ζ a ≠ ω a} ≤ Λ.card * c := by
  rw [setOf_exists_ne_eq_iUnion]
  calc μ (⋃ a ∈ Λ, {ζ : S → E | ζ a ≠ ω a}) ≤ ∑ a ∈ Λ, μ {ζ : S → E | ζ a ≠ ω a} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ Λ, c := Finset.sum_le_sum hc
    _ = Λ.card * c := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Georgii (6.9)**, real-valued form of `μ(σ_Λ ≠ ω_Λ) ≤ |Λ| c`. -/
theorem measureReal_exists_ne_le {μ : Measure (S → E)} {ω : S → E} {c : ℝ} (Λ : Finset S)
    (hc : ∀ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} ≤ c) :
    μ.real {ζ : S → E | ∃ a ∈ Λ, ζ a ≠ ω a} ≤ Λ.card * c := by
  rw [setOf_exists_ne_eq_iUnion]
  calc μ.real (⋃ a ∈ Λ, {ζ : S → E | ζ a ≠ ω a})
      ≤ ∑ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} := measureReal_biUnion_finset_le _ _
    _ ≤ Λ.card • c := Finset.sum_le_card_nsmul _ _ _ hc
    _ = Λ.card * c := by rw [nsmul_eq_mul]

/-- The event form of Georgii's estimate, for events in the finite-volume σ-algebra `𝓕_Λ`. -/
theorem abs_measureReal_sub_dirac_le_of_cylinderEvents {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] {ω : S → E} {c : ℝ} {Λ : Finset S} {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A)
    (hc : ∀ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} ≤ c) :
    |μ.real A - (Measure.dirac ω).real A| ≤ Λ.card * c := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  refine abs_measureReal_sub_dirac_le ((Finset.measurable_restrict Λ) hB) (fun ζ ζ' hζ ↦ ?_) hc
  have h : Λ.restrict ζ = Λ.restrict ζ' := funext fun i ↦ hζ i.1 i.2
  simp only [Set.mem_preimage, h]

/-- **Georgii (6.9), the estimate in the book's form.** For a local function `f ∈ 𝓛_Λ` with
`‖f‖ ≤ M`,
`|μ(f) − δ_ω(f)| ≤ μ(|f − f(ω)|) ≤ 2‖f‖ μ(σ_Λ ≠ ω_Λ) ≤ 2‖f‖ |Λ| c`. -/
theorem abs_integral_sub_apply_le [MeasurableSingletonClass E] {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] {ω : S → E} {c M : ℝ} {Λ : Finset S} {f : (S → E) → ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] f)
    (hM : ∀ ζ, |f ζ| ≤ M) (hc : ∀ a ∈ Λ, μ.real {ζ : S → E | ζ a ≠ ω a} ≤ c) :
    |(∫ ζ, f ζ ∂μ) - f ω| ≤ 2 * M * (Λ.card * c) := by
  classical
  set A : Set (S → E) := {ζ : S → E | ∃ a ∈ Λ, ζ a ≠ ω a} with hAdef
  have hAmeas : MeasurableSet A := by
    rw [hAdef, setOf_exists_ne_eq_iUnion]
    exact Λ.measurableSet_biUnion fun a _ ↦ measurableSet_ne_apply ω a
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ω)
  have hfmeas : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn f (Λ : Set S) := hf.dependsOn_of_cylinderEvents
  have hint : Integrable f μ :=
    Integrable.mono' (integrable_const M) hfmeas.aestronglyMeasurable
      (Eventually.of_forall fun ζ ↦ by simpa using hM ζ)
  have hbound : ∀ ζ, |f ζ - f ω| ≤ (2 * M) * A.indicator (fun _ ↦ (1 : ℝ)) ζ := by
    intro ζ
    by_cases hζ : ζ ∈ A
    · rw [Set.indicator_of_mem hζ, mul_one]
      calc |f ζ - f ω| ≤ |f ζ| + |f ω| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM ζ) (hM ω)
        _ = 2 * M := by ring
    · have hagree : ∀ a ∈ (Λ : Set S), ζ a = ω a := by
        intro a ha
        by_contra hne
        exact hζ ⟨a, by simpa using ha, hne⟩
      rw [hdep hagree, sub_self, abs_zero, Set.indicator_of_notMem hζ, mul_zero]
  have hintabs : Integrable (fun ζ ↦ |f ζ - f ω|) μ :=
    (hint.sub (integrable_const _)).abs
  have hintind : Integrable (fun ζ ↦ (2 * M) * A.indicator (fun _ ↦ (1 : ℝ)) ζ) μ :=
    ((integrable_const (1 : ℝ)).indicator hAmeas).const_mul _
  calc |(∫ ζ, f ζ ∂μ) - f ω|
      = |∫ ζ, (f ζ - f ω) ∂μ| := by
        rw [integral_sub hint (integrable_const _), integral_const]
        simp
    _ ≤ ∫ ζ, |f ζ - f ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ζ, (2 * M) * A.indicator (fun _ ↦ (1 : ℝ)) ζ ∂μ :=
        integral_mono hintabs hintind hbound
    _ = (2 * M) * μ.real A := by
        rw [integral_const_mul, integral_indicator_const (1 : ℝ) hAmeas, smul_eq_mul, mul_one]
    _ ≤ 2 * M * (Λ.card * c) := by
        exact mul_le_mul_of_nonneg_left (measureReal_exists_ne_le Λ hc) (by linarith)

end MeasureTheory

namespace MeasureTheory

/-! ## M4 (abstract form). Local convergence to a Dirac measure from a per-site bound -/

variable {S E : Type*} [MeasurableSpace E] [Countable S] [Finite E]

/-- **Georgii (6.9), the passage to the limit.** If `μ_i(σ_a ≠ ω_a) ≤ c_i` for all sites `a` and
`c_i → 0`, then `μ_i → δ_ω` in the topology of local convergence, i.e.
`localDist (μ_i) δ_ω → 0`. -/
theorem tendsto_localDist_diracProb {ι : Type*} {l : Filter ι}
    {μs : ι → ProbabilityMeasure (S → E)} {ω : S → E} {c : ι → ℝ}
    (hc : Tendsto c l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ a : S,
      ((μs i : Measure (S → E))).real {ζ : S → E | ζ a ≠ ω a} ≤ c i) :
    Tendsto (fun i ↦ localDist (μs i) (diracProb ω)) l (𝓝 0) := by
  rw [← tendsto_withLocalConvergence_iff_tendsto_localDist, tendsto_withLocalConvergence_iff_real]
  intro A hA
  obtain ⟨κ, hκ0, hκ⟩ := exists_const_abs_measureReal_sub_dirac_le (ω := ω) hA
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq, diracProb_toMeasure]
  refine squeeze_zero' (g := fun i ↦ κ * c i) (Eventually.of_forall fun i ↦ abs_nonneg _) ?_ ?_
  · filter_upwards [hbound] with i hi
    exact hκ _ (μs i).2 (c i) hi
  · simpa using hc.const_mul κ

/-- **Georgii (6.9), `d(F, δ_ω) → 0`.** If a set `F i` of random fields contains, for each `i`, a
field `μ i` with the per-site bound `c i → 0`, then Georgii's distance `d(F i, δ_ω)` tends to
`0`. -/
theorem tendsto_localDistSet_diracProb {ι : Type*} {l : Filter ι}
    {F : ι → Set (ProbabilityMeasure (S → E))} {μs : ι → ProbabilityMeasure (S → E)}
    {ω : S → E} {c : ι → ℝ} (hmem : ∀ i, μs i ∈ F i)
    (hc : Tendsto c l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ a : S,
      ((μs i : Measure (S → E))).real {ζ : S → E | ζ a ≠ ω a} ≤ c i) :
    Tendsto (fun i ↦ localDistSet (F i) (diracProb ω)) l (𝓝 0) :=
  squeeze_zero (fun _ ↦ localDistSet_nonneg _ _) (fun i ↦ localDistSet_le (hmem i))
    (tendsto_localDist_diracProb hc hbound)

end MeasureTheory

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M2. Georgii (6.9): `r(β) → 0` as `β → ∞` -/

lemma tendsto_ofReal_exp_atTop :
    Tendsto (fun b : ℝ ↦ ENNReal.ofReal (Real.exp (-2 * b))) atTop (𝓝 0) := by
  have h2 : Tendsto (fun b : ℝ ↦ 2 * b) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_id
  have hlin : Tendsto (fun b : ℝ ↦ -2 * b) atTop atBot := by
    simpa [Function.comp_def, neg_mul] using tendsto_neg_atTop_atBot.comp h2
  simpa [Function.comp_def] using
    ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hlin)

/-- **Georgii (6.9).** The Peierls series `r(β) = ∑_{ℓ ≥ 1} ℓ (3 e^{-2β})^ℓ` (here in the
repository's form `∑_{ℓ ≥ 1} ℓ · 4096^ℓ e^{-2βℓ}`) tends to `0` as `β → ∞`. -/
theorem tendsto_r_atTop : Tendsto r atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hub : Tendsto (fun b : ℝ ↦ (16384 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)))
      atTop (𝓝 0) := by
    simpa using
      ENNReal.Tendsto.const_mul (a := (16384 : ℝ≥0∞)) tendsto_ofReal_exp_atTop (Or.inr (by simp))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Eventually.of_forall fun _ ↦ (zero_le : (0:ℝ≥0∞) ≤ _)) ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb
  have hx := ofReal_exp_le hb
  have h8 : (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 2⁻¹ := by
    calc (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 8192 * 65536⁻¹ := by gcongr
      _ = 8⁻¹ := by
          rw [show (65536 : ℝ≥0∞) = 8192 * 8 by norm_num,
            ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (by norm_num)
  calc r b ≤ 2 * (8192 * ENNReal.ofReal (Real.exp (-2 * b))) := r_le_of_ofReal_exp_le h8
    _ = 16384 * ENNReal.ofReal (Real.exp (-2 * b)) := by rw [← mul_assoc]; norm_num

/-- **Georgii (6.9).** The real-valued Peierls bound tends to `0`. -/
theorem tendsto_toReal_r_atTop : Tendsto (fun b : ℝ ↦ (r b).toReal) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp tendsto_r_atTop

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M6. Georgii's phases `μ_+^β` and `μ_-^β = τ(μ_+^β)` -/

lemma r_ne_top {b : ℝ} (hb : 8 * Real.log 2 ≤ b) : r b ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (r_le_quarter hb)

/-- **Georgii (6.9)**, `μ_+^β`: the shift-invariant Gibbs measure obtained as a cluster point of
the cube averages with the `+1` boundary condition. -/
def plusPhase (b : ℝ) : ProbabilityMeasure (Site → Bool) := (exists_plus_phase b).choose

lemma plusPhase_mem_GP (b : ℝ) :
    plusPhase b ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) :=
  (exists_plus_phase b).choose_spec.1

lemma plusPhase_measurePreserving_shift (b : ℝ) (j : Site) :
    MeasurePreserving (shift Bool j).toFun (plusPhase b : Measure (Site → Bool))
      (plusPhase b : Measure (Site → Bool)) :=
  (exists_plus_phase b).choose_spec.2.1 j

lemma plusPhase_eq_false_le (b : ℝ) (a : Site) :
    (plusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ r b :=
  (exists_plus_phase b).choose_spec.2.2 a

/-- **Georgii (6.9)**: `μ_+^β(σ_a ≠ +1) ≤ r(β)`. -/
lemma plusPhase_real_ne_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (a : Site) :
    (plusPhase b : Measure (Site → Bool)).real
        {z : Site → Bool | z a ≠ (fun _ : Site ↦ true) a} ≤ (r b).toReal := by
  have hset : {z : Site → Bool | z a ≠ (fun _ : Site ↦ true) a}
      = {z : Site → Bool | z a = false} := by
    ext z; simp
  rw [hset, measureReal_def]
  exact ENNReal.toReal_mono (r_ne_top hb) (plusPhase_eq_false_le b a)

/-- **Georgii (6.9)**, `μ_-^β = τ(μ_+^β)`: the spin-flip image of the plus phase. -/
def minusPhase (b : ℝ) : ProbabilityMeasure (Site → Bool) :=
  (plusPhase b).map spinFlip.measurable_toFun.aemeasurable

lemma minusPhase_toMeasure (b : ℝ) :
    (minusPhase b : Measure (Site → Bool))
      = Measure.map spinFlip.toFun (plusPhase b : Measure (Site → Bool)) :=
  ProbabilityMeasure.toMeasure_map _ _

lemma minusPhase_mem_GP (b : ℝ) :
    minusPhase b ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) :=
  (isInvariant_spinFlip b).map_mem_GP (plusPhase_mem_GP b)

lemma minusPhase_measurePreserving_shift (b : ℝ) (j : Site) :
    MeasurePreserving (shift Bool j).toFun (minusPhase b : Measure (Site → Bool))
      (minusPhase b : Measure (Site → Bool)) := by
  refine ⟨(shift Bool j).measurable_toFun, ?_⟩
  rw [minusPhase_toMeasure,
    Measure.map_map (shift Bool j).measurable_toFun spinFlip.measurable_toFun,
    show (shift Bool j).toFun ∘ spinFlip.toFun = spinFlip.toFun ∘ (shift Bool j).toFun from
      funext fun z ↦ funext fun i ↦ by simp,
    ← Measure.map_map spinFlip.measurable_toFun (shift Bool j).measurable_toFun,
    (plusPhase_measurePreserving_shift b j).map_eq]

/-- **Georgii (6.9)**: `μ_-^β(σ_a ≠ -1) ≤ r(β)`. -/
lemma minusPhase_real_ne_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (a : Site) :
    (minusPhase b : Measure (Site → Bool)).real
        {z : Site → Bool | z a ≠ (fun _ : Site ↦ false) a} ≤ (r b).toReal := by
  have hset : {z : Site → Bool | z a ≠ (fun _ : Site ↦ false) a}
      = {z : Site → Bool | z a = true} := by
    ext z; simp
  have hmeas : MeasurableSet {z : Site → Bool | z a = true} := by
    have h : {z : Site → Bool | z a = true} = (fun z : Site → Bool ↦ z a) ⁻¹' {true} := rfl
    rw [h]
    exact (measurable_pi_apply a) (measurableSet_singleton true)
  have hval : (minusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = true}
      = (plusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = false} := by
    rw [minusPhase_toMeasure, Measure.map_apply spinFlip.measurable_toFun hmeas]
    congr 1
    ext z
    simp
  rw [hset, measureReal_def, hval]
  exact ENNReal.toReal_mono (r_ne_top hb) (plusPhase_eq_false_le b a)

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ### Georgii (6.9), the estimate for the plus phase, in the book's form -/

/-- **Georgii (6.9)**: `μ_+^β(σ_Λ ≠ ω⁺_Λ) ≤ ∑_{a ∈ Λ} μ_+^β(σ_a = -1) ≤ |Λ| r(β)`. -/
theorem plusPhase_exists_eq_false_le (b : ℝ) (Λ : Finset Site) :
    (plusPhase b : Measure (Site → Bool)) {ζ : Site → Bool | ∃ a ∈ Λ, ζ a = false}
      ≤ Λ.card * r b := by
  have hEq : {ζ : Site → Bool | ∃ a ∈ Λ, ζ a = false}
      = {ζ : Site → Bool | ∃ a ∈ Λ, ζ a ≠ (fun _ : Site ↦ true) a} := by
    ext ζ; simp
  rw [hEq]
  refine measure_exists_ne_le Λ fun a _ ↦ ?_
  have hset : {ζ : Site → Bool | ζ a ≠ (fun _ : Site ↦ true) a}
      = {ζ : Site → Bool | ζ a = false} := by
    ext ζ; simp
  rw [hset]
  exact plusPhase_eq_false_le b a

/-- **Georgii (6.9)**, the event form: for `A ∈ 𝓕_Λ`,
`|μ_+^β(A) − δ_+(A)| ≤ |Λ| r(β)`. -/
theorem abs_plusPhase_sub_dirac_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {A : Set (Site → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] A) :
    |(plusPhase b : Measure (Site → Bool)).real A
        - (Measure.dirac (fun _ : Site ↦ true)).real A| ≤ Λ.card * (r b).toReal :=
  abs_measureReal_sub_dirac_le_of_cylinderEvents hA fun a _ ↦ plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**, the estimate exactly as displayed in the book: for `f ∈ 𝓛_Λ` with
`‖f‖ ≤ M`,
`|μ_+^β(f) − δ_+(f)| ≤ 2‖f‖ μ_+^β(σ_Λ ≠ ω⁺_Λ) ≤ 2‖f‖ |Λ| r(β)`. -/
theorem abs_integral_plusPhase_sub_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {f : (Site → Bool) → ℝ} {M : ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] f)
    (hM : ∀ ζ, |f ζ| ≤ M) :
    |(∫ ζ, f ζ ∂(plusPhase b : Measure (Site → Bool))) - f (fun _ ↦ true)|
      ≤ 2 * M * (Λ.card * (r b).toReal) :=
  abs_integral_sub_apply_le hf hM fun a _ ↦ plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**, the same estimate for the minus phase. -/
theorem abs_integral_minusPhase_sub_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {f : (Site → Bool) → ℝ} {M : ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] f)
    (hM : ∀ ζ, |f ζ| ≤ M) :
    |(∫ ζ, f ζ ∂(minusPhase b : Measure (Site → Bool))) - f (fun _ ↦ false)|
      ≤ 2 * M * (Λ.card * (r b).toReal) :=
  abs_integral_sub_apply_le hf hM fun a _ ↦ minusPhase_real_ne_le hb a

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M4. Georgii Theorem (6.9), first half:
`lim_{β→∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β→∞} d(𝒢_Θ(βΦ), δ₋) = 0` -/

/-- **Georgii (5.13)/(6.9)**: `𝒢_Θ(βΦ)`, the set of shift-invariant Gibbs measures of the
two-dimensional Ising ferromagnet with coupling constant `1` and vanishing external field at
inverse temperature `β`. -/
def shiftInvariantGibbs (b : ℝ) : Set (ProbabilityMeasure (Site → Bool)) :=
  {μ | μ ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) ∧
    ∀ j : Site, MeasurePreserving (shift Bool j).toFun (μ : Measure (Site → Bool))
      (μ : Measure (Site → Bool))}

lemma plusPhase_mem_shiftInvariantGibbs (b : ℝ) : plusPhase b ∈ shiftInvariantGibbs b :=
  ⟨plusPhase_mem_GP b, plusPhase_measurePreserving_shift b⟩

lemma minusPhase_mem_shiftInvariantGibbs (b : ℝ) : minusPhase b ∈ shiftInvariantGibbs b :=
  ⟨minusPhase_mem_GP b, minusPhase_measurePreserving_shift b⟩

/-- **Georgii (6.9)**: `μ_+^β → δ_+` in the topology of local convergence as `β → ∞`. -/
theorem tendsto_localDist_plusPhase :
    Tendsto (fun b : ℝ ↦ localDist (plusPhase b) (diracProb (fun _ : Site ↦ true)))
      atTop (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
  exact plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**: `μ_-^β → δ_-` in the topology of local convergence as `β → ∞`. -/
theorem tendsto_localDist_minusPhase :
    Tendsto (fun b : ℝ ↦ localDist (minusPhase b) (diracProb (fun _ : Site ↦ false)))
      atTop (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
  exact minusPhase_real_ne_le hb a

/-- **Georgii Theorem (6.9), first half.** In the ferromagnetic Ising model on `ℤ²` with coupling
constant `1` and vanishing external field,
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`,
where `d` is any metric for the `𝓛`-topology (here `localDist`, one of the metrics whose
existence is Remark (4.3)(3)), `𝒢_Θ(βΦ)` is the set of shift-invariant Gibbs measures, and
`δ_±` are the Dirac
measures at the two ground states `ω^±`. -/
theorem tendsto_localDistSet_shiftInvariantGibbs_dirac :
    Tendsto (fun b : ℝ ↦ localDistSet (shiftInvariantGibbs b)
        (diracProb (fun _ : Site ↦ true))) atTop (𝓝 0) ∧
      Tendsto (fun b : ℝ ↦ localDistSet (shiftInvariantGibbs b)
        (diracProb (fun _ : Site ↦ false))) atTop (𝓝 0) := by
  constructor
  · refine tendsto_localDistSet_diracProb (μs := plusPhase) plusPhase_mem_shiftInvariantGibbs
      (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
    exact plusPhase_real_ne_le hb a
  · refine tendsto_localDistSet_diracProb (μs := minusPhase) minusPhase_mem_shiftInvariantGibbs
      (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
    exact minusPhase_real_ne_le hb a

end MeasureTheory.GibbsMeasure.Peierls

end

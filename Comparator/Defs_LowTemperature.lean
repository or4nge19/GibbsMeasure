import Comparator.Defs
import Comparator.Defs_Ising

/-!
# Definitions: Georgii's metric (4.3)(3) and the shift-invariant Gibbs measures of the Ising model

Vocabulary for Georgii's Theorem (6.9), first assertion
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`, extending the two-dimensional Ising
model of `Comparator.Defs_Ising` with Georgii's metric of Remark (4.3)(3) for the topology of
local convergence.

## Main definitions

* `shiftInvariantGibbs`: `𝒢_Θ(βΦ)` of Georgii (5.13)
* `localDist`, `localDistSet`: `d(μ, ν) = ∑_{n ≥ 1} 2⁻ⁿ|μ(Aₙ) − ν(Aₙ)|` of Remark (4.3)(3), and
  `d(F, ν) = inf_{μ ∈ F} d(μ, ν)`
* `peierlsBound`: the Peierls series `r(β) = ∑_{ℓ ≥ 1} ℓ · 4096^ℓ · e^{-2βℓ}`

Georgii lets `d` be *any* metric for the `𝓛`-topology; Remark (4.3)(3) exhibits one, built from a
cofinal sequence of finite volumes, and an enumeration of the countable algebra `𝓕⁰` gives
another.  Rather than fixing one enumeration, `localDist A` is defined for an arbitrary sequence
`A : ℕ → Set Config` and the theorems are asserted for every such sequence of local events, which
is strictly stronger.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Remark (4.3)(3) and (5.13)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal
open scoped Topology

noncomputable section

namespace GibbsChallenge

/-! ## Local events depend only on the coordinates inside the volume -/

variable {S E : Type*} [MeasurableSpace E]

def restrictInside (Λ : Finset S) (ω : Config S E) : {i : S // i ∈ Λ} → E := fun i => ω i.1

theorem measurable_restrictInside (Λ : Finset S) :
    Measurable[inside Λ] (restrictInside (E := E) Λ) :=
  measurable_pi_of _ fun i => Measurable.of_comap_le (comap_le_inside i.2)

/-- `𝓕_Λ` is the σ-algebra pulled back along the restriction map `ω ↦ ω|_Λ`. -/
theorem inside_eq_comap (Λ : Finset S) :
    inside (E := E) Λ = MeasurableSpace.comap (restrictInside Λ) inferInstance := by
  refine le_antisymm ?_ (measurable_restrictInside Λ).comap_le
  refine iSup₂_le fun i hi => ?_
  have h1 : Measurable[MeasurableSpace.comap (restrictInside (E := E) Λ) inferInstance]
      (restrictInside Λ) := Measurable.of_comap_le le_rfl
  exact ((measurable_pi_apply (⟨i, hi⟩ : {i : S // i ∈ Λ})).comp h1).comap_le

/-- Events measurable inside `Λ` depend only on the coordinates inside `Λ`. -/
theorem mem_iff_mem_of_inside {Λ : Finset S} {A : Set (Config S E)}
    (hA : MeasurableSet[inside Λ] A) {ω ω' : Config S E} (h : ∀ i ∈ Λ, ω i = ω' i) :
    ω ∈ A ↔ ω' ∈ A := by
  rw [inside_eq_comap] at hA
  obtain ⟨C, -, rfl⟩ := hA
  have hr : restrictInside Λ ω = restrictInside Λ ω' := funext fun i => h i.1 i.2
  simp only [Set.mem_preimage, hr]

end GibbsChallenge

namespace IsingChallenge

/-! ### Georgii (5.13): the shift-invariant Gibbs measures `𝒢_Θ(βΦ)` -/

/-- **Georgii (5.13)**: `𝒢_Θ(βΦ)`, the shift-invariant Gibbs measures of the two-dimensional Ising
ferromagnet at inverse temperature `β`. -/
def shiftInvariantGibbs (β : ℝ) : Set (Measure Config) :=
  {μ | IsGibbs β μ ∧ ∀ j : Site, μ.map (shift j) = μ}

/-! ### Local events and Georgii's metric (4.3)(3) for the `𝓛`-topology -/

/-- **Georgii (4.1)**: the algebra `𝓕⁰ = ⋃_Λ 𝓕_Λ` of local events, specialised to the Ising
configuration space. -/
abbrev IsLocalEvent (A : Set Config) : Prop :=
  GibbsChallenge.IsLocalEvent (S := Site) (E := Bool) A

/-- **Georgii (4.2)**: local (`𝓛`-) convergence, specialised to the Ising configuration space. -/
abbrev TendstoLocally (μ : ℝ → Measure Config) (L : Filter ℝ) (ν : Measure Config) : Prop :=
  GibbsChallenge.TendstoLocally (S := Site) (E := Bool) μ L ν

/-- A metric `d(μ, ν) = ∑_{n ≥ 1} 2⁻ⁿ |μ(Aₙ) − ν(Aₙ)|` for the topology of local convergence,
built from a sequence `A` of local events.  **Georgii, Remark (4.3)(3)** exhibits instead the
metric built from a cofinal sequence `(Λ(n))` of finite volumes; (6.9) is stated for *any* metric
of the `𝓛`-topology, and `localDist A` is one whenever `A` enumerates `𝓕⁰`.  The theorems below
are stated for every such sequence. -/
def localDist (A : ℕ → Set Config) (μ ν : Measure Config) : ℝ :=
  ∑' n : ℕ, (2 : ℝ)⁻¹ ^ (n + 1) * |(μ (A n)).toReal - (ν (A n)).toReal|

/-- **Georgii's `d(F, ν)`** `= inf_{μ ∈ F} d(μ, ν)`. -/
def localDistSet (A : ℕ → Set Config) (F : Set (Measure Config)) (ν : Measure Config) : ℝ :=
  sInf ((fun μ ↦ localDist A μ ν) '' F)

/-! ### The Peierls bound -/

/-- The Peierls series `r(β) = ∑_{ℓ ≥ 1} ℓ · 4096^ℓ · e^{-2βℓ}` bounding the probability that the
spin at a given site is `−1` in the plus phase.  The factor `4096^ℓ` is a crude contour count,
much larger than Georgii's `3^ℓ`; no smaller constant is claimed, only `r(β) → 0`. -/
def peierlsBound (β : ℝ) : ℝ≥0∞ :=
  ∑' l : ℕ, ((l : ℝ≥0∞) + 1) * 4096 ^ (l + 1) *
    ENNReal.ofReal (Real.exp (-2 * β * ((l : ℝ) + 1)))

/-! #### `localDist` is a pseudometric, and `localDistSet` is the associated distance to a set -/

theorem abs_toReal_sub_le_one {μ ν : Measure Config} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (B : Set Config) :
    |(μ B).toReal - (ν B).toReal| ≤ 1 := by
  have hμ1 : (μ B).toReal ≤ 1 := measureReal_le_one (μ := μ) (s := B)
  have hν1 : (ν B).toReal ≤ 1 := measureReal_le_one (μ := ν) (s := B)
  have hμ0 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have hν0 : (0 : ℝ) ≤ (ν B).toReal := ENNReal.toReal_nonneg
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem summable_geomHalf : Summable (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ (n + 1)) := by
  have h : Summable (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [pow_succ] using h.mul_right ((2 : ℝ)⁻¹)

theorem localDist_summand_nonneg (A : ℕ → Set Config) (μ ν : Measure Config) (n : ℕ) :
    0 ≤ (2 : ℝ)⁻¹ ^ (n + 1) * |(μ (A n)).toReal - (ν (A n)).toReal| := by positivity

theorem localDist_summand_le (A : ℕ → Set Config) {μ ν : Measure Config} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (n : ℕ) :
    (2 : ℝ)⁻¹ ^ (n + 1) * |(μ (A n)).toReal - (ν (A n)).toReal| ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  nth_rewrite 2 [← mul_one ((2 : ℝ)⁻¹ ^ (n + 1))]
  exact mul_le_mul_of_nonneg_left (abs_toReal_sub_le_one _) (by positivity)

theorem summable_localDist (A : ℕ → Set Config) (μ ν : Measure Config) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    Summable (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ (n + 1) * |(μ (A n)).toReal - (ν (A n)).toReal|) :=
  Summable.of_nonneg_of_le (localDist_summand_nonneg A μ ν)
    (fun n ↦ localDist_summand_le A n) summable_geomHalf

theorem localDist_nonneg (A : ℕ → Set Config) (μ ν : Measure Config) : 0 ≤ localDist A μ ν :=
  tsum_nonneg (localDist_summand_nonneg A μ ν)

theorem localDist_self (A : ℕ → Set Config) (μ : Measure Config) : localDist A μ μ = 0 := by
  simp [localDist]

theorem localDist_comm (A : ℕ → Set Config) (μ ν : Measure Config) :
    localDist A μ ν = localDist A ν μ :=
  tsum_congr fun n ↦ by rw [abs_sub_comm]

theorem localDist_triangle (A : ℕ → Set Config) (μ ν ρ : Measure Config) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    localDist A μ ρ ≤ localDist A μ ν + localDist A ν ρ := by
  rw [localDist, localDist, localDist,
    ← (summable_localDist A μ ν).tsum_add (summable_localDist A ν ρ)]
  refine (summable_localDist A μ ρ).tsum_le_tsum (fun n ↦ ?_)
    ((summable_localDist A μ ν).add (summable_localDist A ν ρ))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) (by positivity)

theorem localDistSet_bddBelow (A : ℕ → Set Config) (F : Set (Measure Config))
    (ν : Measure Config) : BddBelow ((fun μ ↦ localDist A μ ν) '' F) := by
  refine ⟨0, ?_⟩
  rintro x ⟨μ, -, rfl⟩
  exact localDist_nonneg A μ ν

theorem localDistSet_nonneg (A : ℕ → Set Config) (F : Set (Measure Config)) (ν : Measure Config) :
    0 ≤ localDistSet A F ν := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [localDistSet]
  · refine le_csInf (hF.image _) ?_
    rintro x ⟨μ, -, rfl⟩
    exact localDist_nonneg A μ ν

theorem localDistSet_le (A : ℕ → Set Config) {F : Set (Measure Config)} {μ ν : Measure Config}
    (hμ : μ ∈ F) : localDistSet A F ν ≤ localDist A μ ν :=
  csInf_le (localDistSet_bddBelow A F ν) (Set.mem_image_of_mem _ hμ)

end IsingChallenge

end

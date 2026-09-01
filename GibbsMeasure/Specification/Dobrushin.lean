/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.SpecialFunctions.Tanh
public import GibbsMeasure.Potential.Existence
public import GibbsMeasure.Potential.FiniteReference
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

/-!
# Georgii §8.1: Dobrushin's condition of weak dependence

Georgii (8.1)–(8.6), the potential criterion (8.8) and its `tanh` sharpening (8.10).

Proposition (8.8) is proved at Georgii's hypotheses
(`Dobrushin.isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible`): a σ-finite non-zero a priori
measure `λ`, a `λ`-admissible potential — `Potential.IsSummable` plus finiteness of the partition
functions, with no absolute-summability restriction on the self-potential — and
`sup_i |β| ∑_{A ∋ i} (|A| − 1) δ(Φ_A) < 2`. The probability/absolutely-summable case is the
corollary `Dobrushin.isDobrushin_gibbsSpecification`.

The Ising instances live in `GibbsMeasure/Model/IsingDobrushin.lean`: a `Specification/` file
states criteria, a `Model/` file applies them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace MeasureTheory.GibbsMeasure.Dobrushin

variable {S E : Type*} [MeasurableSpace E]

/-- Georgii (8.1): the uniform distance `‖α₁ − α₂‖ = sup_{A ∈ ℰ} (α₁(A) − α₂(A))`, the
subtraction being the truncated subtraction of `ℝ≥0∞`.

Because of that truncation this is *not* a distance for general measures: it is asymmetric, and
it is Georgii's `‖α₁ − α₂‖` only when `α₁` and `α₂` are probability measures. In that case it is
symmetric (`unifDist_comm`) and equals half the total variation of the signed measure
`α₁ − α₂` (`unifDist_eq_totalVariation_div_two`), which is Georgii's own description of (8.1).
Every lemma below that expresses (8.1) as a distance carries `IsProbabilityMeasure`
hypotheses. -/
def unifDist (α₁ α₂ : Measure E) : ℝ≥0∞ := ⨆ (A) (_ : MeasurableSet A), α₁ A - α₂ A

/-- Georgii (8.5): Dobrushin's interdependence matrix. -/
def interdep (γ : Specification S E) (i j : S) : ℝ≥0∞ :=
  ⨆ (ζ : S → E) (η : S → E) (_ : ∀ k, k ≠ j → ζ k = η k),
    unifDist ((γ {i} ζ).map (fun ω ↦ ω i)) ((γ {i} η).map (fun ω ↦ ω i))

/-- **Georgii (8.6)**: Dobrushin's condition of weak dependence. Georgii's definition has *two*
conjuncts: `γ` is quasilocal, and `c(γ) = sup_i ∑_j C_ij(γ) < 1`.

The quasilocality conjunct carries real content and is not implied by the second one: the sum
`∑_j C_ij(γ)` says nothing about the dependence of `γ_i^0(·|ω)` on the behaviour of `ω` at
infinity, so a tail dependence has to be excluded separately. Georgii's Example (2.27) exhibits
the gap: there `E = {0,1}`, `S = ℕ`, and `γ_Λ(·|ω) = γ_Λ^{ξ(ω)}(·|ω)` is glued out of the
independent specifications `γ^x` of the Bernoulli(`x`) measures along the *tail* function
`ξ = liminf_n n⁻¹ ∑_{i ≤ n} σ_i`. Every `γ_i^0(·|ω) = λ^{ξ(ω)}` is then unchanged by a
single-site modification of `ω`, so `C_ij(γ) = 0` for all `i, j` and `c(γ) = 0 < 1`; yet
`𝒢(γ) = {∫ w(dx) μ^x : w ∈ 𝓟([0,1])}` is uncountable, very far from a singleton.
Dropping the quasilocality conjunct would therefore make Theorem (8.7) below false. -/
def IsDobrushin (γ : Specification S E) : Prop :=
  γ.IsQuasilocal ∧ ∃ c : ℝ≥0∞, c < 1 ∧ ∀ i, ∑' j, interdep γ i j ≤ c

/-- The oscillation `δ(f) = sup_{ζ,η} |f(ζ) − f(η)|` of a function on the configuration space
(Georgii, the unnumbered display before Proposition (8.8), "in analogy with (8.2)"; (8.2) itself
is the oscillation of a function on the state space `E`).

It is the oscillation `oscOutside ∅ f` of `f` under variation of *all* coordinates; the two
agree because the `ℝ≥0∞`-valued distance of `ℝ` is `edist a b = ENNReal.ofReal |a − b|`
(`le_osc`, `osc_le`). -/
def osc (f : (S → E) → ℝ) : ℝ≥0∞ := _root_.oscOutside (∅ : Set S) f

/-- Georgii (8.14): the single-site oscillation `δ_j(f)`, the oscillation of `f` under variation
of the coordinate `j` alone, i.e. `oscOutside {j}ᶜ f`. -/
def oscAt (f : (S → E) → ℝ) (j : S) : ℝ≥0∞ := _root_.oscOutside ({j}ᶜ : Set S) f

/-! ### Georgii (8.2), (8.14): the basic oscillation API

`osc` and `oscAt` are the two instances `∅` and `{j}ᶜ` of the general `oscOutside` of
`GibbsMeasure/Mathlib/Topology/MetricSpace/DependsOn.lean`, so everything below is one line of
that API together with the bridge `edist_ofReal_abs_sub` between the `edist` of `ℝ` and
`ENNReal.ofReal |·|`. -/

section OscBasic

omit [MeasurableSpace E]

variable {f : (S → E) → ℝ} {j : S} {c : ℝ≥0∞}

lemma osc_eq_oscOutside_empty (f : (S → E) → ℝ) :
    osc f = _root_.oscOutside (∅ : Set S) f := rfl

lemma oscAt_eq_oscOutside_compl (f : (S → E) → ℝ) (j : S) :
    oscAt f j = _root_.oscOutside ({j}ᶜ : Set S) f := rfl

/-- The bridge between the value type of `oscOutside` on `ℝ` and Georgii's `|f(ζ) − f(η)|`: the
extended distance of two reals is `ENNReal.ofReal` of their absolute difference. -/
lemma edist_ofReal_abs_sub (a b : ℝ) : edist a b = ENNReal.ofReal |a - b| := by
  rw [edist_dist, Real.dist_eq]

lemma le_osc (f : (S → E) → ℝ) (ζ η : S → E) : ENNReal.ofReal |f ζ - f η| ≤ osc f := by
  rw [← edist_ofReal_abs_sub]
  exact _root_.le_oscOutside (by simp)

lemma osc_le (h : ∀ ζ η : S → E, ENNReal.ofReal |f ζ - f η| ≤ c) : osc f ≤ c :=
  _root_.oscOutside_le fun ζ η _ ↦ (edist_ofReal_abs_sub (f ζ) (f η)).trans_le (h ζ η)

lemma le_oscAt {ζ η : S → E} (h : ∀ k, k ≠ j → ζ k = η k) :
    ENNReal.ofReal |f ζ - f η| ≤ oscAt f j := by
  rw [← edist_ofReal_abs_sub]
  exact _root_.le_oscOutside fun k hk ↦ h k (by simpa using hk)

lemma oscAt_le (h : ∀ ζ η : S → E, (∀ k, k ≠ j → ζ k = η k) → ENNReal.ofReal |f ζ - f η| ≤ c) :
    oscAt f j ≤ c :=
  _root_.oscOutside_le fun ζ η hζη ↦
    (edist_ofReal_abs_sub (f ζ) (f η)).trans_le (h ζ η fun k hk ↦ hζη k (by simpa using hk))

/-- Georgii (8.14): the single-site oscillation is dominated by the global oscillation. More
generally `oscOutside s f ≤ osc f` for every `s`, by `oscOutside_antitone`. -/
lemma oscAt_le_osc : oscAt f j ≤ osc f := _root_.oscOutside_antitone (Set.empty_subset _)

@[simp] lemma osc_const (r : ℝ) : osc (fun _ : S → E ↦ r) = 0 :=
  _root_.DependsOn.oscOutside_eq_zero (dependsOn_const r)

@[simp] lemma oscAt_const (r : ℝ) (j : S) : oscAt (fun _ : S → E ↦ r) j = 0 :=
  _root_.DependsOn.oscOutside_eq_zero ((dependsOn_const r).mono (Set.empty_subset _))

/-- A function that only depends on the coordinates in `Δ` has no oscillation at sites off `Δ`. -/
lemma oscAt_eq_zero_of_dependsOn {Δ : Set S} (hf : DependsOn f Δ) (hj : j ∉ Δ) :
    oscAt f j = 0 :=
  _root_.DependsOn.oscOutside_eq_zero <| hf.mono fun k hk ↦ by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hj hk

end OscBasic

/-! ### M1: the uniform distance (Georgii (8.1)) -/

section UnifDist

variable {α₁ α₂ α₃ : Measure E}

lemma le_unifDist {A : Set E} (hA : MeasurableSet A) : α₁ A - α₂ A ≤ unifDist α₁ α₂ :=
  le_iSup₂ (f := fun (A : Set E) (_ : MeasurableSet A) ↦ α₁ A - α₂ A) A hA

lemma unifDist_le {c : ℝ≥0∞} (h : ∀ A, MeasurableSet A → α₁ A - α₂ A ≤ c) :
    unifDist α₁ α₂ ≤ c :=
  iSup₂_le h

@[simp] lemma unifDist_self (α : Measure E) : unifDist α α = 0 :=
  le_antisymm (unifDist_le fun _ _ ↦ by simp) bot_le

private lemma tsub_one_sub {x y : ℝ≥0∞} (hx : x ≤ 1) :
    x - y = (1 - y) - (1 - x) := by
  rcases le_total x y with h | h
  · rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (tsub_le_tsub_left h 1)]
  · have h3 : (1 : ℝ≥0∞) - x = (1 - y) - (x - y) := by
      rw [tsub_tsub, add_tsub_cancel_of_le h]
    rw [h3, ENNReal.sub_sub_cancel (by simp) (tsub_le_tsub_right hx y)]

/-- Georgii (8.1) is symmetric: on complements the two differences swap. -/
lemma unifDist_comm (α₁ α₂ : Measure E) [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ = unifDist α₂ α₁ := by
  have key : ∀ (β₁ β₂ : Measure E), IsProbabilityMeasure β₁ → IsProbabilityMeasure β₂ →
      unifDist β₁ β₂ ≤ unifDist β₂ β₁ := by
    intro β₁ β₂ _ _
    refine unifDist_le fun A hA ↦ ?_
    have h1 : β₁ Aᶜ = 1 - β₁ A := prob_compl_eq_one_sub hA
    have h2 : β₂ Aᶜ = 1 - β₂ A := prob_compl_eq_one_sub hA
    have := tsub_one_sub (x := β₁ A) (y := β₂ A) prob_le_one
    rw [this, ← h1, ← h2]
    exact le_unifDist hA.compl
  exact le_antisymm (key _ _ ‹_› ‹_›) (key _ _ ‹_› ‹_›)

lemma unifDist_le_one [IsProbabilityMeasure α₁] : unifDist α₁ α₂ ≤ 1 :=
  unifDist_le fun _ _ ↦ le_trans tsub_le_self prob_le_one

lemma unifDist_ne_top [IsProbabilityMeasure α₁] : unifDist α₁ α₂ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top unifDist_le_one

/-- The triangle inequality for the uniform distance. -/
lemma unifDist_triangle : unifDist α₁ α₃ ≤ unifDist α₁ α₂ + unifDist α₂ α₃ := by
  refine unifDist_le fun A hA ↦ ?_
  have h1 : α₁ A ≤ (α₁ A - α₂ A) + α₂ A := le_tsub_add
  have h2 : α₂ A ≤ (α₂ A - α₃ A) + α₃ A := le_tsub_add
  refine tsub_le_iff_right.2 (h1.trans ?_)
  calc (α₁ A - α₂ A) + α₂ A ≤ (α₁ A - α₂ A) + ((α₂ A - α₃ A) + α₃ A) := by gcongr
    _ = ((α₁ A - α₂ A) + (α₂ A - α₃ A)) + α₃ A := by ring
    _ ≤ (unifDist α₁ α₂ + unifDist α₂ α₃) + α₃ A := by
        gcongr <;> exact le_unifDist hA

/-- Georgii (8.1) as a supremum of absolute differences. -/
lemma ofReal_abs_sub_le_unifDist [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂]
    {A : Set E} (hA : MeasurableSet A) :
    ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal| ≤ unifDist α₁ α₂ := by
  have h1 : α₁ A ≠ ⊤ := measure_ne_top _ _
  have h2 : α₂ A ≠ ⊤ := measure_ne_top _ _
  rcases le_total (α₂ A) (α₁ A) with h | h
  · have habs : |(α₁ A).toReal - (α₂ A).toReal| = (α₁ A).toReal - (α₂ A).toReal :=
      abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal h2 h1).2 h))
    rw [habs, ← ENNReal.toReal_sub_of_le h h1, ENNReal.ofReal_toReal (by simp [h1, h2])]
    exact le_unifDist hA
  · have habs : |(α₁ A).toReal - (α₂ A).toReal| = (α₂ A).toReal - (α₁ A).toReal :=
      abs_sub_comm ((α₁ A).toReal) ((α₂ A).toReal) ▸
        abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal h1 h2).2 h))
    rw [habs, ← ENNReal.toReal_sub_of_le h h2, ENNReal.ofReal_toReal (by simp [h1, h2]),
      unifDist_comm]
    exact le_unifDist hA

/-- Pushing forward is a contraction for the uniform distance. -/
lemma unifDist_map_le {F : Type*} [MeasurableSpace F] {f : E → F} (hf : Measurable f)
    (α₁ α₂ : Measure E) : unifDist (α₁.map f) (α₂.map f) ≤ unifDist α₁ α₂ := by
  refine unifDist_le fun A hA ↦ ?_
  rw [Measure.map_apply hf hA, Measure.map_apply hf hA]
  exact le_unifDist (hf hA)

/-! #### Georgii (8.1) is half the total variation

`unifDist` is defined with the truncated subtraction of `ℝ≥0∞`; the following identifies it, for
probability measures, with Mathlib's total variation of the signed measure `α₁ − α₂`, which is
what Georgii calls `‖α₁ − α₂‖`. -/

private lemma tsub_eq_ofReal_toReal_sub {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x - y = ENNReal.ofReal (x.toReal - y.toReal) := by
  rcases le_total y x with h | h
  · rw [← ENNReal.toReal_sub_of_le h hx,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top hx tsub_le_self)]
  · rw [tsub_eq_zero_of_le h, ENNReal.ofReal_eq_zero.2 (by
      have := ENNReal.toReal_mono hy h; linarith)]

/-- **Georgii (8.1) is half the total variation.** For probability measures the truncated
`ℝ≥0∞`-subtraction defining `unifDist` computes Georgii's `‖α₁ − α₂‖`: twice it is the total
variation `|α₁ − α₂|(E)` of the signed measure `α₁ − α₂` in the sense of
`MeasureTheory.SignedMeasure.totalVariation`. -/
theorem two_mul_unifDist_eq_totalVariation (α₁ α₂ : Measure E)
    [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    2 * unifDist α₁ α₂
      = (α₁.toSignedMeasure - α₂.toSignedMeasure).totalVariation univ := by
  have hsapp : ∀ A : Set E, MeasurableSet A →
      (α₁.toSignedMeasure - α₂.toSignedMeasure) A = (α₁ A).toReal - (α₂ A).toReal := by
    intro A hA
    rw [Measure.toSignedMeasure_sub_apply hA]
    simp [measureReal_def]
  set s : SignedMeasure E := α₁.toSignedMeasure - α₂.toSignedMeasure with hs
  obtain ⟨i, hi₁, hi₂, hi₃, hpos, hneg⟩ := s.toJordanDecomposition_spec
  -- a Hahn set `i` maximises `s`, so the supremum defining `unifDist` is attained at `i`
  have hmax : ∀ A : Set E, MeasurableSet A → s A ≤ s i := by
    intro A hA
    have h1 : s (A ∩ i) + s (A \ (A ∩ i)) = s A :=
      VectorMeasure.of_add_of_sdiff (hA.inter hi₁) hA Set.inter_subset_left
    have h2 : s (A ∩ i) + s (i \ (A ∩ i)) = s i :=
      VectorMeasure.of_add_of_sdiff (hA.inter hi₁) hi₁ Set.inter_subset_right
    have hlo : s (A \ (A ∩ i)) ≤ 0 := by
      have := VectorMeasure.subset_le_of_restrict_le_restrict s 0 hi₁.compl hi₃
        (show A \ (A ∩ i) ⊆ iᶜ from fun _ hx hxi ↦ hx.2 ⟨hx.1, hxi⟩)
      simpa using this
    have hhi : 0 ≤ s (i \ (A ∩ i)) := by
      have := VectorMeasure.subset_le_of_restrict_le_restrict 0 s hi₁ hi₂
        (show i \ (A ∩ i) ⊆ i from Set.sdiff_subset)
      simpa using this
    linarith
  -- the two Jordan parts, evaluated on the whole space
  have hposUniv : s.toJordanDecomposition.posPart univ = ENNReal.ofReal (s i) := by
    have hreal : (s.toJordanDecomposition.posPart).real univ = s i := by
      rw [hpos, s.toMeasureOfZeroLE_real_apply hi₂ hi₁ MeasurableSet.univ, Set.inter_univ]
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hnegUniv : s.toJordanDecomposition.negPart univ = ENNReal.ofReal (-s iᶜ) := by
    have hreal : (s.toJordanDecomposition.negPart).real univ = -s iᶜ := by
      rw [hneg, s.toMeasureOfLEZero_real_apply hi₃ hi₁.compl MeasurableSet.univ, Set.inter_univ]
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  -- both measures are probability measures, so `s univ = 0` and the two parts have equal mass
  have hsuniv : s univ = 0 := by rw [hsapp univ MeasurableSet.univ]; simp
  have hsplit : s i + s iᶜ = s univ := by
    rw [Set.compl_eq_univ_sdiff]
    exact VectorMeasure.of_add_of_sdiff hi₁ MeasurableSet.univ (Set.subset_univ i)
  have hcompl : -s iᶜ = s i := by rw [hsuniv] at hsplit; linarith
  -- and the supremum defining `unifDist` is `s i`
  have hunif : unifDist α₁ α₂ = ENNReal.ofReal (s i) := by
    refine le_antisymm (unifDist_le fun A hA ↦ ?_) ?_
    · rw [tsub_eq_ofReal_toReal_sub (measure_ne_top _ _) (measure_ne_top _ _), ← hsapp A hA]
      exact ENNReal.ofReal_le_ofReal (hmax A hA)
    · rw [hsapp i hi₁, ← tsub_eq_ofReal_toReal_sub (measure_ne_top _ _) (measure_ne_top _ _)]
      exact le_unifDist hi₁
  rw [SignedMeasure.totalVariation, Measure.add_apply, hposUniv, hnegUniv, hcompl, hunif, two_mul]

/-- **Georgii (8.1).** For probability measures the uniform distance is half the total variation
of the signed measure `α₁ − α₂`. -/
theorem unifDist_eq_totalVariation_div_two (α₁ α₂ : Measure E)
    [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ = (α₁.toSignedMeasure - α₂.toSignedMeasure).totalVariation univ / 2 :=
  (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
    (two_mul_unifDist_eq_totalVariation α₁ α₂)

end UnifDist

/-! ### Georgii (8.1), second expression: `|α₁(f) − α₂(f)| ≤ δ(f) ‖α₁ − α₂‖` -/

section UnifDistIntegral

variable {X : Type*} [MeasurableSpace X] {α₁ α₂ : Measure X}

private lemma ofReal_toReal_sub_le {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    ENNReal.ofReal (x.toReal - y.toReal) ≤ x - y := by
  rcases le_total y x with h | h
  · rw [← ENNReal.toReal_sub_of_le h hx,
      ENNReal.ofReal_toReal (ne_top_of_le_ne_top hx tsub_le_self)]
  · have hle : x.toReal ≤ y.toReal := ENNReal.toReal_mono hy h
    rw [ENNReal.ofReal_eq_zero.2 (by linarith)]
    exact bot_le

/-- The layer-cake form of Georgii (8.1): for `0 ≤ f ≤ δ`, the `f`-integrals of two measures
differ by at most `δ ‖α₁ − α₂‖`. -/
lemma lintegral_ofReal_sub_le {f : X → ℝ} (hf : Measurable f) {δ : ℝ}
    (h0 : ∀ x, 0 ≤ f x) (hub : ∀ x, f x ≤ δ) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂α₁) - ∫⁻ x, ENNReal.ofReal (f x) ∂α₂
      ≤ ENNReal.ofReal δ * unifDist α₁ α₂ := by
  set U := unifDist α₁ α₂ with hU
  rw [lintegral_eq_lintegral_meas_lt α₁ (.of_forall h0) hf.aemeasurable,
      lintegral_eq_lintegral_meas_lt α₂ (.of_forall h0) hf.aemeasurable]
  have hpt : ∀ t : ℝ, α₁ {a | t < f a}
      ≤ α₂ {a | t < f a} + (Set.Iio δ).indicator (fun _ ↦ U) t := by
    intro t
    by_cases ht : t < δ
    · rw [Set.indicator_of_mem (show t ∈ Set.Iio δ from ht)]
      exact tsub_le_iff_left.1 (le_unifDist (measurableSet_lt measurable_const hf))
    · have hempty : {a | t < f a} = (∅ : Set X) := by
        ext a
        simp only [Set.mem_empty_iff_false, iff_false]
        exact fun hc ↦ absurd (lt_of_lt_of_le hc (hub a)) ht
      rw [hempty]
      simp
  rw [tsub_le_iff_right]
  calc ∫⁻ t in Set.Ioi (0:ℝ), α₁ {a | t < f a}
      ≤ ∫⁻ t in Set.Ioi (0:ℝ), (α₂ {a | t < f a} + (Set.Iio δ).indicator (fun _ ↦ U) t) :=
        lintegral_mono hpt
    _ = (∫⁻ t in Set.Ioi (0:ℝ), α₂ {a | t < f a})
          + ∫⁻ t in Set.Ioi (0:ℝ), (Set.Iio δ).indicator (fun _ ↦ U) t :=
        lintegral_add_right _ (measurable_const.indicator measurableSet_Iio)
    _ = (∫⁻ t in Set.Ioi (0:ℝ), α₂ {a | t < f a}) + ENNReal.ofReal δ * U := by
        congr 1
        rw [lintegral_indicator measurableSet_Iio, setLIntegral_const,
          Measure.restrict_apply measurableSet_Iio, Set.Iio_inter_Ioi, Real.volume_Ioo]
        simp [mul_comm]
    _ = ENNReal.ofReal δ * U + ∫⁻ t in Set.Ioi (0:ℝ), α₂ {a | t < f a} := add_comm _ _

lemma ofReal_integral_sub_le [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂]
    {f : X → ℝ} (hf : Measurable f) {δ : ℝ} (h0 : ∀ x, 0 ≤ f x) (hub : ∀ x, f x ≤ δ) :
    ENNReal.ofReal (∫ x, f x ∂α₁ - ∫ x, f x ∂α₂) ≤ ENNReal.ofReal δ * unifDist α₁ α₂ := by
  have hbound : ∀ (α : Measure X), IsProbabilityMeasure α →
      (∫⁻ x, ENNReal.ofReal (f x) ∂α) ≠ ⊤ := by
    intro α hα
    have hle : (∫⁻ x, ENNReal.ofReal (f x) ∂α) ≤ ENNReal.ofReal δ := by
      calc (∫⁻ x, ENNReal.ofReal (f x) ∂α) ≤ ∫⁻ _x, ENNReal.ofReal δ ∂α :=
            lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hub x)
        _ = ENNReal.ofReal δ := by simp [hα.measure_univ]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have heq : ∀ α : Measure X, ∫ x, f x ∂α = (∫⁻ x, ENNReal.ofReal (f x) ∂α).toReal := fun α ↦
    integral_eq_lintegral_of_nonneg_ae (.of_forall h0) hf.aestronglyMeasurable
  rw [heq α₁, heq α₂]
  exact le_trans (ofReal_toReal_sub_le (hbound α₁ ‹_›) (hbound α₂ ‹_›))
    (lintegral_ofReal_sub_le hf h0 hub)

/-- **Georgii (8.1), second expression** (the inequality the uniqueness proof needs):
`|α₁(f) − α₂(f)| ≤ δ(f) ‖α₁ − α₂‖` for a measurable `f` with `a ≤ f ≤ a + δ`. -/
theorem ofReal_abs_integral_sub_le [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂]
    {f : X → ℝ} (hf : Measurable f) {a δ : ℝ}
    (hlo : ∀ x, a ≤ f x) (hhi : ∀ x, f x ≤ a + δ) :
    ENNReal.ofReal |∫ x, f x ∂α₁ - ∫ x, f x ∂α₂| ≤ ENNReal.ofReal δ * unifDist α₁ α₂ := by
  have habs : ∀ (β₁ β₂ : Measure X), IsProbabilityMeasure β₁ → IsProbabilityMeasure β₂ →
      ENNReal.ofReal (∫ x, (f x - a) ∂β₁ - ∫ x, (f x - a) ∂β₂)
        ≤ ENNReal.ofReal δ * unifDist β₁ β₂ := by
    intro β₁ β₂ _ _
    exact ofReal_integral_sub_le (f := fun x ↦ f x - a) (hf.sub measurable_const)
      (fun x ↦ by linarith [hlo x]) (fun x ↦ by linarith [hhi x])
  have hC : ∀ x, ‖f x‖ ≤ |a| + |a + δ| := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      linarith [hlo x, hhi x, neg_abs_le a, le_abs_self a, neg_abs_le (a + δ),
        le_abs_self (a + δ)]
  have hint : ∀ (α : Measure X), IsProbabilityMeasure α → Integrable f α := fun α _ ↦
    Integrable.of_bound hf.aestronglyMeasurable _ (.of_forall hC)
  have hshift : ∀ (α : Measure X), IsProbabilityMeasure α →
      ∫ x, (f x - a) ∂α = (∫ x, f x ∂α) - a := by
    intro α hα
    rw [integral_sub (hint α hα) (integrable_const a), integral_const]
    simp
  rcases le_total (∫ x, f x ∂α₂) (∫ x, f x ∂α₁) with h | h
  · rw [abs_of_nonneg (by linarith)]
    have := habs α₁ α₂ ‹_› ‹_›
    rwa [hshift α₁ ‹_›, hshift α₂ ‹_›,
      show (∫ x, f x ∂α₁) - a - ((∫ x, f x ∂α₂) - a)
        = (∫ x, f x ∂α₁) - ∫ x, f x ∂α₂ by ring] at this
  · rw [abs_of_nonpos (by linarith), neg_sub, unifDist_comm]
    have := habs α₂ α₁ ‹_› ‹_›
    rwa [hshift α₁ ‹_›, hshift α₂ ‹_›,
      show (∫ x, f x ∂α₂) - a - ((∫ x, f x ∂α₁) - a)
        = (∫ x, f x ∂α₂) - ∫ x, f x ∂α₁ by ring] at this

end UnifDistIntegral

/-! ### The elementary analytic estimates behind Georgii (8.8) -/

section Elementary

/-- The Padé lower bound `2 (r-1)/(r+1) ≤ log r` for `r ≥ 1`, obtained from the tangent line to
`t ↦ t⁻¹` at the midpoint `(1+r)/2`. -/
lemma two_mul_sub_div_add_le_log {r : ℝ} (hr : 1 ≤ r) :
    2 * (r - 1) / (r + 1) ≤ Real.log r := by
  rcases eq_or_lt_of_le hr with rfl | hr1
  · simp
  set t₀ : ℝ := (1 + r) / 2 with ht₀def
  have ht₀ : 0 < t₀ := by rw [ht₀def]; linarith
  have hlog : Real.log r = ∫ t in (1:ℝ)..r, t⁻¹ := by
    rw [integral_inv_of_pos one_pos (by linarith)]
    simp
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 1 r) := by
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro x hx
    rw [Set.uIcc_of_le hr] at hx
    exact ne_of_gt (by linarith [hx.1])
  have hint1 : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 r := hcont.intervalIntegrable
  have hmono : (∫ t in (1:ℝ)..r, (2 / t₀ - (t₀ ^ 2)⁻¹ * t)) ≤ ∫ t in (1:ℝ)..r, t⁻¹ := by
    refine intervalIntegral.integral_mono_on hr
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable) hint1 ?_
    intro t ht
    have ht1 : (0:ℝ) < t := by linarith [ht.1]
    have hkey : t⁻¹ - (2 / t₀ - (t₀ ^ 2)⁻¹ * t) = (t - t₀) ^ 2 / (t * t₀ ^ 2) := by
      field_simp
      ring
    have hnn : (0:ℝ) ≤ (t - t₀) ^ 2 / (t * t₀ ^ 2) :=
      div_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hcalc : (∫ t in (1:ℝ)..r, (2 / t₀ - (t₀ ^ 2)⁻¹ * t)) = 2 * (r - 1) / (r + 1) := by
    rw [intervalIntegral.integral_sub ((Continuous.continuousOn (by fun_prop)).intervalIntegrable)
      ((Continuous.continuousOn (by fun_prop)).intervalIntegrable),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    have hr0 : (1:ℝ) + r ≠ 0 := by positivity
    simp only [smul_eq_mul, ht₀def]
    field_simp
    ring
  rw [hlog, ← hcalc]
  exact hmono

/-- `(√M − √m)/(√M + √m) ≤ log (M/m)/4` for `0 < m ≤ M`; this is `tanh x ≤ x` in disguise. -/
lemma sqrtRatio_le_log_div_four {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) ≤ Real.log (M / m) / 4 := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
  have hdiv : 0 < M / m := div_pos hM hm
  set r : ℝ := Real.sqrt (M / m) with hrdef
  have hr1 : 1 ≤ r := by
    rw [hrdef, show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((one_le_div hm).2 hmM)
  have hrr : Real.sqrt M / Real.sqrt m = r := by
    rw [hrdef, Real.sqrt_div hM.le]
  have hlog : Real.log (M / m) = 2 * Real.log r := by
    rw [hrdef, Real.log_sqrt hdiv.le]; ring
  have hkey : 2 * (r - 1) / (r + 1) ≤ Real.log r := two_mul_sub_div_add_le_log hr1
  have hrewrite :
      (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) = (r - 1) / (r + 1) := by
    rw [← hrr]; field_simp
  rw [hrewrite, hlog]
  have hrpos : 0 < r + 1 := by linarith
  rw [div_le_div_iff₀ hrpos (by norm_num)]
  rw [div_le_iff₀ hrpos] at hkey
  linarith

/-- `tanh x ≤ x` for `x ≥ 0`: the `m = 1`, `M = e^{4x}` case of `sqrtRatio_le_log_div_four`,
which is this inequality in disguise. -/
lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hM : (0 : ℝ) < Real.exp (4 * x) := Real.exp_pos _
  have hmM : (1 : ℝ) ≤ Real.exp (4 * x) := Real.one_le_exp (by linarith)
  have h := sqrtRatio_le_log_div_four (m := 1) (M := Real.exp (4 * x)) one_pos hmM
  rw [← Real.tanh_log_div_four one_pos hM] at h
  simpa [Real.log_exp] using h

/-- `tanh x < x` for `x > 0`, so the `tanh` criterion is *strictly* weaker than the `δ` one.
Halving: with `t = tanh (x/2)` the addition formula gives `tanh x = 2t/(1 + t²)`, and
`2t ≤ x` while `1 + t² > 1`. -/
lemma tanh_lt_self {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  set t : ℝ := Real.tanh (x / 2) with ht
  have ht0 : 0 < t := by
    rw [ht, Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 (by linarith)) (Real.cosh_pos _)
  have hthalf : t ≤ x / 2 := ht ▸ tanh_le_self (by linarith)
  have hden : (1 : ℝ) < 1 + t * t := by nlinarith
  have hx2 : x = x / 2 + x / 2 := by ring
  have hsum : t + t ≤ x := by linarith
  calc Real.tanh x = (t + t) / (1 + t * t) := by
        rw [hx2, Real.tanh_add, ← ht]
    _ ≤ x / (1 + t * t) := by gcongr
    _ < x := div_lt_self hx hden

/-- The elementary estimate behind Georgii (8.8): if the "density" of `(c, e)` relative to
`(a, b)` lies between `m` and `M`, then the normalised ratios differ by at most
`(√M − √m)/(√M + √m)`. -/
lemma ratio_sub_ratio_le {m M a b c e : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b)
    (hca : m * a ≤ c) (hcM : c ≤ M * a) (heb : m * b ≤ e) :
    c / (c + e) - a / (a + b) ≤ (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  set sm := Real.sqrt m with hsmdef
  set sM := Real.sqrt M with hsMdef
  have hsm : 0 < sm := Real.sqrt_pos.2 hm
  have hsM : 0 < sM := Real.sqrt_pos.2 hM
  have hsm2 : sm ^ 2 = m := Real.sq_sqrt hm.le
  have hsM2 : sM ^ 2 = M := Real.sq_sqrt hM.le
  have hsmM : sm ≤ sM := Real.sqrt_le_sqrt hmM
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hm.le ha) hca
  have he0 : 0 ≤ e := le_trans (mul_nonneg hm.le hb) heb
  have hce : 0 < c + e := by nlinarith
  have hMamb : 0 < M * a + m * b := by nlinarith
  set K := (sM - sm) / (sM + sm) with hKdef
  have hK0 : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  have hB : a * b * (M - m) ≤ K * ((a + b) * (M * a + m * b)) := by
    rw [hKdef, div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < sM + sm)]
    rw [← hsm2, ← hsM2]
    nlinarith [mul_nonneg (sub_nonneg.2 hsmM) (sq_nonneg (sM * a - sm * b))]
  have hA : (c * b - a * e) * (M * a + m * b) ≤ a * b * (M - m) * (c + e) := by
    nlinarith [mul_le_mul_of_nonneg_left heb (mul_nonneg hM.le ha),
      mul_le_mul_of_nonneg_left hcM (mul_nonneg hm.le hb),
      mul_nonneg ha hb, hab.le]
  have hcomb : (c * b - a * e) * (M * a + m * b)
      ≤ (K * ((c + e) * (a + b))) * (M * a + m * b) := by
    have h1 : a * b * (M - m) * (c + e) ≤ (K * ((a + b) * (M * a + m * b))) * (c + e) :=
      mul_le_mul_of_nonneg_right hB hce.le
    nlinarith [hA, h1]
  have hfinal : c * b - a * e ≤ K * ((c + e) * (a + b)) :=
    le_of_mul_le_mul_right hcomb hMamb
  rw [div_sub_div _ _ (ne_of_gt hce) (ne_of_gt hab), div_le_iff₀ (by positivity)]
  nlinarith [hfinal]

end Elementary

/-! ### The uniform distance between two normalised finite measures -/

section Normalize

private lemma ennreal_sub_le_ofReal {x y : ℝ≥0∞} (hx : x ≠ ⊤) {K : ℝ}
    (h : x.toReal - y.toReal ≤ K) : x - y ≤ ENNReal.ofReal K := by
  rcases le_total x y with hxy | hxy
  · simp [tsub_eq_zero_of_le hxy]
  · rw [← ENNReal.ofReal_toReal (a := x - y) (ne_top_of_le_ne_top hx tsub_le_self),
      ENNReal.toReal_sub_of_le hxy hx]
    exact ENNReal.ofReal_le_ofReal h

/-- **Georgii (8.8), measure-theoretic core, sharp form.** If two finite measures satisfy
`m·μ₀ ≤ μ₁ ≤ M·μ₀` setwise, their normalisations are at uniform distance at most
`(√M − √m)/(√M + √m)`. This is the bound the argument actually produces;
`unifDist_normalize_le` and `unifDist_normalize_le_tanh` are its two readings. -/
lemma unifDist_normalize_le_sqrtRatio {X : Type*} [MeasurableSpace X] {μ₀ μ₁ : Measure X}
    {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (h0top : μ₀ univ ≠ ⊤) (h1top : μ₁ univ ≠ ⊤) (h0ne : μ₀ univ ≠ 0)
    (hlo : ∀ A, MeasurableSet A → ENNReal.ofReal m * μ₀ A ≤ μ₁ A)
    (hhi : ∀ A, MeasurableSet A → μ₁ A ≤ ENNReal.ofReal M * μ₀ A) :
    unifDist ((μ₁ univ)⁻¹ • μ₁) ((μ₀ univ)⁻¹ • μ₀)
      ≤ ENNReal.ofReal ((Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m)) := by
  have hmM0 : ENNReal.ofReal m ≠ 0 := by simpa using hm
  have h1ne : μ₁ univ ≠ 0 := by
    intro hzero
    exact (mul_ne_zero hmM0 h0ne) (le_antisymm (hzero ▸ hlo univ .univ) bot_le)
  have hfin0 : ∀ A, μ₀ A ≠ ⊤ := fun A ↦ ne_top_of_le_ne_top h0top (measure_mono (subset_univ A))
  have hfin1 : ∀ A, μ₁ A ≠ ⊤ := fun A ↦ ne_top_of_le_ne_top h1top (measure_mono (subset_univ A))
  have htoReal : ∀ {ν : Measure X} (A : Set X), ((ν univ)⁻¹ • ν) A = (ν univ)⁻¹ * ν A := by
    intro ν A; simp [Measure.smul_apply]
  refine unifDist_le fun A hA ↦ ?_
  set a := (μ₀ A).toReal with hadef
  set b := (μ₀ Aᶜ).toReal with hbdef
  set c := (μ₁ A).toReal with hcdef
  set e := (μ₁ Aᶜ).toReal with hedef
  have hsum0 : a + b = (μ₀ univ).toReal := by
    rw [hadef, hbdef, ← ENNReal.toReal_add (hfin0 _) (hfin0 _), measure_add_measure_compl hA]
  have hsum1 : c + e = (μ₁ univ).toReal := by
    rw [hcdef, hedef, ← ENNReal.toReal_add (hfin1 _) (hfin1 _), measure_add_measure_compl hA]
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hab : 0 < a + b := by
    rw [hsum0]
    exact ENNReal.toReal_pos h0ne h0top
  have hce : 0 < c + e := by
    rw [hsum1]
    exact ENNReal.toReal_pos h1ne h1top
  have key : ∀ B, MeasurableSet B →
      m * (μ₀ B).toReal ≤ (μ₁ B).toReal ∧ (μ₁ B).toReal ≤ M * (μ₀ B).toReal := by
    intro B hB
    constructor
    · have := ENNReal.toReal_mono (hfin1 B) (hlo B hB)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le] at this
    · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin0 B)) (hhi B hB)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hm.le.trans hmM)] at this
  have hkeyA := key A hA
  have hkeyAc := key Aᶜ hA.compl
  have hmain : c / (c + e) - a / (a + b)
      ≤ (Real.sqrt M - Real.sqrt m) / (Real.sqrt M + Real.sqrt m) :=
    ratio_sub_ratio_le hm hmM ha hb hab hkeyA.1 hkeyA.2 hkeyAc.1
  rw [htoReal A, htoReal A]
  refine ennreal_sub_le_ofReal
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 h1ne) (hfin1 A)) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
    ← hsum0, ← hsum1]
  rw [inv_mul_eq_div, inv_mul_eq_div]
  exact hmain

/-- **Georgii (8.8), measure-theoretic core.** The `log (M/m)/4` reading of
`unifDist_normalize_le_sqrtRatio`, via the Padé bound `sqrtRatio_le_log_div_four`. -/
lemma unifDist_normalize_le {X : Type*} [MeasurableSpace X] {μ₀ μ₁ : Measure X}
    {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (h0top : μ₀ univ ≠ ⊤) (h1top : μ₁ univ ≠ ⊤) (h0ne : μ₀ univ ≠ 0)
    (hlo : ∀ A, MeasurableSet A → ENNReal.ofReal m * μ₀ A ≤ μ₁ A)
    (hhi : ∀ A, MeasurableSet A → μ₁ A ≤ ENNReal.ofReal M * μ₀ A) :
    unifDist ((μ₁ univ)⁻¹ • μ₁) ((μ₀ univ)⁻¹ • μ₀)
      ≤ ENNReal.ofReal (Real.log (M / m) / 4) :=
  (unifDist_normalize_le_sqrtRatio hm hmM h0top h1top h0ne hlo hhi).trans
    (ENNReal.ofReal_le_ofReal (sqrtRatio_le_log_div_four hm hmM))

/-- **The `tanh` form of the comparison bound.** `(√M − √m)/(√M + √m) = tanh (log (M/m)/4)`, so
the normalisations are at uniform distance at most `tanh (log (M/m)/4)` — strictly sharper than
`unifDist_normalize_le`, and the source of Georgii's improvement (8.10) of Proposition (8.8). -/
lemma unifDist_normalize_le_tanh {X : Type*} [MeasurableSpace X] {μ₀ μ₁ : Measure X}
    {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (h0top : μ₀ univ ≠ ⊤) (h1top : μ₁ univ ≠ ⊤) (h0ne : μ₀ univ ≠ 0)
    (hlo : ∀ A, MeasurableSet A → ENNReal.ofReal m * μ₀ A ≤ μ₁ A)
    (hhi : ∀ A, MeasurableSet A → μ₁ A ≤ ENNReal.ofReal M * μ₀ A) :
    unifDist ((μ₁ univ)⁻¹ • μ₁) ((μ₀ univ)⁻¹ • μ₀)
      ≤ ENNReal.ofReal (Real.tanh (Real.log (M / m) / 4)) := by
  rw [Real.tanh_log_div_four hm (lt_of_lt_of_le hm hmM)]
  exact unifDist_normalize_le_sqrtRatio hm hmM h0top h1top h0ne hlo hhi

end Normalize

/-! ### M2: Dobrushin's interdependence matrix (Georgii (8.5), (8.6)) -/

section Interdep

variable {γ : Specification S E} {i j : S}

lemma le_interdep {ζ η : S → E} (h : ∀ k, k ≠ j → ζ k = η k) :
    unifDist ((γ {i} ζ).map (fun ω ↦ ω i)) ((γ {i} η).map (fun ω ↦ ω i)) ≤ interdep γ i j :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

lemma interdep_le {c : ℝ≥0∞}
    (h : ∀ ζ η : S → E, (∀ k, k ≠ j → ζ k = η k) →
      unifDist ((γ {i} ζ).map (fun ω ↦ ω i)) ((γ {i} η).map (fun ω ↦ ω i)) ≤ c) :
    interdep γ i j ≤ c :=
  iSup₂_le fun ζ η ↦ iSup_le (h ζ η)

lemma interdep_le_one (γ : Specification S E) (i j : S) : interdep γ i j ≤ 1 := by
  refine interdep_le fun ζ _ _ ↦ ?_
  have : IsProbabilityMeasure ((γ {i} ζ).map (fun ω ↦ ω i)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable
  exact unifDist_le_one

lemma interdep_ne_top (γ : Specification S E) (i j : S) : interdep γ i j ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (interdep_le_one γ i j)

/-- If the single-site distribution at `i` does not depend on the spin at `j`, the corresponding
entry of Dobrushin's matrix vanishes. -/
lemma interdep_eq_zero (h : ∀ ζ η : S → E, (∀ k, k ≠ j → ζ k = η k) →
    (γ {i} ζ).map (fun ω ↦ ω i) = (γ {i} η).map (fun ω ↦ ω i)) : interdep γ i j = 0 :=
  le_antisymm (interdep_le fun ζ η hζη ↦ by rw [h ζ η hζη]; simp) bot_le

/-- The quasilocality half of Georgii (8.6). -/
lemma IsDobrushin.isQuasilocal {γ : Specification S E} (hd : IsDobrushin γ) :
    γ.IsQuasilocal := hd.1

/-- The `c(γ) < 1` half of Georgii (8.6). -/
lemma IsDobrushin.exists_lt_one {γ : Specification S E} (hd : IsDobrushin γ) :
    ∃ c : ℝ≥0∞, c < 1 ∧ ∀ i, ∑' j, interdep γ i j ≤ c := hd.2

/-- Georgii's own form of (8.6): `γ` is quasilocal and `c(γ) = sup_i ∑_j C_ij(γ) < 1`. The
second conjunct is equivalent to the existential form used in `IsDobrushin`. -/
lemma isDobrushin_iff_iSup_lt_one (γ : Specification S E) :
    IsDobrushin γ ↔ γ.IsQuasilocal ∧ ⨆ i, ∑' j, interdep γ i j < 1 := by
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨c, hc, h⟩
    exact lt_of_le_of_lt (iSup_le h) hc
  · intro h
    exact ⟨_, h, fun i ↦ le_iSup (fun i ↦ ∑' j, interdep γ i j) i⟩

end Interdep

/-! ### The diagonal of Dobrushin's matrix vanishes -/

/-- Since `γ_{i}(·|ω)` is `𝓕_{i}ᶜ`-measurable in `ω`, the diagonal entries of Dobrushin's
interdependence matrix vanish. -/
@[simp] lemma interdep_self (γ : Specification S E) (i : S) : interdep γ i i = 0 := by
  refine interdep_eq_zero fun ζ η h ↦ ?_
  have hζη : γ {i} ζ = γ {i} η := by
    refine Measure.ext fun A hA ↦ ?_
    have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((({i} : Finset S) : Set S)ᶜ)]
        (fun ω : S → E ↦ γ {i} ω A) := Kernel.measurable_coe _ hA
    exact hmeas.dependsOn_of_cylinderEvents (fun k hk ↦ h k (by simpa using hk))
  rw [hζη]

/-! ### The single-site Gibbs distributions of a potential -/

section GibbsSingleSite

variable [Countable S] {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsSummable Φ]
  (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)

/-- The unnormalised single-site distribution at `i` under the boundary condition `ζ`:
the `σ_i`-projection of `e^{-β H_{i}} · λ_{i}(·|ζ)`, over a σ-finite a priori measure. -/
def singleSiteMeasure (Φ : Potential S E) (ν : Measure E) [SigmaFinite ν] (β : ℝ)
    (i : S) (ζ : S → E) : Measure E :=
  ((Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν {i} ζ).withDensity
    (Φ.boltzmannFactor β {i})).map (fun ω ↦ ω i)

variable {ν β}

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] [NeZero ν] in
lemma singleSiteMeasure_apply (i : S) (ζ : S → E) {B : Set E} (hB : MeasurableSet B) :
    singleSiteMeasure Φ ν β i ζ B
      = ∫⁻ y in (fun ω : S → E ↦ ω i) ⁻¹' B, Φ.boltzmannFactor β {i} y
          ∂(Specification.sigmaFiniteLambdaFun (S := S) (E := E) ν {i} ζ) := by
  rw [singleSiteMeasure, Measure.map_apply (measurable_pi_apply i) hB,
    withDensity_apply _ ((measurable_pi_apply i) hB)]

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] [NeZero ν] in
lemma singleSiteMeasure_univ (i : S) (ζ : S → E) :
    singleSiteMeasure Φ ν β i ζ univ
      = Specification.sigmaFiniteLambdaZ (S := S) (E := E) ν (Φ.boltzmannFactor β) {i} ζ := by
  rw [singleSiteMeasure_apply (Φ := Φ) i ζ MeasurableSet.univ]
  simp [Specification.sigmaFiniteLambdaZ]

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] [NeZero ν] in
lemma singleSiteMeasure_univ_ne_zero
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)) (i : S) (ζ : S → E) :
    singleSiteMeasure Φ ν β i ζ univ ≠ 0 := by
  rw [singleSiteMeasure_univ]
  exact (hadm {i} ζ).1

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] [NeZero ν] in
lemma singleSiteMeasure_univ_ne_top
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)) (i : S) (ζ : S → E) :
    singleSiteMeasure Φ ν β i ζ univ ≠ ⊤ := by
  rw [singleSiteMeasure_univ]
  exact (hadm {i} ζ).2

/-- The `σ_i`-projection of the single-site Gibbs kernel is the normalisation of
`singleSiteMeasure`, over any σ-finite a priori measure. -/
lemma map_gibbsSpecification_singleton
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)) (i : S) (ζ : S → E) :
    ((Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) {i} ζ).map
        (fun ω ↦ ω i)
      = (singleSiteMeasure Φ ν β i ζ univ)⁻¹ • singleSiteMeasure Φ ν β i ζ := by
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.map_apply (measurable_pi_apply i) hB,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible_apply_set Φ ν β hadm {i} ζ
      ((measurable_pi_apply i) hB),
    Measure.smul_apply, smul_eq_mul, singleSiteMeasure_apply (Φ := Φ) i ζ hB,
    singleSiteMeasure_univ (Φ := Φ) i ζ]

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] in
/-- Comparison of Boltzmann factors from a bound on the Hamiltonian difference. -/
lemma boltzmannFactor_le_mul {Λ : Finset S} {ω₀ ω₁ : S → E} {c : ℝ}
    (h : β * (Φ.hamiltonian Λ ω₀ - Φ.hamiltonian Λ ω₁) ≤ c) :
    Φ.boltzmannFactor β Λ ω₁ ≤ ENNReal.ofReal (Real.exp c) * Φ.boltzmannFactor β Λ ω₀ := by
  rw [Potential.boltzmannFactor, Potential.boltzmannFactor,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))

omit [NeZero ν] in
/-- A uniform comparison of the single-site Boltzmann factors transfers to the unnormalised
single-site distributions. -/
lemma singleSiteMeasure_le_of_boltzmann_le {i : S} {ζ η : S → E} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hle : ∀ x : ↥({i} : Finset S) → E,
      Φ.boltzmannFactor β {i} (juxt ((({i} : Finset S) : Set S)) η x)
        ≤ C * Φ.boltzmannFactor β {i} (juxt ((({i} : Finset S) : Set S)) ζ x))
    {B : Set E} (hB : MeasurableSet B) :
    singleSiteMeasure Φ ν β i η B ≤ C * singleSiteMeasure Φ ν β i ζ B := by
  set T : Set (S → E) := (fun ω : S → E ↦ ω i) ⁻¹' B with hTdef
  have hTmeas : MeasurableSet T := (measurable_pi_apply i) hB
  have hw : Measurable (Φ.boltzmannFactor β ({i} : Finset S)) :=
    Potential.measurable_boltzmannFactor β {i}
  have key : ∀ ξ : S → E, singleSiteMeasure Φ ν β i ξ B
      = ∫⁻ x : ↥({i} : Finset S) → E, T.indicator (Φ.boltzmannFactor β {i})
          (juxt ((({i} : Finset S) : Set S)) ξ x)
        ∂(Measure.pi fun _ : ↥({i} : Finset S) ↦ ν) := by
    intro ξ
    rw [singleSiteMeasure_apply (Φ := Φ) i ξ hB, ← lintegral_indicator hTmeas,
      Specification.sigmaFiniteLambdaFun_apply_eq_map,
      lintegral_map (hw.indicator hTmeas) Measurable.juxt]
    rfl
  have hmem : ∀ (ξ : S → E) (x : ↥({i} : Finset S) → E),
      (juxt ((({i} : Finset S) : Set S)) ξ x) ∈ T ↔ x ⟨i, by simp⟩ ∈ B := by
    intro ξ x
    simp [hTdef, juxt]
  rw [key η, key ζ, ← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun x ↦ ?_
  by_cases hx : x ⟨i, by simp⟩ ∈ B
  · rw [Set.indicator_of_mem ((hmem η x).2 hx), Set.indicator_of_mem ((hmem ζ x).2 hx)]
    exact hle x
  · rw [Set.indicator_of_notMem (fun hc ↦ hx ((hmem η x).1 hc)),
      Set.indicator_of_notMem (fun hc ↦ hx ((hmem ζ x).1 hc))]
    simp

/-- **Georgii (8.8), the setwise ratio bounds**, over a σ-finite a priori measure. -/
lemma exists_singleSiteMeasure_ratio_bounds {i : S} {ζ η : S → E} {D : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ x y : ↥({i} : Finset S) → E,
      β * ((Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η x)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ x))
           - (Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η y)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ y))) ≤ D) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧ Real.log (M / m) = D ∧
      (∀ B, MeasurableSet B →
        ENNReal.ofReal m * singleSiteMeasure Φ ν β i η B ≤ singleSiteMeasure Φ ν β i ζ B) ∧
      (∀ B, MeasurableSet B →
        singleSiteMeasure Φ ν β i ζ B ≤ ENNReal.ofReal M * singleSiteMeasure Φ ν β i η B) := by
  have hEne : Nonempty E := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    refine NeZero.ne ν (Measure.measure_univ_eq_zero.1 ?_)
    rw [Set.univ_eq_empty_iff.2 hcon]
    exact measure_empty
  have hne : Nonempty (↥({i} : Finset S) → E) := inferInstance
  set v : (↥({i} : Finset S) → E) → ℝ :=
    fun x ↦ β * (Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η x)
      - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ x)) with hvdef
  have hoscv : ∀ x y, v x - v y ≤ D := by
    intro x y
    have := hosc x y
    rw [hvdef]
    simp only
    nlinarith [this]
  obtain ⟨x₀⟩ := hne
  have hbdd : BddAbove (Set.range v) := by
    refine ⟨v x₀ + D, ?_⟩
    rintro _ ⟨y, rfl⟩
    linarith [hoscv y x₀]
  set c₀ : ℝ := sSup (Set.range v) with hc₀def
  have hle_c₀ : ∀ x, v x ≤ c₀ := fun x ↦ le_csSup hbdd ⟨x, rfl⟩
  have hc₀_le : ∀ x, c₀ ≤ v x + D := by
    intro x
    refine csSup_le (Set.range_nonempty v) ?_
    rintro _ ⟨y, rfl⟩
    linarith [hoscv y x]
  set M : ℝ := Real.exp c₀ with hMdef
  set m : ℝ := Real.exp (c₀ - D) with hmdef
  have hm : 0 < m := Real.exp_pos _
  have hmM : m ≤ M := Real.exp_le_exp.2 (by linarith)
  have hlogMm : Real.log (M / m) = D := by
    rw [hMdef, hmdef, ← Real.exp_sub, Real.log_exp]; ring
  have hhi : ∀ x : ↥({i} : Finset S) → E,
      Φ.boltzmannFactor β {i} (juxt ((({i} : Finset S) : Set S)) ζ x)
        ≤ ENNReal.ofReal M * Φ.boltzmannFactor β {i}
            (juxt ((({i} : Finset S) : Set S)) η x) :=
    fun x ↦ boltzmannFactor_le_mul (hle_c₀ x)
  have hlo' : ∀ x : ↥({i} : Finset S) → E,
      Φ.boltzmannFactor β {i} (juxt ((({i} : Finset S) : Set S)) η x)
        ≤ ENNReal.ofReal (Real.exp (D - c₀)) * Φ.boltzmannFactor β {i}
            (juxt ((({i} : Finset S) : Set S)) ζ x) := by
    intro x
    refine boltzmannFactor_le_mul ?_
    have := hc₀_le x
    rw [hvdef] at this
    simp only at this
    nlinarith [this]
  set μ₀ : Measure E := singleSiteMeasure Φ ν β i η with hμ₀
  set μ₁ : Measure E := singleSiteMeasure Φ ν β i ζ with hμ₁
  have hset_hi : ∀ B, MeasurableSet B → μ₁ B ≤ ENNReal.ofReal M * μ₀ B :=
    fun B hB ↦ singleSiteMeasure_le_of_boltzmann_le ENNReal.ofReal_ne_top hhi hB
  have hset_lo : ∀ B, MeasurableSet B → ENNReal.ofReal m * μ₀ B ≤ μ₁ B := by
    intro B hB
    have h1 : μ₀ B ≤ ENNReal.ofReal (Real.exp (D - c₀)) * μ₁ B :=
      singleSiteMeasure_le_of_boltzmann_le ENNReal.ofReal_ne_top hlo' hB
    calc ENNReal.ofReal m * μ₀ B
        ≤ ENNReal.ofReal m * (ENNReal.ofReal (Real.exp (D - c₀)) * μ₁ B) := by gcongr
      _ = μ₁ B := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show c₀ - D + (D - c₀) = 0 by ring, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  exact ⟨m, M, hm, hmM, hlogMm, hset_lo, hset_hi⟩

/-- **Georgii (8.8), key estimate, sharp form, over a σ-finite a priori measure.** -/
lemma unifDist_map_gibbsSpecification_le_tanh
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β))
    {i : S} {ζ η : S → E} {D : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ x y : ↥({i} : Finset S) → E,
      β * ((Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η x)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ x))
           - (Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η y)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ y))) ≤ D) :
    unifDist
        ((Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm {i} ζ).map
          (fun ω ↦ ω i))
        ((Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm {i} η).map
          (fun ω ↦ ω i))
      ≤ ENNReal.ofReal (Real.tanh (D / 4)) := by
  obtain ⟨m, M, hm, hmM, hlogMm, hset_lo, hset_hi⟩ :=
    exists_singleSiteMeasure_ratio_bounds (Φ := Φ) (ν := ν) (β := β) hD hosc
  have hkey := unifDist_normalize_le_tanh
    (μ₀ := singleSiteMeasure Φ ν β i η) (μ₁ := singleSiteMeasure Φ ν β i ζ) hm hmM
    (singleSiteMeasure_univ_ne_top (Φ := Φ) hadm i η)
    (singleSiteMeasure_univ_ne_top (Φ := Φ) hadm i ζ)
    (singleSiteMeasure_univ_ne_zero (Φ := Φ) hadm i η) hset_lo hset_hi
  rw [hlogMm] at hkey
  rwa [map_gibbsSpecification_singleton (Φ := Φ) hadm i ζ,
    map_gibbsSpecification_singleton (Φ := Φ) hadm i η]

/-- **Georgii (8.8), key estimate**, over a σ-finite a priori measure. -/
lemma unifDist_map_gibbsSpecification_le
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β))
    {i : S} {ζ η : S → E} {D : ℝ} (hD : 0 ≤ D)
    (hosc : ∀ x y : ↥({i} : Finset S) → E,
      β * ((Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η x)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ x))
           - (Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η y)
              - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ y))) ≤ D) :
    unifDist
        ((Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm {i} ζ).map
          (fun ω ↦ ω i))
        ((Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm {i} η).map
          (fun ω ↦ ω i))
      ≤ ENNReal.ofReal (D / 4) :=
  (unifDist_map_gibbsSpecification_le_tanh hadm hD hosc).trans
    (ENNReal.ofReal_le_ofReal (tanh_le_self (by linarith)))

omit [Countable S] [Potential.IsPotential Φ] [Potential.IsSummable Φ] [NeZero ν] in
/-- With `β = 0` the single-site distributions do not see the boundary condition. -/
lemma singleSiteMeasure_zero_eq (i : S) (ζ η : S → E) :
    singleSiteMeasure Φ ν 0 i ζ = singleSiteMeasure Φ ν 0 i η := by
  have hbf : Φ.boltzmannFactor 0 ({i} : Finset S) = 1 := by
    funext x
    simp [Potential.boltzmannFactor]
  have hmap : ∀ ξ : S → E, singleSiteMeasure Φ ν 0 i ξ
      = (Measure.pi fun _ : ↥({i} : Finset S) ↦ ν).map
          (fun x ↦ x ⟨i, Finset.mem_singleton_self i⟩) := by
    intro ξ
    rw [singleSiteMeasure, hbf, withDensity_one,
      Specification.sigmaFiniteLambdaFun_apply_eq_map,
      Measure.map_map (measurable_pi_apply i) Measurable.juxt]
    congr 1
    funext x
    simp [Function.comp, juxt]
  rw [hmap ζ, hmap η]

end GibbsSingleSite


/-! ### Oscillations of the interaction terms (Georgii (8.2)) -/

section Osc

omit [MeasurableSpace E] in
lemma osc_le_two_mul_iSup (f : (S → E) → ℝ) : osc f ≤ 2 * ⨆ ζ, ‖f ζ‖ₑ := by
  refine osc_le fun ζ η ↦ ?_
  have habs : |f ζ - f η| ≤ |f ζ| + |f η| := by
    rw [abs_le]
    constructor <;>
      linarith [le_abs_self (f ζ), neg_abs_le (f ζ), le_abs_self (f η), neg_abs_le (f η)]
  have h1 : ENNReal.ofReal |f ζ - f η| ≤ ‖f ζ‖ₑ + ‖f η‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal habs
  refine h1.trans ?_
  calc ‖f ζ‖ₑ + ‖f η‖ₑ ≤ (⨆ ξ, ‖f ξ‖ₑ) + (⨆ ξ, ‖f ξ‖ₑ) :=
        add_le_add (le_iSup (fun ξ ↦ ‖f ξ‖ₑ) ζ) (le_iSup (fun ξ ↦ ‖f ξ‖ₑ) η)
    _ = 2 * ⨆ ξ, ‖f ξ‖ₑ := (two_mul _).symm

/-- Georgii (8.8): `∑_{A ⊇ {i,j}} δ(Φ_A)`. -/
def pairStrength (Φ : Potential S E) (i j : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {A : Finset S | i ∈ A ∧ j ∈ A}.indicator (fun A ↦ osc (Φ A)) A

/-- Georgii (8.8): `∑_{A ∋ i} (|A| − 1) δ(Φ_A)`, the interaction strength at the site `i`. -/
def interactionStrength (Φ : Potential S E) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | i ∈ A}.indicator (fun A ↦ ((A.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ A)) A

lemma pairStrength_le (Φ : Potential S E) (i j : S) : pairStrength Φ i j ≤ 2 * Φ.normAt i := by
  rw [pairStrength, Potential.normAt, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun A ↦ ?_
  by_cases h : i ∈ A ∧ j ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A ∧ j ∈ A} from h),
      Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h.1)]
    exact osc_le_two_mul_iSup _
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A ∧ j ∈ A} from h)]
    exact bot_le

lemma pairStrength_ne_top (Φ : Potential S E) [Potential.IsAbsolutelySummable Φ] (i j : S) :
    pairStrength Φ i j ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (pairStrength_le Φ i j)
  exact ENNReal.mul_ne_top (by norm_num) (Potential.IsAbsolutelySummable.normAt_ne_top i)

end Osc

/-! ### The oscillation of the single-site Hamiltonian difference (Georgii (8.8)) -/

section HamiltonianOsc

variable {Φ : Potential S E}

/-! ### Hamiltonian differences as unconditional sums -/

/-- If the term differences of two boundary conditions are unconditionally summable, the
difference of the (volume-limit) Hamiltonians is their unconditional sum. -/
lemma _root_.Potential.hamiltonian_sub_eq_tsum [Potential.IsSummable Φ] {Λ : Finset S}
    {ζ η : S → E}
    (hsum : Summable fun A ↦ Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A) :
    Φ.hamiltonian Λ ζ - Φ.hamiltonian Λ η
      = ∑' A, (Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A) := by
  have h1 : HasSum (fun A ↦ Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A)
      (Φ.hamiltonian Λ ζ - Φ.hamiltonian Λ η) (SummationFilter.volume S) :=
    (Potential.hasSum_hamiltonian Λ ζ).sub (Potential.hasSum_hamiltonian Λ η)
  exact (hsum.hasSum.volume.unique h1).symm

/-- **Georgii (8.8): the interaction terms felt by a boundary flip at `j`.** For boundary
conditions agreeing off `j`, only the terms whose support contains both `i` and `j` contribute to
the difference of `H_{i}`-terms, and each contributes at most the oscillation of its
interaction. -/
lemma enorm_hamiltonianTerms_sub_le [Potential.IsPotential Φ] {i j : S} {ζ η : S → E}
    (hζη : ∀ k, k ≠ j → ζ k = η k) (A : Finset S) :
    ‖Φ.hamiltonianTerms {i} ζ A - Φ.hamiltonianTerms {i} η A‖ₑ
      ≤ {A : Finset S | i ∈ A ∧ j ∈ A}.indicator (fun A ↦ osc (Φ A)) A := by
  by_cases hiA : i ∈ A
  · have hnd : ¬ Disjoint A ({i} : Finset S) :=
      Finset.not_disjoint_iff.2 ⟨i, hiA, Finset.mem_singleton_self i⟩
    rw [Potential.hamiltonianTerms_of_not_disjoint hnd,
      Potential.hamiltonianTerms_of_not_disjoint hnd]
    by_cases hjA : j ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A ∧ j ∈ A} from ⟨hiA, hjA⟩),
        Real.enorm_eq_ofReal_abs]
      exact le_osc _ _ _
    · have heq : Φ A ζ = Φ A η :=
        Potential.IsPotential.eq_of_eqOn fun k hk ↦ hζη k fun hkj ↦ hjA (hkj ▸ hk)
      simp [heq]
  · have hd : Disjoint A ({i} : Finset S) := Finset.disjoint_singleton_right.2 hiA
    rw [Potential.hamiltonianTerms_of_disjoint hd, Potential.hamiltonianTerms_of_disjoint hd]
    simp

/-- **Georgii (8.8), the estimate `δ(v) ≤ 2 ∑_{A ⊇ {i,j}} δ(Φ_A)`.** The second difference of
`H_{i}` between boundary conditions that agree off `j` only sees the interaction terms
containing both `i` and `j`.

Unlike the corresponding estimate for an absolutely summable potential, only `IsSummable` — the
convergence (2.2)(ii) of the Hamiltonian series — and finiteness of the pair strength
`∑_{A ⊇ {i,j}} δ(Φ_A)` are needed: the *difference* series is absolutely summable even when the
Hamiltonian series is not. -/
lemma enorm_hamiltonian_second_diff_le [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    {i j : S} (hP : pairStrength Φ i j ≠ ⊤) {ω₁ ω₂ ω₃ ω₄ : S → E}
    (h12 : ∀ k, k ≠ j → ω₁ k = ω₂ k) (h34 : ∀ k, k ≠ j → ω₃ k = ω₄ k) :
    ‖(Φ.hamiltonian {i} ω₁ - Φ.hamiltonian {i} ω₂)
       - (Φ.hamiltonian {i} ω₃ - Φ.hamiltonian {i} ω₄)‖ₑ ≤ 2 * pairStrength Φ i j := by
  classical
  set d₁₂ : Finset S → ℝ :=
    fun A ↦ Φ.hamiltonianTerms {i} ω₁ A - Φ.hamiltonianTerms {i} ω₂ A with hd₁₂
  set d₃₄ : Finset S → ℝ :=
    fun A ↦ Φ.hamiltonianTerms {i} ω₃ A - Φ.hamiltonianTerms {i} ω₄ A with hd₃₄
  have hb₁₂ : ∀ A, ‖d₁₂ A‖ₑ ≤ {A : Finset S | i ∈ A ∧ j ∈ A}.indicator (fun A ↦ osc (Φ A)) A :=
    enorm_hamiltonianTerms_sub_le h12
  have hb₃₄ : ∀ A, ‖d₃₄ A‖ₑ ≤ {A : Finset S | i ∈ A ∧ j ∈ A}.indicator (fun A ↦ osc (Φ A)) A :=
    enorm_hamiltonianTerms_sub_le h34
  have htsum₁₂ : ∑' A, ‖d₁₂ A‖ₑ ≤ pairStrength Φ i j := ENNReal.tsum_le_tsum hb₁₂
  have htsum₃₄ : ∑' A, ‖d₃₄ A‖ₑ ≤ pairStrength Φ i j := ENNReal.tsum_le_tsum hb₃₄
  have hs₁₂ : Summable d₁₂ := Summable.of_enorm (ne_top_of_le_ne_top hP htsum₁₂)
  have hs₃₄ : Summable d₃₄ := Summable.of_enorm (ne_top_of_le_ne_top hP htsum₃₄)
  rw [Potential.hamiltonian_sub_eq_tsum hs₁₂, Potential.hamiltonian_sub_eq_tsum hs₃₄,
    ← hs₁₂.tsum_sub hs₃₄]
  refine le_trans enorm_tsum_le_tsum_enorm ?_
  calc ∑' A, ‖d₁₂ A - d₃₄ A‖ₑ
      ≤ ∑' A, (‖d₁₂ A‖ₑ + ‖d₃₄ A‖ₑ) := by
        refine ENNReal.tsum_le_tsum fun A ↦ ?_
        rw [sub_eq_add_neg]
        exact le_trans (enorm_add_le _ _) (by rw [enorm_neg])
    _ = (∑' A, ‖d₁₂ A‖ₑ) + ∑' A, ‖d₃₄ A‖ₑ := ENNReal.tsum_add
    _ ≤ pairStrength Φ i j + pairStrength Φ i j := add_le_add htsum₁₂ htsum₃₄
    _ = 2 * pairStrength Φ i j := (two_mul _).symm

/-! ### Quasilocality of the Hamiltonians (Georgii's first step in the proof of (8.8)) -/

/-- **Georgii, proof of (8.8), first step.** If the interaction strengths
`∑_{A ∋ i} (|A| − 1) δ(Φ_A)` at the sites of `Λ` are finite, the Hamiltonian `H_Λ` is quasilocal:
`sup_{ζ_Δ = η_Δ} |H_Λ(ζ) − H_Λ(η)| ≤ ∑_{i ∈ Λ} ∑_{A ∋ i, A ⊄ Δ} δ(Φ_A) → 0` as `Δ ↑ S`. The
single-site terms drop out of the tail — the sum over `A ∋ i`, `A ⊄ Δ ⊇ Λ` sees only supports of
at least two points — so, as Georgii remarks, the self-potential is unconstrained. -/
theorem isQuasilocalFun_hamiltonian [Potential.IsPotential Φ] [Potential.IsSummable Φ]
    {Λ : Finset S} (hIS : ∀ i ∈ Λ, interactionStrength Φ i ≠ ⊤) :
    IsQuasilocalFun (Φ.hamiltonian Λ) := by
  classical
  intro ε hε
  set ε₀ : ℝ≥0∞ := ENNReal.ofReal ε / (Λ.card + 1) with hε₀
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]
    exact ENNReal.div_pos (by simpa using hε) (by simp)
  -- for each site, a finite family of supports carrying all but `ε₀` of the interaction strength
  have hchoice : ∀ i ∈ Λ, ∃ s : Finset (Finset S),
      ∑' A : {A : Finset S // A ∉ s},
        {B : Finset S | i ∈ B}.indicator
          (fun B ↦ ((B.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ B)) A.1 ≤ ε₀ := by
    intro i hi
    have hne : ∑' A : Finset S, {B : Finset S | i ∈ B}.indicator
        (fun B ↦ ((B.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ B)) A ≠ ⊤ := by
      have hval : ∑' A : Finset S, {B : Finset S | i ∈ B}.indicator
          (fun B ↦ ((B.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ B)) A = interactionStrength Φ i := rfl
      rw [hval]
      exact hIS i hi
    have htail := ENNReal.tendsto_tsum_compl_atTop_zero hne
    exact ((ENNReal.tendsto_nhds_zero.1 htail) ε₀ hε₀pos).exists
  choose! s hs using hchoice
  set Δ : Finset S := Λ ∪ Λ.attach.biUnion (fun i ↦ (s i.1).biUnion id) with hΔdef
  have hΛΔ : Λ ⊆ Δ := Finset.subset_union_left
  have hsΔ : ∀ i ∈ Λ, ∀ A ∈ s i, A ⊆ Δ := by
    intro i hi A hA x hx
    refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, ?_⟩)
    exact Finset.mem_biUnion.2 ⟨A, hA, hx⟩
  refine ⟨Δ, fun ζ η hagree ↦ ?_⟩
  -- the surviving interaction terms
  have hbd : ∀ A : Finset S, ‖Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A‖ₑ
      ≤ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A := by
    intro A
    by_cases hdisj : Disjoint A Λ
    · simp [Potential.hamiltonianTerms_of_disjoint hdisj]
    · rw [Potential.hamiltonianTerms_of_not_disjoint hdisj,
        Potential.hamiltonianTerms_of_not_disjoint hdisj]
      by_cases hAΔ : A ⊆ Δ
      · have heq : Φ A ζ = Φ A η :=
          Potential.IsPotential.eq_of_eqOn fun k hk ↦ hagree k (hAΔ hk)
        simp [heq]
      · rw [Set.indicator_of_mem
          (show A ∈ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ} from ⟨hdisj, hAΔ⟩),
          Real.enorm_eq_ofReal_abs]
        exact le_osc _ _ _
  -- one site of `Λ` witnesses each surviving support
  have hGle : ∀ A : Finset S,
      {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A
        ≤ ∑ i ∈ Λ, {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A := by
    intro A
    by_cases hA : A ∈ {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}
    · rw [Set.indicator_of_mem hA]
      obtain ⟨k, hkA, hkΛ⟩ := Finset.not_disjoint_iff.1 hA.1
      calc osc (Φ A)
          = {B : Finset S | k ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A := by
            rw [Set.indicator_of_mem
              (show A ∈ {B : Finset S | k ∈ B ∧ ¬ B ⊆ Δ} from ⟨hkA, hA.2⟩)]
        _ ≤ ∑ i ∈ Λ, {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A :=
            Finset.single_le_sum
              (f := fun i ↦ {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A)
              (fun _ _ ↦ bot_le) hkΛ
    · rw [Set.indicator_of_notMem hA]
      exact bot_le
  -- each site's tail lies beyond its chosen finite family
  have hinner : ∀ i ∈ Λ,
      ∑' A, {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A ≤ ε₀ := by
    intro i hi
    have hsupp : Function.support
        (fun A ↦ {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A)
          ⊆ {A : Finset S | A ∉ s i} := by
      intro A hA
      rw [Function.mem_support] at hA
      by_contra hmem
      rw [Set.mem_ofPred_eq, not_not] at hmem
      refine hA (Set.indicator_of_notMem ?_ _)
      rintro ⟨-, hAΔ⟩
      exact hAΔ (hsΔ i hi A hmem)
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine le_trans (ENNReal.tsum_le_tsum fun A ↦ ?_) (hs i hi)
    by_cases hmem : A.1 ∈ {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}
    · rw [Set.indicator_of_mem hmem,
        Set.indicator_of_mem (show A.1 ∈ {B : Finset S | i ∈ B} from hmem.1)]
      obtain ⟨k, hkA, hkΔ⟩ := Finset.not_subset.1 hmem.2
      have hki : k ≠ i := fun h ↦ hkΔ (h ▸ hΛΔ hi)
      have h1 : (1 : ℝ≥0∞) ≤ ((A.1.card - 1 : ℕ) : ℝ≥0∞) := by
        have hcard : 1 < A.1.card := Finset.one_lt_card.2 ⟨i, hmem.1, k, hkA, hki.symm⟩
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (by omega)
      calc osc (Φ A.1) = 1 * osc (Φ A.1) := (one_mul _).symm
        _ ≤ ((A.1.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ A.1) := mul_le_mul' h1 le_rfl
    · rw [Set.indicator_of_notMem hmem]
      exact bot_le
  -- total tail bound
  have htotal : ∑' A, ‖Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A‖ₑ
      ≤ ENNReal.ofReal ε := by
    calc ∑' A, ‖Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A‖ₑ
        ≤ ∑' A, {B : Finset S | ¬ Disjoint B Λ ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A :=
          ENNReal.tsum_le_tsum hbd
      _ ≤ ∑' A, ∑ i ∈ Λ, {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A :=
          ENNReal.tsum_le_tsum hGle
      _ = ∑ i ∈ Λ, ∑' A, {B : Finset S | i ∈ B ∧ ¬ B ⊆ Δ}.indicator (fun B ↦ osc (Φ B)) A :=
          Summable.tsum_finsetSum fun i _ ↦ ENNReal.summable
      _ ≤ ∑ _i ∈ Λ, ε₀ := Finset.sum_le_sum hinner
      _ = Λ.card * ε₀ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Λ.card + 1) * ε₀ := mul_le_mul' (by simp) le_rfl
      _ = ENNReal.ofReal ε := by
          rw [hε₀]
          exact ENNReal.mul_div_cancel (by simp) (by simp)
  have hsum : Summable fun A ↦ Φ.hamiltonianTerms Λ ζ A - Φ.hamiltonianTerms Λ η A :=
    Summable.of_enorm (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htotal)
  have habs : ENNReal.ofReal |Φ.hamiltonian Λ ζ - Φ.hamiltonian Λ η| ≤ ENNReal.ofReal ε := by
    rw [Potential.hamiltonian_sub_eq_tsum hsum, ← Real.enorm_eq_ofReal_abs]
    exact le_trans enorm_tsum_le_tsum_enorm htotal
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 habs

end HamiltonianOsc


/-! ### M3: Georgii's Proposition (8.8) -/

section Prop88

variable [Countable S] {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsSummable Φ]
  (ν : Measure E) [SigmaFinite ν] [NeZero ν] (β : ℝ)

omit [Countable S] in
/-- The second difference of the single-site Hamiltonian between two boundary conditions
agreeing off `j` is bounded by `|β| · 2 · ∑_{A ⊇ {i,j}} δ(Φ_A)`. -/
lemma hamiltonian_singleSite_second_diff_le {i j : S} (hP : pairStrength Φ i j ≠ ⊤)
    {ζ η : S → E} (hζη : ∀ k, k ≠ j → ζ k = η k) (x y : ↥({i} : Finset S) → E) :
    β * ((Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η x)
            - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ x))
         - (Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) η y)
            - Φ.hamiltonian {i} (juxt ((({i} : Finset S) : Set S)) ζ y)))
      ≤ |β| * 2 * (pairStrength Φ i j).toReal := by
  set P := pairStrength Φ i j with hPdef
  set D : ℝ := |β| * 2 * P.toReal with hDdef
  set ω₁ := juxt ((({i} : Finset S) : Set S)) η x with hω₁
  set ω₂ := juxt ((({i} : Finset S) : Set S)) ζ x with hω₂
  set ω₃ := juxt ((({i} : Finset S) : Set S)) η y with hω₃
  set ω₄ := juxt ((({i} : Finset S) : Set S)) ζ y with hω₄
  have hagree : ∀ (ξ₁ ξ₂ : S → E) (z : ↥({i} : Finset S) → E), (∀ k, k ≠ j → ξ₁ k = ξ₂ k) →
      ∀ k, k ≠ j → juxt ((({i} : Finset S) : Set S)) ξ₁ z k
        = juxt ((({i} : Finset S) : Set S)) ξ₂ z k := by
    intro ξ₁ ξ₂ z hξ k hk
    by_cases hki : k ∈ ((({i} : Finset S) : Set S))
    · rw [juxt_apply_of_mem hki z, juxt_apply_of_mem hki z]
    · rw [juxt_apply_of_not_mem hki z, juxt_apply_of_not_mem hki z]
      exact hξ k hk
  have h12 : ∀ k, k ≠ j → ω₁ k = ω₂ k := hagree η ζ x fun k hk ↦ (hζη k hk).symm
  have h34 : ∀ k, k ≠ j → ω₃ k = ω₄ k := hagree η ζ y fun k hk ↦ (hζη k hk).symm
  have hbound := enorm_hamiltonian_second_diff_le (Φ := Φ) (i := i) (j := j) hP h12 h34
  rw [Real.enorm_eq_ofReal_abs] at hbound
  have h2P : (2 : ℝ≥0∞) * P ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hP
  have hΔ : |(Φ.hamiltonian {i} ω₁ - Φ.hamiltonian {i} ω₂)
      - (Φ.hamiltonian {i} ω₃ - Φ.hamiltonian {i} ω₄)| ≤ 2 * P.toReal := by
    have h := ENNReal.toReal_mono h2P hbound
    rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
      show ((2 : ℝ≥0∞)).toReal = 2 by norm_num] at h
  calc β * ((Φ.hamiltonian {i} ω₁ - Φ.hamiltonian {i} ω₂)
        - (Φ.hamiltonian {i} ω₃ - Φ.hamiltonian {i} ω₄))
      ≤ |β * ((Φ.hamiltonian {i} ω₁ - Φ.hamiltonian {i} ω₂)
          - (Φ.hamiltonian {i} ω₃ - Φ.hamiltonian {i} ω₄))| := le_abs_self _
    _ = |β| * |(Φ.hamiltonian {i} ω₁ - Φ.hamiltonian {i} ω₂)
          - (Φ.hamiltonian {i} ω₃ - Φ.hamiltonian {i} ω₄)| := abs_mul _ _
    _ ≤ |β| * (2 * P.toReal) := mul_le_mul_of_nonneg_left hΔ (abs_nonneg β)
    _ = D := by rw [hDdef]; ring

variable {ν β}

/-- **Georgii (8.8), entrywise, over a σ-finite a priori measure.** -/
theorem interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)) (i j : S) :
    interdep (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) i j
      ≤ ENNReal.ofReal |β| * pairStrength Φ i j / 2 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [interdep_self]
    exact bot_le
  rcases eq_or_ne β 0 with rfl | hβ
  · have hzero : interdep
        (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν 0 hadm) i j = 0 := by
      refine interdep_eq_zero fun ζ η h ↦ ?_
      rw [map_gibbsSpecification_singleton (Φ := Φ) hadm i ζ,
        map_gibbsSpecification_singleton (Φ := Φ) hadm i η,
        singleSiteMeasure_zero_eq (Φ := Φ) (ν := ν) i ζ η]
    rw [hzero]
    exact bot_le
  rcases eq_or_ne (pairStrength Φ i j) ⊤ with hP | hP
  · have hval : ENNReal.ofReal |β| * pairStrength Φ i j / 2 = ⊤ := by
      rw [hP, ENNReal.mul_top (by simpa [abs_pos] using hβ)]
      exact ENNReal.top_div_of_ne_top (by simp)
    exact hval ▸ le_top
  · set P := pairStrength Φ i j with hPdef
    have hD0 : 0 ≤ |β| * 2 * P.toReal := by positivity
    have hrhs : ENNReal.ofReal (|β| * 2 * P.toReal / 4) = ENNReal.ofReal |β| * P / 2 := by
      rw [show |β| * 2 * P.toReal / 4 = |β| * P.toReal / 2 by ring,
        ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul (abs_nonneg β),
        ENNReal.ofReal_toReal hP]
      norm_num
    rw [← hrhs]
    exact interdep_le fun ζ η hζη ↦ unifDist_map_gibbsSpecification_le hadm hD0
      fun x y ↦ hamiltonian_singleSite_second_diff_le β hP hζη x y

/-- **Georgii, Example (8.9)(2), entrywise, over a σ-finite a priori measure.** -/
theorem interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le_tanh
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β)) {i j : S} (hP : pairStrength Φ i j ≠ ⊤) :
    interdep (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) i j
      ≤ ENNReal.ofReal (Real.tanh (|β| * (pairStrength Φ i j).toReal / 2)) := by
  set P := pairStrength Φ i j with hPdef
  have hD0 : 0 ≤ |β| * 2 * P.toReal := by positivity
  have hquarter : |β| * 2 * P.toReal / 4 = |β| * P.toReal / 2 := by ring
  rw [← hquarter]
  exact interdep_le fun ζ η hζη ↦ unifDist_map_gibbsSpecification_le_tanh hadm hD0
    fun x y ↦ hamiltonian_singleSite_second_diff_le β hP hζη x y

end Prop88

section Prop88Prob

variable [Countable S] {Φ : Potential S E} [Potential.IsPotential Φ]
  [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii (8.8), entrywise.** `C_ij(γ^{βΦ}) ≤ |β|/2 · ∑_{A ⊇ {i,j}} δ(Φ_A)`; the
probability/absolutely-summable special case of
`Dobrushin.interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le`. -/
theorem interdep_gibbsSpecification_le (i j : S) :
    interdep (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) i j
      ≤ ENNReal.ofReal |β| * pairStrength Φ i j / 2 := by
  rw [← Potential.gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Φ) ν β]
  exact interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le (Φ := Φ) _ i j

/-- **Georgii, Example (8.9)(2), general form.** The sharp reading of the pair bound:
`C_ij(γ^Φ) ≤ tanh (|β| ∑_{A ⊇ {i,j}} δ(Φ_A) / 2)`. Georgii derives the `tanh` improvement only
for two-point spin spaces; it holds over an arbitrary state space. -/
theorem interdep_gibbsSpecification_le_tanh (i j : S) :
    interdep (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) i j
      ≤ ENNReal.ofReal (Real.tanh (|β| * (pairStrength Φ i j).toReal / 2)) := by
  rw [← Potential.gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Φ) ν β]
  exact interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le_tanh (Φ := Φ) _
    (pairStrength_ne_top Φ i j)

end Prop88Prob

/-- Georgii (8.8): `∑_{j ≠ i} ∑_{A ⊇ {i,j}} δ(Φ_A) = ∑_{A ∋ i} (|A| − 1) δ(Φ_A)`. -/
lemma tsum_pairStrength (Φ : Potential S E) (i : S) :
    ∑' j : S, {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j
      = interactionStrength Φ i := by
  classical
  set F : S → Finset S → ℝ≥0∞ :=
    fun j A ↦ if j ≠ i ∧ i ∈ A ∧ j ∈ A then osc (Φ A) else 0 with hF
  have hstep1 : ∀ j : S, ∑' A : Finset S, F j A
      = {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp)]
      simp [hF]
    · rw [Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj), pairStrength]
      refine tsum_congr fun A ↦ ?_
      by_cases hA : i ∈ A ∧ j ∈ A
      · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A ∧ j ∈ A} from hA)]
        simp only [hF]
        exact ite_eq_left ⟨hj, hA⟩
      · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A ∧ j ∈ A} from hA)]
        simp only [hF]
        exact ite_eq_right (by tauto)
  have hstep2 : ∀ A : Finset S, ∑' j : S, F j A
      = {A : Finset S | i ∈ A}.indicator
          (fun A ↦ ((A.card - 1 : ℕ) : ℝ≥0∞) * osc (Φ A)) A := by
    intro A
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
      have hsupp : ∀ j ∉ A.erase i, F j A = 0 := by
        intro j hj
        rw [Finset.mem_erase] at hj
        simp only [hF]
        exact ite_eq_right (by tauto)
      have hval : ∀ j ∈ A.erase i, F j A = osc (Φ A) := by
        intro j hj
        rw [Finset.mem_erase] at hj
        simp only [hF]
        exact ite_eq_left ⟨hj.1, hiA, hj.2⟩
      rw [tsum_eq_sum hsupp, Finset.sum_congr rfl hval, Finset.sum_const,
        Finset.card_erase_of_mem hiA, nsmul_eq_mul]
    · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA)]
      have : ∀ j : S, F j A = 0 := fun j ↦ by simp only [hF]; exact ite_eq_right (by tauto)
      simp [this]
  rw [interactionStrength]
  calc ∑' j : S, {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j
      = ∑' j : S, ∑' A : Finset S, F j A := tsum_congr fun j ↦ (hstep1 j).symm
    _ = ∑' A : Finset S, ∑' j : S, F j A := ENNReal.tsum_comm
    _ = _ := tsum_congr hstep2

section Prop88b

variable [Countable S] {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsSummable Φ]
  {ν : Measure E} [SigmaFinite ν] [NeZero ν] {β : ℝ}

/-- **Georgii, Proposition (8.8), at Georgii's hypotheses.** For a σ-finite non-zero a priori
measure `λ` and a `λ`-admissible potential with
`sup_i |β| ∑_{A ∋ i} (|A| − 1) δ(Φ_A) < 2`, the Gibbsian specification of `βΦ` satisfies
Dobrushin's condition of weak dependence. -/
theorem isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β))
    {c : ℝ≥0∞} (hc : c < 2)
    (hΦ : ∀ i, ENNReal.ofReal |β| * interactionStrength Φ i ≤ c) :
    IsDobrushin (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) := by
  have hql : ∀ Λ : Finset S, IsQuasilocalFun fun η : S → E ↦ β * Φ.hamiltonian Λ η := by
    intro Λ
    rcases eq_or_ne β 0 with rfl | hβ
    · intro ε hε
      exact ⟨∅, fun ζ η _ ↦ by simpa using hε.le⟩
    · have hIS : ∀ i ∈ Λ, interactionStrength Φ i ≠ ⊤ := by
        intro i _ htop
        have h1 := hΦ i
        rw [htop, ENNReal.mul_top (by simpa [abs_pos] using hβ)] at h1
        exact absurd (lt_of_le_of_lt h1 hc) (by simp)
      exact (isQuasilocalFun_hamiltonian hIS).const_mul β
  refine ⟨Potential.isQuasilocal_gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm hql,
    c / 2, ?_, fun i ↦ ?_⟩
  · rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul]
    exact hc
  · set γ := Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm with hγ
    have hzero : ∀ j : S, interdep γ i j
        = {j : S | j ≠ i}.indicator (fun j ↦ interdep γ i j) j := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp), interdep_self]
      · rw [Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj)]
    have hstep : ∀ j : S, {j : S | j ≠ i}.indicator (fun j ↦ interdep γ i j) j
        ≤ (ENNReal.ofReal |β| / 2)
          * {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp),
          Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp)]
        simp
      · rw [Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj),
          Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj)]
        have h := interdep_gibbsSpecificationOfSigmaFiniteAdmissible_le (Φ := Φ) hadm i j
        rwa [show ENNReal.ofReal |β| * pairStrength Φ i j / 2
            = ENNReal.ofReal |β| / 2 * pairStrength Φ i j by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring] at h
    calc ∑' j : S, interdep γ i j
        = ∑' j : S, {j : S | j ≠ i}.indicator (fun j ↦ interdep γ i j) j := tsum_congr hzero
      _ ≤ ∑' j : S, (ENNReal.ofReal |β| / 2)
            * {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j :=
          ENNReal.tsum_le_tsum hstep
      _ = (ENNReal.ofReal |β| / 2)
            * ∑' j : S, {j : S | j ≠ i}.indicator (fun j ↦ pairStrength Φ i j) j :=
          ENNReal.tsum_mul_left
      _ = (ENNReal.ofReal |β| / 2) * interactionStrength Φ i := by rw [tsum_pairStrength]
      _ = ENNReal.ofReal |β| * interactionStrength Φ i / 2 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ c / 2 := by gcongr; exact hΦ i

/-- **Georgii, Proposition (8.8)** in Georgii's own `sup`-form, over a σ-finite a priori
measure. -/
theorem isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible_of_iSup_lt
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν
      (Φ.boltzmannFactor β))
    (h : ⨆ i, ENNReal.ofReal |β| * interactionStrength Φ i < 2) :
    IsDobrushin (Potential.gibbsSpecificationOfSigmaFiniteAdmissible Φ ν β hadm) :=
  isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible hadm h
    fun i ↦ le_iSup (fun i ↦ ENNReal.ofReal |β| * interactionStrength Φ i) i

end Prop88b

section Prop88bProb

variable [Countable S] {Φ : Potential S E} [Potential.IsPotential Φ]
  [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)

/-- **Georgii, Proposition (8.8)** for a probability a priori measure and an absolutely summable
potential: the special case of
`Dobrushin.isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible`, which proves (8.8) at
Georgii's own hypotheses — an arbitrary σ-finite non-zero a priori measure and a merely
`λ`-admissible potential, with no restriction on the self-potential. -/
theorem isDobrushin_gibbsSpecification {c : ℝ≥0∞} (hc : c < 2)
    (hΦ : ∀ i, ENNReal.ofReal |β| * interactionStrength Φ i ≤ c) :
    IsDobrushin (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) := by
  rw [← Potential.gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure (Φ := Φ) ν β]
  exact isDobrushin_gibbsSpecificationOfSigmaFiniteAdmissible (Φ := Φ) _ hc hΦ

/-- **Georgii, Example (8.9)(2), general form.** The `tanh` criterion: if for every site the
pair sums `tanh (|β| ∑_{A ⊇ {i,j}} δ(Φ_A) / 2)` add up to less than `1`, the Gibbsian
specification of `βΦ` satisfies Dobrushin's condition. Georgii states this only for two-point
spin spaces; `interdep_gibbsSpecification_le_tanh` gives it over any state space. Since
`tanh x ≤ x`, it is strictly weaker than the hypothesis of `isDobrushin_gibbsSpecification`. -/
theorem isDobrushin_gibbsSpecification_of_tanh {c : ℝ≥0∞} (hc : c < 1)
    (hΦ : ∀ i, ∑' j : S, {j : S | j ≠ i}.indicator
        (fun j ↦ ENNReal.ofReal (Real.tanh (|β| * (pairStrength Φ i j).toReal / 2))) j ≤ c) :
    IsDobrushin (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) := by
  refine ⟨Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable ν β, c, hc, fun i ↦ ?_⟩
  set γ := Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β with hγ
  have hzero : ∀ j : S, interdep γ i j
      = {j : S | j ≠ i}.indicator (fun j ↦ interdep γ i j) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp), interdep_self]
    · rw [Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj)]
  refine le_trans (le_of_eq (tsum_congr hzero)) (le_trans (ENNReal.tsum_le_tsum fun j ↦ ?_) (hΦ i))
  by_cases hj : j = i
  · subst hj
    rw [Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp),
      Set.indicator_of_notMem (show j ∉ {k : S | k ≠ j} by simp)]
  · rw [Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj),
      Set.indicator_of_mem (show j ∈ {j : S | j ≠ i} from hj)]
    exact interdep_gibbsSpecification_le_tanh ν β i j

/-- **Georgii, Proposition (8.8)** in Georgii's own `sup`-form. -/
theorem isDobrushin_gibbsSpecification_of_iSup_lt
    (h : ⨆ i, ENNReal.ofReal |β| * interactionStrength Φ i < 2) :
    IsDobrushin (Potential.gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) :=
  isDobrushin_gibbsSpecification ν β h
    (fun i ↦ le_iSup (fun i ↦ ENNReal.ofReal |β| * interactionStrength Φ i) i)

end Prop88bProb


end MeasureTheory.GibbsMeasure.Dobrushin

end

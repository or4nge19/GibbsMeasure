/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.BrokenShiftInvariance

/-!
# Georgii Example (16.31): a potential with totally broken shift invariance

Georgii's Example (16.31) applies Theorem (16.30) on the two-state lattice `E = {−1, +1}`,
`f = σ₀`, with the index set `I = {i ∈ ℤ^d : |i₁| ≥ R, i₂ = ⋯ = i_d = 0}` on a line through the
origin. The input the theorem needs is an `f`-`I`-oscillating shift-invariant random field of
finite specific entropy, and this file constructs one.

## Main definitions

* `MeasureTheory.GibbsMeasure.altCfg k₀ b`: the two *alternating configurations* in the direction
  `k₀`, `ω^±_j = ±(−1)^{j_{k₀}}`.
* `MeasureTheory.GibbsMeasure.altField k₀`: the random field `μ = (δ_{ω⁺} + δ_{ω⁻})/2`.
* `MeasureTheory.GibbsMeasure.spinObservable ι`: the observable `f = σ₀ ∈ {−1, +1}`, written as a
  difference of two cylinder indicators so that `f ∈ 𝓛_{\{0\}}`.
* `MeasureTheory.GibbsMeasure.altAxis k₀ R`: **Georgii's index set** `I`.

## Main results

* `MeasureTheory.GibbsMeasure.map_shift_altField`, `altField_mem_invariantFields`: `μ` is shift
  invariant — the shift `θ_m` fixes both atoms when `m_{k₀}` is even and exchanges them when
  `m_{k₀}` is odd, and they carry equal mass.
* `MeasureTheory.GibbsMeasure.correlation_spinObservable_altField`: **Georgii's computation**
  `μ(σ₀ σ_i) = (−1)^{i_{k₀}}`.
* `MeasureTheory.GibbsMeasure.isOscillating_altField`: `μ` is `σ₀`-`I`-oscillating, because `I`
  contains infinitely many sites with `i_{k₀}` even and infinitely many with `i_{k₀}` odd.
* `MeasureTheory.GibbsMeasure.exists_isOscillating_altAxis` and
  `MeasureTheory.GibbsMeasure.exists_nonempty_extremePoints_diff_altAxis`: **Example (16.31)**.
  Given any `Φ⁰ ∈ ℬ_Θ` and any `R`, there is a potential `Φ` with `Φ − Φ⁰ ∈ ℬ^I_Θ(σ₀)` — so `Φ`
  coincides with `Φ⁰` except on the `I`-pairs — which admits an `σ₀`-`I`-oscillating
  shift-invariant Gibbs measure, hence (Lemma (16.28)) satisfies
  `ex 𝒢_Θ(Φ) ∖ ex 𝒢(Φ) ≠ ∅` and `ex 𝒢(Φ) ∖ 𝒢_Θ(Φ) ≠ ∅`: its shift invariance is broken.

## Deviations from Georgii

* Georgii builds his oscillating field as `μ = μ₀^{ℤ^{d−1}}`, the product over the lines parallel
  to `e₁` of the unique shift-invariant Markov chain on `{−1, +1}` with transition matrix
  `[[0, 1], [1, 0]]`, which is `μ₀ = (δ_{+−} + δ_{−+})/2`. The field used here is the
  `d`-dimensional analogue of `μ₀` itself, `μ = (δ_{ω⁺} + δ_{ω⁻})/2` with `ω^±_j = ±(−1)^{j₁}`.
  For `d = 1` the two constructions agree. For `d ≥ 2` they differ off the `k₀`-axis — Georgii's
  has `μ(σ₀ σ_i) = 0` when `i` leaves the axis, this one has `μ(σ₀ σ_i) = (−1)^{i₁}` for every `i`
  — but they agree on `I`, which is all that Theorem (16.30) uses, and this one avoids the
  identification `Ω ≅ (E^ℤ)^{ℤ^{d−1}}`.
* Georgii's a priori measure is counting measure on `{−1, +1}`; the a priori measure here is the
  normalised counting measure `uniformOn univ`, as everywhere in this development, since the
  specific entropy `𝓀(·)` is defined relative to a probability measure. For a finite state space
  every shift-invariant random field then has finite specific entropy
  (`specificEntropy_uniformOn_ne_bot`), which is Georgii's `𝓟_Θ(Ω, 𝓕) = 𝓟^λ_Θ(Ω, 𝓕)`.
* The state space is `Bool` rather than `{−1, +1} ⊆ ℝ`; the spins `±1` enter through the
  observable `spinObservable`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

section Alternating

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

variable (k₀ : ι)

/-- The two *alternating configurations* in the direction `k₀`: `altCfg k₀ b` has spin
`b ⊕ (i_{k₀} even)` at the site `i`, so that neighbouring sites in the direction `k₀` carry
opposite spins and `altCfg k₀ false = ¬ altCfg k₀ true`. -/
def altCfg (b : Bool) : (ι → ℤ) → Bool := fun j ↦ xor b (decide (Even (j k₀)))

/-- The observable `σ₀ ∈ {−1, +1}` on the two-state configuration space. -/
def spinObservable (ι : Type*) [Fintype ι] [LinearOrder ι] :
    lp (fun _ : (ι → ℤ) → Bool ↦ ℝ) ∞ :=
  indicatorLp {ω : (ι → ℤ) → Bool | ω 0 = true} - indicatorLp {ω : (ι → ℤ) → Bool | ω 0 = false}

lemma coeFn_spinObservable (ω : (ι → ℤ) → Bool) :
    ⇑(spinObservable ι) ω = if ω 0 = true then 1 else -1 := by
  have h : ⇑(spinObservable ι) ω
      = {ω : (ι → ℤ) → Bool | ω 0 = true}.indicator (fun _ ↦ (1 : ℝ)) ω
        - {ω : (ι → ℤ) → Bool | ω 0 = false}.indicator (fun _ ↦ (1 : ℝ)) ω := rfl
  rw [h]
  by_cases hω : ω 0 = true
  · rw [Set.indicator_of_mem (show ω ∈ {ω : (ι → ℤ) → Bool | ω 0 = true} from hω),
      Set.indicator_of_notMem (show ω ∉ {ω : (ι → ℤ) → Bool | ω 0 = false} by simp [hω]),
      ite_eq_left hω]
    norm_num
  · rw [Set.indicator_of_notMem (show ω ∉ {ω : (ι → ℤ) → Bool | ω 0 = true} from hω),
      Set.indicator_of_mem (show ω ∈ {ω : (ι → ℤ) → Bool | ω 0 = false} by simpa using hω),
      ite_eq_right hω]
    norm_num

omit [Fintype ι] [LinearOrder ι] in
lemma measurableSet_spinAt (c : Bool) :
    MeasurableSet[cylinderEvents (X := fun _ : ι → ℤ ↦ Bool)
        ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ)))] {ω : (ι → ℤ) → Bool | ω 0 = c} := by
  have hmeas : Measurable[cylinderEvents (X := fun _ : ι → ℤ ↦ Bool)
      ((({0} : Finset (ι → ℤ)) : Set (ι → ℤ)))] (fun ω : (ι → ℤ) → Bool ↦ ω 0) := by
    refine measurable_cylinderEvents_iff_dependsOn.2 ⟨measurable_pi_apply 0, fun ω ω' h ↦ ?_⟩
    exact h 0 (by simp)
  exact hmeas (measurableSet_singleton c)

lemma spinObservable_mem_localFunctionsOn :
    spinObservable ι ∈ localFunctionsOn (ι → ℤ) Bool {0} :=
  Subalgebra.sub_mem _ (indicatorLp_mem_localFunctionsOn (measurableSet_spinAt true))
    (indicatorLp_mem_localFunctionsOn (measurableSet_spinAt false))

lemma measurable_spinObservable : Measurable ⇑(spinObservable ι) :=
  (mem_localFunctionsOn.1 spinObservable_mem_localFunctionsOn).mono cylinderEvents_le_pi le_rfl

/-- **Georgii Example (16.31).** The shift-invariant random field `μ = (δ_{ω⁺} + δ_{ω⁻})/2`
carried by the two alternating configurations in the direction `k₀`. -/
def altField : Measure ((ι → ℤ) → Bool) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (altCfg k₀ true) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (altCfg k₀ false)

instance isFiniteMeasure_half_dirac (ω : (ι → ℤ) → Bool) :
    IsFiniteMeasure ((2 : ℝ≥0∞)⁻¹ • Measure.dirac ω) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)

instance : IsProbabilityMeasure (altField k₀) := by
  constructor
  rw [altField, Measure.coe_add, Pi.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ MeasurableSet.univ, Measure.dirac_apply' _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  rw [ENNReal.inv_two_add_inv_two]

omit [Fintype ι] [LinearOrder ι] in
lemma integral_altField {g : ((ι → ℤ) → Bool) → ℝ} (hg : Measurable g) :
    ∫ ω, g ω ∂(altField k₀) = (g (altCfg k₀ true) + g (altCfg k₀ false)) / 2 := by
  have hint : ∀ x : (ι → ℤ) → Bool, Integrable g ((2 : ℝ≥0∞)⁻¹ • Measure.dirac x) := fun x ↦
    (integrable_dirac' hg.stronglyMeasurable (by simp [enorm_lt_top])).smul_measure (by simp)
  rw [altField, integral_add_measure (hint _) (hint _), integral_smul_measure,
    integral_smul_measure, integral_dirac' _ _ hg.stronglyMeasurable,
    integral_dirac' _ _ hg.stronglyMeasurable]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

omit [Fintype ι] [LinearOrder ι] in
/-- The shift moves an alternating configuration to an alternating configuration: it fixes both
when `m_{k₀}` is even and exchanges them when `m_{k₀}` is odd. -/
lemma shift_altCfg (b : Bool) (m : ι → ℤ) :
    (shift Bool m).toFun (altCfg k₀ b) = altCfg k₀ (if Even (m k₀) then b else !b) := by
  funext l
  rw [shift_toFun_apply]
  simp only [altCfg, Pi.sub_apply]
  by_cases hm : Even (m k₀)
  · rw [ite_eq_left hm]
    congr 1
    simp [Int.even_sub, hm]
  · rw [ite_eq_right hm]
    have : decide (Even (l k₀ - m k₀)) = !decide (Even (l k₀)) := by
      simp [Int.even_sub, hm, -Int.not_even_iff_odd]
    rw [this]
    cases b <;> cases hd : decide (Even (l k₀)) <;> simp

omit [Fintype ι] [LinearOrder ι] in
/-- **Georgii Example (16.31).** The alternating field is shift invariant: the shift either fixes
the two atoms or exchanges them, and they carry equal mass. -/
lemma map_shift_altField (m : ι → ℤ) :
    (altField k₀).map (shift Bool m).toFun = altField k₀ := by
  have hmeas : Measurable (shift Bool m).toFun := (shift Bool m).measurable_toFun
  rw [altField, Measure.map_add _ _ hmeas, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hmeas, Measure.map_dirac' hmeas, shift_altCfg, shift_altCfg]
  by_cases hm : Even (m k₀)
  · rw [ite_eq_left hm, ite_eq_left hm]
  · rw [ite_eq_right hm, ite_eq_right hm]
    simp only [Bool.not_true, Bool.not_false]
    exact add_comm _ _

omit [Fintype ι] [LinearOrder ι] in
lemma altField_mem_invariantFields :
    altField k₀ ∈ invariantFields (shiftGroup (ι → ℤ) Bool) :=
  mem_invariantFields_shiftGroup.2
    ⟨inferInstance, fun m ↦ ⟨(shift Bool m).measurable_toFun, map_shift_altField k₀ m⟩⟩

lemma altField_mem_invariantFieldsOfFiniteEntropy :
    altField k₀ ∈ Potential.BTheta.invariantFieldsOfFiniteEntropy ι Bool (uniformOn Set.univ) :=
  ⟨altField_mem_invariantFields k₀,
    specificEntropy_uniformOn_ne_bot (altField_mem_invariantFields k₀)⟩

lemma spinObservable_altCfg (b : Bool) :
    ⇑(spinObservable ι) (altCfg k₀ b) = if b = false then 1 else -1 := by
  rw [coeFn_spinObservable]
  cases b <;> simp [altCfg]

/-- **Georgii Example (16.31):** `μ(σ₀ σ_i) = (−1)^{i_{k₀}}`. -/
theorem correlation_spinObservable_altField (i : ι → ℤ) :
    correlation (spinObservable ι) (altField k₀) i = if Even (i k₀) then 1 else -1 := by
  have hmeas : Measurable fun ω : (ι → ℤ) → Bool ↦
      ⇑(spinObservable ι) ω * ⇑(spinObservable ι) ((shift Bool i).toFun ω) :=
    measurable_spinObservable.mul
      (measurable_spinObservable.comp (shift Bool i).measurable_toFun)
  rw [correlation, integral_altField k₀ hmeas, shift_altCfg, shift_altCfg,
    spinObservable_altCfg, spinObservable_altCfg, spinObservable_altCfg, spinObservable_altCfg]
  by_cases hi : Even (i k₀) <;> simp [hi]

/-- The site `n e_{k₀}` on the `k₀`-axis. -/
def axisPt (n : ℤ) : ι → ℤ := fun l ↦ if l = k₀ then n else 0

omit [Fintype ι] in
@[simp] lemma axisPt_self (n : ℤ) : axisPt k₀ n k₀ = n := by simp [axisPt]

omit [Fintype ι] in
lemma axisPt_of_ne {l : ι} (hl : l ≠ k₀) (n : ℤ) : axisPt k₀ n l = 0 := by simp [axisPt, hl]

omit [Fintype ι] in
lemma axisPt_injective : Function.Injective (axisPt k₀) := fun m n h ↦ by
  simpa using congrFun h k₀

variable (R : ℕ)

/-- **Georgii Example (16.31):** the index set `I = {i : |i₁| ≥ R, i₂ = ⋯ = i_d = 0}`, here with
the distinguished direction `k₀`. -/
def altAxis : Set (ι → ℤ) := {i | (R : ℤ) ≤ |i k₀| ∧ ∀ l, l ≠ k₀ → i l = 0}

omit [Fintype ι] in
lemma axisPt_mem_altAxis {n : ℤ} (hn : (R : ℤ) ≤ |n|) : axisPt k₀ n ∈ altAxis k₀ R :=
  ⟨by simpa using hn, fun l hl ↦ axisPt_of_ne k₀ hl n⟩

/-- The sites of `I` with `i_{k₀}` even, where `μ(σ₀σ_i) = 1`. -/
def altAxisEven : Set (ι → ℤ) := {i ∈ altAxis k₀ R | Even (i k₀)}

/-- The sites of `I` with `i_{k₀}` odd, where `μ(σ₀σ_i) = −1`. -/
def altAxisOdd : Set (ι → ℤ) := {i ∈ altAxis k₀ R | ¬ Even (i k₀)}

omit [Fintype ι] [LinearOrder ι] in
lemma altAxisEven_subset : altAxisEven k₀ R ⊆ altAxis k₀ R := fun _ h ↦ h.1

omit [Fintype ι] [LinearOrder ι] in
lemma altAxisOdd_subset : altAxisOdd k₀ R ⊆ altAxis k₀ R := fun _ h ↦ h.1

omit [Fintype ι] in
lemma infinite_altAxisEven : (altAxisEven k₀ R).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ axisPt k₀ (2 * ((R : ℤ) + n))) (fun m n h ↦ ?_) (fun n ↦ ?_)
  · have := axisPt_injective k₀ h
    omega
  · exact ⟨axisPt_mem_altAxis k₀ R (by rw [abs_of_nonneg (by positivity)]; omega),
      by simp⟩

omit [Fintype ι] in
lemma infinite_altAxisOdd : (altAxisOdd k₀ R).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ ↦ axisPt k₀ (2 * ((R : ℤ) + n) + 1)) (fun m n h ↦ ?_) (fun n ↦ ?_)
  · have := axisPt_injective k₀ h
    omega
  · refine ⟨axisPt_mem_altAxis k₀ R (by rw [abs_of_nonneg (by positivity)]; omega), ?_⟩
    simp only [axisPt_self, Int.not_even_iff_odd]
    exact ⟨_, rfl⟩

omit [Fintype ι] in
lemma infinite_altAxis : (altAxis k₀ R).Infinite :=
  (infinite_altAxisEven k₀ R).mono (altAxisEven_subset k₀ R)

/-- **Georgii Example (16.31).** The alternating field is `σ₀`-`I`-oscillating: along `I` the
correlations `μ(σ₀ σ_i) = (−1)^{i_{k₀}}` take the value `1` for infinitely many `i` and the value
`−1` for infinitely many `i`. -/
theorem isOscillating_altField : IsOscillating (altAxis k₀ R) (spinObservable ι) (altField k₀) := by
  set g := correlation (spinObservable ι) (altField k₀) with hgdef
  set F := atInfinityWithin (altAxis k₀ R) with hFdef
  have hne : F.NeBot := atInfinityWithin_neBot (infinite_altAxis k₀ R)
  have hgval : ∀ i, g i = if Even (i k₀) then 1 else -1 :=
    correlation_spinObservable_altField k₀
  have hub : ∀ i, g i ≤ 1 := fun i ↦ by rw [hgval]; split <;> norm_num
  have hlb : ∀ i, (-1 : ℝ) ≤ g i := fun i ↦ by rw [hgval]; split <;> norm_num
  have hco : F.IsBoundedUnder (· ≤ ·) g := Filter.isBoundedUnder_of ⟨1, hub⟩
  have hco' : F.IsBoundedUnder (· ≥ ·) g := Filter.isBoundedUnder_of ⟨-1, hlb⟩
  have hfreq : ∀ (J : Set (ι → ℤ)) (a : ℝ), J ⊆ altAxis k₀ R → J.Infinite →
      (∀ i ∈ J, g i = a) → ∃ᶠ i in F, g i = a := by
    intro J a hJ hJinf hJa
    have hJne : (atInfinityWithin J).NeBot := atInfinityWithin_neBot hJinf
    refine Filter.Frequently.filter_mono ?_ (inf_le_inf_left _ (Filter.principal_mono.2 hJ))
    refine Filter.Eventually.frequently ?_
    exact Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall hJa)
  have h1 : ∃ᶠ i in F, g i = 1 :=
    hfreq _ 1 (altAxisEven_subset k₀ R) (infinite_altAxisEven k₀ R)
      fun i hi ↦ by rw [hgval, ite_eq_left hi.2]
  have h2 : ∃ᶠ i in F, g i = -1 :=
    hfreq _ (-1) (altAxisOdd_subset k₀ R) (infinite_altAxisOdd k₀ R)
      fun i hi ↦ by rw [hgval, ite_eq_right hi.2]
  have hlim : (1 : ℝ) ≤ Filter.limsup g F :=
    Filter.le_limsup_of_frequently_le (h1.mono fun i hi ↦ hi.ge) hco
  have hlim' : Filter.liminf g F ≤ -1 :=
    Filter.liminf_le_of_frequently_le (h2.mono fun i hi ↦ hi.le) hco'
  rw [IsOscillating]
  linarith

/-! ### Georgii Example (16.31): the conclusion -/

/-- **Georgii Example (16.31).** Given any potential `Φ⁰ ∈ ℬ_Θ` on `{−1, +1}^{ℤ^d}` and any
`R > 0`, there is a potential `Φ ∈ ℬ_Θ` which coincides with `Φ⁰` except on the `I`-pairs
`Λ_i = {0} ∪ {−i}`, `i ∈ I = {i : |i_{k₀}| ≥ R, i_l = 0 for l ≠ k₀}`, and which exhibits *totally
broken shift invariance*: it admits an `σ₀`-`I`-oscillating shift-invariant Gibbs measure, hence
an extreme shift-invariant Gibbs measure which is not extreme in `𝒢(Φ)`, and an extreme Gibbs
measure which is not shift invariant. -/
theorem exists_isOscillating_altAxis (Φ₀ : Potential.BTheta (ι → ℤ) Bool) :
    ∃ Φ : Potential.BTheta (ι → ℤ) Bool,
      Φ - Φ₀ ∈ BThetaOrder {0} (fun _ : Fin 1 ↦ spinObservable ι) (altAxis k₀ R) ∧
      ∃ ρ ∈ invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) Bool)) (uniformOn Set.univ) 1)
          (shiftGroup (ι → ℤ) Bool),
        IsOscillating (altAxis k₀ R) (spinObservable ι) ρ := by
  have : Nonempty ι := ⟨k₀⟩
  exact exists_mem_invariantG_isOscillating (uniformOn Set.univ) (Finset.singleton_nonempty _)
    spinObservable_mem_localFunctionsOn (infinite_altAxis k₀ R)
    (altField_mem_invariantFieldsOfFiniteEntropy k₀) (isOscillating_altField k₀ R) Φ₀

/-- **Georgii Example (16.31), the broken shift invariance.** The potential produced above has
both `ex 𝒢_Θ(Φ) ∖ ex 𝒢(Φ) ≠ ∅` and `ex 𝒢(Φ) ∖ 𝒢_Θ(Φ) ≠ ∅`, by Lemma (16.28). -/
theorem exists_nonempty_extremePoints_diff_altAxis (Φ₀ : Potential.BTheta (ι → ℤ) Bool) :
    ∃ Φ : Potential.BTheta (ι → ℤ) Bool,
      Φ - Φ₀ ∈ BThetaOrder {0} (fun _ : Fin 1 ↦ spinObservable ι) (altAxis k₀ R) ∧
      ((invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) Bool)) (uniformOn Set.univ) 1)
          (shiftGroup (ι → ℤ) Bool)).extremePoints ℝ≥0∞ \
        (G (Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) Bool)) (uniformOn Set.univ) 1)).extremePoints
            ℝ≥0∞).Nonempty ∧
      ((G (Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) Bool)) (uniformOn Set.univ) 1)).extremePoints ℝ≥0∞ \
        invariantG (Potential.gibbsSpecificationOfAbsolutelySummable
          (Φ := (Φ : Potential (ι → ℤ) Bool)) (uniformOn Set.univ) 1)
          (shiftGroup (ι → ℤ) Bool)).Nonempty := by
  have : Nonempty ι := ⟨k₀⟩
  obtain ⟨Φ, hΦ, ρ, hρ, hosc⟩ := exists_isOscillating_altAxis k₀ R Φ₀
  exact ⟨Φ, hΦ,
    nonempty_extremePoints_invariantG_diff_extremePoints_G (infinite_altAxis k₀ R)
      spinObservable_mem_localFunctionsOn hρ hosc,
    nonempty_extremePoints_G_diff_invariantG (infinite_altAxis k₀ R)
      spinObservable_mem_localFunctionsOn hρ hosc⟩

end Alternating

end MeasureTheory.GibbsMeasure

end

end

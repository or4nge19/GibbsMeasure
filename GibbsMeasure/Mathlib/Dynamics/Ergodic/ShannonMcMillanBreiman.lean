/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Trivial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# The Shannon–McMillan theorem for finite-state stationary random fields

Let a countable abelian group `G` carrying a translation-invariant linear order (`[LinearOrder G]`
and `[IsOrderedAddMonoid G]`; for `ℤ^d` this is the lexicographic order, which Mathlib puts on the
type synonym `Lex (ι → ℤ)`) act on a probability space `(Ω, μ)` by measure-preserving maps
`ω ↦ i +ᵥ ω`, and let `X : Ω → E` be measurable into a finite set `E`. The *stationary random
field* is `i ↦ X (i +ᵥ ·)`, the *block* on a finite `Λ ⊆ G` is `X_Λ ω = (X (i +ᵥ ω))_{i ∈ Λ}`
(`MeasureTheory.blockMap`) and its *probability* is `p_Λ ω = μ (X_Λ = X_Λ ω)`
(`MeasureTheory.blockProb`).

The *conditional information* of the spin at the origin given a finite window `W` of the past
`{g | g < 0}` is
`g_W ω = log p_W ω − log p_{W ∪ {0}} ω`, a.s. equal to `−log μ(X_0 = X_0 ω | X_W = X_W ω) ≥ 0`
(`MeasureTheory.condInformation`, `MeasureTheory.condProbGiven_blockMap_eq_div`), and the
*entropy rate* is
`h = inf_W ∫ g_W dμ = inf_W H(X_0 | X_W)` (`MeasureTheory.entropyRate`), the infimum over the
finite windows of the past.

## Main results

* `MeasureTheory.tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate`, the
  **Shannon–McMillan theorem**: if the action is *ergodic* — every set of the invariant σ-algebra
  `MeasurableSpace.smulInvariants (Multiplicative G) Ω` is null or co-null — then along every
  Følner net `F` of finite volumes,
  `∫ | −|F k|⁻¹ log p_{F k} − h | dμ → 0`, i.e. `−|F k|⁻¹ log p_{F k} → h` in `L¹(μ)`.
* `MeasureTheory.tendsto_inv_card_mul_integral_neg_log_blockProb`: integrating, the normalised
  block entropies `|F k|⁻¹ H(X_{F k}) = −|F k|⁻¹ ∫ log p_{F k} dμ` converge to `h`. In particular
  `h` does not depend on the order used to define it, nor on the Følner net.
* `MeasureTheory.tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate_cube` in
  `GibbsMeasure/Mathlib/Dynamics/Ergodic/ShannonMcMillanCube.lean` is the `ℤ^d` statement along
  cubes `Λ_n = x_n + [0, r_n)^d`, `r_n → ∞`, which is the form Georgii cites.

## The proof

* The **chain rule** (`MeasureTheory.neg_log_blockProb_eq_sum_condInformation`): enumerating `Λ`
  in increasing order and telescoping, `−log p_Λ ω = ∑_{i ∈ Λ} g_{W_i(Λ)} (i +ᵥ ω)` with
  `W_i(Λ) = (Λ ∩ {j | j < i}) − i` (`MeasureTheory.pastWindow`) a finite window of the past. The
  identity is exact — no null sets — and uses only the stationarity
  `p_Λ (i +ᵥ ω) = p_{i +ᵥ Λ} ω` (`MeasureTheory.blockProb_vadd`).
* **Conditioning on more reduces the information in the mean**
  (`MeasureTheory.integral_exp_condInformation_sub_le_one`): for `W' ⊆ W`,
  `∫ exp (g_W − g_{W'}) dμ ≤ 1`. Almost surely the integrand is the ratio
  `μ(X_0 = X_0 ω | X_{W'} = X_{W'} ω) / μ(X_0 = X_0 ω | X_W = X_W ω)`; summing over the values of
  the spin, each term is bounded by the pull-out property of the conditional expectation given
  `X_W`, whose elementary version is `MeasureTheory.condExp_indicator_comap_ae_eq_condProbGiven`
  (`MeasureTheory.integral_indicator_mul_div_condProbGiven_le`).
* Hence `∫ g_W ≤ ∫ g_{W'}` (Jensen, `MeasureTheory.integral_condInformation_mono`) and, by
  `MeasureTheory.integral_abs_le_of_integral_exp_le_one` (the pointwise inequality
  `|t| ≤ 2δ + 2(e^t − 1 − t)/δ − t`, which for `t > 0` is the arithmetic–geometric mean inequality
  applied to `e^t − 1 − t ≥ t²/2`), the `L¹` distance `∫ |g_W − g_{W'}|` is controlled by the
  entropy drop `∫ g_{W'} − ∫ g_W` (`MeasureTheory.integral_abs_condInformation_sub_le`).
* Consequently, for a window `W₀` whose mean information is within `ε` of `h`, *every* larger
  finite window `W` of the past has `∫ |g_W − g_{W₀}| ≤ ε`, uniformly in `W`
  (`MeasureTheory.exists_forall_integral_abs_condInformation_sub_le`). In the chain rule, the
  sites `i ∈ F k` with `i + W₀ ⊆ F k` — all but a vanishing fraction, by the Følner property
  (`MeasureTheory.tendsto_card_filter_vadd_not_subset_div_card`) — contribute terms `L¹`-close to
  `g_{W₀}(i +ᵥ ·)`, the others at most `∫ g_∅ + ∫ g_{W₀}` each
  (`MeasureTheory.integral_abs_inv_card_sum_condInformation_sub_le`). Finally
  `|F k|⁻¹ ∑_{i ∈ F k} g_{W₀}(i +ᵥ ·) → ∫ g_{W₀}` in `L¹` by the mean ergodic theorem
  (`MeasureTheory.tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp`) together with
  ergodicity (`MeasureTheory.condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one`).

## Not proved here

* The almost-sure (Breiman) form. Georgii, *Gibbs Measures and Phase Transitions*, uses only the
  `L¹` (McMillan) form: the proof of the large-deviation lower bound (15.47) needs
  `ν(| |Λ|⁻¹ log f_Λ + 𝓀(ν)|) → 0` for an ergodic `ν`, which is the statement proved here once
  `f_Λ` is identified with `p_Λ` (for the counting measure on a finite `E`).
* The identification of `entropyRate` with the specific entropy `𝓀` of
  `GibbsMeasure/Specification/SpecificEntropy.lean`, which belongs downstream and is
  `MeasureTheory.GibbsMeasure.specificEntropy_uniformOn_eq_entropyRate_sub_log_card` in
  `GibbsMeasure/Specification/ShannonMcMillan.lean`: for a shift-invariant random field on
  `E^{ℤ^d}` with `E` finite, `𝓀(μ) = entropyRate (Lex (ℤ^d)) μ (σ ↦ σ_0) − log |E|`. The proof
  does not go through the martingale convergence of `μ(X_0 = · | X_W)` along the finite windows
  of the past; it compares the two *limits* — Georgii's Theorem (15.12) and
  `tendsto_inv_card_mul_integral_neg_log_blockProb` — along one and the same sequence of cubes.
-/

@[expose] public section

open Filter Finset Set
open scoped ENNReal Pointwise Topology symmDiff

/-! ### Functions with finitely many values -/

/-- The range of a function assembled pointwise from two functions with finite range is
finite. -/
lemma Set.finite_range₂ {α β γ δ : Type*} {a : α → β} {b : α → γ} (f : β → γ → δ)
    (ha : (Set.range a).Finite) (hb : (Set.range b).Finite) :
    (Set.range fun x ↦ f (a x) (b x)).Finite :=
  (ha.image2 f hb).subset <| by
    rintro _ ⟨x, rfl⟩
    exact Set.mem_image2_of_mem (Set.mem_range_self x) (Set.mem_range_self x)

/-- A function that factors through a finite type has finite range. -/
lemma Set.finite_range_comp_of_finite {α β γ : Type*} [Finite β] (a : α → β) (g : β → γ) :
    (Set.range fun x ↦ g (a x)).Finite :=
  (Set.finite_range g).subset (Set.range_comp_subset_range a g)

/-- Composing with a function preserves finiteness of the range. -/
lemma Set.finite_range_comp {α β γ : Type*} {f : α → β} (hf : (Set.range f).Finite) (g : β → γ) :
    (Set.range fun x ↦ g (f x)).Finite := by
  rw [show (Set.range fun x ↦ g (f x)) = g '' Set.range f from Set.range_comp g f]
  exact hf.image g

/-- An indicator function of `1` takes at most the two values `0` and `1`. -/
lemma Set.finite_range_indicator_one {α : Type*} (s : Set α) :
    (Set.range (s.indicator fun _ ↦ (1 : ℝ))).Finite := by
  refine ((Set.finite_singleton (1 : ℝ)).insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

namespace MeasureTheory

/-- A measurable real function taking finitely many values on a finite measure space is
integrable. -/
lemma integrable_of_finite_range {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (hr : (Set.range f).Finite) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := (hr.image abs).bddAbove
  exact Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
    rw [Real.norm_eq_abs]
    exact hC ⟨f ω, Set.mem_range_self ω, rfl⟩)


/-- **An `L¹` bound from an exponential moment bound.** If `∫ exp u dμ ≤ 1` on a probability
space then `u` is small in `L¹` as soon as its mean is small: for every `δ > 0`,
`∫ |u| dμ ≤ 2δ + (1 + 2/δ) (-∫ u dμ)`, where `-∫ u dμ ≥ 0` by Jensen's inequality. The pointwise
input is `|t| ≤ 2δ + 2(e^t - 1 - t)/δ - t`, which for `t > 0` is the arithmetic–geometric mean
inequality applied to `e^t - 1 - t ≥ t²/2`. -/
theorem integral_abs_le_of_integral_exp_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Ω → ℝ} (hu : Integrable u μ)
    (hexp : Integrable (fun ω ↦ Real.exp (u ω)) μ) (h : ∫ ω, Real.exp (u ω) ∂μ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ ω, |u ω| ∂μ ≤ 2 * δ + (1 + 2 / δ) * (-∫ ω, u ω ∂μ) := by
  have hpt : ∀ t : ℝ, |t| ≤ 2 * δ + 2 * (Real.exp t - 1 - t) / δ - t := fun t ↦ by
    have hφ : 0 ≤ Real.exp t - 1 - t := by linarith [Real.add_one_le_exp t]
    have h2d : 2 * (Real.exp t - 1 - t) / δ = 2 * ((Real.exp t - 1 - t) / δ) := by ring
    rcases le_or_gt t 0 with ht | ht
    · rw [abs_of_nonpos ht]
      have : 0 ≤ 2 * (Real.exp t - 1 - t) / δ := by positivity
      linarith
    · rw [abs_of_pos ht]
      have hq : t ^ 2 / 2 ≤ Real.exp t - 1 - t := by
        linarith [Real.quadratic_le_exp_of_nonneg ht.le]
      have hkey : t * δ ≤ δ * δ + (Real.exp t - 1 - t) := by nlinarith [sq_nonneg (δ - t / 2)]
      have hdiv : 0 ≤ δ + (Real.exp t - 1 - t) / δ - t := by
        have hE : δ + (Real.exp t - 1 - t) / δ - t
            = (δ * δ + (Real.exp t - 1 - t) - t * δ) / δ := by field_simp
        rw [hE]
        exact div_nonneg (by linarith) hδ.le
      linarith
  have hone : Integrable (fun _ : Ω ↦ (1 : ℝ)) μ := integrable_const (μ := μ) (1 : ℝ)
  have hΔ : 0 ≤ -∫ ω, u ω ∂μ := by
    have h1 : ∫ ω, (1 + u ω) ∂μ ≤ ∫ ω, Real.exp (u ω) ∂μ :=
      integral_mono (hone.add hu) hexp fun ω ↦ by linarith [Real.add_one_le_exp (u ω)]
    rw [integral_add hone hu] at h1
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    linarith
  have hv : Integrable (fun ω ↦ Real.exp (u ω) - 1 - u ω) μ := (hexp.sub hone).sub hu
  have hvint : ∫ ω, (Real.exp (u ω) - 1 - u ω) ∂μ
      = (∫ ω, Real.exp (u ω) ∂μ) - 1 - ∫ ω, u ω ∂μ := by
    have h1 : Integrable (fun ω ↦ Real.exp (u ω) - 1) μ := hexp.sub hone
    rw [integral_sub h1 hu, integral_sub hexp hone]
    simp
  have hi : Integrable (fun ω ↦ 2 * δ + 2 * (Real.exp (u ω) - 1 - u ω) / δ - u ω) μ := by
    have e1 : (fun ω ↦ 2 * δ + 2 * (Real.exp (u ω) - 1 - u ω) / δ - u ω)
        = fun ω ↦ 2 * δ + ((2 / δ) * (Real.exp (u ω) - 1 - u ω) - u ω) := by
      funext ω; ring
    rw [e1]
    exact (integrable_const (μ := μ) (2 * δ)).add ((hv.const_mul (2 / δ)).sub hu)
  have hfin : ∫ ω, (2 * δ + 2 * (Real.exp (u ω) - 1 - u ω) / δ - u ω) ∂μ
      = 2 * δ + 2 * ((∫ ω, Real.exp (u ω) ∂μ) - 1 - ∫ ω, u ω ∂μ) / δ - ∫ ω, u ω ∂μ := by
    have e1 : (fun ω ↦ 2 * δ + 2 * (Real.exp (u ω) - 1 - u ω) / δ - u ω)
        = fun ω ↦ 2 * δ + ((2 / δ) * (Real.exp (u ω) - 1 - u ω) - u ω) := by
      funext ω; ring
    have hB : Integrable (fun _ : Ω ↦ 2 * δ) μ := integrable_const (μ := μ) (2 * δ)
    have hC : Integrable (fun ω ↦ 2 / δ * (Real.exp (u ω) - 1 - u ω)) μ := hv.const_mul (2 / δ)
    have hA : Integrable (fun ω ↦ 2 / δ * (Real.exp (u ω) - 1 - u ω) - u ω) μ := hC.sub hu
    rw [e1, integral_add hB hA, integral_sub hC hu]
    simp only [integral_const, probReal_univ, smul_eq_mul]
    rw [integral_const_mul, hvint]
    ring
  have hstep : 2 * ((∫ ω, Real.exp (u ω) ∂μ) - 1 - ∫ ω, u ω ∂μ) / δ
      ≤ 2 * (-∫ ω, u ω ∂μ) / δ := by gcongr; linarith
  have hlast : 2 * δ + 2 * (-∫ ω, u ω ∂μ) / δ - ∫ ω, u ω ∂μ
      = 2 * δ + (1 + 2 / δ) * (-∫ ω, u ω ∂μ) := by field_simp; ring
  calc ∫ ω, |u ω| ∂μ ≤ ∫ ω, (2 * δ + 2 * (Real.exp (u ω) - 1 - u ω) / δ - u ω) ∂μ :=
        integral_mono hu.abs hi fun ω ↦ hpt (u ω)
    _ = 2 * δ + 2 * ((∫ ω, Real.exp (u ω) ∂μ) - 1 - ∫ ω, u ω ∂μ) / δ - ∫ ω, u ω ∂μ := hfin
    _ ≤ 2 * δ + 2 * (-∫ ω, u ω ∂μ) / δ - ∫ ω, u ω ∂μ := by linarith
    _ = 2 * δ + (1 + 2 / δ) * (-∫ ω, u ω ∂μ) := hlast

end MeasureTheory


namespace MeasureTheory

/-! ### Elementary conditional probabilities given a finitely-valued map -/

section CondProbGiven

variable {Ω T : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableSpace T]

/-- The *elementary conditional probability* `μ(s | Y = Y ω)` of `s` given the value of `Y` at
`ω`, as a real number (`0` when `μ(Y = Y ω) = 0`). For a countably-valued `Y` it is a version of
`μ[1_s | σ(Y)]` (`MeasureTheory.condExp_indicator_comap_ae_eq_condProbGiven`). -/
noncomputable def condProbGiven (μ : Measure Ω) (Y : Ω → T) (s : Set Ω) (ω : Ω) : ℝ :=
  μ.real (Y ⁻¹' {Y ω} ∩ s) / μ.real (Y ⁻¹' {Y ω})

omit [MeasurableSpace T] in
lemma condProbGiven_nonneg (Y : Ω → T) (s : Set Ω) (ω : Ω) : 0 ≤ condProbGiven μ Y s ω :=
  div_nonneg measureReal_nonneg measureReal_nonneg

omit [MeasurableSpace T] in
lemma condProbGiven_le_one (Y : Ω → T) (s : Set Ω) (ω : Ω) [IsFiniteMeasure μ] :
    condProbGiven μ Y s ω ≤ 1 :=
  div_le_one_of_le₀ (measureReal_mono inter_subset_left) measureReal_nonneg

omit [MeasurableSpace T] in
/-- `μ(s | Y = Y ω) · μ(Y = Y ω) = μ(s ∩ {Y = Y ω})`. -/
lemma condProbGiven_mul_measureReal (Y : Ω → T) (s : Set Ω) (ω : Ω) [IsFiniteMeasure μ] :
    condProbGiven μ Y s ω * μ.real (Y ⁻¹' {Y ω}) = μ.real (Y ⁻¹' {Y ω} ∩ s) := by
  unfold condProbGiven
  rcases eq_or_ne (μ.real (Y ⁻¹' {Y ω})) 0 with h | h
  · rw [h, mul_zero]
    have hz : μ.real (Y ⁻¹' {Y ω}) = 0 ↔ μ (Y ⁻¹' {Y ω}) = 0 := measureReal_eq_zero_iff
    have hz' : μ.real (Y ⁻¹' {Y ω} ∩ s) = 0 ↔ μ (Y ⁻¹' {Y ω} ∩ s) = 0 := measureReal_eq_zero_iff
    exact (hz'.2 (measure_mono_null Set.inter_subset_left (hz.1 h))).symm
  · exact div_mul_cancel₀ _ h

/-- The elementary conditional probability is measurable for `σ(Y)`. -/
lemma measurable_comap_condProbGiven [Countable T] [MeasurableSingletonClass T] (Y : Ω → T)
    (s : Set Ω) : Measurable[MeasurableSpace.comap Y ‹_›] (condProbGiven μ Y s) :=
  (measurable_of_countable fun t ↦ μ.real (Y ⁻¹' {t} ∩ s) / μ.real (Y ⁻¹' {t})).comp
    (comap_measurable Y)

/-- **The elementary conditional probability is a version of the conditional expectation.** For a
measurable map `Y` into a finite type with measurable singletons and a measurable set `s`,
`μ[1_s | σ(Y)] = μ(s | Y = ·)` almost surely. -/
theorem condExp_indicator_comap_ae_eq_condProbGiven [Finite T] [MeasurableSingletonClass T]
    [IsFiniteMeasure μ] {Y : Ω → T} (hY : Measurable Y) {s : Set Ω} (hs : MeasurableSet s) :
    μ[s.indicator (fun _ ↦ (1 : ℝ)) | MeasurableSpace.comap Y ‹_›] =ᵐ[μ] condProbGiven μ Y s := by
  have hm : MeasurableSpace.comap Y ‹_› ≤ ‹MeasurableSpace Ω› := hY.comap_le
  have hmeas : Measurable (condProbGiven μ Y s) :=
    (measurable_comap_condProbGiven Y s).mono hm le_rfl
  have hint : Integrable (condProbGiven μ Y s) μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (ae_of_all _ fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (condProbGiven_nonneg Y s ω)]
      exact condProbGiven_le_one Y s ω)
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    ((integrable_const (1 : ℝ)).indicator hs) (fun A _ _ ↦ hint.integrableOn) ?_
    (measurable_comap_condProbGiven Y s).stronglyMeasurable.aestronglyMeasurable).symm
  intro A hA _
  obtain ⟨B, -, rfl⟩ := hA
  classical
  have hfib : ∀ t, MeasurableSet (Y ⁻¹' {t}) := fun t ↦ hY (measurableSet_singleton t)
  have hBfin : (B : Set T).Finite := Set.toFinite B
  have hdisj : (hBfin.toFinset : Set T).PairwiseDisjoint fun t ↦ Y ⁻¹' {t} := fun t _ t' _ htt' ↦
    Set.disjoint_left.2 fun ω h h' ↦ htt' (h.symm.trans h')
  have hunion : Y ⁻¹' B = ⋃ t ∈ hBfin.toFinset, Y ⁻¹' {t} := by
    ext ω; simp
  rw [hunion, integral_biUnion_finset _ (fun t _ ↦ hfib t) hdisj (fun t _ ↦ hint.integrableOn),
    integral_biUnion_finset _ (fun t _ ↦ hfib t) hdisj
      (fun t _ ↦ ((integrable_const (1 : ℝ)).indicator hs).integrableOn)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [integral_indicator hs, Measure.restrict_restrict hs, setIntegral_const, smul_eq_mul, mul_one,
    setIntegral_congr_fun (hfib t) (g := fun _ ↦ μ.real (Y ⁻¹' {t} ∩ s) / μ.real (Y ⁻¹' {t}))
      (fun ω hω ↦ by simp only [condProbGiven, Set.mem_singleton_iff.1 hω]),
    setIntegral_const, smul_eq_mul, Set.inter_comm s]
  rcases eq_or_ne (μ.real (Y ⁻¹' {t})) 0 with h | h
  · rw [h, zero_mul]
    have hz : μ.real (Y ⁻¹' {t}) = 0 ↔ μ (Y ⁻¹' {t}) = 0 := measureReal_eq_zero_iff
    have hz' : μ.real (Y ⁻¹' {t} ∩ s) = 0 ↔ μ (Y ⁻¹' {t} ∩ s) = 0 := measureReal_eq_zero_iff
    exact (hz'.2 (measure_mono_null Set.inter_subset_left (hz.1 h))).symm
  · exact mul_div_cancel₀ _ h


omit [MeasurableSpace T] in
/-- The elementary conditional probability given a finitely-valued map takes finitely many
values. -/
lemma finite_range_condProbGiven [Finite T] (Y : Ω → T) (s : Set Ω) :
    (Set.range (condProbGiven μ Y s)).Finite :=
  Set.finite_range_comp_of_finite Y fun t ↦ μ.real (Y ⁻¹' {t} ∩ s) / μ.real (Y ⁻¹' {t})

/-- If `Y'` factors through `Y`, the elementary conditional probability given `Y'` is measurable
for `σ(Y)`. -/
lemma measurable_comap_condProbGiven_comp [Countable T] [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] (Y : Ω → T) (r : T → T') (s : Set Ω) :
    Measurable[MeasurableSpace.comap Y ‹_›] (condProbGiven μ (r ∘ Y) s) :=
  (measurable_of_countable fun t ↦
      μ.real ((r ∘ Y) ⁻¹' {r t} ∩ s) / μ.real ((r ∘ Y) ⁻¹' {r t})).comp (comap_measurable Y)

/-- **Conditioning on more can only reduce the information, in the mean.** If `Y'` factors
through the finitely-valued `Y` and `s` is measurable, then
`∫ 1_s(ω) · μ(s | Y' = Y' ω) / μ(s | Y = Y ω) dμ(ω) ≤ μ(s)`. This is the mechanism behind
`MeasureTheory.integral_exp_condInformation_sub_le_one`: the ratio is `σ(Y)`-measurable, so it may
be integrated against `μ[1_s | σ(Y)] = μ(s | Y = ·)`, which cancels the denominator. -/
theorem integral_indicator_mul_div_condProbGiven_le [Finite T] [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [Finite T'] [MeasurableSingletonClass T']
    [IsFiniteMeasure μ] {Y : Ω → T} (hY : Measurable Y) (r : T → T') {s : Set Ω}
    (hs : MeasurableSet s) :
    ∫ ω, s.indicator (fun _ ↦ (1 : ℝ)) ω *
      (condProbGiven μ (r ∘ Y) s ω / condProbGiven μ Y s ω) ∂μ ≤ μ.real s := by
  have hm : MeasurableSpace.comap Y ‹_› ≤ ‹MeasurableSpace Ω› := hY.comap_le
  set c := condProbGiven μ Y s with hcdef
  set c' := condProbGiven μ (r ∘ Y) s with hc'def
  set q : Ω → ℝ := fun ω ↦ c' ω / c ω with hqdef
  set e : Ω → ℝ := s.indicator fun _ ↦ (1 : ℝ) with hedef
  have hrY : Measurable (r ∘ Y) := (measurable_of_countable r).comp hY
  have hqm : Measurable[MeasurableSpace.comap Y ‹_›] q :=
    (measurable_comap_condProbGiven_comp Y r s).div (measurable_comap_condProbGiven Y s)
  have hqm0 : Measurable q := hqm.mono hm le_rfl
  have hcm : Measurable c := (measurable_comap_condProbGiven Y s).mono hm le_rfl
  have hc'm : Measurable c' := (measurable_comap_condProbGiven_comp Y r s).mono hm le_rfl
  have hcr : (Set.range c).Finite := finite_range_condProbGiven Y s
  have hc'r : (Set.range c').Finite := finite_range_condProbGiven (r ∘ Y) s
  have hqr : (Set.range q).Finite := Set.finite_range₂ (· / ·) hc'r hcr
  have hem : Measurable e := measurable_const.indicator hs
  have her : (Set.range e).Finite := Set.finite_range_indicator_one s
  have hei : Integrable e μ := (integrable_const (1 : ℝ)).indicator hs
  have hqei : Integrable (q * e) μ :=
    integrable_of_finite_range (hqm0.mul hem) (Set.finite_range₂ (· * ·) hqr her)
  have hqci : Integrable (fun ω ↦ q ω * c ω) μ :=
    integrable_of_finite_range (hqm0.mul hcm) (Set.finite_range₂ (· * ·) hqr hcr)
  have hc'i : Integrable c' μ := integrable_of_finite_range hc'm hc'r
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := MeasurableSpace.comap Y ‹_›)
    hqm.stronglyMeasurable hqei hei
  have h1 : ∫ ω, e ω * (c' ω / c ω) ∂μ = ∫ ω, q ω * c ω ∂μ := by
    have : ∫ ω, e ω * (c' ω / c ω) ∂μ = ∫ ω, (q * e) ω ∂μ := by
      simp only [Pi.mul_apply, hqdef]
      exact integral_congr_ae (ae_of_all _ fun ω ↦ mul_comm _ _)
    rw [this, ← integral_condExp hm (f := q * e)]
    refine integral_congr_ae ?_
    filter_upwards [hpull, condExp_indicator_comap_ae_eq_condProbGiven hY hs] with ω h h'
    rw [h]
    simp only [Pi.mul_apply]
    rw [hedef, h', hcdef]
  have h2 : ∀ ω, q ω * c ω ≤ c' ω := fun ω ↦ by
    rcases eq_or_ne (c ω) 0 with h | h
    · simp only [hqdef, h, div_zero, zero_mul]
      exact condProbGiven_nonneg _ _ _
    · rw [hqdef]
      simp only [div_mul_cancel₀ _ h, le_refl]
  have h3 : ∫ ω, c' ω ∂μ = μ.real s := by
    have hm' : MeasurableSpace.comap (r ∘ Y) ‹_› ≤ ‹MeasurableSpace Ω› := hrY.comap_le
    rw [← integral_congr_ae (condExp_indicator_comap_ae_eq_condProbGiven hrY hs),
      integral_condExp hm', integral_indicator hs, setIntegral_const, smul_eq_mul, mul_one]
  calc ∫ ω, e ω * (c' ω / c ω) ∂μ = ∫ ω, q ω * c ω ∂μ := h1
    _ ≤ ∫ ω, c' ω ∂μ := integral_mono hqci hc'i h2
    _ = μ.real s := h3

/-- The integrand of `MeasureTheory.integral_indicator_mul_div_condProbGiven_le` is integrable:
it takes finitely many values. -/
lemma integrable_indicator_mul_div_condProbGiven [Finite T] [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T'] [Finite T'] [IsFiniteMeasure μ]
    {Y : Ω → T} (hY : Measurable Y) (r : T → T') {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω ↦ s.indicator (fun _ ↦ (1 : ℝ)) ω *
      (condProbGiven μ (r ∘ Y) s ω / condProbGiven μ Y s ω)) μ := by
  have hm : MeasurableSpace.comap Y ‹_› ≤ ‹MeasurableSpace Ω› := hY.comap_le
  refine integrable_of_finite_range
    ((measurable_const.indicator hs).mul
      (((measurable_comap_condProbGiven_comp Y r s).mono hm le_rfl).div
        ((measurable_comap_condProbGiven Y s).mono hm le_rfl))) ?_
  exact Set.finite_range₂ (· * ·) (Set.finite_range_indicator_one s)
    (Set.finite_range₂ (· / ·) (finite_range_condProbGiven (r ∘ Y) s)
      (finite_range_condProbGiven Y s))

end CondProbGiven

/-! ### Blocks of a stationary random field -/

section Block

variable {G Ω E : Type*} [AddCommGroup G] [DecidableEq G] [AddAction G Ω] [MeasurableSpace Ω]
  {μ : Measure Ω} [MeasurableSpace E] (X : Ω → E)

/-- The *block* `X_Λ ω = (X (i +ᵥ ω))_{i ∈ Λ}` of the stationary random field `i ↦ X (i +ᵥ ·)`
on the finite set of sites `Λ`. -/
def blockMap (Λ : Finset G) (ω : Ω) : Λ → E := fun i ↦ X ((i : G) +ᵥ ω)

omit [DecidableEq G] in
lemma measurable_blockMap [MeasurableConstVAdd G Ω] (hX : Measurable X) (Λ : Finset G) :
    Measurable (blockMap X Λ) :=
  measurable_pi_iff.2 fun i ↦ hX.comp (measurable_const_vadd (i : G))

omit [DecidableEq G] [MeasurableSpace Ω] [MeasurableSpace E] in
lemma mem_blockMap_preimage_singleton {Λ : Finset G} {ω η : Ω} :
    η ∈ blockMap X Λ ⁻¹' {blockMap X Λ ω} ↔ ∀ i ∈ Λ, X (i +ᵥ η) = X (i +ᵥ ω) := by
  simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff, Subtype.forall]
  rfl

omit [DecidableEq G] [MeasurableSpace Ω] [MeasurableSpace E] in
lemma blockMap_preimage_singleton_antitone {Λ Λ' : Finset G} (h : Λ ⊆ Λ') (ω : Ω) :
    blockMap X Λ' ⁻¹' {blockMap X Λ' ω} ⊆ blockMap X Λ ⁻¹' {blockMap X Λ ω} := fun _ hη ↦
  (mem_blockMap_preimage_singleton X).2 fun i hi ↦
    (mem_blockMap_preimage_singleton X).1 hη i (h hi)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
lemma blockMap_preimage_singleton_insert (a : G) (Λ : Finset G) (ω : Ω) :
    blockMap X (insert a Λ) ⁻¹' {blockMap X (insert a Λ) ω}
      = blockMap X Λ ⁻¹' {blockMap X Λ ω} ∩ {η | X (a +ᵥ η) = X (a +ᵥ ω)} := by
  ext η
  simp only [mem_blockMap_preimage_singleton, Finset.mem_insert, forall_eq_or_imp,
    Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_comm

variable (μ) in
/-- The *block probability* `p_Λ ω = μ(X_Λ = X_Λ ω)` of the block of `ω` on `Λ`. -/
noncomputable def blockProb (Λ : Finset G) (ω : Ω) : ℝ :=
  μ.real (blockMap X Λ ⁻¹' {blockMap X Λ ω})

omit [DecidableEq G] [MeasurableSpace E] in
lemma blockProb_nonneg (Λ : Finset G) (ω : Ω) : 0 ≤ blockProb μ X Λ ω := measureReal_nonneg

omit [DecidableEq G] [MeasurableSpace E] in
lemma blockProb_le_one [IsProbabilityMeasure μ] (Λ : Finset G) (ω : Ω) :
    blockProb μ X Λ ω ≤ 1 := by
  rw [blockProb, ← probReal_univ (μ := μ)]
  exact measureReal_mono (subset_univ _)

omit [DecidableEq G] [MeasurableSpace E] in
lemma blockProb_anti [IsFiniteMeasure μ] {Λ Λ' : Finset G} (h : Λ ⊆ Λ') (ω : Ω) :
    blockProb μ X Λ' ω ≤ blockProb μ X Λ ω :=
  measureReal_mono (blockMap_preimage_singleton_antitone X h ω)

omit [DecidableEq G] [MeasurableSpace E] in
@[simp] lemma blockProb_empty [IsProbabilityMeasure μ] (ω : Ω) :
    blockProb μ X (∅ : Finset G) ω = 1 := by
  rw [blockProb, ← probReal_univ (μ := μ)]
  congr
  ext η
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  funext i
  exact absurd i.2 (Finset.notMem_empty _)

omit [DecidableEq G] [MeasurableSpace E] in
/-- The block probability factors through the block. -/
lemma blockProb_eq_comp (Λ : Finset G) :
    blockProb μ X Λ = (fun ζ ↦ μ.real (blockMap X Λ ⁻¹' {ζ})) ∘ blockMap X Λ := rfl

omit [DecidableEq G] in
lemma measurable_blockProb [MeasurableConstVAdd G Ω] [Finite E] [MeasurableSingletonClass E]
    (hX : Measurable X) (Λ : Finset G) : Measurable (blockProb μ X Λ) :=
  (measurable_of_finite fun ζ : Λ → E ↦ μ.real (blockMap X Λ ⁻¹' {ζ})).comp
    (measurable_blockMap X hX Λ)

omit [DecidableEq G] in
/-- Any function of a block is integrable: it takes finitely many values. -/
lemma integrable_comp_blockMap [MeasurableConstVAdd G Ω] [Finite E] [MeasurableSingletonClass E]
    [IsFiniteMeasure μ] (hX : Measurable X) (Λ : Finset G) (f : (Λ → E) → ℝ) :
    Integrable (f ∘ blockMap X Λ) μ :=
  (integrable_map_measure (measurable_of_finite f).aestronglyMeasurable
    (measurable_blockMap X hX Λ).aemeasurable).1 Integrable.of_finite

omit [DecidableEq G] [MeasurableSpace E] in
/-- Almost surely the block of `ω` has positive probability. -/
lemma ae_blockProb_pos [Finite E] [IsFiniteMeasure μ] (Λ : Finset G) :
    ∀ᵐ ω ∂μ, 0 < blockProb μ X Λ ω := by
  have hsub : {ω | ¬ 0 < blockProb μ X Λ ω} ⊆
      ⋃ ζ ∈ {ζ : Λ → E | μ (blockMap X Λ ⁻¹' {ζ}) = 0}, blockMap X Λ ⁻¹' {ζ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, not_lt] at hω
    have h0 : μ.real (blockMap X Λ ⁻¹' {blockMap X Λ ω}) = 0 :=
      le_antisymm hω measureReal_nonneg
    have hz : μ.real (blockMap X Λ ⁻¹' {blockMap X Λ ω}) = 0 ↔
        μ (blockMap X Λ ⁻¹' {blockMap X Λ ω}) = 0 := measureReal_eq_zero_iff
    exact Set.mem_biUnion (hz.1 h0) rfl
  rw [ae_iff]
  exact measure_mono_null hsub
    ((measure_biUnion_null_iff (Set.to_countable _)).2 fun ζ hζ ↦ hζ)

/-- **Stationarity of the block probabilities**: `p_Λ (i +ᵥ ω) = p_{i +ᵥ Λ} ω`. -/
lemma blockProb_vadd [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ]
    [Finite E] [MeasurableSingletonClass E] (hX : Measurable X) (Λ : Finset G) (i : G) (ω : Ω) :
    blockProb μ X Λ (i +ᵥ ω) = blockProb μ X (i +ᵥ Λ) ω := by
  have hset : blockMap X Λ ⁻¹' {blockMap X Λ (i +ᵥ ω)}
      = (fun η ↦ (-i) +ᵥ η) ⁻¹' (blockMap X (i +ᵥ Λ) ⁻¹' {blockMap X (i +ᵥ Λ) ω}) := by
    ext η
    change η ∈ blockMap X Λ ⁻¹' {blockMap X Λ (i +ᵥ ω)} ↔
      (-i) +ᵥ η ∈ blockMap X (i +ᵥ Λ) ⁻¹' {blockMap X (i +ᵥ Λ) ω}
    rw [mem_blockMap_preimage_singleton, mem_blockMap_preimage_singleton]
    simp only [Finset.mem_vadd_finset, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      vadd_vadd, vadd_eq_add, add_comm i, add_neg_cancel_right]
  rw [blockProb, hset, measureReal_def, VAddInvariantMeasure.measure_preimage_vadd _
    ((measurable_blockMap X hX _) (measurableSet_singleton _))]
  rfl


omit [DecidableEq G] [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The block on `W'` is a function of the block on a larger set `W`. -/
lemma blockMap_eq_comp_of_subset {W W' : Finset G} (h : W' ⊆ W) :
    blockMap X W' = (fun ζ : W → E ↦ fun i : W' ↦ ζ ⟨i, h i.2⟩) ∘ blockMap X W := rfl

omit [DecidableEq G] [MeasurableSpace E] in
/-- A block probability takes finitely many values. -/
lemma finite_range_blockProb [Finite E] (Λ : Finset G) :
    (Set.range (blockProb μ X Λ)).Finite :=
  Set.finite_range_comp_of_finite (blockMap X Λ) fun ζ ↦ μ.real (blockMap X Λ ⁻¹' {ζ})

omit [DecidableEq G] in
/-- The logarithm of a block probability is integrable: it takes finitely many values. -/
lemma integrable_log_blockProb [MeasurableConstVAdd G Ω] [Finite E] [MeasurableSingletonClass E]
    [IsFiniteMeasure μ] (hX : Measurable X) (Λ : Finset G) :
    Integrable (fun ω ↦ Real.log (blockProb μ X Λ ω)) μ :=
  integrable_of_finite_range (Real.measurable_log.comp (measurable_blockProb X hX Λ))
    (Set.finite_range_comp (finite_range_blockProb X Λ) Real.log)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The fibre of the block on `insert 0 W` is the fibre of the block on `W` intersected with the
event that the spin at the origin takes the value it has at `ω`. -/
lemma blockMap_preimage_singleton_insert_zero (W : Finset G) (ω : Ω) :
    blockMap X (insert 0 W) ⁻¹' {blockMap X (insert 0 W) ω}
      = blockMap X W ⁻¹' {blockMap X W ω} ∩ X ⁻¹' {X ω} := by
  rw [blockMap_preimage_singleton_insert]
  congr 1
  ext η
  simp only [Set.mem_ofPred_eq, zero_vadd, Set.mem_preimage, Set.mem_singleton_iff]

omit [MeasurableSpace E] in
/-- **The conditional probability of the spin at the origin given a block**:
`μ(X_0 = X_0 ω | X_W = X_W ω) = p_{W ∪ {0}} ω / p_W ω`. -/
lemma condProbGiven_blockMap_eq_div (W : Finset G) (ω : Ω) :
    condProbGiven μ (blockMap X W) (X ⁻¹' {X ω}) ω
      = blockProb μ X (insert 0 W) ω / blockProb μ X W ω := by
  rw [condProbGiven, blockProb, blockProb, ← blockMap_preimage_singleton_insert_zero]

end Block

/-! ### The conditional information of the present given a window of the past -/

section CondInformation

variable {G Ω E : Type*} [AddCommGroup G] [DecidableEq G] [AddAction G Ω] [MeasurableSpace Ω]
  {μ : Measure Ω} [MeasurableSpace E] (X : Ω → E)

variable (μ) in
/-- The *conditional information* of the spin at the origin given the block on the set of sites
`W`: `g_W ω = log p_W ω - log p_{W ∪ {0}} ω`, which almost surely equals
`-log μ(X_0 = X_0 ω | X_W = X_W ω) ≥ 0`. -/
noncomputable def condInformation (μ : Measure Ω) (X : Ω → E) (W : Finset G) (ω : Ω) : ℝ :=
  Real.log (blockProb μ X W ω) - Real.log (blockProb μ X (insert 0 W) ω)

lemma measurable_condInformation [MeasurableConstVAdd G Ω] [Finite E] [MeasurableSingletonClass E]
    (hX : Measurable X) (W : Finset G) : Measurable (condInformation μ X W) :=
  (Real.measurable_log.comp (measurable_blockProb X hX W)).sub
    (Real.measurable_log.comp (measurable_blockProb X hX (insert 0 W)))

omit [MeasurableSpace E] in
lemma finite_range_condInformation [Finite E] (W : Finset G) :
    (Set.range (condInformation μ X W)).Finite :=
  Set.finite_range₂ (fun a b ↦ Real.log a - Real.log b) (finite_range_blockProb X W)
    (finite_range_blockProb X (insert 0 W))

lemma integrable_condInformation [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsFiniteMeasure μ] (hX : Measurable X) (W : Finset G) :
    Integrable (condInformation μ X W) μ :=
  integrable_of_finite_range (measurable_condInformation X hX W)
    (finite_range_condInformation X W)

omit [MeasurableSpace E] in
/-- **The conditional information is minus the log conditional probability of the observed spin**,
almost surely: `g_W ω = -log μ(X_0 = X_0 ω | X_W = X_W ω)`. -/
lemma condInformation_ae_eq_neg_log_condProbGiven [Finite E] [IsFiniteMeasure μ] (W : Finset G) :
    ∀ᵐ ω ∂μ, condInformation μ X W ω
      = -Real.log (condProbGiven μ (blockMap X W) (X ⁻¹' {X ω}) ω) := by
  filter_upwards [ae_blockProb_pos X W, ae_blockProb_pos X (insert 0 W)] with ω ha hb
  rw [condProbGiven_blockMap_eq_div, Real.log_div hb.ne' ha.ne', condInformation]
  ring

omit [MeasurableSpace E] in
/-- The conditional information is almost surely nonnegative: conditioning cannot make a
configuration more likely than its own restriction. -/
lemma condInformation_nonneg_ae [Finite E] [IsFiniteMeasure μ] (W : Finset G) :
    ∀ᵐ ω ∂μ, 0 ≤ condInformation μ X W ω := by
  filter_upwards [ae_blockProb_pos X (insert 0 W)] with ω hω
  rw [condInformation, sub_nonneg]
  exact Real.log_le_log hω (blockProb_anti X (Finset.subset_insert 0 W) ω)

/-- **Stationarity of the conditional information**: `g_W (i +ᵥ ω)` is the increment of the
log-block-probabilities of `i +ᵥ W` at `ω`. -/
lemma condInformation_vadd [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [Finite E]
    [MeasurableSingletonClass E] (hX : Measurable X) (W : Finset G) (i : G) (ω : Ω) :
    condInformation μ X W (i +ᵥ ω)
      = Real.log (blockProb μ X (i +ᵥ W) ω)
        - Real.log (blockProb μ X (i +ᵥ insert 0 W) ω) := by
  rw [condInformation, blockProb_vadd X hX W i ω, blockProb_vadd X hX (insert 0 W) i ω]


omit [MeasurableSpace E] in
lemma finite_range_exp_condInformation_sub [Finite E] (W W' : Finset G) :
    (Set.range fun ω ↦ Real.exp (condInformation μ X W ω - condInformation μ X W' ω)).Finite :=
  Set.finite_range₂ (fun a b ↦ Real.exp (a - b)) (finite_range_condInformation X W)
    (finite_range_condInformation X W')

lemma integrable_exp_condInformation_sub [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsFiniteMeasure μ] (hX : Measurable X) (W W' : Finset G) :
    Integrable (fun ω ↦ Real.exp (condInformation μ X W ω - condInformation μ X W' ω)) μ :=
  integrable_of_finite_range
    (Real.measurable_exp.comp
      ((measurable_condInformation X hX W).sub (measurable_condInformation X hX W')))
    (finite_range_exp_condInformation_sub X W W')

/-- **Conditioning on more can only reduce the information, in the mean.** For `W' ⊆ W`,
`∫ exp (g_W - g_{W'}) dμ ≤ 1`. Almost surely the integrand is the ratio
`μ(X_0 = X_0 ω | X_{W'} = X_{W'} ω) / μ(X_0 = X_0 ω | X_W = X_W ω)` of the conditional
probabilities of the spin at the origin, and the bound is
`MeasureTheory.integral_indicator_mul_div_condProbGiven_le` summed over the values of the spin. -/
theorem integral_exp_condInformation_sub_le_one [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsProbabilityMeasure μ] (hX : Measurable X)
    {W W' : Finset G} (hWW' : W' ⊆ W) :
    ∫ ω, Real.exp (condInformation μ X W ω - condInformation μ X W' ω) ∂μ ≤ 1 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  set r : (W → E) → (W' → E) := fun ζ i ↦ ζ ⟨i, hWW' i.2⟩ with hrdef
  have hcomp : r ∘ blockMap X W = blockMap X W' := (blockMap_eq_comp_of_subset X hWW').symm
  have hbW : Measurable (blockMap X W) := measurable_blockMap X hX W
  have hAx : ∀ x : E, MeasurableSet (X ⁻¹' {x}) := fun x ↦ hX (measurableSet_singleton x)
  have hint : ∀ x : E, Integrable (fun ω ↦ (X ⁻¹' {x}).indicator (fun _ ↦ (1 : ℝ)) ω *
      (condProbGiven μ (r ∘ blockMap X W) (X ⁻¹' {x}) ω /
        condProbGiven μ (blockMap X W) (X ⁻¹' {x}) ω)) μ := fun x ↦
    integrable_indicator_mul_div_condProbGiven hbW r (hAx x)
  have key : ∀ᵐ ω ∂μ, Real.exp (condInformation μ X W ω - condInformation μ X W' ω)
      = ∑ x : E, (X ⁻¹' {x}).indicator (fun _ ↦ (1 : ℝ)) ω *
          (condProbGiven μ (r ∘ blockMap X W) (X ⁻¹' {x}) ω /
            condProbGiven μ (blockMap X W) (X ⁻¹' {x}) ω) := by
    filter_upwards [ae_blockProb_pos X W, ae_blockProb_pos X (insert 0 W),
      ae_blockProb_pos X W', ae_blockProb_pos X (insert 0 W')] with ω ha hb ha' hb'
    have ha0 : blockProb μ X W ω ≠ 0 := ha.ne'
    have hb0 : blockProb μ X (insert 0 W) ω ≠ 0 := hb.ne'
    have ha0' : blockProb μ X W' ω ≠ 0 := ha'.ne'
    have hb0' : blockProb μ X (insert 0 W') ω ≠ 0 := hb'.ne'
    have hsum : (∑ x : E, (X ⁻¹' {x}).indicator (fun _ ↦ (1 : ℝ)) ω *
        (condProbGiven μ (r ∘ blockMap X W) (X ⁻¹' {x}) ω /
          condProbGiven μ (blockMap X W) (X ⁻¹' {x}) ω))
        = condProbGiven μ (r ∘ blockMap X W) (X ⁻¹' {X ω}) ω /
          condProbGiven μ (blockMap X W) (X ⁻¹' {X ω}) ω := by
      rw [Finset.sum_eq_single (X ω)]
      · rw [Set.indicator_of_mem (show ω ∈ X ⁻¹' {X ω} from rfl), one_mul]
      · intro x _ hx
        rw [Set.indicator_of_notMem (by
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          exact fun h ↦ hx h.symm), zero_mul]
      · intro hx
        exact absurd (Finset.mem_univ _) hx
    rw [hsum, hcomp, condProbGiven_blockMap_eq_div X W' ω, condProbGiven_blockMap_eq_div X W ω,
      condInformation, condInformation,
      show Real.log (blockProb μ X W ω) - Real.log (blockProb μ X (insert 0 W) ω)
          - (Real.log (blockProb μ X W' ω) - Real.log (blockProb μ X (insert 0 W') ω))
          = Real.log (blockProb μ X W ω) + Real.log (blockProb μ X (insert 0 W') ω)
            - (Real.log (blockProb μ X (insert 0 W) ω) + Real.log (blockProb μ X W' ω)) from by
        ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
      Real.exp_log ha', Real.exp_log hb']
    field_simp
  rw [integral_congr_ae key, integral_finsetSum _ fun x _ ↦ hint x]
  calc ∑ x : E, ∫ ω, (X ⁻¹' {x}).indicator (fun _ ↦ (1 : ℝ)) ω *
        (condProbGiven μ (r ∘ blockMap X W) (X ⁻¹' {x}) ω /
          condProbGiven μ (blockMap X W) (X ⁻¹' {x}) ω) ∂μ
      ≤ ∑ x : E, μ.real (X ⁻¹' {x}) :=
        Finset.sum_le_sum fun x _ ↦ integral_indicator_mul_div_condProbGiven_le hbW r (hAx x)
    _ = 1 := by
        rw [sum_measureReal_preimage_singleton _ fun y _ ↦ hAx y]
        simp

/-- **Conditioning on more does not increase the mean information**: for `W' ⊆ W`,
`∫ g_W dμ ≤ ∫ g_{W'} dμ`. This is Jensen's inequality applied to
`MeasureTheory.integral_exp_condInformation_sub_le_one`. -/
theorem integral_condInformation_mono [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsProbabilityMeasure μ] (hX : Measurable X)
    {W W' : Finset G} (hWW' : W' ⊆ W) :
    ∫ ω, condInformation μ X W ω ∂μ ≤ ∫ ω, condInformation μ X W' ω ∂μ := by
  have hiW := integrable_condInformation (μ := μ) X hX W
  have hiW' := integrable_condInformation (μ := μ) X hX W'
  have hi : Integrable (fun ω ↦ condInformation μ X W ω - condInformation μ X W' ω) μ :=
    hiW.sub hiW'
  have h1 : ∫ ω, (1 + (condInformation μ X W ω - condInformation μ X W' ω)) ∂μ
      ≤ ∫ ω, Real.exp (condInformation μ X W ω - condInformation μ X W' ω) ∂μ :=
    integral_mono ((integrable_const (μ := μ) (1 : ℝ)).add hi)
      (integrable_exp_condInformation_sub X hX W W') fun ω ↦ by
        simpa [add_comm] using Real.add_one_le_exp
          (condInformation μ X W ω - condInformation μ X W' ω)
  have h2 := integral_exp_condInformation_sub_le_one (μ := μ) X hX hWW'
  rw [integral_add (integrable_const (μ := μ) (1 : ℝ)) hi, integral_sub hiW hiW'] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  linarith


/-- **The `L¹` distance between two conditional informations is controlled by the entropy drop.**
For `W' ⊆ W` and every `δ > 0`,
`∫ |g_W - g_{W'}| dμ ≤ 2δ + (1 + 2/δ) (∫ g_{W'} dμ - ∫ g_W dμ)`. -/
theorem integral_abs_condInformation_sub_le [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsProbabilityMeasure μ] (hX : Measurable X)
    {W W' : Finset G} (hWW' : W' ⊆ W) {δ : ℝ} (hδ : 0 < δ) :
    ∫ ω, |condInformation μ X W ω - condInformation μ X W' ω| ∂μ
      ≤ 2 * δ + (1 + 2 / δ) *
        (∫ ω, condInformation μ X W' ω ∂μ - ∫ ω, condInformation μ X W ω ∂μ) := by
  have hiW := integrable_condInformation (μ := μ) X hX W
  have hiW' := integrable_condInformation (μ := μ) X hX W'
  have hu : Integrable (fun ω ↦ condInformation μ X W ω - condInformation μ X W' ω) μ :=
    hiW.sub hiW'
  have h := integral_abs_le_of_integral_exp_le_one hu
    (integrable_exp_condInformation_sub X hX W W')
    (integral_exp_condInformation_sub_le_one (μ := μ) X hX hWW') hδ
  rwa [integral_sub hiW hiW', neg_sub] at h

end CondInformation

/-! ### The entropy rate -/

section EntropyRate

variable {G Ω E : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [DecidableEq G]
  [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableSpace E] (X : Ω → E)

variable (G μ) in
/-- The *entropy rate* of the stationary random field `i ↦ X (i +ᵥ ·)`:
`h = inf_W ∫ g_W dμ`, the infimum of the mean conditional information `H(X_0 | X_W)` over the
finite windows `W` of the past `{i | i < 0}` of the translation-invariant order of `G`. For `ℤ^d`
with the lexicographic order this is Georgii's specific entropy relative to counting measure,
by (15.16). -/
noncomputable def entropyRate : ℝ :=
  ⨅ W : {W : Finset G // ∀ i ∈ W, i < (0 : G)}, ∫ ω, condInformation μ X W.1 ω ∂μ

omit [IsOrderedAddMonoid G] [MeasurableSpace E] in
lemma bddBelow_range_integral_condInformation [Finite E] [IsFiniteMeasure μ] :
    BddBelow (Set.range fun W : {W : Finset G // ∀ i ∈ W, i < (0 : G)} ↦
      ∫ ω, condInformation μ X W.1 ω ∂μ) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨W, rfl⟩
  exact integral_nonneg_of_ae (condInformation_nonneg_ae X W.1)

omit [IsOrderedAddMonoid G] [MeasurableSpace E] in
/-- The entropy rate is a lower bound for the mean conditional information of every finite
window of the past. -/
lemma entropyRate_le_integral_condInformation [Finite E] [IsFiniteMeasure μ] {W : Finset G}
    (hW : ∀ i ∈ W, i < (0 : G)) :
    entropyRate G μ X ≤ ∫ ω, condInformation μ X W ω ∂μ :=
  ciInf_le (bddBelow_range_integral_condInformation X) (⟨W, hW⟩ :
    {W : Finset G // ∀ i ∈ W, i < (0 : G)})

omit [IsOrderedAddMonoid G] [MeasurableSpace E] in
/-- The entropy rate is nonnegative. -/
lemma entropyRate_nonneg [Finite E] [IsFiniteMeasure μ] : 0 ≤ entropyRate G μ X := by
  have : Nonempty {W : Finset G // ∀ i ∈ W, i < (0 : G)} := ⟨⟨∅, by simp⟩⟩
  exact le_ciInf fun W ↦ integral_nonneg_of_ae (condInformation_nonneg_ae X W.1)

omit [IsOrderedAddMonoid G] [MeasurableSpace E] in
/-- The infimum defining the entropy rate is approached by finite windows of the past. -/
lemma exists_integral_condInformation_lt [Finite E] [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ W : Finset G, (∀ i ∈ W, i < (0 : G)) ∧
      ∫ ω, condInformation μ X W ω ∂μ < entropyRate G μ X + ε := by
  have : Nonempty {W : Finset G // ∀ i ∈ W, i < (0 : G)} := ⟨⟨∅, by simp⟩⟩
  obtain ⟨W, hW⟩ := exists_lt_of_ciInf_lt (f := fun W : {W : Finset G // ∀ i ∈ W, i < (0 : G)} ↦
    ∫ ω, condInformation μ X W.1 ω ∂μ) (by linarith : entropyRate G μ X < entropyRate G μ X + ε)
  exact ⟨W.1, W.2, hW⟩

omit [IsOrderedAddMonoid G] in
/-- **A single window of the past approximates all larger ones, uniformly in `L¹`.** For every
`ε > 0` there is a finite window `W₀` of the past whose mean conditional information is within `ε`
of the entropy rate and which is within `ε` in `L¹` of the conditional information of *every*
larger finite window of the past. This is the uniformity that the chain rule needs: the windows
`W_i` produced by the sites of a large volume all contain `W₀`, but they vary with the site. -/
theorem exists_forall_integral_abs_condInformation_sub_le [MeasurableConstVAdd G Ω] [Finite E]
    [MeasurableSingletonClass E] [IsProbabilityMeasure μ] (hX : Measurable X) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ W₀ : Finset G, (∀ i ∈ W₀, i < (0 : G)) ∧
      ∫ ω, condInformation μ X W₀ ω ∂μ ≤ entropyRate G μ X + ε ∧
      ∀ W : Finset G, (∀ i ∈ W, i < (0 : G)) → W₀ ⊆ W →
        ∫ ω, |condInformation μ X W ω - condInformation μ X W₀ ω| ∂μ ≤ ε := by
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hc : 0 < 1 + 2 / δ := by positivity
  set η : ℝ := min ε (ε / (2 * (1 + 2 / δ))) with hηdef
  have hη : 0 < η := lt_min hε (by positivity)
  obtain ⟨W₀, hW₀, hW₀lt⟩ := exists_integral_condInformation_lt (G := G) (μ := μ) X hη
  refine ⟨W₀, hW₀, ?_, fun W hW hsub ↦ ?_⟩
  · exact le_trans hW₀lt.le (by gcongr; exact min_le_left _ _)
  · have h1 : entropyRate G μ X ≤ ∫ ω, condInformation μ X W ω ∂μ :=
      entropyRate_le_integral_condInformation X hW
    have h2 : ∫ ω, condInformation μ X W₀ ω ∂μ - ∫ ω, condInformation μ X W ω ∂μ ≤ η := by
      linarith
    have h3 := integral_abs_condInformation_sub_le (μ := μ) X hX hsub hδ
    have h4 : (1 + 2 / δ) * (∫ ω, condInformation μ X W₀ ω ∂μ
        - ∫ ω, condInformation μ X W ω ∂μ) ≤ (1 + 2 / δ) * (ε / (2 * (1 + 2 / δ))) := by
      gcongr
      exact h2.trans (min_le_right _ _)
    have h5 : (1 + 2 / δ) * (ε / (2 * (1 + 2 / δ))) = ε / 2 := by
      field_simp
    have h6 : 2 * δ = ε / 2 := by rw [hδdef]; ring
    linarith

end EntropyRate

/-! ### The chain rule -/

section ChainRule

variable {G Ω E : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [DecidableEq G]
  [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableSpace E] (X : Ω → E)

variable (G) in
/-- The *window of the past seen from the site `i` inside the volume `Λ`*:
`W_i(Λ) = (Λ ∩ {j | j < i}) - i`, a finite subset of the past `{j | j < 0}`. -/
def pastWindow (Λ : Finset G) (i : G) : Finset G := (-i) +ᵥ Λ.filter (· < i)

omit [IsOrderedAddMonoid G] in
@[simp] lemma mem_pastWindow {Λ : Finset G} {i j : G} :
    j ∈ pastWindow G Λ i ↔ i + j ∈ Λ ∧ i + j < i := by
  simp only [pastWindow, Finset.mem_vadd_finset, Finset.mem_filter, vadd_eq_add]
  constructor
  · rintro ⟨x, ⟨hx, hxi⟩, rfl⟩
    simpa [add_neg_cancel_left] using ⟨hx, hxi⟩
  · rintro ⟨hj, hji⟩
    exact ⟨i + j, ⟨hj, hji⟩, by simp⟩

/-- A window of the past really lies in the past. -/
lemma pastWindow_lt_zero {Λ : Finset G} {i j : G} (hj : j ∈ pastWindow G Λ i) : j < 0 :=
  lt_of_add_lt_add_left (a := i) (by simpa using (mem_pastWindow.1 hj).2)

/-- If the translate `i + W₀` of a window `W₀` of the past fits inside `Λ`, then `W₀` is contained
in the window of the past seen from `i` inside `Λ`. -/
lemma subset_pastWindow {Λ W₀ : Finset G} {i : G} (hW₀ : ∀ j ∈ W₀, j < (0 : G))
    (h : i +ᵥ W₀ ⊆ Λ) : W₀ ⊆ pastWindow G Λ i := by
  intro j hj
  refine mem_pastWindow.2 ⟨h (Finset.mem_vadd_finset.2 ⟨j, hj, rfl⟩), ?_⟩
  simpa using add_lt_add_left (hW₀ j hj) i

omit [IsOrderedAddMonoid G] in
/-- **The chain rule for block probabilities.** Enumerating `Λ` in increasing order and
telescoping, `-log p_Λ ω = ∑_{i ∈ Λ} g_{W_i(Λ)} (i +ᵥ ω)`, where `W_i(Λ) = (Λ ∩ {j < i}) - i` is
the window of the past seen from `i`. The identity is exact, with no null sets: it is the
telescoping of `log p_{Λ ∩ {j < i}} - log p_{Λ ∩ {j ≤ i}}` together with the stationarity
`p_Λ (i +ᵥ ω) = p_{i +ᵥ Λ} ω`. -/
theorem neg_log_blockProb_eq_sum_condInformation [MeasurableConstVAdd G Ω]
    [VAddInvariantMeasure G Ω μ] [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (hX : Measurable X) (Λ : Finset G) (ω : Ω) :
    -Real.log (blockProb μ X Λ ω)
      = ∑ i ∈ Λ, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω) := by
  induction Λ using Finset.strongInduction with
  | _ Λ ih =>
    rcases Λ.eq_empty_or_nonempty with rfl | hne
    · simp
    · have ha : Λ.max' hne ∈ Λ := Λ.max'_mem hne
      have hle : ∀ j ∈ Λ, j ≤ Λ.max' hne := fun j hj ↦ Λ.le_max' j hj
      have hwin : ∀ i ∈ Λ.erase (Λ.max' hne),
          pastWindow G Λ i = pastWindow G (Λ.erase (Λ.max' hne)) i := by
        intro i hi
        have hia : i ≠ Λ.max' hne := Finset.ne_of_mem_erase hi
        have hiΛ : i ∈ Λ := Finset.mem_of_mem_erase hi
        have : Λ.filter (· < i) = (Λ.erase (Λ.max' hne)).filter (· < i) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase]
          exact ⟨fun ⟨hjΛ, hji⟩ ↦ ⟨⟨fun hj ↦ absurd (hle i hiΛ) (not_le.2 (hj ▸ hji)), hjΛ⟩, hji⟩,
            fun ⟨⟨_, hjΛ⟩, hji⟩ ↦ ⟨hjΛ, hji⟩⟩
        rw [pastWindow, pastWindow, this]
      have hwa : pastWindow G Λ (Λ.max' hne) = (-Λ.max' hne) +ᵥ Λ.erase (Λ.max' hne) := by
        have : Λ.filter (· < Λ.max' hne) = Λ.erase (Λ.max' hne) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_erase]
          exact ⟨fun ⟨hjΛ, hja⟩ ↦ ⟨ne_of_lt hja, hjΛ⟩,
            fun ⟨hja, hjΛ⟩ ↦ ⟨hjΛ, lt_of_le_of_ne (hle j hjΛ) hja⟩⟩
        rw [pastWindow, this]
      have hvadd1 : (Λ.max' hne) +ᵥ ((-Λ.max' hne) +ᵥ Λ.erase (Λ.max' hne))
          = Λ.erase (Λ.max' hne) := by
        ext j
        simp only [Finset.mem_vadd_finset, vadd_eq_add]
        exact ⟨by rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩; simpa using hy,
          fun hj ↦ ⟨-Λ.max' hne + j, ⟨j, hj, rfl⟩, by simp⟩⟩
      have hvadd2 : (Λ.max' hne) +ᵥ insert 0 ((-Λ.max' hne) +ᵥ Λ.erase (Λ.max' hne)) = Λ := by
        ext j
        simp only [Finset.mem_vadd_finset, Finset.mem_insert, vadd_eq_add]
        constructor
        · rintro ⟨x, hx | ⟨y, hy, rfl⟩, rfl⟩
          · rw [hx, add_zero]; exact ha
          · simpa using Finset.mem_of_mem_erase hy
        · intro hj
          rcases eq_or_ne j (Λ.max' hne) with rfl | hja
          · exact ⟨0, Or.inl rfl, by simp⟩
          · exact ⟨-Λ.max' hne + j, Or.inr ⟨j, Finset.mem_erase.2 ⟨hja, hj⟩, rfl⟩, by simp⟩
      rw [← Finset.sum_erase_add Λ _ ha,
        Finset.sum_congr rfl (fun i hi ↦ by rw [hwin i hi]),
        ← ih (Λ.erase (Λ.max' hne)) (Finset.erase_ssubset ha), hwa,
        condInformation_vadd X hX _ (Λ.max' hne) ω, hvadd1, hvadd2]
      ring

end ChainRule

/-! ### The Shannon–McMillan theorem -/

section ShannonMcMillan

variable {G Ω E : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [DecidableEq G]
  [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableSpace E] (X : Ω → E)
  {κ : Type*} {l : Filter κ} {F : κ → Finset G}

omit [LinearOrder G] [IsOrderedAddMonoid G] [AddAction G Ω] [MeasurableSpace Ω] [MeasurableSpace E]
  X in
/-- Along a Følner net, the fraction of the sites `i` of `F k` whose translate `i + W₀` of a fixed
finite set of sites is not contained in `F k` tends to `0`. -/
lemma tendsto_card_filter_vadd_not_subset_div_card
    (hFol : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (W₀ : Finset G) :
    Tendsto (fun k ↦ (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card) l (𝓝 0) := by
  refine squeeze_zero (fun k ↦ by positivity) (g := fun k ↦
    ∑ w ∈ W₀, ((((-w) +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) (fun k ↦ ?_) ?_
  · have hsub : ((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k)
        ⊆ W₀.biUnion fun w ↦ F k \ ((-w) +ᵥ F k) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      obtain ⟨hiF, hiW⟩ := hi
      rw [Finset.subset_iff] at hiW
      push Not at hiW
      obtain ⟨y, hy, hyF⟩ := hiW
      obtain ⟨w, hw, rfl⟩ := Finset.mem_vadd_finset.1 hy
      refine Finset.mem_biUnion.2 ⟨w, hw, Finset.mem_sdiff.2 ⟨hiF, fun hmem ↦ hyF ?_⟩⟩
      obtain ⟨x, hx, hxi⟩ := Finset.mem_vadd_finset.1 hmem
      have : x = i +ᵥ w := by
        rw [vadd_eq_add] at hxi ⊢
        rw [← hxi]
        abel
      exact this ▸ hx
    have hcards : (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ)
        ≤ ∑ w ∈ W₀, ((((-w) +ᵥ F k) ∆ F k).card : ℝ) := by
      have h1 : ((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card
          ≤ ∑ w ∈ W₀, (((-w) +ᵥ F k) ∆ F k).card := by
        refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
        refine Finset.sum_le_sum fun w _ ↦ Finset.card_le_card fun j hj ↦ ?_
        rw [Finset.mem_sdiff] at hj
        exact Finset.mem_symmDiff.2 (Or.inr ⟨hj.1, hj.2⟩)
      exact_mod_cast h1
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hcards (by positivity)
  · simpa using tendsto_finsetSum W₀ fun w _ ↦ hFol (-w)

/-- **The chain-rule average is `L¹`-close to the ergodic average of a fixed window.** The sites
`i ∈ Λ` with `i + W₀ ⊆ Λ` have `W₀ ⊆ W_i(Λ)`, so their conditional informations are within `ε` of
`g_{W₀}` in `L¹`; the remaining sites contribute at most `M` each. -/
lemma integral_abs_inv_card_sum_condInformation_sub_le [MeasurableConstVAdd G Ω]
    [VAddInvariantMeasure G Ω μ] [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (hX : Measurable X) {W₀ : Finset G} (hW₀ : ∀ i ∈ W₀, i < (0 : G)) {ε M : ℝ}
    (hunif : ∀ W : Finset G, (∀ i ∈ W, i < (0 : G)) → W₀ ⊆ W →
      ∫ ω, |condInformation μ X W ω - condInformation μ X W₀ ω| ∂μ ≤ ε)
    (hbnd : ∀ W : Finset G, ∫ ω, |condInformation μ X W ω - condInformation μ X W₀ ω| ∂μ ≤ M)
    (Λ : Finset G) (hΛ : Λ.Nonempty) :
    ∫ ω, |(Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
        - (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X W₀ (i +ᵥ ω)| ∂μ
      ≤ ε + ((Λ.filter fun i ↦ ¬ i +ᵥ W₀ ⊆ Λ).card : ℝ) / Λ.card * M := by
  have hcard : (0 : ℝ) < (Λ.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hΛ
  have hε0 : 0 ≤ ε := by
    have h := hunif W₀ hW₀ Finset.Subset.rfl
    simpa using h
  have hig : ∀ (W : Finset G) (i : G),
      Integrable (fun ω ↦ condInformation μ X W (i +ᵥ ω)) μ := fun W i ↦
    (measurePreserving_vadd i μ).integrable_comp_of_integrable
      (integrable_condInformation (μ := μ) X hX W)
  have hterm : ∀ i : G, Integrable (fun ω ↦ |condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
      - condInformation μ X W₀ (i +ᵥ ω)|) μ := fun i ↦ ((hig _ i).sub (hig _ i)).abs
  have hpt : ∀ ω, |(Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
      - (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X W₀ (i +ᵥ ω)|
      ≤ (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, |condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
        - condInformation μ X W₀ (i +ᵥ ω)| := by
    intro ω
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Λ.card : ℝ)⁻¹),
      ← Finset.sum_sub_distrib]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have hcomp : ∀ i ∈ Λ, ∫ ω, |condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
      - condInformation μ X W₀ (i +ᵥ ω)| ∂μ
      = ∫ ω, |condInformation μ X (pastWindow G Λ i) ω - condInformation μ X W₀ ω| ∂μ :=
    fun i _ ↦ (measurePreserving_vadd i μ).integral_comp (measurableEmbedding_const_vadd i)
      fun ω ↦ |condInformation μ X (pastWindow G Λ i) ω - condInformation μ X W₀ ω|
  have hsplit : ∑ i ∈ Λ, ∫ ω, |condInformation μ X (pastWindow G Λ i) ω
      - condInformation μ X W₀ ω| ∂μ
      ≤ (Λ.card : ℝ) * ε + ((Λ.filter fun i ↦ ¬ i +ᵥ W₀ ⊆ Λ).card : ℝ) * M := by
    rw [← Finset.sum_filter_add_sum_filter_not Λ (fun i ↦ i +ᵥ W₀ ⊆ Λ)]
    gcongr ?_ + ?_
    · refine (Finset.sum_le_card_nsmul _ _ ε fun i hi ↦ ?_).trans ?_
      · exact hunif _ (fun j hj ↦ pastWindow_lt_zero hj)
          (subset_pastWindow hW₀ (Finset.mem_filter.1 hi).2)
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_filter_le Λ fun i ↦ i +ᵥ W₀ ⊆ Λ) hε0
    · refine (Finset.sum_le_card_nsmul _ _ M fun i _ ↦ hbnd _).trans ?_
      rw [nsmul_eq_mul]
  calc ∫ ω, |(Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
        - (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, condInformation μ X W₀ (i +ᵥ ω)| ∂μ
      ≤ ∫ ω, (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, |condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
          - condInformation μ X W₀ (i +ᵥ ω)| ∂μ :=
        integral_mono
          ((((integrable_finsetSum Λ fun i _ ↦ hig (pastWindow G Λ i) i).const_mul _).sub
            (((integrable_finsetSum Λ fun i _ ↦ hig W₀ i)).const_mul _))).abs
          ((integrable_finsetSum Λ fun i _ ↦ hterm i).const_mul _) hpt
    _ = (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, ∫ ω, |condInformation μ X (pastWindow G Λ i) (i +ᵥ ω)
          - condInformation μ X W₀ (i +ᵥ ω)| ∂μ := by
        rw [integral_const_mul, integral_finsetSum Λ fun i _ ↦ hterm i]
    _ = (Λ.card : ℝ)⁻¹ * ∑ i ∈ Λ, ∫ ω, |condInformation μ X (pastWindow G Λ i) ω
          - condInformation μ X W₀ ω| ∂μ := by rw [Finset.sum_congr rfl hcomp]
    _ ≤ (Λ.card : ℝ)⁻¹ *
          ((Λ.card : ℝ) * ε + ((Λ.filter fun i ↦ ¬ i +ᵥ W₀ ⊆ Λ).card : ℝ) * M) := by
        gcongr
    _ = ε + ((Λ.filter fun i ↦ ¬ i +ᵥ W₀ ⊆ Λ).card : ℝ) / Λ.card * M := by
        field_simp


/-- **The Shannon–McMillan theorem**, in its `L¹` (McMillan) form. Let a countable abelian group
`G` with a translation-invariant linear order act on a probability space `(Ω, μ)` by
measure-preserving maps `ω ↦ i +ᵥ ω`, let `X : Ω → E` be measurable into a finite state space, and
assume the action is *ergodic*: every invariant event is null or co-null. Then along every Følner
net `F` of finite volumes the normalised information of the observed block converges in `L¹(μ)` to
the entropy rate:
`∫ | -|F k|⁻¹ log μ(X_{F k} = X_{F k} ω) - h | dμ(ω) → 0`, `h = entropyRate G μ X`.

This is the form used by Georgii, *Gibbs Measures and Phase Transitions*, in the proof of the
large-deviation lower bound (15.47): with `λ` the counting measure on the finite `E`,
`μ(X_Λ = X_Λ ω)` is the density `f_Λ` of `μ|𝓕_Λ` with respect to `λ^Λ`. -/
theorem tendsto_integral_abs_neg_inv_card_mul_log_blockProb_sub_entropyRate [Countable G]
    [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [Finite E] [MeasurableSingletonClass E]
    [IsProbabilityMeasure μ] (hX : Measurable X)
    (herg : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants (Multiplicative G) Ω] A →
      μ A = 0 ∨ μ A = 1)
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω, |(-(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω)))
      - entropyRate G μ X| ∂μ) l (𝓝 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hε' : (0 : ℝ) < ε / 5 := by positivity
  obtain ⟨W₀, hW₀past, hW₀close, hW₀unif⟩ :=
    exists_forall_integral_abs_condInformation_sub_le (G := G) (μ := μ) X hX hε'
  set c : ℝ := ∫ ω, condInformation μ X W₀ ω ∂μ with hcdef
  set M : ℝ := (∫ ω, condInformation μ X (∅ : Finset G) ω ∂μ) + c with hMdef
  have hbnd : ∀ W : Finset G,
      ∫ ω, |condInformation μ X W ω - condInformation μ X W₀ ω| ∂μ ≤ M := by
    intro W
    have hiW := integrable_condInformation (μ := μ) X hX W
    have hiW₀ := integrable_condInformation (μ := μ) X hX W₀
    have h1 : (fun ω ↦ |condInformation μ X W ω - condInformation μ X W₀ ω|)
        ≤ᵐ[μ] fun ω ↦ condInformation μ X W ω + condInformation μ X W₀ ω := by
      filter_upwards [condInformation_nonneg_ae X W, condInformation_nonneg_ae X W₀] with ω h1 h2
      rw [abs_sub_le_iff]
      constructor <;> linarith
    calc ∫ ω, |condInformation μ X W ω - condInformation μ X W₀ ω| ∂μ
        ≤ ∫ ω, (condInformation μ X W ω + condInformation μ X W₀ ω) ∂μ :=
          integral_mono_ae (hiW.sub hiW₀).abs (hiW.add hiW₀) h1
      _ = (∫ ω, condInformation μ X W ω ∂μ) + c := integral_add hiW hiW₀
      _ ≤ M := by
          rw [hMdef]
          linarith [integral_condInformation_mono (μ := μ) X hX (Finset.empty_subset W)]
  have hch : |c - entropyRate G μ X| ≤ ε / 5 := by
    have h1 : entropyRate G μ X ≤ c :=
      entropyRate_le_integral_condInformation (μ := μ) X hW₀past
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hcond : μ[condInformation μ X W₀ |
      MeasurableSpace.smulInvariants (Multiplicative G) Ω] =ᵐ[μ] fun _ ↦ c :=
    condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      MeasurableSpace.smulInvariants_le herg _
  have hb : Tendsto (fun k ↦ ∫ ω, |((F k).card : ℝ)⁻¹ *
      ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c| ∂μ) l (𝓝 0) := by
    refine (tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp (E := ℝ) hne hFol
      (integrable_condInformation (μ := μ) X hX W₀)).congr fun k ↦ ?_
    refine integral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    rw [hω]
    simp [Real.norm_eq_abs, smul_eq_mul]
  have hbad : Tendsto (fun k ↦
      (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card * M) l (𝓝 0) := by
    simpa using (tendsto_card_filter_vadd_not_subset_div_card hFol W₀).mul_const M
  filter_upwards [hne, hb.eventually_lt_const hε', hbad.eventually_lt_const hε']
    with k hkne hkb hkbad
  have hcard : (0 : ℝ) < ((F k).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hkne
  have hig : ∀ (W : Finset G) (i : G),
      Integrable (fun ω ↦ condInformation μ X W (i +ᵥ ω)) μ := fun W i ↦
    (measurePreserving_vadd i μ).integrable_comp_of_integrable
      (integrable_condInformation (μ := μ) X hX W)
  have hA : Integrable (fun ω ↦ ((F k).card : ℝ)⁻¹ *
      ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)) μ :=
    (integrable_finsetSum (F k) fun i _ ↦ hig _ i).const_mul _
  have hB : Integrable (fun ω ↦ ((F k).card : ℝ)⁻¹ *
      ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)) μ :=
    (integrable_finsetSum (F k) fun i _ ↦ hig W₀ i).const_mul _
  have hchain : ∀ ω, -(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω))
      = ((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω) := fun ω ↦ by
    rw [show -(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω))
        = ((F k).card : ℝ)⁻¹ * -Real.log (blockProb μ X (F k) ω) from by ring,
      neg_log_blockProb_eq_sum_condInformation X hX (F k) ω]
  have hAB := integral_abs_inv_card_sum_condInformation_sub_le (μ := μ) X hX hW₀past hW₀unif
    hbnd (F k) hkne
  have hgoal : ∫ ω, |(-(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω)))
      - entropyRate G μ X| ∂μ
      ≤ (ε / 5 + (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card * M)
        + (∫ ω, |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c| ∂μ
          + ε / 5) := by
    have hptw : ∀ ω, |(-(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω)))
        - entropyRate G μ X|
        ≤ |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
            - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)|
          + (|((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c|
            + |c - entropyRate G μ X|) := fun ω ↦ by
      rw [hchain ω]
      calc |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
              condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω) - entropyRate G μ X|
          ≤ |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
              condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
              - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)|
            + |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)
              - entropyRate G μ X| := abs_sub_le _ _ _
        _ ≤ _ := by gcongr; exact abs_sub_le _ _ _
    have hint1 : Integrable (fun ω ↦ |((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
        - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)|) μ := (hA.sub hB).abs
    have hint2 : Integrable (fun ω ↦ |((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c|) μ :=
      (hB.sub (integrable_const (μ := μ) c)).abs
    have hint3 : Integrable (fun ω ↦ |((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c| + |c - entropyRate G μ X|) μ :=
      hint2.add (integrable_const (μ := μ) _)
    have hint4 : Integrable (fun ω ↦ |((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
        - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)|
        + (|((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c|
          + |c - entropyRate G μ X|)) μ := hint1.add hint3
    have hint5 : Integrable (fun ω ↦ ((F k).card : ℝ)⁻¹ *
        ∑ i ∈ F k, condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
        - entropyRate G μ X) μ := hA.sub (integrable_const (μ := μ) (entropyRate G μ X))
    calc ∫ ω, |(-(((F k).card : ℝ)⁻¹ * Real.log (blockProb μ X (F k) ω)))
            - entropyRate G μ X| ∂μ
        ≤ ∫ ω, (|((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
              condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
              - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)|
            + (|((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c|
              + |c - entropyRate G μ X|)) ∂μ := by
          refine integral_mono ?_ hint4 hptw
          refine Integrable.abs ?_
          simp only [hchain]
          exact hint5
      _ = (∫ ω, |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
              condInformation μ X (pastWindow G (F k) i) (i +ᵥ ω)
              - ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω)| ∂μ)
            + ((∫ ω, |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, condInformation μ X W₀ (i +ᵥ ω) - c| ∂μ)
              + |c - entropyRate G μ X|) := by
          rw [integral_add hint1 hint3, integral_add hint2 (integrable_const (μ := μ) _)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ _ := by linarith [hAB, hch]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ω ↦ abs_nonneg _)]
  linarith


omit [IsOrderedAddMonoid G] in
/-- **The mean information of a block is the sum of the mean conditional informations of its
sites.** Integrating the chain rule and using stationarity,
`H(X_Λ) = -∫ log p_Λ dμ = ∑_{i ∈ Λ} ∫ g_{W_i(Λ)} dμ`. -/
theorem neg_integral_log_blockProb_eq_sum [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ]
    [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ] (hX : Measurable X)
    (Λ : Finset G) :
    -∫ ω, Real.log (blockProb μ X Λ ω) ∂μ
      = ∑ i ∈ Λ, ∫ ω, condInformation μ X (pastWindow G Λ i) ω ∂μ := by
  have hig : ∀ (W : Finset G) (i : G),
      Integrable (fun ω ↦ condInformation μ X W (i +ᵥ ω)) μ := fun W i ↦
    (measurePreserving_vadd i μ).integrable_comp_of_integrable
      (integrable_condInformation (μ := μ) X hX W)
  calc -∫ ω, Real.log (blockProb μ X Λ ω) ∂μ
      = ∫ ω, ∑ i ∈ Λ, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω) ∂μ := by
        rw [← integral_neg]
        exact integral_congr_ae (.of_forall fun ω ↦
          neg_log_blockProb_eq_sum_condInformation X hX Λ ω)
    _ = ∑ i ∈ Λ, ∫ ω, condInformation μ X (pastWindow G Λ i) (i +ᵥ ω) ∂μ :=
        integral_finsetSum Λ fun i _ ↦ hig _ i
    _ = ∑ i ∈ Λ, ∫ ω, condInformation μ X (pastWindow G Λ i) ω ∂μ :=
        Finset.sum_congr rfl fun i _ ↦ (measurePreserving_vadd i μ).integral_comp
          (measurableEmbedding_const_vadd i) _

/-- **The normalised block entropies converge to the entropy rate**, along any Følner net and with
no ergodicity assumption: `|F k|⁻¹ H(X_{F k}) = -|F k|⁻¹ ∫ log p_{F k} dμ → h`. In particular the
entropy rate does not depend on the translation-invariant order used to define it, nor on the
Følner net.

The chain rule expresses `|Λ|⁻¹ H(X_Λ)` as the average of the mean conditional informations
`∫ g_{W_i(Λ)}`, each of which is at least `h`; and all but a vanishing fraction of the sites `i`
have `W₀ ⊆ W_i(Λ)` for a window `W₀` whose mean information is within `ε` of `h`, so that
`∫ g_{W_i(Λ)} ≤ ∫ g_{W₀}` for those, and `∫ g_{W_i(Λ)} ≤ ∫ g_∅` for the rest. -/
theorem tendsto_inv_card_mul_integral_neg_log_blockProb [MeasurableConstVAdd G Ω]
    [VAddInvariantMeasure G Ω μ] [Finite E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ]
    (hX : Measurable X)
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun k ↦ (((g +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0)) :
    Tendsto (fun k ↦ -(((F k).card : ℝ)⁻¹ * ∫ ω, Real.log (blockProb μ X (F k) ω) ∂μ)) l
      (𝓝 (entropyRate G μ X)) := by
  classical
  set M : ℝ := ∫ ω, condInformation μ X (∅ : Finset G) ω ∂μ with hM
  have hM0 : 0 ≤ M := integral_nonneg_of_ae (condInformation_nonneg_ae X _)
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨W₀, hW₀past, hW₀lt⟩ :=
    exists_integral_condInformation_lt (G := G) (μ := μ) X (half_pos hε)
  set c : ℝ := ∫ ω, condInformation μ X W₀ ω ∂μ with hc
  have hc0 : 0 ≤ c := integral_nonneg_of_ae (condInformation_nonneg_ae X _)
  have hbad : Tendsto (fun k ↦
      (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card * M) l (𝓝 0) := by
    simpa using (tendsto_card_filter_vadd_not_subset_div_card hFol W₀).mul_const M
  filter_upwards [hne, hbad.eventually_lt_const (half_pos hε)] with k hkne hkbad
  have hcard : (0 : ℝ) < ((F k).card : ℝ) := by exact_mod_cast Finset.card_pos.2 hkne
  have hsum := neg_integral_log_blockProb_eq_sum (μ := μ) X hX (F k)
  -- the average of the mean conditional informations is at least the entropy rate
  have hlow : ((F k).card : ℝ) * entropyRate G μ X
      ≤ ∑ i ∈ F k, ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ := by
    calc ((F k).card : ℝ) * entropyRate G μ X
        = ∑ _i ∈ F k, entropyRate G μ X := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ ↦
          entropyRate_le_integral_condInformation X fun j hj ↦ pastWindow_lt_zero hj
  -- and at most `c` up to the boundary sites
  have hhigh : ∑ i ∈ F k, ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ
      ≤ ((F k).card : ℝ) * c
        + (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) * M := by
    rw [← Finset.sum_filter_add_sum_filter_not (F k) (fun i ↦ i +ᵥ W₀ ⊆ F k)]
    gcongr ?_ + ?_
    · refine (Finset.sum_le_card_nsmul _ _ c fun i hi ↦ ?_).trans ?_
      · exact integral_condInformation_mono X hX
          (subset_pastWindow hW₀past (Finset.mem_filter.1 hi).2)
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast Finset.card_filter_le (F k) fun i ↦ i +ᵥ W₀ ⊆ F k) hc0
    · refine (Finset.sum_le_card_nsmul _ _ M fun i _ ↦ ?_).trans ?_
      · exact integral_condInformation_mono X hX (Finset.empty_subset _)
      · rw [nsmul_eq_mul]
  rw [Real.dist_eq, abs_lt]
  have hdiv : -(((F k).card : ℝ)⁻¹ * ∫ ω, Real.log (blockProb μ X (F k) ω) ∂μ)
      = ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
        ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ := by
    rw [← hsum]; ring
  rw [hdiv]
  constructor
  · have h2 : entropyRate G μ X
        ≤ ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
          ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ := by
      have h := mul_le_mul_of_nonneg_left hlow (inv_pos.2 hcard).le
      rwa [← mul_assoc, inv_mul_cancel₀ hcard.ne', one_mul] at h
    linarith
  · have h3 : ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k,
        ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ
        ≤ c + (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card * M := by
      rw [inv_mul_eq_div, div_le_iff₀ hcard]
      calc ∑ i ∈ F k, ∫ ω, condInformation μ X (pastWindow G (F k) i) ω ∂μ
          ≤ ((F k).card : ℝ) * c
            + (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) * M := hhigh
        _ = (c + (((F k).filter fun i ↦ ¬ i +ᵥ W₀ ⊆ F k).card : ℝ) / (F k).card * M)
            * ((F k).card : ℝ) := by field_simp
    linarith

end ShannonMcMillan





end MeasureTheory

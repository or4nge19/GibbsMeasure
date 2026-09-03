/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence
public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import GibbsMeasure.Mathlib.Order.Cofinal
public import GibbsMeasure.Prereqs.CylinderEvents

/-!
# Tail triviality is asymptotic independence

For an antitone sequence `ℱ` of sub-σ-algebras of a probability space, a zero-one law on the tail
σ-algebra `⨅ n, ℱ n` is equivalent to asymptotic independence of the `ℱ n`: for every measurable
`A` and every `ε > 0`, eventually every `B ∈ ℱ n` satisfies
`|μ (A ∩ B) - μ A * μ B| ≤ ε`
(`MeasureTheory.forall_measure_eq_zero_or_one_iInf_iff`).

The substantial direction is Lévy's downward theorem
(`MeasureTheory.tendsto_eLpNorm_condExp_of_antitone`): triviality on the tail makes
`μ[1_A | ⨅ n, ℱ n]` a.e. the constant `μ A`, and `μ (A ∩ B) - μ A · μ B` is the integral of
`μ[1_A | ℱ n] - μ A` over `B`, hence bounded by the `L¹` distance, which tends to `0`. The converse
is immediate on taking `B = A`.

## References

Hans-Otto Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Proposition (7.9).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : ℕ → MeasurableSpace Ω}

variable [IsProbabilityMeasure μ]

lemma iInf_le_of_forall_le (hle : ∀ n, ℱ n ≤ m0) : (⨅ n, ℱ n) ≤ m0 :=
  (iInf_le _ 0).trans (hle 0)

/-- If `μ` is trivial on the tail σ-algebra, the conditional expectation of an indicator given the
tail is a.e. the constant `μ A`. -/
lemma condExp_iInf_indicator_ae_eq_const (hle : ∀ n, ℱ n ≤ m0)
    (htriv : ∀ A, MeasurableSet[⨅ n, ℱ n] A → μ A = 0 ∨ μ A = 1)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ[A.indicator (1 : Ω → ℝ) | ⨅ n, ℱ n] =ᵐ[μ] fun _ ↦ (μ A).toReal := by
  have hm : (⨅ n, ℱ n) ≤ m0 := iInf_le_of_forall_le hle
  have hgi : Integrable (A.indicator (1 : Ω → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hA
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one hm htriv
    (stronglyMeasurable_condExp (m := ⨅ n, ℱ n) (μ := μ)
      (f := A.indicator (1 : Ω → ℝ))).measurable
  have hint : c = (μ A).toReal := by
    have h0 : ∫ x, (μ[A.indicator (1 : Ω → ℝ) | ⨅ n, ℱ n]) x ∂μ = (μ A).toReal := by
      rw [integral_condExp hm, integral_indicator_one hA, measureReal_def]
    rw [integral_congr_ae hc, integral_const] at h0
    simpa [measureReal_def, measure_univ] using h0
  exact hint ▸ hc

/-- **Georgii (7.9).** For an antitone sequence of sub-σ-algebras of a probability space, `μ` is
trivial on the tail σ-algebra `⨅ n, ℱ n` if and only if it is asymptotically independent of the
`ℱ n`: for every measurable `A` and every `ε > 0`, eventually every `B ∈ ℱ n` satisfies
`|μ(A ∩ B) - μ(A) μ(B)| ≤ ε`. -/
theorem forall_measure_eq_zero_or_one_iInf_iff (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0) :
    (∀ A, MeasurableSet[⨅ n, ℱ n] A → μ A = 0 ∨ μ A = 1) ↔
      ∀ A, MeasurableSet A → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ B, MeasurableSet[ℱ n] B →
          |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ ε := by
  constructor
  · intro htriv A hA ε hε
    set g := A.indicator (1 : Ω → ℝ) with hg
    have hgi : Integrable g μ := (integrable_const (1 : ℝ)).indicator hA
    have hconst := condExp_iInf_indicator_ae_eq_const hle htriv hA
    have hlim := tendsto_eLpNorm_condExp_of_antitone (μ := μ) g hℱ hle
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hlim) (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε)] with n hn B hB
    have hBm : MeasurableSet B := hle n B hB
    have hcn : Integrable (μ[g | ℱ n]) μ := integrable_condExp
    have hcT : Integrable (μ[g | ⨅ n, ℱ n]) μ := integrable_condExp
    -- the difference of the two sides is a set integral of `μ[g|ℱ n] - μ[g|⨅ ℱ]`
    have h1 : (μ (A ∩ B)).toReal = ∫ x in B, (μ[g | ℱ n]) x ∂μ := by
      rw [setIntegral_condExp (hle n) hgi hB, hg, setIntegral_indicator hA, Set.inter_comm B A]
      simp [measureReal_def]
    have h2 : (μ A).toReal * (μ B).toReal = ∫ x in B, (μ[g | ⨅ n, ℱ n]) x ∂μ := by
      rw [setIntegral_congr_ae hBm (hconst.mono fun x hx _ ↦ hx), setIntegral_const]
      simp [measureReal_def, mul_comm]
    rw [h1, h2, ← integral_sub hcn.integrableOn hcT.integrableOn, ← Real.norm_eq_abs]
    calc ‖∫ x in B, ((μ[g | ℱ n]) x - (μ[g | ⨅ n, ℱ n]) x) ∂μ‖
        ≤ ∫ x in B, ‖(μ[g | ℱ n]) x - (μ[g | ⨅ n, ℱ n]) x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖(μ[g | ℱ n]) x - (μ[g | ⨅ n, ℱ n]) x‖ ∂μ :=
          setIntegral_le_integral (hcn.sub hcT).norm (.of_forall fun _ ↦ norm_nonneg _)
      _ ≤ ε := by
          have hfi : Integrable (μ[g | ℱ n] - μ[g | ⨅ n, ℱ n]) μ := hcn.sub hcT
          have := ofReal_integral_norm_eq_lintegral_enorm hfi
          rw [← eLpNorm_one_eq_lintegral_enorm] at this
          have hle' : ENNReal.ofReal (∫ x, ‖(μ[g | ℱ n] - μ[g | ⨅ n, ℱ n]) x‖ ∂μ)
              ≤ ENNReal.ofReal ε := this ▸ hn
          simpa using (ENNReal.ofReal_le_ofReal_iff hε.le).1 hle'
  · intro hasym A hA
    have hAn : ∀ n, MeasurableSet[ℱ n] A := fun n ↦ (iInf_le ℱ n) A hA
    have hAm : MeasurableSet A := iInf_le_of_forall_le hle A hA
    have key : ∀ ε : ℝ, 0 < ε → |(μ A).toReal - (μ A).toReal * (μ A).toReal| ≤ ε := by
      intro ε hε
      obtain ⟨n, hn⟩ := ((hasym A hAm ε hε).and (eventually_ge_atTop 0)).exists
      simpa [Set.inter_self] using hn.1 A (hAn n)
    have hsq : (μ A).toReal = (μ A).toReal * (μ A).toReal := by
      by_contra hne
      obtain ⟨ε, hε, hlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < |(μ A).toReal - (μ A).toReal * (μ A).toReal| :=
        ⟨_, half_pos (abs_pos.2 (sub_ne_zero.2 hne)), half_lt_self (abs_pos.2 (sub_ne_zero.2 hne))⟩
      exact absurd (key ε hε) (not_le.2 hlt)
    have hfac : (μ A).toReal * ((μ A).toReal - 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.1 hfac with h | h
    · exact Or.inl (by
        rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top μ A)] at h)
    · refine Or.inr ?_
      have h1 : (μ A).toReal = 1 := by linarith [sub_eq_zero.1 h]
      rwa [ENNReal.toReal_eq_one_iff] at h1

/-- **Georgii (7.9)** over a countable directed index set, which is how the statement is used: the
index set is the finite volumes `Λ ∈ 𝒮`, not `ℕ`. Reduced to the sequential case along a monotone
cofinal sequence. -/
theorem forall_measure_eq_zero_or_one_iInf_iff_of_directed {ι : Type*} [Preorder ι] [Countable ι]
    [Nonempty ι] [IsDirected ι (· ≤ ·)] {𝒜 : ι → MeasurableSpace Ω} (h𝒜 : Antitone 𝒜)
    (hle : ∀ i, 𝒜 i ≤ m0) :
    (∀ A, MeasurableSet[⨅ i, 𝒜 i] A → μ A = 0 ∨ μ A = 1) ↔
      ∀ A, MeasurableSet A → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
        ∀ B, MeasurableSet[𝒜 i] B →
          |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ ε := by
  obtain ⟨f, hfmono, hfcof⟩ := exists_monotone_cofinal ι
  have hℱ : Antitone fun n ↦ 𝒜 (f n) := fun a b hab ↦ h𝒜 (hfmono hab)
  have hiInf : (⨅ i, 𝒜 i) = ⨅ n, 𝒜 (f n) := iInf_eq_iInf_comp_of_cofinal h𝒜 hfcof
  have hseq := forall_measure_eq_zero_or_one_iInf_iff (μ := μ) hℱ fun n ↦ hle (f n)
  constructor
  · intro htriv A hA ε hε
    rw [hiInf] at htriv
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq.1 htriv A hA ε hε)
    filter_upwards [eventually_ge_atTop (f N)] with i hi B hB
    exact hN N le_rfl B (h𝒜 hi B hB)
  · intro hasym
    rw [hiInf]
    refine hseq.2 fun A hA ε hε ↦ ?_
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hasym A hA ε hε)
    obtain ⟨N, hN⟩ := hfcof i₀
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hi₀ (f n) (hN.trans (hfmono hn))

section Freezing

/-- **The "freezing" argument behind Georgii's Theorem (12.6).** If `μ` is trivial on
`⨅ n, cylinderEvents (T n)` for a family `T : ℕ → Set S` of coordinate sets avoiding a fixed site
`i` (`i ∉ T n` for every `n`), then every function measurable for `⨅ n, cylinderEvents ({i} ∪ T
n)` is `μ`-a.e. a function of the single coordinate `σ i`. Unlike the analogous two-coordinate
statement `exists_ae_eq_pair_of_forall_measure_eq_zero_or_one` in
`GibbsMeasure/Specification/MarkovIntChains.lean` (needed there because Georgii's hypothesis
(10.19) genuinely involves both endpoints `σ_{j-1}, σ_j` of a step of `ℤ`), no resampling and no
Fubini argument is needed here: fixing the single coordinate directly produces, for every `x`, an
a.e.-constant function (tail triviality), and the countably many resulting null sets (one per `x
∈ E`, `E` countable) are combined by `Filter.ae_all_iff`. Intended home:
`Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated`, next to
`measurable_cylinderEvents_iff_dependsOn`. -/
theorem exists_ae_eq_single_of_forall_measure_eq_zero_or_one
    {S E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]
    {μ : Measure (S → E)} [IsProbabilityMeasure μ] {i : S} {T : ℕ → Set S} (hi : ∀ n, i ∉ T n)
    (htriv : ∀ A, MeasurableSet[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)] A →
      μ A = 0 ∨ μ A = 1)
    {f : (S → E) → ℝ}
    (hf : Measurable[⨅ n, cylinderEvents (X := fun _ : S ↦ E) ({i} ∪ T n)] f) :
    ∃ q : E → ℝ, Measurable q ∧ f =ᵐ[μ] fun σ ↦ q (σ i) := by
  classical
  have hf' : Measurable f := hf.mono ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) le_rfl
  set q : E → ℝ := fun x ↦ ∫ ω, f (Function.update ω i x) ∂μ with hq_def
  refine ⟨q, measurable_of_countable q, ?_⟩
  have hconst : ∀ x : E, ∀ᵐ ω ∂μ, f (Function.update ω i x) = q x := by
    intro x
    have hshift : Measurable fun ω : S → E ↦ f (Function.update ω i x) :=
      hf'.comp measurable_update_left
    have hmeasT : Measurable[⨅ n, cylinderEvents (X := fun _ : S ↦ E) (T n)]
        fun ω ↦ f (Function.update ω i x) := by
      rw [measurable_iInf_iff_forall]
      intro n
      have hdep : DependsOn f ({i} ∪ T n) :=
        (hf.mono (iInf_le _ n) le_rfl).dependsOn_of_cylinderEvents
      refine hshift.cylinderEvents_of_dependsOn fun ω ω' hωω' ↦ hdep fun k hk ↦ ?_
      rcases hk with hk | hk
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        simp
      · have hki : k ≠ i := fun h ↦ (h ▸ hi n) hk
        simp only [Function.update_of_ne hki]
        exact hωω' k hk
    obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one
      ((iInf_le _ (0 : ℕ)).trans cylinderEvents_le_pi) htriv hmeasT
    have hqc : q x = c := by
      simp only [hq_def]
      rw [integral_congr_ae hc, integral_const]
      simp
    rw [hqc]
    exact hc
  filter_upwards [ae_all_iff.2 hconst] with ω hω
  have h := hω (ω i)
  rwa [Function.update_eq_self] at h

end Freezing

end MeasureTheory

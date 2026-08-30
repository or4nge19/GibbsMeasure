/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Martingale.Convergence

/-!
# Lévy's downward theorem (almost everywhere version)

Given a finite measure `μ`, an antitone sequence of sub-σ-algebras `ℱ n ≤ m0` and an
integrable function `g`, the reversed martingale `n ↦ μ[g | ℱ n]` converges almost everywhere
to `μ[g | ⨅ n, ℱ n]`.

The proof mirrors the architecture of Lévy's upward theorem in
`Mathlib/Probability/Martingale/Convergence.lean`: for each `N`, the finite window
`k ↦ μ[g | ℱ (N - k)]` is a forward martingale with respect to the (monotone) filtration
`k ↦ ℱ (N - k)`, so Doob's upcrossing estimate applies to it with a bound uniform in `N`
(the terminal value is always `μ[g | ℱ 0]`). Upcrossings of the reversed window are
downcrossings of the original sequence, and a sequence which frequently visits both below `a`
and above `b` has arbitrarily many of those; Fatou's lemma then shows that this happens only on
a null set, which yields a.e. convergence. The limit is `⨅ n, ℱ n`-measurable since it is
(everywhere) the limit of the tail sequence, which is `ℱ n`-measurable for every `n`, and it is
identified with `μ[g | ⨅ n, ℱ n]` through the uniform integrability of conditional expectations
(Vitali) and the characterisation of the conditional expectation by set integrals.

## Main results

* `MeasureTheory.tendsto_ae_condExp_of_antitone`: **Lévy's downward theorem**, a.e. version:
  for an antitone sequence `ℱ` of sub-σ-algebras, `μ[g | ℱ n]` converges almost everywhere to
  `μ[g | ⨅ n, ℱ n]`.
* `MeasureTheory.tendsto_eLpNorm_condExp_of_antitone`: **Lévy's downward theorem**, L¹ version.
* `MeasureTheory.ae_exists_tendsto_condExp_of_antitone`: the reversed martingale `μ[g | ℱ n]`
  converges almost everywhere (to some limit).
* `MeasureTheory.stronglyMeasurable_iInf_limUnder_of_antitone`: the pointwise `limUnder` of a
  process adapted to an antitone family `ℱ` is `⨅ n, ℱ n`-strongly measurable.
* `MeasureTheory.le_upcrossingsBefore_reversed_of_frequently`: a sequence which frequently
  visits both below `a` and above `b` has arbitrarily many downcrossings, i.e. the reversed
  windows `j ↦ f (N - j)` have arbitrarily many upcrossings for `N` large.
-/

@[expose] public section

open TopologicalSpace Filter MeasureTheory

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section ReversedWindow

variable {ℱ : ℕ → MeasurableSpace Ω}

/-- Given an antitone family `ℱ` of sub-σ-algebras of `m0` and a time horizon `N`, the
"reversed window" `k ↦ ℱ (N - k)` is a (monotone) filtration. -/
def reversedFiltration (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0) (N : ℕ) : Filtration ℕ m0 where
  seq k := ℱ (N - k)
  mono' _ _ hkl := hℱ (Nat.sub_le_sub_left hkl N)
  le' _ := hle _

@[simp]
theorem reversedFiltration_apply (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0) (N k : ℕ) :
    reversedFiltration hℱ hle N k = ℱ (N - k) :=
  rfl

/-- The reversed window `k ↦ μ[g | ℱ (N - k)]` of the reversed martingale `n ↦ μ[g | ℱ n]` is a
(forward) martingale with respect to the reversed window filtration. -/
theorem martingale_condExp_reversed [IsFiniteMeasure μ] (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (g : Ω → ℝ) (N : ℕ) :
    Martingale (fun k => μ[g | ℱ (N - k)]) (reversedFiltration hℱ hle N) μ :=
  ⟨fun _ => stronglyMeasurable_condExp, fun _ _ hkl =>
    condExp_condExp_of_le (hℱ (Nat.sub_le_sub_left hkl N)) (hle _)⟩

/-- Doob's upcrossing estimate for the reversed window, with a bound which is uniform in the
horizon `N`: the terminal value of the window is always `μ[g | ℱ 0]`. -/
theorem mul_integral_upcrossingsBefore_reversed_le [IsFiniteMeasure μ] (hℱ : Antitone ℱ)
    (hle : ∀ n, ℱ n ≤ m0) (g : Ω → ℝ) (a b : ℝ) (N : ℕ) :
    (b - a) * μ[upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N] ≤
      μ[fun ω => ((μ[g | ℱ 0]) ω - a)⁺] := by
  have := (martingale_condExp_reversed (μ := μ) hℱ hle g N).submartingale
    |>.mul_integral_upcrossingsBefore_le_integral_pos_part a b N
  simpa only [Nat.sub_self] using this

/-- The `lintegral` form of the uniform upcrossing bound. -/
theorem lintegral_upcrossingsBefore_reversed_le [IsFiniteMeasure μ] (hℱ : Antitone ℱ)
    (hle : ∀ n, ℱ n ≤ m0) (g : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) :
    ∫⁻ ω, (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞) ∂μ ≤
      ENNReal.ofReal ((μ[fun ω => ((μ[g | ℱ 0]) ω - a)⁺]) / (b - a)) := by
  have hint : Integrable (fun ω => (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ)) μ :=
    (martingale_condExp_reversed hℱ hle g N).stronglyAdapted.integrable_upcrossingsBefore hab
  rw [(by simp : ∫⁻ ω, (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞) ∂μ =
    ∫⁻ ω, ((upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0) : ℝ≥0∞) ∂μ),
    lintegral_coe_eq_integral _ (by simpa using hint)]
  simp only [NNReal.coe_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (sub_pos.2 hab), mul_comm]
  exact mul_integral_upcrossingsBefore_reversed_le hℱ hle g a b N

end ReversedWindow

section Deterministic

variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω}

/-- If a real sequence frequently visits both below `a` and above `b`, then for every `k` and
every `m`, for all sufficiently large horizons `N`, the reversed window `j ↦ f (N - j)` has at
least `k` upcrossings of `[a, b]` before time `N - m`. -/
theorem le_upcrossingsBefore_reversed_of_frequently (hab : a < b)
    (h₁ : ∃ᶠ n in atTop, f n ω < a) (h₂ : ∃ᶠ n in atTop, b < f n ω) (k : ℕ) :
    ∀ m, ∃ T, ∀ N, T ≤ N → k ≤ upcrossingsBefore a b (fun j => f (N - j)) (N - m) ω := by
  induction k with
  | zero => exact fun m => ⟨m, fun _ _ => Nat.zero_le _⟩
  | succ k ih =>
    intro m
    obtain ⟨s, hms, hs⟩ := frequently_atTop.1 h₂ (m + 1)
    obtain ⟨t, hst, ht⟩ := frequently_atTop.1 h₁ s
    obtain ⟨T, hT⟩ := ih t
    refine ⟨max T t, fun N hN => ?_⟩
    have htN : t ≤ N := le_trans (le_max_right _ _) hN
    have hsN : s ≤ N := hst.trans htN
    have hlt : upcrossingsBefore a b (fun j => f (N - j)) (N - t) ω <
        upcrossingsBefore a b (fun j => f (N - j)) (N - s + 1) ω := by
      refine upcrossingsBefore_lt_of_exists_upcrossing hab le_rfl ?_
        (Nat.sub_le_sub_left hst N) ?_
      · simpa only [Nat.sub_sub_self htN] using ht
      · simpa only [Nat.sub_sub_self hsN] using hs
    have hmono : upcrossingsBefore a b (fun j => f (N - j)) (N - s + 1) ω ≤
        upcrossingsBefore a b (fun j => f (N - j)) (N - m) ω :=
      upcrossingsBefore_mono hab (by omega) ω
    exact (Nat.succ_le_of_lt (lt_of_le_of_lt (hT N (le_trans (le_max_left _ _) hN)) hlt)).trans
      hmono

/-- Specialisation of `le_upcrossingsBefore_reversed_of_frequently` to the full window. -/
theorem le_upcrossingsBefore_reversed_of_frequently' (hab : a < b)
    (h₁ : ∃ᶠ n in atTop, f n ω < a) (h₂ : ∃ᶠ n in atTop, b < f n ω) (k : ℕ) :
    ∃ T, ∀ N, T ≤ N → k ≤ upcrossingsBefore a b (fun j => f (N - j)) N ω := by
  obtain ⟨T, hT⟩ := le_upcrossingsBefore_reversed_of_frequently hab h₁ h₂ k 0
  exact ⟨T, fun N hN => by simpa only [Nat.sub_zero] using hT N hN⟩

/-- A realization of a stochastic process with bounded limit inferior which, for all rationals
`a < b`, does not frequently visit both below `a` and above `b`, is convergent. This is the
criterion underlying `MeasureTheory.tendsto_of_uncrossing_lt_top`. -/
theorem tendsto_of_not_frequently_lt_and_frequently_lt
    (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → ¬((∃ᶠ n in atTop, f n ω < a) ∧ ∃ᶠ n in atTop, b < f n ω)) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact hf₂ a b (Rat.cast_lt.1 hab)
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact False.elim (hf₂ a b hab ⟨h₁, h₂⟩)

/-- Shifting a sequence does not change its `limUnder atTop`. -/
theorem limUnder_atTop_comp_add {α : Type*} [TopologicalSpace α] [Nonempty α] (u : ℕ → α)
    (k : ℕ) : limUnder atTop (fun n => u (n + k)) = limUnder atTop u := by
  unfold limUnder
  conv_rhs => rw [← map_add_atTop_eq_nat k, Filter.map_map]
  rfl

end Deterministic

section Limit

variable {ℱ : ℕ → MeasurableSpace Ω} {f : ℕ → Ω → ℝ}

/-- If `f n` is `ℱ n`-strongly measurable for an antitone family `ℱ`, then the (everywhere
defined) limit `ω ↦ limUnder atTop (fun n => f n ω)` is `⨅ n, ℱ n`-strongly measurable: for
each `n`, it is the limit of the tail sequence `m ↦ f (m + n)`, which is `ℱ n`-measurable. -/
theorem stronglyMeasurable_iInf_limUnder_of_antitone (hℱ : Antitone ℱ)
    (hf : ∀ n, StronglyMeasurable[ℱ n] (f n)) :
    StronglyMeasurable[⨅ n, ℱ n] fun ω => limUnder atTop fun n => f n ω := by
  have h : ∀ n, StronglyMeasurable[ℱ n] fun ω => limUnder atTop fun n => f n ω := by
    intro n
    have : (fun ω => limUnder atTop fun m => f m ω) =
        fun ω => limUnder atTop fun m => f (m + n) ω := by
      ext ω
      exact (limUnder_atTop_comp_add (fun m => f m ω) n).symm
    rw [this]
    exact @StronglyMeasurable.limUnder ℕ Ω ℝ (ℱ n) _ _ atTop _ (fun m => f (m + n)) _ _
      fun m => (hf (m + n)).mono (hℱ (Nat.le_add_left n m))
  refine Measurable.stronglyMeasurable ?_
  exact fun t ht => MeasurableSpace.measurableSet_iInf.2 fun n => (h n).measurable ht

end Limit

section AeConvergence

variable [IsFiniteMeasure μ] {ℱ : ℕ → MeasurableSpace Ω} {g : Ω → ℝ}

/-- The number of upcrossings of the reversed window is measurable. -/
theorem measurable_upcrossingsBefore_reversed (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (g : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) :
    Measurable fun ω => (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞) :=
  measurable_from_top.comp
    ((martingale_condExp_reversed (μ := μ) hℱ hle g N).stronglyAdapted.measurable_upcrossingsBefore
      hab)

/-- Almost everywhere, the reversed martingale `n ↦ μ[g | ℱ n]` does not frequently visit both
below `a` and above `b`: otherwise the reversed windows would have arbitrarily many upcrossings,
contradicting the uniform upcrossing estimate through Fatou's lemma. -/
theorem ae_not_frequently_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (g : Ω → ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂μ, ¬((∃ᶠ n in atTop, (μ[g | ℱ n]) ω < a) ∧ ∃ᶠ n in atTop, b < (μ[g | ℱ n]) ω) := by
  have hUm : ∀ N, Measurable fun ω =>
      (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞) :=
    fun N => measurable_upcrossingsBefore_reversed hℱ hle g hab N
  have hliminf : ∀ᵐ ω ∂μ, liminf (fun N =>
      (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞)) atTop < ∞ := by
    have hC : ∫⁻ ω, liminf (fun N =>
        (upcrossingsBefore a b (fun k => μ[g | ℱ (N - k)]) N ω : ℝ≥0∞)) atTop ∂μ ≤
        ENNReal.ofReal ((μ[fun ω => ((μ[g | ℱ 0]) ω - a)⁺]) / (b - a)) :=
      (lintegral_liminf_le hUm).trans (liminf_le_of_frequently_le (Frequently.of_forall fun N =>
        lintegral_upcrossingsBefore_reversed_le hℱ hle g hab N))
    exact ae_lt_top (Measurable.liminf hUm) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC)
  filter_upwards [hliminf] with ω hω
  rintro ⟨h₁, h₂⟩
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hω.ne
  obtain ⟨T, hT⟩ := le_upcrossingsBefore_reversed_of_frequently' hab h₁ h₂ k
  obtain ⟨N, hN, hNk⟩ := frequently_atTop.1 (frequently_lt_of_liminf_lt (h := hk)) T
  exact absurd (hT N hN) (not_le.2 (by exact_mod_cast hNk))

/-- Almost everywhere, the reversed martingale `n ↦ μ[g | ℱ n]` converges. -/
theorem ae_exists_tendsto_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop (𝓝 c) := by
  have hbdd : ∀ n, eLpNorm (μ[g | ℱ n]) 1 μ ≤ (eLpNorm g 1 μ).toNNReal := fun n => by
    rw [ENNReal.coe_toNNReal (memLp_one_iff_integrable.2 hg).2.ne]
    exact eLpNorm_condExp_le_eLpNorm g le_rfl
  have hfreq : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      ¬((∃ᶠ n in atTop, (μ[g | ℱ n]) ω < a) ∧ ∃ᶠ n in atTop, b < (μ[g | ℱ n]) ω) := by
    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab
    exact ae_not_frequently_condExp_of_antitone hℱ hle g (Rat.cast_lt.2 hab)
  filter_upwards [hfreq, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero
    (fun n => (stronglyMeasurable_condExp.mono (hle n)).measurable) hbdd] with ω h₁ h₂
  exact tendsto_of_not_frequently_lt_and_frequently_lt h₂ h₁

/-- Almost everywhere, the reversed martingale `n ↦ μ[g | ℱ n]` converges to the (everywhere
defined, `⨅ n, ℱ n`-measurable) function `ω ↦ limUnder atTop (fun n => μ[g | ℱ n] ω)`. -/
theorem ae_tendsto_limUnder_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop
      (𝓝 (limUnder atTop fun n => (μ[g | ℱ n]) ω)) := by
  filter_upwards [ae_exists_tendsto_condExp_of_antitone hℱ hle hg] with ω hω
  exact tendsto_nhds_limUnder hω

end AeConvergence

section Identification

variable [IsFiniteMeasure μ] {ℱ : ℕ → MeasurableSpace Ω} {g : Ω → ℝ}

/-- The a.e. limit of the reversed martingale `n ↦ μ[g | ℱ n]` is integrable. -/
theorem integrable_limUnder_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hg : Integrable g μ) :
    Integrable (fun ω => limUnder atTop fun n => (μ[g | ℱ n]) ω) μ := by
  have hmeas : AEStronglyMeasurable (fun ω => limUnder atTop fun n => (μ[g | ℱ n]) ω) μ :=
    ((stronglyMeasurable_iInf_limUnder_of_antitone hℱ fun _ => stronglyMeasurable_condExp).mono
      ((iInf_le _ 0).trans (hle 0))).aestronglyMeasurable
  refine memLp_one_iff_integrable.1 ⟨hmeas, ?_⟩
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm
    (fun n => (stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable) _
    (ae_tendsto_limUnder_condExp_of_antitone hℱ hle hg)).trans_lt ?_
  refine (liminf_le_of_frequently_le (Frequently.of_forall fun n =>
    eLpNorm_condExp_le_eLpNorm g le_rfl)).trans_lt ?_
  exact (memLp_one_iff_integrable.2 hg).2

/-- The reversed martingale `n ↦ μ[g | ℱ n]` converges in L¹ to its a.e. limit, by uniform
integrability of conditional expectations and Vitali's convergence theorem. -/
theorem tendsto_eLpNorm_limUnder_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hg : Integrable g μ) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - fun ω => limUnder atTop fun n => (μ[g | ℱ n]) ω) 1 μ)
      atTop (𝓝 0) :=
  have hmeas : ∀ n, AEStronglyMeasurable (μ[g | ℱ n]) μ := fun n =>
    (stronglyMeasurable_condExp.mono (hle n)).aestronglyMeasurable
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_one_iff_integrable.2 (integrable_limUnder_condExp_of_antitone hℱ hle hg))
    (hg.uniformIntegrable_condExp hle).2.1
    (tendstoInMeasure_of_tendsto_ae hmeas (ae_tendsto_limUnder_condExp_of_antitone hℱ hle hg))

/-- The a.e. limit of the reversed martingale `n ↦ μ[g | ℱ n]` is `μ[g | ⨅ n, ℱ n]`: it is
`⨅ n, ℱ n`-measurable, integrable, and its integrals over `⨅ n, ℱ n`-measurable sets agree with
those of `g` (by passing to the limit in `setIntegral_condExp`, using L¹ convergence). -/
theorem limUnder_condExp_ae_eq_condExp_iInf (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hg : Integrable g μ) :
    (fun ω => limUnder atTop fun n => (μ[g | ℱ n]) ω) =ᵐ[μ] μ[g | ⨅ n, ℱ n] := by
  have hm : ⨅ n, ℱ n ≤ m0 := (iInf_le _ 0).trans (hle 0)
  have hLint : Integrable (fun ω => limUnder atTop fun n => (μ[g | ℱ n]) ω) μ :=
    integrable_limUnder_condExp_of_antitone hℱ hle hg
  have hL1 := tendsto_eLpNorm_limUnder_condExp_of_antitone hℱ hle hg
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hg (fun s _ _ => hLint.integrableOn)
    (fun s hs _ => ?_)
    (stronglyMeasurable_iInf_limUnder_of_antitone hℱ fun _ =>
      stronglyMeasurable_condExp).aestronglyMeasurable
  have hs' : ∀ n, MeasurableSet[ℱ n] s := MeasurableSpace.measurableSet_iInf.1 hs
  have h1 : Tendsto (fun n => ∫ x in s, (μ[g | ℱ n]) x ∂μ) atTop
      (𝓝 (∫ x in s, limUnder atTop (fun n => (μ[g | ℱ n]) x) ∂μ)) := by
    refine tendsto_integral_of_L1 _ hLint.aestronglyMeasurable.restrict
      (Eventually.of_forall fun n => integrable_condExp.integrableOn) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => zero_le)
      fun n => ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have h2 : Tendsto (fun n => ∫ x in s, (μ[g | ℱ n]) x ∂μ) atTop (𝓝 (∫ x in s, g x ∂μ)) :=
    tendsto_const_nhds.congr fun n => (setIntegral_condExp (hle n) hg (hs' n)).symm
  exact tendsto_nhds_unique h1 h2

/-- **Lévy's downward theorem**, almost everywhere version, for an integrable function: given an
antitone sequence of sub-σ-algebras `ℱ n ≤ m0`, the reversed martingale `μ[g | ℱ n]` converges
almost everywhere to `μ[g | ⨅ n, ℱ n]`. -/
theorem Integrable.tendsto_ae_condExp_of_antitone (hg : Integrable g μ) (hℱ : Antitone ℱ)
    (hle : ∀ n, ℱ n ≤ m0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop (𝓝 ((μ[g | ⨅ n, ℱ n]) ω)) := by
  filter_upwards [ae_tendsto_limUnder_condExp_of_antitone hℱ hle hg,
    limUnder_condExp_ae_eq_condExp_iInf hℱ hle hg] with ω hω heq
  rw [← heq]
  exact hω

/-- **Lévy's downward theorem**, almost everywhere version: given a function `g` and an antitone
sequence of sub-σ-algebras `ℱ n ≤ m0`, the sequence `μ[g | ℱ n]` converges almost everywhere to
`μ[g | ⨅ n, ℱ n]`. This is the counterpart of `MeasureTheory.tendsto_ae_condExp` (Lévy's upward
theorem) for a decreasing sequence of σ-algebras. -/
theorem tendsto_ae_condExp_of_antitone (g : Ω → ℝ) (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop (𝓝 ((μ[g | ⨅ n, ℱ n]) ω)) := by
  by_cases hg : Integrable g μ
  · exact hg.tendsto_ae_condExp_of_antitone hℱ hle
  · simp only [condExp_of_not_integrable hg, Pi.zero_apply]
    exact Eventually.of_forall fun _ => tendsto_const_nhds

/-- **Lévy's downward theorem**, L¹ version: given a function `g` and an antitone sequence of
sub-σ-algebras `ℱ n ≤ m0`, the sequence `μ[g | ℱ n]` converges in L¹ to `μ[g | ⨅ n, ℱ n]`. -/
theorem tendsto_eLpNorm_condExp_of_antitone (g : Ω → ℝ) (hℱ : Antitone ℱ)
    (hle : ∀ n, ℱ n ≤ m0) :
    Tendsto (fun n => eLpNorm (μ[g | ℱ n] - μ[g | ⨅ n, ℱ n]) 1 μ) atTop (𝓝 0) := by
  by_cases hg : Integrable g μ
  · refine (tendsto_eLpNorm_limUnder_condExp_of_antitone hℱ hle hg).congr fun n =>
      eLpNorm_congr_ae ?_
    filter_upwards [limUnder_condExp_ae_eq_condExp_iInf hℱ hle hg] with ω hω
    simp only [Pi.sub_apply, hω]
  · simp only [condExp_of_not_integrable hg, sub_zero, eLpNorm_zero]
    exact tendsto_const_nhds

end Identification

end MeasureTheory

end

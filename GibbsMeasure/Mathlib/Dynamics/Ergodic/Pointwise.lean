/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MaximalInequality

/-!
# The pointwise ergodic theorem along regular Følner sequences

Let an abelian group `G` act on a finite measure space `(Ω, μ)` by measure-preserving maps
`ω ↦ g +ᵥ ω`, let `𝓘 = MeasurableSpace.smulInvariants (Multiplicative G) Ω` be the σ-algebra of
invariant events, and let `F : ℕ → Finset G` be an increasing sequence of non-empty finite sets
which is *Følner* (`|(g +ᵥ F n) ∆ F n| / |F n| → 0` for every `g`) and *Tempelman-regular*
(`|F n - F n + F n| ≤ C |F n|` for a finite constant `C`). For integrable `f : Ω → ℝ` the averages
`R_n f = |F n|⁻¹ ∑_{i ∈ F n} f ∘ (i +ᵥ ·)` converge almost surely to `μ[f | 𝓘]`:

* `MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp`, the **individual ergodic theorem**;
* `MeasureTheory.ae_forall_tendsto_inv_card_smul_sum_vadd_condExp`, simultaneously for a
  countable family of integrable functions;
* `MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp_cube`, Georgii's Theorem (14.A8): for
  `ℤ^d` acting on a finite measure space (Georgii: a probability space) along an increasing
  sequence of cubes `Λ_n = x_n + [0, r_n)^d` with `|Λ_n| → ∞`, where `C = 3 ^ d`
  (`MeasureTheory.tendsto_card_vadd_cube_symmDiff_div_card` is the Følner property of the cubes).

## The proof

This is Georgii's proof of (14.A8), which combines the mean ergodic theorem (14.A5)
(`MeasureTheory.tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one`) with the maximal
inequality (14.A6) (`MeasureTheory.mul_measure_lt_ergodicMaximalFunction_le_of_monotone`). Fix
`ε > 0`, a bounded (simple) `g` with `‖f - g‖₁ ≤ η` and, by the mean ergodic theorem, an `N` with
`‖R_N g - μ[g | 𝓘]‖₁ ≤ η`, where `η = ε² / (C + 1)`. Pointwise,
`R_n f - μ[f | 𝓘] = R_n (f - g) + (R_n g - R_n (R_N g)) + R_n (R_N g - μ[g | 𝓘])
  + (μ[g | 𝓘] - μ[f | 𝓘])`
because `R_n μ[g | 𝓘] = μ[g | 𝓘]` (`μ[g | 𝓘]` is strictly invariant). The second term is a finite
average of coboundaries `R_n (g ∘ (j +ᵥ ·) - g)`, bounded by `‖g‖_∞ |(j +ᵥ F n) ∆ F n| / |F n|`,
so it tends to `0` everywhere (`MeasureTheory.tendsto_inv_card_smul_sum_vadd_sub_vadd`). The
maximal inequality bounds the first and third terms by `ε` outside sets of measure `≤ ε`, and
Markov's inequality with `‖μ[· | 𝓘]‖₁ ≤ ‖·‖₁` does the same for the last term
(`MeasureTheory.measure_frequently_le_abs_inv_card_smul_sum_vadd_sub_condExp_le`). Hence
`μ(∃ᶠ n, |R_n f - μ[f | 𝓘]| ≥ 4ε) ≤ 3ε`, and `ε → 0` along a countable set finishes the proof.

## Hypotheses actually used

* `AddCommGroup G`: through the maximal inequality (Tempelman regularity `F n - F n + F n` and
  the Følner windows of `G`).
* `Countable G`: through the mean ergodic theorem (Remark (14.3)(2)); a Følner sequence forces it
  anyway (`countable_of_tendsto_card_smul_symmDiff_div_card`).
* `IsFiniteMeasure μ`: bounded functions must be integrable (the dense class), and the mean
  ergodic theorem needs it. Georgii assumes a probability measure; nothing uses `μ Ω = 1`.
* `C ≠ ∞`: without a genuine regularity constant the maximal inequality is empty, and the
  pointwise theorem fails for general Følner sequences.
* `Monotone F`, `(F 0).Nonempty`: the form of Tempelman regularity provided by
  `mul_measure_lt_ergodicMaximalFunction_le_of_monotone`; `0 ∈ F n` is not needed.
-/

@[expose] public section

open Filter Finset Set
open scoped ENNReal Pointwise symmDiff Topology

namespace MeasureTheory

/-! ### Pointwise algebra of the averages `R_F f ω = |F|⁻¹ ∑_{i ∈ F} f (i +ᵥ ω)` -/

section Averages

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω]

/-- The sums of a bounded function over a finite set and over a translate of it differ by at most
`|(j +ᵥ s) ∆ s| ⋅ M`. -/
lemma abs_sum_vadd_sub_sum_le [DecidableEq G] {h : G → ℝ} {M : ℝ} (hM : ∀ i, |h i| ≤ M) (j : G)
    (s : Finset G) : |∑ i ∈ j +ᵥ s, h i - ∑ i ∈ s, h i| ≤ ((j +ᵥ s) ∆ s).card * M := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have hb : ∀ t : Finset G, |∑ i ∈ t, h i| ≤ t.card * M := fun t ↦
    (Finset.abs_sum_le_sum_abs _ _).trans <| by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun i _ ↦ hM i
  have hsd : (((j +ᵥ s) ∆ s).card : ℝ) = ((j +ᵥ s) \ s).card + (s \ (j +ᵥ s)).card := by
    rw [Finset.symmDiff_def, Finset.card_union_eq_card_add_card.2 disjoint_sdiff_sdiff]
    push_cast; rfl
  calc |∑ i ∈ (j +ᵥ s) \ s, h i - ∑ i ∈ s \ (j +ᵥ s), h i|
      ≤ |∑ i ∈ (j +ᵥ s) \ s, h i| + |∑ i ∈ s \ (j +ᵥ s), h i| := abs_sub _ _
    _ ≤ ((j +ᵥ s) \ s).card * M + (s \ (j +ᵥ s)).card * M := add_le_add (hb _) (hb _)
    _ = ((j +ᵥ s) ∆ s).card * M := by rw [hsd]; ring

/-- **Averages of a coboundary vanish along a Følner sequence.** For bounded `g` and any `j`,
`|F n|⁻¹ ∑_{i ∈ F n} (g (j +ᵥ (i +ᵥ ω)) - g (i +ᵥ ω)) → 0` at every `ω`: the two sums are over
`j +ᵥ F n` and `F n`, and differ on the symmetric difference only. This is the observation
`limsup_n |R_n (R_N g - g)| = 0` in Georgii's proof of (14.A8). -/
lemma tendsto_inv_card_smul_sum_vadd_sub_vadd [DecidableEq G] {F : ℕ → Finset G}
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    {g : Ω → ℝ} {M : ℝ} (hM : ∀ ω, |g ω| ≤ M) (j : G) (ω : Ω) :
    Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, (g (j +ᵥ (i +ᵥ ω)) - g (i +ᵥ ω))) atTop
      (𝓝 0) := by
  refine squeeze_zero_norm (fun n ↦ ?_) (by simpa using (hFol j).mul_const M)
  have h : ∑ i ∈ F n, (g (j +ᵥ (i +ᵥ ω)) - g (i +ᵥ ω)) =
      ∑ i ∈ j +ᵥ F n, g (i +ᵥ ω) - ∑ i ∈ F n, g (i +ᵥ ω) := by
    rw [Finset.sum_sub_distrib, Finset.sum_vadd_finset]
    simp only [vadd_vadd]
  rw [h, Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast, div_mul_eq_mul_div,
    div_eq_inv_mul]
  gcongr
  exact abs_sum_vadd_sub_sum_le (fun i ↦ hM (i +ᵥ ω)) j (F n)

/-- `R_s (R_t g) - R_s g` is the `t`-average of the `s`-averages of the coboundaries
`g ∘ (j +ᵥ ·) - g`. -/
lemma inv_card_smul_sum_vadd_inv_card_smul_sum_vadd_sub_inv_card_smul_sum_vadd (g : Ω → ℝ)
    (s : Finset G) {t : Finset G} (ht : t.Nonempty) (ω : Ω) :
    (s.card : ℝ)⁻¹ • ∑ i ∈ s, (t.card : ℝ)⁻¹ • ∑ j ∈ t, g (j +ᵥ (i +ᵥ ω)) -
        (s.card : ℝ)⁻¹ • ∑ i ∈ s, g (i +ᵥ ω) =
      (t.card : ℝ)⁻¹ • ∑ j ∈ t, (s.card : ℝ)⁻¹ • ∑ i ∈ s, (g (j +ᵥ (i +ᵥ ω)) - g (i +ᵥ ω)) := by
  have ht0 : (t.card : ℝ) ≠ 0 := by exact_mod_cast ht.card_pos.ne'
  have h1 : ∑ i ∈ s, (t.card : ℝ)⁻¹ • ∑ j ∈ t, g (j +ᵥ (i +ᵥ ω)) =
      (t.card : ℝ)⁻¹ * ∑ j ∈ t, ∑ i ∈ s, g (j +ᵥ (i +ᵥ ω)) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  have h2 : ∑ j ∈ t, (s.card : ℝ)⁻¹ • ∑ i ∈ s, (g (j +ᵥ (i +ᵥ ω)) - g (i +ᵥ ω)) =
      (s.card : ℝ)⁻¹ * ∑ j ∈ t, ∑ i ∈ s, g (j +ᵥ (i +ᵥ ω)) -
        t.card * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, g (i +ᵥ ω)) := by
    simp only [smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
  rw [h1, h2]
  simp only [smul_eq_mul]
  field_simp

/-- The average of a strictly invariant function is the function. -/
lemma inv_card_smul_sum_vadd_of_forall_vadd_eq {h : Ω → ℝ} (hh : ∀ (i : G) ω, h (i +ᵥ ω) = h ω)
    {s : Finset G} (hs : s.Nonempty) (ω : Ω) : (s.card : ℝ)⁻¹ • ∑ i ∈ s, h (i +ᵥ ω) = h ω := by
  simp only [hh, Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  rw [inv_mul_cancel_left₀ (by exact_mod_cast hs.card_pos.ne')]

end Averages

/-! ### The maximal inequality for real functions along a regular increasing sequence -/

section Maximal

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] {F : ℕ → Finset G}

/-- `{sup_n |R_n f| > c} ⊆ {sup_n R_n ‖f‖ₑ > c}`. -/
lemma setOf_exists_lt_abs_div_card_subset (hne : ∀ n, (F n).Nonempty) (f : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) :
    {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ⊆
      {ω | ENNReal.ofReal c < ergodicMaximalFunction F (fun ω ↦ ‖f ω‖ₑ) ω} := by
  intro ω ⟨n, hn⟩
  refine lt_ergodicMaximalFunction_iff.2 ⟨n, ?_⟩
  have hcard : (0 : ℝ) < (F n).card := by exact_mod_cast (hne n).card_pos
  rw [abs_div, Nat.abs_cast, lt_div_iff₀ hcard] at hn
  have hn' : c * (F n).card < ∑ j ∈ F n, |f (j +ᵥ ω)| :=
    hn.trans_le (Finset.abs_sum_le_sum_abs _ _)
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast hcard.ne'))
    (Or.inl (ENNReal.natCast_ne_top _))]
  simp_rw [Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ abs_nonneg _, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul hc.le]
  exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hc hcard).trans hn')).2 hn'

variable [DecidableEq G] [MeasurableSpace Ω] {μ : Measure Ω} {C : ℝ≥0∞}

/-- **Tempelman's maximal inequality for real functions**: `μ(sup_n |R_n f| > c) ≤ C μ(|f|) / c`
along an increasing sequence of non-empty finite sets with `|F n - F n + F n| ≤ C |F n|`
(Georgii (14.A6) without the cube geometry, in the form used in the proof of (14.A8)). -/
theorem measure_exists_lt_abs_div_card_le_of_monotone
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hF : Monotone F) (hne : (F 0).Nonempty)
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) {f : Ω → ℝ} (hf : Measurable f)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ≤
      C * (∫⁻ ω, ‖f ω‖ₑ ∂μ) / ENNReal.ofReal c := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact (mul_le_mul_right (measure_mono
    (setOf_exists_lt_abs_div_card_subset (fun n ↦ hne.mono (hF (Nat.zero_le n))) f hc)) _).trans
    (mul_measure_lt_ergodicMaximalFunction_le_of_monotone hθ hF hne hC hf.enorm _)

end Maximal

/-! ### The pointwise ergodic theorem -/

section Pointwise

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω}
  [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [IsFiniteMeasure μ] [Countable G]
  [DecidableEq G] {F : ℕ → Finset G} {C : ℝ≥0∞}

/-- The invariant σ-algebra of the action, `MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
local notation "𝓘" => MeasurableSpace.smulInvariants (Multiplicative G) Ω

/-- **The key estimate in Georgii's proof of (14.A8).** For integrable measurable `f` and
`ε > 0`, `μ(∃ᶠ n, |R_n f - μ[f | 𝓘]| ≥ 4ε) ≤ 3ε`. -/
theorem measure_frequently_le_abs_inv_card_smul_sum_vadd_sub_condExp_le
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfm : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ᶠ n in atTop, 4 * ε ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) -
      (μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω|} ≤
      3 * ENNReal.ofReal ε := by
  have h𝓘le : 𝓘 ≤ ‹MeasurableSpace Ω› := MeasurableSpace.smulInvariants_le
  have hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ := fun g ↦ measurePreserving_vadd g μ
  have hne' : ∀ n, (F n).Nonempty := fun n ↦ hne.mono (hF (Nat.zero_le n))
  -- The approximation scale `η = ε² / (C + 1)`, so that `C η / ε ≤ ε` and `η / ε ≤ ε`.
  set η : ℝ := ε ^ 2 / (C.toReal + 1) with hη
  have hηpos : 0 < η := by positivity
  have hηε : η ≤ ε ^ 2 := div_le_self (sq_nonneg _) (by linarith [ENNReal.toReal_nonneg (a := C)])
  have hCη : C * ENNReal.ofReal η ≤ ENNReal.ofReal (ε ^ 2) := by
    rw [← ENNReal.ofReal_toReal hC', ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hη, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [ENNReal.toReal_nonneg (a := C), sq_nonneg ε]
  have hεε : ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε = ENNReal.ofReal ε := by
    rw [sq, ENNReal.ofReal_mul hε.le,
      ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top]
  -- A bounded measurable `g` with `‖f - g‖₁ < η`.
  obtain ⟨g, hgf, -⟩ := (memLp_one_iff_integrable.2 hf).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ENNReal.ofReal_pos.2 hηpos).ne'
  obtain ⟨M, hM⟩ := g.exists_forall_norm_le
  have hM' : ∀ ω, |g ω| ≤ M := fun ω ↦ by simpa only [Real.norm_eq_abs] using hM ω
  have hgi : Integrable g μ := g.integrable_of_isFiniteMeasure
  have hgm : Measurable g := g.measurable
  -- The mean ergodic theorem: `N` with `‖R_N g - μ[g | 𝓘]‖₁ < η`.
  obtain ⟨N, hN⟩ := ((tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one
    (Eventually.of_forall hne') hFol hgi).eventually
      (gt_mem_nhds (ENNReal.ofReal_pos.2 hηpos))).exists
  set cf := μ[f | 𝓘] with hcf
  set cg := μ[⇑g | 𝓘] with hcg
  set u₁ : Ω → ℝ := f - ⇑g with hu₁
  set u₂ : Ω → ℝ := fun ω ↦ ((F N).card : ℝ)⁻¹ • ∑ i ∈ F N, g (i +ᵥ ω) - cg ω with hu₂
  have hcgm : Measurable[𝓘] cg := stronglyMeasurable_condExp.measurable
  have hcg_inv : ∀ (i : G) ω, cg (i +ᵥ ω) = cg ω := fun i ω ↦
    MeasurableSpace.smul_eq_of_measurable_invariants hcgm (Multiplicative.ofAdd i) ω
  have hu₁m : Measurable u₁ := hfm.sub hgm
  have hu₂m : Measurable u₂ :=
    (measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦ hgm.comp (measurable_const_vadd i))).sub
        (hcgm.mono h𝓘le le_rfl)
  have hu₁L : ∫⁻ ω, ‖u₁ ω‖ₑ ∂μ ≤ ENNReal.ofReal η := by
    rw [← eLpNorm_one_eq_lintegral_enorm]; exact hgf.le
  have hu₂L : ∫⁻ ω, ‖u₂ ω‖ₑ ∂μ ≤ ENNReal.ofReal η := by
    rw [← eLpNorm_one_eq_lintegral_enorm]; exact hN.le
  -- The three exceptional sets.
  set A₁ := {ω | ∃ n, ε < |(∑ j ∈ F n, u₁ (j +ᵥ ω)) / (F n).card|} with hA₁
  set A₂ := {ω | ∃ n, ε < |(∑ j ∈ F n, u₂ (j +ᵥ ω)) / (F n).card|} with hA₂
  set A₃ := {ω | ε < |(μ[u₁ | 𝓘]) ω|} with hA₃
  have hμA₁ : μ A₁ ≤ ENNReal.ofReal ε := by
    calc μ A₁ ≤ C * (∫⁻ ω, ‖u₁ ω‖ₑ ∂μ) / ENNReal.ofReal ε :=
          measure_exists_lt_abs_div_card_le_of_monotone hθ hF hne hC hu₁m hε
      _ ≤ ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε := by
          gcongr; exact (mul_le_mul' le_rfl hu₁L).trans hCη
      _ = ENNReal.ofReal ε := hεε
  have hμA₂ : μ A₂ ≤ ENNReal.ofReal ε := by
    calc μ A₂ ≤ C * (∫⁻ ω, ‖u₂ ω‖ₑ ∂μ) / ENNReal.ofReal ε :=
          measure_exists_lt_abs_div_card_le_of_monotone hθ hF hne hC hu₂m hε
      _ ≤ ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε := by
          gcongr; exact (mul_le_mul' le_rfl hu₂L).trans hCη
      _ = ENNReal.ofReal ε := hεε
  have hμA₃ : μ A₃ ≤ ENNReal.ofReal ε := by
    have hsub : A₃ ⊆ {ω | ENNReal.ofReal ε ≤ ‖(μ[u₁ | 𝓘]) ω‖ₑ} := fun ω hω ↦ by
      rw [Set.mem_ofPred_eq, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal hω.le
    calc μ A₃ ≤ μ {ω | ENNReal.ofReal ε ≤ ‖(μ[u₁ | 𝓘]) ω‖ₑ} := measure_mono hsub
      _ ≤ (∫⁻ ω, ‖(μ[u₁ | 𝓘]) ω‖ₑ ∂μ) / ENNReal.ofReal ε :=
          meas_ge_le_lintegral_div
            (stronglyMeasurable_condExp.mono h𝓘le).measurable.enorm.aemeasurable
            (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε := by
          gcongr
          rw [← eLpNorm_one_eq_lintegral_enorm]
          exact (eLpNorm_condExp_le_eLpNorm _ le_rfl).trans
            (hgf.le.trans (ENNReal.ofReal_le_ofReal hηε))
      _ = ENNReal.ofReal ε := hεε
  -- The a.e. identity `μ[f - g | 𝓘] = μ[f | 𝓘] - μ[g | 𝓘]`.
  have hE : ∀ᵐ ω ∂μ, (μ[u₁ | 𝓘]) ω = cf ω - cg ω := by
    filter_upwards [condExp_sub hf hgi 𝓘] with ω hω
    exact hω
  -- The pointwise decomposition.
  have hdecomp : ∀ n ω, ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω =
      (∑ j ∈ F n, u₁ (j +ᵥ ω)) / (F n).card +
      (((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, g (i +ᵥ ω) -
        ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ((F N).card : ℝ)⁻¹ • ∑ j ∈ F N, g (j +ᵥ (i +ᵥ ω))) +
      (∑ j ∈ F n, u₂ (j +ᵥ ω)) / (F n).card + (cg ω - cf ω) := by
    intro n ω
    have hinv := inv_card_smul_sum_vadd_of_forall_vadd_eq hcg_inv (hne' n) ω
    simp only [hu₁, hu₂, Pi.sub_apply, Finset.sum_sub_distrib, div_eq_inv_mul, smul_eq_mul,
      mul_sub] at hinv ⊢
    rw [hinv]
    ring
  -- Outside `A₁ ∪ A₂ ∪ A₃` and the null set, `|R_n f - μ[f | 𝓘]| < 4ε` eventually.
  have hsub : {ω | ∃ᶠ n in atTop, 4 * ε ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|} ⊆
      A₁ ∪ A₂ ∪ A₃ ∪ {ω | ¬ (μ[u₁ | 𝓘]) ω = cf ω - cg ω} := by
    intro ω hω
    by_contra hcon
    simp only [hA₁, hA₂, hA₃, Set.mem_union, not_or, Set.mem_ofPred_eq, not_exists, not_lt,
      not_not] at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    have hlim : Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, g (i +ᵥ ω) -
        ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ((F N).card : ℝ)⁻¹ • ∑ j ∈ F N, g (j +ᵥ (i +ᵥ ω)))
        atTop (𝓝 0) := by
      have := ((tendsto_finsetSum (F N) fun j _ ↦
        tendsto_inv_card_smul_sum_vadd_sub_vadd hFol hM' j ω).const_smul ((F N).card : ℝ)⁻¹).neg
      simp only [Finset.sum_const_zero, smul_zero, neg_zero] at this
      refine this.congr fun n ↦ ?_
      rw [← inv_card_smul_sum_vadd_inv_card_smul_sum_vadd_sub_inv_card_smul_sum_vadd g (F n)
        (hne' N) ω, neg_sub]
    have hev : ∀ᶠ n in atTop, |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, g (i +ᵥ ω) -
        ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ((F N).card : ℝ)⁻¹ • ∑ j ∈ F N, g (j +ᵥ (i +ᵥ ω))| < ε := by
      have := Metric.tendsto_nhds.1 hlim ε hε
      simpa only [Real.dist_0_eq_abs] using this
    obtain ⟨n, hn, hn'⟩ := (hω.and_eventually hev).exists
    rw [hdecomp] at hn
    have hb : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d ↦ by
      linarith [abs_add_le (a + b + c) d, abs_add_le (a + b) c, abs_add_le a b]
    have h4' : |cg ω - cf ω| ≤ ε := by rw [abs_sub_comm, ← h4]; exact h3
    linarith [hn.trans (hb _ _ _ _), h1 n, h2 n]
  have hnull : μ {ω | ¬ (μ[u₁ | 𝓘]) ω = cf ω - cg ω} = 0 := ae_iff.1 hE
  calc μ {ω | ∃ᶠ n in atTop, 4 * ε ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|}
      ≤ μ (A₁ ∪ A₂ ∪ A₃ ∪ {ω | ¬ (μ[u₁ | 𝓘]) ω = cf ω - cg ω}) := measure_mono hsub
    _ ≤ μ (A₁ ∪ A₂ ∪ A₃) + μ {ω | ¬ (μ[u₁ | 𝓘]) ω = cf ω - cg ω} := measure_union_le _ _
    _ ≤ μ (A₁ ∪ A₂) + μ A₃ + 0 := by rw [hnull]; gcongr; exact measure_union_le _ _
    _ ≤ μ A₁ + μ A₂ + μ A₃ + 0 := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + 0 := by gcongr
    _ = 3 * ENNReal.ofReal ε := by ring

/-- The pointwise ergodic theorem for a measurable integrable function; see
`ae_tendsto_inv_card_smul_sum_vadd_condExp` for the general statement. -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measurable
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfm : Measurable f) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) := by
  set cf := μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω] with hcf
  have key : ∀ δ : ℝ, 0 < δ →
      ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω| < δ := by
    intro δ hδ
    rw [ae_iff]
    have hset : {ω | ¬ ∀ᶠ n in atTop, |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω| < δ} =
        {ω | ∃ᶠ n in atTop, δ ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Filter.not_eventually, not_lt]
    rw [hset]
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) bot_le
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
    set ε' : ℝ := min (δ / 4) (ε / 3) with hε'def
    have hε'pos : 0 < ε' := lt_min (by positivity) (by positivity)
    have hsub : {ω | ∃ᶠ n in atTop, δ ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|} ⊆
        {ω | ∃ᶠ n in atTop, 4 * ε' ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|} :=
      fun ω hω ↦ hω.mono fun n hn ↦ le_trans (by linarith [min_le_left (δ / 4) (ε / 3)]) hn
    calc μ {ω | ∃ᶠ n in atTop, δ ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|}
        ≤ μ {ω | ∃ᶠ n in atTop, 4 * ε' ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) - cf ω|} :=
          measure_mono hsub
      _ ≤ 3 * ENNReal.ofReal ε' :=
          measure_frequently_le_abs_inv_card_smul_sum_vadd_sub_condExp_le hF hne hFol hC hC' hf
            hfm hε'pos
      _ ≤ 3 * ENNReal.ofReal (ε / 3) := by gcongr; exact min_le_right _ _
      _ = 0 + ε := by
          rw [zero_add, ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_coe_nnreal, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
  have := ae_all_iff.2 fun k : ℕ ↦ key (1 / ((k : ℝ) + 1)) (by positivity)
  filter_upwards [this] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  exact (hω k).mono fun n hn ↦ by rw [Real.dist_eq]; exact hn.trans hk

/-- **The pointwise ergodic theorem along a regular Følner sequence** (Georgii, Theorem (14.A8),
for a general countable abelian group). Let `G` act on a finite measure space `(Ω, μ)` by
measure-preserving maps `ω ↦ i +ᵥ ω`, and let `F : ℕ → Finset G` be increasing, non-empty,
Følner (`|(g +ᵥ F n) ∆ F n| / |F n| → 0`) and Tempelman-regular (`|F n - F n + F n| ≤ C |F n|`
with `C < ∞`). Then for every integrable `f : Ω → ℝ`, for `μ`-a.e. `ω`,
`|F n|⁻¹ ∑_{i ∈ F n} f (i +ᵥ ω) → μ[f | 𝓘] ω`, where `𝓘` is the invariant σ-algebra
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) := by
  set f' := hf.1.mk f with hf'def
  have hf' : Integrable f' μ := hf.congr hf.1.ae_eq_mk
  have h := ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measurable hF hne hFol hC hC' hf'
    hf.1.measurable_mk
  have h1 : ∀ᵐ ω ∂μ, ∀ n, ∀ i ∈ F n, f (i +ᵥ ω) = f' (i +ᵥ ω) :=
    ae_all_iff.2 fun n ↦ (eventually_all_finset _).2 fun i _ ↦
      (measurePreserving_vadd i μ).quasiMeasurePreserving.ae_eq_comp hf.1.ae_eq_mk
  have h2 : μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω] =ᵐ[μ]
      μ[f' | MeasurableSpace.smulInvariants (Multiplicative G) Ω] := condExp_congr_ae hf.1.ae_eq_mk
  filter_upwards [h, h1, h2] with ω hω h1 h2
  rw [h2]
  exact hω.congr fun n ↦ by rw [Finset.sum_congr rfl fun i hi ↦ (h1 n i hi).symm]

/-- The pointwise ergodic theorem simultaneously for a countable family of integrable functions:
`μ`-a.e. `ω` is *generic* for all of them at once. This is the form used by Georgii in the proof
of Theorem (14.10). -/
theorem ae_forall_tendsto_inv_card_smul_sum_vadd_condExp
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {ι : Type*} [Countable ι] {f : ι → Ω → ℝ} (hf : ∀ k, Integrable (f k) μ) :
    ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f k (i +ᵥ ω)) atTop
      (𝓝 ((μ[f k | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) :=
  ae_all_iff.2 fun k ↦ ae_tendsto_inv_card_smul_sum_vadd_condExp hF hne hFol hC hC' (hf k)

end Pointwise

/-! ### Cubes in `ℤ^d`: Georgii's Theorem (14.A8) -/

section Cube

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sub-cube `[m, r - m)^d` of `[0, r)^d`, `m = ∑ |g_i|`, lies in the cube and in its
translate by `g`. -/
lemma piFinset_Ico_subset_inter_vadd_piFinset_Ico (g : ι → ℤ) (r : ℕ) :
    (Fintype.piFinset fun _ : ι ↦ Finset.Ico ((∑ k, (g k).natAbs : ℕ) : ℤ)
        (r - (∑ k, (g k).natAbs : ℕ))) ⊆
      (g +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r) ∩
        Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r := by
  intro y hy
  rw [Fintype.mem_piFinset] at hy
  have hg : ∀ k, (g k).natAbs ≤ ∑ k, (g k).natAbs := fun k ↦
    Finset.single_le_sum (f := fun k ↦ (g k).natAbs) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ k)
  refine Finset.mem_inter.2 ⟨Finset.mem_vadd_finset_iff_sub_mem.2 ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro k
    have := Finset.mem_Ico.1 (hy k)
    have := hg k
    simp only [Pi.sub_apply, Finset.mem_Ico]
    omega
  · rw [Fintype.mem_piFinset]
    intro k
    have := Finset.mem_Ico.1 (hy k)
    have := hg k
    simp only [Finset.mem_Ico]
    omega

/-- `|(g +ᵥ [0, r)^d) ∆ [0, r)^d| ≤ 2 (r^d - (r - 2m)^d)` with `m = ∑ |g_i|`. -/
lemma card_vadd_piFinset_Ico_symmDiff_le (g : ι → ℤ) (r : ℕ) :
    (((g +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r) ∆
        Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r).card : ℝ) ≤
      2 * ((r : ℝ) ^ Fintype.card ι - ((r - 2 * ∑ k, (g k).natAbs : ℕ) : ℝ) ^ Fintype.card ι) := by
  set m : ℕ := ∑ k, (g k).natAbs with hm
  set Q : Finset (ι → ℤ) := Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r with hQ
  set S : Finset (ι → ℤ) := Fintype.piFinset fun _ : ι ↦ Finset.Ico (m : ℤ) (r - m) with hS
  have hSsub := piFinset_Ico_subset_inter_vadd_piFinset_Ico g r
  rw [← hm, ← hQ, ← hS] at hSsub
  have hS1 : S ⊆ g +ᵥ Q := hSsub.trans Finset.inter_subset_left
  have hS2 : S ⊆ Q := hSsub.trans Finset.inter_subset_right
  have hQcard : Q.card = r ^ Fintype.card ι := by
    simp [hQ, Fintype.card_piFinset, Int.card_Ico]
  have hScard : S.card = (r - 2 * m) ^ Fintype.card ι := by
    simp only [hS, Fintype.card_piFinset, Int.card_Ico, Finset.prod_const, Finset.card_univ]
    congr 1
    omega
  have hSQ : S.card ≤ Q.card := Finset.card_le_card hS2
  have hsub : (g +ᵥ Q) ∆ Q ⊆ ((g +ᵥ Q) \ S) ∪ (Q \ S) := by
    rw [Finset.symmDiff_def]
    exact Finset.union_subset_union (Finset.sdiff_subset_sdiff le_rfl hS2)
      (Finset.sdiff_subset_sdiff le_rfl hS1)
  have h1 : ((g +ᵥ Q) ∆ Q).card ≤ 2 * (Q.card - S.card) := by
    calc ((g +ᵥ Q) ∆ Q).card ≤ (((g +ᵥ Q) \ S) ∪ (Q \ S)).card := Finset.card_le_card hsub
      _ ≤ ((g +ᵥ Q) \ S).card + (Q \ S).card := Finset.card_union_le _ _
      _ = 2 * (Q.card - S.card) := by
          rw [Finset.card_sdiff_of_subset hS1, Finset.card_sdiff_of_subset hS2,
            Finset.card_vadd_finset]
          ring
  have h2 : (((g +ᵥ Q) ∆ Q).card : ℝ) ≤ 2 * ((Q.card : ℝ) - S.card) := by
    rw [← Nat.cast_sub hSQ]; exact_mod_cast h1
  rw [hQcard, hScard] at h2
  push_cast at h2
  exact h2

/-- **The cubes `x_n + [0, r_n)^d` form a Følner sequence** as soon as `r_n → ∞`:
`|(g +ᵥ Λ_n) ∆ Λ_n| / |Λ_n| → 0` for every `g ∈ ℤ^d`. -/
theorem tendsto_card_vadd_cube_symmDiff_div_card (x : ℕ → ι → ℤ) {r : ℕ → ℕ}
    (hr : Tendsto r atTop atTop) (g : ι → ℤ) :
    Tendsto (fun n ↦ (((g +ᵥ (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))) ∆
        (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))).card : ℝ) /
      (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card) atTop (𝓝 0) := by
  set m : ℕ := ∑ k, (g k).natAbs with hm
  -- Translation by `x n` does not change the ratio.
  have htrans : ∀ n, (((g +ᵥ (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))) ∆
        (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))).card : ℝ) /
      (x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card =
      (((g +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)) ∆
        Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card : ℝ) /
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card := fun n ↦ by
    rw [vadd_vadd, add_comm, ← vadd_vadd, ← Finset.vadd_finset_symmDiff, Finset.card_vadd_finset,
      Finset.card_vadd_finset]
  simp only [htrans]
  -- The ratio for the cube `[0, r)^d`, as a function of `r`.
  have hratio : Tendsto (fun r : ℕ ↦ (((g +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r) ∆
      Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r).card : ℝ) /
      (Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r).card) atTop (𝓝 0) := by
    have hQcard : ∀ r : ℕ, ((Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) r).card : ℝ) =
        (r : ℝ) ^ Fintype.card ι := fun r ↦ by
      simp [Fintype.card_piFinset, Int.card_Ico]
    -- `(r - 2m) / r → 1`.
    have hq : Tendsto (fun r : ℕ ↦ ((r - 2 * m : ℕ) : ℝ) / r) atTop (𝓝 1) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (2 * m : ℝ)).const_sub 1
      rw [sub_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (2 * m + 1)] with r hr
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      rw [Nat.cast_sub (by omega)]
      field_simp
      push_cast
      ring
    have hlim : Tendsto (fun r : ℕ ↦ 2 * (1 - (((r - 2 * m : ℕ) : ℝ) / r) ^ Fintype.card ι))
        atTop (𝓝 0) := by
      have := ((hq.pow (Fintype.card ι)).const_sub 1).const_mul 2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun r ↦ by positivity) ?_
    filter_upwards [eventually_gt_atTop 0] with r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    rw [hQcard, div_le_iff₀ (by positivity)]
    have hkey : (((r - 2 * m : ℕ) : ℝ) / r) ^ Fintype.card ι * (r : ℝ) ^ Fintype.card ι =
        ((r - 2 * m : ℕ) : ℝ) ^ Fintype.card ι := by
      rw [div_pow, div_mul_cancel₀ _ (by positivity)]
    have := card_vadd_piFinset_Ico_symmDiff_le g r
    rw [← hm] at this
    linarith
  exact hratio.comp hr

/-- **Georgii, Theorem (14.A8): the multidimensional individual ergodic theorem.** Let `ℤ^d`
act on a finite measure space `(Ω, μ)` by measure-preserving maps, and let
`Λ_n = x_n + [0, r_n)^d` be an increasing sequence of cubes with `|Λ_n| → ∞`. Then for every
integrable `f : Ω → ℝ`, `μ`-a.s., `R_n f = |Λ_n|⁻¹ ∑_{i ∈ Λ_n} f ∘ (i +ᵥ ·) → μ[f | 𝓘]`, where
`𝓘 = MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ)) Ω` is the σ-algebra of invariant
events. The regularity constant of the cubes is `3 ^ d`. -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp_cube {Ω : Type*} [AddAction (ι → ℤ) Ω]
    [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableConstVAdd (ι → ℤ) Ω]
    [VAddInvariantMeasure (ι → ℤ) Ω μ] [IsFiniteMeasure μ] (x : ℕ → ι → ℤ) {r : ℕ → ℕ}
    (hr : ∀ n, 0 < r n) (hr' : Tendsto r atTop atTop)
    (hΛ : Monotone fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n))
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      ((x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card : ℝ)⁻¹ •
        ∑ i ∈ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n), f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ)) Ω]) ω)) := by
  refine ae_tendsto_inv_card_smul_sum_vadd_condExp (C := 3 ^ Fintype.card ι) hΛ ?_
    (tendsto_card_vadd_cube_symmDiff_div_card x hr') (fun n ↦ ?_) (by simp) hf
  · exact ⟨x 0, Finset.mem_vadd_finset.2 ⟨0, Fintype.mem_piFinset.2 fun i ↦ by
      simp only [Pi.zero_apply, Finset.mem_Ico, le_refl, true_and]; exact_mod_cast hr 0, by simp⟩⟩
  · exact_mod_cast card_sub_add_cube_le (x n) (r n)

end Cube

end MeasureTheory

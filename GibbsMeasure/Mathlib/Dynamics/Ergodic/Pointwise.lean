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

Monotonicity and Tempelman regularity are used for one purpose only, the weak type `(1,1)`
maximal inequality, and the theorem is stated so that this is visible:

* `MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le`
  and its countable-family form assume of `F` only the Følner property and
  `μ(sup_n |R_n u| > c) ≤ C ‖u‖₁ / c`; the three theorems above are its corollaries.
* `MeasureTheory.measure_exists_lt_abs_div_card_le_of_forall_exists_subset` supplies that
  hypothesis for a sequence `F` that is *dominated* by an increasing Tempelman-regular sequence
  `F'` — every `F n` inside some `F' k` with `|F' k| ≤ D |F n|` — with constant `C D`, the
  averages along `F` being bounded by `D` times the maximal function along `F'`
  (`MeasureTheory.ergodicMaximalFunction_le_of_forall_exists_subset`). Nothing is assumed about
  `F` itself.
* `MeasureTheory.ae_tendsto_inv_card_smul_sum_vadd_condExp_cube_of_forall_abs_le` is the cube
  case: `Λ_n = x_n + [0, r_n)^d` with `r_n → ∞` and `|x_n(i)| ≤ K r_n`, neither nested nor ordered
  by size, dominated by the increasing cubes `[−K(k+1), (K+1)(k+1))^d`. Georgii's increasing cubes
  are the case `K = 1` after the translation that puts `0` into `Λ_0`.

For cubes with unrestricted centres — Georgii's `|Λ| → ∞` in §15.5 — the individual theorem is
*not* available: the maximal inequality itself fails (see the docstring of the cube theorem for a
counterexample on `ℤ/M`), and moving averages `[a_n, a_n + L_n)` with `a_n / L_n → ∞` are the
classical counterexamples to a.e. convergence (Akcoglu–del Junco; Bellow–Jones–Rosenblatt). The
*mean* ergodic theorem (14.A5) is not affected — it holds along every Følner sequence — which is
what Georgii's (15.44) actually uses.

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
* `Monotone F`, `(F 0).Nonempty`: only to produce the maximal inequality, in the form provided by
  `mul_measure_lt_ergodicMaximalFunction_le_of_monotone`; `0 ∈ F n` is not needed. The proof
  itself uses nothing but `∀ n, (F n).Nonempty`, the Følner property and that inequality.
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

/-! ### Maximal functions of a dominated sequence of averaging sets -/

section Domination

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] {F F' : ℕ → Finset G} {D : ℝ≥0∞}

/-- **A dominated maximal function.** If every `F n` is contained in a set `F' k` of comparable
size, `|F' k| ≤ D |F n|`, then the maximal function along `F` is at most `D` times the maximal
function along `F'`: the `F n`-average of a nonnegative function is at most `|F' k| / |F n|` times
its `F' k`-average. Nothing is assumed about the sequence `F` itself; in particular it need not be
monotone, and the index `k` need not be related to `n`. -/
lemma ergodicMaximalFunction_le_of_forall_exists_subset (hne : ∀ n, (F n).Nonempty)
    (hD : ∀ n, ∃ k, F n ⊆ F' k ∧ ((F' k).card : ℝ≥0∞) ≤ D * (F n).card) (f : Ω → ℝ≥0∞) (ω : Ω) :
    ergodicMaximalFunction F f ω ≤ D * ergodicMaximalFunction F' f ω := by
  refine iSup_le fun n ↦ ?_
  obtain ⟨k, hsub, hcard⟩ := hD n
  have hn0 : ((F n).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast (hne n).card_pos.ne'
  have hk0 : ((F' k).card : ℝ≥0∞) ≠ 0 := by exact_mod_cast ((hne n).mono hsub).card_pos.ne'
  rw [ENNReal.div_le_iff_le_mul (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top _))]
  calc ∑ j ∈ F n, f (j +ᵥ ω)
      ≤ ∑ j ∈ F' k, f (j +ᵥ ω) := Finset.sum_le_sum_of_subset hsub
    _ = ((F' k).card : ℝ≥0∞) * ((∑ j ∈ F' k, f (j +ᵥ ω)) / (F' k).card) :=
        (ENNReal.mul_div_cancel hk0 (ENNReal.natCast_ne_top _)).symm
    _ ≤ (D * (F n).card) * ((∑ j ∈ F' k, f (j +ᵥ ω)) / (F' k).card) := by gcongr
    _ ≤ (D * (F n).card) * ergodicMaximalFunction F' f ω := by
        gcongr
        exact le_iSup (fun k ↦ (∑ j ∈ F' k, f (j +ᵥ ω)) / (F' k).card) k
    _ = D * ergodicMaximalFunction F' f ω * (F n).card := by ring

variable [DecidableEq G] [MeasurableSpace Ω] {μ : Measure Ω} {C : ℝ≥0∞}

/-- **The weak type `(1,1)` maximal inequality for a dominated sequence.** Let `F'` be an
increasing Tempelman-regular sequence of finite sets, `|F' k − F' k + F' k| ≤ C |F' k|`, and let
`F` be an *arbitrary* sequence of non-empty finite sets, each contained in some `F' k` with
`|F' k| ≤ D |F n|`. Then `μ(sup_n |R_n f| > c) ≤ C D μ(|f|) / c`.

Monotonicity is required of the dominating sequence `F'`, where Tempelman's covering argument
(Georgii (14.A6), `mul_measure_lt_ergodicMaximalFunction_le_of_monotone`) takes place, and not of
`F`. -/
theorem measure_exists_lt_abs_div_card_le_of_forall_exists_subset
    (hθ : ∀ g : G, MeasurePreserving (g +ᵥ · : Ω → Ω) μ μ) (hF' : Monotone F')
    (hne' : (F' 0).Nonempty) (hC : ∀ k, ((F' k - F' k + F' k).card : ℝ≥0∞) ≤ C * (F' k).card)
    (hne : ∀ n, (F n).Nonempty) (hD0 : D ≠ 0) (hDtop : D ≠ ∞)
    (hD : ∀ n, ∃ k, F n ⊆ F' k ∧ ((F' k).card : ℝ≥0∞) ≤ D * (F n).card)
    {f : Ω → ℝ} (hf : Measurable f) {c : ℝ} (hc : 0 < c) :
    μ {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ≤
      C * D * (∫⁻ ω, ‖f ω‖ₑ ∂μ) / ENNReal.ofReal c := by
  have hsub : {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} ⊆
      {ω | ENNReal.ofReal c / D < ergodicMaximalFunction F' (fun ω ↦ ‖f ω‖ₑ) ω} := by
    intro ω hω
    have h1 := setOf_exists_lt_abs_div_card_subset hne f hc hω
    have h2 := ergodicMaximalFunction_le_of_forall_exists_subset hne hD (fun ω ↦ ‖f ω‖ₑ) ω
    rw [Set.mem_ofPred_eq, ENNReal.div_lt_iff (Or.inl hD0) (Or.inl hDtop)]
    exact lt_of_lt_of_le h1 (h2.trans (le_of_eq (mul_comm _ _)))
  have hcancel : ENNReal.ofReal c / D * D = ENNReal.ofReal c := ENNReal.div_mul_cancel hD0 hDtop
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top)]
  calc μ {ω | ∃ n, c < |(∑ j ∈ F n, f (j +ᵥ ω)) / (F n).card|} * ENNReal.ofReal c
      ≤ μ {ω | ENNReal.ofReal c / D < ergodicMaximalFunction F' (fun ω ↦ ‖f ω‖ₑ) ω}
          * ENNReal.ofReal c := by gcongr
    _ = ENNReal.ofReal c / D
          * μ {ω | ENNReal.ofReal c / D < ergodicMaximalFunction F' (fun ω ↦ ‖f ω‖ₑ) ω} * D := by
        rw [mul_assoc, mul_comm _ D, ← mul_assoc, hcancel, mul_comm]
    _ ≤ C * (∫⁻ ω, ‖f ω‖ₑ ∂μ) * D :=
        mul_le_mul'
          (mul_measure_lt_ergodicMaximalFunction_le_of_monotone hθ hF' hne' hC hf.enorm _) le_rfl
    _ = C * D * (∫⁻ ω, ‖f ω‖ₑ ∂μ) := by ring

end Domination

/-! ### The pointwise ergodic theorem -/

section Pointwise

variable {G Ω : Type*} [AddCommGroup G] [AddAction G Ω] [MeasurableSpace Ω] {μ : Measure Ω}
  [MeasurableConstVAdd G Ω] [VAddInvariantMeasure G Ω μ] [IsFiniteMeasure μ] [Countable G]
  [DecidableEq G] {F : ℕ → Finset G} {C : ℝ≥0∞}

/-- The invariant σ-algebra of the action, `MeasurableSpace.smulInvariants (Multiplicative G) Ω`. -/
local notation "𝓘" => MeasurableSpace.smulInvariants (Multiplicative G) Ω

/-- **The key estimate in Georgii's proof of (14.A8).** For integrable measurable `f` and
`ε > 0`, `μ(∃ᶠ n, |R_n f - μ[f | 𝓘]| ≥ 4ε) ≤ 3ε`.

The only property of the averaging sets used besides the Følner property is the weak type `(1,1)`
maximal inequality `hmax`, which is where the geometry of the sets enters; for an increasing
Tempelman-regular sequence it is `measure_exists_lt_abs_div_card_le_of_monotone`, and for a
sequence dominated by such a one it is
`measure_exists_lt_abs_div_card_le_of_forall_exists_subset`. -/
theorem measure_frequently_le_abs_inv_card_smul_sum_vadd_sub_condExp_le
    (hne : ∀ n, (F n).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hmax : ∀ u : Ω → ℝ, Measurable u → ∀ c : ℝ, 0 < c →
      μ {ω | ∃ n, c < |(∑ j ∈ F n, u (j +ᵥ ω)) / (F n).card|}
        ≤ C * (∫⁻ ω, ‖u ω‖ₑ ∂μ) / ENNReal.ofReal c)
    (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfm : Measurable f) {ε : ℝ} (hε : 0 < ε) :
    μ {ω | ∃ᶠ n in atTop, 4 * ε ≤ |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω) -
      (μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω|} ≤
      3 * ENNReal.ofReal ε := by
  have h𝓘le : 𝓘 ≤ ‹MeasurableSpace Ω› := MeasurableSpace.smulInvariants_le
  have hne' : ∀ n, (F n).Nonempty := hne
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
    calc μ A₁ ≤ C * (∫⁻ ω, ‖u₁ ω‖ₑ ∂μ) / ENNReal.ofReal ε := hmax u₁ hu₁m ε hε
      _ ≤ ENNReal.ofReal (ε ^ 2) / ENNReal.ofReal ε := by
          gcongr; exact (mul_le_mul' le_rfl hu₁L).trans hCη
      _ = ENNReal.ofReal ε := hεε
  have hμA₂ : μ A₂ ≤ ENNReal.ofReal ε := by
    calc μ A₂ ≤ C * (∫⁻ ω, ‖u₂ ω‖ₑ ∂μ) / ENNReal.ofReal ε := hmax u₂ hu₂m ε hε
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
    (hne : ∀ n, (F n).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hmax : ∀ u : Ω → ℝ, Measurable u → ∀ c : ℝ, 0 < c →
      μ {ω | ∃ n, c < |(∑ j ∈ F n, u (j +ᵥ ω)) / (F n).card|}
        ≤ C * (∫⁻ ω, ‖u ω‖ₑ ∂μ) / ENNReal.ofReal c)
    (hC' : C ≠ ∞)
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
          measure_frequently_le_abs_inv_card_smul_sum_vadd_sub_condExp_le hne hFol hmax hC' hf
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

/-- **The pointwise ergodic theorem from the maximal inequality** (the Banach principle behind
Georgii's Theorem (14.A8)). Let `G` act on a finite measure space `(Ω, μ)` by measure-preserving
maps `ω ↦ i +ᵥ ω` and let `F : ℕ → Finset G` be a Følner sequence of non-empty finite sets whose
maximal operator is of weak type `(1,1)` with a finite constant `C`, i.e.
`μ(sup_n |R_n u| > c) ≤ C ‖u‖₁ / c` for measurable `u` and `c > 0`. Then for every integrable
`f : Ω → ℝ`, for `μ`-a.e. `ω`, `|F n|⁻¹ ∑_{i ∈ F n} f (i +ᵥ ω) → μ[f | 𝓘] ω`, where `𝓘` is the
invariant σ-algebra `MeasurableSpace.smulInvariants (Multiplicative G) Ω`.

Neither monotonicity nor Tempelman regularity of `F` is used directly: they enter only through
the maximal inequality (`ae_tendsto_inv_card_smul_sum_vadd_condExp` for an increasing regular
sequence, `ae_tendsto_inv_card_smul_sum_vadd_condExp_cube_of_forall_abs_le` for cubes of bounded
eccentricity). The maximal hypothesis cannot be dropped: the mean ergodic theorem
`tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one` holds along every Følner sequence, but
the almost sure statement does not. -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le
    (hne : ∀ n, (F n).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hmax : ∀ u : Ω → ℝ, Measurable u → ∀ c : ℝ, 0 < c →
      μ {ω | ∃ n, c < |(∑ j ∈ F n, u (j +ᵥ ω)) / (F n).card|}
        ≤ C * (∫⁻ ω, ‖u ω‖ₑ ∂μ) / ENNReal.ofReal c)
    (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) := by
  set f' := hf.1.mk f with hf'def
  have hf' : Integrable f' μ := hf.congr hf.1.ae_eq_mk
  have h := ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measurable hne hFol hmax hC' hf'
    hf.1.measurable_mk
  have h1 : ∀ᵐ ω ∂μ, ∀ n, ∀ i ∈ F n, f (i +ᵥ ω) = f' (i +ᵥ ω) :=
    ae_all_iff.2 fun n ↦ (eventually_all_finset _).2 fun i _ ↦
      (measurePreserving_vadd i μ).quasiMeasurePreserving.ae_eq_comp hf.1.ae_eq_mk
  have h2 : μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω] =ᵐ[μ]
      μ[f' | MeasurableSpace.smulInvariants (Multiplicative G) Ω] := condExp_congr_ae hf.1.ae_eq_mk
  filter_upwards [h, h1, h2] with ω hω h1 h2
  rw [h2]
  exact hω.congr fun n ↦ by rw [Finset.sum_congr rfl fun i hi ↦ (h1 n i hi).symm]

/-- **The pointwise ergodic theorem along a regular Følner sequence** (Georgii, Theorem (14.A8),
for a general countable abelian group). Let `G` act on a finite measure space `(Ω, μ)` by
measure-preserving maps `ω ↦ i +ᵥ ω`, and let `F : ℕ → Finset G` be increasing, non-empty,
Følner (`|(g +ᵥ F n) ∆ F n| / |F n| → 0`) and Tempelman-regular (`|F n - F n + F n| ≤ C |F n|`
with `C < ∞`). Then for every integrable `f : Ω → ℝ`, for `μ`-a.e. `ω`,
`|F n|⁻¹ ∑_{i ∈ F n} f (i +ᵥ ω) → μ[f | 𝓘] ω`, where `𝓘` is the invariant σ-algebra
`MeasurableSpace.smulInvariants (Multiplicative G) Ω`.

This is the case of `ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le`
in which the maximal inequality is Tempelman's
(`measure_exists_lt_abs_div_card_le_of_monotone`). -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp
    (hF : Monotone F) (hne : (F 0).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hC : ∀ n, ((F n - F n + F n).card : ℝ≥0∞) ≤ C * (F n).card) (hC' : C ≠ ∞)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) :=
  ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le
    (fun n ↦ hne.mono (hF (Nat.zero_le n))) hFol
    (fun _u hu _c hc ↦ measure_exists_lt_abs_div_card_le_of_monotone
      (fun g ↦ measurePreserving_vadd g μ) hF hne hC hu hc) hC' hf

/-- The pointwise ergodic theorem simultaneously for a countable family of integrable functions:
`μ`-a.e. `ω` is *generic* for all of them at once, under the weak type `(1,1)` maximal inequality
of `ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le`. -/
theorem ae_forall_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le
    (hne : ∀ n, (F n).Nonempty)
    (hFol : ∀ g : G, Tendsto (fun n ↦ (((g +ᵥ F n) ∆ F n).card : ℝ) / (F n).card) atTop (𝓝 0))
    (hmax : ∀ u : Ω → ℝ, Measurable u → ∀ c : ℝ, 0 < c →
      μ {ω | ∃ n, c < |(∑ j ∈ F n, u (j +ᵥ ω)) / (F n).card|}
        ≤ C * (∫⁻ ω, ‖u ω‖ₑ ∂μ) / ENNReal.ofReal c)
    (hC' : C ≠ ∞)
    {ι : Type*} [Countable ι] {f : ι → Ω → ℝ} (hf : ∀ k, Integrable (f k) μ) :
    ∀ᵐ ω ∂μ, ∀ k, Tendsto (fun n ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, f k (i +ᵥ ω)) atTop
      (𝓝 ((μ[f k | MeasurableSpace.smulInvariants (Multiplicative G) Ω]) ω)) :=
  ae_all_iff.2 fun k ↦
    ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le hne hFol hmax
      hC' (hf k)

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

open scoped Pointwise in
/-- Membership in a translated cube of `ℤ^d`: `y ∈ a + [0, R)^d` iff `a i ≤ y i < a i + R` for
every coordinate `i`. -/
lemma _root_.Fintype.mem_vadd_piFinset_Ico {a y : ι → ℤ} {R : ℤ} :
    y ∈ a +ᵥ Fintype.piFinset (fun _ : ι ↦ Finset.Ico (0 : ℤ) R) ↔
      ∀ i, a i ≤ y i ∧ y i < a i + R := by
  rw [Finset.mem_vadd_finset]
  constructor
  · rintro ⟨z, hz, rfl⟩ i
    have h := Finset.mem_Ico.1 (Fintype.mem_piFinset.1 hz i)
    simp only [vadd_eq_add, Pi.add_apply]
    omega
  · intro h
    refine ⟨y - a, Fintype.mem_piFinset.2 fun i ↦ Finset.mem_Ico.2 ?_, ?_⟩
    · have := h i
      simp only [Pi.sub_apply]
      omega
    · funext i
      simp only [vadd_eq_add, Pi.add_apply, Pi.sub_apply]
      ring

open scoped Pointwise in
/-- A translated cube `a + [0, R)^d` of `ℤ^d` has `R ^ d` points. -/
lemma _root_.Finset.card_vadd_piFinset_Ico (a : ι → ℤ) (R : ℕ) :
    (a +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (R : ℤ)).card = R ^ Fintype.card ι := by
  simp [Finset.card_vadd_finset, Fintype.card_piFinset, Int.card_Ico]

/-- **The individual ergodic theorem along cubes of bounded eccentricity.** Let `ℤ^d` act on a
finite measure space `(Ω, μ)` by measure-preserving maps and let `Λ_n = x_n + [0, r_n)^d` be cubes
whose side lengths tend to infinity and whose position is bounded by a fixed multiple of their
side, `|x_n(i)| ≤ K r_n`. Then for every integrable `f : Ω → ℝ`, `μ`-almost surely,
`|Λ_n|⁻¹ ∑_{i ∈ Λ_n} f (i +ᵥ ω) → μ[f | 𝓘] ω`.

The cubes are neither nested nor ordered by size; what is assumed is that they stay in a cone of
the origin, `Λ_n ⊆ [−K r_n, (K+1) r_n)^d`, so that the maximal function along them is dominated by
the maximal function along the increasing cubes `[−K(k+1), (K+1)(k+1))^d`
(`measure_exists_lt_abs_div_card_le_of_forall_exists_subset`). Georgii's increasing cubes
(`ae_tendsto_inv_card_smul_sum_vadd_condExp_cube`) are the case `K = 1` after the translation that
puts the origin into `Λ_0`: if `0 ∈ x_n + [0, r_n)^d` then `−r_n < x_n(i) ≤ 0`. That translation
is the normalisation `0 ∈ Λ_1` in Georgii's proof of (14.A6).

A hypothesis of this kind cannot be dropped: the weak type `(1,1)` maximal inequality for cubes
with unrestricted centres is false — already on `ℤ/M` with the translation action, disjoint
intervals `Λ_j` of side `j` give `μ(sup_j R_j 1_{{0}} > c) ≍ c^{-2}/M` against `μ(1_{{0}})/c =
c^{-1}/M` — and with it the argument of (14.A8). The *mean* ergodic theorem
`tendsto_eLpNorm_inv_card_smul_sum_vadd_sub_condExp_one` is unaffected: it holds along every
sequence of cubes with `r_n → ∞`, since cubes are Følner
(`tendsto_card_vadd_cube_symmDiff_div_card`). -/
theorem ae_tendsto_inv_card_smul_sum_vadd_condExp_cube_of_forall_abs_le {Ω : Type*}
    [AddAction (ι → ℤ) Ω] [MeasurableSpace Ω] {μ : Measure Ω} [MeasurableConstVAdd (ι → ℤ) Ω]
    [VAddInvariantMeasure (ι → ℤ) Ω μ] [IsFiniteMeasure μ] {x : ℕ → ι → ℤ} {r : ℕ → ℕ}
    (hr : ∀ n, 0 < r n) (hr' : Tendsto r atTop atTop) {K : ℕ}
    (hK : ∀ n i, |x n i| ≤ (K : ℤ) * r n) {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦
      ((x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n)).card : ℝ)⁻¹ •
        ∑ i ∈ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n), f (i +ᵥ ω)) atTop
      (𝓝 ((μ[f | MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ)) Ω]) ω)) := by
  classical
  set Q : ℕ → Finset (ι → ℤ) :=
    fun n ↦ x n +ᵥ Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (r n) with hQ
  set Q' : ℕ → Finset (ι → ℤ) := fun k ↦ ((fun _ ↦ (-((K * (k + 1) : ℕ) : ℤ))) : ι → ℤ) +ᵥ
    Fintype.piFinset fun _ : ι ↦ Finset.Ico (0 : ℤ) (((2 * K + 1) * (k + 1) : ℕ) : ℤ) with hQ'
  have hmemQ : ∀ n y, y ∈ Q n ↔ ∀ i, x n i ≤ y i ∧ y i < x n i + r n := fun n y ↦
    Fintype.mem_vadd_piFinset_Ico
  have hmemQ' : ∀ k y, y ∈ Q' k ↔ ∀ i, -((K * (k + 1) : ℕ) : ℤ) ≤ y i ∧
      y i < -((K * (k + 1) : ℕ) : ℤ) + (((2 * K + 1) * (k + 1) : ℕ) : ℤ) := fun k y ↦
    Fintype.mem_vadd_piFinset_Ico
  have hexp : ∀ m : ℕ, (((2 * K + 1) * m : ℕ) : ℤ) = 2 * ((K * m : ℕ) : ℤ) + m := by
    intro m; push_cast; ring
  have hQne : ∀ n, (Q n).Nonempty := fun n ↦
    ⟨x n, (hmemQ n _).2 fun i ↦ ⟨le_rfl, by have := hr n; omega⟩⟩
  have hQ'mono : Monotone Q' := by
    intro a b hab y hy
    have hKab : ((K * (a + 1) : ℕ) : ℤ) ≤ ((K * (b + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_left K (by omega)
    refine (hmemQ' b y).2 fun i ↦ ?_
    have h := (hmemQ' a y).1 hy i
    have h1 := hexp (a + 1)
    have h2 := hexp (b + 1)
    omega
  have hQ'card : ∀ k, (Q' k).card = ((2 * K + 1) * (k + 1)) ^ Fintype.card ι := fun k ↦
    Finset.card_vadd_piFinset_Ico _ _
  have hQcard : ∀ n, (Q n).card = r n ^ Fintype.card ι := fun n ↦
    Finset.card_vadd_piFinset_Ico _ _
  set D : ℝ≥0∞ := ((2 * K + 1 : ℕ) : ℝ≥0∞) ^ Fintype.card ι with hD
  have hdom : ∀ n, ∃ k, Q n ⊆ Q' k ∧ ((Q' k).card : ℝ≥0∞) ≤ D * (Q n).card := by
    intro n
    refine ⟨r n - 1, fun y hy ↦ ?_, ?_⟩
    · have hrn : r n - 1 + 1 = r n := Nat.succ_pred_eq_of_pos (hr n)
      refine (hmemQ' _ y).2 fun i ↦ ?_
      have h := (hmemQ n y).1 hy i
      have hx := abs_le.1 (hK n i)
      have h2 := hexp (r n - 1 + 1)
      rw [hrn] at h2 ⊢
      omega
    · have hrn : r n - 1 + 1 = r n := Nat.succ_pred_eq_of_pos (hr n)
      rw [hQ'card, hQcard, hrn, hD, mul_pow]
      push_cast
      ring_nf
      exact le_rfl
  have hD0 : D ≠ 0 := pow_ne_zero _ (by simp)
  have hDtop : D ≠ ∞ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have hCtop : (3 : ℝ≥0∞) ^ Fintype.card ι * D ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hDtop
  refine ae_tendsto_inv_card_smul_sum_vadd_condExp_of_measure_exists_lt_abs_div_card_le
    (C := 3 ^ Fintype.card ι * D) hQne (tendsto_card_vadd_cube_symmDiff_div_card x hr')
    (fun u hu c hc ↦ measure_exists_lt_abs_div_card_le_of_forall_exists_subset
      (fun g ↦ measurePreserving_vadd g μ) hQ'mono ?_ (fun k ↦ ?_) hQne hD0 hDtop hdom hu hc)
    hCtop hf
  · exact ⟨_, (hmemQ' 0 _).2 fun i ↦ ⟨le_rfl, by have := hexp (0 + 1); omega⟩⟩
  · have := card_sub_add_cube_le ((fun _ ↦ (-((K * (k + 1) : ℕ) : ℤ))) : ι → ℤ)
      ((2 * K + 1) * (k + 1))
    exact_mod_cast this

end Cube

end MeasureTheory

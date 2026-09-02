/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence

/-!
# Dominated convergence for reversed martingales

Let `μ` be a finite measure, `ℱ` an antitone sequence of sub-σ-algebras `ℱ n ≤ m0`, and `f n`
a sequence of real functions dominated by a fixed integrable `g` and converging almost everywhere
to `F`. Then the "diagonal" sequence `n ↦ μ[f n | ℱ n]` converges almost everywhere to
`μ[F | ⨅ n, ℱ n]` (`MeasureTheory.tendsto_ae_condExp_of_antitone_of_dominated`). This is
Georgii, *Gibbs Measures and Phase Transitions*, Lemma (14.19), a refinement of Lévy's downward
theorem (`MeasureTheory.tendsto_ae_condExp_of_antitone`) in which the integrand is allowed to
vary with `n`.

The proof follows Georgii: with `G N := ⨅ n, f (n + N)`, Lévy's downward theorem gives
`μ[G N | ⨅ n, ℱ n] = lim_n μ[G N | ℱ n] ≤ liminf_n μ[f n | ℱ n]` almost everywhere, and since
`G N ↑ F`, monotone convergence for conditional expectations
(`MeasureTheory.tendsto_ae_condExp_of_monotone`) yields
`μ[F | ⨅ n, ℱ n] ≤ liminf_n μ[f n | ℱ n]`. The `limsup` bound follows by applying this to `-f`,
and the two bounds squeeze the limit.

## Main results

* `MeasureTheory.tendsto_ae_condExp_of_monotone`: **monotone convergence** for conditional
  expectations, a.e. version: if `h n ↑ H` almost everywhere with `h n` and `H` integrable, then
  `μ[h n | m]` converges almost everywhere to `μ[H | m]`.
* `MeasureTheory.condExp_iInf_le_liminf_condExp_of_antitone`: the `liminf` half of Georgii's
  Lemma (14.19).
* `MeasureTheory.limsup_condExp_le_condExp_iInf_of_antitone`: the `limsup` half.
* `MeasureTheory.tendsto_ae_condExp_of_antitone_of_dominated`: **dominated convergence for
  reversed martingales**, Georgii's Lemma (14.19).
-/

@[expose] public section

open Filter MeasureTheory

open scoped Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

section MonotoneConvergence

variable {m : MeasurableSpace Ω} {h : ℕ → Ω → ℝ} {H : Ω → ℝ}

/-- **Monotone convergence for conditional expectations**, almost everywhere version: if the
integrable functions `h n` increase almost everywhere to the integrable function `H`, then
`μ[h n | m]` converges almost everywhere to `μ[H | m]`.

The a.e. limit `L := ⨆ n, μ[h n | m]` exists by monotonicity and is bounded by `μ[H | m]`; its
integral equals `∫ H = ∫ μ[H | m]` by the monotone convergence theorem for integrals, applied to
both `h n` and `μ[h n | m]`, so `L = μ[H | m]` almost everywhere. -/
theorem tendsto_ae_condExp_of_monotone (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hint : ∀ n, Integrable (h n) μ) (hH : Integrable H μ)
    (hmono : ∀ᵐ ω ∂μ, Monotone fun n => h n ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 (H ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[h n | m]) ω) atTop (𝓝 ((μ[H | m]) ω)) := by
  have hle : ∀ n, h n ≤ᵐ[μ] H := fun n => by
    filter_upwards [hmono, hlim] with ω hω hω'
    exact hω.ge_of_tendsto hω' n
  have hcmono : ∀ᵐ ω ∂μ, Monotone fun n => (μ[h n | m]) ω := by
    have : ∀ n, μ[h n | m] ≤ᵐ[μ] μ[h (n + 1) | m] := fun n =>
      condExp_mono (hint n) (hint (n + 1)) (hmono.mono fun ω hω => hω (Nat.le_succ n))
    filter_upwards [ae_all_iff.2 this] with ω hω
    exact monotone_nat_of_le_succ hω
  have hcle : ∀ᵐ ω ∂μ, ∀ n, (μ[h n | m]) ω ≤ (μ[H | m]) ω :=
    ae_all_iff.2 fun n => condExp_mono (hint n) hH (hle n)
  set L : Ω → ℝ := fun ω => ⨆ n, (μ[h n | m]) ω with hL
  have hLmeas : Measurable[m0] L :=
    Measurable.iSup fun n => (stronglyMeasurable_condExp.mono hm).measurable
  have hbdd : ∀ᵐ ω ∂μ, BddAbove (Set.range fun n => (μ[h n | m]) ω) := by
    filter_upwards [hcle] with ω hω
    exact ⟨_, Set.forall_mem_range.2 hω⟩
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[h n | m]) ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hcmono, hbdd] with ω hω hω'
    exact tendsto_atTop_ciSup hω hω'
  have hLle : L ≤ᵐ[μ] μ[H | m] := by
    filter_upwards [hcle] with ω hω
    exact ciSup_le hω
  have hLge : μ[h 0 | m] ≤ᵐ[μ] L := by
    filter_upwards [hbdd] with ω hω
    exact le_ciSup hω 0
  have hLint : Integrable L μ := by
    have h0 : Integrable (μ[h 0 | m]) μ := integrable_condExp
    have hH' : Integrable (μ[H | m]) μ := integrable_condExp
    refine Integrable.mono' (h0.abs.add hH'.abs) hLmeas.aestronglyMeasurable ?_
    filter_upwards [hLle, hLge] with ω h1 h2
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le ((μ[h 0 | m]) ω), abs_nonneg ((μ[H | m]) ω)]
    · linarith [le_abs_self ((μ[H | m]) ω), abs_nonneg ((μ[h 0 | m]) ω)]
  have hint1 : Tendsto (fun n => ∫ ω, (μ[h n | m]) ω ∂μ) atTop (𝓝 (∫ ω, L ω ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone (fun _ => integrable_condExp) hLint hcmono htend
  have hint2 : Tendsto (fun n => ∫ ω, (μ[h n | m]) ω ∂μ) atTop
      (𝓝 (∫ ω, (μ[H | m]) ω ∂μ)) := by
    simp_rw [integral_condExp hm]
    exact integral_tendsto_of_tendsto_of_monotone hint hH hmono hlim
  have hLeq : L =ᵐ[μ] μ[H | m] :=
    (integral_eq_iff_of_ae_le hLint integrable_condExp hLle).1 (tendsto_nhds_unique hint1 hint2)
  filter_upwards [htend, hLeq] with ω hω heq
  rwa [heq] at hω

end MonotoneConvergence

section DominatedBackward

variable [IsFiniteMeasure μ] {ℱ : ℕ → MeasurableSpace Ω} {f : ℕ → Ω → ℝ} {g F : Ω → ℝ}

/-- If `‖f n‖ ≤ g` almost everywhere with `g` integrable, then almost everywhere the diagonal
sequence `n ↦ μ[f n | ℱ n]` is bounded above and below: it is sandwiched between
`-μ[g | ℱ n]` and `μ[g | ℱ n]`, which converge by Lévy's downward theorem. -/
theorem ae_isBoundedUnder_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω) :
    ∀ᵐ ω ∂μ, IsBoundedUnder (· ≤ ·) atTop (fun n => (μ[f n | ℱ n]) ω) ∧
      IsBoundedUnder (· ≥ ·) atTop (fun n => (μ[f n | ℱ n]) ω) := by
  have hbound' : ∀ᵐ ω ∂μ, ∀ n, |f n ω| ≤ g ω := by
    simpa only [Real.norm_eq_abs] using ae_all_iff.2 hbound
  have hfint : ∀ n, Integrable (f n) μ := fun n => hg.mono' (hf n) (hbound n)
  have hupp : ∀ᵐ ω ∂μ, ∀ n, (μ[f n | ℱ n]) ω ≤ (μ[g | ℱ n]) ω :=
    ae_all_iff.2 fun n =>
      condExp_mono (hfint n) hg (hbound'.mono fun ω hω => (abs_le.1 (hω n)).2)
  have hlow : ∀ᵐ ω ∂μ, ∀ n, -(μ[g | ℱ n]) ω ≤ (μ[f n | ℱ n]) ω := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [condExp_mono hg.neg (hfint n)
      (hbound'.mono fun ω hω => (abs_le.1 (hω n)).1), condExp_neg g (ℱ n)] with ω h1 h2
    rw [Pi.neg_apply] at h2
    exact h2.symm.trans_le h1
  filter_upwards [hupp, hlow, tendsto_ae_condExp_of_antitone g hℱ hle] with ω h1 h2 h3
  exact ⟨h3.isBoundedUnder_le.mono_le (Eventually.of_forall h1),
    h3.neg.isBoundedUnder_ge.mono_ge (Eventually.of_forall h2)⟩

/-- The `liminf` half of Georgii's Lemma (14.19): if `‖f n‖ ≤ g` with `g` integrable and
`f n → F` almost everywhere, then `μ[F | ⨅ n, ℱ n] ≤ liminf_n μ[f n | ℱ n]` almost everywhere.

With `G N := ⨅ n, f (n + N)`, Lévy's downward theorem and `G N ≤ f n` for `n ≥ N` give
`μ[G N | ⨅ n, ℱ n] = lim_n μ[G N | ℱ n] ≤ liminf_n μ[f n | ℱ n]`; since `G N ↑ F`, monotone
convergence for conditional expectations passes to the limit in `N`. -/
theorem condExp_iInf_le_liminf_condExp_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω))) :
    ∀ᵐ ω ∂μ, (μ[F | ⨅ n, ℱ n]) ω ≤ liminf (fun n => (μ[f n | ℱ n]) ω) atTop := by
  have hm : ⨅ n, ℱ n ≤ m0 := (iInf_le _ 0).trans (hle 0)
  have hbound' : ∀ᵐ ω ∂μ, ∀ n, |f n ω| ≤ g ω := by
    simpa only [Real.norm_eq_abs] using ae_all_iff.2 hbound
  have hfint : ∀ n, Integrable (f n) μ := fun n => hg.mono' (hf n) (hbound n)
  have hFint : Integrable F μ := by
    refine hg.mono' (aestronglyMeasurable_of_tendsto_ae atTop hf hlim) ?_
    filter_upwards [ae_all_iff.2 hbound, hlim] with ω hω hω'
    exact le_of_tendsto' hω'.norm hω
  -- the running infima `G N = ⨅ n, f (n + N)`
  set G : ℕ → Ω → ℝ := fun N ω => ⨅ n, f (n + N) ω with hG
  have hGbdd : ∀ᵐ ω ∂μ, ∀ N, BddBelow (Set.range fun n => f (n + N) ω) := by
    filter_upwards [hbound'] with ω hω N
    exact ⟨-g ω, Set.forall_mem_range.2 fun n => (abs_le.1 (hω (n + N))).1⟩
  have hGmeas : ∀ N, AEStronglyMeasurable (G N) μ := fun N =>
    (AEMeasurable.iInf fun n => (hf (n + N)).aemeasurable).aestronglyMeasurable
  have hGle : ∀ᵐ ω ∂μ, ∀ N n, G N ω ≤ f (n + N) ω := by
    filter_upwards [hGbdd] with ω hω N n
    exact ciInf_le (hω N) n
  have hGge : ∀ᵐ ω ∂μ, ∀ N, -g ω ≤ G N ω := by
    filter_upwards [hbound'] with ω hω N
    exact le_ciInf fun n => (abs_le.1 (hω (n + N))).1
  have hGint : ∀ N, Integrable (G N) μ := fun N => by
    refine hg.mono' (hGmeas N) ?_
    filter_upwards [hGle, hGge, hbound'] with ω h1 h2 h3
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨h2 N, (h1 N 0).trans (abs_le.1 (h3 (0 + N))).2⟩
  have hGmono : ∀ᵐ ω ∂μ, Monotone fun N => G N ω := by
    filter_upwards [hGbdd] with ω hω
    refine monotone_nat_of_le_succ fun N => le_ciInf fun n => ?_
    have hk : n + (N + 1) = n + 1 + N := by omega
    rw [hk]
    exact ciInf_le (hω N) (n + 1)
  have hGlim : ∀ᵐ ω ∂μ, Tendsto (fun N => G N ω) atTop (𝓝 (F ω)) := by
    filter_upwards [hlim, hGle] with ω hω hGle'
    refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · obtain ⟨a', haa', ha'⟩ := exists_between ha
      obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1 hω).1 a' ha')
      filter_upwards [eventually_ge_atTop N₀] with N hN
      exact haa'.trans_le (le_ciInf fun n => (hN₀ _ (hN.trans (Nat.le_add_left N n))).le)
    · obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1 hω).2 b hb)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have := hGle' N 0
      rw [Nat.zero_add] at this
      exact this.trans_lt (hN₀ N hN)
  -- comparison of the conditional expectations along the diagonal
  have hcond : ∀ᵐ ω ∂μ, ∀ N k, (μ[G N | ℱ (k + N)]) ω ≤ (μ[f (k + N) | ℱ (k + N)]) ω :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun k =>
      condExp_mono (hGint N) (hfint (k + N)) (hGle.mono fun ω hω => hω N k)
  -- Lévy's downward theorem for each `G N`
  have hback : ∀ᵐ ω ∂μ, ∀ N,
      Tendsto (fun n => (μ[G N | ℱ n]) ω) atTop (𝓝 ((μ[G N | ⨅ n, ℱ n]) ω)) :=
    ae_all_iff.2 fun N => tendsto_ae_condExp_of_antitone (G N) hℱ hle
  -- monotone convergence `μ[G N | ⨅ n, ℱ n] → μ[F | ⨅ n, ℱ n]`
  have hmc : ∀ᵐ ω ∂μ,
      Tendsto (fun N => (μ[G N | ⨅ n, ℱ n]) ω) atTop (𝓝 ((μ[F | ⨅ n, ℱ n]) ω)) :=
    tendsto_ae_condExp_of_monotone hm hGint hFint hGmono hGlim
  filter_upwards [hcond, hback, hmc,
    ae_isBoundedUnder_condExp_of_antitone hℱ hle hf hg hbound] with ω hcond hback hmc hbdd
  refine le_of_tendsto' hmc fun N => ?_
  rw [← (hback N).liminf_eq]
  refine liminf_le_liminf ?_ (hback N).isBoundedUnder_ge hbdd.1.isCoboundedUnder_ge
  filter_upwards [eventually_ge_atTop N] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact hcond N k

/-- The `limsup` half of Georgii's Lemma (14.19): if `‖f n‖ ≤ g` with `g` integrable and
`f n → F` almost everywhere, then `limsup_n μ[f n | ℱ n] ≤ μ[F | ⨅ n, ℱ n]` almost everywhere.
This is `condExp_iInf_le_liminf_condExp_of_antitone` applied to `-f`. -/
theorem limsup_condExp_le_condExp_iInf_of_antitone (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω))) :
    ∀ᵐ ω ∂μ, limsup (fun n => (μ[f n | ℱ n]) ω) atTop ≤ (μ[F | ⨅ n, ℱ n]) ω := by
  have hneg := condExp_iInf_le_liminf_condExp_of_antitone (f := fun n => -f n) (F := -F)
    hℱ hle (fun n => (hf n).neg) hg (fun n => by simpa only [Pi.neg_apply, norm_neg] using hbound n)
    (hlim.mono fun ω hω => hω.neg)
  have hnegf : ∀ᵐ ω ∂μ, ∀ n, (μ[-f n | ℱ n]) ω = -(μ[f n | ℱ n]) ω :=
    ae_all_iff.2 fun n => (condExp_neg (f n) (ℱ n)).mono fun ω hω => by
      rw [hω, Pi.neg_apply]
  filter_upwards [hneg, hnegf, condExp_neg F (⨅ n, ℱ n),
    ae_isBoundedUnder_condExp_of_antitone hℱ hle hf hg hbound] with ω hneg hnegf hnegF hbdd
  rw [hnegF, Pi.neg_apply, liminf_congr (Eventually.of_forall hnegf)] at hneg
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => limsup_le_of_le hbdd.2.isCoboundedUnder_le ?_
  have hbdd' : IsBoundedUnder (· ≥ ·) atTop fun n => -(μ[f n | ℱ n]) ω := by
    obtain ⟨c, hc⟩ := hbdd.1
    exact ⟨-c, eventually_map.2 ((eventually_map.1 hc).mono fun n hn => neg_le_neg hn)⟩
  filter_upwards [eventually_lt_of_lt_liminf ((neg_lt_neg hb).trans_le hneg) hbdd'] with n hn
  exact (neg_lt_neg_iff.1 hn).le

/-- **Dominated convergence for reversed martingales** (Georgii, Lemma (14.19)). Let `μ` be a
finite measure, `ℱ` an antitone sequence of sub-σ-algebras `ℱ n ≤ m0`, and `f n` a sequence of
real functions with `‖f n‖ ≤ g` almost everywhere for an integrable `g`, converging almost
everywhere to `F`. Then `μ[f n | ℱ n]` converges almost everywhere to `μ[F | ⨅ n, ℱ n]`.

For constant `f n = F` this is Lévy's downward theorem
`MeasureTheory.tendsto_ae_condExp_of_antitone`. -/
theorem tendsto_ae_condExp_of_antitone_of_dominated (hℱ : Antitone ℱ) (hle : ∀ n, ℱ n ≤ m0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ g ω)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (F ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (μ[f n | ℱ n]) ω) atTop (𝓝 ((μ[F | ⨅ n, ℱ n]) ω)) := by
  filter_upwards [condExp_iInf_le_liminf_condExp_of_antitone hℱ hle hf hg hbound hlim,
    limsup_condExp_le_condExp_iInf_of_antitone hℱ hle hf hg hbound hlim,
    ae_isBoundedUnder_condExp_of_antitone hℱ hle hf hg hbound] with ω hinf hsup hbdd
  exact tendsto_of_le_liminf_of_limsup_le hinf hsup hbdd.1 hbdd.2

end DominatedBackward

end MeasureTheory

end

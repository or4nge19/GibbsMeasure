/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Complete convergence implies almost sure convergence

A sequence of functions `F n : Ω → E` into a pseudometric space *converges completely* to `L` if
`∑' n, μ {ω | ε ≤ dist (F n ω) L} < ∞` for every `ε > 0` (Hsu–Robbins). The first Borel–Cantelli
lemma turns this into almost sure convergence.

## Main declarations

* `MeasureTheory.tendsto_ae_of_forall_tsum_measure_ne_top`: complete convergence implies almost
  sure convergence.
* `MeasureTheory.tendsto_ae_of_forall_tsum_measure_ne_top'`: the same with the deviation events
  replaced by any larger family of sets, for use when the natural bound is on supersets of the
  deviation events.

No measurability is needed, and the statements are at the generality of the Borel–Cantelli lemma
`MeasureTheory.ae_eventually_notMem` itself: `μ` is an arbitrary outer measure.
-/

@[expose] public section

open Filter

open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω E F : Type*} [FunLike F (Set Ω) ℝ≥0∞] [OuterMeasureClass F Ω] {μ : F}
  [PseudoMetricSpace E]

/-- **Complete convergence implies almost sure convergence.** If for every `ε > 0` the
deviation masses `μ {ω | ε ≤ dist (F n ω) L}` are summable, then `F n → L` almost everywhere.

For each `m` the first Borel–Cantelli lemma (`MeasureTheory.ae_eventually_notMem`) gives a null
set outside which `dist (F n ω) L < 1/(m+1)` for all large `n`; the countably many exceptional
sets are discarded at once by `ae_all_iff`. -/
theorem tendsto_ae_of_forall_tsum_measure_ne_top {f : ℕ → Ω → E} {L : E}
    (h : ∀ ε : ℝ, 0 < ε → (∑' n : ℕ, μ {ω | ε ≤ dist (f n ω) L}) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ f n ω) atTop (𝓝 L) := by
  have hae : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, dist (f n ω) L < 1 / (m + 1) := by
    intro m
    have hε : (0 : ℝ) < 1 / (m + 1) := by positivity
    filter_upwards [ae_eventually_notMem (h _ hε)] with ω hω
    filter_upwards [hω] with n hn
    simpa only [Set.mem_ofPred_eq, not_le] using hn
  filter_upwards [ae_all_iff.2 hae] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω m)
  exact ⟨N, fun n hn ↦ (hN n hn).trans hm⟩

/-- `tendsto_ae_of_forall_tsum_measure_ne_top` with the deviation events replaced by a larger
family `s ε n`: the version that applies when the natural summable bound is available only for
supersets of `{ω | ε ≤ dist (f n ω) L}`, for instance for preimages of coordinate events. -/
theorem tendsto_ae_of_forall_tsum_measure_ne_top' {f : ℕ → Ω → E} {L : E}
    {s : ℝ → ℕ → Set Ω} (hs : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, {ω | ε ≤ dist (f n ω) L} ⊆ s ε n)
    (h : ∀ ε : ℝ, 0 < ε → (∑' n : ℕ, μ (s ε n)) ≠ ⊤) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ f n ω) atTop (𝓝 L) :=
  tendsto_ae_of_forall_tsum_measure_ne_top fun ε hε ↦
    ne_top_of_le_ne_top (h ε hε) (ENNReal.tsum_le_tsum fun n ↦ measure_mono (hs ε hε n))

end MeasureTheory

end

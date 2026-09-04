/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Extremal fixed points of a monotone continuous self-map of `ℝ`

If `ψ : ℝ → ℝ` is monotone and continuous, `ψ M ≤ M` and `ψ` is bounded below, then the orbit
`ψ^[n] M` decreases to a fixed point of `ψ` which dominates every fixed point below `M`; dually
for `m ≤ ψ m` and `ψ` bounded above. This is the elementary "iterate from above/below" argument
used, for instance, to bound the solutions of a recursion `t = ψ(t)` by its extremal fixed points.

## Main results

* `Monotone.exists_fixedPt_tendsto_iterate_of_le`: the orbit from above; the limit is a fixed
  point of `ψ` dominating every fixed point `≤ M`.
* `Monotone.exists_fixedPt_tendsto_iterate_of_ge`: the orbit from below, dually.
-/

@[expose] public section

open Filter Set Topology

namespace Monotone

variable {ψ : ℝ → ℝ}

/-- The orbit `ψ^[n] M` is antitone as soon as `ψ M ≤ M`. -/
lemma antitone_iterate_of_le (hmono : Monotone ψ) {M : ℝ} (hM : ψ M ≤ M) :
    Antitone fun n : ℕ ↦ ψ^[n] M := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [Function.iterate_succ_apply]
  exact hmono.iterate n hM

/-- **Iterating from above.** If `ψ` is monotone and continuous, `ψ M ≤ M` and `ψ` is bounded
below, then `ψ^[n] M` decreases to a fixed point `p` of `ψ`, and every fixed point `q ≤ M`
satisfies `q ≤ p`. -/
theorem exists_fixedPt_tendsto_iterate_of_le (hmono : Monotone ψ) (hcont : Continuous ψ) {M m : ℝ}
    (hM : ψ M ≤ M) (hm : ∀ x, m ≤ ψ x) :
    ∃ p : ℝ, ψ p = p ∧ Tendsto (fun n : ℕ ↦ ψ^[n] M) atTop (𝓝 p) ∧
      ∀ q, ψ q = q → q ≤ M → q ≤ p := by
  set u : ℕ → ℝ := fun n ↦ ψ^[n] M with hu
  have hanti : Antitone u := hmono.antitone_iterate_of_le hM
  have hlb : ∀ n, min m M ≤ u n := by
    intro n
    cases n with
    | zero => exact (min_le_right m M)
    | succ k =>
      rw [hu]
      simp only [Function.iterate_succ_apply']
      exact (min_le_left m M).trans (hm _)
  have hbdd : BddBelow (Set.range u) := ⟨min m M, by rintro _ ⟨n, rfl⟩; exact hlb n⟩
  have htend : Tendsto u atTop (𝓝 (⨅ n, u n)) := tendsto_atTop_ciInf hanti hbdd
  set p := ⨅ n, u n with hp
  have hfix : ψ p = p := by
    have h1 : Tendsto (fun n ↦ u (n + 1)) atTop (𝓝 p) := htend.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n ↦ ψ (u n)) atTop (𝓝 (ψ p)) := (hcont.tendsto p).comp htend
    have h3 : (fun n ↦ ψ (u n)) = fun n ↦ u (n + 1) := by
      funext n
      rw [hu]
      simp [Function.iterate_succ_apply']
    rw [h3] at h2
    exact tendsto_nhds_unique h2 h1
  refine ⟨p, hfix, htend, fun q hq hqM ↦ ?_⟩
  refine _root_.ge_of_tendsto htend (Filter.Eventually.of_forall fun n ↦ ?_)
  calc q = ψ^[n] q := (Function.IsFixedPt.iterate hq n).symm
    _ ≤ ψ^[n] M := hmono.iterate n hqM

/-- **Iterating from below.** The dual of `exists_fixedPt_tendsto_iterate_of_le`. -/
theorem exists_fixedPt_tendsto_iterate_of_ge (hmono : Monotone ψ) (hcont : Continuous ψ) {m M : ℝ}
    (hm : m ≤ ψ m) (hM : ∀ x, ψ x ≤ M) :
    ∃ p : ℝ, ψ p = p ∧ Tendsto (fun n : ℕ ↦ ψ^[n] m) atTop (𝓝 p) ∧
      ∀ q, ψ q = q → m ≤ q → p ≤ q := by
  set u : ℕ → ℝ := fun n ↦ ψ^[n] m with hu
  have hmonoU : Monotone u := by
    refine monotone_nat_of_le_succ fun n ↦ ?_
    rw [hu]
    simp only
    rw [Function.iterate_succ_apply]
    exact hmono.iterate n hm
  have hub : ∀ n, u n ≤ max M m := by
    intro n
    cases n with
    | zero => exact le_max_right M m
    | succ k =>
      rw [hu]
      simp only [Function.iterate_succ_apply']
      exact (hM _).trans (le_max_left M m)
  have hbdd : BddAbove (Set.range u) := ⟨max M m, by rintro _ ⟨n, rfl⟩; exact hub n⟩
  have htend : Tendsto u atTop (𝓝 (⨆ n, u n)) := tendsto_atTop_ciSup hmonoU hbdd
  set p := ⨆ n, u n with hp
  have hfix : ψ p = p := by
    have h1 : Tendsto (fun n ↦ u (n + 1)) atTop (𝓝 p) := htend.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n ↦ ψ (u n)) atTop (𝓝 (ψ p)) := (hcont.tendsto p).comp htend
    have h3 : (fun n ↦ ψ (u n)) = fun n ↦ u (n + 1) := by
      funext n
      rw [hu]
      simp [Function.iterate_succ_apply']
    rw [h3] at h2
    exact tendsto_nhds_unique h2 h1
  refine ⟨p, hfix, htend, fun q hq hmq ↦ ?_⟩
  refine _root_.le_of_tendsto htend (Filter.Eventually.of_forall fun n ↦ ?_)
  calc ψ^[n] m ≤ ψ^[n] q := hmono.iterate n hmq
    _ = q := Function.IsFixedPt.iterate hq n

end Monotone

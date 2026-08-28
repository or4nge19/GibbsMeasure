/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.Algebra.Algebra

/-!
# Bounded measurable functions

The bounded real functions on `α` form the commutative Banach algebra `lp (fun _ : α ↦ ℝ) ∞`. Inside
it, the ones measurable for a σ-algebra `m` form a closed subalgebra `MeasureTheory.boundedMeasurable m`.

## Main declarations

* `MeasureTheory.boundedMeasurable`: the subalgebra of bounded `m`-measurable functions.
* `MeasureTheory.isClosed_boundedMeasurable`: it is closed, i.e. a uniform limit of measurable
  functions is measurable.
-/

@[expose] public section

open scoped ENNReal Topology
open Filter

noncomputable section

namespace MeasureTheory

variable {α : Type*}

/-- The bounded real-valued `m`-measurable functions on `α`, as a subalgebra of the commutative
Banach algebra `lp (fun _ : α ↦ ℝ) ∞` of all bounded real functions on `α`.

This is the ambient algebra for Georgii's local and quasilocal observables (Georgii, *Gibbs Measures
and Phase Transitions*, Definition (2.20)). -/
def boundedMeasurable (m : MeasurableSpace α) : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞) where
  carrier := {f | Measurable[m] (⇑f : α → ℝ)}
  mul_mem' {f g} hf hg := by
    show Measurable[m] (⇑(f * g) : α → ℝ)
    rw [lp.infty_coeFn_mul]
    exact Measurable.mul (m := m) hf hg
  one_mem' := by
    show Measurable[m] (⇑(1 : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ)
    rw [lp.infty_coeFn_one]
    exact measurable_one
  add_mem' {f g} hf hg := by
    show Measurable[m] (⇑(f + g) : α → ℝ)
    rw [lp.coeFn_add]
    exact Measurable.add (m := m) hf hg
  zero_mem' := by
    show Measurable[m] (⇑(0 : lp (fun _ : α ↦ ℝ) ∞) : α → ℝ)
    rw [lp.coeFn_zero]
    exact measurable_zero
  algebraMap_mem' r := by
    show Measurable[m] (⇑(algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r) : α → ℝ)
    have h : ⇑(algebraMap ℝ (lp (fun _ : α ↦ ℝ) ∞) r) = fun _ : α ↦ r := by
      rw [Algebra.algebraMap_eq_smul_one]
      funext x
      simp [lp.coeFn_smul, lp.infty_coeFn_one]
    rw [h]
    exact measurable_const

lemma mem_boundedMeasurable {m : MeasurableSpace α} {f : lp (fun _ : α ↦ ℝ) ∞} :
    f ∈ boundedMeasurable m ↔ Measurable[m] (⇑f : α → ℝ) := Iff.rfl

/-- `boundedMeasurable` is monotone in the σ-algebra. -/
lemma boundedMeasurable_mono {m₁ m₂ : MeasurableSpace α} (h : m₁ ≤ m₂) :
    boundedMeasurable m₁ ≤ boundedMeasurable m₂ :=
  fun _ hf ↦ hf.mono h le_rfl

/-- Convergence in `ℓ^∞` implies pointwise convergence. -/
lemma lp.tendsto_apply_of_tendsto {ι : Type*} {l : Filter ι}
    {f : ι → lp (fun _ : α ↦ ℝ) ∞} {g : lp (fun _ : α ↦ ℝ) ∞} (h : Tendsto f l (𝓝 g)) (x : α) :
    Tendsto (fun n ↦ (f n : α → ℝ) x) l (𝓝 ((g : α → ℝ) x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) h
  simpa [_root_.lp.coeFn_sub] using
    _root_.lp.norm_apply_le_norm ENNReal.top_ne_zero (f n - g) x

/-- **Uniform limits of measurable functions are measurable**: the bounded `m`-measurable functions
form a *closed* subalgebra of the bounded functions. -/
lemma isClosed_boundedMeasurable (m : MeasurableSpace α) :
    IsClosed (boundedMeasurable m : Set (lp (fun _ : α ↦ ℝ) ∞)) := by
  refine IsSeqClosed.isClosed fun f g hf hfg ↦ ?_
  rw [SetLike.mem_coe, mem_boundedMeasurable]
  refine measurable_of_tendsto_metrizable (f := fun n ↦ ((f n : α → ℝ))) hf ?_
  rw [tendsto_pi_nhds]
  exact fun x ↦ lp.tendsto_apply_of_tendsto hfg x

/-- A closed subalgebra contains the closure of any subalgebra it contains. In particular the
quasilocal functions consist of measurable functions. -/
lemma topologicalClosure_le_boundedMeasurable {m : MeasurableSpace α}
    {A : Subalgebra ℝ (lp (fun _ : α ↦ ℝ) ∞)} (hA : A ≤ boundedMeasurable m) :
    A.topologicalClosure ≤ boundedMeasurable m :=
  Subalgebra.topologicalClosure_minimal hA (isClosed_boundedMeasurable m)

end MeasureTheory

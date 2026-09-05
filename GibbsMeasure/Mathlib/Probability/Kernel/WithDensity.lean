/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# `n`-step densities of a kernel

A transition kernel `P` on `E` with a density `p` with respect to a fixed measure `ν`
(`P x = p(x, ·) ν`) has `n`-step densities obtained by the convolution recursion
`p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)` (`Kernel.densityPow`,
`Kernel.pow_apply_eq_withDensity_densityPow`), and any mixture `α P` has the density
`y ↦ ∫ p(u, y) α(du)` (`Measure.bind_eq_withDensity_lintegral`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MeasureTheory

/-- The `ν`-density of a mixture `α P` of a kernel `P` whose values have `ν`-densities `p x`. -/
theorem Measure.bind_eq_withDensity_lintegral {E F : Type*} [MeasurableSpace E]
    [MeasurableSpace F] {ν : Measure F} [SFinite ν] {p : E → F → ℝ≥0∞}
    (hp : Measurable (Function.uncurry p)) {P : Kernel E F}
    (hP : ∀ x, P x = ν.withDensity (p x)) (α : Measure E) [SFinite α] :
    α.bind P = ν.withDensity fun y ↦ ∫⁻ u, p u y ∂α := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs]
  have h1 : ∀ u, P u s = ∫⁻ y in s, p u y ∂ν := fun u ↦ by rw [hP u, withDensity_apply _ hs]
  simp_rw [h1]
  exact lintegral_lintegral_swap hp.aemeasurable

end MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {p : E → E → ℝ≥0∞}

/-- The `n`-step transition density of a kernel `P` with `P x = p(x, ·) ν`, defined by the
convolution recursion `p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)` — Georgii **(10.29)**.
The value at `n = 0` is junk (`P ^ 0` is the identity kernel, which has no `ν`-density);
every statement about `Kernel.densityPow` carries the hypothesis `1 ≤ n`. -/
noncomputable def Kernel.densityPow (ν : Measure E) (p : E → E → ℝ≥0∞) :
    ℕ → E → E → ℝ≥0∞
  | 0 => fun _ _ ↦ 0
  | 1 => p
  | (n + 2) => fun x y ↦ ∫⁻ u, Kernel.densityPow ν p (n + 1) x u * p u y ∂ν

@[simp] lemma Kernel.densityPow_one : Kernel.densityPow ν p 1 = p := rfl

/-- The convolution recursion `p^{n+1}(x, y) = ∫ p^n(x, u) p(u, y) ν(du)`, `n ≥ 1`. -/
lemma Kernel.densityPow_succ {n : ℕ} (hn : 1 ≤ n) (x y : E) :
    Kernel.densityPow ν p (n + 1) x y = ∫⁻ u, Kernel.densityPow ν p n x u * p u y ∂ν := by
  cases n with
  | zero => exact absurd hn (by norm_num)
  | succ m => rfl

lemma Kernel.measurable_uncurry_densityPow [SFinite ν] (hp : Measurable (Function.uncurry p))
    (n : ℕ) : Measurable (Function.uncurry (Kernel.densityPow ν p n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      cases n with
      | zero => exact hp
      | succ m =>
          change Measurable fun q : E × E ↦
            ∫⁻ u, Kernel.densityPow ν p (m + 1) q.1 u * p u q.2 ∂ν
          refine Measurable.lintegral_prod_right' (f := fun q : (E × E) × E ↦
            Kernel.densityPow ν p (m + 1) q.1.1 q.2 * p q.2 q.1.2) ?_
          exact (ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
            (hp.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

/-- `P ^ n` has the `ν`-density `p^n` of `Kernel.densityPow`, for every `n ≥ 1`. -/
theorem Kernel.pow_apply_eq_withDensity_densityPow [SFinite ν]
    (hp : Measurable (Function.uncurry p)) {P : Kernel E E}
    (hP : ∀ x, P x = ν.withDensity (p x)) :
    ∀ {n : ℕ}, 1 ≤ n → ∀ x, (P ^ n) x = ν.withDensity (Kernel.densityPow ν p n x) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simpa using hP
  | succ n hn ih =>
      intro x
      ext s hs
      have hdn : Measurable (Kernel.densityPow ν p n x) :=
        (Kernel.measurable_uncurry_densityPow hp n).comp (measurable_const.prodMk measurable_id)
      have hPs : Measurable fun b ↦ P b s := Kernel.measurable_coe P hs
      have hpb : ∀ b : E, Measurable (p b) := fun b ↦
        hp.comp (measurable_const.prodMk measurable_id)
      have hL : ∀ b : E, Kernel.densityPow ν p n x b * P b s
          = ∫⁻ y in s, Kernel.densityPow ν p n x b * p b y ∂ν := fun b ↦ by
        rw [hP b, withDensity_apply _ hs, lintegral_const_mul _ (hpb b)]
      rw [Kernel.pow_succ_apply_eq_lintegral P n x hs, ih x,
        lintegral_withDensity_eq_lintegral_mul _ hdn hPs, withDensity_apply _ hs]
      simp only [Pi.mul_apply]
      rw [lintegral_congr hL, lintegral_lintegral_swap]
      · exact lintegral_congr fun y ↦ (Kernel.densityPow_succ hn x y).symm
      · exact (((Kernel.measurable_uncurry_densityPow hp n).comp
          (measurable_const.prodMk measurable_fst)).mul
          (hp.comp (measurable_fst.prodMk measurable_snd))).aemeasurable

end ProbabilityTheory

end

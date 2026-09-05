/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Translating and scaling the essential infimum of a real function

Mathlib records how `essInf` transforms under an order isomorphism (`OrderIso.essInf_apply`)
but has no instance of it for the affine maps of `ℝ`, and the boundedness side conditions of
`OrderIso.essInf_apply` are not discharged automatically over `ℝ`.  Both gaps are filled here,
under the hypothesis that the function is bounded below almost everywhere — which is genuinely
needed, since `essInf` of an essentially unbounded-below real function is the junk value
`sSup ∅ = 0`.
-/

@[expose] public section

namespace MeasureTheory

open Filter

variable {α : Type*} {_ : MeasurableSpace α} {μ : Measure α} {f : α → ℝ} {M : ℝ}

/-- A function bounded below almost everywhere is bounded below along the a.e. filter. -/
lemma isBoundedUnder_ge_ae (hM : ∀ᵐ x ∂μ, M ≤ f x) : IsBoundedUnder (· ≥ ·) (ae μ) f := ⟨M, hM⟩

/-- **The essential lower bounds of a real function are bounded above**, for any nonzero measure:
if arbitrarily large reals were essential lower bounds of `f`, countable intersection of the
corresponding almost-sure sets would produce a point at which `f` exceeds every natural number.
In `Filter` language this is `IsCoboundedUnder (· ≥ ·) (ae μ) f`, one of the side conditions of
`OrderIso.essInf_apply`, and it is exactly what makes `essInf f μ = sSup {a | ∀ᵐ x, a ≤ f x}`
a genuine supremum rather than the junk value `sSup ∅`. -/
lemma isCoboundedUnder_ge_ae [NeZero μ] (f : α → ℝ) : IsCoboundedUnder (· ≥ ·) (ae μ) f := by
  have : (ae μ).NeBot := ae_neBot.2 (NeZero.ne μ)
  by_contra hcon
  -- if no bound works, arbitrarily large reals are essential lower bounds of `f`
  have key : ∀ b : ℝ, ∃ a : ℝ, (∀ᵐ x ∂μ, a ≤ f x) ∧ b < a := by
    intro b
    by_contra hb
    refine hcon ⟨b, fun a ha ↦ ?_⟩
    rw [eventually_map] at ha
    by_contra hab
    exact hb ⟨a, ha, not_le.1 hab⟩
  choose a ha ha' using key
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, (n : ℝ) ≤ f x := by
    rw [ae_all_iff]
    intro n
    filter_upwards [ha (n : ℝ)] with x hx using (ha' (n : ℝ)).le.trans hx
  obtain ⟨x, hx⟩ := hall.exists
  obtain ⟨n, hn⟩ := exists_nat_gt (f x)
  exact absurd (hx n) (not_le.2 hn)

/-- **Translation commutes with the essential infimum** of a real function bounded below almost
everywhere. -/
lemma essInf_add_const [NeZero μ] (hM : ∀ᵐ x ∂μ, M ≤ f x) (c : ℝ) :
    essInf (fun x ↦ f x + c) μ = essInf f μ + c := by
  have hM' : ∀ᵐ x ∂μ, M + c ≤ f x + c := hM.mono fun x hx ↦ by linarith
  exact (OrderIso.essInf_apply f μ (OrderIso.addRight c) (isBoundedUnder_ge_ae hM)
    (isCoboundedUnder_ge_ae f) (isBoundedUnder_ge_ae hM') (isCoboundedUnder_ge_ae _)).symm

/-- **Scaling by a positive constant commutes with the essential infimum** of a real function
bounded below almost everywhere. -/
lemma essInf_const_mul [NeZero μ] {c : ℝ} (hc : 0 < c) (hM : ∀ᵐ x ∂μ, M ≤ f x) :
    essInf (fun x ↦ c * f x) μ = c * essInf f μ := by
  have hM' : ∀ᵐ x ∂μ, c * M ≤ c * f x := hM.mono fun x hx ↦ by nlinarith
  exact (OrderIso.essInf_apply f μ (OrderIso.mulLeft₀ c hc) (isBoundedUnder_ge_ae hM)
    (isCoboundedUnder_ge_ae f) (isBoundedUnder_ge_ae hM') (isCoboundedUnder_ge_ae _)).symm

/-- Comparing the essential infima of two real functions that differ by at most a constant. -/
lemma essInf_le_essInf_add [NeZero μ] {g : α → ℝ} {M' c : ℝ} (hM : ∀ᵐ x ∂μ, M ≤ f x)
    (hg : ∀ᵐ x ∂μ, M' ≤ g x) (h : ∀ᵐ x ∂μ, f x ≤ g x + c) :
    essInf f μ ≤ essInf g μ + c := by
  rw [← essInf_add_const hg c]
  exact essInf_mono_ae h (isBoundedUnder_ge_ae hM) (isCoboundedUnder_ge_ae _)

end MeasureTheory

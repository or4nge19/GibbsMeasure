/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential

/-!
# Single-site potentials

* `Potential.siteTerms f`: the family `A ↦ f i` if `A = {i}`, else `0`. The single-site
  counterpart of `Potential.pairTerms`.
* `Potential.site f`: the one-body potential `Φ_{\{i\}}(ω) = f i (ω i)`, `Φ_A = 0` otherwise. It
  is a potential in the sense of Georgii (2.2)(i) as soon as each `f i` is measurable
  (`Potential.isPotential_site`), and has finite range (Georgii (2.15)) unconditionally
  (`Potential.isFiniteRange_site`), each site interacting only with itself.

One-body terms appear in every Gibbsian model with an external field; Georgii's Gaussian
potential (13.11) is `Potential.site` plus `Potential.pair`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S]

section SiteTerms

variable {α : Type*} [AddCommMonoid α]

/-- The family `A ↦ f i` if `A = {i}`, and `0` otherwise, written as a `Finset.sum` so that it is
manifestly measurable in any parameters of `f`. The single-site counterpart of
`Potential.pairTerms`. -/
def siteTerms (f : S → α) (A : Finset S) : α :=
  ∑ i ∈ A, if A = {i} then f i else 0

variable {f g : S → α}

lemma siteTerms_singleton (i : S) : siteTerms f {i} = f i := by simp [siteTerms]

lemma siteTerms_eq_zero {A : Finset S} (hA : ∀ i, A ≠ {i}) : siteTerms f A = 0 :=
  Finset.sum_eq_zero fun i _ ↦ ite_eq_right (hA i)

/-- Summing `siteTerms f` over the powerset of `Δ` is summing `f` over `Δ`: only the singletons
`{i}`, `i ∈ Δ`, are both in `Δ.powerset` and possibly nonzero. The site-term counterpart of
`Potential.sum_powerset_pairTerms`. -/
lemma sum_powerset_siteTerms (Δ : Finset S) (f : S → α) :
    ∑ A ∈ Δ.powerset, siteTerms f A = ∑ i ∈ Δ, f i := by
  classical
  have hsub : Δ.image (fun i ↦ ({i} : Finset S)) ⊆ Δ.powerset := by
    intro A hA
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hA
    simpa using hi
  have hzero : ∀ A ∈ Δ.powerset, A ∉ Δ.image (fun i ↦ ({i} : Finset S)) → siteTerms f A = 0 := by
    intro A hA hAim
    refine siteTerms_eq_zero fun k hk ↦ hAim ?_
    have hkΔ : k ∈ Δ := Finset.mem_powerset.1 hA (hk ▸ Finset.mem_singleton_self k)
    exact Finset.mem_image.2 ⟨k, hkΔ, hk.symm⟩
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun a _ b _ hab ↦ Finset.singleton_injective hab)]
  exact Finset.sum_congr rfl fun i _ ↦ siteTerms_singleton i

end SiteTerms

/-- **The single-site half of a potential**: `Φ_{\{i\}} = f i (η i)`, and `Φ_A = 0` for every
other `A`. The counterpart of `Potential.pair` for singletons, needed because Georgii's (13.11)
is a one-body term (site) plus a pair term. -/
def site (f : S → E → ℝ) : Potential S E := fun A η ↦ siteTerms (fun i ↦ f i (η i)) A

variable {f : S → E → ℝ}

lemma site_apply (A : Finset S) (η : S → E) : site f A η = siteTerms (fun i ↦ f i (η i)) A := rfl

lemma site_singleton (i : S) (η : S → E) : site f {i} η = f i (η i) :=
  siteTerms_singleton i

lemma site_eq_zero {A : Finset S} (hA : ∀ i, A ≠ {i}) : site f A = 0 :=
  funext fun _ ↦ siteTerms_eq_zero hA

/-- A single-site potential with measurable `f i` is a potential in the sense of Georgii
(2.2)(i). -/
lemma isPotential_site (hf : ∀ i, Measurable (f i)) : IsPotential (site f) where
  measurable A := by
    unfold site siteTerms
    refine Finset.measurable_sum _ fun i hi ↦ ?_
    by_cases hA : A = {i}
    · simp only [ite_eq_left hA]
      exact (hf i).comp (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Finset.mem_coe.2 hi))
    · simp only [ite_eq_right hA]
      exact measurable_const

/-- A single-site potential has finite range unconditionally: each site interacts only with
itself. -/
lemma isFiniteRange_site : IsFiniteRange (site f) where
  exists_finset i := ⟨{i}, fun A hiA hΦ ↦ by
    by_cases hA : A = {i}
    · rw [hA]
    · exact absurd (site_eq_zero fun k hk ↦ hA (by
        have hik : i = k := Finset.mem_singleton.1 (hk ▸ hiA)
        rw [hik, hk])) hΦ⟩

end Potential

end

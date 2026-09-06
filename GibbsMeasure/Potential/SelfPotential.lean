/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Site
public import GibbsMeasure.Potential.Transformation

/-!
# Bounded single-site potentials belong to `ℬ` and, when homogeneous, to `ℬ_Θ`

`Potential.site f` (`GibbsMeasure/Potential/Site.lean`) is the potential `Φ_{i} = f i (η i)`,
`Φ_A = 0` for every volume `A` that is not a singleton. Georgii calls a homogeneous one — `f i = f`
for all `i` — a **self-potential**, and Example (15.50) is the large deviation principle for the
spatial means `M_Λ f = |Λ|⁻¹ ∑_{i ∈ Λ} f(σ_i)` that its Hamiltonians produce.

This file supplies the two structural facts that Example (15.50) needs and that
`GibbsMeasure/Potential/Site.lean` does not yet record:

* `Potential.normAt_site`, Georgii (2.12): `‖site f‖ᵢ = sup_η ‖f i (η i)‖`, since the site `i` is
  contained in exactly one volume carrying a nonzero interaction, namely `{i}`; hence
  `Potential.isAbsolutelySummable_site`, **a bounded single-site potential lies in Georgii's `ℬ`**
  (2.11).
* `Potential.isShiftInvariant_site`, Georgii (5.8): **a homogeneous single-site potential is
  shift invariant.** With the previous item, a bounded measurable `f : E → ℝ` gives an element of
  Georgii's Banach space `ℬ_Θ` (15.21).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure
open scoped ENNReal NNReal

noncomputable section

namespace Potential

variable {S E : Type*} [MeasurableSpace E] [DecidableEq S]

/-- A volume containing `i` and different from `{i}` is not a singleton, so it carries no
interaction of a single-site potential. -/
lemma site_eq_zero_of_mem_of_ne (f : S → E → ℝ) {A : Finset S} {i : S} (hi : i ∈ A)
    (hA : A ≠ {i}) : site f A = 0 :=
  site_eq_zero fun k hk ↦ hA (by subst hk; rw [Finset.mem_singleton.1 hi])

/-- **Georgii (2.12) for a single-site potential**: `‖site f‖ᵢ = sup_η ‖f i (η i)‖`. Only the
volume `{i}` contributes to the sum defining the norm at `i`. -/
theorem normAt_site (f : S → E → ℝ) (i : S) :
    (site f).normAt i = ⨆ η : S → E, ‖f i (η i)‖ₑ := by
  rw [normAt]
  refine (tsum_eq_single {i} fun A hA ↦ ?_).trans ?_
  · by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA),
        site_eq_zero_of_mem_of_ne f hiA hA]
      simp
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from hiA) _
  · rw [Set.indicator_of_mem
      (show ({i} : Finset S) ∈ {A : Finset S | i ∈ A} from Finset.mem_singleton_self i)]
    exact iSup_congr fun η ↦ by rw [site_singleton]

/-- **A bounded single-site potential lies in Georgii's `ℬ`** (2.11): its norm at every site is
the supremum of `|f i|`. -/
theorem isAbsolutelySummable_site {f : S → E → ℝ} {c : ℝ} (hb : ∀ i x, |f i x| ≤ c) :
    IsAbsolutelySummable (site f) where
  normAt_ne_top i := by
    have hle : (⨆ η : S → E, ‖f i (η i)‖ₑ) ≤ ENNReal.ofReal c := by
      refine iSup_le fun η ↦ ?_
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hb i (η i))
    rw [normAt_site]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-! ### The Hamiltonian of a single-site potential -/

/-- A single-site potential is its own one-body part: it vanishes on every volume that is not a
singleton. -/
@[simp] lemma oneBody_site (f : S → E → ℝ) : (site f).oneBody = site f := by
  funext A η
  rcases le_or_gt A.card 1 with h | h
  · rw [oneBody_of_card_le h]
  · rw [oneBody_of_one_lt_card h, site_eq_zero (fun i hi ↦ by
      rw [hi] at h; simp at h)]

/-- **The Hamiltonian of a single-site potential** is the spatial sum of its interactions,
`H^{site f}_Λ(η) = ∑_{i ∈ Λ} f i (η i)`: only the singletons `{i}` with `i ∈ Λ` carry a nonzero
term meeting `Λ`. -/
@[simp] theorem hamiltonian_site (f : S → E → ℝ) (Λ : Finset S) (η : S → E) :
    (site f).hamiltonian Λ η = ∑ i ∈ Λ, f i (η i) := by
  have h := hamiltonian_oneBody (Φ := site f) Λ η
  rw [oneBody_site] at h
  rw [h]
  exact Finset.sum_congr rfl fun i _ ↦ site_singleton i η

instance isSummable_site (f : S → E → ℝ) : IsSummable (site f) :=
  ⟨fun Λ η ↦ by
    rw [← oneBody_site f]
    exact (hasSum_hamiltonianTerms_oneBody (Φ := site f) Λ η).summable⟩

section Shift

variable {S : Type*} [AddGroup S] [DecidableEq S]

/-- **Georgii (5.8) for a self-potential.** A homogeneous single-site potential
`Φ_{i}(η) = f(η i)` is shift invariant: the shift takes the volume `{a}` to `{a + j}` and the
configuration `η` to `η(· − j)`, so `Φ_{a + j}(θ_j η) = f(η a) = Φ_{a}(η)`, and both sides vanish
on a volume that is not a singleton. -/
theorem isShiftInvariant_site (f : E → ℝ) : (site fun _ : S ↦ f).IsShiftInvariant := by
  rw [isShiftInvariant_iff]
  intro j A η
  rcases Finset.eq_empty_or_nonempty A with rfl | ⟨a, ha⟩
  · simp [site_apply, siteTerms]
  by_cases hA : A = {a}
  · subst hA
    have hmap : ({a} : Finset S).map (Equiv.addRight j).toEmbedding = {a + j} := by
      ext x; simp
    rw [hmap, site_singleton, site_singleton, shift_toFun_apply, add_sub_cancel_right]
  · have hmapne : ∀ k : S, A.map (Equiv.addRight j).toEmbedding ≠ {k} := by
      intro k hk
      refine hA (Finset.eq_singleton_iff_unique_mem.2 ⟨ha, fun b hb ↦ ?_⟩)
      have hb' : b + j ∈ A.map (Equiv.addRight j).toEmbedding :=
        Finset.mem_map.2 ⟨b, hb, rfl⟩
      have ha' : a + j ∈ A.map (Equiv.addRight j).toEmbedding :=
        Finset.mem_map.2 ⟨a, ha, rfl⟩
      rw [hk, Finset.mem_singleton] at hb' ha'
      exact add_right_cancel (hb'.trans ha'.symm)
    rw [site_eq_zero hmapne, site_eq_zero fun k hk ↦ hA (by
      subst hk; rw [Finset.mem_singleton.1 ha])]
    simp

end Shift

end Potential

end

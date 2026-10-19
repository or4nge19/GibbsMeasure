/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Summable

/-!
# The potential of a family of local terms

Many lattice models are given as a family of interaction terms `φ_b`, `b : ι`, each reading the
spins of one finite volume `supp b`, rather than volume by volume: the plaquettes of a lattice
gauge theory (`supp p` = the boundary links of `p`), the hyperedges of a hypergraph spin model,
a pair model with repeated bonds. Georgii's potential (2.2) collects the terms by volume,
`Φ_A = ∑_{b : supp b = A} φ_b`; this is `Potential.ofLocal supp φ`.

## Main results

* `Potential.isPotential_ofLocal`: **Georgii (2.2)(i)** — `φ_b` is `𝓕_{supp b}`-measurable and
  finitely many terms share each volume.
* `Potential.isFiniteRange_ofLocal`: **Georgii (2.15)** — each site lies in finitely many
  supports.
* `Potential.normAt_ofLocal_le`, `Potential.isAbsolutelySummable_ofLocal`: Georgii's
  `‖Φ‖ᵢ` (2.12) is at most `∑_{b : i ∈ supp b} sup |φ_b|`, so bounded terms with locally finite
  supports give `Φ ∈ ℬ` (2.11), the class on which
  `Potential.gibbsSpecificationOfAbsolutelySummable` and Dobrushin's theory (Georgii §8) are
  stated.
* `Potential.hamiltonian_ofLocal`, `Potential.hamiltonian_ofLocal_of_fintype`: Georgii (2.3) is
  the sum of the terms whose support meets `Λ`, `H_Λ = ∑_{b : supp b ∩ Λ ≠ ∅} φ_b`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Potential

variable {S E ι : Type*} [MeasurableSpace E] {supp : ι → Finset S} {φ : ι → (S → E) → ℝ}

variable (supp φ) in
/-- The potential of the local terms `φ b`, the term `b` being read on the volume `supp b`:
`Φ_A = ∑_{b : supp b = A} φ_b`. The `finsum` is a finite sum on every finite fibre
`supp ⁻¹' {A}`, which is all the results below use. -/
def ofLocal : Potential S E := fun A η ↦ ∑ᶠ b ∈ supp ⁻¹' {A}, φ b η

lemma ofLocal_apply (A : Finset S) (η : S → E) :
    ofLocal supp φ A η = ∑ᶠ b ∈ supp ⁻¹' {A}, φ b η := rfl

lemma ofLocal_apply_of_finite {A : Finset S} (hA : (supp ⁻¹' {A}).Finite) (η : S → E) :
    ofLocal supp φ A η = ∑ b ∈ hA.toFinset, φ b η :=
  finsum_mem_eq_finite_toFinset_sum _ hA

/-- A volume carrying a nonzero interaction is the support of one of the local terms. -/
lemma exists_supp_eq_of_ofLocal_ne_zero {A : Finset S} (h : ofLocal supp φ A ≠ 0) :
    ∃ b, supp b = A := by
  by_contra! hb
  exact h <| funext fun η ↦ finsum_mem_of_eqOn_zero fun b hb' ↦
    absurd (Set.mem_singleton_iff.1 hb') (hb b)

/-- The fibre of a volume containing `i` lies among the terms whose support contains `i`. -/
lemma preimage_singleton_subset_setOf_mem {A : Finset S} {i : S} (hi : i ∈ A) :
    supp ⁻¹' {A} ⊆ {b | i ∈ supp b} := fun b hb ↦ by
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hb
  change i ∈ supp b
  rw [hb]
  exact hi

/-- **Georgii (2.2)(i)** for `ofLocal`: if each term `φ_b` is `𝓕_{supp b}`-measurable and only
finitely many terms share a volume, then `ofLocal supp φ` is a potential. -/
lemma isPotential_ofLocal (hfin : ∀ A : Finset S, (supp ⁻¹' {A}).Finite)
    (hφ : ∀ b, Measurable[cylinderEvents (X := fun _ : S ↦ E) (supp b : Set S)] (φ b)) :
    IsPotential (ofLocal supp φ) where
  measurable A := by
    rw [show ofLocal supp φ A = fun η ↦ ∑ b ∈ (hfin A).toFinset, φ b η from
      funext (ofLocal_apply_of_finite (hfin A))]
    refine Finset.measurable_sum _ fun b hb ↦ ?_
    have hbA : supp b = A := by simpa using hb
    exact hbA ▸ hφ b

/-- **Georgii (2.15)** for `ofLocal`: if each site lies in the support of finitely many terms,
the potential has finite range. -/
lemma isFiniteRange_ofLocal (hloc : ∀ i, {b | i ∈ supp b}.Finite) :
    IsFiniteRange (ofLocal supp φ) where
  exists_finset i := by
    classical
    refine ⟨(hloc i).toFinset.biUnion supp, fun A hiA hA ↦ ?_⟩
    obtain ⟨b, rfl⟩ := exists_supp_eq_of_ofLocal_ne_zero hA
    exact Finset.subset_biUnion_of_mem supp (by simpa using hiA)

/-- The sup-norm of the interaction on a volume is at most the sum of the sup-norms of the terms
supported on it. -/
lemma iSup_enorm_ofLocal_le {A : Finset S} (hA : (supp ⁻¹' {A}).Finite) :
    ⨆ η, ‖ofLocal supp φ A η‖ₑ
      ≤ ∑' b, (supp ⁻¹' {A}).indicator (fun b ↦ ⨆ η, ‖φ b η‖ₑ) b := by
  refine iSup_le fun η ↦ ?_
  rw [ofLocal_apply_of_finite hA]
  refine (enorm_sum_le _ _).trans ((Finset.sum_le_sum fun b hb ↦ ?_).trans
    (ENNReal.sum_le_tsum hA.toFinset))
  rw [Set.indicator_of_mem (hA.mem_toFinset.1 hb)]
  exact le_iSup (fun η ↦ ‖φ b η‖ₑ) η

/-- **Georgii (2.12) for `ofLocal`**: `‖Φ‖ᵢ ≤ ∑_{b : i ∈ supp b} sup |φ_b|`. Each term enters the
norm at exactly one volume, its support. -/
theorem normAt_ofLocal_le (hloc : ∀ i, {b | i ∈ supp b}.Finite) (i : S) :
    (ofLocal supp φ).normAt i
      ≤ ∑' b, {b | i ∈ supp b}.indicator (fun b ↦ ⨆ η, ‖φ b η‖ₑ) b := by
  classical
  set M : ι → ℝ≥0∞ := fun b ↦ ⨆ η, ‖φ b η‖ₑ
  set g : Finset S → ι → ℝ≥0∞ := fun A b ↦ if supp b = A ∧ i ∈ A then M b else 0
  have hA : ∀ A : Finset S,
      {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖ofLocal supp φ A η‖ₑ) A ≤ ∑' b, g A b := by
    intro A
    by_cases hiA : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from hiA)]
      refine (iSup_enorm_ofLocal_le
        ((hloc i).subset (preimage_singleton_subset_setOf_mem hiA))).trans_eq
          (tsum_congr fun b ↦ ?_)
      by_cases hb : supp b = A
      · simp [g, M, hb, hiA]
      · simp [g, hb]
    · simp [hiA]
  have hb : ∀ b, ∑' A, g A b = {b | i ∈ supp b}.indicator M b := by
    intro b
    rw [tsum_eq_single (supp b) fun A hA ↦ by simp [g, Ne.symm hA]]
    by_cases hib : i ∈ supp b
    · simp [g, hib]
    · simp [g, hib]
  calc (ofLocal supp φ).normAt i ≤ ∑' A, ∑' b, g A b := ENNReal.tsum_le_tsum hA
    _ = ∑' b, ∑' A, g A b := ENNReal.tsum_comm
    _ = ∑' b, {b | i ∈ supp b}.indicator M b := tsum_congr hb

/-- **Georgii (2.11) for `ofLocal`**: bounded terms with locally finite supports give an
absolutely summable potential. -/
theorem isAbsolutelySummable_ofLocal (hloc : ∀ i, {b | i ∈ supp b}.Finite)
    (hφ : ∀ b, ⨆ η, ‖φ b η‖ₑ ≠ ∞) : IsAbsolutelySummable (ofLocal supp φ) where
  normAt_ne_top i := by
    refine ne_top_of_le_ne_top ?_ (normAt_ofLocal_le hloc i)
    rw [tsum_eq_sum (s := (hloc i).toFinset) fun b hb ↦
      Set.indicator_of_notMem (by simpa using hb) _]
    exact ENNReal.sum_ne_top.2 fun b _ ↦ (Set.indicator_le_self _ _ b).trans_lt
      (lt_top_iff_ne_top.2 (hφ b)) |>.ne

/-- The terms whose support meets a finite volume are finitely many. -/
lemma finite_setOf_not_disjoint (hloc : ∀ i, {b | i ∈ supp b}.Finite) (Λ : Finset S) :
    {b | ¬ Disjoint (supp b) Λ}.Finite := by
  refine (Λ.finite_toSet.biUnion fun i _ ↦ hloc i).subset fun b hb ↦ ?_
  obtain ⟨i, hib, hiΛ⟩ := Finset.not_disjoint_iff.1 hb
  exact Set.mem_biUnion (Finset.mem_coe.2 hiΛ) hib

/-- **Georgii (2.3) for `ofLocal`**: the Hamiltonian in `Λ` is the sum of the local terms whose
support meets `Λ`. -/
theorem hamiltonian_ofLocal (hloc : ∀ i, {b | i ∈ supp b}.Finite) (Λ : Finset S) (η : S → E) :
    (ofLocal supp φ).hamiltonian Λ η = ∑ᶠ b ∈ {b | ¬ Disjoint (supp b) Λ}, φ b η := by
  classical
  have hT := finite_setOf_not_disjoint hloc Λ
  set t := hT.toFinset with ht
  have hmem : ∀ b, b ∈ t ↔ ¬ Disjoint (supp b) Λ := fun b ↦ by simp [t]
  rw [finsum_mem_eq_finite_toFinset_sum _ hT]
  have hfib : ∀ A : Finset S, ¬ Disjoint A Λ →
      ofLocal supp φ A η = ∑ b ∈ t with supp b = A, φ b η := by
    intro A hA
    refine finsum_mem_eq_sum_of_subset _ (fun b hb ↦ ?_) fun b hb ↦ ?_
    · have hbA : supp b = A := hb.1
      rw [Finset.coe_filter]
      exact ⟨(hmem b).2 (hbA ▸ hA), hbA⟩
    · rw [Finset.coe_filter] at hb
      exact hb.2
  have hzero : ∀ A ∉ t.image supp, (ofLocal supp φ).hamiltonianTerms Λ η A = 0 := by
    intro A hA
    by_cases hAΛ : Disjoint A Λ
    · exact hamiltonianTerms_of_disjoint hAΛ η
    · rw [hamiltonianTerms_of_not_disjoint hAΛ, ofLocal_apply]
      refine finsum_mem_of_eqOn_zero fun b hb ↦ absurd ?_ hA
      have hbA : supp b = A := hb
      exact Finset.mem_image.2 ⟨b, (hmem b).2 (hbA ▸ hAΛ), hbA⟩
  have hsum : HasSum ((ofLocal supp φ).hamiltonianTerms Λ η) (∑ b ∈ t, φ b η) := by
    have heq : ∑ b ∈ t, φ b η
        = ∑ A ∈ t.image supp, (ofLocal supp φ).hamiltonianTerms Λ η A := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := supp) (t := t.image supp)
        fun b hb ↦ Finset.mem_image_of_mem supp hb]
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hA
      rw [hamiltonianTerms_of_not_disjoint ((hmem b).1 hb), hfib _ ((hmem b).1 hb)]
    rw [heq]
    exact hasSum_sum_of_ne_finset_zero hzero
  exact hsum.volume.tsum_eq

/-- `hamiltonian_ofLocal` for finitely many terms, as a `Finset` sum. -/
theorem hamiltonian_ofLocal_of_fintype [Fintype ι] [DecidableEq S] (Λ : Finset S) (η : S → E) :
    (ofLocal supp φ).hamiltonian Λ η = ∑ b with ¬ Disjoint (supp b) Λ, φ b η := by
  rw [hamiltonian_ofLocal (fun _ ↦ Set.toFinite _), ← Finset.coe_filter_univ,
    finsum_mem_coe_finset]

end Potential

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Space
public import GibbsMeasure.Mathlib.Data.Finset.Map
public import GibbsMeasure.Prereqs.Transformation

/-!
# Transformations of potentials, and the shift on `ℤ^d`

Georgii (5.3): the image `τ(Φ)_Λ = Φ_{τ_*⁻¹ Λ} ∘ τ⁻¹` of a potential under a transformation;
Georgii (5.2)(1)/(5.8): the shift `θ_j` on the lattice `ℤ^d` and shift-invariant potentials.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ### Georgii (5.3): the action on potentials -/

open MeasureTheory.GibbsMeasure Transformation

namespace Potential

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (5.3).** The image `τ(Φ)_Λ = Φ_{τ_*⁻¹ Λ} ∘ τ⁻¹` of a potential under a
transformation. -/
def map (τ : Transformation S E) (Φ : Potential S E) : Potential S E :=
  fun A η ↦ Φ (A.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)

lemma map_apply (τ : Transformation S E) (Φ : Potential S E) (A : Finset S) (η : S → E) :
    Potential.map τ Φ A η = Φ (A.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) :=
  rfl

/-- The image of a potential is a potential (Georgii, after (5.3)). -/
instance (τ : Transformation S E) (Φ : Potential S E) [IsPotential Φ] :
    IsPotential (Potential.map τ Φ) := by
  constructor
  intro Δ
  have h := τ.inv.measurable_comp_cylinderEvents
    (Λ := ((Δ.map τ.sites.symm.toEmbedding : Finset S) : Set S))
    (IsPotential.measurable (Φ := Φ) (Δ.map τ.sites.symm.toEmbedding))
  have hset : (τ.inv.sites ⁻¹' ((Δ.map τ.sites.symm.toEmbedding : Finset S) : Set S))
      = (Δ : Set S) := by
    ext i
    simp [inv, Finset.coe_map]
  rw [hset] at h
  exact h

end Potential

namespace Potential

variable {S E : Type*} [MeasurableSpace E] [AddGroup S]

/-- **Georgii (5.8).** A potential is shift-invariant if `Φ_{A + j} ∘ θ_j = Φ_A`. -/
def IsShiftInvariant (Φ : Potential S E) : Prop :=
  ∀ j, Potential.map (shift E j) Φ = Φ

end Potential

open MeasureTheory.GibbsMeasure Transformation Filter
open scoped Topology

namespace Potential

variable {S E : Type*} [MeasurableSpace E]

section Reindex

variable {α : Type*} [AddCommMonoid α] (σ : S ≃ S) (f : Finset S → α)

lemma sum_powerset_map (Δ : Finset S) :
    ∑ A ∈ Δ.powerset, f (A.map σ.toEmbedding) = ∑ B ∈ (Δ.map σ.toEmbedding).powerset, f B := by
  have h : Δ.powerset.map (Finset.mapEmbedding σ.toEmbedding).toEmbedding
      = (Δ.map σ.toEmbedding).powerset := by
    ext B
    simp only [Finset.mem_map, Finset.mem_powerset, RelEmbedding.coe_toEmbedding,
      Finset.mapEmbedding_apply]
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact Finset.map_subset_map.2 hA
    · intro hB
      refine ⟨B.map σ.symm.toEmbedding, ?_, Finset.map_map_symm σ B⟩
      rw [← Finset.map_subset_map (f := σ.toEmbedding), Finset.map_map_symm]
      exact hB
  rw [← h, Finset.sum_map]
  rfl

variable [TopologicalSpace α]

/-- Summation along `SummationFilter.volume` is invariant under reindexing by a bijection of the
sites. -/
lemma hasSum_volume_map_iff (a : α) :
    HasSum (fun A ↦ f (A.map σ.toEmbedding)) a (SummationFilter.volume S) ↔
      HasSum f a (SummationFilter.volume S) := by
  simp only [HasSum, SummationFilter.volume_filter, Filter.tendsto_map'_iff, Function.comp_def,
    sum_powerset_map σ f]
  conv_rhs => rw [← σ.finsetOrderIso.map_atTop, Filter.tendsto_map'_iff]
  exact Iff.rfl

lemma summable_volume_map_iff :
    Summable (fun A ↦ f (A.map σ.toEmbedding)) (SummationFilter.volume S) ↔
      Summable f (SummationFilter.volume S) :=
  exists_congr fun a ↦ hasSum_volume_map_iff σ f a

lemma tsum_volume_map [T2Space α] :
    ∑'[SummationFilter.volume S] A, f (A.map σ.toEmbedding)
      = ∑'[SummationFilter.volume S] B, f B := by
  by_cases h : Summable f (SummationFilter.volume S)
  · exact ((hasSum_volume_map_iff σ f _).2 h.hasSum).tsum_eq
  · rw [tsum_eq_zero_of_not_summable h,
      tsum_eq_zero_of_not_summable (mt (summable_volume_map_iff σ f).1 h)]

end Reindex

/-! ### Georgii (5.3): `Potential.map` is a left action -/

section Map

variable (τ σ : Transformation S E) (Φ : Potential S E)

/-- Georgii (5.3) is a left action: `τ(σ(Φ)) = (τ ∘ σ)(Φ)`. -/
lemma map_map : Potential.map τ (Potential.map σ Φ) = Potential.map (τ.comp σ) Φ := by
  funext A η
  rw [Potential.map_apply, Potential.map_apply, Potential.map_apply, comp_inv_toFun]
  congr 1
  ext i
  simp only [Finset.mem_map_equiv, Equiv.symm_symm]
  exact Iff.rfl

@[simp] lemma map_id : Potential.map Transformation.id Φ = Φ := by
  funext A η
  have h1 : A.map (Transformation.id : Transformation S E).sites.symm.toEmbedding = A :=
    Finset.ext fun i ↦ by simp [Transformation.id]
  have h2 : (Transformation.id : Transformation S E).inv.toFun η = η := by
    funext i; simp [Transformation.id, Transformation.inv, Transformation.toFun]
  rw [Potential.map_apply, h1, h2]

lemma hamiltonianTerms_map (Λ : Finset S) (ω : S → E) (A : Finset S) :
    (Potential.map τ Φ).hamiltonianTerms (Λ.map τ.sites.toEmbedding) (τ.toFun ω)
      (A.map τ.sites.toEmbedding) = Φ.hamiltonianTerms Λ ω A := by
  by_cases h : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint h,
      hamiltonianTerms_of_disjoint ((Finset.disjoint_map τ.sites.toEmbedding).2 h)]
  · rw [hamiltonianTerms_of_not_disjoint h,
      hamiltonianTerms_of_not_disjoint (mt (Finset.disjoint_map τ.sites.toEmbedding).1 h),
      Potential.map_apply, Finset.map_symm_map, inv_toFun_toFun]

lemma hamiltonianTerms_map' (Λ : Finset S) (η : S → E) (B : Finset S) :
    (Potential.map τ Φ).hamiltonianTerms Λ η B
      = Φ.hamiltonianTerms (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)
        (B.map τ.sites.symm.toEmbedding) := by
  have := hamiltonianTerms_map τ Φ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)
    (B.map τ.sites.symm.toEmbedding)
  rwa [Finset.map_map_symm, Finset.map_map_symm, toFun_inv_toFun] at this

/-- **Georgii (5.6)(c).** `H^{τ(Φ)}_{τ_* Λ} ∘ τ = H^Φ_Λ`. -/
theorem hamiltonian_map (Λ : Finset S) (ω : S → E) :
    (Potential.map τ Φ).hamiltonian (Λ.map τ.sites.toEmbedding) (τ.toFun ω)
      = Φ.hamiltonian Λ ω := by
  unfold hamiltonian
  exact (tsum_volume_map τ.sites _).symm.trans
    (tsum_congr fun A ↦ hamiltonianTerms_map τ Φ Λ ω A)

/-- Georgii (5.6)(c) in the form of (5.3): `H^{τ(Φ)}_Λ = H^Φ_{τ_*⁻¹ Λ} ∘ τ⁻¹`. -/
theorem hamiltonian_map' (Λ : Finset S) (η : S → E) :
    (Potential.map τ Φ).hamiltonian Λ η
      = Φ.hamiltonian (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η) := by
  have := hamiltonian_map τ Φ (Λ.map τ.sites.symm.toEmbedding) (τ.inv.toFun η)
  rwa [Finset.map_map_symm, toFun_inv_toFun] at this

instance [IsSummable Φ] : IsSummable (Potential.map τ Φ) where
  summable Λ η := by
    rw [funext (hamiltonianTerms_map' τ Φ Λ η)]
    exact (summable_volume_map_iff τ.sites.symm _).2 (IsSummable.summable _ _)

/-- Georgii (5.6)(c) for the Boltzmann factors: `h^{τ(Φ)}_{τ_* Λ} ∘ τ = h^Φ_Λ`. -/
theorem boltzmannFactor_map (β : ℝ) (Λ : Finset S) (ω : S → E) :
    (Potential.map τ Φ).boltzmannFactor β (Λ.map τ.sites.toEmbedding) (τ.toFun ω)
      = Φ.boltzmannFactor β Λ ω := by
  rw [boltzmannFactor, boltzmannFactor, hamiltonian_map]

instance [IsFiniteRange Φ] : IsFiniteRange (Potential.map τ Φ) where
  exists_finset i := by
    obtain ⟨Δ, hΔ⟩ := IsFiniteRange.exists_finset (Φ := Φ) (τ.sites.symm i)
    refine ⟨Δ.map τ.sites.toEmbedding, fun A hi hA ↦ ?_⟩
    have hΦ : Φ (A.map τ.sites.symm.toEmbedding) ≠ 0 := by
      intro h0
      apply hA
      funext η
      simp [Potential.map_apply, h0]
    have := hΔ (A.map τ.sites.symm.toEmbedding) (Finset.mem_map_of_mem _ hi) hΦ
    rw [← Finset.map_subset_map (f := τ.sites.toEmbedding), Finset.map_map_symm] at this
    exact this

/-- Georgii (5.7)(a): `τ` is a symmetry of `Φ` iff `Φ_{τ_* A} ∘ τ = Φ_A` for all `A`. -/
lemma map_eq_iff :
    Potential.map τ Φ = Φ ↔
      ∀ (A : Finset S) (η : S → E), Φ (A.map τ.sites.toEmbedding) (τ.toFun η) = Φ A η := by
  constructor
  · intro h A η
    conv_lhs => rw [← h]
    rw [Potential.map_apply, Finset.map_symm_map, inv_toFun_toFun]
  · intro h
    funext A η
    rw [Potential.map_apply, ← h (A.map τ.sites.symm.toEmbedding) (τ.inv.toFun η),
      Finset.map_map_symm, toFun_inv_toFun]

/-- Georgii (2.12) is transported by (5.3): `‖τ(Φ)‖_{τ_* i} = ‖Φ‖ᵢ`. -/
theorem normAt_map (i : S) : (Potential.map τ Φ).normAt (τ.sites i) = Φ.normAt i := by
  unfold normAt
  refine (τ.sites.finsetOrderIso.toEquiv.tsum_eq _).symm.trans (tsum_congr fun A ↦ ?_)
  change ({B : Finset S | τ.sites i ∈ B}.indicator (fun B ↦ ⨆ η, ‖Potential.map τ Φ B η‖ₑ))
    (A.map τ.sites.toEmbedding) = _
  by_cases h : i ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h), Set.indicator_of_mem
      (show A.map τ.sites.toEmbedding ∈ {B : Finset S | τ.sites i ∈ B} by
        simpa [Finset.mem_map_equiv] using h)]
    simp only [Potential.map_apply, Finset.map_symm_map]
    exact τ.toMeasurableEquiv.symm.toEquiv.iSup_comp (g := fun η ↦ ‖Φ A η‖ₑ)
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from h),
      Set.indicator_of_notMem
        (show A.map τ.sites.toEmbedding ∉ {B : Finset S | τ.sites i ∈ B} by
          simpa [Finset.mem_map_equiv] using h)]

instance [IsAbsolutelySummable Φ] : IsAbsolutelySummable (Potential.map τ Φ) where
  normAt_ne_top j := by
    have h := normAt_map τ Φ (τ.sites.symm j)
    rw [Equiv.apply_symm_apply] at h
    rw [h]
    exact IsAbsolutelySummable.normAt_ne_top _

lemma sum_normAt_map (Λ : Finset S) :
    ∑ j ∈ Λ.map τ.sites.toEmbedding, (Potential.map τ Φ).normAt j = ∑ i ∈ Λ, Φ.normAt i := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ ↦ normAt_map τ Φ i

/-- Georgii (2.14) is transported by (5.3): `∑_{j ∈ τ_* Λ} ‖τ(Φ)‖_j = ∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
lemma hamiltonianBound_map (Λ : Finset S) :
    (Potential.map τ Φ).hamiltonianBound (Λ.map τ.sites.toEmbedding) = Φ.hamiltonianBound Λ := by
  rw [hamiltonianBound, hamiltonianBound, sum_normAt_map]

lemma map_mem_absolutelySummable {Φ : Potential S E} (hΦ : Φ ∈ absolutelySummable S E) :
    Potential.map τ Φ ∈ absolutelySummable S E := by
  obtain ⟨_, h₂, _⟩ := hΦ
  exact ⟨inferInstance, funext fun η ↦ by simp [Potential.map_apply, h₂], inferInstance⟩

@[simp] lemma map_zero : Potential.map τ (0 : Potential S E) = 0 := rfl

lemma map_add (Φ Ψ : Potential S E) :
    Potential.map τ (Φ + Ψ) = Potential.map τ Φ + Potential.map τ Ψ := rfl

lemma map_sub (Φ Ψ : Potential S E) :
    Potential.map τ (Φ - Ψ) = Potential.map τ Φ - Potential.map τ Ψ := rfl

lemma map_smul (c : ℝ) : Potential.map τ (c • Φ) = c • Potential.map τ Φ := rfl

end Map

section Shift

variable {S : Type*} [AddGroup S]

/-- **Georgii (5.8).** `Φ` is shift-invariant iff `Φ_{A + j} ∘ θ_j = Φ_A` for all `A`, `j`. -/
lemma isShiftInvariant_iff (Φ : Potential S E) :
    Φ.IsShiftInvariant ↔ ∀ (j : S) (A : Finset S) (η : S → E),
      Φ (A.map (Equiv.addRight j).toEmbedding) ((shift E j).toFun η) = Φ A η :=
  forall_congr' fun j ↦ map_eq_iff (shift E j) Φ

variable {Φ Ψ : Potential S E}

lemma IsShiftInvariant.add (hΦ : Φ.IsShiftInvariant) (hΨ : Ψ.IsShiftInvariant) :
    (Φ + Ψ).IsShiftInvariant := fun j ↦ by rw [map_add, hΦ j, hΨ j]

lemma IsShiftInvariant.sub (hΦ : Φ.IsShiftInvariant) (hΨ : Ψ.IsShiftInvariant) :
    (Φ - Ψ).IsShiftInvariant := fun j ↦ by rw [map_sub, hΦ j, hΨ j]

lemma IsShiftInvariant.smul (c : ℝ) (hΦ : Φ.IsShiftInvariant) : (c • Φ).IsShiftInvariant :=
  fun j ↦ by rw [map_smul, hΦ j]

/-- Georgii (2.12) is constant along the sites for a shift-invariant potential:
`‖Φ‖ᵢ = ‖Φ‖₀`. -/
lemma IsShiftInvariant.normAt_eq (hΦ : Φ.IsShiftInvariant) (i : S) : Φ.normAt i = Φ.normAt 0 := by
  have h := normAt_map (shift E i) Φ 0
  rw [hΦ i] at h
  simpa [shift] using h

/-- Georgii (2.14) for a shift-invariant potential: the Hamiltonian bound is `|Λ| ‖Φ‖₀`. -/
lemma IsShiftInvariant.hamiltonianBound_eq (hΦ : Φ.IsShiftInvariant) (Λ : Finset S) :
    Φ.hamiltonianBound Λ = Λ.card * (Φ.normAt 0).toReal := by
  simp only [hamiltonianBound, hΦ.normAt_eq, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast]

end Shift

/-! ### Translates of finite volumes

The translate `A + g` of a finite volume, in the `Finset.map (Equiv.addRight g)` spelling used by
`isShiftInvariant_iff` above, together with its membership API. -/

section Translate

variable {S : Type*} [AddCommGroup S] {B : Finset S} {g h : S}

/-- The translate `A + g` of a finite set of sites. This is an `abbrev` for the
`Finset.map (Equiv.addRight g)` spelling of Georgii (5.8) (`isShiftInvariant_iff`), so the two
spellings are interchangeable. -/
abbrev translate (B : Finset S) (g : S) : Finset S := B.map (Equiv.addRight g).toEmbedding

@[simp] lemma mem_translate {x : S} : x ∈ translate B g ↔ x - g ∈ B := by
  rw [translate, Finset.mem_map_equiv]
  simp [sub_eq_add_neg]

lemma mem_translate_of_mem {x : S} (hx : x ∈ B) : x + g ∈ translate B g :=
  mem_translate.2 (by simpa using hx)

@[simp] lemma translate_zero (B : Finset S) : translate B 0 = B := by
  ext x; rw [mem_translate]; simp

lemma translate_translate (B : Finset S) (g h : S) :
    translate (translate B g) h = translate B (g + h) := by
  ext x
  rw [mem_translate, mem_translate, mem_translate, sub_sub, add_comm h g]

@[simp] lemma translate_nonempty : (translate B g).Nonempty ↔ B.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨x - g, mem_translate.1 hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x + g, mem_translate_of_mem hx⟩

lemma translate_subset_iff {Δ : Finset S} : translate B g ⊆ Δ ↔ ∀ x ∈ B, x + g ∈ Δ := by
  constructor
  · intro h x hx; exact h (mem_translate_of_mem hx)
  · intro h x hx
    have := h _ (mem_translate.1 hx)
    simpa using this

end Translate

section Closed

/-- The fixed-point set `{Φ ∈ ℬ : τ(Φ) = Φ}` of a transformation is closed in `ℬ`; cf. Georgii
(5.8), which states this for the shift group. -/
theorem isClosed_setOf_map_eq [Countable S] (τ : Transformation S E) :
    IsClosed {Φ : absolutelySummable S E | Potential.map τ (Φ : Potential S E) = Φ} := by
  rw [← isSeqClosed_iff_isClosed]
  intro u Φ hu hlim
  change Potential.map τ (Φ : Potential S E) = Φ
  rw [map_eq_iff]
  intro A η
  rcases A.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [Finset.map_empty, coe_apply_empty]
    rfl
  · refine tendsto_nhds_unique
      (tendsto_apply_of_tendsto hlim (Finset.mem_map_of_mem τ.sites.toEmbedding hi) (τ.toFun η)) ?_
    refine (tendsto_apply_of_tendsto hlim hi η).congr fun n ↦ ?_
    exact ((map_eq_iff τ _).1 (hu n) A η).symm

variable {d : ℕ}

/-- **Georgii (5.8).** `ℬ_Θ`, the set of shift-invariant elements of `ℬ`, is closed. -/
theorem isClosed_setOf_isShiftInvariant :
    IsClosed {Φ : absolutelySummable (Fin d → ℤ) E |
      (Φ : Potential (Fin d → ℤ) E).IsShiftInvariant} := by
  have : {Φ : absolutelySummable (Fin d → ℤ) E | (Φ : Potential (Fin d → ℤ) E).IsShiftInvariant}
      = ⋂ j, {Φ : absolutelySummable (Fin d → ℤ) E |
        Potential.map (shift E j) (Φ : Potential (Fin d → ℤ) E) = Φ} := by
    ext Φ
    simp [IsShiftInvariant]
  rw [this]
  exact isClosed_iInter fun j ↦ isClosed_setOf_map_eq (shift E j)

end Closed

end Potential

end

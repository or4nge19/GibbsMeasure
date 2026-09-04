/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Reindexing the sites of a potential along a bijection

Georgii states the lattice-gas and Markov-chain results on the site set `ℤ` and the thermodynamic
formalism of Chapter 15 on `ℤ^d`; Example (15.40) identifies `ℤ` with `ℤ^1`. This file transports
the objects of Chapter 2 along an arbitrary bijection `e : S ≃ S'` of site sets, the spin space `E`
being fixed:

* configurations, by precomposition:
  `MeasurableEquiv.arrowCongr' e (.refl E) : (S → E) ≃ᵐ (S' → E)`, `ω ↦ ω ∘ e.symm`
  (`Mathlib/MeasureTheory/Constructions/Cylinders.lean` records that it carries
  `cylinderEvents Δ` to `cylinderEvents (e '' Δ)`);
* transformations (Georgii (5.1)): `Transformation.reindex e τ` is the conjugate of `τ` by the
  configuration equivalence, and `e ↦ Transformation.reindexMulEquiv e` is a group isomorphism
  carrying the shift `θ_j` to `θ_{e j}` when `e` is additive;
* potentials: `Potential.reindex e Φ` has interaction `Φ_{e⁻¹ A} ∘ (ω ↦ ω ∘ e)` on the volume
  `A ⊆ S'`. It is the analogue of Georgii (5.3) for a bijection between *different* site sets, and
  `Potential.map (siteEquiv E e) Φ = Φ.reindex e` definitionally when `S' = S`.

Everything Chapter 2 attaches to a potential is transported: `IsPotential`, `IsFiniteRange`,
`IsSummable`, `IsAbsolutelySummable`, the Hamiltonians `H_Λ`, the Boltzmann factors, Georgii's
norms `‖Φ‖ᵢ` (2.12) and the bound (2.14), membership in `ℬ`, and shift invariance (5.8) along an
additive bijection.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure Set
open scoped ENNReal

noncomputable section

/-! ### Transformations conjugated by a bijection of the site sets -/

namespace MeasureTheory.GibbsMeasure.Transformation

variable {S S' E : Type*} [MeasurableSpace E]

/-- The transformation of `S' → E` obtained from a transformation `τ` of `S → E` by conjugating
with the reindexing `ω ↦ ω ∘ e.symm` along `e : S ≃ S'`: its spatial part is `e ∘ τ_* ∘ e⁻¹` and
its spin at `i'` is the spin of `τ` at `e⁻¹ i'`. -/
def reindex (e : S ≃ S') (τ : Transformation S E) : Transformation S' E where
  sites := e.symm.trans (τ.sites.trans e)
  spin i := τ.spin (e.symm i)

variable (e : S ≃ S') (τ σ : Transformation S E)

@[simp] lemma reindex_sites : (τ.reindex e).sites = e.symm.trans (τ.sites.trans e) := rfl

@[simp] lemma reindex_spin (i : S') : (τ.reindex e).spin i = τ.spin (e.symm i) := rfl

/-- `τ.reindex e` is the conjugate of `τ` by the configuration equivalence. -/
lemma reindex_toFun :
    (τ.reindex e).toFun = MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ∘ τ.toFun ∘
      (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm := rfl

lemma reindex_toFun_apply (ω : S' → E) (i : S') :
    (τ.reindex e).toFun ω i = τ.spin (e.symm i) (ω (e (τ.sites.symm (e.symm i)))) := rfl

lemma reindex_toFun_arrowCongr' (ω : S → E) :
    (τ.reindex e).toFun (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) =
      MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) (τ.toFun ω) := by
  rw [reindex_toFun, Function.comp_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]

lemma reindex_id : (Transformation.id : Transformation S E).reindex e = Transformation.id :=
  Transformation.ext (Equiv.ext fun i ↦ by simp [Transformation.id]) rfl

lemma reindex_comp : (τ.comp σ).reindex e = (τ.reindex e).comp (σ.reindex e) :=
  Transformation.ext (Equiv.ext fun i ↦ by simp [Transformation.comp])
    (funext fun i ↦ by simp [Transformation.comp])

lemma reindex_inv : τ.inv.reindex e = (τ.reindex e).inv :=
  Transformation.ext (Equiv.ext fun i ↦ by simp [Transformation.inv])
    (funext fun i ↦ by simp [Transformation.inv])

lemma reindex_refl : τ.reindex (Equiv.refl S) = τ :=
  Transformation.ext (Equiv.ext fun _ ↦ rfl) rfl

lemma reindex_reindex {S'' : Type*} (f : S' ≃ S'') :
    (τ.reindex e).reindex f = τ.reindex (e.trans f) :=
  Transformation.ext (Equiv.ext fun _ ↦ rfl) rfl

lemma reindex_symm_reindex : (τ.reindex e).reindex e.symm = τ := by
  rw [reindex_reindex, Equiv.self_trans_symm, reindex_refl]

variable (E) in
/-- Conjugation by the reindexing along `e : S ≃ S'` is a group isomorphism of Georgii's
transformation groups `T`. -/
def reindexMulEquiv : Transformation S E ≃* Transformation S' E where
  toFun := reindex e
  invFun := reindex e.symm
  left_inv τ := reindex_symm_reindex e τ
  right_inv τ := by rw [reindex_reindex, Equiv.symm_trans_self, reindex_refl]
  map_mul' τ σ := reindex_comp e τ σ

@[simp] lemma reindexMulEquiv_apply : reindexMulEquiv E e τ = τ.reindex e := rfl

@[simp] lemma reindexMulEquiv_symm_apply (τ : Transformation S' E) :
    (reindexMulEquiv E e).symm τ = τ.reindex e.symm := rfl

/-- Reindexing a site bijection (Georgii (5.2)(2)) along `e` conjugates it by `e`. -/
lemma reindex_siteEquiv (f : S ≃ S) :
    (siteEquiv E f).reindex e = siteEquiv E (e.symm.trans (f.trans e)) := rfl

/-- The site bijection `siteEquiv E e` of Georgii (5.2)(2) acts on configurations as the
reindexing `ω ↦ ω ∘ e.symm`: `siteEquiv` is the `S' = S` instance of the configuration
equivalence. -/
lemma siteEquiv_toFun (e : S ≃ S) :
    (siteEquiv E e).toFun = MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) := rfl

lemma siteEquiv_toMeasurableEquiv (e : S ≃ S) :
    (siteEquiv E e).toMeasurableEquiv = MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) :=
  MeasurableEquiv.ext rfl

/-- Reindexing along an additive bijection carries the shift `θ_j` (Georgii (5.2)(1)) to
`θ_{e j}`. -/
lemma reindex_shift [AddGroup S] [AddGroup S'] (e : S ≃+ S') (j : S) :
    (shift E j).reindex (e : S ≃ S') = shift E (e j) :=
  Transformation.ext (Equiv.ext fun i ↦ by simp [shift]) rfl

end MeasureTheory.GibbsMeasure.Transformation

/-! ### Reindexing potentials -/

namespace Potential

variable {S S' E : Type*} [MeasurableSpace E]

/-- The potential on `S'` obtained from a potential `Φ` on `S` by reindexing the sites along
`e : S ≃ S'`: `(Φ.reindex e)_A(η) = Φ_{e⁻¹ A}(η ∘ e)`. This is Georgii (5.3) for the site
bijection `e`, between different site sets. -/
def reindex (e : S ≃ S') (Φ : Potential S E) : Potential S' E :=
  fun A η ↦ Φ (A.map e.symm.toEmbedding) (η ∘ e)

variable (e : S ≃ S') (Φ : Potential S E)

lemma reindex_apply (A : Finset S') (η : S' → E) :
    Φ.reindex e A η = Φ (A.map e.symm.toEmbedding) (η ∘ e) := rfl

lemma reindex_apply_arrowCongr' (A : Finset S') (η : S' → E) :
    Φ.reindex e A η = Φ (A.map e.symm.toEmbedding)
      ((MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm η) := rfl

/-- `Φ.reindex e` on the image of a volume, evaluated on a reindexed configuration. -/
lemma reindex_map_arrowCongr' (A : Finset S) (η : S → E) :
    Φ.reindex e (A.map e.toEmbedding) (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) η) =
      Φ A η := by
  rw [reindex_apply_arrowCongr', Finset.map_symm_map, MeasurableEquiv.symm_apply_apply]

/-- `Potential.map` along the site bijection `siteEquiv E e` of Georgii (5.2)(2) is
`Potential.reindex e`: the two notions agree definitionally when the site sets coincide. -/
lemma map_siteEquiv (e : S ≃ S) : Potential.map (siteEquiv E e) Φ = Φ.reindex e := rfl

/-- Reindexing commutes with Georgii's action (5.3):
`(τ Φ).reindex e = (τ.reindex e) (Φ.reindex e)`. -/
lemma map_reindex (τ : Transformation S E) :
    Potential.map (τ.reindex e) (Φ.reindex e) = (Potential.map τ Φ).reindex e := by
  funext A η
  simp only [Potential.map_apply, reindex_apply]
  congr 1
  · ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Transformation.reindex_sites,
      Equiv.trans_apply, Equiv.symm_apply_apply]
  · rw [← Transformation.reindex_inv]
    funext i
    simp [Transformation.toFun]

@[simp] lemma reindex_refl : Φ.reindex (Equiv.refl S) = Φ := by
  funext A η
  simp [reindex_apply]

lemma reindex_reindex {S'' : Type*} (f : S' ≃ S'') :
    (Φ.reindex e).reindex f = Φ.reindex (e.trans f) := by
  funext A η
  simp only [reindex_apply, Finset.map_map]
  rfl

@[simp] lemma reindex_symm_reindex : (Φ.reindex e).reindex e.symm = Φ := by
  rw [reindex_reindex, Equiv.self_trans_symm, reindex_refl]

@[simp] lemma reindex_reindex_symm (Ψ : Potential S' E) : (Ψ.reindex e.symm).reindex e = Ψ := by
  rw [reindex_reindex, Equiv.symm_trans_self, reindex_refl]

@[simp] lemma reindex_zero : (0 : Potential S E).reindex e = 0 := rfl

lemma reindex_add (Ψ : Potential S E) : (Φ + Ψ).reindex e = Φ.reindex e + Ψ.reindex e := rfl

lemma reindex_sub (Ψ : Potential S E) : (Φ - Ψ).reindex e = Φ.reindex e - Ψ.reindex e := rfl

lemma reindex_neg : (-Φ).reindex e = -Φ.reindex e := rfl

lemma reindex_smul (c : ℝ) : (c • Φ).reindex e = c • Φ.reindex e := rfl

lemma reindex_injective : Function.Injective (reindex (E := E) e) := fun Φ Ψ h ↦ by
  rw [← reindex_symm_reindex e Φ, h, reindex_symm_reindex]

/-- The image `e '' (e⁻¹ A)` of a reindexed volume is the volume. -/
lemma coe_map_symm_image (A : Finset S') :
    e '' ((A.map e.symm.toEmbedding : Finset S) : Set S) = (A : Set S') := by
  rw [Finset.coe_map, Equiv.coe_toEmbedding, Equiv.image_symm_image]

/-- The reindexed potential is an interaction potential (Georgii (2.2)(i)). -/
instance [IsPotential Φ] : IsPotential (Φ.reindex e) where
  measurable A := by
    have h := (IsPotential.measurable (Φ := Φ) (A.map e.symm.toEmbedding)).comp
      (measurable_arrowCongr'_refl_symm_cylinderEvents (E := E) e
        ((A.map e.symm.toEmbedding : Finset S) : Set S))
    rwa [coe_map_symm_image] at h

/-- The reindexed potential has finite range when `Φ` has (Georgii (2.15)). -/
instance [IsFiniteRange Φ] : IsFiniteRange (Φ.reindex e) where
  exists_finset i := by
    obtain ⟨Δ, hΔ⟩ := IsFiniteRange.exists_finset (Φ := Φ) (e.symm i)
    refine ⟨Δ.map e.toEmbedding, fun A hi hA ↦ ?_⟩
    have hΦ : Φ (A.map e.symm.toEmbedding) ≠ 0 := by
      intro h0
      apply hA
      funext η
      simp [reindex_apply, h0]
    have := hΔ (A.map e.symm.toEmbedding) (Finset.mem_map_of_mem _ hi) hΦ
    rw [← Finset.map_subset_map (f := e.toEmbedding), Finset.map_map_symm] at this
    exact this

/-! #### Hamiltonians and Boltzmann factors -/

lemma hamiltonianTerms_reindex (Λ : Finset S) (ω : S → E) (A : Finset S) :
    (Φ.reindex e).hamiltonianTerms (Λ.map e.toEmbedding)
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) (A.map e.toEmbedding) =
      Φ.hamiltonianTerms Λ ω A := by
  by_cases h : Disjoint A Λ
  · rw [hamiltonianTerms_of_disjoint h,
      hamiltonianTerms_of_disjoint ((Finset.disjoint_map e.toEmbedding).2 h)]
  · rw [hamiltonianTerms_of_not_disjoint h,
      hamiltonianTerms_of_not_disjoint (mt (Finset.disjoint_map e.toEmbedding).1 h),
      reindex_map_arrowCongr']

lemma hamiltonianTerms_reindex' (Λ : Finset S') (η : S' → E) (B : Finset S') :
    (Φ.reindex e).hamiltonianTerms Λ η B =
      Φ.hamiltonianTerms (Λ.map e.symm.toEmbedding) (η ∘ e) (B.map e.symm.toEmbedding) := by
  have := hamiltonianTerms_reindex e Φ (Λ.map e.symm.toEmbedding) (η ∘ e)
    (B.map e.symm.toEmbedding)
  rwa [Finset.map_map_symm, Finset.map_map_symm,
    show MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) (η ∘ e) = η from
      funext fun i ↦ by simp] at this

/-- **Georgii (5.6)(c)** for a reindexing: `H^{Φ.reindex e}_{e Λ}(ω ∘ e⁻¹) = H^Φ_Λ(ω)`. -/
theorem hamiltonian_reindex (Λ : Finset S) (ω : S → E) :
    (Φ.reindex e).hamiltonian (Λ.map e.toEmbedding)
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) =
      Φ.hamiltonian Λ ω := by
  unfold hamiltonian
  exact (SummationFilter.tsum_volume_map_equiv e _).symm.trans
    (tsum_congr fun A ↦ hamiltonianTerms_reindex e Φ Λ ω A)

/-- Georgii (5.6)(c) in the form of (5.3): `H^{Φ.reindex e}_Λ(η) = H^Φ_{e⁻¹ Λ}(η ∘ e)`. -/
theorem hamiltonian_reindex' (Λ : Finset S') (η : S' → E) :
    (Φ.reindex e).hamiltonian Λ η = Φ.hamiltonian (Λ.map e.symm.toEmbedding) (η ∘ e) := by
  have := hamiltonian_reindex e Φ (Λ.map e.symm.toEmbedding) (η ∘ e)
  rwa [Finset.map_map_symm,
    show MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) (η ∘ e) = η from
      funext fun i ↦ by simp] at this

/-- The reindexed potential is summable when `Φ` is (Georgii (2.2)(ii)). -/
instance [IsSummable Φ] : IsSummable (Φ.reindex e) where
  summable Λ η := by
    rw [funext (hamiltonianTerms_reindex' e Φ Λ η)]
    exact (SummationFilter.summable_volume_map_equiv_iff e.symm _).2 (IsSummable.summable _ _)

theorem boltzmannFactor_reindex (β : ℝ) (Λ : Finset S) (ω : S → E) :
    (Φ.reindex e).boltzmannFactor β (Λ.map e.toEmbedding)
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E) ω) =
      Φ.boltzmannFactor β Λ ω := by
  rw [boltzmannFactor, boltzmannFactor, hamiltonian_reindex]

theorem boltzmannFactor_reindex' (β : ℝ) (Λ : Finset S') (η : S' → E) :
    (Φ.reindex e).boltzmannFactor β Λ η =
      Φ.boltzmannFactor β (Λ.map e.symm.toEmbedding) (η ∘ e) := by
  rw [boltzmannFactor, boltzmannFactor, hamiltonian_reindex']

/-! #### Georgii's norms (2.12) and absolute summability (2.11) -/

/-- Georgii (2.12) is transported: `‖Φ.reindex e‖_{e i} = ‖Φ‖ᵢ`. -/
theorem normAt_reindex (i : S) : (Φ.reindex e).normAt (e i) = Φ.normAt i := by
  unfold normAt
  refine (e.finsetOrderIso.toEquiv.tsum_eq _).symm.trans (tsum_congr fun A ↦ ?_)
  change ({B : Finset S' | e i ∈ B}.indicator (fun B ↦ ⨆ η, ‖Φ.reindex e B η‖ₑ))
    (A.map e.toEmbedding) = _
  by_cases h : i ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {A : Finset S | i ∈ A} from h), Set.indicator_of_mem
      (show A.map e.toEmbedding ∈ {B : Finset S' | e i ∈ B} by
        simpa [Finset.mem_map_equiv] using h)]
    simp only [reindex_apply, Finset.map_symm_map]
    exact (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl E)).symm.toEquiv.iSup_comp
      (g := fun η ↦ ‖Φ A η‖ₑ)
  · rw [Set.indicator_of_notMem (show A ∉ {A : Finset S | i ∈ A} from h),
      Set.indicator_of_notMem
        (show A.map e.toEmbedding ∉ {B : Finset S' | e i ∈ B} by
          simpa [Finset.mem_map_equiv] using h)]

theorem normAt_reindex' (i : S') : (Φ.reindex e).normAt i = Φ.normAt (e.symm i) := by
  rw [← normAt_reindex e Φ (e.symm i), Equiv.apply_symm_apply]

/-- The reindexed potential is absolutely summable when `Φ` is (Georgii (2.11)). -/
instance [IsAbsolutelySummable Φ] : IsAbsolutelySummable (Φ.reindex e) where
  normAt_ne_top j := by
    rw [normAt_reindex']
    exact IsAbsolutelySummable.normAt_ne_top _

lemma sum_normAt_reindex (Λ : Finset S) :
    ∑ j ∈ Λ.map e.toEmbedding, (Φ.reindex e).normAt j = ∑ i ∈ Λ, Φ.normAt i := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ ↦ normAt_reindex e Φ i

/-- Georgii (2.14) is transported: `∑_{j ∈ e Λ} ‖Φ.reindex e‖_j = ∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
lemma hamiltonianBound_reindex (Λ : Finset S) :
    (Φ.reindex e).hamiltonianBound (Λ.map e.toEmbedding) = Φ.hamiltonianBound Λ := by
  rw [hamiltonianBound, hamiltonianBound, sum_normAt_reindex]

lemma hamiltonianBound_reindex' (Λ : Finset S') :
    (Φ.reindex e).hamiltonianBound Λ = Φ.hamiltonianBound (Λ.map e.symm.toEmbedding) := by
  rw [← hamiltonianBound_reindex e Φ, Finset.map_map_symm]

/-- Reindexing preserves Georgii's space `ℬ` of (2.11). -/
lemma reindex_mem_absolutelySummable {Φ : Potential S E} (hΦ : Φ ∈ absolutelySummable S E) :
    Φ.reindex e ∈ absolutelySummable S' E := by
  obtain ⟨_, h₂, _⟩ := hΦ
  exact ⟨inferInstance, funext fun η ↦ by simp [reindex_apply, h₂], inferInstance⟩

lemma reindex_mem_absolutelySummable_iff {Φ : Potential S E} :
    Φ.reindex e ∈ absolutelySummable S' E ↔ Φ ∈ absolutelySummable S E :=
  ⟨fun h ↦ by simpa using reindex_mem_absolutelySummable e.symm h,
    reindex_mem_absolutelySummable e⟩

/-! #### Shift invariance (Georgii (5.8)) along an additive bijection -/

variable {Φ} in
/-- Reindexing along an additive bijection `e : S ≃+ S'` preserves shift invariance
(Georgii (5.8)): `Φ.reindex e ∈ ℬ_Θ` iff `Φ ∈ ℬ_Θ`. -/
theorem isShiftInvariant_reindex_iff [AddGroup S] [AddGroup S'] (e : S ≃+ S') :
    (Φ.reindex (e : S ≃ S')).IsShiftInvariant ↔ Φ.IsShiftInvariant := by
  simp only [IsShiftInvariant]
  constructor
  · intro h j
    have := h (e j)
    rw [← Transformation.reindex_shift e j, map_reindex] at this
    exact reindex_injective (e : S ≃ S') this
  · intro h j'
    obtain ⟨j, rfl⟩ := e.surjective j'
    rw [← Transformation.reindex_shift e j, map_reindex, h j]

alias ⟨IsShiftInvariant.of_reindex, IsShiftInvariant.reindex⟩ := isShiftInvariant_reindex_iff

end Potential

end

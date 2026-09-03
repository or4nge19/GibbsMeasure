/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Prereqs.CylinderEvents
public import GibbsMeasure.Prereqs.Juxt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure

/-!
# Transformations of configuration space

Georgii §5.1, (5.1): transformations `τ = (τ_*; τ_i)` of `S → E` built from a bijection `τ_*` of
the sites and measurable bijections `τ_i` of the state space, acting by
`(τ ω)_i = τ_i (ω_{τ_*⁻¹ i})`. They form a group and transport the finite-volume σ-algebras:
`f ∘ τ` is `𝓕_{τ_*⁻¹ Λ}`-measurable when `f` is `𝓕_Λ`-measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (5.1).** A transformation `τ = (τ_*; τ_i)` of the configuration space: a bijection
`τ_*` of the sites and a measurable bijection `τ_i` of the state space at each site, acting by
`(τ ω)_i = τ_i (ω_{τ_*⁻¹ i})`. -/
structure Transformation (S E : Type*) [MeasurableSpace E] where
  /-- The spatial part `τ_*`. -/
  sites : S ≃ S
  /-- The spin transformations `τ_i`. -/
  spin : S → E ≃ᵐ E

namespace Transformation

variable (τ : Transformation S E)

/-- The action of `τ` on configurations, Georgii (5.1). -/
def toFun (ω : S → E) : S → E := fun i ↦ τ.spin i (ω (τ.sites.symm i))

/-- The inverse transformation `τ⁻¹ = (τ_*⁻¹; τ_{τ_* i}⁻¹)` (Georgii, after (5.1)). -/
def inv : Transformation S E where
  sites := τ.sites.symm
  spin i := (τ.spin (τ.sites i)).symm

lemma inv_toFun_toFun (ω : S → E) : τ.inv.toFun (τ.toFun ω) = ω := by
  funext i
  simp [toFun, inv]

lemma toFun_inv_toFun (ω : S → E) : τ.toFun (τ.inv.toFun ω) = ω := by
  funext i
  simp [toFun, inv]

lemma measurable_toFun : Measurable τ.toFun :=
  measurable_pi_lambda _ fun i ↦ (τ.spin i).measurable.comp (measurable_pi_apply _)

/-- `τ` as a measurable equivalence of the configuration space. -/
def toMeasurableEquiv : (S → E) ≃ᵐ (S → E) where
  toFun := τ.toFun
  invFun := τ.inv.toFun
  left_inv := τ.inv_toFun_toFun
  right_inv := τ.toFun_inv_toFun
  measurable_toFun := τ.measurable_toFun
  measurable_invFun := τ.inv.measurable_toFun

@[simp] lemma toMeasurableEquiv_apply (ω : S → E) (i : S) :
    τ.toMeasurableEquiv ω i = τ.spin i (ω (τ.sites.symm i)) := rfl

@[simp] lemma toMeasurableEquiv_symm_apply (ω : S → E) (i : S) :
    τ.toMeasurableEquiv.symm ω i = (τ.spin (τ.sites i)).symm (ω (τ.sites i)) := rfl

instance : CoeFun (Transformation S E) (fun _ ↦ (S → E) → (S → E)) := ⟨fun τ ↦ τ.toFun⟩

/-- Composition of transformations (Georgii: `T` is a group). -/
def comp (τ σ : Transformation S E) : Transformation S E where
  sites := σ.sites.trans τ.sites
  spin i := (σ.spin (τ.sites.symm i)).trans (τ.spin i)

lemma comp_toFun (τ σ : Transformation S E) (ω : S → E) :
    (τ.comp σ).toFun ω = τ.toFun (σ.toFun ω) := by
  funext i
  simp [toFun, comp]

/-- The identity transformation. -/
def id : Transformation S E where
  sites := Equiv.refl S
  spin _ := MeasurableEquiv.refl E

@[simp] lemma id_toFun (ω : S → E) : (id : Transformation S E).toFun ω = ω := by
  funext i; simp [toFun, id]

/-! ### Transport of the finite-volume σ-algebras (Georgii, remark after (5.1)) -/

/-- `τ` is measurable from `𝓕_{τ_*⁻¹ Λ}` to `𝓕_Λ`: the spatial part transports the finite-volume
σ-algebras (Georgii, remark after (5.1)). -/
lemma measurable_toFun_cylinderEvents (Λ : Set S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (τ.sites ⁻¹' Λ),
      cylinderEvents (X := fun _ : S ↦ E) Λ] τ.toFun := by
  let : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (τ.sites ⁻¹' Λ)
  rw [measurable_iff_comap_le, cylinderEvents_eq_comap_domRestrict (X := fun _ : S ↦ E) Λ,
    MeasurableSpace.comap_comp]
  refine Measurable.comap_le ?_
  refine measurable_pi_lambda _ fun j ↦ ?_
  have hj : τ.sites.symm j ∈ τ.sites ⁻¹' Λ := by simp [j.2]
  exact (τ.spin j).measurable.comp (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) hj)

/-- `f ∘ τ` is `𝓕_{τ_*⁻¹ Λ}`-measurable when `f` is `𝓕_Λ`-measurable. -/
lemma measurable_comp_cylinderEvents {Λ : Set S} {Z : Type*} [MeasurableSpace Z]
    {f : (S → E) → Z} (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λ] f) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (τ.sites ⁻¹' Λ)] (f ∘ τ.toFun) :=
  hf.comp (τ.measurable_toFun_cylinderEvents Λ)

end Transformation

namespace Transformation

variable (τ : Transformation S E)


/-- `τ_*⁻¹ Λ` as the preimage of `Λ` under `τ_*`. -/
lemma sites_preimage_coe (Λ : Finset S) :
    τ.sites ⁻¹' (Λ : Set S) = ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S) := by
  ext i; simp

/-- `τ` is measurable from `𝓕_{(τ_*⁻¹ Λ)ᶜ}` to `𝓕_{Λᶜ}` (Georgii, remark after (5.1)). -/
lemma measurable_toFun_cylinderEvents_compl (Λ : Finset S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E)
        ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S)ᶜ,
      cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ] τ.toFun := by
  have h := τ.measurable_toFun_cylinderEvents (Λ : Set S)ᶜ
  rwa [preimage_compl, sites_preimage_coe] at h

/-- `τ⁻¹` is measurable from `𝓕_{Λᶜ}` to `𝓕_{(τ_*⁻¹ Λ)ᶜ}` (Georgii, remark after (5.1)). -/
lemma measurable_inv_toFun_cylinderEvents_compl (Λ : Finset S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ,
      cylinderEvents (X := fun _ : S ↦ E)
        ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S)ᶜ] τ.inv.toFun := by
  have h := τ.inv.measurable_toFun_cylinderEvents
    ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S)ᶜ
  have hset : τ.inv.sites ⁻¹' ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S)ᶜ =
      (Λ : Set S)ᶜ := by
    ext i; simp [Transformation.inv]
  rwa [hset] at h

variable (σ : Transformation S E)

lemma comp_inv_toFun (ω : S → E) : (τ.comp σ).inv.toFun ω = σ.inv.toFun (τ.inv.toFun ω) := by
  conv_lhs => rw [← τ.toFun_inv_toFun ω, ← σ.toFun_inv_toFun (τ.inv.toFun ω), ← comp_toFun]
  exact (τ.comp σ).inv_toFun_toFun _

@[simp] lemma id_inv_toFun (ω : S → E) : (id : Transformation S E).inv.toFun ω = ω := by
  funext i; simp [toFun, inv, id]


end Transformation

namespace Transformation

variable (τ : Transformation S E)

/-- The bijection `τ_*⁻¹ Λ ≃ Λ` induced by the spatial part `τ_*`. -/
def sitesEquiv (Λ : Finset S) : (Λ.map τ.sites.symm.toEmbedding : Finset S) ≃ Λ :=
  τ.sites.subtypeEquiv fun _ ↦ by simp [Finset.mem_map_equiv]

@[simp] lemma coe_sitesEquiv_apply (Λ : Finset S)
    (j : (Λ.map τ.sites.symm.toEmbedding : Finset S)) : (τ.sitesEquiv Λ j : S) = τ.sites j := rfl

@[simp] lemma coe_sitesEquiv_symm_apply (Λ : Finset S) (i : Λ) :
    ((τ.sitesEquiv Λ).symm i : S) = τ.sites.symm i := rfl

/-- Reindexing `τ_*⁻¹ Λ → Λ` along `τ_*` and applying the spins `τ_i` pushes the product measure
`λ^{τ_*⁻¹ Λ}` forward to `λ^Λ` when `τ` is `λ`-preserving. -/
lemma measurePreserving_spin_piCongrLeft {ν : Measure E} [SigmaFinite ν]
    (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) (Λ : Finset S) :
    MeasurePreserving
      ((fun ζ : Λ → E ↦ fun i : Λ ↦ τ.spin i (ζ i)) ∘
        MeasurableEquiv.piCongrLeft (fun _ : Λ ↦ E) (τ.sitesEquiv Λ))
      (Measure.pi fun _ : (Λ.map τ.sites.symm.toEmbedding : Finset S) ↦ ν)
      (Measure.pi fun _ : Λ ↦ ν) :=
  (measurePreserving_pi (fun _ : Λ ↦ ν) (fun _ ↦ ν) fun i ↦ hτ i).comp
    (measurePreserving_piCongrLeft (fun _ : Λ ↦ ν) (τ.sitesEquiv Λ))

/-- `τ` intertwines the juxtaposition maps: `τ ∘ juxt_{τ_*⁻¹ Λ}(τ⁻¹ ω) = juxt_Λ(ω) ∘ g`, where
`g` reindexes along `τ_*` and applies the spins `τ_i`. -/
lemma toFun_comp_juxt (Λ : Finset S) (ω : S → E) :
    τ.toFun ∘ juxt ((Λ.map τ.sites.symm.toEmbedding : Finset S) : Set S) (τ.inv.toFun ω) =
      juxt (Λ : Set S) ω ∘ (fun ζ : Λ → E ↦ fun i : Λ ↦ τ.spin i (ζ i)) ∘
        MeasurableEquiv.piCongrLeft (fun _ : Λ ↦ E) (τ.sitesEquiv Λ) := by
  funext ζ i
  simp only [Function.comp_apply, toFun]
  by_cases hi : i ∈ Λ
  · have hi' : τ.sites.symm i ∈ Λ.map τ.sites.symm.toEmbedding := by
      simp [hi]
    rw [juxt_apply_of_mem (Finset.mem_coe.2 hi), juxt_apply_of_mem (Finset.mem_coe.2 hi')]
    have hij : (⟨i, hi⟩ : Λ) = τ.sitesEquiv Λ ⟨τ.sites.symm i, hi'⟩ := Subtype.ext (by simp)
    rw [hij, MeasurableEquiv.piCongrLeft_apply_apply]
    simp
  · have hi' : τ.sites.symm i ∉ Λ.map τ.sites.symm.toEmbedding := by
      simp [hi]
    rw [juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi),
      juxt_apply_of_not_mem (Finset.mem_coe.not.2 hi')]
    exact congrFun (τ.toFun_inv_toFun ω) i

end Transformation


namespace Transformation

variable (τ σ : Transformation S E)

@[ext] lemma ext {τ σ : Transformation S E} (h₁ : τ.sites = σ.sites) (h₂ : τ.spin = σ.spin) :
    τ = σ := by
  cases τ; cases σ; cases h₁; cases h₂; rfl

/-- Georgii §5.1: `T` is a group. -/
instance : Group (Transformation S E) where
  mul := comp
  one := id
  inv := inv
  mul_assoc τ σ ρ := ext rfl (funext fun _ ↦ rfl)
  one_mul τ := ext (Equiv.trans_refl _) (funext fun _ ↦ MeasurableEquiv.ext rfl)
  mul_one τ := ext (Equiv.refl_trans _) (funext fun _ ↦ MeasurableEquiv.ext rfl)
  inv_mul_cancel τ := by
    refine ext (Equiv.self_trans_symm _) (funext fun i ↦ ?_)
    change (τ.spin (τ.sites.symm.symm i)).trans (τ.spin (τ.sites i)).symm = MeasurableEquiv.refl E
    simp only [Equiv.symm_symm]
    exact MeasurableEquiv.self_trans_symm _

@[simp] lemma mul_def : τ * σ = τ.comp σ := rfl
@[simp] lemma one_def : (1 : Transformation S E) = id := rfl
@[simp] lemma inv_def : τ⁻¹ = τ.inv := rfl

/-- The action `τ • ω = τ ω` of `T` on configurations. -/
instance : MulAction (Transformation S E) (S → E) where
  smul τ ω := τ.toFun ω
  one_smul ω := id_toFun ω
  mul_smul τ σ ω := comp_toFun τ σ ω

@[simp] lemma smul_def (ω : S → E) : τ • ω = τ.toFun ω := rfl

/-- `toMeasurableEquiv` is the composite of Mathlib's `piCongrLeft` and `piCongrRight`. -/
lemma toMeasurableEquiv_eq_piCongr :
    τ.toMeasurableEquiv =
      (MeasurableEquiv.piCongrLeft (fun _ : S ↦ E) τ.sites).trans
        (MeasurableEquiv.piCongrRight τ.spin) := by
  refine MeasurableEquiv.ext (funext fun ω ↦ funext fun i ↦ ?_)
  obtain ⟨a, rfl⟩ := τ.sites.surjective i
  simp [MeasurableEquiv.trans_apply, MeasurableEquiv.piCongrRight,
    MeasurableEquiv.piCongrLeft_apply_apply]

end Transformation

/-! ### Pure spin transformations, Georgii (9.9) -/

namespace Transformation

variable {S E : Type*} [MeasurableSpace E] {τ : Transformation S E}

/-- **Georgii (9.9).** A transformation is a *pure spin transformation* if its spatial part is the
identity: `τ ω = (τ_i ω_i)_{i ∈ S}`. -/
def IsPureSpin (τ : Transformation S E) : Prop := τ.sites = Equiv.refl S

lemma IsPureSpin.toFun_apply (h : τ.IsPureSpin) (ω : S → E) (i : S) :
    τ.toFun ω i = τ.spin i (ω i) := by
  rw [Transformation.toFun, h]; rfl

lemma IsPureSpin.inv (h : τ.IsPureSpin) : τ.inv.IsPureSpin := by
  simp only [IsPureSpin, Transformation.inv] at h ⊢
  rw [h]; rfl

lemma IsPureSpin.inv_toFun_apply (h : τ.IsPureSpin) (ω : S → E) (i : S) :
    τ.inv.toFun ω i = (τ.spin i).symm (ω i) := by
  rw [h.inv.toFun_apply]
  simp only [Transformation.inv, IsPureSpin] at h ⊢
  rw [h]; rfl

/-- The iterates of a pure spin transformation act site-wise by the iterates of the spins. -/
lemma IsPureSpin.iterate_toFun_apply (h : τ.IsPureSpin) (k : ℕ) (ω : S → E) (i : S) :
    τ.toFun^[k] ω i = (τ.spin i)^[k] (ω i) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, h.toFun_apply]

end Transformation

namespace Transformation

variable {S E : Type*} [MeasurableSpace E] {τ σ : Transformation S E}

lemma IsPureSpin.one : (1 : Transformation S E).IsPureSpin := rfl

lemma IsPureSpin.mul (hτ : τ.IsPureSpin) (hσ : σ.IsPureSpin) : (τ * σ).IsPureSpin := by
  simp only [IsPureSpin] at hτ hσ ⊢
  change σ.sites.trans τ.sites = Equiv.refl S
  rw [hτ, hσ]
  rfl

/-- The spins of a product with a pure spin transformation compose site-wise. -/
lemma IsPureSpin.mul_spin_apply (hτ : τ.IsPureSpin) (σ : Transformation S E) (i : S) (x : E) :
    (τ * σ).spin i x = τ.spin i (σ.spin i x) := by
  have h : τ.sites.symm i = i := by rw [hτ]; rfl
  change (σ.spin (τ.sites.symm i)).trans (τ.spin i) x = _
  rw [h]
  rfl

lemma IsPureSpin.inv_spin_apply (hτ : τ.IsPureSpin) (i : S) (x : E) :
    τ⁻¹.spin i x = (τ.spin i).symm x := by
  have h : τ.sites i = i := by rw [hτ]; rfl
  change (τ.spin (τ.sites i)).symm x = _
  rw [h]

lemma IsPureSpin.pow (hτ : τ.IsPureSpin) (k : ℕ) : (τ ^ k).IsPureSpin := by
  induction k with
  | zero => exact IsPureSpin.one
  | succ k ih => rw [pow_succ]; exact ih.mul hτ

/-- The spins of `τ ^ k` are the iterates of the spins of the pure spin transformation `τ`. -/
lemma IsPureSpin.pow_spin_apply (hτ : τ.IsPureSpin) (k : ℕ) (i : S) (x : E) :
    (τ ^ k).spin i x = (τ.spin i)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [pow_succ, (hτ.pow k).mul_spin_apply, ih, Function.iterate_succ_apply]

end Transformation

/-! ### Transformations with measure-preserving spins preserve the product field -/

/-- A transformation whose spins preserve `λ` preserves the product field `λ^S`: Georgii's remark
in Examples (5.20)(2)–(3) that the boundary fields may be taken to be
`ν = (λ(E)⁻¹ λ)^S ∈ 𝓟_I(Ω, 𝓕)`. In particular the product field is invariant under every
periodic modification `τ_N`, whose spins are those of `τ`. -/
lemma Transformation.measurePreserving_infinitePi (τ : Transformation S E) {ν : Measure E}
    [IsProbabilityMeasure ν] (hτ : ∀ i, MeasurePreserving (τ.spin i) ν ν) :
    MeasurePreserving τ.toFun (Measure.infinitePi fun _ : S ↦ ν)
      (Measure.infinitePi fun _ : S ↦ ν) := by
  refine ⟨τ.measurable_toFun, ?_⟩
  have hfun : τ.toFun = (fun x (i : S) ↦ τ.spin i (x i)) ∘
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : S ↦ E) τ.sites) := by
    funext ω i
    obtain ⟨j, rfl⟩ := τ.sites.surjective i
    change τ.spin _ (ω (τ.sites.symm (τ.sites j)))
        = τ.spin _ ((MeasurableEquiv.piCongrLeft (fun _ : S ↦ E) τ.sites) ω (τ.sites j))
    rw [MeasurableEquiv.piCongrLeft_apply_apply, Equiv.symm_apply_apply]
  calc (Measure.infinitePi fun _ : S ↦ ν).map τ.toFun
      = ((Measure.infinitePi fun _ : S ↦ ν).map
          (MeasurableEquiv.piCongrLeft (fun _ : S ↦ E) τ.sites)).map
            fun x (i : S) ↦ τ.spin i (x i) := by
        rw [Measure.map_map (measurable_pi_lambda (fun x (i : S) ↦ τ.spin i (x i))
            fun i ↦ (τ.spin i).measurable.comp (measurable_pi_apply i))
          (MeasurableEquiv.piCongrLeft (fun _ : S ↦ E) τ.sites).measurable, ← hfun]
    _ = (Measure.infinitePi fun _ : S ↦ ν).map fun x (i : S) ↦ τ.spin i (x i) := by
        rw [Measure.infinitePi_map_piCongrLeft (μ := fun _ : S ↦ ν) τ.sites]
    _ = Measure.infinitePi fun i : S ↦ ν.map (τ.spin i) :=
        Measure.infinitePi_map_pi (fun _ ↦ ν) fun i ↦ (τ.spin i).measurable
    _ = Measure.infinitePi fun _ : S ↦ ν := by
        congr 1
        funext i
        exact (hτ i).map_eq

/-! ### The shift (Georgii (5.2)(1))

Georgii's shift is stated on `ℤ^d`, but nothing in it uses more than the additive group structure
of the site set: `Equiv.addRight` needs only `[AddGroup S]`, and `Transformation S E` is already
generic in `S`. It is therefore defined here for an arbitrary additive group of sites, `ℤ^d` being
the instance Georgii uses. -/

variable {S E : Type*} [MeasurableSpace E] [AddGroup S]

variable (E) in
/-- **Georgii (5.2)(1).** The shift `θ_j : ω ↦ (ω_{i - j})_i` on an additive group of sites. -/
def shift (j : S) : Transformation S E where
  sites := Equiv.addRight j
  spin _ := MeasurableEquiv.refl E

@[simp] lemma shift_toFun_apply (j : S) (ω : S → E) (i : S) :
    (shift E j).toFun ω i = ω (i - j) := by
  simp [shift, Transformation.toFun, sub_eq_add_neg]

@[simp] lemma shift_inv_toFun_apply (j : S) (ω : S → E) (i : S) :
    (shift E j).inv.toFun ω i = ω (i + j) := by
  simp [shift, Transformation.inv, Transformation.toFun]

open MeasureTheory in
/-- The shift `θ_j` preserves every single-spin measure (Georgii, remark after (5.9)). -/
lemma measurePreserving_shift_spin (ν : Measure E) (j i : S) :
    MeasurePreserving ((shift E j).spin i) ν ν :=
  MeasurePreserving.id ν

/-- The inverse of the shift `θ_j` is `θ_{-j}`. -/
lemma shift_neg_toFun_eq {S : Type*} [AddGroup S] (j : S) :
    (shift E (-j)).toFun = (shift E j).inv.toFun := by
  funext ω i
  simp [sub_neg_eq_add]
/-- `θ_{j + k} = θ_k ∘ θ_j`. -/
lemma shift_add_toFun_eq {S : Type*} [AddGroup S] (j k : S) :
    (shift E (j + k)).toFun = (shift E k).toFun ∘ (shift E j).toFun := by
  funext ω i
  simp [sub_add_eq_sub_sub_swap]
/-- The composition of two shifts: `θ_a ∘ θ_b = θ_{a + b}` (Georgii (5.2)(1)). -/
lemma shift_toFun_comp_shift_toFun {S : Type*} [AddCommGroup S] (a b : S) :
    (shift E a).toFun ∘ (shift E b).toFun = (shift E (a + b)).toFun := by
  funext ω i
  simp only [Function.comp_apply, shift_toFun_apply, sub_sub]
/-- `θ_i ∘ θ_j = θ_{i + j}` (Georgii (5.2)(1)), in the transformation group. -/
lemma shift_mul_shift {S : Type*} [AddCommGroup S] (i j : S) : shift E i * shift E j = shift E (i
    + j) := by
  refine Transformation.ext (Equiv.ext fun k ↦ ?_) rfl
  change k + j + i = k + (i + j)
  rw [add_assoc, add_comm j i]

/-! ### The spin flip of `Bool` -/

/-- The spin flip `b ↦ !b` of `Bool` as a measurable equivalence: the single-site spin flip of
Georgii (5.2)(2). -/
def boolNot : Bool ≃ᵐ Bool :=
  MeasurableEquiv.ofInvolutive not (fun b ↦ Bool.not_not b) Measurable.of_discrete

@[simp] lemma boolNot_apply (b : Bool) : boolNot b = !b := rfl

@[simp] lemma boolNot_symm_apply (b : Bool) : boolNot.symm b = !b := rfl

lemma boolNot_trans_boolNot : boolNot.trans boolNot = MeasurableEquiv.refl Bool :=
  MeasurableEquiv.ext (funext fun b ↦ Bool.not_not b)

/-! ### Site bijections (Georgii (5.2)(2)) -/

variable (E) in
/-- **Georgii (5.2)(2).** The transformation induced by a bijection of the site set: it acts on
configurations by `ω ↦ (ω_{e⁻¹ i})_i` and leaves the spins alone.  The reflections and lattice
rotations of Georgii's group `R` are of this form, and so is the shift
(`shift_eq_siteEquiv`). -/
def siteEquiv (e : S ≃ S) : Transformation S E where
  sites := e
  spin _ := MeasurableEquiv.refl E

omit [AddGroup S] in
@[simp] lemma siteEquiv_toFun_apply (e : S ≃ S) (ω : S → E) (i : S) :
    (siteEquiv E e).toFun ω i = ω (e.symm i) := rfl

omit [AddGroup S] in
@[simp] lemma siteEquiv_sites (e : S ≃ S) : (siteEquiv E e).sites = e := rfl

omit [AddGroup S] in
lemma siteEquiv_comp (e f : S ≃ S) :
    (siteEquiv E e).comp (siteEquiv E f) = siteEquiv E (f.trans e) := rfl

omit [AddGroup S] in
lemma shift_eq_siteEquiv [AddGroup S] (j : S) : shift E j = siteEquiv E (Equiv.addRight j) := rfl

omit [AddGroup S] in
/-- **Georgii, in the proof of (5.17)(2): a site automorphism conjugates shifts into shifts,**
`τ_e ∘ θ_j = θ_{e j} ∘ τ_e`.  This is what makes the shift group normal in `R ∘ Θ`. -/
lemma siteEquiv_comp_shift [AddGroup S] (e : S ≃+ S) (j : S) :
    (siteEquiv E (e : S ≃ S)).comp (shift E j)
      = (shift E (e j)).comp (siteEquiv E (e : S ≃ S)) := by
  refine Transformation.ext ?_ ?_
  · ext i
    change e (i + j) = e i + e j
    exact map_add e i j
  · rfl

end MeasureTheory.GibbsMeasure

end

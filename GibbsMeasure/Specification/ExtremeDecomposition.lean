/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.GibbsKernel
public import GibbsMeasure.Specification.PAKernel
public import GibbsMeasure.Specification.ChoquetLaw
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.Existence

/-!
# Georgii, Theorem (7.26): the extreme decomposition of Gibbs measures

For a specification `γ` on `S → E` (`S` countable, `E` standard Borel) with `G(γ) ≠ ∅`,
`ex G(γ) ≠ ∅` and every `μ ∈ G(γ)` is the barycentre `μ = ∫ ν w_μ(dν)` of a unique probability
weight `w_μ` on `Measure (S → E)` carried by `ex G(γ)`; the map `μ ↦ w_μ` is an affine bijection
from `G(γ)` onto these weights, induced by the `(G(γ), 𝓣)`-kernel `gibbsKernel γ ν₀`.

Every statement is the instance `P = G(γ)`, `𝒜 = 𝓣` of the abstract extreme decomposition of
`GibbsMeasure/Specification/PAKernel.lean` (namespace `IsPAKernel`), fed with Theorem (7.7)(a)
(`extremePoints_G_eq_inter_trivialOn`), the measurability of `G(γ)` (`measurableSet_G`) and
Proposition (7.25) (`isPAKernel_gibbsKernel`).
-/

@[expose] public section


open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [Countable S] [StandardBorelSpace E]
  (γ : Specification S E)

local notation3 (prettyPrint := false) "Ω" => (S → E)

/-! ### `G(γ)` is measurable and `ex G(γ) = G(γ) ∩ P_𝓣` -/

/-- `G(γ)` is cut out by the countable-core Gibbs property `IsGibbsCore`. -/
lemma G_eq_setOf_isGibbsCore : G γ = {μ : Measure Ω | IsGibbsCore γ μ} := by
  ext μ
  constructor
  · rintro ⟨hprob, hgibbs⟩
    exact isGibbsCore_of_isGibbsMeasure γ hgibbs
  · intro h
    exact ⟨⟨h.1⟩, isGibbsMeasure_of_isGibbsCore γ h⟩

/-- `G(γ)` is a measurable subset of `Measure (S → E)` (for the evaluation σ-algebra). -/
lemma measurableSet_G : MeasurableSet (G γ) := by
  rw [G_eq_setOf_isGibbsCore]
  exact measurableSet_isGibbsCore γ

omit [StandardBorelSpace E] in
/-- Georgii Theorem (7.7)(a) in the language of (7.22): `ex G(γ) = G(γ) ∩ P_𝓣`. -/
lemma extremePoints_G_eq_inter_trivialOn :
    (G γ).extremePoints ℝ≥0∞ = G γ ∩ trivialOn (@tailSigmaAlgebra S E _) := by
  ext μ
  constructor
  · intro h
    exact ⟨h.1, tailTrivial_of_mem_extremePoints_G h⟩
  · rintro ⟨hμG, htriv⟩
    exact mem_extremePoints_G_of_isTailTrivial hμG fun A hA ↦ htriv A hA

variable {γ}

/-- The Gibbs measure `hG.some` chosen from a nonempty `G(γ)` is a probability measure. -/
instance isProbabilityMeasure_nonempty_G_some (hG : (G γ).Nonempty) :
    IsProbabilityMeasure hG.some :=
  hG.some_mem.1

/-- Proposition (7.25) for the chosen Gibbs measure `hG.some`: `gibbsKernel γ hG.some` is a
`(G(γ), 𝓣)`-kernel. -/
lemma isPAKernel_gibbsKernel_some (hG : (G γ).Nonempty) :
    IsPAKernel (G γ) (@tailSigmaAlgebra S E _) (gibbsKernel γ hG.some) :=
  isPAKernel_gibbsKernel γ _ hG.some_mem

/-! ### Existence and uniqueness of the representing weight -/

/-- Georgii (7.26): `ex G(γ) ≠ ∅` as soon as `G(γ) ≠ ∅`. -/
theorem nonempty_extremePoints_G (hG : (G γ).Nonempty) :
    ((G γ).extremePoints ℝ≥0∞).Nonempty :=
  (isPAKernel_gibbsKernel_some hG).nonempty_extremePoints tailSigmaAlgebra_le_pi
    (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) hG

/-- **Georgii, Theorem (7.26)** (existence and uniqueness): every `μ ∈ G(γ)` is represented,
`μ = ∫ ν w(dν)`, by a unique probability weight `w` carried by `ex G(γ)`. -/
theorem exists_unique_weight_extremePoints (hG : (G γ).Nonempty) {μ : Measure Ω}
    (hμ : μ ∈ G γ) :
    ∃! w : Measure (Measure Ω), IsProbabilityMeasure w ∧
      w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ :=
  (isPAKernel_gibbsKernel_some hG).exists_unique_weight_extremePoints tailSigmaAlgebra_le_pi
    (fun _ hμ ↦ hμ.1) (measurableSet_G γ) (extremePoints_G_eq_inter_trivialOn γ) hμ

/-! ### Surjectivity: barycentres of weights on `G(γ)` are Gibbs measures -/

omit [Countable S] [StandardBorelSpace E] in
/-- The barycentre of a probability weight carried by `G(γ)` is a probability measure. -/
lemma isProbabilityMeasure_join_of_G_compl (w : Measure (Measure Ω)) [IsProbabilityMeasure w]
    (hw : w (G γ)ᶜ = 0) : IsProbabilityMeasure (Measure.join w) :=
  isProbabilityMeasure_join_of_ae w ((ae_iff.2 hw).mono fun _ hν ↦ hν.1)

omit [Countable S] [StandardBorelSpace E] in
/-- The barycentre `∫ ν w(dν)` of a probability weight carried by `G(γ)` lies in `G(γ)`:
`(∫ ν w(dν)) γ_Λ = ∫ ν γ_Λ w(dν) = ∫ ν w(dν)`. -/
theorem join_mem_G (w : Measure (Measure Ω)) [IsProbabilityMeasure w] (hw : w (G γ)ᶜ = 0) :
    Measure.join w ∈ G γ := by
  have hprob := isProbabilityMeasure_join_of_G_compl w hw
  refine ⟨hprob, ?_⟩
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have hγ : Measurable (γ Λ : Ω → Measure Ω) := γ.measurable_kernel_toMeasure Λ
  ext s hs
  have hs' : Measurable fun ω ↦ γ Λ ω s :=
    (Kernel.measurable_coe (γ Λ) hs).mono cylinderEvents_le_pi le_rfl
  rw [Measure.bind_apply hs hγ.aemeasurable, Measure.lintegral_join hs'.aemeasurable,
    Measure.join_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_iff.2 hw] with ν hν
  have := hν.1
  rw [← Measure.bind_apply hs hγ.aemeasurable,
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hν.2) Λ]

/-! ### The weight `w_μ` and the affine bijection `μ ↦ w_μ` -/

/-- The weight `w_μ` of Theorem (7.26): the law of `ω ↦ π(· | ω)` under `μ`, for the
`(G(γ), 𝓣)`-kernel `π = gibbsKernel γ hG.some`. -/
noncomputable def weightOf (hG : (G γ).Nonempty) (μ : Measure Ω) : Measure (Measure Ω) :=
  weight (gibbsKernel γ hG.some) μ

lemma weightOf_apply (hG : (G γ).Nonempty) (μ : Measure Ω) {M : Set (Measure Ω)}
    (hM : MeasurableSet M) : weightOf hG μ M = μ (gibbsKernel γ hG.some ⁻¹' M) :=
  weight_apply tailSigmaAlgebra_le_pi μ hM

instance isProbabilityMeasure_weightOf (hG : (G γ).Nonempty) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (weightOf hG μ) :=
  isProbabilityMeasure_weight tailSigmaAlgebra_le_pi μ

/-- `w_μ` is carried by `ex G(γ)`. -/
lemma weightOf_extremePoints_compl (hG : (G γ).Nonempty) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    weightOf hG μ ((G γ).extremePoints ℝ≥0∞)ᶜ = 0 :=
  (isPAKernel_gibbsKernel_some hG).weight_extremePoints_compl tailSigmaAlgebra_le_pi
    (fun _ hμ ↦ hμ.1) (measurableSet_G γ) (extremePoints_G_eq_inter_trivialOn γ) hμ

/-- `w_μ` represents `μ`: `∫ ν w_μ(dν) = μ`. -/
lemma join_weightOf (hG : (G γ).Nonempty) {μ : Measure Ω} (hμ : μ ∈ G γ) :
    Measure.join (weightOf hG μ) = μ :=
  haveI := hμ.1
  (isPAKernel_gibbsKernel_some hG).join_weight tailSigmaAlgebra_le_pi hμ

/-- Uniqueness: a weight carried by `ex G(γ)` representing `μ` is `w_μ`. -/
theorem eq_weightOf_of_join_eq (hG : (G γ).Nonempty) {μ : Measure Ω} {w : Measure (Measure Ω)}
    (hw : w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0) (hjoin : Measure.join w = μ) :
    w = weightOf hG μ :=
  (isPAKernel_gibbsKernel_some hG).eq_weight_of_join_eq' tailSigmaAlgebra_le_pi
    (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) hw hjoin

/-- `μ ↦ w_μ` inverts `w ↦ ∫ ν w(dν)` on weights carried by `ex G(γ)`. -/
theorem weightOf_join (hG : (G γ).Nonempty) (w : Measure (Measure Ω))
    (hw : w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0) : weightOf hG (Measure.join w) = w :=
  (isPAKernel_gibbsKernel_some hG).weight_join
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (extremePoints_G_eq_inter_trivialOn γ) w hw

/-- The weight of a Gibbs measure does not depend on the choice of the `(G(γ), 𝓣)`-kernel. -/
lemma weight_gibbsKernel_eq {ν₀ ν₁ : Measure Ω} (hν₀ : ν₀ ∈ G γ) (hν₁ : ν₁ ∈ G γ)
    {μ : Measure Ω} (hμ : μ ∈ G γ) :
    weight (gibbsKernel γ ν₀) μ = weight (gibbsKernel γ ν₁) μ := by
  have := hν₀.1
  have := hν₁.1
  have := hμ.1
  exact (isPAKernel_gibbsKernel γ ν₁ hν₁).eq_weight_of_join_eq tailSigmaAlgebra_le_pi
    (fun μ hμ ↦ hμ.1)
    (ae_iff.2 ((isPAKernel_gibbsKernel γ ν₀ hν₀).weight_compl_eq_zero tailSigmaAlgebra_le_pi
      (measurableSet_G γ) hμ))
    ((isPAKernel_gibbsKernel γ ν₀ hν₀).join_weight tailSigmaAlgebra_le_pi hμ)

/-- **Georgii, Theorem (7.26)** (bijection): `μ ↦ w_μ` is a bijection from `G(γ)` onto the
probability weights on `Measure (S → E)` carried by `ex G(γ)`, with inverse `w ↦ ∫ ν w(dν)`. -/
noncomputable def extremeDecomposition (hG : (G γ).Nonempty) :
    G γ ≃ {w : Measure (Measure Ω) //
      IsProbabilityMeasure w ∧ w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0} where
  toFun μ := ⟨weightOf hG μ, by
    have := μ.2.1
    exact ⟨inferInstance, weightOf_extremePoints_compl hG μ.2⟩⟩
  invFun w := ⟨Measure.join w.1, by
    have := w.2.1
    exact join_mem_G w.1
      (measure_mono_null (compl_subset_compl.2 extremePoints_subset) w.2.2)⟩
  left_inv μ := Subtype.ext (join_weightOf hG μ.2)
  right_inv w := Subtype.ext (weightOf_join hG w.1 w.2.2)

@[simp] lemma extremeDecomposition_apply_coe (hG : (G γ).Nonempty) (μ : G γ) :
    (extremeDecomposition hG μ : Measure (Measure Ω)) = weightOf hG μ := rfl

@[simp] lemma extremeDecomposition_symm_apply_coe (hG : (G γ).Nonempty)
    (w : {w : Measure (Measure Ω) // IsProbabilityMeasure w ∧ w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0}) :
    ((extremeDecomposition hG).symm w : Measure Ω) = Measure.join w.1 := rfl

/-- **Georgii, Theorem (7.26)** (affinity): `μ ↦ w_μ` is affine. -/
theorem weightOf_add_smul (hG : (G γ).Nonempty) (μ ν : Measure Ω) (a b : ℝ≥0∞) :
    weightOf hG (a • μ + b • ν) = a • weightOf hG μ + b • weightOf hG ν :=
  IsPAKernel.weight_add_smul tailSigmaAlgebra_le_pi μ ν a b

/-- **Georgii, Theorem (7.26)** (bijection, set form): `μ ↦ w_μ` maps `G(γ)` bijectively onto
the probability weights carried by `ex G(γ)`. -/
theorem bijOn_weightOf (hG : (G γ).Nonempty) :
    BijOn (weightOf hG) (G γ)
      {w : Measure (Measure Ω) | IsProbabilityMeasure w ∧ w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0} :=
  (isPAKernel_gibbsKernel_some hG).bijOn_weight
    tailSigmaAlgebra_le_pi (fun _ hμ ↦ hμ.1) (measurableSet_G γ)
    (extremePoints_G_eq_inter_trivialOn γ) fun w hw hw' ↦
      haveI := hw
      join_mem_G w (measure_mono_null (compl_subset_compl.2 extremePoints_subset) hw')

/-- **Georgii, Theorem (7.26)**, summary: if `G(γ) ≠ ∅` then `ex G(γ) ≠ ∅`; every `μ ∈ G(γ)` is
represented by a unique probability weight carried by `ex G(γ)`; `μ ↦ w_μ` is an affine bijection
from `G(γ)` onto these weights, and `w_μ` is the image of `μ` under `ω ↦ π(· | ω)`. -/
theorem extremeDecomposition_theorem (hG : (G γ).Nonempty) :
    ((G γ).extremePoints ℝ≥0∞).Nonempty ∧
    (∀ μ ∈ G γ, ∃! w : Measure (Measure Ω), IsProbabilityMeasure w ∧
      w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ) ∧
    BijOn (weightOf hG) (G γ)
      {w : Measure (Measure Ω) | IsProbabilityMeasure w ∧ w ((G γ).extremePoints ℝ≥0∞)ᶜ = 0} ∧
    (∀ (μ ν : Measure Ω) (a b : ℝ≥0∞),
      weightOf hG (a • μ + b • ν) = a • weightOf hG μ + b • weightOf hG ν) ∧
    ∀ μ : Measure Ω, weightOf hG μ = μ.map (gibbsKernel γ hG.some) :=
  ⟨nonempty_extremePoints_G hG, fun _ hμ ↦ exists_unique_weight_extremePoints hG hμ,
    bijOn_weightOf hG, weightOf_add_smul hG, fun _ ↦ rfl⟩

omit [Countable S] [StandardBorelSpace E] in
/-- `G(γ)` is convex: convex combinations of Gibbs measures are Gibbs measures. -/
lemma add_smul_mem_G {μ ν : Measure Ω} (hμ : μ ∈ G γ) (hν : ν ∈ G γ) {a b : ℝ≥0∞}
    (hab : a + b = 1) : a • μ + b • ν ∈ G γ := by
  have := hμ.1
  have := hν.1
  have hprob : IsProbabilityMeasure (a • μ + b • ν) := ⟨by simp [hab]⟩
  refine ⟨hprob, ?_⟩
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  rw [Measure.bind_add _ _ _ (γ.measurable_kernel_toMeasure Λ), Measure.bind_smul,
    Measure.bind_smul, (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hμ.2) Λ,
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hν.2) Λ]

end MeasureTheory.GibbsMeasure

end

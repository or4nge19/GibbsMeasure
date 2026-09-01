/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.GroupTheory.Foelner
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.UniformAverage
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Specification.Transformation

/-!
# Existence of invariant Gibbs measures by symmetrisation

Georgii Theorem (5.15) and Corollary (5.16): symmetrisation enlarges the symmetry group of a
Gibbs measure. Given two families of symmetries — Georgii's subgroups `I₀` and `I₁` of the
transformation group, with `τ₁ ∘ I₀ = I₀ ∘ τ₁` for all `τ₁ ∈ I₁` — a Gibbs measure invariant
under `I₀` is averaged over `I₁` into a Gibbs measure invariant under `I₁ ∘ I₀`, under either of
two hypotheses: (i) a left-invariant probability weight on `I₁` (for Georgii, the Haar measure of
a compact group with measurable evaluation map), or (ii) `I₁` abelian and `𝒢(γ)` compact in the
topology of local convergence. Corollary (5.16) is the case `I₀ = {id}`.

Georgii's proof of (ii) averages a Gibbs measure `ν` over larger and larger finite subsets of the
abelian group and passes to a cluster point. Where `GibbsMeasure/Specification/Average.lean`
averages the finite-volume Gibbs distributions `ν γ_Λ` over a finite family of **volumes**
(Georgii (5.18)), this file averages the **images** `τ(ν)` over a finite family of
transformations. Both are instances of the uniform average `uniformAverage m F = |F|⁻¹ ∑_{i ∈ F}
m i` of a finite family of measures, with its total-variation estimate
`|avg_F(A) - avg_{F'}(A)| ≤ |F ∆ F'| / |F|` for `|F| = |F'|`.

## Main results

* `MeasureTheory.mem_GP_finset_sum_smul` and `MeasureTheory.mem_GP_uniformAverage`: a finite
  convex combination of Gibbs measures is a Gibbs measure, generalising the binary
  `convexCombo_mem_GP` of `GibbsMeasure/Specification/Structure.lean`;
* `MeasureTheory.GibbsMeasure.map_transAverage`: `Φ b (avg_F ν) = avg_{b + F} ν` for a family of
  transformations indexed by an abelian group;
* `exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_transportLaw`:
  **Georgii Theorem (5.15)(ii)** for an abelian group acting by symmetries, at Georgii's own
  compactness hypothesis — `𝒢_{I₀}(γ)` compact, not `𝒢(γ)`: the averaging carries the
  `I₀`-invariance of the starting measure through to the cluster point;
  `exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving` is the case
  where `𝒢(γ)` itself is compact;
* `exists_mem_GP_and_forall_measurePreserving_of_commute_mod_of_measurePreserving`: **Georgii
  Theorem (5.15)(ii)** for two subgroups `I₀`, `I₁` of the transformation group at Georgii's
  hypotheses — `I₁` commutative modulo `I₀`, `𝒢_{I₀}(γ)` compact — with the group form
  `..._sup_of_commute_mod_of_measurePreserving` (`𝒢_{I₁∘I₀}(γ) ≠ ∅`) and the abelian special
  case `exists_mem_GP_and_forall_measurePreserving_of_commute_of_measurePreserving`;
* `MeasureTheory.GibbsMeasure.exists_mem_GP_and_forall_measurePreserving_of_isCompact` and
  `exists_mem_GP_and_forall_measurePreserving_of_commute`: **Georgii Corollary (5.16)** — the
  `I₀ = {id}` case — for a group action and for an abelian subgroup of transformations;
* `MeasureTheory.GibbsMeasure.exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq`,
  **Georgii Theorem (5.15)(i)** at the hypothesis its proof uses — a left-invariant probability
  measure on the acting group — with the `MeasurePreserving` form
  `exists_mem_GP_and_forall_measurePreserving_of_invariantWeight_of_measurePreserving` and the
  compact-group case
  `exists_mem_GP_and_forall_measurePreserving_of_compactGroup_of_measurePreserving`, where Haar
  measure supplies the weight; their `I₀ = {id}` cases
  (`..._of_invariantWeight`, `..._of_compactGroup`) are Corollary (5.16) for a compact group.
  None of these needs compactness of `𝒢(γ)`.

The Følner sets driving branch (ii) come from `GibbsMeasure/Mathlib/GroupTheory/Foelner.lean`.

Branch (ii) is proved at Georgii's hypotheses: commutativity of `I₁` modulo `I₀`
(`τ₁ ∘ τ₂ = τ₂ ∘ τ₁ ∘ τ₀` for some `τ₀ ∈ I₀`) and compactness of `𝒢_{I₀}(γ)` rather than of
`𝒢(γ)`. The passage from the abelian form — the case `τ₀ = id`, the one all of Georgii's
examples (5.17) use — is Georgii's finite-intersection argument: for a finite `F ⊆ I₁` the group
`[I₀ ∪ F]` is normalised by every element of `I₁`, so its generators can be added one at a time
by the cyclic case, and `𝒢_{I₀ ∪ F}(γ)` is a non-empty closed subset of the compact
`𝒢_{I₀}(γ)`; compactness then produces a point common to all of them.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Pointwise symmDiff Topology

noncomputable section

namespace MeasureTheory

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-! ### Finite convex combinations of Gibbs measures -/

variable {S E : Type*} [MeasurableSpace E]

open MeasureTheory.GibbsMeasure in
/-- **Finite convex combination of Gibbs measures.** Any finite linear combination of Gibbs
measures which is again a probability measure — in particular any convex combination, where the
weights `w` sum to `1` — is a Gibbs measure. This generalises the binary `convexCombo_mem_GP`
to a finite family. -/
lemma mem_GP_finset_sum_smul {γ : Specification S E} {m : ι → ProbabilityMeasure (S → E)}
    (hm : ∀ i, m i ∈ GP (S := S) (E := E) γ) {w : ι → ℝ≥0∞} {F : Finset ι}
    {μ : ProbabilityMeasure (S → E)}
    (hμ : (μ : Measure (S → E)) = ∑ i ∈ F, w i • (m i : Measure (S → E))) :
    μ ∈ GP (S := S) (E := E) γ := by
  have hfix : ∀ Λ : Finset S, (μ : Measure (S → E)).bind (γ Λ) = (μ : Measure (S → E)) := by
    intro Λ
    have hmi : ∀ i, (m i : Measure (S → E)).bind (γ Λ) = (m i : Measure (S → E)) := fun i ↦ by
      have : γ.IsGibbsMeasure (m i : Measure (S → E)) := hm i
      exact (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).1 this Λ
    rw [hμ, Measure.bind_finset_sum _ _ _ (γ.measurable_kernel_toMeasure Λ)]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Measure.bind_smul, hmi i]
  have : γ.IsGibbsMeasure (μ : Measure (S → E)) :=
    (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)).2 hfix
  exact this

open MeasureTheory.GibbsMeasure in
/-- **Finite convex combination of Gibbs measures**, with equal weights. -/
lemma mem_GP_uniformAverage {γ : Specification S E} {m : ι → ProbabilityMeasure (S → E)}
    (hm : ∀ i, m i ∈ GP (S := S) (E := E) γ) {F : Finset ι} {μ : ProbabilityMeasure (S → E)}
    (hμ : (μ : Measure (S → E)) = uniformAverage (fun i ↦ (m i : Measure (S → E))) F) :
    μ ∈ GP (S := S) (E := E) γ :=
  mem_GP_finset_sum_smul hm (w := fun _ ↦ (F.card : ℝ≥0∞)⁻¹)
    (by rw [hμ, uniformAverage, Finset.smul_sum])

/-- Pushing a uniform average forward along a measurable map averages the push-forwards. -/
lemma map_uniformAverage {β : Type*} [MeasurableSpace β] (m : ι → Measure Ω) (F : Finset ι)
    {f : Ω → β} (hf : Measurable f) :
    (uniformAverage m F).map f = uniformAverage (fun i ↦ (m i).map f) F := by
  rw [uniformAverage, uniformAverage, Measure.map_smul, Measure.map_finset_sum hf.aemeasurable]

end MeasureTheory

namespace MeasureTheory.GibbsMeasure

variable {S E A : Type*} [MeasurableSpace E]

/-! ### Averages over a family of transformations -/

/-- The averaging device of Georgii's proof of Theorem (5.15)(ii): the average
`|F|⁻¹ ∑_{a ∈ F} Φ a (ν)` of the images of a random field `ν` under a finite family `F` of
transformations. -/
def transAverage (Φ : A → Transformation S E) (ν : Measure (S → E)) (F : Finset A) :
    Measure (S → E) :=
  uniformAverage (fun a ↦ ν.map (Φ a).toFun) F

lemma isProbabilityMeasure_transAverage (Φ : A → Transformation S E) (ν : Measure (S → E))
    [IsProbabilityMeasure ν] {F : Finset A} (hF : F.Nonempty) :
    IsProbabilityMeasure (transAverage Φ ν F) :=
  isProbabilityMeasure_uniformAverage _
    (fun a ↦ Measure.isProbabilityMeasure_map (Φ a).measurable_toFun.aemeasurable) hF

/-- In Georgii's proof of Theorem (5.15)(ii), translating the index set by `b` is the same as
pushing the average forward by `Φ b`.

The hypothesis is the weakest one the computation uses: the composition law is needed only after
transporting `ν`, not as an identity of transformations.  That is what makes Georgii's case (ii)
available, where `Φ` is a homomorphism only *modulo* the subgroup `I₀` and the law is recovered
because `ν` is `I₀`-invariant (`transportLaw_of_measurePreserving`). -/
lemma map_transAverage_of_transportLaw [AddCommGroup A] [DecidableEq A]
    {Φ : A → Transformation S E} {ν : Measure (S → E)}
    (hΦν : ∀ x y, (ν.map (Φ y).toFun).map (Φ x).toFun = ν.map (Φ (x + y)).toFun)
    (F : Finset A) (b : A) :
    (transAverage Φ ν F).map (Φ b).toFun = transAverage Φ ν (b +ᵥ F) := by
  have hterm : ∀ a : A, (ν.map (Φ a).toFun).map (Φ b).toFun = ν.map (Φ (b + a)).toFun :=
    fun a ↦ hΦν b a
  rw [transAverage, transAverage, uniformAverage, uniformAverage, Measure.map_smul,
    Measure.map_finset_sum (Φ b).measurable_toFun.aemeasurable, Finset.card_vadd_finset]
  congr 1
  rw [show b +ᵥ F = F.image (b + ·) from rfl,
    Finset.sum_image fun x _ y _ h ↦ add_left_cancel h]
  exact Finset.sum_congr rfl fun a _ ↦ hterm a

/-- **Georgii's transport law from a homomorphism modulo `I₀`.**  If `Φ x ∘ Φ y` differs from
`Φ (x + y)` by a transformation `T₀ i` preserving `ν` — Georgii's `τ₁ ∘ τ₂ = τ₂ ∘ τ₁ ∘ τ₀` with
`τ₀ ∈ I₀` and `ν` an `I₀`-invariant Gibbs measure — then the composition law holds after
transporting `ν`, which is all the averaging argument uses. -/
lemma transportLaw_of_measurePreserving [AddCommGroup A] {Φ : A → Transformation S E}
    {ι₀ : Type*} {T₀ : ι₀ → Transformation S E} {ν : Measure (S → E)}
    (hΦ : ∀ x y, ∃ i : ι₀,
      (Φ x).toFun ∘ (Φ y).toFun = (Φ (x + y)).toFun ∘ (T₀ i).toFun)
    (hν₀ : ∀ i, MeasurePreserving (T₀ i).toFun ν ν) (x y : A) :
    (ν.map (Φ y).toFun).map (Φ x).toFun = ν.map (Φ (x + y)).toFun := by
  obtain ⟨i, hi⟩ := hΦ x y
  rw [Measure.map_map (Φ x).measurable_toFun (Φ y).measurable_toFun, hi,
    ← Measure.map_map (Φ (x + y)).measurable_toFun (T₀ i).measurable_toFun, (hν₀ i).map_eq]

/-- `map_transAverage_of_transportLaw` for a genuine homomorphism `Φ (x + y) = Φ x ∘ Φ y`. -/
lemma map_transAverage [AddCommGroup A] [DecidableEq A] {Φ : A → Transformation S E}
    (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y) (ν : Measure (S → E)) (F : Finset A) (b : A) :
    (transAverage Φ ν F).map (Φ b).toFun = transAverage Φ ν (b +ᵥ F) :=
  map_transAverage_of_transportLaw
    (fun x y ↦ by
      rw [Measure.map_map (Φ x).measurable_toFun (Φ y).measurable_toFun, hΦ]
      congr 1) F b

/-! ### The symmetries of a specification are closed under the group operations

Georgii §5.1: the symmetries of `γ` form a subgroup of the transformation group. Closure under
composition is `Specification.IsInvariant.comp` in
`GibbsMeasure/Specification/Transformation.lean`; here the multiplicative form and closure under
integer powers, which the single-generator step of Theorem (5.15)(ii) applies to the cyclic
group `{τ ^ k : k ∈ ℤ}` generated by one symmetry. -/

/-! ### Invariance under a group of transformations, and compactness of `𝒢_I(γ)`

Georgii's set `𝒢_I(γ) = 𝒢(γ) ∩ 𝒫_I(Ω, 𝓕)` of (5.13) is closed in the topology of local
convergence (`isClosed_setOf_mem_GP_and_measurePreserving`, in
`GibbsMeasure/Specification/InvariantFields.lean`). What Georgii's proof of (5.15)(ii) needs on
top of that is: invariance under a set of transformations is invariance under the group it
generates, and `𝒢_J(γ)` is compact as soon as `𝒢_I(γ)` is for some `I ⊆ J` — in particular as
soon as `𝒢(γ)` is. -/

/-- **Georgii, remark after (5.12): `𝒫_I(Ω, 𝓕) = 𝒫_{[I]}(Ω, 𝓕)`.** The transformations
preserving a fixed measure form a subgroup of the transformation group, so a measure preserved by
every transformation in a set `I` is preserved by every element of the group `[I]` generated
by `I`. -/
theorem measurePreserving_of_mem_closure {μ : Measure (S → E)} {I : Set (Transformation S E)}
    (h : ∀ σ ∈ I, MeasurePreserving σ.toFun μ μ) {τ : Transformation S E}
    (hτ : τ ∈ Subgroup.closure I) : MeasurePreserving τ.toFun μ μ := by
  induction hτ using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one =>
    have h1 : (1 : Transformation S E).toFun = _root_.id := funext Transformation.id_toFun
    rw [h1]
    exact MeasurePreserving.id μ
  | mul x y _ _ ihx ihy =>
    have hxy : (x * y).toFun = x.toFun ∘ y.toFun := funext (Transformation.comp_toFun x y)
    rw [hxy]
    exact ihx.comp ihy
  | inv x _ ihx =>
    refine ⟨x⁻¹.measurable_toFun, ?_⟩
    have hcomp : x⁻¹.toFun ∘ x.toFun = _root_.id :=
      funext fun ω ↦ Transformation.inv_toFun_toFun x ω
    calc μ.map x⁻¹.toFun = (μ.map x.toFun).map x⁻¹.toFun := by rw [ihx.map_eq]
      _ = μ := by
          rw [Measure.map_map x⁻¹.measurable_toFun x.measurable_toFun, hcomp, Measure.map_id]

/-- `𝒢_{[X]}(γ) = 𝒢_X(γ)`: by Georgii's remark after (5.12), invariance under a set of
transformations is invariance under the group it generates, so the set of Georgii (5.13) is
unchanged when `X` is saturated to the subgroup `[X]`. -/
lemma setOf_mem_GP_and_forall_measurePreserving_closure {γ : Specification S E}
    (X : Set (Transformation S E)) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ σ ∈ (Subgroup.closure X : Set (Transformation S E)),
          MeasurePreserving σ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} =
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ σ ∈ X, MeasurePreserving σ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  ext μ
  simp only [Set.mem_ofPred_eq]
  exact and_congr_right fun _ ↦
    ⟨fun h σ hσ ↦ h σ (Subgroup.subset_closure hσ),
     fun h σ hσ ↦ measurePreserving_of_mem_closure h hσ⟩

/-- The invariance of Georgii (5.13) under a family of transformations, written as invariance
under the range of that family. -/
lemma setOf_mem_GP_and_forall_measurePreserving_range {γ : Specification S E} {ι : Type*}
    (T : ι → Transformation S E) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ i, MeasurePreserving (T i).toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} =
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ τ ∈ Set.range T,
          MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  ext μ
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range]

/-- **`𝒢_J(γ)` is compact as soon as `𝒢_I(γ)` is**, for `I ⊆ J`: it is the intersection of
`𝒢_I(γ)` with the closed set `𝒫_J(Ω, 𝓕)` of Georgii's remark after (5.12). -/
theorem isCompact_setOf_mem_GP_and_forall_measurePreserving_of_subset {γ : Specification S E}
    {I J : Set (Transformation S E)} (hIJ : I ⊆ J)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure}) :
    IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ J, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  have hset : {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ J, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} =
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} ∩
      {μ : WithLocalConvergence S E |
        ∀ τ ∈ J, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
    ext μ
    exact ⟨fun h ↦ ⟨⟨h.1, fun τ hτ ↦ h.2 τ (hIJ hτ)⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
  rw [hset]
  exact hcpt.inter_right (isClosed_setOf_forall_measurePreserving J)

/-- **`𝒢_I(γ)` is compact as soon as `𝒢(γ)` is** (Georgii (5.13) and the remark after (5.12)). -/
theorem isCompact_setOf_mem_GP_and_forall_measurePreserving {γ : Specification S E}
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (I : Set (Transformation S E)) :
    IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
  rw [Set.ofPred_and]
  exact hcpt.inter_right (isClosed_setOf_forall_measurePreserving I)

/-! ### Georgii Theorem (5.15)(ii) and Corollary (5.16) -/

/-- **Georgii Theorem (5.15)(ii)**, family form. Let `Φ` turn an abelian group `A` into
symmetries of the specification `γ`, and let `T₀` be a second family of transformations —
Georgii's subgroup `I₀` — such that each `T₀ i` commutes with each `Φ x` modulo the family:
`T₀ i ∘ Φ x = Φ x ∘ T₀ i'` for some index `i'` (Georgii's normality hypothesis
`τ₁ ∘ I₀ = I₀ ∘ τ₁`). If the set `𝒢_{I₀}(γ)` of `T₀`-invariant Gibbs measures is compact in the
topology of local convergence and contains `ν`, then it contains a measure invariant under every
`T₀ i` **and** every `Φ x` — in Georgii's notation, `𝒢_{I₀}(γ) ≠ ∅` implies `𝒢_{I₁∘I₀}(γ) ≠ ∅`.

The proof is Georgii's Markov–Kakutani argument: average `ν` over the Følner sets of `A` supplied
by `AddCommGroup.exists_finset_transDist_le` and take a cluster point. The averages stay
`T₀`-invariant because `ν` is and the two families commute, so the cluster point inherits this
invariance exactly, while the `Φ`-invariance comes from the Følner symmetric-difference estimate.
Invariance of `γ` under `T₀` is not needed. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_transportLaw
    [AddCommGroup A] {ι₀ : Type*} {γ : Specification S E} {Φ : A → Transformation S E}
    {T₀ : ι₀ → Transformation S E} {ν : ProbabilityMeasure (S → E)}
    (hΦ : ∀ x y, ((ν : Measure (S → E)).map (Φ y).toFun).map (Φ x).toFun
      = (ν : Measure (S → E)).map (Φ (x + y)).toFun)
    (hcomm : ∀ (i : ι₀) (x : A), ∃ i',
      (T₀ i).toFun ∘ (Φ x).toFun = (Φ x).toFun ∘ (T₀ i').toFun)
    (hγ : ∀ x, Specification.IsInvariant (Φ x) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ i : ι₀, MeasurePreserving (T₀ i).toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ i, MeasurePreserving (T₀ i).toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ i, MeasurePreserving (T₀ i).toFun (μ : Measure (S → E)) μ) ∧
        ∀ x : A, MeasurePreserving (Φ x).toFun (μ : Measure (S → E)) μ := by
  classical
  -- Følner sets, one for each finite set of directions and each accuracy
  have hchoice : ∀ p : Finset A × ℕ, ∃ F : Finset A, F.Nonempty ∧
      ∀ g ∈ p.1, (F.transDist g : ℝ) ≤ (1 / ((p.2 : ℝ) + 1)) * F.card := by
    intro p
    obtain ⟨F, h1, -, h2⟩ :=
      AddCommGroup.exists_finset_transDist_le p.1 (1 / ((p.2 : ℝ) + 1)) (by positivity)
    exact ⟨F, h1, h2⟩
  choose Fs hFsne hFsbd using hchoice
  have hprobm : ∀ a : A, IsProbabilityMeasure ((ν : Measure (S → E)).map (Φ a).toFun) :=
    fun a ↦ Measure.isProbabilityMeasure_map (Φ a).measurable_toFun.aemeasurable
  have hprob : ∀ p, IsProbabilityMeasure (transAverage Φ (ν : Measure (S → E)) (Fs p)) :=
    fun p ↦ isProbabilityMeasure_transAverage Φ _ (hFsne p)
  set μs : Finset A × ℕ → ProbabilityMeasure (S → E) :=
    fun p ↦ ⟨transAverage Φ (ν : Measure (S → E)) (Fs p), hprob p⟩ with hμsdef
  have hμsc : ∀ p, (μs p : Measure (S → E)) = transAverage Φ (ν : Measure (S → E)) (Fs p) :=
    fun _ ↦ rfl
  -- each average is a Gibbs measure, by (5.10) and convexity
  have hmapGP : ∀ a : A, ν.map (Φ a).measurable_toFun.aemeasurable ∈ GP (S := S) (E := E) γ :=
    fun a ↦ (hγ a).map_mem_GP hν
  have hμsGP : ∀ p, μs p ∈ GP (S := S) (E := E) γ := by
    intro p
    refine mem_GP_uniformAverage (m := fun a ↦ ν.map (Φ a).measurable_toFun.aemeasurable)
      hmapGP (F := Fs p) ?_
    rw [hμsc p, transAverage]
    simp [ProbabilityMeasure.toMeasure_map]
  -- each average is invariant under the family `T₀`, because `ν` is and the families commute
  have hterm₀ : ∀ (a : A) (i : ι₀),
      ((ν : Measure (S → E)).map (Φ a).toFun).map (T₀ i).toFun
        = (ν : Measure (S → E)).map (Φ a).toFun := by
    intro a i
    obtain ⟨i', hi'⟩ := hcomm i a
    rw [Measure.map_map (T₀ i).measurable_toFun (Φ a).measurable_toFun, hi',
      ← Measure.map_map (Φ a).measurable_toFun (T₀ i').measurable_toFun, (hν₀ i').map_eq]
  have hμs₀ : ∀ p i, (μs p : Measure (S → E)).map (T₀ i).toFun = μs p := by
    intro p i
    rw [hμsc p, transAverage, map_uniformAverage _ _ (T₀ i).measurable_toFun]
    exact congrArg (fun m ↦ uniformAverage m (Fs p)) (funext fun a ↦ hterm₀ a i)
  -- `𝒢_{T₀}(γ)` is compact, so the net of averages — all of them `T₀`-invariant — has a cluster
  -- point in it, and that cluster point is `T₀`-invariant for free
  have hle : map (fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E))
      atTop ≤ 𝓟 {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ i : ι₀, MeasurePreserving (T₀ i).toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} :=
    le_principal_iff.2 (mem_map.2 (Eventually.of_forall fun p ↦
      ⟨hμsGP p, fun i ↦ ⟨(T₀ i).measurable_toFun, hμs₀ p i⟩⟩))
  obtain ⟨μ, hμmem, hμcl⟩ := hcpt.exists_clusterPt hle
  have hMCP : MapClusterPt μ (atTop : Filter (Finset A × ℕ))
      fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E) := hμcl
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hMCP
  refine ⟨μ.toMeasure, hμmem.1, hμmem.2, fun x ↦ ⟨(Φ x).measurable_toFun, ?_⟩⟩
  -- `Φ`-invariance of the cluster point, by the Følner estimate
  · have hmap : IsProbabilityMeasure ((μ.toMeasure : Measure (S → E)).map (Φ x).toFun) := by
      constructor
      rw [Measure.map_apply (Φ x).measurable_toFun .univ, preimage_univ, measure_univ]
    refine separatesOn_localEvents hmap inferInstance fun B hB ↦ ?_
    have hBm : MeasurableSet B := .of_mem_measurableCylinders hB
    rw [Measure.map_apply (Φ x).measurable_toFun hBm]
    have h1 : Tendsto (fun p ↦ ((μs p : Measure (S → E)) B).toReal) U
        (𝓝 (((μ.toMeasure : Measure (S → E)) B).toReal)) :=
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
        (tendsto_withLocalConvergence_iff.1 hU B hB)
    have h2 : Tendsto (fun p ↦ ((μs p : Measure (S → E)) ((Φ x).toFun ⁻¹' B)).toReal) U
        (𝓝 (((μ.toMeasure : Measure (S → E)) ((Φ x).toFun ⁻¹' B)).toReal)) :=
      (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
        (tendsto_withLocalConvergence_iff.1 hU _ ((Φ x).preimage_mem_localEvents hB))
    -- `μ_p(Φx⁻¹ B)` is the average over the translated index set, by `map_transAverage`
    have hn : ∀ p, ((μs p : Measure (S → E)) ((Φ x).toFun ⁻¹' B)).toReal =
        (transAverage Φ (ν : Measure (S → E)) (x +ᵥ Fs p)).real B := by
      intro p
      rw [measureReal_def, ← map_transAverage_of_transportLaw hΦ,
        Measure.map_apply (Φ x).measurable_toFun hBm,
        hμsc p]
    -- the difference tends to `0` by the Følner estimate
    have hfst : Tendsto (Prod.fst : Finset A × ℕ → Finset A) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_fst
    have hsnd : Tendsto (Prod.snd : Finset A × ℕ → ℕ) atTop atTop := by
      rw [← Filter.prod_atTop_atTop_eq]; exact tendsto_snd
    have hev : ∀ᶠ p : Finset A × ℕ in atTop, x ∈ p.1 :=
      hfst.eventually ((eventually_ge_atTop ({x} : Finset A)).mono fun s hs ↦
        hs (Finset.mem_singleton_self x))
    have hg : Tendsto (fun p : Finset A × ℕ ↦ 1 / ((p.2 : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd
    have hdiff : Tendsto (fun p ↦ ((μs p : Measure (S → E)) ((Φ x).toFun ⁻¹' B)).toReal -
        ((μs p : Measure (S → E)) B).toReal) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [hev] with p hp
      rw [Real.norm_eq_abs, hn p, ← measureReal_def, hμsc p]
      have hest := abs_uniformAverage_real_sub_le_of_card_eq
        (m := fun a ↦ (ν : Measure (S → E)).map (Φ a).toFun) hprobm
        (F := x +ᵥ Fs p) (F' := Fs p) (hFsne p).vadd_finset (Finset.card_vadd_finset _ _) B
      refine hest.trans ?_
      rw [Finset.card_vadd_finset]
      have hc : (0 : ℝ) < (Fs p).card := by exact_mod_cast Finset.card_pos.2 (hFsne p)
      rw [div_le_iff₀ hc]
      exact hFsbd p x hp
    have h3 := tendsto_nhds_unique (h2.sub h1) (hdiff.mono_left hUle)
    rw [sub_eq_zero] at h3
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h3

/-- **Georgii Theorem (5.15)(ii)**, two-subgroup form for a genuine homomorphism `Φ`: the
specialisation of `exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_transportLaw` in
which `Φ (x + y) = Φ x ∘ Φ y` holds on the nose. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving
    [AddCommGroup A] {ι₀ : Type*} {γ : Specification S E} {Φ : A → Transformation S E}
    {T₀ : ι₀ → Transformation S E} (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y)
    (hcomm : ∀ (i : ι₀) (x : A), ∃ i',
      (T₀ i).toFun ∘ (Φ x).toFun = (Φ x).toFun ∘ (T₀ i').toFun)
    (hγ : ∀ x, Specification.IsInvariant (Φ x) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ i, MeasurePreserving (T₀ i).toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ i, MeasurePreserving (T₀ i).toFun (μ : Measure (S → E)) μ) ∧
        ∀ x : A, MeasurePreserving (Φ x).toFun (μ : Measure (S → E)) μ :=
  exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_transportLaw
    (fun x y ↦ by
      rw [Measure.map_map (Φ x).measurable_toFun (Φ y).measurable_toFun, hΦ]
      congr 1)
    hcomm hγ (by
      have h := isCompact_setOf_mem_GP_and_forall_measurePreserving_of_subset
        (γ := γ) (I := (∅ : Set (Transformation S E))) (J := Set.range T₀)
        (Set.empty_subset _) (by simpa using hcpt)
      simpa [Set.forall_mem_range] using h)
    hν hν₀

/-- **The finite-intersection step of Georgii's proof of Theorem (5.15)(ii).**  If `𝒢_I(γ)` is
compact in the topology of local convergence and `𝒢_{I ∪ F}(γ)` is non-empty for every *finite*
`F ⊆ J`, then `𝒢_{I ∪ J}(γ)` is non-empty: the sets `𝒢_{I ∪ {τ}}(γ)`, `τ ∈ J`, are closed subsets
of the compact `𝒢_I(γ)` with the finite intersection property. -/
theorem nonempty_setOf_mem_GP_and_forall_measurePreserving_of_forall_finset
    {γ : Specification S E} {I J : Set (Transformation S E)}
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    (hfin : ∀ F : Finset (Transformation S E), (F : Set (Transformation S E)) ⊆ J →
      {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ τ ∈ I ∪ (F : Set (Transformation S E)),
          MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure}.Nonempty) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I ∪ J,
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure}.Nonempty := by
  classical
  set K : Set (WithLocalConvergence S E) :=
    {μ | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} with hK
  set t : J → Set (WithLocalConvergence S E) := fun τ ↦
    {μ | ∀ σ ∈ ({(τ : Transformation S E)} : Set (Transformation S E)),
      MeasurePreserving σ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} with ht
  have htclosed : ∀ τ : J, IsClosed (t τ) := fun τ ↦
    isClosed_setOf_forall_measurePreserving _
  have hgoal : {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ I ∪ J,
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure}
      = K ∩ ⋂ τ : J, t τ := by
    ext μ
    simp only [hK, ht, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_singleton_iff,
      forall_eq, Set.mem_union]
    constructor
    · rintro ⟨hg, hinv⟩
      exact ⟨⟨hg, fun τ hτ ↦ hinv τ (.inl hτ)⟩, fun τ ↦ hinv τ (.inr τ.2)⟩
    · rintro ⟨⟨hg, hI⟩, hJ⟩
      exact ⟨hg, fun τ hτ ↦ hτ.elim (hI τ) fun h ↦ hJ ⟨τ, h⟩⟩
  rw [hgoal]
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed t htclosed
    (Set.disjoint_iff_inter_eq_empty.2 hempty)
  set F : Finset (Transformation S E) := u.image (fun τ : J ↦ (τ : Transformation S E)) with hF
  obtain ⟨μ, hμ⟩ := hfin F (by
    intro σ hσ
    simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hσ
    obtain ⟨τ, -, rfl⟩ := hσ
    exact τ.2)
  have hmemF : ∀ τ : J, τ ∈ u → (τ : Transformation S E) ∈ (F : Set (Transformation S E)) := by
    intro τ hτ
    simp only [hF, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨τ, hτ, rfl⟩
  have hμK : μ ∈ K := ⟨hμ.1, fun τ hτ ↦ hμ.2 τ (.inl hτ)⟩
  have hμt : μ ∈ ⋂ τ ∈ u, t τ := by
    simp only [Set.mem_iInter, ht, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    intro τ hτ
    exact hμ.2 (τ : Transformation S E) (.inr (hmemF τ hτ))
  exact Set.not_disjoint_iff.2 ⟨μ, hμK, hμt⟩ hu

/-! #### Georgii's own hypotheses: two subgroups with `I₁` commuting modulo `I₀`

Theorem (5.15)(ii) as Georgii states it: `𝒢_{I₀}(γ)` compact — not `𝒢(γ)` — and
`τ₁ ∘ τ₂ = τ₂ ∘ τ₁ ∘ τ₀` for some `τ₀ ∈ I₀`, rather than `I₁` abelian. Each `τ ∈ I₁` is
adjoined by the Følner argument over the cyclic group `{τ ^ k : k ∈ ℤ}`; the transport law
`τ^x(τ^y(ν)) = τ^{x+y}(ν)` is `zpow_add`, and the accumulated invariances survive because `τ`
normalises the subgroup generated by `I₀` and the transformations already adjoined. -/

/-- The group-theoretic step of Georgii's proof of Theorem (5.15)(ii): if `I₀` is normalised by
`I₁` elementwise (`τ₀ ∘ τ₁ = τ₁ ∘ τ₀'`) and `I₁` commutes modulo `I₀` (`σ ∘ τ = τ ∘ σ ∘ τ₀`),
then every `τ ∈ I₁` normalises the subgroup generated by `I₀` together with any subset
`s ⊆ I₁`: conjugation by `τ` moves a generator from `I₀` inside `I₀` and a generator `σ ∈ s`
to `σ ∘ τ₀'` with `τ₀' ∈ I₀`. -/
lemma mem_normalizer_closure_union {G : Type*} [Group G] {I₀ I₁ : Subgroup G}
    (hcomm₁ : ∀ σ ∈ I₁, ∀ τ ∈ I₁, ∃ τ₀ ∈ I₀, σ * τ = τ * σ * τ₀)
    (hcomm₀ : ∀ τ₀ ∈ I₀, ∀ τ₁ ∈ I₁, ∃ τ₀' ∈ I₀, τ₀ * τ₁ = τ₁ * τ₀')
    {s : Set G} (hs : s ⊆ (I₁ : Set G)) {τ : G} (hτ : τ ∈ I₁) :
    τ ∈ Subgroup.normalizer (Subgroup.closure ((I₀ : Set G) ∪ s) : Set G) := by
  have hconj : ∀ t ∈ I₁, ∀ g ∈ Subgroup.closure ((I₀ : Set G) ∪ s),
      t * g * t⁻¹ ∈ Subgroup.closure ((I₀ : Set G) ∪ s) := by
    intro t ht g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · obtain ⟨x', hx', hxeq⟩ := hcomm₀ x hx t⁻¹ (inv_mem ht)
        have hx'' : t * x * t⁻¹ = x' := by
          rw [mul_assoc, hxeq, ← mul_assoc, mul_inv_cancel, one_mul]
        rw [hx'']
        exact Subgroup.subset_closure (Set.mem_union_left _ hx')
      · obtain ⟨τ₀, hτ₀, hxeq⟩ := hcomm₁ t ht x (hs hx)
        obtain ⟨τ₀', hτ₀', h₀eq⟩ := hcomm₀ τ₀ hτ₀ t⁻¹ (inv_mem ht)
        have hconj₀ : t * τ₀ * t⁻¹ = τ₀' := by
          rw [mul_assoc, h₀eq, ← mul_assoc, mul_inv_cancel, one_mul]
        have hx'' : t * x * t⁻¹ = x * τ₀' := by
          rw [hxeq, ← hconj₀]
          simp [mul_assoc]
        rw [hx'']
        exact mul_mem (Subgroup.subset_closure (Set.mem_union_right _ hx))
          (Subgroup.subset_closure (Set.mem_union_left _ hτ₀'))
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by
        simp [mul_assoc]
      rw [hxy]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have hxinv : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by
        simp [mul_assoc]
      rw [hxinv]
      exact inv_mem ihx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg ↦ hconj τ hτ g hg
  · intro hg
    have h := hconj τ⁻¹ (inv_mem hτ) _ hg
    have hgid : τ⁻¹ * (τ * g * τ⁻¹) * τ⁻¹⁻¹ = g := by
      simp [mul_assoc]
    rwa [hgid] at h

/-- The single-generator step of Georgii's proof of Theorem (5.15)(ii): a transformation `τ`
that is a symmetry of `γ` and normalises a subgroup `J` of the transformation group can be
adjoined to `J`. If `𝒢_J(γ)` is compact and contains `ν`, it contains a measure that is
moreover `τ`-invariant: the Følner average of `ν` over the cyclic group `{τ ^ k : k ∈ ℤ}` stays
`J`-invariant because `τ` normalises `J`, and a cluster point is `τ`-invariant by the
symmetric-difference estimate. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_mem_normalizer
    {γ : Specification S E} {J : Subgroup (Transformation S E)} {τ : Transformation S E}
    (hτ : τ ∈ Subgroup.normalizer (J : Set (Transformation S E)))
    (hγ : Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ σ ∈ (J : Set (Transformation S E)),
        MeasurePreserving σ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ σ ∈ J, MeasurePreserving σ.toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ σ ∈ J, MeasurePreserving σ.toFun (μ : Measure (S → E)) μ) ∧
        MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  classical
  have hmulFun : ∀ σ ρ : Transformation S E, (σ * ρ).toFun = σ.toFun ∘ ρ.toFun :=
    fun σ ρ ↦ funext fun ω ↦ Transformation.comp_toFun σ ρ ω
  have hcomm : ∀ (i : ↥J) (x : ℤ), ∃ i' : ↥J,
      ((i : Transformation S E)).toFun ∘ (τ ^ x).toFun
        = (τ ^ x).toFun ∘ ((i' : Transformation S E)).toFun := by
    intro σ k
    have hmem : (τ ^ k)⁻¹ * (σ : Transformation S E) * τ ^ k ∈ J :=
      (Subgroup.mem_normalizer_iff''.1 (zpow_mem hτ k) (σ : Transformation S E)).1 σ.2
    refine ⟨⟨(τ ^ k)⁻¹ * (σ : Transformation S E) * τ ^ k, hmem⟩, ?_⟩
    have hgrp : (σ : Transformation S E) * τ ^ k
        = τ ^ k * ((τ ^ k)⁻¹ * (σ : Transformation S E) * τ ^ k) := by
      rw [← mul_assoc, mul_inv_cancel_left]
    rw [← hmulFun, ← hmulFun, hgrp]
  have hrange : Set.range (fun σ : ↥J ↦ (σ : Transformation S E))
      = (J : Set (Transformation S E)) := by
    ext σ
    constructor
    · rintro ⟨i, rfl⟩
      exact i.2
    · intro hσ
      exact ⟨⟨σ, hσ⟩, rfl⟩
  have hcpt' : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ i : ↥J, MeasurePreserving ((i : Transformation S E)).toFun
        (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
    rw [setOf_mem_GP_and_forall_measurePreserving_range
      (T := fun σ : ↥J ↦ (σ : Transformation S E)), hrange]
    exact hcpt
  obtain ⟨μ, hμGP, hμJ, hμτ⟩ :=
    exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_transportLaw
      (A := ℤ) (Φ := fun k : ℤ ↦ τ ^ k) (T₀ := fun σ : ↥J ↦ (σ : Transformation S E)) (ν := ν)
      (fun x y ↦ by
        change ((ν : Measure (S → E)).map (τ ^ y).toFun).map (τ ^ x).toFun
          = (ν : Measure (S → E)).map (τ ^ (x + y)).toFun
        rw [Measure.map_map (τ ^ x).measurable_toFun (τ ^ y).measurable_toFun, zpow_add]
        congr 1)
      hcomm (fun k ↦ hγ.zpow k) hcpt' hν (fun i ↦ hν₀ i i.2)
  exact ⟨μ, hμGP, fun σ hσ ↦ hμJ ⟨σ, hσ⟩, by simpa using hμτ 1⟩

/-- **The finite case of Georgii's proof of Theorem (5.15)(ii)**: `𝒢_{I₀ ∪ F}(γ) ≠ ∅` for every
finite `F ⊆ I₁`. The generators of `F` are adjoined one at a time by the cyclic Følner argument
(`exists_mem_GP_and_forall_measurePreserving_of_mem_normalizer`), the subgroup generated by
`I₀` and the transformations already adjoined being normalised by the next generator
(`mem_normalizer_closure_union`). -/
theorem nonempty_setOf_mem_GP_and_forall_measurePreserving_union_finset_of_commute_mod
    {γ : Specification S E} {I₀ I₁ : Subgroup (Transformation S E)}
    (hcomm₁ : ∀ σ ∈ I₁, ∀ τ ∈ I₁, ∃ τ₀ ∈ I₀, σ * τ = τ * σ * τ₀)
    (hcomm₀ : ∀ τ₀ ∈ I₀, ∀ τ₁ ∈ I₁, ∃ τ₀' ∈ I₀, τ₀ * τ₁ = τ₁ * τ₀')
    (hγ : ∀ τ ∈ I₁, Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ (I₀ : Set (Transformation S E)),
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ τ ∈ I₀, MeasurePreserving τ.toFun (ν : Measure (S → E)) ν)
    (F : Finset (Transformation S E))
    (hF : (F : Set (Transformation S E)) ⊆ (I₁ : Set (Transformation S E))) :
    {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ (I₀ : Set (Transformation S E)) ∪ (F : Set (Transformation S E)),
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure}.Nonempty := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨WithSetwiseTopology.ofMeasure ν, hν, fun σ hσ ↦ ?_⟩
    rw [Finset.coe_empty, Set.union_empty] at hσ
    exact hν₀ σ hσ
  | insert τ F hτF ih =>
    have hτ₁ : τ ∈ I₁ := hF (Finset.mem_coe.2 (Finset.mem_insert_self τ F))
    have hF' : (F : Set (Transformation S E)) ⊆ (I₁ : Set (Transformation S E)) :=
      fun σ hσ ↦ hF (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hσ)))
    obtain ⟨ν', hν'GP, hν'inv⟩ := ih hF'
    have hcptJ : IsCompact {μ : WithLocalConvergence S E |
        μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
        ∀ σ ∈ (Subgroup.closure
            ((I₀ : Set (Transformation S E)) ∪ (F : Set (Transformation S E))) :
          Set (Transformation S E)),
          MeasurePreserving σ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure} := by
      rw [setOf_mem_GP_and_forall_measurePreserving_closure]
      exact isCompact_setOf_mem_GP_and_forall_measurePreserving_of_subset
        Set.subset_union_left hcpt
    have hν'J : ∀ σ ∈ Subgroup.closure
        ((I₀ : Set (Transformation S E)) ∪ (F : Set (Transformation S E))),
        MeasurePreserving σ.toFun (ν'.toMeasure : Measure (S → E)) ν'.toMeasure :=
      fun σ hσ ↦ measurePreserving_of_mem_closure hν'inv hσ
    obtain ⟨μ, hμGP, hμJ, hμτ⟩ :=
      exists_mem_GP_and_forall_measurePreserving_of_mem_normalizer
        (mem_normalizer_closure_union hcomm₁ hcomm₀ hF' hτ₁) (hγ τ hτ₁) hcptJ hν'GP hν'J
    refine ⟨WithSetwiseTopology.ofMeasure μ, hμGP, fun σ hσ ↦ ?_⟩
    rcases hσ with hσ | hσ
    · exact hμJ σ (Subgroup.subset_closure (Set.mem_union_left _ hσ))
    · rw [Finset.coe_insert] at hσ
      rcases Set.mem_insert_iff.1 hσ with rfl | hσ
      · exact hμτ
      · exact hμJ σ (Subgroup.subset_closure (Set.mem_union_right _ hσ))

/-- **Georgii Theorem (5.15)(ii)** for two subgroups `I₀`, `I₁` of the transformation group, at
Georgii's hypotheses. Suppose `τ₀ ∘ τ₁ ∈ τ₁ ∘ I₀` for all `τ₀ ∈ I₀` and `τ₁ ∈ I₁` (Georgii's
normality hypothesis `τ₁ ∘ I₀ = I₀ ∘ τ₁`), `I₁` commutes modulo `I₀` — for all `σ, τ ∈ I₁`
there is some `τ₀ ∈ I₀` with `σ ∘ τ = τ ∘ σ ∘ τ₀` — `γ` is `I₁`-invariant, and `𝒢_{I₀}(γ)` is
compact in the topology of local convergence. If `𝒢_{I₀}(γ) ≠ ∅` then `𝒢(γ)` contains a measure
invariant under both `I₀` and `I₁`. Invariance of `γ` under `I₀` is not needed, nor is
compactness of `𝒢(γ)` itself. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_commute_mod_of_measurePreserving
    {γ : Specification S E} {I₀ I₁ : Subgroup (Transformation S E)}
    (hcomm₁ : ∀ σ ∈ I₁, ∀ τ ∈ I₁, ∃ τ₀ ∈ I₀, σ * τ = τ * σ * τ₀)
    (hcomm₀ : ∀ τ₀ ∈ I₀, ∀ τ₁ ∈ I₁, ∃ τ₀' ∈ I₀, τ₀ * τ₁ = τ₁ * τ₀')
    (hγ : ∀ τ ∈ I₁, Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ (I₀ : Set (Transformation S E)),
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ τ ∈ I₀, MeasurePreserving τ.toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ τ ∈ I₀, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ) ∧
        ∀ τ ∈ I₁, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  obtain ⟨μ, hμGP, hμinv⟩ :=
    nonempty_setOf_mem_GP_and_forall_measurePreserving_of_forall_finset
      (I := (I₀ : Set (Transformation S E))) (J := (I₁ : Set (Transformation S E))) hcpt
      (fun F hF ↦
        nonempty_setOf_mem_GP_and_forall_measurePreserving_union_finset_of_commute_mod
          hcomm₁ hcomm₀ hγ hcpt hν hν₀ F hF)
  exact ⟨μ.toMeasure, hμGP, fun τ hτ ↦ hμinv τ (Set.mem_union_left _ hτ),
    fun τ hτ ↦ hμinv τ (Set.mem_union_right _ hτ)⟩

/-- **Georgii Theorem (5.15)(ii)**, group form: at the hypotheses of
`exists_mem_GP_and_forall_measurePreserving_of_commute_mod_of_measurePreserving`,
`𝒢_{I₀}(γ) ≠ ∅` implies `𝒢_{I₁∘I₀}(γ) ≠ ∅` — the symmetrised Gibbs measure is invariant under
the whole subgroup `I₀ ⊔ I₁ = [I₀ ∪ I₁]`, which Georgii's normality hypothesis identifies with
`I₁ ∘ I₀`. -/
theorem exists_mem_GP_and_forall_measurePreserving_sup_of_commute_mod_of_measurePreserving
    {γ : Specification S E} {I₀ I₁ : Subgroup (Transformation S E)}
    (hcomm₁ : ∀ σ ∈ I₁, ∀ τ ∈ I₁, ∃ τ₀ ∈ I₀, σ * τ = τ * σ * τ₀)
    (hcomm₀ : ∀ τ₀ ∈ I₀, ∀ τ₁ ∈ I₁, ∃ τ₀' ∈ I₀, τ₀ * τ₁ = τ₁ * τ₀')
    (hγ : ∀ τ ∈ I₁, Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ ∧
      ∀ τ ∈ (I₀ : Set (Transformation S E)),
        MeasurePreserving τ.toFun (μ.toMeasure : Measure (S → E)) μ.toMeasure})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ τ ∈ I₀, MeasurePreserving τ.toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ τ ∈ I₀ ⊔ I₁, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  obtain ⟨μ, hμGP, h₀, h₁⟩ :=
    exists_mem_GP_and_forall_measurePreserving_of_commute_mod_of_measurePreserving
      hcomm₁ hcomm₀ hγ hcpt hν hν₀
  refine ⟨μ, hμGP, fun τ hτ ↦ ?_⟩
  have hmem : τ ∈ Subgroup.closure
      ((I₀ : Set (Transformation S E)) ∪ (I₁ : Set (Transformation S E))) := by
    rwa [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  refine measurePreserving_of_mem_closure (fun σ hσ ↦ ?_) hmem
  rcases hσ with hσ | hσ
  · exact h₀ σ hσ
  · exact h₁ σ hσ

/-- **Georgii Corollary (5.16)** for an abelian group acting by symmetries — the `I₀ = {id}`
case of Theorem (5.15)(ii)
(`exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving`). Let `Φ` turn
an abelian group `A` into symmetries of the specification `γ`. If `𝒢(γ)` is non-empty and
compact in the topology of local convergence, then `𝒢(γ)` contains a measure invariant under
every `Φ x`. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_isCompact [AddCommGroup A]
    {γ : Specification S E} {Φ : A → Transformation S E} (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y)
    (hγ : ∀ x, Specification.IsInvariant (Φ x) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ x : A, MeasurePreserving (Φ x).toFun (μ : Measure (S → E)) μ := by
  obtain ⟨ν, hν⟩ := hne
  obtain ⟨μ, hμ, -, h⟩ :=
    exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving
      (T₀ := fun i : Empty ↦ i.elim) hΦ (fun i ↦ i.elim) hγ hcpt hν (fun i ↦ i.elim)
  exact ⟨μ, hμ, h⟩

/-- **Georgii Theorem (5.15)(ii)** for two subgroups `I₀`, `I₁` of the transformation group,
with abelian outer subgroup. Suppose `I₁` is abelian, `τ₀ ∘ τ₁ ∈ τ₁ ∘ I₀` for all `τ₀ ∈ I₀` and
`τ₁ ∈ I₁` (Georgii's hypothesis `τ₁ ∘ I₀ = I₀ ∘ τ₁`), `γ` is `I₁`-invariant, and `𝒢(γ)` is
compact in the topology of local convergence. If `𝒢(γ)` contains an `I₀`-invariant measure —
`𝒢_{I₀}(γ) ≠ ∅` — then it contains a measure invariant under both `I₀` and `I₁`, hence under
`I₁ ∘ I₀`: `𝒢_{I₁∘I₀}(γ) ≠ ∅`. Invariance of `γ` under `I₀` is not needed. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_commute_of_measurePreserving
    {γ : Specification S E} {I₀ I₁ : Subgroup (Transformation S E)}
    (hcomm₁ : ∀ σ ∈ I₁, ∀ τ ∈ I₁, σ * τ = τ * σ)
    (hcomm₀ : ∀ τ₀ ∈ I₀, ∀ τ₁ ∈ I₁, ∃ τ₀' ∈ I₀, τ₀ * τ₁ = τ₁ * τ₀')
    (hγ : ∀ τ ∈ I₁, Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ τ ∈ I₀, MeasurePreserving τ.toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ τ ∈ I₀, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ) ∧
        ∀ τ ∈ I₁, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  classical
  let _ : CommGroup ↥I₁ :=
    { (inferInstance : Group ↥I₁) with mul_comm := fun a b ↦ Subtype.ext (hcomm₁ a a.2 b b.2) }
  have hmulFun : ∀ σ τ : Transformation S E, (σ * τ).toFun = σ.toFun ∘ τ.toFun :=
    fun σ τ ↦ funext fun ω ↦ Transformation.comp_toFun σ τ ω
  have hcomm : ∀ (i : ↥I₀) (x : Additive ↥I₁), ∃ i' : ↥I₀,
      ((i : Transformation S E)).toFun ∘
          (((Additive.toMul x : ↥I₁) : Transformation S E)).toFun
        = (((Additive.toMul x : ↥I₁) : Transformation S E)).toFun ∘
            ((i' : Transformation S E)).toFun := by
    intro i x
    obtain ⟨τ₀', hτ₀', heq⟩ := hcomm₀ (i : Transformation S E) i.2 _ (Additive.toMul x).2
    exact ⟨⟨τ₀', hτ₀'⟩, by rw [← hmulFun, ← hmulFun, heq]⟩
  obtain ⟨μ, hμ, h₀, h₁⟩ :=
    exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving
      (A := Additive ↥I₁) (Φ := fun x ↦ ((Additive.toMul x : ↥I₁) : Transformation S E))
      (T₀ := fun i : ↥I₀ ↦ (i : Transformation S E)) (fun _ _ ↦ rfl) hcomm
      (fun x ↦ hγ _ (Additive.toMul x).2) hcpt hν (fun i ↦ hν₀ i i.2)
  exact ⟨μ, hμ, fun τ hτ ↦ h₀ ⟨τ, hτ⟩, fun τ hτ ↦ h₁ (Additive.ofMul (⟨τ, hτ⟩ : ↥I₁))⟩

/-- **Georgii Corollary (5.16)**, abelian case. Let `I` be an abelian subgroup of the
transformation group and `γ` an `I`-invariant specification with `𝒢(γ) ≠ ∅`. If `𝒢(γ)` is compact
in the topology of local convergence, then the set `𝒢_I(γ)` of `I`-invariant Gibbs measures is
non-empty. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_commute {γ : Specification S E}
    {I : Subgroup (Transformation S E)} (hcomm : ∀ σ ∈ I, ∀ τ ∈ I, σ * τ = τ * σ)
    (hγ : ∀ τ ∈ I, Specification.IsInvariant τ γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  classical
  let _ : CommGroup ↥I :=
    { (inferInstance : Group ↥I) with mul_comm := fun a b ↦ Subtype.ext (hcomm a a.2 b b.2) }
  obtain ⟨μ, hμ, hinv⟩ := exists_mem_GP_and_forall_measurePreserving_of_isCompact
    (A := Additive ↥I) (Φ := fun x ↦ ((Additive.toMul x : ↥I) : Transformation S E))
    (fun _ _ ↦ rfl) (fun x ↦ hγ _ (Additive.toMul x).2) hcpt hne
  exact ⟨μ, hμ, fun τ hτ ↦ hinv (Additive.ofMul (⟨τ, hτ⟩ : ↥I))⟩

/-! ### Georgii (5.15)(i): averaging against an invariant weight on the acting group

Georgii's hypothesis (i) supplies a compact topology on the outer symmetry group `I₁`, and his
proof averages a Gibbs measure over its Haar measure. What the argument uses is only that the
group carries a *left-invariant probability measure* against which the action is measurable;
compactness enters solely to produce one. The theorems are therefore proved at that hypothesis,
with the second subgroup `I₀` carried along: the average of an `I₀`-invariant Gibbs measure is
`I₀`-invariant again when `I₀` commutes with the action modulo `I₀`
(`map_groupAverage_eq_of_comp_eq`). Unlike the Følner branch (5.15)(ii), no compactness of
`𝒢(γ)` is needed. -/

section InvariantWeight

variable {S E : Type*} [MeasurableSpace E] {H : Type*} [Group H] [MeasurableSpace H]
  {γ : Specification S E} {Φ : H → Transformation S E} {ν : Measure (S → E)} {w : Measure H}

variable (Φ) in
/-- The average `∫ τ_g(ν) w(dg)` of a measure over a group action, against a weight `w` on the
group. -/
noncomputable def groupAverage (ν : Measure (S → E)) (w : Measure H) : Measure (S → E) :=
  w.bind fun g ↦ ν.map (Φ g).toFun

omit [Group H] in
/-- Georgii's measurability hypothesis on the evaluation map `e : (τ, ω) ↦ τω` makes the family of
push-forwards a measurable map into the Giry space. -/
lemma measurable_map_toFun (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (ν : Measure (S → E)) [SFinite ν] :
    Measurable fun g ↦ ν.map (Φ g).toFun := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  have hval : (fun g ↦ ν.map (Φ g).toFun A)
      = fun g ↦ ∫⁻ ω, A.indicator 1 ((Φ g).toFun ω) ∂ν := by
    funext g
    rw [Measure.map_apply (Φ g).measurable_toFun hA,
      ← lintegral_indicator_one ((Φ g).measurable_toFun hA)]
    rfl
  rw [hval]
  exact Measurable.lintegral_prod_right'
    (f := fun p : H × (S → E) ↦ A.indicator 1 ((Φ p.1).toFun p.2))
    ((measurable_one.indicator hA).comp hev)

omit [Group H] in
lemma groupAverage_apply (hmeas : Measurable fun g ↦ ν.map (Φ g).toFun) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    groupAverage Φ ν w A = ∫⁻ g, ν.map (Φ g).toFun A ∂w :=
  Measure.bind_apply hA hmeas.aemeasurable

omit [Group H] in
lemma isProbabilityMeasure_groupAverage [IsProbabilityMeasure ν] [IsProbabilityMeasure w]
    (hmeas : Measurable fun g ↦ ν.map (Φ g).toFun) :
    IsProbabilityMeasure (groupAverage Φ ν w) := by
  constructor
  rw [groupAverage_apply hmeas MeasurableSet.univ]
  have hone : ∀ g : H, ν.map (Φ g).toFun Set.univ = 1 := fun g ↦ by
    rw [Measure.map_apply (Φ g).measurable_toFun MeasurableSet.univ, Set.preimage_univ]
    exact measure_univ
  simp [hone]

omit [Group H] in
/-- **The average of a Gibbs measure over a group of symmetries is a Gibbs measure.** Each
`τ_g(ν)` satisfies the DLR equations by Georgii (5.10), and `Measure.bind` is associative. -/
theorem isGibbsMeasure_groupAverage [IsProbabilityMeasure ν] [IsProbabilityMeasure w]
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (hmeas : Measurable fun g ↦ ν.map (Φ g).toFun) (hν : γ.IsGibbsMeasure ν) :
    γ.IsGibbsMeasure (groupAverage Φ ν w) := by
  have hprob := isProbabilityMeasure_groupAverage (Φ := Φ) (w := w) hmeas
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have hstep : ∀ g : H, (ν.map (Φ g).toFun).bind (γ Λ) = ν.map (Φ g).toFun := by
    intro g
    have hgp : IsProbabilityMeasure (ν.map (Φ g).toFun) :=
      Measure.isProbabilityMeasure_map (Φ g).measurable_toFun.aemeasurable
    exact (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1
      ((hγ g).map_isGibbsMeasure hν)) Λ
  rw [groupAverage, Measure.bind_bind hmeas.aemeasurable
    ((γ.measurable_kernel_toMeasure Λ).aemeasurable), funext hstep]

omit [Group H] in
/-- **Georgii (5.15)(i), the `I₀`-invariance of the symmetrised measure.** The group average
`∫ τ_g(ν) w(dg)` is invariant under any transformation `τ` that commutes with the action modulo
transformations preserving `ν`: for each `g` there are `σ` with `τ ∘ τ_g = τ_g ∘ σ` and
`σ(ν) = ν`. Neither invariance of `w` nor a group structure on `H` is needed for this part. -/
theorem map_groupAverage_eq_of_comp_eq (hmeas : Measurable fun g ↦ ν.map (Φ g).toFun)
    {τ : Transformation S E}
    (hcomm : ∀ g : H, ∃ σ : Transformation S E,
      τ.toFun ∘ (Φ g).toFun = (Φ g).toFun ∘ σ.toFun ∧ ν.map σ.toFun = ν) :
    (groupAverage Φ ν w).map τ.toFun = groupAverage Φ ν w := by
  have hstep : ∀ g : H, (ν.map (Φ g).toFun).map τ.toFun = ν.map (Φ g).toFun := by
    intro g
    obtain ⟨σ, hσ, hνσ⟩ := hcomm g
    rw [Measure.map_map τ.measurable_toFun (Φ g).measurable_toFun, hσ,
      ← Measure.map_map (Φ g).measurable_toFun σ.measurable_toFun, hνσ]
  calc (groupAverage Φ ν w).map τ.toFun
      = w.bind fun g ↦ (ν.map (Φ g).toFun).map τ.toFun :=
        Measure.map_bind hmeas τ.measurable_toFun
    _ = groupAverage Φ ν w := by rw [funext hstep]; rfl

variable [MeasurableMul H]

/-- The average is invariant: left invariance of `w` absorbs the translation `g ↦ h * g`. -/
theorem map_groupAverage_eq (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hmeas : Measurable fun g ↦ ν.map (Φ g).toFun)
    (hw : ∀ g : H, w.map (g * ·) = w) (h : H) :
    (groupAverage Φ ν w).map (Φ h).toFun = groupAverage Φ ν w := by
  have hstep : ∀ g : H, (ν.map (Φ g).toFun).map (Φ h).toFun = ν.map (Φ (h * g)).toFun := by
    intro g
    rw [Measure.map_map (Φ h).measurable_toFun (Φ g).measurable_toFun, hhom h g]
    exact congrArg (fun f ↦ Measure.map f ν)
      (funext fun ω ↦ (Transformation.comp_toFun (Φ h) (Φ g) ω).symm)
  calc (groupAverage Φ ν w).map (Φ h).toFun
      = w.bind fun g ↦ (ν.map (Φ g).toFun).map (Φ h).toFun :=
        Measure.map_bind hmeas (Φ h).measurable_toFun
    _ = w.bind fun g ↦ ν.map (Φ (h * g)).toFun := by rw [funext hstep]
    _ = (w.map (h * ·)).bind fun g ↦ ν.map (Φ g).toFun :=
        (Measure.bind_map (measurable_const_mul h) hmeas).symm
    _ = groupAverage Φ ν w := by rw [hw h]; rfl

/-- **Georgii, Theorem (5.15)(i)**, at the hypothesis the proof uses. Let a group `H` act on
configuration space by symmetries of `γ` — Georgii's outer subgroup `I₁` — with measurable
evaluation map `(g, ω) ↦ τ_g ω` and a left-invariant probability weight `w`; for a compact
group, `w` is the Haar measure. Let `T₀` index a family of transformations — Georgii's `I₀` —
preserving the Gibbs measure `ν` and commuting with the `H`-action modulo the family
(`τ₁ ∘ I₀ = I₀ ∘ τ₁`). Then the `w`-average of `ν` is a Gibbs measure invariant under the
`H`-action **and** under every `T₀ i`: `𝒢_{I₀}(γ) ≠ ∅` implies `𝒢_{I₁∘I₀}(γ) ≠ ∅`. No
compactness of `𝒢(γ)` is required. -/
theorem exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq
    [IsProbabilityMeasure ν] {ι₀ : Type*} {T₀ : ι₀ → Transformation S E}
    (hν : γ.IsGibbsMeasure ν)
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (hcomm : ∀ (i : ι₀) (g : H), ∃ i',
      (T₀ i).toFun ∘ (Φ g).toFun = (Φ g).toFun ∘ (T₀ i').toFun)
    (hν₀ : ∀ i, ν.map (T₀ i).toFun = ν)
    (w : Measure H) [IsProbabilityMeasure w] (hw : ∀ g : H, w.map (g * ·) = w) :
    ∃ μ : Measure (S → E), IsProbabilityMeasure μ ∧ γ.IsGibbsMeasure μ
      ∧ (∀ i, μ.map (T₀ i).toFun = μ) ∧ ∀ g : H, μ.map (Φ g).toFun = μ := by
  have hmeas := measurable_map_toFun hev ν (Φ := Φ)
  refine ⟨groupAverage Φ ν w, isProbabilityMeasure_groupAverage hmeas,
    isGibbsMeasure_groupAverage hγ hmeas hν, fun i ↦ ?_,
    fun g ↦ map_groupAverage_eq hhom hmeas hw g⟩
  refine map_groupAverage_eq_of_comp_eq hmeas fun g ↦ ?_
  obtain ⟨i', hi'⟩ := hcomm i g
  exact ⟨T₀ i', hi', hν₀ i'⟩

/-- **Georgii Corollary (5.16)**, invariant-weight branch — the `I₀ = {id}` case of Theorem
(5.15)(i) (`exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq`). If a group
`H` acts on configuration space by symmetries of `γ`, the evaluation map `(g, ω) ↦ τ_g ω` is
measurable, and `H` carries a left-invariant probability measure, then a non-empty `𝒢(γ)`
contains an `H`-invariant Gibbs measure. No compactness of `𝒢(γ)` is required. -/
theorem exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight
    [IsProbabilityMeasure ν] (hν : γ.IsGibbsMeasure ν)
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (w : Measure H) [IsProbabilityMeasure w] (hw : ∀ g : H, w.map (g * ·) = w) :
    ∃ μ : Measure (S → E), IsProbabilityMeasure μ ∧ γ.IsGibbsMeasure μ
      ∧ ∀ g : H, μ.map (Φ g).toFun = μ := by
  obtain ⟨μ, h1, h2, -, h3⟩ :=
    exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq
      (T₀ := fun i : Empty ↦ i.elim) hν hev hhom hγ (fun i ↦ i.elim) (fun i ↦ i.elim) w hw
  exact ⟨μ, h1, h2, h3⟩

/-- **Georgii, Theorem (5.15)(i)**, in the `MeasurePreserving` form of the Følner branch: from a
Gibbs measure invariant under the family `T₀`, the weight-average over the `H`-action produces a
Gibbs measure invariant under both. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_invariantWeight_of_measurePreserving
    {ι₀ : Type*} {T₀ : ι₀ → Transformation S E}
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (hcomm : ∀ (i : ι₀) (g : H), ∃ i',
      (T₀ i).toFun ∘ (Φ g).toFun = (Φ g).toFun ∘ (T₀ i').toFun)
    (w : Measure H) [IsProbabilityMeasure w] (hw : ∀ g : H, w.map (g * ·) = w)
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ i, MeasurePreserving (T₀ i).toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ i, MeasurePreserving (T₀ i).toFun (μ : Measure (S → E)) μ) ∧
        ∀ g : H, MeasurePreserving (Φ g).toFun (μ : Measure (S → E)) μ := by
  have : IsProbabilityMeasure (ν : Measure (S → E)) := ν.2
  obtain ⟨μ, hprob, hgibbs, hinv₀, hinv⟩ :=
    exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight_of_map_eq
      (ν := (ν : Measure (S → E))) hν hev hhom hγ hcomm (fun i ↦ (hν₀ i).map_eq) w hw
  exact ⟨⟨μ, hprob⟩, hgibbs, fun i ↦ ⟨(T₀ i).measurable_toFun, hinv₀ i⟩,
    fun g ↦ ⟨(Φ g).measurable_toFun, hinv g⟩⟩

/-- **Georgii Corollary (5.16)**, invariant-weight branch, in the `MeasurePreserving` form of the
Følner branch — the `I₀ = {id}` case of Theorem (5.15)(i). -/
theorem exists_mem_GP_and_forall_measurePreserving_of_invariantWeight
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (w : Measure H) [IsProbabilityMeasure w] (hw : ∀ g : H, w.map (g * ·) = w)
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ g : H, MeasurePreserving (Φ g).toFun (μ : Measure (S → E)) μ := by
  obtain ⟨ν, hν⟩ := hne
  have : IsProbabilityMeasure (ν : Measure (S → E)) := ν.2
  obtain ⟨μ, hprob, hgibbs, hinv⟩ :=
    exists_isGibbsMeasure_and_forall_map_eq_of_invariantWeight (ν := (ν : Measure (S → E)))
      hν hev hhom hγ w hw
  exact ⟨⟨μ, hprob⟩, hgibbs, fun g ↦ ⟨(Φ g).measurable_toFun, hinv g⟩⟩

/-! #### The compact case: Haar measure supplies the invariant weight -/

section Compact

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [Nonempty H]
  [MeasurableSpace H] [BorelSpace H] {Φ : H → Transformation S E}

/-- The Haar measure of a compact group, normalized to a probability measure. -/
noncomputable def haarProb (H : Type*) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [Nonempty H] [MeasurableSpace H] [BorelSpace H] : Measure H :=
  Measure.haarMeasure ⊤

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb H) := by
  constructor
  have htop : ((⊤ : TopologicalSpace.PositiveCompacts H) : Set H) = Set.univ := rfl
  rw [haarProb, ← htop]
  exact Measure.haarMeasure_self

lemma map_mul_haarProb (g : H) : (haarProb H).map (g * ·) = haarProb H :=
  (Measure.isMulLeftInvariant_haarMeasure ⊤).map_mul_left_eq_self g

/-- **Georgii, Theorem (5.15)(i)** for a compact group. If a compact group `H` acts on
configuration space by symmetries of `γ` with measurable evaluation map `(g, ω) ↦ τ_g ω`, and
`T₀` indexes a family of transformations commuting with the action modulo the family, then a
Gibbs measure invariant under the family `T₀` yields one invariant under `T₀` and `H` together:
Haar measure supplies the weight in
`exists_mem_GP_and_forall_measurePreserving_of_invariantWeight_of_measurePreserving`. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_compactGroup_of_measurePreserving
    {ι₀ : Type*} {T₀ : ι₀ → Transformation S E}
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (hcomm : ∀ (i : ι₀) (g : H), ∃ i',
      (T₀ i).toFun ∘ (Φ g).toFun = (Φ g).toFun ∘ (T₀ i').toFun)
    {ν : ProbabilityMeasure (S → E)} (hν : ν ∈ GP (S := S) (E := E) γ)
    (hν₀ : ∀ i, MeasurePreserving (T₀ i).toFun (ν : Measure (S → E)) ν) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      (∀ i, MeasurePreserving (T₀ i).toFun (μ : Measure (S → E)) μ) ∧
        ∀ g : H, MeasurePreserving (Φ g).toFun (μ : Measure (S → E)) μ :=
  exists_mem_GP_and_forall_measurePreserving_of_invariantWeight_of_measurePreserving
    hev hhom hγ hcomm (haarProb H) map_mul_haarProb hν hν₀

/-- **Georgii Corollary (5.16)** for a compact group — the `I₀ = {id}` case of Theorem
(5.15)(i). If a compact group `H` acts on configuration space by symmetries of `γ` with
measurable evaluation map `(g, ω) ↦ τ_g ω`, then a non-empty `𝒢(γ)` contains an `H`-invariant
Gibbs measure. Unlike the Følner branch, no compactness of `𝒢(γ)` is needed. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_compactGroup
    (hev : Measurable fun p : H × (S → E) ↦ (Φ p.1).toFun p.2)
    (hhom : ∀ g h : H, Φ (g * h) = Φ g * Φ h)
    (hγ : ∀ g, Specification.IsInvariant (Φ g) γ)
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ g : H, MeasurePreserving (Φ g).toFun (μ : Measure (S → E)) μ :=
  exists_mem_GP_and_forall_measurePreserving_of_invariantWeight hev hhom hγ (haarProb H)
    map_mul_haarProb hne

end Compact

end InvariantWeight

end MeasureTheory.GibbsMeasure

end

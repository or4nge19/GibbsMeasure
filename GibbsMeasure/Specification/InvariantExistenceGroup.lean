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
* `GibbsMeasure.exists_mem_GP_and_forall_measurePreserving_of_isCompact_of_measurePreserving`:
  **Georgii Theorem (5.15)(ii)** for an abelian group acting by symmetries — the averaging
  carries the `I₀`-invariance of the starting measure through to the cluster point;
  `exists_mem_GP_and_forall_measurePreserving_of_commute_of_measurePreserving` states it for two
  subgroups `I₀`, `I₁` of the transformation group;
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

In branch (ii), Georgii weakens commutativity of `I₁` to commutativity modulo `I₀`
(`τ₁ ∘ τ₂ = τ₂ ∘ τ₁ ∘ τ₀` for some `τ₀ ∈ I₀`) at the price of assuming `𝒢_{I₀}(γ)` compact and
running a finite-intersection argument over finite subsets of `I₁`. The form proved here (`I₁`
abelian, `𝒢(γ)` compact) is the one used by all of Georgii's examples (5.17), whose outer groups
are abelian or compact.
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
pushing the average forward by `Φ b`, when `Φ` turns addition into composition. -/
lemma map_transAverage [AddCommGroup A] [DecidableEq A] {Φ : A → Transformation S E}
    (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y) (ν : Measure (S → E)) (F : Finset A) (b : A) :
    (transAverage Φ ν F).map (Φ b).toFun = transAverage Φ ν (b +ᵥ F) := by
  have hterm : ∀ a : A, (ν.map (Φ a).toFun).map (Φ b).toFun = ν.map (Φ (b + a)).toFun := by
    intro a
    rw [Measure.map_map (Φ b).measurable_toFun (Φ a).measurable_toFun, hΦ]
    congr 1
  rw [transAverage, transAverage, uniformAverage, uniformAverage, Measure.map_smul,
    Measure.map_finset_sum (Φ b).measurable_toFun.aemeasurable, Finset.card_vadd_finset]
  congr 1
  rw [show b +ᵥ F = F.image (b + ·) from rfl,
    Finset.sum_image fun x _ y _ h ↦ add_left_cancel h]
  exact Finset.sum_congr rfl fun a _ ↦ hterm a

/-! ### Georgii Theorem (5.15)(ii) and Corollary (5.16) -/

/-- **Georgii Theorem (5.15)(ii)**, family form. Let `Φ` turn an abelian group `A` into
symmetries of the specification `γ`, and let `T₀` be a second family of transformations —
Georgii's subgroup `I₀` — such that each `T₀ i` commutes with each `Φ x` modulo the family:
`T₀ i ∘ Φ x = Φ x ∘ T₀ i'` for some index `i'` (Georgii's normality hypothesis
`τ₁ ∘ I₀ = I₀ ∘ τ₁`). If `𝒢(γ)` is compact in the topology of local convergence and contains a
measure `ν` invariant under every `T₀ i`, then it contains a measure invariant under every `T₀ i`
**and** every `Φ x` — in Georgii's notation, `𝒢_{I₀}(γ) ≠ ∅` implies `𝒢_{I₁∘I₀}(γ) ≠ ∅`.

The proof is Georgii's Markov–Kakutani argument: average `ν` over the Følner sets of `A` supplied
by `AddCommGroup.exists_finset_transDist_le` and take a cluster point. The averages stay
`T₀`-invariant because `ν` is and the two families commute, so the cluster point inherits this
invariance exactly, while the `Φ`-invariance comes from the Følner symmetric-difference estimate.
Invariance of `γ` under `T₀` is not needed. -/
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
  -- 𝒢(γ) is compact, so the net of averages has a cluster point in it
  have hle : map (fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E))
      atTop ≤ 𝓟 {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ} :=
    le_principal_iff.2 (mem_map.2 (Eventually.of_forall fun p ↦ hμsGP p))
  obtain ⟨μ, hμmem, hμcl⟩ := hcpt.exists_clusterPt hle
  have hMCP : MapClusterPt μ (atTop : Filter (Finset A × ℕ))
      fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E) := hμcl
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hMCP
  refine ⟨μ.toMeasure, hμmem, fun i ↦ ⟨(T₀ i).measurable_toFun, ?_⟩,
    fun x ↦ ⟨(Φ x).measurable_toFun, ?_⟩⟩
  -- `T₀`-invariance passes to the cluster point exactly, with no Følner error
  · have hmap : IsProbabilityMeasure ((μ.toMeasure : Measure (S → E)).map (T₀ i).toFun) := by
      constructor
      rw [Measure.map_apply (T₀ i).measurable_toFun .univ, preimage_univ, measure_univ]
    refine separatesOn_localEvents hmap inferInstance fun B hB ↦ ?_
    have hBm : MeasurableSet B := .of_mem_measurableCylinders hB
    rw [Measure.map_apply (T₀ i).measurable_toFun hBm]
    have h1 : Tendsto (fun p ↦ (μs p : Measure (S → E)) B) U
        (𝓝 ((μ.toMeasure : Measure (S → E)) B)) :=
      tendsto_withLocalConvergence_iff.1 hU B hB
    have h2 : Tendsto (fun p ↦ (μs p : Measure (S → E)) ((T₀ i).toFun ⁻¹' B)) U
        (𝓝 ((μ.toMeasure : Measure (S → E)) ((T₀ i).toFun ⁻¹' B))) :=
      tendsto_withLocalConvergence_iff.1 hU _ ((T₀ i).preimage_mem_localEvents hB)
    have heq : ∀ p, (μs p : Measure (S → E)) ((T₀ i).toFun ⁻¹' B)
        = (μs p : Measure (S → E)) B := fun p ↦ by
      rw [← Measure.map_apply (T₀ i).measurable_toFun hBm, hμs₀ p i]
    exact tendsto_nhds_unique (h2.congr heq) h1
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
      rw [measureReal_def, ← map_transAverage hΦ, Measure.map_apply (Φ x).measurable_toFun hBm,
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

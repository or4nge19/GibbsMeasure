/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.GroupTheory.Foelner
public import GibbsMeasure.Specification.InvariantFields
public import GibbsMeasure.Specification.Transformation

/-!
# Existence of invariant Gibbs measures by symmetrisation

Georgii Theorem (5.15)(ii) and Corollary (5.16): if `𝒢(γ)` is non-empty and compact in the
topology of local convergence and the symmetry group `I` of `γ` is abelian, then `𝒢_I(γ) ≠ ∅`.

Georgii's proof averages a Gibbs measure `ν` over larger and larger finite subsets of the abelian
group and passes to a cluster point. Where `GibbsMeasure/Specification/Average.lean` averages the
finite-volume Gibbs distributions `ν γ_Λ` over a finite family of **volumes** (Georgii (5.18)),
this file averages the **images** `τ(ν)` over a finite family of transformations; the two
constructions are genuinely different objects, so the API is deliberately parallel rather than
shared. Both are instances of the uniform average `uniformAverage m F = |F|⁻¹ ∑_{i ∈ F} m i` of a
finite family of measures, which is defined here together with the total-variation estimate
`|avg_F(A) - avg_{F'}(A)| ≤ |F ∆ F'| / |F|` for `|F| = |F'|`.

## Main results

* `MeasureTheory.mem_GP_finset_sum_smul` and `MeasureTheory.mem_GP_uniformAverage`: a finite
  convex combination of Gibbs measures is a Gibbs measure, generalising the binary
  `convexCombo_mem_GP` of `GibbsMeasure/Specification/Structure.lean`;
* `MeasureTheory.GibbsMeasure.map_transAverage`: `Φ b (avg_F ν) = avg_{b + F} ν` for a family of
  transformations indexed by an abelian group;
* `MeasureTheory.GibbsMeasure.exists_mem_GP_and_forall_measurePreserving_of_isCompact`, Georgii
  (5.15)(ii) with `I₀ = {id}`;
* `MeasureTheory.GibbsMeasure.exists_mem_GP_and_forall_measurePreserving_of_commute`, Georgii
  Corollary (5.16) for an abelian subgroup of transformations.

The Følner sets driving the averaging come from `GibbsMeasure/Mathlib/GroupTheory/Foelner.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal Pointwise symmDiff Topology

noncomputable section

namespace MeasureTheory

variable {ι Ω : Type*} [MeasurableSpace Ω]

/-! ### Uniform averages of a finite family of measures -/

/-- The uniform average `|F|⁻¹ ∑_{i ∈ F} m i` of a family of measures over a finite index set. -/
def uniformAverage (m : ι → Measure Ω) (F : Finset ι) : Measure Ω :=
  (F.card : ℝ≥0∞)⁻¹ • ∑ i ∈ F, m i

lemma uniformAverage_apply (m : ι → Measure Ω) (F : Finset ι) (A : Set Ω) :
    uniformAverage m F A = (F.card : ℝ≥0∞)⁻¹ * ∑ i ∈ F, m i A := by
  simp only [uniformAverage, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]

lemma isProbabilityMeasure_uniformAverage (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F : Finset ι} (hF : F.Nonempty) :
    IsProbabilityMeasure (uniformAverage m F) := by
  constructor
  rw [uniformAverage_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ (hm i).measure_univ, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hF.card_pos.ne') (ENNReal.natCast_ne_top _)

lemma uniformAverage_real_apply (m : ι → Measure Ω) (hm : ∀ i, IsProbabilityMeasure (m i))
    (F : Finset ι) (A : Set Ω) :
    (uniformAverage m F).real A = (F.card : ℝ)⁻¹ * ∑ i ∈ F, (m i).real A := by
  rw [measureReal_def, uniformAverage_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_sum fun i _ ↦ have := hm i; measure_ne_top _ A]
  simp only [measureReal_def]

/-- Two uniform averages over non-empty index sets `F`, `F'` differ on every event by at most
`|F ∆ F'| / |F| + | |F'| / |F| - 1 |`. -/
lemma abs_uniformAverage_real_sub_le [DecidableEq ι] (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F F' : Finset ι} (hF : F.Nonempty) (hF' : F'.Nonempty)
    (A : Set Ω) :
    |(uniformAverage m F).real A - (uniformAverage m F').real A| ≤
      ((F ∆ F').card : ℝ) / F.card + |(F'.card : ℝ) / F.card - 1| := by
  set g : ι → ℝ := fun i ↦ (m i).real A with hg
  have hg0 : ∀ i, 0 ≤ g i := fun _ ↦ measureReal_nonneg
  have hg1 : ∀ i, g i ≤ 1 := fun i ↦ have := hm i; measureReal_le_one
  have hc : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hc' : (0 : ℝ) < F'.card := by exact_mod_cast hF'.card_pos
  rw [uniformAverage_real_apply m hm, uniformAverage_real_apply m hm]
  have hsum_le : ∀ T : Finset ι, ∑ i ∈ T, g i ≤ T.card := fun T ↦ by
    simpa using Finset.sum_le_card_nsmul T g 1 fun i _ ↦ hg1 i
  have hsum_nn : ∀ T : Finset ι, 0 ≤ ∑ i ∈ T, g i := fun T ↦
    Finset.sum_nonneg fun i _ ↦ hg0 i
  have hdecomp : (F.card : ℝ)⁻¹ * ∑ i ∈ F, g i - (F'.card : ℝ)⁻¹ * ∑ i ∈ F', g i =
      (F.card : ℝ)⁻¹ * (∑ i ∈ F \ F', g i - ∑ i ∈ F' \ F, g i) +
        ((F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹) * ∑ i ∈ F', g i := by
    rw [Finset.sum_sdiff_sub_sum_sdiff]; ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (inv_pos.2 hc), div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hc).le
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (hsum_nn _), abs_of_nonneg (hsum_nn _), Finset.symmDiff_def,
      Finset.card_union_of_disjoint disjoint_sdiff_sdiff, Nat.cast_add]
    exact add_le_add (hsum_le _) (hsum_le _)
  · rw [abs_mul, abs_of_nonneg (hsum_nn _)]
    calc |(F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹| * ∑ i ∈ F', g i
        ≤ |(F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹| * F'.card :=
          mul_le_mul_of_nonneg_left (hsum_le _) (abs_nonneg _)
      _ = |((F.card : ℝ)⁻¹ - (F'.card : ℝ)⁻¹) * F'.card| := by rw [abs_mul, abs_of_pos hc']
      _ = |(F'.card : ℝ) / F.card - 1| := by
          congr 1
          rw [sub_mul, inv_mul_cancel₀ hc'.ne', div_eq_inv_mul]

/-- Uniform averages over index sets of the same cardinality differ by at most `|F ∆ F'| / |F|`. -/
lemma abs_uniformAverage_real_sub_le_of_card_eq [DecidableEq ι] (m : ι → Measure Ω)
    (hm : ∀ i, IsProbabilityMeasure (m i)) {F F' : Finset ι} (hF : F.Nonempty)
    (hcard : F.card = F'.card) (A : Set Ω) :
    |(uniformAverage m F).real A - (uniformAverage m F').real A| ≤
      ((F ∆ F').card : ℝ) / F.card := by
  have hF' : F'.Nonempty := Finset.card_pos.1 (hcard ▸ hF.card_pos)
  have h := abs_uniformAverage_real_sub_le m hm hF hF' A
  rwa [← hcard, div_self (by exact_mod_cast hF.card_pos.ne'), sub_self, abs_zero, add_zero] at h

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

end MeasureTheory

namespace MeasureTheory.GibbsMeasure

variable {S E A : Type*} [MeasurableSpace E]

/-! ### Averages over a family of transformations -/

/-- **Georgii (5.15)(ii).** The average `|F|⁻¹ ∑_{a ∈ F} Φ a (ν)` of the images of a random field
`ν` under a finite family `F` of transformations. -/
def transAverage (Φ : A → Transformation S E) (ν : Measure (S → E)) (F : Finset A) :
    Measure (S → E) :=
  uniformAverage (fun a ↦ ν.map (Φ a).toFun) F

lemma isProbabilityMeasure_transAverage (Φ : A → Transformation S E) (ν : Measure (S → E))
    [IsProbabilityMeasure ν] {F : Finset A} (hF : F.Nonempty) :
    IsProbabilityMeasure (transAverage Φ ν F) :=
  isProbabilityMeasure_uniformAverage _
    (fun a ↦ Measure.isProbabilityMeasure_map (Φ a).measurable_toFun.aemeasurable) hF

/-- **Georgii (5.15)(ii).** Translating the index set by `b` is the same as pushing the average
forward by `Φ b`, when `Φ` turns addition into composition. -/
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

/-- **Georgii (5.15)(ii)** with trivial first subgroup. Let `Φ` turn an abelian group `A` into
symmetries of the specification `γ`. If `𝒢(γ)` is non-empty and compact in the topology of local
convergence, then `𝒢(γ)` contains a measure invariant under every `Φ x`.

The proof is Georgii's Markov–Kakutani argument: average a Gibbs measure over the Følner sets of
`A` supplied by `AddCommGroup.exists_finset_transDist_le` and take a cluster point. -/
theorem exists_mem_GP_and_forall_measurePreserving_of_isCompact [AddCommGroup A]
    {γ : Specification S E} {Φ : A → Transformation S E} (hΦ : ∀ x y, Φ (x + y) = Φ x * Φ y)
    (hγ : ∀ x, Specification.IsInvariant (Φ x) γ)
    (hcpt : IsCompact {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ})
    (hne : (GP (S := S) (E := E) γ).Nonempty) :
    ∃ μ ∈ GP (S := S) (E := E) γ,
      ∀ x : A, MeasurePreserving (Φ x).toFun (μ : Measure (S → E)) μ := by
  classical
  obtain ⟨ν, hν⟩ := hne
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
  -- 𝒢(γ) is compact, so the net of averages has a cluster point in it
  have hle : map (fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E))
      atTop ≤ 𝓟 {μ : WithLocalConvergence S E | μ.toMeasure ∈ GP (S := S) (E := E) γ} :=
    le_principal_iff.2 (mem_map.2 (Eventually.of_forall fun p ↦ hμsGP p))
  obtain ⟨μ, hμmem, hμcl⟩ := hcpt.exists_clusterPt hle
  have hMCP : MapClusterPt μ (atTop : Filter (Finset A × ℕ))
      fun p ↦ (WithSetwiseTopology.ofMeasure (μs p) : WithLocalConvergence S E) := hμcl
  obtain ⟨U, hUle, hU⟩ := mapClusterPt_iff_ultrafilter.1 hMCP
  refine ⟨μ.toMeasure, hμmem, fun x ↦ ⟨(Φ x).measurable_toFun, ?_⟩⟩
  have hmap : IsProbabilityMeasure ((μ.toMeasure : Measure (S → E)).map (Φ x).toFun) := by
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

end MeasureTheory.GibbsMeasure

end

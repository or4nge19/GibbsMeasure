/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.StieltjesPoint
public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence
public import GibbsMeasure.Specification.Abstract
public import GibbsMeasure.Specification.PAKernel

/-!
# Georgii, Proposition (7.25) in the abstract setting of Remark (7.13)

For an `AbstractSpecification γ` on a standard Borel space `Ω` we build a probability kernel
`paKernel γ f hf hcof ν₀ : Kernel[γ.tail] Ω Ω` which does not depend on the measure whose tail
conditional distribution it is (only on a fixed fallback `ν₀ ∈ 𝒢(γ)`, used on the bad tail set):
it is a version of `μ(· | 𝓣)` for every `μ ∈ 𝒢(γ)`, and takes all its values in `𝒢(γ)`; that is,
it is a `(𝒢(γ), 𝓣)`-kernel in the sense of `IsPAKernel` (Georgii's Definition (7.21)).

The construction is parameterised by a monotone cofinal sequence `f : ℕ → ι` (hypotheses
`hf : Monotone f` and `hcof : ∀ i, ∃ n, i ≤ f n`), so that a concrete specification can pass its
own exhaustion and the specialisation is definitional. When `ι` is a countable nonempty preorder
directed upwards, the canonical choice `cofinalSeq ι` (from `exists_monotone_cofinal`) yields the
existence theorem `exists_isPAKernel_invariant`.

Along `f`, Lévy's downward theorem and the invariance equation identify `lim_n γ_{f n}(A | ·)`
with `μ(A | 𝓣)`; applying this to the half-lines `{embeddingReal Ω ≤ q}`, `q : ℚ`, gives a
tail-measurable rational CDF, which `kernelOfMeasurableRat` (i.e. `stieltjesOfMeasurableRat`)
turns into a kernel to `ℝ`, pulled back to `Ω` by `comapRight`. The bad tail sets are sent to a
fixed `ν₀ ∈ 𝒢(γ)`.

`GibbsMeasure/Specification/GibbsKernel.lean` instantiates everything here along
`Specification.toAbstract` and the exhaustion `exhaustionVolumes` to obtain the `(G(γ), 𝓣)`-kernel
of a concrete specification; the construction exists only once, in this file.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

namespace AbstractSpecification

variable {Ω ι : Type*} [m : MeasurableSpace Ω] [Preorder ι]

/-! ### A canonical cofinal sequence -/

section CofinalSeq

variable (ι) [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]

/-- A canonical monotone cofinal sequence in a countable nonempty preorder directed upwards. -/
noncomputable def cofinalSeq : ℕ → ι := Classical.choose (exists_monotone_cofinal ι)

lemma monotone_cofinalSeq : Monotone (cofinalSeq ι) :=
  (Classical.choose_spec (exists_monotone_cofinal ι)).1

lemma cofinal_cofinalSeq (i : ι) : ∃ n, i ≤ cofinalSeq ι n :=
  (Classical.choose_spec (exists_monotone_cofinal ι)).2 i

end CofinalSeq

/-! ### The kernels are versions of the conditional expectation -/

section CondExp

variable {γ : AbstractSpecification Ω ι} {μ : Measure Ω}

lemma isCondExp_ker [IsProbabilityMeasure μ] (hμ : μ ∈ γ.invariant) (i : ι) :
    (γ.ker i).IsCondExp μ :=
  (Kernel.isCondExp_iff_bind_eq_left (γ.isProper i) (γ.sub_le i)).2 (hμ.2 i)

lemma condExp_sub_ae_eq [IsProbabilityMeasure μ] (hμ : μ ∈ γ.invariant) (i : ι) {A : Set Ω}
    (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.sub i] =ᵐ[μ] fun ω ↦ (γ.ker i ω A).toReal :=
  @Kernel.IsCondExp.condExp_ae_eq_kernel_apply _ _ _ _ _ (isCondExp_ker hμ i) A hA

end CondExp

/-! ### The tail limit along a monotone cofinal sequence -/

section TailLimit

variable (γ : AbstractSpecification Ω ι) (f : ℕ → ι)

/-- The tail limit `lim_n γ_{f n}(A | ω)` along a sequence `f` of indices, defined everywhere as
a `limUnder`. -/
noncomputable def tailLimit (A : Set Ω) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ (γ.ker (f n) ω A).toReal

lemma measurable_tailLimit (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) {A : Set Ω}
    (hA : MeasurableSet A) :
    Measurable[γ.tail] (γ.tailLimit f A) := by
  rw [tail_eq_iInf_of_cofinal (γ := γ) hcof]
  refine (stronglyMeasurable_iInf_limUnder_of_antitone (γ.sub_antitone.comp_monotone hf)
    (f := fun n ω ↦ (γ.ker (f n) ω A).toReal) fun n ↦ ?_).measurable
  exact (Kernel.measurable_coe (γ.ker (f n)) hA).ennreal_toReal.stronglyMeasurable

variable {γ f}

/-- Lévy's downward theorem: along a monotone cofinal sequence `f`, `lim_n γ_{f n}(A | ·)` is a
version of `μ(A | 𝓣)` for every invariant probability measure `μ`. -/
lemma tailLimit_ae_eq_condExp {μ : Measure Ω} [IsProbabilityMeasure μ] (hf : Monotone f)
    (hcof : ∀ i, ∃ n, i ≤ f n) (hμ : μ ∈ γ.invariant) {A : Set Ω} (hA : MeasurableSet A) :
    γ.tailLimit f A =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] := by
  have hg : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hA
  have h1 := limUnder_condExp_ae_eq_condExp_iInf (μ := μ) (ℱ := fun n ↦ γ.sub (f n))
    (γ.sub_antitone.comp_monotone hf) (fun n ↦ γ.sub_le (f n)) hg
  rw [← tail_eq_iInf_of_cofinal (γ := γ) hcof] at h1
  have h2 : ∀ᵐ ω ∂μ, ∀ n, μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.sub (f n)] ω =
      (γ.ker (f n) ω A).toReal :=
    ae_all_iff.2 fun n ↦ condExp_sub_ae_eq hμ (f n) hA
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [← h1ω]
  exact congrArg _ (funext fun n ↦ (h2ω n).symm)

end TailLimit

/-! ### The tail-measurable kernel to `ℝ` -/

section RatCDF

variable [StandardBorelSpace Ω] (γ : AbstractSpecification Ω ι) (f : ℕ → ι)

/-- The rational tail CDF `ω ↦ (q ↦ lim_n γ_{f n}({e ≤ q} | ω))`, where `e = embeddingReal Ω`. -/
noncomputable def tailRatCDF (ω : Ω) (q : ℚ) : ℝ :=
  γ.tailLimit f (embeddingReal Ω ⁻¹' Iic (q : ℝ)) ω

lemma measurable_tailRatCDF (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) :
    Measurable[γ.tail] (γ.tailRatCDF f) := by
  have h : ∀ q : ℚ, Measurable[γ.tail] fun ω ↦ γ.tailRatCDF f ω q := fun q ↦
    measurable_tailLimit γ f hf hcof (measurableSet_Iic.preimage (measurable_embeddingReal Ω))
  let _ : MeasurableSpace Ω := γ.tail
  exact measurable_pi_iff.2 h

/-- The tail-measurable kernel to `ℝ` obtained from the rational tail CDF. -/
noncomputable def tailRealKernel (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) :
    Kernel[γ.tail] Ω ℝ :=
  kernelOfMeasurableRat γ.tail (γ.tailRatCDF f) (γ.measurable_tailRatCDF f hf hcof)

instance (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) :
    IsMarkovKernel (γ.tailRealKernel f hf hcof) :=
  isMarkovKernel_kernelOfMeasurableRat _ _ _

end RatCDF

/-! ### Identification with the tail conditional kernel -/

section TailCondKernel

variable [StandardBorelSpace Ω] (γ : AbstractSpecification Ω ι) (μ : Measure Ω)
  [IsProbabilityMeasure μ]

/-- The tail conditional kernel of `μ`, a regular conditional distribution given `𝓣`. -/
noncomputable def tailCondKernel : Kernel[γ.tail] Ω Ω := condExpKernel (mΩ := m) μ γ.tail

instance : IsMarkovKernel (tailCondKernel γ μ) := by
  unfold tailCondKernel; infer_instance

variable {γ μ}

lemma tailCondKernel_real_ae_eq_condExp [Nonempty ι] {A : Set Ω} (hA : MeasurableSet A) :
    (fun ω ↦ (tailCondKernel γ μ ω).real A) =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] :=
  condExpKernel_ae_eq_condExp (μ := μ) γ.tail_le hA

/-- Tower property: the tail conditional measures of an invariant measure are a.e. fixed by every
`γᵢ` on every measurable set. -/
lemma ae_bind_tailCondKernel_apply_eq [Nonempty ι] (hμ : μ ∈ γ.invariant) (i : ι) {B : Set Ω}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, (tailCondKernel γ μ ω).bind (γ.ker i) B = tailCondKernel γ μ ω B := by
  set g : Ω → ℝ := fun x ↦ (γ.ker i x B).toReal with hg
  have hg_meas : Measurable g :=
    ((Kernel.measurable_coe (γ.ker i) hB).mono (γ.sub_le i) le_rfl).ennreal_toReal
  have hg_int : ∀ (ν : Measure Ω) [IsFiniteMeasure ν], Integrable g ν := fun ν _ ↦
    (memLp_top_of_bound hg_meas.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))).integrable
      le_top
  have h1 : μ[g | γ.tail] =ᵐ[μ] fun ω ↦ ∫ y, g y ∂(tailCondKernel γ μ ω) :=
    condExp_ae_eq_integral_condExpKernel γ.tail_le (hg_int μ)
  have h2 : g =ᵐ[μ] μ[B.indicator (fun _ ↦ (1 : ℝ)) | γ.sub i] := (condExp_sub_ae_eq hμ i hB).symm
  have h3 : μ[g | γ.tail] =ᵐ[μ] μ[B.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] :=
    (condExp_congr_ae h2).trans (condExp_condExp_of_le (γ.tail_le_sub i) (γ.sub_le i))
  filter_upwards [h1, h3, tailCondKernel_real_ae_eq_condExp (γ := γ) (μ := μ) hB]
    with ω h1ω h3ω h4ω
  have hint : ∫ y, g y ∂(tailCondKernel γ μ ω) = (tailCondKernel γ μ ω).real B := by
    rw [← h1ω, h3ω, h4ω]
  have hlint : ∫⁻ x, γ.ker i x B ∂(tailCondKernel γ μ ω)
      = ENNReal.ofReal (∫ y, g y ∂(tailCondKernel γ μ ω)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hg_int _) (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)]
    exact lintegral_congr fun x ↦ (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [Measure.bind_apply hB (γ.aemeasurable_ker i _), hlint, hint, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

end TailCondKernel

/-! ### A countable core for invariance -/

section Core

variable [MeasurableSpace.CountablyGenerated Ω] [Countable ι] (γ : AbstractSpecification Ω ι)

/-- A *countable* core formulation of invariance: check `μ γᵢ = μ` on a countable π-system
generating the σ-algebra. -/
def IsInvariantCore (μ : Measure Ω) : Prop :=
  μ univ = 1 ∧ ∀ (i : ι) (t : Finset ℕ),
    (μ.bind (γ.ker i)) (piNatGen (Ω := Ω) t) = μ (piNatGen (Ω := Ω) t)

lemma measurableSet_isInvariantCore : MeasurableSet {μ : Measure Ω | γ.IsInvariantCore μ} := by
  have h_univ : MeasurableSet {μ : Measure Ω | μ univ = (1 : ℝ≥0∞)} :=
    (measurableSet_singleton (1 : ℝ≥0∞)).preimage (Measure.measurable_coe MeasurableSet.univ)
  have hEq (i : ι) (t : Finset ℕ) : MeasurableSet {μ : Measure Ω |
      (μ.bind (γ.ker i)) (piNatGen (Ω := Ω) t) = μ (piNatGen (Ω := Ω) t)} := by
    have hbind : Measurable fun μ : Measure Ω ↦ μ.bind fun ω ↦ (γ.ker i ω : Measure Ω) :=
      Measure.measurable_bind' (γ.measurable_ker i)
    have h_eval : Measurable fun μ : Measure Ω ↦ μ (piNatGen (Ω := Ω) t) :=
      Measure.measurable_coe (measurableSet_piNatGen t)
    exact measurableSet_eq_fun (h_eval.comp hbind) h_eval
  have hAll : MeasurableSet {μ : Measure Ω | ∀ (i : ι) (t : Finset ℕ),
      (μ.bind (γ.ker i)) (piNatGen (Ω := Ω) t) = μ (piNatGen (Ω := Ω) t)} := by
    simpa [Set.ofPred_forall] using
      MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun t ↦ hEq i t
  simpa [IsInvariantCore, Set.ofPred_and, Set.ofPred_forall] using h_univ.inter hAll

omit [Countable ι] in
lemma mem_invariant_of_isInvariantCore {μ : Measure Ω} (hcore : γ.IsInvariantCore μ) :
    μ ∈ γ.invariant := by
  have hprob : IsProbabilityMeasure μ := ⟨hcore.1⟩
  refine ⟨hprob, fun i ↦ ?_⟩
  have hbind : IsProbabilityMeasure (μ.bind (γ.ker i)) :=
    isProbabilityMeasure_bind (γ.aemeasurable_ker i μ)
      (Eventually.of_forall fun ω ↦ IsMarkovKernel.isProbabilityMeasure ω)
  refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
    generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
  rintro s ⟨t, rfl⟩
  exact hcore.2 i t

omit [Countable ι] in
lemma isInvariantCore_of_mem_invariant {μ : Measure Ω} (hμ : μ ∈ γ.invariant) :
    γ.IsInvariantCore μ := by
  have : IsProbabilityMeasure μ := hμ.1
  exact ⟨measure_univ, fun i t ↦ by rw [hμ.2 i]⟩

lemma measurableSet_invariant [Nonempty ι] [IsDirected ι (· ≤ ·)] :
    MeasurableSet γ.invariant := by
  have h : γ.invariant = {μ | γ.IsInvariantCore μ} :=
    Set.ext fun μ ↦ ⟨isInvariantCore_of_mem_invariant γ, mem_invariant_of_isInvariantCore γ⟩
  rw [h]
  exact measurableSet_isInvariantCore γ

end Core

/-! ### The tail conditional measures satisfy the invariance core -/

section InvariantCoreTailCondKernel

variable [StandardBorelSpace Ω] [Countable ι] {γ : AbstractSpecification Ω ι} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- Tower property, π-system form: the tail conditional measures of an invariant measure a.e.
satisfy the countable invariance core. -/
lemma ae_isInvariantCore_tailCondKernel [Nonempty ι] (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, γ.IsInvariantCore (tailCondKernel γ μ ω) := by
  have h : ∀ᵐ ω ∂μ, ∀ (i : ι) (t : Finset ℕ),
      ((tailCondKernel γ μ ω).bind (γ.ker i)) (piNatGen (Ω := Ω) t) =
        tailCondKernel γ μ ω (piNatGen (Ω := Ω) t) :=
    ae_all_iff.2 fun i ↦ ae_all_iff.2 fun t ↦
      ae_bind_tailCondKernel_apply_eq hμ i (measurableSet_piNatGen t)
  filter_upwards [h] with ω hω
  exact ⟨measure_univ, hω⟩

end InvariantCoreTailCondKernel

section Identification

variable [StandardBorelSpace Ω] {γ : AbstractSpecification Ω ι} {f : ℕ → ι} (μ : Measure Ω)
  [IsProbabilityMeasure μ]

lemma ae_forall_tailRatCDF_eq [Nonempty ι] (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n)
    (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, γ.tailRatCDF f ω q =
      ((tailCondKernel γ μ ω).map (embeddingReal Ω)).real (Iic (q : ℝ)) := by
  refine ae_all_iff.2 fun q ↦ ?_
  have hA : MeasurableSet (embeddingReal Ω ⁻¹' Iic (q : ℝ)) :=
    measurableSet_Iic.preimage (measurable_embeddingReal _)
  filter_upwards [tailLimit_ae_eq_condExp hf hcof hμ hA,
    tailCondKernel_real_ae_eq_condExp (γ := γ) (μ := μ) hA] with ω h1 h2
  rw [map_measureReal_apply (measurable_embeddingReal _) measurableSet_Iic]
  exact h1.trans h2.symm

lemma ae_tailRealKernel_eq_map [Nonempty ι] (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n)
    (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, γ.tailRealKernel f hf hcof ω = (tailCondKernel γ μ ω).map (embeddingReal Ω) := by
  filter_upwards [ae_forall_tailRatCDF_eq μ hf hcof hμ] with ω hω
  have : IsProbabilityMeasure ((tailCondKernel γ μ ω).map (embeddingReal Ω)) :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal _).aemeasurable
  exact kernelOfMeasurableRat_eq γ.tail (γ.measurable_tailRatCDF f hf hcof) _ hω

end Identification

/-! ### The `(𝒢(γ), 𝓣)`-kernel -/

section PAKernel

variable [StandardBorelSpace Ω] [Countable ι] (γ : AbstractSpecification Ω ι) (f : ℕ → ι)
  (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) (ν₀ : Measure Ω)

/-- The tail event on which `γ.tailRealKernel` is carried by the range of `embeddingReal`. -/
def rangeSet : Set Ω := {ω | γ.tailRealKernel f hf hcof ω (range (embeddingReal Ω)) = 1}

omit [Countable ι] in
lemma measurableSet_rangeSet : MeasurableSet[γ.tail] (γ.rangeSet f hf hcof) :=
  (measurableSet_singleton 1).preimage
    (Kernel.measurable_coe _ (measurableEmbedding_embeddingReal _).measurableSet_range)

open Classical in
/-- `γ.tailRealKernel`, replaced off `γ.rangeSet` by the pushforward of `ν₀`. -/
noncomputable def tailRealKernel' : Kernel[γ.tail] Ω ℝ :=
  Kernel.piecewise (measurableSet_rangeSet γ f hf hcof) (γ.tailRealKernel f hf hcof)
    (@Kernel.const Ω ℝ γ.tail _ (ν₀.map (embeddingReal Ω)))

omit [Countable ι] in
lemma tailRealKernel'_apply_range [IsProbabilityMeasure ν₀] (ω : Ω) :
    tailRealKernel' γ f hf hcof ν₀ ω (range (embeddingReal Ω)) = 1 := by
  classical
  rw [tailRealKernel', Kernel.piecewise_apply]
  split_ifs with h
  · exact h
  · rw [Kernel.const_apply, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]

/-- The candidate `(𝒢(γ), 𝓣)`-kernel, before correction on the bad tail set. -/
noncomputable def paKernelAux : Kernel[γ.tail] Ω Ω :=
  Kernel.comapRight (tailRealKernel' γ f hf hcof ν₀) (measurableEmbedding_embeddingReal Ω)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (paKernelAux γ f hf hcof ν₀) :=
  Kernel.IsMarkovKernel.comapRight _ _ (tailRealKernel'_apply_range γ f hf hcof ν₀)

/-- The tail event on which `paKernelAux γ f hf hcof ν₀` is invariant. -/
def invariantSet : Set Ω := {ω | γ.IsInvariantCore (paKernelAux γ f hf hcof ν₀ ω)}

lemma measurableSet_invariantSet : MeasurableSet[γ.tail] (invariantSet γ f hf hcof ν₀) :=
  (measurableSet_isInvariantCore γ).preimage (paKernelAux γ f hf hcof ν₀).measurable

open Classical in
/-- **Georgii (7.25)**, abstract form: the `μ`-independent `(𝒢(γ), 𝓣)`-kernel, equal to `ν₀` off
`invariantSet γ f hf hcof ν₀`. -/
noncomputable def paKernel : Kernel[γ.tail] Ω Ω :=
  Kernel.piecewise (measurableSet_invariantSet γ f hf hcof ν₀) (paKernelAux γ f hf hcof ν₀)
    (@Kernel.const Ω Ω γ.tail _ ν₀)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (paKernel γ f hf hcof ν₀) := by
  unfold paKernel; infer_instance

lemma paKernel_mem_invariant (hν₀ : ν₀ ∈ γ.invariant) (ω : Ω) :
    paKernel γ f hf hcof ν₀ ω ∈ γ.invariant := by
  classical
  rw [paKernel, Kernel.piecewise_apply]
  split_ifs with h
  · exact mem_invariant_of_isInvariantCore γ h
  · rw [Kernel.const_apply]; exact hν₀

variable {γ f hf hcof ν₀} {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma ae_paKernel_eq_tailCondKernel [Nonempty ι] (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, paKernel γ f hf hcof ν₀ ω = tailCondKernel γ μ ω := by
  classical
  filter_upwards [ae_tailRealKernel_eq_map μ hf hcof hμ,
    ae_isInvariantCore_tailCondKernel hμ] with ω h1 h2
  have hrange : ω ∈ γ.rangeSet f hf hcof := by
    change γ.tailRealKernel f hf hcof ω (range (embeddingReal Ω)) = 1
    rw [h1, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]
  have haux : paKernelAux γ f hf hcof ν₀ ω = tailCondKernel γ μ ω := by
    rw [paKernelAux, Kernel.comapRight_apply, tailRealKernel', Kernel.piecewise_apply,
      ite_eq_left hrange, h1, (measurableEmbedding_embeddingReal _).comap_map]
  have hgood : ω ∈ invariantSet γ f hf hcof ν₀ := by
    change γ.IsInvariantCore (paKernelAux γ f hf hcof ν₀ ω)
    rw [haux]; exact h2
  rw [paKernel, Kernel.piecewise_apply, ite_eq_left hgood, haux]

/-- Georgii (7.21)(i) for `paKernel`: it is a version of `μ(· | 𝓣)` for every `μ ∈ 𝒢(γ)`. -/
theorem condExp_ae_eq_paKernel [Nonempty ι] (hμ : μ ∈ γ.invariant) {A : Set Ω}
    (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] =ᵐ[μ]
      fun ω ↦ (paKernel γ f hf hcof ν₀ ω).real A := by
  filter_upwards [ae_paKernel_eq_tailCondKernel (ν₀ := ν₀) hμ,
    tailCondKernel_real_ae_eq_condExp (γ := γ) (μ := μ) hA] with ω h1 h2
  rw [h1, ← h2]

end PAKernel

section Main

variable [StandardBorelSpace Ω] [Countable ι] (γ : AbstractSpecification Ω ι) (f : ℕ → ι)
  (hf : Monotone f) (hcof : ∀ i, ∃ n, i ≤ f n) (ν₀ : Measure Ω)

theorem isPAKernel_paKernel [Nonempty ι] (hν₀ : ν₀ ∈ γ.invariant) :
    IsPAKernel γ.invariant γ.tail (paKernel γ f hf hcof ν₀) :=
  ⟨fun μ hμ A hA ↦ by
    have := hμ.1
    exact (condExp_ae_eq_paKernel hμ hA).symm, paKernel_mem_invariant γ f hf hcof ν₀ hν₀⟩

end Main

section Exists

variable [StandardBorelSpace Ω] [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  (γ : AbstractSpecification Ω ι)

/-- **Georgii, Proposition (7.25)** in the setting of Remark (7.13): if `𝒢(γ) ≠ ∅` then there is a
`(𝒢(γ), 𝓣)`-kernel, which can be taken with all its values in `𝒢(γ)`. -/
theorem exists_isPAKernel_invariant (hG : γ.invariant.Nonempty) :
    ∃ π : Kernel[γ.tail] Ω Ω, IsMarkovKernel π ∧ IsPAKernel γ.invariant γ.tail π := by
  obtain ⟨ν₀, hν₀⟩ := hG
  have := hν₀.1
  exact ⟨paKernel γ (cofinalSeq ι) (monotone_cofinalSeq ι) (cofinal_cofinalSeq ι) ν₀,
    inferInstance,
    isPAKernel_paKernel γ (cofinalSeq ι) (monotone_cofinalSeq ι) (cofinal_cofinalSeq ι) ν₀ hν₀⟩

end Exists

end AbstractSpecification

end MeasureTheory.GibbsMeasure

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Abstract
public import GibbsMeasure.Specification.GibbsKernel

/-!
# Georgii, Proposition (7.25) in the abstract setting of Remark (7.13)

For an `AbstractSpecification γ` on a standard Borel space `Ω`, indexed by a countable nonempty
preorder directed upwards, we build a probability kernel `paKernel γ ν₀ : Kernel[γ.tail] Ω Ω`
which does not depend on any invariant measure, is a version of `μ(· | 𝓣)` for every
`μ ∈ 𝒢(γ)`, and takes all its values in `𝒢(γ)`; that is, it is a `(𝒢(γ), 𝓣)`-kernel in the sense
of `IsPAKernel` (Georgii's Definition (7.21)).

The proof follows `GibbsMeasure.gibbsKernel`: along the canonical cofinal sequence `cofinalSeq ι`,
Lévy's downward theorem and the invariance equation identify `lim_n γ_{iₙ}(A | ·)` with
`μ(A | 𝓣)`; applying this to the half-lines `{embeddingReal Ω ≤ q}`, `q : ℚ`, gives a
tail-measurable rational CDF, which `stieltjesOfMeasurableRat` turns into a kernel to `ℝ`, pulled
back to `Ω` by `comapRight`. The bad tail sets are sent to a fixed `ν₀ ∈ 𝒢(γ)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

/-! ### A kernel to `ℝ` built from a rational CDF measurable for a given σ-algebra -/

section RealKernelOfRatCDF

variable {Ω : Type*}

/-- The probability kernel from `Ω` to `ℝ` determined by a rational CDF `f` measurable for a
σ-algebra `𝒜`. This is `stieltjesOfMeasurableRat` packaged as a `Kernel[𝒜]`, with `𝒜` an explicit
argument, so that it applies to a σ-algebra which is not the ambient instance. -/
noncomputable def realKernelOfRatCDF (𝒜 : MeasurableSpace Ω) (f : Ω → ℚ → ℝ)
    (hf : Measurable[𝒜] f) : Kernel[𝒜] Ω ℝ where
  toFun ω := (@stieltjesOfMeasurableRat Ω 𝒜 f hf ω).measure
  measurable' := @measurable_measure_stieltjesOfMeasurableRat Ω f 𝒜 hf

lemma realKernelOfRatCDF_apply (𝒜 : MeasurableSpace Ω) (f : Ω → ℚ → ℝ) (hf : Measurable[𝒜] f)
    (ω : Ω) :
    realKernelOfRatCDF 𝒜 f hf ω = (@stieltjesOfMeasurableRat Ω 𝒜 f hf ω).measure := rfl

instance isMarkovKernel_realKernelOfRatCDF (𝒜 : MeasurableSpace Ω) (f : Ω → ℚ → ℝ)
    (hf : Measurable[𝒜] f) : IsMarkovKernel (realKernelOfRatCDF 𝒜 f hf) :=
  ⟨fun ω ↦ ⟨@measure_stieltjesOfMeasurableRat_univ Ω f 𝒜 hf ω⟩⟩

/-- If a rational CDF agrees at `ω` with the CDF of a probability measure `ν` on `ℝ`, then
`realKernelOfRatCDF` takes the value `ν` at `ω`. -/
lemma realKernelOfRatCDF_eq (𝒜 : MeasurableSpace Ω) {f : Ω → ℚ → ℝ} (hf : Measurable[𝒜] f)
    {ω : Ω} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hω : ∀ q : ℚ, f ω q = ν.real (Iic (q : ℝ))) : realKernelOfRatCDF 𝒜 f hf ω = ν := by
  have hpt : IsRatStieltjesPoint f ω := isRatStieltjesPoint_of_forall_eq_real_Iic ν hω
  have hS : @stieltjesOfMeasurableRat Ω 𝒜 f hf ω = cdf ν := by
    ext x
    rw [← (cdf ν).iInf_rat_gt_eq x]
    change IsMeasurableRatCDF.stieltjesFunctionAux (toRatCDF f) ω x = _
    rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
    refine iInf_congr fun r ↦ ?_
    rw [toRatCDF_of_isRatStieltjesPoint hpt, hω, cdf_eq_real]
  rw [realKernelOfRatCDF_apply, hS, measure_cdf]

end RealKernelOfRatCDF

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

section Filtration

variable [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] (γ : AbstractSpecification Ω ι)

set_option warn.classDefReducibility false in
/-- The decreasing sequence of σ-algebras along the canonical cofinal sequence. -/
noncomputable def subFiltration (n : ℕ) : MeasurableSpace Ω := γ.sub (cofinalSeq ι n)

lemma antitone_subFiltration : Antitone γ.subFiltration :=
  γ.sub_antitone.comp_monotone (monotone_cofinalSeq ι)

lemma subFiltration_le (n : ℕ) : γ.subFiltration n ≤ m := γ.sub_le _

lemma iInf_subFiltration : ⨅ n, γ.subFiltration n = γ.tail :=
  (tail_eq_iInf_of_cofinal (cofinal_cofinalSeq ι)).symm

end Filtration

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

/-! ### The tail limit -/

section TailLimit

variable [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] (γ : AbstractSpecification Ω ι)

/-- The tail limit `lim_n γ_{iₙ}(A | ω)` along the canonical cofinal sequence, defined everywhere
as a `limUnder`. -/
noncomputable def tailLimit (A : Set Ω) (ω : Ω) : ℝ :=
  limUnder atTop fun n ↦ (γ.ker (cofinalSeq ι n) ω A).toReal

lemma measurable_tailLimit {A : Set Ω} (hA : MeasurableSet A) :
    Measurable[γ.tail] (γ.tailLimit A) := by
  rw [← iInf_subFiltration γ]
  refine (stronglyMeasurable_iInf_limUnder_of_antitone (antitone_subFiltration γ)
    (f := fun n ω ↦ (γ.ker (cofinalSeq ι n) ω A).toReal) fun n ↦ ?_).measurable
  exact (Kernel.measurable_coe (γ.ker (cofinalSeq ι n)) hA).ennreal_toReal.stronglyMeasurable

variable {γ}

/-- Lévy's downward theorem: `lim_n γ_{iₙ}(A | ·)` is a version of `μ(A | 𝓣)` for every invariant
probability measure `μ`. -/
lemma tailLimit_ae_eq_condExp {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ γ.invariant)
    {A : Set Ω} (hA : MeasurableSet A) :
    γ.tailLimit A =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] := by
  have hg : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hA
  have h1 := limUnder_condExp_ae_eq_condExp_iInf (μ := μ) (antitone_subFiltration γ)
    (subFiltration_le γ) hg
  rw [iInf_subFiltration γ] at h1
  have h2 : ∀ᵐ ω ∂μ, ∀ n, μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.subFiltration n] ω =
      (γ.ker (cofinalSeq ι n) ω A).toReal :=
    ae_all_iff.2 fun n ↦ condExp_sub_ae_eq hμ (cofinalSeq ι n) hA
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [← h1ω]
  exact congrArg _ (funext fun n ↦ (h2ω n).symm)

end TailLimit

/-! ### The tail-measurable kernel to `ℝ` -/

section RatCDF

variable [StandardBorelSpace Ω] [Nonempty Ω] [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  (γ : AbstractSpecification Ω ι)

/-- The rational tail CDF `ω ↦ (q ↦ lim_n γ_{iₙ}({e ≤ q} | ω))`, where `e = embeddingReal Ω`. -/
noncomputable def tailRatCDF (ω : Ω) (q : ℚ) : ℝ :=
  γ.tailLimit (embeddingReal Ω ⁻¹' Iic (q : ℝ)) ω

omit [Nonempty Ω] in
lemma measurable_tailRatCDF : Measurable[γ.tail] γ.tailRatCDF := by
  have h : ∀ q : ℚ, Measurable[γ.tail] fun ω ↦ γ.tailRatCDF ω q := fun q ↦
    measurable_tailLimit γ (measurableSet_Iic.preimage (measurable_embeddingReal Ω))
  let _ : MeasurableSpace Ω := γ.tail
  exact measurable_pi_iff.2 h

/-- The tail-measurable kernel to `ℝ` obtained from the rational tail CDF. -/
noncomputable def tailRealKernel : Kernel[γ.tail] Ω ℝ :=
  realKernelOfRatCDF γ.tail γ.tailRatCDF (measurable_tailRatCDF γ)

instance : IsMarkovKernel γ.tailRealKernel :=
  isMarkovKernel_realKernelOfRatCDF _ _ _

end RatCDF

/-! ### Identification with the tail conditional kernel -/

section TailCondKernel

variable [StandardBorelSpace Ω] [Nonempty Ω] [Nonempty ι] (γ : AbstractSpecification Ω ι)
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The tail conditional kernel of `μ`, a regular conditional distribution given `𝓣`. -/
noncomputable def tailCondKernel : Kernel[γ.tail] Ω Ω := condExpKernel (mΩ := m) μ γ.tail

instance : IsMarkovKernel (tailCondKernel γ μ) := by
  unfold tailCondKernel; infer_instance

variable {γ μ}

omit [Nonempty Ω] in
lemma tailCondKernel_real_ae_eq_condExp {A : Set Ω} (hA : MeasurableSet A) :
    (fun ω ↦ (tailCondKernel γ μ ω).real A) =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] :=
  condExpKernel_ae_eq_condExp (μ := μ) γ.tail_le hA

omit [Nonempty Ω] in
/-- Tower property: the tail conditional measures of an invariant measure are a.e. fixed by every
`γᵢ` on every measurable set. -/
lemma ae_bind_tailCondKernel_apply_eq (hμ : μ ∈ γ.invariant) (i : ι) {B : Set Ω}
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

section Identification

variable [StandardBorelSpace Ω] [Nonempty Ω] [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  {γ : AbstractSpecification Ω ι} (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [Nonempty Ω] in
lemma ae_forall_tailRatCDF_eq (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, γ.tailRatCDF ω q =
      ((tailCondKernel γ μ ω).map (embeddingReal Ω)).real (Iic (q : ℝ)) := by
  refine ae_all_iff.2 fun q ↦ ?_
  have hA : MeasurableSet (embeddingReal Ω ⁻¹' Iic (q : ℝ)) :=
    measurableSet_Iic.preimage (measurable_embeddingReal _)
  filter_upwards [tailLimit_ae_eq_condExp hμ hA,
    tailCondKernel_real_ae_eq_condExp (γ := γ) (μ := μ) hA] with ω h1 h2
  rw [map_measureReal_apply (measurable_embeddingReal _) measurableSet_Iic]
  exact h1.trans h2.symm

omit [Nonempty Ω] in
lemma ae_tailRealKernel_eq_map (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, γ.tailRealKernel ω = (tailCondKernel γ μ ω).map (embeddingReal Ω) := by
  filter_upwards [ae_forall_tailRatCDF_eq μ hμ] with ω hω
  have : IsProbabilityMeasure ((tailCondKernel γ μ ω).map (embeddingReal Ω)) :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal _).aemeasurable
  exact realKernelOfRatCDF_eq γ.tail (measurable_tailRatCDF γ) _ hω

end Identification

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

end Core

/-! ### The `(𝒢(γ), 𝓣)`-kernel -/

section PAKernel

variable [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace.CountablyGenerated Ω] [Countable ι]
  [Nonempty ι] [IsDirected ι (· ≤ ·)] (γ : AbstractSpecification Ω ι) (ν₀ : Measure Ω)

/-- The tail event on which `γ.tailRealKernel` is carried by the range of `embeddingReal`. -/
def rangeSet : Set Ω := {ω | γ.tailRealKernel ω (range (embeddingReal Ω)) = 1}

omit [Nonempty Ω] [MeasurableSpace.CountablyGenerated Ω] in
lemma measurableSet_rangeSet : MeasurableSet[γ.tail] γ.rangeSet :=
  (measurableSet_singleton 1).preimage
    (Kernel.measurable_coe _ (measurableEmbedding_embeddingReal _).measurableSet_range)

open Classical in
/-- `γ.tailRealKernel`, replaced off `γ.rangeSet` by the pushforward of `ν₀`. -/
noncomputable def tailRealKernel' : Kernel[γ.tail] Ω ℝ :=
  Kernel.piecewise (measurableSet_rangeSet γ) γ.tailRealKernel
    (@Kernel.const Ω ℝ γ.tail _ (ν₀.map (embeddingReal Ω)))

omit [Nonempty Ω] [MeasurableSpace.CountablyGenerated Ω] in
lemma tailRealKernel'_apply_range [IsProbabilityMeasure ν₀] (ω : Ω) :
    tailRealKernel' γ ν₀ ω (range (embeddingReal Ω)) = 1 := by
  classical
  rw [tailRealKernel', Kernel.piecewise_apply]
  split_ifs with h
  · exact h
  · rw [Kernel.const_apply, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]

/-- The candidate `(𝒢(γ), 𝓣)`-kernel, before correction on the bad tail set. -/
noncomputable def paKernelAux : Kernel[γ.tail] Ω Ω :=
  Kernel.comapRight (tailRealKernel' γ ν₀) (measurableEmbedding_embeddingReal Ω)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (paKernelAux γ ν₀) :=
  Kernel.IsMarkovKernel.comapRight _ _ (tailRealKernel'_apply_range γ ν₀)

/-- The tail event on which `paKernelAux γ ν₀` is invariant. -/
def invariantSet : Set Ω := {ω | γ.IsInvariantCore (paKernelAux γ ν₀ ω)}

omit [Nonempty Ω] in
lemma measurableSet_invariantSet : MeasurableSet[γ.tail] (invariantSet γ ν₀) :=
  (measurableSet_isInvariantCore γ).preimage (paKernelAux γ ν₀).measurable

open Classical in
/-- **Georgii (7.25)**, abstract form: the `μ`-independent `(𝒢(γ), 𝓣)`-kernel, equal to `ν₀` off
`invariantSet γ ν₀`. -/
noncomputable def paKernel : Kernel[γ.tail] Ω Ω :=
  Kernel.piecewise (measurableSet_invariantSet γ ν₀) (paKernelAux γ ν₀)
    (@Kernel.const Ω Ω γ.tail _ ν₀)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (paKernel γ ν₀) := by
  unfold paKernel; infer_instance

omit [Nonempty Ω] in
lemma paKernel_mem_invariant (hν₀ : ν₀ ∈ γ.invariant) (ω : Ω) : paKernel γ ν₀ ω ∈ γ.invariant := by
  classical
  rw [paKernel, Kernel.piecewise_apply]
  split_ifs with h
  · exact mem_invariant_of_isInvariantCore γ h
  · rw [Kernel.const_apply]; exact hν₀

variable {γ ν₀} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Nonempty Ω] in
lemma ae_paKernel_eq_tailCondKernel (hμ : μ ∈ γ.invariant) :
    ∀ᵐ ω ∂μ, paKernel γ ν₀ ω = tailCondKernel γ μ ω := by
  classical
  have hcore : ∀ᵐ ω ∂μ, γ.IsInvariantCore (tailCondKernel γ μ ω) := by
    have h : ∀ᵐ ω ∂μ, ∀ (i : ι) (t : Finset ℕ),
        ((tailCondKernel γ μ ω).bind (γ.ker i)) (piNatGen (Ω := Ω) t) =
          tailCondKernel γ μ ω (piNatGen (Ω := Ω) t) :=
      ae_all_iff.2 fun i ↦ ae_all_iff.2 fun t ↦
        ae_bind_tailCondKernel_apply_eq hμ i (measurableSet_piNatGen t)
    filter_upwards [h] with ω hω
    exact ⟨measure_univ, hω⟩
  filter_upwards [ae_tailRealKernel_eq_map μ hμ, hcore] with ω h1 h2
  have hrange : ω ∈ γ.rangeSet := by
    show γ.tailRealKernel ω (range (embeddingReal Ω)) = 1
    rw [h1, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]
  have haux : paKernelAux γ ν₀ ω = tailCondKernel γ μ ω := by
    rw [paKernelAux, Kernel.comapRight_apply, tailRealKernel', Kernel.piecewise_apply,
      ite_eq_left hrange, h1, (measurableEmbedding_embeddingReal _).comap_map]
  have hgood : ω ∈ invariantSet γ ν₀ := by
    show γ.IsInvariantCore (paKernelAux γ ν₀ ω)
    rw [haux]; exact h2
  rw [paKernel, Kernel.piecewise_apply, ite_eq_left hgood, haux]

omit [Nonempty Ω] in
/-- Georgii (7.21)(i) for `paKernel`: it is a version of `μ(· | 𝓣)` for every `μ ∈ 𝒢(γ)`. -/
theorem condExp_ae_eq_paKernel (hμ : μ ∈ γ.invariant) {A : Set Ω} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | γ.tail] =ᵐ[μ] fun ω ↦ (paKernel γ ν₀ ω).real A := by
  filter_upwards [ae_paKernel_eq_tailCondKernel (ν₀ := ν₀) hμ,
    tailCondKernel_real_ae_eq_condExp (γ := γ) (μ := μ) hA] with ω h1 h2
  rw [h1, ← h2]

end PAKernel

section Main

variable [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace.CountablyGenerated Ω] [Countable ι]
  [Nonempty ι] [IsDirected ι (· ≤ ·)] (γ : AbstractSpecification Ω ι) (ν₀ : Measure Ω)

omit [Nonempty Ω] in
theorem isPAKernel_paKernel (hν₀ : ν₀ ∈ γ.invariant) :
    IsPAKernel γ.invariant γ.tail (paKernel γ ν₀) :=
  ⟨fun μ hμ A hA ↦ by
    have := hμ.1
    exact (condExp_ae_eq_paKernel hμ hA).symm, paKernel_mem_invariant γ ν₀ hν₀⟩

omit [Nonempty Ω] in
/-- **Georgii, Proposition (7.25)** in the setting of Remark (7.13): if `𝒢(γ) ≠ ∅` then there is a
`(𝒢(γ), 𝓣)`-kernel, which can be taken with all its values in `𝒢(γ)`. -/
theorem exists_isPAKernel_invariant (hG : γ.invariant.Nonempty) :
    ∃ π : Kernel[γ.tail] Ω Ω, IsMarkovKernel π ∧ IsPAKernel γ.invariant γ.tail π := by
  obtain ⟨ν₀, hν₀⟩ := hG
  have := hν₀.1
  exact ⟨paKernel γ ν₀, inferInstance, isPAKernel_paKernel γ ν₀ hν₀⟩

end Main

end AbstractSpecification

end MeasureTheory.GibbsMeasure

end

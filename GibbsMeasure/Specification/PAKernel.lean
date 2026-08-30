/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.ChoquetLaw
public import GibbsMeasure.Specification.Structure

/-!
# Georgii, Definition (7.21) and Proposition (7.22): `(P, 𝒜)`-kernels and the unique
representation of measures as mixtures of `𝒜`-trivial measures.

Setting: a measurable space `Ω` with countably generated σ-algebra, a sub-σ-algebra `𝒜`,
a nonempty set `P` of probability measures on `Ω`, and a Markov kernel `π : Kernel[𝒜] Ω Ω`.
Weights live in `Measure (Measure Ω)`; the representation `μ = ∫ ν w(dν)` is `Measure.join w = μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

-- `𝒜` is declared before the ambient `m` so that `m` is the default instance on `Ω`.
variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [m : MeasurableSpace Ω]

/-- Georgii's `P_𝒜`: the measures that are trivial (0-1 valued) on the sub-σ-algebra `𝒜`. -/
def trivialOn (𝒜 : MeasurableSpace Ω) : Set (Measure[m] Ω) :=
  {μ | ∀ A, MeasurableSet[𝒜] A → μ A = 0 ∨ μ A = 1}

omit m in
lemma mem_trivialOn [m : MeasurableSpace Ω] {μ : Measure[m] Ω} :
    μ ∈ trivialOn 𝒜 ↔ ∀ A, MeasurableSet[𝒜] A → μ A = 0 ∨ μ A = 1 := Iff.rfl

omit m in
/-- Tail-triviality (`IsTailTrivial`) is `trivialOn` for the tail σ-algebra. -/
lemma isTailTrivial_iff_mem_trivialOn {S E : Type*} [MeasurableSpace E]
    (μ : ProbabilityMeasure (S → E)) :
    IsTailTrivial μ ↔ (μ : Measure (S → E)) ∈ trivialOn (tailSigmaAlgebra S E) := Iff.rfl

/-- Georgii Definition (7.21): a `(P, 𝒜)`-kernel is a probability kernel from `(Ω, 𝒜)` to
`(Ω, m)` which is a version of `μ(· | 𝒜)` for every `μ ∈ P`, and whose values lie in `P`
(Georgii's normalisation `Ω_P = Ω`). -/
def IsPAKernel (P : Set (Measure[m] Ω)) (𝒜 : MeasurableSpace Ω) (π : Kernel[𝒜, m] Ω Ω) : Prop :=
  (∀ μ ∈ P, ∀ A, MeasurableSet[m] A →
      (fun ω ↦ (π ω).real A) =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ∧
    ∀ ω, π ω ∈ P

section Kernel

variable {P : Set (Measure Ω)} {π : Kernel[𝒜] Ω Ω} [IsMarkovKernel π]

omit [IsMarkovKernel π] in
lemma measurable_kernel_of_le (h𝒜 : 𝒜 ≤ m) : Measurable π :=
  π.measurable.mono h𝒜 le_rfl

omit [IsMarkovKernel π] in
lemma measurable_kernel_coe_of_le (h𝒜 : 𝒜 ≤ m) {A : Set Ω} (hA : MeasurableSet A) :
    Measurable fun ω ↦ π ω A :=
  (π.measurable_coe hA).mono h𝒜 le_rfl

omit [IsMarkovKernel π] in
/-- A real function is a.e. equal to `c` as soon as the countably many level sets below/above
rationals on the wrong side of `c` are null. -/
lemma ae_eq_const_of_forall_rat {ν : Measure Ω} {f : Ω → ℝ} {c : ℝ}
    (h : ∀ q : ℚ, ((q : ℝ) ≤ c → ν {ω | f ω < q} = 0) ∧ (c < q → ν {ω | (q : ℝ) ≤ f ω} = 0)) :
    ∀ᵐ ω ∂ν, f ω = c := by
  rw [ae_iff]
  have hsub : {ω | ¬ f ω = c} ⊆
      (⋃ q : ℚ, {ω | f ω < q ∧ (q : ℝ) ≤ c}) ∪ ⋃ q : ℚ, {ω | (q : ℝ) ≤ f ω ∧ c < q} := by
    intro ω hω
    rcases lt_or_gt_of_ne hω with hlt | hgt
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
      exact Or.inl (mem_iUnion.2 ⟨q, hq1, hq2.le⟩)
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hgt
      exact Or.inr (mem_iUnion.2 ⟨q, hq2.le, hq1⟩)
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun q ↦ ?_)
    (measure_iUnion_null fun q ↦ ?_))
  · by_cases hq : (q : ℝ) ≤ c
    · exact measure_mono_null (fun ω hω ↦ hω.1) ((h q).1 hq)
    · have : {ω | f ω < q ∧ (q : ℝ) ≤ c} = ∅ := by ext ω; simp [hq]
      simp [this]
  · by_cases hq : c < q
    · exact measure_mono_null (fun ω hω ↦ hω.1) ((h q).2 hq)
    · have : {ω | (q : ℝ) ≤ f ω ∧ c < q} = ∅ := by ext ω; simp [hq]
      simp [this]

/-- `{ω | π(· | ω) = ν}` is `𝒜`-measurable for a probability measure `ν`. -/
lemma measurableSet_eq_measure [MeasurableSpace.CountablyGenerated Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] : MeasurableSet[𝒜] {ω | π ω = ν} := by
  have hset : {ω | π ω = ν} = ⋂ t : Finset ℕ, {ω | π ω (piNatGen t) = ν (piNatGen t)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    refine ⟨fun h t ↦ by rw [h], fun h ↦ ?_⟩
    refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
      generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
    rintro s ⟨t, rfl⟩
    exact h t
  rw [hset]
  exact MeasurableSet.iInter fun t ↦
    (measurableSet_singleton _).preimage (π.measurable_coe (measurableSet_piNatGen t))

namespace IsPAKernel

variable (hπ : IsPAKernel P 𝒜 π) (h𝒜 : 𝒜 ≤ m)
include hπ h𝒜

/-- `∫ π(A | ω) μ(dω) = μ(A)` for `μ ∈ P`. -/
lemma lintegral_apply_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P)
    {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ ω, π ω A ∂μ = μ A := by
  have : SigmaFinite (μ.trim h𝒜) := by infer_instance
  have hreal : ∫ ω, (π ω).real A ∂μ = μ.real A := by
    calc ∫ ω, (π ω).real A ∂μ
        = ∫ ω, (μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ω ∂μ := integral_congr_ae (hπ.1 μ hμ A hA)
      _ = ∫ ω, A.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ := integral_condExp h𝒜
      _ = μ.real A := by simp [integral_indicator_const _ hA]
  have hmeas : Measurable fun ω ↦ π ω A := measurable_kernel_coe_of_le h𝒜 hA
  have htoReal : ∫ ω, (π ω).real A ∂μ = (∫⁻ ω, π ω A ∂μ).toReal := by
    simp only [measureReal_def]
    exact integral_toReal hmeas.aemeasurable (Eventually.of_forall fun ω ↦ measure_lt_top _ _)
  have hne : ∫⁻ ω, π ω A ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂μ) (by simp) ?_
    exact lintegral_mono fun ω ↦ prob_le_one
  rw [htoReal, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hne (measure_ne_top _ _)).1 hreal

/-- `μ.bind π = μ` for `μ ∈ P` (Georgii's `μπ = μ`). -/
lemma bind_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P) : μ.bind π = μ := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_kernel_of_le h𝒜).aemeasurable]
  exact hπ.lintegral_apply_eq h𝒜 hμ hA

/-- On `𝒜`-measurable sets, `π(B | ω) = 1_B(ω)` for `μ`-a.e. `ω`, `μ ∈ P`. -/
lemma ae_apply_eq_indicator {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P)
    {B : Set Ω} (hB : MeasurableSet[𝒜] B) :
    ∀ᵐ ω ∂μ, π ω B = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  have : SigmaFinite (μ.trim h𝒜) := by infer_instance
  have hB' : MeasurableSet B := h𝒜 _ hB
  have hcond : μ[B.indicator (fun _ ↦ (1 : ℝ)) | 𝒜] = B.indicator (fun _ ↦ (1 : ℝ)) :=
    condExp_of_stronglyMeasurable h𝒜 (stronglyMeasurable_const.indicator hB)
      ((integrable_const _).indicator hB')
  filter_upwards [hπ.1 μ hμ B hB'] with ω hω
  rw [hcond] at hω
  by_cases hωB : ω ∈ B
  · simp only [indicator_of_mem hωB, measureReal_def] at hω ⊢
    exact (ENNReal.toReal_eq_one_iff _).1 hω
  · simp only [indicator_of_notMem hωB, measureReal_def] at hω ⊢
    exact ((ENNReal.toReal_eq_zero_iff _).1 hω).resolve_right (measure_ne_top _ _)

/-- (7.23), first half: if `μ ∈ P` is trivial on `𝒜` then `π(A | ·) = μ(A)` `μ`-a.e. -/
lemma ae_apply_eq_of_mem_trivialOn {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P)
    (htriv : μ ∈ trivialOn 𝒜) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, π ω A = μ A := by
  set g : Ω → ℝ≥0∞ := fun ω ↦ π ω A with hg
  have hg𝒜 : Measurable[𝒜] g := π.measurable_coe hA
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, g =ᵐ[μ] fun _ ↦ c := by
    refine Filter.exists_eventuallyEq_const_of_forall_separating (l := ae μ) (f := g)
      MeasurableSet fun U hU ↦ ?_
    have hpre : MeasurableSet[𝒜] (g ⁻¹' U) := hg𝒜 hU
    rcases htriv _ hpre with h0 | h1
    · right
      rw [ae_iff]
      simp only [not_not]
      exact h0
    · left
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff (h𝒜 _ hpre)).2 h1
  have hint : ∫⁻ ω, g ω ∂μ = μ A := hπ.lintegral_apply_eq h𝒜 hμ hA
  have hc' : c = μ A := by
    rw [← hint, lintegral_congr_ae hc]
    simp
  filter_upwards [hc] with ω hω
  simpa [hc'] using hω

lemma ae_eq_of_mem_trivialOn [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) (htriv : μ ∈ trivialOn 𝒜) :
    ∀ᵐ ω ∂μ, π ω = μ := by
  have h : ∀ᵐ ω ∂μ, ∀ t : Finset ℕ, π ω (piNatGen t) = μ (piNatGen t) :=
    ae_all_iff.2 fun t ↦ hπ.ae_apply_eq_of_mem_trivialOn h𝒜 hμ htriv (measurableSet_piNatGen t)
  filter_upwards [h] with ω hω
  refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
    generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
  rintro s ⟨t, rfl⟩
  exact hω t

/-- (7.23), second half: if `π(· | ω) = μ` for `μ`-a.e. `ω` then `μ` is trivial on `𝒜`. -/
lemma mem_trivialOn_of_ae_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P)
    (h : ∀ᵐ ω ∂μ, π ω = μ) : μ ∈ trivialOn 𝒜 := by
  intro B hB
  have h2 : ∀ᵐ ω ∂μ, μ B = B.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
    filter_upwards [h, hπ.ae_apply_eq_indicator h𝒜 hμ hB] with ω hω h1ω
    rw [← hω]
    exact h1ω
  have : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨ω, hω⟩ := h2.exists
  by_cases hωB : ω ∈ B
  · right
    simpa [indicator_of_mem hωB] using hω
  · left
    simpa [indicator_of_notMem hωB] using hω

/-- Georgii (7.23): for `μ ∈ P`, `μ` is trivial on `𝒜` iff `π(· | ω) = μ` for `μ`-a.e. `ω`. -/
lemma mem_trivialOn_iff_ae_eq [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    μ ∈ trivialOn 𝒜 ↔ ∀ᵐ ω ∂μ, π ω = μ :=
  ⟨hπ.ae_eq_of_mem_trivialOn h𝒜 hμ, hπ.mem_trivialOn_of_ae_eq h𝒜 hμ⟩

/-- Georgii (7.23): for `μ ∈ P`, `μ` is trivial on `𝒜` iff `μ {π(· | ω) = μ} = 1`. -/
lemma mem_trivialOn_iff_measure_eq_one [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    μ ∈ trivialOn 𝒜 ↔ μ {ω | π ω = μ} = 1 := by
  rw [hπ.mem_trivialOn_iff_ae_eq h𝒜 hμ,
    ← prob_compl_eq_zero_iff (h𝒜 _ (measurableSet_eq_measure (π := π) μ)), ae_iff]
  rfl

/-- Step 2 of (7.22): for `μ ∈ P` and `μ`-a.e. `ω`, `π(A | ·)` is `π(· | ω)`-a.e. equal to
`π(A | ω)` (i.e. the variance `v_A(π(· | ω))` vanishes). -/
lemma ae_ae_apply_eq {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P) {A : Set Ω}
    (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, ∀ᵐ ω' ∂(π ω), π ω' A = π ω A := by
  set f : Ω → ℝ := fun ω ↦ (π ω).real A with hf
  have hf𝒜 : Measurable[𝒜] f := by
    simp only [hf, measureReal_def]
    exact (π.measurable_coe hA).ennreal_toReal
  have hlt (q : ℚ) : MeasurableSet[𝒜] {ω | f ω < q} := measurableSet_lt hf𝒜 measurable_const
  have hle (q : ℚ) : MeasurableSet[𝒜] {ω | (q : ℝ) ≤ f ω} := measurableSet_le measurable_const hf𝒜
  have h : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      π ω {ω' | f ω' < q} = {ω' | f ω' < q}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∧
      π ω {ω' | (q : ℝ) ≤ f ω'} = {ω' | (q : ℝ) ≤ f ω'}.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω :=
    ae_all_iff.2 fun q ↦
      (hπ.ae_apply_eq_indicator h𝒜 hμ (hlt q)).and (hπ.ae_apply_eq_indicator h𝒜 hμ (hle q))
  filter_upwards [h] with ω hω
  have hreal : ∀ᵐ ω' ∂(π ω), f ω' = f ω := by
    refine ae_eq_const_of_forall_rat fun q ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
    · rw [(hω q).1]
      exact indicator_of_notMem (by simpa using not_lt.2 hq) _
    · rw [(hω q).2]
      exact indicator_of_notMem (by simpa using not_le.2 hq) _
  filter_upwards [hreal] with ω' hω'
  simp only [hf, measureReal_def] at hω'
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hω'

lemma ae_ae_eq [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hμ : μ ∈ P) :
    ∀ᵐ ω ∂μ, ∀ᵐ ω' ∂(π ω), π ω' = π ω := by
  have h : ∀ᵐ ω ∂μ, ∀ t : Finset ℕ, ∀ᵐ ω' ∂(π ω), π ω' (piNatGen t) = π ω (piNatGen t) :=
    ae_all_iff.2 fun t ↦ hπ.ae_ae_apply_eq h𝒜 hμ (measurableSet_piNatGen t)
  filter_upwards [h] with ω hω
  filter_upwards [ae_all_iff.2 hω] with ω' hω'
  refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
    generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
  rintro s ⟨t, rfl⟩
  exact hω' t

/-- Step 2 of (7.22): `μ(π(· | ω) ∈ P_𝒜) = 1` for `μ ∈ P`. -/
lemma ae_mem_trivialOn [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    ∀ᵐ ω ∂μ, π ω ∈ trivialOn 𝒜 := by
  filter_upwards [hπ.ae_ae_eq h𝒜 hμ] with ω hω
  exact hπ.mem_trivialOn_of_ae_eq h𝒜 (hπ.2 ω) hω

end IsPAKernel

/-! ### A measurable core for `P_𝒜` and the weight `w_μ` -/

omit [IsMarkovKernel π] in
/-- The identity on measures, truncated to a finite kernel `Measure Ω → Measure Ω`. -/
noncomputable def truncKernel (Ω : Type*) [m : MeasurableSpace Ω] : Kernel (Measure[m] Ω) Ω where
  toFun ν := if ν univ ≤ 1 then ν else 0
  measurable' := Measurable.ite
    (measurableSet_le (Measure.measurable_coe MeasurableSet.univ) measurable_const)
    measurable_id measurable_const

omit [IsMarkovKernel π] in
lemma truncKernel_apply (ν : Measure Ω) : truncKernel Ω ν = if ν univ ≤ 1 then ν else 0 := rfl

instance : IsFiniteKernel (truncKernel Ω) :=
  ⟨⟨1, ENNReal.one_lt_top, fun ν ↦ by
    rw [truncKernel_apply]
    split_ifs with h
    · exact h
    · simp⟩⟩

/-- The set of probability measures `ν` with `π(· | ω) = ν` for `ν`-a.e. `ω`.  By (7.23) it cuts
out `trivialOn 𝒜` inside `P`; unlike `trivialOn 𝒜` it is measurable in `Measure Ω`. -/
def fixedCore (π : Kernel[𝒜, m] Ω Ω) : Set (Measure[m] Ω) :=
  {ν | ν univ = 1 ∧ ∀ᵐ ω ∂ν, π ω = ν}

lemma measurableSet_fixedCore [MeasurableSpace.CountablyGenerated Ω] (h𝒜 : 𝒜 ≤ m) :
    MeasurableSet (fixedCore π) := by
  let t : Set (Measure Ω × Ω) := {p | ∀ s : Finset ℕ, π p.2 (piNatGen s) = p.1 (piNatGen s)}
  have ht : MeasurableSet t := by
    simp only [t, ofPred_forall]
    refine MeasurableSet.iInter fun s ↦ ?_
    exact measurableSet_eq_fun
      ((measurable_kernel_coe_of_le h𝒜 (measurableSet_piNatGen s)).comp measurable_snd)
      ((Measure.measurable_coe (measurableSet_piNatGen s)).comp measurable_fst)
  have hset : fixedCore π =
      {ν | ν univ = 1} ∩ {ν | truncKernel Ω ν (Prod.mk ν ⁻¹' tᶜ) = 0} := by
    ext ν
    simp only [fixedCore, mem_ofPred_eq, mem_inter_iff]
    refine and_congr_right fun h1 ↦ ?_
    have : IsProbabilityMeasure ν := ⟨h1⟩
    have hκ : truncKernel Ω ν = ν := by simp [truncKernel_apply, h1]
    have hpre : Prod.mk ν ⁻¹' tᶜ = {ω | ¬ π ω = ν} := by
      ext ω
      simp only [mem_preimage, mem_compl_iff, mem_ofPred_eq, t]
      refine ⟨fun h heq ↦ h fun s ↦ by rw [heq], fun h h' ↦ h ?_⟩
      refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet Ω)
        generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
      rintro s ⟨u, rfl⟩
      exact h' u
    rw [hκ, hpre, ae_iff]
  rw [hset]
  exact ((measurableSet_singleton 1).preimage (Measure.measurable_coe MeasurableSet.univ)).inter
    ((measurableSet_singleton 0).preimage (Kernel.measurable_kernel_prodMk_left ht.compl))

/-- Step 3 of (7.22): the weight `w_μ = μ(π(· | ·) ∈ ·)`, the law of `ω ↦ π(· | ω)` under `μ`. -/
noncomputable def weight (π : Kernel[𝒜, m] Ω Ω) (μ : Measure[m] Ω) : Measure (Measure[m] Ω) :=
  μ.map π

omit [IsMarkovKernel π] in
lemma weight_apply (h𝒜 : 𝒜 ≤ m) (μ : Measure Ω) {M : Set (Measure Ω)} (hM : MeasurableSet M) :
    weight π μ M = μ (π ⁻¹' M) :=
  Measure.map_apply (measurable_kernel_of_le h𝒜) hM

omit [IsMarkovKernel π] in
lemma isProbabilityMeasure_weight (h𝒜 : 𝒜 ≤ m) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (weight π μ) :=
  Measure.isProbabilityMeasure_map (measurable_kernel_of_le h𝒜).aemeasurable

namespace IsPAKernel

variable (hπ : IsPAKernel P 𝒜 π) (h𝒜 : 𝒜 ≤ m)
include hπ h𝒜

lemma mem_fixedCore_iff [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    μ ∈ fixedCore π ↔ μ ∈ trivialOn 𝒜 := by
  rw [hπ.mem_trivialOn_iff_ae_eq h𝒜 hμ]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨measure_univ, h⟩⟩

lemma ae_mem_fixedCore [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    ∀ᵐ ω ∂μ, π ω ∈ fixedCore π := by
  filter_upwards [hπ.ae_ae_eq h𝒜 hμ] with ω hω
  exact ⟨measure_univ, hω⟩

/-- Step 3 of (7.22): `w_μ` represents `μ`, i.e. `∫ ν w_μ(dν) = μ`. -/
lemma join_weight {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    Measure.join (weight π μ) = μ :=
  hπ.bind_eq h𝒜 hμ

lemma weight_fixedCore_compl [MeasurableSpace.CountablyGenerated Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    weight π μ (fixedCore π)ᶜ = 0 := by
  rw [weight_apply h𝒜 μ (measurableSet_fixedCore h𝒜).compl]
  exact ae_iff.1 (hπ.ae_mem_fixedCore h𝒜 hμ)

/-- Step 3 of (7.22): `w_μ` is concentrated on `P_𝒜 = P ∩ trivialOn 𝒜`. -/
lemma weight_compl_eq_zero [MeasurableSpace.CountablyGenerated Ω] (hPm : MeasurableSet P)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hμ : μ ∈ P) :
    weight π μ (P ∩ trivialOn 𝒜)ᶜ = 0 := by
  have hsub : (P ∩ trivialOn 𝒜)ᶜ ⊆ (P ∩ fixedCore π)ᶜ := by
    intro ν hν hν'
    have : IsProbabilityMeasure ν := ⟨hν'.2.1⟩
    exact hν ⟨hν'.1, (hπ.mem_fixedCore_iff h𝒜 hν'.1).1 hν'.2⟩
  refine measure_mono_null hsub ?_
  rw [weight_apply h𝒜 μ (hPm.inter (measurableSet_fixedCore h𝒜)).compl]
  refine ae_iff.1 ?_
  filter_upwards [hπ.ae_mem_fixedCore h𝒜 hμ] with ω hω
  exact ⟨hπ.2 ω, hω⟩

/-- Step 4 of (7.22): for `ν ∈ P_𝒜`, `ν(π(· | ·) ∈ M) = 1_M(ν)`. -/
lemma measure_preimage_eq_indicator [MeasurableSpace.CountablyGenerated Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (hν : ν ∈ P) (htriv : ν ∈ trivialOn 𝒜) {M : Set (Measure Ω)}
    (hM : MeasurableSet M) :
    ν (π ⁻¹' M) = M.indicator 1 ν := by
  have hae := ae_iff.1 (hπ.ae_eq_of_mem_trivialOn h𝒜 hν htriv)
  by_cases hνM : ν ∈ M
  · rw [indicator_of_mem hνM, Pi.one_apply, ← prob_compl_eq_zero_iff (h𝒜 _ (π.measurable hM))]
    refine measure_mono_null ?_ hae
    intro ω hω hωeq
    exact hω (by rw [mem_preimage, hωeq]; exact hνM)
  · rw [indicator_of_notMem hνM]
    refine measure_mono_null ?_ hae
    intro ω hω hωeq
    exact hνM (by rw [← hωeq]; exact hω)

/-- Step 4 of (7.22), uniqueness: a weight concentrated on `P_𝒜` representing `μ` is `w_μ`. -/
theorem eq_weight_of_join_eq [MeasurableSpace.CountablyGenerated Ω]
    (hP : ∀ μ ∈ P, IsProbabilityMeasure μ) {μ : Measure Ω} {w : Measure (Measure Ω)}
    (hw : ∀ᵐ ν ∂w, ν ∈ P ∩ trivialOn 𝒜) (hjoin : Measure.join w = μ) :
    w = weight π μ := by
  ext M hM
  have hpre : MeasurableSet (π ⁻¹' M) := h𝒜 _ (π.measurable hM)
  calc w M = ∫⁻ ν, M.indicator 1 ν ∂w := (lintegral_indicator_one hM).symm
    _ = ∫⁻ ν, ν (π ⁻¹' M) ∂w := by
        refine lintegral_congr_ae ?_
        filter_upwards [hw] with ν hν
        have : IsProbabilityMeasure ν := hP ν hν.1
        exact (hπ.measure_preimage_eq_indicator h𝒜 hν.1 hν.2 hM).symm
    _ = Measure.join w (π ⁻¹' M) := (Measure.join_apply hpre).symm
    _ = μ (π ⁻¹' M) := by rw [hjoin]
    _ = weight π μ M := (weight_apply h𝒜 μ hM).symm

/-- Georgii (7.22): `P_𝒜 ≠ ∅`. -/
lemma nonempty_inter_trivialOn [MeasurableSpace.CountablyGenerated Ω]
    (hP : ∀ μ ∈ P, IsProbabilityMeasure μ) (hne : P.Nonempty) :
    (P ∩ trivialOn 𝒜).Nonempty := by
  obtain ⟨μ, hμ⟩ := hne
  have := hP μ hμ
  have : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  obtain ⟨ω, hω⟩ := (hπ.ae_mem_trivialOn h𝒜 hμ).exists
  exact ⟨π ω, hπ.2 ω, hω⟩

/-- **Georgii, Proposition (7.22)**: for `μ ∈ P` there is a unique probability weight `w` on
`Measure Ω`, concentrated on `P_𝒜 = P ∩ trivialOn 𝒜`, with `∫ ν w(dν) = μ`; it is `weight π μ`.
`P` is assumed measurable in the Giry σ-algebra (automatic for `P = G γ`). -/
theorem exists_unique_representing_weight [MeasurableSpace.CountablyGenerated Ω]
    (hP : ∀ μ ∈ P, IsProbabilityMeasure μ) (hPm : MeasurableSet P) {μ : Measure Ω} (hμ : μ ∈ P) :
    ∃! w : Measure (Measure Ω),
      IsProbabilityMeasure w ∧ w (P ∩ trivialOn 𝒜)ᶜ = 0 ∧ Measure.join w = μ := by
  have := hP μ hμ
  refine ⟨weight π μ, ⟨isProbabilityMeasure_weight h𝒜 μ, hπ.weight_compl_eq_zero h𝒜 hPm hμ,
    hπ.join_weight h𝒜 hμ⟩, ?_⟩
  rintro w ⟨_, hw, hjoin⟩
  exact hπ.eq_weight_of_join_eq h𝒜 hP (ae_iff.2 hw) hjoin

end IsPAKernel

end Kernel

end MeasureTheory.GibbsMeasure

end

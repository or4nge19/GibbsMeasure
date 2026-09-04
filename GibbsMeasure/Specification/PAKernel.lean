/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Abstract
public import GibbsMeasure.Specification.ChoquetLaw
public import GibbsMeasure.Specification.Structure

/-!
# Georgii, Definition (7.21) and Proposition (7.22): `(P, 𝒜)`-kernels and the unique
representation of measures as mixtures of `𝒜`-trivial measures.

Setting: a measurable space `Ω` with countably generated σ-algebra, a sub-σ-algebra `𝒜`,
a nonempty set `P` of probability measures on `Ω`, and a Markov kernel `π : Kernel[𝒜] Ω Ω`.
Weights live in `Measure (Measure Ω)`; the representation `μ = ∫ ν w(dν)` is `Measure.join w = μ`.

The second half of the file (namespace `IsPAKernel`, sections `Abstract` and `Density`) is the
extreme decomposition governed by a `(P, 𝒜)`-kernel: Theorem (7.26) and Corollaries (7.28),
(7.29), (7.30) for any measurable `P` with `ex P = P ∩ P_𝒜`. The Chapter 7 statements for
`P = 𝒢(γ)`, `𝒜 = 𝓣` and the Chapter 14 statements for `P = 𝓟_Θ`, `𝒢_Θ(γ)`, `𝒜 = 𝓘` are
instances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology symmDiff

namespace MeasureTheory.GibbsMeasure

-- `𝒜` is declared before the ambient `m` so that `m` is the default instance on `Ω`.
variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [m : MeasurableSpace Ω]

/-- Georgii Definition (7.21): a `(P, 𝒜)`-kernel is a probability kernel from `(Ω, 𝒜)` to
`(Ω, m)` which is a version of `μ(· | 𝒜)` for every `μ ∈ P`, and whose values lie in `P`
(Georgii's normalisation `Ω_P = Ω`). This predicate records only the last two conditions;
Markov-ness of `π` is carried separately, by the `[IsMarkovKernel π]` hypothesis of the lemmas
below. -/
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

/-- `∫_A π(B | ω) μ(dω) = μ(A ∩ B)` for `A ∈ 𝒜`, `μ ∈ P`. -/
lemma setLIntegral_apply_eq {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) {A : Set Ω} (hA : MeasurableSet[𝒜] A) {B : Set Ω}
    (hB : MeasurableSet B) :
    ∫⁻ ω in A, π ω B ∂μ = μ (A ∩ B) := by
  have : SigmaFinite (μ.trim h𝒜) := inferInstance
  have hA' : MeasurableSet A := h𝒜 _ hA
  have hreal : ∫ ω in A, (π ω).real B ∂μ = μ.real (A ∩ B) := by
    calc ∫ ω in A, (π ω).real B ∂μ
        = ∫ ω in A, (μ[B.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ω ∂μ :=
          integral_congr_ae (ae_restrict_of_ae (hπ.1 μ hμ B hB))
      _ = ∫ ω in A, B.indicator (fun _ ↦ (1 : ℝ)) ω ∂μ :=
          setIntegral_condExp h𝒜 ((integrable_const _).indicator hB) hA
      _ = μ.real (A ∩ B) := by
          rw [integral_indicator hB, Measure.restrict_restrict hB, setIntegral_const, smul_eq_mul,
            mul_one, Set.inter_comm]
  have hmeas : Measurable fun ω ↦ π ω B := measurable_kernel_coe_of_le h𝒜 hB
  have htoReal : ∫ ω in A, (π ω).real B ∂μ = (∫⁻ ω in A, π ω B ∂μ).toReal := by
    simp only [measureReal_def]
    exact integral_toReal hmeas.aemeasurable (Eventually.of_forall fun ω ↦ measure_lt_top _ _)
  have hne : ∫⁻ ω in A, π ω B ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in A, (1 : ℝ≥0∞) ∂μ) (by simp) ?_
    exact lintegral_mono fun ω ↦ prob_le_one
  rw [htoReal, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' hne (measure_ne_top _ _)).1 hreal

/-- `∫_A π(F | ω) μ(dω) = ∫_A F dμ` for `A ∈ 𝒜`, `μ ∈ P` and measurable `F ≥ 0`: a `(P, 𝒜)`-kernel
is a version of the conditional expectation `μ(· | 𝒜)` on nonnegative functions. -/
lemma setLIntegral_lintegral_eq {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hμ : μ ∈ P) {A : Set Ω} (hA : MeasurableSet[𝒜] A) {F : Ω → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ ω in A, ∫⁻ ω', F ω' ∂(π ω) ∂μ = ∫⁻ ω in A, F ω ∂μ := by
  refine Measurable.ennreal_induction
    (motive := fun F ↦ ∫⁻ ω in A, ∫⁻ ω', F ω' ∂(π ω) ∂μ = ∫⁻ ω in A, F ω ∂μ) ?_ ?_ ?_ hF
  · intro c B hB
    simp_rw [lintegral_indicator_const hB]
    rw [lintegral_const_mul _ (measurable_kernel_coe_of_le h𝒜 hB),
      hπ.setLIntegral_apply_eq h𝒜 hμ hA hB, Measure.restrict_apply hB, Set.inter_comm]
  · intro f g _ hf hg ihf ihg
    have hf' : Measurable fun ω ↦ ∫⁻ ω', f ω' ∂(π ω) :=
      (Measurable.lintegral_kernel hf).mono h𝒜 le_rfl
    simp_rw [Pi.add_apply, lintegral_add_left hf]
    rw [lintegral_add_left hf', ihf, ihg]
  · intro f hfm hfmono ih
    have hf' : ∀ n, Measurable fun ω ↦ ∫⁻ ω', f n ω' ∂(π ω) := fun n ↦
      (Measurable.lintegral_kernel (hfm n)).mono h𝒜 le_rfl
    simp_rw [lintegral_iSup hfm hfmono]
    rw [lintegral_iSup hf' fun a b hab ω ↦ lintegral_mono fun ω' ↦ hfmono hab ω']
    exact iSup_congr ih

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

/-! ### Giry-monad helpers -/

section GiryHelpers

variable {X : Type*} [MeasurableSpace X]

/-- The join of a finite combination of Dirac masses is the corresponding combination. -/
lemma join_finset_sum_smul_dirac {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0∞) (ν : ι → Measure X) :
    Measure.join (∑ i ∈ s, c i • Measure.dirac (ν i)) = ∑ i ∈ s, c i • ν i := by
  ext A hA
  rw [Measure.join_apply hA, lintegral_finsetSum_measure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (Measure.measurable_coe hA), Measure.smul_apply]

variable [MeasurableSpace.CountablyGenerated X]

/-- In a countably generated space, the singleton of a probability measure is measurable in
`Measure X` (Georgii's remark (iii) on the evaluation σ-algebra). -/
lemma measurableSet_singleton_measure (ν : Measure X) [IsProbabilityMeasure ν] :
    MeasurableSet ({ν} : Set (Measure X)) := by
  have hset : ({ν} : Set (Measure X)) =
      {ρ : Measure X | ρ univ = 1} ∩
        ⋂ t : Finset ℕ, {ρ : Measure X | ρ (piNatGen (Ω := X) t) = ν (piNatGen (Ω := X) t)} := by
    ext ρ
    simp only [mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro rfl
      exact ⟨measure_univ, fun t ↦ rfl⟩
    · rintro ⟨hρuniv, hρ⟩
      have : IsProbabilityMeasure ρ := ⟨hρuniv⟩
      refine Measure.ext_of_generate_finite_of_isProbabilityMeasure (C := piNatGenSet X)
        generateFrom_piNatGenSet.symm isPiSystem_piNatGenSet ?_
      rintro s ⟨t, rfl⟩
      exact hρ t
  rw [hset]
  exact ((measurableSet_singleton 1).preimage (Measure.measurable_coe MeasurableSet.univ)).inter
    (MeasurableSet.iInter fun t ↦ (measurableSet_singleton _).preimage
      (Measure.measurable_coe (measurableSet_piNatGen t)))

/-- A weight carried by a finite set of probability measures is a finite combination of Dirac
masses. -/
lemma eq_sum_smul_dirac (w : Measure (Measure X)) (T : Finset (Measure X))
    (hT : ∀ ν ∈ T, IsProbabilityMeasure ν) (hw : w ((↑T : Set (Measure X))ᶜ) = 0) :
    w = ∑ ν ∈ T, w {ν} • Measure.dirac ν := by
  classical
  have hsing : ∀ ν ∈ T, MeasurableSet ({ν} : Set (Measure X)) := fun ν hν ↦
    have := hT ν hν
    measurableSet_singleton_measure ν
  have hTmeas : MeasurableSet (↑T : Set (Measure X)) := by
    rw [← Set.biUnion_of_singleton (↑T : Set (Measure X))]
    exact MeasurableSet.biUnion T.countable_toSet fun ν hν ↦ hsing ν hν
  ext M hM
  have h1 : w M = w (M ∩ ↑T) := by
    have h0 : w (M \ ↑T) = 0 := measure_mono_null (fun ν hν ↦ hν.2) hw
    rw [← measure_inter_add_sdiff M hTmeas, h0, add_zero]
  have h2 : M ∩ ↑T = ⋃ ν ∈ T.filter (· ∈ M), ({ν} : Set (Measure X)) := by
    ext ρ
    simp only [mem_inter_iff, mem_iUnion, mem_singleton_iff, Finset.mem_filter, Finset.mem_coe,
      exists_prop]
    constructor
    · rintro ⟨hρM, hρT⟩
      exact ⟨ρ, ⟨hρT, hρM⟩, rfl⟩
    · rintro ⟨ν, ⟨hνT, hνM⟩, rfl⟩
      exact ⟨hνM, hνT⟩
  have hdisj : (↑(T.filter (· ∈ M)) : Set (Measure X)).PairwiseDisjoint
      (fun ν ↦ ({ν} : Set (Measure X))) :=
    fun a _ b _ hab ↦ Set.disjoint_singleton.2 hab
  rw [h1, h2, measure_biUnion_finset hdisj
    (fun ν hν ↦ hsing ν (Finset.mem_of_mem_filter ν hν)), Measure.finsetSum_apply,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun ν hν ↦ ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hM, smul_eq_mul, Set.indicator_apply]
  split_ifs with h <;> simp

/-- The barycentre of a weight carried by a finite set of probability measures is the
corresponding finite convex combination. -/
lemma join_eq_sum_smul (w : Measure (Measure X)) (T : Finset (Measure X))
    (hT : ∀ ν ∈ T, IsProbabilityMeasure ν) (hw : w ((↑T : Set (Measure X))ᶜ) = 0) :
    Measure.join w = ∑ ν ∈ T, w {ν} • ν := by
  conv_lhs => rw [eq_sum_smul_dirac w T hT hw]
  simpa using join_finset_sum_smul_dirac T (fun ν ↦ w {ν}) (fun ν ↦ ν)

end GiryHelpers

/-! ### Barycentres of weights -/

section Join

/-- The barycentre of a probability weight carried by the probability measures is a probability
measure. -/
lemma isProbabilityMeasure_join_of_ae (w : Measure (Measure Ω)) [IsProbabilityMeasure w]
    (hw : ∀ᵐ ν ∂w, IsProbabilityMeasure ν) : IsProbabilityMeasure (Measure.join w) := by
  constructor
  rw [Measure.join_apply MeasurableSet.univ]
  calc ∫⁻ ν, ν univ ∂w = ∫⁻ _, (1 : ℝ≥0∞) ∂w :=
        lintegral_congr_ae (hw.mono fun ν hν ↦ hν.measure_univ)
    _ = 1 := by simp

/-- The barycentre of a weight carried by the invariant measures of a group action is
invariant. -/
lemma smulInvariantMeasure_join_of_ae {M : Type*} [Group M] [MulAction M Ω]
    [MeasurableConstSMul M Ω] (w : Measure (Measure Ω))
    (hw : ∀ᵐ ν ∂w, SMulInvariantMeasure M Ω ν) : SMulInvariantMeasure M Ω (Measure.join w) := by
  refine ((smulInvariantMeasure_tfae M (Measure.join w)).out 1 6).2 fun g ↦ ?_
  rw [← Measure.join_map_map (measurable_const_smul g)]
  congr 1
  calc w.map (Measure.map (g • ·)) = w.map id :=
        Measure.map_congr (hw.mono fun ν hν ↦ by
          have := hν
          exact (measurePreserving_smul g ν).map_eq)
    _ = w := Measure.map_id

/-- The barycentre of a weight carried by the invariant measures of an additive action is
invariant. -/
lemma vaddInvariantMeasure_join_of_ae {G : Type*} [AddGroup G] [AddAction G Ω]
    [MeasurableConstVAdd G Ω] (w : Measure (Measure Ω))
    (hw : ∀ᵐ ν ∂w, VAddInvariantMeasure G Ω ν) : VAddInvariantMeasure G Ω (Measure.join w) := by
  refine ((vaddInvariantMeasure_tfae G (Measure.join w)).out 1 6).2 fun g ↦ ?_
  rw [← Measure.join_map_map (measurable_const_vadd g)]
  congr 1
  calc w.map (Measure.map (g +ᵥ ·)) = w.map id :=
        Measure.map_congr (hw.mono fun ν hν ↦ by
          have := hν
          exact (measurePreserving_vadd g ν).map_eq)
    _ = w := Measure.map_id

/-- A finite convex combination of probability measures is a probability measure. -/
lemma isProbabilityMeasure_sum_smul {n : ℕ} {c : Fin n → ℝ≥0∞} {ν : Fin n → Measure Ω}
    (hν : ∀ i, IsProbabilityMeasure (ν i)) (hc : ∑ i, c i = 1) :
    IsProbabilityMeasure (∑ i, c i • ν i) := by
  constructor
  simp [Measure.finsetSum_apply, (hν _).measure_univ, hc]


end Join

/-! ### Conditioning through an almost surely larger σ-algebra -/

section Tower

-- `ℬ` is a class-typed local, hence a local instance; pin the ambient σ-algebra of `μ` to `m`.
variable {ℬ : MeasurableSpace Ω} {μ : Measure[m] Ω}

/-- If every `𝒜`-measurable set agrees `μ`-a.e. with a `ℬ`-measurable set ("`𝒜 ⊆ ℬ` `μ`-a.s.",
Georgii's Proposition (14.9)), then conditioning on `𝒜` factors through `ℬ`:
`μ[μ[f | ℬ] | 𝒜] = μ[f | 𝒜]` a.e. This is the tower property for σ-algebras nested only modulo
null sets. -/
lemma condExp_condExp_of_forall_exists_measure_symmDiff_eq_zero (h𝒜 : 𝒜 ≤ m) (hℬ : ℬ ≤ m)
    [IsFiniteMeasure μ] (h : ∀ s, MeasurableSet[𝒜] s → ∃ t, MeasurableSet[ℬ] t ∧ μ (s ∆ t) = 0)
    {f : Ω → ℝ} (hf : Integrable f μ) : μ[μ[f | ℬ] | 𝒜] =ᵐ[μ] μ[f | 𝒜] := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) h𝒜 (f := μ[f | ℬ]) (g := μ[f | 𝒜])
    integrable_condExp (fun s _ _ ↦ (integrable_condExp (m := 𝒜) (f := f) (μ := μ)).integrableOn)
    (fun s hs _ ↦ ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  obtain ⟨t, ht, hst⟩ := h s hs
  have hst' : s =ᵐ[μ] t := measure_symmDiff_eq_zero_iff.1 hst
  calc ∫ x in s, (μ[f | 𝒜]) x ∂μ = ∫ x in s, f x ∂μ := setIntegral_condExp h𝒜 hf hs
    _ = ∫ x in t, f x ∂μ := setIntegral_congr_set hst'
    _ = ∫ x in t, (μ[f | ℬ]) x ∂μ := (setIntegral_condExp hℬ hf ht).symm
    _ = ∫ x in s, (μ[f | ℬ]) x ∂μ := setIntegral_congr_set hst'.symm


end Tower

/-! ### Finite convex combinations in the topology of setwise convergence -/

section ConvexCombos

variable {𝒞 : Set (Set Ω)}

/-- Finite convex combinations of a set of probability measures, inside the space of probability
measures with the topology of setwise convergence on `𝒞` (Georgii's `cx L`; on configuration
space with `𝒞 = localEvents S E`, the topology of local convergence). -/
def convexCombos (L : Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω))) :
    Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) :=
  {μ | ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)),
    (∀ i, ν i ∈ L) ∧ ∑ i, c i = 1 ∧
    (μ.toMeasure : Measure Ω) = ∑ i, c i • ((ν i).toMeasure : Measure Ω)}

lemma subset_convexCombos (L : Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω))) :
    L ⊆ convexCombos L :=
  fun μ hμ ↦ ⟨1, fun _ ↦ 1, fun _ ↦ μ, fun _ ↦ hμ, by simp, by simp⟩


end ConvexCombos

/-! ### The extreme decomposition governed by a `(P, 𝒜)`-kernel

Proposition (7.22) produces, from a `(P, 𝒜)`-kernel `π`, the unique representing weight
`w_μ = weight π μ` of every `μ ∈ P`. The statements of Theorem (7.26) — `w_μ` is carried by
`ex P`, `μ ↦ w_μ` is an affine bijection onto the probability weights carried by `ex P`, with
inverse `w ↦ ∫ ν w(dν)` — and of its corollaries (7.28) (commutation with symmetries), (7.29)
(linear independence counts extreme points) and (7.30) (the discretisation step and the density
of finite convex combinations of extreme points) use nothing about `P` beyond `ex P = P ∩ P_𝒜`
and measurability of `P`. They are proved here once, at that generality, and instantiated at
`P = 𝒢(γ)`, `𝒜 = 𝓣` (Theorem (7.26) and Corollaries (7.28)–(7.30), in
`ExtremeDecomposition.lean` and `ExtremeCorollaries.lean`), at `P = 𝓟_Θ` (Theorem (14.10)) and
at `P = 𝒢_Θ(γ)` (Theorem (14.17), Corollaries (14.18), (14.25), in
`InvariantDecomposition.lean`). -/

namespace IsPAKernel

section Abstract

variable [MeasurableSpace.CountablyGenerated Ω] {P : Set (Measure Ω)} {π : Kernel[𝒜, m] Ω Ω}
  [IsMarkovKernel π] (hπ : IsPAKernel P 𝒜 π) (h𝒜 : 𝒜 ≤ m)
  (hP : ∀ μ ∈ P, IsProbabilityMeasure μ)


include hπ h𝒜 hP

/-- If `ex P = P ∩ P_𝒜` then `ex P = P ∩ fixedCore π`: the extreme points are cut out inside `P`
by the measurable condition `π(· | ω) = ν` for `ν`-a.e. `ω`. -/
lemma extremePoints_eq_inter_fixedCore (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) :
    P.extremePoints ℝ≥0∞ = P ∩ fixedCore π := by
  rw [hex]
  ext ν
  simp only [mem_inter_iff, and_congr_right_iff]
  intro hν
  have := hP ν hν
  exact (hπ.mem_fixedCore_iff h𝒜 hν).symm

/-- `ex P` is measurable in `Measure Ω`. -/
lemma measurableSet_extremePoints (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) : MeasurableSet (P.extremePoints ℝ≥0∞) := by
  rw [hπ.extremePoints_eq_inter_fixedCore h𝒜 hP hex]
  exact hPm.inter (measurableSet_fixedCore h𝒜)

/-- `ex P ≠ ∅` as soon as `P ≠ ∅`. -/
lemma nonempty_extremePoints (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (hne : P.Nonempty) :
    (P.extremePoints ℝ≥0∞).Nonempty := by
  rw [hex]; exact hπ.nonempty_inter_trivialOn h𝒜 hP hne

variable {μ : Measure Ω}

/-- The weight `w_μ` is carried by `ex P`. -/
lemma weight_extremePoints_compl (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (hμ : μ ∈ P) :
    weight π μ (P.extremePoints ℝ≥0∞)ᶜ = 0 := by
  have := hP μ hμ
  rw [hex]; exact hπ.weight_compl_eq_zero h𝒜 hPm hμ

/-- **Georgii (7.26), pointwise form**: `π(· | ω) ∈ ex P` for `μ`-a.e. `ω`, `μ ∈ P`. -/
lemma ae_mem_extremePoints (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (hμ : μ ∈ P) :
    ∀ᵐ ω ∂μ, π ω ∈ P.extremePoints ℝ≥0∞ := by
  have hmeas := hπ.measurableSet_extremePoints h𝒜 hP hPm hex
  have hzero : μ (π ⁻¹' (P.extremePoints ℝ≥0∞)ᶜ) = 0 := by
    rw [← weight_apply h𝒜 μ hmeas.compl]
    exact hπ.weight_extremePoints_compl h𝒜 hP hPm hex hμ
  rw [ae_iff]
  exact hzero

/-- Uniqueness: a weight carried by `ex P` representing `μ` is `w_μ`. -/
theorem eq_weight_of_join_eq' (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜)
    {w : Measure (Measure Ω)} (hw : w (P.extremePoints ℝ≥0∞)ᶜ = 0)
    (hjoin : Measure.join w = μ) : w = weight π μ := by
  refine hπ.eq_weight_of_join_eq h𝒜 hP ?_ hjoin
  rw [← hex]
  exact ae_iff.2 hw

/-- `μ ↦ w_μ` inverts `w ↦ ∫ ν w(dν)` on weights carried by `ex P`. -/
theorem weight_join (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (w : Measure (Measure Ω))
    (hw : w (P.extremePoints ℝ≥0∞)ᶜ = 0) : weight π (Measure.join w) = w :=
  (hπ.eq_weight_of_join_eq' h𝒜 hP hex hw rfl).symm

omit hπ hP [MeasurableSpace.CountablyGenerated Ω] [IsMarkovKernel π] in
/-- **Georgii (7.26), affinity**: `μ ↦ w_μ` is affine. -/
theorem weight_add_smul (μ ν : Measure Ω) (a b : ℝ≥0∞) :
    weight π (a • μ + b • ν) = a • weight π μ + b • weight π ν := by
  simp only [weight, Measure.map_add _ _ (measurable_kernel_of_le h𝒜),
    Measure.map_smul]

/-- **Georgii (7.26), bijection**: `μ ↦ w_μ` maps `P` bijectively onto the probability weights
carried by `ex P`, provided the barycentre of such a weight lies in `P`. -/
theorem bijOn_weight (hPm : MeasurableSet P) (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜)
    (hjoin : ∀ w : Measure (Measure Ω), IsProbabilityMeasure w →
      w (P.extremePoints ℝ≥0∞)ᶜ = 0 → Measure.join w ∈ P) :
    BijOn (weight π) P
      {w : Measure (Measure Ω) | IsProbabilityMeasure w ∧ w (P.extremePoints ℝ≥0∞)ᶜ = 0} := by
  refine ⟨fun μ hμ ↦ ?_, fun μ hμ ν hν h ↦ ?_, fun w hw ↦ ?_⟩
  · have := hP μ hμ
    exact ⟨isProbabilityMeasure_weight h𝒜 μ, hπ.weight_extremePoints_compl h𝒜 hP hPm hex hμ⟩
  · have := hP μ hμ
    have := hP ν hν
    calc μ = Measure.join (weight π μ) := (hπ.join_weight h𝒜 hμ).symm
      _ = Measure.join (weight π ν) := by rw [h]
      _ = ν := hπ.join_weight h𝒜 hν
  · have := hw.1
    exact ⟨Measure.join w, hjoin w hw.1 hw.2, hπ.weight_join h𝒜 hP hex w hw.2⟩

/-- **Georgii (7.26), existence and uniqueness**: every `μ ∈ P` is represented,
`μ = ∫ ν w(dν)`, by a unique probability weight `w` carried by `ex P`. -/
theorem exists_unique_weight_extremePoints (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (hμ : μ ∈ P) :
    ∃! w : Measure (Measure Ω), IsProbabilityMeasure w ∧
      w (P.extremePoints ℝ≥0∞)ᶜ = 0 ∧ Measure.join w = μ := by
  have := hP μ hμ
  refine ⟨weight π μ, ⟨isProbabilityMeasure_weight h𝒜 μ,
    hπ.weight_extremePoints_compl h𝒜 hP hPm hex hμ, hπ.join_weight h𝒜 hμ⟩, ?_⟩
  rintro w ⟨-, hw, hjoin⟩
  exact hπ.eq_weight_of_join_eq' h𝒜 hP hex hw hjoin

omit [MeasurableSpace.CountablyGenerated Ω] [IsMarkovKernel π] in
/-- **Georgii (14.10), the level-set formula**: `w_μ(ν(A) ≤ c) = μ(μ(A | 𝒜) ≤ c)`. -/
theorem weight_setOf_real_le (hμ : μ ∈ P) {A : Set Ω} (hA : MeasurableSet A) (c : ℝ) :
    weight π μ {ν | ν.real A ≤ c} = μ {ω | (μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ω ≤ c} := by
  have := hP μ hμ
  have hM : MeasurableSet {ν : Measure Ω | ν.real A ≤ c} :=
    measurableSet_le (Measure.measurable_coe hA).ennreal_toReal measurable_const
  rw [weight_apply h𝒜 μ hM]
  refine measure_congr ?_
  have h := hπ.1 μ hμ A hA
  filter_upwards [h] with ω hω
  change ((π ω).real A ≤ c) = ((μ[A.indicator (fun _ ↦ (1 : ℝ)) | 𝒜]) ω ≤ c)
  rw [hω]

/-! #### Georgii (7.28): the weight map commutes with a symmetry -/

/-- **Georgii, Corollary (7.28)**, abstract form: for a measurable map `T` sending `ex P` into
itself, `w_{T(μ)} = T(w_μ)` for `μ ∈ P`. -/
theorem weight_map (hPm : MeasurableSet P) (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜)
    {T : Ω → Ω} (hT : Measurable T)
    (hTex : ∀ ν ∈ P.extremePoints ℝ≥0∞, ν.map T ∈ P.extremePoints ℝ≥0∞) (hμ : μ ∈ P) :
    weight π (μ.map T) = (weight π μ).map (Measure.map T) := by
  have := hP μ hμ
  refine (hπ.eq_weight_of_join_eq' h𝒜 hP hex ?_ ?_).symm
  · rw [Measure.map_apply (Measure.measurable_map _ hT)
      (hπ.measurableSet_extremePoints h𝒜 hP hPm hex).compl]
    exact measure_mono_null (fun ν hν hνex ↦ hν (hTex ν hνex))
      (hπ.weight_extremePoints_compl h𝒜 hP hPm hex hμ)
  · rw [Measure.join_map_map hT, hπ.join_weight h𝒜 hμ]

/-- **Georgii, Corollary (7.28)**, second half, abstract form: for a measurable map `T` sending
`ex P` into itself, `μ ∈ P` is `T`-invariant iff its weight `w_μ` is invariant under
`ν ↦ T(ν)`. -/
theorem map_eq_self_iff_weight_map_eq_self (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) {T : Ω → Ω} (hT : Measurable T)
    (hTex : ∀ ν ∈ P.extremePoints ℝ≥0∞, ν.map T ∈ P.extremePoints ℝ≥0∞) (hμ : μ ∈ P) :
    μ.map T = μ ↔ (weight π μ).map (Measure.map T) = weight π μ := by
  have := hP μ hμ
  constructor
  · intro h
    rw [← hπ.weight_map h𝒜 hP hPm hex hT hTex hμ, h]
  · intro h
    calc μ.map T = Measure.join ((weight π μ).map (Measure.map T)) := by
          rw [Measure.join_map_map hT, hπ.join_weight h𝒜 hμ]
      _ = Measure.join (weight π μ) := by rw [h]
      _ = μ := hπ.join_weight h𝒜 hμ

/-- Georgii (7.28), abstract form: `T` preserves `μ ∈ P` iff `ν ↦ T(ν)` preserves `w_μ`. -/
theorem measurePreserving_iff_measurePreserving_weight (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) {T : Ω → Ω} (hT : Measurable T)
    (hTex : ∀ ν ∈ P.extremePoints ℝ≥0∞, ν.map T ∈ P.extremePoints ℝ≥0∞) (hμ : μ ∈ P) :
    MeasurePreserving T μ μ ↔
      MeasurePreserving (Measure.map T) (weight π μ) (weight π μ) := by
  constructor
  · intro h
    exact ⟨Measure.measurable_map _ hT,
      (hπ.map_eq_self_iff_weight_map_eq_self h𝒜 hP hPm hex hT hTex hμ).1 h.map_eq⟩
  · intro h
    exact ⟨hT, (hπ.map_eq_self_iff_weight_map_eq_self h𝒜 hP hPm hex hT hTex hμ).2 h.map_eq⟩

/-! #### Georgii (7.29): linear dimension counts the extreme points -/

/-- An extreme point gives full mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_kernel_eq_self (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜)
    (hμ : μ ∈ P.extremePoints ℝ≥0∞) : μ {ω | π ω = μ} = 1 := by
  have hμP : μ ∈ P := extremePoints_subset hμ
  have := hP μ hμP
  have hμ' := hμ
  rw [hex] at hμ'
  have hae : ∀ᵐ ω ∂μ, π ω = μ := hπ.ae_eq_of_mem_trivialOn h𝒜 hμP hμ'.2
  rw [← prob_compl_eq_zero_iff (h𝒜 _ (measurableSet_eq_measure (π := π) μ)), compl_ofPred]
  exact ae_iff.1 hae

/-- Any extreme point `ν ≠ μ` gives zero mass to `{ω | π(· | ω) = μ}`. -/
lemma measure_kernel_eq_ne (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) {ν : Measure Ω}
    (hν : ν ∈ P.extremePoints ℝ≥0∞) (hne : μ ≠ ν) : ν {ω | π ω = μ} = 0 := by
  have hνP : ν ∈ P := extremePoints_subset hν
  have := hP ν hνP
  have hν' := hν
  rw [hex] at hν'
  have hae : ∀ᵐ ω ∂ν, π ω = ν := hπ.ae_eq_of_mem_trivialOn h𝒜 hνP hν'.2
  refine measure_mono_null ?_ (ae_iff.1 hae)
  intro ω hω hcontra
  exact hne (by rw [← hω, hcontra])

/-- **Georgii, Corollary (7.29)**, part 1, abstract form: distinct extreme points of `P` are
linearly independent over `ℝ≥0∞`. -/
theorem linearIndependent_of_mem_extremePoints (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜)
    {N : ℕ} {μ : Fin N → Measure Ω} (hμ : ∀ i, μ i ∈ P.extremePoints ℝ≥0∞)
    (hinj : Function.Injective μ) : LinearIndependent ℝ≥0∞ μ := by
  rw [Fintype.linearIndependent_iffₛ]
  intro c d hcd i
  set A : Set Ω := {ω | π ω = μ i} with hAdef
  have key : ∀ e : Fin N → ℝ≥0∞, (∑ l, e l • μ l) A = e i := by
    intro e
    rw [Measure.finsetSum_apply]
    rw [Finset.sum_eq_single i (fun l _ hl ↦ ?_) (fun h ↦ absurd (Finset.mem_univ i) h)]
    · rw [Measure.smul_apply, hπ.measure_kernel_eq_self h𝒜 hP hex (hμ i), smul_eq_mul, mul_one]
    · rw [Measure.smul_apply, hπ.measure_kernel_eq_ne h𝒜 hP hex (hμ l) (hinj.ne hl.symm),
        smul_eq_mul, mul_zero]
  have h2 : (∑ l, c l • μ l) A = (∑ l, d l • μ l) A := congrArg (fun ρ : Measure Ω ↦ ρ A) hcd
  rwa [key c, key d] at h2

/-- **Georgii, Corollary (7.29)**, part 2, abstract form: if `ex P` has fewer than `N` elements,
any `N` elements of `P` satisfy a nontrivial `ℝ≥0∞`-linear relation. -/
theorem exists_ne_sum_smul_eq_sum_smul (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) {N : ℕ}
    (hcard : (P.extremePoints ℝ≥0∞).encard < N) {μ : Fin N → Measure Ω} (hμ : ∀ i, μ i ∈ P) :
    ∃ c d : Fin N → ℝ≥0∞, c ≠ d ∧ ∑ i, c i • μ i = ∑ i, d i • μ i := by
  classical
  have hfin : (P.extremePoints ℝ≥0∞).Finite := encard_lt_top_iff.1 (hcard.trans_le le_top)
  have hTcard : hfin.toFinset.card < N := by
    have h1 : (hfin.toFinset.card : ℕ∞) < N := by
      rw [← hfin.encard_eq_coe_toFinset_card]
      exact hcard
    exact_mod_cast h1
  have hTprob : ∀ ν ∈ hfin.toFinset, IsProbabilityMeasure ν := fun ν hν ↦
    hP ν (extremePoints_subset (hfin.mem_toFinset.1 hν))
  have hprob : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ hP _ (hμ i)
  have hwnull : ∀ i, (weight π (μ i)) ((↑hfin.toFinset : Set (Measure Ω))ᶜ) = 0 := by
    intro i
    have := hprob i
    have h := hπ.weight_extremePoints_compl h𝒜 hP hPm hex (hμ i)
    rwa [← hfin.coe_toFinset] at h
  have hrep : ∀ i, μ i = ∑ ν ∈ hfin.toFinset, (weight π (μ i)) {ν} • ν := fun i ↦ by
    have := hprob i
    conv_lhs => rw [← hπ.join_weight h𝒜 (hμ i)]
    exact join_eq_sum_smul _ hfin.toFinset hTprob (hwnull i)
  -- the real weight vectors are linearly dependent
  set v : Fin N → (↥hfin.toFinset → ℝ) :=
    fun i t ↦ ((weight π (μ i)) {t.1}).toReal with hvdef
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hLI
    have hle := hLI.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at hle
    omega
  obtain ⟨g, hg0, i₀, hgi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hofmax : ∀ a : ℝ, ENNReal.ofReal (max a 0) = ENNReal.ofReal a := by
    intro a
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  refine ⟨fun i ↦ ENNReal.ofReal (g i), fun i ↦ ENNReal.ofReal (-g i), ?_, ?_⟩
  · -- the two coefficient families differ at `i₀`
    intro hcd
    have h := congrFun hcd i₀
    rcases lt_or_gt_of_ne hgi₀ with hneg | hpos
    · rw [ENNReal.ofReal_of_nonpos hneg.le] at h
      exact (ENNReal.ofReal_pos.2 (neg_pos.2 hneg)).ne h
    · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.2 hpos.le)] at h
      exact (ENNReal.ofReal_pos.2 hpos).ne' h
  · -- the two combinations agree
    have hcoord : ∀ ν ∈ hfin.toFinset,
        ∑ i, ENNReal.ofReal (g i) * (weight π (μ i)) {ν} =
          ∑ i, ENNReal.ofReal (-g i) * (weight π (μ i)) {ν} := by
      intro ν hν
      have hreal : ∑ i, g i * v i ⟨ν, hν⟩ = 0 := by
        have h := congrFun hg0 ⟨ν, hν⟩
        simpa using h
      have hsplit : ∑ i, max (g i) 0 * v i ⟨ν, hν⟩ = ∑ i, max (-g i) 0 * v i ⟨ν, hν⟩ := by
        have h2 : ∑ i, (max (g i) 0 * v i ⟨ν, hν⟩ - max (-g i) 0 * v i ⟨ν, hν⟩) = 0 := by
          calc ∑ i, (max (g i) 0 * v i ⟨ν, hν⟩ - max (-g i) 0 * v i ⟨ν, hν⟩)
              = ∑ i, g i * v i ⟨ν, hν⟩ := Finset.sum_congr rfl fun i _ ↦ by
                rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
            _ = 0 := hreal
        rw [Finset.sum_sub_distrib] at h2
        exact sub_eq_zero.1 h2
      calc ∑ i, ENNReal.ofReal (g i) * (weight π (μ i)) {ν}
          = ∑ i, ENNReal.ofReal (max (g i) 0 * v i ⟨ν, hν⟩) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have := hprob i
            have := isProbabilityMeasure_weight (π := π) h𝒜 (μ i)
            rw [ENNReal.ofReal_mul (le_max_right (g i) 0), hofmax,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ = ENNReal.ofReal (∑ i, max (g i) 0 * v i ⟨ν, hν⟩) :=
            (ENNReal.ofReal_sum_of_nonneg fun i _ ↦
              mul_nonneg (le_max_right (g i) 0) ENNReal.toReal_nonneg).symm
        _ = ENNReal.ofReal (∑ i, max (-g i) 0 * v i ⟨ν, hν⟩) := by rw [hsplit]
        _ = ∑ i, ENNReal.ofReal (max (-g i) 0 * v i ⟨ν, hν⟩) :=
            ENNReal.ofReal_sum_of_nonneg fun i _ ↦
              mul_nonneg (le_max_right (-g i) 0) ENNReal.toReal_nonneg
        _ = ∑ i, ENNReal.ofReal (-g i) * (weight π (μ i)) {ν} := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            have := hprob i
            have := isProbabilityMeasure_weight (π := π) h𝒜 (μ i)
            rw [ENNReal.ofReal_mul (le_max_right (-g i) 0), hofmax,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hassemble : ∀ e : Fin N → ℝ≥0∞, ∑ i, e i • μ i =
        ∑ ν ∈ hfin.toFinset, (∑ i, e i * (weight π (μ i)) {ν}) • ν := by
      intro e
      calc ∑ i, e i • μ i
          = ∑ i, ∑ ν ∈ hfin.toFinset, e i • ((weight π (μ i)) {ν} • ν) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            conv_lhs => rw [hrep i]
            rw [Finset.smul_sum]
        _ = ∑ ν ∈ hfin.toFinset, ∑ i, e i • ((weight π (μ i)) {ν} • ν) := Finset.sum_comm
        _ = ∑ ν ∈ hfin.toFinset, (∑ i, e i * (weight π (μ i)) {ν}) • ν := by
            refine Finset.sum_congr rfl fun ν _ ↦ ?_
            rw [Finset.sum_smul]
            exact Finset.sum_congr rfl fun i _ ↦ smul_smul _ _ _
    rw [hassemble, hassemble]
    exact Finset.sum_congr rfl fun ν hν ↦ by rw [hcoord ν hν]

/-- **Georgii, Corollary (7.29)**, abstract form: `|ex P| ≥ N` iff `P` contains `N` linearly
independent elements. -/
theorem le_encard_extremePoints_iff (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (N : ℕ) :
    (N : ℕ∞) ≤ (P.extremePoints ℝ≥0∞).encard ↔
      ∃ μ : Fin N → Measure Ω, (∀ i, μ i ∈ P) ∧ LinearIndependent ℝ≥0∞ μ := by
  constructor
  · intro hN
    obtain ⟨t, htsub, htcard⟩ := Set.exists_subset_encard_eq hN
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htcard
    have hcard : htfin.toFinset.card = N := by
      have h := htfin.encard_eq_coe_toFinset_card
      rw [htcard] at h
      exact_mod_cast h.symm
    set e := Finset.equivFinOfCardEq hcard with hedef
    have hext : ∀ i, ((e.symm i : ↥htfin.toFinset) : Measure Ω) ∈ P.extremePoints ℝ≥0∞ :=
      fun i ↦ htsub (htfin.mem_toFinset.1 (e.symm i).2)
    refine ⟨fun i ↦ ((e.symm i : ↥htfin.toFinset) : Measure Ω),
      fun i ↦ extremePoints_subset (hext i), ?_⟩
    exact hπ.linearIndependent_of_mem_extremePoints h𝒜 hP hex hext
      fun i j h ↦ e.symm.injective (Subtype.coe_injective h)
  · rintro ⟨μ, hμP, hLI⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, d, hcd, hsum⟩ := hπ.exists_ne_sum_smul_eq_sum_smul h𝒜 hP hPm hex hlt hμP
    exact hcd (funext (Fintype.linearIndependent_iffₛ.1 hLI c d hsum))

/-! #### Georgii (7.30), discretisation step -/

/-- Discretisation step of Georgii (7.30), abstract form: `μ ∈ P` is approximated within `1/r` on
finitely many events by a finite convex combination of extreme points of `P`. -/
theorem exists_extremePoints_combo_approx (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) (hμ : μ ∈ P)
    {k : ℕ} (A : Fin k → Set Ω) (hA : ∀ j, MeasurableSet (A j)) {r : ℕ} (hr : 0 < r) :
    ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → Measure Ω),
      (∀ i, ν i ∈ P.extremePoints ℝ≥0∞) ∧ (∑ i, c i) = 1 ∧
      ∀ j, (∑ i, c i • ν i) (A j) ≤ μ (A j) + (r : ℝ≥0∞)⁻¹ ∧
        μ (A j) ≤ (∑ i, c i • ν i) (A j) + (r : ℝ≥0∞)⁻¹ := by
  classical
  have hprobμ := hP μ hμ
  set w := weight π μ with hwdef
  have hwprob : IsProbabilityMeasure w := hwdef ▸ isProbabilityMeasure_weight h𝒜 μ
  have hXm : MeasurableSet (P.extremePoints ℝ≥0∞) :=
    hπ.measurableSet_extremePoints h𝒜 hP hPm hex
  have hwX : w ((P.extremePoints ℝ≥0∞)ᶜ) = 0 := hπ.weight_extremePoints_compl h𝒜 hP hPm hex hμ
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  -- the grid index of a measure
  set idx : Measure Ω → Fin k → ℕ := fun ρ j ↦ ⌊(ρ (A j)).toReal * r⌋₊ with hidxdef
  have hidx_meas : ∀ (j : Fin k) (m : ℕ), MeasurableSet {ρ : Measure Ω | idx ρ j = m} := by
    intro j m
    have h1 : Measurable fun ρ : Measure Ω ↦ (ρ (A j)).toReal * (r : ℝ) :=
      ((Measure.measurable_coe (hA j)).ennreal_toReal).mul_const _
    exact h1.nat_floor (measurableSet_singleton m)
  -- the cells of the induced partition of `ex P`
  set cell : (Fin k → Fin (r + 1)) → Set (Measure Ω) :=
    fun p ↦ (P.extremePoints ℝ≥0∞) ∩ {ρ | ∀ j, idx ρ j = (p j : ℕ)} with hcelldef
  have hcell_meas : ∀ p, MeasurableSet (cell p) := by
    intro p
    refine hXm.inter ?_
    have h : {ρ : Measure Ω | ∀ j, idx ρ j = (p j : ℕ)} =
        ⋂ j, {ρ : Measure Ω | idx ρ j = (p j : ℕ)} := Set.ofPred_forall _
    rw [h]
    exact MeasurableSet.iInter fun j ↦ hidx_meas j (p j)
  have hdisj : (↑(Finset.univ : Finset (Fin k → Fin (r + 1))) :
      Set (Fin k → Fin (r + 1))).PairwiseDisjoint cell := by
    intro p _ q _ hpq
    refine Set.disjoint_left.2 fun ρ hρp hρq ↦ hpq ?_
    funext j
    exact Fin.val_injective ((hρp.2 j).symm.trans (hρq.2 j))
  have hcover : (P.extremePoints ℝ≥0∞) =
      ⋃ p ∈ (Finset.univ : Finset (Fin k → Fin (r + 1))), cell p := by
    ext ρ
    constructor
    · intro hρ
      have : IsProbabilityMeasure ρ := hP ρ (extremePoints_subset hρ)
      have hbound : ∀ j, idx ρ j < r + 1 := by
        intro j
        have hle1 : (ρ (A j)).toReal ≤ 1 := by
          simpa using ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ρ) (s := A j))
        have hler : (ρ (A j)).toReal * r ≤ (r : ℝ) := by
          calc (ρ (A j)).toReal * r ≤ 1 * (r : ℝ) :=
                mul_le_mul_of_nonneg_right hle1 (Nat.cast_nonneg r)
            _ = r := one_mul _
        calc idx ρ j ≤ ⌊(r : ℝ)⌋₊ := Nat.floor_mono hler
          _ = r := Nat.floor_natCast r
          _ < r + 1 := Nat.lt_succ_self r
      exact Set.mem_iUnion₂.2 ⟨fun j ↦ ⟨idx ρ j, hbound j⟩, Finset.mem_univ _,
        hρ, fun j ↦ rfl⟩
    · intro hρ
      obtain ⟨p, -, hρp⟩ := Set.mem_iUnion₂.1 hρ
      exact hρp.1
  -- representatives: one extreme point per nonempty cell
  obtain ⟨νstar, hνstar⟩ := hπ.nonempty_extremePoints h𝒜 hP hex ⟨μ, hμ⟩
  have hrepex : ∀ p, ∃ ρ : Measure Ω,
      ρ ∈ P.extremePoints ℝ≥0∞ ∧ ((cell p).Nonempty → ρ ∈ cell p) := by
    intro p
    by_cases hp : (cell p).Nonempty
    · exact ⟨hp.some, hp.some_mem.1, fun _ ↦ hp.some_mem⟩
    · exact ⟨νstar, hνstar, fun h ↦ absurd h hp⟩
  choose rep hrepX hrepmem using hrepex
  -- total weight one
  have hsum1 : ∑ p : (Fin k → Fin (r + 1)), w (cell p) = 1 := by
    rw [← measure_biUnion_finset hdisj fun p _ ↦ hcell_meas p, ← hcover]
    exact (prob_compl_eq_zero_iff hXm).1 hwX
  -- diameter bound on cells
  have hdiam : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k) (ρ σ : Measure Ω), ρ ∈ cell p →
      σ ∈ cell p → ρ (A j) ≤ σ (A j) + (r : ℝ≥0∞)⁻¹ := by
    intro p j ρ σ hρ hσ
    have : IsProbabilityMeasure ρ := hP ρ (extremePoints_subset hρ.1)
    have : IsProbabilityMeasure σ := hP σ (extremePoints_subset hσ.1)
    have hx : (ρ (A j)).toReal * r < (idx ρ j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hy : (idx σ j : ℝ) ≤ (σ (A j)).toReal * r := Nat.floor_le (by positivity)
    have heq : idx ρ j = idx σ j := (hρ.2 j).trans (hσ.2 j).symm
    have hreal : (ρ (A j)).toReal ≤ (σ (A j)).toReal + (r : ℝ)⁻¹ := by
      rw [heq] at hx
      have h1 : (ρ (A j)).toReal * r ≤ (σ (A j)).toReal * r + 1 := by linarith
      have h2 : (ρ (A j)).toReal ≤ ((σ (A j)).toReal * r + 1) / r := by
        rw [le_div_iff₀ hr0]
        exact h1
      calc (ρ (A j)).toReal ≤ ((σ (A j)).toReal * r + 1) / r := h2
        _ = (σ (A j)).toReal + (r : ℝ)⁻¹ := by
          rw [add_div, mul_div_cancel_right₀ _ hr0.ne', one_div]
    calc ρ (A j) = ENNReal.ofReal ((ρ (A j)).toReal) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ((σ (A j)).toReal + (r : ℝ)⁻¹) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((σ (A j)).toReal) + ENNReal.ofReal ((r : ℝ)⁻¹) :=
          ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)
      _ = σ (A j) + (r : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_inv_of_pos hr0,
            ENNReal.ofReal_natCast]
  -- per-cell comparison of the representative with the integral
  have hcell_upper : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k), w (cell p) * (rep p) (A j) ≤
      (∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
    intro p j
    by_cases hp : (cell p).Nonempty
    · have hrepp := hrepmem p hp
      calc w (cell p) * (rep p) (A j) = ∫⁻ _ in cell p, (rep p) (A j) ∂w := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ ρ in cell p, (ρ (A j) + (r : ℝ≥0∞)⁻¹) ∂w :=
            setLIntegral_mono ((Measure.measurable_coe (hA j)).add_const _)
              fun ρ hρ ↦ hdiam p j (rep p) ρ hrepp hρ
        _ = (∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
            rw [lintegral_add_right _ measurable_const, setLIntegral_const, mul_comm]
    · have hempty : cell p = ∅ := Set.not_nonempty_iff_eq_empty.1 hp
      simp [hempty]
  have hcell_lower : ∀ (p : Fin k → Fin (r + 1)) (j : Fin k),
      (∫⁻ ρ in cell p, ρ (A j) ∂w) ≤
        w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
    intro p j
    by_cases hp : (cell p).Nonempty
    · have hrepp := hrepmem p hp
      calc ∫⁻ ρ in cell p, ρ (A j) ∂w
          ≤ ∫⁻ _ in cell p, ((rep p) (A j) + (r : ℝ≥0∞)⁻¹) ∂w :=
            setLIntegral_mono measurable_const fun ρ hρ ↦ hdiam p j ρ (rep p) hρ hrepp
        _ = w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹ := by
            rw [setLIntegral_const]
            ring
    · have hempty : cell p = ∅ := Set.not_nonempty_iff_eq_empty.1 hp
      simp [hempty]
  -- decomposition of `μ` over the cells
  have hμdecomp : ∀ j : Fin k,
      μ (A j) = ∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w := by
    intro j
    have h1 : μ (A j) = ∫⁻ ρ, ρ (A j) ∂w := by
      conv_lhs => rw [← hπ.join_weight h𝒜 hμ]
      rw [Measure.join_apply (hA j)]
    have h2 : ∫⁻ ρ, ρ (A j) ∂w = ∫⁻ ρ in P.extremePoints ℝ≥0∞, ρ (A j) ∂w := by
      rw [← lintegral_add_compl (fun ρ ↦ ρ (A j)) hXm]
      have h0 : ∫⁻ ρ in (P.extremePoints ℝ≥0∞)ᶜ, ρ (A j) ∂w = 0 := by
        rw [Measure.restrict_eq_zero.2 hwX]
        exact lintegral_zero_measure _
      rw [h0, add_zero]
    rw [h1, h2, hcover, lintegral_biUnion_finset hdisj (fun p _ ↦ hcell_meas p)]
  -- the two estimates
  have hupper : ∀ j : Fin k, ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) ≤
      μ (A j) + (r : ℝ≥0∞)⁻¹ := by
    intro j
    calc ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)
        ≤ ∑ p : (Fin k → Fin (r + 1)),
            ((∫⁻ ρ in cell p, ρ (A j) ∂w) + w (cell p) * (r : ℝ≥0∞)⁻¹) :=
          Finset.sum_le_sum fun p _ ↦ hcell_upper p j
      _ = (∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w) +
            (∑ p : (Fin k → Fin (r + 1)), w (cell p)) * (r : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = μ (A j) + (r : ℝ≥0∞)⁻¹ := by rw [← hμdecomp j, hsum1, one_mul]
  have hlower : ∀ j : Fin k, μ (A j) ≤
      (∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)) + (r : ℝ≥0∞)⁻¹ := by
    intro j
    calc μ (A j) = ∑ p : (Fin k → Fin (r + 1)), ∫⁻ ρ in cell p, ρ (A j) ∂w := hμdecomp j
      _ ≤ ∑ p : (Fin k → Fin (r + 1)),
            (w (cell p) * (rep p) (A j) + w (cell p) * (r : ℝ≥0∞)⁻¹) :=
          Finset.sum_le_sum fun p _ ↦ hcell_lower p j
      _ = (∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j)) +
            (∑ p : (Fin k → Fin (r + 1)), w (cell p)) * (r : ℝ≥0∞)⁻¹ := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by rw [hsum1, one_mul]
  -- reindex over `Fin n`
  set eqv := Fintype.equivFin (Fin k → Fin (r + 1)) with heqv
  refine ⟨Fintype.card (Fin k → Fin (r + 1)), fun i ↦ w (cell (eqv.symm i)),
    fun i ↦ rep (eqv.symm i), fun i ↦ hrepX (eqv.symm i), ?_, fun j ↦ ?_⟩
  · rw [Equiv.sum_comp eqv.symm fun p ↦ w (cell p)]
    exact hsum1
  · have hcombo : (∑ i, w (cell (eqv.symm i)) • rep (eqv.symm i)) (A j) =
        ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) := by
      calc (∑ i, w (cell (eqv.symm i)) • rep (eqv.symm i)) (A j)
          = ∑ i, w (cell (eqv.symm i)) * (rep (eqv.symm i)) (A j) := by
            rw [Measure.finsetSum_apply]
            exact Finset.sum_congr rfl fun i _ ↦ by rw [Measure.smul_apply, smul_eq_mul]
        _ = ∑ p : (Fin k → Fin (r + 1)), w (cell p) * (rep p) (A j) :=
            Equiv.sum_comp eqv.symm fun p ↦ w (cell p) * (rep p) (A j)
    rw [hcombo]
    exact ⟨hupper j, hlower j⟩


end Abstract

end IsPAKernel

section Density

variable [MeasurableSpace.CountablyGenerated Ω] {P : Set (Measure Ω)} {π : Kernel[𝒜, m] Ω Ω}
  [IsMarkovKernel π] (hπ : IsPAKernel P 𝒜 π) (h𝒜 : 𝒜 ≤ m)
  (hP : ∀ μ ∈ P, IsProbabilityMeasure μ)

include hπ h𝒜 hP

/-- Hard inclusion of **Georgii, Corollary (7.30)/(14.25)**, abstract form: if `P` has a
`(P, 𝒜)`-kernel with `ex P = P ∩ P_𝒜` and every extreme point of `P` lies in `L`, then every
`μ ∈ P` lies in the closed convex hull of `L` in the topology of setwise convergence on a family
`𝒞` of measurable sets. Georgii's proof: the neighbourhoods of `μ` are indexed by the directed
family of pairs (finitely many sets `I ⊆ 𝒞`, precision `1/(r+1)`), and the discretisation step
`exists_extremePoints_combo_approx` meets each of them with a finite convex combination of
extreme points. -/
theorem IsPAKernel.setOf_mem_subset_closure_convexCombos (hPm : MeasurableSet P)
    (hex : P.extremePoints ℝ≥0∞ = P ∩ trivialOn 𝒜) {𝒞 : Set (Set Ω)}
    (h𝒞 : ∀ A ∈ 𝒞, MeasurableSet A) {L : Set (WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω))}
    (hlim : ∀ μ : ProbabilityMeasure Ω, (μ : Measure Ω) ∈ P.extremePoints ℝ≥0∞ →
      (WithSetwiseTopology.ofMeasure μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω)) ∈ L) :
    {μ : WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) | (μ.toMeasure : Measure Ω) ∈ P} ⊆
      closure (convexCombos L) := by
  classical
  intro μ0 hμ0
  have hμP : (μ0.toMeasure : Measure Ω) ∈ P := hμ0
  -- stage-`(I, r)` approximation: precision `1 / (r + 1)` on the sets in `I`
  have happrox : ∀ p : Finset 𝒞 × ℕ,
      ∃ (n : ℕ) (c : Fin n → ℝ≥0∞) (ν : Fin n → Measure Ω),
        (∀ i, ν i ∈ P.extremePoints ℝ≥0∞) ∧ (∑ i, c i) = 1 ∧
        ∀ A ∈ p.1,
          (∑ i, c i • ν i) (A : Set Ω) ≤
              (μ0.toMeasure : Measure Ω) (A : Set Ω) + ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ ∧
            (μ0.toMeasure : Measure Ω) (A : Set Ω) ≤
              (∑ i, c i • ν i) (A : Set Ω) + ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rintro ⟨I, r⟩
    obtain ⟨n, c, ν, hν, hc, hbounds⟩ := hπ.exists_extremePoints_combo_approx h𝒜 hP hPm hex hμP
      (fun j : Fin I.card ↦ ((I.equivFin.symm j : 𝒞) : Set Ω))
      (fun j ↦ h𝒞 _ (I.equivFin.symm j).1.2) (r := r + 1) r.succ_pos
    refine ⟨n, c, ν, hν, hc, fun A hA ↦ ?_⟩
    have h := hbounds (I.equivFin ⟨A, hA⟩)
    rwa [Equiv.symm_apply_apply] at h
  choose n c ν hν hc hbounds using happrox
  have hprob : ∀ p, IsProbabilityMeasure (∑ i, c p i • ν p i : Measure Ω) := fun p ↦
    isProbabilityMeasure_sum_smul (fun i ↦ hP _ (extremePoints_subset (hν p i))) (hc p)
  set combo : Finset 𝒞 × ℕ → WithSetwiseTopology 𝒞 (ProbabilityMeasure Ω) := fun p ↦
    WithSetwiseTopology.ofMeasure (⟨∑ i, c p i • ν p i, hprob p⟩ : ProbabilityMeasure Ω)
    with hcombodef
  -- each `combo p` is a finite convex combination of elements of `L`
  have hmem : ∀ p, combo p ∈ convexCombos L := fun p ↦
    ⟨n p, c p, fun i ↦ WithSetwiseTopology.ofMeasure
      (⟨ν p i, hP _ (extremePoints_subset (hν p i))⟩ : ProbabilityMeasure Ω),
      fun i ↦ hlim _ (hν p i), hc p, rfl⟩
  -- `combo → μ0` along the directed family of stages
  have htendsto : Tendsto combo atTop (𝓝 μ0) := by
    rw [WithSetwiseTopology.tendsto_prob_iff]
    intro B hB
    set ε : Finset 𝒞 × ℕ → ℝ≥0∞ := fun p ↦ ((p.2 + 1 : ℕ) : ℝ≥0∞)⁻¹ with hεdef
    have hsnd : Tendsto (fun p : Finset 𝒞 × ℕ ↦ p.2) atTop atTop :=
      tendsto_atTop_atTop.2 fun b ↦ ⟨(∅, b), fun p hp ↦ hp.2⟩
    have hεtendsto : Tendsto ε atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp ((tendsto_add_atTop_nat 1).comp hsnd)
    have hupper : Tendsto (fun p ↦ (μ0.toMeasure : Measure Ω) B + ε p) atTop
        (𝓝 ((μ0.toMeasure : Measure Ω) B)) := by
      have h := Tendsto.add
        (tendsto_const_nhds (x := (μ0.toMeasure : Measure Ω) B)
          (f := (atTop : Filter (Finset 𝒞 × ℕ)))) hεtendsto
      simpa using h
    have hlower : Tendsto (fun p ↦ (μ0.toMeasure : Measure Ω) B - ε p) atTop
        (𝓝 ((μ0.toMeasure : Measure Ω) B)) := by
      have h := ENNReal.Tendsto.sub
        (tendsto_const_nhds (x := (μ0.toMeasure : Measure Ω) B)
          (f := (atTop : Filter (Finset 𝒞 × ℕ)))) hεtendsto
        (Or.inl (measure_ne_top _ _))
      simpa using h
    have hBev : ∀ᶠ p : Finset 𝒞 × ℕ in atTop, (⟨B, hB⟩ : 𝒞) ∈ p.1 :=
      eventually_atTop.2 ⟨({⟨B, hB⟩}, 0), fun p hp ↦ hp.1 (Finset.mem_singleton_self _)⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
    · filter_upwards [hBev] with p hp
      exact tsub_le_iff_right.2 (hbounds p ⟨B, hB⟩ hp).2
    · filter_upwards [hBev] with p hp
      exact (hbounds p ⟨B, hB⟩ hp).1
  exact mem_closure_of_tendsto htendsto (Eventually.of_forall hmem)


end Density

end MeasureTheory.GibbsMeasure

end

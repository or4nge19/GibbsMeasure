/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Existence

/-!
# A specification with no Gibbs measure

**Georgii Example (4.16).** Over the state space `Bool` on a countably infinite `S`, the
specification `γ` of a single particle at a uniformly random site — `γ_Λ(·|ω)` is the uniform
distribution on the spikes `ω^a`, `a ∈ Λ`, when `ω` vanishes off `Λ`, and the Dirac mass at
`0_Λ ω` otherwise — is a proper, consistent specification (`specification`) with `𝒢(γ) = ∅`
(`GP_eq_empty`). It is not quasilocal (`not_isQuasilocal_specification`): this is Georgii's
example that quasilocality cannot be dropped from Theorems (4.17) and (4.22). For finite `S` the
same kernels do admit a Gibbs measure (`mem_GP_of_finite`), so `[Infinite S]` is sharp.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.Example416

variable {S : Type*} [Countable S] [DecidableEq S]

/-- The configuration with a single `1` at site `a` (Georgii's `ω^a`). -/
def spike (a : S) : S → Bool := fun i ↦ decide (i = a)

/-- `0_Λ ω`: the configuration `ω` with the coordinates in `Λ` set to `0`. -/
def zeroOn (Λ : Finset S) (ω : S → Bool) : S → Bool := fun i ↦ if i ∈ Λ then false else ω i

/-- The guard `ω = 0 off Λ`. -/
def vanishOff (Λ : Finset S) : Set (S → Bool) := {ω | ∀ i, i ∉ Λ → ω i = false}

omit [DecidableEq S] in
lemma measurableSet_vanishOff (Λ : Finset S) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)] (vanishOff Λ) := by
  have : vanishOff Λ = ⋂ i ∈ ((Λ : Set S)ᶜ), (fun ω : S → Bool ↦ ω i) ⁻¹' {false} := by
    ext ω; simp [vanishOff]
  rw [this]
  refine MeasurableSet.biInter (Set.to_countable _) fun i hi ↦ ?_
  exact measurable_cylinderEvent_apply hi (measurableSet_singleton false)

omit [Countable S] in
lemma measurable_zeroOn (Λ : Finset S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)] (zeroOn Λ) := by
  letI : MeasurableSpace (S → Bool) := cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases hi : i ∈ Λ
  · simpa [zeroOn, hi] using (measurable_const : Measurable fun _ : S → Bool ↦ false)
  · simpa [zeroOn, hi] using measurable_cylinderEvent_apply (X := fun _ : S ↦ Bool)
      (show i ∈ ((Λ : Set S)ᶜ) by simpa using hi)

/-- The uniform distribution on the spikes `ω^a`, `a ∈ Λ`. -/
def spikeMeasure (Λ : Finset S) : Measure (S → Bool) :=
  (Λ.card : ℝ≥0∞)⁻¹ • ∑ a ∈ Λ, Measure.dirac (spike a)

instance (Λ : Finset S) [hΛ : Fact Λ.Nonempty] : IsProbabilityMeasure (spikeMeasure Λ) := by
  constructor
  rw [spikeMeasure, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [ENNReal.inv_mul_cancel]
  · exact_mod_cast hΛ.out.card_pos.ne'
  · exact ENNReal.natCast_ne_top _

/-- The kernels of Georgii (4.16): on the guard `ω = 0 off Λ`, the uniform distribution on the
spikes in `Λ`; otherwise the Dirac mass at `0_Λ ω`. (For `Λ = ∅` the identity kernel.) -/
def kernel (Λ : Finset S) :
    Kernel[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)] (S → Bool) (S → Bool) :=
  letI : MeasurableSpace (S → Bool) := cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)
  if h : Λ = ∅ then
    Kernel.deterministic id (measurable_id.mono le_rfl (le_of_eq (by
      subst h
      rw [Finset.coe_empty, Set.compl_empty, cylinderEvents_univ])))
  else
    haveI := Classical.decPred (· ∈ vanishOff Λ)
    Kernel.piecewise (measurableSet_vanishOff Λ) (Kernel.const _ (spikeMeasure Λ))
      (Kernel.deterministic (zeroOn Λ) (measurable_zeroOn Λ))

/-- The kernels of (4.16) are probability kernels. -/
instance (Λ : Finset S) : IsMarkovKernel (kernel (S := S) Λ) := by
  unfold kernel
  split_ifs with h
  · exact Kernel.isMarkovKernel_deterministic _
  · haveI : Fact Λ.Nonempty := ⟨Finset.nonempty_iff_ne_empty.2 h⟩
    infer_instance

omit [Countable S] in
/-- Spikes at sites of `Λ` agree with a configuration vanishing off `Λ`, outside `Λ`. -/
lemma spike_eqOn_compl {Λ : Finset S} {a : S} (ha : a ∈ Λ) {ω : S → Bool} (hω : ω ∈ vanishOff Λ)
    {i : S} (hi : i ∉ Λ) : spike a i = ω i := by
  have h1 : spike a i = false := by
    simp only [spike, decide_eq_false_iff_not]
    rintro rfl; exact hi ha
  rw [h1, hω i hi]

omit [Countable S] in
lemma zeroOn_eqOn_compl (Λ : Finset S) (ω : S → Bool) {i : S} (hi : i ∉ Λ) :
    zeroOn Λ ω i = ω i := by simp [zeroOn, hi]

omit [Countable S] [DecidableEq S] in
/-- A `cylinderEvents Λᶜ`-measurable set has the same indicator at configurations agreeing
outside `Λ`. -/
lemma indicator_eq_of_eqOn_compl {Λ : Finset S} {B : Set (S → Bool)}
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)] B)
    {ω ω' : S → Bool} (h : ∀ i, i ∉ Λ → ω' i = ω i) :
    B.indicator (1 : (S → Bool) → ℝ≥0∞) ω' = B.indicator 1 ω := by
  have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)]
      (B.indicator (1 : (S → Bool) → ℝ≥0∞)) := by
    letI : MeasurableSpace (S → Bool) := cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)
    exact measurable_const.indicator hB
  exact hmeas.dependsOn_of_cylinderEvents fun i hi ↦ h i (by simpa using hi)

/-- **Properness** of the kernels of (4.16). -/
lemma isProper_kernel (Λ : Finset S) : (kernel (S := S) Λ).IsProper := by
  classical
  rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
  intro A hA B hB x
  have hAB : MeasurableSet (A ∩ B) := hA.inter (cylinderEvents_le_pi _ hB)
  unfold kernel
  split_ifs with h
  · -- `Λ = ∅`: the identity kernel
    rw [Kernel.deterministic_apply, id_eq, Measure.dirac_apply' _ hAB, Measure.dirac_apply' _ hA,
      Set.inter_indicator_one, Pi.mul_apply, mul_comm]
  · rw [Kernel.piecewise_apply]
    split_ifs with hx
    · -- on the guard: the uniform distribution on the spikes
      rw [Kernel.const_apply, spikeMeasure, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
        smul_eq_mul, Measure.finsetSum_apply, Measure.finsetSum_apply]
      simp only [Measure.dirac_apply' _ hAB, Measure.dirac_apply' _ hA, Set.inter_indicator_one,
        Pi.mul_apply]
      have hspike : ∀ a ∈ Λ, B.indicator (1 : (S → Bool) → ℝ≥0∞) (spike a) = B.indicator 1 x :=
        fun a ha ↦ indicator_eq_of_eqOn_compl hB fun i hi ↦ spike_eqOn_compl ha hx hi
      rw [Finset.sum_congr rfl fun a ha ↦ by rw [hspike a ha], ← Finset.sum_mul]
      ring
    · -- off the guard: the Dirac mass at `0_Λ x`
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hAB, Measure.dirac_apply' _ hA,
        Set.inter_indicator_one, Pi.mul_apply,
        indicator_eq_of_eqOn_compl hB fun i hi ↦ zeroOn_eqOn_compl Λ x hi, mul_comm]

lemma kernel_apply_of_mem {Λ : Finset S} (hΛ : Λ ≠ ∅) {x : S → Bool} (hx : x ∈ vanishOff Λ) :
    kernel (S := S) Λ x = spikeMeasure Λ := by
  classical
  unfold kernel
  rw [dif_neg hΛ, Kernel.piecewise_apply, if_pos hx, Kernel.const_apply]

lemma kernel_apply_of_not_mem {Λ : Finset S} (hΛ : Λ ≠ ∅) {x : S → Bool}
    (hx : x ∉ vanishOff Λ) : kernel (S := S) Λ x = Measure.dirac (zeroOn Λ x) := by
  classical
  unfold kernel
  rw [dif_neg hΛ, Kernel.piecewise_apply, if_neg hx, Kernel.deterministic_apply]

lemma kernel_empty_apply (x : S → Bool) : kernel (S := S) ∅ x = Measure.dirac x := by
  unfold kernel
  rw [dif_pos rfl, Kernel.deterministic_apply, id_eq]

omit [Countable S] in
/-- A spike at `a` vanishes off `Λ` iff `a ∈ Λ`. -/
lemma spike_mem_vanishOff_iff {Λ : Finset S} {a : S} : spike a ∈ vanishOff Λ ↔ a ∈ Λ := by
  constructor
  · intro h
    by_contra ha
    have := h a ha
    simp [spike] at this
  · intro ha i hi
    simp only [spike, decide_eq_false_iff_not]
    rintro rfl; exact hi ha

/-- `0_Λ x` vanishes off `Λ'` iff `x` vanishes off `Λ ∪ Λ'`. -/
lemma zeroOn_mem_vanishOff_iff {Λ Λ' : Finset S} {x : S → Bool} :
    zeroOn Λ x ∈ vanishOff Λ' ↔ x ∈ vanishOff (Λ ∪ Λ') := by
  constructor
  · intro h i hi
    have hi' : i ∉ Λ' := fun h' ↦ hi (Finset.mem_union_right _ h')
    have hiΛ : i ∉ Λ := fun h' ↦ hi (Finset.mem_union_left _ h')
    have := h i hi'
    rwa [zeroOn_eqOn_compl Λ x hiΛ] at this
  · intro h i hi
    by_cases hiΛ : i ∈ Λ
    · simp [zeroOn, hiΛ]
    · rw [zeroOn_eqOn_compl Λ x hiΛ]
      exact h i (by simp [hiΛ, hi])

omit [Countable S] in
lemma zeroOn_zeroOn_of_subset {Λ₁ Λ₂ : Finset S} (h : Λ₁ ⊆ Λ₂) (x : S → Bool) :
    zeroOn Λ₁ (zeroOn Λ₂ x) = zeroOn Λ₂ x := by
  funext i
  by_cases hi : i ∈ Λ₁
  · simp [zeroOn, hi, h hi]
  · simp [zeroOn, hi]

omit [Countable S] in
lemma zeroOn_spike_of_not_mem {Λ : Finset S} {a : S} (ha : a ∉ Λ) : zeroOn Λ (spike a) = spike a := by
  funext i
  by_cases hi : i ∈ Λ
  · have : spike a i = false := by
      simp only [spike, decide_eq_false_iff_not]
      rintro rfl; exact ha hi
    simp [zeroOn, hi, this]
  · simp [zeroOn, hi]

lemma measurable_kernel_apply (Λ : Finset S) {s : Set (S → Bool)} (hs : MeasurableSet s) :
    Measurable fun b ↦ kernel (S := S) Λ b s :=
  ((kernel Λ).measurable_coe hs).mono cylinderEvents_le_pi le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Consistency** of the kernels of (4.16): Georgii's computation
`γ_Δ γ_Λ = γ_Δ` for `Λ ⊆ Δ`. -/
lemma isConsistent_kernel : IsConsistent (kernel (S := S)) := by
  classical
  intro Λ₁ Λ₂ h
  refine Kernel.ext fun x ↦ Measure.ext fun s hs ↦ ?_
  rw [Kernel.comp_apply' _ _ _ hs]
  change ∫⁻ b, kernel (S := S) Λ₁ b s ∂(kernel (S := S) Λ₂ x) = kernel (S := S) Λ₂ x s
  by_cases h₂ : Λ₂ = ∅
  · -- then `Λ₁ = ∅` too: identity kernels
    have h₁ : Λ₁ = ∅ := Finset.subset_empty.1 (h₂ ▸ h)
    subst h₁; subst h₂
    rw [kernel_empty_apply, lintegral_dirac' _ (measurable_kernel_apply _ hs), kernel_empty_apply]
  by_cases hx : x ∈ vanishOff Λ₂
  · -- on the guard of `Λ₂`: average over the spikes of `Λ₂`
    rw [kernel_apply_of_mem h₂ hx, spikeMeasure, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    simp only [lintegral_dirac' _ (measurable_kernel_apply Λ₁ hs)]
    rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
    congr 1
    by_cases h₁ : Λ₁ = ∅
    · subst h₁
      simp only [kernel_empty_apply]
    · -- split the sum over `Λ₂` into `Λ₁` and `Λ₂ \ Λ₁`
      have hne : (Λ₁.card : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (Finset.nonempty_iff_ne_empty.2 h₁).card_pos.ne'
      have hkern : ∀ a ∈ Λ₂, kernel (S := S) Λ₁ (spike a) s =
          if a ∈ Λ₁ then spikeMeasure Λ₁ s else Measure.dirac (spike a) s := by
        intro a _
        split_ifs with ha
        · rw [kernel_apply_of_mem h₁ (spike_mem_vanishOff_iff.2 ha)]
        · rw [kernel_apply_of_not_mem h₁ (fun h' ↦ ha (spike_mem_vanishOff_iff.1 h')),
            zeroOn_spike_of_not_mem ha]
      rw [Finset.sum_congr rfl hkern, ← Finset.sum_sdiff h, ← Finset.sum_sdiff h]
      have hA : ∀ a ∈ Λ₂ \ Λ₁, (if a ∈ Λ₁ then spikeMeasure Λ₁ s else Measure.dirac (spike a) s)
          = Measure.dirac (spike a) s := fun a ha ↦ by
        rw [if_neg (Finset.mem_sdiff.1 ha).2]
      have hB : ∀ a ∈ Λ₁, (if a ∈ Λ₁ then spikeMeasure Λ₁ s else Measure.dirac (spike a) s)
          = spikeMeasure Λ₁ s := fun a ha ↦ by rw [if_pos ha]
      rw [Finset.sum_congr rfl hA, Finset.sum_congr rfl hB, Finset.sum_const, nsmul_eq_mul,
        spikeMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
        ← mul_assoc, ENNReal.mul_inv_cancel hne (ENNReal.natCast_ne_top _), one_mul]
  · -- off the guard of `Λ₂`: the Dirac mass at `0_{Λ₂} x`, which is off the guard of `Λ₁`
    rw [kernel_apply_of_not_mem h₂ hx, lintegral_dirac' _ (measurable_kernel_apply Λ₁ hs)]
    have hx' : zeroOn Λ₂ x ∉ vanishOff Λ₁ := by
      rw [zeroOn_mem_vanishOff_iff, Finset.union_eq_left.2 h]
      exact hx
    by_cases h₁ : Λ₁ = ∅
    · subst h₁
      rw [kernel_empty_apply]
    · rw [kernel_apply_of_not_mem h₁ hx', zeroOn_zeroOn_of_subset h]

/-- **Georgii Example (4.16)**: the specification with no Gibbs measure. -/
def specification : Specification S Bool where
  toPreSpecification := { toFun := kernel, isConsistent' := isConsistent_kernel }
  isMarkovKernel' := fun Λ ↦ by change IsMarkovKernel (kernel Λ); infer_instance
  isProper' := fun Λ ↦ isProper_kernel Λ

omit [Countable S] in
lemma spike_apply_self (a : S) : spike a a = true := by simp [spike]

omit [Countable S] in
lemma spike_injective : Function.Injective (spike (S := S)) := by
  intro a b h
  have := congrArg (fun ω : S → Bool ↦ ω a) h
  simpa [spike, eq_comm] using this

/-- The two-site kernel gives no mass to configurations with `1` at both sites. -/
lemma kernel_pair_apply_eq_zero {i j : S} (hij : i ≠ j) (ω : S → Bool) :
    kernel (S := S) {i, j} ω {ω' | ω' i = true ∧ ω' j = true} = 0 := by
  classical
  have hne : ({i, j} : Finset S) ≠ ∅ := by simp
  have hmeas : MeasurableSet {ω' : S → Bool | ω' i = true ∧ ω' j = true} := by
    show MeasurableSet ((fun f : S → Bool ↦ f i) ⁻¹' {true} ∩ (fun f : S → Bool ↦ f j) ⁻¹' {true})
    exact (measurable_pi_apply i (measurableSet_singleton _)).inter
      (measurable_pi_apply j (measurableSet_singleton _))
  by_cases hω : ω ∈ vanishOff {i, j}
  · rw [kernel_apply_of_mem hne hω, spikeMeasure, Measure.smul_apply, Measure.finsetSum_apply]
    have h0 : ∀ a ∈ ({i, j} : Finset S),
        Measure.dirac (spike a) {ω' : S → Bool | ω' i = true ∧ ω' j = true} = 0 := by
      intro a _
      rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
      rintro ⟨h1, h2⟩
      simp only [spike, decide_eq_true_eq] at h1 h2
      exact hij (h1.trans h2.symm)
    rw [Finset.sum_congr rfl h0]
    simp
  · rw [kernel_apply_of_not_mem hne hω, Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    rintro ⟨h1, -⟩
    simp [zeroOn] at h1

/-- No kernel gives mass to the zero configuration. -/
lemma kernel_apply_zero_eq_zero {Λ : Finset S} (hΛ : Λ ≠ ∅) (ω : S → Bool) :
    kernel (S := S) Λ ω {fun _ ↦ false} = 0 := by
  classical
  have hmeas : MeasurableSet ({fun _ ↦ false} : Set (S → Bool)) := measurableSet_singleton _
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hΛ
  by_cases hω : ω ∈ vanishOff Λ
  · rw [kernel_apply_of_mem hΛ hω, spikeMeasure, Measure.smul_apply, Measure.finsetSum_apply]
    have h0 : ∀ b ∈ Λ, Measure.dirac (spike b) ({fun _ ↦ false} : Set (S → Bool)) = 0 := by
      intro b _
      rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
      intro h
      have := congrArg (fun ω : S → Bool ↦ ω b) h
      simp [spike] at this
    rw [Finset.sum_congr rfl h0]
    simp
  · rw [kernel_apply_of_not_mem hΛ hω, Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    intro h
    apply hω
    intro i hi
    have := congrArg (fun ω : S → Bool ↦ ω i) h
    simpa [zeroOn, hi] using this

/-- The mass of a spike under the `Λ`-kernel is at most `|Λ|⁻¹` when `a ∈ Λ`. -/
lemma kernel_apply_spike_le {Λ : Finset S} {a : S} (ha : a ∈ Λ) (ω : S → Bool) :
    kernel (S := S) Λ ω {spike a} ≤ (Λ.card : ℝ≥0∞)⁻¹ := by
  classical
  have hΛ : Λ ≠ ∅ := Finset.ne_empty_of_mem ha
  have hmeas : MeasurableSet ({spike a} : Set (S → Bool)) := measurableSet_singleton _
  by_cases hω : ω ∈ vanishOff Λ
  · rw [kernel_apply_of_mem hΛ hω, spikeMeasure, Measure.smul_apply, Measure.finsetSum_apply,
      smul_eq_mul]
    have h1 : ∀ b ∈ Λ, Measure.dirac (spike b) ({spike a} : Set (S → Bool))
        = if b = a then 1 else 0 := by
      intro b _
      rw [Measure.dirac_apply' _ hmeas]
      by_cases hb : b = a
      · subst hb; simp
      · rw [if_neg hb, Set.indicator_of_notMem]
        intro h
        exact hb (spike_injective (by simpa using h))
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' Λ a, if_pos ha, mul_one]
  · rw [kernel_apply_of_not_mem hΛ hω, Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    · simp
    · intro h
      have := congrArg (fun ω : S → Bool ↦ ω a) h
      simp [zeroOn, ha, spike] at this

/-! ### Infinite `S`: no Gibbs measure -/

section Infinite

variable [Infinite S]

/-- **Georgii Example (4.16).** The specification `γ` of a single particle at a uniformly random
site has **no Gibbs measure**: `𝒢(γ) = ∅`. -/
theorem GP_eq_empty : GP (S := S) (E := Bool) (specification (S := S)) = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  intro μ hμ
  have hprob : IsProbabilityMeasure (μ : Measure (S → Bool)) := μ.2
  -- (a) no two `1`s
  have hpair : ∀ i j : S, i ≠ j →
      (μ : Measure (S → Bool)) {ω' | ω' i = true ∧ ω' j = true} = 0 := by
    intro i j hij
    have hmeas : MeasurableSet {ω' : S → Bool | ω' i = true ∧ ω' j = true} := by
      show MeasurableSet ((fun f : S → Bool ↦ f i) ⁻¹' {true} ∩ (fun f : S → Bool ↦ f j) ⁻¹' {true})
      exact (measurable_pi_apply i (measurableSet_singleton _)).inter
        (measurable_pi_apply j (measurableSet_singleton _))
    refine le_antisymm ?_ zero_le
    exact apply_le_of_mem_GP hμ {i, j} hmeas fun ω ↦
      le_of_eq (kernel_pair_apply_eq_zero hij ω)
  -- (b) no zero configuration
  have hzero : (μ : Measure (S → Bool)) {fun _ ↦ false} = 0 := by
    obtain ⟨a⟩ := (inferInstance : Nonempty S)
    refine le_antisymm ?_ zero_le
    exact apply_le_of_mem_GP hμ {a} (measurableSet_singleton _) fun ω ↦
      le_of_eq (kernel_apply_zero_eq_zero (by simp) ω)
  -- (c) no single spike
  have hspike : ∀ a : S, (μ : Measure (S → Bool)) {spike a} = 0 := by
    intro a
    refine le_antisymm ?_ zero_le
    have hbound : ∀ n : ℕ, (μ : Measure (S → Bool)) {spike a} ≤ (n : ℝ≥0∞)⁻¹ := by
      intro n
      obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq S n
      have hcard : (n : ℝ≥0∞) ≤ ((insert a s).card : ℝ≥0∞) := by
        exact_mod_cast hs ▸ Finset.card_le_card (Finset.subset_insert a s)
      calc (μ : Measure (S → Bool)) {spike a}
          ≤ ((insert a s).card : ℝ≥0∞)⁻¹ :=
            apply_le_of_mem_GP hμ (insert a s) (measurableSet_singleton _) fun ω ↦
              kernel_apply_spike_le (Finset.mem_insert_self a s) ω
        _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hcard
    exact ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero hbound
  -- (d) every configuration has zero, one, or at least two `1`s
  have hcover : (Set.univ : Set (S → Bool)) ⊆
      (⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {ω' : S → Bool | ω' i = true ∧ ω' j = true})
        ∪ {fun _ ↦ false} ∪ ⋃ a, {spike a} := by
    intro ω _
    by_cases h2 : ∃ i j, i ≠ j ∧ ω i = true ∧ ω j = true
    · obtain ⟨i, j, hij, hi, hj⟩ := h2
      exact Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2
        ⟨hij, hi, hj⟩⟩⟩))
    · push Not at h2
      by_cases h1 : ∃ a, ω a = true
      · obtain ⟨a, ha⟩ := h1
        refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
        rw [Set.mem_singleton_iff]
        funext i
        by_cases hia : i = a
        · subst hia; simp [spike, ha]
        · have hi : ω i = false := by
            have h := h2 a i (Ne.symm hia) ha
            cases hωi : ω i with
            | false => rfl
            | true => simp_all
          simp [spike, hia, hi]
      · push Not at h1
        refine Or.inl (Or.inr ?_)
        rw [Set.mem_singleton_iff]
        funext i
        exact Bool.eq_false_iff.2 (h1 i)
  have hnull : (μ : Measure (S → Bool))
      ((⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {ω' : S → Bool | ω' i = true ∧ ω' j = true})
        ∪ {fun _ ↦ false} ∪ ⋃ a, {spike a}) = 0 := by
    refine measure_union_null (measure_union_null ?_ hzero) (measure_iUnion_null hspike)
    exact measure_iUnion_null fun i ↦ measure_iUnion_null fun j ↦
      measure_iUnion_null fun hij ↦ hpair i j hij
  have : (μ : Measure (S → Bool)) Set.univ = 0 :=
    le_antisymm ((measure_mono hcover).trans hnull.le) zero_le
  rw [measure_univ] at this
  exact one_ne_zero this

end Infinite

/-! ### The specification is not quasilocal -/

/-- The observable `σ_a`, the indicator of `{σ_a = 1}`, as a bounded function. -/
def spinAt (a : S) : lp (fun _ : S → Bool ↦ ℝ) ∞ :=
  ⟨({ω : S → Bool | ω a = true} : Set (S → Bool)).indicator 1, memℓp_infty ⟨1, by
    rintro _ ⟨ω, rfl⟩
    by_cases h : ω ∈ ({ω : S → Bool | ω a = true} : Set (S → Bool)) <;> simp [h]⟩⟩

omit [Countable S] [DecidableEq S] in
lemma coeFn_spinAt (a : S) :
    ⇑(spinAt a) = ({ω : S → Bool | ω a = true} : Set (S → Bool)).indicator 1 := rfl

omit [Countable S] [DecidableEq S] in
lemma measurableSet_setOf_apply_eq_true (a : S) :
    MeasurableSet {ω : S → Bool | ω a = true} := by
  show MeasurableSet ((fun ω : S → Bool ↦ ω a) ⁻¹' {true})
  exact measurable_pi_apply a (measurableSet_singleton _)

omit [Countable S] [DecidableEq S] in
/-- `σ_a` is a local observable (Georgii (2.20)(a)). -/
lemma spinAt_mem_localFunctions (a : S) : spinAt a ∈ localFunctions S Bool := by
  refine mem_localFunctions.2 ⟨{a}, ?_⟩
  rw [mem_localFunctionsOn, coeFn_spinAt]
  let _ : MeasurableSpace (S → Bool) :=
    cylinderEvents (X := fun _ : S ↦ Bool) (({a} : Finset S) : Set S)
  refine measurable_one.indicator ?_
  show MeasurableSet ((fun ω : S → Bool ↦ ω a) ⁻¹' {true})
  exact measurable_cylinderEvent_apply (X := fun _ : S ↦ Bool) (by simp) (measurableSet_singleton _)

/-- Georgii (4.16): `γ_{{a}}(σ_a = 1 | ·) = 1_{ω = 0 off {a}}`, a tail-dependent observable. -/
lemma action_spinAt_apply (a : S) (η : S → Bool) :
    (Specification.action (specification (S := S)) {a} (spinAt a) : (S → Bool) → ℝ) η
      = (vanishOff {a}).indicator 1 η := by
  rw [Specification.action_apply, coeFn_spinAt,
    integral_indicator_one (measurableSet_setOf_apply_eq_true a)]
  change (kernel (S := S) {a} η).real {ω : S → Bool | ω a = true} = _
  by_cases hη : η ∈ vanishOff {a}
  · have hspike : spikeMeasure ({a} : Finset S) = Measure.dirac (spike a) := by
      simp [spikeMeasure]
    rw [kernel_apply_of_mem (Finset.singleton_ne_empty a) hη, Set.indicator_of_mem hη, hspike,
      measureReal_def, Measure.dirac_apply_of_mem (show spike a ∈ {ω : S → Bool | ω a = true} by
        simp [spike])]
    simp
  · rw [kernel_apply_of_not_mem (Finset.singleton_ne_empty a) hη, Set.indicator_of_notMem hη,
      measureReal_def, Measure.dirac_apply' _ (measurableSet_setOf_apply_eq_true a),
      Set.indicator_of_notMem (by simp [zeroOn])]
    simp

/-- **Georgii Example (4.16) is not quasilocal** (Definition (2.23)): `γ_{{a}}(σ_a = 1 | ·)` is
the indicator of `ω = 0 off {a}`, which changes by `1` under a spike at any far-away site. -/
theorem not_isQuasilocal_specification [Infinite S] :
    ¬ (specification (S := S)).IsQuasilocal := by
  intro hql
  obtain ⟨a⟩ := (inferInstance : Nonempty S)
  have hmem : Specification.action (specification (S := S)) {a} (spinAt a)
      ∈ quasilocalFunctions S Bool :=
    hql {a} (spinAt a) (localFunctions_le_quasilocalFunctions (spinAt_mem_localFunctions a))
  obtain ⟨Δ, hΔ⟩ := ((ENNReal.tendsto_nhds_zero.1
    (tendsto_oscOutside_of_mem_quasilocalFunctions hmem)) 2⁻¹ (by simp)).exists
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert a Δ)
  have hba : b ≠ a := fun h ↦ hb (h ▸ Finset.mem_insert_self a Δ)
  have hagree : ∀ i ∈ Δ, (fun _ ↦ false : S → Bool) i = spike b i := by
    intro i hi
    have hib : i ≠ b := fun h ↦ hb (h ▸ Finset.mem_insert_of_mem hi)
    simp [spike, hib]
  have hle := le_oscOutside (Λ := Δ)
    (f := ⇑(Specification.action (specification (S := S)) {a} (spinAt a))) hagree
  rw [action_spinAt_apply, action_spinAt_apply,
    Set.indicator_of_mem (show (fun _ ↦ false : S → Bool) ∈ vanishOff {a} from fun _ _ ↦ rfl),
    Set.indicator_of_notMem (show spike b ∉ vanishOff {a} from
      fun h ↦ hba (Finset.mem_singleton.1 (spike_mem_vanishOff_iff.1 h)))] at hle
  simp only [Pi.one_apply, sub_zero, abs_one, ENNReal.ofReal_one] at hle
  exact absurd (ENNReal.one_le_inv.1 (hle.trans hΔ)) (by norm_num)

/-! ### Finite `S`: the same kernels admit a Gibbs measure, so `[Infinite S]` is sharp -/

section Finite

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

instance : Fact (Finset.univ : Finset S).Nonempty := ⟨Finset.univ_nonempty⟩

lemma kernel_univ_apply (x : S → Bool) :
    kernel (S := S) Finset.univ x = spikeMeasure Finset.univ :=
  kernel_apply_of_mem Finset.univ_nonempty.ne_empty fun i hi ↦ absurd (Finset.mem_univ i) hi

/-- For finite `S` the uniform distribution on all spikes is a Gibbs measure, so `[Infinite S]`
is essential in `GP_eq_empty`. -/
theorem mem_GP_of_finite :
    (⟨spikeMeasure Finset.univ, inferInstance⟩ : ProbabilityMeasure (S → Bool)) ∈
      GP (S := S) (E := Bool) (specification (S := S)) := by
  change Specification.IsGibbsMeasure (specification (S := S)) (spikeMeasure Finset.univ)
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  intro Λ
  have h := Specification.bind (γ := specification (S := S)) (Finset.subset_univ Λ) (fun _ ↦ false)
  change (kernel Finset.univ (fun _ ↦ false)).bind (kernel Λ) = kernel Finset.univ (fun _ ↦ false) at h
  rwa [kernel_univ_apply] at h

end Finite

end MeasureTheory.GibbsMeasure.Example416

end

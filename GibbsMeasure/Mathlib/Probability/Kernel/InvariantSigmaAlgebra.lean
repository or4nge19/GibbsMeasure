/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Invariants
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Analysis.Convex.Extreme
public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Dynamics.Ergodic.Action.Basic

/-!
# The almost surely invariant σ-algebra of a Markov kernel

For a Markov kernel `π : Kernel Ω Ω` and a finite measure `μ` with `Kernel.Invariant π μ`, the
sets `A` with `π(A | ·) = 1_A` `μ`-a.e. form a σ-algebra `I_π(μ)`
(`ProbabilityTheory.Kernel.aeInvariantSigmaAlgebra`), and a density `f` of finite mass makes `f·μ`
invariant exactly when `f` is `I_π(μ)`-measurable
(`ProbabilityTheory.Kernel.invariant_withDensity_iff_measurable`).

For a family `κ : ι → Kernel Ω Ω` of Markov kernels all leaving `μ` invariant, a `μ`-invariant
probability measure is an extreme point of the convex set of such measures if and only if it is
trivial on `I_Π(μ) = ⨅ i, I_{κ i}(μ)`
(`ProbabilityTheory.Kernel.mem_extremePoints_iff_trivialOn`).

This contains Mathlib's `Ergodic.iff_mem_extremePoints` and extends it in two directions, to
genuinely random kernels and to families: `preErgodic_iff_trivialOn_aeInvariant` identifies
Mathlib's `PreErgodic` with triviality on `I_π(μ)` for a deterministic kernel.

## Why almost sure, and not strict, invariance

Mathlib's `PreErgodic` is a zero-one law over the *strictly* invariant measurable sets
`T ⁻¹' s = s`. That is not stable under changing `T` on a null set as stated, and the equivalence
with the usual a.e. formulation
(`preErgodic_iff_forall_nullMeasurableSet`, `preErgodic_congr_ae`) rests on
`QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae`, which corrects an a.e. invariant set to
a strictly invariant one by iterating `T` — so it needs `T` measurable, not merely a.e. measurable.

`aeInvariantSets` is defined by an a.e. condition and so depends only on the a.e. class of the
kernel outright (`aeInvariantSets_congr`), with no correction step. For a general kernel no such
correction exists: `TwoAbsorbingStates` is a stochastic matrix whose strictly invariant σ-algebra
is trivial while its invariant measures form a segment. Almost sure invariance is therefore the
primitive here, and the strictly invariant sets are not an alternative definition but a
special-case convenience.

The `Filter.EventuallyConst` API is used in exactly one place,
`preErgodic_iff_forall_nullMeasurableSet`, which is the only bridge to Mathlib's `PreErgodic`;
every other statement is phrased as `μ s = 0 ∨ μ s = 1`. That lemma also consumes
`MeasurePreserving.quasiMeasurePreserving`, so if `MeasurePreserving` is ever weakened to require
only `AEMeasurable`, it is the single place needing an explicit `Measurable T`. Almost sure
invariance cannot be weakened to strict invariance, and `TwoAbsorbingStates` below proves it
(Georgii's Example (7.5)): a stochastic matrix on three points whose strictly invariant σ-algebra
is trivial while its invariant measures form a segment, so triviality on it does not imply
extremality.

## The strictly invariant σ-algebra of a countable group action

For a *group action* the situation of Example (7.5) cannot occur once the group is countable:
`MeasurableSpace.smulInvariants M Ω` is Georgii's σ-algebra `𝓘` (14.2) of strictly invariant
measurable sets, a measurable function is `𝓘`-measurable iff it is invariant
(`MeasurableSpace.measurable_invariants_iff`, Remark (14.3)(1)), and over a countable group every
a.e. invariant set or density can be corrected to a strictly invariant one
(`exists_measurableSet_invariants_ae_eq`, `exists_measurable_invariants_ae_eq`,
Remark (14.3)(2) — the a.s. invariant σ-algebra `𝓘(μ)` is the `μ`-completion of `𝓘`). This
upgrades the a.s. statements to Georgii's Theorem (14.5) as literally stated: extremality in the
invariant probability measures is triviality on `𝓘`
(`mem_extremePoints_iff_forall_measurableSet_invariants`, (14.5)(a) and Definition (14.6) via
`ergodicSMul_iff_forall_measurableSet_invariants`), an absolutely continuous probability measure
is invariant iff its density is `𝓘`-measurable (`smulInvariantMeasure_iff_exists_withDensity`,
(14.5)(b)), an invariant probability measure is determined by its restriction to `𝓘`
(`eq_of_forall_measurableSet_invariants_eq`, (14.5)(c)), and distinct extreme invariant
probability measures are separated by a set in `𝓘`
(`exists_measurableSet_invariants_eq_one_eq_zero`, (14.5)(d)).

## References

Hans-Otto Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Proposition (7.3),
Corollary (7.4), and §14.1: (14.2), Remark (14.3), Theorem (14.5), Definition (14.6).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal symmDiff

/-! ### The strictly invariant σ-algebra of an action (Georgii (14.2)) -/

namespace MeasurableSpace

variable {M Ω : Type*} [m : MeasurableSpace Ω] [SMul M Ω]

variable (M Ω) in
/-- **Georgii (14.2).** The σ-algebra `𝓘` of strictly invariant measurable sets of an action:
the measurable `A` with `(c • ·) ⁻¹' A = A` for every `c`. It is the infimum over `c : M` of
Mathlib's single-map `MeasurableSpace.invariants (c • ·)` inside `m`
(`MeasurableSpace.smulInvariants_eq_inf_iInf_invariants`). For a group action these are exactly
the measurable sets with `g • A = A` for all `g`
(`MeasurableSpace.measurableSet_smulInvariants_iff_smul_eq`). -/
@[instance_reducible]
def smulInvariants : MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ ∀ c : M, (c • ·) ⁻¹' A = A
  measurableSet_empty := ⟨.empty, fun _ ↦ Set.preimage_empty⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun c ↦ by
    rw [Set.preimage_compl, hA.2 c]⟩
  measurableSet_iUnion f hf := ⟨.iUnion fun n ↦ (hf n).1, fun c ↦ by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun n ↦ (hf n).2 c⟩

@[simp] lemma measurableSet_smulInvariants {A : Set Ω} :
    MeasurableSet[smulInvariants M Ω] A ↔ MeasurableSet A ∧ ∀ c : M, (c • ·) ⁻¹' A = A := Iff.rfl

lemma smulInvariants_le : smulInvariants M Ω ≤ m := fun _ h ↦ h.1

/-- The action-invariant σ-algebra is the infimum, inside `m`, of Mathlib's single-map
`MeasurableSpace.invariants (c • ·)` over the acting elements. -/
lemma smulInvariants_eq_inf_iInf_invariants :
    smulInvariants M Ω = m ⊓ ⨅ c : M, invariants (c • · : Ω → Ω) := by
  ext A
  rw [measurableSet_smulInvariants, measurableSet_inf, measurableSet_iInf]
  simp only [measurableSet_invariants]
  exact ⟨fun h ↦ ⟨h.1, fun c ↦ ⟨h.1, h.2 c⟩⟩, fun h ↦ ⟨h.1, fun c ↦ (h.2 c).2⟩⟩

/-- Georgii (14.3)(1), the easy direction: a measurable invariant function is
`𝓘`-measurable. -/
lemma measurable_invariants_of_forall_smul_eq {X : Type*} [MeasurableSpace X] {f : Ω → X}
    (hfm : Measurable f) (hf : ∀ (c : M) (ω : Ω), f (c • ω) = f ω) :
    Measurable[smulInvariants M Ω] f := fun _U hU ↦
  ⟨hfm hU, fun c ↦ by ext ω; simp [hf c ω]⟩

/-- Georgii (14.3)(1), the substantial direction: an `𝓘`-measurable function into a space with
measurable singletons is invariant, because each fibre `f ⁻¹' {f ω}` is a strictly invariant
set containing `ω`. -/
lemma smul_eq_of_measurable_invariants {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {f : Ω → X} (hf : Measurable[smulInvariants M Ω] f) (c : M)
    (ω : Ω) : f (c • ω) = f ω := by
  have h := (hf (measurableSet_singleton (f ω))).2 c
  have hmem : ω ∈ f ⁻¹' {f ω} := rfl
  rw [← h] at hmem
  exact hmem

/-- **Georgii, Remark (14.3)(1).** A measurable function into a space with measurable singletons
is measurable for the invariant σ-algebra `𝓘` if and only if it is invariant:
`f (c • ω) = f ω` for all `c` and `ω`. -/
theorem measurable_invariants_iff {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {f : Ω → X} :
    Measurable[smulInvariants M Ω] f ↔ Measurable f ∧ ∀ (c : M) (ω : Ω), f (c • ω) = f ω :=
  ⟨fun hf ↦ ⟨hf.mono smulInvariants_le le_rfl, smul_eq_of_measurable_invariants hf⟩,
    fun hf ↦ measurable_invariants_of_forall_smul_eq hf.1 hf.2⟩

open scoped Pointwise in
/-- For a group action, the strictly invariant sets are the measurable sets fixed setwise by
every group element — Georgii's (14.2) as literally stated, `θ_i A = A`. -/
lemma measurableSet_smulInvariants_iff_smul_eq {G : Type*} [Group G] [MulAction G Ω] {A : Set Ω} :
    MeasurableSet[smulInvariants G Ω] A ↔ MeasurableSet A ∧ ∀ g : G, g • A = A := by
  rw [measurableSet_smulInvariants]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h g
    have hg := h g⁻¹
    rwa [Set.preimage_smul, inv_inv] at hg
  · intro h g
    rw [Set.preimage_smul, h g⁻¹]

end MeasurableSpace

namespace ProbabilityTheory.Kernel

variable {Ω : Type*} {m : MeasurableSpace Ω} {π : Kernel Ω Ω} {μ : Measure Ω}

variable (π μ) in
/-- The sets that are `μ`-almost surely `π`-invariant: `π(A | ·) = 1_A` holds `μ`-a.e. -/
def aeInvariantSets : Set (Set Ω) :=
  {A | MeasurableSet A ∧ ∀ᵐ ω ∂μ, π ω A = A.indicator 1 ω}

lemma mem_aeInvariantSets {A : Set Ω} :
    A ∈ aeInvariantSets π μ ↔
      MeasurableSet A ∧ ∀ᵐ ω ∂μ, π ω A = A.indicator 1 ω := Iff.rfl

lemma measurableSet_of_mem_aeInvariantSets {A : Set Ω} (h : A ∈ aeInvariantSets π μ) :
    MeasurableSet A := h.1

/-- `aeInvariantSets` depends only on the `μ`-a.e. class of the kernel. Contrast Mathlib's
`PreErgodic`, which is phrased with *strictly* invariant sets and is therefore not manifestly
invariant under modifying the map on a null set. -/
lemma aeInvariantSets_congr {π' : Kernel Ω Ω} (h : ∀ᵐ ω ∂μ, π ω = π' ω) :
    aeInvariantSets π μ = aeInvariantSets π' μ := by
  have key : ∀ (κ₁ κ₂ : Kernel Ω Ω), (∀ᵐ ω ∂μ, κ₁ ω = κ₂ ω) →
      aeInvariantSets κ₁ μ ⊆ aeInvariantSets κ₂ μ := by
    intro κ₁ κ₂ hκ A hA
    refine ⟨hA.1, ?_⟩
    filter_upwards [hA.2, hκ] with ω h1 h2
    rw [← h2]; exact h1
  exact Set.Subset.antisymm (key _ _ h) (key _ _ (h.mono fun _ hω ↦ hω.symm))

/-- The integral of `ω ↦ π ω A` against an invariant measure is `μ A`. -/
lemma lintegral_kernel_apply_of_invariant (hπ : Invariant π μ) {A : Set Ω}
    (hA : MeasurableSet A) : ∫⁻ ω, π ω A ∂μ = μ A := by
  rw [← Measure.bind_apply hA π.aemeasurable, hπ.def]

/-- **The engine of Georgii (7.3).** For an invariant finite measure, the inequality
`1_A ≤ π(A | ·)` a.e. already forces equality: the two sides have the same integral. -/
lemma mem_aeInvariantSets_of_indicator_ae_le [IsFiniteMeasure μ] (hπ : Invariant π μ)
    {A : Set Ω} (hA : MeasurableSet A) (h : A.indicator 1 ≤ᵐ[μ] fun ω ↦ π ω A) :
    A ∈ aeInvariantSets π μ := by
  refine ⟨hA, ?_⟩
  have hfin : ∫⁻ ω, A.indicator 1 ω ∂μ ≠ ∞ := by
    rw [lintegral_indicator_one hA]; exact measure_ne_top μ A
  have hle : ∫⁻ ω, π ω A ∂μ ≤ ∫⁻ ω, A.indicator 1 ω ∂μ := by
    rw [lintegral_kernel_apply_of_invariant hπ hA, lintegral_indicator_one hA]
  exact (ae_eq_of_ae_le_of_lintegral_le h hfin (π.measurable_coe hA).aemeasurable hle).symm

/-- **Georgii (7.3), first half.** For a Markov kernel `π` and an invariant finite measure `μ`,
the `μ`-almost surely `π`-invariant sets form a σ-algebra `I_π(μ)`.

Closure under complements is the Markov property; closure under countable unions is the engine
`mem_aeInvariantSets_of_indicator_ae_le`: a union `A` of invariant sets satisfies `1_A ≤ π(A|·)`
a.e. pointwise, and invariance of `μ` upgrades that inequality to an equality. -/
@[instance_reducible]
def aeInvariantSigmaAlgebra [IsMarkovKernel π] [IsFiniteMeasure μ] (hπ : Invariant π μ) :
    MeasurableSpace Ω where
  MeasurableSet' A := A ∈ aeInvariantSets π μ
  measurableSet_empty := ⟨MeasurableSet.empty, by filter_upwards with ω; simp⟩
  measurableSet_compl := by
    rintro A ⟨hA, hae⟩
    refine ⟨hA.compl, ?_⟩
    filter_upwards [hae] with ω hω
    rw [measure_compl hA (measure_ne_top _ _), measure_univ, hω]
    by_cases h : ω ∈ A <;> simp [h]
  measurableSet_iUnion := by
    intro f hf
    refine mem_aeInvariantSets_of_indicator_ae_le hπ
      (MeasurableSet.iUnion fun n ↦ (hf n).1) ?_
    have hall : ∀ᵐ ω ∂μ, ∀ n, π ω (f n) = (f n).indicator 1 ω :=
      ae_all_iff.2 fun n ↦ (hf n).2
    filter_upwards [hall] with ω hω
    by_cases h : ω ∈ ⋃ n, f n
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      calc (⋃ n, f n).indicator (1 : Ω → ℝ≥0∞) ω = 1 := by simp [h]
        _ ≤ π ω (f n) := by rw [hω n]; simp [hn]
        _ ≤ π ω (⋃ n, f n) := measure_mono (subset_iUnion f n)
    · simp [h]

section Core

variable [IsMarkovKernel π] [IsFiniteMeasure μ]

@[simp] lemma measurableSet_aeInvariantSigmaAlgebra_iff (hπ : Invariant π μ) {A : Set Ω} :
    MeasurableSet[aeInvariantSigmaAlgebra hπ] A ↔
      MeasurableSet A ∧ ∀ᵐ ω ∂μ, π ω A = A.indicator 1 ω := Iff.rfl

lemma aeInvariantSigmaAlgebra_le (hπ : Invariant π μ) : aeInvariantSigmaAlgebra hπ ≤ m :=
  fun _ h ↦ h.1

section Density

variable {A : Set Ω}

omit [IsFiniteMeasure μ] in
lemma ae_kernel_compl_eq_zero_of_mem (hA : A ∈ aeInvariantSets π μ) :
    ∀ᵐ ω ∂μ, ω ∈ A → π ω Aᶜ = 0 := by
  filter_upwards [hA.2] with ω hω hmem
  rw [measure_compl hA.1 (measure_ne_top _ _), measure_univ, hω]
  simp [hmem]

omit [IsMarkovKernel π] [IsFiniteMeasure μ] in
lemma ae_kernel_eq_zero_of_notMem (hA : A ∈ aeInvariantSets π μ) :
    ∀ᵐ ω ∂μ, ω ∉ A → π ω A = 0 := by
  filter_upwards [hA.2] with ω hω hmem
  rw [hω]; simp [hmem]

omit [IsFiniteMeasure μ] in
/-- For an a.s. invariant `A`, the kernel mass of any `B` averaged over `A` is `μ (A ∩ B)`:
`π` neither leaves `A` nor enters it. -/
lemma setLIntegral_kernel_apply_of_mem_aeInvariantSets (hπ : Invariant π μ)
    (hA : A ∈ aeInvariantSets π μ) {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ ω in A, π ω B ∂μ = μ (A ∩ B) := by
  have hAm : MeasurableSet A := hA.1
  have hstep₁ : ∫⁻ ω in A, π ω B ∂μ = ∫⁻ ω in A, π ω (A ∩ B) ∂μ := by
    refine lintegral_congr_ae ((ae_restrict_iff' hAm).2 ?_)
    filter_upwards [ae_kernel_compl_eq_zero_of_mem hA] with ω hω hmem
    refine le_antisymm ?_ (measure_mono Set.inter_subset_right)
    calc π ω B ≤ π ω (A ∩ B) + π ω (B \ A) := by
          refine (measure_mono ?_).trans (measure_union_le _ _)
          intro x hx; by_cases h : x ∈ A
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr ⟨hx, h⟩
      _ ≤ π ω (A ∩ B) + π ω Aᶜ := by gcongr; exact fun x hx ↦ hx.2
      _ = π ω (A ∩ B) := by rw [hω hmem, add_zero]
  have hzero : ∫⁻ ω in Aᶜ, π ω (A ∩ B) ∂μ = 0 := by
    refine (lintegral_eq_zero_iff (π.measurable_coe (hAm.inter hB))).2 ?_
    refine (ae_restrict_iff' hAm.compl).2 ?_
    filter_upwards [ae_kernel_eq_zero_of_notMem hA] with ω hω hmem
    exact le_antisymm ((measure_mono Set.inter_subset_left).trans (hω hmem).le) bot_le
  have hstep₂ : ∫⁻ ω in A, π ω (A ∩ B) ∂μ = ∫⁻ ω, π ω (A ∩ B) ∂μ := by
    conv_rhs => rw [← lintegral_add_compl (fun ω ↦ π ω (A ∩ B)) hAm]
    rw [hzero, add_zero]
  rw [hstep₁, hstep₂, lintegral_kernel_apply_of_invariant hπ (hAm.inter hB)]

end Density

section WithDensity

/-- The identity behind Georgii (7.3): for `I_π(μ)`-measurable `f`, averaging `f` against the
kernel mass of `B` is the same as integrating `f` over `B`. -/
lemma lintegral_mul_kernel_apply_of_measurable (hπ : Invariant π μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeInvariantSigmaAlgebra hπ] f) {B : Set Ω} (hB : MeasurableSet B) :
    ∫⁻ ω, f ω * π ω B ∂μ = ∫⁻ ω in B, f ω ∂μ := by
  have hle : aeInvariantSigmaAlgebra hπ ≤ m := aeInvariantSigmaAlgebra_le hπ
  revert hB
  refine @Measurable.ennreal_induction Ω (aeInvariantSigmaAlgebra hπ)
    (fun f ↦ ∀ B : Set Ω, MeasurableSet B → ∫⁻ ω, f ω * π ω B ∂μ = ∫⁻ ω in B, f ω ∂μ)
    ?_ ?_ ?_ f hf B
  · -- constant multiples of indicators of a.s. invariant sets
    intro c A hA B hB
    have hAm : MeasurableSet A := hle _ hA
    have hL : ∫⁻ ω, (A.indicator (fun _ ↦ c) ω) * π ω B ∂μ = c * μ (A ∩ B) := by
      rw [show (fun ω ↦ (A.indicator (fun _ ↦ c) ω) * π ω B)
            = A.indicator (fun ω ↦ c * π ω B) from by
          funext ω; by_cases h : ω ∈ A <;> simp [h],
        lintegral_indicator hAm, lintegral_const_mul _ (π.measurable_coe hB),
        setLIntegral_kernel_apply_of_mem_aeInvariantSets hπ hA hB]
    have hR : ∫⁻ ω in B, A.indicator (fun _ ↦ c) ω ∂μ = c * μ (A ∩ B) := by
      rw [lintegral_indicator hAm, MeasureTheory.setLIntegral_const,
        Measure.restrict_apply hAm,
        Set.inter_comm, mul_comm]
    rw [hL, hR]
  · -- additivity
    intro f g _ hfm hgm hf' hg' B hB
    have hfm' : Measurable f := hfm.mono hle le_rfl
    have hgm' : Measurable g := hgm.mono hle le_rfl
    have hm1 : Measurable fun ω ↦ f ω * π ω B := hfm'.mul (π.measurable_coe hB)
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left hm1, hf' B hB, hg' B hB, lintegral_add_left hfm']
  · -- monotone limits
    intro f hfm hmono hf' B hB
    have hfm' : ∀ n, Measurable (f n) := fun n ↦ (hfm n).mono hle le_rfl
    have h1 : ∫⁻ ω, (⨆ n, f n ω) * π ω B ∂μ = ⨆ n, ∫⁻ ω, f n ω * π ω B ∂μ := by
      rw [show (fun ω ↦ (⨆ n, f n ω) * π ω B) = fun ω ↦ ⨆ n, f n ω * π ω B from by
        funext ω; rw [ENNReal.iSup_mul]]
      exact lintegral_iSup (fun n ↦ (hfm' n).mul (π.measurable_coe hB))
        (fun a b hab ω ↦ by gcongr; exact hmono hab ω)
    rw [h1, lintegral_iSup hfm' (fun a b hab ω ↦ hmono hab ω)]
    exact iSup_congr fun n ↦ hf' n B hB

omit [IsMarkovKernel π] [IsFiniteMeasure μ] in
/-- Invariance of a weighted measure `f·μ`, tested against sets. -/
lemma invariant_withDensity_iff_forall {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    Invariant π (μ.withDensity f) ↔
      ∀ B, MeasurableSet B → ∫⁻ ω, f ω * π ω B ∂μ = ∫⁻ ω in B, f ω ∂μ := by
  constructor
  · intro hν B hB
    have h := congrArg (fun m : Measure Ω ↦ m B) hν.def
    rwa [Measure.bind_apply hB π.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul μ hf (π.measurable_coe hB),
      withDensity_apply f hB] at h
  · intro h
    refine Measure.ext fun B hB ↦ ?_
    rw [Measure.bind_apply hB π.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul μ hf (π.measurable_coe hB), withDensity_apply f hB]
    exact h B hB

/-- **Georgii (7.3), second half, "if" direction.** If `f` is `I_π(μ)`-measurable then `f·μ` is
again `π`-invariant. -/
theorem invariant_withDensity_of_measurable (hπ : Invariant π μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeInvariantSigmaAlgebra hπ] f) :
    Invariant π (μ.withDensity f) :=
  (invariant_withDensity_iff_forall (hf.mono (aeInvariantSigmaAlgebra_le hπ) le_rfl)).2
    fun _ hB ↦ lintegral_mul_kernel_apply_of_measurable hπ hf hB

omit [IsMarkovKernel π] [IsFiniteMeasure μ] in
/-- A `μ`-null measurable set is a.s. invariant: invariance of `μ` forces `π(A|·)` to have
integral `μ A = 0`. -/
lemma mem_aeInvariantSets_of_measure_eq_zero (hπ : Invariant π μ) {A : Set Ω}
    (hA : MeasurableSet A) (h : μ A = 0) : A ∈ aeInvariantSets π μ := by
  refine ⟨hA, ?_⟩
  have hzero : ∀ᵐ ω ∂μ, π ω A = 0 :=
    (lintegral_eq_zero_iff (π.measurable_coe hA)).1
      (by rw [lintegral_kernel_apply_of_invariant hπ hA, h])
  have hAnull : ∀ᵐ ω ∂μ, ω ∉ A := by
    rw [ae_iff]; simpa using h
  filter_upwards [hzero, hAnull] with ω h1 h2
  rw [h1]; simp [h2]

end WithDensity

section Converse

/-- The pointwise inequality driving Georgii's step 2: for `c ≤ f` and `κ ≤ 1`, the product
`(f - c)(1 - κ)` is nonnegative, stated additively so as to avoid truncated subtraction. -/
private lemma mul_add_le_add_mul_of_le {c f κ : ℝ≥0∞} (hcf : c ≤ f) (hκ : κ ≤ 1) :
    f * κ + c ≤ f + c * κ := by
  obtain ⟨d, hd⟩ : ∃ d, κ + d = 1 := ⟨1 - κ, add_tsub_cancel_of_le hκ⟩
  have hc' : c = c * κ + c * d := by rw [← mul_add, hd, mul_one]
  have hf' : f = f * κ + f * d := by rw [← mul_add, hd, mul_one]
  calc f * κ + c = f * κ + c * κ + c * d := by
        conv_lhs => rw [hc']
        ring
    _ ≤ f * κ + c * κ + f * d := by gcongr
    _ = f + c * κ := by
        conv_rhs => rw [hf']
        ring


/-- Georgii's step 2: for `0 < c < ∞` the level set `{f ≥ c}` is a.s. invariant. -/
private lemma mem_aeInvariantSets_preimage_Ici (hπ : Invariant π μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∫⁻ ω, f ω ∂μ ≠ ∞) (hν : Invariant π (μ.withDensity f))
    {c : ℝ≥0∞} (hctop : c ≠ ∞) :
    f ⁻¹' Set.Ici c ∈ aeInvariantSets π μ := by
  set A := f ⁻¹' Set.Ici c with hAdef
  have hAm : MeasurableSet A := hf measurableSet_Ici
  have hmemA : ∀ {ω}, ω ∈ A ↔ c ≤ f ω := Iff.rfl
  set κ : Ω → ℝ≥0∞ := fun ω ↦ π ω A with hκdef
  have hκm : Measurable κ := π.measurable_coe hAm
  have hκle : ∀ ω, κ ω ≤ 1 := fun ω ↦ prob_le_one
  -- the two conservation identities
  have hI : ∫⁻ ω in A, f ω * κ ω ∂μ + ∫⁻ ω in Aᶜ, f ω * κ ω ∂μ = ∫⁻ ω in A, f ω ∂μ := by
    rw [lintegral_add_compl _ hAm]
    exact (invariant_withDensity_iff_forall hf).1 hν A hAm
  have hII : ∫⁻ ω in A, κ ω ∂μ + ∫⁻ ω in Aᶜ, κ ω ∂μ = μ A := by
    rw [lintegral_add_compl _ hAm]
    exact lintegral_kernel_apply_of_invariant hπ hAm
  -- finiteness
  have hfA : ∫⁻ ω in A, f ω ∂μ ≠ ∞ := ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
  have hYfin : ∫⁻ ω in A, f ω * κ ω ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top hfA (lintegral_mono fun ω ↦ ?_)
    calc f ω * κ ω ≤ f ω * 1 := by gcongr; exact hκle ω
      _ = f ω := mul_one _
  have hZfin : c * ∫⁻ ω in A, κ ω ∂μ ≠ ∞ := by
    refine ENNReal.mul_ne_top hctop (ne_top_of_le_ne_top (measure_ne_top μ A) ?_)
    calc ∫⁻ ω in A, κ ω ∂μ ≤ ∫⁻ _ω in A, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun ω ↦ hκle ω
      _ = μ A := by simp
  -- the pointwise inequality on `A`, integrated
  have hpt : ∫⁻ ω in A, f ω * κ ω ∂μ + c * μ A
      ≤ ∫⁻ ω in A, f ω ∂μ + c * ∫⁻ ω in A, κ ω ∂μ := by
    have hm1 : Measurable fun ω ↦ f ω * κ ω := hf.mul hκm
    have hsplit1 : ∫⁻ ω in A, (f ω * κ ω + c) ∂μ = ∫⁻ ω in A, f ω * κ ω ∂μ + c * μ A := by
      rw [lintegral_add_left hm1, MeasureTheory.setLIntegral_const]
    have hsplit2 : ∫⁻ ω in A, (f ω + c * κ ω) ∂μ
        = ∫⁻ ω in A, f ω ∂μ + c * ∫⁻ ω in A, κ ω ∂μ := by
      rw [lintegral_add_left hf, lintegral_const_mul c hκm]
    rw [← hsplit1, ← hsplit2]
    refine lintegral_mono_ae ((ae_restrict_iff' hAm).2 ?_)
    filter_upwards with ω hω
    exact mul_add_le_add_mul_of_le (hmemA.1 hω) (hκle ω)
  -- squeeze: `c * ∫_{Aᶜ} κ ≤ ∫_{Aᶜ} f κ ≤ c * ∫_{Aᶜ} κ`
  have hge : c * ∫⁻ ω in Aᶜ, κ ω ∂μ ≤ ∫⁻ ω in Aᶜ, f ω * κ ω ∂μ := by
    rw [← hII, ← hI, mul_add] at hpt
    have hstep : (∫⁻ ω in A, f ω * κ ω ∂μ + c * ∫⁻ ω in A, κ ω ∂μ)
          + c * ∫⁻ ω in Aᶜ, κ ω ∂μ
        ≤ (∫⁻ ω in A, f ω * κ ω ∂μ + c * ∫⁻ ω in A, κ ω ∂μ)
          + ∫⁻ ω in Aᶜ, f ω * κ ω ∂μ := by
      convert hpt using 1 <;> ring
    exact (ENNReal.add_le_add_iff_left (by finiteness)).1 hstep
  have hle : ∫⁻ ω in Aᶜ, f ω * κ ω ∂μ ≤ c * ∫⁻ ω in Aᶜ, κ ω ∂μ := by
    rw [← lintegral_const_mul c hκm]
    refine lintegral_mono_ae ((ae_restrict_iff' hAm.compl).2 ?_)
    filter_upwards with ω hω
    gcongr
    exact (not_le.1 (hmemA.not.1 hω)).le
  -- hence `κ = 0` off `A`, because `f < c` there
  have hκzero : ∀ᵐ ω ∂μ, ω ∉ A → κ ω = 0 := by
    have hYc : ∫⁻ ω in Aᶜ, f ω * κ ω ∂μ ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ hle
      exact ENNReal.mul_ne_top hctop
        (ne_top_of_le_ne_top (measure_ne_top μ Aᶜ)
          (le_trans (lintegral_mono fun ω ↦ hκle ω) (by simp)))
    have hae : (fun ω ↦ f ω * κ ω) =ᵐ[μ.restrict Aᶜ] fun ω ↦ c * κ ω := by
      refine ae_eq_of_ae_le_of_lintegral_le ?_ hYc (hκm.const_mul c).aemeasurable ?_
      · refine (ae_restrict_iff' hAm.compl).2 ?_
        filter_upwards with ω hω
        gcongr
        exact (not_le.1 (hmemA.not.1 hω)).le
      · rw [lintegral_const_mul c hκm]; exact hge
    have hae' := (ae_restrict_iff' hAm.compl).1 hae
    filter_upwards [hae'] with ω hω hmem
    by_contra hne
    have hlt : f ω < c := not_le.1 (hmemA.not.1 hmem)
    have hstrict : κ ω * f ω < κ ω * c :=
      ENNReal.mul_lt_mul_right hne (ne_top_of_le_ne_top ENNReal.one_ne_top (hκle ω)) hlt
    rw [mul_comm (κ ω) (f ω), mul_comm (κ ω) c] at hstrict
    exact absurd (hω hmem) (ne_of_lt hstrict)
  -- and therefore `κ = 1` on `A`
  have hW : ∫⁻ ω in Aᶜ, κ ω ∂μ = 0 := by
    refine (lintegral_eq_zero_iff hκm).2 ((ae_restrict_iff' hAm.compl).2 ?_)
    filter_upwards [hκzero] with ω hω hmem
    exact hω hmem
  have hZeq : ∫⁻ ω in A, κ ω ∂μ = μ A := by rw [← hII, hW, add_zero]
  have hone : ∀ᵐ ω ∂μ, ω ∈ A → κ ω = 1 := by
    have hZne : ∫⁻ ω in A, κ ω ∂μ ≠ ∞ := by rw [hZeq]; exact measure_ne_top μ A
    have hint : ∫⁻ _ω in A, (1 : ℝ≥0∞) ∂μ ≤ ∫⁻ ω in A, κ ω ∂μ := by
      simp only [MeasureTheory.lintegral_const, Measure.restrict_apply_univ, one_mul]
      rw [hZeq]
    have h1 : κ =ᵐ[μ.restrict A] fun _ ↦ (1 : ℝ≥0∞) :=
      ae_eq_of_ae_le_of_lintegral_le (.of_forall hκle) hZne aemeasurable_const hint
    exact (ae_restrict_iff' hAm).1 h1
  refine ⟨hAm, ?_⟩
  filter_upwards [hone, hκzero] with ω ha hb
  by_cases h : ω ∈ A
  · rw [show π ω A = κ ω from rfl, ha h]; simp [h]
  · rw [show π ω A = κ ω from rfl, hb h]; simp [h]

/-- **Georgii (7.3), second half, "only if" direction.** If `f·μ` is `π`-invariant and of finite
mass then `f` is `I_π(μ)`-measurable: every level set `{f ≥ c}` is a.s. invariant. -/
theorem measurable_of_invariant_withDensity (hπ : Invariant π μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∫⁻ ω, f ω ∂μ ≠ ∞) (hν : Invariant π (μ.withDensity f)) :
    Measurable[aeInvariantSigmaAlgebra hπ] f := by
  refine measurable_of_Ici fun c ↦ ?_
  rcases eq_or_ne c ∞ with rfl | hctop
  · refine mem_aeInvariantSets_of_measure_eq_zero hπ (hf measurableSet_Ici) ?_
    have hset : f ⁻¹' Set.Ici (∞ : ℝ≥0∞) = {ω | ¬ f ω < ∞} := by
      ext ω; simp [not_lt]
    rw [hset]
    exact ae_iff.1 (ae_lt_top hf hfin)
  · exact mem_aeInvariantSets_preimage_Ici hπ hf hfin hν hctop

/-- **Georgii (7.3), second half.** For a density `f` of finite mass, the weighted measure `f·μ`
is `π`-invariant if and only if `f` is measurable with respect to `I_π(μ)`. -/
theorem invariant_withDensity_iff_measurable (hπ : Invariant π μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∫⁻ ω, f ω ∂μ ≠ ∞) :
    Invariant π (μ.withDensity f) ↔ Measurable[aeInvariantSigmaAlgebra hπ] f :=
  ⟨measurable_of_invariant_withDensity hπ hf hfin, invariant_withDensity_of_measurable hπ⟩

end Converse


end Core

section Family

variable {ι : Type*} {κ : ι → Kernel Ω Ω} [∀ i, IsMarkovKernel (κ i)]

variable (κ) in
/-- **Georgii (7.4).** The σ-algebra `I_Π(μ)` of `μ`-almost surely `Π`-invariant sets, for a
family `Π` of Markov kernels leaving `μ` invariant. -/
@[instance_reducible]
def aeInvariantSigmaAlgebraFamily [IsFiniteMeasure μ] (hκ : ∀ i, Invariant (κ i) μ) :
    MeasurableSpace Ω := ⨅ i, aeInvariantSigmaAlgebra (hκ i)

lemma aeInvariantSigmaAlgebraFamily_le [IsFiniteMeasure μ] [Nonempty ι]
    (hκ : ∀ i, Invariant (κ i) μ) : aeInvariantSigmaAlgebraFamily κ hκ ≤ m :=
  le_trans (iInf_le _ (Classical.arbitrary ι)) (aeInvariantSigmaAlgebra_le _)

lemma measurableSet_aeInvariantSigmaAlgebraFamily_iff [IsFiniteMeasure μ]
    (hκ : ∀ i, Invariant (κ i) μ) {A : Set Ω} :
    MeasurableSet[aeInvariantSigmaAlgebraFamily κ hκ] A ↔ ∀ i, A ∈ aeInvariantSets (κ i) μ :=
  MeasurableSpace.measurableSet_iInf

lemma measurable_aeInvariantSigmaAlgebraFamily_iff [IsFiniteMeasure μ]
    (hκ : ∀ i, Invariant (κ i) μ) {X : Type*} [MeasurableSpace X] {f : Ω → X} :
    Measurable[aeInvariantSigmaAlgebraFamily κ hκ] f ↔
      ∀ i, Measurable[aeInvariantSigmaAlgebra (hκ i)] f := by
  rw [aeInvariantSigmaAlgebraFamily]
  exact measurable_iInf_iff_forall _

/-- **Georgii (7.4), the substantial half.** If `μ` is trivial on `I_Π(μ)`, every `Π`-invariant
probability measure absolutely continuous with respect to `μ` *is* `μ`. -/
theorem eq_of_absolutelyContinuous_of_trivialOn [IsProbabilityMeasure μ] [Nonempty ι]
    (hκ : ∀ i, Invariant (κ i) μ)
    (htriv : ∀ A, MeasurableSet[aeInvariantSigmaAlgebraFamily κ hκ] A → μ A = 0 ∨ μ A = 1)
    {ν : Measure Ω} [IsProbabilityMeasure ν] (hν : ∀ i, Invariant (κ i) ν) (hac : ν ≪ μ) :
    ν = μ := by
  set f := ν.rnDeriv μ with hfdef
  have hfm : Measurable f := ν.measurable_rnDeriv μ
  have hwd : μ.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν μ hac
  have hmass : ∫⁻ ω, f ω ∂μ = 1 := by
    have h := congrArg (fun m : Measure Ω ↦ m Set.univ) hwd
    simpa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
  have hfin : ∫⁻ ω, f ω ∂μ ≠ ∞ := by rw [hmass]; exact ENNReal.one_ne_top
  have hmeas : Measurable[aeInvariantSigmaAlgebraFamily κ hκ] f :=
    (measurable_aeInvariantSigmaAlgebraFamily_iff hκ).2 fun i ↦
      measurable_of_invariant_withDensity (hκ i) hfm hfin (by rw [hwd]; exact hν i)
  obtain ⟨c, hc⟩ := MeasureTheory.exists_ae_eq_const_of_forall_measure_eq_zero_or_one
    (aeInvariantSigmaAlgebraFamily_le hκ) htriv hmeas
  have hc1 : c = 1 := by
    have hcalc : ∫⁻ ω, f ω ∂μ = c := by rw [lintegral_congr_ae hc]; simp
    rw [← hcalc, hmass]
  have hf1 : f =ᵐ[μ] 1 := by rw [hc1] at hc; exact hc
  rw [← hwd, withDensity_congr_ae hf1, withDensity_one]

/-- Normalising `μ` on an a.s. `Π`-invariant set of positive measure gives a `Π`-invariant
probability measure: its density is a constant multiple of `1_A`, which is `I_Π(μ)`-measurable. -/
lemma invariant_withDensity_indicator [IsFiniteMeasure μ] (hκ : ∀ i, Invariant (κ i) μ)
    {A : Set Ω} (hA : MeasurableSet[aeInvariantSigmaAlgebraFamily κ hκ] A) (c : ℝ≥0∞) (i : ι) :
    Invariant (κ i) (μ.withDensity (A.indicator fun _ ↦ c)) :=
  invariant_withDensity_of_measurable (hκ i)
    (((measurable_const (a := c)).indicator hA).mono (iInf_le _ i) le_rfl)

/-- **Georgii (7.4).** A `Π`-invariant probability measure is extreme among the `Π`-invariant
probability measures if and only if it is trivial on the σ-algebra `I_Π(μ)` of `μ`-almost surely
`Π`-invariant sets.

Georgii's Example (7.5) shows that the *strictly* invariant sets do not suffice. -/
theorem mem_extremePoints_iff_trivialOn [IsProbabilityMeasure μ] [Nonempty ι]
    (hκ : ∀ i, Invariant (κ i) μ) :
    μ ∈ ({ν : Measure Ω | IsProbabilityMeasure ν ∧ ∀ i, Invariant (κ i) ν} :
        Set (Measure Ω)).extremePoints ℝ≥0∞ ↔
      ∀ A, MeasurableSet[aeInvariantSigmaAlgebraFamily κ hκ] A → μ A = 0 ∨ μ A = 1 := by
  constructor
  · -- extreme ⟹ trivial, by contraposition: a nontrivial invariant set splits `μ`
    intro hext A hA
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h0, h1⟩ := hcon
    have hAm : MeasurableSet A := aeInvariantSigmaAlgebraFamily_le hκ _ hA
    have hAtop : μ A ≠ ∞ := measure_ne_top μ A
    have hcompl : μ Aᶜ = 1 - μ A := by
      rw [measure_compl hAm hAtop, measure_univ]
    have hAlt : μ A < 1 := lt_of_le_of_ne prob_le_one h1
    have hc0 : μ Aᶜ ≠ 0 := by rw [hcompl]; exact (tsub_pos_iff_lt.2 hAlt).ne'
    have hcAm : MeasurableSet Aᶜ := hAm.compl
    have hcA : MeasurableSet[aeInvariantSigmaAlgebraFamily κ hκ] Aᶜ := hA.compl
    -- the two conditioned measures
    set ν₁ := μ.withDensity (A.indicator fun _ ↦ (μ A)⁻¹) with hν₁
    set ν₂ := μ.withDensity (Aᶜ.indicator fun _ ↦ (μ Aᶜ)⁻¹) with hν₂
    have hmass : ∀ (B : Set Ω), MeasurableSet B → ∀ (c : ℝ≥0∞),
        μ.withDensity (B.indicator fun _ ↦ c) Set.univ = c * μ B := by
      intro B hB c
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, lintegral_indicator hB,
        MeasureTheory.setLIntegral_const]
    have hp₁ : IsProbabilityMeasure ν₁ :=
      ⟨by rw [hν₁, hmass A hAm]; exact ENNReal.inv_mul_cancel h0 hAtop⟩
    have hp₂ : IsProbabilityMeasure ν₂ :=
      ⟨by rw [hν₂, hmass Aᶜ hcAm]; exact ENNReal.inv_mul_cancel hc0 (measure_ne_top μ Aᶜ)⟩
    -- `μ` sits strictly inside the segment from `ν₁` to `ν₂`
    have hseg : μ ∈ openSegment ℝ≥0∞ ν₁ ν₂ := by
      refine ⟨μ A, μ Aᶜ, pos_iff_ne_zero.2 h0, pos_iff_ne_zero.2 hc0, ?_, ?_⟩
      · rw [hcompl, add_tsub_cancel_of_le hAlt.le]
      · refine Measure.ext fun B hB ↦ ?_
        have hone : ∀ (C : Set Ω), MeasurableSet C → μ C ≠ 0 → μ C ≠ ∞ →
            μ C * μ.withDensity (C.indicator fun _ ↦ (μ C)⁻¹) B = μ (C ∩ B) := by
          intro C hC hC0 hCtop
          rw [withDensity_apply _ hB, lintegral_indicator hC, Measure.restrict_restrict hC,
            MeasureTheory.setLIntegral_const, ← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop,
            one_mul, Set.inter_comm]
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hone A hAm h0 hAtop, hone Aᶜ hcAm hc0 (measure_ne_top μ Aᶜ),
          ← measure_inter_add_sdiff B hAm, Set.inter_comm A B]
        congr 1
        rw [Set.inter_comm]
        rfl
    -- but `ν₁ ≠ μ`, contradicting extremality
    have hν₁ne : ν₁ ≠ μ := by
      intro h
      have : μ Aᶜ = 0 := by
        rw [← h, hν₁, withDensity_apply _ hcAm, lintegral_indicator hAm,
          Measure.restrict_restrict hAm]
        simp
      exact hc0 this
    exact hν₁ne (hext.2 ⟨hp₁, fun i ↦ invariant_withDensity_indicator hκ hA _ i⟩
      ⟨hp₂, fun i ↦ invariant_withDensity_indicator hκ hcA _ i⟩ hseg)
  · -- trivial ⟹ extreme
    intro htriv
    refine ⟨⟨‹IsProbabilityMeasure μ›, hκ⟩, ?_⟩
    intro ν₁ h₁ ν₂ h₂ hseg
    obtain ⟨a, b, ha, hb, _, hsum⟩ := hseg
    have hac : ν₁ ≪ μ := by
      intro s hs
      have hz : a * ν₁ s + b * ν₂ s = 0 := by
        have h := congrArg (fun m : Measure Ω ↦ m s) hsum
        simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul] at h
        rw [h]; exact hs
      rcases mul_eq_zero.1 (add_eq_zero.1 hz).1 with h | h
      · exact absurd h ha.ne'
      · exact h
    have := h₁.1
    exact eq_of_absolutelyContinuous_of_trivialOn hκ htriv h₁.2 hac

end Family

/-! ### Specialisation to a deterministic kernel: Mathlib's ergodicity -/

section Deterministic

variable {T : Ω → Ω}

/-- For the deterministic kernel of a map, kernel invariance is measure preservation. -/
lemma invariant_deterministic_iff (hT : Measurable T) :
    Invariant (Kernel.deterministic T hT) μ ↔ μ.map T = μ := by
  rw [Invariant, show ((Kernel.deterministic T hT : Kernel Ω Ω) : Ω → Measure Ω)
      = fun ω ↦ Measure.dirac (T ω) from funext (Kernel.deterministic_apply hT),
    Measure.bind_dirac_eq_map μ hT]

/-- The `μ`-a.s. invariant sets of a deterministic kernel are the `μ`-a.e. invariant sets of the
map. -/
lemma mem_aeInvariantSets_deterministic_iff (hT : Measurable T) {A : Set Ω} :
    A ∈ aeInvariantSets (Kernel.deterministic T hT) μ ↔
      MeasurableSet A ∧ T ⁻¹' A =ᵐ[μ] A := by
  rw [mem_aeInvariantSets]
  refine and_congr_right fun hA ↦ ?_
  have hiff : ∀ ω, (Kernel.deterministic T hT ω A = A.indicator 1 ω)
      ↔ ((ω ∈ T ⁻¹' A) = (ω ∈ A)) := by
    intro ω
    rw [Kernel.deterministic_apply' hT ω hA]
    by_cases h1 : T ω ∈ A <;> by_cases h2 : ω ∈ A <;>
      simp [h1, h2, Set.mem_preimage, eq_iff_iff]
  exact eventually_congr (.of_forall hiff)

/-- **The almost-everywhere characterisation of pre-ergodicity.** For a measure-preserving map on a
probability space, Mathlib's `PreErgodic` — a zero-one law over *strictly* invariant measurable sets
— is equivalent to the zero-one law over *null measurable, almost everywhere* invariant sets, which
is how ergodicity is normally stated.

Measurability of `T` is essential, not cosmetic: the equivalence runs through
`QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae`, which corrects an a.e. invariant set to
a strictly invariant one by iterating `T`, and that correction is unavailable for a merely a.e.
measurable map. `aeInvariantSets_congr` and `preErgodic_congr_ae` are the payoff: the right-hand
side, unlike the definition, manifestly depends only on the a.e. class. -/
theorem preErgodic_iff_forall_nullMeasurableSet [IsProbabilityMeasure μ]
    (hmp : MeasurePreserving T μ μ) :
    PreErgodic T μ ↔
      ∀ s, NullMeasurableSet s μ → T ⁻¹' s =ᵐ[μ] s → μ s = 0 ∨ μ s = 1 := by
  constructor
  · intro herg s hs hae
    obtain ⟨t, htm, hteq, hinv⟩ :=
      hmp.quasiMeasurePreserving.exists_preimage_eq_of_preimage_ae hs hae
    rcases eventuallyConst_set'.1 (herg.aeconst_set htm hinv) with h | h
    · exact Or.inl (by rw [← measure_congr hteq]; exact ae_eq_empty.1 h)
    · exact Or.inr (by
        rw [← measure_congr hteq]; exact (prob_compl_eq_zero_iff htm).1 (ae_eq_univ.1 h))
  · intro htriv
    refine ⟨fun s hsm hinv ↦ ?_⟩
    rw [eventuallyConst_set']
    rcases htriv s hsm.nullMeasurableSet (by rw [hinv]; exact EventuallyEq.rfl) with h | h
    · exact Or.inl (ae_eq_empty.2 h)
    · exact Or.inr (ae_eq_univ.2 ((prob_compl_eq_zero_iff hsm).2 h))

/-- Pre-ergodicity of a measure-preserving map depends only on its `μ`-a.e. class. This is not
apparent from the definition, which quantifies over strictly invariant sets. -/
theorem preErgodic_congr_ae [IsProbabilityMeasure μ] {T' : Ω → Ω}
    (hmp : MeasurePreserving T μ μ) (hmp' : MeasurePreserving T' μ μ) (h : T =ᵐ[μ] T') :
    PreErgodic T μ ↔ PreErgodic T' μ := by
  have hpre : ∀ s : Set Ω, T ⁻¹' s =ᵐ[μ] T' ⁻¹' s := fun s ↦ by
    filter_upwards [h] with ω hω
    change (T ω ∈ s) = (T' ω ∈ s)
    rw [hω]
  rw [preErgodic_iff_forall_nullMeasurableSet hmp, preErgodic_iff_forall_nullMeasurableSet hmp']
  constructor
  · exact fun H s hs hae ↦ H s hs ((hpre s).trans hae)
  · exact fun H s hs hae ↦ H s hs ((hpre s).symm.trans hae)

/-- **Mathlib's `Ergodic.iff_mem_extremePoints` is the deterministic case of (7.4).** For a
measure-preserving self-map `T`, pre-ergodicity is triviality on `I_π(μ)` for the deterministic
kernel `π = δ_{T(·)}`. Georgii's Example (7.5) shows that for a general kernel no such reduction to
strictly invariant sets is available, so the a.s. invariant σ-algebra is the right primitive. -/
theorem preErgodic_iff_trivialOn_aeInvariant [IsProbabilityMeasure μ] (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) :
    PreErgodic T μ ↔
      ∀ A, MeasurableSet[aeInvariantSigmaAlgebra
        ((invariant_deterministic_iff (μ := μ) hT).2 hmp.map_eq)] A → μ A = 0 ∨ μ A = 1 := by
  rw [preErgodic_iff_forall_nullMeasurableSet hmp]
  constructor
  · intro h A hA
    obtain ⟨hAm, hae⟩ := (mem_aeInvariantSets_deterministic_iff hT).1 hA
    exact h A hAm.nullMeasurableSet hae
  · intro h s hs hae
    obtain ⟨t, htm, hteq⟩ := hs
    -- `NullMeasurableSet` gives `hteq : s =ᵐ[μ] t`
    have htinv : T ⁻¹' t =ᵐ[μ] t :=
      ((hmp.quasiMeasurePreserving.preimage_ae_eq hteq).symm.trans hae).trans hteq
    have hA : MeasurableSet[aeInvariantSigmaAlgebra
        ((invariant_deterministic_iff (μ := μ) hT).2 hmp.map_eq)] t :=
      (mem_aeInvariantSets_deterministic_iff hT).2 ⟨htm, htinv⟩
    rw [measure_congr hteq]
    exact h t hA

/-- A function measurable for the a.s. invariant σ-algebra of the deterministic kernel of `T` is
`μ`-a.e. `T`-invariant: countably many rational super-level sets, each a.s. invariant, pin
`f (T ω)` to `f ω`. -/
lemma ae_comp_eq_of_measurable_aeInvariantSigmaAlgebra [IsFiniteMeasure μ] (hT : Measurable T)
    (hinv : Invariant (Kernel.deterministic T hT) μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeInvariantSigmaAlgebra hinv] f) :
    (fun ω ↦ f (T ω)) =ᵐ[μ] f := by
  have hlev : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      ((Real.toNNReal q : ℝ≥0∞) ≤ f (T ω) ↔ (Real.toNNReal q : ℝ≥0∞) ≤ f ω) := by
    intro q
    have h := ((mem_aeInvariantSets_deterministic_iff hT).1
      (hf (measurableSet_Ici (a := (Real.toNNReal q : ℝ≥0∞))))).2
    exact Filter.eventuallyEq_set.1 h
  have hall : ∀ᵐ ω ∂μ, ∀ q : ℚ,
      ((Real.toNNReal q : ℝ≥0∞) ≤ f (T ω) ↔ (Real.toNNReal q : ℝ≥0∞) ≤ f ω) :=
    ae_all_iff.2 hlev
  filter_upwards [hall] with ω hω
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    exact absurd ((hω q).2 hq2.le) (not_le.2 hq1)
  · obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    exact absurd ((hω q).1 hq2.le) (not_le.2 hq1)

end Deterministic

/-! ### Specialisation to a group action: ergodicity as extremality -/

section SMul

variable {G : Type*} [Group G] [MulAction G Ω] [MeasurableConstSMul G Ω]

variable (G) in
/-- The deterministic kernel of the action of `g`; Georgii's `θ̂_i` of (14.4). -/
noncomputable def smulKernel (g : G) : Kernel Ω Ω :=
  Kernel.deterministic (fun ω : Ω ↦ g • ω) (measurable_const_smul g)

instance isMarkovKernel_smulKernel (g : G) :
    IsMarkovKernel (smulKernel G g : Kernel Ω Ω) := by
  unfold smulKernel; infer_instance

/-- `SMulInvariantMeasure` is exactly invariance under every `smulKernel`. -/
lemma smulInvariantMeasure_iff_forall_invariant {ν : Measure Ω} :
    SMulInvariantMeasure G Ω ν ↔ ∀ g : G, Invariant (smulKernel G g) ν := by
  simp only [smulKernel, invariant_deterministic_iff]
  constructor
  · intro h g
    refine Measure.ext fun s hs ↦ ?_
    rw [Measure.map_apply (measurable_const_smul g) hs]
    exact h.measure_preimage_smul g hs
  · intro h
    refine ⟨fun g s hs ↦ ?_⟩
    have hg := congrArg (fun m : Measure Ω ↦ m s) (h g)
    rwa [Measure.map_apply (measurable_const_smul g) hs] at hg

/-- The `μ`-a.s. invariant σ-algebra of the family `smulKernel` is Georgii's `𝓘(μ)` of (14.3): the
sets whose preimage under every `g • ·` agrees with them almost everywhere. -/
lemma measurableSet_aeInvariantSigmaAlgebraFamily_smul [IsFiniteMeasure μ]
    (hμ : ∀ g : G, Invariant (smulKernel G g) μ) {A : Set Ω} :
    MeasurableSet[aeInvariantSigmaAlgebraFamily (smulKernel G) hμ] A ↔
      MeasurableSet A ∧ ∀ g : G, (fun ω : Ω ↦ g • ω) ⁻¹' A =ᵐ[μ] A := by
  rw [measurableSet_aeInvariantSigmaAlgebraFamily_iff]
  constructor
  · intro h
    refine ⟨((mem_aeInvariantSets_deterministic_iff
      (measurable_const_smul (1 : G))).1 (h 1)).1, fun g ↦ ?_⟩
    exact ((mem_aeInvariantSets_deterministic_iff (measurable_const_smul g)).1 (h g)).2
  · rintro ⟨hA, hae⟩ g
    exact (mem_aeInvariantSets_deterministic_iff (measurable_const_smul g)).2 ⟨hA, hae g⟩

/-- **Georgii (14.5)(a).** An invariant probability measure is ergodic — trivial on the σ-algebra
`𝓘(μ)` of almost surely invariant events — if and only if it is an extreme point of the convex set
of invariant probability measures.

Mathlib has `Ergodic.iff_mem_extremePoints` for a single map; this is the statement for a group
action, which is what Chapter 14 needs, and Mathlib does not have it. Note that Mathlib's
`ErgodicSMul` is already phrased with almost sure invariance, unlike `PreErgodic`. -/
theorem ergodicSMul_iff_mem_extremePoints [IsProbabilityMeasure μ]
    (hμ : SMulInvariantMeasure G Ω μ) :
    ErgodicSMul G Ω μ ↔
      μ ∈ ({ν : Measure Ω | IsProbabilityMeasure ν ∧ SMulInvariantMeasure G Ω ν} :
        Set (Measure Ω)).extremePoints ℝ≥0∞ := by
  have hinv : ∀ g : G, Invariant (smulKernel G g) μ :=
    smulInvariantMeasure_iff_forall_invariant.1 hμ
  have hset : {ν : Measure Ω | IsProbabilityMeasure ν ∧ SMulInvariantMeasure G Ω ν}
      = {ν : Measure Ω | IsProbabilityMeasure ν ∧ ∀ g : G, Invariant (smulKernel G g) ν} := by
    ext ν; simp [smulInvariantMeasure_iff_forall_invariant]
  rw [hset, mem_extremePoints_iff_trivialOn hinv]
  constructor
  · intro herg A hA
    obtain ⟨hAm, hae⟩ := (measurableSet_aeInvariantSigmaAlgebraFamily_smul hinv).1 hA
    rcases eventuallyConst_set'.1
      (ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hAm hae) with h | h
    · exact Or.inl (ae_eq_empty.1 h)
    · exact Or.inr ((prob_compl_eq_zero_iff hAm).1 (ae_eq_univ.1 h))
  · intro htriv
    refine ⟨fun {s} hsm hae ↦ ?_⟩
    have hA : MeasurableSet[aeInvariantSigmaAlgebraFamily (smulKernel G) hinv] s :=
      (measurableSet_aeInvariantSigmaAlgebraFamily_smul hinv).2 ⟨hsm, hae⟩
    rw [eventuallyConst_set']
    rcases htriv s hA with h | h
    · exact Or.inl (ae_eq_empty.2 h)
    · exact Or.inr (ae_eq_univ.2 ((prob_compl_eq_zero_iff hsm).2 h))

/-- Strictly invariant sets are almost surely invariant: `𝓘 ≤ I_Π(μ)`. -/
lemma invariants_le_aeInvariantSigmaAlgebraFamily [IsFiniteMeasure μ]
    (hμ : ∀ g : G, Invariant (smulKernel G g) μ) :
    MeasurableSpace.smulInvariants G Ω ≤ aeInvariantSigmaAlgebraFamily (smulKernel G) hμ :=
  fun A hA ↦ (measurableSet_aeInvariantSigmaAlgebraFamily_smul hμ).2
    ⟨hA.1, fun g ↦ by rw [hA.2 g]; exact Filter.EventuallyEq.rfl⟩

/-- A function measurable for the a.s. invariant σ-algebra `I_Π(μ)` of a group action is a.e.
invariant under every group element. -/
lemma ae_comp_smul_eq_of_measurable [IsFiniteMeasure μ]
    (hμ : ∀ g : G, Invariant (smulKernel G g) μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeInvariantSigmaAlgebraFamily (smulKernel G) hμ] f) (g : G) :
    (fun ω ↦ f (g • ω)) =ᵐ[μ] f := by
  have hg : Invariant (Kernel.deterministic (fun ω : Ω ↦ g • ω) (measurable_const_smul g)) μ :=
    hμ g
  exact ae_comp_eq_of_measurable_aeInvariantSigmaAlgebra (measurable_const_smul g) hg
    ((measurable_aeInvariantSigmaAlgebraFamily_iff hμ).1 hf g)

/-- **Georgii (14.3)(2), function form.** Over a countable group, a function measurable for the
a.s. invariant σ-algebra `I_Π(μ)` agrees `μ`-a.e. with a *strictly* invariant function — its
orbit-wise supremum. -/
lemma exists_measurable_invariants_ae_eq [Countable G] [IsFiniteMeasure μ]
    (hμ : ∀ g : G, Invariant (smulKernel G g) μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[aeInvariantSigmaAlgebraFamily (smulKernel G) hμ] f) :
    ∃ g : Ω → ℝ≥0∞, Measurable[MeasurableSpace.smulInvariants G Ω] g ∧ f =ᵐ[μ] g := by
  have hne : Nonempty G := ⟨1⟩
  have hfm : Measurable f := hf.mono (aeInvariantSigmaAlgebraFamily_le hμ) le_rfl
  refine ⟨fun ω ↦ ⨆ i : G, f (i • ω), ?_, ?_⟩
  · refine MeasurableSpace.measurable_invariants_of_forall_smul_eq
      (Measurable.iSup fun i ↦ hfm.comp (measurable_const_smul i)) fun c ω ↦ ?_
    have h := Equiv.iSup_comp (g := fun i : G ↦ f (i • ω)) (e := Equiv.mulRight c)
    simpa only [Equiv.coe_mulRight, mul_smul] using h
  · have hall : ∀ᵐ ω ∂μ, ∀ i : G, f (i • ω) = f ω :=
      ae_all_iff.2 fun i ↦ ae_comp_smul_eq_of_measurable hμ hf i
    filter_upwards [hall] with ω hω
    simp only [hω]
    exact iSup_const.symm

/-- **Georgii (14.3)(2).** Over a countable group, every measurable set that is a.e. invariant
under each group element agrees `μ`-a.e. with a strictly invariant set: the a.s. invariant
σ-algebra `𝓘(μ)` is the `μ`-completion of `𝓘`. The strictly invariant companion is the orbit
`⋃ g, (g • ·) ⁻¹' A` of `A`. -/
lemma exists_measurableSet_invariants_ae_eq [Countable G] {A : Set Ω} (hA : MeasurableSet A)
    (hae : ∀ g : G, (g • ·) ⁻¹' A =ᵐ[μ] A) :
    ∃ B, MeasurableSet[MeasurableSpace.smulInvariants G Ω] B ∧ μ (A ∆ B) = 0 := by
  refine ⟨⋃ g : G, (g • ·) ⁻¹' A,
    ⟨MeasurableSet.iUnion fun g ↦ measurable_const_smul g hA, fun c ↦ ?_⟩, ?_⟩
  · rw [Set.preimage_iUnion]
    have hcomp : ∀ g : G, (c • ·) ⁻¹' ((g • ·) ⁻¹' A) = ((g * c) • ·) ⁻¹' A := fun g ↦ by
      ext ω; simp [mul_smul]
    calc ⋃ g : G, (c • ·) ⁻¹' ((g • ·) ⁻¹' A)
        = ⋃ g : G, ((g * c) • ·) ⁻¹' A := Set.iUnion_congr hcomp
      _ = ⋃ g : G, (g • ·) ⁻¹' A := by
          rw [← Set.iSup_eq_iUnion, ← Set.iSup_eq_iUnion]
          have h := Equiv.iSup_comp (g := fun g : G ↦ (g • ·) ⁻¹' A) (e := Equiv.mulRight c)
          simpa only [Equiv.coe_mulRight] using h
  · have hsub : A ⊆ ⋃ g : G, (g • ·) ⁻¹' A := fun ω hω ↦
      Set.mem_iUnion.2 ⟨1, by simpa using hω⟩
    rw [symmDiff_of_le hsub]
    refine measure_mono_null ?_ (measure_iUnion_null fun g ↦
      measure_mono_null (fun ω hω ↦ mem_symmDiff.2 (Or.inl hω))
        (measure_symmDiff_eq_zero_iff.2 (hae g)))
    rintro ω ⟨hmem, hnot⟩
    obtain ⟨g, hg⟩ := Set.mem_iUnion.1 hmem
    exact Set.mem_iUnion.2 ⟨g, hg, hnot⟩

/-- Triviality on the strictly invariant σ-algebra extends to every a.e. invariant set, over a
countable group. -/
lemma measure_eq_zero_or_one_of_forall_preimage_smul_ae_eq [Countable G]
    (htriv : ∀ B, MeasurableSet[MeasurableSpace.smulInvariants G Ω] B → μ B = 0 ∨ μ B = 1)
    {A : Set Ω} (hA : MeasurableSet A) (hae : ∀ g : G, (g • ·) ⁻¹' A =ᵐ[μ] A) :
    μ A = 0 ∨ μ A = 1 := by
  obtain ⟨B, hB, hAB⟩ := exists_measurableSet_invariants_ae_eq hA hae
  rw [measure_congr (measure_symmDiff_eq_zero_iff.1 hAB)]
  exact htriv B hB

/-- **Georgii (14.6) at the level of a countable group action.** Ergodicity in Mathlib's
almost-sure sense is triviality on the *strictly* invariant σ-algebra `𝓘`. The countability of
the group is what allows the a.e. invariant sets to be corrected to strictly invariant ones
(Remark (14.3)(2)). -/
theorem ergodicSMul_iff_forall_measurableSet_invariants [Countable G] [IsProbabilityMeasure μ]
    (hμ : SMulInvariantMeasure G Ω μ) :
    ErgodicSMul G Ω μ ↔
      ∀ A, MeasurableSet[MeasurableSpace.smulInvariants G Ω] A → μ A = 0 ∨ μ A = 1 := by
  constructor
  · intro herg A hA
    have hae : ∀ g : G, (g • ·) ⁻¹' A =ᵐ[μ] A := fun g ↦ by
      rw [hA.2 g]; exact Filter.EventuallyEq.rfl
    rcases eventuallyConst_set'.1
      (ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hA.1 hae) with h | h
    · exact Or.inl (ae_eq_empty.1 h)
    · exact Or.inr ((prob_compl_eq_zero_iff hA.1).1 (ae_eq_univ.1 h))
  · intro htriv
    refine ⟨fun {s} hsm hae ↦ ?_⟩
    rw [eventuallyConst_set']
    rcases measure_eq_zero_or_one_of_forall_preimage_smul_ae_eq htriv hsm hae with h | h
    · exact Or.inl (ae_eq_empty.2 h)
    · exact Or.inr (ae_eq_univ.2 ((prob_compl_eq_zero_iff hsm).2 h))

/-- **Georgii (14.5)(a), strict form.** For a countable group, an invariant probability measure
is extreme among the invariant probability measures iff it is trivial on the strictly invariant
σ-algebra `𝓘` — Georgii's own phrasing of (14.5)(a). -/
theorem mem_extremePoints_iff_forall_measurableSet_invariants [Countable G]
    [IsProbabilityMeasure μ] (hμ : SMulInvariantMeasure G Ω μ) :
    μ ∈ ({ν : Measure Ω | IsProbabilityMeasure ν ∧ SMulInvariantMeasure G Ω ν} :
        Set (Measure Ω)).extremePoints ℝ≥0∞ ↔
      ∀ A, MeasurableSet[MeasurableSpace.smulInvariants G Ω] A → μ A = 0 ∨ μ A = 1 :=
  (ergodicSMul_iff_mem_extremePoints hμ).symm.trans
    (ergodicSMul_iff_forall_measurableSet_invariants hμ)

/-- If the density is measurable for the strictly invariant σ-algebra, the weighted measure is
again invariant. This is the direction of Georgii (14.5)(b) that needs no countability. -/
theorem smulInvariantMeasure_withDensity_of_measurable_invariants [IsFiniteMeasure μ]
    (hμ : SMulInvariantMeasure G Ω μ) {f : Ω → ℝ≥0∞}
    (hf : Measurable[MeasurableSpace.smulInvariants G Ω] f) :
    SMulInvariantMeasure G Ω (μ.withDensity f) := by
  have hinv : ∀ g : G, Invariant (smulKernel G g) μ :=
    smulInvariantMeasure_iff_forall_invariant.1 hμ
  refine smulInvariantMeasure_iff_forall_invariant.2 fun g ↦ ?_
  exact invariant_withDensity_of_measurable (hinv g)
    (hf.mono ((invariants_le_aeInvariantSigmaAlgebraFamily hinv).trans (iInf_le _ g)) le_rfl)

/-- **Georgii (14.5)(b), density form.** For an invariant finite measure `μ` and a density `f` of
finite mass, `f·μ` is invariant iff `f` agrees `μ`-a.e. with a function measurable for the
strictly invariant σ-algebra `𝓘`. -/
theorem smulInvariantMeasure_withDensity_iff [Countable G] [IsFiniteMeasure μ]
    (hμ : SMulInvariantMeasure G Ω μ) {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ ω, f ω ∂μ ≠ ∞) :
    SMulInvariantMeasure G Ω (μ.withDensity f) ↔
      ∃ g, Measurable[MeasurableSpace.smulInvariants G Ω] g ∧ f =ᵐ[μ] g := by
  have hinv : ∀ g : G, Invariant (smulKernel G g) μ :=
    smulInvariantMeasure_iff_forall_invariant.1 hμ
  constructor
  · intro hν
    have hinvν : ∀ g : G, Invariant (smulKernel G g) (μ.withDensity f) :=
      smulInvariantMeasure_iff_forall_invariant.1 hν
    exact exists_measurable_invariants_ae_eq hinv
      ((measurable_aeInvariantSigmaAlgebraFamily_iff hinv).2 fun g ↦
        measurable_of_invariant_withDensity (hinv g) hf hfin (hinvν g))
  · rintro ⟨g, hg, hfg⟩
    rw [withDensity_congr_ae hfg]
    exact smulInvariantMeasure_withDensity_of_measurable_invariants hμ hg

/-- **Georgii, Theorem (14.5)(b).** For an invariant probability measure `μ` and a probability
measure `ν ≪ μ`, `ν` is invariant iff `ν = f·μ` for a density `f` measurable for the strictly
invariant σ-algebra `𝓘`. -/
theorem smulInvariantMeasure_iff_exists_withDensity [Countable G] [IsProbabilityMeasure μ]
    (hμ : SMulInvariantMeasure G Ω μ) {ν : Measure Ω} [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    SMulInvariantMeasure G Ω ν ↔
      ∃ f, Measurable[MeasurableSpace.smulInvariants G Ω] f ∧ ν = μ.withDensity f := by
  constructor
  · intro hν
    set f := ν.rnDeriv μ with hfdef
    have hfm : Measurable f := ν.measurable_rnDeriv μ
    have hwd : μ.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
    have hmass : ∫⁻ ω, f ω ∂μ = 1 := by
      have h := congrArg (fun m : Measure Ω ↦ m Set.univ) hwd
      simpa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using h
    have hfin : ∫⁻ ω, f ω ∂μ ≠ ∞ := by rw [hmass]; exact ENNReal.one_ne_top
    have hν' : SMulInvariantMeasure G Ω (μ.withDensity f) := hwd ▸ hν
    obtain ⟨g, hg, hfg⟩ := (smulInvariantMeasure_withDensity_iff hμ hfm hfin).1 hν'
    exact ⟨g, hg, by rw [← hwd, withDensity_congr_ae hfg]⟩
  · rintro ⟨f, hfI, rfl⟩
    exact smulInvariantMeasure_withDensity_of_measurable_invariants hμ hfI

/-- **Georgii, Theorem (14.5)(c).** An invariant probability measure of a countable group action
is determined, among invariant probability measures, by its restriction to the strictly
invariant σ-algebra `𝓘`. -/
theorem eq_of_forall_measurableSet_invariants_eq [Countable G] {μ ν : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : SMulInvariantMeasure G Ω μ) (hν : SMulInvariantMeasure G Ω ν)
    (h : ∀ A, MeasurableSet[MeasurableSpace.smulInvariants G Ω] A → μ A = ν A) : μ = ν := by
  set ρ : Measure Ω := (2⁻¹ : ℝ≥0∞) • μ + (2⁻¹ : ℝ≥0∞) • ν with hρdef
  have hρp : IsProbabilityMeasure ρ := ⟨by
    simp only [hρdef, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.inv_two_add_inv_two⟩
  have hρinv : SMulInvariantMeasure G Ω ρ := ⟨fun c s hs ↦ by
    simp only [hρdef, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hμ.measure_preimage_smul c hs, hν.measure_preimage_smul c hs]⟩
  have hhalf : (2⁻¹ : ℝ≥0∞) ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top
  have hμρ : μ ≪ ρ := Measure.AbsolutelyContinuous.mk fun s _hs h0 ↦ by
    simp only [hρdef, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h0
    exact (mul_eq_zero.1 (add_eq_zero.1 h0).1).resolve_left hhalf
  have hνρ : ν ≪ ρ := Measure.AbsolutelyContinuous.mk fun s _hs h0 ↦ by
    simp only [hρdef, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at h0
    exact (mul_eq_zero.1 (add_eq_zero.1 h0).2).resolve_left hhalf
  obtain ⟨f, hfI, hμf⟩ := (smulInvariantMeasure_iff_exists_withDensity hρinv hμρ).1 hμ
  obtain ⟨g, hgI, hνg⟩ := (smulInvariantMeasure_iff_exists_withDensity hρinv hνρ).1 hν
  have hm : MeasurableSpace.smulInvariants G Ω ≤ m := MeasurableSpace.smulInvariants_le
  have htrim : μ.trim hm = ν.trim hm :=
    @Measure.ext _ (MeasurableSpace.smulInvariants G Ω) _ _ fun A hA ↦ by
      rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA]
      exact h A hA
  have h1 : (ρ.trim hm).withDensity f = (ρ.trim hm).withDensity g := by
    rw [← trim_withDensity hm hfI, ← trim_withDensity hm hgI, ← hμf, ← hνg]
    exact htrim
  have hfg : f =ᵐ[ρ] g :=
    ae_of_ae_trim hm
      ((withDensity_eq_iff_of_sigmaFinite hfI.aemeasurable hgI.aemeasurable).1 h1)
  rw [hμf, hνg]
  exact withDensity_congr_ae hfg

/-- **Georgii, Theorem (14.5)(d).** Distinct extreme invariant probability measures of a
countable group action are mutually singular *on the strictly invariant σ-algebra* `𝓘`: some
strictly invariant `A` has `μ A = 1` and `ν A = 0`. -/
theorem exists_measurableSet_invariants_eq_one_eq_zero [Countable G] {μ ν : Measure Ω}
    (hμ : μ ∈ ({ρ : Measure Ω | IsProbabilityMeasure ρ ∧ SMulInvariantMeasure G Ω ρ} :
      Set (Measure Ω)).extremePoints ℝ≥0∞)
    (hν : ν ∈ ({ρ : Measure Ω | IsProbabilityMeasure ρ ∧ SMulInvariantMeasure G Ω ρ} :
      Set (Measure Ω)).extremePoints ℝ≥0∞)
    (hne : μ ≠ ν) :
    ∃ A, MeasurableSet[MeasurableSpace.smulInvariants G Ω] A ∧ μ A = 1 ∧ ν A = 0 := by
  have hμm := hμ.1
  have hνm := hν.1
  have hμp : IsProbabilityMeasure μ := hμm.1
  have hνp : IsProbabilityMeasure ν := hνm.1
  have htrivμ := (mem_extremePoints_iff_forall_measurableSet_invariants hμm.2).1 hμ
  have htrivν := (mem_extremePoints_iff_forall_measurableSet_invariants hνm.2).1 hν
  obtain ⟨A, hA, hAne⟩ : ∃ A, MeasurableSet[MeasurableSpace.smulInvariants G Ω] A ∧ μ A ≠ ν A := by
    by_contra hall
    push Not at hall
    exact hne (eq_of_forall_measurableSet_invariants_eq hμm.2 hνm.2 hall)
  have hAm : MeasurableSet A := MeasurableSpace.smulInvariants_le _ hA
  rcases htrivμ A hA with hμ0 | hμ1 <;> rcases htrivν A hA with hν0 | hν1
  · exact absurd (hμ0.trans hν0.symm) hAne
  · exact ⟨Aᶜ, hA.compl, (prob_compl_eq_one_iff hAm).2 hμ0, (prob_compl_eq_zero_iff hAm).2 hν1⟩
  · exact ⟨A, hA, hμ1, hν0⟩
  · exact absurd (hμ1.trans hν1.symm) hAne

/-- **Georgii, Theorem (14.5)(d)**, measure form: distinct extreme invariant probability measures
are mutually singular. -/
theorem mutuallySingular_of_mem_extremePoints_smulInvariant [Countable G] {μ ν : Measure Ω}
    (hμ : μ ∈ ({ρ : Measure Ω | IsProbabilityMeasure ρ ∧ SMulInvariantMeasure G Ω ρ} :
      Set (Measure Ω)).extremePoints ℝ≥0∞)
    (hν : ν ∈ ({ρ : Measure Ω | IsProbabilityMeasure ρ ∧ SMulInvariantMeasure G Ω ρ} :
      Set (Measure Ω)).extremePoints ℝ≥0∞)
    (hne : μ ≠ ν) : μ.MutuallySingular ν := by
  obtain ⟨A, hA, hμA, hνA⟩ := exists_measurableSet_invariants_eq_one_eq_zero hμ hν hne
  have hμp : IsProbabilityMeasure μ := hμ.1.1
  have hAm : MeasurableSet A := MeasurableSpace.smulInvariants_le _ hA
  exact ⟨Aᶜ, hAm.compl, (prob_compl_eq_zero_iff hAm).2 hμA, by rwa [compl_compl]⟩


end SMul

/-! ### A Markov kernel with two absorbing states: a.s. invariance is not strict invariance -/

/-! `TwoAbsorbingStates.ker` is the Markov kernel on `Fin 3` whose states `0` and `2` are absorbing
and whose state `1` jumps to each of them with probability `1/2`. Its strictly invariant sets are
only `∅` and `univ`, yet its invariant probability measures form the whole segment from `δ₀` to
`δ₂`; so triviality on the *strictly* invariant σ-algebra does not characterise extremality, and
the almost surely invariant σ-algebra `aeInvariantSets` is the right object. (Georgii, Example
(7.5).) -/

namespace TwoAbsorbingStates

open Measure

/-- Georgii's Example (7.5): the stochastic matrix on three points in which `0` and `2` are
absorbing and `1` jumps to each of them with probability `1/2`. -/
noncomputable def ker : Kernel (Fin 3) (Fin 3) :=
  Kernel.ofFunOfCountable fun i ↦
    if i = 1 then (2⁻¹ : ℝ≥0∞) • dirac 0 + (2⁻¹ : ℝ≥0∞) • dirac 2 else dirac i

lemma ker_apply (i : Fin 3) :
    ker i = if i = 1 then (2⁻¹ : ℝ≥0∞) • dirac 0 + (2⁻¹ : ℝ≥0∞) • dirac 2 else dirac i := rfl

lemma ker_zero : ker 0 = dirac 0 := by rw [ker_apply, ite_eq_right (by decide)]
lemma ker_two : ker 2 = dirac 2 := by rw [ker_apply, ite_eq_right (by decide)]
lemma ker_one : ker 1 = (2⁻¹ : ℝ≥0∞) • dirac 0 + (2⁻¹ : ℝ≥0∞) • dirac 2 := by
  rw [ker_apply, ite_eq_left rfl]

instance : IsMarkovKernel ker := by
  refine ⟨fun i ↦ ⟨?_⟩⟩
  fin_cases i
  · simp [ker_zero]
  · simp [ker_one, ENNReal.inv_two_add_inv_two]
  · simp [ker_two]

/-- The invariant measure `μ = ½δ₀ + ½δ₂` of Example (7.5). -/
noncomputable def mu : Measure (Fin 3) := (2⁻¹ : ℝ≥0∞) • dirac 0 + (2⁻¹ : ℝ≥0∞) • dirac 2

instance : IsProbabilityMeasure mu := ⟨by simp [mu, ENNReal.inv_two_add_inv_two]⟩

lemma invariant_mu : Kernel.Invariant ker mu := by
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.bind_apply hB ker.aemeasurable]
  simp [mu, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, ker_zero, ker_two]

lemma invariant_dirac_zero : Kernel.Invariant ker (dirac 0) := by
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.bind_apply hB ker.aemeasurable, lintegral_dirac, ker_zero]

lemma invariant_dirac_two : Kernel.Invariant ker (dirac 2) := by
  refine Measure.ext fun B hB ↦ ?_
  rw [Measure.bind_apply hB ker.aemeasurable, lintegral_dirac, ker_two]

/-- Every **strictly** `ker`-invariant set is trivial: the middle state forces
`½·1_A(0) + ½·1_A(2) = 1_A(1)`, whose only solutions with values in `{0,1}` are constant. -/
lemma eq_empty_or_univ_of_strictly_invariant {A : Set (Fin 3)}
    (h : ∀ i, ker i A = A.indicator 1 i) : A = ∅ ∨ A = Set.univ := by
  classical
  have key : (2⁻¹ : ℝ≥0∞) * A.indicator 1 0 + 2⁻¹ * A.indicator 1 2 = A.indicator 1 1 := by
    have h1 := h 1
    rw [ker_one] at h1
    simpa [Measure.dirac_apply] using h1
  by_cases h0 : (0 : Fin 3) ∈ A <;> by_cases hm : (1 : Fin 3) ∈ A <;>
      by_cases h2 : (2 : Fin 3) ∈ A <;>
    simp [h0, hm, h2, ENNReal.inv_two_add_inv_two] at key
  · exact Or.inr (by ext x; fin_cases x <;> simp [h0, hm, h2])
  · exact Or.inl (by ext x; fin_cases x <;> simp [h0, hm, h2])

/-- **Georgii (7.5).** `μ` is trivial on the σ-algebra of *strictly* `ker`-invariant sets. -/
theorem trivial_on_strictly_invariant (A : Set (Fin 3)) (h : ∀ i, ker i A = A.indicator 1 i) :
    mu A = 0 ∨ mu A = 1 := by
  rcases eq_empty_or_univ_of_strictly_invariant h with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

/-- **Georgii (7.5).** Nevertheless `μ` is *not* extreme: it is the midpoint of `δ₀` and `δ₂`,
both invariant. So Corollary (7.4) genuinely needs the *almost surely* invariant σ-algebra
`I_π(μ)`; the strictly invariant sets do not suffice. -/
theorem not_mem_extremePoints :
    mu ∉ ({ν : Measure (Fin 3) | IsProbabilityMeasure ν ∧ Kernel.Invariant ker ν} :
      Set (Measure (Fin 3))).extremePoints ℝ≥0∞ := by
  intro hext
  have hseg : mu ∈ openSegment ℝ≥0∞ (dirac (0 : Fin 3)) (dirac (2 : Fin 3)) :=
    ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, ENNReal.inv_two_add_inv_two, rfl⟩
  have hd0 : dirac (0 : Fin 3) = mu :=
    hext.2 ⟨inferInstance, invariant_dirac_zero⟩ ⟨inferInstance, invariant_dirac_two⟩ hseg
  have hone : (1 : ℝ≥0∞) = 2⁻¹ := by
    have := congrArg (fun m : Measure (Fin 3) ↦ m {0}) hd0
    simpa [mu, Measure.dirac_apply] using this
  exact absurd hone.symm (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2)).ne

end TwoAbsorbingStates

end Kernel

end ProbabilityTheory

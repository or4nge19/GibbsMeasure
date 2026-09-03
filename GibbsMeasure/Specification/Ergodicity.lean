/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.InvariantSigmaAlgebra
public import GibbsMeasure.Prereqs.Transformation
public import Mathlib.MeasureTheory.Group.Action
public import GibbsMeasure.Specification.Abstract

/-!
# Ergodic random fields (Georgii §14.1)

Georgii (14.1)–(14.6) for the configuration space `S → E` acted on by a subgroup `Θ` of the
transformation group `T` of (5.1): the set `𝓟_Θ` of `Θ`-invariant random fields
(`invariantFields`, (14.1)), the invariant σ-algebra `𝓘` (`invariantEvents`, (14.2)), and the
structure theory linking them. Georgii states the chapter for the shift group `Θ` on `ℤ^d` and
notes that Theorem (14.5) holds for **any countable subgroup** of `T`; everything here is proved
at that generality, over an arbitrary site set `S` and state space `(E, ℰ)`.

## Main results

* `measurable_invariantEvents_iff` — **Remark (14.3)(1)**: a function is `𝓘`-measurable iff it
  is measurable and invariant, `f ∘ θ = f` for all `θ ∈ Θ`.
* `ergodicSMul_iff_mem_trivialOn_invariantEvents` — **Definition (14.6)**: a `Θ`-invariant
  random field is *ergodic* iff it is trivial on `𝓘`; for a countable `Θ` this is Mathlib's
  `ErgodicSMul`, thanks to Remark (14.3)(2) (an a.e. invariant event agrees a.e. with a strictly
  invariant one — `𝓘(μ)` is the `μ`-completion of `𝓘`).
* `mem_extremePoints_invariantFields_iff_mem_trivialOn` — **Theorem (14.5)(a)**: `μ ∈ 𝓟_Θ` is
  extreme in `𝓟_Θ` iff it is trivial on `𝓘`; `ergodicSMul_iff_mem_extremePoints_invariantFields`
  is the ergodic form, valid for an arbitrary subgroup.
* `mem_invariantFields_iff_exists_withDensity` — **Theorem (14.5)(b)**: for `μ ∈ 𝓟_Θ` and a
  probability measure `ν ≪ μ`, `ν ∈ 𝓟_Θ` iff `ν = f·μ` for an `𝓘`-measurable density `f`.
* `eq_of_forall_measurableSet_invariantEvents_eq` — **Theorem (14.5)(c)**: each `μ ∈ 𝓟_Θ` is
  uniquely determined within `𝓟_Θ` by its restriction to `𝓘`.
* `exists_measurableSet_invariantEvents_eq_one_eq_zero` — **Theorem (14.5)(d)**: distinct
  extreme `Θ`-invariant random fields are mutually singular *on `𝓘`*: some `A ∈ 𝓘` has
  `μ A = 1` and `ν A = 0`.

The general countable-group statements live in
`GibbsMeasure.Mathlib.Probability.Kernel.InvariantSigmaAlgebra`; this file instantiates them at
the action of `Θ ≤ T` on `S → E` and translates between the subgroup action and Georgii's
phrasings — `MeasurePreserving` as in (5.12) (`mem_invariantFields_iff`), and the family
`Π = (θ̂_τ)` of deterministic kernels of (14.4)
(`mem_invariantFields_iff_forall_kernel_invariant`), which identifies `𝓟_Θ = 𝓟_Π` in the sense
of Corollary (7.4).
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel Set
open scoped ENNReal NNReal

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- Georgii's group `T` of transformations (5.1) acts measurably on configuration space, so
every subgroup `Θ ≤ T` does as well (`Subgroup.instMeasurableConstSMul`). -/
instance : MeasurableConstSMul (Transformation S E) (S → E) :=
  ⟨fun τ ↦ τ.measurable_toFun⟩

variable (Θ : Subgroup (Transformation S E))

/-- **Georgii (14.2).** The σ-algebra `𝓘` of `Θ`-invariant events: the measurable sets fixed by
every transformation in `Θ`. -/
abbrev invariantEvents : MeasurableSpace (S → E) :=
  MeasurableSpace.smulInvariants Θ (S → E)

/-- **Georgii (14.1).** The set `𝓟_Θ` of `Θ`-invariant random fields: the probability measures
on configuration space invariant under every transformation in `Θ`. -/
def invariantFields : Set (Measure (S → E)) :=
  {μ | IsProbabilityMeasure μ ∧ SMulInvariantMeasure Θ (S → E) μ}

variable {Θ}

lemma mem_invariantFields {μ : Measure (S → E)} :
    μ ∈ invariantFields Θ ↔ IsProbabilityMeasure μ ∧ SMulInvariantMeasure Θ (S → E) μ :=
  Iff.rfl

/-- Invariance under the subgroup action is invariance under each transformation, in the
`MeasurePreserving` phrasing of Georgii (5.12) used for `𝓟_I`. -/
lemma smulInvariantMeasure_iff_forall_measurePreserving {μ : Measure (S → E)} :
    SMulInvariantMeasure Θ (S → E) μ ↔ ∀ τ ∈ Θ, MeasurePreserving τ.toFun μ μ := by
  constructor
  · intro hinv τ hτ
    refine ⟨τ.measurable_toFun, Measure.ext fun s hs ↦ ?_⟩
    rw [Measure.map_apply τ.measurable_toFun hs]
    exact hinv.measure_preimage_smul (⟨τ, hτ⟩ : Θ) hs
  · intro h
    refine ⟨fun c s hs ↦ ?_⟩
    calc μ ((fun x ↦ c • x) ⁻¹' s) = μ.map c.1.toFun s :=
          (Measure.map_apply c.1.measurable_toFun hs).symm
      _ = μ s := by rw [(h c.1 c.2).map_eq]

/-- **Georgii (14.1)**, in the `MeasurePreserving` phrasing of (5.12). -/
lemma mem_invariantFields_iff {μ : Measure (S → E)} :
    μ ∈ invariantFields Θ ↔
      IsProbabilityMeasure μ ∧ ∀ τ ∈ Θ, MeasurePreserving τ.toFun μ μ :=
  mem_invariantFields.trans
    (and_congr_right fun _ ↦ smulInvariantMeasure_iff_forall_measurePreserving)

/-- **Georgii (14.4).** `𝓟_Θ` is the set of probability measures invariant under the family
`Π = (θ̂_τ)` of deterministic kernels of the action, in the sense of Corollary (7.4). -/
lemma mem_invariantFields_iff_forall_kernel_invariant {μ : Measure (S → E)} :
    μ ∈ invariantFields Θ ↔
      IsProbabilityMeasure μ ∧ ∀ τ : Θ, Kernel.Invariant (smulKernel Θ τ) μ :=
  mem_invariantFields.trans
    (and_congr_right fun _ ↦ smulInvariantMeasure_iff_forall_invariant)

/-- **Georgii (14.2)**, membership: `A ∈ 𝓘` iff `A` is measurable and fixed under the preimage
of every transformation in `Θ`. -/
lemma measurableSet_invariantEvents {A : Set (S → E)} :
    MeasurableSet[invariantEvents Θ] A ↔ MeasurableSet A ∧ ∀ τ ∈ Θ, τ.toFun ⁻¹' A = A := by
  rw [MeasurableSpace.measurableSet_smulInvariants]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h τ hτ
    exact h ⟨τ, hτ⟩
  · intro h c
    exact h c.1 c.2

open scoped Pointwise in
/-- **Georgii (14.2)** as literally stated: `A ∈ 𝓘` iff `A` is measurable and `θ A = A` for
every `θ ∈ Θ`. -/
lemma measurableSet_invariantEvents_iff_image {A : Set (S → E)} :
    MeasurableSet[invariantEvents Θ] A ↔ MeasurableSet A ∧ ∀ τ ∈ Θ, τ.toFun '' A = A := by
  rw [MeasurableSpace.measurableSet_smulInvariants_iff_smul_eq]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h τ hτ
    have hτA := h ⟨τ, hτ⟩
    rwa [← Set.image_smul] at hτA
  · intro h c
    rw [← Set.image_smul]
    exact h c.1 c.2

/-- **Georgii, Remark (14.3)(1).** A function into a space with measurable singletons is
`𝓘`-measurable iff it is measurable and invariant: `f ∘ θ = f` for all `θ ∈ Θ`. -/
theorem measurable_invariantEvents_iff {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {f : (S → E) → X} :
    Measurable[invariantEvents Θ] f ↔ Measurable f ∧ ∀ τ ∈ Θ, f ∘ τ.toFun = f := by
  rw [MeasurableSpace.measurable_invariants_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro h τ hτ
    funext ω
    exact h ⟨τ, hτ⟩ ω
  · intro h c ω
    exact congrFun (h c.1 c.2) ω

/-- **Georgii, Definition (14.6).** A `Θ`-invariant random field is *ergodic* iff it is trivial
on the invariant σ-algebra `𝓘`. For a countable subgroup `Θ` this triviality is exactly
Mathlib's `ErgodicSMul`, which is phrased with almost surely invariant sets; Remark (14.3)(2)
supplies the correction of an a.e. invariant set to a strictly invariant one. -/
theorem ergodicSMul_iff_mem_trivialOn_invariantEvents [Countable Θ] {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : SMulInvariantMeasure Θ (S → E) μ) :
    ErgodicSMul Θ (S → E) μ ↔ μ ∈ trivialOn (invariantEvents Θ) :=
  ergodicSMul_iff_forall_measurableSet_invariants hμ

/-- **Georgii, Theorem (14.5)(a)**, ergodic form: a `Θ`-invariant random field is ergodic iff it
is extreme in `𝓟_Θ`. This form holds for an arbitrary subgroup `Θ`. -/
theorem ergodicSMul_iff_mem_extremePoints_invariantFields {μ : Measure (S → E)}
    [IsProbabilityMeasure μ] (hμ : SMulInvariantMeasure Θ (S → E) μ) :
    ErgodicSMul Θ (S → E) μ ↔ μ ∈ (invariantFields Θ).extremePoints ℝ≥0∞ :=
  ergodicSMul_iff_mem_extremePoints hμ

/-- **Georgii, Theorem (14.5)(a).** A `Θ`-invariant random field is extreme in `𝓟_Θ` iff it is
trivial on the invariant σ-algebra `𝓘`. -/
theorem mem_extremePoints_invariantFields_iff_mem_trivialOn [Countable Θ]
    {μ : Measure (S → E)} (hμ : μ ∈ invariantFields Θ) :
    μ ∈ (invariantFields Θ).extremePoints ℝ≥0∞ ↔ μ ∈ trivialOn (invariantEvents Θ) := by
  have := hμ.1
  exact mem_extremePoints_iff_forall_measurableSet_invariants hμ.2

/-- **Georgii, Theorem (14.5)(b).** For `μ ∈ 𝓟_Θ` and a probability measure `ν ≪ μ`:
`ν ∈ 𝓟_Θ` iff `ν = f·μ` for an `𝓘`-measurable density `f`. -/
theorem mem_invariantFields_iff_exists_withDensity [Countable Θ] {μ ν : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ) [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) :
    ν ∈ invariantFields Θ ↔
      ∃ f, Measurable[invariantEvents Θ] f ∧ ν = μ.withDensity f := by
  have := hμ.1
  constructor
  · intro hν
    exact (smulInvariantMeasure_iff_exists_withDensity hμ.2 hνμ).1 hν.2
  · intro hf
    exact ⟨‹IsProbabilityMeasure ν›,
      (smulInvariantMeasure_iff_exists_withDensity hμ.2 hνμ).2 hf⟩

/-- **Georgii, Theorem (14.5)(c).** Each `μ ∈ 𝓟_Θ` is uniquely determined within `𝓟_Θ` by its
restriction to the invariant σ-algebra `𝓘`. -/
theorem eq_of_forall_measurableSet_invariantEvents_eq [Countable Θ] {μ ν : Measure (S → E)}
    (hμ : μ ∈ invariantFields Θ) (hν : ν ∈ invariantFields Θ)
    (h : ∀ A, MeasurableSet[invariantEvents Θ] A → μ A = ν A) : μ = ν := by
  have := hμ.1
  have := hν.1
  exact eq_of_forall_measurableSet_invariants_eq hμ.2 hν.2 h

/-- **Georgii, Theorem (14.5)(d).** Distinct extreme `Θ`-invariant random fields are mutually
singular *on the invariant σ-algebra*: there is an `A ∈ 𝓘` with `μ A = 1` and `ν A = 0`. -/
theorem exists_measurableSet_invariantEvents_eq_one_eq_zero [Countable Θ]
    {μ ν : Measure (S → E)}
    (hμ : μ ∈ (invariantFields Θ).extremePoints ℝ≥0∞)
    (hν : ν ∈ (invariantFields Θ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    ∃ A, MeasurableSet[invariantEvents Θ] A ∧ μ A = 1 ∧ ν A = 0 :=
  Kernel.exists_measurableSet_invariants_eq_one_eq_zero hμ hν hne

/-- **Georgii, Theorem (14.5)(d)**, measure form: distinct extreme `Θ`-invariant random fields
are mutually singular. -/
theorem mutuallySingular_of_mem_extremePoints_invariantFields [Countable Θ]
    {μ ν : Measure (S → E)}
    (hμ : μ ∈ (invariantFields Θ).extremePoints ℝ≥0∞)
    (hν : ν ∈ (invariantFields Θ).extremePoints ℝ≥0∞) (hne : μ ≠ ν) :
    μ.MutuallySingular ν :=
  Kernel.mutuallySingular_of_mem_extremePoints_smulInvariant hμ hν hne

/-! ### Georgii's shift group -/

section ShiftGroup

variable {S E : Type*} [MeasurableSpace E] [AddGroup S]

variable (S E) in
/-- **Georgii's shift group `Θ`** (5.2)(1): the subgroup of the transformation group generated by
the shifts, as the range of the homomorphism `j ↦ θ_j` from the additive site group. -/
def shiftGroup : Subgroup (Transformation S E) where
  carrier := Set.range (shift E : S → Transformation S E)
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨j + i, ?_⟩
    refine Transformation.ext ?_ rfl
    ext k
    change k + (j + i) = k + j + i
    exact (add_assoc k j i).symm
  one_mem' := ⟨0, by
    refine Transformation.ext ?_ rfl
    ext k
    change k + 0 = k
    exact add_zero k⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    refine ⟨-i, ?_⟩
    refine Transformation.ext ?_ rfl
    ext k
    simp [shift, Transformation.inv]

@[simp] lemma mem_shiftGroup {τ : Transformation S E} :
    τ ∈ shiftGroup S E ↔ ∃ j : S, shift E j = τ := Iff.rfl

lemma shift_mem_shiftGroup (j : S) : shift E j ∈ shiftGroup S E := ⟨j, rfl⟩

instance [Countable S] : Countable (shiftGroup S E) :=
  Set.countable_range (shift E : S → Transformation S E) |>.to_subtype

/-- **Georgii (14.1)–(14.2) for the shift group**: `μ` is shift invariant exactly when it is
`Θ`-invariant, so `𝓟_Θ` and the invariant σ-algebra `𝓘` are the ones Georgii writes. -/
lemma mem_invariantFields_shiftGroup {μ : Measure (S → E)} :
    μ ∈ invariantFields (shiftGroup S E) ↔
      IsProbabilityMeasure μ ∧ ∀ j : S, MeasurePreserving (shift E j).toFun μ μ := by
  rw [mem_invariantFields_iff]
  refine and_congr_right fun _ ↦ ⟨fun h j ↦ h _ (shift_mem_shiftGroup j), ?_⟩
  rintro h τ ⟨j, rfl⟩
  exact h j

/-- Convex combinations of shift-invariant random fields are shift invariant: `𝓟_Θ` is convex
(Georgii, (14.1)). -/
lemma smul_add_smul_mem_invariantFields_shiftGroup {μ₁ μ₂ : Measure (S → E)}
    (hμ₁ : μ₁ ∈ invariantFields (shiftGroup S E))
    (hμ₂ : μ₂ ∈ invariantFields (shiftGroup S E)) {s t : ℝ≥0} (hst : s + t = 1) :
    s • μ₁ + t • μ₂ ∈ invariantFields (shiftGroup S E) := by
  obtain ⟨h₁, h₁'⟩ := mem_invariantFields_shiftGroup.1 hμ₁
  obtain ⟨h₂, h₂'⟩ := mem_invariantFields_shiftGroup.1 hμ₂
  refine mem_invariantFields_shiftGroup.2 ⟨⟨?_⟩, fun j ↦ ⟨(shift E j).measurable_toFun, ?_⟩⟩
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.coe_add, hst, ENNReal.coe_one]
  · rw [Measure.map_add _ _ (shift E j).measurable_toFun, Measure.map_smul, Measure.map_smul,
      (h₁' j).map_eq, (h₂' j).map_eq]

end ShiftGroup

section ShiftAction

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S]

variable (S E) in
/-- The shift action of the site group on configuration space, `j +ᵥ ω = θ_j ω`, i.e.
`(j +ᵥ ω) i = ω (i - j)` (Georgii (5.2)(1)). -/
@[instance_reducible] def shiftAddAction : AddAction S (S → E) where
  vadd j ω := (shift E j).toFun ω
  zero_vadd ω := funext fun i ↦ by
    change (shift E 0).toFun ω i = ω i
    simp
  add_vadd j k ω := funext fun i ↦ by
    change (shift E (j + k)).toFun ω i = (shift E j).toFun ((shift E k).toFun ω) i
    simp [sub_sub]

attribute [local instance] shiftAddAction

@[simp] lemma shift_vadd (j : S) (ω : S → E) : j +ᵥ ω = (shift E j).toFun ω := rfl

/-- The shifts act measurably. -/
lemma measurableConstVAdd_shift : MeasurableConstVAdd S (S → E) :=
  ⟨fun j ↦ (shift E j).measurable_toFun⟩

attribute [local instance] measurableConstVAdd_shift

/-- Under the shift action, the strictly invariant σ-algebra of the site group is Georgii's `𝓘`
for the shift group `Θ` (14.2). -/
lemma smulInvariants_multiplicative_eq_invariantEvents_shiftGroup :
    MeasurableSpace.smulInvariants (Multiplicative S) (S → E)
      = invariantEvents (shiftGroup S E) := by
  refine (MeasurableSpace.ext fun A ↦ ?_).symm
  rw [measurableSet_invariantEvents, MeasurableSpace.measurableSet_smulInvariants]
  refine and_congr_right fun _ ↦ ⟨fun h c ↦ h _ (shift_mem_shiftGroup c.toAdd), ?_⟩
  rintro h _ ⟨j, rfl⟩
  exact h (Multiplicative.ofAdd j)

/-- Under the shift action, invariance for the site group is invariance for the shift group. -/
lemma vaddInvariantMeasure_iff_smulInvariantMeasure_shiftGroup {μ : Measure (S → E)} :
    VAddInvariantMeasure S (S → E) μ ↔ SMulInvariantMeasure (shiftGroup S E) (S → E) μ := by
  have h : VAddInvariantMeasure S (S → E) μ ↔ ∀ c : S, MeasurePreserving (c +ᵥ ·) μ μ :=
    (vaddInvariantMeasure_tfae S μ).out 1 7
  refine h.trans (Iff.trans ?_ smulInvariantMeasure_iff_forall_measurePreserving.symm)
  constructor
  · rintro h τ ⟨j, rfl⟩
    exact h j
  · intro h j
    exact h (shift E j) (shift_mem_shiftGroup j)

/-- **Georgii (14.1) for the shift group**, in the additive phrasing: `𝓟_Θ` is the set of
probability measures invariant under the shift action of the site group. -/
lemma mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure {μ : Measure (S → E)} :
    μ ∈ invariantFields (shiftGroup S E) ↔
      IsProbabilityMeasure μ ∧ VAddInvariantMeasure S (S → E) μ :=
  mem_invariantFields.trans
    (and_congr_right fun _ ↦ vaddInvariantMeasure_iff_smulInvariantMeasure_shiftGroup.symm)

/-- A shift-invariant random field is an invariant measure for the shift action. -/
lemma vaddInvariantMeasure_of_forall_measurePreserving_shift {μ : Measure (S → E)}
    (hμ : ∀ j : S, MeasurePreserving (shift E j).toFun μ μ) :
    VAddInvariantMeasure S (S → E) μ :=
  ⟨fun j _ hs ↦ (hμ j).measure_preimage hs.nullMeasurableSet⟩

end ShiftAction

end MeasureTheory.GibbsMeasure

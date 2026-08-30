/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.AbstractPAKernel
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.ZeroOne

/-!
# Georgii (7.16), (7.17): exchangeability and the Hewitt-Savage zero-one law

Georgii's Example (7.16) observes that the exchangeable probability measures on `(E, ℰ)^ℕ` fit
into the abstract framework of Remark (7.13): the σ-algebras are the `Iₙ`-invariant events, where
`Iₙ` is the group of permutations of `ℕ` fixing every index `≥ n`, and the kernels are the
symmetrisations `γₙ(A | ω) = |Iₙ|⁻¹ ∑_{σ ∈ Iₙ} 1_A(ω ∘ σ)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal symmDiff

namespace MeasureTheory.GibbsMeasure

/-! ### Finitary permutations of `ℕ` -/

/-- Georgii's `Iₙ`: the group of permutations of `ℕ` fixing every index `≥ n`. -/
def finPerm (n : ℕ) : Subgroup (Equiv.Perm ℕ) where
  carrier := {σ | ∀ i, n ≤ i → σ i = i}
  mul_mem' {σ τ} hσ hτ i hi := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Equiv.Perm.mul_apply, hτ i hi, hσ i hi]
  one_mem' i _ := rfl
  inv_mem' {σ} hσ i hi := by
    simp only [Set.mem_ofPred_eq] at *
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hσ i hi]

lemma mem_finPerm {n : ℕ} {σ : Equiv.Perm ℕ} : σ ∈ finPerm n ↔ ∀ i, n ≤ i → σ i = i := Iff.rfl

lemma finPerm_mono : Monotone finPerm := fun _ _ h _ hσ i hi ↦ hσ i (h.trans hi)

lemma finPerm_apply_lt {n : ℕ} {σ : Equiv.Perm ℕ} (hσ : σ ∈ finPerm n) {i : ℕ} (hi : i < n) :
    σ i < n := by
  by_contra h
  exact absurd (σ.injective (hσ _ (not_lt.1 h))) (by omega)

instance instFiniteFinPerm (n : ℕ) : Finite (finPerm n) := by
  refine Finite.of_injective
    (fun σ : finPerm n ↦ fun i : Fin n ↦ (⟨(σ : Equiv.Perm ℕ) i, finPerm_apply_lt σ.2 i.2⟩ : Fin n))
    fun σ τ h ↦ ?_
  refine Subtype.ext (Equiv.ext fun i ↦ ?_)
  rcases lt_or_ge i n with hi | hi
  · exact congrArg Fin.val (congrFun h ⟨i, hi⟩)
  · rw [σ.2 i hi, τ.2 i hi]

noncomputable instance instFintypeFinPerm (n : ℕ) : Fintype (finPerm n) := Fintype.ofFinite _

lemma card_finPerm_pos (n : ℕ) : 0 < Fintype.card (finPerm n) := Fintype.card_pos

lemma card_finPerm_ne_zero (n : ℕ) : (Fintype.card (finPerm n) : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (card_finPerm_pos n).ne'

lemma card_finPerm_ne_top (n : ℕ) : (Fintype.card (finPerm n) : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.natCast_ne_top _

/-- The group of permutations of `ℕ` moving only finitely many indices, Georgii's
`I = ⋃ₙ Iₙ`. -/
def finitaryPerm : Subgroup (Equiv.Perm ℕ) where
  carrier := {σ | ∃ n, ∀ i, n ≤ i → σ i = i}
  mul_mem' := by
    rintro σ τ ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨max n m, fun i hi ↦ by
      rw [Equiv.Perm.mul_apply, hm i (le_of_max_le_right hi), hn i (le_of_max_le_left hi)]⟩
  one_mem' := ⟨0, fun _ _ ↦ rfl⟩
  inv_mem' := by
    rintro σ ⟨n, hn⟩
    exact ⟨n, fun i hi ↦ by rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq, hn i hi]⟩

lemma finPerm_le_finitaryPerm (n : ℕ) : finPerm n ≤ finitaryPerm := fun _ hσ ↦ ⟨n, hσ⟩

lemma mem_finitaryPerm_iff {σ : Equiv.Perm ℕ} : σ ∈ finitaryPerm ↔ ∃ n, σ ∈ finPerm n := Iff.rfl

/-! ### The action on configuration space -/

variable {E : Type*} [MeasurableSpace E]

/-- The action of a permutation of the index set on configurations, `permute σ ω = ω ∘ σ`. -/
def permute (σ : Equiv.Perm ℕ) (ω : ℕ → E) : ℕ → E := fun i ↦ ω (σ i)

omit [MeasurableSpace E] in
@[simp] lemma permute_apply (σ : Equiv.Perm ℕ) (ω : ℕ → E) (i : ℕ) : permute σ ω i = ω (σ i) := rfl

omit [MeasurableSpace E] in
@[simp] lemma permute_one (ω : ℕ → E) : permute 1 ω = ω := rfl

omit [MeasurableSpace E] in
lemma permute_permute (σ τ : Equiv.Perm ℕ) (ω : ℕ → E) :
    permute σ (permute τ ω) = permute (τ * σ) ω := rfl

lemma measurable_permute (σ : Equiv.Perm ℕ) : Measurable (permute (E := E) σ) :=
  measurable_pi_lambda _ fun i ↦ measurable_pi_apply _

/-! ### Georgii's `𝓘ₙ` and `𝓘` -/

set_option warn.classDefReducibility false in
/-- Georgii's `𝓘ₙ`: the σ-algebra of measurable events invariant under `Iₙ`. -/
def symmSub (E : Type*) [MeasurableSpace E] (n : ℕ) : MeasurableSpace (ℕ → E) where
  MeasurableSet' A := MeasurableSet A ∧ ∀ σ ∈ finPerm n, permute σ ⁻¹' A = A
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ ↦ by simp⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun σ hσ ↦ by
    rw [Set.preimage_compl, hA.2 σ hσ]⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun j ↦ (hf j).1, fun σ hσ ↦ by
    rw [Set.preimage_iUnion]; exact Set.iUnion_congr fun j ↦ (hf j).2 σ hσ⟩

lemma measurableSet_symmSub_iff {n : ℕ} {A : Set (ℕ → E)} :
    MeasurableSet[symmSub E n] A ↔ MeasurableSet A ∧ ∀ σ ∈ finPerm n, permute σ ⁻¹' A = A :=
  Iff.rfl

lemma symmSub_le (n : ℕ) : symmSub E n ≤ (inferInstance : MeasurableSpace (ℕ → E)) :=
  fun _ hA ↦ hA.1

lemma symmSub_antitone : Antitone (symmSub E) :=
  fun _ _ h _ hA ↦ ⟨hA.1, fun σ hσ ↦ hA.2 σ (finPerm_mono h hσ)⟩

set_option warn.classDefReducibility false in
/-- Georgii's `𝓘`: the σ-algebra of symmetric events. -/
def symmetricSigmaAlgebra (E : Type*) [MeasurableSpace E] : MeasurableSpace (ℕ → E) :=
  ⨅ n, symmSub E n

lemma symmetricSigmaAlgebra_le :
    symmetricSigmaAlgebra E ≤ (inferInstance : MeasurableSpace (ℕ → E)) :=
  (iInf_le _ 0).trans (symmSub_le 0)

lemma measurableSet_symmetricSigmaAlgebra_iff {A : Set (ℕ → E)} :
    MeasurableSet[symmetricSigmaAlgebra E] A ↔ ∀ n, MeasurableSet[symmSub E n] A := by
  refine ⟨fun hA n ↦ iInf_le (fun n ↦ symmSub E n) n A hA, fun hA ↦ ?_⟩
  exact (MeasurableSpace.measurableSet_iInf (m := fun n ↦ symmSub E n) (s := A)).2 hA

/-- A measurable `Iₙ`-invariant function is `𝓘ₙ`-measurable. -/
lemma measurable_symmSub {X : Type*} [MeasurableSpace X] {n : ℕ} {f : (ℕ → E) → X}
    (hf : Measurable f) (hinv : ∀ σ ∈ finPerm n, ∀ ω, f (permute σ ω) = f ω) :
    Measurable[symmSub E n] f := fun B hB ↦
  ⟨hf hB, fun σ hσ ↦ by ext ω; simp only [Set.mem_preimage, hinv σ hσ ω]⟩


/-! ### Georgii's symmetrisation kernels `γₙ` -/

variable (E) in
/-- The unnormalised symmetrisation `∑_{σ ∈ Iₙ} 1_A(σω)` of an indicator. -/
noncomputable def symmSum (n : ℕ) (A : Set (ℕ → E)) (ω : ℕ → E) : ℝ≥0∞ :=
  ∑ σ : finPerm n, A.indicator 1 (permute (σ : Equiv.Perm ℕ) ω)

lemma symmSum_permute {n : ℕ} (A : Set (ℕ → E)) {τ : Equiv.Perm ℕ} (hτ : τ ∈ finPerm n)
    (ω : ℕ → E) : symmSum E n A (permute τ ω) = symmSum E n A ω := by
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : finPerm n)) _ _ fun σ ↦ ?_
  rw [permute_permute]
  rfl

/-- Right translation by an element of `Iₙ` leaves the symmetrised indicator unchanged. -/
lemma sum_indicator_permute_mul_right {n : ℕ} (A : Set (ℕ → E)) {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ finPerm n) (ω : ℕ → E) :
    ∑ τ : finPerm n, A.indicator 1 (permute ((τ : Equiv.Perm ℕ) * σ) ω) = symmSum E n A ω :=
  Fintype.sum_equiv (Equiv.mulRight (⟨σ, hσ⟩ : finPerm n)) _ _ fun _ ↦ rfl

lemma measurable_symmSum {n : ℕ} {A : Set (ℕ → E)} (hA : MeasurableSet A) :
    Measurable[symmSub E n] (symmSum E n A) :=
  measurable_symmSub
    (Finset.measurable_sum _ fun σ _ ↦ (measurable_one.indicator hA).comp (measurable_permute _))
    fun _ hτ _ ↦ symmSum_permute A hτ _

@[simp] lemma symmSum_univ (n : ℕ) (ω : ℕ → E) :
    symmSum E n (univ : Set (ℕ → E)) ω = Fintype.card (finPerm n) := by
  simp [symmSum, Finset.card_univ]

/-- Composing symmetrisations: `γₘ` averaged over `Iₙ` is `|Iₘ|` times `γₙ`, for `m ≤ n`. -/
lemma sum_symmSum {m n : ℕ} (hmn : m ≤ n) (A : Set (ℕ → E)) (ω : ℕ → E) :
    ∑ τ : finPerm n, symmSum E m A (permute (τ : Equiv.Perm ℕ) ω)
      = (Fintype.card (finPerm m) : ℝ≥0∞) * symmSum E n A ω := by
  simp only [symmSum, permute_permute]
  rw [Finset.sum_comm,
    Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) ↦
      sum_indicator_permute_mul_right A (finPerm_mono hmn σ.2) ω]
  simp [Finset.card_univ, nsmul_eq_mul, symmSum]

variable (E) in
/-- The uniform average of the Dirac measures at the `Iₙ`-permutations of `ω`. -/
noncomputable def symmMeasure (n : ℕ) (ω : ℕ → E) : Measure (ℕ → E) :=
  (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ •
    ∑ σ : finPerm n, Measure.dirac (permute (σ : Equiv.Perm ℕ) ω)

lemma symmMeasure_apply (n : ℕ) (ω : ℕ → E) {A : Set (ℕ → E)} (hA : MeasurableSet A) :
    symmMeasure E n ω A = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * symmSum E n A ω := by
  simp [symmMeasure, symmSum, Measure.dirac_apply' _ hA]

lemma measurable_symmMeasure (n : ℕ) : Measurable[symmSub E n] (symmMeasure E n) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simpa only [symmMeasure_apply _ _ hA] using (measurable_symmSum hA).const_mul _

variable (E) in
/-- **Georgii (7.16)**: the symmetrisation kernel `γₙ(A|ω) = |Iₙ|⁻¹ ∑_{σ ∈ Iₙ} 1_A(σω)`. -/
noncomputable def symmKernel (n : ℕ) : Kernel[symmSub E n] (ℕ → E) (ℕ → E) :=
  @Kernel.mk (ℕ → E) (ℕ → E) (symmSub E n) _ (symmMeasure E n) (measurable_symmMeasure n)

@[simp] lemma symmKernel_toFun (n : ℕ) (ω : ℕ → E) : symmKernel E n ω = symmMeasure E n ω := rfl

lemma symmKernel_apply (n : ℕ) (ω : ℕ → E) {A : Set (ℕ → E)} (hA : MeasurableSet A) :
    symmKernel E n ω A = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ * symmSum E n A ω :=
  symmMeasure_apply n ω hA

instance isMarkovKernel_symmKernel (n : ℕ) : IsMarkovKernel (symmKernel E n) := by
  refine ⟨fun ω ↦ ⟨?_⟩⟩
  rw [symmKernel_apply n ω MeasurableSet.univ, symmSum_univ,
    ENNReal.inv_mul_cancel (card_finPerm_ne_zero n) (card_finPerm_ne_top n)]

lemma isProper_symmKernel (n : ℕ) : (symmKernel E n).IsProper := by
  rw [Kernel.isProper_iff_inter_eq_indicator_mul (symmSub_le n)]
  intro A hA B hB ω
  have hB' : MeasurableSet B := hB.1
  rw [symmKernel_apply n ω (hA.inter hB'), symmKernel_apply n ω hA]
  have hsum : symmSum E n (A ∩ B) ω = B.indicator 1 ω * symmSum E n A ω := by
    simp only [symmSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    have hmem : permute (σ : Equiv.Perm ℕ) ω ∈ B ↔ ω ∈ B := by
      constructor
      · intro h; rw [← hB.2 _ σ.2]; exact h
      · intro h; rw [← hB.2 _ σ.2] at h; exact h
    by_cases hω : ω ∈ B
    · have h1 : permute (σ : Equiv.Perm ℕ) ω ∈ B := hmem.2 hω
      rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul]
      by_cases hAx : permute (σ : Equiv.Perm ℕ) ω ∈ A
      · rw [Set.indicator_of_mem (Set.mem_inter hAx h1), Set.indicator_of_mem hAx]
      · rw [Set.indicator_of_notMem fun h ↦ hAx h.1, Set.indicator_of_notMem hAx]
    · have h1 : permute (σ : Equiv.Perm ℕ) ω ∉ B := fun h ↦ hω (hmem.1 h)
      rw [Set.indicator_of_notMem hω, zero_mul, Set.indicator_of_notMem fun h ↦ h1 h.2]
  rw [hsum, ← mul_assoc, ← mul_assoc, mul_comm ((Fintype.card (finPerm n) : ℝ≥0∞)⁻¹)]

lemma lintegral_symmKernel {n : ℕ} {f : (ℕ → E) → ℝ≥0∞} (hf : Measurable f) (ω : ℕ → E) :
    ∫⁻ x, f x ∂(symmKernel E n ω) = (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ *
      ∑ τ : finPerm n, f (permute (τ : Equiv.Perm ℕ) ω) := by
  rw [symmKernel_toFun, symmMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac' _ hf, smul_eq_mul]

lemma isConsistent_symmKernel {m n : ℕ} (hmn : m ≤ n) :
    (symmKernel E m).comap id (symmSub_le m) ∘ₖ symmKernel E n = symmKernel E n := by
  refine Kernel.ext fun ω ↦ Measure.ext fun A hA ↦ ?_
  have hmeas : Measurable fun x : ℕ → E ↦ symmKernel E m x A :=
    ((symmKernel E m).measurable_coe hA).mono (symmSub_le m) le_rfl
  rw [Kernel.comp_apply' _ _ _ hA]
  simp only [Kernel.comap_apply, id_eq]
  rw [lintegral_symmKernel hmeas ω]
  simp only [symmKernel_apply _ _ hA]
  rw [← Finset.mul_sum, sum_symmSum hmn, ← mul_assoc, mul_assoc,
    ← mul_assoc ((Fintype.card (finPerm m) : ℝ≥0∞)⁻¹),
    ENNReal.inv_mul_cancel (card_finPerm_ne_zero m) (card_finPerm_ne_top m), one_mul]

variable (E) in
/-- **Georgii, Example (7.16)**: exchangeable distributions form the invariant measures of an
abstract specification in the sense of Remark (7.13). -/
noncomputable def exchangeableSpec : AbstractSpecification (ℕ → E) ℕ where
  sub := symmSub E
  sub_le := symmSub_le
  sub_antitone := symmSub_antitone
  ker := symmKernel E
  isMarkovKernel := isMarkovKernel_symmKernel
  isProper := isProper_symmKernel
  isConsistent _ _ := isConsistent_symmKernel

@[simp] lemma exchangeableSpec_sub (n : ℕ) : (exchangeableSpec E).sub n = symmSub E n := rfl

@[simp] lemma exchangeableSpec_ker (n : ℕ) : (exchangeableSpec E).ker n = symmKernel E n := rfl

@[simp] lemma exchangeableSpec_tail : (exchangeableSpec E).tail = symmetricSigmaAlgebra E := rfl

/-! ### Exchangeable measures -/

/-- A measure is *exchangeable* if it is invariant under every permutation of finitely many
coordinates. -/
def IsExchangeable (μ : Measure (ℕ → E)) : Prop :=
  ∀ σ ∈ finitaryPerm, μ.map (permute σ) = μ

lemma bind_symmKernel_apply (μ : Measure (ℕ → E)) (n : ℕ) {A : Set (ℕ → E)}
    (hA : MeasurableSet A) :
    μ.bind (symmKernel E n) A =
      (Fintype.card (finPerm n) : ℝ≥0∞)⁻¹ *
        ∑ σ : finPerm n, μ (permute (σ : Equiv.Perm ℕ) ⁻¹' A) := by
  have hmeas : Measurable fun ω : ℕ → E ↦ symmKernel E n ω :=
    (symmKernel E n).measurable.mono (symmSub_le n) le_rfl
  rw [Measure.bind_apply hA hmeas.aemeasurable]
  simp only [symmKernel_apply _ _ hA, symmSum]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (card_finPerm_ne_zero n)),
    lintegral_finsetSum (f := fun (σ : finPerm n) a ↦ A.indicator 1 (permute (σ : Equiv.Perm ℕ) a))
      _ fun σ _ ↦ (measurable_one.indicator hA).comp (measurable_permute _)]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ ↦ ?_)
  rw [← lintegral_indicator_one (measurable_permute (σ : Equiv.Perm ℕ) hA)]
  exact lintegral_congr fun _ ↦ rfl

/-- **Georgii (7.16)**: `𝒫_I = {μ : μγₙ = μ for all n}`. -/
theorem mem_exchangeableSpec_invariant_iff (μ : Measure (ℕ → E)) :
    μ ∈ (exchangeableSpec E).invariant ↔ IsProbabilityMeasure μ ∧ IsExchangeable μ := by
  constructor
  · rintro ⟨hp, hbind⟩
    refine ⟨hp, fun σ hσ ↦ ?_⟩
    obtain ⟨n, hn⟩ := hσ
    have hbn : μ.bind (symmKernel E n) = μ := hbind n
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.map_apply (measurable_permute σ) hA]
    have hpre : MeasurableSet (permute σ ⁻¹' A) := measurable_permute σ hA
    have h := bind_symmKernel_apply μ n hpre
    rw [hbn] at h
    have hre : ∀ τ : finPerm n, permute (τ : Equiv.Perm ℕ) ⁻¹' (permute σ ⁻¹' A)
        = permute ((τ : Equiv.Perm ℕ) * σ) ⁻¹' A := fun _ ↦ by
      rw [← Set.preimage_comp]; rfl
    have h2 : ∑ τ : finPerm n, μ (permute (τ : Equiv.Perm ℕ) ⁻¹' (permute σ ⁻¹' A))
        = ∑ τ : finPerm n, μ (permute ((τ : Equiv.Perm ℕ) * σ) ⁻¹' A) :=
      Finset.sum_congr rfl fun τ _ ↦ congrArg μ (hre τ)
    rw [h, h2, Fintype.sum_equiv (Equiv.mulRight (⟨σ, hn⟩ : finPerm n))
      (fun τ : finPerm n ↦ μ (permute ((τ : Equiv.Perm ℕ) * σ) ⁻¹' A))
      (fun ρ : finPerm n ↦ μ (permute (ρ : Equiv.Perm ℕ) ⁻¹' A)) fun _ ↦ rfl,
      ← bind_symmKernel_apply μ n hA, hbn]
  · rintro ⟨hp, hex⟩
    refine ⟨hp, fun n ↦ ?_⟩
    show μ.bind (symmKernel E n) = μ
    refine Measure.ext fun A hA ↦ ?_
    rw [bind_symmKernel_apply μ n hA]
    have hcst : ∀ σ : finPerm n, μ (permute (σ : Equiv.Perm ℕ) ⁻¹' A) = μ A := fun σ ↦ by
      rw [← Measure.map_apply (measurable_permute _) hA,
        hex _ (finPerm_le_finitaryPerm n σ.2)]
    rw [Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) ↦ hcst σ, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel (card_finPerm_ne_zero n) (card_finPerm_ne_top n), one_mul]

theorem exchangeableSpec_invariant :
    (exchangeableSpec E).invariant = {μ | IsProbabilityMeasure μ ∧ IsExchangeable μ} :=
  Set.ext mem_exchangeableSpec_invariant_iff

/-- **Georgii (7.7)(a)** for exchangeable measures: an exchangeable probability measure is extreme
in `𝒫_I` iff it is trivial on the σ-algebra `𝓘` of symmetric events. -/
theorem mem_extremePoints_iff_mem_trivialOn_symmetric {μ : Measure (ℕ → E)}
    (hμ : μ ∈ (exchangeableSpec E).invariant) :
    μ ∈ (exchangeableSpec E).invariant.extremePoints ℝ≥0∞ ↔
      μ ∈ trivialOn (symmetricSigmaAlgebra E) :=
  AbstractSpecification.mem_extremePoints_iff_mem_trivialOn hμ

/-! ### Cylinder approximation -/

/-- Events depending on finitely many coordinates form a ring of sets. -/
lemma isSetRing_finiteCoordEvents :
    IsSetRing {B : Set (ℕ → E) | ∃ k, MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Iio k)] B}
    := by
  have hmono : ∀ {k l : ℕ}, k ≤ l → ∀ {B : Set (ℕ → E)},
      MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Iio k)] B →
      MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Iio l)] B :=
    fun hkl _ hB ↦ cylinderEvents_mono (X := fun _ : ℕ ↦ E) (Iio_subset_Iio hkl) _ hB
  refine ⟨⟨0, @MeasurableSet.empty _ (cylinderEvents (X := fun _ : ℕ ↦ E) (Iio 0))⟩, ?_, ?_⟩
  · rintro s t ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨max k l, (hmono (le_max_left k l) hk).union (hmono (le_max_right k l) hl)⟩
  · rintro s t ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨max k l, (hmono (le_max_left k l) hk).diff (hmono (le_max_right k l) hl)⟩

lemma generateFrom_finiteCoordEvents :
    (inferInstance : MeasurableSpace (ℕ → E)) = MeasurableSpace.generateFrom
      {B : Set (ℕ → E) | ∃ k, MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Iio k)] B} := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun B ⟨_, hk⟩ ↦ cylinderEvents_le_pi _ hk)
  refine iSup_le fun i ↦ ?_
  rintro _ ⟨t, ht, rfl⟩
  exact MeasurableSpace.measurableSet_generateFrom ⟨i + 1,
    measurable_cylinderEvent_apply (X := fun _ : ℕ ↦ E)
      (Δ := Iio (i + 1)) (mem_Iio.2 (Nat.lt_succ_self i)) ht⟩

/-- Every measurable set is approximated in measure by an event depending on finitely many
coordinates. -/
lemma exists_cylinder_measure_symmDiff_lt (μ : Measure (ℕ → E)) [IsFiniteMeasure μ]
    {A : Set (ℕ → E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (k : ℕ) (B : Set (ℕ → E)),
      MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Set.Iio k)] B ∧ μ (B ∆ A) < ε := by
  obtain ⟨B, ⟨k, hk⟩, hlt⟩ :=
    exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ) isSetRing_finiteCoordEvents
      ⟨{univ}, countable_singleton _, by rintro s rfl; exact ⟨0, @MeasurableSet.univ _ (cylinderEvents (X := fun _ : ℕ ↦ E) (Iio 0))⟩, by simp⟩
      generateFrom_finiteCoordEvents hA hε
  exact ⟨k, B, hk, hlt⟩

/-- Permuting the coordinates by `σ` sends `J`-cylinder events to `K`-cylinder events whenever
`σ` maps `J` into `K`. -/
lemma measurableSet_preimage_permute {J K : Set ℕ} {σ : Equiv.Perm ℕ} (h : ∀ i ∈ J, σ i ∈ K)
    {B : Set (ℕ → E)} (hB : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) J] B) :
    MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) K] (permute σ ⁻¹' B) :=
  (measurable_cylinderEvents_iff (X := fun _ : ℕ ↦ E)
    (mα := cylinderEvents (X := fun _ : ℕ ↦ E) K) (g := permute σ)).2
    (fun i hi ↦ measurable_cylinderEvent_apply (X := fun _ : ℕ ↦ E) (h i hi)) hB

/-! ### The block swap -/

/-- The involution of `ℕ` exchanging `i` and `i + k` for `i < k`. -/
def blockSwapFun (k i : ℕ) : ℕ := if i < k then i + k else if i < 2 * k then i - k else i

lemma blockSwapFun_involutive (k : ℕ) : Function.Involutive (blockSwapFun k) := by
  intro i
  simp only [blockSwapFun]
  split_ifs <;> omega

/-- The permutation of `ℕ` exchanging the blocks `[0, k)` and `[k, 2k)`. -/
def blockSwap (k : ℕ) : Equiv.Perm ℕ :=
  Function.Involutive.toPerm (blockSwapFun k) (blockSwapFun_involutive k)

@[simp] lemma blockSwap_apply (k i : ℕ) : blockSwap k i = blockSwapFun k i := rfl

lemma blockSwap_mem_finPerm (k : ℕ) : blockSwap k ∈ finPerm (2 * k) := by
  intro i hi
  simp only [blockSwap_apply, blockSwapFun]
  split_ifs <;> omega

lemma blockSwap_mem_finitaryPerm (k : ℕ) : blockSwap k ∈ finitaryPerm :=
  finPerm_le_finitaryPerm _ (blockSwap_mem_finPerm k)

lemma blockSwap_maps_Iio (k : ℕ) : ∀ i ∈ Set.Iio k, blockSwap k i ∈ Set.Ico k (2 * k) := by
  intro i hi
  simp only [mem_Iio] at hi
  simp only [blockSwap_apply, blockSwapFun, mem_Ico]
  split_ifs <;> omega

/-- Squaring is stable under a small perturbation. -/
private lemma mul_self_le_of_le_add {x y ε : ℝ≥0∞} (hx : x ≤ y + ε) (hy : y ≤ 1) (hε : ε ≤ 1) :
    x * x ≤ y * y + 3 * ε := by
  have h1 : y * ε ≤ ε := by calc y * ε ≤ 1 * ε := by gcongr
                                 _ = ε := one_mul ε
  have h2 : ε * y ≤ ε := by calc ε * y ≤ ε * 1 := by gcongr
                                 _ = ε := mul_one ε
  have h3 : ε * ε ≤ ε := by calc ε * ε ≤ 1 * ε := by gcongr
                                 _ = ε := one_mul ε
  calc x * x ≤ (y + ε) * (y + ε) := mul_le_mul' hx hx
    _ = y * y + (y * ε + (ε * y + ε * ε)) := by ring
    _ ≤ y * y + (ε + (ε + ε)) := by gcongr
    _ = y * y + 3 * ε := by ring

/-! ### The Hewitt-Savage zero-one law -/

section HewittSavage

variable {ν : Measure E} [IsProbabilityMeasure ν]

/-- Product measures are exchangeable. -/
theorem isExchangeable_infinitePi :
    IsExchangeable (Measure.infinitePi (fun _ : ℕ ↦ ν)) :=
  fun σ _ ↦ Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ ν) σ.injective

/-- Under a product measure, disjoint sets of coordinates generate independent σ-algebras. -/
lemma indep_cylinderEvents_infinitePi {J K : Set ℕ} (hJK : Disjoint J K) :
    Indep (cylinderEvents (X := fun _ : ℕ ↦ E) J) (cylinderEvents (X := fun _ : ℕ ↦ E) K)
      (Measure.infinitePi (fun _ : ℕ ↦ ν)) :=
  indep_iSup_of_disjoint (fun i ↦ (measurable_pi_apply i).comap_le)
    (iIndepFun_infinitePi (P := fun _ : ℕ ↦ ν) (X := fun (_ : ℕ) (x : E) ↦ x)
      fun _ ↦ measurable_id) hJK

/-- **The Hewitt-Savage zero-one law (Georgii (7.17))**: an i.i.d. product measure on `Eᴺ` is
trivial on the σ-algebra of symmetric events. -/
theorem measure_symmetric_eq_zero_or_one {A : Set (ℕ → E)}
    (hA : MeasurableSet[symmetricSigmaAlgebra E] A) :
    Measure.infinitePi (fun _ : ℕ ↦ ν) A = 0 ∨ Measure.infinitePi (fun _ : ℕ ↦ ν) A = 1 := by
  set μ := Measure.infinitePi (fun _ : ℕ ↦ ν) with hμdef
  have hprob : IsProbabilityMeasure μ := by rw [hμdef]; infer_instance
  have hAn : ∀ n, MeasurableSet[symmSub E n] A := measurableSet_symmetricSigmaAlgebra_iff.1 hA
  have hAm : MeasurableSet A := (hAn 0).1
  have hA1 : μ A ≤ 1 := prob_le_one
  have key : ∀ ε : ℝ≥0∞, 0 < ε → ε ≤ 1 →
      μ A ≤ μ A * μ A + 5 * ε ∧ μ A * μ A ≤ μ A + 4 * ε := by
    intro ε hε hε1
    obtain ⟨k, B, hB, hBA⟩ := exists_cylinder_measure_symmDiff_lt μ hAm hε
    have hBm : MeasurableSet B := cylinderEvents_le_pi _ hB
    have hB1 : μ B ≤ 1 := prob_le_one
    have hτmem : blockSwap k ∈ finPerm (2 * k) := blockSwap_mem_finPerm k
    have hCcyl : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ E) (Ico k (2 * k))]
        (permute (blockSwap k) ⁻¹' B) :=
      measurableSet_preimage_permute (blockSwap_maps_Iio k) hB
    have hCm : MeasurableSet (permute (blockSwap k) ⁻¹' B) := cylinderEvents_le_pi _ hCcyl
    have hτA : permute (blockSwap k) ⁻¹' A = A := (hAn (2 * k)).2 _ hτmem
    have hmapτ : ∀ S : Set (ℕ → E), MeasurableSet S → μ (permute (blockSwap k) ⁻¹' S) = μ S := by
      intro S hS
      rw [← Measure.map_apply (measurable_permute _) hS,
        hμdef, isExchangeable_infinitePi _ (blockSwap_mem_finitaryPerm k)]
    have hCA : μ ((permute (blockSwap k) ⁻¹' B) ∆ A) < ε := by
      rw [show (permute (blockSwap k) ⁻¹' B) ∆ A
          = permute (blockSwap k) ⁻¹' (B ∆ A) by rw [preimage_symmDiff, hτA],
        hmapτ _ (hBm.symmDiff hAm)]
      exact hBA
    have hCB : μ (permute (blockSwap k) ⁻¹' B) = μ B := hmapτ B hBm
    have hdisj : Disjoint (Iio k) (Ico k (2 * k)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [mem_Iio] at hx
      simp only [mem_Ico] at hx'
      omega
    have hBC : μ (B ∩ permute (blockSwap k) ⁻¹' B) = μ B * μ B := by
      rw [((indep_cylinderEvents_infinitePi (ν := ν) hdisj).indepSet_of_measurableSet hB
        hCcyl).measure_inter_eq_mul, hCB]
    constructor
    · have hsub : A ⊆ (B ∩ permute (blockSwap k) ⁻¹' B)
          ∪ ((B ∆ A) ∪ ((permute (blockSwap k) ⁻¹' B) ∆ A)) := by
        intro x hx
        simp only [mem_union, mem_inter_iff, Set.mem_symmDiff]
        tauto
      have h4 : μ A ≤ μ B * μ B + (ε + ε) := by
        calc μ A ≤ μ ((B ∩ permute (blockSwap k) ⁻¹' B)
              ∪ ((B ∆ A) ∪ ((permute (blockSwap k) ⁻¹' B) ∆ A))) := measure_mono hsub
          _ ≤ μ (B ∩ permute (blockSwap k) ⁻¹' B)
              + μ ((B ∆ A) ∪ ((permute (blockSwap k) ⁻¹' B) ∆ A)) := measure_union_le _ _
          _ ≤ μ B * μ B + (μ (B ∆ A) + μ ((permute (blockSwap k) ⁻¹' B) ∆ A)) := by
              rw [hBC]; gcongr; exact measure_union_le _ _
          _ ≤ μ B * μ B + (ε + ε) := add_le_add_left (add_le_add hBA.le hCA.le) _
      have hsubB : B ⊆ A ∪ (B ∆ A) := by
        intro x hx; simp only [mem_union, Set.mem_symmDiff]; tauto
      have hb : μ B ≤ μ A + ε :=
        (measure_mono hsubB).trans ((measure_union_le _ _).trans (add_le_add_left hBA.le _))
      calc μ A ≤ μ B * μ B + (ε + ε) := h4
        _ ≤ (μ A * μ A + 3 * ε) + (ε + ε) := by
            gcongr; exact mul_self_le_of_le_add hb hA1 hε1
        _ = μ A * μ A + 5 * ε := by ring
    · have hsubA : A ⊆ B ∪ (B ∆ A) := by
        intro x hx; simp only [mem_union, Set.mem_symmDiff]; tauto
      have ha : μ A ≤ μ B + ε :=
        (measure_mono hsubA).trans ((measure_union_le _ _).trans (add_le_add_left hBA.le _))
      have hsubBC : B ∩ permute (blockSwap k) ⁻¹' B ⊆ A ∪ (B ∆ A) := by
        intro x hx; simp only [mem_union, mem_inter_iff, Set.mem_symmDiff] at *; tauto
      have hbb : μ B * μ B ≤ μ A + ε := by
        rw [← hBC]
        exact (measure_mono hsubBC).trans
          ((measure_union_le _ _).trans (add_le_add_left hBA.le _))
      calc μ A * μ A ≤ μ B * μ B + 3 * ε := mul_self_le_of_le_add ha hB1 hε1
        _ ≤ (μ A + ε) + 3 * ε := by gcongr
        _ = μ A + 4 * ε := by ring
  have hsmall : ∀ (δ : ℝ≥0), 0 < δ → ∃ ε : ℝ≥0∞, 0 < ε ∧ ε ≤ 1 ∧ 5 * ε ≤ δ ∧ 4 * ε ≤ δ := by
    intro δ hδ
    refine ⟨min ((δ : ℝ≥0∞) / 5) 1, lt_min (ENNReal.div_pos (by exact_mod_cast hδ.ne') (by simp))
      one_pos, min_le_right _ _, ?_, ?_⟩
    · calc (5 : ℝ≥0∞) * min ((δ : ℝ≥0∞) / 5) 1 ≤ 5 * ((δ : ℝ≥0∞) / 5) := by
            gcongr; exact min_le_left _ _
        _ = δ := ENNReal.mul_div_cancel' (by simp) (by simp)
    · calc (4 : ℝ≥0∞) * min ((δ : ℝ≥0∞) / 5) 1 ≤ 5 * ((δ : ℝ≥0∞) / 5) := by
            gcongr
            · norm_num
            · exact min_le_left _ _
        _ = δ := ENNReal.mul_div_cancel' (by simp) (by simp)
  have hle₁ : μ A ≤ μ A * μ A := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨ε, hε, hε1, h5, -⟩ := hsmall δ hδ
    exact (key ε hε hε1).1.trans (add_le_add_left h5 _)
  have hle₂ : μ A * μ A ≤ μ A := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ ↦ ?_
    obtain ⟨ε, hε, hε1, -, h4⟩ := hsmall δ hδ
    exact (key ε hε hε1).2.trans (add_le_add_left h4 _)
  have heq : μ A * 1 = μ A * μ A := by rw [mul_one]; exact le_antisymm hle₁ hle₂
  by_cases h0 : μ A = 0
  · exact Or.inl h0
  · exact Or.inr (ENNReal.mul_left_cancel h0 (measure_ne_top _ _) heq).symm

theorem mem_trivialOn_symmetricSigmaAlgebra_infinitePi :
    Measure.infinitePi (fun _ : ℕ ↦ ν) ∈ trivialOn (symmetricSigmaAlgebra E) :=
  fun _ hA ↦ measure_symmetric_eq_zero_or_one hA

/-- Product measures are extreme points of the set of exchangeable probability measures. -/
theorem infinitePi_mem_extremePoints :
    Measure.infinitePi (fun _ : ℕ ↦ ν) ∈ (exchangeableSpec E).invariant.extremePoints ℝ≥0∞ :=
  AbstractSpecification.mem_extremePoints_of_mem_trivialOn
    ((mem_exchangeableSpec_invariant_iff _).2 ⟨inferInstance, isExchangeable_infinitePi⟩)
    mem_trivialOn_symmetricSigmaAlgebra_infinitePi

end HewittSavage

end MeasureTheory.GibbsMeasure

end

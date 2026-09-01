/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import GibbsMeasure.Mathlib.Probability.ConditionalProbability
public import GibbsMeasure.Specification.PAKernel
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Georgii, Remark (7.13): the abstract setting behind Chapter 7

Georgii's Remark (7.13) observes that Theorem (7.7) and Theorem (7.12)(a) hold verbatim in the
following generality: `(Ω, 𝓕)` is an arbitrary measurable space, `ι` a countable index set
directed upwards by a partial order, `(𝓣ᵢ)` a decreasing family of sub-σ-algebras of `𝓕` with
`𝓣 = ⨅ i, 𝓣ᵢ`, and `γ` any family of proper probability kernels `γᵢ` from `𝓣ᵢ` to `𝓕`. The set
`𝒢(γ) = 𝒫_γ` of `γ`-invariant probability measures replaces the set of Gibbs measures.

Georgii asks for no consistency between the kernels, and none is used below: invariance of `μ`
is what the arguments consume, not `γᵢ γⱼ = γⱼ`.

## Main definitions

* `AbstractSpecification Ω ι`: the data of Remark (7.13).
* `AbstractSpecification.tail`: the tail σ-algebra `𝓣 = ⨅ i, 𝓣ᵢ`.
* `AbstractSpecification.invariant`: the convex set `𝒢(γ)` of `γ`-invariant probability measures.

## Main results

* `AbstractSpecification.cond_mem_invariant`: Georgii (7.7)(b), conditioning on a tail event of
  positive measure preserves invariance.
* `AbstractSpecification.mem_extremePoints_iff_mem_trivialOn`: Georgii (7.7)(a), an invariant
  probability measure is extreme in `𝒢(γ)` iff it is trivial on the tail σ-algebra.
* `Specification.toAbstract`: every specification is an abstract specification, whose tail
  σ-algebra is `tailSigmaAlgebra S E` and whose invariant set is `𝒢(γ)`.
-/

@[expose] public section

-- Lean 4.34's module system does not unfold non-exposed mathlib defs (e.g. `Kernel.comap`)
-- during `isDefEq`.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

/-! ### Auxiliary lemmas -/

section Aux

variable {Ω : Type*}

/-- An antitone sequence in a complete lattice has the same infimum as each of its tails. -/
lemma iInf_ge_eq_iInf_of_antitone {α : Type*} [CompleteLattice α] {h : ℕ → α} (hh : Antitone h)
    (N : ℕ) : (⨅ n : ℕ, h n) = ⨅ n : {n // N ≤ n}, h n.1 := by
  refine le_antisymm (le_iInf fun n ↦ iInf_le _ n.1) (le_iInf fun n ↦ ?_)
  by_cases hn : N ≤ n
  · simpa using iInf_le (fun k : {k // N ≤ k} ↦ h k.1) ⟨n, hn⟩
  · have hN : (⨅ k : {k // N ≤ k}, h k.1) ≤ h N := by
      simpa using iInf_le (fun k : {k // N ≤ k} ↦ h k.1) ⟨N, le_rfl⟩
    exact hN.trans (hh (le_of_not_ge hn))

lemma antitone_iSup_ge_apply {α : Type*} [CompleteLattice α] (g : ℕ → α) :
    Antitone fun n : ℕ ↦ ⨆ i : ℕ, ⨆ (_ : i ≥ n), g i := fun _ _ hab ↦
  iSup_le fun i ↦ iSup_le fun hib ↦ le_iSup_of_le i (le_iSup_of_le (hab.trans hib) le_rfl)

/-- The `limsup` of functions measurable for an antitone sequence of σ-algebras is measurable for
the infimum of that sequence. -/
lemma measurable_limsup_iInf (mn : ℕ → MeasurableSpace Ω) (hm : Antitone mn) (g : ℕ → Ω → ℝ≥0∞)
    (hg : ∀ n, Measurable[mn n] (g n)) :
    Measurable[iInf mn] fun ω ↦ limsup (fun n ↦ g n ω) atTop := by
  refine (measurable_iInf_iff_forall (mκ := mn)).2 fun N ↦ ?_
  have h_limsup : (fun ω ↦ limsup (fun n ↦ g n ω) atTop) =
      fun ω ↦ ⨅ n : {n // N ≤ n}, ⨆ i : ℕ, ⨆ (_ : i ≥ n.1), g i ω := by
    funext ω
    rw [Filter.limsup_eq_iInf_iSup_of_nat (u := fun n ↦ g n ω)]
    exact iInf_ge_eq_iInf_of_antitone (antitone_iSup_ge_apply (g := fun i ↦ g i ω)) N
  rw [h_limsup]
  refine Measurable.iInf fun n ↦ ?_
  have h_each : ∀ i : {i // i ≥ n.1}, Measurable[mn N] (g i.1) := fun i ↦
    (hg i.1).mono (hm (n.2.trans i.2)) le_rfl
  simpa [iSup_subtype] using Measurable.iSup (f := fun i : {i // i ≥ n.1} ↦ g i.1) h_each

/-- A nonempty countable preorder directed upwards contains a monotone cofinal sequence. -/
lemma exists_monotone_cofinal (ι : Type*) [Preorder ι] [Countable ι] [Nonempty ι]
    [IsDirected ι (· ≤ ·)] : ∃ f : ℕ → ι, Monotone f ∧ ∀ i, ∃ n, i ≤ f n := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  choose g hg₁ hg₂ using fun a b : ι ↦ directed_of (· ≤ ·) a b
  refine ⟨fun n ↦ Nat.rec (e 0) (fun k ih ↦ g ih (e (k + 1))) n,
    monotone_nat_of_le_succ fun n ↦ hg₁ _ _, fun i ↦ ?_⟩
  obtain ⟨n, rfl⟩ := he i
  cases n with
  | zero => exact ⟨0, le_rfl⟩
  | succ k => exact ⟨k + 1, hg₂ _ _⟩

end Aux

/-! ### The abstract framework of Remark (7.13) -/

variable (Ω : Type*) [m : MeasurableSpace Ω] (ι : Type*) [Preorder ι] in
/-- **Georgii, Remark (7.13)**: the abstract setting in which the results of Section 7.1 hold.

A decreasing family `sub` of sub-σ-algebras of `m`, indexed by a preorder `ι`, together with a
consistent family of proper Markov kernels `ker i` from `sub i` to `m`. Consistency is Georgii's
`γᵢ γⱼ = γⱼ` for `i ≤ j`, written exactly as in `IsConsistent`. -/
structure AbstractSpecification where
  /-- The decreasing family `(𝓣ᵢ)` of sub-σ-algebras. -/
  sub : ι → MeasurableSpace Ω
  /-- Each `𝓣ᵢ` is a sub-σ-algebra of the ambient σ-algebra. -/
  sub_le : ∀ i, sub i ≤ m
  /-- The family `(𝓣ᵢ)` is decreasing. -/
  sub_antitone : Antitone sub
  /-- The kernels `γᵢ`, from `(Ω, 𝓣ᵢ)` to `(Ω, 𝓕)`. -/
  ker : ∀ i, Kernel[sub i, m] Ω Ω
  /-- Each `γᵢ` is a probability kernel. -/
  isMarkovKernel : ∀ i, IsMarkovKernel (ker i)
  /-- Each `γᵢ` is proper. -/
  isProper : ∀ i, (ker i).IsProper

namespace AbstractSpecification

variable {Ω ι : Type*} [m : MeasurableSpace Ω] [Preorder ι] (γ : AbstractSpecification Ω ι)

instance instIsMarkovKernel (i : ι) : IsMarkovKernel (γ.ker i) := γ.isMarkovKernel i

lemma measurable_ker (i : ι) : Measurable (γ.ker i) :=
  (γ.ker i).measurable.mono (γ.sub_le i) le_rfl

lemma aemeasurable_ker (i : ι) (μ : Measure Ω) : AEMeasurable (γ.ker i) μ :=
  (γ.measurable_ker i).aemeasurable

/-- The tail σ-algebra `𝓣 = ⨅ i, 𝓣ᵢ`. -/
@[reducible] def tail : MeasurableSpace Ω := ⨅ i, γ.sub i

lemma tail_le_sub (i : ι) : γ.tail ≤ γ.sub i := iInf_le _ i

lemma tail_le [Nonempty ι] : γ.tail ≤ m :=
  (γ.tail_le_sub (Classical.arbitrary ι)).trans (γ.sub_le _)

/-- The set `𝒢(γ) = 𝒫_γ` of `γ`-invariant probability measures. -/
def invariant : Set (Measure Ω) :=
  {μ | IsProbabilityMeasure μ ∧ ∀ i, μ.bind (γ.ker i) = μ}

variable {γ}

lemma isProbabilityMeasure_of_mem_invariant {μ : Measure Ω} (hμ : μ ∈ γ.invariant) :
    IsProbabilityMeasure μ := hμ.1

lemma bind_eq_self_of_mem_invariant {μ : Measure Ω} (hμ : μ ∈ γ.invariant) (i : ι) :
    μ.bind (γ.ker i) = μ := hμ.2 i

/-- Along a cofinal sequence the tail σ-algebra is already reached. -/
lemma tail_eq_iInf_of_cofinal {f : ℕ → ι} (hcof : ∀ i, ∃ n, i ≤ f n) :
    γ.tail = ⨅ n, γ.sub (f n) := by
  refine le_antisymm (le_iInf fun n ↦ γ.tail_le_sub _) (le_iInf fun i ↦ ?_)
  obtain ⟨n, hn⟩ := hcof i
  exact (iInf_le (fun n ↦ γ.sub (f n)) n).trans (γ.sub_antitone hn)

/-! ### Georgii (7.7)(b): conditioning on a tail event -/

/-- Properness lets a `𝓣ᵢ`-measurable event be pulled out of `μ γᵢ`. -/
lemma bind_restrict (i : ι) {A : Set Ω} (hA : MeasurableSet[γ.sub i] A) (μ : Measure Ω) :
    (μ.restrict A).bind (γ.ker i) = (μ.bind (γ.ker i)).restrict A := by
  ext s hs
  have hA' : MeasurableSet A := γ.sub_le i _ hA
  have hproper : ∀ x, γ.ker i x (s ∩ A) = A.indicator 1 x * γ.ker i x s := fun x ↦
    (γ.isProper i).inter_eq_indicator_mul (γ.sub_le i) hs hA x
  calc
    ((μ.restrict A).bind (γ.ker i)) s = ∫⁻ x, γ.ker i x s ∂(μ.restrict A) := by
        simp [Measure.bind_apply hs (γ.aemeasurable_ker i _)]
    _ = ∫⁻ x, A.indicator (fun x ↦ γ.ker i x s) x ∂μ := by
        simpa using (lintegral_indicator (μ := μ) hA' (f := fun x ↦ γ.ker i x s)).symm
    _ = ∫⁻ x, γ.ker i x (s ∩ A) ∂μ := by
        refine lintegral_congr fun x ↦ ?_
        by_cases hx : x ∈ A <;> simp [hproper x, hx]
    _ = (μ.bind (γ.ker i)) (s ∩ A) := by
        simp [Measure.bind_apply (hs.inter hA') (γ.aemeasurable_ker i _)]
    _ = ((μ.bind (γ.ker i)).restrict A) s := by
        simp [Measure.restrict_apply, hs, hA', Set.inter_comm]

/-- **Georgii (7.7)(b)**: conditioning an invariant probability measure on a tail event of
positive measure yields an invariant probability measure. -/
theorem cond_mem_invariant [Nonempty ι] {μ : Measure Ω} (hμ : μ ∈ γ.invariant) {A : Set Ω}
    (hA : MeasurableSet[γ.tail] A) (hA0 : μ A ≠ 0) : cond μ A ∈ γ.invariant := by
  have hprob : IsProbabilityMeasure μ := hμ.1
  have hcond : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hA0
  refine ⟨hcond, fun i ↦ ?_⟩
  have hAi : MeasurableSet[γ.sub i] A := γ.tail_le_sub i _ hA
  calc
    (cond μ A).bind (γ.ker i) = ((μ A)⁻¹ • μ.restrict A).bind (γ.ker i) := rfl
    _ = (μ A)⁻¹ • ((μ.restrict A).bind (γ.ker i)) :=
        Measure.bind_smul ((μ A)⁻¹) (μ.restrict A) (γ.ker i)
    _ = (μ A)⁻¹ • ((μ.bind (γ.ker i)).restrict A) := by rw [bind_restrict i hAi μ]
    _ = cond μ A := by rw [hμ.2 i]; rfl

/-! ### Densities: properness makes `withDensity` commute with `μ ↦ μ γᵢ` -/

lemma lintegral_bind_indicator (i : ι) (μ : Measure[γ.sub i] Ω) (f : Ω → ℝ≥0∞)
    (hf : Measurable[γ.sub i] f) {A : Set Ω} (hA : MeasurableSet A) :
    ∫⁻ x, A.indicator f x ∂(μ.bind (γ.ker i)) = ∫⁻ η, f η * γ.ker i η A ∂μ := by
  have hf_amb : Measurable f := hf.mono (γ.sub_le i) le_rfl
  have hbind := Measure.lintegral_bind (m := μ) (μ := γ.ker i)
    (f := fun x ↦ A.indicator f x) (γ.ker i).measurable.aemeasurable
    (hf_amb.indicator hA).aemeasurable
  have hinner : (fun η ↦ ∫⁻ x, A.indicator f x ∂(γ.ker i η)) = fun η ↦ f η * γ.ker i η A := by
    funext η
    have hrw : (fun x ↦ A.indicator f x) = fun x ↦ f x * A.indicator (1 : Ω → ℝ≥0∞) x := by
      funext x; by_cases hx : x ∈ A <;> simp [hx]
    rw [hrw, (γ.isProper i).lintegral_mul (γ.sub_le i) (measurable_one.indicator hA) hf η]
    simp [lintegral_indicator_one hA]
  rw [hinner] at hbind
  simpa using hbind

lemma withDensity_bind (i : ι) (μ : Measure[γ.sub i] Ω) (f : Ω → ℝ≥0∞)
    (hf : Measurable[γ.sub i] f) :
    (μ.bind (γ.ker i)).withDensity f = (μ.withDensity f).bind (γ.ker i) := by
  ext A hA
  calc
    ((μ.bind (γ.ker i)).withDensity f) A = ∫⁻ x in A, f x ∂(μ.bind (γ.ker i)) :=
        withDensity_apply f hA
    _ = ∫⁻ x, A.indicator f x ∂(μ.bind (γ.ker i)) := by
        simpa using (lintegral_indicator (μ := μ.bind (γ.ker i)) hA (f := f)).symm
    _ = ∫⁻ η, f η * γ.ker i η A ∂μ := lintegral_bind_indicator i μ f hf hA
    _ = ∫⁻ η, γ.ker i η A ∂(μ.withDensity f) := by
        simpa [mul_comm] using (lintegral_withDensity_eq_lintegral_mul (μ := μ) (f := f) hf
          (g := fun η ↦ γ.ker i η A) ((γ.ker i).measurable_coe hA)).symm
    _ = ((μ.withDensity f).bind (γ.ker i)) A := by
        simp [Measure.bind_apply hA (γ.ker i).measurable.aemeasurable]

lemma bind_trim (i : ι) (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    (μ.trim (γ.sub_le i)).bind (γ.ker i) A = μ.bind (γ.ker i) A := by
  have hkerA : Measurable[γ.sub i] fun η ↦ γ.ker i η A := (γ.ker i).measurable_coe hA
  simp [Measure.bind_apply hA (γ.aemeasurable_ker i μ),
    Measure.bind_apply hA (γ.ker i).measurable.aemeasurable,
    lintegral_trim (γ.sub_le i) hkerA]

/-- For invariant `μ`, `ν ≪ μ`, the density of `ν` with respect to `μ` may be chosen
`𝓣ᵢ`-measurable, for every `i`. -/
lemma exists_withDensity_of_absolutelyContinuous (i : ι) {μ ν : Measure Ω} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : μ.bind (γ.ker i) = μ) (hν : ν.bind (γ.ker i) = ν) (hνμ : ν ≪ μ) :
    ∃ g : Ω → ℝ≥0∞, Measurable[γ.sub i] g ∧ μ.withDensity g = ν := by
  set μb : Measure[γ.sub i] Ω := μ.trim (γ.sub_le i) with hμb_def
  set νb : Measure[γ.sub i] Ω := ν.trim (γ.sub_le i) with hνb_def
  have hνbμb : νb ≪ μb := Measure.AbsolutelyContinuous.trim (hμν := hνμ) (γ.sub_le i)
  set g : Ω → ℝ≥0∞ := νb.rnDeriv μb with hg_def
  have hg : Measurable[γ.sub i] g := Measure.measurable_rnDeriv νb μb
  have : IsFiniteMeasure μb := by rw [hμb_def]; infer_instance
  have : IsFiniteMeasure νb := by rw [hνb_def]; infer_instance
  have hwd : μb.withDensity g = νb := Measure.withDensity_rnDeriv_eq (μ := νb) (ν := μb) hνbμb
  have hμb_bind : μb.bind (γ.ker i) = μ := by
    ext A hA; rw [hμb_def, bind_trim i μ hA, hμ]
  have hνb_bind : νb.bind (γ.ker i) = ν := by
    ext A hA; rw [hνb_def, bind_trim i ν hA, hν]
  refine ⟨g, hg, ?_⟩
  calc
    μ.withDensity g = (μb.bind (γ.ker i)).withDensity g := by rw [hμb_bind]
    _ = (μb.withDensity g).bind (γ.ker i) := withDensity_bind i μb g hg
    _ = νb.bind (γ.ker i) := by rw [hwd]
    _ = ν := hνb_bind

/-- **Georgii (7.7)(b)**, density form: the Radon–Nikodym derivative of an invariant measure with
respect to an invariant measure it is absolutely continuous with respect to is a.e. equal to a
tail-measurable function. -/
lemma exists_tail_measurable_rnDeriv [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ i, μ.bind (γ.ker i) = μ) (hν : ∀ i, ν.bind (γ.ker i) = ν) (hνμ : ν ≪ μ) :
    ∃ g : Ω → ℝ≥0∞, Measurable[γ.tail] g ∧ ν.rnDeriv μ =ᵐ[μ] g := by
  obtain ⟨f, hf_mono, hf_cof⟩ := exists_monotone_cofinal ι
  choose g hg hμg using fun n ↦
    exists_withDensity_of_absolutelyContinuous (γ := γ) (f n) (hμ (f n)) (hν (f n)) hνμ
  have hfg : ∀ n, ν.rnDeriv μ =ᵐ[μ] g n := by
    intro n
    have hg_amb : Measurable (g n) := (hg n).mono (γ.sub_le (f n)) le_rfl
    have := Measure.rnDeriv_withDensity (ν := μ) (f := g n) hg_amb
    rw [hμg n] at this
    exact this
  refine ⟨fun ω ↦ limsup (fun n ↦ g n ω) atTop, ?_, ?_⟩
  · rw [tail_eq_iInf_of_cofinal (γ := γ) hf_cof]
    exact measurable_limsup_iInf _ (γ.sub_antitone.comp_monotone hf_mono) g hg
  · have hall : ∀ᵐ ω ∂μ, ∀ n, g n ω = ν.rnDeriv μ ω :=
      ae_all_iff.2 fun n ↦ (hfg n).symm
    filter_upwards [hall] with ω hω
    have : (fun n ↦ g n ω) = fun _ : ℕ ↦ ν.rnDeriv μ ω := funext fun n ↦ hω n
    simp [this]

/-- If `μ` is invariant and trivial on the tail σ-algebra, then any invariant probability measure
absolutely continuous with respect to `μ` equals `μ`. -/
theorem eq_of_absolutelyContinuous [Countable ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {μ ν : Measure Ω} (hμ : μ ∈ γ.invariant) (hν : ν ∈ γ.invariant)
    (htriv : μ ∈ trivialOn γ.tail) (hνμ : ν ≪ μ) : ν = μ := by
  have hμp : IsProbabilityMeasure μ := hμ.1
  have hνp : IsProbabilityMeasure ν := hν.1
  obtain ⟨g, hg_tail, hfg⟩ :=
    exists_tail_measurable_rnDeriv (γ := γ) hμ.2 hν.2 hνμ
  obtain ⟨c, hgc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one γ.tail_le htriv hg_tail
  have hfc : ν.rnDeriv μ =ᵐ[μ] fun _ ↦ c := hfg.trans hgc
  have hrepr : μ.withDensity (ν.rnDeriv μ) = ν :=
    Measure.withDensity_rnDeriv_eq (μ := ν) (ν := μ) hνμ
  have hconst : ν = c • μ := by
    have := withDensity_congr_ae (μ := μ) hfc
    rw [hrepr, withDensity_const] at this
    exact this
  have hc : c = 1 := by
    have := congrArg (fun m : Measure Ω ↦ m (univ : Set Ω)) hconst
    simpa using this.symm
  rw [hconst, hc, one_smul]

/-! ### Georgii (7.7)(a): extremality is tail triviality -/

section ExtremePoints

variable [Nonempty ι]

/-- If an invariant probability measure gives a tail event probability strictly between `0` and
`1`, then it is not an extreme point of `𝒢(γ)`. -/
theorem not_mem_extremePoints_of_tail_prob {μ : Measure Ω} (hμ : μ ∈ γ.invariant) {A : Set Ω}
    (hA : MeasurableSet[γ.tail] A) (hA0 : 0 < μ A) (hA1 : μ A < 1) :
    μ ∉ γ.invariant.extremePoints ℝ≥0∞ := by
  have hμp : IsProbabilityMeasure μ := hμ.1
  have hA' : MeasurableSet A := γ.tail_le _ hA
  have hA0' : μ A ≠ 0 := hA0.ne'
  have hAc0' : μ Aᶜ ≠ 0 := by
    rw [prob_compl_eq_one_sub hA']
    exact (tsub_pos_of_lt hA1).ne'
  have hcondA : cond μ A ∈ γ.invariant := cond_mem_invariant hμ hA hA0'
  have hcondAc : cond μ Aᶜ ∈ γ.invariant :=
    cond_mem_invariant hμ (MeasurableSet.compl hA) hAc0'
  have hcondA_prob : IsProbabilityMeasure (cond μ A) := cond_isProbabilityMeasure hA0'
  have hseg : μ ∈ openSegment ℝ≥0∞ (cond μ A) (cond μ Aᶜ) := by
    refine ⟨μ A, μ Aᶜ, hA0, pos_iff_ne_zero.2 hAc0', prob_add_prob_compl hA', ?_⟩
    have h₁ : (μ A) • cond μ A = μ.restrict A :=
      measure_smul_cond hA0' (measure_ne_top _ _)
    have h₂ : (μ Aᶜ) • cond μ Aᶜ = μ.restrict Aᶜ :=
      measure_smul_cond hAc0' (measure_ne_top _ _)
    rw [h₁, h₂, Measure.restrict_add_restrict_compl hA']
  intro hext
  obtain ⟨-, hleft⟩ := (mem_extremePoints_iff_left (𝕜 := ℝ≥0∞)).1 hext
  have hEq : cond μ A = μ := hleft _ hcondA _ hcondAc hseg
  have : μ A = 1 := by
    rw [← hEq]
    exact cond_apply_self hA0' (measure_ne_top _ _)
  exact hA1.ne this

/-- Extreme points of `𝒢(γ)` are trivial on the tail σ-algebra. -/
theorem mem_trivialOn_of_mem_extremePoints {μ : Measure Ω}
    (hext : μ ∈ γ.invariant.extremePoints ℝ≥0∞) : μ ∈ trivialOn γ.tail := by
  obtain ⟨hμ, -⟩ := (mem_extremePoints (𝕜 := ℝ≥0∞)).1 hext
  have hμp : IsProbabilityMeasure μ := hμ.1
  intro A hA
  rcases eq_or_lt_of_le (prob_le_one (μ := μ) (s := A)) with h1 | hlt
  · exact Or.inr h1
  · by_cases h0 : μ A = 0
    · exact Or.inl h0
    · exact absurd hext
        (not_mem_extremePoints_of_tail_prob hμ hA (pos_iff_ne_zero.2 h0) hlt)

/-- Invariant probability measures trivial on the tail σ-algebra are extreme in `𝒢(γ)`. -/
theorem mem_extremePoints_of_mem_trivialOn [Countable ι] [IsDirected ι (· ≤ ·)] {μ : Measure Ω}
    (hμ : μ ∈ γ.invariant) (htriv : μ ∈ trivialOn γ.tail) :
    μ ∈ γ.invariant.extremePoints ℝ≥0∞ := by
  have hμp : IsProbabilityMeasure μ := hμ.1
  rw [mem_extremePoints_iff_left]
  refine ⟨hμ, ?_⟩
  rintro ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, hab, hsum⟩
  have hν₁p : IsProbabilityMeasure ν₁ := hν₁.1
  have hν₂p : IsProbabilityMeasure ν₂ := hν₂.1
  have hν₁μ : ν₁ ≪ μ := by
    intro s hs
    have hμs : a * ν₁ s + b * ν₂ s = 0 := by
      have := congrArg (fun m : Measure Ω ↦ m s) hsum
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at this
      rw [this]; exact hs
    rcases mul_eq_zero.1 (add_eq_zero.1 hμs).1 with h | h
    · exact absurd h ha.ne'
    · exact h
  exact eq_of_absolutelyContinuous hμ hν₁ htriv hν₁μ

/-- **Georgii, Theorem (7.7)(a)**, in the generality of Remark (7.13): an invariant probability
measure is extreme in `𝒢(γ)` if and only if it is trivial on the tail σ-algebra. -/
theorem mem_extremePoints_iff_mem_trivialOn [Countable ι] [IsDirected ι (· ≤ ·)] {μ : Measure Ω}
    (hμ : μ ∈ γ.invariant) :
    μ ∈ γ.invariant.extremePoints ℝ≥0∞ ↔ μ ∈ trivialOn γ.tail :=
  ⟨mem_trivialOn_of_mem_extremePoints, mem_extremePoints_of_mem_trivialOn hμ⟩

end ExtremePoints

end AbstractSpecification

end MeasureTheory.GibbsMeasure

/-! ### Specifications are abstract specifications -/

namespace Specification

open MeasureTheory MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- Every specification is an abstract specification in the sense of Georgii (7.13), indexed by
the finite volumes, with `𝓣_Λ = cylinderEvents Λᶜ`. -/
noncomputable def toAbstract (γ : Specification S E) :
    AbstractSpecification (S → E) (Finset S) where
  sub Λ := cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)
  sub_le _ := cylinderEvents_le_pi
  sub_antitone _ _ h := cylinderEvents_mono (X := fun _ : S ↦ E) fun _ hx hx' ↦ hx (h hx')
  ker Λ := γ Λ
  isMarkovKernel _ := inferInstance
  isProper := γ.isProper

@[simp] lemma toAbstract_sub (γ : Specification S E) (Λ : Finset S) :
    γ.toAbstract.sub Λ = cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := rfl

@[simp] lemma toAbstract_ker (γ : Specification S E) (Λ : Finset S) :
    γ.toAbstract.ker Λ = γ Λ := rfl

/-- The tail σ-algebra of `γ.toAbstract` is the tail σ-algebra of the configuration space. -/
@[simp] lemma toAbstract_tail (γ : Specification S E) :
    γ.toAbstract.tail = tailSigmaAlgebra S E := rfl

/-- The invariant measures of `γ.toAbstract` are exactly the Gibbs probability measures for `γ`,
i.e. `𝒢(γ)`. -/
lemma toAbstract_invariant (γ : Specification S E) :
    γ.toAbstract.invariant =
      {μ : Measure (S → E) | IsProbabilityMeasure μ ∧ γ.IsGibbsMeasure μ} := by
  ext μ
  constructor
  · rintro ⟨hp, hbind⟩
    have := hp
    exact ⟨hp, (isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) (μ := μ)).2 hbind⟩
  · rintro ⟨hp, hG⟩
    have := hp
    exact ⟨hp, (isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ) (μ := μ)).1 hG⟩

lemma mem_toAbstract_invariant_iff (γ : Specification S E) (μ : Measure (S → E)) :
    μ ∈ γ.toAbstract.invariant ↔ IsProbabilityMeasure μ ∧ γ.IsGibbsMeasure μ := by
  rw [toAbstract_invariant]; rfl

/-- Tail triviality is triviality on the tail σ-algebra of `γ.toAbstract`. -/
lemma isTailTrivial_iff_mem_trivialOn_toAbstract (γ : Specification S E)
    (μ : ProbabilityMeasure (S → E)) :
    IsTailTrivial μ ↔ (μ : Measure (S → E)) ∈ trivialOn γ.toAbstract.tail := Iff.rfl

end Specification

end

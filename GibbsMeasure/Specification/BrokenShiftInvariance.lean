/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Normed.Lp.lpSpace
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.Correlation
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Trivial
public import GibbsMeasure.Mathlib.Probability.Kernel.Composition.MeasureComp
public import GibbsMeasure.Specification.OrderParameters
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Georgii, Lemma (16.28): oscillating correlations break the shift invariance

Let `(E, ℰ)` be standard Borel, `γ` a specification on `ℤ^d → E`, `f ∈ 𝓛` a bounded local
observable and `I ⊆ ℤ^d` an infinite set of sites. Georgii's Lemma (16.28) relates three
statements:

* (i) some `μ ∈ 𝒢_Θ(γ)` is `f`-`I`-oscillating, i.e. satisfies (16.29),
  `limsup_{|i| → ∞, i ∈ I} μ(f · f ∘ θ_i) > liminf_{|i| → ∞, i ∈ I} μ(f · f ∘ θ_i)`;
* (ii) some `ν ∈ ex 𝒢_Θ(γ) \ ex 𝒢(γ)` has `ν(ν(f | 𝓣) ≠ ν(f)) > 0`;
* (iii) some `ν̃ ∈ ex 𝒢(γ) \ 𝒢_Θ(γ)` has `ν̃(f ∘ θ_j) ≠ ν̃(f)` for some site `j`;

and proves (i) ⇒ (ii) ⇒ (iii).

## Main results

* `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_invariantG_isOscillating`: the ergodic
  decomposition half of (i) ⇒ (ii) — if some shift-invariant Gibbs measure is `f`-`I`-oscillating,
  so is one of its ergodic components, i.e. some element of `ex 𝒢_Θ(γ)`.
* `MeasureTheory.GibbsMeasure.correlation_sub_integral_sq_eq`: Georgii's identity
  `ν(f · f ∘ θ_i) − ν(f)² = ν((ν(f | 𝓕_{Λᶜ}) − ν(f)) · f ∘ θ_i)` for a shift-invariant `ν` and a
  finite volume `Λ` outside which `f ∘ θ_i` is measurable — which happens as soon as `Λ` misses
  the localisation volume `Δ − i` of `f ∘ θ_i`
  (`MeasureTheory.GibbsMeasure.measurable_cylinderEvents_compl_comp_shift`), hence for all but
  finitely many `i` (`MeasureTheory.GibbsMeasure.eventually_disjoint_translate`).
* `MeasureTheory.GibbsMeasure.integral_abs_condExp_tail_sub_integral_pos_of_isOscillating`,
  `MeasureTheory.GibbsMeasure.measure_condExp_tail_ne_integral_pos_of_isOscillating`: an
  `f`-`I`-oscillating shift-invariant random field has `ν(f | 𝓣) ≠ ν(f)` on a set of positive
  measure. This is the analytic core of (i) ⇒ (ii) and uses **no** Gibbs property.
* `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_invariantG_notMem_extremePoints_G`:
  **(16.28) (i) ⇒ (ii)**.
* `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_G_integral_comp_shift_ne`:
  **(16.28) (ii) ⇒ (iii)**.
* `MeasureTheory.GibbsMeasure.exists_mem_extremePoints_G_notMem_invariantG_of_isOscillating`:
  **(16.28) (i) ⇒ (iii)**.
* `MeasureTheory.GibbsMeasure.nonempty_extremePoints_invariantG_diff_extremePoints_G`,
  `MeasureTheory.GibbsMeasure.nonempty_extremePoints_G_diff_invariantG`: the two
  set-nonemptiness statements Georgii records in the last sentence of Theorem (16.30).

## Hypotheses actually used

Georgii states (16.28) for a potential `Φ ∈ ℬ_Θ`, that is for the Gibbsian specification `γ^Φ`.
The proof uses only

* the ergodic decomposition of `𝒢_Θ(γ)`, Theorem (14.17): a `(𝓟_Θ, 𝓘)`-kernel takes values in
  `ex 𝒢_Θ(γ)` almost surely (`ae_mem_invariantG_of_isPAKernel_invariantFields`), and represents
  every `μ ∈ 𝒢_Θ(γ)` as `μ = μπ` (`IsPAKernel.bind_eq`);
* the existence of a `(𝒢(γ), 𝓣)`-kernel, Proposition (7.25) (`isPAKernel_gibbsKernel_some`), and
  the identification `ex 𝒢(γ) = 𝒢(γ) ∩ P_𝓣` of Theorem (7.7)
  (`extremePoints_G_eq_inter_trivialOn`);
* the backward martingale convergence theorem and the mean ergodic theorem (14.A5).

None of these needs quasilocality, absolute summability, or even shift invariance of `γ`, so the
statements below are proved for an **arbitrary** specification `γ` on `ℤ^d → E`; `γ = γ^Φ` for
`Φ ∈ ℬ_Θ` is the instance Georgii uses. What *is* needed is `S = ℤ^d` (through
`MeasureTheory.GibbsMeasure.IsOscillating`, the shift group and the Følner cubes), a countable
site set and a standard Borel state space.

Two further hypotheses of Georgii's are not used. Locality of `f` enters only through the
localisation volume `Δ` of the martingale step, so (ii) ⇒ (iii) needs no more than a bounded
measurable `f`. And the conjunct `ν ∉ ex 𝒢(Φ)` of statement (ii) is never used in the proof of
(ii) ⇒ (iii): it *follows* from `ν(ν(f | 𝓣) ≠ ν(f)) > 0`
(`MeasureTheory.GibbsMeasure.notMem_extremePoints_G_of_measure_condExp_tail_ne_integral_pos`), so
it is recorded as a conclusion of (i) ⇒ (ii) rather than assumed in (ii) ⇒ (iii).

Georgii runs the martingale step along the cubes `Δ_n = [−n, n]^d`. Any monotone cofinal sequence
of finite volumes does; we use the exhaustion `exhaustionVolumes` already fixed in
`GibbsMeasure/Specification/Extremal.lean`, whose antitone filtration `exhaustionFiltration` has
infimum the tail σ-algebra `𝓣`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### Georgii's filter `|i| → ∞, i ∈ I` -/

section AtInfinityWithin

variable {ι : Type*}

/-- For finite volumes `Δ` and `Λ`, all but finitely many shifts move `Δ` off `Λ`: the translate
`Δ − i` is disjoint from `Λ` eventually along `|i| → ∞`. This is Georgii's condition
`(Δ − i) ∩ Δ_n = ∅` in the proof of (16.28). -/
lemma eventually_disjoint_translate (Δ Λ : Finset (ι → ℤ)) (I : Set (ι → ℤ)) :
    ∀ᶠ i in atInfinityWithin I, Disjoint (Potential.translate Δ (-i)) Λ := by
  classical
  have hsub : {i : ι → ℤ | ¬ Disjoint (Potential.translate Δ (-i)) Λ} ⊆
      (((Δ ×ˢ Λ).image fun p : (ι → ℤ) × (ι → ℤ) ↦ p.1 - p.2 : Finset (ι → ℤ)) :
        Set (ι → ℤ)) := by
    intro i hi
    obtain ⟨x, hxΔ, hxΛ⟩ := Finset.not_disjoint_iff.1 hi
    rw [Potential.mem_translate, sub_neg_eq_add] at hxΔ
    exact Finset.mem_coe.2 (Finset.mem_image.2
      ⟨(x + i, x), Finset.mem_product.2 ⟨hxΔ, hxΛ⟩, by simp⟩)
  exact (Filter.eventually_cofinite.2
    (((Δ ×ˢ Λ).image fun p : (ι → ℤ) × (ι → ℤ) ↦ p.1 - p.2).finite_toSet.subset
      hsub)).filter_mono inf_le_left

variable [Finite ι]

/-- Georgii's filter `|i| → ∞, i ∈ I` has the countable basis `{tᶜ ∩ I : t finite}`: the site set
`ℤ^d` is countable, so it has only countably many finite subsets. -/
lemma hasCountableBasis_atInfinityWithin (I : Set (ι → ℤ)) :
    (atInfinityWithin I).HasCountableBasis Set.Finite fun t : Set (ι → ℤ) ↦ tᶜ ∩ I :=
  ⟨Filter.hasBasis_cofinite.inf_principal I, Set.Countable.ofPred_finite⟩

/-- Georgii's filter `|i| → ∞, i ∈ I` is countably generated, so the dominated convergence
theorem applies along it. -/
lemma isCountablyGenerated_atInfinityWithin (I : Set (ι → ℤ)) :
    (atInfinityWithin I).IsCountablyGenerated :=
  (hasCountableBasis_atInfinityWithin I).isCountablyGenerated

end AtInfinityWithin

/-! ### Correlations of bounded observables -/

section Correlations

variable {ι E : Type*} [MeasurableSpace E] {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}

/-- A shifted bounded measurable observable is integrable against any finite measure. -/
lemma integrable_comp_shift (hf : Measurable ⇑f) (ν : Measure ((ι → ℤ) → E)) [IsFiniteMeasure ν]
    (i : ι → ℤ) : Integrable (fun ω ↦ ⇑f ((shift E i).toFun ω)) ν :=
  .of_bound (hf.comp (shift E i).measurable_toFun).aestronglyMeasurable ‖f‖
    (.of_forall fun _ ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f _)

/-- The correlation integrand `ω ↦ f ω · f (θ_i ω)` of a bounded measurable observable is
integrable against any finite measure. -/
lemma integrable_mul_comp_shift (hf : Measurable ⇑f) (ν : Measure ((ι → ℤ) → E))
    [IsFiniteMeasure ν] (i : ι → ℤ) :
    Integrable (fun ω ↦ ⇑f ω * ⇑f ((shift E i).toFun ω)) ν :=
  (integrable_comp_shift hf ν i).bdd_mul hf.aestronglyMeasurable
    (.of_forall fun ω ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f ω)

/-- The correlation `ω ↦ ∫ f · f ∘ θ_i dκ(ω)` of a bounded measurable observable is a measurable
function of the boundary condition `ω`, for any s-finite kernel `κ`. -/
lemma measurable_correlation_kernel {κ : Kernel ((ι → ℤ) → E) ((ι → ℤ) → E)} [IsSFiniteKernel κ]
    (hf : Measurable ⇑f) (i : ι → ℤ) : Measurable fun ω ↦ correlation f (κ ω) i := by
  have hg : Measurable fun x : (ι → ℤ) → E ↦ ⇑f x * ⇑f ((shift E i).toFun x) :=
    hf.mul (hf.comp (shift E i).measurable_toFun)
  exact ((hg.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'
    (κ := κ)).measurable

end Correlations

/-! ### Georgii (16.28)(i): some *ergodic* Gibbs measure already oscillates

The ergodic decomposition theorem (14.17) writes `μ ∈ 𝒢_Θ(γ)` as `μ = μπ` for a `(𝓟_Θ, 𝓘)`-kernel
`π` taking its values in `ex 𝒢_Θ(γ)` almost surely. If none of these values oscillated, the
correlations `π(· | ω)(f · f ∘ θ_i)` would converge along `|i| → ∞, i ∈ I`, and dominated
convergence — legitimate because Georgii's filter is countably generated — would make the
correlations of `μ` converge too. -/

section ErgodicComponent

variable {ι E : Type*} [Finite ι] [Nonempty ι] [MeasurableSpace E] [StandardBorelSpace E]
  {γ : Specification (ι → ℤ) E} {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {I : Set (ι → ℤ)}
  {μ : Measure ((ι → ℤ) → E)}

/-- **Georgii, Lemma (16.28), the ergodic decomposition step.** If some shift-invariant Gibbs
measure `μ` is `f`-`I`-oscillating, then so is one of its ergodic components, i.e. some
`ν ∈ ex 𝒢_Θ(γ)`.

Georgii phrases this as "there exists `ν ∈ ex 𝒢_Θ(Φ)` such that `lim_{|i| → ∞, i ∈ I} ν(f f∘θ_i)`
does not exist"; for a uniformly bounded family, non-existence of the limit is exactly
`MeasureTheory.GibbsMeasure.IsOscillating`. -/
theorem exists_mem_extremePoints_invariantG_isOscillating (hI : I.Infinite)
    (hf : Measurable ⇑f) (hμ : μ ∈ invariantG γ (shiftGroup (ι → ℤ) E))
    (hosc : IsOscillating I f μ) :
    ∃ ν ∈ (invariantG γ (shiftGroup (ι → ℤ) E)).extremePoints ℝ≥0∞, IsOscillating I f ν := by
  classical
  set Θ : Subgroup (Transformation (ι → ℤ) E) := shiftGroup (ι → ℤ) E
  have : IsProbabilityMeasure μ := hμ.1.1
  have hne : (atInfinityWithin I).NeBot := atInfinityWithin_neBot hI
  have hcg : (atInfinityWithin I).IsCountablyGenerated := isCountablyGenerated_atInfinityWithin I
  by_contra hcon
  push Not at hcon
  obtain ⟨π, hmark, hπ⟩ :=
    exists_isPAKernel_invariantFields_shiftGroup_int (E := E) (ι := ι) ⟨μ, hμ.2⟩
  have hle : invariantEvents Θ ≤ MeasurableSpace.pi := MeasurableSpace.smulInvariants_le
  have hΘ := shiftGroup_exists_disjoint_sites_preimage (E := E) (S := ι → ℤ)
  -- The kernel takes extreme shift-invariant Gibbs measures as values, almost surely.
  have haeext : ∀ᵐ ω ∂μ, π ω ∈ (invariantG γ Θ).extremePoints ℝ≥0∞ := by
    rw [extremePoints_invariantG hΘ]
    filter_upwards [ae_mem_invariantG_of_isPAKernel_invariantFields hΘ hπ hμ,
      hπ.ae_mem_extremePoints hle (fun _ ↦ isProbabilityMeasure_of_mem_invariantFields)
        measurableSet_invariantFields extremePoints_invariantFields_eq_inter_trivialOn hμ.2]
      with ω h1 h2
    exact ⟨h1, h2⟩
  -- View `π` as a kernel for the ambient σ-algebra, so that `Measure.integral_bind` applies.
  set κ : Kernel ((ι → ℤ) → E) ((ι → ℤ) → E) := π.comap id (measurable_id'' hle) with hκdef
  have hκπ : ∀ ω, κ ω = π ω := fun ω ↦ by rw [hκdef, Kernel.comap_apply, id_eq]
  have : IsMarkovKernel κ := ⟨fun ω ↦ by rw [hκπ ω]; infer_instance⟩
  have hbind : μ.bind ⇑κ = μ := by
    rw [show (⇑κ : ((ι → ℤ) → E) → Measure ((ι → ℤ) → E)) = ⇑π from funext hκπ]
    exact hπ.bind_eq hle hμ.2
  -- The barycentre identity for the correlations.
  have hbary : ∀ i, correlation f μ i = ∫ ω, correlation f (π ω) i ∂μ := by
    intro i
    have hint : Integrable (fun x ↦ ⇑f x * ⇑f ((shift E i).toFun x)) (μ.bind ⇑κ) := by
      rw [hbind]; exact integrable_mul_comp_shift hf μ i
    have h := Measure.integral_bind (κ := κ) hint
    rw [hbind] at h
    simp only [hκπ] at h
    exact h
  -- The limit function; measurable because the filter has a countable basis of countable sets.
  set L : ((ι → ℤ) → E) → ℝ := fun ω ↦ Filter.limsup (correlation f (π ω)) (atInfinityWithin I)
  have hmeas : ∀ i, Measurable fun ω ↦ correlation f (π ω) i := by
    intro i
    simpa only [hκπ] using measurable_correlation_kernel (κ := κ) hf i
  have hLmeas : Measurable L :=
    Measurable.limsup' hmeas (hasCountableBasis_atInfinityWithin I) fun _ ↦ Set.to_countable _
  -- Each ergodic component has a genuine limit.
  have htend : ∀ᵐ ω ∂μ, Tendsto (correlation f (π ω)) (atInfinityWithin I) (𝓝 (L ω)) := by
    filter_upwards [haeext] with ω hω
    have : IsProbabilityMeasure (π ω) := (extremePoints_subset hω).1.1
    have hb1 : (atInfinityWithin I).IsBoundedUnder (· ≤ ·) (correlation f (π ω)) :=
      isBoundedUnder_of ⟨‖f‖ * ‖f‖, fun i ↦ (abs_le.1 (abs_correlation_le f (π ω) i)).2⟩
    have hb2 : (atInfinityWithin I).IsBoundedUnder (· ≥ ·) (correlation f (π ω)) :=
      isBoundedUnder_of ⟨-(‖f‖ * ‖f‖), fun i ↦ (abs_le.1 (abs_correlation_le f (π ω) i)).1⟩
    have hnot : Filter.limsup (correlation f (π ω)) (atInfinityWithin I)
        ≤ Filter.liminf (correlation f (π ω)) (atInfinityWithin I) := not_lt.1 (hcon _ hω)
    exact tendsto_of_liminf_eq_limsup (le_antisymm (Filter.liminf_le_limsup hb1 hb2) hnot) rfl
      hb1 hb2
  -- Dominated convergence along Georgii's filter.
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := atInfinityWithin I) (F := fun i ω ↦ correlation f (π ω) i) (f := L)
    (bound := fun _ ↦ ‖f‖ * ‖f‖)
    (.of_forall fun i ↦ (hmeas i).aestronglyMeasurable)
    (.of_forall fun i ↦ .of_forall fun ω ↦ by
      have : IsProbabilityMeasure (π ω) := hmark.isProbabilityMeasure ω
      rw [Real.norm_eq_abs]; exact abs_correlation_le f (π ω) i)
    (integrable_const _) htend
  have hdct' : Tendsto (correlation f μ) (atInfinityWithin I) (𝓝 (∫ ω, L ω ∂μ)) :=
    hdct.congr fun i ↦ (hbary i).symm
  exact absurd hosc (by rw [IsOscillating, hdct'.liminf_eq, hdct'.limsup_eq]; exact lt_irrefl _)

end ErgodicComponent

/-! ### Correlations against the conditional expectation outside a finite volume

Georgii's identity in the proof of (16.28): if `f ∘ θ_i` is `𝓕_{Λᶜ}`-measurable, then pulling it
out of the conditional expectation gives

`ν(f · f ∘ θ_i) − ν(f)² = ν((ν(f | 𝓕_{Λᶜ}) − ν(f)) · f ∘ θ_i)`

for every shift-invariant `ν`. Georgii takes `Λ = Δ_n = [−n, n]^d` with `(Δ − i) ∩ Δ_n = ∅`, where
`Δ` is the localisation volume of `f`. No Gibbs property is involved. -/

section CondExpBound

variable {ι E : Type*} [MeasurableSpace E] {Δ Λ : Finset (ι → ℤ)}
  {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {ν : Measure ((ι → ℤ) → E)} [IsProbabilityMeasure ν]

/-- The shifted observable `f ∘ θ_i` is measurable for the exterior σ-algebra `𝓕_{Λᶜ}` as soon as
the volume `Λ` is disjoint from the translate `Δ − i` of the localisation volume of `f`. -/
lemma measurable_cylinderEvents_compl_comp_shift (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ)
    {i : ι → ℤ} (hi : Disjoint (Potential.translate Δ (-i)) Λ) :
    Measurable[cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]
      fun ω ↦ ⇑f ((shift E i).toFun ω) := by
  have hsub : ((Potential.translate Δ (-i) : Finset (ι → ℤ)) : Set (ι → ℤ))
      ⊆ ((Λ : Set (ι → ℤ))ᶜ) := fun x hx hxΛ ↦
    Finset.disjoint_left.1 hi (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hxΛ)
  exact (mem_localFunctionsOn.1 (precomp_shift_mem_localFunctionsOn hf i)).mono
    (cylinderEvents_mono hsub) le_rfl

/-- **Georgii's identity in the proof of (16.28).** For a shift-invariant random field `ν`, a
bounded measurable observable `f` and a finite volume `Λ` for which `f ∘ θ_i` is
`𝓕_{Λᶜ}`-measurable,

`ν(f · f ∘ θ_i) − ν(f)² = ν((ν(f | 𝓕_{Λᶜ}) − ν(f)) · f ∘ θ_i)`.

The proof is the pull-out property of the conditional expectation together with the shift
invariance `ν(f ∘ θ_i) = ν(f)`. -/
theorem correlation_sub_integral_sq_eq (hf : Measurable ⇑f)
    (hν : ν ∈ invariantFields (shiftGroup (ι → ℤ) E)) {i : ι → ℤ}
    (hgm : Measurable[cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]
      fun ω ↦ ⇑f ((shift E i).toFun ω)) :
    correlation f ν i - (∫ ω, ⇑f ω ∂ν) ^ 2
      = ∫ ω, ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
          - ∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω) ∂ν := by
  have hm : (cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ))
      ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hsf : SigmaFinite (ν.trim hm) := by infer_instance
  have hgbdd : ∀ ω, ‖⇑f ((shift E i).toFun ω)‖ ≤ ‖f‖ := fun _ ↦
    lp.norm_apply_le_norm ENNReal.top_ne_zero f _
  have hfint : Integrable ⇑f ν := lp.integrable_of_measurable hf ν
  have hgint : Integrable (fun ω ↦ ⇑f ((shift E i).toFun ω)) ν := integrable_comp_shift hf ν i
  have hprod : Integrable (⇑f * fun ω ↦ ⇑f ((shift E i).toFun ω)) ν :=
    integrable_mul_comp_shift hf ν i
  have hcond : Integrable ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E)
      ((Λ : Set (ι → ℤ))ᶜ)]) * fun ω ↦ ⇑f ((shift E i).toFun ω)) ν :=
    integrable_condExp.mul_bdd (hgm.mono hm le_rfl).aestronglyMeasurable (.of_forall hgbdd)
  -- The mean of the shifted observable is the mean of the observable.
  have hshift : ∫ ω, ⇑f ((shift E i).toFun ω) ∂ν = ∫ ω, ⇑f ω ∂ν := by
    have hmp : MeasurePreserving (shift E i).toFun ν ν :=
      (mem_invariantFields_shiftGroup.1 hν).2 i
    have h := integral_map (φ := (shift E i).toFun) (f := (⇑f : ((ι → ℤ) → E) → ℝ))
      hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
    rw [hmp.map_eq] at h
    exact h.symm
  -- Pulling `f ∘ θ_i` out of the conditional expectation.
  have hpull : ∫ ω, (⇑f * fun ω ↦ ⇑f ((shift E i).toFun ω)) ω ∂ν
      = ∫ ω, ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)])
          * fun ω ↦ ⇑f ((shift E i).toFun ω)) ω ∂ν := by
    rw [← integral_condExp (f := ⇑f * fun ω ↦ ⇑f ((shift E i).toFun ω)) hm]
    exact integral_congr_ae
      (condExp_mul_of_stronglyMeasurable_right hgm.stronglyMeasurable hprod hfint)
  symm
  calc ∫ ω, ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
        - ∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω) ∂ν
      = ∫ ω, (((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)])
          * fun ω ↦ ⇑f ((shift E i).toFun ω)) ω
          - (∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω)) ∂ν := by
        refine integral_congr_ae (.of_forall fun ω ↦ ?_)
        simp only [Pi.mul_apply]; ring
    _ = ∫ ω, ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)])
          * fun ω ↦ ⇑f ((shift E i).toFun ω)) ω ∂ν
          - ∫ ω, (∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω) ∂ν :=
        integral_sub hcond (hgint.const_mul _)
    _ = correlation f ν i - (∫ ω, ⇑f ω ∂ν) ^ 2 := by
        rw [← hpull, integral_const_mul, hshift]
        simp only [correlation, Pi.mul_apply, sq]

/-- The correlation of a bounded observable is within `‖f‖ · ν|ν(f | 𝓕_{Λᶜ}) − ν(f)|` of the
square of its mean, for every volume `Λ` making `f ∘ θ_i` measurable outside it. -/
theorem abs_correlation_sub_integral_sq_le (hf : Measurable ⇑f)
    (hν : ν ∈ invariantFields (shiftGroup (ι → ℤ) E)) {i : ι → ℤ}
    (hgm : Measurable[cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]
      fun ω ↦ ⇑f ((shift E i).toFun ω)) :
    |correlation f ν i - (∫ ω, ⇑f ω ∂ν) ^ 2|
      ≤ ‖f‖ * ∫ ω, |(ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
          - ∫ x, ⇑f x ∂ν| ∂ν := by
  have hm : (cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ))
      ≤ MeasurableSpace.pi := cylinderEvents_le_pi
  have hgbdd : ∀ ω, ‖⇑f ((shift E i).toFun ω)‖ ≤ ‖f‖ := fun _ ↦
    lp.norm_apply_le_norm ENNReal.top_ne_zero f _
  have hhint : Integrable (fun ω ↦
      (ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
        - ∫ x, ⇑f x ∂ν) ν := integrable_condExp.sub (integrable_const _)
  have hhg : Integrable (fun ω ↦
      ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
        - ∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω)) ν :=
    hhint.mul_bdd (hgm.mono hm le_rfl).aestronglyMeasurable (.of_forall hgbdd)
  rw [correlation_sub_integral_sq_eq hf hν hgm]
  calc |∫ ω, ((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
        - ∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω) ∂ν|
      ≤ ∫ ω, |((ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
          - ∫ x, ⇑f x ∂ν) * ⇑f ((shift E i).toFun ω)| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ ω, |(ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
          - ∫ x, ⇑f x ∂ν| * ‖f‖ ∂ν := by
        refine integral_mono hhg.abs (hhint.abs.mul_const _) fun ω ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _) ▸ hgbdd ω) (abs_nonneg _)
    _ = ‖f‖ * ∫ ω, |(ν[⇑f | cylinderEvents (X := fun _ : (ι → ℤ) ↦ E) ((Λ : Set (ι → ℤ))ᶜ)]) ω
          - ∫ x, ⇑f x ∂ν| ∂ν := by rw [integral_mul_const]; ring

end CondExpBound

/-! ### Backward martingale convergence to the tail σ-algebra -/

section TailLimit

variable {ι E : Type*} [Finite ι] [MeasurableSpace E]

/-- **Backward martingale convergence, integral form.** Along the exhaustion of `ℤ^d` by finite
volumes, `ν|ν(f | 𝓕_{Λ_nᶜ}) − c| → ν|ν(f | 𝓣) − c|` for every real `c`. This is Georgii's last
step in the proof of (16.28)(i) ⇒ (ii). -/
lemma tendsto_integral_abs_condExp_exhaustionFiltration_sub
    (f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞) (ν : Measure ((ι → ℤ) → E))
    [IsProbabilityMeasure ν] (c : ℝ) :
    Tendsto (fun n ↦ ∫ ω, |(ν[⇑f | exhaustionFiltration (ι → ℤ) E n]) ω - c| ∂ν) atTop
      (𝓝 (∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - c| ∂ν)) := by
  have hae : ∀ᵐ ω ∂ν, Tendsto (fun n ↦ |(ν[⇑f | exhaustionFiltration (ι → ℤ) E n]) ω - c|) atTop
      (𝓝 |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - c|) := by
    have h := tendsto_ae_condExp_of_antitone (μ := ν) (⇑f) antitone_exhaustionFiltration
      exhaustionFiltration_le_pi
    rw [iInf_exhaustionFiltration] at h
    filter_upwards [h] with ω hω
    exact (hω.sub_const c).abs
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ ↦ ‖f‖ + |c|) (.of_forall fun n ↦ ?_) (.of_forall fun n ↦ ?_)
    (integrable_const _) hae
  · have hmeas : Measurable fun ω ↦ (ν[⇑f | exhaustionFiltration (ι → ℤ) E n]) ω - c :=
      (stronglyMeasurable_condExp.mono
        (exhaustionFiltration_le_pi n)).measurable.sub measurable_const
    exact hmeas.norm.aestronglyMeasurable
  · filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (μ := ν)
      (m := exhaustionFiltration (ι → ℤ) E n) (f := ⇑f) (R := ‖f‖)
      (.of_forall fun ω ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f ω)] with ω hω
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (add_le_add (by rwa [Real.norm_eq_abs] at hω) le_rfl)

end TailLimit

/-! ### An oscillating shift-invariant random field is not tail-trivial along `f`

This is the analytic core of Georgii's (16.28)(i) ⇒ (ii). It uses no Gibbs property: only shift
invariance of `ν`, boundedness and locality of `f`, and the backward martingale convergence
theorem. -/

section Oscillation

variable {ι E : Type*} [Finite ι] [MeasurableSpace E] {Δ : Finset (ι → ℤ)}
  {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞} {I : Set (ι → ℤ)} {ν : Measure ((ι → ℤ) → E)}

/-- **Georgii, Lemma (16.28), the martingale step.** An `f`-`I`-oscillating shift-invariant random
field satisfies `ν|ν(f | 𝓣) − ν(f)| > 0`.

If that integral vanished, Georgii's bound
`|ν(f · f ∘ θ_i) − ν(f)²| ≤ ‖f‖ · ν|ν(f | 𝓕_{Λ_nᶜ}) − ν(f)|` — valid for all large `|i|` — together
with backward martingale convergence would force `ν(f · f ∘ θ_i) → ν(f)²`, so that the `limsup`
and the `liminf` of (16.29) would agree. -/
theorem integral_abs_condExp_tail_sub_integral_pos_of_isOscillating (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ)
    (hν : ν ∈ invariantFields (shiftGroup (ι → ℤ) E)) (hosc : IsOscillating I f ν) :
    0 < ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν := by
  have hprob : IsProbabilityMeasure ν := hν.1
  have hne : (atInfinityWithin I).NeBot := atInfinityWithin_neBot hI
  have hfm : Measurable ⇑f := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  by_contra hcon
  push Not at hcon
  have hzero : ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν = 0 :=
    le_antisymm hcon (integral_nonneg fun _ ↦ abs_nonneg _)
  have hlim : Tendsto (fun n ↦ ‖f‖ *
      ∫ ω, |(ν[⇑f | exhaustionFiltration (ι → ℤ) E n]) ω - ∫ x, ⇑f x ∂ν| ∂ν) atTop (𝓝 0) := by
    have h := (tendsto_integral_abs_condExp_exhaustionFiltration_sub f ν
      (∫ x, ⇑f x ∂ν)).const_mul ‖f‖
    rwa [hzero, mul_zero] at h
  have htend : Tendsto (correlation f ν) (atInfinityWithin I) (𝓝 ((∫ x, ⇑f x ∂ν) ^ 2)) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
    have hFn : exhaustionFiltration (ι → ℤ) E n
        = cylinderEvents (X := fun _ : (ι → ℤ) ↦ E)
            ((exhaustionVolumes (S := ι → ℤ) n : Set (ι → ℤ))ᶜ) := rfl
    rw [hFn] at hn
    filter_upwards [eventually_disjoint_translate Δ (exhaustionVolumes (S := ι → ℤ) n) I]
      with i hi
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (abs_correlation_sub_integral_sq_le hfm hν
      (measurable_cylinderEvents_compl_comp_shift hf hi)) hn
  exact absurd hosc (by rw [IsOscillating, htend.liminf_eq, htend.limsup_eq]; exact lt_irrefl _)

/-- **Georgii, Lemma (16.28)(ii), the conclusion `ν(ν(f | 𝓣) ≠ ν(f)) > 0`** for an
`f`-`I`-oscillating shift-invariant random field. -/
theorem measure_condExp_tail_ne_integral_pos_of_isOscillating (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ)
    (hν : ν ∈ invariantFields (shiftGroup (ι → ℤ) E)) (hosc : IsOscillating I f ν) :
    0 < ν {ω | (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω ≠ ∫ x, ⇑f x ∂ν} := by
  have hprob : IsProbabilityMeasure ν := hν.1
  rw [pos_iff_ne_zero]
  intro hzero
  have hae : ∀ᵐ ω ∂ν, (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω = ∫ x, ⇑f x ∂ν := ae_iff.2 hzero
  have h : ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν = 0 := by
    rw [integral_congr_ae (g := fun _ : (ι → ℤ) → E ↦ (0 : ℝ))
      (hae.mono fun ω hω ↦ by rw [hω, sub_self, abs_zero]), integral_zero]
  exact absurd h
    (integral_abs_condExp_tail_sub_integral_pos_of_isOscillating hI hf hν hosc).ne'

end Oscillation

/-! ### Georgii, Lemma (16.28)(i) ⇒ (ii) -/

section ImpliesTwo

variable {ι E : Type*} [Finite ι] [Nonempty ι] [MeasurableSpace E] [StandardBorelSpace E]
  {γ : Specification (ι → ℤ) E} {Δ : Finset (ι → ℤ)} {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
  {I : Set (ι → ℤ)} {μ : Measure ((ι → ℤ) → E)}

omit [Nonempty ι] [StandardBorelSpace E] in
/-- A Gibbs measure whose conditional expectation of `f` given the tail is not almost surely
constant is not extreme in `𝒢(γ)`: extremality is tail-triviality, Georgii's Theorem (7.7). -/
lemma notMem_extremePoints_G_of_measure_condExp_tail_ne_integral_pos {ν : Measure ((ι → ℤ) → E)}
    (hν : 0 < ν {ω | (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω ≠ ∫ x, ⇑f x ∂ν}) :
    ν ∉ (G γ).extremePoints ℝ≥0∞ := by
  intro hmem
  have hνG : ν ∈ G γ := extremePoints_subset hmem
  have : IsProbabilityMeasure ν := hνG.1
  have hmem' : ν ∈ G γ ∩ trivialOn (tailSigmaAlgebra (ι → ℤ) E) := by
    rw [extremePoints_G_eq_inter_trivialOn γ] at hmem; exact hmem
  have h := condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
    (tailSigmaAlgebra_le_pi (S := ι → ℤ) (E := E)) hmem'.2 ⇑f
  exact absurd (ae_iff.1 h) hν.ne'

/-- **Georgii, Lemma (16.28), (i) ⇒ (ii).** If some shift-invariant Gibbs measure is
`f`-`I`-oscillating for an infinite `I`, then there is a measure `ν ∈ ex 𝒢_Θ(γ) \ ex 𝒢(γ)` with
`ν(ν(f | 𝓣) ≠ ν(f)) > 0`. -/
theorem exists_mem_extremePoints_invariantG_notMem_extremePoints_G (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ) (hμ : μ ∈ invariantG γ (shiftGroup (ι → ℤ) E))
    (hosc : IsOscillating I f μ) :
    ∃ ν ∈ (invariantG γ (shiftGroup (ι → ℤ) E)).extremePoints ℝ≥0∞,
      ν ∉ (G γ).extremePoints ℝ≥0∞ ∧
      0 < ν {ω | (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω ≠ ∫ x, ⇑f x ∂ν} := by
  have hfm : Measurable ⇑f := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  obtain ⟨ν, hνex, hνosc⟩ := exists_mem_extremePoints_invariantG_isOscillating hI hfm hμ hosc
  have hpos := measure_condExp_tail_ne_integral_pos_of_isOscillating hI hf
    (extremePoints_subset hνex).2 hνosc
  exact ⟨ν, hνex, notMem_extremePoints_G_of_measure_condExp_tail_ne_integral_pos hpos, hpos⟩

/-- **Georgii, Theorem (16.30), last sentence, first half:** if some `f`-`I`-oscillating
shift-invariant Gibbs measure exists, then `ex 𝒢_Θ(γ) \ ex 𝒢(γ) ≠ ∅`. -/
theorem nonempty_extremePoints_invariantG_diff_extremePoints_G (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ) (hμ : μ ∈ invariantG γ (shiftGroup (ι → ℤ) E))
    (hosc : IsOscillating I f μ) :
    ((invariantG γ (shiftGroup (ι → ℤ) E)).extremePoints ℝ≥0∞ \
      (G γ).extremePoints ℝ≥0∞).Nonempty := by
  obtain ⟨ν, hνex, hνnot, -⟩ :=
    exists_mem_extremePoints_invariantG_notMem_extremePoints_G hI hf hμ hosc
  exact ⟨ν, hνex, hνnot⟩

end ImpliesTwo

/-! ### Georgii, Lemma (16.28)(ii) ⇒ (iii)

If `ν ∈ ex 𝒢_Θ(γ)` had `ν(f ∘ θ_j | 𝓣) = ν(f | 𝓣)` for every site `j`, then averaging over a
Følner sequence of cubes and using the mean ergodic theorem (14.A5) together with the ergodicity
of `ν` would give `ν(f | 𝓣) = ν(f)` almost surely. So some site `j` separates the two conditional
expectations, and the `(𝒢(γ), 𝓣)`-kernel of Proposition (7.25) turns this into an *extreme* Gibbs
measure which is not shift invariant. -/

section ImpliesThree

variable {ι E : Type*} [Finite ι] [Nonempty ι] [MeasurableSpace E] [StandardBorelSpace E]
  {γ : Specification (ι → ℤ) E} {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
  {ν : Measure ((ι → ℤ) → E)}

attribute [local instance] shiftAddAction measurableConstVAdd_shift

omit [Nonempty ι] [StandardBorelSpace E] in
/-- **The ergodic step of Georgii (16.28)(ii) ⇒ (iii).** If `ν` is an ergodic shift-invariant
random field and `ν(f ∘ θ_j | 𝓣) = ν(f | 𝓣)` almost surely for every site `j`, then
`ν(f | 𝓣) = ν(f)` almost surely.

The Cesàro averages `R_n f = |Λ_n|⁻¹ ∑_{j ∈ Λ_n} f ∘ θ_j` over a Følner sequence of cubes have
`ν(R_n f | 𝓣) = ν(f | 𝓣)` and converge in `L¹` to `ν(f | 𝓘) = ν(f)`, and the conditional
expectation is an `L¹` contraction. -/
theorem condExp_tail_ae_eq_integral_of_forall_condExp_comp_shift (hf : Measurable ⇑f)
    (hν : ν ∈ invariantFields (shiftGroup (ι → ℤ) E))
    (herg : ν ∈ trivialOn (invariantEvents (shiftGroup (ι → ℤ) E)))
    (hj : ∀ j : ι → ℤ, (ν[fun ω ↦ ⇑f ((shift E j).toFun ω) | tailSigmaAlgebra (ι → ℤ) E])
      =ᵐ[ν] ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) :
    (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) =ᵐ[ν] fun _ ↦ ∫ x, ⇑f x ∂ν := by
  classical
  have := Fintype.ofFinite ι
  have hprob : IsProbabilityMeasure ν := hν.1
  have : VAddInvariantMeasure (ι → ℤ) ((ι → ℤ) → E) ν :=
    (mem_invariantFields_shiftGroup_iff_vaddInvariantMeasure.1 hν).2
  have h𝓣 : (tailSigmaAlgebra (ι → ℤ) E) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := ι → ℤ) (E := E)
  have : SigmaFinite (ν.trim h𝓣) := by infer_instance
  have hbdd : ∀ ω, |⇑f ω| ≤ ‖f‖ := fun ω ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f ω
  have hfint : Integrable ⇑f ν := lp.integrable_of_measurable hf ν
  -- The Følner sequence of cubes.
  obtain ⟨F, C, hFmono, hF0, hFol, -, -, -⟩ := exists_monotone_regular_foelner_cube (ι := ι)
  have hFne : ∀ n, (F n).Nonempty := fun n ↦ hF0.mono (hFmono (Nat.zero_le n))
  -- The averages and their conditional expectation given the tail.
  have hRint : ∀ n, Integrable
      (fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω)) ν := fun n ↦
    integrable_inv_card_smul_sum_vadd hf hbdd (F n)
  have hRcond : ∀ n, (ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) |
      tailSigmaAlgebra (ι → ℤ) E]) =ᵐ[ν] ν[⇑f | tailSigmaAlgebra (ι → ℤ) E] := by
    intro n
    have hfun : (fun ω : (ι → ℤ) → E ↦ ∑ i ∈ F n, ⇑f (i +ᵥ ω))
        = ∑ i ∈ F n, fun ω : (ι → ℤ) → E ↦ ⇑f (i +ᵥ ω) := by
      funext ω; rw [Finset.sum_apply]
    have hsum : (ν[fun ω ↦ ∑ i ∈ F n, ⇑f (i +ᵥ ω) | tailSigmaAlgebra (ι → ℤ) E])
        =ᵐ[ν] fun ω ↦ ∑ i ∈ F n,
          (ν[fun ω ↦ ⇑f (i +ᵥ ω) | tailSigmaAlgebra (ι → ℤ) E]) ω := by
      rw [hfun]
      filter_upwards [condExp_finsetSum (μ := ν) (s := F n) (f := fun i ω ↦ ⇑f (i +ᵥ ω))
        (fun i _ ↦ integrable_comp_vadd hf hbdd i) (tailSigmaAlgebra (ι → ℤ) E)] with ω hω
      rw [hω, Finset.sum_apply]
    have hall : ∀ᵐ ω ∂ν, ∀ i ∈ F n,
        (ν[fun ω ↦ ⇑f (i +ᵥ ω) | tailSigmaAlgebra (ι → ℤ) E]) ω
          = (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω := by
      rw [Filter.eventually_all_finset]
      exact fun i _ ↦ hj i
    have hcard : ((F n).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 (hFne n))
    have hsmul : (ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) |
        tailSigmaAlgebra (ι → ℤ) E]) =ᵐ[ν] ((F n).card : ℝ)⁻¹ •
          ν[fun ω ↦ ∑ i ∈ F n, ⇑f (i +ᵥ ω) | tailSigmaAlgebra (ι → ℤ) E] :=
      condExp_smul (((F n).card : ℝ)⁻¹) (fun ω ↦ ∑ i ∈ F n, ⇑f (i +ᵥ ω))
        (tailSigmaAlgebra (ι → ℤ) E)
    filter_upwards [hsmul, hsum, hall] with ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  -- The mean ergodic theorem: the averages converge in `L¹` to `ν(f | 𝓘) = ν(f)`.
  have hcondI : (ν[⇑f | MeasurableSpace.smulInvariants (Multiplicative (ι → ℤ)) ((ι → ℤ) → E)])
      =ᵐ[ν] fun _ ↦ ∫ x, ⇑f x ∂ν := by
    rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
    exact condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one
      MeasurableSpace.smulInvariants_le herg ⇑f
  have hmean : Tendsto (fun n ↦ ∫ ω,
      ‖((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν‖ ∂ν) atTop (𝓝 0) := by
    refine (tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp
      (μ := ν) (F := F) (l := atTop) (.of_forall hFne) hFol hfint).congr fun n ↦ ?_
    exact integral_congr_ae (by filter_upwards [hcondI] with ω hω; rw [hω])
  -- Conditional expectation is an `L¹` contraction, so the constant is squeezed to zero.
  have hbnd : ∀ n, ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν
      ≤ ∫ ω, ‖((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν‖ ∂ν := by
    intro n
    have hsub : (ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν |
        tailSigmaAlgebra (ι → ℤ) E])
          =ᵐ[ν] fun ω ↦ (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν := by
      have h1 : (ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν |
          tailSigmaAlgebra (ι → ℤ) E])
            =ᵐ[ν] (ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) |
              tailSigmaAlgebra (ι → ℤ) E])
              - ν[fun _ : (ι → ℤ) → E ↦ ∫ x, ⇑f x ∂ν | tailSigmaAlgebra (ι → ℤ) E] :=
        condExp_sub (hRint n) (integrable_const _) (tailSigmaAlgebra (ι → ℤ) E)
      have h2 : (ν[fun _ : (ι → ℤ) → E ↦ ∫ x, ⇑f x ∂ν | tailSigmaAlgebra (ι → ℤ) E])
          = fun _ ↦ ∫ x, ⇑f x ∂ν := condExp_const h𝓣 _
      filter_upwards [h1, hRcond n] with ω hω1 hω2
      rw [hω1, Pi.sub_apply, h2, hω2]
    calc ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν
        = ∫ ω, |(ν[fun ω ↦ ((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν |
            tailSigmaAlgebra (ι → ℤ) E]) ω| ∂ν :=
          (integral_congr_ae (hsub.mono fun ω hω ↦ by rw [hω])).symm
      _ ≤ ∫ ω, |((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν| ∂ν :=
          integral_abs_condExp_le _
      _ = ∫ ω, ‖((F n).card : ℝ)⁻¹ • ∑ i ∈ F n, ⇑f (i +ᵥ ω) - ∫ x, ⇑f x ∂ν‖ ∂ν := by
          simp only [Real.norm_eq_abs]
  have hle : ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hmean hbnd
  have hzero : ∫ ω, |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν| ∂ν = 0 :=
    le_antisymm hle (integral_nonneg fun _ ↦ abs_nonneg _)
  have hint : Integrable
      (fun ω ↦ |(ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω - ∫ x, ⇑f x ∂ν|) ν :=
    (integrable_condExp.sub (integrable_const _)).abs
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae (.of_forall fun _ ↦ abs_nonneg _)
    hint).1 hzero] with ω hω
  simpa [sub_eq_zero] using hω

/-- **Georgii, Lemma (16.28), (ii) ⇒ (iii).** If some `ν ∈ ex 𝒢_Θ(γ)` has `ν(f | 𝓣) ≠ ν(f)` with
positive probability, then some `ν̃ ∈ ex 𝒢(γ)` fails to be shift invariant — indeed
`ν̃(f ∘ θ_j) ≠ ν̃(f)` for some site `j`, so `ν̃ ∉ 𝒢_Θ(γ)`. -/
theorem exists_mem_extremePoints_G_integral_comp_shift_ne (hf : Measurable ⇑f)
    (hν : ν ∈ (invariantG γ (shiftGroup (ι → ℤ) E)).extremePoints ℝ≥0∞)
    (hpos : 0 < ν {ω | (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω ≠ ∫ x, ⇑f x ∂ν}) :
    ∃ j : ι → ℤ, ∃ ν' ∈ (G γ).extremePoints ℝ≥0∞,
      ν' ∉ invariantG γ (shiftGroup (ι → ℤ) E) ∧
      ∫ ω, ⇑f ((shift E j).toFun ω) ∂ν' ≠ ∫ ω, ⇑f ω ∂ν' := by
  classical
  have hνmem : ν ∈ invariantG γ (shiftGroup (ι → ℤ) E) := extremePoints_subset hν
  have hprob : IsProbabilityMeasure ν := hνmem.1.1
  have hνG : ν ∈ G γ := hνmem.1
  have h𝓣 : (tailSigmaAlgebra (ι → ℤ) E) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := ι → ℤ) (E := E)
  have hfint : Integrable ⇑f ν := lp.integrable_of_measurable hf ν
  -- Some site separates the conditional expectations, by the ergodic theorem.
  have herg : ν ∈ trivialOn (invariantEvents (shiftGroup (ι → ℤ) E)) :=
    (mem_extremePoints_invariantG_iff_mem_trivialOn
      (shiftGroup_exists_disjoint_sites_preimage (E := E) (S := ι → ℤ)) hνmem).1 hν
  obtain ⟨j, hjne⟩ : ∃ j : ι → ℤ, ¬ ((ν[fun ω ↦ ⇑f ((shift E j).toFun ω) |
      tailSigmaAlgebra (ι → ℤ) E]) =ᵐ[ν] ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) := by
    by_contra hall
    push Not at hall
    exact absurd (ae_iff.1 (condExp_tail_ae_eq_integral_of_forall_condExp_comp_shift hf
      hνmem.2 herg hall)) hpos.ne'
  have hjpos : 0 < ν {ω | (ν[fun ω ↦ ⇑f ((shift E j).toFun ω) | tailSigmaAlgebra (ι → ℤ) E]) ω
      ≠ (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω} := by
    rw [pos_iff_ne_zero]
    exact fun h ↦ hjne (ae_iff.2 h)
  -- The `(𝒢(γ), 𝓣)`-kernel of Proposition (7.25).
  have hG : (G γ).Nonempty := ⟨ν, hνG⟩
  have hπ := isPAKernel_gibbsKernel_some hG
  have hkernel : ∀ᵐ ω ∂ν, gibbsKernel γ hG.some ω
      = condExpKernel ν (tailSigmaAlgebra (ι → ℤ) E) ω := hπ.ae_eq_condExpKernel h𝓣 hνG
  have hae1 : ∀ᵐ ω ∂ν, ∫ x, ⇑f x ∂(gibbsKernel γ hG.some ω)
      = (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω := by
    filter_upwards [hkernel,
      (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel h𝓣 hfint).symm] with ω hω1 hω2
    rw [hω1, hω2]
  have hae2 : ∀ᵐ ω ∂ν, ∫ x, ⇑f ((shift E j).toFun x) ∂(gibbsKernel γ hG.some ω)
      = (ν[fun ω ↦ ⇑f ((shift E j).toFun ω) | tailSigmaAlgebra (ι → ℤ) E]) ω := by
    filter_upwards [hkernel, (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel h𝓣
      (integrable_comp_shift hf ν j)).symm] with ω hω1 hω2
    rw [hω1, hω2]
  have hext : ∀ᵐ ω ∂ν, gibbsKernel γ hG.some ω ∈ (G γ).extremePoints ℝ≥0∞ :=
    ae_mem_extremePoints_G_gibbsKernel hG hνG
  -- Pick a boundary condition in the positive-measure set.
  obtain ⟨ω, hωext, hω1, hω2, hωne⟩ :
      ∃ ω, gibbsKernel γ hG.some ω ∈ (G γ).extremePoints ℝ≥0∞ ∧
        ∫ x, ⇑f x ∂(gibbsKernel γ hG.some ω) = (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω ∧
        ∫ x, ⇑f ((shift E j).toFun x) ∂(gibbsKernel γ hG.some ω)
          = (ν[fun ω ↦ ⇑f ((shift E j).toFun ω) | tailSigmaAlgebra (ι → ℤ) E]) ω ∧
        (ν[fun ω ↦ ⇑f ((shift E j).toFun ω) | tailSigmaAlgebra (ι → ℤ) E]) ω
          ≠ (ν[⇑f | tailSigmaAlgebra (ι → ℤ) E]) ω := by
    by_contra hemp
    push Not at hemp
    refine hjpos.ne' (ae_iff.1 ?_)
    filter_upwards [hext, hae1, hae2] with ω h1 h2 h3
    exact hemp ω h1 h2 h3
  refine ⟨j, gibbsKernel γ hG.some ω, hωext, ?_, ?_⟩
  · intro hmem
    have hmp : MeasurePreserving (shift E j).toFun (gibbsKernel γ hG.some ω)
        (gibbsKernel γ hG.some ω) := (mem_invariantFields_shiftGroup.1 hmem.2).2 j
    have : IsProbabilityMeasure (gibbsKernel γ hG.some ω) := hmem.1.1
    have heq : ∫ x, ⇑f ((shift E j).toFun x) ∂(gibbsKernel γ hG.some ω)
        = ∫ x, ⇑f x ∂(gibbsKernel γ hG.some ω) := by
      have h := integral_map (φ := (shift E j).toFun) (f := (⇑f : ((ι → ℤ) → E) → ℝ))
        hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
      rw [hmp.map_eq] at h
      exact h.symm
    rw [hω1, hω2] at heq
    exact hωne heq
  · rw [hω1, hω2]
    exact hωne

end ImpliesThree

/-! ### Georgii, Lemma (16.28) (i) ⇒ (iii), and the second corollary of Theorem (16.30) -/

section Composite

variable {ι E : Type*} [Finite ι] [Nonempty ι] [MeasurableSpace E] [StandardBorelSpace E]
  {γ : Specification (ι → ℤ) E} {Δ : Finset (ι → ℤ)} {f : lp (fun _ : (ι → ℤ) → E ↦ ℝ) ∞}
  {I : Set (ι → ℤ)} {μ : Measure ((ι → ℤ) → E)}

/-- **Georgii, Lemma (16.28), (i) ⇒ (iii).** An `f`-`I`-oscillating shift-invariant Gibbs measure
forces the existence of an extreme Gibbs measure which is *not* shift invariant. -/
theorem exists_mem_extremePoints_G_notMem_invariantG_of_isOscillating (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ) (hμ : μ ∈ invariantG γ (shiftGroup (ι → ℤ) E))
    (hosc : IsOscillating I f μ) :
    ∃ j : ι → ℤ, ∃ ν' ∈ (G γ).extremePoints ℝ≥0∞,
      ν' ∉ invariantG γ (shiftGroup (ι → ℤ) E) ∧
      ∫ ω, ⇑f ((shift E j).toFun ω) ∂ν' ≠ ∫ ω, ⇑f ω ∂ν' := by
  have hfm : Measurable ⇑f := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  obtain ⟨ν, hνex, -, hpos⟩ :=
    exists_mem_extremePoints_invariantG_notMem_extremePoints_G hI hf hμ hosc
  exact exists_mem_extremePoints_G_integral_comp_shift_ne hfm hνex hpos

/-- **Georgii, Theorem (16.30), last sentence, second half:** if some `f`-`I`-oscillating
shift-invariant Gibbs measure exists, then `ex 𝒢(γ) \ 𝒢_Θ(γ) ≠ ∅`, i.e. `γ` admits an extreme
Gibbs measure with broken shift invariance. -/
theorem nonempty_extremePoints_G_diff_invariantG (hI : I.Infinite)
    (hf : f ∈ localFunctionsOn (ι → ℤ) E Δ) (hμ : μ ∈ invariantG γ (shiftGroup (ι → ℤ) E))
    (hosc : IsOscillating I f μ) :
    ((G γ).extremePoints ℝ≥0∞ \ invariantG γ (shiftGroup (ι → ℤ) E)).Nonempty := by
  obtain ⟨-, ν', hν'ex, hν'not, -⟩ :=
    exists_mem_extremePoints_G_notMem_invariantG_of_isOscillating hI hf hμ hosc
  exact ⟨ν', hν'ex, hν'not⟩

end Composite

end MeasureTheory.GibbsMeasure

end

end

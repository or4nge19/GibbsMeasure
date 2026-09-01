/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.KolmogorovZeroOne
public import GibbsMeasure.Specification.GibbsKernel
public import GibbsMeasure.Topology.LocalMetric

/-!
# No proper regular conditional distribution given the tail σ-algebra

The eventual-agreement (`E₀`) class of a configuration is a tail event
(`measurableSet_tail_eventualAgreementClass`), null for any independent product with a uniform
atom bound (`infinitePi_eventualAgreementClass_eq_zero`). Tail triviality (Kolmogorov) pins the
tail conditional kernel to the measure itself on a countable generating π-system
(`tailKernel_apply_ae_eq_measure`, `ae_tailKernel_eq_self`), so properness on the whole tail
σ-algebra fails at every point of a full-measure set: Blackwell–Dubins
(`not_ae_forall_tailKernel_apply_eq_indicator`).

This turns the module-doc discussion in `ChoquetLaw.lean` and `ErgodicDecomposition.lean` — the
guarded conclusions there are false in Georgii's setting, not merely unprovable — into a theorem.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {ω : S → E}

/-- The eventual-agreement (`E₀`) class of a configuration: those configurations differing from it
at only finitely many sites. -/
def eventualAgreementClass (ω : S → E) : Set (S → E) := {ζ | {i | ζ i ≠ ω i}.Finite}

lemma self_mem_eventualAgreementClass (ω : S → E) : ω ∈ eventualAgreementClass ω := by
  simp [eventualAgreementClass]

lemma eventualAgreementClass_eq_iUnion (ω : S → E) :
    eventualAgreementClass ω = ⋃ Λ : Finset S, {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i} := by
  ext ζ
  simp only [eventualAgreementClass, mem_setOf_eq, mem_iUnion]
  constructor
  · intro h
    exact ⟨h.toFinset, fun i hi ↦ by
      by_contra hne
      exact hi (by simpa using hne)⟩
  · rintro ⟨Λ, hΛ⟩
    exact Λ.finite_toSet.subset fun i hi ↦ by
      by_contra hmem
      exact hi (hΛ i hmem)

/-- The `E₀`-class of every configuration is a tail event. -/
lemma measurableSet_tail_eventualAgreementClass [Countable S] [MeasurableSingletonClass E]
    (ω : S → E) :
    MeasurableSet[tailSigmaAlgebra S E] (eventualAgreementClass ω) := by
  classical
  rw [tailSigmaAlgebra]
  refine MeasurableSpace.measurableSet_iInf.2 fun Δ ↦ ?_
  rw [eventualAgreementClass_eq_iUnion]
  -- restrict the union to `Λ ⊇ Δ`, which does not change it
  have hres : (⋃ Λ : Finset S, {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i})
      = ⋃ Λ : Finset S, {ζ : S → E | ∀ i ∉ Δ ∪ Λ, ζ i = ω i} := by
    classical
    ext ζ
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨Λ, hΛ⟩
      exact ⟨Λ, fun i hi ↦ hΛ i fun hmem ↦ hi (Finset.mem_union_right _ hmem)⟩
    · rintro ⟨Λ, hΛ⟩
      exact ⟨Δ ∪ Λ, hΛ⟩
  rw [hres]
  refine MeasurableSet.iUnion fun Λ ↦ ?_
  have : {ζ : S → E | ∀ i ∉ Δ ∪ Λ, ζ i = ω i}
      = ⋂ i ∈ ((Δ ∪ Λ : Finset S) : Set S)ᶜ, {ζ : S → E | ζ i = ω i} := by
    ext ζ; simp
  rw [this]
  refine MeasurableSet.biInter (Set.to_countable _) fun i hi ↦ ?_
  have hmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Δ ∪ Λ : Finset S) : Set S)ᶜ]
      fun ζ : S → E ↦ ζ i := measurable_cylinderEvent_apply hi
  have h1 : {ζ : S → E | ζ i = ω i} = (fun ζ : S → E ↦ ζ i) ⁻¹' {ω i} := rfl
  have h2 : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ ∪ Λ : Finset S) : Set S)ᶜ]
      ((fun ζ : S → E ↦ ζ i) ⁻¹' {ω i}) := hmeas (measurableSet_singleton (ω i))
  -- this is `cylinderEvents (Δ∪Λ)ᶜ ≤ cylinderEvents Δᶜ`
  refine (cylinderEvents_mono ?_) _ (h1 ▸ h2)
  intro x hx
  simp only [Set.mem_compl_iff, Finset.coe_union, Set.mem_union] at hx ⊢
  exact fun hxΔ ↦ hx (Or.inl hxΔ)

/-- Under a uniform atom bound `μs i {x} ≤ c < 1`, the configurations agreeing with `ω` outside a
fixed finite volume form a null set for the product measure. -/
lemma infinitePi_setOf_forall_eq_zero [Infinite S] [MeasurableSingletonClass E]
    {μs : S → Measure E} [∀ i, IsProbabilityMeasure (μs i)] {c : ℝ≥0∞}
    (hc : ∀ i x, μs i {x} ≤ c) (hc1 : c < 1) (Λ : Finset S) (ω : S → E) :
    Measure.infinitePi μs {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i} = 0 := by
  classical
  have hbound : ∀ n : ℕ,
      Measure.infinitePi μs {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i} ≤ c ^ n := by
    intro n
    have hinf : ((Λ : Set S)ᶜ : Set S).Infinite := by
      have := Set.Finite.infinite_compl (Λ.finite_toSet)
      exact this
    obtain ⟨F, hFsub, hFcard⟩ := hinf.exists_subset_card_eq n
    have hsubset : {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i} ⊆ Set.pi (↑F) (fun i ↦ {ω i}) := by
      intro ζ hζ i hiF
      have hiΛ : i ∉ Λ := by
        have := hFsub hiF
        simpa using this
      simpa using hζ i hiΛ
    calc Measure.infinitePi μs {ζ : S → E | ∀ i ∉ Λ, ζ i = ω i}
        ≤ Measure.infinitePi μs (Set.pi (↑F) (fun i ↦ {ω i})) := measure_mono hsubset
      _ = ∏ i ∈ F, μs i {ω i} :=
          Measure.infinitePi_pi (μ := μs) fun i _ ↦ measurableSet_singleton (ω i)
      _ ≤ ∏ _i ∈ F, c := Finset.prod_le_prod' fun i _ ↦ hc i (ω i)
      _ = c ^ n := by rw [Finset.prod_const, hFcard]
  refine le_antisymm ?_ bot_le
  exact ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc1)
    (Eventually.of_forall hbound)

/-- Under a uniform atom bound, every `E₀`-class is null for the product measure. -/
lemma infinitePi_eventualAgreementClass_eq_zero [Countable S] [Infinite S]
    [MeasurableSingletonClass E] {μs : S → Measure E} [∀ i, IsProbabilityMeasure (μs i)] {c : ℝ≥0∞}
    (hc : ∀ i x, μs i {x} ≤ c) (hc1 : c < 1) (ω : S → E) :
    Measure.infinitePi μs (eventualAgreementClass ω) = 0 := by
  rw [eventualAgreementClass_eq_iUnion]
  exact measure_iUnion_null fun Λ ↦ infinitePi_setOf_forall_eq_zero hc hc1 Λ ω

-- (i) for a tail-trivial probability measure, the tail kernel is a.e. constant per event
lemma tailKernel_apply_ae_eq_measure [Countable S] [StandardBorelSpace E]
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (htriv : ∀ A, MeasurableSet[tailSigmaAlgebra S E] A → μ A = 0 ∨ μ A = 1)
    {B : Set (S → E)} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, tailKernel μ ω B = μ B := by
  have hm : (tailSigmaAlgebra S E : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi (S := S) (E := E)
  -- the conditional expectation of `1_B` given the tail is a.e. constant, with value `μ.real B`
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_forall_measure_eq_zero_or_one hm htriv
    (stronglyMeasurable_condExp (m := tailSigmaAlgebra S E) (μ := μ)
      (f := B.indicator (fun _ ↦ (1 : ℝ)))).measurable
  have hgi : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ := (integrable_const (1 : ℝ)).indicator hB
  have hcval : c = μ.real B := by
    have h0 : ∫ x, (μ[B.indicator (fun _ ↦ (1 : ℝ)) | tailSigmaAlgebra S E]) x ∂μ = μ.real B := by
      rw [integral_condExp hm]
      exact integral_indicator_one hB
    rw [integral_congr_ae hc, integral_const] at h0
    simpa [measureReal_def, measure_univ] using h0
  filter_upwards [tailKernel_real_ae_eq_condExp μ hB, hc] with ω h1 h2
  have hreal : (tailKernel μ ω).real B = μ.real B := by rw [h1, h2, hcval]
  have hK : IsProbabilityMeasure (tailKernel μ ω) := inferInstance
  have := congrArg ENNReal.ofReal hreal
  rwa [measureReal_def, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at this

-- (ii) over a countable generating π-system, the kernel is a.e. THE measure
lemma ae_tailKernel_eq_self [Countable S] [Finite E] [StandardBorelSpace E]
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (htriv : ∀ A, MeasurableSet[tailSigmaAlgebra S E] A → μ A = 0 ∨ μ A = 1) :
    ∀ᵐ ω ∂μ, tailKernel μ ω = μ := by
  have hcnt : (localEvents S E).Countable := countable_localEvents (S := S) (E := E)
  have hall : ∀ᵐ ω ∂μ, ∀ C ∈ localEvents S E, tailKernel μ ω C = μ C := by
    rw [ae_ball_iff hcnt]
    intro C hC
    exact tailKernel_apply_ae_eq_measure htriv (.of_mem_measurableCylinders hC)
  filter_upwards [hall] with ω hω
  refine ext_of_generate_finite (measurableCylinders (fun _ : S ↦ E))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (fun C hC ↦ hω C hC) ?_
  simp

/-- **Blackwell–Dubins: no proper regular conditional distribution given the tail σ-algebra.**
For an independent product with a uniform atom bound `μs i {x} ≤ c < 1` over an infinite site set,
the library's tail conditional kernel `tailKernel μ = condExpKernel μ 𝓣` does NOT satisfy
"for `μ`-a.e. `ω`, for all tail events `A`, `tailKernel μ ω A = 1_A(ω)`" — and by
`ae_tailKernel_eq_self` no version could: tail triviality pins the kernel to `μ` itself, while the
`E₀`-class of `ω` is a `μ`-null tail event containing `ω`. This is why the
`CountableOrCountablyGenerated` hypotheses of `ChoquetLaw.lean`/`ErgodicDecomposition.lean` cannot
be removed. -/
theorem not_ae_forall_tailKernel_apply_eq_indicator
    [Countable S] [Infinite S] [Finite E] [MeasurableSingletonClass E] [StandardBorelSpace E]
    {μs : S → Measure E} [∀ i, IsProbabilityMeasure (μs i)] {c : ℝ≥0∞}
    (hc : ∀ i x, μs i {x} ≤ c) (hc1 : c < 1) :
    ¬ ∀ᵐ ω ∂(Measure.infinitePi μs),
        ∀ A, MeasurableSet[tailSigmaAlgebra S E] A →
          tailKernel (Measure.infinitePi μs) ω A
            = A.indicator (fun _ ↦ (1 : ℝ≥0∞)) ω := by
  intro hcontra
  have htriv : ∀ A, MeasurableSet[tailSigmaAlgebra S E] A →
      Measure.infinitePi μs A = 0 ∨ Measure.infinitePi μs A = 1 :=
    fun A hA ↦ forall_tail_measure_eq_zero_or_one_infinitePi μs hA
  have hker := ae_tailKernel_eq_self (μ := Measure.infinitePi μs) htriv
  have hne : (ae (Measure.infinitePi μs)).NeBot :=
    ae_neBot.2 (IsProbabilityMeasure.ne_zero _)
  obtain ⟨ω, hω1, hω2⟩ := (hker.and hcontra).exists
  have hA := measurableSet_tail_eventualAgreementClass (E := E) ω
  have h1 : tailKernel (Measure.infinitePi μs) ω (eventualAgreementClass ω) = 1 := by
    rw [hω2 _ hA, Set.indicator_of_mem (self_mem_eventualAgreementClass ω)]
  rw [hω1, infinitePi_eventualAgreementClass_eq_zero hc hc1 ω] at h1
  exact zero_ne_one h1

end MeasureTheory.GibbsMeasure

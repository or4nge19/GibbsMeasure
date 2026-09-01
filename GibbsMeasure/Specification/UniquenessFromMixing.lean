/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Quasilocality
public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.Probability.ConditionalProbability

/-!
# Georgii, Proposition (7.11)(a): uniqueness from uniform mixing

Georgii's property (7.10) for a probability measure `μ` on the configuration space `E^S`:

  `lim_Λ sup { |μ(A | B) - μ(A)| : B ∈ 𝓣_Λ, μ(B) > 0 } = 0`  for every cylinder event `A`,

i.e. conditioning on any non-null event outside a large enough volume moves the probability of a
local event by arbitrarily little.  This is `MeasureTheory.GibbsMeasure.IsUniformlyMixing`.

**Proposition (7.11)(a)**: if `γ = ρλ` is a *quasilocal* λ-specification with *positive*
densities and some `μ ∈ 𝒢(γ)` satisfies (7.10), then `𝒢(γ) = {μ}`.

Following Georgii's half-page proof:

* from (7.10) and the DLR equation, `γ_Λ(A|·)` is within `ε` of `μ(A)` `μ`-almost surely
  (`ae_abs_real_apply_sub_le_of_forall_cond_abs_le`);
* quasilocality replaces `γ_Λ(A|·)` by a local observable `f ∈ 𝓛_Δ` within `ε`
  (`Specification.IsQuasilocal.exists_measurable_cylinderEvents_dist_le`);
* Remark (1.28)(2) — Gibbs measures of a positive λ-specification are mutually absolutely
  continuous on every finite-volume σ-algebra `𝓕_Δ`
  (`Specification.IsGibbsMeasure.lambdaSpecification_null_iff`) — transfers the `μ`-a.s. bound
  `|f - μ(A)| ≤ 2ε` to any other `ν ∈ 𝒢(γ)`;
* integrating `ν γ_Λ = ν` gives `|ν(A) - μ(A)| ≤ 3ε`, and a π-system argument on the cylinder
  events concludes `ν = μ`.

## Main declarations

* `MeasureTheory.GibbsMeasure.IsUniformlyMixing`: Georgii's mixing property (7.10).
* `Specification.IsGibbsMeasure.lambdaSpecification_null_iff` and
  `Specification.IsGibbsMeasure.lambdaSpecification_null_iff_null`: **Georgii, Remark (1.28)(2)**.
* `MeasureTheory.GibbsMeasure.eq_of_isGibbsMeasure_of_isUniformlyMixing`: the abstract core of
  (7.11)(a) — quasilocality plus local absolute continuity plus (7.10) forces uniqueness.
* `MeasureTheory.GibbsMeasure.eq_of_isGibbsMeasure_lambdaSpecification_of_isUniformlyMixing` and
  `MeasureTheory.GibbsMeasure.G_lambdaSpecification_eq_singleton_of_isUniformlyMixing`:
  **Georgii, Proposition (7.11)(a)**.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Georgii's mixing property (7.10) -/

/-- **Georgii (7.10).** A probability measure `μ` on the configuration space is *uniformly
mixing* if for every cylinder event `A` and every `ε > 0`, all large enough finite volumes `Λ`
satisfy `|μ(A | B) - μ(A)| ≤ ε` for every non-null `B ∈ 𝓣_Λ = 𝓕_{Λᶜ}`.

This strengthens the short-range-correlations characterization of tail triviality (Georgii (7.9),
`MeasureTheory.GibbsMeasure.isTailTrivial_iff_asymptotically_independent`): there the *covariance*
`|μ(A ∩ B) - μ(A)μ(B)|` is small, here the *conditional probability* `μ(A | B)` is close to
`μ(A)` even for events `B` of very small positive probability. -/
def IsUniformlyMixing (μ : Measure (S → E)) : Prop :=
  ∀ A ∈ localEvents S E, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ Λ : Finset S in Filter.atTop,
      ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B → μ B ≠ 0 →
        |(μ[|B]).real A - μ.real A| ≤ ε

/-- To be uniformly mixing it suffices to find, for every cylinder event and tolerance, *one*
finite volume that works: the exterior σ-algebras `𝓣_Λ` shrink as `Λ` grows. -/
lemma isUniformlyMixing_of_forall_exists {μ : Measure (S → E)}
    (h : ∀ A ∈ localEvents S E, ∀ ε : ℝ, 0 < ε →
      ∃ Λ : Finset S, ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B →
        μ B ≠ 0 → |(μ[|B]).real A - μ.real A| ≤ ε) :
    IsUniformlyMixing μ := by
  intro A hA ε hε
  obtain ⟨Λ₀, hΛ₀⟩ := h A hA ε hε
  filter_upwards [Filter.eventually_ge_atTop Λ₀] with Λ hΛ B hB hB0
  exact hΛ₀ B (cylinderEvents_mono (compl_subset_compl.2 (by exact_mod_cast hΛ)) _ hB) hB0

/-- Extract one good volume from uniform mixing. -/
lemma IsUniformlyMixing.exists_finset {μ : Measure (S → E)} (hmix : IsUniformlyMixing μ)
    {A : Set (S → E)} (hA : A ∈ localEvents S E) {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ : Finset S, ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B →
      μ B ≠ 0 → |(μ[|B]).real A - μ.real A| ≤ ε := by
  classical
  exact (hmix A hA ε hε).exists

/-! ### The DLR equation, conditioned on an exterior event -/

variable {γ : Specification S E} {μ : Measure (S → E)}

/-- If `μ` is Gibbs for `γ` and `B ∈ 𝓕_{Λᶜ}` is an event outside the volume `Λ`, then
`μ(A ∩ B) = ∫_B γ_Λ(A|·) dμ`.  This is the display in Georgii's proof of (7.11)(a). -/
lemma measure_inter_eq_setLIntegral_of_isGibbsMeasure [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) {A B : Set (S → E)} (hA : MeasurableSet A)
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B) :
    μ (A ∩ B) = ∫⁻ η in B, γ Λ η A ∂μ := by
  have hfix : μ.bind (γ Λ) = μ :=
    (Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ)).1 hμ Λ
  have hBpi : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hAB : MeasurableSet (A ∩ B) := hA.inter hBpi
  have hmeasγ : Measurable (γ Λ : (S → E) → Measure (S → E)) :=
    (γ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  calc
    μ (A ∩ B) = (μ.bind (γ Λ)) (A ∩ B) := by rw [hfix]
    _ = ∫⁻ η, γ Λ η (A ∩ B) ∂μ := Measure.bind_apply hAB hmeasγ.aemeasurable
    _ = ∫⁻ η, B.indicator (fun η ↦ γ Λ η A) η ∂μ := by
        refine lintegral_congr fun η ↦ ?_
        rw [γ.isProper.inter_eq_indicator_mul Λ hA hB η]
        by_cases hη : η ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hη]
    _ = ∫⁻ η in B, γ Λ η A ∂μ := lintegral_indicator hBpi fun η ↦ γ Λ η A

/-- A pointwise lower bound on `γ_Λ(A|·)` over a non-null exterior event `B` lower-bounds the
conditional probability `μ(A | B)` of a Gibbs measure. -/
lemma le_cond_real_of_isGibbsMeasure [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) {Λ : Finset S} {A B : Set (S → E)} (hA : MeasurableSet A)
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B) (hB0 : μ B ≠ 0)
    {c : ℝ} (hc : 0 ≤ c) (hle : ∀ η ∈ B, c ≤ (γ Λ η).real A) :
    c ≤ (μ[|B]).real A := by
  have hBpi : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hBfin : μ B ≠ ∞ := measure_ne_top μ B
  have hkey : ENNReal.ofReal c * μ B ≤ μ (B ∩ A) := by
    rw [Set.inter_comm, measure_inter_eq_setLIntegral_of_isGibbsMeasure hμ Λ hA hB]
    calc ENNReal.ofReal c * μ B = ∫⁻ _ in B, ENNReal.ofReal c ∂μ :=
          (setLIntegral_const B _).symm
    _ ≤ ∫⁻ η in B, γ Λ η A ∂μ := by
        refine setLIntegral_mono_ae ((γ Λ).measurable_coe hA |>.mono cylinderEvents_le_pi
          le_rfl).aemeasurable (ae_of_all _ fun η hη ↦ ?_)
        exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 (hle η hη)
  have h2 : ENNReal.ofReal c ≤ (μ B)⁻¹ * μ (B ∩ A) := by
    calc ENNReal.ofReal c = ENNReal.ofReal c * ((μ B)⁻¹ * μ B) := by
          rw [ENNReal.inv_mul_cancel hB0 hBfin, mul_one]
    _ = (μ B)⁻¹ * (ENNReal.ofReal c * μ B) := by ring
    _ ≤ (μ B)⁻¹ * μ (B ∩ A) := by gcongr
  have h3 : (μ B)⁻¹ * μ (B ∩ A) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := 1) ENNReal.one_ne_top ?_
    calc (μ B)⁻¹ * μ (B ∩ A) ≤ (μ B)⁻¹ * μ B := by
          gcongr
          exact Set.inter_subset_left
    _ = 1 := ENNReal.inv_mul_cancel hB0 hBfin
  calc c = (ENNReal.ofReal c).toReal := (ENNReal.toReal_ofReal hc).symm
  _ ≤ ((μ B)⁻¹ * μ (B ∩ A)).toReal := ENNReal.toReal_mono h3 h2
  _ = (μ[|B]).real A := by rw [measureReal_def, cond_apply hBpi μ A]

/-- A pointwise upper bound on `γ_Λ(A|·)` over a non-null exterior event `B` upper-bounds the
conditional probability `μ(A | B)` of a Gibbs measure. -/
lemma cond_real_le_of_isGibbsMeasure [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) {Λ : Finset S} {A B : Set (S → E)} (hA : MeasurableSet A)
    (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B) (hB0 : μ B ≠ 0)
    {c : ℝ} (hle : ∀ η ∈ B, (γ Λ η).real A ≤ c) :
    (μ[|B]).real A ≤ c := by
  have hBpi : MeasurableSet B := cylinderEvents_le_pi _ hB
  have hBfin : μ B ≠ ∞ := measure_ne_top μ B
  obtain ⟨η₁, hη₁⟩ : B.Nonempty := Set.nonempty_iff_ne_empty.2 fun h ↦ hB0 (h ▸ measure_empty)
  have hc : 0 ≤ c := le_trans measureReal_nonneg (hle η₁ hη₁)
  have hkey : μ (B ∩ A) ≤ ENNReal.ofReal c * μ B := by
    rw [Set.inter_comm, measure_inter_eq_setLIntegral_of_isGibbsMeasure hμ Λ hA hB]
    calc ∫⁻ η in B, γ Λ η A ∂μ ≤ ∫⁻ _ in B, ENNReal.ofReal c ∂μ := by
          refine setLIntegral_mono_ae aemeasurable_const (ae_of_all _ fun η hη ↦ ?_)
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc).2 (hle η hη)
    _ = ENNReal.ofReal c * μ B := setLIntegral_const B _
  have h4 : (μ B)⁻¹ * μ (B ∩ A) ≤ ENNReal.ofReal c := by
    calc (μ B)⁻¹ * μ (B ∩ A) ≤ (μ B)⁻¹ * (ENNReal.ofReal c * μ B) := by gcongr
    _ = ENNReal.ofReal c * ((μ B)⁻¹ * μ B) := by ring
    _ = ENNReal.ofReal c := by rw [ENNReal.inv_mul_cancel hB0 hBfin, mul_one]
  rw [measureReal_def, cond_apply hBpi μ A]
  exact ENNReal.toReal_le_of_le_ofReal hc h4

/-- **First step of Georgii's proof of (7.11)(a).** If conditioning `μ` on any non-null event
outside `Λ` moves the probability of `A` by at most `ε`, then the kernel probabilities
`γ_Λ(A|·)` are within `ε` of `μ(A)`, `μ`-almost surely. -/
lemma ae_abs_real_apply_sub_le_of_forall_cond_abs_le [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) {A : Set (S → E)} (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε)
    {Λ : Finset S}
    (hmix : ∀ B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B →
      μ B ≠ 0 → |(μ[|B]).real A - μ.real A| ≤ ε) :
    ∀ᵐ η ∂μ, |(γ Λ η).real A - μ.real A| ≤ ε := by
  have hgmeas : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
      fun η ↦ (γ Λ η).real A := by
    simp only [measureReal_def]
    exact ((γ Λ).measurable_coe hA).ennreal_toReal
  -- upper exceptional sets
  have hupper : ∀ n : ℕ,
      μ {η | μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤ (γ Λ η).real A} = 0 := by
    intro n
    have hinv : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    by_contra hB0
    have hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
        {η | μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤ (γ Λ η).real A} :=
      measurableSet_le measurable_const hgmeas
    have hge : μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤
        (μ[|{η | μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤ (γ Λ η).real A}]).real A :=
      le_cond_real_of_isGibbsMeasure hμ hA hB hB0 (by positivity) fun η hη ↦ hη
    have hle := (abs_le.1 (hmix _ hB hB0)).2
    linarith
  -- lower exceptional sets
  have hlower : ∀ n : ℕ,
      μ {η | (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹} = 0 := by
    intro n
    have hinv : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    rcases lt_or_ge (μ.real A - ε - ((n : ℝ) + 1)⁻¹) 0 with hneg | hpos
    · have : {η : S → E | (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun η hη ↦
          absurd (le_trans measureReal_nonneg hη) (not_le.2 hneg)
      rw [this, measure_empty]
    · by_contra hB0
      have hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
          {η | (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹} :=
        measurableSet_le hgmeas measurable_const
      have hge : (μ[|{η | (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹}]).real A ≤
          μ.real A - ε - ((n : ℝ) + 1)⁻¹ :=
        cond_real_le_of_isGibbsMeasure hμ hA hB hB0 fun η hη ↦ hη
      have hle := (abs_le.1 (hmix _ hB hB0)).1
      linarith
  -- combine
  rw [ae_iff]
  refine measure_mono_null (fun η hη ↦ ?_) (measure_iUnion_null fun n ↦
    measure_union_null (hupper n) (hlower n))
  have hη' : ε < |(γ Λ η).real A - μ.real A| := not_le.1 hη
  rcases lt_abs.1 hη' with h | h
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < (γ Λ η).real A - μ.real A - ε by
      linarith)
    rw [one_div] at hn
    refine Set.mem_iUnion.2 ⟨n, Set.mem_union_left _ ?_⟩
    show μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤ (γ Λ η).real A
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < μ.real A - (γ Λ η).real A - ε by
      linarith)
    rw [one_div] at hn
    refine Set.mem_iUnion.2 ⟨n, Set.mem_union_right _ ?_⟩
    show (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹
    linarith

end MeasureTheory.GibbsMeasure

/-! ### Quasilocality: uniform approximation of `γ_Λ(A|·)` by a local observable -/

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}

/-- **Second step of Georgii's proof of (7.11)(a).** For a quasilocal specification and a cylinder
event `A`, the function `γ_Λ(A|·)` is uniformly within `ε` of a bounded observable that is
measurable for a finite-volume σ-algebra `𝓕_Δ`. -/
lemma IsQuasilocal.exists_measurable_cylinderEvents_dist_le (hqc : γ.IsQuasilocal)
    {A : Set (S → E)} (hA : A ∈ localEvents S E) (Λ : Finset S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Δ : Finset S) (f : (S → E) → ℝ),
      Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] f ∧
        ∀ η, |(γ Λ η).real A - f η| ≤ ε := by
  obtain ⟨Δ₀, hΔ₀⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hApi : MeasurableSet A := cylinderEvents_le_pi _ hΔ₀
  have hmem : Memℓp (A.indicator (fun _ ↦ (1 : ℝ)) : (S → E) → ℝ) ∞ := by
    refine memℓp_infty ⟨1, ?_⟩
    rintro x ⟨η, rfl⟩
    by_cases hη : η ∈ A <;> simp [hη]
  set indA : lp (fun _ : S → E ↦ ℝ) ∞ := ⟨A.indicator (fun _ ↦ (1 : ℝ)), hmem⟩
  have hloc : indA ∈ localFunctions S E :=
    mem_localFunctions.2 ⟨Δ₀, measurable_const.indicator hΔ₀⟩
  have hql : γ.action Λ indA ∈ quasilocalFunctions S E :=
    hqc Λ indA (localFunctions_le_quasilocalFunctions hloc)
  obtain ⟨g, hg, hdist⟩ :=
    Metric.mem_closure_iff.1 (mem_quasilocalFunctions_iff_mem_closure.1 hql) ε hε
  obtain ⟨Δ, hΔ⟩ := mem_localFunctions.1 (SetLike.mem_coe.1 hg)
  refine ⟨Δ, ⇑g, hΔ, fun η ↦ ?_⟩
  have h1 : (γ.action Λ indA : (S → E) → ℝ) η = (γ Λ η).real A := by
    rw [action_apply]
    show (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(γ Λ η)) = _
    simpa [Pi.one_def] using integral_indicator_one (μ := γ Λ η) hApi
  have h2 : |(γ.action Λ indA : (S → E) → ℝ) η - g η| ≤ dist (γ.action Λ indA) g := by
    have h := lp.norm_apply_le_norm ENNReal.top_ne_zero (γ.action Λ indA - g) η
    rw [dist_eq_norm]
    simpa [lp.coeFn_sub, Real.norm_eq_abs] using h
  rw [← h1]
  exact le_trans h2 hdist.le

end Specification

/-! ### Georgii, Remark (1.28)(2): local equivalence of Gibbs measures of a positive
λ-specification -/

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E} {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- On events of the finite-volume σ-algebra `𝓕_Δ`, the reference kernel
`λ_Δ(·|η) = λ^Δ × δ_{η_{S∖Δ}}` does not depend on the boundary condition `η`. -/
lemma sigmaFiniteLambdaFun_apply_congr (ν : Measure E) [SigmaFinite ν] (Δ : Finset S)
    {C : Set (S → E)} (hC : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] C)
    (η η' : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η C =
      sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η' C := by
  have hCpi : MeasurableSet C := cylinderEvents_le_pi _ hC
  have hpre : juxt ((Δ : Set S)) η ⁻¹' C = juxt ((Δ : Set S)) η' ⁻¹' C := by
    ext ζ
    exact mem_congr_of_measurableSet_cylinderEvents hC fun i hi ↦ by
      rw [juxt_apply_of_mem hi, juxt_apply_of_mem hi]
  rw [sigmaFiniteLambdaFun_apply_eq_map, sigmaFiniteLambdaFun_apply_eq_map,
    Measure.map_apply (Measurable.juxt) hCpi, Measure.map_apply (Measurable.juxt) hCpi, hpre]

variable (ν : Measure E) [SigmaFinite ν] [NeZero ν]
  {hρ : IsPremodifier (S := S) (E := E) ρ}
  {hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ}

/-- **Georgii, Remark (1.28)(2), one measure.** A Gibbs measure for a λ-specification with
*positive* densities annihilates an event of a finite-volume σ-algebra `𝓕_Δ` exactly when the
reference kernel `λ_Δ` does.  In particular its null events in `𝓕_Δ` do not depend on the Gibbs
measure. -/
theorem IsGibbsMeasure.lambdaSpecification_null_iff {μ : Measure (S → E)}
    [IsFiniteMeasure μ] [NeZero μ]
    (hμ : (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (Δ : Finset S) {C : Set (S → E)}
    (hC : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] C) :
    μ C = 0 ↔ ∀ η, sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η C = 0 := by
  set γ := lambdaSpecification (S := S) (E := E) ν ρ hρ hZ with hγdef
  have hCpi : MeasurableSet C := cylinderEvents_le_pi _ hC
  have hdensmeas : Measurable (sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Δ) :=
    sigmaFinitePremodifierNorm_measurable (S := S) (E := E) ν hρ Δ
  have hker : ∀ η, γ Δ η C = 0 ↔ sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η C = 0 := by
    intro η
    rw [hγdef, lambdaSpecification_apply, withDensity_apply_eq_zero hdensmeas]
    have huniv : {σ | sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Δ σ ≠ 0} = Set.univ := by
      refine Set.eq_univ_of_forall fun σ ↦ ?_
      show sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Δ σ ≠ 0
      rw [sigmaFinitePremodifierNorm]
      simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
      exact ⟨hpos Δ σ, hZ.ne_top Δ σ⟩
    rw [huniv, Set.univ_inter]
  have hmeasγ : Measurable fun η ↦ γ Δ η C :=
    ((γ Δ).measurable_coe hCpi).mono cylinderEvents_le_pi le_rfl
  have hbind : μ C = ∫⁻ η, γ Δ η C ∂μ := by
    conv_lhs => rw [← (isGibbsMeasure_iff_forall_bind_eq (γ := γ)).1 hμ Δ]
    exact Measure.bind_apply hCpi ((γ Δ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
  constructor
  · intro h0
    have hae : ∀ᵐ η ∂μ, γ Δ η C = 0 := by
      have := (lintegral_eq_zero_iff hmeasγ).1 (hbind ▸ h0)
      filter_upwards [this] with η hη using hη
    obtain ⟨η₀, hη₀⟩ := hae.exists
    intro η
    rw [sigmaFiniteLambdaFun_apply_congr ν Δ hC η η₀]
    exact (hker η₀).1 hη₀
  · intro h
    rw [hbind]
    have hzero : ∀ η, γ Δ η C = 0 := fun η ↦ (hker η).2 (h η)
    simp [hzero]

/-- **Georgii, Remark (1.28)(2).** Any two Gibbs measures for a λ-specification with positive
densities are mutually absolutely continuous on every finite-volume σ-algebra `𝓕_Δ`. -/
theorem IsGibbsMeasure.lambdaSpecification_null_iff_null {μ ν' : Measure (S → E)}
    [IsFiniteMeasure μ] [NeZero μ] [IsFiniteMeasure ν'] [NeZero ν']
    (hμ : (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ)
    (hν' : (lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure ν')
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) (Δ : Finset S) {C : Set (S → E)}
    (hC : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] C) :
    μ C = 0 ↔ ν' C = 0 := by
  rw [IsGibbsMeasure.lambdaSpecification_null_iff ν hμ hpos Δ hC,
    IsGibbsMeasure.lambdaSpecification_null_iff ν hν' hpos Δ hC]

end Specification

/-! ### Georgii, Proposition (7.11)(a) -/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-- The abstract core of **Georgii, Proposition (7.11)(a)**: let `γ` be a quasilocal
specification and `μ, ν ∈ 𝒢(γ)`.  If `ν` is absolutely continuous with respect to `μ` on every
finite-volume σ-algebra `𝓕_Δ` (which Remark (1.28)(2) provides when `γ` is a λ-specification
with positive densities) and `μ` is uniformly mixing (7.10), then `ν = μ`. -/
theorem eq_of_isGibbsMeasure_of_isUniformlyMixing {γ : Specification S E}
    (hqc : γ.IsQuasilocal) {μ ν : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : γ.IsGibbsMeasure μ) (hν : γ.IsGibbsMeasure ν)
    (habs : ∀ (Δ : Finset S) ⦃C : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] C → μ C = 0 → ν C = 0)
    (hmix : IsUniformlyMixing μ) :
    ν = μ := by
  refine Measure.ext_of_generate_finite_of_isProbabilityMeasure
    (measurableCylinders fun _ : S ↦ E) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders fun A hA ↦ ?_
  have hApi : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  -- Georgii's estimate: `|ν(A) - μ(A)| ≤ 3ε` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → |ν.real A - μ.real A| ≤ 3 * ε := by
    intro ε hε
    obtain ⟨Λ, hΛ⟩ := hmix.exists_finset hA hε
    have hae_μ : ∀ᵐ η ∂μ, |(γ Λ η).real A - μ.real A| ≤ ε :=
      ae_abs_real_apply_sub_le_of_forall_cond_abs_le hμ hApi hε hΛ
    obtain ⟨Δ, f, hf, hfapprox⟩ :=
      hqc.exists_measurable_cylinderEvents_dist_le hA Λ hε
    -- the `𝓕_Δ`-measurable exceptional event
    have hNmeas : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
        {η | ¬|f η - μ.real A| ≤ 2 * ε} := by
      have h1 : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)]
          {η | |f η - μ.real A| ≤ 2 * ε} := by
        have heq : {η : S → E | |f η - μ.real A| ≤ 2 * ε}
            = {η | -(2 * ε) ≤ f η - μ.real A} ∩ {η | f η - μ.real A ≤ 2 * ε} := by
          ext η
          simp [abs_le]
        rw [heq]
        exact (measurableSet_le measurable_const (hf.sub measurable_const)).inter
          (measurableSet_le (hf.sub measurable_const) measurable_const)
      exact h1.compl
    have hμN : μ {η | ¬|f η - μ.real A| ≤ 2 * ε} = 0 := by
      rw [← ae_iff]
      filter_upwards [hae_μ] with η hη
      calc |f η - μ.real A|
          ≤ |f η - (γ Λ η).real A| + |(γ Λ η).real A - μ.real A| := abs_sub_le _ _ _
      _ ≤ ε + ε := add_le_add (by rw [abs_sub_comm]; exact hfapprox η) hη
      _ = 2 * ε := by ring
    have hae_ν : ∀ᵐ η ∂ν, |(γ Λ η).real A - μ.real A| ≤ 3 * ε := by
      have hν2 : ∀ᵐ η ∂ν, |f η - μ.real A| ≤ 2 * ε := by
        rw [ae_iff]
        exact habs Δ hNmeas hμN
      filter_upwards [hν2] with η hη
      calc |(γ Λ η).real A - μ.real A|
          ≤ |(γ Λ η).real A - f η| + |f η - μ.real A| := abs_sub_le _ _ _
      _ ≤ ε + 2 * ε := add_le_add (hfapprox η) hη
      _ = 3 * ε := by ring
    -- integrate `ν γ_Λ = ν`
    have hgmeas : Measurable fun η ↦ γ Λ η A :=
      ((γ Λ).measurable_coe hApi).mono cylinderEvents_le_pi le_rfl
    have hbind : ν A = ∫⁻ η, γ Λ η A ∂ν := by
      conv_lhs => rw [← (Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ)).1 hν Λ]
      exact Measure.bind_apply hApi
        ((γ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable
    have hint : ∫ η, (γ Λ η).real A ∂ν = ν.real A := by
      simp only [measureReal_def]
      rw [integral_toReal hgmeas.aemeasurable (ae_of_all _ fun η ↦ measure_lt_top _ _), ← hbind]
    have hIntg : Integrable (fun η ↦ (γ Λ η).real A) ν := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun η ↦ ?_)
      · exact (Measurable.aestronglyMeasurable (by
          simp only [measureReal_def]; exact hgmeas.ennreal_toReal))
      · rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    have h1 : ∫ η, ((γ Λ η).real A - μ.real A) ∂ν = ν.real A - μ.real A := by
      rw [integral_sub hIntg (integrable_const _), hint, integral_const]
      simp
    calc |ν.real A - μ.real A| = |∫ η, ((γ Λ η).real A - μ.real A) ∂ν| := by rw [h1]
    _ ≤ 3 * ε * ν.real Set.univ := by
        have h := norm_integral_le_of_norm_le_const (μ := ν)
          (f := fun η ↦ (γ Λ η).real A - μ.real A) (C := 3 * ε)
          (hae_ν.mono fun η hη ↦ (Real.norm_eq_abs _).le.trans hη)
        simpa [Real.norm_eq_abs] using h
    _ = 3 * ε := by simp [measureReal_def]
  have hreal : ν.real A = μ.real A := by
    by_contra hne
    have h3 : 0 < |ν.real A - μ.real A| := abs_pos.2 (sub_ne_zero.2 hne)
    have h4 := key (|ν.real A - μ.real A| / 4) (by positivity)
    linarith
  rw [measureReal_def, measureReal_def] at hreal
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν A) (measure_ne_top μ A)).1 hreal

/-- **Georgii, Proposition (7.11)(a).** Let `γ = ρλ` be a quasilocal λ-specification with
positive densities.  If some Gibbs measure `μ ∈ 𝒢(γ)` satisfies the mixing property (7.10), then
every Gibbs measure for `γ` equals `μ`. -/
theorem eq_of_isGibbsMeasure_lambdaSpecification_of_isUniformlyMixing (ν : Measure E)
    [SigmaFinite ν] [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    {hρ : Specification.IsPremodifier (S := S) (E := E) ρ}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ}
    (hqc : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsQuasilocal)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) {μ ν' : Measure (S → E)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hμ : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure μ)
    (hmix : IsUniformlyMixing μ)
    (hν' : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsGibbsMeasure ν') :
    ν' = μ :=
  eq_of_isGibbsMeasure_of_isUniformlyMixing hqc hμ hν'
    (fun Δ _C hC h0 ↦
      (Specification.IsGibbsMeasure.lambdaSpecification_null_iff_null ν hμ hν' hpos Δ hC).1 h0)
    hmix

/-- **Georgii, Proposition (7.11)(a)**, in the form `𝒢(γ) = {μ}`. -/
theorem G_lambdaSpecification_eq_singleton_of_isUniformlyMixing (ν : Measure E)
    [SigmaFinite ν] [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
    {hρ : Specification.IsPremodifier (S := S) (E := E) ρ}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ}
    (hqc : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsQuasilocal)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) {μ : Measure (S → E)}
    (hμG : μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ))
    (hmix : IsUniformlyMixing μ) :
    G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ} := by
  obtain ⟨hμP, hμ⟩ := hμG
  refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨hμP, hμ⟩, fun ν' hν' ↦ ?_⟩
  obtain ⟨hν'P, hν'G⟩ := hν'
  have := hμP
  have := hν'P
  exact eq_of_isGibbsMeasure_lambdaSpecification_of_isUniformlyMixing ν hqc hpos hμ hmix hν'G

end MeasureTheory.GibbsMeasure

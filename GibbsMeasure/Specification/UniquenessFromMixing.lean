/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Quasilocality
public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.Existence
public import GibbsMeasure.Topology.LocalConvergence
public import Mathlib.Probability.ConditionalProbability

/-!
# Georgii, Proposition (7.11): uniform mixing and uniqueness

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

**Proposition (7.11)(b)** is the converse, over a standard Borel state space, for bounded
densities and a finite `λ`: if `𝒢(γ) = {μ}` then `γ_Λ(·|ω) → μ` in the topology of local
convergence *uniformly in the boundary condition* `ω`, and `μ` satisfies (7.10).  Georgii's proof
runs through Chapter 4: assuming the uniformity fails for a local event `A`, one gets a cofinal
family of pairs `(Λ, ω)` with `|γ_Λ(A|ω) - μ(A)| > ε`; the net of finite-volume Gibbs
distributions along those pairs is locally equicontinuous (Georgii (4.11)(1)/(4.12), uniformly in
`ω` because the densities are bounded and `λ^S` is a probability measure), so it has a cluster
point (Georgii (4.9)/(4.22)), that cluster point is a Gibbs measure (Georgii (4.17)), and
uniqueness identifies it with `μ` — contradicting the `ε`-separation along the ultrafilter.

* `MeasureTheory.GibbsMeasure.abs_cond_real_sub_le_of_forall_abs_le`: the converse of
  `ae_abs_real_apply_sub_le_of_forall_cond_abs_le`, which turns the uniform bound into (7.10).
* `MeasureTheory.GibbsMeasure.eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq`,
  `MeasureTheory.GibbsMeasure.tendsto_iSup_ofReal_abs_real_apply_sub_of_forall_isGibbsMeasure_eq`,
  `MeasureTheory.GibbsMeasure.tendsto_finiteVolumeDistributions_of_forall_mem_GP_eq`,
  `MeasureTheory.GibbsMeasure.isUniformlyMixing_of_forall_isGibbsMeasure_eq`:
  **Georgii, Proposition (7.11)(b)**, for any quasilocal specification whose kernels are
  dominated on each finite volume by a finite measure uniformly in the boundary condition.
* `MeasureTheory.GibbsMeasure.exists_forall_abs_integral_sub_le_of_forall_abs_measureReal_sub_le`:
  **Georgii, Remark (4.3)(2)** made quantitative — a bounded local observable is tested by
  *finitely many* local events — and hence
  `MeasureTheory.GibbsMeasure.eventually_forall_abs_integral_sub_le_of_forall_isGibbsMeasure_eq`
  and
  `MeasureTheory.GibbsMeasure.tendsto_iSup_ofReal_abs_integral_sub_of_forall_isGibbsMeasure_eq`:
  the same uniformity for `sup_ω |γ_Λ(f|ω) - μ(f)|`, `f ∈ 𝓛`.
* `Specification.modification_apply_le_smul_of_hasFreeMeasure`,
  `Specification.exists_isFiniteMeasure_modification_apply_le`,
  `Specification.exists_isFiniteMeasure_modification_isssd_apply_le`,
  `Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le`: that domination, for
  bounded densities over any reference specification with a finite free measure — in particular
  over a probability a priori measure.
* `MeasureTheory.GibbsMeasure.G_lambdaSpecification_eq_singleton_iff_isUniformlyMixing` and
  `MeasureTheory.GibbsMeasure.G_lambdaSpecification_eq_singleton_iff_isUniformlyMixing_of_isFiniteMeasure`:
  **Georgii, Proposition (7.11)** as an equivalence — for a quasilocal λ-specification with
  positive bounded densities over a standard Borel state space, (7.10) holds for a Gibbs measure
  exactly when it is the unique one.
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
    change μ.real A + ε + ((n : ℝ) + 1)⁻¹ ≤ (γ Λ η).real A
    linarith
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < μ.real A - (γ Λ η).real A - ε by
      linarith)
    rw [one_div] at hn
    refine Set.mem_iUnion.2 ⟨n, Set.mem_union_right _ ?_⟩
    change (γ Λ η).real A ≤ μ.real A - ε - ((n : ℝ) + 1)⁻¹
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
    change (∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(γ Λ η)) = _
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

/-- **Georgii, Remark (1.28)(2), the kernel step.**  A λ-specification with *positive*
densities has the same null sets as its reference kernel: `γ_Δ(·|η) = ρ_Δ λ_Δ(·|η)` and
`λ_Δ(·|η)` are equivalent, for every volume `Δ` and every boundary condition `η`.  This is the
form used in Georgii's definition of a *quasi-Gibbsian* random field in §18.1. -/
theorem lambdaSpecification_apply_eq_zero_iff (hpos : ∀ Λ η, ρ Λ η ≠ 0)
    (Δ : Finset S) (η : S → E) (C : Set (S → E)) :
    lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Δ η C = 0 ↔
      sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η C = 0 := by
  rw [lambdaSpecification_apply, withDensity_apply_eq_zero
    (sigmaFinitePremodifierNorm_measurable (S := S) (E := E) ν hρ Δ)]
  have huniv : {σ | sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Δ σ ≠ 0} = Set.univ := by
    refine Set.eq_univ_of_forall fun σ ↦ ?_
    change sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Δ σ ≠ 0
    rw [sigmaFinitePremodifierNorm]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨hpos Δ σ, hZ.ne_top Δ σ⟩
  rw [huniv, Set.univ_inter]

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
  have hker : ∀ η, γ Δ η C = 0 ↔ sigmaFiniteLambdaFun (S := S) (E := E) ν Δ η C = 0 :=
    fun η ↦ lambdaSpecification_apply_eq_zero_iff ν hpos Δ η C
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

/-! ### Georgii, Proposition (7.11)(b)

Georgii's converse: for a quasilocal λ-specification over a standard Borel state space with
bounded densities and a finite a priori measure, uniqueness of the Gibbs measure forces the
finite-volume Gibbs distributions to converge to it *uniformly in the boundary condition*, and
the limit then satisfies (7.10).

The proof is Georgii's: suppose `sup_ω |γ_Λ(A|ω) - μ(A)|` does not tend to `0` for some local
event `A`.  Then along a cofinal set of volumes there is a boundary condition witnessing
`|γ_Λ(A|ω) - μ(A)| > ε`.  Indexing by the *pairs* `(Λ, ω)` (Georgii's sequences `(Λ_n, ω^n)`) and
filtering by the witnessing set, local equicontinuity (Georgii (4.11)(1) uniformly in `ω`, which
bounded densities and a probability a priori measure supply) plus Georgii (4.9)/(4.12) produce a
cluster point of the net `γ_Λ(·|ω)`, Georgii (4.17) makes it a Gibbs measure, and uniqueness
identifies it with `μ` — contradicting `|γ_Λ(A|ω) - μ(A)| > ε` along the ultrafilter.
-/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {μ : Measure (S → E)}

/-- **Converse of `ae_abs_real_apply_sub_le_of_forall_cond_abs_le`**, the second half of Georgii's
proof of (7.11)(b): if `γ_Λ(A|·)` is within `ε` of `μ(A)` for *every* boundary condition, then
conditioning `μ` on any non-null event outside `Λ` moves `μ(A)` by at most `ε`.  This is the
display `μ(A|B) = μ(B)⁻¹ ∫_B γ_Λ(A|·) dμ` of Georgii's proof. -/
theorem abs_cond_real_sub_le_of_forall_abs_le [IsFiniteMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) {Λ : Finset S} {A : Set (S → E)} (hA : MeasurableSet A) {ε : ℝ}
    (h : ∀ ω, |(γ Λ ω).real A - μ.real A| ≤ ε)
    {B : Set (S → E)} (hB : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] B)
    (hB0 : μ B ≠ 0) :
    |(μ[|B]).real A - μ.real A| ≤ ε := by
  refine abs_le.2 ⟨?_, ?_⟩
  · have hlow : ∀ η ∈ B, μ.real A - ε ≤ (γ Λ η).real A := fun η _ ↦ by
      have := (abs_le.1 (h η)).1; linarith
    rcases le_or_gt 0 (μ.real A - ε) with hc | hc
    · have := le_cond_real_of_isGibbsMeasure hμ hA hB hB0 hc hlow
      linarith
    · have := measureReal_nonneg (μ := μ[|B]) (s := A)
      linarith
  · have hup : ∀ η ∈ B, (γ Λ η).real A ≤ μ.real A + ε := fun η _ ↦ by
      have := (abs_le.1 (h η)).2; linarith
    have := cond_real_le_of_isGibbsMeasure hμ hA hB hB0 hup
    linarith

/-- **Georgii, Remark (4.3)(2), quantitatively.**  Testing the topology of local convergence
against a bounded local *observable* `f ∈ 𝓛` reduces to testing it against *finitely many* local
*events*: given `ε > 0` there are a finite set `Y` of values, a family `A` of local events indexed
by them, and a tolerance `δ > 0` such that every probability measure `ν` with
`|ν(A y) - μ(A y)| ≤ δ` for all `y ∈ Y` already satisfies `|ν(f) - μ(f)| ≤ ε`.

This is Georgii's step function `g = ∑ a_k 1_{A_k} ∈ 𝓛_Λ` with `‖f - g‖` small: `f` is a uniform
limit of `𝓕_Λ`-simple functions (`MeasureTheory.exists_simpleFunc_dist_le`), and a simple function
integrates to a finite sum of measures of its fibres.  Because the reduction is to *finitely many*
events, it transports uniformity in a parameter — which is what Proposition (7.11)(b) needs. -/
theorem exists_forall_abs_integral_sub_le_of_forall_abs_measureReal_sub_le
    [IsProbabilityMeasure μ] {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Y : Finset ℝ) (A : ℝ → Set (S → E)) (δ : ℝ), 0 < δ ∧
      (∀ y, A y ∈ localEvents S E) ∧
      ∀ ν : Measure (S → E), IsProbabilityMeasure ν →
        (∀ y ∈ Y, |ν.real (A y) - μ.real (A y)| ≤ δ) →
        |(∫ x, (f : (S → E) → ℝ) x ∂ν) - ∫ x, (f : (S → E) → ℝ) x ∂μ| ≤ ε := by
  classical
  obtain ⟨Δ, hΔ⟩ := mem_localFunctions.1 hf
  have hmΔ : Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] (⇑f) :=
    mem_localFunctionsOn.1 hΔ
  have hmle : cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
      ≤ (inferInstance : MeasurableSpace (S → E)) := cylinderEvents_le_pi
  obtain ⟨g, hg⟩ := exists_simpleFunc_dist_le
    (m := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)) hmΔ (C := ‖f‖)
    (fun x ↦ by simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f x)
    (by positivity : (0 : ℝ) < ε / 4)
  have hfmeas : Measurable (⇑f) := hmΔ.mono hmle le_rfl
  have hgmeas : Measurable (⇑g : (S → E) → ℝ) :=
    (@SimpleFunc.measurable _ _ (cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)) _ g).mono
      hmle le_rfl
  set gL : lp (fun _ : S → E ↦ ℝ) ∞ := ⟨(⇑g : (S → E) → ℝ), memℓp_simpleFunc g⟩ with hgL
  set Y : Finset ℝ := @SimpleFunc.range _ _ (cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)) g
    with hY
  set A : ℝ → Set (S → E) := fun y ↦ (⇑g : (S → E) → ℝ) ⁻¹' {y} with hA
  refine ⟨Y, A, (ε / 2) / (1 + ∑ y ∈ Y, |y|), by positivity, fun y ↦ ?_, ?_⟩
  · exact mem_localEvents_of_cylinderEvents Δ (@SimpleFunc.measurableSet_fiber _ _
      (cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)) g y)
  · intro ν hν hclose
    have hbound : ∀ ρ : Measure (S → E), IsProbabilityMeasure ρ →
        |(∫ x, (f : (S → E) → ℝ) x ∂ρ) - ∑ y ∈ Y, ρ.real (A y) • y| ≤ ε / 4 := by
      intro ρ hρ
      have hfint : Integrable (⇑f) ρ := lp.integrable_of_measurable hfmeas ρ
      have hgint : Integrable (⇑g : (S → E) → ℝ) ρ :=
        lp.integrable_of_measurable (f := gL) hgmeas ρ
      have hsum : ∫ x, (⇑g : (S → E) → ℝ) x ∂ρ = ∑ y ∈ Y, ρ.real (A y) • y :=
        integral_simpleFunc_larger_space hmle g hgint
      rw [← hsum, ← integral_sub hfint hgint]
      have h := norm_integral_le_of_norm_le_const (μ := ρ) (C := ε / 4)
        (f := fun x ↦ (f : (S → E) → ℝ) x - (⇑g : (S → E) → ℝ) x)
        (.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hg x)
      simpa [Real.norm_eq_abs] using h
    have hmid : |∑ y ∈ Y, ν.real (A y) • y - ∑ y ∈ Y, μ.real (A y) • y| ≤ ε / 2 := by
      have hrw : ∑ y ∈ Y, ν.real (A y) • y - ∑ y ∈ Y, μ.real (A y) • y
          = ∑ y ∈ Y, (ν.real (A y) - μ.real (A y)) * y := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun y _ ↦ by ring
      rw [hrw]
      calc |∑ y ∈ Y, (ν.real (A y) - μ.real (A y)) * y|
          ≤ ∑ y ∈ Y, |(ν.real (A y) - μ.real (A y)) * y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ Y, (ε / 2) / (1 + ∑ z ∈ Y, |z|) * |y| := by
            refine Finset.sum_le_sum fun y hy ↦ ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hclose y hy) (abs_nonneg _)
        _ = (ε / 2) / (1 + ∑ z ∈ Y, |z|) * ∑ y ∈ Y, |y| := by rw [Finset.mul_sum]
        _ ≤ ε / 2 := by
            have hT : (0 : ℝ) ≤ ∑ z ∈ Y, |z| := Finset.sum_nonneg fun z _ ↦ abs_nonneg z
            rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
            nlinarith [hε.le]
    have h1 := hbound ν hν
    have h2 := hbound μ inferInstance
    calc |(∫ x, (f : (S → E) → ℝ) x ∂ν) - ∫ x, (f : (S → E) → ℝ) x ∂μ|
        ≤ |(∫ x, (f : (S → E) → ℝ) x ∂ν) - ∑ y ∈ Y, ν.real (A y) • y|
            + |∑ y ∈ Y, ν.real (A y) • y - ∫ x, (f : (S → E) → ℝ) x ∂μ| := abs_sub_le _ _ _
      _ ≤ |(∫ x, (f : (S → E) → ℝ) x ∂ν) - ∑ y ∈ Y, ν.real (A y) • y|
            + (|∑ y ∈ Y, ν.real (A y) • y - ∑ y ∈ Y, μ.real (A y) • y|
              + |∑ y ∈ Y, μ.real (A y) • y - ∫ x, (f : (S → E) → ℝ) x ∂μ|) := by
            gcongr; exact abs_sub_le _ _ _
      _ ≤ ε / 4 + (ε / 2 + ε / 4) := by
            gcongr
            · rw [abs_sub_comm]; exact h2
      _ = ε := by ring

section UniformLimit

variable [StandardBorelSpace E] (hqc : γ.IsQuasilocal)
  (hdom : ∀ Λ : Finset S, ∃ κ : Measure (S → E), IsFiniteMeasure κ ∧
    ∀ (ω : S → E) ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A → γ Λ ω A ≤ κ A)

include hqc hdom

/-- **Georgii, Proposition (7.11)(b), first half** (the abstract core): let `γ` be a quasilocal
specification over a standard Borel state space whose kernels are, on each finite volume `Λ`,
dominated by a finite measure *uniformly in the boundary condition* (Georgii's hypothesis of
bounded densities and finite `λ`, in the form of his Example (4.11)(1)).  If every Gibbs
probability measure of `γ` equals `μ`, then for every local event `A` and every `ε > 0` all large
enough volumes satisfy `|γ_Λ(A|ω) - μ(A)| ≤ ε` for **every** boundary condition `ω`.

Note that `μ ∈ 𝒢(γ)` is *not* assumed: the compactness argument produces a Gibbs measure, so the
uniqueness hypothesis is never vacuous. -/
theorem eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq
    [IsProbabilityMeasure μ]
    (huniq : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν → ν = μ)
    {A : Set (S → E)} (hA : A ∈ localEvents S E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : Finset S in atTop, ∀ ω : S → E, |(γ Λ ω).real A - μ.real A| ≤ ε := by
  choose κ hκfin hκ using hdom
  have : ∀ Λ, IsFiniteMeasure (κ Λ) := hκfin
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- Georgii's sequences `(Λ_n, ω^n)`: the set of pairs witnessing the failure …
  set T : Set (Finset S × (S → E)) := {p | ε < |(γ p.1 p.2).real A - μ.real A|} with hTdef
  have hfreq : ∀ Λ₀ : Finset S, ∃ Λ, Λ₀ ≤ Λ ∧ ∃ ω, (Λ, ω) ∈ T := by
    intro Λ₀
    obtain ⟨Λ, hΛ, hbad⟩ := frequently_atTop.1 hcon Λ₀
    obtain ⟨ω, hω⟩ := not_forall.1 hbad
    exact ⟨Λ, hΛ, ω, not_le.1 hω⟩
  -- … and the filter along which the volumes exhaust `S` inside that set.
  set l : Filter (Finset S × (S → E)) := comap Prod.fst atTop ⊓ 𝓟 T with hldef
  have hlne : l.NeBot := by
    rw [hldef, inf_principal_neBot_iff]
    intro U hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨Λ₀, hΛ₀⟩ := mem_atTop_sets.1 hV
    obtain ⟨Λ, hΛ, ω, hω⟩ := hfreq Λ₀
    exact ⟨(Λ, ω), hVU (hΛ₀ Λ hΛ), hω⟩
  have hΛs : Tendsto (Prod.fst : Finset S × (S → E) → Finset S) l atTop := by
    rw [hldef]; exact tendsto_comap.mono_left inf_le_left
  set νs : Finset S × (S → E) → ProbabilityMeasure (S → E) :=
    fun p ↦ ⟨Measure.dirac p.2, inferInstance⟩ with hνsdef
  have hdirac : ∀ p : Finset S × (S → E),
      γ.bindPM p.1 (νs p) = finiteVolumeDistributions γ p.2 p.1 := fun p ↦
    Subtype.ext (Measure.dirac_bind (γ.measurable_kernel_toMeasure p.1) p.2)
  -- Georgii (4.11)(1): the net is locally equicontinuous, by consistency and the domination.
  have hle : LocallyEquicontinuous l (fun p ↦ γ.bindPM p.1 (νs p)) := by
    refine locallyEquicontinuous_of_eventually_le κ fun Λ ↦ ?_
    filter_upwards [hΛs.eventually_ge_atTop Λ] with p hp A' hA'
    rw [hdirac p]
    exact finiteVolumeDistributions_apply_le hp p.2 (cylinderEvents_le_pi _ hA')
      fun ω ↦ hκ Λ ω hA'
  -- Georgii (4.12) + (4.17): a cluster point exists and is a Gibbs measure.
  obtain ⟨νlim, hνGP, hcp⟩ := exists_mem_GP_mapClusterPt (l := l) hqc
    (γs := fun _ ↦ γ) (Λs := Prod.fst) (νs := νs) hΛs (fun Λ f _ ↦ by simp) hle
  obtain ⟨U, hU, hUconv⟩ := mapClusterPt_iff_ultrafilter.1 hcp
  have hνμ : (νlim : Measure (S → E)) = μ := huniq _ inferInstance hνGP
  have heval : Tendsto (fun p : Finset S × (S → E) ↦ (γ p.1 p.2) A) (U : Filter _) (𝓝 (μ A)) := by
    have h := tendsto_withLocalConvergence_iff.1 hUconv A hA
    simp only [hdirac, hνμ] at h
    exact h
  have hreal : Tendsto (fun p : Finset S × (S → E) ↦ (γ p.1 p.2).real A) (U : Filter _)
      (𝓝 (μ.real A)) := by
    simp only [measureReal_def]
    exact (ENNReal.tendsto_toReal (measure_ne_top μ A)).comp heval
  have h0 : Tendsto (fun p : Finset S × (S → E) ↦ |(γ p.1 p.2).real A - μ.real A|)
      (U : Filter _) (𝓝 0) := by
    simpa using (hreal.sub (tendsto_const_nhds (x := μ.real A))).abs
  have hTU : T ∈ (U : Filter (Finset S × (S → E))) := by
    refine Filter.le_def.1 hU T ?_
    rw [hldef]
    exact le_principal_iff.1 inf_le_right
  obtain ⟨p, hp1, hp2⟩ :=
    ((eventually_of_mem hTU fun p hp ↦ hp).and (h0.eventually_lt_const hε)).exists
  exact absurd hp1 (not_lt.2 hp2.le)

/-- **Georgii, Proposition (7.11)(b)** as the book displays the uniformity:
`lim_Λ sup_ω |γ_Λ(A|ω) - μ(A)| = 0` for every local event `A`. -/
theorem tendsto_iSup_ofReal_abs_real_apply_sub_of_forall_isGibbsMeasure_eq
    [IsProbabilityMeasure μ]
    (huniq : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν → ν = μ)
    {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    Tendsto (fun Λ : Finset S ↦ ⨆ ω : S → E, ENNReal.ofReal |(γ Λ ω).real A - μ.real A|)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun Λ ↦ le_top
  · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    filter_upwards [eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq
      hqc hdom huniq hA hεr] with Λ hΛ
    refine iSup_le fun ω ↦ ?_
    rw [← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal (hΛ ω)

/-- **Georgii, Proposition (7.11)(b), tested on local observables.**  Georgii's `𝓛`-topology is
generated by the evaluations `ν ↦ ν(f)` at bounded local observables `f ∈ 𝓛` just as well as by
the evaluations at local events (Remark (4.3)(2)), and the uniformity in the boundary condition
survives that translation: for every `f ∈ 𝓛` and every `ε > 0` all large enough volumes satisfy
`|γ_Λ(f|ω) - μ(f)| ≤ ε` for **every** `ω`.

The reduction is the quantitative form of Remark (4.3)(2),
`exists_forall_abs_integral_sub_le_of_forall_abs_measureReal_sub_le`: `f` is uniformly close to a
step function over *finitely many* local events, and a finite family of eventualities is again
eventual. -/
theorem eventually_forall_abs_integral_sub_le_of_forall_isGibbsMeasure_eq
    [IsProbabilityMeasure μ]
    (huniq : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν → ν = μ)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : Finset S in atTop, ∀ ω : S → E,
      |(∫ x, (f : (S → E) → ℝ) x ∂(γ Λ ω)) - ∫ x, (f : (S → E) → ℝ) x ∂μ| ≤ ε := by
  obtain ⟨Y, A, δ, hδ, hAloc, hkey⟩ :=
    exists_forall_abs_integral_sub_le_of_forall_abs_measureReal_sub_le (μ := μ) hf hε
  have h : ∀ y ∈ Y, ∀ᶠ Λ : Finset S in atTop, ∀ ω : S → E,
      |(γ Λ ω).real (A y) - μ.real (A y)| ≤ δ := fun y _ ↦
    eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq hqc hdom huniq
      (hAloc y) hδ
  filter_upwards [(Filter.eventually_all_finset (I := Y)).2 h] with Λ hΛ ω
  exact hkey (γ Λ ω) inferInstance fun y hy ↦ hΛ y hy ω

/-- **Georgii, Proposition (7.11)(b)**, the uniformity as the book displays it, tested on local
observables: `lim_Λ sup_ω |γ_Λ(f|ω) - μ(f)| = 0` for every `f ∈ 𝓛`. -/
theorem tendsto_iSup_ofReal_abs_integral_sub_of_forall_isGibbsMeasure_eq
    [IsProbabilityMeasure μ]
    (huniq : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν → ν = μ)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    Tendsto (fun Λ : Finset S ↦ ⨆ ω : S → E, ENNReal.ofReal
        |(∫ x, (f : (S → E) → ℝ) x ∂(γ Λ ω)) - ∫ x, (f : (S → E) → ℝ) x ∂μ|)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · exact Eventually.of_forall fun Λ ↦ le_top
  · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    filter_upwards [eventually_forall_abs_integral_sub_le_of_forall_isGibbsMeasure_eq
      hqc hdom huniq hf hεr] with Λ hΛ
    refine iSup_le fun ω ↦ ?_
    rw [← ENNReal.ofReal_toReal hεtop]
    exact ENNReal.ofReal_le_ofReal (hΛ ω)

/-- **Georgii, Proposition (7.11)(b)**, `γ_Λ(·|ω) →^𝓛 μ`: for a unique Gibbs measure the whole net
of finite-volume Gibbs distributions converges in the topology of local convergence, from *every*
boundary condition (compare Georgii (8.23)(ii),
`MeasureTheory.GibbsMeasure.Dobrushin.tendsto_finiteVolumeDistributions_of_isDobrushin`). -/
theorem tendsto_finiteVolumeDistributions_of_forall_mem_GP_eq
    {μ : ProbabilityMeasure (S → E)} (huniq : ∀ ν ∈ GP (S := S) (E := E) γ, ν = μ) (ω : S → E) :
    Tendsto (fun Λ : Finset S ↦ (WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ ω Λ) :
      WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) := by
  have huniq' : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν →
      ν = (μ : Measure (S → E)) := fun ν hν hG ↦
    congrArg (fun x : ProbabilityMeasure (S → E) ↦ (x : Measure (S → E))) (huniq ⟨ν, hν⟩ hG)
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  have hreal : Tendsto (fun Λ : Finset S ↦ (γ Λ ω).real A) atTop
      (𝓝 ((μ : Measure (S → E)).real A)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq
      hqc hdom huniq' hA (half_pos hε)] with Λ hΛ
    have h := hΛ ω
    rw [Real.dist_eq]
    linarith
  have hcast : ∀ Λ : Finset S,
      ((WithSetwiseTopology.ofMeasure (finiteVolumeDistributions γ ω Λ) :
          WithLocalConvergence S E).toMeasure : Measure (S → E)) A
        = ENNReal.ofReal ((γ Λ ω).real A) :=
    fun Λ ↦ (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hgoal : ((WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E).toMeasure :
      Measure (S → E)) A = ENNReal.ofReal ((μ : Measure (S → E)).real A) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  simp only [hcast]
  rw [hgoal]
  exact ENNReal.tendsto_ofReal hreal

/-- **Georgii, Proposition (7.11)(b), second half**: the unique Gibbs measure satisfies the mixing
property (7.10).  Together with `eq_of_isGibbsMeasure_of_isUniformlyMixing` this closes the loop:
for such specifications, (7.10) *characterizes* uniqueness. -/
theorem isUniformlyMixing_of_forall_isGibbsMeasure_eq [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ)
    (huniq : ∀ ν : Measure (S → E), IsProbabilityMeasure ν → γ.IsGibbsMeasure ν → ν = μ) :
    IsUniformlyMixing μ := by
  refine isUniformlyMixing_of_forall_exists fun A hA ε hε ↦ ?_
  obtain ⟨Λ, hΛ⟩ := (eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq
    hqc hdom huniq hA hε).exists
  exact ⟨Λ, fun B hB hB0 ↦ abs_cond_real_sub_le_of_forall_abs_le hμ
    (MeasurableSet.of_mem_measurableCylinders hA) hΛ hB hB0⟩

end UniformLimit

end MeasureTheory.GibbsMeasure

/-! ### The domination hypothesis of (7.11)(b) for bounded densities -/

namespace Specification

variable {S E : Type*} {mE : MeasurableSpace E}

/-- **Georgii, Example (4.11)(1) / Comment (4.14)(1), uniformly in the boundary condition.** A
modification whose densities are bounded by `C Λ` on the volume `Λ` is dominated on `𝓕_Λ` by
`C Λ · μ₀`, for every boundary condition, as soon as the reference specification has free measure
`μ₀` — Georgii's `λ_Λ(A | η) = λ^S(A)` for `A ∈ 𝓕_Λ`.  The homogeneous independent specification
(`Specification.hasFreeMeasure_isssd`) and the inhomogeneous one
(`Specification.hasFreeMeasure_isssdFamily`) are the two examples. -/
lemma modification_apply_le_smul_of_hasFreeMeasure {γ₀ : Specification S E}
    {μ₀ : Measure (S → E)} (h₀ : γ₀.HasFreeMeasure μ₀)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : γ₀.IsModifier ρ)
    {C : Finset S → ℝ≥0∞} (hbdd : ∀ Λ σ, ρ Λ σ ≤ C Λ) (Λ : Finset S) (ω : S → E)
    {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A) :
    γ₀.modification ρ hρ Λ ω A ≤ (C Λ • μ₀) A := by
  rw [Measure.smul_apply, smul_eq_mul]
  calc γ₀.modification ρ hρ Λ ω A ≤ C Λ * γ₀ Λ ω A :=
        modification_apply_le _ ρ hρ Λ ω (cylinderEvents_le_pi _ hA) fun σ ↦ hbdd Λ σ
    _ = C Λ * μ₀ A := by rw [h₀ Λ ω hA]

/-- The domination hypothesis of Georgii (7.11)(b), for a modification with bounded densities of
a reference specification with a finite free measure. -/
lemma exists_isFiniteMeasure_modification_apply_le {γ₀ : Specification S E}
    {μ₀ : Measure (S → E)} [IsFiniteMeasure μ₀] (h₀ : γ₀.HasFreeMeasure μ₀)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : γ₀.IsModifier ρ)
    {C : Finset S → ℝ≥0∞} (hC : ∀ Λ, C Λ ≠ ∞) (hbdd : ∀ Λ σ, ρ Λ σ ≤ C Λ) (Λ : Finset S) :
    ∃ κ : Measure (S → E), IsFiniteMeasure κ ∧ ∀ (ω : S → E) ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
        γ₀.modification ρ hρ Λ ω A ≤ κ A := by
  refine ⟨C Λ • μ₀, ⟨?_⟩, fun ω _A hA ↦
    modification_apply_le_smul_of_hasFreeMeasure h₀ hρ hbdd Λ ω hA⟩
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (hC Λ).lt_top (measure_lt_top μ₀ _)

/-- The domination hypothesis of Georgii (7.11)(b), for a modification of the independent
specification with bounded densities. -/
lemma exists_isFiniteMeasure_modification_isssd_apply_le (ν : Measure E) [IsProbabilityMeasure ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : (isssd (S := S) (E := E) ν).IsModifier ρ)
    {C : Finset S → ℝ≥0∞} (hC : ∀ Λ, C Λ ≠ ∞) (hbdd : ∀ Λ σ, ρ Λ σ ≤ C Λ) (Λ : Finset S) :
    ∃ κ : Measure (S → E), IsFiniteMeasure κ ∧ ∀ (ω : S → E) ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
        (isssd (S := S) (E := E) ν).modification ρ hρ Λ ω A ≤ κ A :=
  exists_isFiniteMeasure_modification_apply_le (hasFreeMeasure_isssd ν) hρ hC hbdd Λ

/-- The domination hypothesis of Georgii (7.11)(b), for a λ-specification with bounded normalized
densities over a probability a priori measure. -/
lemma exists_isFiniteMeasure_lambdaSpecification_apply_le (ν : Measure E)
    [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifier ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ) {C : Finset S → ℝ≥0∞}
    (hC : ∀ Λ, C Λ ≠ ∞)
    (hbdd : ∀ Λ σ, sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ σ ≤ C Λ) (Λ : Finset S) :
    ∃ κ : Measure (S → E), IsFiniteMeasure κ ∧ ∀ (ω : S → E) ⦃A : Set (S → E)⦄,
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)] A →
        lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω A ≤ κ A := by
  rw [lambdaSpecification_eq_modification_isssd ν hρ hZ]
  refine exists_isFiniteMeasure_modification_isssd_apply_le ν _ hC (fun Λ' σ ↦ ?_) Λ
  rw [premodifierNorm_eq_sigmaFinitePremodifierNorm]
  exact hbdd Λ' σ

end Specification

/-! ### Georgii, Proposition (7.11) for λ-specifications: (7.10) is equivalent to uniqueness -/

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} {mE : MeasurableSpace E} [StandardBorelSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
  {hρ : Specification.IsPremodifier (S := S) (E := E) ρ}
  {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν ρ}

section LambdaSpec

variable (hqc : (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ).IsQuasilocal)
  {C : Finset S → ℝ≥0∞} (hC : ∀ Λ, C Λ ≠ ∞)
  (hbdd : ∀ Λ σ, Specification.sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ σ ≤ C Λ)

include hqc hC hbdd

/-- **Georgii, Proposition (7.11)(b)** for a λ-specification `γ = ρ λ` with bounded densities over
a probability a priori measure: `𝒢(γ) = {μ}` implies `γ_Λ(·|ω) → μ` uniformly in `ω`. -/
theorem eventually_forall_abs_real_apply_sub_le_lambdaSpecification_of_G_eq_singleton
    {μ : Measure (S → E)}
    (hG : G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ})
    {A : Set (S → E)} (hA : A ∈ localEvents S E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Λ : Finset S in atTop, ∀ ω : S → E,
      |(Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω).real A
        - μ.real A| ≤ ε := by
  have hμmem : μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) := by
    rw [hG]; exact Set.mem_singleton μ
  have hμP : IsProbabilityMeasure μ := hμmem.1
  exact eventually_forall_abs_real_apply_sub_le_of_forall_isGibbsMeasure_eq hqc
    (Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le ν hρ hZ hC hbdd)
    (fun ν' hν' hG' ↦ Set.mem_singleton_iff.1 (hG ▸ (⟨hν', hG'⟩ :
      ν' ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)))) hA hε

/-- **Georgii, Proposition (7.11)(b)** for a λ-specification, in the book's display
`lim_Λ sup_ω |γ_Λ(A|ω) - μ(A)| = 0`. -/
theorem tendsto_iSup_ofReal_abs_real_apply_sub_lambdaSpecification_of_G_eq_singleton
    {μ : Measure (S → E)}
    (hG : G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ})
    {A : Set (S → E)} (hA : A ∈ localEvents S E) :
    Tendsto (fun Λ : Finset S ↦ ⨆ ω : S → E, ENNReal.ofReal
        |(Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω).real A
          - μ.real A|) atTop (𝓝 0) := by
  have hμmem : μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) := by
    rw [hG]; exact Set.mem_singleton μ
  have hμP : IsProbabilityMeasure μ := hμmem.1
  exact tendsto_iSup_ofReal_abs_real_apply_sub_of_forall_isGibbsMeasure_eq hqc
    (Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le ν hρ hZ hC hbdd)
    (fun ν' hν' hG' ↦ Set.mem_singleton_iff.1 (hG ▸ (⟨hν', hG'⟩ :
      ν' ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)))) hA

/-- **Georgii, Proposition (7.11)(b)** for a λ-specification, tested on local observables:
`lim_Λ sup_ω |γ_Λ(f|ω) - μ(f)| = 0` for every `f ∈ 𝓛`. -/
theorem tendsto_iSup_ofReal_abs_integral_sub_lambdaSpecification_of_G_eq_singleton
    {μ : Measure (S → E)}
    (hG : G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ})
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    Tendsto (fun Λ : Finset S ↦ ⨆ ω : S → E, ENNReal.ofReal
        |(∫ x, (f : (S → E) → ℝ) x
            ∂(Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ Λ ω))
          - ∫ x, (f : (S → E) → ℝ) x ∂μ|) atTop (𝓝 0) := by
  have hμmem : μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) := by
    rw [hG]; exact Set.mem_singleton μ
  have hμP : IsProbabilityMeasure μ := hμmem.1
  exact tendsto_iSup_ofReal_abs_integral_sub_of_forall_isGibbsMeasure_eq hqc
    (Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le ν hρ hZ hC hbdd)
    (fun ν' hν' hG' ↦ Set.mem_singleton_iff.1 (hG ▸ (⟨hν', hG'⟩ :
      ν' ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ)))) hf

/-- **Georgii, Proposition (7.11)(b)**, local convergence form: the unique Gibbs measure of a
λ-specification with bounded densities is the local limit of `γ_Λ(·|ω)` for every `ω`. -/
theorem tendsto_finiteVolumeDistributions_lambdaSpecification_of_GP_eq_singleton
    {μ : ProbabilityMeasure (S → E)}
    (hGP : GP (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ})
    (ω : S → E) :
    Tendsto (fun Λ : Finset S ↦ (WithSetwiseTopology.ofMeasure
        (finiteVolumeDistributions
          (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) ω Λ) :
      WithLocalConvergence S E)) atTop (𝓝 (WithSetwiseTopology.ofMeasure μ)) :=
  tendsto_finiteVolumeDistributions_of_forall_mem_GP_eq hqc
    (Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le ν hρ hZ hC hbdd)
    (fun _ν' hν' ↦ Set.mem_singleton_iff.1 (hGP ▸ hν')) ω

/-- **Georgii, Proposition (7.11)(b), second half** for a λ-specification: the unique Gibbs measure
satisfies (7.10). -/
theorem isUniformlyMixing_of_G_lambdaSpecification_eq_singleton {μ : Measure (S → E)}
    (hG : G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ}) :
    IsUniformlyMixing μ := by
  have hμmem : μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) := by
    rw [hG]; exact Set.mem_singleton μ
  have hμP : IsProbabilityMeasure μ := hμmem.1
  exact isUniformlyMixing_of_forall_isGibbsMeasure_eq hqc
    (Specification.exists_isFiniteMeasure_lambdaSpecification_apply_le ν hρ hZ hC hbdd)
    hμmem.2 (fun ν' hν' hG' ↦ Set.mem_singleton_iff.1 (hG ▸ (⟨hν', hG'⟩ :
      ν' ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ))))

/-- **Georgii, Proposition (7.11)** as an equivalence.  For a quasilocal λ-specification `γ = ρ λ`
over a standard Borel state space, with *positive* and *bounded* densities and a probability a
priori measure, Georgii's mixing property (7.10) holds for some Gibbs measure `μ` exactly when `μ`
is the only one:

* `←` is Proposition (7.11)(a), `G_lambdaSpecification_eq_singleton_of_isUniformlyMixing`;
* `→` is Proposition (7.11)(b), `isUniformlyMixing_of_G_lambdaSpecification_eq_singleton`. -/
theorem G_lambdaSpecification_eq_singleton_iff_isUniformlyMixing
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) {μ : Measure (S → E)} :
    G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) = {μ} ↔
      μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) ν ρ hρ hZ) ∧
        IsUniformlyMixing μ := by
  refine ⟨fun hG ↦ ⟨by rw [hG]; exact Set.mem_singleton μ,
    isUniformlyMixing_of_G_lambdaSpecification_eq_singleton ν hqc hC hbdd hG⟩, ?_⟩
  rintro ⟨hμG, hmix⟩
  exact G_lambdaSpecification_eq_singleton_of_isUniformlyMixing ν hqc hpos hμG hmix

end LambdaSpec

/-- **Georgii, Proposition (7.11)** at Georgii's own hypotheses: a *finite* non-zero a priori
measure `λ`.  The λ-specification of a finite `λ` is the λ-specification of the normalized
`λ̃ = λ(E)⁻¹ λ` (Georgii, Remark (1.28)(3),
`Specification.lambdaSpecification_probNormalize`), and the boundedness hypothesis is stated for
the densities relative to `λ̃`. -/
theorem G_lambdaSpecification_eq_singleton_iff_isUniformlyMixing_of_isFiniteMeasure
    {S E : Type*} {mE : MeasurableSpace E} [StandardBorelSpace E]
    (lam : Measure E) [IsFiniteMeasure lam] [NeZero lam] {ρ : Finset S → (S → E) → ℝ≥0∞}
    {hρ : Specification.IsPremodifier (S := S) (E := E) ρ}
    {hZ : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam ρ}
    (hqc : (Specification.lambdaSpecification (S := S) (E := E) lam ρ hρ hZ).IsQuasilocal)
    {C : Finset S → ℝ≥0∞} (hC : ∀ Λ, C Λ ≠ ∞)
    (hbdd : ∀ Λ σ, Specification.sigmaFinitePremodifierNorm (S := S) (E := E)
      lam.probNormalize ρ Λ σ ≤ C Λ)
    (hpos : ∀ Λ η, ρ Λ η ≠ 0) {μ : Measure (S → E)} :
    G (Specification.lambdaSpecification (S := S) (E := E) lam ρ hρ hZ) = {μ} ↔
      μ ∈ G (Specification.lambdaSpecification (S := S) (E := E) lam ρ hρ hZ) ∧
        IsUniformlyMixing μ := by
  have hZ' : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := E) lam.probNormalize ρ :=
    (Specification.isSigmaFiniteLambdaAdmissible_probNormalize lam).2 hZ
  rw [Specification.lambdaSpecification_probNormalize (S := S) (E := E) lam hρ hZ hZ'] at hqc ⊢
  exact G_lambdaSpecification_eq_singleton_iff_isUniformlyMixing lam.probNormalize hqc hC hbdd hpos

end MeasureTheory.GibbsMeasure

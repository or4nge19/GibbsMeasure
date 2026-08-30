import Comparator.Defs_LocalLimit
import GibbsMeasure

/-!
# Comparator solution: local limits of extreme Gibbs measures (Georgii, Theorem (7.12))

The solution file matching `Comparator/Challenge_LocalLimit.lean`.  The `LocalLimitBridge`
namespace identifies the from-scratch definitions of `Comparator.Defs_LocalLimit` with those of
the `GibbsMeasure` library — a family satisfying the preamble's specification axioms with a
library `Specification`, `IsExtremeGibbs` with `(G γ').extremePoints ℝ≥0∞`, and a λ-specification
with a modification of the ISSSD — after which the theorems are quoted from the library.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Theorem (7.12)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section LocalLimit

variable {S E : Type*} [MeasurableSpace E]

/-! ### The bridge to the `GibbsMeasure` library -/

namespace LocalLimitBridge

open ProbabilityTheory MeasureTheory.GibbsMeasure
open scoped ENNReal

variable {S E : Type*} [MeasurableSpace E]

/-- The preamble's `𝓕_Δ` is Mathlib's cylinder σ-algebra of `Δ`. -/
lemma inside_eq_cylinderEvents (Δ : Finset S) :
    inside (S := S) (E := E) Δ = cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S) := rfl

/-- The preamble's external σ-algebra `𝓣_Λ` is Mathlib's cylinder σ-algebra of `Λᶜ`. -/
lemma outside_eq_cylinderEvents (Λ : Finset S) :
    outside (S := S) (E := E) Λ = cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := rfl

/-- The preamble's independent kernel `λ_Λ` is the library's ISSSD kernel. -/
lemma indepSpec_eq_isssd (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S)
    (ω : Config S E) : indepSpec ν Λ ω = Specification.isssd ν Λ ω := by
  have hcomp : (fun σ : Config S E ↦ glue Λ σ ω)
      = juxt (Λ : Set S) ω ∘ (Λ.restrict : Config S E → (Λ → E)) := by
    funext σ
    funext i
    by_cases hi : i ∈ Λ
    · rw [Function.comp_apply, glue_of_mem hi,
        juxt_apply_of_mem (Λ := (Λ : Set S)) (Finset.mem_coe.2 hi)]
      rfl
    · rw [Function.comp_apply, glue_of_notMem hi,
        juxt_apply_of_not_mem (Λ := (Λ : Set S)) (fun h ↦ hi (Finset.mem_coe.1 h))]
  rw [indepSpec, hcomp, ← Measure.map_map Measurable.juxt (Finset.measurable_restrict Λ),
    Measure.infinitePi_map_restrict]
  rfl

/-! #### From a family of kernels satisfying the preamble's axioms to a library `Specification` -/

variable {γ : Finset S → Config S E → Measure (Config S E)}

/-- The `Λ`-kernel of the family `γ`, as a kernel from `𝓣_Λ` to `𝓕`. -/
def ker (hγ : IsSpecification γ) (Λ : Finset S) :
    @Kernel (Config S E) (Config S E)
      (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) inferInstance :=
  @Kernel.mk (Config S E) (Config S E)
    (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) inferInstance (γ Λ)
    (Measure.measurable_measure.2 fun A hA ↦ hγ.measurable_apply Λ A hA)

@[simp] lemma ker_apply (hγ : IsSpecification γ) (Λ : Finset S) (ω : Config S E) :
    ker hγ Λ ω = γ Λ ω := rfl

instance isMarkovKernel_ker (hγ : IsSpecification γ) (Λ : Finset S) :
    IsMarkovKernel (ker hγ Λ) := ⟨fun ω ↦ hγ.isProbabilityMeasure Λ ω⟩

lemma isProper_ker (hγ : IsSpecification γ) (Λ : Finset S) : (ker hγ Λ).IsProper := by
  refine (Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi).2 ?_
  intro A hA B hB ω
  rw [ker_apply, hγ.proper Λ A B hA hB ω]
  by_cases h : ω ∈ B <;> simp [h]

lemma isConsistent_ker (hγ : IsSpecification γ) : IsConsistent (ker hγ) := by
  intro Λ₁ Λ₂ hΛ
  refine Kernel.ext fun ω ↦ Measure.ext fun A hA ↦ ?_
  rw [Kernel.comp_apply' _ _ _ hA]
  simp only [Kernel.comap_apply, ker_apply, id_eq]
  exact hγ.consistent Λ₁ Λ₂ hΛ ω A hA

/-- The library specification attached to a family satisfying the preamble's axioms. -/
def spec (hγ : IsSpecification γ) : Specification S E :=
  @Specification.mk S E _ (@PreSpecification.mk S E _ (ker hγ) (isConsistent_ker hγ))
    (fun Λ ↦ isMarkovKernel_ker hγ Λ) (fun Λ ↦ isProper_ker hγ Λ)

lemma coe_spec (hγ : IsSpecification γ) (Λ : Finset S) : ⇑(spec hγ Λ) = γ Λ := rfl

/-! #### Gibbs measures and extremality -/

lemma measurable_coe (γ' : Specification S E) (Λ : Finset S) : Measurable (⇑(γ' Λ)) :=
  (γ' Λ).measurable.mono cylinderEvents_le_pi le_rfl

/-- The DLR equations of the preamble are the library's Gibbs property, for any library
specification `γ'` whose kernels agree pointwise with `γ`. -/
lemma isGibbs_iff_mem_G {γ' : Specification S E} (h : ∀ (Λ : Finset S) (ω : Config S E),
    γ Λ ω = γ' Λ ω) (μ : Measure (Config S E)) : IsGibbs γ μ ↔ μ ∈ G γ' := by
  have hfun : ∀ Λ : Finset S, (fun ω ↦ γ Λ ω) = ⇑(γ' Λ) := fun Λ ↦ funext (h Λ)
  constructor
  · rintro ⟨hprob, hdlr⟩
    have : IsProbabilityMeasure μ := hprob
    refine ⟨hprob, ?_⟩
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
    intro Λ
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA (measurable_coe γ' Λ).aemeasurable, ← hfun Λ]
    exact (hdlr Λ A hA).symm
  · rintro ⟨hprob, hgibbs⟩
    have : IsProbabilityMeasure μ := hprob
    refine ⟨hprob, fun Λ A hA ↦ ?_⟩
    have h2 : (⇑(γ' Λ) ∘ₘ μ) A = μ A := by
      rw [(Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hgibbs) Λ]
    rw [Measure.bind_apply hA (measurable_coe γ' Λ).aemeasurable, ← hfun Λ] at h2
    exact h2.symm

/-- `IsExtremeGibbs` is the library's `(G γ').extremePoints ℝ≥0∞`. -/
lemma isExtremeGibbs_iff_mem_extremePoints {γ' : Specification S E}
    (h : ∀ (Λ : Finset S) (ω : Config S E), γ Λ ω = γ' Λ ω) (μ : Measure (Config S E)) :
    IsExtremeGibbs γ μ ↔ μ ∈ (G γ').extremePoints ℝ≥0∞ := by
  rw [mem_extremePoints]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(isGibbs_iff_mem_G h μ).1 h1, fun ν₁ hν₁ ν₂ hν₂ hseg ↦ ?_⟩
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    exact h2 ν₁ ν₂ ((isGibbs_iff_mem_G h ν₁).2 hν₁) ((isGibbs_iff_mem_G h ν₂).2 hν₂)
      a b ha hb hab heq.symm
  · rintro ⟨h1, h2⟩
    refine ⟨(isGibbs_iff_mem_G h μ).2 h1, fun ν₁ ν₂ hν₁ hν₂ a b ha hb hab heq ↦ ?_⟩
    exact h2 ν₁ ((isGibbs_iff_mem_G h ν₁).1 hν₁) ν₂ ((isGibbs_iff_mem_G h ν₂).1 hν₂)
      ⟨a, b, ha, hb, hab, heq.symm⟩

/-! #### λ-specifications are modifications of the ISSSD -/

variable {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}

lemma eq_withDensity (hγ : IsLambdaSpec ν ρ γ) (Λ : Finset S) (ω : Config S E) :
    γ Λ ω = (Specification.isssd ν Λ ω).withDensity (ρ Λ) := by
  refine Measure.ext fun A hA ↦ ?_
  rw [hγ.density_apply Λ ω A hA, withDensity_apply _ hA, indepSpec_eq_isssd]

/-- The `Λ`-kernel of the modified ISSSD is the `Λ`-kernel of the λ-specification. -/
lemma modificationKer_eq_ker (hγ : IsLambdaSpec ν ρ γ) (h : ∀ Λ : Finset S, Measurable (ρ Λ))
    (Λ : Finset S) :
    Specification.modificationKer (⇑(Specification.isssd ν)) ρ h Λ = ker hγ.isSpecification Λ :=
  Kernel.ext fun ω ↦ by
    rw [Specification.modificationKer_apply, ker_apply, ← eq_withDensity hγ]

/-- A λ-specification in the sense of Georgii (1.27) is a modification of the ISSSD. -/
lemma isModifier (hγ : IsLambdaSpec ν ρ γ) : (Specification.isssd ν).IsModifier ρ where
  measurable Λ := hγ.measurable_density Λ
  isMarkovKernel Λ := by
    rw [modificationKer_eq_ker hγ]
    infer_instance
  isProper Λ := by
    rw [modificationKer_eq_ker hγ]
    exact isProper_ker hγ.isSpecification Λ
  isConsistent := by
    have h : Specification.modificationKer (⇑(Specification.isssd ν)) ρ
        (fun Λ ↦ hγ.measurable_density Λ) = ker hγ.isSpecification :=
      funext fun Λ ↦ modificationKer_eq_ker hγ _ Λ
    rw [h]
    exact isConsistent_ker hγ.isSpecification

lemma eq_modification (hγ : IsLambdaSpec ν ρ γ) (Λ : Finset S) (ω : Config S E) :
    γ Λ ω = ((Specification.isssd ν).modification ρ (isModifier hγ)) Λ ω := by
  rw [Specification.coe_modification, Specification.modificationKer_apply,
    ← eq_withDensity hγ]

end LocalLimitBridge

/-- **Georgii, Theorem (7.12)(a)**: for an extreme Gibbs measure `μ` of `γ` and an increasing
cofinal sequence of volumes, `γ_{Λ n} f → μ(f)` `μ`-almost surely, for every bounded measurable
`f`. -/
theorem georgii_7_12_a [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {f : Config S E → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ x, f x ∂(γ (Λ n) ω)) atTop (nhds (∫ x, f x ∂μ)) := by
  have hprob : IsProbabilityMeasure μ := hμ.isGibbs.1
  have hint : Integrable f μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := C) (Filter.Eventually.of_forall fun x ↦ ?_)
    simpa [Real.norm_eq_abs] using hC x
  have hμ' : μ ∈ (MeasureTheory.GibbsMeasure.G (LocalLimitBridge.spec hγ)).extremePoints ℝ≥0∞ :=
    (LocalLimitBridge.isExtremeGibbs_iff_mem_extremePoints
      (γ' := LocalLimitBridge.spec hγ) (fun _ _ ↦ rfl) μ).1 hμ
  exact MeasureTheory.GibbsMeasure.tendsto_ae_integral_kernel_of_mem_extremePoints_G hμ' hmono
    hcof hint

/-- **Georgii, Theorem (7.12)(a)** in the form used for the tail-triviality argument:
`γ_{Λ n}(A | ω) → μ(A)` for `μ`-almost every `ω`, for every measurable event `A`. -/
theorem georgii_7_12_a_measure [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n)
    {A : Set (Config S E)} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ γ (Λ n) ω A) atTop (nhds (μ A)) := by
  have hprob : IsProbabilityMeasure μ := hμ.isGibbs.1
  have hmeas : Measurable (A.indicator (1 : Config S E → ℝ)) := measurable_one.indicator hA
  have hbdd : ∀ x, |A.indicator (1 : Config S E → ℝ) x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have key := georgii_7_12_a hγ hμ hmono hcof hmeas hbdd
  have hcalc : ∀ m : Measure (Config S E), IsFiniteMeasure m →
      ∫ x, A.indicator (1 : Config S E → ℝ) x ∂m = (m A).toReal := by
    intro m hm
    haveI := hm
    rw [MeasureTheory.integral_indicator_one hA]
    rfl
  filter_upwards [key] with ω hω
  have hγprob : ∀ n, IsProbabilityMeasure (γ (Λ n) ω) :=
    fun n ↦ hγ.isProbabilityMeasure (Λ n) ω
  have hω' : Tendsto (fun n ↦ (γ (Λ n) ω A).toReal) atTop (nhds ((μ A).toReal)) := by
    rw [hcalc μ inferInstance] at hω
    refine hω.congr fun n ↦ ?_
    haveI := hγprob n
    exact hcalc (γ (Λ n) ω) inferInstance
  refine (ENNReal.tendsto_toReal_iff (fun n ↦ ?_) ?_).1 hω'
  · exact (measure_lt_top (γ (Λ n) ω) A).ne
  · exact (measure_lt_top μ A).ne

/-- **Georgii, Theorem (7.12)(c)**: for a λ-specification over an arbitrary measurable state space
and `μ ∈ ex 𝓖(γ)`, `sup {|γ_{Λ n}(A | ω) − μ(A)| : A ∈ 𝓕_Δ} → 0` for every finite volume `Δ`, for
`μ`-almost every `ω` — one single full-measure set of `ω`'s serving all volumes at once. -/
theorem georgii_7_12_c [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, ∀ Δ : Finset S, Tendsto (fun n ↦ tvOn Δ (γ (Λ n) ω) μ) atTop (nhds 0) := by
  classical
  have hmod := LocalLimitBridge.isModifier hγ
  have hEq : ∀ (Θ : Finset S) (ω : Config S E),
      γ Θ ω = ((Specification.isssd ν).modification ρ hmod) Θ ω :=
    LocalLimitBridge.eq_modification hγ
  have hμ' : μ ∈ (MeasureTheory.GibbsMeasure.G
      ((Specification.isssd ν).modification ρ hmod)).extremePoints ℝ≥0∞ :=
    (LocalLimitBridge.isExtremeGibbs_iff_mem_extremePoints hEq μ).1 hμ
  rw [ae_all_iff]
  intro Δ
  obtain ⟨N, hN⟩ := hcof Δ
  have hmono' : Monotone fun n ↦ Λ (n + N) := fun a b hab ↦ hmono (Nat.add_le_add_right hab N)
  have hcof' : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ (n + N) := by
    intro Θ
    obtain ⟨m, hm⟩ := hcof Θ
    exact ⟨m, hm.trans (hmono (Nat.le_add_right m N))⟩
  have hΔ' : ∀ n, Δ ⊆ Λ (n + N) := fun n ↦ hN.trans (hmono (Nat.le_add_left N n))
  have key := MeasureTheory.GibbsMeasure.ae_tendsto_iSup_ofReal_abs_sub_of_mem_extremePoints_G
    hmod hμ' hmono' hcof' hΔ'
  filter_upwards [key] with ω hω
  rw [← Filter.tendsto_add_atTop_iff_nat N]
  refine hω.congr fun n ↦ ?_
  simp only [tvOn, ← hEq]
  rfl

/-- **Georgii, Theorem (7.12)(c)**, the conclusion drawn from the total-variation estimate:
`γ_{Λ n}(· | ω) → μ` in the topology of local convergence of (4.2), for `μ`-almost every `ω`. -/
theorem georgii_7_12_c_tendstoLocally [Countable S]
    {ν : Measure E} [IsProbabilityMeasure ν] {ρ : Finset S → Config S E → ℝ≥0∞}
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsLambdaSpec ν ρ γ)
    {μ : Measure (Config S E)} (hμ : IsExtremeGibbs γ μ)
    {Λ : ℕ → Finset S} (hmono : Monotone Λ) (hcof : ∀ Θ : Finset S, ∃ n, Θ ⊆ Λ n) :
    ∀ᵐ ω ∂μ, TendstoLocally (fun n ↦ γ (Λ n) ω) atTop μ := by
  have hprob : IsProbabilityMeasure μ := hμ.isGibbs.1
  filter_upwards [georgii_7_12_c hγ hμ hmono hcof] with ω hω
  rintro A ⟨Δ, hAΔ⟩
  have hA : MeasurableSet A := measurableSet_of_inside hAΔ
  have hγprob : ∀ n, IsProbabilityMeasure (γ (Λ n) ω) :=
    fun n ↦ hγ.isSpecification.isProbabilityMeasure (Λ n) ω
  have h1 : Tendsto (fun n ↦ ENNReal.ofReal |(γ (Λ n) ω A).toReal - (μ A).toReal|) atTop
      (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ ↦ (0 : ℝ≥0∞))
      (h := fun n ↦ tvOn Δ (γ (Λ n) ω) μ) tendsto_const_nhds (hω Δ) (fun _ ↦ bot_le)
      fun n ↦ le_tvOn _ _ hAΔ
  have h2 : Tendsto (fun n ↦ |(γ (Λ n) ω A).toReal - (μ A).toReal|) atTop (nhds 0) := by
    have h3 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal, abs_nonneg] using h3
  have h4 : Tendsto (fun n ↦ (γ (Λ n) ω A).toReal) atTop (nhds ((μ A).toReal)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using h2
  refine (ENNReal.tendsto_toReal_iff (fun n ↦ ?_) ?_).1 h4
  · exact (measure_lt_top (γ (Λ n) ω) A).ne
  · exact (measure_lt_top μ A).ne

/-- Non-degeneracy of the hypotheses of `georgii_7_12_c`: the independent specification is a
λ-specification with density `ρ ≡ 1`, and its Gibbs measure `ν^S` is extreme. -/
theorem exists_isLambdaSpec_isExtremeGibbs [Countable S] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsLambdaSpec ν (fun _ _ ↦ 1) (indepSpec (S := S) ν) ∧
      IsExtremeGibbs (indepSpec (S := S) ν) (Measure.infinitePi fun _ : S ↦ ν) := by
  have hspec : IsSpecification (indepSpec (S := S) ν) := isSpecification_indep ν
  have hlam : IsLambdaSpec ν (fun _ _ ↦ 1) (indepSpec (S := S) ν) :=
    { measurable_density := fun _ ↦ measurable_const
      density_apply := fun Λ ω A _ ↦ by rw [setLIntegral_one]
      isSpecification := hspec }
  refine ⟨hlam, ?_⟩
  have hbridge : ∀ (Λ : Finset S) (ω : Config S E),
      indepSpec ν Λ ω = Specification.isssd ν Λ ω := LocalLimitBridge.indepSpec_eq_isssd ν
  have huniq : ∀ κ : Measure (Config S E), IsGibbs (indepSpec (S := S) ν) κ →
      κ = Measure.infinitePi fun _ : S ↦ ν := by
    intro κ hκ
    have hκ' : κ ∈ MeasureTheory.GibbsMeasure.G (Specification.isssd (S := S) ν) :=
      (LocalLimitBridge.isGibbs_iff_mem_G hbridge κ).1 hκ
    have : IsProbabilityMeasure κ := hκ'.1
    exact (Specification.isGibbsMeasure_isssd_iff ν κ).1 hκ'.2
  refine ⟨isGibbs_indep ν, fun ν₁ ν₂ h₁ h₂ a b _ _ _ _ ↦ ⟨huniq ν₁ h₁, huniq ν₂ h₂⟩⟩

end LocalLimit

end GibbsChallenge

end

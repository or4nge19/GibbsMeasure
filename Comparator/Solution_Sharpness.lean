import Comparator.Defs_Sharpness
import GibbsMeasure

/-!
# Georgii, Example (2.27): solution

The solution file matching `Comparator/Challenge_Sharpness.lean`. It differs from the challenge
only by `import GibbsMeasure`, the auxiliary `namespace Bridge` translating the from-scratch
definitions into the `GibbsMeasure` library, and the proof terms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace SharpnessChallenge

open GibbsChallenge DobrushinChallenge

/-! ## The bridge to the `GibbsMeasure` library

Auxiliary: identifies the notions of `Comparator.Defs`, `Comparator.Defs_Dobrushin` and
`Comparator.Defs_Sharpness` with those of the `GibbsMeasure` library, whose theorems are then
quoted. -/

namespace Bridge

open MeasureTheory.GibbsMeasure ProbabilityTheory
open MeasureTheory.GibbsMeasure.Exchangeable

/-- The witness: the kernels of Georgii's Example (2.27), as a plain family of measures. -/
def gam (Λ : Finset ℕ) (ω : Config ℕ Bool) : Measure (Config ℕ Bool) :=
  MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ ω

theorem gam_eq (Λ : Finset ℕ) (ω : Config ℕ Bool) :
    gam Λ ω = MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ ω := rfl

instance instIsProbabilityMeasureGam (Λ : Finset ℕ) (ω : Config ℕ Bool) :
    IsProbabilityMeasure (gam Λ ω) := by
  rw [gam_eq]; infer_instance

theorem aemeasurable_gammaEx (Λ : Finset ℕ) (μ : Measure (Config ℕ Bool)) :
    AEMeasurable (fun ω : Config ℕ Bool ↦
      MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ ω) μ :=
  (((MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ).measurable).mono cylinderEvents_le_pi
    le_rfl).aemeasurable

/-! ### `γ` is a specification -/

/-- **Georgii (2.27)**: the glued family really is a specification — via the library. -/
theorem isSpecification_gam : IsSpecification gam := by
  refine ⟨fun Λ ω ↦ inferInstance, fun Λ A hA ↦ ?_, fun Λ A B hA hB ω ↦ ?_,
    fun Λ Δ hΛΔ ω A hA ↦ ?_⟩
  · exact (MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ).measurable_coe hA
  · have hB' : MeasurableSet[cylinderEvents (X := fun _ : ℕ ↦ Bool) ((Λ : Set ℕ)ᶜ)] B := hB
    have h := (Kernel.isProper_iff_inter_eq_indicator_mul
      (cylinderEvents_le_pi (X := fun _ : ℕ ↦ Bool))).1
      (MeasureTheory.GibbsMeasure.Exchangeable.gammaEx.isProper Λ) hA hB' ω
    rw [gam_eq, h]
    by_cases hωB : ω ∈ B <;> simp [hωB]
  · have hb := Specification.bind (γ := MeasureTheory.GibbsMeasure.Exchangeable.gammaEx) hΛΔ ω
    have h := congrArg (fun m : Measure (Config ℕ Bool) ↦ m A) hb
    rw [Measure.bind_apply hA
      (aemeasurable_gammaEx Λ (MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Δ ω))] at h
    exact h

/-! ### The DLR equations -/

/-- The DLR equation of the challenge and the library's `Measure.bind` equation agree. -/
theorem bind_eq_iff (μ : Measure (Config ℕ Bool)) (Λ : Finset ℕ) :
    μ.bind (MeasureTheory.GibbsMeasure.Exchangeable.gammaEx Λ) = μ ↔
      ∀ A : Set (Config ℕ Bool), MeasurableSet A → μ A = ∫⁻ ω, gam Λ ω A ∂μ := by
  constructor
  · intro h A hA
    have h' := congrArg (fun m : Measure (Config ℕ Bool) ↦ m A) h
    rw [Measure.bind_apply hA (aemeasurable_gammaEx Λ μ)] at h'
    exact h'.symm
  · intro h
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA (aemeasurable_gammaEx Λ μ)]
    exact (h A hA).symm

/-! ### Georgii (2.27): the Bernoulli measures of the challenge are the library's -/

theorem bern_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    bern x = MeasureTheory.GibbsMeasure.Exchangeable.bern (ENNReal.ofReal x) := by
  have hmin : min (ENNReal.ofReal x) 1 = ENNReal.ofReal x :=
    min_eq_left (ENNReal.ofReal_le_one.2 hx1)
  have hsub : ENNReal.ofReal (1 - x) = 1 - ENNReal.ofReal x := by
    rw [ENNReal.ofReal_sub 1 hx0, ENNReal.ofReal_one]
  rw [bern, MeasureTheory.GibbsMeasure.Exchangeable.bern, hmin, hsub]

theorem bernoulliField_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    bernoulliField x
      = MeasureTheory.GibbsMeasure.Exchangeable.bernoulliField (ENNReal.ofReal x) := by
  rw [bernoulliField, MeasureTheory.GibbsMeasure.Exchangeable.bernoulliField]
  exact congrArg _ (funext fun _ ↦ bern_eq hx0 hx1)

/-- **Georgii, Example (2.27)**: every Bernoulli field `μ^x`, `x ∈ [0,1]`, is a Gibbs measure for
`γ` — via `Exchangeable.isGibbsMeasure_bernoulliField`. -/
theorem isGibbs_bernoulliField {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsGibbs gam (bernoulliField x) := by
  have hprob : IsProbabilityMeasure (bernoulliField x) :=
    isProbabilityMeasure_bernoulliField hx0 hx1
  have hG : Specification.IsGibbsMeasure MeasureTheory.GibbsMeasure.Exchangeable.gammaEx
      (bernoulliField x) := by
    rw [bernoulliField_eq hx0 hx1]
    exact MeasureTheory.GibbsMeasure.Exchangeable.isGibbsMeasure_bernoulliField hx0 hx1
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob] at hG
  exact ⟨hprob, fun Λ A hA ↦ (bind_eq_iff (bernoulliField x) Λ).1 (hG Λ) A hA⟩

/-! ### Georgii (8.1), (8.5): the uniform distance and the interdependence matrix -/

theorem unifDist_eq (α₁ α₂ : Measure Bool) [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ = MeasureTheory.GibbsMeasure.Dobrushin.unifDist α₁ α₂ := by
  refine le_antisymm (unifDist_le fun A hA ↦
      MeasureTheory.GibbsMeasure.Dobrushin.ofReal_abs_sub_le_unifDist hA)
    (MeasureTheory.GibbsMeasure.Dobrushin.unifDist_le fun A hA ↦
      le_trans ?_ (le_unifDist (α₁ := α₁) hA))
  rcases le_total (α₁ A) (α₂ A) with h | h
  · simp [tsub_eq_zero_of_le h]
  · rw [← ENNReal.ofReal_toReal (a := α₁ A - α₂ A)
      (ne_top_of_le_ne_top (measure_ne_top α₁ A) tsub_le_self),
      ENNReal.toReal_sub_of_le h (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)

theorem proj_eq (i : ℕ) (ζ : Config ℕ Bool) :
    proj gam i ζ = MeasureTheory.GibbsMeasure.Dobrushin.proj
      MeasureTheory.GibbsMeasure.Exchangeable.gammaEx i ζ := rfl

instance instIsProbabilityMeasureProj (i : ℕ) (ζ : Config ℕ Bool) :
    IsProbabilityMeasure (proj gam i ζ) := by
  rw [proj_eq]; infer_instance

/-- **Georgii, Example (2.27)**: `C_ij(γ) = 0` for all `i, j` — via
`Exchangeable.interdep_gammaEx`. -/
theorem interdep_gam (i j : ℕ) : interdep gam i j = 0 := by
  refine le_antisymm (interdep_le fun ζ η h ↦ ?_) (by simp)
  rw [unifDist_eq, proj_eq, proj_eq]
  have hle := MeasureTheory.GibbsMeasure.Dobrushin.unifDist_proj_le_interdep
    MeasureTheory.GibbsMeasure.Exchangeable.gammaEx i j h
  rwa [MeasureTheory.GibbsMeasure.Exchangeable.interdep_gammaEx] at hle

/-! ### Georgii (2.20), (2.23): local and quasilocal observables -/

/-- A bounded function, as an element of `ℓ^∞`. -/
def toLp {f : Config ℕ Bool → ℝ} (hf : IsBddFn f) : lp (fun _ : ℕ → Bool ↦ ℝ) ∞ :=
  ⟨f, memℓp_infty ⟨hf.choose, by
    rintro _ ⟨ω, rfl⟩
    simpa [Real.norm_eq_abs] using hf.choose_spec ω⟩⟩

@[simp] theorem coe_toLp {f : Config ℕ Bool → ℝ} (hf : IsBddFn f) : ⇑(toLp hf) = f := rfl

theorem isBddFn_coe (f : lp (fun _ : ℕ → Bool ↦ ℝ) ∞) : IsBddFn (S := ℕ) (E := Bool) (⇑f) :=
  ⟨‖f‖, fun ω ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f ω⟩

theorem isLocalFn_coe {f : lp (fun _ : ℕ → Bool ↦ ℝ) ∞} (hf : f ∈ localFunctions ℕ Bool) :
    IsLocalFn (S := ℕ) (E := Bool) (⇑f) := by
  obtain ⟨Λ, hΛ⟩ := mem_localFunctions.1 hf
  exact ⟨isBddFn_coe f, Λ, mem_localFunctionsOn.1 hΛ⟩

theorem mem_quasilocalFunctions_of_isQuasilocalFn {f : lp (fun _ : ℕ → Bool ↦ ℝ) ∞}
    (hf : IsQuasilocalFn (S := ℕ) (E := Bool) (⇑f)) : f ∈ quasilocalFunctions ℕ Bool := by
  rw [mem_quasilocalFunctions_iff_mem_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := hf.2 (ε / 2) (by linarith)
  refine ⟨toLp hg.1, ?_, ?_⟩
  · obtain ⟨Λ, hΛ⟩ := hg.2
    exact mem_localFunctions.2 ⟨Λ, mem_localFunctionsOn.2 hΛ⟩
  · have hnorm : ‖f - toLp hg.1‖ ≤ ε / 2 := by
      refine lp.norm_le_of_forall_le (by linarith) fun ω ↦ ?_
      rw [lp.coeFn_sub, Pi.sub_apply]
      simpa [Real.norm_eq_abs] using hfg ω
    rw [dist_eq_norm]
    linarith

/-- Georgii's own formulation of (2.23) — quantifying over **local** observables only — implies
the library's, which quantifies over quasilocal ones. This is the analytic step of Georgii's
remark after (2.23), supplied by `Specification.isQuasilocal_iff_forall_mem_localFunctions`. -/
theorem isQuasilocal_gammaEx (hq : IsQuasilocalSpec gam) :
    MeasureTheory.GibbsMeasure.Exchangeable.gammaEx.IsQuasilocal :=
  Specification.isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦
    mem_quasilocalFunctions_of_isQuasilocalFn (hq Λ (⇑f) (isLocalFn_coe hf))

/-- **Georgii, Example (2.27)**: `γ` is not quasilocal — via
`Exchangeable.not_isQuasilocal_gammaEx`. -/
theorem not_isQuasilocalSpec_gam : ¬ IsQuasilocalSpec gam := fun hq ↦
  MeasureTheory.GibbsMeasure.Exchangeable.not_isQuasilocal_gammaEx (isQuasilocal_gammaEx hq)

/-! ### `𝓖(γ)` is uncountable -/

/-- **Georgii, Example (2.27)**: `𝓖(γ)` is uncountable, because it contains the continuum-sized
family `(μ^x)_{x ∈ [0,1]}`. -/
theorem not_countable_isGibbs_gam :
    ¬ {μ : Measure (Config ℕ Bool) | IsGibbs gam μ}.Countable := by
  intro hG
  have hmaps : Set.MapsTo (fun x : ℝ ↦ bernoulliField x) (Set.Icc 0 1)
      {μ : Measure (Config ℕ Bool) | IsGibbs gam μ} :=
    fun x hx ↦ isGibbs_bernoulliField hx.1 hx.2
  have hinj : Set.InjOn (fun x : ℝ ↦ bernoulliField x) (Set.Icc 0 1) := by
    intro a ha b hb hab
    by_contra hne
    exact bernoulliField_ne ha hb hne hab
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable := hmaps.countable_of_injOn hinj hG
  simp only [Cardinal.Real.Icc_countable_iff] at hIcc
  norm_num at hIcc

end Bridge

/-! ## The theorems -/

/-- **Georgii, Example (2.27)**: there is a specification `γ` on `Ω = {0,1}^ℕ` whose
interdependence matrix vanishes identically, which has every Bernoulli random field `μ^x`,
`x ∈ [0,1]`, among its Gibbs measures — so `𝓖(γ)` is uncountable — and which is **not**
quasilocal. It fails Dobrushin's condition (8.6) only through the quasilocality conjunct, which is
therefore not droppable from Theorem (8.7). -/
theorem exists_isSpecification_interdep_eq_zero_not_isQuasilocalSpec :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ (∀ i j, interdep γ i j = 0) ∧
        (∀ x ∈ Set.Icc (0 : ℝ) 1, IsGibbs γ (bernoulliField x)) ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Countable ∧
        ¬ IsQuasilocalSpec γ ∧ ¬ IsDobrushin γ := by
  refine ⟨Bridge.gam, Bridge.isSpecification_gam, Bridge.interdep_gam,
    fun x hx ↦ Bridge.isGibbs_bernoulliField hx.1 hx.2, Bridge.not_countable_isGibbs_gam,
    Bridge.not_isQuasilocalSpec_gam, ?_⟩
  exact fun hd ↦ Bridge.not_isQuasilocalSpec_gam hd.1

/-- **Georgii, Example (2.27)**, stated against Theorem (8.7): the second conjunct of Dobrushin's
condition, `c(γ) = sup_i ∑_j C_ij(γ) < 1`, does not by itself imply that `𝓖(γ)` has at most one
element. -/
theorem not_subsingleton_isGibbs_of_iSup_tsum_interdep_lt_one :
    ∃ γ : Finset ℕ → Config ℕ Bool → Measure (Config ℕ Bool),
      IsSpecification γ ∧ ⨆ i, ∑' j, interdep γ i j < 1 ∧
        ¬ {μ : Measure (Config ℕ Bool) | IsGibbs γ μ}.Subsingleton := by
  refine ⟨Bridge.gam, Bridge.isSpecification_gam, ?_, ?_⟩
  · have h : ⨆ i : ℕ, ∑' j : ℕ, interdep Bridge.gam i j = 0 := by
      simp [Bridge.interdep_gam]
    rw [h]
    exact zero_lt_one
  · intro hsub
    have h0 : IsGibbs Bridge.gam (bernoulliField 0) :=
      Bridge.isGibbs_bernoulliField le_rfl zero_le_one
    have h1 : IsGibbs Bridge.gam (bernoulliField 1) :=
      Bridge.isGibbs_bernoulliField zero_le_one le_rfl
    exact bernoulliField_ne (by norm_num) (by norm_num) (by norm_num) (hsub h0 h1)

end SharpnessChallenge

end

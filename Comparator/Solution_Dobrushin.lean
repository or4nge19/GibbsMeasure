import Comparator.Defs_Dobrushin
import GibbsMeasure

/-!
# Comparator solution: Dobrushin's uniqueness theorem (Georgii, Theorem (8.7))

This is the *solution* file matching `Comparator/Challenge_Dobrushin.lean`.  Both files take their
definitions from the same modules `Comparator.Defs` and `Comparator.Defs_Dobrushin`, which import
`Mathlib` and nothing else, so the statements of the two theorems below are literally the
challenge's statements; the only differences are the extra `import GibbsMeasure`, this module
docstring, an auxiliary `namespace Bridge` block translating between those from-scratch definitions
and the `GibbsMeasure` library, and the proof terms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace DobrushinChallenge

open GibbsChallenge

variable {S E : Type*} [MeasurableSpace E]

/-! ## The bridge to the `GibbsMeasure` library

Everything in this section is auxiliary: it identifies the notions of `Comparator.Defs` and
`Comparator.Defs_Dobrushin` with those of the `GibbsMeasure` library, whose theorems are then
quoted. **None of the statements of the challenge is touched.** -/

namespace Bridge

open MeasureTheory.GibbsMeasure ProbabilityTheory

variable {S E : Type*} [MeasurableSpace E]
variable {γ γ' : Finset S → Config S E → Measure (Config S E)}

/-! ### The σ-algebras -/

theorem outside_eq_cylinderEvents (Λ : Finset S) :
    outside (S := S) (E := E) Λ = cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := rfl

theorem inside_eq_cylinderEvents (Λ : Finset S) :
    inside (S := S) (E := E) Λ = cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S) := rfl

/-! ### The library `Specification` attached to a first-principles specification -/

/-- The library's `Specification` bundling the kernels of a first-principles specification. -/
def spec (γ : Finset S → Config S E → Measure (Config S E)) (hγ : IsSpecification γ) :
    Specification S E where
  toFun Λ := @ProbabilityTheory.Kernel.mk (S → E) (S → E)
    (cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) _ (γ Λ)
    (Measure.measurable_measure.2 fun A hA ↦ hγ.measurable_apply Λ A hA)
  isConsistent' := by
    intro Λ₁ Λ₂ h
    refine Kernel.ext fun ω ↦ Measure.ext fun A hA ↦ ?_
    rw [Kernel.comp_apply' _ _ _ hA]
    exact hγ.consistent Λ₁ Λ₂ h ω A hA
  isMarkovKernel' Λ := ⟨fun ω ↦ hγ.isProbabilityMeasure Λ ω⟩
  isProper' Λ := by
    rw [Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi]
    intro A hA B hB ω
    show γ Λ ω (A ∩ B) = B.indicator 1 ω * γ Λ ω A
    rw [hγ.proper Λ A B hA hB ω]
    by_cases hω : ω ∈ B <;> simp [hω]

@[simp] theorem spec_apply (hγ : IsSpecification γ) (Λ : Finset S) (ω : Config S E) :
    spec γ hγ Λ ω = γ Λ ω := rfl


/-! ### Gibbs measures -/

theorem comp_eq (hγ : IsSpecification γ) {μ : Measure (Config S E)} (hμ : IsGibbs γ μ)
    (Λ : Finset S) : ⇑(spec γ hγ Λ) ∘ₘ μ = μ := by
  have := hμ.1
  refine Measure.ext fun A hA ↦ ?_
  rw [Measure.bind_apply hA
    (((spec γ hγ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)]
  exact (hμ.2 Λ A hA).symm

theorem isGibbsMeasure (hγ : IsSpecification γ) {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    Specification.IsGibbsMeasure (spec γ hγ) μ := by
  have := hμ.1
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
  exact fun Λ ↦ comp_eq hγ hμ Λ

/-! ### Georgii (8.1): the two uniform distances agree -/

theorem unifDist_eq (α₁ α₂ : Measure E) [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ = GibbsMeasure.Dobrushin.unifDist α₁ α₂ := by
  refine le_antisymm (unifDist_le fun A hA ↦ GibbsMeasure.Dobrushin.ofReal_abs_sub_le_unifDist hA)
    (GibbsMeasure.Dobrushin.unifDist_le fun A hA ↦ le_trans ?_ (le_unifDist (α₁ := α₁) hA))
  rcases le_total (α₁ A) (α₂ A) with h | h
  · simp [tsub_eq_zero_of_le h]
  · rw [← ENNReal.ofReal_toReal (a := α₁ A - α₂ A)
      (ne_top_of_le_ne_top (measure_ne_top α₁ A) tsub_le_self),
      ENNReal.toReal_sub_of_le h (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)

/-! ### Georgii (8.4), (8.5): the single-site distributions and Dobrushin's matrix -/

theorem proj_eq (hγ : IsSpecification γ) (i : S) (ζ : Config S E) :
    proj γ i ζ = GibbsMeasure.Dobrushin.proj (spec γ hγ) i ζ := rfl

theorem isProbabilityMeasure_proj (hγ : IsSpecification γ) (i : S) (ζ : Config S E) :
    IsProbabilityMeasure (proj γ i ζ) := by
  have := hγ.isProbabilityMeasure ({i} : Finset S) ζ
  exact Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

theorem interdep_eq (hγ : IsSpecification γ) (i j : S) :
    interdep γ i j = GibbsMeasure.Dobrushin.interdep (spec γ hγ) i j := by
  rw [GibbsMeasure.Dobrushin.interdep_eq]
  refine iSup_congr fun ζ ↦ iSup_congr fun η ↦ iSup_congr fun _ ↦ ?_
  have := isProbabilityMeasure_proj hγ i ζ
  have := isProbabilityMeasure_proj hγ i η
  exact unifDist_eq (proj γ i ζ) (proj γ i η)

/-! ### Georgii (8.14): the two single-site oscillations agree -/

omit [MeasurableSpace E] in
theorem oscAt_eq (f : Config S E → ℝ) (j : S) :
    oscAt f j = GibbsMeasure.Dobrushin.oscAt f j := by
  refine le_antisymm (iSup₂_le fun ζ η ↦ iSup_le fun h ↦ GibbsMeasure.Dobrushin.le_oscAt h)
    (GibbsMeasure.Dobrushin.oscAt_le fun ζ η h ↦ ?_)
  exact le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

/-! ### Georgii (8.19): the two series agree -/

theorem interdepIter_eq (hγ : IsSpecification γ) (n : ℕ) (b : S → ℝ≥0∞) (i : S) :
    interdepIter γ n b i = GibbsMeasure.Dobrushin.interdepIter (spec γ hγ) n b i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      show ∑' j, interdep γ i j * interdepIter γ n b j
        = ∑' j, GibbsMeasure.Dobrushin.interdep (spec γ hγ) i j *
            GibbsMeasure.Dobrushin.interdepIter (spec γ hγ) n b j
      exact tsum_congr fun j ↦ by rw [interdep_eq hγ, ih j]

theorem interdepSeries_eq (hγ : IsSpecification γ) (b : S → ℝ≥0∞) (i : S) :
    interdepSeries γ b i = GibbsMeasure.Dobrushin.interdepSeries (spec γ hγ) b i :=
  tsum_congr fun n ↦ interdepIter_eq hγ n b i

/-! ### Local and quasilocal observables -/

/-- A bounded function, as an element of `ℓ^∞`. -/
def toLp {f : Config S E → ℝ} (hf : IsBddFn f) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨f, memℓp_infty ⟨hf.choose, by
    rintro _ ⟨ω, rfl⟩
    simpa [Real.norm_eq_abs] using hf.choose_spec ω⟩⟩

omit [MeasurableSpace E] in
@[simp] theorem coe_toLp {f : Config S E → ℝ} (hf : IsBddFn f) : ⇑(toLp hf) = f := rfl

omit [MeasurableSpace E] in
theorem isBddFn_coe (f : lp (fun _ : S → E ↦ ℝ) ∞) : IsBddFn (S := S) (E := E) (⇑f) :=
  ⟨‖f‖, fun ω ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f ω⟩

theorem isLocalFn_coe {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    IsLocalFn (S := S) (E := E) (⇑f) := by
  obtain ⟨Λ, hΛ⟩ := mem_localFunctions.1 hf
  exact ⟨isBddFn_coe f, Λ, mem_localFunctionsOn.1 hΛ⟩

theorem mem_localFunctions_toLp {f : Config S E → ℝ} (hf : IsLocalFn f) :
    toLp hf.1 ∈ localFunctions S E := by
  obtain ⟨Λ, hΛ⟩ := hf.2
  exact mem_localFunctions.2 ⟨Λ, mem_localFunctionsOn.2 hΛ⟩

theorem isQuasilocalFn_coe {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ quasilocalFunctions S E) :
    IsQuasilocalFn (S := S) (E := E) (⇑f) := by
  refine ⟨isBddFn_coe f, fun ε hε ↦ ?_⟩
  obtain ⟨g, hg, hfg⟩ :=
    Metric.mem_closure_iff.1 (mem_quasilocalFunctions_iff_mem_closure.1 hf) ε hε
  refine ⟨⇑g, isLocalFn_coe hg, fun ω ↦ ?_⟩
  have h1 := lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) ω
  rw [lp.coeFn_sub, Pi.sub_apply] at h1
  rw [← Real.norm_eq_abs]
  rw [dist_eq_norm] at hfg
  exact h1.trans hfg.le

theorem mem_quasilocalFunctions_of_isQuasilocalFn {f : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : IsQuasilocalFn (S := S) (E := E) (⇑f)) : f ∈ quasilocalFunctions S E := by
  rw [mem_quasilocalFunctions_iff_mem_closure, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := hf.2 (ε / 2) (by linarith)
  refine ⟨toLp hg.1, mem_localFunctions_toLp hg, ?_⟩
  have hnorm : ‖f - toLp hg.1‖ ≤ ε / 2 := by
    refine lp.norm_le_of_forall_le (by linarith) fun ω ↦ ?_
    rw [lp.coeFn_sub, Pi.sub_apply]
    simpa [Real.norm_eq_abs] using hfg ω
  rw [dist_eq_norm]
  linarith

/-! ### Georgii (2.23): the two notions of quasilocality agree

The challenge's `IsQuasilocalSpec` is Georgii's own formulation of (2.23): it quantifies over
**local** `f` only. The library's `Specification.IsQuasilocal` quantifies over **quasilocal** `f`.
So the hypothesis available here is the *weaker* one, and the passage from it to the library's
notion is a real analytic step, not a matter of unfolding: one has to know that `γ_Λ` is a
contraction for the sup-norm and that `𝓛̄`, being a uniform closure, is closed, so that
`γ_Λ(𝓛) ⊆ 𝓛̄` propagates from `𝓛` to its closure `𝓛̄`. That is exactly Georgii's remark
immediately after (2.23), and the library supplies it as
`Specification.isQuasilocal_iff_forall_mem_localFunctions`; we *invoke* that theorem here rather
than assuming the stronger hypothesis. -/

theorem isQuasilocal_spec (hγ : IsSpecification γ) (hq : IsQuasilocalSpec γ) :
    (spec γ hγ).IsQuasilocal :=
  Specification.isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦
    mem_quasilocalFunctions_of_isQuasilocalFn (hq Λ (⇑f) (isLocalFn_coe hf))

/-! ### Georgii (8.6): the two forms of Dobrushin's condition agree -/

theorem isDobrushin_spec (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    GibbsMeasure.Dobrushin.IsDobrushin (spec γ hγ) := by
  refine (GibbsMeasure.Dobrushin.isDobrushin_iff_iSup_lt_one _).2
    ⟨isQuasilocal_spec hγ hd.1, lt_of_le_of_lt (le_of_eq ?_) hd.2⟩
  exact iSup_congr fun i ↦ tsum_congr fun j ↦ (interdep_eq hγ i j).symm

end Bridge

/-! ## The theorems -/

/-- **Georgii, Theorem (8.7)**: a specification satisfying Dobrushin's condition of weak
dependence has *at most one* Gibbs measure, i.e. `|𝓖(γ)| ≤ 1`. -/
theorem subsingleton_isGibbs_of_isDobrushin
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    {μ : Measure (Config S E) | IsGibbs γ μ}.Subsingleton := by
  intro μ hμ ν hν
  have hq : (Bridge.spec γ hγ).IsQuasilocal := Bridge.isQuasilocal_spec hγ hd.1
  have hD : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  have hmμ : (⟨μ, hμ.1⟩ : ProbabilityMeasure (Config S E)) ∈
      MeasureTheory.GibbsMeasure.GP (Bridge.spec γ hγ) := Bridge.isGibbsMeasure hγ hμ
  have hmν : (⟨ν, hν.1⟩ : ProbabilityMeasure (Config S E)) ∈
      MeasureTheory.GibbsMeasure.GP (Bridge.spec γ hγ) := Bridge.isGibbsMeasure hγ hν
  have h : (⟨μ, hμ.1⟩ : ProbabilityMeasure (Config S E)) = ⟨ν, hν.1⟩ :=
    MeasureTheory.GibbsMeasure.Dobrushin.subsingleton_GP_of_isDobrushin hq hD hmμ hmν
  exact congrArg (fun x : ProbabilityMeasure (Config S E) ↦ (x : Measure (Config S E))) h

/-- **Georgii, Theorem (8.20)**, the Dobrushin comparison theorem: if `γ` satisfies Dobrushin's
condition, `μ ∈ 𝓖(γ)`, `ν ∈ 𝓖(γ')`, and `b_i` dominates `‖γ_i^0(·|ω) − γ'^0_i(·|ω)‖`, then for
every local observable `f`
`|μ(f) − ν(f)| ≤ ∑_{i,j} δ_i(f) D_ij(γ) ν(b_j)`. -/
theorem ofReal_abs_integral_sub_le_interdepSeries
    (γ γ' : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hγ' : IsSpecification γ') (hd : IsDobrushin γ)
    (μ ν : Measure (Config S E)) (hμ : IsGibbs γ μ) (hν : IsGibbs γ' ν)
    (b : S → Config S E → ℝ≥0∞) (hbm : ∀ i, Measurable (b i))
    (hb : ∀ (i : S) (ω : Config S E), unifDist (proj γ i ω) (proj γ' i ω) ≤ b i ω)
    (f : Config S E → ℝ) (hf : IsLocalFn f) :
    ENNReal.ofReal |(∫ σ, f σ ∂μ) - ∫ σ, f σ ∂ν|
      ≤ ∑' i, interdepSeries γ (fun j ↦ ∫⁻ ω, b j ω ∂ν) i * oscAt f i := by
  have hμp : IsProbabilityMeasure μ := hμ.1
  have hνp : IsProbabilityMeasure ν := hν.1
  have hq : (Bridge.spec γ hγ).IsQuasilocal := Bridge.isQuasilocal_spec hγ hd.1
  have hD : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  have hb' : ∀ (i : S) (ω : Config S E),
      MeasureTheory.GibbsMeasure.Dobrushin.unifDist
          (MeasureTheory.GibbsMeasure.Dobrushin.proj (Bridge.spec γ hγ) i ω)
          (MeasureTheory.GibbsMeasure.Dobrushin.proj (Bridge.spec γ' hγ') i ω) ≤ b i ω := by
    intro i ω
    have h1 := Bridge.isProbabilityMeasure_proj hγ i ω
    have h2 := Bridge.isProbabilityMeasure_proj hγ' i ω
    have h3 := hb i ω
    rw [Bridge.unifDist_eq (proj γ i ω) (proj γ' i ω)] at h3
    exact h3
  have H := MeasureTheory.GibbsMeasure.Dobrushin.comparison
    (γ := Bridge.spec γ hγ) (γ' := Bridge.spec γ' hγ') hq hD
    (fun i ↦ Bridge.comp_eq hγ hμ {i}) (fun i ↦ Bridge.comp_eq hγ' hν {i}) hbm hb'
  have h2 := H (Bridge.toLp hf.1) (Bridge.mem_localFunctions_toLp hf)
  simp only [Bridge.coe_toLp] at h2
  refine h2.trans_eq (tsum_congr fun i ↦ ?_)
  rw [Bridge.interdepSeries_eq hγ, Bridge.oscAt_eq]

end DobrushinChallenge

end

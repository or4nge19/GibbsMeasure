import Comparator.Defs_Dobrushin
import GibbsMeasure

/-!
# Dobrushin's uniqueness theorem: solution (Georgii, Theorem (8.7))

The solution file matching `Comparator/Challenge_Dobrushin.lean`. It differs from the challenge
only by `import GibbsMeasure`, the auxiliary `namespace Bridge` translating the from-scratch
definitions into the `GibbsMeasure` library, and the proof terms.
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

Auxiliary: identifies the notions of `Comparator.Defs` and `Comparator.Defs_Dobrushin` with those
of the `GibbsMeasure` library, whose theorems are then quoted. -/

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

theorem isGibbs_of_mem_GP (hγ : IsSpecification γ) {μ : Measure (Config S E)}
    [IsProbabilityMeasure μ] (h : Specification.IsGibbsMeasure (spec γ hγ) μ) : IsGibbs γ μ := by
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob] at h
  refine ⟨inferInstance, fun Λ A hA ↦ ?_⟩
  have h2 : (⇑(spec γ hγ Λ) ∘ₘ μ) A = μ A := by rw [h Λ]
  rw [Measure.bind_apply hA
    (((spec γ hγ Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)] at h2
  exact h2.symm

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

theorem interdepTail_eq [DecidableEq S] (hγ : IsSpecification γ) (Δ : Finset S) (i : S) :
    interdepTail γ Δ i = GibbsMeasure.Dobrushin.interdepTail (spec γ hγ) Δ i :=
  interdepSeries_eq hγ _ i

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

The challenge's `IsQuasilocalSpec` quantifies over **local** `f` only, whereas the library's
`Specification.IsQuasilocal` quantifies over **quasilocal** `f`; the hypothesis available here is
therefore the weaker one, and the passage between them is a genuine analytic step supplied by
`Specification.isQuasilocal_iff_forall_mem_localFunctions`, which we invoke rather than assume. -/

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

/-- Georgii (8.23), step 1, transported to the challenge's vocabulary: under Dobrushin's condition
the net of finite-volume Gibbs distributions has a Gibbs cluster point. -/
theorem exists_isLocalThermodynamicLimit [StandardBorelSpace E] (hγ : IsSpecification γ)
    (hd : IsDobrushin γ) (ω : Config S E) :
    ∃ μ ∈ GP (S := S) (E := E) (spec γ hγ), IsLocalThermodynamicLimit (spec γ hγ) ω μ :=
  exists_isLocalThermodynamicLimit_mem_GP (isQuasilocal_spec hγ hd.1) ω
    (Dobrushin.locallyEquicontinuous_finiteVolumeDistributions_of_isDobrushin
      (isQuasilocal_spec hγ hd.1) (isDobrushin_spec hγ hd) ω)

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

/-- **Georgii, Theorem (8.7), in full**: over a standard Borel state space a specification
satisfying Dobrushin's condition has *exactly one* Gibbs measure, existence included. -/
theorem existsUnique_isGibbs_of_isDobrushin [Nonempty E] [StandardBorelSpace E]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    ∃! μ : Measure (Config S E), IsGibbs γ μ := by
  have hq : (Bridge.spec γ hγ).IsQuasilocal := Bridge.isQuasilocal_spec hγ hd.1
  have hD : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  obtain ⟨μ, hμ, huniq⟩ :=
    MeasureTheory.GibbsMeasure.Dobrushin.existsUnique_mem_GP_of_isDobrushin_of_standardBorel hq hD
  refine ⟨(μ : Measure (Config S E)), Bridge.isGibbs_of_mem_GP hγ hμ, fun ν hν ↦ ?_⟩
  have hprob : IsProbabilityMeasure ν := hν.1
  have h := huniq (⟨ν, hprob⟩ : ProbabilityMeasure (Config S E)) (Bridge.isGibbsMeasure hγ hν)
  exact congrArg (fun x : ProbabilityMeasure (Config S E) ↦ (x : Measure (Config S E))) h

/-- **Georgii (8.23), the Cauchy estimate**: for a `Λ`-local event `A` and finite volumes
`Δ ⊆ Δ'`, `|γ_Δ(A|ω) − γ_{Δ'}(A|ω)| ≤ ∑_{i ∈ Λ} ∑_{j ∉ Δ} D_ij(γ)`. -/
theorem ofReal_abs_toReal_sub_le_interdepTail [DecidableEq S]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) {Λ Δ Δ' : Finset S} (hΔ : Δ ⊆ Δ')
    (ω : Config S E) {A : Set (Config S E)} (hA : MeasurableSet[inside Λ] A) :
    ENNReal.ofReal |(γ Δ ω A).toReal - (γ Δ' ω A).toReal| ≤ ∑ i ∈ Λ, interdepTail γ Δ i := by
  have hq : (Bridge.spec γ hγ).IsQuasilocal := Bridge.isQuasilocal_spec hγ hd.1
  have hD : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  have hTeq : (∑ i ∈ Λ, interdepTail γ Δ i)
      = ∑ i ∈ Λ, MeasureTheory.GibbsMeasure.Dobrushin.interdepTail (Bridge.spec γ hγ) Δ i :=
    Finset.sum_congr rfl fun i _ ↦ Bridge.interdepTail_eq hγ Δ i
  rw [hTeq]
  set T : ℝ≥0∞ :=
    ∑ i ∈ Λ, MeasureTheory.GibbsMeasure.Dobrushin.interdepTail (Bridge.spec γ hγ) Δ i with hTdef
  rcases eq_or_ne T ⊤ with hT | hT
  · simp [hT]
  have hprobΔ : IsProbabilityMeasure (γ Δ ω) := hγ.isProbabilityMeasure Δ ω
  have hprobΔ' : IsProbabilityMeasure (γ Δ' ω) := hγ.isProbabilityMeasure Δ' ω
  have hAm : MeasurableSet A := measurableSet_of_inside hA
  have h1 : γ Δ' ω A ≤ γ Δ ω A + T :=
    MeasureTheory.GibbsMeasure.Dobrushin.measure_le_add_interdepTail hq hD hΔ ω hA
  have h1c : γ Δ' ω Aᶜ ≤ γ Δ ω Aᶜ + T :=
    MeasureTheory.GibbsMeasure.Dobrushin.measure_le_add_interdepTail hq hD hΔ ω hA.compl
  have hcompl : ∀ ρ : Measure (Config S E), IsProbabilityMeasure ρ →
      (ρ Aᶜ).toReal = 1 - (ρ A).toReal := by
    intro ρ _
    rw [prob_compl_eq_one_sub hAm, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have hr1 : (γ Δ' ω A).toReal ≤ (γ Δ ω A).toReal + T.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hT⟩) h1
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hT] at h
  have hr2 : 1 - (γ Δ' ω A).toReal ≤ (1 - (γ Δ ω A).toReal) + T.toReal := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, hT⟩) h1c
    rwa [ENNReal.toReal_add (measure_ne_top _ _) hT, hcompl _ hprobΔ', hcompl _ hprobΔ] at h
  have habs : |(γ Δ ω A).toReal - (γ Δ' ω A).toReal| ≤ T.toReal :=
    abs_le.2 ⟨by linarith, by linarith⟩
  calc ENNReal.ofReal |(γ Δ ω A).toReal - (γ Δ' ω A).toReal|
      ≤ ENNReal.ofReal T.toReal := ENNReal.ofReal_le_ofReal habs
    _ = T := ENNReal.ofReal_toReal hT

/-- **Georgii (8.23)**: under Dobrushin's condition the error term of the Cauchy estimate tends
to `0` as `Δ ↑ S`, so the finite-volume Gibbs distributions with a fixed boundary condition are
Cauchy on every local event. -/
theorem tendsto_interdepTail [DecidableEq S]
    (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) (i : S) :
    Tendsto (fun Δ : Finset S ↦ interdepTail γ Δ i) atTop (nhds 0) := by
  have hD0 : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  have heq : (fun Δ : Finset S ↦ interdepTail γ Δ i)
      = fun Δ ↦ MeasureTheory.GibbsMeasure.Dobrushin.interdepTail (Bridge.spec γ hγ) Δ i :=
    funext fun Δ ↦ Bridge.interdepTail_eq hγ Δ i
  rw [heq]
  exact MeasureTheory.GibbsMeasure.Dobrushin.tendsto_interdepTail hD0 i

/-- **Georgii (8.23)**: over a standard Borel state space Dobrushin's condition *constructs* the
Gibbs measure — there is exactly one, and `(γ_Δ(·|ω))_Δ` converges to it in the topology of local
convergence, Georgii (4.2), for every boundary condition `ω`. -/
theorem exists_isGibbs_tendstoLocally_of_isDobrushin [DecidableEq S] [Nonempty E]
    [StandardBorelSpace E] (γ : Finset S → Config S E → Measure (Config S E))
    (hγ : IsSpecification γ) (hd : IsDobrushin γ) :
    ∃ μ : Measure (Config S E), IsGibbs γ μ ∧
      (∀ ν : Measure (Config S E), IsGibbs γ ν → ν = μ) ∧
      ∀ ω : Config S E, TendstoLocally (fun Δ : Finset S ↦ γ Δ ω) atTop μ := by
  have hq : (Bridge.spec γ hγ).IsQuasilocal := Bridge.isQuasilocal_spec hγ hd.1
  have hD : MeasureTheory.GibbsMeasure.Dobrushin.IsDobrushin (Bridge.spec γ hγ) :=
    Bridge.isDobrushin_spec hγ hd
  obtain ⟨μ, hμ, huniq⟩ := existsUnique_isGibbs_of_isDobrushin γ hγ hd
  refine ⟨μ, hμ, huniq, fun ω A hA ↦ ?_⟩
  obtain ⟨Λ, hAΛ⟩ := hA
  have hAm : MeasurableSet A := measurableSet_of_inside hAΛ
  -- (1) the net of finite-volume probabilities of `A` is Cauchy, by the estimate (8.23)
  have htail : Tendsto (fun Δ : Finset S ↦ ∑ i ∈ Λ, interdepTail γ Δ i) atTop (nhds 0) := by
    have h := tendsto_finsetSum (f := fun (i : S) (Δ : Finset S) ↦ interdepTail γ Δ i)
      (a := fun _ : S ↦ (0 : ℝ≥0∞)) Λ fun i _ ↦ tendsto_interdepTail γ hγ hd i
    simpa using h
  have hcauchy : Cauchy (Filter.map (fun Δ : Finset S ↦ (γ Δ ω A).toReal) atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε ↦ ?_⟩
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := by
      simpa using ENNReal.ofReal_pos.2 (by linarith)
    obtain ⟨Δ₀, hΔ₀⟩ :=
      ((ENNReal.tendsto_nhds_zero.1 htail) (ENNReal.ofReal (ε / 4)) hpos).exists
    set t : ℝ≥0∞ := ∑ i ∈ Λ, interdepTail γ Δ₀ i with htdef
    have httop : t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΔ₀
    have htle : t.toReal ≤ ε / 4 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hΔ₀
      rwa [ENNReal.toReal_ofReal (by linarith)] at this
    have hbnd : ∀ Δ : Finset S, Δ₀ ≤ Δ →
        |(γ Δ₀ ω A).toReal - (γ Δ ω A).toReal| ≤ t.toReal := by
      intro Δ hΔ
      have h := ofReal_abs_toReal_sub_le_interdepTail γ hγ hd hΔ ω hAΛ
      have h2 := ENNReal.toReal_mono httop h
      rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2
    refine ⟨(fun Δ : Finset S ↦ (γ Δ ω A).toReal) '' {Δ : Finset S | Δ₀ ≤ Δ}, ?_, ?_⟩
    · exact Filter.image_mem_map (Filter.eventually_ge_atTop Δ₀)
    · rintro x ⟨Δ, hΔ, rfl⟩ y ⟨Δ', hΔ', rfl⟩
      have h1 := hbnd Δ hΔ
      have h2 := hbnd Δ' hΔ'
      rw [Real.dist_eq]
      have : |(γ Δ ω A).toReal - (γ Δ' ω A).toReal| ≤ t.toReal + t.toReal := by
        calc |(γ Δ ω A).toReal - (γ Δ' ω A).toReal|
            ≤ |(γ Δ ω A).toReal - (γ Δ₀ ω A).toReal|
              + |(γ Δ₀ ω A).toReal - (γ Δ' ω A).toReal| := abs_sub_le _ _ _
          _ ≤ t.toReal + t.toReal := by
              rw [abs_sub_comm ((γ Δ ω A).toReal)]
              exact add_le_add h1 h2
      linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete hcauchy
  have hLtend : Tendsto (fun Δ : Finset S ↦ (γ Δ ω A).toReal) atTop (nhds L) := hL
  have htend : Tendsto (fun Δ : Finset S ↦ γ Δ ω A) atTop (nhds (ENNReal.ofReal L)) := by
    have h1 : Tendsto (fun Δ : Finset S ↦ ENNReal.ofReal ((γ Δ ω A).toReal)) atTop
        (nhds (ENNReal.ofReal L)) := (ENNReal.continuous_ofReal.tendsto L).comp hLtend
    have heq : (fun Δ : Finset S ↦ γ Δ ω A)
        = fun Δ : Finset S ↦ ENNReal.ofReal ((γ Δ ω A).toReal) := by
      funext Δ
      have := hγ.isProbabilityMeasure Δ ω
      exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [heq]
    exact h1
  -- (2) the unique Gibbs measure is a cluster point of that net
  obtain ⟨μ0, hμ0GP, hltl⟩ := Bridge.exists_isLocalThermodynamicLimit hγ hd ω
  have hμ0 : (μ0 : Measure (Config S E)) = μ := huniq _ (Bridge.isGibbs_of_mem_GP hγ hμ0GP)
  have hcont : Continuous fun ρ : MeasureTheory.WithLocalConvergence S E ↦
      ((ρ.toMeasure : Measure (Config S E)) A) :=
    MeasureTheory.WithSetwiseTopology.continuous_apply_enn
      (MeasureTheory.mem_localEvents_of_cylinderEvents Λ hAΛ)
  have hcl : ClusterPt ((μ0 : Measure (Config S E)) A)
      (Filter.map (fun Δ : Finset S ↦ γ Δ ω A) atTop) := by
    have h := hltl.map hcont.continuousAt Filter.tendsto_map
    rw [Filter.map_map] at h
    exact h
  -- (3) a cluster point of a convergent net is its limit
  have hfin : (μ0 : Measure (Config S E)) A = ENNReal.ofReal L :=
    eq_of_nhds_neBot (hcl.mono htend)
  rw [hμ0] at hfin
  rw [hfin]
  exact htend

/-- **Non-vacuity**: for a single-spin distribution `ν` and an arbitrary — in particular infinite
— site set `S`, the independent specification satisfies Dobrushin's condition with `c(γ) = 0`, its
Gibbs measures are exactly `ν^S`, and the finite-volume Gibbs distributions converge locally to
`ν^S` from every boundary condition. -/
theorem isDobrushin_indepSpec [DecidableEq S] [StandardBorelSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsSpecification (indepSpec (S := S) ν) ∧ IsDobrushin (indepSpec (S := S) ν) ∧
      (∀ i j : S, interdep (indepSpec (S := S) ν) i j = 0) ∧
      (∀ μ : Measure (Config S E),
        IsGibbs (indepSpec (S := S) ν) μ ↔ μ = Measure.infinitePi fun _ : S ↦ ν) ∧
      ∀ ω : Config S E, TendstoLocally (fun Δ : Finset S ↦ indepSpec ν Δ ω) atTop
        (Measure.infinitePi fun _ : S ↦ ν) := by
  have hE : Nonempty E := GibbsChallenge.nonempty_of_isProbabilityMeasure ν
  have hspec : IsSpecification (indepSpec (S := S) ν) := isSpecification_indep ν
  have hdob : IsDobrushin (indepSpec (S := S) ν) := Indep.isDobrushin_indepSpec ν
  obtain ⟨μ, hμ, huniq, hconv⟩ :=
    exists_isGibbs_tendstoLocally_of_isDobrushin (indepSpec (S := S) ν) hspec hdob
  have hprod : (Measure.infinitePi fun _ : S ↦ ν) = μ := huniq _ (isGibbs_indep ν)
  refine ⟨hspec, hdob, Indep.interdep_indepSpec ν,
    fun ρ ↦ ⟨fun hρ ↦ by rw [huniq ρ hρ, hprod], fun hρ ↦ ?_⟩, fun ω ↦ ?_⟩
  · rw [hρ]
    exact isGibbs_indep ν
  · rw [hprod]
    exact hconv ω

end DobrushinChallenge

end

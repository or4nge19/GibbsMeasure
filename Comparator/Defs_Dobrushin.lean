import Comparator.Defs

/-!
# Dobrushin's uniqueness theorem: definitions

Georgii's Section 8.1: the uniform distance, Dobrushin's interdependence matrix and his condition
of weak dependence, the single-site oscillation, and the series `D(γ)`.

## Main definitions

* `unifDist`: Georgii (8.1), the uniform distance `‖α₁ − α₂‖` between probability measures.
* `proj`: Georgii (8.4), the law of the single spin `σ_i` under `γ_{i}(·|ζ)`.
* `interdep`: Georgii (8.5), Dobrushin's interdependence matrix `C_ij(γ)`.
* `IsLocalFn`, `IsQuasilocalFn`: Georgii (2.20), local and quasilocal observables.
* `IsQuasilocalSpec`: Georgii (2.23), quasilocality of a specification.
* `IsDobrushin`: Georgii (8.6), Dobrushin's condition of weak dependence.
* `oscAt`: Georgii (8.14), the single-site oscillation `δ_j(f)`.
* `interdepSeries`, `interdepTail`: Georgii (8.19), the series `D(γ) b = ∑_{n ≥ 0} C(γ)^n b`.
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

/-! ## Georgii (8.1): the uniform distance -/

/-- **Georgii (8.1)**: the uniform distance `‖α₁ − α₂‖ = sup_A |α₁(A) − α₂(A)|` between two
probability measures on `E`. The value is recorded in `ℝ≥0∞` purely so that the suprema and series
below need no boundedness side conditions. -/
def unifDist (α₁ α₂ : Measure E) : ℝ≥0∞ :=
  ⨆ (A : Set E) (_ : MeasurableSet A), ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal|

theorem le_unifDist {α₁ α₂ : Measure E} {A : Set E} (hA : MeasurableSet A) :
    ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal| ≤ unifDist α₁ α₂ :=
  le_iSup₂ (f := fun (A : Set E) (_ : MeasurableSet A) ↦
    ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal|) A hA

theorem unifDist_le {α₁ α₂ : Measure E} {c : ℝ≥0∞}
    (h : ∀ A : Set E, MeasurableSet A → ENNReal.ofReal |(α₁ A).toReal - (α₂ A).toReal| ≤ c) :
    unifDist α₁ α₂ ≤ c := iSup₂_le h

theorem unifDist_comm (α₁ α₂ : Measure E) : unifDist α₁ α₂ = unifDist α₂ α₁ := by
  simp only [unifDist, abs_sub_comm]

@[simp] theorem unifDist_self (α : Measure E) : unifDist α α = 0 := by
  simp [unifDist]

theorem unifDist_le_one (α₁ α₂ : Measure E) [IsProbabilityMeasure α₁] [IsProbabilityMeasure α₂] :
    unifDist α₁ α₂ ≤ 1 := by
  have key : ∀ (α : Measure E) (_ : IsProbabilityMeasure α) (A : Set E),
      0 ≤ (α A).toReal ∧ (α A).toReal ≤ 1 := by
    intro α hα A
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  refine unifDist_le fun A _ ↦ ENNReal.ofReal_le_one.2 ?_
  obtain ⟨h1, h2⟩ := key α₁ ‹_› A
  obtain ⟨h3, h4⟩ := key α₂ ‹_› A
  rw [abs_le]
  constructor <;> linarith

/-! ## Georgii (8.4), (8.5): the single-site distributions and Dobrushin's matrix -/

/-- **Georgii (8.4)**: `γ_i^0(·|ζ)`, the law of the single spin `σ_i` under the single-site
kernel `γ_{i}(·|ζ)`. -/
def proj (γ : Finset S → Config S E → Measure (Config S E)) (i : S) (ζ : Config S E) :
    Measure E := (γ {i} ζ).map fun ω ↦ ω i

/-- **Georgii (8.5)**: Dobrushin's interdependence matrix
`C_ij(γ) = sup { ‖γ_i^0(·|ζ) − γ_i^0(·|η)‖ : ζ, η agree off the single site j }`. -/
def interdep (γ : Finset S → Config S E → Measure (Config S E)) (i j : S) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E) (_ : ∀ k, k ≠ j → ζ k = η k),
    unifDist (proj γ i ζ) (proj γ i η)

theorem le_interdep {γ : Finset S → Config S E → Measure (Config S E)} {i j : S}
    {ζ η : Config S E} (h : ∀ k, k ≠ j → ζ k = η k) :
    unifDist (proj γ i ζ) (proj γ i η) ≤ interdep γ i j :=
  le_iSup_of_le ζ (le_iSup_of_le η (le_iSup_of_le h le_rfl))

theorem interdep_le {γ : Finset S → Config S E → Measure (Config S E)} {i j : S} {c : ℝ≥0∞}
    (h : ∀ ζ η : Config S E, (∀ k, k ≠ j → ζ k = η k) →
      unifDist (proj γ i ζ) (proj γ i η) ≤ c) :
    interdep γ i j ≤ c := iSup₂_le fun ζ η ↦ iSup_le (h ζ η)

/-! ## Georgii (2.20), (2.23): local and quasilocal observables -/

/-- A bounded function on the configuration space. -/
def IsBddFn (f : Config S E → ℝ) : Prop := ∃ C : ℝ, ∀ ω, |f ω| ≤ C

/-- **Georgii (2.20)(a)**: a *local* observable, i.e. an element of `𝓛 = ⋃_Λ 𝓛_Λ`: a bounded
function that is `𝓕_Λ`-measurable for some finite volume `Λ`. -/
def IsLocalFn (f : Config S E → ℝ) : Prop :=
  IsBddFn f ∧ ∃ Λ : Finset S, Measurable[inside Λ] f

theorem IsLocalFn.measurable {f : Config S E → ℝ} (hf : IsLocalFn f) : Measurable f := by
  obtain ⟨Λ, hΛ⟩ := hf.2
  exact hΛ.mono (inside_le Λ) le_rfl

/-- **Georgii (2.20)(b)**: a *quasilocal* observable, i.e. an element of `𝓛̄`: a bounded function
which is a **uniform** limit of local observables. -/
def IsQuasilocalFn (f : Config S E → ℝ) : Prop :=
  IsBddFn f ∧ ∀ ε : ℝ, 0 < ε → ∃ g : Config S E → ℝ, IsLocalFn g ∧ ∀ ω, |f ω - g ω| ≤ ε

theorem IsLocalFn.isQuasilocalFn {f : Config S E → ℝ} (hf : IsLocalFn f) : IsQuasilocalFn f :=
  ⟨hf.1, fun ε hε ↦ ⟨f, hf, fun ω ↦ by simp [le_of_lt hε]⟩⟩

theorem IsQuasilocalFn.measurable {f : Config S E → ℝ} (hf : IsQuasilocalFn f) : Measurable f := by
  have hex : ∀ n : ℕ, ∃ g : Config S E → ℝ, IsLocalFn g ∧ ∀ ω, |f ω - g ω| ≤ 1 / (n + 1) :=
    fun n ↦ hf.2 (1 / (n + 1)) (by positivity)
  choose g hg1 hg2 using hex
  refine measurable_of_tendsto_metrizable (fun n ↦ (hg1 n).measurable) ?_
  rw [tendsto_pi_nhds]
  intro ω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn ↦ ?_⟩
  have hmono : (1 : ℝ) / (n + 1) ≤ 1 / (N + 1) := by
    have : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact one_div_le_one_div_of_le (by positivity) this
  rw [Real.dist_eq, abs_sub_comm]
  calc |f ω - g n ω| ≤ 1 / (n + 1) := hg2 n ω
    _ ≤ 1 / (N + 1) := hmono
    _ < ε := hN

/-- **Georgii, Definition (2.23)**: the specification `γ` is *quasilocal* if `f ∈ 𝓛` implies
`γ_Λ f ∈ 𝓛̄` for every `Λ ∈ 𝓢`, where `(γ_Λ f)(ω) = ∫ f dγ_Λ(·|ω)`.

The premise is that `f` be **local**, not merely quasilocal, following Georgii's remark after
(2.23); this is the weaker demand on `γ`, so `IsDobrushin` below is a weaker hypothesis and the
uniqueness theorem consuming it is correspondingly stronger. -/
def IsQuasilocalSpec (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  ∀ (Λ : Finset S) (f : Config S E → ℝ), IsLocalFn f →
    IsQuasilocalFn fun ω ↦ ∫ x, f x ∂(γ Λ ω)

/-- `IsQuasilocalSpec` is the weaker of the two readings of (2.23): the quasilocal-premise reading
implies it, since local observables are quasilocal. -/
theorem isQuasilocalSpec_of_forall_isQuasilocalFn
    {γ : Finset S → Config S E → Measure (Config S E)}
    (h : ∀ (Λ : Finset S) (f : Config S E → ℝ), IsQuasilocalFn f →
      IsQuasilocalFn fun ω ↦ ∫ x, f x ∂(γ Λ ω)) :
    IsQuasilocalSpec γ :=
  fun Λ f hf ↦ h Λ f hf.isQuasilocalFn

/-! ## Georgii (8.6): Dobrushin's condition of weak dependence -/

/-- **Georgii (8.6)**: Dobrushin's condition of weak dependence: `γ` is quasilocal and
`c(γ) = sup_i ∑_j C_ij(γ) < 1`. The quasilocality conjunct carries real content — Georgii's
Example (2.27) has `C_ij(γ) = 0` for all `i, j` while `𝓖(γ)` is uncountable. -/
def IsDobrushin (γ : Finset S → Config S E → Measure (Config S E)) : Prop :=
  IsQuasilocalSpec γ ∧ ⨆ i, ∑' j, interdep γ i j < 1

/-! ## Georgii (8.14), (8.19): the single-site oscillation and the series `D(γ)` -/

/-- **Georgii (8.14)**: the single-site oscillation
`δ_j(f) = sup { |f(ζ) − f(η)| : ζ, η agree off the single site j }`. -/
def oscAt (f : Config S E → ℝ) (j : S) : ℝ≥0∞ :=
  ⨆ (ζ : Config S E) (η : Config S E) (_ : ∀ k, k ≠ j → ζ k = η k),
    ENNReal.ofReal |f ζ - f η|

omit [MeasurableSpace E] in
@[simp] theorem oscAt_const (r : ℝ) (j : S) : oscAt (fun _ : Config S E ↦ r) j = 0 := by
  simp [oscAt]

/-- `C(γ)^n b`, the `n`-fold action of Dobrushin's interdependence matrix on a vector. -/
def interdepIter (γ : Finset S → Config S E → Measure (Config S E)) :
    ℕ → (S → ℝ≥0∞) → S → ℝ≥0∞
  | 0, b => b
  | (n + 1), b => fun i ↦ ∑' j, interdep γ i j * interdepIter γ n b j

/-- **Georgii (8.19)**: `D(γ) b = ∑_{n ≥ 0} C(γ)^n b`. -/
def interdepSeries (γ : Finset S → Config S E → Measure (Config S E)) (b : S → ℝ≥0∞) (i : S) :
    ℝ≥0∞ := ∑' n : ℕ, interdepIter γ n b i

/-- The tail `∑_{j ∉ Δ} D_ij(γ)` of Georgii's series (8.19), the error term of the Cauchy
estimate (8.23). -/
def interdepTail [DecidableEq S] (γ : Finset S → Config S E → Measure (Config S E))
    (Δ : Finset S) (i : S) : ℝ≥0∞ :=
  interdepSeries γ (fun j ↦ if j ∈ Δ then 0 else 1) i


/-! ## The `inside` σ-algebra: locality

Mirrors of the preamble's `outside` lemmas, used to recognise a function as *local* in the sense
of Georgii (2.20)(a).
-/

/-- The restriction of a configuration to `Λ`. -/
def restrictInside (Λ : Finset S) (ω : Config S E) : {i : S // i ∈ Λ} → E := fun i ↦ ω i.1

theorem measurable_restrictInside (Λ : Finset S) :
    Measurable[inside Λ] (restrictInside (E := E) Λ) :=
  measurable_pi_of _ fun i ↦ Measurable.of_comap_le (comap_le_inside i.2)

/-- `𝓕_Λ` is the σ-algebra pulled back along the restriction map `ω ↦ ω|_Λ`. -/
theorem inside_eq_comap (Λ : Finset S) :
    inside (E := E) Λ = MeasurableSpace.comap (restrictInside Λ) inferInstance := by
  refine le_antisymm ?_ (measurable_restrictInside Λ).comap_le
  refine iSup₂_le fun i hi ↦ ?_
  have h1 : Measurable[MeasurableSpace.comap (restrictInside (E := E) Λ) inferInstance]
      (restrictInside Λ) := Measurable.of_comap_le le_rfl
  exact ((measurable_pi_apply (⟨i, hi⟩ : {i : S // i ∈ Λ})).comp h1).comap_le

/-- **Events measurable inside `Λ` do not depend on the coordinates off `Λ`.** -/
theorem mem_iff_mem_of_inside {Λ : Finset S} {B : Set (Config S E)}
    (hB : MeasurableSet[inside Λ] B) {ω ω' : Config S E} (h : ∀ i ∈ Λ, ω i = ω' i) :
    ω ∈ B ↔ ω' ∈ B := by
  rw [inside_eq_comap] at hB
  obtain ⟨C, -, rfl⟩ := hB
  have hr : restrictInside Λ ω = restrictInside Λ ω' := funext fun i ↦ h i.1 i.2
  simp only [Set.mem_preimage, hr]

/-- A `𝓕_Λ`-measurable real function does not depend on the coordinates off `Λ`. -/
theorem eq_of_measurable_inside {Λ : Finset S} {f : Config S E → ℝ}
    (hf : Measurable[inside Λ] f) {ω ω' : Config S E} (h : ∀ i ∈ Λ, ω i = ω' i) : f ω = f ω' := by
  have hB : MeasurableSet[inside Λ] (f ⁻¹' {f ω}) := hf (measurableSet_singleton (f ω))
  have hmem : ω' ∈ f ⁻¹' {f ω} := (mem_iff_mem_of_inside hB h).1 (by simp)
  simpa using hmem.symm

/-- Conversely, a measurable function not depending on the coordinates off `Λ` is
`𝓕_Λ`-measurable. -/
theorem measurable_inside_of_local [Nonempty E] {α : Type*} [MeasurableSpace α] (Λ : Finset S)
    {f : Config S E → α} (hf : Measurable f)
    (hloc : ∀ ω ω' : Config S E, (∀ i ∈ Λ, ω i = ω' i) → f ω = f ω') :
    Measurable[inside Λ] f := by
  set ζ : Config S E := fun _ ↦ Classical.arbitrary E with hζ
  have hg : Measurable[inside Λ] fun ω : Config S E ↦ glue Λ ω ζ := by
    refine measurable_pi_of _ fun i ↦ ?_
    by_cases hi : i ∈ Λ
    · simp only [glue_of_mem hi]
      exact Measurable.of_comap_le (comap_le_inside hi)
    · simp only [glue_of_notMem hi]
      exact measurable_const
  have hfg : f = f ∘ fun ω : Config S E ↦ glue Λ ω ζ :=
    funext fun ω ↦ hloc _ _ fun i hi ↦ (glue_of_mem hi ω ζ).symm
  rw [hfg]
  exact hf.comp hg

/-! ## Non-vacuity: the independent specification satisfies Dobrushin's condition -/

namespace Indep

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- Under the independent specification `γ_i^0(·|ζ)` is the `i`-th marginal of `ν^S`; in
particular it does not depend on the boundary condition `ζ`. -/
theorem proj_indepSpec (i : S) (ζ : Config S E) :
    proj (indepSpec (S := S) ν) i ζ
      = Measure.map (fun σ : Config S E ↦ σ i) (Measure.infinitePi fun _ : S ↦ ν) := by
  rw [proj, indepSpec, Measure.map_map (measurable_pi_apply i)
    (measurable_glue_left ({i} : Finset S) ζ)]
  congr 1
  funext σ
  simp [Function.comp_def, glue_of_mem (Finset.mem_singleton_self i)]

/-- **Dobrushin's interdependence matrix of the independent specification vanishes.** -/
theorem interdep_indepSpec (i j : S) : interdep (indepSpec (S := S) ν) i j = 0 :=
  le_antisymm (interdep_le fun ζ η _ ↦ by
    rw [proj_indepSpec, proj_indepSpec, unifDist_self]) bot_le

/-- Averaging a local observable over the independent specification gives a local observable. -/
theorem isLocalFn_integral_indepSpec {f : Config S E → ℝ} (hf : IsLocalFn f) (Λ : Finset S) :
    IsLocalFn fun ω ↦ ∫ x, f x ∂(indepSpec (S := S) ν Λ ω) := by
  have hE : Nonempty E := GibbsChallenge.nonempty_of_isProbabilityMeasure ν
  obtain ⟨⟨C, hC⟩, Λ', hΛ'⟩ := hf
  have hfm : Measurable f := hΛ'.mono (inside_le Λ') le_rfl
  have heq : ∀ ω : Config S E, ∫ x, f x ∂(indepSpec (S := S) ν Λ ω)
      = ∫ σ, f (glue Λ σ ω) ∂(Measure.infinitePi fun _ : S ↦ ν) := by
    intro ω
    rw [indepSpec, integral_map (measurable_glue_left Λ ω).aemeasurable
      hfm.aestronglyMeasurable]
  have hmeas : Measurable fun ω : Config S E ↦ ∫ x, f x ∂(indepSpec (S := S) ν Λ ω) := by
    rw [funext heq]
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right'
      (f := fun p : Config S E × Config S E ↦ f (glue Λ p.2 p.1))
      (hfm.comp (measurable_glue_swap Λ)).stronglyMeasurable).measurable
  refine ⟨⟨C, fun ω ↦ ?_⟩, Λ', measurable_inside_of_local Λ' hmeas fun ω ω' hω ↦ ?_⟩
  · have hprob : IsProbabilityMeasure (indepSpec (S := S) ν Λ ω) := inferInstance
    have h := norm_integral_le_of_norm_le_const (μ := indepSpec (S := S) ν Λ ω) (f := f)
      (C := C) (Filter.Eventually.of_forall fun x ↦ by simpa [Real.norm_eq_abs] using hC x)
    simpa [Real.norm_eq_abs, measureReal_def] using h
  · rw [heq, heq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ ↦ ?_)
    refine eq_of_measurable_inside hΛ' fun i hi ↦ ?_
    by_cases hiΛ : i ∈ Λ
    · rw [glue_of_mem hiΛ, glue_of_mem hiΛ]
    · rw [glue_of_notMem hiΛ, glue_of_notMem hiΛ]
      exact hω i hi

/-- **The independent specification is quasilocal** in the sense of Georgii (2.23). -/
theorem isQuasilocalSpec_indepSpec : IsQuasilocalSpec (indepSpec (S := S) ν) :=
  fun Λ _ hf ↦ (isLocalFn_integral_indepSpec ν hf Λ).isQuasilocalFn

/-- **The independent specification satisfies Dobrushin's condition**, with `c(γ) = 0`. -/
theorem isDobrushin_indepSpec : IsDobrushin (indepSpec (S := S) ν) := by
  refine ⟨isQuasilocalSpec_indepSpec ν, ?_⟩
  refine lt_of_le_of_lt (iSup_le fun i ↦ ?_) (by norm_num : (0 : ℝ≥0∞) < 1)
  simp [interdep_indepSpec]

end Indep

end DobrushinChallenge

end

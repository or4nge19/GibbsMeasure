import Comparator.Defs_Simplex
import GibbsMeasure

/-!
# The simplex of Gibbs measures

Solution file matching `Comparator/Challenge_Simplex.lean`; the statements below are the
challenge's statements verbatim, and the extra `namespace SimplexBridge` translates the
from-scratch definitions of `Comparator.Defs_Simplex` into the `GibbsMeasure` library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

section Simplex

variable {S E : Type*} [MeasurableSpace E]

/-! ### The bridge to the `GibbsMeasure` library -/

namespace SimplexBridge

open ProbabilityTheory
open scoped ENNReal

variable {S E : Type*} [MeasurableSpace E]

/-- The preamble's external σ-algebra `𝓣_Λ` is the cylinder σ-algebra of `Λᶜ`, the library's source
σ-algebra for the `Λ`-kernel of a specification. -/
lemma outside_eq_cylinderEvents (Λ : Finset S) :
    outside (S := S) (E := E) Λ
      = MeasureTheory.cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) := rfl

/-- The preamble's tail σ-algebra is the library's `𝓣`. -/
lemma tail_eq_tailSigmaAlgebra :
    tail S E = MeasureTheory.GibbsMeasure.tailSigmaAlgebra S E := rfl

variable {γ : Finset S → Config S E → Measure (Config S E)}

lemma measurable_gamma (hγ : IsSpecification γ) (Λ : Finset S) : Measurable (γ Λ) := by
  have h : Measurable[outside Λ] (γ Λ) :=
    Measure.measurable_measure.2 fun A hA ↦ hγ.measurable_apply Λ A hA
  exact h.mono (outside_le Λ) le_rfl

/-- The `Λ`-kernel of the family `γ`, as a kernel from `𝓣_Λ` to `𝓕`. -/
def ker (hγ : IsSpecification γ) (Λ : Finset S) :
    @Kernel (Config S E) (Config S E)
      (MeasureTheory.cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) inferInstance :=
  @Kernel.mk (Config S E) (Config S E)
    (MeasureTheory.cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) inferInstance (γ Λ)
    (Measure.measurable_measure.2 fun A hA ↦ hγ.measurable_apply Λ A hA)

@[simp] lemma ker_apply (hγ : IsSpecification γ) (Λ : Finset S) (ω : Config S E) :
    ker hγ Λ ω = γ Λ ω := rfl

instance isMarkovKernel_ker (hγ : IsSpecification γ) (Λ : Finset S) :
    IsMarkovKernel (ker hγ Λ) := ⟨fun ω ↦ hγ.isProbabilityMeasure Λ ω⟩

lemma isProper_ker (hγ : IsSpecification γ) (Λ : Finset S) : (ker hγ Λ).IsProper := by
  refine (Kernel.isProper_iff_inter_eq_indicator_mul MeasureTheory.cylinderEvents_le_pi).2 ?_
  intro A hA B hB ω
  rw [ker_apply, hγ.proper Λ A B hA hB ω]
  by_cases h : ω ∈ B <;> simp [h]

lemma isConsistent_ker (hγ : IsSpecification γ) : IsConsistent (ker hγ) := by
  intro Λ₁ Λ₂ hΛ
  refine Kernel.ext fun ω ↦ Measure.ext fun A hA ↦ ?_
  rw [Kernel.comp_apply' _ _ _ hA]
  simp only [ker_apply]
  exact hγ.consistent Λ₁ Λ₂ hΛ ω A hA

/-- The library specification attached to a family satisfying the preamble's axioms. -/
def spec (hγ : IsSpecification γ) : Specification S E :=
  @Specification.mk S E _ (@PreSpecification.mk S E _ (ker hγ) (isConsistent_ker hγ))
    (fun Λ ↦ isMarkovKernel_ker hγ Λ) (fun Λ ↦ isProper_ker hγ Λ)

@[simp] lemma spec_apply (hγ : IsSpecification γ) (Λ : Finset S) (ω : Config S E) :
    spec hγ Λ ω = γ Λ ω := rfl

lemma coe_spec (hγ : IsSpecification γ) (Λ : Finset S) :
    ⇑(spec hγ Λ) = γ Λ := rfl

/-- The DLR equations of the preamble are the library's Gibbs property. -/
lemma isGibbs_iff_mem_G (hγ : IsSpecification γ) (μ : Measure (Config S E)) :
    IsGibbs γ μ ↔ μ ∈ MeasureTheory.GibbsMeasure.G (spec hγ) := by
  constructor
  · rintro ⟨hprob, hdlr⟩
    have : IsProbabilityMeasure μ := hprob
    refine ⟨hprob, ?_⟩
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
    intro Λ
    refine Measure.ext fun A hA ↦ ?_
    rw [coe_spec, Measure.bind_apply hA (measurable_gamma hγ Λ).aemeasurable]
    exact (hdlr Λ A hA).symm
  · rintro ⟨hprob, hgibbs⟩
    have : IsProbabilityMeasure μ := hprob
    refine ⟨hprob, fun Λ A hA ↦ ?_⟩
    have h := (Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob.1 hgibbs) Λ
    have h2 : (⇑(spec hγ Λ) ∘ₘ μ) A = μ A := by rw [h]
    rw [coe_spec, Measure.bind_apply hA (measurable_gamma hγ Λ).aemeasurable] at h2
    exact h2.symm

lemma gibbsSet_eq_G (hγ : IsSpecification γ) :
    GibbsSet γ = MeasureTheory.GibbsMeasure.G (spec hγ) :=
  Set.ext fun μ ↦ isGibbs_iff_mem_G hγ μ

/-- The from-scratch notion of extremality is Mathlib's `Set.extremePoints`. -/
lemma isExtremeIn_iff_mem_extremePoints (P : Set (Measure (Config S E)))
    (μ : Measure (Config S E)) :
    IsExtremeIn P μ ↔ μ ∈ P.extremePoints ℝ≥0∞ := by
  rw [mem_extremePoints]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ν₁ hν₁ ν₂ hν₂ hseg ↦ ?_⟩
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    exact h2 ν₁ hν₁ ν₂ hν₂ a b ha hb hab heq.symm
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ν₁ hν₁ ν₂ hν₂ a b ha hb hab heq ↦
      h2 ν₁ hν₁ ν₂ hν₂ ⟨a, b, ha, hb, hab, heq.symm⟩⟩

lemma setOf_isExtremeIn_eq (hγ : IsSpecification γ) :
    {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}
      = (MeasureTheory.GibbsMeasure.G (spec hγ)).extremePoints ℝ≥0∞ := by
  rw [← gibbsSet_eq_G hγ]
  exact Set.ext fun ν ↦ isExtremeIn_iff_mem_extremePoints _ ν

/-- The representing weight of Georgii (7.26) is the library's `weightOf`: it is carried by the
extreme Gibbs measures, it represents `μ`, and it is the only such weight. -/
lemma weightOf_spec [Countable S] [StandardBorelSpace E] (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ)
    (hG : (MeasureTheory.GibbsMeasure.G (spec hγ)).Nonempty) :
    MeasureTheory.GibbsMeasure.weightOf hG μ
        ((MeasureTheory.GibbsMeasure.G (spec hγ)).extremePoints ℝ≥0∞)ᶜ = 0 ∧
      Measure.join (MeasureTheory.GibbsMeasure.weightOf hG μ) = μ ∧
      ∀ w : Measure (Measure (Config S E)),
        w ((MeasureTheory.GibbsMeasure.G (spec hγ)).extremePoints ℝ≥0∞)ᶜ = 0 →
        Measure.join w = μ → w = MeasureTheory.GibbsMeasure.weightOf hG μ := by
  have hμG : μ ∈ MeasureTheory.GibbsMeasure.G (spec hγ) := (isGibbs_iff_mem_G hγ μ).1 hμ
  exact ⟨MeasureTheory.GibbsMeasure.weightOf_extremePoints_compl hG hμG,
    MeasureTheory.GibbsMeasure.join_weightOf hG hμG,
    fun w hw hjoin ↦ MeasureTheory.GibbsMeasure.eq_weightOf_of_join_eq hG hw hjoin⟩

/-- The same existence-and-uniqueness statement, read off the library's packaged form of
Georgii (7.26). -/
lemma existsUnique_weight_library [Countable S] [StandardBorelSpace E] (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    ∃! w : Measure (Measure (Config S E)), IsProbabilityMeasure w ∧
      w ((MeasureTheory.GibbsMeasure.G (spec hγ)).extremePoints ℝ≥0∞)ᶜ = 0 ∧
      Measure.join w = μ :=
  MeasureTheory.GibbsMeasure.exists_unique_weight_extremePoints
    ⟨μ, (isGibbs_iff_mem_G hγ μ).1 hμ⟩ ((isGibbs_iff_mem_G hγ μ).1 hμ)

/-- The from-scratch notion of tail-triviality is the library's. -/
lemma isTailTrivialOn_iff (μ : Measure (Config S E)) (hμ : IsProbabilityMeasure μ) :
    IsTailTrivialOn μ
      ↔ MeasureTheory.GibbsMeasure.IsTailTrivial
          (⟨μ, hμ⟩ : ProbabilityMeasure (Config S E)) := Iff.rfl

end SimplexBridge

/-! ### Georgii, Theorem (7.7)(a) -/

/-- **Georgii (7.7)(a)**: a Gibbs measure is an extreme point of `𝓖(γ)` iff it is trivial on the
tail σ-algebra. -/
theorem isExtremeIn_iff_isTailTrivialOn [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    IsExtremeIn (GibbsSet γ) μ ↔ IsTailTrivialOn μ := by
  have hμG : μ ∈ MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ) :=
    (SimplexBridge.isGibbs_iff_mem_G hγ μ).1 hμ
  rw [SimplexBridge.isExtremeIn_iff_mem_extremePoints, SimplexBridge.gibbsSet_eq_G hγ,
    SimplexBridge.isTailTrivialOn_iff μ hμ.1]
  exact MeasureTheory.GibbsMeasure.mem_extremePoints_G_iff_isTailTrivial
    (γ := SimplexBridge.spec hγ) ⟨μ, hμ.1⟩ hμG

/-! ### Georgii, Theorem (7.26) -/

/-- **Georgii (7.26)**, first half: over a standard Borel state space, a specification admitting a
Gibbs measure admits an extreme one. -/
theorem exists_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    ∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν := by
  have hG : (MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ)).Nonempty := by
    rwa [← SimplexBridge.gibbsSet_eq_G hγ]
  obtain ⟨ν, hν⟩ := MeasureTheory.GibbsMeasure.nonempty_extremePoints_G hG
  refine ⟨ν, ?_⟩
  rw [SimplexBridge.isExtremeIn_iff_mem_extremePoints, SimplexBridge.gibbsSet_eq_G hγ]
  exact hν

/-- **Georgii (7.26)**, second half, the extremal decomposition: every Gibbs measure `μ` is the
barycentre `μ = ∫ ν w(dν)` of a unique probability weight `w` concentrated on `ex 𝓖(γ)`. -/
theorem existsUnique_weight_isExtremeIn [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ : Measure (Config S E)} (hμ : IsGibbs γ μ) :
    ∃! w : Measure (Measure (Config S E)),
      IsProbabilityMeasure w ∧
        w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
        Measure.join w = μ := by
  have hμG : μ ∈ MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ) :=
    (SimplexBridge.isGibbs_iff_mem_G hγ μ).1 hμ
  have hG : (MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ)).Nonempty := ⟨μ, hμG⟩
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨hcarrier, hbary, huniq⟩ := SimplexBridge.weightOf_spec hγ hμ hG
  rw [SimplexBridge.setOf_isExtremeIn_eq hγ]
  exact ⟨MeasureTheory.GibbsMeasure.weightOf hG μ, ⟨inferInstance, hcarrier, hbary⟩,
    fun w hw ↦ huniq w hw.2.1 hw.2.2⟩

/-- **Georgii (7.26)**, both halves: a nonempty `𝓖(γ)` is a simplex, with nonempty extreme set
representing each of its elements uniquely. -/
theorem georgii_7_26 [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    (∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν) ∧
      ∀ μ ∈ GibbsSet γ, ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
          Measure.join w = μ :=
  ⟨exists_isExtremeIn hγ hne, fun _ hμ ↦ existsUnique_weight_isExtremeIn hγ hμ⟩

/-! ### Georgii, Theorem (7.7)(d) and Corollary (7.29) -/

/-- **Georgii (7.7)(d)**: distinct extreme Gibbs measures are mutually singular *on the tail
σ-algebra*: some tail event carries all of `μ` and none of `ν`. This is the theorem's actual
strength — mutual singularity on the ambient σ-algebra is the trailing corollary. -/
theorem mutuallySingular_of_isExtremeIn [Countable S]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    {μ ν : Measure (Config S E)} (hμ : IsExtremeIn (GibbsSet γ) μ)
    (hν : IsExtremeIn (GibbsSet γ) ν) (hne : μ ≠ ν) :
    (∃ A : Set (Config S E), MeasurableSet[tail S E] A ∧ μ A = 1 ∧ ν A = 0) ∧
      μ.MutuallySingular ν := by
  have hμ' : μ ∈ (MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ)).extremePoints ℝ≥0∞ := by
    rw [← SimplexBridge.gibbsSet_eq_G hγ, ← SimplexBridge.isExtremeIn_iff_mem_extremePoints]
    exact hμ
  have hν' : ν ∈ (MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ)).extremePoints ℝ≥0∞ := by
    rw [← SimplexBridge.gibbsSet_eq_G hγ, ← SimplexBridge.isExtremeIn_iff_mem_extremePoints]
    exact hν
  obtain ⟨A, hA, h1, h0⟩ :=
    MeasureTheory.GibbsMeasure.exists_tail_eq_one_eq_zero_of_mem_extremePoints hμ' hν' hne
  exact ⟨⟨A, hA, h1, h0⟩,
    MeasureTheory.GibbsMeasure.mutuallySingular_of_mem_extremePoints hμ' hν' hne⟩

/-- **Georgii (7.29)**: `𝓖(γ)` has at least `N` extreme points iff it contains `N` measures that
are linearly independent over `ℝ≥0∞`. -/
theorem le_encard_setOf_isExtremeIn_iff [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) (N : ℕ) :
    (N : ℕ∞) ≤ {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}.encard ↔
      ∃ μ : Fin N → Measure (Config S E), (∀ i, IsGibbs γ (μ i)) ∧ LinearIndependent ℝ≥0∞ μ := by
  have hG : (MeasureTheory.GibbsMeasure.G (SimplexBridge.spec hγ)).Nonempty := by
    rwa [← SimplexBridge.gibbsSet_eq_G hγ]
  rw [SimplexBridge.setOf_isExtremeIn_eq hγ,
    MeasureTheory.GibbsMeasure.le_encard_extremePoints_iff hG N]
  exact ⟨fun ⟨μ, hμ, hLI⟩ ↦ ⟨μ, fun i ↦ (SimplexBridge.isGibbs_iff_mem_G hγ (μ i)).2 (hμ i), hLI⟩,
    fun ⟨μ, hμ, hLI⟩ ↦ ⟨μ, fun i ↦ (SimplexBridge.isGibbs_iff_mem_G hγ (μ i)).1 (hμ i), hLI⟩⟩

/-! ### Non-degeneracy -/

/-- Non-degeneracy: the independent specification `indepSpec ν` has `ν^S` as a Gibbs measure, so
the hypotheses of `georgii_7_26` are satisfiable even for infinite `S`. -/
theorem gibbsSet_indepSpec_nonempty [Countable S] [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : S ↦ ν) ∈ GibbsSet (indepSpec (S := S) ν) ∧
      (∃ ρ : Measure (Config S E), IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ) ∧
      ∀ μ ∈ GibbsSet (indepSpec (S := S) ν), ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ρ : Measure (Config S E) | IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ}ᶜ = 0 ∧
          Measure.join w = μ := by
  have hmem : (Measure.infinitePi fun _ : S ↦ ν) ∈ GibbsSet (indepSpec (S := S) ν) :=
    isGibbs_indep ν
  obtain ⟨h1, h2⟩ := georgii_7_26 (isSpecification_indep ν) ⟨_, hmem⟩
  exact ⟨hmem, h1, h2⟩

end Simplex

end GibbsChallenge

end

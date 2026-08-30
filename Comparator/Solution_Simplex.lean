import Comparator.Defs_Simplex
import GibbsMeasure

/-!
# Comparator solution: the simplex of Gibbs measures (Georgii, Theorems (7.7)(a) and (7.26))

This is the *solution* file matching `Comparator/Challenge_Simplex.lean`.  Both files take their
definitions from the same modules `Comparator.Defs` and `Comparator.Defs_Simplex`, which import
`Mathlib` and nothing else, so the statements of the theorems below are literally the challenge's
statements; the only differences are the extra `import GibbsMeasure`, this module docstring, an
auxiliary `namespace SimplexBridge` block translating between those from-scratch definitions and
the `GibbsMeasure` library, and the proof terms.
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

/-! ### The bridge to the `GibbsMeasure` library

Everything in this namespace is auxiliary: it translates between the from-scratch definitions of
`Comparator.Defs` and `Comparator.Defs_Simplex` and the `GibbsMeasure` library.  None of the
statements of the challenge is touched. -/

namespace SimplexBridge

open ProbabilityTheory
open scoped ENNReal

variable {S E : Type*} [MeasurableSpace E]

/-- The preamble's external σ-algebra `𝓣_Λ` is Mathlib's cylinder σ-algebra of `Λᶜ`, which is what
the library uses as the source σ-algebra of the `Λ`-kernel of a specification. -/
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

/-- **The DLR equations of the preamble are the library's Gibbs property.** -/
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

/-- **The from-scratch notion of extremality is Mathlib's `Set.extremePoints`.** -/
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
extreme Gibbs measures (`weightOf_extremePoints_compl`), it represents `μ` (`join_weightOf`), and
any weight carried by the extreme Gibbs measures which represents `μ` is equal to it
(`eq_weightOf_of_join_eq`). -/
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

/-- **The from-scratch notion of tail-triviality is the library's.** -/
lemma isTailTrivialOn_iff (μ : Measure (Config S E)) (hμ : IsProbabilityMeasure μ) :
    IsTailTrivialOn μ
      ↔ MeasureTheory.GibbsMeasure.IsTailTrivial
          (⟨μ, hμ⟩ : ProbabilityMeasure (Config S E)) := Iff.rfl

end SimplexBridge

/-! ### Georgii, Theorem (7.7)(a) -/

/-- **Georgii, Theorem (7.7)(a).** Let `γ` be a specification on `E^S` with `S` countable. A Gibbs
measure `μ ∈ 𝓖(γ)` is an *extreme point* of `𝓖(γ)` if and only if it is *trivial on the tail
σ-algebra*. -/
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

/-- **Georgii, Theorem (7.26), first half.** Over a standard Borel state space and a countable
parameter set, if a specification admits at least one Gibbs measure then it admits at least one
*extreme* Gibbs measure. -/
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

/-- **Georgii, Theorem (7.26), second half: the extremal decomposition.** Over a standard Borel
state space and a countable parameter set, every Gibbs measure `μ` is the barycentre
`μ = ∫ ν w(dν)` of a **unique** probability measure `w` on the space of measures which is
concentrated on the set of extreme Gibbs measures. -/
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

/-- **Georgii, Theorem (7.26)**, both halves together: over a standard Borel state space and a
countable parameter set, a nonempty set of Gibbs measures is a simplex whose extreme points are
nonempty and represent every one of its elements uniquely. -/
theorem georgii_7_26 [Countable S] [StandardBorelSpace E]
    {γ : Finset S → Config S E → Measure (Config S E)} (hγ : IsSpecification γ)
    (hne : (GibbsSet γ).Nonempty) :
    (∃ ν : Measure (Config S E), IsExtremeIn (GibbsSet γ) ν) ∧
      ∀ μ ∈ GibbsSet γ, ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ν : Measure (Config S E) | IsExtremeIn (GibbsSet γ) ν}ᶜ = 0 ∧
          Measure.join w = μ :=
  ⟨exists_isExtremeIn hγ hne, fun _ hμ ↦ existsUnique_weight_isExtremeIn hγ hμ⟩

/-! ### Non-degeneracy -/

/-- **Non-degeneracy: the hypotheses above are not vacuous.** For a finite parameter set `S` and a
single-spin distribution `ν` on a standard Borel state space, the independent specification
`indepSpec ν` of the preamble has a nonempty set of Gibbs measures — the product measure `ν^S` is
one — and hence, by `georgii_7_26`, a nonempty set of *extreme* Gibbs measures, each Gibbs measure
being the barycentre of a unique weight carried by them. -/
theorem gibbsSet_indepSpec_nonempty [Fintype S] [StandardBorelSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : S ↦ ν) ∈ GibbsSet (indepSpec (S := S) ν) ∧
      (∃ ρ : Measure (Config S E), IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ) ∧
      ∀ μ ∈ GibbsSet (indepSpec (S := S) ν), ∃! w : Measure (Measure (Config S E)),
        IsProbabilityMeasure w ∧
          w {ρ : Measure (Config S E) | IsExtremeIn (GibbsSet (indepSpec (S := S) ν)) ρ}ᶜ = 0 ∧
          Measure.join w = μ := by
  have hmem : (Measure.pi fun _ : S ↦ ν) ∈ GibbsSet (indepSpec (S := S) ν) := isGibbs_indep ν
  obtain ⟨h1, h2⟩ := georgii_7_26 (isSpecification_indep ν) ⟨_, hmem⟩
  exact ⟨hmem, h1, h2⟩

end Simplex

end GibbsChallenge

end

module

public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.TrivialOn
public import GibbsMeasure.Mathlib.Order.Cofinal
public import GibbsMeasure.Mathlib.Probability.ConditionalProbability
public import GibbsMeasure.Mathlib.Probability.Kernel.InvariantSigmaAlgebra
public import GibbsMeasure.Specification.Abstract
public import GibbsMeasure.Specification.Structure
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Data.Set.Countable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Extremality and tail triviality (Georgii, Thm. (7.7)(a))

A Gibbs measure `μ ∈ G(γ)` is extreme in `G(γ)` if and only if it is trivial on the tail σ-algebra
`𝓣`. Both directions, and the (7.7)(b) tower feeding them, are derived from the abstract
Remark (7.13) versions in `GibbsMeasure.Specification.Abstract`, instantiated at `γ.toAbstract`
(the abstract specification with `𝓣_Λ = cylinderEvents Λᶜ` and kernels `γ Λ`, whose invariant
measures are exactly the Gibbs probability measures `G γ`).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

namespace GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

/-! ### Tail events are boundary events for every finite volume -/

lemma measurableSet_cylinderEvents_compl_of_measurableSet_tail
    (Λ : Finset S) {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] A := by
  have hle :
      (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤
        cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ) :=
    iInf_le (fun Λ : Finset S => cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) Λ
  exact hle _ hA

/-! ### Restricting a Gibbs measure to a tail event gives another Gibbs measure -/

section Restrict

variable (γ : Specification S E)

lemma bind_restrict_eq_of_measurableSet_boundary (Λ : Finset S)
    {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] A)
    (μ : Measure (S → E)) :
    (μ.restrict A).bind (γ Λ) = (μ.bind (γ Λ)).restrict A :=
  AbstractSpecification.bind_restrict (γ := γ.toAbstract) Λ hA μ

lemma bind_restrict_eq_of_measurableSet_tail (Λ : Finset S)
    {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A)
    (μ : Measure (S → E)) :
    (μ.restrict A).bind (γ Λ) = (μ.bind (γ Λ)).restrict A := by
  exact bind_restrict_eq_of_measurableSet_boundary (γ := γ) (Λ := Λ)
    (hA := measurableSet_cylinderEvents_compl_of_measurableSet_tail (S := S) (E := E) Λ hA) μ

/-- If `μ` is Gibbs for `γ`, then the restriction of `μ` to a tail event is also Gibbs. -/
lemma isGibbsMeasure_restrict_of_measurableSet_tail
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set (S → E)} (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) :
    _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ (μ.restrict A) := by
  have hfix : ∀ Λ : Finset S, μ.bind (γ Λ) = μ := by
    simpa [_root_.Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := γ)] using hμ
  have hfix_restrict : ∀ Λ : Finset S, (μ.restrict A).bind (γ Λ) = μ.restrict A := by
    intro Λ
    calc
      (μ.restrict A).bind (γ Λ)
          = (μ.bind (γ Λ)).restrict A :=
            bind_restrict_eq_of_measurableSet_tail (γ := γ) (Λ := Λ) (hA := hA) μ
      _ = μ.restrict A := by simp [hfix Λ]
  -- `μ.restrict A` is not a probability measure in general, so use the finite-measure fixed-point lemma.
  have : IsFiniteMeasure μ := by infer_instance
  have : IsFiniteMeasure (μ.restrict A) := by infer_instance
  exact (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ.restrict A)).2
      hfix_restrict

end Restrict

/-! ### From non-tail-triviality to non-extremality (Georgii Thm. 7.7, easy direction) -/

section ExtremePoints

open scoped Convex

variable (γ : Specification S E)

/-- The set `G(γ)` of Gibbs **probability** measures, viewed as a subset of `Measure (S → E)` so that
we can use Mathlib's `Set.extremePoints`. -/
def G : Set (Measure (S → E)) :=
  {μ | IsProbabilityMeasure μ ∧ _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ}

namespace G

variable {γ}

@[simp] lemma mem_iff (μ : Measure (S → E)) :
    μ ∈ G (γ := γ) ↔
      IsProbabilityMeasure μ ∧ _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ :=
  Iff.rfl

end G

section

variable {γ}

local notation3 "Ω" => (S → E)

lemma measurableSet_of_measurableSet_tail {A : Set Ω}
    (hA : MeasurableSet[@tailSigmaAlgebra S E _] A) : MeasurableSet A := by
  have hle_tail_pi :
      (@tailSigmaAlgebra S E _ : MeasurableSpace Ω) ≤ MeasurableSpace.pi := by
    refine le_trans
      (iInf_le (fun Λ : Finset S =>
          cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)) (∅ : Finset S)) ?_
    simp
  exact hle_tail_pi _ hA

/-! ### Proper kernels commute with `withDensity` for boundary-measurable densities -/

lemma lintegral_bind_indicator_boundary_eq (Λ : Finset S)
    (μ : Measure[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] f)
    {A : Set Ω} (hA : MeasurableSet A) :
    (∫⁻ x, A.indicator f x ∂(μ.bind (γ Λ))) =
      ∫⁻ η, f η * (γ Λ η) A ∂μ :=
  AbstractSpecification.lintegral_bind_indicator (γ := γ.toAbstract) Λ μ f hf hA

lemma withDensity_bind_eq_bind_withDensity (Λ : Finset S)
    (μ : Measure[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] f) :
    (μ.bind (γ Λ)).withDensity f = (μ.withDensity f).bind (γ Λ) :=
  AbstractSpecification.withDensity_bind (γ := γ.toAbstract) Λ μ f hf

/-- If a probability measure gives an event mass strictly below `1`, then the complement has
non-zero mass. -/
lemma measure_compl_ne_zero_of_lt_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (hA1 : μ A < 1) :
    μ Aᶜ ≠ 0 := by
  intro hAcompl0
  have hμA_le : μ A ≤ 1 := by
    have : μ A ≤ μ (Set.univ : Set Ω) := measure_mono (subset_univ A)
    simpa [IsProbabilityMeasure.measure_univ (μ := μ)] using this
  have hcompl : μ Aᶜ = 1 - μ A := prob_compl_eq_one_sub (μ := μ) hA
  have hμA : μ A = 1 := by
    have : 1 - μ A = 0 := by simpa [hcompl] using hAcompl0
    exact le_antisymm hμA_le ((tsub_eq_zero_iff_le).1 this)
  exact (ne_of_lt hA1) hμA

lemma isGibbsMeasure_cond_of_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra S E _] A) (hA0 : μ A ≠ 0) :
    _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ((ProbabilityTheory.cond μ A)) := by
  have hmem : μ ∈ γ.toAbstract.invariant :=
    (γ.mem_toAbstract_invariant_iff μ).2 ⟨‹IsProbabilityMeasure μ›, hμ⟩
  have hA' : MeasurableSet[γ.toAbstract.tail] A := by
    rw [γ.toAbstract_tail]; exact hA_tail
  exact ((γ.mem_toAbstract_invariant_iff _).1
    (AbstractSpecification.cond_mem_invariant hmem hA' hA0)).2

/-- If a Gibbs probability measure assigns a tail event probability strictly between `0` and `1`,
then it is **not** an extreme point of `G(γ)`.

Derived from `AbstractSpecification.not_mem_extremePoints_of_tail_prob` (Georgii (7.7),
in the generality of Remark (7.13)): `G(γ)` is the set of `γ.toAbstract`-invariant probability
measures, and conditioning on `A` and on `Aᶜ` exhibits `μ` as a proper convex combination of two
Gibbs measures. -/
theorem not_mem_extremePoints_G_of_tail_prob
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    {A : Set Ω} (hA_tail : MeasurableSet[@tailSigmaAlgebra S E _] A)
    (hA0 : 0 < μ A) (hA1 : μ A < 1) :
    μ ∉ (G (γ := γ)).extremePoints ENNReal := by
  have hG : G (γ := γ) = γ.toAbstract.invariant := (γ.toAbstract_invariant).symm
  have hA' : MeasurableSet[γ.toAbstract.tail] A := by
    rw [γ.toAbstract_tail]; exact hA_tail
  rw [hG]
  exact AbstractSpecification.not_mem_extremePoints_of_tail_prob
    ((γ.mem_toAbstract_invariant_iff μ).2 ⟨‹IsProbabilityMeasure μ›, hμ⟩) hA' hA0 hA1

/-- **Extreme** Gibbs probability measures are **tail-trivial** (Georgii Thm. 7.7, direction
`extreme → tail-trivial`). -/
theorem tailTrivial_of_mem_extremePoints_G
    {μ : Measure Ω}
    (hμext : μ ∈ (G (γ := γ)).extremePoints ENNReal) :
    ∀ A, MeasurableSet[@tailSigmaAlgebra S E _] A → μ A = 0 ∨ μ A = 1 := by
  have hG : G (γ := γ) = γ.toAbstract.invariant := (γ.toAbstract_invariant).symm
  rw [hG] at hμext
  intro A hA_tail
  have hA' : MeasurableSet[γ.toAbstract.tail] A := by
    rw [γ.toAbstract_tail]; exact hA_tail
  exact AbstractSpecification.mem_trivialOn_of_mem_extremePoints hμext A hA'

/-- Probability-measure version of `tailTrivial_of_mem_extremePoints_G`. -/
theorem isTailTrivial_of_mem_extremePoints_G
    (μ : ProbabilityMeasure Ω)
    (hμext : (μ : Measure Ω) ∈ (G (γ := γ)).extremePoints ENNReal) :
    IsTailTrivial (S := S) (E := E) μ := by
  intro A hA
  simpa using
    tailTrivial_of_mem_extremePoints_G (γ := γ) (μ := (μ : Measure Ω)) hμext A hA

/-! ### Tail-triviality implies extremality (Georgii Thm. 7.7, hard direction) -/

section TailTrivialImpliesExtreme

open Filter

variable [Countable S]

omit [MeasurableSpace E] [Countable S] in
lemma measurable_iInf_iff {ι : Sort*} (m : ι → MeasurableSpace Ω) {X : Type*}
    [MeasurableSpace X] {f : Ω → X} :
    Measurable[iInf m] f ↔ ∀ i, Measurable[m i] f :=
  measurable_iInf_iff_forall m

lemma iInf_eq_iInf_ge_of_antitone {α : Type*} [CompleteLattice α] (h : ℕ → α)
    (hh : Antitone h) (N : ℕ) :
    (⨅ n : ℕ, h n) = (⨅ n : {n // N ≤ n}, h n.1) :=
  iInf_ge_eq_iInf_of_antitone hh N

lemma antitone_iSup_ge {α : Type*} [CompleteLattice α] (g : ℕ → α) :
    Antitone (fun n : ℕ => (⨆ i : ℕ, ⨆ (_ : i ≥ n), g i)) :=
  antitone_iSup_ge_apply g

omit [MeasurableSpace E] [Countable S] in
lemma measurable_limsup_of_antitone_measurableSpace
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m)
    (g : ℕ → Ω → ℝ≥0∞) (hg : ∀ n, Measurable[m n] (g n)) :
    Measurable[iInf m] (fun ω : Ω => Filter.limsup (fun n => g n ω) atTop) :=
  measurable_limsup_iInf m hm g hg

/-- A monotone exhaustion of a countable `S` by finite volumes: the images of `Finset.range n`
under a fixed surjection `ℕ → S` (the constant empty family when `S` is empty). It is cofinal by
`exhaustionVolumes_cofinal`, so `⨅ n, cylinderEvents (exhaustionVolumes n)ᶜ` is the tail σ-algebra
(`tailSigmaAlgebra_eq_iInf_exhaustion`). -/
noncomputable def exhaustionVolumes : ℕ → Finset S := by
  classical
  by_cases hS : Nonempty S
  · exact fun n => (Finset.range n).image (Classical.choose (exists_surjective_nat S))
  · exact fun _ => ∅

lemma exhaustionVolumes_monotone :
    Monotone (exhaustionVolumes (S := S) : ℕ → Finset S) := by
  classical
  by_cases hS : Nonempty S
  · simp [exhaustionVolumes, hS]
    intro a b hab
    exact Finset.image_subset_image (Finset.range_mono hab)
  · intro a b hab
    simp [exhaustionVolumes, hS]

lemma exhaustionVolumes_cofinal (Λ : Finset S) :
    ∃ n : ℕ, Λ ⊆ exhaustionVolumes (S := S) n := by
  by_cases hS : Nonempty S
  · let f : ℕ → S := Classical.choose (exists_surjective_nat S)
    classical
    have hf : Function.Surjective f := Classical.choose_spec (exists_surjective_nat S)
    have hexh : (exhaustionVolumes (S := S) : ℕ → Finset S) = fun n => (Finset.range n).image f
        := by
      simp [exhaustionVolumes, hS, f]
    classical
    have : ∀ x : S, x ∈ Λ → ∃ n, f n = x := by
      intro x hx
      exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
    let ns : Finset ℕ := Λ.attach.image fun x => Classical.choose (hf x.1)
    have hns : ∀ x : S, x ∈ Λ → Classical.choose (hf x) ∈ ns := by
      intro x hx
      have : (⟨x, hx⟩ : {y // y ∈ Λ}) ∈ Λ.attach := by
        simp
      exact Finset.mem_image_of_mem _ this
    let n0 : ℕ := ns.sup id + 1
    refine ⟨n0, ?_⟩
    intro x hx
    have hx_idx : Classical.choose (hf x) < n0 := by
      have hle : Classical.choose (hf x) ≤ ns.sup id := by
        exact Finset.le_sup (f := id) (hns x hx)
      exact lt_of_le_of_lt hle (Nat.lt_succ_self _)
    have hx_mem_range : Classical.choose (hf x) ∈ Finset.range n0 := by
      simpa [Finset.mem_range] using hx_idx
    have hfx : f (Classical.choose (hf x)) = x := Classical.choose_spec (hf x)
    have : x ∈ (Finset.range n0).image f := by
      refine Finset.mem_image.2 ?_
      refine ⟨Classical.choose (hf x), hx_mem_range, ?_⟩
      simp [hfx]
    simpa [hexh] using this
  · have : Λ = ∅ := by
      classical
      simpa using (Finset.eq_empty_of_forall_notMem (s := Λ) (by
        intro x hx
        exact (hS ⟨x⟩)))
    subst this
    refine ⟨0, by simp [exhaustionVolumes, hS]⟩

lemma tailSigmaAlgebra_eq_iInf_exhaustion :
    (@tailSigmaAlgebra S E _ : MeasurableSpace Ω)
      =
      ⨅ n : ℕ,
        cylinderEvents (X := fun _ : S ↦ E) (((exhaustionVolumes (S := S) n : Finset S) : Set
            S)ᶜ) := by
  refine iInf_eq_iInf_comp_of_cofinal
    (m := fun Λ : Finset S => cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ))
    (fun Λ₁ Λ₂ h => cylinderEvents_mono (X := fun _ : S ↦ E)
      (compl_subset_compl.2 (Finset.coe_subset.2 h))) fun Λ => ?_
  obtain ⟨n, hn⟩ := exhaustionVolumes_cofinal (S := S) Λ
  exact ⟨n, hn⟩

omit [Countable S] in
lemma bind_eq_bind_trim (Λ : Finset S) (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    (μ.trim (MeasureTheory.cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := ((Λ : Set S)ᶜ)))).bind
        (γ Λ) A
      =
    μ.bind (γ Λ) A :=
  AbstractSpecification.bind_trim (γ := γ.toAbstract) Λ μ hA

omit [Countable S] in
lemma exists_withDensity_of_absolutelyContinuous_gibbs
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hν : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    (hνμ : ν ≪ μ) (Λ : Finset S) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] g ∧
      μ.withDensity g = ν := by
  have hbindμ : μ.bind (γ Λ) = μ :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ)).1 hμ Λ
  have hbindν : ν.bind (γ Λ) = ν :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := ν)).1 hν Λ
  exact AbstractSpecification.exists_withDensity_of_absolutelyContinuous
    (γ := γ.toAbstract) Λ hbindμ hbindν hνμ

lemma ae_eq_tailMeasurable_of_forall_boundary
    {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hν : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    (hνμ : ν ≪ μ) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[@tailSigmaAlgebra S E _] g ∧
      (ν.rnDeriv μ) =ᵐ[μ] g := by
  have hbindμ : ∀ Λ : Finset S, μ.bind (γ Λ) = μ :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := μ)).1 hμ
  have hbindν : ∀ Λ : Finset S, ν.bind (γ Λ) = ν :=
    (_root_.Specification.isGibbsMeasure_iff_forall_bind_eq (γ := γ) (μ := ν)).1 hν
  obtain ⟨g, hg, hfg⟩ := AbstractSpecification.exists_tail_measurable_rnDeriv
    (γ := γ.toAbstract) hbindμ hbindν hνμ
  refine ⟨g, ?_, hfg⟩
  rw [← γ.toAbstract_tail]
  exact hg

/-- If `μ` is Gibbs and tail-trivial, then any absolutely continuous Gibbs measure equals `μ`.

This is the key analytic step in Georgii Thm. 7.7, direction `tail-trivial → extreme`. -/
theorem eq_of_absolutelyContinuous_of_isTailTrivial
    {μ ν : Measure Ω}
    (hμG : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ μ)
    (hνG : _root_.Specification.IsGibbsMeasure (S := S) (E := E) γ ν)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμtail : IsTailTrivial (S := S) (E := E) (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure
        Ω))
    (hνμ : ν ≪ μ) :
    ν = μ := by
  have hμ' : μ ∈ γ.toAbstract.invariant :=
    (γ.mem_toAbstract_invariant_iff μ).2 ⟨‹IsProbabilityMeasure μ›, hμG⟩
  have hν' : ν ∈ γ.toAbstract.invariant :=
    (γ.mem_toAbstract_invariant_iff ν).2 ⟨‹IsProbabilityMeasure ν›, hνG⟩
  have htriv : μ ∈ trivialOn γ.toAbstract.tail :=
    (γ.isTailTrivial_iff_mem_trivialOn_toAbstract
      (⟨μ, ‹IsProbabilityMeasure μ›⟩ : ProbabilityMeasure Ω)).1 hμtail
  exact AbstractSpecification.eq_of_absolutelyContinuous hμ' hν' htriv hνμ

/-- **Tail-trivial** Gibbs probability measures are **extreme** (Georgii Thm. 7.7, direction
`tail-trivial → extreme`). -/
theorem mem_extremePoints_G_of_isTailTrivial
    {μ : Measure Ω}
    (hμG : μ ∈ G (γ := γ))
    (hμtail : IsTailTrivial (S := S) (E := E) (⟨μ, hμG.1⟩ : ProbabilityMeasure Ω)) :
    μ ∈ (G (γ := γ)).extremePoints ENNReal := by
  have hG : G (γ := γ) = γ.toAbstract.invariant := (γ.toAbstract_invariant).symm
  have hμ' : μ ∈ γ.toAbstract.invariant :=
    (γ.mem_toAbstract_invariant_iff μ).2 ⟨hμG.1, hμG.2⟩
  have htriv : μ ∈ trivialOn γ.toAbstract.tail :=
    (γ.isTailTrivial_iff_mem_trivialOn_toAbstract (⟨μ, hμG.1⟩ : ProbabilityMeasure Ω)).1 hμtail
  rw [hG]
  exact AbstractSpecification.mem_extremePoints_of_mem_trivialOn hμ' htriv

end TailTrivialImpliesExtreme

end

end ExtremePoints

end GibbsMeasure

end MeasureTheory

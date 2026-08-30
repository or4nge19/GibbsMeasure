import Comparator.Defs_MarkovChain
import GibbsMeasure

/-!
# Markov chains as Gibbs measures on `ℤ`: solution (Georgii, Theorem (3.5))

The solution file matching `Comparator/Challenge_MarkovChain.lean`. It differs from the challenge
only by `import GibbsMeasure`, the auxiliary `namespace Bridge` translating the from-scratch
definitions into the `GibbsMeasure` library, and the proof terms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace MarkovChainChallenge

open GibbsChallenge

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [Nonempty E]

/-! ### Bridge to the `GibbsMeasure` development

Auxiliary: translates the from-scratch notions of `Comparator.Defs` and
`Comparator.Defs_MarkovChain` into the vocabulary of the `GibbsMeasure` library, so that the
theorems below can be discharged by `Markov.gibbsMeasure_eq_singleton` and
`Markov.markovChain_cylinder`. -/

namespace Bridge

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [Nonempty E]

/-! #### The σ-algebras match -/

/-- The preamble's `outside Λ` is Mathlib's `cylinderEvents ((Λ : Set ℤ)ᶜ)`, on the nose. -/
theorem outside_eq_cylinderEvents (Λ : Finset ℤ) :
    outside (S := ℤ) (E := E) Λ = cylinderEvents ((Λ : Set ℤ)ᶜ) := rfl

/-! #### A challenge specification is a library specification -/

variable (γ : Finset ℤ → Config ℤ E → Measure (Config ℤ E))

/-- The `Λ`-kernel of a challenge specification, as a library kernel from `cylinderEvents Λᶜ`. -/
def toKernel (hγ : IsSpecification γ) (Λ : Finset ℤ) :
    Kernel[cylinderEvents ((Λ : Set ℤ)ᶜ)] (ℤ → E) (ℤ → E) :=
  @Kernel.mk _ _ (_) _ (γ Λ)
    (Measure.measurable_measure.2 fun A hA => hγ.measurable_apply Λ A hA)

@[simp] theorem toKernel_apply (hγ : IsSpecification γ) (Λ : Finset ℤ) (ω : Config ℤ E) :
    toKernel γ hγ Λ ω = γ Λ ω := rfl

/-- A challenge specification, packaged as a library `Specification ℤ E`. -/
def toSpec (hγ : IsSpecification γ) : Specification ℤ E where
  toFun := toKernel γ hγ
  isConsistent' := by
    intro Λ₁ Λ₂ h
    refine Kernel.ext fun ω => ?_
    rw [Kernel.comp_apply]
    refine Measure.ext fun A hA => ?_
    rw [Measure.bind_apply hA (Kernel.measurable _).aemeasurable]
    simp only [toKernel_apply]
    exact hγ.consistent Λ₁ Λ₂ h ω A hA
  isMarkovKernel' := fun Λ => ⟨fun ω => hγ.isProbabilityMeasure Λ ω⟩
  isProper' := fun Λ =>
    Kernel.IsProper.of_inter_eq_indicator_mul cylinderEvents_le_pi fun A hA B hB ω => by
      have h := hγ.proper Λ A B hA hB ω
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω] at h
        rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul]
        exact h
      · rw [Set.indicator_of_notMem hω] at h
        rw [Set.indicator_of_notMem hω, zero_mul]
        exact h

@[simp] theorem toSpec_apply (hγ : IsSpecification γ) (Λ : Finset ℤ) (ω : Config ℤ E) :
    toSpec γ hγ Λ ω = γ Λ ω := rfl

/-- The challenge's DLR equations are the library's `IsGibbsMeasure`. -/
theorem isGibbs_iff (hγ : IsSpecification γ) (ν : Measure (Config ℤ E)) :
    IsGibbs γ ν ↔ ν ∈ MeasureTheory.GibbsMeasure.G (toSpec γ hγ) := by
  constructor
  · rintro ⟨hprob, hdlr⟩
    have := hprob
    refine ⟨hprob, ?_⟩
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
    intro Λ
    refine Measure.ext fun A hA => ?_
    rw [Measure.bind_apply hA
      (((toSpec γ hγ) Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable]
    exact (hdlr Λ A hA).symm
  · rintro ⟨hprob, hgibbs⟩
    have := hprob
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob] at hgibbs
    refine ⟨hprob, fun Λ A hA => ?_⟩
    have h : (ν.bind ((toSpec γ hγ) Λ)) A = ν A := by rw [hgibbs Λ]
    rw [Measure.bind_apply hA
      (((toSpec γ hγ) Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable] at h
    exact h.symm

/-- Conversely, a library `Specification ℤ E` satisfies the preamble's axioms. -/
theorem ofSpec (Γ : Specification ℤ E) :
    IsSpecification (fun Λ (ω : Config ℤ E) ↦ Γ Λ ω) where
  isProbabilityMeasure Λ ω := inferInstance
  measurable_apply Λ A hA := Kernel.measurable_coe (Γ Λ) hA
  proper Λ := by
    intro A B hA hB ω
    have h := (Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi).1
      (Γ.isProper Λ) hA hB ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω, Pi.one_apply, one_mul] at h
      rw [Set.indicator_of_mem hω]
      exact h
    · rw [Set.indicator_of_notMem hω, zero_mul] at h
      rw [Set.indicator_of_notMem hω]
      exact h
  consistent Λ Δ hsub ω A hA := by
    have h := _root_.Specification.bind (γ := Γ) (hΛ := hsub) (η := ω)
    have h2 : ((Γ Δ ω).bind (Γ Λ)) A = Γ Δ ω A := by rw [h]
    rwa [Measure.bind_apply hA
      (((Γ Λ).measurable.mono cylinderEvents_le_pi le_rfl)).aemeasurable] at h2

/-! #### The matrix side -/

/-- `P : E → E → ℝ` viewed as a matrix. -/
def toMatrix (P : E → E → ℝ) : Matrix E E ℝ := Matrix.of P

@[simp] theorem toMatrix_apply (P : E → E → ℝ) (x y : E) : toMatrix P x y = P x y := rfl

theorem toMatrix_mem_rowStochastic (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1) : toMatrix P ∈ Matrix.rowStochastic ℝ E :=
  Matrix.mem_rowStochastic_iff_sum.2 ⟨fun i j => (hpos i j).le, hstoch⟩

/-- The challenge's determining function (3.11) is the library's. -/
theorem determiningFun_eq (P : E → E → ℝ) :
    determiningFun P = markovDeterminingFun (toMatrix P) := by
  funext x y z
  rw [determiningFun, markovDeterminingFun, pow_two, Matrix.mul_apply]
  rfl

/-- A challenge specification whose singleton kernels are given by (3.11) *is* the library's
`markovSpecification`. This is Georgii's step 4. -/
theorem toSpec_eq_markovSpecification (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hγ : IsSpecification γ)
    (hsingle : ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
      γ {i} ω {σ : Config ℤ E | σ i = y}
        = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1)))) :
    toSpec γ hγ = markovSpecification (toMatrix P) := by
  refine eq_markovSpecification_of_determiningFun (P := toMatrix P) (g := determiningFun P)
    (fun x y => hpos x y) ⟨fun x y z => ?_, fun i y ω => hsingle i y ω⟩ (determiningFun_eq P)
  rw [determiningFun_eq P]
  exact markovDeterminingFun_pos (fun x y => hpos x y) x y z

/-! #### Reindexing the path product -/

theorem prod_Ico_eq_prod_range (a : ℤ) (n : ℕ) (f : ℤ → ℝ) :
    ∏ k ∈ Finset.Ico a (a + (n : ℤ)), f k = ∏ k ∈ Finset.range n, f (a + (k : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Finset.Ico a (a + ((n : ℤ) + 1))
        = insert (a + (n : ℤ)) (Finset.Ico a (a + (n : ℤ))) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have h2 : (a + (n : ℤ)) ∉ Finset.Ico a (a + (n : ℤ)) := by simp
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, h1, Finset.prod_insert h2,
      Finset.prod_range_succ, ih, mul_comm]

set_option linter.unusedSectionVars true

end Bridge

/-- **Georgii, Theorem (3.5)**: for a strictly positive stochastic matrix `P` on a finite state
space `E`, *any* specification `γ` on `ℤ` whose singleton kernels are given by the determining
function (3.11), `γ_{i}(σ_i = y | ω) = P(ω_{i-1}, y) P(y, ω_{i+1}) / P²(ω_{i-1}, ω_{i+1})`, has
exactly one Gibbs measure, namely the stationary Markov chain `μ_P`: for the strictly positive
`P`-invariant probability vector `α`,
`μ(σ_a = x_a, …, σ_{a+n} = x_{a+n}) = α(x_a) P(x_a, x_{a+1}) ⋯ P(x_{a+n-1}, x_{a+n})`. -/
theorem georgii_3_5_markovChain (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1)
    (γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E))
    (hγ : IsSpecification γ)
    (hsingle : ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
      γ {i} ω {σ : Config ℤ E | σ i = y}
        = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1)))) :
    ∃ (μ : MeasureTheory.Measure (Config ℤ E)) (α : E → ℝ),
      (∀ y, 0 < α y) ∧
      (∑ y, α y = 1) ∧
      (∀ y, ∑ x, α x * P x y = α y) ∧
      (∀ (a : ℤ) (n : ℕ) (x : Config ℤ E),
        μ (cylinder a (a + n) x)
          = ENNReal.ofReal (α (x a) * ∏ k ∈ Finset.range n, P (x (a + k)) (x (a + k + 1)))) ∧
      (∀ ν : MeasureTheory.Measure (Config ℤ E), IsGibbs γ ν ↔ ν = μ) :=
  by
    have hQ : Bridge.toMatrix P ∈ Matrix.rowStochastic ℝ E :=
      Bridge.toMatrix_mem_rowStochastic P hpos hstoch
    have hQpos : ∀ x y, 0 < Bridge.toMatrix P x y := hpos
    have hspec : Bridge.toSpec γ hγ
        = MeasureTheory.GibbsMeasure.Markov.markovSpecification (Bridge.toMatrix P) :=
      Bridge.toSpec_eq_markovSpecification γ P hpos hγ hsingle
    refine ⟨MeasureTheory.GibbsMeasure.Markov.stationaryChain (Bridge.toMatrix P) hQ hQpos,
      MeasureTheory.GibbsMeasure.Markov.stationaryDist (Bridge.toMatrix P) hQ hQpos,
      fun y => MeasureTheory.GibbsMeasure.Markov.stationaryDist_pos _ hQ hQpos y,
      (MeasureTheory.GibbsMeasure.Markov.stationaryDist_mem_stdSimplex _ hQ hQpos).2,
      fun y => congrFun (MeasureTheory.GibbsMeasure.Markov.vecMul_stationaryDist
        (Bridge.toMatrix P) hQ hQpos) y,
      fun a n x => ?_, fun ν => ?_⟩
    · have hab : a ≤ a + (n : ℤ) := by omega
      have hcyl : cylinder a (a + (n : ℤ)) x
          = {τ : ℤ → E | ∀ k ∈ Finset.Icc a (a + (n : ℤ)), τ k = x k} := rfl
      rw [hcyl, MeasureTheory.GibbsMeasure.Markov.markovChain_cylinder
        (Bridge.toMatrix P) hQ hQpos hab x]
      congr 1
      congr 1
      simp only [Bridge.toMatrix_apply]
      exact Bridge.prod_Ico_eq_prod_range a n (fun k => P (x k) (x (k + 1)))
    · rw [Bridge.isGibbs_iff γ hγ ν, hspec,
        MeasureTheory.GibbsMeasure.Markov.gibbsMeasure_eq_singleton (Bridge.toMatrix P) hQ hQpos,
        Set.mem_singleton_iff]

/-- **Georgii, Theorem (3.5), the uniqueness half.** A specification on `ℤ` whose singleton kernels
come from a strictly positive stochastic matrix `P` via (3.11) has exactly one Gibbs measure. -/
theorem georgii_3_5_uniqueness (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1)
    (γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E))
    (hγ : IsSpecification γ)
    (hsingle : ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
      γ {i} ω {σ : Config ℤ E | σ i = y}
        = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1)))) :
    ∃! μ : MeasureTheory.Measure (Config ℤ E), IsGibbs γ μ :=
  by
    obtain ⟨μ, α, -, -, -, -, huniq⟩ := georgii_3_5_markovChain P hpos hstoch γ hγ hsingle
    exact ⟨μ, (huniq μ).2 rfl, fun ν hν => (huniq ν).1 hν⟩

/-- **Non-vacuity of Theorem (3.5)**: for every strictly positive stochastic matrix `P` on a
finite state space there really is a specification on `ℤ` whose singleton kernels are given by the
determining function (3.11). -/
theorem exists_isSpecification_determiningFun (P : E → E → ℝ) (hpos : ∀ x y, 0 < P x y)
    (hstoch : ∀ x, ∑ y, P x y = 1) :
    ∃ γ : Finset ℤ → Config ℤ E → MeasureTheory.Measure (Config ℤ E), IsSpecification γ ∧
      ∀ (i : ℤ) (y : E) (ω : Config ℤ E),
        γ {i} ω {σ : Config ℤ E | σ i = y}
          = ENNReal.ofReal (determiningFun P (ω (i - 1)) y (ω (i + 1))) :=
  ⟨fun Λ ω ↦ MeasureTheory.GibbsMeasure.Markov.markovSpecification (Bridge.toMatrix P) Λ ω,
    Bridge.ofSpec _, fun i y ω ↦ by
      rw [MeasureTheory.GibbsMeasure.Markov.markovSpecification_singleton_apply
        (P := Bridge.toMatrix P) hpos i y ω, Bridge.determiningFun_eq P]⟩

end MarkovChainChallenge

end

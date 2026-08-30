import Comparator.Defs_NoGibbs
import GibbsMeasure

/-!
# Comparator solution: Georgii Example (4.16) — a specification with no Gibbs measure

The solution file matching `Comparator/Challenge_NoGibbs.lean`.  The `Bridge` namespace identifies
the kernels `gamma` of `Comparator.Defs_NoGibbs` with `MeasureTheory.GibbsMeasure.Example416.kernel`
and transports the library results across.

## References

* [Georgii, *Gibbs Measures and Phase Transitions*][georgii2011], Example (4.16)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace GibbsChallenge

namespace SingleParticle

variable {S : Type*} [Countable S] [DecidableEq S]

/-! ### Bridge to the `GibbsMeasure` library -/

namespace Bridge

open ProbabilityTheory MeasureTheory.GibbsMeasure

omit [Countable S] [DecidableEq S] in
/-- The challenge's external σ-algebra `𝓣_Λ` is the library's `cylinderEvents Λᶜ`. -/
theorem outside_eq_cylinderEvents (Λ : Finset S) :
    outside (E := Bool) Λ = cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ) := rfl

omit [Countable S] in
theorem spike_eq (a : S) : spike a = Example416.spike a := rfl

omit [Countable S] [DecidableEq S] in
theorem vanishOff_eq (Λ : Finset S) : vanishOff Λ = Example416.vanishOff Λ := rfl

omit [Countable S] in
theorem spikeMeasure_eq (Λ : Finset S) : spikeMeasure Λ = Example416.spikeMeasure Λ := rfl

/-- `gamma Λ ω` is the `Λ`-kernel of `Example416.specification` at the boundary condition `ω`. -/
theorem gamma_eq (Λ : Finset S) (ω : Config S Bool) :
    gamma Λ ω = Example416.kernel Λ ω := by
  have hz : ∀ ω : Config S Bool, zeroOn (∅ : Finset S) ω = ω := by
    intro ω
    funext i
    simp [zeroOn]
  unfold gamma
  split_ifs with h
  · rw [Example416.kernel_apply_of_mem (Finset.nonempty_iff_ne_empty.1 h.1) h.2, spikeMeasure_eq]
  · rw [not_and_or] at h
    by_cases hΛ : Λ = ∅
    · subst hΛ
      rw [hz ω, Example416.kernel_empty_apply]
    · have hω : ω ∉ vanishOff Λ := by
        rcases h with h | h
        · exact absurd (Finset.nonempty_iff_ne_empty.2 hΛ) h
        · exact h
      rw [Example416.kernel_apply_of_not_mem hΛ hω]
      rfl

theorem gamma_eq_specification (Λ : Finset S) (ω : Config S Bool) :
    gamma Λ ω = Example416.specification (S := S) Λ ω := gamma_eq Λ ω

theorem aemeasurable_specification (Λ : Finset S) (μ : Measure (Config S Bool)) :
    AEMeasurable (fun ω : Config S Bool ↦ Example416.specification (S := S) Λ ω) μ :=
  (((Example416.specification (S := S) Λ).measurable).mono cylinderEvents_le_pi le_rfl).aemeasurable

theorem bind_eq_iff (μ : Measure (Config S Bool)) (Λ : Finset S) :
    μ.bind (Example416.specification (S := S) Λ) = μ ↔
      ∀ A : Set (Config S Bool), MeasurableSet A → μ A = ∫⁻ ω, gamma Λ ω A ∂μ := by
  constructor
  · intro h A hA
    have := congrArg (fun m : Measure (Config S Bool) ↦ m A) h
    rw [Measure.bind_apply hA (aemeasurable_specification Λ μ)] at this
    simp only [← gamma_eq_specification] at this
    exact this.symm
  · intro h
    refine Measure.ext fun A hA ↦ ?_
    rw [Measure.bind_apply hA (aemeasurable_specification Λ μ)]
    simp only [← gamma_eq_specification]
    exact (h A hA).symm

/-- **Georgii (4.16) is a specification** — via the library. -/
theorem isSpecification_gamma : IsSpecification (gamma (S := S)) := by
  refine ⟨fun Λ ω ↦ ?_, fun Λ A hA ↦ ?_, fun Λ A B hA hB ω ↦ ?_, fun Λ Δ hΛΔ ω A hA ↦ ?_⟩
  · rw [gamma_eq]
    infer_instance
  · have h : (fun ω : Config S Bool ↦ gamma Λ ω A) = fun ω ↦ Example416.kernel (S := S) Λ ω A :=
      funext fun ω ↦ by rw [gamma_eq]
    rw [h]
    exact (Example416.kernel (S := S) Λ).measurable_coe hA
  · have hB' : MeasurableSet[cylinderEvents (X := fun _ : S ↦ Bool) ((Λ : Set S)ᶜ)] B := hB
    have h := (Kernel.isProper_iff_inter_eq_indicator_mul
      (cylinderEvents_le_pi (X := fun _ : S ↦ Bool))).1 (Example416.isProper_kernel Λ) hA hB' ω
    rw [gamma_eq, h]
    by_cases hωB : ω ∈ B <;> simp [hωB]
  · have hb := Specification.bind (γ := Example416.specification (S := S)) hΛΔ ω
    have h := (bind_eq_iff (Example416.specification (S := S) Δ ω) Λ).1 hb A hA
    rw [gamma_eq_specification Δ ω]
    exact h.symm

/-- **Georgii (4.16) has no Gibbs measure** — via `Example416.GP_eq_empty`. -/
theorem not_isGibbs_gamma [Infinite S] (μ : Measure (Config S Bool)) :
    ¬ IsGibbs (gamma (S := S)) μ := by
  rintro ⟨hprob, hdlr⟩
  have hmem : (⟨μ, hprob⟩ : ProbabilityMeasure (S → Bool)) ∈
      GP (S := S) (E := Bool) (Example416.specification (S := S)) := by
    show Specification.IsGibbsMeasure (Example416.specification (S := S)) μ
    rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob]
    exact fun Λ ↦ (bind_eq_iff μ Λ).2 fun A hA ↦ hdlr Λ A hA
  rw [Example416.GP_eq_empty] at hmem
  exact hmem

/-- Georgii's computation `γ_{a}(σ_a = 1 | η) = 1_{η = 0 off {a}}` — via
`Example416.action_spinAt_apply`. -/
theorem toReal_gamma_singleton (a : S) (η : Config S Bool) :
    (gamma ({a} : Finset S) η {σ : Config S Bool | σ a = true}).toReal
      = (vanishOff ({a} : Finset S)).indicator 1 η := by
  have h := Example416.action_spinAt_apply a η
  rw [Specification.action_apply, Example416.coeFn_spinAt,
    integral_indicator_one (Example416.measurableSet_setOf_apply_eq_true a)] at h
  rw [gamma_eq_specification, ← measureReal_def]
  exact h

/-- **On a finite site set the same kernels do have a Gibbs measure** — via
`Example416.mem_GP_of_finite`. -/
theorem isGibbs_spikeMeasure_univ {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] :
    IsGibbs (gamma (S := S)) (spikeMeasure (Finset.univ : Finset S)) := by
  have : Fact (Finset.univ : Finset S).Nonempty := ⟨Finset.univ_nonempty⟩
  have hprob : IsProbabilityMeasure (spikeMeasure (Finset.univ : Finset S)) := by
    rw [spikeMeasure_eq]
    infer_instance
  refine ⟨hprob, fun Λ A hA ↦ ?_⟩
  have hG : Specification.IsGibbsMeasure (Example416.specification (S := S))
      (spikeMeasure (Finset.univ : Finset S)) := Example416.mem_GP_of_finite (S := S)
  rw [Specification.isGibbsMeasure_iff_forall_bind_eq_of_prob] at hG
  exact (bind_eq_iff (spikeMeasure (Finset.univ : Finset S)) Λ).1 (hG Λ) A hA

end Bridge

/-! ### The statements -/

/-- **Georgii (4.16) is a specification**: proper, consistent, and each `γ_Λ(A|·)` is a
`𝓣_Λ`-measurable probability kernel. -/
theorem isSpecification_gamma : IsSpecification (gamma (S := S)) := by
  exact Bridge.isSpecification_gamma

/-- **Georgii (4.16) has no Gibbs measure**: `𝓖(γ) = ∅` on a countably infinite site set. -/
theorem not_isGibbs_gamma [Infinite S] (μ : Measure (Config S Bool)) :
    ¬ IsGibbs (gamma (S := S)) μ := by
  exact Bridge.not_isGibbs_gamma μ

/-- The explicit witness of non-quasilocality: `ω ↦ γ_{a}(σ_a = 1 | ω)` is the indicator of
`{ω = 0 off {a}}`, whose oscillation off every finite volume is at least `1`. -/
theorem one_le_oscOutside_gamma [Infinite S] (a : S) (Δ : Finset S) :
    1 ≤ oscOutside Δ fun ω => (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal := by
  obtain ⟨b, hb⟩ := Infinite.exists_notMem_finset (insert a Δ)
  have hba : b ≠ a := fun h ↦ hb (h ▸ Finset.mem_insert_self a Δ)
  have hbΔ : b ∉ Δ := fun h ↦ hb (Finset.mem_insert_of_mem h)
  have hfun : (fun ω : Config S Bool =>
      (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal)
      = (vanishOff ({a} : Finset S)).indicator 1 := funext (Bridge.toReal_gamma_singleton a)
  rw [hfun]
  have hagree : ∀ i ∈ Δ, (fun _ ↦ false : Config S Bool) i = spike b i := by
    intro i hi
    have hib : i ≠ b := fun h ↦ hbΔ (h ▸ hi)
    simp [spike, hib]
  have hmem : (fun _ ↦ false : Config S Bool) ∈ vanishOff ({a} : Finset S) := fun _ _ ↦ rfl
  have hnot : spike b ∉ vanishOff ({a} : Finset S) := by
    intro h
    have hb' : b ∉ ({a} : Finset S) := by simpa using hba
    have hbb := h b hb'
    simp [spike] at hbb
  refine le_trans ?_ (le_oscOutside
    (f := (vanishOff ({a} : Finset S)).indicator (1 : Config S Bool → ℝ)) hagree)
  rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot]
  simp

/-- **Georgii, Example (4.16)** is not quasilocal; with `isSpecification_gamma` and
`not_isGibbs_gamma` this shows quasilocality cannot be dropped from the existence theorems (4.17)
and (4.22). -/
theorem not_isQuasilocal_gamma [Infinite S] : ¬ IsQuasilocal (gamma (S := S)) := by
  intro hql
  obtain ⟨a⟩ := (inferInstance : Nonempty S)
  have hA : MeasurableSet {σ : Config S Bool | σ a = true} := by
    show MeasurableSet ((fun σ : Config S Bool ↦ σ a) ⁻¹' {true})
    exact measurable_pi_apply a (measurableSet_singleton _)
  have hloc : IsLocalFun
      (({σ : Config S Bool | σ a = true}).indicator (1 : Config S Bool → ℝ)) := by
    refine ⟨{a}, fun ω ω' h ↦ ?_⟩
    have ha : ω a = ω' a := h a (Finset.mem_singleton_self a)
    simp [Set.indicator_apply, ha]
  have hbdd : ∀ ω : Config S Bool,
      |({σ : Config S Bool | σ a = true}).indicator (1 : Config S Bool → ℝ) ω| ≤ 1 := by
    intro ω
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have h : IsQuasilocalFun (fun ω : Config S Bool =>
      ∫ σ, ({σ : Config S Bool | σ a = true}).indicator (1 : Config S Bool → ℝ) σ
        ∂(gamma ({a} : Finset S) ω)) :=
    hql {a} (({σ : Config S Bool | σ a = true}).indicator (1 : Config S Bool → ℝ))
      (measurable_one.indicator hA) hloc hbdd
  have hrw : (fun ω : Config S Bool =>
      ∫ σ, ({σ : Config S Bool | σ a = true}).indicator (1 : Config S Bool → ℝ) σ
        ∂(gamma ({a} : Finset S) ω))
      = fun ω : Config S Bool =>
        (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal := by
    funext ω
    rw [integral_indicator_one hA, measureReal_def]
  rw [hrw] at h
  have h' : Filter.Tendsto (fun Δ : Finset S => oscOutside Δ fun ω : Config S Bool =>
      (gamma ({a} : Finset S) ω {σ : Config S Bool | σ a = true}).toReal)
      Filter.atTop (nhds 0) := h
  obtain ⟨Δ, hΔ⟩ := ((ENNReal.tendsto_nhds_zero.1 h') 2⁻¹ (by simp)).exists
  exact absurd (ENNReal.one_le_inv.1 ((one_le_oscOutside_gamma a Δ).trans hΔ)) (by norm_num)

/-- Infinitude of `S` is essential: on a finite site set the same formulas do have a Gibbs
measure, the uniform distribution on the one-particle configurations. -/
theorem isGibbs_spikeMeasure_of_finite {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S] :
    IsGibbs (gamma (S := S)) (spikeMeasure (Finset.univ : Finset S)) := by
  exact Bridge.isGibbs_spikeMeasure_univ

end SingleParticle

end GibbsChallenge

end

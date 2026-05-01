module

public import GibbsMeasure.Prereqs.Kernel.CondExpClass
public import GibbsMeasure.Prereqs.Kernel.CondExpBind
public import Mathlib.Probability.Kernel.Proper
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

public section

open MeasureTheory ENNReal NNReal Set Filter

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {μ : Measure[𝓧] X}
  {A B : Set X} {f g : X → ℝ≥0∞} {x₀ : X}

lemma isCondExp_iff_bind_eq_left [IsFiniteMeasure μ] [IsMarkovKernel π]
    (hπ : π.IsProper) (h𝓑𝓧 : 𝓑 ≤ 𝓧) [SigmaFinite (μ.trim h𝓑𝓧)] :
    IsCondExp π μ ↔ μ.bind π = μ := by
  have h_iff_A (A : Set X) (hA : MeasurableSet[𝓧] A) :
      (μ[A.indicator 1|𝓑] =ᵐ[μ] fun a ↦ (π a A).toReal) ↔
        (∀ t, MeasurableSet[𝓑] t → μ (A ∩ t) = ∫⁻ a in t, π a A ∂μ) := by
    have hgm : AEStronglyMeasurable[𝓑] (fun a ↦ π a A) μ :=
      (Kernel.measurable_coe π hA).aestronglyMeasurable
    have hg_fin : ∀ᵐ a ∂ μ, π a A ≠ ⊤ := by
      filter_upwards with a
      exact measure_ne_top (π a) A
    simpa [Filter.eventuallyEq_comm] using
      (toReal_ae_eq_indicator_condExp_iff_forall_meas_inter_eq
        (m := 𝓑) (m0 := 𝓧) (μ := μ)
        h𝓑𝓧 hA (measure_ne_top μ A) hgm hg_fin)
  rw [isCondExp_iff, Measure.ext_iff]
  constructor
  · intro h A hA
    rw [Measure.bind_apply hA (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable]
    rw [← setLIntegral_univ]
    have hforall := (h_iff_A A hA).mp (h hA)
    have h_univ := hforall Set.univ MeasurableSet.univ
    simpa using h_univ.symm
  · intro h A hA
    refine (h_iff_A A hA).mpr ?_
    intro t ht
    have hAt_meas : MeasurableSet[𝓧] (A ∩ t) := hA.inter (h𝓑𝓧 _ ht)
    have hμ_bind : μ (A ∩ t) = (μ.bind π) (A ∩ t) := by
      simpa [eq_comm] using h (A ∩ t) hAt_meas
    have h_bind_apply :
        (μ.bind π) (A ∩ t)
          = ∫⁻ a, π a (A ∩ t) ∂ μ :=
      Measure.bind_apply hAt_meas (π.measurable.mono h𝓑𝓧 le_rfl).aemeasurable
    have h_prop := hπ.inter_eq_indicator_mul h𝓑𝓧 hA ht
    have h_integrand :
        (fun a => t.indicator 1 a * π a A)
          = t.indicator (fun a => π a A) := by
      ext a; by_cases ha : a ∈ t <;> simp [ha]
    have hmeas : Measurable[𝓧] (fun a => π a A) :=
      (Kernel.measurable_coe π hA).mono h𝓑𝓧 le_rfl
    calc
      μ (A ∩ t)
          = (μ.bind π) (A ∩ t) := by simpa using hμ_bind
      _ = ∫⁻ a, π a (A ∩ t) ∂ μ := h_bind_apply
      _ = ∫⁻ a, t.indicator 1 a * π a A ∂ μ := by
            simp_rw [h_prop]
      _ = ∫⁻ a, t.indicator (fun a => π a A) a ∂ μ := by
            simp_rw [h_integrand]
      _ = ∫⁻ a in t, π a A ∂ μ := by rw [lintegral_indicator (h𝓑𝓧 t ht) fun a ↦ (π a) A]

lemma condExp_ae_eq_kernel_apply
    (h : ∀ (f : X → ℝ), Bornology.IsBounded (Set.range f) → Measurable[𝓧] f →
      condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)))
    {A : Set X} (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ))) =ᵐ[μ] (fun x ↦ (π x A).toReal) := by
  have ind_bdd : Bornology.IsBounded (Set.range (A.indicator (fun _ ↦ (1 : ℝ)))) := by
    apply (Metric.isBounded_Icc (0 : ℝ) 1).subset
    rw [range_subset_iff]
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have ind_mble : Measurable[𝓧] (A.indicator (fun _ ↦ (1 : ℝ))) := by
    exact (measurable_indicator_const_iff 1).mpr A_mble
  specialize h _ ind_bdd ind_mble
  apply h.trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [π.IsCondExp μ]

private lemma condExp_indicator_ae_eq_integral_kernel (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (1 : ℝ)) x ∂(π x₀)) := by
  apply (IsCondExp.condExp_ae_eq_kernel_apply (π := π) A_mble).trans
  simp_rw [← Pi.one_def, @integral_indicator_one X 𝓧 _ _ A_mble]
  rfl

variable [IsFiniteMeasure μ] [IsFiniteKernel π]

private lemma condExp_const_indicator_ae_eq_integral_kernel (c : ℝ) (A_mble : MeasurableSet[𝓧] A) :
    condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ)))
      =ᵐ[μ] (fun x₀ ↦ ∫ x, A.indicator (fun _ ↦ (c : ℝ)) x ∂(π x₀)) := by
  have smul_eq : A.indicator (fun _ ↦ (c : ℝ)) = c • A.indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [hx, smul_eq_mul]
  have foo : c • condExp 𝓑 μ (A.indicator (fun _ ↦ (1 : ℝ)))
     =ᵐ[μ] condExp 𝓑 μ (A.indicator (fun _ ↦ (c : ℝ))) := by
    rw [smul_eq]; exact (condExp_smul (μ := μ) c (A.indicator (fun _ ↦ (1 : ℝ))) 𝓑).symm
  apply foo.symm.trans
  have h_smul_integral :
      c • (fun x₀ ↦ ∫ (a : X), A.indicator (fun _ ↦ (1 : ℝ)) a ∂π x₀)
        = (fun x₀ ↦ ∫ (a : X), A.indicator (fun _ ↦ (c : ℝ)) a ∂π x₀) := by
    funext x₀
    have h1 :
        ∫ (a : X), A.indicator (fun _ : X ↦ (1 : ℝ)) a ∂(π x₀) = (π x₀).real A := by
      simpa [Set.inter_univ] using
        (MeasureTheory.setIntegral_indicator_one (μ := π x₀) (s := A)
          (hs := by simpa using A_mble) (t := Set.univ))
    have h2 :
        ∫ (a : X), A.indicator (fun _ : X ↦ (c : ℝ)) a ∂(π x₀) = (π x₀).real A • c := by
      simpa [Set.inter_univ] using
        (MeasureTheory.setIntegral_indicator_const (μ := π x₀) (E := ℝ)
          (s := A) (t := Set.univ) (c := c) (hs := by simpa using A_mble))
    simp [h1, h2, smul_eq_mul, mul_comm]
  rw [← h_smul_integral]
  have h_ind1 := condExp_indicator_ae_eq_integral_kernel (μ := μ) (π := π) A_mble
  exact Filter.EventuallyEq.const_smul h_ind1 c

/-- Simple functions satisfy the kernel integral representation; see
`ProbabilityTheory.Kernel.condExp_ae_eq_integral_kernel` in `CondExpBind.lean` for the general
Fubini-bind statement under `IsMarkovKernel` and integrability hypotheses. -/
private lemma condExp_simpleFunc_ae_eq_integral_kernel (f : @SimpleFunc X 𝓧 ℝ) :
    condExp 𝓑 μ f =ᵐ[μ] (fun x₀ ↦ ∫ x, f x ∂(π x₀)) := by
  classical
  letI : MeasurableSpace X := 𝓧
  refine @SimpleFunc.induction _ _ _ _ (fun f => condExp 𝓑 μ f =ᵐ[μ]
    (fun x₀ => ∫ x, f x ∂(π x₀))) ?_ ?_ f
  · intro c s hs
    simp [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    simpa using
      (condExp_const_indicator_ae_eq_integral_kernel (μ := μ) (π := π) (A := s) c hs)
  · intro f g _disj hf hg
    have hf_int : Integrable f μ := SimpleFunc.integrable_of_isFiniteMeasure f
    have hg_int : Integrable g μ := SimpleFunc.integrable_of_isFiniteMeasure g
    have h_add_condExp := condExp_add hf_int hg_int 𝓑
    filter_upwards [h_add_condExp, hf, hg] with x₀ h_add hf_eq hg_eq
    rw [SimpleFunc.coe_add, h_add, Pi.add_apply, hf_eq, hg_eq, ← integral_add, ← SimpleFunc.coe_add]
    · exact rfl
    · exact SimpleFunc.integrable_of_isFiniteMeasure f
    exact SimpleFunc.integrable_of_isFiniteMeasure g

end ProbabilityTheory.Kernel

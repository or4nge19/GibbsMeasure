module

public import GibbsMeasure.Mathlib.Data.ENNReal.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
public import GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import GibbsMeasure.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.Integral.Bochner.Basic
public import GibbsMeasure.Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Kernel.Proper

/-!
# Proper kernels

We define the notion of properness for measure kernels and highlight important consequences.
-/

public section

open MeasureTheory ENNReal NNReal Set
open scoped ProbabilityTheory

namespace ProbabilityTheory.Kernel
variable {X : Type*} {𝓑 𝓧 : MeasurableSpace X} {π : Kernel[𝓑, 𝓧] X X} {A B : Set X}
  {f g : X → ℝ} {x₀ : X}

private lemma IsProper.integral_indicator_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (hB : MeasurableSet[𝓑] B) :
    ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀) =
      B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  calc
        ∫ x, (B.indicator 1 x * A.indicator 1 x : ℝ) ∂(π x₀)
    _ = (∫⁻ x, .ofReal (B.indicator 1 x * A.indicator 1 x) ∂π x₀).toReal :=
      integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg, mul_nonneg])
        (by measurability)
    _ = (∫⁻ x, B.indicator 1 x * A.indicator 1 x ∂π x₀).toReal := by simp [indicator_nonneg]
    _ = (B.indicator 1 x₀ * ∫⁻ x, A.indicator 1 x ∂π x₀).toReal := by
      rw [hπ.lintegral_mul h𝓑𝓧 (by measurability) (by measurability)]
    _ = B.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
      rw [integral_eq_lintegral_of_nonneg_ae (.of_forall <| by simp [indicator_nonneg])
        (by measurability)]
      simp

variable [IsFiniteKernel π]

open SimpleFunc in
private lemma IsProper.integral_simpleFunc_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (g : X →ₛ[𝓑] ℝ) :
    ∫ x, g x * A.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  have hmul_to_indicator :
      (fun x ↦ g x * A.indicator 1 x) = (fun x ↦ A.indicator g x) := by
    ext x; by_cases hxA : x ∈ A <;> simp [hxA]
  rw [hmul_to_indicator]
  refine @SimpleFunc.induction X ℝ 𝓑 inferInstance
      (fun g ↦ ∫ x, A.indicator g x ∂π x₀ = g x₀ * ∫ x, A.indicator 1 x ∂π x₀)
      (fun c S hS ↦ ?_)
      (fun f g disj hf hg ↦ ?_) g
  · calc
      ∫ x, A.indicator (S.indicator (fun _ ↦ c)) x ∂π x₀
        = c * ∫ x, S.indicator 1 x * A.indicator 1 x ∂π x₀ := by
        rw [← integral_const_mul]
        congr! with _ x
        by_cases hxA : x ∈ A <;> by_cases hxS : x ∈ S <;> simp [hxA, hxS]
      _ = c * (S.indicator 1 x₀ * ∫ x, A.indicator 1 x ∂π x₀) := by
        simp [hπ.integral_indicator_mul_indicator h𝓑𝓧 hA hS]
      _ = S.indicator (fun _ ↦ c) x₀ * ∫ x, A.indicator 1 x ∂π x₀ := by
        by_cases hxS : x₀ ∈ S <;> simp [hxS]
  · simp only [SimpleFunc.coe_add, indicator_add', Pi.add_apply, add_mul, ← hf, ← hg]
    apply MeasureTheory.integral_add <;> exact .indicator (integrable_of_isFiniteMeasure' h𝓑𝓧 _) hA

private lemma IsProper.integral_bdd_mul_indicator (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hA : MeasurableSet[𝓧] A) (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (x₀ : X) :
    ∫ x, g x * A.indicator 1 x ∂(π x₀) = g x₀ * ∫ x, A.indicator 1 x ∂(π x₀) := by
  obtain ⟨C, hC⟩ := hgbdd
  refine tendsto_nhds_unique ?_ <| (hg.tendsto_approxBounded_of_norm_le <| hC _).mul_const _
  simp_rw [← hπ.integral_simpleFunc_mul_indicator h𝓑𝓧 hA]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ C) (fun n ↦ ?_) (integrable_const _)
    (fun n ↦ .of_forall fun x ↦ ?_) <| .of_forall fun x ↦ ?_
  · exact (((hg.approxBounded C n).stronglyMeasurable.mono h𝓑𝓧).mul
      (by fun_prop (disch := assumption))).aestronglyMeasurable
  · simpa [-norm_mul] using
      norm_mul_le_of_le (hg.norm_approxBounded_le ((norm_nonneg _).trans <| hC x₀) _ _)
        (norm_indicator_le_norm_self 1 _)
  · exact .mul_const _ <| hg.tendsto_approxBounded_of_norm_le <| hC _

omit [IsFiniteKernel π] in
private lemma l1_mul_sub_ae {m : MeasurableSpace X} {μ : Measure[m] X} (g : X → ℝ)
    (a b : X →₁[μ] ℝ) :
    (fun x ↦ g x * a x - g x * b x) =ᵐ[μ] fun x ↦ g x * (a - b) x := by
  filter_upwards [Lp.coeFn_sub a b] with x hx
  have hmul : g x * (a - b) x = g x * (a x - b x) := by
    simpa [hx] using congrArg (fun t ↦ g x * t) hx
  calc
    g x * a x - g x * b x = g x * (a x - b x) := by simp [mul_sub]
    _ = g x * (a - b) x := by simp [hmul.symm]

omit [IsFiniteKernel π] in
private lemma integrable_l1_bdd_mul {C : ℝ} (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hg : StronglyMeasurable[𝓑] g)
    (hC : ∀ x, ‖g x‖ ≤ C) (a : X →₁[π x₀] ℝ) :
    Integrable (fun x ↦ g x * a x) (π x₀) :=
  (L1.integrable_coeFn a).bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable <| .of_forall hC

omit [IsFiniteKernel π] in
private lemma norm_integral_l1_bdd_mul_le {C : ℝ} (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hg : StronglyMeasurable[𝓑] g)
    (hC : ∀ x, ‖g x‖ ≤ C) (a : X →₁[π x₀] ℝ) :
    ‖∫ x, g x * a x ∂π x₀‖ ≤ C * ‖a‖ := by
  have hInt : Integrable (fun x ↦ g x * a x) (π x₀) := integrable_l1_bdd_mul h𝓑𝓧 hg hC a
  have hdInt : Integrable (fun x ↦ C * ‖a x‖) (π x₀) := (L1.integrable_coeFn a).norm.smul C
  have hle_ae : (fun x ↦ ‖g x * a x‖) ≤ᵐ[π x₀] fun x ↦ C * ‖a x‖ :=
    .of_forall fun x ↦ by simpa using mul_le_mul_of_nonneg_right (hC x) (norm_nonneg (a x))
  calc
    ‖∫ x, g x * a x ∂π x₀‖ ≤ ∫ x, ‖g x * a x‖ ∂π x₀ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, C * ‖a x‖ ∂π x₀ := integral_mono_ae hInt.norm hdInt hle_ae
    _ = C * ∫ x, ‖a x‖ ∂π x₀ := by simp [integral_const_mul]
    _ = C * ‖a‖ := by rw [(L1.norm_eq_integral_norm a (μ := π x₀)).symm]

omit [IsFiniteKernel π] in
private lemma norm_integral_l1_bdd_mul_sub_le {C : ℝ} (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hg : StronglyMeasurable[𝓑] g) (hC : ∀ x, ‖g x‖ ≤ C) (a b : X →₁[π x₀] ℝ) :
    ‖∫ x, g x * a x ∂π x₀ - ∫ x, g x * b x ∂π x₀‖ ≤ C * ‖a - b‖ := by
  have hInt1 : Integrable (fun x ↦ g x * a x) (π x₀) := integrable_l1_bdd_mul h𝓑𝓧 hg hC a
  have hInt2 : Integrable (fun x ↦ g x * b x) (π x₀) := integrable_l1_bdd_mul h𝓑𝓧 hg hC b
  have hsub :
      ‖∫ x, g x * a x ∂π x₀ - ∫ x, g x * b x ∂π x₀‖ =
        ‖∫ x, g x * a x - g x * b x ∂π x₀‖ := by
    simp [integral_sub hInt1 hInt2]
  have hdiff : ‖∫ x, g x * a x - g x * b x ∂π x₀‖ =
      ‖∫ x, g x * (a - b) x ∂π x₀‖ := by
    rw [integral_congr_ae (l1_mul_sub_ae g a b)]
  rw [hsub, hdiff]
  exact norm_integral_l1_bdd_mul_le h𝓑𝓧 hg hC (a - b)

omit [IsFiniteKernel π] in
private lemma continuous_integral_l1_bdd_mul {C : ℝ} (h𝓑𝓧 : 𝓑 ≤ 𝓧)
    (hg : StronglyMeasurable[𝓑] g) (hpC : 0 < C) (hC : ∀ x, ‖g x‖ ≤ C) :
    Continuous fun a : X →₁[π x₀] ℝ ↦ ∫ x, g x * a x ∂π x₀ := by
  refine Metric.continuous_iff.mpr fun b ε hε ↦ ⟨ε / C, div_pos hε hpC, fun a ha ↦ ?_⟩
  have hle := norm_integral_l1_bdd_mul_sub_le h𝓑𝓧 hg hC a b
  have hlt : C * ‖a - b‖ < ε := by
    have hdist : ‖a - b‖ < ε / C := by simpa [dist_eq_norm] using ha
    simpa [mul_div, mul_div_cancel_left₀ ε (ne_of_gt hpC)] using
      mul_lt_mul_of_pos_left hdist hpC
  exact lt_of_le_of_lt hle hlt

lemma IsProper.integral_bdd_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π) (hf : Integrable[𝓧] f (π x₀))
    (hg : StronglyMeasurable[𝓑] g) (hgbdd : ∃ C > 0, ∀ x, ‖g x‖ ≤ C) :
    ∫ x, g x * f x ∂(π x₀) = g x₀ * ∫ x, f x ∂(π x₀) := by
  obtain ⟨C, hpC, hC⟩ := hgbdd
  refine (Integrable.induction (μ := π x₀) (E := ℝ)
      (P := fun k => ∫ x, g x * k x ∂(π x₀) = g x₀ * ∫ x, k x ∂(π x₀)) ?_ ?_ ?_ ?_) hf
  · intro c s hs hμs
    simp [← smul_indicator_one_apply, mul_left_comm, integral_const_mul,
      hπ.integral_bdd_mul_indicator h𝓑𝓧 hs hg ⟨C, hC⟩]
  · intro f₁ f₂ hdisj hf₁ hf₂ hgf₁ hgf₂
    have : Integrable (fun x ↦ g x * f₁ x) (π x₀) :=
      hf₁.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable <| .of_forall hC
    have : Integrable (fun x ↦ g x * f₂ x) (π x₀) :=
      hf₂.bdd_mul (hg.mono h𝓑𝓧).aestronglyMeasurable <| .of_forall hC
    simp [mul_add, integral_add, *]
  · exact isClosed_eq (continuous_integral_l1_bdd_mul h𝓑𝓧 hg hpC hC)
      (continuous_const.mul continuous_integral)
  · intro f₁ f₂ hfg hf₁ hPf₁
    have hmul : (fun x ↦ g x * f₁ x) =ᵐ[π x₀] (fun x ↦ g x * f₂ x) := by
      filter_upwards [hfg] with x hx; simp [hx]
    simpa [integral_congr_ae hmul, integral_congr_ae hfg.symm] using hPf₁

lemma IsProper.integral_indicator_mul (h𝓑𝓧 : 𝓑 ≤ 𝓧) (hπ : IsProper π)
    (hf : Integrable[𝓧] f (π x₀)) (hB : MeasurableSet[𝓑] B) :
    ∫ x, B.indicator 1 x * f x ∂(π x₀) =
      B.indicator 1 x₀ * ∫ x, f x ∂(π x₀) := by
  exact hπ.integral_bdd_mul h𝓑𝓧 hf (stronglyMeasurable_one.indicator hB)
    ⟨1, zero_lt_one, fun x ↦ by
      simpa using
        norm_indicator_le_norm_self (s := B) (f := fun _ : X ↦ (1 : ℝ)) (a := x)⟩

end ProbabilityTheory.Kernel

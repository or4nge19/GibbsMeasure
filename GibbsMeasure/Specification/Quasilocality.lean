/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Normed.Lp.lpSpace
public import GibbsMeasure.Specification
public import GibbsMeasure.Specification.QuasilocalAlgebra
public import GibbsMeasure.Specification.Rescaling
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Quasilocal specifications

Georgii's Definition (2.23): a specification is quasilocal if each `γ Λ` maps quasilocal observables
to quasilocal observables. No topology on `E` is involved.

## Main declarations

* `Specification.action`: `γ_Λ f = ∫ f ∂γ_Λ(·|·)` on bounded observables.
* `Specification.IsQuasilocal`: Georgii (2.23).
* `Specification.isQuasilocal_iff_forall_mem_localFunctions`: it suffices to check local
observables.
* `Specification.IsResampling.isQuasilocal_modification_relNorm_of_isQuasilocalFun`,
  `Specification.isQuasilocal_lambdaSpecification`: Georgii (2.24)(b) at Georgii's hypotheses —
  measurable quasilocal Hamiltonians, not assumed bounded, over a resampling reference
  specification resp. a σ-finite a priori measure.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E]

lemma mem_quasilocalFunctions_iff_mem_closure {f : lp (fun _ : S → E ↦ ℝ) ∞} :
    f ∈ quasilocalFunctions S E
      ↔ f ∈ closure (localFunctions S E : Set (lp (fun _ : S → E ↦ ℝ) ∞)) :=
  Iff.rfl

/-- **The estimate in Georgii's proof of Proposition (2.24)(b).** If two nonnegative densities
`p, q` on a measure space are multiplicatively within a factor `K ≥ 1` of each other, then the
`p`- and `q`-weighted normalized expectations of an observable bounded by `M` differ by at most
`2(K − 1)M`. Georgii's application has `p = e^{-H_Λ}`, `q = e^{-u}` for a local `u` with
`‖H_Λ − u‖ ≤ ε`, so `K = e^ε` and the bound is `2(e^ε − 1)M`. -/
theorem abs_integral_mul_div_sub_integral_mul_div_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p q f : X → ℝ} {K M : ℝ}
    (hq : AEStronglyMeasurable q μ) (hf : AEStronglyMeasurable f μ)
    (hK : 1 ≤ K) (hM : 0 ≤ M)
    (hfM : ∀ x, |f x| ≤ M) (hp0 : ∀ x, 0 ≤ p x)
    (hqK : ∀ x, q x ≤ K * p x) (hpK : ∀ x, p x ≤ K * q x)
    (hpint : Integrable p μ) (hppos : 0 < ∫ x, p x ∂μ) :
    |(∫ x, f x * p x ∂μ) / ∫ x, p x ∂μ - (∫ x, f x * q x ∂μ) / ∫ x, q x ∂μ|
      ≤ 2 * (K - 1) * M := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have hq0 : ∀ x, 0 ≤ q x := fun x ↦ by nlinarith [hp0 x, hpK x]
  have hqint : Integrable q μ :=
    (hpint.const_mul K).mono' hq
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]; exact hqK x)
  set a := ∫ x, p x ∂μ with ha
  set b := ∫ x, q x ∂μ with hb
  have hab : a ≤ K * b := by
    calc a ≤ ∫ x, K * q x ∂μ := integral_mono hpint (hqint.const_mul K) hpK
      _ = K * b := integral_const_mul K q
  have hbpos : 0 < b := by nlinarith
  have hfp : Integrable (fun x ↦ f x * p x) μ :=
    (hpint.const_mul M).mono' (hf.mul hpint.aestronglyMeasurable)
      (.of_forall fun x ↦ by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
        exact mul_le_mul_of_nonneg_right (hfM x) (hp0 x))
  have hfq : Integrable (fun x ↦ f x * q x) μ :=
    (hqint.const_mul M).mono' (hf.mul hq)
      (.of_forall fun x ↦ by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq0 x)]
        exact mul_le_mul_of_nonneg_right (hfM x) (hq0 x))
  -- the pointwise multiplicative closeness gives `|p − q| ≤ (K − 1) p`
  have hpq : ∀ x, |p x - q x| ≤ (K - 1) * p x := by
    intro x
    rw [abs_le]
    refine ⟨by nlinarith [hqK x], ?_⟩
    have h1 : K * (p x - q x) ≤ K * ((K - 1) * p x) := by
      nlinarith [hpK x, mul_nonneg (hp0 x) (sq_nonneg (K - 1))]
    exact le_of_mul_le_mul_left h1 hK0
  -- hence the normalizers are `(K − 1) a`-close
  have hba : |b - a| ≤ (K - 1) * a := by
    have h1 : |b - a| ≤ ∫ x, |q x - p x| ∂μ := by
      rw [hb, ha, ← integral_sub hqint hpint]
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := μ) (f := fun x ↦ q x - p x)
    refine h1.trans ?_
    calc ∫ x, |q x - p x| ∂μ
        ≤ ∫ x, (K - 1) * p x ∂μ :=
          integral_mono (hqint.sub hpint).abs (hpint.const_mul _)
            fun x ↦ (abs_sub_comm (q x) (p x)) ▸ hpq x
      _ = (K - 1) * a := integral_const_mul _ p
  set c := |1 / a - 1 / b| with hc
  -- the pointwise estimate on the normalized densities
  have hpoint : ∀ x, |f x * p x / a - f x * q x / b|
      ≤ M * ((K - 1) / a) * p x + (M * c) * q x := by
    intro x
    have hsplit : f x * p x / a - f x * q x / b
        = f x * ((p x - q x) / a + q x * (1 / a - 1 / b)) := by
      field_simp
      ring
    rw [hsplit, abs_mul]
    have h2 : |(p x - q x) / a + q x * (1 / a - 1 / b)|
        ≤ (K - 1) * p x / a + q x * c := by
      refine le_trans (abs_add_le _ _) ?_
      gcongr
      · rw [abs_div, abs_of_pos hppos]
        exact div_le_div_of_nonneg_right (hpq x) hppos.le
      · rw [abs_mul, abs_of_nonneg (hq0 x)]
    calc |f x| * |(p x - q x) / a + q x * (1 / a - 1 / b)|
        ≤ M * ((K - 1) * p x / a + q x * c) :=
          mul_le_mul (hfM x) h2 (abs_nonneg _) hM
      _ = M * ((K - 1) / a) * p x + (M * c) * q x := by ring
  -- assemble
  have hcb : c * b ≤ K - 1 := by
    have hcval : c * b = |b - a| / a := by
      rw [hc, div_sub_div _ _ (ne_of_gt hppos) (ne_of_gt hbpos), abs_div,
        abs_of_pos (mul_pos hppos hbpos), one_mul, mul_one, div_mul_eq_mul_div,
        mul_comm a b, mul_comm |b - a| b, mul_div_mul_left _ _ (ne_of_gt hbpos)]
    rw [hcval, div_le_iff₀ hppos]
    exact hba
  have hstep : (∫ x, f x * p x ∂μ) / a - (∫ x, f x * q x ∂μ) / b
      = ∫ x, (f x * p x / a - f x * q x / b) ∂μ := by
    rw [integral_sub (hfp.div_const a) (hfq.div_const b), integral_div, integral_div]
  calc |(∫ x, f x * p x ∂μ) / a - (∫ x, f x * q x ∂μ) / b|
      = |∫ x, (f x * p x / a - f x * q x / b) ∂μ| := by rw [hstep]
    _ ≤ ∫ x, |f x * p x / a - f x * q x / b| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := μ) (f := fun x ↦ f x * p x / a - f x * q x / b)
    _ ≤ ∫ x, (M * ((K - 1) / a) * p x + (M * c) * q x) ∂μ := by
        refine integral_mono ((hfp.div_const a).sub (hfq.div_const b)).abs
          (((hpint.const_mul _)).add ((hqint.const_mul _))) hpoint
    _ = M * ((K - 1) / a) * a + (M * c) * b := by
        rw [integral_add (hpint.const_mul _) (hqint.const_mul _),
          integral_const_mul, integral_const_mul]
    _ = M * (K - 1) + M * (c * b) := by
        field_simp
    _ ≤ M * (K - 1) + M * (K - 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcb hM)
    _ = 2 * (K - 1) * M := by ring

/-- A local observable's pointwise inverse is local: inversion preserves
`cylinderEvents`-measurability. Boundedness of the inverse is the caller's obligation — it is the
construction of the element `g` of `lp ∞` — and typically comes from a positive lower bound on
`r`. -/
theorem inv_mem_localFunctionsOn {Δ : Finset S} {r g : lp (fun _ : S → E ↦ ℝ) ∞}
    (hr : r ∈ localFunctionsOn S E Δ) (hg : ∀ η, (⇑g) η = ((⇑r) η)⁻¹) :
    g ∈ localFunctionsOn S E Δ := by
  rw [mem_localFunctionsOn, show ⇑g = fun η ↦ ((⇑r) η)⁻¹ from funext hg]
  exact (mem_localFunctionsOn.1 hr).inv

/-- A measurable function that is quasilocal in the sense of Georgii's (2.22) is uniformly
approximable by *measurable local* functions: the local approximant is `f` composed with the
patching of a fixed configuration outside a large volume. This is the unbounded counterpart of
`MeasureTheory.GibbsMeasure.mem_quasilocalFunctions_iff_isQuasilocalFun`. -/
theorem IsQuasilocalFun.exists_measurable_dependsOn {f : (S → E) → ℝ} (hmeas : Measurable f)
    (hf : IsQuasilocalFun f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (Δ : Finset S) (u : (S → E) → ℝ), Measurable u ∧ DependsOn u (Δ : Set S) ∧
      ∀ η, |f η - u η| ≤ ε := by
  classical
  obtain ⟨Δ, hΔ⟩ := hf ε hε
  by_cases hne : Nonempty (S → E)
  · obtain ⟨η₀⟩ := hne
    set T : (S → E) → S → E := fun ω i ↦ if i ∈ Δ then ω i else η₀ i with hT
    have hTmeas : Measurable T := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      by_cases hi : i ∈ Δ
      · simpa [hT, hi] using measurable_pi_apply (X := fun _ : S ↦ E) i
      · simp only [hT, hi, ite_false]
        exact measurable_const
    have hTdep : DependsOn T (Δ : Set S) := by
      intro ω ω' h
      funext i
      by_cases hi : i ∈ Δ
      · simp [hT, hi, h i (by exact_mod_cast hi)]
      · simp [hT, hi]
    refine ⟨Δ, f ∘ T, hmeas.comp hTmeas, DependsOn.comp f hTdep, fun η ↦ ?_⟩
    exact hΔ η (T η) fun i hi ↦ by simp [hT, hi]
  · exact ⟨∅, f, hmeas, by intro ω ω' _; exact (hne ⟨ω⟩).elim, fun η ↦ (hne ⟨η⟩).elim⟩

/-- Scaling preserves quasilocality in the sense of Georgii's (2.22). -/
theorem IsQuasilocalFun.const_mul {f : (S → E) → ℝ} (hf : IsQuasilocalFun f) (c : ℝ) :
    IsQuasilocalFun fun η ↦ c * f η := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨∅, fun ζ η _ ↦ by simpa using hε.le⟩
  · have hcpos : 0 < |c| := abs_pos.2 hc
    obtain ⟨Δ, hΔ⟩ := hf (ε / |c|) (by positivity)
    refine ⟨Δ, fun ζ η h ↦ ?_⟩
    have h1 := hΔ ζ η h
    have h2 : |c * f ζ - c * f η| = |c| * |f ζ - f η| := by
      rw [← abs_mul]
      ring_nf
    rw [h2, ← le_div_iff₀' hcpos]
    exact h1

/-- Integrating a bounded observable against the normalization of a finite positive density
`e^{-H} dμ` computes as a quotient of integrals: `∫ f dμ^H = μ(f e^{-H}) / μ(e^{-H})`. -/
theorem integral_withDensity_ofReal_div_const {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : X → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x) {Z : ℝ≥0∞}
    (hZval : Z = ∫⁻ x, ENNReal.ofReal (p x) ∂μ) (hZ0 : Z ≠ 0) (hZtop : Z ≠ ⊤) (f : X → ℝ) :
    ∫ x, f x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (p x) / Z)
      = (∫ x, f x * p x ∂μ) / ∫ x, p x ∂μ := by
  have htR : 0 < Z.toReal := ENNReal.toReal_pos hZ0 hZtop
  have hmeas : Measurable fun x ↦ (p x / Z.toReal).toNNReal :=
    (hp.div_const _).real_toNNReal
  calc ∫ x, f x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (p x) / Z)
      = ∫ x, f x ∂(μ.withDensity fun x ↦ (((p x / Z.toReal).toNNReal : ℝ≥0) : ℝ≥0∞)) := by
        congr 1
        refine withDensity_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [show (((p x / Z.toReal).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (p x / Z.toReal)
            from rfl,
          ENNReal.ofReal_div_of_pos htR, ENNReal.ofReal_toReal hZtop]
    _ = ∫ x, (p x / Z.toReal).toNNReal • f x ∂μ := integral_withDensity_eq_integral_smul hmeas f
    _ = ∫ x, f x * p x / Z.toReal ∂μ := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (hp0 x) htR.le)]
        ring
    _ = (∫ x, f x * p x ∂μ) / Z.toReal := integral_div _ _
    _ = (∫ x, f x * p x ∂μ) / ∫ x, p x ∂μ := by
        rw [integral_eq_lintegral_of_nonneg_ae (.of_forall hp0) hp.aestronglyMeasurable, ← hZval]

/-- **The core of Georgii's Proposition (2.24)(b).** Let `κ` be a reference kernel that resamples
the volume `Λ` (an arbitrary measure on the inside configurations, juxtaposed with the frozen
exterior), and let `H` be a measurable quasilocal Hamiltonian whose partition functions
`κ_η(e^{-H})` are positive and finite. Then for every bounded local `f`, the normalized expectation
`η ↦ κ_η(f e^{-H}) / κ_η(e^{-H})` is a bounded quasilocal observable.

The proof is Georgii's: approximate `H` uniformly within `ε` by a local `u`; the competitor
`η ↦ κ_η(f e^{-u}) / κ_η(e^{-u})` is local, and the multiplicative bounds
`e^{-ε} ≤ e^{-H}/e^{-u} ≤ e^{ε}` give the uniform estimate `2(e^ε − 1)‖f‖` between the two
normalized expectations. -/
theorem exists_mem_quasilocalFunctions_integral_exp_neg_div {Λ : Finset S}
    {κ : Kernel[cylinderEvents ((Λ : Set S)ᶜ)] (S → E) (S → E)}
    (hκ : ∃ μΛ : Measure (Λ → E), ∀ η, κ η = μΛ.map (juxt (Λ : Set S) η))
    {H : (S → E) → ℝ} (hH : Measurable H) (hql : IsQuasilocalFun H)
    (hZ0 : ∀ η, ∫⁻ x, ENNReal.ofReal (Real.exp (-H x)) ∂(κ η) ≠ 0)
    (hZtop : ∀ η, ∫⁻ x, ENNReal.ofReal (Real.exp (-H x)) ∂(κ η) ≠ ⊤)
    {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctions S E) :
    ∃ r ∈ quasilocalFunctions S E, ∀ η : S → E,
      (⇑r) η = (∫ x, (⇑f) x * Real.exp (-H x) ∂(κ η)) / ∫ x, Real.exp (-H x) ∂(κ η) := by
  classical
  obtain ⟨μΛ, hμΛ⟩ := hκ
  obtain ⟨Δf, hΔf⟩ := mem_localFunctions.1 hf
  have hfmeas : Measurable (⇑f) := (mem_localFunctionsOn.1 hΔf).mono cylinderEvents_le_pi le_rfl
  have hfdep : DependsOn (⇑f) (Δf : Set S) :=
    (mem_localFunctionsOn.1 hΔf).dependsOn_of_cylinderEvents
  have hfM : ∀ x, |(⇑f) x| ≤ ‖f‖ := fun x ↦ by
    simpa [Real.norm_eq_abs] using lp.norm_apply_le_norm ENNReal.top_ne_zero f x
  set pR : (S → E) → ℝ := fun x ↦ Real.exp (-H x) with hpR
  have hpRmeas : Measurable pR := hH.neg.exp
  have hpR0 : ∀ x, 0 ≤ pR x := fun x ↦ (Real.exp_pos _).le
  -- integrating a measurable local observable against the reference is measurable and local
  have hint_meas : ∀ g : (S → E) → ℝ, Measurable g →
      Measurable fun η ↦ ∫ x, g x ∂(κ η) := fun g hg ↦
    ((StronglyMeasurable.integral_kernel (κ := κ) hg.stronglyMeasurable).measurable).mono
      cylinderEvents_le_pi le_rfl
  have hint_dep : ∀ (g : (S → E) → ℝ) (Δ : Finset S), Measurable g →
      DependsOn g (Δ : Set S) → DependsOn (fun η ↦ ∫ x, g x ∂(κ η)) (Δ : Set S) := by
    intro g Δ hg hgdep η η' hηη'
    have hrepr : ∀ ξ : S → E, ∫ x, g x ∂(κ ξ) = ∫ ζ, g (juxt (Λ : Set S) ξ ζ) ∂μΛ := by
      intro ξ
      rw [hμΛ ξ, integral_map Measurable.juxt.aemeasurable hg.aestronglyMeasurable]
      rfl
    dsimp only
    rw [hrepr η, hrepr η']
    refine integral_congr_ae (.of_forall fun ζ ↦ hgdep fun i hi ↦ ?_)
    by_cases hiΛ : i ∈ (Λ : Set S)
    · rw [juxt_apply_of_mem hiΛ, juxt_apply_of_mem hiΛ]
    · rw [juxt_apply_of_not_mem hiΛ, juxt_apply_of_not_mem hiΛ]
      exact hηη' i hi
  -- the per-boundary partition function
  have hpint : ∀ η, Integrable pR (κ η) := fun η ↦
    ⟨hpRmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (.of_forall hpR0)).2 (lt_top_iff_ne_top.2 (hZtop η))⟩
  have haval : ∀ η, ∫ x, pR x ∂(κ η) = (∫⁻ x, ENNReal.ofReal (pR x) ∂(κ η)).toReal := fun η ↦
    integral_eq_lintegral_of_nonneg_ae (.of_forall hpR0) hpRmeas.aestronglyMeasurable
  have hapos : ∀ η, 0 < ∫ x, pR x ∂(κ η) := fun η ↦ by
    rw [haval η]
    exact ENNReal.toReal_pos (hZ0 η) (hZtop η)
  -- the normalized expectation, as a bounded function
  set G : (S → E) → ℝ := fun η ↦ (∫ x, (⇑f) x * pR x ∂(κ η)) / ∫ x, pR x ∂(κ η) with hG
  -- boundedness of normalized expectations against any density `q` comparable to `pR`
  have hbdd : ∀ (q : (S → E) → ℝ), Measurable q → (∀ x, 0 ≤ q x) →
      (∀ η, Integrable q (κ η)) → (∀ η, 0 < ∫ x, q x ∂(κ η)) →
      ∀ η, |(∫ x, (⇑f) x * q x ∂(κ η)) / ∫ x, q x ∂(κ η)| ≤ ‖f‖ := by
    intro q hq hq0 hqint hqpos η
    rw [abs_div, abs_of_pos (hqpos η), div_le_iff₀ (hqpos η)]
    have hfq : Integrable (fun x ↦ (⇑f) x * q x) (κ η) :=
      ((hqint η).const_mul ‖f‖).mono' (hfmeas.aestronglyMeasurable.mul hq.aestronglyMeasurable)
        (.of_forall fun x ↦ by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hq0 x)]
          exact mul_le_mul_of_nonneg_right (hfM x) (hq0 x))
    calc |∫ x, (⇑f) x * q x ∂(κ η)|
        ≤ ∫ x, |(⇑f) x * q x| ∂(κ η) := by
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := κ η) (f := fun x ↦ (⇑f) x * q x)
      _ ≤ ∫ x, ‖f‖ * q x ∂(κ η) := by
          refine integral_mono hfq.abs ((hqint η).const_mul _) fun x ↦ ?_
          rw [abs_mul, abs_of_nonneg (hq0 x)]
          exact mul_le_mul_of_nonneg_right (hfM x) (hq0 x)
      _ = ‖f‖ * ∫ x, q x ∂(κ η) := integral_const_mul _ _
  have hGmem : G ∈ lp (fun _ : S → E ↦ ℝ) ∞ :=
    memℓp_infty ⟨‖f‖, by
      rintro _ ⟨η, rfl⟩
      simpa [Real.norm_eq_abs] using hbdd pR hpRmeas hpR0 hpint hapos η⟩
  refine ⟨⟨G, hGmem⟩, ?_, fun η ↦ rfl⟩
  -- quasilocality: approximate `H` within `ε` by a local `u` and compare
  rw [mem_quasilocalFunctions_iff_mem_closure, Metric.mem_closure_iff]
  intro ε' hε'
  set δ : ℝ := ε' / (2 * (‖f‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  set ε : ℝ := Real.log (1 + δ) with hεdef
  have hεpos : 0 < ε := Real.log_pos (by linarith)
  have hexpε : Real.exp ε = 1 + δ := Real.exp_log (by linarith)
  obtain ⟨Δ, u, humeas, hudep, huapprox⟩ := hql.exists_measurable_dependsOn hH hεpos
  set qR : (S → E) → ℝ := fun x ↦ Real.exp (-u x) with hqR
  have hqRmeas : Measurable qR := humeas.neg.exp
  have hqR0 : ∀ x, 0 ≤ qR x := fun x ↦ (Real.exp_pos _).le
  -- the multiplicative approximation `e^{-ε} ≤ e^{-H}/e^{-u} ≤ e^{ε}`
  have hqp : ∀ x, qR x ≤ Real.exp ε * pR x := fun x ↦ by
    rw [hqR, hpR, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (huapprox x)).2])
  have hpq : ∀ x, pR x ≤ Real.exp ε * qR x := fun x ↦ by
    rw [hqR, hpR, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [(abs_le.1 (huapprox x)).1])
  have hqint : ∀ η, Integrable qR (κ η) := fun η ↦
    ((hpint η).const_mul (Real.exp ε)).mono' hqRmeas.aestronglyMeasurable
      (.of_forall fun x ↦ by rw [Real.norm_eq_abs, abs_of_nonneg (hqR0 x)]; exact hqp x)
  have hqpos : ∀ η, 0 < ∫ x, qR x ∂(κ η) := by
    intro η
    have h1 : ∫ x, pR x ∂(κ η) ≤ Real.exp ε * ∫ x, qR x ∂(κ η) := by
      rw [← integral_const_mul]
      exact integral_mono (hpint η) ((hqint η).const_mul _) hpq
    nlinarith [hapos η, Real.exp_pos ε]
  -- the local competitor
  set Gu : (S → E) → ℝ := fun η ↦ (∫ x, (⇑f) x * qR x ∂(κ η)) / ∫ x, qR x ∂(κ η) with hGu
  have hGumem : Gu ∈ lp (fun _ : S → E ↦ ℝ) ∞ :=
    memℓp_infty ⟨‖f‖, by
      rintro _ ⟨η, rfl⟩
      simpa [Real.norm_eq_abs] using hbdd qR hqRmeas hqR0 hqint hqpos η⟩
  have hGuloc : (⟨Gu, hGumem⟩ : lp (fun _ : S → E ↦ ℝ) ∞) ∈ localFunctions S E := by
    refine mem_localFunctions.2 ⟨Δf ∪ Δ, mem_localFunctionsOn.2 ?_⟩
    have hfq : Measurable fun x ↦ (⇑f) x * qR x := hfmeas.mul hqRmeas
    have hqRdep : DependsOn qR (Δ : Set S) := hudep.comp fun t ↦ Real.exp (-t)
    have hqdep : DependsOn qR ((Δf ∪ Δ : Finset S) : Set S) :=
      hqRdep.mono (by exact_mod_cast Finset.subset_union_right)
    have hfqdep : DependsOn (fun x ↦ (⇑f) x * qR x) ((Δf ∪ Δ : Finset S) : Set S) :=
      DependsOn.mul (hfdep.mono (by exact_mod_cast Finset.subset_union_left)) hqdep
    refine Measurable.cylinderEvents_of_dependsOn ?_ ?_
    · exact (hint_meas _ hfq).div (hint_meas _ hqRmeas)
    · exact (hint_dep _ _ hfq hfqdep).div (hint_dep _ _ hqRmeas hqdep)
  refine ⟨⟨Gu, hGumem⟩, hGuloc, ?_⟩
  -- the uniform `2(e^ε − 1)‖f‖` estimate
  have hdist : ∀ η, |G η - Gu η| ≤ 2 * (Real.exp ε - 1) * ‖f‖ := fun η ↦
    abs_integral_mul_div_sub_integral_mul_div_le hqRmeas.aestronglyMeasurable
      hfmeas.aestronglyMeasurable (Real.one_le_exp hεpos.le) (norm_nonneg f) hfM hpR0
      hqp hpq (hpint η) (hapos η)
  have hlt : 2 * (Real.exp ε - 1) * ‖f‖ < ε' := by
    have hpos1 : (0 : ℝ) < ‖f‖ + 1 := by positivity
    have hε'' : ε' = 2 * δ * (‖f‖ + 1) := by
      rw [hδ]
      field_simp
    rw [hexpε]
    nlinarith [hδpos, norm_nonneg f]
  rw [dist_eq_norm]
  have hc0 : 0 ≤ 2 * (Real.exp ε - 1) * ‖f‖ := by
    have h1 := Real.one_le_exp hεpos.le
    have : 0 ≤ Real.exp ε - 1 := by linarith
    positivity
  refine lt_of_le_of_lt (lp.norm_le_of_forall_le hc0 fun η ↦ ?_) hlt
  rw [lp.coeFn_sub, Pi.sub_apply]
  simpa [Real.norm_eq_abs] using hdist η

end MeasureTheory.GibbsMeasure

namespace Specification

open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E} {Λ : Finset S}
  {f : lp (fun _ : S → E ↦ ℝ) ∞}

/-- `(γ_Λ f)(η) = ∫ f ∂γ_Λ(·|η)`, on bounded observables. -/
def action (γ : Specification S E) (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞) :
    lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ ∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η), by
    refine memℓp_infty ⟨‖f‖, ?_⟩
    rintro _ ⟨η, rfl⟩
    have h : ‖∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η)‖ ≤ ‖f‖ * (γ Λ η).real univ :=
      norm_integral_le_of_norm_le_const
        (.of_forall fun x ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero f x)
    simpa using h⟩

@[simp] lemma action_apply (γ : Specification S E) (Λ : Finset S)
    (f : lp (fun _ : S → E ↦ ℝ) ∞) (η : S → E) :
    (action γ Λ f : (S → E) → ℝ) η = ∫ x, (f : (S → E) → ℝ) x ∂(γ Λ η) := rfl

/-- `γ_Λ f` is measurable for the boundary σ-algebra `cylinderEvents Λᶜ`. -/
lemma action_mem_localFunctionsOn_compl (hf : Measurable (⇑f)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)]
      ((action γ Λ f : (S → E) → ℝ)) :=
  (StronglyMeasurable.integral_kernel (κ := γ Λ) hf.stronglyMeasurable).measurable

lemma measurable_action (hf : Measurable (⇑f)) : Measurable ((action γ Λ f : (S → E) → ℝ)) :=
  (action_mem_localFunctionsOn_compl (γ := γ) (Λ := Λ) hf).mono cylinderEvents_le_pi le_rfl

/-- The action is a contraction on measurable observables. -/
lemma dist_action_le {f g : lp (fun _ : S → E ↦ ℝ) ∞}
    (hf : Measurable (⇑f)) (hg : Measurable (⇑g)) :
    dist (action γ Λ f) (action γ Λ g) ≤ dist f g := by
  rw [dist_eq_norm, dist_eq_norm]
  refine lp.norm_le_of_forall_le (norm_nonneg _) fun η ↦ ?_
  rw [lp.coeFn_sub, Pi.sub_apply, action_apply, action_apply,
    ← integral_sub (lp.integrable_of_measurable hf _) (lp.integrable_of_measurable hg _)]
  have h : ‖∫ x, ((f : (S → E) → ℝ) x - (g : (S → E) → ℝ) x) ∂(γ Λ η)‖
      ≤ ‖f - g‖ * (γ Λ η).real univ := by
    refine norm_integral_le_of_norm_le_const (.of_forall fun x ↦ ?_)
    have := lp.norm_apply_le_norm ENNReal.top_ne_zero (f - g) x
    rwa [lp.coeFn_sub, Pi.sub_apply] at this
  simpa using h


end Specification

namespace Specification
open MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] {γ : Specification S E}

/-- **Georgii, Definition (2.23).** -/
def IsQuasilocal (γ : Specification S E) : Prop :=
  ∀ (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞),
    f ∈ quasilocalFunctions S E → action γ Λ f ∈ quasilocalFunctions S E

/-- Georgii's remark following (2.23): it suffices to check local observables. -/
theorem isQuasilocal_iff_forall_mem_localFunctions :
    γ.IsQuasilocal ↔ ∀ (Λ : Finset S) (f : lp (fun _ : S → E ↦ ℝ) ∞),
      f ∈ localFunctions S E → action γ Λ f ∈ quasilocalFunctions S E := by
  refine ⟨fun h Λ f hf ↦ h Λ f (localFunctions_le_quasilocalFunctions hf), fun h Λ f hf ↦ ?_⟩
  have hclosed : IsClosed (quasilocalFunctions S E : Set (lp (fun _ : S → E ↦ ℝ) ∞)) :=
    Subalgebra.isClosed_topologicalClosure _
  have hfmeas : Measurable (⇑f) := measurable_of_mem_quasilocalFunctions hf
  rw [← SetLike.mem_coe, ← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ :=
    Metric.mem_closure_iff.1 (MeasureTheory.GibbsMeasure.mem_quasilocalFunctions_iff_mem_closure.1 hf) ε hε
  have hgmeas : Measurable (⇑g) :=
    measurable_of_mem_quasilocalFunctions (localFunctions_le_quasilocalFunctions hg)
  exact ⟨action γ Λ g, h Λ g hg, lt_of_le_of_lt (dist_action_le hfmeas hgmeas) hfg⟩

/-! ### The independent specification, and modifications of it -/

section Isssd

variable (ν : Measure E) [IsProbabilityMeasure ν]

/-- Integrating out `Λ` against a resampling kernel sends a `Δ`-local observable to a
`Δ \ Λ`-local one. -/
lemma IsResampling.dependsOn_action [DecidableEq S] {γ : Specification S E} (hγ : IsResampling γ)
    {f : (S → E) → ℝ} (hfm : Measurable f) {Δ : Finset S} (hf : DependsOn f (Δ : Set S))
    (Λ : Finset S) :
    DependsOn (fun η ↦ ∫ x, f x ∂(γ Λ η)) (((Δ \ Λ : Finset S) : Set S)) := by
  intro η η' hηη'
  obtain ⟨μ, hμ⟩ := hγ Λ
  have hint : ∀ ξ : S → E, ∫ x, f x ∂(γ Λ ξ) = ∫ ζ, f (juxt (Λ : Set S) ξ ζ) ∂μ := by
    intro ξ
    rw [hμ ξ, integral_map (Measurable.juxt).aemeasurable hfm.aestronglyMeasurable]
    rfl
  dsimp only
  rw [hint η, hint η']
  refine integral_congr_ae (.of_forall fun ζ ↦ hf fun i hi ↦ ?_)
  by_cases hiΛ : i ∈ Λ
  · simp [juxt_apply_of_mem (Λ := (Λ : Set S)) (by exact_mod_cast hiΛ)]
  · have hmem : i ∈ ((Δ \ Λ : Finset S) : Set S) := by
      simpa using Finset.mem_sdiff.2 ⟨by exact_mod_cast hi, hiΛ⟩
    simp [juxt_apply_of_not_mem (Λ := (Λ : Set S)) (by exact_mod_cast hiΛ), hηη' i hmem]

/-- A resampling specification maps `Δ`-local observables to `Δ \ Λ`-local ones. -/
theorem IsResampling.action_mem_localFunctionsOn [DecidableEq S] {γ : Specification S E}
    (hγ : IsResampling γ) (Λ Δ : Finset S) {f : lp (fun _ : S → E ↦ ℝ) ∞} (hf : f ∈ localFunctionsOn S E Δ) :
    action γ Λ f ∈ localFunctionsOn S E (Δ \ Λ) := by
  have hfm : Measurable (⇑f) := (mem_localFunctionsOn.1 hf).mono cylinderEvents_le_pi le_rfl
  have hdep : DependsOn (⇑f) (Δ : Set S) :=
    (mem_localFunctionsOn.1 hf).dependsOn_of_cylinderEvents
  rw [mem_localFunctionsOn, measurable_cylinderEvents_iff_dependsOn]
  exact ⟨measurable_action (γ := γ) hfm, hγ.dependsOn_action hfm hdep Λ⟩

/-- Georgii, after (2.23): every resampling specification — in particular every independent one,
homogeneous or not — is quasilocal. -/
theorem IsResampling.isQuasilocal {γ : Specification S E} (hγ : IsResampling γ) :
    γ.IsQuasilocal := by
  classical
  refine isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦ ?_
  obtain ⟨Δ, hΔ⟩ := mem_localFunctions.1 hf
  exact localFunctions_le_quasilocalFunctions
    (mem_localFunctions.2 ⟨Δ \ Λ, hγ.action_mem_localFunctionsOn Λ Δ hΔ⟩)

theorem isQuasilocal_isssd : (isssd (S := S) (E := E) ν).IsQuasilocal :=
  (isResampling_isssd ν).isQuasilocal

end Isssd

/-! ### Georgii (2.24)(b) at Georgii's hypotheses -/

/-- A family of everywhere positive, finite weights whose normalization is a modifier is
automatically admissible: the partition functions `relZ` are positive and finite. This is why
Georgii's λ-admissibility need not be assumed separately in (2.24)(b) once `γ^Φ` exists as a
specification. -/
theorem isRelAdmissible_of_isModifier_relNorm {ρ : Finset S → (S → E) → ℝ≥0∞}
    (hmeas : ∀ Λ, Measurable (ρ Λ)) (h0 : ∀ Λ x, ρ Λ x ≠ 0)
    (hρ : γ.IsModifier (relNorm γ ρ)) : IsRelAdmissible γ ρ := by
  intro Λ η
  have hone : ∫⁻ x, relNorm γ ρ Λ x ∂(γ Λ η) = 1 := by
    have h1 := (hρ.isMarkovKernel Λ).isProbabilityMeasure η
    have h2 : (γ Λ η).withDensity (relNorm γ ρ Λ) Set.univ = 1 := h1.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h2
  have hone2 : ∫⁻ x, ρ Λ x / relZ γ ρ Λ η ∂(γ Λ η) = 1 := by
    rw [← hone]
    refine lintegral_congr_ae ?_
    filter_upwards [relZ_ae_eq (γ := γ) hmeas (Finset.Subset.refl Λ) η] with ζ hζ
    rw [relNorm, hζ]
  refine ⟨fun hz ↦ ?_, fun ht ↦ ?_⟩
  · rw [hz, show (fun x : S → E ↦ ρ Λ x / (0 : ℝ≥0∞)) = fun _ ↦ (⊤ : ℝ≥0∞) from
        funext fun x ↦ ENNReal.div_zero (h0 Λ x),
      lintegral_const, measure_univ, mul_one] at hone2
    simp at hone2
  · rw [ht, show (fun x : S → E ↦ ρ Λ x / (⊤ : ℝ≥0∞)) = fun _ ↦ (0 : ℝ≥0∞) from
        funext fun x ↦ ENNReal.div_top, lintegral_const, zero_mul] at hone2
    simp at hone2

/-- **Georgii, Proposition (2.24)(b), at Georgii's hypotheses.** Let `γ` be a resampling reference
specification and `H Λ` a family of *measurable* Hamiltonians — not assumed bounded — that are
quasilocal in the sense of (2.22), and suppose the normalized Boltzmann weights
`e^{-H_Λ}/γ_Λ(e^{-H_Λ})` form a modifier (which encodes Georgii's λ-admissibility, by
`Specification.isRelAdmissible_of_isModifier_relNorm`). Then the Gibbsian specification they
define is quasilocal.

The bounded-Hamiltonian special case is
`Specification.IsResampling.isQuasilocal_modification_relNorm`. -/
theorem IsResampling.isQuasilocal_modification_relNorm_of_isQuasilocalFun (hγ : IsResampling γ)
    {H : Finset S → (S → E) → ℝ} (hH : ∀ Λ, Measurable (H Λ))
    (hql : ∀ Λ, IsQuasilocalFun (H Λ))
    (hρ : γ.IsModifier (relNorm γ fun Λ η ↦ ENNReal.ofReal (Real.exp (-H Λ η)))) :
    (γ.modification _ hρ).IsQuasilocal := by
  classical
  have hhmeas : ∀ Λ, Measurable fun η ↦ ENNReal.ofReal (Real.exp (-H Λ η)) := fun Λ ↦
    ((hH Λ).neg.exp).ennreal_ofReal
  have hadm : IsRelAdmissible γ fun Λ η ↦ ENNReal.ofReal (Real.exp (-H Λ η)) :=
    isRelAdmissible_of_isModifier_relNorm hhmeas (fun Λ x ↦ by simp [Real.exp_pos]) hρ
  rw [isQuasilocal_iff_forall_mem_localFunctions]
  intro Λ f hf
  obtain ⟨r, hrmem, hr⟩ := exists_mem_quasilocalFunctions_integral_exp_neg_div
    (κ := γ Λ) (hγ Λ) (hH Λ) (hql Λ) (fun η ↦ (hadm Λ η).1) (fun η ↦ (hadm Λ η).2) hf
  have hkey : action (γ.modification _ hρ) Λ f = r := by
    refine lp.ext (funext fun η ↦ ?_)
    rw [action_apply, hr η]
    have hae : (relNorm γ (fun Λ η ↦ ENNReal.ofReal (Real.exp (-H Λ η))) Λ)
        =ᵐ[γ Λ η] fun x ↦ ENNReal.ofReal (Real.exp (-H Λ x))
          / relZ γ (fun Λ η ↦ ENNReal.ofReal (Real.exp (-H Λ η))) Λ η := by
      filter_upwards [relZ_ae_eq (γ := γ) hhmeas (Finset.Subset.refl Λ) η] with ζ hζ
      rw [relNorm, hζ]
    rw [modification_apply, withDensity_congr_ae hae]
    exact integral_withDensity_ofReal_div_const ((hH Λ).neg.exp)
      (fun x ↦ (Real.exp_pos _).le) rfl ((hadm Λ η).1) ((hadm Λ η).2) ⇑f
  rw [hkey]
  exact hrmem

/-- **Georgii, Proposition (2.24)(b) for a σ-finite a priori measure.** The λ-specification of a
premodifier of Boltzmann form `ρ_Λ = e^{-H_Λ}` with quasilocal Hamiltonians is quasilocal. The
measurability of the Hamiltonians is automatic: `H_Λ = -log (ρ_Λ.toReal)`. -/
theorem isQuasilocal_lambdaSpecification {ν : Measure E} [SigmaFinite ν] [NeZero ν]
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : IsPremodifier ρ)
    (hZ : IsSigmaFiniteLambdaAdmissible ν ρ)
    {H : Finset S → (S → E) → ℝ} (hρH : ∀ Λ η, ρ Λ η = ENNReal.ofReal (Real.exp (-H Λ η)))
    (hql : ∀ Λ, IsQuasilocalFun (H Λ)) :
    (lambdaSpecification ν ρ hρ hZ).IsQuasilocal := by
  classical
  have hH : ∀ Λ, Measurable (H Λ) := by
    intro Λ
    have hval : H Λ = fun η ↦ -Real.log ((ρ Λ η).toReal) := by
      funext η
      rw [hρH Λ η, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, neg_neg]
    rw [hval]
    exact ((hρ.measurable Λ).ennreal_toReal.log).neg
  rw [isQuasilocal_iff_forall_mem_localFunctions]
  intro Λ f hf
  have hZmeas : Measurable (sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ) := by
    have h : sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ
        = fun a ↦ ∫⁻ b, ρ Λ b ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ a) := rfl
    rw [h]
    exact (Measurable.lintegral_kernel (κ := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
      (hρ.measurable Λ)).mono cylinderEvents_le_pi le_rfl
  -- the partition function in Boltzmann form
  have hZrepr : ∀ η, sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η
      = ∫⁻ x, ENNReal.ofReal (Real.exp (-H Λ x))
          ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η) := fun η ↦
    lintegral_congr fun x ↦ hρH Λ x
  obtain ⟨r, hrmem, hr⟩ := exists_mem_quasilocalFunctions_integral_exp_neg_div
    (κ := sigmaFiniteLambdaFun (S := S) (E := E) ν Λ)
    ⟨Measure.pi fun _ : Λ ↦ ν, fun η ↦ sigmaFiniteLambdaFun_apply_eq_map ν Λ η⟩
    (hH Λ) (hql Λ)
    (fun η ↦ (hZrepr η) ▸ (hZ Λ η).1) (fun η ↦ (hZrepr η) ▸ (hZ Λ η).2) hf
  have hkey : action (lambdaSpecification ν ρ hρ hZ) Λ f = r := by
    refine lp.ext (funext fun η ↦ ?_)
    rw [action_apply, hr η, lambdaSpecification_apply]
    -- the boundary normalization is a.e. constant under the reference kernel
    have hae : sigmaFinitePremodifierNorm (S := S) (E := E) ν ρ Λ
        =ᵐ[sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η]
          fun x ↦ ENNReal.ofReal (Real.exp (-H Λ x))
            / sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η := by
      have haeZ : ∀ᵐ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ η),
          sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ x
            = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η := by
        rw [sigmaFiniteLambdaFun_apply_eq_map]
        exact (ae_map_iff (p := fun x ↦ sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ x
              = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ η)
            Measurable.juxt.aemeasurable (hZmeas (measurableSet_singleton _))).2
          (.of_forall fun ζ ↦ sigmaFiniteLambdaZ_congr_of_eqOn_compl ν (hρ.measurable Λ)
            (juxt_agree_on_compl Λ η ζ))
      filter_upwards [haeZ] with x hx
      rw [sigmaFinitePremodifierNorm, hx, hρH Λ x]
    rw [withDensity_congr_ae hae]
    exact integral_withDensity_ofReal_div_const ((hH Λ).neg.exp)
      (fun x ↦ (Real.exp_pos _).le) (hZrepr η) ((hZ Λ η).1) ((hZ Λ η).2) ⇑f
  rw [hkey]
  exact hrmem

/-! ### Georgii (2.24) -/

/-- A modification of a quasilocal specification by *bounded* quasilocal densities is quasilocal.

This is a variant of **Georgii (2.24)(a)**, which assumes `γ = ρλ` for an a priori measure `λ` and
concludes from either `ρ_Λ` local (any `λ`) or `λ` finite and `ρ_Λ` quasilocal — in neither branch
is `ρ_Λ` assumed bounded. Here the reference `γ` is an arbitrary quasilocal specification, but the
densities are required to lie in `𝓛̄`. -/
theorem IsQuasilocal.modification {γ : Specification S E} (hγ : γ.IsQuasilocal)
    {ρ : Finset S → (S → E) → ℝ≥0∞} (hρ : γ.IsModifier ρ)
    {r : Finset S → lp (fun _ : S → E ↦ ℝ) ∞}
    (hr : ∀ Λ, r Λ ∈ quasilocalFunctions S E)
    (hrρ : ∀ Λ η, (⇑(r Λ)) η = (ρ Λ η).toReal)
    (hfin : ∀ Λ η, ρ Λ η ≠ ∞) :
    (γ.modification ρ hρ).IsQuasilocal := by
  refine isQuasilocal_iff_forall_mem_localFunctions.2 fun Λ f hf ↦ ?_
  have key : action (γ.modification ρ hρ) Λ f = action γ Λ (r Λ * f) := by
    refine lp.ext (funext fun η ↦ ?_)
    have hmeas : Measurable fun x ↦ ((⇑(r Λ)) x).toNNReal :=
      (measurable_of_mem_quasilocalFunctions (hr Λ)).real_toNNReal
    have hden : ρ Λ = fun x ↦ ((((⇑(r Λ)) x).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      funext x
      rw [hrρ Λ x, ← ENNReal.ofReal, ENNReal.ofReal_toReal (hfin Λ x)]
    change ∫ x, (⇑f) x ∂((γ Λ η).withDensity (ρ Λ)) = _
    rw [hden, integral_withDensity_eq_integral_smul hmeas, action_apply]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change ((⇑(r Λ)) x).toNNReal • (⇑f) x = _
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by rw [hrρ Λ x]; exact ENNReal.toReal_nonneg),
      lp.infty_coeFn_mul]
    rfl
  rw [key]
  exact hγ Λ (r Λ * f) (Subalgebra.mul_mem _ (hr Λ) (localFunctions_le_quasilocalFunctions hf))

section Boltzmann

/-- The Boltzmann factor of a bounded observable. -/
noncomputable def boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) : lp (fun _ : S → E ↦ ℝ) ∞ :=
  ⟨fun η ↦ Real.exp (-(⇑H) η), memℓp_infty ⟨Real.exp ‖H‖, by
    rintro _ ⟨η, rfl⟩
    change ‖Real.exp (-(⇑H) η)‖ ≤ Real.exp ‖H‖
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (le_trans (neg_le_abs _) (lp.norm_apply_le_norm ENNReal.top_ne_zero H η))⟩⟩

@[simp] lemma coeFn_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) :
    ⇑(boltzmann H) = fun η ↦ Real.exp (-(⇑H) η) := rfl

lemma boltzmann_mem_quasilocalFunctions {H : lp (fun _ : S → E ↦ ℝ) ∞}
    (hH : H ∈ quasilocalFunctions S E) : boltzmann H ∈ quasilocalFunctions S E :=
  Subalgebra.comp_mem_lp (Subalgebra.isClosed_topologicalClosure _) hH
    (a := -‖H‖) (b := ‖H‖)
    (fun x ↦ abs_le.1 (le_trans (le_abs_self _) (by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero H x)))
    (F := fun t ↦ Real.exp (-t)) (Real.continuous_exp.comp continuous_neg).continuousOn
    (fun _ ↦ rfl)

lemma le_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞) (η : S → E) :
    Real.exp (-‖H‖) ≤ (⇑(boltzmann H)) η :=
  Real.exp_le_exp.2 (neg_le_neg (le_trans (le_abs_self _) (lp.norm_apply_le_norm ENNReal.top_ne_zero H η)))

variable {γ : Specification S E}

lemma integrable_boltzmann {H : lp (fun _ : S → E ↦ ℝ) ∞} (hH : H ∈ quasilocalFunctions S E)
    (Λ : Finset S) (η : S → E) : Integrable (⇑(boltzmann H)) (γ Λ η) :=
  Integrable.mono' (integrable_const ‖boltzmann H‖)
    (measurable_of_mem_quasilocalFunctions
      (boltzmann_mem_quasilocalFunctions hH)).aestronglyMeasurable
    (.of_forall fun x ↦ by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero (boltzmann H) x)

lemma le_action_boltzmann (H : lp (fun _ : S → E ↦ ℝ) ∞)
    (hH : H ∈ quasilocalFunctions S E) (Λ : Finset S) (η : S → E) :
    Real.exp (-‖H‖) ≤ (⇑(action γ Λ (boltzmann H))) η := by
  rw [action_apply]
  calc Real.exp (-‖H‖)
      = ∫ _ : S → E, Real.exp (-‖H‖) ∂(γ Λ η) := by
        rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    _ ≤ _ := integral_mono (integrable_const _) (integrable_boltzmann hH Λ η)
        fun x ↦ le_boltzmann H x

/-- **Georgii (2.24)(b), bounded-Hamiltonian case.** If every Hamiltonian is a *bounded* quasilocal
observable, the Gibbsian specification obtained by normalizing `e^{-H_Λ}` against a resampling
reference specification is quasilocal.

This is the special case of
`Specification.IsResampling.isQuasilocal_modification_relNorm_of_isQuasilocalFun` — Georgii's
(2.24)(b) proper, which needs neither boundedness of the Hamiltonians nor membership in `𝓛̄`,
only measurability and the oscillation condition (2.22). -/
theorem IsResampling.isQuasilocal_modification_relNorm (hγ : IsResampling γ)
    {H : Finset S → lp (fun _ : S → E ↦ ℝ) ∞} (hH : ∀ Λ, H Λ ∈ quasilocalFunctions S E)
    (hρ : γ.IsModifier (relNorm γ fun Λ η ↦ ENNReal.ofReal ((⇑(boltzmann (H Λ))) η))) :
    (γ.modification _ hρ).IsQuasilocal :=
  hγ.isQuasilocal_modification_relNorm_of_isQuasilocalFun (H := fun Λ ↦ ⇑(H Λ))
    (fun Λ ↦ measurable_of_mem_quasilocalFunctions (hH Λ))
    (fun Λ ↦ (mem_quasilocalFunctions_iff_isQuasilocalFun.1 (hH Λ)).2) hρ

variable (ν : Measure E) [IsProbabilityMeasure ν]

theorem isQuasilocal_modification_premodifierNorm
    {H : Finset S → lp (fun _ : S → E ↦ ℝ) ∞} (hH : ∀ Λ, H Λ ∈ quasilocalFunctions S E)
    (hρ : (isssd ν).IsModifier
      (premodifierNorm ν fun Λ η ↦ ENNReal.ofReal ((⇑(boltzmann (H Λ))) η))) :
    ((isssd ν).modification _ hρ).IsQuasilocal :=
  (isResampling_isssd ν).isQuasilocal_modification_relNorm hH hρ

end Boltzmann



end Specification

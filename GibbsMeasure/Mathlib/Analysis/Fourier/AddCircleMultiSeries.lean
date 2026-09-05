/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fourier series on the torus with summable coefficients

`Mathlib/Analysis/Fourier/AddCircleMulti.lean` defines the monomials `mFourier n` on the torus
`UnitAddTorus d = d → ℝ/ℤ`, the Fourier coefficients `mFourierCoeff f n` of a function on the
torus, and proves Parseval and the uniform convergence of the Fourier series of a continuous
function with summable coefficients. This file goes the other way: starting from an absolutely
summable family `c : (d → ℤ) → ℂ`, the trigonometric series `∑' n, c n * mFourier n` is a
continuous function on the torus whose Fourier coefficients are `c`, and multiplying an integrable
`g` by it convolves the coefficients (`mFourierCoeff_tsum_mul_mFourier_mul`).

We also record the elementary algebra of `mFourierCoeff`: coefficients of constants, of a
monomial times a function, of an a.e.-equal function, of the conjugate.

`UnitAddTorus.exists_norm_sub_sum_mul_mFourier_le` restates Mathlib's
`span_mFourier_closure_eq_top` in coordinates: every continuous function on the torus is, up to
a uniform error `ε`, a finite trigonometric polynomial `∑_{j ∈ I} c j * mFourier j`.

Finally we compute the quadratic form of the **Toeplitz matrix** `(i, j) ↦ mFourierCoeff g (i-j)`
of a real integrable `g` as a Fourier integral, `∑_{i,j} ū_i u_j ĝ(i-j) = ∫ |∑_j u_j z^j|² g`
(`UnitAddTorus.sum_sum_conj_mul_mFourierCoeff_sub` for complex `u`, and
`UnitAddTorus.sum_sum_mul_re_mFourierCoeff_sub` for real `u`), and deduce that the matrix is
nonnegative definite when `g ≥ 0`
(`UnitAddTorus.sum_sum_mul_re_mFourierCoeff_sub_nonneg`) and positive definite when moreover
`g ≠ 0` a.e. (`UnitAddTorus.eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero`) or when `g` is
continuous, nonnegative and not identically zero
(`UnitAddTorus.eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero_of_continuous`). The latter
rests on `UnitAddTorus.sum_mul_mFourier_eq_zero_of_eqOn_zero`: a trigonometric polynomial that
vanishes on a non-empty open subset of the torus vanishes identically, because read on `ℝ^d` it is
a real-analytic function on a connected space.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate ENNReal

open Set MeasureTheory


/-! ### Integrability of a reciprocal from `∫⁻ (ofReal f)⁻¹ < ∞`

These two lemmas are about an arbitrary measure space; they record the meaning of the
condition `∫ f⁻¹ dμ < ∞` read with the convention `1/0 = ∞`, as `∫⁻ (ENNReal.ofReal f)⁻¹ ≠ ∞`. -/

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

/-- If `∫⁻ (ofReal f)⁻¹ < ∞` then `f > 0` almost everywhere. -/
theorem ae_pos_of_lintegral_inv_ofReal_ne_top (hf : AEMeasurable f μ)
    (h : ∫⁻ x, (ENNReal.ofReal (f x))⁻¹ ∂μ ≠ ∞) : ∀ᵐ x ∂μ, 0 < f x := by
  have h0 := measure_eq_top_of_lintegral_ne_top
    (measurable_inv.comp_aemeasurable hf.ennreal_ofReal) h
  rw [← compl_mem_ae_iff] at h0
  filter_upwards [h0] with x hx
  simpa [ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero] using hx

/-- If `∫⁻ (ofReal f)⁻¹ < ∞` then `f⁻¹` is integrable. -/
theorem integrable_inv_of_lintegral_inv_ofReal_ne_top (hf : AEMeasurable f μ)
    (h : ∫⁻ x, (ENNReal.ofReal (f x))⁻¹ ∂μ ≠ ∞) : Integrable (fun x ↦ (f x)⁻¹) μ := by
  refine ⟨hf.inv.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top]
  refine ne_top_of_le_ne_top h (le_of_eq (lintegral_congr_ae ?_))
  filter_upwards [ae_pos_of_lintegral_inv_ofReal_ne_top hf h] with x hx
  rw [Real.enorm_of_nonneg (inv_nonneg.2 hx.le), ENNReal.ofReal_inv_of_pos hx]

end MeasureTheory

/-- In this file we normalise the measure on `ℝ / ℤ` to have total volume 1. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The measure on `ℝ / ℤ` is a Haar measure. -/
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-! ### Pointwise facts about the monomials -/

section Monomials

variable {n m : d → ℤ} {x : UnitAddTorus d}

@[simp] lemma norm_mFourier_apply (n : d → ℤ) (x : UnitAddTorus d) : ‖mFourier n x‖ = 1 := by
  simp [mFourier, fourier_apply, norm_prod, Circle.norm_coe]

lemma mFourier_sub : mFourier (m - n) x = mFourier m x * conj (mFourier n x) := by
  rw [sub_eq_add_neg, mFourier_add, mFourier_neg]

lemma mFourier_apply_neg : mFourier n (-x) = mFourier (-n) x := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, neg_smul, smul_neg]

lemma mFourier_mul_mFourier_neg : mFourier n x * mFourier (-n) x = 1 := by
  rw [← mFourier_add, add_neg_cancel, mFourier_zero, ContinuousMap.one_apply]

/-- The Haar integral of a monomial: `∫ mFourier n = δ_{n,0}`. -/
lemma integral_mFourier (n : d → ℤ) :
    ∫ x, mFourier n x = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.1 (orthonormal_mFourier (d := d))) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  rw [h]
  simp only [eq_comm]

/-- The Haar integral of the real part of a monomial: `∫ Re(z^n) dz = δ_{n,0}`. -/
lemma integral_re_mFourier (n : d → ℤ) :
    ∫ x : UnitAddTorus d, (mFourier n x).re = if n = 0 then 1 else 0 := by
  have hint : Integrable fun x : UnitAddTorus d ↦ mFourier n x :=
    (mFourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_mFourier]
  split_ifs <;> simp

end Monomials

/-! ### Algebra of Fourier coefficients -/

section Coeff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma mFourierCoeff_congr_ae {f g : UnitAddTorus d → E} (h : f =ᵐ[volume] g) :
    mFourierCoeff f = mFourierCoeff g := by
  funext n
  unfold mFourierCoeff
  exact integral_congr_ae (h.mono fun x hx ↦ by simp only [hx])

lemma mFourierCoeff_const [CompleteSpace E] (a : E) (n : d → ℤ) :
    mFourierCoeff (fun _ : UnitAddTorus d ↦ a) n = if n = 0 then a else 0 := by
  unfold mFourierCoeff
  rw [integral_smul_const, integral_mFourier]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, neg_eq_zero]

lemma mFourierCoeff_mFourier_smul (n m : d → ℤ) (g : UnitAddTorus d → E) :
    mFourierCoeff (fun x ↦ mFourier n x • g x) m = mFourierCoeff g (m - n) := by
  unfold mFourierCoeff
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [smul_smul, neg_sub, ← mFourier_add]
  congr 3
  abel

lemma mFourierCoeff_mFourier_mul (n m : d → ℤ) (g : UnitAddTorus d → ℂ) :
    mFourierCoeff (fun x ↦ mFourier n x * g x) m = mFourierCoeff g (m - n) :=
  mFourierCoeff_mFourier_smul n m g

lemma mFourierCoeff_mFourier (n m : d → ℤ) :
    mFourierCoeff (mFourier n) m = if m = n then 1 else 0 := by
  have := mFourierCoeff_mFourier_mul n m (fun _ ↦ (1 : ℂ))
  simp only [mul_one] at this
  rw [show (⇑(mFourier n) : UnitAddTorus d → ℂ) = fun x ↦ mFourier n x from rfl, this,
    mFourierCoeff_const]
  simp only [sub_eq_zero]

/-- The Fourier coefficients of a trigonometric polynomial `∑ j ∈ I, c j * mFourier j` are its
coefficients. -/
lemma mFourierCoeff_sum_mul_mFourier (I : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ j ∈ I, c j * mFourier j x) m = if m ∈ I then c m else 0 := by
  unfold mFourierCoeff
  simp_rw [Finset.smul_sum, smul_eq_mul, mul_left_comm (mFourier (-m) _)]
  have hint : ∀ j ∈ I, Integrable fun t ↦ c j * (mFourier (-m) t * mFourier j t) := fun j _ ↦
    (((mFourier (-m)).continuous.mul (mFourier j).continuous).const_mul (c j))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ hint]
  simp_rw [integral_const_mul, ← mFourier_add, integral_mFourier, neg_add_eq_zero]
  simp

/-- The Fourier coefficients of a difference of continuous functions. -/
lemma mFourierCoeff_sub_of_continuous {f g : UnitAddTorus d → E} (hf : Continuous f)
    (hg : Continuous g) (n : d → ℤ) :
    mFourierCoeff (fun x ↦ f x - g x) n = mFourierCoeff f n - mFourierCoeff g n := by
  have hif : Integrable fun x ↦ mFourier (-n) x • f x :=
    ((mFourier (-n)).continuous.smul hf).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hig : Integrable fun x ↦ mFourier (-n) x • g x :=
    ((mFourier (-n)).continuous.smul hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold mFourierCoeff
  simp_rw [smul_sub]
  exact integral_sub hif hig

lemma norm_mFourierCoeff_le {f : UnitAddTorus d → E} (n : d → ℤ) :
    ‖mFourierCoeff f n‖ ≤ ∫ x, ‖f x‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp [norm_smul]

lemma conj_mFourierCoeff (f : UnitAddTorus d → ℂ) (n : d → ℤ) :
    conj (mFourierCoeff f n) = mFourierCoeff (fun x ↦ conj (f x)) (-n) := by
  unfold mFourierCoeff
  rw [← integral_conj]
  simp only [smul_eq_mul, map_mul, ← mFourier_neg, neg_neg]

/-- For a real-valued `g`, the Fourier coefficients at `n` and `-n` are conjugate. -/
lemma mFourierCoeff_ofReal_neg (g : UnitAddTorus d → ℝ) (n : d → ℤ) :
    mFourierCoeff (fun x ↦ (g x : ℂ)) (-n) = conj (mFourierCoeff (fun x ↦ (g x : ℂ)) n) := by
  rw [conj_mFourierCoeff]
  simp only [Complex.conj_ofReal]

lemma re_mFourierCoeff_ofReal_neg (g : UnitAddTorus d → ℝ) (n : d → ℤ) :
    (mFourierCoeff (fun x ↦ (g x : ℂ)) (-n)).re = (mFourierCoeff (fun x ↦ (g x : ℂ)) n).re := by
  rw [mFourierCoeff_ofReal_neg, Complex.conj_re]

end Coeff

/-! ### Trigonometric series with summable coefficients -/

section Series

variable {c : (d → ℤ) → ℂ}

lemma summable_mul_mFourier (hc : Summable c) (x : UnitAddTorus d) :
    Summable fun n ↦ c n * mFourier n x :=
  hc.norm.of_norm_bounded fun n ↦ by simp

lemma norm_tsum_mul_mFourier_le (hc : Summable c) (x : UnitAddTorus d) :
    ‖∑' n, c n * mFourier n x‖ ≤ ∑' n, ‖c n‖ :=
  (norm_tsum_le_tsum_norm (hc.norm.of_norm_bounded fun n ↦ by simp)).trans
    (le_of_eq (by simp))

/-- A trigonometric series with absolutely summable coefficients is continuous on the torus. -/
lemma continuous_tsum_mul_mFourier (hc : Summable c) :
    Continuous fun x : UnitAddTorus d ↦ ∑' n, c n * mFourier n x :=
  continuous_tsum (fun n ↦ continuous_const.mul (mFourier n).continuous) hc.norm
    fun n x ↦ by simp

/-- The series is even in the sense `f (-x) = ∑' n, c (-n) * mFourier n x`. -/
lemma tsum_mul_mFourier_neg (x : UnitAddTorus d) :
    ∑' n, c n * mFourier n (-x) = ∑' n, c (-n) * mFourier n x := by
  simp_rw [mFourier_apply_neg]
  conv_rhs => rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  simp only [Equiv.neg_apply, neg_neg]

/-- The conjugate of a trigonometric series with real coefficients is the series with the
coefficients reflected. -/
lemma conj_tsum_mul_mFourier (hreal : ∀ n, conj (c n) = c n) (x : UnitAddTorus d) :
    conj (∑' n, c n * mFourier n x) = ∑' n, c (-n) * mFourier n x := by
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  simp only [Equiv.neg_apply, neg_neg, map_mul, hreal, ← mFourier_neg]

/-- **Convolution of coefficients.** Multiplying an integrable `g` by the trigonometric series
`∑' n, c n * mFourier n` convolves the Fourier coefficients:
`(f g)^(m) = ∑' n, c n * ĝ(m - n)`. -/
theorem mFourierCoeff_tsum_mul_mFourier_mul (hc : Summable c) {g : UnitAddTorus d → ℂ}
    (hg : Integrable g) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ (∑' n, c n * mFourier n x) * g x) m
      = ∑' n, c n * mFourierCoeff g (m - n) := by
  set F : (d → ℤ) → UnitAddTorus d → ℂ :=
    fun n x ↦ (c n * mFourier (-m) x * mFourier n x) * g x with hF
  have hFint : ∀ n, Integrable (F n) := fun n ↦ by
    refine hg.bdd_mul (c := ‖c n‖) ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
    · exact ((continuous_const.mul (mFourier (-m)).continuous).mul
        (mFourier n).continuous).aestronglyMeasurable
    · simp
  have hFnorm : ∀ n, ∫ x, ‖F n x‖ = ‖c n‖ * ∫ x, ‖g x‖ := fun n ↦ by
    rw [← integral_const_mul]
    congr 1 with x
    simp [hF]
  have hsum : Summable fun n ↦ ∫ x, ‖F n x‖ := by
    simp_rw [hFnorm]
    exact hc.norm.mul_right _
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsum
  have hpt : ∀ x, mFourier (-m) x • ((∑' n, c n * mFourier n x) * g x) = ∑' n, F n x := by
    intro x
    simp only [hF, smul_eq_mul, ← tsum_mul_right, ← tsum_mul_left]
    congr 1 with n
    ring
  unfold mFourierCoeff
  simp_rw [hpt]
  rw [hHS.tsum_eq.symm]
  congr 1 with n
  have := mFourierCoeff_mFourier_mul n m g
  unfold mFourierCoeff at this
  rw [← this, ← integral_const_mul]
  congr 1 with x
  simp only [hF, smul_eq_mul]
  ring

/-- The Fourier coefficients of a trigonometric series with absolutely summable coefficients are
those coefficients. -/
theorem mFourierCoeff_tsum_mul_mFourier (hc : Summable c) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑' n, c n * mFourier n x) m = c m := by
  have := mFourierCoeff_tsum_mul_mFourier_mul hc (g := fun _ ↦ (1 : ℂ)) (integrable_const _) m
  simp only [mul_one] at this
  rw [this]
  simp_rw [mFourierCoeff_const, sub_eq_zero]
  simp

end Series

/-! ### Uniform approximation by trigonometric polynomials -/

section StoneWeierstrass

/-- **Stone–Weierstrass on the torus, in coordinates.** Every continuous function on
`UnitAddTorus d` is a uniform limit of trigonometric polynomials: for every `ε > 0` there are a
finite `I ⊆ ℤᵈ` and coefficients `c : ℤᵈ → ℂ` with `‖f x - ∑_{j ∈ I} c j * mFourier j x‖ ≤ ε` for
every `x`. This is `span_mFourier_closure_eq_top` unfolded into coordinates. -/
theorem exists_norm_sub_sum_mul_mFourier_le (f : C(UnitAddTorus d, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (I : Finset (d → ℤ)) (c : (d → ℤ) → ℂ),
      ∀ x, ‖f x - ∑ j ∈ I, c j * mFourier j x‖ ≤ ε := by
  have hmem : f ∈ closure ((Submodule.span ℂ (Set.range (mFourier (d := d)))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top]
    trivial
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hb
  refine ⟨c.support, fun j ↦ c j, fun x ↦ ?_⟩
  have hbx : b x = ∑ j ∈ c.support, c j * mFourier j x := by
    rw [← hc, Finsupp.sum]
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← hbx, ← dist_eq_norm]
  exact (ContinuousMap.dist_apply_le_dist x).trans hdist.le

end StoneWeierstrass

/-! ### The zero set of a trigonometric polynomial

A trigonometric polynomial `∑_{j ∈ I} u_j z^j` is, read on `ℝ^d` through the canonical surjection
`p ↦ (p_ℓ mod 1)_ℓ`, a finite sum of exponentials, hence a real-analytic function on `ℝ^d`. The
identity principle therefore forbids it to vanish on a non-empty open subset of the torus without
vanishing identically. This is the step Georgii glosses as "`|g|²` can only vanish on a null set"
in the proof of Proposition (13.A8). -/

section ZeroSet

omit [Fintype d] in
/-- The canonical surjection `ℝ^d → (ℝ/ℤ)^d` is onto. -/
theorem exists_eq_coe (z : UnitAddTorus d) :
    ∃ p : d → ℝ, (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle)) = z := by
  choose p hp using fun ℓ ↦
    (QuotientAddGroup.mk_surjective (z ℓ) : ∃ p : ℝ, ((p : ℝ) : UnitAddCircle) = z ℓ)
  exact ⟨p, funext hp⟩

/-- The monomial `z^n` read on `ℝ^d`: `z_p^n = exp(2πi ∑_ℓ n_ℓ p_ℓ)`. -/
lemma mFourier_coe (n : d → ℤ) (p : d → ℝ) :
    mFourier n (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle))
      = Complex.exp (∑ ℓ, 2 * Real.pi * Complex.I * (n ℓ : ℂ) * (p ℓ : ℂ)) := by
  rw [Complex.exp_sum]
  simp only [mFourier, ContinuousMap.coe_mk]
  exact Finset.prod_congr rfl fun ℓ _ ↦ by rw [fourier_coe_apply]; norm_num

/-- The monomial `z^n`, read on `ℝ^d`, is a real-analytic function. -/
lemma analyticAt_mFourier_coe (n : d → ℤ) (p₀ : d → ℝ) :
    AnalyticAt ℝ (fun p : d → ℝ ↦ mFourier n (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle))) p₀ := by
  have hfun : (fun p : d → ℝ ↦ mFourier n (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle)))
      = Complex.exp ∘ fun p : d → ℝ ↦ ∑ ℓ, 2 * Real.pi * Complex.I * (n ℓ : ℂ) * (p ℓ : ℂ) :=
    funext fun p ↦ mFourier_coe n p
  rw [hfun]
  have hlin : AnalyticAt ℝ
      (fun p : d → ℝ ↦ ∑ ℓ, 2 * Real.pi * Complex.I * (n ℓ : ℂ) * (p ℓ : ℂ)) p₀ := by
    refine Finset.analyticAt_fun_sum _ fun ℓ _ ↦ ?_
    have hproj : AnalyticAt ℝ (fun q : d → ℝ ↦ ((q ℓ : ℝ) : ℂ)) p₀ :=
      ContinuousLinearMap.analyticAt
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d ↦ ℝ) ℓ)) p₀
    exact analyticAt_const.mul hproj
  exact AnalyticAt.comp (AnalyticAt.restrictScalars (𝕜 := ℝ) analyticAt_cexp) hlin

/-- **A trigonometric polynomial vanishing on a non-empty open subset of the torus vanishes
identically.** Read on `ℝ^d` it is real-analytic, so the identity principle
`AnalyticOnNhd.eq_of_eventuallyEq` applies on the connected space `ℝ^d`. -/
theorem sum_mul_mFourier_eq_zero_of_eqOn_zero {I : Finset (d → ℤ)} {u : (d → ℤ) → ℂ}
    {U : Set (UnitAddTorus d)} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, ∑ j ∈ I, u j * mFourier j z = 0) (z : UnitAddTorus d) :
    ∑ j ∈ I, u j * mFourier j z = 0 := by
  have hccont : Continuous fun (p : d → ℝ) ↦ (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle)) := by
    fun_prop
  set F : (d → ℝ) → ℂ :=
    fun p ↦ ∑ j ∈ I, u j * mFourier j (fun ℓ ↦ ((p ℓ : ℝ) : UnitAddCircle))
  have hFa : AnalyticOnNhd ℝ F Set.univ := fun p _ ↦
    Finset.analyticAt_fun_sum _ fun j _ ↦ analyticAt_const.mul (analyticAt_mFourier_coe j p)
  obtain ⟨z₀, hz₀⟩ := hUne
  obtain ⟨p₀, rfl⟩ := exists_eq_coe z₀
  have hnhds : F =ᶠ[nhds p₀] 0 := by
    filter_upwards [(hU.preimage hccont).mem_nhds hz₀] with p hp
    exact h _ hp
  have hzero : F = 0 := hFa.eq_of_eventuallyEq analyticOnNhd_const hnhds
  obtain ⟨p, rfl⟩ := exists_eq_coe z
  exact congrFun hzero p

/-- **The coefficients of a trigonometric polynomial vanishing on a non-empty open subset of the
torus are zero.** -/
theorem eq_zero_of_sum_mul_mFourier_eqOn_zero {I : Finset (d → ℤ)} {u : (d → ℤ) → ℂ}
    {U : Set (UnitAddTorus d)} (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, ∑ j ∈ I, u j * mFourier j z = 0) {j : d → ℤ} (hj : j ∈ I) : u j = 0 := by
  have hzero : (fun z ↦ ∑ j ∈ I, u j * mFourier j z) = fun _ : UnitAddTorus d ↦ (0 : ℂ) :=
    funext (sum_mul_mFourier_eq_zero_of_eqOn_zero hU hUne h)
  have h1 : mFourierCoeff (fun z ↦ ∑ j ∈ I, u j * mFourier j z) j = u j := by
    simp [mFourierCoeff_sum_mul_mFourier, hj]
  rw [hzero, mFourierCoeff_const] at h1
  simpa using h1.symm

end ZeroSet

/-! ### The Toeplitz matrix of a nonnegative function is nonnegative definite -/

section PosSemidef

variable {g : UnitAddTorus d → ℝ}

/-- The quadratic form of the Toeplitz matrix `(i, j) ↦ ĝ(i - j)` at a **complex** vector `u` is
`∫ |∑_j u_j mFourier j|² g`. -/
lemma sum_sum_conj_mul_mFourierCoeff_sub (hg : Integrable g) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℂ) :
    ∑ i ∈ I, ∑ j ∈ I, conj (u i) * u j * mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)
      = ∫ x, (Complex.normSq (∑ j ∈ I, u j * mFourier j x) : ℂ) * g x := by
  have hint : ∀ i j, Integrable fun x ↦
      conj (u i) * u j * (mFourier (-(i - j)) x • (g x : ℂ)) := fun i j ↦ by
    refine Integrable.const_mul ?_ _
    exact hg.ofReal.bdd_mul (c := 1) (mFourier _).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦ by simp)
  simp_rw [mFourierCoeff, ← integral_const_mul]
  have h1 : ∀ i ∈ I, ∑ j ∈ I, ∫ x, conj (u i) * u j * (mFourier (-(i - j)) x • (g x : ℂ))
      = ∫ x, ∑ j ∈ I, conj (u i) * u j * (mFourier (-(i - j)) x • (g x : ℂ)) :=
    fun i _ ↦ (integral_finsetSum _ fun j _ ↦ hint i j).symm
  rw [Finset.sum_congr rfl h1,
    ← integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
  congr 1 with x
  rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul, ← mFourier_neg, smul_eq_mul]
  rw [show -(i - j) = -i + j by abel, mFourier_add]
  ring

/-- The quadratic form of the Toeplitz matrix `(i, j) ↦ ĝ(i - j)` at a real vector `u` is
`∫ |∑_j u_j mFourier j|² g`, complex form. -/
lemma sum_sum_mul_mFourierCoeff_sub (hg : Integrable g) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℝ) :
    ∑ i ∈ I, ∑ j ∈ I, ((u i * u j : ℝ) : ℂ) * mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)
      = ∫ x, (Complex.normSq (∑ j ∈ I, (u j : ℂ) * mFourier j x) : ℂ) * g x := by
  rw [← sum_sum_conj_mul_mFourierCoeff_sub hg I fun j ↦ ((u j : ℝ) : ℂ)]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    simp [Complex.conj_ofReal]

lemma integrable_normSq_sum_mul_mFourier_mul (hg : Integrable g) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℂ) :
    Integrable fun x ↦ Complex.normSq (∑ j ∈ I, u j * mFourier j x) * g x := by
  refine hg.bdd_mul (c := (∑ j ∈ I, ‖u j‖) ^ 2) ?_ (Filter.Eventually.of_forall fun x ↦ ?_)
  · exact (Complex.continuous_normSq.comp
      (continuous_finsetSum _ fun j _ ↦ continuous_const.mul (mFourier j).continuous))
      |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (by simp))

/-- The quadratic form of the real Toeplitz matrix `(i, j) ↦ Re ĝ(i - j)` of a real-valued `g`
at a real vector `u` is `∫ |∑_j u_j mFourier j|² g`. -/
theorem sum_sum_mul_re_mFourierCoeff_sub (hg : Integrable g) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℝ) :
    ∑ i ∈ I, ∑ j ∈ I, u i * u j * (mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re
      = ∫ x, Complex.normSq (∑ j ∈ I, (u j : ℂ) * mFourier j x) * g x := by
  have hre : ∑ i ∈ I, ∑ j ∈ I, u i * u j * (mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re
      = (∑ i ∈ I, ∑ j ∈ I, ((u i * u j : ℝ) : ℂ)
          * mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re := by
    simp [Complex.re_sum]
  rw [hre, sum_sum_mul_mFourierCoeff_sub hg]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- **The Toeplitz matrix of a nonnegative integrable function is nonnegative definite.** For a
real-valued `g ≥ 0` a.e. and any real vector `u` supported on `I`,
`∑_{i,j ∈ I} u_i u_j Re ĝ(i - j) = ∫ |∑_j u_j mFourier j|² g ≥ 0`. -/
theorem sum_sum_mul_re_mFourierCoeff_sub_nonneg (hg : Integrable g)
    (hg0 : 0 ≤ᵐ[volume] g) (I : Finset (d → ℤ)) (u : (d → ℤ) → ℝ) :
    0 ≤ ∑ i ∈ I, ∑ j ∈ I, u i * u j * (mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re := by
  rw [sum_sum_mul_re_mFourierCoeff_sub hg]
  exact integral_nonneg_of_ae (hg0.mono fun x hx ↦ mul_nonneg (Complex.normSq_nonneg _) hx)

/-- **Strict positivity.** If moreover `g ≠ 0` a.e., the quadratic form of the Toeplitz matrix
vanishes at `u` only if `u` vanishes on `I`. -/
theorem eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero (hg : Integrable g)
    (hg0 : 0 ≤ᵐ[volume] g) (hg1 : ∀ᵐ x ∂volume, g x ≠ 0) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℝ)
    (hu : ∑ i ∈ I, ∑ j ∈ I, u i * u j * (mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re = 0) :
    ∀ j ∈ I, u j = 0 := by
  rw [sum_sum_mul_re_mFourierCoeff_sub hg] at hu
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (hg0.mono fun x hx ↦ mul_nonneg (Complex.normSq_nonneg _) hx)
    (integrable_normSq_sum_mul_mFourier_mul hg I fun j ↦ ((u j : ℝ) : ℂ))).1 hu
  have hP : (fun x ↦ ∑ j ∈ I, (u j : ℂ) * mFourier j x) =ᵐ[volume] fun _ ↦ (0 : ℂ) := by
    filter_upwards [hae, hg1] with x hx hgx
    simp only [Pi.zero_apply, mul_eq_zero, hgx, or_false, Complex.normSq_eq_zero] at hx
    exact hx
  intro j hj
  have := congrFun (mFourierCoeff_congr_ae hP) j
  rw [mFourierCoeff_sum_mul_mFourier, mFourierCoeff_const,
    ite_eq_left_of_eq_true _ _ (eq_true hj)] at this
  split_ifs at this with h0
  · exact_mod_cast this
  · exact_mod_cast this

/-- **The Toeplitz matrix of a continuous nonnegative `g ≢ 0` is positive definite**: its
quadratic form vanishes at `u` only if `u` vanishes on `I`. This is Georgii's hypothesis in
Proposition (13.A8) — `ĝ ≥ 0` and `ĝ` not identically zero — in place of the almost-everywhere
non-vanishing of `UnitAddTorus.eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero`: the
trigonometric polynomial `∑_j u_j z^j` vanishes on the non-empty open set `{g ≠ 0}`, hence
everywhere (`UnitAddTorus.eq_zero_of_sum_mul_mFourier_eqOn_zero`). -/
theorem eq_zero_of_sum_sum_mul_re_mFourierCoeff_sub_eq_zero_of_continuous
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hgne : g ≠ 0) (I : Finset (d → ℤ))
    (u : (d → ℤ) → ℝ)
    (hu : ∑ i ∈ I, ∑ j ∈ I, u i * u j * (mFourierCoeff (fun x ↦ (g x : ℂ)) (i - j)).re = 0) :
    ∀ j ∈ I, u j = 0 := by
  have hgint : Integrable g :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [sum_sum_mul_re_mFourierCoeff_sub hgint] at hu
  have hcont : Continuous fun x ↦ Complex.normSq (∑ j ∈ I, (u j : ℂ) * mFourier j x) * g x := by
    fun_prop
  have hnn : (0 : UnitAddTorus d → ℝ)
      ≤ fun x ↦ Complex.normSq (∑ j ∈ I, (u j : ℂ) * mFourier j x) * g x :=
    fun x ↦ mul_nonneg (Complex.normSq_nonneg _) (hg0 x)
  have hae := (integral_eq_zero_iff_of_nonneg hnn
    (integrable_normSq_sum_mul_mFourier_mul hgint I fun j ↦ ((u j : ℝ) : ℂ))).1 hu
  have heq : (fun x ↦ Complex.normSq (∑ j ∈ I, (u j : ℂ) * mFourier j x) * g x) = 0 :=
    (hcont.ae_eq_iff_eq volume continuous_const).1 hae
  obtain ⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by
    by_contra hcon
    exact hgne (funext fun x ↦ not_not.1 fun hx ↦ hcon ⟨x, hx⟩)
  have hvanish : ∀ z ∈ {x | g x ≠ 0}, ∑ j ∈ I, ((u j : ℝ) : ℂ) * mFourier j z = 0 := by
    intro z hz
    have hz' : g z ≠ 0 := hz
    rcases mul_eq_zero.1 (congrFun heq z) with hcon | hcon
    · exact Complex.normSq_eq_zero.1 hcon
    · exact absurd hcon hz'
  intro j hj
  exact_mod_cast eq_zero_of_sum_mul_mFourier_eqOn_zero
    (isOpen_ne_fun hg continuous_const) ⟨x₀, hx₀⟩ hvanish hj

end PosSemidef

end UnitAddTorus

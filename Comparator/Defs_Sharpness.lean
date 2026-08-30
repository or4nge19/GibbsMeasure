import Comparator.Defs_Dobrushin

/-!
# Georgii, Example (2.27): the Bernoulli measures

The two objects of Georgii's Example (2.27) that are not already part of Section 8.1. Section 8.1
is imported rather than copied, so that the `interdep` and `IsQuasilocalSpec` appearing in the
sharpness statements are literally those used to state Dobrushin's uniqueness theorem (8.7).

## Main definitions

* `bern`: Georgii (2.27), the single spin distribution `λ^x = x δ_1 + (1 − x) δ_0` on `E = {0,1}`.
* `bernoulliField`: Georgii (2.27), the Bernoulli random field `μ^x = (λ^x)^ℕ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace SharpnessChallenge

open GibbsChallenge DobrushinChallenge

/-! ## Georgii (2.27): the single spin distributions -/

/-- **Georgii (2.27)**: the single spin distribution `λ^x = x δ_1 + (1 − x) δ_0` on the two-point
spin space `E = {0, 1}`, here realised as `Bool` with `1 = true` and `0 = false`. -/
def bern (x : ℝ) : Measure Bool :=
  ENNReal.ofReal x • Measure.dirac true + ENNReal.ofReal (1 - x) • Measure.dirac false

theorem bern_apply (x : ℝ) (B : Set Bool) :
    bern x B = ENNReal.ofReal x * B.indicator 1 true + ENNReal.ofReal (1 - x) *
      B.indicator 1 false := by
  simp [bern, Measure.add_apply, Measure.smul_apply, smul_eq_mul]

@[simp] theorem bern_apply_true (x : ℝ) : bern x {true} = ENNReal.ofReal x := by
  simp [bern_apply]

@[simp] theorem bern_apply_false (x : ℝ) : bern x {false} = ENNReal.ofReal (1 - x) := by
  simp [bern_apply]

theorem isProbabilityMeasure_bern {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsProbabilityMeasure (bern x) := by
  constructor
  rw [bern_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add hx0 (by linarith)]
  simp

@[simp] theorem bern_zero : bern 0 = Measure.dirac false := by
  simp [bern]

@[simp] theorem bern_one : bern 1 = Measure.dirac true := by
  simp [bern]

/-! ## Georgii (2.27): the Bernoulli random fields -/

/-- **Georgii (2.27)**: the Bernoulli random field `μ^x = (λ^x)^ℕ`, the law of a sequence of
independent spins each distributed as `λ^x`. -/
def bernoulliField (x : ℝ) : Measure (Config ℕ Bool) := Measure.infinitePi fun _ : ℕ ↦ bern x

theorem isProbabilityMeasure_bernoulliField {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsProbabilityMeasure (bernoulliField x) := by
  have : ∀ _ : ℕ, IsProbabilityMeasure (bern x) := fun _ ↦ isProbabilityMeasure_bern hx0 hx1
  rw [bernoulliField]
  infer_instance

/-- Under `μ^x` each single spin `σ_i` is `λ^x`-distributed. -/
theorem bernoulliField_map_eval {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    (bernoulliField x).map (fun ω : Config ℕ Bool ↦ ω i) = bern x := by
  exact @Measure.infinitePi_map_eval ℕ (fun _ ↦ Bool) (fun _ ↦ inferInstance)
    (fun _ ↦ bern x) (fun _ ↦ isProbabilityMeasure_bern hx0 hx1) i

/-- `μ^x(σ_i = 1) = x`; in particular `μ^x` is not a degenerate object. -/
theorem bernoulliField_apply_eq_true {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (i : ℕ) :
    bernoulliField x {ω : Config ℕ Bool | ω i = true} = ENNReal.ofReal x := by
  have hmeas : Measurable fun ω : Config ℕ Bool ↦ ω i := measurable_pi_apply i
  have h : {ω : Config ℕ Bool | ω i = true} = (fun ω : Config ℕ Bool ↦ ω i) ⁻¹' {true} := rfl
  rw [h, ← Measure.map_apply hmeas (measurableSet_singleton true),
    bernoulliField_map_eval hx0 hx1 i, bern_apply_true]

/-- Distinct parameters in `[0,1]` give distinct Bernoulli fields. -/
theorem bernoulliField_ne {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hxy : x ≠ y) : bernoulliField x ≠ bernoulliField y := by
  intro h
  have h1 := bernoulliField_apply_eq_true hx.1 hx.2 0
  rw [h, bernoulliField_apply_eq_true hy.1 hy.2 0] at h1
  exact hxy ((ENNReal.ofReal_eq_ofReal_iff hx.1 hy.1).1 h1.symm)

end SharpnessChallenge

end

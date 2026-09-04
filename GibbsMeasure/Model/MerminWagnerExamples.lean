/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.MerminWagner
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.HaarToSphere
public import GibbsMeasure.Mathlib.Analysis.InnerProductSpace.ExpSkewAdjoint
public import GibbsMeasure.Mathlib.Analysis.InnerProductSpace.PlaneRotations
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# Georgii §9.2: Examples (9.22)–(9.23) of the Mermin–Wagner theorem

The instances of Theorem (9.20) (`measurePreserving_of_logDecay` in
`GibbsMeasure/Model/MerminWagner.lean`) given by Georgii.

## Plane rotors, Example (9.22)

The state space is the circle `E = ℝ / 2πℤ` (`AddCircle (2 * π)`, Georgii's `[0, 2π[`), the a
priori measure the normalised Haar measure `AddCircle.haarAddCircle`, and the symmetry group the
simultaneous rotations `τ^t ω = (ω_i + t)_i` (`spinRotation`).

* `MeasureTheory.GibbsMeasure.rotorPair g`: the pair interactions `φ_{ij}(x, y) = g_{ij}(y − x)`
  invariant under all rotations, and `measurePreserving_spinRotation_rotorPair`: **Theorem (9.20)
  for rotor models**, every `μ ∈ 𝒢(βΦ)` is invariant under every `τ^t` provided
  `t ↦ g_{ij}(θ + t)` is `C²` with `β g_{ij}'' ≤ J(i, j)` and `J` satisfies (9.21).
* `MeasureTheory.GibbsMeasure.longRangeRotor p`: **Example (9.22)(1)**, the long-range plane rotor
  `φ_{ij}(x, y) = −|i − j|^{-p} cos (y − x)` on `ℤ²` (Euclidean distance `intLexEuclid`);
  `isAbsolutelySummable_pair_longRangeRotor` (`p > 2`) and
  `measurePreserving_spinRotation_longRangeRotor`: for `p ≥ 4` and every inverse temperature
  `β`, every `μ ∈ 𝒢(βΦ)` is invariant under every rotation `τ^t`. The coupling of (9.21) is
  `J(i, j) = |β| ‖i − j‖_∞^{-4}`, which dominates `|β| |i − j|^{-p}` since `‖·‖_∞ ≤ |·|`.
* `MeasureTheory.GibbsMeasure.shlosmanRotor`: **Example (9.22)(2)**, Shlosman's rotator
  `φ_{ij} = −cos(x − y)` for `|i − j| = √2`, `cos²(x − y)` for `|i − j| = 1` (the profile
  `shlosmanProfile`), absolutely summable as a bounded finite-range potential, and
  `measurePreserving_spinRotation_shlosmanRotor`: for every `β`, every `μ ∈ 𝒢(βΦ)` is invariant
  under every rotation, from `logDecay_of_finite_range` with the coupling `J = 2|β|` between
  neighbours. (The phase transition of this model, Georgii §18.3.8, is not treated here.)

## Classical Heisenberg models, Example (9.23)

The state space is the unit sphere of a finite-dimensional real inner product space `V`
(Georgii: `ℝ^N`, `N ≥ 2`), the a priori measure the surface measure `volume.toSphere`
(Mathlib's `Measure.toSphere`), and the interaction `φ_{ij}(x, y) = −K(i, j) ⟪x, y⟫`
(`heisenbergPair K`).

* `measurePreserving_sphereRotation_heisenbergPair`: **Theorem (9.20) for one-parameter groups
  of rotations**: for a one-parameter group `R : ℝ → V ≃ₗᵢ[ℝ] V` of rotations with `C²` orbits
  `t ↦ R_t y` and `‖(R_· y)''‖ ≤ M` on the sphere, and `|K(i, j)| ≤ K₀ ‖i − j‖^{-4}`, every
  `μ ∈ 𝒢(βΦ)` is invariant under every `R_t`.
* `measurePreserving_sphereRotation_expRotation_heisenbergPair`: the one-parameter groups
  `t ↦ exp (t A)` of a skew-adjoint `A` (`skewAdjoint.expRotation`), Georgii's
  `M(t r₁, …, t rₙ)`: every `μ ∈ 𝒢(βΦ)` is invariant under `exp A` for every skew-adjoint `A`.
* `measurePreserving_sphereRotation_orthogonalExtend_rotation_heisenbergPair`: the rotation
  `M(θ)` of any plane `K ≤ V`, extended by the identity on `Kᗮ` (`Submodule.orthogonalExtend`),
  is the time-one map of the one-parameter group `t ↦ M(θ t)` of the plane
  (`planeRotationOneParam`, built on Mathlib's `Orientation.rotation`), so every `μ ∈ 𝒢(βΦ)` is
  invariant under it.
* `measurePreserving_sphereRotation_of_det_pos_heisenbergPair`: **Example (9.23) in full, the
  `SO(N)`-symmetry is not broken**: every `μ ∈ 𝒢(βΦ)` is invariant under every rotation
  `r ∈ SO(N)` (every linear isometric equivalence of positive determinant). Georgii embeds `r`
  into a one-parameter subgroup through the real normal form `M(r₁, …, rₙ)` of an orthogonal
  matrix; here `r` is written as a product of plane rotations by the Cartan–Dieudonné theorem
  (`LinearIsometryEquiv.exists_list_orthogonalExtend_rotation_prod_of_det_pos`), and the
  invariance passes to products (`measurePreserving_pureSpin_sphereMeasurableEquiv_list_prod`).
  On `ℤ²` with the surface measure and `|K(i, j)| ≤ K₀ |i − j|^{-p}`, `p ≥ 4`:
  `measurePreserving_sphereRotation_of_det_pos_heisenbergPair_int_lex`.

## Conventions

As in `MerminWagner.lean`, the inverse temperature `β` multiplies the Hamiltonian, so that
Georgii's `βΦ` is the potential at inverse temperature `β`; the hypothesis (ii) of (9.20) is
read for `βΦ`, so no sign condition on `β` is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Potential
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### One-parameter groups of pure spin transformations, Georgii (9.18) -/

variable {S E : Type*} [MeasurableSpace E]

/-- A one-parameter group `t ↦ e_t` of measurable bijections of the state space induces the
one-parameter group `τ^t = pureSpin S e_t` of pure spin transformations, Georgii (9.18):
`τ^s τ^t = τ^{s + t}`. -/
lemma pureSpin_mul_pureSpin {e : ℝ → E ≃ᵐ E} (he : ∀ s t x, e s (e t x) = e (s + t) x)
    (s t : ℝ) : pureSpin S (e s) * pureSpin S (e t) = pureSpin S (e (s + t)) := by
  rw [pureSpin_mul]
  congr 1
  exact MeasurableEquiv.ext (funext fun x ↦ he s t x)

/-! ### Georgii, Example (9.22): plane rotors -/

section Rotor

open Real

/-- `0 < 2π`, needed for the Haar measure of `AddCircle (2 * π)`. -/
instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Georgii (9.22): the rotation `x ↦ x + t` of the circle `E = ℝ / 2πℤ` by the angle `t`. -/
def spinRotation (t : ℝ) : AddCircle (2 * π) ≃ᵐ AddCircle (2 * π) :=
  MeasurableEquiv.addRight (t : AddCircle (2 * π))

@[simp] lemma spinRotation_apply (t : ℝ) (x : AddCircle (2 * π)) :
    spinRotation t x = x + (t : AddCircle (2 * π)) := rfl

/-- The rotations form a one-parameter group. -/
lemma spinRotation_spinRotation (s t : ℝ) (x : AddCircle (2 * π)) :
    spinRotation s (spinRotation t x) = spinRotation (s + t) x := by
  simp only [spinRotation_apply, AddCircle.coe_add, add_assoc, add_comm (t : AddCircle (2 * π))]

/-- The rotations preserve the Haar measure of the circle. -/
lemma measurePreserving_spinRotation (t : ℝ) :
    MeasurePreserving (spinRotation t) AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  measurePreserving_add_right _ _

/-- Georgii (9.22): the rotation-invariant pair interactions `φ_{ij}(x, y) = g_{ij}(y − x)` on
the circle. -/
def rotorPair (g : S → S → AddCircle (2 * π) → ℝ) :
    S → S → AddCircle (2 * π) → AddCircle (2 * π) → ℝ :=
  fun i j x y ↦ g i j (y - x)

/-- The rotor interactions are invariant under the simultaneous rotations. -/
lemma rotorPair_spinRotation (g : S → S → AddCircle (2 * π) → ℝ) (t : ℝ) (i j : S)
    (x y : AddCircle (2 * π)) :
    rotorPair g i j (spinRotation t x) (spinRotation t y) = rotorPair g i j x y := by
  simp [rotorPair]

variable [LinearOrder S]

/-- `Φ = pair (rotorPair g)` is invariant under every rotation
`τ^t = pureSpin S (spinRotation t)`. -/
lemma map_pureSpin_spinRotation_pair_rotorPair (g : S → S → AddCircle (2 * π) → ℝ) (t : ℝ) :
    Potential.map (pureSpin S (spinRotation t)) (pair (rotorPair g)) = pair (rotorPair g) :=
  (map_pair_eq_iff _ (isPureSpin_pureSpin _)).2 fun i j _ x y ↦ rotorPair_spinRotation g t i j x y

/-- The rotor interactions are measurable when the `g_{ij}` are. -/
lemma isPotential_pair_rotorPair {g : S → S → AddCircle (2 * π) → ℝ}
    (hg : ∀ i j, Measurable (g i j)) : IsPotential (pair (rotorPair g)) :=
  isPotential_pair _ fun i j ↦ (hg i j).comp (measurable_snd.sub measurable_fst)

variable [Countable S]

/-- **Georgii, Theorem (9.20) for rotor models.** Let `S` be a countable linearly ordered site
set with a planar norm (e.g. `ℤ²`), `E = ℝ / 2πℤ` with the normalised Haar measure, and
`Φ = pair (rotorPair g)` a `λ`-admissible rotor potential such that `t ↦ g_{ij}(θ + t)` is `C²`
with `β ∂²_t g_{ij}(θ + t) ≤ J(i, j)` for a symmetric `J ≥ 0` satisfying the decay condition
(9.21). Then every `μ ∈ 𝒢(βΦ)` is invariant under every rotation `τ^u`. -/
theorem measurePreserving_spinRotation_rotorPair {g : S → S → AddCircle (2 * π) → ℝ}
    [IsPotential (pair (rotorPair g))] [IsSummable (pair (rotorPair g))] {β : ℝ}
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := AddCircle (2 * π))
      AddCircle.haarAddCircle ((pair (rotorPair g)).boltzmannFactor β))
    (hg : ∀ i j, i < j → ∀ θ : AddCircle (2 * π), ContDiff ℝ 2 fun t : ℝ ↦ g i j (θ + t))
    {J : S → S → ℝ} (hJ : ∀ i j, i < j → ∀ (θ : AddCircle (2 * π)) (t : ℝ),
      β * iteratedDeriv 2 (fun t : ℝ ↦ g i j (θ + t)) t ≤ J i j)
    (hJ0 : ∀ i j, 0 ≤ J i j) (hJsymm : ∀ i j, J i j = J j i)
    {nrm : S → ℕ} {d : S → S → ℕ} {c₀ : ℕ} (hgeo : MerminWagner.IsPlanarSiteNorm nrm d c₀)
    {K : ℝ} (hdecay : MerminWagner.LogDecay d J K)
    {μ : Measure (S → AddCircle (2 * π))}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (rotorPair g))
      AddCircle.haarAddCircle β hadm)) (u : ℝ) :
    MeasurePreserving (pureSpin S (spinRotation u)).toFun μ μ := by
  have hshift : ∀ i j (x y : AddCircle (2 * π)),
      (fun t : ℝ ↦ rotorPair g i j x (spinRotation t y)) =
        fun t : ℝ ↦ g i j ((y - x) + (t : AddCircle (2 * π))) := by
    intro i j x y
    funext t
    simp only [rotorPair, spinRotation_apply, add_sub_right_comm]
  refine measurePreserving_of_logDecay (τ := fun t ↦ pureSpin S (spinRotation t)) _ hadm
    (fun _ ↦ isPureSpin_pureSpin _) (pureSpin_mul_pureSpin spinRotation_spinRotation)
    (fun t _ ↦ measurePreserving_spinRotation t)
    (fun t i j _ x y ↦ rotorPair_spinRotation g t i j x y) (fun i j hij x y ↦ ?_)
    (fun i j hij x y t ↦ ?_) hJ0 hJsymm hgeo hdecay hμ u
  · simp only [pureSpin_spin]
    rw [hshift]
    exact hg i j hij (y - x)
  · simp only [pureSpin_spin]
    rw [hshift]
    exact hJ i j hij (y - x) t

end Rotor

/-! ### Georgii, Example (9.22)(1): long-range plane rotors on `ℤ²` -/

section LongRangeRotor

open Real MerminWagner

/-- The Euclidean distance `|i − j|` on `ℤ² = ℤ ×ₗ ℤ`. -/
def intLexEuclid (i j : ℤ ×ₗ ℤ) : ℝ :=
  √((((ofLex i).1 - (ofLex j).1 : ℤ) : ℝ) ^ 2 + (((ofLex i).2 - (ofLex j).2 : ℤ) : ℝ) ^ 2)

lemma intLexEuclid_nonneg (i j : ℤ ×ₗ ℤ) : 0 ≤ intLexEuclid i j := Real.sqrt_nonneg _

/-- The maximum norm is dominated by the Euclidean norm: `‖i − j‖_∞ ≤ |i − j|`. -/
lemma intLexDist_le_intLexEuclid (i j : ℤ ×ₗ ℤ) : (intLexDist i j : ℝ) ≤ intLexEuclid i j := by
  unfold intLexDist intLexEuclid
  rw [Real.le_sqrt (by positivity) (by positivity)]
  rcases le_total ((ofLex i).1 - (ofLex j).1).natAbs ((ofLex i).2 - (ofLex j).2).natAbs with h | h
  · rw [max_eq_right h]
    have : ((((ofLex i).2 - (ofLex j).2).natAbs : ℕ) : ℝ) ^ 2 =
        (((ofLex i).2 - (ofLex j).2 : ℤ) : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [this]
    nlinarith [sq_nonneg ((((ofLex i).1 - (ofLex j).1 : ℤ) : ℝ))]
  · rw [max_eq_left h]
    have : ((((ofLex i).1 - (ofLex j).1).natAbs : ℕ) : ℝ) ^ 2 =
        (((ofLex i).1 - (ofLex j).1 : ℤ) : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [this]
    nlinarith [sq_nonneg ((((ofLex i).2 - (ofLex j).2 : ℤ) : ℝ))]

/-- Distinct sites are at maximum-norm distance at least `1`. -/
lemma one_le_intLexDist_of_ne {i j : ℤ ×ₗ ℤ} (hij : i ≠ j) : 1 ≤ intLexDist i j := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have h' : (ofLex i).1 = (ofLex j).1 ∧ (ofLex i).2 = (ofLex j).2 := by
    simp only [intLexDist] at h
    omega
  exact hij (ofLex.injective (Prod.ext h'.1 h'.2))

lemma one_le_intLexDist_of_lt {i j : ℤ ×ₗ ℤ} (hij : i < j) : 1 ≤ intLexDist i j :=
  one_le_intLexDist_of_ne hij.ne

/-- Sites at positive maximum-norm distance are distinct. -/
lemma ne_of_intLexDist_pos {i j : ℤ ×ₗ ℤ} (h : 0 < intLexDist i j) : i ≠ j := by
  rintro rfl
  simp [intLexDist] at h

/-- **Georgii, Example (9.22)(1).** The long-range plane rotor interaction
`φ_{ij}(x, y) = −|i − j|^{-p} cos (y − x)` on `ℤ²`, Georgii's `β` being the inverse temperature
of the Gibbs specification. -/
def longRangeRotor (p : ℝ) :
    ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → AddCircle (2 * π) → AddCircle (2 * π) → ℝ :=
  rotorPair fun i j θ ↦ -(intLexEuclid i j ^ (-p)) * Real.Angle.cos θ

/-- `Real.Angle.cos` is measurable on the circle. -/
lemma measurable_angle_cos : Measurable fun x : AddCircle (2 * π) ↦ Real.Angle.cos x :=
  Continuous.measurable (f := fun x : AddCircle (2 * π) ↦ Real.Angle.cos x)
    Real.Angle.continuous_cos

/-- `|cos θ| ≤ 1` on the circle. -/
lemma abs_angle_cos_le_one (θ : AddCircle (2 * π)) : |Real.Angle.cos θ| ≤ 1 := by
  induction θ using Real.Angle.induction_on with
  | h x => rw [Real.Angle.cos_coe]; exact Real.abs_cos_le_one x

instance isPotential_pair_longRangeRotor (p : ℝ) : IsPotential (pair (longRangeRotor p)) :=
  isPotential_pair_rotorPair fun _ _ ↦ measurable_angle_cos.const_mul _

/-- `|i − j|^{-p} ≤ ‖i − j‖_∞^{-p}` for `p ≥ 0` and `i ≠ j`. -/
lemma intLexEuclid_rpow_neg_le {p : ℝ} (hp : 0 ≤ p) {i j : ℤ ×ₗ ℤ} (hij : i ≠ j) :
    intLexEuclid i j ^ (-p) ≤ (intLexDist i j : ℝ) ^ (-p) := by
  have h1 : (1 : ℝ) ≤ intLexDist i j := by exact_mod_cast one_le_intLexDist_of_ne hij
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (intLexDist_le_intLexEuclid i j)
    (neg_nonpos.2 hp)

/-- The interaction terms of the long-range rotor are bounded by `‖i − j‖_∞^{-p}`. -/
lemma enorm_longRangeRotor_le {p : ℝ} (hp : 0 ≤ p) {i j : ℤ ×ₗ ℤ} (hij : i < j)
    (x y : AddCircle (2 * π)) :
    ‖longRangeRotor p i j x y‖ₑ ≤ ENNReal.ofReal ((intLexDist i j : ℝ) ^ (-p)) := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [longRangeRotor, rotorPair, norm_mul, norm_neg, Real.norm_eq_abs]
  have h0 : 0 ≤ intLexEuclid i j ^ (-p) := Real.rpow_nonneg (intLexEuclid_nonneg i j) _
  rw [abs_of_nonneg h0]
  calc intLexEuclid i j ^ (-p) * |Real.Angle.cos (y - x)|
      ≤ intLexEuclid i j ^ (-p) * 1 :=
        mul_le_mul_of_nonneg_left (abs_angle_cos_le_one _) h0
    _ ≤ (intLexDist i j : ℝ) ^ (-p) := by
        rw [mul_one]; exact intLexEuclid_rpow_neg_le hp hij.ne

/-- The row sums `∑_j ‖i − j‖_∞^{-p}` on `ℤ²` are finite for `p > 2` (Georgii: "the condition
`p > 2` implies that `Φ` is absolutely summable"). -/
lemma tsum_ofReal_intLexDist_rpow_neg_ne_top {p : ℝ} (hp : 2 < p) (i : ℤ ×ₗ ℤ) :
    ∑' j, ENNReal.ofReal ((intLexDist i j : ℝ) ^ (-p)) ≠ ⊤ := by
  set G : ℕ → ℝ≥0∞ := fun m ↦ ENNReal.ofReal ((m : ℝ) ^ (-p)) with hG
  have hle := tsum_comp_dist_le (d := intLexDist) (c₀ := 8) encard_setOf_intLexDist_eq_le i G
  refine ne_top_of_le_ne_top ?_ hle
  set g : ℕ → ℝ := fun m ↦ ((8 * (m + 1) : ℕ) : ℝ) * (m : ℝ) ^ (-p) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m ↦ mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)
  have hgle : ∀ m, g m ≤ 16 * (m : ℝ) ^ (1 - p) := by
    intro m
    simp only [hg]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      simp
    · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have : (m : ℝ) ^ (1 - p) = m * (m : ℝ) ^ (-p) := by
        rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
      rw [this]
      push_cast
      have h0 : 0 ≤ (m : ℝ) ^ (-p) := Real.rpow_nonneg (by positivity) _
      nlinarith
  have hsum : Summable g :=
    Summable.of_nonneg_of_le hg0 hgle
      ((Real.summable_nat_rpow.2 (by linarith)).mul_left 16)
  have : ∑' m, ((8 * (m + 1) : ℕ) : ℝ≥0∞) * G m = ENNReal.ofReal (∑' m, g m) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hg0 hsum]
    refine tsum_congr fun m ↦ ?_
    simp only [hG, hg]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  rw [this]
  exact ENNReal.ofReal_ne_top

/-- **Georgii, Example (9.22)(1)**: for `p > 2` the long-range rotor potential is absolutely
summable. -/
theorem isAbsolutelySummable_pair_longRangeRotor {p : ℝ} (hp : 2 < p) :
    IsAbsolutelySummable (pair (longRangeRotor p)) :=
  isAbsolutelySummable_pair (fun i j hij x y ↦ enorm_longRangeRotor_le (by linarith) hij x y)
    (fun i j ↦ by rw [isPlanarSiteNorm_int_lex.d_comm])
    (tsum_ofReal_intLexDist_rpow_neg_ne_top hp)

/-- `t ↦ cos(θ + t)` on the circle is `C²` (indeed smooth). -/
lemma contDiff_angle_cos_add (θ : AddCircle (2 * π)) :
    ContDiff ℝ 2 fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π))) := by
  obtain ⟨θ₀, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have : (fun t : ℝ ↦ Real.Angle.cos ((θ₀ : AddCircle (2 * π)) + (t : AddCircle (2 * π)))) =
      fun t ↦ Real.cos (θ₀ + t) := by
    funext t
    rw [← AddCircle.coe_add]
    exact Real.Angle.cos_coe _
  rw [this]
  exact Real.contDiff_cos.comp (contDiff_const.add contDiff_id)

/-- `|∂²_t cos(θ + t)| ≤ 1` on the circle. -/
lemma abs_iteratedDeriv_two_angle_cos_add_le (θ : AddCircle (2 * π)) (t : ℝ) :
    |iteratedDeriv 2 (fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π)))) t| ≤ 1 := by
  obtain ⟨θ₀, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have : (fun t : ℝ ↦ Real.Angle.cos ((θ₀ : AddCircle (2 * π)) + (t : AddCircle (2 * π)))) =
      fun t ↦ Real.cos (θ₀ + t) := by
    funext t
    rw [← AddCircle.coe_add]
    exact Real.Angle.cos_coe _
  rw [this, iteratedDeriv_comp_const_add]
  exact Real.abs_iteratedDeriv_cos_le_one 2 _

/-- The hypothesis (ii) of (9.20) for the long-range rotor at inverse temperature `β`:
`β ∂²_t φ_{ij}(x, τ^t_j y) ≤ |β| / ‖i − j‖_∞⁴` for `p ≥ 4`. -/
lemma mul_iteratedDeriv_two_longRangeRotor_le {p : ℝ} (hp : 4 ≤ p) (β : ℝ) {i j : ℤ ×ₗ ℤ}
    (hij : i < j) (θ : AddCircle (2 * π)) (t : ℝ) :
    β * iteratedDeriv 2 (fun t : ℝ ↦
      -(intLexEuclid i j ^ (-p)) * Real.Angle.cos (θ + (t : AddCircle (2 * π)))) t ≤
      |β| / (intLexDist i j : ℝ) ^ 4 := by
  rw [iteratedDeriv_const_mul _ (contDiff_angle_cos_add θ).contDiffAt]
  have h1 : (1 : ℝ) ≤ intLexDist i j := by exact_mod_cast one_le_intLexDist_of_lt hij
  have hD := abs_iteratedDeriv_two_angle_cos_add_le θ t
  have hc0 : 0 ≤ intLexEuclid i j ^ (-p) := Real.rpow_nonneg (intLexEuclid_nonneg i j) _
  have hc : intLexEuclid i j ^ (-p) ≤ 1 / (intLexDist i j : ℝ) ^ 4 := by
    calc intLexEuclid i j ^ (-p) ≤ (intLexDist i j : ℝ) ^ (-p) :=
          intLexEuclid_rpow_neg_le (by linarith) hij.ne
      _ ≤ (intLexDist i j : ℝ) ^ (-(4 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = 1 / (intLexDist i j : ℝ) ^ 4 := by
          rw [Real.rpow_neg (by linarith), one_div]
          norm_cast
  calc β * (-(intLexEuclid i j ^ (-p)) *
        iteratedDeriv 2 (fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π)))) t)
      ≤ |β * (-(intLexEuclid i j ^ (-p)) *
        iteratedDeriv 2 (fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π)))) t)| :=
        le_abs_self _
    _ = |β| * (intLexEuclid i j ^ (-p) *
        |iteratedDeriv 2 (fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π)))) t|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hc0]
    _ ≤ |β| * (1 / (intLexDist i j : ℝ) ^ 4 * 1) := by gcongr
    _ = |β| / (intLexDist i j : ℝ) ^ 4 := by ring

/-- **Georgii, Example (9.22)(1).** For `p ≥ 4` and every inverse temperature `β`, every Gibbs
measure of the long-range plane rotor `φ_{ij}(x, y) = −|i − j|^{-p} cos (y − x)` on `ℤ²` is
invariant under every simultaneous rotation `τ^u` of the spins: there is no breaking of the
continuous symmetry. (For `2 < p < 4` and large `β` the symmetry *is* broken, Georgii (20.21),
not treated here.) -/
theorem measurePreserving_spinRotation_longRangeRotor {p : ℝ} (hp : 4 ≤ p) (β : ℝ)
    {μ : Measure (ℤ ×ₗ ℤ → AddCircle (2 * π))}
    (hμ : haveI := isAbsolutelySummable_pair_longRangeRotor (by linarith : 2 < p)
      μ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := pair (longRangeRotor p))
        AddCircle.haarAddCircle β)) (u : ℝ) :
    MeasurePreserving (pureSpin (ℤ ×ₗ ℤ) (spinRotation u)).toFun μ μ := by
  have hsum := isAbsolutelySummable_pair_longRangeRotor (by linarith : 2 < p)
  rw [← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure,
    gibbsSpecificationOfFiniteReference] at hμ
  have hJ0 : ∀ i j : ℤ ×ₗ ℤ, 0 ≤ |β| / (intLexDist i j : ℝ) ^ 4 := fun i j ↦ by positivity
  have hJsymm : ∀ i j : ℤ ×ₗ ℤ, |β| / (intLexDist i j : ℝ) ^ 4 = |β| / (intLexDist j i : ℝ) ^ 4 :=
    fun i j ↦ by rw [isPlanarSiteNorm_int_lex.d_comm]
  have hdecay := logDecay_of_le_div_pow_four (J := fun i j ↦ |β| / (intLexDist i j : ℝ) ^ 4)
    encard_setOf_intLexDist_eq_le hJ0 (abs_nonneg β) fun i j _ ↦ le_rfl
  have hg : ∀ i j : ℤ ×ₗ ℤ, i < j → ∀ θ : AddCircle (2 * π), ContDiff ℝ 2 fun t : ℝ ↦
      -(intLexEuclid i j ^ (-p)) * Real.Angle.cos (θ + (t : AddCircle (2 * π))) :=
    fun i j _ θ ↦ contDiff_const.mul (contDiff_angle_cos_add θ)
  have : IsPotential (pair (rotorPair fun i j θ ↦ -(intLexEuclid i j ^ (-p)) *
    Real.Angle.cos θ)) := isPotential_pair_longRangeRotor p
  have : IsAbsolutelySummable (pair (rotorPair fun i j θ ↦ -(intLexEuclid i j ^ (-p)) *
    Real.Angle.cos θ)) := hsum
  exact measurePreserving_spinRotation_rotorPair
    (g := fun i j θ ↦ -(intLexEuclid i j ^ (-p)) * Real.Angle.cos θ)
    (J := fun i j ↦ |β| / (intLexDist i j : ℝ) ^ 4) (β := β)
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor _ _) hg
    (fun i j hij θ t ↦ mul_iteratedDeriv_two_longRangeRotor_le hp β hij θ t)
    hJ0 hJsymm isPlanarSiteNorm_int_lex hdecay hμ u

end LongRangeRotor

/-! ### Georgii, Example (9.22)(2): Shlosman's rotator -/

section ShlosmanRotor

open Real MerminWagner

/-- The profile `g_{ij}` of Shlosman's rotator: `−cos` between diagonal neighbours
(`|i − j| = √2`), `cos²` between nearest neighbours (`|i − j| = 1`), `0` otherwise. -/
def shlosmanProfile (i j : ℤ ×ₗ ℤ) (θ : AddCircle (2 * π)) : ℝ :=
  if intLexEuclid i j = √2 then -Real.Angle.cos θ
  else if intLexEuclid i j = 1 then Real.Angle.cos θ ^ 2 else 0

/-- **Georgii, Example (9.22)(2).** Shlosman's rotator on `ℤ²`: the interaction
`φ_{ij}(x, y) = −cos (x − y)` between diagonal neighbours (`|i − j| = √2`), `cos² (x − y)`
between nearest neighbours (`|i − j| = 1`), and `0` otherwise (as `cos` is even, `cos (x − y)`
is the rotor interaction `g_{ij}(y − x)`); Georgii's `β > 0` is the inverse temperature of the
Gibbs specification. -/
abbrev shlosmanRotor : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → AddCircle (2 * π) → AddCircle (2 * π) → ℝ :=
  rotorPair shlosmanProfile

/-- Sites at Euclidean distance `1` or `√2` are at maximum-norm distance at most `1`. -/
lemma intLexDist_le_one_of_intLexEuclid_eq {i j : ℤ ×ₗ ℤ}
    (h : intLexEuclid i j = √2 ∨ intLexEuclid i j = 1) : intLexDist i j ≤ 1 := by
  have hle := intLexDist_le_intLexEuclid i j
  have hsqrt : √2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rcases h with h | h
  · rw [h] at hle
    have : (intLexDist i j : ℝ) < 2 := hle.trans_lt hsqrt
    exact Nat.lt_succ_iff.1 (by exact_mod_cast this)
  · rw [h] at hle
    exact_mod_cast hle

/-- Shlosman's rotator has range `1` in the maximum norm. -/
lemma shlosmanProfile_eq_zero_of_one_lt_intLexDist {i j : ℤ ×ₗ ℤ} (h : 1 < intLexDist i j)
    (θ : AddCircle (2 * π)) : shlosmanProfile i j θ = 0 := by
  have h1 : intLexEuclid i j ≠ √2 := fun h1 ↦
    h.not_ge (intLexDist_le_one_of_intLexEuclid_eq (Or.inl h1))
  have h2 : intLexEuclid i j ≠ 1 := fun h2 ↦
    h.not_ge (intLexDist_le_one_of_intLexEuclid_eq (Or.inr h2))
  simp [shlosmanProfile, h1, h2]

/-- `|g_{ij}| ≤ 1` for Shlosman's rotator. -/
lemma abs_shlosmanProfile_le_one (i j : ℤ ×ₗ ℤ) (θ : AddCircle (2 * π)) :
    |shlosmanProfile i j θ| ≤ 1 := by
  unfold shlosmanProfile
  split_ifs
  · rw [abs_neg]; exact abs_angle_cos_le_one _
  · rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_angle_cos_le_one _)
  · simp

lemma measurable_shlosmanProfile (i j : ℤ ×ₗ ℤ) : Measurable (shlosmanProfile i j) := by
  unfold shlosmanProfile
  split_ifs
  · exact measurable_angle_cos.neg
  · exact measurable_angle_cos.pow_const 2
  · exact measurable_const

instance isPotential_pair_shlosmanRotor : IsPotential (pair shlosmanRotor) :=
  isPotential_pair_rotorPair measurable_shlosmanProfile

/-- Shlosman's rotator is absolutely summable: it is bounded and of finite range. -/
instance isAbsolutelySummable_pair_shlosmanRotor : IsAbsolutelySummable (pair shlosmanRotor) := by
  refine isAbsolutelySummable_pair (M := fun i j ↦ if intLexDist i j ≤ 1 then 1 else 0)
    (fun i j _ x y ↦ ?_) (fun i j ↦ by rw [isPlanarSiteNorm_int_lex.d_comm]) fun i ↦ ?_
  · by_cases hd : intLexDist i j ≤ 1
    · rw [ite_eq_left hd, ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (abs_shlosmanProfile_le_one i j _)
    · simp [shlosmanRotor, rotorPair, shlosmanProfile_eq_zero_of_one_lt_intLexDist (not_le.1 hd)]
  · have hfin := finite_setOf_dist_le (d := intLexDist) (c₀ := 8) encard_setOf_intLexDist_eq_le i 1
    rw [tsum_eq_sum (s := hfin.toFinset) fun j hj ↦ ?_]
    · exact ENNReal.sum_ne_top.2 fun j _ ↦ by split_ifs <;> simp
    · rw [hfin.mem_toFinset] at hj
      exact ite_eq_right hj

/-- `t ↦ g_{ij}(θ + t)` is `C²` for Shlosman's rotator. -/
lemma contDiff_shlosmanProfile_add (i j : ℤ ×ₗ ℤ) (θ : AddCircle (2 * π)) :
    ContDiff ℝ 2 fun t : ℝ ↦ shlosmanProfile i j (θ + (t : AddCircle (2 * π))) := by
  unfold shlosmanProfile
  split_ifs
  · exact (contDiff_angle_cos_add θ).neg
  · exact (contDiff_angle_cos_add θ).pow 2
  · exact contDiff_const

/-- `|∂²_t cos² (θ + t)| ≤ 2` on the circle, as `cos² u = (1 + cos 2u) / 2`. -/
lemma abs_iteratedDeriv_two_angle_cos_add_sq_le (θ : AddCircle (2 * π)) (t : ℝ) :
    |iteratedDeriv 2 (fun t : ℝ ↦ Real.Angle.cos (θ + (t : AddCircle (2 * π))) ^ 2) t| ≤ 2 := by
  obtain ⟨θ₀, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have : (fun t : ℝ ↦ Real.Angle.cos ((θ₀ : AddCircle (2 * π)) + (t : AddCircle (2 * π))) ^ 2) =
      fun t ↦ 1 / 2 + (1 / 2) * (fun s ↦ Real.cos (2 * θ₀ + s)) (2 * t) := by
    funext t
    have hc : Real.Angle.cos ((θ₀ : AddCircle (2 * π)) + (t : AddCircle (2 * π))) =
        Real.cos (θ₀ + t) := by
      rw [← AddCircle.coe_add]
      exact Real.Angle.cos_coe _
    simp only
    rw [hc, Real.cos_sq, mul_add]
    ring
  rw [this, iteratedDeriv_const_add (by norm_num), iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_smul (f := fun s ↦ Real.cos (2 * θ₀ + s)) (by fun_prop) 2]
  simp only [smul_eq_mul, iteratedDeriv_comp_const_add]
  have h := Real.abs_iteratedDeriv_cos_le_one 2 (2 * θ₀ + 2 * t)
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 ^ 2)]
  nlinarith [abs_nonneg (iteratedDeriv 2 Real.cos (2 * θ₀ + 2 * t))]

/-- `|∂²_t g_{ij}(θ + t)| ≤ 2` for Shlosman's rotator. -/
lemma abs_iteratedDeriv_two_shlosmanProfile_add_le (i j : ℤ ×ₗ ℤ) (θ : AddCircle (2 * π))
    (t : ℝ) :
    |iteratedDeriv 2 (fun t : ℝ ↦ shlosmanProfile i j (θ + (t : AddCircle (2 * π)))) t| ≤ 2 := by
  unfold shlosmanProfile
  split_ifs
  · rw [iteratedDeriv_fun_neg, abs_neg]
    exact (abs_iteratedDeriv_two_angle_cos_add_le θ t).trans (by norm_num)
  · exact abs_iteratedDeriv_two_angle_cos_add_sq_le θ t
  · simp

/-- The hypothesis (ii) of (9.20) for Shlosman's rotator at inverse temperature `β`, with the
coupling `J(i, j) = 2 |β|` between neighbours and `0` otherwise. -/
lemma mul_iteratedDeriv_two_shlosmanProfile_le (β : ℝ) (i j : ℤ ×ₗ ℤ) (θ : AddCircle (2 * π))
    (t : ℝ) :
    β * iteratedDeriv 2 (fun t : ℝ ↦ shlosmanProfile i j (θ + (t : AddCircle (2 * π)))) t ≤
      if intLexDist i j ≤ 1 then 2 * |β| else 0 := by
  split_ifs with hd
  · refine (le_abs_self _).trans ?_
    rw [abs_mul]
    nlinarith [abs_nonneg β, abs_iteratedDeriv_two_shlosmanProfile_add_le i j θ t]
  · simp [shlosmanProfile_eq_zero_of_one_lt_intLexDist (not_le.1 hd)]

/-- **Georgii, Example (9.22)(2).** For every inverse temperature `β`, every Gibbs measure of
Shlosman's rotator on `ℤ²` is invariant under every simultaneous rotation `τ^u` of the spins:
the continuous symmetry is not broken. (The phase transition of this model — the breaking of the
discrete symmetry rotating the even sublattice by `π` — is Georgii's Subsection 18.3.8, not
treated here.) -/
theorem measurePreserving_spinRotation_shlosmanRotor (β : ℝ)
    {μ : Measure (ℤ ×ₗ ℤ → AddCircle (2 * π))}
    (hμ : μ ∈ G (gibbsSpecificationOfAbsolutelySummable (Φ := pair shlosmanRotor)
      AddCircle.haarAddCircle β)) (u : ℝ) :
    MeasurePreserving (pureSpin (ℤ ×ₗ ℤ) (spinRotation u)).toFun μ μ := by
  rw [← gibbsSpecificationOfFiniteReference_eq_of_isProbabilityMeasure,
    gibbsSpecificationOfFiniteReference] at hμ
  set J : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ := fun i j ↦ if intLexDist i j ≤ 1 then 2 * |β| else 0 with hJ
  have hJ0 : ∀ i j, 0 ≤ J i j := fun i j ↦ by
    simp only [hJ]
    split_ifs <;> positivity
  have hJsymm : ∀ i j, J i j = J j i := fun i j ↦ by
    simp only [hJ, isPlanarSiteNorm_int_lex.d_comm i j]
  have hdecay :=
    logDecay_of_finite_range encard_setOf_intLexDist_eq_le hJ0 (M := 2 * |β|) (by positivity)
      (R := 1) (fun i j ↦ by simp only [hJ]; split_ifs <;> first | exact le_rfl | positivity)
      (fun i j hij ↦ by simp only [hJ]; rw [ite_eq_right (not_le.2 hij)])
  exact measurePreserving_spinRotation_rotorPair (g := shlosmanProfile) (J := J) (β := β)
    (isSigmaFiniteLambdaAdmissible_boltzmannFactor _ _)
    (fun i j _ θ ↦ contDiff_shlosmanProfile_add i j θ)
    (fun i j _ θ t ↦ mul_iteratedDeriv_two_shlosmanProfile_le β i j θ t)
    hJ0 hJsymm isPlanarSiteNorm_int_lex hdecay hμ u

end ShlosmanRotor

/-! ### Georgii, Example (9.23): classical Heisenberg models -/

section Heisenberg

open Metric MerminWagner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The unit sphere of a finite-dimensional space is standard Borel (it is compact metrizable). -/
instance : StandardBorelSpace (sphere (0 : V) 1) :=
  have : PolishSpace (sphere (0 : V) 1) := Metric.isClosed_sphere.polishSpace
  inferInstance

/-- The surface measure of the unit sphere of a nontrivial space is non-zero. -/
instance [Nontrivial V] : NeZero (volume : Measure V).toSphere := ⟨Measure.toSphere_ne_zero volume⟩

/-- **Georgii (9.23).** The Heisenberg interaction `φ_{ij}(x, y) = −K(i, j) ⟪x, y⟫` between unit
spins in `V` (Georgii: `ℝ^N`), for a coupling `K : S → S → ℝ`. -/
def heisenbergPair (K : S → S → ℝ) : S → S → sphere (0 : V) 1 → sphere (0 : V) 1 → ℝ :=
  fun i j x y ↦ -K i j * ⟪(x : V), (y : V)⟫

omit [FiniteDimensional ℝ V] in
/-- The Heisenberg interaction is invariant under every simultaneous rotation of the spins. -/
lemma heisenbergPair_sphereMeasurableEquiv (K : S → S → ℝ) (e : V ≃ₗᵢ[ℝ] V) (i j : S)
    (x y : sphere (0 : V) 1) :
    heisenbergPair K i j (e.sphereMeasurableEquiv x) (e.sphereMeasurableEquiv y) =
      heisenbergPair K i j x y := by
  simp [heisenbergPair, LinearIsometryEquiv.inner_map_map]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The Heisenberg interaction is bounded by `|K(i, j)|` on the sphere. -/
lemma enorm_heisenbergPair_le (K : S → S → ℝ) (i j : S) (x y : sphere (0 : V) 1) :
    ‖heisenbergPair K i j x y‖ₑ ≤ ENNReal.ofReal |K i j| := by
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [heisenbergPair, norm_mul, norm_neg, Real.norm_eq_abs]
  calc |K i j| * |⟪(x : V), (y : V)⟫| ≤ |K i j| * (‖(x : V)‖ * ‖(y : V)‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    _ = |K i j| := by
        rw [mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.2, one_mul, mul_one]

variable [LinearOrder S]

instance isPotential_pair_heisenbergPair (K : S → S → ℝ) :
    IsPotential (pair (heisenbergPair (V := V) K)) :=
  isPotential_pair _ fun i j ↦ by
    refine Continuous.measurable ?_
    have : Function.uncurry (heisenbergPair (V := V) K i j) =
        fun p : sphere (0 : V) 1 × sphere (0 : V) 1 ↦ -K i j * ⟪(p.1 : V), (p.2 : V)⟫ := rfl
    rw [this]
    exact continuous_const.mul (Continuous.inner (𝕜 := ℝ)
      (continuous_subtype_val.comp continuous_fst) (continuous_subtype_val.comp continuous_snd))

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The Heisenberg potential is absolutely summable when the coupling is symmetric with finite
row sums `∑_j |K(i, j)| < ∞`. -/
lemma isAbsolutelySummable_pair_heisenbergPair {K : S → S → ℝ} (hK : ∀ i j, K i j = K j i)
    (hsum : ∀ i, ∑' j, ENNReal.ofReal |K i j| ≠ ⊤) :
    IsAbsolutelySummable (pair (heisenbergPair (V := V) K)) :=
  isAbsolutelySummable_pair (fun i j _ x y ↦ enorm_heisenbergPair_le K i j x y)
    (fun i j ↦ by rw [hK]) hsum

omit [FiniteDimensional ℝ V] [LinearOrder S] in
/-- Georgii (9.23): a one-parameter group `R : ℝ → V ≃ₗᵢ[ℝ] V` of rotations acts on the
spins by `τ^t = pureSpin S (R t).sphereMeasurableEquiv`; (9.18) holds. -/
lemma pureSpin_sphereMeasurableEquiv_mul {R : ℝ → V ≃ₗᵢ[ℝ] V}
    (hR : ∀ s t (y : V), R s (R t y) = R (s + t) y) (s t : ℝ) :
    pureSpin S (R s).sphereMeasurableEquiv * pureSpin S (R t).sphereMeasurableEquiv =
      pureSpin S (R (s + t)).sphereMeasurableEquiv :=
  pureSpin_mul_pureSpin (e := fun t ↦ (R t).sphereMeasurableEquiv)
    (fun s t x ↦ Subtype.ext (by simpa using hR s t (x : V))) s t

variable [Countable S]

/-- **Georgii, Theorem (9.20) for Heisenberg models and a one-parameter group of rotations.**
Let `S` be a countable linearly ordered site set with a planar norm, `ν` a σ-finite non-zero
measure on the unit sphere of `V` invariant under the rotations `R_t` of a one-parameter group
`(R_t)_{t ∈ ℝ}` whose orbits `t ↦ R_t y` are `C²` with `‖(R_· y)''‖ ≤ M` on the sphere, and
`Φ = pair (heisenbergPair K)` a `ν`-admissible Heisenberg potential with
`|β| |K(i, j)| M ≤ J(i, j)` for a symmetric `J ≥ 0` satisfying (9.21). Then every `μ ∈ 𝒢(βΦ)`
is invariant under every `R_u`. -/
theorem measurePreserving_sphereRotation_heisenbergPair {K : S → S → ℝ}
    [IsSummable (pair (heisenbergPair (V := V) K))] {β : ℝ} (ν : Measure (sphere (0 : V) 1))
    [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := sphere (0 : V) 1) ν
      ((pair (heisenbergPair K)).boltzmannFactor β))
    {R : ℝ → V ≃ₗᵢ[ℝ] V} (hR : ∀ s t (y : V), R s (R t y) = R (s + t) y)
    (hν : ∀ t, MeasurePreserving (R t).sphereMeasurableEquiv ν ν)
    (hsmooth : ∀ y : V, ContDiff ℝ 2 fun t ↦ R t y) {M : ℝ}
    (hM : ∀ y : V, ‖y‖ = 1 → ∀ t, ‖iteratedDeriv 2 (fun t ↦ R t y) t‖ ≤ M)
    {J : S → S → ℝ} (hJ : ∀ i j, i < j → |β| * |K i j| * M ≤ J i j)
    (hJ0 : ∀ i j, 0 ≤ J i j) (hJsymm : ∀ i j, J i j = J j i)
    {nrm : S → ℕ} {d : S → S → ℕ} {c₀ : ℕ} (hgeo : IsPlanarSiteNorm nrm d c₀)
    {K₁ : ℝ} (hdecay : LogDecay d J K₁) {μ : Measure (S → sphere (0 : V) 1)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (heisenbergPair K)) ν β hadm))
    (u : ℝ) :
    MeasurePreserving (pureSpin S (R u).sphereMeasurableEquiv).toFun μ μ := by
  have horbit : ∀ i j (x y : sphere (0 : V) 1),
      (fun t : ℝ ↦ heisenbergPair K i j x ((R t).sphereMeasurableEquiv y)) =
        fun t ↦ -K i j * ⟪(x : V), R t y⟫ := by
    intro i j x y
    funext t
    simp [heisenbergPair]
  refine measurePreserving_of_logDecay (τ := fun t ↦ pureSpin S (R t).sphereMeasurableEquiv) ν
    hadm (fun _ ↦ isPureSpin_pureSpin _) (pureSpin_sphereMeasurableEquiv_mul hR)
    (fun t _ ↦ hν t) (fun t i j _ x y ↦ heisenbergPair_sphereMeasurableEquiv K (R t) i j x y)
    (fun i j hij x y ↦ ?_) (fun i j hij x y t ↦ ?_) hJ0 hJsymm hgeo hdecay hμ u
  · simp only [pureSpin_spin]
    rw [horbit]
    exact contDiff_const.mul (contDiff_const.inner ℝ (hsmooth y))
  · simp only [pureSpin_spin]
    rw [horbit, iteratedDeriv_const_mul _ (contDiff_const.inner ℝ (hsmooth y)).contDiffAt,
      iteratedDeriv_inner_const_left (hsmooth y).contDiffAt]
    refine le_trans (le_abs_self _) ((abs_mul _ _).le.trans ?_)
    rw [abs_mul, abs_neg]
    calc |β| * (|K i j| * |⟪(x : V), iteratedDeriv 2 (fun t ↦ R t y) t⟫|)
        ≤ |β| * (|K i j| * (‖(x : V)‖ * ‖iteratedDeriv 2 (fun t ↦ R t y) t‖)) := by
          gcongr
          exact abs_real_inner_le_norm _ _
      _ ≤ |β| * (|K i j| * (1 * M)) := by
          gcongr
          · exact (mem_sphere_zero_iff_norm.1 x.2).le
          · exact hM y (mem_sphere_zero_iff_norm.1 y.2) t
      _ = |β| * |K i j| * M := by ring
      _ ≤ J i j := hJ i j hij

/-- **Georgii, Theorem (9.20) for Heisenberg models with couplings `|K(i, j)| ≤ K₀ / d(i, j)⁴`**
(Georgii's `|K(i, j)| ≤ K |i − j|^{-p}`, `p ≥ 4`, after `|i − j|^{-p} ≤ ‖i − j‖_∞^{-4}`), for a
one-parameter group of rotations with `C²` orbits and `‖(R_· y)''‖ ≤ M` on the sphere: every
`μ ∈ 𝒢(βΦ)` is invariant under every `R_u`. The coupling of (9.21) is
`J(i, j) = |β| |K(i, j)| M ≤ |β| K₀ M / d(i, j)⁴`. -/
theorem measurePreserving_sphereRotation_heisenbergPair_of_le_div_pow_four {K : S → S → ℝ}
    [IsSummable (pair (heisenbergPair (V := V) K))] {β : ℝ} (ν : Measure (sphere (0 : V) 1))
    [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := sphere (0 : V) 1) ν
      ((pair (heisenbergPair K)).boltzmannFactor β))
    {R : ℝ → V ≃ₗᵢ[ℝ] V} (hR : ∀ s t (y : V), R s (R t y) = R (s + t) y)
    (hν : ∀ t, MeasurePreserving (R t).sphereMeasurableEquiv ν ν)
    (hsmooth : ∀ y : V, ContDiff ℝ 2 fun t ↦ R t y) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y : V, ‖y‖ = 1 → ∀ t, ‖iteratedDeriv 2 (fun t ↦ R t y) t‖ ≤ M)
    {d : S → S → ℕ} {c₀ : ℕ}
    (hshell : ∀ i m, {j | d i j = m}.encard ≤ (c₀ * (m + 1) : ℕ))
    {nrm : S → ℕ} (hgeo : IsPlanarSiteNorm nrm d c₀)
    (hKsymm : ∀ i j, K i j = K j i) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ i j, 0 < d i j → |K i j| ≤ K₀ / (d i j : ℝ) ^ 4)
    {μ : Measure (S → sphere (0 : V) 1)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (heisenbergPair K)) ν β hadm))
    (u : ℝ) :
    MeasurePreserving (pureSpin S (R u).sphereMeasurableEquiv).toFun μ μ := by
  set J : S → S → ℝ := fun i j ↦ |β| * |K i j| * M with hJdef
  have hJ0 : ∀ i j, 0 ≤ J i j := fun i j ↦ by positivity
  have hJsymm : ∀ i j, J i j = J j i := fun i j ↦ by simp only [hJdef, hKsymm i j]
  have hdecay : LogDecay d J (5 * c₀ * (|β| * K₀ * M)) := by
    refine logDecay_of_le_div_pow_four hshell hJ0 (by positivity) fun i j hij ↦ ?_
    simp only [hJdef]
    calc |β| * |K i j| * M ≤ |β| * (K₀ / (d i j : ℝ) ^ 4) * M := by
          gcongr
          exact hK i j hij
      _ = |β| * K₀ * M / (d i j : ℝ) ^ 4 := by ring
  exact measurePreserving_sphereRotation_heisenbergPair ν hadm hR hν hsmooth hM (J := J)
    (fun i j _ ↦ le_rfl) hJ0 hJsymm hgeo hdecay hμ u

/-- **Georgii, Example (9.23), the one-parameter groups `exp (t A)`.** For a skew-adjoint `A`
(Georgii's `M(t r₁, …, t rₙ)`), every `μ ∈ 𝒢(βΦ)` of a `ν`-admissible Heisenberg potential with
`|K(i, j)| ≤ K₀ / d(i, j)⁴` is invariant under every rotation `exp (u A)`; in particular under
`exp A` (`u = 1`). -/
theorem measurePreserving_sphereRotation_expRotation_heisenbergPair {K : S → S → ℝ}
    [IsSummable (pair (heisenbergPair (V := V) K))] {β : ℝ} (ν : Measure (sphere (0 : V) 1))
    [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := sphere (0 : V) 1) ν
      ((pair (heisenbergPair K)).boltzmannFactor β))
    (hν : ∀ e : V ≃ₗᵢ[ℝ] V, MeasurePreserving e.sphereMeasurableEquiv ν ν)
    {d : S → S → ℕ} {c₀ : ℕ}
    (hshell : ∀ i m, {j | d i j = m}.encard ≤ (c₀ * (m + 1) : ℕ))
    {nrm : S → ℕ} (hgeo : IsPlanarSiteNorm nrm d c₀)
    (hKsymm : ∀ i j, K i j = K j i) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ i j, 0 < d i j → |K i j| ≤ K₀ / (d i j : ℝ) ^ 4)
    {A : V →L[ℝ] V} (hA : A ∈ skewAdjoint (V →L[ℝ] V)) {μ : Measure (S → sphere (0 : V) 1)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (heisenbergPair K)) ν β hadm))
    (u : ℝ) :
    MeasurePreserving (pureSpin S (skewAdjoint.expRotation hA u).sphereMeasurableEquiv).toFun
      μ μ :=
  measurePreserving_sphereRotation_heisenbergPair_of_le_div_pow_four ν hadm
    (skewAdjoint.expRotation_add hA) (fun t ↦ hν _) (skewAdjoint.contDiff_expRotation_apply hA 2)
    (M := ‖A‖ ^ 2) (by positivity)
    (fun y hy t ↦ by
      simpa [hy] using skewAdjoint.norm_iteratedDeriv_two_expRotation_apply_le hA t y)
    hshell hgeo hKsymm hK₀ hK hμ u

/-! #### `N = 2`: the full rotation group `SO(2)` -/

section TwoDim

variable [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Georgii (9.23) for `N = 2`: the one-parameter group `t ↦ M(θ t)` of rotations by the angles
`θ t` (Mathlib's `Orientation.rotation`). -/
def rotationOneParam (θ t : ℝ) : V ≃ₗᵢ[ℝ] V := o.rotation ((θ * t : ℝ) : Real.Angle)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The rotations `M(θ t)` form a one-parameter group. -/
lemma rotationOneParam_add (θ s t : ℝ) (y : V) :
    rotationOneParam o θ s (rotationOneParam o θ t y) = rotationOneParam o θ (s + t) y := by
  simp only [rotationOneParam, Orientation.rotation_rotation, mul_add, Real.Angle.coe_add]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The orbit of `y` under the rotations: `M(θ t) y = cos (θ t) y + sin (θ t) J y`. -/
lemma rotationOneParam_orbit (θ : ℝ) (y : V) :
    (fun t ↦ rotationOneParam o θ t y) =
      fun t ↦ (fun s ↦ Real.cos s • y + Real.sin s • o.rightAngleRotation y) (θ * t) := by
  funext t
  simp [rotationOneParam, Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma contDiff_cos_smul_add_sin_smul (y : V) (n : WithTop ℕ∞) :
    ContDiff ℝ n fun s : ℝ ↦ Real.cos s • y + Real.sin s • o.rightAngleRotation y :=
  (Real.contDiff_cos.smul contDiff_const).add (Real.contDiff_sin.smul contDiff_const)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The orbits of the rotation group are smooth. -/
lemma contDiff_rotationOneParam_apply (θ : ℝ) (y : V) :
    ContDiff ℝ 2 fun t ↦ rotationOneParam o θ t y := by
  rw [rotationOneParam_orbit]
  exact (contDiff_cos_smul_add_sin_smul o y 2).comp (contDiff_const.mul contDiff_id)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Georgii (9.23): `|∂²_t (M(θ t) y)| ≤ 2 θ² ‖y‖` (Georgii's `max r_i²`, up to the factor `2`). -/
lemma norm_iteratedDeriv_two_rotationOneParam_apply_le (θ : ℝ) (y : V) (t : ℝ) :
    ‖iteratedDeriv 2 (fun t ↦ rotationOneParam o θ t y) t‖ ≤ 2 * θ ^ 2 * ‖y‖ := by
  rw [rotationOneParam_orbit, iteratedDeriv_comp_const_smul (contDiff_cos_smul_add_sin_smul o y 2)]
  simp only
  have h1 : ContDiff ℝ 2 fun s : ℝ ↦ Real.cos s • y := Real.contDiff_cos.smul contDiff_const
  have h2 : ContDiff ℝ 2 fun s : ℝ ↦ Real.sin s • o.rightAngleRotation y :=
    Real.contDiff_sin.smul contDiff_const
  rw [iteratedDeriv_fun_add (f := fun s : ℝ ↦ Real.cos s • y)
      (g := fun s : ℝ ↦ Real.sin s • o.rightAngleRotation y) h1.contDiffAt h2.contDiffAt,
    iteratedDeriv_smul_const Real.contDiff_cos.contDiffAt,
    iteratedDeriv_smul_const Real.contDiff_sin.contDiffAt, norm_smul, Real.norm_eq_abs, abs_pow]
  have hc := Real.abs_iteratedDeriv_cos_le_one 2 (θ * t)
  have hs := Real.abs_iteratedDeriv_sin_le_one 2 (θ * t)
  have hJ : ‖o.rightAngleRotation y‖ = ‖y‖ := LinearIsometryEquiv.norm_map _ y
  calc |θ| ^ 2 * ‖iteratedDeriv 2 Real.cos (θ * t) • y +
        iteratedDeriv 2 Real.sin (θ * t) • o.rightAngleRotation y‖
      ≤ |θ| ^ 2 * (‖iteratedDeriv 2 Real.cos (θ * t) • y‖ +
        ‖iteratedDeriv 2 Real.sin (θ * t) • o.rightAngleRotation y‖) := by
        gcongr
        exact norm_add_le _ _
    _ = |θ| ^ 2 * (|iteratedDeriv 2 Real.cos (θ * t)| * ‖y‖ +
        |iteratedDeriv 2 Real.sin (θ * t)| * ‖y‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hJ]
    _ ≤ |θ| ^ 2 * (1 * ‖y‖ + 1 * ‖y‖) := by gcongr
    _ = 2 * θ ^ 2 * ‖y‖ := by rw [sq_abs]; ring

end TwoDim

/-! #### Plane rotations in any dimension: the full rotation group `SO(N)`

Georgii embeds a rotation `r ∈ SO(N)` into a one-parameter subgroup through the real normal form
`M(r₁, …, rₙ)` of an orthogonal matrix. Here `r` is instead written as a product of *plane
rotations* — rotations of two-dimensional subspaces `K` extended by the identity on `Kᗮ`
(`Submodule.orthogonalExtend`), each of which is the time-one map of the one-parameter group
`M(θ t)` of the plane — by the Cartan–Dieudonné theorem
(`LinearIsometryEquiv.exists_list_orthogonalExtend_rotation_prod_of_det_pos`); invariance under
`r` then follows from invariance under each factor. -/

section PlaneRotation

variable (K : Submodule ℝ V) [Fact (Module.finrank ℝ K = 2)] (o : Orientation ℝ K (Fin 2))

/-- The one-parameter group of rotations `M(θ t)` of the plane `K`, extended by the identity
on `Kᗮ`. -/
def planeRotationOneParam (θ t : ℝ) : V ≃ₗᵢ[ℝ] V :=
  K.orthogonalExtend (rotationOneParam o θ t)

omit [MeasurableSpace V] [BorelSpace V] in
/-- The plane rotations `M(θ t)` form a one-parameter group. -/
lemma planeRotationOneParam_add (θ s t : ℝ) (y : V) :
    planeRotationOneParam K o θ s (planeRotationOneParam K o θ t y) =
      planeRotationOneParam K o θ (s + t) y := by
  unfold planeRotationOneParam
  rw [← LinearIsometryEquiv.trans_apply, K.orthogonalExtend_trans]
  congr 2
  exact LinearIsometryEquiv.ext fun y ↦ rotationOneParam_add o θ s t y

omit [MeasurableSpace V] [BorelSpace V] in
/-- The orbit of `y` under the plane rotations: the orbit of the projection of `y` on `K` under
`M(θ t)`, shifted by the projection of `y` on `Kᗮ`. -/
lemma planeRotationOneParam_orbit (θ : ℝ) (y : V) :
    (fun t ↦ planeRotationOneParam K o θ t y) =
      fun t ↦ K.subtypeL (rotationOneParam o θ t (K.orthogonalProjectionOnto y)) +
        Kᗮ.starProjection y := by
  funext t
  simp [planeRotationOneParam]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The orbits of the plane rotations are smooth. -/
lemma contDiff_planeRotationOneParam_apply (θ : ℝ) (y : V) :
    ContDiff ℝ 2 fun t ↦ planeRotationOneParam K o θ t y := by
  rw [planeRotationOneParam_orbit]
  exact (K.subtypeL.contDiff.comp (contDiff_rotationOneParam_apply o θ _)).add contDiff_const

omit [MeasurableSpace V] [BorelSpace V] in
/-- `|∂²_t (M(θ t) y)| ≤ 2 θ² ‖y‖` for the plane rotations. -/
lemma norm_iteratedDeriv_two_planeRotationOneParam_apply_le (θ : ℝ) (y : V) (t : ℝ) :
    ‖iteratedDeriv 2 (fun t ↦ planeRotationOneParam K o θ t y) t‖ ≤ 2 * θ ^ 2 * ‖y‖ := by
  have horb : ContDiff ℝ 2 fun t ↦ K.subtypeL (rotationOneParam o θ t
      (K.orthogonalProjectionOnto y)) :=
    K.subtypeL.contDiff.comp (contDiff_rotationOneParam_apply o θ _)
  rw [planeRotationOneParam_orbit,
    iteratedDeriv_fun_add (f := fun t ↦ K.subtypeL (rotationOneParam o θ t
      (K.orthogonalProjectionOnto y))) (g := fun _ ↦ Kᗮ.starProjection y) horb.contDiffAt
      contDiff_const.contDiffAt,
    iteratedDeriv_const, ite_eq_right (by norm_num), add_zero]
  change ‖iteratedDeriv 2 (K.subtypeL ∘ fun t ↦ rotationOneParam o θ t
    (K.orthogonalProjectionOnto y)) t‖ ≤ _
  rw [K.subtypeL.iteratedDeriv_comp_left (contDiff_rotationOneParam_apply o θ _).contDiffAt,
    Submodule.coe_subtypeL, Submodule.coe_subtype, Submodule.norm_coe]
  calc ‖iteratedDeriv 2 (fun t ↦ rotationOneParam o θ t (K.orthogonalProjectionOnto y)) t‖
      ≤ 2 * θ ^ 2 * ‖K.orthogonalProjectionOnto y‖ :=
        norm_iteratedDeriv_two_rotationOneParam_apply_le o θ _ t
    _ ≤ 2 * θ ^ 2 * ‖y‖ := by
        gcongr
        exact K.norm_orthogonalProjectionOnto_apply_le y

/-- **Georgii, Example (9.23), plane rotations.** Every `μ ∈ 𝒢(βΦ)` of a `ν`-admissible
Heisenberg potential with `|K(i, j)| ≤ K₀ / d(i, j)⁴` is invariant under the rotation by any
angle `θ` of any plane `K ≤ V`, extended by the identity on `Kᗮ`: this rotation is the time-one
map of the one-parameter group `M(θ t)` of the plane. -/
theorem measurePreserving_sphereRotation_orthogonalExtend_rotation_heisenbergPair
    {K' : S → S → ℝ} [IsSummable (pair (heisenbergPair (V := V) K'))] {β : ℝ}
    (ν : Measure (sphere (0 : V) 1)) [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := sphere (0 : V) 1) ν
      ((pair (heisenbergPair K')).boltzmannFactor β))
    (hν : ∀ e : V ≃ₗᵢ[ℝ] V, MeasurePreserving e.sphereMeasurableEquiv ν ν)
    {d : S → S → ℕ} {c₀ : ℕ}
    (hshell : ∀ i m, {j | d i j = m}.encard ≤ (c₀ * (m + 1) : ℕ))
    {nrm : S → ℕ} (hgeo : IsPlanarSiteNorm nrm d c₀)
    (hKsymm : ∀ i j, K' i j = K' j i) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ i j, 0 < d i j → |K' i j| ≤ K₀ / (d i j : ℝ) ^ 4) (θ : Real.Angle)
    {μ : Measure (S → sphere (0 : V) 1)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (heisenbergPair K')) ν β hadm)) :
    MeasurePreserving
      (pureSpin S (K.orthogonalExtend (o.rotation θ)).sphereMeasurableEquiv).toFun μ μ := by
  induction θ using Real.Angle.induction_on with
  | h θ₀ =>
    have hr : K.orthogonalExtend (o.rotation θ₀) = planeRotationOneParam K o θ₀ 1 := by
      rw [planeRotationOneParam, rotationOneParam, mul_one]
    rw [hr]
    exact measurePreserving_sphereRotation_heisenbergPair_of_le_div_pow_four ν hadm
      (planeRotationOneParam_add K o θ₀) (fun t ↦ hν _)
      (contDiff_planeRotationOneParam_apply K o θ₀) (M := 2 * θ₀ ^ 2) (by positivity)
      (fun y hy t ↦ by
        simpa [hy] using norm_iteratedDeriv_two_planeRotationOneParam_apply_le K o θ₀ y t)
      hshell hgeo hKsymm hK₀ hK hμ 1

end PlaneRotation

omit [FiniteDimensional ℝ V] [LinearOrder S] [Countable S] in
/-- Invariance under simultaneous rotations of the spins is closed under products of rotations.
-/
lemma measurePreserving_pureSpin_sphereMeasurableEquiv_mul {μ : Measure (S → sphere (0 : V) 1)}
    {e f : V ≃ₗᵢ[ℝ] V} (he : MeasurePreserving (pureSpin S e.sphereMeasurableEquiv).toFun μ μ)
    (hf : MeasurePreserving (pureSpin S f.sphereMeasurableEquiv).toFun μ μ) :
    MeasurePreserving (pureSpin S (e * f).sphereMeasurableEquiv).toFun μ μ := by
  rw [LinearIsometryEquiv.mul_def, ← LinearIsometryEquiv.sphereMeasurableEquiv_trans,
    ← pureSpin_mul, Transformation.mul_def]
  have : ((pureSpin S e.sphereMeasurableEquiv).comp (pureSpin S f.sphereMeasurableEquiv)).toFun =
      (pureSpin S e.sphereMeasurableEquiv).toFun ∘ (pureSpin S f.sphereMeasurableEquiv).toFun :=
    funext (Transformation.comp_toFun _ _)
  rw [this]
  exact he.comp hf

omit [FiniteDimensional ℝ V] [LinearOrder S] [Countable S] in
/-- Invariance under the trivial rotation. -/
lemma measurePreserving_pureSpin_sphereMeasurableEquiv_one {μ : Measure (S → sphere (0 : V) 1)} :
    MeasurePreserving (pureSpin S (1 : V ≃ₗᵢ[ℝ] V).sphereMeasurableEquiv).toFun μ μ := by
  rw [LinearIsometryEquiv.one_def, LinearIsometryEquiv.sphereMeasurableEquiv_refl, pureSpin_refl]
  exact MeasurePreserving.id μ

omit [FiniteDimensional ℝ V] [LinearOrder S] [Countable S] in
/-- Invariance under simultaneous rotations of the spins is closed under products of lists of
rotations. -/
lemma measurePreserving_pureSpin_sphereMeasurableEquiv_list_prod
    {μ : Measure (S → sphere (0 : V) 1)} (L : List (V ≃ₗᵢ[ℝ] V))
    (hL : ∀ e ∈ L, MeasurePreserving (pureSpin S e.sphereMeasurableEquiv).toFun μ μ) :
    MeasurePreserving (pureSpin S L.prod.sphereMeasurableEquiv).toFun μ μ := by
  induction L with
  | nil => exact measurePreserving_pureSpin_sphereMeasurableEquiv_one
  | cons e L ih =>
    rw [List.prod_cons]
    exact measurePreserving_pureSpin_sphereMeasurableEquiv_mul (hL e (by simp))
      (ih fun f hf ↦ hL f (by simp [hf]))

/-- **Georgii, Example (9.23), in full: the `SO(N)`-symmetry is not broken.** Every `μ ∈ 𝒢(βΦ)`
of a `ν`-admissible Heisenberg potential on a finite-dimensional `V` (Georgii: `ℝ^N`, `N ≥ 2`)
with `|K(i, j)| ≤ K₀ / d(i, j)⁴` is invariant under the simultaneous rotation of all spins by
every `r ∈ SO(N)`, i.e. every linear isometric equivalence `r` of `V` of positive determinant:
`r` is a product of plane rotations
(`LinearIsometryEquiv.exists_list_orthogonalExtend_rotation_prod_of_det_pos`), each the time-one
map of a one-parameter group of rotations. -/
theorem measurePreserving_sphereRotation_of_det_pos_heisenbergPair {K : S → S → ℝ}
    [IsSummable (pair (heisenbergPair (V := V) K))] {β : ℝ} (ν : Measure (sphere (0 : V) 1))
    [SigmaFinite ν] [NeZero ν]
    (hadm : Specification.IsSigmaFiniteLambdaAdmissible (S := S) (E := sphere (0 : V) 1) ν
      ((pair (heisenbergPair K)).boltzmannFactor β))
    (hν : ∀ e : V ≃ₗᵢ[ℝ] V, MeasurePreserving e.sphereMeasurableEquiv ν ν)
    {d : S → S → ℕ} {c₀ : ℕ}
    (hshell : ∀ i m, {j | d i j = m}.encard ≤ (c₀ * (m + 1) : ℕ))
    {nrm : S → ℕ} (hgeo : IsPlanarSiteNorm nrm d c₀)
    (hKsymm : ∀ i j, K i j = K j i) {K₀ : ℝ} (hK₀ : 0 ≤ K₀)
    (hK : ∀ i j, 0 < d i j → |K i j| ≤ K₀ / (d i j : ℝ) ^ 4)
    {r : V ≃ₗᵢ[ℝ] V} (hr : 0 < LinearMap.det (r.toLinearEquiv : V →ₗ[ℝ] V))
    {μ : Measure (S → sphere (0 : V) 1)}
    (hμ : μ ∈ G (gibbsSpecificationOfSigmaFiniteAdmissible (pair (heisenbergPair K)) ν β hadm)) :
    MeasurePreserving (pureSpin S r.sphereMeasurableEquiv).toFun μ μ := by
  obtain ⟨L, hL, rfl⟩ :=
    LinearIsometryEquiv.exists_list_orthogonalExtend_rotation_prod_of_det_pos hr
  refine measurePreserving_pureSpin_sphereMeasurableEquiv_list_prod L fun g hg ↦ ?_
  obtain ⟨W, hW, o, θ, rfl⟩ := hL g hg
  exact measurePreserving_sphereRotation_orthogonalExtend_rotation_heisenbergPair W o ν hadm hν
    hshell hgeo hKsymm hK₀ hK θ hμ

/-! #### Georgii's setting: `ℤ²`, the surface measure, `|K(i, j)| ≤ K |i − j|^{-p}` -/

section IntLex

variable [Nontrivial V]

/-- `‖i − j‖_∞^{-p} ≤ 1 / ‖i − j‖_∞⁴` for `p ≥ 4` and `i ≠ j`. -/
lemma intLexDist_rpow_neg_le_one_div_pow_four {p : ℝ} (hp : 4 ≤ p) {i j : ℤ ×ₗ ℤ}
    (hij : i ≠ j) : (intLexDist i j : ℝ) ^ (-p) ≤ 1 / (intLexDist i j : ℝ) ^ 4 := by
  have h1 : (1 : ℝ) ≤ intLexDist i j := by exact_mod_cast one_le_intLexDist_of_ne hij
  calc (intLexDist i j : ℝ) ^ (-p) ≤ (intLexDist i j : ℝ) ^ (-(4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = 1 / (intLexDist i j : ℝ) ^ 4 := by
        rw [Real.rpow_neg (by linarith), one_div]
        norm_cast

omit [FiniteDimensional ℝ V] [BorelSpace V] [Nontrivial V] in
/-- **Georgii (9.23)**: a symmetric coupling with `|K(i, j)| ≤ K₀ |i − j|^{-p}`, `p > 2`, gives an
absolutely summable Heisenberg potential on `ℤ²`. -/
theorem isAbsolutelySummable_pair_heisenbergPair_int_lex {K : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ}
    (hKsymm : ∀ i j, K i j = K j i) {K₀ p : ℝ} (hK₀ : 0 ≤ K₀) (hp : 2 < p)
    (hK : ∀ i j, i ≠ j → |K i j| ≤ K₀ * intLexEuclid i j ^ (-p)) :
    IsAbsolutelySummable (pair (heisenbergPair (V := V) K)) := by
  refine isAbsolutelySummable_pair_heisenbergPair hKsymm fun i ↦ ?_
  have hle : ∀ j, ENNReal.ofReal |K i j| ≤
      ENNReal.ofReal K₀ * ENNReal.ofReal ((intLexDist i j : ℝ) ^ (-p)) +
        (if j = i then ENNReal.ofReal |K i i| else 0) := by
    intro j
    by_cases hij : j = i
    · subst hij
      simp
    · rw [ite_eq_right hij, add_zero, ← ENNReal.ofReal_mul hK₀]
      refine ENNReal.ofReal_le_ofReal ((hK i j (Ne.symm hij)).trans ?_)
      exact mul_le_mul_of_nonneg_left (intLexEuclid_rpow_neg_le (by linarith) (Ne.symm hij)) hK₀
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, tsum_ite_eq]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tsum_ofReal_intLexDist_rpow_neg_ne_top hp i), ENNReal.ofReal_ne_top⟩

/-- Georgii's coupling bound `|K(i, j)| ≤ K₀ |i − j|^{-p}`, `p ≥ 4`, implies
`|K(i, j)| ≤ K₀ / ‖i − j‖_∞⁴`. -/
lemma abs_le_div_pow_four_of_le_intLexEuclid_rpow {K : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ} {K₀ p : ℝ}
    (hK₀ : 0 ≤ K₀) (hp : 4 ≤ p) (hK : ∀ i j, i ≠ j → |K i j| ≤ K₀ * intLexEuclid i j ^ (-p))
    (i j : ℤ ×ₗ ℤ) (hd : 0 < intLexDist i j) : |K i j| ≤ K₀ / (intLexDist i j : ℝ) ^ 4 := by
  have hij := ne_of_intLexDist_pos hd
  calc |K i j| ≤ K₀ * intLexEuclid i j ^ (-p) := hK i j hij
    _ ≤ K₀ * (1 / (intLexDist i j : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left ((intLexEuclid_rpow_neg_le (by linarith) hij).trans
          (intLexDist_rpow_neg_le_one_div_pow_four hp hij)) hK₀
    _ = K₀ / (intLexDist i j : ℝ) ^ 4 := by ring

/-- **Georgii, Example (9.23) on `ℤ²`, one-parameter subgroups.** Let `K` be symmetric with
`|K(i, j)| ≤ K₀ |i − j|^{-p}`, `p ≥ 4`, and `λ` the surface measure of the unit sphere. Then
every `μ ∈ 𝒢(βΦ)` is invariant under the simultaneous rotation of all spins by `exp (u A)`, for
every skew-adjoint `A` and every `u`. -/
theorem measurePreserving_sphereRotation_expRotation_heisenbergPair_int_lex
    {K : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ} (hKsymm : ∀ i j, K i j = K j i) {K₀ p : ℝ} (hK₀ : 0 ≤ K₀)
    (hp : 4 ≤ p) (hK : ∀ i j, i ≠ j → |K i j| ≤ K₀ * intLexEuclid i j ^ (-p)) (β : ℝ)
    {A : V →L[ℝ] V} (hA : A ∈ skewAdjoint (V →L[ℝ] V))
    {μ : Measure (ℤ ×ₗ ℤ → sphere (0 : V) 1)}
    (hμ : haveI := isAbsolutelySummable_pair_heisenbergPair_int_lex (V := V) hKsymm hK₀
                     (by linarith : 2 < p) hK
          μ ∈ G (gibbsSpecificationOfFiniteReference (pair (heisenbergPair K)) volume.toSphere β))
    (u : ℝ) :
    MeasurePreserving
      (pureSpin (ℤ ×ₗ ℤ) (skewAdjoint.expRotation hA u).sphereMeasurableEquiv).toFun μ μ := by
  have := isAbsolutelySummable_pair_heisenbergPair_int_lex (V := V) hKsymm hK₀
    (by linarith : 2 < p) hK
  unfold gibbsSpecificationOfFiniteReference at hμ
  have h := measurePreserving_sphereRotation_expRotation_heisenbergPair (S := ℤ ×ₗ ℤ) (K := K)
    (β := β) (volume : Measure V).toSphere (isSigmaFiniteLambdaAdmissible_boltzmannFactor _ _)
    (fun e ↦ e.measurePreserving_sphere_toSphere_volume) encard_setOf_intLexDist_eq_le
    isPlanarSiteNorm_int_lex hKsymm hK₀ (abs_le_div_pow_four_of_le_intLexEuclid_rpow hK₀ hp hK)
    hA (μ := μ)
  exact h hμ u

/-- **Georgii, Example (9.23) on `ℤ²`, in full.** Let `V` be a finite-dimensional real inner
product space (Georgii: `ℝ^N`, `N ≥ 2`), `K` symmetric with `|K(i, j)| ≤ K₀ |i − j|^{-p}`,
`p ≥ 4`, and `λ` the surface measure of the unit sphere. Then every `μ ∈ 𝒢(βΦ)` is invariant
under the simultaneous rotation of all spins by every `r ∈ SO(N)`: the `SO(N)`-symmetry is not
broken. -/
theorem measurePreserving_sphereRotation_of_det_pos_heisenbergPair_int_lex
    {K : ℤ ×ₗ ℤ → ℤ ×ₗ ℤ → ℝ} (hKsymm : ∀ i j, K i j = K j i) {K₀ p : ℝ} (hK₀ : 0 ≤ K₀)
    (hp : 4 ≤ p) (hK : ∀ i j, i ≠ j → |K i j| ≤ K₀ * intLexEuclid i j ^ (-p)) (β : ℝ)
    {r : V ≃ₗᵢ[ℝ] V} (hr : 0 < LinearMap.det (r.toLinearEquiv : V →ₗ[ℝ] V))
    {μ : Measure (ℤ ×ₗ ℤ → sphere (0 : V) 1)}
    (hμ : haveI := isAbsolutelySummable_pair_heisenbergPair_int_lex (V := V) hKsymm hK₀
                     (by linarith : 2 < p) hK
          μ ∈ G (gibbsSpecificationOfFiniteReference (pair (heisenbergPair K)) volume.toSphere β)) :
    MeasurePreserving (pureSpin (ℤ ×ₗ ℤ) r.sphereMeasurableEquiv).toFun μ μ := by
  have := isAbsolutelySummable_pair_heisenbergPair_int_lex (V := V) hKsymm hK₀
    (by linarith : 2 < p) hK
  unfold gibbsSpecificationOfFiniteReference at hμ
  have h := measurePreserving_sphereRotation_of_det_pos_heisenbergPair (S := ℤ ×ₗ ℤ) (K := K)
    (β := β) (volume : Measure V).toSphere (isSigmaFiniteLambdaAdmissible_boltzmannFactor _ _)
    (fun e ↦ e.measurePreserving_sphere_toSphere_volume) encard_setOf_intLexDist_eq_le
    isPlanarSiteNorm_int_lex hKsymm hK₀ (abs_le_div_pow_four_of_le_intLexEuclid_rpow hK₀ hp hK)
    hr (μ := μ)
  exact h hμ

end IntLex

end Heisenberg



end MeasureTheory.GibbsMeasure

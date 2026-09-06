/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AnisotropicAntiferroOceans

/-!
# Georgii 18.3.8: Shlosman's plane rotor model

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.8.  The state space is the circle, the a
priori measure is the uniform one, and the `C`-potential is **(18.36)**

`Φ_C = -∑_{{i,j} ⊆ C, |i-j|=√2} cos(σ_i - σ_j) + J ∑_{{i,j} ⊆ C, |i-j|=1} cos²(σ_i - σ_j)`,
`J > 0`.

Georgii writes `E = [0, 2π[` with addition mod `2π`.  Here the circle is the **unit circle of an
oriented two-dimensional real inner product space** `V`, the a priori measure is the normalised
arc length `sphereProb V` of `GibbsMeasure/Model/HeisenbergOceans.lean`, and Georgii's
`cos(σ_i - σ_j)` is the inner product `⟪σ_i, σ_j⟫`.  This is the same model — the isomorphism
`AddCircle (2π) ≃ sphere (0 : V) 1`, `θ ↦ (cos θ, sin θ)`, carries the uniform measure to the
normalised arc length and `cos(θ - θ')` to `⟪·,·⟫` — written in the ontology in which the rest
of §18.3 is formalised, so that the sphere's measure-theoretic instances
(`StandardBorelSpace`, `IsOpenPosMeasure`, compactness, measure preservation under linear
isometries) are available.  Shlosman's rotator appears in
`GibbsMeasure/Model/MerminWagnerExamples.lean` as `shlosmanRotor = rotorPair shlosmanProfile`,
Georgii's Example (9.22)(2): that is the same interaction *as a pair potential on `ℤ²`*, with
`E = AddCircle (2π)` and coupling `J = 1`, used there for the Mermin-Wagner theorem (9.20).  The
`C`-potential (18.36) is a different object — the equivalent `C`-potential of Comment (17.19)(2)
— so neither file can be expressed in terms of the other; the *profile* `shlosmanProfile` is
not duplicated here, since here the interaction is written with the inner product instead of the
cosine.

## The orientation

The two classes of local ground states of (18.36) are distinguished by the **sense of rotation**
from the even to the odd sublattice, so an orientation of `V` is part of the data: the classes
are exchanged by a reflection, and only after an orientation is chosen can they be named.  The
relevant quantity is the area form `ω = o.areaForm` of Mathlib's
`Analysis/InnerProductSpace/TwoDim.lean`, which is Georgii's `sin(σ_i - σ_j)`:
`⟪x, y⟫² + ω x y² = 1` on the circle.

## Main results

* `shlosmanCube`, `shlosmanCube_eq_neg_two_iff` — the interaction (18.36) and **Georgii's "a
  configuration on `C` is a local ground state of `Φ` if and only if any two adjacent spins are
  orthogonal and any two next-nearest neighbour spins coincide"**; `m_Φ = -2`
  (`localGroundEnergy_shlosmanCube`).
* `shlosmanG` — Georgii's two open `(τ^t)`-invariant neighbourhoods `G_1`, `G_2` of the two
  classes, `G_n = {ζ : ω(σ_i, σ_j) > 1 - δ along every edge, with the staggered sign}`.  The
  two classes are `{ω(σ_even, σ_odd) = 1}` and `{ω(σ_even, σ_odd) = -1}`, which is Georgii's
  `ω_i = x ± π_i/2`.  `pairwise_disjoint_faceRestrict_shlosmanG` is the stability
  (18.23)(a)(ii) — Georgii's "for each face `F` of `C`, the distance between the `σ_F`-images of
  these classes is positive" — and `localGroundStates_subset_shlosmanG` the inclusion
  `G_ε(Φ) ⊆ G_1 ∪ G_2` for small `ε`.
* `shlosmanFlip`, `isPhiSymmetric_shlosmanG` — **Georgii's spin reversal `τ` on the even
  sublattice**, `ω_i ↦ ω_i + π`, here the antipodal map of the circle on the even corners: it is
  a symmetry of `Φ` and it exchanges `G_1` and `G_2`.
* `measurePreserving_rotation_shlosmanG` — the **continuous symmetry group `(τ^t)`**: every
  rotation of the circle is a symmetry of `Φ` which preserves *each* `G_n`, so Theorem
  (18.25)(ii) gives the `(τ^t)`-invariance of `μ_1` and `μ_2` that Georgii also deduces from
  Example (9.22)(2).
* `eventually_two_le_encard_extremePoints_shlosman` — **Georgii's conclusion**: for `β` large
  `𝒢(βΦ)` contains two mutually singular Gibbs measures, invariant under the rotations `(τ^t)`
  and under the even shifts `Θ̃`, and exchanged by `τ`, `r_0`, `r_1`, `r_2`, `θ_{(1,0)}` and
  `θ_{(0,1)}`; in particular `|ex 𝒢(βΦ)| ≥ 2`.

The variation (18.37) of Shlosman's theme, with `cos² sin²` in place of `cos²` and a stable
ground state degeneracy of order `4`, is not formalised.
-/

@[expose] public section

open Filter MeasureTheory Metric Module ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] [Fact (finrank ℝ V = 2)]

/-! ### Georgii (18.36): the interaction -/

variable (V) in
/-- **Georgii (18.36)**: Shlosman's plane rotor, `Φ_C = -∑_{diag} cos(σ_i - σ_j)
+ J ∑_{nn} cos²(σ_i - σ_j)` with `J > 0`, written with the inner product of the circle in place
of the cosine of the angle difference. -/
def shlosmanCube (J : ℝ) : ((Fin 2 → Fin 2) → sphere (0 : V) 1) → ℝ := fun ζ ↦
  -sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ
    + J * cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ

variable {J : ℝ}

lemma inner_sphere_comm (x y : sphere (0 : V) 1) : ⟪(x : V), (y : V)⟫ = ⟪(y : V), (x : V)⟫ :=
  real_inner_comm _ _

lemma continuous_shlosmanCube : Continuous (shlosmanCube V J) := by
  have hc : ∀ c c' : Fin 2 → Fin 2,
      Continuous fun ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 ↦ ⟪(ζ c : V), (ζ c' : V)⟫ :=
    fun c c' ↦ (continuous_subtype_val.comp (continuous_apply c)).inner
      (continuous_subtype_val.comp (continuous_apply c'))
  have hinner : Continuous fun p : sphere (0 : V) 1 × sphere (0 : V) 1 ↦ ⟪(p.1 : V), (p.2 : V)⟫ :=
    (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
  refine Continuous.add ?_ (continuous_const.mul (continuous_cubeBondSum (hinner.pow 2)))
  exact Continuous.neg ((hc _ _).add (hc _ _))

lemma measurable_shlosmanCube : Measurable (shlosmanCube V J) :=
  continuous_shlosmanCube.measurable

/-- **Condition (iii) of Georgii (17.18)** for (18.36). -/
lemma shlosmanCube_cubeRefl (k : Fin 2) (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    shlosmanCube V J (cubeRefl (sphere (0 : V) 1) k ζ) = shlosmanCube V J ζ := by
  simp only [shlosmanCube, cubeBondSum_cubeRefl,
    sqDiagSum_cubeRefl (fun x y : sphere (0 : V) 1 ↦ inner_sphere_comm x y) k ζ]

lemma zero_le_shlosmanBond (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    0 ≤ cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ := by
  have h := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) (m := 0) (ζ := ζ)
    fun c c' ↦ sq_nonneg _
  norm_num at h
  exact h

lemma sqDiagSum_inner_le_two (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ ≤ 2 := by
  have h := sqDiagSum_le (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) (M := 1) (ζ := ζ)
    fun x y ↦ real_inner_sphere_le_one x y
  linarith

/-- **Georgii's `Φ_C ≥ -2`** for (18.36) when `J ≥ 0`. -/
lemma neg_two_le_shlosmanCube (hJ : 0 ≤ J) (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    -2 ≤ shlosmanCube V J ζ := by
  have h1 := sqDiagSum_inner_le_two ζ
  have h2 := mul_nonneg hJ (zero_le_shlosmanBond ζ)
  rw [shlosmanCube]
  linarith

/-- **`|Φ_C| ≤ 2 + 4|J|`** for (18.36), the first alternative of condition (iv) of (17.18). -/
lemma abs_shlosmanCube_le (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    |shlosmanCube V J ζ| ≤ 2 + 4 * |J| := by
  have hd1 := sqDiagSum_inner_le_two ζ
  have hd2 := sqDiagSum_ge (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) (m := -1)
    (ζ := ζ) fun x y ↦ neg_one_le_real_inner_sphere x y
  have hb1 := zero_le_shlosmanBond ζ
  have hb2 := cubeBondSum_le (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) (M := 1) (ζ := ζ) fun c c' ↦ by
      have h1 := neg_one_le_real_inner_sphere (ζ c) (ζ c')
      have h2 := real_inner_sphere_le_one (ζ c) (ζ c')
      nlinarith
  norm_num at hb2
  have habs : |shlosmanCube V J ζ|
      ≤ |sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ|
        + |J * cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ| := by
    simpa only [shlosmanCube, abs_neg] using
      abs_add_le (-sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ)
        (J * cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ)
  refine habs.trans ?_
  rw [abs_mul]
  have hd : |sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ| ≤ 2 :=
    abs_le.2 ⟨by linarith, hd1⟩
  have hb : |cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ| ≤ 4 :=
    abs_le.2 ⟨by linarith, hb2⟩
  have : |J| * |cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ|
      ≤ |J| * 4 := by gcongr
  linarith

/-! ### Georgii's local ground states of (18.36) -/

/-- **Georgii's "a configuration on `C` is a local ground state of `Φ` if and only if any two
adjacent spins are orthogonal and any two next-nearest neighbour spins coincide".** -/
theorem shlosmanCube_eq_neg_two_iff (hJ : 0 < J) (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    shlosmanCube V J ζ = -2 ↔
      (∀ c c', (cubeGraph 2).Adj c c' → ⟪(ζ c : V), (ζ c' : V)⟫ = 0) ∧
        ζ (sqCorner 0 0) = ζ (sqCorner 1 1) ∧ ζ (sqCorner 1 0) = ζ (sqCorner 0 1) := by
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (0 : ℝ))) = 0 := by norm_num
  constructor
  · intro heq
    have hd1 := sqDiagSum_inner_le_two ζ
    have hb1 := zero_le_shlosmanBond ζ
    rw [shlosmanCube] at heq
    have hbond : cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ = 0 := by
      nlinarith
    have hdiag : sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ = 2 := by
      rw [hbond] at heq; linarith
    have hdiag' : ⟪(ζ (sqCorner 0 0) : V), (ζ (sqCorner 1 1) : V)⟫
        + ⟪(ζ (sqCorner 1 0) : V), (ζ (sqCorner 0 1) : V)⟫ = 2 := hdiag
    refine ⟨fun c c' hcc' ↦ ?_, ?_, ?_⟩
    · have h := (cubeBondSum_eq_iff_forall_adj (ψ := fun x y : sphere (0 : V) 1 ↦
        ⟪(x : V), (y : V)⟫ ^ 2) (m := 0) (fun x y ↦ sq_nonneg _) ζ).1 (by rw [hbond, hval])
        c c' hcc'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    · have h1 := real_inner_sphere_le_one (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1))
      have h2 := real_inner_sphere_le_one (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1))
      have e1 : ⟪(ζ (sqCorner 0 0) : V), (ζ (sqCorner 1 1) : V)⟫ = 1 := by linarith
      exact Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (norm_sphere_eq_one _)
        (norm_sphere_eq_one _)).1 e1)
    · have h1 := real_inner_sphere_le_one (ζ (sqCorner 0 0)) (ζ (sqCorner 1 1))
      have h2 := real_inner_sphere_le_one (ζ (sqCorner 1 0)) (ζ (sqCorner 0 1))
      have e2 : ⟪(ζ (sqCorner 1 0) : V), (ζ (sqCorner 0 1) : V)⟫ = 1 := by linarith
      exact Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (norm_sphere_eq_one _)
        (norm_sphere_eq_one _)).1 e2)
  · rintro ⟨hadj, hd1, hd2⟩
    have hbond : cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ = 0 := by
      rw [← hval]
      exact (cubeBondSum_eq_iff_forall_adj (ψ := fun x y : sphere (0 : V) 1 ↦
        ⟪(x : V), (y : V)⟫ ^ 2) (m := 0) (fun x y ↦ sq_nonneg _) ζ).2
        fun c c' hcc' ↦ by rw [hadj c c' hcc']; ring
    have hdiag : sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ = 2 := by
      rw [sqDiagSum_def, ← hd1, ← hd2]
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_sphere_eq_one,
        norm_sphere_eq_one]
      norm_num
    rw [shlosmanCube, hbond, hdiag]
    ring


/-! ### A local ground state, and `m_Φ = -2` -/

lemma fin_two_ne_add_one (k : Fin 2) : k ≠ k + 1 := by revert k; decide

/-- The two signs of `anisoSign` are inverse to themselves.  (Intended home:
`GibbsMeasure/Model/AnisotropicHeisenbergOceans.lean`, next to `anisoSign`.) -/
lemma anisoSign_mul_self (n : Fin 2) : anisoSign n * anisoSign n = 1 := by
  rcases fin_two_eq_zero_or_one n with rfl | rfl <;> norm_num [anisoSign]

/-- `anisoSign` reverses under a parity flip.  (Intended home:
`GibbsMeasure/Model/AnisotropicHeisenbergOceans.lean`.) -/
lemma anisoSign_add_one (n : Fin 2) : anisoSign (n + 1) = -anisoSign n :=
  anisoSign_eq_neg_of_ne (fin_two_ne_add_one n).symm

/-- In `Fin 2`, a shift by `j` at both ends cancels. -/
lemma fin_two_add_add_cancel (x y j : Fin 2) : x + j + (y + j) = x + y := by
  revert x y j; decide

variable (o : Orientation ℝ V (Fin 2))

/-- The quarter turn of a spin of the circle, Georgii's `x ↦ x + π/2`. -/
def quarterTurn (x : sphere (0 : V) 1) : sphere (0 : V) 1 :=
  ⟨o.rightAngleRotation (x : V), by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_sphere_eq_one]⟩

@[simp] lemma coe_quarterTurn (x : sphere (0 : V) 1) :
    ((quarterTurn o x : sphere (0 : V) 1) : V) = o.rightAngleRotation (x : V) := rfl

/-- **Georgii's local ground states `ω_i = x + π_i/2`**: the even corners of `C` carry `x`, the
odd ones its quarter turn. -/
def shlosmanGround (x : sphere (0 : V) 1) : (Fin 2 → Fin 2) → sphere (0 : V) 1 :=
  fun c ↦ if ∑ k, c k = 0 then x else quarterTurn o x

lemma inner_quarterTurn_right (x : sphere (0 : V) 1) :
    ⟪(x : V), ((quarterTurn o x : sphere (0 : V) 1) : V)⟫ = 0 := by
  rw [coe_quarterTurn, o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero]

lemma inner_quarterTurn_left (x : sphere (0 : V) 1) :
    ⟪((quarterTurn o x : sphere (0 : V) 1) : V), (x : V)⟫ = 0 := by
  rw [real_inner_comm]
  exact inner_quarterTurn_right o x

lemma areaForm_quarterTurn_right (x : sphere (0 : V) 1) :
    o.areaForm (x : V) ((quarterTurn o x : sphere (0 : V) 1) : V) = 1 := by
  rw [coe_quarterTurn, o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq,
    norm_sphere_eq_one]
  norm_num

/-- **Georgii's `m_Φ = -2`** for (18.36): the ground state with the odd sublattice rotated by a
quarter turn attains the bound. -/
lemma shlosmanCube_shlosmanGround (hJ : 0 < J) (x : sphere (0 : V) 1) :
    shlosmanCube V J (shlosmanGround o x) = -2 := by
  have hpar : ∀ c c' : Fin 2 → Fin 2, (cubeGraph 2).Adj c c' →
      ⟪((shlosmanGround o x c : sphere (0 : V) 1) : V),
        ((shlosmanGround o x c' : sphere (0 : V) 1) : V)⟫ = 0 := by
    intro c c' hcc'
    have hs := sum_eq_add_one_of_adj hcc'
    simp only [shlosmanGround]
    rcases fin_two_eq_zero_or_one (∑ k, c k) with hc | hc <;>
      rw [hc] at hs ⊢ <;> rw [hs] <;> simp only [if_neg (by decide : (1 : Fin 2) ≠ 0),
        if_neg (by decide : (0 : Fin 2) + 1 ≠ 0), if_pos (by decide : (1 : Fin 2) + 1 = 0)]
    · exact inner_quarterTurn_right o x
    · exact inner_quarterTurn_left o x
  rw [shlosmanCube_eq_neg_two_iff hJ]
  refine ⟨hpar, ?_, ?_⟩ <;> simp only [shlosmanGround, sum_sqCorner] <;> rfl

/-- **Georgii's `m_Φ = -2`** for (18.36).  The orientation is not part of the statement; it is
used only to name a ground state. -/
theorem localGroundEnergy_shlosmanCube (o : Orientation ℝ V (Fin 2)) (hJ : 0 < J) :
    localGroundEnergy (shlosmanCube V J) (sphereProb V) = -2 := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : V) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  exact localGroundEnergy_eq_of_isOpenPosMeasure continuous_shlosmanCube
    (neg_two_le_shlosmanCube hJ.le) (ζ₀ := shlosmanGround o ⟨x, hx⟩)
    (shlosmanCube_shlosmanGround o hJ _)

/-! ### Georgii's neighbourhoods `G_1` and `G_2` -/

/-- **Georgii's `G_1` and `G_2` of 18.3.8**: the two open, rotation invariant neighbourhoods of
the two classes of local ground states, separated by the *sense* of the quarter turn from the
even to the odd sublattice.  `o.areaForm` is Georgii's `sin(σ_i - σ_j)`. -/
def shlosmanG (δ : ℝ) (n : Fin 2) : Set ((Fin 2 → Fin 2) → sphere (0 : V) 1) :=
  {ζ | ∀ c c', (cubeGraph 2).Adj c c' →
    1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V)}

variable {o} {δ : ℝ}

lemma mem_shlosmanG {n : Fin 2} {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1} :
    ζ ∈ shlosmanG o δ n ↔ ∀ c c', (cubeGraph 2).Adj c c' →
      1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V) := Iff.rfl

lemma continuous_areaForm_apply (c c' : Fin 2 → Fin 2) :
    Continuous fun ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 ↦ o.areaForm (ζ c : V) (ζ c' : V) := by
  have h : (fun ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 ↦ o.areaForm (ζ c : V) (ζ c' : V))
      = fun ζ ↦ ⟪o.rightAngleRotation (ζ c : V), (ζ c' : V)⟫ := by
    funext ζ
    rw [o.inner_rightAngleRotation_left]
  rw [h]
  exact ((o.rightAngleRotation.continuous).comp
    (continuous_subtype_val.comp (continuous_apply c))).inner
      (continuous_subtype_val.comp (continuous_apply c'))

lemma isOpen_shlosmanG (n : Fin 2) : IsOpen (shlosmanG o δ n) := by
  have h : shlosmanG o δ n = ⋂ c, ⋂ c', {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 |
      (cubeGraph 2).Adj c c' → 1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V)}
      := by
    ext ζ
    simp [shlosmanG, Set.mem_iInter]
  rw [h]
  refine isOpen_iInter_of_finite fun c ↦ isOpen_iInter_of_finite fun c' ↦ ?_
  by_cases hcc' : (cubeGraph 2).Adj c c'
  · have hset : {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 | (cubeGraph 2).Adj c c' →
        1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V)}
        = {ζ | 1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V)} := by
      ext ζ; simp [hcc']
    rw [hset]
    exact isOpen_lt continuous_const (continuous_const.mul (continuous_areaForm_apply c c'))
  · have hset : {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1 | (cubeGraph 2).Adj c c' →
        1 - δ < anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V)} = Set.univ := by
      ext ζ; simp [hcc']
    rw [hset]
    exact isOpen_univ

lemma measurableSet_shlosmanG (n : Fin 2) : MeasurableSet (shlosmanG o δ n) :=
  (isOpen_shlosmanG n).measurableSet

/-- **Georgii's "for each face `F` of `C`, the distance between the `σ_F`-images of these classes
is positive"**: the two classes are separated already on one edge of a face. -/
theorem pairwise_disjoint_faceRestrict_shlosmanG (hδ1 : δ ≤ 1) (k : Fin 2) (a : Fin 2) :
    Pairwise fun m n ↦ Disjoint (faceRestrict (sphere (0 : V) 1) k a '' shlosmanG o δ m)
      (faceRestrict (sphere (0 : V) 1) k a '' shlosmanG o δ n) := by
  intro m n hmn
  rw [Set.disjoint_left]
  rintro g ⟨ζ, hζ, rfl⟩ ⟨ξ, hξ, hfe⟩
  set c₁ : Fin 2 → Fin 2 := fun _ ↦ a with hc₁
  set c₂ : Fin 2 → Fin 2 := cubeSiteRefl (k + 1) c₁ with hc₂
  have hc₂k : c₂ k = a := by
    rw [hc₂, cubeSiteRefl_apply, Function.update_of_ne (fin_two_ne_add_one k)]
  have h1' : ζ c₁ = ξ c₁ :=
    (congrFun hfe (⟨c₁, rfl⟩ : {c : Fin 2 → Fin 2 // c k = a})).symm
  have h2' : ζ c₂ = ξ c₂ :=
    (congrFun hfe (⟨c₂, hc₂k⟩ : {c : Fin 2 → Fin 2 // c k = a})).symm
  have hadj : (cubeGraph 2).Adj c₁ c₂ := cubeGraph_adj_cubeSiteRefl_self _ _
  have hsum : ∑ l, c₁ l = 0 := by
    rw [hc₁, Fin.sum_univ_two]
    exact fin_two_add_self a
  have hz := hζ c₁ c₂ hadj
  have hx := hξ c₁ c₂ hadj
  rw [hsum, add_zero] at hz hx
  rw [← h1', ← h2'] at hx
  rw [anisoSign_eq_neg_of_ne hmn] at hz
  nlinarith [hz, hx, hδ1]

/-- **Georgii's `G_ε(Φ) ⊆ G_1 ∪ G_2`**: an exact local ground state has
`ω(σ_even, σ_odd) = ±1`, and the sign says which class it belongs to. -/
theorem groundStates_subset_shlosmanG (hJ : 0 < J) (hδ0 : 0 < δ)
    {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1} (hζ : shlosmanCube V J ζ = -2) :
    ζ ∈ shlosmanG o δ 0 ∪ shlosmanG o δ 1 := by
  obtain ⟨hadj, hd1, hd2⟩ := (shlosmanCube_eq_neg_two_iff hJ ζ).1 hζ
  have hval : ∀ c : Fin 2 → Fin 2,
      ζ c = if ∑ k, c k = 0 then ζ (sqCorner 0 0) else ζ (sqCorner 1 0) := by
    intro c
    rcases sqCorner_surjective c with rfl | rfl | rfl | rfl <;> rw [sum_sqCorner]
    · rfl
    · rfl
    · exact hd2.symm
    · exact hd1.symm
  set A : V := (ζ (sqCorner 0 0) : V) with hA
  set B : V := (ζ (sqCorner 1 0) : V) with hB
  have hAB : ⟪A, B⟫ = 0 :=
    hadj (sqCorner 0 0) (sqCorner 1 0)
      (by decide : (cubeGraph 2).Adj (sqCorner 0 0) (sqCorner 1 0))
  have hsq : o.areaForm A B ^ 2 = 1 := by
    have h := o.inner_sq_add_areaForm_sq A B
    rw [hAB, hA, hB, norm_sphere_eq_one, norm_sphere_eq_one] at h
    nlinarith [h]
  have hpm : o.areaForm A B = 1 ∨ o.areaForm A B = -1 := by
    have hfac : (o.areaForm A B - 1) * (o.areaForm A B + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.1 hfac with hz | hz
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hkey : ∀ n : Fin 2, o.areaForm A B = anisoSign n → ζ ∈ shlosmanG o δ n := by
    intro n hn c c' hcc'
    have hs : ∑ k, c' k = ∑ k, c k + 1 := sum_eq_add_one_of_adj hcc'
    have hsign : anisoSign (n + ∑ k, c k) * o.areaForm (ζ c : V) (ζ c' : V) = 1 := by
      rcases fin_two_eq_zero_or_one (∑ k, c k) with hc | hc
      · have hζc : ζ c = ζ (sqCorner 0 0) := by rw [hval c, hc]; rfl
        have hζc' : ζ c' = ζ (sqCorner 1 0) := by rw [hval c', hs, hc]; rfl
        rw [hζc, hζc', hc, add_zero, ← hA, ← hB, hn]
        exact anisoSign_mul_self n
      · have hζc : ζ c = ζ (sqCorner 1 0) := by rw [hval c, hc]; rfl
        have hζc' : ζ c' = ζ (sqCorner 0 0) := by rw [hval c', hs, hc]; rfl
        rw [hζc, hζc', hc, ← hA, ← hB, o.areaForm_swap B A, hn, anisoSign_add_one, neg_mul_neg]
        exact anisoSign_mul_self n
    rw [hsign]
    linarith
  rcases hpm with hp | hp
  · exact Or.inl (hkey 0 (by rw [hp]; rfl))
  · exact Or.inr (hkey 1 (by rw [hp]; rfl))


/-! ### Georgii's symmetries of (18.36) -/

variable (o) in
/-- **Georgii's spin reversal `τ` on the even sublattice**, `τω = (ω_i + π_i)_i` with `π_i = π`
for `i_1 + i_2` even: the antipodal map of the circle at the corners of even parity, a pure spin
transformation (18.21). -/
def shlosmanFlip : CubeTransformation (sphere (0 : V) 1) 2 :=
  CubeTransformation.pureSpin fun c ↦
    if ∑ k, c k = 0 then (LinearIsometryEquiv.neg ℝ (E := V)).sphereMeasurableEquiv
      else MeasurableEquiv.refl _

lemma shlosmanFlip_spin (c : Fin 2 → Fin 2) :
    (shlosmanFlip (V := V)).spin c
      = if ∑ k, c k = 0 then (LinearIsometryEquiv.neg ℝ (E := V)).sphereMeasurableEquiv
        else MeasurableEquiv.refl _ := rfl

@[simp] lemma coe_onCube_shlosmanFlip (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1)
    (c : Fin 2 → Fin 2) :
    (((shlosmanFlip (V := V)).onCube.toFun ζ c : sphere (0 : V) 1) : V)
      = if ∑ k, c k = 0 then -(ζ c : V) else (ζ c : V) := by
  rw [shlosmanFlip, CubeTransformation.pureSpin_onCube_toFun_apply]
  split_ifs with h <;> rfl

@[simp] lemma sum_sqCorner_zero_zero : ∑ k, (sqCorner 0 0 : Fin 2 → Fin 2) k = 0 := by
  rw [sum_sqCorner]; rfl

@[simp] lemma sum_sqCorner_one_one : ∑ k, (sqCorner 1 1 : Fin 2 → Fin 2) k = 0 := by
  rw [sum_sqCorner]; rfl

@[simp] lemma sum_sqCorner_one_zero : ∑ k, (sqCorner 1 0 : Fin 2 → Fin 2) k = 1 := by
  rw [sum_sqCorner]; rfl

@[simp] lemma sum_sqCorner_zero_one : ∑ k, (sqCorner 0 1 : Fin 2 → Fin 2) k = 1 := by
  rw [sum_sqCorner]; rfl

/-- **`Φ_C ∘ τ = Φ_C`** for the spin reversal on the even sublattice: it negates exactly one end
of every edge, which the *square* of the inner product does not see, and both ends of every
diagonal, which the inner product does not see either. -/
lemma shlosmanCube_onCube_shlosmanFlip (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    shlosmanCube V J ((shlosmanFlip (V := V)).onCube.toFun ζ) = shlosmanCube V J ζ := by
  have hspin : ∀ (b : Fin 2 → Fin 2) (z : sphere (0 : V) 1),
      (((shlosmanFlip (V := V)).spin b z : sphere (0 : V) 1) : V)
        = if ∑ k, b k = 0 then -(z : V) else (z : V) := by
    intro b z
    rw [shlosmanFlip_spin]
    split_ifs with h <;> rfl
  have hbond : cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2)
      ((shlosmanFlip (V := V)).onCube.toFun ζ)
      = cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ := by
    refine cubeBondSum_onCube _ (fun c c' hcc' x y ↦ ?_) ζ
    have hs : ∑ k, c' k = ∑ k, c k + 1 := sum_eq_add_one_of_adj hcc'
    change ⟪(((shlosmanFlip (V := V)).spin c x : sphere (0 : V) 1) : V),
      (((shlosmanFlip (V := V)).spin c' y : sphere (0 : V) 1) : V)⟫ ^ 2 = ⟪(x : V), (y : V)⟫ ^ 2
    rw [hspin c x, hspin c' y, hs]
    rcases fin_two_eq_zero_or_one (∑ k, c k) with hc | hc <;> rw [hc] <;>
      simp [inner_neg_left, inner_neg_right, neg_sq]
  have hdiag : sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫)
      ((shlosmanFlip (V := V)).onCube.toFun ζ)
      = sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ := by
    change ⟪(((shlosmanFlip (V := V)).onCube.toFun ζ (sqCorner 0 0) : sphere (0 : V) 1) : V),
        (((shlosmanFlip (V := V)).onCube.toFun ζ (sqCorner 1 1) : sphere (0 : V) 1) : V)⟫
        + ⟪(((shlosmanFlip (V := V)).onCube.toFun ζ (sqCorner 1 0) : sphere (0 : V) 1) : V),
          (((shlosmanFlip (V := V)).onCube.toFun ζ (sqCorner 0 1) : sphere (0 : V) 1) : V)⟫
        = ⟪(ζ (sqCorner 0 0) : V), (ζ (sqCorner 1 1) : V)⟫
          + ⟪(ζ (sqCorner 1 0) : V), (ζ (sqCorner 0 1) : V)⟫
    rw [coe_onCube_shlosmanFlip, coe_onCube_shlosmanFlip, coe_onCube_shlosmanFlip,
      coe_onCube_shlosmanFlip, sum_sqCorner_zero_zero, sum_sqCorner_one_one,
      sum_sqCorner_one_zero, sum_sqCorner_zero_one]
    norm_num
  rw [shlosmanCube, shlosmanCube, hbond, hdiag]

lemma measurePreserving_neg_sphereProb :
    MeasurePreserving (LinearIsometryEquiv.neg ℝ (E := V)).sphereMeasurableEquiv
      (sphereProb V) (sphereProb V) :=
  MeasurePreserving.probNormalize
    ((LinearIsometryEquiv.neg ℝ (E := V)).measurePreserving_sphere_toSphere_volume)

/-- Georgii's `τ` belongs to `I_{C,λ}(Φ)` for (18.36). -/
theorem isSymmetry_shlosmanFlip :
    (shlosmanFlip (V := V)).IsSymmetry (shlosmanCube V J) (sphereProb V) :=
  CubeTransformation.IsSymmetry.of_apply_onCube shlosmanCube_cubeRefl
    (fun c ↦ by
      rw [shlosmanFlip_spin]
      split_ifs with h
      · exact measurePreserving_neg_sphereProb
      · exact MeasurePreserving.id _)
    shlosmanCube_onCube_shlosmanFlip

/-- **Georgii's "`G_1` and `G_2` are related to each other by `τ`"**: the spin reversal on the
even sublattice reverses the sense of the quarter turn. -/
lemma preimage_onCube_shlosmanFlip_shlosmanG (n : Fin 2) :
    (shlosmanFlip (V := V)).onCube.toFun ⁻¹' shlosmanG o δ n = shlosmanG o δ (n + 1) := by
  have hflip : ∀ (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) c c', (cubeGraph 2).Adj c c' →
      o.areaForm (((shlosmanFlip (V := V)).onCube.toFun ζ c : sphere (0 : V) 1) : V)
        (((shlosmanFlip (V := V)).onCube.toFun ζ c' : sphere (0 : V) 1) : V)
        = -o.areaForm (ζ c : V) (ζ c' : V) := by
    intro ζ c c' hcc'
    have hs : ∑ k, c' k = ∑ k, c k + 1 := sum_eq_add_one_of_adj hcc'
    rw [coe_onCube_shlosmanFlip, coe_onCube_shlosmanFlip, hs]
    rcases fin_two_eq_zero_or_one (∑ k, c k) with hc | hc <;> rw [hc] <;> simp
  ext ζ
  simp only [Set.mem_preimage, mem_shlosmanG]
  constructor
  · intro hζ c c' hcc'
    have hc := hζ c c' hcc'
    rw [hflip ζ c c' hcc'] at hc
    rw [add_right_comm, anisoSign_add_one]
    linarith
  · intro hζ c c' hcc'
    have hc := hζ c c' hcc'
    rw [add_right_comm, anisoSign_add_one] at hc
    rw [hflip ζ c c' hcc']
    linarith

lemma image_onCube_shlosmanFlip_shlosmanG {m n : Fin 2} (hmn : m ≠ n) :
    (shlosmanFlip (V := V)).onCube.toFun '' shlosmanG o δ m = shlosmanG o δ n := by
  have hm : m = n + 1 := by
    rw [← fin_two_add_one_eq_of_ne hmn]
    revert hmn; fin_cases m <;> fin_cases n <;> decide
  rw [hm, ← preimage_onCube_shlosmanFlip_shlosmanG n, Set.image_preimage_eq _
    (Function.RightInverse.surjective (shlosmanFlip (V := V)).onCube.toFun_inv_toFun)]

/-! ### The spatial symmetries and the shifts -/

/-- **A parity-reversing corner map exchanges `G_1` and `G_2`, a parity-preserving one fixes
them.**  This covers Georgii's `r_0`, `r_1`, `r_2` (`j = 1`) and the shifts `θ_a` with
`a_1 + a_2` even (`j = 0`). -/
lemma preimage_comp_shlosmanG {ρ : (Fin 2 → Fin 2) → (Fin 2 → Fin 2)}
    (hsurj : Function.Surjective ρ)
    (hadj : ∀ c c', (cubeGraph 2).Adj (ρ c) (ρ c') ↔ (cubeGraph 2).Adj c c') (j : Fin 2)
    (hpar : ∀ c, ∑ l, ρ c l = ∑ l, c l + j) (n : Fin 2) :
    (fun (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) c ↦ ζ (ρ c)) ⁻¹' shlosmanG o δ n
      = shlosmanG o δ (n + j) := by
  ext ζ
  simp only [Set.mem_preimage, mem_shlosmanG]
  constructor
  · intro hζ b b' hbb'
    obtain ⟨c, rfl⟩ := hsurj b
    obtain ⟨c', rfl⟩ := hsurj b'
    have hc := hζ c c' ((hadj c c').1 hbb')
    rw [hpar c, fin_two_add_add_cancel]
    exact hc
  · intro hζ c c' hcc'
    have hc := hζ (ρ c) (ρ c') ((hadj c c').2 hcc')
    rwa [hpar c, fin_two_add_add_cancel] at hc

lemma preimage_cubeRefl_shlosmanG (k : Fin 2) (n : Fin 2) :
    cubeRefl (sphere (0 : V) 1) k ⁻¹' shlosmanG o δ n = shlosmanG o δ (n + 1) :=
  preimage_comp_shlosmanG (cubeSiteRefl k).surjective
    (fun c c' ↦ cubeGraph_adj_cubeSiteRefl k c c') 1 (sum_cubeSiteRefl k) n

lemma image_onCube_refl_shlosmanG (k : Fin 2) {m n : Fin 2} (hmn : m ≠ n) :
    (CubeTransformation.refl (E := sphere (0 : V) 1) k).onCube.toFun '' shlosmanG o δ m
      = shlosmanG o δ n := by
  have hm : m = n + 1 := by
    rw [← fin_two_add_one_eq_of_ne hmn]
    revert hmn; fin_cases m <;> fin_cases n <;> decide
  rw [CubeTransformation.refl_onCube_toFun, hm, ← preimage_cubeRefl_shlosmanG k n,
    Set.image_preimage_eq _ (cubeRefl (sphere (0 : V) 1) k).surjective]

/-- **Georgii's shift group `Θ̃ = {θ_i : i_1 + i_2 ≡ 0 mod 2}`** for (18.36). -/
lemma preimage_tauPow_shlosmanG {a : Fin 2 → ℤ} (ha : Even (a 0 + a 1)) (n : Fin 2) :
    tauPow (cubeRefl (sphere (0 : V) 1)) (latticeToTorus 0 a) ⁻¹' shlosmanG o δ n
      = shlosmanG o δ n := by
  have hp : ∑ k, latticeParity a k = 0 := sum_latticeParity_two ha
  have h := preimage_comp_shlosmanG (o := o) (δ := δ)
    (ρ := fun c ↦ c + latticeParity a)
    (fun b ↦ ⟨b + latticeParity a, by
      change b + latticeParity a + latticeParity a = b
      rw [add_assoc, corner_add_self, add_zero]⟩)
    (by
      intro c c'
      revert c c'
      have : ∀ p c c' : Fin 2 → Fin 2,
          (cubeGraph 2).Adj (c + p) (c' + p) ↔ (cubeGraph 2).Adj c c' := by decide
      exact fun c c' ↦ this (latticeParity a) c c')
    0 (fun c ↦ by rw [sum_add, hp, add_zero]) n
  rw [add_zero] at h
  rw [← h]
  congr 1
  funext ζ
  rw [tauPow_cubeRefl_latticeToTorus_zero]


/-- A *spatial* cube transformation — Georgii's `r_0`, `r_1`, `r_2` — belongs to `I_{C,λ}(Φ)`
for (18.36). -/
theorem isSymmetry_of_spin_refl_shlosmanCube {τ : CubeTransformation (sphere (0 : V) 1) 2}
    (hτ : ∀ c, τ.spin c = MeasurableEquiv.refl _) :
    τ.IsSymmetry (shlosmanCube V J) (sphereProb V) :=
  CubeTransformation.isSymmetry_of_spin_refl shlosmanCube_cubeRefl hτ fun ζ ↦ by
    have hb := cubeBondSum_onCube_of_spin_refl
      (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) τ hτ ζ
    have hd := sqDiagSum_onCube_of_spin_refl
      (ψ := fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫)
      (fun x y : sphere (0 : V) 1 ↦ inner_sphere_comm x y) τ hτ ζ
    simp only [shlosmanCube]
    rw [hb, hd]

/-! ### Georgii's continuous symmetry group `(τ^t)` -/

/-- **Georgii's spin rotations `τ^t : ω ↦ (ω_i + t)_i`**, here the simultaneous action of a
linear isometry of the plane on all spins.  For an oriented plane the *positively oriented*
isometries are exactly the rotations. -/
def shlosmanRotation (φ : V ≃ₗᵢ[ℝ] V) : CubeTransformation (sphere (0 : V) 1) 2 :=
  CubeTransformation.pureSpin fun _ ↦ φ.sphereMeasurableEquiv

@[simp] lemma coe_onCube_shlosmanRotation (φ : V ≃ₗᵢ[ℝ] V)
    (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) (c : Fin 2 → Fin 2) :
    (((shlosmanRotation φ).onCube.toFun ζ c : sphere (0 : V) 1) : V) = φ (ζ c : V) := by
  rw [shlosmanRotation, CubeTransformation.pureSpin_onCube_toFun_apply]
  rfl

/-- Every rotation of the spins is a symmetry of (18.36): the interaction depends on the spins
only through their inner products. -/
theorem isSymmetry_shlosmanRotation (φ : V ≃ₗᵢ[ℝ] V) :
    (shlosmanRotation φ).IsSymmetry (shlosmanCube V J) (sphereProb V) := by
  refine CubeTransformation.IsSymmetry.of_apply_onCube shlosmanCube_cubeRefl
    (fun c ↦ MeasurePreserving.probNormalize (φ.measurePreserving_sphere_toSphere_volume))
    fun ζ ↦ ?_
  have hbond : cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2)
      ((shlosmanRotation φ).onCube.toFun ζ)
      = cubeBondSum 2 (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫ ^ 2) ζ := by
    refine cubeBondSum_onCube _ (fun c c' _ x y ↦ ?_) ζ
    change ⟪φ (x : V), φ (y : V)⟫ ^ 2 = ⟪(x : V), (y : V)⟫ ^ 2
    rw [φ.inner_map_map]
  have hdiag : sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫)
      ((shlosmanRotation φ).onCube.toFun ζ)
      = sqDiagSum (fun x y : sphere (0 : V) 1 ↦ ⟪(x : V), (y : V)⟫) ζ := by
    change ⟪(((shlosmanRotation φ).onCube.toFun ζ (sqCorner 0 0) : sphere (0 : V) 1) : V),
        (((shlosmanRotation φ).onCube.toFun ζ (sqCorner 1 1) : sphere (0 : V) 1) : V)⟫
        + ⟪(((shlosmanRotation φ).onCube.toFun ζ (sqCorner 1 0) : sphere (0 : V) 1) : V),
          (((shlosmanRotation φ).onCube.toFun ζ (sqCorner 0 1) : sphere (0 : V) 1) : V)⟫
        = ⟪(ζ (sqCorner 0 0) : V), (ζ (sqCorner 1 1) : V)⟫
          + ⟪(ζ (sqCorner 1 0) : V), (ζ (sqCorner 0 1) : V)⟫
    rw [coe_onCube_shlosmanRotation, coe_onCube_shlosmanRotation, coe_onCube_shlosmanRotation,
      coe_onCube_shlosmanRotation, φ.inner_map_map, φ.inner_map_map]
  simp only [shlosmanCube]
  rw [hbond, hdiag]

/-- **The rotations preserve each of `G_1` and `G_2`**: they preserve the area form, so they do
not change the sense of the quarter turn.  This is why Georgii's neighbourhoods are
`(τ^t)`-invariant, and hence why (18.25)(ii) gives the `(τ^t)`-invariance of the two Gibbs
measures. -/
theorem image_onCube_shlosmanRotation_shlosmanG (φ : V ≃ₗᵢ[ℝ] V)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : V →ₗ[ℝ] V)) (n : Fin 2) :
    (shlosmanRotation φ).onCube.toFun '' shlosmanG o δ n = shlosmanG o δ n := by
  have hpre : (shlosmanRotation φ).onCube.toFun ⁻¹' shlosmanG o δ n = shlosmanG o δ n := by
    ext ζ
    simp only [Set.mem_preimage, mem_shlosmanG, coe_onCube_shlosmanRotation]
    exact forall_congr' fun c ↦ forall_congr' fun c' ↦ imp_congr Iff.rfl
      (by rw [o.areaForm_comp_linearIsometryEquiv φ hφ])
  calc (shlosmanRotation φ).onCube.toFun '' shlosmanG o δ n
      = (shlosmanRotation φ).onCube.toFun ''
          ((shlosmanRotation φ).onCube.toFun ⁻¹' shlosmanG o δ n) := by rw [hpre]
    _ = shlosmanG o δ n := Set.image_preimage_eq _
          (Function.RightInverse.surjective (shlosmanRotation φ).onCube.toFun_inv_toFun)

/-! ### Georgii 18.3.8: the conclusion -/

section Conclusion

variable (hJ : 0 < J) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)

include hJ hδ0

/-- **Georgii's `G_ε(Φ) ⊆ G_1 ∪ G_2` for small `ε`** for (18.36). -/
theorem exists_localGroundStates_subset_shlosmanG :
    ∃ ε > 0, localGroundStates (shlosmanCube V J) (sphereProb V) ε ⊆ ⋃ n, shlosmanG o δ n := by
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : V) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  refine exists_pos_localGroundStates_subset_of_compactSpace continuous_shlosmanCube
    (neg_two_le_shlosmanCube hJ.le) (ζ₀ := shlosmanGround o ⟨x, hx⟩)
    (shlosmanCube_shlosmanGround o hJ _) (isOpen_iUnion fun n ↦ isOpen_shlosmanG n) ?_
  intro ζ hζ
  rcases groundStates_subset_shlosmanG hJ hδ0 hζ with h | h
  · exact Set.mem_iUnion.2 ⟨0, h⟩
  · exact Set.mem_iUnion.2 ⟨1, h⟩

include hδ1

/-- **Georgii's "`{G_1, G_2}` is a stable partition of the local ground states"** for (18.36). -/
theorem isPStablePartition_shlosmanG :
    IsPStablePartition (shlosmanCube V J) (sphereProb V) Set.univ (shlosmanG o δ) where
  exists_localGroundStates_subset := exists_localGroundStates_subset_shlosmanG hJ hδ0
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_shlosmanG hδ1 k a

omit hJ hδ0 hδ1 in
/-- **Georgii's "`G_1` and `G_2` are related to each other by the symmetries `τ, r_0, r_1, r_2`"**
for (18.36). -/
theorem isPhiSymmetric_shlosmanG :
    IsPhiSymmetric (shlosmanCube V J) (sphereProb V) (shlosmanG o δ) :=
  isPhiSymmetric_of_ne shlosmanCube_cubeRefl fun m n hmn ↦
    ⟨shlosmanFlip, isSymmetry_shlosmanFlip, image_onCube_shlosmanFlip_shlosmanG hmn⟩

/-- **Georgii 18.3.8, Shlosman's plane rotor (18.36).**  *If `β` is sufficiently large then
`𝒢(βΦ)` contains two mutually singular Gibbs measures `μ_1` and `μ_2` which are invariant under
`(τ^t)_{t}` and `Θ̃ = {θ_i : i_1 + i_2 even}` and satisfy `μ_2 = τ(μ_1)`.* -/
theorem eventually_exists_shlosman_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * shlosmanCube V J ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * shlosmanCube V J ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → sphere (0 : V) 1),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (sphere (0 : V) 1)
          (fun ζ ↦ β * shlosmanCube V J ζ) (sphereProb V) hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart (sphere (0 : V) 1) (shlosmanG o δ n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ), Even (a 0 + a 1) →
          MeasurePreserving (shift (sphere (0 : V) 1) a).toFun (μ n) (μ n)) ∧
        (∀ (n : Fin 2) (φ : V ≃ₗᵢ[ℝ] V),
          0 < LinearMap.det (φ.toLinearEquiv : V →ₗ[ℝ] V) →
          MeasurePreserving ((shlosmanRotation φ).onLattice (sphere (0 : V) 1)).toFun
            (μ n) (μ n)) ∧
        (μ 0).map ((shlosmanFlip (V := V)).onLattice (sphere (0 : V) 1)).toFun = μ 1 ∧
        (μ 1).map ((shlosmanFlip (V := V)).onLattice (sphere (0 : V) 1)).toFun = μ 0 := by
  obtain ⟨ε, hε, hGε⟩ := exists_localGroundStates_subset_shlosmanG (o := o) (δ := δ) hJ hδ0
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := sphere (0 : V) 1)
    (φ := shlosmanCube V J) (ν := sphereProb V) (G := shlosmanG o δ)
    measurable_shlosmanCube (neg_two_le_shlosmanCube hJ.le) shlosmanCube_cubeRefl
    (isCubeConfining_univ ⟨2 + 4 * |J|, abs_shlosmanCube_le⟩)
    (isPStablePartition_shlosmanG hJ hδ0 hδ1)
    (isPhiSymmetric_shlosmanG (o := o) (δ := δ) (J := J)) measurableSet_shlosmanG hε hGε]
    with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, h7, h8, -⟩ := hβ hφβ hMβ
  have hflipβ : (shlosmanFlip (V := V)).IsSymmetry
      (fun ζ ↦ β * shlosmanCube V J ζ) (sphereProb V) :=
    isSymmetry_shlosmanFlip.const_mul shlosmanCube_cubeRefl β
  refine ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n a ha ↦ h6 n a (preimage_tauPow_shlosmanG ha n),
    fun n φ hφ ↦ h7 n (shlosmanRotation φ)
      ((isSymmetry_shlosmanRotation φ).const_mul shlosmanCube_cubeRefl β)
      (image_onCube_shlosmanRotation_shlosmanG φ hφ n),
    h8 0 1 _ hflipβ (image_onCube_shlosmanFlip_shlosmanG (by decide)),
    h8 1 0 _ hflipβ (image_onCube_shlosmanFlip_shlosmanG (by decide))⟩

/-- **Georgii 18.3.8**: `|ex 𝒢(βΦ)| ≥ 2` for `β` large.  As the partition is staggered it is not
`r`-symmetric, so this is the count in `𝒢(βΦ)` through Corollary (7.29). -/
theorem eventually_two_le_encard_extremePoints_shlosman (o : Orientation ℝ V (Fin 2)) :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * shlosmanCube V J ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * shlosmanCube V J ζ),
      (2 : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G (cubeGibbsSpec (sphere (0 : V) 1)
        (fun ζ ↦ β * shlosmanCube V J ζ) (sphereProb V) hφβ hMβ)).extremePoints
          ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hGε⟩ := exists_localGroundStates_subset_shlosmanG (o := o) (δ := δ) hJ hδ0
  exact eventually_le_encard_extremePoints_G (E := sphere (0 : V) 1)
    (φ := shlosmanCube V J) (ν := sphereProb V) (Gs := shlosmanG o δ)
    measurable_shlosmanCube (neg_two_le_shlosmanCube hJ.le) shlosmanCube_cubeRefl
    (isCubeConfining_univ ⟨2 + 4 * |J|, abs_shlosmanCube_le⟩)
    (isPStablePartition_shlosmanG hJ hδ0 hδ1)
    (isPhiSymmetric_shlosmanG (o := o) (δ := δ) (J := J)) measurableSet_shlosmanG hε hGε

end Conclusion

end MeasureTheory.GibbsMeasure

end

end

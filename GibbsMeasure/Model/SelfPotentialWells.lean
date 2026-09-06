/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.EntropyEnergyConflict
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Georgii, Example (19.19): wells of a self-potential

Placeholder header, to be filled in.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The a priori measure: normalised Lebesgue measure on a ball of `ℝ^p` -/

section BallProb

variable {p : ℕ} {R s : ℝ}

/-- **Georgii's a priori measure `λ` of Example (19.19)**, normalised: Lebesgue measure on the
ball `E = {x ∈ ℝ^p : |x| ≤ R}` divided by its total mass. -/
def ballProb (p : ℕ) (R : ℝ) : Measure (EuclideanSpace ℝ (Fin p)) :=
  (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin p)) R)).probNormalize

variable (p) in
lemma volume_closedBall_ne_top (R : ℝ) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) R) ≠ ⊤ :=
  measure_closedBall_lt_top.ne

variable (p) in
lemma volume_closedBall_pos (hR : 0 < R) :
    0 < volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) R) :=
  measure_closedBall_pos _ _ hR

instance isFiniteMeasure_restrict_closedBall :
    IsFiniteMeasure (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin p)) R)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact measure_closedBall_lt_top

lemma neZero_restrict_closedBall (hR : 0 < R) :
    NeZero (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin p)) R)) := by
  refine ⟨fun h ↦ ?_⟩
  have := volume_closedBall_pos p (R := R) hR
  rw [← Measure.restrict_apply_univ, h] at this
  simp at this

lemma isProbabilityMeasure_ballProb (hR : 0 < R) : IsProbabilityMeasure (ballProb p R) := by
  have := neZero_restrict_closedBall (p := p) hR
  exact Measure.isProbabilityMeasure_probNormalize _

/-- The reference constant: the Lebesgue measure of the unit ball of `ℝ^p`. -/
lemma volume_closedBall_eq (hs : 0 ≤ s) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) s)
      = ENNReal.ofReal (s ^ p) * volume (ball (0 : EuclideanSpace ℝ (Fin p)) 1) := by
  rw [Measure.addHaar_closedBall volume _ hs, finrank_euclideanSpace_fin]

lemma volume_ball_one_pos : 0 < volume (ball (0 : EuclideanSpace ℝ (Fin p)) 1) :=
  measure_ball_pos _ _ one_pos

lemma volume_ball_one_ne_top : volume (ball (0 : EuclideanSpace ℝ (Fin p)) 1) ≠ ⊤ :=
  measure_ball_lt_top.ne

/-- `λ(S)` for a measurable `S` inside the ball. -/
lemma ballProb_apply {S : Set (EuclideanSpace ℝ (Fin p))} (hS : MeasurableSet S)
    (hsub : S ⊆ closedBall 0 R) :
    ballProb p R S = volume S / volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) R) := by
  rw [ballProb, Measure.probNormalize_def, Measure.smul_apply, Measure.restrict_apply_univ,
    Measure.restrict_apply hS, Set.inter_eq_self_of_subset_left hsub, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

/-- **`λ(closedBall 0 s) = (s/R)^p`.**  The normalisation is what makes Georgii's conditions
(19.17) and (19.18) scale invariant. -/
lemma ballProb_closedBall (hR : 0 < R) (hs : 0 ≤ s) (hsR : s ≤ R) :
    ballProb p R (closedBall (0 : EuclideanSpace ℝ (Fin p)) s) = ENNReal.ofReal ((s / R) ^ p) := by
  have hcpos := volume_ball_one_pos (p := p)
  have hctop := volume_ball_one_ne_top (p := p)
  rw [ballProb_apply measurableSet_closedBall (closedBall_subset_closedBall hsR),
    volume_closedBall_eq hs, volume_closedBall_eq hR.le,
    ENNReal.mul_div_mul_right _ _ hcpos.ne' hctop, div_pow,
    ENNReal.ofReal_div_of_pos (by positivity)]

variable (p) in
/-- The Lebesgue measure of the unit ball of `ℝ^p`, as a positive real number.  Only the fact
that it is a positive constant matters: it cancels in every ratio below. -/
def unitBallVolume : ℝ := (volume (ball (0 : EuclideanSpace ℝ (Fin p)) 1)).toReal

variable (p) in
lemma unitBallVolume_pos : 0 < unitBallVolume p :=
  ENNReal.toReal_pos volume_ball_one_pos.ne' volume_ball_one_ne_top

variable (p) in
lemma volume_ball_one_eq :
    volume (ball (0 : EuclideanSpace ℝ (Fin p)) 1) = ENNReal.ofReal (unitBallVolume p) :=
  (ENNReal.ofReal_toReal volume_ball_one_ne_top).symm

lemma volume_closedBall_eq' (hs : 0 ≤ s) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) s)
      = ENNReal.ofReal (s ^ p * unitBallVolume p) := by
  rw [volume_closedBall_eq hs, volume_ball_one_eq, ← ENNReal.ofReal_mul (by positivity)]

lemma volume_ball_eq' (hp : 0 < p) (hs : 0 ≤ s) :
    volume (ball (0 : EuclideanSpace ℝ (Fin p)) s) = ENNReal.ofReal (s ^ p * unitBallVolume p) := by
  have : Nontrivial (EuclideanSpace ℝ (Fin p)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hp)
  rw [Measure.addHaar_ball volume _ hs, finrank_euclideanSpace_fin, volume_ball_one_eq,
    ← ENNReal.ofReal_mul (by positivity)]

/-- **An upper bound for the normalised volume of the spherical shell `{ |‖x‖ - a| ≤ ρ }`**:
it is at most `((a + ρ)^p - (a - ρ)^p)/R^p`.  For Georgii's `A_0` this is the thinness of the
deep well, which is what condition (19.18) constrains. -/
lemma ballProb_shell_le {a ρ : ℝ} (hp : 0 < p) (hR : 0 < R) (hρ : 0 ≤ ρ) (haρ : 0 ≤ a - ρ)
    (h : a + ρ ≤ R) :
    ballProb p R {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2}
      ≤ ENNReal.ofReal (((a + ρ) ^ p - (a - ρ) ^ p) / R ^ p) := by
  have hC := unitBallVolume_pos p
  have hmono : (a - ρ) ^ p ≤ (a + ρ) ^ p := by
    refine pow_le_pow_left₀ haρ (by linarith) p
  have hSm : MeasurableSet {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin p), (‖x‖ - a) ^ 2 ≤ ρ ^ 2 →
      a - ρ ≤ ‖x‖ ∧ ‖x‖ ≤ a + ρ := by
    intro x hx
    obtain ⟨h1, h2⟩ := abs_le_of_sq_le_sq' hx hρ
    exact ⟨by linarith, by linarith⟩
  have hsub : {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2}
      ⊆ closedBall 0 (a + ρ) \ ball 0 (a - ρ) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hnorm x hx
    refine ⟨by simpa [mem_closedBall, dist_eq_norm] using h2, ?_⟩
    simp only [mem_ball, dist_eq_norm, sub_zero, not_lt]
    exact h1
  have hsubR : {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2} ⊆ closedBall 0 R := by
    intro x hx
    have := (hnorm x hx).2
    simpa [mem_closedBall, dist_eq_norm] using this.trans h
  have hdiff : volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) (a + ρ) \ ball 0 (a - ρ))
      = ENNReal.ofReal (((a + ρ) ^ p - (a - ρ) ^ p) * unitBallVolume p) := by
    rw [measure_sdiff (ball_subset_closedBall.trans
        (closedBall_subset_closedBall (by linarith))) measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne,
      volume_closedBall_eq' (by linarith), volume_ball_eq' hp haρ,
      ← ENNReal.ofReal_sub _ (by positivity), sub_mul]
  calc ballProb p R {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2}
      = volume {x : EuclideanSpace ℝ (Fin p) | (‖x‖ - a) ^ 2 ≤ ρ ^ 2}
          / volume (closedBall (0 : EuclideanSpace ℝ (Fin p)) R) := ballProb_apply hSm hsubR
    _ ≤ ENNReal.ofReal (((a + ρ) ^ p - (a - ρ) ^ p) * unitBallVolume p)
          / ENNReal.ofReal (R ^ p * unitBallVolume p) := by
        gcongr
        · rw [← hdiff]
          exact measure_mono hsub
        · rw [volume_closedBall_eq' hR.le]
    _ = ENNReal.ofReal (((a + ρ) ^ p - (a - ρ) ^ p) / R ^ p) := by
        rw [← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        field_simp

end BallProb

/-! ### Georgii's interaction of Example (19.19) -/

section Interaction

variable {p : ℕ} {r δ κ : ℝ} {x y : EuclideanSpace ℝ (Fin p)}
  {ζ : (Fin 2 → Fin 2) → EuclideanSpace ℝ (Fin p)}

/-- The radius `|x| ∧ 3r`.  Georgii's state space is the ball `E = {|x| ≤ 3r}`, on which this is
`|x|`; here the spins range over all of `ℝ^p` and the a priori measure is carried by `E`, so the
truncation only serves to make `Φ_C` a *bounded* function on the whole configuration space, as
the framework of §18.1 requires.  It changes nothing `λ^C`-almost everywhere. -/
def wellNorm (r : ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ := min ‖x‖ (3 * r)

/-- **Georgii's `u(x, y) = |x - y|²`**, truncated at its maximum `36 r²` on `E`. -/
def wellPair (r : ℝ) (x y : EuclideanSpace ℝ (Fin p)) : ℝ := min (‖x - y‖ ^ 2) (36 * r ^ 2)

/-- **Georgii's `v(x) = (δ + |x|²) ∧ κ(|x| - 2r)²`**. -/
def wellSelf (r δ κ : ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  min (δ + wellNorm r x ^ 2) (κ * (wellNorm r x - 2 * r) ^ 2)

/-- **Georgii's cube interaction of Example (19.19)**,
`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} u(σ_i, σ_j) + ∑_{i ∈ C} v(σ_i)`.

The four nearest-neighbour pairs of the unit square are the pairs `{c, c + e_k}`, `c ∈ C`,
`k ∈ {0, 1}`, each of which occurs twice in the double sum; hence the factor `1/2`. -/
def wellCube (r δ κ : ℝ) (ζ : (Fin 2 → Fin 2) → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (∑ c : Fin 2 → Fin 2, ∑ k : Fin 2, wellPair r (ζ c) (ζ (c + Pi.single k 1))) / 2
    + ∑ c : Fin 2 → Fin 2, wellSelf r δ κ (ζ c)

lemma wellNorm_nonneg (hr : 0 ≤ r) : 0 ≤ wellNorm r x :=
  le_min (norm_nonneg _) (by positivity)

lemma wellNorm_eq_norm (hx : ‖x‖ ≤ 3 * r) : wellNorm r x = ‖x‖ := min_eq_left hx

lemma wellNorm_le (r : ℝ) (x : EuclideanSpace ℝ (Fin p)) : wellNorm r x ≤ ‖x‖ := min_le_left _ _

lemma wellPair_nonneg (r : ℝ) (x y : EuclideanSpace ℝ (Fin p)) : 0 ≤ wellPair r x y :=
  le_min (by positivity) (by positivity)

lemma wellPair_le_sq (r : ℝ) (x y : EuclideanSpace ℝ (Fin p)) :
    wellPair r x y ≤ ‖x - y‖ ^ 2 := min_le_left _ _

lemma wellSelf_nonneg (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) : 0 ≤ wellSelf r δ κ x :=
  le_min (by positivity) (by positivity)

lemma wellSelf_le_first (r δ κ : ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    wellSelf r δ κ x ≤ δ + wellNorm r x ^ 2 := min_le_left _ _

lemma wellSelf_le_second (r δ κ : ℝ) (x : EuclideanSpace ℝ (Fin p)) :
    wellSelf r δ κ x ≤ κ * (wellNorm r x - 2 * r) ^ 2 := min_le_right _ _

lemma le_wellSelf {m : ℝ} (h₁ : m ≤ δ + wellNorm r x ^ 2)
    (h₂ : m ≤ κ * (wellNorm r x - 2 * r) ^ 2) : m ≤ wellSelf r δ κ x := le_min h₁ h₂

/-- `Φ_C ≥ 0`: both `u` and `v` are nonnegative. -/
lemma wellCube_nonneg (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) : 0 ≤ wellCube r δ κ ζ := by
  refine add_nonneg (div_nonneg (Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun k _ ↦
    wellPair_nonneg _ _ _) (by norm_num)) (Finset.sum_nonneg fun c _ ↦ wellSelf_nonneg hδ hκ)

/-- An upper bound for `Φ_C` from uniform bounds on `u` and `v`: `Φ_C ≤ 4U + 4V`. -/
lemma wellCube_le {U V : ℝ} (hu : ∀ c k, wellPair r (ζ c) (ζ (c + Pi.single k 1)) ≤ U)
    (hv : ∀ c, wellSelf r δ κ (ζ c) ≤ V) : wellCube r δ κ ζ ≤ 4 * U + 4 * V := by
  have h1 : (∑ c : Fin 2 → Fin 2, ∑ k : Fin 2, wellPair r (ζ c) (ζ (c + Pi.single k 1)))
      ≤ 8 * U := by
    calc (∑ c : Fin 2 → Fin 2, ∑ k : Fin 2, wellPair r (ζ c) (ζ (c + Pi.single k 1)))
        ≤ ∑ _c : Fin 2 → Fin 2, ∑ _k : Fin 2, U :=
          Finset.sum_le_sum fun c _ ↦ Finset.sum_le_sum fun k _ ↦ hu c k
      _ = 8 * U := by simp [Finset.sum_const]; try ring
  have h2 : (∑ c : Fin 2 → Fin 2, wellSelf r δ κ (ζ c)) ≤ 4 * V := by
    calc (∑ c : Fin 2 → Fin 2, wellSelf r δ κ (ζ c)) ≤ ∑ _c : Fin 2 → Fin 2, V :=
          Finset.sum_le_sum fun c _ ↦ hv c
      _ = 4 * V := by simp [Finset.sum_const]; try ring
  rw [wellCube]
  linarith

/-- A lower bound for `Φ_C` from a uniform lower bound on `v`: `Φ_C ≥ 4V`. -/
lemma le_wellCube {V : ℝ} (hv : ∀ c, V ≤ wellSelf r δ κ (ζ c)) :
    4 * V ≤ wellCube r δ κ ζ := by
  have h1 : (0 : ℝ) ≤ ∑ c : Fin 2 → Fin 2, ∑ k : Fin 2, wellPair r (ζ c) (ζ (c + Pi.single k 1)) :=
    Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun k _ ↦ wellPair_nonneg _ _ _
  have h2 : 4 * V ≤ ∑ c : Fin 2 → Fin 2, wellSelf r δ κ (ζ c) := by
    calc 4 * V = ∑ _c : Fin 2 → Fin 2, V := by simp [Finset.sum_const]; try ring
      _ ≤ _ := Finset.sum_le_sum fun c _ ↦ hv c
  rw [wellCube]
  linarith

end Interaction

/-! ### Georgii's wells `W_n = A_n^C` and rectangles `V_n = B_n^C` -/

section Wells

variable {p : ℕ} {r δ κ s : ℝ} {z x y : EuclideanSpace ℝ (Fin p)}
  {ζ : (Fin 2 → Fin 2) → EuclideanSpace ℝ (Fin p)}

/-- **Georgii's `A_0` and `A_1`** of Example (19.19): the thin spherical shell
`A_0 = {(|x| - 2r)² ≤ r²/κ}` about the sphere of radius `2r`, at whose centre the self-potential
vanishes, and the ball `A_1 = {|x| ≤ r}`, on which the self-potential is `δ + |x|² ≥ δ`. -/
def wellBase (r κ : ℝ) : Fin 2 → Set (EuclideanSpace ℝ (Fin p)) :=
  ![{x | (‖x‖ - 2 * r) ^ 2 ≤ r ^ 2 / κ}, closedBall 0 r]

/-- **Georgii's `B_0` and `B_1`**: the ball `B_0` of radius `√(δ/6κ)` about a point `z` of norm
`2r` — Georgii's `(2r, 0, …, 0)` — and the ball `B_1` of radius `s ≤ r` about the origin. -/
def wellRect (r δ κ s : ℝ) (z : EuclideanSpace ℝ (Fin p)) :
    Fin 2 → Set (EuclideanSpace ℝ (Fin p)) :=
  ![closedBall z (Real.sqrt (δ / (6 * κ))), closedBall 0 s]

/-- **Georgii's wells `W_n = A_n^C`**. -/
def wellPattern (r κ : ℝ) : Fin 2 → Set ((Fin 2 → Fin 2) → EuclideanSpace ℝ (Fin p)) :=
  fun n ↦ Set.univ.pi fun _ ↦ wellBase r κ n

@[simp] lemma wellBase_zero :
    (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0
      = {x | (‖x‖ - 2 * r) ^ 2 ≤ r ^ 2 / κ} := rfl

@[simp] lemma wellBase_one :
    (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1 = closedBall 0 r := rfl

@[simp] lemma wellRect_zero :
    (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0
      = closedBall z (Real.sqrt (δ / (6 * κ))) := rfl

@[simp] lemma wellRect_one :
    (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1 = closedBall 0 s := rfl

lemma mem_wellPattern {n : Fin 2} :
    ζ ∈ wellPattern r κ n ↔ ∀ c, ζ c ∈ wellBase r κ n := by
  simp [wellPattern]

/-! #### Geometry of the wells -/

/-- On Georgii's shell `A_0` the norm is within `r/4` of `2r`, once `κ ≥ 16`. -/
lemma norm_bounds_of_mem_wellBase_zero (hr : 0 < r) (hκ : 16 ≤ κ)
    (hx : x ∈ (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0) :
    2 * r - r / 4 ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * r + r / 4 := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have h1 : (‖x‖ - 2 * r) ^ 2 ≤ r ^ 2 / κ := hx
  have h2 : r ^ 2 / κ ≤ (r / 4) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hκ0 (by norm_num)]
    nlinarith [sq_nonneg r]
  obtain ⟨ha, hb⟩ := abs_le_of_sq_le_sq' (h1.trans h2) (by linarith)
  exact ⟨by linarith, by linarith⟩

/-- Georgii's two wells are disjoint: `A_0` sits at distance `≥ 7r/4` from the origin. -/
lemma disjoint_wellBase (hr : 0 < r) (hκ : 16 ≤ κ) :
    Disjoint ((wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0) (wellBase r κ 1) := by
  refine Set.disjoint_left.2 fun x hx0 hx1 ↦ ?_
  have h0 := (norm_bounds_of_mem_wellBase_zero hr hκ hx0).1
  have h1 : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hx1
  linarith

/-- **On Georgii's `B_0`, `(|x| - 2r)² ≤ δ/6κ`.**  `B_0` is the ball of radius `√(δ/6κ)` about
a point of norm `2r`, so the radius fluctuates by at most `√(δ/6κ)` on it. -/
lemma sq_sub_le_of_mem_wellRect_zero (hδ : 0 ≤ δ) (hκ : 0 < κ) (hz : ‖z‖ = 2 * r)
    (hx : x ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0) :
    (‖x‖ - 2 * r) ^ 2 ≤ δ / (6 * κ) := by
  have hsq : Real.sqrt (δ / (6 * κ)) ^ 2 = δ / (6 * κ) := Real.sq_sqrt (by positivity)
  have hdist : ‖x - z‖ ≤ Real.sqrt (δ / (6 * κ)) := by
    simpa [mem_closedBall, dist_eq_norm] using hx
  have habs : |‖x‖ - 2 * r| ≤ Real.sqrt (δ / (6 * κ)) := by
    rw [← hz]; exact (abs_norm_sub_norm_le x z).trans hdist
  rw [← hsq, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- The radius of `B_0` is at most `r`; in particular `B_0 ⊆ E`. -/
lemma sqrt_delta_le (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < 6 * r ^ 2) (hκ : 16 ≤ κ) :
    Real.sqrt (δ / (6 * κ)) ≤ r := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hle : δ / (6 * κ) ≤ r ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hr.le] at this

/-- `B_0 ⊆ A_0` and `B_1 ⊆ A_1`. -/
lemma wellRect_subset_wellBase (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < 6 * r ^ 2) (hκ : 16 ≤ κ)
    (hsr : s ≤ r) (hz : ‖z‖ = 2 * r) (n : Fin 2) :
    (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) n ≤ wellBase r κ n := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  fin_cases n
  · intro x hx
    change (‖x‖ - 2 * r) ^ 2 ≤ r ^ 2 / κ
    refine (sq_sub_le_of_mem_wellRect_zero hδ.le hκ0 hz hx).trans ?_
    rw [div_le_div_iff₀ (by positivity) hκ0]
    nlinarith
  · exact closedBall_subset_closedBall hsr

/-! #### The self-potential on the wells -/

/-- On `A_1` the self-potential is at least `δ`: the barrier branch `κ(|x| - 2r)²` is at least
`16 r² > 6 r² > δ` there. -/
lemma delta_le_wellSelf_of_mem_wellBase_one (hr : 0 < r) (hδr : δ < 6 * r ^ 2) (hκ : 16 ≤ κ)
    (hx : x ∈ (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1) :
    δ ≤ wellSelf r δ κ x := by
  have hnx : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hw : wellNorm r x = ‖x‖ := wellNorm_eq_norm (by linarith)
  refine le_wellSelf ?_ ?_ <;> rw [hw]
  · nlinarith [norm_nonneg x]
  · nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 2 * r)]

/-- On `B_1` the self-potential is at most `δ + s²`. -/
lemma wellSelf_le_of_mem_wellRect_one (hr : 0 < r) (hsr : s ≤ r)
    (hx : x ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1) :
    wellSelf r δ κ x ≤ δ + s ^ 2 := by
  have hnx : ‖x‖ ≤ s := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hw : wellNorm r x = ‖x‖ := wellNorm_eq_norm (by linarith)
  refine (wellSelf_le_first r δ κ x).trans ?_
  rw [hw]
  nlinarith [norm_nonneg x]

/-- On `B_0` the self-potential is at most `δ/6`. -/
lemma wellSelf_le_of_mem_wellRect_zero (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < 6 * r ^ 2)
    (hκ : 16 ≤ κ) (hz : ‖z‖ = 2 * r)
    (hx : x ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0) :
    wellSelf r δ κ x ≤ δ / 6 := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hsq' := sq_sub_le_of_mem_wellRect_zero hδ.le hκ0 hz hx
  have hdist : ‖x - z‖ ≤ Real.sqrt (δ / (6 * κ)) := by
    simpa [mem_closedBall, dist_eq_norm] using hx
  have hnx : ‖x‖ ≤ 3 * r := by
    have h1 : ‖x‖ - 2 * r ≤ |‖x‖ - 2 * r| := le_abs_self _
    have h2 : |‖x‖ - 2 * r| ≤ Real.sqrt (δ / (6 * κ)) := by
      rw [← hz]; exact (abs_norm_sub_norm_le x z).trans hdist
    have h3 := sqrt_delta_le hr hδ hδr hκ
    linarith
  have hw : wellNorm r x = ‖x‖ := wellNorm_eq_norm hnx
  refine (wellSelf_le_second r δ κ x).trans ?_
  rw [hw]
  calc κ * (‖x‖ - 2 * r) ^ 2 ≤ κ * (δ / (6 * κ)) := by nlinarith
    _ = δ / 6 := by field_simp

/-- **Off `A_0 ∪ A_1` the self-potential exceeds the barrier height `b = r²`.**  Either the
branch `δ + |x|²` exceeds `r²` because `|x| > r`, or the branch `κ(|x| - 2r)²` does because
`(|x| - 2r)² > r²/κ`. -/
lemma sq_le_wellSelf_of_notMem (hr : 0 < r) (hδ : 0 < δ) (hκ : 16 ≤ κ)
    (h0 : x ∉ (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0)
    (h1 : x ∉ (wellBase r κ : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1) :
    r ^ 2 ≤ wellSelf r δ κ x := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  have hn : r < ‖x‖ := by
    by_contra hcon
    exact h1 (by simpa [mem_closedBall, dist_eq_norm] using not_lt.1 hcon)
  have hsq : r ^ 2 / κ < (‖x‖ - 2 * r) ^ 2 := by
    by_contra hcon
    exact h0 (not_lt.1 hcon)
  have hwr : r < wellNorm r x := lt_min hn (by linarith)
  refine le_wellSelf ?_ ?_
  · nlinarith [hr.le]
  · rcases le_total ‖x‖ (3 * r) with h | h
    · rw [wellNorm_eq_norm h]
      rw [div_lt_iff₀ hκ0] at hsq
      nlinarith
    · have : wellNorm r x = 3 * r := min_eq_right h
      rw [this]
      nlinarith

/-! #### The pair potential on the rectangles -/

/-- On `B_0` the pair potential is at most `2δ/3κ`: `B_0` has diameter `2√(δ/6κ)`. -/
lemma wellPair_le_of_mem_wellRect_zero (hδ : 0 ≤ δ) (hκ : 0 < κ)
    (hx : x ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0)
    (hy : y ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 0) :
    wellPair r x y ≤ 2 * δ / (3 * κ) := by
  have hsq : Real.sqrt (δ / (6 * κ)) ^ 2 = δ / (6 * κ) := Real.sq_sqrt (by positivity)
  have hx' : ‖x - z‖ ≤ Real.sqrt (δ / (6 * κ)) := by
    simpa [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y - z‖ ≤ Real.sqrt (δ / (6 * κ)) := by
    simpa [mem_closedBall, dist_eq_norm] using hy
  have hxy : ‖x - y‖ ≤ 2 * Real.sqrt (δ / (6 * κ)) := by
    have : ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub x z y
    rw [norm_sub_rev z y] at this
    linarith
  refine (wellPair_le_sq r x y).trans ?_
  have h2 : ‖x - y‖ ^ 2 ≤ (2 * Real.sqrt (δ / (6 * κ))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hxy 2
  calc ‖x - y‖ ^ 2 ≤ (2 * Real.sqrt (δ / (6 * κ))) ^ 2 := h2
    _ = 4 * (δ / (6 * κ)) := by rw [mul_pow, hsq]; ring
    _ = 2 * δ / (3 * κ) := by field_simp; ring

/-- On `B_1` the pair potential is at most `4s²`. -/
lemma wellPair_le_of_mem_wellRect_one (hs : 0 ≤ s)
    (hx : x ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1)
    (hy : y ∈ (wellRect r δ κ s z : Fin 2 → Set (EuclideanSpace ℝ (Fin p))) 1) :
    wellPair r x y ≤ 4 * s ^ 2 := by
  have hx' : ‖x‖ ≤ s := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y‖ ≤ s := by simpa [mem_closedBall, dist_eq_norm] using hy
  refine (wellPair_le_sq r x y).trans ?_
  have hxy : ‖x - y‖ ≤ 2 * s := (norm_sub_le x y).trans (by linarith)
  nlinarith [norm_nonneg (x - y)]

/-! #### The barrier: at least two edges of `C` cross between the wells -/

/-- **The corners of the unit square, enumerated.**

Intended home: `GibbsMeasure/Specification/PeriodicGibbs.lean`, next to `cubeSiteRefl`. -/
lemma sum_univ_corner {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 2) → M) :
    ∑ c : Fin 2 → Fin 2, f c
      = f ![0, 0] + f ![0, 1] + (f ![1, 0] + f ![1, 1]) := by
  have hrep : ∀ c : Fin 2 → Fin 2, f c = f ![c 0, c 1] := by
    intro c
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [Fintype.sum_equiv (Equiv.piFinTwoEquiv fun _ : Fin 2 ↦ Fin 2) f
    (fun x ↦ f ![x.1, x.2]) hrep, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

/-- The nearest neighbour of `(a, b)` in the first direction is `(a + 1, b)`.

Intended home: `GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`. -/
lemma corner_add_single_zero (a b : Fin 2) :
    (![a, b] : Fin 2 → Fin 2) + Pi.single 0 1 = ![a + 1, b] := by
  funext i; fin_cases i <;> simp [Pi.single_apply]

/-- The nearest neighbour of `(a, b)` in the second direction is `(a, b + 1)`.

Intended home: `GibbsMeasure/Specification/PeriodicGibbsSymmetry.lean`. -/
lemma corner_add_single_one (a b : Fin 2) :
    (![a, b] : Fin 2 → Fin 2) + Pi.single 1 1 = ![a, b + 1] := by
  funext i; fin_cases i <;> simp [Pi.single_apply]

lemma wellPair_comm (r : ℝ) (x y : EuclideanSpace ℝ (Fin p)) :
    wellPair r x y = wellPair r y x := by
  rw [wellPair, wellPair, norm_sub_rev]

/-- **The interaction of Example (19.19), written out.**  The four nearest-neighbour pairs of
the unit square form the `4`-cycle `(0,0) — (1,0) — (1,1) — (0,1) — (0,0)`. -/
lemma wellCube_eq (r δ κ : ℝ) (ζ : (Fin 2 → Fin 2) → EuclideanSpace ℝ (Fin p)) :
    wellCube r δ κ ζ
      = wellPair r (ζ ![0, 0]) (ζ ![1, 0]) + wellPair r (ζ ![1, 0]) (ζ ![1, 1])
        + wellPair r (ζ ![1, 1]) (ζ ![0, 1]) + wellPair r (ζ ![0, 1]) (ζ ![0, 0])
        + (wellSelf r δ κ (ζ ![0, 0]) + wellSelf r δ κ (ζ ![0, 1])
          + (wellSelf r δ κ (ζ ![1, 0]) + wellSelf r δ κ (ζ ![1, 1]))) := by
  rw [wellCube, sum_univ_corner (fun c ↦ ∑ k : Fin 2, wellPair r (ζ c) (ζ (c + Pi.single k 1))),
    sum_univ_corner (fun c ↦ wellSelf r δ κ (ζ c))]
  simp only [Fin.sum_univ_two, corner_add_single_zero, corner_add_single_one]
  norm_num
  rw [wellPair_comm r (ζ ![0, 1]) (ζ ![1, 1]), wellPair_comm r (ζ ![1, 0]) (ζ ![0, 0]),
    wellPair_comm r (ζ ![1, 1]) (ζ ![0, 1]), wellPair_comm r (ζ ![1, 1]) (ζ ![1, 0])]
  ring

/-- **The barrier estimate, combinatorial half**: a non-constant two-colouring of a `4`-cycle
has at least two bichromatic edges.  This is what makes Georgii's barrier `b = r²` work: a
single crossing edge would give only `r²(1 - κ^{-1/2})² < r²`. -/
lemma two_mul_le_of_crossing {m u₁ u₂ u₃ u₄ : ℝ} (a b c d : Bool)
    (hne : ¬ (a = b ∧ a = c ∧ a = d)) (hm : 0 ≤ m)
    (h₁ : a ≠ b → m ≤ u₁) (h₂ : b ≠ d → m ≤ u₂) (h₃ : d ≠ c → m ≤ u₃) (h₄ : c ≠ a → m ≤ u₄)
    (hn₁ : 0 ≤ u₁) (hn₂ : 0 ≤ u₂) (hn₃ : 0 ≤ u₃) (hn₄ : 0 ≤ u₄) :
    2 * m ≤ u₁ + u₂ + u₃ + u₄ := by
  revert h₁ h₂ h₃ h₄ hne
  cases a <;> cases b <;> cases c <;> cases d <;> intros <;> simp_all <;> linarith

/-- A single site bounds `Φ_C` from below. -/
lemma wellSelf_le_wellCube (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (c₀ : Fin 2 → Fin 2) :
    wellSelf r δ κ (ζ c₀) ≤ wellCube r δ κ ζ := by
  have h1 : (0 : ℝ) ≤ (∑ c : Fin 2 → Fin 2, ∑ k : Fin 2,
      wellPair r (ζ c) (ζ (c + Pi.single k 1))) / 2 :=
    div_nonneg (Finset.sum_nonneg fun c _ ↦ Finset.sum_nonneg fun k _ ↦
      wellPair_nonneg _ _ _) (by norm_num)
  have h2 : wellSelf r δ κ (ζ c₀) ≤ ∑ c : Fin 2 → Fin 2, wellSelf r δ κ (ζ c) :=
    Finset.single_le_sum (f := fun c ↦ wellSelf r δ κ (ζ c))
      (fun i _ ↦ wellSelf_nonneg hδ hκ) (Finset.mem_univ c₀)
  rw [wellCube]
  linarith

end Wells

end MeasureTheory.GibbsMeasure

end

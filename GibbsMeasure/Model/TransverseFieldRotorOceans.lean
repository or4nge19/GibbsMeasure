/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.AnisotropicAntiferroOceans

/-!
# Georgii 18.3.7, second model: the plane rotor in a transverse field

Georgii, *Gibbs Measures and Phase Transitions*, §18.3.7, second half: "It is natural to ask what
happens when the external field is transverse to the 1-direction which is favoured by the
anisotropy."  The state space is the unit circle, the a priori measure the uniform (arc length)
measure, and the `C`-potential is **(18.35)**

`Φ_C = ∑_{{i,j} ⊆ C, |i-j|=1} [σ_{i,1}σ_{j,1} + α σ_{i,2}σ_{j,2}] - h ∑_{i ∈ C} σ_{i,2}`,

`|h| < 2(α + 1)` and `0 ≤ α < 1`; "if `h ≠ 0` we can also allow for the isotropic case `α = 1`".

## Georgii's computation, verified

Georgii asserts that "a straightforward application of Lagrange's multiplier method shows that
`φ(x, y) = x₁y₁ + α x₂y₂ - h(x₂+y₂)/2` takes its minimum at the two pairs `(v, w)` and `(w, v)`,
where `v, w ∈ E` are such that `v₁ = -w₁` and `v₂ = w₂ = h/(2 + 2α)`".  **This is correct**, and
it is proved here without Lagrange multipliers, by an exact algebraic decomposition.  Writing
`X = ⟪x, e⟫`, `p = ⟪x, f⟫` for the two coordinates of `x` (and `Y, q` for `y`),
`P = √(1 - p²) ≥ |X|`, `Q = √(1 - q²) ≥ |Y|` and `t = h/(2 + 2α)`,

`φ(x, y) - m = (XY + PQ) + (1+α)(a+b)²/4 + (1-α)(a-b)²/4 + (P-Q)²/2`,
`a = p - t`, `b = q - t`, `m = -1 - (1+α)t²`,

an identity (`transverseCore_sub_min`) in which each of the four summands is nonnegative as soon
as `-1 ≤ α ≤ 1`.  So `m` is the minimum, and it is attained exactly when all four vanish.  The
last three force `p = q = t` — for `α < 1` because `(a-b)² = (a+b)² = 0`, and for `α = 1` because
`a + b = 0` and `P = Q` give `p² = q²`, whence `4ta = 0` and `t ≠ 0` — and the first then forces
`XY = -(1 - t²)`, i.e. `X = -Y = ±√(1 - t²)`.  This is Georgii's `(v, w)`, `(w, v)`.

Georgii's hypotheses are exactly the right ones, and both are sharp.  `|h| < 2(1 + α)` is what
makes `√(1 - t²) > 0`, so that `v ≠ w` and there really are *two* ground states
(`transverseRotorVec_eq_of_sq_eq`); and `α = 1` needs `h ≠ 0` because at `α = 1`, `h = 0` the
interaction is the isotropic antiferromagnetic `⟪x, y⟫` on the plane, minimised by *every*
antipodal pair of that plane (`exists_transverseRotorBond_eq_min_isotropic`) — a continuum of
local ground states, not a stable degeneracy of order `2`.  Unlike
the sibling model (18.34), whose hypothesis `|h| < 2` is *insufficient* (see the module doc of
`GibbsMeasure/Model/AnisotropicAntiferroOceans.lean`), **(18.35) needs no erratum**: the field is
transverse to the axis favoured by the anisotropy, so it tilts the ground state instead of
competing with it, and the tilt `t = h/(2 + 2α)` is the exact minimiser for every `|h| < 2(1+α)`.

## Generality

Georgii assumes `n = 2` "for simplicity".  Nothing here needs it: `E` is the unit sphere of any
finite-dimensional real inner product space `V` and `e, f` are any orthonormal pair, Georgii's
directions `1` and `2`; the coordinates orthogonal to `e` and `f` do not occur in `Φ`, and the
inequality `⟪x, e⟫² + ⟪x, f⟫² ≤ ‖x‖²` (Bessel, `inner_sq_add_inner_sq_le`) is all that is used in
their place.  For `finrank ℝ V = 2` this is Georgii's plane rotor verbatim, with the same circle
and the same normalised arc length `sphereProb V` as
`GibbsMeasure/Model/ShlosmanRotorOceans.lean`.  The hypothesis on `α` is weakened from Georgii's
`0 ≤ α < 1`, or `α = 1` with `h ≠ 0`, to `-1 < α ≤ 1` with `α < 1 ∨ h ≠ 0`, which is what the
argument uses (`-1 < α` for the tilt to exist, `|α| ≤ 1` for the two middle squares to be
nonnegative).

## Main results

* `transverseRotorBond`, `transverseRotorCube`, `transverseRotorCube_eq_cubeBondSum` — the
  interaction (18.35) and Georgii's reduction of its minimisation to a single bond: in the plane
  every corner of `C` lies on exactly two edges, so the field distributes over the edges and `Φ_C`
  is the bond sum of `φ`.
* `transverseRotorTilt`, `transverseRotorRadius`, `transverseRotorVec` — Georgii's `t = h/(2+2α)`,
  `√(1 - t²)` and the two spins `v = √(1-t²)·e + t·f`, `w = -√(1-t²)·e + t·f`;
  `transverseRotorMin` is his minimum `m = -1 - (1+α)t² = -1 - h²/(4 + 4α)`.
* `transverseRotorMin_le_transverseRotorBond`, `transverseRotorBond_eq_min_iff` — **`φ ≥ m` with
  equality exactly at `(v, w)` and `(w, v)`**, Georgii's Lagrange computation.
* `transverseRotorVec_eq_of_sq_eq`, `exists_transverseRotorBond_eq_min_isotropic` — **both of
  Georgii's restrictions are sharp**: at `|h| = 2(α + 1)` one has `v = w`, and at `α = 1`, `h = 0`
  the pair `(f, -f)` attains `m` without being `(v, w)` or `(w, v)`.
* `transverseRotorCube_eq_min_iff`, `localGroundEnergy_transverseRotorCube` — **`Φ` has exactly
  two local ground states**, the two staggered `v`/`w` patterns `transverseRotorStagger`, and
  `m_Φ = 4m = -4 - h²/(1 + α)`.
* `isPStablePartition_transverseRotorG`, `isPhiSymmetric_transverseRotorG` — the stable
  `Φ`-symmetric partition, and `exists_localGroundStates_subset_transverseRotorG` is Georgii's
  "by continuity, `G_ε(Φ) ⊆ G_1 ∪ G_2` for small `ε`".  Georgii's neighbourhoods are the
  *staggered caps* `anisoAntiG δ e n` of (18.34), reused verbatim: `v` and `w` are separated by
  the sign of their component along the anisotropy axis `e`, so the same sets serve, with the
  threshold `1 - δ` below `√(1 - t²)` instead of below `1`.
* `eventually_two_le_encard_extremePoints_transverseRotor`,
  `eventually_exists_transverseRotor_gibbsMeasure_pair` — **Georgii's conclusion**,
  `|ex 𝒢(βΦ)| ≥ 2` for large `β`, and the two Gibbs measures with the invariances of Theorem
  (18.25): they are mutually singular, live on the ocean of their own pattern, are invariant
  under the shifts `θ_a` with `a₁ + a₂` even, and are exchanged by `r₀`, `r₁`, `r₂`, `θ_{(1,0)}`
  and `θ_{(0,1)}`.

`norm_sub_proj_pair_sq`, `inner_sq_add_inner_sq_le` and `eq_proj_pair_of_norm_sq_le` are Bessel's
inequality for a pair of orthonormal vectors and its equality case; their intended home is
Mathlib's `Analysis/InnerProductSpace/Orthonormal.lean`, where the indexed-family version
`Orthonormal.sum_inner_products_le` lives.
-/

@[expose] public section

open Filter MeasureTheory Metric ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The arithmetic behind Georgii's minimisation of `φ`

The three lemmas of this section are Georgii's "straightforward application of Lagrange's
multiplier method", carried out by an exact decomposition instead. -/

section Arithmetic

/-- **The identity behind Georgii's minimisation of (18.35).**  With `p, q` the components of the
two spins along the field direction, `P, Q ≥ 0` with `P² = 1 - p²`, `Q² = 1 - q²` the moduli of
the components along the anisotropy axis, and `t` the tilt `h/(2 + 2α)`, the shifted interaction
`-(PQ) + αpq - (1+α)t(p+q)` exceeds `-1 - (1+α)t²` by a sum of three squares. -/
lemma transverseCore_sub_min (α t p q P Q : ℝ) (hP : P ^ 2 = 1 - p ^ 2)
    (hQ : Q ^ 2 = 1 - q ^ 2) :
    (-(P * Q) + α * (p * q) - (1 + α) * t * (p + q)) - (-1 - (1 + α) * t ^ 2)
      = (1 + α) * ((p - t) + (q - t)) ^ 2 / 4 + (1 - α) * ((p - t) - (q - t)) ^ 2 / 4
        + (P - Q) ^ 2 / 2 := by
  linear_combination (-1 / 2 : ℝ) * hP + (-1 / 2 : ℝ) * hQ

/-- **Georgii's minimum of `φ` in coordinates**: for `-1 ≤ α ≤ 1` the three squares of
`transverseCore_sub_min` are nonnegative. -/
lemma min_le_transverseCore {α t p q P Q : ℝ} (hα0 : -1 ≤ α) (hα1 : α ≤ 1)
    (hP : P ^ 2 = 1 - p ^ 2) (hQ : Q ^ 2 = 1 - q ^ 2) :
    -1 - (1 + α) * t ^ 2 ≤ -(P * Q) + α * (p * q) - (1 + α) * t * (p + q) := by
  have hid := transverseCore_sub_min α t p q P Q hP hQ
  have h1 : 0 ≤ (1 + α) * ((p - t) + (q - t)) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by norm_num)
  have h2 : 0 ≤ (1 - α) * ((p - t) - (q - t)) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by norm_num)
  have h3 : 0 ≤ (P - Q) ^ 2 / 2 := by positivity
  linarith

/-- **The equality case of `min_le_transverseCore`**: Georgii's "`φ` takes its minimum at the two
pairs `(v, w)` and `(w, v)` with `v₂ = w₂ = h/(2 + 2α)`", in coordinates.  Both spins are tilted
by exactly `t`.  For `α = 1` this needs `t ≠ 0`: at `α = 1`, `h = 0` the minimum is attained on a
whole circle of antipodal pairs. -/
lemma eq_tilt_of_transverseCore_eq_min {α t p q P Q : ℝ} (hα0 : -1 < α) (hα1 : α ≤ 1)
    (hsep : α < 1 ∨ t ≠ 0) (hP : P ^ 2 = 1 - p ^ 2) (hQ : Q ^ 2 = 1 - q ^ 2)
    (heq : -(P * Q) + α * (p * q) - (1 + α) * t * (p + q) = -1 - (1 + α) * t ^ 2) :
    p = t ∧ q = t := by
  have hid := transverseCore_sub_min α t p q P Q hP hQ
  rw [heq, sub_self] at hid
  have h1 : 0 ≤ (1 + α) * ((p - t) + (q - t)) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by norm_num)
  have h2 : 0 ≤ (1 - α) * ((p - t) - (q - t)) ^ 2 / 4 :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by norm_num)
  have h3 : 0 ≤ (P - Q) ^ 2 / 2 := by positivity
  -- each of the three squares vanishes
  have e1 : (1 + α) * ((p - t) + (q - t)) ^ 2 = 0 := by linarith
  have hsum : p + q = 2 * t := by
    have hsq : ((p - t) + (q - t)) ^ 2 = 0 := by
      rcases mul_eq_zero.1 e1 with hz | hz
      · linarith
      · exact hz
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  have hPQ : P = Q := by
    have hsq : (P - Q) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linarith
  have hpq2 : p ^ 2 = q ^ 2 := by
    have : P ^ 2 = Q ^ 2 := by rw [hPQ]
    rw [hP, hQ] at this
    linarith
  have hfac : (p - q) * (p + q) = 0 := by nlinarith [hpq2]
  rcases mul_eq_zero.1 hfac with hd | hs
  · constructor <;> linarith
  · -- `p + q = 0`, hence `t = 0`; then `α < 1` and the second square gives `p = q`
    have ht0 : t = 0 := by linarith
    have hα1' : α < 1 := by
      rcases hsep with hα | ht
      · exact hα
      · exact absurd ht0 ht
    have e2 : (1 - α) * ((p - t) - (q - t)) ^ 2 = 0 := by linarith
    have hdq : p = q := by
      have hsq : ((p - t) - (q - t)) ^ 2 = 0 := by
        rcases mul_eq_zero.1 e2 with hz | hz
        · linarith
        · exact hz
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
      linarith
    constructor <;> linarith

end Arithmetic

/-! ### The plane spanned by Georgii's directions `1` and `2` -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {e f x : V}

/-- The residual of a vector after projecting onto an orthonormal pair.  (Intended home:
`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`, next to
`Orthonormal.sum_inner_products_le`, of which this is the two-vector case written without an
indexed family.) -/
lemma norm_sub_proj_pair_sq (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (x : V) :
    ‖x - ⟪x, e⟫ • e - ⟪x, f⟫ • f‖ ^ 2 = ‖x‖ ^ 2 - ⟪x, e⟫ ^ 2 - ⟪x, f⟫ ^ 2 := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hex : ⟪e, x⟫ = ⟪x, e⟫ := real_inner_comm x e
  have hfx : ⟪f, x⟫ = ⟪x, f⟫ := real_inner_comm x f
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hef, hfe, hex, hfx]
  simp only [real_inner_self_eq_norm_sq, he, hf]
  ring

/-- **Bessel's inequality for two orthonormal vectors**: the two coordinates of `x` in Georgii's
directions `1` and `2` satisfy `x₁² + x₂² ≤ ‖x‖²`, with equality exactly when `x` lies in the
plane they span (`eq_proj_pair_of_norm_sq_le`). -/
lemma inner_sq_add_inner_sq_le (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (x : V) :
    ⟪x, e⟫ ^ 2 + ⟪x, f⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := norm_sub_proj_pair_sq he hf hef x
  have h0 : (0 : ℝ) ≤ ‖x - ⟪x, e⟫ • e - ⟪x, f⟫ • f‖ ^ 2 := sq_nonneg _
  linarith

/-- The equality case of `inner_sq_add_inner_sq_le`: a vector whose two coordinates already carry
its whole norm lies in the plane spanned by the pair. -/
lemma eq_proj_pair_of_norm_sq_le (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (hx : ‖x‖ ^ 2 ≤ ⟪x, e⟫ ^ 2 + ⟪x, f⟫ ^ 2) : x = ⟪x, e⟫ • e + ⟪x, f⟫ • f := by
  have h := norm_sub_proj_pair_sq he hf hef x
  have hle : ‖x - ⟪x, e⟫ • e - ⟪x, f⟫ • f‖ ^ 2 ≤ 0 := by linarith
  have hz : ‖x - ⟪x, e⟫ • e - ⟪x, f⟫ • f‖ = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hle (sq_nonneg _))
  have := norm_eq_zero.1 hz
  rw [sub_sub, sub_eq_zero] at this
  exact this

end Plane

/-! ### Georgii's tilted ground state spins `v` and `w` -/

section Tilt

/-- **Georgii's tilt `h/(2 + 2α)`** of the local ground states of (18.35): the common component
`v₂ = w₂` of the two spins along the direction of the external field. -/
def transverseRotorTilt (α h : ℝ) : ℝ := h / (2 * (1 + α))

/-- `√(1 - t²)`, the modulus `|v₁| = |w₁|` of the components of Georgii's two ground state spins
along the anisotropy axis. -/
def transverseRotorRadius (α h : ℝ) : ℝ := Real.sqrt (1 - transverseRotorTilt α h ^ 2)

/-- **Georgii's minimum of `φ`** for (18.35): `m = -1 - (1+α)t² = -1 - h²/(4 + 4α)`. -/
def transverseRotorMin (α h : ℝ) : ℝ := -1 - (1 + α) * transverseRotorTilt α h ^ 2

variable {α h : ℝ}

lemma mul_transverseRotorTilt (hα0 : -1 < α) : (1 + α) * transverseRotorTilt α h = h / 2 := by
  have hne : (1 : ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  rw [transverseRotorTilt]
  field_simp

/-- `m = -1 - h²/(4 + 4α)`, Georgii's minimum written with the field. -/
lemma transverseRotorMin_eq (hα0 : -1 < α) :
    transverseRotorMin α h = -1 - h ^ 2 / (4 * (1 + α)) := by
  have hne : (1 : ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  rw [transverseRotorMin, transverseRotorTilt]
  field_simp
  ring

/-- **Georgii's `|h| < 2(α + 1)`** says exactly that the tilt is strictly inside `[-1, 1]`, so
that the two ground state spins are distinct. -/
lemma transverseRotorTilt_sq_lt_one (hα0 : -1 < α) (hh : h ^ 2 < 4 * (1 + α) ^ 2) :
    transverseRotorTilt α h ^ 2 < 1 := by
  have hne : (0 : ℝ) < 1 + α := by linarith
  rw [transverseRotorTilt, div_pow, div_lt_one (by positivity)]
  nlinarith

lemma transverseRotorTilt_sq_le_one (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2) :
    transverseRotorTilt α h ^ 2 ≤ 1 := by
  have hne : (0 : ℝ) < 1 + α := by linarith
  rw [transverseRotorTilt, div_pow, div_le_one (by positivity)]
  nlinarith

lemma transverseRotorRadius_nonneg : 0 ≤ transverseRotorRadius α h := Real.sqrt_nonneg _

lemma transverseRotorRadius_sq (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2) :
    transverseRotorRadius α h ^ 2 = 1 - transverseRotorTilt α h ^ 2 :=
  Real.sq_sqrt (by linarith [transverseRotorTilt_sq_le_one hα0 hh])

lemma transverseRotorRadius_pos (hα0 : -1 < α) (hh : h ^ 2 < 4 * (1 + α) ^ 2) :
    0 < transverseRotorRadius α h :=
  Real.sqrt_pos.2 (by linarith [transverseRotorTilt_sq_lt_one hα0 hh])

end Tilt

section Vec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {α h : ℝ} {e f x y : V}

variable (α h) (e f) in
/-- **Georgii's two ground state spins `v` and `w`** of (18.35): `v = √(1-t²)·e + t·f` and
`w = -√(1-t²)·e + t·f`, the two unit vectors with `v₁ = -w₁` and `v₂ = w₂ = h/(2 + 2α)`. -/
def transverseRotorVec (n : Fin 2) : V :=
  (anisoSign n * transverseRotorRadius α h) • e + transverseRotorTilt α h • f

lemma inner_transverseRotorVec_left (he : ‖e‖ = 1) (hef : ⟪e, f⟫ = 0) (n : Fin 2) :
    ⟪transverseRotorVec α h e f n, e⟫ = anisoSign n * transverseRotorRadius α h := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  rw [transverseRotorVec, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he, hfe]
  ring

lemma inner_transverseRotorVec_right (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (n : Fin 2) :
    ⟪transverseRotorVec α h e f n, f⟫ = transverseRotorTilt α h := by
  rw [transverseRotorVec, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hf, hef]
  ring

/-- Georgii's `v` and `w` are unit vectors as soon as `|h| ≤ 2(α + 1)`. -/
lemma norm_transverseRotorVec (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2) (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (n : Fin 2) : ‖transverseRotorVec α h e f n‖ = 1 := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hsign : anisoSign n * anisoSign n = 1 := by
    rcases fin_two_eq_zero_or_one n with hn | hn <;> rw [hn] <;> norm_num [anisoSign]
  have hsq : ‖transverseRotorVec α h e f n‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, transverseRotorVec]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hef, hfe]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he, hf]
    linear_combination (transverseRotorRadius α h ^ 2) * hsign + transverseRotorRadius_sq hα0 hh
  have hfac : (‖transverseRotorVec α h e f n‖ - 1) * (‖transverseRotorVec α h e f n‖ + 1) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.1 hfac with hz | hz
  · linarith
  · linarith [norm_nonneg (transverseRotorVec α h e f n)]

/-- The two ground state spins are distinct: this is Georgii's `|h| < 2(α + 1)`. -/
lemma transverseRotorVec_ne (hα0 : -1 < α) (hh : h ^ 2 < 4 * (1 + α) ^ 2) (he : ‖e‖ = 1)
    (hef : ⟪e, f⟫ = 0) {m n : Fin 2} (hmn : m ≠ n) :
    transverseRotorVec α h e f m ≠ transverseRotorVec α h e f n := by
  intro hcon
  have h1 := inner_transverseRotorVec_left (α := α) (h := h) (e := e) (f := f) he hef m
  have h2 := inner_transverseRotorVec_left (α := α) (h := h) (e := e) (f := f) he hef n
  rw [hcon, h2, anisoSign_eq_neg_of_ne hmn] at h1
  have hr := transverseRotorRadius_pos hα0 hh
  have hs : anisoSign n = 1 ∨ anisoSign n = -1 := by
    rcases fin_two_eq_zero_or_one n with hn | hn <;> rw [hn] <;> norm_num [anisoSign]
  rcases hs with hs | hs <;> rw [hs] at h1 <;> nlinarith

end Vec

/-! ### Georgii (18.35): the bond interaction and its minimum -/

section BondArith

variable {α h : ℝ}

/-- **Georgii's minimum of `φ` in coordinates**, with the field in place of the tilt. -/
lemma transverseRotorMin_le_core {p q P Q : ℝ} (hα0 : -1 < α) (hα1 : α ≤ 1)
    (hP : P ^ 2 = 1 - p ^ 2) (hQ : Q ^ 2 = 1 - q ^ 2) :
    transverseRotorMin α h ≤ -(P * Q) + α * (p * q) - h * (p + q) / 2 := by
  have hcore := min_le_transverseCore (α := α) (t := transverseRotorTilt α h) hα0.le hα1 hP hQ
  have hkey : (1 + α) * transverseRotorTilt α h * (p + q) = h * (p + q) / 2 := by
    rw [mul_transverseRotorTilt (α := α) (h := h) hα0]
    ring
  rw [transverseRotorMin]
  linarith only [hcore, hkey]

/-- **The equality case**, with the field in place of the tilt: both spins are tilted by exactly
`t = h/(2 + 2α)`. -/
lemma eq_tilt_of_core_eq_min {p q P Q : ℝ} (hα0 : -1 < α) (hα1 : α ≤ 1) (hsep : α < 1 ∨ h ≠ 0)
    (hP : P ^ 2 = 1 - p ^ 2) (hQ : Q ^ 2 = 1 - q ^ 2)
    (heq : -(P * Q) + α * (p * q) - h * (p + q) / 2 = transverseRotorMin α h) :
    p = transverseRotorTilt α h ∧ q = transverseRotorTilt α h := by
  have hkey : (1 + α) * transverseRotorTilt α h * (p + q) = h * (p + q) / 2 := by
    rw [mul_transverseRotorTilt (α := α) (h := h) hα0]
    ring
  have hsept : α < 1 ∨ transverseRotorTilt α h ≠ 0 := by
    rcases hsep with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (div_ne_zero h1 (ne_of_gt (by linarith)))
  rw [transverseRotorMin] at heq
  exact eq_tilt_of_transverseCore_eq_min hα0 hα1 hsept hP hQ (by linarith only [heq, hkey])

/-- If `XY = -r²` with `|X|, |Y| ≤ r` and `r > 0`, then `X` and `Y` are the two ends of the
diameter: this is the last step of Georgii's `v₁ = -w₁`. -/
lemma eq_or_eq_of_mul_eq_neg_sq {X Y r : ℝ} (hr : 0 < r) (hX : |X| ≤ r) (hY : |Y| ≤ r)
    (hXY : X * Y = -(r * r)) : (X = r ∧ Y = -r) ∨ (X = -r ∧ Y = r) := by
  have hX2 : X ^ 2 ≤ r ^ 2 := sq_le_sq' (abs_le.1 hX).1 (abs_le.1 hX).2
  have hY2 : Y ^ 2 ≤ r ^ 2 := sq_le_sq' (abs_le.1 hY).1 (abs_le.1 hY).2
  have hsum : 2 * r ^ 2 ≤ X ^ 2 + Y ^ 2 := by nlinarith only [sq_nonneg (X + Y), hXY]
  have hXeq : X ^ 2 = r ^ 2 := by linarith only [hsum, hX2, hY2]
  have hfacX : (X - r) * (X + r) = 0 := by nlinarith only [hXeq]
  rcases mul_eq_zero.1 hfacX with hz | hz
  · have h1 : X = r := by linarith only [hz]
    subst h1
    refine Or.inl ⟨rfl, mul_left_cancel₀ (ne_of_gt hr) ?_⟩
    rw [hXY]; ring
  · have h1 : X = -r := by linarith only [hz]
    subst h1
    refine Or.inr ⟨rfl, mul_left_cancel₀ (ne_of_gt hr) ?_⟩
    linear_combination -hXY

end BondArith

section Bond

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {α h : ℝ} {e f x y : V}

variable (α h) (e f) in
/-- **The bond interaction of Georgii (18.35)**, `φ(x, y) = x₁y₁ + α x₂y₂ - h(x₂ + y₂)/2`: the
anisotropic antiferromagnetic bond in the plane of the orthonormal pair `e, f` (Georgii's
directions `1` and `2`) together with half of the *transverse* external field at each of its two
ends.  In the plane every corner of `C` lies on exactly two edges, so summing this over the four
edges of `C` gives (18.35), `transverseRotorCube_eq_cubeBondSum`. -/
def transverseRotorBond (x y : V) : ℝ :=
  ⟪x, e⟫ * ⟪y, e⟫ + α * (⟪x, f⟫ * ⟪y, f⟫) - h * (⟪x, f⟫ + ⟪y, f⟫) / 2

lemma transverseRotorBond_comm (x y : V) :
    transverseRotorBond α h e f x y = transverseRotorBond α h e f y x := by
  rw [transverseRotorBond, transverseRotorBond]
  ring

lemma continuous_transverseRotorBond (α h : ℝ) (e f : V) :
    Continuous (Function.uncurry (transverseRotorBond α h e f)) := by
  unfold Function.uncurry transverseRotorBond
  fun_prop

/-- Bessel's inequality for the two coordinates of a *unit* spin. -/
lemma inner_sq_add_inner_sq_le_one (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (hx : ‖x‖ = 1) : ⟪x, e⟫ ^ 2 + ⟪x, f⟫ ^ 2 ≤ 1 := by
  have h := inner_sq_add_inner_sq_le he hf hef x
  rwa [hx, one_pow] at h

/-- `√(1 - x₂²)` squares back, the tilt of a unit spin being at most `1`. -/
lemma sq_sqrt_one_sub_inner_sq (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (hx : ‖x‖ = 1) :
    Real.sqrt (1 - ⟪x, f⟫ ^ 2) ^ 2 = 1 - ⟪x, f⟫ ^ 2 :=
  Real.sq_sqrt (by nlinarith only [inner_sq_add_inner_sq_le_one he hf hef hx, sq_nonneg ⟪x, e⟫])

/-- **`|x₁| ≤ √(1 - x₂²)`** for a unit spin, with equality exactly when `x` lies in the plane of
`e` and `f`. -/
lemma abs_inner_le_sqrt_one_sub (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (hx : ‖x‖ = 1) :
    |⟪x, e⟫| ≤ Real.sqrt (1 - ⟪x, f⟫ ^ 2) :=
  abs_le_of_sq_le_sq
    (by rw [sq_sqrt_one_sub_inner_sq he hf hef hx]
        linarith only [inner_sq_add_inner_sq_le_one he hf hef hx])
    (Real.sqrt_nonneg _)

/-- **Georgii's `x₁y₁ ≥ -√(1 - x₂²)√(1 - y₂²)`**: the bond interaction dominates its value in
the coordinates alone. -/
lemma core_le_transverseRotorBond (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -(Real.sqrt (1 - ⟪x, f⟫ ^ 2) * Real.sqrt (1 - ⟪y, f⟫ ^ 2)) + α * (⟪x, f⟫ * ⟪y, f⟫)
        - h * (⟪x, f⟫ + ⟪y, f⟫) / 2 ≤ transverseRotorBond α h e f x y := by
  have hXP := abs_inner_le_sqrt_one_sub he hf hef hx
  have hYQ := abs_inner_le_sqrt_one_sub he hf hef hy
  have habs : |⟪x, e⟫ * ⟪y, e⟫|
      ≤ Real.sqrt (1 - ⟪x, f⟫ ^ 2) * Real.sqrt (1 - ⟪y, f⟫ ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hXP hYQ (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [transverseRotorBond]
  linarith only [habs, neg_abs_le (⟪x, e⟫ * ⟪y, e⟫)]

/-- **`φ(v, w) = φ(w, v) = m`**: Georgii's two tilted spins realise the minimum. -/
lemma transverseRotorBond_vec (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2) (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) {m n : Fin 2} (hmn : m ≠ n) :
    transverseRotorBond α h e f (transverseRotorVec α h e f m) (transverseRotorVec α h e f n)
      = transverseRotorMin α h := by
  have hsign : anisoSign n * anisoSign n = 1 := by
    rcases fin_two_eq_zero_or_one n with hn | hn <;> rw [hn] <;> norm_num [anisoSign]
  have hr := transverseRotorRadius_sq hα0 hh
  have ht := mul_transverseRotorTilt (α := α) (h := h) hα0
  rw [transverseRotorBond, transverseRotorMin]
  simp only [inner_transverseRotorVec_left he hef, inner_transverseRotorVec_right hf hef,
    anisoSign_eq_neg_of_ne hmn]
  linear_combination (-(transverseRotorRadius α h ^ 2)) * hsign + (-1 : ℝ) * hr
    + (2 * transverseRotorTilt α h) * ht

/-- **Georgii's minimum of `φ`.**  For `-1 < α ≤ 1` the bond interaction of (18.35) is at least
`m = -1 - h²/(4 + 4α)` on unit spins. -/
theorem transverseRotorMin_le_transverseRotorBond (hα0 : -1 < α) (hα1 : α ≤ 1) (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    transverseRotorMin α h ≤ transverseRotorBond α h e f x y :=
  (transverseRotorMin_le_core hα0 hα1 (sq_sqrt_one_sub_inner_sq he hf hef hx)
    (sq_sqrt_one_sub_inner_sq he hf hef hy)).trans (core_le_transverseRotorBond he hf hef hx hy)

/-- A unit spin whose two coordinates are `(±√(1 - t²), t)` is one of Georgii's ground state
spins `v`, `w`: the two coordinates already carry the whole norm, so the spin lies in the plane
of `e` and `f`. -/
lemma eq_transverseRotorVec (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2) (he : ‖e‖ = 1)
    (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (hx : ‖x‖ = 1) {n : Fin 2}
    (h1 : ⟪x, e⟫ = anisoSign n * transverseRotorRadius α h)
    (h2 : ⟪x, f⟫ = transverseRotorTilt α h) : x = transverseRotorVec α h e f n := by
  have hsign : anisoSign n * anisoSign n = 1 := by
    rcases fin_two_eq_zero_or_one n with hn | hn <;> rw [hn] <;> norm_num [anisoSign]
  have heqn : (anisoSign n * transverseRotorRadius α h) ^ 2 + transverseRotorTilt α h ^ 2 = 1 := by
    linear_combination (transverseRotorRadius α h ^ 2) * hsign + transverseRotorRadius_sq hα0 hh
  have hnorm : ‖x‖ ^ 2 ≤ ⟪x, e⟫ ^ 2 + ⟪x, f⟫ ^ 2 := by
    rw [hx, h1, h2, one_pow, heqn]
  have hproj := eq_proj_pair_of_norm_sq_le he hf hef hnorm
  rw [hproj, h1, h2, transverseRotorVec]

/-- **Georgii's "`φ` takes its minimum at the two pairs `(v, w)` and `(w, v)`, where `v, w ∈ E`
are such that `v₁ = -w₁` and `v₂ = w₂ = h/(2 + 2α)`"** — the exact minimisers of the bond
interaction of (18.35), under Georgii's hypotheses `|h| < 2(α + 1)`, `-1 < α ≤ 1` and
`α = 1 → h ≠ 0`. -/
theorem transverseRotorBond_eq_min_iff (hα0 : -1 < α) (hα1 : α ≤ 1) (hsep : α < 1 ∨ h ≠ 0)
    (hh : h ^ 2 < 4 * (1 + α) ^ 2) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    transverseRotorBond α h e f x y = transverseRotorMin α h ↔
      (x = transverseRotorVec α h e f 0 ∧ y = transverseRotorVec α h e f 1) ∨
        (x = transverseRotorVec α h e f 1 ∧ y = transverseRotorVec α h e f 0) := by
  constructor
  · intro heq
    have hP2 := sq_sqrt_one_sub_inner_sq he hf hef hx
    have hQ2 := sq_sqrt_one_sub_inner_sq he hf hef hy
    have hlow := transverseRotorMin_le_core (h := h) hα0 hα1 hP2 hQ2
    have hup := core_le_transverseRotorBond (α := α) (h := h) he hf hef hx hy
    have hcoreq : -(Real.sqrt (1 - ⟪x, f⟫ ^ 2) * Real.sqrt (1 - ⟪y, f⟫ ^ 2))
        + α * (⟪x, f⟫ * ⟪y, f⟫) - h * (⟪x, f⟫ + ⟪y, f⟫) / 2 = transverseRotorMin α h :=
      le_antisymm (by linarith only [hup, heq]) hlow
    obtain ⟨hpt, hqt⟩ := eq_tilt_of_core_eq_min hα0 hα1 hsep hP2 hQ2 hcoreq
    -- both spins are tilted by exactly `t`, so both moduli equal the radius `√(1 - t²)`
    have hPr : Real.sqrt (1 - ⟪x, f⟫ ^ 2) = transverseRotorRadius α h := by
      rw [hpt, transverseRotorRadius]
    have hQr : Real.sqrt (1 - ⟪y, f⟫ ^ 2) = transverseRotorRadius α h := by
      rw [hqt, transverseRotorRadius]
    have hprod0 : ⟪x, e⟫ * ⟪y, e⟫
        = -(Real.sqrt (1 - ⟪x, f⟫ ^ 2) * Real.sqrt (1 - ⟪y, f⟫ ^ 2)) := by
      rw [transverseRotorBond] at heq
      linarith only [heq, hcoreq]
    have hprod : ⟪x, e⟫ * ⟪y, e⟫
        = -(transverseRotorRadius α h * transverseRotorRadius α h) := by
      rw [hprod0, hPr, hQr]
    have hXP : |⟪x, e⟫| ≤ transverseRotorRadius α h := by
      rw [← hPr]; exact abs_inner_le_sqrt_one_sub he hf hef hx
    have hYQ : |⟪y, e⟫| ≤ transverseRotorRadius α h := by
      rw [← hQr]; exact abs_inner_le_sqrt_one_sub he hf hef hy
    rcases eq_or_eq_of_mul_eq_neg_sq (transverseRotorRadius_pos hα0 hh) hXP hYQ hprod with
      ⟨hX, hY⟩ | ⟨hX, hY⟩
    · exact Or.inl ⟨eq_transverseRotorVec hα0 hh.le he hf hef hx (n := 0)
        (by rw [hX, anisoSign_zero]; ring) hpt,
        eq_transverseRotorVec hα0 hh.le he hf hef hy (n := 1)
        (by rw [hY, anisoSign_one]; ring) hqt⟩
    · exact Or.inr ⟨eq_transverseRotorVec hα0 hh.le he hf hef hx (n := 1)
        (by rw [hX, anisoSign_one]; ring) hpt,
        eq_transverseRotorVec hα0 hh.le he hf hef hy (n := 0)
        (by rw [hY, anisoSign_zero]; ring) hqt⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact transverseRotorBond_vec hα0 hh.le he hf hef (by decide)
    · exact transverseRotorBond_vec hα0 hh.le he hf hef (by decide)

end Bond

/-! ### Georgii's hypotheses are sharp -/

section Boundary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {α h : ℝ} {e f : V}

/-- **At `|h| = 2(α + 1)` the two ground state spins coincide.**  `√(1 - t²) = 0`, so
`v = w = t·f`, the candidate degeneracy is of order `1` and there is nothing to break.  This is
why Georgii's `|h| < 2(α + 1)` is strict.  (For `|h| > 2(α + 1)` the tilt `t` leaves `[-1, 1]`
and the minimum of `φ` moves to the boundary `x₂ = y₂ = ±1`, where it is again attained at the
single pair `(f, f)` resp. `(-f, -f)`; that is outside Georgii's range and is not formalised.) -/
lemma transverseRotorVec_eq_of_sq_eq (hα0 : -1 < α) (hh : h ^ 2 = 4 * (1 + α) ^ 2) (m n : Fin 2) :
    transverseRotorVec α h e f m = transverseRotorVec α h e f n := by
  have hne : (1 : ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have ht : transverseRotorTilt α h ^ 2 = 1 := by
    rw [transverseRotorTilt, div_pow, hh]
    field_simp
    ring
  have hr : transverseRotorRadius α h = 0 := by
    rw [transverseRotorRadius, ht, sub_self, Real.sqrt_zero]
  simp [transverseRotorVec, hr]

/-- **Georgii's exclusion of `α = 1, h = 0` is necessary.**  At `α = 1` and `h = 0` the bond
interaction of (18.35) is the isotropic antiferromagnetic `⟪x, y⟫` restricted to the plane of `e`
and `f`, whose minimum `m = -1` is attained at *every* antipodal pair of that plane — a continuum
of local ground states, not a stable degeneracy of order `2`.  The pair `(f, -f)` already
witnesses the failure of `transverseRotorBond_eq_min_iff`, since `v = e` and `w = -e` there. -/
theorem exists_transverseRotorBond_eq_min_isotropic (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : ⟪e, f⟫ = 0) :
    ∃ x y : V, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      transverseRotorBond 1 0 e f x y = transverseRotorMin 1 0 ∧
      ¬((x = transverseRotorVec 1 0 e f 0 ∧ y = transverseRotorVec 1 0 e f 1) ∨
        (x = transverseRotorVec 1 0 e f 1 ∧ y = transverseRotorVec 1 0 e f 0)) := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have ht0 : transverseRotorTilt (1 : ℝ) (0 : ℝ) = 0 := by rw [transverseRotorTilt]; norm_num
  have hr1 : transverseRotorRadius (1 : ℝ) (0 : ℝ) = 1 := by
    rw [transverseRotorRadius, ht0]
    norm_num
  have hv0 : transverseRotorVec (1 : ℝ) (0 : ℝ) e f 0 = e := by
    rw [transverseRotorVec, hr1, ht0, anisoSign_zero]
    module
  refine ⟨f, -f, hf, by rw [norm_neg]; exact hf, ?_, ?_⟩
  · rw [transverseRotorBond, transverseRotorMin, ht0, hfe, inner_neg_left, hfe,
      inner_neg_left, real_inner_self_eq_norm_sq, hf]
    ring
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · rw [hv0] at h1
      rw [h1, real_inner_self_eq_norm_sq, he] at hef
      norm_num at hef
    · rw [hv0] at h2
      have : ⟪(-f : V), e⟫ = 0 := by rw [inner_neg_left, hfe, neg_zero]
      rw [h2, real_inner_self_eq_norm_sq, he] at this
      norm_num at this

end Boundary

/-! ### Georgii (18.35): the cube interaction -/

section Cube

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {α h : ℝ} {e f : sphere (0 : V) 1} {d : ℕ}

variable (α h) (e f) (d) in
/-- **Georgii (18.35)**: the `C`-potential of the plane rotor with anisotropy `α` along the
direction `e` and a *transverse* external field `h` along the direction `f`, `e ⟂ f`.  The
bracket `σ_{i,1}σ_{j,1} + α σ_{i,2}σ_{j,2}` of (18.35) is the bond interaction at zero field,
`transverseRotorBond α 0 e f`; the field enters through the site sum `h ∑_{i ∈ C} σ_{i,2}`. -/
abbrev transverseRotorCube : ((Fin d → Fin 2) → sphere (0 : V) 1) → ℝ := fun ζ ↦
  cubeBondSum d
      (fun x y : sphere (0 : V) 1 ↦ transverseRotorBond α 0 (e : V) (f : V) (x : V) (y : V)) ζ
    - h * cubeSiteSum d (fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (f : V)⟫) ζ

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_transverseRotorCube : Continuous (transverseRotorCube α h e f d) := by
  refine Continuous.sub (continuous_cubeBondSum ?_) (continuous_const.mul ?_)
  · have h1 : Continuous fun p : sphere (0 : V) 1 × sphere (0 : V) 1 ↦ ((p.1 : V), (p.2 : V)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (continuous_transverseRotorBond α 0 (e : V) (f : V)).comp h1
  · unfold cubeSiteSum
    exact continuous_finsetSum _ fun c _ ↦
      (continuous_subtype_val.comp (continuous_apply c)).inner continuous_const

lemma measurable_transverseRotorCube : Measurable (transverseRotorCube α h e f d) :=
  continuous_transverseRotorCube.measurable

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Condition (iii) of Georgii (17.18)** for (18.35): invariance under the reflections of the
cube. -/
lemma transverseRotorCube_cubeRefl (k : Fin d) (ζ : (Fin d → Fin 2) → sphere (0 : V) 1) :
    transverseRotorCube α h e f d (cubeRefl (sphere (0 : V) 1) k ζ)
      = transverseRotorCube α h e f d ζ := by
  simp only [transverseRotorCube, cubeBondSum_cubeRefl, cubeSiteSum_cubeRefl]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **In the plane, (18.35) is the bond sum of `φ`**: every corner of `C` lies on exactly two of
the four edges, so the field term `h ∑_{i ∈ C} σ_{i,2}` splits over the edges.  This is Georgii's
"to find the local ground states of `Φ` it suffices to determine the minima of the function
`φ(x, y) = x₁y₁ + α x₂y₂ - h(x₂ + y₂)/2` on `E × E`". -/
lemma transverseRotorCube_eq_cubeBondSum (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    transverseRotorCube α h e f 2 ζ
      = cubeBondSum 2
          (fun x y : sphere (0 : V) 1 ↦
            transverseRotorBond α h (e : V) (f : V) (x : V) (y : V)) ζ := by
  rw [transverseRotorCube,
    cubeBondSum_two
      (fun x y : sphere (0 : V) 1 ↦ transverseRotorBond_comm (α := α) (h := 0) (x : V) (y : V)) ζ,
    cubeBondSum_two
      (fun x y : sphere (0 : V) 1 ↦ transverseRotorBond_comm (x : V) (y : V)) ζ,
    cubeSiteSum_def, sum_univ_cubeCorners]
  simp only [transverseRotorBond]
  ring

/-- **Georgii's `m_Φ = 4m`**, the lower bound: `Φ_C` is the sum of its four bonds. -/
lemma four_mul_transverseRotorMin_le (hα0 : -1 < α) (hα1 : α ≤ 1) (hef : ⟪(e : V), (f : V)⟫ = 0)
    (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    4 * transverseRotorMin α h ≤ transverseRotorCube α h e f 2 ζ := by
  rw [transverseRotorCube_eq_cubeBondSum]
  have hb := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ transverseRotorBond α h (e : V) (f : V) (x : V) (y : V))
    (m := transverseRotorMin α h) (ζ := ζ) fun c c' ↦
      transverseRotorMin_le_transverseRotorBond hα0 hα1 (norm_sphere_eq_one e)
        (norm_sphere_eq_one f) hef (norm_sphere_eq_one _) (norm_sphere_eq_one _)
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * transverseRotorMin α h))
      = 4 * transverseRotorMin α h := by push_cast; ring
  rwa [hval] at hb

/-- **`|Φ_C| ≤ 4(1 + |α| + |h|)`** for (18.35), the first alternative of condition (iv) of
(17.18). -/
lemma abs_transverseRotorCube_le (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    |transverseRotorCube α h e f 2 ζ| ≤ 4 * (1 + |α| + |h|) := by
  have hbond : ∀ x y : sphere (0 : V) 1,
      |transverseRotorBond α h (e : V) (f : V) (x : V) (y : V)| ≤ 1 + |α| + |h| := by
    intro x y
    have h1 := abs_real_inner_le_one (norm_sphere_eq_one x) (norm_sphere_eq_one e)
    have h2 := abs_real_inner_le_one (norm_sphere_eq_one y) (norm_sphere_eq_one e)
    have h3 := abs_real_inner_le_one (norm_sphere_eq_one x) (norm_sphere_eq_one f)
    have h4 := abs_real_inner_le_one (norm_sphere_eq_one y) (norm_sphere_eq_one f)
    have hAB : |⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫| ≤ 1 := by
      rw [abs_mul]
      have := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
      linarith
    have hCD : |⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫| ≤ 1 := by
      rw [abs_mul]
      have := mul_le_mul h3 h4 (abs_nonneg _) zero_le_one
      linarith
    have hb2 : |α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫)| ≤ |α| := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left hCD (abs_nonneg α)
      linarith
    have hCsum : |⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith)
    have hb3 : |h * (⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫) / 2| ≤ |h| := by
      rw [abs_div, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
      have := mul_le_mul_of_nonneg_left hCsum (abs_nonneg h)
      linarith
    have hsplit : |⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫
          + α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫)
          - h * (⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫) / 2|
        ≤ |⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫|
          + |α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫)|
          + |h * (⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫) / 2| := by
      rw [show ⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫
            + α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫)
            - h * (⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫) / 2
          = (⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫
            + α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫))
            + -(h * (⟪(x : V), (f : V)⟫ + ⟪(y : V), (f : V)⟫) / 2) from by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      have := abs_add_le (⟪(x : V), (e : V)⟫ * ⟪(y : V), (e : V)⟫)
        (α * (⟪(x : V), (f : V)⟫ * ⟪(y : V), (f : V)⟫))
      linarith
    rw [transverseRotorBond]
    linarith
  rw [transverseRotorCube_eq_cubeBondSum]
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (1 + |α| + |h|)))
      = 4 * (1 + |α| + |h|) := by push_cast; ring
  have hval' : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * (-(1 + |α| + |h|))))
      = -(4 * (1 + |α| + |h|)) := by push_cast; ring
  have hb1 := cubeBondSum_ge (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ transverseRotorBond α h (e : V) (f : V) (x : V) (y : V))
    (m := -(1 + |α| + |h|)) (ζ := ζ) fun c c' ↦ (abs_le.1 (hbond _ _)).1
  have hb2 := cubeBondSum_le (d := 2)
    (ψ := fun x y : sphere (0 : V) 1 ↦ transverseRotorBond α h (e : V) (f : V) (x : V) (y : V))
    (M := 1 + |α| + |h|) (ζ := ζ) fun c c' ↦ (abs_le.1 (hbond _ _)).2
  rw [hval] at hb2
  rw [hval'] at hb1
  exact abs_le.2 ⟨hb1, hb2⟩

end Cube

/-! ### Georgii's two local ground states of (18.35) -/

section GroundStates

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {α h : ℝ} {e f : sphere (0 : V) 1} {d : ℕ}

variable (α h) (e f) in
/-- **Georgii's two local ground states of (18.35)**, `(v w / w v)` and `(w v / v w)`: the spin
at the corner `c` is `v` when `n + c_1 + ⋯ + c_d` is even and `w` when it is odd. -/
def transverseRotorStagger (n : Fin 2) : (Fin d → Fin 2) → V :=
  fun c ↦ transverseRotorVec α h (e : V) (f : V) (n + ∑ k, c k)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma transverseRotorStagger_apply (n : Fin 2) (c : Fin d → Fin 2) :
    transverseRotorStagger α h e f n c
      = transverseRotorVec α h (e : V) (f : V) (n + ∑ k, c k) := rfl

/-- The staggered pattern is a configuration of unit spins. -/
lemma exists_sphere_transverseRotorStagger (hα0 : -1 < α) (hh : h ^ 2 ≤ 4 * (1 + α) ^ 2)
    (hef : ⟪(e : V), (f : V)⟫ = 0) (n : Fin 2) :
    ∃ ζ : (Fin d → Fin 2) → sphere (0 : V) 1,
      ∀ c, (ζ c : V) = transverseRotorStagger α h e f n c :=
  ⟨fun c ↦ ⟨transverseRotorVec α h (e : V) (f : V) (n + ∑ k, c k),
    mem_sphere_zero_iff_norm.2 (norm_transverseRotorVec hα0 hh (norm_sphere_eq_one e)
      (norm_sphere_eq_one f) hef _)⟩, fun _ ↦ rfl⟩

/-- Along an edge of the cube a staggered pattern takes the two values `v` and `w`, so every bond
of it is at the minimum. -/
lemma transverseRotorBond_stagger (hα0 : -1 < α) (hh : h ^ 2 < 4 * (1 + α) ^ 2)
    (hef : ⟪(e : V), (f : V)⟫ = 0) {n : Fin 2} {c c' : Fin d → Fin 2}
    (hcc' : (cubeGraph d).Adj c c') :
    transverseRotorBond α h (e : V) (f : V) (transverseRotorStagger α h e f n c)
      (transverseRotorStagger α h e f n c') = transverseRotorMin α h := by
  have hs : n + ∑ k, c' k = (n + ∑ k, c k) + 1 := by
    rw [sum_eq_add_one_of_adj hcc', ← add_assoc]
  have hne : ∀ m : Fin 2, m ≠ m + 1 := by decide
  rw [transverseRotorStagger_apply, transverseRotorStagger_apply, hs]
  exact transverseRotorBond_vec hα0 hh.le (norm_sphere_eq_one e) (norm_sphere_eq_one f) hef
    (hne _)

variable [Nontrivial V]

omit [Nontrivial V] in
/-- **Georgii's `Φ_C = 4m` at the staggered patterns.** -/
lemma transverseRotorCube_stagger (hα0 : -1 < α) (hα1 : α ≤ 1) (hh : h ^ 2 < 4 * (1 + α) ^ 2)
    (hef : ⟪(e : V), (f : V)⟫ = 0) {n : Fin 2} {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1}
    (hζ : ∀ c, (ζ c : V) = transverseRotorStagger α h e f n c) :
    transverseRotorCube α h e f 2 ζ = 4 * transverseRotorMin α h := by
  rw [transverseRotorCube_eq_cubeBondSum]
  have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * transverseRotorMin α h))
      = 4 * transverseRotorMin α h := by push_cast; ring
  rw [← hval]
  refine (cubeBondSum_eq_iff_forall_adj (fun a b ↦
    transverseRotorMin_le_transverseRotorBond hα0 hα1 (norm_sphere_eq_one e)
      (norm_sphere_eq_one f) hef (norm_sphere_eq_one a) (norm_sphere_eq_one b)) _).2
    fun c c' hcc' ↦ ?_
  rw [hζ c, hζ c']
  exact transverseRotorBond_stagger hα0 hh hef hcc'

omit [Nontrivial V] in
/-- **Georgii's "`Φ` has again two local ground states, namely `(v w / w v)` and `(w v / v w)`".**
The bond minimisation `transverseRotorBond_eq_min_iff` puts every spin at `v` or `w` and makes
adjacent spins differ, and the connectedness of the cube turns that into the staggered
pattern. -/
theorem transverseRotorCube_eq_min_iff (hα0 : -1 < α) (hα1 : α ≤ 1) (hsep : α < 1 ∨ h ≠ 0)
    (hh : h ^ 2 < 4 * (1 + α) ^ 2) (hef : ⟪(e : V), (f : V)⟫ = 0)
    (ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1) :
    transverseRotorCube α h e f 2 ζ = 4 * transverseRotorMin α h ↔
      ∃ n : Fin 2, ∀ c, (ζ c : V) = transverseRotorStagger α h e f n c := by
  classical
  have he := norm_sphere_eq_one e
  have hf := norm_sphere_eq_one f
  constructor
  · intro h4
    have hval : ((2 : ℝ)⁻¹ * (((2 ^ 2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) * transverseRotorMin α h))
        = 4 * transverseRotorMin α h := by push_cast; ring
    rw [transverseRotorCube_eq_cubeBondSum, ← hval] at h4
    have hall := (cubeBondSum_eq_iff_forall_adj (fun a b ↦
      transverseRotorMin_le_transverseRotorBond hα0 hα1 he hf hef (norm_sphere_eq_one a)
        (norm_sphere_eq_one b)) ζ).1 h4
    have hpair : ∀ c c', (cubeGraph 2).Adj c c' →
        ((ζ c : V) = transverseRotorVec α h (e : V) (f : V) 0 ∧
            (ζ c' : V) = transverseRotorVec α h (e : V) (f : V) 1) ∨
          ((ζ c : V) = transverseRotorVec α h (e : V) (f : V) 1 ∧
            (ζ c' : V) = transverseRotorVec α h (e : V) (f : V) 0) := fun c c' hcc' ↦
      (transverseRotorBond_eq_min_iff hα0 hα1 hsep hh he hf hef (norm_sphere_eq_one _)
        (norm_sphere_eq_one _)).1 (hall c c' hcc')
    have hinj : ∀ a b : Fin 2, transverseRotorVec α h (e : V) (f : V) a
        = transverseRotorVec α h (e : V) (f : V) b → a = b := by
      intro a b hab
      by_contra hne
      exact transverseRotorVec_ne hα0 hh he hef hne hab
    have hex : ∀ c, ∃ m : Fin 2, (ζ c : V) = transverseRotorVec α h (e : V) (f : V) m := by
      intro c
      rcases hpair c (cubeSiteRefl 0 c) (cubeGraph_adj_cubeSiteRefl_self 0 c) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact ⟨0, h1⟩
      · exact ⟨1, h1⟩
    choose g hζg using hex
    have hflip : ∀ c c', (cubeGraph 2).Adj c c' → g c' = g c + 1 := by
      intro c c' hcc'
      rcases hpair c c' hcc' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hinj (g c) 0 (by rw [← hζg c, h1]), hinj (g c') 1 (by rw [← hζg c', h2])]
        rfl
      · rw [hinj (g c) 1 (by rw [← hζg c, h1]), hinj (g c') 0 (by rw [← hζg c', h2])]
        rfl
    have hconst : ∀ c c', (cubeGraph 2).Adj c c' →
        (fun c ↦ g c + ∑ k, c k) c = (fun c ↦ g c + ∑ k, c k) c' := by
      intro c c' hcc'
      change g c + ∑ k, c k = g c' + ∑ k, c' k
      rw [hflip c c' hcc', sum_eq_add_one_of_adj hcc', fin_two_add_one_add_add_one]
    refine ⟨g 0, fun c ↦ ?_⟩
    have hc := cubeGraph_forall_eq_of_adj hconst c
    have h0 : ∑ k, (0 : Fin 2 → Fin 2) k = 0 := by simp
    rw [hζg c, transverseRotorStagger_apply]
    congr 1
    have hc' : g c + ∑ k, c k = g 0 := by
      have hcc : (fun c ↦ g c + ∑ k, c k) c = (fun c ↦ g c + ∑ k, c k) 0 := hc
      simpa [h0] using hcc
    rw [← hc', add_assoc, fin_two_add_self, add_zero]
  · rintro ⟨n, hn⟩
    exact transverseRotorCube_stagger hα0 hα1 hh hef hn

/-- **Georgii's `m_Φ = 4m = -4 - h²/(1 + α)`** for (18.35). -/
theorem localGroundEnergy_transverseRotorCube (hα0 : -1 < α) (hα1 : α ≤ 1)
    (hh : h ^ 2 < 4 * (1 + α) ^ 2) (hef : ⟪(e : V), (f : V)⟫ = 0) :
    localGroundEnergy (transverseRotorCube α h e f 2) (sphereProb V)
      = 4 * transverseRotorMin α h := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_sphere_transverseRotorStagger (d := 2) hα0 hh.le hef 0
  exact localGroundEnergy_eq_of_isOpenPosMeasure continuous_transverseRotorCube
    (four_mul_transverseRotorMin_le hα0 hα1 hef) (ζ₀ := ζ₀)
    (transverseRotorCube_stagger hα0 hα1 hh hef hζ₀)

end GroundStates

/-! ### Georgii's stable `Φ`-symmetric partition `{G_1, G_2}` for (18.35)

Georgii's neighbourhoods of the two local ground states are the *staggered caps*
`anisoAntiG δ e n = {ζ : (-1)^{n + c_1 + c_2} ⟪ζ_c, e⟫ > 1 - δ for every corner c}` of the
sibling model (18.34): his `v` and `w` differ exactly in the sign of their component along the
anisotropy axis `e`, `v₁ = -w₁ = √(1 - t²)`, so the same sets separate the two staggered
patterns.  Only the admissible range of the threshold changes: `1 - δ` must lie below
`√(1 - t²)` rather than below `1`. -/

section Partition

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V] {α h δ : ℝ} {e f : sphere (0 : V) 1}

omit [Nontrivial V] in
/-- **Each staggered ground state lies in its own cap.**  This is where Georgii's `|h| < 2(α + 1)`
is used a second time: the threshold `1 - δ` has to be below `|v₁| = √(1 - t²)`, which is positive
exactly then. -/
lemma mem_anisoAntiG_of_stagger (hδ : 1 - transverseRotorRadius α h < δ)
    (hef : ⟪(e : V), (f : V)⟫ = 0) {n : Fin 2} {ζ : (Fin 2 → Fin 2) → sphere (0 : V) 1}
    (hζ : ∀ c, (ζ c : V) = transverseRotorStagger α h e f n c) : ζ ∈ anisoAntiG δ e n := by
  intro c
  have hsq : anisoSign (n + ∑ k, c k) * anisoSign (n + ∑ k, c k) = 1 := by
    rcases fin_two_eq_zero_or_one (n + ∑ k, c k) with hm | hm <;> rw [hm] <;> norm_num [anisoSign]
  rw [hζ c, transverseRotorStagger_apply,
    inner_transverseRotorVec_left (norm_sphere_eq_one e) hef, ← mul_assoc, hsq, one_mul]
  linarith

/-- Georgii's rotation `r_0` (18.20) belongs to `I_{C,λ}(Φ)` for (18.35). -/
theorem isSymmetry_planeRot_transverseRotorCube :
    (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).IsSymmetry
      (transverseRotorCube α h e f 2) (sphereProb V) :=
  CubeTransformation.isSymmetry_of_spin_refl transverseRotorCube_cubeRefl (fun _ ↦ rfl) fun ζ ↦ by
    have hb := cubeBondSum_onCube_of_spin_refl
      (ψ := fun x y : sphere (0 : V) 1 ↦ transverseRotorBond α 0 (e : V) (f : V) (x : V) (y : V))
      (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)) (fun _ ↦ rfl) ζ
    have hs := cubeSiteSum_onCube_of_spin_refl
      (v := fun x : sphere (0 : V) 1 ↦ ⟪(x : V), (f : V)⟫)
      (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)) (fun _ ↦ rfl) ζ
    simp only [transverseRotorCube]
    rw [hb, hs]

/-- **Georgii's "`G_1` and `G_2` are related to each other by `r_0, r_1, r_2`"** for (18.35): each
reflection of the cube reverses the parity of the corners, hence exchanges the two staggered
caps. -/
theorem isPhiSymmetric_transverseRotorG :
    IsPhiSymmetric (transverseRotorCube α h e f 2) (sphereProb V) (anisoAntiG δ e) :=
  isPhiSymmetric_of_ne transverseRotorCube_cubeRefl fun _m _n hmn ↦
    ⟨CubeTransformation.refl 0, CubeTransformation.isSymmetry_refl transverseRotorCube_cubeRefl 0,
      image_onCube_refl_anisoAntiG 0 hmn⟩

section Conclusion

variable (hα0 : -1 < α) (hα1 : α ≤ 1) (hsep : α < 1 ∨ h ≠ 0) (hh : h ^ 2 < 4 * (1 + α) ^ 2)
  (hef : ⟪(e : V), (f : V)⟫ = 0) (hδ : 1 - transverseRotorRadius α h < δ)

include hα0 hα1 hsep hh hef hδ

/-- **Georgii's "by continuity, `G_ε(Φ) ⊆ G_1 ∪ G_2` when `ε > 0` is small enough"** for (18.35):
the two exact local ground states lie in the *open* set `G_1 ∪ G_2`, and `E^C` is compact. -/
theorem exists_localGroundStates_subset_transverseRotorG :
    ∃ ε > 0, localGroundStates (transverseRotorCube α h e f 2) (sphereProb V) ε
      ⊆ ⋃ n, anisoAntiG δ e n := by
  obtain ⟨ζ₀, hζ₀⟩ := exists_sphere_transverseRotorStagger (d := 2) hα0 hh.le hef 0
  refine exists_pos_localGroundStates_subset_of_compactSpace continuous_transverseRotorCube
    (four_mul_transverseRotorMin_le hα0 hα1 hef) (ζ₀ := ζ₀)
    (transverseRotorCube_stagger hα0 hα1 hh hef hζ₀)
    (isOpen_iUnion fun n ↦ isOpen_anisoAntiG n) ?_
  intro ζ hζ
  obtain ⟨n, hn⟩ := (transverseRotorCube_eq_min_iff hα0 hα1 hsep hh hef ζ).1 hζ
  exact Set.mem_iUnion.2 ⟨n, mem_anisoAntiG_of_stagger hδ hef hn⟩

variable (hδ1 : δ ≤ 1)

include hδ1

/-- **Georgii's "`{G_1, G_2}` is a stable partition of the local ground states"** for (18.35). -/
theorem isPStablePartition_transverseRotorG :
    IsPStablePartition (transverseRotorCube α h e f 2) (sphereProb V) Set.univ
      (anisoAntiG δ e) where
  exists_localGroundStates_subset :=
    exists_localGroundStates_subset_transverseRotorG hα0 hα1 hsep hh hef hδ
  pairwise_disjoint_faceRestrict k _ a := pairwise_disjoint_faceRestrict_anisoAntiG hδ1 k a

/-- **Georgii 18.3.7, the plane rotor in a transverse field (18.35).**  *Theorem (18.25) implies
that `|ex 𝒢(βΦ)| ≥ 2` when `β` is large.*

The local ground states are the two staggered `v`/`w` patterns
(`transverseRotorCube_eq_min_iff`), the partition into the two staggered caps is stable because
the patterns disagree at every corner (`isPStablePartition_transverseRotorG`), and it is
`Φ`-symmetric because each reflection `r_k` of the cube reverses the parity of the corners
(`isPhiSymmetric_transverseRotorG`).  As in the Ising antiferromagnet 18.3.2 the partition is
*not* `r`-symmetric, so this is the count in `𝒢(βΦ)`, through Corollary (7.29), and not in
`𝒢_Θ(βΦ)`. -/
theorem eventually_two_le_encard_extremePoints_transverseRotor :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * transverseRotorCube α h e f 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * transverseRotorCube α h e f 2 ζ),
      (2 : ℕ∞) ≤ ((MeasureTheory.GibbsMeasure.G (cubeGibbsSpec (sphere (0 : V) 1)
        (fun ζ ↦ β * transverseRotorCube α h e f 2 ζ) (sphereProb V) hφβ hMβ)).extremePoints
          ℝ≥0∞).encard := by
  obtain ⟨ε, hε, hGε⟩ :=
    exists_localGroundStates_subset_transverseRotorG hα0 hα1 hsep hh hef hδ
  exact eventually_le_encard_extremePoints_G (E := sphere (0 : V) 1)
    (φ := transverseRotorCube α h e f 2) (ν := sphereProb V) (Gs := anisoAntiG δ e)
    measurable_transverseRotorCube (four_mul_transverseRotorMin_le hα0 hα1 hef)
    transverseRotorCube_cubeRefl
    (isCubeConfining_univ ⟨4 * (1 + |α| + |h|), abs_transverseRotorCube_le⟩)
    (isPStablePartition_transverseRotorG hα0 hα1 hsep hh hef hδ hδ1)
    (isPhiSymmetric_transverseRotorG (α := α) (h := h) (e := e) (f := f) (δ := δ))
    measurableSet_anisoAntiG hε hGε

open Peierls in
/-- **Georgii 18.3.7, the plane rotor in a transverse field (18.35)**, the two Gibbs measures
themselves: for `β` large there are two mutually singular Gibbs measures for `βΦ`, random
perturbations of the two staggered `v`/`w` ground states, invariant under the shifts `θ_a` with
`a_1 + a_2` even and exchanged by the `Φ`-symmetries `r_0`, `r_1`, `r_2` and by the shifts
`θ_{(1,0)}`, `θ_{(0,1)}`. -/
theorem eventually_exists_transverseRotor_gibbsMeasure_pair :
    ∀ᶠ β : ℝ in atTop, ∀ (hφβ : Measurable fun ζ ↦ β * transverseRotorCube α h e f 2 ζ)
      (hMβ : ∃ M : ℝ, ∀ ζ, M ≤ β * transverseRotorCube α h e f 2 ζ),
      ∃ μ : Fin 2 → Measure ((Fin 2 → ℤ) → sphere (0 : V) 1),
        (∀ n, IsProbabilityMeasure (μ n)) ∧
        (∀ n, Specification.IsGibbsMeasure (cubeGibbsSpec (sphere (0 : V) 1)
          (fun ζ ↦ β * transverseRotorCube α h e f 2 ζ) (sphereProb V) hφβ hMβ) (μ n)) ∧
        (μ 0).MutuallySingular (μ 1) ∧
        (∀ n, μ n {ω | (latticeOceanPart (sphere (0 : V) 1) (anisoAntiG δ e n) ω).Nonempty} = 1) ∧
        (∀ (n : Fin 2) (a : Fin 2 → ℤ), Even (a 0 + a 1) →
          MeasurePreserving (shift (sphere (0 : V) 1) a).toFun (μ n) (μ n)) ∧
        (μ 0).map ((CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onLattice
          (sphere (0 : V) 1)).toFun = μ 1 ∧
        (μ 1).map ((CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).onLattice
          (sphere (0 : V) 1)).toFun = μ 0 ∧
        (∀ k : Fin 2, (μ 0).map ((CubeTransformation.refl (E := sphere (0 : V) 1) k).onLattice
          (sphere (0 : V) 1)).toFun = μ 1) ∧
        (∀ k : Fin 2, (μ 1).map ((CubeTransformation.refl (E := sphere (0 : V) 1) k).onLattice
          (sphere (0 : V) 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 1).map (shift (sphere (0 : V) 1) (Pi.single k 1)).toFun = μ 0) ∧
        (∀ k : Fin 2, (μ 0).map (shift (sphere (0 : V) 1) (Pi.single k 1)).toFun = μ 1) := by
  obtain ⟨ε, hε, hGε⟩ :=
    exists_localGroundStates_subset_transverseRotorG hα0 hα1 hsep hh hef hδ
  filter_upwards [eventually_exists_gibbsMeasure_family_shift (E := sphere (0 : V) 1)
    (φ := transverseRotorCube α h e f 2) (ν := sphereProb V) (G := anisoAntiG δ e)
    measurable_transverseRotorCube (four_mul_transverseRotorMin_le hα0 hα1 hef)
    transverseRotorCube_cubeRefl
    (isCubeConfining_univ ⟨4 * (1 + |α| + |h|), abs_transverseRotorCube_le⟩)
    (isPStablePartition_transverseRotorG hα0 hα1 hsep hh hef hδ hδ1)
    (isPhiSymmetric_transverseRotorG (α := α) (h := h) (e := e) (f := f) (δ := δ))
    measurableSet_anisoAntiG hε hGε] with β hβ hφβ hMβ
  obtain ⟨ρ, h1, h2, h3, h4, -, h6, -, h8, h9⟩ := hβ hφβ hMβ
  have hrot : (CubeTransformation.planeRot (E := sphere (0 : V) 1) (d := 0)).IsSymmetry
      (fun ζ ↦ β * transverseRotorCube α h e f 2 ζ) (sphereProb V) :=
    isSymmetry_planeRot_transverseRotorCube.const_mul transverseRotorCube_cubeRefl β
  have hrefl : ∀ k : Fin 2, (CubeTransformation.refl (E := sphere (0 : V) 1) k).IsSymmetry
      (fun ζ ↦ β * transverseRotorCube α h e f 2 ζ) (sphereProb V) := fun k ↦
    CubeTransformation.isSymmetry_refl (ν := sphereProb V)
      (fun k ζ ↦ by rw [transverseRotorCube_cubeRefl k ζ]) k
  exact ⟨ρ, h1, h2, h3 (by decide), h4,
    fun n a ha ↦ h6 n a (preimage_tauPow_anisoAntiG ha n),
    h8 0 1 _ hrot (image_onCube_planeRot_anisoAntiG (by decide)),
    h8 1 0 _ hrot (image_onCube_planeRot_anisoAntiG (by decide)),
    fun k ↦ h8 0 1 _ (hrefl k) (image_onCube_refl_anisoAntiG k (by decide)),
    fun k ↦ h8 1 0 _ (hrefl k) (image_onCube_refl_anisoAntiG k (by decide)),
    fun k ↦ h9 0 1 k (by rw [preimage_cubeRefl_anisoAntiG]; rfl),
    fun k ↦ h9 1 0 k (by rw [preimage_cubeRefl_anisoAntiG]; rfl)⟩

end Conclusion

end Partition

end MeasureTheory.GibbsMeasure

end

end

/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Data.Real.Pointwise
public import Mathlib.Topology.Order.Monotone

/-!
# One-sided directional derivatives and tangent functionals of a convex function

Let `f : E → ℝ` be convex on a real vector space `E`. For `x y : E` the difference quotient
`dirSlope f x y t = (f (x + t • y) - f x) / t` is monotone in `t` on `ℝ \ {0}`, so the one-sided
directional derivatives

* `rightDirDeriv f x y = ⨅_{t > 0} dirSlope f x y t`
* `leftDirDeriv f x y = ⨆_{t < 0} dirSlope f x y t`

exist and satisfy `leftDirDeriv ≤ rightDirDeriv`. This is Georgii, *Gibbs Measures and Phase
Transitions*, (16.2).

These are the one-sided derivatives of the line restriction `t ↦ f (x + t • y)`, so everything
about them is Mathlib's one-variable convex-derivative theory
(`Mathlib/Analysis/Convex/Deriv.lean`) transported along `ConvexOn.convexOn_line`:
`ConvexOn.dirSlope_eq_slope`, `ConvexOn.rightDirDeriv_eq_derivWithin` and
`ConvexOn.leftDirDeriv_eq_derivWithin` are the bridge, and the basic monotonicity, boundedness,
comparison and limit lemmas below are corollaries of `ConvexOn.slope_mono`,
`bddBelow_slope_lt_of_mem_interior`, `ConvexOn.rightDeriv_le_slope_of_mem_interior`,
`ConvexOn.slope_le_leftDeriv_of_mem_interior`,
`ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior` and
`ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior`. What is genuinely new here is the
several-variable, direction-wise part: sublinearity of `y ↦ rightDirDeriv f x y`, `subgradientAt`,
`negFenchel` and the Hahn–Banach construction of tangent functionals.

`y ↦ rightDirDeriv f x y` is *sublinear*: positively homogeneous and subadditive. That is the
input to the Hahn–Banach theorem behind the theory of tangent functionals:

* `subgradientAt f x = {L : E →ₗ[ℝ] ℝ | ∀ y, L y ≤ f (x + y) - f x}` is Georgii's `∂f(x)`,
  Definition (16.4)(b).

## Main results

* `ConvexOn.leftDirDeriv_le_rightDirDeriv`: **(16.2)**.
* `ConvexOn.tendsto_dirSlope_rightDirDeriv`, `ConvexOn.tendsto_dirSlope_leftDirDeriv`: the
  one-sided derivatives are limits, as (16.2) states them.
* `ConvexOn.hasDerivAt_line_of_leftDirDeriv_eq_rightDirDeriv`,
  `ConvexOn.hasDerivAt_line_add_smul_of_leftDirDeriv_eq_rightDirDeriv`,
  `ConvexOn.differentiable_line_of_leftDirDeriv_eq_rightDirDeriv`: where the two one-sided
  derivatives agree, the line restriction `t ↦ f (x + t • y)` has a genuine two-sided derivative
  `∂⁺_y f(x + t y)` — at the base point, at an arbitrary point of the line, and along the whole
  line. The two one-sided slope limits above are then limits along `𝓝[<] 0` and `𝓝[>] 0` with the
  same value, and `𝓝[≠] 0 = 𝓝[<] 0 ⊔ 𝓝[>] 0`.
* `ConvexOn.rightDirDeriv_smul`, `ConvexOn.rightDirDeriv_add_le`: sublinearity of the right
  directional derivative in the direction.
* `ConvexOn.leftDirDeriv_le_of_mem_subgradientAt`,
  `ConvexOn.le_rightDirDeriv_of_mem_subgradientAt`: **Georgii (16.6)(1)**.
* `ConvexOn.exists_mem_subgradientAt_apply_eq`: **Georgii (16.6)(2)**, Hahn–Banach; hence
  `ConvexOn.subgradientAt_nonempty` and
  `ConvexOn.leftDirDeriv_eq_rightDirDeriv_of_subgradientAt_subsingleton`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set Topology
open scoped Pointwise

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} {x y z : E}

/-! ### The difference quotient -/

/-- The difference quotient `(f (x + t • y) - f x) / t` of `f` at `x` in the direction `y`. -/
def dirSlope (f : E → ℝ) (x y : E) (t : ℝ) : ℝ := (f (x + t • y) - f x) / t

lemma dirSlope_apply (f : E → ℝ) (x y : E) (t : ℝ) :
    dirSlope f x y t = (f (x + t • y) - f x) / t := rfl

@[simp] lemma dirSlope_zero_direction (f : E → ℝ) (x : E) (t : ℝ) : dirSlope f x 0 t = 0 := by
  simp [dirSlope]

/-- The right-hand directional derivative `∂⁺_y f(x)` of Georgii (16.2). -/
def rightDirDeriv (f : E → ℝ) (x y : E) : ℝ := sInf (dirSlope f x y '' Ioi 0)

/-- The left-hand directional derivative `∂⁻_y f(x)` of Georgii (16.2). -/
def leftDirDeriv (f : E → ℝ) (x y : E) : ℝ := sSup (dirSlope f x y '' Iio 0)

/-! ### Tangent functionals -/

/-- **Georgii Definition (16.4)(b):** `L` is a *tangent functional* to `f` at `x` when
`L Ψ ≤ f (x + Ψ) - f x` for all `Ψ`; the set of these is Georgii's `∂f(x)`. For a convex `f`
this is the subgradient of `f` at `x`. -/
def subgradientAt (f : E → ℝ) (x : E) : Set (E →ₗ[ℝ] ℝ) := {L | ∀ y, L y ≤ f (x + y) - f x}

lemma mem_subgradientAt {L : E →ₗ[ℝ] ℝ} :
    L ∈ subgradientAt f x ↔ ∀ y, L y ≤ f (x + y) - f x := Iff.rfl

/-- **Georgii Definition (16.4)(a):** `L` is `f`-bounded (Georgii: `P`-bounded) when `L ≤ f + c`
for some constant `c`. -/
def IsBoundedBy (f : E → ℝ) (L : E →ₗ[ℝ] ℝ) : Prop := BddBelow (Set.range fun y ↦ f y - L y)

lemma isBoundedBy_iff {L : E →ₗ[ℝ] ℝ} :
    IsBoundedBy f L ↔ ∃ c : ℝ, ∀ y, L y ≤ f y + c := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨-c, fun y ↦ ?_⟩
    have h : c ≤ f y - L y := hc (mem_range_self y)
    linarith
  · rintro ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    rintro _ ⟨y, rfl⟩
    show -c ≤ f y - L y
    have := hc y
    linarith

/-- **Georgii (16.5):** `𝒜(L) = inf_Ψ (f Ψ - L Ψ)`, the negative of the Fenchel transform of `f`
at `L`. Georgii lets it take the value `-∞`; here it is a real number, meaningful exactly when `L`
is `f`-bounded (`IsBoundedBy`, i.e. the set below is bounded below), which is the hypothesis of
every lemma about it. -/
def negFenchel (f : E → ℝ) (L : E →ₗ[ℝ] ℝ) : ℝ := sInf (Set.range fun y ↦ f y - L y)

lemma negFenchel_le {L : E →ₗ[ℝ] ℝ} (hL : IsBoundedBy f L) (y : E) :
    negFenchel f L ≤ f y - L y := csInf_le hL (mem_range_self y)

/-- A tangent functional at `x` is exactly a linear functional at which the infimum (16.5) is
attained at `x`. -/
lemma mem_subgradientAt_iff {L : E →ₗ[ℝ] ℝ} :
    L ∈ subgradientAt f x ↔ ∀ y, f x - L x ≤ f y - L y := by
  constructor
  · intro hL y
    have := hL (y - x)
    rw [add_sub_cancel, map_sub] at this
    linarith
  · intro hL y
    have := hL (x + y)
    rw [map_add] at this
    linarith

/-- **Georgii, after (16.5):** every tangent functional is `f`-bounded. -/
lemma isBoundedBy_of_mem_subgradientAt {L : E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt f x) :
    IsBoundedBy f L := by
  refine ⟨f x - L x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact mem_subgradientAt_iff.1 hL y

/-- **Georgii, after (16.5):** the infimum (16.5) is attained at `x` for a functional tangent
at `x`. -/
lemma negFenchel_eq_of_mem_subgradientAt {L : E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt f x) :
    negFenchel f L = f x - L x :=
  le_antisymm (negFenchel_le (isBoundedBy_of_mem_subgradientAt hL) x)
    (le_csInf ⟨_, mem_range_self x⟩ (by rintro _ ⟨y, rfl⟩; exact mem_subgradientAt_iff.1 hL y))

namespace ConvexOn

variable (hf : ConvexOn ℝ (univ : Set E) f)
include hf

/-- The restriction of a convex function to the line `t ↦ x + t • y` is convex. -/
lemma convexOn_line (x y : E) : ConvexOn ℝ (univ : Set ℝ) fun t : ℝ ↦ f (x + t • y) := by
  have := hf.comp_affineMap (AffineMap.lineMap x (x + y))
  simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using this

omit hf in
/-- The difference quotient of `f` at `x` in the direction `y` is the slope at `0` of the
restriction of `f` to the line `t ↦ x + t • y`. This identifies `dirSlope` with Mathlib's
`slope`, and hence `rightDirDeriv` / `leftDirDeriv` with Mathlib's one-sided `derivWithin`s. -/
lemma dirSlope_eq_slope (f : E → ℝ) (x y : E) :
    dirSlope f x y = slope (fun t : ℝ ↦ f (x + t • y)) 0 := by
  ext t
  rw [slope_def_field]
  simp [dirSlope]

omit hf in
private lemma sep_univ_gt (a : ℝ) : {t | t ∈ (univ : Set ℝ) ∧ a < t} = Ioi a := by
  ext t; simp

omit hf in
private lemma sep_univ_lt (a : ℝ) : {t | t ∈ (univ : Set ℝ) ∧ t < a} = Iio a := by
  ext t; simp

/-- `∂⁺_y f(x)` is Mathlib's right derivative at `0` of the line restriction
`t ↦ f (x + t • y)`. -/
lemma rightDirDeriv_eq_derivWithin (x y : E) :
    rightDirDeriv f x y = derivWithin (fun t : ℝ ↦ f (x + t • y)) (Ioi 0) 0 := by
  rw [rightDirDeriv, dirSlope_eq_slope,
    (hf.convexOn_line x y).rightDeriv_eq_sInf_slope_of_mem_interior (by simp), sep_univ_gt]

/-- `∂⁻_y f(x)` is Mathlib's left derivative at `0` of the line restriction
`t ↦ f (x + t • y)`. -/
lemma leftDirDeriv_eq_derivWithin (x y : E) :
    leftDirDeriv f x y = derivWithin (fun t : ℝ ↦ f (x + t • y)) (Iio 0) 0 := by
  rw [leftDirDeriv, dirSlope_eq_slope,
    (hf.convexOn_line x y).leftDeriv_eq_sSup_slope_of_mem_interior (by simp), sep_univ_lt]

/-- The difference quotient is monotone off `0`: Georgii's convexity argument for (16.2). This is
Mathlib's `ConvexOn.slope_mono` for the line restriction. -/
lemma monotoneOn_dirSlope (x y : E) : MonotoneOn (dirSlope f x y) {t : ℝ | t ≠ 0} := by
  rw [dirSlope_eq_slope]
  exact ((hf.convexOn_line x y).slope_mono (mem_univ 0)).mono fun t ht ↦ ⟨mem_univ t, ht⟩

lemma monotoneOn_dirSlope_Ioi (x y : E) : MonotoneOn (dirSlope f x y) (Ioi 0) :=
  (hf.monotoneOn_dirSlope x y).mono fun _ ht ↦ ne_of_gt ht

lemma monotoneOn_dirSlope_Iio (x y : E) : MonotoneOn (dirSlope f x y) (Iio 0) :=
  (hf.monotoneOn_dirSlope x y).mono fun _ ht ↦ ne_of_lt ht

/-- Every left difference quotient is at most every right difference quotient. -/
lemma dirSlope_le_dirSlope (x y : E) {s t : ℝ} (hs : s < 0) (ht : 0 < t) :
    dirSlope f x y s ≤ dirSlope f x y t :=
  hf.monotoneOn_dirSlope x y (ne_of_lt hs) (ne_of_gt ht) (hs.trans ht).le

lemma bddBelow_dirSlope_Ioi (x y : E) : BddBelow (dirSlope f x y '' Ioi 0) := by
  rw [dirSlope_eq_slope, ← sep_univ_gt (0 : ℝ)]
  exact bddBelow_slope_lt_of_mem_interior (hf.convexOn_line x y) (by simp)

lemma bddAbove_dirSlope_Iio (x y : E) : BddAbove (dirSlope f x y '' Iio 0) := by
  rw [dirSlope_eq_slope, ← sep_univ_lt (0 : ℝ)]
  exact bddAbove_slope_gt_of_mem_interior (hf.convexOn_line x y) (by simp)

/-- `∂⁺_y f(x) ≤ (f (x + t • y) - f x) / t` for every `t > 0`. -/
lemma rightDirDeriv_le_dirSlope (x y : E) {t : ℝ} (ht : 0 < t) :
    rightDirDeriv f x y ≤ dirSlope f x y t := by
  rw [hf.rightDirDeriv_eq_derivWithin, dirSlope_eq_slope]
  exact (hf.convexOn_line x y).rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ t) ht

/-- `(f (x + t • y) - f x) / t ≤ ∂⁻_y f(x)` for every `t < 0`. -/
lemma dirSlope_le_leftDirDeriv (x y : E) {t : ℝ} (ht : t < 0) :
    dirSlope f x y t ≤ leftDirDeriv f x y := by
  rw [hf.leftDirDeriv_eq_derivWithin, dirSlope_eq_slope, slope_comm]
  exact (hf.convexOn_line x y).slope_le_leftDeriv_of_mem_interior (mem_univ t) (by simp) ht

/-- **Georgii (16.2):** `∂⁻_y f(x) ≤ ∂⁺_y f(x)`. -/
lemma leftDirDeriv_le_rightDirDeriv (x y : E) :
    leftDirDeriv f x y ≤ rightDirDeriv f x y := by
  rw [hf.leftDirDeriv_eq_derivWithin, hf.rightDirDeriv_eq_derivWithin]
  exact (hf.convexOn_line x y).leftDeriv_le_rightDeriv_of_mem_interior (by simp)

/-- **Georgii (16.2):** `∂⁺_y f(x) = lim_{t ↓ 0} (f (x + t • y) - f x) / t`. -/
lemma tendsto_dirSlope_rightDirDeriv (x y : E) :
    Tendsto (dirSlope f x y) (𝓝[>] 0) (𝓝 (rightDirDeriv f x y)) := by
  rw [hf.rightDirDeriv_eq_derivWithin, dirSlope_eq_slope]
  exact (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1
    ((hf.convexOn_line x y).hasDerivWithinAt_rightDeriv_of_mem_interior (by simp))

/-- **Georgii (16.2):** `∂⁻_y f(x) = lim_{t ↑ 0} (f (x + t • y) - f x) / t`. -/
lemma tendsto_dirSlope_leftDirDeriv (x y : E) :
    Tendsto (dirSlope f x y) (𝓝[<] 0) (𝓝 (leftDirDeriv f x y)) := by
  rw [hf.leftDirDeriv_eq_derivWithin, dirSlope_eq_slope]
  exact (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).1
    ((hf.convexOn_line x y).hasDerivWithinAt_leftDeriv_of_mem_interior (by simp))


/-! ### Sublinearity of the right directional derivative -/

/-- `∂⁺_y f(x) ≤ f (x + y) - f x`: the case `t = 1`. -/
lemma rightDirDeriv_le_sub (x y : E) : rightDirDeriv f x y ≤ f (x + y) - f x := by
  simpa [dirSlope] using hf.rightDirDeriv_le_dirSlope x y one_pos

@[simp] lemma rightDirDeriv_zero_direction (x : E) : rightDirDeriv f x 0 = 0 := by
  refine le_antisymm (by simpa using hf.rightDirDeriv_le_dirSlope x 0 one_pos) ?_
  refine le_csInf ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ ?_
  rintro _ ⟨t, _, rfl⟩
  simp

omit hf in
private lemma dirSlope_neg_direction (f : E → ℝ) (x y : E) (t : ℝ) :
    dirSlope f x (-y) t = -dirSlope f x y (-t) := by
  rw [dirSlope, dirSlope, smul_neg, ← neg_smul, div_neg, neg_neg]

/-- `∂⁻_y f(x) = -∂⁺_{-y} f(x)`. -/
lemma leftDirDeriv_eq_neg_rightDirDeriv (x y : E) :
    leftDirDeriv f x y = -rightDirDeriv f x (-y) := by
  refine le_antisymm ?_ ?_
  · refine csSup_le ⟨_, ⟨-1, mem_Iio.2 (by norm_num), rfl⟩⟩ ?_
    rintro _ ⟨s, hs, rfl⟩
    have := hf.rightDirDeriv_le_dirSlope x (-y) (t := -s) (by simpa using hs)
    rw [dirSlope_neg_direction, neg_neg] at this
    linarith
  · rw [neg_le]
    refine le_csInf ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [dirSlope_neg_direction, neg_le_neg_iff]
    exact hf.dirSlope_le_leftDirDeriv x y (by simpa using ht)

omit hf in
private lemma image_dirSlope_smul (f : E → ℝ) (x y : E) {c : ℝ} (hc : 0 < c) :
    dirSlope f x (c • y) '' Ioi 0 = c • (dirSlope f x y '' Ioi 0) := by
  ext a
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_Ioi] at ht
    refine ⟨dirSlope f x y (t * c), ⟨t * c, mem_Ioi.2 (mul_pos ht hc), rfl⟩, ?_⟩
    simp only [dirSlope, smul_eq_mul, smul_smul]
    field_simp
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [mem_Ioi] at hs
    refine ⟨s / c, mem_Ioi.2 (div_pos hs hc), ?_⟩
    simp only [dirSlope, smul_eq_mul, smul_smul, div_mul_cancel₀ _ hc.ne']
    field_simp

omit hf in
/-- Positive homogeneity of `y ↦ ∂⁺_y f(x)`. -/
lemma rightDirDeriv_smul (x y : E) {c : ℝ} (hc : 0 < c) :
    rightDirDeriv f x (c • y) = c * rightDirDeriv f x y := by
  rw [rightDirDeriv, image_dirSlope_smul f x y hc, Real.sInf_smul_of_nonneg hc.le,
    smul_eq_mul, rightDirDeriv]

/-- Positive homogeneity of `y ↦ ∂⁺_y f(x)`, including `c = 0`. -/
lemma rightDirDeriv_smul_of_nonneg (x y : E) {c : ℝ} (hc : 0 ≤ c) :
    rightDirDeriv f x (c • y) = c * rightDirDeriv f x y := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [hf.rightDirDeriv_zero_direction]
  · exact rightDirDeriv_smul x y hc

/-- Half-way step to subadditivity: convexity applied at the midpoint. -/
lemma dirSlope_add_le (x y z : E) {t : ℝ} (ht : 0 < t) :
    dirSlope f x (y + z) t ≤ dirSlope f x y (2 * t) + dirSlope f x z (2 * t) := by
  have hmid : (2⁻¹ : ℝ) • (x + (2 * t) • y) + (2⁻¹ : ℝ) • (x + (2 * t) • z) = x + t • (y + z) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_add]
    module
  have hconv := hf.2 (mem_univ (x + (2 * t) • y)) (mem_univ (x + (2 * t) • z))
    (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)
  rw [hmid] at hconv
  simp only [smul_eq_mul] at hconv
  rw [dirSlope, dirSlope, dirSlope, ← sub_nonneg]
  have hrw : (f (x + (2 * t) • y) - f x) / (2 * t) + (f (x + (2 * t) • z) - f x) / (2 * t)
      - (f (x + t • (y + z)) - f x) / t
      = (f (x + (2 * t) • y) + f (x + (2 * t) • z) - 2 * f (x + t • (y + z))) / (2 * t) := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (by linarith) (by positivity)

/-- Subadditivity of `y ↦ ∂⁺_y f(x)`. -/
lemma rightDirDeriv_add_le (x y z : E) :
    rightDirDeriv f x (y + z) ≤ rightDirDeriv f x y + rightDirDeriv f x z := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨_, ⟨t₁, ht₁, rfl⟩, h₁⟩ := exists_lt_of_csInf_lt (s := dirSlope f x y '' Ioi 0)
    ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ (show rightDirDeriv f x y < rightDirDeriv f x y + ε / 2 by
      linarith)
  obtain ⟨_, ⟨t₂, ht₂, rfl⟩, h₂⟩ := exists_lt_of_csInf_lt (s := dirSlope f x z '' Ioi 0)
    ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ (show rightDirDeriv f x z < rightDirDeriv f x z + ε / 2 by
      linarith)
  rw [mem_Ioi] at ht₁ ht₂
  set t : ℝ := min t₁ t₂ / 2 with hts
  have htpos : 0 < t := by positivity
  have h2t₁ : 2 * t ≤ t₁ := by rw [hts]; rw [mul_div_cancel₀ _ (two_ne_zero)]; exact min_le_left _ _
  have h2t₂ : 2 * t ≤ t₂ := by
    rw [hts, mul_div_cancel₀ _ (two_ne_zero)]; exact min_le_right _ _
  have hy : dirSlope f x y (2 * t) ≤ dirSlope f x y t₁ :=
    hf.monotoneOn_dirSlope_Ioi x y (mem_Ioi.2 (by linarith)) (mem_Ioi.2 ht₁) h2t₁
  have hz : dirSlope f x z (2 * t) ≤ dirSlope f x z t₂ :=
    hf.monotoneOn_dirSlope_Ioi x z (mem_Ioi.2 (by linarith)) (mem_Ioi.2 ht₂) h2t₂
  have := hf.rightDirDeriv_le_dirSlope x (y + z) htpos
  have := hf.dirSlope_add_le x y z htpos
  linarith


/-! ### Tangent functionals (Georgii Definition (16.4)) -/

@[simp] lemma leftDirDeriv_zero_direction (x : E) : leftDirDeriv f x 0 = 0 := by
  simp [hf.leftDirDeriv_eq_neg_rightDirDeriv, hf.rightDirDeriv_zero_direction]

omit hf in
/-- **Georgii Remark (16.6)(1):** `L(Ψ) ≤ ∂⁺_Ψ f(x)` for every tangent functional `L`. -/
lemma le_rightDirDeriv_of_mem_subgradientAt {L : E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt f x) (y : E) :
    L y ≤ rightDirDeriv f x y := by
  refine le_csInf ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_Ioi] at ht
  have h := hL (t • y)
  rw [map_smul, smul_eq_mul] at h
  rw [dirSlope, le_div_iff₀ ht, mul_comm]
  exact h

/-- **Georgii Remark (16.6)(1):** `∂⁻_Ψ f(x) ≤ L(Ψ)` for every tangent functional `L`. -/
lemma leftDirDeriv_le_of_mem_subgradientAt {L : E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt f x) (y : E) :
    leftDirDeriv f x y ≤ L y := by
  rw [hf.leftDirDeriv_eq_neg_rightDirDeriv, neg_le]
  simpa using le_rightDirDeriv_of_mem_subgradientAt hL (-y)

/-- **Georgii Remark (16.6)(1), last sentence:** if `f` is Gateaux differentiable at `x` then it
has at most one tangent functional there. -/
lemma subgradientAt_subsingleton (h : ∀ y, leftDirDeriv f x y = rightDirDeriv f x y) :
    (subgradientAt f x).Subsingleton := fun L hL L' hL' ↦ by
  refine LinearMap.ext fun y ↦ ?_
  have h₁ := hf.leftDirDeriv_le_of_mem_subgradientAt hL y
  have h₂ := le_rightDirDeriv_of_mem_subgradientAt hL y
  have h₃ := hf.leftDirDeriv_le_of_mem_subgradientAt hL' y
  have h₄ := le_rightDirDeriv_of_mem_subgradientAt hL' y
  rw [h y] at h₁ h₃
  linarith

/-- **Georgii Remark (16.6)(2):** for every direction `y` and every `a` between the two one-sided
derivatives there is a tangent functional taking the value `a` at `y`. This is the Hahn–Banach
theorem applied to the sublinear majorant `∂⁺_· f(x)`. -/
theorem exists_mem_subgradientAt_apply_eq (x y : E) {a : ℝ}
    (ha : a ∈ Icc (leftDirDeriv f x y) (rightDirDeriv f x y)) :
    ∃ L ∈ subgradientAt f x, L y = a := by
  obtain ⟨ha₁, ha₂⟩ := ha
  have H : ∀ c : ℝ, c • y = 0 → (RingHom.id ℝ) c • a = 0 := by
    intro c hc
    rcases eq_or_ne y 0 with rfl | hy
    · rw [hf.leftDirDeriv_zero_direction] at ha₁
      rw [hf.rightDirDeriv_zero_direction] at ha₂
      rw [le_antisymm ha₂ ha₁, smul_zero]
    · rcases smul_eq_zero.1 hc with rfl | h
      · simp
      · exact absurd h hy
  have hdom : (LinearPMap.mkSpanSingleton' y a H).domain = ℝ ∙ y := rfl
  have key : ∀ v : (LinearPMap.mkSpanSingleton' y a H).domain,
      (LinearPMap.mkSpanSingleton' y a H) v ≤ rightDirDeriv f x (v : E) := by
    rintro ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hdom ▸ hv)
    simp only [LinearPMap.mkSpanSingleton'_apply, RingHom.id_apply, smul_eq_mul]
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have h1 : rightDirDeriv f x (c • y) = c * leftDirDeriv f x y := by
        have : c • y = (-c) • (-y) := by module
        rw [this, rightDirDeriv_smul x (-y) (by linarith),
          hf.leftDirDeriv_eq_neg_rightDirDeriv x y]
        ring
      rw [h1]
      exact mul_le_mul_of_nonpos_left ha₁ hc.le
    · simp [hf.rightDirDeriv_zero_direction]
    · rw [rightDirDeriv_smul x y hc]
      exact mul_le_mul_of_nonneg_left ha₂ hc.le
  obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_le_sublinear (LinearPMap.mkSpanSingleton' y a H)
    (rightDirDeriv f x) (fun c hc v ↦ rightDirDeriv_smul x v hc) (hf.rightDirDeriv_add_le x) key
  refine ⟨g, fun v ↦ (hg₂ v).trans (hf.rightDirDeriv_le_sub x v), ?_⟩
  have hy : y ∈ (LinearPMap.mkSpanSingleton' y a H).domain := by
    rw [hdom]; exact Submodule.mem_span_singleton_self y
  have := hg₁ ⟨y, hy⟩
  rwa [LinearPMap.mkSpanSingleton'_apply_self] at this

/-- **Georgii Remark (16.6)(2):** a convex function has a tangent functional at every point. -/
theorem subgradientAt_nonempty (x : E) : (subgradientAt f x).Nonempty := by
  obtain ⟨L, hL, -⟩ := hf.exists_mem_subgradientAt_apply_eq x 0
    (a := 0) (by simp [hf.leftDirDeriv_zero_direction, hf.rightDirDeriv_zero_direction])
  exact ⟨L, hL⟩

/-- **Georgii Remark (16.6)(2), last sentence:** if `f` has exactly one tangent functional `L` at
`x` then `f` is Gateaux differentiable at `x` with `∂⁻_Ψ f(x) = ∂⁺_Ψ f(x) = L(Ψ)`. -/
theorem leftDirDeriv_eq_and_rightDirDeriv_eq_of_subgradientAt_eq_singleton
    {L : E →ₗ[ℝ] ℝ} (h : subgradientAt f x = {L}) (y : E) :
    leftDirDeriv f x y = L y ∧ rightDirDeriv f x y = L y := by
  obtain ⟨L₁, hL₁, hL₁y⟩ := hf.exists_mem_subgradientAt_apply_eq x y
    ⟨le_rfl, hf.leftDirDeriv_le_rightDirDeriv x y⟩
  obtain ⟨L₂, hL₂, hL₂y⟩ := hf.exists_mem_subgradientAt_apply_eq x y
    ⟨hf.leftDirDeriv_le_rightDirDeriv x y, le_rfl⟩
  rw [h, mem_singleton_iff] at hL₁ hL₂
  subst hL₁; subst hL₂
  exact ⟨hL₁y.symm, hL₂y.symm⟩

/-- **Georgii Remark (16.6)(2), last sentence:** at most one tangent functional forces Gateaux
differentiability. -/
theorem leftDirDeriv_eq_rightDirDeriv_of_subgradientAt_subsingleton
    (h : (subgradientAt f x).Subsingleton) (y : E) :
    leftDirDeriv f x y = rightDirDeriv f x y := by
  obtain ⟨L, hL⟩ := hf.subgradientAt_nonempty x
  obtain ⟨h₁, h₂⟩ := hf.leftDirDeriv_eq_and_rightDirDeriv_eq_of_subgradientAt_eq_singleton
    (L := L) (h.eq_singleton_of_mem hL) y
  rw [h₁, h₂]


/-! ### Monotonicity of the derivative along a line -/

omit hf in
private lemma add_smul_add_sub_smul (x y : E) (t t' : ℝ) :
    x + t • y + (t' - t) • y = x + t' • y := by module

/-- Along the line through `x` in the direction `y`, the right derivative at an earlier point is
at most the left derivative at a later one. -/
lemma rightDirDeriv_le_leftDirDeriv_of_lt (x y : E) {t t' : ℝ} (h : t < t') :
    rightDirDeriv f (x + t • y) y ≤ leftDirDeriv f (x + t' • y) y := by
  have h₁ := hf.rightDirDeriv_le_dirSlope (x + t • y) y (sub_pos.2 h)
  have h₂ := hf.dirSlope_le_leftDirDeriv (x + t' • y) y (sub_neg.2 h)
  rw [dirSlope, add_smul_add_sub_smul] at h₁
  rw [dirSlope, add_smul_add_sub_smul] at h₂
  refine h₁.trans (le_trans (le_of_eq ?_) h₂)
  rw [div_eq_div_iff (by linarith) (by linarith)]
  ring

/-! ### Differentiability along a line -/

/-- **The differentiable case of Georgii (16.2).** If the two one-sided directional derivatives of
a convex function agree at `x` in the direction `y`, then the line restriction `t ↦ f (x + t • y)`
is differentiable at `0`, with derivative `∂⁺_y f(x)`.

The two one-sided limits of the difference quotient (`tendsto_dirSlope_leftDirDeriv` and
`tendsto_dirSlope_rightDirDeriv`) then have the same value, and `𝓝[≠] 0 = 𝓝[<] 0 ⊔ 𝓝[>] 0`. -/
theorem hasDerivAt_line_of_leftDirDeriv_eq_rightDirDeriv (x y : E)
    (h : leftDirDeriv f x y = rightDirDeriv f x y) :
    HasDerivAt (fun t : ℝ ↦ f (x + t • y)) (rightDirDeriv f x y) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right, ← dirSlope_eq_slope]
  refine ⟨?_, hf.tendsto_dirSlope_rightDirDeriv x y⟩
  rw [← h]
  exact hf.tendsto_dirSlope_leftDirDeriv x y

/-- `hasDerivAt_line_of_leftDirDeriv_eq_rightDirDeriv` at an arbitrary point `x + t • y` of the
line: the line restriction is differentiable at `t` as soon as the two one-sided directional
derivatives of `f` in the direction `y` agree there. -/
theorem hasDerivAt_line_add_smul_of_leftDirDeriv_eq_rightDirDeriv (x y : E) {t : ℝ}
    (h : leftDirDeriv f (x + t • y) y = rightDirDeriv f (x + t • y) y) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • y)) (rightDirDeriv f (x + t • y) y) t := by
  have hbase : HasDerivAt (fun u : ℝ ↦ f (x + t • y + u • y)) (rightDirDeriv f (x + t • y) y)
      (t - t) := by
    rw [sub_self]
    exact hf.hasDerivAt_line_of_leftDirDeriv_eq_rightDirDeriv (x + t • y) y h
  simpa only [add_smul_add_sub_smul] using hbase.comp_sub_const t t

/-- If a convex function is Gateaux differentiable in the direction `y` at every point of the line
through `x` in the direction `y`, then its restriction to that line is differentiable, with
derivative `∂⁺_y f(x + t y)` at `t` (`deriv_line_of_leftDirDeriv_eq_rightDirDeriv`). -/
theorem differentiable_line_of_leftDirDeriv_eq_rightDirDeriv (x y : E)
    (h : ∀ t : ℝ, leftDirDeriv f (x + t • y) y = rightDirDeriv f (x + t • y) y) :
    Differentiable ℝ fun t : ℝ ↦ f (x + t • y) := fun t ↦
  (hf.hasDerivAt_line_add_smul_of_leftDirDeriv_eq_rightDirDeriv x y (h t)).differentiableAt

lemma deriv_line_of_leftDirDeriv_eq_rightDirDeriv (x y : E) {t : ℝ}
    (h : leftDirDeriv f (x + t • y) y = rightDirDeriv f (x + t • y) y) :
    deriv (fun s : ℝ ↦ f (x + s • y)) t = rightDirDeriv f (x + t • y) y :=
  (hf.hasDerivAt_line_add_smul_of_leftDirDeriv_eq_rightDirDeriv x y h).deriv

end ConvexOn

/-! ### Georgii Proposition (16.3): generic Gateaux differentiability -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {K : NNReal}

/-- The auxiliary sets `G_{Ψ,n} = ⋃_{s > 0} G_{Ψ,n,s}` of Georgii's proof of (16.3). -/
def gateauxAux (f : E → ℝ) (y : E) (n : ℕ) : Set E :=
  {x : E | ∃ s > (0 : ℝ), f (x + s • y) + f (x - s • y) - 2 * f x < s / n}

namespace ConvexOn

variable (hf : ConvexOn ℝ (univ : Set E) f)
include hf

omit hf in
private lemma dirSlope_sub_dirSlope_neg (f : E → ℝ) (x y : E) {s : ℝ} (hs : 0 < s) :
    dirSlope f x y s - dirSlope f x y (-s)
      = (f (x + s • y) + f (x - s • y) - 2 * f x) / s := by
  rw [dirSlope, dirSlope, neg_smul, ← sub_eq_add_neg, div_neg, sub_neg_eq_add]
  field_simp
  ring

/-- If `f` is `K`-Lipschitz then `∂⁺_y f(x) ≤ K‖y‖`. -/
lemma rightDirDeriv_le_mul_norm (hK : LipschitzWith K f) (x y : E) :
    rightDirDeriv f x y ≤ K * ‖y‖ := by
  refine (hf.rightDirDeriv_le_sub x y).trans ?_
  have := hK.dist_le_mul (x + y) x
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at this
  exact (le_abs_self _).trans this

/-- If `f` is `K`-Lipschitz then `|∂⁺_y f(x)| ≤ K‖y‖`. -/
lemma abs_rightDirDeriv_le (hK : LipschitzWith K f) (x y : E) :
    |rightDirDeriv f x y| ≤ K * ‖y‖ := by
  refine abs_le.2 ⟨?_, hf.rightDirDeriv_le_mul_norm hK x y⟩
  have := hf.rightDirDeriv_le_mul_norm hK x (-y)
  have h2 := hf.leftDirDeriv_le_rightDirDeriv x y
  rw [hf.leftDirDeriv_eq_neg_rightDirDeriv] at h2
  rw [norm_neg] at this
  linarith

/-- If `f` is `K`-Lipschitz then so is the direction dependence of `∂⁺ f(x)`: Georgii's remark
that `Ψ ↦ ∂^±_Ψ P(Φ)` is continuous, at the start of the proof of (16.3). -/
lemma lipschitzWith_rightDirDeriv (hK : LipschitzWith K f) (x : E) :
    LipschitzWith K (rightDirDeriv f x) := by
  refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · have h₁ := hf.rightDirDeriv_add_le x z (y - z)
    have h₂ := hf.rightDirDeriv_le_mul_norm hK x (y - z)
    rw [add_sub_cancel] at h₁
    rw [← dist_eq_norm] at h₂
    linarith
  · have h₁ := hf.rightDirDeriv_add_le x y (z - y)
    have h₂ := hf.rightDirDeriv_le_mul_norm hK x (z - y)
    rw [add_sub_cancel] at h₁
    rw [← dist_eq_norm, dist_comm] at h₂
    linarith

/-- If `f` is `K`-Lipschitz then so is the direction dependence of `∂⁻ f(x)`. -/
lemma lipschitzWith_leftDirDeriv (hK : LipschitzWith K f) (x : E) :
    LipschitzWith K (leftDirDeriv f x) := by
  refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
  have h := (hf.lipschitzWith_rightDirDeriv hK x).dist_le_mul (-y) (-z)
  rw [dist_neg_neg, Real.dist_eq] at h
  rw [Real.dist_eq, hf.leftDirDeriv_eq_neg_rightDirDeriv, hf.leftDirDeriv_eq_neg_rightDirDeriv,
    neg_sub_neg, abs_sub_comm]
  exact h

/-- Georgii's second-difference criterion: if the symmetric second difference is at least `s/n`
for every `s > 0` then `∂⁺ - ∂⁻ ≥ 1/n`. -/
lemma le_rightDirDeriv_sub_leftDirDeriv (x y : E) {c : ℝ}
    (h : ∀ s > (0 : ℝ), s * c ≤ f (x + s • y) + f (x - s • y) - 2 * f x) :
    c ≤ rightDirDeriv f x y - leftDirDeriv f x y := by
  have key : ∀ s > (0 : ℝ), c ≤ dirSlope f x y s - dirSlope f x y (-s) := fun s hs ↦ by
    rw [dirSlope_sub_dirSlope_neg f x y hs, le_div_iff₀ hs, mul_comm]
    exact h s hs
  rw [le_sub_comm]
  refine csSup_le ⟨_, ⟨-1, mem_Iio.2 (by norm_num), rfl⟩⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  rw [mem_Iio] at hu
  rw [le_sub_iff_add_le]
  refine le_csInf ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩ ?_
  rintro _ ⟨t, ht, rfl⟩
  rw [mem_Ioi] at ht
  set r : ℝ := min t (-u) with hr
  have hrpos : 0 < r := lt_min ht (by linarith)
  have h₁ : dirSlope f x y r ≤ dirSlope f x y t :=
    hf.monotoneOn_dirSlope_Ioi x y (mem_Ioi.2 hrpos) (mem_Ioi.2 ht) (min_le_left _ _)
  have h₂ : dirSlope f x y u ≤ dirSlope f x y (-r) :=
    hf.monotoneOn_dirSlope_Iio x y (mem_Iio.2 hu) (mem_Iio.2 (by linarith))
      (by simp only [hr, le_neg]; exact min_le_right _ _)
  have := key r hrpos
  linarith

omit hf in
lemma gateauxAux_eq_iUnion (f : E → ℝ) (y : E) (n : ℕ) :
    gateauxAux f y n
      = ⋃ s ∈ Ioi (0 : ℝ), {x : E | f (x + s • y) + f (x - s • y) - 2 * f x < s / n} := by
  ext x
  simp [gateauxAux]

omit hf in
/-- Georgii's sets `G_{Ψ,n}` are open, because `f` is continuous. -/
lemma isOpen_gateauxAux (hK : LipschitzWith K f) (y : E) (n : ℕ) :
    IsOpen (gateauxAux f y n) := by
  rw [gateauxAux_eq_iUnion]
  refine isOpen_biUnion fun s _ ↦ ?_
  have hcont : Continuous fun x : E ↦ f (x + s • y) + f (x - s • y) - 2 * f x :=
    ((hK.continuous.comp (continuous_id.add continuous_const)).add
      (hK.continuous.comp (continuous_id.sub continuous_const))).sub
      (continuous_const.mul hK.continuous)
  exact isOpen_Iio.preimage hcont

/-- Georgii's sets `G_{Ψ,n}` are dense: otherwise the convex function `t ↦ f (x₀ + t Ψ)` would
have a jump of size at least `1/n` in its derivative at every point of an interval, which is
impossible because `f` is Lipschitz. -/
lemma dense_gateauxAux (hK : LipschitzWith K f) (y : E) {n : ℕ} (hn : 0 < n) :
    Dense (gateauxAux f y n) := by
  rw [Metric.dense_iff]
  intro x₀ ε hε
  rcases eq_or_ne y 0 with rfl | hy
  · refine ⟨x₀, Metric.mem_ball_self hε, 1, one_pos, ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < 1 / n := by positivity
    simp only [smul_zero, add_zero, sub_zero]
    linarith
  have hnorm : 0 < ‖y‖ := norm_pos_iff.2 hy
  set δ : ℝ := ε / ‖y‖ with hδdef
  have hδ : 0 < δ := div_pos hε hnorm
  by_contra hcon
  rw [not_nonempty_iff_eq_empty, eq_empty_iff_forall_notMem] at hcon
  -- every point of the segment fails to be in `G_{Ψ,n}`
  have hjump : ∀ t ∈ Ioo (-δ) δ, (n : ℝ)⁻¹ ≤
      rightDirDeriv f (x₀ + t • y) y - leftDirDeriv f (x₀ + t • y) y := by
    intro t ht
    have hmem : x₀ + t • y ∈ Metric.ball x₀ ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        ← lt_div_iff₀ hnorm]
      exact abs_lt.2 ⟨ht.1, ht.2⟩
    have hnot := hcon (x₀ + t • y)
    simp only [mem_inter_iff, hmem, true_and, gateauxAux, not_exists,
      not_and, not_lt, mem_ofPred_eq] at hnot
    refine hf.le_rightDirDeriv_sub_leftDirDeriv _ y fun s hs ↦ ?_
    rw [← div_eq_mul_inv]
    exact hnot s hs
  set g : ℝ → ℝ := fun t ↦ rightDirDeriv f (x₀ + t • y) y with hg
  have hstep : ∀ a ∈ Ioo (-δ) δ, ∀ b ∈ Ioo (-δ) δ, a < b → g a + (n : ℝ)⁻¹ ≤ g b := by
    intro a _ b hb hab
    have h₁ := hf.rightDirDeriv_le_leftDirDeriv_of_lt x₀ y hab
    have h₂ := hjump b hb
    simp only [hg]
    linarith
  have key : ∀ k : ℕ, ∀ a ∈ Ioo (-δ) δ, ∀ b ∈ Ioo (-δ) δ, a < b →
      g a + k * (n : ℝ)⁻¹ ≤ g b := by
    intro k
    induction k with
    | zero =>
      intro a _ b hb hab
      have h₁ := hf.rightDirDeriv_le_leftDirDeriv_of_lt x₀ y hab
      have h₂ := hf.leftDirDeriv_le_rightDirDeriv (x₀ + b • y) y
      simp only [hg, Nat.cast_zero, zero_mul, add_zero]
      linarith
    | succ k ih =>
      intro a ha b hb hab
      obtain ⟨m, ham, hmb⟩ := exists_between hab
      have hm : m ∈ Ioo (-δ) δ := ⟨ha.1.trans ham, hmb.trans hb.2⟩
      have h₁ := ih a ha m hm ham
      have h₂ := hstep m hm b hb hmb
      push_cast
      linarith
  have hbdd : ∀ t : ℝ, |g t| ≤ K * ‖y‖ := fun t ↦ hf.abs_rightDirDeriv_le hK _ y
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (K * ‖y‖) * n)
  have ha : (-δ / 2) ∈ Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hb : (δ / 2) ∈ Ioo (-δ) δ := ⟨by linarith, by linarith⟩
  have hmain := key k _ ha _ hb (by linarith)
  have h1 := abs_le.1 (hbdd (-δ / 2))
  have h2 := abs_le.1 (hbdd (δ / 2))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hkey : (k : ℝ) * (n : ℝ)⁻¹ ≤ 2 * (K * ‖y‖) := by linarith [h1.1, h2.2]
  have hkn : (k : ℝ) ≤ 2 * (K * ‖y‖) * n := by
    have h := mul_le_mul_of_nonneg_right hkey hnpos.le
    rwa [inv_mul_cancel_right₀ hnpos.ne'] at h
  linarith

/-- If `x ∈ G_{Ψ,n}` then the two one-sided derivatives differ by less than `1/n`. -/
lemma rightDirDeriv_sub_leftDirDeriv_lt_of_mem_gateauxAux (x y : E) {n : ℕ} (hn : 0 < n)
    (hx : x ∈ gateauxAux f y n) :
    rightDirDeriv f x y - leftDirDeriv f x y < (n : ℝ)⁻¹ := by
  obtain ⟨s, hs, hlt⟩ := hx
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h₁ := hf.rightDirDeriv_le_dirSlope x y hs
  have h₂ := hf.dirSlope_le_leftDirDeriv x y (neg_neg_iff_pos.2 hs)
  have h₃ : dirSlope f x y s - dirSlope f x y (-s)
      = (f (x + s • y) + f (x - s • y) - 2 * f x) / s := dirSlope_sub_dirSlope_neg f x y hs
  have h₄ : (f (x + s • y) + f (x - s • y) - 2 * f x) / s < (n : ℝ)⁻¹ := by
    rw [div_lt_iff₀ hs]
    calc f (x + s • y) + f (x - s • y) - 2 * f x < s / n := hlt
      _ = (n : ℝ)⁻¹ * s := div_eq_inv_mul _ _
  linarith

/-- Georgii's description of the set `G_Ψ` of points of differentiability in the direction `Ψ`
as `⋂_{n ≥ 1} G_{Ψ,n}`. -/
theorem mem_gateauxAux_iff (x y : E) :
    (∀ n : ℕ, 0 < n → x ∈ gateauxAux f y n) ↔ leftDirDeriv f x y = rightDirDeriv f x y := by
  constructor
  · intro h
    refine le_antisymm (hf.leftDirDeriv_le_rightDirDeriv x y) ?_
    rw [← sub_nonpos]
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
    have hεinv : (0 : ℝ) < ε⁻¹ := by positivity
    have hnR : (0 : ℝ) < n := hεinv.trans hn
    have hnpos : 0 < n := by exact_mod_cast hnR
    have hlt := hf.rightDirDeriv_sub_leftDirDeriv_lt_of_mem_gateauxAux x y hnpos (h n hnpos)
    have hnc : (n : ℝ)⁻¹ < ε := (inv_lt_comm₀ hε hnR).1 hn
    linarith
  · intro h n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hhalfpos : (0 : ℝ) < ((2 : ℝ) * n)⁻¹ := by positivity
    obtain ⟨_, ⟨s₁, hs₁, rfl⟩, h₁⟩ := exists_lt_of_csInf_lt (s := dirSlope f x y '' Ioi 0)
      ⟨_, ⟨1, mem_Ioi.2 one_pos, rfl⟩⟩
      (show rightDirDeriv f x y < rightDirDeriv f x y + ((2 : ℝ) * n)⁻¹ by linarith)
    obtain ⟨_, ⟨s₂, hs₂, rfl⟩, h₂⟩ := exists_lt_of_lt_csSup (s := dirSlope f x y '' Iio 0)
      ⟨_, ⟨-1, mem_Iio.2 (by norm_num), rfl⟩⟩
      (show leftDirDeriv f x y - ((2 : ℝ) * n)⁻¹ < leftDirDeriv f x y by linarith)
    rw [mem_Ioi] at hs₁
    rw [mem_Iio] at hs₂
    refine ⟨min s₁ (-s₂), lt_min hs₁ (by linarith), ?_⟩
    set s : ℝ := min s₁ (-s₂) with hsdef
    have hspos : 0 < s := lt_min hs₁ (by linarith)
    have hle₁ : dirSlope f x y s ≤ dirSlope f x y s₁ :=
      hf.monotoneOn_dirSlope_Ioi x y (mem_Ioi.2 hspos) (mem_Ioi.2 hs₁) (min_le_left _ _)
    have hle₂ : dirSlope f x y s₂ ≤ dirSlope f x y (-s) :=
      hf.monotoneOn_dirSlope_Iio x y (mem_Iio.2 hs₂) (mem_Iio.2 (by linarith))
        (by simp only [hsdef, le_neg]; exact min_le_right _ _)
    have h₃ : dirSlope f x y s - dirSlope f x y (-s)
        = (f (x + s • y) + f (x - s • y) - 2 * f x) / s := dirSlope_sub_dirSlope_neg f x y hspos
    have hhalf : ((2 : ℝ) * n)⁻¹ + ((2 : ℝ) * n)⁻¹ = (n : ℝ)⁻¹ := by
      field_simp
      ring
    have hsum : (f (x + s • y) + f (x - s • y) - 2 * f x) / s < (n : ℝ)⁻¹ := by
      rw [← h₃]
      linarith
    rw [div_lt_iff₀ hspos] at hsum
    calc f (x + s • y) + f (x - s • y) - 2 * f x < (n : ℝ)⁻¹ * s := hsum
      _ = s / n := (div_eq_inv_mul _ _).symm

variable [CompleteSpace E]

/-- **Georgii Proposition (16.3).** Let `C` be a countable set of directions. The set of points at
which the convex Lipschitz function `f` is Gateaux differentiable in all directions of `closure C`
is a dense `Gδ`; equivalently its complement is of first Baire category. -/
theorem isGδ_dense_setOf_differentiable_directions (hK : LipschitzWith K f) {C : Set E}
    (hC : C.Countable) :
    IsGδ {x : E | ∀ y ∈ closure C, leftDirDeriv f x y = rightDirDeriv f x y} ∧
      Dense {x : E | ∀ y ∈ closure C, leftDirDeriv f x y = rightDirDeriv f x y} := by
  have := hC.to_subtype
  have hD : {x : E | ∀ y ∈ closure C, leftDirDeriv f x y = rightDirDeriv f x y}
      = ⋂ p : C × ℕ, gateauxAux f (p.1 : E) (p.2 + 1) := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · rintro hx ⟨⟨y, hy⟩, n⟩
      exact (hf.mem_gateauxAux_iff x y).2 (hx y (subset_closure hy)) (n + 1) n.succ_pos
    · intro hx
      have hclosed : IsClosed {y : E | leftDirDeriv f x y = rightDirDeriv f x y} :=
        isClosed_eq (hf.lipschitzWith_leftDirDeriv hK x).continuous
          (hf.lipschitzWith_rightDirDeriv hK x).continuous
      refine closure_minimal (fun y hy ↦ ?_) hclosed
      refine (hf.mem_gateauxAux_iff x y).1 fun n hn ↦ ?_
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
      exact hx (⟨⟨y, hy⟩, m⟩ : C × ℕ)
  rw [hD]
  exact ⟨IsGδ.iInter_of_isOpen fun p ↦ isOpen_gateauxAux hK _ _,
    dense_iInter_of_isOpen (fun p ↦ isOpen_gateauxAux hK _ _)
      fun p ↦ hf.dense_gateauxAux hK _ p.2.succ_pos⟩

/-- **Mazur's theorem** (Georgii's remark after (16.3)): a convex Lipschitz function on a separable
Banach space is Gateaux differentiable on a dense `Gδ` set. -/
theorem isGδ_dense_setOf_gateauxDifferentiable [TopologicalSpace.SeparableSpace E]
    (hK : LipschitzWith K f) :
    IsGδ {x : E | ∀ y, leftDirDeriv f x y = rightDirDeriv f x y} ∧
      Dense {x : E | ∀ y, leftDirDeriv f x y = rightDirDeriv f x y} := by
  obtain ⟨C, hCcount, hCdense⟩ := TopologicalSpace.exists_countable_dense E
  have h := hf.isGδ_dense_setOf_differentiable_directions hK hCcount
  rwa [hCdense.closure_eq, show {x : E | ∀ y ∈ (univ : Set E),
    leftDirDeriv f x y = rightDirDeriv f x y}
      = {x : E | ∀ y, leftDirDeriv f x y = rightDirDeriv f x y} by simp] at h

/-! ### Georgii Proposition (16.7): tangent functionals approximate `f`-bounded ones -/

/-- **Georgii Proposition (16.7)** in the normalized case `L₀ = 0`. `C` is a closed convex cone
with vertex `0` (`0 ∈ C`, `C + C ⊆ C`, `C` convex). The point `x` is produced by Georgii's
nested-sets construction (an Ekeland variational argument) and the tangent functional `L` by
separating the strict epigraph of `f` from the cone `x + C` below the graph. -/
theorem exists_mem_subgradientAt_of_bddBelow (hcont : Continuous f)
    (hbdd : BddBelow (range f)) {C : Set E} (hC : IsClosed C) (hCconv : Convex ℝ C)
    (hC0 : (0 : E) ∈ C) (hCadd : ∀ ψ ∈ C, ∀ χ ∈ C, ψ + χ ∈ C) (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, x - x₀ ∈ C ∧ ∃ L ∈ subgradientAt f x,
      ε * ‖x - x₀‖ ≤ f x₀ - sInf (range f) ∧ ∀ ψ ∈ C, -(ε * ‖ψ‖) ≤ L ψ := by
  classical
  set F : E → Set E := fun u ↦ {v | v - u ∈ C ∧ f v ≤ f u - ε * ‖v - u‖} with hFdef
  have hmem_self : ∀ u, u ∈ F u := fun u ↦ by simp [hFdef, hC0]
  have hclosed : ∀ u, IsClosed (F u) := fun u ↦ by
    have h1 : IsClosed {v : E | v - u ∈ C} := hC.preimage (continuous_id.sub continuous_const)
    have h2 : IsClosed {v : E | f v ≤ f u - ε * ‖v - u‖} :=
      isClosed_le hcont (continuous_const.sub (continuous_const.mul
        (continuous_id.sub continuous_const).norm))
    exact h1.inter h2
  have hnest : ∀ u v, v ∈ F u → F v ⊆ F u := by
    intro u v hv w hw
    have hsplit : w - u = (w - v) + (v - u) := by abel
    refine ⟨by rw [hsplit]; exact hCadd _ hw.1 _ hv.1, ?_⟩
    have h3 : ‖w - u‖ ≤ ‖w - v‖ + ‖v - u‖ := by rw [hsplit]; exact norm_add_le _ _
    have h4 := mul_le_mul_of_nonneg_left h3 hε.le
    have h1 : f w ≤ f v - ε * ‖w - v‖ := hw.2
    have h2 : f v ≤ f u - ε * ‖v - u‖ := hv.2
    nlinarith [h1, h2, h4]
  have hbddF : ∀ u, BddBelow (f '' F u) := fun u ↦ BddBelow.mono (image_subset_range f _) hbdd
  have hchoice : ∀ (u : E) (δ : ℝ), 0 < δ → ∃ v, v ∈ F u ∧ f v < sInf (f '' F u) + δ := by
    intro u δ hδ
    obtain ⟨_, ⟨v, hv, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt
      (⟨f u, mem_image_of_mem f (hmem_self u)⟩ : (f '' F u).Nonempty)
      (show sInf (f '' F u) < sInf (f '' F u) + δ by linarith)
    exact ⟨v, hv, hlt⟩
  choose! nxt hnxt₁ hnxt₂ using hchoice
  set Φ : ℕ → E := fun n ↦ Nat.rec x₀ (fun k u ↦ nxt u (ε * (1 / 2 : ℝ) ^ k)) n with hΦdef
  have hδpos : ∀ n : ℕ, 0 < ε * (1 / 2 : ℝ) ^ n := fun n ↦ by positivity
  have hstep : ∀ n, Φ (n + 1) ∈ F (Φ n) := fun n ↦ hnxt₁ _ _ (hδpos n)
  have hstep2 : ∀ n, f (Φ (n + 1)) < sInf (f '' F (Φ n)) + ε * (1 / 2 : ℝ) ^ n := fun n ↦
    hnxt₂ _ _ (hδpos n)
  have hchain : ∀ m n, m ≤ n → Φ n ∈ F (Φ m) := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact hmem_self _
    | succ n hn ih => exact hnest _ _ ih (hstep n)
  have hdist : ∀ (v : E) (m : ℕ), v ∈ F (Φ (m + 1)) → ‖v - Φ (m + 1)‖ ≤ (1 / 2 : ℝ) ^ m := by
    intro v m hv
    have h2 : v ∈ F (Φ m) := hnest _ _ (hstep m) hv
    have h3 : sInf (f '' F (Φ m)) ≤ f v := csInf_le (hbddF _) (mem_image_of_mem f h2)
    have h4 := hstep2 m
    have h5 : f v ≤ f (Φ (m + 1)) - ε * ‖v - Φ (m + 1)‖ := hv.2
    have h6 : ε * ‖v - Φ (m + 1)‖ ≤ ε * (1 / 2 : ℝ) ^ m := by linarith
    exact le_of_mul_le_mul_left h6 hε
  have hgeom : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hcauchy : CauchySeq fun n ↦ Φ (n + 1) := by
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ 2 * (1 / 2 : ℝ) ^ N) (fun n m N hn hm ↦ ?_) ?_
    · have h1 := hdist _ N (hchain (N + 1) (n + 1) (by omega))
      have h2 := hdist _ N (hchain (N + 1) (m + 1) (by omega))
      calc dist (Φ (n + 1)) (Φ (m + 1))
          ≤ dist (Φ (n + 1)) (Φ (N + 1)) + dist (Φ (N + 1)) (Φ (m + 1)) := dist_triangle _ _ _
        _ ≤ 2 * (1 / 2 : ℝ) ^ N := by
            rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (Φ (N + 1))]
            linarith
    · simpa using hgeom.const_mul 2
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxlim : Tendsto Φ atTop (𝓝 x) := (tendsto_add_atTop_iff_nat 1).1 hx
  have hxF : ∀ n, x ∈ F (Φ n) := fun n ↦ by
    refine (hclosed (Φ n)).mem_of_tendsto hxlim ?_
    filter_upwards [eventually_ge_atTop n] with m hm using hchain n m hm
  have hx0 : x ∈ F x₀ := hxF 0
  have hFx : F x = {x} := by
    refine Set.Subset.antisymm (fun v hv ↦ ?_) (by simpa using hmem_self x)
    have hsub : ∀ m : ℕ, v ∈ F (Φ (m + 1)) := fun m ↦ hnest _ _ (hxF (m + 1)) hv
    have hz : Tendsto (fun m : ℕ ↦ Φ (m + 1) - v) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun m ↦ ?_) hgeom
      rw [norm_sub_rev]
      exact hdist v m (hsub m)
    have hten : Tendsto (fun m ↦ Φ (m + 1)) atTop (𝓝 v) := by
      simpa using hz.add (tendsto_const_nhds (x := v))
    exact mem_singleton_iff.2 (tendsto_nhds_unique hten hx)
  -- Step 2: separation
  set A : Set (E × ℝ) := {p | f p.1 < p.2} with hAdef
  set B : Set (E × ℝ) := {p | p.1 - x ∈ C ∧ p.2 ≤ f x - ε * ‖p.1 - x‖} with hBdef
  have hAopen : IsOpen A := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hAconv : Convex ℝ A := by
    rintro p hp q hq a b ha hb hab
    have h1 : f (a • p.1 + b • q.1) ≤ a * f p.1 + b * f q.1 :=
      hf.2 (mem_univ _) (mem_univ _) ha hb hab
    have hp' : f p.1 < p.2 := hp
    have hq' : f q.1 < q.2 := hq
    show f (a • p + b • q).1 < (a • p + b • q).2
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp only [zero_mul, zero_add, one_mul] at *
      linarith
    · have h2 : a * f p.1 < a * p.2 := by nlinarith
      have h3 : b * f q.1 ≤ b * q.2 := by nlinarith
      linarith
  have hBconv : Convex ℝ B := by
    rintro p hp q hq a b ha hb hab
    have hfst : (a • p + b • q).1 - x = a • (p.1 - x) + b • (q.1 - x) := by
      have : a • p.1 + b • q.1 - x
          = a • (p.1 - x) + b • (q.1 - x) + ((a + b) • x - x) := by module
      simpa [hab] using this
    refine ⟨by rw [hfst]; exact hCconv hp.1 hq.1 ha hb hab, ?_⟩
    have hnorm : ‖(a • p + b • q).1 - x‖ ≤ a * ‖p.1 - x‖ + b * ‖q.1 - x‖ := by
      rw [hfst]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg hb]
    have h1 : p.2 ≤ f x - ε * ‖p.1 - x‖ := hp.2
    have h2 : q.2 ≤ f x - ε * ‖q.1 - x‖ := hq.2
    have h3 := mul_le_mul_of_nonneg_left hnorm hε.le
    show (a • p + b • q).2 ≤ f x - ε * ‖(a • p + b • q).1 - x‖
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have k1 := mul_le_mul_of_nonneg_left h1 ha
    have k2 := mul_le_mul_of_nonneg_left h2 hb
    have e1 : a * (f x - ε * ‖p.1 - x‖) = a * f x - ε * (a * ‖p.1 - x‖) := by ring
    have e2 : b * (f x - ε * ‖q.1 - x‖) = b * f x - ε * (b * ‖q.1 - x‖) := by ring
    have e3 : ε * (a * ‖p.1 - x‖ + b * ‖q.1 - x‖)
        = ε * (a * ‖p.1 - x‖) + ε * (b * ‖q.1 - x‖) := by ring
    have e4 : a * f x + b * f x = f x := by rw [← add_mul, hab, one_mul]
    rw [e1] at k1
    rw [e2] at k2
    rw [e3] at h3
    linarith
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro ⟨ψ, t⟩ hpA hpB
    have h1 : f ψ < t := hpA
    have h2 : t ≤ f x - ε * ‖ψ - x‖ := hpB.2
    have hψ : ψ ∈ F x := ⟨hpB.1, by linarith⟩
    rw [hFx, mem_singleton_iff] at hψ
    subst hψ
    simp only [sub_self, norm_zero, mul_zero, sub_zero] at h2
    linarith
  obtain ⟨G, u, hGA, hGB⟩ := geometric_hahn_banach_open hAconv hAopen hBconv hdisj
  set Lc : E →L[ℝ] ℝ := G.comp (ContinuousLinearMap.inl ℝ E ℝ) with hLcdef
  set c : ℝ := G (0, 1) with hcdef
  have hGsplit : ∀ (ψ : E) (t : ℝ), G (ψ, t) = Lc ψ + t * c := by
    intro ψ t
    have hpair : ((ψ, t) : E × ℝ) = (ψ, 0) + t • ((0 : E), (1 : ℝ)) := by
      simp
    rw [hpair, map_add, map_smul, hLcdef, hcdef]
    simp [smul_eq_mul]
  have hBx : ((x, f x) : E × ℝ) ∈ B := by
    refine ⟨by simpa using hC0, ?_⟩
    simp
  have hu₁ : u ≤ Lc x + f x * c := by rw [← hGsplit]; exact hGB _ hBx
  have hcneg : c < 0 := by
    have h := hGA (x, f x + 1) (by show f x < f x + 1; linarith)
    rw [hGsplit] at h
    have hexp : (f x + 1) * c = f x * c + c := by ring
    linarith
  have hcne : c ≠ 0 := ne_of_lt hcneg
  have hnegc : 0 < -c := by linarith
  have hA' : ∀ ψ : E, Lc ψ + f ψ * c ≤ u := by
    intro ψ
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    have hr : 0 < δ / (-c) := div_pos hδ hnegc
    have h := hGA (ψ, f ψ + δ / (-c)) (by show f ψ < f ψ + δ / (-c); linarith)
    rw [hGsplit] at h
    have hexp : (f ψ + δ / (-c)) * c = f ψ * c + δ / (-c) * c := by ring
    have hcc : δ / (-c) * c = -δ := by field_simp
    linarith
  have hu : u = Lc x + f x * c := le_antisymm hu₁ (hA' x)
  set L : E →ₗ[ℝ] ℝ := (-c)⁻¹ • (Lc : E →ₗ[ℝ] ℝ) with hLdef
  have hLapply : ∀ ψ, L ψ = (-c)⁻¹ * Lc ψ := fun ψ ↦ rfl
  have hcinv : 0 < (-c)⁻¹ := inv_pos.2 hnegc
  have hLsub : L ∈ subgradientAt f x := by
    rw [mem_subgradientAt_iff]
    intro ψ
    have h := (hA' ψ).trans_eq hu
    have h2 := mul_le_mul_of_nonneg_left h hcinv.le
    have e1 : (-c)⁻¹ * (Lc ψ + f ψ * c) = (-c)⁻¹ * Lc ψ - f ψ := by field_simp; ring
    have e2 : (-c)⁻¹ * (Lc x + f x * c) = (-c)⁻¹ * Lc x - f x := by field_simp; ring
    rw [e1, e2] at h2
    rw [hLapply, hLapply]
    linarith
  refine ⟨x, hx0.1, L, hLsub, ?_, ?_⟩
  · have h1 : f x ≤ f x₀ - ε * ‖x - x₀‖ := hx0.2
    have h2 : sInf (range f) ≤ f x := csInf_le hbdd (mem_range_self x)
    linarith
  · intro χ hχ
    have hmemB : ((x + χ, f x - ε * ‖χ‖) : E × ℝ) ∈ B := by
      refine ⟨by simpa using hχ, ?_⟩
      simp
    have h := hGB _ hmemB
    rw [hGsplit, hu] at h
    have hLcadd : Lc (x + χ) = Lc x + Lc χ := map_add _ _ _
    rw [hLcadd] at h
    have hexp : (f x - ε * ‖χ‖) * c = f x * c - ε * ‖χ‖ * c := by ring
    have h2 : 0 ≤ Lc χ - ε * ‖χ‖ * c := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hcinv.le
    have e1 : (-c)⁻¹ * (Lc χ - ε * ‖χ‖ * c) = (-c)⁻¹ * Lc χ + ε * ‖χ‖ := by field_simp; ring
    rw [mul_zero, e1] at h3
    rw [hLapply]
    linarith

omit hf [CompleteSpace E] in
/-- An `f`-bounded linear functional is automatically bounded by the Lipschitz constant of `f`.
This is why Georgii may replace `P` by the *continuous* convex function `P - L₀` at the start of
the proof of (16.7). -/
lemma _root_.IsBoundedBy.abs_apply_le {L : E →ₗ[ℝ] ℝ} (hL : IsBoundedBy f L)
    (hK : LipschitzWith K f) (y : E) : |L y| ≤ K * ‖y‖ := by
  obtain ⟨c, hc⟩ := isBoundedBy_iff.1 hL
  have hbound : ∀ z : E, L z ≤ K * ‖z‖ := by
    intro z
    refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
    set M : ℝ := f 0 + c with hM
    set t : ℝ := max 1 (M / δ) with htdef
    have ht : (0 : ℝ) < t := lt_of_lt_of_le one_pos (le_max_left _ _)
    have htM : M / t ≤ δ := by
      rw [div_le_iff₀ ht]
      rcases le_or_gt M 0 with hM0 | hM0
      · nlinarith
      · have h := le_max_right (1 : ℝ) (M / δ)
        rw [← htdef] at h
        have h' := (div_le_iff₀ hδ).1 h
        linarith [mul_comm t δ]
    have h1 : L (t • z) ≤ f (t • z) + c := hc _
    have h2 : |f (t • z) - f 0| ≤ K * ‖t • z‖ := by
      have h := hK.dist_le_mul (t • z) 0
      rwa [Real.dist_eq, dist_zero_right] at h
    have hn : ‖t • z‖ = t * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [hn] at h2
    have h3 : f (t • z) ≤ f 0 + K * (t * ‖z‖) := by linarith [abs_le.1 h2]
    rw [map_smul, smul_eq_mul] at h1
    have h4 : t * L z ≤ M + K * (t * ‖z‖) := by rw [hM]; linarith
    have h5 : t * L z ≤ t * (M / t + K * ‖z‖) := by
      have e : t * (M / t + K * ‖z‖) = M + K * (t * ‖z‖) := by field_simp
      rw [e]; exact h4
    have h6 := le_of_mul_le_mul_left h5 ht
    linarith
  refine abs_le.2 ⟨?_, hbound y⟩
  have h := hbound (-y)
  rw [map_neg, norm_neg] at h
  linarith

omit hf [CompleteSpace E] in
/-- An `f`-bounded linear functional is continuous when `f` is Lipschitz. -/
lemma _root_.IsBoundedBy.continuous {L : E →ₗ[ℝ] ℝ} (hL : IsBoundedBy f L)
    (hK : LipschitzWith K f) : Continuous L :=
  AddMonoidHomClass.continuous_of_bound L (K : ℝ) fun y ↦ by
    rw [Real.norm_eq_abs]; exact hL.abs_apply_le hK y

/-- **Georgii Proposition (16.7).** Given an `f`-bounded functional `L₀`, a closed convex cone `C`
with vertex `0`, a point `x₀` and `ε > 0`, there is `x ∈ x₀ + C` and a tangent functional
`L ∈ ∂f(x)` with `ε‖x - x₀‖ ≤ f(x₀) - L₀(x₀) - 𝒜(L₀)` (16.8) and
`L(Ψ) ≥ L₀(Ψ) - ε‖Ψ‖` for all `Ψ ∈ C` (16.9). -/
theorem exists_mem_subgradientAt_of_isBoundedBy (hK : LipschitzWith K f) {L₀ : E →ₗ[ℝ] ℝ}
    (hL₀ : IsBoundedBy f L₀) {C : Set E} (hC : IsClosed C) (hCconv : Convex ℝ C)
    (hC0 : (0 : E) ∈ C) (hCadd : ∀ ψ ∈ C, ∀ χ ∈ C, ψ + χ ∈ C) (x₀ : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, x - x₀ ∈ C ∧ ∃ L ∈ subgradientAt f x,
      ε * ‖x - x₀‖ ≤ f x₀ - L₀ x₀ - negFenchel f L₀ ∧ ∀ ψ ∈ C, L₀ ψ - ε * ‖ψ‖ ≤ L ψ := by
  have hL₀cont : Continuous L₀ := hL₀.continuous hK
  set g : E → ℝ := fun y ↦ f y - L₀ y with hgdef
  have hgconv : ConvexOn ℝ (univ : Set E) g := hf.sub (L₀.concaveOn convex_univ)
  have hgcont : Continuous g := hK.continuous.sub hL₀cont
  have hgbdd : BddBelow (range g) := hL₀
  obtain ⟨x, hxC, L', hL'sub, h₈, h₉⟩ :=
    hgconv.exists_mem_subgradientAt_of_bddBelow hgcont hgbdd hC hCconv hC0 hCadd x₀ hε
  refine ⟨x, hxC, L' + L₀, fun ψ ↦ ?_, ?_, fun ψ hψ ↦ ?_⟩
  · have h := hL'sub ψ
    simp only [hgdef, map_add] at h
    simp only [LinearMap.add_apply]
    linarith
  · simpa only [hgdef, negFenchel, sub_sub] using h₈
  · have h := h₉ ψ hψ
    simp only [LinearMap.add_apply]
    linarith

end ConvexOn

end Normed

end

end

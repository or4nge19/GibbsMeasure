/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Data.ENNReal.Action
public import Mathlib.Data.ENNReal.Basic

/-!
# Extreme points: transport along injective linear maps, and `ℝ≥0∞` versus `ℝ≥0` scalars

* `LinearMapClass.image_openSegment`, `LinearMapClass.image_extremePoints`: an injective linear map
  over an ordered semiring carries open segments to open segments and extreme points to extreme
  points. This generalises Mathlib's `image_extremePoints`, which is stated for linear
  *equivalences* over an ordered *ring* between additive *groups*.
* `openSegment_ennreal`, `extremePoints_ennreal`: in a module over `ℝ≥0∞`, open segments and
  extreme points with `ℝ≥0∞` scalars coincide with those for the restricted `ℝ≥0` scalars (a
  convex combination `a + b = 1` in `ℝ≥0∞` has finite coefficients).
-/

@[expose] public section

open Set

variable {𝕜 E F L : Type*}

section LinearMapClass

variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E]
  [Module 𝕜 F] [FunLike L E F] [LinearMapClass L 𝕜 E F]

/-- A linear map carries an open segment onto the open segment between the images. -/
lemma LinearMapClass.image_openSegment (f : L) (x y : E) :
    f '' openSegment 𝕜 x y = openSegment 𝕜 (f x) (f y) := by
  ext z
  simp only [openSegment, mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, hab, by simp only [map_add, map_smul]⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    exact ⟨a • x + b • y, ⟨a, b, ha, hb, hab, rfl⟩, by simp only [map_add, map_smul]⟩

/-- An injective linear map carries the extreme points of `s` onto the extreme points of the image
`f '' s`. Generalises `image_extremePoints` (linear equivalences over an ordered ring). -/
lemma LinearMapClass.image_extremePoints (f : L) (hf : Function.Injective f) (s : Set E) :
    f '' s.extremePoints 𝕜 = (f '' s).extremePoints 𝕜 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_extremePoints] at hx ⊢
    refine ⟨mem_image_of_mem f hx.1, ?_⟩
    rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ hy
    rw [← LinearMapClass.image_openSegment f, hf.mem_set_image] at hy
    obtain ⟨h₁, h₂⟩ := hx.2 x₁ hx₁ x₂ hx₂ hy
    exact ⟨congrArg f h₁, congrArg f h₂⟩
  · intro hy
    rw [mem_extremePoints] at hy
    obtain ⟨⟨x, hx, rfl⟩, h⟩ := hy
    refine ⟨x, ?_, rfl⟩
    rw [mem_extremePoints]
    refine ⟨hx, fun x₁ hx₁ x₂ hx₂ hx' ↦ ?_⟩
    have := h (f x₁) (mem_image_of_mem f hx₁) (f x₂) (mem_image_of_mem f hx₂)
      (by rw [← LinearMapClass.image_openSegment f]; exact mem_image_of_mem f hx')
    exact ⟨hf this.1, hf this.2⟩

end LinearMapClass

section ENNReal

open scoped ENNReal NNReal

variable {M : Type*} [AddCommMonoid M] [Module ℝ≥0∞ M] [SMul ℝ≥0 M] [IsScalarTower ℝ≥0 ℝ≥0∞ M]

/-- In a module over `ℝ≥0∞`, any `ℝ≥0`-action compatible with it is the action of the coercion. -/
lemma nnreal_smul_eq_coe_ennreal_smul (c : ℝ≥0) (x : M) : c • x = (c : ℝ≥0∞) • x := by
  rw [← smul_one_smul ℝ≥0∞ c x, ENNReal.smul_one]

/-- In a module over `ℝ≥0∞`, open segments with `ℝ≥0∞` scalars are open segments with `ℝ≥0`
scalars: a convex combination `a + b = 1` in `ℝ≥0∞` has finite coefficients. -/
lemma openSegment_ennreal (x y : M) : openSegment ℝ≥0∞ x y = openSegment ℝ≥0 x y := by
  ext z
  simp only [openSegment, mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    lift a to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
    lift b to ℝ≥0 using ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
    refine ⟨a, b, ENNReal.coe_pos.1 ha, ENNReal.coe_pos.1 hb, ?_, ?_⟩
    · exact_mod_cast hab
    · rw [nnreal_smul_eq_coe_ennreal_smul, nnreal_smul_eq_coe_ennreal_smul]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a, b, ENNReal.coe_pos.2 ha, ENNReal.coe_pos.2 hb, ?_, ?_⟩
    · exact_mod_cast hab
    · rw [nnreal_smul_eq_coe_ennreal_smul, nnreal_smul_eq_coe_ennreal_smul]

/-- In a module over `ℝ≥0∞`, extreme points with `ℝ≥0∞` scalars are extreme points with `ℝ≥0`
scalars. -/
lemma extremePoints_ennreal (s : Set M) : s.extremePoints ℝ≥0∞ = s.extremePoints ℝ≥0 := by
  simp only [Set.extremePoints, openSegment_ennreal]

end ENNReal

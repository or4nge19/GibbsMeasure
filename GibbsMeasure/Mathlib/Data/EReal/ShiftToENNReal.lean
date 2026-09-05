/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# The order isomorphism `[a, ∞] ≃o [0, ∞]` of `EReal` with `ℝ≥0∞`

For a real `a`, the map `x ↦ (x − a).toENNReal` is an order isomorphism from the interval
`Set.Ici (a : EReal)` onto `ℝ≥0∞`, with inverse `u ↦ (u : EReal) + a`. This file records the
consequences that transport statements about an `EReal`-valued functional bounded below by `a`
into statements about the `ℝ≥0∞`-valued functional the convex-analysis API asks for: the shift is
monotone, order reflecting on `[a, ∞]`, and it commutes with infima.

## Main statements

* `EReal.shiftToENNReal a x = (x − a).toENNReal`, together with `EReal.coe_shiftToENNReal_add`
  (`(x − a).toENNReal + a = x` on `[a, ∞]`) and `EReal.shiftToENNReal_coe_add`
  (`((u : EReal) + a − a).toENNReal = u`), which say that it is a bijection `[a, ∞] → [0, ∞]`.
* `EReal.shiftToENNReal_le_shiftToENNReal_iff`: it is order reflecting on `[a, ∞]`.
* `EReal.shiftToENNReal_smul_add_smul_le`: it preserves convex combinations, so an affine (or
  concave) `EReal`-valued functional bounded below by `a` becomes an affine (concave)
  `[0, ∞]`-valued one; `LowerSemicontinuousOn.shiftToENNReal` says the same for lower
  semicontinuity.
* `EReal.iInf_shiftToENNReal`: it commutes with infima,
  `⨅ i, (f i − a).toENNReal = ((⨅ i, f i) − a).toENNReal` for a family bounded below by `a`;
  `EReal.biInf_shiftToENNReal` is the form with a side condition, and
  `EReal.biInf_eq_biInf_of_shiftToENNReal` reads an equality of two shifted infima back in
  `EReal`.
-/

@[expose] public section

open Set

open scoped ENNReal

namespace EReal

variable {a : ℝ}

/-- The shift of an extended real by a real, read in `[0, ∞]`: `x ↦ (x − a).toENNReal`. On
`[a, ∞]` it is an order isomorphism onto `ℝ≥0∞` (`EReal.coe_shiftToENNReal_add`,
`EReal.shiftToENNReal_coe_add`, `EReal.shiftToENNReal_le_shiftToENNReal_iff`). -/
noncomputable def shiftToENNReal (a : ℝ) (x : EReal) : ℝ≥0∞ := (x - (a : EReal)).toENNReal

lemma shiftToENNReal_def (x : EReal) : shiftToENNReal a x = (x - (a : EReal)).toENNReal := rfl

@[simp] lemma shiftToENNReal_top : shiftToENNReal a ⊤ = ⊤ := by
  rw [shiftToENNReal, EReal.top_sub_coe, EReal.toENNReal_top]

@[simp] lemma shiftToENNReal_zero_eq_toENNReal (x : EReal) :
    shiftToENNReal 0 x = x.toENNReal := by
  rw [shiftToENNReal, EReal.coe_zero, sub_zero]

lemma monotone_shiftToENNReal : Monotone (shiftToENNReal a) := fun _ _ h ↦
  EReal.toENNReal_le_toENNReal (EReal.sub_le_sub h le_rfl)

/-- The inverse shift, `u ↦ (u : EReal) + a`, is monotone. -/
lemma monotone_coe_add : Monotone fun u : ℝ≥0∞ ↦ (u : EReal) + (a : EReal) := fun _ _ h ↦
  add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.2 h) le_rfl

/-- The shift is left-inverted by `u ↦ u + a` on `[a, ∞]`. -/
lemma coe_shiftToENNReal_add {x : EReal} (hx : (a : EReal) ≤ x) :
    ((shiftToENNReal a x : ℝ≥0∞) : EReal) + (a : EReal) = x := by
  rw [shiftToENNReal, EReal.coe_toENNReal ((EReal.sub_nonneg (.inr (EReal.coe_ne_top a))
    (.inr (EReal.coe_ne_bot a))).2 hx), EReal.sub_add_cancel]

/-- The shift is right-inverted by `u ↦ u + a`. -/
@[simp] lemma shiftToENNReal_coe_add (u : ℝ≥0∞) :
    shiftToENNReal a ((u : EReal) + (a : EReal)) = u := by
  rw [shiftToENNReal, EReal.add_sub_cancel_right, EReal.toENNReal_coe]

/-- On `[a, ∞]` the shift is order reflecting, hence injective. -/
lemma shiftToENNReal_le_shiftToENNReal_iff {x y : EReal} (hx : (a : EReal) ≤ x)
    (hy : (a : EReal) ≤ y) : shiftToENNReal a x ≤ shiftToENNReal a y ↔ x ≤ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ monotone_shiftToENNReal h⟩
  have h' : ((shiftToENNReal a x : ℝ≥0∞) : EReal) + (a : EReal)
      ≤ ((shiftToENNReal a y : ℝ≥0∞) : EReal) + (a : EReal) := monotone_coe_add (a := a) h
  rwa [coe_shiftToENNReal_add hx, coe_shiftToENNReal_add hy] at h'

lemma shiftToENNReal_eq_shiftToENNReal_iff {x y : EReal} (hx : (a : EReal) ≤ x)
    (hy : (a : EReal) ≤ y) : shiftToENNReal a x = shiftToENNReal a y ↔ x = y := by
  rw [le_antisymm_iff, le_antisymm_iff, shiftToENNReal_le_shiftToENNReal_iff hx hy,
    shiftToENNReal_le_shiftToENNReal_iff hy hx]

/-- **The shift commutes with infima.** For a family of extended reals bounded below by `a`,
`⨅ i, (f i − a).toENNReal = ((⨅ i, f i) − a).toENNReal`. The index sort may be empty, both sides
being then `⊤`. -/
lemma iInf_shiftToENNReal {ι : Sort*} (f : ι → EReal) (hf : ∀ i, (a : EReal) ≤ f i) :
    ⨅ i, shiftToENNReal a (f i) = shiftToENNReal a (⨅ i, f i) := by
  refine le_antisymm ?_ (le_iInf fun i ↦ monotone_shiftToENNReal (iInf_le f i))
  have hstep : ((⨅ i, shiftToENNReal a (f i) : ℝ≥0∞) : EReal) + (a : EReal) ≤ ⨅ i, f i := by
    refine le_iInf fun i ↦ ?_
    have h' : ((⨅ j, shiftToENNReal a (f j) : ℝ≥0∞) : EReal) + (a : EReal)
        ≤ ((shiftToENNReal a (f i) : ℝ≥0∞) : EReal) + (a : EReal) :=
      monotone_coe_add (a := a) (iInf_le (fun j ↦ shiftToENNReal a (f j)) i)
    rwa [coe_shiftToENNReal_add (hf i)] at h'
  have h'' := monotone_shiftToENNReal (a := a) hstep
  rwa [shiftToENNReal_coe_add] at h''

/-- The shift commutes with an infimum restricted to a set: for `f` bounded below by `a` on `s`,
`⨅ i ∈ s, (f i − a).toENNReal = ((⨅ i ∈ s, f i) − a).toENNReal`. -/
lemma biInf_shiftToENNReal {ι : Type*} (f : ι → EReal) (s : Set ι)
    (hf : ∀ i ∈ s, (a : EReal) ≤ f i) :
    ⨅ i ∈ s, shiftToENNReal a (f i) = shiftToENNReal a (⨅ i ∈ s, f i) := by
  rw [← iInf_shiftToENNReal (fun i ↦ ⨅ _ : i ∈ s, f i) fun i ↦ le_iInf fun hi ↦ hf i hi]
  exact iInf_congr fun i ↦ iInf_shiftToENNReal (fun _ : i ∈ s ↦ f i) fun hi ↦ hf i hi

/-! ### The shift preserves affine combinations -/

/-- **The shift is affine.** For a convex combination `s + t = 1` with `s, t ≥ 0` and `x, y ≥ a`,
`s (x − a) + t (y − a) = (s x + t y) − a`. This is the identity behind
`EReal.shiftToENNReal_smul_add_smul_le`: the shift by a real number turns an affine functional
bounded below by `a` into an affine `[0, ∞]`-valued functional. -/
lemma smul_sub_add_smul_sub {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) {x y : EReal}
    (hx : (a : EReal) ≤ x) (hy : (a : EReal) ≤ y) :
    (s : EReal) * (x - (a : EReal)) + (t : EReal) * (y - (a : EReal))
      = ((s : EReal) * x + (t : EReal) * y) - (a : EReal) := by
  have hxb : x ≠ ⊥ := fun h ↦ by simp [h] at hx
  have hyb : y ≠ ⊥ := fun h ↦ by simp [h] at hy
  -- the case where a positive weight multiplies `⊤`
  have htop : ∀ {u v : EReal} {c d : ℝ}, 0 < c → 0 ≤ d → v ≠ ⊥ →
      (c : EReal) * (⊤ - (a : EReal)) + (d : EReal) * (v - (a : EReal))
        = ((c : EReal) * ⊤ + (d : EReal) * v) - (a : EReal) := by
    intro u v c d hc hd hv
    have h1 : (c : EReal) * (⊤ - (a : EReal)) = ⊤ := by
      rw [EReal.top_sub_coe, EReal.coe_mul_top_of_pos hc]
    have hvsub : v - (a : EReal) ≠ ⊥ := by
      induction v using EReal.rec with
      | bot => exact absurd rfl hv
      | top => simp
      | coe r => rw [← EReal.coe_sub]; exact EReal.coe_ne_bot _
    have h2 : (d : EReal) * (v - (a : EReal)) ≠ ⊥ := by
      refine fun h ↦ ?_
      rcases (EReal.mul_eq_bot _ _).1 h with h | h | h | h
      · exact absurd h.1 (EReal.coe_ne_bot d)
      · exact absurd h.2 hvsub
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (not_lt.2 (EReal.coe_nonneg.2 hd))
    have h3 : (d : EReal) * v ≠ ⊥ := by
      refine fun h ↦ ?_
      rcases (EReal.mul_eq_bot _ _).1 h with h | h | h | h
      · exact absurd h.1 (EReal.coe_ne_bot d)
      · exact absurd h.2 hv
      · exact absurd h.1 (by simp)
      · exact absurd h.1 (not_lt.2 (EReal.coe_nonneg.2 hd))
    rw [h1, EReal.top_add_of_ne_bot h2, EReal.coe_mul_top_of_pos hc,
      EReal.top_add_of_ne_bot h3, EReal.top_sub_coe]
  induction x using EReal.rec with
  | bot => exact absurd rfl hxb
  | top =>
      rcases eq_or_lt_of_le hs with rfl | hs'
      · have ht1 : t = 1 := by linarith
        subst ht1
        rw [EReal.coe_zero, zero_mul, zero_mul, zero_add, zero_add, EReal.coe_one, one_mul,
          one_mul]
      · exact htop (u := (⊤ : EReal)) hs' ht hyb
  | coe r =>
      induction y using EReal.rec with
      | bot => exact absurd rfl hyb
      | top =>
          rcases eq_or_lt_of_le ht with rfl | ht'
          · have hs1 : s = 1 := by linarith
            subst hs1
            rw [EReal.coe_zero, zero_mul, zero_mul, add_zero, add_zero, EReal.coe_one, one_mul,
              one_mul]
          · rw [add_comm ((s : EReal) * (r : EReal)), add_comm ((s : EReal) * _)]
            exact htop (u := (⊤ : EReal)) ht' hs (EReal.coe_ne_bot r)
      | coe q =>
          rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_mul,
            ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_sub,
            EReal.coe_eq_coe_iff]
          have hts : t = 1 - s := by linarith
          subst hts
          ring

/-- **The shift transports a concavity inequality.** If `s x + t y ≤ z` for a convex combination
`s + t = 1` of points above `a`, the same inequality holds for the shifted `[0, ∞]`-valued
quantities. Together with `EReal.iInf_shiftToENNReal` this is what lets a statement about an
`EReal`-valued affine functional bounded below be proved by `ℝ≥0∞`-valued convex analysis. -/
lemma shiftToENNReal_smul_add_smul_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    {x y z : EReal} (hx : (a : EReal) ≤ x) (hy : (a : EReal) ≤ y)
    (h : (s : EReal) * x + (t : EReal) * y ≤ z) :
    ENNReal.ofReal s * shiftToENNReal a x + ENNReal.ofReal t * shiftToENNReal a y
      ≤ shiftToENNReal a z := by
  have hx0 : (0 : EReal) ≤ x - (a : EReal) :=
    (EReal.sub_nonneg (.inr (EReal.coe_ne_top a)) (.inr (EReal.coe_ne_bot a))).2 hx
  have hy0 : (0 : EReal) ≤ y - (a : EReal) :=
    (EReal.sub_nonneg (.inr (EReal.coe_ne_top a)) (.inr (EReal.coe_ne_bot a))).2 hy
  have hcs : ENNReal.ofReal s = ((s : EReal)).toENNReal := (EReal.real_coe_toENNReal s).symm
  have hct : ENNReal.ofReal t = ((t : EReal)).toENNReal := (EReal.real_coe_toENNReal t).symm
  rw [shiftToENNReal, shiftToENNReal, shiftToENNReal, hcs, hct,
    ← EReal.toENNReal_mul (EReal.coe_nonneg.2 hs), ← EReal.toENNReal_mul (EReal.coe_nonneg.2 ht),
    ← EReal.toENNReal_add (EReal.mul_nonneg (EReal.coe_nonneg.2 hs) hx0)
      (EReal.mul_nonneg (EReal.coe_nonneg.2 ht) hy0),
    smul_sub_add_smul_sub hs ht hst hx hy]
  exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub h le_rfl)

/-- Two infima of an `EReal`-valued family bounded below by `a` are equal as soon as the infima
of the shifted `[0, ∞]`-valued family are. This is the step that reads a statement proved by
`ℝ≥0∞`-valued convex analysis back in `EReal`. -/
lemma biInf_eq_biInf_of_shiftToENNReal {ι : Type*} (f : ι → EReal) (s t : Set ι)
    (hs : ∀ i ∈ s, (a : EReal) ≤ f i) (ht : ∀ i ∈ t, (a : EReal) ≤ f i)
    (h : ⨅ i ∈ s, shiftToENNReal a (f i) = ⨅ i ∈ t, shiftToENNReal a (f i)) :
    ⨅ i ∈ s, f i = ⨅ i ∈ t, f i := by
  rw [biInf_shiftToENNReal f s hs, biInf_shiftToENNReal f t ht] at h
  exact (shiftToENNReal_eq_shiftToENNReal_iff (le_iInf fun i ↦ le_iInf fun hi ↦ hs i hi)
    (le_iInf fun i ↦ le_iInf fun hi ↦ ht i hi)).1 h

end EReal

/-- **The shift preserves lower semicontinuity.** If `f` is lower semicontinuous on `s` and
bounded below there by the real number `a`, then `x ↦ (f x − a).toENNReal` is lower
semicontinuous on `s`. -/
lemma LowerSemicontinuousOn.shiftToENNReal {X : Type*} [TopologicalSpace X] {s : Set X}
    {f : X → EReal} {a : ℝ} (hf : LowerSemicontinuousOn f s)
    (hbdd : ∀ x ∈ s, (a : EReal) ≤ f x) :
    LowerSemicontinuousOn (fun x ↦ EReal.shiftToENNReal a (f x)) s := by
  intro x hx u hu
  -- pull `u` back to `[a, ∞]` along the inverse shift
  set y : EReal := (u : EReal) + (a : EReal) with hy
  have hya : (a : EReal) ≤ y := by
    have h0 : ((0 : ℝ≥0∞) : EReal) + (a : EReal) ≤ (u : EReal) + (a : EReal) :=
      EReal.monotone_coe_add (a := a) (bot_le : (0 : ℝ≥0∞) ≤ u)
    simpa [hy] using h0
  have hyx : y < f x := by
    refine lt_of_not_ge fun hcon ↦ absurd ?_ (not_le.2 hu)
    have := (EReal.shiftToENNReal_le_shiftToENNReal_iff (a := a) (hbdd x hx) hya).2 hcon
    rwa [hy, EReal.shiftToENNReal_coe_add] at this
  filter_upwards [hf x hx y hyx, self_mem_nhdsWithin] with x' hx' hx's
  refine lt_of_not_ge fun hcon ↦ absurd ?_ (not_le.2 hx')
  have := (EReal.shiftToENNReal_le_shiftToENNReal_iff (a := a) (hbdd x' hx's) hya).1
    (by rwa [hy, EReal.shiftToENNReal_coe_add])
  exact this

end

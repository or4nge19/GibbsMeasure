/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Algebra.QuadraticDiscriminant
public import GibbsMeasure.Mathlib.Data.ZMod.Basic
public import GibbsMeasure.Prereqs.Transformation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Georgii §17.1: reflection positivity and the chessboard estimate

Georgii's torus `Λ(N) = ]-N, N]^d ∩ ℤ^d` (17.1) with the addition modulo `Λ` of (17.2) is the
group `(ℤ/2N)^d`.  We use the labels `0, …, 2N - 1` in each coordinate direction instead of
Georgii's `-N + 1, …, N`; the translation `i ↦ i - 1` carries one to the other and turns his
reflection `i ↦ 1 - i` of (17.5), in the plane `x = 1/2`, into `z ↦ -1 - z`, the reflection in
the plane `x = -1/2`, which exchanges the halves `{0, …, N - 1}` and `{N, …, 2N - 1}`.  Georgii's
`Λ_{+,k}` of (17.4) is the first of these halves.

## Main definitions and results

* `MeasureTheory.GibbsMeasure.foldPos` / `foldNeg`: the two "colour reversed mirror image"
  operations on `(ℤ/2N)`-indexed words appearing in hypothesis (ii) of Georgii's Lemma (17.9).
* `MeasureTheory.GibbsMeasure.altConfig`: the alternating word `(a, ã, a, ã, …)`.
* `MeasureTheory.GibbsMeasure.pow_le_prod_of_chessboard`: **Georgii, Lemma (17.9)**, the
  combinatorial chessboard estimate.
-/

@[expose] public section

open MeasureTheory Set

namespace MeasureTheory.GibbsMeasure

/-! ### Words on a set with an involution, indexed by the discrete circle `ℤ/2N` -/

section Combinatorics

variable {A : Type*} {N : ℕ}

/-- Georgii (17.9): the alternating word `(a, ã, a, ã, …)` of length `2N`. -/
def altConfig (N : ℕ) (t : A → A) (a : A) : ZMod (2 * N) → A :=
  fun z ↦ if Even z.val then a else t a

/-- The word obtained from `α` by keeping it on the positive half `{0, …, N - 1}` of the circle
and replacing it on the negative half by the `t`-reversed mirror image: the first of the two
words compared with `α` in hypothesis (ii) of Georgii's Lemma (17.9). -/
def foldPos (N : ℕ) (t : A → A) (α : ZMod (2 * N) → A) : ZMod (2 * N) → A :=
  fun z ↦ if z.val < N then α z else t (α (-1 - z))

/-- The word obtained from `α` by keeping it on the negative half `{N, …, 2N - 1}` of the circle
and replacing it on the positive half by the `t`-reversed mirror image: the second of the two
words compared with `α` in hypothesis (ii) of Georgii's Lemma (17.9). -/
def foldNeg (N : ℕ) (t : A → A) (α : ZMod (2 * N) → A) : ZMod (2 * N) → A :=
  fun z ↦ if z.val < N then t (α (-1 - z)) else α z

/-- `α` carries an alternating strip of length `2ℓ` with value `a`, centred on the circle: the
sets `R_{a,ℓ}` of Georgii's proof of (17.9) are the words with `IsStrip N t a ℓ` at which the
functional in question is positive. -/
def IsStrip (N : ℕ) (t : A → A) (a : A) (ℓ : ℕ) (α : ZMod (2 * N) → A) : Prop :=
  ∀ m < 2 * ℓ, α ((N - ℓ + m : ℕ) : ZMod (2 * N)) = if Even m then a else t a

variable [NeZero N]

instance : NeZero (2 * N) := ⟨by have := NeZero.ne N; omega⟩

omit [NeZero N] in
@[simp] lemma altConfig_apply (t : A → A) (a : A) (z : ZMod (2 * N)) :
    altConfig N t a z = if Even z.val then a else t a := rfl

/-- A word with a full-length alternating strip is the alternating word. -/
lemma eq_altConfig_of_isStrip {t : A → A} {a : A} {α : ZMod (2 * N) → A}
    (h : IsStrip N t a N α) : α = altConfig N t a := by
  funext z
  have hz : z.val < 2 * N := ZMod.val_lt z
  have := h z.val (by simpa using hz)
  simpa [ZMod.natCast_val_self] using this

/-! ### The inductive core of Georgii's Lemma (17.9)

Georgii's proof of (17.9) runs the same induction twice: once for the predicate `F > 0` and once
for the predicate `G = max G`.  Both times the only properties used are that the predicate is
invariant under the cyclic shift and stable under `foldPos`.  We isolate that argument. -/

variable {t : A → A} {P : (ZMod (2 * N) → A) → Prop}

omit [NeZero N] in
lemma shift_natCast_of_shift (hshift : ∀ α, P α → P fun z ↦ α (z + 1))
    {α : ZMod (2 * N) → A} (hα : P α) (k : ℕ) : P fun z ↦ α (z + (k : ZMod (2 * N))) := by
  induction k with
  | zero => simpa using hα
  | succ k ih =>
      have h := hshift _ ih
      have he : (fun z : ZMod (2 * N) ↦ α (z + 1 + (k : ZMod (2 * N))))
          = fun z : ZMod (2 * N) ↦ α (z + ((k + 1 : ℕ) : ZMod (2 * N))) := by
        funext z; push_cast; ring_nf
      rw [he] at h
      exact h

/-- A shift-invariant predicate is invariant under every cyclic shift. -/
lemma shift_of_shift (hshift : ∀ α, P α → P fun z ↦ α (z + 1))
    {α : ZMod (2 * N) → A} (hα : P α) (s : ZMod (2 * N)) : P fun z ↦ α (z + s) := by
  have h := shift_natCast_of_shift hshift hα s.val
  rwa [ZMod.natCast_val_self] at h

/-- The doubling step in Georgii's proof of (17.9): a strip of length `2ℓ` produces a strip of
length `2 (N ⊓ 2ℓ)`, by a cyclic shift bringing the strip to the positions `N - k, …, N - 1`
followed by the folding `foldPos`. -/
lemma exists_isStrip_min (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hshift : ∀ α, P α → P fun z ↦ α (z + 1)) (hfold : ∀ α, P α → P (foldPos N t α))
    {a : A} {ℓ : ℕ} (hℓ : 0 < ℓ) (hℓN : ℓ ≤ N) (h : ∃ γ, P γ ∧ IsStrip N t a ℓ γ) :
    ∃ γ, P γ ∧ IsStrip N t a (min N (2 * ℓ)) γ := by
  obtain ⟨γ, hγP, hγS⟩ := h
  set k := min N (2 * ℓ) with hkdef
  have hkN : k ≤ N := min_le_left _ _
  have hk2l : k ≤ 2 * ℓ := min_le_right _ _
  have hk0 : 0 < k := lt_min hN (by omega)
  set β : ZMod (2 * N) → A := fun z ↦ γ (z + ((k : ZMod (2 * N)) - (ℓ : ZMod (2 * N)))) with hβdef
  have hβP : P β := shift_of_shift hshift hγP _
  have key : ∀ m : ℕ, β ((N - k + m : ℕ) : ZMod (2 * N)) = γ ((N - ℓ + m : ℕ) : ZMod (2 * N)) := by
    intro m
    have h1 : ((N - k + m : ℕ) : ZMod (2 * N)) + (k : ZMod (2 * N))
        = ((N + m : ℕ) : ZMod (2 * N)) := by rw [← Nat.cast_add]; congr 1; omega
    have h2 : ((N - ℓ + m : ℕ) : ZMod (2 * N)) + (ℓ : ZMod (2 * N))
        = ((N + m : ℕ) : ZMod (2 * N)) := by rw [← Nat.cast_add]; congr 1; omega
    have h3 : ((N - k + m : ℕ) : ZMod (2 * N)) + ((k : ZMod (2 * N)) - (ℓ : ZMod (2 * N)))
        = ((N - ℓ + m : ℕ) : ZMod (2 * N)) := by
      have h4 : ((N - k + m : ℕ) : ZMod (2 * N)) + ((k : ZMod (2 * N)) - (ℓ : ZMod (2 * N)))
          = (((N - k + m : ℕ) : ZMod (2 * N)) + (k : ZMod (2 * N))) - (ℓ : ZMod (2 * N)) := by
        ring
      rw [h4, h1, ← h2]; ring
    simp only [hβdef, h3]
  have hβS : ∀ m < 2 * ℓ, β ((N - k + m : ℕ) : ZMod (2 * N)) = if Even m then a else t a :=
    fun m hm ↦ (key m).trans (hγS m hm)
  refine ⟨foldPos N t β, hfold _ hβP, ?_⟩
  intro m hm
  have hlt : N - k + m < 2 * N := by omega
  have hval : (((N - k + m : ℕ) : ZMod (2 * N))).val = N - k + m := ZMod.val_natCast_of_lt hlt
  by_cases hmk : m < k
  · have hcond : N - k + m < N := by omega
    simp only [foldPos, hval, hcond, ite_true]
    exact hβS m (by omega)
  · have hmk' : k ≤ m := by omega
    have hge : ¬ N - k + m < N := by omega
    have hrefl : -1 - ((N - k + m : ℕ) : ZMod (2 * N))
        = ((N - k + (2 * k - m - 1) : ℕ) : ZMod (2 * N)) := by
      rw [ZMod.neg_one_sub_natCast hlt]
      congr 1
      omega
    simp only [foldPos, hval, hge, ite_false, hrefl]
    rw [hβS (2 * k - m - 1) (by omega)]
    rcases Nat.even_or_odd m with he | ho
    · have h' : ¬ Even (2 * k - m - 1) := by
        rcases he with ⟨r, hr⟩
        exact Nat.not_even_iff_odd.2 ⟨k - r - 1, by omega⟩
      simp [he, h', ht]
    · have h' : Even (2 * k - m - 1) := by
        rcases ho with ⟨r, hr⟩
        exact ⟨k - r - 1, by omega⟩
      simp [Nat.not_even_iff_odd.2 ho, h']

/-- Iterating the doubling step up to a strip filling the whole circle. -/
lemma exists_isStrip_top (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hshift : ∀ α, P α → P fun z ↦ α (z + 1)) (hfold : ∀ α, P α → P (foldPos N t α)) {a : A} :
    ∀ j ℓ : ℕ, N - ℓ ≤ j → 0 < ℓ → ℓ ≤ N → (∃ γ, P γ ∧ IsStrip N t a ℓ γ) →
      ∃ γ, P γ ∧ IsStrip N t a N γ := by
  intro j
  induction j with
  | zero =>
      intro ℓ hj hℓ hℓN h
      have : ℓ = N := by omega
      exact this ▸ h
  | succ j ih =>
      intro ℓ hj hℓ hℓN h
      rcases eq_or_lt_of_le hℓN with rfl | hlt
      · exact h
      · exact ih (min N (2 * ℓ)) (by omega) (lt_min hN (by omega)) (min_le_left _ _)
          (exists_isStrip_min hN ht hshift hfold hℓ hℓN h)

/-- **The inductive core of Georgii's Lemma (17.9).** If a predicate on words is invariant under
the cyclic shift and stable under the folding `foldPos`, then it holds at the alternating word
`(a, ã, a, ã, …)` built from any letter `a` occurring in a word satisfying it. -/
theorem altConfig_of_shift_of_foldPos (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hshift : ∀ α, P α → P fun z ↦ α (z + 1)) (hfold : ∀ α, P α → P (foldPos N t α))
    {α : ZMod (2 * N) → A} (hα : P α) (z₀ : ZMod (2 * N)) : P (altConfig N t (α z₀)) := by
  set a := α z₀ with hadef
  set β : ZMod (2 * N) → A := fun z ↦ α (z + (z₀ - ((N - 1 : ℕ) : ZMod (2 * N)))) with hβdef
  have hβP : P β := shift_of_shift hshift hα _
  have hβa : β ((N - 1 : ℕ) : ZMod (2 * N)) = a := by simp [hβdef, hadef]
  -- the base case: `foldPos β` carries an alternating strip of length `2`
  have hbase : ∃ γ, P γ ∧ IsStrip N t a 1 γ := by
    refine ⟨foldPos N t β, hfold _ hβP, ?_⟩
    intro m hm
    interval_cases m
    · have hv : (((N - 1 + 0 : ℕ) : ZMod (2 * N))).val = N - 1 :=
        ZMod.val_natCast_of_lt (by omega)
      simp only [foldPos, hv, show N - 1 < N by omega, ite_true]
      simpa using hβa
    · have hv : (((N - 1 + 1 : ℕ) : ZMod (2 * N))).val = N := by
        rw [show N - 1 + 1 = N by omega]; exact ZMod.val_natCast_of_lt (by omega)
      have hr : -1 - (((N - 1 + 1 : ℕ) : ZMod (2 * N))) = ((N - 1 : ℕ) : ZMod (2 * N)) := by
        rw [ZMod.neg_one_sub_natCast (show N - 1 + 1 < 2 * N by omega)]
        congr 1
        omega
      simp only [foldPos, hv, show ¬ N < N by omega, ite_false, hr, hβa]
      simp
  obtain ⟨γ, hγP, hγS⟩ := exists_isStrip_top hN ht hshift hfold N 1 (by omega) one_pos
    (by omega) hbase
  rwa [eq_altConfig_of_isStrip hγS] at hγP

end Combinatorics

end MeasureTheory.GibbsMeasure

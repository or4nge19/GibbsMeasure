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
  combinatorial chessboard estimate, in the root-free form
  `D α ^ (2N) ≤ ∏_z D (α z, t (α z), α z, t (α z), …)` for a nonnegative shift-invariant `D`
  satisfying `D α ^ 2 ≤ D (foldPos α) · D (foldNeg α)`.  The alphabet is finite, as Georgii's
  `A(N) = {1, …, 2N} × {0, 1}` is.
* `MeasureTheory.GibbsMeasure.IsReflectionPositive`: **Georgii, Definition (17.7)**.  The
  generalized reflection `r̃_k` of (17.6) is `pureSpin S τ_k * siteEquiv E r_k`, and "depends only
  on the coordinates in `Λ_{+,k}`" is measurability for `cylinderEvents Λ_{+,k}`.
* `MeasureTheory.GibbsMeasure.sq_integral_mul_comp_le`: **Georgii (17.8)**, Cauchy–Schwarz for the
  form `(f, g) ↦ μ(f · g∘r̃_k)`.  It carries the extra hypothesis that `μ` is `r̃_k`-*invariant*,
  which is what makes that real bilinear form symmetric; nonnegativity alone bounds only its
  symmetric part, so (17.8) is false as stated without it.  Georgii's measures of §17.2 are
  reflection invariant.
* `MeasureTheory.GibbsMeasure.abs_integral_prod_pow_le`: **Georgii, Theorem (17.11) for `d = 1`**,
  `|μ(∏_i f_i ∘ σ_i)|^{2N} ≤ ∏_j μ(∏_i f_j ∘ τ^i ∘ σ_i)`.  The dictionary between words over
  `A(N)` and products of single-spin functions is `wordProd`, and the two halves of a word are
  `wordProdPos` / `wordProdNeg`; `wordProdPos_genReflection` and `wordProdNeg_genReflection` are
  the identifications `f* ` of Georgii's proof, and `sq_integral_wordProd_le` /
  `integral_wordProd_shift` are hypotheses (ii) and (i) of (17.9) for `D = |μ(wordProd ·)|`.

## Not formalised here

Georgii's induction on the dimension `d` in the proof of (17.11) (step 2: view `μ` on
`(E^{Λ_0})^{Λ_1}` and apply the one-dimensional case in each direction), and the coarse-graining
(17.12)–(17.17) to functions of the elementary cubes `C(i)`.  Only `d = 1` is proved.
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


/-! ### Georgii's Lemma (17.9): the chessboard estimate

Georgii's map `F : A(N)^{2N} → [0, ∞[` is here a function `D` on words `ZMod (2 * N) → A`, and
his two hypotheses read

* (i)  `D (fun z ↦ α (z + 1)) = D α` — invariance under the cyclic shift;
* (ii) `D α ^ 2 ≤ D (foldPos N t α) * D (foldNeg N t α)` — the Cauchy–Schwarz hypothesis (17.8),
  which compares a word with the two words obtained by reflecting one of its halves onto the
  other with the colours reversed.

The conclusion `F(a_1, …, a_{2N}) ≤ ∏_ℓ F(a_ℓ, ã_ℓ, …, a_ℓ, ã_ℓ)^{1/2N}` is stated in the
equivalent root-free form `D α ^ (2 * N) ≤ ∏_z D (altConfig N t (α z))`, both sides being
nonnegative. -/

section Chessboard

variable {A : Type*} {N : ℕ} [NeZero N] {t : A → A} {D : (ZMod (2 * N) → A) → ℝ}

/-- In `ZMod (2 * N)` the parity of `val` alternates: adding `1` flips it, including at the
wrap-around `2 * N - 1 ↦ 0`, because `2 * N` is even. -/
lemma even_val_add_one_iff (hN : 0 < N) (z : ZMod (2 * N)) :
    Even (z + 1).val ↔ ¬ Even z.val := by
  have : Fact (1 < 2 * N) := ⟨by omega⟩
  have hval : (z + 1).val = (z.val + 1) % (2 * N) := by
    rw [ZMod.val_add, ZMod.val_one]
  have hmod : (z.val + 1) % (2 * N) % 2 = (z.val + 1) % 2 :=
    Nat.mod_mod_of_dvd _ ⟨N, rfl⟩
  simp only [Nat.even_iff, hval, hmod]
  omega

/-- The alternating word built from `ã` is the cyclic shift of the one built from `a`
(Georgii's remark that it does not matter whether the leftmost chip is black or white). -/
lemma altConfig_involute (hN : 0 < N) (ht : ∀ a, t (t a) = a) (a : A) :
    altConfig N t (t a) = fun z : ZMod (2 * N) ↦ altConfig N t a (z + 1) := by
  funext z
  simp only [altConfig_apply, even_val_add_one_iff hN z, ht]
  by_cases h : Even z.val <;> simp [h]

/-- Georgii's reference value `F(a, ã, …, a, ã)` is unchanged by the involution. -/
lemma altConfig_involute_value (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hshift : ∀ α, D (fun z ↦ α (z + 1)) = D α) (a : A) :
    D (altConfig N t (t a)) = D (altConfig N t a) := by
  rw [altConfig_involute hN ht, hshift]

/-- All `2 * N` letters of an alternating word carry the same reference value. -/
lemma prod_altConfig_value (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hshift : ∀ α, D (fun z ↦ α (z + 1)) = D α) (a : A) :
    ∏ z : ZMod (2 * N), D (altConfig N t (altConfig N t a z))
      = D (altConfig N t a) ^ (2 * N) := by
  have h : ∀ z : ZMod (2 * N),
      D (altConfig N t (altConfig N t a z)) = D (altConfig N t a) := by
    intro z
    by_cases hz : Even z.val
    · simp only [altConfig_apply, hz, ite_true]
    · simp only [altConfig_apply, hz, ite_false]
      exact altConfig_involute_value hN ht hshift a
  rw [Finset.prod_congr rfl fun z _ ↦ h z, Finset.prod_const, Finset.card_univ, ZMod.card]

/-- The reflection `z ↦ -1 - z` is a bijection of the discrete circle, so it does not change a
product over it. -/
lemma prod_neg_one_sub (f : ZMod (2 * N) → ℝ) :
    ∏ z : ZMod (2 * N), f (-1 - z) = ∏ z : ZMod (2 * N), f z :=
  Equiv.prod_comp (Equiv.subLeft (-1 : ZMod (2 * N))) f

/-- The cyclic shift does not change a product over the discrete circle. -/
lemma prod_add_one (f : ZMod (2 * N) → ℝ) :
    ∏ z : ZMod (2 * N), f (z + 1) = ∏ z : ZMod (2 * N), f z :=
  Equiv.prod_comp (Equiv.addRight (1 : ZMod (2 * N))) f

/-- **The reference product is unchanged by folding.** At every position the pair of letters
produced by `foldPos` and `foldNeg` is `(α z, t (α (-1 - z)))` up to order, so a weight `Q`
invariant under `t` has `∏ Q ∘ foldPos · ∏ Q ∘ foldNeg = (∏ Q ∘ α) ^ 2`. -/
lemma prod_foldPos_mul_prod_foldNeg {Q : A → ℝ} (hQ : ∀ a, Q (t a) = Q a)
    (α : ZMod (2 * N) → A) :
    (∏ z : ZMod (2 * N), Q (foldPos N t α z)) * (∏ z : ZMod (2 * N), Q (foldNeg N t α z))
      = (∏ z : ZMod (2 * N), Q (α z)) ^ 2 := by
  rw [← Finset.prod_mul_distrib]
  have h : ∀ z : ZMod (2 * N),
      Q (foldPos N t α z) * Q (foldNeg N t α z) = Q (α z) * Q (α (-1 - z)) := by
    intro z
    by_cases hz : z.val < N
    · simp [foldPos, foldNeg, hz, hQ]
    · simp [foldPos, foldNeg, hz, hQ, mul_comm]
  rw [Finset.prod_congr rfl fun z _ ↦ h z, Finset.prod_mul_distrib,
    prod_neg_one_sub fun z ↦ Q (α z), sq]

/-- **Step 1 of Georgii's proof of (17.9).** If `D` is positive at a word then it is positive at
the alternating word built from any of its letters: the set `{D > 0}` is shift invariant and, by
hypothesis (ii), stable under `foldPos`. -/
theorem pos_altConfig_of_pos (hN : 0 < N) (ht : ∀ a, t (t a) = a) (hD : ∀ α, 0 ≤ D α)
    (hshift : ∀ α, D (fun z ↦ α (z + 1)) = D α)
    (hCS : ∀ α, D α ^ 2 ≤ D (foldPos N t α) * D (foldNeg N t α))
    {α : ZMod (2 * N) → A} (hα : 0 < D α) (z₀ : ZMod (2 * N)) :
    0 < D (altConfig N t (α z₀)) := by
  refine altConfig_of_shift_of_foldPos (P := fun β ↦ 0 < D β) hN ht (fun β hβ ↦ ?_)
    (fun β hβ ↦ ?_) hα z₀
  · rwa [hshift]
  · by_contra hcon
    rw [not_lt] at hcon
    have h0 : D (foldPos N t β) = 0 := le_antisymm hcon (hD _)
    have h := hCS β
    rw [h0, zero_mul] at h
    nlinarith [hβ]

/-- **Georgii, Lemma (17.9): the chessboard estimate.** Let `A` be a finite alphabet with an
involution `t` (Georgii's `A(N) = {1, …, 2N} × {0, 1}` with the colour change `a ↦ ã`), and let
`D` be a nonnegative function on words of length `2 * N` over `A` which is

* invariant under the cyclic shift (Georgii's hypothesis (i)), and
* satisfies `D α ^ 2 ≤ D (foldPos N t α) * D (foldNeg N t α)` (his hypothesis (ii)).

Then every word is dominated by the geometric mean of the alternating words built from its
letters: `D α ^ (2 * N) ≤ ∏_z D (α z, t (α z), α z, t (α z), …)`. -/
theorem pow_le_prod_of_chessboard [Finite A] (hN : 0 < N) (ht : ∀ a, t (t a) = a)
    (hD : ∀ α, 0 ≤ D α) (hshift : ∀ α, D (fun z ↦ α (z + 1)) = D α)
    (hCS : ∀ α, D α ^ 2 ≤ D (foldPos N t α) * D (foldNeg N t α))
    (α : ZMod (2 * N) → A) :
    D α ^ (2 * N) ≤ ∏ z : ZMod (2 * N), D (altConfig N t (α z)) := by
  classical
  set Q : A → ℝ := fun a ↦ D (altConfig N t a) with hQdef
  have hQ0 : ∀ a, 0 ≤ Q a := fun _ ↦ hD _
  have hQt : ∀ a, Q (t a) = Q a := fun a ↦ altConfig_involute_value hN ht hshift a
  -- Step 1: if some letter has reference value `0` then `D α = 0`.
  by_cases hzero : ∃ z, Q (α z) = 0
  · obtain ⟨z₀, hz₀⟩ := hzero
    have hprod : ∏ z : ZMod (2 * N), Q (α z) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ z₀) hz₀
    have hDα : D α = 0 := by
      by_contra hne
      exact absurd hz₀ (ne_of_gt (pos_altConfig_of_pos hN ht hD hshift hCS
        (lt_of_le_of_ne (hD α) (Ne.symm hne)) z₀))
    rw [hprod, hDα, zero_pow (by omega)]
  -- Step 2: all letters have positive reference value; maximise the normalised functional.
  simp only [not_exists] at hzero
  have hQpos : ∀ z, 0 < Q (α z) := fun z ↦ lt_of_le_of_ne (hQ0 _) (Ne.symm (hzero z))
  set Spos : Set (ZMod (2 * N) → A) := {β | ∀ z, 0 < Q (β z)} with hSdef
  have hαS : α ∈ Spos := hQpos
  have hprodpos : ∀ β ∈ Spos, 0 < ∏ z : ZMod (2 * N), Q (β z) :=
    fun β hβ ↦ Finset.prod_pos fun z _ ↦ hβ z
  set G : (ZMod (2 * N) → A) → ℝ := fun β ↦ D β ^ (2 * N) / ∏ z, Q (β z) with hGdef
  rcases eq_or_lt_of_le (hD α) with hDα | hDα
  · rw [← hDα, zero_pow (by omega)]
    exact (hprodpos α hαS).le
  obtain ⟨α₀, hα₀S, hα₀max⟩ := Set.exists_max_image Spos G (Set.toFinite _) ⟨α, hαS⟩
  set c := G α₀ with hcdef
  have hcpos : 0 < c :=
    lt_of_lt_of_le (div_pos (pow_pos hDα _) (hprodpos α hαS)) (hα₀max α hαS)
  -- both foldings preserve the set of words all of whose letters have positive reference value
  have hfoldS : ∀ β ∈ Spos, foldPos N t β ∈ Spos ∧ foldNeg N t β ∈ Spos := by
    intro β hβ
    refine ⟨fun z ↦ ?_, fun z ↦ ?_⟩
    · by_cases hz : z.val < N
      · simpa [foldPos, hz] using hβ z
      · simpa [foldPos, hz, hQt] using hβ (-1 - z)
    · by_cases hz : z.val < N
      · simpa [foldNeg, hz, hQt] using hβ (-1 - z)
      · simpa [foldNeg, hz] using hβ z
  -- hypothesis (ii) transfers to the normalised functional
  have hkey : ∀ β ∈ Spos, G β ^ 2 ≤ G (foldPos N t β) * G (foldNeg N t β) := by
    intro β hβ
    obtain ⟨hfp, hfn⟩ := hfoldS β hβ
    have hden : (∏ z : ZMod (2 * N), Q (foldPos N t β z))
          * (∏ z : ZMod (2 * N), Q (foldNeg N t β z))
        = (∏ z : ZMod (2 * N), Q (β z)) ^ 2 := prod_foldPos_mul_prod_foldNeg hQt β
    have hnum : (D β ^ (2 * N)) ^ 2
        ≤ D (foldPos N t β) ^ (2 * N) * D (foldNeg N t β) ^ (2 * N) := by
      calc (D β ^ (2 * N)) ^ 2 = (D β ^ 2) ^ (2 * N) := by ring
        _ ≤ (D (foldPos N t β) * D (foldNeg N t β)) ^ (2 * N) :=
            pow_le_pow_left₀ (sq_nonneg _) (hCS β) _
        _ = _ := mul_pow _ _ _
    simp only [hGdef]
    rw [div_pow, div_mul_div_comm, hden]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  -- the maximum is attained at an alternating word, where the functional equals `1`
  have hmax : ∀ β, (β ∈ Spos ∧ G β = c) → ((fun z ↦ β (z + 1)) ∈ Spos ∧
      G (fun z ↦ β (z + 1)) = c) := by
    rintro β ⟨hβS, hβc⟩
    refine ⟨fun z ↦ hβS _, ?_⟩
    simp only [hGdef] at hβc ⊢
    rw [hshift, prod_add_one fun z ↦ Q (β z)]
    exact hβc
  have hfoldmax : ∀ β, (β ∈ Spos ∧ G β = c) → (foldPos N t β ∈ Spos ∧ G (foldPos N t β) = c) := by
    rintro β ⟨hβS, hβc⟩
    obtain ⟨hfp, hfn⟩ := hfoldS β hβS
    refine ⟨hfp, le_antisymm (hα₀max _ hfp) ?_⟩
    have h1 : c ^ 2 ≤ G (foldPos N t β) * G (foldNeg N t β) := hβc ▸ hkey β hβS
    have h2 : G (foldNeg N t β) ≤ c := hα₀max _ hfn
    have h3 : 0 ≤ G (foldPos N t β) :=
      div_nonneg (pow_nonneg (hD _) _) (hprodpos _ hfp).le
    nlinarith [h1, h2, h3, hcpos]
  obtain ⟨hbS, hbc⟩ := altConfig_of_shift_of_foldPos
    (P := fun β ↦ β ∈ Spos ∧ G β = c) hN ht hmax hfoldmax ⟨hα₀S, rfl⟩ 0
  have hQa : 0 < Q (α₀ 0) := hα₀S 0
  have hone : G (altConfig N t (α₀ 0)) = 1 := by
    simp only [hGdef, hQdef]
    rw [prod_altConfig_value hN ht hshift]
    exact div_self (by positivity)
  rw [hone] at hbc
  have hfinal : G α ≤ 1 := hbc ▸ hα₀max α hαS
  simp only [hGdef] at hfinal
  rw [div_le_one (hprodpos α hαS)] at hfinal
  exact hfinal

end Chessboard

end Combinatorics


/-! ### Georgii (17.7), (17.8): reflection positivity and Cauchy–Schwarz -/

section ReflectionPositive

variable {S E : Type*} [MeasurableSpace E]

/-- **Georgii (17.7).** A finite measure `μ` on `E^S` is `τ̃`-positive relative to the half `Λpos`
of the site set if `μ(f · f∘τ̃) ≥ 0` for every bounded function `f` on `E^S` that depends only on
the coordinates in `Λpos`, i.e. is measurable for `cylinderEvents Λpos`.  These are Georgii's
`f ∈ 𝒜_{+,k}` and `f* = f ∘ r̃_k`; the generalized reflection `r̃_k` of (17.6) is
`pureSpin S τ_k * siteEquiv E r_k`. -/
def IsReflectionPositive (Λpos : Set S) (τ : Transformation S E) (μ : Measure (S → E)) : Prop :=
  ∀ f : (S → E) → ℝ, Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f →
    (∃ C, ∀ ω, |f ω| ≤ C) → 0 ≤ ∫ ω, f ω * f (τ.toFun ω) ∂μ

/-- A bounded measurable real function is integrable against a finite measure. -/
lemma integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by simpa using hC ω)

/-- The integrand `f · g∘τ̃` of the reflection form is integrable when `f` and `g` are bounded
and measurable and `μ` is finite. -/
lemma integrable_mul_comp {τ : Transformation S E} {μ : Measure (S → E)} [IsFiniteMeasure μ]
    {f g : (S → E) → ℝ} (hf : Measurable f) (hg : Measurable g) {Cf Cg : ℝ}
    (hCf : ∀ ω, |f ω| ≤ Cf) (hCg : ∀ ω, |g ω| ≤ Cg) :
    Integrable (fun ω ↦ f ω * g (τ.toFun ω)) μ := by
  refine integrable_of_abs_le (hf.mul (hg.comp τ.measurable_toFun)) (C := |Cf| * |Cg|) fun ω ↦ ?_
  rw [abs_mul]
  exact mul_le_mul ((hCf ω).trans (le_abs_self _)) ((hCg _).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- **Georgii (17.8): Cauchy–Schwarz for a reflection positive measure.**

The bilinear form `(f, g) ↦ μ(f · g∘τ̃)` on the bounded `cylinderEvents Λpos`-measurable functions
is nonnegative definite by (17.7).  It is *symmetric* precisely because `μ` is invariant under
the reflection `τ̃`: for a real bilinear form, `B x x ≥ 0` alone bounds only the symmetric part
`B x y + B y x`.  Georgii's measures of §17.2 are reflection invariant, so the hypothesis
`hinv` is his. -/
theorem sq_integral_mul_comp_le {Λpos : Set S} {τ : Transformation S E} {μ : Measure (S → E)}
    [IsFiniteMeasure μ] (hinv : MeasurePreserving τ.toFun μ μ)
    (hτ : ∀ ω, τ.toFun (τ.toFun ω) = ω) (hpos : IsReflectionPositive Λpos τ μ)
    {f g : (S → E) → ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f) (hfb : ∃ C, ∀ ω, |f ω| ≤ C)
    (hg : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] g) (hgb : ∃ C, ∀ ω, |g ω| ≤ C) :
    (∫ ω, f ω * g (τ.toFun ω) ∂μ) ^ 2
      ≤ (∫ ω, f ω * f (τ.toFun ω) ∂μ) * (∫ ω, g ω * g (τ.toFun ω) ∂μ) := by
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  have hgm : Measurable g := hg.mono cylinderEvents_le_pi le_rfl
  -- symmetry of the form, from the invariance of `μ` under the involution `τ̃`
  have hmp : MeasurePreserving τ.toMeasurableEquiv μ μ := hinv
  have hsymm : ∫ ω, g ω * f (τ.toFun ω) ∂μ = ∫ ω, f ω * g (τ.toFun ω) ∂μ := by
    have h := hmp.integral_comp' (fun ω ↦ f ω * g (τ.toFun ω))
    have hcoe : ⇑τ.toMeasurableEquiv = τ.toFun := rfl
    rw [hcoe] at h
    simp only [hτ] at h
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)
  refine sq_le_mul_of_forall_quadratic_nonneg fun t ↦ ?_
  have hbound : ∀ ω, |f ω + t * g ω| ≤ Cf + |t| * Cg := by
    intro ω
    have h1 := abs_le.1 (hCf ω)
    have h2 : |t * g ω| ≤ |t| * Cg := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCg ω) (abs_nonneg t)
    have h3 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith
  have hcomb := hpos (fun ω ↦ f ω + t * g ω) (hf.add ((measurable_const (a := t)).mul hg))
    ⟨Cf + |t| * Cg, hbound⟩
  have hI1 : Integrable (fun ω ↦ f ω * f (τ.toFun ω)) μ :=
    integrable_mul_comp (τ := τ) hfm hfm hCf hCf
  have hI2 : Integrable (fun ω ↦ f ω * g (τ.toFun ω)) μ :=
    integrable_mul_comp (τ := τ) hfm hgm hCf hCg
  have hI3 : Integrable (fun ω ↦ g ω * f (τ.toFun ω)) μ :=
    integrable_mul_comp (τ := τ) hgm hfm hCg hCf
  have hI4 : Integrable (fun ω ↦ g ω * g (τ.toFun ω)) μ :=
    integrable_mul_comp (τ := τ) hgm hgm hCg hCg
  have hexpand : ∀ ω, (f ω + t * g ω) * (f (τ.toFun ω) + t * g (τ.toFun ω))
      = f ω * f (τ.toFun ω) + t * (f ω * g (τ.toFun ω))
        + (t * (g ω * f (τ.toFun ω)) + t ^ 2 * (g ω * g (τ.toFun ω))) := fun ω ↦ by ring
  rw [funext hexpand] at hcomb
  have hA : Integrable (fun ω ↦ f ω * f (τ.toFun ω) + t * (f ω * g (τ.toFun ω))) μ :=
    hI1.add (hI2.const_mul t)
  have hB : Integrable
      (fun ω ↦ t * (g ω * f (τ.toFun ω)) + t ^ 2 * (g ω * g (τ.toFun ω))) μ :=
    (hI3.const_mul t).add (hI4.const_mul (t ^ 2))
  rw [integral_add hA hB, integral_add hI1 (hI2.const_mul t),
    integral_add (hI3.const_mul t) (hI4.const_mul (t ^ 2)),
    integral_const_mul, integral_const_mul, integral_const_mul, hsymm] at hcomb
  nlinarith [hcomb]

end ReflectionPositive


/-! ### The one-dimensional torus: Georgii (17.3)–(17.6) and Theorem (17.11) for `d = 1`

The sites are `ZMod (2 * N)`, Georgii's `Λ(N)` with the addition (17.2), the periodic shifts
(17.3) are the transformations `shift E j`, and the reflection `r_1` of (17.5) is `z ↦ -1 - z`
(see the module docstring for the change of coordinates). -/

section Torus

variable {E : Type*} [MeasurableSpace E] {N : ℕ} [NeZero N]

/-- The reflection `z ↦ -1 - z` in natural-number coordinates on `ZMod (2 * N)`. -/
lemma val_neg_one_sub (z : ZMod (2 * N)) : (-1 - z).val = 2 * N - 1 - z.val := by
  have hz : z.val < 2 * N := ZMod.val_lt z
  have h : (-1 : ZMod (2 * N)) - z = ((2 * N - 1 - z.val : ℕ) : ZMod (2 * N)) := by
    conv_lhs => rw [← ZMod.natCast_val_self z]
    exact ZMod.neg_one_sub_natCast hz
  rw [h]
  exact ZMod.val_natCast_of_lt (by omega)

omit [NeZero N] in
lemma neg_one_sub_neg_one_sub (z : ZMod (2 * N)) : -1 - (-1 - z) = z := by ring

omit [NeZero N] in
lemma neg_one_sub_injective : Function.Injective fun z : ZMod (2 * N) ↦ -1 - z :=
  fun _ _ h ↦ by linear_combination -h

/-- The reflection `r_1` of Georgii (17.5) on the discrete torus, in the coordinates of this
file: `z ↦ -1 - z`, an involution exchanging the two halves. -/
def torusRefl (N : ℕ) : ZMod (2 * N) ≃ ZMod (2 * N) where
  toFun z := -1 - z
  invFun z := -1 - z
  left_inv := neg_one_sub_neg_one_sub
  right_inv := neg_one_sub_neg_one_sub

/-- **Georgii (17.4).** The positive half `Λ_{+,1} = {0, …, N - 1}` of the torus. -/
def torusPos (N : ℕ) : Set (ZMod (2 * N)) := {z | z.val < N}

/-- The positive half as a `Finset`. -/
def torusPosFinset (N : ℕ) [NeZero N] : Finset (ZMod (2 * N)) :=
  Finset.univ.filter fun z ↦ z.val < N

@[simp] lemma mem_torusPosFinset {z : ZMod (2 * N)} : z ∈ torusPosFinset N ↔ z.val < N := by
  simp [torusPosFinset]

lemma coe_torusPosFinset : (torusPosFinset N : Set (ZMod (2 * N))) = torusPos N := by
  ext z; simp [torusPos]

/-- **Georgii (17.6).** The generalized reflection `r̃_1`: reflect the sites by `r_1` and apply
the involution `τ_1` to every spin. -/
def genReflection (N : ℕ) (τ : E ≃ᵐ E) : Transformation (ZMod (2 * N)) E :=
  pureSpin (ZMod (2 * N)) τ * siteEquiv E (torusRefl N)

omit [NeZero N] in
@[simp] lemma genReflection_toFun_apply (τ : E ≃ᵐ E) (ω : ZMod (2 * N) → E)
    (i : ZMod (2 * N)) : (genReflection N τ).toFun ω i = τ (ω (-1 - i)) := by
  rw [genReflection, Transformation.mul_def, Transformation.comp_toFun,
    pureSpin_toFun_apply, siteEquiv_toFun_apply]
  rfl

omit [NeZero N] in
/-- `r̃_1` is an involution of the configuration space when `τ_1` is one. -/
lemma genReflection_involutive {τ : E ≃ᵐ E} (hτ : ∀ x, τ (τ x) = x) (ω : ZMod (2 * N) → E) :
    (genReflection N τ).toFun ((genReflection N τ).toFun ω) = ω := by
  funext i
  rw [genReflection_toFun_apply, genReflection_toFun_apply, hτ, neg_one_sub_neg_one_sub]

/-- The reflection exchanges the two halves of the torus. -/
lemma compl_torusPosFinset_eq_image :
    (torusPosFinset N)ᶜ = (torusPosFinset N).image fun z ↦ -1 - z := by
  ext w
  have hw : w.val < 2 * N := ZMod.val_lt w
  simp only [Finset.mem_compl, mem_torusPosFinset, Finset.mem_image, not_lt]
  constructor
  · intro hle
    exact ⟨-1 - w, by rw [val_neg_one_sub]; omega, neg_one_sub_neg_one_sub w⟩
  · rintro ⟨z, hz, rfl⟩
    have := ZMod.val_lt z
    rw [val_neg_one_sub]
    omega

/-- The reflection exchanges the two halves of the torus (the other direction). -/
lemma image_compl_torusPosFinset :
    ((torusPosFinset N)ᶜ).image (fun z : ZMod (2 * N) ↦ -1 - z) = torusPosFinset N := by
  ext w
  have hw : w.val < 2 * N := ZMod.val_lt w
  simp only [Finset.mem_image, Finset.mem_compl, mem_torusPosFinset, not_lt]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have := ZMod.val_lt z
    rw [val_neg_one_sub]
    omega
  · intro hlt
    exact ⟨-1 - w, by rw [val_neg_one_sub]; omega, neg_one_sub_neg_one_sub w⟩

/-! #### Georgii's alphabet `A(N)` and the products of the proof of (17.11) -/

omit [NeZero N] in
/-- The colour change `a ↦ ã` of Georgii's alphabet `A(N) = Λ × {0, 1}`. -/
def flipColour (a : ZMod (2 * N) × Bool) : ZMod (2 * N) × Bool := (a.1, !a.2)

omit [NeZero N] in
lemma flipColour_involutive (a : ZMod (2 * N) × Bool) : flipColour (flipColour a) = a := by
  simp [flipColour]

omit [NeZero N] in
/-- Georgii's `τ^i` in dimension one: the involution `τ_1` iterated `i` times, which by
`τ_1 ∘ τ_1 = id` depends only on the parity of `i`. -/
def spinIterate (τ : E ≃ᵐ E) (i : ZMod (2 * N)) (x : E) : E := if Even i.val then x else τ x

omit [NeZero N] in
/-- Georgii's `f_{(n,0)} = f_n` and `f_{(n,1)} = f_n ∘ τ_1`. -/
def letterFun (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E) (a : ZMod (2 * N) × Bool) : E → ℝ :=
  fun x ↦ f a.1 (if a.2 then τ x else x)

omit [NeZero N] in
@[simp] lemma letterFun_apply (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (a : ZMod (2 * N) × Bool) (x : E) :
    letterFun f τ a x = f a.1 (if a.2 then τ x else x) := rfl

omit [NeZero N] in
/-- Precomposing a letter with the spin involution changes its colour. -/
lemma letterFun_comp_spin {f : ZMod (2 * N) → E → ℝ} {τ : E ≃ᵐ E} (hτ : ∀ x, τ (τ x) = x)
    (a : ZMod (2 * N) × Bool) (x : E) :
    letterFun f τ a (τ x) = letterFun f τ (flipColour a) x := by
  cases ha : a.2 <;> simp [flipColour, ha, hτ]

omit [NeZero N] in
lemma measurable_letterFun {f : ZMod (2 * N) → E → ℝ} (hf : ∀ n, Measurable (f n))
    (τ : E ≃ᵐ E) (a : ZMod (2 * N) × Bool) : Measurable (letterFun f τ a) := by
  unfold letterFun
  cases ha : a.2
  · simpa [ha] using hf a.1
  · simpa [ha, Function.comp_def] using (hf a.1).comp τ.measurable

/-- The product `∏_{i ∈ Λ} f_{α i}(ω_i)` of Georgii's proof of (17.11). -/
def wordProd (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E) (α : ZMod (2 * N) → ZMod (2 * N) × Bool)
    (ω : ZMod (2 * N) → E) : ℝ := ∏ z, letterFun f τ (α z) (ω z)

/-- Its factor over the positive half `Λ_{+,1}`: Georgii's `f ∈ 𝒜_{+,1}`. -/
def wordProdPos (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) : ℝ :=
  ∏ z ∈ torusPosFinset N, letterFun f τ (α z) (ω z)

/-- Its factor over the negative half. -/
def wordProdNeg (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) : ℝ :=
  ∏ z ∈ (torusPosFinset N)ᶜ, letterFun f τ (α z) (ω z)

lemma wordProd_eq_mul (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProd f τ α ω = wordProdPos f τ α ω * wordProdNeg f τ α ω :=
  (Finset.prod_mul_prod_compl _ _).symm

/-- `wordProdPos` sees only the positive half, where `foldPos` does not change the word. -/
lemma wordProdPos_foldPos (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdPos f τ (foldPos N flipColour α) ω = wordProdPos f τ α ω :=
  Finset.prod_congr rfl fun z hz ↦ by
    have hz' : z.val < N := mem_torusPosFinset.1 hz
    simp only [foldPos, hz', ite_true]

/-- `wordProdNeg` sees only the negative half, where `foldNeg` does not change the word. -/
lemma wordProdNeg_foldNeg (f : ZMod (2 * N) → E → ℝ) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdNeg f τ (foldNeg N flipColour α) ω = wordProdNeg f τ α ω :=
  Finset.prod_congr rfl fun z hz ↦ by
    have hz' : ¬ z.val < N := by simpa using Finset.mem_compl.1 hz
    simp only [foldNeg, hz', ite_false]

/-- **The reflected positive half is the negative half of the folded word.** -/
lemma wordProdPos_genReflection {f : ZMod (2 * N) → E → ℝ} {τ : E ≃ᵐ E}
    (hτ : ∀ x, τ (τ x) = x) (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdPos f τ α ((genReflection N τ).toFun ω)
      = wordProdNeg f τ (foldPos N flipColour α) ω := by
  have hstep : ∀ z ∈ torusPosFinset N,
      letterFun f τ (α z) ((genReflection N τ).toFun ω z)
        = letterFun f τ (foldPos N flipColour α (-1 - z)) (ω (-1 - z)) := by
    intro z hz
    have hz' : ¬ ((-1 - z : ZMod (2 * N)).val < N) := by
      have := mem_torusPosFinset.1 hz
      rw [val_neg_one_sub]
      omega
    rw [genReflection_toFun_apply, letterFun_comp_spin hτ]
    simp only [foldPos, hz', ite_false, neg_one_sub_neg_one_sub]
  rw [wordProdPos, Finset.prod_congr rfl hstep, wordProdNeg, compl_torusPosFinset_eq_image,
    Finset.prod_image fun x _ y _ hxy ↦ neg_one_sub_injective hxy]

/-- **The reflected negative half is the positive half of the folded word.** -/
lemma wordProdNeg_genReflection {f : ZMod (2 * N) → E → ℝ} {τ : E ≃ᵐ E}
    (hτ : ∀ x, τ (τ x) = x) (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdNeg f τ α ((genReflection N τ).toFun ω)
      = wordProdPos f τ (foldNeg N flipColour α) ω := by
  have hstep : ∀ z ∈ (torusPosFinset N)ᶜ,
      letterFun f τ (α z) ((genReflection N τ).toFun ω z)
        = letterFun f τ (foldNeg N flipColour α (-1 - z)) (ω (-1 - z)) := by
    intro z hz
    have hzc : ¬ z.val < N := by simpa using Finset.mem_compl.1 hz
    have hz' : (-1 - z : ZMod (2 * N)).val < N := by
      have := ZMod.val_lt z
      rw [val_neg_one_sub]
      omega
    rw [genReflection_toFun_apply, letterFun_comp_spin hτ]
    simp only [foldNeg, hz', ite_true, neg_one_sub_neg_one_sub]
  have himg : ∏ w ∈ ((torusPosFinset N)ᶜ).image (fun z : ZMod (2 * N) ↦ -1 - z),
        letterFun f τ (foldNeg N flipColour α w) (ω w)
      = ∏ z ∈ (torusPosFinset N)ᶜ,
        letterFun f τ (foldNeg N flipColour α (-1 - z)) (ω (-1 - z)) :=
    Finset.prod_image fun x _ y _ hxy ↦ neg_one_sub_injective hxy
  calc wordProdNeg f τ α ((genReflection N τ).toFun ω)
      = ∏ z ∈ (torusPosFinset N)ᶜ,
          letterFun f τ (foldNeg N flipColour α (-1 - z)) (ω (-1 - z)) :=
        Finset.prod_congr rfl hstep
    _ = ∏ w ∈ ((torusPosFinset N)ᶜ).image (fun z : ZMod (2 * N) ↦ -1 - z),
          letterFun f τ (foldNeg N flipColour α w) (ω w) := himg.symm
    _ = wordProdPos f τ (foldNeg N flipColour α) ω := by
        rw [wordProdPos, image_compl_torusPosFinset]


/-! #### The three products of Georgii's proof of (17.11) -/

variable {f : ZMod (2 * N) → E → ℝ} {τ : E ≃ᵐ E}

/-- Georgii's `μ(g g*)`: the word obtained by reflecting the positive half onto the negative one
is `foldPos` of the original word. -/
lemma mul_genReflection_eq_wordProd_foldPos (hτ : ∀ x, τ (τ x) = x)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdPos f τ β ω * wordProdPos f τ β ((genReflection N τ).toFun ω)
      = wordProd f τ (foldPos N flipColour β) ω := by
  rw [wordProd_eq_mul, wordProdPos_foldPos, wordProdPos_genReflection hτ]

/-- The negative half of a word is the reflected positive half of its `foldNeg`. -/
lemma wordProdNeg_eq_wordProdPos_foldNeg (hτ : ∀ x, τ (τ x) = x)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdNeg f τ β ω
      = wordProdPos f τ (foldNeg N flipColour β) ((genReflection N τ).toFun ω) := by
  have h := wordProdNeg_genReflection (f := f) hτ β ((genReflection N τ).toFun ω)
  rwa [genReflection_involutive hτ] at h

/-- Georgii's `μ(f f*)`. -/
lemma mul_genReflection_eq_wordProd_foldNeg (hτ : ∀ x, τ (τ x) = x)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdPos f τ (foldNeg N flipColour β) ω
        * wordProdPos f τ (foldNeg N flipColour β) ((genReflection N τ).toFun ω)
      = wordProd f τ (foldNeg N flipColour β) ω := by
  rw [wordProd_eq_mul, wordProdNeg_foldNeg, ← wordProdNeg_eq_wordProdPos_foldNeg hτ]

/-- Georgii's `μ(f g*)`: the word itself. -/
lemma mul_genReflection_eq_wordProd (hτ : ∀ x, τ (τ x) = x)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    wordProdPos f τ β ω
        * wordProdPos f τ (foldNeg N flipColour β) ((genReflection N τ).toFun ω)
      = wordProd f τ β ω := by
  rw [wordProd_eq_mul, ← wordProdNeg_eq_wordProdPos_foldNeg hτ]

/-! #### Measurability and boundedness -/

lemma measurable_wordProdPos (hf : ∀ n, Measurable (f n)) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) :
    Measurable[cylinderEvents (X := fun _ : ZMod (2 * N) ↦ E) (torusPos N)]
      (wordProdPos f τ α) := by
  show Measurable[cylinderEvents (X := fun _ : ZMod (2 * N) ↦ E) (torusPos N)]
    fun ω ↦ ∏ z ∈ torusPosFinset N, letterFun f τ (α z) (ω z)
  refine Finset.measurable_prod _ fun z hz ↦ ?_
  exact (measurable_letterFun hf τ (α z)).comp
    (measurable_cylinderEvent_apply (X := fun _ : ZMod (2 * N) ↦ E)
      (show z ∈ torusPos N from mem_torusPosFinset.1 hz))

lemma measurable_wordProd (hf : ∀ n, Measurable (f n)) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) : Measurable (wordProd f τ α) := by
  show Measurable fun ω : ZMod (2 * N) → E ↦ ∏ z, letterFun f τ (α z) (ω z)
  exact Finset.measurable_prod _ fun z _ ↦
    (measurable_letterFun hf τ (α z)).comp (measurable_pi_apply z)

lemma abs_wordProdPos_le {C : ℝ} (hC : ∀ n x, |f n x| ≤ C) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    |wordProdPos f τ α ω| ≤ C ^ (torusPosFinset N).card := by
  rw [wordProdPos, Finset.abs_prod]
  calc ∏ z ∈ torusPosFinset N, |letterFun f τ (α z) (ω z)|
      ≤ ∏ _z ∈ torusPosFinset N, C :=
        Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ hC _ _
    _ = C ^ (torusPosFinset N).card := Finset.prod_const C

lemma abs_wordProd_le {C : ℝ} (hC : ∀ n x, |f n x| ≤ C) (τ : E ≃ᵐ E)
    (α : ZMod (2 * N) → ZMod (2 * N) × Bool) (ω : ZMod (2 * N) → E) :
    |wordProd f τ α ω| ≤ C ^ (2 * N) := by
  rw [wordProd, Finset.abs_prod]
  calc ∏ z : ZMod (2 * N), |letterFun f τ (α z) (ω z)|
      ≤ ∏ _z : ZMod (2 * N), C :=
        Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) fun _ _ ↦ hC _ _
    _ = C ^ (2 * N) := by rw [Finset.prod_const, Finset.card_univ, ZMod.card]

/-! #### The alternating words -/

/-- The reflection reverses the parity of a site of the torus. -/
lemma even_val_neg_one_sub_iff (z : ZMod (2 * N)) : Even (-1 - z).val ↔ ¬ Even z.val := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hz : z.val < 2 * N := ZMod.val_lt z
  rw [val_neg_one_sub]
  simp only [Nat.even_iff]
  omega

/-- Folding a word that is already folded onto its negative half changes nothing. -/
lemma foldPos_foldNeg {A : Type*} {t : A → A} (ht : ∀ a, t (t a) = a)
    (β : ZMod (2 * N) → A) : foldPos N t (foldNeg N t β) = foldNeg N t β := by
  funext z
  by_cases h : z.val < N
  · simp only [foldPos, h, ite_true]
  · have h' : ((-1 - z : ZMod (2 * N))).val < N := by
      have := ZMod.val_lt z
      rw [val_neg_one_sub]
      omega
    simp only [foldPos, h, ite_false, foldNeg, h', ite_true, neg_one_sub_neg_one_sub, ht]

/-- An alternating word is its own fold: this is why Georgii may drop the absolute value on the
right-hand side of (17.11). -/
lemma foldPos_altConfig (a : ZMod (2 * N) × Bool) :
    foldPos N flipColour (altConfig N flipColour a) = altConfig N flipColour a := by
  funext z
  by_cases h : z.val < N
  · simp only [foldPos, h, ite_true]
  · simp only [foldPos, h, ite_false, altConfig_apply, even_val_neg_one_sub_iff]
    by_cases he : Even z.val <;> simp [he, flipColour_involutive]

/-- The word `(a, ã, a, ã, …)` built from the letter `(j, 0)` produces Georgii's family
`f_j ∘ τ^i` of (17.11). -/
lemma wordProd_altConfig (j : ZMod (2 * N)) (ω : ZMod (2 * N) → E) :
    wordProd f τ (altConfig N flipColour (j, false)) ω
      = ∏ i, f j (spinIterate τ i (ω i)) := by
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases h : Even i.val <;> simp [altConfig, flipColour, spinIterate, h]

lemma wordProd_baseWord (ω : ZMod (2 * N) → E) :
    wordProd f τ (fun z ↦ (z, false)) ω = ∏ i, f i (ω i) :=
  Finset.prod_congr rfl fun i _ ↦ by simp

/-! #### Georgii Theorem (17.11) in dimension one -/

section Measure

variable {μ : Measure (ZMod (2 * N) → E)} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- The `foldPos` of any word has nonnegative integral: it is of the form `h · h∘r̃_1`. -/
lemma integral_wordProd_foldPos_nonneg (hτ : ∀ x, τ (τ x) = x)
    (hpos : IsReflectionPositive (torusPos N) (genReflection N τ) μ)
    (hf : ∀ n, Measurable (f n)) {C : ℝ} (hC : ∀ n x, |f n x| ≤ C)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) :
    0 ≤ ∫ ω, wordProd f τ (foldPos N flipColour β) ω ∂μ := by
  have hEq : ∀ ω, wordProd f τ (foldPos N flipColour β) ω
      = wordProdPos f τ β ω * wordProdPos f τ β ((genReflection N τ).toFun ω) :=
    fun ω ↦ (mul_genReflection_eq_wordProd_foldPos hτ β ω).symm
  simp only [hEq]
  exact hpos (wordProdPos f τ β) (measurable_wordProdPos hf τ β)
    ⟨_, abs_wordProdPos_le hC τ β⟩

omit [IsFiniteMeasure μ] in
/-- The `foldNeg` of any word has nonnegative integral. -/
lemma integral_wordProd_foldNeg_nonneg (hτ : ∀ x, τ (τ x) = x)
    (hpos : IsReflectionPositive (torusPos N) (genReflection N τ) μ)
    (hf : ∀ n, Measurable (f n)) {C : ℝ} (hC : ∀ n x, |f n x| ≤ C)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) :
    0 ≤ ∫ ω, wordProd f τ (foldNeg N flipColour β) ω ∂μ := by
  have hEq : ∀ ω, wordProd f τ (foldNeg N flipColour β) ω
      = wordProdPos f τ (foldNeg N flipColour β) ω
        * wordProdPos f τ (foldNeg N flipColour β) ((genReflection N τ).toFun ω) :=
    fun ω ↦ (mul_genReflection_eq_wordProd_foldNeg hτ β ω).symm
  simp only [hEq]
  exact hpos (wordProdPos f τ (foldNeg N flipColour β))
    (measurable_wordProdPos hf τ _) ⟨_, abs_wordProdPos_le hC τ _⟩

/-- **Hypothesis (ii) of Lemma (17.9)** for the word functional of Georgii's proof of (17.11):
it is exactly the Cauchy–Schwarz inequality (17.8) applied to the two halves. -/
lemma sq_integral_wordProd_le (hτ : ∀ x, τ (τ x) = x)
    (hrefl : MeasurePreserving (genReflection N τ).toFun μ μ)
    (hpos : IsReflectionPositive (torusPos N) (genReflection N τ) μ)
    (hf : ∀ n, Measurable (f n)) {C : ℝ} (hC : ∀ n x, |f n x| ≤ C)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) :
    (∫ ω, wordProd f τ β ω ∂μ) ^ 2
      ≤ (∫ ω, wordProd f τ (foldPos N flipColour β) ω ∂μ)
        * (∫ ω, wordProd f τ (foldNeg N flipColour β) ω ∂μ) := by
  have key := sq_integral_mul_comp_le (Λpos := torusPos N) (τ := genReflection N τ) (μ := μ)
    hrefl (genReflection_involutive hτ) hpos
    (f := wordProdPos f τ β) (g := wordProdPos f τ (foldNeg N flipColour β))
    (measurable_wordProdPos hf τ β) ⟨_, abs_wordProdPos_le hC τ β⟩
    (measurable_wordProdPos hf τ _) ⟨_, abs_wordProdPos_le hC τ _⟩
  simp only [mul_genReflection_eq_wordProd hτ, mul_genReflection_eq_wordProd_foldPos hτ] at key
  rwa [foldPos_foldNeg flipColour_involutive] at key

omit [IsFiniteMeasure μ] in
/-- **Hypothesis (i) of Lemma (17.9)**: the `Λ`-periodicity (17.3) of `μ`. -/
lemma integral_wordProd_shift
    (hper : MeasurePreserving (shift E (1 : ZMod (2 * N))).toFun μ μ)
    (β : ZMod (2 * N) → ZMod (2 * N) × Bool) :
    ∫ ω, wordProd f τ (fun z ↦ β (z + 1)) ω ∂μ = ∫ ω, wordProd f τ β ω ∂μ := by
  have hmp : MeasurePreserving (shift E (1 : ZMod (2 * N))).toMeasurableEquiv μ μ := hper
  have h := hmp.integral_comp' (wordProd f τ β)
  have hcoe : ⇑(shift E (1 : ZMod (2 * N))).toMeasurableEquiv
      = (shift E (1 : ZMod (2 * N))).toFun := rfl
  rw [hcoe] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  show (∏ z, letterFun f τ (β (z + 1)) (ω z))
      = ∏ z, letterFun f τ (β z) ((shift E (1 : ZMod (2 * N))).toFun ω z)
  refine Fintype.prod_equiv (Equiv.addRight (1 : ZMod (2 * N))) _ _ fun z ↦ ?_
  rw [Equiv.coe_addRight, shift_toFun_apply, add_sub_cancel_right]

/-- **Georgii, Theorem (17.11) in dimension `d = 1`: the chessboard estimate.**

Let `μ` be a finite measure on `E^{Λ(N)}`, `Λ(N) = ZMod (2 * N)`, which is
* `Λ`-periodic — on the one-dimensional torus it suffices that the shift by `1` preserves `μ`,
  since it generates all the rotations (17.3) —, and
* `r̃_1`-positive (17.7) and `r̃_1`-invariant, for the generalized reflection (17.6) built from a
  measurable involution `τ_1` of `E`.

Then for every family `(f_i)_{i ∈ Λ}` of bounded measurable functions on `E`,
`|μ(∏_i f_i ∘ σ_i)|^{|Λ|} ≤ ∏_j μ(∏_i f_j ∘ τ^i ∘ σ_i)`, the root-free form of Georgii's
inequality.  The factors on the right are nonnegative by reflection positivity
(`integral_wordProd_foldPos_nonneg`), which is why they carry no absolute value. -/
theorem abs_integral_prod_pow_le {τ : E ≃ᵐ E} (hτ : ∀ x, τ (τ x) = x)
    (hper : MeasurePreserving (shift E (1 : ZMod (2 * N))).toFun μ μ)
    (hrefl : MeasurePreserving (genReflection N τ).toFun μ μ)
    (hpos : IsReflectionPositive (torusPos N) (genReflection N τ) μ)
    {f : ZMod (2 * N) → E → ℝ} (hf : ∀ n, Measurable (f n)) {C : ℝ}
    (hC : ∀ n x, |f n x| ≤ C) :
    |∫ ω, ∏ i, f i (ω i) ∂μ| ^ (2 * N)
      ≤ ∏ j : ZMod (2 * N), ∫ ω, ∏ i, f j (spinIterate τ i (ω i)) ∂μ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  set D : (ZMod (2 * N) → ZMod (2 * N) × Bool) → ℝ :=
    fun β ↦ |∫ ω, wordProd f τ β ω ∂μ| with hDdef
  have hD : ∀ β, 0 ≤ D β := fun _ ↦ abs_nonneg _
  have hDshift : ∀ β, D (fun z ↦ β (z + 1)) = D β := fun β ↦ by
    simp only [hDdef, integral_wordProd_shift hper β]
  have hDfoldPos : ∀ β, D (foldPos N flipColour β)
      = ∫ ω, wordProd f τ (foldPos N flipColour β) ω ∂μ := fun β ↦
    abs_of_nonneg (integral_wordProd_foldPos_nonneg hτ hpos hf hC β)
  have hDfoldNeg : ∀ β, D (foldNeg N flipColour β)
      = ∫ ω, wordProd f τ (foldNeg N flipColour β) ω ∂μ := fun β ↦
    abs_of_nonneg (integral_wordProd_foldNeg_nonneg hτ hpos hf hC β)
  have hDCS : ∀ β, D β ^ 2 ≤ D (foldPos N flipColour β) * D (foldNeg N flipColour β) := by
    intro β
    rw [hDfoldPos, hDfoldNeg, hDdef]
    simp only [sq_abs]
    exact sq_integral_wordProd_le hτ hrefl hpos hf hC β
  have main := pow_le_prod_of_chessboard (t := flipColour) (D := D) hN
    flipColour_involutive hD hDshift hDCS (fun z ↦ (z, false))
  have hbase : ∀ ω : ZMod (2 * N) → E, wordProd f τ (fun z ↦ (z, false)) ω = ∏ i, f i (ω i) :=
    fun ω ↦ wordProd_baseWord ω
  have hlhs : D (fun z ↦ (z, false)) = |∫ ω, ∏ i, f i (ω i) ∂μ| := by
    simp only [hDdef, hbase]
  have hrhs : ∀ j : ZMod (2 * N), D (altConfig N flipColour (j, false))
      = ∫ ω, ∏ i, f j (spinIterate τ i (ω i)) ∂μ := by
    intro j
    have heq : ∀ ω : ZMod (2 * N) → E,
        wordProd f τ (altConfig N flipColour (j, false)) ω
          = ∏ i, f j (spinIterate τ i (ω i)) := fun ω ↦ wordProd_altConfig j ω
    have hnn := integral_wordProd_foldPos_nonneg hτ hpos hf hC
      (altConfig N flipColour (j, false))
    rw [foldPos_altConfig] at hnn
    simp only [heq] at hnn
    simp only [hDdef, heq]
    exact abs_of_nonneg hnn
  rw [hlhs] at main
  refine main.trans (le_of_eq (Finset.prod_congr rfl fun j _ ↦ hrhs j))

end Measure

end Torus

end MeasureTheory.GibbsMeasure

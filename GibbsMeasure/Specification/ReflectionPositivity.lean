/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Algebra.QuadraticDiscriminant
public import GibbsMeasure.Mathlib.LinearAlgebra.BilinearMap.CauchySchwarz
public import GibbsMeasure.Mathlib.Data.ZMod.Basic
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeasurePreserving
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

  **Erratum to (17.8).**  Georgii's `𝒜_{+,k}` consists of *real* functions and `f^* = f ∘ r̃_k`
  carries no conjugation, so `(f, g) ↦ μ(f g^*)` is a real bilinear form; "nonnegative definite"
  for such a form is `μ(f f^*) ≥ 0`, and that implies Cauchy–Schwarz only through the symmetric
  part (`LinearMap.BilinMap.sq_add_swap_apply_le_of_nonneg`; a nonnegative non-symmetric form
  violating Cauchy–Schwarz is `LinearMap.BilinMap.notSymm`).  The three results below say exactly
  what is missing and that it is not free:
  - `integral_mul_comp_comm`: if `μ` is `r̃_k`-invariant the form is symmetric.  This is the step
    Georgii's "of course" uses.
  - `measurePreserving_of_integral_mul_comp_comm` and
    `measurePreserving_iff_integral_mul_comp_comm`: conversely, when `Λ_{+,k} ∪ r_k Λ_{+,k}` is
    the whole site set, symmetry of the form on the bounded `𝓕_{Λ_{+,k}}`-measurable functions
    *forces* `r̃_k`-invariance (π–λ on `𝓕_{Λ_{+,k}} ∨ 𝓕_{r_k Λ_{+,k}}`).  So `hinv` is not a
    strengthening of Georgii's hypothesis: it is his hypothesis, made explicit.
  - `exists_isReflectionPositive_not_sq_integral_mul_comp_le` and the section
    `ReflectionCounterexample`: two sites, two spin values, and the measure `!![1, 2; 0, 1]` —
    reflection positive, not reflection invariant, and `μ(f g^*)^2 = 4 > 1 = μ(f f^*) μ(g g^*)`.
    Since every §17.2 measure Georgii applies (17.8) to *is* reflection invariant, none of his
    applications is affected.
* `MeasureTheory.GibbsMeasure.abs_integral_prod_pow_le`: **Georgii, Theorem (17.11) for `d = 1`**,
  `|μ(∏_i f_i ∘ σ_i)|^{2N} ≤ ∏_j μ(∏_i f_j ∘ τ^i ∘ σ_i)`.  The dictionary between words over
  `A(N)` and products of single-spin functions is `wordProd`, and the two halves of a word are
  `wordProdPos` / `wordProdNeg`; `wordProdPos_genReflection` and `wordProdNeg_genReflection` are
  the identifications `f* ` of Georgii's proof, and `sq_integral_wordProd_le` /
  `integral_wordProd_shift` are hypotheses (ii) and (i) of (17.9) for `D = |μ(wordProd ·)|`.

* `MeasureTheory.GibbsMeasure.abs_integral_prod_pow_le_pi`: **Georgii, Theorem (17.11)** on the
  `d`-dimensional torus `Λ = (ℤ/2N)^d`,
  `|μ(∏_i f_i ∘ σ_i)|^{|Λ|} ≤ ∏_j μ(∏_i f_j ∘ τ^i ∘ σ_i)`, where `τ^i` is the iterated
  involution (17.10) `tauPow τ i`.  Georgii's proof is an induction on `d`: `splitTail` views
  `μ` on `(E^{Λ_0})^{Λ_1}` and `splitHead` views it on `(E^{Λ_1})^{Λ_0}`, the section `Split`
  transports the three hypotheses along both views, and `abs_integral_prod_pow_le_pi_abs` runs
  the induction with absolute values on both sides.  `integral_prod_tauPow_nonneg` then removes
  the absolute value on the right, using reflection positivity in the direction `0` alone.

## Not formalised here

Georgii's coarse-graining (17.12)–(17.17) to functions of the elementary cubes `C(i)` and his
§17.2 are in `GibbsMeasure.Specification.PeriodicGibbs`, which imports this file.
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

/-- **The reflection form is symmetric when `μ` is reflection invariant.**  If `μ` is invariant
under the involution `τ̃` then `μ(f · g∘τ̃) = μ(g · f∘τ̃)`, because substituting `ω ↦ τ̃ ω`
exchanges the two factors.  This is the step Georgii's (17.8) uses silently. -/
theorem integral_mul_comp_comm {τ : Transformation S E} {μ : Measure (S → E)}
    (hinv : MeasurePreserving τ.toFun μ μ) (hτ : ∀ ω, τ.toFun (τ.toFun ω) = ω)
    (f g : (S → E) → ℝ) :
    ∫ ω, f ω * g (τ.toFun ω) ∂μ = ∫ ω, g ω * f (τ.toFun ω) ∂μ := by
  have hmp : MeasurePreserving τ.toMeasurableEquiv μ μ := hinv
  have h := hmp.integral_comp' (fun ω ↦ f ω * g (τ.toFun ω))
  have hcoe : ⇑τ.toMeasurableEquiv = τ.toFun := rfl
  rw [hcoe] at h
  simp only [hτ] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

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
  have hsymm : ∫ ω, g ω * f (τ.toFun ω) ∂μ = ∫ ω, f ω * g (τ.toFun ω) ∂μ :=
    integral_mul_comp_comm hinv hτ g f
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

/-! ### Georgii (17.8): the symmetry of the form is exactly reflection invariance

Georgii calls the form `(f, g) ↦ μ(f g^*)` nonnegative definite and deduces Cauchy–Schwarz
"of course".  For a *real* bilinear form nonnegativity alone bounds only the symmetric part
(`LinearMap.BilinMap.sq_add_swap_apply_le_of_nonneg`), and the two lemmas below identify the
missing hypothesis: the form is symmetric if and only if `μ` is `τ̃`-invariant, provided the two
halves cover the site set.  `ReflectionCounterexample` below shows that (17.8) really is false
without it. -/

/-- **Symmetry of the reflection form forces reflection invariance.**  Let `τ̃` be an involution
of `E^S` whose spatial part `τ_*` is an involution of the sites, and suppose the half `Λpos` and
its reflection `τ_* Λpos = τ_*⁻¹ Λpos` cover the site set.  If the bilinear form
`(f, g) ↦ μ(f · g∘τ̃)` is symmetric on the bounded `cylinderEvents Λpos`-measurable functions,
then `μ` is `τ̃`-invariant.

Indicators turn the symmetry into `μ(A ∩ B) = (τ̃ μ)(A ∩ B)` for `A ∈ 𝓕_{Λ₊}` and
`B ∈ 𝓕_{τ_* Λ₊}`; those intersections are a π-system generating
`𝓕_{Λ₊} ⊔ 𝓕_{τ_* Λ₊} = 𝓕_{Λ₊ ∪ τ_* Λ₊} = 𝓕_S`, so the two finite measures agree.  Together with
`integral_mul_comp_comm`, this says the hypothesis `hinv` of `sq_integral_mul_comp_le` *is* the
symmetry of Georgii's form, not an extra assumption. -/
theorem measurePreserving_of_integral_mul_comp_comm {Λpos : Set S} {τ : Transformation S E}
    {μ : Measure (S → E)} [IsFiniteMeasure μ]
    (hsites : ∀ i, τ.sites (τ.sites i) = i) (hτ : ∀ ω, τ.toFun (τ.toFun ω) = ω)
    (hcover : Λpos ∪ τ.sites ⁻¹' Λpos = univ)
    (hsymm : ∀ f g : (S → E) → ℝ,
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f → (∃ C, ∀ ω, |f ω| ≤ C) →
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, f ω * g (τ.toFun ω) ∂μ = ∫ ω, g ω * f (τ.toFun ω) ∂μ) :
    MeasurePreserving τ.toFun μ μ := by
  classical
  have hmeas : Measurable τ.toFun := τ.measurable_toFun
  set ν : Measure (S → E) := Measure.map τ.toFun μ with hνdef
  have hνuniv : ν univ = μ univ := by
    rw [hνdef, Measure.map_apply hmeas MeasurableSet.univ, preimage_univ]
  have hνapply : ∀ s, MeasurableSet s → ν s = μ (τ.toFun ⁻¹' s) := fun s hs ↦ by
    rw [hνdef, Measure.map_apply hmeas hs]
  haveI : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top μ univ⟩
  -- the reflected half, and the transport of cylinder measurability along `τ̃`
  have hsq : τ.sites ⁻¹' (τ.sites ⁻¹' Λpos) = Λpos := by
    ext i; simp only [mem_preimage, hsites i]
  have hmB : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos,
      cylinderEvents (X := fun _ : S ↦ E) (τ.sites ⁻¹' Λpos)] τ.toFun := by
    have h := τ.measurable_toFun_cylinderEvents (τ.sites ⁻¹' Λpos)
    rwa [hsq] at h
  -- the generating π-system of "rectangles" straddling the plane of the reflection
  set C : Set (Set (S → E)) :=
    {s | ∃ A B, MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) Λpos] A ∧
      MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (τ.sites ⁻¹' Λpos)] B ∧ s = A ∩ B}
    with hCdef
  have hgen : (inferInstance : MeasurableSpace (S → E)) = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ ?_
    · have hle : cylinderEvents (X := fun _ : S ↦ E) univ ≤ MeasurableSpace.generateFrom C := by
        rw [← hcover, cylinderEvents_union]
        refine sup_le (fun A hA ↦ ?_) (fun B hB ↦ ?_)
        · exact MeasurableSpace.measurableSet_generateFrom
            ⟨A, univ, hA, MeasurableSet.univ, (inter_univ A).symm⟩
        · exact MeasurableSpace.measurableSet_generateFrom
            ⟨univ, B, MeasurableSet.univ, hB, (univ_inter B).symm⟩
      simpa using hle
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨A, B, hA, hB, rfl⟩
      exact (cylinderEvents_le_pi A hA).inter (cylinderEvents_le_pi B hB)
  have hpi : IsPiSystem C := by
    rintro _ ⟨A₁, B₁, hA₁, hB₁, rfl⟩ _ ⟨A₂, B₂, hA₂, hB₂, rfl⟩ -
    exact ⟨A₁ ∩ A₂, B₁ ∩ B₂, hA₁.inter hA₂, hB₁.inter hB₂, by
      ext ω; simp only [mem_inter_iff]; tauto⟩
  -- the symmetry of the form on indicators is the agreement of `μ` and `ν` on `C`
  have hCeq : ∀ s ∈ C, μ s = ν s := by
    rintro _ ⟨A, B, hA, hB, rfl⟩
    have hAm : MeasurableSet A := cylinderEvents_le_pi A hA
    have hBm : MeasurableSet B := cylinderEvents_le_pi B hB
    set f : (S → E) → ℝ := A.indicator 1 with hf
    set g : (S → E) → ℝ := (τ.toFun ⁻¹' B).indicator 1 with hg
    have hfm : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f :=
      Measurable.indicator measurable_const hA
    have hgm : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] g :=
      Measurable.indicator measurable_const (hmB hB)
    have hbound : ∀ (s : Set (S → E)) ω, |s.indicator (1 : (S → E) → ℝ) ω| ≤ 1 := by
      intro s ω
      rw [Set.indicator_apply]
      split <;> simp
    have hprod : ∀ (s t : Set (S → E)) ω,
        (s ∩ t).indicator (1 : (S → E) → ℝ) ω = s.indicator 1 ω * t.indicator 1 ω := by
      intro s t ω
      by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;>
        simp [Set.indicator_apply, hs, ht]
    -- `g ∘ τ̃ = 1_B` and `f ∘ τ̃ = 1_{τ̃⁻¹ A}`
    have hgτ : ∀ ω, g (τ.toFun ω) = B.indicator (1 : (S → E) → ℝ) ω := by
      intro ω
      simp only [hg, Set.indicator_apply, mem_preimage, hτ ω, Pi.one_apply]
    have hleft : ∫ ω, f ω * g (τ.toFun ω) ∂μ = (μ (A ∩ B)).toReal := by
      have hpt : ∀ ω, f ω * g (τ.toFun ω) = (A ∩ B).indicator (1 : (S → E) → ℝ) ω := by
        intro ω
        rw [hgτ ω, hf, hprod]
      rw [funext hpt, integral_indicator_one (hAm.inter hBm), measureReal_def]
    have hright : ∫ ω, g ω * f (τ.toFun ω) ∂μ = (ν (A ∩ B)).toReal := by
      have hfτ : ∀ ω, f (τ.toFun ω) = (τ.toFun ⁻¹' A).indicator (1 : (S → E) → ℝ) ω := by
        intro ω; simp only [hf, Set.indicator_apply, mem_preimage, Pi.one_apply]
      have hpt : ∀ ω, g ω * f (τ.toFun ω)
          = (τ.toFun ⁻¹' (A ∩ B)).indicator (1 : (S → E) → ℝ) ω := by
        intro ω
        rw [hfτ ω, hg, preimage_inter, hprod, mul_comm]
      rw [funext hpt, integral_indicator_one (hmeas (hAm.inter hBm)), measureReal_def,
        hνapply _ (hAm.inter hBm)]
    have hkey := hsymm f g hfm ⟨1, hbound A⟩ hgm ⟨1, hbound _⟩
    rw [hleft, hright] at hkey
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).1 hkey
  have hμν : μ = ν := ext_of_generate_finite C hgen hpi hCeq hνuniv.symm
  exact ⟨hmeas, hμν.symm⟩

/-- **Georgii (17.8): the missing hypothesis, as an equivalence.**  For a finite measure on
`E^S` whose reflection `τ̃` is an involution with involutive spatial part, and two halves covering
the site set, reflection invariance of `μ` is *equivalent* to the symmetry of Georgii's bilinear
form `(f, g) ↦ μ(f · g∘τ̃)` on `𝒜_{+,k}`. -/
theorem measurePreserving_iff_integral_mul_comp_comm {Λpos : Set S} {τ : Transformation S E}
    {μ : Measure (S → E)} [IsFiniteMeasure μ]
    (hsites : ∀ i, τ.sites (τ.sites i) = i) (hτ : ∀ ω, τ.toFun (τ.toFun ω) = ω)
    (hcover : Λpos ∪ τ.sites ⁻¹' Λpos = univ) :
    MeasurePreserving τ.toFun μ μ ↔ ∀ f g : (S → E) → ℝ,
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f → (∃ C, ∀ ω, |f ω| ≤ C) →
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, f ω * g (τ.toFun ω) ∂μ = ∫ ω, g ω * f (τ.toFun ω) ∂μ :=
  ⟨fun hinv f g _ _ _ _ ↦ integral_mul_comp_comm hinv hτ f g,
    measurePreserving_of_integral_mul_comp_comm hsites hτ hcover⟩

/-! ### Georgii (17.8) is false without reflection invariance

Two sites, `Λ = {false, true}` with `Λ_+ = {false}`, two spin values `E = Bool`, and the
reflection `r` that exchanges the two sites (with `τ = id`).  A measure on `E^Λ` is a
`2 × 2` matrix `M x y = μ{ω : ω_false = x, ω_true = y}`, the reflection form is
`μ(f · g∘r) = ∑_{x, y} f(x) g(y) M x y`, and `μ` is reflection positive exactly when the
quadratic form of `M` is nonnegative.  The matrix `!![1, 2; 0, 1]` has quadratic form
`(a + b)^2 ≥ 0` but is not symmetric, and Cauchy–Schwarz fails at the two coordinate
indicators, where `μ(f g^*) = 2` while `μ(f f^*) = μ(g g^*) = 1`.

Every hypothesis of `measurePreserving_iff_integral_mul_comp_comm` holds here except reflection
invariance, so (17.8) as Georgii states it — with no hypothesis beyond (17.7) — is false, and
`sq_integral_mul_comp_le` cannot drop `hinv`. -/

namespace ReflectionCounterexample

/-- The configuration with spin `x` at the site `false` and spin `y` at the site `true`. -/
def cfg (x y : Bool) : Bool → Bool := fun i ↦ cond i y x

@[simp] lemma cfg_false (x y : Bool) : cfg x y false = x := rfl

@[simp] lemma cfg_true (x y : Bool) : cfg x y true = y := rfl

/-- Georgii's `Λ_{+,1}`: the single site `false`. -/
def posHalf : Set Bool := {false}

/-- Georgii's `r̃_1` here: the transposition of the two sites, with the identity spin
involution. -/
def siteSwap : Transformation Bool Bool := siteEquiv Bool (Equiv.swap false true)

@[simp] lemma siteSwap_cfg (x y : Bool) : siteSwap.toFun (cfg x y) = cfg y x := by
  funext i
  cases i <;> simp [siteSwap, cfg]

lemma siteSwap_involutive (ω : Bool → Bool) :
    siteSwap.toFun (siteSwap.toFun ω) = ω := by
  funext i
  simp [siteSwap]

lemma siteSwap_sites_involutive (i : Bool) : siteSwap.sites (siteSwap.sites i) = i := by
  simp [siteSwap]

lemma posHalf_union_preimage : posHalf ∪ siteSwap.sites ⁻¹' posHalf = Set.univ := by
  ext i
  cases i <;> simp [posHalf, siteSwap]

/-- The measure `!![1, 2; 0, 1]` on `E^Λ`: mass `1` on `(false, false)`, mass `2` on
`(false, true)`, mass `0` on `(true, false)` and mass `1` on `(true, true)`. -/
noncomputable def refMeasure : Measure (Bool → Bool) :=
  Measure.dirac (cfg false false) + Measure.dirac (cfg false true)
    + Measure.dirac (cfg false true) + Measure.dirac (cfg true true)

noncomputable instance : IsFiniteMeasure refMeasure := by
  unfold refMeasure; infer_instance

lemma integral_refMeasure (h : (Bool → Bool) → ℝ) :
    ∫ ω, h ω ∂refMeasure
      = h (cfg false false) + 2 * h (cfg false true) + h (cfg true true) := by
  have hint : ∀ ω₀ : Bool → Bool, Integrable h (Measure.dirac ω₀) := fun _ ↦ Integrable.of_finite
  rw [refMeasure,
    integral_add_measure (((hint _).add_measure (hint _)).add_measure (hint _)) (hint _),
    integral_add_measure ((hint _).add_measure (hint _)) (hint _),
    integral_add_measure (hint _) (hint _)]
  simp only [integral_dirac]
  ring

/-- **The counterexample measure is reflection positive**: the quadratic form of `!![1, 2; 0, 1]`
is `(a + b) ^ 2`. -/
theorem isReflectionPositive_refMeasure :
    IsReflectionPositive posHalf siteSwap refMeasure := by
  intro f hf _
  have hdep : DependsOn f posHalf := hf.dependsOn_of_cylinderEvents
  have hA : f (cfg false false) = f (cfg false true) := by
    refine hdep fun i hi ↦ ?_
    rw [show i = false from hi]
    rfl
  have hB : f (cfg true false) = f (cfg true true) := by
    refine hdep fun i hi ↦ ?_
    rw [show i = false from hi]
    rfl
  rw [integral_refMeasure fun ω ↦ f ω * f (siteSwap.toFun ω)]
  simp only [siteSwap_cfg]
  rw [← hA, ← hB]
  nlinarith [sq_nonneg (f (cfg false false) + f (cfg true false))]

/-- The indicator of `{ω : ω_false = false}`, a bounded function of the coordinates in `Λ_+`. -/
def fPos (ω : Bool → Bool) : ℝ := if ω false then 0 else 1

/-- The indicator of `{ω : ω_false = true}`, a bounded function of the coordinates in `Λ_+`. -/
def fNeg (ω : Bool → Bool) : ℝ := if ω false then 1 else 0

lemma measurable_fPos : Measurable[cylinderEvents (X := fun _ : Bool ↦ Bool) posHalf] fPos := by
  have h : fPos = (fun b : Bool ↦ if b then (0 : ℝ) else 1) ∘ fun ω : Bool → Bool ↦ ω false := rfl
  rw [h]
  exact (measurable_of_countable _).comp
    (measurable_cylinderEvent_apply (X := fun _ : Bool ↦ Bool) (Set.mem_singleton false))

lemma measurable_fNeg : Measurable[cylinderEvents (X := fun _ : Bool ↦ Bool) posHalf] fNeg := by
  have h : fNeg = (fun b : Bool ↦ if b then (1 : ℝ) else 0) ∘ fun ω : Bool → Bool ↦ ω false := rfl
  rw [h]
  exact (measurable_of_countable _).comp
    (measurable_cylinderEvent_apply (X := fun _ : Bool ↦ Bool) (Set.mem_singleton false))

lemma abs_fPos_le (ω : Bool → Bool) : |fPos ω| ≤ 1 := by
  rw [fPos]; split <;> simp

lemma abs_fNeg_le (ω : Bool → Bool) : |fNeg ω| ≤ 1 := by
  rw [fNeg]; split <;> simp

@[simp] lemma integral_fPos_mul_fNeg :
    ∫ ω, fPos ω * fNeg (siteSwap.toFun ω) ∂refMeasure = 2 := by
  rw [integral_refMeasure]
  norm_num [fPos, fNeg]

@[simp] lemma integral_fNeg_mul_fPos :
    ∫ ω, fNeg ω * fPos (siteSwap.toFun ω) ∂refMeasure = 0 := by
  rw [integral_refMeasure]
  norm_num [fPos, fNeg]

@[simp] lemma integral_fPos_mul_fPos :
    ∫ ω, fPos ω * fPos (siteSwap.toFun ω) ∂refMeasure = 1 := by
  rw [integral_refMeasure]
  norm_num [fPos]

@[simp] lemma integral_fNeg_mul_fNeg :
    ∫ ω, fNeg ω * fNeg (siteSwap.toFun ω) ∂refMeasure = 1 := by
  rw [integral_refMeasure]
  norm_num [fNeg]

/-- **The counterexample measure is not reflection invariant.**  Its reflection form is not
symmetric: `μ(f g^*) = 2` while `μ(g f^*) = 0`. -/
theorem not_measurePreserving_siteSwap :
    ¬ MeasurePreserving siteSwap.toFun refMeasure refMeasure := by
  intro hinv
  have h := integral_mul_comp_comm hinv siteSwap_involutive fPos fNeg
  rw [integral_fPos_mul_fNeg, integral_fNeg_mul_fPos] at h
  norm_num at h

/-- **Georgii (17.8) fails for a reflection positive measure that is not reflection invariant**:
here `μ(f g^*) ^ 2 = 4` while `μ(f f^*) · μ(g g^*) = 1`. -/
theorem not_sq_integral_mul_comp_le :
    ¬ ((∫ ω, fPos ω * fNeg (siteSwap.toFun ω) ∂refMeasure) ^ 2
        ≤ (∫ ω, fPos ω * fPos (siteSwap.toFun ω) ∂refMeasure)
          * (∫ ω, fNeg ω * fNeg (siteSwap.toFun ω) ∂refMeasure)) := by
  rw [integral_fPos_mul_fNeg, integral_fPos_mul_fPos, integral_fNeg_mul_fNeg]
  norm_num

end ReflectionCounterexample

/-- **The reflection invariance in `sq_integral_mul_comp_le` cannot be dropped.**  There is a
finite measure `μ` on `E^S` which is reflection positive for a half `Λ_+` whose reflection covers
the complement, together with two bounded `cylinderEvents Λ_+`-measurable functions violating
Georgii's Cauchy–Schwarz inequality (17.8).  Necessarily `μ` is not reflection invariant. -/
theorem exists_isReflectionPositive_not_sq_integral_mul_comp_le :
    ∃ (S E : Type) (_ : MeasurableSpace E) (Λpos : Set S) (τ : Transformation S E)
      (μ : Measure (S → E)) (_ : IsFiniteMeasure μ) (f g : (S → E) → ℝ),
      (∀ ω, τ.toFun (τ.toFun ω) = ω) ∧ (∀ i, τ.sites (τ.sites i) = i) ∧
      Λpos ∪ τ.sites ⁻¹' Λpos = univ ∧
      IsReflectionPositive Λpos τ μ ∧
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] f ∧ (∀ ω, |f ω| ≤ 1) ∧
      Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos] g ∧ (∀ ω, |g ω| ≤ 1) ∧
      ¬ ((∫ ω, f ω * g (τ.toFun ω) ∂μ) ^ 2
          ≤ (∫ ω, f ω * f (τ.toFun ω) ∂μ) * (∫ ω, g ω * g (τ.toFun ω) ∂μ)) :=
  ⟨Bool, Bool, inferInstance, ReflectionCounterexample.posHalf,
    ReflectionCounterexample.siteSwap, ReflectionCounterexample.refMeasure, inferInstance,
    ReflectionCounterexample.fPos, ReflectionCounterexample.fNeg,
    ReflectionCounterexample.siteSwap_involutive,
    ReflectionCounterexample.siteSwap_sites_involutive,
    ReflectionCounterexample.posHalf_union_preimage,
    ReflectionCounterexample.isReflectionPositive_refMeasure,
    ReflectionCounterexample.measurable_fPos, ReflectionCounterexample.abs_fPos_le,
    ReflectionCounterexample.measurable_fNeg, ReflectionCounterexample.abs_fNeg_le,
    ReflectionCounterexample.not_sq_integral_mul_comp_le⟩

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

omit [IsFiniteMeasure μ] in
/-- The right-hand side factors of Georgii's (17.11) are nonnegative: `∏_i f_j ∘ τ^i ∘ σ_i` is
the word `(j, j̃, j, j̃, …)`, which is its own fold, hence of the form `h · h∘r̃_1`. -/
lemma integral_prod_spinIterate_nonneg (hτ : ∀ x, τ (τ x) = x)
    (hpos : IsReflectionPositive (torusPos N) (genReflection N τ) μ)
    (hf : ∀ n, Measurable (f n)) {C : ℝ} (hC : ∀ n x, |f n x| ≤ C) (j : ZMod (2 * N)) :
    0 ≤ ∫ ω, ∏ i, f j (spinIterate τ i (ω i)) ∂μ := by
  have hnn := integral_wordProd_foldPos_nonneg hτ hpos hf hC (altConfig N flipColour (j, false))
  rw [foldPos_altConfig] at hnn
  simpa only [wordProd_altConfig] using hnn

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


/-! ### Transport of reflection positivity along a measurable map

Georgii's proof of (17.11) "thinks of `μ` as a measure on `(E^{Λ₀})^{Λ₁}`", and the coarse-graining
(17.16) views `μ` on `(E^C)^Λ`.  Both are image measures `μ.map Ψ`, and reflection positivity is
carried along `Ψ` as soon as `Ψ` intertwines the two reflections and carries the σ-algebra of the
positive half into the σ-algebra of the positive half. -/

section Transport

variable {S S' E E' : Type*} [MeasurableSpace E] [MeasurableSpace E']

/-- **Reflection positivity is pushed forward** along a measurable `Ψ` with `τ' ∘ Ψ = Ψ ∘ τ` that
is measurable from `𝓕_{Λpos}` to `𝓕_{Λpos'}`. -/
lemma IsReflectionPositive.map {Λpos : Set S} {Λpos' : Set S'} {τ : Transformation S E}
    {τ' : Transformation S' E'} {μ : Measure (S → E)} (hpos : IsReflectionPositive Λpos τ μ)
    {Ψ : (S → E) → (S' → E')} (hΨ : Measurable Ψ)
    (hΨc : Measurable[cylinderEvents (X := fun _ : S ↦ E) Λpos,
      cylinderEvents (X := fun _ : S' ↦ E') Λpos'] Ψ)
    (hcomm : ∀ ω, τ'.toFun (Ψ ω) = Ψ (τ.toFun ω)) :
    IsReflectionPositive Λpos' τ' (μ.map Ψ) := by
  intro f hf hfb
  have hfm : Measurable f := hf.mono cylinderEvents_le_pi le_rfl
  rw [integral_map hΨ.aemeasurable (f := fun ω ↦ f ω * f (τ'.toFun ω))
    (hfm.mul (hfm.comp τ'.measurable_toFun)).aestronglyMeasurable]
  simp only [hcomm]
  exact hpos (f ∘ Ψ) (hf.comp hΨc) (hfb.imp fun C hC ω ↦ hC _)

end Transport


/-! ### The `d`-dimensional torus: Georgii (17.1)–(17.6) and Theorem (17.11)

Georgii's `Λ(N) = ]-N, N]^d ∩ ℤ^d` with the addition (17.2) is `Fin d → ZMod (2 * N)`.  The
reflection `r_k` of (17.5) in the plane between the sites, the half `Λ_{+,k}` of (17.4), the
generalized reflection `r̃_k` of (17.6) and the iterated involutions `τ^i` of (17.10) are
`torusReflAt`, `torusPosAt`, `genReflectionAt` and `tauPow`. -/

section Lattice

variable {E : Type*} [MeasurableSpace E] {N d : ℕ}

/-- **Georgii (17.5) in direction `k`.** The reflection `r_k` of the torus in the plane between
the sites, `z ↦ -1 - z` in the `k`-th coordinate (see the module docstring for the change of
coordinates from Georgii's labels). -/
def torusReflAt (N : ℕ) (k : Fin d) : (Fin d → ZMod (2 * N)) ≃ (Fin d → ZMod (2 * N)) where
  toFun i := Function.update i k (-1 - i k)
  invFun i := Function.update i k (-1 - i k)
  left_inv i := by simp [Function.update_idem]
  right_inv i := by simp [Function.update_idem]

lemma torusReflAt_apply (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    torusReflAt N k i = Function.update i k (-1 - i k) := rfl

@[simp] lemma torusReflAt_symm (k : Fin d) : (torusReflAt N k).symm = torusReflAt N k := rfl

@[simp] lemma torusReflAt_apply_self (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    torusReflAt N k i k = -1 - i k := by simp [torusReflAt_apply]

lemma torusReflAt_apply_of_ne {k l : Fin d} (h : l ≠ k) (i : Fin d → ZMod (2 * N)) :
    torusReflAt N k i l = i l := by simp [torusReflAt_apply, h]

lemma torusReflAt_torusReflAt (k : Fin d) (i : Fin d → ZMod (2 * N)) :
    torusReflAt N k (torusReflAt N k i) = i := (torusReflAt N k).left_inv i

/-- **Georgii (17.4).** The positive half `Λ_{+,k} = {i : 0 ≤ i_k ≤ N - 1}` of the torus in
direction `k`. -/
def torusPosAt (N : ℕ) (k : Fin d) : Set (Fin d → ZMod (2 * N)) := {i | (i k).val < N}

@[simp] lemma mem_torusPosAt {k : Fin d} {i : Fin d → ZMod (2 * N)} :
    i ∈ torusPosAt N k ↔ (i k).val < N := Iff.rfl

/-- **Georgii (17.6) in direction `k`.** The generalized reflection `r̃_k`: reflect the sites by
`r_k` and apply the involution `τ_k` to every spin. -/
def genReflectionAt (N : ℕ) (τ : Fin d → E ≃ᵐ E) (k : Fin d) :
    Transformation (Fin d → ZMod (2 * N)) E :=
  pureSpin (Fin d → ZMod (2 * N)) (τ k) * siteEquiv E (torusReflAt N k)

@[simp] lemma genReflectionAt_toFun_apply (τ : Fin d → E ≃ᵐ E) (k : Fin d)
    (ω : (Fin d → ZMod (2 * N)) → E) (i : Fin d → ZMod (2 * N)) :
    (genReflectionAt N τ k).toFun ω i = τ k (ω (torusReflAt N k i)) := by
  rw [genReflectionAt, Transformation.mul_def, Transformation.comp_toFun,
    pureSpin_toFun_apply, siteEquiv_toFun_apply, torusReflAt_symm]

/-- **Georgii (17.10).** The iterated involution `τ^i = τ_1^{i_1} ∘ ⋯ ∘ τ_d^{i_d}` of `E`, each
`τ_k` being applied when `i_k` is odd.  Georgii assumes the `τ_k` commute, so that the order of
composition is immaterial; here the factors are applied in the order of the coordinates, and no
commutation is needed anywhere. -/
def tauPow (τ : Fin d → E ≃ᵐ E) (i : Fin d → ZMod (2 * N)) (x : E) : E :=
  Fin.foldl d (fun x k ↦ spinIterate (τ k) (i k) x) x

@[simp] lemma tauPow_zero (τ : Fin 0 → E ≃ᵐ E) (i : Fin 0 → ZMod (2 * N)) (x : E) :
    tauPow τ i x = x := Fin.foldl_zero _ _

lemma tauPow_succ (τ : Fin (d + 1) → E ≃ᵐ E) (i : Fin (d + 1) → ZMod (2 * N)) (x : E) :
    tauPow τ i x = tauPow (fun k ↦ τ k.succ) (Fin.tail i) (spinIterate (τ 0) (i 0) x) :=
  Fin.foldl_succ _ _

lemma tauPow_cons (τ : Fin (d + 1) → E ≃ᵐ E) (i₀ : ZMod (2 * N)) (i₁ : Fin d → ZMod (2 * N))
    (x : E) :
    tauPow τ (Fin.cons i₀ i₁) x = tauPow (fun k ↦ τ k.succ) i₁ (spinIterate (τ 0) i₀ x) := by
  rw [tauPow_succ, Fin.cons_zero, Fin.tail_cons]

lemma measurable_spinIterate (τ : E ≃ᵐ E) (i : ZMod (2 * N)) :
    Measurable (spinIterate τ i) := by
  unfold spinIterate
  split_ifs <;> fun_prop

lemma measurable_tauPow (τ : Fin d → E ≃ᵐ E) (i : Fin d → ZMod (2 * N)) :
    Measurable (tauPow τ i) := by
  induction d with
  | zero =>
      have h : tauPow τ i = id := funext fun x ↦ tauPow_zero τ i x
      rw [h]; exact measurable_id
  | succ d ih =>
      have h : tauPow τ i = tauPow (fun k ↦ τ k.succ) (Fin.tail i) ∘ spinIterate (τ 0) (i 0) :=
        funext fun x ↦ tauPow_succ τ i x
      rw [h]
      exact (ih _ _).comp (measurable_spinIterate _ _)

/-- The spin involution acting coordinatewise on `T → E`: Georgii's `τ_k` viewed as an
involution of `E^{Λ₀}` in the induction step of the proof of (17.11). -/
abbrev coordInvolution (T : Type*) (τ : E ≃ᵐ E) : (T → E) ≃ᵐ (T → E) :=
  MeasurableEquiv.piCongrRight fun _ : T ↦ τ

@[simp] lemma coordInvolution_apply {T : Type*} (τ : E ≃ᵐ E) (ζ : T → E) (t : T) :
    coordInvolution T τ ζ t = τ (ζ t) := rfl

lemma spinIterate_coordInvolution {T : Type*} (τ : E ≃ᵐ E) (i : ZMod (2 * N)) (ζ : T → E)
    (t : T) : spinIterate (coordInvolution T τ) i ζ t = spinIterate τ i (ζ t) := by
  unfold spinIterate
  split_ifs <;> rfl

lemma tauPow_coordInvolution {T : Type*} (τ : Fin d → E ≃ᵐ E) (i : Fin d → ZMod (2 * N))
    (ζ : T → E) (t : T) :
    tauPow (fun k ↦ coordInvolution T (τ k)) i ζ t = tauPow τ i (ζ t) := by
  induction d generalizing ζ with
  | zero => simp
  | succ d ih =>
      rw [tauPow_succ, tauPow_succ, ih, spinIterate_coordInvolution]

end Lattice


/-! ### Splitting off one coordinate direction

Georgii's induction step for (17.11) writes `Λ = Λ₀ × Λ₁` and views `μ` first on `(E^{Λ₀})^{Λ₁}`
and then on `(E^{Λ₁})^{Λ₀}`.  With `Λ = Fin (d + 1) → ZMod (2 * N)`, `Λ₀` is the coordinate `0`
and `Λ₁` the remaining ones; the two views are the image measures of `μ` under `splitTail` and
`splitHead`. -/

section Split

variable {E : Type*} [MeasurableSpace E] {N d : ℕ}

/-- `E^Λ` viewed as `(E^{Λ₁})^{Λ₀}`: the site `i₀ ∈ Λ₀` outside, `i₁ ∈ Λ₁` inside. -/
def splitHead (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    ZMod (2 * N) → (Fin d → ZMod (2 * N)) → E :=
  fun i₀ i₁ ↦ ω (Fin.cons i₀ i₁)

/-- `E^Λ` viewed as `(E^{Λ₀})^{Λ₁}`: the site `i₁ ∈ Λ₁` outside, `i₀ ∈ Λ₀` inside. -/
def splitTail (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    (Fin d → ZMod (2 * N)) → ZMod (2 * N) → E :=
  fun i₁ i₀ ↦ ω (Fin.cons i₀ i₁)

omit [MeasurableSpace E] in
@[simp] lemma splitHead_apply (ω : (Fin (d + 1) → ZMod (2 * N)) → E) (i₀ : ZMod (2 * N))
    (i₁ : Fin d → ZMod (2 * N)) : splitHead ω i₀ i₁ = ω (Fin.cons i₀ i₁) := rfl

omit [MeasurableSpace E] in
@[simp] lemma splitTail_apply (ω : (Fin (d + 1) → ZMod (2 * N)) → E) (i₁ : Fin d → ZMod (2 * N))
    (i₀ : ZMod (2 * N)) : splitTail ω i₁ i₀ = ω (Fin.cons i₀ i₁) := rfl

lemma measurable_splitHead : Measurable (splitHead (E := E) (N := N) (d := d)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma measurable_splitTail : Measurable (splitTail (E := E) (N := N) (d := d)) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma abs_prod_le_pow_card {ι : Type*} [Fintype ι] {g : ι → ℝ} {C : ℝ} (hg : ∀ i, |g i| ≤ C) :
    |∏ i, g i| ≤ C ^ Fintype.card ι := by
  rw [Finset.abs_prod]
  calc ∏ i, |g i| ≤ ∏ _i : ι, C := Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) fun i _ ↦ hg i
    _ = C ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]

lemma cons_sub (i₀ j₀ : ZMod (2 * N)) (i₁ j₁ : Fin d → ZMod (2 * N)) :
    (Fin.cons i₀ i₁ - Fin.cons j₀ j₁ : Fin (d + 1) → ZMod (2 * N))
      = Fin.cons (i₀ - j₀) (i₁ - j₁) := by
  funext l
  refine Fin.cases ?_ (fun l ↦ ?_) l <;> simp

lemma torusReflAt_cons_succ (k : Fin d) (i₀ : ZMod (2 * N)) (i₁ : Fin d → ZMod (2 * N)) :
    torusReflAt N k.succ (Fin.cons i₀ i₁) = Fin.cons i₀ (torusReflAt N k i₁) := by
  rw [torusReflAt_apply, torusReflAt_apply, Fin.cons_succ, Fin.cons_update]

lemma torusReflAt_cons_zero (i₀ : ZMod (2 * N)) (i₁ : Fin d → ZMod (2 * N)) :
    torusReflAt N 0 (Fin.cons i₀ i₁) = Fin.cons (-1 - i₀) i₁ := by
  rw [torusReflAt_apply, Fin.cons_zero, Fin.update_cons_zero]

/-! #### The shifts, reflections and half-space σ-algebras through the two views -/

lemma splitTail_shift (j₁ : Fin d → ZMod (2 * N)) (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    splitTail ((shift E (Fin.cons 0 j₁)).toFun ω)
      = (shift (ZMod (2 * N) → E) j₁).toFun (splitTail ω) := by
  funext i₁ i₀
  simp [cons_sub]

lemma splitHead_shift (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    splitHead ((shift E (Fin.cons 1 0)).toFun ω)
      = (shift ((Fin d → ZMod (2 * N)) → E) (1 : ZMod (2 * N))).toFun (splitHead ω) := by
  funext i₀ i₁
  simp [cons_sub]

lemma splitTail_genReflectionAt (τ : Fin (d + 1) → E ≃ᵐ E) (k : Fin d)
    (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    splitTail ((genReflectionAt N τ k.succ).toFun ω)
      = (genReflectionAt N (fun k ↦ coordInvolution (ZMod (2 * N)) (τ k.succ)) k).toFun
          (splitTail ω) := by
  funext i₁ i₀
  simp [torusReflAt_cons_succ]

lemma splitHead_genReflectionAt (τ : Fin (d + 1) → E ≃ᵐ E)
    (ω : (Fin (d + 1) → ZMod (2 * N)) → E) :
    splitHead ((genReflectionAt N τ 0).toFun ω)
      = (genReflection N (coordInvolution (Fin d → ZMod (2 * N)) (τ 0))).toFun (splitHead ω) := by
  funext i₀ i₁
  simp [torusReflAt_cons_zero]

lemma measurable_splitTail_cylinderEvents (k : Fin d) :
    Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E) (torusPosAt N k.succ),
      cylinderEvents (X := fun _ : Fin d → ZMod (2 * N) ↦ ZMod (2 * N) → E) (torusPosAt N k)]
      (splitTail (E := E) (N := N) (d := d)) := by
  let : MeasurableSpace ((Fin (d + 1) → ZMod (2 * N)) → E) :=
    cylinderEvents (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E) (torusPosAt N k.succ)
  refine measurable_cylinderEvents_iff.2 fun i₁ hi₁ ↦ measurable_pi_lambda _ fun i₀ ↦ ?_
  exact measurable_cylinderEvent_apply (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E)
    (show Fin.cons i₀ i₁ ∈ torusPosAt N k.succ by simpa using hi₁)

lemma measurable_splitHead_cylinderEvents :
    Measurable[cylinderEvents (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E) (torusPosAt N 0),
      cylinderEvents (X := fun _ : ZMod (2 * N) ↦ (Fin d → ZMod (2 * N)) → E) (torusPos N)]
      (splitHead (E := E) (N := N) (d := d)) := by
  let : MeasurableSpace ((Fin (d + 1) → ZMod (2 * N)) → E) :=
    cylinderEvents (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E) (torusPosAt N 0)
  refine measurable_cylinderEvents_iff.2 fun i₀ hi₀ ↦ measurable_pi_lambda _ fun i₁ ↦ ?_
  exact measurable_cylinderEvent_apply (X := fun _ : Fin (d + 1) → ZMod (2 * N) ↦ E)
    (show Fin.cons i₀ i₁ ∈ torusPosAt N 0 by simpa [torusPos] using hi₀)

/-! #### Transport of the hypotheses of (17.11) to the two views -/

variable {μ : Measure ((Fin (d + 1) → ZMod (2 * N)) → E)} {τ : Fin (d + 1) → E ≃ᵐ E}

lemma measurePreserving_shift_map_splitTail
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ) (j₁ : Fin d → ZMod (2 * N)) :
    MeasurePreserving (shift (ZMod (2 * N) → E) j₁).toFun (μ.map splitTail) (μ.map splitTail) :=
  (hper (Fin.cons 0 j₁)).map_of_comp_eq measurable_splitTail measurable_splitTail
    (Transformation.measurable_toFun _) (funext fun ω ↦ (splitTail_shift j₁ ω).symm)

lemma measurePreserving_shift_map_splitHead
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ) :
    MeasurePreserving (shift ((Fin d → ZMod (2 * N)) → E) (1 : ZMod (2 * N))).toFun
      (μ.map splitHead) (μ.map splitHead) :=
  (hper (Fin.cons 1 0)).map_of_comp_eq measurable_splitHead measurable_splitHead
    (Transformation.measurable_toFun _) (funext fun ω ↦ (splitHead_shift ω).symm)

lemma measurePreserving_genReflectionAt_map_splitTail
    (hrefl : ∀ k, MeasurePreserving (genReflectionAt N τ k).toFun μ μ) (k : Fin d) :
    MeasurePreserving
      (genReflectionAt N (fun k ↦ coordInvolution (ZMod (2 * N)) (τ k.succ)) k).toFun
      (μ.map splitTail) (μ.map splitTail) :=
  (hrefl k.succ).map_of_comp_eq measurable_splitTail measurable_splitTail
    (Transformation.measurable_toFun _) (funext fun ω ↦ (splitTail_genReflectionAt τ k ω).symm)

lemma measurePreserving_genReflection_map_splitHead
    (hrefl : ∀ k, MeasurePreserving (genReflectionAt N τ k).toFun μ μ) :
    MeasurePreserving (genReflection N (coordInvolution (Fin d → ZMod (2 * N)) (τ 0))).toFun
      (μ.map splitHead) (μ.map splitHead) :=
  (hrefl 0).map_of_comp_eq measurable_splitHead measurable_splitHead
    (Transformation.measurable_toFun _) (funext fun ω ↦ (splitHead_genReflectionAt τ ω).symm)

lemma isReflectionPositive_map_splitTail
    (hpos : ∀ k, IsReflectionPositive (torusPosAt N k) (genReflectionAt N τ k) μ) (k : Fin d) :
    IsReflectionPositive (torusPosAt N k)
      (genReflectionAt N (fun k ↦ coordInvolution (ZMod (2 * N)) (τ k.succ)) k)
      (μ.map splitTail) :=
  (hpos k.succ).map measurable_splitTail (measurable_splitTail_cylinderEvents k)
    fun ω ↦ (splitTail_genReflectionAt τ k ω).symm

lemma isReflectionPositive_map_splitHead
    (hpos : IsReflectionPositive (torusPosAt N 0) (genReflectionAt N τ 0) μ) :
    IsReflectionPositive (torusPos N)
      (genReflection N (coordInvolution (Fin d → ZMod (2 * N)) (τ 0))) (μ.map splitHead) :=
  hpos.map measurable_splitHead measurable_splitHead_cylinderEvents
    fun ω ↦ (splitHead_genReflectionAt τ ω).symm

lemma integral_map_splitHead {g : (ZMod (2 * N) → (Fin d → ZMod (2 * N)) → E) → ℝ}
    (hg : Measurable g) : ∫ ω', g ω' ∂(μ.map splitHead) = ∫ ω, g (splitHead ω) ∂μ :=
  integral_map measurable_splitHead.aemeasurable hg.aestronglyMeasurable

lemma integral_map_splitTail {g : ((Fin d → ZMod (2 * N)) → ZMod (2 * N) → E) → ℝ}
    (hg : Measurable g) : ∫ ω', g ω' ∂(μ.map splitTail) = ∫ ω, g (splitTail ω) ∂μ :=
  integral_map measurable_splitTail.aemeasurable hg.aestronglyMeasurable

variable [NeZero N]

/-- A product over the torus, split along the coordinate `0`. -/
lemma prod_cons {M : Type*} [CommMonoid M] (g : (Fin (d + 1) → ZMod (2 * N)) → M) :
    ∏ i, g i = ∏ i₀ : ZMod (2 * N), ∏ i₁ : Fin d → ZMod (2 * N), g (Fin.cons i₀ i₁) := by
  rw [← Fintype.prod_prod_type (fun p ↦ g (Fin.cons p.1 p.2))]
  exact (Fintype.prod_equiv (Fin.consEquiv fun _ ↦ ZMod (2 * N)) _ _ fun _ ↦ rfl).symm

lemma card_pi_zmod : Fintype.card (Fin d → ZMod (2 * N)) = (2 * N) ^ d := by
  simp [ZMod.card]

end Split


/-! ### Georgii, Theorem (17.11): the chessboard estimate in dimension `d`

Georgii's proof is an induction on `d`.  The step views `μ` on `(E^{Λ₀})^{Λ₁}` (`splitTail`),
applies the case `d - 1` with state space `E^{Λ₀}` and the coordinatewise involutions
`coordInvolution _ (τ_k)`, `k ≥ 2`, and then, for each of the resulting factors, views `μ` on
`(E^{Λ₁})^{Λ₀}` (`splitHead`) and applies the one-dimensional case
`abs_integral_prod_pow_le` with state space `E^{Λ₁}`.  The induction is run with absolute values
on both sides, which makes the statement true (and trivial) for `d = 0` as well; for `d ≥ 1` the
right-hand side factors are nonnegative (`integral_prod_tauPow_nonneg`) and the absolute values
disappear, giving Georgii's inequality. -/

section ChessboardPi

universe u

variable {N : ℕ} [NeZero N]

/-- **Georgii, Theorem (17.11), with absolute values on both sides**, proved by induction on the
dimension `d`; see `abs_integral_prod_pow_le_pi` for Georgii's statement. -/
theorem abs_integral_prod_pow_le_pi_abs (d : ℕ) :
    ∀ (E : Type u) [MeasurableSpace E] (μ : Measure ((Fin d → ZMod (2 * N)) → E))
      [IsFiniteMeasure μ] (τ : Fin d → E ≃ᵐ E), (∀ k x, τ k (τ k x) = x) →
      (∀ j, MeasurePreserving (shift E j).toFun μ μ) →
      (∀ k, MeasurePreserving (genReflectionAt N τ k).toFun μ μ) →
      (∀ k, IsReflectionPositive (torusPosAt N k) (genReflectionAt N τ k) μ) →
      ∀ (f : (Fin d → ZMod (2 * N)) → E → ℝ), (∀ i, Measurable (f i)) →
      ∀ C : ℝ, (∀ i x, |f i x| ≤ C) →
      |∫ ω, ∏ i, f i (ω i) ∂μ| ^ ((2 * N) ^ d)
        ≤ ∏ j, |∫ ω, ∏ i, f j (tauPow τ i (ω i)) ∂μ| := by
  induction d with
  | zero =>
      intro E _ μ _ τ hτ hper hrefl hpos f hf C hC
      simp only [pow_zero, pow_one, tauPow_zero, Fintype.prod_unique, le_refl]
  | succ d ih =>
      intro E _ μ _ τ hτ hper hrefl hpos f hf C hC
      -- Step A: the induction hypothesis applied to `μ` viewed on `(E^{Λ₀})^{Λ₁}`.
      set τ₁ : Fin d → (ZMod (2 * N) → E) ≃ᵐ (ZMod (2 * N) → E) :=
        fun k ↦ coordInvolution (ZMod (2 * N)) (τ k.succ) with hτ₁
      set g : (Fin d → ZMod (2 * N)) → (ZMod (2 * N) → E) → ℝ :=
        fun i₁ ζ ↦ ∏ i₀, f (Fin.cons i₀ i₁) (ζ i₀) with hg
      have hgm : ∀ i₁, Measurable (g i₁) := fun i₁ ↦
        Finset.measurable_prod _ fun i₀ _ ↦ (hf _).comp (measurable_pi_apply i₀)
      have hgC : ∀ i₁ ζ, |g i₁ ζ| ≤ C ^ (2 * N) := fun i₁ ζ ↦ by
        have := abs_prod_le_pow_card (g := fun i₀ ↦ f (Fin.cons i₀ i₁) (ζ i₀)) (C := C)
          fun i₀ ↦ hC _ _
        rwa [ZMod.card] at this
      have hτ₁' : ∀ k x, τ₁ k (τ₁ k x) = x := fun k x ↦ funext fun i₀ ↦ by simp [hτ₁, hτ]
      have hA := ih (ZMod (2 * N) → E) (μ.map splitTail) τ₁ hτ₁'
        (measurePreserving_shift_map_splitTail hper)
        (measurePreserving_genReflectionAt_map_splitTail hrefl)
        (isReflectionPositive_map_splitTail hpos) g hgm _ hgC
      set A : (Fin d → ZMod (2 * N)) → ℝ := fun j₁ ↦
        ∫ ω, ∏ i₁, ∏ i₀, f (Fin.cons i₀ j₁)
          (tauPow (fun k ↦ τ k.succ) i₁ (ω (Fin.cons i₀ i₁))) ∂μ with hA_def
      set R : (Fin (d + 1) → ZMod (2 * N)) → ℝ :=
        fun j ↦ ∫ ω, ∏ i, f j (tauPow τ i (ω i)) ∂μ with hR
      have hAL : ∫ ω', ∏ i₁, g i₁ (ω' i₁) ∂(μ.map splitTail) = ∫ ω, ∏ i, f i (ω i) ∂μ := by
        rw [integral_map_splitTail (g := fun ω' ↦ ∏ i₁, g i₁ (ω' i₁))
          (Finset.measurable_prod _ fun i₁ _ ↦ (hgm i₁).comp (measurable_pi_apply i₁))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        simp only [hg, splitTail_apply]
        rw [prod_cons (fun i ↦ f i (ω i)), Finset.prod_comm]
      have hAR : ∀ j₁, ∫ ω', ∏ i₁, g j₁ (tauPow τ₁ i₁ (ω' i₁)) ∂(μ.map splitTail) = A j₁ := by
        intro j₁
        rw [integral_map_splitTail (g := fun ω' ↦ ∏ i₁, g j₁ (tauPow τ₁ i₁ (ω' i₁)))
          (Finset.measurable_prod _ fun i₁ _ ↦
            (hgm j₁).comp ((measurable_tauPow _ _).comp (measurable_pi_apply i₁)))]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        simp only [hg, hτ₁, tauPow_coordInvolution, splitTail_apply]
      rw [hAL] at hA
      simp only [hAR] at hA
      -- Step B: the one-dimensional case applied to `μ` viewed on `(E^{Λ₁})^{Λ₀}`.
      have hB : ∀ j₁, |A j₁| ^ (2 * N) ≤ ∏ j₀, R (Fin.cons j₀ j₁) := by
        intro j₁
        set τ₀ := coordInvolution (Fin d → ZMod (2 * N)) (τ 0) with hτ₀
        set F : ZMod (2 * N) → ((Fin d → ZMod (2 * N)) → E) → ℝ := fun i₀ ζ ↦
          ∏ i₁, f (Fin.cons i₀ j₁) (tauPow (fun k ↦ τ k.succ) i₁ (ζ i₁)) with hF
        have hFm : ∀ i₀, Measurable (F i₀) := fun i₀ ↦ Finset.measurable_prod _ fun i₁ _ ↦
          (hf _).comp ((measurable_tauPow _ _).comp (measurable_pi_apply i₁))
        have hFC : ∀ i₀ ζ, |F i₀ ζ| ≤ C ^ ((2 * N) ^ d) := fun i₀ ζ ↦ by
          have := abs_prod_le_pow_card
            (g := fun i₁ ↦ f (Fin.cons i₀ j₁) (tauPow (fun k ↦ τ k.succ) i₁ (ζ i₁))) (C := C)
            fun i₁ ↦ hC _ _
          rwa [card_pi_zmod] at this
        have hτ₀' : ∀ x, τ₀ (τ₀ x) = x := fun x ↦ funext fun i₁ ↦ by simp [hτ₀, hτ]
        have key := abs_integral_prod_pow_le (μ := μ.map splitHead) (τ := τ₀) hτ₀'
          (measurePreserving_shift_map_splitHead hper)
          (measurePreserving_genReflection_map_splitHead hrefl)
          (isReflectionPositive_map_splitHead (hpos 0)) hFm hFC
        have hBL : ∫ ω', ∏ i₀, F i₀ (ω' i₀) ∂(μ.map splitHead) = A j₁ := by
          rw [integral_map_splitHead (g := fun ω' ↦ ∏ i₀, F i₀ (ω' i₀))
            (Finset.measurable_prod _ fun i₀ _ ↦ (hFm i₀).comp (measurable_pi_apply i₀))]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
          simp only [hF, splitHead_apply]
          exact Finset.prod_comm
        have hBR : ∀ j₀, ∫ ω', ∏ i₀, F j₀ (spinIterate τ₀ i₀ (ω' i₀)) ∂(μ.map splitHead)
            = R (Fin.cons j₀ j₁) := by
          intro j₀
          rw [integral_map_splitHead (g := fun ω' ↦ ∏ i₀, F j₀ (spinIterate τ₀ i₀ (ω' i₀)))
            (Finset.measurable_prod _ fun i₀ _ ↦
              (hFm j₀).comp ((measurable_spinIterate _ _).comp (measurable_pi_apply i₀)))]
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
          simp only [hF, hτ₀, spinIterate_coordInvolution, splitHead_apply, ← tauPow_cons]
          exact (prod_cons fun i ↦ f (Fin.cons j₀ j₁) (tauPow τ i (ω i))).symm
        rw [hBL] at key
        simp only [hBR] at key
        exact key
      -- Assembling the two steps.
      calc |∫ ω, ∏ i, f i (ω i) ∂μ| ^ ((2 * N) ^ (d + 1))
          = (|∫ ω, ∏ i, f i (ω i) ∂μ| ^ ((2 * N) ^ d)) ^ (2 * N) := by rw [pow_succ, pow_mul]
        _ ≤ (∏ j₁, |A j₁|) ^ (2 * N) := pow_le_pow_left₀ (pow_nonneg (abs_nonneg _) _) hA _
        _ = ∏ j₁, |A j₁| ^ (2 * N) := (Finset.prod_pow _ _ _).symm
        _ ≤ ∏ j₁, ∏ j₀, R (Fin.cons j₀ j₁) :=
            Finset.prod_le_prod (fun _ _ ↦ pow_nonneg (abs_nonneg _) _) fun j₁ _ ↦ hB j₁
        _ ≤ ∏ j₁, ∏ j₀, |R (Fin.cons j₀ j₁)| :=
            Finset.prod_le_prod (fun j₁ _ ↦ (pow_nonneg (abs_nonneg _) _).trans (hB j₁))
              fun j₁ _ ↦ (le_abs_self _).trans (le_of_eq (Finset.abs_prod _ _))
        _ = ∏ j, |R j| := by rw [prod_cons (fun j ↦ |R j|), Finset.prod_comm]

variable {E : Type*} [MeasurableSpace E] {d : ℕ}
  {μ : Measure ((Fin (d + 1) → ZMod (2 * N)) → E)} [IsFiniteMeasure μ]
  {τ : Fin (d + 1) → E ≃ᵐ E}

omit [IsFiniteMeasure μ] in
/-- The right-hand side factors of Georgii's (17.11) are nonnegative, by reflection positivity in
the direction `0` alone: `∏_i f_j ∘ τ^i ∘ σ_i` is of the form `h · h∘r̃_1` once `μ` is viewed on
`(E^{Λ₁})^{Λ₀}`. -/
theorem integral_prod_tauPow_nonneg (hτ : ∀ k x, τ k (τ k x) = x)
    (hpos : IsReflectionPositive (torusPosAt N 0) (genReflectionAt N τ 0) μ)
    {f : (Fin (d + 1) → ZMod (2 * N)) → E → ℝ} (hf : ∀ i, Measurable (f i)) {C : ℝ}
    (hC : ∀ i x, |f i x| ≤ C) (j : Fin (d + 1) → ZMod (2 * N)) :
    0 ≤ ∫ ω, ∏ i, f j (tauPow τ i (ω i)) ∂μ := by
  set τ₀ := coordInvolution (Fin d → ZMod (2 * N)) (τ 0) with hτ₀
  set F : ZMod (2 * N) → ((Fin d → ZMod (2 * N)) → E) → ℝ := fun _ ζ ↦
    ∏ i₁, f j (tauPow (fun k ↦ τ k.succ) i₁ (ζ i₁)) with hF
  have hFm : ∀ i₀, Measurable (F i₀) := fun i₀ ↦ Finset.measurable_prod _ fun i₁ _ ↦
    (hf _).comp ((measurable_tauPow _ _).comp (measurable_pi_apply i₁))
  have hFC : ∀ i₀ ζ, |F i₀ ζ| ≤ C ^ ((2 * N) ^ d) := fun i₀ ζ ↦ by
    have := abs_prod_le_pow_card
      (g := fun i₁ ↦ f j (tauPow (fun k ↦ τ k.succ) i₁ (ζ i₁))) (C := C) fun i₁ ↦ hC _ _
    rwa [card_pi_zmod] at this
  have hτ₀' : ∀ x, τ₀ (τ₀ x) = x := fun x ↦ funext fun i₁ ↦ by simp [hτ₀, hτ]
  have h := integral_prod_spinIterate_nonneg (μ := μ.map splitHead) (τ := τ₀) hτ₀'
    (isReflectionPositive_map_splitHead hpos) hFm hFC 0
  rw [integral_map_splitHead (g := fun ω' ↦ ∏ i₀, F 0 (spinIterate τ₀ i₀ (ω' i₀)))
    (Finset.measurable_prod _ fun i₀ _ ↦
      (hFm 0).comp ((measurable_spinIterate _ _).comp (measurable_pi_apply i₀)))] at h
  refine h.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [hF, hτ₀, spinIterate_coordInvolution, splitHead_apply, ← tauPow_cons]
  exact (prod_cons fun i ↦ f j (tauPow τ i (ω i))).symm

/-- **Georgii, Theorem (17.11): the chessboard estimate.**

Let `Λ = Λ(N) = (ℤ/2N)^d` with `d ≥ 1`, and let `μ` be a finite measure on `E^Λ` which is
* `Λ`-periodic (17.3), i.e. invariant under every rotation `θ_j`, `j ∈ Λ`, and
* `r̃_k`-positive (17.7) and `r̃_k`-invariant for every coordinate direction `k`, where `r̃_k`
  is the generalized reflection (17.6) built from a measurable involution `τ_k` of `E`.

Then for every family `(f_i)_{i ∈ Λ}` of bounded measurable functions on `E`,
`|μ(∏_i f_i ∘ σ_i)|^{|Λ|} ≤ ∏_j μ(∏_i f_j ∘ τ^i ∘ σ_i)`, the root-free form of Georgii's
inequality, where `τ^i` is the iterated involution (17.10) `tauPow τ i`.  The factors on the
right are nonnegative (`integral_prod_tauPow_nonneg`), so no absolute value is needed there.
The invariance hypothesis `hrefl` is the one that makes the Cauchy–Schwarz inequality (17.8)
available (`sq_integral_mul_comp_le`). -/
theorem abs_integral_prod_pow_le_pi (hτ : ∀ k x, τ k (τ k x) = x)
    (hper : ∀ j, MeasurePreserving (shift E j).toFun μ μ)
    (hrefl : ∀ k, MeasurePreserving (genReflectionAt N τ k).toFun μ μ)
    (hpos : ∀ k, IsReflectionPositive (torusPosAt N k) (genReflectionAt N τ k) μ)
    {f : (Fin (d + 1) → ZMod (2 * N)) → E → ℝ} (hf : ∀ i, Measurable (f i)) {C : ℝ}
    (hC : ∀ i x, |f i x| ≤ C) :
    |∫ ω, ∏ i, f i (ω i) ∂μ| ^ ((2 * N) ^ (d + 1))
      ≤ ∏ j, ∫ ω, ∏ i, f j (tauPow τ i (ω i)) ∂μ :=
  (abs_integral_prod_pow_le_pi_abs (d + 1) E μ τ hτ hper hrefl hpos f hf C hC).trans
    (le_of_eq (Finset.prod_congr rfl fun j _ ↦
      abs_of_nonneg (integral_prod_tauPow_nonneg hτ (hpos 0) hf hC j)))

end ChessboardPi

end MeasureTheory.GibbsMeasure

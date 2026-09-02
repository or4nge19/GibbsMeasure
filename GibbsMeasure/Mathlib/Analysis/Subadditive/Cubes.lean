/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Order.Monotone

/-!
# Fekete's lemma on `ℤ^d`: subadditive functions of boxes

Let `ι` be a finite type and call a finite subset of `ι → ℤ` a *box* if it is a nonempty
interval `Finset.Icc m n = ∏ₖ [mₖ, nₖ]` of the product order (`Finset.IsBox`). This is Georgii's
system `𝒮_□` of rectangular boxes in `S = ℤ^d` (*Gibbs Measures and Phase Transitions*, §15.2,
before Lemma (15.11)); the *cubes* of §14.1 are the boxes with all sides equal.

A function `a` on finite subsets of `ι → ℤ` is `BoxSubadditive` if it is translation invariant
on boxes and subadditive on pairs of disjoint boxes whose union is a box — Georgii's conditions
(15.11)(i) and (ii). The main results are:

* `BoxSubadditive.Icc_le_nsmul_add_nsmul`, the tiling estimate
  `a(Λ) ≤ N • a(Δ) + (|Λ| - N |Δ|) • a({0})`, where `N = ∏ₖ ⌊Lₖ / pₖ⌋` is the number of disjoint
  translates of the box `Δ` with sides `p` which fit in the box `Λ` with sides `L ≥ p`. It is
  assembled from `Icc_le_prod_nsmul` (a box tiled exactly by translates of `Δ`) and
  `Icc_le_add_card_sub_nsmul` (trimming a box to a sub-box costs `a({0})` per removed site).
* `BoxSubadditive.tendsto_div_card`, **Georgii Lemma (15.11)**: for `a` with values in
  `[-∞, ∞)` (an `EReal`-valued function never equal to `⊤` on boxes) and boxes
  `Λⱼ = Icc (m j) (n j)` all of whose side lengths tend to infinity along a filter,
  `|Λⱼ|⁻¹ a(Λⱼ) → inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ a(Δ)` in `EReal`. Georgii states this for sequences of
  cubes with `|Λₙ| → ∞`; that is `tendsto_div_card_of_tendsto_card`. The proof only uses that
  every fixed box eventually tiles `Λⱼ` up to a boundary layer of relative size `o(1)`, which is
  exactly the hypothesis that all side lengths tend to infinity (a `1 × n` strip, say, cannot
  be tiled by a `2 × 2` square, so `|Λⱼ| → ∞` alone would not do for non-cubes).
* `BoxSubadditive.tendsto_coe_div_card` and `tendsto_div_card_of_bddBelow`, the real-valued
  versions; the latter, with a `BddBelow` hypothesis and a real infimum, has the shape of
  Mathlib's one-dimensional Fekete lemma `Subadditive.tendsto_lim`.

Georgii uses (15.11) for the existence of the specific entropy (Theorem (15.12)) and of the
pressure (Theorem (15.30)).

## Relation to `Subadditive`

`Subadditive.tendsto_lim` is the case `ι = Unit`: a subadditive sequence `u : ℕ → ℝ` yields the
box-subadditive function `Λ ↦ u |Λ|` (`Subadditive.boxSubadditive_card`, valid on every
`ι → ℤ`), and on `Unit → ℤ` the boxes `Icc 0 (n - 1)` have cardinality `n`, so
`tendsto_div_card_of_bddBelow` for these boxes is Fekete's lemma
(`Subadditive.tendsto_lim_of_tendsto_div_card`).
-/

@[expose] public section

open Filter Finset Function Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Finset

/-- Georgii's `𝒮_□`: a finite subset of `ι → ℤ` is a *box* if it is a nonempty interval
`Icc m n = ∏ₖ [mₖ, nₖ]` of the product order. -/
def IsBox (Λ : Finset (ι → ℤ)) : Prop :=
  ∃ m n : ι → ℤ, m ≤ n ∧ Λ = Icc m n

lemma isBox_Icc {m n : ι → ℤ} (h : m ≤ n) : (Icc m n).IsBox := ⟨m, n, h, rfl⟩

lemma isBox_singleton (x : ι → ℤ) : ({x} : Finset (ι → ℤ)).IsBox :=
  ⟨x, x, le_rfl, (Icc_self x).symm⟩

lemma IsBox.nonempty {Λ : Finset (ι → ℤ)} (h : Λ.IsBox) : Λ.Nonempty := by
  obtain ⟨m, n, hmn, rfl⟩ := h
  exact nonempty_Icc.2 hmn

lemma IsBox.card_pos {Λ : Finset (ι → ℤ)} (h : Λ.IsBox) : 0 < #Λ := h.nonempty.card_pos

/-- Translates of boxes are boxes. -/
lemma IsBox.image_add_right {Λ : Finset (ι → ℤ)} (h : Λ.IsBox) (i : ι → ℤ) :
    (Λ.image (· + i)).IsBox := by
  obtain ⟨m, n, hmn, rfl⟩ := h
  rw [image_add_right_Icc]
  exact isBox_Icc (add_le_add hmn le_rfl)

/-- Cutting a box along the coordinate hyperplane `xₖ = t`: `Icc m n` is the union of the two
boxes `{x ∈ Icc m n | xₖ ≤ t}` and `{x ∈ Icc m n | t < xₖ}`. -/
lemma Icc_eq_union_Icc_update (m n : ι → ℤ) (k : ι) {t : ℤ} (hmt : m k ≤ t) (htn : t ≤ n k) :
    Icc m n = Icc m (update n k t) ∪ Icc (update m k (t + 1)) n := by
  ext x
  simp only [mem_union, mem_Icc, Pi.le_def]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_cases hx : x k ≤ t
    · refine Or.inl ⟨h₁, fun i ↦ ?_⟩
      by_cases hi : i = k
      · subst hi; simpa
      · rw [update_of_ne hi]; exact h₂ i
    · refine Or.inr ⟨fun i ↦ ?_, h₂⟩
      by_cases hi : i = k
      · subst hi; simp; omega
      · rw [update_of_ne hi]; exact h₁ i
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · refine ⟨h₁, fun i ↦ (h₂ i).trans ?_⟩
      by_cases hi : i = k
      · subst hi; simpa
      · rw [update_of_ne hi]
    · refine ⟨fun i ↦ le_trans ?_ (h₁ i), h₂⟩
      by_cases hi : i = k
      · subst hi; simp; omega
      · rw [update_of_ne hi]

/-- The two halves of a box cut along a coordinate hyperplane are disjoint. -/
lemma disjoint_Icc_update (m n : ι → ℤ) (k : ι) (t : ℤ) :
    Disjoint (Icc m (update n k t)) (Icc (update m k (t + 1)) n) := by
  rw [disjoint_left]
  intro x hx hx'
  rw [mem_Icc] at hx hx'
  have h₁ : x k ≤ update n k t k := hx.2 k
  have h₂ : update m k (t + 1) k ≤ x k := hx'.1 k
  simp only [update_self] at h₁ h₂
  omega

end Finset

variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]

/-- Georgii (15.11)(i)–(ii): a function `a` on finite subsets of `ι → ℤ` is *box-subadditive*
if it is invariant under translations of boxes, `a(Λ + i) = a(Λ)`, and subadditive on disjoint
boxes whose union is a box, `a(Λ ∪ Δ) ≤ a(Λ) + a(Δ)`. Values of `a` outside the boxes are
irrelevant. -/
structure BoxSubadditive (a : Finset (ι → ℤ) → β) : Prop where
  /-- Translation invariance on boxes, Georgii (15.11)(i). -/
  image_add_right : ∀ Λ : Finset (ι → ℤ), Λ.IsBox → ∀ i : ι → ℤ, a (Λ.image (· + i)) = a Λ
  /-- Subadditivity on disjoint boxes whose union is a box, Georgii (15.11)(ii). -/
  union_le : ∀ Λ Δ : Finset (ι → ℤ), Λ.IsBox → Δ.IsBox → Disjoint Λ Δ → (Λ ∪ Δ).IsBox →
    a (Λ ∪ Δ) ≤ a Λ + a Δ

namespace BoxSubadditive

variable {a : Finset (ι → ℤ) → β} (ha : BoxSubadditive a)
include ha

omit [IsOrderedAddMonoid β] in
/-- Subadditivity along a coordinate cut of a box. -/
lemma Icc_le_add_update {m n : ι → ℤ} (hmn : m ≤ n) {k : ι} {t : ℤ} (hmt : m k ≤ t)
    (htn : t < n k) :
    a (Icc m n) ≤ a (Icc m (update n k t)) + a (Icc (update m k (t + 1)) n) := by
  have h₁ : m ≤ update n k t := fun i ↦ by
    by_cases hi : i = k
    · subst hi; simpa
    · rw [update_of_ne hi]; exact hmn i
  have h₂ : update m k (t + 1) ≤ n := fun i ↦ by
    by_cases hi : i = k
    · subst hi; simp; omega
    · rw [update_of_ne hi]; exact hmn i
  have := ha.union_le _ _ (isBox_Icc h₁) (isBox_Icc h₂) (disjoint_Icc_update m n k t)
    (by rw [← Icc_eq_union_Icc_update m n k hmt htn.le]; exact isBox_Icc hmn)
  rwa [← Icc_eq_union_Icc_update m n k hmt htn.le] at this

/-- A box exactly tiled by `∏ₖ qₖ` translates of the box `Δ = ∏ₖ [0, pₖ)` satisfies
`a(Λ) ≤ (∏ₖ qₖ) • a(Δ)`: Georgii's "applying (ii) successively (in the right order) and
using (i)". -/
lemma Icc_le_prod_nsmul (m : ι → ℤ) {p q : ι → ℕ} (hp : ∀ k, 0 < p k) (hq : ∀ k, 0 < q k) :
    a (Icc m fun k ↦ m k + q k * p k - 1) ≤ (∏ k, q k) • a (Icc 0 fun k ↦ (p k : ℤ) - 1) := by
  suffices H : ∀ s : ℕ, ∀ (m : ι → ℤ) (q : ι → ℕ), (∀ k, 0 < q k) → ∑ k, q k = s →
      a (Icc m fun k ↦ m k + q k * p k - 1) ≤ (∏ k, q k) • a (Icc 0 fun k ↦ (p k : ℤ) - 1) from
    H _ m q hq rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro m q hq hs
  by_cases hq1 : ∀ k, q k = 1
  · -- a single tile: a translate of `Δ`
    have hΔ : Icc m (fun k ↦ m k + q k * p k - 1)
        = (Icc 0 fun k ↦ (p k : ℤ) - 1).image (· + m) := by
      rw [image_add_right_Icc, zero_add]
      congr 1
      ext k
      simp [hq1 k]
      ring
    rw [hΔ, ha.image_add_right _ (isBox_Icc fun k ↦ by have := hp k; simp; omega) m,
      prod_eq_one fun k _ ↦ hq1 k, one_nsmul]
  · -- some coordinate has at least two tiles: cut off one layer of tiles there
    obtain ⟨k, hk⟩ := not_forall.1 hq1
    have hk2 : 2 ≤ q k := by have := hq k; omega
    set n : ι → ℤ := fun k ↦ m k + q k * p k - 1 with hn
    have hqp : ∀ i, (1 : ℤ) ≤ q i * p i := fun i ↦ by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (hq i).ne' (hp i).ne')
    have hmn : m ≤ n := fun i ↦ by simp only [hn]; linarith [hqp i]
    have hmt : m k ≤ m k + p k - 1 := by have := hp k; omega
    have htn : m k + p k - 1 < n k := by
      simp only [hn]
      have h2 : (2 : ℤ) ≤ q k := by exact_mod_cast hk2
      have hpk : (0 : ℤ) < p k := by exact_mod_cast hp k
      nlinarith
    refine (ha.Icc_le_add_update hmn hmt htn).trans ?_
    have hL : Icc m (update n k (m k + p k - 1)) =
        Icc m fun i ↦ m i + (update q k 1 i) * p i - 1 := by
      congr 1
      ext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hn, update_of_ne hi]
    have hR : Icc (update m k (m k + p k - 1 + 1)) n = Icc (update m k (m k + p k))
        fun i ↦ (update m k (m k + p k)) i + (update q k (q k - 1) i) * p i - 1 := by
      rw [sub_add_cancel]
      congr 1
      ext i
      by_cases hi : i = k
      · subst hi
        simp only [hn, update_self, Nat.cast_pred (hq _)]
        ring
      · simp [hn, update_of_ne hi]
    rw [hL, hR]
    have hsum1 : ∑ i, update q k 1 i < s := by
      rw [sum_update_of_mem (mem_univ k), ← hs, ← add_sum_erase univ q (mem_univ k),
        sdiff_singleton_eq_erase]
      omega
    have hsum2 : ∑ i, update q k (q k - 1) i < s := by
      rw [sum_update_of_mem (mem_univ k), ← hs, ← add_sum_erase univ q (mem_univ k),
        sdiff_singleton_eq_erase]
      omega
    have h1 := ih _ hsum1 m (update q k 1) (fun i ↦ by
      by_cases hi : i = k
      · subst hi; simp
      · simp [update_of_ne hi, hq i]) rfl
    have h2 := ih _ hsum2 (update m k (m k + p k)) (update q k (q k - 1)) (fun i ↦ by
      by_cases hi : i = k
      · subst hi; simp; omega
      · simp [update_of_ne hi, hq i]) rfl
    refine (add_le_add h1 h2).trans_eq ?_
    rw [← add_nsmul, prod_update_of_mem (mem_univ k), prod_update_of_mem (mem_univ k), ← add_mul,
      Nat.add_sub_cancel' (hq k), sdiff_singleton_eq_erase, mul_prod_erase univ q (mem_univ k)]

/-- Every box `Λ` satisfies `a(Λ) ≤ |Λ| • a({0})`: tile it by singletons. -/
lemma Icc_le_card_nsmul {m n : ι → ℤ} (hmn : m ≤ n) : a (Icc m n) ≤ #(Icc m n) • a {0} := by
  have hq : ∀ k, 0 < (n k + 1 - m k).toNat := fun k ↦ by
    have hk : m k ≤ n k := hmn k
    omega
  have key := ha.Icc_le_prod_nsmul m (p := fun _ ↦ 1) (q := fun k ↦ (n k + 1 - m k).toNat)
    (fun _ ↦ one_pos) hq
  have e₁ : Icc m n
      = Icc m fun k ↦ m k + (((n k + 1 - m k).toNat : ℕ) : ℤ) * ((1 : ℕ) : ℤ) - 1 := by
    congr 1
    ext k
    have hk : m k ≤ n k := hmn k
    simp
    omega
  have e₂ : #(Icc m n) = ∏ k, (n k + 1 - m k).toNat := by
    simp only [Pi.card_Icc, Int.card_Icc]
  have e₃ : ({0} : Finset (ι → ℤ)) = Icc 0 fun _ ↦ ((1 : ℕ) : ℤ) - 1 := by
    rw [show (fun _ : ι ↦ ((1 : ℕ) : ℤ) - 1) = 0 from funext fun _ ↦ by simp, Icc_self]
  rw [e₂, e₁, e₃]
  exact key

lemma le_card_nsmul {Λ : Finset (ι → ℤ)} (hΛ : Λ.IsBox) : a Λ ≤ #Λ • a {0} := by
  obtain ⟨m, n, hmn, rfl⟩ := hΛ
  exact ha.Icc_le_card_nsmul hmn

omit ha in
private lemma le_add_card_sub_nsmul_trans {x y z w : β} {A B C : ℕ} (hBA : B ≤ A) (hCB : C ≤ B)
    (h₁ : x ≤ y + (A - B) • w) (h₂ : y ≤ z + (B - C) • w) : x ≤ z + (A - C) • w :=
  calc x ≤ y + (A - B) • w := h₁
    _ ≤ z + (B - C) • w + (A - B) • w := add_le_add h₂ le_rfl
    _ = z + (A - C) • w := by
      rw [add_assoc, ← add_nsmul, add_comm (B - C), Nat.sub_add_sub_cancel hBA hCB]

/-- Trimming the top of a box in one coordinate costs `a({0})` per removed site. -/
lemma Icc_le_add_card_sub_nsmul_update_right {m n : ι → ℤ} (hmn : m ≤ n) (k : ι) {t : ℤ}
    (hmt : m k ≤ t) (htn : t ≤ n k) :
    a (Icc m n) ≤ a (Icc m (update n k t)) + (#(Icc m n) - #(Icc m (update n k t))) • a {0} := by
  rcases htn.lt_or_eq with htn | rfl
  · have hcard : #(Icc m n) = #(Icc m (update n k t)) + #(Icc (update m k (t + 1)) n) := by
      rw [Icc_eq_union_Icc_update m n k hmt htn.le,
        card_union_of_disjoint (disjoint_Icc_update m n k t)]
    have hle : update m k (t + 1) ≤ n := fun i ↦ by
      by_cases hi : i = k
      · subst hi; simp; omega
      · rw [update_of_ne hi]; exact hmn i
    have hslab := ha.Icc_le_card_nsmul hle
    calc a (Icc m n) ≤ a (Icc m (update n k t)) + a (Icc (update m k (t + 1)) n) :=
          ha.Icc_le_add_update hmn hmt htn
      _ ≤ _ := by rw [hcard, Nat.add_sub_cancel_left]; exact add_le_add le_rfl hslab
  · rw [update_eq_self, Nat.sub_self, zero_nsmul, add_zero]

/-- Trimming the bottom of a box in one coordinate costs `a({0})` per removed site. -/
lemma Icc_le_add_card_sub_nsmul_update_left {m n : ι → ℤ} (hmn : m ≤ n) (k : ι) {s : ℤ}
    (hms : m k ≤ s) (hsn : s ≤ n k) :
    a (Icc m n) ≤ a (Icc (update m k s) n) + (#(Icc m n) - #(Icc (update m k s) n)) • a {0} := by
  rcases hms.lt_or_eq with hms | rfl
  · have hsplit := Icc_eq_union_Icc_update m n k (t := s - 1) (by omega) (by omega)
    rw [sub_add_cancel] at hsplit
    have hcard : #(Icc m n) = #(Icc m (update n k (s - 1))) + #(Icc (update m k s) n) := by
      have := disjoint_Icc_update m n k (s - 1)
      rw [sub_add_cancel] at this
      rw [hsplit, card_union_of_disjoint this]
    have hle : m ≤ update n k (s - 1) := fun i ↦ by
      by_cases hi : i = k
      · subst hi; simp; omega
      · rw [update_of_ne hi]; exact hmn i
    have hslab := ha.Icc_le_card_nsmul hle
    have hcut := ha.Icc_le_add_update hmn (k := k) (t := s - 1) (by omega) (by omega)
    rw [sub_add_cancel] at hcut
    calc a (Icc m n) ≤ a (Icc m (update n k (s - 1))) + a (Icc (update m k s) n) := hcut
      _ ≤ _ := by
        rw [hcard, Nat.add_sub_cancel, add_comm]
        exact add_le_add le_rfl hslab
  · rw [update_eq_self, Nat.sub_self, zero_nsmul, add_zero]

/-- Trimming a box `Λ = Icc m n` to a sub-box `Δ = Icc m' n'` costs `a({0})` per removed site:
`a(Λ) ≤ a(Δ) + (|Λ| - |Δ|) • a({0})`. -/
lemma Icc_le_add_card_sub_nsmul {m m' n' n : ι → ℤ} (hmm' : m ≤ m') (hm'n' : m' ≤ n')
    (hn'n : n' ≤ n) :
    a (Icc m n) ≤ a (Icc m' n') + (#(Icc m n) - #(Icc m' n')) • a {0} := by
  have hmn : m ≤ n := hmm'.trans (hm'n'.trans hn'n)
  -- trim one coordinate at a time
  have key : ∀ s : Finset ι, a (Icc m n) ≤
      a (Icc (fun i ↦ if i ∈ s then m' i else m i) fun i ↦ if i ∈ s then n' i else n i) +
        (#(Icc m n) -
          #(Icc (fun i ↦ if i ∈ s then m' i else m i) fun i ↦ if i ∈ s then n' i else n i)) •
          a {0} := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s hk ih =>
      set ms : ι → ℤ := fun i ↦ if i ∈ s then m' i else m i with hms
      set ns : ι → ℤ := fun i ↦ if i ∈ s then n' i else n i with hns
      have hms_le : m ≤ ms := fun i ↦ by
        simp only [hms]; split_ifs; exacts [hmm' i, le_rfl]
      have hns_le : ns ≤ n := fun i ↦ by
        simp only [hns]; split_ifs; exacts [hn'n i, le_rfl]
      have hmsns : ms ≤ ns := fun i ↦ by
        simp only [hms, hns]; split_ifs; exacts [hm'n' i, hmn i]
      have hms_k : ms k = m k := by simp [hms, hk]
      have hns_k : ns k = n k := by simp [hns, hk]
      have e₁ : (fun i ↦ if i ∈ insert k s then m' i else m i) = update ms k (m' k) := by
        ext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hms, hi]
      have e₂ : (fun i ↦ if i ∈ insert k s then n' i else n i) = update ns k (n' k) := by
        ext i
        by_cases hi : i = k
        · subst hi; simp
        · simp [hns, hi]
      rw [e₁, e₂]
      have hup : update ns k (n' k) ≤ ns := fun i ↦ by
        by_cases hi : i = k
        · subst hi; simp only [update_self, hns_k]; exact hn'n _
        · rw [update_of_ne hi]
      have hlow : ms ≤ update ms k (m' k) := fun i ↦ by
        by_cases hi : i = k
        · subst hi; simp only [update_self, hms_k]; exact hmm' _
        · rw [update_of_ne hi]
      have hmsup : ms ≤ update ns k (n' k) := fun i ↦ by
        by_cases hi : i = k
        · subst hi; simp only [update_self, hms_k]; exact (hmm' _).trans (hm'n' _)
        · rw [update_of_ne hi]; exact hmsns i
      have t₁ := ha.Icc_le_add_card_sub_nsmul_update_right hmsns k (t := n' k)
        (by rw [hms_k]; exact (hmm' k).trans (hm'n' k)) (by rw [hns_k]; exact hn'n k)
      have t₂ := ha.Icc_le_add_card_sub_nsmul_update_left hmsup k (s := m' k)
        (by rw [hms_k]; exact hmm' k) (by simp only [update_self]; exact hm'n' k)
      refine le_add_card_sub_nsmul_trans (card_le_card (Icc_subset_Icc hms_le hns_le))
        (card_le_card (Icc_subset_Icc hlow hup)) ih ?_
      exact le_add_card_sub_nsmul_trans (card_le_card (Icc_subset_Icc le_rfl hup))
        (card_le_card (Icc_subset_Icc hlow le_rfl)) t₁ t₂
  simpa using key univ

/-- **The tiling estimate behind Georgii (15.11).** Let `Δ = ∏ₖ [0, pₖ)` be a box with sides
`p`, and `Λ = Icc m n` a box with sides `Lₖ = nₖ + 1 - mₖ ≥ pₖ`. Then `Λ` contains
`N = ∏ₖ ⌊Lₖ / pₖ⌋` disjoint translates of `Δ`, and the remaining `|Λ| - N |Δ|` sites form a
boundary layer covered by singletons, whence
`a(Λ) ≤ N • a(Δ) + (|Λ| - N |Δ|) • a({0})`. -/
lemma Icc_le_nsmul_add_nsmul {m n : ι → ℤ} {p : ι → ℕ} (hp : ∀ k, 0 < p k)
    (hpL : ∀ k, (p k : ℤ) ≤ n k + 1 - m k) :
    a (Icc m n) ≤ (∏ k, (n k + 1 - m k).toNat / p k) • a (Icc 0 fun k ↦ (p k : ℤ) - 1) +
      (#(Icc m n) - (∏ k, (n k + 1 - m k).toNat / p k) * ∏ k, p k) • a {0} := by
  set q : ι → ℕ := fun k ↦ (n k + 1 - m k).toNat / p k with hq
  have hq0 : ∀ k, 0 < q k := fun k ↦ Nat.div_pos (by have := hpL k; omega) (hp k)
  have hqp : ∀ k, q k * p k ≤ (n k + 1 - m k).toNat := fun k ↦ Nat.div_mul_le_self _ _
  set n' : ι → ℤ := fun k ↦ m k + ((q k * p k : ℕ) : ℤ) - 1 with hn'
  have hmn' : m ≤ n' := fun k ↦ by
    have : 1 ≤ q k * p k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (hq0 k).ne' (hp k).ne')
    simp only [hn']
    omega
  have hn'n : n' ≤ n := fun k ↦ by
    have := hqp k
    have := hpL k
    simp only [hn']
    omega
  have hcore : #(Icc m n') = (∏ k, q k) * ∏ k, p k := by
    rw [Pi.card_Icc, ← prod_mul_distrib]
    refine prod_congr rfl fun k _ ↦ ?_
    rw [Int.card_Icc]
    simp only [hn']
    have : m k + ((q k * p k : ℕ) : ℤ) - 1 + 1 - m k = ((q k * p k : ℕ) : ℤ) := by ring
    rw [this, Int.toNat_natCast]
  have hIcc : Icc m n' = Icc m fun k ↦ m k + q k * p k - 1 := by
    simp only [hn', Nat.cast_mul]
  calc a (Icc m n) ≤ a (Icc m n') + (#(Icc m n) - #(Icc m n')) • a {0} :=
        ha.Icc_le_add_card_sub_nsmul le_rfl hmn' hn'n
    _ ≤ _ := by
        rw [hcore, hIcc]
        exact add_le_add (ha.Icc_le_prod_nsmul m hp hq0) le_rfl

end BoxSubadditive

omit [Fintype ι] [DecidableEq ι] in
/-- If all side lengths of the boxes `Icc (m j) (n j)` tend to infinity, then eventually
`m j ≤ n j`. -/
private lemma eventually_le_of_tendsto_sub [Finite ι] {κ : Type*} {l : Filter κ} {m n : κ → ι → ℤ}
    (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) : ∀ᶠ j in l, m j ≤ n j :=
  eventually_all.2 fun k ↦ ((h k).eventually_ge_atTop 0).mono fun _ hj ↦ by
    simpa [sub_nonneg] using hj

namespace BoxSubadditive

/-- **Georgii Lemma (15.11), real-valued case.** Let `a` be a real-valued box-subadditive
function on `ι → ℤ` and `Λⱼ = Icc (m j) (n j)` boxes all of whose side lengths tend to infinity
along the filter `l`. Then `|Λⱼ|⁻¹ a(Λⱼ) → inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ a(Δ)`, the infimum and the limit
being taken in `EReal` (the infimum may be `-∞`). -/
theorem tendsto_coe_div_card {a : Finset (ι → ℤ) → ℝ} (ha : BoxSubadditive a) {κ : Type*}
    {l : Filter κ} {m n : κ → ι → ℤ} (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ ((a (Icc (m j) (n j)) / #(Icc (m j) (n j)) : ℝ) : EReal)) l
      (𝓝 (⨅ Δ, ⨅ (_ : Δ.IsBox), ((a Δ / #Δ : ℝ) : EReal))) := by
  have hbox := eventually_le_of_tendsto_sub h
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun c hc ↦ ?_⟩
  · filter_upwards [hbox] with j hj
    exact hb.trans_le (iInf₂_le _ (isBox_Icc hj))
  rcases eq_or_ne c ⊤ with rfl | hc'
  · exact Eventually.of_forall fun j ↦ EReal.coe_lt_top _
  lift c to ℝ using ⟨hc', (bot_le.trans_lt hc).ne'⟩
  -- a box `Δ` with `|Δ|⁻¹ a(Δ) < c`
  obtain ⟨Δ, ⟨m₀, n₀, hmn₀, rfl⟩, hΔc⟩ : ∃ Δ : Finset (ι → ℤ), Δ.IsBox ∧ a Δ / #Δ < c := by
    simpa only [iInf_lt_iff, EReal.coe_lt_coe_iff, exists_prop] using hc
  set p : ι → ℕ := fun k ↦ (n₀ k + 1 - m₀ k).toNat with hp
  have hp0 : ∀ k, 0 < p k := fun k ↦ by
    have hk : m₀ k ≤ n₀ k := hmn₀ k
    simp only [hp]
    omega
  set Δ₀ : Finset (ι → ℤ) := Icc 0 fun k ↦ (p k : ℤ) - 1 with hΔ₀
  have hΔ₀box : Δ₀.IsBox := isBox_Icc fun k ↦ by
    have := hp0 k
    simp only [Pi.zero_apply]
    omega
  have haΔ : a (Icc m₀ n₀) = a Δ₀ := by
    have : Icc m₀ n₀ = Δ₀.image (· + m₀) := by
      rw [hΔ₀, image_add_right_Icc, zero_add]
      congr 1
      ext k
      have hk : m₀ k ≤ n₀ k := hmn₀ k
      simp only [hp, Pi.add_apply]
      omega
    rw [this, ha.image_add_right _ hΔ₀box m₀]
  have hcardΔ : #(Icc m₀ n₀) = ∏ k, p k := by
    simp only [Pi.card_Icc, Int.card_Icc, hp]
  set P : ℕ := ∏ k, p k with hP
  have hP0 : 0 < P := prod_pos fun k _ ↦ hp0 k
  -- eventually every side of `Λⱼ` is at least the corresponding side of `Δ`
  have hE : ∀ᶠ j in l, ∀ k, (p k : ℤ) ≤ n j k + 1 - m j k :=
    eventually_all.2 fun k ↦ ((h k).eventually_ge_atTop (p k)).mono fun j hj ↦ by omega
  set L : κ → ι → ℕ := fun j k ↦ (n j k + 1 - m j k).toNat with hL
  set Q : κ → ℕ := fun j ↦ ∏ k, L j k / p k with hQ
  have hcard : ∀ j, #(Icc (m j) (n j)) = ∏ k, L j k := fun j ↦ by
    simp only [Pi.card_Icc, Int.card_Icc, hL]
  -- the fraction of `Λⱼ` covered by the `Q j` tiles tends to `1`
  set ρ : κ → ℝ := fun j ↦ (Q j * P : ℝ) / #(Icc (m j) (n j)) with hρ
  have hρ_eq : ∀ j, ρ j = ∏ k, ((L j k / p k * p k : ℕ) : ℝ) / (L j k : ℝ) := by
    intro j
    simp only [hρ, hQ, hP, hcard]
    push_cast
    rw [← prod_mul_distrib, ← prod_div_distrib]
  have hfac : ∀ k, Tendsto (fun j ↦ ((L j k / p k * p k : ℕ) : ℝ) / (L j k : ℝ)) l (𝓝 1) := by
    intro k
    have hLk : Tendsto (fun j ↦ (L j k : ℝ)) l atTop := by
      have : Tendsto (fun j ↦ ((n j k + 1 - m j k : ℤ) : ℝ)) l atTop := by
        exact tendsto_intCast_atTop_atTop.comp ((h k).atTop_add (tendsto_const_nhds (x := 1))
          |>.congr fun j ↦ (by ring : n j k - m j k + 1 = n j k + 1 - m j k))
      refine this.congr' (((h k).eventually_ge_atTop 0).mono fun j hj ↦ ?_)
      simp only [hL]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    have hlow : Tendsto (fun j ↦ 1 - (p k : ℝ) / L j k) l (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hLk)
    have hLpos : ∀ᶠ j in l, (0 : ℝ) < L j k :=
      hE.mono fun j hj ↦ by
        have := hj k
        have := hp0 k
        simp only [hL]
        exact_mod_cast (by omega : 0 < (n j k + 1 - m j k).toNat)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hLpos] with j hj
      have h1 : (L j k : ℝ) - p k ≤ ((L j k / p k * p k : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := L j k) (hp0 k)
        have : (L j k : ℝ) < ((L j k / p k * p k : ℕ) : ℝ) + p k := by exact_mod_cast this
        linarith
      rw [show 1 - (p k : ℝ) / L j k = ((L j k : ℝ) - p k) / L j k by field_simp]
      exact div_le_div_of_nonneg_right h1 hj.le
    · filter_upwards [hLpos] with j hj
      rw [div_le_one hj]
      exact_mod_cast Nat.div_mul_le_self _ _
  have hρ_lim : Tendsto ρ l (𝓝 1) := by
    have key : Tendsto (fun j ↦ ∏ k, ((L j k / p k * p k : ℕ) : ℝ) / (L j k : ℝ)) l
        (𝓝 (∏ _k : ι, (1 : ℝ))) := tendsto_finsetProd _ fun k _ ↦ hfac k
    rwa [prod_const_one, ← funext hρ_eq] at key
  -- the tiling estimate, divided by `|Λⱼ|`
  have hineq : ∀ᶠ j in l, a (Icc (m j) (n j)) / #(Icc (m j) (n j)) ≤
      ρ j * (a (Icc m₀ n₀) / #(Icc m₀ n₀)) + (1 - ρ j) * a {0} := by
    filter_upwards [hE, hbox] with j hj hjbox
    have key := ha.Icc_le_nsmul_add_nsmul hp0 hj
    have hQP : Q j * P ≤ #(Icc (m j) (n j)) := by
      rw [hcard, hQ, hP, ← prod_mul_distrib]
      exact prod_le_prod' fun k _ ↦ Nat.div_mul_le_self _ _
    have hC : (0 : ℝ) < #(Icc (m j) (n j)) := by exact_mod_cast (isBox_Icc hjbox).card_pos
    rw [haΔ, hcardΔ, div_le_iff₀ hC]
    have hC' : (#(Icc (m j) (n j)) : ℝ) ≠ 0 := hC.ne'
    have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast hP0.ne'
    have hrhs : (ρ j * (a Δ₀ / P) + (1 - ρ j) * a {0}) * #(Icc (m j) (n j)) =
        Q j * a Δ₀ + ((#(Icc (m j) (n j)) : ℝ) - Q j * P) * a {0} := by
      simp only [hρ]
      field_simp
    rw [hrhs]
    have key' : a (Icc (m j) (n j)) ≤
        (Q j : ℝ) * a Δ₀ + ((#(Icc (m j) (n j)) - Q j * P : ℕ) : ℝ) * a {0} := by
      simpa only [nsmul_eq_mul, hQ, hP, hL, hΔ₀] using key
    rwa [Nat.cast_sub hQP, Nat.cast_mul] at key'
  have hlim : Tendsto (fun j ↦ ρ j * (a (Icc m₀ n₀) / #(Icc m₀ n₀)) + (1 - ρ j) * a {0}) l
      (𝓝 (a (Icc m₀ n₀) / #(Icc m₀ n₀))) := by
    have := (hρ_lim.mul (tendsto_const_nhds (x := a (Icc m₀ n₀) / #(Icc m₀ n₀)))).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hρ_lim).mul (tendsto_const_nhds (x := a {0})))
    simpa using this
  filter_upwards [hineq, hlim.eventually (gt_mem_nhds hΔc)] with j h₁ h₂
  exact EReal.coe_lt_coe_iff.2 (h₁.trans_lt h₂)

omit [Fintype ι] [DecidableEq ι] in
private lemma _root_.EReal.nsmul_bot_of_ne_zero {N : ℕ} (hN : N ≠ 0) : N • (⊥ : EReal) = ⊥ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  rw [succ_nsmul, EReal.add_bot]

/-- **Georgii Lemma (15.11).** Let `a : 𝒮_□ → [-∞, ∞)` be translation invariant and
subadditive on disjoint boxes with box union (`BoxSubadditive`, with `a Λ ≠ ⊤` on boxes), and let
`Λⱼ = Icc (m j) (n j)` be boxes all of whose side lengths tend to infinity along the filter `l`
(for a sequence of cubes this is `|Λⱼ| → ∞`, see `tendsto_div_card_of_tendsto_card`). Then
`lim_j |Λⱼ|⁻¹ a(Λⱼ) = inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ a(Δ)` in `[-∞, ∞)`.

This is the `d`-dimensional Fekete lemma; Mathlib's `Subadditive.tendsto_lim` is the case
`ι = Unit` (see `Subadditive.tendsto_lim_of_tendsto_div_card`). -/
theorem tendsto_div_card {a : Finset (ι → ℤ) → EReal} (ha : BoxSubadditive a)
    (ha' : ∀ Λ : Finset (ι → ℤ), Λ.IsBox → a Λ ≠ ⊤) {κ : Type*} {l : Filter κ}
    {m n : κ → ι → ℤ} (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ a (Icc (m j) (n j)) / (#(Icc (m j) (n j)) : EReal)) l
      (𝓝 (⨅ Δ, ⨅ (_ : Δ.IsBox), a Δ / (#Δ : EReal))) := by
  have hbox := eventually_le_of_tendsto_sub h
  by_cases hbot : ∃ Δ : Finset (ι → ℤ), Δ.IsBox ∧ a Δ = ⊥
  · -- `a` takes the value `-∞` on some box: then `a(Λⱼ) = -∞` as soon as `Λⱼ` contains a
    -- translate of that box, and the infimum is `-∞`
    obtain ⟨Δ, ⟨m₀, n₀, hmn₀, rfl⟩, hΔ⟩ := hbot
    have hα : (⨅ Δ : Finset (ι → ℤ), ⨅ (_ : Δ.IsBox), a Δ / (#Δ : EReal)) = ⊥ := by
      refine le_bot_iff.1 ((iInf₂_le _ (isBox_Icc hmn₀)).trans ?_)
      rw [hΔ, EReal.bot_div_of_pos_ne_top (by exact_mod_cast (nonempty_Icc.2 hmn₀).card_pos)
        (EReal.natCast_ne_top _)]
    rw [hα]
    set p : ι → ℕ := fun k ↦ (n₀ k + 1 - m₀ k).toNat with hp
    have hp0 : ∀ k, 0 < p k := fun k ↦ by
      have hk : m₀ k ≤ n₀ k := hmn₀ k
      simp only [hp]
      omega
    have hΔ₀box : (Icc 0 fun k ↦ (p k : ℤ) - 1).IsBox := isBox_Icc fun k ↦ by
      have := hp0 k
      simp only [Pi.zero_apply]
      omega
    have haΔ : a (Icc 0 fun k ↦ (p k : ℤ) - 1) = ⊥ := by
      rw [← hΔ]
      have : Icc m₀ n₀ = (Icc 0 fun k ↦ (p k : ℤ) - 1).image (· + m₀) := by
        rw [image_add_right_Icc, zero_add]
        congr 1
        ext k
        have hk : m₀ k ≤ n₀ k := hmn₀ k
        simp only [hp, Pi.add_apply]
        omega
      rw [this, ha.image_add_right _ hΔ₀box m₀]
    have hE : ∀ᶠ j in l, ∀ k, (p k : ℤ) ≤ n j k + 1 - m j k :=
      eventually_all.2 fun k ↦ ((h k).eventually_ge_atTop (p k)).mono fun j hj ↦ by omega
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hE, hbox] with j hj hjbox
    have key := ha.Icc_le_nsmul_add_nsmul hp0 hj
    have hQ : ∏ k, (n j k + 1 - m j k).toNat / p k ≠ 0 :=
      (prod_pos fun k _ ↦ Nat.div_pos (by have := hj k; omega) (hp0 k)).ne'
    rw [haΔ, EReal.nsmul_bot_of_ne_zero hQ, EReal.bot_add, le_bot_iff] at key
    rw [key, EReal.bot_div_of_pos_ne_top (by exact_mod_cast (nonempty_Icc.2 hjbox).card_pos)
      (EReal.natCast_ne_top _)]
  · -- `a` is real-valued on boxes: transport `tendsto_coe_div_card`
    have hbot' : ∀ Λ : Finset (ι → ℤ), Λ.IsBox → a Λ ≠ ⊥ := fun Λ hΛ hb ↦ hbot ⟨Λ, hΛ, hb⟩
    have hcoe : ∀ Λ : Finset (ι → ℤ), Λ.IsBox → (((a Λ).toReal : ℝ) : EReal) = a Λ :=
      fun Λ hΛ ↦ EReal.coe_toReal (ha' Λ hΛ) (hbot' Λ hΛ)
    have ha'' : BoxSubadditive fun Λ ↦ (a Λ).toReal :=
      { image_add_right := fun Λ hΛ i ↦ by simp only [ha.image_add_right Λ hΛ i]
        union_le := fun Λ Δ hΛ hΔ hd hu ↦ by
          have := ha.union_le Λ Δ hΛ hΔ hd hu
          rw [← hcoe _ hΛ, ← hcoe _ hΔ, ← hcoe _ hu, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
          exact this }
    have := ha''.tendsto_coe_div_card h
    have hα : (⨅ Δ : Finset (ι → ℤ), ⨅ (_ : Δ.IsBox), (((a Δ).toReal / #Δ : ℝ) : EReal)) =
        ⨅ Δ : Finset (ι → ℤ), ⨅ (_ : Δ.IsBox), a Δ / (#Δ : EReal) :=
      iInf_congr fun Δ ↦ iInf_congr fun hΔ ↦ by rw [EReal.coe_div, hcoe Δ hΔ, EReal.coe_natCast]
    rw [hα] at this
    refine this.congr' ?_
    filter_upwards [hbox] with j hj
    rw [EReal.coe_div, hcoe _ (isBox_Icc hj), EReal.coe_natCast]

/-- **Georgii Lemma (15.11) for real-valued `a` bounded below**, in the form of Mathlib's
`Subadditive.tendsto_lim`: if the ratios `|Δ|⁻¹ a(Δ)`, `Δ ∈ 𝒮_□`, are bounded below, then along
boxes all of whose sides tend to infinity `|Λⱼ|⁻¹ a(Λⱼ)` converges in `ℝ` to their infimum. -/
theorem tendsto_div_card_of_bddBelow {a : Finset (ι → ℤ) → ℝ} (ha : BoxSubadditive a)
    (hbdd : BddBelow ((fun Δ ↦ a Δ / #Δ) '' {Δ : Finset (ι → ℤ) | Δ.IsBox})) {κ : Type*}
    {l : Filter κ} {m n : κ → ι → ℤ} (h : ∀ k, Tendsto (fun j ↦ n j k - m j k) l atTop) :
    Tendsto (fun j ↦ a (Icc (m j) (n j)) / #(Icc (m j) (n j))) l
      (𝓝 (sInf ((fun Δ ↦ a Δ / #Δ) '' {Δ : Finset (ι → ℤ) | Δ.IsBox}))) := by
  have hne : ((fun Δ ↦ a Δ / #Δ) '' {Δ : Finset (ι → ℤ) | Δ.IsBox}).Nonempty :=
    ⟨_, {0}, isBox_singleton 0, rfl⟩
  rw [← EReal.tendsto_coe]
  convert ha.tendsto_coe_div_card h using 2
  rw [EReal.coe_strictMono.monotone.map_csInf_of_continuousAt
    continuous_coe_real_ereal.continuousAt hne hbdd, Set.image_image, sInf_image]
  rfl

/-- **Georgii Lemma (15.11) as stated**, for cubes: if `Λⱼ = ∏ₖ [mⱼₖ, mⱼₖ + sⱼ]` are cubes with
`|Λⱼ| → ∞`, then `|Λⱼ|⁻¹ a(Λⱼ) → inf_{Δ ∈ 𝒮_□} |Δ|⁻¹ a(Δ)` in `[-∞, ∞)`. -/
theorem tendsto_div_card_of_tendsto_card {a : Finset (ι → ℤ) → EReal} (ha : BoxSubadditive a)
    (ha' : ∀ Λ : Finset (ι → ℤ), Λ.IsBox → a Λ ≠ ⊤) {κ : Type*} {l : Filter κ}
    {m : κ → ι → ℤ} {s : κ → ℕ}
    (hs : Tendsto (fun j ↦ #(Icc (m j) fun k ↦ m j k + s j)) l atTop) :
    Tendsto (fun j ↦ a (Icc (m j) fun k ↦ m j k + s j) /
      (#(Icc (m j) fun k ↦ m j k + s j) : EReal)) l
      (𝓝 (⨅ Δ, ⨅ (_ : Δ.IsBox), a Δ / (#Δ : EReal))) := by
  refine ha.tendsto_div_card ha' fun k ↦ ?_
  simp only [add_sub_cancel_left]
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hcard : ∀ j, #(Icc (m j) fun k ↦ m j k + s j) = (s j + 1) ^ Fintype.card ι := fun j ↦ by
    have : ∀ k, (m j k + (s j : ℤ) + 1 - m j k).toNat = s j + 1 := fun k ↦ by omega
    simp only [Pi.card_Icc, Int.card_Icc, this, prod_const, card_univ]
  simp only [hcard] at hs
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 fun b ↦ ?_)
  rcases isEmpty_or_nonempty ι with hι | hι
  · exfalso
    have := hι
    simp only [Fintype.card_eq_zero, pow_zero] at hs
    obtain ⟨j, hj⟩ := (tendsto_atTop.1 hs 2).exists
    omega
  · have hd : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
    filter_upwards [tendsto_atTop.1 hs ((b + 1) ^ Fintype.card ι)] with j hj
    have := (Nat.pow_le_pow_iff_left hd).1 hj
    omega

end BoxSubadditive

/-- A subadditive sequence `u : ℕ → ℝ`, evaluated at the cardinality, is box-subadditive on
every `ι → ℤ`: disjoint boxes with box union have additive cardinalities. -/
theorem Subadditive.boxSubadditive_card {u : ℕ → ℝ} (h : Subadditive u) :
    BoxSubadditive fun Λ : Finset (ι → ℤ) ↦ u #Λ where
  image_add_right Λ _ i := by simp only [card_image_of_injective _ (add_left_injective i)]
  union_le Λ Δ _ _ hd _ := by
    show u #(Λ ∪ Δ) ≤ u #Λ + u #Δ
    rw [card_union_of_disjoint hd]
    exact h _ _

/-- Mathlib's one-dimensional Fekete lemma `Subadditive.tendsto_lim`, recovered from Georgii's
Lemma (15.11) in the form `BoxSubadditive.tendsto_div_card_of_bddBelow` on `Unit → ℤ`: the boxes
`Icc 0 (n - 1)` of `Unit → ℤ` have cardinality `n`, so the box infimum over `𝒮_□` is the infimum
over `n ≥ 1` defining `Subadditive.lim`. -/
theorem Subadditive.tendsto_lim_of_tendsto_div_card {u : ℕ → ℝ} (h : Subadditive u)
    (hbdd : BddBelow (Set.range fun n : ℕ ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 h.lim) := by
  have hcard : ∀ n : ℕ, #(Icc (fun _ : Unit ↦ (0 : ℤ)) fun _ ↦ (n : ℤ) - 1) = n := fun n ↦ by
    simp [Pi.card_Icc, Int.card_Icc]
  -- the boxes of `Unit → ℤ` have exactly the cardinalities `n ≥ 1`
  have himage : (fun Δ : Finset (Unit → ℤ) ↦ u #Δ / #Δ) '' {Δ | Δ.IsBox} =
      (fun n : ℕ ↦ u n / n) '' Set.Ici 1 := by
    ext x
    constructor
    · rintro ⟨Δ, hΔ, rfl⟩
      exact ⟨#Δ, hΔ.card_pos, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      refine ⟨Icc (fun _ ↦ 0) fun _ ↦ (n : ℤ) - 1, isBox_Icc fun _ ↦ ?_, ?_⟩
      · have : 1 ≤ n := hn
        simp only []
        omega
      · simp only [hcard]
  have hbdd' : BddBelow ((fun Δ : Finset (Unit → ℤ) ↦ u #Δ / #Δ) '' {Δ | Δ.IsBox}) := by
    rw [himage]
    exact hbdd.mono (Set.image_subset_range _ _)
  have key := (h.boxSubadditive_card (ι := Unit)).tendsto_div_card_of_bddBelow hbdd' (l := atTop)
    (m := fun (_ : ℕ) _ ↦ (0 : ℤ)) (n := fun (j : ℕ) _ ↦ (j : ℤ) - 1) fun _ ↦
      tendsto_atTop_atTop.2 fun b ↦ ⟨(b + 1).toNat, fun j hj ↦ by
        show b ≤ (j : ℤ) - 1 - 0
        omega⟩
  rw [himage] at key
  rw [Subadditive.lim]
  refine (tendsto_congr fun j ↦ ?_).1 key
  simp only [hcard]

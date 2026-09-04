/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Boundaries, bonds and interval bounds of finite subsets of `ℤ`

Georgii (3.4): the boundary `∂Λ = {i ∉ Λ : |i - j| = 1 for some j ∈ Λ}` of a finite `Λ ⊆ ℤ`; the
bonds `{j, j + 1}` meeting `Λ`, indexed by their left endpoint; and the symmetric interval bound
`Λ ⊆ [-boundOf Λ, boundOf Λ]`.
-/

@[expose] public section

namespace MeasureTheory.GibbsMeasure.Markov

/-- Georgii (3.4): the boundary `∂Λ = {i ∈ ℤ ∖ Λ : |i - j| = 1 for some j ∈ Λ}` of a finite
volume `Λ ⊆ ℤ`. -/
def boundary (Λ : Finset ℤ) : Finset ℤ := (Λ.image (· + 1) ∪ Λ.image (· - 1)) \ Λ

lemma mem_boundary {Λ : Finset ℤ} {i : ℤ} :
    i ∈ boundary Λ ↔ i ∉ Λ ∧ ∃ j ∈ Λ, |i - j| = 1 := by
  simp only [boundary, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩, hi⟩ <;>
      exact ⟨hi, j, hj, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩
  · rintro ⟨hi, j, hj, habs⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs
    refine ⟨?_, hi⟩
    rcases habs with h | h
    · exact Or.inl ⟨j, hj, by omega⟩
    · exact Or.inr ⟨j, hj, by omega⟩

lemma disjoint_boundary (Λ : Finset ℤ) : Disjoint Λ (boundary Λ) :=
  Finset.disjoint_sdiff

lemma succ_mem_union_boundary {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ Λ) :
    i + 1 ∈ Λ ∪ boundary Λ := by
  by_cases h : i + 1 ∈ Λ
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (mem_boundary.2 ⟨h, i, hi, by
      rw [show i + 1 - i = (1 : ℤ) by omega, abs_one]⟩)

lemma pred_mem_union_boundary {Λ : Finset ℤ} {i : ℤ} (hi : i ∈ Λ) :
    i - 1 ∈ Λ ∪ boundary Λ := by
  by_cases h : i - 1 ∈ Λ
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (mem_boundary.2 ⟨h, i, hi, by
      rw [show i - 1 - i = (-1 : ℤ) by omega, abs_neg, abs_one]⟩)

/-- The boundary of an interval is the two-point set of Georgii (3.8)(1). -/
lemma boundary_Icc {a b : ℤ} (hab : a ≤ b) :
    boundary (Finset.Icc a b) = {a - 1, b + 1} := by
  ext i
  rw [mem_boundary]
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hi, j, hj, habs⟩
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at habs
    omega
  · rintro (rfl | rfl)
    · exact ⟨by omega, a, ⟨le_rfl, hab⟩, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩
    · exact ⟨by omega, b, ⟨hab, le_rfl⟩, by rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega⟩

/-- The left endpoints of the bonds `{j, j + 1}` meeting a finite volume `Λ ⊆ ℤ`. -/
def bondsOf (Λ : Finset ℤ) : Finset ℤ := Λ ∪ Λ.image (· - 1)

lemma mem_bondsOf {Λ : Finset ℤ} {j : ℤ} : j ∈ bondsOf Λ ↔ j ∈ Λ ∨ j + 1 ∈ Λ := by
  simp only [bondsOf, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨k, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hk)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨j + 1, h, by omega⟩

lemma bondsOf_Icc {a b : ℤ} (hab : a ≤ b) :
    bondsOf (Finset.Icc a b) = Finset.Ico (a - 1) (b + 1) := by
  ext j
  rw [mem_bondsOf]
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

lemma bondsOf_mono {Λ₁ Λ₂ : Finset ℤ} (h : Λ₁ ⊆ Λ₂) : bondsOf Λ₁ ⊆ bondsOf Λ₂ := fun _ hj ↦ by
  rw [mem_bondsOf] at hj ⊢
  exact hj.imp (fun h' ↦ h h') fun h' ↦ h h'

lemma subset_bondsOf (Λ : Finset ℤ) : Λ ⊆ bondsOf Λ := fun _ hj ↦ mem_bondsOf.2 (Or.inl hj)

lemma bondsOf_union (Λ₁ Λ₂ : Finset ℤ) : bondsOf (Λ₁ ∪ Λ₂) = bondsOf Λ₁ ∪ bondsOf Λ₂ := by
  ext j
  simp only [mem_bondsOf, Finset.mem_union]
  tauto

/-- Volumes with disjoint bonds are disjoint and non-adjacent. -/
lemma disjoint_of_disjoint_bondsOf {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) :
    Disjoint Λ₁ Λ₂ :=
  Finset.disjoint_of_subset_left (subset_bondsOf Λ₁)
    (Finset.disjoint_of_subset_right (subset_bondsOf Λ₂) h)

/-- The two bonds `{i - 1, i}` and `{i, i + 1}` meeting a single site. -/
lemma bondsOf_singleton (i : ℤ) : bondsOf {i} = {i - 1, i} := by
  ext j
  rw [mem_bondsOf]
  simp only [Finset.mem_singleton, Finset.mem_insert]
  omega

/-- The bonds meeting the open interval `]i, k[` are exactly `[i, k[`. -/
lemma bondsOf_Ioo {i k : ℤ} (hik : i + 1 < k) : bondsOf (Finset.Ioo i k) = Finset.Ico i k := by
  ext j
  rw [mem_bondsOf]
  simp only [Finset.mem_Ioo, Finset.mem_Ico]
  omega

/-- The bonds meeting a translate `Λ.image (·+a)` are the translate of the bonds meeting `Λ`. -/
lemma bondsOf_image_add (Λ : Finset ℤ) (a : ℤ) :
    bondsOf (Λ.image (· + a)) = (bondsOf Λ).image (· + a) := by
  ext j
  rw [Finset.mem_image, mem_bondsOf]
  constructor
  · rintro (h | h)
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 h
      exact ⟨k, mem_bondsOf.2 (Or.inl hk), rfl⟩
    · obtain ⟨k, hk, hjk⟩ := Finset.mem_image.1 h
      refine ⟨k - 1, mem_bondsOf.2 (Or.inr ?_), by omega⟩
      rwa [sub_add_cancel]
  · rintro ⟨k, hk, rfl⟩
    rcases mem_bondsOf.1 hk with h | h
    · exact Or.inl (Finset.mem_image.2 ⟨k, h, rfl⟩)
    · exact Or.inr (Finset.mem_image.2 ⟨k + 1, h, by omega⟩)

/-- A symmetric interval bound for a finite volume: `Λ ⊆ [-boundOf Λ, boundOf Λ]`. -/
def boundOf (Λ : Finset ℤ) : ℤ := ((Λ.sup fun i ↦ i.natAbs : ℕ) : ℤ)

lemma boundOf_nonneg (Λ : Finset ℤ) : 0 ≤ boundOf Λ := Int.natCast_nonneg _

lemma subset_Icc_boundOf (Λ : Finset ℤ) : Λ ⊆ Finset.Icc (-boundOf Λ) (boundOf Λ) := by
  intro i hi
  have h := Finset.le_sup (f := fun j : ℤ ↦ j.natAbs) hi
  simp only [Finset.mem_Icc, boundOf]
  omega

end MeasureTheory.GibbsMeasure.Markov

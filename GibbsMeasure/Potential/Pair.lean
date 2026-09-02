/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Transformation
public import GibbsMeasure.Potential.Summable

/-!
# Pair potentials

* `Potential.pairTerms f`: the family `A ↦ f i j` if `A = {i, j}` with `i < j`, else `0`, on a
  linearly ordered set of sites.
* `Potential.pair φ`: **Georgii (9.10)**, the pair potential `Φ_{{i,j}}(ω) = φ_{ij}(ω_i, ω_j)`;
  `map_pair_eq_iff` characterises its pure-spin symmetries.
* `Potential.pairShift φ`: **Georgii (9.4)**, the shift-invariant pair potential
  `Φ_{{i, i+k}} = φ_k(σ_i, σ_{i+k})` on `ℤ`; `isShiftInvariant_pairShift`, the site-norm bound
  `normAt_pairShift_le` and the criterion `isAbsolutelySummable_pairShift`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ### Pair potentials on a linearly ordered set of sites, Georgii (9.10) -/

namespace Potential

variable {S E : Type*} [MeasurableSpace E] [LinearOrder S]

section PairTerms

variable {α : Type*} [AddCommMonoid α]

/-- The family `A ↦ f i j` if `A = {i, j}` with `i < j`, and `0` otherwise, written as a finite
double sum so that it is manifestly measurable in any parameters of `f`. -/
def pairTerms (f : S → S → α) (A : Finset S) : α :=
  ∑ i ∈ A, ∑ j ∈ A, if A = {i, j} then (if i < j then f i j else 0) else 0

variable {f g : S → S → α}

/-- A pair `{i, j}` with `i < j` determines `i` and `j`. -/
lemma pair_eq_pair_iff_of_lt {i j i' j' : S} (hij : i < j) (hij' : i' < j') :
    ({i, j} : Finset S) = {i', j'} ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have hi : i ∈ ({i', j'} : Finset S) := h ▸ Finset.mem_insert_self i {j}
    have hj : j ∈ ({i', j'} : Finset S) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      first
      | exact ⟨hi, hj⟩
      | (rw [hi, hj] at hij; exact absurd hij (lt_irrefl _))
      | (rw [hi, hj] at hij; exact absurd (hij'.trans hij) (lt_irrefl _))
  · rintro ⟨rfl, rfl⟩
    rfl

lemma pairTerms_pair {i j : S} (hij : i < j) : pairTerms f {i, j} = f i j := by
  have hne : i ≠ j := hij.ne
  have hii : ({i, j} : Finset S) ≠ {i, i} := fun h ↦ by
    have : j ∈ ({i, i} : Finset S) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at this
    exact hne this.symm
  have hjj : ({i, j} : Finset S) ≠ {j, j} := fun h ↦ by
    have : i ∈ ({j, j} : Finset S) := h ▸ Finset.mem_insert_self i {j}
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at this
    exact hne this
  have e1 : (if ({i, j} : Finset S) = {i, i} then (if i < i then f i i else 0) else 0) = 0 :=
    ite_eq_right hii
  have e2 : (if ({i, j} : Finset S) = {i, j} then (if i < j then f i j else 0) else 0) = f i j := by
    rw [ite_eq_left rfl, ite_eq_left hij]
  have e3 : (if ({i, j} : Finset S) = {j, i} then (if j < i then f j i else 0) else 0) = 0 := by
    rw [ite_eq_left (Finset.pair_comm i j), ite_eq_right (not_lt.2 hij.le)]
  have e4 : (if ({i, j} : Finset S) = {j, j} then (if j < j then f j j else 0) else 0) = 0 :=
    ite_eq_right hjj
  unfold pairTerms
  rw [Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne, e1, e2, e3, e4, zero_add,
    add_zero, add_zero]

lemma pairTerms_eq_zero {A : Finset S} (hA : ∀ i j, i < j → A ≠ {i, j}) :
    pairTerms f A = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases h1 : A = {i, j}
  · by_cases h2 : i < j
    · exact absurd h1 (hA i j h2)
    · simp [h2]
  · simp [h1]

/-- Every finite set of sites is a pair `{i, j}`, `i < j`, or not. -/
lemma exists_lt_pair_or (A : Finset S) :
    (∃ i j, i < j ∧ A = {i, j}) ∨ ∀ i j, i < j → A ≠ {i, j} := by
  by_cases h : ∃ i j, i < j ∧ A = {i, j}
  · exact Or.inl h
  · push Not at h
    exact Or.inr h

lemma pairTerms_congr (h : ∀ i j, i < j → f i j = g i j) (A : Finset S) :
    pairTerms f A = pairTerms g A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij, pairTerms_pair hij, h i j hij]
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero hA]

lemma pairTerms_add (f g : S → S → α) (A : Finset S) :
    pairTerms (fun i j ↦ f i j + g i j) A = pairTerms f A + pairTerms g A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij, pairTerms_pair hij, pairTerms_pair hij]
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero hA, pairTerms_eq_zero hA, add_zero]

lemma pairTerms_sub {α : Type*} [AddCommGroup α] (f g : S → S → α) (A : Finset S) :
    pairTerms (fun i j ↦ f i j - g i j) A = pairTerms f A - pairTerms g A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij, pairTerms_pair hij, pairTerms_pair hij]
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero hA, pairTerms_eq_zero hA, sub_zero]

lemma pairTerms_le_pairTerms {α : Type*} [AddCommMonoid α] [Preorder α] {f g : S → S → α}
    (h : ∀ i j, i < j → f i j ≤ g i j) (A : Finset S) :
    pairTerms f A ≤ pairTerms g A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij, pairTerms_pair hij]; exact h i j hij
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero hA]

lemma pairTerms_nonneg {α : Type*} [AddCommMonoid α] [Preorder α] {g : S → S → α}
    (h0 : ∀ i j, i < j → 0 ≤ g i j) (A : Finset S) : 0 ≤ pairTerms g A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij]; exact h0 i j hij
  · rw [pairTerms_eq_zero hA]

/-- An indicator on the finite set pulls into the pair family. -/
lemma ite_pairTerms (P : Finset S → Prop) [DecidablePred P] (A : Finset S) :
    (if P A then pairTerms f A else 0) = pairTerms (fun i j ↦ if P {i, j} then f i j else 0) A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij, pairTerms_pair hij]
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero hA, ite_self]

/-- Summing the pair family over all finite sets of sites is summing `f` over the pairs `i < j`;
no summability is assumed. -/
lemma tsum_pairTerms [TopologicalSpace α] (f : S → S → α) :
    ∑' A : Finset S, pairTerms f A = ∑' q : S × S, if q.1 < q.2 then f q.1 q.2 else 0 := by
  let g : {q : S × S // q.1 < q.2} → Finset S := fun q ↦ {q.1.1, q.1.2}
  have hg : Function.Injective g := fun q q' h ↦ by
    obtain ⟨h1, h2⟩ := (pair_eq_pair_iff_of_lt q.2 q'.2).1 h
    exact Subtype.ext (Prod.ext h1 h2)
  have hsupp : Function.support (pairTerms f) ⊆ Set.range g := by
    intro A hA
    rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA'
    · exact ⟨⟨(i, j), hij⟩, rfl⟩
    · exact absurd (pairTerms_eq_zero hA') hA
  rw [← hg.tsum_eq hsupp, ← tsum_subtype_eq_of_support_subset
    (s := {q : S × S | q.1 < q.2}) (f := fun q : S × S ↦ if q.1 < q.2 then f q.1 q.2 else 0)
    (fun q hq ↦ by by_contra h; exact hq (ite_eq_right h))]
  refine tsum_congr fun q ↦ ?_
  simp only [g, pairTerms_pair q.2]
  exact (ite_eq_left q.2).symm

/-- The summability transfer along the pair enumeration. -/
lemma summable_pairTerms_iff [TopologicalSpace α] (f : S → S → α) :
    Summable (pairTerms f) ↔ Summable (fun q : S × S ↦ if q.1 < q.2 then f q.1 q.2 else 0) := by
  let g : {q : S × S // q.1 < q.2} → Finset S := fun q ↦ {q.1.1, q.1.2}
  have hg : Function.Injective g := fun q q' h ↦ by
    obtain ⟨h1, h2⟩ := (pair_eq_pair_iff_of_lt q.2 q'.2).1 h
    exact Subtype.ext (Prod.ext h1 h2)
  have hsupp : Function.support (pairTerms f) ⊆ Set.range g := by
    intro A hA
    rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA'
    · exact ⟨⟨(i, j), hij⟩, rfl⟩
    · exact absurd (pairTerms_eq_zero hA') hA
  rw [← hg.summable_iff fun A hA ↦ Function.notMem_support.1 fun h ↦ hA (hsupp h)]
  have hF : (fun q : S × S ↦ if q.1 < q.2 then f q.1 q.2 else 0) =
      {q : S × S | q.1 < q.2}.indicator (fun q ↦ if q.1 < q.2 then f q.1 q.2 else 0) := by
    funext q
    by_cases h : q.1 < q.2
    · rw [Set.indicator_of_mem (show q ∈ {q : S × S | q.1 < q.2} from h)]
    · rw [Set.indicator_of_notMem (show q ∉ {q : S × S | q.1 < q.2} from h), ite_eq_right h]
  conv_rhs => rw [hF]
  rw [← summable_subtype_iff_indicator]
  refine summable_congr fun q ↦ ?_
  simp only [Function.comp_apply, g, pairTerms_pair q.2]
  exact (ite_eq_left q.2).symm

/-- Summing the pair family over the subsets of a finite volume `Δ` sums `f` over the pairs in
`Δ`. -/
lemma sum_powerset_pairTerms (Δ : Finset S) (f : S → S → α) :
    ∑ A ∈ Δ.powerset, pairTerms f A = ∑ i ∈ Δ, ∑ j ∈ Δ, if i < j then f i j else 0 := by
  have h1 : ∀ A ∈ Δ.powerset, pairTerms f A =
      ∑ i ∈ Δ, ∑ j ∈ Δ, if A = {i, j} then (if i < j then f i j else 0) else 0 := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    unfold pairTerms
    rw [Finset.sum_subset hA fun i _ hi ↦ Finset.sum_eq_zero fun j _ ↦
      ite_eq_right fun h ↦ hi (by rw [h]; exact Finset.mem_insert_self i {j})]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_subset hA fun j _ hj ↦ ?_
    exact ite_eq_right fun h ↦ hj (by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.sum_ite_eq' Δ.powerset {i, j} (fun _ ↦ if i < j then f i j else 0)]
  exact ite_eq_left (Finset.mem_powerset.2
    (Finset.insert_subset hi (Finset.singleton_subset_iff.2 hj)))

end PairTerms

/-- **Georgii (9.10).** The pair potential `Φ_{{i,j}} = φ_{ij}(σ_i, σ_j)` for `i < j`, and
`Φ_A = 0` for every other `A`. Georgii's (9.4) is the shift-invariant special case
`φ_{ij} = φ_{j-i}` on `ℤ` (`Potential.pairShift`). -/
def pair (φ : S → S → E → E → ℝ) : Potential S E :=
  fun A η ↦ pairTerms (fun i j ↦ φ i j (η i) (η j)) A

variable (φ : S → S → E → E → ℝ)

lemma pair_apply (A : Finset S) (η : S → E) :
    pair φ A η = pairTerms (fun i j ↦ φ i j (η i) (η j)) A := rfl

lemma pair_pair {i j : S} (hij : i < j) (η : S → E) : pair φ {i, j} η = φ i j (η i) (η j) :=
  pairTerms_pair hij

lemma pair_eq_zero {A : Finset S} (hA : ∀ i j, i < j → A ≠ {i, j}) : pair φ A = 0 :=
  funext fun _ ↦ pairTerms_eq_zero hA

/-- A pair potential with measurable `φ_{ij}` is a potential in the sense of Georgii (2.2)(i). -/
lemma isPotential_pair (hφ : ∀ i j, Measurable (Function.uncurry (φ i j))) :
    IsPotential (pair φ) where
  measurable A := by
    unfold pair pairTerms
    refine Finset.measurable_sum _ fun i hi ↦ Finset.measurable_sum _ fun j hj ↦ ?_
    by_cases hA : A = {i, j}
    · by_cases hij : i < j
      · simp only [ite_eq_left hA, ite_eq_left hij]
        exact (hφ i j).comp
          ((measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Finset.mem_coe.2 hi)).prodMk
            (measurable_cylinderEvent_apply (X := fun _ : S ↦ E) (Finset.mem_coe.2 hj)))
      · simp only [ite_eq_right hij, ite_self]
        exact measurable_const
    · simp only [ite_eq_right hA]
      exact measurable_const

/-- The interaction terms of a pair potential in the volume `Λ`, as a pair family. -/
lemma hamiltonianTerms_pair (Λ : Finset S) (η : S → E) (A : Finset S) :
    (pair φ).hamiltonianTerms Λ η A =
      pairTerms (fun i j ↦ if ¬ Disjoint {i, j} Λ then φ i j (η i) (η j) else 0) A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [pairTerms_pair hij]
    by_cases h : Disjoint ({i, j} : Finset S) Λ
    · rw [hamiltonianTerms_of_disjoint h, ite_eq_right (not_not.2 h)]
    · rw [hamiltonianTerms_of_not_disjoint h, ite_eq_left h, pair_pair φ hij]
  · rw [pairTerms_eq_zero hA]
    by_cases h : Disjoint A Λ
    · exact hamiltonianTerms_of_disjoint h η
    · rw [hamiltonianTerms_of_not_disjoint h, pair_apply, pairTerms_eq_zero hA]

/-- Georgii, remark after (9.10): a pure spin transformation `τ = (τ_i)` is a symmetry of the
pair potential `Φ` iff `φ_{ij}(τ_i x, τ_j y) = φ_{ij}(x, y)` for all `i < j` and `x, y`. -/
theorem map_pair_eq_iff {τ : MeasureTheory.GibbsMeasure.Transformation S E}
    (hτ : τ.IsPureSpin) :
    Potential.map τ (pair φ) = pair φ ↔
      ∀ i j, i < j → ∀ x y, φ i j (τ.spin i x) (τ.spin j y) = φ i j x y := by
  have hsites : ∀ A : Finset S, A.map τ.sites.toEmbedding = A := fun A ↦ by
    ext i
    rw [Finset.mem_map_equiv, hτ]
    rfl
  rw [map_eq_iff]
  constructor
  · intro h i j hij x y
    classical
    have := h {i, j} (fun k ↦ if k = i then x else y)
    rw [hsites, pair_pair φ hij, pair_pair φ hij, hτ.toFun_apply, hτ.toFun_apply] at this
    simpa [hij.ne'] using this
  · intro h A η
    rw [hsites, pair_apply, pair_apply]
    refine pairTerms_congr (fun i j hij ↦ ?_) A
    rw [hτ.toFun_apply, hτ.toFun_apply, h i j hij]

end Potential

/-! ### Georgii (9.4): shift-invariant pair potentials on `ℤ` -/

namespace Potential

variable {E : Type*} [MeasurableSpace E]

/-- **Georgii (9.4).** The shift-invariant pair potential `Φ_{{i, i+k}} = φ_k(σ_i, σ_{i+k})`,
`k ≥ 1`, on `S = ℤ`; the values `φ_k` for `k ≤ 0` are not used. -/
def pairShift (φ : ℤ → E → E → ℝ) : Potential ℤ E := pair fun i j x y ↦ φ (j - i) x y

variable (φ : ℤ → E → E → ℝ)

lemma pairShift_pair {i j : ℤ} (hij : i < j) (η : ℤ → E) :
    pairShift φ {i, j} η = φ (j - i) (η i) (η j) := pair_pair _ hij η

lemma isPotential_pairShift (hφ : ∀ k, Measurable (Function.uncurry (φ k))) :
    IsPotential (pairShift φ) :=
  isPotential_pair _ fun i j ↦ hφ (j - i)

/-- The pair family transported along an order-preserving bijection of the sites. -/
lemma pairTerms_map {S α : Type*} [LinearOrder S] [AddCommMonoid α] (f : S → S → α) (e : S ≃ S)
    (he : ∀ a b, e a < e b ↔ a < b) (A : Finset S) :
    pairTerms f (A.map e.toEmbedding) = pairTerms (fun i j ↦ f (e i) (e j)) A := by
  rcases exists_lt_pair_or A with ⟨i, j, hij, rfl⟩ | hA
  · rw [Finset.map_insert, Finset.map_singleton]
    simp only [Equiv.coe_toEmbedding]
    rw [pairTerms_pair ((he i j).2 hij), pairTerms_pair hij]
  · rw [pairTerms_eq_zero hA, pairTerms_eq_zero]
    intro i j hij h
    have := hA (e.symm i) (e.symm j) (by rwa [← he, e.apply_symm_apply, e.apply_symm_apply])
    apply this
    rw [← Finset.map_inj (f := e.toEmbedding), h, Finset.map_insert, Finset.map_singleton]
    simp

/-- **Georgii, after (9.4):** the potential (9.4) is shift-invariant, `Φ ∈ ℬ_Θ`. -/
theorem isShiftInvariant_pairShift : (pairShift φ).IsShiftInvariant := by
  intro p
  rw [map_eq_iff]
  intro A η
  simp only [pairShift, pair_apply]
  rw [show (shift E p).sites = Equiv.addRight p from rfl,
    pairTerms_map _ (Equiv.addRight p) (fun a b ↦ by simp) A]
  refine pairTerms_congr (fun i j _ ↦ ?_) A
  simp only [shift_toFun_apply, Equiv.coe_addRight, add_sub_cancel_right,
    add_sub_add_right_eq_sub]

/-- The uniform norm `‖φ_k‖ = sup_{x, y} |φ_k(x, y)|` of the `k`-th pair interaction. -/
def pairNorm (k : ℤ) : ℝ≥0∞ := ⨆ (x : E) (y : E), ‖φ k x y‖ₑ

/-- `‖φ_a − φ_b‖ = sup_{x, y} |φ_a(x, y) − φ_b(x, y)|`. -/
def pairDist (a b : ℤ) : ℝ≥0∞ := ⨆ (x : E) (y : E), ‖φ a x y - φ b x y‖ₑ

omit [MeasurableSpace E] in
lemma enorm_le_pairNorm (k : ℤ) (x y : E) : ‖φ k x y‖ₑ ≤ pairNorm φ k :=
  le_iSup₂ (f := fun x y ↦ ‖φ k x y‖ₑ) x y

omit [MeasurableSpace E] in
lemma enorm_sub_le_pairDist (a b : ℤ) (x y : E) : ‖φ a x y - φ b x y‖ₑ ≤ pairDist φ a b :=
  le_iSup₂ (f := fun x y ↦ ‖φ a x y - φ b x y‖ₑ) x y

omit [MeasurableSpace E] in
lemma pairDist_comm (a b : ℤ) : pairDist φ a b = pairDist φ b a := by
  simp only [pairDist, enorm_sub_rev]

/-- **Georgii, after (9.4):** the potential (9.4) is absolutely summable when
`∑_{k ≥ 1} ‖φ_k‖ < ∞`; in fact `‖Φ‖_i ≤ 2 ∑_{k ≥ 1} ‖φ_k‖` at every site. -/
theorem normAt_pairShift_le (i : ℤ) :
    (pairShift φ).normAt i ≤ 2 * ∑' k : ℕ, pairNorm φ (k + 1) := by
  classical
  let N : ℤ → ℤ → ℝ≥0∞ := fun a b ↦ if a = i ∨ b = i then pairNorm φ (b - a) else 0
  have hpt : ∀ A : Finset ℤ,
      {A : Finset ℤ | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖pairShift φ A η‖ₑ) A ≤ pairTerms N A := by
    intro A
    rcases exists_lt_pair_or A with ⟨a, b, hab, rfl⟩ | hA
    · rw [pairTerms_pair hab]
      by_cases hi : i ∈ ({a, b} : Finset ℤ)
      · rw [Set.indicator_of_mem (show ({a, b} : Finset ℤ) ∈ {A : Finset ℤ | i ∈ A} from hi)]
        simp only [N, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
        rw [ite_eq_left (show a = i ∨ b = i by rcases hi with rfl | rfl <;> simp)]
        refine iSup_le fun η ↦ ?_
        rw [pairShift_pair φ hab]
        exact enorm_le_pairNorm φ _ _ _
      · rw [Set.indicator_of_notMem (show ({a, b} : Finset ℤ) ∉ {A : Finset ℤ | i ∈ A} from hi)]
        exact bot_le
    · rw [pairTerms_eq_zero hA]
      by_cases hi : i ∈ A
      · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | i ∈ A} from hi)]
        refine iSup_le fun η ↦ ?_
        rw [pairShift, pair_apply, pairTerms_eq_zero hA, enorm_zero]
      · rw [Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | i ∈ A} from hi)]
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [tsum_pairTerms]
  let F₁ : ℤ × ℤ → ℝ≥0∞ := fun q ↦ if q.1 < q.2 ∧ q.1 = i then pairNorm φ (q.2 - q.1) else 0
  let F₂ : ℤ × ℤ → ℝ≥0∞ := fun q ↦ if q.1 < q.2 ∧ q.2 = i then pairNorm φ (q.2 - q.1) else 0
  have hsplit : ∀ q : ℤ × ℤ, (if q.1 < q.2 then N q.1 q.2 else 0) ≤ F₁ q + F₂ q := by
    intro q
    simp only [N, F₁, F₂]
    by_cases h : q.1 < q.2
    · rw [ite_eq_left h]
      by_cases h1 : q.1 = i
      · rw [ite_eq_left (Or.inl h1), ite_eq_left ⟨h, h1⟩]
        exact le_self_add
      · by_cases h2 : q.2 = i
        · rw [ite_eq_left (Or.inr h2), ite_eq_right (show ¬ (q.1 < q.2 ∧ q.1 = i) by tauto),
            ite_eq_left (show q.1 < q.2 ∧ q.2 = i from ⟨h, h2⟩), zero_add]
        · rw [ite_eq_right (by tauto)]
          exact bot_le
    · rw [ite_eq_right h]
      exact bot_le
  refine le_trans (ENNReal.tsum_le_tsum hsplit) ?_
  rw [ENNReal.tsum_add, two_mul]
  refine add_le_add ?_ ?_
  · let g : ℕ → ℤ × ℤ := fun k ↦ (i, i + 1 + k)
    have hg : Function.Injective g := fun k l h ↦ by
      simp only [g, Prod.mk.injEq, true_and] at h
      omega
    have hsupp : Function.support F₁ ⊆ Set.range g := by
      intro q hq
      simp only [F₁, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hq
      refine ⟨(q.2 - q.1 - 1).toNat, ?_⟩
      simp only [g]
      ext
      · exact hq.1.2.symm
      · simp only
        omega
    rw [← hg.tsum_eq hsupp]
    refine le_of_eq (tsum_congr fun k ↦ ?_)
    simp only [F₁, g, and_true]
    rw [ite_eq_left (show i < i + 1 + (k : ℤ) by omega)]
    congr 1
    ring
  · let g : ℕ → ℤ × ℤ := fun k ↦ (i - 1 - k, i)
    have hg : Function.Injective g := fun k l h ↦ by
      simp only [g, Prod.mk.injEq, and_true] at h
      omega
    have hsupp : Function.support F₂ ⊆ Set.range g := by
      intro q hq
      simp only [F₂, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hq
      refine ⟨(q.2 - q.1 - 1).toNat, ?_⟩
      simp only [g]
      ext
      · simp only
        omega
      · exact hq.1.2.symm
    rw [← hg.tsum_eq hsupp]
    refine le_of_eq (tsum_congr fun k ↦ ?_)
    simp only [F₂, g, and_true]
    rw [ite_eq_left (show i - 1 - (k : ℤ) < i by omega)]
    congr 1
    ring

/-- The potential (9.4) is absolutely summable when `∑_{k ≥ 1} ‖φ_k‖ < ∞`. -/
theorem isAbsolutelySummable_pairShift (h : ∑' k : ℕ, pairNorm φ (k + 1) ≠ ⊤) :
    IsAbsolutelySummable (pairShift φ) where
  normAt_ne_top i := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top h)
    (normAt_pairShift_le φ i)

/-- For a shift-invariant potential the site norms `‖Φ‖_i` do not depend on `i`. -/
lemma normAt_eq_of_isShiftInvariant {S : Type*} [AddGroup S] {Φ : Potential S E}
    (h : Φ.IsShiftInvariant) (i : S) : Φ.normAt i = Φ.normAt 0 := by
  have := normAt_map (shift E i) Φ 0
  rw [h i] at this
  rw [← this]
  simp [shift]

end Potential

end

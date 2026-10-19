/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Chains in a symmetric relation of positive measure

Let `μ` be a probability measure on `X` and let `A ⊆ X × X` be measurable and *symmetric*, that
is `Prod.swap ⁻¹' A = A`.  If `A` has positive measure for `μ ⊗ μ`, then an independent tuple
`(y 0, …, y n)` has positive probability of being an `A`-chain, `(y j, y (j + 1)) ∈ A` for all
`j < n`.  The contrapositive is `MeasureTheory.prod_eq_zero_of_pi_chainSet_eq_zero`.

## Main definitions

* `MeasureTheory.chainSet A n`: the event that `(y 0, …, y n)` is an `A`-chain.
* `MeasureTheory.chainFun μ A n`: the `n`-th iterate at `1` of the transfer operator
  `f ↦ fun x ↦ ∫⁻ y, 1_A (x, y) * f y ∂μ` of `A`.
* `MeasureTheory.chainMeasure μ A n`: its total mass `∫⁻ x, chainFun μ A n x ∂μ`.

## Main results

* `MeasureTheory.pi_chainSet`: `chainMeasure μ A n` is the probability of `chainSet A n`.
* `MeasureTheory.prod_eq_zero_of_pi_chainSet_eq_zero`: a symmetric relation with a null chain
  event of some length is `μ ⊗ μ`-null.
* `MeasureTheory.pi_chainSet_one_eq_zero_of_pi_chainSet_eq_zero`: the same statement with both
  events written as products.
* `MeasureTheory.prod_eq_zero_of_pi_chain_eq_zero`: the same statement for a chain of length
  four, with the chain event written out.

## Implementation notes

Symmetry of `A` makes the transfer operator self-adjoint for the pairing `⟨f, g⟩ = ∫⁻ f * g ∂μ`,
so `⟨chainFun μ A m, chainFun μ A k⟩` depends only on `m + k`
(`MeasureTheory.lintegral_chainFun_mul`); in particular `chainMeasure μ A (2 * m)` is
`∫⁻ (chainFun μ A m) ^ 2`, and therefore a vanishing chain probability at `2 * m` forces one at
`m`.  Since `chainMeasure μ A` is antitone and `chainMeasure μ A 1 = (μ ⊗ μ) A`, halving from
`2 ^ n` down to `1` proves the theorem.

Turning `Measure.pi (fun _ : Fin (n + 1) ↦ μ)` into an iterated integral is done one coordinate
at a time, by `MeasureTheory.measurePreserving_finCons` and Tonelli's theorem.
-/

@[expose] public section

open Set

open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-! ### Prepending a coordinate to a finite product of copies of a measure -/

section Cons

variable (μ : Measure X) [SigmaFinite μ]

/-- **Prepending a coordinate.**  `Fin.cons` pushes `μ ⊗ μ^n` forward to `μ^{n + 1}`. -/
theorem measurePreserving_finCons {n : ℕ} :
    MeasurePreserving (fun p : X × (Fin n → X) ↦ Fin.cons p.1 p.2)
      (μ.prod (Measure.pi fun _ : Fin n ↦ μ)) (Measure.pi fun _ : Fin (n + 1) ↦ μ) := by
  have hmeas : Measurable fun p : X × (Fin n → X) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → X) :=
    Measurable.of_eval fun i ↦ by
      induction i using Fin.cases with
      | zero => simpa using measurable_fst
      | succ j => simpa [Function.comp_def] using (measurable_pi_apply j).comp measurable_snd
  refine ⟨hmeas, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  have hpre : (fun p : X × (Fin n → X) ↦ (Fin.cons p.1 p.2 : Fin (n + 1) → X)) ⁻¹' univ.pi s
      = s 0 ×ˢ univ.pi fun i ↦ s i.succ := by
    ext p
    simp [Fin.forall_fin_succ]
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod, Measure.pi_pi,
    Fin.prod_univ_succ]

/-- **Tonelli's theorem for one coordinate of a finite product.** -/
theorem lintegral_pi_fin_succ {n : ℕ} {f : (Fin (n + 1) → X) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(Measure.pi fun _ : Fin (n + 1) ↦ μ)
      = ∫⁻ x, ∫⁻ w, f (Fin.cons x w) ∂(Measure.pi fun _ : Fin n ↦ μ) ∂μ := by
  rw [← (measurePreserving_finCons μ).lintegral_comp hf,
    lintegral_prod (fun p : X × (Fin n → X) ↦ f (Fin.cons p.1 p.2))
      (hf.comp (measurePreserving_finCons μ).measurable).aemeasurable]

end Cons

/-! ### The chain event and the transfer operator -/

/-- The `n`-step chain event of a relation `A ⊆ X × X`: the set of tuples `(y 0, …, y n)` with
`(y j, y (j + 1)) ∈ A` for every `j < n`. -/
def chainSet (A : Set (X × X)) (n : ℕ) : Set (Fin (n + 1) → X) :=
  {y | ∀ j : Fin n, (y j.castSucc, y j.succ) ∈ A}

/-- The `n`-th iterate at the constant function `1` of the transfer operator
`f ↦ fun x ↦ ∫⁻ y, 1_A (x, y) * f y ∂μ` of a relation `A ⊆ X × X`.  Equivalently,
`chainFun μ A n x` is the probability that a `μ`-independent tuple `(y 1, …, y n)` continues `x`
to an `A`-chain. -/
noncomputable def chainFun (μ : Measure X) (A : Set (X × X)) : ℕ → X → ℝ≥0∞
  | 0 => 1
  | n + 1 => fun x ↦ ∫⁻ y, A.indicator 1 (x, y) * chainFun μ A n y ∂μ

/-- The probability that a `μ`-independent tuple `(y 0, …, y n)` is an `A`-chain; see
`MeasureTheory.pi_chainSet`. -/
noncomputable def chainMeasure (μ : Measure X) (A : Set (X × X)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, chainFun μ A n x ∂μ

variable {μ : Measure X} {A : Set (X × X)}

omit [MeasurableSpace X] in
@[simp] lemma chainSet_zero (A : Set (X × X)) : chainSet A 0 = univ := by
  ext y; simp [chainSet]

omit [MeasurableSpace X] in
lemma mem_chainSet_iff {n : ℕ} {y : Fin (n + 1) → X} :
    y ∈ chainSet A n ↔ ∀ j : Fin n, (y j.castSucc, y j.succ) ∈ A := Iff.rfl

omit [MeasurableSpace X] in
/-- A tuple of length `n + 2` is an `A`-chain iff its first bond lies in `A` and its tail is an
`A`-chain. -/
lemma finCons_mem_chainSet_succ {n : ℕ} (x : X) (w : Fin (n + 1) → X) :
    Fin.cons x w ∈ chainSet A (n + 1) ↔ (x, w 0) ∈ A ∧ w ∈ chainSet A n := by
  simp only [chainSet, mem_ofPred_eq, Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.castSucc_succ, Fin.cons_succ]

lemma measurableSet_chainSet (hA : MeasurableSet A) (n : ℕ) : MeasurableSet (chainSet A n) := by
  have : chainSet A n = ⋂ j : Fin n, {y : Fin (n + 1) → X | (y j.castSucc, y j.succ) ∈ A} := by
    ext y; simp [chainSet]
  rw [this]
  exact MeasurableSet.iInter fun j ↦
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _)) hA

@[simp] lemma chainFun_zero (μ : Measure X) (A : Set (X × X)) :
    chainFun μ A 0 = (1 : X → ℝ≥0∞) := rfl

lemma chainFun_succ_apply (μ : Measure X) (A : Set (X × X)) (n : ℕ) (x : X) :
    chainFun μ A (n + 1) x = ∫⁻ y, A.indicator 1 (x, y) * chainFun μ A n y ∂μ := rfl

lemma chainMeasure_eq_lintegral (μ : Measure X) (A : Set (X × X)) (n : ℕ) :
    chainMeasure μ A n = ∫⁻ x, chainFun μ A n x ∂μ := rfl

private lemma measurable_indicator_prod (hA : MeasurableSet A) :
    Measurable (A.indicator (1 : X × X → ℝ≥0∞)) := measurable_one.indicator hA

lemma measurable_chainFun [SFinite μ] (hA : MeasurableSet A) (n : ℕ) :
    Measurable (chainFun μ A n) := by
  induction n with
  | zero => simpa using measurable_one
  | succ n ih =>
      change Measurable fun x ↦
        ∫⁻ y, A.indicator (1 : X × X → ℝ≥0∞) (x, y) * chainFun μ A n y ∂μ
      exact Measurable.lintegral_prod_right
        ((measurable_indicator_prod hA).mul (ih.comp measurable_snd))

omit [MeasurableSpace X] in
/-- Symmetry of `A`, in the pointwise form used below. -/
private lemma indicator_symm (hsymm : Prod.swap ⁻¹' A = A) (x y : X) :
    A.indicator (1 : X × X → ℝ≥0∞) (x, y) = A.indicator (1 : X × X → ℝ≥0∞) (y, x) := by
  have hiff : ((y, x) ∈ A) ↔ ((x, y) ∈ A) := Set.ext_iff.mp hsymm (x, y)
  by_cases hxy : (x, y) ∈ A
  · simp [hxy, hiff.mpr hxy]
  · have hyx : (y, x) ∉ A := fun hh ↦ hxy (hiff.mp hh)
    simp [hxy, hyx]

/-! ### Self-adjointness of the transfer operator -/

/-- **The transfer operator of a symmetric relation is self-adjoint** for the pairing
`⟨f, g⟩ = ∫⁻ f * g ∂μ`: moving one step from the left factor to the right factor does not change
the pairing of two iterates. -/
theorem lintegral_chainFun_succ_mul [SFinite μ] (hA : MeasurableSet A)
    (hsymm : Prod.swap ⁻¹' A = A) (m k : ℕ) :
    ∫⁻ x, chainFun μ A (m + 1) x * chainFun μ A k x ∂μ
      = ∫⁻ x, chainFun μ A m x * chainFun μ A (k + 1) x ∂μ := by
  have hind := measurable_indicator_prod hA
  calc ∫⁻ x, chainFun μ A (m + 1) x * chainFun μ A k x ∂μ
      = ∫⁻ x, ∫⁻ y, A.indicator (1 : X × X → ℝ≥0∞) (x, y) * chainFun μ A m y
          * chainFun μ A k x ∂μ ∂μ := by
        refine lintegral_congr fun x ↦ ?_
        rw [chainFun_succ_apply, ← lintegral_mul_const
          (f := fun y ↦ A.indicator (1 : X × X → ℝ≥0∞) (x, y) * chainFun μ A m y) _
          ((hind.comp measurable_prodMk_left).mul (measurable_chainFun hA m))]
    _ = ∫⁻ y, ∫⁻ x, A.indicator (1 : X × X → ℝ≥0∞) (x, y) * chainFun μ A m y
          * chainFun μ A k x ∂μ ∂μ :=
        lintegral_lintegral_swap
          ((hind.mul ((measurable_chainFun hA m).comp measurable_snd)).mul
            ((measurable_chainFun hA k).comp measurable_fst)).aemeasurable
    _ = ∫⁻ y, chainFun μ A m y * chainFun μ A (k + 1) y ∂μ := by
        refine lintegral_congr fun y ↦ ?_
        rw [chainFun_succ_apply, ← lintegral_const_mul
          (f := fun z ↦ A.indicator (1 : X × X → ℝ≥0∞) (y, z) * chainFun μ A k z) _
          ((hind.comp measurable_prodMk_left).mul (measurable_chainFun hA k))]
        exact lintegral_congr fun x ↦ by rw [indicator_symm hsymm x y]; ring

/-- **The pairing of two iterates depends only on the total number of steps.** -/
theorem lintegral_chainFun_mul [SFinite μ] (hA : MeasurableSet A) (hsymm : Prod.swap ⁻¹' A = A) :
    ∀ (m k : ℕ), ∫⁻ x, chainFun μ A m x * chainFun μ A k x ∂μ = chainMeasure μ A (m + k) := by
  intro m
  induction m with
  | zero => intro k; simp [chainMeasure_eq_lintegral]
  | succ m ih =>
      intro k
      rw [lintegral_chainFun_succ_mul hA hsymm m k, ih (k + 1)]
      congr 1
      omega

theorem chainMeasure_two_mul [SFinite μ] (hA : MeasurableSet A) (hsymm : Prod.swap ⁻¹' A = A)
    (m : ℕ) :
    chainMeasure μ A (2 * m) = ∫⁻ x, chainFun μ A m x * chainFun μ A m x ∂μ := by
  rw [lintegral_chainFun_mul hA hsymm m m]
  congr 1
  omega

/-- **Halving.**  If no chain of length `2 * m` exists, then none of length `m` does. -/
theorem chainMeasure_eq_zero_of_two_mul [SFinite μ] (hA : MeasurableSet A)
    (hsymm : Prod.swap ⁻¹' A = A) {m : ℕ} (h : chainMeasure μ A (2 * m) = 0) :
    chainMeasure μ A m = 0 := by
  rw [chainMeasure_two_mul hA hsymm m] at h
  have h0 := (lintegral_eq_zero_iff
    ((measurable_chainFun hA m).mul (measurable_chainFun hA m))).mp h
  rw [chainMeasure_eq_lintegral, lintegral_eq_zero_iff (measurable_chainFun hA m)]
  filter_upwards [h0] with x hx
  simpa [mul_self_eq_zero] using hx

/-- Longer chains are less likely. -/
theorem chainMeasure_antitone [IsProbabilityMeasure μ] :
    Antitone (chainMeasure μ A) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  have hle : ∀ x, chainFun μ A (n + 1) x ≤ chainMeasure μ A n := by
    intro x
    rw [chainFun_succ_apply, chainMeasure_eq_lintegral]
    refine lintegral_mono fun y ↦ ?_
    by_cases h : (x, y) ∈ A <;> simp [h]
  calc chainMeasure μ A (n + 1) = ∫⁻ x, chainFun μ A (n + 1) x ∂μ := rfl
    _ ≤ ∫⁻ _, chainMeasure μ A n ∂μ := lintegral_mono hle
    _ = chainMeasure μ A n := by simp

/-! ### The chain probability -/

/-- The bridge between the product measure and the transfer operator, in the form needed for the
induction: the integral of a function of the first coordinate against the chain event. -/
private lemma lintegral_pi_indicator_chainSet [IsProbabilityMeasure μ] (hA : MeasurableSet A) :
    ∀ (n : ℕ) (v : X → ℝ≥0∞), Measurable v →
      ∫⁻ z, v (z 0) * (chainSet A n).indicator 1 z ∂(Measure.pi fun _ : Fin (n + 1) ↦ μ)
        = ∫⁻ x, v x * chainFun μ A n x ∂μ := by
  intro n
  induction n with
  | zero =>
      intro v hv
      rw [lintegral_pi_fin_succ μ
        (f := fun z : Fin (0 + 1) → X ↦ v (z 0) * (chainSet A 0).indicator 1 z)
        ((hv.comp (measurable_pi_apply 0)).mul
          (measurable_one.indicator (measurableSet_chainSet hA 0)))]
      simp
  | succ n ih =>
      intro v hv
      rw [lintegral_pi_fin_succ μ
        (f := fun z : Fin (n + 1 + 1) → X ↦ v (z 0) * (chainSet A (n + 1)).indicator 1 z)
        ((hv.comp (measurable_pi_apply 0)).mul
          (measurable_one.indicator (measurableSet_chainSet hA (n + 1))))]
      refine lintegral_congr fun x ↦ ?_
      have hint : ∀ w : Fin (n + 1) → X,
          v ((Fin.cons x w : Fin (n + 2) → X) 0) *
              (chainSet A (n + 1)).indicator (1 : (Fin (n + 2) → X) → ℝ≥0∞) (Fin.cons x w)
            = v x * (A.indicator (1 : X × X → ℝ≥0∞) (x, w 0)
                * (chainSet A n).indicator 1 w) := by
        intro w
        rw [Fin.cons_zero]
        congr 1
        by_cases h1 : (x, w 0) ∈ A <;> by_cases h2 : w ∈ chainSet A n <;>
          simp [finCons_mem_chainSet_succ, h1, h2]
      simp_rw [hint]
      rw [lintegral_const_mul (f := fun w : Fin (n + 1) → X ↦
          A.indicator (1 : X × X → ℝ≥0∞) (x, w 0) * (chainSet A n).indicator 1 w) _
        (((measurable_indicator_prod hA).comp
          (measurable_const.prodMk (measurable_pi_apply 0))).mul
          (measurable_one.indicator (measurableSet_chainSet hA n))), chainFun_succ_apply]
      congr 1
      exact ih (fun y ↦ A.indicator 1 (x, y))
        ((measurable_indicator_prod hA).comp measurable_prodMk_left)

/-- **`chainMeasure μ A n` is the probability of the chain event `chainSet A n`.** -/
theorem pi_chainSet [IsProbabilityMeasure μ] (hA : MeasurableSet A) (n : ℕ) :
    Measure.pi (fun _ : Fin (n + 1) ↦ μ) (chainSet A n) = chainMeasure μ A n := by
  rw [← lintegral_indicator_one (measurableSet_chainSet hA n)]
  simpa [chainMeasure_eq_lintegral] using
    lintegral_pi_indicator_chainSet hA n 1 measurable_one

/-- A one-step chain event is the relation itself. -/
theorem chainMeasure_one [SFinite μ] (hA : MeasurableSet A) :
    chainMeasure μ A 1 = (μ.prod μ) A := by
  rw [Measure.prod_apply hA, chainMeasure_eq_lintegral]
  refine lintegral_congr fun x ↦ ?_
  rw [chainFun_succ_apply, ← lintegral_indicator_one (measurable_prodMk_left hA)]
  refine lintegral_congr fun y ↦ ?_
  by_cases h : (x, y) ∈ A <;> simp [h]

/-! ### The main theorem -/

/-- Auxiliary form of the descent: if some `chainMeasure μ A (2 ^ j)` vanishes, so does
`chainMeasure μ A 1`. -/
private lemma chainMeasure_one_eq_zero_of_pow [SFinite μ] (hA : MeasurableSet A)
    (hsymm : Prod.swap ⁻¹' A = A) :
    ∀ j : ℕ, chainMeasure μ A (2 ^ j) = 0 → chainMeasure μ A 1 = 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      intro hj
      refine ih (chainMeasure_eq_zero_of_two_mul hA hsymm ?_)
      rwa [← pow_succ']

/-- **A symmetric relation of positive measure has chains of every length.**  Let `μ` be a
probability measure on `X` and `A ⊆ X × X` a measurable set invariant under `Prod.swap`.  If the
`μ`-probability that `(y 0, y 1), …, (y (n-1), y n)` all lie in `A` vanishes for some `n ≠ 0`,
then `(μ ⊗ μ) A = 0`. -/
theorem prod_eq_zero_of_pi_chainSet_eq_zero (μ : Measure X) [IsProbabilityMeasure μ]
    {A : Set (X × X)} (hA : MeasurableSet A) (hsymm : Prod.swap ⁻¹' A = A) {n : ℕ} (hn : n ≠ 0)
    (h : Measure.pi (fun _ : Fin (n + 1) ↦ μ) (chainSet A n) = 0) :
    (μ.prod μ) A = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pi_chainSet hA] at h
  have hpow : chainMeasure μ A (2 ^ (m + 1)) = 0 := by
    refine le_antisymm ?_ (by simp)
    calc chainMeasure μ A (2 ^ (m + 1))
        ≤ chainMeasure μ A (m + 1) := chainMeasure_antitone (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 0 := h
  rw [← chainMeasure_one hA]
  exact chainMeasure_one_eq_zero_of_pow hA hsymm (m + 1) hpow

/-- **A symmetric relation with a null chain event has a null one-step chain event.**  The
`Measure.pi` form of `MeasureTheory.prod_eq_zero_of_pi_chainSet_eq_zero`. -/
theorem pi_chainSet_one_eq_zero_of_pi_chainSet_eq_zero (μ : Measure X) [IsProbabilityMeasure μ]
    {A : Set (X × X)} (hA : MeasurableSet A) (hsymm : Prod.swap ⁻¹' A = A) {n : ℕ} (hn : n ≠ 0)
    (h : Measure.pi (fun _ : Fin (n + 1) ↦ μ) (chainSet A n) = 0) :
    Measure.pi (fun _ : Fin 2 ↦ μ) (chainSet A 1) = 0 := by
  rw [pi_chainSet hA, chainMeasure_one hA]
  exact prod_eq_zero_of_pi_chainSet_eq_zero μ hA hsymm hn h

omit [MeasurableSpace X] in
/-- The four-step chain event, spelled out. -/
lemma chainSet_four (A : Set (X × X)) :
    chainSet A 4
      = {y : Fin 5 → X | (y 0, y 1) ∈ A ∧ (y 1, y 2) ∈ A ∧ (y 2, y 3) ∈ A ∧ (y 3, y 4) ∈ A} := by
  ext y
  constructor
  · exact fun hy ↦ ⟨hy 0, hy 1, hy 2, hy 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    exacts [h0, h1, h2, h3]

/-- **A symmetric relation of positive measure has chains of every length**, spelled out for
chains of length four. -/
theorem prod_eq_zero_of_pi_chain_eq_zero (μ : Measure X) [IsProbabilityMeasure μ]
    {A : Set (X × X)} (hA : MeasurableSet A) (hsymm : Prod.swap ⁻¹' A = A)
    (h : Measure.pi (fun _ : Fin 5 ↦ μ)
        {y | (y 0, y 1) ∈ A ∧ (y 1, y 2) ∈ A ∧ (y 2, y 3) ∈ A ∧ (y 3, y 4) ∈ A} = 0) :
    (μ.prod μ) A = 0 :=
  prod_eq_zero_of_pi_chainSet_eq_zero μ hA hsymm (n := 4) (by norm_num)
    (by rw [chainSet_four]; exact h)

end MeasureTheory


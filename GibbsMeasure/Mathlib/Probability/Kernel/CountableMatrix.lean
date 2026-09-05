/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Comp

/-!
# Kernels on a countable space as (possibly infinite) matrices

On a countable measurable space `α` with measurable singletons, a kernel `κ : Kernel α β` is
determined by the entries `κ a {b}`, and a function `Q : α → α → ℝ≥0∞` — a matrix on `α`, of any
cardinality — determines the kernel `ofMatrix Q` with density `Q a` with respect to counting
measure: `ofMatrix Q a = Measure.count.withDensity (Q a)`.

Kernel composition `η ∘ₖ κ` is then matrix multiplication with a `tsum` in place of the finite
sum of `Matrix.mul` (`comp_apply_eq_tsum`, `ofMatrix_comp_ofMatrix`), and the powers `κ ^ n` in
the monoid `Kernel α α` are the matrix powers (`pow_succ_apply_eq_tsum`). Row vectors act by
`Measure.bind` (`bind_ofMatrix_apply_singleton`), column vectors by `∫⁻` (`lintegral_ofMatrix`).

## Main declarations

* `MeasureTheory.Measure.pi_count`: the finite product of counting measures is counting measure.
* `ProbabilityTheory.Kernel.ext_of_singleton`, `comp_apply_eq_tsum`, `pow_succ_apply_eq_tsum`,
  `pow_succ'_apply_eq_tsum`: kernels on a countable space are matrices.
* `ProbabilityTheory.Kernel.isSFiniteKernel_of_countable`: a kernel on a countable space with
  s-finite values is s-finite.
* `ProbabilityTheory.Kernel.ofMatrix` and its API.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The finite product of counting measures on countable spaces is counting measure. -/
theorem pi_count {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, Countable (X i)] [∀ i, MeasurableSingletonClass (X i)] :
    Measure.pi (fun i ↦ (count : Measure (X i))) = count := by
  refine ext_of_singleton fun x ↦ ?_
  rw [pi_singleton, count_singleton]
  simp

theorem count_withDensity_apply_singleton (f : α → ℝ≥0∞) (a : α) :
    count.withDensity f {a} = f a := by
  rw [withDensity_apply _ (measurableSet_singleton a), lintegral_singleton, count_singleton,
    mul_one]

/-- Integration against a measure with density `f` with respect to counting measure. -/
theorem lintegral_count_withDensity [Countable α] (f g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂count.withDensity f = ∑' a, f a * g a := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_count]
  rfl

/-- Every measure on a countable space with measurable singletons has a density with respect
to counting measure, namely its singleton values. -/
theorem eq_count_withDensity [Countable α] (μ : Measure α) :
    μ = count.withDensity fun a ↦ μ {a} :=
  ext_of_singleton fun a ↦ by rw [count_withDensity_apply_singleton]

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Two kernels into a countable space with measurable singletons agree if their entries
`κ a {b}` agree. -/
theorem ext_of_singleton [Countable β] [MeasurableSingletonClass β] {κ η : Kernel α β}
    (h : ∀ a b, κ a {b} = η a {b}) : κ = η :=
  Kernel.ext fun a ↦ Measure.ext_of_singleton (h a)

/-- Composition of kernels through a countable space is matrix multiplication:
`(η ∘ₖ κ) a s = ∑' b, κ a {b} * η b s`. -/
theorem comp_apply_eq_tsum [Countable β] [MeasurableSingletonClass β] (η : Kernel β γ)
    (κ : Kernel α β) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    (η ∘ₖ κ) a s = ∑' b, κ a {b} * η b s := by
  rw [comp_apply' _ _ _ hs, lintegral_countable']
  simp_rw [mul_comm]

/-- Integration against a composite kernel through a countable space. -/
theorem lintegral_comp_eq_tsum [Countable β] [MeasurableSingletonClass β] (η : Kernel β γ)
    (κ : Kernel α β) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂(η ∘ₖ κ) a = ∑' b, κ a {b} * ∫⁻ c, g c ∂η b := by
  rw [lintegral_comp _ _ _ hg, lintegral_countable']
  simp_rw [mul_comm]

variable [Countable α] [MeasurableSingletonClass α]

/-- Powers of a kernel on a countable space are matrix powers:
`κ^(n+1) a s = ∑' b, κ a {b} * κ^n b s`. -/
theorem pow_succ_apply_eq_tsum (κ : Kernel α α) (n : ℕ) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (n + 1)) a s = ∑' b, κ a {b} * (κ ^ n) b s := by
  rw [pow_succ]
  exact comp_apply_eq_tsum _ _ _ hs

/-- Powers of a kernel on a countable space are matrix powers:
`κ^(n+1) a s = ∑' b, κ^n a {b} * κ b s`. -/
theorem pow_succ'_apply_eq_tsum (κ : Kernel α α) (n : ℕ) (a : α) {s : Set α}
    (hs : MeasurableSet s) :
    (κ ^ (n + 1)) a s = ∑' b, (κ ^ n) a {b} * κ b s := by
  rw [pow_succ']
  exact comp_apply_eq_tsum _ _ _ hs

omit [Countable α] in
@[simp] theorem pow_zero_apply_singleton (κ : Kernel α α) (a b : α) :
    (κ ^ 0) a {b} = ({b} : Set α).indicator 1 a := by
  rw [pow_zero]
  change Kernel.id a {b} = _
  rw [id_apply, Measure.dirac_apply' _ (measurableSet_singleton b)]

/-- A kernel on a countable space whose values are s-finite measures is an s-finite kernel. -/
theorem isSFiniteKernel_of_countable (κ : Kernel α β) [∀ a, SFinite (κ a)] :
    IsSFiniteKernel κ := by
  classical
  let κs : α × ℕ → Kernel α β := fun p ↦
    ofFunOfCountable fun a ↦ if a = p.1 then sfiniteSeq (κ p.1) p.2 else 0
  have hκs : ∀ p, κs p = ofFunOfCountable fun a ↦
      if a = p.1 then sfiniteSeq (κ p.1) p.2 else 0 := fun _ ↦ rfl
  have hfin : ∀ p, IsFiniteKernel (κs p) := fun p ↦
    ⟨⟨sfiniteSeq (κ p.1) p.2 Set.univ, measure_lt_top _ _, fun a ↦ by
      change (if a = p.1 then sfiniteSeq (κ p.1) p.2 else 0) Set.univ ≤ _
      split_ifs with h
      · subst h; exact le_rfl
      · simp⟩⟩
  have hsum : κ = Kernel.sum κs := by
    ext a s hs
    rw [sum_apply' _ _ hs]
    refine (?_ : (κ a) s = ∑' a₀ : α, ∑' n : ℕ, ((κs (a₀, n)) a) s).trans
      (ENNReal.tsum_prod (f := fun a₀ n ↦ ((κs (a₀, n)) a) s)).symm
    rw [tsum_eq_single a fun a' ha' ↦ ?_]
    · change (κ a) s = ∑' n : ℕ, (if a = a then sfiniteSeq (κ a) n else 0) s
      simp only [ite_true]
      rw [← Measure.sum_apply _ hs, sum_sfiniteSeq]
    · change ∑' n : ℕ, (if a = a' then sfiniteSeq (κ a') n else 0) s = 0
      simp [Ne.symm ha']
  rw [hsum]
  have : ∀ p, IsSFiniteKernel (κs p) := fun p ↦ by
    have := hfin p
    infer_instance
  infer_instance

/-! ### The kernel of a matrix on a countable space -/

section OfMatrix

variable (Q : α → α → ℝ≥0∞)

/-- The kernel on a countable space `α` with density `Q a` with respect to counting measure:
the (possibly infinite) matrix `Q` acting on `α`, `ofMatrix Q a {b} = Q a b`. -/
noncomputable def ofMatrix : Kernel α α :=
  ofFunOfCountable fun a ↦ Measure.count.withDensity (Q a)

@[simp] theorem ofMatrix_apply (a : α) : ofMatrix Q a = Measure.count.withDensity (Q a) := rfl

@[simp] theorem ofMatrix_apply_singleton (a b : α) : ofMatrix Q a {b} = Q a b := by
  rw [ofMatrix_apply, Measure.count_withDensity_apply_singleton]

theorem ofMatrix_apply_set (a : α) (s : Set α) : ofMatrix Q a s = ∑' b : s, Q a b := by
  rw [ofMatrix_apply, withDensity_apply', lintegral_countable _ s.to_countable]
  simp

theorem ofMatrix_apply_univ (a : α) : ofMatrix Q a Set.univ = ∑' b, Q a b := by
  rw [ofMatrix_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_count]

/-- Column vectors act on `ofMatrix Q` by integration: `(Q r)(a) = ∫⁻ b, r b ∂ofMatrix Q a`. -/
theorem lintegral_ofMatrix (a : α) (f : α → ℝ≥0∞) :
    ∫⁻ b, f b ∂ofMatrix Q a = ∑' b, Q a b * f b := by
  rw [ofMatrix_apply, lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_count]
  rfl

/-- Row vectors act on `ofMatrix Q` by `Measure.bind`: `(ℓ Q)(b) = ∑' a, ℓ a * Q a b`. -/
theorem bind_ofMatrix_apply_singleton (μ : Measure α) (b : α) :
    (μ.bind (ofMatrix Q)) {b} = ∑' a, μ {a} * Q a b := by
  rw [Measure.bind_apply (measurableSet_singleton b) (ofMatrix Q).measurable.aemeasurable,
    lintegral_countable']
  simp_rw [ofMatrix_apply_singleton, mul_comm]

theorem count_withDensity_bind_ofMatrix (ℓ : α → ℝ≥0∞) :
    (Measure.count.withDensity ℓ).bind (ofMatrix Q)
      = Measure.count.withDensity fun b ↦ ∑' a, ℓ a * Q a b :=
  Measure.ext_of_singleton fun b ↦ by
    rw [bind_ofMatrix_apply_singleton, Measure.count_withDensity_apply_singleton]
    simp_rw [Measure.count_withDensity_apply_singleton]

/-- Composition of matrix kernels is matrix multiplication (with the `tsum` of a countable
index): `ofMatrix Q ∘ₖ ofMatrix P` first applies `P`, then `Q`. -/
theorem ofMatrix_comp_ofMatrix (P : α → α → ℝ≥0∞) :
    ofMatrix Q ∘ₖ ofMatrix P = ofMatrix fun a c ↦ ∑' b, P a b * Q b c :=
  ext_of_singleton fun a c ↦ by
    rw [comp_apply_eq_tsum _ _ _ (measurableSet_singleton c), ofMatrix_apply_singleton]
    simp_rw [ofMatrix_apply_singleton]

theorem ofMatrix_pow_succ_apply_singleton (n : ℕ) (a c : α) :
    (ofMatrix Q ^ (n + 1)) a {c} = ∑' b, Q a b * (ofMatrix Q ^ n) b {c} := by
  rw [pow_succ_apply_eq_tsum _ _ _ (measurableSet_singleton c)]
  simp_rw [ofMatrix_apply_singleton]

theorem ofMatrix_pow_succ'_apply_singleton (n : ℕ) (a c : α) :
    (ofMatrix Q ^ (n + 1)) a {c} = ∑' b, (ofMatrix Q ^ n) a {b} * Q b c := by
  rw [pow_succ'_apply_eq_tsum _ _ _ (measurableSet_singleton c)]
  simp_rw [ofMatrix_apply_singleton]

@[simp] theorem ofMatrix_pow_one_apply_singleton (a b : α) :
    (ofMatrix Q ^ 1) a {b} = Q a b := by
  rw [pow_one, ofMatrix_apply_singleton]

theorem ofMatrix_pow_two_apply_singleton (a c : α) :
    (ofMatrix Q ^ 2) a {c} = ∑' b, Q a b * Q b c := by
  rw [ofMatrix_pow_succ_apply_singleton]
  simp_rw [ofMatrix_pow_one_apply_singleton]

instance isSFiniteKernel_ofMatrix : IsSFiniteKernel (ofMatrix Q) :=
  isSFiniteKernel_of_countable _

/-- `ofMatrix Q` is a Markov kernel iff `Q` is a stochastic matrix. -/
theorem isMarkovKernel_ofMatrix_iff : IsMarkovKernel (ofMatrix Q) ↔ ∀ a, ∑' b, Q a b = 1 := by
  constructor
  · intro h a
    rw [← ofMatrix_apply_univ]
    exact measure_univ
  · intro h
    exact ⟨fun a ↦ ⟨by rw [ofMatrix_apply_univ, h]⟩⟩

theorem isMarkovKernel_ofMatrix (h : ∀ a, ∑' b, Q a b = 1) : IsMarkovKernel (ofMatrix Q) :=
  (isMarkovKernel_ofMatrix_iff Q).2 h

/-- Every kernel on a countable space is the kernel of its matrix of entries. -/
theorem ofMatrix_entries (κ : Kernel α α) : ofMatrix (fun a b ↦ κ a {b}) = κ :=
  ext_of_singleton fun a b ↦ by rw [ofMatrix_apply_singleton]

/-- On a finite space, a matrix with finite entries gives a finite kernel. -/
theorem isFiniteKernel_ofMatrix [Finite α] (hQ : ∀ a b, Q a b ≠ ⊤) :
    IsFiniteKernel (ofMatrix Q) := by
  cases nonempty_fintype α
  refine ⟨⟨∑ a, ∑ b, Q a b, ENNReal.sum_lt_top.2 fun a _ ↦ ENNReal.sum_lt_top.2 fun b _ ↦
    (hQ a b).lt_top, fun a ↦ ?_⟩⟩
  rw [ofMatrix_apply_univ, tsum_fintype]
  exact Finset.single_le_sum (f := fun a ↦ ∑ b, Q a b) (fun _ _ ↦ zero_le) (Finset.mem_univ a)

end OfMatrix

/-- Powers of a finite kernel are finite. -/
theorem isFiniteKernel_pow {α : Type*} {mα : MeasurableSpace α} (κ : Kernel α α)
    [IsFiniteKernel κ] : ∀ n, IsFiniteKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsFiniteKernel (Kernel.id : Kernel α α))
  | n + 1 => by
    rw [pow_succ]
    have := isFiniteKernel_pow κ n
    exact (inferInstance : IsFiniteKernel ((κ ^ n) ∘ₖ κ))

/-- Supermultiplicativity of the diagonal of kernel powers on a countable space, Georgii's
remark after (11.6): `κ^m(x, {x}) κ^n(x, {x}) ≤ κ^{m+n}(x, {x})`. -/
lemma pow_apply_singleton_mul_le {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] (κ : Kernel E E) (m n : ℕ)
    (x : E) : (κ ^ m) x {x} * (κ ^ n) x {x} ≤ (κ ^ (m + n)) x {x} := by
  rw [pow_add]
  change (κ ^ m) x {x} * (κ ^ n) x {x} ≤ ((κ ^ m) ∘ₖ (κ ^ n)) x {x}
  rw [comp_apply_eq_tsum _ _ _ (measurableSet_singleton x), mul_comm]
  exact ENNReal.le_tsum x

lemma pow_le_pow_mul_apply_singleton {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] (κ : Kernel E E) (k n : ℕ)
    (x : E) : (κ ^ n) x {x} ^ k ≤ (κ ^ (k * n)) x {x} := by
  induction k with
  | zero =>
    rw [Nat.zero_mul, Kernel.pow_zero_apply_singleton, pow_zero,
      Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply]
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (mul_le_mul' ih le_rfl).trans (κ.pow_apply_singleton_mul_le _ _ x)

end ProbabilityTheory.Kernel

/-! ### Lazy matrices `tP + (1 - t)I` -/

namespace ProbabilityTheory.Kernel

variable {α : Type*}

/-- The lazy matrix `Q = tP + (1 - t)I` of a matrix `P`: with probability `t` move according to
`P`, otherwise stay put. -/
noncomputable def lazy (P : α → α → ℝ≥0∞) (t : ℝ≥0∞) (x y : α) : ℝ≥0∞ :=
  t * P x y + (1 - t) * ({y} : Set α).indicator 1 x

variable {P : α → α → ℝ≥0∞} {t : ℝ≥0∞}

lemma lazy_pos (hpos : ∀ x y, 0 < P x y) (ht : t ≠ 0) (x y : α) : 0 < lazy P t x y :=
  add_pos_of_left (ENNReal.mul_pos ht (hpos x y).ne') _

/-- `inf_x Q(x, x) ≥ 1 - t` for `Q = tP + (1 - t)I`. -/
lemma le_lazy_apply_self (x : α) : 1 - t ≤ lazy P t x x := by
  simp [lazy]

/-- `Q = tP + (1 - t)I` is stochastic when `P` is and `t ≤ 1`. -/
lemma lazy_stochastic (hP : ∀ x, ∑' y, P x y = 1) (ht : t ≤ 1) (x : α) :
    ∑' y, lazy P t x y = 1 := by
  simp only [lazy]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hP,
    tsum_eq_single x fun y hy ↦ by simp [Ne.symm hy]]
  simp [add_tsub_cancel_of_le ht]

/-- An invariant vector of `P` is invariant for `Q = tP + (1 - t)I`. -/
lemma tsum_mul_lazy {v : α → ℝ≥0∞} (hvP : ∀ y, ∑' x, v x * P x y = v y) (ht : t ≤ 1) (y : α) :
    ∑' x, v x * lazy P t x y = v y := by
  simp only [lazy, mul_add]
  rw [ENNReal.tsum_add]
  simp_rw [mul_left_comm (v _) t, mul_left_comm (v _) (1 - t)]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hvP, tsum_eq_single y fun x hx ↦ by simp [hx]]
  simp [← add_mul, add_tsub_cancel_of_le ht]

/-- The binomial formula `Q^n(x, x) = ∑_k C(n,k) t^k (1-t)^{n-k} P^k(x, x)` for the lazy matrix
`Q = tP + (1-t)I`, by induction on `n` via Pascal's rule. -/
theorem ofMatrix_lazy_pow_apply_singleton {E : Type*} [MeasurableSpace E] [Countable E]
    [MeasurableSingletonClass E] (P : E → E → ℝ≥0∞) (t : ℝ≥0∞) (n : ℕ) (a c : E) :
    (Kernel.ofMatrix (lazy P t) ^ n) a {c}
      = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
          * (Kernel.ofMatrix P ^ k) a {c} := by
  induction n generalizing a c with
  | zero =>
    simp
  | succ n ih =>
    rw [Kernel.ofMatrix_pow_succ'_apply_singleton]
    have hrw : ∀ b, (Kernel.ofMatrix (lazy P t) ^ n) a {b} * lazy P t b c
        = ∑ k ∈ Finset.range (n + 1),
            (t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}
              * P b c)
            + (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
                  * (Kernel.ofMatrix P ^ k) a {b}))) := by
      intro b
      rw [ih a b, Finset.sum_mul]
      congr 1
      ext k
      simp only [lazy]
      ring
    simp_rw [hrw]
    rw [Summable.tsum_finsetSum (fun k _ => ENNReal.summable)]
    have hterm : ∀ k, ∑' b,
          (t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}
              * P b c)
            + (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b})))
        = (n.choose k : ℝ≥0∞) * t ^ (k+1) * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ (k+1)) a {c}
          + (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k + 1)
              * (Kernel.ofMatrix P ^ k) a {c} := by
      intro k
      rw [ENNReal.tsum_add]
      congr 1
      · have step : ∀ i, t * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k)
              * (Kernel.ofMatrix P ^ k) a {i} * P i c)
            = (t * (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k))
              * ((Kernel.ofMatrix P ^ k) a {i} * P i c) := by
          intro i; ring
        simp_rw [step, ENNReal.tsum_mul_left,
          ← Kernel.ofMatrix_pow_succ'_apply_singleton P k a c]
        ring
      · have step : ∀ b, (1 - t) * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b
              * ((n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ k) a {b}))
            = ((1 - t) * (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k))
              * (({c} : Set E).indicator (1 : E → ℝ≥0∞) b * (Kernel.ofMatrix P ^ k) a {b}) := by
          intro b; ring
        simp_rw [step, ENNReal.tsum_mul_left]
        have hcol : ∑' b, ({c} : Set E).indicator (1 : E → ℝ≥0∞) b * (Kernel.ofMatrix P ^ k) a {b}
            = (Kernel.ofMatrix P ^ k) a {c} := by
          rw [tsum_eq_single c (fun b hb => by simp [Set.indicator_of_notMem, hb])]
          simp
        rw [hcol]
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    set A := ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ≥0∞) * t ^ (k + 1) * (1 - t) ^ (n - k) * (Kernel.ofMatrix P ^ (k + 1)) a {c}
      with hA
    set B := ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ≥0∞) * t ^ k * (1 - t) ^ (n - k + 1) * (Kernel.ofMatrix P ^ k) a {c}
      with hB
    have hCA : ∀ i ∈ Finset.range (n + 1),
        ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
            * (Kernel.ofMatrix P ^ (i + 1)) a {c}
          = (n.choose i : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c}
            + (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      intro i _
      have hp : ((n + 1).choose (i + 1) : ℝ≥0∞)
          = (n.choose i : ℝ≥0∞) + (n.choose (i + 1) : ℝ≥0∞) := by
        rw [← Nat.cast_add, Nat.choose_succ_succ' n i]
      rw [hp]; ring
    have hCstep : ∑ i ∈ Finset.range (n + 1),
          ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c}
        = A + ∑ i ∈ Finset.range (n + 1),
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      rw [Finset.sum_congr rfl hCA, Finset.sum_add_distrib, hA]
    have hfront : ∑ j ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose j : ℝ≥0∞) * t ^ j * (1 - t) ^ (n + 1 - j) * (Kernel.ofMatrix P ^ j) a {c}
        = (∑ i ∈ Finset.range (n + 1),
              ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n + 1 - (i + 1))
                * (Kernel.ofMatrix P ^ (i + 1)) a {c})
          + ((n + 1).choose 0 : ℝ≥0∞) * t ^ 0 * (1 - t) ^ (n + 1 - 0)
              * (Kernel.ofMatrix P ^ 0) a {c} :=
      Finset.sum_range_succ' _ (n + 1)
    have hexp : ∀ i ∈ Finset.range (n + 1),
        ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n + 1 - (i + 1))
            * (Kernel.ofMatrix P ^ (i + 1)) a {c}
          = ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.1 hi
      have hexp : n + 1 - (i + 1) = n - i := by omega
      rw [hexp]
    rw [Finset.sum_congr rfl hexp] at hfront
    have hf0 : ((n + 1).choose 0 : ℝ≥0∞) * t ^ 0 * (1 - t) ^ (n + 1 - 0)
        * (Kernel.ofMatrix P ^ 0) a {c}
        = (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by simp
    rw [hf0] at hfront
    have hS12 : (∑ i ∈ Finset.range (n + 1),
          (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c})
        = ∑ i ∈ Finset.range n,
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
      rw [Finset.sum_range_succ]
      have hz : (n.choose (n + 1) : ℝ≥0∞) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
      rw [hz]
      ring
    have hBdecomp : B = (∑ i ∈ Finset.range n,
            (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                * (Kernel.ofMatrix P ^ (i + 1)) a {c})
          + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by
      rw [hB, Finset.sum_range_succ']
      have hexp2 : ∀ i ∈ Finset.range n,
          (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - (i + 1) + 1)
              * (Kernel.ofMatrix P ^ (i + 1)) a {c}
            = (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                * (Kernel.ofMatrix P ^ (i + 1)) a {c} := by
        intro i hi
        have hi' : i < n := Finset.mem_range.1 hi
        have he : n - (i + 1) + 1 = n - i := by omega
        rw [he]
      rw [Finset.sum_congr rfl hexp2]
      simp
    calc A + B = A + ((∑ i ∈ Finset.range n,
              (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                  * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c}) := by rw [hBdecomp]
      _ = (A + ∑ i ∈ Finset.range (n + 1),
              (n.choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                  * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by rw [hS12]; ring
      _ = (∑ i ∈ Finset.range (n + 1),
              ((n + 1).choose (i + 1) : ℝ≥0∞) * t ^ (i + 1) * (1 - t) ^ (n - i)
                  * (Kernel.ofMatrix P ^ (i + 1)) a {c})
            + (1 - t) ^ (n + 1) * (Kernel.ofMatrix P ^ 0) a {c} := by rw [← hCstep]
      _ = ∑ j ∈ Finset.range (n + 1 + 1),
            ((n + 1).choose j : ℝ≥0∞) * t ^ j * (1 - t) ^ (n + 1 - j)
                * (Kernel.ofMatrix P ^ j) a {c} := hfront.symm

end ProbabilityTheory.Kernel

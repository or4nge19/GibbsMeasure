/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Probability.Kernel.Irreducible

/-!
# Convergence norm, potential kernel and recurrence of kernels on a countable space

For a kernel `κ` on a countable measurable space with measurable singletons (a possibly infinite
nonnegative matrix), this file studies the growth of the diagonal entries `κ^n x {x}` and the
Green function `∑ₙ κ^n x {y}`.

## Main definitions

* `ProbabilityTheory.Kernel.convergenceNorm κ x`: the convergence norm
  `limsup_n (κ^n x {x})^(1/n)` (Vere-Jones); its inverse is the radius of convergence of the
  power series `∑ₙ κ^n x {x} zⁿ`.
* `ProbabilityTheory.Kernel.potential κ`: the potential (Green) kernel `∑ₙ κ^n`.
* `ProbabilityTheory.Kernel.IsRecurrent κ`, `IsTransient κ`, `IsPositiveRecurrent κ`.

## Main results

* `ProbabilityTheory.Kernel.tendsto_convergenceNorm`: if `κ^n x {x} > 0` for all large `n`,
  the sequence `(κ^n x {x})^(1/n)` converges to `convergenceNorm κ x` (Fekete's lemma for the
  supermultiplicative sequence `κ^n x {x}`).
* `ProbabilityTheory.Kernel.convergenceNorm_eq_of_pow_pos`: the convergence norm does not
  depend on the state on a communicating class; for a strictly positive kernel this is
  `convergenceNorm_eq_of_forall_pos`, and `tendsto_convergenceNorm_of_forall_pos` gives the
  unconditional existence of the limit in that case.
* `ProbabilityTheory.Kernel.tsum_pow_apply_singleton_mul_pow_ne_top`,
  `tsum_pow_apply_singleton_mul_pow_eq_top`: Cauchy–Hadamard for `∑ₙ κ^n x {x} zⁿ`.
* `ProbabilityTheory.Kernel.isRecurrent_or_isTransient`: an irreducible kernel is either
  recurrent (`∑ₙ κ^n x {y} = ∞` for all `x, y`) or transient (`< ∞` for all `x, y`).
* `ProbabilityTheory.Kernel.IsRecurrent.apply_eq_apply_of_lintegral_eq`: a finite harmonic
  function of an irreducible recurrent Markov kernel is constant.
* `ProbabilityTheory.Kernel.eq_of_apply_eq_mul_div_of_isRecurrent`: two Markov kernels related by
  `η x {y} = κ x {y} r y / (q r x)` with equal finite positive convergence norms have the same
  recurrence properties, and coincide if they are recurrent.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} {mα : MeasurableSpace α}

/-! ### The convergence norm -/

/-- The convergence norm of the kernel `κ` at the state `x`: `limsup_n (κ^n x {x})^(1/n)`. Its
inverse is the radius of convergence of the power series `∑ₙ κ^n x {x} zⁿ` (Vere-Jones'
convergence parameter). When `κ^n x {x} > 0` for all large `n`, the `limsup` is a limit
(`tendsto_convergenceNorm`). -/
noncomputable def convergenceNorm (κ : Kernel α α) (x : α) : ℝ≥0∞ :=
  limsup (fun n : ℕ ↦ (κ ^ n) x {x} ^ (n : ℝ)⁻¹) atTop

variable {κ : Kernel α α} {x : α} {t : ℝ≥0∞}

theorem le_convergenceNorm_of_frequently (h : ∃ᶠ n in atTop, t ^ n ≤ (κ ^ n) x {x}) :
    t ≤ convergenceNorm κ x := by
  refine le_limsup_of_frequently_le' ?_
  refine (h.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  rw [ENNReal.le_rpow_inv_iff (Nat.cast_pos.2 hn1), ENNReal.rpow_natCast]
  exact hn

theorem frequently_pow_lt_of_lt_convergenceNorm (h : t < convergenceNorm κ x) :
    ∃ᶠ n in atTop, t ^ n < (κ ^ n) x {x} := by
  refine ((frequently_lt_of_lt_limsup (by isBoundedDefault) h).and_eventually
    (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  rwa [ENNReal.lt_rpow_inv_iff (Nat.cast_pos.2 hn1), ENNReal.rpow_natCast] at hn

theorem eventually_lt_pow_of_convergenceNorm_lt (h : convergenceNorm κ x < t) :
    ∀ᶠ n in atTop, (κ ^ n) x {x} < t ^ n := by
  refine ((eventually_lt_of_limsup_lt h).and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  rwa [ENNReal.rpow_inv_lt_iff (Nat.cast_pos.2 hn1), ENNReal.rpow_natCast] at hn

theorem convergenceNorm_le_of_eventually (h : ∀ᶠ n in atTop, (κ ^ n) x {x} ≤ t ^ n) :
    convergenceNorm κ x ≤ t := by
  refine limsup_le_of_le (by isBoundedDefault) ?_
  refine (h.and (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ ↦ ?_
  rw [ENNReal.rpow_inv_le_iff (Nat.cast_pos.2 hn1), ENNReal.rpow_natCast]
  exact hn

/-- **Cauchy–Hadamard**, convergence half: `∑ₙ κ^n x {x} zⁿ < ∞` for
`z < (convergenceNorm κ x)⁻¹`. -/
theorem tsum_pow_apply_singleton_mul_pow_ne_top_aux {z : ℝ≥0∞}
    (hfin : ∀ n, (κ ^ n) x {x} ≠ ∞) (hz : z < (convergenceNorm κ x)⁻¹) :
    ∑' n, (κ ^ n) x {x} * z ^ n ≠ ∞ := by
  have hz_top : z ≠ ∞ := hz.ne_top
  rw [ENNReal.lt_inv_iff_lt_inv] at hz
  obtain ⟨s, hLs, hsz⟩ := exists_between hz
  have hs0 : s ≠ 0 := (bot_le.trans_lt hLs).ne'
  have hzs : z * s < 1 := by
    have h := ENNReal.lt_inv_iff_lt_inv.1 hsz
    rwa [← one_div, ENNReal.lt_div_iff_mul_lt (Or.inl hs0) (Or.inl hsz.ne_top)] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_lt_pow_of_convergenceNorm_lt hLs)
  rw [← Summable.sum_add_tsum_nat_add' (f := fun n ↦ (κ ^ n) x {x} * z ^ n) (k := N)
    ENNReal.summable]
  refine ENNReal.add_ne_top.2 ⟨(ENNReal.sum_lt_top.2 fun n _ ↦ ?_).ne, ne_top_of_le_ne_top
    (tsum_geometric_lt_top.2 hzs).ne (ENNReal.tsum_le_tsum fun n ↦ ?_)⟩
  · exact ENNReal.mul_lt_top (hfin n).lt_top (ENNReal.pow_lt_top hz_top.lt_top)
  · calc (κ ^ (n + N)) x {x} * z ^ (n + N) ≤ s ^ (n + N) * z ^ (n + N) :=
          mul_le_mul' (hN _ (Nat.le_add_left N n)).le le_rfl
      _ = (z * s) ^ (n + N) := by rw [← mul_pow, mul_comm]
      _ ≤ (z * s) ^ n := pow_le_pow_of_le_one zero_le hzs.le (Nat.le_add_right n N)

/-- **Cauchy–Hadamard**, divergence half: `∑ₙ κ^n x {x} zⁿ = ∞` for
`z > (convergenceNorm κ x)⁻¹`. -/
theorem tsum_pow_apply_singleton_mul_pow_eq_top {z : ℝ≥0∞} (hz : (convergenceNorm κ x)⁻¹ < z) :
    ∑' n, (κ ^ n) x {x} * z ^ n = ∞ := by
  rw [ENNReal.inv_lt_iff_inv_lt] at hz
  obtain ⟨s, hzs, hsL⟩ := exists_between hz
  have h1 : 1 < s * z := by
    have h := hzs
    rwa [← one_div, ENNReal.div_lt_iff (Or.inr one_ne_zero) (Or.inr ENNReal.one_ne_top)] at h
  by_contra h
  have hev : ∀ᶠ n in atTop, (κ ^ n) x {x} * z ^ n < 1 :=
    (tendsto_order.1 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top h)).2 _ zero_lt_one
  obtain ⟨n, hn, hlt⟩ := ((frequently_pow_lt_of_lt_convergenceNorm hsL).and_eventually hev).exists
  refine hlt.not_ge ?_
  calc (1 : ℝ≥0∞) ≤ (s * z) ^ n := one_le_pow₀ h1.le
    _ = s ^ n * z ^ n := mul_pow _ _ _
    _ ≤ (κ ^ n) x {x} * z ^ n := mul_le_mul' hn.le le_rfl

/-! ### Powers of Markov kernels, the potential kernel, recurrence -/

instance isMarkovKernel_pow (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel α α))
  | succ n ih => rw [_root_.pow_succ]; exact IsMarkovKernel.comp (κ ^ n) κ

theorem convergenceNorm_le_one [IsMarkovKernel κ] : convergenceNorm κ x ≤ 1 :=
  convergenceNorm_le_of_eventually (Eventually.of_forall fun n ↦ by rw [one_pow]; exact prob_le_one)

/-- The potential (Green) kernel `∑ₙ κ^n` of `κ`: `potential κ x s` is the expected number of
visits to `s` (time `0` included) of the chain with transition kernel `κ` started at `x`. -/
noncomputable def potential (κ : Kernel α α) : Kernel α α := Kernel.sum fun n ↦ κ ^ n

theorem potential_apply' (κ : Kernel α α) (x : α) {s : Set α} (hs : MeasurableSet s) :
    potential κ x s = ∑' n, (κ ^ n) x s :=
  sum_apply' _ _ hs

theorem potential_apply_singleton [MeasurableSingletonClass α] (κ : Kernel α α) (x y : α) :
    potential κ x {y} = ∑' n, (κ ^ n) x {y} :=
  potential_apply' _ _ (measurableSet_singleton y)

/-- A kernel is *recurrent* if the expected number of returns to every state is infinite:
`∑ₙ κ^n x {x} = ∞` for all `x`. For a Markov kernel on a countable space this is the
potential-theoretic form of recurrence; its equivalence with almost sure return is not yet in
the library. -/
def IsRecurrent (κ : Kernel α α) : Prop := ∀ x, potential κ x {x} = ∞

/-- A kernel is *transient* if the expected number of returns to every state is finite. -/
def IsTransient (κ : Kernel α α) : Prop := ∀ x, potential κ x {x} ≠ ∞

/-- A kernel is *positive recurrent* if it is recurrent and admits an invariant probability
measure. For irreducible Markov kernels on a countable space the first condition follows from
the second (`isRecurrent_of_invariant`). -/
def IsPositiveRecurrent (κ : Kernel α α) : Prop :=
  IsRecurrent κ ∧ ∃ μ : Measure α, IsProbabilityMeasure μ ∧ κ.Invariant μ

theorem IsPositiveRecurrent.isRecurrent {κ : Kernel α α} (h : IsPositiveRecurrent κ) :
    IsRecurrent κ :=
  h.1

/-! ### Countable state spaces: Chapman–Kolmogorov bounds and Fekete's lemma -/

variable [Countable α] [MeasurableSingletonClass α]

/-- A three-factor Chapman–Kolmogorov lower bound: the weight of the paths `x' → x → y → y'`
with `k`, `n`, `m` steps is at most `κ^(k+n+m) x' {y'}`. -/
theorem mul_mul_le_pow_apply_singleton (κ : Kernel α α) (k n m : ℕ) (x' x y y' : α) :
    (κ ^ k) x' {x} * (κ ^ n) x {y} * (κ ^ m) y {y'} ≤ (κ ^ (k + n + m)) x' {y'} := by
  have h1 : (κ ^ k) x' {x} * (κ ^ n) x {y} ≤ (κ ^ (n + k)) x' {y} := by
    rw [Kernel.pow_add, comp_apply_eq_tsum _ _ _ (measurableSet_singleton y)]
    exact ENNReal.le_tsum x
  calc (κ ^ k) x' {x} * (κ ^ n) x {y} * (κ ^ m) y {y'}
      ≤ (κ ^ (n + k)) x' {y} * (κ ^ m) y {y'} := mul_le_mul' h1 le_rfl
    _ ≤ (κ ^ (m + (n + k))) x' {y'} := by
        rw [Kernel.pow_add κ m (n + k), comp_apply_eq_tsum _ _ _ (measurableSet_singleton y')]
        exact ENNReal.le_tsum y
    _ = (κ ^ (k + n + m)) x' {y'} := by rw [show m + (n + k) = k + n + m by ring]

theorem convergenceNorm_eq_top_of_pow_eq_top {n : ℕ} (hn : n ≠ 0) (h : (κ ^ n) x {x} = ∞) :
    convergenceNorm κ x = ∞ := by
  refine top_le_iff.1 (le_convergenceNorm_of_frequently (frequently_atTop.2 fun N ↦
    ⟨N * n, Nat.le_mul_of_pos_right N (Nat.pos_of_ne_zero hn), ?_⟩))
  calc (∞ : ℝ≥0∞) ^ (N * n) = (κ ^ n) x {x} ^ N := by rw [pow_mul', h, ENNReal.top_pow hn]
    _ ≤ (κ ^ (N * n)) x {x} := pow_le_pow_mul_apply_singleton κ N n x

theorem pow_apply_singleton_ne_top_of_convergenceNorm_ne_top (h : convergenceNorm κ x ≠ ∞)
    {n : ℕ} (hn : n ≠ 0) : (κ ^ n) x {x} ≠ ∞ :=
  fun h' ↦ h (convergenceNorm_eq_top_of_pow_eq_top hn h')

/-- **Cauchy–Hadamard**, convergence half: `∑ₙ κ^n x {x} zⁿ < ∞` for
`z < (convergenceNorm κ x)⁻¹`. -/
theorem tsum_pow_apply_singleton_mul_pow_ne_top {z : ℝ≥0∞} (hz : z < (convergenceNorm κ x)⁻¹) :
    ∑' n, (κ ^ n) x {x} * z ^ n ≠ ∞ := by
  refine tsum_pow_apply_singleton_mul_pow_ne_top_aux (fun n ↦ ?_) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero_apply_singleton, Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply]
    exact ENNReal.one_ne_top
  · refine pow_apply_singleton_ne_top_of_convergenceNorm_ne_top (fun h ↦ ?_) hn.ne'
    rw [h, ENNReal.inv_top] at hz
    exact (not_lt_bot hz).elim

theorem one_le_convergenceNorm_of_potential_eq_top (h : potential κ x {x} = ∞) :
    1 ≤ convergenceNorm κ x := by
  by_contra hlt
  rw [not_le] at hlt
  refine tsum_pow_apply_singleton_mul_pow_ne_top (ENNReal.one_lt_inv.2 hlt) ?_
  simpa only [one_pow, mul_one, potential_apply_singleton] using h

/-- A recurrent Markov kernel has convergence norm `1`. -/
theorem IsRecurrent.convergenceNorm_eq_one [IsMarkovKernel κ] (h : IsRecurrent κ) (x : α) :
    convergenceNorm κ x = 1 :=
  le_antisymm convergenceNorm_le_one (one_le_convergenceNorm_of_potential_eq_top (h x))

/-- The convergence norm is monotone along one-way communication: if `y` leads to `x` and `x`
leads to `y`, then `convergenceNorm κ y ≤ convergenceNorm κ x`. -/
theorem convergenceNorm_le_convergenceNorm {y : α} {k m : ℕ} (hxy : 0 < (κ ^ k) x {y})
    (hyx : 0 < (κ ^ m) y {x}) : convergenceNorm κ y ≤ convergenceNorm κ x := by
  refine le_of_forall_lt_imp_le_of_dense fun t ht ↦ ?_
  obtain ⟨s, hts, hsL⟩ := exists_between ht
  have hs0 : s ≠ 0 := (bot_le.trans_lt hts).ne'
  have hst : s ≠ ∞ := hsL.ne_top
  set c := (κ ^ k) x {y} * (κ ^ m) y {x} with hc
  have hc0 : 0 < c := ENNReal.mul_pos hxy.ne' hyx.ne'
  have hρ : t / s < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hs0) (Or.inl hst), one_mul]; exact hts
  have hev : ∀ᶠ n : ℕ in atTop, (t / s) ^ n * t ^ (k + m) ≤ c := by
    have hT : t ^ (k + m) ≠ ∞ := ENNReal.pow_ne_top hts.ne_top
    have := (tendsto_order.1 (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ)).2 _
      (ENNReal.div_pos hc0.ne' hT)
    exact this.mono fun n hn ↦ ENNReal.mul_le_of_le_div hn.le
  refine le_convergenceNorm_of_frequently ?_
  refine (tendsto_add_atTop_nat (m + k)).frequently
    (((frequently_pow_lt_of_lt_convergenceNorm hsL).and_eventually hev).mono fun n ⟨hn, hn'⟩ ↦ ?_)
  calc t ^ (n + (m + k)) = (t / s * s) ^ n * t ^ (k + m) := by
        rw [ENNReal.div_mul_cancel hs0 hst, ← _root_.pow_add, add_comm k]
    _ = (t / s) ^ n * t ^ (k + m) * s ^ n := by rw [mul_pow]; ring
    _ ≤ c * (κ ^ n) y {y} := mul_le_mul hn' hn.le zero_le zero_le
    _ = (κ ^ k) x {y} * (κ ^ n) y {y} * (κ ^ m) y {x} := by rw [hc]; ring
    _ ≤ (κ ^ (k + n + m)) x {x} := mul_mul_le_pow_apply_singleton κ k n m x y y x
    _ = (κ ^ (n + (m + k))) x {x} := by rw [show k + n + m = n + (m + k) by ring]

/-- The convergence norm is constant on communicating classes. -/
theorem convergenceNorm_eq_of_pow_pos {y : α} {k m : ℕ} (hxy : 0 < (κ ^ k) x {y})
    (hyx : 0 < (κ ^ m) y {x}) : convergenceNorm κ x = convergenceNorm κ y :=
  le_antisymm (convergenceNorm_le_convergenceNorm hyx hxy)
    (convergenceNorm_le_convergenceNorm hxy hyx)

/-- **Fekete's lemma** for the supermultiplicative sequence `κ^n x {x}`: if `κ^n x {x} > 0` for
all large `n`, then `(κ^n x {x})^(1/n)` converges to `convergenceNorm κ x`. -/
theorem tendsto_convergenceNorm (hpos : ∀ᶠ n in atTop, 0 < (κ ^ n) x {x}) :
    Tendsto (fun n : ℕ ↦ (κ ^ n) x {x} ^ (n : ℝ)⁻¹) atTop (𝓝 (convergenceNorm κ x)) := by
  refine tendsto_of_le_liminf_of_limsup_le (le_of_forall_lt_imp_le_of_dense fun t ht ↦ ?_) le_rfl
  refine le_liminf_of_le (by isBoundedDefault) ?_
  obtain ⟨s, hts, hsL⟩ := exists_between ht
  have hs0 : s ≠ 0 := (bot_le.trans_lt hts).ne'
  have hst : s ≠ ∞ := hsL.ne_top
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hpos
  obtain ⟨n, hn, hsn⟩ :=
    frequently_atTop.1 (frequently_pow_lt_of_lt_convergenceNorm hsL) (max n₀ 1)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnn₀ : n₀ ≤ n := (le_max_left _ _).trans hn
  obtain ⟨r₀, -, hr₀⟩ := Finset.exists_min_image (Finset.range n)
    (fun r ↦ (κ ^ (n + r)) x {x}) ⟨0, Finset.mem_range.2 hn1⟩
  have hA : 0 < (κ ^ (n + r₀)) x {x} := hn₀ _ (hnn₀.trans (Nat.le_add_right n r₀))
  have hρ : t / s < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hs0) (Or.inl hst), one_mul]; exact hts
  have hT : (max 1 t) ^ (2 * n) ≠ ∞ :=
    ENNReal.pow_ne_top (max_lt ENNReal.one_lt_top hts.ne_top.lt_top).ne
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((tendsto_order.1
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ)).2 _ (ENNReal.div_pos hA.ne' hT))
  refine eventually_atTop.2 ⟨max (n * (J + 1)) 1, fun m hm ↦ ?_⟩
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  rw [ENNReal.le_rpow_inv_iff (Nat.cast_pos.2 hm1), ENNReal.rpow_natCast]
  obtain ⟨k, hk⟩ : ∃ k, m / n = k + 1 := by
    refine ⟨m / n - 1, ?_⟩
    have : J + 1 ≤ m / n :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact (le_max_left _ _).trans hm)
    omega
  have hJk : J ≤ k := by
    have : J + 1 ≤ m / n :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact (le_max_left _ _).trans hm)
    omega
  have hr : m % n < n := Nat.mod_lt _ (by omega)
  have hm' : m = k * n + (n + m % n) := by
    have h := Nat.div_add_mod m n
    rw [hk] at h
    calc m = n * (k + 1) + m % n := h.symm
      _ = k * n + (n + m % n) := by ring
  have i1 : (t / s) ^ (k * n) ≤ (t / s) ^ J :=
    pow_le_pow_of_le_one zero_le hρ.le (hJk.trans (Nat.le_mul_of_pos_right k (by omega)))
  have i2 : s ^ (k * n) ≤ (κ ^ n) x {x} ^ k := by
    rw [pow_mul']; exact pow_le_pow_left' hsn.le k
  have i3 : t ^ (n + m % n) ≤ (max 1 t) ^ (2 * n) :=
    (pow_le_pow_left' (le_max_right 1 t) _).trans
      (pow_le_pow_right₀ (le_max_left 1 t) (by omega))
  calc t ^ m = (t / s * s) ^ (k * n) * t ^ (n + m % n) := by
        rw [ENNReal.div_mul_cancel hs0 hst, ← _root_.pow_add, ← hm']
    _ = (t / s) ^ (k * n) * s ^ (k * n) * t ^ (n + m % n) := by rw [mul_pow]
    _ ≤ (t / s) ^ J * (κ ^ n) x {x} ^ k * (max 1 t) ^ (2 * n) :=
        mul_le_mul (mul_le_mul i1 i2 zero_le zero_le) i3 zero_le zero_le
    _ = (t / s) ^ J * (max 1 t) ^ (2 * n) * (κ ^ n) x {x} ^ k := by ring
    _ ≤ (κ ^ (n + r₀)) x {x} * (κ ^ (k * n)) x {x} :=
        mul_le_mul (ENNReal.mul_le_of_le_div (hJ J le_rfl).le)
          (pow_le_pow_mul_apply_singleton κ k n x) zero_le zero_le
    _ ≤ (κ ^ (k * n)) x {x} * (κ ^ (n + m % n)) x {x} := by
        rw [mul_comm]; exact mul_le_mul' le_rfl (hr₀ _ (Finset.mem_range.2 hr))
    _ ≤ (κ ^ (k * n + (n + m % n))) x {x} := pow_apply_singleton_mul_le κ _ _ x
    _ = (κ ^ m) x {x} := by rw [← hm']

/-! ### Irreducibility on a countable space -/

omit [Countable α] in
theorem exists_pow_apply_singleton_pos [IsIrreducible Measure.count κ] (x y : α) :
    ∃ n, 0 < (κ ^ n) x {y} :=
  IsIrreducible.irreducible (measurableSet_singleton y)
    (by rw [Measure.count_singleton]; exact one_pos) x

omit [Countable α] [MeasurableSingletonClass α] in
/-- On a countable space, irreducibility with respect to counting measure is the usual
irreducibility of the transition matrix: every state leads to every state. -/
theorem isIrreducible_count_of_forall (h : ∀ x y, ∃ n, 0 < (κ ^ n) x {y}) :
    IsIrreducible Measure.count κ where
  irreducible A hA hcount x := by
    obtain ⟨y, hy⟩ : A.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro rfl
      simp at hcount
    obtain ⟨n, hn⟩ := h x y
    exact ⟨n, hn.trans_le (measure_mono (Set.singleton_subset_iff.2 hy))⟩

omit [Countable α] in
theorem isIrreducible_count_iff :
    IsIrreducible Measure.count κ ↔ ∀ x y, ∃ n, 0 < (κ ^ n) x {y} :=
  ⟨fun _ ↦ exists_pow_apply_singleton_pos, isIrreducible_count_of_forall⟩

/-! ### Strictly positive kernels

A *positive matrix* in Georgii's sense is a kernel all of whose entries `κ a {b}` are strictly
positive. For such a kernel the `limsup` defining `convergenceNorm` is a genuine limit and does
not depend on the state, which is the content of Georgii's (11.6). -/

/-- All `n`-step entries of a strictly positive kernel are strictly positive, `n ≥ 1`. -/
theorem pow_succ_apply_singleton_pos (hpos : ∀ a b, 0 < κ a {b}) (n : ℕ) (a b : α) :
    0 < (κ ^ (n + 1)) a {b} := by
  induction n generalizing a with
  | zero => rw [zero_add, pow_one]; exact hpos a b
  | succ n ih =>
    rw [pow_succ_apply_eq_tsum _ _ _ (measurableSet_singleton b)]
    exact lt_of_lt_of_le (ENNReal.mul_pos (hpos a a).ne' (ih a).ne') (ENNReal.le_tsum a)

omit [Countable α] [MeasurableSingletonClass α] in
/-- A strictly positive kernel is irreducible with respect to the counting measure. -/
theorem isIrreducible_count_of_forall_pos (hpos : ∀ a b, 0 < κ a {b}) :
    IsIrreducible Measure.count κ :=
  isIrreducible_count_of_forall fun a b ↦ ⟨1, by rw [pow_one]; exact hpos a b⟩

/-- **(11.6)**, existence of the limit: for a strictly positive kernel `(κ^n a {a})^(1/n)`
converges to `convergenceNorm κ a`. -/
theorem tendsto_convergenceNorm_of_forall_pos (hpos : ∀ a b, 0 < κ a {b}) (a : α) :
    Tendsto (fun n : ℕ ↦ (κ ^ n) a {a} ^ (n : ℝ)⁻¹) atTop (𝓝 (convergenceNorm κ a)) :=
  tendsto_convergenceNorm ((eventually_ge_atTop 1).mono fun n hn ↦ by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm]
    exact pow_succ_apply_singleton_pos hpos m a a)

/-- **(11.6)**, independence of the state: the convergence norm of a strictly positive kernel is
the same at every state. -/
theorem convergenceNorm_eq_of_forall_pos (hpos : ∀ a b, 0 < κ a {b}) (a b : α) :
    convergenceNorm κ a = convergenceNorm κ b :=
  convergenceNorm_eq_of_pow_pos (k := 1) (m := 1) (by rw [pow_one]; exact hpos a b)
    (by rw [pow_one]; exact hpos b a)

/-! ### The recurrence/transience dichotomy -/

omit [Countable α] in
theorem pow_zero_apply_singleton_self (κ : Kernel α α) (x : α) : (κ ^ 0) x {x} = 1 := by
  rw [pow_zero_apply_singleton, Set.indicator_of_mem (Set.mem_singleton x), Pi.one_apply]

/-- Paths `x' → x`, then `x → y` in any number of steps, then `y → y'`, are counted by the
potential kernel at `(x', y')`. -/
theorem mul_potential_mul_le_potential (κ : Kernel α α) (k m : ℕ) (x' x y y' : α) :
    (κ ^ k) x' {x} * potential κ x {y} * (κ ^ m) y {y'} ≤ potential κ x' {y'} := by
  rw [potential_apply_singleton, potential_apply_singleton, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right]
  calc ∑' n, (κ ^ k) x' {x} * (κ ^ n) x {y} * (κ ^ m) y {y'}
      ≤ ∑' n, (κ ^ (k + n + m)) x' {y'} :=
        ENNReal.tsum_le_tsum fun n ↦ mul_mul_le_pow_apply_singleton κ k n m x' x y y'
    _ ≤ ∑' n, (κ ^ n) x' {y'} :=
        ENNReal.tsum_comp_le_tsum_of_injective (f := fun n ↦ k + n + m)
          (fun a b h ↦ by simpa using h) _

theorem potential_eq_top_of_pow_pos {k m : ℕ} {x' x y y' : α} (hx'x : 0 < (κ ^ k) x' {x})
    (hyy' : 0 < (κ ^ m) y {y'}) (h : potential κ x {y} = ∞) : potential κ x' {y'} = ∞ := by
  refine top_le_iff.1 (le_trans (le_of_eq ?_) (mul_potential_mul_le_potential κ k m x' x y y'))
  rw [h, ENNReal.mul_top hx'x.ne', ENNReal.top_mul hyy'.ne']

theorem isRecurrent_of_potential_eq_top [IsIrreducible Measure.count κ] {x y : α}
    (h : potential κ x {y} = ∞) : IsRecurrent κ := fun z ↦ by
  obtain ⟨k, hk⟩ := exists_pow_apply_singleton_pos (κ := κ) z x
  obtain ⟨m, hm⟩ := exists_pow_apply_singleton_pos (κ := κ) y z
  exact potential_eq_top_of_pow_pos hk hm h

theorem IsRecurrent.potential_eq_top [IsIrreducible Measure.count κ] (h : IsRecurrent κ)
    (x y : α) : potential κ x {y} = ∞ := by
  obtain ⟨m, hm⟩ := exists_pow_apply_singleton_pos (κ := κ) x y
  exact potential_eq_top_of_pow_pos (k := 0) (by rw [pow_zero_apply_singleton_self]; exact one_pos)
    hm (h x)

theorem IsTransient.potential_ne_top [IsIrreducible Measure.count κ] (h : IsTransient κ)
    (x y : α) : potential κ x {y} ≠ ∞ :=
  fun h' ↦ h x (isRecurrent_of_potential_eq_top h' x)

/-- **Recurrence/transience dichotomy** for an irreducible kernel on a countable space: either
`∑ₙ κ^n x {y} = ∞` for all `x, y`, or `∑ₙ κ^n x {y} < ∞` for all `x, y`. -/
theorem isRecurrent_or_isTransient [IsIrreducible Measure.count κ] :
    IsRecurrent κ ∨ IsTransient κ := by
  by_cases h : ∃ x, potential κ x {x} = ∞
  · obtain ⟨x, hx⟩ := h
    exact Or.inl (isRecurrent_of_potential_eq_top hx)
  · exact Or.inr (not_exists.1 h)

theorem not_isTransient_iff [Nonempty α] [IsIrreducible Measure.count κ] :
    ¬ IsTransient κ ↔ IsRecurrent κ :=
  ⟨fun h ↦ isRecurrent_or_isTransient.resolve_right h,
    fun h h' ↦ h' (Classical.arbitrary α) (h _)⟩

/-! ### Superharmonic functions of recurrent kernels are constant -/

/-- Integration of a function against `κ ^ (n + 1)` is integration of `∫⁻ g ∂κ` against
`κ ^ n`. -/
theorem lintegral_pow_succ (κ : Kernel α α) (n : ℕ) (x : α) (g : α → ℝ≥0∞) :
    ∫⁻ z, g z ∂(κ ^ (n + 1)) x = ∫⁻ y, ∫⁻ z, g z ∂κ y ∂(κ ^ n) x := by
  rw [_root_.pow_succ']
  exact lintegral_comp κ (κ ^ n) x (measurable_of_countable g)

/-- **Riesz decomposition** of a superharmonic function `g` (i.e. `κ g ≤ g`):
`g = κ^n g + ∑_{i < n} κ^i (g - κ g)`. -/
theorem eq_lintegral_pow_add_sum_of_lintegral_le {g : α → ℝ≥0∞}
    (hg : ∀ z, ∫⁻ y, g y ∂κ z ≤ g z) (n : ℕ) (x : α) :
    g x = ∫⁻ z, g z ∂(κ ^ n) x
      + ∑ i ∈ Finset.range n, ∫⁻ z, g z - ∫⁻ y, g y ∂κ z ∂(κ ^ i) x := by
  induction n with
  | zero =>
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty, add_zero]
    change g x = ∫⁻ z, g z ∂(Kernel.id x)
    rw [Kernel.id_apply, lintegral_dirac]
  | succ n ih =>
    calc g x = ∫⁻ z, g z ∂(κ ^ n) x
          + ∑ i ∈ Finset.range n, ∫⁻ z, g z - ∫⁻ y, g y ∂κ z ∂(κ ^ i) x := ih
      _ = ∫⁻ z, ((∫⁻ y, g y ∂κ z) + (g z - ∫⁻ y, g y ∂κ z)) ∂(κ ^ n) x
          + ∑ i ∈ Finset.range n, ∫⁻ z, g z - ∫⁻ y, g y ∂κ z ∂(κ ^ i) x := by
        congr 1
        exact lintegral_congr fun z ↦ (add_tsub_cancel_of_le (hg z)).symm
      _ = _ := by
        rw [lintegral_add_left (measurable_of_countable _), lintegral_pow_succ,
          Finset.sum_range_succ]
        ring

theorem mul_apply_singleton_le_lintegral (μ : Measure α) (g : α → ℝ≥0∞) (z : α) :
    g z * μ {z} ≤ ∫⁻ y, g y ∂μ := by
  rw [lintegral_countable']
  exact ENNReal.le_tsum z

theorem _root_.MeasureTheory.Measure.tsum_apply_singleton (μ : Measure α) :
    ∑' x, μ {x} = μ Set.univ := by
  simpa using (lintegral_countable' (μ := μ) fun _ ↦ 1).symm.trans lintegral_one

/-- A finite superharmonic function `g` of a kernel `κ` with `potential κ x {z} = ∞` is
harmonic at `z`: the "excess" `g z - κ g z` vanishes. -/
theorem lintegral_eq_of_potential_eq_top {g : α → ℝ≥0∞} (hg : ∀ z, ∫⁻ y, g y ∂κ z ≤ g z)
    {x z : α} (hx : g x ≠ ∞) (hxz : potential κ x {z} = ∞) : ∫⁻ y, g y ∂κ z = g z := by
  set d : α → ℝ≥0∞ := fun z ↦ g z - ∫⁻ y, g y ∂κ z with hd
  have key : ∀ n, d z * ∑ i ∈ Finset.range n, (κ ^ i) x {z} ≤ g x := fun n ↦ by
    rw [Finset.mul_sum, eq_lintegral_pow_add_sum_of_lintegral_le hg n x]
    exact le_add_left (Finset.sum_le_sum fun i _ ↦ mul_apply_singleton_le_lintegral _ d z)
  have hpot : d z * potential κ x {z} ≤ g x := by
    rw [potential_apply_singleton, ENNReal.tsum_eq_iSup_nat, ENNReal.mul_iSup]
    exact iSup_le key
  rw [hxz] at hpot
  have hd0 : d z = 0 := by
    by_contra h0
    rw [ENNReal.mul_top h0] at hpot
    exact hx (top_le_iff.1 hpot)
  have : g z - ∫⁻ y, g y ∂κ z = 0 := hd0
  exact le_antisymm (hg z) (tsub_eq_zero_iff_le.1 this)

/-- **Maximum principle**: a harmonic function of an irreducible Markov kernel on a countable
space that attains its (finite) supremum is constant. -/
theorem apply_eq_of_lintegral_eq_of_le [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {g : α → ℝ≥0∞} (hg : ∀ z, ∫⁻ y, g y ∂κ z = g z) {y : α} (hy : g y ≠ ∞)
    (hle : ∀ z, g z ≤ g y) (x : α) : g x = g y := by
  refine le_antisymm (hle x) (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨n, hn⟩ := exists_pow_apply_singleton_pos (κ := κ) y x
  have hpow : ∀ n, ∫⁻ z, g z ∂(κ ^ n) y = g y := fun n ↦ by
    have := eq_lintegral_pow_add_sum_of_lintegral_le (fun z ↦ (hg z).le) n y
    simpa [hg] using this.symm
  have h1 : ∑' w, g y * (κ ^ n) y {w} = g y := by
    rw [ENNReal.tsum_mul_left, Measure.tsum_apply_singleton, measure_univ, mul_one]
  refine (lt_irrefl (g y)) ?_
  calc g y = ∫⁻ z, g z ∂(κ ^ n) y := (hpow n).symm
    _ = ∑' w, g w * (κ ^ n) y {w} := lintegral_countable' g
    _ < ∑' w, g y * (κ ^ n) y {w} := by
        refine ENNReal.tsum_lt_tsum (i := x) ?_ (fun w ↦ mul_le_mul' (hle w) le_rfl) ?_
        · rw [← lintegral_countable', hpow]; exact hy
        · exact ENNReal.mul_lt_mul_left hn.ne' (measure_ne_top _ _) hlt
    _ = g y := h1

/-- **Liouville property of recurrent kernels**: a finite superharmonic function of an
irreducible recurrent Markov kernel on a countable space is constant. -/
theorem IsRecurrent.apply_eq_apply_of_lintegral_le [IsMarkovKernel κ]
    [IsIrreducible Measure.count κ] (hrec : IsRecurrent κ) {r : α → ℝ≥0∞} (hr : ∀ x, r x ≠ ∞)
    (hharm : ∀ x, ∫⁻ y, r y ∂κ x ≤ r x) (x y : α) : r x = r y := by
  suffices key : ∀ x y, r y ≤ r x from le_antisymm (key y x) (key x y)
  intro x y
  set g : α → ℝ≥0∞ := fun z ↦ min (r z) (r y) with hg
  have hgsup : ∀ z, ∫⁻ w, g w ∂κ z ≤ g z := fun z ↦ by
    refine le_min ((lintegral_mono fun w ↦ min_le_left _ _).trans (hharm z)) ?_
    calc ∫⁻ w, g w ∂κ z ≤ ∫⁻ _, r y ∂κ z := lintegral_mono fun w ↦ min_le_right _ _
      _ = r y := by rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  have hgharm : ∀ z, ∫⁻ w, g w ∂κ z = g z := fun z ↦
    lintegral_eq_of_potential_eq_top hgsup (x := y) (ne_top_of_le_ne_top (hr y) (min_le_right _ _))
      (hrec.potential_eq_top y z)
  have hgy : g y = r y := min_self _
  have := apply_eq_of_lintegral_eq_of_le hgharm (y := y) (hgy ▸ hr y)
    (fun z ↦ hgy ▸ min_le_right _ _) x
  rw [hgy] at this
  exact this ▸ min_le_left _ _

/-! ### Invariant probability measures force recurrence -/

omit [Countable α] [MeasurableSingletonClass α] in
theorem Invariant.pow {μ : Measure α} (h : κ.Invariant μ) (n : ℕ) : (κ ^ n).Invariant μ := by
  induction n with
  | zero => rw [pow_zero]; exact Measure.bind_dirac
  | succ n ih => rw [_root_.pow_succ]; exact ih.comp h

theorem Invariant.apply_singleton_eq_tsum {μ : Measure α} (h : κ.Invariant μ) (y : α) :
    μ {y} = ∑' x, κ x {y} * μ {x} := by
  conv_lhs => rw [← h.def]
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable, lintegral_countable']

/-- An irreducible Markov kernel on a countable space with an invariant probability measure is
recurrent. -/
theorem isRecurrent_of_invariant [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
    {μ : Measure α} [IsProbabilityMeasure μ] (hμ : κ.Invariant μ) : IsRecurrent κ := by
  refine isRecurrent_or_isTransient.resolve_right fun htrans ↦ ?_
  have hzero : ∀ y, μ {y} = 0 := fun y ↦ by
    have key : ∀ ε : ℝ≥0∞, 0 < ε → μ {y} ≤ ε + ε := fun ε hε ↦ by
      have htail := ENNReal.tendsto_tsum_compl_atTop_zero (f := fun x ↦ μ {x})
        (by rw [Measure.tsum_apply_singleton, measure_univ]; exact ENNReal.one_ne_top)
      obtain ⟨F, hF⟩ := eventually_atTop.1 ((tendsto_order.1 htail).2 _ hε)
      have hlim : Tendsto (fun n ↦ ∑ x ∈ F, (κ ^ n) x {y} * μ {x}) atTop (𝓝 0) := by
        rw [← Finset.sum_const_zero (s := F)]
        refine tendsto_finsetSum _ fun x _ ↦ ?_
        rw [← zero_mul (μ {x})]
        refine ENNReal.Tendsto.mul_const ?_ (Or.inr (measure_ne_top _ _))
        exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top
          (by rw [← potential_apply_singleton]; exact htrans.potential_ne_top x y)
      obtain ⟨n, hn⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 _ hε)
      calc μ {y} = ∑' x, (κ ^ n) x {y} * μ {x} := (hμ.pow n).apply_singleton_eq_tsum y
        _ = ∑ x ∈ F, (κ ^ n) x {y} * μ {x}
              + ∑' x : ↥(F : Set α)ᶜ, (κ ^ n) (x : α) {y} * μ {(x : α)} :=
            (ENNReal.sum_add_tsum_compl F _).symm
        _ ≤ ε + ε := by
            refine add_le_add (hn n le_rfl).le ((ENNReal.tsum_le_tsum fun x ↦ ?_).trans
              (hF F le_rfl).le)
            exact mul_le_of_le_one_left' prob_le_one
    refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun ε hε ↦ ?_) bot_le
    calc μ {y} ≤ ε / 2 + ε / 2 := key _ (ENNReal.half_pos hε.ne')
      _ = ε := ENNReal.add_halves ε
  have : μ Set.univ = 0 := by
    rw [← Measure.tsum_apply_singleton]
    simp [hzero]
  exact zero_ne_one (this.symm.trans measure_univ)

/-! ### Kernels related by a change of measure `η x {y} = κ x {y} r y / (q r x)`

Two kernels `κ`, `η` on a countable space are related by the positive function `r` and the
constant `q` if `η x {y} = κ x {y} r y / (q r x)`. This is the relation between two transfer
matrices defining the same Markov specification on `ℤ`; here it is studied for its own sake:
the powers are related the same way, the convergence norms differ by the factor `q`, and if
`q = 1` the potentials agree, so that recurrence and transience are shared. If moreover both
kernels are Markov and `κ` is irreducible and recurrent, then `r` is constant and `η = κ`. -/

section ChangeOfMeasure

variable {η : Kernel α α} {q : ℝ≥0∞} {r : α → ℝ≥0∞}

omit [Countable α] [MeasurableSingletonClass α] in
theorem apply_singleton_mul_eq_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (x y : α) : η x {y} * (q * r x) = κ x {y} * r y := by
  rw [h, ENNReal.div_mul_cancel (mul_ne_zero hq0 (hr0 x)) (ENNReal.mul_ne_top hqt (hrt x))]

/-- Powers of related kernels are related: `η^n x {y} (qⁿ r x) = κ^n x {y} r y`. -/
theorem pow_apply_singleton_mul_eq_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (n : ℕ) (x y : α) : (η ^ n) x {y} * (q ^ n * r x) = (κ ^ n) x {y} * r y := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero_apply_singleton, pow_zero_apply_singleton, pow_zero, one_mul]
    rcases eq_or_ne x y with rfl | hxy
    · rfl
    · simp [hxy]
  | succ n ih =>
    rw [pow_succ_apply_eq_tsum _ _ _ (measurableSet_singleton y),
      pow_succ_apply_eq_tsum _ _ _ (measurableSet_singleton y), ← ENNReal.tsum_mul_right,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun b ↦ ?_
    rw [← ENNReal.mul_left_inj (hr0 b) (hrt b)]
    calc η x {b} * (η ^ n) b {y} * (q ^ (n + 1) * r x) * r b
        = (η x {b} * (q * r x)) * ((η ^ n) b {y} * (q ^ n * r b)) := by ring
      _ = (κ x {b} * r b) * ((κ ^ n) b {y} * r y) := by
        rw [apply_singleton_mul_eq_of_apply_eq_mul_div hq0 hqt hr0 hrt h, ih]
      _ = κ x {b} * (κ ^ n) b {y} * r y * r b := by ring

theorem pow_apply_singleton_pos_iff_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (n : ℕ) (x y : α) : 0 < (η ^ n) x {y} ↔ 0 < (κ ^ n) x {y} := by
  have key := pow_apply_singleton_mul_eq_of_apply_eq_mul_div hq0 hqt hr0 hrt h n x y
  simp only [pos_iff_ne_zero]
  constructor
  · intro hη hκ
    rw [hκ, zero_mul] at key
    exact mul_ne_zero hη (mul_ne_zero (pow_ne_zero n hq0) (hr0 x)) key
  · intro hκ hη
    rw [hη, zero_mul] at key
    exact mul_ne_zero hκ (hr0 y) key.symm

/-- Irreducibility transfers along the relation `η x {y} = κ x {y} r y / (q r x)`. -/
theorem isIrreducible_count_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    [IsIrreducible Measure.count η] : IsIrreducible Measure.count κ :=
  isIrreducible_count_of_forall fun x y ↦ by
    obtain ⟨n, hn⟩ := exists_pow_apply_singleton_pos (κ := η) x y
    exact ⟨n, (pow_apply_singleton_pos_iff_of_apply_eq_mul_div hq0 hqt hr0 hrt h n x y).1 hn⟩

/-- On the diagonal, `η^n x {x} qⁿ = κ^n x {x}`. -/
theorem pow_apply_singleton_self_mul_eq_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (n : ℕ) (x : α) : (η ^ n) x {x} * q ^ n = (κ ^ n) x {x} := by
  have := pow_apply_singleton_mul_eq_of_apply_eq_mul_div hq0 hqt hr0 hrt h n x x
  rwa [← mul_assoc, ENNReal.mul_left_inj (hr0 x) (hrt x)] at this

/-- The convergence norms of related kernels differ by the factor `q`. -/
theorem convergenceNorm_eq_div_of_apply_eq_mul_div (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (x : α) : convergenceNorm η x = convergenceNorm κ x / q := by
  have hdiag : ∀ n, (η ^ n) x {x} = (κ ^ n) x {x} * q⁻¹ ^ n := fun n ↦ by
    rw [← pow_apply_singleton_self_mul_eq_of_apply_eq_mul_div hq0 hqt hr0 hrt h n x, mul_assoc,
      ← mul_pow, ENNReal.mul_inv_cancel hq0 hqt, one_pow, mul_one]
  have := ENNReal.limsup_mul_const_of_ne_top (f := atTop)
    (u := fun n : ℕ ↦ (κ ^ n) x {x} ^ (n : ℝ)⁻¹) (ENNReal.inv_ne_top.2 hq0)
  unfold convergenceNorm
  rw [div_eq_mul_inv, mul_comm, ← this]
  refine limsup_congr ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
  rw [hdiag, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.pow_rpow_inv_natCast (n := n) (by omega)]

/-- If related kernels have the same finite positive convergence norm at some state, the
constant `q` is `1`. -/
theorem eq_one_of_apply_eq_mul_div_of_convergenceNorm_eq (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (hL : convergenceNorm η x = convergenceNorm κ x) (h0 : convergenceNorm κ x ≠ 0)
    (ht : convergenceNorm κ x ≠ ∞) : q = 1 := by
  have := convergenceNorm_eq_div_of_apply_eq_mul_div hq0 hqt hr0 hrt h x
  rw [hL, ENNReal.eq_div_iff hq0 hqt] at this
  exact (ENNReal.mul_left_inj h0 ht).1 (this.trans (one_mul _).symm)

/-- For `q = 1`, related kernels have the same diagonal potentials. -/
theorem potential_apply_singleton_self_eq_of_apply_eq_mul_div (hr0 : ∀ x, r x ≠ 0)
    (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / r x) (x : α) :
    potential η x {x} = potential κ x {x} := by
  simp_rw [potential_apply_singleton]
  refine tsum_congr fun n ↦ ?_
  have := pow_apply_singleton_self_mul_eq_of_apply_eq_mul_div one_ne_zero ENNReal.one_ne_top
    hr0 hrt (by simpa using h) n x
  rwa [one_pow, mul_one] at this

theorem isRecurrent_iff_of_apply_eq_mul_div (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞)
    (h : ∀ x y, η x {y} = κ x {y} * r y / r x) : IsRecurrent η ↔ IsRecurrent κ := by
  simp only [IsRecurrent, potential_apply_singleton_self_eq_of_apply_eq_mul_div hr0 hrt h]

theorem isTransient_iff_of_apply_eq_mul_div (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞)
    (h : ∀ x y, η x {y} = κ x {y} * r y / r x) : IsTransient η ↔ IsTransient κ := by
  simp only [IsTransient, potential_apply_singleton_self_eq_of_apply_eq_mul_div hr0 hrt h]

/-- If `η x {y} = κ x {y} r y / r x` for Markov kernels `κ`, `η` on a countable space with `κ`
irreducible and recurrent, then `r` is harmonic for `κ`, hence constant, and `η = κ`. -/
theorem eq_of_apply_eq_mul_div_of_isRecurrent [IsMarkovKernel κ] [IsMarkovKernel η]
    [IsIrreducible Measure.count κ] (hrec : IsRecurrent κ) (hr0 : ∀ x, r x ≠ 0)
    (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / r x) : η = κ := by
  have hharm : ∀ x, ∫⁻ y, r y ∂κ x = r x := fun x ↦ by
    have h1 : ∑' y, η x {y} = 1 := by rw [Measure.tsum_apply_singleton, measure_univ]
    have h2 : ∑' y, r y * κ x {y} = (∑' y, η x {y}) * r x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun y ↦ ?_
      rw [h, ENNReal.div_mul_cancel (hr0 x) (hrt x)]
      exact mul_comm _ _
    rw [lintegral_countable', h2, h1, one_mul]
  have hconst := hrec.apply_eq_apply_of_lintegral_le hrt fun x ↦ (hharm x).le
  refine ext_of_singleton fun x y ↦ ?_
  rw [h, hconst y x, mul_div_assoc, ENNReal.div_self (hr0 x) (hrt x), mul_one]

/-- Related Markov kernels `η x {y} = κ x {y} r y / (q r x)` with `κ` irreducible and
recurrent and `convergenceNorm η = 1` at some state coincide. (For a recurrent Markov kernel
`convergenceNorm κ = 1` holds automatically, `IsRecurrent.convergenceNorm_eq_one`.) -/
theorem eq_of_apply_eq_mul_div_of_isRecurrent_of_convergenceNorm_eq_one [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsIrreducible Measure.count κ] (hrec : IsRecurrent κ) (hq0 : q ≠ 0)
    (hqt : q ≠ ∞) (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞)
    (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x)) (hη : convergenceNorm η x = 1) : η = κ := by
  have hq : q = 1 := eq_one_of_apply_eq_mul_div_of_convergenceNorm_eq hq0 hqt hr0 hrt h
    (hη.trans (hrec.convergenceNorm_eq_one x).symm) (by rw [hrec.convergenceNorm_eq_one x]; simp)
    (by rw [hrec.convergenceNorm_eq_one x]; simp)
  subst hq
  exact eq_of_apply_eq_mul_div_of_isRecurrent hrec hr0 hrt (by simpa using h)

/-- Related Markov kernels with convergence norm `1` at some common state share their
recurrence type: if one is transient so is the other. -/
theorem isTransient_iff_of_apply_eq_mul_div_of_convergenceNorm_eq_one (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (hκ : convergenceNorm κ x = 1) (hη : convergenceNorm η x = 1) :
    IsTransient η ↔ IsTransient κ := by
  have hq : q = 1 := eq_one_of_apply_eq_mul_div_of_convergenceNorm_eq hq0 hqt hr0 hrt h
    (hη.trans hκ.symm) (by rw [hκ]; simp) (by rw [hκ]; simp)
  subst hq
  exact isTransient_iff_of_apply_eq_mul_div hr0 hrt (by simpa using h)

theorem isRecurrent_iff_of_apply_eq_mul_div_of_convergenceNorm_eq_one (hq0 : q ≠ 0) (hqt : q ≠ ∞)
    (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (hκ : convergenceNorm κ x = 1) (hη : convergenceNorm η x = 1) :
    IsRecurrent η ↔ IsRecurrent κ := by
  have hq : q = 1 := eq_one_of_apply_eq_mul_div_of_convergenceNorm_eq hq0 hqt hr0 hrt h
    (hη.trans hκ.symm) (by rw [hκ]; simp) (by rw [hκ]; simp)
  subst hq
  exact isRecurrent_iff_of_apply_eq_mul_div hr0 hrt (by simpa using h)

/-- A Markov kernel `κ` with convergence norm `1` which is related to an irreducible positive
recurrent Markov kernel `η` by `η x {y} = κ x {y} r y / (q r x)` is equal to `η`, hence
positive recurrent itself: a null recurrent or transient kernel with convergence norm `1` is
never related to a positive recurrent one. -/
theorem isPositiveRecurrent_of_apply_eq_mul_div [IsMarkovKernel κ] [IsMarkovKernel η]
    [IsIrreducible Measure.count η] (hq0 : q ≠ 0) (hqt : q ≠ ∞) (hr0 : ∀ x, r x ≠ 0)
    (hrt : ∀ x, r x ≠ ∞) (h : ∀ x y, η x {y} = κ x {y} * r y / (q * r x))
    (hκ : convergenceNorm κ x = 1) (hη : IsPositiveRecurrent η) : IsPositiveRecurrent κ := by
  have : IsIrreducible Measure.count κ := isIrreducible_count_of_apply_eq_mul_div hq0 hqt hr0 hrt h
  have hrec : IsRecurrent κ :=
    (isRecurrent_iff_of_apply_eq_mul_div_of_convergenceNorm_eq_one hq0 hqt hr0 hrt h hκ
      (hη.isRecurrent.convergenceNorm_eq_one x)).1 hη.isRecurrent
  rw [← eq_of_apply_eq_mul_div_of_isRecurrent_of_convergenceNorm_eq_one hrec hq0 hqt hr0 hrt h
    (hη.isRecurrent.convergenceNorm_eq_one x)]
  exact hη

end ChangeOfMeasure

open scoped Classical in
/-- A positive matrix, seen as a kernel on a countable state space, is irreducible with respect to
counting measure: from any state, every nonempty set is reached in exactly one step. -/
lemma isIrreducible_count_ofMatrix_of_forall_pos [Countable α] [MeasurableSingletonClass α] {P : α → α → ℝ≥0∞} (hP : ∀ x y, 0 < P x y) :
    ProbabilityTheory.Kernel.IsIrreducible (Measure.count : Measure α) (Kernel.ofMatrix P) where
  irreducible A _ hcount a := by
    obtain ⟨y, hy⟩ := Measure.count_ne_zero_iff.1 hcount.ne'
    refine ⟨1, ?_⟩
    rw [pow_one]
    calc (0 : ℝ≥0∞) < P a y := hP a y
      _ = Kernel.ofMatrix P a {y} := (Kernel.ofMatrix_apply_singleton P a y).symm
      _ ≤ Kernel.ofMatrix P a A := measure_mono (Set.singleton_subset_iff.2 hy)

/-! ## The period of a state, and Breiman's eventual positivity

The period of a state is the gcd of its return times (`Nat.setGcd`), aperiodicity is period one
at every state, and `Nat.exists_mem_closure_of_ge` (the additive submonoid generated by a set of
gcd `1` contains all large naturals) turns supermultiplicativity of the diagonal into eventual
positivity. -/

section Period

/-- The *period* of the state `x` under the kernel `κ`: the greatest common divisor of the
return times `{n | κ^n x {x} > 0}` (`0` if there are none; `κ^0 x {x} = 1` contributes nothing
to the gcd). -/
noncomputable def period (κ : Kernel α α) (x : α) : ℕ := Nat.setGcd {n | 0 < (κ ^ n) x {x}}

/-- A kernel on a countable space is *aperiodic* if every state has period `1`. -/
def IsAperiodic (κ : Kernel α α) : Prop := ∀ x, period κ x = 1

variable {κ : Kernel α α} {x : α}

/-- The return times to `x` form an additive submonoid (supermultiplicativity of the diagonal). -/
theorem pow_apply_singleton_self_pos_of_mem_closure {n : ℕ}
    (h : n ∈ AddSubmonoid.closure {n | 0 < (κ ^ n) x {x}}) : 0 < (κ ^ n) x {x} := by
  refine AddSubmonoid.closure_induction (fun m hm ↦ hm) ?_ (fun a b _ _ ha hb ↦ ?_) h
  · rw [pow_zero_apply_singleton_self]; exact one_pos
  · exact (ENNReal.mul_pos ha.ne' hb.ne').trans_le (pow_apply_singleton_mul_le κ a b x)

omit [Countable α] [MeasurableSingletonClass α] in
theorem period_dvd_of_pos {n : ℕ} (h : 0 < (κ ^ n) x {x}) : period κ x ∣ n :=
  Nat.setGcd_dvd_of_mem h

omit [Countable α] [MeasurableSingletonClass α] in
theorem period_eq_one_of_pos (h : 0 < κ x {x}) : period κ x = 1 :=
  Nat.dvd_one.1 (period_dvd_of_pos (by rw [pow_one]; exact h))

/-- A state of period one is returned to at all sufficiently large times. -/
theorem eventually_pow_apply_singleton_self_pos (h : period κ x = 1) :
    ∀ᶠ n in Filter.atTop, 0 < (κ ^ n) x {x} := by
  obtain ⟨n₀, hn₀⟩ := Nat.exists_mem_closure_of_ge {n | 0 < (κ ^ n) x {x}}
  refine Filter.eventually_atTop.2 ⟨n₀, fun m hm ↦ pow_apply_singleton_self_pos_of_mem_closure
    (hn₀ m hm ?_)⟩
  unfold period at h
  rw [h]
  exact one_dvd m

/-- **Aperiodic irreducible kernels are eventually positive** (Breiman, *Probability*, Ch. 7):
for all states `x, y`, `κ^n x {y} > 0` for all sufficiently large `n`. -/
theorem eventually_pow_apply_singleton_pos [IsIrreducible Measure.count κ] (haper : IsAperiodic κ)
    (x y : α) : ∀ᶠ n in Filter.atTop, 0 < (κ ^ n) x {y} := by
  obtain ⟨k, hk⟩ := exists_pow_apply_singleton_pos (κ := κ) x y
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (eventually_pow_apply_singleton_self_pos (haper x))
  refine Filter.eventually_atTop.2 ⟨n₀ + k, fun n hn ↦ ?_⟩
  have h1 := mul_mul_le_pow_apply_singleton κ (n - k) k 0 x x y y
  rw [pow_zero_apply_singleton_self, mul_one, show n - k + k + 0 = n by omega] at h1
  exact (ENNReal.mul_pos (hn₀ _ (by omega)).ne' hk.ne').trans_le h1

end Period

end ProbabilityTheory.Kernel

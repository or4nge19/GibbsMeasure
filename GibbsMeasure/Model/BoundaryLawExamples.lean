/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix.Homogeneous
public import GibbsMeasure.Model.BoundaryLawUniqueness
public import GibbsMeasure.Specification.OneDimensionalUniqueness

/-!
# Georgii §11.1, Comment (11.18)(2) and Corollary (11.19)

Sites `ℤ`, a countable state space `E`, counting measure, a positive matrix `Q` with finite
powers (Georgii (11.1)), and its specification `γ^Q = transferSpecification Q hQ`
(`GibbsMeasure/Model/BoundaryLaw.lean`).

## Main declarations

* `isTransferMatrix_of_translationInvariant`,
  `eq_empty_G_transferSpecification_of_translationInvariant`,
  `eq_empty_G_transferSpecification_randomWalk` — **Georgii Corollary (11.19)**: a translation
  invariant positive matrix `Q` on an *infinite* countable additive group `E` with
  `∑_x Q(0, x) < ∞` has `𝒢(Q) = ∅`. Georgii states this for `E = ℤ^N`; nothing but the group
  structure, countability and infinitude is used, and `eq_empty_G_transferSpecification_randomWalk`
  is the statement at `E = Fin N → ℤ`, `N ≥ 1`, verbatim. Georgii's Stirling/Cramér step is not
  needed; see the section docstring below for the shorter argument and where it differs.
* `tsum_pow_succ_apply_singleton_self_le_of_le_mul`, `tsum_mul_ne_top_of_mul_le`,
  `not_exists_pos_forall_le_sum_pow_of_bounded_ratio` — **Georgii Comment (11.18)(2)**, the
  quantitative half: `C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` gives `∑_x Q^n(x,x) ≤ [C ∑_x u(x)v(x)]^n`
  and `∑_x u(x)v(x) < ∞`, hence on an infinite `E` the condition `inf_x ∑_{n=1}^N Q^n(x,x) > 0`
  of Corollary (11.17) fails: the uniqueness conditions of Theorem (8.39) and of Corollary (11.17)
  exclude each other.
* `ratioMatrix`, `boundaryWeight`, `transferWeight_eq_mul_boundaryWeight`,
  `transferSpecification_eq_gibbsSpecificationOfFiniteReference`,
  `transferSpecification_eq_gibbsSpecification_of_bounded_ratio` — **Georgii Comment (11.18)(2)**,
  the Gibbsian representation: under the bounded-ratio condition, `γ^Q` *is* the Gibbs
  specification of the bounded nearest-neighbour potential
  `Φ_{{i,i+1}} = -log[Q(σ_i,σ_{i+1})/(u(σ_i)v(σ_{i+1}))]` for the (necessarily finite) a priori
  measure `(uv)λ`, `λ` counting measure.
* `oscSpan_markovPotential`, `iSup_oscSpan_markovPotential_ne_top`,
  `subsingleton_G_transferSpecification_of_bounded_ratio`,
  `existsUnique_mem_GP_transferSpecification_of_bounded_ratio` — **Georgii Comment (11.18)(2)**,
  the conclusion `|𝒢(γ^Q)| = 1`. Only the bond `{i, i+1}` spans the site `i`, so Georgii's
  condition (8.40) for the potential above is the single bound `δ(Φ_{{i,i+1}}) ≤ 2 log C`, and
  Theorem (8.39) (`GibbsMeasure/Specification/OneDimensionalUniqueness.lean`) applies. Existence
  is the second half of (8.39): a countable state space with measurable singletons is standard
  Borel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section


namespace MeasureTheory.GibbsMeasure.Markov

/-! ## Georgii, Corollary (11.19): random walk transfer matrices have no Gibbs measure

Georgii's proof runs: `inf_x Q(x,x) = Q(0,0) > 0` gives the hypothesis of Corollary (11.17) at
`N = 1`, so it remains to rule out that `Q` is equivalent, in the sense of (11.5), to a positive
recurrent stochastic matrix `P`. He produces a *homogeneous* stochastic `P` equivalent to `Q` by
an exponential tilt `Q_s(x,y) = Q(x,y) e^{s·(y-x)}/φ(s)` at a minimiser `s₀` of the moment
generating function `φ`, identifying `φ(s₀) = L(Q)` through a truncation and a Stirling/Cramér
lower bound on the number of loops of length `n`, and then quotes that a homogeneous stochastic
matrix is never positive recurrent.

The Stirling estimate is not needed. Georgii's tilting step exists only to *replace* the
equivalent stochastic matrix `P` by a homogeneous one; but `P` is homogeneous already. Indeed,
for every `z` the translate `P_z(x,y) = P(x+z, y+z)` is again stochastic and again equivalent to
`Q` — via the translated vector `r_z = r(· + z)`, because `Q` is translation invariant — and two
change-of-measure representations of the same matrix with the same constant `q` coincide as soon
as one of them is recurrent (Georgii's Remark (11.7); here
`Kernel.eq_of_apply_eq_mul_div_of_apply_eq_mul_div_of_isRecurrent`). Hence `P_z = P` for every
`z`, i.e. `P` is homogeneous, and
`Kernel.not_isPositiveRecurrent_ofMatrix_of_translationInvariant` finishes.
-/

section RandomWalk

variable {E : Type*} [AddCommGroup E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- All rows of a translation invariant matrix have the same total mass. -/
lemma tsum_eq_tsum_zero_of_translationInvariant {Q : E → E → ℝ≥0∞}
    (hhom : ∀ x y z, Q (x + z) (y + z) = Q x y) (x : E) : ∑' y, Q x y = ∑' y, Q 0 y := by
  have h : ∀ y : E, Q x y = Q 0 (y + -x) := fun y ↦ by
    rw [← sub_eq_add_neg]
    exact Kernel.apply_eq_apply_zero_sub_of_translationInvariant hhom x y
  calc ∑' y, Q x y = ∑' y, Q 0 (y + -x) := tsum_congr h
    _ = ∑' y, Q 0 y := by simpa using (Equiv.addRight (-x)).tsum_eq fun y ↦ Q 0 y
/-- The entries of the powers of a translation invariant matrix are bounded by the powers of the
common row sum `C = ∑_x Q(0, x)`. -/
lemma pow_apply_singleton_le_pow_tsum_of_translationInvariant {Q : E → E → ℝ≥0∞}
    (hhom : ∀ x y z, Q (x + z) (y + z) = Q x y) (n : ℕ) (x y : E) :
    (Kernel.ofMatrix Q ^ n) x {y} ≤ (∑' z, Q 0 z) ^ n := by
  induction n generalizing x y with
  | zero =>
    rw [Kernel.pow_zero_apply_singleton, pow_zero]
    rcases eq_or_ne x y with rfl | h
    · simp
    · rw [Set.indicator_of_notMem (by simpa using h)]
      exact zero_le_one
  | succ n ih =>
    rw [Kernel.ofMatrix_pow_succ_apply_singleton, pow_succ']
    calc ∑' b, Q x b * (Kernel.ofMatrix Q ^ n) b {y}
        ≤ ∑' b, Q x b * (∑' z, Q 0 z) ^ n :=
          ENNReal.tsum_le_tsum fun b ↦ mul_le_mul' le_rfl (ih b y)
      _ = (∑' b, Q x b) * (∑' z, Q 0 z) ^ n := ENNReal.tsum_mul_right
      _ = (∑' z, Q 0 z) * (∑' z, Q 0 z) ^ n := by
          rw [tsum_eq_tsum_zero_of_translationInvariant hhom]

/-- **Georgii (11.1) for a random walk matrix.** A positive translation invariant matrix with
summable rows satisfies `Q^n(x, y) < ∞`, hence defines the specification `γ^Q`. -/
lemma isTransferMatrix_of_translationInvariant {Q : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < Q x y)
    (hhom : ∀ x y z, Q (x + z) (y + z) = Q x y) (hC : ∑' z, Q 0 z ≠ ⊤) :
    IsTransferMatrix Q where
  pos := hpos
  pow_ne_top n x y := ne_top_of_le_ne_top
    (ENNReal.pow_ne_top (n := n + 1) hC)
    (pow_apply_singleton_le_pow_tsum_of_translationInvariant hhom (n + 1) x y)

/-- **Georgii, Corollary (11.19).** Let `E` be an infinite countable additive group and `Q` a
translation invariant positive matrix on `E` with `C = ∑_x Q(0, x) < ∞`. Then `𝒢(Q) = ∅`:
the specification `γ^Q` of a random walk transfer matrix has no Gibbs measure at all. -/
theorem eq_empty_G_transferSpecification_of_translationInvariant [Infinite E]
    {Q : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < Q x y)
    (hhom : ∀ x y z, Q (x + z) (y + z) = Q x y) (hC : ∑' z, Q 0 z ≠ ⊤) :
    G (transferSpecification Q (isTransferMatrix_of_translationInvariant hpos hhom hC)) = ∅ := by
  have hQ := isTransferMatrix_of_translationInvariant hpos hhom hC
  have hnotequiv : ¬ ∃ (P : E → E → ℝ≥0∞) (q : ℝ≥0∞) (r : E → ℝ≥0∞), 0 < q ∧ q ≠ ⊤ ∧
      (∀ x, 0 < r x) ∧ (∀ x, r x ≠ ⊤) ∧ (∀ x y, P x y = Q x y * r y / (q * r x)) ∧
      (∀ x, ∑' y, P x y = 1) ∧ Kernel.IsPositiveRecurrent (Kernel.ofMatrix P) := by
    rintro ⟨P, q, r, hq0, hqt, hr0, hrt, hPQ, hPstoch, hposrec⟩
    have hPpos : ∀ x y, 0 < P x y := fun x y ↦ by
      rw [hPQ]
      exact ENNReal.div_pos (ENNReal.mul_pos (hQ.pos x y).ne' (hr0 y).ne').ne'
        (ENNReal.mul_ne_top hqt (hrt x))
    have hMP : IsMarkovKernel (Kernel.ofMatrix P) := Kernel.isMarkovKernel_ofMatrix P hPstoch
    have hPirr : Kernel.IsIrreducible (Measure.count : Measure E) (Kernel.ofMatrix P) :=
      Kernel.isIrreducible_count_ofMatrix_of_forall_pos hPpos
    -- every translate of `P` is again stochastic and again equivalent to `Q`, hence equals `P`
    have hPhom : ∀ x y z, P (x + z) (y + z) = P x y := by
      intro x y z
      have hPzstoch : ∀ a, ∑' b, P (a + z) (b + z) = 1 := fun a ↦ by
        have h := (Equiv.addRight z).tsum_eq fun b ↦ P (a + z) b
        simpa using h.trans (hPstoch (a + z))
      have hMPz : IsMarkovKernel (Kernel.ofMatrix fun a b ↦ P (a + z) (b + z)) :=
        Kernel.isMarkovKernel_ofMatrix _ hPzstoch
      have hPz : ∀ a b : E, P (a + z) (b + z) = Q a b * r (b + z) / (q * r (a + z)) :=
        fun a b ↦ by rw [hPQ, hhom]
      have hEq := Kernel.eq_of_apply_eq_mul_div_of_apply_eq_mul_div_of_isRecurrent
        (Q := Q) (P := P) (P' := fun a b ↦ P (a + z) (b + z)) (r := r) (r' := fun w ↦ r (w + z))
        hq0.ne' hqt (fun x ↦ (hr0 x).ne') hrt (fun x ↦ (hr0 _).ne') (fun x ↦ hrt _)
        hPQ hPz hposrec.isRecurrent
      exact congrFun (congrFun hEq x) y
    exact Kernel.not_isPositiveRecurrent_ofMatrix_of_translationInvariant hPpos hPstoch hPhom
      hposrec
  refine eq_empty_G_of_forall_le_sum Q hQ hnotequiv (N := 1) one_pos (ε := Q 0 0) (hpos 0 0)
    fun y ↦ ?_
  rw [Finset.Icc_self, Finset.sum_singleton, pow_one, Kernel.ofMatrix_apply_singleton]
  have h : Q y y = Q 0 0 := by simpa using hhom 0 0 y
  exact h.ge

/-- **Georgii, Corollary (11.19), verbatim.** On `E = ℤ^N` a homogeneous positive matrix `Q`
with `C = ∑_x Q(0, x) < ∞` has `𝒢(Q) = ∅`. -/
theorem eq_empty_G_transferSpecification_randomWalk (N : ℕ) [NeZero N]
    {Q : (Fin N → ℤ) → (Fin N → ℤ) → ℝ≥0∞} (hpos : ∀ x y, 0 < Q x y)
    (hhom : ∀ x y z, Q (x + z) (y + z) = Q x y) (hC : ∑' z, Q 0 z ≠ ⊤) :
    G (transferSpecification Q (isTransferMatrix_of_translationInvariant hpos hhom hC)) = ∅ :=
  eq_empty_G_transferSpecification_of_translationInvariant hpos hhom hC

end RandomWalk

/-! ## Georgii, Comment (11.18)(2): the bounded-ratio condition excludes Corollary (11.17)

Georgii compares the uniqueness condition of Corollary (11.17), `inf_x ∑_{n=1}^N Q^n(x,x) > 0`,
with the one obtainable from Theorem (8.39): the existence of `u, v : E → ]0, ∞[` and `C > 1`
with `C^{-1} ≤ Q(x,y)/(u(x) v(y)) ≤ C`. The latter forces `∑_x ∑_{n=1}^N Q^n(x,x) < ∞` for every
`N`, because `∑_x Q^n(x,x) ≤ [C ∑_x u(x)v(x)]^n` and `C^{-2} u(a)v(a) ∑_x u(x)v(x) ≤ Q^2(a,a) <
∞`. On an infinite `E` a summable family has infimum `0`, so the two conditions exclude each
other. (Georgii writes `C^{-1}` in the second display; the two applications of the lower bound
give `C^{-2}`, which is what is proved here and is all that is used.)
-/

section BoundedRatio

variable {E : Type*} [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  {Q : E → E → ℝ≥0∞} {u v : E → ℝ≥0∞} {C : ℝ≥0∞}

/-- The upper half `Q(x,y) ≤ C u(x) v(y)` of Georgii's bounded-ratio condition propagates to the
powers: `Q^{n+1}(x,y) ≤ C^{n+1} u(x) W^n v(y)` with `W = ∑_z u(z) v(z)`. -/
lemma pow_succ_apply_singleton_le_of_le_mul
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (n : ℕ) (x y : E) :
    (Kernel.ofMatrix Q ^ (n + 1)) x {y} ≤ C ^ (n + 1) * u x * (∑' z, u z * v z) ^ n * v y := by
  induction n generalizing x y with
  | zero =>
    rw [Kernel.ofMatrix_pow_one_apply_singleton]
    calc Q x y ≤ C * (u x * v y) := hle x y
      _ = C ^ 1 * u x * (∑' z, u z * v z) ^ 0 * v y := by ring
  | succ n ih =>
    rw [Kernel.ofMatrix_pow_succ_apply_singleton]
    calc ∑' b, Q x b * (Kernel.ofMatrix Q ^ (n + 1)) b {y}
        ≤ ∑' b, (C * (u x * v b)) * (C ^ (n + 1) * u b * (∑' z, u z * v z) ^ n * v y) :=
          ENNReal.tsum_le_tsum fun b ↦ mul_le_mul' (hle x b) (ih b y)
      _ = (C ^ (n + 1 + 1) * u x * (∑' z, u z * v z) ^ n * v y) * ∑' b, u b * v b := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun b ↦ by ring
      _ = C ^ (n + 1 + 1) * u x * (∑' z, u z * v z) ^ (n + 1) * v y := by ring

/-- **Georgii, Comment (11.18)(2), second display.** `∑_x Q^{n+1}(x,x) ≤ [C ∑_x u(x)v(x)]^{n+1}`. -/
theorem tsum_pow_succ_apply_singleton_self_le_of_le_mul
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (n : ℕ) :
    ∑' x, (Kernel.ofMatrix Q ^ (n + 1)) x {x} ≤ (C * ∑' z, u z * v z) ^ (n + 1) := by
  calc ∑' x, (Kernel.ofMatrix Q ^ (n + 1)) x {x}
      ≤ ∑' x, C ^ (n + 1) * u x * (∑' z, u z * v z) ^ n * v x :=
        ENNReal.tsum_le_tsum fun x ↦ pow_succ_apply_singleton_le_of_le_mul hle n x x
    _ = (C ^ (n + 1) * (∑' z, u z * v z) ^ n) * ∑' x, u x * v x := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x ↦ by ring
    _ = (C * ∑' z, u z * v z) ^ (n + 1) := by rw [mul_pow]; ring

/-- **Georgii, Comment (11.18)(2), third display.** The lower half of the bounded-ratio condition
and the finiteness (11.1) of `Q^2(a,a)` force `∑_x u(x) v(x) < ∞`: the a priori measure `(uv)λ`
of the Gibbsian representation is *necessarily finite*. -/
theorem tsum_mul_ne_top_of_mul_le (hQ : IsTransferMatrix Q) (hCt : C ≠ ⊤)
    (hge : ∀ x y, u x * v y ≤ C * Q x y) {a : E} (hua : u a ≠ 0) (hva : v a ≠ 0) :
    ∑' z, u z * v z ≠ ⊤ := by
  have hbound : (u a * v a) * ∑' z, u z * v z ≤ C ^ 2 * (Kernel.ofMatrix Q ^ 2) a {a} := by
    rw [Kernel.ofMatrix_pow_two_apply_singleton, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun z ↦ ?_
    calc u a * v a * (u z * v z) = (u a * v z) * (u z * v a) := by ring
      _ ≤ (C * Q a z) * (C * Q z a) := mul_le_mul' (hge a z) (hge z a)
      _ = C ^ 2 * (Q a z * Q z a) := by ring
  intro htop
  rw [htop, ENNReal.mul_top (mul_ne_zero hua hva)] at hbound
  exact (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCt) (hQ.pow_two_ne_top a a))
    (top_le_iff.1 hbound)

/-- **Georgii, Comment (11.18)(2), conclusion.** On an *infinite* state space the bounded-ratio
condition of Theorem (8.39) and the condition `inf_x ∑_{n=1}^N Q^n(x,x) > 0` of Corollary (11.17)
exclude each other: the summability of `x ↦ ∑_{n=1}^N Q^n(x,x)` leaves the infimum equal to `0`. -/
theorem not_exists_pos_forall_le_sum_pow_of_bounded_ratio [Infinite E] (hQ : IsTransferMatrix Q)
    (hCt : C ≠ ⊤) (hu0 : ∀ x, u x ≠ 0) (hv0 : ∀ x, v x ≠ 0)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) (N : ℕ) :
    ¬ ∃ ε : ℝ≥0∞, 0 < ε ∧
      ∀ x, ε ≤ ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x} := by
  classical
  rintro ⟨ε, hε, hle'⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty E)
  have hW : ∑' z, u z * v z ≠ ⊤ := tsum_mul_ne_top_of_mul_le hQ hCt hge (hu0 a) (hv0 a)
  have hCW : C * ∑' z, u z * v z ≠ ⊤ := ENNReal.mul_ne_top hCt hW
  -- Georgii's summability, in the form `∑_x ∑_{n=1}^N Q^n(x,x) < ∞`
  have hfin : ∑' x : E, ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x} ≠ ⊤ := by
    rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
    refine (ENNReal.sum_lt_top.2 fun n hn ↦ ?_).ne
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      ⟨n - 1, by have := (Finset.mem_Icc.1 hn).1; omega⟩
    exact lt_of_le_of_lt (tsum_pow_succ_apply_singleton_self_le_of_le_mul hle m)
      (Ne.lt_top (ENNReal.pow_ne_top (n := m + 1) hCW))
  -- but a uniform positive lower bound over an infinite index set has infinite sum
  refine hfin (top_le_iff.1 ?_)
  calc (⊤ : ℝ≥0∞) = ∑' _ : E, ε := (ENNReal.tsum_const_eq_top_of_ne_zero hε.ne').symm
    _ ≤ ∑' x : E, ∑ n ∈ Finset.Icc 1 N, (Kernel.ofMatrix Q ^ n) x {x} :=
      ENNReal.tsum_le_tsum hle'

end BoundedRatio


/-! ### Georgii's Gibbsian representation of `γ^Q`, Comment (11.18)(2)

Under `C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` the specification `γ^Q` is the Gibbs specification of the
*bounded* nearest-neighbour potential `Φ_{{i,i+1}} = -log[Q(σ_i,σ_{i+1})/(u(σ_i)v(σ_{i+1}))]` for
the a priori measure `(uv)λ`. The proof factors the transfer weight
`ρ^Q_Λ = ∏_{j ∈ bondsOf Λ} Q(ω_j, ω_{j+1})` as
`e^{-H_Λ} · ∏_{i ∈ Λ} u(ω_i)v(ω_i) · (boundary weight)`, the boundary weight collecting the sites
of the bonds meeting `Λ` that lie outside `Λ`; the middle factor is the rescaling of the a priori
measure (Remark (1.28)(3)) and the last one drops out by
`Specification.lambdaSpecification_eq_of_mul_boundary`.
-/

section GibbsRepresentation

variable {E : Type*} [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  {Q : E → E → ℝ≥0∞} {u v : E → ℝ≥0∞}

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Every site of `Λ` is the right endpoint of a bond meeting `Λ`. -/
lemma subset_image_succ_bondsOf (Λ : Finset ℤ) : Λ ⊆ (bondsOf Λ).image (· + 1) := by
  intro j hj
  refine Finset.mem_image.2 ⟨j - 1, mem_bondsOf.2 (Or.inr ?_), by omega⟩
  simpa using hj

variable (Q u v) in
/-- **Georgii's bond weight** `M(x, y) = Q(x, y)/(u(x) v(y))` of Comment (11.18)(2), as a real
matrix; the potential of the Comment is `markovPotential (ratioMatrix Q u v)`. -/
def ratioMatrix : Matrix E E ℝ := fun x y ↦ (Q x y / (u x * v y)).toReal

variable (u v) in
/-- **Georgii's boundary weight.** The `u`-weight of the left endpoints and the `v`-weight of the
right endpoints of the bonds meeting `Λ`, restricted to the sites outside `Λ`. -/
def boundaryWeight (Λ : Finset ℤ) (ω : ℤ → E) : ℝ≥0∞ :=
  (∏ j ∈ bondsOf Λ \ Λ, u (ω j)) * ∏ j ∈ (bondsOf Λ).image (· + 1) \ Λ, v (ω j)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma ofReal_ratioMatrix_mul (hu0 : ∀ x, u x ≠ 0) (hv0 : ∀ x, v x ≠ 0)
    (hQt : ∀ x y, Q x y ≠ ⊤) (hut : ∀ x, u x ≠ ⊤) (hvt : ∀ x, v x ≠ ⊤) (x y : E) :
    ENNReal.ofReal (ratioMatrix Q u v x y) * (u x * v y) = Q x y := by
  rw [ratioMatrix, ENNReal.ofReal_toReal (ENNReal.div_ne_top (hQt x y) (mul_ne_zero (hu0 x)
    (hv0 y))), ENNReal.div_mul_cancel (mul_ne_zero (hu0 x) (hv0 y))
    (ENNReal.mul_ne_top (hut x) (hvt y))]

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma ratioMatrix_pos (hQ0 : ∀ x y, Q x y ≠ 0) (hQt : ∀ x y, Q x y ≠ ⊤) (hu0 : ∀ x, u x ≠ 0)
    (hv0 : ∀ x, v x ≠ 0) (hut : ∀ x, u x ≠ ⊤) (hvt : ∀ x, v x ≠ ⊤) (x y : E) :
    0 < ratioMatrix Q u v x y :=
  ENNReal.toReal_pos
    (by simp [ENNReal.div_eq_zero_iff, hQ0 x y, ENNReal.mul_ne_top (hut x) (hvt y)])
    (ENNReal.div_ne_top (hQt x y) (mul_ne_zero (hu0 x) (hv0 y)))

omit [Countable E] [MeasurableSingletonClass E] in
/-- **The factorisation of the transfer weight.** `ρ^Q_Λ = e^{-H_Λ} · ∏_{i ∈ Λ} u(ω_i)v(ω_i) ·
(boundary weight)`. -/
theorem transferWeight_eq_mul_boundaryWeight (hu0 : ∀ x, u x ≠ 0) (hv0 : ∀ x, v x ≠ 0)
    (hQ0 : ∀ x y, Q x y ≠ 0) (hQt : ∀ x y, Q x y ≠ ⊤) (hut : ∀ x, u x ≠ ⊤) (hvt : ∀ x, v x ≠ ⊤)
    (Λ : Finset ℤ) (ω : ℤ → E) :
    transferWeight Q Λ ω
      = ((markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ ω *
          Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ ω)
        * boundaryWeight u v Λ ω := by
  classical
  set M := ratioMatrix Q u v with hM
  have hMpos : ∀ x y, 0 < M x y := fun x y ↦ ratioMatrix_pos hQ0 hQt hu0 hv0 hut hvt x y
  set B := bondsOf Λ with hB
  set B' := B.image (· + 1) with hB'
  have hΛB : Λ ⊆ B := subset_bondsOf Λ
  have hΛB' : Λ ⊆ B' := subset_image_succ_bondsOf Λ
  have hprodv : ∏ j ∈ B', v (ω j) = ∏ j ∈ B, v (ω (j + 1)) :=
    Finset.prod_image fun i _ j _ h ↦ by omega
  have hfactor : transferWeight Q Λ ω
      = (∏ j ∈ B, ENNReal.ofReal (M (ω j) (ω (j + 1)))) *
          ((∏ j ∈ B, u (ω j)) * ∏ j ∈ B', v (ω j)) := by
    rw [transferWeight_eq_prod_bondsOf, hprodv, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ ↦
      (ofReal_ratioMatrix_mul hu0 hv0 hQt hut hvt (ω j) (ω (j + 1))).symm
  have hu_split : ∏ j ∈ B, u (ω j) = (∏ j ∈ B \ Λ, u (ω j)) * ∏ j ∈ Λ, u (ω j) :=
    (Finset.prod_sdiff hΛB).symm
  have hv_split : ∏ j ∈ B', v (ω j) = (∏ j ∈ B' \ Λ, v (ω j)) * ∏ j ∈ Λ, v (ω j) :=
    (Finset.prod_sdiff hΛB').symm
  rw [hfactor, boltzmannFactor_eq_prod_bondsOf hMpos,
    ENNReal.ofReal_prod_of_nonneg fun j _ ↦ (hMpos _ _).le, ← hB, hu_split, hv_split,
    Specification.lambdaWeight, Finset.prod_mul_distrib, boundaryWeight, ← hB, ← hB']
  ring


omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma boundaryWeight_ne_zero (hu0 : ∀ x, u x ≠ 0) (hv0 : ∀ x, v x ≠ 0) (Λ : Finset ℤ)
    (ω : ℤ → E) : boundaryWeight u v Λ ω ≠ 0 := by
  classical
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ ↦ hu0 _)
    (Finset.prod_ne_zero_iff.2 fun j _ ↦ hv0 _)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
lemma boundaryWeight_ne_top (hut : ∀ x, u x ≠ ⊤) (hvt : ∀ x, v x ≠ ⊤) (Λ : Finset ℤ)
    (ω : ℤ → E) : boundaryWeight u v Λ ω ≠ ⊤ := by
  classical
  exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun j _ ↦ hut _)
    (ENNReal.prod_ne_top fun j _ ↦ hvt _)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The boundary weight of `Λ` only involves sites outside `Λ`. -/
lemma dependsOn_boundaryWeight (Λ : Finset ℤ) :
    DependsOn (boundaryWeight u v Λ) ((Λ : Set ℤ)ᶜ) := by
  classical
  intro ω τ h
  unfold boundaryWeight
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun j hj ↦ ?_)
    (Finset.prod_congr rfl fun j hj ↦ ?_) <;>
    rw [h j (by simpa using (Finset.mem_sdiff.1 hj).2)]

/-! ### The bounded-ratio hypothesis gives the two instances Georgii's potential needs -/

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- Under `C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` the bond energies are bounded by `log C`: Georgii's
potential is a *bounded* nearest-neighbour potential. -/
lemma abs_log_ratioMatrix_le {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤)
    (hQ0 : ∀ x y, Q x y ≠ 0) (hQt : ∀ x y, Q x y ≠ ⊤) (hu0 : ∀ x, u x ≠ 0)
    (hut : ∀ x, u x ≠ ⊤) (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) (x y : E) :
    |Real.log (ratioMatrix Q u v x y)| ≤ Real.log C.toReal := by
  have hCt1 : (1 : ℝ) ≤ C.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hCt hC1
  have hCt0 : (0 : ℝ) < C.toReal := lt_of_lt_of_le zero_lt_one hCt1
  have hQr : (0 : ℝ) < (Q x y).toReal := ENNReal.toReal_pos (hQ0 x y) (hQt x y)
  have hur : (0 : ℝ) < (u x).toReal := ENNReal.toReal_pos (hu0 x) (hut x)
  have hvr : (0 : ℝ) < (v y).toReal := ENNReal.toReal_pos (hv0 y) (hvt y)
  have hMeq : ratioMatrix Q u v x y = (Q x y).toReal / ((u x).toReal * (v y).toReal) := by
    rw [ratioMatrix, ENNReal.toReal_div, ENNReal.toReal_mul]
  have h1 : (Q x y).toReal ≤ C.toReal * ((u x).toReal * (v y).toReal) := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hCt (ENNReal.mul_ne_top (hut x) (hvt y))) (hle x y)
    simpa [ENNReal.toReal_mul] using h
  have h2 : (u x).toReal * (v y).toReal ≤ C.toReal * (Q x y).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hCt (hQt x y)) (hge x y)
    simpa [ENNReal.toReal_mul] using h
  have hMpos : 0 < ratioMatrix Q u v x y := by
    rw [hMeq]; positivity
  have hub : ratioMatrix Q u v x y ≤ C.toReal := by
    rw [hMeq, div_le_iff₀ (by positivity)]
    linarith
  have hlb : (C.toReal)⁻¹ ≤ ratioMatrix Q u v x y := by
    rw [hMeq, ← one_div, div_le_div_iff₀ hCt0 (by positivity)]
    linarith
  refine abs_le.2 ⟨?_, Real.log_le_log hMpos hub⟩
  calc -Real.log C.toReal = Real.log (C.toReal)⁻¹ := (Real.log_inv _).symm
    _ ≤ Real.log (ratioMatrix Q u v x y) := Real.log_le_log (by positivity) hlb

omit [Countable E] [MeasurableSingletonClass E] in
/-- **Georgii's potential of Comment (11.18)(2) is absolutely summable.** -/
lemma isAbsolutelySummable_markovPotential_ratioMatrix {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤)
    (hQ0 : ∀ x y, Q x y ≠ 0) (hQt : ∀ x y, Q x y ≠ ⊤) (hu0 : ∀ x, u x ≠ 0)
    (hut : ∀ x, u x ≠ ⊤) (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) :
    (markovPotential (ratioMatrix Q u v)).IsAbsolutelySummable :=
  isAbsolutelySummable_markovPotential_of_abs_log_le _
    (abs_log_ratioMatrix_le hC1 hCt hQ0 hQt hu0 hut hv0 hvt hle hge)

omit [Countable E] in
/-- **Georgii's a priori measure `(uv)λ` is finite**, `λ` being counting measure. -/
lemma isFiniteMeasure_count_withDensity_mul (hW : ∑' z, u z * v z ≠ ⊤) :
    IsFiniteMeasure ((Measure.count : Measure E).withDensity fun x ↦ u x * v x) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_count]
  exact hW.lt_top

omit [Countable E] in
/-- `(uv)λ` is non-zero. -/
lemma neZero_count_withDensity_mul [Nonempty E] (hu0 : ∀ x, u x ≠ 0) (hv0 : ∀ x, v x ≠ 0) :
    NeZero ((Measure.count : Measure E).withDensity fun x ↦ u x * v x) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty E)
  refine ⟨fun h ↦ ?_⟩
  have := Measure.count_withDensity_apply_singleton (fun x ↦ u x * v x) a
  rw [h] at this
  exact mul_ne_zero (hu0 a) (hv0 a) this.symm

/-! ### The representation itself -/

variable [Nonempty E]

omit [Nonempty E] in
/-- The pre-modification `e^{-H_Λ} ∏_{i ∈ Λ} u(ω_i)v(ω_i)` obtained from Georgii's potential by
undoing the rescaling of the a priori measure. -/
lemma isPremodifier_boltzmannFactor_mul_lambdaWeight :
    Specification.IsPremodifier (S := ℤ) (E := E) (fun Λ ω ↦
      (markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ ω *
        Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ ω) where
  measurable Λ :=
    (Potential.measurable_boltzmannFactor (Φ := markovPotential (ratioMatrix Q u v)) 1 Λ).mul
      (Specification.measurable_lambdaWeight (S := ℤ) (E := E)
        (fun _ ↦ measurable_of_countable _) Λ)
  comm_of_subset := by
    intro Λ₁ Λ₂ ζ η hΛ hrestrict
    have hb := (Potential.isPremodifier_boltzmannFactor
      (Φ := markovPotential (ratioMatrix Q u v)) 1).comm_of_subset hΛ hrestrict
    have hw := Specification.lambdaWeight_mul_comm_of_subset (S := ℤ) (E := E)
      (r := fun _ x ↦ u x * v x) hΛ hrestrict
    calc ((markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₂ ζ *
            Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₂ ζ) *
          ((markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₁ η *
            Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₁ η)
        = ((markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₂ ζ *
              (markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₁ η) *
            (Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₂ ζ *
              Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₁ η) := by
          ring
      _ = ((markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₁ ζ *
              (markovPotential (ratioMatrix Q u v)).boltzmannFactor 1 Λ₂ η) *
            (Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₁ ζ *
              Specification.lambdaWeight (S := ℤ) (E := E) (fun _ x ↦ u x * v x) Λ₂ η) := by
          rw [hb, hw]
      _ = _ := by ring

/-- **Georgii, Comment (11.18)(2), the Gibbsian representation.** Under
`C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` the specification `γ^Q` *is* the Gibbs specification of the
bounded nearest-neighbour potential `Φ_{{i,i+1}} = -log[Q(σ_i,σ_{i+1})/(u(σ_i)v(σ_{i+1}))]` for
the (necessarily finite) a priori measure `(uv)λ`, `λ` counting measure. The three instance
arguments are supplied by `isAbsolutelySummable_markovPotential_ratioMatrix`,
`isFiniteMeasure_count_withDensity_mul` (via `tsum_mul_ne_top_of_mul_le`) and
`neZero_count_withDensity_mul`. -/
theorem transferSpecification_eq_gibbsSpecificationOfFiniteReference
    [(markovPotential (ratioMatrix Q u v)).IsAbsolutelySummable]
    [IsFiniteMeasure ((Measure.count : Measure E).withDensity fun x ↦ u x * v x)]
    [NeZero ((Measure.count : Measure E).withDensity fun x ↦ u x * v x)]
    (hQ : IsTransferMatrix Q) (hu0 : ∀ x, u x ≠ 0) (hut : ∀ x, u x ≠ ⊤)
    (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤) :
    transferSpecification Q hQ
      = Potential.gibbsSpecificationOfFiniteReference (markovPotential (ratioMatrix Q u v))
          ((Measure.count : Measure E).withDensity fun x ↦ u x * v x) 1 := by
  classical
  set Φ := markovPotential (ratioMatrix Q u v) with hΦ
  set w : E → ℝ≥0∞ := fun x ↦ u x * v x with hwdef
  set ρ₁ : Finset ℤ → (ℤ → E) → ℝ≥0∞ := fun Λ ω ↦ Φ.boltzmannFactor 1 Λ ω *
    Specification.lambdaWeight (S := ℤ) (E := E) (fun _ ↦ w) Λ ω with hρ₁def
  have hQ0 : ∀ x y, Q x y ≠ 0 := fun x y ↦ (hQ.pos x y).ne'
  have hQt : ∀ x y, Q x y ≠ ⊤ := hQ.ne_top
  have hw0 : ∀ x, w x ≠ 0 := fun x ↦ mul_ne_zero (hu0 x) (hv0 x)
  have hwt : ∀ x, w x ≠ ⊤ := fun x ↦ ENNReal.mul_ne_top (hut x) (hvt x)
  have hwmeas : Measurable w := measurable_of_countable _
  have hfact : ∀ (Λ : Finset ℤ) (ω : ℤ → E),
      transferWeight Q Λ ω = ρ₁ Λ ω * boundaryWeight u v Λ ω :=
    fun Λ ω ↦ transferWeight_eq_mul_boundaryWeight hu0 hv0 hQ0 hQt hut hvt Λ ω
  have hρ₁ : Specification.IsPremodifier (S := ℤ) (E := E) ρ₁ :=
    isPremodifier_boltzmannFactor_mul_lambdaWeight
  have hd0 := boundaryWeight_ne_zero (u := u) (v := v) hu0 hv0
  have hdt := boundaryWeight_ne_top (u := u) (v := v) hut hvt
  have hdep := dependsOn_boundaryWeight (u := u) (v := v) (E := E)
  -- admissibility of `ρ₁` for counting measure, from that of the transfer weights
  have hZ₁ : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) Measure.count ρ₁ := by
    intro Λ η
    have hZ := Specification.sigmaFiniteLambdaZ_mul_boundary (S := ℤ) (E := E) Measure.count
      hρ₁.measurable (isPremodifier_transferWeight Q).measurable hdep hfact Λ η
    have h0 := (hQ.isSigmaFiniteLambdaAdmissible Λ η).1
    have ht := (hQ.isSigmaFiniteLambdaAdmissible Λ η).2
    constructor
    · intro h; rw [h, zero_mul] at hZ; exact h0 hZ
    · intro h; rw [h, ENNReal.top_mul (hd0 Λ η)] at hZ; exact ht hZ
  -- (i) the boundary weight drops out
  have h3 : transferSpecification Q hQ
      = Specification.lambdaSpecification (S := ℤ) (E := E) Measure.count ρ₁ hρ₁ hZ₁ :=
    Specification.lambdaSpecification_eq_of_mul_boundary (S := ℤ) (E := E) Measure.count hρ₁ hZ₁
      (isPremodifier_transferWeight Q) hQ.isSigmaFiniteLambdaAdmissible hd0 hdt hdep hfact
  -- (ii) undoing the rescaling of the a priori measure
  have hrescale : Specification.rescale (S := ℤ) (E := E) w ρ₁ = Φ.boltzmannFactor 1 := by
    funext Λ ω
    rw [Specification.rescale_apply, hρ₁def, mul_div_assoc,
      ENNReal.div_self (Specification.lambdaWeight_ne_zero (S := ℤ) (E := E) (fun _ _ ↦ hw0 _) Λ ω)
        (Specification.lambdaWeight_ne_top (S := ℤ) (E := E) (fun _ _ ↦ hwt _) Λ ω), mul_one]
  have h2 := Specification.lambdaSpecification_eq_lambdaSpecification_withDensity (S := ℤ) (E := E)
    Measure.count hwmeas hw0 hwt hρ₁ hZ₁
  rw [h3, h2, Potential.gibbsSpecificationOfFiniteReference,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible]
  exact Specification.lambdaSpecification_congr (S := ℤ) (E := E) _ hrescale _ _ _ _

/-- **Georgii, Comment (11.18)(2), the Gibbsian representation**, with the three instance
arguments discharged from the bounded-ratio hypothesis alone. -/
theorem transferSpecification_eq_gibbsSpecification_of_bounded_ratio
    (hQ : IsTransferMatrix Q) {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤)
    (hu0 : ∀ x, u x ≠ 0) (hut : ∀ x, u x ≠ ⊤) (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) :
    haveI := isAbsolutelySummable_markovPotential_ratioMatrix hC1 hCt
      (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt hle hge
    haveI := isFiniteMeasure_count_withDensity_mul (u := u) (v := v)
      (tsum_mul_ne_top_of_mul_le hQ hCt hge (hu0 (Classical.arbitrary E))
        (hv0 (Classical.arbitrary E)))
    haveI := neZero_count_withDensity_mul hu0 hv0
    transferSpecification Q hQ
      = Potential.gibbsSpecificationOfFiniteReference (markovPotential (ratioMatrix Q u v))
          ((Measure.count : Measure E).withDensity fun x ↦ u x * v x) 1 := by
  have := isAbsolutelySummable_markovPotential_ratioMatrix hC1 hCt
    (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt hle hge
  have := isFiniteMeasure_count_withDensity_mul (u := u) (v := v)
    (tsum_mul_ne_top_of_mul_le hQ hCt hge (hu0 (Classical.arbitrary E))
      (hv0 (Classical.arbitrary E)))
  have := neZero_count_withDensity_mul (u := u) (v := v) hu0 hv0
  exact transferSpecification_eq_gibbsSpecificationOfFiniteReference hQ hu0 hut hv0 hvt

/-! ### Georgii, Comment (11.18)(2): `|𝒢(γ^Q)| = 1`

The representation above exhibits `γ^Q` as the Gibbs specification of the *bounded*
nearest-neighbour potential `Φ_{{i,i+1}} = -log[Q(σ_i,σ_{i+1})/(u(σ_i)v(σ_{i+1}))]`. Georgii's
condition (8.40), `sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞`, is immediate for such a potential:
only the bond `{i, i+1}` spans the site `i`, so the sum is the single oscillation
`δ(Φ_{{i,i+1}}) ≤ 2 log C`. Theorem (8.39) then gives uniqueness and — over a countable, hence
standard Borel, state space — existence as well.
-/

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- Only the bond `{i, i+1}` spans the site `i`, so Georgii's sum (8.40) at `i` reduces, for a
homogeneous nearest-neighbour potential, to the oscillation of that single bond. -/
lemma oscSpan_markovPotential (M : Matrix E E ℝ) (i : ℤ) :
    oscSpan (markovPotential M) i = Dobrushin.osc (markovPotential M {i, i + 1}) := by
  rw [oscSpan, tsum_eq_single ({i, i + 1} : Finset ℤ) ?_]
  · exact Set.indicator_of_mem
      (show ({i, i + 1} : Finset ℤ) ∈ {A : Finset ℤ | Spans A i} from
        ⟨⟨i, by simp, le_rfl⟩, ⟨i + 1, by simp, by omega⟩⟩) _
  · intro A hA
    by_cases hspan : Spans A i
    · rw [Set.indicator_of_mem (show A ∈ {A : Finset ℤ | Spans A i} from hspan)]
      by_cases hpair : ∃ j : ℤ, A = {j, j + 1}
      · exfalso
        obtain ⟨j, rfl⟩ := hpair
        obtain ⟨⟨a, ha, hai⟩, b, hb, hib⟩ := hspan
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        exact hA (by rw [show j = i by omega])
      · rw [show markovPotential M A = fun _ ↦ (0 : ℝ) from
          funext fun σ ↦ markovPotential_of_not_pair M hpair σ, Dobrushin.osc_const]
    · exact Set.indicator_of_notMem (show A ∉ {A : Finset ℤ | Spans A i} from hspan) _

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- A bond energy bounded by `c` oscillates by at most `2c`. -/
lemma osc_markovPotential_pair_le (M : Matrix E E ℝ) {c : ℝ}
    (hM : ∀ x y, |Real.log (M x y)| ≤ c) (i : ℤ) :
    Dobrushin.osc (markovPotential M {i, i + 1}) ≤ ENNReal.ofReal (2 * c) := by
  refine Dobrushin.osc_le fun ζ η ↦ ENNReal.ofReal_le_ofReal ?_
  have h1 := hM (ζ i) (ζ (i + 1))
  have h2 := hM (η i) (η (i + 1))
  rw [abs_le] at h1 h2
  rw [markovPotential_pair, markovPotential_pair, abs_le]
  constructor <;> linarith

omit [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- **Georgii's condition (8.40) for a bounded nearest-neighbour potential.** If the bond energies
of `markovPotential M` are uniformly bounded then `sup_i ∑_{A : min A ≤ i < max A} δ(Φ_A) < ∞`. -/
theorem iSup_oscSpan_markovPotential_ne_top (M : Matrix E E ℝ) {c : ℝ}
    (hM : ∀ x y, |Real.log (M x y)| ≤ c) :
    ⨆ i : ℤ, oscSpan (markovPotential M) i ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (iSup_le fun i ↦ (oscSpan_markovPotential M i).trans_le
      (osc_markovPotential_pair_le M hM i))

/-- **Georgii, Comment (11.18)(2), the uniqueness half.** Under `C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C`
the specification `γ^Q` has at most one Gibbs measure: by
`transferSpecification_eq_gibbsSpecification_of_bounded_ratio` it is the Gibbs specification of the
nearest-neighbour potential `-log[Q/(uv)]`, whose bond energies are bounded by `log C`, so
Georgii's condition (8.40) holds and Theorem (8.39) applies. -/
theorem subsingleton_G_transferSpecification_of_bounded_ratio
    (hQ : IsTransferMatrix Q) {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤)
    (hu0 : ∀ x, u x ≠ 0) (hut : ∀ x, u x ≠ ⊤) (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) :
    (G (transferSpecification Q hQ)).Subsingleton := by
  have := isAbsolutelySummable_markovPotential_ratioMatrix hC1 hCt
    (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt hle hge
  have := isFiniteMeasure_count_withDensity_mul (u := u) (v := v)
    (tsum_mul_ne_top_of_mul_le hQ hCt hge (hu0 (Classical.arbitrary E))
      (hv0 (Classical.arbitrary E)))
  have := neZero_count_withDensity_mul (u := u) (v := v) hu0 hv0
  rw [transferSpecification_eq_gibbsSpecificationOfFiniteReference hQ hu0 hut hv0 hvt,
    Potential.gibbsSpecificationOfFiniteReference,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible]
  exact subsingleton_G_lambdaSpecification_of_iSup_oscSpan_ne_top hasBoundedBoundary_int _ 1 _
    (iSup_oscSpan_markovPotential_ne_top _
      (abs_log_ratioMatrix_le hC1 hCt (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt
        hle hge))

/-- **Georgii, Comment (11.18)(2), in full: `|𝒢(γ^Q)| = 1`.** For a positive matrix `Q` with finite
powers on a countable state space, the existence of `u, v : E → ]0, ∞[` and `C ≥ 1` with
`C^{-1} ≤ Q(x,y)/(u(x)v(y)) ≤ C` forces `γ^Q` to have exactly one Gibbs measure. Uniqueness is
Theorem (8.39); existence is its second half, available because a countable state space with
measurable singletons is standard Borel. -/
theorem existsUnique_mem_GP_transferSpecification_of_bounded_ratio
    (hQ : IsTransferMatrix Q) {C : ℝ≥0∞} (hC1 : 1 ≤ C) (hCt : C ≠ ⊤)
    (hu0 : ∀ x, u x ≠ 0) (hut : ∀ x, u x ≠ ⊤) (hv0 : ∀ x, v x ≠ 0) (hvt : ∀ x, v x ≠ ⊤)
    (hle : ∀ x y, Q x y ≤ C * (u x * v y)) (hge : ∀ x y, u x * v y ≤ C * Q x y) :
    ∃! μ : ProbabilityMeasure (ℤ → E), μ ∈ GP (transferSpecification Q hQ) := by
  have := isAbsolutelySummable_markovPotential_ratioMatrix hC1 hCt
    (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt hle hge
  have := isFiniteMeasure_count_withDensity_mul (u := u) (v := v)
    (tsum_mul_ne_top_of_mul_le hQ hCt hge (hu0 (Classical.arbitrary E))
      (hv0 (Classical.arbitrary E)))
  have := neZero_count_withDensity_mul (u := u) (v := v) hu0 hv0
  rw [transferSpecification_eq_gibbsSpecificationOfFiniteReference hQ hu0 hut hv0 hvt,
    Potential.gibbsSpecificationOfFiniteReference,
    Potential.gibbsSpecificationOfSigmaFiniteAdmissible]
  exact existsUnique_mem_GP_lambdaSpecification_of_iSup_oscSpan_ne_top hasBoundedBoundary_int _ 1 _
    (iSup_oscSpan_markovPotential_ne_top _
      (abs_log_ratioMatrix_le hC1 hCt (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top hu0 hut hv0 hvt
        hle hge))

end GibbsRepresentation

end MeasureTheory.GibbsMeasure.Markov

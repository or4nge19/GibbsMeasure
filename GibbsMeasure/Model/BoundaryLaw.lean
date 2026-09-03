/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Probability.Kernel.CountableMatrix
public import GibbsMeasure.Model.MarkovChain

/-!
# Georgii §11.1: transfer matrices and boundary laws on `ℤ`

Sites `ℤ`, a *countable* state space `E`, and counting measure as a priori measure. A positive
matrix `Q` on `E` with finite powers (Georgii (11.1)) defines the positive homogeneous Markov
specification `γ^Q` of (11.2)–(11.3), and a boundary law `{ℓ_i, r_i}` for `Q` (Definition (11.8))
defines, through Kolmogorov's extension theorem, a probability measure `μ` on `E^ℤ` with the
cylinder probabilities (11.10); Theorem (11.9)(a) is `μ ∈ 𝒢(γ^Q)`.

The matrix `Q` is the Mathlib kernel `ProbabilityTheory.Kernel.ofMatrix Q`
(`GibbsMeasure/Mathlib/Probability/Kernel/CountableMatrix.lean`): powers are the powers in the
monoid `Kernel E E`, and (11.1) is finiteness of their entries.

## Main declarations

* `Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq`: Georgii (1.33)
  for the λ-specification of a σ-finite a priori measure: `μ ∈ 𝒢(γ)` iff `μ γ_{i} = μ` for all `i`.
* `Specification.lintegral_sigmaFiniteLambdaFun_count_insert`: the counting-measure reference
  kernel `λ_{Λ ∪ {j}}` integrates by summing the free coordinate `j`.
* `MeasureTheory.GibbsMeasure.Markov.transferWeight Q Λ`: `∏_{bonds meeting Λ} Q(σ_j, σ_{j+1})`,
  the pre-modification defining `γ^Q`; `isPremodifier_transferWeight`.
* `MeasureTheory.GibbsMeasure.Markov.IsTransferMatrix Q`: `Q` is positive with finite powers,
  Georgii (11.1).
* `MeasureTheory.GibbsMeasure.Markov.sigmaFiniteLambdaZ_transferWeight_Icc`: the partition
  function of an interval is the corresponding entry of a power of `Q`.
* `MeasureTheory.GibbsMeasure.Markov.transferSpecification Q hQ`: **Georgii's `γ^Q`**, the
  λ-specification of `transferWeight Q` for counting measure;
  `transferSpecification_Icc_apply_intervalCylinder` is **(11.2)** and
  `transferSpecification_apply_cyl_union` is **(11.3)**.
* `MeasureTheory.GibbsMeasure.Markov.transferSpecification_eq_iff`: **Georgii Remark (11.4)**,
  `γ^P = γ^Q` iff `P(x,y) = Q(x,y) r(y)/(q r(x))` (11.5).
* `MeasureTheory.GibbsMeasure.Markov.IsBoundaryLaw Q ℓ r`: **Georgii Definition (11.8)**.
* `MeasureTheory.GibbsMeasure.Markov.boundaryLawMeasure`: the measure (11.10);
  `boundaryLawMeasure_intervalCylinder` is (11.10) and `isProbabilityMeasure_boundaryLawMeasure`,
  `eq_boundaryLawMeasure_of_forall_intervalCylinder` its uniqueness.
* `MeasureTheory.GibbsMeasure.Markov.isGibbsMeasure_transferSpecification_boundaryLawMeasure`:
  **Georgii Theorem (11.9)(a)**, `μ ∈ 𝒢(Q)`.
* `MeasureTheory.GibbsMeasure.Markov.markovSpecification_eq_transferSpecification`,
  `stationaryChain_eq_boundaryLawMeasure`: the finite-state theory of Chapter 3 is the instance
  `Q = P` stochastic, `ℓ_i = α_P`, `r_i = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-! ## Georgii's `γ^Q`: the transfer matrix as a pre-modification

The counting-measure reference kernel `λ_Λ(·|η)` and its calculus (`lintegral_lambdaCount`,
`setLIntegral_lambdaCount_cyl`, `cyl`, …) live in `GibbsMeasure/Specification/CountingKernel.lean`
for an arbitrary site space; here they are used at `S = ℤ`. -/

namespace MeasureTheory.GibbsMeasure.Markov

variable {E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

local notation "λ₀" => Specification.sigmaFiniteLambdaFun (S := ℤ) (E := E) Measure.count

section TransferWeight

variable (Q : E → E → ℝ≥0∞)

lemma measurable_bond (j : ℤ) : Measurable fun σ : ℤ → E ↦ Q (σ j) (σ (j + 1)) :=
  measurable_pair Q j (j + 1)

/-- Georgii (11.2)–(11.3) before normalisation: the weight
`ρ^Q_Λ(σ) = ∏_{j ∈ bondsOf Λ} Q(σ_j, σ_{j+1})` of the bonds meeting `Λ`. For `Q = e^{-Φ}` with `Φ`
the nearest-neighbour potential of the transfer matrix `Q`, this is the Boltzmann factor
`e^{-H_Λ}`. -/
def transferWeight (Λ : Finset ℤ) (σ : ℤ → E) : ℝ≥0∞ := ∏ j ∈ bondsOf Λ, Q (σ j) (σ (j + 1))

lemma measurable_transferWeight (Λ : Finset ℤ) : Measurable (transferWeight Q Λ) :=
  Finset.measurable_prod _ fun j _ ↦ measurable_bond Q j

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma transferWeight_pos (hQ : ∀ x y, 0 < Q x y) (Λ : Finset ℤ) (σ : ℤ → E) :
    0 < transferWeight Q Λ σ :=
  pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦ (hQ _ _).ne')

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma transferWeight_ne_top (hQ : ∀ x y, Q x y ≠ ⊤) (Λ : Finset ℤ) (σ : ℤ → E) :
    transferWeight Q Λ σ ≠ ⊤ :=
  (ENNReal.prod_lt_top fun _ _ ↦ (hQ _ _).lt_top).ne

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma transferWeight_congr {Λ : Finset ℤ} {σ τ : ℤ → E}
    (h : ∀ j ∈ bondsOf Λ, σ j = τ j ∧ σ (j + 1) = τ (j + 1)) :
    transferWeight Q Λ σ = transferWeight Q Λ τ :=
  Finset.prod_congr rfl fun j hj ↦ by rw [(h j hj).1, (h j hj).2]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma bondsOf_mono {Λ₁ Λ₂ : Finset ℤ} (h : Λ₁ ⊆ Λ₂) : bondsOf Λ₁ ⊆ bondsOf Λ₂ := fun _ hj ↦ by
  rw [mem_bondsOf] at hj ⊢
  exact hj.imp (fun h' ↦ h h') fun h' ↦ h h'

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The transfer weights form a pre-modification (Georgii (1.28)(5)): the weights of the bonds
not meeting `Λ₁` factor out. -/
lemma transferWeight_mul_comm_of_subset {Λ₁ Λ₂ : Finset ℤ} (hΛ : Λ₁ ⊆ Λ₂) {ζ η : ℤ → E}
    (h : ∀ s ∉ Λ₁, ζ s = η s) :
    transferWeight Q Λ₂ ζ * transferWeight Q Λ₁ η
      = transferWeight Q Λ₁ ζ * transferWeight Q Λ₂ η := by
  have hsplit : ∀ ω : ℤ → E, transferWeight Q Λ₂ ω
      = (∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, Q (ω j) (ω (j + 1))) * transferWeight Q Λ₁ ω := fun ω ↦
    (Finset.prod_sdiff (bondsOf_mono hΛ)).symm
  have hdiff : (∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, Q (ζ j) (ζ (j + 1)))
      = ∏ j ∈ bondsOf Λ₂ \ bondsOf Λ₁, Q (η j) (η (j + 1)) :=
    Finset.prod_congr rfl fun j hj ↦ by
      have hj' := (Finset.mem_sdiff.1 hj).2
      rw [mem_bondsOf, not_or] at hj'
      rw [h j hj'.1, h (j + 1) hj'.2]
  rw [hsplit ζ, hsplit η, hdiff]
  ring

lemma isPremodifier_transferWeight : Specification.IsPremodifier (transferWeight Q) where
  measurable := measurable_transferWeight Q
  comm_of_subset _ _ _ _ hΛ h := transferWeight_mul_comm_of_subset Q hΛ h

end TransferWeight

/-! ## Positive matrices with finite powers: Georgii (11.1) -/

/-- **Georgii (11.1).** A positive matrix `Q` on `E` all of whose powers `Q^n`, `n ≥ 1`, have
finite entries; the powers are those of the kernel `ofMatrix Q` in the monoid `Kernel E E`. -/
structure IsTransferMatrix (Q : E → E → ℝ≥0∞) : Prop where
  pos : ∀ x y, 0 < Q x y
  pow_ne_top : ∀ (n : ℕ) (x y : E), (Kernel.ofMatrix Q ^ (n + 1)) x {y} ≠ ⊤

namespace IsTransferMatrix

variable {Q : E → E → ℝ≥0∞} (hQ : IsTransferMatrix Q)
include hQ

lemma ne_top (x y : E) : Q x y ≠ ⊤ := by
  have := hQ.pow_ne_top 0 x y
  rwa [zero_add, Kernel.ofMatrix_pow_one_apply_singleton] at this

lemma pow_pos (n : ℕ) (x y : E) : 0 < (Kernel.ofMatrix Q ^ (n + 1)) x {y} := by
  induction n with
  | zero => rw [zero_add, Kernel.ofMatrix_pow_one_apply_singleton]; exact hQ.pos x y
  | succ n ih =>
    rw [Kernel.ofMatrix_pow_succ_apply_singleton]
    exact (ENNReal.mul_pos (hQ.pos x x).ne' ih.ne').trans_le (ENNReal.le_tsum x)

lemma pow_two_pos (x y : E) : 0 < (Kernel.ofMatrix Q ^ 2) x {y} := hQ.pow_pos 1 x y

lemma pow_two_ne_top (x y : E) : (Kernel.ofMatrix Q ^ 2) x {y} ≠ ⊤ := hQ.pow_ne_top 1 x y

end IsTransferMatrix

/-- On a finite state space every positive matrix with finite entries is a transfer matrix. -/
lemma isTransferMatrix_of_finite [Finite E] {Q : E → E → ℝ≥0∞} (hpos : ∀ x y, 0 < Q x y)
    (htop : ∀ x y, Q x y ≠ ⊤) : IsTransferMatrix Q where
  pos := hpos
  pow_ne_top n x y := by
    have := Kernel.isFiniteKernel_ofMatrix Q htop
    have := Kernel.isFiniteKernel_pow (Kernel.ofMatrix Q) (n + 1)
    exact measure_ne_top _ _

/-! ## Products of transfer weights along an interval -/

section PathProd

variable (Q : E → E → ℝ≥0∞)

/-- The weight `∏_{j = a}^{b-1} Q(σ_j, σ_{j+1})` of the bonds inside `[a, b]`. -/
def pathProd (a b : ℤ) (σ : ℤ → E) : ℝ≥0∞ := ∏ j ∈ Finset.Ico a b, Q (σ j) (σ (j + 1))

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
@[simp] lemma pathProd_self (a : ℤ) (σ : ℤ → E) : pathProd Q a a σ = 1 := by
  simp [pathProd]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_split {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (σ : ℤ → E) :
    pathProd Q a c σ = pathProd Q a b σ * pathProd Q b c σ := by
  rw [pathProd, ← Finset.Ico_union_Ico_eq_Ico hab hbc,
    Finset.prod_union (Finset.Ico_disjoint_Ico_consecutive a b c)]
  rfl

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_succ (a : ℤ) (σ : ℤ → E) : pathProd Q a (a + 1) σ = Q (σ a) (σ (a + 1)) := by
  rw [pathProd, show Finset.Ico a (a + 1) = {a} by ext k; simp; omega, Finset.prod_singleton]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_pred (a : ℤ) (σ : ℤ → E) : pathProd Q (a - 1) a σ = Q (σ (a - 1)) (σ a) := by
  have := pathProd_succ Q (a - 1) σ
  rwa [sub_add_cancel] at this

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_succ_top {a b : ℤ} (h : a ≤ b) (σ : ℤ → E) :
    pathProd Q a (b + 1) σ = pathProd Q a b σ * Q (σ b) (σ (b + 1)) := by
  rw [pathProd_split Q h (by omega), pathProd_succ]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_pred_bot {a b : ℤ} (h : a ≤ b) (σ : ℤ → E) :
    pathProd Q (a - 1) b σ = Q (σ (a - 1)) (σ a) * pathProd Q a b σ := by
  rw [pathProd_split Q (show a - 1 ≤ a by omega) h, pathProd_pred]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_congr {a b : ℤ} {σ τ : ℤ → E} (h : ∀ k ∈ Finset.Icc a b, σ k = τ k) :
    pathProd Q a b σ = pathProd Q a b τ := by
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_Ico] at hj
  rw [h j (Finset.mem_Icc.2 (by omega)), h (j + 1) (Finset.mem_Icc.2 (by omega))]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_update_of_notMem {a b i : ℤ} (hi : i ∉ Finset.Icc a b) (σ : ℤ → E) (y : E) :
    pathProd Q a b (Function.update σ i y) = pathProd Q a b σ :=
  pathProd_congr Q fun _ hk ↦ Function.update_of_ne (ne_of_mem_of_not_mem hk hi) _ _

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_pos (hQ : ∀ x y, 0 < Q x y) (a b : ℤ) (σ : ℤ → E) : 0 < pathProd Q a b σ :=
  pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ ↦ (hQ _ _).ne')

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_ne_top (hQ : ∀ x y, Q x y ≠ ⊤) (a b : ℤ) (σ : ℤ → E) :
    pathProd Q a b σ ≠ ⊤ :=
  (ENNReal.prod_lt_top fun _ _ ↦ (hQ _ _).lt_top).ne

lemma measurable_pathProd (a b : ℤ) : Measurable (pathProd Q a b) :=
  Finset.measurable_prod _ fun j _ ↦ measurable_bond Q j

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- The weight of an interval volume is the weight of the bonds from `a - 1` to `b + 1`. -/
lemma transferWeight_Icc {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) :
    transferWeight Q (Finset.Icc a b) σ = pathProd Q (a - 1) (b + 1) σ := by
  rw [transferWeight, bondsOf_Icc hab]
  rfl

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma transferWeight_singleton (i : ℤ) (σ : ℤ → E) :
    transferWeight Q {i} σ = Q (σ (i - 1)) (σ i) * Q (σ i) (σ (i + 1)) := by
  rw [← Finset.Icc_self, transferWeight_Icc Q le_rfl, pathProd_pred_bot Q (by omega),
    pathProd_succ]

/-! ### The partition function of an interval: Georgii (11.2) -/

/-- The engine of Georgii (11.2): integrating the bond weights inside `[a - 1, a + n]` times a
function of the right endpoint against `λ_{[a, a+n]}(·|ω)` for counting measure produces the
corresponding power of `Q` from the left boundary spin `ω_{a-1}`. -/
lemma lintegral_lambdaCount_Icc_pathProd_mul_pow (a : ℤ) (n m : ℕ) (c : E) (ω : ℤ → E) :
    ∫⁻ ζ, pathProd Q (a - 1) (a + n) ζ * (Kernel.ofMatrix Q ^ (m + 1)) (ζ (a + n)) {c}
        ∂(λ₀ (Finset.Icc a (a + n)) ω)
      = (Kernel.ofMatrix Q ^ (n + m + 2)) (ω (a - 1)) {c} := by
  induction n generalizing m with
  | zero =>
    have h0 : Finset.Icc a (a + ((0 : ℕ) : ℤ)) = {a} := by simp
    rw [show 0 + m + 2 = m + 1 + 1 by omega, h0, lintegral_lambdaCount_singleton a ω
      (F := fun ζ ↦ pathProd Q (a - 1) (a + ((0 : ℕ) : ℤ)) ζ
        * (Kernel.ofMatrix Q ^ (m + 1)) (ζ (a + ((0 : ℕ) : ℤ))) {c})
      ((measurable_pathProd Q _ _).mul
        (measurable_coord (fun x ↦ (Kernel.ofMatrix Q ^ (m + 1)) x {c}) _))]
    simp only [Nat.cast_zero, add_zero, pathProd_pred, Function.update_self,
      Function.update_of_ne (show a - 1 ≠ a by omega)]
    rw [← Kernel.ofMatrix_pow_succ_apply_singleton]
  | succ n ih =>
    have hins : Finset.Icc a (a + ((n + 1 : ℕ) : ℤ))
        = insert (a + n + 1) (Finset.Icc a (a + n)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    have hnot : a + n + 1 ∉ Finset.Icc a (a + n) := by simp
    rw [hins, lintegral_lambdaCount_insert hnot ω
      (F := fun ζ ↦ pathProd Q (a - 1) (a + ((n + 1 : ℕ) : ℤ)) ζ
        * (Kernel.ofMatrix Q ^ (m + 1)) (ζ (a + ((n + 1 : ℕ) : ℤ))) {c})
      ((measurable_pathProd Q _ _).mul
        (measurable_coord (fun x ↦ (Kernel.ofMatrix Q ^ (m + 1)) x {c}) _))]
    have hint : ∀ ζ : ℤ → E, ∑' y, pathProd Q (a - 1) (a + ((n + 1 : ℕ) : ℤ))
          (Function.update ζ (a + n + 1) y)
          * (Kernel.ofMatrix Q ^ (m + 1))
              (Function.update ζ (a + n + 1) y (a + ((n + 1 : ℕ) : ℤ))) {c}
        = pathProd Q (a - 1) (a + n) ζ
          * (Kernel.ofMatrix Q ^ (m + 1 + 1)) (ζ (a + n)) {c} := by
      intro ζ
      have hcast : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
      simp_rw [hcast, Function.update_self, pathProd_succ_top Q (show a - 1 ≤ a + n by omega),
        pathProd_update_of_notMem Q (show a + n + 1 ∉ Finset.Icc (a - 1) (a + n) by simp),
        Function.update_of_ne (show a + n ≠ a + n + 1 by omega), Function.update_self,
        Kernel.ofMatrix_pow_succ_apply_singleton Q (m + 1), mul_assoc, ENNReal.tsum_mul_left]
    simp_rw [hint]
    rw [ih (m + 1), show n + (m + 1) + 2 = n + 1 + m + 2 by omega]

/-- **Georgii (11.2), the partition function.** For counting measure and the interval
`Λ = [a, b]`, `Z_Λ(ω) = Q^{b-a+2}(ω_{a-1}, ω_{b+1})`. -/
lemma sigmaFiniteLambdaZ_transferWeight_Icc {a b : ℤ} (hab : a ≤ b) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
        (Finset.Icc a b) ω
      = (Kernel.ofMatrix Q ^ (b - a + 2).toNat) (ω (a - 1)) {ω (b + 1)} := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  rw [Specification.sigmaFiniteLambdaZ, lintegral_lambdaCount_congr _ _
    (measurable_transferWeight Q _) ((measurable_pathProd Q _ _).mul
      (measurable_coord (fun x ↦ (Kernel.ofMatrix Q ^ (0 + 1)) x {ω (a + n + 1)}) _))
    (G := fun ζ ↦ pathProd Q (a - 1) (a + n) ζ
      * (Kernel.ofMatrix Q ^ (0 + 1)) (ζ (a + n)) {ω (a + n + 1)}) fun ζ hζ ↦ ?_,
    lintegral_lambdaCount_Icc_pathProd_mul_pow, show (a + n - a + 2).toNat = n + 0 + 2 by omega]
  rw [transferWeight_Icc Q hab, pathProd_succ_top Q (by omega), zero_add,
    Kernel.ofMatrix_pow_one_apply_singleton, hζ (a + n + 1) (by simp)]

lemma sigmaFiniteLambdaZ_transferWeight_singleton (i : ℤ) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q) {i} ω
      = (Kernel.ofMatrix Q ^ 2) (ω (i - 1)) {ω (i + 1)} := by
  rw [← Finset.Icc_self, sigmaFiniteLambdaZ_transferWeight_Icc Q le_rfl]
  simp

end PathProd

/-! ## Admissibility of the transfer weights for counting measure -/

section Admissible

variable {ρ : Finset ℤ → (ℤ → E) → ℝ≥0∞}

/-- **Monotonicity of admissibility for counting measure.** Restricting the sum defining `Z_Δ` to
the configurations agreeing with `ω` on `Δ \ Λ` gives `Z_Λ(ω) ρ_Δ(ω) ≤ Z_Δ(ω) ρ_Λ(ω)`. -/
lemma sigmaFiniteLambdaZ_count_mul_le_of_subset (hρ : Specification.IsPremodifier ρ)
    {Λ Δ : Finset ℤ} (hΛΔ : Λ ⊆ Δ) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count ρ Λ ω * ρ Δ ω
      ≤ Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count ρ Δ ω * ρ Λ ω := by
  classical
  let ext : (Λ → E) → (Δ → E) := fun x k ↦ if h : (k : ℤ) ∈ Λ then x ⟨k, h⟩ else ω k
  have hjuxt : ∀ x : Λ → E, juxt (Δ : Set ℤ) ω (ext x) = juxt (Λ : Set ℤ) ω x := by
    intro x
    funext i
    by_cases hiΛ : i ∈ Λ
    · rw [juxt_apply_of_mem (Finset.mem_coe.2 (hΛΔ hiΛ)), juxt_apply_of_mem (Finset.mem_coe.2 hiΛ)]
      exact dite_eq_left hiΛ
    · rw [juxt_apply_of_not_mem (show i ∉ (Λ : Set ℤ) by simpa using hiΛ)]
      by_cases hiΔ : i ∈ Δ
      · rw [juxt_apply_of_mem (Finset.mem_coe.2 hiΔ)]
        exact dite_eq_right hiΛ
      · rw [juxt_apply_of_not_mem (show i ∉ (Δ : Set ℤ) by simpa using hiΔ)]
  have hinj : Function.Injective ext := by
    intro x x' h
    funext k
    have := congrFun h ⟨k, hΛΔ k.2⟩
    simpa [ext, k.2] using this
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ,
    lintegral_lambdaCount Λ ω (hρ.measurable Λ), lintegral_lambdaCount Δ ω (hρ.measurable Δ),
    ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right]
  calc ∑' x : Λ → E, ρ Λ (juxt (Λ : Set ℤ) ω x) * ρ Δ ω
      = ∑' x : Λ → E, ρ Δ (juxt (Δ : Set ℤ) ω (ext x)) * ρ Λ ω := by
        refine tsum_congr fun x ↦ ?_
        rw [hjuxt, hρ.comm_of_subset hΛΔ (juxt_agree_on_compl Λ ω x)]
    _ ≤ ∑' y : Δ → E, ρ Δ (juxt (Δ : Set ℤ) ω y) * ρ Λ ω :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj _

lemma sigmaFiniteLambdaZ_count_ne_top_of_subset (hρ : Specification.IsPremodifier ρ)
    {Λ Δ : Finset ℤ} (hΛΔ : Λ ⊆ Δ) {ω : ℤ → E} (hΔ0 : ρ Δ ω ≠ 0) (hΛtop : ρ Λ ω ≠ ⊤)
    (hZ : Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count ρ Δ ω ≠ ⊤) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count ρ Λ ω ≠ ⊤ := by
  intro htop
  have h := sigmaFiniteLambdaZ_count_mul_le_of_subset hρ hΛΔ ω
  rw [htop, ENNReal.top_mul hΔ0] at h
  exact (ENNReal.mul_lt_top hZ.lt_top hΛtop.lt_top).ne_top (top_le_iff.1 h)

/-- **Georgii (11.1) ⇒ λ-admissibility.** A transfer matrix is admissible for counting measure:
every finite volume lies in an interval, and interval partition functions are entries of powers
of `Q`. -/
theorem IsTransferMatrix.isSigmaFiniteLambdaAdmissible {Q : E → E → ℝ≥0∞}
    (hQ : IsTransferMatrix Q) :
    Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) Measure.count
      (transferWeight Q) := by
  intro Λ ω
  refine ⟨sigmaFiniteLambdaZ_count_ne_zero (isPremodifier_transferWeight Q)
    (transferWeight_pos Q hQ.pos Λ ω).ne', ?_⟩
  refine sigmaFiniteLambdaZ_count_ne_top_of_subset (isPremodifier_transferWeight Q)
    (subset_Icc_boundOf Λ) (transferWeight_pos Q hQ.pos _ ω).ne'
    (transferWeight_ne_top Q hQ.ne_top Λ ω) ?_
  have hN := boundOf_nonneg Λ
  rw [sigmaFiniteLambdaZ_transferWeight_Icc Q (by omega)]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (boundOf Λ - -boundOf Λ + 2).toNat = m + 1 :=
    ⟨(boundOf Λ + boundOf Λ + 1).toNat, by omega⟩
  rw [hm]
  exact hQ.pow_ne_top m _ _

end Admissible

/-! ## Georgii's specification `γ^Q` -/

section TransferSpecification

variable [Nonempty E] (Q : E → E → ℝ≥0∞) (hQ : IsTransferMatrix Q)

/-- **Georgii's `γ^Q`, defined by (11.2)–(11.3).** The λ-specification, for counting measure on
the countable state space `E`, of the transfer weights `∏_{bonds meeting Λ} Q(σ_j, σ_{j+1})` of a
positive matrix `Q` with finite powers. -/
def transferSpecification : Specification ℤ E :=
  Specification.lambdaSpecification (S := ℤ) (E := E) Measure.count (transferWeight Q)
    (isPremodifier_transferWeight Q) hQ.isSigmaFiniteLambdaAdmissible

lemma transferSpecification_apply (Λ : Finset ℤ) (ω : ℤ → E) {A : Set (ℤ → E)}
    (hA : MeasurableSet A) :
    transferSpecification Q hQ Λ ω A
      = (Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
          Λ ω)⁻¹ * ∫⁻ ζ in A, transferWeight Q Λ ζ ∂(λ₀ Λ ω) := by
  rw [transferSpecification, Specification.lambdaSpecification_apply]
  exact Specification.withDensity_sigmaFinitePremodifierNorm_apply (S := ℤ) (E := E)
    Measure.count (isPremodifier_transferWeight Q) hA ω

/-- `γ^Q_Λ(σ_Λ = ω_Λ | ω) = ρ^Q_Λ(ω) / Z_Λ(ω)`: Georgii's `ρ_Λ(ω)` of §11.1. -/
lemma transferSpecification_apply_cyl (Λ : Finset ℤ) (ω : ℤ → E) :
    transferSpecification Q hQ Λ ω (cyl Λ ω)
      = transferWeight Q Λ ω / Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E)
          Measure.count (transferWeight Q) Λ ω := by
  rw [transferSpecification_apply Q hQ Λ ω (measurableSet_cyl Λ ω),
    setLIntegral_lambdaCount_cyl Λ ω (measurable_transferWeight Q Λ), ENNReal.div_eq_inv_mul]

/-- **Georgii (11.2).** For the interval `Λ = ]i, k[ = [a, b]` (`a = i + 1`, `b = k - 1`),
`γ^Q_Λ(σ_Λ = ω_Λ | ω) = ∏_{j=i+1}^{k} Q(ω_{j-1}, ω_j) / Q^{k-i}(ω_i, ω_k)`. -/
theorem transferSpecification_Icc_apply_intervalCylinder {a b : ℤ} (hab : a ≤ b) (ω : ℤ → E) :
    transferSpecification Q hQ (Finset.Icc a b) ω (intervalCylinder a b ω)
      = pathProd Q (a - 1) (b + 1) ω
          / (Kernel.ofMatrix Q ^ (b - a + 2).toNat) (ω (a - 1)) {ω (b + 1)} := by
  rw [intervalCylinder_eq_cyl a b ω,
    transferSpecification_apply_cyl, transferWeight_Icc Q hab,
    sigmaFiniteLambdaZ_transferWeight_Icc Q hab]

/-- The singleton kernel of `γ^Q`, Georgii (11.2) for `Λ = {i}` on an interval cylinder
containing `i` in its interior: `γ^Q_{i}(σ_{[a,b]} = σ | ω)` is
`Q(σ_{i-1}, σ_i) Q(σ_i, σ_{i+1}) / Q²(σ_{i-1}, σ_{i+1})` if `ω` agrees with `σ` on `[a, b] \ {i}`
and `0` otherwise. -/
theorem transferSpecification_singleton_apply_intervalCylinder {a b i : ℤ} (hai : a < i)
    (hib : i < b) (σ ω : ℤ → E) :
    transferSpecification Q hQ {i} ω (intervalCylinder a b σ)
      = (puncturedCylinder a b i σ).indicator
          (fun _ ↦ Q (σ (i - 1)) (σ i) * Q (σ i) (σ (i + 1))
            / (Kernel.ofMatrix Q ^ 2) (σ (i - 1)) {σ (i + 1)}) ω := by
  rw [transferSpecification_apply Q hQ {i} ω (measurableSet_intervalCylinder a b σ),
    ← lintegral_indicator (measurableSet_intervalCylinder a b σ),
    lintegral_lambdaCount_singleton i ω
      ((measurable_transferWeight Q {i}).indicator (measurableSet_intervalCylinder a b σ)),
    sigmaFiniteLambdaZ_transferWeight_singleton]
  have hi : i ∈ Finset.Icc a b := Finset.mem_Icc.2 ⟨hai.le, hib.le⟩
  have hi1 : i - 1 ∈ (Finset.Icc a b).erase i := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  have hi2 : i + 1 ∈ (Finset.Icc a b).erase i := by
    simp only [Finset.mem_erase, Finset.mem_Icc]; omega
  by_cases hω : ω ∈ puncturedCylinder a b i σ
  · rw [Set.indicator_of_mem hω, tsum_eq_single (σ i) fun y hy ↦ ?_]
    · have hmem : Function.update ω i (σ i) ∈ intervalCylinder a b σ := by
        intro k hk
        by_cases hki : k = i
        · subst hki; exact Function.update_self ..
        · rw [Function.update_of_ne hki]
          exact hω k (Finset.mem_erase.2 ⟨hki, hk⟩)
      rw [Set.indicator_of_mem hmem, transferWeight_singleton, Function.update_self,
        Function.update_of_ne (show i - 1 ≠ i by omega),
        Function.update_of_ne (show i + 1 ≠ i by omega), hω _ hi1, hω _ hi2,
        ENNReal.div_eq_inv_mul]
    · refine Set.indicator_of_notMem (fun h ↦ hy ?_) _
      have := h i hi
      rwa [Function.update_self] at this
  · rw [Set.indicator_of_notMem hω]
    have : ∀ y, (intervalCylinder a b σ).indicator (transferWeight Q {i})
        (Function.update ω i y) = 0 := fun y ↦
      Set.indicator_of_notMem (fun h ↦ hω fun k hk ↦ by
        have hki := (Finset.mem_erase.1 hk).1
        have := h k (Finset.mem_erase.1 hk).2
        rwa [Function.update_of_ne hki] at this) _
    simp [this]

end TransferSpecification

/-! ## Georgii (11.3): non-adjacent volumes factorise -/

section Factorisation

variable (Q : E → E → ℝ≥0∞)

/-- Integrating against `λ_{Λ₁ ∪ Λ₂}` for disjoint volumes: integrate over `Λ₂`, then over `Λ₁`
(counting measure; Georgii's Notation (1.26) `λ_{Λ₁} λ_{Λ₂} = λ_{Λ₁ ∪ Λ₂}`). -/
lemma lintegral_lambdaCount_union {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint Λ₁ Λ₂) (η : ℤ → E)
    {F : (ℤ → E) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ζ, F ζ ∂(λ₀ (Λ₁ ∪ Λ₂) η) = ∫⁻ ζ, ∫⁻ ξ, F ξ ∂(λ₀ Λ₂ ζ) ∂(λ₀ Λ₁ η) := by
  induction Λ₂ using Finset.induction_on generalizing F with
  | empty =>
    simp_rw [lintegral_lambdaCount_empty _ hF]
    rw [Finset.union_empty]
  | insert j Λ₂ hj ih =>
    rw [Finset.disjoint_insert_right] at h
    have hG : Measurable fun ζ : ℤ → E ↦ ∑' y, F (Function.update ζ j y) :=
      Measurable.tsum fun y ↦ hF.comp (measurable_update_left j y)
    rw [Finset.union_insert, lintegral_lambdaCount_insert (by simp [h.1, hj]) η hF, ih h.2 hG]
    exact lintegral_congr fun ζ ↦ (lintegral_lambdaCount_insert hj ζ hF).symm

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma bondsOf_union (Λ₁ Λ₂ : Finset ℤ) : bondsOf (Λ₁ ∪ Λ₂) = bondsOf Λ₁ ∪ bondsOf Λ₂ := by
  ext j
  simp only [mem_bondsOf, Finset.mem_union]
  tauto

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma subset_bondsOf (Λ : Finset ℤ) : Λ ⊆ bondsOf Λ := fun _ hj ↦ mem_bondsOf.2 (Or.inl hj)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- Volumes with disjoint bonds are disjoint and non-adjacent. -/
lemma disjoint_of_disjoint_bondsOf {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) :
    Disjoint Λ₁ Λ₂ :=
  Finset.disjoint_of_subset_left (subset_bondsOf Λ₁)
    (Finset.disjoint_of_subset_right (subset_bondsOf Λ₂) h)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- For non-adjacent volumes, the weight of `Λ₁` does not depend on the spins in `Λ₂`. -/
lemma transferWeight_congr_of_disjoint_bondsOf {Λ₁ Λ₂ : Finset ℤ}
    (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) {ζ η : ℤ → E} (hζη : ∀ k ∉ Λ₂, ζ k = η k) :
    transferWeight Q Λ₁ ζ = transferWeight Q Λ₁ η := by
  refine transferWeight_congr Q fun j hj ↦ ⟨hζη j fun hj' ↦ ?_, hζη (j + 1) fun hj' ↦ ?_⟩
  · exact Finset.disjoint_left.1 h hj (mem_bondsOf.2 (Or.inl hj'))
  · exact Finset.disjoint_left.1 h hj (mem_bondsOf.2 (Or.inr hj'))

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma transferWeight_union {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂))
    (σ : ℤ → E) : transferWeight Q (Λ₁ ∪ Λ₂) σ = transferWeight Q Λ₁ σ * transferWeight Q Λ₂ σ := by
  rw [transferWeight, bondsOf_union, Finset.prod_union h]
  rfl

/-- The partition function of `Λ₂` depends only on the spins outside a non-adjacent volume. -/
lemma sigmaFiniteLambdaZ_transferWeight_congr {Λ₁ Λ₂ : Finset ℤ}
    (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) {ζ ω : ℤ → E} (hζω : ∀ k ∉ Λ₁, ζ k = ω k) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q) Λ₂ ζ
      = Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
          Λ₂ ω := by
  rw [Specification.sigmaFiniteLambdaZ, Specification.sigmaFiniteLambdaZ,
    lintegral_lambdaCount _ _ (measurable_transferWeight Q _),
    lintegral_lambdaCount _ _ (measurable_transferWeight Q _)]
  refine tsum_congr fun x ↦ transferWeight_congr_of_disjoint_bondsOf Q h.symm fun k hk ↦ ?_
  by_cases hk2 : k ∈ Λ₂
  · rw [juxt_apply_of_mem (Finset.mem_coe.2 hk2), juxt_apply_of_mem (Finset.mem_coe.2 hk2)]
  · rw [juxt_apply_of_not_mem (show k ∉ (Λ₂ : Set ℤ) by simpa using hk2),
      juxt_apply_of_not_mem (show k ∉ (Λ₂ : Set ℤ) by simpa using hk2), hζω k hk]

/-- **Georgii (11.3), partition functions.** `Z_{Λ₁ ∪ Λ₂} = Z_{Λ₁} Z_{Λ₂}` for non-adjacent
volumes. -/
lemma sigmaFiniteLambdaZ_transferWeight_union {Λ₁ Λ₂ : Finset ℤ}
    (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) (ω : ℤ → E) :
    Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
        (Λ₁ ∪ Λ₂) ω
      = Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q) Λ₁ ω
        * Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E) Measure.count (transferWeight Q)
            Λ₂ ω := by
  have hinner : ∀ ζ : ℤ → E, (∀ k ∉ Λ₁, ζ k = ω k) →
      ∫⁻ ξ, transferWeight Q (Λ₁ ∪ Λ₂) ξ ∂(λ₀ Λ₂ ζ)
        = transferWeight Q Λ₁ ζ * Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E)
            Measure.count (transferWeight Q) Λ₂ ω := by
    intro ζ hζ
    rw [lintegral_lambdaCount_congr Λ₂ ζ (measurable_transferWeight Q _)
      (measurable_const.mul (measurable_transferWeight Q Λ₂))
      (G := fun ξ ↦ transferWeight Q Λ₁ ζ * transferWeight Q Λ₂ ξ) fun ξ hξ ↦ by
        rw [transferWeight_union Q h, transferWeight_congr_of_disjoint_bondsOf Q h hξ],
      lintegral_const_mul _ (measurable_transferWeight Q Λ₂), ← Specification.sigmaFiniteLambdaZ,
      sigmaFiniteLambdaZ_transferWeight_congr Q h hζ]
  rw [Specification.sigmaFiniteLambdaZ,
    lintegral_lambdaCount_union (disjoint_of_disjoint_bondsOf h) ω (measurable_transferWeight Q _),
    lintegral_lambdaCount_congr Λ₁ ω
      ((measurable_transferWeight Q _).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)
      ((measurable_transferWeight Q Λ₁).mul measurable_const)
      (G := fun ζ ↦ transferWeight Q Λ₁ ζ * Specification.sigmaFiniteLambdaZ (S := ℤ) (E := E)
        Measure.count (transferWeight Q) Λ₂ ω) hinner,
    lintegral_mul_const _ (measurable_transferWeight Q Λ₁)]
  rfl

/-- **Georgii (11.3).** For disjoint non-adjacent volumes `Λ₁`, `Λ₂` (no bond meets both),
`γ^Q_{Λ₁ ∪ Λ₂}(σ_{Λ₁ ∪ Λ₂} = ω | ω) = γ^Q_{Λ₁}(σ_{Λ₁} = ω | ω) γ^Q_{Λ₂}(σ_{Λ₂} = ω | ω)`; the
product over `N` pairwise non-adjacent intervals follows by induction. -/
theorem transferSpecification_apply_cyl_union [Nonempty E] (hQ : IsTransferMatrix Q)
    {Λ₁ Λ₂ : Finset ℤ} (h : Disjoint (bondsOf Λ₁) (bondsOf Λ₂)) (ω : ℤ → E) :
    transferSpecification Q hQ (Λ₁ ∪ Λ₂) ω (cyl (Λ₁ ∪ Λ₂) ω)
      = transferSpecification Q hQ Λ₁ ω (cyl Λ₁ ω)
        * transferSpecification Q hQ Λ₂ ω (cyl Λ₂ ω) := by
  rw [transferSpecification_apply_cyl, transferSpecification_apply_cyl,
    transferSpecification_apply_cyl, transferWeight_union Q h,
    sigmaFiniteLambdaZ_transferWeight_union Q h, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (hQ.isSigmaFiniteLambdaAdmissible Λ₁ ω).1)
      (Or.inl (hQ.isSigmaFiniteLambdaAdmissible Λ₁ ω).2)]
  ring

end Factorisation

/-! ## Georgii Remark (11.4): equivalent transfer matrices -/

section Equivalence

variable [Nonempty E] {P Q : E → E → ℝ≥0∞}

/-- The singleton kernel of `γ^Q` is the density change of the counting reference kernel by the
determining function `Q(σ_{i-1}, σ_i) Q(σ_i, σ_{i+1}) / Q²(σ_{i-1}, σ_{i+1})` of (11.2). -/
lemma transferSpecification_singleton_eq (hQ : IsTransferMatrix Q) (i : ℤ) (ω : ℤ → E) :
    transferSpecification Q hQ {i} ω = (λ₀ {i} ω).withDensity fun ζ ↦
      Q (ζ (i - 1)) (ζ i) * Q (ζ i) (ζ (i + 1))
        / (Kernel.ofMatrix Q ^ 2) (ζ (i - 1)) {ζ (i + 1)} := by
  rw [transferSpecification, Specification.lambdaSpecification_apply]
  congr 1
  funext ζ
  rw [Specification.sigmaFinitePremodifierNorm, transferWeight_singleton,
    sigmaFiniteLambdaZ_transferWeight_singleton]

omit [Nonempty E] in
lemma measurable_detFun (Q : E → E → ℝ≥0∞) (i : ℤ) :
    Measurable fun ζ : ℤ → E ↦ Q (ζ (i - 1)) (ζ i) * Q (ζ i) (ζ (i + 1))
      / (Kernel.ofMatrix Q ^ 2) (ζ (i - 1)) {ζ (i + 1)} :=
  ((measurable_pair Q _ _).mul (measurable_pair Q _ _)).div
    (measurable_pair (fun x z ↦ (Kernel.ofMatrix Q ^ 2) x {z}) _ _)

omit [Nonempty E] in
/-- Two density changes of the singleton reference kernel `λ_{i}(·|ω)` agree iff their densities
agree on the configurations differing from `ω` at most at `i`. -/
lemma withDensity_lambdaCount_singleton_congr (i : ℤ) (ω : ℤ → E) {f g : (ℤ → E) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ y, f (Function.update ω i y) = g (Function.update ω i y)) :
    (λ₀ {i} ω).withDensity f = (λ₀ {i} ω).withDensity g := by
  ext A hA
  rw [withDensity_apply _ hA, withDensity_apply _ hA, ← lintegral_indicator hA,
    ← lintegral_indicator hA, lintegral_lambdaCount_singleton i ω (hf.indicator hA),
    lintegral_lambdaCount_singleton i ω (hg.indicator hA)]
  exact tsum_congr fun y ↦ by by_cases hy : Function.update ω i y ∈ A <;> simp [hy, h y]

omit [Nonempty E] in
/-- (11.5) implies equality of the determining functions `P(x,y)P(y,z)/P²(x,z)`. -/
lemma det_eq_of_rel {q : ℝ≥0∞}
    {r : E → ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hr0 : ∀ x, r x ≠ 0) (hrt : ∀ x, r x ≠ ⊤)
    (hPQ : ∀ x y, P x y = Q x y * r y / (q * r x)) (x y z : E) :
    P x y * P y z / (Kernel.ofMatrix P ^ 2) x {z}
      = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z} := by
  set c : ℝ≥0∞ := r z * q⁻¹ * q⁻¹ * (r x)⁻¹ with hc
  have hc0 : c ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hr0 z) (ENNReal.inv_ne_zero.2 hqt))
      (ENNReal.inv_ne_zero.2 hqt)) (ENNReal.inv_ne_zero.2 (hrt x))
  have hct : c ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hrt z) (ENNReal.inv_ne_top.2 hq0))
      (ENNReal.inv_ne_top.2 hq0)) (ENNReal.inv_ne_top.2 (hr0 x))
  have key : ∀ y, P x y * P y z = Q x y * Q y z * c := fun y ↦ by
    rw [hPQ x y, hPQ y z, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hq0) (Or.inl hqt),
      ENNReal.mul_inv (Or.inl hq0) (Or.inl hqt)]
    calc Q x y * r y * (q⁻¹ * (r x)⁻¹) * (Q y z * r z * (q⁻¹ * (r y)⁻¹))
        = Q x y * Q y z * c * (r y * (r y)⁻¹) := by rw [hc]; ring
      _ = Q x y * Q y z * c := by rw [ENNReal.mul_inv_cancel (hr0 y) (hrt y), mul_one]
  rw [key, Kernel.ofMatrix_pow_two_apply_singleton, Kernel.ofMatrix_pow_two_apply_singleton]
  simp_rw [key]
  rw [ENNReal.tsum_mul_right, ENNReal.mul_div_mul_right _ _ hc0 hct]

/-- **Georgii Remark (11.4), "if".** Matrices related by (11.5) define the same specification. -/
theorem transferSpecification_eq_of_rel (hP : IsTransferMatrix P) (hQ : IsTransferMatrix Q)
    {q : ℝ≥0∞} {r : E → ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ ⊤) (hr0 : ∀ x, r x ≠ 0)
    (hrt : ∀ x, r x ≠ ⊤) (hPQ : ∀ x y, P x y = Q x y * r y / (q * r x)) :
    transferSpecification P hP = transferSpecification Q hQ := by
  refine Specification.eq_lambdaSpecification_of_forall_singleton_eq (S := ℤ) (E := E)
    Measure.count (isPremodifier_transferWeight Q)
    (fun Λ ω ↦ (transferWeight_pos Q hQ.pos Λ ω).ne')
    (fun Λ ω ↦ transferWeight_ne_top Q hQ.ne_top Λ ω) hQ.isSigmaFiniteLambdaAdmissible fun i ↦ ?_
  refine Kernel.ext fun ω ↦ ?_
  change transferSpecification P hP {i} ω = transferSpecification Q hQ {i} ω
  rw [transferSpecification_singleton_eq hP, transferSpecification_singleton_eq hQ]
  refine withDensity_lambdaCount_singleton_congr i ω (measurable_detFun P i)
    (measurable_detFun Q i) fun y ↦ ?_
  simp only [Function.update_self, Function.update_of_ne (show i - 1 ≠ i by omega),
    Function.update_of_ne (show i + 1 ≠ i by omega)]
  exact det_eq_of_rel hq0 hqt hr0 hrt hPQ _ _ _

/-- The configuration `x` at `i - 1`, `y` at `i`, `z` elsewhere. -/
def tripleConfig (i : ℤ) (x y z : E) : ℤ → E := fun k ↦
  if k = i - 1 then x else if k = i then y else z

/-- The determining function `Q(x,y)Q(y,z)/Q²(x,z)` of `γ^Q` is read off the singleton kernels
(Georgii (11.2) for `Λ = {i}`). -/
lemma transferSpecification_tripleConfig (hQ : IsTransferMatrix Q) (i : ℤ) (x y z : E) :
    transferSpecification Q hQ {i} (tripleConfig i x y z)
        (intervalCylinder (i - 1) (i + 1) (tripleConfig i x y z))
      = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z} := by
  rw [transferSpecification_singleton_apply_intervalCylinder Q hQ (show i - 1 < i by omega)
    (show i < i + 1 by omega), Set.indicator_of_mem (show tripleConfig i x y z ∈
      puncturedCylinder (i - 1) (i + 1) i (tripleConfig i x y z) from fun _ _ ↦ rfl)]
  simp [tripleConfig, show i ≠ i - 1 by omega, show i + 1 ≠ i - 1 by omega,
    show i + 1 ≠ i by omega]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] [Nonempty E] in
/-- The algebra of Georgii's proof of (11.4): equal determining functions give (11.5) with
`q = Q(a,a)/P(a,a)` and `r(x) = Q²(x,a)/P²(x,a)`. -/
lemma rel_of_det_eq {P Q P₂ Q₂ : E → E → ℝ≥0∞} (hP0 : ∀ x y, P x y ≠ 0) (hPt : ∀ x y, P x y ≠ ⊤)
    (hP₂0 : ∀ x y, P₂ x y ≠ 0) (hP₂t : ∀ x y, P₂ x y ≠ ⊤) (hQ0 : ∀ x y, Q x y ≠ 0)
    (hQt : ∀ x y, Q x y ≠ ⊤) (hQ₂0 : ∀ x y, Q₂ x y ≠ 0) (hQ₂t : ∀ x y, Q₂ x y ≠ ⊤)
    (hid : ∀ x y z, P x y * P y z / P₂ x z = Q x y * Q y z / Q₂ x z) (a x y : E) :
    P x y = Q x y * (Q₂ y a / P₂ y a) / (Q a a / P a a * (Q₂ x a / P₂ x a)) := by
  have E2 : Q₂ x a * (P x y * P y a) = P₂ x a * (Q x y * Q y a) :=
    (ENNReal.div_eq_div_iff (hQ₂0 x a) (hQ₂t x a) (hP₂0 x a) (hP₂t x a)).1 (hid x y a)
  have E1 : Q₂ y a * (P y a * P a a) = P₂ y a * (Q y a * Q a a) :=
    (ENNReal.div_eq_div_iff (hQ₂0 y a) (hQ₂t y a) (hP₂0 y a) (hP₂t y a)).1 (hid y a a)
  have hd0 : Q a a / P a a * (Q₂ x a / P₂ x a) ≠ 0 :=
    mul_ne_zero (ENNReal.div_ne_zero.2 ⟨hQ0 a a, hPt a a⟩)
      (ENNReal.div_ne_zero.2 ⟨hQ₂0 x a, hP₂t x a⟩)
  have hdt : Q a a / P a a * (Q₂ x a / P₂ x a) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top (hQt a a) (hP0 a a))
      (ENNReal.div_ne_top (hQ₂t x a) (hP₂0 x a))
  rw [ENNReal.eq_div_iff hd0 hdt]
  set D : ℝ≥0∞ := P a a * P₂ x a * P₂ y a * P y a with hD
  have hD0 : D ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hP0 a a) (hP₂0 x a)) (hP₂0 y a)) (hP0 y a)
  have hDt : D ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hPt a a) (hP₂t x a)) (hP₂t y a))
      (hPt y a)
  refine (ENNReal.mul_right_inj hD0 hDt).1 ?_
  calc D * (Q a a / P a a * (Q₂ x a / P₂ x a) * P x y)
      = (P a a * (Q a a / P a a)) * (P₂ x a * (Q₂ x a / P₂ x a)) * P₂ y a * P y a * P x y := by
        rw [hD]; ring
    _ = Q a a * Q₂ x a * P₂ y a * P y a * P x y := by
        rw [ENNReal.mul_div_cancel (hP0 a a) (hPt a a),
          ENNReal.mul_div_cancel (hP₂0 x a) (hP₂t x a)]
    _ = Q a a * P₂ y a * (Q₂ x a * (P x y * P y a)) := by ring
    _ = Q a a * P₂ y a * (P₂ x a * (Q x y * Q y a)) := by rw [E2]
    _ = P₂ x a * Q x y * (P₂ y a * (Q y a * Q a a)) := by ring
    _ = P₂ x a * Q x y * (Q₂ y a * (P y a * P a a)) := by rw [E1]
    _ = P a a * P₂ x a * P y a * Q x y * (P₂ y a * (Q₂ y a / P₂ y a)) := by
        rw [ENNReal.mul_div_cancel (hP₂0 y a) (hP₂t y a)]; ring
    _ = D * (Q x y * (Q₂ y a / P₂ y a)) := by rw [hD]; ring

/-- **Georgii Remark (11.4), "only if".** Matrices defining the same specification are related by
(11.5). -/
theorem exists_rel_of_transferSpecification_eq (hP : IsTransferMatrix P) (hQ : IsTransferMatrix Q)
    (h : transferSpecification P hP = transferSpecification Q hQ) :
    ∃ (q : ℝ≥0∞) (r : E → ℝ≥0∞), q ≠ 0 ∧ q ≠ ⊤ ∧ (∀ x, r x ≠ 0) ∧ (∀ x, r x ≠ ⊤) ∧
      ∀ x y, P x y = Q x y * r y / (q * r x) := by
  have hid : ∀ x y z, P x y * P y z / (Kernel.ofMatrix P ^ 2) x {z}
      = Q x y * Q y z / (Kernel.ofMatrix Q ^ 2) x {z} := fun x y z ↦ by
    rw [← transferSpecification_tripleConfig hP 0 x y z,
      ← transferSpecification_tripleConfig hQ 0 x y z, h]
  obtain ⟨a⟩ := ‹Nonempty E›
  refine ⟨Q a a / P a a, fun x ↦ (Kernel.ofMatrix Q ^ 2) x {a} / (Kernel.ofMatrix P ^ 2) x {a},
    ENNReal.div_ne_zero.2 ⟨(hQ.pos a a).ne', hP.ne_top a a⟩,
    ENNReal.div_ne_top (hQ.ne_top a a) (hP.pos a a).ne',
    fun x ↦ ENNReal.div_ne_zero.2 ⟨(hQ.pow_two_pos x a).ne', hP.pow_two_ne_top x a⟩,
    fun x ↦ ENNReal.div_ne_top (hQ.pow_two_ne_top x a) (hP.pow_two_pos x a).ne', fun x y ↦ ?_⟩
  exact rel_of_det_eq (fun x y ↦ (hP.pos x y).ne') hP.ne_top (fun x y ↦ (hP.pow_two_pos x y).ne')
    hP.pow_two_ne_top (fun x y ↦ (hQ.pos x y).ne') hQ.ne_top (fun x y ↦ (hQ.pow_two_pos x y).ne')
    hQ.pow_two_ne_top hid a x y

/-- **Georgii Remark (11.4).** Two positive matrices with finite powers define the same
specification, `γ^P = γ^Q`, iff `P(x,y) = Q(x,y) r(y) / (q r(x))` for a constant `q > 0` and a
positive finite function `r` (Georgii (11.5)). -/
theorem transferSpecification_eq_iff (hP : IsTransferMatrix P) (hQ : IsTransferMatrix Q) :
    transferSpecification P hP = transferSpecification Q hQ ↔
      ∃ (q : ℝ≥0∞) (r : E → ℝ≥0∞), q ≠ 0 ∧ q ≠ ⊤ ∧ (∀ x, r x ≠ 0) ∧ (∀ x, r x ≠ ⊤) ∧
        ∀ x y, P x y = Q x y * r y / (q * r x) :=
  ⟨exists_rel_of_transferSpecification_eq hP hQ, fun ⟨_, _, hq0, hqt, hr0, hrt, hPQ⟩ ↦
    transferSpecification_eq_of_rel hP hQ hq0 hqt hr0 hrt hPQ⟩

end Equivalence

/-! ## Boundary laws: Georgii Definition (11.8) -/

/-- **Georgii Definition (11.8).** A boundary law for `Q` is a family of positive finite row
vectors `ℓ_i` and column vectors `r_i` with `ℓ_i Q = ℓ_{i+1}`, `Q r_i = r_{i-1}` and
`ℓ_i r_i = 1`. Row vectors are the measures `ℓ_i · count` acting on the kernel `ofMatrix Q` by
`Measure.bind`; column vectors are integrated against it. -/
structure IsBoundaryLaw (Q : E → E → ℝ≥0∞) (ℓ r : ℤ → E → ℝ≥0∞) : Prop where
  left_pos : ∀ i x, 0 < ℓ i x
  left_ne_top : ∀ i x, ℓ i x ≠ ⊤
  right_pos : ∀ i x, 0 < r i x
  right_ne_top : ∀ i x, r i x ≠ ⊤
  /-- `ℓ_i Q = ℓ_{i+1}`. -/
  bind_left : ∀ i, (Measure.count.withDensity (ℓ i)).bind (Kernel.ofMatrix Q)
    = Measure.count.withDensity (ℓ (i + 1))
  /-- `Q r_i = r_{i-1}`. -/
  lintegral_right : ∀ i x, ∫⁻ y, r i y ∂(Kernel.ofMatrix Q x) = r (i - 1) x
  /-- `ℓ_i r_i = 1`. -/
  lintegral_left_right : ∀ i, ∫⁻ x, r i x ∂(Measure.count.withDensity (ℓ i)) = 1

namespace IsBoundaryLaw

variable {Q : E → E → ℝ≥0∞} {ℓ r : ℤ → E → ℝ≥0∞}

/-- Georgii (11.8) in coordinates. -/
lemma of_tsum (left_pos : ∀ i x, 0 < ℓ i x) (left_ne_top : ∀ i x, ℓ i x ≠ ⊤)
    (right_pos : ∀ i x, 0 < r i x) (right_ne_top : ∀ i x, r i x ≠ ⊤)
    (hℓ : ∀ i y, ∑' x, ℓ i x * Q x y = ℓ (i + 1) y)
    (hr : ∀ i x, ∑' y, Q x y * r i y = r (i - 1) x)
    (hℓr : ∀ i, ∑' x, ℓ i x * r i x = 1) : IsBoundaryLaw Q ℓ r where
  left_pos := left_pos
  left_ne_top := left_ne_top
  right_pos := right_pos
  right_ne_top := right_ne_top
  bind_left i := by
    rw [Kernel.count_withDensity_bind_ofMatrix]
    exact congrArg _ (funext (hℓ i))
  lintegral_right i x := by rw [Kernel.lintegral_ofMatrix, hr]
  lintegral_left_right i := by rw [Measure.lintegral_count_withDensity, hℓr]

variable (h : IsBoundaryLaw Q ℓ r)
include h

/-- `ℓ_i Q = ℓ_{i+1}` in coordinates. -/
lemma tsum_left_mul (i : ℤ) (y : E) : ∑' x, ℓ i x * Q x y = ℓ (i + 1) y := by
  have := congrArg (fun μ : Measure E ↦ μ {y}) (h.bind_left i)
  simpa only [Kernel.bind_ofMatrix_apply_singleton, Measure.count_withDensity_apply_singleton]
    using this

lemma tsum_left_mul_pred (i : ℤ) (y : E) : ∑' x, ℓ (i - 1) x * Q x y = ℓ i y := by
  rw [h.tsum_left_mul, sub_add_cancel]

/-- `Q r_i = r_{i-1}` in coordinates. -/
lemma tsum_mul_right (i : ℤ) (x : E) : ∑' y, Q x y * r i y = r (i - 1) x := by
  rw [← Kernel.lintegral_ofMatrix, h.lintegral_right]

lemma tsum_mul_right_succ (i : ℤ) (x : E) : ∑' y, Q x y * r (i + 1) y = r i x := by
  rw [h.tsum_mul_right, add_sub_cancel_right]

/-- `ℓ_i r_i = 1` in coordinates. -/
lemma tsum_left_mul_right (i : ℤ) : ∑' x, ℓ i x * r i x = 1 := by
  rw [← Measure.lintegral_count_withDensity, h.lintegral_left_right]

end IsBoundaryLaw

/-! ## The measure (11.10) of a boundary law -/

section BoundaryLawMeasure

variable (Q : E → E → ℝ≥0∞) (ℓ r : ℤ → E → ℝ≥0∞)

/-- The right-hand side of Georgii (11.10): the weight
`ℓ_a(σ_a) Q(σ_a, σ_{a+1}) ⋯ Q(σ_{b-1}, σ_b) r_b(σ_b)` of a configuration on `[a, b]`. -/
def boundaryLawWeight (a b : ℤ) (σ : ℤ → E) : ℝ≥0∞ :=
  ℓ a (σ a) * pathProd Q a b σ * r b (σ b)

lemma measurable_boundaryLawWeight (a b : ℤ) : Measurable (boundaryLawWeight Q ℓ r a b) :=
  ((measurable_coord (ℓ a) a).mul (measurable_pathProd Q a b)).mul (measurable_coord (r b) b)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundaryLawWeight_congr {a b : ℤ} {σ τ : ℤ → E} (h : ∀ k ∈ Finset.Icc a b, σ k = τ k)
    (hab : a ≤ b) : boundaryLawWeight Q ℓ r a b σ = boundaryLawWeight Q ℓ r a b τ := by
  rw [boundaryLawWeight, boundaryLawWeight, pathProd_congr Q h,
    h a (Finset.mem_Icc.2 ⟨le_rfl, hab⟩), h b (Finset.mem_Icc.2 ⟨hab, le_rfl⟩)]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma boundOf_mono {Λ Δ : Finset ℤ} (h : Λ ⊆ Δ) : boundOf Λ ≤ boundOf Δ :=
  Nat.cast_le.2 (Finset.sup_mono h)

variable [Nonempty E]

/-- The measure `ρ λ_{[a,b]}(·|ω₀)` on `ℤ → E` with the density (11.10) on the interval `[a, b]`
with respect to counting measure, and the fixed configuration `baseConfig` outside. -/
def intervalLaw (a b : ℤ) : Measure (ℤ → E) :=
  (λ₀ (Finset.Icc a b) (baseConfig (E := E))).withDensity (boundaryLawWeight Q ℓ r a b)

/-- The finite-dimensional distributions of the boundary law: the marginal on `Λ` of the interval
law of any interval containing `Λ`. -/
def boundaryLawFDD (Λ : Finset ℤ) : Measure (Λ → E) :=
  (intervalLaw Q ℓ r (-boundOf Λ) (boundOf Λ)).map Λ.restrict

namespace IsBoundaryLaw

variable {Q ℓ r} (hbl : IsBoundaryLaw Q ℓ r)
include hbl

omit [Nonempty E] in
lemma tsum_boundaryLawWeight_update_succ {a b : ℤ} (hab : a ≤ b) (ζ : ℤ → E) :
    ∑' y, boundaryLawWeight Q ℓ r a (b + 1) (Function.update ζ (b + 1) y)
      = boundaryLawWeight Q ℓ r a b ζ := by
  simp_rw [boundaryLawWeight, pathProd_succ_top Q hab,
    pathProd_update_of_notMem Q (show b + 1 ∉ Finset.Icc a b by simp),
    Function.update_of_ne (show a ≠ b + 1 by omega),
    Function.update_of_ne (show b ≠ b + 1 by omega), Function.update_self]
  have : ∀ y, ℓ a (ζ a) * (pathProd Q a b ζ * Q (ζ b) y) * r (b + 1) y
      = ℓ a (ζ a) * pathProd Q a b ζ * (Q (ζ b) y * r (b + 1) y) := fun y ↦ by ring
  simp_rw [this, ENNReal.tsum_mul_left, hbl.tsum_mul_right_succ]

omit [Nonempty E] in
lemma tsum_boundaryLawWeight_update_pred {a b : ℤ} (hab : a ≤ b) (ζ : ℤ → E) :
    ∑' y, boundaryLawWeight Q ℓ r (a - 1) b (Function.update ζ (a - 1) y)
      = boundaryLawWeight Q ℓ r a b ζ := by
  simp_rw [boundaryLawWeight, pathProd_pred_bot Q hab,
    pathProd_update_of_notMem Q (show a - 1 ∉ Finset.Icc a b by simp),
    Function.update_of_ne (show a ≠ a - 1 by omega),
    Function.update_of_ne (show b ≠ a - 1 by omega), Function.update_self]
  have : ∀ y, ℓ (a - 1) y * (Q y (ζ a) * pathProd Q a b ζ) * r b (ζ b)
      = (ℓ (a - 1) y * Q y (ζ a)) * (pathProd Q a b ζ * r b (ζ b)) := fun y ↦ by ring
  simp_rw [this, ENNReal.tsum_mul_right, hbl.tsum_left_mul_pred, mul_assoc]

/-- Extending the interval to the right does not change the marginal on `[a, b]`
(`Q r_{b+1} = r_b`). -/
lemma intervalLaw_succ_map_restrict {a b : ℤ} (hab : a ≤ b) :
    (intervalLaw Q ℓ r a (b + 1)).map (Finset.Icc a b).restrict
      = (intervalLaw Q ℓ r a b).map (Finset.Icc a b).restrict := by
  have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [intervalLaw, intervalLaw, hins]
  exact map_restrict_withDensity_insert (by simp) _ (measurable_boundaryLawWeight Q ℓ r _ _)
    (hbl.tsum_boundaryLawWeight_update_succ hab)

/-- Extending the interval to the left does not change the marginal on `[a, b]`
(`ℓ_{a-1} Q = ℓ_a`). -/
lemma intervalLaw_pred_map_restrict {a b : ℤ} (hab : a ≤ b) :
    (intervalLaw Q ℓ r (a - 1) b).map (Finset.Icc a b).restrict
      = (intervalLaw Q ℓ r a b).map (Finset.Icc a b).restrict := by
  have hins : Finset.Icc (a - 1) b = insert (a - 1) (Finset.Icc a b) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [intervalLaw, intervalLaw, hins]
  exact map_restrict_withDensity_insert (by simp) _ (measurable_boundaryLawWeight Q ℓ r _ _)
    (hbl.tsum_boundaryLawWeight_update_pred hab)

lemma intervalLaw_add_map_restrict {a b : ℤ} (hab : a ≤ b) (k : ℕ) :
    (intervalLaw Q ℓ r a (b + k)).map (Finset.Icc a b).restrict
      = (intervalLaw Q ℓ r a b).map (Finset.Icc a b).restrict := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, show b + ((k + 1 : ℕ) : ℤ) = b + k + 1 by push_cast; ring]
    exact map_restrict_eq_of_subset
      (Finset.Icc_subset_Icc (a₁ := a) (b₁ := b) (a₂ := a) (b₂ := b + k) le_rfl (by omega))
      (hbl.intervalLaw_succ_map_restrict (a := a) (b := b + k) (by omega))

lemma intervalLaw_sub_map_restrict {a b : ℤ} (hab : a ≤ b) (k : ℕ) :
    (intervalLaw Q ℓ r (a - k) b).map (Finset.Icc a b).restrict
      = (intervalLaw Q ℓ r a b).map (Finset.Icc a b).restrict := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, show a - ((k + 1 : ℕ) : ℤ) = a - k - 1 by push_cast; ring]
    exact map_restrict_eq_of_subset
      (Finset.Icc_subset_Icc (a₁ := a) (b₁ := b) (a₂ := a - k) (b₂ := b) (by omega) le_rfl)
      (hbl.intervalLaw_pred_map_restrict (a := a - k) (b := b) (by omega))

/-- The marginal of `intervalLaw a' b'` on a volume `J ⊆ [a, b] ⊆ [a', b']` is that of
`intervalLaw a b`: the interval laws form a projective family. -/
lemma intervalLaw_map_restrict_eq {J : Finset ℤ} {a b a' b' : ℤ} (hJ : J ⊆ Finset.Icc a b)
    (ha : a' ≤ a) (hab : a ≤ b) (hb : b ≤ b') :
    (intervalLaw Q ℓ r a' b').map J.restrict = (intervalLaw Q ℓ r a b).map J.restrict := by
  refine map_restrict_eq_of_subset hJ ?_
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b' = b + k := ⟨(b' - b).toNat, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, a' = a - m := ⟨(a - a').toNat, by omega⟩
  calc (intervalLaw Q ℓ r (a - m) (b + k)).map (Finset.Icc a b).restrict
      = (intervalLaw Q ℓ r (a - m) b).map (Finset.Icc a b).restrict :=
        map_restrict_eq_of_subset
          (Finset.Icc_subset_Icc (a₁ := a) (b₁ := b) (a₂ := a - m) (b₂ := b) (by omega) le_rfl)
          (hbl.intervalLaw_add_map_restrict (a := a - m) (b := b) (by omega) k)
    _ = (intervalLaw Q ℓ r a b).map (Finset.Icc a b).restrict :=
        hbl.intervalLaw_sub_map_restrict hab m

lemma intervalLaw_univ {a b : ℤ} (hab : a ≤ b) : intervalLaw Q ℓ r a b Set.univ = 1 := by
  have h := congrArg (fun μ : Measure ((∅ : Finset ℤ) → E) ↦ μ Set.univ)
    (hbl.intervalLaw_map_restrict_eq (J := ∅) (a := a) (b := a) (by simp) le_rfl le_rfl hab)
  simp only [Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) _)
    MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, intervalLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Finset.Icc_self, lintegral_lambdaCount_singleton a _ (measurable_boundaryLawWeight Q ℓ r a a)]
  simp_rw [boundaryLawWeight, pathProd_self, mul_one, Function.update_self]
  exact hbl.tsum_left_mul_right a

lemma boundaryLawFDD_eq {Λ : Finset ℤ} {a b : ℤ} (hΛ : Λ ⊆ Finset.Icc a b) (hab : a ≤ b) :
    boundaryLawFDD Q ℓ r Λ = (intervalLaw Q ℓ r a b).map Λ.restrict := by
  have hN := boundOf_nonneg Λ
  rw [boundaryLawFDD, ← hbl.intervalLaw_map_restrict_eq (a' := min a (-boundOf Λ))
    (b' := max b (boundOf Λ)) (subset_Icc_boundOf Λ) (min_le_right _ _) (by omega)
    (le_max_right _ _),
    hbl.intervalLaw_map_restrict_eq hΛ (min_le_left _ _) hab (le_max_left _ _)]

lemma isProjectiveMeasureFamily_boundaryLawFDD :
    IsProjectiveMeasureFamily (α := fun _ : ℤ ↦ E) (boundaryLawFDD Q ℓ r) := by
  intro I J hJI
  have hN := boundOf_nonneg I
  have hJ : boundOf J ≤ boundOf I := boundOf_mono hJI
  rw [boundaryLawFDD, boundaryLawFDD,
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℤ ↦ E) hJI)
      (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) I),
    Finset.restrict₂_comp_restrict]
  exact (hbl.intervalLaw_map_restrict_eq (subset_Icc_boundOf J) (by omega)
    (by have := boundOf_nonneg J; omega) hJ).symm

lemma isProbabilityMeasure_boundaryLawFDD (Λ : Finset ℤ) :
    IsProbabilityMeasure (boundaryLawFDD Q ℓ r Λ) := by
  constructor
  rw [boundaryLawFDD, Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) Λ)
    MeasurableSet.univ, Set.preimage_univ]
  exact hbl.intervalLaw_univ (by have := boundOf_nonneg Λ; omega)

lemma exists_isProjectiveLimit_boundaryLawFDD :
    ∃ μ : Measure (ℤ → E), IsProjectiveLimit μ (boundaryLawFDD Q ℓ r) := by
  have : ∀ Λ, IsFiniteMeasure (boundaryLawFDD Q ℓ r Λ) := fun Λ ↦ by
    have := hbl.isProbabilityMeasure_boundaryLawFDD Λ
    infer_instance
  exact exists_isProjectiveLimit_of_standardBorel hbl.isProjectiveMeasureFamily_boundaryLawFDD

end IsBoundaryLaw

variable {Q ℓ r}

/-- **Georgii (11.9)(a), the measure.** The probability measure `μ` on `E^ℤ` with the cylinder
probabilities (11.10), `μ(σ_a = x_a, …, σ_b = x_b) = ℓ_a(x_a) Q(x_a, x_{a+1}) ⋯ Q(x_{b-1}, x_b)
r_b(x_b)`, obtained from a boundary law by Kolmogorov's extension theorem. -/
def boundaryLawMeasure (hbl : IsBoundaryLaw Q ℓ r) : Measure (ℤ → E) :=
  hbl.exists_isProjectiveLimit_boundaryLawFDD.choose

namespace IsBoundaryLaw

variable (hbl : IsBoundaryLaw Q ℓ r)
include hbl

lemma isProjectiveLimit_boundaryLawMeasure :
    IsProjectiveLimit (boundaryLawMeasure hbl) (boundaryLawFDD Q ℓ r) :=
  hbl.exists_isProjectiveLimit_boundaryLawFDD.choose_spec

instance isProbabilityMeasure_boundaryLawMeasure :
    IsProbabilityMeasure (boundaryLawMeasure hbl) := by
  constructor
  have h := hbl.isProjectiveLimit_boundaryLawMeasure (∅ : Finset ℤ)
  have := hbl.isProbabilityMeasure_boundaryLawFDD (∅ : Finset ℤ)
  calc boundaryLawMeasure hbl Set.univ
      = ((boundaryLawMeasure hbl).map (∅ : Finset ℤ).restrict) Set.univ := by
        rw [Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) _)
          MeasurableSet.univ, Set.preimage_univ]
    _ = boundaryLawFDD Q ℓ r ∅ Set.univ := by rw [h]
    _ = 1 := measure_univ

/-- **Georgii (11.10).** -/
theorem boundaryLawMeasure_intervalCylinder {a b : ℤ} (hab : a ≤ b) (σ : ℤ → E) :
    boundaryLawMeasure hbl (intervalCylinder a b σ)
      = ℓ a (σ a) * pathProd Q a b σ * r b (σ b) := by
  rw [intervalCylinder_eq_preimage, ← Measure.map_apply
    (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) _) (measurableSet_singleton _),
    hbl.isProjectiveLimit_boundaryLawMeasure, hbl.boundaryLawFDD_eq le_rfl hab,
    Measure.map_apply (Finset.measurable_restrict (X := fun _ : ℤ ↦ E) _)
      (measurableSet_singleton _),
    ← intervalCylinder_eq_preimage, intervalLaw,
    withDensity_apply _ (measurableSet_intervalCylinder a b σ),
    intervalCylinder_eq_cyl a b σ,
    setLIntegral_lambdaCount_cyl' _ _ _ (measurable_boundaryLawWeight Q ℓ r a b),
    boundaryLawWeight_congr Q ℓ r (τ := σ)
      (fun k hk ↦ juxt_apply_of_mem (Finset.mem_coe.2 hk) _) hab]
  rfl

/-- **Georgii (11.9)(a), uniqueness of the measure.** A probability measure with the cylinder
probabilities (11.10) is `boundaryLawMeasure`. -/
theorem eq_boundaryLawMeasure_of_forall_intervalCylinder {μ : Measure (ℤ → E)}
    [IsProbabilityMeasure μ]
    (h : ∀ a b : ℤ, a ≤ b → ∀ σ : ℤ → E,
      μ (intervalCylinder a b σ) = ℓ a (σ a) * pathProd Q a b σ * r b (σ b)) :
    μ = boundaryLawMeasure hbl :=
  ext_of_centredCylinders 0 fun a b ha hb σ ↦ by
    rw [h a b (by omega) σ, hbl.boundaryLawMeasure_intervalCylinder (by omega)]

end IsBoundaryLaw

end BoundaryLawMeasure

/-! ## Georgii Theorem (11.9)(a): the measure of a boundary law is a Gibbs measure for `γ^Q` -/

section Gibbs

variable (Q : E → E → ℝ≥0∞)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_split_middle {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) :
    pathProd Q a b σ = pathProd Q a (i - 1) σ * (Q (σ (i - 1)) (σ i) * Q (σ i) (σ (i + 1)))
      * pathProd Q (i + 1) b σ := by
  rw [pathProd_split Q (show a ≤ i + 1 by omega) (show i + 1 ≤ b by omega),
    pathProd_split Q (show a ≤ i - 1 by omega) (show i - 1 ≤ i + 1 by omega),
    pathProd_split Q (show i - 1 ≤ i by omega) (show i ≤ i + 1 by omega), pathProd_pred,
    pathProd_succ]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
lemma pathProd_update_middle {a b i : ℤ} (hai : a < i) (hib : i < b) (σ : ℤ → E) (y : E) :
    pathProd Q a b (Function.update σ i y)
      = pathProd Q a (i - 1) σ * (Q (σ (i - 1)) y * Q y (σ (i + 1))) * pathProd Q (i + 1) b σ := by
  rw [pathProd_split_middle Q hai hib,
    pathProd_update_of_notMem Q (show i ∉ Finset.Icc a (i - 1) by simp),
    pathProd_update_of_notMem Q (show i ∉ Finset.Icc (i + 1) b by simp), Function.update_self,
    Function.update_of_ne (show i - 1 ≠ i by omega),
    Function.update_of_ne (show i + 1 ≠ i by omega)]

variable [Nonempty E] {Q} (hQ : IsTransferMatrix Q) {ℓ r : ℤ → E → ℝ≥0∞}
  (hbl : IsBoundaryLaw Q ℓ r)
include hQ hbl

/-- **Georgii Theorem (11.9)(a).** The probability measure (11.10) of a boundary law for a
positive matrix `Q` with finite powers is a Gibbs measure for `γ^Q`: `μ ∈ 𝒢(Q)`. -/
theorem isGibbsMeasure_transferSpecification_boundaryLawMeasure :
    (transferSpecification Q hQ).IsGibbsMeasure (boundaryLawMeasure hbl) := by
  refine (Specification.lambdaSpecification_isGibbsMeasure_iff_forall_singleton_bind_eq
    (S := ℤ) (E := E) Measure.count (isPremodifier_transferWeight Q)
    (fun Λ ω ↦ (transferWeight_pos Q hQ.pos Λ ω).ne')
    (fun Λ ω ↦ transferWeight_ne_top Q hQ.ne_top Λ ω)
    hQ.isSigmaFiniteLambdaAdmissible).2 fun i ↦ ?_
  change (boundaryLawMeasure hbl).bind (transferSpecification Q hQ {i}) = boundaryLawMeasure hbl
  have hmeas : Measurable (transferSpecification Q hQ {i}) :=
    (transferSpecification Q hQ {i}).measurable.mono cylinderEvents_le_pi le_rfl
  have hprob : IsProbabilityMeasure
      ((boundaryLawMeasure hbl).bind (transferSpecification Q hQ {i})) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
    simp
  refine ext_of_centredCylinders i fun a b hai hib σ ↦ ?_
  have hi : i ∈ Finset.Icc a b := Finset.mem_Icc.2 ⟨hai.le, hib.le⟩
  rw [Measure.bind_apply (measurableSet_intervalCylinder a b σ) hmeas.aemeasurable]
  simp_rw [transferSpecification_singleton_apply_intervalCylinder Q hQ hai hib σ]
  rw [lintegral_indicator (measurableSet_puncturedCylinder a b i σ), setLIntegral_const,
    measure_puncturedCylinder_tsum _ hi σ]
  simp_rw [hbl.boundaryLawMeasure_intervalCylinder (show a ≤ b by omega),
    pathProd_update_middle Q hai hib, Function.update_of_ne (show a ≠ i by omega),
    Function.update_of_ne (show b ≠ i by omega)]
  have hre : ∀ y, ℓ a (σ a) * (pathProd Q a (i - 1) σ * (Q (σ (i - 1)) y * Q y (σ (i + 1)))
        * pathProd Q (i + 1) b σ) * r b (σ b)
      = (Q (σ (i - 1)) y * Q y (σ (i + 1)))
        * (ℓ a (σ a) * (pathProd Q a (i - 1) σ * pathProd Q (i + 1) b σ) * r b (σ b)) :=
    fun y ↦ by ring
  simp_rw [hre, ENNReal.tsum_mul_right, ← Kernel.ofMatrix_pow_two_apply_singleton]
  rw [pathProd_split_middle Q hai hib, ← mul_assoc,
    ENNReal.div_mul_cancel (hQ.pow_two_pos _ _).ne' (hQ.pow_two_ne_top _ _)]
  ring

end Gibbs

/-! ## The finite state space of Chapter 3 as an instance -/

section FiniteState

variable [Fintype E] [DecidableEq E] [Nonempty E] (P : Matrix E E ℝ)

omit [Fintype E] [DecidableEq E] [Nonempty E] in
/-- The transfer matrix of a positive real matrix. -/
lemma isTransferMatrix_ofReal [Finite E] (hpos : ∀ x y, 0 < P x y) :
    IsTransferMatrix fun x y ↦ ENNReal.ofReal (P x y) :=
  isTransferMatrix_of_finite (fun x y ↦ ENNReal.ofReal_pos.2 (hpos x y))
    fun _ _ ↦ ENNReal.ofReal_ne_top

omit [Countable E] [MeasurableSingletonClass E] [Fintype E] [DecidableEq E] [Nonempty E] in
/-- The Boltzmann factor of the potential `-log P` of Chapter 3 is the transfer weight of `P`. -/
lemma boltzmannFactor_markovPotential [Finite E] (hpos : ∀ x y, 0 < P x y) :
    (markovPotential P).boltzmannFactor 1 = transferWeight fun x y ↦ ENNReal.ofReal (P x y) := by
  cases nonempty_fintype E
  funext Λ σ
  rw [boltzmannFactor_eq_prod_bondsOf hpos, transferWeight,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (hpos _ _).le]

omit [Countable E] [MeasurableSingletonClass E] [Fintype E] [DecidableEq E] [Nonempty E] in
lemma uniformOn_univ_eq_smul_count :
    (uniformOn (Set.univ : Set E) : Measure E)
      = (Measure.count (Set.univ : Set E))⁻¹ • (Measure.count : Measure E) := by
  rw [uniformOn, ProbabilityTheory.cond, Measure.restrict_univ]

omit [DecidableEq E] in
/-- **Chapter 3 is the finite-state case of Chapter 11.** The Markov specification `γ_P` of a
positive stochastic matrix `P` (Georgii (3.5)) is the transfer-matrix specification `γ^P`: the
uniform reference measure of `markovSpecification` and counting measure give the same
specification (Remark (1.28)(3)). -/
theorem markovSpecification_eq_transferSpecification (hpos : ∀ x y, 0 < P x y) :
    markovSpecification P
      = transferSpecification (fun x y ↦ ENNReal.ofReal (P x y))
          (isTransferMatrix_ofReal P hpos) := by
  have hρ : Specification.IsPremodifier (S := ℤ) (E := E) ((markovPotential P).boltzmannFactor 1) :=
    Potential.isPremodifier_boltzmannFactor 1
  have hZu : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E)
      (uniformOn Set.univ) ((markovPotential P).boltzmannFactor 1) :=
    (Specification.isPremodifierAdmissible_iff_isSigmaFiniteLambdaAdmissible _ _).1
      (Potential.isPremodifierAdmissible_boltzmannFactor _ 1)
  have hbf := boltzmannFactor_markovPotential P hpos
  have hZc : Specification.IsSigmaFiniteLambdaAdmissible (S := ℤ) (E := E) Measure.count
      ((markovPotential P).boltzmannFactor 1) := by
    rw [hbf]; exact (isTransferMatrix_ofReal P hpos).isSigmaFiniteLambdaAdmissible
  have hc0 : (Measure.count (Set.univ : Set E))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have hct : (Measure.count (Set.univ : Set E))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.2 (Measure.measure_univ_ne_zero.2 (NeZero.ne _))
  calc markovSpecification P
      = Specification.lambdaSpecification (S := ℤ) (E := E) (uniformOn Set.univ)
          ((markovPotential P).boltzmannFactor 1) hρ hZu :=
        (Specification.lambdaSpecification_eq_modification_isssd _ hρ hZu).symm
    _ = Specification.lambdaSpecification (S := ℤ) (E := E) Measure.count
          ((markovPotential P).boltzmannFactor 1) hρ hZc := by
        refine Specification.ext fun Λ ↦ ?_
        rw [Specification.coe_lambdaSpecification, Specification.coe_lambdaSpecification,
          Specification.sigmaFinitePremodifierKernel, Specification.sigmaFinitePremodifierKernel]
        exact congrFun (Specification.modificationKer_sigmaFiniteLambdaFun_of_smul (S := ℤ) (E := E)
          Measure.count (uniformOn Set.univ) hc0 hct uniformOn_univ_eq_smul_count hρ.measurable
          _ _) Λ
    _ = transferSpecification (fun x y ↦ ENNReal.ofReal (P x y)) (isTransferMatrix_ofReal P hpos) :=
        Specification.lambdaSpecification_congr _ hbf hρ hZc _ _

variable (hP : P ∈ Matrix.rowStochastic ℝ E) (hpos : ∀ x y, 0 < P x y)

/-- The stationary distribution `α_P` of a positive stochastic matrix, with `r_i ≡ 1`, is a
boundary law for `P` (Georgii's remark after (11.8): an entrance law is a boundary law). -/
theorem isBoundaryLaw_stationaryDist :
    IsBoundaryLaw (fun x y ↦ ENNReal.ofReal (P x y))
      (fun _ x ↦ ENNReal.ofReal (stationaryDist P hP hpos x)) (fun _ _ ↦ 1) := by
  have hα := stationaryDist_mem_stdSimplex P hP hpos
  refine IsBoundaryLaw.of_tsum (fun _ x ↦ ENNReal.ofReal_pos.2 (stationaryDist_pos P hP hpos x))
    (fun _ _ ↦ ENNReal.ofReal_ne_top) (fun _ _ ↦ one_pos) (fun _ _ ↦ ENNReal.one_ne_top)
    (fun _ y ↦ ?_) (fun _ x ↦ ?_) fun _ ↦ ?_
  · rw [tsum_fintype]
    simp_rw [← ENNReal.ofReal_mul (hα.1 _)]
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (hα.1 x) (hpos x y).le]
    exact congrArg ENNReal.ofReal (congrFun (vecMul_stationaryDist P hP hpos) y)
  · simp_rw [mul_one]
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun y _ ↦ (hpos x y).le,
      Matrix.sum_row_of_mem_rowStochastic hP x, ENNReal.ofReal_one]
  · simp_rw [mul_one]
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hα.1 x, hα.2, ENNReal.ofReal_one]

/-- **Georgii (3.3) as an instance of (11.10).** The stationary Markov chain `μ_P` of Chapter 3
is the measure of the boundary law `ℓ_i = α_P`, `r_i = 1`. -/
theorem stationaryChain_eq_boundaryLawMeasure :
    stationaryChain P hP hpos = boundaryLawMeasure (isBoundaryLaw_stationaryDist P hP hpos) := by
  have := isProbabilityMeasure_stationaryChain P hP hpos
  refine (isBoundaryLaw_stationaryDist P hP hpos).eq_boundaryLawMeasure_of_forall_intervalCylinder
    fun a b hab σ ↦ ?_
  have hα := stationaryDist_mem_stdSimplex P hP hpos
  rw [intervalCylinder_eq_cyl a b σ, markovChain_cylinder P hP hpos hab σ, mul_one, pathProd,
    ENNReal.ofReal_mul (hα.1 _), ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (hpos _ _).le]

end FiniteState

end MeasureTheory.GibbsMeasure.Markov

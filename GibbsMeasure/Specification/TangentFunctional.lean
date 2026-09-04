/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.Analysis.Convex.TangentFunctional
public import GibbsMeasure.Potential.Space
public import GibbsMeasure.Specification.Pressure

/-!
# The Banach space `ℬ_Θ` and the tangent functionals of the pressure (Georgii §16.1)

Georgii's Chapter 16 takes place in the Banach space `ℬ_Θ` of shift-invariant absolutely summable
potentials, normed by `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖` (Georgii (15.21), which is `Potential.normAt 0`).

* `Potential.BTheta S E` is `ℬ_Θ`: the `ℝ`-submodule of `Potential.absolutelySummable S E`
  (Georgii's `ℬ`) cut out by shift invariance, viewed as a submodule of `Potential S E` so that
  it carries the *norm* topology of `‖·‖₀` rather than the Fréchet topology of `ℬ`. On
  shift-invariant potentials all of Georgii's seminorms `‖·‖ᵢ` agree with `‖·‖₀`
  (`Potential.IsShiftInvariant.normAt_eq`), and `‖·‖₀` separates points, so `ℬ_Θ` is a normed
  space; it is complete (`Potential.BTheta.instCompleteSpace`).
* `Potential.BTheta.pressure ν Φ = P(Φ)` is Georgii's pressure (15.31), (15.36) as a function on
  `ℬ_Θ`.

## Main results

* `Potential.BTheta.convexOn_pressure`, `Potential.BTheta.lipschitzWith_pressure`:
  **Georgii Proposition (16.1)** on `ℬ_Θ`, `P` is convex and `1`-Lipschitz.
* `Potential.BTheta.leftDirDeriv_le_rightDirDeriv_pressure`: **(16.2)**.
* `Potential.BTheta.isGδ_dense_setOf_differentiable_directions_pressure`: **(16.3)**.
* `Potential.BTheta.subgradientAt_pressure_nonempty`,
  `Potential.BTheta.exists_mem_subgradientAt_pressure_apply_eq`,
  `Potential.BTheta.le_rightDirDeriv_pressure_of_mem_subgradientAt`: **(16.6)**.
* `Potential.BTheta.exists_mem_subgradientAt_pressure_of_isBoundedBy`: **(16.7)** with
  **(16.8)** and **(16.9)**.

The convex analysis itself (one-sided directional derivatives, tangent functionals, Hahn–Banach,
Baire) is `GibbsMeasure/Mathlib/Analysis/Convex/TangentFunctional.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory Set Topology
open MeasureTheory.GibbsMeasure Transformation
open scoped ENNReal NNReal Topology

noncomputable section

namespace Potential

variable {S E : Type*} [AddGroup S] [MeasurableSpace E]

variable (S E) in
/-- **Georgii's `ℬ_Θ`**: the shift-invariant potentials of `ℬ` (`Potential.absolutelySummable`),
as an `ℝ`-submodule of `Potential S E`. -/
def BTheta : Submodule ℝ (Potential S E) where
  carrier := {Φ | Φ ∈ absolutelySummable S E ∧ Φ.IsShiftInvariant}
  add_mem' hΦ hΨ := ⟨(absolutelySummable S E).add_mem hΦ.1 hΨ.1, hΦ.2.add hΨ.2⟩
  zero_mem' := ⟨(absolutelySummable S E).zero_mem, fun _ ↦ map_zero _⟩
  smul_mem' c _ hΦ := ⟨(absolutelySummable S E).smul_mem c hΦ.1, hΦ.2.smul c⟩

namespace BTheta

@[simp] lemma mem_BTheta {Φ : Potential S E} :
    Φ ∈ BTheta S E ↔ Φ ∈ absolutelySummable S E ∧ Φ.IsShiftInvariant := Iff.rfl

instance (Φ : BTheta S E) : IsAbsolutelySummable (Φ : Potential S E) := Φ.2.1.1

instance (Φ : BTheta S E) : IsPotential (Φ : Potential S E) := Φ.2.1.2.2

lemma isShiftInvariant (Φ : BTheta S E) : (Φ : Potential S E).IsShiftInvariant := Φ.2.2

lemma coe_apply_empty (Φ : BTheta S E) : (Φ : Potential S E) ∅ = 0 := Φ.2.1.2.1

/-- The underlying element of Georgii's `ℬ`. -/
def toB (Φ : BTheta S E) : absolutelySummable S E := ⟨(Φ : Potential S E), Φ.2.1⟩

@[simp] lemma coe_toB (Φ : BTheta S E) : (toB Φ : Potential S E) = (Φ : Potential S E) := rfl

/-! ### The norm `‖Φ‖₀` of Georgii (15.21) -/

instance : Norm (BTheta S E) := ⟨fun Φ ↦ ((Φ : Potential S E).normAt 0).toReal⟩

lemma norm_def (Φ : BTheta S E) : ‖Φ‖ = ((Φ : Potential S E).normAt 0).toReal := rfl

lemma normAt_ne_top (Φ : BTheta S E) (i : S) : (Φ : Potential S E).normAt i ≠ ⊤ :=
  IsAbsolutelySummable.normAt_ne_top i

lemma norm_eq_normAt (Φ : BTheta S E) (i : S) :
    ‖Φ‖ = ((Φ : Potential S E).normAt i).toReal := by
  rw [norm_def, (isShiftInvariant Φ).normAt_eq i]

/-- Every interaction term is dominated by `‖Φ‖₀`, at every site of its support. -/
lemma abs_apply_le_norm (Φ : BTheta S E) {A : Finset S} {i : S} (hi : i ∈ A) (η : S → E) :
    |(Φ : Potential S E) A η| ≤ ‖Φ‖ := by
  rw [norm_eq_normAt Φ i]
  exact abs_apply_le_seminormAt (toB Φ) hi η

instance : NormedAddCommGroup (BTheta S E) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := norm
      map_zero' := by rw [norm_def]; simp
      neg' := fun Φ ↦ by
        rw [norm_def, norm_def, Submodule.coe_neg, normAt_neg]
      add_le' := fun Φ Ψ ↦ by
        rw [norm_def, norm_def, norm_def, Submodule.coe_add,
          ← ENNReal.toReal_add (normAt_ne_top Φ 0) (normAt_ne_top Ψ 0)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.2 ⟨normAt_ne_top Φ 0, normAt_ne_top Ψ 0⟩) (normAt_add_le _ _ 0)
      eq_zero_of_map_eq_zero' := fun Φ hΦ ↦ by
        refine Subtype.ext (funext fun A ↦ funext fun η ↦ ?_)
        rcases A.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
        · rw [coe_apply_empty Φ]; rfl
        · have := abs_apply_le_norm Φ hi η
          rw [hΦ] at this
          have h0 : (Φ : Potential S E) A η = 0 := abs_nonpos_iff.1 this
          rw [h0]; rfl }

instance : NormedSpace ℝ (BTheta S E) where
  norm_smul_le c Φ := by
    rw [norm_def, norm_def, Submodule.coe_smul, normAt_smul, ENNReal.toReal_mul,
      Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg c), Real.norm_eq_abs]

lemma normAt_sub_ne_top (Φ Ψ : BTheta S E) (i : S) :
    ((Φ : Potential S E) - (Ψ : Potential S E)).normAt i ≠ ⊤ := by
  have h := normAt_ne_top (Φ - Ψ) i
  rwa [Submodule.coe_sub] at h

lemma normAt_sub_eq_ofReal (Φ Ψ : BTheta S E) (i : S) :
    ((Φ : Potential S E) - (Ψ : Potential S E)).normAt i = ENNReal.ofReal ‖Φ - Ψ‖ := by
  rw [← ENNReal.ofReal_toReal (normAt_sub_ne_top Φ Ψ i), norm_eq_normAt (Φ - Ψ) i,
    Submodule.coe_sub]

/-! ### Completeness: `ℬ_Θ` is a Banach space -/

/-- **Georgii, Chapter 16, opening paragraph:** `ℬ_Θ` is a Banach space. The proof is the usual
one for a space of summable families: the interaction terms converge uniformly because
`|Φ_A(η)| ≤ ‖Φ‖₀` whenever `0 ∈ A` (and hence, by shift invariance, for every `A ≠ ∅`), the
limit is again a shift-invariant potential, and `‖·‖₀` is lower semicontinuous along pointwise
convergence (`Potential.normAt_le_liminf`). -/
instance instCompleteSpace : CompleteSpace (BTheta S E) := by
  classical
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖u n - u m‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    exact ⟨N, fun m hm n hn ↦ by rw [← dist_eq_norm]; exact hN n hn m hm⟩
  have hptw : ∀ (A : Finset S) (η : S → E), A.Nonempty →
      CauchySeq fun n ↦ (u n : Potential S E) A η := by
    intro A η hA
    obtain ⟨i, hi⟩ := hA
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    rw [Real.dist_eq]
    calc |(u m : Potential S E) A η - (u n : Potential S E) A η|
        = |((u m - u n : BTheta S E) : Potential S E) A η| := by
          rw [Submodule.coe_sub, sub_apply]
      _ ≤ ‖u m - u n‖ := abs_apply_le_norm _ hi η
      _ < ε := hN n hn m hm
  choose! L hL using fun (A : Finset S) (η : S → E) (hA : A.Nonempty) ↦
    cauchySeq_tendsto_of_complete (hptw A η hA)
  set Ψ : Potential S E := fun A η ↦ if A.Nonempty then L A η else 0 with hΨdef
  have hΨ_empty : Ψ ∅ = 0 := by funext η; simp [hΨdef]
  have hconv : ∀ A η, Tendsto (fun n ↦ (u n : Potential S E) A η) atTop (𝓝 (Ψ A η)) := by
    intro A η
    by_cases hA : A.Nonempty
    · simp only [hΨdef, ite_eq_left hA]
      exact hL A η hA
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      simp only [hΨdef, Finset.not_nonempty_empty, ite_false]
      have hz : ∀ n, (u n : Potential S E) ∅ η = 0 := fun n ↦ by rw [coe_apply_empty]; rfl
      simp only [hz]
      exact tendsto_const_nhds
  have hbdd : ∀ i : S, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ n in atTop, (u n : Potential S E).normAt i ≤ C := by
    intro i
    obtain ⟨N, hN⟩ := hcauchy 1 one_pos
    refine ⟨(u N : Potential S E).normAt i + 1,
      ENNReal.add_ne_top.2 ⟨normAt_ne_top _ i, ENNReal.one_ne_top⟩, ?_⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    calc (u n : Potential S E).normAt i
        ≤ (u N : Potential S E).normAt i
          + ((u n : Potential S E) - (u N : Potential S E)).normAt i :=
          normAt_le_normAt_add_normAt_sub _ _ i
      _ ≤ (u N : Potential S E).normAt i + 1 := by
          gcongr
          rw [normAt_sub_eq_ofReal (u n) (u N) i]
          exact (ENNReal.ofReal_le_ofReal (hN N le_rfl n hn).le).trans (by simp)
  have hΨ_summable : IsAbsolutelySummable Ψ := by
    refine ⟨fun i ↦ ?_⟩
    obtain ⟨C, hC, hev⟩ := hbdd i
    exact ne_top_of_le_ne_top hC
      ((normAt_le_liminf hconv i).trans (liminf_le_of_frequently_le' hev.frequently))
  have hΨ_pot : IsPotential Ψ := by
    refine ⟨fun Δ ↦ ?_⟩
    rcases Δ.eq_empty_or_nonempty with rfl | _
    · rw [hΨ_empty]
      exact @measurable_const _ _ _ (cylinderEvents (X := fun _ : S ↦ E) (∅ : Finset S)) _
    · let : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
      exact measurable_of_tendsto_metrizable (fun n ↦ IsPotential.measurable (Φ := (u n :
        Potential S E)) Δ) (tendsto_pi_nhds.2 fun η ↦ hconv Δ η)
  have hΨ_shift : Ψ.IsShiftInvariant := by
    rw [isShiftInvariant_iff]
    intro j A η
    have h1 := hconv (A.map (Equiv.addRight j).toEmbedding) ((shift E j).toFun η)
    have h2 : ∀ n, (u n : Potential S E) (A.map (Equiv.addRight j).toEmbedding)
        ((shift E j).toFun η) = (u n : Potential S E) A η :=
      fun n ↦ (isShiftInvariant_iff _).1 (isShiftInvariant (u n)) j A η
    simp only [h2] at h1
    exact tendsto_nhds_unique h1 (hconv A η)
  refine ⟨⟨Ψ, ⟨hΨ_summable, hΨ_empty, hΨ_pot⟩, hΨ_shift⟩, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_def, Submodule.coe_sub]
  have hconv' : ∀ A η, Tendsto (fun m ↦ ((u n : Potential S E) - (u m : Potential S E)) A η)
      atTop (𝓝 (((u n : Potential S E) - Ψ) A η)) := by
    intro A η
    simp only [sub_apply]
    exact tendsto_const_nhds.sub (hconv A η)
  have hle : ((u n : Potential S E) - Ψ).normAt 0 ≤ ENNReal.ofReal (ε / 2) := by
    refine (normAt_le_liminf hconv' 0).trans
      (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop N] with m hm
    rw [normAt_sub_eq_ofReal (u n) (u m) 0]
    exact ENNReal.ofReal_le_ofReal (hN m hm n hn).le
  calc (((u n : Potential S E) - Ψ).normAt 0).toReal
      ≤ ε / 2 := by
        rw [← ENNReal.toReal_ofReal (half_pos hε).le]
        exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ < ε := half_lt_self hε

/-! ### The pressure on `ℬ_Θ` -/

section Pressure

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace E]
  (ν : Measure E) [IsProbabilityMeasure ν]

/-- **Georgii (15.31), (15.36):** the pressure `P` as a real function on the Banach space
`ℬ_Θ`. -/
def pressure (Φ : BTheta (ι → ℤ) E) : ℝ := (Φ : Potential (ι → ℤ) E).pressure ν

lemma pressure_apply (Φ : BTheta (ι → ℤ) E) :
    pressure ν Φ = (Φ : Potential (ι → ℤ) E).pressure ν := rfl

/-- **Georgii Proposition (16.1), convexity**, on `ℬ_Θ`. -/
theorem convexOn_pressure : ConvexOn ℝ (univ : Set (BTheta (ι → ℤ) E)) (pressure ν) := by
  refine ⟨convex_univ, fun Φ _ Ψ _ a b ha hb hab ↦ ?_⟩
  have hcoe : ((a • Φ + b • Ψ : BTheta (ι → ℤ) E) : Potential (ι → ℤ) E)
      = a • (Φ : Potential (ι → ℤ) E) + b • (Ψ : Potential (ι → ℤ) E) := by
    rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  simp only [pressure_apply, hcoe, smul_eq_mul]
  exact Potential.pressure_smul_add_smul_le ν (isShiftInvariant Φ) (isShiftInvariant Ψ) ha hb hab

/-- **Georgii Proposition (16.1), Lipschitz continuity**: `|P(Φ) − P(Ψ)| ≤ ‖Φ − Ψ‖₀`. -/
theorem lipschitzWith_pressure : LipschitzWith 1 (pressure (ι := ι) ν) := by
  refine LipschitzWith.of_dist_le_mul fun Φ Ψ ↦ ?_
  rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm, norm_def, Submodule.coe_sub,
    pressure_apply, pressure_apply]
  exact Potential.abs_pressure_sub_le (Φ := (Φ : Potential (ι → ℤ) E))
    (Ψ := (Ψ : Potential (ι → ℤ) E)) ν (isShiftInvariant Φ) (isShiftInvariant Ψ)

/-! ### Georgii (16.2): the one-sided directional derivatives of `P` -/

/-- **Georgii (16.2):** `∂⁻_Ψ P(Φ) ≤ ∂⁺_Ψ P(Φ)`. -/
theorem leftDirDeriv_le_rightDirDeriv_pressure (Φ Ψ : BTheta (ι → ℤ) E) :
    leftDirDeriv (pressure ν) Φ Ψ ≤ rightDirDeriv (pressure ν) Φ Ψ :=
  (convexOn_pressure ν).leftDirDeriv_le_rightDirDeriv Φ Ψ

/-- **Georgii (16.2):** `∂⁺_Ψ P(Φ)` is the limit of the difference quotients from the right. -/
theorem tendsto_dirSlope_rightDirDeriv_pressure (Φ Ψ : BTheta (ι → ℤ) E) :
    Tendsto (dirSlope (pressure ν) Φ Ψ) (𝓝[>] 0) (𝓝 (rightDirDeriv (pressure ν) Φ Ψ)) :=
  (convexOn_pressure ν).tendsto_dirSlope_rightDirDeriv Φ Ψ

/-- **Georgii (16.2):** `∂⁻_Ψ P(Φ)` is the limit of the difference quotients from the left. -/
theorem tendsto_dirSlope_leftDirDeriv_pressure (Φ Ψ : BTheta (ι → ℤ) E) :
    Tendsto (dirSlope (pressure ν) Φ Ψ) (𝓝[<] 0) (𝓝 (leftDirDeriv (pressure ν) Φ Ψ)) :=
  (convexOn_pressure ν).tendsto_dirSlope_leftDirDeriv Φ Ψ

/-! ### Georgii (16.6): the tangent functionals `∂P(Φ)` -/

/-- **Georgii Remark (16.6)(1):** `∂⁻_Ψ P(Φ) ≤ L(Ψ) ≤ ∂⁺_Ψ P(Φ)` for `L ∈ ∂P(Φ)`. -/
theorem leftDirDeriv_le_and_le_rightDirDeriv_pressure {Φ : BTheta (ι → ℤ) E}
    {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt (pressure ν) Φ)
    (Ψ : BTheta (ι → ℤ) E) :
    leftDirDeriv (pressure ν) Φ Ψ ≤ L Ψ ∧ L Ψ ≤ rightDirDeriv (pressure ν) Φ Ψ :=
  ⟨(convexOn_pressure ν).leftDirDeriv_le_of_mem_subgradientAt hL Ψ,
    ConvexOn.le_rightDirDeriv_of_mem_subgradientAt hL Ψ⟩

/-- **Georgii Remark (16.6)(1), last sentence:** if `P` is differentiable at `Φ` then
`|∂P(Φ)| ≤ 1`. -/
theorem subgradientAt_pressure_subsingleton {Φ : BTheta (ι → ℤ) E}
    (h : ∀ Ψ, leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ) :
    (subgradientAt (pressure ν) Φ).Subsingleton :=
  (convexOn_pressure ν).subgradientAt_subsingleton h

/-- **Georgii Remark (16.6)(2):** every value between the one-sided derivatives in a direction `Ψ`
is realized by a tangent functional. -/
theorem exists_mem_subgradientAt_pressure_apply_eq (Φ Ψ : BTheta (ι → ℤ) E) {a : ℝ}
    (ha : a ∈ Icc (leftDirDeriv (pressure ν) Φ Ψ) (rightDirDeriv (pressure ν) Φ Ψ)) :
    ∃ L ∈ subgradientAt (pressure ν) Φ, L Ψ = a :=
  (convexOn_pressure ν).exists_mem_subgradientAt_apply_eq Φ Ψ ha

/-- **Georgii Remark (16.6)(2):** `∂P(Φ) ≠ ∅`. -/
theorem subgradientAt_pressure_nonempty (Φ : BTheta (ι → ℤ) E) :
    (subgradientAt (pressure ν) Φ).Nonempty :=
  (convexOn_pressure ν).subgradientAt_nonempty Φ

/-- **Georgii Remark (16.6)(2), last sentence:** if `∂P(Φ) = {L}` then `P` is differentiable at
`Φ` and `∂⁻_Ψ P(Φ) = ∂⁺_Ψ P(Φ) = L(Ψ)`. -/
theorem leftDirDeriv_eq_and_rightDirDeriv_eq_pressure_of_subgradientAt_eq_singleton
    {Φ : BTheta (ι → ℤ) E} {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ}
    (h : subgradientAt (pressure ν) Φ = {L}) (Ψ : BTheta (ι → ℤ) E) :
    leftDirDeriv (pressure ν) Φ Ψ = L Ψ ∧ rightDirDeriv (pressure ν) Φ Ψ = L Ψ :=
  (convexOn_pressure ν).leftDirDeriv_eq_and_rightDirDeriv_eq_of_subgradientAt_eq_singleton h Ψ

/-- **Georgii Remark (16.6)(2):** a unique tangent functional at `Φ` forces differentiability
of `P` at `Φ`. -/
theorem leftDirDeriv_eq_rightDirDeriv_pressure_of_subgradientAt_subsingleton
    {Φ : BTheta (ι → ℤ) E} (h : (subgradientAt (pressure ν) Φ).Subsingleton)
    (Ψ : BTheta (ι → ℤ) E) :
    leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ :=
  (convexOn_pressure ν).leftDirDeriv_eq_rightDirDeriv_of_subgradientAt_subsingleton h Ψ

/-! ### Georgii (16.3): `P` is generically differentiable -/

/-- **Georgii Proposition (16.3).** For a countable set `𝒞` of directions, the set `𝒟` of
potentials at which `P` is differentiable in all directions of `closure 𝒞` is a dense `Gδ`
subset of `ℬ_Θ`; equivalently `ℬ_Θ \ 𝒟` is of first Baire category. -/
theorem isGδ_dense_setOf_differentiable_directions_pressure
    {C : Set (BTheta (ι → ℤ) E)} (hC : C.Countable) :
    IsGδ {Φ : BTheta (ι → ℤ) E | ∀ Ψ ∈ closure C,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ} ∧
      Dense {Φ : BTheta (ι → ℤ) E | ∀ Ψ ∈ closure C,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ} :=
  (convexOn_pressure ν).isGδ_dense_setOf_differentiable_directions (lipschitzWith_pressure ν) hC

/-- **Georgii's remark after (16.3)** (Mazur's theorem): if `ℬ_Θ` is separable — Georgii's example
is `E` finite, where the finite-range potentials with rational values are dense — then `P` is
Gateaux differentiable on a dense `Gδ` subset of `ℬ_Θ`. -/
theorem isGδ_dense_setOf_gateauxDifferentiable_pressure
    [TopologicalSpace.SeparableSpace (BTheta (ι → ℤ) E)] :
    IsGδ {Φ : BTheta (ι → ℤ) E | ∀ Ψ,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ} ∧
      Dense {Φ : BTheta (ι → ℤ) E | ∀ Ψ,
        leftDirDeriv (pressure ν) Φ Ψ = rightDirDeriv (pressure ν) Φ Ψ} :=
  (convexOn_pressure ν).isGδ_dense_setOf_gateauxDifferentiable (lipschitzWith_pressure ν)

/-! ### Georgii (16.7): tangent functionals approximate `P`-bounded functionals -/

/-- **Georgii Proposition (16.7)**, with **(16.8)** and **(16.9)**: given a `P`-bounded linear
functional `L₀` on `ℬ_Θ`, a closed convex cone `C` with vertex `0`, a potential `Φ⁰` and
`ε > 0`, there is `Φ ∈ Φ⁰ + C` carrying a tangent functional `L ∈ ∂P(Φ)` with
`ε‖Φ − Φ⁰‖₀ ≤ P(Φ⁰) − L₀(Φ⁰) − 𝒜(L₀)` and `L(Ψ) ≥ L₀(Ψ) − ε‖Ψ‖₀` for all `Ψ ∈ C`. -/
theorem exists_mem_subgradientAt_pressure_of_isBoundedBy
    {L₀ : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} (hL₀ : IsBoundedBy (pressure ν) L₀)
    {C : Set (BTheta (ι → ℤ) E)} (hC : IsClosed C) (hCconv : Convex ℝ C)
    (hC0 : (0 : BTheta (ι → ℤ) E) ∈ C) (hCadd : ∀ Ψ ∈ C, ∀ Χ ∈ C, Ψ + Χ ∈ C)
    (Φ₀ : BTheta (ι → ℤ) E) {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ, Φ - Φ₀ ∈ C ∧ ∃ L ∈ subgradientAt (pressure ν) Φ,
      ε * ‖Φ - Φ₀‖ ≤ pressure ν Φ₀ - L₀ Φ₀ - negFenchel (pressure ν) L₀ ∧
        ∀ Ψ ∈ C, L₀ Ψ - ε * ‖Ψ‖ ≤ L Ψ :=
  (convexOn_pressure ν).exists_mem_subgradientAt_of_isBoundedBy (lipschitzWith_pressure ν) hL₀
    hC hCconv hC0 hCadd Φ₀ hε

/-- **Georgii, after (16.5):** a tangent functional to `P` is `P`-bounded, and the infimum (16.5)
is attained at the point of tangency. -/
theorem negFenchel_pressure_eq_of_mem_subgradientAt {Φ : BTheta (ι → ℤ) E}
    {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ} (hL : L ∈ subgradientAt (pressure ν) Φ) :
    IsBoundedBy (pressure ν) L ∧ negFenchel (pressure ν) L = pressure ν Φ - L Φ :=
  ⟨isBoundedBy_of_mem_subgradientAt hL, negFenchel_eq_of_mem_subgradientAt hL⟩

/-- A `P`-bounded linear functional on `ℬ_Θ` is automatically continuous, with
`|L(Ψ)| ≤ ‖Ψ‖₀`: this is Georgii's (16.1) behind the reduction to `L₀ = 0` in (16.7). -/
theorem abs_apply_le_norm_of_isBoundedBy {L : BTheta (ι → ℤ) E →ₗ[ℝ] ℝ}
    (hL : IsBoundedBy (pressure ν) L) (Ψ : BTheta (ι → ℤ) E) : |L Ψ| ≤ ‖Ψ‖ := by
  simpa using hL.abs_apply_le (lipschitzWith_pressure ν) Ψ

end Pressure

end BTheta

end Potential

end

end

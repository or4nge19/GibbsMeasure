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
* `Potential.BTheta.countable_finiteRangeRat`, `Potential.BTheta.dense_finiteRangeRat` and the
  instance `Potential.BTheta.instSeparableSpace`: **Georgii's remark after (16.3)**, for a finite
  state space the potentials of finite range with rational values are a countable dense subset of
  `ℬ_Θ`, so `ℬ_Θ` is separable and
  `Potential.BTheta.isGδ_dense_setOf_gateauxDifferentiable_pressure` applies with no hypothesis
  beyond `[Finite E]`.

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

/-! ### Georgii's remark after (16.3): `ℬ_Θ` is separable for a finite state space

Georgii records that for a finite state space the finite-range potentials with rational values are
dense in `ℬ_Θ`. The approximant of `Φ ∈ ℬ_Θ` is `Potential.BTheta.approx 𝒜 m Φ`: keep the
interaction terms carried by the translates of the finitely many volumes of `𝒜` and round their
values to the grid `(1/m)ℤ`. Both operations preserve shift invariance, the first because
`Potential.BTheta.translates 𝒜` is translation invariant and the second because rounding acts on
values. Truncation costs the tail of the convergent series `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖` and rounding
costs `1/m` on each of the finitely many volumes of `translates 𝒜` containing the origin. -/

section Separable

variable {S E : Type*} [AddCommGroup S] [MeasurableSpace E]

/-- The translates `A + j` of the volumes `A` of a finite family `𝒜`: the volumes on which a
finite-range shift-invariant potential built from `𝒜` is allowed to be nonzero. -/
def translates (𝒜 : Finset (Finset S)) : Set (Finset S) :=
  {B | ∃ A ∈ 𝒜, ∃ j : S, B = translate A j}

lemma mem_translates_of_mem {𝒜 : Finset (Finset S)} {A : Finset S} (hA : A ∈ 𝒜) :
    A ∈ translates 𝒜 := ⟨A, hA, 0, (translate_zero A).symm⟩

lemma translate_mem_translates {𝒜 : Finset (Finset S)} {B : Finset S} (hB : B ∈ translates 𝒜)
    (j : S) : translate B j ∈ translates 𝒜 := by
  obtain ⟨A, hA, k, rfl⟩ := hB
  exact ⟨A, hA, k + j, translate_translate A k j⟩

/-- `translates 𝒜` is invariant under translation. -/
@[simp] lemma translate_mem_translates_iff {𝒜 : Finset (Finset S)} {B : Finset S} {j : S} :
    translate B j ∈ translates 𝒜 ↔ B ∈ translates 𝒜 := by
  refine ⟨fun h ↦ ?_, fun h ↦ translate_mem_translates h j⟩
  have h' := translate_mem_translates h (-j)
  rwa [translate_translate, add_neg_cancel, translate_zero] at h'

/-- Only finitely many translates of the volumes of a finite family contain a given site: if
`i ∈ A + j` then `j = i - a` for one of the finitely many `a ∈ A`. -/
lemma finite_translates_mem (𝒜 : Finset (Finset S)) (i : S) :
    {B | B ∈ translates 𝒜 ∧ i ∈ B}.Finite := by
  refine Set.Finite.subset (Set.Finite.biUnion 𝒜.finite_toSet
    fun A _ ↦ (A.finite_toSet.image fun a ↦ translate A (i - a))) ?_
  rintro B ⟨⟨A, hA, j, rfl⟩, hi⟩
  refine Set.mem_biUnion (show A ∈ (𝒜 : Set (Finset S)) from hA) ⟨i - j, mem_translate.1 hi, ?_⟩
  simp

/-- The finite-range rational approximant of a potential: the interaction terms carried by the
translates of the volumes of `𝒜`, with their values rounded to the grid `(1/m)ℤ`. -/
def approx (𝒜 : Finset (Finset S)) (m : ℕ) (Φ : Potential S E) : Potential S E :=
  (translates 𝒜).indicator fun B η ↦ (⌊(m : ℝ) * Φ B η⌋ : ℝ) / m

lemma approx_apply_of_mem {𝒜 : Finset (Finset S)} {m : ℕ} {Φ : Potential S E} {B : Finset S}
    (hB : B ∈ translates 𝒜) (η : S → E) :
    approx 𝒜 m Φ B η = (⌊(m : ℝ) * Φ B η⌋ : ℝ) / m := by
  rw [approx, Set.indicator_of_mem hB]

lemma approx_apply_of_notMem {𝒜 : Finset (Finset S)} {m : ℕ} {Φ : Potential S E} {B : Finset S}
    (hB : B ∉ translates 𝒜) (η : S → E) : approx 𝒜 m Φ B η = 0 := by
  rw [approx, Set.indicator_of_notMem hB]; rfl

/-- The values of the approximant are rational. -/
lemma approx_apply_mem_range_rat {𝒜 : Finset (Finset S)} {m : ℕ} {Φ : Potential S E}
    (B : Finset S) (η : S → E) :
    approx 𝒜 m Φ B η ∈ Set.range ((↑) : ℚ → ℝ) := by
  by_cases hB : B ∈ translates 𝒜
  · exact ⟨(⌊(m : ℝ) * Φ B η⌋ : ℚ) / m, by push_cast [approx_apply_of_mem hB]; ring⟩
  · exact ⟨0, by rw [approx_apply_of_notMem hB]; norm_num⟩

/-- The approximant vanishes off the translates of `𝒜`. -/
lemma approx_apply_eq_zero_of_notMem {𝒜 : Finset (Finset S)} {m : ℕ} {Φ : Potential S E}
    {B : Finset S} (hB : B ∉ translates 𝒜) : approx 𝒜 m Φ B = 0 :=
  funext fun η ↦ approx_apply_of_notMem hB η

/-- Rounding to the grid `(1/m)ℤ` moves each value by at most `1/m`. -/
lemma abs_sub_approx_le {𝒜 : Finset (Finset S)} {m : ℕ} (hm : 0 < m) {Φ : Potential S E}
    {B : Finset S} (hB : B ∈ translates 𝒜) (η : S → E) :
    |Φ B η - approx 𝒜 m Φ B η| ≤ 1 / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [approx_apply_of_mem hB]
  set x := Φ B η with hx
  have h1 : (⌊(m : ℝ) * x⌋ : ℝ) ≤ (m : ℝ) * x := Int.floor_le _
  have h2 : (m : ℝ) * x < (⌊(m : ℝ) * x⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hle : (⌊(m : ℝ) * x⌋ : ℝ) / m ≤ x := by rw [div_le_iff₀ hm']; nlinarith
  have hge : x - (⌊(m : ℝ) * x⌋ : ℝ) / m ≤ 1 / m := by
    have hsplit : (1 : ℝ) / m + (⌊(m : ℝ) * x⌋ : ℝ) / m = ((⌊(m : ℝ) * x⌋ : ℝ) + 1) / m := by
      ring
    rw [sub_le_iff_le_add, hsplit, le_div_iff₀ hm']; nlinarith
  rw [abs_le]
  exact ⟨by simp only [neg_le_sub_iff_le_add]; nlinarith [one_div_pos.2 hm'], hge⟩

/-- Truncating to the translates of a finite family and rounding preserve shift invariance. -/
lemma isShiftInvariant_approx {Φ : Potential S E} (hΦ : Φ.IsShiftInvariant)
    (𝒜 : Finset (Finset S)) (m : ℕ) : (approx 𝒜 m Φ).IsShiftInvariant := by
  rw [isShiftInvariant_iff]
  intro j A η
  by_cases h : A ∈ translates 𝒜
  · rw [approx_apply_of_mem (translate_mem_translates h j), approx_apply_of_mem h,
      (isShiftInvariant_iff Φ).1 hΦ j A η]
  · rw [approx_apply_of_notMem fun hc ↦ h (translate_mem_translates_iff.1 hc),
      approx_apply_of_notMem h]

lemma isPotential_approx (𝒜 : Finset (Finset S)) (m : ℕ) (Φ : Potential S E) [IsPotential Φ] :
    IsPotential (approx 𝒜 m Φ) := by
  refine ⟨fun Δ ↦ ?_⟩
  let : MeasurableSpace (S → E) := cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)
  by_cases h : Δ ∈ translates 𝒜
  · have hmeas : Measurable fun η ↦ (⌊(m : ℝ) * Φ Δ η⌋ : ℝ) / m :=
      (measurable_from_top.comp
        (((IsPotential.measurable (Φ := Φ) Δ).const_mul (m : ℝ)).floor)).div_const _
    have heq : approx 𝒜 m Φ Δ = fun η ↦ (⌊(m : ℝ) * Φ Δ η⌋ : ℝ) / m :=
      funext fun η ↦ approx_apply_of_mem h η
    rw [heq]
    exact hmeas
  · rw [approx_apply_eq_zero_of_notMem h]
    exact measurable_const

/-- **The approximation estimate.** Georgii's norm (15.21) of the error made by truncating `Φ` to
the translates of `𝒜` and rounding to the grid `(1/m)ℤ` is at most `1/m` on each of the finitely
many volumes of `translates 𝒜` containing the origin, plus the tail of `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖`
outside `𝒜`. -/
lemma normAt_sub_approx_le {𝒜 : Finset (Finset S)} {m : ℕ} (hm : 0 < m) (Φ : Potential S E) :
    (Φ - approx 𝒜 m Φ).normAt 0
      ≤ (finite_translates_mem 𝒜 (0 : S)).toFinset.card * ENNReal.ofReal (1 / m)
        + ∑' B : {B : Finset S // B ∉ 𝒜},
            {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) (B : Finset S) := by
  classical
  set g : Finset S → ℝ≥0∞ :=
    fun A ↦ {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A with hg
  set F := (finite_translates_mem 𝒜 (0 : S)).toFinset with hF
  have key : ∀ B : Finset S,
      {A : Finset S | (0 : S) ∈ A}.indicator
          (fun A ↦ ⨆ η, ‖(Φ - approx 𝒜 m Φ) A η‖ₑ) B
        ≤ (F : Set (Finset S)).indicator (fun _ ↦ ENNReal.ofReal (1 / m)) B
          + ((𝒜 : Set (Finset S))ᶜ).indicator g B := by
    intro B
    by_cases h0 : (0 : S) ∈ B
    · rw [Set.indicator_of_mem (show B ∈ {A : Finset S | (0 : S) ∈ A} from h0)]
      by_cases hB : B ∈ translates 𝒜
      · refine le_trans (iSup_le fun η ↦ ?_) le_self_add
        rw [Set.indicator_of_mem (show B ∈ (F : Set (Finset S)) from
          (Set.Finite.mem_toFinset _).2 ⟨hB, h0⟩), Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (by
          simpa using abs_sub_approx_le (𝒜 := 𝒜) hm hB η)
      · have hB𝒜 : B ∈ ((𝒜 : Set (Finset S))ᶜ) := fun hc ↦ hB (mem_translates_of_mem hc)
        rw [Set.indicator_of_mem hB𝒜]
        refine le_trans (le_of_eq ?_) le_add_self
        show _ = {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) B
        rw [Set.indicator_of_mem (show B ∈ {A : Finset S | (0 : S) ∈ A} from h0)]
        exact iSup_congr fun η ↦ by rw [sub_apply, approx_apply_of_notMem hB, sub_zero]
    · rw [Set.indicator_of_notMem (show B ∉ {A : Finset S | (0 : S) ∈ A} from h0)]
      exact bot_le
  refine le_trans (ENNReal.tsum_le_tsum key) ?_
  rw [ENNReal.tsum_add]
  gcongr
  · refine le_of_eq ?_
    rw [tsum_eq_sum (s := F) fun b hb ↦ Set.indicator_of_notMem (by simpa using hb) _]
    rw [Finset.sum_congr rfl fun b hb ↦ Set.indicator_of_mem (by simpa using hb) _,
      Finset.sum_const, nsmul_eq_mul]
  · exact le_of_eq (tsum_subtype ((𝒜 : Set (Finset S))ᶜ) g).symm

/-- `∑_{A ∋ 0, A ∉ 𝒜} ‖Φ_A‖ ≤ ‖Φ‖₀`: the tail of Georgii's norm is bounded by the norm. -/
lemma tsum_subtype_indicator_le_normAt (𝒜 : Finset (Finset S)) (Φ : Potential S E) :
    ∑' B : {B : Finset S // B ∉ 𝒜},
        {A : Finset S | (0 : S) ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) (B : Finset S)
      ≤ Φ.normAt 0 := by
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _

/-- The approximant of a potential of `ℬ_Θ` again lies in `ℬ_Θ`. -/
lemma approx_mem (𝒜 : Finset (Finset S)) {m : ℕ} (hm : 0 < m) (Φ : BTheta S E) :
    approx 𝒜 m (Φ : Potential S E) ∈ BTheta S E := by
  have hshift : (approx 𝒜 m (Φ : Potential S E)).IsShiftInvariant :=
    isShiftInvariant_approx (isShiftInvariant Φ) 𝒜 m
  have hsub : ((Φ : Potential S E) - approx 𝒜 m (Φ : Potential S E)).IsShiftInvariant :=
    (isShiftInvariant Φ).sub hshift
  have hfin : ((Φ : Potential S E) - approx 𝒜 m (Φ : Potential S E)).normAt 0 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (normAt_sub_approx_le hm (Φ : Potential S E))
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (by simp),
      ne_top_of_le_ne_top (normAt_ne_top Φ 0)
        (tsum_subtype_indicator_le_normAt 𝒜 (Φ : Potential S E))⟩
  refine ⟨⟨⟨fun i ↦ ?_⟩, ?_, isPotential_approx 𝒜 m (Φ : Potential S E)⟩, hshift⟩
  · rw [hshift.normAt_eq i]
    refine ne_top_of_le_ne_top ?_
      (normAt_le_normAt_add_normAt_sub (approx 𝒜 m (Φ : Potential S E)) (Φ : Potential S E) 0)
    refine ENNReal.add_ne_top.2 ⟨normAt_ne_top Φ 0, ?_⟩
    rwa [← normAt_neg, neg_sub]
  · funext η
    by_cases h : (∅ : Finset S) ∈ translates 𝒜
    · rw [approx_apply_of_mem h η, coe_apply_empty Φ]
      norm_num
    · rw [approx_apply_of_notMem h η]
      rfl

variable (S E) in
/-- **Georgii's remark after (16.3):** the potentials of finite range with rational values. For a
finite state space this set is countable (`Potential.BTheta.countable_finiteRangeRat`) and dense
(`Potential.BTheta.dense_finiteRangeRat`) in `ℬ_Θ`. Finite range is spelled as vanishing off the
translates of a finite family of volumes. -/
def finiteRangeRat : Set (BTheta S E) :=
  {Ψ | ∃ 𝒜 : Finset (Finset S), (∀ B ∉ translates 𝒜, (Ψ : Potential S E) B = 0) ∧
    ∀ B η, (Ψ : Potential S E) B η ∈ Set.range ((↑) : ℚ → ℝ)}

section Countable

open scoped Classical in
/-- Extend a spin pattern on a finite volume to a configuration, by a fixed spin off the
volume. -/
def extend [Nonempty E] (A : Finset S) (g : {i : S // i ∈ A} → E) : S → E :=
  fun i ↦ if h : i ∈ A then g ⟨i, h⟩ else Classical.arbitrary E

omit [AddCommGroup S] in
/-- An interaction term is determined by the spins inside its volume, so by its values at the
configurations `Potential.BTheta.extend A g`. -/
lemma apply_extend [Nonempty E] (Φ : Potential S E) [IsPotential Φ] (A : Finset S) (η : S → E) :
    Φ A (extend A fun i ↦ η i) = Φ A η := by
  classical
  refine (IsPotential.measurable (Φ := Φ) A).dependsOn_of_cylinderEvents fun i hi ↦ ?_
  simp [extend, Finset.mem_coe.1 hi]

/-- The interaction terms of a shift-invariant potential on the translates of a volume are the
translates of its interaction term on that volume. -/
lemma apply_translate {Φ : Potential S E} (hΦ : Φ.IsShiftInvariant) (A : Finset S) (j : S)
    (η : S → E) : Φ (translate A j) η = Φ A ((shift E j).inv.toFun η) := by
  have h := (isShiftInvariant_iff Φ).1 hΦ j A ((shift E j).inv.toFun η)
  rwa [show (shift E j).toFun ((shift E j).inv.toFun η) = η from funext fun i ↦ by simp] at h

/-- A shift-invariant potential vanishing off `translates 𝒜` is determined by its interaction
terms on the volumes of `𝒜`. -/
lemma eq_of_forall_apply_eq {Φ Ψ : Potential S E} (hΦ : Φ.IsShiftInvariant)
    (hΨ : Ψ.IsShiftInvariant) {𝒜 : Finset (Finset S)}
    (h0Φ : ∀ B ∉ translates 𝒜, Φ B = 0) (h0Ψ : ∀ B ∉ translates 𝒜, Ψ B = 0)
    (h : ∀ A ∈ 𝒜, Φ A = Ψ A) : Φ = Ψ := by
  funext B η
  by_cases hB : B ∈ translates 𝒜
  · obtain ⟨A, hA, j, rfl⟩ := hB
    rw [apply_translate hΦ, apply_translate hΨ, h A hA]
  · rw [h0Φ B hB, h0Ψ B hB]

/-- **Georgii's remark after (16.3):** for a finite state space the potentials of finite range
with rational values form a countable set. Such a potential is determined by the finitely many
interaction terms carried by the volumes of its finite family `𝒜`, and each of these is
determined by finitely many rational numbers, one for each spin pattern on the volume. -/
theorem countable_finiteRangeRat [Countable S] [Finite E] : (finiteRangeRat S E).Countable := by
  rcases isEmpty_or_nonempty E with hE | hE
  · have : Subsingleton (BTheta S E) :=
      ⟨fun Φ Ψ ↦ Subtype.ext (funext fun A ↦ funext fun η ↦ (IsEmpty.false η).elim)⟩
    have : Finite (BTheta S E) := Finite.of_subsingleton
    exact Set.Countable.mono (Set.subset_univ _) (Set.countable_univ_iff.2 inferInstance)
  have hcover : finiteRangeRat S E = ⋃ 𝒜 : Finset (Finset S), {Ψ : BTheta S E |
      (∀ B ∉ translates 𝒜, (Ψ : Potential S E) B = 0) ∧
        ∀ B η, (Ψ : Potential S E) B η ∈ Set.range ((↑) : ℚ → ℝ)} := by
    ext Ψ
    simp [finiteRangeRat]
  rw [hcover]
  refine Set.countable_iUnion fun 𝒜 ↦ ?_
  rw [Set.countable_iff_exists_injOn]
  obtain ⟨e, he⟩ := Countable.exists_injective_nat
    ((A : {A : Finset S // A ∈ 𝒜}) → ({i : S // i ∈ (A : Finset S)} → E) → ℚ)
  refine ⟨fun Ψ ↦ e fun A g ↦
    Function.invFun ((↑) : ℚ → ℝ) ((Ψ : Potential S E) (A : Finset S) (extend (A : Finset S) g)),
    ?_⟩
  rintro Ψ ⟨h0Ψ, hqΨ⟩ Ψ' ⟨h0Ψ', hqΨ'⟩ hEq
  have hfun := he hEq
  refine Subtype.ext (eq_of_forall_apply_eq (isShiftInvariant Ψ) (isShiftInvariant Ψ')
    h0Ψ h0Ψ' fun A hA ↦ ?_)
  funext η
  have hg := congrFun (congrFun hfun ⟨A, hA⟩) fun i ↦ η i
  rw [← apply_extend (Ψ : Potential S E) A η, ← apply_extend (Ψ' : Potential S E) A η,
    ← Function.invFun_eq (hqΨ A (extend A fun i ↦ η i)),
    ← Function.invFun_eq (hqΨ' A (extend A fun i ↦ η i)), hg]

end Countable

/-- **Georgii's remark after (16.3):** the potentials of finite range with rational values are
dense in `ℬ_Θ`. Truncating `Φ` to the translates of a large enough finite family `𝒜` costs the
tail of the convergent series `‖Φ‖₀ = ∑_{A ∋ 0} ‖Φ_A‖`, and rounding the remaining, finitely
many, interaction terms containing the origin to a fine enough grid costs `1/m` on each of
them. -/
theorem dense_finiteRangeRat : Dense (finiteRangeRat S E) := by
  refine Metric.dense_iff.2 fun Φ ε hε ↦ ?_
  set g : Finset S → ℝ≥0∞ :=
    fun A ↦ {A : Finset S | (0 : S) ∈ A}.indicator
      (fun A ↦ ⨆ η, ‖(Φ : Potential S E) A η‖ₑ) A with hg
  have hgtop : ∑' B, g B ≠ ⊤ := normAt_ne_top Φ 0
  obtain ⟨𝒜, h𝒜⟩ : ∃ 𝒜 : Finset (Finset S),
      (∑' B : {B : Finset S // B ∉ 𝒜}, g (B : Finset S)) ≤ ENNReal.ofReal (ε / 4) :=
    (ENNReal.tendsto_nhds_zero.1 (ENNReal.tendsto_tsum_compl_atTop_zero hgtop)
      (ENNReal.ofReal (ε / 4)) (by positivity)).exists
  set N := (finite_translates_mem 𝒜 (0 : S)).toFinset.card with hN
  set m : ℕ := ⌈(4 * N / ε : ℝ)⌉₊ + 1 with hmdef
  have hm0 : 0 < m := Nat.succ_pos _
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmN : (N : ℝ) / m ≤ ε / 4 := by
    have hceil : (4 * N / ε : ℝ) ≤ ⌈(4 * N / ε : ℝ)⌉₊ := Nat.le_ceil _
    have h4 : 4 * (N : ℝ) ≤ ⌈(4 * N / ε : ℝ)⌉₊ * ε := (div_le_iff₀ hε).1 hceil
    have hcast : (m : ℝ) = (⌈(4 * N / ε : ℝ)⌉₊ : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    rw [div_le_div_iff₀ hmR (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  refine ⟨⟨approx 𝒜 m (Φ : Potential S E), approx_mem 𝒜 hm0 Φ⟩, ?_,
    ⟨𝒜, fun B hB ↦ approx_apply_eq_zero_of_notMem hB, fun B η ↦ approx_apply_mem_range_rat B η⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev, norm_def, Submodule.coe_sub]
  have hle : ((Φ : Potential S E) - approx 𝒜 m (Φ : Potential S E)).normAt 0
      ≤ (N : ℝ≥0∞) * ENNReal.ofReal (1 / m) + ENNReal.ofReal (ε / 4) := by
    refine (normAt_sub_approx_le (𝒜 := 𝒜) hm0 (Φ : Potential S E)).trans ?_
    gcongr
  have htop : ((N : ℝ≥0∞) * ENNReal.ofReal (1 / m) + ENNReal.ofReal (ε / 4)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) (by simp), by simp⟩
  calc (((Φ : Potential S E) - approx 𝒜 m (Φ : Potential S E)).normAt 0).toReal
      ≤ ((N : ℝ≥0∞) * ENNReal.ofReal (1 / m) + ENNReal.ofReal (ε / 4)).toReal :=
        ENNReal.toReal_mono htop hle
    _ = (N : ℝ) * (1 / m) + ε / 4 := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (by simp)) (by simp),
          ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
    _ < ε := by
        rw [mul_one_div]
        linarith

/-- **Georgii's remark after (16.3):** for a finite state space, `ℬ_Θ` is separable — the
potentials of finite range with rational values are a countable dense set. -/
instance instSeparableSpace [Countable S] [Finite E] :
    TopologicalSpace.SeparableSpace (BTheta S E) :=
  ⟨⟨finiteRangeRat S E, countable_finiteRangeRat, dense_finiteRangeRat⟩⟩

end Separable

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

/-- **Georgii's remark after (16.3)** (Mazur's theorem): for a finite state space `ℬ_Θ` is
separable (`Potential.BTheta.instSeparableSpace`: the finite-range potentials with rational
values are a countable dense set), so `P` is Gateaux differentiable on a dense `Gδ` subset of
`ℬ_Θ`. -/
theorem isGδ_dense_setOf_gateauxDifferentiable_pressure [Finite E] :
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

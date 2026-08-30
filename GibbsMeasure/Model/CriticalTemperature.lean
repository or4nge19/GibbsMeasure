/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.PhaseTransition
public import GibbsMeasure.Specification.DobrushinUniqueness

/-!
# The critical temperature of the two-dimensional Ising ferromagnet

Georgii, *Gibbs Measures and Phase Transitions*, 2nd ed., Theorems (6.9), (8.7), (8.8).

This file assembles the two halves of Georgii's `0 < β_c < ∞` for the nearest-neighbour Ising
ferromagnet on `ℤ²` with coupling `J = 1` and no external field:

* **high temperature** — Dobrushin's condition (8.8) plus Dobrushin's uniqueness theorem (8.7)
  give `|𝒢(γ_β)| = 1` for `|β| < 1/4`;
* **low temperature** — the Peierls argument (6.9) gives `|𝒢(γ_β)| ≥ 2` for `β ≥ 8 log 2`.

It also closes the `r(β) → 0` gap in `GibbsMeasure/Model/PhaseTransition.lean` and proves
Georgii's `μ₊(σ_Λ ≠ ω⁺_Λ) ≤ |Λ| r(β)` together with the resulting local convergence
`μ₊ → δ_{ω⁺}` as `β → ∞`.
-/

@[expose] public section


open Filter MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

open MeasureTheory.GibbsMeasure.Peierls (Site r)

/-! ### M1: high temperature — uniqueness from Dobrushin's condition -/

/-- **Georgii (8.7)+(8.8) for the `ℤ^d` Ising model.** If `4d|βJ| < 2`, then the Ising
specification on `ℤ^d` has at most one Gibbs measure.

Quasilocality of the Ising specification — the first conjunct of Georgii's Definition (8.6),
without which Theorem (8.7) is false (Example (2.27)) — is part of
`Dobrushin.isDobrushin_isingSpecification`, which obtains it from
`Potential.isQuasilocal_gibbsSpecificationOfAbsolutelySummable`, the Ising potential being
absolutely summable on a locally finite graph. -/
theorem subsingleton_GP_isingSpecification_of_lt (d : ℕ) (J h β : ℝ) (hβ : 4 * d * |β * J| < 2) :
    (GP (S := Fin d → ℤ) (E := Bool) (isingSpecification (latticeGraph d) J h β)).Subsingleton :=
  Dobrushin.subsingleton_GP_of_isDobrushin
    (Dobrushin.isDobrushin_isingSpecification d J h β hβ).1
    (Dobrushin.isDobrushin_isingSpecification d J h β hβ)

/-- **Georgii (8.7)+(8.8) for the `ℤ^d` Ising model**, existence and uniqueness combined:
if `4d|βJ| < 2` there is exactly one Ising Gibbs measure. Existence is Georgii (4.23)(a)
(`isingGibbsMeasure_nonempty`). -/
theorem existsUnique_mem_GP_isingSpecification_of_lt (d : ℕ) (J h β : ℝ)
    (hβ : 4 * d * |β * J| < 2) :
    ∃! μ : ProbabilityMeasure ((Fin d → ℤ) → Bool),
      μ ∈ GP (S := Fin d → ℤ) (E := Bool) (isingSpecification (latticeGraph d) J h β) :=
  Dobrushin.existsUnique_mem_GP_of_isDobrushin
    (Dobrushin.isDobrushin_isingSpecification d J h β hβ).1
    (Dobrushin.isDobrushin_isingSpecification d J h β hβ)
    (isingGibbsMeasure_nonempty (latticeGraph d) J h β)

/-- The `d = 2`, `J = 1`, `h = 0` instance of Dobrushin's criterion: `4 · 2 · |β| < 2`. -/
lemma dobrushin_hyp_ising2D {β : ℝ} (hβ : |β| < 1 / 4) :
    4 * ((2 : ℕ) : ℝ) * |β * 1| < 2 := by
  rw [mul_one]
  push_cast
  linarith

/-- **Georgii's high-temperature uniqueness for the two-dimensional Ising ferromagnet.**
For `|β| < 1/4` there is exactly one Gibbs measure. -/
theorem existsUnique_mem_GP_ising2D_of_abs_lt {β : ℝ} (hβ : |β| < 1 / 4) :
    ∃! μ : ProbabilityMeasure (Site → Bool),
      μ ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 β) :=
  existsUnique_mem_GP_isingSpecification_of_lt 2 1 0 β (dobrushin_hyp_ising2D hβ)

/-- **Georgii's high-temperature uniqueness for the two-dimensional Ising ferromagnet**,
subsingleton form. -/
theorem subsingleton_GP_ising2D_of_abs_lt {β : ℝ} (hβ : |β| < 1 / 4) :
    (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β)).Subsingleton :=
  subsingleton_GP_isingSpecification_of_lt 2 1 0 β (dobrushin_hyp_ising2D hβ)

/-! ### M2: low temperature — non-uniqueness from the Peierls argument -/

/-- **Georgii Theorem (6.9), restated in the `isingSpecification` parametrisation.**
For `β ≥ 8 log 2` the two-dimensional Ising ferromagnet has at least two Gibbs measures. -/
theorem nontrivial_GP_ising2D_of_le {β : ℝ} (hβ : 8 * Real.log 2 ≤ β) :
    (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial := by
  obtain ⟨mp, mm, hne, hp, hm, -, -, -, -, -, -⟩ :=
    Peierls.exists_two_shiftInvariant_gibbs β hβ
  exact ⟨mp, hp, mm, hm, hne⟩

/-! ### M3: the two-sided theorem -/

/-- **Georgii's `0 < β_c < ∞` for the two-dimensional Ising ferromagnet** (`J = 1`, `h = 0`),
in the honest two-sided form.

* At high temperature (`0 ≤ β < 1/4`) the Gibbs measure is unique — Dobrushin's condition of
  weak dependence (8.8) together with Dobrushin's uniqueness theorem (8.7), plus existence
  (4.23)(a).
* At low temperature (`β ≥ 8 log 2`) there are at least two — the Peierls argument (6.9).

Since `1/4 < 8 log 2`, the two ranges are disjoint and the statement is not vacuous: the model
has a genuine phase transition somewhere in `[1/4, 8 log 2]`.

**Caveat.** This does *not* assert the existence of a sharp critical inverse temperature `β_c`
with uniqueness below and non-uniqueness above. That requires monotonicity of the phase diagram
in `β` (Griffiths'/GKS correlation inequalities, or the FKG-based monotonicity of the `+`-phase
magnetisation), which is **not** formalized in this development. What is proved here is exactly
Georgii's assertion that the transition point is strictly between `0` and `∞`. -/
theorem ising_two_dimensional_phase_transition :
    (∀ β : ℝ, 0 ≤ β → β < 1 / 4 →
        ∃! μ : ProbabilityMeasure (Site → Bool),
          μ ∈ GP (S := Fin 2 → ℤ) (E := Bool)
            (isingSpecification (latticeGraph 2) 1 0 β)) ∧
    (∀ β : ℝ, 8 * Real.log 2 ≤ β →
        (GP (S := Fin 2 → ℤ) (E := Bool)
          (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial) := by
  refine ⟨fun β hβ0 hβ ↦ existsUnique_mem_GP_ising2D_of_abs_lt ?_,
    fun β hβ ↦ nontrivial_GP_ising2D_of_le hβ⟩
  rwa [abs_of_nonneg hβ0]

/-- The two temperature ranges of `ising_two_dimensional_phase_transition` are disjoint:
`1/4 < 8 log 2`. -/
theorem quarter_lt_eight_log_two : (1 : ℝ) / 4 < 8 * Real.log 2 := by
  have h : (1 : ℝ) - (2 : ℝ)⁻¹ ≤ Real.log 2 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at h
  linarith

/-! ### M4: `r(β) → 0` as `β → ∞` -/

/-- The Peierls series is `≤ 2 · 8192 · e^{-2β}` for `β ≥ 8 log 2`. -/
lemma r_le_of_eight_log_two_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) :
    r b ≤ 2 * ((8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b))) := by
  have hx := Peierls.ofReal_exp_le hb
  have h8 : (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 8⁻¹ := by
    calc (8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b)) ≤ 8192 * 65536⁻¹ := by gcongr
      _ = 8⁻¹ := by
          rw [show (65536 : ℝ≥0∞) = 8192 * 8 by norm_num,
            ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact Peierls.r_le_of_ofReal_exp_le
    (le_trans h8 (ENNReal.inv_le_inv.2 (by norm_num)))

/-- **The `r(β) → 0` claim of the `M5` section header of `Model/PhaseTransition.lean`.**
Georgii's Peierls series `r(β) = ∑_{ℓ ≥ 1} ℓ 4096^ℓ e^{-2βℓ}` tends to `0` as `β → ∞`.

Consequently every threshold `r(β) ≤ c` with `c > 0` — in particular `r_le_quarter`'s `1/4` —
holds for all large `β`, and the `+`-phase gives full mass to the all-`+1` configuration in the
limit (see `tendsto_localConvergence_diracPlus`). -/
theorem tendsto_r_atTop : Tendsto r atTop (𝓝 0) := by
  have hexp : Tendsto (fun b : ℝ ↦ Real.exp (-2 * b)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0) tendsto_id)
  have hE : Tendsto (fun b : ℝ ↦ ENNReal.ofReal (Real.exp (-2 * b))) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hexp
    rwa [ENNReal.ofReal_zero] at h
  have hM : Tendsto (fun b : ℝ ↦ 2 * ((8192 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-2 * b))))
      atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := (8192 : ℝ≥0∞)) hE (Or.inr (by finiteness))
    rw [mul_zero] at h1
    have h2 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) h1 (Or.inr (by finiteness))
    rwa [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hM
    (Filter.Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb
  exact r_le_of_eight_log_two_le hb

/-! ### M5: Georgii's `μ₊(σ_Λ ≠ ω⁺_Λ) ≤ |Λ| r(β)` and the limit `μ₊ → δ_{ω⁺}` -/

/-- **Georgii (6.9), the quantitative closeness estimate.** Subadditivity over `Λ` of the
per-site Peierls bound: if `μ(σ_a = -1) ≤ r(β)` for every site `a`, then
`μ(σ_Λ ≠ ω⁺_Λ) ≤ |Λ| r(β)` for every finite `Λ`. -/
theorem measure_exists_eq_false_le (b : ℝ) (m : Measure (Site → Bool))
    (hm : ∀ a : Site, m {z : Site → Bool | z a = false} ≤ r b) (Λ : Finset Site) :
    m {z : Site → Bool | ∃ a ∈ Λ, z a = false} ≤ (Λ.card : ℝ≥0∞) * r b := by
  have hset : {z : Site → Bool | ∃ a ∈ Λ, z a = false}
      = ⋃ a ∈ Λ, {z : Site → Bool | z a = false} := by
    ext z; simp
  rw [hset]
  calc m (⋃ a ∈ Λ, {z : Site → Bool | z a = false})
      ≤ ∑ a ∈ Λ, m {z : Site → Bool | z a = false} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ Λ, r b := Finset.sum_le_sum fun a _ ↦ hm a
    _ = (Λ.card : ℝ≥0∞) * r b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Georgii (6.9), first half.** The `+`-phase `μ₊` of the two-dimensional Ising ferromagnet
satisfies `μ₊(σ_Λ ≠ ω⁺_Λ) ≤ |Λ| r(β)` for every finite volume `Λ`. -/
theorem exists_plus_phase_card_bound (b : ℝ) :
    ∃ m : ProbabilityMeasure (Site → Bool),
      m ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (m : Measure (Site → Bool)) m) ∧
      (∀ a : Site, (m : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ r b) ∧
      ∀ Λ : Finset Site,
        (m : Measure (Site → Bool)) {z : Site → Bool | ∃ a ∈ Λ, z a = false}
          ≤ (Λ.card : ℝ≥0∞) * r b := by
  obtain ⟨m, hGP, hshift, hbound⟩ := Peierls.exists_plus_phase b
  exact ⟨m, hGP, hshift, hbound, fun Λ ↦ measure_exists_eq_false_le b _ hbound Λ⟩

/-- The all-`+1` configuration `ω⁺` of `ℤ²`. -/
def plusConfig : Site → Bool := fun _ ↦ true

/-- The Dirac measure at `ω⁺`, as a probability measure. -/
def diracPlus : ProbabilityMeasure (Site → Bool) := ⟨Measure.dirac plusConfig, inferInstance⟩

lemma restrict_eq_restrict_plusConfig {Λ : Finset Site} {z : Site → Bool}
    (h : ∀ a ∈ Λ, z a = true) : Λ.restrict z = Λ.restrict plusConfig := by
  funext a
  have ha := h a.1 a.2
  simpa [plusConfig] using ha

/-- **Georgii (6.9), the `β → ∞` limit of the `+`-phase.** If `m β` is, for each `β`, a
probability measure satisfying the per-site Peierls bound `m β (σ_a = -1) ≤ r(β)` — for instance
the `+`-phase of `exists_plus_phase` — then `m β → δ_{ω⁺}` in the topology of local convergence
(Georgii (4.2)) as `β → ∞`. -/
theorem tendsto_localConvergence_diracPlus (m : ℝ → ProbabilityMeasure (Site → Bool))
    (hm : ∀ (b : ℝ) (a : Site),
      (m b : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ r b) :
    Tendsto
      (fun b : ℝ ↦ (WithSetwiseTopology.ofMeasure (m b) : WithLocalConvergence Site Bool))
      atTop (𝓝 (WithSetwiseTopology.ofMeasure diracPlus)) := by
  rw [tendsto_withLocalConvergence_iff]
  intro A hA
  obtain ⟨Λ, B, hB, rfl⟩ := mem_localEvents_iff_exists_finsetRestrict_preimage.1 hA
  have hAmeas : MeasurableSet (Λ.restrict ⁻¹' B : Set (Site → Bool)) := Λ.measurable_restrict hB
  have hcard : Tendsto (fun b : ℝ ↦ (Λ.card : ℝ≥0∞) * r b) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (Λ.card : ℝ≥0∞)) tendsto_r_atTop
      (Or.inr (ENNReal.natCast_ne_top _))
    rwa [mul_zero] at h
  have hagree : ∀ z : Site → Bool, z ∉ {w : Site → Bool | ∃ a ∈ Λ, w a = false} →
      Λ.restrict z = Λ.restrict plusConfig := by
    intro z hz
    simp only [Set.mem_ofPred_eq, not_exists, not_and] at hz
    refine restrict_eq_restrict_plusConfig fun a ha ↦ ?_
    rcases Bool.eq_false_or_eq_true (z a) with h | h
    · exact h
    · exact absurd h (hz a ha)
  change Tendsto (fun b : ℝ ↦ (m b : Measure (Site → Bool)) (Λ.restrict ⁻¹' B)) atTop
    (𝓝 ((Measure.dirac plusConfig : Measure (Site → Bool)) (Λ.restrict ⁻¹' B)))
  rw [Measure.dirac_apply' _ hAmeas]
  by_cases hplus : plusConfig ∈ (Λ.restrict ⁻¹' B : Set (Site → Bool))
  · rw [Set.indicator_of_mem hplus, Pi.one_apply]
    refine (ENNReal.tendsto_const_sub_nhds_zero_iff (a := 1) (by simp)
      (fun b ↦ prob_le_one)).1 ?_
    have hsubc : (Λ.restrict ⁻¹' B : Set (Site → Bool))ᶜ
        ⊆ {z : Site → Bool | ∃ a ∈ Λ, z a = false} := by
      intro z hz
      by_contra hcon
      refine hz ?_
      change Λ.restrict z ∈ B
      rw [hagree z hcon]
      exact hplus
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcard
      (Filter.Eventually.of_forall fun _ ↦ bot_le)
      (Filter.Eventually.of_forall fun b ↦ ?_)
    rw [← prob_compl_eq_one_sub hAmeas]
    exact le_trans (measure_mono hsubc) (measure_exists_eq_false_le b _ (hm b) Λ)
  · rw [Set.indicator_of_notMem hplus]
    have hsub : (Λ.restrict ⁻¹' B : Set (Site → Bool))
        ⊆ {z : Site → Bool | ∃ a ∈ Λ, z a = false} := by
      intro z hz
      by_contra hcon
      refine hplus ?_
      change Λ.restrict plusConfig ∈ B
      rw [← hagree z hcon]
      exact hz
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcard
      (Filter.Eventually.of_forall fun _ ↦ bot_le)
      (Filter.Eventually.of_forall fun b ↦ ?_)
    exact le_trans (measure_mono hsub) (measure_exists_eq_false_le b _ (hm b) Λ)

/-- **Georgii (6.9), the `+`-phase at low temperature converges to `δ_{ω⁺}`.** Choosing, for each
`β`, a `+`-phase `μ₊(β)` as in `exists_plus_phase`, the family satisfies Georgii's estimate
`μ₊(β)(σ_Λ ≠ ω⁺_Λ) ≤ |Λ| r(β)` and converges to the all-`+1` Dirac measure in the topology of
local convergence as `β → ∞`. -/
theorem exists_plusPhase_family_tendsto_diracPlus :
    ∃ m : ℝ → ProbabilityMeasure (Site → Bool),
      (∀ b : ℝ, m b ∈ GP (S := Fin 2 → ℤ) (E := Bool)
        (isingSpecification (latticeGraph 2) 1 0 b)) ∧
      (∀ (b : ℝ) (Λ : Finset Site),
        (m b : Measure (Site → Bool)) {z : Site → Bool | ∃ a ∈ Λ, z a = false}
          ≤ (Λ.card : ℝ≥0∞) * r b) ∧
      Tendsto
        (fun b : ℝ ↦ (WithSetwiseTopology.ofMeasure (m b) : WithLocalConvergence Site Bool))
        atTop (𝓝 (WithSetwiseTopology.ofMeasure diracPlus)) := by
  choose m hGP _hshift hbound using Peierls.exists_plus_phase
  exact ⟨m, hGP, fun b Λ ↦ measure_exists_eq_false_le b _ (hbound b) Λ,
    tendsto_localConvergence_diracPlus m hbound⟩

end MeasureTheory.GibbsMeasure

end

end

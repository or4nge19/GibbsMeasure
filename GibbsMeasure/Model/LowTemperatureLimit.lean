/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.CriticalTemperature
public import GibbsMeasure.Model.PlusPhase
public import GibbsMeasure.Topology.LocalMetric

/-!
# Georgii Theorem (6.9), first half: the low-temperature limit

Georgii Remark (4.3)(3) gives a metric for the topology of local convergence when the state
space is finite; with it, the Peierls bound of `GibbsMeasure/Model/PhaseTransition.lean` yields
the first assertion of Theorem (6.9): the set of shift-invariant Gibbs measures of the
two-dimensional Ising ferromagnet approaches each of the two ground states as the temperature
tends to zero,
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ_±) = 0`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology Set
open scoped ENNReal Topology

noncomputable section



namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M2. Georgii (6.9): `r(β) → 0` as `β → ∞`

`tendsto_r_atTop` is `MeasureTheory.GibbsMeasure.tendsto_r_atTop` (`Model/CriticalTemperature.lean`);
only its real-valued form is added here. -/

/-- **Georgii (6.9).** The real-valued Peierls bound tends to `0`. -/
theorem tendsto_toReal_r_atTop : Tendsto (fun b : ℝ ↦ (r b).toReal) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp tendsto_r_atTop

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M6. Georgii's phases `μ_+^β` and `μ_-^β = τ(μ_+^β)` -/

lemma r_ne_top {b : ℝ} (hb : 8 * Real.log 2 ≤ b) : r b ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (r_le_quarter hb)

/-- **Georgii (6.9)**, `μ_+^β`: the shift-invariant Gibbs measure obtained as a cluster point of
the cube averages with the `+1` boundary condition.

It is defined as a cluster point of `plusCubeAverage`, not as an unanchored choice out of
`exists_plus_phase`, so that it can be *identified*: for `0 ≤ β` it is the monotone
boundary-condition limit `plusState` (`plusPhase_eq_plusState`), the object the FKG development
and the Lebowitz–Martin-Löf theorem use.  There is one plus phase, under two names. -/
def plusPhase (b : ℝ) : ProbabilityMeasure (Site → Bool) :=
  (exists_mapClusterPt_plusCubeAverage b).choose

/-- `μ_+^β` is a cluster point of Georgii's cube averages, by construction. -/
lemma mapClusterPt_plusPhase (b : ℝ) :
    MapClusterPt (WithSetwiseTopology.ofMeasure (plusPhase b) : WithLocalConvergence Site Bool)
      atTop fun N ↦ WithSetwiseTopology.ofMeasure (plusCubeAverage b N) :=
  (exists_mapClusterPt_plusCubeAverage b).choose_spec

lemma plusPhase_mem_GP (b : ℝ) :
    plusPhase b ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) :=
  mem_GP_of_mapClusterPt_plusCubeAverage (mapClusterPt_plusPhase b)

lemma plusPhase_measurePreserving_shift (b : ℝ) (j : Site) :
    MeasurePreserving (shift Bool j).toFun (plusPhase b : Measure (Site → Bool))
      (plusPhase b : Measure (Site → Bool)) :=
  measurePreserving_shift_of_mapClusterPt_plusCubeAverage (mapClusterPt_plusPhase b) j

lemma plusPhase_eq_false_le (b : ℝ) (a : Site) :
    (plusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = false} ≤ r b :=
  eq_false_le_of_mapClusterPt_plusCubeAverage_of_cube (mapClusterPt_plusPhase b)
    (fun N a ↦ isingSpecification_cube_eq_false_le b N a) a

/-- **The library has one plus phase.**  Georgii's `μ_+^β` of (6.9), a cluster point of the
cube-averaged `+`-boundary distributions, *is* the monotone boundary-condition limit `plusState`
of the FKG development, for every `0 ≤ β`.  Everything proved about either object therefore holds
of the other: `plusState` is shift-invariant with `μ(σ_a = -1) ≤ r(β)`, and `μ_+^β` is
`≽`-maximal in `𝒢(β)`. -/
theorem plusPhase_eq_plusState {b : ℝ} (hb : 0 ≤ b) :
    plusPhase b = plusState (latticeGraph 2) 1 0 b :=
  eq_plusState_of_mapClusterPt_plusCubeAverage hb (mapClusterPt_plusPhase b)

/-- **Georgii (6.9)**: `μ_+^β(σ_a ≠ +1) ≤ r(β)`. -/
lemma plusPhase_real_ne_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (a : Site) :
    (plusPhase b : Measure (Site → Bool)).real
        {z : Site → Bool | z a ≠ (fun _ : Site ↦ true) a} ≤ (r b).toReal := by
  have hset : {z : Site → Bool | z a ≠ (fun _ : Site ↦ true) a}
      = {z : Site → Bool | z a = false} := by
    ext z; simp
  rw [hset, measureReal_def]
  exact ENNReal.toReal_mono (r_ne_top hb) (plusPhase_eq_false_le b a)

/-- **Georgii (6.9)**, `μ_-^β = τ(μ_+^β)`: the spin-flip image of the plus phase. -/
def minusPhase (b : ℝ) : ProbabilityMeasure (Site → Bool) :=
  (plusPhase b).map spinFlip.measurable_toFun.aemeasurable

lemma minusPhase_toMeasure (b : ℝ) :
    (minusPhase b : Measure (Site → Bool))
      = Measure.map spinFlip.toFun (plusPhase b : Measure (Site → Bool)) :=
  ProbabilityMeasure.toMeasure_map _ _

lemma minusPhase_mem_GP (b : ℝ) :
    minusPhase b ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) :=
  (isInvariant_spinFlip b).map_mem_GP (plusPhase_mem_GP b)

lemma minusPhase_measurePreserving_shift (b : ℝ) (j : Site) :
    MeasurePreserving (shift Bool j).toFun (minusPhase b : Measure (Site → Bool))
      (minusPhase b : Measure (Site → Bool)) := by
  refine ⟨(shift Bool j).measurable_toFun, ?_⟩
  rw [minusPhase_toMeasure,
    Measure.map_map (shift Bool j).measurable_toFun spinFlip.measurable_toFun,
    show (shift Bool j).toFun ∘ spinFlip.toFun = spinFlip.toFun ∘ (shift Bool j).toFun from
      funext fun z ↦ funext fun i ↦ by simp,
    ← Measure.map_map spinFlip.measurable_toFun (shift Bool j).measurable_toFun,
    (plusPhase_measurePreserving_shift b j).map_eq]

/-- **Georgii (6.9)**: `μ_-^β(σ_a ≠ -1) ≤ r(β)`. -/
lemma minusPhase_real_ne_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) (a : Site) :
    (minusPhase b : Measure (Site → Bool)).real
        {z : Site → Bool | z a ≠ (fun _ : Site ↦ false) a} ≤ (r b).toReal := by
  have hset : {z : Site → Bool | z a ≠ (fun _ : Site ↦ false) a}
      = {z : Site → Bool | z a = true} := by
    ext z; simp
  have hmeas : MeasurableSet {z : Site → Bool | z a = true} := by
    have h : {z : Site → Bool | z a = true} = (fun z : Site → Bool ↦ z a) ⁻¹' {true} := rfl
    rw [h]
    exact (measurable_pi_apply a) (measurableSet_singleton true)
  have hval : (minusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = true}
      = (plusPhase b : Measure (Site → Bool)) {z : Site → Bool | z a = false} := by
    rw [minusPhase_toMeasure, Measure.map_apply spinFlip.measurable_toFun hmeas]
    congr 1
    ext z
    simp
  rw [hset, measureReal_def, hval]
  exact ENNReal.toReal_mono (r_ne_top hb) (plusPhase_eq_false_le b a)

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ### Georgii (6.9), the estimate for the plus phase, in the book's form -/

/-- **Georgii (6.9)**: `μ_+^β(σ_Λ ≠ ω⁺_Λ) ≤ ∑_{a ∈ Λ} μ_+^β(σ_a = -1) ≤ |Λ| r(β)`. -/
theorem plusPhase_exists_eq_false_le (b : ℝ) (Λ : Finset Site) :
    (plusPhase b : Measure (Site → Bool)) {ζ : Site → Bool | ∃ a ∈ Λ, ζ a = false}
      ≤ Λ.card * r b := by
  have hEq : {ζ : Site → Bool | ∃ a ∈ Λ, ζ a = false}
      = {ζ : Site → Bool | ∃ a ∈ Λ, ζ a ≠ (fun _ : Site ↦ true) a} := by
    ext ζ; simp
  rw [hEq]
  refine measure_exists_ne_le Λ fun a _ ↦ ?_
  have hset : {ζ : Site → Bool | ζ a ≠ (fun _ : Site ↦ true) a}
      = {ζ : Site → Bool | ζ a = false} := by
    ext ζ; simp
  rw [hset]
  exact plusPhase_eq_false_le b a

/-- **Georgii (6.9)**, the event form: for `A ∈ 𝓕_Λ`,
`|μ_+^β(A) − δ_+(A)| ≤ |Λ| r(β)`. -/
theorem abs_plusPhase_sub_dirac_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {A : Set (Site → Bool)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] A) :
    |(plusPhase b : Measure (Site → Bool)).real A
        - (Measure.dirac (fun _ : Site ↦ true)).real A| ≤ Λ.card * (r b).toReal :=
  abs_measureReal_sub_dirac_le_of_cylinderEvents hA fun a _ ↦ plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**, the estimate exactly as displayed in the book: for `f ∈ 𝓛_Λ` with
`‖f‖ ≤ M`,
`|μ_+^β(f) − δ_+(f)| ≤ 2‖f‖ μ_+^β(σ_Λ ≠ ω⁺_Λ) ≤ 2‖f‖ |Λ| r(β)`. -/
theorem abs_integral_plusPhase_sub_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {f : (Site → Bool) → ℝ} {M : ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] f)
    (hM : ∀ ζ, |f ζ| ≤ M) :
    |(∫ ζ, f ζ ∂(plusPhase b : Measure (Site → Bool))) - f (fun _ ↦ true)|
      ≤ 2 * M * (Λ.card * (r b).toReal) :=
  abs_integral_sub_apply_le hf hM fun a _ ↦ plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**, the same estimate for the minus phase. -/
theorem abs_integral_minusPhase_sub_le {b : ℝ} (hb : 8 * Real.log 2 ≤ b) {Λ : Finset Site}
    {f : (Site → Bool) → ℝ} {M : ℝ}
    (hf : Measurable[cylinderEvents (X := fun _ : Site ↦ Bool) (Λ : Set Site)] f)
    (hM : ∀ ζ, |f ζ| ≤ M) :
    |(∫ ζ, f ζ ∂(minusPhase b : Measure (Site → Bool))) - f (fun _ ↦ false)|
      ≤ 2 * M * (Λ.card * (r b).toReal) :=
  abs_integral_sub_apply_le hf hM fun a _ ↦ minusPhase_real_ne_le hb a

end MeasureTheory.GibbsMeasure.Peierls

namespace MeasureTheory.GibbsMeasure.Peierls

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

/-! ## M4. Georgii Theorem (6.9), first half:
`lim_{β→∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β→∞} d(𝒢_Θ(βΦ), δ₋) = 0` -/

/-- **Georgii (5.13)/(6.9)**: `𝒢_Θ(βΦ)`, the set of shift-invariant Gibbs measures of the
two-dimensional Ising ferromagnet with coupling constant `1` and vanishing external field at
inverse temperature `β`. -/
def shiftInvariantGibbs (b : ℝ) : Set (ProbabilityMeasure (Site → Bool)) :=
  {μ | μ ∈ GP (isingSpecification (latticeGraph 2) 1 0 b) ∧
    ∀ j : Site, MeasurePreserving (shift Bool j).toFun (μ : Measure (Site → Bool))
      (μ : Measure (Site → Bool))}

lemma plusPhase_mem_shiftInvariantGibbs (b : ℝ) : plusPhase b ∈ shiftInvariantGibbs b :=
  ⟨plusPhase_mem_GP b, plusPhase_measurePreserving_shift b⟩

lemma minusPhase_mem_shiftInvariantGibbs (b : ℝ) : minusPhase b ∈ shiftInvariantGibbs b :=
  ⟨minusPhase_mem_GP b, minusPhase_measurePreserving_shift b⟩

/-- **Georgii (6.9)**: `μ_+^β → δ_+` in the topology of local convergence as `β → ∞`. -/
theorem tendsto_localDist_plusPhase :
    Tendsto (fun b : ℝ ↦ localDist (plusPhase b) (diracProb (fun _ : Site ↦ true)))
      atTop (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
  exact plusPhase_real_ne_le hb a

/-- **Georgii (6.9)**: `μ_-^β → δ_-` in the topology of local convergence as `β → ∞`. -/
theorem tendsto_localDist_minusPhase :
    Tendsto (fun b : ℝ ↦ localDist (minusPhase b) (diracProb (fun _ : Site ↦ false)))
      atTop (𝓝 0) := by
  refine tendsto_localDist_diracProb (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
  filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
  exact minusPhase_real_ne_le hb a

/-- **Georgii Theorem (6.9), first half.** In the ferromagnetic Ising model on `ℤ²` with coupling
constant `1` and vanishing external field,
`lim_{β → ∞} d(𝒢_Θ(βΦ), δ₊) = lim_{β → ∞} d(𝒢_Θ(βΦ), δ₋) = 0`,
where `d` is any metric for the `𝓛`-topology (here `localDist`, one of the metrics whose
existence is Remark (4.3)(3)), `𝒢_Θ(βΦ)` is the set of shift-invariant Gibbs measures, and
`δ_±` are the Dirac
measures at the two ground states `ω^±`. -/
theorem tendsto_localDistSet_shiftInvariantGibbs_dirac :
    Tendsto (fun b : ℝ ↦ localDistSet (shiftInvariantGibbs b)
        (diracProb (fun _ : Site ↦ true))) atTop (𝓝 0) ∧
      Tendsto (fun b : ℝ ↦ localDistSet (shiftInvariantGibbs b)
        (diracProb (fun _ : Site ↦ false))) atTop (𝓝 0) := by
  constructor
  · refine tendsto_localDistSet_diracProb (μs := plusPhase) plusPhase_mem_shiftInvariantGibbs
      (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
    exact plusPhase_real_ne_le hb a
  · refine tendsto_localDistSet_diracProb (μs := minusPhase) minusPhase_mem_shiftInvariantGibbs
      (c := fun b ↦ (r b).toReal) tendsto_toReal_r_atTop ?_
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with b hb a
    exact minusPhase_real_ne_le hb a

end MeasureTheory.GibbsMeasure.Peierls

end

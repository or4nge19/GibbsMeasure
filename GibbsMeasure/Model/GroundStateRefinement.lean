/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.DiscreteSymmetryBreaking

/-!
# Georgii, Corollary (19.7): splitting a phase along a symmetry-related refinement

Georgii, *Gibbs Measures and Phase Transitions*, Corollary (19.7).  Suppose a Gibbs measure `μ`
lives on the event that a pattern set `G = G_1 ∪ ⋯ ∪ G_k` percolates,
`μ(ξ⁰_P(G, ·) ≠ ∅) = 1`, and that the members `G_1, …, G_k` of a *stable* refinement of `G`
(condition (18.23)(a)(ii) only — Georgii's "the adjective stable will refer to property
(18.23)(a)(ii)") are carried into each other by symmetries which preserve `μ`.  Then `μ` splits
into `k` mutually singular Gibbs measures `μ_ℓ = μ(· | ξ⁰_P(G_ℓ, ·) ≠ ∅)`, one for each member,
each of them again with full mass on its own percolation event and with *the same* probability
of containing the origin in its ocean as `μ` had for `G`.

Georgii's proof, verbatim: the events `A_ℓ = {ξ⁰_P(G_ℓ, ·) ≠ ∅}` are pairwise disjoint and cover
`A = {ξ⁰_P(G, ·) ≠ ∅}` — the analogue of (18.24) — and the symmetries permute them, so
`μ(A_ℓ) = 1/k`; the `A_ℓ` are tail events, so conditioning on them stays inside `𝒢(Φ)` by
Theorem (7.7)(b).

## Main results

* `measurableSet_setOf_mem_latticeOceanPart` — the event `{i ∈ ξ⁰_P(G, ·)}` is measurable; the
  ocean part is either empty or the union of the infinite clusters, so this is the intersection
  of two events already known to be measurable.  Its home is
  `GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/Measurable.lean`, next to
  `SimpleGraph.measurableSet_setOf_oceanPart_nonempty`.
* `measure_setOf_latticeOceanPart_nonempty_eq_of_map`,
  `measure_setOf_zero_mem_latticeOceanPart_eq_of_map` — a `μ`-preserving cube transformation
  carrying `G` to `G'` equates the two percolation events, resp. the two events that the origin
  lies in the ocean.  These are `measure_setOf_latticeOceanPart_nonempty_eq` and
  `measure_setOf_zero_mem_latticeOceanPart_eq` of
  `GibbsMeasure/Model/DiscreteSymmetryBreaking.lean` with the hypothesis `μ ∈ 𝒢₀(Φ)` — which
  enters there only through Remark (18.22) — replaced by the invariance itself.
* `measure_setOf_latticeOceanPart_nonempty_eq_inv` — **Georgii's `μ_n(A_{n,ℓ}) = 1/k_n`**.
* `exists_gibbsMeasure_refinement` — **Corollary (19.7)**.

## Relation to Theorem (19.6)

Georgii states (19.7) for the measures `μ_n` produced by Theorem (19.6), which is not available
here (see the module docstring of
`GibbsMeasure/Specification/ResolvingPerturbations.lean`).  The statement below takes the
properties of `μ` that Georgii's proof actually uses as its hypotheses, so it applies verbatim
to the output of (19.6) once that is available — and, unconditionally, to the family produced by
Theorem (18.25), `MeasureTheory.GibbsMeasure.exists_gibbsMeasure_family`.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {E : Type*} [MeasurableSpace E] {φ φ₀ : ((Fin 2 → Fin 2) → E) → ℝ} {ν : Measure E}
  {μ : Measure ((Fin 2 → ℤ) → E)}

/-! ### The event that a site lies in the maximal ocean -/

/-- **The event `{i ∈ ξ⁰_P(G, ·)}` is measurable**, for an arbitrary measurable pattern set `G`.
Georgii's `ξ⁰_P(G, ω)` is the union of the infinite clusters of `V(G, ω)` when that union is an
ocean and `∅` otherwise, so the event is the intersection of the event that the union is an
ocean with the event that `i` lies in it.

This belongs next to `SimpleGraph.measurableSet_setOf_oceanPart_nonempty` in
`GibbsMeasure/Mathlib/Combinatorics/SimpleGraph/Measurable.lean`. -/
theorem measurableSet_setOf_mem_latticeOceanPart {W : Set ((Fin 2 → Fin 2) → E)}
    (hW : MeasurableSet W) (i : Peierls.Site) :
    MeasurableSet {ω : (Fin 2 → ℤ) → E | i ∈ latticeOceanPart E W ω} := by
  classical
  have hS : ∀ v : Fin 2 → ℤ, MeasurableSet {ω : (Fin 2 → ℤ) → E | v ∈ latticePattern E W ω} :=
    fun v ↦ measurableSet_setOf_mem_latticePattern hW v
  have hinf : ∀ v : Fin 2 → ℤ, MeasurableSet {ω : (Fin 2 → ℤ) → E |
      v ∈ (latticeGraph 2).infiniteClusters (latticePattern E W ω)} :=
    fun v ↦ (latticeGraph 2).measurableSet_setOf_mem_infiniteClusters hS v
  have hrw : {ω : (Fin 2 → ℤ) → E | i ∈ latticeOceanPart E W ω}
      = {ω : (Fin 2 → ℤ) → E | SimpleGraph.IsOceanIn (latticeGraph 2) (starLatticeGraph 2)
            Set.univ ((latticeGraph 2).infiniteClusters (latticePattern E W ω))}
        ∩ {ω : (Fin 2 → ℤ) → E |
            i ∈ (latticeGraph 2).infiniteClusters (latticePattern E W ω)} := by
    ext ω
    simp only [latticeOceanPart, SimpleGraph.oceanPart, Set.mem_inter_iff, Set.mem_ofPred_eq]
    split_ifs with h <;> simp [h]
  rw [hrw]
  exact ((latticeGraph 2).measurableSet_setOf_isOceanIn Set.univ hinf).inter (hinf i)

/-! ### Transporting the percolation events by a symmetry -/

/-- **`μ(ξ⁰_P(G, ·) ≠ ∅) = μ(ξ⁰_P(G', ·) ≠ ∅)`** whenever a `μ`-preserving cube transformation
carries `G` to `G'`. -/
theorem measure_setOf_latticeOceanPart_nonempty_eq_of_map {W W' : Set ((Fin 2 → Fin 2) → E)}
    {τ : CubeTransformation E 2} (hτμ : MeasurePreserving (τ.onLattice E).toFun μ μ)
    (hW : τ.onCube.toFun '' W = W') (hW'meas : MeasurableSet W') :
    μ {ω | (latticeOceanPart E W ω).Nonempty} = μ {ω | (latticeOceanPart E W' ω).Nonempty} := by
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' W' = W := by rw [← hW, Set.preimage_image_eq _ hinj]
  have hmp := hτμ.measure_preimage
    (measurableSet_setOf_latticeOceanPart_nonempty hW'meas).nullMeasurableSet
  rw [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre] at hmp
  exact hmp

/-- **`μ(0 ∈ ξ⁰_P(G, ·)) = μ(0 ∈ ξ⁰_P(G', ·))`** whenever a `μ`-preserving cube transformation
carries `G` to `G'`; the spatial part of a cube transformation fixes the origin. -/
theorem measure_setOf_zero_mem_latticeOceanPart_eq_of_map {W W' : Set ((Fin 2 → Fin 2) → E)}
    {τ : CubeTransformation E 2} (hτμ : MeasurePreserving (τ.onLattice E).toFun μ μ)
    (hW : τ.onCube.toFun '' W = W') (hW'meas : MeasurableSet W') :
    μ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E W ω}
      = μ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E W' ω} := by
  have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
  have hpre : τ.onCube.toFun ⁻¹' W' = W := by rw [← hW, Set.preimage_image_eq _ hinj]
  have hmp := hτμ.measure_preimage
    (measurableSet_setOf_mem_latticeOceanPart hW'meas 0).nullMeasurableSet
  rw [preimage_onLattice_setOf_zero_mem_latticeOceanPart, hpre] at hmp
  exact hmp

/-! ### Georgii's `μ_n(A_{n,ℓ}) = 1/k_n` -/

variable {k : ℕ} {G : Fin k → Set ((Fin 2 → Fin 2) → E)}

/-- **Georgii's `μ_n(ξ⁰_P(G_{n,ℓ}, ·) ≠ ∅) = 1/k_n`.**  The `k` percolation events are pairwise
disjoint, they cover the percolation event of the union (the analogue of (18.24)), which carries
all the mass, and the symmetries permute them. -/
theorem measure_setOf_latticeOceanPart_nonempty_eq_inv [NeZero k]
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ ℓ, MeasurableSet (G ℓ))
    (hμ1 : μ {ω | (latticeOceanPart E (⋃ ℓ, G ℓ) ω).Nonempty} = 1)
    (htrans : ∀ ℓ ℓ' : Fin k, ∃ τ : CubeTransformation E 2,
      MeasurePreserving (τ.onLattice E).toFun μ μ ∧ τ.onCube.toFun '' G ℓ = G ℓ')
    (ℓ : Fin k) : μ {ω | (latticeOceanPart E (G ℓ) ω).Nonempty} = (k : ℝ≥0∞)⁻¹ := by
  classical
  set A : Fin k → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (latticeOceanPart E (G m) ω).Nonempty} with hAdef
  have hAmeas : ∀ m, MeasurableSet (A m) :=
    fun m ↦ measurableSet_setOf_latticeOceanPart_nonempty (hGmeas m)
  have heq : ∀ ℓ' : Fin k, μ (A ℓ') = μ (A ℓ) := fun ℓ' ↦ by
    obtain ⟨τ, hτμ, hτG⟩ := htrans ℓ' ℓ
    exact measure_setOf_latticeOceanPart_nonempty_eq_of_map hτμ hτG (hGmeas ℓ)
  have hsum : (k : ℝ≥0∞) * μ (A ℓ) = 1 := by
    have hUn : (⋃ m : Fin k, A m) = ⋃ m ∈ (Finset.univ : Finset (Fin k)), A m := by simp
    have h1 : μ (⋃ m : Fin k, A m) = ∑ m : Fin k, μ (A m) := by
      rw [hUn]
      exact measure_biUnion_finset
        (fun m _ p _ hmp ↦ hpart.disjoint_setOf_latticeOceanPart_nonempty hmp)
        fun m _ ↦ hAmeas m
    rw [Finset.sum_congr rfl fun m _ ↦ heq m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    rw [← h1, ← hpart.setOf_latticeOceanPart_iUnion_nonempty_eq, hμ1]
  have hk0 : (k : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne k)
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  calc μ (A ℓ) = (k : ℝ≥0∞)⁻¹ * ((k : ℝ≥0∞) * μ (A ℓ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
    _ = (k : ℝ≥0∞)⁻¹ := by rw [hsum, mul_one]

/-! ### Georgii, Corollary (19.7) -/

/-- **Georgii, Corollary (19.7).**  Let `Φ` be a `C`-potential, `{G_1, …, G_k}` a family of
measurable pattern sets satisfying the stability condition (18.23)(a)(ii), and `μ` a Gibbs
measure for `Φ` which

* gives full mass to the event that `G = G_1 ∪ ⋯ ∪ G_k` percolates, and
* is invariant under cube transformations carrying each `G_ℓ` onto each `G_{ℓ'}`.

Then the conditional measures `μ_ℓ = μ(· | ξ⁰_P(G_ℓ, ·) ≠ ∅)` are `k` pairwise mutually singular
Gibbs measures for `Φ`, each of `μ`-mass `1/k`, with

* `μ_ℓ(ξ⁰_P(G_ℓ, ·) ≠ ∅) = 1` and `μ_ℓ(0 ∈ ξ⁰_P(G_ℓ, ·)) = μ(0 ∈ ξ⁰_P(G, ·))`;
* `θ_a(μ_ℓ) = μ_ℓ` for every `μ`-preserving shift with `r^a G_ℓ = G_ℓ`, and
  `τ(μ_ℓ) = μ_{ℓ'}` for every `μ`-preserving cube transformation with `τ G_ℓ = G_{ℓ'}`.

Georgii's proof: the events `A_ℓ` are pairwise disjoint (two oceans always meet) and cover the
percolation event of `G` by the argument of (18.24), the symmetries permute them, hence
`μ(A_ℓ) = 1/k`; and `A_ℓ` is a tail event, so Theorem (7.7)(b) keeps `μ(· | A_ℓ)` Gibbsian. -/
theorem exists_gibbsMeasure_refinement [NeZero k] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ] (hφ : Measurable φ) (hM : ∃ M : ℝ, ∀ ζ, M ≤ φ ζ)
    (hpart : IsPStablePartition φ₀ ν Set.univ G) (hGmeas : ∀ ℓ, MeasurableSet (G ℓ))
    (hμGibbs : Specification.IsGibbsMeasure (cubeGibbsSpec E φ ν hφ hM) μ)
    (hμ1 : μ {ω | (latticeOceanPart E (⋃ ℓ, G ℓ) ω).Nonempty} = 1)
    (htrans : ∀ ℓ ℓ' : Fin k, ∃ τ : CubeTransformation E 2,
      MeasurePreserving (τ.onLattice E).toFun μ μ ∧ τ.onCube.toFun '' G ℓ = G ℓ') :
    ∃ ρ : Fin k → Measure ((Fin 2 → ℤ) → E),
      (∀ ℓ, IsProbabilityMeasure (ρ ℓ)) ∧
      (∀ ℓ, Specification.IsGibbsMeasure (cubeGibbsSpec E φ ν hφ hM) (ρ ℓ)) ∧
      (Pairwise fun ℓ ℓ' ↦ (ρ ℓ).MutuallySingular (ρ ℓ')) ∧ Function.Injective ρ ∧
      (∀ ℓ, μ {ω | (latticeOceanPart E (G ℓ) ω).Nonempty} = (k : ℝ≥0∞)⁻¹) ∧
      (∀ ℓ, ρ ℓ {ω | (latticeOceanPart E (G ℓ) ω).Nonempty} = 1) ∧
      (∀ ℓ, ρ ℓ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (G ℓ) ω}
        = μ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (⋃ m, G m) ω}) ∧
      (∀ (ℓ : Fin k) (a : Fin 2 → ℤ), MeasurePreserving (shift E a).toFun μ μ →
        tauPow (cubeRefl E) (latticeToTorus 0 a) ⁻¹' G ℓ = G ℓ →
        MeasurePreserving (shift E a).toFun (ρ ℓ) (ρ ℓ)) ∧
      (∀ (ℓ ℓ' : Fin k) (τ : CubeTransformation E 2),
        MeasurePreserving (τ.onLattice E).toFun μ μ → τ.onCube.toFun '' G ℓ = G ℓ' →
        (ρ ℓ).map (τ.onLattice E).toFun = ρ ℓ') := by
  classical
  set A : Fin k → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (latticeOceanPart E (G m) ω).Nonempty} with hAdef
  set B : Fin k → Set ((Fin 2 → ℤ) → E) :=
    fun m ↦ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (G m) ω} with hBdef
  have hAmeas : ∀ m, MeasurableSet (A m) :=
    fun m ↦ measurableSet_setOf_latticeOceanPart_nonempty (hGmeas m)
  have hBmeas : ∀ m, MeasurableSet (B m) :=
    fun m ↦ measurableSet_setOf_mem_latticeOceanPart (hGmeas m) 0
  have hBA : ∀ m, B m ⊆ A m := fun m ω hω ↦ ⟨0, hω⟩
  have hAinv : ∀ m, μ (A m) = (k : ℝ≥0∞)⁻¹ :=
    measure_setOf_latticeOceanPart_nonempty_eq_inv hpart hGmeas hμ1 htrans
  have hktop : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hA0 : ∀ m, μ (A m) ≠ 0 := fun m ↦ by
    rw [hAinv m]; exact ENNReal.inv_ne_zero.2 hktop
  refine ⟨fun m ↦ μ[|A m], fun m ↦ cond_isProbabilityMeasure (hA0 m), fun m ↦ ?_, ?_, ?_,
    hAinv, fun m ↦ cond_apply_self (hA0 m) (measure_ne_top _ _), ?_, ?_, ?_⟩
  · exact isGibbsMeasure_cond_of_tail μ hμGibbs
      (tail_measurableSet_setOf_latticeOceanPart_nonempty (hGmeas m)) (hA0 m)
  · intro m n hmn
    refine ⟨(A m)ᶜ, (hAmeas m).compl, ?_, ?_⟩
    · rw [cond_apply (hAmeas m), Set.inter_compl_self, measure_empty, mul_zero]
    · rw [compl_compl, cond_apply (hAmeas n),
        Set.disjoint_iff_inter_eq_empty.1
          ((hpart.disjoint_setOf_latticeOceanPart_nonempty hmn).symm),
        measure_empty, mul_zero]
  · intro m n hmn
    by_contra hne
    have h1 : (μ[|A m]) (A m) = 1 := cond_apply_self (hA0 m) (measure_ne_top _ _)
    rw [show (μ[|A m]) = μ[|A n] from hmn, cond_apply (hAmeas n),
      Set.disjoint_iff_inter_eq_empty.1
        (hpart.disjoint_setOf_latticeOceanPart_nonempty (Ne.symm hne)),
      measure_empty, mul_zero] at h1
    exact zero_ne_one h1
  · intro m
    have hBeq : ∀ m' : Fin k, μ (B m') = μ (B m) := fun m' ↦ by
      obtain ⟨τ, hτμ, hτG⟩ := htrans m' m
      exact measure_setOf_zero_mem_latticeOceanPart_eq_of_map hτμ hτG (hGmeas m)
    have hBsum : μ {ω | (0 : Peierls.Site) ∈ latticeOceanPart E (⋃ p, G p) ω}
        = (k : ℝ≥0∞) * μ (B m) := by
      rw [hpart.setOf_mem_latticeOceanPart_iUnion_eq 0]
      have hUn : (⋃ p : Fin k, B p) = ⋃ p ∈ (Finset.univ : Finset (Fin k)), B p := by simp
      rw [hUn, measure_biUnion_finset
        (fun p _ q _ hpq ↦ (hpart.disjoint_setOf_latticeOceanPart_nonempty hpq).mono
          (hBA p) (hBA q)) (fun p _ ↦ hBmeas p),
        Finset.sum_congr rfl fun p _ ↦ hBeq p, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [cond_apply (hAmeas m), Set.inter_eq_self_of_subset_right (hBA m), hAinv m, inv_inv,
      hBsum]
  · intro m a hshift hGa
    refine hshift.cond_of_preimage_eq (hAmeas m) ?_
    simp only [hAdef]
    rw [preimage_shift_setOf_latticeOceanPart_nonempty_eq_tauPow, hGa]
  · intro m n τ hτμ hτG
    have hinj : Function.Injective τ.onCube.toFun := τ.onCube.toMeasurableEquiv.injective
    have hpre : τ.onCube.toFun ⁻¹' G n = G m := by rw [← hτG, Set.preimage_image_eq _ hinj]
    refine hτμ.map_cond_of_preimage_eq (hAmeas n) ?_ (by rw [hAinv m, hAinv n])
    simp only [hAdef]
    rw [preimage_onLattice_setOf_latticeOceanPart_nonempty, hpre]

end MeasureTheory.GibbsMeasure

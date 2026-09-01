/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Model.SharpContours
public import GibbsMeasure.Model.CriticalTemperature

/-!
# Georgii Theorem (6.9) at the sharp Peierls threshold

This file re-derives the Peierls estimate and the two-dimensional Ising phase transition with
Georgii's *own* contour count `ℓ · 3 ^ (ℓ - 1)` (`PeierlsSharp.ncard_anchored_circuits_le`)
in place of the crude connected-bond-set count `4096 ^ ℓ` used in
`GibbsMeasure/Model/PhaseTransition.lean`.  The resulting threshold is

`Real.log 9 ≤ 2 * β`, i.e. `β ≥ log 3 ≈ 1.0986`,

instead of `β ≥ 8 log 2 ≈ 5.5452`.
-/

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.GibbsMeasure MeasureTheory.GibbsMeasure.Peierls
open ProbabilityTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure.PeierlsSharp

/-! ### M1: the anchored circuits of a given length, as a finset -/

/-- The circuits of `ℓ` bonds meeting the horizontal half-line to the right of `a` at one of its
first `ℓ` bonds, as a `Finset`.  This is the index set of Georgii's count (6.13). -/
def anchoredCircuitFinset (a : Site) (ℓ : ℕ) : Finset (Finset (Sym2 Site)) :=
  (Finset.range ℓ).biUnion (fun k ↦
    (finite_circuitSets (hBond (a 0 + k) (a 1)) (mk (a 0 + k) (a 1))
      (hBond_mem_plaquette_mk _ _) ℓ).toFinset)

lemma mem_anchoredCircuitFinset {a : Site} {ℓ : ℕ} {C : Finset (Sym2 Site)}
    (hc : IsCircuit C) (hcard : C.card = ℓ) {k : ℕ} (hk : k < ℓ)
    (hmem : s(a + k • e0, a + (k + 1) • e0) ∈ C) : C ∈ anchoredCircuitFinset a ℓ := by
  rw [anchoredCircuitFinset]
  refine Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 hk, ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨hc, by rwa [anchor_bond_eq] at hmem, hcard⟩

lemma card_eq_of_mem_anchoredCircuitFinset {a : Site} {ℓ : ℕ} {C : Finset (Sym2 Site)}
    (hC : C ∈ anchoredCircuitFinset a ℓ) : C.card = ℓ := by
  rw [anchoredCircuitFinset] at hC
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hC
  rw [Set.Finite.mem_toFinset] at hk
  exact hk.2.2

/-- **Georgii Lemma (6.13)**: at most `ℓ · 3 ^ (ℓ - 1)` circuits of length `ℓ` are anchored on
the horizontal half-line from `a`. -/
lemma card_anchoredCircuitFinset_le (a : Site) (ℓ : ℕ) :
    (anchoredCircuitFinset a ℓ).card ≤ ℓ * 3 ^ (ℓ - 1) := by
  rw [anchoredCircuitFinset]
  refine le_trans (Finset.card_biUnion_le_card_mul _ _ (3 ^ (ℓ - 1)) fun k _ ↦ ?_) ?_
  · have hcast : ((finite_circuitSets (hBond (a 0 + k) (a 1)) (mk (a 0 + k) (a 1))
        (hBond_mem_plaquette_mk _ _) ℓ).toFinset).card
      = (circuitSets (hBond (a 0 + k) (a 1)) ℓ).ncard := by
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    rw [hcast]
    exact ncard_circuitSets_le _ _ (hBond_mem_plaquette_mk _ _) ℓ
  · rw [Finset.card_range]

/-! ### M2: sharp contour candidates -/

open Classical in
/-- Sharp contour candidates: anchored circuits of `ℓ` bonds whose interior is closed and
contained in `Λ`.  Compare `Peierls.contourFinset`, which counts arbitrary
plaquette-connected bond sets. -/
def sharpContourFinset (Λ : Finset Site) (a : Site) (ℓ : ℕ) : Finset (Finset (Sym2 Site)) :=
  (anchoredCircuitFinset a ℓ).filter (fun C ↦
    edgeBoundary (interiorOf (↑C : Set (Sym2 Site))) = (↑C : Set (Sym2 Site)) ∧
      interiorOf (↑C : Set (Sym2 Site)) ⊆ (↑Λ : Set Site))

open Classical in
lemma mem_sharpContourFinset {Λ : Finset Site} {a : Site} {ℓ : ℕ} {C : Finset (Sym2 Site)} :
    C ∈ sharpContourFinset Λ a ℓ ↔ C ∈ anchoredCircuitFinset a ℓ ∧
      (edgeBoundary (interiorOf (↑C : Set (Sym2 Site))) = (↑C : Set (Sym2 Site)) ∧
        interiorOf (↑C : Set (Sym2 Site)) ⊆ (↑Λ : Set Site)) := by
  rw [sharpContourFinset, Finset.mem_filter]

/-- **Georgii Lemma (6.13)** for the contour candidates: at most `ℓ · 3 ^ (ℓ - 1)` of them. -/
lemma card_sharpContourFinset_le (Λ : Finset Site) (a : Site) (ℓ : ℕ) :
    (sharpContourFinset Λ a ℓ).card ≤ ℓ * 3 ^ (ℓ - 1) := by
  classical
  exact le_trans (Finset.card_filter_le _ _) (card_anchoredCircuitFinset_le a ℓ)

/-! ### M3: the covering of the event `σ_a = -1` by circuits -/

/-- The union of the circuit-contour events of length `l + 1` anchored at `a`. -/
def sharpContourUnion (N : ℕ) (a : Site) (l : ℕ) : Set (Site → Bool) :=
  ⋃ C ∈ sharpContourFinset (cube 2 N) a (l + 1),
    {ζ : Site → Bool | (↑C : Set (Sym2 Site)) ⊆ discordant ζ}

/-- **Georgii (6.14), sharpened**: if `ζ` is `+1` off the cube and `-1` at `a`, then `a` is
surrounded by a *circuit* of discordant bonds. -/
theorem sharp_minus_event_subset_iUnion (N : ℕ) (a : Site) :
    {ζ : Site → Bool | ζ a = false ∧ ∀ i ∉ cube 2 N, ζ i = true} ⊆
      ⋃ l : ℕ, sharpContourUnion N a l := by
  classical
  rintro ζ ⟨ha, hout⟩
  set D : Set Site := minusCluster a ζ with hDdef
  have haD : a ∈ D := mem_minusCluster_self ha
  have hDsub : D ⊆ ((cube 2 N : Finset Site) : Set Site) :=
    minusCluster_subset_of_forall_eq_true (fun i hi ↦ hout i (by simpa using hi))
  have hDbox : D ⊆ box N := by rw [← coe_cube_eq_box N]; exact hDsub
  have hDfin : D.Finite := (box_finite N).subset hDbox
  have hOBfin : (outerBoundary D).Finite := outerBoundary_finite hDfin
  set C : Finset (Sym2 Site) := hOBfin.toFinset with hCdef
  have hCcoe : (↑C : Set (Sym2 Site)) = outerBoundary D := Set.Finite.coe_toFinset _
  have hcard : C.card = (outerBoundary D).ncard := by rw [← hCcoe, Set.ncard_coe_finset]
  have hpos : 0 < C.card := by
    rw [hcard]
    exact (Set.ncard_pos hOBfin).2 (outerBoundary_nonempty hDfin ⟨a, haD⟩)
  have hcirc : IsCircuit C :=
    isCircuit_outerBoundary hDfin ⟨a, haD⟩ (minusCluster_connected ha)
  obtain ⟨k, hk, hbond⟩ := exists_anchor_bond hDfin haD
  have hkc : k < C.card := by rw [hcard]; exact hk
  have hbondC : s(a + k • e0, a + (k + 1) • e0) ∈ C := by
    rw [← Finset.mem_coe, hCcoe]; exact hbond
  have hsucc : C.card - 1 + 1 = C.card := by omega
  refine Set.mem_iUnion.2 ⟨C.card - 1, ?_⟩
  rw [sharpContourUnion]
  refine Set.mem_iUnion₂.2 ⟨C, ?_, ?_⟩
  · rw [mem_sharpContourFinset, hsucc]
    refine ⟨mem_anchoredCircuitFinset hcirc rfl hkc hbondC, ?_, ?_⟩
    · rw [hCcoe]; exact edgeBoundary_interiorOf_outerBoundary hDfin
    · rw [hCcoe, coe_cube_eq_box N]; exact interiorOf_outerBoundary_subset_box hDbox
  · show (↑C : Set (Sym2 Site)) ⊆ discordant ζ
    rw [hCcoe]
    exact outerBoundary_minusCluster_subset_discordant a ζ

/-! ### M4: the sharpened Peierls sum -/

/-- The Peierls bound for the circuits of a given length: the sharp count `ℓ · 3 ^ (ℓ - 1)`
in place of the crude `4096 ^ ℓ` of `Peierls.isingSpecification_contourUnion_le`. -/
lemma isingSpecification_sharpContourUnion_le (b : ℝ) (N : ℕ) (a : Site) (l : ℕ) :
    isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
        (sharpContourUnion N a l) ≤
      ((l : ℝ≥0∞) + 1) * 3 ^ l * ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) := by
  classical
  set X := ENNReal.ofReal (Real.exp (-2 * b * ((l : ℝ) + 1))) with hX
  rw [sharpContourUnion]
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ X (fun C hC ↦ ?_)) ?_
  · obtain ⟨hCanch, hbd, hsub⟩ := mem_sharpContourFinset.1 hC
    have hcard : C.card = l + 1 := card_eq_of_mem_anchoredCircuitFinset hCanch
    have h := isingSpecification_subset_discordant_le (Λ := cube 2 N) b hsub hbd (fun _ ↦ true)
    rw [hcard] at h
    refine le_trans h (le_of_eq ?_)
    rw [hX]
    congr 1
    push_cast
    ring
  · rw [nsmul_eq_mul]
    have hle : ((sharpContourFinset (cube 2 N) a (l + 1)).card : ℝ≥0∞) ≤ ((l : ℝ≥0∞) + 1) * 3 ^ l := by
      have h := card_sharpContourFinset_le (cube 2 N) a (l + 1)
      simp only [Nat.add_sub_cancel] at h
      have h' : (((sharpContourFinset (cube 2 N) a (l + 1)).card : ℕ) : ℝ≥0∞)
          ≤ (((l + 1) * 3 ^ l : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h
      push_cast at h'
      exact h'
    exact mul_le_mul' hle le_rfl

/-- **Georgii (6.9), the sharpened Peierls estimate**: in a cube with the `+1` boundary
condition, the probability of a minus spin at `a` is at most `r' β`. -/
theorem isingSpecification_cube_eq_false_le' (b : ℝ) (N : ℕ) (a : Site) :
    isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
      {z : Site → Bool | z a = false} ≤ r' b := by
  have hsplit : {z : Site → Bool | z a = false} ⊆
      {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} ∪
        {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true} := by
    intro z hz
    by_cases h : ∀ i ∉ cube 2 N, z i = true
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr h
  calc isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
        {z : Site → Bool | z a = false}
      ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          ({z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} ∪
            {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true}) := measure_mono hsplit
    _ ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} +
        isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | ¬ ∀ i ∉ cube 2 N, z i = true} := measure_union_le _ _
    _ = isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          {z : Site → Bool | z a = false ∧ ∀ i ∉ cube 2 N, z i = true} := by
          rw [isingSpecification_boundary_null b (cube 2 N), add_zero]
    _ ≤ isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          (⋃ l : ℕ, sharpContourUnion N a l) :=
        measure_mono (sharp_minus_event_subset_iUnion N a)
    _ ≤ ∑' l : ℕ, isingSpecification (latticeGraph 2) 1 0 b (cube 2 N) (fun _ ↦ true)
          (sharpContourUnion N a l) := measure_iUnion_le _
    _ ≤ r' b := ENNReal.tsum_le_tsum (isingSpecification_sharpContourUnion_le b N a)

/-! ### M5: the plus phase at the sharp threshold -/

/-- **Georgii Theorem (6.9), the "in particular" part, at the sharp threshold.**
For `log 9 ≤ 2β` — i.e. `β ≥ log 3 ≈ 1.0986`, against the `8 log 2 ≈ 5.5452` of
`Peierls.exists_two_shiftInvariant_gibbs` — the two-dimensional Ising ferromagnet with coupling
`1` and no external field has two distinct shift-invariant Gibbs measures `μ₋ = τ(μ₊)`,
exchanged by the spin flip, with `μ₊(σ₀ = -1) < 1/2 < μ₋(σ₀ = -1)`: spontaneous magnetisation. `Peierls.exists_two_shiftInvariant_gibbs_of_cube` instantiated with the sharpened cube
estimate `isingSpecification_cube_eq_false_le'` and threshold `r'_le_quarter`. -/
theorem exists_two_shiftInvariant_gibbs_sharp (b : ℝ) (hb : Real.log 9 ≤ 2 * b) :
    ∃ mp mm : ProbabilityMeasure (Site → Bool),
      mp ≠ mm ∧
      mp ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      mm ∈ GP (S := Fin 2 → ℤ) (E := Bool) (isingSpecification (latticeGraph 2) 1 0 b) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mp : Measure (Site → Bool)) mp) ∧
      (∀ j : Site, MeasurePreserving (shift Bool j).toFun (mm : Measure (Site → Bool)) mm) ∧
      (mm : Measure (Site → Bool)) = Measure.map spinFlip.toFun (mp : Measure (Site → Bool)) ∧
      (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} < 2⁻¹ ∧
      2⁻¹ < (mm : Measure (Site → Bool)) {z : Site → Bool | z 0 = false} ∧
      2⁻¹ < (mp : Measure (Site → Bool)) {z : Site → Bool | z 0 = true} :=
  Peierls.exists_two_shiftInvariant_gibbs_of_cube
    (fun N a ↦ isingSpecification_cube_eq_false_le' b N a) (r'_le_quarter hb)

/-- `log 9 / 2 = log 3`. -/
lemma log_nine_div_two : Real.log 9 / 2 = Real.log 3 := by
  have h9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 from by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h9]
  ring

/-- **Georgii Theorem (6.9) at the sharp threshold**: for `β ≥ log 3` the set of Gibbs measures
of the two-dimensional Ising ferromagnet is not a singleton, `|𝒢(βΦ)| > 1`. -/
theorem nontrivial_GP_isingSpecification_of_log_three {β : ℝ} (hβ : Real.log 3 ≤ β) :
    (GP (S := Fin 2 → ℤ) (E := Bool)
      (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial := by
  have hb : Real.log 9 ≤ 2 * β := by
    rw [← log_nine_div_two] at hβ
    linarith
  obtain ⟨mp, mm, hne, hp, hm, -, -, -, -, -, -⟩ := exists_two_shiftInvariant_gibbs_sharp β hb
  exact ⟨mp, hp, mm, hm, hne⟩

/-- The two temperature ranges of `ising_two_dimensional_phase_transition_sharp` are still
disjoint: `1/4 < log 9 / 2 = log 3 ≈ 1.0986`. -/
theorem quarter_lt_log_nine_div_two : (1 : ℝ) / 4 < Real.log 9 / 2 := by
  have h : (1 : ℝ) - (9 : ℝ)⁻¹ ≤ Real.log 9 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  norm_num at h
  linarith

/-- **Georgii's `0 < β_c < ∞` for the two-dimensional Ising ferromagnet, sharpened.**

* At high temperature (`0 ≤ β < 1/4`) the Gibbs measure is unique — Dobrushin (8.7)+(8.8),
  `subsingleton_GP_ising2D_of_abs_lt`.
* At low temperature (`log 9 ≤ 2β`, i.e. `β ≥ log 3`) there are at least two — the Peierls
  argument (6.9) with Georgii's own contour count `ℓ · 3 ^ (ℓ - 1)`.

Since `1/4 < log 9 / 2` (`quarter_lt_log_nine_div_two`) the two ranges are disjoint, so the
statement is not vacuous: the transition point lies in `[1/4, log 3]`, a window some five times
narrower than the `[1/4, 8 log 2]` of `ising_two_dimensional_phase_transition`.

This is the two-sided bracket only; the sharp form, with a `β_c` satisfying uniqueness below and
non-uniqueness above, is `ising_sharp_phase_transition` in
`GibbsMeasure/Model/SharpCriticalTemperature.lean`. -/
theorem ising_two_dimensional_phase_transition_sharp :
    (∀ β : ℝ, |β| < 1 / 4 →
        (GP (S := Fin 2 → ℤ) (E := Bool)
          (isingSpecification (latticeGraph 2) 1 0 β)).Subsingleton) ∧
    (∀ β : ℝ, 0 ≤ β → β < 1 / 4 →
        ∃! μ : ProbabilityMeasure (Site → Bool),
          μ ∈ GP (S := Fin 2 → ℤ) (E := Bool)
            (isingSpecification (latticeGraph 2) 1 0 β)) ∧
    (∀ β : ℝ, Real.log 9 ≤ 2 * β →
        (GP (S := Fin 2 → ℤ) (E := Bool)
          (isingSpecification (latticeGraph 2) 1 0 β)).Nontrivial) ∧
    (1 : ℝ) / 4 < Real.log 9 / 2 := by
  refine ⟨fun β hβ ↦ subsingleton_GP_ising2D_of_abs_lt hβ,
    fun β hβ0 hβ ↦ existsUnique_mem_GP_ising2D_of_abs_lt ?_, fun β hβ ↦ ?_,
    quarter_lt_log_nine_div_two⟩
  · rwa [abs_of_nonneg hβ0]
  · refine nontrivial_GP_isingSpecification_of_log_three ?_
    rw [← log_nine_div_two]
    linarith

end MeasureTheory.GibbsMeasure.PeierlsSharp

end

end

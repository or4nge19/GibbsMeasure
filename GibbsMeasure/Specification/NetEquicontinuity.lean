/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Existence

/-!
# Georgii Theorems (4.12) and (4.13): local equicontinuity of nets of Gibbs distributions

General forms of Georgii §4.2, Theorems (4.12) and (4.13), for a **probability** reference
measure `ν` (Georgii's finite-`λ` case; WLOG by Georgii (1.28)(3) one can normalize a finite
`λ`). This simplifies Georgii's hypotheses:

* Georgii (4.12) additionally requires a set `B_Λ ∈ 𝓔^Λ` with `B ⊆ {σ_Λ ∈ B_Λ}` and
  `λ^Λ(B_Λ) < ∞`. For a probability reference measure we may take `B_Λ = E^Λ`, whose
  `ν^Λ`-measure is `1 < ∞`; the hypothesis is vacuous and is dropped.
* Georgii's `limsup_α sup_{ω ∈ B} ρ^α_Λ(ω) < ∞` is stated as the (equivalent, directly usable)
  eventual bound `∀ᶠ a, ∀ ω ∈ B, ρs a Λ ω ≤ C` for a finite `C`, with the `limsup`-`iSup` form
  derived (`locallyEquicontinuous_of_limsup_iSup_ne_top`).
* Georgii (4.13)(i) `0 < λ(K_ℓ) < ∞` loses its finiteness half; the positivity half is only
  needed for the Hamiltonian form (`Potential.locallyEquicontinuous_of_confinement_hamiltonian`
  in `GibbsMeasure/Potential/Existence.lean`).

The bounded-density special case (Georgii Comment (4.14)(1),
`Potential.locallyEquicontinuous_finiteVolumeDistributions`) is derived from the general
theorem in `GibbsMeasure/Potential/Existence.lean`.
-/

@[expose] public section

open Filter MeasureTheory MeasureTheory.GibbsMeasure Set Topology
open scoped ENNReal Topology

noncomputable section

namespace MeasureTheory.GibbsMeasure

variable {S E ι : Type*} [MeasurableSpace E] {l : Filter ι}

/-- **Georgii Theorem (4.12).** A net of finite-volume Gibbs distributions `νₐ γᵃ_{Λₐ}` with
`Λₐ ↑ S` is locally equicontinuous if, for each volume and `ε > 0`, the densities are eventually
bounded on a set of eventual measure `≥ 1 - ε`. -/
theorem locallyEquicontinuous_of_eventually_boundedOn
    (ν : Measure E) [IsProbabilityMeasure ν]
    (ρs : ι → Finset S → (S → E) → ℝ≥0∞)
    (hρs : ∀ a, (Specification.isssd ν).IsModifier (ρs a))
    (Λs : ι → Finset S) (hΛs : Tendsto Λs l atTop)
    (νs : ι → ProbabilityMeasure (S → E))
    (μs : ι → ProbabilityMeasure (S → E))
    (hμs : ∀ a, μs a
      = ((Specification.isssd ν).modification (ρs a) (hρs a)).bindPM (Λs a) (νs a))
    (hBC : ∀ (Λ : Finset S) (ε : ℝ≥0∞), 0 < ε →
      ∃ (B : Set (S → E)) (C : ℝ≥0∞), MeasurableSet B ∧ C ≠ ∞ ∧
        (∀ᶠ a in l, ∀ ω ∈ B, ρs a Λ ω ≤ C) ∧
        limsup (fun a ↦ (μs a : Measure (S → E)) Bᶜ) l ≤ ε) :
    LocallyEquicontinuous l μs := by
  intro Λ A hmeas hanti hempty
  -- full-σ-algebra measurability of the events
  have hAfull : ∀ m, MeasurableSet (A m) := fun m ↦
    cylinderEvents_le_pi (X := fun _ : S ↦ E) _ (hmeas m)
  -- the free measure `ν^S` of the events tends to `0`
  have hν0 : Tendsto (fun m ↦ Measure.infinitePi (fun _ : S ↦ ν) (A m)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := Measure.infinitePi (fun _ : S ↦ ν))
      (fun m ↦ (hAfull m).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rwa [hempty, measure_empty] at h
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨B, C, hBmeas, hCne, hCbound, hBc⟩ := hBC Λ (ε / 2) (ENNReal.half_pos hε.ne')
  -- Georgii's estimate, for every event of the sequence:
  -- `limsup_a μs a (A m) ≤ C · ν^S(A m) + ε/2`.
  have key : ∀ m, limsup (fun a ↦ (μs a : Measure (S → E)) (A m)) l
      ≤ C * Measure.infinitePi (fun _ : S ↦ ν) (A m) + ε / 2 := by
    intro m
    have hev : ∀ᶠ a in l, (μs a : Measure (S → E)) (A m)
        ≤ C * Measure.infinitePi (fun _ : S ↦ ν) (A m) + (μs a : Measure (S → E)) Bᶜ := by
      filter_upwards [hΛs.eventually_ge_atTop Λ, hCbound] with a hΛa hCa
      rw [hμs a, Specification.coe_bindPM]
      -- `μs a = νs a γᵃ_{Λs a}`; split `A m` along `B`
      have h1 : ((νs a : Measure (S → E)).bind
            ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) (A m)
          ≤ ((νs a : Measure (S → E)).bind
              ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) (A m ∩ B)
            + ((νs a : Measure (S → E)).bind
                ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) Bᶜ := by
        refine (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
        by_cases hxB : x ∈ B
        · exact Or.inl ⟨hx, hxB⟩
        · exact Or.inr hxB
      -- consistency `μs a γᵃ_Λ = μs a` for `Λ ⊆ Λs a` and the density bound on `B`
      have h2 : ((νs a : Measure (S → E)).bind
            ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) (A m ∩ B)
          ≤ C * Measure.infinitePi (fun _ : S ↦ ν) (A m) := by
        have hbind : (((νs a : Measure (S → E)).bind
              ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))).bind
                ((Specification.isssd ν).modification (ρs a) (hρs a) Λ))
            = (νs a : Measure (S → E)).bind
                ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a)) :=
          ((Specification.isssd ν).modification (ρs a) (hρs a)).bind_bind_of_subset hΛa _
        have : IsProbabilityMeasure ((νs a : Measure (S → E)).bind
            ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) :=
          ((Specification.isssd ν).modification (ρs a) (hρs a)).isProbabilityMeasure_bind
            (Λs a) _
        calc ((νs a : Measure (S → E)).bind
              ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) (A m ∩ B)
            = (((νs a : Measure (S → E)).bind
                ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))).bind
                  ((Specification.isssd ν).modification (ρs a) (hρs a) Λ)) (A m ∩ B) := by
              rw [hbind]
          _ = ∫⁻ ω, (Specification.isssd ν).modification (ρs a) (hρs a) Λ ω (A m ∩ B)
                ∂((νs a : Measure (S → E)).bind
                  ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) :=
              Measure.bind_apply ((hAfull m).inter hBmeas)
                (((Specification.isssd ν).modification (ρs a)
                  (hρs a)).measurable_kernel_toMeasure Λ).aemeasurable
          _ ≤ ∫⁻ _, C * Measure.infinitePi (fun _ : S ↦ ν) (A m)
                ∂((νs a : Measure (S → E)).bind
                  ((Specification.isssd ν).modification (ρs a) (hρs a) (Λs a))) := by
              refine lintegral_mono fun ω ↦ ?_
              calc (Specification.isssd ν).modification (ρs a) (hρs a) Λ ω (A m ∩ B)
                  ≤ C * Specification.isssd ν Λ ω (A m) :=
                    Specification.modification_apply_inter_le _ _ _ Λ ω (hAfull m) hBmeas hCa
                _ = C * Measure.infinitePi (fun _ : S ↦ ν) (A m) := by
                    rw [Specification.isssd_apply_of_mem_cylinderEvents ν Λ ω (hmeas m)]
          _ = C * Measure.infinitePi (fun _ : S ↦ ν) (A m) := by
              rw [lintegral_const, measure_univ, mul_one]
      exact h1.trans (add_le_add h2 le_rfl)
    calc limsup (fun a ↦ (μs a : Measure (S → E)) (A m)) l
        ≤ limsup (fun a ↦ C * Measure.infinitePi (fun _ : S ↦ ν) (A m)
            + (μs a : Measure (S → E)) Bᶜ) l := limsup_le_limsup hev
      _ ≤ C * Measure.infinitePi (fun _ : S ↦ ν) (A m) + ε / 2 := by
          rcases l.eq_or_neBot with rfl | hne
          · simp
          · rw [limsup_const_add l (fun a ↦ (μs a : Measure (S → E)) Bᶜ)
              (C * Measure.infinitePi (fun _ : S ↦ ν) (A m))
              ⟨⊤, Eventually.of_forall fun _ ↦ le_top⟩ ⟨0, fun _ _ ↦ zero_le⟩]
            exact add_le_add le_rfl hBc
  -- `C · ν^S(A m) → 0`, so eventually `limsup_a μs a (A m) ≤ ε/2 + ε/2 = ε`
  have hK0 : Tendsto (fun m ↦ C * Measure.infinitePi (fun _ : S ↦ ν) (A m)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := C) hν0 (Or.inr hCne)
  filter_upwards [hK0.eventually_lt_const (ENNReal.half_pos hε.ne')] with m hm
  calc limsup (fun a ↦ (μs a : Measure (S → E)) (A m)) l
      ≤ C * Measure.infinitePi (fun _ : S ↦ ν) (A m) + ε / 2 := key m
    _ ≤ ε / 2 + ε / 2 := add_le_add hm.le le_rfl
    _ = ε := ENNReal.add_halves ε

/-- Georgii Theorem (4.12), with the density hypothesis in the literal form
`limsup_a ⨆ ω ∈ B, ρₐ(ω) ≠ ∞`. -/
theorem locallyEquicontinuous_of_limsup_iSup_ne_top
    (ν : Measure E) [IsProbabilityMeasure ν]
    (ρs : ι → Finset S → (S → E) → ℝ≥0∞)
    (hρs : ∀ a, (Specification.isssd ν).IsModifier (ρs a))
    (Λs : ι → Finset S) (hΛs : Tendsto Λs l atTop)
    (νs μs : ι → ProbabilityMeasure (S → E))
    (hμs : ∀ a, μs a
      = ((Specification.isssd ν).modification (ρs a) (hρs a)).bindPM (Λs a) (νs a))
    (hBC : ∀ (Λ : Finset S) (ε : ℝ≥0∞), 0 < ε →
      ∃ B : Set (S → E), MeasurableSet B ∧
        limsup (fun a ↦ ⨆ ω ∈ B, ρs a Λ ω) l ≠ ∞ ∧
        limsup (fun a ↦ (μs a : Measure (S → E)) Bᶜ) l ≤ ε) :
    LocallyEquicontinuous l μs := by
  refine locallyEquicontinuous_of_eventually_boundedOn ν ρs hρs Λs hΛs νs μs hμs
    fun Λ ε hε ↦ ?_
  obtain ⟨B, hBmeas, hBsup, hBc⟩ := hBC Λ ε hε
  refine ⟨B, limsup (fun a ↦ ⨆ ω ∈ B, ρs a Λ ω) l + 1, hBmeas,
    ENNReal.add_ne_top.2 ⟨hBsup, ENNReal.one_ne_top⟩, ?_, hBc⟩
  have hlt : limsup (fun a ↦ ⨆ ω ∈ B, ρs a Λ ω) l
      < limsup (fun a ↦ ⨆ ω ∈ B, ρs a Λ ω) l + 1 :=
    ENNReal.lt_add_right hBsup one_ne_zero
  filter_upwards [eventually_lt_of_limsup_lt hlt] with a ha ω hω
  exact (le_iSup₂ (f := fun ω (_ : ω ∈ B) ↦ ρs a Λ ω) ω hω).trans ha.le

end MeasureTheory.GibbsMeasure

/-!
### Georgii Corollary (4.13)

Two forms are given, both for a probability reference measure `ν`:

* a **density form** (`locallyEquicontinuous_of_confinement`), whose hypothesis (iii) directly
  bounds the densities on the confinement boxes `B_ℓ = K_ℓ^Δ × E^{S∖Δ}` — this is the actual
  reduction of (4.13) to (4.12): the choice of the confinement level `ℓ` from hypothesis (ii)
  by a union bound over the sites of `Δ`;
* the **Hamiltonian form** (`Potential.locallyEquicontinuous_of_confinement_hamiltonian`),
  Georgii's own statement for Gibbsian specifications: hypothesis (iii) bounds `|H_Λ^{Φᵃ}|`
  on the boxes, and the density bound
  `ρ_Λ ≤ e^{|β|c} / (e^{-|β|c} ν(K_ℓ)^{|Λ|})` is derived from it
  (Georgii's `e^{2c(ℓ)} λ(K_ℓ)^{-|Λ|}`), using `0 < ν (K ℓ)` — the surviving half of
  Georgii's hypothesis (i) (the finiteness half `λ(K_ℓ) < ∞` is automatic for `ν`).
-/

namespace MeasureTheory.GibbsMeasure

/-- **Georgii Corollary (4.13), density form.** If the mass escaping the confinement sets `K ℓ`
at each site vanishes along the net, and the densities are eventually bounded on each box
`K_ℓ^Δ × E^{S∖Δ}`, then the finite-volume Gibbs distributions are locally equicontinuous. -/
theorem locallyEquicontinuous_of_confinement
    {S E ι : Type*} [MeasurableSpace E] {l : Filter ι}
    (ν : Measure E) [IsProbabilityMeasure ν]
    (ρs : ι → Finset S → (S → E) → ℝ≥0∞)
    (hρs : ∀ a, (Specification.isssd ν).IsModifier (ρs a))
    (Λs : ι → Finset S) (hΛs : Tendsto Λs l atTop)
    (νs μs : ι → ProbabilityMeasure (S → E))
    (hμs : ∀ a, μs a
      = ((Specification.isssd ν).modification (ρs a) (hρs a)).bindPM (Λs a) (νs a))
    (K : ℕ → Set E) (hK : ∀ ℓ, MeasurableSet (K ℓ))
    (hii : ∀ i : S, Tendsto
      (fun ℓ ↦ limsup (fun a ↦ (μs a : Measure (S → E)) {ω | ω i ∉ K ℓ}) l) atTop (𝓝 0))
    (hiii : ∀ Λ : Finset S, ∃ Δ : Finset S, Λ ⊆ Δ ∧ ∀ ℓ : ℕ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ᶠ a in l, ∀ ω ∈ {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ}, ρs a Λ ω ≤ C) :
    LocallyEquicontinuous l μs := by
  refine locallyEquicontinuous_of_eventually_boundedOn ν ρs hρs Λs hΛs νs μs hμs
    fun Λ ε hε ↦ ?_
  obtain ⟨Δ, hΛΔ, hΔ⟩ := hiii Λ
  -- measurability of the confinement boxes
  have hBmeas : ∀ ℓ, MeasurableSet {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ} := by
    intro ℓ
    have h : {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ}
        = ⋂ i ∈ Δ, (fun x : S → E ↦ x i) ⁻¹' K ℓ := by
      ext x; simp
    rw [h]
    exact MeasurableSet.biInter Δ.countable_toSet fun i _ ↦ measurable_pi_apply i (hK ℓ)
  -- when `ε = ∞` any box does the job
  rcases eq_or_ne ε ∞ with rfl | hεtop
  · obtain ⟨C, hCne, hCa⟩ := hΔ 0
    exact ⟨_, C, hBmeas 0, hCne, hCa, le_top⟩
  -- when `Δ = ∅` the box is everything
  rcases Finset.eq_empty_or_nonempty Δ with rfl | hΔne
  · obtain ⟨C, hCne, hCa⟩ := hΔ 0
    refine ⟨_, C, hBmeas 0, hCne, hCa, ?_⟩
    have huniv : {x : S → E | ∀ i ∈ (∅ : Finset S), x i ∈ K 0} = univ := by
      ext x; simp
    rw [huniv, compl_univ]
    exact limsup_le_of_le (h := Eventually.of_forall fun a ↦ by simp)
  -- choose a confinement level `ℓ` from hypothesis (ii), by a union bound over `Δ`
  have hδ0 : (ε / Δ.card : ℝ≥0∞) ≠ 0 :=
    (ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top _)).ne'
  have hδtop : (ε / Δ.card : ℝ≥0∞) ≠ ∞ :=
    ENNReal.div_ne_top hεtop (Nat.cast_ne_zero.2 hΔne.card_pos.ne')
  have hall : ∀ᶠ ℓ in atTop, ∀ i ∈ Δ,
      limsup (fun a ↦ (μs a : Measure (S → E)) {ω | ω i ∉ K ℓ}) l ≤ ε / Δ.card / 2 :=
    (eventually_all_finset Δ).2 fun i _ ↦
      (ENNReal.tendsto_nhds_zero.1 (hii i)) _ (ENNReal.half_pos hδ0)
  obtain ⟨ℓ, hℓ⟩ := hall.exists
  obtain ⟨C, hCne, hCa⟩ := hΔ ℓ
  refine ⟨_, C, hBmeas ℓ, hCne, hCa, ?_⟩
  have heva : ∀ᶠ a in l, ∀ i ∈ Δ,
      (μs a : Measure (S → E)) {ω | ω i ∉ K ℓ} < ε / Δ.card :=
    (eventually_all_finset Δ).2 fun i hi ↦
      eventually_lt_of_limsup_lt ((hℓ i hi).trans_lt (ENNReal.half_lt_self hδ0 hδtop))
  refine limsup_le_of_le (h := ?_)
  filter_upwards [heva] with a ha
  have hsub : {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ}ᶜ ⊆ ⋃ i ∈ Δ, {ω : S → E | ω i ∉ K ℓ} := by
    intro x hx
    have h : ¬ ∀ i ∈ Δ, x i ∈ K ℓ := hx
    push Not at h
    obtain ⟨i, hi, hxi⟩ := h
    exact mem_biUnion hi hxi
  calc (μs a : Measure (S → E)) {x : S → E | ∀ i ∈ Δ, x i ∈ K ℓ}ᶜ
      ≤ ∑ i ∈ Δ, (μs a : Measure (S → E)) {ω | ω i ∉ K ℓ} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le Δ _)
    _ ≤ ∑ _i ∈ Δ, ε / Δ.card := Finset.sum_le_sum fun i hi ↦ (ha i hi).le
    _ = Δ.card • (ε / Δ.card) := Finset.sum_const _
    _ = (Δ.card : ℝ≥0∞) * (ε / Δ.card) := nsmul_eq_mul _ _
    _ ≤ ε := ENNReal.mul_div_le

end MeasureTheory.GibbsMeasure
end

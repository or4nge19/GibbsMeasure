/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential.Periodic
public import GibbsMeasure.Potential.GibbsTransformation
public import GibbsMeasure.Specification.Average

/-!
# Georgii Example (5.20)(3): periodic boundary conditions and symmetric Gibbs measures

Let `λ` be a finite a priori measure, `m ≥ 1`, and `Φ ∈ ℬ` a potential invariant under a
transformation group `I` with `Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ`: `I` contains the shifts, and each
`τ ∈ I` is the composition of an `m`-periodic `λ`-preserving pure spin transformation, a lattice
automorphism (Georgii's reflection group `R`), and a shift. For boxes `Δ_N ↑ S` with sides
divisible by `m`, every cluster point of the periodic-boundary sequence
`μ_N = ν_N γ^{Φ̃^{Δ_N}}_{Δ_N}` lies in `𝒢_I(Φ)`, for arbitrary boundary fields `ν_N`.

The proof combines the two halves exactly as Georgii does. The Gibbs half is Example (4.20)(2)
(`Potential.mem_GP_of_mapClusterPt_periodicModification`). For the symmetry half, the boundary
fields may be replaced by the product field `λ^S` (Georgii: "the set `𝒢₀(Φ)` does not depend on
the choice of `(ν_N)`", `mapClusterPt_bindPM_periodicModification_congr`), which is invariant
under every transformation with `λ`-preserving spins
(`Transformation.measurePreserving_infinitePi`) — in particular under the periodic modification
`τ_N` of each `τ ∈ I` (`Potential.periodize`). Proposition (5.18)
(`measurePreserving_of_mapClusterPt_average_of_eventually_preimage_eq`) then applies with the
one-element volume families `𝓡_N = {Δ_N}`: the box is `τ_{N*}`-stable, the modified potential
`Φ̃^{Δ_N}` is `τ_N`-invariant (`Potential.map_periodize_periodicModification`, Georgii's displayed
computation), and `f ∘ τ_N = f ∘ τ` eventually for every local `f`
(`Potential.eventually_preimage_periodize_eq`).

The general form `mem_GP_and_measurePreserving_of_mapClusterPt_periodicModification` is stated
for an arbitrary additive group of sites and any exhausting net of torus reductions;
`mem_GP_and_measurePreserving_of_mapClusterPt_latticePeriodic` instantiates it on `S = ℤ^d` with
Georgii's hypotheses `Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ` (the upper bound in the form: affine spatial
part and `m`-periodic `λ`-preserving spins, which the composites `τ⁰ ∘ τ_r ∘ θ_t` of Georgii's
group satisfy, `affine_and_periodic_spin_comp_siteEquiv_shift`), and
`mem_GP_and_measurePreserving_of_mapClusterPt_mPeriodicBox` fixes the concrete boxes
`Δ_n = [-m(n+1), m(n+1))^d`.
-/

@[expose] public section

open Filter Function MeasureTheory MeasureTheory.GibbsMeasure Potential Set Topology
open scoped ENNReal Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The product field `λ^S` is invariant under `λ`-preserving transformations -/

section ProductField

variable {S E : Type*} [MeasurableSpace E]

end ProductField

/-! ### Georgii Example (5.20)(3): the general form -/

section PeriodicSymmetry

variable {S E : Type*} [Countable S] [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {Φ : Potential S E} [Potential.IsPotential Φ] [Potential.IsAbsolutelySummable Φ]
  {ι : Type*} {l : Filter ι} {G : ι → AddSubgroup S} {Δ : ι → Finset S} {π : ι → S → S}
  {anchor : Finset S → S}

/-- **Georgii (5.20)(3): "the set `𝒢₀(Φ)` does not depend on the choice of `(ν_N)`".** Cluster
points of the periodic-boundary net do not depend on the boundary fields: the finite-volume
Gibbs distribution with periodic boundary condition, restricted to `𝓕_{Δ_N}`, is independent of
the boundary condition, and every local event eventually lies in `𝓕_{Δ_N}`. -/
theorem mapClusterPt_bindPM_periodicModification_congr
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (hπ : ∀ a, IsTorusReduction (G a) (Δ a) (π a)) (ha : IsAnchor anchor)
    (hΦ : Φ.IsShiftInvariant) (hΔ : Tendsto Δ l atTop)
    (νs νs' : ι → ProbabilityMeasure (S → E)) {μ : ProbabilityMeasure (S → E)}
    (hcp : haveI := fun a ↦ isPotential_periodicModification (Φ := Φ) (hπ a) ha hΦ
      haveI := fun a ↦ isAbsolutelySummable_periodicModification (Φ := Φ) (hπ a) ha hΦ
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun a ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).bindPM (Δ a) (νs a))) :
    haveI := fun a ↦ isPotential_periodicModification (Φ := Φ) (hπ a) ha hΦ
    haveI := fun a ↦ isAbsolutelySummable_periodicModification (Φ := Φ) (hπ a) ha hΦ
    MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun a ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).bindPM (Δ a) (νs' a)) := by
  have instP := fun a ↦ isPotential_periodicModification (Φ := Φ) (hπ a) ha hΦ
  have instS := fun a ↦ isAbsolutelySummable_periodicModification (Φ := Φ) (hπ a) ha hΦ
  refine mapClusterPt_of_tendsto_real_sub hcp fun A hA ↦ ?_
  obtain ⟨Λ, hAΛ⟩ := mem_localEvents_iff_cylinderEvents.1 hA
  have hAm : MeasurableSet A := .of_mem_measurableCylinders hA
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hΔ.eventually (Filter.eventually_ge_atTop Λ)] with a haΛ
  have hAd : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) ((Δ a : Finset S) : Set S)] A :=
    cylinderEvents_mono (Finset.coe_subset.2 haΛ) A hAΛ
  obtain ⟨ω₀⟩ : Nonempty (S → E) := (νs a).nonempty
  have hbind : ∀ κ : ProbabilityMeasure (S → E),
      ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).bindPM (Δ a) κ :
        Measure (S → E)) A
      = gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β (Δ a) ω₀ A := by
    intro κ
    rw [Specification.coe_bindPM, Measure.bind_apply hAm
      ((gibbsSpecificationOfAbsolutelySummable
        (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).measurable_kernel_toMeasure
          (Δ a)).aemeasurable]
    calc ∫⁻ ω, gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β (Δ a) ω A ∂(κ : Measure (S → E))
        = ∫⁻ _, gibbsSpecificationOfAbsolutelySummable
            (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β (Δ a) ω₀ A
              ∂(κ : Measure (S → E)) :=
          lintegral_congr fun ω ↦
            gibbsSpecification_periodicModification_apply_eq ν β (hπ a) ω ω₀ hAd
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]
  change (0 : ℝ) = _ - _
  rw [measureReal_def, measureReal_def, hbind (νs a), hbind (νs' a), sub_self]

/-- **Georgii Example (5.20)(3): periodic boundary conditions produce symmetric Gibbs
measures.** Let `Φ ∈ ℬ` be a shift-invariant potential, invariant under a set `I` of
transformations that are periodizable along an exhausting net of tori `(G_N, Δ_N, π_N)` and whose
spins preserve the a priori measure `λ` — Georgii's `Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ` with translates
`Δ_N` of the cubes `S ∩ [1, mN]^d`. Then every cluster point `μ` of the periodic-boundary net
`μ_N = ν_N γ^{Φ̃^{Δ_N}}_{Δ_N}` is an `I`-invariant Gibbs measure for `Φ`: `𝒢₀(Φ) ⊆ 𝒢_I(Φ)`.

The boundary fields `ν_N` are arbitrary: the Gibbs half is Example (4.20)(2)
(`mem_GP_of_mapClusterPt_periodicModification`), and for the symmetry half the boundary fields
may be replaced by the product field `λ^S` (`mapClusterPt_bindPM_periodicModification_congr`),
which is invariant under every periodic modification `τ_N`; Proposition (5.18) applies with the
one-element volume families `𝓡_N = {Δ_N}`, since `τ_{N*} Δ_N = Δ_N`, the modified potential
`Φ̃^{Δ_N}` is `τ_N`-invariant, and `f ∘ τ_N = f ∘ τ` eventually for every local `f`. -/
theorem mem_GP_and_measurePreserving_of_mapClusterPt_periodicModification [l.NeBot]
    (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (hπ : ∀ a, IsTorusReduction (G a) (Δ a) (π a)) (ha : IsAnchor anchor)
    (hΦ : Φ.IsShiftInvariant) (hΔ : Tendsto Δ l atTop)
    {I : Set (Transformation S E)} (hI : ∀ τ ∈ I, ∀ a, IsPeriodizable (G a) τ)
    (hIspin : ∀ τ ∈ I, ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hIΦ : ∀ τ ∈ I, Potential.map τ Φ = Φ)
    (νs : ι → ProbabilityMeasure (S → E)) {μ : ProbabilityMeasure (S → E)}
    (hcp : haveI := fun a ↦ isPotential_periodicModification (Φ := Φ) (hπ a) ha hΦ
      haveI := fun a ↦ isAbsolutelySummable_periodicModification (Φ := Φ) (hπ a) ha hΦ
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence S E) l
      fun a ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).bindPM (Δ a) (νs a))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure (S → E)) μ := by
  have instP := fun a ↦ isPotential_periodicModification (Φ := Φ) (hπ a) ha hΦ
  have instS := fun a ↦ isAbsolutelySummable_periodicModification (Φ := Φ) (hπ a) ha hΦ
  refine ⟨mem_GP_of_mapClusterPt_periodicModification ν β hπ ha hΦ hΔ νs hcp, fun τ hτmem ↦ ?_⟩
  -- replace the boundary fields by the product field `λ^S`, which is `τ_N`-invariant
  set νPi : ProbabilityMeasure (S → E) :=
    ⟨Measure.infinitePi fun _ : S ↦ ν, inferInstance⟩ with hνPi
  have hcp' := mapClusterPt_bindPM_periodicModification_congr ν β hπ ha hΦ hΔ νs
    (fun _ ↦ νPi) hcp
  -- Proposition (5.18) with `τ_N`, `γ^{Φ̃^{Δ_N}}`, `ν = λ^S` and `𝓡_N = {Δ_N}`
  refine measurePreserving_of_mapClusterPt_average_of_eventually_preimage_eq
    (τs := fun a ↦ periodize τ (hπ a) (hI τ hτmem a))
    (γs := fun a ↦ gibbsSpecificationOfAbsolutelySummable
      (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β)
    (νs := fun _ ↦ νPi) (R := fun a ↦ {Δ a})
    (fun a ↦ Potential.isInvariant_gibbsSpecification _ _ ν β (fun i ↦ hIspin τ hτmem i)
      (map_periodize_periodicModification (hπ a) ha hΦ (hI τ hτmem a) (hIΦ τ hτmem)))
    (fun a ↦ Transformation.measurePreserving_infinitePi _ fun i ↦ hIspin τ hτmem i)
    (fun _ ↦ Finset.singleton_nonempty _) ?_
    (fun A hA ↦ eventually_preimage_periodize_eq hπ τ (hI τ hτmem) hΔ hA)
    (μs := fun a ↦ (gibbsSpecificationOfAbsolutelySummable
      (Φ := periodicModification Φ (Δ a) (π a) anchor) ν β).bindPM (Δ a) νPi)
    (fun a ↦ by rw [Specification.average_singleton]; rfl) hcp'
  -- the box is stable under `τ_N`, so the Følner ratio of `𝓡_N = {Δ_N}` vanishes identically
  refine tendsto_const_nhds.congr fun a ↦ ?_
  have hmap : ({Δ a} : Finset (Finset S)).map
      (Finset.mapEmbedding (periodize τ (hπ a) (hI τ hτmem a)).sites.toEmbedding).toEmbedding
      = {Δ a} := by
    rw [Finset.map_singleton]
    congr 1
    change (Finset.mapEmbedding (periodize τ (hπ a) (hI τ hτmem a)).sites.toEmbedding) (Δ a) = Δ a
    rw [Finset.mapEmbedding_apply, map_periodize_sites_box]
  rw [hmap, symmDiff_self]
  simp

end PeriodicSymmetry

/-! ### Georgii Example (5.20)(3) on the lattice `ℤ^d`: `Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ` -/

section Lattice

variable {d : ℕ} {E : Type*} [MeasurableSpace E]

/-- A lattice automorphism maps the constant-period group `p·ℤ^d` into itself: `r (p•h) = p•r h`.
This is why Georgii's reflections and rotations preserve the congruence modulo `mN·S`. -/
lemma addEquiv_mem_piPeriods {c : ℤ} (r : (Fin d → ℤ) ≃+ (Fin d → ℤ)) {g : Fin d → ℤ}
    (hg : g ∈ piPeriods fun _ ↦ c) : r g ∈ piPeriods fun _ ↦ c := by
  obtain ⟨h, rfl⟩ : ∃ h : Fin d → ℤ, g = c • h := by
    choose h hh using fun k ↦ AddSubgroup.mem_zmultiples_iff.1 (mem_piPeriods.1 hg k)
    refine ⟨h, funext fun k ↦ ?_⟩
    rw [Pi.smul_apply, ← hh k, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [map_zsmul]
  exact mem_piPeriods.2 fun k ↦ AddSubgroup.mem_zmultiples_iff.2
    ⟨r h k, by rw [Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]⟩

/-- **Georgii (5.20)(3) on `ℤ^d`.** A transformation with affine spatial part — a lattice
automorphism composed with a translation, as every element of Georgii's `R ∘ Θ` is — and
`m`-periodic spins is periodizable along every torus whose periods are multiples of `m`. -/
lemma isPeriodizable_of_affine {m : ℕ} {c : ℤ} (hc : (m : ℤ) ∣ c)
    {τ : Transformation (Fin d → ℤ) E}
    (hsites : ∃ r : (Fin d → ℤ) ≃+ (Fin d → ℤ), ∀ i, τ.sites i = r i + τ.sites 0)
    (hspin : ∀ i j : Fin d → ℤ, (∀ k, (m : ℤ) ∣ i k - j k) → τ.spin i = τ.spin j) :
    IsPeriodizable (piPeriods fun _ ↦ c) τ := by
  obtain ⟨r, hr⟩ := hsites
  have hsymm : ∀ y, τ.sites.symm y = r.symm (y - τ.sites 0) := by
    intro y
    apply τ.sites.injective
    rw [Equiv.apply_symm_apply, hr, AddEquiv.apply_symm_apply, sub_add_cancel]
  refine ⟨fun i j hij ↦ hspin i j fun k ↦ ?_, fun g hg ↦ ?_, fun g hg ↦ ?_⟩
  · refine hc.trans ?_
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_piPeriods.1 hij k)
    refine ⟨n, ?_⟩
    have h1 : i k - j k = n * c := by
      rw [← smul_eq_mul, hn, Pi.sub_apply]
    rw [h1, mul_comm]
  · refine ⟨r g, addEquiv_mem_piPeriods r hg, fun i ↦ ?_⟩
    rw [hr (i + g), hr i, _root_.map_add]
    abel
  · refine ⟨r.symm g, addEquiv_mem_piPeriods r.symm hg, fun i ↦ ?_⟩
    rw [hsymm (i + g), hsymm i, ← _root_.map_add]
    congr 1
    abel

/-- **Georgii's group `T_λ^{(m)} ∘ R ∘ Θ` on `ℤ^d`.** A composite `τ⁰ ∘ τ_r ∘ θ_t` of an
`m`-periodic `λ`-preserving pure spin transformation `τ⁰ ∈ T_λ^{(m)}`, the site transformation of
a lattice automorphism `r` — Georgii's reflection group `R` consists of these — and a shift
`θ_t ∈ Θ` satisfies the three hypotheses of
`mem_GP_and_measurePreserving_of_mapClusterPt_latticePeriodic`: affine spatial part,
`m`-periodic spins, and `λ`-preserving spins. -/
lemma affine_and_periodic_spin_comp_siteEquiv_shift {ν : Measure E} {m : ℕ}
    (τ0 : Transformation (Fin d → ℤ) E) (h0 : τ0.sites = Equiv.refl (Fin d → ℤ))
    (h0per : ∀ i j : Fin d → ℤ, (∀ k, (m : ℤ) ∣ i k - j k) → τ0.spin i = τ0.spin j)
    (h0ν : ∀ i, MeasurePreserving (τ0.spin i) ν ν)
    (r : (Fin d → ℤ) ≃+ (Fin d → ℤ)) (t : Fin d → ℤ) :
    (∃ r' : (Fin d → ℤ) ≃+ (Fin d → ℤ), ∀ i,
        (τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp (shift E t))).sites i
          = r' i + (τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp
              (shift E t))).sites 0)
      ∧ (∀ i j : Fin d → ℤ, (∀ k, (m : ℤ) ∣ i k - j k) →
          (τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp (shift E t))).spin i
            = (τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp (shift E t))).spin j)
      ∧ ∀ i, MeasurePreserving
          ((τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp (shift E t))).spin i)
          ν ν := by
  have hsites : ∀ i, (τ0.comp ((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp
      (shift E t))).sites i = r (i + t) := by
    intro i
    change τ0.sites (r (Equiv.addRight t i)) = r (i + t)
    rw [h0]
    simp
  refine ⟨⟨r, fun i ↦ ?_⟩, fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · rw [hsites, hsites, zero_add, _root_.map_add]
  · change (((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp (shift E t)).spin
        (τ0.sites.symm i)).trans (τ0.spin i) = _
    rw [h0per i j hij]
    rfl
  · change MeasurePreserving ((((siteEquiv E (r : (Fin d → ℤ) ≃ (Fin d → ℤ))).comp
        (shift E t)).spin (τ0.sites.symm i)).trans (τ0.spin i)) ν ν
    exact h0ν i

/-- **Georgii Example (5.20)(3) on the lattice `S = ℤ^d`.** Let `λ` be a probability measure,
`m ≥ 1`, and `Φ ∈ ℬ` a potential invariant under a set `I` of transformations with
`Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ` — `I` contains the shifts, and every `τ ∈ I` has affine spatial
part (a lattice automorphism composed with a translation) and `m`-periodic `λ`-preserving spins.
Choose rectangular boxes `Δ_N` with sides `p N` divisible by `m` and `Δ_N ↑ S` — translates of
the cubes `S ∩ [1, mN]^d`. Then every cluster point of the periodic-boundary sequence
`μ_N = ν_N γ^{Φ̃^{Δ_N}}_{Δ_N}` lies in `𝒢_I(Φ)`, for arbitrary boundary fields `ν_N`. -/
theorem mem_GP_and_measurePreserving_of_mapClusterPt_latticePeriodic
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ]
    [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    (m : ℕ) {p : ℕ → ℤ} {c : ℕ → Fin d → ℤ} (hp : ∀ n, 0 < p n) (hmp : ∀ n, (m : ℤ) ∣ p n)
    (hbox : Tendsto (fun n ↦ piBox (c n) fun _ ↦ p n) atTop atTop)
    {I : Set (Transformation (Fin d → ℤ) E)} (hΘ : ∀ t, shift E t ∈ I)
    (hIsites : ∀ τ ∈ I, ∃ r : (Fin d → ℤ) ≃+ (Fin d → ℤ), ∀ i, τ.sites i = r i + τ.sites 0)
    (hIper : ∀ τ ∈ I, ∀ i j : Fin d → ℤ, (∀ k, (m : ℤ) ∣ i k - j k) → τ.spin i = τ.spin j)
    (hIspin : ∀ τ ∈ I, ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hIΦ : ∀ τ ∈ I, Potential.map τ Φ = Φ)
    (νs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hcp : haveI := fun n ↦ isPotential_periodicModification (Φ := Φ)
            (isTorusReduction_piIntReduce (fun _ ↦ hp n) (c n)) isAnchor_lexAnchor
            (fun t ↦ hIΦ _ (hΘ t))
      haveI := fun n ↦ isAbsolutelySummable_periodicModification (Φ := Φ)
            (isTorusReduction_piIntReduce (fun _ ↦ hp n) (c n)) isAnchor_lexAnchor
            (fun t ↦ hIΦ _ (hΘ t))
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E) atTop
      fun n ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (piBox (c n) fun _ ↦ p n)
            (piIntReduce (c n) fun _ ↦ p n) lexAnchor) ν β).bindPM
              (piBox (c n) fun _ ↦ p n) (νs n))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  mem_GP_and_measurePreserving_of_mapClusterPt_periodicModification ν β
    (G := fun n ↦ piPeriods fun _ ↦ p n)
    (fun n ↦ isTorusReduction_piIntReduce (fun _ ↦ hp n) (c n)) isAnchor_lexAnchor
    (fun t ↦ hIΦ _ (hΘ t)) hbox
    (fun τ hτ n ↦ isPeriodizable_of_affine (hmp n) (hIsites τ hτ) (hIper τ hτ))
    hIspin hIΦ νs hcp

/-- Georgii (5.20)(3): a concrete choice of the boxes — the cube `Δ_n = [-m(n+1), m(n+1))^d`, a
translate of `S ∩ [1, 2m(n+1)]^d` with side `2m(n+1)` divisible by `m`. -/
def mPeriodicBox (d m n : ℕ) : Finset (Fin d → ℤ) :=
  piBox (fun _ ↦ -(m * (n + 1) : ℤ)) fun _ ↦ 2 * (m * (n + 1) : ℤ)

/-- The box `mPeriodicBox d m n`, viewed as the torus `ℤ^d / 2m(n+1)·ℤ^d`. -/
def mPeriodicTorus (d m n : ℕ) : (Fin d → ℤ) → Fin d → ℤ :=
  piIntReduce (fun _ ↦ -(m * (n + 1) : ℤ)) fun _ ↦ 2 * (m * (n + 1) : ℤ)

lemma isTorusReduction_mPeriodicTorus {m : ℕ} (hm : 0 < m) (n : ℕ) :
    IsTorusReduction (piPeriods fun _ : Fin d ↦ 2 * (m * (n + 1) : ℤ)) (mPeriodicBox d m n)
      (mPeriodicTorus d m n) :=
  isTorusReduction_piIntReduce (fun _ ↦ by positivity) _

/-- **`Δ_n ↑ ℤ^d`**: the boxes `[-m(n+1), m(n+1))^d` exhaust the lattice. -/
lemma tendsto_mPeriodicBox_atTop {m : ℕ} (hm : 0 < m) :
    Tendsto (mPeriodicBox d m) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun Λ ↦
    ⟨Λ.sup fun y ↦ Finset.univ.sup fun k ↦ (y k).natAbs, fun n hn x hx ↦ ?_⟩
  refine mem_piBox.2 fun k ↦ ?_
  have h1 : (x k).natAbs ≤ n :=
    le_trans (le_trans (Finset.le_sup (f := fun k ↦ (x k).natAbs) (Finset.mem_univ k))
      (Finset.le_sup (f := fun y : Fin d → ℤ ↦ Finset.univ.sup fun k ↦ (y k).natAbs) hx)) hn
  have hM : (n : ℤ) + 1 ≤ (m : ℤ) * ((n : ℤ) + 1) :=
    le_mul_of_one_le_left (by positivity) (by exact_mod_cast hm)
  rw [Finset.mem_Ico]
  set M : ℤ := (m : ℤ) * ((n : ℤ) + 1) with hMdef
  omega

/-- **Georgii Example (5.20)(3) on `ℤ^d`, over the concrete boxes
`Δ_n = [-m(n+1), m(n+1))^d`.** Every cluster point of the periodic-boundary sequence
`μ_n = ν_n γ^{Φ̃^{Δ_n}}_{Δ_n}` is an `I`-invariant Gibbs measure for `Φ`, for any group `I` of
symmetries of `Φ` with `Θ ⊆ I ⊆ T_λ^{(m)} ∘ R ∘ Θ` and arbitrary boundary fields `ν_n`. -/
theorem mem_GP_and_measurePreserving_of_mapClusterPt_mPeriodicBox
    {Φ : Potential (Fin d → ℤ) E} [Potential.IsPotential Φ]
    [Potential.IsAbsolutelySummable Φ] (ν : Measure E) [IsProbabilityMeasure ν] (β : ℝ)
    {m : ℕ} (hm : 0 < m)
    {I : Set (Transformation (Fin d → ℤ) E)} (hΘ : ∀ t, shift E t ∈ I)
    (hIsites : ∀ τ ∈ I, ∃ r : (Fin d → ℤ) ≃+ (Fin d → ℤ), ∀ i, τ.sites i = r i + τ.sites 0)
    (hIper : ∀ τ ∈ I, ∀ i j : Fin d → ℤ, (∀ k, (m : ℤ) ∣ i k - j k) → τ.spin i = τ.spin j)
    (hIspin : ∀ τ ∈ I, ∀ i, MeasurePreserving (τ.spin i) ν ν)
    (hIΦ : ∀ τ ∈ I, Potential.map τ Φ = Φ)
    (νs : ℕ → ProbabilityMeasure ((Fin d → ℤ) → E))
    {μ : ProbabilityMeasure ((Fin d → ℤ) → E)}
    (hcp : haveI := fun n ↦ isPotential_periodicModification (Φ := Φ)
            (isTorusReduction_mPeriodicTorus hm n) isAnchor_lexAnchor (fun t ↦ hIΦ _ (hΘ t))
      haveI := fun n ↦ isAbsolutelySummable_periodicModification (Φ := Φ)
            (isTorusReduction_mPeriodicTorus hm n) isAnchor_lexAnchor (fun t ↦ hIΦ _ (hΘ t))
      MapClusterPt (WithSetwiseTopology.ofMeasure μ : WithLocalConvergence (Fin d → ℤ) E) atTop
      fun n ↦ WithSetwiseTopology.ofMeasure
        ((gibbsSpecificationOfAbsolutelySummable
          (Φ := periodicModification Φ (mPeriodicBox d m n) (mPeriodicTorus d m n) lexAnchor)
            ν β).bindPM (mPeriodicBox d m n) (νs n))) :
    μ ∈ GP (gibbsSpecificationOfAbsolutelySummable (Φ := Φ) ν β) ∧
      ∀ τ ∈ I, MeasurePreserving τ.toFun (μ : Measure ((Fin d → ℤ) → E)) μ :=
  mem_GP_and_measurePreserving_of_mapClusterPt_latticePeriodic ν β m
    (p := fun n ↦ 2 * (m * (n + 1) : ℤ)) (c := fun n _ ↦ -(m * (n + 1) : ℤ))
    (fun n ↦ by positivity) (fun n ↦ ⟨2 * ((n : ℤ) + 1), by ring⟩)
    (tendsto_mPeriodicBox_atTop hm) hΘ hIsites hIper hIspin hIΦ νs hcp

end Lattice

end MeasureTheory.GibbsMeasure

end

end

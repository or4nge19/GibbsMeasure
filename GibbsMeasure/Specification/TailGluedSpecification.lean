/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.Extremal
public import GibbsMeasure.Specification.GluedFamily
public import GibbsMeasure.Specification.Rescaling
public import GibbsMeasure.Specification.ZeroDirac

/-!
# Specifications whose Hamiltonians converge only on a tail event

Georgii builds two specifications this way: the Gaussian specification (13.18), and the Gibbsian
specification (20.5) of a Heisenberg potential over an unbounded state space.  In both cases the
formal Hamiltonians `H_Λ^Φ` are defined — the defining series converges absolutely — only for
boundary conditions `ω` in a **tail-measurable** set `Ω_*`, and the specification is *defined* to
be a Dirac mass off `Ω_*`:

`γ_Λ(A | ω) = Z_Λ(ω)⁻¹ λ_Λ(1_A e^{-H_Λ} | ω)` if `ω ∈ Ω_*`,  `δ_{0_Λ ω_{S∖Λ}}(A)` otherwise.

Georgii's justification is one sentence in each place ("just as in (13.18), the tail-measurability
of `Ω_*` implies that `γ^Φ` is indeed a specification"), and the analogous sentence for the Gibbs
measures ("in analogy to (13.19) we also have `μ(Ω_*) = 1` for all `μ ∈ 𝒢(Φ)`").  This file proves
both, once, for an arbitrary site set, an arbitrary tail event and an arbitrary density family.

## The two halves

Gluing two *specifications* along a tail event is Georgii's Remark (2.26) at a two-point parameter
space, i.e. `Specification.glued` of `GibbsMeasure.Specification.GluedFamily`; that is
`Specification.tailGlued` below.  It cannot be applied directly, because the Gibbsian branch is
*not* a specification: its kernels are undefined off `Ω_*`.

The missing half is therefore the observation that the branch may be **completed arbitrarily off
`Ω_*`**: a density family `ρ` satisfying Georgii's pre-modification identity (1.31) only for
boundary conditions in `Ω_*` becomes a genuine `Specification.IsPremodifier` once it is redefined
to be `1` (or any other pre-modification) off `Ω_*`.  The reason is exactly the tail-measurability
of `Ω_*`: `Ω_*` is `𝓕_{Λᶜ}`-measurable for every finite `Λ`, so the two configurations `ζ`, `η` of
the identity `ρ_{Λ₂}(ζ) ρ_{Λ₁}(η) = ρ_{Λ₁}(ζ) ρ_{Λ₂}(η)`, which agree off `Λ₁`, are either both in
`Ω_*` or both outside it.  The completed family has a genuine `Specification.lambdaSpecification`,
whose kernels coincide with the Gibbsian ones on `Ω_*` (the reference kernel `λ_Λ(· | ω)` is
carried by the fibre through `ω`, which lies in `Ω_*` when `ω` does), and gluing it to
`Specification.zeroDirac` along `Ω_*` gives Georgii's `γ^Φ`.

## Main declarations

* `Specification.tailGlued`: **Georgii's gluing pattern**, `γ_Λ(·|ω) = γ_Λ(·|ω)` on a tail event
  `Ω_*` and `γ'_Λ(·|ω)` off it.  Remark (2.26) at `X = Bool`.
* `Specification.IsPremodifierOn`: Georgii's Definition (1.31) restricted to a set of boundary
  conditions.
* `Specification.piecewiseDensity` and `Specification.isPremodifier_piecewiseDensity`: the
  completion described above.
* `Specification.gibbsOnTailSet`: **Georgii (13.18)/(20.5)** for an arbitrary tail event `Ω_*`,
  density family `ρ` and σ-finite finite non-zero a priori measure, with
  `gibbsOnTailSet_apply_of_mem` and `gibbsOnTailSet_apply_of_notMem` identifying its two branches.
* `Specification.measure_eq_one_of_isGibbsMeasure_tailGlued`: **Georgii (13.19)**, in the
  generality in which he uses it at (20.5): if the off-`Ω_*` branch is `Specification.zeroDirac`
  and the zero configuration lies in `Ω_*`, then `μ(Ω_*) = 1` for every Gibbs measure `μ` of the
  glued specification, *whatever* the on-`Ω_*` branch is.
  `Specification.measure_eq_one_of_isGibbsMeasure_gibbsOnTailSet` is its Gibbsian instance.

## Relation to `GibbsMeasure.Model.GaussianSpecification`

`Potential.gaussianGluedSpecification` there is the same construction as `tailGlued` at
`Ω₀ = Ω_J` — `Specification.glued` of the two-valued family `Potential.gaussianSpecificationBranch`
along the `Bool`-valued indicator of `Ω_J` — spelled out by hand rather than through `tailGlued`,
and stated only for `J` of finite row support, where `Ω_J = Ω` and the gluing is vacuous.  It is
*not* yet an instance of `gibbsOnTailSet`: that needs the Gaussian Boltzmann factor as a density
family on `Ω_J` for infinite-range `J`, the gap that file's module doc records.  Neither file is
changed here.

## Hypotheses, against Georgii

* Georgii's `λ ∈ 𝓜(E, ℰ)` is σ-finite; `gibbsOnTailSet` additionally needs `λ` **finite** and
  non-zero, because the completion of the density family off `Ω_*` by `1` has partition function
  `λ(E)^{|Λ|}` there, which must be non-zero and finite.  This is not a restriction in Georgii's
  §20, where `λ` is finite by standing assumption; and the general
  `isPremodifier_piecewiseDensity` and `isSigmaFiniteLambdaAdmissible_piecewiseDensity` take an
  arbitrary completing density, so a σ-finite `λ` only needs *some* admissible pre-modification to
  complete with.
* `measure_eq_one_of_isGibbsMeasure_tailGlued` needs `S` countable (to intersect the events
  `{σ_i = 0}`) and `{0}` measurable in `E`.  Georgii uses both silently.
-/

@[expose] public section

-- As in `GibbsMeasure.Specification.GluedFamily`: Lean 4.34's module system does not unfold
-- non-exposed mathlib defs (e.g. `Kernel.comap`) during `isDefEq`.
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory MeasureTheory.GibbsMeasure ProbabilityTheory Set
open scoped ENNReal

namespace Specification

variable {S E : Type*} [MeasurableSpace E]

/-! ### Gluing two specifications along a tail event -/

section TailGlued

variable (γ γ' : Specification S E)

/-- The two-valued family of specifications used to glue `γ` (on a tail event) to `γ'` (off it).
This is Georgii's Remark (2.26) at the two-point parameter space `Bool`. -/
noncomputable def boolBranch : Bool → Specification S E := fun b ↦ bif b then γ else γ'

@[simp] lemma boolBranch_true : boolBranch γ γ' true = γ := rfl

@[simp] lemma boolBranch_false : boolBranch γ γ' false = γ' := rfl

/-- Georgii's measurability condition (2.26)(ii) is automatic for a two-valued family. -/
lemma isMeasurableFamily_boolBranch : IsMeasurableFamily (boolBranch γ γ') := by
  classical
  intro Λ A hA
  have hg : Measurable[cylinderEvents ((Λ : Set S)ᶜ)] fun ω ↦ γ Λ ω A :=
    Kernel.measurable_coe _ hA
  have hz : Measurable[cylinderEvents ((Λ : Set S)ᶜ)] fun ω ↦ γ' Λ ω A :=
    Kernel.measurable_coe _ hA
  have hset : @MeasurableSet (Bool × (S → E))
      (@Prod.instMeasurableSpace Bool (S → E) _ (cylinderEvents ((Λ : Set S)ᶜ)))
      (Prod.fst ⁻¹' ({true} : Set Bool)) :=
    measurable_fst MeasurableSpace.measurableSet_top
  have hfn : (fun p : Bool × (S → E) ↦ boolBranch γ γ' p.1 Λ p.2 A) =
      (Prod.fst ⁻¹' ({true} : Set Bool)).piecewise (fun p ↦ γ Λ p.2 A) fun p ↦ γ' Λ p.2 A := by
    funext p
    obtain ⟨b, ω⟩ := p
    cases b <;> simp [boolBranch]
  rw [hfn]
  exact Measurable.piecewise hset (hg.comp measurable_snd) (hz.comp measurable_snd)

variable {γ γ'}

/-- The `Bool`-valued indicator of a tail event is tail measurable. -/
lemma measurable_tail_boolIndicator {Ω₀ : Set (S → E)}
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) :
    Measurable[tailSigmaAlgebra S E] Ω₀.boolIndicator := by
  refine @measurable_to_countable' Bool (S → E) _ _ (tailSigmaAlgebra S E) Ω₀.boolIndicator
    fun b ↦ ?_
  cases b with
  | true => rw [Set.preimage_boolIndicator_true]; exact hΩ₀
  | false => rw [Set.preimage_boolIndicator_false]; exact hΩ₀.compl

variable (γ γ')

/-- **Georgii's gluing pattern of (13.18) and (20.5).** Two specifications glued along a
tail-measurable set: `γ` for boundary conditions in `Ω₀`, `γ'` for the others.  This is
Remark (2.26) (`Specification.glued`) at the two-point parameter space. -/
noncomputable def tailGlued (Ω₀ : Set (S → E))
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) : Specification S E :=
  glued (boolBranch γ γ') Ω₀.boolIndicator (isMeasurableFamily_boolBranch γ γ')
    (measurable_tail_boolIndicator hΩ₀)

variable {Ω₀ : Set (S → E)} {hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀}

@[simp] lemma tailGlued_apply_of_mem (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) :
    tailGlued γ γ' Ω₀ hΩ₀ Λ ω = γ Λ ω := by
  rw [tailGlued, glued_apply, (Set.mem_iff_boolIndicator Ω₀ ω).1 hω, boolBranch_true]

@[simp] lemma tailGlued_apply_of_notMem (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    tailGlued γ γ' Ω₀ hΩ₀ Λ ω = γ' Λ ω := by
  rw [tailGlued, glued_apply, (Set.notMem_iff_boolIndicator Ω₀ ω).1 hω, boolBranch_false]

end TailGlued

/-! ### Georgii (13.19): the Gibbs measures live on the tail event

Georgii's argument, verbatim.  If `μ(Ω₀) < 1` then `ν = μ(· | Ω₀ᶜ)` is again a Gibbs measure,
because `Ω₀` is a tail event; `ν` lives off `Ω₀`, where the specification is the Dirac mass at the
configuration vanishing on the resampled volume, so `ν(σ_i = 0) = 1` for every site, hence
`ν = δ_0`; but `0 ∈ Ω₀` and `ν(Ω₀) = 0`. -/

section MeasureEqOne

variable [Zero E]

/-- **Georgii (13.19)**, in the generality in which he uses it at (20.5): if the off-`Ω₀` branch of
the gluing is the Dirac reference `Specification.zeroDirac` and the zero configuration belongs to
`Ω₀`, then every Gibbs measure of the glued specification is carried by `Ω₀` — whatever the
on-`Ω₀` branch is.  "The artificial part of the definition of `γ^Φ` has no effect on the associated
class of Gibbs measures." -/
theorem measure_eq_one_of_isGibbsMeasure_tailGlued [Countable S]
    (hE : MeasurableSet ({(0 : E)} : Set E)) (γ : Specification S E) {Ω₀ : Set (S → E)}
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (h0 : (0 : S → E) ∈ Ω₀)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (tailGlued γ (zeroDirac S E) Ω₀ hΩ₀).IsGibbsMeasure μ) :
    μ Ω₀ = 1 := by
  classical
  set δ : Specification S E := tailGlued γ (zeroDirac S E) Ω₀ hΩ₀ with hδ
  have hΩmeas : MeasurableSet Ω₀ :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀)
  by_contra hne
  -- `ν = μ(· | Ω₀ᶜ)` is again Gibbs, and lives off `Ω₀`.
  have hlt : μ Ω₀ < 1 := lt_of_le_of_ne prob_le_one hne
  have hc0 : μ Ω₀ᶜ ≠ 0 := by
    rw [prob_compl_eq_one_sub hΩmeas]
    exact (tsub_pos_of_lt hlt).ne'
  set ν : Measure (S → E) := μ[|Ω₀ᶜ] with hν
  have hνprob : IsProbabilityMeasure ν := cond_isProbabilityMeasure hc0
  have hνgibbs : δ.IsGibbsMeasure ν :=
    isGibbsMeasure_cond_of_tail (γ := δ) μ hμ hΩ₀.compl hc0
  have hνc : ν Ω₀ᶜ = 1 := cond_apply_self hc0 (measure_ne_top _ _)
  have hνΩ : ν Ω₀ = 0 := by
    have h : ν (Ω₀ᶜ)ᶜ = 1 - ν Ω₀ᶜ := prob_compl_eq_one_sub (μ := ν) hΩmeas.compl
    rw [compl_compl, hνc, tsub_self] at h
    exact h
  have hAmeas : ∀ i : S, MeasurableSet {σ : S → E | σ i = 0} := by
    intro i
    have h : {σ : S → E | σ i = 0} = (fun σ : S → E ↦ σ i) ⁻¹' ({0} : Set E) := by
      ext σ; simp
    rw [h]
    exact (measurable_pi_apply i) hE
  -- Off `Ω₀` the kernels are Dirac masses at configurations vanishing on the resampled volume.
  have hsite : ∀ i : S, ν {σ : S → E | σ i = 0} = 1 := by
    intro i
    have hbind : ν.bind (δ ({i} : Finset S)) = ν :=
      (isGibbsMeasure_iff_forall_bind_eq_of_prob (γ := δ)).1 hνgibbs _
    have hkey : ν.bind (δ ({i} : Finset S)) {σ : S → E | σ i = 0} = ν {σ : S → E | σ i = 0} := by
      rw [hbind]
    rw [Measure.bind_apply (hAmeas i)
      (((δ ({i} : Finset S)).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable)] at hkey
    have hae : ∀ᵐ ω ∂ν, δ ({i} : Finset S) ω {σ : S → E | σ i = 0} = 1 := by
      have hcompl : ∀ᵐ ω ∂ν, ω ∈ Ω₀ᶜ := by
        rw [MeasureTheory.ae_iff]
        have hsub : {ω : S → E | ¬ ω ∈ Ω₀ᶜ} = Ω₀ := by ext ω; simp
        rw [hsub, hνΩ]
      filter_upwards [hcompl] with ω hω
      rw [hδ, tailGlued_apply_of_notMem _ _ _ hω, zeroDirac_apply,
        Measure.dirac_apply' _ (hAmeas i), Set.indicator_of_mem]
      · rfl
      · exact juxt_apply_of_mem (by simp) (0 : ({i} : Finset S) → E)
    rw [lintegral_congr_ae hae, lintegral_one, measure_univ] at hkey
    exact hkey.symm
  -- Hence `ν = δ_0`; but `0 ∈ Ω₀` and `ν(Ω₀) = 0`.
  have hzero : ν {σ : S → E | ∀ i, σ i = 0} = 1 := by
    have hinter : {σ : S → E | ∀ i, σ i = 0} = ⋂ i : S, {σ : S → E | σ i = 0} := by
      ext σ; simp
    have hc : ν (⋂ i : S, {σ : S → E | σ i = 0})ᶜ = 0 := by
      rw [Set.compl_iInter]
      refine le_antisymm ((measure_iUnion_le _).trans ?_) (by simp)
      have hzeroi : ∀ i : S, ν {σ : S → E | σ i = 0}ᶜ = 0 := fun i ↦ by
        rw [prob_compl_eq_one_sub (hAmeas i), hsite i, tsub_self]
      simp [hzeroi]
    have htot := measure_add_measure_compl (μ := ν) (MeasurableSet.iInter hAmeas)
    rw [hc, add_zero, measure_univ] at htot
    rw [hinter]
    exact htot
  have hsub : {σ : S → E | ∀ i, σ i = 0} ⊆ Ω₀ := by
    intro σ hσ
    have : σ = (0 : S → E) := funext fun i ↦ hσ i
    rw [this]
    exact h0
  have : (1 : ℝ≥0∞) ≤ 0 := hzero ▸ hνΩ ▸ measure_mono hsub
  simp at this

end MeasureEqOne

/-! ### Density families defined only on a tail event -/

section PremodifierOn

variable {ρ ρ' : Finset S → (S → E) → ℝ≥0∞}

variable (ρ) in
/-- **Georgii's pre-modification identity (1.31), restricted to a set of boundary conditions.**
This is what a Gibbsian density family `ρ_Λ = e^{-H_Λ^Φ}` satisfies when the Hamiltonians `H_Λ^Φ`
are only defined on a set `Ω₀` of configurations — for instance the convergence set `Ω_J` of
(13.9) or the set `Ω_*` of slowly increasing configurations of §20.1. -/
structure IsPremodifierOn (Ω₀ : Set (S → E)) : Prop where
  /-- Each density is measurable (on all of `Ω`, not merely on `Ω₀`). -/
  measurable Λ : Measurable (ρ Λ)
  /-- Georgii's identity, for boundary conditions in `Ω₀`. -/
  comm_of_subset ⦃Λ₁ Λ₂ : Finset S⦄ ⦃ζ η : S → E⦄ (hΛ : Λ₁ ⊆ Λ₂) (hζ : ζ ∈ Ω₀) (hη : η ∈ Ω₀)
    (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) : ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η

/-- A pre-modification is a pre-modification on every set of boundary conditions. -/
lemma IsPremodifier.isPremodifierOn (hρ : IsPremodifier (S := S) (E := E) ρ)
    (Ω₀ : Set (S → E)) : IsPremodifierOn ρ Ω₀ where
  measurable := hρ.measurable
  comm_of_subset _ _ _ _ hΛ _ _ hrestrict := hρ.comm_of_subset hΛ hrestrict

/-- The constant density family `1` is a pre-modification on every set. -/
lemma isPremodifierOn_one (Ω₀ : Set (S → E)) :
    IsPremodifierOn (S := S) (E := E) 1 Ω₀ where
  measurable _ := measurable_one
  comm_of_subset _ _ _ _ _ _ _ _ := rfl

open scoped Classical in
/-- The density family which is `ρ` on `Ω₀` and `ρ'` off it.  Completing a Gibbsian density family
off the set where its Hamiltonians converge is what makes Georgii's (13.18)/(20.5) a gluing of two
genuine specifications. -/
noncomputable def piecewiseDensity (Ω₀ : Set (S → E)) (ρ ρ' : Finset S → (S → E) → ℝ≥0∞) :
    Finset S → (S → E) → ℝ≥0∞ :=
  fun Λ ↦ Ω₀.piecewise (ρ Λ) (ρ' Λ)

variable {Ω₀ : Set (S → E)}

omit [MeasurableSpace E] in
@[simp] lemma piecewiseDensity_of_mem (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) :
    piecewiseDensity Ω₀ ρ ρ' Λ ω = ρ Λ ω := by
  classical simpa [piecewiseDensity] using Set.piecewise_eq_of_mem Ω₀ (ρ Λ) (ρ' Λ) hω

omit [MeasurableSpace E] in
@[simp] lemma piecewiseDensity_of_notMem (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    piecewiseDensity Ω₀ ρ ρ' Λ ω = ρ' Λ ω := by
  classical simpa [piecewiseDensity] using Set.piecewise_eq_of_notMem Ω₀ (ρ Λ) (ρ' Λ) hω

/-- **The completion of a density family off a tail event is a pre-modification.**  Georgii's
"just as in (13.18), the tail-measurability of `Ω_*` implies that `γ^Φ` is indeed a specification".
The point is that the two configurations of Georgii's identity (1.31) agree off a finite set, so
they lie on the same side of a tail event. -/
theorem isPremodifier_piecewiseDensity (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀)
    (hρ : IsPremodifierOn ρ Ω₀) (hρ' : IsPremodifierOn ρ' Ω₀ᶜ) :
    IsPremodifier (S := S) (E := E) (piecewiseDensity Ω₀ ρ ρ') where
  measurable Λ := by
    classical
    have hmeas : MeasurableSet Ω₀ :=
      cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀)
    exact Measurable.piecewise hmeas (hρ.measurable Λ) (hρ'.measurable Λ)
  comm_of_subset Λ₁ Λ₂ ζ η hΛ hrestrict := by
    have hiff : ζ ∈ Ω₀ ↔ η ∈ Ω₀ :=
      mem_congr_of_measurableSet_cylinderEvents
        (measurableSet_cylinderEvents_compl_of_measurableSet_tail Λ₁ hΩ₀)
        fun i hi ↦ hrestrict i (by simpa using hi)
    by_cases hζ : ζ ∈ Ω₀
    · have hη : η ∈ Ω₀ := hiff.1 hζ
      rw [piecewiseDensity_of_mem _ hζ, piecewiseDensity_of_mem _ hη,
        piecewiseDensity_of_mem _ hζ, piecewiseDensity_of_mem _ hη]
      exact hρ.comm_of_subset hΛ hζ hη hrestrict
    · have hη : η ∉ Ω₀ := fun hc ↦ hζ (hiff.2 hc)
      rw [piecewiseDensity_of_notMem _ hζ, piecewiseDensity_of_notMem _ hη,
        piecewiseDensity_of_notMem _ hζ, piecewiseDensity_of_notMem _ hη]
      exact hρ'.comm_of_subset hΛ hζ hη hrestrict

/-! #### The partition function of a completed density family -/

variable {ν : Measure E} [SigmaFinite ν]

/-- On a tail event, the reference kernel `λ_Λ(· | ω)` is carried by configurations lying on the
same side of the event as `ω`, so the completed density family has the same partition function as
the original one. -/
lemma sigmaFiniteLambdaZ_piecewiseDensity_of_mem
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hρ' : ∀ Λ, Measurable (ρ' Λ)) (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν (piecewiseDensity Ω₀ ρ ρ') Λ ω
      = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω := by
  classical
  have hmeasΩ : MeasurableSet Ω₀ :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀)
  have hmeas : Measurable (piecewiseDensity Ω₀ ρ ρ' Λ) :=
    Measurable.piecewise hmeasΩ (hρ Λ) (hρ' Λ)
  rw [sigmaFiniteLambdaZ, sigmaFiniteLambdaZ, sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hmeas Measurable.juxt, lintegral_map (hρ Λ) Measurable.juxt]
  refine lintegral_congr fun ζ ↦ ?_
  have hmem : juxt (Λ : Set S) ω ζ ∈ Ω₀ :=
    (mem_congr_of_measurableSet_cylinderEvents
      (measurableSet_cylinderEvents_compl_of_measurableSet_tail Λ hΩ₀)
      fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi) ζ).2 hω
  exact piecewiseDensity_of_mem _ hmem

/-- On a tail event, the completed density family may be replaced by the original one inside every
set integral against the reference kernel. -/
lemma setLIntegral_piecewiseDensity_of_mem
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hρ' : ∀ Λ, Measurable (ρ' Λ)) (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    ∫⁻ x in A, piecewiseDensity Ω₀ ρ ρ' Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω)
      = ∫⁻ x in A, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω) := by
  classical
  have hmeasΩ : MeasurableSet Ω₀ :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀)
  have hmeas : Measurable (piecewiseDensity Ω₀ ρ ρ' Λ) :=
    Measurable.piecewise hmeasΩ (hρ Λ) (hρ' Λ)
  rw [setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt _ hmeas hA ω,
    setLIntegral_sigmaFiniteLambdaFun_eq_setLIntegral_juxt _ (hρ Λ) hA ω]
  refine lintegral_congr fun ζ ↦ ?_
  have hmem : juxt (Λ : Set S) ω ζ ∈ Ω₀ :=
    (mem_congr_of_measurableSet_cylinderEvents
      (measurableSet_cylinderEvents_compl_of_measurableSet_tail Λ hΩ₀)
      fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi) ζ).2 hω
  exact piecewiseDensity_of_mem _ hmem

/-- Off the tail event, the completed density family has the partition function of the completing
family. -/
lemma sigmaFiniteLambdaZ_piecewiseDensity_of_notMem
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hρ' : ∀ Λ, Measurable (ρ' Λ)) (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν (piecewiseDensity Ω₀ ρ ρ') Λ ω
      = sigmaFiniteLambdaZ (S := S) (E := E) ν ρ' Λ ω := by
  classical
  have hmeasΩ : MeasurableSet Ω₀ :=
    cylinderEvents_le_pi _ (measurableSet_cylinderEvents_compl_of_measurableSet_tail ∅ hΩ₀)
  have hmeas : Measurable (piecewiseDensity Ω₀ ρ ρ' Λ) :=
    Measurable.piecewise hmeasΩ (hρ Λ) (hρ' Λ)
  rw [sigmaFiniteLambdaZ, sigmaFiniteLambdaZ, sigmaFiniteLambdaFun_apply_eq_map,
    lintegral_map hmeas Measurable.juxt, lintegral_map (hρ' Λ) Measurable.juxt]
  refine lintegral_congr fun ζ ↦ ?_
  have hmem : juxt (Λ : Set S) ω ζ ∉ Ω₀ := fun hc ↦ hω
    ((mem_congr_of_measurableSet_cylinderEvents
      (measurableSet_cylinderEvents_compl_of_measurableSet_tail Λ hΩ₀)
      fun i hi ↦ juxt_apply_of_not_mem (by simpa using hi) ζ).1 hc)
  exact piecewiseDensity_of_notMem _ hmem

/-- The completed density family is admissible as soon as the two halves are admissible on their
own sides. -/
theorem isSigmaFiniteLambdaAdmissible_piecewiseDensity
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hρ' : ∀ Λ, Measurable (ρ' Λ))
    (hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ 0 ∧
        sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ ⊤)
    (hZ' : ∀ (Λ : Finset S) (ω : S → E), ω ∉ Ω₀ →
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ' Λ ω ≠ 0 ∧
        sigmaFiniteLambdaZ (S := S) (E := E) ν ρ' Λ ω ≠ ⊤) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (piecewiseDensity Ω₀ ρ ρ') := by
  intro Λ ω
  by_cases hω : ω ∈ Ω₀
  · rw [sigmaFiniteLambdaZ_piecewiseDensity_of_mem hΩ₀ hρ hρ' Λ hω]; exact hZ Λ ω hω
  · rw [sigmaFiniteLambdaZ_piecewiseDensity_of_notMem hΩ₀ hρ hρ' Λ hω]; exact hZ' Λ ω hω

/-- The total mass of the reference kernel is `λ(E)^{|Λ|}`. -/
lemma sigmaFiniteLambdaFun_univ (Λ : Finset S) (ω : S → E) :
    sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω Set.univ = ν Set.univ ^ Λ.card := by
  rw [sigmaFiniteLambdaFun_apply_eq_map, Measure.map_apply Measurable.juxt MeasurableSet.univ]
  simp [Measure.pi_univ]

/-- The partition function of the constant density family `1` is `λ(E)^{|Λ|}`. -/
lemma sigmaFiniteLambdaZ_one (Λ : Finset S) (ω : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν 1 Λ ω = ν Set.univ ^ Λ.card := by
  have h : sigmaFiniteLambdaZ (S := S) (E := E) ν 1 Λ ω
      = sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω Set.univ := by
    simp [sigmaFiniteLambdaZ]
  rw [h, sigmaFiniteLambdaFun_univ]

/-- **The partition function of a strictly positive density family is non-zero**, for a non-zero
a priori measure: Georgii's `Z_Λ^Φ(ω) > 0`, which for a Gibbsian `ρ_Λ = e^{-H_Λ}` needs nothing
beyond `λ ≠ 0`. -/
lemma sigmaFiniteLambdaZ_ne_zero_of_pos [NeZero ν] (Λ : Finset S)
    (hmeas : Measurable (ρ Λ)) (hpos : ∀ ω, 0 < ρ Λ ω) (ω : S → E) :
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ 0 := by
  rw [sigmaFiniteLambdaZ, ← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
  have hsupp : Function.support (ρ Λ) = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ (hpos x).ne'
  rw [hsupp, sigmaFiniteLambdaFun_univ, pos_iff_ne_zero]
  exact pow_ne_zero _ (univ_ne_zero_of_neZero ν)

end PremodifierOn

/-! ### Georgii (13.18)/(20.5): the Gibbsian specification of a density family on a tail event -/

section GibbsOnTailSet

variable {ν : Measure E} [IsFiniteMeasure ν] [NeZero ν] {ρ : Finset S → (S → E) → ℝ≥0∞}
  {Ω₀ : Set (S → E)}

/-- Completing a density family off a tail event by `1` is admissible, for a finite non-zero a
priori measure, as soon as it is admissible on the tail event itself. -/
theorem isSigmaFiniteLambdaAdmissible_piecewiseDensity_one
    (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀) (hρ : ∀ Λ, Measurable (ρ Λ))
    (hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ 0 ∧
        sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ ⊤) :
    IsSigmaFiniteLambdaAdmissible (S := S) (E := E) ν (piecewiseDensity Ω₀ ρ 1) := by
  refine isSigmaFiniteLambdaAdmissible_piecewiseDensity hΩ₀ hρ (fun _ ↦ measurable_const) hZ
    fun Λ ω _ ↦ ?_
  rw [sigmaFiniteLambdaZ_one]
  exact ⟨pow_ne_zero _ (univ_ne_zero_of_neZero ν), by
    simp [ENNReal.pow_eq_top_iff, measure_ne_top ν Set.univ]⟩

variable (ν ρ Ω₀)

/-- **Georgii's Definition (13.18), and (20.5).**  The specification attached to a density family
`ρ_Λ = e^{-H_Λ^Φ}` whose pre-modification identity holds only on a tail-measurable set `Ω₀` and
whose partition functions are finite and non-zero there: the Gibbsian kernel on `Ω₀`, the Dirac
mass at `0_Λ ω_{S∖Λ}` off it. -/
noncomputable def gibbsOnTailSet (hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀)
    [Zero E] (hρ : IsPremodifierOn ρ Ω₀)
    (hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ 0 ∧
        sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ ⊤) :
    Specification S E :=
  tailGlued
    (lambdaSpecification (S := S) (E := E) ν (piecewiseDensity Ω₀ ρ 1)
      (isPremodifier_piecewiseDensity hΩ₀ hρ (isPremodifierOn_one _))
      (isSigmaFiniteLambdaAdmissible_piecewiseDensity_one hΩ₀ hρ.measurable hZ))
    (zeroDirac S E) Ω₀ hΩ₀

variable {ν ρ Ω₀}
variable {hΩ₀ : MeasurableSet[tailSigmaAlgebra S E] Ω₀} [Zero E] {hρ : IsPremodifierOn ρ Ω₀}
  {hZ : ∀ (Λ : Finset S) (ω : S → E), ω ∈ Ω₀ →
    sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ 0 ∧
      sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω ≠ ⊤}

/-- **The Gibbsian branch of (20.5).**  For a boundary condition in `Ω₀`, the kernel is Georgii's
`Z_Λ(ω)⁻¹ λ_Λ(1_A ρ_Λ | ω)`; the completion of `ρ` off `Ω₀` has disappeared, because `λ_Λ(· | ω)`
is carried by the fibre through `ω`, which lies in `Ω₀`. -/
theorem gibbsOnTailSet_apply_of_mem (Λ : Finset S) {ω : S → E} (hω : ω ∈ Ω₀) {A : Set (S → E)}
    (hA : MeasurableSet A) :
    gibbsOnTailSet ν ρ Ω₀ hΩ₀ hρ hZ Λ ω A
      = (sigmaFiniteLambdaZ (S := S) (E := E) ν ρ Λ ω)⁻¹
        * ∫⁻ x in A, ρ Λ x ∂(sigmaFiniteLambdaFun (S := S) (E := E) ν Λ ω) := by
  classical
  rw [gibbsOnTailSet, tailGlued_apply_of_mem _ _ _ hω, lambdaSpecification_apply,
    withDensity_sigmaFinitePremodifierNorm_apply _
      (isPremodifier_piecewiseDensity hΩ₀ hρ (isPremodifierOn_one _)) hA,
    sigmaFiniteLambdaZ_piecewiseDensity_of_mem (ν := ν) (ρ := ρ)
      (ρ' := (1 : Finset S → (S → E) → ℝ≥0∞)) hΩ₀ hρ.measurable (fun _ ↦ measurable_one) Λ hω]
  congr 1
  exact setLIntegral_piecewiseDensity_of_mem hΩ₀ hρ.measurable (fun _ ↦ measurable_one) Λ hω hA

/-- **The artificial branch of (20.5).**  Off `Ω₀` the kernel is the Dirac mass at the
configuration vanishing on `Λ` and agreeing with `ω` outside. -/
theorem gibbsOnTailSet_apply_of_notMem (Λ : Finset S) {ω : S → E} (hω : ω ∉ Ω₀) :
    gibbsOnTailSet ν ρ Ω₀ hΩ₀ hρ hZ Λ ω = Measure.dirac (juxt (Λ : Set S) ω (0 : Λ → E)) := by
  rw [gibbsOnTailSet, tailGlued_apply_of_notMem _ _ _ hω, zeroDirac_apply]

/-- **Georgii (13.19), for (20.5)**: `μ(Ω_*) = 1` for every `μ ∈ 𝒢(γ^Φ)`. -/
theorem measure_eq_one_of_isGibbsMeasure_gibbsOnTailSet [Countable S]
    (hE : MeasurableSet ({(0 : E)} : Set E)) (h0 : (0 : S → E) ∈ Ω₀)
    {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    (hμ : (gibbsOnTailSet ν ρ Ω₀ hΩ₀ hρ hZ).IsGibbsMeasure μ) :
    μ Ω₀ = 1 :=
  measure_eq_one_of_isGibbsMeasure_tailGlued hE _ hΩ₀ h0 hμ

end GibbsOnTailSet

end Specification

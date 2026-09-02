/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.AbstractPAKernel
public import GibbsMeasure.Specification.PAKernel
public import GibbsMeasure.Specification.ChoquetLaw
public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.CDF

/-!
# Georgii, Proposition (7.25): a `(G(γ), 𝓣)`-kernel

For a specification `γ` on `S → E` (`S` countable, `E` standard Borel) with `G(γ) ≠ ∅`, we build
a probability kernel `gibbsKernel γ ν₀ : Kernel[𝓣] (S → E) (S → E)` depending only on `γ` and on a
fixed `ν₀ ∈ G(γ)` (Georgii's fallback value off the good tail set), and not on the measure it
disintegrates: it is a version of `μ(· | 𝓣)` for every `μ ∈ G(γ)` (Definition (7.21)), with all
its values in `G(γ)`.

The construction exists once, for an `AbstractSpecification` in the abstract setting of Georgii's
Remark (7.13) (`GibbsMeasure/Specification/AbstractPAKernel.lean`), parameterised by a monotone
cofinal sequence of indices. This file only specialises it along `Specification.toAbstract` at
the exhaustion `exhaustionVolumes`: every definition below is definitionally the abstract one,
and every lemma is a one-line instance of its abstract counterpart. Concretely, along the
exhaustion, Lévy's downward theorem (`limUnder_condExp_ae_eq_condExp_iInf`) and the DLR equation
identify `lim_n γ_{Λ_n}(A | ·)` with `μ(A | 𝓣)`; applying this to the half-lines
`{embeddingReal (S → E) ≤ q}`, `q : ℚ`, gives a tail-measurable rational CDF, which
`stieltjesOfMeasurableRat` turns into a kernel to `ℝ`, pulled back to `S → E` by `comapRight`.
For a Gibbs measure `μ` this kernel is `μ`-a.e. equal to `tailKernel μ = condExpKernel μ 𝓣`,
which is a.e. Gibbs by the tower property; the remaining bad tail set is sent to `ν₀ ∈ G(γ)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory.GibbsMeasure

variable {S E : Type*} [MeasurableSpace E] [Countable S]

set_option warn.classDefReducibility false in
/-- The decreasing sequence of outside-volume σ-algebras along the exhaustion
`exhaustionVolumes`. -/
noncomputable def exhaustionFiltration (S E : Type*) [MeasurableSpace E] [Countable S]
    (n : ℕ) : MeasurableSpace (S → E) :=
  cylinderEvents (X := fun _ : S ↦ E) ((exhaustionVolumes (S := S) n : Set S)ᶜ)

lemma antitone_exhaustionFiltration : Antitone (exhaustionFiltration S E) := by
  intro m n hmn
  exact cylinderEvents_mono (X := fun _ : S ↦ E)
    (compl_subset_compl.2 (Finset.coe_subset.2 (exhaustionVolumes_monotone hmn)))

lemma exhaustionFiltration_le_pi (n : ℕ) :
    exhaustionFiltration S E n ≤ MeasurableSpace.pi :=
  cylinderEvents_le_pi

lemma iInf_exhaustionFiltration :
    (⨅ n, exhaustionFiltration S E n) = (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) :=
  (tailSigmaAlgebra_eq_iInf_exhaustion (S := S) (E := E)).symm

/-! ### The abstract specification of `γ`, along the exhaustion

`Specification.toAbstract` realises `γ` as an `AbstractSpecification (S → E) (Finset S)` with
`toAbstract.sub Λ = 𝓕_{Λᶜ}`, `toAbstract.ker Λ = γ Λ` and `toAbstract.tail = 𝓣`, all by `rfl`;
the exhaustion `exhaustionVolumes` is a monotone cofinal sequence in `Finset S`. The following
bridges identify `G γ` with the abstract invariant measures. -/

section ToAbstract

variable {γ : Specification S E} {μ : Measure (S → E)}

omit [Countable S] in
/-- The invariant measures of `γ.toAbstract` are exactly the Gibbs probability measures `G γ`. -/
lemma _root_.Specification.toAbstract_invariant_eq_G (γ : Specification S E) :
    γ.toAbstract.invariant = G γ :=
  γ.toAbstract_invariant

omit [Countable S] in
lemma mem_toAbstract_invariant_of_isGibbsMeasure [IsProbabilityMeasure μ]
    (hμ : γ.IsGibbsMeasure μ) : μ ∈ γ.toAbstract.invariant :=
  (γ.mem_toAbstract_invariant_iff μ).2 ⟨‹_›, hμ⟩

omit [Countable S] in
lemma mem_toAbstract_invariant_of_mem_G {ν : Measure (S → E)} (hν : ν ∈ G γ) :
    ν ∈ γ.toAbstract.invariant :=
  (γ.mem_toAbstract_invariant_iff ν).2 hν

end ToAbstract

section Levy

variable {γ : Specification S E} {μ : Measure (S → E)}

/-- The DLR equation along the exhaustion: for a Gibbs measure, `γ_{Λ_n}(A | ·)` is a version of
`μ(A | 𝓕_{Λ_nᶜ})`. -/
lemma condExp_exhaustionFiltration_ae_eq (hμ : γ.IsGibbsMeasure μ) {A : Set (S → E)}
    (hA : MeasurableSet A) (n : ℕ) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | exhaustionFiltration S E n] =ᵐ[μ]
      fun ω ↦ (γ (exhaustionVolumes n) ω A).toReal :=
  @Kernel.IsCondExp.condExp_ae_eq_kernel_apply _ _ _ _ _ (hμ _) A hA

/-- Lévy's downward theorem along the exhaustion: `lim_n γ_{Λ_n}(A | ·)` is a version of
`μ(A | 𝓣)` for every Gibbs measure `μ`. -/
lemma limUnder_ae_eq_condExp_tail [IsProbabilityMeasure μ] (hμ : γ.IsGibbsMeasure μ)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    (fun ω ↦ limUnder atTop fun n ↦ (γ (exhaustionVolumes n) ω A).toReal) =ᵐ[μ]
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
  AbstractSpecification.tailLimit_ae_eq_condExp exhaustionVolumes_monotone
    exhaustionVolumes_cofinal (mem_toAbstract_invariant_of_isGibbsMeasure hμ) hA

end Levy

section TailLimit

variable (γ : Specification S E)

/-- The tail limit `lim_n γ_{Λ_n}(A | ω)` along the exhaustion (as a `limUnder`, hence defined
everywhere). -/
noncomputable def tailLimit (A : Set (S → E)) (ω : S → E) : ℝ :=
  γ.toAbstract.tailLimit exhaustionVolumes A ω

lemma measurable_tailLimit {A : Set (S → E)} (hA : MeasurableSet A) :
    Measurable[@tailSigmaAlgebra S E _] (tailLimit γ A) :=
  γ.toAbstract.measurable_tailLimit exhaustionVolumes exhaustionVolumes_monotone
    exhaustionVolumes_cofinal hA

lemma tailLimit_ae_eq_condExp {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {γ : Specification S E}
    (hμ : γ.IsGibbsMeasure μ) {A : Set (S → E)} (hA : MeasurableSet A) :
    tailLimit γ A =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
  AbstractSpecification.tailLimit_ae_eq_condExp exhaustionVolumes_monotone
    exhaustionVolumes_cofinal (mem_toAbstract_invariant_of_isGibbsMeasure hμ) hA

end TailLimit

section RatCDF

variable [StandardBorelSpace E] (γ : Specification S E)

/-- The rational tail CDF `ω ↦ (q ↦ lim_n γ_{Λ_n}({e ≤ q} | ω))`, where
`e = embeddingReal (S → E)`. -/
noncomputable def tailRatCDF (ω : S → E) (q : ℚ) : ℝ :=
  γ.toAbstract.tailRatCDF exhaustionVolumes ω q

lemma measurable_tailRatCDF : Measurable[@tailSigmaAlgebra S E _] (tailRatCDF γ) :=
  γ.toAbstract.measurable_tailRatCDF exhaustionVolumes exhaustionVolumes_monotone
    exhaustionVolumes_cofinal

/-- The tail-measurable kernel to `ℝ` obtained from the rational tail CDF. -/
noncomputable def tailRealKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) ℝ :=
  γ.toAbstract.tailRealKernel exhaustionVolumes exhaustionVolumes_monotone
    exhaustionVolumes_cofinal

lemma tailRealKernel_apply (ω : S → E) :
    tailRealKernel γ ω =
      (@stieltjesOfMeasurableRat (S → E) (@tailSigmaAlgebra S E _) (tailRatCDF γ)
        (measurable_tailRatCDF γ) ω).measure := rfl

instance : IsMarkovKernel (tailRealKernel γ) := by
  unfold tailRealKernel; infer_instance

lemma tailRealKernel_apply_Iic {ω : S → E} (hω : IsRatStieltjesPoint (tailRatCDF γ) ω) (q : ℚ) :
    tailRealKernel γ ω (Iic (q : ℝ)) = ENNReal.ofReal (tailRatCDF γ ω q) :=
  kernelOfMeasurableRat_apply_Iic _ _ hω q

end RatCDF

section Identification

variable [StandardBorelSpace E] {γ : Specification S E} (μ : Measure (S → E))
  [IsProbabilityMeasure μ]

lemma tailKernel_real_ae_eq_condExp {A : Set (S → E)} (hA : MeasurableSet A) :
    (fun ω ↦ (tailKernel μ ω).real A) =ᵐ[μ]
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
  condExpKernel_ae_eq_condExp (μ := μ) (tailSigmaAlgebra_le_pi (S := S) (E := E)) hA

lemma ae_forall_tailRatCDF_eq (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, tailRatCDF γ ω q =
      ((tailKernel μ ω).map (embeddingReal (S → E))).real (Iic (q : ℝ)) :=
  AbstractSpecification.ae_forall_tailRatCDF_eq μ exhaustionVolumes_monotone
    exhaustionVolumes_cofinal (mem_toAbstract_invariant_of_isGibbsMeasure hμ)

lemma ae_tailRealKernel_eq_map (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, tailRealKernel γ ω = (tailKernel μ ω).map (embeddingReal (S → E)) :=
  AbstractSpecification.ae_tailRealKernel_eq_map μ exhaustionVolumes_monotone
    exhaustionVolumes_cofinal (mem_toAbstract_invariant_of_isGibbsMeasure hμ)

/-- Tower property: the tail conditional measures of a Gibbs measure are a.e. fixed by `γ Λ`
on any measurable set. -/
lemma ae_bind_tailKernel_apply_eq (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) {B : Set (S → E)}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, (tailKernel μ ω).bind (γ Λ) B = tailKernel μ ω B :=
  AbstractSpecification.ae_bind_tailCondKernel_apply_eq (γ := γ.toAbstract)
    (mem_toAbstract_invariant_of_isGibbsMeasure hμ) Λ hB

lemma ae_isGibbsCore_tailKernel (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, IsGibbsCore γ (tailKernel μ ω) :=
  AbstractSpecification.ae_isInvariantCore_tailCondKernel (γ := γ.toAbstract)
    (mem_toAbstract_invariant_of_isGibbsMeasure hμ)

end Identification

section GibbsKernel

variable [StandardBorelSpace E] (γ : Specification S E) (ν₀ : Measure (S → E))

/-- The tail event on which `tailRealKernel γ` is carried by the range of `embeddingReal`. -/
def rangeSet : Set (S → E) :=
  γ.toAbstract.rangeSet exhaustionVolumes exhaustionVolumes_monotone exhaustionVolumes_cofinal

lemma measurableSet_rangeSet : MeasurableSet[@tailSigmaAlgebra S E _] (rangeSet γ) :=
  γ.toAbstract.measurableSet_rangeSet exhaustionVolumes exhaustionVolumes_monotone
    exhaustionVolumes_cofinal

open Classical in
/-- `tailRealKernel γ`, replaced off `rangeSet γ` by the pushforward of `ν₀`. -/
noncomputable def tailRealKernel' : Kernel[@tailSigmaAlgebra S E _] (S → E) ℝ :=
  AbstractSpecification.tailRealKernel' γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀

lemma tailRealKernel'_apply_range [IsProbabilityMeasure ν₀] (ω : S → E) :
    tailRealKernel' γ ν₀ ω (range (embeddingReal (S → E))) = 1 :=
  AbstractSpecification.tailRealKernel'_apply_range γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀ ω

/-- The candidate `(G(γ), 𝓣)`-kernel, before correction on the bad tail set. -/
noncomputable def gibbsKernelAux : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  AbstractSpecification.paKernelAux γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (gibbsKernelAux γ ν₀) := by
  unfold gibbsKernelAux; infer_instance

/-- The tail event on which `gibbsKernelAux γ ν₀` is a Gibbs measure. -/
def gibbsSet : Set (S → E) :=
  AbstractSpecification.invariantSet γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀

lemma measurableSet_gibbsSet : MeasurableSet[@tailSigmaAlgebra S E _] (gibbsSet γ ν₀) :=
  AbstractSpecification.measurableSet_invariantSet γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀

open Classical in
/-- Georgii (7.25): the `μ`-independent `(G(γ), 𝓣)`-kernel, equal to `ν₀` off `gibbsSet γ ν₀`. -/
noncomputable def gibbsKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  AbstractSpecification.paKernel γ.toAbstract exhaustionVolumes
    exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (gibbsKernel γ ν₀) := by
  unfold gibbsKernel; infer_instance

lemma gibbsKernel_mem_G (hν₀ : ν₀ ∈ G γ) (ω : S → E) : gibbsKernel γ ν₀ ω ∈ G γ :=
  γ.toAbstract_invariant_eq_G ▸
    AbstractSpecification.paKernel_mem_invariant γ.toAbstract exhaustionVolumes
      exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀
      (mem_toAbstract_invariant_of_mem_G hν₀) ω

variable {μ : Measure (S → E)} [IsProbabilityMeasure μ]

lemma ae_gibbsKernel_eq_tailKernel {γ : Specification S E} (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, gibbsKernel γ ν₀ ω = tailKernel μ ω :=
  AbstractSpecification.ae_paKernel_eq_tailCondKernel
    (mem_toAbstract_invariant_of_isGibbsMeasure hμ)

/-- Georgii (7.21)(i) for `gibbsKernel`: it is a version of `μ(· | 𝓣)` for every Gibbs `μ`. -/
theorem condExp_ae_eq_gibbsKernel {γ : Specification S E} (hμ : γ.IsGibbsMeasure μ)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] =ᵐ[μ]
      fun ω ↦ (gibbsKernel γ ν₀ ω A).toReal :=
  AbstractSpecification.condExp_ae_eq_paKernel
    (mem_toAbstract_invariant_of_isGibbsMeasure hμ) hA

end GibbsKernel

section Main

variable [StandardBorelSpace E] (γ : Specification S E) (ν₀ : Measure (S → E))

theorem isPAKernel_gibbsKernel (hν₀ : ν₀ ∈ G γ) :
    IsPAKernel (G γ) (@tailSigmaAlgebra S E _) (gibbsKernel γ ν₀) :=
  γ.toAbstract_invariant_eq_G ▸
    AbstractSpecification.isPAKernel_paKernel γ.toAbstract exhaustionVolumes
      exhaustionVolumes_monotone exhaustionVolumes_cofinal ν₀
      (mem_toAbstract_invariant_of_mem_G hν₀)

/-- **Georgii, Proposition (7.25)**: if `G(γ) ≠ ∅` then there is a `(G(γ), 𝓣)`-kernel, which can be
taken with all its values in `G(γ)`. -/
theorem exists_isPAKernel_G (hG : (G γ).Nonempty) :
    ∃ π : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E),
      IsMarkovKernel π ∧ IsPAKernel (G γ) (@tailSigmaAlgebra S E _) π := by
  obtain ⟨ν₀, hν₀⟩ := hG
  have := hν₀.1
  exact ⟨gibbsKernel γ ν₀, inferInstance, isPAKernel_gibbsKernel γ ν₀ hν₀⟩

end Main

end MeasureTheory.GibbsMeasure

end

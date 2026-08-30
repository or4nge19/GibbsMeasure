/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Specification.PAKernel
public import GibbsMeasure.Specification.ChoquetLaw
public import GibbsMeasure.Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.CDF

/-!
# Georgii, Proposition (7.25): a `(G(γ), 𝓣)`-kernel

For a specification `γ` on `S → E` (`S` countable, `E` standard Borel) with `G(γ) ≠ ∅`, we build
a probability kernel `gibbsKernel γ ν₀ : Kernel[𝓣] (S → E) (S → E)` which does not depend on any
Gibbs measure and is a version of `μ(· | 𝓣)` for every `μ ∈ G(γ)` (Definition (7.21)), with all
its values in `G(γ)`.

Instead of Georgii's countable core we use Mathlib's disintegration toolkit: along the exhaustion
`exhaustionVolumes`, Lévy's downward theorem (`limUnder_condExp_ae_eq_condExp_iInf`) and the DLR
equation identify `lim_n γ_{Λ_n}(A | ·)` with `μ(A | 𝓣)`; applying this to the half-lines
`{embeddingReal (S → E) ≤ q}`, `q : ℚ`, gives a tail-measurable rational CDF, which
`stieltjesOfMeasurableRat` turns into a kernel to `ℝ`, pulled back to `S → E` by `comapRight`.
For a Gibbs measure `μ` this kernel is `μ`-a.e. equal to `tailKernel μ = condExpKernel μ 𝓣`,
which is a.e. Gibbs by the tower property; the remaining bad tail set is sent to `ν₀ ∈ G(γ)`.
-/

@[expose] public section

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
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] := by
  have hg : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hA
  have h1 := limUnder_condExp_ae_eq_condExp_iInf (μ := μ)
    (antitone_exhaustionFiltration (S := S) (E := E)) exhaustionFiltration_le_pi hg
  rw [iInf_exhaustionFiltration] at h1
  have h2 : ∀ᵐ ω ∂μ, ∀ n,
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | exhaustionFiltration S E n] ω
        = (γ (exhaustionVolumes n) ω A).toReal :=
    ae_all_iff.2 fun n ↦ condExp_exhaustionFiltration_ae_eq hμ hA n
  filter_upwards [h1, h2] with ω h1ω h2ω
  rw [← h1ω]
  congr 1
  funext n
  exact (h2ω n).symm

end Levy

section TailLimit

variable (γ : Specification S E)

/-- The tail limit `lim_n γ_{Λ_n}(A | ω)` along the exhaustion (as a `limUnder`, hence defined
everywhere). -/
noncomputable def tailLimit (A : Set (S → E)) (ω : S → E) : ℝ :=
  limUnder atTop fun n ↦ (γ (exhaustionVolumes n) ω A).toReal

lemma measurable_tailLimit {A : Set (S → E)} (hA : MeasurableSet A) :
    Measurable[@tailSigmaAlgebra S E _] (tailLimit γ A) := by
  rw [← iInf_exhaustionFiltration]
  refine (stronglyMeasurable_iInf_limUnder_of_antitone
    (antitone_exhaustionFiltration (S := S) (E := E))
    (f := fun n ω ↦ (γ (exhaustionVolumes n) ω A).toReal) fun n ↦ ?_).measurable
  exact (Kernel.measurable_coe (γ (exhaustionVolumes n)) hA).ennreal_toReal.stronglyMeasurable

lemma tailLimit_ae_eq_condExp {μ : Measure (S → E)} [IsProbabilityMeasure μ]
    {γ : Specification S E}
    (hμ : γ.IsGibbsMeasure μ) {A : Set (S → E)} (hA : MeasurableSet A) :
    tailLimit γ A =ᵐ[μ] μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
  limUnder_ae_eq_condExp_tail hμ hA

end TailLimit

section RatCDF

variable [StandardBorelSpace E] (γ : Specification S E)

/-- The rational tail CDF `ω ↦ (q ↦ lim_n γ_{Λ_n}({e ≤ q} | ω))`, where
`e = embeddingReal (S → E)`. -/
noncomputable def tailRatCDF (ω : S → E) (q : ℚ) : ℝ :=
  tailLimit γ (embeddingReal (S → E) ⁻¹' Iic (q : ℝ)) ω

lemma measurable_tailRatCDF : Measurable[@tailSigmaAlgebra S E _] (tailRatCDF γ) := by
  have h : ∀ q : ℚ, MeasurableSet (embeddingReal (S → E) ⁻¹' Iic (q : ℝ)) := fun q ↦
    measurableSet_Iic.preimage (measurable_embeddingReal _)
  let _ : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
  exact measurable_pi_iff.2 fun q ↦ measurable_tailLimit γ (h q)

/-- The tail-measurable kernel to `ℝ` obtained from the rational tail CDF. -/
noncomputable def tailRealKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) ℝ :=
  letI : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
  ⟨fun ω ↦ (stieltjesOfMeasurableRat (tailRatCDF γ) (measurable_tailRatCDF γ) ω).measure,
    measurable_measure_stieltjesOfMeasurableRat _⟩

lemma tailRealKernel_apply (ω : S → E) :
    tailRealKernel γ ω =
      (@stieltjesOfMeasurableRat (S → E) (@tailSigmaAlgebra S E _) (tailRatCDF γ)
        (measurable_tailRatCDF γ) ω).measure := rfl

instance : IsMarkovKernel (tailRealKernel γ) := by
  let _ : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
  exact ⟨fun ω ↦ ⟨by rw [tailRealKernel_apply]; exact measure_stieltjesOfMeasurableRat_univ _ _⟩⟩

lemma tailRealKernel_apply_Iic {ω : S → E} (hω : IsRatStieltjesPoint (tailRatCDF γ) ω) (q : ℚ) :
    tailRealKernel γ ω (Iic (q : ℝ)) = ENNReal.ofReal (tailRatCDF γ ω q) := by
  let _ : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
  rw [tailRealKernel_apply, measure_stieltjesOfMeasurableRat_Iic, stieltjesOfMeasurableRat_eq,
    toRatCDF_of_isRatStieltjesPoint hω]

end RatCDF

section StieltjesPoint

/-- A function agreeing on the rationals with the CDF of a probability measure on `ℝ` is a
Stieltjes point. -/
lemma isRatStieltjesPoint_of_forall_eq_real_Iic {α : Type*} {f : α → ℚ → ℝ} {a : α}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h : ∀ q : ℚ, f a q = ν.real (Iic (q : ℝ))) :
    IsRatStieltjesPoint f a := by
  have hf : f a = fun q : ℚ ↦ cdf ν (q : ℝ) := funext fun q ↦ by rw [h, cdf_eq_real]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hf]; exact fun q r hqr ↦ monotone_cdf ν (by exact_mod_cast hqr)
  · rw [hf]; exact (tendsto_cdf_atTop ν).comp (tendsto_ratCast_atTop_iff.2 tendsto_id)
  · rw [hf]; exact (tendsto_cdf_atBot ν).comp (tendsto_ratCast_atBot_iff.2 tendsto_id)
  · intro t
    rw [hf]
    show ⨅ r : Ioi t, cdf ν ((r : ℚ) : ℝ) = cdf ν (t : ℝ)
    rw [← (cdf ν).iInf_rat_gt_eq (t : ℝ)]
    exact Equiv.iInf_congr
      { toFun := fun r ↦ ⟨r.1, by exact_mod_cast Set.mem_Ioi.1 r.2⟩
        invFun := fun r ↦ ⟨r.1, Set.mem_Ioi.2 (by exact_mod_cast r.2)⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } fun _ ↦ rfl

end StieltjesPoint

section Identification

variable [StandardBorelSpace E] {γ : Specification S E} (μ : Measure (S → E))
  [IsProbabilityMeasure μ]

lemma tailKernel_real_ae_eq_condExp {A : Set (S → E)} (hA : MeasurableSet A) :
    (fun ω ↦ (tailKernel μ ω).real A) =ᵐ[μ]
      μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
  condExpKernel_ae_eq_condExp (μ := μ) (tailSigmaAlgebra_le_pi (S := S) (E := E)) hA

lemma ae_forall_tailRatCDF_eq (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, ∀ q : ℚ, tailRatCDF γ ω q =
      ((tailKernel μ ω).map (embeddingReal (S → E))).real (Iic (q : ℝ)) := by
  refine ae_all_iff.2 fun q ↦ ?_
  have hA : MeasurableSet (embeddingReal (S → E) ⁻¹' Iic (q : ℝ)) :=
    measurableSet_Iic.preimage (measurable_embeddingReal _)
  filter_upwards [tailLimit_ae_eq_condExp hμ hA, tailKernel_real_ae_eq_condExp μ hA] with ω h1 h2
  rw [map_measureReal_apply (measurable_embeddingReal _) measurableSet_Iic]
  exact h1.trans h2.symm

lemma ae_tailRealKernel_eq_map (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, tailRealKernel γ ω = (tailKernel μ ω).map (embeddingReal (S → E)) := by
  filter_upwards [ae_forall_tailRatCDF_eq μ hμ] with ω hω
  set ν : Measure ℝ := (tailKernel μ ω).map (embeddingReal (S → E)) with hν
  have : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_embeddingReal _).aemeasurable
  have hpt : IsRatStieltjesPoint (tailRatCDF γ) ω :=
    isRatStieltjesPoint_of_forall_eq_real_Iic ν hω
  have hS : @stieltjesOfMeasurableRat (S → E) (@tailSigmaAlgebra S E _) (tailRatCDF γ)
      (measurable_tailRatCDF γ) ω = cdf ν := by
    let _ : MeasurableSpace (S → E) := @tailSigmaAlgebra S E _
    ext x
    rw [← (cdf ν).iInf_rat_gt_eq x]
    show IsMeasurableRatCDF.stieltjesFunctionAux (toRatCDF (tailRatCDF γ)) ω x = _
    rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
    refine iInf_congr fun r ↦ ?_
    rw [toRatCDF_of_isRatStieltjesPoint hpt, hω, cdf_eq_real]
  rw [tailRealKernel_apply, hS, measure_cdf]

/-- Tower property: the tail conditional measures of a Gibbs measure are a.e. fixed by `γ Λ`
on any measurable set. -/
lemma ae_bind_tailKernel_apply_eq (hμ : γ.IsGibbsMeasure μ) (Λ : Finset S) {B : Set (S → E)}
    (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, (tailKernel μ ω).bind (γ Λ) B = tailKernel μ ω B := by
  have hm : (@tailSigmaAlgebra S E _ : MeasurableSpace (S → E)) ≤ MeasurableSpace.pi :=
    tailSigmaAlgebra_le_pi
  have hmeasγ : Measurable (γ Λ : (S → E) → Measure (S → E)) :=
    (γ Λ).measurable.mono cylinderEvents_le_pi le_rfl
  set g : (S → E) → ℝ := fun x ↦ (γ Λ x B).toReal with hg
  have hg_meas : Measurable g :=
    ((Kernel.measurable_coe (γ Λ) hB).mono cylinderEvents_le_pi le_rfl).ennreal_toReal
  have hg_int : ∀ (ν : Measure (S → E)) [IsFiniteMeasure ν], Integrable g ν := fun ν _ ↦
    (memLp_top_of_bound hg_meas.aestronglyMeasurable 1 (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one))).integrable
      le_top
  have h1 : μ[g | @tailSigmaAlgebra S E _] =ᵐ[μ] fun ω ↦ ∫ y, g y ∂(tailKernel μ ω) :=
    condExp_ae_eq_integral_condExpKernel hm (hg_int μ)
  have h2 : g =ᵐ[μ] μ[B.indicator (fun _ ↦ (1 : ℝ)) |
      cylinderEvents (X := fun _ : S ↦ E) ((Λ : Set S)ᶜ)] :=
    (@Kernel.IsCondExp.condExp_ae_eq_kernel_apply _ _ _ _ _ (hμ Λ) B hB).symm
  have h3 : μ[g | @tailSigmaAlgebra S E _] =ᵐ[μ]
      μ[B.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] :=
    (condExp_congr_ae h2).trans
      (condExp_condExp_of_le (tailSigmaAlgebra_le_cylinderEvents Λ) cylinderEvents_le_pi)
  filter_upwards [h1, h3, tailKernel_real_ae_eq_condExp μ hB] with ω h1ω h3ω h4ω
  have hint : ∫ y, g y ∂(tailKernel μ ω) = (tailKernel μ ω).real B := by
    rw [← h1ω, h3ω, h4ω]
  have hlint : ∫⁻ x, γ Λ x B ∂(tailKernel μ ω) = ENNReal.ofReal (∫ y, g y ∂(tailKernel μ ω)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hg_int _) (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)]
    exact lintegral_congr fun x ↦ (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [Measure.bind_apply hB hmeasγ.aemeasurable, hlint, hint, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma ae_isGibbsCore_tailKernel (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, IsGibbsCore γ (tailKernel μ ω) := by
  have h : ∀ᵐ ω ∂μ, ∀ (Λ : Finset S) (t : Finset ℕ),
      (tailKernel μ ω).bind (γ Λ) (piNatGen (Ω := S → E) t) =
        tailKernel μ ω (piNatGen (Ω := S → E) t) :=
    ae_all_iff.2 fun Λ ↦ ae_all_iff.2 fun t ↦
      ae_bind_tailKernel_apply_eq μ hμ Λ (measurableSet_piNatGen t)
  filter_upwards [h] with ω hω
  exact ⟨measure_univ, hω⟩

end Identification

section GibbsKernel

variable [StandardBorelSpace E] (γ : Specification S E) (ν₀ : Measure (S → E))

/-- The tail event on which `tailRealKernel γ` is carried by the range of `embeddingReal`. -/
def rangeSet : Set (S → E) :=
  {ω | tailRealKernel γ ω (range (embeddingReal (S → E))) = 1}

lemma measurableSet_rangeSet : MeasurableSet[@tailSigmaAlgebra S E _] (rangeSet γ) :=
  (measurableSet_singleton 1).preimage
    (Kernel.measurable_coe _ (measurableEmbedding_embeddingReal _).measurableSet_range)

open Classical in
/-- `tailRealKernel γ`, replaced off `rangeSet γ` by the pushforward of `ν₀`. -/
noncomputable def tailRealKernel' : Kernel[@tailSigmaAlgebra S E _] (S → E) ℝ :=
  Kernel.piecewise (measurableSet_rangeSet γ) (tailRealKernel γ)
    (@Kernel.const (S → E) ℝ (@tailSigmaAlgebra S E _) _ (ν₀.map (embeddingReal (S → E))))

lemma tailRealKernel'_apply_range [IsProbabilityMeasure ν₀] (ω : S → E) :
    tailRealKernel' γ ν₀ ω (range (embeddingReal (S → E))) = 1 := by
  classical
  rw [tailRealKernel', Kernel.piecewise_apply]
  split_ifs with h
  · exact h
  · rw [Kernel.const_apply, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]

/-- The candidate `(G(γ), 𝓣)`-kernel, before correction on the bad tail set. -/
noncomputable def gibbsKernelAux : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  Kernel.comapRight (tailRealKernel' γ ν₀) (measurableEmbedding_embeddingReal (S → E))

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (gibbsKernelAux γ ν₀) :=
  Kernel.IsMarkovKernel.comapRight _ _ (tailRealKernel'_apply_range γ ν₀)

/-- The tail event on which `gibbsKernelAux γ ν₀` is a Gibbs measure. -/
def gibbsSet : Set (S → E) := {ω | IsGibbsCore γ (gibbsKernelAux γ ν₀ ω)}

lemma measurableSet_gibbsSet : MeasurableSet[@tailSigmaAlgebra S E _] (gibbsSet γ ν₀) :=
  (measurableSet_isGibbsCore γ).preimage (gibbsKernelAux γ ν₀).measurable

open Classical in
/-- Georgii (7.25): the `μ`-independent `(G(γ), 𝓣)`-kernel, equal to `ν₀` off `gibbsSet γ ν₀`. -/
noncomputable def gibbsKernel : Kernel[@tailSigmaAlgebra S E _] (S → E) (S → E) :=
  Kernel.piecewise (measurableSet_gibbsSet γ ν₀) (gibbsKernelAux γ ν₀)
    (@Kernel.const (S → E) (S → E) (@tailSigmaAlgebra S E _) _ ν₀)

instance [IsProbabilityMeasure ν₀] : IsMarkovKernel (gibbsKernel γ ν₀) := by
  unfold gibbsKernel; infer_instance

lemma gibbsKernel_mem_G (hν₀ : ν₀ ∈ G γ) (ω : S → E) : gibbsKernel γ ν₀ ω ∈ G γ := by
  classical
  rw [gibbsKernel, Kernel.piecewise_apply]
  split_ifs with h
  · exact ⟨⟨h.1⟩, isGibbsMeasure_of_isGibbsCore γ h⟩
  · rw [Kernel.const_apply]; exact hν₀

variable {μ : Measure (S → E)} [IsProbabilityMeasure μ]

lemma ae_gibbsKernel_eq_tailKernel {γ : Specification S E} (hμ : γ.IsGibbsMeasure μ) :
    ∀ᵐ ω ∂μ, gibbsKernel γ ν₀ ω = tailKernel μ ω := by
  classical
  filter_upwards [ae_tailRealKernel_eq_map μ hμ, ae_isGibbsCore_tailKernel μ hμ] with ω h1 h2
  have hrange : ω ∈ rangeSet γ := by
    show tailRealKernel γ ω (range (embeddingReal (S → E))) = 1
    rw [h1, Measure.map_apply (measurable_embeddingReal _)
      (measurableEmbedding_embeddingReal _).measurableSet_range, preimage_range, measure_univ]
  have haux : gibbsKernelAux γ ν₀ ω = tailKernel μ ω := by
    rw [gibbsKernelAux, Kernel.comapRight_apply, tailRealKernel', Kernel.piecewise_apply,
      ite_eq_left hrange, h1, (measurableEmbedding_embeddingReal _).comap_map]
  have hgood : ω ∈ gibbsSet γ ν₀ := by
    show IsGibbsCore γ (gibbsKernelAux γ ν₀ ω)
    rw [haux]; exact h2
  rw [gibbsKernel, Kernel.piecewise_apply, ite_eq_left hgood, haux]

/-- Georgii (7.21)(i) for `gibbsKernel`: it is a version of `μ(· | 𝓣)` for every Gibbs `μ`. -/
theorem condExp_ae_eq_gibbsKernel {γ : Specification S E} (hμ : γ.IsGibbsMeasure μ)
    {A : Set (S → E)} (hA : MeasurableSet A) :
    μ[A.indicator (fun _ ↦ (1 : ℝ)) | @tailSigmaAlgebra S E _] =ᵐ[μ]
      fun ω ↦ (gibbsKernel γ ν₀ ω A).toReal := by
  filter_upwards [ae_gibbsKernel_eq_tailKernel ν₀ hμ, tailKernel_real_ae_eq_condExp μ hA]
    with ω h1 h2
  rw [h1, ← h2, measureReal_def]

end GibbsKernel

section Main

variable [StandardBorelSpace E] (γ : Specification S E) (ν₀ : Measure (S → E))

theorem isPAKernel_gibbsKernel (hν₀ : ν₀ ∈ G γ) :
    IsPAKernel (G γ) (@tailSigmaAlgebra S E _) (gibbsKernel γ ν₀) :=
  ⟨fun μ hμ A hA ↦ by
    have := hμ.1
    exact (condExp_ae_eq_gibbsKernel ν₀ hμ.2 hA).symm, gibbsKernel_mem_G γ ν₀ hν₀⟩

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

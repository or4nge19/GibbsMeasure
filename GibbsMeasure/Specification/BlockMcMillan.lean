/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.PiWithDensity
public import GibbsMeasure.Mathlib.MeasureTheory.Function.ConditionalExpectation.Trivial
public import GibbsMeasure.Mathlib.Dynamics.Ergodic.MeanErgodic
public import GibbsMeasure.Specification.BlockEntropy
public import GibbsMeasure.Specification.ErgodicGibbs
public import GibbsMeasure.Specification.KolmogorovZeroOne

/-!
# The theorem of McMillan for an independent-block random field (Georgii, proof of (15.47))

Georgii's proof of the large deviation lower bound (15.47) invokes "the theorem of McMillan"
(Shannon–McMillan, `L¹` form) for one very special ergodic random field: the randomly shifted
independent-block measure `γ̃` of Proposition (15.52). For that field no general
Shannon–McMillan theorem is needed. Its density relative to the a priori product measure
factorises over the independent blocks, so the statement is the `L¹` law of large numbers for the
i.i.d. block variables, i.e. the mean ergodic theorem for a Bernoulli field.

This file proves that law, for an arbitrary measurable state space and an arbitrary a priori
probability measure — Georgii's generality, and more: no standard Borel hypothesis and no
finiteness of the state space enters anywhere.

## Main results

### The Bernoulli field is ergodic, and its `L¹` law of large numbers

* `MeasureTheory.GibbsMeasure.infinitePi_mem_trivialOn_invariantEvents`: for a countable
  **infinite** additive group of sites `S` and a probability measure `γ` on `X`, the i.i.d.
  random field `γ^S = Measure.infinitePi (fun _ : S ↦ γ)` is trivial on the invariant σ-algebra
  `𝓘` of the shift group; `MeasureTheory.GibbsMeasure.ergodicSMul_infinitePi` says the same in
  the language of Georgii Definition (14.6). This is Kolmogorov's 0–1 law
  (`forall_tail_measure_eq_zero_or_one_infinitePi`) together with Georgii's Proposition (14.9)
  (`mem_trivialOn_invariantEvents_of_mem_trivialOn_tail`): `𝓘 ⊆ 𝓣` almost surely.
* `MeasureTheory.GibbsMeasure.tendsto_integral_abs_inv_card_sum_shift_sub_integral`, the **`L¹`
  law of large numbers**: for integrable `f` and any Følner net `F` of finite subsets of `S`,
  `∫ | |F_k|⁻¹ ∑_{i ∈ F_k} f(θ_i ω) − γ^S(f) | dγ^S(ω) → 0`. This is the mean ergodic theorem
  (14.A5) (`tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp`) plus the ergodicity above.

### The density of a Bernoulli field in a finite volume

* `MeasureTheory.GibbsMeasure.infinitePi_apply_eq_setLIntegral_prod_rnDeriv`: on the cylinder
  σ-algebra `𝓕_F` of a finite volume, `γ^S` has density `∏_{i ∈ F} r(ω_i)` relative to `λ^S`,
  where `r = dγ/dλ` (`Measure.pi_withDensity`).
* `MeasureTheory.GibbsMeasure.infinitePi_le_mul_infinitePi_of_prod_rnDeriv_le` and
  `MeasureTheory.GibbsMeasure.infinitePi_inter_le_mul_infinitePi`, the **change of measure** that
  Georgii's estimate consumes: if `A` is `𝓕_F`-measurable then
  `γ^S(A ∩ {∏_{i ∈ F} r(ω_i) ≤ M}) ≤ M λ^S(A)`.

### McMillan for the i.i.d. field

* `MeasureTheory.GibbsMeasure.tendsto_integral_abs_inv_card_sum_llr_sub`, the **`L¹` theorem of
  McMillan for a Bernoulli field**: `|F_k|⁻¹ ∑_{i ∈ F_k} log r(ζ_i) → 𝓗(γ | λ)` in `L¹(γ^S)`
  along any Følner net, where `r = dγ/dλ`. The only hypotheses are `γ ≪ λ` and the integrability
  of `log r`, i.e. `𝓗(γ | λ) < ∞`.
* `MeasureTheory.GibbsMeasure.tendsto_measure_setOf_prod_rnDeriv_le`: consequently, for every
  `ε > 0`, `γ^S(∏_{i ∈ F_k} r(ζ_i) ≤ exp(|F_k| (𝓗(γ | λ) + ε))) → 1`.

### Transport to the lattice: the independent-block field of Proposition (15.52)

* `MeasureTheory.GibbsMeasure.tileProduct_pi_eq_infinitePi`: for a tiling `(C, H)` of the group
  of sites, the independent-block field of the a priori law `λ^C` on a tile is `λ^S`.
* `MeasureTheory.GibbsMeasure.blockDensity`, the density `∏_{k ∈ K} r(ω_{C+k})` of `γ̂` in a
  volume `Δ` that is a union of tiles, `K` the set of tile indices; and
  `MeasureTheory.GibbsMeasure.tileProduct_inter_le_mul_infinitePi`, the change of measure it
  produces: `γ̂(A ∩ {blockDensity ≤ M}) ≤ M λ^S(A)` for every `𝓕_Δ`-event `A`.
* `MeasureTheory.GibbsMeasure.tendsto_tileProduct_setOf_blockDensity_le`, **the form used in the
  proof of the large deviation lower bound (15.47)**: along volumes `Δ_n` that are unions of
  tiles whose index sets are Følner in `H`,
  `γ̂(blockDensity Δ_n ≤ exp(|K_n| (𝓗(γ | λ^C) + ε))) → 1`. Since `|Δ_n| = |K_n| |C|` and
  `𝓀(γ̃) = −|C|⁻¹ 𝓗(γ | λ^C)` by Proposition (15.52)
  (`MeasureTheory.GibbsMeasure.specificEntropy_tileAverage`), this is Georgii's
  `|Δ_n|⁻¹ log f_{Δ_n} ≤ −𝓀(γ̃) + ε` with probability tending to one.

### The centred-cube tiling of `ℤ^d`

* `MeasureTheory.GibbsMeasure.scaleAddEquiv`: multiplication by `p = 2n+1` is an isomorphism
  `ℤ^d ≃+ p ℤ^d` of the site group onto the tiling subgroup of `isComplement_piFinset_Icc`;
  `MeasureTheory.GibbsMeasure.tileIdxImage_cubeUnion`: the tile indices met by the centred cube
  `Δ_M` of radius `M p + n` are the `p i` with `|i| ≤ M`; hence
  `MeasureTheory.GibbsMeasure.tendsto_card_vadd_tileIdxImage_symmDiff_div_card`, **the Følner
  property** of those index sets in `p ℤ^d`.
* `MeasureTheory.GibbsMeasure.tendsto_tileProduct_setOf_blockDensity_le_cube` and
  `MeasureTheory.GibbsMeasure.tendsto_tileProduct_setOf_blockDensity_le_specificEntropy`,
  **the block McMillan theorem in Georgii's own terms** on `ℤ^d` (`d ≥ 1`): for a block law `γ`
  on `E^{Λ(n)}` with `𝓗(γ | λ^{Λ(n)}) < ∞`, along the centred cubes `Δ_M` of radius `M p + n`,
  `γ̂(|Δ_M|⁻¹ log f_{Δ_M} ≤ −𝓀(γ̃) + ε) → 1` for every `ε > 0`, where `𝓀(γ̃)` is the specific
  entropy of the randomly shifted independent-block field of Proposition (15.52).

### The tiles met by an arbitrary box

Georgii's lower bound (15.47) takes its limit inferior along an *arbitrary* sequence of cubes,
which are not unions of tiles. The volume that is fed to the block McMillan theorem is then
Georgii's `Δ⁺`, the union `tileHull` of the tiles that meet the cube.

* `MeasureTheory.GibbsMeasure.tileHull_Icc_subset` and
  `MeasureTheory.GibbsMeasure.card_tileHull_Icc_le`: the union of the tiles meeting a box of side
  `s + 1` is contained in the box enlarged by `2n` in each direction, so it has at most
  `(s + 4n + 1)^d` sites; hence
  `MeasureTheory.GibbsMeasure.tendsto_card_tileHull_div_card`, **`|Δ⁺| / |Λ| → 1`** along cubes
  whose side tends to infinity. This is what lets an estimate that lives on a union of tiles be
  read at the scale of an arbitrary cube.
* `MeasureTheory.GibbsMeasure.tendsto_card_vadd_tileIdxImage_Icc_symmDiff_div_card`: the tile
  indices met by such cubes are **Følner** in `p ℤ^d`, by
  `MeasureTheory.GibbsMeasure.card_vadd_tileIdxImage_symmDiff_le` together with `|K| ≥ |Λ| / |C|`.

## Why no Shannon–McMillan theorem is needed

The general Shannon–McMillan(–Breiman) theorem asserts `|Λ|⁻¹ log f_Λ → −𝓀(μ)` in `L¹(μ)` for
*every* ergodic `μ ∈ 𝓟_Θ`; over a general standard Borel state space it is a genuine theorem
about the martingale of conditional densities. Georgii applies it only to `γ̃`, and for `γ̃`
restricted to a volume that is a union of tiles the density is *exactly* a product of `|Δ|/|C|`
independent copies of one function; there is nothing left but the law of large numbers, which is
the mean ergodic theorem. Only the upper bound in probability
(`tendsto_measure_setOf_prod_rnDeriv_le`) is consumed by the proof of (15.47), but the `L¹`
statement is what is proved here, since it costs nothing more.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Finset Function MeasureTheory ProbabilityTheory Real Topology
open InformationTheory
open scoped ENNReal NNReal Pointwise Topology symmDiff

noncomputable section

namespace MeasureTheory.GibbsMeasure

/-! ### The i.i.d. random field is ergodic -/

section Ergodic

variable {S X : Type*} [MeasurableSpace X] [AddCommGroup S]
  (γ : Measure X) [IsProbabilityMeasure γ]

/-- The i.i.d. random field `γ^S` is a shift-invariant random field, `γ^S ∈ 𝓟_Θ`. -/
theorem infinitePi_mem_invariantFields_shiftGroup :
    (Measure.infinitePi fun _ : S ↦ γ) ∈ invariantFields (shiftGroup S X) :=
  mem_invariantFields_shiftGroup.2 ⟨inferInstance, measurePreserving_shift_infinitePi γ⟩

variable [Countable S] [Infinite S]

/-- **The i.i.d. random field is ergodic.** For a countable *infinite* additive group of sites,
`γ^S` is trivial on the invariant σ-algebra `𝓘`: Kolmogorov's 0–1 law says it is trivial on the
tail σ-algebra, and Georgii's Proposition (14.9) says `𝓘 ⊆ 𝓣` up to `γ^S`-null sets. -/
theorem infinitePi_mem_trivialOn_invariantEvents :
    (Measure.infinitePi fun _ : S ↦ γ) ∈ trivialOn (invariantEvents (shiftGroup S X)) :=
  mem_trivialOn_invariantEvents_of_mem_trivialOn_tail
    (infinitePi_mem_invariantFields_shiftGroup γ)
    (shiftGroup_exists_disjoint_sites_preimage (E := X))
    fun _ hA ↦ forall_tail_measure_eq_zero_or_one_infinitePi _ hA

/-- **The i.i.d. random field is ergodic**, in the language of Georgii Definition (14.6). -/
theorem ergodicSMul_infinitePi : ErgodicSMul (shiftGroup S X) (S → X)
    (Measure.infinitePi fun _ : S ↦ γ) :=
  (ergodicSMul_iff_mem_trivialOn_invariantEvents
    (infinitePi_mem_invariantFields_shiftGroup γ).2).2
    (infinitePi_mem_trivialOn_invariantEvents γ)

end Ergodic

/-! ### The `L¹` law of large numbers for an i.i.d. random field -/

section LLN

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {S X : Type*} [MeasurableSpace X] [AddCommGroup S] [DecidableEq S] [Countable S]
  [Infinite S] (γ : Measure X) [IsProbabilityMeasure γ]

omit [DecidableEq S] in
/-- Under the shift action, the conditional expectation of an integrable observable given the
invariant σ-algebra of an i.i.d. random field is its mean. -/
theorem condExp_infinitePi_ae_eq_integral {f : (S → X) → ℝ} :
    (Measure.infinitePi fun _ : S ↦ γ)[f |
        MeasurableSpace.smulInvariants (Multiplicative S) (S → X)]
      =ᵐ[Measure.infinitePi fun _ : S ↦ γ]
      fun _ ↦ ∫ ω, f ω ∂(Measure.infinitePi fun _ : S ↦ γ) := by
  refine condExp_ae_eq_integral_of_forall_measure_eq_zero_or_one ?_ (fun A hA ↦ ?_) f
  · rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup]
    exact fun A hA ↦ (measurableSet_invariantEvents.1 hA).1
  · rw [smulInvariants_multiplicative_eq_invariantEvents_shiftGroup] at hA
    exact infinitePi_mem_trivialOn_invariantEvents γ A hA

variable {κ : Type*} {l : Filter κ} {F : κ → Finset S}

/-- **The `L¹` law of large numbers for an i.i.d. random field.** For an integrable observable `f`
and a Følner net `(F_k)` of finite sets of sites,
`∫ | |F_k|⁻¹ ∑_{i ∈ F_k} f(θ_i ω) − γ^S(f) | dγ^S(ω) → 0`.
This is Georgii's mean ergodic theorem (14.A5) together with the ergodicity of `γ^S`. -/
theorem tendsto_integral_abs_inv_card_sum_shift_sub_integral
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hF : ∀ j : S, Tendsto (fun k ↦ (((j +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {f : (S → X) → ℝ} (hf : Integrable f (Measure.infinitePi fun _ : S ↦ γ)) :
    Tendsto (fun k ↦ ∫ ω, |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, f ((shift X i).toFun ω)
        - ∫ ω, f ω ∂(Measure.infinitePi fun _ : S ↦ γ)|
      ∂(Measure.infinitePi fun _ : S ↦ γ)) l (𝓝 0) := by
  have hvadd : VAddInvariantMeasure S (S → X) (Measure.infinitePi fun _ : S ↦ γ) :=
    vaddInvariantMeasure_of_forall_measurePreserving_shift
      (measurePreserving_shift_infinitePi γ)
  have h := tendsto_integral_norm_inv_card_smul_sum_vadd_sub_condExp
    (μ := Measure.infinitePi fun _ : S ↦ γ) (F := F) hne hF hf
  refine h.congr fun k ↦ ?_
  refine integral_congr_ae ?_
  filter_upwards [condExp_infinitePi_ae_eq_integral γ (f := f)] with ω hω
  simp only [shift_vadd] at *
  rw [hω, Real.norm_eq_abs, smul_eq_mul]

end LLN

/-! ### The density of an i.i.d. random field in a finite volume -/

section Density

variable {S X : Type*} [MeasurableSpace X] {γ lam : Measure X}
  [IsProbabilityMeasure γ] [IsProbabilityMeasure lam]

omit [IsProbabilityMeasure γ] [IsProbabilityMeasure lam] in
variable (γ lam) in
/-- The product of the single-site densities over a finite volume `F` is measurable for the
cylinder σ-algebra `𝓕_F`. -/
theorem measurable_cylinderEvents_prod_rnDeriv (F : Finset S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ X) (F : Set S)]
      fun ω : S → X ↦ ∏ i ∈ F, γ.rnDeriv lam (ω i) :=
  Finset.measurable_prod _ fun _ hi ↦
    (γ.measurable_rnDeriv lam).comp
      (Measurable.eval_cylinderEvents (Δ := (F : Set S)) (Finset.mem_coe.2 hi) measurable_id)

/-- **The density of a Bernoulli field in a finite volume.** If `γ ≪ λ` then, on the cylinder
σ-algebra `𝓕_F` of a finite volume `F`, the i.i.d. random field `γ^S` has density
`∏_{i ∈ F} r(ω_i)` relative to `λ^S`, where `r = dγ/dλ`. -/
theorem infinitePi_apply_eq_setLIntegral_prod_rnDeriv (hac : γ ≪ lam) {F : Finset S}
    {A : Set (S → X)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ X) (F : Set S)] A) :
    (Measure.infinitePi fun _ : S ↦ γ) A
      = ∫⁻ ω in A, ∏ i ∈ F, γ.rnDeriv lam (ω i) ∂(Measure.infinitePi fun _ : S ↦ lam) := by
  classical
  have hr : Measurable (γ.rnDeriv lam) := γ.measurable_rnDeriv lam
  -- the finite-volume marginals, and the product density
  have hpi : Measure.pi (fun _ : F ↦ γ)
      = (Measure.pi fun _ : F ↦ lam).withDensity fun v ↦ ∏ i : F, γ.rnDeriv lam (v i) := by
    have hγ : γ = lam.withDensity (γ.rnDeriv lam) := (Measure.withDensity_rnDeriv_eq γ lam hac).symm
    have : ∀ _ : F, SigmaFinite (lam.withDensity (γ.rnDeriv lam)) := fun _ ↦ by
      rw [← hγ]; infer_instance
    conv_lhs => rw [show (fun _ : F ↦ γ) = fun _ : F ↦ lam.withDensity (γ.rnDeriv lam) from
      funext fun _ ↦ hγ]
    exact Measure.pi_withDensity _ fun _ ↦ hr
  -- `A` is a cylinder over `F`
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA
  obtain ⟨B, hB, rfl⟩ := hA
  have hAmeas : MeasurableSet ((F.restrict ⁻¹' B : Set (S → X))) :=
    Finset.measurable_restrict F hB
  have hprod : ∀ ω : S → X, ∏ i ∈ F, γ.rnDeriv lam (ω i)
      = ∏ i : F, γ.rnDeriv lam (F.restrict ω i) := fun ω ↦ (Finset.prod_coe_sort F _).symm
  calc (Measure.infinitePi fun _ : S ↦ γ) (F.restrict ⁻¹' B)
      = Measure.pi (fun _ : F ↦ γ) B := by
        rw [← Measure.map_apply (Finset.measurable_restrict F) hB, Measure.infinitePi_map_restrict]
    _ = ∫⁻ v in B, ∏ i : F, γ.rnDeriv lam (v i) ∂(Measure.pi fun _ : F ↦ lam) := by
        rw [hpi, withDensity_apply _ hB]
    _ = ∫⁻ ω in F.restrict ⁻¹' B, ∏ i ∈ F, γ.rnDeriv lam (ω i)
          ∂(Measure.infinitePi fun _ : S ↦ lam) := by
        rw [← Measure.infinitePi_map_restrict (μ := fun _ : S ↦ lam),
          setLIntegral_map hB (by fun_prop) (Finset.measurable_restrict F)]
        exact setLIntegral_congr_fun hAmeas fun ω _ ↦ (hprod ω).symm

/-- **The change of measure behind Georgii's proof of the lower bound (15.47).** If `A` is an
event of the finite volume `F` on which the product `∏_{i ∈ F} r(ω_i)` of the single-site
densities is at most `M`, then `γ^S(A) ≤ M λ^S(A)`. -/
theorem infinitePi_le_mul_infinitePi_of_prod_rnDeriv_le (hac : γ ≪ lam) {F : Finset S}
    {A : Set (S → X)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ X) (F : Set S)] A)
    {M : ℝ≥0∞} (hM : ∀ ω ∈ A, ∏ i ∈ F, γ.rnDeriv lam (ω i) ≤ M) :
    (Measure.infinitePi fun _ : S ↦ γ) A ≤ M * (Measure.infinitePi fun _ : S ↦ lam) A := by
  have hAmeas : MeasurableSet A := cylinderEvents_le_pi _ hA
  rw [infinitePi_apply_eq_setLIntegral_prod_rnDeriv hac hA]
  calc ∫⁻ ω in A, ∏ i ∈ F, γ.rnDeriv lam (ω i) ∂(Measure.infinitePi fun _ : S ↦ lam)
      ≤ ∫⁻ _ in A, M ∂(Measure.infinitePi fun _ : S ↦ lam) :=
        setLIntegral_mono' hAmeas fun ω hω ↦ hM ω hω
    _ = M * (Measure.infinitePi fun _ : S ↦ lam) A := setLIntegral_const _ _

/-- **The change of measure of Georgii's proof of (15.47), with the McMillan cut-off built in.**
For a `𝓕_F`-event `A`, the part of `A` on which the product of the single-site densities is at
most `M` has `γ^S`-measure at most `M λ^S(A)`. -/
theorem infinitePi_inter_le_mul_infinitePi (hac : γ ≪ lam) {F : Finset S} {A : Set (S → X)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ X) (F : Set S)] A) (M : ℝ≥0∞) :
    (Measure.infinitePi fun _ : S ↦ γ)
        (A ∩ {ζ : S → X | ∏ i ∈ F, γ.rnDeriv lam (ζ i) ≤ M})
      ≤ M * (Measure.infinitePi fun _ : S ↦ lam) A := by
  have h1 : (Measure.infinitePi fun _ : S ↦ γ)
      (A ∩ {ζ : S → X | ∏ i ∈ F, γ.rnDeriv lam (ζ i) ≤ M})
      ≤ M * (Measure.infinitePi fun _ : S ↦ lam)
        (A ∩ {ζ : S → X | ∏ i ∈ F, γ.rnDeriv lam (ζ i) ≤ M}) :=
    infinitePi_le_mul_infinitePi_of_prod_rnDeriv_le hac
      (hA.inter ((measurable_cylinderEvents_prod_rnDeriv γ lam F) measurableSet_Iic))
      fun ω hω ↦ hω.2
  exact h1.trans (by gcongr; exact Set.inter_subset_left)

end Density

/-! ### The theorem of McMillan for an i.i.d. random field -/

section McMillan

attribute [local instance] shiftAddAction measurableConstVAdd_shift

variable {S X : Type*} [MeasurableSpace X] [AddCommGroup S] [DecidableEq S] [Countable S]
  [Infinite S] {γ lam : Measure X} [IsProbabilityMeasure γ] [IsProbabilityMeasure lam]
  {κ : Type*} {l : Filter κ} {F : κ → Finset S}

/-- For probability measures, the Kullback–Leibler divergence is the mean of the log-likelihood
ratio. -/
theorem toReal_klDiv_eq_integral_llr (hac : γ ≪ lam) (hint : Integrable (llr γ lam) γ) :
    (klDiv γ lam).toReal = ∫ x, llr γ lam x ∂γ := by
  rw [toReal_klDiv hac hint]
  simp

omit [DecidableEq S] [Countable S] [Infinite S] [IsProbabilityMeasure lam] in
variable (γ) in
/-- The single-site log-likelihood ratio, read at the origin, is integrable for the i.i.d. random
field as soon as it is integrable for the single-site law. -/
theorem integrable_llr_eval_infinitePi (hint : Integrable (llr γ lam) γ) :
    Integrable (fun ζ : S → X ↦ llr γ lam (ζ 0)) (Measure.infinitePi fun _ : S ↦ γ) :=
  (measurePreserving_eval_infinitePi (fun _ : S ↦ γ) 0).integrable_comp_of_integrable hint

omit [DecidableEq S] [Countable S] [Infinite S] [IsProbabilityMeasure lam] in
variable (γ) in
/-- The mean of the single-site log-likelihood ratio under the i.i.d. random field. -/
theorem integral_llr_eval_infinitePi (hint : Integrable (llr γ lam) γ) :
    ∫ ζ : S → X, llr γ lam (ζ 0) ∂(Measure.infinitePi fun _ : S ↦ γ) = ∫ x, llr γ lam x ∂γ :=
  Measure.integral_infinitePi_eval (fun _ : S ↦ γ) 0 hint.1

omit [Countable S] [Infinite S] [IsProbabilityMeasure γ] [IsProbabilityMeasure lam] in
/-- The reflection `F ↦ −F` of a Følner net is a Følner net. -/
theorem tendsto_card_vadd_image_neg_symmDiff_div_card
    (hFol : ∀ j : S, Tendsto (fun k ↦ (((j +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    (j : S) :
    Tendsto (fun k ↦ ((((j +ᵥ (F k).image fun i ↦ -i) ∆ (F k).image fun i ↦ -i)).card : ℝ)
      / ((F k).image fun i ↦ -i).card) l (𝓝 0) := by
  have hinj : Function.Injective fun i : S ↦ -i := neg_injective
  have hvadd : ∀ k : κ, (j +ᵥ (F k).image fun i ↦ -i)
      = (((-j) +ᵥ F k).image fun i ↦ -i) := by
    intro k
    ext x
    simp only [Finset.mem_vadd_finset, Finset.mem_image, vadd_eq_add]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨-j + y, ⟨y, hy, rfl⟩, by abel⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨-y, ⟨y, hy, rfl⟩, by abel⟩
  refine (hFol (-j)).congr fun k ↦ ?_
  rw [hvadd k, ← Finset.image_symmDiff _ _ hinj, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ hinj]

omit [IsProbabilityMeasure lam] in
/-- **The theorem of McMillan for an i.i.d. random field, `L¹` form.** Let `γ ≪ λ` be probability
measures on `X` with integrable log-likelihood ratio `log r`, `r = dγ/dλ`. Then along every
Følner net `(F_k)` of finite volumes,
`∫ | |F_k|⁻¹ ∑_{i ∈ F_k} log r(ζ_i) − 𝓗(γ | λ) | dγ^S(ζ) → 0`,
where `𝓗(γ | λ) = ∫ log r dγ` is the relative entropy of the single-site law. -/
theorem tendsto_integral_abs_inv_card_sum_llr_sub (hint : Integrable (llr γ lam) γ)
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hFol : ∀ j : S, Tendsto (fun k ↦ (((j +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ζ, |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, llr γ lam (ζ i)
        - ∫ x, llr γ lam x ∂γ| ∂(Measure.infinitePi fun _ : S ↦ γ)) l (𝓝 0) := by
  classical
  have hinj : Function.Injective fun i : S ↦ -i := neg_injective
  have hf := integrable_llr_eval_infinitePi (S := S) γ hint
  have h := tendsto_integral_abs_inv_card_sum_shift_sub_integral γ
    (F := fun k ↦ (F k).image fun i ↦ -i)
    (hne.mono fun k hk ↦ hk.image _) (tendsto_card_vadd_image_neg_symmDiff_div_card hFol) hf
  rw [integral_llr_eval_infinitePi (S := S) γ hint] at h
  refine h.congr fun k ↦ ?_
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [Finset.card_image_of_injective _ hinj,
    Finset.sum_image fun (a : S) _ (b : S) _ h ↦ hinj h, shift_toFun_apply, zero_sub, neg_neg]

omit [AddCommGroup S] [DecidableEq S] [Countable S] [Infinite S] [IsProbabilityMeasure lam] in
/-- The single-site density is finite at every site of a finite volume, almost surely. -/
theorem ae_forall_rnDeriv_ne_top (hac : γ ≪ lam) (F : Finset S) :
    ∀ᵐ ζ ∂(Measure.infinitePi fun _ : S ↦ γ), ∀ i ∈ F, γ.rnDeriv lam (ζ i) ≠ ⊤ := by
  refine (ae_ball_iff F.countable_toSet).2 fun i _ ↦ ?_
  have h : ∀ᵐ x ∂γ, γ.rnDeriv lam x ≠ ⊤ := hac.ae_le (Measure.rnDeriv_ne_top γ lam)
  exact (measurePreserving_eval_infinitePi (fun _ : S ↦ γ) i).quasiMeasurePreserving.ae h

/-- **The theorem of McMillan for an i.i.d. random field, in probability.** For every `ε > 0` the
probability that the product `∏_{i ∈ F_k} r(ζ_i)` of the single-site densities exceeds
`exp(|F_k| (𝓗(γ | λ) + ε))` tends to zero. This is the only consequence of McMillan that
Georgii's proof of the large deviation lower bound (15.47) consumes. -/
theorem tendsto_measure_setOf_prod_rnDeriv_le (hac : γ ≪ lam) (hint : Integrable (llr γ lam) γ)
    (hne : ∀ᶠ k in l, (F k).Nonempty)
    (hFol : ∀ j : S, Tendsto (fun k ↦ (((j +ᵥ F k) ∆ F k).card : ℝ) / (F k).card) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k ↦ (Measure.infinitePi fun _ : S ↦ γ)
        {ζ : S → X | ∏ i ∈ F k, γ.rnDeriv lam (ζ i)
          ≤ ENNReal.ofReal (Real.exp ((F k).card * ((klDiv γ lam).toReal + ε)))}) l (𝓝 1) := by
  classical
  set μ := Measure.infinitePi fun _ : S ↦ γ with hμdef
  set c : ℝ := ∫ x, llr γ lam x ∂γ with hcdef
  have hc : (klDiv γ lam).toReal = c := toReal_klDiv_eq_integral_llr hac hint
  set g : κ → (S → X) → ℝ :=
    fun k ζ ↦ |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, llr γ lam (ζ i) - c| with hgdef
  set T : κ → Set (S → X) := fun k ↦ {ζ : S → X | ∏ i ∈ F k, γ.rnDeriv lam (ζ i)
    ≤ ENNReal.ofReal (Real.exp ((F k).card * ((klDiv γ lam).toReal + ε)))} with hTdef
  have hgint : ∀ k, Integrable (g k) μ := by
    intro k
    refine (Integrable.sub ((integrable_finsetSum (F k) fun i _ ↦ ?_).const_mul _)
      (integrable_const c)).abs
    exact (measurePreserving_eval_infinitePi (fun _ : S ↦ γ) i).integrable_comp_of_integrable hint
  have hL1 : Tendsto (fun k ↦ ∫ ζ, g k ζ ∂μ) l (𝓝 0) :=
    tendsto_integral_abs_inv_card_sum_llr_sub hint hne hFol
  -- Markov's inequality turns the `L¹` convergence into convergence in probability
  have hmark : ∀ k, μ {ζ | ε ≤ g k ζ} ≤ ENNReal.ofReal (ε⁻¹ * ∫ ζ, g k ζ ∂μ) := by
    intro k
    have h := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := g k)
      (.of_forall fun ζ ↦ abs_nonneg _) (hgint k) ε
    have hle : μ.real {ζ | ε ≤ g k ζ} ≤ ε⁻¹ * ∫ ζ, g k ζ ∂μ := by
      rw [inv_mul_eq_div, le_div_iff₀ hε, mul_comm]
      exact h
    calc μ {ζ | ε ≤ g k ζ} = ENNReal.ofReal (μ.real {ζ | ε ≤ g k ζ}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      _ ≤ ENNReal.ofReal (ε⁻¹ * ∫ ζ, g k ζ ∂μ) := ENNReal.ofReal_le_ofReal hle
  have hup : Tendsto (fun k ↦ ENNReal.ofReal (ε⁻¹ * ∫ ζ, g k ζ ∂μ)) l (𝓝 0) := by
    have hre : Tendsto (fun k ↦ ε⁻¹ * ∫ ζ, g k ζ ∂μ) l (𝓝 0) := by simpa using hL1.const_mul ε⁻¹
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hre
  have hzero : Tendsto (fun k ↦ μ {ζ | ε ≤ g k ζ}) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (.of_forall fun _ ↦ bot_le) (.of_forall hmark)
  -- the good event is contained in the event we care about, up to a null set
  have hsub : ∀ᶠ k in l, μ {ζ | g k ζ < ε} ≤ μ (T k) := by
    filter_upwards [hne] with k hk
    refine measure_mono_ae ?_
    filter_upwards [ae_forall_rnDeriv_ne_top hac (F k)] with ζ htop hζ
    have hn : (0 : ℝ) < (F k).card := by exact_mod_cast hk.card_pos
    have hζ' : |((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, llr γ lam (ζ i) - c| < ε := hζ
    have hsum : ∑ i ∈ F k, llr γ lam (ζ i) ≤ (F k).card * (c + ε) := by
      have h2 := (abs_lt.1 hζ').2
      have : ((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, llr γ lam (ζ i) < c + ε := by linarith
      calc ∑ i ∈ F k, llr γ lam (ζ i)
          = (F k).card * (((F k).card : ℝ)⁻¹ * ∑ i ∈ F k, llr γ lam (ζ i)) := by
            field_simp
        _ ≤ (F k).card * (c + ε) := by nlinarith
    change ∏ i ∈ F k, γ.rnDeriv lam (ζ i)
      ≤ ENNReal.ofReal (Real.exp ((F k).card * ((klDiv γ lam).toReal + ε)))
    rw [hc]
    by_cases hz : ∃ i ∈ F k, γ.rnDeriv lam (ζ i) = 0
    · obtain ⟨i, hi, hi0⟩ := hz
      rw [Finset.prod_eq_zero hi hi0]
      exact bot_le
    rw [not_exists] at hz
    simp only [not_and] at hz
    have hpos : ∀ i ∈ F k, 0 < (γ.rnDeriv lam (ζ i)).toReal := fun i hi ↦
      ENNReal.toReal_pos (hz i hi) (htop i hi)
    have hprod : ∏ i ∈ F k, γ.rnDeriv lam (ζ i)
        = ENNReal.ofReal (∏ i ∈ F k, (γ.rnDeriv lam (ζ i)).toReal) := by
      rw [ENNReal.ofReal_prod_of_nonneg fun i _ ↦ ENNReal.toReal_nonneg]
      exact Finset.prod_congr rfl fun i hi ↦ (ENNReal.ofReal_toReal (htop i hi)).symm
    rw [hprod]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ∏ i ∈ F k, (γ.rnDeriv lam (ζ i)).toReal
        = Real.exp (∑ i ∈ F k, llr γ lam (ζ i)) := by
          rw [← Real.exp_log (Finset.prod_pos hpos),
            Real.log_prod fun i hi ↦ (hpos i hi).ne']
          rfl
      _ ≤ Real.exp ((F k).card * (c + ε)) := Real.exp_le_exp.2 hsum
  -- conclude
  have hge : ∀ᶠ k in l, (1 : ℝ≥0∞) - μ {ζ | ε ≤ g k ζ} ≤ μ (T k) := by
    filter_upwards [hsub] with k hk
    have hcompl : {ζ : S → X | g k ζ < ε} = {ζ : S → X | ε ≤ g k ζ}ᶜ := by
      ext ζ; simp [not_le]
    have hnm : NullMeasurableSet {ζ : S → X | ε ≤ g k ζ} μ :=
      (hgint k).aemeasurable.nullMeasurable measurableSet_Ici
    calc (1 : ℝ≥0∞) - μ {ζ | ε ≤ g k ζ} = μ ({ζ : S → X | ε ≤ g k ζ}ᶜ) :=
          (prob_compl_eq_one_sub₀ hnm).symm
      _ = μ {ζ : S → X | g k ζ < ε} := by rw [hcompl]
      _ ≤ μ (T k) := hk
  have hone : Tendsto (fun k ↦ (1 : ℝ≥0∞) - μ {ζ | ε ≤ g k ζ}) l (𝓝 1) := by
    have h := ENNReal.Tendsto.sub (ma := fun _ : κ ↦ (1 : ℝ≥0∞))
      (mb := fun k ↦ μ {ζ | ε ≤ g k ζ}) tendsto_const_nhds hzero (Or.inl ENNReal.one_ne_top)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hone tendsto_const_nhds hge
    (.of_forall fun _ ↦ prob_le_one)


end McMillan

/-! ### Transport to the lattice: the independent-block field of Proposition (15.52) -/

section Tiling

variable {S E : Type*} [MeasurableSpace E] [AddCommGroup S] [DecidableEq S]
  {C : Finset S} {H : AddSubgroup S}
  (hCH : AddSubgroup.IsComplement (C : Set S) (H : Set S))
  (lam : Measure E) [IsProbabilityMeasure lam]

include hCH

omit [DecidableEq S] in
/-- A tiling of an infinite group by a finite tile has infinitely many tiles. -/
theorem infinite_of_isComplement [Infinite S] : Infinite H := by
  have hsurj : Function.Surjective fun p : C × H ↦ ((p.1 : S) + (p.2 : S)) := fun g ↦
    ⟨(⟨(hCH.equiv g).1, Finset.mem_coe.1 (hCH.equiv g).1.2⟩,
      ⟨(hCH.equiv g).2, SetLike.mem_coe.1 (hCH.equiv g).2.2⟩), hCH.equiv_fst_add_equiv_snd g⟩
  have hinf : Infinite (C × H) := Infinite.of_surjective _ hsurj
  rw [← not_finite_iff_infinite]
  intro hfin
  exact not_finite (C × H)

omit [DecidableEq S] in
/-- **The independent-block field of the a priori law on a tile is the a priori law on the whole
lattice.** In Georgii's notation, `λ̂^C = λ^S`. -/
theorem tileProduct_pi_eq_infinitePi :
    tileProduct hCH (Measure.pi fun _ : C ↦ lam) = Measure.infinitePi fun _ : S ↦ lam := by
  have hinj : Function.Injective fun p : H × C ↦ ((p.2 : S) + (p.1 : S)) := by
    rintro ⟨h₁, c₁⟩ ⟨h₂, c₂⟩ hp
    have h1 := hCH.equiv_add (Finset.mem_coe.2 c₁.2) (SetLike.mem_coe.2 h₁.2)
    have h2 := hCH.equiv_add (Finset.mem_coe.2 c₂.2) (SetLike.mem_coe.2 h₂.2)
    simp only at hp
    rw [hp, h2] at h1
    have hc : (c₂ : S) = (c₁ : S) := congrArg (fun p ↦ (p.1 : S)) h1
    have hh : (h₂ : S) = (h₁ : S) := congrArg (fun p ↦ (p.2 : S)) h1
    exact Prod.ext (Subtype.ext hh.symm) (Subtype.ext hc.symm)
  have h1 : (Measure.infinitePi fun _ : S ↦ lam).map
      (fun (ω : S → E) (p : H × C) ↦ ω ((p.2 : S) + (p.1 : S)))
      = Measure.infinitePi fun _ : H × C ↦ lam :=
    Measure.map_infinitePi_infinitePi_of_inj hinj
  have h2 : (Measure.infinitePi fun _ : H × C ↦ lam).map (MeasurableEquiv.curry H C E)
      = Measure.infinitePi fun _ : H ↦ Measure.pi fun _ : C ↦ lam := by
    have h := Measure.infinitePi_map_curry (ι := H) (κ := C) (X := E) fun _ _ ↦ lam
    rwa [Measure.infinitePi_eq_pi (fun _ : C ↦ lam)] at h
  have hcomp : (Measure.infinitePi fun _ : S ↦ lam).map (tilingEquiv (E := E) hCH).symm
      = Measure.infinitePi fun _ : H ↦ Measure.pi fun _ : C ↦ lam := by
    rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.curry H C E).measurable
      (Measurable.of_eval fun p ↦ measurable_pi_apply ((p.2 : S) + (p.1 : S)))]
    rfl
  rw [tileProduct, ← hcomp, Measure.map_map (tilingEquiv (E := E) hCH).measurable
    (tilingEquiv (E := E) hCH).symm.measurable]
  simp

/-- **The density of the independent-block field `γ̂` in a volume that is a union of tiles**:
the product, over the tiles `C + k` met by `Δ`, of the block densities `r = dγ/dλ^C` evaluated at
the configuration in the tile. -/
def blockDensity (γ : Measure (C → E)) (Δ : Finset S) (ω : S → E) : ℝ≥0∞ :=
  ∏ k ∈ tileIdxImage hCH Δ,
    γ.rnDeriv (Measure.pi fun _ : C ↦ lam) ((tilingEquiv (E := E) hCH).symm ω k)

variable (γ : Measure (C → E)) [IsProbabilityMeasure γ]

/-- In tile coordinates, an event of a volume that is a union of tiles is an event of the
corresponding set of tile indices. -/
theorem measurableSet_cylinderEvents_tilingEquiv_preimage {Δ : Finset S}
    (h : IsTileUnion hCH Δ) {A : Set (S → E)}
    (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A) :
    MeasurableSet[cylinderEvents (X := fun _ : H ↦ (C → E))
      ((tileIdxImage hCH Δ : Finset H) : Set H)] ((tilingEquiv (E := E) hCH) ⁻¹' A) := by
  rw [cylinderEvents_eq_comap_finsetRestrict] at hA ⊢
  obtain ⟨B, hB, rfl⟩ := hA
  refine ⟨(blockEquiv (E := E) hCH h).symm ⁻¹' B, (blockEquiv hCH h).symm.measurable hB, ?_⟩
  have hfun : Δ.restrict ∘ (tilingEquiv (E := E) hCH)
      = (blockEquiv (E := E) hCH h).symm ∘ (tileIdxImage hCH Δ).restrict := by
    have h1 := blockEquiv_comp_finsetRestrict_comp_tilingEquiv (E := E) hCH h
    funext ζ
    have := congrFun h1 ζ
    simpa using congrArg (blockEquiv (E := E) hCH h).symm this
  rw [← Set.preimage_comp, ← Set.preimage_comp, hfun]

/-- **The change of measure of Georgii's proof of (15.47), on the lattice.** For a volume `Δ`
that is a union of tiles and a `𝓕_Δ`-event `A`, the part of `A` on which the product of the block
densities is at most `M` has `γ̂`-measure at most `M λ^S(A)`. -/
theorem tileProduct_inter_le_mul_infinitePi
    (hac : γ ≪ Measure.pi fun _ : C ↦ lam) {Δ : Finset S} (h : IsTileUnion hCH Δ)
    {A : Set (S → E)} (hA : MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] A)
    (M : ℝ≥0∞) :
    tileProduct hCH γ (A ∩ {ω : S → E | blockDensity hCH lam γ Δ ω ≤ M})
      ≤ M * (Measure.infinitePi fun _ : S ↦ lam) A := by
  have hmeas := (tilingEquiv (E := E) hCH).measurable
  have hset : (tilingEquiv (E := E) hCH) ⁻¹'
      (A ∩ {ω : S → E | blockDensity hCH lam γ Δ ω ≤ M})
      = ((tilingEquiv (E := E) hCH) ⁻¹' A) ∩ {ζ : H → C → E |
        ∏ k ∈ tileIdxImage hCH Δ,
          γ.rnDeriv (Measure.pi fun _ : C ↦ lam) (ζ k) ≤ M} := by
    rw [Set.preimage_inter]
    congr 1
    ext ζ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, blockDensity,
      MeasurableEquiv.symm_apply_apply]
  calc tileProduct hCH γ (A ∩ {ω : S → E | blockDensity hCH lam γ Δ ω ≤ M})
      = (Measure.infinitePi fun _ : H ↦ γ) ((tilingEquiv (E := E) hCH) ⁻¹'
          (A ∩ {ω : S → E | blockDensity hCH lam γ Δ ω ≤ M})) := by
        rw [tileProduct, Measure.map_apply hmeas
          ((cylinderEvents_le_pi _ hA).inter (by
            have hbd : Measurable fun ω : S → E ↦ blockDensity hCH lam γ Δ ω :=
              Finset.measurable_prod _ fun k _ ↦ (γ.measurable_rnDeriv _).comp
                ((measurable_pi_apply k).comp (tilingEquiv (E := E) hCH).symm.measurable)
            exact hbd measurableSet_Iic))]
    _ ≤ M * (Measure.infinitePi fun _ : H ↦ Measure.pi fun _ : C ↦ lam)
          ((tilingEquiv (E := E) hCH) ⁻¹' A) := by
        rw [hset]
        exact infinitePi_inter_le_mul_infinitePi hac
          (measurableSet_cylinderEvents_tilingEquiv_preimage hCH h hA) M
    _ = M * (Measure.infinitePi fun _ : S ↦ lam) A := by
        congr 1
        rw [← Measure.map_apply hmeas (cylinderEvents_le_pi _ hA)]
        exact congrArg (fun μ : Measure (S → E) ↦ μ A) (tileProduct_pi_eq_infinitePi hCH lam)

/-- **The theorem of McMillan for the independent-block field `γ̂` of Georgii Proposition
(15.52).** Let `Δ_n` be volumes that are unions of tiles whose index sets `K_n` form a Følner net
in the tiling subgroup `H`. Then, in `γ̂`-probability, the product of the block densities is at
most `exp(|K_n| (𝓗(γ | λ^C) + ε))` with probability tending to one. Since `|Δ_n| = |K_n| |C|`,
this is Georgii's `|Δ_n|⁻¹ log f_{Δ_n} → −𝓀(γ̃) = |C|⁻¹ 𝓗(γ | λ^C)` in probability, which is what
the proof of the large deviation lower bound (15.47) consumes. -/
theorem tendsto_tileProduct_setOf_blockDensity_le [Countable S] [Infinite S]
    (hac : γ ≪ Measure.pi fun _ : C ↦ lam)
    (hint : Integrable (llr γ (Measure.pi fun _ : C ↦ lam)) γ)
    {κ : Type*} {l : Filter κ} {Δ : κ → Finset S}
    (hne : ∀ᶠ n in l, (tileIdxImage hCH (Δ n)).Nonempty)
    (hFol : ∀ j : H, Tendsto (fun n ↦
      (((j +ᵥ tileIdxImage hCH (Δ n)) ∆ tileIdxImage hCH (Δ n)).card : ℝ)
        / (tileIdxImage hCH (Δ n)).card) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ tileProduct hCH γ {ω : S → E | blockDensity hCH lam γ (Δ n) ω
      ≤ ENNReal.ofReal (Real.exp ((tileIdxImage hCH (Δ n)).card
        * ((klDiv γ (Measure.pi fun _ : C ↦ lam)).toReal + ε)))}) l (𝓝 1) := by
  have : Infinite H := infinite_of_isComplement hCH
  have hmeas := (tilingEquiv (E := E) hCH).measurable
  have hbd : ∀ n : κ, Measurable fun ω : S → E ↦ blockDensity hCH lam γ (Δ n) ω := fun n ↦
    Finset.measurable_prod _ fun k _ ↦ (γ.measurable_rnDeriv _).comp
      ((measurable_pi_apply k).comp (tilingEquiv (E := E) hCH).symm.measurable)
  refine (tendsto_measure_setOf_prod_rnDeriv_le (γ := γ) (lam := Measure.pi fun _ : C ↦ lam)
    (F := fun n ↦ tileIdxImage hCH (Δ n)) hac hint hne hFol hε).congr fun n ↦ ?_
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((tileIdxImage hCH (Δ n)).card
    * ((klDiv γ (Measure.pi fun _ : C ↦ lam)).toReal + ε))) with hM
  have hset : (tilingEquiv (E := E) hCH) ⁻¹' {ω : S → E | blockDensity hCH lam γ (Δ n) ω ≤ M}
      = {ζ : H → C → E | ∏ i ∈ tileIdxImage hCH (Δ n),
          γ.rnDeriv (Measure.pi fun _ : C ↦ lam) (ζ i) ≤ M} := by
    ext ζ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, blockDensity,
      MeasurableEquiv.symm_apply_apply]
  have hmap : tileProduct hCH γ {ω : S → E | blockDensity hCH lam γ (Δ n) ω ≤ M}
      = (Measure.infinitePi fun _ : H ↦ γ)
        ((tilingEquiv (E := E) hCH) ⁻¹' {ω : S → E | blockDensity hCH lam γ (Δ n) ω ≤ M}) :=
    Measure.map_apply hmeas ((hbd n) measurableSet_Iic)
  rw [hmap, hset]

end Tiling

/-! ### The centred-cube tiling of `ℤ^d` -/

section CubeTiling

variable {d : ℕ} (n : ℕ)

/-- The tiling subgroup `p ℤ^d`, `p = 2n + 1`, of the tiling of `ℤ^d` by the centred cubes
`Λ(n) = [-n, n]^d` (`isComplement_piFinset_Icc`). -/
abbrev tileSubgroup : AddSubgroup (Fin d → ℤ) :=
  AddSubgroup.pi Set.univ fun _ : Fin d ↦ AddSubgroup.zmultiples (2 * (n : ℤ) + 1)

/-- Multiplication by `p = 2n + 1` is an isomorphism `ℤ^d ≃+ p ℤ^d` of the site group onto the
tiling subgroup. -/
def scaleAddEquiv : (Fin d → ℤ) ≃+ tileSubgroup (d := d) n where
  toFun a := ⟨fun k ↦ (2 * (n : ℤ) + 1) * a k,
    (AddSubgroup.mem_pi _).2 fun k _ ↦ Int.mem_zmultiples_iff.2 ⟨a k, rfl⟩⟩
  invFun h := fun k ↦ (h : Fin d → ℤ) k / (2 * (n : ℤ) + 1)
  left_inv a := funext fun k ↦ Int.mul_ediv_cancel_left _ (by omega)
  right_inv h := by
    refine Subtype.ext (funext fun k ↦ ?_)
    obtain ⟨c, hc⟩ := Int.mem_zmultiples_iff.1 ((AddSubgroup.mem_pi _).1 h.2 k (Set.mem_univ k))
    simp only
    rw [hc, Int.mul_ediv_cancel_left _ (by omega)]
  map_add' a b := Subtype.ext (funext fun k ↦ by simp [mul_add])

@[simp] lemma coe_scaleAddEquiv (a : Fin d → ℤ) (k : Fin d) :
    ((scaleAddEquiv (d := d) n a : Fin d → ℤ)) k = (2 * (n : ℤ) + 1) * a k := rfl

/-- The centred cube of radius `M p + n`, the union of the `(2M+1)^d` tiles indexed by
`|i| ≤ M`. -/
abbrev cubeUnion (M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d ↦
    Finset.Icc (-((M * (2 * n + 1) + n : ℕ) : ℤ)) ((M * (2 * n + 1) + n : ℕ) : ℤ)

private lemma abs_add_mul_le_iff' (M : ℕ) {a i : ℤ} (ha : |a| ≤ (n : ℤ)) :
    |a + (2 * (n : ℤ) + 1) * i| ≤ (M : ℤ) * (2 * (n : ℤ) + 1) + n ↔ |i| ≤ (M : ℤ) := by
  have hp : (0 : ℤ) < 2 * (n : ℤ) + 1 := by positivity
  constructor
  · intro hle
    by_contra hi
    rw [not_le] at hi
    have h1 : (M : ℤ) + 1 ≤ |i| := hi
    have h2 : |(2 * (n : ℤ) + 1) * i| - |a| ≤ |a + (2 * (n : ℤ) + 1) * i| := by
      have h := abs_sub_abs_le_abs_sub ((2 * (n : ℤ) + 1) * i) (-a)
      rw [abs_neg, sub_neg_eq_add, add_comm ((2 * (n : ℤ) + 1) * i) a] at h
      exact h
    rw [abs_mul, abs_of_pos hp] at h2
    nlinarith
  · intro hi
    calc |a + (2 * (n : ℤ) + 1) * i| ≤ |a| + |(2 * (n : ℤ) + 1) * i| := abs_add_le _ _
      _ = |a| + (2 * (n : ℤ) + 1) * |i| := by rw [abs_mul, abs_of_pos hp]
      _ ≤ (n : ℤ) + (2 * (n : ℤ) + 1) * (M : ℤ) := by gcongr
      _ = (M : ℤ) * (2 * (n : ℤ) + 1) + n := by ring

private lemma mem_cubeUnion_iff {M : ℕ} {x : Fin d → ℤ} :
    x ∈ cubeUnion (d := d) n M ↔ ∀ k, |x k| ≤ (M : ℤ) * (2 * (n : ℤ) + 1) + n := by
  have hcast : ((M * (2 * n + 1) + n : ℕ) : ℤ) = (M : ℤ) * (2 * (n : ℤ) + 1) + n := by
    push_cast; ring
  simp only [cubeUnion, Fintype.mem_piFinset, Finset.mem_Icc, abs_le, hcast]

private lemma mem_tile_iff {c : Fin d → ℤ} :
    c ∈ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) ↔ ∀ k, |c k| ≤ (n : ℤ) := by
  simp only [Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- **The tile indices met by the centred cube of radius `M p + n`** are the multiples `p i` with
`|i| ≤ M`. -/
theorem tileIdxImage_cubeUnion (M : ℕ) :
    tileIdxImage (isComplement_piFinset_Icc (d := d) n) (cubeUnion (d := d) n M)
      = (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(M : ℤ)) M).image
          (scaleAddEquiv (d := d) n) := by
  classical
  set hCH := isComplement_piFinset_Icc (d := d) n with hCHdef
  ext h
  simp only [tileIdxImage, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    set c : Fin d → ℤ := (tileRep hCH x : Fin d → ℤ) with hc
    have hcmem : ∀ k, |c k| ≤ (n : ℤ) := (mem_tile_iff n).1 (tileRep hCH x).2
    obtain ⟨i, hi⟩ : ∃ i : Fin d → ℤ, ∀ k,
        ((tileIdx hCH x : Fin d → ℤ)) k = (2 * (n : ℤ) + 1) * i k := by
      refine ⟨fun k ↦ ((tileIdx hCH x : Fin d → ℤ)) k / (2 * (n : ℤ) + 1), fun k ↦ ?_⟩
      obtain ⟨e, he⟩ := Int.mem_zmultiples_iff.1
        ((AddSubgroup.mem_pi _).1 (tileIdx hCH x).2 k (Set.mem_univ k))
      simp only
      rw [he, Int.mul_ediv_cancel_left _ (by omega)]
    have hxk : ∀ k, x k = c k + (2 * (n : ℤ) + 1) * i k := fun k ↦ by
      rw [← hi k, hc]
      exact (congrFun (coe_tileRep_add_coe_tileIdx hCH x) k).symm
    refine ⟨i, Fintype.mem_piFinset.2 fun k ↦ Finset.mem_Icc.2 (abs_le.1 ?_), ?_⟩
    · rw [← abs_add_mul_le_iff' n M (hcmem k), ← hxk k]
      exact (mem_cubeUnion_iff n).1 hx k
    · exact Subtype.ext (funext fun k ↦ (hi k).symm)
  · rintro ⟨i, hi, rfl⟩
    have hib := fun k ↦ abs_le.2 (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hi k))
    refine ⟨fun k ↦ (2 * (n : ℤ) + 1) * i k, (mem_cubeUnion_iff n).2 fun k ↦ ?_, ?_⟩
    · have h0 : |(0 : ℤ)| ≤ (n : ℤ) := by simp
      have := (abs_add_mul_le_iff' n M h0).2 (hib k)
      simpa using this
    · have hmem : ((0 : Fin d → ℤ)) ∈ (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) :=
        (mem_tile_iff n).2 fun k ↦ by simp
      have hk : (fun k ↦ (2 * (n : ℤ) + 1) * i k) ∈ tileSubgroup (d := d) n :=
        (scaleAddEquiv (d := d) n i).2
      have h := tileIdx_add hCH hmem hk
      rw [zero_add] at h
      exact h

/-- The tile-index sets of the centred cubes form a **Følner sequence** in the tiling subgroup
`p ℤ^d`: they are the images of the cubes `[-M, M]^d` under the isomorphism `ℤ^d ≃+ p ℤ^d`. -/
theorem tendsto_card_vadd_tileIdxImage_symmDiff_div_card (h : tileSubgroup (d := d) n) :
    Tendsto (fun M : ℕ ↦
      (((h +ᵥ tileIdxImage (isComplement_piFinset_Icc (d := d) n) (cubeUnion (d := d) n M)) ∆
          tileIdxImage (isComplement_piFinset_Icc (d := d) n) (cubeUnion (d := d) n M)).card : ℝ)
        / (tileIdxImage (isComplement_piFinset_Icc (d := d) n) (cubeUnion (d := d) n M)).card)
      atTop (𝓝 0) := by
  classical
  set e := scaleAddEquiv (d := d) n with hedef
  obtain ⟨a, rfl⟩ := e.surjective h
  set Q : ℕ → Finset (Fin d → ℤ) := fun M ↦ Fintype.piFinset fun _ : Fin d ↦
    Finset.Icc (-(M : ℤ)) M with hQ
  have hinj : Function.Injective (e : (Fin d → ℤ) → tileSubgroup (d := d) n) := e.injective
  have hvadd : ∀ M : ℕ, (e a +ᵥ (Q M).image e) = ((a +ᵥ Q M).image e) := by
    intro M
    ext y
    simp only [Finset.mem_vadd_finset, Finset.mem_image, vadd_eq_add]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨b, hb, rfl⟩, by rw [map_add]⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨e b, ⟨b, hb, rfl⟩, by rw [map_add]⟩
  -- the cube `[-M, M]^d` is a translate of the standard cube `[0, 2M+1)^d`
  have hQcube : ∀ M : ℕ, Q M = (fun _ : Fin d ↦ -(M : ℤ)) +ᵥ
      Fintype.piFinset fun _ : Fin d ↦ Finset.Ico (0 : ℤ) (((2 * M : ℕ) + 1 : ℕ) : ℤ) := by
    intro M
    have h1 : Q M = Finset.Icc (fun _ : Fin d ↦ -(M : ℤ))
        fun k ↦ (fun _ : Fin d ↦ -(M : ℤ)) k + ((2 * M : ℕ) : ℤ) := by
      ext x
      simp only [hQ, Fintype.mem_piFinset, Finset.mem_Icc, Pi.le_def]
      constructor
      · intro hx
        exact ⟨fun k ↦ (hx k).1, fun k ↦ by have := (hx k).2; push_cast; omega⟩
      · rintro ⟨h1, h2⟩ k
        refine ⟨h1 k, ?_⟩
        have := h2 k
        push_cast at this ⊢
        omega
    rw [h1, Finset.Icc_cube_eq_vadd_piFinset_Ico]
  have hr : Tendsto (fun M : ℕ ↦ 2 * M + 1) atTop atTop := by
    refine tendsto_atTop_mono (fun M ↦ ?_) (tendsto_id (α := ℕ))
    simp only [id_eq]
    omega
  have hfol := tendsto_card_vadd_cube_symmDiff_div_card (ι := Fin d)
    (fun M : ℕ ↦ fun _ : Fin d ↦ -(M : ℤ)) (r := fun M : ℕ ↦ 2 * M + 1) hr a
  refine hfol.congr fun M ↦ ?_
  rw [← hQcube M, tileIdxImage_cubeUnion n M, hvadd M,
    ← Finset.image_symmDiff _ _ hinj, Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ hinj]

variable {E : Type*} [MeasurableSpace E] (lam : Measure E) [IsProbabilityMeasure lam]
  (γ : Measure ((Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n) → E))
  [IsProbabilityMeasure γ]

/-- **The theorem of McMillan for Georgii's independent-block field `γ̂` on `ℤ^d`.** Let `Λ(n)` be
the centred cube of side `p = 2n+1`, `γ` a block law on `E^{Λ(n)}` with finite relative entropy
`𝓗(γ | λ^{Λ(n)})`, and `γ̂` the field making the blocks `Λ(n) + p i` independent with law `γ`.
Then, along the centred cubes `Δ_M` of radius `M p + n` — the volumes that are unions of tiles —
`|Δ_M|⁻¹ log f_{Δ_M} ≤ |Λ(n)|⁻¹ 𝓗(γ | λ^{Λ(n)}) + ε` with `γ̂`-probability tending to one, where
`f_{Δ_M} = blockDensity` is the density of `γ̂` on `𝓕_{Δ_M}` relative to `λ^S`. -/
theorem tendsto_tileProduct_setOf_blockDensity_le_cube [NeZero d]
    (hac : γ ≪ Measure.pi fun _ ↦ lam)
    (hint : Integrable (llr γ (Measure.pi fun _ ↦ lam)) γ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun M : ℕ ↦ tileProduct (isComplement_piFinset_Icc n) γ
      {ω : (Fin d → ℤ) → E |
        blockDensity (isComplement_piFinset_Icc n) lam γ (cubeUnion (d := d) n M) ω
          ≤ ENNReal.ofReal (Real.exp ((cubeUnion (d := d) n M).card
            * ((klDiv γ (Measure.pi fun _ ↦ lam)).toReal / ((2 * n + 1) ^ d : ℕ) + ε)))})
      atTop (𝓝 1) := by
  classical
  set hCH := isComplement_piFinset_Icc (d := d) n with hCHdef
  set q : ℕ := (2 * n + 1) ^ d with hqdef
  have hqpos : (0 : ℝ) < q := by
    rw [hqdef]; positivity
  have hcardC : (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n).card = q :=
    card_piFinset_Icc n
  have hcard : ∀ M : ℕ, (cubeUnion (d := d) n M).card
      = (tileIdxImage hCH (cubeUnion (d := d) n M)).card * q := fun M ↦ by
    rw [← hcardC]
    exact card_of_isTileUnion hCH (isTileUnion_piFinset_Icc n M)
  have hne : ∀ᶠ M : ℕ in atTop, (tileIdxImage hCH (cubeUnion (d := d) n M)).Nonempty := by
    refine .of_forall fun M ↦ ?_
    rw [tileIdxImage_cubeUnion n M]
    exact (Finset.image_nonempty).2 ⟨0, Fintype.mem_piFinset.2 fun _ ↦ by simp⟩
  have h := tendsto_tileProduct_setOf_blockDensity_le hCH lam γ hac hint hne
    (tendsto_card_vadd_tileIdxImage_symmDiff_div_card n) (ε := (q : ℝ) * ε) (by positivity)
  refine h.congr fun M ↦ ?_
  congr 2
  rw [hcard M]
  push_cast
  field_simp

/-- **Georgii's form of the block McMillan theorem**: the cut-off is `−𝓀(γ̃) + ε`, where
`𝓀(γ̃) = |Λ(n)|⁻¹ 𝓗_{Λ(n)}(γ)` is the specific entropy of the randomly shifted independent-block
field of Proposition (15.52) (`specificEntropy_tileAverage`). -/
theorem tendsto_tileProduct_setOf_blockDensity_le_specificEntropy [NeZero d]
    (hac : γ ≪ Measure.pi fun _ ↦ lam)
    (hint : Integrable (llr γ (Measure.pi fun _ ↦ lam)) γ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun M : ℕ ↦ tileProduct (isComplement_piFinset_Icc n) γ
      {ω : (Fin d → ℤ) → E |
        blockDensity (isComplement_piFinset_Icc n) lam γ (cubeUnion (d := d) n M) ω
          ≤ ENNReal.ofReal (Real.exp ((cubeUnion (d := d) n M).card
            * (-(specificEntropy lam
                (tileAverage (isComplement_piFinset_Icc n) γ)).toReal + ε)))})
      atTop (𝓝 1) := by
  have hq : ((2 * n + 1) ^ d : ℕ) ≠ 0 := by positivity
  have hKfin : klDiv γ (Measure.pi fun _ ↦ lam) ≠ ⊤ := klDiv_ne_top hac hint
  have hk : (specificEntropy lam (tileAverage (isComplement_piFinset_Icc (d := d) n) γ)).toReal
      = -((klDiv γ (Measure.pi fun _ ↦ lam)).toReal / ((2 * n + 1) ^ d : ℕ)) := by
    have hq' : (((2 * n + 1) ^ d : ℕ) : EReal) = ((((2 * n + 1) ^ d : ℕ) : ℝ) : EReal) := by
      rw [EReal.coe_coe_eq_natCast]
    rw [specificEntropy_tileAverage lam n γ, ← EReal.coe_ennreal_toReal hKfin, ← EReal.coe_neg,
      hq', ← EReal.coe_div, EReal.toReal_coe]
    ring
  simpa [hk] using tendsto_tileProduct_setOf_blockDensity_le_cube n lam γ hac hint hε

end CubeTiling

/-! ### The tiles met by an arbitrary box -/

section BoxHull

open scoped Pointwise

variable {d : ℕ} (n : ℕ)

/-- **The tiles met by a box lie within `2n` of it.** Every site of the union `Δ⁺` of the tiles
`Λ(n) + p i` that meet the box `∏_k [a_k, a_k + s]` lies in that box enlarged by `2n` in each
direction, because two sites of one tile differ by at most `2n` in each coordinate. -/
lemma tileHull_Icc_subset (a : Fin d → ℤ) (s : ℕ) :
    tileHull (isComplement_piFinset_Icc (d := d) n) (Finset.Icc a fun k ↦ a k + (s : ℤ))
      ⊆ Finset.Icc (fun k ↦ a k - 2 * (n : ℤ))
        (fun k ↦ (a k - 2 * (n : ℤ)) + ((s + 4 * n : ℕ) : ℤ)) := by
  intro x hx
  obtain ⟨y, hy, c, hc, c', hc', rfl⟩ := exists_of_mem_tileHull _ hx
  have hy1 : ∀ k, a k ≤ y k := fun k ↦ (Finset.mem_Icc.1 hy).1 k
  have hy2 : ∀ k, y k ≤ a k + (s : ℤ) := fun k ↦ (Finset.mem_Icc.1 hy).2 k
  have hcb : ∀ k, |c k| ≤ (n : ℤ) := (mem_tile_iff (d := d) n).1 hc
  have hcb' : ∀ k, |c' k| ≤ (n : ℤ) := (mem_tile_iff (d := d) n).1 hc'
  have hle1 : ∀ k, a k - 2 * (n : ℤ) ≤ y k + (c k - c' k) := by
    intro k
    have h3 := abs_le.1 (hcb k)
    have h4 := abs_le.1 (hcb' k)
    have := hy1 k
    omega
  have hle2 : ∀ k, y k + (c k - c' k) ≤ (a k - 2 * (n : ℤ)) + ((s + 4 * n : ℕ) : ℤ) := by
    intro k
    have h3 := abs_le.1 (hcb k)
    have h4 := abs_le.1 (hcb' k)
    have := hy2 k
    push_cast
    omega
  exact Finset.mem_Icc.2 ⟨fun k ↦ hle1 k, fun k ↦ hle2 k⟩

/-- The union of the tiles met by a box of side `s + 1` has at most `(s + 4n + 1)^d` sites. -/
lemma card_tileHull_Icc_le (a : Fin d → ℤ) (s : ℕ) :
    (tileHull (isComplement_piFinset_Icc (d := d) n)
        (Finset.Icc a fun k ↦ a k + (s : ℤ))).card ≤ (s + 4 * n + 1) ^ d := by
  refine (Finset.card_le_card (tileHull_Icc_subset n a s)).trans ?_
  rw [card_Icc_add (fun k ↦ a k - 2 * (n : ℤ)) (fun _ ↦ s + 4 * n), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The cardinality of a box of side `s + 1` in `ℤ^d`. -/
lemma card_Icc_cube (a : Fin d → ℤ) (s : ℕ) :
    (Finset.Icc a fun k ↦ a k + (s : ℤ)).card = (s + 1) ^ d := by
  rw [card_Icc_add a (fun _ ↦ s), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **`|Δ⁺| / |Λ| → 1`.** Along cubes whose side tends to infinity, the union `Δ⁺` of the tiles
meeting the cube is asymptotically the cube itself. This is what lets an estimate for the
independent-block field, which lives on a union of tiles, be read at the scale of an *arbitrary*
cube. -/
theorem tendsto_card_tileHull_div_card (a : ℕ → Fin d → ℤ) {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) :
    Tendsto (fun j ↦ ((tileHull (isComplement_piFinset_Icc (d := d) n)
        (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))).card : ℝ)
      / (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ)).card) atTop (𝓝 1) := by
  have hcard : ∀ j : ℕ, ((Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ)).card : ℝ)
      = ((s j : ℝ) + 1) ^ d := fun j ↦ by
    rw [card_Icc_cube]; push_cast; ring
  have hpos : ∀ j : ℕ, (0 : ℝ) < ((s j : ℝ) + 1) ^ d := fun j ↦ by positivity
  have hub : Tendsto (fun j ↦ (((s j : ℝ) + 4 * n + 1) ^ d) / (((s j : ℝ) + 1) ^ d)) atTop
      (𝓝 1) := by
    have hden : Tendsto (fun j ↦ (s j : ℝ) + 1) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp hs).atTop_add tendsto_const_nhds
    have h0 : Tendsto (fun j ↦ (4 * (n : ℝ)) / ((s j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have h1 : Tendsto (fun j ↦ 1 + (4 * (n : ℝ)) / ((s j : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add h0
    rw [add_zero] at h1
    have hbase : Tendsto (fun j ↦ ((s j : ℝ) + 4 * n + 1) / ((s j : ℝ) + 1)) atTop (𝓝 1) := by
      refine h1.congr fun j ↦ ?_
      have h3 : ((s j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    have h2 := hbase.pow d
    rw [one_pow] at h2
    exact h2.congr fun j ↦ div_pow _ _ d
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (.of_forall fun j ↦ ?_) (.of_forall fun j ↦ ?_)
  · rw [hcard j, le_div_iff₀ (hpos j), one_mul, ← hcard j]
    exact_mod_cast Finset.card_le_card (subset_tileHull _ _)
  · rw [hcard j]
    have hnum : ((tileHull (isComplement_piFinset_Icc (d := d) n)
        (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))).card : ℝ)
        ≤ ((s j : ℝ) + 4 * n + 1) ^ d := by
      have hle := card_tileHull_Icc_le n (a j) (s j)
      calc ((tileHull (isComplement_piFinset_Icc (d := d) n)
            (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))).card : ℝ)
          ≤ (((s j + 4 * n + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hle
        _ = ((s j : ℝ) + 4 * n + 1) ^ d := by push_cast; ring
    gcongr

/-- **The tile-index sets of an arbitrary sequence of cubes whose sides tend to infinity form a
Følner sequence in the tiling subgroup `p ℤ^d`.** The Følner property passes from the volumes to
the tiles they meet (`card_vadd_tileIdxImage_symmDiff_le`), and `|K| ≥ |Λ| / |Λ(n)|`. -/
theorem tendsto_card_vadd_tileIdxImage_Icc_symmDiff_div_card (a : ℕ → Fin d → ℤ) {s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (h : tileSubgroup (d := d) n) :
    Tendsto (fun j ↦ (((h +ᵥ tileIdxImage (isComplement_piFinset_Icc (d := d) n)
          (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))) ∆
        tileIdxImage (isComplement_piFinset_Icc (d := d) n)
          (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))).card : ℝ)
      / (tileIdxImage (isComplement_piFinset_Icc (d := d) n)
          (Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ))).card) atTop (𝓝 0) := by
  classical
  set hCH := isComplement_piFinset_Icc (d := d) n with hCHdef
  set Λ : ℕ → Finset (Fin d → ℤ) := fun j ↦ Finset.Icc (a j) fun k ↦ a j k + (s j : ℤ) with hΛ
  set q : ℕ := (2 * n + 1) ^ d with hq
  have hcardC : (Fintype.piFinset fun _ : Fin d ↦ Finset.Icc (-(n : ℤ)) n).card = q :=
    card_piFinset_Icc n
  have hΛne : ∀ j, (Λ j).Nonempty := fun j ↦
    Finset.nonempty_Icc.2 fun k ↦ by simp only [le_add_iff_nonneg_right]; positivity
  have hΛcard : ∀ j, (0 : ℝ) < (Λ j).card := fun j ↦ by exact_mod_cast (hΛne j).card_pos
  have hKne : ∀ j, (tileIdxImage hCH (Λ j)).Nonempty := fun j ↦
    Finset.image_nonempty.2 (hΛne j)
  have hKcard : ∀ j, (0 : ℝ) < (tileIdxImage hCH (Λ j)).card := fun j ↦ by
    exact_mod_cast (hKne j).card_pos
  -- the Følner property of the cubes themselves
  have hcube : ∀ j, Λ j = a j +ᵥ Fintype.piFinset fun _ : Fin d ↦
      Finset.Ico (0 : ℤ) ((s j + 1 : ℕ) : ℤ) := fun j ↦ Finset.Icc_cube_eq_vadd_piFinset_Ico _ _
  have hr : Tendsto (fun j ↦ s j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j ↦ Nat.le_succ (s j)) hs
  have hfol := tendsto_card_vadd_cube_symmDiff_div_card (ι := Fin d) a (r := fun j ↦ s j + 1) hr
    (h : Fin d → ℤ)
  have hfol' : Tendsto (fun j ↦ ((((h : Fin d → ℤ) +ᵥ Λ j) ∆ Λ j).card : ℝ) / (Λ j).card) atTop
      (𝓝 0) := by
    refine hfol.congr fun j ↦ ?_
    rw [hcube j]
  have hbound : Tendsto (fun j ↦ (q : ℝ) *
      (((((h : Fin d → ℤ) +ᵥ Λ j) ∆ Λ j).card : ℝ) / (Λ j).card)) atTop (𝓝 0) := by
    simpa using hfol'.const_mul (q : ℝ)
  refine squeeze_zero (fun j ↦ by positivity) (fun j ↦ ?_) hbound
  rw [mul_div_assoc'] at *
  rw [div_le_div_iff₀ (hKcard j) (hΛcard j)]
  have h1 : (((h +ᵥ tileIdxImage hCH (Λ j)) ∆ tileIdxImage hCH (Λ j)).card : ℝ)
      ≤ ((((h : Fin d → ℤ) +ᵥ Λ j) ∆ Λ j).card : ℝ) := by
    exact_mod_cast card_vadd_tileIdxImage_symmDiff_le hCH (Λ j) h
  have h2 : ((Λ j).card : ℝ) ≤ (tileIdxImage hCH (Λ j)).card * (q : ℝ) := by
    rw [← hcardC]
    exact_mod_cast card_le_card_tileIdxImage_mul hCH (Λ j)
  calc (((h +ᵥ tileIdxImage hCH (Λ j)) ∆ tileIdxImage hCH (Λ j)).card : ℝ) * (Λ j).card
      ≤ ((((h : Fin d → ℤ) +ᵥ Λ j) ∆ Λ j).card : ℝ)
          * ((tileIdxImage hCH (Λ j)).card * (q : ℝ)) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = (q : ℝ) * ((((h : Fin d → ℤ) +ᵥ Λ j) ∆ Λ j).card : ℝ)
          * (tileIdxImage hCH (Λ j)).card := by ring

end BoxHull

end MeasureTheory.GibbsMeasure
